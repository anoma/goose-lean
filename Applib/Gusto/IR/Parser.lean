import Lean

import Prelude.See
import Applib.Gusto.Syntax
import Applib.Gusto.IR.Types

namespace Gusto.IR.Parser

open Lean Meta
open Gusto.IR
open Gusto

/-!
# Gusto Syntax → IR Parser

The parser is organized into modular sections:

1. Type Parsing: parseType, parseReturnType
2. Expression Parsing: mutual recursive parsers (atom → primary → ... → comp)
3. Statement Parsing:parseTarget, parseStmt, parseBlock
4. Member Parsing: parseParam, parseDecorator, parseField, parseFunction
5. Class/Module Parsing:parseClassBody, parseClassDecl, parseModule
6. Inference Helpers: inferFunctionCategory

-/

/-! ## Helper Functions -/

/-- Check if decorators contain a specific name -/
def hasDecorator (decorators : Array DecoratorInfo) (name : Name) : Bool :=
  decorators.any (·.name == name)

/-- Infer function category from decorators -/
def inferFunctionCategoryFromDecorators
  (decorators : Array DecoratorInfo) : Option FunctionCategory :=
  decorators.findSome? fun dec =>
    match dec.name with
    | `constructor  => some .constructor
    | `destructor   => some .destructor
    | `multimethod  => some .multimethod
    | `method       => some .method
    | _             => none

/-! ## Type Parsing -/

partial def parseType (stx : Syntax) : MetaM TypeInfo := do
  match stx with
  | `(gusto_type| $name:ident) =>
    seeThis f!"[Gusto.Parser.Type] Parsed simple type: {name.getId}"
    return .simple name.getId
  | _ =>
    seeThis f!"[Gusto.Parser.Type] Failed to parse type: {stx}"
    throwError "Expected type syntax"

partial def parseReturnType (stx : Syntax) : MetaM TypeInfo := do
  match stx with
  | `(gusto_return_type| $ty:gusto_type) =>
    parseType ty
  | `(gusto_return_type| ($types:gusto_type, $rest:gusto_type,*)) =>
    let mut parsedTypes := #[← parseType types]
    for ty in rest.getElems do
      parsedTypes := parsedTypes.push (← parseType ty)
    seeThis f!"[Gusto.Parser.Type] Parsed tuple return type with {parsedTypes.size} types"
    return .tuple parsedTypes
  | _ =>
    throwError "Expected return type syntax"

/-! ## Expression Parsing -/

mutual
-- Parse atoms (lowest level)
partial def parseAtom (stx : Syntax) : MetaM ExprInfo := do
  match stx with
  -- Numeric literals
  | `(gusto_atom| $n:num) =>
    let val := n.getNat
    seeThis f!"[Gusto.Parser.Expr] Parsed num literal: {val}"
    return .literal (.nat val)
  -- String literals
  | `(gusto_atom| $s:str) =>
    let val := s.getString
    seeThis f!"[Gusto.Parser.Expr] Parsed string literal: {val}"
    return .literal (.string val)
  -- Boolean literals
  | `(gusto_atom| True) =>
    seeThis f!"[Gusto.Parser.Expr] Parsed True"
    return .literal (.bool true)
  | `(gusto_atom| False) =>
    seeThis f!"[Gusto.Parser.Expr] Parsed False"
    return .literal (.bool false)
  -- None literal
  | `(gusto_atom| None) =>
    seeThis f!"[Gusto.Parser.Expr] Parsed None"
    return .literal .none
  -- Identifiers
  | `(gusto_atom| $id:ident) =>
    seeThis f!"[Gusto.Parser.Expr] Parsed ident: {id.getId}"
    return .ident id.getId
  -- Grouped expressions
  | `(gusto_atom| ($e:gusto_expr)) =>
    let parsed ← parseExpr e
    seeThis f!"[Gusto.Parser.Expr] Parsed grouped expression"
    return .group parsed
  -- Tuple expressions
  | `(gusto_atom| ($e:gusto_expr, $es:gusto_expr,*)) =>
    let first ← parseExpr e
    let mut rest := #[first]
    for elem in es.getElems do
      rest := rest.push (← parseExpr elem)
    seeThis f!"[Gusto.Parser.Expr] Parsed tuple with {rest.size} elements"
    return .tuple rest
  | _ =>
    seeThis f!"[Gusto.Parser.Expr] Failed to parse atom: {stx}"
    throwError "Expected atom syntax"

-- Parse function call arguments
partial def parseArg (stx : Syntax) : MetaM ArgInfo := do
  match stx with
  -- Positional arguments
  | `(gusto_arg| $e:gusto_expr) =>
    let parsed ← parseExpr e
    return .positional parsed
  -- Keyword arguments
  | `(gusto_arg| $name:ident = $e:gusto_expr) =>
    let parsed ← parseExpr e
    seeThis f!"[Gusto.Parser.Expr] Parsed keyword arg: {name.getId}"
    return .keyword name.getId parsed
  | _ =>
    throwError "Expected argument syntax"

-- Parse primary (attribute access, calls, atoms)
partial def parsePrimary (stx : Syntax) : MetaM ExprInfo := do
  match stx with
  -- Atoms
  | `(gusto_primary| $atom:gusto_atom) =>
    parseAtom atom
  -- Attribute access
  | `(gusto_primary| $obj:gusto_primary . $attr:ident) =>
    let objParsed ← parsePrimary obj
    seeThis f!"[Gusto.Parser.Expr] Parsed attribute access: .{attr.getId}"
    return .attribute objParsed attr.getId
  -- Function calls
  | `(gusto_primary| $fn:gusto_primary ($args:gusto_arg,*)) =>
    let fnParsed ← parsePrimary fn
    let mut parsedArgs := #[]
    for arg in args.getElems do
      parsedArgs := parsedArgs.push (← parseArg arg)
    seeThis f!"[Gusto.Parser.Expr] Parsed function call with {parsedArgs.size} args"
    return .call fnParsed parsedArgs
  | _ =>
    throwError "Expected primary syntax"

-- Parse power (exponentiation)
partial def parsePower (stx : Syntax) : MetaM ExprInfo := do
  match stx with
  | `(gusto_power| $p:gusto_primary) =>
    parsePrimary p
  | `(gusto_power| $base:gusto_primary ** $exp:gusto_factor) =>
    let baseParsed ← parsePrimary base
    let expParsed ← parseFactor exp
    seeThis f!"[Gusto.Parser.Expr] Parsed power operator"
    return .binary .pow baseParsed expParsed
  | _ =>
    throwError "Expected power syntax"

-- Parse factor (unary +/-)
partial def parseFactor (stx : Syntax) : MetaM ExprInfo := do
  match stx with
  | `(gusto_factor| $p:gusto_power) =>
    parsePower p
  | `(gusto_factor| + $f:gusto_factor) =>
    let operand ← parseFactor f
    seeThis f!"[Gusto.Parser.Expr] Parsed unary +"
    return .unary .pos operand
  | `(gusto_factor| - $f:gusto_factor) =>
    let operand ← parseFactor f
    seeThis f!"[Gusto.Parser.Expr] Parsed unary -"
    return .unary .neg operand
  | _ =>
    throwError "Expected factor syntax"

-- Parse term (*, /, //, %)
partial def parseTerm (stx : Syntax) : MetaM ExprInfo := do
  match stx with
  -- Factor
  | `(gusto_term| $f:gusto_factor) =>
    parseFactor f
  -- Multiplication
  | `(gusto_term| $left:gusto_term * $right:gusto_factor) =>
    let l ← parseTerm left
    let r ← parseFactor right
    seeThis f!"[Gusto.Parser.Expr] Parsed * operator"
    return .binary .mul l r
  -- Division
  | `(gusto_term| $left:gusto_term / $right:gusto_factor) =>
    let l ← parseTerm left
    let r ← parseFactor right
    seeThis f!"[Gusto.Parser.Expr] Parsed / operator"
    return .binary .div l r
  -- Floor division
  | `(gusto_term| $left:gusto_term // $right:gusto_factor) =>
    let l ← parseTerm left
    let r ← parseFactor right
    seeThis f!"[Gusto.Parser.Expr] Parsed // operator"
    return .binary .floordiv l r
  -- Modulo
  | `(gusto_term| $left:gusto_term % $right:gusto_factor) =>
    let l ← parseTerm left
    let r ← parseFactor right
    seeThis f!"[Gusto.Parser.Expr] Parsed % operator"
    return .binary .mod l r
  | _ =>
    throwError "Expected term syntax"

-- Parse sum (+, -)
partial def parseSum (stx : Syntax) : MetaM ExprInfo := do
  match stx with
  -- Term
  | `(gusto_sum| $t:gusto_term) =>
    parseTerm t
  -- Addition
  | `(gusto_sum| $left:gusto_sum + $right:gusto_term) =>
    let l ← parseSum left
    let r ← parseTerm right
    seeThis f!"[Gusto.Parser.Expr] Parsed + operator"
    return .binary .add l r
  -- Subtraction
  | `(gusto_sum| $left:gusto_sum - $right:gusto_term) =>
    let l ← parseSum left
    let r ← parseTerm right
    seeThis f!"[Gusto.Parser.Expr] Parsed - operator"
    return .binary .sub l r
  | _ =>
    throwError "Expected sum syntax"

-- Parse comparison (==, !=, <, >, <=, >=)
partial def parseComp (stx : Syntax) : MetaM ExprInfo := do
  match stx with
  | `(gusto_comp| $s:gusto_sum) =>
    parseSum s
  -- Equality
  | `(gusto_comp| $left:gusto_comp == $right:gusto_sum) =>
    let l ← parseComp left
    let r ← parseSum right
    seeThis f!"[Gusto.Parser.Expr] Parsed == operator"
    return .binary .eq l r
  -- Inequality
  | `(gusto_comp| $left:gusto_comp != $right:gusto_sum) =>
    let l ← parseComp left
    let r ← parseSum right
    seeThis f!"[Gusto.Parser.Expr] Parsed != operator"
    return .binary .ne l r
  -- Less than
  | `(gusto_comp| $left:gusto_comp < $right:gusto_sum) =>
    let l ← parseComp left
    let r ← parseSum right
    seeThis f!"[Gusto.Parser.Expr] Parsed < operator"
    return .binary .lt l r
  -- Greater than
  | `(gusto_comp| $left:gusto_comp > $right:gusto_sum) =>
    let l ← parseComp left
    let r ← parseSum right
    seeThis f!"[Gusto.Parser.Expr] Parsed > operator"
    return .binary .gt l r
  -- Less than or equal to
  | `(gusto_comp| $left:gusto_comp <= $right:gusto_sum) =>
    let l ← parseComp left
    let r ← parseSum right
    seeThis f!"[Gusto.Parser.Expr] Parsed <= operator"
    return .binary .le l r
  -- Greater than or equal to
  | `(gusto_comp| $left:gusto_comp >= $right:gusto_sum) =>
    let l ← parseComp left
    let r ← parseSum right
    seeThis f!"[Gusto.Parser.Expr] Parsed >= operator"
    return .binary .ge l r
  | _ =>
    throwError "Expected comparison syntax"

-- Top-level expression parser
partial def parseExpr (stx : Syntax) : MetaM ExprInfo := do
  match stx with
  -- Comparison
  | `(gusto_expr| $c:gusto_comp) =>
    parseComp c
  | _ =>
    throwError "Expected expression syntax"

end -- end mutual

/-! ## Assignment Target Parsing -/

partial def parseTarget (stx : Syntax) : MetaM TargetInfo := do
  seeThis f!"[Gusto.Parser.Target] Parsing target from syntax"
  -- Try ident first
  if stx.isIdent then
    seeThis f!"[Gusto.Parser.Target] Parsed ident target: {stx.getId}"
    return .ident stx.getId

  -- Try to match other patterns by inspecting syntax structure
  -- Pattern: gusto_primary "." ident
  if stx.getKind == `Gusto.«gusto_target_._» && stx.getNumArgs >= 3 then
    let obj := stx.getArg 0
    let attr := stx.getArg 2
    if attr.isIdent then
      let objParsed ← parsePrimary obj
      seeThis f!"[Gusto.Parser.Target] Parsed attribute target: .{attr.getId}"
      return .attribute objParsed attr.getId

  -- Pattern: "(" gusto_target ")"
  if stx.getKind == `Gusto.«gusto_target(_)» && stx.getNumArgs >= 3 then
    let inner := stx.getArg 1
    let parsed ← parseTarget inner
    return .group parsed

  -- Fallback: check if it's just an ident wrapped
  if stx.getNumArgs > 0 then
    let arg0 := stx.getArg 0
    if arg0.isIdent then
      let id := arg0.getId
      seeThis f!"[Gusto.Parser.Target] Parsed wrapped ident target: {id}"
      return .ident id

  throwError "Expected target syntax: {stx}"

/-! ## Statement Parsing -/

mutual

partial def parseSimpleStmt (stx : Syntax) : MetaM StmtInfo := do
  match stx with
  -- Expression statement
  | `(gusto_simple_stmt| $e:gusto_expr) =>
    let parsed ← parseExpr e
    seeThis f!"[Gusto.Parser.Stmt] Parsed expression statement"
    return .expr parsed
  -- Return statement
  | `(gusto_simple_stmt| return) =>
    seeThis f!"[Gusto.Parser.Stmt] Parsed return (no value)"
    return .return none
  -- Return statement with value
  | `(gusto_simple_stmt| return $e:gusto_expr) =>
    let parsed ← parseExpr e
    seeThis f!"[Gusto.Parser.Stmt] Parsed return with value"
    return .return (some parsed)
  -- Pass statement
  | `(gusto_simple_stmt| pass) =>
    seeThis f!"[Gusto.Parser.Stmt] Parsed pass"
    return .pass
  -- Destroy statement
  | `(gusto_simple_stmt| destroy $e:gusto_expr) =>
    let parsed ← parseExpr e
    seeThis "[Gusto.Parser.Stmt] Parsed destroy"
    return .destroy parsed
  -- Del statement (this does the same as destroy)
  | `(gusto_simple_stmt| del $e:gusto_expr) =>
    let parsed ← parseExpr e
    seeThis "[Gusto.Parser.Stmt] Parsed del (destroy)"
    return .destroy parsed
  -- Assignment statement, e.g. `x = 1`
  | `(gusto_simple_stmt| $target:gusto_target = $value:gusto_expr) =>
    let t ← parseTarget target
    let v ← parseExpr value
    seeThis f!"[Gusto.Parser.Stmt] Parsed assignment"
    return .assign t v
  -- Fallback: throw error
  | _ =>
    throwError "Expected simple statement syntax"

partial def parseBlockStmt (stx : Syntax) : MetaM StmtInfo := do
  match stx with
  -- Simple statement
  | `(gusto_block_stmt| $s:gusto_simple_stmt) =>
    parseSimpleStmt s
  -- If statement
  | `(gusto_block_stmt| if $cond:gusto_expr : $thenBlock:gusto_block) =>
    let c ← parseExpr cond
    let tb ← parseBlock thenBlock
    seeThis f!"[Gusto.Parser.Stmt] Parsed if statement"
    return .ifThen c tb
  -- If-else statement
  | `(gusto_block_stmt| if $cond:gusto_expr : $thenBlock:gusto_block else : $elseBlock:gusto_block) =>
    let c ← parseExpr cond
    let tb ← parseBlock thenBlock
    let eb ← parseBlock elseBlock
    seeThis f!"[Gusto.Parser.Stmt] Parsed if-else statement"
    return .ifThenElse c tb eb
  -- Fallback: throw error
  | _ =>
    throwError "Expected block statement syntax"

partial def parseBlock (stx : Syntax) : MetaM BlockInfo := do
  match stx with
  -- Block statement list
  | `(gusto_block| $stmts:gusto_block_stmt*) =>
    let mut parsedStmts := #[]
    for stmt in stmts do
      parsedStmts := parsedStmts.push (← parseBlockStmt stmt)
    seeThis f!"[Gusto.Parser.Block] Parsed block with {parsedStmts.size} statements"
    return { stmts := parsedStmts }
  -- Fallback: throw error
  | _ =>
    throwError "Expected block syntax"

end -- end mutual

/-! ## Parameter Parsing -/

def parseParam (stx : Syntax) : MetaM ParamInfo := do
  match stx with
  -- Simple parameter, e.g. `def foo(x)`
  | `(gusto_param| $name:ident) =>
    seeThis f!"[Gusto.Parser.Param] Parsed simple param: {name.getId}"
    return .simple name.getId
  -- Parameter with default, e.g. `def foo(x = 1)`
  | `(gusto_param| $name:ident = $default:gusto_expr) =>
    let d ← parseExpr default
    seeThis f!"[Gusto.Parser.Param] Parsed param with default: {name.getId}"
    return .withDefault name.getId d
  -- Typed parameter, e.g. `def foo(x : Int)`
  | `(gusto_param| $name:ident : $ty:gusto_type) =>
    let t ← parseType ty
    seeThis f!"[Gusto.Parser.Param] Parsed typed param: {name.getId}"
    return .typed name.getId t
  -- Typed parameter with default, e.g. `def foo(x : Int = 1)`
  | `(gusto_param| $name:ident : $ty:gusto_type = $default:gusto_expr) =>
    let t ← parseType ty
    let d ← parseExpr default
    seeThis f!"[Gusto.Parser.Param] Parsed typed param with default: {name.getId}"
    return .typedWithDefault name.getId t d
  -- Fallback: throw error
  | _ =>
    throwError "Expected parameter syntax"

def parseParams (stx : Syntax) : MetaM (Array ParamInfo) := do
  match stx with
  -- Parameter list, e.g. `def foo(x, y, z)`
  | `(gusto_param_list| $params:gusto_param,*) =>
    let mut parsed := #[]
    for p in params.getElems do
      parsed := parsed.push (← parseParam p)
    seeThis f!"[Gusto.Parser.Param] Parsed {parsed.size} parameter(s)"
    return parsed
  | _ =>
    throwError "Expected parameter list syntax"

/-! ## Decorator Parsing -/

def parseDecorator (stx : Syntax) : MetaM DecoratorInfo := do
  match stx with
  | `(gusto_decorator| @$id:ident) =>
    seeThis f!"[Gusto.Parser.Decorator] Parsed decorator: @{id.getId}"
    return { name := id.getId, args := #[] }
  | `(gusto_decorator| @$id:ident ($args:gusto_expr,*)) =>
    let mut parsedArgs := #[]
    for arg in args.getElems do
      parsedArgs := parsedArgs.push (← parseExpr arg)
    seeThis f!"[Gusto.Parser.Decorator] Parsed decorator @{id.getId} with {parsedArgs.size} args"
    return { name := id.getId, args := parsedArgs }
  | _ =>
    throwError "Expected decorator syntax"

/-! ## Field Parsing -/

def parseFieldDecl (stx : Syntax) : MetaM FieldInfo := do
  match stx with
  -- Type annotation, e.g. `x : Int`
  | `(gusto_type_annotation| $name:ident : $ty:ident) =>
    let typeInfo := TypeInfo.simple ty.getId
    seeThis f!"[Gusto.Parser.Field] Parsed field: {name.getId} : {ty.getId}"
    return { name := name.getId, type := typeInfo }
  -- Fallback: throw error
  | _ =>
    throwError "Expected field declaration syntax"

/-! ## Function Parsing (Methods/Constructors/Destructors) -/

/-- Parse a function declaration and infer its category from decorators.
    Handles both gusto_compound_stmt (module-level) and gusto_function_def (class members). -/
def parseFunctionDecl
  (stx : Syntax)
  : MetaM FunctionInfo := do

  match stx with
  -- Function declaration, e.g. `def foo(x, y, z) : <gusto_block>`
  | `(gusto_compound_stmt|
      $decs:gusto_decorator*
      def $name:ident ($params:gusto_param_list) :
         $body:gusto_block)
      =>
        let decorators ← decs.mapM parseDecorator
        let parsedParams ← parseParams params
        let parsedBody ← parseBlock body
        let category := inferFunctionCategoryFromDecorators decorators

        seeThis f!"[Gusto.Parser.Function] Parsed function: {name.getId} (no return type)"
        seeThis f!"[Gusto.Parser.Function]   Decorators: {decorators.size}, Params: {parsedParams.size}"

        return {
          decorators := decorators,
          name := name.getId,
          params := parsedParams,
          returnType := none,
          body := parsedBody,
          category := category
        }
  -- Function declaration with return type, e.g. `def foo(x, y, z) -> Int : <gusto_block>`
  | `(gusto_compound_stmt|
      $decs:gusto_decorator*
      def $name:ident ($params:gusto_param_list) -> $retTy:gusto_return_type :
         $body:gusto_block)
     =>
      let decorators ← decs.mapM parseDecorator
      let parsedParams ← parseParams params
      let parsedRetTy ← parseReturnType retTy
      let parsedBody ← parseBlock body
      let category := inferFunctionCategoryFromDecorators decorators
      seeThis f!"[Gusto.Parser.Function] Parsed function: {name.getId} (with return type)"
      seeThis f!"[Gusto.Parser.Function]   Decorators: {decorators.size}, Params: {parsedParams.size}"
      return {
        decorators := decorators,
        name := name.getId,
        params := parsedParams,
        returnType := some parsedRetTy,
        body := parsedBody,
        category := category
      }
  -- Class function declaration, e.g. `@decorator def foo(x, y, z) : <gusto_block>`
  | `(gusto_function_def|
      $decs:gusto_decorator*
      def $name:ident ($params:gusto_param_list) :
         $body:gusto_block)
    =>
      let decorators ← decs.mapM parseDecorator
      let parsedParams ← parseParams params
      let parsedBody ← parseBlock body
      let category := inferFunctionCategoryFromDecorators decorators
      seeThis f!"[Gusto.Parser.Function] Parsed class function: {name.getId} (no return type)"
      seeThis f!"[Gusto.Parser.Function]   Decorators: {decorators.size}, Params: {parsedParams.size}"
      return {
        decorators := decorators,
        name := name.getId,
        params := parsedParams,
        returnType := none,
        body := parsedBody,
        category := category
      }
  | `(gusto_function_def|
      $decs:gusto_decorator*
      def $name:ident ($params:gusto_param_list) -> $retTy:gusto_return_type :
         $body:gusto_block)
    =>
      let decorators ← decs.mapM parseDecorator
      let parsedParams ← parseParams params
      let parsedRetTy ← parseReturnType retTy
      let parsedBody ← parseBlock body
      let category := inferFunctionCategoryFromDecorators decorators
      seeThis f!"[Gusto.Parser.Function] Parsed class function: {name.getId} (with return type)"
      seeThis f!"[Gusto.Parser.Function]   Decorators: {decorators.size}, Params: {parsedParams.size}"
      return {
        decorators := decorators,
        name := name.getId,
        params := parsedParams,
        returnType := some parsedRetTy,
        body := parsedBody,
        category := category
      }
  | _ =>
    throwError "Expected function declaration syntax"

/-! ## Class Member Parser -/

def parseClassMember
  (stx : Syntax)
  : MetaM (MemberKind × (FieldInfo ⊕ FunctionInfo)) := do

  let innerStx := if stx.getNumArgs > 0 then stx.getArg 0 else stx
  seeThis "[Gusto.Parser] Parsing class member..."

  -- Try parse as type annotation (field)
  try
    let field ← parseFieldDecl innerStx
    seeThis f!"[Gusto.Parser] Class member is a field: {field.name}"
    return (.field, .inl field)
  catch _ =>
    pure ()

  -- Try parse as compound statement (function: method/constructor/destructor)
  let fn ← parseFunctionDecl innerStx
  let categoryStr := match fn.category with
    | some .constructor => "constructor"
    | some .destructor => "destructor"
    | some .multimethod => "multimethod"
    | _ => "method"
  seeThis f!"[Gusto.Parser] Class member is a {categoryStr}: {fn.name}"
  return (.function, .inr fn)

/-! ## Class Body Parser -/

def parseClassBody (block : Syntax) : MetaM ClassBody := do
  seeThis f!"[Gusto.Parser] Parsing class body...
  (block.getKind={block.getKind}, block.getNumArgs={block.getNumArgs})"

  let mut fields := #[]
  let mut constructors := #[]
  let mut methods := #[]
  let mut destructors := #[]

  -- The block is a raw Syntax node representing the class body
  -- Structure: (ppLine gusto_type_annotation)* (ppLine gusto_function_def)*
  -- Each element can be a null node containing multiple sub-elements
  for i in [:block.getNumArgs] do
    let arg := block.getArg i
    seeThis f!"[Gusto.Parser] Class body arg {i}: kind={arg.getKind}, numArgs={arg.getNumArgs}"

    -- If it's a null node, it might contain multiple elements - process all of them
    let elemsToProcess := if arg.getKind == `null then
      (List.range arg.getNumArgs).map arg.getArg
    else
      [arg]

    for elem in elemsToProcess do
      seeThis f!"[Gusto.Parser] Processing elem: kind={elem.getKind}"

      -- Try to parse as type annotation (field)
      try
        let field ← parseFieldDecl elem
        seeThis f!"[Gusto.Parser] Added field to class body: {field.name}"
        fields := fields.push field
        continue
      catch _ => pure ()

      -- Try to parse as function definition
      try
        let fn ← parseFunctionDecl elem
        -- Categorize based on FunctionInfo.category
        match fn.category with
        | some .constructor =>
          seeThis f!"[Gusto.Parser] Added constructor to class body: {fn.name}"
          constructors := constructors.push fn
        | some .destructor =>
          seeThis f!"[Gusto.Parser] Added destructor to class body: {fn.name}"
          destructors := destructors.push fn
        | some .method | none =>
          -- Default to method if uncategorized
          seeThis f!"[Gusto.Parser] Added method to class body: {fn.name}"
          methods := methods.push fn
        | some .multimethod =>
          seeThis f!"[Gusto.Parser] Warning: multimethod {fn.name} in class body (should be at ecosystem level)"
          methods := methods.push fn  -- Add as regular method for now
        continue
      catch _ => pure ()

  seeThis f!"[Gusto.Parser] Class body summary:
  - {fields.size} fields
  - {constructors.size} constructors
  - {methods.size} methods
  - {destructors.size} destructors"
  return { fields, constructors, methods, destructors }

/-! ## Base Class Parser -/

def parseBaseClasses (stx : Syntax) : MetaM (Array Name) := do
  match stx with
  | `(gusto_expr| $id:ident) =>
    return #[id.getId]
  | _ =>
    return #[]

/-! ## Class Declaration Parser -/

def parseClassDecl
    (name : Syntax)
    (body : Syntax)
    (decorators : Array Syntax := #[])
    (bases : Option (Array Syntax) := none)
    : MetaM ClassInfo := do

  let className := if name.isIdent then name.getId else `UnknownClass
  seeThis f!"[Gusto.Parser] === Parsing class declaration: {className} ==="

  let parsedDecorators ← decorators.mapM parseDecorator
  seeThis f!"[Gusto.Parser] Decorators: {parsedDecorators.size}"

  let mut baseClasses := #[]

  match bases with
  | some baseSyntaxes =>
    seeThis f!"[Gusto.Parser] Class has {baseSyntaxes.size} base class(es)"
    for baseSyntax in baseSyntaxes do
      let parsed ← parseBaseClasses baseSyntax
      baseClasses := baseClasses ++ parsed
  | none =>
    seeThis f!"[Gusto.Parser] Class has no base classes"

  let classBody ← parseClassBody body

  seeThis f!"[Gusto.Parser] ===== Finished parsing class {className} ====="
  return {
    name := className,
    baseClasses := baseClasses,
    decorators := parsedDecorators,
    body := classBody
  }

/-! ## Multi-Method Parser (for Ecosystems) -/

/-- Parse a multi-method declaration (top-level function in ecosystem).
    Uses the same FunctionInfo structure but with category = multimethod.
    Multi-methods are just functions at the module/ecosystem level
    They use the same syntax as regular functions
    -/
def parseMultiMethodDecl (stx : Syntax) : MetaM FunctionInfo := do
  let fn ← parseFunctionDecl stx
  return { fn with category := some .multimethod }

/-! ## Module Parser -/

/-- Parse a gusto module body into ModuleInfo.
    The body contains statements which can be:
    - Class definitions (gusto_compound_stmt with class)
    - Multi-method definitions (gusto_statement with def at module level)
-/
def parseModule (moduleName : Name) (body : Syntax) : MetaM ModuleInfo := do
  seeThis f!"[Gusto.Parser.Module] Parsing module: {moduleName}"

  let mut classes := #[]
  let mut multiMethods := #[]

  for i in [:body.getNumArgs] do
    let arg := body.getArg i
    seeThis f!"[Gusto.Parser.Module] Arg {i}: kind={arg.getKind}, numArgs={arg.getNumArgs}"

    -- Skip ppLine nodes and get to the actual statement
    let stmt := if arg.getKind == `null && arg.getNumArgs > 0 then
      arg.getArg 0
    else
      arg

    -- gusto_statement wraps gusto_compound_stmt (which includes class definitions)
    -- We need to unwrap it first
    let innerStmt := if stmt.getKind == `Gusto.gusto_statement_ && stmt.getNumArgs > 0 then
      stmt.getArg 0
    else
      stmt

    -- Try to parse as class definition (compound statement)
    try
      match innerStmt with
      -- Class definition, e.g. `class ClassName : <gusto_class_body>`
      | `(gusto_compound_stmt| class $name:ident : $classBody:gusto_class_body) =>
        let classInfo ← parseClassDecl name classBody
        seeThis f!"[Gusto.Parser.Module] Parsed class: {classInfo.name}"
        classes := classes.push classInfo
        continue
      -- Class definition with base classes, e.g. `class ClassName(BaseClass1, BaseClass2) : <gusto_class_body>`
      | `(gusto_compound_stmt| class $name:ident ($bases:gusto_expr,*) : $classBody:gusto_class_body) =>
        let classInfo ← parseClassDecl name classBody #[] (some bases.getElems)
        seeThis f!"[Gusto.Parser.Module] Parsed class with bases: {classInfo.name}"
        classes := classes.push classInfo
        continue
      | _ => pure ()
    catch _ =>
      seeThis f!"[Gusto.Parser.Module] Not a class (parse failed): {innerStmt.getKind}"
      pure ()

    -- Try to parse as multi-method (top-level function)
    try
      let fn ← parseMultiMethodDecl stmt
      seeThis f!"[Gusto.Parser.Module] Parsed multi-method: {fn.name}"
      multiMethods := multiMethods.push fn
      continue
    catch _ =>
      seeThis f!"[Gusto.Parser.Module] Not a multi-method (parse failed): {innerStmt.getKind}"
      pure ()

  seeThis f!"[Gusto.Parser.Module] Module {moduleName}: {classes.size} classes, {multiMethods.size} multi-methods"
  return {
    name := moduleName,
    classes := classes,
    multiMethods := multiMethods
  }

end Gusto.IR.Parser
