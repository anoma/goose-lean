-- Based on: lean-impl/AVM/Class.lean
import Lean

namespace Gusto.IR

open Lean

/-! ## Member Classification -/

inductive FunctionCategory
  | constructor
  | destructor
  | method
  | multimethod
  deriving Inhabited, BEq, Repr

/-- Class members are either fields OR functions -/
inductive MemberKind
  | field
  | function
  deriving Inhabited, BEq, Repr

/-! ## Type Representations -/

inductive TypeInfo
  | simple (name : Name)
  | tuple (types : Array TypeInfo)
  deriving Inhabited, BEq, Repr

/-! ## Expression IR (mutually inductive) -/

inductive LiteralValue
  | nat (n : Nat)
  | int (i : Int)
  | string (s : String)
  | bool (b : Bool)
  | none
  deriving Inhabited, BEq, Repr

inductive BinaryOp
  | add | sub | mul | div | floordiv | mod
  | pow
  | eq | ne | lt | gt | le | ge
  deriving Inhabited, BEq, Repr

inductive UnaryOp
  | pos | neg
  deriving Inhabited, BEq, Repr

mutual
  inductive ExprInfo
    | ident (name : Name)
    | literal (value : LiteralValue)
    | attribute (obj : ExprInfo) (attr : Name)
    | call (fn : ExprInfo) (args : Array ArgInfo)
    | binary (op : BinaryOp) (left : ExprInfo) (right : ExprInfo)
    | unary (op : UnaryOp) (operand : ExprInfo)
    | tuple (exprs : Array ExprInfo)
    | group (expr : ExprInfo)  -- parenthesized expression
    deriving Inhabited, BEq, Repr

  inductive ArgInfo
    | positional (expr : ExprInfo)
    | keyword (name : Name) (expr : ExprInfo)
    deriving Inhabited, BEq, Repr
end

/-! ## Assignment Targets -/

inductive TargetInfo
  | ident (name : Name)
  | attribute (obj : ExprInfo) (attr : Name)
  | group (target : TargetInfo)
  deriving Inhabited, BEq, Repr

/-! ## Block and Statement IR (mutually inductive) -/

mutual
  inductive StmtInfo
    | expr (expr : ExprInfo)
    | assign (target : TargetInfo) (value : ExprInfo)
    | return (value : Option ExprInfo)
    | pass
    | destroy (expr : ExprInfo)
    | ifThen (cond : ExprInfo) (thenBlock : BlockInfo)
    | ifThenElse (cond : ExprInfo) (thenBlock : BlockInfo) (elseBlock : BlockInfo)
    deriving Inhabited, BEq, Repr

  structure BlockInfo where
    stmts : Array StmtInfo
    deriving Inhabited, BEq, Repr
end

/-! ## Parameter IR -/

inductive ParamInfo
  | simple (name : Name)
  | withDefault (name : Name) (default : ExprInfo)
  | typed (name : Name) (type : TypeInfo)
  | typedWithDefault (name : Name) (type : TypeInfo) (default : ExprInfo)
  deriving Inhabited, BEq, Repr

/-! ## Decorator IR -/

structure DecoratorInfo where
  name : Name
  args : Array ExprInfo
  deriving Inhabited, BEq, Repr

/-! ## Field IR -/

structure FieldInfo where
  name : Name
  type : TypeInfo
  deriving Inhabited, BEq, Repr

/-! ## Function IR -/

/-- Unified function representation for constructors, destructors, methods, and multimethods.
    Category can be None (to be inferred from context) or explicitly set via decorators. -/
structure FunctionInfo where
  decorators : Array DecoratorInfo
  name : Name
  params : Array ParamInfo
  returnType : Option TypeInfo
  body : BlockInfo
  category : Option FunctionCategory  -- None = infer from decorators/context
  deriving Inhabited, BEq, Repr

/-! ## Method IR (legacy compatibility) -/

/-- Compatibility type - same as FunctionInfo but used for class methods specifically -/
abbrev MethodInfo := FunctionInfo

/-! ## Class IR -/

structure ClassBody where
  fields : Array FieldInfo
  constructors : Array FunctionInfo
  methods : Array FunctionInfo
  destructors : Array FunctionInfo
  deriving Inhabited, BEq, Repr

structure ClassInfo where
  name : Name
  baseClasses : Array Name
  decorators : Array DecoratorInfo
  body : ClassBody
  deriving Inhabited, BEq, Repr

/-! ## Module IR (for gusto blocks) -/

/-- Compatibility type - same as FunctionInfo but for top-level functions -/
abbrev MultiMethodInfo := FunctionInfo

/-- A module member can be a class or a multi-method (top-level function) -/
inductive ModuleMember
  | classDecl (info : ClassInfo)
  | multiMethod (info : MultiMethodInfo)
  deriving Inhabited, BEq, Repr

/-- Module info represents a gusto block
    - Single class → generates simple Class + Ecosystem
    - Multiple classes → generates multi-class Ecosystem automatically
    - Multi-methods → added to the generated Ecosystem
-/
structure ModuleInfo where
  name : Name
  classes : Array ClassInfo
  multiMethods : Array MultiMethodInfo
  deriving Inhabited, BEq, Repr

end Gusto.IR
