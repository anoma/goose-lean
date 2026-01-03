import Lean
import Prelude.See
import Applib.Gusto.Syntax
import Applib.Gusto.IR.Types
import Applib.Gusto.IR.Parser
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.DeriveFintype

/-

NOTICE: This file is a work in progress.
Most of the elab steps are not implemented yet.
-/
namespace Gusto.Elab.AVM

open Lean Elab Command Meta Term
open Gusto
open Gusto.IR
open Gusto.IR.Parser

def genConstructorEnum
    (className : Name)
    (body : ClassBody)
    : CommandElabM Unit := do
  if body.constructors.isEmpty then
    seeThis f!"[Gusto.Elab] No constructors for {className}, skipping"
    return ()

  let enumName := mkIdent (className ++ `Constructors)
  let variants := String.intercalate ", " (body.constructors.map (·.name.toString) |>.toList)
  seeThis f!"[Gusto.Elab] Generating {enumName} with {body.constructors.size} variants: {variants}"

  -- Generate: inductive ClassName.Constructors where | Variant1 | Variant2 ... deriving DecidableEq, Fintype, Repr
  let ctorVariants := body.constructors.map fun ctor =>
    let variantName := ctor.name.toString.capitalize
    mkIdent (Name.mkSimple variantName)

  let inductiveCmd ← `(command|
    inductive $enumName where
      $[| $ctorVariants:ident]*
      deriving DecidableEq, Fintype, Repr
  )

  elabCommand inductiveCmd

def genMethodEnum (className : Name) (body : ClassBody) : CommandElabM Unit := do
  if body.methods.isEmpty then
    seeThis f!"[Gusto.Elab] No methods for {className}, skipping"
    return ()

  let enumName := mkIdent (className ++ `Methods)
  let variants := String.intercalate ", " (body.methods.map (·.name.toString) |>.toList)
  seeThis f!"[Gusto.Elab] Generating {enumName} with {body.methods.size} variants: {variants}"

  -- Generate: inductive ClassName.Methods where | Variant1 | Variant2 ... deriving DecidableEq, Fintype, Repr
  let methodVariants := body.methods.map fun method =>
    let variantName := method.name.toString.capitalize
    mkIdent (Name.mkSimple variantName)

  let inductiveCmd ← `(command|
    inductive $enumName where
      $[| $methodVariants:ident]*
      deriving DecidableEq, Fintype, Repr
  )

  elabCommand inductiveCmd

def genDestructorEnum (className : Name) (body : ClassBody) : CommandElabM Unit := do
  if body.destructors.isEmpty then
    seeThis f!"[Gusto.Elab] No destructors for {className}, skipping"
    return ()

  let enumName := mkIdent (className ++ `Destructors)
  let variants := String.intercalate ", " (body.destructors.map (·.name.toString) |>.toList)
  seeThis f!"[Gusto.Elab] Generating {enumName} with {body.destructors.size} variants: {variants}"

  -- Generate: inductive ClassName.Destructors where | Variant1 | Variant2 ... deriving DecidableEq, Fintype, Repr
  let dtorVariants := body.destructors.map fun dtor =>
    let variantName := dtor.name.toString.capitalize
    mkIdent (Name.mkSimple variantName)

  let inductiveCmd ← `(command|
    inductive $enumName where
      $[| $dtorVariants:ident]*
      deriving DecidableEq, Fintype, Repr
  )

  elabCommand inductiveCmd

-- Helper to format TypeInfo
partial def formatTypeInfo : TypeInfo → String
  | .simple name => s!"{name}"
  | .tuple types => s!"({String.intercalate ", " (types.toList.map formatTypeInfo)})"

def genDataStructure (className : Name) (fields : Array IR.FieldInfo) : CommandElabM Unit := do
  let fieldStrs := fields.map (fun f => s!"{f.name}:{formatTypeInfo f.type}") |>.toList
  let fieldList := String.intercalate ", " fieldStrs
  seeThis f!"[Gusto.Elab] Generating structures {className}Data and {className} with {fields.size} fields: {fieldList}"

  -- TODO: Generate both {Name}Data (private fields) and {Name} (extends {Name}Data, adds quantity)

def genClassLabel (className : Name) (body : ClassBody) : CommandElabM Unit := do
  seeThis f!"[Gusto.Elab] Generating Class.Label for {className} (Ctors:{body.constructors.size}, Methods:{body.methods.size}, Dtors:{body.destructors.size})"

  -- The Class.Label should specify:
  -- - name: String
  -- - PrivateFields: Type (the structure we generated)
  -- - MethodId, ConstructorId, DestructorId: Type (the enums)
  -- - MethodArgs, ConstructorArgs, etc.: Id → Args

  -- TODO

def genClassImpl (className : Name) (body : ClassBody) : CommandElabM Unit := do
  seeThis f!"[Gusto.Elab] Generating Class and Ecosystem for {className} (needs {body.constructors.size} ctors, {body.methods.size} methods, {body.destructors.size} dtors)"

  -- The Class should be a value of type:
  -- AVM.Class (classLabel : Class.Label) (classId : label.ClassId)
  -- TODO: Generate remaining components (Signature IDs, TypeRep, Args, conversions, impls, assembly)

-- Elaborate: gusto class Name: body
elab "gusto" "class" className:ident ":" body:gusto_class_body : command => do
  let name := className.getId
  let classBody ← liftTermElabM <| parseClassBody body
  seeThis f!"[Gusto.Elab] Elaborating class {name} ({classBody.fields.size} fields, {classBody.constructors.size} ctors, {classBody.methods.size} methods, {classBody.destructors.size} dtors)"

  -- 1. Generate enums for member IDs
  genConstructorEnum name classBody
  genMethodEnum name classBody
  genDestructorEnum name classBody

  -- 2. Generate the data structure
  genDataStructure name classBody.fields

  -- 3. Generate the AVM.Class.Label
  genClassLabel name classBody

  -- 4. Generate the AVM.Class implementation
  genClassImpl name classBody

  seeThis f!"[Gusto.Elab] Finished elaborating class {name}"

-- Elaborate: gusto class Name(bases): body
elab "gusto" "class" className:ident "(" _bases:gusto_expr,* ")" ":" body:gusto_class_body : command => do
  let name := className.getId
  let classBody ← liftTermElabM <| parseClassBody body
  seeThis f!"[Gusto.Elab] Elaborating class {name} with base classes ({classBody.fields.size} fields, {classBody.constructors.size} ctors, {classBody.methods.size} methods, {classBody.destructors.size} dtors)"

  -- Same steps as above
  genConstructorEnum name classBody
  genMethodEnum name classBody
  genDestructorEnum name classBody
  genDataStructure name classBody.fields
  genClassLabel name classBody
  genClassImpl name classBody

  seeThis f!"[Gusto.Elab] Finished elaborating class {name}"

-- Elaborate: gusto ModuleName <body> end [ModuleName]
@[command_elab Gusto.«gustoModule»]
def elabGustoModule : CommandElab := fun stx => do
  -- Access syntax tree manually: gusto <ident> <body> end [ident]?
  -- Structure: "gusto" <space> <ident> <newline> <body> <newline> "end" [<space> <ident>]?
  let modName := stx[1]  -- The identifier after "gusto"
  let body := stx[2]     -- The module body

  let moduleName := modName.getId
  seeThis f!"[Gusto.Elab.Module] ===== Elaborating module: {moduleName} ====="

  -- Parse the module body
  let moduleInfo ← liftTermElabM <| parseModule moduleName body
  seeThis f!"[Gusto.Elab.Module] Module has {moduleInfo.classes.size} class(es), {moduleInfo.multiMethods.size} multi-method(s)"

  -- Elaborate each class
  for classInfo in moduleInfo.classes do
    seeThis f!"[Gusto.Elab.Module] Elaborating class: {classInfo.name}"

    -- Generate the same components as the standalone class elaborator
    genConstructorEnum classInfo.name classInfo.body
    genMethodEnum classInfo.name classInfo.body
    genDestructorEnum classInfo.name classInfo.body
    genDataStructure classInfo.name classInfo.body.fields
    genClassLabel classInfo.name classInfo.body
    genClassImpl classInfo.name classInfo.body

  -- TODO: If multiple classes or multi-methods, generate Ecosystem
  if moduleInfo.classes.size > 1 || moduleInfo.multiMethods.size > 0 then
    seeThis f!"[Gusto.Elab.Module] TODO: Generate ecosystem for multi-class/multi-method module"

  seeThis f!"[Gusto.Elab.Module] ===== Finished elaborating module {moduleName} ====="

end Gusto.Elab.AVM
