import AVM.Object

namespace AVM

inductive Program.Parameters where
  | empty
  | fetch (param : TypedObjectId) (rest : Object param.classLabel → Program.Parameters)
  | rand (rest : Nat → Program.Parameters)
deriving Inhabited, Nonempty

def Program.Parameters.genId (rest : ObjectId → Program.Parameters) : Program.Parameters :=
  .rand rest

def Program.Parameters.Product (params : Program.Parameters) : Type u :=
  match params with
  | .empty => PUnit
  | .fetch param rest =>
    Σ (obj : Object param.classLabel), Program.Parameters.Product (rest obj)
  | .rand rest =>
    Σ (r : Nat), Program.Parameters.Product (rest r)

def Program.Parameters.Product.defaultValue (params : Program.Parameters) : params.Product :=
  match params with
  | .empty => PUnit.unit
  | .fetch _ rest =>
    ⟨default, Product.defaultValue (rest default)⟩
  | .rand rest =>
    ⟨default, Product.defaultValue (rest default)⟩

instance {params : Program.Parameters} : Inhabited params.Product where
  default := Program.Parameters.Product.defaultValue params

def Program.Parameters.map (f : {lab : Class.Label} → Object lab → Object lab) (params : Program.Parameters) : Program.Parameters :=
  match params with
  | .empty => .empty
  | .fetch p rest =>
    .fetch p (fun obj => map f (rest (f obj)))
  | .rand rest =>
    .rand (fun r => map f (rest r))

instance {params : Program.Parameters} : TypeRep params.Product where
  rep := Rep.atomic "Program.Parameters.Product" -- TODO: this should depend on params

namespace Program.Parameters

def Product.beq {params : Program.Parameters} (a b : params.Product) :=
    match params with
    | .empty => true
    | .fetch _ _ =>
      let ⟨objA, valsA⟩ := a
      let ⟨objB, valsB⟩ := b
      check objA == objB
      let try valsB' := tryCast valsB
      beq valsA valsB'
    | .rand _ =>
      let ⟨rA, valsA⟩ := a
      let ⟨rB, valsB⟩ := b
      check rA == rB
      let try valsB' := tryCast valsB
      beq valsA valsB'

instance {params : Program.Parameters} : BEq params.Product where
  beq := Program.Parameters.Product.beq

def append (params1 : Program.Parameters) (params2 : params1.Product → Program.Parameters) : Program.Parameters :=
  match params1 with
  | .empty =>
    params2 PUnit.unit
  | .fetch p1 ps1 =>
    .fetch p1
      (fun obj => (ps1 obj).append (fun vals => params2 ⟨obj, vals⟩))
  | .rand ps1 =>
    .rand (fun r => (ps1 r).append (fun vals => params2 ⟨r, vals⟩))

def Product.append
  {params1 : Program.Parameters}
  {params2 : params1.Product → Program.Parameters}
  (vals1 : params1.Product)
  (vals2 : (params2 vals1).Product)
  : (params1.append params2).Product :=
  match params1 with
  | .empty => vals2
  | .fetch _ _ =>
    let ⟨obj, vals1'⟩ := vals1
    ⟨obj, Product.append vals1' vals2⟩
  | .rand _ =>
    let ⟨r, vals1'⟩ := vals1
    ⟨r, Product.append vals1' vals2⟩

def Product.split
  {params1 : Program.Parameters}
  {params2 : params1.Product → Program.Parameters}
  (vals : params1.append params2 |>.Product)
  : Σ (vals : params1.Product), (params2 vals).Product :=
  match params1 with
  | .empty => ⟨PUnit.unit, vals⟩
  | .fetch _ _ =>
    let ⟨obj, vals'⟩ := vals
    let ⟨vals1, vals2⟩ := vals'.split
    ⟨⟨obj, vals1⟩, vals2⟩
  | .rand _ =>
    let ⟨r, vals'⟩ := vals
    let ⟨vals1, vals2⟩ := vals'.split
    ⟨⟨r, vals1⟩, vals2⟩
