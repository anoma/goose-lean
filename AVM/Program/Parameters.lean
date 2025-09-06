import AVM.Object

namespace AVM

inductive Program.Parameters where
  | empty
  | fetch (param : TypedObjectId) (rest : Object param.classLabel → Program.Parameters)
  | genId (rest : ObjectId → Program.Parameters)
deriving Inhabited, Nonempty

def Program.Parameters.Product (params : Program.Parameters) : Type u :=
  match params with
  | .empty => PUnit
  | .fetch param rest =>
    Σ (obj : Object param.classLabel), Program.Parameters.Product (rest obj)
  | .genId rest =>
    Σ (objId : ObjectId), Program.Parameters.Product (rest objId)

def Program.Parameters.map (f : {lab : Class.Label} → Object lab → Object lab) (params : Program.Parameters) : Program.Parameters :=
  match params with
  | .empty => .empty
  | .fetch p rest =>
    .fetch p (fun obj => map f (rest (f obj)))
  | .genId rest =>
    .genId (fun objId => map f (rest objId))

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
    | .genId _ =>
      let ⟨objIdA, valsA⟩ := a
      let ⟨objIdB, valsB⟩ := b
      check objIdA == objIdB
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
  | .genId ps1 =>
    .genId (fun objId => (ps1 objId).append (fun vals => params2 ⟨objId, vals⟩))

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
  | .genId _ =>
    let ⟨objId, vals1'⟩ := vals1
    ⟨objId, Product.append vals1' vals2⟩

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
  | .genId _ =>
    let ⟨objId, vals'⟩ := vals
    let ⟨vals1, vals2⟩ := vals'.split
    ⟨⟨objId, vals1⟩, vals2⟩
