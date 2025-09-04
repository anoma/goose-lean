import AVM.Object

namespace AVM

inductive Program.Parameters where
  | empty
  | fetch (param : TypedObjectId) (rest : Object param.classLabel → Program.Parameters)
  | genId (rest : ObjectId → Program.Parameters)
deriving Inhabited

def Program.Parameters.Product (params : Program.Parameters) : Type u :=
  match params with
  | .empty => PUnit
  | .fetch param rest =>
    Σ (obj : Object param.classLabel), Program.Parameters.Product (rest obj)
  | .genId rest =>
    Σ (objId : ObjectId), Program.Parameters.Product (rest objId)

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

def snocFetch (params : Program.Parameters) (objId : params.Product → TypedObjectId) : Program.Parameters :=
  params.append (fun vals => .fetch (objId vals) (fun _ => .empty))

def snocGenId (params : Program.Parameters) : Program.Parameters :=
  params.append (fun _ => .genId (fun _ => .empty))

def concat (params : List Program.Parameters) : Program.Parameters :=
  match params with
  | [] => .empty
  | ps :: rest =>
    ps.append (fun _ => concat rest)

def splitProduct
  {params1 : Program.Parameters}
  {params2 : params1.Product → Program.Parameters}
  (vals : params1.append params2 |>.Product)
  : Σ (vals : params1.Product), (params2 vals).Product :=
  match params1 with
  | .empty => ⟨PUnit.unit, vals⟩
  | .fetch _ _ =>
    let ⟨obj, vals'⟩ := vals
    let ⟨vals1, vals2⟩ := splitProduct vals'
    ⟨⟨obj, vals1⟩, vals2⟩
  | .genId _ =>
    let ⟨objId, vals'⟩ := vals
    let ⟨vals1, vals2⟩ := splitProduct vals'
    ⟨⟨objId, vals1⟩, vals2⟩

def splitProducts
  {params : List Program.Parameters}
  (vals : Program.Parameters.concat params |>.Product)
  : HList (params.map Program.Parameters.Product) :=
  match params with
  | [] => HList.nil
  | _ :: ps =>
    let ⟨vals1, vals'⟩ := splitProduct vals
    let rest : HList (ps.map Program.Parameters.Product) := splitProducts vals'
    HList.cons vals1 rest

def Values.snocFetch {ps : Program.Parameters} (objId : ps.Product → TypedObjectId) (vals : ps.Product) (obj : Object (objId vals).classLabel) : (ps.snocFetch objId).Product :=
  match ps with
  | .empty => ⟨obj, PUnit.unit⟩
  | .fetch _ _ =>
    let ⟨obj', vals'⟩ := vals
    ⟨obj', Values.snocFetch (fun vs => objId ⟨obj', vs⟩) vals' obj⟩
  | .genId _ =>
    let ⟨objId', vals'⟩ := vals
    ⟨objId', Values.snocFetch (fun vs => objId ⟨objId', vs⟩) vals' obj⟩

def Values.snocGenId {ps : Program.Parameters} (vals : ps.Product) (objId : ObjectId) : ps.snocGenId.Product :=
  match ps with
  | .empty => ⟨objId, PUnit.unit⟩
  | .fetch _ _ =>
    let ⟨obj', vals'⟩ := vals
    ⟨obj', Values.snocGenId vals' objId⟩
  | .genId _ =>
    let ⟨objId', vals'⟩ := vals
    ⟨objId', Values.snocGenId vals' objId⟩

def Values.dropLastGenId {ps : Program.Parameters} (vals : ps.snocGenId.Product) : ps.Product :=
  match ps with
  | .empty => vals.2
  | .fetch _ _ =>
    let ⟨obj, vals'⟩ := vals
    ⟨obj, dropLastGenId vals'⟩
  | .genId _ =>
    let ⟨objId, vals'⟩ := vals
    ⟨objId, dropLastGenId vals'⟩

def Values.dropLastFetch {ps : Program.Parameters} {objId : ps.Product → TypedObjectId} (vals : (ps.snocFetch objId).Product) : ps.Product :=
  match ps with
  | .empty => vals.2
  | .fetch _ _ =>
    let ⟨obj, vals'⟩ := vals
    ⟨obj, dropLastFetch vals'⟩
  | .genId _ =>
    let ⟨objId, vals'⟩ := vals
    ⟨objId, dropLastFetch vals'⟩
