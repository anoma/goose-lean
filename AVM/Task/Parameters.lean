import AVM.Object

namespace AVM

inductive Task.Parameters where
  | empty
  | fetch (param : TypedObjectId) (rest : Object param.classLabel → Task.Parameters)
  | genId (rest : ObjectId → Task.Parameters)
deriving Inhabited

def Task.Parameters.Product (params : Task.Parameters) : Type u :=
  match params with
  | .empty => PUnit
  | .fetch param rest =>
    Σ (obj : Object param.classLabel), Task.Parameters.Product (rest obj)
  | .genId rest =>
    Σ (objId : ObjectId), Task.Parameters.Product (rest objId)

instance {params : Task.Parameters} : TypeRep params.Product where
  rep := Rep.atomic "Task.Parameters.Product" -- TODO: this should depend on params

def Task.Parameters.Product.beq {params : Task.Parameters} (a b : params.Product) :=
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

instance {params : Task.Parameters} : BEq params.Product where
  beq := Task.Parameters.Product.beq

def Task.Parameters.append (params1 : Task.Parameters) (params2 : params1.Product → Task.Parameters) : Task.Parameters :=
  match params1 with
  | .empty =>
    params2 PUnit.unit
  | .fetch p1 ps1 =>
    .fetch p1
      (fun obj => (ps1 obj).append (fun vals => params2 ⟨obj, vals⟩))
  | .genId ps1 =>
    .genId (fun objId => (ps1 objId).append (fun vals => params2 ⟨objId, vals⟩))

def Task.Parameters.snocFetch (params : Task.Parameters) (objId : params.Product → TypedObjectId) : Task.Parameters :=
  params.append (fun vals => .fetch (objId vals) (fun _ => .empty))

def Task.Parameters.snocGenId (params : Task.Parameters) : Task.Parameters :=
  params.append (fun _ => .genId (fun _ => .empty))

def Task.Parameters.concat (params : List Task.Parameters) : Task.Parameters :=
  match params with
  | [] => .empty
  | ps :: rest =>
    ps.append (fun _ => Task.Parameters.concat rest)

def Task.Parameters.splitProduct
  {params1 : Task.Parameters}
  {params2 : params1.Product → Task.Parameters}
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

def Task.Parameters.splitProducts
  {params : List Task.Parameters}
  (vals : Task.Parameters.concat params |>.Product)
  : HList (params.map Product) :=
  match params with
  | [] => HList.nil
  | _ :: ps =>
    let ⟨vals1, vals'⟩ := splitProduct vals
    let rest : HList (ps.map Product) := splitProducts vals'
    HList.cons vals1 rest

def Task.Parameters.Values.snocFetch {ps : Task.Parameters} (objId : ps.Product → TypedObjectId) (vals : ps.Product) (obj : Object (objId vals).classLabel) : (ps.snocFetch objId).Product :=
  match ps with
  | .empty => ⟨obj, PUnit.unit⟩
  | .fetch _ _ =>
    let ⟨obj', vals'⟩ := vals
    ⟨obj', snocFetch (fun vs => objId ⟨obj', vs⟩) vals' obj⟩
  | .genId _ =>
    let ⟨objId', vals'⟩ := vals
    ⟨objId', snocFetch (fun vs => objId ⟨objId', vs⟩) vals' obj⟩

def Task.Parameters.Values.snocGenId {ps : Task.Parameters} (vals : ps.Product) (objId : ObjectId) : ps.snocGenId.Product :=
  match ps with
  | .empty => ⟨objId, PUnit.unit⟩
  | .fetch _ _ =>
    let ⟨obj', vals'⟩ := vals
    ⟨obj', snocGenId vals' objId⟩
  | .genId _ =>
    let ⟨objId', vals'⟩ := vals
    ⟨objId', snocGenId vals' objId⟩

def Task.Parameters.Values.dropLastGenId {ps : Task.Parameters} (vals : ps.snocGenId.Product) : ps.Product :=
  match ps with
  | .empty => vals.2
  | .fetch _ _ =>
    let ⟨obj, vals'⟩ := vals
    ⟨obj, dropLastGenId vals'⟩
  | .genId _ =>
    let ⟨objId, vals'⟩ := vals
    ⟨objId, dropLastGenId vals'⟩

def Task.Parameters.Values.dropLastFetch {ps : Task.Parameters} {objId : ps.Product → TypedObjectId} (vals : (ps.snocFetch objId).Product) : ps.Product :=
  match ps with
  | .empty => vals.2
  | .fetch _ _ =>
    let ⟨obj, vals'⟩ := vals
    ⟨obj, dropLastFetch vals'⟩
  | .genId _ =>
    let ⟨objId, vals'⟩ := vals
    ⟨objId, dropLastFetch vals'⟩
