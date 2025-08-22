import AVM.Object

namespace AVM

inductive Task.Parameters where
  | empty
  | fetch (param : TypedObjectId) (rest : Object param.classLabel → Task.Parameters)
  | genId (rest : ObjectId → Task.Parameters)
deriving Inhabited

def Task.Parameters.Product (params : Task.Parameters) : Type :=
  match params with
  | .empty => PUnit
  | .fetch param rest =>
    Σ (obj : Object param.classLabel), Task.Parameters.Product (rest obj)
  | .genId rest =>
    Σ (objId : ObjectId), Task.Parameters.Product (rest objId)

def Task.Parameters.append (params1 : Task.Parameters) (params2 : params1.Product → Task.Parameters) : Task.Parameters :=
  match params1 with
  | .empty =>
    params2 PUnit.unit
  | .fetch p1 ps1 =>
    .fetch p1
      (fun obj => (ps1 obj).append (fun vals => params2 ⟨obj, vals⟩))
  | .genId ps1 =>
    .genId (fun objId => (ps1 objId).append (fun vals => params2 ⟨objId, vals⟩))

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
