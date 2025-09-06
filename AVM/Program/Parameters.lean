import AVM.Object
import AVM.Ecosystem.Label

namespace AVM

inductive Program.Parameters.{u} : Type (u + 1) where
  | empty
  | fetch (param : TypedObjectId.{u}) (rest : Object param.classLabel → Program.Parameters)
  | genId (rest : ObjectId → Program.Parameters)
  deriving Inhabited, Nonempty

namespace Program.Parameters

def fetchMany
  (params : List TypedObjectId)
  (rest : Pi (params.map (fun param => Object param.classLabel)) Program.Parameters)
  : Program.Parameters :=
  match params with
  | [] => rest.down
  | i :: is => .fetch i (fun o => fetchMany is (rest o))

-- TODO should this be kept?
def fetchManyHList
  (params : List TypedObjectId)
  (rest : HList (params.map (fun param => Object param.classLabel)) → Program.Parameters)
  : Program.Parameters := fetchMany params (HList.toPi rest)

theorem helper
  {lab : Ecosystem.Label}
  {multiId : lab.MultiMethodId}
  (selvesIds : multiId.SelvesIds)
  : HList
    (List.map (fun param => Object param.classLabel)
    (List.map (fun arg => { classLabel := arg.classId.label, uid := selvesIds arg : TypedObjectId }) multiId.objectArgNames))
    =
    HList (List.map (fun c => Object c.label) multiId.argsClasses) := sorry

def fetchSelves
  {lab : Ecosystem.Label}
  {multiId : lab.MultiMethodId}
  (selvesIds : multiId.SelvesIds)
  (rest : multiId.Selves → Program.Parameters)
  : Program.Parameters :=
    fetchManyHList
      (multiId.objectArgNames.map (fun arg =>
                                     { uid := selvesIds arg
                                       classLabel := arg.classId.label}))
      (fun h => rest (multiId.SelvesFromHList (helper selvesIds ▸ h)))

def Product (params : Program.Parameters) : Type u :=
  match params with
  | .empty => PUnit
  | .fetch param rest =>
    Σ (obj : Object param.classLabel), Program.Parameters.Product (rest obj)
  | .genId rest =>
    Σ (objId : ObjectId), Program.Parameters.Product (rest objId)

instance {params : Program.Parameters} : TypeRep params.Product where
  rep := Rep.atomic "Program.Parameters.Product" -- TODO: this should depend on params

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
