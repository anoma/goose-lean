import Anoma
import AVM.Object
import AVM.Message
import AVM.Action
import AVM.Program.Parameters

namespace AVM

structure Task.Actions.{u, v} : Type (max u v + 1) where
  actions : List Anoma.Action.{u, v}
  deltaWitness : Anoma.DeltaWitness

/-- Tasks are intermediate data structures used in the translation. Translating
  AVM message sends to Transactions first generates Tasks as an intermediate
  step. Tasks enable modularity of the translation – they are at the right
  level of abstraction to compose translations of different message sends,
  enabling nested method calls and subobjects. -/
structure Task.{u, v} : Type (max u v + 1) where
  /-- Task parameters - objects to fetch from the Anoma system and random values
    to generate. In general, values in `task.params.Product` are assumed to be
    unadjusted (see `Program.Parameters.Product`). -/
  params : Program.Parameters
  /-- The message to send to the recipient. -/
  message : params.Product → Option SomeMessage
  /-- Task actions - actions to perform parameterised by fetched objects and new
    object ids. -/
  actions : params.Product → Rand (Option Task.Actions.{u, v})
  deriving Inhabited

def Task.absorbParams (params : Program.Parameters) (task : params.Product → Task) : Task :=
  { params := params.append (fun vals => (task vals).params),
    message := fun vals =>
      let ⟨vals1, vals2⟩ := vals.split
      (task vals1).message vals2,
    actions := fun vals =>
      let ⟨vals1, vals2⟩ := vals.split
      (task vals1).actions vals2 }

def Task.absorbGenId (task : ObjectId → Task) : Task :=
  Task.absorbParams
    (Program.Parameters.genId (fun _ => .empty))
    (fun ⟨newId, ()⟩ => task newId)

def Task.absorbFetch {label : Ecosystem.Label} {c : label.ClassId} (objId : ObjectId) (task : Object c → Task) : Task :=
  Task.absorbParams
    (Program.Parameters.fetch objId (fun _ => .empty))
    (fun ⟨obj, ()⟩ => task obj)
