
import Prelude
import AVM.Intent
import AVM.Class.Member.Logic
import AVM.Class.AppData

namespace AVM

def Intent.logic (intent : Intent) (args : Anoma.Logic.Args Unit) : Bool :=
  if args.isConsumed then
    match Intent.ResourceData.fromResource args.self with
    | some data =>
      let receivedObjects := List.map (SomeObject.fromResource (PublicFields := ⟨Unit⟩) ()) args.created
      match tryCast data.args with
      | some argsData =>
        intent.condition argsData data.provided receivedObjects
      | none =>
        false
    | none =>
      false
  else
    true

/-- An action which consumes the provided objects and creates the intent. -/
def Intent.action (intent : Intent) (args : intent.Args.type) (provided : List SomeObject) : Anoma.Action :=
  -- TODO: set nonce and nullifierKeyCommitment properly
  let consumedObjects := provided
  let consumedResources := List.map SomeObject.toResource consumedObjects
  let intentResource := Intent.toResource intent args provided
  let appData : Std.HashMap Anoma.Tag Class.SomeAppData :=
    Std.HashMap.emptyWithCapacity
    |>.insertMany (List.zipWithExact (mkTagDataPair (isConsumed := true)) consumedObjects consumedResources)
  { Data := Class.SomeAppData,
    consumed := List.map Anoma.RootedNullifiableResource.Transparent.fromResource consumedResources,
    created := [intentResource],
    appData }
  where
    mkTagDataPair (isConsumed : Bool) (obj : SomeObject) (res : Anoma.Resource) : Anoma.Tag × Class.SomeAppData :=
      (Anoma.Tag.fromResource isConsumed res,
        { appData := {
            Args := Unit,
            memberAppData := Class.Member.appData obj.sig obj.object (),
            -- An indication for trivial member logic (no extra logic for the
            -- resources consumed in intent creation)
            memberLogic := trueLogic
          }
        })

/-- A transaction which consumes the provided objects and creates the intent. -/
def Intent.transaction (intent : Intent) (args : intent.Args.type) (provided : List SomeObject) (currentRoot : Anoma.CommitmentRoot) : Anoma.Transaction :=
  let action := intent.action args provided
  { roots := [currentRoot],
    actions := [action],
    -- TODO: set deltaProof properly
    deltaProof := "" }
