
import Utils
import Goose.Intent
import Goose.Class.Member.Logic

namespace Goose

noncomputable unsafe def Intent.logic (intent : Intent) (args : Anoma.Logic.Args Unit) : Bool :=
  match Intent.ResourceData.fromResource args.self with
  | some data =>
    let receivedObjects := List.map (Object.fromResource ()) args.created
    intent.condition (unsafeCast data.args) data.provided receivedObjects
  | none =>
    false

/-- An action which consumes the provided objects and creates the intent. -/
def Intent.action (intent : Intent) (args : intent.Args) (provided : List Object) : Anoma.Action :=
  -- TODO: set nonce and nullifierKeyCommitment properly
  let consumedObjects := provided
  let consumedResources := List.map Object.toResource consumedObjects
  let intentResource := Intent.toResource intent args provided
  let appData : Std.HashMap Anoma.Tag Class.AppData :=
    Std.HashMap.emptyWithCapacity
    |>.insertMany (List.zipWithExact (mkTagDataPair (isConsumed := true)) consumedObjects consumedResources)
  { Data := Class.AppData,
    consumed := List.map Anoma.RootedNullifiableResource.Transparent.fromResource consumedResources,
    created := [intentResource],
    appData }
  where
    mkTagDataPair (isConsumed : Bool) (obj : Object) (res : Anoma.Resource) : Anoma.Tag × Class.AppData :=
      (Anoma.Tag.fromResource isConsumed res,
        { Args := Unit,
          memberAppData := Class.Member.appData obj (),
          -- An indication for trivial member logic (no extra logic for intent creation)
          memberLogic := trueLogic
        })

/-- A transaction which consumes the provided objects and creates the intent. -/
def Intent.transaction (intent : Intent) (args : intent.Args) (provided : List Object) (currentRoot : Anoma.CommitmentRoot) : Anoma.Transaction :=
  let action := intent.action args provided
  { roots := [currentRoot],
    actions := [action],
    -- TODO: set deltaProof properly
    deltaProof := "" }

end Goose
