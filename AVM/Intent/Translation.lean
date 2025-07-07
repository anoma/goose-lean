
import Prelude
import AVM.Intent
import AVM.Class.Member.Logic
import AVM.Class.AppData

namespace AVM

def Intent.logic (intent : Intent) (args : Anoma.Logic.Args Unit) : Bool :=
  if args.isConsumed then
    match Intent.ResourceData.fromResource args.self with
    | some data => BoolCheck.run do
      let receivedObjects ← BoolCheck.some <| List.mapSome (SomeObject.fromResource (PublicFields := ⟨Unit⟩) ()) args.created
      BoolCheck.ret <|
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
    |>.insertMany (List.zipWithExact (mkTagDataPairConsumed) consumedObjects consumedResources)
  { Data := Class.SomeAppData,
    consumed := List.map Anoma.RootedNullifiableResource.Transparent.fromResource consumedResources,
    created := [intentResource],
    appData }
  where
    mkTagDataPairConsumed (obj : SomeObject) (_res : Anoma.Resource)
     : Anoma.Tag × Class.SomeAppData :=
      (Anoma.Tag.Consumed Anoma.Nullifier.placeholder,
        { label := obj.label,
          appData := {
            -- TODO: assigning falseLogicId to memberId is not correct - it will
            -- make the logic fail. But what should we assign here? It seems
            -- like the consumed object needs to know about the intent and have
            -- a method which allows its consumption in the intent. How does
            -- this actually work in the kudos / spacebucks examples we have?
            memberId := Class.Label.MemberId.falseLogicId,
            memberArgs := UUnit.unit,
            publicFields := obj.object.publicFields
        }})

/-- A transaction which consumes the provided objects and creates the intent. -/
def Intent.transaction (intent : Intent) (args : intent.Args.type) (provided : List SomeObject) (currentRoot : Anoma.CommitmentRoot) : Anoma.Transaction :=
  let action := intent.action args provided
  { roots := [currentRoot],
    actions := [action],
    -- TODO: set deltaProof properly
    deltaProof := "" }
