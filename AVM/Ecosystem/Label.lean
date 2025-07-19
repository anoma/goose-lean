import AVM.Class.Label
import AVM.Object

namespace AVM

structure EcosystemLabel : Type 1 where
  name : String

  ClassId : Type
  classes : ClassId -> Class.Label
  [classesFinite : Fintype ClassId]
  [classesRepr : Repr ClassId]
  [classesBEq : BEq ClassId]

  -- TODO consider grouping these fields in a struct so that all default values can be provided
  FunctionId : Type := Empty
  FunctionArgs : FunctionId → SomeType := fun _ => ⟨UUnit⟩
  FunctionObjectArgNames : FunctionId → Type := fun _ => UUnit
  FunctionObjectArgClass : {f : FunctionId} → FunctionObjectArgNames f → ClassId
  [objectArgNamesEnum (f : FunctionId) : FinEnum (FunctionObjectArgNames f)]
  [objectArgNamesBEq (f : FunctionId) : BEq (FunctionObjectArgNames f)]
  [functionsFinite : FinEnum FunctionId]
  [functionsRepr : Repr FunctionId]
  [functionsBEq : BEq FunctionId]

  /-- The arguments for the intent member logic are UUnit.unit. -/
  IntentId : Type := Empty
  [intentsFinite : FinEnum IntentId]
  [intentsRepr : Repr IntentId]
  [intentsBEq : BEq IntentId]

namespace EcosystemLabel

open Class

/-- Singleton ecosystem: An ecosystem with a single class, no functions and no intents -/
def singleton (l : Label) : EcosystemLabel where
  name := l.name

  ClassId := UUnit
  classes := fun _ => l

  FunctionObjectArgClass := fun _ => UUnit.unit
  objectArgNamesEnum := fun f => f.elim
  objectArgNamesBEq := fun f => f.elim


def ClassId.label {lab : EcosystemLabel} (classId : lab.ClassId) : Label :=
  lab.classes classId

def ClassId.MemberId {lab : EcosystemLabel} (c : lab.ClassId) : Type := c.label.MemberId

inductive MemberId (lab : EcosystemLabel) where
  | functionId (funId : lab.FunctionId)
  | intentId (intentId : lab.IntentId)
  | classMember {classId : lab.ClassId} (memId : classId.MemberId)
  /-- Signifies an "always false" member logic. This is used for the member
    logic field of app data, in the created case. It is important that "dummy"
    member logic indicator for the created case always returns false – otherwise
    one could circumvent method logic checks by providing the dummy member logic
    indicator. This could also be represented by an `Option` type in app data,
    but having explicit `falseLogicId` makes its intended behaviour clear. -/
  | falseLogicId

instance ClassId.MemberId.hasTypeRep {lab : EcosystemLabel} {c : lab.ClassId} : TypeRep c.MemberId := Label.MemberId.hasTypeRep c.label

instance ClassId.MemberId.hasBEq {lab : EcosystemLabel} {c : lab.ClassId} : BEq c.MemberId := Label.MemberId.hasBEq

instance MemberId.hasBEq {lab : EcosystemLabel} : BEq (EcosystemLabel.MemberId lab) where
  beq a b :=
    match a, b with
    | functionId c1, functionId c2 => lab.functionsBEq.beq c1 c2
    | functionId _, _ => false
    | _, functionId _ => false
    | classMember c1, classMember c2 => c1 === c2
    | classMember _, _ => false
    | _, classMember _ => false
    | intentId i1, intentId i2 => lab.intentsBEq.beq i1 i2
    | intentId _, _ => false
    | _, intentId _ => false
    | falseLogicId, falseLogicId => true

def FunctionId.Args {lab : EcosystemLabel} (functionId : lab.FunctionId) : SomeType :=
  lab.FunctionArgs functionId

def FunctionId.ObjectArgNames {lab : EcosystemLabel} (functionId : lab.FunctionId) : Type :=
  lab.FunctionObjectArgNames functionId

def FunctionId.objectArgNames {lab : EcosystemLabel} (functionId : lab.FunctionId) : List functionId.ObjectArgNames :=
  (lab.objectArgNamesEnum functionId).toList

def FunctionId.ObjectArgNames.classId {lab : EcosystemLabel} {functionId : lab.FunctionId} (argName : functionId.ObjectArgNames) : lab.ClassId :=
  lab.FunctionObjectArgClass argName

/-- Returns the index of an object argument -/
def FunctionId.ObjectArgNames.ix {lab : EcosystemLabel} {functionId : lab.FunctionId} (argName : functionId.ObjectArgNames) : Fin (lab.objectArgNamesEnum functionId).card :=
  (lab.objectArgNamesEnum functionId).equiv.toFun argName

def FunctionId.numObjectArgs {lab : EcosystemLabel} {functionId : lab.FunctionId} : Nat :=
  (lab.objectArgNamesEnum functionId).card

def FunctionId.argsClasses {lab : EcosystemLabel} (functionId : lab.FunctionId) : List lab.ClassId :=
  let getArg (a : functionId.ObjectArgNames) : lab.ClassId := lab.FunctionObjectArgClass a
  List.map getArg functionId.objectArgNames

def MemberId.Args {lab : EcosystemLabel} (memberId : MemberId lab) : SomeType :=
  match memberId with
  | functionId f => lab.FunctionArgs f
  | classMember m => Label.MemberId.Args m
  | intentId _ => ⟨UUnit⟩
  | falseLogicId => ⟨UUnit⟩

def IntentId.fromIntentLabel {lab : EcosystemLabel} (intentLabel : String) : Option lab.IntentId :=
  (@FinEnum.toList lab.IntentId lab.intentsFinite).find? fun intentId =>
    (@repr _ (lab.intentsRepr) intentId).pretty == intentLabel

instance {lab : EcosystemLabel} {classId : lab.ClassId}
  : CoeHead classId.label.ConstructorId classId.MemberId where
  coe := .constructorId

instance {lab : EcosystemLabel} {classId : lab.ClassId}
  : CoeHead classId.label.MethodId classId.MemberId where
  coe := .methodId

instance {lab : EcosystemLabel} {classId : lab.ClassId}
  : CoeHead classId.label.DestructorId classId.MemberId where
  coe := .destructorId

instance {lab : EcosystemLabel}
  : CoeHead lab.IntentId lab.MemberId where
  coe := .intentId

def FunctionId.Selfs {lab : EcosystemLabel} (functionId : lab.FunctionId) : Type :=
  (argName : lab.FunctionObjectArgNames functionId) → Object (lab.FunctionObjectArgClass argName).label

end EcosystemLabel
