import AVM

namespace Applib

open AVM

macro "noIntents" lab:ident clab:ident : term => `(fun _ h => by simp [$lab:ident, Ecosystem.Label.ClassId.label, Ecosystem.Label.singleton, $clab:ident] at h)
macro "noDestructors" : term => `(fun x => Empty.elim x)
macro "noFunctions" : term => `(fun x => Empty.elim x)
macro "noMethods" : term => `(fun x => Empty.elim x)

class IsObject (s : Type) where
  label : Class.Label
  toObject : s → Object label
  fromObject : Object label → Option s
  roundTrip : fromObject ∘ toObject = some

structure AnObject where
  {ty : Type}
  [isObject : IsObject ty]
  obj : ty

def AnObject.toSomeObject (g : AnObject) : SomeObject :=
  let i : IsObject g.ty := g.isObject
  (i.toObject g.obj).toSomeObject

instance {ty : Type} [IsObject ty] : CoeHead ty AnObject where
  coe (obj : ty) := {obj}

def defMethod (cl : Type) [i : IsObject cl] {methodId : i.label.MethodId}
 (body : (self : cl) → methodId.Args.type → List AnObject)
 (invariant : (self : cl) → methodId.Args.type → Bool := fun _ _ => true)
 : Class.Method methodId where
    invariant (self : Object i.label) (args : methodId.Args.type) :=
      let try self' := i.fromObject self
      invariant self' args
    created (self : Object i.label) (args : methodId.Args.type) :=
      let try self' := i.fromObject self
      List.map AnObject.toSomeObject (body self' args)

def defConstructor {cl : Type} [i : IsObject cl] {constrId : i.label.ConstructorId}
 (body : constrId.Args.type → cl)
 (invariant : constrId.Args.type → Bool := fun _ => true)
 : Class.Constructor constrId where
    invariant (args : constrId.Args.type) := invariant args
    created (args : constrId.Args.type) := i.toObject (body args)

def defDestructor {cl : Type} [i : IsObject cl] {destructorId : i.label.DestructorId}
 (invariant : (self : cl) -> destructorId.Args.type → Bool := fun _ _ => true)
 : Class.Destructor destructorId where
    invariant (self : Object i.label) (args : destructorId.Args.type) :=
      let try self' := i.fromObject self
      invariant self' args

structure ObjectArgInfo
  (label : Ecosystem.Label)
  (funId : label.FunctionId)
  (argName : label.FunctionObjectArgNames funId)
  : Type 1 where
  type : Type
  [isObject : IsObject type]
  withLabel : isObject.label = (label.FunctionObjectArgClass argName).label := by rfl

def ObjectArgs
  (lab : Ecosystem.Label)
  (funId : lab.FunctionId)
  (argsInfo : (a : funId.ObjectArgNames) → ObjectArgInfo lab funId a)
  : Type
  := (a : funId.ObjectArgNames) → (argsInfo a).type

structure DestroyableObject where
  anObject : AnObject
  key : Anoma.NullifierKey := Anoma.NullifierKey.universal

structure FunctionResult where
  created : List AnObject := []
  destroyed : List DestroyableObject := []

def FunctionResult.toAVM (r : FunctionResult) : AVM.FunctionResult where
  created := r.created.map (·.toSomeObject)
  destroyed := r.destroyed.map (fun d => d.anObject.toSomeObject.toConsumable false d.key)

def defFunction
  (lab : Ecosystem.Label)
  (funId : lab.FunctionId)
  (argsInfo : (a : funId.ObjectArgNames) → ObjectArgInfo lab funId a)
  (body : ObjectArgs lab funId argsInfo → funId.Args.type → FunctionResult)
  (invariant : ObjectArgs lab funId argsInfo → funId.Args.type → Bool := fun _ _ => true)
  : Function funId where
  body (selves : funId.Selves) (args : funId.Args.type) : AVM.FunctionResult :=
    match FinEnum.decImageOption' (enum := lab.objectArgNamesEnum funId) (getArg selves) with
    | none => {created := [], destroyed := []}
    | some (p : (argName : funId.ObjectArgNames) → (argsInfo argName).type) => (body p args).toAVM
  invariant (selves : funId.Selves) (args : funId.Args.type) : Bool :=
    match FinEnum.decImageOption' (enum := lab.objectArgNamesEnum funId) (getArg selves) with
    | none => false
    | some (p : (argName : funId.ObjectArgNames) → (argsInfo argName).type) => invariant p args
  where
  getArg (selves : funId.Selves) (argName : funId.ObjectArgNames) : Option (argsInfo argName).type :=
    (argsInfo argName).isObject.fromObject
    (by rw [(argsInfo argName).withLabel]
        exact selves argName)
