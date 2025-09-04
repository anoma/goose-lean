import AVM.Object
import AVM.Class.Label
import AVM.Ecosystem.Label
import AVM.Task.Parameters

namespace AVM

/-- The parameters `params` represent objects fetched and new object ids
  generated in the body before the current statement. -/
inductive Program'.{u} (lab : Ecosystem.Label) (ReturnType : Type u) : Task.Parameters.{u} → Type (u + 1) where
  | constructor
      {params : Task.Parameters}
      (cid : lab.ClassId)
      (constrId : cid.label.ConstructorId)
      (args : params.Product → constrId.Args.type)
      (next : Program' lab ReturnType params.snocGenId)
      : Program' lab ReturnType params
  | destructor
      {params : Task.Parameters}
      (cid : lab.ClassId)
      (destrId : cid.label.DestructorId)
      (selfId : params.Product → ObjectId)
      (args : params.Product → destrId.Args.type)
      (next : Program' lab ReturnType params)
      : Program' lab ReturnType params
  | method
      {params : Task.Parameters}
      (cid : lab.ClassId)
      (methodId : cid.label.MethodId)
      (selfId : params.Product → ObjectId)
      (args : params.Product → methodId.Args.type)
      (next : Program' lab ReturnType params)
      : Program' lab ReturnType params
  | fetch
      {params : Task.Parameters}
      (objId : params.Product → TypedObjectId)
      (next : Program' lab ReturnType (params.snocFetch objId))
      : Program' lab ReturnType params
  | return
      {params : Task.Parameters}
      (val : params.Product → ReturnType)
      : Program' lab ReturnType params

/-- All body parameters - the parameters at the point of the return statement. -/
def Program'.params {lab ReturnType params} (body : Program' lab ReturnType params) : Task.Parameters :=
  match body with
  | .constructor _ _ _ next => next.params
  | .destructor _ _ _ _ next => next.params
  | .method _ _ _ _ next => next.params
  | .fetch _ next => next.params
  | .return _ => params

def Program'.returnValue {lab ReturnType params} (body : Program' lab ReturnType params) (vals : body.params.Product) : ReturnType :=
  match body with
  | .constructor _ _ _ next => next.returnValue vals
  | .destructor _ _ _ _ next => next.returnValue vals
  | .method _ _ _ _ next => next.returnValue vals
  | .fetch _ next => next.returnValue vals
  | .return val => val vals

def Program'.prefixProduct {lab ReturnType params} (body : Program' lab ReturnType params) (vals : body.params.Product)
  : params.Product :=
  match body with
  | .constructor _ _ _ next =>
    prefixProduct next vals |> Task.Parameters.Values.dropLastGenId
  | .destructor _ _ _ _ next => prefixProduct next vals
  | .method _ _ _ _ next => prefixProduct next vals
  | .fetch _ next =>
    prefixProduct next vals |> Task.Parameters.Values.dropLastFetch
  | .return _ => vals

def Program'.map {lab : Ecosystem.Label} {A B : Type u} {params : Task.Parameters} (f : A → B) (body : Program' lab A params) : Program' lab B params :=
  match body with
  | .constructor cid constrId args next =>
    .constructor cid constrId args (map f next)
  | .destructor cid destrId selfId args next =>
    .destructor cid destrId selfId args (map f next)
  | .method cid methodId selfId args next =>
    .method cid methodId selfId args (map f next)
  | .fetch objId next =>
    .fetch objId (map f next)
  | .return val =>
    .return (fun p => f (val p))

def Program (lab : Ecosystem.Label) (ReturnType : Type u) : Type (u + 1) :=
  Program' lab ReturnType Task.Parameters.empty
