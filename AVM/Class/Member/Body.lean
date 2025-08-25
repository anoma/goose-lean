import AVM.Object
import AVM.Class.Label
import AVM.Ecosystem.Label
import AVM.Task.Parameters

namespace AVM.Class

/-- The parameters `params` represent objects fetched and new object ids
  generated in the body before the current statement. -/
inductive Member.Body.{u} (lab : Ecosystem.Label) (ReturnType : Type u) : Task.Parameters.{u} → Type (u + 1) where
  | constructor {params : Task.Parameters} (cid : lab.ClassId) (constrId : cid.label.ConstructorId) (args : params.Product → constrId.Args.type) (next : Member.Body lab ReturnType params.snocGenId) : Member.Body lab ReturnType params
  | destructor {params : Task.Parameters} (cid : lab.ClassId) (destrId : cid.label.DestructorId) (selfId : params.Product → ObjectId) (args : params.Product → destrId.Args.type) (next : Member.Body lab ReturnType params) : Member.Body lab ReturnType params
  | method {params : Task.Parameters} (cid : lab.ClassId) (methodId : cid.label.MethodId) (selfId : params.Product → ObjectId) (args : params.Product → methodId.Args.type) (next : Member.Body lab ReturnType params) : Member.Body lab ReturnType params
  | fetch {params : Task.Parameters} (objId : params.Product → TypedObjectId) (next : Member.Body lab ReturnType (params.snocFetch objId)) : Member.Body lab ReturnType params
  | return {params : Task.Parameters} (val : params.Product → ReturnType) : Member.Body lab ReturnType params

/-- All body parameters - the parameters at the point of the return statement. -/
def Member.Body.params {lab ReturnType params} (body : Member.Body lab ReturnType params) : Task.Parameters :=
  match body with
  | .constructor _ _ _ next => next.params
  | .destructor _ _ _ _ next => next.params
  | .method _ _ _ _ next => next.params
  | .fetch _ next => next.params
  | .return _ => params

def Member.Body.returnValue {lab ReturnType params} (body : Member.Body lab ReturnType params) (vals : body.params.Product) : ReturnType :=
  match body with
  | .constructor _ _ _ next => next.returnValue vals
  | .destructor _ _ _ _ next => next.returnValue vals
  | .method _ _ _ _ next => next.returnValue vals
  | .fetch _ next => next.returnValue vals
  | .return val => val vals

def Member.Body.prefixProduct {lab ReturnType params} (body : Member.Body lab ReturnType params) (vals : body.params.Product)
  : params.Product :=
  match body with
  | .constructor _ _ _ next =>
    prefixProduct next vals |> Task.Parameters.Values.dropLastGenId
  | .destructor _ _ _ _ next => prefixProduct next vals
  | .method _ _ _ _ next => prefixProduct next vals
  | .fetch _ next =>
    prefixProduct next vals |> Task.Parameters.Values.dropLastFetch
  | .return _ => vals
