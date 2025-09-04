import AVM
import Applib.Surface.Object
import Applib.Surface.Reference

namespace Applib

open AVM

inductive Program.Sized (lab : Ecosystem.Label) : (ReturnType : Type) → Nat → Type 2 where
  | create
    {ReturnType : Type}
    {n : Nat}
    (C : Type)
    (cid : lab.ClassId)
    (constrId : cid.label.ConstructorId)
    (args : constrId.Args.type)
    (next : ObjectId → Program.Sized lab ReturnType n)
    : Program.Sized lab ReturnType (n + 1)
  | destroy
    {ReturnType : Type}
    {n : Nat}
    (cid : lab.ClassId)
    (destrId : cid.label.DestructorId)
    (selfId : ObjectId)
    (args : destrId.Args.type)
    (next : Program.Sized lab ReturnType n)
    : Program.Sized lab ReturnType (n + 1)
  | call
    {ReturnType : Type}
    {n : Nat}
    (cid : lab.ClassId)
    (methodId : cid.label.MethodId)
    (selfId : ObjectId)
    (args : methodId.Args.type)
    (next : Program.Sized lab ReturnType n)
    : Program.Sized lab ReturnType (n + 1)
  | fetch
    {ReturnType : Type}
    {n : Nat}
    (C : Type)
    [i : IsObject C]
    (objId : ObjectId)
    (next : C → Program.Sized lab ReturnType n)
    : Program.Sized lab ReturnType (n + 1)
  | invoke
    {ReturnType : Type}
    {n : Nat}
    {α : Type}
    (prog : Program.Sized lab α n)
    (next : α → Program.Sized lab ReturnType n)
    : Program.Sized lab ReturnType (n + 1)
  | return
    {ReturnType : Type}
    {n : Nat}
    (val : ReturnType)
    : Program.Sized lab ReturnType n

def Program lab ReturnType := Σ n, Program.Sized lab ReturnType n

def Program.Sized.toAVM {n : Nat} {lab ReturnType} (prog : Program.Sized lab ReturnType n) : AVM.Program.Sized lab ReturnType n :=
  match prog with
  | .create _ cid constrId args next =>
    .constructor cid constrId args (fun objId => toAVM (next objId))
  | .destroy cid destrId selfId args next =>
    .destructor cid destrId selfId args (toAVM next)
  | .call cid methodId selfId args next =>
    .method cid methodId selfId args (toAVM next)
  | @fetch _ _ _ _ i objId next =>
    .fetch ⟨i.classId.label, objId⟩ (fun obj => toAVM (next (i.fromObject obj.data)))
  | .invoke p next =>
    .invoke (toAVM p) (fun x => toAVM (next x))
  | .return val =>
    .return val

def Program.Sized.map {n : Nat} {lab : Ecosystem.Label} {A B : Type} (f : A → B) (prog : Program.Sized lab A n) : Program.Sized lab B n :=
  match prog with
  | .create C cid constrId args next =>
    .create C cid constrId args (fun x => map f (next x))
  | .destroy cid destrId selfId args next =>
    .destroy cid destrId selfId args (map f next)
  | .call cid methodId selfId args next =>
    .call cid methodId selfId args (map f next)
  | @fetch _ _ _ C _ objId next =>
    .fetch C objId (fun x => map f (next x))
  | .invoke p next =>
    .invoke p (fun x => map f (next x))
  | .return val =>
    .return (f val)

def Program.Sized.lift {n m : Nat} {lab : Ecosystem.Label} {ReturnType} (prog : Program.Sized lab ReturnType n) : Program.Sized lab ReturnType (m + n) :=
  match prog with
  | .create C cid constrId args next =>
    .create C cid constrId args (fun x => lift (next x))
  | .destroy cid destrId selfId args next =>
    .destroy cid destrId selfId args (lift next)
  | .call cid methodId selfId args next =>
    .call cid methodId selfId args (lift next)
  | @fetch _ _ _ C _ objId next =>
    .fetch C objId (fun x => lift (next x))
  | .invoke p next =>
    .invoke (lift p) (fun x => lift (next x))
  | .return val =>
    .return val

def Program.Sized.lift' {n m : Nat} {lab : Ecosystem.Label} {ReturnType} (prog : Program.Sized lab ReturnType n) : Program.Sized lab ReturnType (n + m) :=
  cast (by rw [Nat.add_comm]) (Program.Sized.lift (m := m) prog)

def Program.Sized.create' {n : Nat} {ReturnType} (C : Type) [i : IsObject C] (constrId : i.classId.label.ConstructorId) (args : constrId.Args.type) (next : Reference C → Program.Sized i.label ReturnType n) : Program.Sized i.label ReturnType (n + 1) :=
  Program.Sized.create C i.classId constrId args (fun objId => next ⟨objId⟩)

def Program.Sized.destroy' {n : Nat} {ReturnType} {C : Type} (r : Reference C) [i : IsObject C] (destrId : i.classId.label.DestructorId) (args : destrId.Args.type) (next : Program.Sized i.label ReturnType n) : Program.Sized i.label ReturnType (n + 1) :=
  Program.Sized.destroy i.classId destrId r.objId args next

def Program.Sized.call' {n : Nat} {ReturnType} {C : Type} (r : Reference C) [i : IsObject C] (methodId : i.classId.label.MethodId) (args : methodId.Args.type) (next : Program.Sized i.label ReturnType n) : Program.Sized i.label ReturnType (n + 1) :=
  Program.Sized.call i.classId methodId r.objId args next

def Program.Sized.fetch' {n : Nat} {ReturnType} {lab : Ecosystem.Label} {C : Type} (r : Reference C) [i : IsObject C] (next : C → Program.Sized lab ReturnType n) : Program.Sized lab ReturnType (n + 1) :=
  Program.Sized.fetch C r.objId next

def Program.Sized.invoke' {n : Nat} {lab : Ecosystem.Label} {ReturnType α : Type} (prog : Program lab α) (next : α → Program.Sized lab ReturnType n) : Program.Sized lab ReturnType (prog.fst + n + 1) :=
  Program.Sized.invoke prog.snd.lift' (fun x => next x |>.lift)

def Program.Sized.return' {lab : Ecosystem.Label} {ReturnType} (val : ReturnType) : Program.Sized lab ReturnType 0 :=
  Program.Sized.return val

def Program.Sized.toProgram {n : Nat} {lab ReturnType} (prog : Program.Sized lab ReturnType n) : Program lab ReturnType :=
  ⟨n, prog⟩

def Program.map {lab : Ecosystem.Label} {A B : Type} (f : A → B) (prog : Program lab A) : Program lab B :=
  ⟨prog.1, prog.2.map f⟩

def Program.return {lab : Ecosystem.Label} {ReturnType} (val : ReturnType) : Program lab ReturnType :=
  ⟨0, .return val⟩

def Program.toAVM {lab : Ecosystem.Label} {ReturnType} (prog : Program lab ReturnType) : AVM.Program lab ReturnType :=
  ⟨prog.1, prog.2.toAVM⟩
