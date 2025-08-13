/-
Universe‑polymorphic HList indexed by a list of types.
Works with core + mathlib4. Partly generated with GPT-5.
-/

/-- Heterogeneous list whose element types are tracked by `ts : List (Type u)`. -/
inductive HList.{u} : List (Type u) → Type (u+1) where
  | nil  : HList []
  | cons : {α : Type u} → {ts : List (Type u)} → α → HList ts → HList (α :: ts)

namespace HList

instance instInhabited {ts} (h : ts = [] := by rfl) : Inhabited (HList ts) where
  default := cast (by rw [h]) HList.nil

def length {ts : List (Type u)} (_ : HList ts) : Nat :=
  ts.length

def head {α : Type u} {ts : List (Type u)} : HList (α :: ts) → α
  | .cons x _ => x

def tail {α : Type u} {ts : List (Type u)} : HList (α :: ts) → HList ts
  | .cons _ xs => xs

/-- Append two heterogeneous lists. -/
def append : {ts us : List (Type u)} → HList ts → HList us → HList (ts ++ us)
  | [],  _, .nil, ys => ys
  | _ :: _, _, .cons x xs, ys => .cons x (append xs ys)

/--
Indexing by `Fin ts.length`. The result type is the *type at that index*,
i.e. `ts.get i : Type u`. We return a value in that type.
-/
def get :
    {ts : List (Type u)} →
    (xs : HList ts) →
    (i : Fin ts.length) →
    ts.get i
  | [], .nil, i => nomatch i  -- impossible
  | _ :: _, .cons x _xs, ⟨0, _⟩ => x
  | _ :: ts, .cons _ xs, ⟨i+1, h⟩ =>
      have : i < ts.length := Nat.lt_of_succ_lt_succ h
      get xs ⟨i, this⟩

/--
Map each element through a type constructor `F : Type u → Type v` using a
uniform “natural transformation” `f : ∀ {α}, α → F α`.
Resulting `HList` is indexed by `ts.map F`.
-/
def map {F : Type u → Type v}
    (f : ∀ {α : Type u}, α → F α) :
    {ts : List (Type u)} → HList ts → HList (ts.map F)
  | [], .nil => .nil
  | _ :: _, .cons x xs  => .cons (f x) (map f xs)

/--
Zip two `HList`s with a uniform binary function.
-/
def zipWith.{u, v, w} {R : Type u → Type v → Type w}
    (f : ∀ {α β}, α → β → R α β) :
    {ts : List (Type u)} → {us : List (Type v)} →
    HList.{u} ts → HList.{v} us → HList.{w} (List.zipWith R ts us)
  | [],        [],        .nil,        .nil        => .nil
  | _ :: ts,   _ :: us,   .cons x xs,  .cons y ys  =>
      .cons (f x y) (zipWith (R := R) f xs ys)
  | [],        _,        _,        _ => .nil
  | _,        [],        _,        _ => cast (by rw [List.zipWith_nil_right]) HList.nil

def zip.{u, v} :
    {ts : List (Type u)} → {us : List (Type v)} →
    HList.{u} ts → HList.{v} us → HList.{max u v} (List.zipWith (fun α β => α × β) ts us) :=
  zipWith (R := fun α β => α × β) (fun x y => (x, y))
