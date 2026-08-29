/-
Copyright (c) 2023 Antoine Labelle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Labelle
-/
module

public import Mathlib.Combinatorics.Quiver.Cast
public import Mathlib.Combinatorics.Quiver.Symmetric

/-!
# Single-object quiver

Single object quiver with a given arrows type.

## Main definitions

Given a type `α`, `SingleObj α` is the `Unit` type, whose single object is called `star α`, with
`Quiver` structure such that `star α ⟶ star α` is the type `α`.
An element `x : α` can be reinterpreted as an element of `star α ⟶ star α` using
`toHom`.
More generally, a list of elements of `a` can be reinterpreted as a path from `star α` to
itself using `pathEquivList`.
-/

@[expose] public section

namespace Quiver

/-- Type tag on `Unit` used to define single-object quivers. -/
@[nolint unusedArguments, implicit_reducible]
/--
Definition of `SingleObj` / `SingleObj` 的定义

English:
definition SingleObj
  signature: (_ : Type*)
  body: Unit
deriving Unique

中文:
定义 SingleObj
  签名: (_ : 类型)
  定义体: Unit
deriving Unique
-/
def SingleObj (_ : Type*) : Type :=
  Unit
deriving Unique

namespace SingleObj

variable (α β γ : Type*)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Quiver (SingleObj α)
  body: ⟨fun _ _ => α⟩

中文:
实例 :
  签名: 箭图 (SingleObj α)
  定义体: ⟨fun _ _ => α⟩
-/
instance : Quiver (SingleObj α) :=
  ⟨fun _ _ => α⟩

/--
Definition of `star` / `star` 的定义

English:
definition star
  signature: : SingleObj α
  body: default

中文:
定义 star
  签名: : SingleObj α
  定义体: default
-/
def star : SingleObj α := default

variable {α β γ}

/--
lemma `ext` / 引理 `ext`

English:
lemma ext
  given: {x y : SingleObj α}
  statement: x = y
  proof: Unit.ext x y

中文:
引理 ext
  条件: {x y : SingleObj α}
  结论: x = y
  证明: Unit.ext x y

Depends on / 依赖: Unit.ext
-/
lemma ext {x y : SingleObj α} : x = y := Unit.ext x y

-- See note [reducible non-instances]
/--
Definition of `hasReverse` / `hasReverse` 的定义

English:
abbreviation hasReverse
  signature: (rev : α -> α)
  body: ⟨rev⟩

中文:
缩写 hasReverse
  签名: (rev : α -> α)
  定义体: ⟨rev⟩
-/
abbrev hasReverse (rev : α -> α) : HasReverse (SingleObj α) := ⟨rev⟩

-- See note [reducible non-instances]
/--
Definition of `hasInvolutiveReverse` / `hasInvolutiveReverse` 的定义

English:
abbreviation hasInvolutiveReverse
  signature: (rev : α -> α) (h : Function.Involutive rev)
  body: hasReverse rev
  inv' := h

中文:
缩写 hasInvolutiveReverse
  签名: (rev : α -> α) (h : 函数.对合 rev)
  定义体: hasReverse rev
  inv' := h

Depends on / 依赖: hasReverse
-/
abbrev hasInvolutiveReverse (rev : α -> α) (h : Function.Involutive rev) :
    HasInvolutiveReverse (SingleObj α) where
  toHasReverse := hasReverse rev
  inv' := h

/-- The type of arrows from `star α` to itself is equivalent to the original type `α`. -/
@[simps!]
/--
Definition of `toHom` / `toHom` 的定义

English:
definition toHom
  signature: : α ≃ (star α ⟶ star α)
  body: Equiv.refl _

中文:
定义 toHom
  签名: : α ≃ (star α ⟶ star α)
  定义体: Equiv.refl _

Depends on / 依赖: Equiv.refl
-/
def toHom : α ≃ (star α ⟶ star α) :=
  Equiv.refl _

/-- Prefunctors between two `SingleObj` quivers correspond to functions between the corresponding
arrows types.
-/
@[simps]
/--
Definition of `toPrefunctor` / `toPrefunctor` 的定义

English:
definition toPrefunctor
  signature: : (α -> β) ≃ SingleObj α ⥤q SingleObj β where
  body: ⟨id, f⟩
  invFun f a := f.map (toHom a)

中文:
定义 toPrefunctor
  签名: : (α -> β) ≃ SingleObj α ⥤q SingleObj β where
  定义体: ⟨id, f⟩
  invFun f a := f.map (toHom a)
-/
def toPrefunctor : (α -> β) ≃ SingleObj α ⥤q SingleObj β where
  toFun f := ⟨id, f⟩
  invFun f a := f.map (toHom a)

/--
theorem `toPrefunctor_id` / 定理 `toPrefunctor_id`

English:
theorem toPrefunctor_id
  statement: toPrefunctor id = 𝟭q (SingleObj α)
  proof: rfl

@[simp]

中文:
定理 toPrefunctor_id
  结论: toPrefunctor id = 𝟭q (SingleObj α)
  证明: rfl

@[simp]
-/
theorem toPrefunctor_id : toPrefunctor id = 𝟭q (SingleObj α) :=
  rfl

@[simp]
/--
theorem `toPrefunctor_symm_id` / 定理 `toPrefunctor_symm_id`

English:
theorem toPrefunctor_symm_id
  statement: toPrefunctor.symm (𝟭q (SingleObj α)) = id
  proof: rfl

中文:
定理 toPrefunctor_symm_id
  结论: toPrefunctor.symm (𝟭q (SingleObj α)) = id
  证明: rfl
-/
theorem toPrefunctor_symm_id : toPrefunctor.symm (𝟭q (SingleObj α)) = id :=
  rfl

/--
theorem `toPrefunctor_comp` / 定理 `toPrefunctor_comp`

English:
theorem toPrefunctor_comp
  given: (f : α -> β) (g : β -> γ)
  proof: rfl

@[simp]

中文:
定理 toPrefunctor_comp
  条件: (f : α -> β) (g : β -> γ)
  证明: rfl

@[simp]
-/
theorem toPrefunctor_comp (f : α -> β) (g : β -> γ) :
    toPrefunctor (g ∘ f) = toPrefunctor f ⋙q toPrefunctor g :=
  rfl

@[simp]
/--
theorem `toPrefunctor_symm_comp` / 定理 `toPrefunctor_symm_comp`

English:
theorem toPrefunctor_symm_comp
  given: (f : SingleObj α ⥤q SingleObj β) (g : SingleObj β ⥤q SingleObj γ)
  proof: by
  simp only [Equiv.symm_apply_eq, toPrefunctor_comp, Equiv.apply_symm_apply]

中文:
定理 toPrefunctor_symm_comp
  条件: (f : SingleObj α ⥤q SingleObj β) (g : SingleObj β ⥤q SingleObj γ)
  证明: by
  simp only [Equiv.symm_apply_eq, toPrefunctor_comp, Equiv.apply_symm_apply]

Depends on / 依赖: Equiv.apply_symm_apply, Equiv.symm_apply_eq, apply_symm_apply, symm_apply_eq, toPrefunctor_comp
-/
theorem toPrefunctor_symm_comp (f : SingleObj α ⥤q SingleObj β) (g : SingleObj β ⥤q SingleObj γ) :
    toPrefunctor.symm (f ⋙q g) = toPrefunctor.symm g ∘ toPrefunctor.symm f := by
  simp only [Equiv.symm_apply_eq, toPrefunctor_comp, Equiv.apply_symm_apply]

/--
Definition of `pathToList` / `pathToList` 的定义

English:
definition pathToList
  signature: : forall {x : SingleObj α}, Path (star α) x -> List α

中文:
定义 pathToList
  签名: : 对任意 {x : SingleObj α}, 道路 (star α) x -> 列表 α
-/
def pathToList : forall {x : SingleObj α}, Path (star α) x -> List α
  | _, Path.nil => []
  | _, Path.cons p a => a :: pathToList p

/-- Auxiliary definition for `quiver.SingleObj.pathEquivList`.
Converts a list of elements of type `α` into a path in the quiver `SingleObj α`.
-/
@[simp]
/--
Definition of `listToPath` / `listToPath` 的定义

English:
definition listToPath
  signature: : List α -> Path (star α) (star α)

中文:
定义 listToPath
  签名: : 列表 α -> 道路 (star α) (star α)
-/
def listToPath : List α -> Path (star α) (star α)
  | [] => Path.nil
  | a :: l => (listToPath l).cons a

set_option backward.isDefEq.respectTransparency false in
/--
theorem `listToPath_pathToList` / 定理 `listToPath_pathToList`

English:
theorem listToPath_pathToList
  given: {x : SingleObj α} (p : Path (star α) x)
  proof: by
  induction p with
  | nil => rfl
  | cons _ _ ih => dsimp [pathToList] at *; rw [ih]

中文:
定理 listToPath_pathToList
  条件: {x : SingleObj α} (p : 道路 (star α) x)
  证明: by
  induction p with
  | nil => rfl
  | cons _ _ ih => dsimp [pathToList] at *; rw [ih]

Depends on / 依赖: pathToList
-/
theorem listToPath_pathToList {x : SingleObj α} (p : Path (star α) x) :
    listToPath (pathToList p) = p.cast rfl ext := by
  induction p with
  | nil => rfl
  | cons _ _ ih => dsimp [pathToList] at *; rw [ih]

/--
theorem `pathToList_listToPath` / 定理 `pathToList_listToPath`

English:
theorem pathToList_listToPath
  given: (l : List α)
  statement: pathToList (listToPath l) = l
  proof: by
  induction l with
  | nil => rfl
  | cons a l ih => change a :: pathToList (listToPath l) = a :: l; rw [ih]

中文:
定理 pathToList_listToPath
  条件: (l : 列表 α)
  结论: pathToList (listToPath l) = l
  证明: by
  induction l with
  | nil => rfl
  | cons a l ih => change a :: pathToList (listToPath l) = a :: l; rw [ih]

Depends on / 依赖: listToPath, pathToList
-/
theorem pathToList_listToPath (l : List α) : pathToList (listToPath l) = l := by
  induction l with
  | nil => rfl
  | cons a l ih => change a :: pathToList (listToPath l) = a :: l; rw [ih]

/--
Definition of `pathEquivList` / `pathEquivList` 的定义

English:
definition pathEquivList
  signature: : Path (star α) (star α) ≃ List α
  body: ⟨pathToList, listToPath, fun p => listToPath_pathToList p, pathToList_listToPath⟩

@[simp]

中文:
定义 pathEquivList
  签名: : 道路 (star α) (star α) ≃ 列表 α
  定义体: ⟨pathToList, listToPath, fun p => listToPath_pathToList p, pathToList_listToPath⟩

@[simp]

Depends on / 依赖: listToPath, listToPath_pathToList, pathToList, pathToList_listToPath
-/
def pathEquivList : Path (star α) (star α) ≃ List α :=
  ⟨pathToList, listToPath, fun p => listToPath_pathToList p, pathToList_listToPath⟩

@[simp]
/--
theorem `pathEquivList_nil` / 定理 `pathEquivList_nil`

English:
theorem pathEquivList_nil
  statement: pathEquivList Path.nil = ([] : List α)
  proof: rfl

@[simp]

中文:
定理 pathEquivList_nil
  结论: pathEquivList 道路.nil = ([] : 列表 α)
  证明: rfl

@[simp]
-/
theorem pathEquivList_nil : pathEquivList Path.nil = ([] : List α) :=
  rfl

@[simp]
/--
theorem `pathEquivList_cons` / 定理 `pathEquivList_cons`

English:
theorem pathEquivList_cons
  given: (p : Path (star α) (star α)) (a : star α ⟶ star α)
  proof: rfl

@[simp]

中文:
定理 pathEquivList_cons
  条件: (p : 道路 (star α) (star α)) (a : star α ⟶ star α)
  证明: rfl

@[simp]
-/
theorem pathEquivList_cons (p : Path (star α) (star α)) (a : star α ⟶ star α) :
    pathEquivList (Path.cons p a) = a :: pathToList p :=
  rfl

@[simp]
/--
theorem `pathEquivList_symm_nil` / 定理 `pathEquivList_symm_nil`

English:
theorem pathEquivList_symm_nil
  statement: pathEquivList.symm ([] : List α) = Path.nil
  proof: rfl

@[simp]

中文:
定理 pathEquivList_symm_nil
  结论: pathEquivList.symm ([] : 列表 α) = 道路.nil
  证明: rfl

@[simp]
-/
theorem pathEquivList_symm_nil : pathEquivList.symm ([] : List α) = Path.nil :=
  rfl

@[simp]
/--
theorem `pathEquivList_symm_cons` / 定理 `pathEquivList_symm_cons`

English:
theorem pathEquivList_symm_cons
  given: (l : List α) (a : α)
  proof: rfl

中文:
定理 pathEquivList_symm_cons
  条件: (l : 列表 α) (a : α)
  证明: rfl
-/
theorem pathEquivList_symm_cons (l : List α) (a : α) :
    pathEquivList.symm (a :: l) = Path.cons (pathEquivList.symm l) a :=
  rfl

end SingleObj

end Quiver
