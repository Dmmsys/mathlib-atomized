/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Fintype.Defs

/-!
# Computable inverses for injective/surjective functions on finite types

## Main results

* `Function.Injective.invOfMemRange`, `Embedding.invOfMemRange`, `Fintype.bijInv`:
  computable versions of `Function.invFun`.
* `Fintype.choose`: computably obtain a witness for `ExistsUnique`.
-/

@[expose] public section

assert_not_exists Monoid

open Function

open Nat

universe u v

variable {α β γ : Type*}

section Inv

namespace Function

variable [Fintype α] [DecidableEq β]

namespace Injective

variable {f : α -> β} (hf : Function.Injective f)

/--
Definition of `invOfMemRange` / `invOfMemRange` 的定义

English:
definition invOfMemRange
  signature: : Set.range f -> α
  body: fun b =>
  Finset.choose (fun a => f a = b) Finset.univ
    ((existsUnique_congr (by simp)).mp (hf.existsUnique_of_mem_range b.property))

中文:
定义 invOfMemRange
  签名: : Set.range f -> α
  定义体: fun b =>
  Finset.choose (fun a => f a = b) Finset.univ
    ((existsUnique_congr (by simp)).mp (hf.existsUnique_of_mem_range b.property))
-/
def invOfMemRange : Set.range f -> α := fun b =>
  Finset.choose (fun a => f a = b) Finset.univ
    ((existsUnique_congr (by simp)).mp (hf.existsUnique_of_mem_range b.property))

/--
theorem `left_inv_of_invOfMemRange` / 定理 `left_inv_of_invOfMemRange`

English:
theorem left_inv_of_invOfMemRange
  given: (b : Set.range f)
  statement: f (hf.invOfMemRange b) = b
  proof: (Finset.choose_spec (fun a => f a = b) _ _).right

@[simp]

中文:
定理 left_inv_of_invOfMemRange
  条件: (b : Set.range f)
  结论: f (hf.invOfMemRange b) = b
  证明: (Finset.choose_spec (fun a => f a = b) _ _).right

@[simp]

Depends on / 依赖: Finset, Finset.choose_spec, choose_spec
-/
theorem left_inv_of_invOfMemRange (b : Set.range f) : f (hf.invOfMemRange b) = b :=
  (Finset.choose_spec (fun a => f a = b) _ _).right

@[simp]
/--
theorem `right_inv_of_invOfMemRange` / 定理 `right_inv_of_invOfMemRange`

English:
theorem right_inv_of_invOfMemRange
  given: (a : α)
  statement: hf.invOfMemRange ⟨f a, Set.mem_range_self a⟩ = a
  proof: hf (Finset.choose_spec (fun a' => f a' = f a) _ _).right

中文:
定理 right_inv_of_invOfMemRange
  条件: (a : α)
  结论: hf.invOfMemRange ⟨f a, Set.mem_range_self a⟩ = a
  证明: hf (Finset.choose_spec (fun a' => f a' = f a) _ _).right

Depends on / 依赖: Finset, Finset.choose_spec, choose_spec
-/
theorem right_inv_of_invOfMemRange (a : α) : hf.invOfMemRange ⟨f a, Set.mem_range_self a⟩ = a :=
  hf (Finset.choose_spec (fun a' => f a' = f a) _ _).right

/--
theorem `invFun_restrict` / 定理 `invFun_restrict`

English:
theorem invFun_restrict
  given: [Nonempty α]
  statement: (Set.range f).domRestrict (invFun f) = hf.invOfMemRange
  proof: by
  ext ⟨b, h⟩
  apply hf
  simp [hf.left_inv_of_invOfMemRange, @invFun_eq _ _ _ f b (Set.mem_range.mp h)]

中文:
定理 invFun_restrict
  条件: [Nonempty α]
  结论: (Set.range f).domRestrict (invFun f) = hf.invOfMemRange
  证明: by
  ext ⟨b, h⟩
  apply hf
  simp [hf.left_inv_of_invOfMemRange, @invFun_eq _ _ _ f b (Set.mem_range.mp h)]

Depends on / 依赖: Set.mem_range.mp, hf.left_inv_of_invOfMemRange, invFun_eq, left_inv_of_invOfMemRange, mem_range
-/
theorem invFun_restrict [Nonempty α] : (Set.range f).domRestrict (invFun f) = hf.invOfMemRange := by
  ext ⟨b, h⟩
  apply hf
  simp [hf.left_inv_of_invOfMemRange, @invFun_eq _ _ _ f b (Set.mem_range.mp h)]

/--
theorem `invOfMemRange_surjective` / 定理 `invOfMemRange_surjective`

English:
theorem invOfMemRange_surjective
  statement: Function.Surjective hf.invOfMemRange
  proof: fun a =>
  ⟨⟨f a, Set.mem_range_self a⟩, by simp⟩

中文:
定理 invOfMemRange_surjective
  结论: Function.Surjective hf.invOfMemRange
  证明: fun a =>
  ⟨⟨f a, Set.mem_range_self a⟩, by simp⟩
-/
theorem invOfMemRange_surjective : Function.Surjective hf.invOfMemRange := fun a =>
  ⟨⟨f a, Set.mem_range_self a⟩, by simp⟩

end Injective

namespace Embedding

variable (f : α ↪ β) (b : Set.range f)

/--
Definition of `invOfMemRange` / `invOfMemRange` 的定义

English:
definition invOfMemRange
  signature: : α
  body: f.injective.invOfMemRange b

@[simp]

中文:
定义 invOfMemRange
  签名: : α
  定义体: f.injective.invOfMemRange b

@[simp]

Depends on / 依赖: f.injective.invOfMemRange, injective, invOfMemRange
-/
def invOfMemRange : α :=
  f.injective.invOfMemRange b

@[simp]
/--
theorem `left_inv_of_invOfMemRange` / 定理 `left_inv_of_invOfMemRange`

English:
theorem left_inv_of_invOfMemRange
  statement: f (f.invOfMemRange b) = b
  proof: f.injective.left_inv_of_invOfMemRange b

@[simp]

中文:
定理 left_inv_of_invOfMemRange
  结论: f (f.invOfMemRange b) = b
  证明: f.injective.left_inv_of_invOfMemRange b

@[simp]

Depends on / 依赖: f.injective.left_inv_of_invOfMemRange, injective, left_inv_of_invOfMemRange
-/
theorem left_inv_of_invOfMemRange : f (f.invOfMemRange b) = b :=
  f.injective.left_inv_of_invOfMemRange b

@[simp]
/--
theorem `right_inv_of_invOfMemRange` / 定理 `right_inv_of_invOfMemRange`

English:
theorem right_inv_of_invOfMemRange
  given: (a : α)
  statement: f.invOfMemRange ⟨f a, Set.mem_range_self a⟩ = a
  proof: f.injective.right_inv_of_invOfMemRange a

中文:
定理 right_inv_of_invOfMemRange
  条件: (a : α)
  结论: f.invOfMemRange ⟨f a, Set.mem_range_self a⟩ = a
  证明: f.injective.right_inv_of_invOfMemRange a

Depends on / 依赖: f.injective.right_inv_of_invOfMemRange, injective, right_inv_of_invOfMemRange
-/
theorem right_inv_of_invOfMemRange (a : α) : f.invOfMemRange ⟨f a, Set.mem_range_self a⟩ = a :=
  f.injective.right_inv_of_invOfMemRange a

/--
theorem `invFun_restrict` / 定理 `invFun_restrict`

English:
theorem invFun_restrict
  given: [Nonempty α]
  statement: (Set.range f).domRestrict (invFun f) = f.invOfMemRange
  proof: by
  ext ⟨b, h⟩
  apply f.injective
  simp [f.left_inv_of_invOfMemRange, @invFun_eq _ _ _ f b (Set.mem_range.mp h)]

中文:
定理 invFun_restrict
  条件: [Nonempty α]
  结论: (Set.range f).domRestrict (invFun f) = f.invOfMemRange
  证明: by
  ext ⟨b, h⟩
  apply f.injective
  simp [f.left_inv_of_invOfMemRange, @invFun_eq _ _ _ f b (Set.mem_range.mp h)]

Depends on / 依赖: Set.mem_range.mp, f.injective, f.left_inv_of_invOfMemRange, injective, invFun_eq, left_inv_of_invOfMemRange, mem_range
-/
theorem invFun_restrict [Nonempty α] : (Set.range f).domRestrict (invFun f) = f.invOfMemRange := by
  ext ⟨b, h⟩
  apply f.injective
  simp [f.left_inv_of_invOfMemRange, @invFun_eq _ _ _ f b (Set.mem_range.mp h)]

/--
theorem `invOfMemRange_surjective` / 定理 `invOfMemRange_surjective`

English:
theorem invOfMemRange_surjective
  statement: Function.Surjective f.invOfMemRange
  proof: fun a =>
  ⟨⟨f a, Set.mem_range_self a⟩, by simp⟩

中文:
定理 invOfMemRange_surjective
  结论: Function.Surjective f.invOfMemRange
  证明: fun a =>
  ⟨⟨f a, Set.mem_range_self a⟩, by simp⟩
-/
theorem invOfMemRange_surjective : Function.Surjective f.invOfMemRange := fun a =>
  ⟨⟨f a, Set.mem_range_self a⟩, by simp⟩

end Embedding

end Function

end Inv

open Finset

namespace Fintype

section Choose

open Fintype Equiv

variable [Fintype α] (p : α -> Prop) [DecidablePred p]

/--
Definition of `chooseX` / `chooseX` 的定义

English:
definition chooseX
  signature: (hp : exists! a : α, p a)
  body: ⟨Finset.choose p univ (by simpa), Finset.choose_property _ _ _⟩

中文:
定义 chooseX
  签名: (hp : 存在! a : α, p a)
  定义体: ⟨Finset.choose p univ (by simpa), Finset.choose_property _ _ _⟩

Depends on / 依赖: Finset, Finset.choose, Finset.choose_property, choose_property
-/
def chooseX (hp : exists! a : α, p a) : { a // p a } :=
  ⟨Finset.choose p univ (by simpa), Finset.choose_property _ _ _⟩

/--
Definition of `choose` / `choose` 的定义

English:
definition choose
  signature: (hp : exists! a, p a)
  body: chooseX p hp

中文:
定义 choose
  签名: (hp : 存在! a, p a)
  定义体: chooseX p hp

Depends on / 依赖: chooseX
-/
def choose (hp : exists! a, p a) : α :=
  chooseX p hp

/--
theorem `choose_spec` / 定理 `choose_spec`

English:
theorem choose_spec
  given: (hp : exists! a, p a)
  statement: p (choose p hp)
  proof: (chooseX p hp).property

中文:
定理 choose_spec
  条件: (hp : 存在! a, p a)
  结论: p (choose p hp)
  证明: (chooseX p hp).property

Depends on / 依赖: chooseX, property
-/
theorem choose_spec (hp : exists! a, p a) : p (choose p hp) :=
  (chooseX p hp).property

/--
theorem `choose_subtype_eq` / 定理 `choose_subtype_eq`

English:
theorem choose_subtype_eq
  statement: {α : Type*} (p : α -> Prop) [Fintype { a : α // p a }] [DecidableEq α]
  proof: by
  rw [Subtype.ext_iff]; rw [Fintype.choose_spec (fun y : { a : α // p a } => (y : α) = x) _]

中文:
定理 choose_subtype_eq
  结论: {α : 类型} (p : α -> 命题) [Fintype { a : α // p a }] [DecidableEq α]
  证明: by
  rw [Subtype.ext_iff]; rw [Fintype.choose_spec (fun y : { a : α // p a } => (y : α) = x) _]

Depends on / 依赖: Fintype, Fintype.choose, Fintype.choose_spec, Subtype, Subtype.ext_iff, choose_spec, ext_iff
-/
theorem choose_subtype_eq {α : Type*} (p : α -> Prop) [Fintype { a : α // p a }] [DecidableEq α]
    (x : { a : α // p a })
    (h : exists! a : { a // p a }, (a : α) = x :=
      ⟨x, rfl, fun y hy => by simpa [Subtype.ext_iff] using hy⟩) :
    Fintype.choose (fun y : { a : α // p a } => (y : α) = x) h = x := by
  rw [Subtype.ext_iff]; rw [Fintype.choose_spec (fun y : { a : α // p a } => (y : α) = x) _]

end Choose

section BijectionInverse

variable [Fintype α] [DecidableEq β] {f : α -> β}

/--
Definition of `bijInv` / `bijInv` 的定义

English:
definition bijInv
  signature: (f_bij : Bijective f) (b : β)
  body: Fintype.choose (fun a => f a = b) (f_bij.existsUnique b)

中文:
定义 bijInv
  签名: (f_bij : Bijective f) (b : β)
  定义体: Fintype.choose (fun a => f a = b) (f_bij.existsUnique b)

Depends on / 依赖: Fintype, Fintype.choose, existsUnique, f_bij, f_bij.existsUnique
-/
def bijInv (f_bij : Bijective f) (b : β) : α :=
  Fintype.choose (fun a => f a = b) (f_bij.existsUnique b)

/--
theorem `leftInverse_bijInv` / 定理 `leftInverse_bijInv`

English:
theorem leftInverse_bijInv
  given: (f_bij : Bijective f)
  statement: LeftInverse (bijInv f_bij) f
  proof: fun a =>
  f_bij.left (choose_spec (fun a' => f a' = f a) _)

中文:
定理 leftInverse_bijInv
  条件: (f_bij : Bijective f)
  结论: LeftInverse (bijInv f_bij) f
  证明: fun a =>
  f_bij.left (choose_spec (fun a' => f a' = f a) _)
-/
theorem leftInverse_bijInv (f_bij : Bijective f) : LeftInverse (bijInv f_bij) f := fun a =>
  f_bij.left (choose_spec (fun a' => f a' = f a) _)

/--
theorem `rightInverse_bijInv` / 定理 `rightInverse_bijInv`

English:
theorem rightInverse_bijInv
  given: (f_bij : Bijective f)
  statement: RightInverse (bijInv f_bij) f
  proof: fun b =>
  choose_spec (fun a' => f a' = b) _

中文:
定理 rightInverse_bijInv
  条件: (f_bij : Bijective f)
  结论: RightInverse (bijInv f_bij) f
  证明: fun b =>
  choose_spec (fun a' => f a' = b) _
-/
theorem rightInverse_bijInv (f_bij : Bijective f) : RightInverse (bijInv f_bij) f := fun b =>
  choose_spec (fun a' => f a' = b) _

/--
theorem `bijective_bijInv` / 定理 `bijective_bijInv`

English:
theorem bijective_bijInv
  given: (f_bij : Bijective f)
  statement: Bijective (bijInv f_bij)
  proof: ⟨(rightInverse_bijInv _).injective, (leftInverse_bijInv _).surjective⟩

中文:
定理 bijective_bijInv
  条件: (f_bij : Bijective f)
  结论: Bijective (bijInv f_bij)
  证明: ⟨(rightInverse_bijInv _).injective, (leftInverse_bijInv _).surjective⟩

Depends on / 依赖: injective, leftInverse_bijInv, rightInverse_bijInv, surjective
-/
theorem bijective_bijInv (f_bij : Bijective f) : Bijective (bijInv f_bij) :=
  ⟨(rightInverse_bijInv _).injective, (leftInverse_bijInv _).surjective⟩

end BijectionInverse

end Fintype
