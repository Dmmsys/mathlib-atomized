/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.CharP.Basic
public import Mathlib.Algebra.Group.Pointwise.Set.Basic
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Order.BigOperators.Group.Multiset
public import Mathlib.Algebra.Order.Group.Nat
public import Mathlib.Data.ZMod.Defs

/-!
# Freiman homomorphisms

In this file, we define Freiman homomorphisms and isomorphisms.

An `n`-Freiman homomorphism from `A` to `B` is a function `f : α → β` such that `f '' A ⊆ B` and
`f x₁ * ... * f xₙ = f y₁ * ... * f yₙ` for all `x₁, ..., xₙ, y₁, ..., yₙ ∈ A` such that
`x₁ * ... * xₙ = y₁ * ... * yₙ`. In particular, any `MulHom` is a Freiman homomorphism.

Note a `0`- or `1`-Freiman homomorphism is simply a map, thus a `2`-Freiman homomorphism is the
first interesting case (and the most common). As `n` increases further, the property of being
an `n`-Freiman homomorphism between abelian groups becomes increasingly stronger.

An `n`-Freiman isomorphism from `A` to `B` is a function `f : α → β` bijective between `A` and `B`
such that `f x₁ * ... * f xₙ = f y₁ * ... * f yₙ ↔ x₁ * ... * xₙ = y₁ * ... * yₙ` for all
`x₁, ..., xₙ, y₁, ..., yₙ ∈ A`. In particular, any `MulEquiv` is a Freiman isomorphism.

They are of interest in additive combinatorics.

## Main declarations

* `IsMulFreimanHom`: Predicate for a function to be a multiplicative Freiman homomorphism.
* `IsAddFreimanHom`: Predicate for a function to be an additive Freiman homomorphism.
* `IsMulFreimanIso`: Predicate for a function to be a multiplicative Freiman isomorphism.
* `IsAddFreimanIso`: Predicate for a function to be an additive Freiman isomorphism.

## Main results

* `isMulFreimanHom_two`: Characterisation of `2`-Freiman homomorphisms.
* `IsMulFreimanHom.mono`: If `m ≤ n` and `f` is an `n`-Freiman homomorphism, then it is also an
  `m`-Freiman homomorphism.

## Implementation notes

In the context of combinatorics, we are interested in Freiman homomorphisms over sets which are not
necessarily closed under addition/multiplication. This means we must parametrize them with a set in
an `AddMonoid`/`Monoid` instead of the `AddMonoid`/`Monoid` itself.

## References

[Yufei Zhao, *18.225: Graph Theory and Additive Combinatorics*](https://yufeizhao.com/gtac/)

## TODO

* `MonoidHomClass.isMulFreimanHom` could be relaxed to `MulHom.toFreimanHom` by proving
  `(s.map f).prod = (t.map f).prod` directly by induction instead of going through `f s.prod`.
* Affine maps are Freiman homomorphisms.
-/

@[expose] public section

assert_not_exists Field Ideal TwoSidedIdeal

open Multiset Set
open scoped Pointwise

variable {F α β γ : Type*}

section CommMonoid
variable [CommMonoid α] [CommMonoid β] [CommMonoid γ] {A A₁ A₂ : Set α}
  {B B₁ B₂ : Set β} {C : Set γ} {f f₁ f₂ : α -> β} {g : β -> γ} {n : Nat}

/--
Definition of `IsAddFreimanHom` / `IsAddFreimanHom` 的定义

English:
structure IsAddFreimanHom
  parameters: [AddCommMonoid α] [AddCommMonoid β] (n : Nat) (A : Set α) (B : Set β)
  axioms and operations (2):
    - mapsTo : MapsTo f A B
    - map_sum_eq_map_sum(⦃s t) : Multiset α⦄ (hsA : forall ⦃x⦄, x in s -> x in A) (htA : forall ⦃x⦄, x in t -> x in A) (hs : Multiset.card s = n) (ht : Multiset.card t = n) (h : s.sum = t.sum) : (s.map f).sum = (t.map f).sum

中文:
结构 是加法Freiman态射
  参数: [加法交换幺半群 α] [加法交换幺半群 β] (n : 自然数) (A : 集合 α) (B : 集合 β)
  公理与运算 (2 个):
    - mapsTo : 映射到 f A B
    - map_sum_eq_map_sum(⦃s t) : Multiset α⦄ (hsA : 对任意 ⦃x⦄, x in s -> x in A) (htA : 对任意 ⦃x⦄, x in t -> x in A) (hs : Multiset.card s = n) (ht : Multiset.card t = n) (h : s.求和 = t.求和) : (s.map f).求和 = (t.map f).求和
-/
structure IsAddFreimanHom [AddCommMonoid α] [AddCommMonoid β] (n : Nat) (A : Set α) (B : Set β)
    (f : α -> β) : Prop where
  mapsTo : MapsTo f A B
  /-- An additive `n`-Freiman homomorphism preserves sums of `n` elements. -/
  map_sum_eq_map_sum ⦃s t : Multiset α⦄ (hsA : forall ⦃x⦄, x in s -> x in A) (htA : forall ⦃x⦄, x in t -> x in A)
    (hs : Multiset.card s = n) (ht : Multiset.card t = n) (h : s.sum = t.sum) :
    (s.map f).sum = (t.map f).sum

/-- An `n`-Freiman homomorphism from a set `A` to a set `B` is a map which preserves products of `n`
elements. -/
@[to_additive]
/--
Definition of `IsMulFreimanHom` / `IsMulFreimanHom` 的定义

English:
structure IsMulFreimanHom
  parameters: (n : Nat) (A : Set α) (B : Set β) (f : α -> β)
  axioms and operations (2):
    - mapsTo : MapsTo f A B
    - map_prod_eq_map_prod(⦃s t) : Multiset α⦄ (hsA : forall ⦃x⦄, x in s -> x in A) (htA : forall ⦃x⦄, x in t -> x in A) (hs : Multiset.card s = n) (ht : Multiset.card t = n) (h : s.prod = t.prod) : (s.map f).prod = (t.map f).prod

中文:
结构 是MulFreiman态射
  参数: (n : 自然数) (A : 集合 α) (B : 集合 β) (f : α -> β)
  公理与运算 (2 个):
    - mapsTo : 映射到 f A B
    - map_prod_eq_map_prod(⦃s t) : Multiset α⦄ (hsA : 对任意 ⦃x⦄, x in s -> x in A) (htA : 对任意 ⦃x⦄, x in t -> x in A) (hs : Multiset.card s = n) (ht : Multiset.card t = n) (h : s.乘积 = t.乘积) : (s.map f).乘积 = (t.map f).乘积
-/
structure IsMulFreimanHom (n : Nat) (A : Set α) (B : Set β) (f : α -> β) : Prop where
  mapsTo : MapsTo f A B
  /-- An `n`-Freiman homomorphism preserves products of `n` elements. -/
  map_prod_eq_map_prod ⦃s t : Multiset α⦄ (hsA : forall ⦃x⦄, x in s -> x in A) (htA : forall ⦃x⦄, x in t -> x in A)
    (hs : Multiset.card s = n) (ht : Multiset.card t = n) (h : s.prod = t.prod) :
    (s.map f).prod = (t.map f).prod

/--
Definition of `IsAddFreimanIso` / `IsAddFreimanIso` 的定义

English:
structure IsAddFreimanIso
  parameters: [AddCommMonoid α] [AddCommMonoid β] (n : Nat) (A : Set α) (B : Set β)
  axioms and operations (2):
    - bijOn : BijOn f A B
    - map_sum_eq_map_sum(⦃s t) : Multiset α⦄ (hsA : forall ⦃x⦄, x in s -> x in A) (htA : forall ⦃x⦄, x in t -> x in A) (hs : Multiset.card s = n) (ht : Multiset.card t = n) : (s.map f).sum = (t.map f).sum ↔ s.sum = t.sum

中文:
结构 是加法FreimanIso
  参数: [加法交换幺半群 α] [加法交换幺半群 β] (n : 自然数) (A : 集合 α) (B : 集合 β)
  公理与运算 (2 个):
    - bijOn : 双射限制 f A B
    - map_sum_eq_map_sum(⦃s t) : Multiset α⦄ (hsA : 对任意 ⦃x⦄, x in s -> x in A) (htA : 对任意 ⦃x⦄, x in t -> x in A) (hs : Multiset.card s = n) (ht : Multiset.card t = n) : (s.map f).求和 = (t.map f).求和 ↔ s.求和 = t.求和
-/
structure IsAddFreimanIso [AddCommMonoid α] [AddCommMonoid β] (n : Nat) (A : Set α) (B : Set β)
    (f : α -> β) : Prop where
  bijOn : BijOn f A B
  /-- An additive `n`-Freiman homomorphism preserves sums of `n` elements. -/
  map_sum_eq_map_sum ⦃s t : Multiset α⦄ (hsA : forall ⦃x⦄, x in s -> x in A) (htA : forall ⦃x⦄, x in t -> x in A)
    (hs : Multiset.card s = n) (ht : Multiset.card t = n) :
    (s.map f).sum = (t.map f).sum ↔ s.sum = t.sum

/-- An `n`-Freiman homomorphism from a set `A` to a set `B` is a map which preserves products of `n`
elements. -/
@[to_additive]
/--
Definition of `IsMulFreimanIso` / `IsMulFreimanIso` 的定义

English:
structure IsMulFreimanIso
  parameters: (n : Nat) (A : Set α) (B : Set β) (f : α -> β)
  axioms and operations (2):
    - bijOn : BijOn f A B
    - map_prod_eq_map_prod(⦃s t) : Multiset α⦄ (hsA : forall ⦃x⦄, x in s -> x in A) (htA : forall ⦃x⦄, x in t -> x in A) (hs : Multiset.card s = n) (ht : Multiset.card t = n) : (s.map f).prod = (t.map f).prod ↔ s.prod = t.prod

中文:
结构 是MulFreimanIso
  参数: (n : 自然数) (A : 集合 α) (B : 集合 β) (f : α -> β)
  公理与运算 (2 个):
    - bijOn : 双射限制 f A B
    - map_prod_eq_map_prod(⦃s t) : Multiset α⦄ (hsA : 对任意 ⦃x⦄, x in s -> x in A) (htA : 对任意 ⦃x⦄, x in t -> x in A) (hs : Multiset.card s = n) (ht : Multiset.card t = n) : (s.map f).乘积 = (t.map f).乘积 ↔ s.乘积 = t.乘积
-/
structure IsMulFreimanIso (n : Nat) (A : Set α) (B : Set β) (f : α -> β) : Prop where
  bijOn : BijOn f A B
  /-- An `n`-Freiman homomorphism preserves products of `n` elements. -/
  map_prod_eq_map_prod ⦃s t : Multiset α⦄ (hsA : forall ⦃x⦄, x in s -> x in A) (htA : forall ⦃x⦄, x in t -> x in A)
    (hs : Multiset.card s = n) (ht : Multiset.card t = n) :
    (s.map f).prod = (t.map f).prod ↔ s.prod = t.prod

@[to_additive]
/--
lemma `IsMulFreimanIso.isMulFreimanHom` / 引理 `IsMulFreimanIso.isMulFreimanHom`

English:
lemma IsMulFreimanIso.isMulFreimanHom
  given: (hf : IsMulFreimanIso n A B f)
  statement: IsMulFreimanHom n A B f where
  proof: hf.bijOn.mapsTo
  map_prod_eq_map_prod _s _t hsA htA hs ht := (hf.map_prod_eq_map_prod hsA htA hs ht).2

中文:
引理 是MulFreimanIso.isMulFreimanHom
  条件: (hf : 是MulFreimanIso n A B f)
  结论: 是MulFreiman态射 n A B f where
  证明: hf.bijOn.mapsTo
  map_prod_eq_map_prod _s _t hsA htA hs ht := (hf.map_prod_eq_map_prod hsA htA hs ht).2

Depends on / 依赖: hf.bijOn.mapsTo, mapsTo
-/
lemma IsMulFreimanIso.isMulFreimanHom (hf : IsMulFreimanIso n A B f) : IsMulFreimanHom n A B f where
  mapsTo := hf.bijOn.mapsTo
  map_prod_eq_map_prod _s _t hsA htA hs ht := (hf.map_prod_eq_map_prod hsA htA hs ht).2

/--
lemma `IsMulFreimanHom.congr` / 引理 `IsMulFreimanHom.congr`

English:
lemma IsMulFreimanHom.congr
  given: (hf₁ : IsMulFreimanHom n A B f₁) (h : EqOn f₁ f₂ A)
  proof: hf₁.mapsTo.congr h
  map_prod_eq_map_prod s t hsA htA hs ht h' := by
    rw [map_congr rfl fun x hx => (h (hsA hx)).symm]; rw [map_congr rfl fun x hx => (h (htA hx)).symm]; rw [hf₁.map_prod_eq_map_prod hsA htA hs ht h']

中文:
引理 是MulFreiman态射.congr
  条件: (hf₁ : 是MulFreiman态射 n A B f₁) (h : EqOn f₁ f₂ A)
  证明: hf₁.mapsTo.congr h
  map_prod_eq_map_prod s t hsA htA hs ht h' := by
    rw [map_congr rfl fun x hx => (h (hsA hx)).symm]; rw [map_congr rfl fun x hx => (h (htA hx)).symm]; rw [hf₁.map_prod_eq_map_prod hsA htA hs ht h']

Depends on / 依赖: mapsTo, mapsTo.congr
-/
lemma IsMulFreimanHom.congr (hf₁ : IsMulFreimanHom n A B f₁) (h : EqOn f₁ f₂ A) :
    IsMulFreimanHom n A B f₂ where
  mapsTo := hf₁.mapsTo.congr h
  map_prod_eq_map_prod s t hsA htA hs ht h' := by
    rw [map_congr rfl fun x hx => (h (hsA hx)).symm]; rw [map_congr rfl fun x hx => (h (htA hx)).symm]; rw [hf₁.map_prod_eq_map_prod hsA htA hs ht h']

/--
lemma `IsMulFreimanIso.congr` / 引理 `IsMulFreimanIso.congr`

English:
lemma IsMulFreimanIso.congr
  given: (hf₁ : IsMulFreimanIso n A B f₁) (h : EqOn f₁ f₂ A)
  proof: hf₁.bijOn.congr h
  map_prod_eq_map_prod s t hsA htA hs ht := by
    rw [map_congr rfl fun x hx => h.symm (hsA hx)]; rw [map_congr rfl fun x hx => h.symm (htA hx)]; rw [hf₁.map_prod_eq_map_prod hsA htA hs ht]

中文:
引理 是MulFreimanIso.congr
  条件: (hf₁ : 是MulFreimanIso n A B f₁) (h : EqOn f₁ f₂ A)
  证明: hf₁.bijOn.congr h
  map_prod_eq_map_prod s t hsA htA hs ht := by
    rw [map_congr rfl fun x hx => h.symm (hsA hx)]; rw [map_congr rfl fun x hx => h.symm (htA hx)]; rw [hf₁.map_prod_eq_map_prod hsA htA hs ht]

Depends on / 依赖: bijOn.congr
-/
lemma IsMulFreimanIso.congr (hf₁ : IsMulFreimanIso n A B f₁) (h : EqOn f₁ f₂ A) :
    IsMulFreimanIso n A B f₂ where
  bijOn := hf₁.bijOn.congr h
  map_prod_eq_map_prod s t hsA htA hs ht := by
    rw [map_congr rfl fun x hx => h.symm (hsA hx)]; rw [map_congr rfl fun x hx => h.symm (htA hx)]; rw [hf₁.map_prod_eq_map_prod hsA htA hs ht]

/--
Given a Freiman isomorphism `f` from `A` to `B`, if `g` maps `B` into `A`, and is a right inverse
to `f` on `B`, then `g` is a Freiman isomorphism from `B` to `A`.
-/
@[to_additive
/--
Given an additive Freiman isomorphism `f` from `A` to `B`, if `g` maps `B` into `A`, and is a
right inverse to `f` on `B`, then `g` is an additive Freiman isomorphism from `B` to `A`.
-/]
/--
lemma `IsMulFreimanIso.symm` / 引理 `IsMulFreimanIso.symm`

English:
lemma IsMulFreimanIso.symm
  statement: {g : β -> α} (hg₁ : MapsTo g B A) (hg₂ : RightInvOn g f B)
  proof: hf.bijOn.symm ⟨hg₂, InjOn.rightInvOn_of_leftInvOn hf.bijOn.injOn hg₂ hf.bijOn.mapsTo hg₁⟩
  map_prod_eq_map_prod := fun s t hsB htB hs ht => by
    rw [← hf.map_prod_eq_map_prod _ _ (by simp [hs]) (by simp [ht]), map_map, map_congr rfl, map_id,
      map_map, map_congr rfl, map_id]
    all_goals aesop

中文:
引理 是MulFreimanIso.symm
  结论: {g : β -> α} (hg₁ : 映射到 g B A) (hg₂ : RightInvOn g f B)
  证明: hf.bijOn.symm ⟨hg₂, InjOn.rightInvOn_of_leftInvOn hf.bijOn.injOn hg₂ hf.bijOn.mapsTo hg₁⟩
  map_prod_eq_map_prod := fun s t hsB htB hs ht => by
    rw [← hf.map_prod_eq_map_prod _ _ (by simp [hs]) (by simp [ht]), map_map, map_congr rfl, map_id,
      map_map, map_congr rfl, map_id]
    all_goals aesop

Depends on / 依赖: InjOn.rightInvOn_of_leftInvOn, hf.bijOn.injOn, hf.bijOn.mapsTo, hf.bijOn.symm, mapsTo, rightInvOn_of_leftInvOn
-/
lemma IsMulFreimanIso.symm {g : β -> α} (hg₁ : MapsTo g B A) (hg₂ : RightInvOn g f B)
    (hf : IsMulFreimanIso n A B f) :
    IsMulFreimanIso n B A g where
  bijOn := hf.bijOn.symm ⟨hg₂, InjOn.rightInvOn_of_leftInvOn hf.bijOn.injOn hg₂ hf.bijOn.mapsTo hg₁⟩
  map_prod_eq_map_prod := fun s t hsB htB hs ht => by
    rw [← hf.map_prod_eq_map_prod _ _ (by simp [hs]) (by simp [ht]), map_map, map_congr rfl, map_id,
      map_map, map_congr rfl, map_id]
    all_goals aesop

/--
If the inverse of a Freiman homomorphism is itself a Freiman homomorphism, then it is a Freiman
isomorphism.
-/
@[to_additive
/--
If the inverse of a Freiman homomorphism is itself a Freiman homomorphism, then it is a Freiman
isomorphism.
-/]
/--
lemma `IsMulFreimanHom.to_isMulFreimanIso` / 引理 `IsMulFreimanHom.to_isMulFreimanIso`

English:
lemma IsMulFreimanHom.to_isMulFreimanIso
  statement: {g : β -> α} (h : InvOn g f A B)
  proof: h.bijOn hf.mapsTo hg.mapsTo
  map_prod_eq_map_prod s t hsA htA hs ht := by
    refine ⟨fun h' => ?_, hf.map_prod_eq_map_prod hsA htA hs ht⟩
    have : (map g (map f s)).prod = (map g (map f t)).prod := by
      have := hf.mapsTo
      apply hg.map_prod_eq_map_prod <;> simp_all [MapsTo]
    rwa [map_map, map_congr rfl fun x hx => ?g1, map_id, map_map,
      map_congr rfl fun x hx => ?g2, map_id] at this
    case g1 => exact h.1 (hsA hx)
    case g2 => exact h.1 (htA hx)

中文:
引理 是MulFreiman态射.to_isMulFreimanIso
  结论: {g : β -> α} (h : InvOn g f A B)
  证明: h.bijOn hf.mapsTo hg.mapsTo
  map_prod_eq_map_prod s t hsA htA hs ht := by
    refine ⟨fun h' => ?_, hf.map_prod_eq_map_prod hsA htA hs ht⟩
    have : (map g (map f s)).prod = (map g (map f t)).prod := by
      have := hf.mapsTo
      apply hg.map_prod_eq_map_prod <;> simp_all [MapsTo]
    rwa [map_map, map_congr rfl fun x hx => ?g1, map_id, map_map,
      map_congr rfl fun x hx => ?g2, map_id] at this
    case g1 => exact h.1 (hsA hx)
    case g2 => exact h.1 (htA hx)

Depends on / 依赖: h.bijOn, hf.mapsTo, hg.mapsTo, mapsTo
-/
lemma IsMulFreimanHom.to_isMulFreimanIso {g : β -> α} (h : InvOn g f A B)
    (hf : IsMulFreimanHom n A B f) (hg : IsMulFreimanHom n B A g) :
    IsMulFreimanIso n A B f where
  bijOn := h.bijOn hf.mapsTo hg.mapsTo
  map_prod_eq_map_prod s t hsA htA hs ht := by
    refine ⟨fun h' => ?_, hf.map_prod_eq_map_prod hsA htA hs ht⟩
    have : (map g (map f s)).prod = (map g (map f t)).prod := by
      have := hf.mapsTo
      apply hg.map_prod_eq_map_prod <;> simp_all [MapsTo]
    rwa [map_map, map_congr rfl fun x hx => ?g1, map_id, map_map,
      map_congr rfl fun x hx => ?g2, map_id] at this
    case g1 => exact h.1 (hsA hx)
    case g2 => exact h.1 (htA hx)

/-- If `f` is a multiplicative Freiman isomorphism from `A` to `B`, then `f.invFunOn A` is
a multiplicative Freiman isomorphism from `B` to `A`. -/
@[to_additive /-- If `f` is an additive Freiman isomorphism from `A` to `B`, then `f.invFunOn A` is
an additive Freiman isomorphism from `B` to `A`. -/]
/--
lemma `IsMulFreimanIso.invFunOn` / 引理 `IsMulFreimanIso.invFunOn`

English:
lemma IsMulFreimanIso.invFunOn
  given: (hf : IsMulFreimanIso n A B f)
  proof: hf.symm hf.bijOn.surjOn.mapsTo_invFunOn hf.bijOn.surjOn.rightInvOn_invFunOn

中文:
引理 是MulFreimanIso.invFunOn
  条件: (hf : 是MulFreimanIso n A B f)
  证明: hf.symm hf.bijOn.surjOn.mapsTo_invFunOn hf.bijOn.surjOn.rightInvOn_invFunOn
-/
protected lemma IsMulFreimanIso.invFunOn (hf : IsMulFreimanIso n A B f) :
    IsMulFreimanIso n B A (f.invFunOn A) :=
  hf.symm hf.bijOn.surjOn.mapsTo_invFunOn hf.bijOn.surjOn.rightInvOn_invFunOn

/-- A version of the Freiman homomorphism condition expressed using `Finset`s, for practicality. -/
@[to_additive /-- A version of the Freiman homomorphism condition expressed using `Finset`s,
for practicality. -/]
/--
lemma `IsMulFreimanHom.prod_apply` / 引理 `IsMulFreimanHom.prod_apply`

English:
lemma IsMulFreimanHom.prod_apply
  statement: (hf : IsMulFreimanHom n A B f) {s t : Finset α}
  proof: by
  simpa using hf.map_prod_eq_map_prod hsA htA hs ht

@[to_additive]

中文:
引理 是MulFreiman态射.prod_apply
  结论: (hf : 是MulFreiman态射 n A B f) {s t : 有限集 α}
  证明: by
  simpa using hf.map_prod_eq_map_prod hsA htA hs ht

@[to_additive]

Depends on / 依赖: hf.map_prod_eq_map_prod, map_prod_eq_map_prod
-/
lemma IsMulFreimanHom.prod_apply (hf : IsMulFreimanHom n A B f) {s t : Finset α}
    {hsA : (s : Set α) subseteq A} {htA : (t : Set α) subseteq A}
    (hs : s.card = n) (ht : t.card = n) :
    ∏ i in s, i = ∏ i in t, i -> ∏ i in s, f i = ∏ i in t, f i := by
  simpa using hf.map_prod_eq_map_prod hsA htA hs ht

@[to_additive]
/--
lemma `IsMulFreimanHom.mul_eq_mul` / 引理 `IsMulFreimanHom.mul_eq_mul`

English:
lemma IsMulFreimanHom.mul_eq_mul
  statement: (hf : IsMulFreimanHom 2 A B f) {a b c d : α}
  proof: by
  simp_rw [← prod_pair] at h ⊢
  refine hf.map_prod_eq_map_prod ?_ ?_ (card_pair _ _) (card_pair _ _) h <;> simp [ha, hb, hc, hd]

@[to_additive]

中文:
引理 是MulFreiman态射.mul_eq_mul
  结论: (hf : 是MulFreiman态射 2 A B f) {a b c d : α}
  证明: by
  simp_rw [← prod_pair] at h ⊢
  refine hf.map_prod_eq_map_prod ?_ ?_ (card_pair _ _) (card_pair _ _) h <;> simp [ha, hb, hc, hd]

@[to_additive]

Depends on / 依赖: card_pair, hf.map_prod_eq_map_prod, map_prod_eq_map_prod, prod_pair, simp_rw
-/
lemma IsMulFreimanHom.mul_eq_mul (hf : IsMulFreimanHom 2 A B f) {a b c d : α}
    (ha : a in A) (hb : b in A) (hc : c in A) (hd : d in A) (h : a * b = c * d) :
    f a * f b = f c * f d := by
  simp_rw [← prod_pair] at h ⊢
  refine hf.map_prod_eq_map_prod ?_ ?_ (card_pair _ _) (card_pair _ _) h <;> simp [ha, hb, hc, hd]

@[to_additive]
/--
lemma `IsMulFreimanIso.mul_eq_mul` / 引理 `IsMulFreimanIso.mul_eq_mul`

English:
lemma IsMulFreimanIso.mul_eq_mul
  statement: (hf : IsMulFreimanIso 2 A B f) {a b c d : α}
  proof: by
  simp_rw [← prod_pair]
  refine hf.map_prod_eq_map_prod ?_ ?_ (card_pair _ _) (card_pair _ _) <;> simp [ha, hb, hc, hd]

中文:
引理 是MulFreimanIso.mul_eq_mul
  结论: (hf : 是MulFreimanIso 2 A B f) {a b c d : α}
  证明: by
  simp_rw [← prod_pair]
  refine hf.map_prod_eq_map_prod ?_ ?_ (card_pair _ _) (card_pair _ _) <;> simp [ha, hb, hc, hd]

Depends on / 依赖: card_pair, hf.map_prod_eq_map_prod, map_prod_eq_map_prod, prod_pair, simp_rw
-/
lemma IsMulFreimanIso.mul_eq_mul (hf : IsMulFreimanIso 2 A B f) {a b c d : α}
    (ha : a in A) (hb : b in A) (hc : c in A) (hd : d in A) :
    f a * f b = f c * f d ↔ a * b = c * d := by
  simp_rw [← prod_pair]
  refine hf.map_prod_eq_map_prod ?_ ?_ (card_pair _ _) (card_pair _ _) <;> simp [ha, hb, hc, hd]

/-- Characterisation of `2`-Freiman homomorphisms. -/
@[to_additive /-- Characterisation of `2`-Freiman homomorphisms. -/]
/--
lemma `isMulFreimanHom_two` / 引理 `isMulFreimanHom_two`

English:
lemma isMulFreimanHom_two
  proof: ⟨hf.mapsTo, fun _ ha _ hb _ hc _ hd => hf.mul_eq_mul ha hb hc hd⟩
  mpr hf := ⟨hf.1, by aesop (add simp card_eq_two)⟩

中文:
引理 isMulFreimanHom_two
  证明: ⟨hf.mapsTo, fun _ ha _ hb _ hc _ hd => hf.mul_eq_mul ha hb hc hd⟩
  mpr hf := ⟨hf.1, by aesop (add simp card_eq_two)⟩

Depends on / 依赖: hf.mapsTo, hf.mul_eq_mul, mapsTo, mul_eq_mul
-/
lemma isMulFreimanHom_two :
    IsMulFreimanHom 2 A B f ↔ MapsTo f A B ∧ forall a in A, forall b in A, forall c in A, forall d in A,
      a * b = c * d -> f a * f b = f c * f d where
  mp hf := ⟨hf.mapsTo, fun _ ha _ hb _ hc _ hd => hf.mul_eq_mul ha hb hc hd⟩
  mpr hf := ⟨hf.1, by aesop (add simp card_eq_two)⟩

/-- Characterisation of `2`-Freiman homs. -/
@[to_additive /-- Characterisation of `2`-Freiman isomorphisms. -/]
/--
lemma `isMulFreimanIso_two` / 引理 `isMulFreimanIso_two`

English:
lemma isMulFreimanIso_two
  proof: ⟨hf.bijOn, fun _ ha _ hb _ hc _ hd => hf.mul_eq_mul ha hb hc hd⟩
  mpr hf := ⟨hf.1, by aesop (add simp card_eq_two)⟩

中文:
引理 isMulFreimanIso_two
  证明: ⟨hf.bijOn, fun _ ha _ hb _ hc _ hd => hf.mul_eq_mul ha hb hc hd⟩
  mpr hf := ⟨hf.1, by aesop (add simp card_eq_two)⟩

Depends on / 依赖: hf.bijOn, hf.mul_eq_mul, mul_eq_mul
-/
lemma isMulFreimanIso_two :
    IsMulFreimanIso 2 A B f ↔ BijOn f A B ∧ forall a in A, forall b in A, forall c in A, forall d in A,
      f a * f b = f c * f d ↔ a * b = c * d where
  mp hf := ⟨hf.bijOn, fun _ ha _ hb _ hc _ hd => hf.mul_eq_mul ha hb hc hd⟩
  mpr hf := ⟨hf.1, by aesop (add simp card_eq_two)⟩

/--
lemma `isMulFreimanHom_id` / 引理 `isMulFreimanHom_id`

English:
lemma isMulFreimanHom_id
  given: (hA : A₁ subseteq A₂)
  statement: IsMulFreimanHom n A₁ A₂ id where
  proof: hA
  map_prod_eq_map_prod s t _ _ _ _ h := by simpa using h

中文:
引理 isMulFreimanHom_id
  条件: (hA : A₁ subseteq A₂)
  结论: 是MulFreiman态射 n A₁ A₂ id where
  证明: hA
  map_prod_eq_map_prod s t _ _ _ _ h := by simpa using h
-/
@[to_additive] lemma isMulFreimanHom_id (hA : A₁ subseteq A₂) : IsMulFreimanHom n A₁ A₂ id where
  mapsTo := hA
  map_prod_eq_map_prod s t _ _ _ _ h := by simpa using h

/--
lemma `isMulFreimanIso_id` / 引理 `isMulFreimanIso_id`

English:
lemma isMulFreimanIso_id
  statement: IsMulFreimanIso n A A id where
  proof: bijOn_id _
  map_prod_eq_map_prod s t _ _ _ _ := by simp

中文:
引理 isMulFreimanIso_id
  结论: 是MulFreimanIso n A A id where
  证明: bijOn_id _
  map_prod_eq_map_prod s t _ _ _ _ := by simp
-/
@[to_additive] lemma isMulFreimanIso_id : IsMulFreimanIso n A A id where
  bijOn := bijOn_id _
  map_prod_eq_map_prod s t _ _ _ _ := by simp

/--
lemma `IsMulFreimanHom.comp` / 引理 `IsMulFreimanHom.comp`

English:
lemma IsMulFreimanHom.comp
  statement: (hg : IsMulFreimanHom n B C g)
  proof: hg.mapsTo.comp hf.mapsTo
  map_prod_eq_map_prod s t hsA htA hs ht h := by
    rw [← map_map]; rw [← map_map]
    refine hg.map_prod_eq_map_prod ?_ ?_ (by rwa [card_map]) (by rwa [card_map])
      (hf.map_prod_eq_map_prod hsA htA hs ht h)
    · simpa using fun a h => hf.mapsTo (hsA h)
    · simpa using fun a h => hf.mapsTo (htA h)

中文:
引理 是MulFreiman态射.comp
  结论: (hg : 是MulFreiman态射 n B C g)
  证明: hg.mapsTo.comp hf.mapsTo
  map_prod_eq_map_prod s t hsA htA hs ht h := by
    rw [← map_map]; rw [← map_map]
    refine hg.map_prod_eq_map_prod ?_ ?_ (by rwa [card_map]) (by rwa [card_map])
      (hf.map_prod_eq_map_prod hsA htA hs ht h)
    · simpa using fun a h => hf.mapsTo (hsA h)
    · simpa using fun a h => hf.mapsTo (htA h)
-/
@[to_additive] lemma IsMulFreimanHom.comp (hg : IsMulFreimanHom n B C g)
    (hf : IsMulFreimanHom n A B f) : IsMulFreimanHom n A C (g ∘ f) where
  mapsTo := hg.mapsTo.comp hf.mapsTo
  map_prod_eq_map_prod s t hsA htA hs ht h := by
    rw [← map_map]; rw [← map_map]
    refine hg.map_prod_eq_map_prod ?_ ?_ (by rwa [card_map]) (by rwa [card_map])
      (hf.map_prod_eq_map_prod hsA htA hs ht h)
    · simpa using fun a h => hf.mapsTo (hsA h)
    · simpa using fun a h => hf.mapsTo (htA h)

/--
lemma `IsMulFreimanIso.comp` / 引理 `IsMulFreimanIso.comp`

English:
lemma IsMulFreimanIso.comp
  statement: (hg : IsMulFreimanIso n B C g)
  proof: hg.bijOn.comp hf.bijOn
  map_prod_eq_map_prod s t hsA htA hs ht := by
    rw [← map_map]; rw [← map_map]
    rw [hg.map_prod_eq_map_prod _ _ (by rwa [card_map]) (by rwa [card_map]),
      hf.map_prod_eq_map_prod hsA htA hs ht]
    · simpa using fun a h => hf.bijOn.mapsTo (hsA h)
    · simpa using fun a h => hf.bijOn.mapsTo (htA h)

中文:
引理 是MulFreimanIso.comp
  结论: (hg : 是MulFreimanIso n B C g)
  证明: hg.bijOn.comp hf.bijOn
  map_prod_eq_map_prod s t hsA htA hs ht := by
    rw [← map_map]; rw [← map_map]
    rw [hg.map_prod_eq_map_prod _ _ (by rwa [card_map]) (by rwa [card_map]),
      hf.map_prod_eq_map_prod hsA htA hs ht]
    · simpa using fun a h => hf.bijOn.mapsTo (hsA h)
    · simpa using fun a h => hf.bijOn.mapsTo (htA h)
-/
@[to_additive] lemma IsMulFreimanIso.comp (hg : IsMulFreimanIso n B C g)
    (hf : IsMulFreimanIso n A B f) : IsMulFreimanIso n A C (g ∘ f) where
  bijOn := hg.bijOn.comp hf.bijOn
  map_prod_eq_map_prod s t hsA htA hs ht := by
    rw [← map_map]; rw [← map_map]
    rw [hg.map_prod_eq_map_prod _ _ (by rwa [card_map]) (by rwa [card_map]),
      hf.map_prod_eq_map_prod hsA htA hs ht]
    · simpa using fun a h => hf.bijOn.mapsTo (hsA h)
    · simpa using fun a h => hf.bijOn.mapsTo (htA h)

/--
lemma `IsMulFreimanHom.subset` / 引理 `IsMulFreimanHom.subset`

English:
lemma IsMulFreimanHom.subset
  statement: (hA : A₁ subseteq A₂) (hf : IsMulFreimanHom n A₂ B₂ f)
  proof: hf'
  __ := hf.comp (isMulFreimanHom_id hA)

中文:
引理 是MulFreiman态射.subset
  结论: (hA : A₁ subseteq A₂) (hf : 是MulFreiman态射 n A₂ B₂ f)
  证明: hf'
  __ := hf.comp (isMulFreimanHom_id hA)
-/
@[to_additive] lemma IsMulFreimanHom.subset (hA : A₁ subseteq A₂) (hf : IsMulFreimanHom n A₂ B₂ f)
    (hf' : MapsTo f A₁ B₁) : IsMulFreimanHom n A₁ B₁ f where
  mapsTo := hf'
  __ := hf.comp (isMulFreimanHom_id hA)

/--
lemma `IsMulFreimanHom.superset` / 引理 `IsMulFreimanHom.superset`

English:
lemma IsMulFreimanHom.superset
  given: (hB : B₁ subseteq B₂) (hf : IsMulFreimanHom n A B₁ f)
  proof: (isMulFreimanHom_id hB).comp hf

中文:
引理 是MulFreiman态射.superset
  条件: (hB : B₁ subseteq B₂) (hf : 是MulFreiman态射 n A B₁ f)
  证明: (isMulFreimanHom_id hB).comp hf
-/
@[to_additive] lemma IsMulFreimanHom.superset (hB : B₁ subseteq B₂) (hf : IsMulFreimanHom n A B₁ f) :
    IsMulFreimanHom n A B₂ f := (isMulFreimanHom_id hB).comp hf

/--
lemma `IsMulFreimanIso.subset` / 引理 `IsMulFreimanIso.subset`

English:
lemma IsMulFreimanIso.subset
  statement: (hA : A₁ subseteq A₂) (hf : IsMulFreimanIso n A₂ B₂ f)
  proof: hf'
  map_prod_eq_map_prod s t hsA htA hs ht := by
    refine hf.map_prod_eq_map_prod (fun a ha => hA (hsA ha)) (fun a ha => hA (htA ha)) hs ht

@[to_additive]

中文:
引理 是MulFreimanIso.subset
  结论: (hA : A₁ subseteq A₂) (hf : 是MulFreimanIso n A₂ B₂ f)
  证明: hf'
  map_prod_eq_map_prod s t hsA htA hs ht := by
    refine hf.map_prod_eq_map_prod (fun a ha => hA (hsA ha)) (fun a ha => hA (htA ha)) hs ht

@[to_additive]
-/
@[to_additive] lemma IsMulFreimanIso.subset (hA : A₁ subseteq A₂) (hf : IsMulFreimanIso n A₂ B₂ f)
    (hf' : BijOn f A₁ B₁) : IsMulFreimanIso n A₁ B₁ f where
  bijOn := hf'
  map_prod_eq_map_prod s t hsA htA hs ht := by
    refine hf.map_prod_eq_map_prod (fun a ha => hA (hsA ha)) (fun a ha => hA (htA ha)) hs ht

@[to_additive]
/--
lemma `isMulFreimanHom_const` / 引理 `isMulFreimanHom_const`

English:
lemma isMulFreimanHom_const
  given: {b : β} (hb : b in B)
  statement: IsMulFreimanHom n A B fun _ => b where
  proof: hb
  map_prod_eq_map_prod s t _ _ hs ht _ := by simp only [map_const', hs, prod_replicate, ht]

@[to_additive (attr := simp)]

中文:
引理 isMulFreimanHom_const
  条件: {b : β} (hb : b in B)
  结论: 是MulFreiman态射 n A B fun _ => b where
  证明: hb
  map_prod_eq_map_prod s t _ _ hs ht _ := by simp only [map_const', hs, prod_replicate, ht]

@[to_additive (attr := simp)]
-/
lemma isMulFreimanHom_const {b : β} (hb : b in B) : IsMulFreimanHom n A B fun _ => b where
  mapsTo _ _ := hb
  map_prod_eq_map_prod s t _ _ hs ht _ := by simp only [map_const', hs, prod_replicate, ht]

@[to_additive (attr := simp)]
/--
lemma `isMulFreimanHom_zero_iff` / 引理 `isMulFreimanHom_zero_iff`

English:
lemma isMulFreimanHom_zero_iff
  statement: IsMulFreimanHom 0 A B f ↔ MapsTo f A B
  proof: ⟨fun h => h.mapsTo, fun h => ⟨h, by simp_all⟩⟩

@[to_additive (attr := simp)]

中文:
引理 isMulFreimanHom_zero_iff
  结论: 是MulFreiman态射 0 A B f ↔ 映射到 f A B
  证明: ⟨fun h => h.mapsTo, fun h => ⟨h, by simp_all⟩⟩

@[to_additive (attr := simp)]

Depends on / 依赖: h.mapsTo, mapsTo
-/
lemma isMulFreimanHom_zero_iff : IsMulFreimanHom 0 A B f ↔ MapsTo f A B :=
  ⟨fun h => h.mapsTo, fun h => ⟨h, by simp_all⟩⟩

@[to_additive (attr := simp)]
/--
lemma `isMulFreimanIso_zero_iff` / 引理 `isMulFreimanIso_zero_iff`

English:
lemma isMulFreimanIso_zero_iff
  statement: IsMulFreimanIso 0 A B f ↔ BijOn f A B
  proof: ⟨fun h => h.bijOn, fun h => ⟨h, by simp_all⟩⟩

@[to_additive (attr := simp) isAddFreimanHom_one_iff]

中文:
引理 isMulFreimanIso_zero_iff
  结论: 是MulFreimanIso 0 A B f ↔ 双射限制 f A B
  证明: ⟨fun h => h.bijOn, fun h => ⟨h, by simp_all⟩⟩

@[to_additive (attr := simp) isAddFreimanHom_one_iff]

Depends on / 依赖: h.bijOn
-/
lemma isMulFreimanIso_zero_iff : IsMulFreimanIso 0 A B f ↔ BijOn f A B :=
  ⟨fun h => h.bijOn, fun h => ⟨h, by simp_all⟩⟩

@[to_additive (attr := simp) isAddFreimanHom_one_iff]
/--
lemma `isMulFreimanHom_one_iff` / 引理 `isMulFreimanHom_one_iff`

English:
lemma isMulFreimanHom_one_iff
  statement: IsMulFreimanHom 1 A B f ↔ MapsTo f A B
  proof: ⟨fun h => h.mapsTo, fun h => ⟨h, by aesop (add simp card_eq_one)⟩⟩

@[to_additive (attr := simp) isAddFreimanIso_one_iff]

中文:
引理 isMulFreimanHom_one_iff
  结论: 是MulFreiman态射 1 A B f ↔ 映射到 f A B
  证明: ⟨fun h => h.mapsTo, fun h => ⟨h, by aesop (add simp card_eq_one)⟩⟩

@[to_additive (attr := simp) isAddFreimanIso_one_iff]

Depends on / 依赖: card_eq_one, h.mapsTo, mapsTo
-/
lemma isMulFreimanHom_one_iff : IsMulFreimanHom 1 A B f ↔ MapsTo f A B :=
  ⟨fun h => h.mapsTo, fun h => ⟨h, by aesop (add simp card_eq_one)⟩⟩

@[to_additive (attr := simp) isAddFreimanIso_one_iff]
/--
lemma `isMulFreimanIso_one_iff` / 引理 `isMulFreimanIso_one_iff`

English:
lemma isMulFreimanIso_one_iff
  statement: IsMulFreimanIso 1 A B f ↔ BijOn f A B
  proof: ⟨fun h => h.bijOn, fun h => ⟨h, by aesop (add simp [card_eq_one, BijOn])⟩⟩

@[to_additive (attr := simp)]

中文:
引理 isMulFreimanIso_one_iff
  结论: 是MulFreimanIso 1 A B f ↔ 双射限制 f A B
  证明: ⟨fun h => h.bijOn, fun h => ⟨h, by aesop (add simp [card_eq_one, BijOn])⟩⟩

@[to_additive (attr := simp)]

Depends on / 依赖: card_eq_one, h.bijOn
-/
lemma isMulFreimanIso_one_iff : IsMulFreimanIso 1 A B f ↔ BijOn f A B :=
  ⟨fun h => h.bijOn, fun h => ⟨h, by aesop (add simp [card_eq_one, BijOn])⟩⟩

@[to_additive (attr := simp)]
/--
lemma `isMulFreimanHom_empty` / 引理 `isMulFreimanHom_empty`

English:
lemma isMulFreimanHom_empty
  statement: IsMulFreimanHom n (∅ : Set α) B f where
  proof: mapsTo_empty f B
  map_prod_eq_map_prod s t := by aesop (add simp eq_zero_of_forall_notMem)

@[to_additive (attr := simp)]

中文:
引理 isMulFreimanHom_empty
  结论: 是MulFreiman态射 n (∅ : 集合 α) B f where
  证明: mapsTo_empty f B
  map_prod_eq_map_prod s t := by aesop (add simp eq_zero_of_forall_notMem)

@[to_additive (attr := simp)]

Depends on / 依赖: mapsTo_empty
-/
lemma isMulFreimanHom_empty : IsMulFreimanHom n (∅ : Set α) B f where
  mapsTo := mapsTo_empty f B
  map_prod_eq_map_prod s t := by aesop (add simp eq_zero_of_forall_notMem)

@[to_additive (attr := simp)]
/--
lemma `isMulFreimanIso_empty` / 引理 `isMulFreimanIso_empty`

English:
lemma isMulFreimanIso_empty
  statement: IsMulFreimanIso n (∅ : Set α) (∅ : Set β) f where
  proof: bijOn_empty _
  map_prod_eq_map_prod s t hs ht := by
    simp [eq_zero_of_forall_notMem hs, eq_zero_of_forall_notMem ht]

中文:
引理 isMulFreimanIso_empty
  结论: 是MulFreimanIso n (∅ : 集合 α) (∅ : 集合 β) f where
  证明: bijOn_empty _
  map_prod_eq_map_prod s t hs ht := by
    simp [eq_zero_of_forall_notMem hs, eq_zero_of_forall_notMem ht]

Depends on / 依赖: bijOn_empty
-/
lemma isMulFreimanIso_empty : IsMulFreimanIso n (∅ : Set α) (∅ : Set β) f where
  bijOn := bijOn_empty _
  map_prod_eq_map_prod s t hs ht := by
    simp [eq_zero_of_forall_notMem hs, eq_zero_of_forall_notMem ht]

/--
lemma `IsMulFreimanHom.mul` / 引理 `IsMulFreimanHom.mul`

English:
lemma IsMulFreimanHom.mul
  statement: (h₁ : IsMulFreimanHom n A B₁ f₁)
  proof: h₁.mapsTo.mul h₂.mapsTo
  map_prod_eq_map_prod s t hsA htA hs ht h := by
    rw [Pi.mul_def]; rw [prod_map_mul]; rw [prod_map_mul]; rw [h₁.map_prod_eq_map_prod hsA htA hs ht h]; rw [h₂.map_prod_eq_map_prod hsA htA hs ht h]

中文:
引理 是MulFreiman态射.mul
  结论: (h₁ : 是MulFreiman态射 n A B₁ f₁)
  证明: h₁.mapsTo.mul h₂.mapsTo
  map_prod_eq_map_prod s t hsA htA hs ht h := by
    rw [Pi.mul_def]; rw [prod_map_mul]; rw [prod_map_mul]; rw [h₁.map_prod_eq_map_prod hsA htA hs ht h]; rw [h₂.map_prod_eq_map_prod hsA htA hs ht h]
-/
@[to_additive] lemma IsMulFreimanHom.mul (h₁ : IsMulFreimanHom n A B₁ f₁)
    (h₂ : IsMulFreimanHom n A B₂ f₂) : IsMulFreimanHom n A (B₁ * B₂) (f₁ * f₂) where
  mapsTo := h₁.mapsTo.mul h₂.mapsTo
  map_prod_eq_map_prod s t hsA htA hs ht h := by
    rw [Pi.mul_def]; rw [prod_map_mul]; rw [prod_map_mul]; rw [h₁.map_prod_eq_map_prod hsA htA hs ht h]; rw [h₂.map_prod_eq_map_prod hsA htA hs ht h]

/--
lemma `MulHomClass.isMulFreimanHom` / 引理 `MulHomClass.isMulFreimanHom`

English:
lemma MulHomClass.isMulFreimanHom
  statement: [FunLike F α β] [MulHomClass F α β] (f : F)
  proof: match n with
  | 0 => by simpa
  | n + 1 => IsMulFreimanHom.mk hfAB fun s t hsA htA hs ht h => by
    rw [← map_multiset_ne_zero_prod _ (by grind [Multiset.card_eq_zero]),
        h, map_multiset_ne_zero_prod _ (by grind [Multiset.card_eq_zero])]

@[deprecated (since := "2026-04-29")]
alias MonoidHomClass.isMulFreimanHom := MulHomClass.isMulFreimanHom

@[deprecated (since := "2026-04-29")]
alias AddMonoidHomClass.isAddFreimanHom := AddHomClass.isAddFreimanHom

中文:
引理 乘法态射类.isMulFreimanHom
  结论: [函数状 F α β] [乘法态射类 F α β] (f : F)
  证明: match n with
  | 0 => by simpa
  | n + 1 => IsMulFreimanHom.mk hfAB fun s t hsA htA hs ht h => by
    rw [← map_multiset_ne_zero_prod _ (by grind [Multiset.card_eq_zero]),
        h, map_multiset_ne_zero_prod _ (by grind [Multiset.card_eq_zero])]

@[deprecated (since := "2026-04-29")]
alias MonoidHomClass.isMulFreimanHom := MulHomClass.isMulFreimanHom

@[deprecated (since := "2026-04-29")]
alias AddMonoidHomClass.isAddFreimanHom := AddHomClass.isAddFreimanHom
-/
@[to_additive] lemma MulHomClass.isMulFreimanHom [FunLike F α β] [MulHomClass F α β] (f : F)
    (hfAB : MapsTo f A B) : IsMulFreimanHom n A B f :=
  match n with
  | 0 => by simpa
  | n + 1 => IsMulFreimanHom.mk hfAB fun s t hsA htA hs ht h => by
    rw [← map_multiset_ne_zero_prod _ (by grind [Multiset.card_eq_zero]),
        h, map_multiset_ne_zero_prod _ (by grind [Multiset.card_eq_zero])]

@[deprecated (since := "2026-04-29")]
alias MonoidHomClass.isMulFreimanHom := MulHomClass.isMulFreimanHom

@[deprecated (since := "2026-04-29")]
alias AddMonoidHomClass.isAddFreimanHom := AddHomClass.isAddFreimanHom

/--
lemma `MulEquivClass.isMulFreimanIso` / 引理 `MulEquivClass.isMulFreimanIso`

English:
lemma MulEquivClass.isMulFreimanIso
  statement: [EquivLike F α β] [MulEquivClass F α β] (f : F)
  proof: hfAB
  map_prod_eq_map_prod s t _ _ _ _ := by
    rw [← map_multiset_prod]; rw [← map_multiset_prod]; rw [EquivLike.apply_eq_iff_eq]

@[to_additive]

中文:
引理 乘法等价类.isMulFreimanIso
  结论: [等价状 F α β] [乘法等价类 F α β] (f : F)
  证明: hfAB
  map_prod_eq_map_prod s t _ _ _ _ := by
    rw [← map_multiset_prod]; rw [← map_multiset_prod]; rw [EquivLike.apply_eq_iff_eq]

@[to_additive]
-/
@[to_additive] lemma MulEquivClass.isMulFreimanIso [EquivLike F α β] [MulEquivClass F α β] (f : F)
    (hfAB : BijOn f A B) : IsMulFreimanIso n A B f where
  bijOn := hfAB
  map_prod_eq_map_prod s t _ _ _ _ := by
    rw [← map_multiset_prod]; rw [← map_multiset_prod]; rw [EquivLike.apply_eq_iff_eq]

@[to_additive]
/--
lemma `IsMulFreimanHom.subtypeVal` / 引理 `IsMulFreimanHom.subtypeVal`

English:
lemma IsMulFreimanHom.subtypeVal
  given: {S : Type*} [SetLike S α] [SubmonoidClass S α] {s : S}
  proof: MulHomClass.isMulFreimanHom (SubmonoidClass.subtype s) (mapsTo_univ ..)

中文:
引理 是MulFreiman态射.subtypeVal
  条件: {S : 类型} [集合状 S α] [子幺半群类 S α] {s : S}
  证明: MulHomClass.isMulFreimanHom (SubmonoidClass.subtype s) (mapsTo_univ ..)

Depends on / 依赖: MulHomClass, MulHomClass.isMulFreimanHom, SubmonoidClass, SubmonoidClass.subtype, isMulFreimanHom, mapsTo_univ, subtype
-/
lemma IsMulFreimanHom.subtypeVal {S : Type*} [SetLike S α] [SubmonoidClass S α] {s : S} :
    IsMulFreimanHom n (univ : Set s) univ Subtype.val :=
  MulHomClass.isMulFreimanHom (SubmonoidClass.subtype s) (mapsTo_univ ..)

end CommMonoid

section CancelCommMonoid
variable [CommMonoid α] [CancelCommMonoid β] {A : Set α} {B : Set β} {f : α -> β} {m n : Nat}

@[to_additive]
/--
lemma `isMulFreimanHom_antitone` / 引理 `isMulFreimanHom_antitone`

English:
lemma isMulFreimanHom_antitone
  statement: Antitone (IsMulFreimanHom · A B f)
  proof: antitone_nat_of_succ_le fun n hf =>
  { mapsTo := hf.mapsTo,
    map_prod_eq_map_prod := fun s t hsA htA hs _ h => match n with
      | 0 => by aesop
      | n + 1 => by
        have ⟨a, ha⟩ : exists a, a in s := card_pos_iff_exists_mem.1 (by simp [hs])
        simpa [*] using hf.map_prod_eq_map_prod (s := a ::ₘ s) (t := a ::ₘ t)
            (by simpa [hsA ha]) (by simpa [hsA ha]) }

@[to_additive]

中文:
引理 isMulFreimanHom_antitone
  结论: 递减 (是MulFreiman态射 · A B f)
  证明: antitone_nat_of_succ_le fun n hf =>
  { mapsTo := hf.mapsTo,
    map_prod_eq_map_prod := fun s t hsA htA hs _ h => match n with
      | 0 => by aesop
      | n + 1 => by
        have ⟨a, ha⟩ : exists a, a in s := card_pos_iff_exists_mem.1 (by simp [hs])
        simpa [*] using hf.map_prod_eq_map_prod (s := a ::ₘ s) (t := a ::ₘ t)
            (by simpa [hsA ha]) (by simpa [hsA ha]) }

@[to_additive]

Depends on / 依赖: antitone_nat_of_succ_le, card_pos_iff_exists_mem, hf.map_prod_eq_map_prod, hf.mapsTo, map_prod_eq_map_prod, mapsTo
-/
lemma isMulFreimanHom_antitone : Antitone (IsMulFreimanHom · A B f) :=
  antitone_nat_of_succ_le fun n hf =>
  { mapsTo := hf.mapsTo,
    map_prod_eq_map_prod := fun s t hsA htA hs _ h => match n with
      | 0 => by aesop
      | n + 1 => by
        have ⟨a, ha⟩ : exists a, a in s := card_pos_iff_exists_mem.1 (by simp [hs])
        simpa [*] using hf.map_prod_eq_map_prod (s := a ::ₘ s) (t := a ::ₘ t)
            (by simpa [hsA ha]) (by simpa [hsA ha]) }

@[to_additive]
/--
lemma `IsMulFreimanHom.mono` / 引理 `IsMulFreimanHom.mono`

English:
lemma IsMulFreimanHom.mono
  given: (hmn : m <= n) (hf : IsMulFreimanHom n A B f)
  statement: IsMulFreimanHom m A B f
  proof: isMulFreimanHom_antitone hmn hf

中文:
引理 是MulFreiman态射.mono
  条件: (hmn : m <= n) (hf : 是MulFreiman态射 n A B f)
  结论: 是MulFreiman态射 m A B f
  证明: isMulFreimanHom_antitone hmn hf

Depends on / 依赖: isMulFreimanHom_antitone
-/
lemma IsMulFreimanHom.mono (hmn : m <= n) (hf : IsMulFreimanHom n A B f) : IsMulFreimanHom m A B f :=
  isMulFreimanHom_antitone hmn hf

end CancelCommMonoid

section CancelCommMonoid
variable [CancelCommMonoid α] [CancelCommMonoid β] {A : Set α} {B : Set β} {f : α -> β} {m n : Nat}

@[to_additive]
/--
lemma `IsMulFreimanIso.mono` / 引理 `IsMulFreimanIso.mono`

English:
lemma IsMulFreimanIso.mono
  given: {hmn : m <= n} (hf : IsMulFreimanIso n A B f)
  proof: (hf.isMulFreimanHom.mono hmn).to_isMulFreimanIso hf.bijOn.invOn_invFunOn
    (hf.invFunOn.isMulFreimanHom.mono hmn)

中文:
引理 是MulFreimanIso.mono
  条件: {hmn : m <= n} (hf : 是MulFreimanIso n A B f)
  证明: (hf.isMulFreimanHom.mono hmn).to_isMulFreimanIso hf.bijOn.invOn_invFunOn
    (hf.invFunOn.isMulFreimanHom.mono hmn)

Depends on / 依赖: hf.bijOn.invOn_invFunOn, hf.invFunOn.isMulFreimanHom.mono, hf.isMulFreimanHom.mono, invFunOn, invOn_invFunOn, isMulFreimanHom, to_isMulFreimanIso
-/
lemma IsMulFreimanIso.mono {hmn : m <= n} (hf : IsMulFreimanIso n A B f) :
    IsMulFreimanIso m A B f :=
  (hf.isMulFreimanHom.mono hmn).to_isMulFreimanIso hf.bijOn.invOn_invFunOn
    (hf.invFunOn.isMulFreimanHom.mono hmn)

end CancelCommMonoid

section DivisionCommMonoid
variable [CommMonoid α] [DivisionCommMonoid β] {A : Set α} {B : Set β} {f : α -> β} {n : Nat}

@[to_additive]
/--
lemma `IsMulFreimanHom.inv` / 引理 `IsMulFreimanHom.inv`

English:
lemma IsMulFreimanHom.inv
  given: (hf : IsMulFreimanHom n A B f)
  statement: IsMulFreimanHom n A B⁻¹ f⁻¹ where
  proof: hf.mapsTo.inv
  map_prod_eq_map_prod s t hsA htA hs ht h := by
    rw [Pi.inv_def]; rw [prod_map_inv]; rw [prod_map_inv]; rw [hf.map_prod_eq_map_prod hsA htA hs ht h]

中文:
引理 是MulFreiman态射.inv
  条件: (hf : 是MulFreiman态射 n A B f)
  结论: 是MulFreiman态射 n A B⁻¹ f⁻¹ where
  证明: hf.mapsTo.inv
  map_prod_eq_map_prod s t hsA htA hs ht h := by
    rw [Pi.inv_def]; rw [prod_map_inv]; rw [prod_map_inv]; rw [hf.map_prod_eq_map_prod hsA htA hs ht h]

Depends on / 依赖: hf.mapsTo.inv, mapsTo
-/
lemma IsMulFreimanHom.inv (hf : IsMulFreimanHom n A B f) : IsMulFreimanHom n A B⁻¹ f⁻¹ where
  mapsTo := hf.mapsTo.inv
  map_prod_eq_map_prod s t hsA htA hs ht h := by
    rw [Pi.inv_def]; rw [prod_map_inv]; rw [prod_map_inv]; rw [hf.map_prod_eq_map_prod hsA htA hs ht h]

/--
lemma `IsMulFreimanHom.div` / 引理 `IsMulFreimanHom.div`

English:
lemma IsMulFreimanHom.div
  statement: {β : Type*} [DivisionCommMonoid β] {B₁ B₂ : Set β}
  proof: h₁.mapsTo.div h₂.mapsTo
  map_prod_eq_map_prod s t hsA htA hs ht h := by
    rw [Pi.div_def]; rw [prod_map_div]; rw [prod_map_div]; rw [h₁.map_prod_eq_map_prod hsA htA hs ht h]; rw [h₂.map_prod_eq_map_prod hsA htA hs ht h]

中文:
引理 是MulFreiman态射.div
  结论: {β : 类型} [DivisionComm幺半群 β] {B₁ B₂ : 集合 β}
  证明: h₁.mapsTo.div h₂.mapsTo
  map_prod_eq_map_prod s t hsA htA hs ht h := by
    rw [Pi.div_def]; rw [prod_map_div]; rw [prod_map_div]; rw [h₁.map_prod_eq_map_prod hsA htA hs ht h]; rw [h₂.map_prod_eq_map_prod hsA htA hs ht h]
-/
@[to_additive] lemma IsMulFreimanHom.div {β : Type*} [DivisionCommMonoid β] {B₁ B₂ : Set β}
    {f₁ f₂ : α -> β} (h₁ : IsMulFreimanHom n A B₁ f₁) (h₂ : IsMulFreimanHom n A B₂ f₂) :
    IsMulFreimanHom n A (B₁ / B₂) (f₁ / f₂) where
  mapsTo := h₁.mapsTo.div h₂.mapsTo
  map_prod_eq_map_prod s t hsA htA hs ht h := by
    rw [Pi.div_def]; rw [prod_map_div]; rw [prod_map_div]; rw [h₁.map_prod_eq_map_prod hsA htA hs ht h]; rw [h₂.map_prod_eq_map_prod hsA htA hs ht h]

end DivisionCommMonoid

section Prod

@[to_additive]
/--
lemma `IsMulFreimanHom.fst` / 引理 `IsMulFreimanHom.fst`

English:
lemma IsMulFreimanHom.fst
  given: [CommMonoid α] [CommMonoid β] {A : Set α} {B : Set β} {n : Nat}
  proof: MulHomClass.isMulFreimanHom (MonoidHom.fst _ _) mapsTo_fst_prod

@[to_additive]

中文:
引理 是MulFreiman态射.fst
  条件: [交换幺半群 α] [交换幺半群 β] {A : 集合 α} {B : 集合 β} {n : 自然数}
  证明: MulHomClass.isMulFreimanHom (MonoidHom.fst _ _) mapsTo_fst_prod

@[to_additive]

Depends on / 依赖: MonoidHom, MonoidHom.fst, MulHomClass, MulHomClass.isMulFreimanHom, isMulFreimanHom, mapsTo_fst_prod
-/
lemma IsMulFreimanHom.fst [CommMonoid α] [CommMonoid β] {A : Set α} {B : Set β} {n : Nat} :
    IsMulFreimanHom n (A ×ˢ B) A Prod.fst :=
  MulHomClass.isMulFreimanHom (MonoidHom.fst _ _) mapsTo_fst_prod

@[to_additive]
/--
lemma `IsMulFreimanHom.snd` / 引理 `IsMulFreimanHom.snd`

English:
lemma IsMulFreimanHom.snd
  given: [CommMonoid α] [CommMonoid β] {A : Set α} {B : Set β} {n : Nat}
  proof: MulHomClass.isMulFreimanHom (MonoidHom.snd _ _) mapsTo_snd_prod

中文:
引理 是MulFreiman态射.snd
  条件: [交换幺半群 α] [交换幺半群 β] {A : 集合 α} {B : 集合 β} {n : 自然数}
  证明: MulHomClass.isMulFreimanHom (MonoidHom.snd _ _) mapsTo_snd_prod

Depends on / 依赖: MonoidHom, MonoidHom.snd, MulHomClass, MulHomClass.isMulFreimanHom, isMulFreimanHom, mapsTo_snd_prod
-/
lemma IsMulFreimanHom.snd [CommMonoid α] [CommMonoid β] {A : Set α} {B : Set β} {n : Nat} :
    IsMulFreimanHom n (A ×ˢ B) B Prod.snd :=
  MulHomClass.isMulFreimanHom (MonoidHom.snd _ _) mapsTo_snd_prod

section

variable {α β₁ β₂ : Type*} [CommMonoid α] [CommMonoid β₁] [CommMonoid β₂]
  {A : Set α} {B₁ : Set β₁} {B₂ : Set β₂} {f₁ : α -> β₁} {f₂ : α -> β₂} {n : Nat}

@[to_additive prodMk]
/--
lemma `IsMulFreimanHom.prodMk` / 引理 `IsMulFreimanHom.prodMk`

English:
lemma IsMulFreimanHom.prodMk
  given: (h₁ : IsMulFreimanHom n A B₁ f₁) (h₂ : IsMulFreimanHom n A B₂ f₂)
  proof: fun x hx => mk_mem_prod (h₁.mapsTo hx) (h₂.mapsTo hx)
  map_prod_eq_map_prod s t hsA htA hs ht h := by
    simp [Prod.ext_iff, fst_prod, snd_prod,
      h₁.map_prod_eq_map_prod hsA htA hs ht h, h₂.map_prod_eq_map_prod hsA htA hs ht h]

中文:
引理 是MulFreiman态射.prodMk
  条件: (h₁ : 是MulFreiman态射 n A B₁ f₁) (h₂ : 是MulFreiman态射 n A B₂ f₂)
  证明: fun x hx => mk_mem_prod (h₁.mapsTo hx) (h₂.mapsTo hx)
  map_prod_eq_map_prod s t hsA htA hs ht h := by
    simp [Prod.ext_iff, fst_prod, snd_prod,
      h₁.map_prod_eq_map_prod hsA htA hs ht h, h₂.map_prod_eq_map_prod hsA htA hs ht h]

Depends on / 依赖: mapsTo, mk_mem_prod
-/
lemma IsMulFreimanHom.prodMk (h₁ : IsMulFreimanHom n A B₁ f₁) (h₂ : IsMulFreimanHom n A B₂ f₂) :
    IsMulFreimanHom n A (B₁ ×ˢ B₂) (fun x => (f₁ x, f₂ x)) where
  mapsTo := fun x hx => mk_mem_prod (h₁.mapsTo hx) (h₂.mapsTo hx)
  map_prod_eq_map_prod s t hsA htA hs ht h := by
    simp [Prod.ext_iff, fst_prod, snd_prod,
      h₁.map_prod_eq_map_prod hsA htA hs ht h, h₂.map_prod_eq_map_prod hsA htA hs ht h]

end

section

variable {α₁ α₂ β₁ β₂ : Type*} [CommMonoid α₁] [CommMonoid α₂] [CommMonoid β₁] [CommMonoid β₂]
  {A₁ : Set α₁} {A₂ : Set α₂} {B₁ : Set β₁} {B₂ : Set β₂} {f₁ : α₁ -> β₁} {f₂ : α₂ -> β₂} {n : Nat}

@[to_additive prodMap]
/--
lemma `IsMulFreimanHom.prodMap` / 引理 `IsMulFreimanHom.prodMap`

English:
lemma IsMulFreimanHom.prodMap
  given: (h₁ : IsMulFreimanHom n A₁ B₁ f₁) (h₂ : IsMulFreimanHom n A₂ B₂ f₂)
  proof: (h₁.comp .fst).prodMk (h₂.comp .snd)

@[to_additive prodMap]

中文:
引理 是MulFreiman态射.prodMap
  条件: (h₁ : 是MulFreiman态射 n A₁ B₁ f₁) (h₂ : 是MulFreiman态射 n A₂ B₂ f₂)
  证明: (h₁.comp .fst).prodMk (h₂.comp .snd)

@[to_additive prodMap]

Depends on / 依赖: prodMk
-/
lemma IsMulFreimanHom.prodMap (h₁ : IsMulFreimanHom n A₁ B₁ f₁) (h₂ : IsMulFreimanHom n A₂ B₂ f₂) :
    IsMulFreimanHom n (A₁ ×ˢ A₂) (B₁ ×ˢ B₂) (Prod.map f₁ f₂) :=
  (h₁.comp .fst).prodMk (h₂.comp .snd)

@[to_additive prodMap]
/--
lemma `IsMulFreimanIso.prodMap` / 引理 `IsMulFreimanIso.prodMap`

English:
lemma IsMulFreimanIso.prodMap
  given: (h₁ : IsMulFreimanIso n A₁ B₁ f₁) (h₂ : IsMulFreimanIso n A₂ B₂ f₂)
  proof: (h₁.isMulFreimanHom.prodMap h₂.isMulFreimanHom).to_isMulFreimanIso
    (h₁.bijOn.invOn_invFunOn.prodMap h₂.bijOn.invOn_invFunOn)
    (h₁.invFunOn.isMulFreimanHom.prodMap h₂.invFunOn.isMulFreimanHom)

中文:
引理 是MulFreimanIso.prodMap
  条件: (h₁ : 是MulFreimanIso n A₁ B₁ f₁) (h₂ : 是MulFreimanIso n A₂ B₂ f₂)
  证明: (h₁.isMulFreimanHom.prodMap h₂.isMulFreimanHom).to_isMulFreimanIso
    (h₁.bijOn.invOn_invFunOn.prodMap h₂.bijOn.invOn_invFunOn)
    (h₁.invFunOn.isMulFreimanHom.prodMap h₂.invFunOn.isMulFreimanHom)

Depends on / 依赖: bijOn.invOn_invFunOn, bijOn.invOn_invFunOn.prodMap, invFunOn, invFunOn.isMulFreimanHom, invFunOn.isMulFreimanHom.prodMap, invOn_invFunOn, isMulFreimanHom, isMulFreimanHom.prodMap, prodMap, to_isMulFreimanIso
-/
lemma IsMulFreimanIso.prodMap (h₁ : IsMulFreimanIso n A₁ B₁ f₁) (h₂ : IsMulFreimanIso n A₂ B₂ f₂) :
    IsMulFreimanIso n (A₁ ×ˢ A₂) (B₁ ×ˢ B₂) (Prod.map f₁ f₂) :=
  (h₁.isMulFreimanHom.prodMap h₂.isMulFreimanHom).to_isMulFreimanIso
    (h₁.bijOn.invOn_invFunOn.prodMap h₂.bijOn.invOn_invFunOn)
    (h₁.invFunOn.isMulFreimanHom.prodMap h₂.invFunOn.isMulFreimanHom)

end

end Prod

namespace Fin
variable {k m n : Nat}

open Fin.CommRing

/--
lemma `aux` / 引理 `aux`

English:
lemma aux
  given: (hm : m != 0) (hkmn : m * k <= n)
  statement: k < (n + 1)
  proof: Nat.lt_succ_iff.2 le_trans (Nat.le_mul_of_pos_left _ hm.bot_lt) hkmn

中文:
引理 aux
  条件: (hm : m != 0) (hkmn : m * k <= n)
  结论: k < (n + 1)
  证明: Nat.lt_succ_iff.2 le_trans (Nat.le_mul_of_pos_left _ hm.bot_lt) hkmn
-/
private lemma aux (hm : m != 0) (hkmn : m * k <= n) : k < (n + 1) :=
Nat.lt_succ_iff.2 le_trans (Nat.le_mul_of_pos_left _ hm.bot_lt) hkmn

/--
lemma `isAddFreimanIso_Iic` / 引理 `isAddFreimanIso_Iic`

English:
lemma isAddFreimanIso_Iic
  given: (hm : m != 0) (hkmn : m * k <= n)
  proof: by simp [MapsTo, Fin.le_iff_val_le_val, Nat.mod_eq_of_lt, aux hm hkmn]
  bijOn.right.left := val_injective.injOn
  bijOn.right.right x (hx : x <= _) :=
    ⟨x, by simpa [le_iff_val_le_val, -val_fin_le, Nat.mod_eq_of_lt, aux hm hkmn, hx.trans_lt]⟩
  map_sum_eq_map_sum s t hsA htA hs ht := by
    have (u : Multiset (Fin (n + 1))) : Nat.castRingHom _ (u.map val).sum = u.sum := by simp
    rw [← this]; rw [← this]
    have {u : Multiset (Fin (n + 1))} (huk : forall x in u, x <= k) (hu : card u = m) :
(u.map val).sum < (n + 1) := Nat.lt_succ_iff.2 hkmn.trans' by
      rw [← hu]; rw [← card_map]
      refine sum_le_card_nsmul (u.map val) k ?_
      simpa [le_iff_val_le_val, -val_fin_le, Nat.mod_eq_of_lt, aux hm hkmn] using huk
    exact ⟨congr_arg _, CharP.natCast_injOn_Iio _ (n + 1) (this hsA hs) (this htA ht)⟩

中文:
引理 isAddFreimanIso_Iic
  条件: (hm : m != 0) (hkmn : m * k <= n)
  证明: by simp [MapsTo, Fin.le_iff_val_le_val, Nat.mod_eq_of_lt, aux hm hkmn]
  bijOn.right.left := val_injective.injOn
  bijOn.right.right x (hx : x <= _) :=
    ⟨x, by simpa [le_iff_val_le_val, -val_fin_le, Nat.mod_eq_of_lt, aux hm hkmn, hx.trans_lt]⟩
  map_sum_eq_map_sum s t hsA htA hs ht := by
    have (u : Multiset (Fin (n + 1))) : Nat.castRingHom _ (u.map val).sum = u.sum := by simp
    rw [← this]; rw [← this]
    have {u : Multiset (Fin (n + 1))} (huk : forall x in u, x <= k) (hu : card u = m) :
(u.map val).sum < (n + 1) := Nat.lt_succ_iff.2 hkmn.trans' by
      rw [← hu]; rw [← card_map]
      refine sum_le_card_nsmul (u.map val) k ?_
      simpa [le_iff_val_le_val, -val_fin_le, Nat.mod_eq_of_lt, aux hm hkmn] using huk
    exact ⟨congr_arg _, CharP.natCast_injOn_Iio _ (n + 1) (this hsA hs) (this htA ht)⟩

Depends on / 依赖: Fin.le_iff_val_le_val, MapsTo, Multiset, Nat.castRingHom, Nat.mod_eq_of_lt, bijOn.right.left, bijOn.right.right, castRingHom, hx.trans_lt, le_iff_val_le_val, map_sum_eq_map_sum, mod_eq_of_lt, trans_lt, u.map, u.sum, val_fin_le, val_injective, val_injective.injOn
-/
lemma isAddFreimanIso_Iic (hm : m != 0) (hkmn : m * k <= n) :
    IsAddFreimanIso m (Iic (k : Fin (n + 1))) (Iic k) val where
  bijOn.left := by simp [MapsTo, Fin.le_iff_val_le_val, Nat.mod_eq_of_lt, aux hm hkmn]
  bijOn.right.left := val_injective.injOn
  bijOn.right.right x (hx : x <= _) :=
    ⟨x, by simpa [le_iff_val_le_val, -val_fin_le, Nat.mod_eq_of_lt, aux hm hkmn, hx.trans_lt]⟩
  map_sum_eq_map_sum s t hsA htA hs ht := by
    have (u : Multiset (Fin (n + 1))) : Nat.castRingHom _ (u.map val).sum = u.sum := by simp
    rw [← this]; rw [← this]
    have {u : Multiset (Fin (n + 1))} (huk : forall x in u, x <= k) (hu : card u = m) :
(u.map val).sum < (n + 1) := Nat.lt_succ_iff.2 hkmn.trans' by
      rw [← hu]; rw [← card_map]
      refine sum_le_card_nsmul (u.map val) k ?_
      simpa [le_iff_val_le_val, -val_fin_le, Nat.mod_eq_of_lt, aux hm hkmn] using huk
    exact ⟨congr_arg _, CharP.natCast_injOn_Iio _ (n + 1) (this hsA hs) (this htA ht)⟩

/--
lemma `isAddFreimanIso_Iio` / 引理 `isAddFreimanIso_Iio`

English:
lemma isAddFreimanIso_Iio
  given: (hm : m != 0) (hkmn : m * k <= n)
  proof: by
  obtain _ | k := k
  · simp
  have hkmn' : m * k <= n := (Nat.mul_le_mul_left _ k.le_succ).trans hkmn
  convert! isAddFreimanIso_Iic hm hkmn' using 1 <;> ext x
  · simp only [Nat.cast_add, Nat.cast_one, mem_Iio, lt_def, mem_Iic, le_iff_val_le_val,
      val_natCast, aux hm hkmn', Nat.mod_eq_of_lt]
    simp_rw [← Nat.cast_add_one]
    rw [Fin.val_cast_of_lt (aux hm hkmn)]; rw [Nat.lt_succ_iff]
  · simp [Nat.lt_succ_iff]

中文:
引理 isAddFreimanIso_Iio
  条件: (hm : m != 0) (hkmn : m * k <= n)
  证明: by
  obtain _ | k := k
  · simp
  have hkmn' : m * k <= n := (Nat.mul_le_mul_left _ k.le_succ).trans hkmn
  convert! isAddFreimanIso_Iic hm hkmn' using 1 <;> ext x
  · simp only [Nat.cast_add, Nat.cast_one, mem_Iio, lt_def, mem_Iic, le_iff_val_le_val,
      val_natCast, aux hm hkmn', Nat.mod_eq_of_lt]
    simp_rw [← Nat.cast_add_one]
    rw [Fin.val_cast_of_lt (aux hm hkmn)]; rw [Nat.lt_succ_iff]
  · simp [Nat.lt_succ_iff]

Depends on / 依赖: Fin.val_cast_of_lt, Nat.cast_add, Nat.cast_add_one, Nat.cast_one, Nat.lt_succ_iff, Nat.mod_eq_of_lt, Nat.mul_le_mul_left, cast_add, cast_add_one, cast_one, convert, isAddFreimanIso_Iic, k.le_succ, le_iff_val_le_val, le_succ, lt_def, lt_succ_iff, mem_Iic, mem_Iio, mod_eq_of_lt
-/
lemma isAddFreimanIso_Iio (hm : m != 0) (hkmn : m * k <= n) :
    IsAddFreimanIso m (Iio (k : Fin (n + 1))) (Iio k) val := by
  obtain _ | k := k
  · simp
  have hkmn' : m * k <= n := (Nat.mul_le_mul_left _ k.le_succ).trans hkmn
  convert! isAddFreimanIso_Iic hm hkmn' using 1 <;> ext x
  · simp only [Nat.cast_add, Nat.cast_one, mem_Iio, lt_def, mem_Iic, le_iff_val_le_val,
      val_natCast, aux hm hkmn', Nat.mod_eq_of_lt]
    simp_rw [← Nat.cast_add_one]
    rw [Fin.val_cast_of_lt (aux hm hkmn)]; rw [Nat.lt_succ_iff]
  · simp [Nat.lt_succ_iff]

end Fin
