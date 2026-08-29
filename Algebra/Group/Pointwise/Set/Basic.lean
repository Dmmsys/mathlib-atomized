/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Floris van Doorn, Yaël Dillies
-/
module

public import Mathlib.Algebra.Group.Equiv.Basic
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Order.Monoid.Unbundled.Pow
public import Mathlib.Data.Set.NAry

/-!
# Pointwise operations of sets

This file defines pointwise algebraic operations on sets.

## Main declarations

For sets `s` and `t` and scalar `a`:
* `s * t`: Multiplication, set of all `x * y` where `x ∈ s` and `y ∈ t`.
* `s + t`: Addition, set of all `x + y` where `x ∈ s` and `y ∈ t`.
* `s⁻¹`: Inversion, set of all `x⁻¹` where `x ∈ s`.
* `-s`: Negation, set of all `-x` where `x ∈ s`.
* `s / t`: Division, set of all `x / y` where `x ∈ s` and `y ∈ t`.
* `s - t`: Subtraction, set of all `x - y` where `x ∈ s` and `y ∈ t`.

For `α` a semigroup/monoid, `Set α` is a semigroup/monoid.
As an unfortunate side effect, this means that `n • s`, where `n : ℕ`, is ambiguous between
pointwise scaling and repeated pointwise addition; the former has `(2 : ℕ) • {1, 2} = {2, 4}`, while
the latter has `(2 : ℕ) • {1, 2} = {2, 3, 4}`. See note [pointwise nat action].

Appropriate definitions and results are also transported to the additive theory via `to_additive`.

## Implementation notes

* The following expressions are considered in simp-normal form in a group:
  `(fun h ↦ h * g) ⁻¹' s`, `(fun h ↦ g * h) ⁻¹' s`, `(fun h ↦ h * g⁻¹) ⁻¹' s`,
  `(fun h ↦ g⁻¹ * h) ⁻¹' s`, `s * t`, `s⁻¹`, `(1 : Set _)` (and similarly for additive variants).
  Expressions equal to one of these will be simplified.
* We put all instances in the scope `Pointwise`, so that these instances are not available by
  default. Note that we do not mark them as reducible (as argued by note [reducible non-instances])
  since we expect the scope to be open whenever the instances are actually used (and making the
  instances reducible changes the behavior of `simp`).

## Tags

set multiplication, set addition, pointwise addition, pointwise multiplication,
pointwise subtraction
-/

@[expose] public section

assert_not_exists Set.iUnion MulAction MonoidWithZero IsOrderedMonoid

library_note «pointwise nat action» /--
Pointwise monoids (`Set`, `Finset`, `Filter`) have derived pointwise actions of the form
`SMul α β → SMul α (Set β)`. When `α` is `ℕ` or `ℤ`, this action conflicts with the
nat or int action coming from `Set β` being a `Monoid` or `DivInvMonoid`. For example,
`2 • {a, b}` can both be `{2 • a, 2 • b}` (pointwise action, pointwise repeated addition,
`Set.smulSet`) and `{a + a, a + b, b + a, b + b}` (nat or int action, repeated pointwise
addition, `Set.NSMul`).

Because the pointwise action can easily be spelled out in such cases, we give higher priority to the
nat and int actions.
-/

open Function MulOpposite

variable {F α β γ : Type*}

namespace Set

/-! ### `0`/`1` as sets -/

section One

variable [One α] {s : Set α} {a : α}

/-- The set `1 : Set α` is defined as `{1}` in scope `Pointwise`. -/
@[to_additive (attr := instance_reducible)
  /-- The set `0 : Set α` is defined as `{0}` in scope `Pointwise`. -/]
/--
Definition of `one` / `one` 的定义

English:
definition one
  signature: : One (Set α)
  body: ⟨{1}⟩

scoped[Pointwise] attribute [instance] Set.one Set.zero

中文:
定义 one
  签名: : 幺 (集合 α)
  定义体: ⟨{1}⟩

scoped[Pointwise] attribute [instance] Set.one Set.zero
-/
protected def one : One (Set α) :=
  ⟨{1}⟩

scoped[Pointwise] attribute [instance] Set.one Set.zero

open scoped Pointwise

-- TODO: This would be a good simp lemma scoped to `Pointwise`, but it seems `@[simp]` can't be
-- scoped
@[to_additive]
/--
theorem `singleton_one` / 定理 `singleton_one`

English:
theorem singleton_one
  statement: ({1} : Set α) = 1
  proof: rfl

@[to_additive (attr := simp, push)]

中文:
定理 singleton_one
  结论: ({1} : 集合 α) = 1
  证明: rfl

@[to_additive (attr := simp, push)]
-/
theorem singleton_one : ({1} : Set α) = 1 :=
  rfl

@[to_additive (attr := simp, push)]
/--
theorem `mem_one` / 定理 `mem_one`

English:
theorem mem_one
  statement: a in (1 : Set α) ↔ a = 1
  proof: Iff.rfl

@[to_additive]

中文:
定理 mem_one
  结论: a in (1 : 集合 α) ↔ a = 1
  证明: Iff.rfl

@[to_additive]

Depends on / 依赖: Iff.rfl
-/
theorem mem_one : a in (1 : Set α) ↔ a = 1 :=
  Iff.rfl

@[to_additive]
/--
theorem `one_mem_one` / 定理 `one_mem_one`

English:
theorem one_mem_one
  statement: (1 : α) in (1 : Set α)
  proof: Eq.refl _

@[to_additive (attr := simp)]

中文:
定理 one_mem_one
  结论: (1 : α) in (1 : 集合 α)
  证明: Eq.refl _

@[to_additive (attr := simp)]

Depends on / 依赖: Eq.refl
-/
theorem one_mem_one : (1 : α) in (1 : Set α) :=
  Eq.refl _

@[to_additive (attr := simp)]
/--
theorem `one_subset` / 定理 `one_subset`

English:
theorem one_subset
  statement: 1 subseteq s ↔ (1 : α) in s
  proof: singleton_subset_iff

@[to_additive (attr := simp)]

中文:
定理 one_subset
  结论: 1 subseteq s ↔ (1 : α) in s
  证明: singleton_subset_iff

@[to_additive (attr := simp)]

Depends on / 依赖: singleton_subset_iff
-/
theorem one_subset : 1 subseteq s ↔ (1 : α) in s :=
  singleton_subset_iff

@[to_additive (attr := simp)]
/--
theorem `one_nonempty` / 定理 `one_nonempty`

English:
theorem one_nonempty
  statement: (1 : Set α).Nonempty
  proof: ⟨1, rfl⟩

@[to_additive (attr := simp)]

中文:
定理 one_nonempty
  结论: (1 : 集合 α).非空
  证明: ⟨1, rfl⟩

@[to_additive (attr := simp)]
-/
theorem one_nonempty : (1 : Set α).Nonempty :=
  ⟨1, rfl⟩

@[to_additive (attr := simp)]
/--
theorem `image_one` / 定理 `image_one`

English:
theorem image_one
  given: {f : α -> β}
  statement: f '' 1 = {f 1}
  proof: image_singleton

@[to_additive]

中文:
定理 image_one
  条件: {f : α -> β}
  结论: f '' 1 = {f 1}
  证明: image_singleton

@[to_additive]

Depends on / 依赖: image_singleton
-/
theorem image_one {f : α -> β} : f '' 1 = {f 1} :=
  image_singleton

@[to_additive]
/--
theorem `subset_one_iff_eq` / 定理 `subset_one_iff_eq`

English:
theorem subset_one_iff_eq
  statement: s subseteq 1 ↔ s = ∅ ∨ s = 1
  proof: subset_singleton_iff_eq

@[to_additive]

中文:
定理 subset_one_iff_eq
  结论: s subseteq 1 ↔ s = ∅ ∨ s = 1
  证明: subset_singleton_iff_eq

@[to_additive]

Depends on / 依赖: subset_singleton_iff_eq
-/
theorem subset_one_iff_eq : s subseteq 1 ↔ s = ∅ ∨ s = 1 :=
  subset_singleton_iff_eq

@[to_additive]
/--
theorem `Nonempty.subset_one_iff` / 定理 `Nonempty.subset_one_iff`

English:
theorem Nonempty.subset_one_iff
  given: (h : s.Nonempty)
  statement: s subseteq 1 ↔ s = 1
  proof: h.subset_singleton_iff

中文:
定理 非空.subset_one_iff
  条件: (h : s.非空)
  结论: s subseteq 1 ↔ s = 1
  证明: h.subset_singleton_iff
-/
theorem Nonempty.subset_one_iff (h : s.Nonempty) : s subseteq 1 ↔ s = 1 :=
  h.subset_singleton_iff

/-- The singleton operation as a `OneHom`. -/
@[to_additive /-- The singleton operation as a `ZeroHom`. -/]
/--
Definition of `singletonOneHom` / `singletonOneHom` 的定义

English:
definition singletonOneHom
  signature: : OneHom α (Set α) where
  body: singleton; map_one' := singleton_one

@[to_additive (attr := simp)]

中文:
定义 singletonOneHom
  签名: : 幺态射 α (集合 α) where
  定义体: singleton; map_one' := singleton_one

@[to_additive (attr := simp)]

Depends on / 依赖: map_one, singleton, singleton_one
-/
def singletonOneHom : OneHom α (Set α) where
  toFun := singleton; map_one' := singleton_one

@[to_additive (attr := simp)]
/--
theorem `coe_singletonOneHom` / 定理 `coe_singletonOneHom`

English:
theorem coe_singletonOneHom
  statement: (singletonOneHom : α -> Set α) = singleton
  proof: rfl

中文:
定理 coe_singletonOneHom
  结论: (singletonOneHom : α -> 集合 α) = singleton
  证明: rfl
-/
theorem coe_singletonOneHom : (singletonOneHom : α -> Set α) = singleton :=
  rfl

/--
lemma `image_op_one` / 引理 `image_op_one`

English:
lemma image_op_one
  statement: (1 : Set α).image op = 1
  proof: image_singleton

@[to_additive (attr := simp) zero_prod_zero]

中文:
引理 image_op_one
  结论: (1 : 集合 α).像 op = 1
  证明: image_singleton

@[to_additive (attr := simp) zero_prod_zero]
-/
@[to_additive] lemma image_op_one : (1 : Set α).image op = 1 := image_singleton

@[to_additive (attr := simp) zero_prod_zero]
/--
lemma `one_prod_one` / 引理 `one_prod_one`

English:
lemma one_prod_one
  given: [One β]
  statement: (1 ×ˢ 1 : Set (α × β)) = 1
  proof: by ext; simp [Prod.ext_iff]

中文:
引理 one_prod_one
  条件: [幺 β]
  结论: (1 ×ˢ 1 : 集合 (α × β)) = 1
  证明: by ext; simp [Prod.ext_iff]

Depends on / 依赖: Prod.ext_iff, ext_iff
-/
lemma one_prod_one [One β] : (1 ×ˢ 1 : Set (α × β)) = 1 := by ext; simp [Prod.ext_iff]

end One

/-! ### Set negation/inversion -/


section Inv

/-- The pointwise inversion of set `s⁻¹` is defined as `{x | x⁻¹ ∈ s}` in scope `Pointwise`. It is
equal to `{x⁻¹ | x ∈ s}`, see `Set.image_inv_eq_inv`. -/
@[to_additive (attr := instance_reducible)
      /-- The pointwise negation of set `-s` is defined as `{x | -x ∈ s}` in scope `Pointwise`.
      It is equal to `{-x | x ∈ s}`, see `Set.image_neg_eq_neg`. -/]
/--
Definition of `inv` / `inv` 的定义

English:
definition inv
  signature: [Inv α]
  body: ⟨preimage Inv.inv⟩

scoped[Pointwise] attribute [instance] Set.inv Set.neg

中文:
定义 inv
  签名: [取逆 α]
  定义体: ⟨preimage Inv.inv⟩

scoped[Pointwise] attribute [instance] Set.inv Set.neg
-/
protected def inv [Inv α] : Inv (Set α) :=
  ⟨preimage Inv.inv⟩

scoped[Pointwise] attribute [instance] Set.inv Set.neg

open scoped Pointwise

section Inv

variable {ι : Sort*} [Inv α] {s t : Set α} {a : α}

@[to_additive (attr := simp)]
/--
theorem `inv_ofPred` / 定理 `inv_ofPred`

English:
theorem inv_ofPred
  given: (p : α -> Prop)
  statement: {x | p x}⁻¹ = {x | p x⁻¹}
  proof: rfl

@[deprecated (since := "2026-07-09")] alias inv_setOf := inv_ofPred
@[deprecated (since := "2026-07-09")] alias neg_setOf := neg_ofPred

@[to_additive (attr := simp, push)]

中文:
定理 inv_ofPred
  条件: (p : α -> 命题)
  结论: {x | p x}⁻¹ = {x | p x⁻¹}
  证明: rfl

@[deprecated (since := "2026-07-09")] alias inv_setOf := inv_ofPred
@[deprecated (since := "2026-07-09")] alias neg_setOf := neg_ofPred

@[to_additive (attr := simp, push)]

Depends on / 依赖: CanLift, Subgroup
-/
theorem inv_ofPred (p : α -> Prop) : {x | p x}⁻¹ = {x | p x⁻¹} :=
  rfl

@[deprecated (since := "2026-07-09")] alias inv_setOf := inv_ofPred
@[deprecated (since := "2026-07-09")] alias neg_setOf := neg_ofPred

@[to_additive (attr := simp, push)]
/--
theorem `mem_inv` / 定理 `mem_inv`

English:
theorem mem_inv
  statement: a in s⁻¹ ↔ a⁻¹ in s
  proof: Iff.rfl

@[to_additive (attr := simp)]

中文:
定理 mem_inv
  结论: a in s⁻¹ ↔ a⁻¹ in s
  证明: Iff.rfl

@[to_additive (attr := simp)]

Depends on / 依赖: Iff.rfl
-/
theorem mem_inv : a in s⁻¹ ↔ a⁻¹ in s :=
  Iff.rfl

@[to_additive (attr := simp)]
/--
theorem `inv_preimage` / 定理 `inv_preimage`

English:
theorem inv_preimage
  statement: Inv.inv ⁻¹' s = s⁻¹
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 inv_preimage
  结论: 取逆.inv ⁻¹' s = s⁻¹
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem inv_preimage : Inv.inv ⁻¹' s = s⁻¹ :=
  rfl

@[to_additive (attr := simp)]
/--
theorem `inv_empty` / 定理 `inv_empty`

English:
theorem inv_empty
  statement: (∅ : Set α)⁻¹ = ∅
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 inv_empty
  结论: (∅ : 集合 α)⁻¹ = ∅
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem inv_empty : (∅ : Set α)⁻¹ = ∅ :=
  rfl

@[to_additive (attr := simp)]
/--
theorem `inv_univ` / 定理 `inv_univ`

English:
theorem inv_univ
  statement: (univ : Set α)⁻¹ = univ
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 inv_univ
  结论: (univ : 集合 α)⁻¹ = univ
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem inv_univ : (univ : Set α)⁻¹ = univ :=
  rfl

@[to_additive (attr := simp)]
/--
theorem `inter_inv` / 定理 `inter_inv`

English:
theorem inter_inv
  statement: (s inter t)⁻¹ = s⁻¹ inter t⁻¹
  proof: preimage_inter

@[to_additive (attr := simp)]

中文:
定理 inter_inv
  结论: (s inter t)⁻¹ = s⁻¹ inter t⁻¹
  证明: preimage_inter

@[to_additive (attr := simp)]

Depends on / 依赖: preimage_inter
-/
theorem inter_inv : (s inter t)⁻¹ = s⁻¹ inter t⁻¹ :=
  preimage_inter

@[to_additive (attr := simp)]
/--
theorem `union_inv` / 定理 `union_inv`

English:
theorem union_inv
  statement: (s union t)⁻¹ = s⁻¹ union t⁻¹
  proof: preimage_union

@[to_additive (attr := simp)]

中文:
定理 union_inv
  结论: (s union t)⁻¹ = s⁻¹ union t⁻¹
  证明: preimage_union

@[to_additive (attr := simp)]

Depends on / 依赖: preimage_union
-/
theorem union_inv : (s union t)⁻¹ = s⁻¹ union t⁻¹ :=
  preimage_union

@[to_additive (attr := simp)]
/--
theorem `compl_inv` / 定理 `compl_inv`

English:
theorem compl_inv
  statement: sᶜ⁻¹ = s⁻¹ᶜ
  proof: preimage_compl

@[to_additive (attr := simp) neg_prod]

中文:
定理 compl_inv
  结论: sᶜ⁻¹ = s⁻¹ᶜ
  证明: preimage_compl

@[to_additive (attr := simp) neg_prod]

Depends on / 依赖: preimage_compl
-/
theorem compl_inv : sᶜ⁻¹ = s⁻¹ᶜ :=
  preimage_compl

@[to_additive (attr := simp) neg_prod]
/--
lemma `inv_prod` / 引理 `inv_prod`

English:
lemma inv_prod
  given: [Inv β] (s : Set α) (t : Set β)
  statement: (s ×ˢ t)⁻¹ = s⁻¹ ×ˢ t⁻¹
  proof: rfl

中文:
引理 inv_prod
  条件: [取逆 β] (s : 集合 α) (t : 集合 β)
  结论: (s ×ˢ t)⁻¹ = s⁻¹ ×ˢ t⁻¹
  证明: rfl
-/
lemma inv_prod [Inv β] (s : Set α) (t : Set β) : (s ×ˢ t)⁻¹ = s⁻¹ ×ˢ t⁻¹ := rfl

end Inv

section InvolutiveInv

variable [InvolutiveInv α] {s t : Set α} {a : α}

@[to_additive]
/--
theorem `inv_mem_inv` / 定理 `inv_mem_inv`

English:
theorem inv_mem_inv
  statement: a⁻¹ in s⁻¹ ↔ a in s
  proof: by simp only [mem_inv, inv_inv]

@[to_additive (attr := simp)]

中文:
定理 inv_mem_inv
  结论: a⁻¹ in s⁻¹ ↔ a in s
  证明: by simp only [mem_inv, inv_inv]

@[to_additive (attr := simp)]

Depends on / 依赖: inv_inv, mem_inv
-/
theorem inv_mem_inv : a⁻¹ in s⁻¹ ↔ a in s := by simp only [mem_inv, inv_inv]

@[to_additive (attr := simp)]
/--
theorem `nonempty_inv` / 定理 `nonempty_inv`

English:
theorem nonempty_inv
  statement: s⁻¹.Nonempty ↔ s.Nonempty
  proof: inv_involutive.surjective.nonempty_preimage

@[to_additive]

中文:
定理 nonempty_inv
  结论: s⁻¹.非空 ↔ s.非空
  证明: inv_involutive.surjective.nonempty_preimage

@[to_additive]

Depends on / 依赖: inv_involutive, inv_involutive.surjective.nonempty_preimage, nonempty_preimage, surjective
-/
theorem nonempty_inv : s⁻¹.Nonempty ↔ s.Nonempty :=
  inv_involutive.surjective.nonempty_preimage

@[to_additive]
/--
theorem `Nonempty.inv` / 定理 `Nonempty.inv`

English:
theorem Nonempty.inv
  given: (h : s.Nonempty)
  statement: s⁻¹.Nonempty
  proof: nonempty_inv.2 h

@[to_additive (attr := simp)]

中文:
定理 非空.inv
  条件: (h : s.非空)
  结论: s⁻¹.非空
  证明: nonempty_inv.2 h

@[to_additive (attr := simp)]

Depends on / 依赖: nonempty_inv
-/
theorem Nonempty.inv (h : s.Nonempty) : s⁻¹.Nonempty :=
  nonempty_inv.2 h

@[to_additive (attr := simp)]
/--
theorem `image_inv_eq_inv` / 定理 `image_inv_eq_inv`

English:
theorem image_inv_eq_inv
  statement: (·⁻¹) '' s = s⁻¹
  proof: congr_fun (image_eq_preimage_of_inverse inv_involutive.leftInverse inv_involutive.rightInverse) _

@[to_additive (attr := simp)]

中文:
定理 image_inv_eq_inv
  结论: (·⁻¹) '' s = s⁻¹
  证明: congr_fun (image_eq_preimage_of_inverse inv_involutive.leftInverse inv_involutive.rightInverse) _

@[to_additive (attr := simp)]

Depends on / 依赖: congr_fun, image_eq_preimage_of_inverse, inv_involutive, inv_involutive.leftInverse, inv_involutive.rightInverse, leftInverse, rightInverse
-/
theorem image_inv_eq_inv : (·⁻¹) '' s = s⁻¹ :=
  congr_fun (image_eq_preimage_of_inverse inv_involutive.leftInverse inv_involutive.rightInverse) _

@[to_additive (attr := simp)]
/--
theorem `inv_eq_empty` / 定理 `inv_eq_empty`

English:
theorem inv_eq_empty
  statement: s⁻¹ = ∅ ↔ s = ∅
  proof: by
  rw [← image_inv_eq_inv]; rw [image_eq_empty]

@[to_additive (attr := simp)]

中文:
定理 inv_eq_empty
  结论: s⁻¹ = ∅ ↔ s = ∅
  证明: by
  rw [← image_inv_eq_inv]; rw [image_eq_empty]

@[to_additive (attr := simp)]

Depends on / 依赖: image_eq_empty, image_inv_eq_inv
-/
theorem inv_eq_empty : s⁻¹ = ∅ ↔ s = ∅ := by
  rw [← image_inv_eq_inv]; rw [image_eq_empty]

@[to_additive (attr := simp)]
/--
Instance `involutiveInv` / 实例 `involutiveInv`

English:
instance involutiveInv
  signature: : InvolutiveInv (Set α) where
  body: by simp only [← inv_preimage, preimage_preimage, inv_inv, preimage_id']

@[to_additive (attr := simp)]

中文:
实例 involutiveInv
  签名: : InvolutiveInv (集合 α) where
  定义体: by simp only [← inv_preimage, preimage_preimage, inv_inv, preimage_id']

@[to_additive (attr := simp)]

Depends on / 依赖: inv_inv, inv_preimage, preimage_id, preimage_preimage
-/
instance involutiveInv : InvolutiveInv (Set α) where
  inv_inv s := by simp only [← inv_preimage, preimage_preimage, inv_inv, preimage_id']

@[to_additive (attr := simp)]
/--
theorem `inv_subset_inv` / 定理 `inv_subset_inv`

English:
theorem inv_subset_inv
  statement: s⁻¹ subseteq t⁻¹ ↔ s subseteq t
  proof: (Equiv.inv α).surjective.preimage_subset_preimage_iff

@[to_additive]

中文:
定理 inv_subset_inv
  结论: s⁻¹ subseteq t⁻¹ ↔ s subseteq t
  证明: (Equiv.inv α).surjective.preimage_subset_preimage_iff

@[to_additive]

Depends on / 依赖: Equiv.inv, preimage_subset_preimage_iff, surjective, surjective.preimage_subset_preimage_iff
-/
theorem inv_subset_inv : s⁻¹ subseteq t⁻¹ ↔ s subseteq t :=
  (Equiv.inv α).surjective.preimage_subset_preimage_iff

@[to_additive]
/--
theorem `inv_subset` / 定理 `inv_subset`

English:
theorem inv_subset
  statement: s⁻¹ subseteq t ↔ s subseteq t⁻¹
  proof: by rw [← inv_subset_inv, inv_inv]

@[to_additive]

中文:
定理 inv_subset
  结论: s⁻¹ subseteq t ↔ s subseteq t⁻¹
  证明: by rw [← inv_subset_inv, inv_inv]

@[to_additive]

Depends on / 依赖: inv_inv, inv_subset_inv
-/
theorem inv_subset : s⁻¹ subseteq t ↔ s subseteq t⁻¹ := by rw [← inv_subset_inv, inv_inv]

@[to_additive]
/--
theorem `inv_eq_self_iff_inv_subset` / 定理 `inv_eq_self_iff_inv_subset`

English:
theorem inv_eq_self_iff_inv_subset
  statement: s⁻¹ = s ↔ s⁻¹ subseteq s
  proof: ⟨le_of_eq, fun h => antisymm h inv_subset.mp h⟩

@[to_additive (attr := simp)]

中文:
定理 inv_eq_self_iff_inv_subset
  结论: s⁻¹ = s ↔ s⁻¹ subseteq s
  证明: ⟨le_of_eq, fun h => antisymm h inv_subset.mp h⟩

@[to_additive (attr := simp)]

Depends on / 依赖: antisymm, inv_subset, inv_subset.mp, le_of_eq
-/
theorem inv_eq_self_iff_inv_subset : s⁻¹ = s ↔ s⁻¹ subseteq s :=
⟨le_of_eq, fun h => antisymm h inv_subset.mp h⟩

@[to_additive (attr := simp)]
/--
theorem `inv_singleton` / 定理 `inv_singleton`

English:
theorem inv_singleton
  given: (a : α)
  statement: ({a} : Set α)⁻¹ = {a⁻¹}
  proof: by
  rw [← image_inv_eq_inv]; rw [image_singleton]

@[to_additive (attr := simp)]

中文:
定理 inv_singleton
  条件: (a : α)
  结论: ({a} : 集合 α)⁻¹ = {a⁻¹}
  证明: by
  rw [← image_inv_eq_inv]; rw [image_singleton]

@[to_additive (attr := simp)]

Depends on / 依赖: image_inv_eq_inv, image_singleton
-/
theorem inv_singleton (a : α) : ({a} : Set α)⁻¹ = {a⁻¹} := by
  rw [← image_inv_eq_inv]; rw [image_singleton]

@[to_additive (attr := simp)]
/--
theorem `inv_insert` / 定理 `inv_insert`

English:
theorem inv_insert
  given: (a : α) (s : Set α)
  statement: (insert a s)⁻¹ = insert a⁻¹ s⁻¹
  proof: by
  rw [insert_eq]; rw [union_inv]; rw [inv_singleton]; rw [insert_eq]

@[to_additive]

中文:
定理 inv_insert
  条件: (a : α) (s : 集合 α)
  结论: (insert a s)⁻¹ = insert a⁻¹ s⁻¹
  证明: by
  rw [insert_eq]; rw [union_inv]; rw [inv_singleton]; rw [insert_eq]

@[to_additive]

Depends on / 依赖: insert_eq, inv_singleton, union_inv
-/
theorem inv_insert (a : α) (s : Set α) : (insert a s)⁻¹ = insert a⁻¹ s⁻¹ := by
  rw [insert_eq]; rw [union_inv]; rw [inv_singleton]; rw [insert_eq]

@[to_additive]
/--
theorem `inv_range` / 定理 `inv_range`

English:
theorem inv_range
  given: {ι : Sort*} {f : ι -> α}
  statement: (range f)⁻¹ = range fun i => (f i)⁻¹
  proof: by
  rw [← image_inv_eq_inv]
  exact (range_comp ..).symm

@[to_additive]

中文:
定理 inv_range
  条件: {ι : 类型层*} {f : ι -> α}
  结论: (range f)⁻¹ = range fun i => (f i)⁻¹
  证明: by
  rw [← image_inv_eq_inv]
  exact (range_comp ..).symm

@[to_additive]

Depends on / 依赖: image_inv_eq_inv, range_comp
-/
theorem inv_range {ι : Sort*} {f : ι -> α} : (range f)⁻¹ = range fun i => (f i)⁻¹ := by
  rw [← image_inv_eq_inv]
  exact (range_comp ..).symm

@[to_additive]
/--
lemma `inv_range'` / 引理 `inv_range'`

English:
lemma inv_range'
  given: {ι : Type*} {f : ι -> α}
  statement: (range f)⁻¹ = range f⁻¹
  proof: inv_range

@[to_additive]

中文:
引理 inv_range'
  条件: {ι : 类型} {f : ι -> α}
  结论: (range f)⁻¹ = range f⁻¹
  证明: inv_range

@[to_additive]

Depends on / 依赖: inv_range
-/
lemma inv_range' {ι : Type*} {f : ι -> α} : (range f)⁻¹ = range f⁻¹ := inv_range

@[to_additive]
/--
theorem `image_inv_of_apply_inv_eq` / 定理 `image_inv_of_apply_inv_eq`

English:
theorem image_inv_of_apply_inv_eq
  given: {f g : α -> β} (H : forall x in s, f x⁻¹ = g x)
  proof: by
  rw [← Set.image_inv_eq_inv]; rw [Set.image_image]; exact Set.image_congr H

@[to_additive]

中文:
定理 image_inv_of_apply_inv_eq
  条件: {f g : α -> β} (H : 对任意 x in s, f x⁻¹ = g x)
  证明: by
  rw [← Set.image_inv_eq_inv]; rw [Set.image_image]; exact Set.image_congr H

@[to_additive]

Depends on / 依赖: Set.image_congr, Set.image_image, Set.image_inv_eq_inv, image_congr, image_image, image_inv_eq_inv
-/
theorem image_inv_of_apply_inv_eq {f g : α -> β} (H : forall x in s, f x⁻¹ = g x) :
    f '' (s⁻¹) = g '' s := by
  rw [← Set.image_inv_eq_inv]; rw [Set.image_image]; exact Set.image_congr H

@[to_additive]
/--
theorem `image_inv_of_apply_inv_eq_inv` / 定理 `image_inv_of_apply_inv_eq_inv`

English:
theorem image_inv_of_apply_inv_eq_inv
  statement: [InvolutiveInv β] {f g : α -> β}
  proof: by
  conv_rhs => rw [← image_inv_eq_inv, image_image, ← image_inv_of_apply_inv_eq H]

@[to_additive (attr := simp)]

中文:
定理 image_inv_of_apply_inv_eq_inv
  结论: [InvolutiveInv β] {f g : α -> β}
  证明: by
  conv_rhs => rw [← image_inv_eq_inv, image_image, ← image_inv_of_apply_inv_eq H]

@[to_additive (attr := simp)]

Depends on / 依赖: conv_rhs, image_image, image_inv_eq_inv, image_inv_of_apply_inv_eq
-/
theorem image_inv_of_apply_inv_eq_inv [InvolutiveInv β] {f g : α -> β}
    (H : forall x in s, f x⁻¹ = (g x)⁻¹) : f '' s⁻¹ = (g '' s)⁻¹ := by
  conv_rhs => rw [← image_inv_eq_inv, image_image, ← image_inv_of_apply_inv_eq H]

@[to_additive (attr := simp)]
/--
theorem `forall_inv_mem` / 定理 `forall_inv_mem`

English:
theorem forall_inv_mem
  given: {p : α -> Prop}
  statement: (forall x, x⁻¹ in s -> p x) ↔ forall x in s, p x⁻¹
  proof: by
  rw [← (Equiv.inv _).forall_congr_right]
  simp

@[to_additive (attr := simp)]

中文:
定理 对任意_inv_mem
  条件: {p : α -> 命题}
  结论: (对任意 x, x⁻¹ in s -> p x) ↔ 对任意 x in s, p x⁻¹
  证明: by
  rw [← (Equiv.inv _).forall_congr_right]
  simp

@[to_additive (attr := simp)]

Depends on / 依赖: Equiv.inv, forall_congr_right
-/
theorem forall_inv_mem {p : α -> Prop} : (forall x, x⁻¹ in s -> p x) ↔ forall x in s, p x⁻¹ := by
  rw [← (Equiv.inv _).forall_congr_right]
  simp

@[to_additive (attr := simp)]
/--
theorem `exists_inv_mem` / 定理 `exists_inv_mem`

English:
theorem exists_inv_mem
  given: {p : α -> Prop}
  statement: (exists x, x⁻¹ in s ∧ p x) ↔ exists x in s, p x⁻¹
  proof: by
  rw [← (Equiv.inv _).exists_congr_right]
  simp

中文:
定理 存在_inv_mem
  条件: {p : α -> 命题}
  结论: (存在 x, x⁻¹ in s ∧ p x) ↔ 存在 x in s, p x⁻¹
  证明: by
  rw [← (Equiv.inv _).exists_congr_right]
  simp

Depends on / 依赖: Equiv.inv, exists_congr_right
-/
theorem exists_inv_mem {p : α -> Prop} : (exists x, x⁻¹ in s ∧ p x) ↔ exists x in s, p x⁻¹ := by
  rw [← (Equiv.inv _).exists_congr_right]
  simp

open MulOpposite

@[to_additive]
/--
theorem `image_op_inv` / 定理 `image_op_inv`

English:
theorem image_op_inv
  statement: op '' s⁻¹ = (op '' s)⁻¹
  proof: by
  simp_rw [← image_inv_eq_inv, Function.Semiconj.set_image op_inv s]

中文:
定理 image_op_inv
  结论: op '' s⁻¹ = (op '' s)⁻¹
  证明: by
  simp_rw [← image_inv_eq_inv, Function.Semiconj.set_image op_inv s]

Depends on / 依赖: Function, Function.Semiconj.set_image, Semiconj, image_inv_eq_inv, op_inv, set_image, simp_rw
-/
theorem image_op_inv : op '' s⁻¹ = (op '' s)⁻¹ := by
  simp_rw [← image_inv_eq_inv, Function.Semiconj.set_image op_inv s]

end InvolutiveInv

end Inv

open scoped Pointwise

/-! ### Set addition/multiplication -/


section Mul

variable {ι : Sort*} {κ : ι -> Sort*} [Mul α] {s s₁ s₂ t t₁ t₂ u : Set α} {a b : α}

/-- The pointwise multiplication of sets `s * t` and `t` is defined as `{x * y | x ∈ s, y ∈ t}` in
scope `Pointwise`. -/
@[to_additive (attr := instance_reducible)
      /-- The pointwise addition of sets `s + t` is defined as `{x + y | x ∈ s, y ∈ t}` in locale
      `Pointwise`. -/]
/--
Definition of `mul` / `mul` 的定义

English:
definition mul
  signature: : Mul (Set α)
  body: ⟨image2 (· * ·)⟩

scoped[Pointwise] attribute [instance] Set.mul Set.add

@[to_additive (attr := simp)]

中文:
定义 mul
  签名: : 乘法 (集合 α)
  定义体: ⟨image2 (· * ·)⟩

scoped[Pointwise] attribute [instance] Set.mul Set.add

@[to_additive (attr := simp)]
-/
protected def mul : Mul (Set α) :=
  ⟨image2 (· * ·)⟩

scoped[Pointwise] attribute [instance] Set.mul Set.add

@[to_additive (attr := simp)]
/--
theorem `image2_mul` / 定理 `image2_mul`

English:
theorem image2_mul
  statement: image2 (· * ·) s t = s * t
  proof: rfl

@[to_additive (attr := push)]

中文:
定理 image2_mul
  结论: image2 (· * ·) s t = s * t
  证明: rfl

@[to_additive (attr := push)]
-/
theorem image2_mul : image2 (· * ·) s t = s * t :=
  rfl

@[to_additive (attr := push)]
/--
theorem `mem_mul` / 定理 `mem_mul`

English:
theorem mem_mul
  statement: a in s * t ↔ exists x in s, exists y in t, x * y = a
  proof: Iff.rfl

@[to_additive]

中文:
定理 mem_mul
  结论: a in s * t ↔ 存在 x in s, 存在 y in t, x * y = a
  证明: Iff.rfl

@[to_additive]

Depends on / 依赖: Iff.rfl
-/
theorem mem_mul : a in s * t ↔ exists x in s, exists y in t, x * y = a :=
  Iff.rfl

@[to_additive]
/--
theorem `mul_mem_mul` / 定理 `mul_mem_mul`

English:
theorem mul_mem_mul
  statement: a in s -> b in t -> a * b in s * t
  proof: mem_image2_of_mem

@[to_additive add_image_prod]

中文:
定理 mul_mem_mul
  结论: a in s -> b in t -> a * b in s * t
  证明: mem_image2_of_mem

@[to_additive add_image_prod]

Depends on / 依赖: mem_image2_of_mem
-/
theorem mul_mem_mul : a in s -> b in t -> a * b in s * t :=
  mem_image2_of_mem

@[to_additive add_image_prod]
/--
theorem `image_mul_prod` / 定理 `image_mul_prod`

English:
theorem image_mul_prod
  statement: (fun x : α × α => x.fst * x.snd) '' s ×ˢ t = s * t
  proof: image_prod _

@[to_additive (attr := simp)]

中文:
定理 image_mul_prod
  结论: (fun x : α × α => x.fst * x.snd) '' s ×ˢ t = s * t
  证明: image_prod _

@[to_additive (attr := simp)]

Depends on / 依赖: image_prod
-/
theorem image_mul_prod : (fun x : α × α => x.fst * x.snd) '' s ×ˢ t = s * t :=
  image_prod _

@[to_additive (attr := simp)]
/--
theorem `empty_mul` / 定理 `empty_mul`

English:
theorem empty_mul
  statement: ∅ * s = ∅
  proof: image2_empty_left

@[to_additive (attr := simp)]

中文:
定理 empty_mul
  结论: ∅ * s = ∅
  证明: image2_empty_left

@[to_additive (attr := simp)]

Depends on / 依赖: image2_empty_left
-/
theorem empty_mul : ∅ * s = ∅ :=
  image2_empty_left

@[to_additive (attr := simp)]
/--
theorem `mul_empty` / 定理 `mul_empty`

English:
theorem mul_empty
  statement: s * ∅ = ∅
  proof: image2_empty_right

@[to_additive (attr := simp)]

中文:
定理 mul_empty
  结论: s * ∅ = ∅
  证明: image2_empty_right

@[to_additive (attr := simp)]

Depends on / 依赖: image2_empty_right
-/
theorem mul_empty : s * ∅ = ∅ :=
  image2_empty_right

@[to_additive (attr := simp)]
/--
theorem `mul_eq_empty` / 定理 `mul_eq_empty`

English:
theorem mul_eq_empty
  statement: s * t = ∅ ↔ s = ∅ ∨ t = ∅
  proof: image2_eq_empty_iff

@[to_additive (attr := simp)]

中文:
定理 mul_eq_empty
  结论: s * t = ∅ ↔ s = ∅ ∨ t = ∅
  证明: image2_eq_empty_iff

@[to_additive (attr := simp)]

Depends on / 依赖: image2_eq_empty_iff
-/
theorem mul_eq_empty : s * t = ∅ ↔ s = ∅ ∨ t = ∅ :=
  image2_eq_empty_iff

@[to_additive (attr := simp)]
/--
theorem `mul_nonempty` / 定理 `mul_nonempty`

English:
theorem mul_nonempty
  statement: (s * t).Nonempty ↔ s.Nonempty ∧ t.Nonempty
  proof: image2_nonempty_iff

@[to_additive]

中文:
定理 mul_nonempty
  结论: (s * t).非空 ↔ s.非空 ∧ t.非空
  证明: image2_nonempty_iff

@[to_additive]

Depends on / 依赖: image2_nonempty_iff
-/
theorem mul_nonempty : (s * t).Nonempty ↔ s.Nonempty ∧ t.Nonempty :=
  image2_nonempty_iff

@[to_additive]
/--
theorem `Nonempty.mul` / 定理 `Nonempty.mul`

English:
theorem Nonempty.mul
  statement: s.Nonempty -> t.Nonempty -> (s * t).Nonempty
  proof: Nonempty.image2

@[to_additive]

中文:
定理 非空.mul
  结论: s.非空 -> t.非空 -> (s * t).非空
  证明: Nonempty.image2

@[to_additive]
-/
theorem Nonempty.mul : s.Nonempty -> t.Nonempty -> (s * t).Nonempty :=
  Nonempty.image2

@[to_additive]
/--
theorem `Nonempty.of_mul_left` / 定理 `Nonempty.of_mul_left`

English:
theorem Nonempty.of_mul_left
  statement: (s * t).Nonempty -> s.Nonempty
  proof: Nonempty.of_image2_left

@[to_additive]

中文:
定理 非空.of_mul_left
  结论: (s * t).非空 -> s.非空
  证明: Nonempty.of_image2_left

@[to_additive]
-/
theorem Nonempty.of_mul_left : (s * t).Nonempty -> s.Nonempty :=
  Nonempty.of_image2_left

@[to_additive]
/--
theorem `Nonempty.of_mul_right` / 定理 `Nonempty.of_mul_right`

English:
theorem Nonempty.of_mul_right
  statement: (s * t).Nonempty -> t.Nonempty
  proof: Nonempty.of_image2_right

@[to_additive (attr := simp)]

中文:
定理 非空.of_mul_right
  结论: (s * t).非空 -> t.非空
  证明: Nonempty.of_image2_right

@[to_additive (attr := simp)]
-/
theorem Nonempty.of_mul_right : (s * t).Nonempty -> t.Nonempty :=
  Nonempty.of_image2_right

@[to_additive (attr := simp)]
/--
theorem `mul_singleton` / 定理 `mul_singleton`

English:
theorem mul_singleton
  statement: s * {b} = (· * b) '' s
  proof: image2_singleton_right

@[to_additive (attr := simp)]

中文:
定理 mul_singleton
  结论: s * {b} = (· * b) '' s
  证明: image2_singleton_right

@[to_additive (attr := simp)]

Depends on / 依赖: image2_singleton_right
-/
theorem mul_singleton : s * {b} = (· * b) '' s :=
  image2_singleton_right

@[to_additive (attr := simp)]
/--
theorem `singleton_mul` / 定理 `singleton_mul`

English:
theorem singleton_mul
  statement: {a} * t = (a * ·) '' t
  proof: image2_singleton_left

@[to_additive]

中文:
定理 singleton_mul
  结论: {a} * t = (a * ·) '' t
  证明: image2_singleton_left

@[to_additive]

Depends on / 依赖: image2_singleton_left
-/
theorem singleton_mul : {a} * t = (a * ·) '' t :=
  image2_singleton_left

@[to_additive]
/--
theorem `singleton_mul_singleton` / 定理 `singleton_mul_singleton`

English:
theorem singleton_mul_singleton
  statement: ({a} : Set α) * {b} = {a * b}
  proof: image2_singleton

@[to_additive]

中文:
定理 singleton_mul_singleton
  结论: ({a} : 集合 α) * {b} = {a * b}
  证明: image2_singleton

@[to_additive]

Depends on / 依赖: IsMulCommutative, Subgroup, image2_singleton, normal_of_isMulCommutative
-/
theorem singleton_mul_singleton : ({a} : Set α) * {b} = {a * b} :=
  image2_singleton

@[to_additive]
/--
theorem `mul_subset_mul` / 定理 `mul_subset_mul`

English:
theorem mul_subset_mul
  statement: s₁ subseteq t₁ -> s₂ subseteq t₂ -> s₁ * s₂ subseteq t₁ * t₂
  proof: image2_subset

@[to_additive]

中文:
定理 mul_subset_mul
  结论: s₁ subseteq t₁ -> s₂ subseteq t₂ -> s₁ * s₂ subseteq t₁ * t₂
  证明: image2_subset

@[to_additive]

Depends on / 依赖: image2_subset
-/
theorem mul_subset_mul : s₁ subseteq t₁ -> s₂ subseteq t₂ -> s₁ * s₂ subseteq t₁ * t₂ :=
  image2_subset

@[to_additive]
/--
theorem `mul_subset_mul_left` / 定理 `mul_subset_mul_left`

English:
theorem mul_subset_mul_left
  statement: t₁ subseteq t₂ -> s * t₁ subseteq s * t₂
  proof: image2_subset_left

@[to_additive]

中文:
定理 mul_subset_mul_left
  结论: t₁ subseteq t₂ -> s * t₁ subseteq s * t₂
  证明: image2_subset_left

@[to_additive]

Depends on / 依赖: image2_subset_left
-/
theorem mul_subset_mul_left : t₁ subseteq t₂ -> s * t₁ subseteq s * t₂ :=
  image2_subset_left

@[to_additive]
/--
theorem `mul_subset_mul_right` / 定理 `mul_subset_mul_right`

English:
theorem mul_subset_mul_right
  statement: s₁ subseteq s₂ -> s₁ * t subseteq s₂ * t
  proof: image2_subset_right

中文:
定理 mul_subset_mul_right
  结论: s₁ subseteq s₂ -> s₁ * t subseteq s₂ * t
  证明: image2_subset_right

Depends on / 依赖: image2_subset_right
-/
theorem mul_subset_mul_right : s₁ subseteq s₂ -> s₁ * t subseteq s₂ * t :=
  image2_subset_right

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MulLeftMono (Set α)
  body: mul_subset_mul_left

中文:
实例 :
  签名: MulLeftMono (集合 α)
  定义体: mul_subset_mul_left
-/
@[to_additive] instance : MulLeftMono (Set α) where elim _s _t₁ _t₂ := mul_subset_mul_left
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MulRightMono (Set α)
  body: mul_subset_mul_right

@[to_additive]

中文:
实例 :
  签名: MulRightMono (集合 α)
  定义体: mul_subset_mul_right

@[to_additive]
-/
@[to_additive] instance : MulRightMono (Set α) where elim _t _s₁ _s₂ := mul_subset_mul_right

@[to_additive]
/--
theorem `mul_subset_iff` / 定理 `mul_subset_iff`

English:
theorem mul_subset_iff
  statement: s * t subseteq u ↔ forall x in s, forall y in t, x * y in u
  proof: image2_subset_iff

@[to_additive]

中文:
定理 mul_subset_iff
  结论: s * t subseteq u ↔ 对任意 x in s, 对任意 y in t, x * y in u
  证明: image2_subset_iff

@[to_additive]

Depends on / 依赖: image2_subset_iff
-/
theorem mul_subset_iff : s * t subseteq u ↔ forall x in s, forall y in t, x * y in u :=
  image2_subset_iff

@[to_additive]
/--
theorem `union_mul` / 定理 `union_mul`

English:
theorem union_mul
  statement: (s₁ union s₂) * t = s₁ * t union s₂ * t
  proof: image2_union_left

@[to_additive]

中文:
定理 union_mul
  结论: (s₁ union s₂) * t = s₁ * t union s₂ * t
  证明: image2_union_left

@[to_additive]

Depends on / 依赖: image2_union_left
-/
theorem union_mul : (s₁ union s₂) * t = s₁ * t union s₂ * t :=
  image2_union_left

@[to_additive]
/--
theorem `mul_union` / 定理 `mul_union`

English:
theorem mul_union
  statement: s * (t₁ union t₂) = s * t₁ union s * t₂
  proof: image2_union_right

@[to_additive]

中文:
定理 mul_union
  结论: s * (t₁ union t₂) = s * t₁ union s * t₂
  证明: image2_union_right

@[to_additive]

Depends on / 依赖: image2_union_right
-/
theorem mul_union : s * (t₁ union t₂) = s * t₁ union s * t₂ :=
  image2_union_right

@[to_additive]
/--
theorem `inter_mul_subset` / 定理 `inter_mul_subset`

English:
theorem inter_mul_subset
  statement: s₁ inter s₂ * t subseteq s₁ * t inter (s₂ * t)
  proof: image2_inter_subset_left

@[to_additive]

中文:
定理 inter_mul_subset
  结论: s₁ inter s₂ * t subseteq s₁ * t inter (s₂ * t)
  证明: image2_inter_subset_left

@[to_additive]

Depends on / 依赖: image2_inter_subset_left
-/
theorem inter_mul_subset : s₁ inter s₂ * t subseteq s₁ * t inter (s₂ * t) :=
  image2_inter_subset_left

@[to_additive]
/--
theorem `mul_inter_subset` / 定理 `mul_inter_subset`

English:
theorem mul_inter_subset
  statement: s * (t₁ inter t₂) subseteq s * t₁ inter (s * t₂)
  proof: image2_inter_subset_right

@[to_additive]

中文:
定理 mul_inter_subset
  结论: s * (t₁ inter t₂) subseteq s * t₁ inter (s * t₂)
  证明: image2_inter_subset_right

@[to_additive]

Depends on / 依赖: image2_inter_subset_right
-/
theorem mul_inter_subset : s * (t₁ inter t₂) subseteq s * t₁ inter (s * t₂) :=
  image2_inter_subset_right

@[to_additive]
/--
theorem `inter_mul_union_subset_union` / 定理 `inter_mul_union_subset_union`

English:
theorem inter_mul_union_subset_union
  statement: s₁ inter s₂ * (t₁ union t₂) subseteq s₁ * t₁ union s₂ * t₂
  proof: image2_inter_union_subset_union

@[to_additive]

中文:
定理 inter_mul_union_subset_union
  结论: s₁ inter s₂ * (t₁ union t₂) subseteq s₁ * t₁ union s₂ * t₂
  证明: image2_inter_union_subset_union

@[to_additive]

Depends on / 依赖: image2_inter_union_subset_union
-/
theorem inter_mul_union_subset_union : s₁ inter s₂ * (t₁ union t₂) subseteq s₁ * t₁ union s₂ * t₂ :=
  image2_inter_union_subset_union

@[to_additive]
/--
theorem `union_mul_inter_subset_union` / 定理 `union_mul_inter_subset_union`

English:
theorem union_mul_inter_subset_union
  statement: (s₁ union s₂) * (t₁ inter t₂) subseteq s₁ * t₁ union s₂ * t₂
  proof: image2_union_inter_subset_union

中文:
定理 union_mul_inter_subset_union
  结论: (s₁ union s₂) * (t₁ inter t₂) subseteq s₁ * t₁ union s₂ * t₂
  证明: image2_union_inter_subset_union

Depends on / 依赖: image2_union_inter_subset_union
-/
theorem union_mul_inter_subset_union : (s₁ union s₂) * (t₁ inter t₂) subseteq s₁ * t₁ union s₂ * t₂ :=
  image2_union_inter_subset_union

/-- The singleton operation as a `MulHom`. -/
@[to_additive /-- The singleton operation as an `AddHom`. -/]
/--
Definition of `singletonMulHom` / `singletonMulHom` 的定义

English:
definition singletonMulHom
  signature: : α ->ₙ* Set α where
  body: singleton
  map_mul' _ _ := singleton_mul_singleton.symm

@[to_additive (attr := simp)]

中文:
定义 singletonMulHom
  签名: : α ->ₙ* 集合 α where
  定义体: singleton
  map_mul' _ _ := singleton_mul_singleton.symm

@[to_additive (attr := simp)]

Depends on / 依赖: singleton
-/
def singletonMulHom : α ->ₙ* Set α where
  toFun := singleton
  map_mul' _ _ := singleton_mul_singleton.symm

@[to_additive (attr := simp)]
/--
theorem `coe_singletonMulHom` / 定理 `coe_singletonMulHom`

English:
theorem coe_singletonMulHom
  statement: (singletonMulHom : α -> Set α) = singleton
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 coe_singletonMulHom
  结论: (singletonMulHom : α -> 集合 α) = singleton
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem coe_singletonMulHom : (singletonMulHom : α -> Set α) = singleton :=
  rfl

@[to_additive (attr := simp)]
/--
theorem `singletonMulHom_apply` / 定理 `singletonMulHom_apply`

English:
theorem singletonMulHom_apply
  given: (a : α)
  statement: singletonMulHom a = {a}
  proof: rfl

中文:
定理 singletonMulHom_apply
  条件: (a : α)
  结论: singletonMulHom a = {a}
  证明: rfl
-/
theorem singletonMulHom_apply (a : α) : singletonMulHom a = {a} :=
  rfl

open MulOpposite

@[to_additive (attr := simp)]
/--
theorem `image_op_mul` / 定理 `image_op_mul`

English:
theorem image_op_mul
  statement: op '' (s * t) = op '' t * op '' s
  proof: image_image2_antidistrib op_mul

@[to_additive (attr := simp) prod_add_prod_comm]

中文:
定理 image_op_mul
  结论: op '' (s * t) = op '' t * op '' s
  证明: image_image2_antidistrib op_mul

@[to_additive (attr := simp) prod_add_prod_comm]

Depends on / 依赖: image_image2_antidistrib, op_mul
-/
theorem image_op_mul : op '' (s * t) = op '' t * op '' s :=
  image_image2_antidistrib op_mul

@[to_additive (attr := simp) prod_add_prod_comm]
/--
lemma `prod_mul_prod_comm` / 引理 `prod_mul_prod_comm`

English:
lemma prod_mul_prod_comm
  given: [Mul β] (s₁ s₂ : Set α) (t₁ t₂ : Set β)
  proof: by ext; simp [mem_mul]; aesop

中文:
引理 prod_mul_prod_comm
  条件: [乘法 β] (s₁ s₂ : 集合 α) (t₁ t₂ : 集合 β)
  证明: by ext; simp [mem_mul]; aesop

Depends on / 依赖: mem_mul
-/
lemma prod_mul_prod_comm [Mul β] (s₁ s₂ : Set α) (t₁ t₂ : Set β) :
    (s₁ ×ˢ t₁) * (s₂ ×ˢ t₂) = (s₁ * s₂) ×ˢ (t₁ * t₂) := by ext; simp [mem_mul]; aesop

end Mul

/-! ### Set subtraction/division -/


section Div

variable {ι : Sort*} {κ : ι -> Sort*} [Div α] {s s₁ s₂ t t₁ t₂ u : Set α} {a b : α}

/-- The pointwise division of sets `s / t` is defined as `{x / y | x ∈ s, y ∈ t}` in locale
`Pointwise`. -/
@[to_additive (attr := instance_reducible)
      /-- The pointwise subtraction of sets `s - t` is defined as `{x - y | x ∈ s, y ∈ t}` in locale
      `Pointwise`. -/]
/--
Definition of `div` / `div` 的定义

English:
definition div
  signature: : Div (Set α)
  body: ⟨image2 (· / ·)⟩

scoped[Pointwise] attribute [instance] Set.div Set.sub

@[to_additive (attr := simp)]

中文:
定义 div
  签名: : 除法 (集合 α)
  定义体: ⟨image2 (· / ·)⟩

scoped[Pointwise] attribute [instance] Set.div Set.sub

@[to_additive (attr := simp)]
-/
protected def div : Div (Set α) :=
  ⟨image2 (· / ·)⟩

scoped[Pointwise] attribute [instance] Set.div Set.sub

@[to_additive (attr := simp)]
/--
theorem `image2_div` / 定理 `image2_div`

English:
theorem image2_div
  statement: image2 (· / ·) s t = s / t
  proof: rfl

@[to_additive (attr := push)]

中文:
定理 image2_div
  结论: image2 (· / ·) s t = s / t
  证明: rfl

@[to_additive (attr := push)]
-/
theorem image2_div : image2 (· / ·) s t = s / t :=
  rfl

@[to_additive (attr := push)]
/--
theorem `mem_div` / 定理 `mem_div`

English:
theorem mem_div
  statement: a in s / t ↔ exists x in s, exists y in t, x / y = a
  proof: Iff.rfl

@[to_additive]

中文:
定理 mem_div
  结论: a in s / t ↔ 存在 x in s, 存在 y in t, x / y = a
  证明: Iff.rfl

@[to_additive]

Depends on / 依赖: Iff.rfl
-/
theorem mem_div : a in s / t ↔ exists x in s, exists y in t, x / y = a :=
  Iff.rfl

@[to_additive]
/--
theorem `div_mem_div` / 定理 `div_mem_div`

English:
theorem div_mem_div
  statement: a in s -> b in t -> a / b in s / t
  proof: mem_image2_of_mem

@[to_additive sub_image_prod]

中文:
定理 div_mem_div
  结论: a in s -> b in t -> a / b in s / t
  证明: mem_image2_of_mem

@[to_additive sub_image_prod]

Depends on / 依赖: mem_image2_of_mem
-/
theorem div_mem_div : a in s -> b in t -> a / b in s / t :=
  mem_image2_of_mem

@[to_additive sub_image_prod]
/--
theorem `image_div_prod` / 定理 `image_div_prod`

English:
theorem image_div_prod
  statement: (fun x : α × α => x.fst / x.snd) '' s ×ˢ t = s / t
  proof: image_prod _

@[to_additive (attr := simp)]

中文:
定理 image_div_prod
  结论: (fun x : α × α => x.fst / x.snd) '' s ×ˢ t = s / t
  证明: image_prod _

@[to_additive (attr := simp)]

Depends on / 依赖: image_prod
-/
theorem image_div_prod : (fun x : α × α => x.fst / x.snd) '' s ×ˢ t = s / t :=
  image_prod _

@[to_additive (attr := simp)]
/--
theorem `empty_div` / 定理 `empty_div`

English:
theorem empty_div
  statement: ∅ / s = ∅
  proof: image2_empty_left

@[to_additive (attr := simp)]

中文:
定理 empty_div
  结论: ∅ / s = ∅
  证明: image2_empty_left

@[to_additive (attr := simp)]

Depends on / 依赖: image2_empty_left
-/
theorem empty_div : ∅ / s = ∅ :=
  image2_empty_left

@[to_additive (attr := simp)]
/--
theorem `div_empty` / 定理 `div_empty`

English:
theorem div_empty
  statement: s / ∅ = ∅
  proof: image2_empty_right

@[to_additive (attr := simp)]

中文:
定理 div_empty
  结论: s / ∅ = ∅
  证明: image2_empty_right

@[to_additive (attr := simp)]

Depends on / 依赖: image2_empty_right
-/
theorem div_empty : s / ∅ = ∅ :=
  image2_empty_right

@[to_additive (attr := simp)]
/--
theorem `div_eq_empty` / 定理 `div_eq_empty`

English:
theorem div_eq_empty
  statement: s / t = ∅ ↔ s = ∅ ∨ t = ∅
  proof: image2_eq_empty_iff

@[to_additive (attr := simp)]

中文:
定理 div_eq_empty
  结论: s / t = ∅ ↔ s = ∅ ∨ t = ∅
  证明: image2_eq_empty_iff

@[to_additive (attr := simp)]

Depends on / 依赖: image2_eq_empty_iff
-/
theorem div_eq_empty : s / t = ∅ ↔ s = ∅ ∨ t = ∅ :=
  image2_eq_empty_iff

@[to_additive (attr := simp)]
/--
theorem `div_nonempty` / 定理 `div_nonempty`

English:
theorem div_nonempty
  statement: (s / t).Nonempty ↔ s.Nonempty ∧ t.Nonempty
  proof: image2_nonempty_iff

@[to_additive]

中文:
定理 div_nonempty
  结论: (s / t).非空 ↔ s.非空 ∧ t.非空
  证明: image2_nonempty_iff

@[to_additive]

Depends on / 依赖: Fintype, image2_nonempty_iff
-/
theorem div_nonempty : (s / t).Nonempty ↔ s.Nonempty ∧ t.Nonempty :=
  image2_nonempty_iff

@[to_additive]
/--
theorem `Nonempty.div` / 定理 `Nonempty.div`

English:
theorem Nonempty.div
  statement: s.Nonempty -> t.Nonempty -> (s / t).Nonempty
  proof: Nonempty.image2

@[to_additive]

中文:
定理 非空.div
  结论: s.非空 -> t.非空 -> (s / t).非空
  证明: Nonempty.image2

@[to_additive]

Depends on / 依赖: Subtype, Subtype.finite, finite
-/
theorem Nonempty.div : s.Nonempty -> t.Nonempty -> (s / t).Nonempty :=
  Nonempty.image2

@[to_additive]
/--
theorem `Nonempty.of_div_left` / 定理 `Nonempty.of_div_left`

English:
theorem Nonempty.of_div_left
  statement: (s / t).Nonempty -> s.Nonempty
  proof: Nonempty.of_image2_left

@[to_additive]

中文:
定理 非空.of_div_left
  结论: (s / t).非空 -> s.非空
  证明: Nonempty.of_image2_left

@[to_additive]
-/
theorem Nonempty.of_div_left : (s / t).Nonempty -> s.Nonempty :=
  Nonempty.of_image2_left

@[to_additive]
/--
theorem `Nonempty.of_div_right` / 定理 `Nonempty.of_div_right`

English:
theorem Nonempty.of_div_right
  statement: (s / t).Nonempty -> t.Nonempty
  proof: Nonempty.of_image2_right

@[to_additive (attr := simp)]

中文:
定理 非空.of_div_right
  结论: (s / t).非空 -> t.非空
  证明: Nonempty.of_image2_right

@[to_additive (attr := simp)]
-/
theorem Nonempty.of_div_right : (s / t).Nonempty -> t.Nonempty :=
  Nonempty.of_image2_right

@[to_additive (attr := simp)]
/--
theorem `div_singleton` / 定理 `div_singleton`

English:
theorem div_singleton
  statement: s / {b} = (· / b) '' s
  proof: image2_singleton_right

@[to_additive (attr := simp)]

中文:
定理 div_singleton
  结论: s / {b} = (· / b) '' s
  证明: image2_singleton_right

@[to_additive (attr := simp)]

Depends on / 依赖: image2_singleton_right
-/
theorem div_singleton : s / {b} = (· / b) '' s :=
  image2_singleton_right

@[to_additive (attr := simp)]
/--
theorem `singleton_div` / 定理 `singleton_div`

English:
theorem singleton_div
  statement: {a} / t = (· / ·) a '' t
  proof: image2_singleton_left

@[to_additive]

中文:
定理 singleton_div
  结论: {a} / t = (· / ·) a '' t
  证明: image2_singleton_left

@[to_additive]

Depends on / 依赖: image2_singleton_left
-/
theorem singleton_div : {a} / t = (· / ·) a '' t :=
  image2_singleton_left

@[to_additive]
/--
theorem `singleton_div_singleton` / 定理 `singleton_div_singleton`

English:
theorem singleton_div_singleton
  statement: ({a} : Set α) / {b} = {a / b}
  proof: image2_singleton

@[to_additive (attr := mono, gcongr)]

中文:
定理 singleton_div_singleton
  结论: ({a} : 集合 α) / {b} = {a / b}
  证明: image2_singleton

@[to_additive (attr := mono, gcongr)]

Depends on / 依赖: image2_singleton
-/
theorem singleton_div_singleton : ({a} : Set α) / {b} = {a / b} :=
  image2_singleton

@[to_additive (attr := mono, gcongr)]
/--
theorem `div_subset_div` / 定理 `div_subset_div`

English:
theorem div_subset_div
  statement: s₁ subseteq t₁ -> s₂ subseteq t₂ -> s₁ / s₂ subseteq t₁ / t₂
  proof: image2_subset

@[to_additive]

中文:
定理 div_subset_div
  结论: s₁ subseteq t₁ -> s₂ subseteq t₂ -> s₁ / s₂ subseteq t₁ / t₂
  证明: image2_subset

@[to_additive]

Depends on / 依赖: image2_subset
-/
theorem div_subset_div : s₁ subseteq t₁ -> s₂ subseteq t₂ -> s₁ / s₂ subseteq t₁ / t₂ :=
  image2_subset

@[to_additive]
/--
theorem `div_subset_div_left` / 定理 `div_subset_div_left`

English:
theorem div_subset_div_left
  statement: t₁ subseteq t₂ -> s / t₁ subseteq s / t₂
  proof: image2_subset_left

@[to_additive]

中文:
定理 div_subset_div_left
  结论: t₁ subseteq t₂ -> s / t₁ subseteq s / t₂
  证明: image2_subset_left

@[to_additive]

Depends on / 依赖: image2_subset_left
-/
theorem div_subset_div_left : t₁ subseteq t₂ -> s / t₁ subseteq s / t₂ :=
  image2_subset_left

@[to_additive]
/--
theorem `div_subset_div_right` / 定理 `div_subset_div_right`

English:
theorem div_subset_div_right
  statement: s₁ subseteq s₂ -> s₁ / t subseteq s₂ / t
  proof: image2_subset_right

@[to_additive]

中文:
定理 div_subset_div_right
  结论: s₁ subseteq s₂ -> s₁ / t subseteq s₂ / t
  证明: image2_subset_right

@[to_additive]

Depends on / 依赖: image2_subset_right
-/
theorem div_subset_div_right : s₁ subseteq s₂ -> s₁ / t subseteq s₂ / t :=
  image2_subset_right

@[to_additive]
/--
theorem `div_subset_iff` / 定理 `div_subset_iff`

English:
theorem div_subset_iff
  statement: s / t subseteq u ↔ forall x in s, forall y in t, x / y in u
  proof: image2_subset_iff

@[to_additive]

中文:
定理 div_subset_iff
  结论: s / t subseteq u ↔ 对任意 x in s, 对任意 y in t, x / y in u
  证明: image2_subset_iff

@[to_additive]

Depends on / 依赖: image2_subset_iff
-/
theorem div_subset_iff : s / t subseteq u ↔ forall x in s, forall y in t, x / y in u :=
  image2_subset_iff

@[to_additive]
/--
theorem `union_div` / 定理 `union_div`

English:
theorem union_div
  statement: (s₁ union s₂) / t = s₁ / t union s₂ / t
  proof: image2_union_left

@[to_additive]

中文:
定理 union_div
  结论: (s₁ union s₂) / t = s₁ / t union s₂ / t
  证明: image2_union_left

@[to_additive]

Depends on / 依赖: image2_union_left
-/
theorem union_div : (s₁ union s₂) / t = s₁ / t union s₂ / t :=
  image2_union_left

@[to_additive]
/--
theorem `div_union` / 定理 `div_union`

English:
theorem div_union
  statement: s / (t₁ union t₂) = s / t₁ union s / t₂
  proof: image2_union_right

@[to_additive]

中文:
定理 div_union
  结论: s / (t₁ union t₂) = s / t₁ union s / t₂
  证明: image2_union_right

@[to_additive]

Depends on / 依赖: image2_union_right
-/
theorem div_union : s / (t₁ union t₂) = s / t₁ union s / t₂ :=
  image2_union_right

@[to_additive]
/--
theorem `inter_div_subset` / 定理 `inter_div_subset`

English:
theorem inter_div_subset
  statement: s₁ inter s₂ / t subseteq s₁ / t inter (s₂ / t)
  proof: image2_inter_subset_left

@[to_additive]

中文:
定理 inter_div_subset
  结论: s₁ inter s₂ / t subseteq s₁ / t inter (s₂ / t)
  证明: image2_inter_subset_left

@[to_additive]

Depends on / 依赖: image2_inter_subset_left
-/
theorem inter_div_subset : s₁ inter s₂ / t subseteq s₁ / t inter (s₂ / t) :=
  image2_inter_subset_left

@[to_additive]
/--
theorem `div_inter_subset` / 定理 `div_inter_subset`

English:
theorem div_inter_subset
  statement: s / (t₁ inter t₂) subseteq s / t₁ inter (s / t₂)
  proof: image2_inter_subset_right

@[to_additive]

中文:
定理 div_inter_subset
  结论: s / (t₁ inter t₂) subseteq s / t₁ inter (s / t₂)
  证明: image2_inter_subset_right

@[to_additive]

Depends on / 依赖: image2_inter_subset_right
-/
theorem div_inter_subset : s / (t₁ inter t₂) subseteq s / t₁ inter (s / t₂) :=
  image2_inter_subset_right

@[to_additive]
/--
theorem `inter_div_union_subset_union` / 定理 `inter_div_union_subset_union`

English:
theorem inter_div_union_subset_union
  statement: s₁ inter s₂ / (t₁ union t₂) subseteq s₁ / t₁ union s₂ / t₂
  proof: image2_inter_union_subset_union

@[to_additive]

中文:
定理 inter_div_union_subset_union
  结论: s₁ inter s₂ / (t₁ union t₂) subseteq s₁ / t₁ union s₂ / t₂
  证明: image2_inter_union_subset_union

@[to_additive]

Depends on / 依赖: image2_inter_union_subset_union
-/
theorem inter_div_union_subset_union : s₁ inter s₂ / (t₁ union t₂) subseteq s₁ / t₁ union s₂ / t₂ :=
  image2_inter_union_subset_union

@[to_additive]
/--
theorem `union_div_inter_subset_union` / 定理 `union_div_inter_subset_union`

English:
theorem union_div_inter_subset_union
  statement: (s₁ union s₂) / (t₁ inter t₂) subseteq s₁ / t₁ union s₂ / t₂
  proof: image2_union_inter_subset_union

@[to_additive (attr := simp) prod_sub_prod_comm]

中文:
定理 union_div_inter_subset_union
  结论: (s₁ union s₂) / (t₁ inter t₂) subseteq s₁ / t₁ union s₂ / t₂
  证明: image2_union_inter_subset_union

@[to_additive (attr := simp) prod_sub_prod_comm]

Depends on / 依赖: image2_union_inter_subset_union
-/
theorem union_div_inter_subset_union : (s₁ union s₂) / (t₁ inter t₂) subseteq s₁ / t₁ union s₂ / t₂ :=
  image2_union_inter_subset_union

@[to_additive (attr := simp) prod_sub_prod_comm]
/--
lemma `prod_div_prod_comm` / 引理 `prod_div_prod_comm`

English:
lemma prod_div_prod_comm
  given: [Div β] (s₁ s₂ : Set α) (t₁ t₂ : Set β)
  proof: by aesop (add simp mem_div)

中文:
引理 prod_div_prod_comm
  条件: [除法 β] (s₁ s₂ : 集合 α) (t₁ t₂ : 集合 β)
  证明: by aesop (add simp mem_div)

Depends on / 依赖: mem_div
-/
lemma prod_div_prod_comm [Div β] (s₁ s₂ : Set α) (t₁ t₂ : Set β) :
    (s₁ ×ˢ t₁) / (s₂ ×ˢ t₂) = (s₁ / s₂) ×ˢ (t₁ / t₂) := by aesop (add simp mem_div)

end Div

-- TODO: rename `NPow` to `npow` and `ZPow` to `zpow`.
/-- Repeated pointwise multiplication (not the same as pointwise repeated multiplication!) of a
`Set`. See note [pointwise nat action]. -/
@[to_additive (attr := instance_reducible)
/-- Repeated pointwise addition (not the same as pointwise repeated addition!) of a `Set`. See
note [pointwise nat action]. -/]
/--
Definition of `NPow` / `NPow` 的定义

English:
definition NPow
  signature: [One α] [Mul α]
  body: ⟨fun s n => npowRec n s⟩

中文:
定义 自然数幂
  签名: [幺 α] [乘法 α]
  定义体: ⟨fun s n => npowRec n s⟩
-/
protected def NPow [One α] [Mul α] : Pow (Set α) Nat :=
  ⟨fun s n => npowRec n s⟩

/-- Repeated pointwise multiplication/division (not the same as pointwise repeated
multiplication/division!) of a `Set`. See note [pointwise nat action]. -/
@[to_additive (attr := instance_reducible)
/-- Repeated pointwise addition/subtraction (not the same as pointwise repeated
addition/subtraction!) of a `Set`. See note [pointwise nat action]. -/]
/--
Definition of `ZPow` / `ZPow` 的定义

English:
definition ZPow
  signature: [One α] [Mul α] [Inv α]
  body: ⟨fun s n => zpowRec npowRec n s⟩

scoped[Pointwise] attribute [instance] Set.NSMul Set.NPow Set.ZSMul Set.ZPow

中文:
定义 整数幂
  签名: [幺 α] [乘法 α] [取逆 α]
  定义体: ⟨fun s n => zpowRec npowRec n s⟩

scoped[Pointwise] attribute [instance] Set.NSMul Set.NPow Set.ZSMul Set.ZPow
-/
protected def ZPow [One α] [Mul α] [Inv α] : Pow (Set α) Int :=
  ⟨fun s n => zpowRec npowRec n s⟩

scoped[Pointwise] attribute [instance] Set.NSMul Set.NPow Set.ZSMul Set.ZPow

/-- `Set α` is a `Semigroup` under pointwise operations if `α` is. -/
@[to_additive (attr := instance_reducible)
  /-- `Set α` is an `AddSemigroup` under pointwise operations if `α` is. -/]
/--
Definition of `semigroup` / `semigroup` 的定义

English:
definition semigroup
  signature: [Semigroup α]
  body: { Set.mul with mul_assoc := fun _ _ _ => image2_assoc mul_assoc }

中文:
定义 semigroup
  签名: [半群 α]
  定义体: { Set.mul with mul_assoc := fun _ _ _ => image2_assoc mul_assoc }
-/
protected def semigroup [Semigroup α] : Semigroup (Set α) :=
  { Set.mul with mul_assoc := fun _ _ _ => image2_assoc mul_assoc }

section CommSemigroup

variable [CommSemigroup α] {s t : Set α}

/-- `Set α` is a `CommSemigroup` under pointwise operations if `α` is. -/
@[to_additive (attr := instance_reducible)
  /-- `Set α` is an `AddCommSemigroup` under pointwise operations if `α` is. -/]
/--
Definition of `commSemigroup` / `commSemigroup` 的定义

English:
definition commSemigroup
  signature: : CommSemigroup (Set α)
  body: { Set.semigroup with mul_comm := fun _ _ => image2_comm mul_comm }

@[to_additive]

中文:
定义 commSemigroup
  签名: : 交换半群 (集合 α)
  定义体: { Set.semigroup with mul_comm := fun _ _ => image2_comm mul_comm }

@[to_additive]
-/
protected def commSemigroup : CommSemigroup (Set α) :=
  { Set.semigroup with mul_comm := fun _ _ => image2_comm mul_comm }

@[to_additive]
/--
theorem `inter_mul_union_subset` / 定理 `inter_mul_union_subset`

English:
theorem inter_mul_union_subset
  statement: s inter t * (s union t) subseteq s * t
  proof: image2_inter_union_subset mul_comm

@[to_additive]

中文:
定理 inter_mul_union_subset
  结论: s inter t * (s union t) subseteq s * t
  证明: image2_inter_union_subset mul_comm

@[to_additive]

Depends on / 依赖: image2_inter_union_subset, mul_comm
-/
theorem inter_mul_union_subset : s inter t * (s union t) subseteq s * t :=
  image2_inter_union_subset mul_comm

@[to_additive]
/--
theorem `union_mul_inter_subset` / 定理 `union_mul_inter_subset`

English:
theorem union_mul_inter_subset
  statement: (s union t) * (s inter t) subseteq s * t
  proof: image2_union_inter_subset mul_comm

中文:
定理 union_mul_inter_subset
  结论: (s union t) * (s inter t) subseteq s * t
  证明: image2_union_inter_subset mul_comm

Depends on / 依赖: image2_union_inter_subset, mul_comm
-/
theorem union_mul_inter_subset : (s union t) * (s inter t) subseteq s * t :=
  image2_union_inter_subset mul_comm

end CommSemigroup

section MulOneClass

variable [MulOneClass α]

/-- `Set α` is a `MulOneClass` under pointwise operations if `α` is. -/
@[to_additive (attr := instance_reducible)
  /-- `Set α` is an `AddZeroClass` under pointwise operations if `α` is. -/]
/--
Definition of `mulOneClass` / `mulOneClass` 的定义

English:
definition mulOneClass
  signature: : MulOneClass (Set α)
  body: { Set.one, Set.mul with
    mul_one := image2_right_identity mul_one
    one_mul := image2_left_identity one_mul }

scoped[Pointwise]
  attribute [instance]
    Set.mulOneClass Set.addZeroClass Set.semigroup Set.addSemigroup Set.commSemigroup
    Set.addCommSemigroup

@[to_additive]

中文:
定义 mulOneClass
  签名: : MulOne类 (集合 α)
  定义体: { Set.one, Set.mul with
    mul_one := image2_right_identity mul_one
    one_mul := image2_left_identity one_mul }

scoped[Pointwise]
  attribute [instance]
    Set.mulOneClass Set.addZeroClass Set.semigroup Set.addSemigroup Set.commSemigroup
    Set.addCommSemigroup

@[to_additive]
-/
protected def mulOneClass : MulOneClass (Set α) :=
  { Set.one, Set.mul with
    mul_one := image2_right_identity mul_one
    one_mul := image2_left_identity one_mul }

scoped[Pointwise]
  attribute [instance]
    Set.mulOneClass Set.addZeroClass Set.semigroup Set.addSemigroup Set.commSemigroup
    Set.addCommSemigroup

@[to_additive]
/--
theorem `subset_mul_left` / 定理 `subset_mul_left`

English:
theorem subset_mul_left
  given: (s : Set α) {t : Set α} (ht : (1 : α) in t)
  statement: s subseteq s * t
  proof: fun x hx =>
  ⟨x, hx, 1, ht, mul_one _⟩

@[to_additive]

中文:
定理 subset_mul_left
  条件: (s : 集合 α) {t : 集合 α} (ht : (1 : α) in t)
  结论: s subseteq s * t
  证明: fun x hx =>
  ⟨x, hx, 1, ht, mul_one _⟩

@[to_additive]
-/
theorem subset_mul_left (s : Set α) {t : Set α} (ht : (1 : α) in t) : s subseteq s * t := fun x hx =>
  ⟨x, hx, 1, ht, mul_one _⟩

@[to_additive]
/--
theorem `subset_mul_right` / 定理 `subset_mul_right`

English:
theorem subset_mul_right
  given: {s : Set α} (t : Set α) (hs : (1 : α) in s)
  statement: t subseteq s * t
  proof: fun x hx =>
  ⟨1, hs, x, hx, one_mul _⟩

中文:
定理 subset_mul_right
  条件: {s : 集合 α} (t : 集合 α) (hs : (1 : α) in s)
  结论: t subseteq s * t
  证明: fun x hx =>
  ⟨1, hs, x, hx, one_mul _⟩
-/
theorem subset_mul_right {s : Set α} (t : Set α) (hs : (1 : α) in s) : t subseteq s * t := fun x hx =>
  ⟨1, hs, x, hx, one_mul _⟩

/-- The singleton operation as a `MonoidHom`. -/
@[to_additive /-- The singleton operation as an `AddMonoidHom`. -/]
/--
Definition of `singletonMonoidHom` / `singletonMonoidHom` 的定义

English:
definition singletonMonoidHom
  signature: : α ->* Set α
  body: { singletonMulHom, singletonOneHom with }

@[to_additive (attr := simp)]

中文:
定义 singletonMonoidHom
  签名: : α ->* 集合 α
  定义体: { singletonMulHom, singletonOneHom with }

@[to_additive (attr := simp)]

Depends on / 依赖: singletonMulHom, singletonOneHom
-/
def singletonMonoidHom : α ->* Set α :=
  { singletonMulHom, singletonOneHom with }

@[to_additive (attr := simp)]
/--
theorem `coe_singletonMonoidHom` / 定理 `coe_singletonMonoidHom`

English:
theorem coe_singletonMonoidHom
  statement: (singletonMonoidHom : α -> Set α) = singleton
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 coe_singletonMonoidHom
  结论: (singletonMonoidHom : α -> 集合 α) = singleton
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem coe_singletonMonoidHom : (singletonMonoidHom : α -> Set α) = singleton :=
  rfl

@[to_additive (attr := simp)]
/--
theorem `singletonMonoidHom_apply` / 定理 `singletonMonoidHom_apply`

English:
theorem singletonMonoidHom_apply
  given: (a : α)
  statement: singletonMonoidHom a = {a}
  proof: rfl

中文:
定理 singletonMonoidHom_apply
  条件: (a : α)
  结论: singletonMonoidHom a = {a}
  证明: rfl
-/
theorem singletonMonoidHom_apply (a : α) : singletonMonoidHom a = {a} :=
  rfl

end MulOneClass

section Monoid

variable [Monoid α] {s t : Set α} {a : α} {m n : Nat}

/-- `Set α` is a `Monoid` under pointwise operations if `α` is. -/
@[to_additive (attr := instance_reducible)
  /-- `Set α` is an `AddMonoid` under pointwise operations if `α` is. -/]
/--
Definition of `monoid` / `monoid` 的定义

English:
definition monoid
  signature: : Monoid (Set α)
  body: { Set.semigroup, Set.mulOneClass, @Set.NPow α _ _ with }

scoped[Pointwise] attribute [instance] Set.monoid Set.addMonoid

中文:
定义 monoid
  签名: : 幺半群 (集合 α)
  定义体: { Set.semigroup, Set.mulOneClass, @Set.NPow α _ _ with }

scoped[Pointwise] attribute [instance] Set.monoid Set.addMonoid
-/
protected def monoid : Monoid (Set α) :=
  { Set.semigroup, Set.mulOneClass, @Set.NPow α _ _ with }

scoped[Pointwise] attribute [instance] Set.monoid Set.addMonoid

-- `Set.pow_left_monotone` doesn't exist since it would syntactically be a special case of
-- `pow_left_mono`

@[to_additive]
/--
lemma `pow_right_monotone` / 引理 `pow_right_monotone`

English:
lemma pow_right_monotone
  given: (hs : 1 in s)
  statement: Monotone (s ^ ·)
  proof: pow_right_monotone one_subset.2 hs

@[to_additive]

中文:
引理 pow_right_monotone
  条件: (hs : 1 in s)
  结论: 递增 (s ^ ·)
  证明: pow_right_monotone one_subset.2 hs

@[to_additive]
-/
protected lemma pow_right_monotone (hs : 1 in s) : Monotone (s ^ ·) :=
pow_right_monotone one_subset.2 hs

@[to_additive]
/--
lemma `pow_subset_pow_left` / 引理 `pow_subset_pow_left`

English:
lemma pow_subset_pow_left
  given: (hst : s subseteq t)
  statement: s ^ n subseteq t ^ n
  proof: pow_left_mono _ hst

@[to_additive]

中文:
引理 pow_subset_pow_left
  条件: (hst : s subseteq t)
  结论: s ^ n subseteq t ^ n
  证明: pow_left_mono _ hst

@[to_additive]

Depends on / 依赖: pow_left_mono
-/
lemma pow_subset_pow_left (hst : s subseteq t) : s ^ n subseteq t ^ n := pow_left_mono _ hst

@[to_additive]
/--
lemma `pow_subset_pow_right` / 引理 `pow_subset_pow_right`

English:
lemma pow_subset_pow_right
  given: (hs : 1 in s) (hmn : m <= n)
  statement: s ^ m subseteq s ^ n
  proof: Set.pow_right_monotone hs hmn

@[to_additive (attr := gcongr)]

中文:
引理 pow_subset_pow_right
  条件: (hs : 1 in s) (hmn : m <= n)
  结论: s ^ m subseteq s ^ n
  证明: Set.pow_right_monotone hs hmn

@[to_additive (attr := gcongr)]

Depends on / 依赖: Set.pow_right_monotone, pow_right_monotone
-/
lemma pow_subset_pow_right (hs : 1 in s) (hmn : m <= n) : s ^ m subseteq s ^ n :=
  Set.pow_right_monotone hs hmn

@[to_additive (attr := gcongr)]
/--
lemma `pow_subset_pow` / 引理 `pow_subset_pow`

English:
lemma pow_subset_pow
  given: (hst : s subseteq t) (ht : 1 in t) (hmn : m <= n)
  statement: s ^ m subseteq t ^ n
  proof: (pow_subset_pow_left hst).trans (pow_subset_pow_right ht hmn)

@[to_additive]

中文:
引理 pow_subset_pow
  条件: (hst : s subseteq t) (ht : 1 in t) (hmn : m <= n)
  结论: s ^ m subseteq t ^ n
  证明: (pow_subset_pow_left hst).trans (pow_subset_pow_right ht hmn)

@[to_additive]

Depends on / 依赖: pow_subset_pow_left, pow_subset_pow_right
-/
lemma pow_subset_pow (hst : s subseteq t) (ht : 1 in t) (hmn : m <= n) : s ^ m subseteq t ^ n :=
  (pow_subset_pow_left hst).trans (pow_subset_pow_right ht hmn)

@[to_additive]
/--
lemma `subset_pow` / 引理 `subset_pow`

English:
lemma subset_pow
  given: (hs : 1 in s) (hn : n != 0)
  statement: s subseteq s ^ n
  proof: by
simpa using pow_subset_pow_right hs Nat.one_le_iff_ne_zero.2 hn

@[to_additive]

中文:
引理 subset_pow
  条件: (hs : 1 in s) (hn : n != 0)
  结论: s subseteq s ^ n
  证明: by
simpa using pow_subset_pow_right hs Nat.one_le_iff_ne_zero.2 hn

@[to_additive]

Depends on / 依赖: Nat.one_le_iff_ne_zero, one_le_iff_ne_zero, pow_subset_pow_right
-/
lemma subset_pow (hs : 1 in s) (hn : n != 0) : s subseteq s ^ n := by
simpa using pow_subset_pow_right hs Nat.one_le_iff_ne_zero.2 hn

@[to_additive]
/--
lemma `pow_subset_pow_mul_of_sq_subset_mul` / 引理 `pow_subset_pow_mul_of_sq_subset_mul`

English:
lemma pow_subset_pow_mul_of_sq_subset_mul
  given: (hst : s ^ 2 subseteq t * s) (hn : n != 0)
  proof: pow_le_pow_mul_of_sq_le_mul hst hn

@[to_additive (attr := simp) nsmul_empty]

中文:
引理 pow_subset_pow_mul_of_sq_subset_mul
  条件: (hst : s ^ 2 subseteq t * s) (hn : n != 0)
  证明: pow_le_pow_mul_of_sq_le_mul hst hn

@[to_additive (attr := simp) nsmul_empty]

Depends on / 依赖: pow_le_pow_mul_of_sq_le_mul
-/
lemma pow_subset_pow_mul_of_sq_subset_mul (hst : s ^ 2 subseteq t * s) (hn : n != 0) :
    s ^ n subseteq t ^ (n - 1) * s := pow_le_pow_mul_of_sq_le_mul hst hn

@[to_additive (attr := simp) nsmul_empty]
/--
lemma `empty_pow` / 引理 `empty_pow`

English:
lemma empty_pow
  given: (hn : n != 0)
  statement: (∅ : Set α) ^ n = ∅
  proof: match n with | n + 1 => by simp [pow_succ]

@[to_additive]

中文:
引理 empty_pow
  条件: (hn : n != 0)
  结论: (∅ : 集合 α) ^ n = ∅
  证明: match n with | n + 1 => by simp [pow_succ]

@[to_additive]

Depends on / 依赖: pow_succ
-/
lemma empty_pow (hn : n != 0) : (∅ : Set α) ^ n = ∅ := match n with | n + 1 => by simp [pow_succ]

@[to_additive]
/--
lemma `Nonempty.pow` / 引理 `Nonempty.pow`

English:
lemma Nonempty.pow
  given: (hs : s.Nonempty)
  statement: forall {n}, (s ^ n).Nonempty

中文:
引理 非空.pow
  条件: (hs : s.非空)
  结论: 对任意 {n}, (s ^ n).非空
-/
lemma Nonempty.pow (hs : s.Nonempty) : forall {n}, (s ^ n).Nonempty
  | 0 => by simp
  | n + 1 => by rw [pow_succ]; exact hs.pow.mul hs

/--
lemma `pow_eq_empty` / 引理 `pow_eq_empty`

English:
lemma pow_eq_empty
  statement: s ^ n = ∅ ↔ s = ∅ ∧ n != 0
  proof: by
  constructor
  · contrapose! +distrib
    rintro (hs | rfl)
    · exact hs.pow
    · simp
  · rintro ⟨rfl, hn⟩
    exact empty_pow hn

@[to_additive (attr := simp) nsmul_singleton]

中文:
引理 pow_eq_empty
  结论: s ^ n = ∅ ↔ s = ∅ ∧ n != 0
  证明: by
  constructor
  · contrapose! +distrib
    rintro (hs | rfl)
    · exact hs.pow
    · simp
  · rintro ⟨rfl, hn⟩
    exact empty_pow hn

@[to_additive (attr := simp) nsmul_singleton]
-/
@[to_additive (attr := simp)] lemma pow_eq_empty : s ^ n = ∅ ↔ s = ∅ ∧ n != 0 := by
  constructor
  · contrapose! +distrib
    rintro (hs | rfl)
    · exact hs.pow
    · simp
  · rintro ⟨rfl, hn⟩
    exact empty_pow hn

@[to_additive (attr := simp) nsmul_singleton]
/--
lemma `singleton_pow` / 引理 `singleton_pow`

English:
lemma singleton_pow
  given: (a : α)
  statement: forall n, ({a} : Set α) ^ n = {a ^ n}

中文:
引理 singleton_pow
  条件: (a : α)
  结论: 对任意 n, ({a} : 集合 α) ^ n = {a ^ n}
-/
lemma singleton_pow (a : α) : forall n, ({a} : Set α) ^ n = {a ^ n}
  | 0 => by simp [singleton_one]
  | n + 1 => by simp [pow_succ, singleton_pow _ n]

/--
lemma `pow_mem_pow` / 引理 `pow_mem_pow`

English:
lemma pow_mem_pow
  given: (ha : a in s)
  statement: a ^ n in s ^ n
  proof: by
  simpa using pow_subset_pow_left (singleton_subset_iff.2 ha)

中文:
引理 pow_mem_pow
  条件: (ha : a in s)
  结论: a ^ n in s ^ n
  证明: by
  simpa using pow_subset_pow_left (singleton_subset_iff.2 ha)
-/
@[to_additive] lemma pow_mem_pow (ha : a in s) : a ^ n in s ^ n := by
  simpa using pow_subset_pow_left (singleton_subset_iff.2 ha)

/--
lemma `one_mem_pow` / 引理 `one_mem_pow`

English:
lemma one_mem_pow
  given: (hs : 1 in s)
  statement: 1 in s ^ n
  proof: by simpa using pow_mem_pow hs

@[to_additive]

中文:
引理 one_mem_pow
  条件: (hs : 1 in s)
  结论: 1 in s ^ n
  证明: by simpa using pow_mem_pow hs

@[to_additive]
-/
@[to_additive] lemma one_mem_pow (hs : 1 in s) : 1 in s ^ n := by simpa using pow_mem_pow hs

@[to_additive]
/--
lemma `inter_pow_subset` / 引理 `inter_pow_subset`

English:
lemma inter_pow_subset
  statement: (s inter t) ^ n subseteq s ^ n inter t ^ n
  proof: by apply subset_inter <;> gcongr <;> simp

@[to_additive]

中文:
引理 inter_pow_subset
  结论: (s inter t) ^ n subseteq s ^ n inter t ^ n
  证明: by apply subset_inter <;> gcongr <;> simp

@[to_additive]

Depends on / 依赖: subset_inter
-/
lemma inter_pow_subset : (s inter t) ^ n subseteq s ^ n inter t ^ n := by apply subset_inter <;> gcongr <;> simp

@[to_additive]
/--
theorem `mul_univ_of_one_mem` / 定理 `mul_univ_of_one_mem`

English:
theorem mul_univ_of_one_mem
  given: (hs : (1 : α) in s)
  statement: s * univ = univ
  proof: eq_univ_iff_forall.2 fun _ => mem_mul.2 ⟨_, hs, _, mem_univ _, one_mul _⟩

@[to_additive]

中文:
定理 mul_univ_of_one_mem
  条件: (hs : (1 : α) in s)
  结论: s * univ = univ
  证明: eq_univ_iff_forall.2 fun _ => mem_mul.2 ⟨_, hs, _, mem_univ _, one_mul _⟩

@[to_additive]

Depends on / 依赖: eq_univ_iff_forall, mem_mul, mem_univ, one_mul
-/
theorem mul_univ_of_one_mem (hs : (1 : α) in s) : s * univ = univ :=
  eq_univ_iff_forall.2 fun _ => mem_mul.2 ⟨_, hs, _, mem_univ _, one_mul _⟩

@[to_additive]
/--
theorem `univ_mul_of_one_mem` / 定理 `univ_mul_of_one_mem`

English:
theorem univ_mul_of_one_mem
  given: (ht : (1 : α) in t)
  statement: univ * t = univ
  proof: eq_univ_iff_forall.2 fun _ => mem_mul.2 ⟨_, mem_univ _, _, ht, mul_one _⟩

@[to_additive (attr := simp)]

中文:
定理 univ_mul_of_one_mem
  条件: (ht : (1 : α) in t)
  结论: univ * t = univ
  证明: eq_univ_iff_forall.2 fun _ => mem_mul.2 ⟨_, mem_univ _, _, ht, mul_one _⟩

@[to_additive (attr := simp)]

Depends on / 依赖: eq_univ_iff_forall, mem_mul, mem_univ, mul_one
-/
theorem univ_mul_of_one_mem (ht : (1 : α) in t) : univ * t = univ :=
  eq_univ_iff_forall.2 fun _ => mem_mul.2 ⟨_, mem_univ _, _, ht, mul_one _⟩

@[to_additive (attr := simp)]
/--
theorem `univ_mul_univ` / 定理 `univ_mul_univ`

English:
theorem univ_mul_univ
  statement: (univ : Set α) * univ = univ
  proof: mul_univ_of_one_mem mem_univ _

@[to_additive (attr := simp) nsmul_univ]

中文:
定理 univ_mul_univ
  结论: (univ : 集合 α) * univ = univ
  证明: mul_univ_of_one_mem mem_univ _

@[to_additive (attr := simp) nsmul_univ]

Depends on / 依赖: mem_univ, mul_univ_of_one_mem
-/
theorem univ_mul_univ : (univ : Set α) * univ = univ :=
mul_univ_of_one_mem mem_univ _

@[to_additive (attr := simp) nsmul_univ]
/--
theorem `univ_pow` / 定理 `univ_pow`

English:
theorem univ_pow
  statement: forall {n : Nat}, n != 0 -> (univ : Set α) ^ n = univ

中文:
定理 univ_pow
  结论: 对任意 {n : 自然数}, n != 0 -> (univ : 集合 α) ^ n = univ
-/
theorem univ_pow : forall {n : Nat}, n != 0 -> (univ : Set α) ^ n = univ
  | 0 => fun h => (h rfl).elim
  | 1 => fun _ => pow_one _
  | n + 2 => fun _ => by rw [pow_succ, univ_pow n.succ_ne_zero, univ_mul_univ]

@[to_additive]
/--
theorem `_root_.IsUnit.set` / 定理 `_root_.IsUnit.set`

English:
theorem _root_.IsUnit.set
  statement: IsUnit a -> IsUnit ({a} : Set α)
  proof: IsUnit.map (singletonMonoidHom : α ->* Set α)

@[to_additive nsmul_prod]

中文:
定理 _root_.是单位.set
  结论: 是单位 a -> 是单位 ({a} : 集合 α)
  证明: IsUnit.map (singletonMonoidHom : α ->* Set α)

@[to_additive nsmul_prod]
-/
protected theorem _root_.IsUnit.set : IsUnit a -> IsUnit ({a} : Set α) :=
  IsUnit.map (singletonMonoidHom : α ->* Set α)

@[to_additive nsmul_prod]
/--
lemma `prod_pow` / 引理 `prod_pow`

English:
lemma prod_pow
  given: [Monoid β] (s : Set α) (t : Set β)
  statement: forall n, (s ×ˢ t) ^ n = (s ^ n) ×ˢ (t ^ n)

中文:
引理 prod_pow
  条件: [幺半群 β] (s : 集合 α) (t : 集合 β)
  结论: 对任意 n, (s ×ˢ t) ^ n = (s ^ n) ×ˢ (t ^ n)
-/
lemma prod_pow [Monoid β] (s : Set α) (t : Set β) : forall n, (s ×ˢ t) ^ n = (s ^ n) ×ˢ (t ^ n)
  | 0 => by simp
  | n + 1 => by simp [pow_succ, prod_pow _ _ n]

end Monoid

section IsLeftCancelMul
variable [Mul α] [IsLeftCancelMul α] {s t : Set α}

@[to_additive]
/--
lemma `Nontrivial.mul_left` / 引理 `Nontrivial.mul_left`

English:
lemma Nontrivial.mul_left
  statement: t.Nontrivial -> s.Nonempty -> (s * t).Nontrivial
  proof: by
  rintro ⟨a, ha, b, hb, hab⟩ ⟨c, hc⟩
  exact ⟨c * a, mul_mem_mul hc ha, c * b, mul_mem_mul hc hb, by simpa⟩

@[to_additive]

中文:
引理 非平凡.mul_left
  结论: t.非平凡 -> s.非空 -> (s * t).非平凡
  证明: by
  rintro ⟨a, ha, b, hb, hab⟩ ⟨c, hc⟩
  exact ⟨c * a, mul_mem_mul hc ha, c * b, mul_mem_mul hc hb, by simpa⟩

@[to_additive]
-/
lemma Nontrivial.mul_left : t.Nontrivial -> s.Nonempty -> (s * t).Nontrivial := by
  rintro ⟨a, ha, b, hb, hab⟩ ⟨c, hc⟩
  exact ⟨c * a, mul_mem_mul hc ha, c * b, mul_mem_mul hc hb, by simpa⟩

@[to_additive]
/--
lemma `Nontrivial.mul` / 引理 `Nontrivial.mul`

English:
lemma Nontrivial.mul
  given: (hs : s.Nontrivial) (ht : t.Nontrivial)
  statement: (s * t).Nontrivial
  proof: ht.mul_left hs.nonempty

中文:
引理 非平凡.mul
  条件: (hs : s.非平凡) (ht : t.非平凡)
  结论: (s * t).非平凡
  证明: ht.mul_left hs.nonempty
-/
lemma Nontrivial.mul (hs : s.Nontrivial) (ht : t.Nontrivial) : (s * t).Nontrivial :=
  ht.mul_left hs.nonempty

end IsLeftCancelMul

section IsRightCancelMul
variable [Mul α] [IsRightCancelMul α] {s t : Set α}

@[to_additive]
/--
lemma `Nontrivial.mul_right` / 引理 `Nontrivial.mul_right`

English:
lemma Nontrivial.mul_right
  statement: s.Nontrivial -> t.Nonempty -> (s * t).Nontrivial
  proof: by
  rintro ⟨a, ha, b, hb, hab⟩ ⟨c, hc⟩
  exact ⟨a * c, mul_mem_mul ha hc, b * c, mul_mem_mul hb hc, by simpa⟩

中文:
引理 非平凡.mul_right
  结论: s.非平凡 -> t.非空 -> (s * t).非平凡
  证明: by
  rintro ⟨a, ha, b, hb, hab⟩ ⟨c, hc⟩
  exact ⟨a * c, mul_mem_mul ha hc, b * c, mul_mem_mul hb hc, by simpa⟩
-/
lemma Nontrivial.mul_right : s.Nontrivial -> t.Nonempty -> (s * t).Nontrivial := by
  rintro ⟨a, ha, b, hb, hab⟩ ⟨c, hc⟩
  exact ⟨a * c, mul_mem_mul ha hc, b * c, mul_mem_mul hb hc, by simpa⟩

end IsRightCancelMul

section CancelMonoid
variable [CancelMonoid α] {s t : Set α} {a : α} {n : Nat}

@[to_additive]
/--
lemma `Nontrivial.pow` / 引理 `Nontrivial.pow`

English:
lemma Nontrivial.pow
  given: (hs : s.Nontrivial)
  statement: forall {n}, n != 0 -> (s ^ n).Nontrivial

中文:
引理 非平凡.pow
  条件: (hs : s.非平凡)
  结论: 对任意 {n}, n != 0 -> (s ^ n).非平凡
-/
lemma Nontrivial.pow (hs : s.Nontrivial) : forall {n}, n != 0 -> (s ^ n).Nontrivial
  | 1, _ => by simpa
  | n + 2, _ => by simpa [pow_succ] using (hs.pow n.succ_ne_zero).mul hs

end CancelMonoid

/-- `Set α` is a `CommMonoid` under pointwise operations if `α` is. -/
@[to_additive (attr := instance_reducible)
  /-- `Set α` is an `AddCommMonoid` under pointwise operations if `α` is. -/]
/--
Definition of `commMonoid` / `commMonoid` 的定义

English:
definition commMonoid
  signature: [CommMonoid α]
  body: { Set.monoid, Set.commSemigroup with }

scoped[Pointwise] attribute [instance] Set.commMonoid Set.addCommMonoid

中文:
定义 commMonoid
  签名: [交换幺半群 α]
  定义体: { Set.monoid, Set.commSemigroup with }

scoped[Pointwise] attribute [instance] Set.commMonoid Set.addCommMonoid
-/
protected def commMonoid [CommMonoid α] : CommMonoid (Set α) :=
  { Set.monoid, Set.commSemigroup with }

scoped[Pointwise] attribute [instance] Set.commMonoid Set.addCommMonoid

open scoped Pointwise

section DivisionMonoid

variable [DivisionMonoid α] {s t : Set α} {n : Int}

@[to_additive]
/--
theorem `mul_eq_one_iff` / 定理 `mul_eq_one_iff`

English:
theorem mul_eq_one_iff
  statement: s * t = 1 ↔ exists a b, s = {a} ∧ t = {b} ∧ a * b = 1
  proof: by
  refine ⟨fun h => ?_, ?_⟩
  · have hst : (s * t).Nonempty := h.symm.subst one_nonempty
    obtain ⟨a, ha⟩ := hst.of_image2_left
    obtain ⟨b, hb⟩ := hst.of_image2_right
    have H : forall {a b}, a in s -> b in t -> a * b = (1 : α) := fun {a b} ha hb =>
h.subset mem_image2_of_mem ha hb
    refine ⟨a, b, ?_, ?_, H ha hb⟩ <;> refine eq_singleton_iff_unique_mem.2 ⟨‹_›, fun x hx => ?_⟩
    · exact (eq_inv_of_mul_eq_one_left <| H hx hb).trans (inv_eq_of_mul_eq_one_left <| H ha hb)
    · exact (eq_inv_of_mul_eq_one_right <| H ha hx).trans (inv_eq_of_mul_eq_one_right <| H ha hb)
  · rintro ⟨b, c, rfl, rfl, h⟩
    rw [singleton_mul_singleton]; rw [h]; rw [singleton_one]

中文:
定理 mul_eq_one_iff
  结论: s * t = 1 ↔ 存在 a b, s = {a} ∧ t = {b} ∧ a * b = 1
  证明: by
  refine ⟨fun h => ?_, ?_⟩
  · have hst : (s * t).Nonempty := h.symm.subst one_nonempty
    obtain ⟨a, ha⟩ := hst.of_image2_left
    obtain ⟨b, hb⟩ := hst.of_image2_right
    have H : forall {a b}, a in s -> b in t -> a * b = (1 : α) := fun {a b} ha hb =>
h.subset mem_image2_of_mem ha hb
    refine ⟨a, b, ?_, ?_, H ha hb⟩ <;> refine eq_singleton_iff_unique_mem.2 ⟨‹_›, fun x hx => ?_⟩
    · exact (eq_inv_of_mul_eq_one_left <| H hx hb).trans (inv_eq_of_mul_eq_one_left <| H ha hb)
    · exact (eq_inv_of_mul_eq_one_right <| H ha hx).trans (inv_eq_of_mul_eq_one_right <| H ha hb)
  · rintro ⟨b, c, rfl, rfl, h⟩
    rw [singleton_mul_singleton]; rw [h]; rw [singleton_one]
-/
protected theorem mul_eq_one_iff : s * t = 1 ↔ exists a b, s = {a} ∧ t = {b} ∧ a * b = 1 := by
  refine ⟨fun h => ?_, ?_⟩
  · have hst : (s * t).Nonempty := h.symm.subst one_nonempty
    obtain ⟨a, ha⟩ := hst.of_image2_left
    obtain ⟨b, hb⟩ := hst.of_image2_right
    have H : forall {a b}, a in s -> b in t -> a * b = (1 : α) := fun {a b} ha hb =>
h.subset mem_image2_of_mem ha hb
    refine ⟨a, b, ?_, ?_, H ha hb⟩ <;> refine eq_singleton_iff_unique_mem.2 ⟨‹_›, fun x hx => ?_⟩
    · exact (eq_inv_of_mul_eq_one_left <| H hx hb).trans (inv_eq_of_mul_eq_one_left <| H ha hb)
    · exact (eq_inv_of_mul_eq_one_right <| H ha hx).trans (inv_eq_of_mul_eq_one_right <| H ha hb)
  · rintro ⟨b, c, rfl, rfl, h⟩
    rw [singleton_mul_singleton]; rw [h]; rw [singleton_one]

/--
theorem `nonempty_image_mulLeft_inv_inter_iff` / 定理 `nonempty_image_mulLeft_inv_inter_iff`

English:
theorem nonempty_image_mulLeft_inv_inter_iff
  given: {a : α}
  proof: by
  rw [← nonempty_inv]; rw [inter_inv]; simp_rw [← image_inv_eq_inv, image_image, mul_inv_rev, inv_inv]

中文:
定理 nonempty_image_mulLeft_inv_inter_iff
  条件: {a : α}
  证明: by
  rw [← nonempty_inv]; rw [inter_inv]; simp_rw [← image_inv_eq_inv, image_image, mul_inv_rev, inv_inv]
-/
@[to_additive] theorem nonempty_image_mulLeft_inv_inter_iff {a : α} :
    ((a⁻¹ * ·) '' s inter t).Nonempty ↔ ((· * a) '' s⁻¹ inter t⁻¹).Nonempty := by
  rw [← nonempty_inv]; rw [inter_inv]; simp_rw [← image_inv_eq_inv, image_image, mul_inv_rev, inv_inv]

/--
theorem `nonempty_image_mulRight_inv_inter_iff` / 定理 `nonempty_image_mulRight_inv_inter_iff`

English:
theorem nonempty_image_mulRight_inv_inter_iff
  given: {a : α}
  proof: by
  rw [← nonempty_inv]; rw [inter_inv]; simp_rw [← image_inv_eq_inv, image_image, mul_inv_rev, inv_inv]

中文:
定理 nonempty_image_mulRight_inv_inter_iff
  条件: {a : α}
  证明: by
  rw [← nonempty_inv]; rw [inter_inv]; simp_rw [← image_inv_eq_inv, image_image, mul_inv_rev, inv_inv]
-/
@[to_additive] theorem nonempty_image_mulRight_inv_inter_iff {a : α} :
    ((· * a⁻¹) '' s inter t).Nonempty ↔ ((a * ·) '' s⁻¹ inter t⁻¹).Nonempty := by
  rw [← nonempty_inv]; rw [inter_inv]; simp_rw [← image_inv_eq_inv, image_image, mul_inv_rev, inv_inv]

/-- `Set α` is a division monoid under pointwise operations if `α` is. -/
@[to_additive (attr := instance_reducible)
    /-- `Set α` is a subtraction monoid under pointwise operations if `α` is. -/]
/--
Definition of `divisionMonoid` / `divisionMonoid` 的定义

English:
definition divisionMonoid
  signature: : DivisionMonoid (Set α)
  body: { Set.monoid, Set.involutiveInv, Set.div, @Set.ZPow α _ _ _ with
    mul_inv_rev := fun s t => by
      simp_rw [← image_inv_eq_inv]
      exact image_image2_antidistrib mul_inv_rev
    inv_eq_of_mul := fun s t h => by
      obtain ⟨a, b, rfl, rfl, hab⟩ := Set.mul_eq_one_iff.1 h
      rw [inv_singleton]; rw [inv_eq_of_mul_eq_one_right hab]
    div_eq_mul_inv := fun s t => by
      rw [← image_id (s / t)]; rw [← image_inv_eq_inv]
      exact image_image2_distrib_right div_eq_mul_inv }

scoped[Pointwise] attribute [instance] Set.divisionMonoid Set.subtractionMonoid

@[to_additive (attr := simp 500)]

中文:
定义 divisionMonoid
  签名: : Division幺半群 (集合 α)
  定义体: { Set.monoid, Set.involutiveInv, Set.div, @Set.ZPow α _ _ _ with
    mul_inv_rev := fun s t => by
      simp_rw [← image_inv_eq_inv]
      exact image_image2_antidistrib mul_inv_rev
    inv_eq_of_mul := fun s t h => by
      obtain ⟨a, b, rfl, rfl, hab⟩ := Set.mul_eq_one_iff.1 h
      rw [inv_singleton]; rw [inv_eq_of_mul_eq_one_right hab]
    div_eq_mul_inv := fun s t => by
      rw [← image_id (s / t)]; rw [← image_inv_eq_inv]
      exact image_image2_distrib_right div_eq_mul_inv }

scoped[Pointwise] attribute [instance] Set.divisionMonoid Set.subtractionMonoid

@[to_additive (attr := simp 500)]
-/
protected def divisionMonoid : DivisionMonoid (Set α) :=
  { Set.monoid, Set.involutiveInv, Set.div, @Set.ZPow α _ _ _ with
    mul_inv_rev := fun s t => by
      simp_rw [← image_inv_eq_inv]
      exact image_image2_antidistrib mul_inv_rev
    inv_eq_of_mul := fun s t h => by
      obtain ⟨a, b, rfl, rfl, hab⟩ := Set.mul_eq_one_iff.1 h
      rw [inv_singleton]; rw [inv_eq_of_mul_eq_one_right hab]
    div_eq_mul_inv := fun s t => by
      rw [← image_id (s / t)]; rw [← image_inv_eq_inv]
      exact image_image2_distrib_right div_eq_mul_inv }

scoped[Pointwise] attribute [instance] Set.divisionMonoid Set.subtractionMonoid

@[to_additive (attr := simp 500)]
/--
theorem `isUnit_iff` / 定理 `isUnit_iff`

English:
theorem isUnit_iff
  statement: IsUnit s ↔ exists a, s = {a} ∧ IsUnit a
  proof: by
  constructor
  · rintro ⟨u, rfl⟩
    obtain ⟨a, b, ha, hb, h⟩ := Set.mul_eq_one_iff.1 u.mul_inv
    refine ⟨a, ha, ⟨a, b, h, singleton_injective ?_⟩, rfl⟩
    rw [← singleton_mul_singleton]; rw [← ha]; rw [← hb]
    exact u.inv_mul
  · rintro ⟨a, rfl, ha⟩
    exact ha.set

@[to_additive (attr := simp)]

中文:
定理 isUnit_iff
  结论: 是单位 s ↔ 存在 a, s = {a} ∧ 是单位 a
  证明: by
  constructor
  · rintro ⟨u, rfl⟩
    obtain ⟨a, b, ha, hb, h⟩ := Set.mul_eq_one_iff.1 u.mul_inv
    refine ⟨a, ha, ⟨a, b, h, singleton_injective ?_⟩, rfl⟩
    rw [← singleton_mul_singleton]; rw [← ha]; rw [← hb]
    exact u.inv_mul
  · rintro ⟨a, rfl, ha⟩
    exact ha.set

@[to_additive (attr := simp)]

Depends on / 依赖: Set.mul_eq_one_iff, ha.set, inv_mul, mul_eq_one_iff, mul_inv, singleton_injective, singleton_mul_singleton, u.inv_mul, u.mul_inv
-/
theorem isUnit_iff : IsUnit s ↔ exists a, s = {a} ∧ IsUnit a := by
  constructor
  · rintro ⟨u, rfl⟩
    obtain ⟨a, b, ha, hb, h⟩ := Set.mul_eq_one_iff.1 u.mul_inv
    refine ⟨a, ha, ⟨a, b, h, singleton_injective ?_⟩, rfl⟩
    rw [← singleton_mul_singleton]; rw [← ha]; rw [← hb]
    exact u.inv_mul
  · rintro ⟨a, rfl, ha⟩
    exact ha.set

@[to_additive (attr := simp)]
/--
lemma `univ_div_univ` / 引理 `univ_div_univ`

English:
lemma univ_div_univ
  statement: (univ / univ : Set α) = univ
  proof: by simp [div_eq_mul_inv]

中文:
引理 univ_div_univ
  结论: (univ / univ : 集合 α) = univ
  证明: by simp [div_eq_mul_inv]

Depends on / 依赖: div_eq_mul_inv
-/
lemma univ_div_univ : (univ / univ : Set α) = univ := by simp [div_eq_mul_inv]

/--
lemma `subset_div_left` / 引理 `subset_div_left`

English:
lemma subset_div_left
  given: (ht : 1 in t)
  statement: s subseteq s / t
  proof: by
rw [div_eq_mul_inv]; exact subset_mul_left _ by simpa

中文:
引理 subset_div_left
  条件: (ht : 1 in t)
  结论: s subseteq s / t
  证明: by
rw [div_eq_mul_inv]; exact subset_mul_left _ by simpa
-/
@[to_additive] lemma subset_div_left (ht : 1 in t) : s subseteq s / t := by
rw [div_eq_mul_inv]; exact subset_mul_left _ by simpa

/--
lemma `inv_subset_div_right` / 引理 `inv_subset_div_right`

English:
lemma inv_subset_div_right
  given: (hs : 1 in s)
  statement: t⁻¹ subseteq s / t
  proof: by
  rw [div_eq_mul_inv]; exact subset_mul_right _ hs

@[to_additive (attr := simp) zsmul_empty]

中文:
引理 inv_subset_div_right
  条件: (hs : 1 in s)
  结论: t⁻¹ subseteq s / t
  证明: by
  rw [div_eq_mul_inv]; exact subset_mul_right _ hs

@[to_additive (attr := simp) zsmul_empty]
-/
@[to_additive] lemma inv_subset_div_right (hs : 1 in s) : t⁻¹ subseteq s / t := by
  rw [div_eq_mul_inv]; exact subset_mul_right _ hs

@[to_additive (attr := simp) zsmul_empty]
/--
lemma `empty_zpow` / 引理 `empty_zpow`

English:
lemma empty_zpow
  given: (hn : n != 0)
  statement: (∅ : Set α) ^ n = ∅
  proof: by cases n <;> aesop

@[to_additive]

中文:
引理 empty_zpow
  条件: (hn : n != 0)
  结论: (∅ : 集合 α) ^ n = ∅
  证明: by cases n <;> aesop

@[to_additive]
-/
lemma empty_zpow (hn : n != 0) : (∅ : Set α) ^ n = ∅ := by cases n <;> aesop

@[to_additive]
/--
lemma `Nonempty.zpow` / 引理 `Nonempty.zpow`

English:
lemma Nonempty.zpow
  given: (hs : s.Nonempty)
  statement: forall {n : Int}, (s ^ n).Nonempty

中文:
引理 非空.zpow
  条件: (hs : s.非空)
  结论: 对任意 {n : 整数}, (s ^ n).非空
-/
lemma Nonempty.zpow (hs : s.Nonempty) : forall {n : Int}, (s ^ n).Nonempty
  | (n : Nat) => hs.pow
  | .negSucc n => by simpa using hs.pow

/--
lemma `zpow_eq_empty` / 引理 `zpow_eq_empty`

English:
lemma zpow_eq_empty
  statement: s ^ n = ∅ ↔ s = ∅ ∧ n != 0
  proof: by
  constructor
  · contrapose! +distrib
    rintro (hs | rfl)
    · exact hs.zpow
    · simp
  · rintro ⟨rfl, hn⟩
    exact empty_zpow hn

@[to_additive (attr := simp) zsmul_singleton]

中文:
引理 zpow_eq_empty
  结论: s ^ n = ∅ ↔ s = ∅ ∧ n != 0
  证明: by
  constructor
  · contrapose! +distrib
    rintro (hs | rfl)
    · exact hs.zpow
    · simp
  · rintro ⟨rfl, hn⟩
    exact empty_zpow hn

@[to_additive (attr := simp) zsmul_singleton]
-/
@[to_additive (attr := simp)] lemma zpow_eq_empty : s ^ n = ∅ ↔ s = ∅ ∧ n != 0 := by
  constructor
  · contrapose! +distrib
    rintro (hs | rfl)
    · exact hs.zpow
    · simp
  · rintro ⟨rfl, hn⟩
    exact empty_zpow hn

@[to_additive (attr := simp) zsmul_singleton]
/--
lemma `singleton_zpow` / 引理 `singleton_zpow`

English:
lemma singleton_zpow
  given: (a : α) (n : Int)
  statement: ({a} : Set α) ^ n = {a ^ n}
  proof: by cases n <;> simp

中文:
引理 singleton_zpow
  条件: (a : α) (n : 整数)
  结论: ({a} : 集合 α) ^ n = {a ^ n}
  证明: by cases n <;> simp
-/
lemma singleton_zpow (a : α) (n : Int) : ({a} : Set α) ^ n = {a ^ n} := by cases n <;> simp

end DivisionMonoid

/-- `Set α` is a commutative division monoid under pointwise operations if `α` is. -/
@[to_additive (attr := instance_reducible) subtractionCommMonoid
      /-- `Set α` is a commutative subtraction monoid under pointwise operations if `α` is. -/]
/--
Definition of `divisionCommMonoid` / `divisionCommMonoid` 的定义

English:
definition divisionCommMonoid
  signature: [DivisionCommMonoid α]
  body: { Set.divisionMonoid, Set.commSemigroup with }

scoped[Pointwise] attribute [instance] Set.divisionCommMonoid Set.subtractionCommMonoid

中文:
定义 divisionCommMonoid
  签名: [DivisionComm幺半群 α]
  定义体: { Set.divisionMonoid, Set.commSemigroup with }

scoped[Pointwise] attribute [instance] Set.divisionCommMonoid Set.subtractionCommMonoid
-/
protected def divisionCommMonoid [DivisionCommMonoid α] :
    DivisionCommMonoid (Set α) :=
  { Set.divisionMonoid, Set.commSemigroup with }

scoped[Pointwise] attribute [instance] Set.divisionCommMonoid Set.subtractionCommMonoid

section Group

variable [Group α] {s t : Set α} {a b : α}

/-! Note that `Set` is not a `Group` because `s / s ≠ 1` in general. -/


@[to_additive (attr := simp)]
/--
theorem `one_mem_div_iff` / 定理 `one_mem_div_iff`

English:
theorem one_mem_div_iff
  statement: (1 : α) in s / t ↔ ¬Disjoint s t
  proof: by
  simp [not_disjoint_iff_nonempty_inter, mem_div, div_eq_one, Set.Nonempty]

@[to_additive (attr := simp)]

中文:
定理 one_mem_div_iff
  结论: (1 : α) in s / t ↔ ¬Disjoint s t
  证明: by
  simp [not_disjoint_iff_nonempty_inter, mem_div, div_eq_one, Set.Nonempty]

@[to_additive (attr := simp)]

Depends on / 依赖: Nonempty, Set.Nonempty, div_eq_one, mem_div, not_disjoint_iff_nonempty_inter
-/
theorem one_mem_div_iff : (1 : α) in s / t ↔ ¬Disjoint s t := by
  simp [not_disjoint_iff_nonempty_inter, mem_div, div_eq_one, Set.Nonempty]

@[to_additive (attr := simp)]
/--
lemma `one_mem_inv_mul_iff` / 引理 `one_mem_inv_mul_iff`

English:
lemma one_mem_inv_mul_iff
  statement: (1 : α) in t⁻¹ * s ↔ ¬Disjoint s t
  proof: by
  aesop (add simp [not_disjoint_iff_nonempty_inter, mem_mul, mul_eq_one_iff_eq_inv, Set.Nonempty])

@[to_additive]

中文:
引理 one_mem_inv_mul_iff
  结论: (1 : α) in t⁻¹ * s ↔ ¬Disjoint s t
  证明: by
  aesop (add simp [not_disjoint_iff_nonempty_inter, mem_mul, mul_eq_one_iff_eq_inv, Set.Nonempty])

@[to_additive]

Depends on / 依赖: Nonempty, Set.Nonempty, mem_mul, mul_eq_one_iff_eq_inv, not_disjoint_iff_nonempty_inter
-/
lemma one_mem_inv_mul_iff : (1 : α) in t⁻¹ * s ↔ ¬Disjoint s t := by
  aesop (add simp [not_disjoint_iff_nonempty_inter, mem_mul, mul_eq_one_iff_eq_inv, Set.Nonempty])

@[to_additive]
/--
theorem `one_notMem_div_iff` / 定理 `one_notMem_div_iff`

English:
theorem one_notMem_div_iff
  statement: (1 : α) ∉ s / t ↔ Disjoint s t
  proof: one_mem_div_iff.not_left

@[to_additive]

中文:
定理 one_notMem_div_iff
  结论: (1 : α) ∉ s / t ↔ Disjoint s t
  证明: one_mem_div_iff.not_left

@[to_additive]

Depends on / 依赖: not_left, one_mem_div_iff, one_mem_div_iff.not_left
-/
theorem one_notMem_div_iff : (1 : α) ∉ s / t ↔ Disjoint s t :=
  one_mem_div_iff.not_left

@[to_additive]
/--
lemma `one_notMem_inv_mul_iff` / 引理 `one_notMem_inv_mul_iff`

English:
lemma one_notMem_inv_mul_iff
  statement: (1 : α) ∉ t⁻¹ * s ↔ Disjoint s t
  proof: one_mem_inv_mul_iff.not_left

alias ⟨_, _root_.Disjoint.one_notMem_div_set⟩ := one_notMem_div_iff

中文:
引理 one_notMem_inv_mul_iff
  结论: (1 : α) ∉ t⁻¹ * s ↔ Disjoint s t
  证明: one_mem_inv_mul_iff.not_left

alias ⟨_, _root_.Disjoint.one_notMem_div_set⟩ := one_notMem_div_iff

Depends on / 依赖: not_left, one_mem_inv_mul_iff, one_mem_inv_mul_iff.not_left
-/
lemma one_notMem_inv_mul_iff : (1 : α) ∉ t⁻¹ * s ↔ Disjoint s t := one_mem_inv_mul_iff.not_left

alias ⟨_, _root_.Disjoint.one_notMem_div_set⟩ := one_notMem_div_iff

attribute [to_additive] Disjoint.one_notMem_div_set

@[to_additive]
/--
theorem `Nonempty.one_mem_div` / 定理 `Nonempty.one_mem_div`

English:
theorem Nonempty.one_mem_div
  given: (h : s.Nonempty)
  statement: (1 : α) in s / s
  proof: let ⟨a, ha⟩ := h
  mem_div.2 ⟨a, ha, a, ha, div_self' _⟩

@[to_additive]

中文:
定理 非空.one_mem_div
  条件: (h : s.非空)
  结论: (1 : α) in s / s
  证明: let ⟨a, ha⟩ := h
  mem_div.2 ⟨a, ha, a, ha, div_self' _⟩

@[to_additive]
-/
theorem Nonempty.one_mem_div (h : s.Nonempty) : (1 : α) in s / s :=
  let ⟨a, ha⟩ := h
  mem_div.2 ⟨a, ha, a, ha, div_self' _⟩

@[to_additive]
/--
theorem `isUnit_singleton` / 定理 `isUnit_singleton`

English:
theorem isUnit_singleton
  given: (a : α)
  statement: IsUnit ({a} : Set α)
  proof: (Group.isUnit a).set

@[to_additive (attr := simp)]

中文:
定理 isUnit_singleton
  条件: (a : α)
  结论: 是单位 ({a} : 集合 α)
  证明: (Group.isUnit a).set

@[to_additive (attr := simp)]

Depends on / 依赖: Group.isUnit, isUnit
-/
theorem isUnit_singleton (a : α) : IsUnit ({a} : Set α) :=
  (Group.isUnit a).set

@[to_additive (attr := simp)]
/--
theorem `isUnit_iff_singleton` / 定理 `isUnit_iff_singleton`

English:
theorem isUnit_iff_singleton
  statement: IsUnit s ↔ exists a, s = {a}
  proof: by
  simp only [isUnit_iff, Group.isUnit, and_true]

@[to_additive (attr := simp)]

中文:
定理 isUnit_iff_singleton
  结论: 是单位 s ↔ 存在 a, s = {a}
  证明: by
  simp only [isUnit_iff, Group.isUnit, and_true]

@[to_additive (attr := simp)]

Depends on / 依赖: Group.isUnit, and_true, isUnit, isUnit_iff
-/
theorem isUnit_iff_singleton : IsUnit s ↔ exists a, s = {a} := by
  simp only [isUnit_iff, Group.isUnit, and_true]

@[to_additive (attr := simp)]
/--
theorem `image_mul_left` / 定理 `image_mul_left`

English:
theorem image_mul_left
  statement: (a * ·) '' t = (a⁻¹ * ·) ⁻¹' t
  proof: by
  rw [image_eq_preimage_of_inverse] <;> intro c <;> simp

@[to_additive (attr := simp)]

中文:
定理 image_mul_left
  结论: (a * ·) '' t = (a⁻¹ * ·) ⁻¹' t
  证明: by
  rw [image_eq_preimage_of_inverse] <;> intro c <;> simp

@[to_additive (attr := simp)]

Depends on / 依赖: image_eq_preimage_of_inverse
-/
theorem image_mul_left : (a * ·) '' t = (a⁻¹ * ·) ⁻¹' t := by
  rw [image_eq_preimage_of_inverse] <;> intro c <;> simp

@[to_additive (attr := simp)]
/--
theorem `image_mul_right` / 定理 `image_mul_right`

English:
theorem image_mul_right
  statement: (· * b) '' t = (· * b⁻¹) ⁻¹' t
  proof: by
  rw [image_eq_preimage_of_inverse] <;> intro c <;> simp

@[to_additive]

中文:
定理 image_mul_right
  结论: (· * b) '' t = (· * b⁻¹) ⁻¹' t
  证明: by
  rw [image_eq_preimage_of_inverse] <;> intro c <;> simp

@[to_additive]

Depends on / 依赖: image_eq_preimage_of_inverse
-/
theorem image_mul_right : (· * b) '' t = (· * b⁻¹) ⁻¹' t := by
  rw [image_eq_preimage_of_inverse] <;> intro c <;> simp

@[to_additive]
/--
theorem `image_mul_left'` / 定理 `image_mul_left'`

English:
theorem image_mul_left'
  statement: (a⁻¹ * ·) '' t = (a * ·) ⁻¹' t
  proof: by simp

@[to_additive]

中文:
定理 image_mul_left'
  结论: (a⁻¹ * ·) '' t = (a * ·) ⁻¹' t
  证明: by simp

@[to_additive]
-/
theorem image_mul_left' : (a⁻¹ * ·) '' t = (a * ·) ⁻¹' t := by simp

@[to_additive]
/--
theorem `image_mul_right'` / 定理 `image_mul_right'`

English:
theorem image_mul_right'
  statement: (· * b⁻¹) '' t = (· * b) ⁻¹' t
  proof: by simp

@[to_additive]

中文:
定理 image_mul_right'
  结论: (· * b⁻¹) '' t = (· * b) ⁻¹' t
  证明: by simp

@[to_additive]
-/
theorem image_mul_right' : (· * b⁻¹) '' t = (· * b) ⁻¹' t := by simp

@[to_additive]
/--
theorem `image_div_left` / 定理 `image_div_left`

English:
theorem image_div_left
  statement: (a / ·) '' t = (·⁻¹ * a) ⁻¹' t
  proof: by
  rw [image_eq_preimage_of_inverse] <;> intro c <;> simp

@[to_additive]

中文:
定理 image_div_left
  结论: (a / ·) '' t = (·⁻¹ * a) ⁻¹' t
  证明: by
  rw [image_eq_preimage_of_inverse] <;> intro c <;> simp

@[to_additive]

Depends on / 依赖: image_eq_preimage_of_inverse
-/
theorem image_div_left : (a / ·) '' t = (·⁻¹ * a) ⁻¹' t := by
  rw [image_eq_preimage_of_inverse] <;> intro c <;> simp

@[to_additive]
/--
theorem `image_div_right` / 定理 `image_div_right`

English:
theorem image_div_right
  statement: (· / b) '' t = (· * b) ⁻¹' t
  proof: by
  rw [image_eq_preimage_of_inverse] <;> intro c <;> simp

@[to_additive (attr := simp)]

中文:
定理 image_div_right
  结论: (· / b) '' t = (· * b) ⁻¹' t
  证明: by
  rw [image_eq_preimage_of_inverse] <;> intro c <;> simp

@[to_additive (attr := simp)]

Depends on / 依赖: image_eq_preimage_of_inverse
-/
theorem image_div_right : (· / b) '' t = (· * b) ⁻¹' t := by
  rw [image_eq_preimage_of_inverse] <;> intro c <;> simp

@[to_additive (attr := simp)]
/--
theorem `preimage_mul_left_singleton` / 定理 `preimage_mul_left_singleton`

English:
theorem preimage_mul_left_singleton
  statement: (a * ·) ⁻¹' {b} = {a⁻¹ * b}
  proof: by
  rw [← image_mul_left']; rw [image_singleton]

@[to_additive (attr := simp)]

中文:
定理 preimage_mul_left_singleton
  结论: (a * ·) ⁻¹' {b} = {a⁻¹ * b}
  证明: by
  rw [← image_mul_left']; rw [image_singleton]

@[to_additive (attr := simp)]

Depends on / 依赖: image_mul_left, image_singleton
-/
theorem preimage_mul_left_singleton : (a * ·) ⁻¹' {b} = {a⁻¹ * b} := by
  rw [← image_mul_left']; rw [image_singleton]

@[to_additive (attr := simp)]
/--
theorem `preimage_mul_right_singleton` / 定理 `preimage_mul_right_singleton`

English:
theorem preimage_mul_right_singleton
  statement: (· * a) ⁻¹' {b} = {b * a⁻¹}
  proof: by
  rw [← image_mul_right']; rw [image_singleton]

@[to_additive (attr := simp)]

中文:
定理 preimage_mul_right_singleton
  结论: (· * a) ⁻¹' {b} = {b * a⁻¹}
  证明: by
  rw [← image_mul_right']; rw [image_singleton]

@[to_additive (attr := simp)]

Depends on / 依赖: image_mul_right, image_singleton
-/
theorem preimage_mul_right_singleton : (· * a) ⁻¹' {b} = {b * a⁻¹} := by
  rw [← image_mul_right']; rw [image_singleton]

@[to_additive (attr := simp)]
/--
theorem `preimage_inv_mul_right_singleton` / 定理 `preimage_inv_mul_right_singleton`

English:
theorem preimage_inv_mul_right_singleton
  statement: (·⁻¹ * a) ⁻¹' {b} = {a / b}
  proof: by
  rw [← image_div_left]; rw [image_singleton]

@[to_additive (attr := simp)]

中文:
定理 preimage_inv_mul_right_singleton
  结论: (·⁻¹ * a) ⁻¹' {b} = {a / b}
  证明: by
  rw [← image_div_left]; rw [image_singleton]

@[to_additive (attr := simp)]

Depends on / 依赖: image_div_left, image_singleton
-/
theorem preimage_inv_mul_right_singleton : (·⁻¹ * a) ⁻¹' {b} = {a / b} := by
  rw [← image_div_left]; rw [image_singleton]

@[to_additive (attr := simp)]
/--
theorem `preimage_mul_left_one` / 定理 `preimage_mul_left_one`

English:
theorem preimage_mul_left_one
  statement: (a * ·) ⁻¹' 1 = {a⁻¹}
  proof: by
  rw [← image_mul_left']; rw [image_one]; rw [mul_one]

@[to_additive (attr := simp)]

中文:
定理 preimage_mul_left_one
  结论: (a * ·) ⁻¹' 1 = {a⁻¹}
  证明: by
  rw [← image_mul_left']; rw [image_one]; rw [mul_one]

@[to_additive (attr := simp)]

Depends on / 依赖: image_mul_left, image_one, mul_one
-/
theorem preimage_mul_left_one : (a * ·) ⁻¹' 1 = {a⁻¹} := by
  rw [← image_mul_left']; rw [image_one]; rw [mul_one]

@[to_additive (attr := simp)]
/--
theorem `preimage_mul_right_one` / 定理 `preimage_mul_right_one`

English:
theorem preimage_mul_right_one
  statement: (· * b) ⁻¹' 1 = {b⁻¹}
  proof: by
  rw [← image_mul_right']; rw [image_one]; rw [one_mul]

@[to_additive]

中文:
定理 preimage_mul_right_one
  结论: (· * b) ⁻¹' 1 = {b⁻¹}
  证明: by
  rw [← image_mul_right']; rw [image_one]; rw [one_mul]

@[to_additive]

Depends on / 依赖: image_mul_right, image_one, one_mul
-/
theorem preimage_mul_right_one : (· * b) ⁻¹' 1 = {b⁻¹} := by
  rw [← image_mul_right']; rw [image_one]; rw [one_mul]

@[to_additive]
/--
theorem `preimage_mul_left_one'` / 定理 `preimage_mul_left_one'`

English:
theorem preimage_mul_left_one'
  statement: (a⁻¹ * ·) ⁻¹' 1 = {a}
  proof: by simp

@[to_additive]

中文:
定理 preimage_mul_left_one'
  结论: (a⁻¹ * ·) ⁻¹' 1 = {a}
  证明: by simp

@[to_additive]
-/
theorem preimage_mul_left_one' : (a⁻¹ * ·) ⁻¹' 1 = {a} := by simp

@[to_additive]
/--
theorem `preimage_mul_right_one'` / 定理 `preimage_mul_right_one'`

English:
theorem preimage_mul_right_one'
  statement: (· * b⁻¹) ⁻¹' 1 = {b}
  proof: by simp

@[to_additive (attr := simp)]

中文:
定理 preimage_mul_right_one'
  结论: (· * b⁻¹) ⁻¹' 1 = {b}
  证明: by simp

@[to_additive (attr := simp)]
-/
theorem preimage_mul_right_one' : (· * b⁻¹) ⁻¹' 1 = {b} := by simp

@[to_additive (attr := simp)]
/--
theorem `mul_univ` / 定理 `mul_univ`

English:
theorem mul_univ
  given: (hs : s.Nonempty)
  statement: s * (univ : Set α) = univ
  proof: let ⟨a, ha⟩ := hs
  eq_univ_of_forall fun b => ⟨a, ha, a⁻¹ * b, trivial, mul_inv_cancel_left ..⟩

@[to_additive (attr := simp)]

中文:
定理 mul_univ
  条件: (hs : s.非空)
  结论: s * (univ : 集合 α) = univ
  证明: let ⟨a, ha⟩ := hs
  eq_univ_of_forall fun b => ⟨a, ha, a⁻¹ * b, trivial, mul_inv_cancel_left ..⟩

@[to_additive (attr := simp)]

Depends on / 依赖: eq_univ_of_forall, mul_inv_cancel_left
-/
theorem mul_univ (hs : s.Nonempty) : s * (univ : Set α) = univ :=
  let ⟨a, ha⟩ := hs
  eq_univ_of_forall fun b => ⟨a, ha, a⁻¹ * b, trivial, mul_inv_cancel_left ..⟩

@[to_additive (attr := simp)]
/--
theorem `univ_mul` / 定理 `univ_mul`

English:
theorem univ_mul
  given: (ht : t.Nonempty)
  statement: (univ : Set α) * t = univ
  proof: let ⟨a, ha⟩ := ht
  eq_univ_of_forall fun b => ⟨b * a⁻¹, trivial, a, ha, inv_mul_cancel_right ..⟩

@[to_additive]

中文:
定理 univ_mul
  条件: (ht : t.非空)
  结论: (univ : 集合 α) * t = univ
  证明: let ⟨a, ha⟩ := ht
  eq_univ_of_forall fun b => ⟨b * a⁻¹, trivial, a, ha, inv_mul_cancel_right ..⟩

@[to_additive]

Depends on / 依赖: eq_univ_of_forall, inv_mul_cancel_right
-/
theorem univ_mul (ht : t.Nonempty) : (univ : Set α) * t = univ :=
  let ⟨a, ha⟩ := ht
  eq_univ_of_forall fun b => ⟨b * a⁻¹, trivial, a, ha, inv_mul_cancel_right ..⟩

@[to_additive]
/--
lemma `image_inv` / 引理 `image_inv`

English:
lemma image_inv
  given: [DivisionMonoid β] [FunLike F α β] [MonoidHomClass F α β] (f : F) (s : Set α)
  proof: by
  rw [← image_inv_eq_inv]; rw [← image_inv_eq_inv]; exact image_comm (map_inv _)

中文:
引理 image_inv
  条件: [Division幺半群 β] [函数状 F α β] [幺半群态射类 F α β] (f : F) (s : 集合 α)
  证明: by
  rw [← image_inv_eq_inv]; rw [← image_inv_eq_inv]; exact image_comm (map_inv _)

Depends on / 依赖: image_comm, image_inv_eq_inv, map_inv
-/
lemma image_inv [DivisionMonoid β] [FunLike F α β] [MonoidHomClass F α β] (f : F) (s : Set α) :
    f '' s⁻¹ = (f '' s)⁻¹ := by
  rw [← image_inv_eq_inv]; rw [← image_inv_eq_inv]; exact image_comm (map_inv _)

end Group

section Mul

variable [Mul α] [Mul β] [FunLike F α β] [MulHomClass F α β] (m : F) {s t : Set α}

@[to_additive]
/--
theorem `image_mul` / 定理 `image_mul`

English:
theorem image_mul
  statement: m '' (s * t) = m '' s * m '' t
  proof: image_image2_distrib map_mul m

@[to_additive]

中文:
定理 image_mul
  结论: m '' (s * t) = m '' s * m '' t
  证明: image_image2_distrib map_mul m

@[to_additive]

Depends on / 依赖: image_image2_distrib, map_mul
-/
theorem image_mul : m '' (s * t) = m '' s * m '' t :=
image_image2_distrib map_mul m

@[to_additive]
/--
lemma `mul_subset_range` / 引理 `mul_subset_range`

English:
lemma mul_subset_range
  given: {s t : Set β} (hs : s subseteq range m) (ht : t subseteq range m)
  statement: s * t subseteq range m
  proof: by
  rintro _ ⟨a, ha, b, hb, rfl⟩
  obtain ⟨a, rfl⟩ := hs ha
  obtain ⟨b, rfl⟩ := ht hb
  exact ⟨a * b, map_mul ..⟩

@[to_additive]

中文:
引理 mul_subset_range
  条件: {s t : 集合 β} (hs : s subseteq range m) (ht : t subseteq range m)
  结论: s * t subseteq range m
  证明: by
  rintro _ ⟨a, ha, b, hb, rfl⟩
  obtain ⟨a, rfl⟩ := hs ha
  obtain ⟨b, rfl⟩ := ht hb
  exact ⟨a * b, map_mul ..⟩

@[to_additive]

Depends on / 依赖: Normal, f.ker.Normal, map_mul, normal_ker
-/
lemma mul_subset_range {s t : Set β} (hs : s subseteq range m) (ht : t subseteq range m) : s * t subseteq range m := by
  rintro _ ⟨a, ha, b, hb, rfl⟩
  obtain ⟨a, rfl⟩ := hs ha
  obtain ⟨b, rfl⟩ := ht hb
  exact ⟨a * b, map_mul ..⟩

@[to_additive]
/--
theorem `preimage_mul_preimage_subset` / 定理 `preimage_mul_preimage_subset`

English:
theorem preimage_mul_preimage_subset
  given: {s t : Set β}
  statement: m ⁻¹' s * m ⁻¹' t subseteq m ⁻¹' (s * t)
  proof: by
  rintro _ ⟨_, _, _, _, rfl⟩
  exact ⟨_, ‹_›, _, ‹_›, (map_mul m ..).symm⟩

@[to_additive]

中文:
定理 preimage_mul_preimage_subset
  条件: {s t : 集合 β}
  结论: m ⁻¹' s * m ⁻¹' t subseteq m ⁻¹' (s * t)
  证明: by
  rintro _ ⟨_, _, _, _, rfl⟩
  exact ⟨_, ‹_›, _, ‹_›, (map_mul m ..).symm⟩

@[to_additive]

Depends on / 依赖: map_mul
-/
theorem preimage_mul_preimage_subset {s t : Set β} : m ⁻¹' s * m ⁻¹' t subseteq m ⁻¹' (s * t) := by
  rintro _ ⟨_, _, _, _, rfl⟩
  exact ⟨_, ‹_›, _, ‹_›, (map_mul m ..).symm⟩

@[to_additive]
/--
lemma `preimage_mul` / 引理 `preimage_mul`

English:
lemma preimage_mul
  given: (hm : Injective m) {s t : Set β} (hs : s subseteq range m) (ht : t subseteq range m)
  proof: hm.image_injective by
    rw [image_mul]; rw [image_preimage_eq_iff.2 hs]; rw [image_preimage_eq_iff.2 ht]; rw [image_preimage_eq_iff.2 (mul_subset_range m hs ht)]

中文:
引理 preimage_mul
  条件: (hm : 单射 m) {s t : 集合 β} (hs : s subseteq range m) (ht : t subseteq range m)
  证明: hm.image_injective by
    rw [image_mul]; rw [image_preimage_eq_iff.2 hs]; rw [image_preimage_eq_iff.2 ht]; rw [image_preimage_eq_iff.2 (mul_subset_range m hs ht)]

Depends on / 依赖: hm.image_injective, image_injective, image_mul, image_preimage_eq_iff, mul_subset_range
-/
lemma preimage_mul (hm : Injective m) {s t : Set β} (hs : s subseteq range m) (ht : t subseteq range m) :
    m ⁻¹' (s * t) = m ⁻¹' s * m ⁻¹' t :=
hm.image_injective by
    rw [image_mul]; rw [image_preimage_eq_iff.2 hs]; rw [image_preimage_eq_iff.2 ht]; rw [image_preimage_eq_iff.2 (mul_subset_range m hs ht)]

end Mul

section Monoid
variable [Monoid α] [Monoid β] [FunLike F α β]

@[to_additive]
/--
lemma `image_pow_of_ne_zero` / 引理 `image_pow_of_ne_zero`

English:
lemma image_pow_of_ne_zero
  given: [MulHomClass F α β]

中文:
引理 image_pow_of_ne_zero
  条件: [乘法态射类 F α β]
-/
lemma image_pow_of_ne_zero [MulHomClass F α β] :
    forall {n}, n != 0 -> forall (f : F) (s : Set α), f '' (s ^ n) = (f '' s) ^ n
  | 1, _ => by simp
  | n + 2, _ => by simp [image_mul, pow_succ _ n.succ, image_pow_of_ne_zero]

@[to_additive]
/--
lemma `image_pow` / 引理 `image_pow`

English:
lemma image_pow
  given: [MonoidHomClass F α β] (f : F) (s : Set α)
  statement: forall n, f '' (s ^ n) = (f '' s) ^ n

中文:
引理 image_pow
  条件: [幺半群态射类 F α β] (f : F) (s : 集合 α)
  结论: 对任意 n, f '' (s ^ n) = (f '' s) ^ n
-/
lemma image_pow [MonoidHomClass F α β] (f : F) (s : Set α) : forall n, f '' (s ^ n) = (f '' s) ^ n
  | 0 => by simp [singleton_one]
  | n + 1 => image_pow_of_ne_zero n.succ_ne_zero ..

@[to_additive]
/--
lemma `preimage_pow_subset` / 引理 `preimage_pow_subset`

English:
lemma preimage_pow_subset
  given: [MonoidHomClass F α β] (f : F) (s : Set β)

中文:
引理 preimage_pow_subset
  条件: [幺半群态射类 F α β] (f : F) (s : 集合 β)
-/
lemma preimage_pow_subset [MonoidHomClass F α β] (f : F) (s : Set β) :
    forall n, (f ⁻¹' s) ^ n subseteq f ⁻¹' (s ^ n)
  | 0 => by simp [Set.subset_def]
  | n + 1 => by simpa [pow_succ] using Subset.trans (mul_subset_mul_right
    (preimage_pow_subset f s n)) (preimage_mul_preimage_subset f)

end Monoid

section Group

variable [Group α] [DivisionMonoid β] [FunLike F α β] [MonoidHomClass F α β] (m : F) {s t : Set α}

@[to_additive]
/--
theorem `image_div` / 定理 `image_div`

English:
theorem image_div
  statement: m '' (s / t) = m '' s / m '' t
  proof: image_image2_distrib map_div m

@[to_additive]

中文:
定理 image_div
  结论: m '' (s / t) = m '' s / m '' t
  证明: image_image2_distrib map_div m

@[to_additive]

Depends on / 依赖: image_image2_distrib, map_div
-/
theorem image_div : m '' (s / t) = m '' s / m '' t :=
image_image2_distrib map_div m

@[to_additive]
/--
lemma `div_subset_range` / 引理 `div_subset_range`

English:
lemma div_subset_range
  given: {s t : Set β} (hs : s subseteq range m) (ht : t subseteq range m)
  statement: s / t subseteq range m
  proof: by
  rintro _ ⟨a, ha, b, hb, rfl⟩
  obtain ⟨a, rfl⟩ := hs ha
  obtain ⟨b, rfl⟩ := ht hb
  exact ⟨a / b, map_div ..⟩

@[to_additive]

中文:
引理 div_subset_range
  条件: {s t : 集合 β} (hs : s subseteq range m) (ht : t subseteq range m)
  结论: s / t subseteq range m
  证明: by
  rintro _ ⟨a, ha, b, hb, rfl⟩
  obtain ⟨a, rfl⟩ := hs ha
  obtain ⟨b, rfl⟩ := ht hb
  exact ⟨a / b, map_div ..⟩

@[to_additive]

Depends on / 依赖: map_div
-/
lemma div_subset_range {s t : Set β} (hs : s subseteq range m) (ht : t subseteq range m) : s / t subseteq range m := by
  rintro _ ⟨a, ha, b, hb, rfl⟩
  obtain ⟨a, rfl⟩ := hs ha
  obtain ⟨b, rfl⟩ := ht hb
  exact ⟨a / b, map_div ..⟩

@[to_additive]
/--
theorem `preimage_div_preimage_subset` / 定理 `preimage_div_preimage_subset`

English:
theorem preimage_div_preimage_subset
  given: {s t : Set β}
  statement: m ⁻¹' s / m ⁻¹' t subseteq m ⁻¹' (s / t)
  proof: by
  rintro _ ⟨_, _, _, _, rfl⟩
  exact ⟨_, ‹_›, _, ‹_›, (map_div m ..).symm⟩

@[to_additive]

中文:
定理 preimage_div_preimage_subset
  条件: {s t : 集合 β}
  结论: m ⁻¹' s / m ⁻¹' t subseteq m ⁻¹' (s / t)
  证明: by
  rintro _ ⟨_, _, _, _, rfl⟩
  exact ⟨_, ‹_›, _, ‹_›, (map_div m ..).symm⟩

@[to_additive]

Depends on / 依赖: map_div
-/
theorem preimage_div_preimage_subset {s t : Set β} : m ⁻¹' s / m ⁻¹' t subseteq m ⁻¹' (s / t) := by
  rintro _ ⟨_, _, _, _, rfl⟩
  exact ⟨_, ‹_›, _, ‹_›, (map_div m ..).symm⟩

@[to_additive]
/--
lemma `preimage_div` / 引理 `preimage_div`

English:
lemma preimage_div
  given: (hm : Injective m) {s t : Set β} (hs : s subseteq range m) (ht : t subseteq range m)
  proof: hm.image_injective by
    rw [image_div]; rw [image_preimage_eq_iff.2 hs]; rw [image_preimage_eq_iff.2 ht]; rw [image_preimage_eq_iff.2 (div_subset_range m hs ht)]

中文:
引理 preimage_div
  条件: (hm : 单射 m) {s t : 集合 β} (hs : s subseteq range m) (ht : t subseteq range m)
  证明: hm.image_injective by
    rw [image_div]; rw [image_preimage_eq_iff.2 hs]; rw [image_preimage_eq_iff.2 ht]; rw [image_preimage_eq_iff.2 (div_subset_range m hs ht)]

Depends on / 依赖: div_subset_range, hm.image_injective, image_div, image_injective, image_preimage_eq_iff
-/
lemma preimage_div (hm : Injective m) {s t : Set β} (hs : s subseteq range m) (ht : t subseteq range m) :
    m ⁻¹' (s / t) = m ⁻¹' s / m ⁻¹' t :=
hm.image_injective by
    rw [image_div]; rw [image_preimage_eq_iff.2 hs]; rw [image_preimage_eq_iff.2 ht]; rw [image_preimage_eq_iff.2 (div_subset_range m hs ht)]

end Group

section Pi

variable {ι : Type*} {α : ι -> Type*} [forall i, Inv (α i)]

@[to_additive (attr := simp)]
/--
lemma `inv_pi` / 引理 `inv_pi`

English:
lemma inv_pi
  given: (s : Set ι) (t : forall i, Set (α i))
  statement: (s.pi t)⁻¹ = s.pi fun i => (t i)⁻¹
  proof: by ext x; simp

中文:
引理 inv_pi
  条件: (s : 集合 ι) (t : 对任意 i, 集合 (α i))
  结论: (s.pi t)⁻¹ = s.pi fun i => (t i)⁻¹
  证明: by ext x; simp
-/
lemma inv_pi (s : Set ι) (t : forall i, Set (α i)) : (s.pi t)⁻¹ = s.pi fun i => (t i)⁻¹ := by ext x; simp

end Pi

section Pointwise

open scoped Pointwise

@[to_additive]
/--
lemma `MapsTo.mul` / 引理 `MapsTo.mul`

English:
lemma MapsTo.mul
  statement: [Mul β] {A : Set α} {B₁ B₂ : Set β} {f₁ f₂ : α -> β}
  proof: fun _ h => mul_mem_mul (h₁ h) (h₂ h)

@[to_additive]

中文:
引理 映射到.mul
  结论: [乘法 β] {A : 集合 α} {B₁ B₂ : 集合 β} {f₁ f₂ : α -> β}
  证明: fun _ h => mul_mem_mul (h₁ h) (h₂ h)

@[to_additive]

Depends on / 依赖: mul_mem_mul
-/
lemma MapsTo.mul [Mul β] {A : Set α} {B₁ B₂ : Set β} {f₁ f₂ : α -> β}
    (h₁ : MapsTo f₁ A B₁) (h₂ : MapsTo f₂ A B₂) : MapsTo (f₁ * f₂) A (B₁ * B₂) :=
  fun _ h => mul_mem_mul (h₁ h) (h₂ h)

@[to_additive]
/--
lemma `MapsTo.inv` / 引理 `MapsTo.inv`

English:
lemma MapsTo.inv
  given: [InvolutiveInv β] {A : Set α} {B : Set β} {f : α -> β} (h : MapsTo f A B)
  proof: fun _ ha => inv_mem_inv.2 (h ha)


@[to_additive]

中文:
引理 映射到.inv
  条件: [InvolutiveInv β] {A : 集合 α} {B : 集合 β} {f : α -> β} (h : 映射到 f A B)
  证明: fun _ ha => inv_mem_inv.2 (h ha)


@[to_additive]

Depends on / 依赖: inv_mem_inv
-/
lemma MapsTo.inv [InvolutiveInv β] {A : Set α} {B : Set β} {f : α -> β} (h : MapsTo f A B) :
    MapsTo (f⁻¹) A (B⁻¹) :=
  fun _ ha => inv_mem_inv.2 (h ha)


@[to_additive]
/--
lemma `MapsTo.div` / 引理 `MapsTo.div`

English:
lemma MapsTo.div
  statement: [Div β] {A : Set α} {B₁ B₂ : Set β} {f₁ f₂ : α -> β}
  proof: fun _ ha => div_mem_div (h₁ ha) (h₂ ha)

中文:
引理 映射到.div
  结论: [除法 β] {A : 集合 α} {B₁ B₂ : 集合 β} {f₁ f₂ : α -> β}
  证明: fun _ ha => div_mem_div (h₁ ha) (h₂ ha)

Depends on / 依赖: div_mem_div
-/
lemma MapsTo.div [Div β] {A : Set α} {B₁ B₂ : Set β} {f₁ f₂ : α -> β}
    (h₁ : MapsTo f₁ A B₁) (h₂ : MapsTo f₂ A B₂) : MapsTo (f₁ / f₂) A (B₁ / B₂) :=
  fun _ ha => div_mem_div (h₁ ha) (h₂ ha)

end Pointwise

end Set
