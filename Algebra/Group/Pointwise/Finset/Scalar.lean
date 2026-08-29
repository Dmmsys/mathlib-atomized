/-
Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Yaël Dillies
-/
module

public import Mathlib.Data.Finset.NAry
public import Mathlib.Algebra.Group.Pointwise.Set.Finite

/-!
# Pointwise operations of finsets

This file defines pointwise algebraic operations on finsets.

## Main declarations

For finsets `s` and `t`:

* `s +ᵥ t` (`Finset.vadd`): Scalar addition, finset of all `x +ᵥ y` where `x ∈ s` and `y ∈ t`.
* `s • t` (`Finset.smul`): Scalar multiplication, finset of all `x • y` where `x ∈ s` and
  `y ∈ t`.
* `s -ᵥ t` (`Finset.vsub`): Scalar subtraction, finset of all `x -ᵥ y` where `x ∈ s` and
  `y ∈ t`.
* `a • s` (`Finset.smulFinset`): Scaling, finset of all `a • x` where `x ∈ s`.
* `a +ᵥ s` (`Finset.vaddFinset`): Translation, finset of all `a +ᵥ x` where `x ∈ s`.

For `α` a semigroup/monoid, `Finset α` is a semigroup/monoid.
As an unfortunate side effect, this means that `n • s`, where `n : ℕ`, is ambiguous between
pointwise scaling and repeated pointwise addition; the former has `(2 : ℕ) • {1, 2} = {2, 4}`, while
the latter has `(2 : ℕ) • {1, 2} = {2, 3, 4}`. See note [pointwise nat action].

## Implementation notes

We put all instances in the scope `Pointwise`, so that these instances are not available by
default. Note that we do not mark them as reducible (as argued by note [reducible non-instances])
since we expect the scope to be open whenever the instances are actually used (and making the
instances reducible changes the behavior of `simp`).

## Tags

finset multiplication, finset addition, pointwise addition, pointwise multiplication,
pointwise subtraction
-/

@[expose] public section

assert_not_exists Cardinal Finset.dens MonoidWithZero MulAction IsOrderedMonoid

open Function MulOpposite

open scoped Pointwise

variable {F α β γ : Type*}

namespace Finset

open scoped Pointwise

/-! ### Scalar addition/multiplication of finsets -/

section SMul
variable [DecidableEq β] [SMul α β] {s s₁ s₂ : Finset α} {t t₁ t₂ u : Finset β} {a : α} {b : β}

/-- The pointwise product of two finsets `s` and `t`: `s • t = {x • y | x ∈ s, y ∈ t}`. -/
@[to_additive (attr := instance_reducible)
/-- The pointwise sum of two finsets `s` and `t`: `s +ᵥ t = {x +ᵥ y | x ∈ s, y ∈ t}`. -/]
/--
Definition of `smul` / `smul` 的定义

English:
definition smul
  signature: : SMul (Finset α) (Finset β)
  body: ⟨image₂ (· • ·)⟩

scoped[Pointwise] attribute [instance] Finset.smul Finset.vadd

中文:
定义 smul
  签名: : SMul (Finset α) (Finset β)
  定义体: ⟨image₂ (· • ·)⟩

scoped[Pointwise] attribute [instance] Finset.smul Finset.vadd
-/
protected def smul : SMul (Finset α) (Finset β) := ⟨image₂ (· • ·)⟩

scoped[Pointwise] attribute [instance] Finset.smul Finset.vadd

/--
lemma `smul_def` / 引理 `smul_def`

English:
lemma smul_def
  statement: s • t = (s ×ˢ t).image fun p : α × β => p.1 • p.2
  proof: rfl

@[to_additive]

中文:
引理 smul_def
  结论: s • t = (s ×ˢ t).image fun p : α × β => p.1 • p.2
  证明: rfl

@[to_additive]
-/
@[to_additive] lemma smul_def : s • t = (s ×ˢ t).image fun p : α × β => p.1 • p.2 := rfl

@[to_additive]
/--
lemma `image_smul_product` / 引理 `image_smul_product`

English:
lemma image_smul_product
  statement: ((s ×ˢ t).image fun x : α × β => x.fst • x.snd) = s • t
  proof: rfl

中文:
引理 image_smul_product
  结论: ((s ×ˢ t).image fun x : α × β => x.fst • x.snd) = s • t
  证明: rfl
-/
lemma image_smul_product : ((s ×ˢ t).image fun x : α × β => x.fst • x.snd) = s • t := rfl

/--
lemma `mem_smul` / 引理 `mem_smul`

English:
lemma mem_smul
  given: {x : β}
  statement: x in s • t ↔ exists y in s, exists z in t, y • z = x
  proof: mem_image₂

@[to_additive (attr := simp, norm_cast)]

中文:
引理 mem_smul
  条件: {x : β}
  结论: x in s • t ↔ 存在 y in s, 存在 z in t, y • z = x
  证明: mem_image₂

@[to_additive (attr := simp, norm_cast)]
-/
@[to_additive] lemma mem_smul {x : β} : x in s • t ↔ exists y in s, exists z in t, y • z = x := mem_image₂

@[to_additive (attr := simp, norm_cast)]
/--
lemma `coe_smul` / 引理 `coe_smul`

English:
lemma coe_smul
  given: (s : Finset α) (t : Finset β)
  statement: ↑(s • t) = (s : Set α) • (t : Set β)
  proof: coe_image₂ ..

中文:
引理 coe_smul
  条件: (s : Finset α) (t : Finset β)
  结论: ↑(s • t) = (s : Set α) • (t : Set β)
  证明: coe_image₂ ..
-/
lemma coe_smul (s : Finset α) (t : Finset β) : ↑(s • t) = (s : Set α) • (t : Set β) := coe_image₂ ..

/--
lemma `smul_mem_smul` / 引理 `smul_mem_smul`

English:
lemma smul_mem_smul
  statement: a in s -> b in t -> a • b in s • t
  proof: mem_image₂_of_mem

中文:
引理 smul_mem_smul
  结论: a in s -> b in t -> a • b in s • t
  证明: mem_image₂_of_mem
-/
@[to_additive] lemma smul_mem_smul : a in s -> b in t -> a • b in s • t := mem_image₂_of_mem

/--
lemma `card_smul_le` / 引理 `card_smul_le`

English:
lemma card_smul_le
  statement: #(s • t) <= #s * #t
  proof: card_image₂_le ..

@[to_additive (attr := simp)]

中文:
引理 card_smul_le
  结论: #(s • t) <= #s * #t
  证明: card_image₂_le ..

@[to_additive (attr := simp)]
-/
@[to_additive] lemma card_smul_le : #(s • t) <= #s * #t := card_image₂_le ..

@[to_additive (attr := simp)]
/--
lemma `empty_smul` / 引理 `empty_smul`

English:
lemma empty_smul
  given: (t : Finset β)
  statement: (∅ : Finset α) • t = ∅
  proof: image₂_empty_left

@[to_additive (attr := simp)]

中文:
引理 empty_smul
  条件: (t : Finset β)
  结论: (∅ : Finset α) • t = ∅
  证明: image₂_empty_left

@[to_additive (attr := simp)]
-/
lemma empty_smul (t : Finset β) : (∅ : Finset α) • t = ∅ := image₂_empty_left

@[to_additive (attr := simp)]
/--
lemma `smul_empty` / 引理 `smul_empty`

English:
lemma smul_empty
  given: (s : Finset α)
  statement: s • (∅ : Finset β) = ∅
  proof: image₂_empty_right

@[to_additive (attr := simp)]

中文:
引理 smul_empty
  条件: (s : Finset α)
  结论: s • (∅ : Finset β) = ∅
  证明: image₂_empty_right

@[to_additive (attr := simp)]
-/
lemma smul_empty (s : Finset α) : s • (∅ : Finset β) = ∅ := image₂_empty_right

@[to_additive (attr := simp)]
/--
lemma `smul_eq_empty` / 引理 `smul_eq_empty`

English:
lemma smul_eq_empty
  statement: s • t = ∅ ↔ s = ∅ ∨ t = ∅
  proof: image₂_eq_empty_iff

@[to_additive (attr := simp)]

中文:
引理 smul_eq_empty
  结论: s • t = ∅ ↔ s = ∅ ∨ t = ∅
  证明: image₂_eq_empty_iff

@[to_additive (attr := simp)]
-/
lemma smul_eq_empty : s • t = ∅ ↔ s = ∅ ∨ t = ∅ := image₂_eq_empty_iff

@[to_additive (attr := simp)]
/--
lemma `smul_nonempty_iff` / 引理 `smul_nonempty_iff`

English:
lemma smul_nonempty_iff
  statement: (s • t).Nonempty ↔ s.Nonempty ∧ t.Nonempty
  proof: image₂_nonempty_iff

@[to_additive (attr := aesop safe apply (rule_sets := [finsetNonempty]))]

中文:
引理 smul_nonempty_iff
  结论: (s • t).Nonempty ↔ s.Nonempty ∧ t.Nonempty
  证明: image₂_nonempty_iff

@[to_additive (attr := aesop safe apply (rule_sets := [finsetNonempty]))]
-/
lemma smul_nonempty_iff : (s • t).Nonempty ↔ s.Nonempty ∧ t.Nonempty := image₂_nonempty_iff

@[to_additive (attr := aesop safe apply (rule_sets := [finsetNonempty]))]
/--
lemma `Nonempty.smul` / 引理 `Nonempty.smul`

English:
lemma Nonempty.smul
  statement: s.Nonempty -> t.Nonempty -> (s • t).Nonempty
  proof: .image₂

中文:
引理 Nonempty.smul
  结论: s.Nonempty -> t.Nonempty -> (s • t).Nonempty
  证明: .image₂
-/
lemma Nonempty.smul : s.Nonempty -> t.Nonempty -> (s • t).Nonempty := .image₂

/--
lemma `Nonempty.of_smul_left` / 引理 `Nonempty.of_smul_left`

English:
lemma Nonempty.of_smul_left
  statement: (s • t).Nonempty -> s.Nonempty
  proof: .of_image₂_left

中文:
引理 Nonempty.of_smul_left
  结论: (s • t).Nonempty -> s.Nonempty
  证明: .of_image₂_left
-/
@[to_additive] lemma Nonempty.of_smul_left : (s • t).Nonempty -> s.Nonempty := .of_image₂_left
/--
lemma `Nonempty.of_smul_right` / 引理 `Nonempty.of_smul_right`

English:
lemma Nonempty.of_smul_right
  statement: (s • t).Nonempty -> t.Nonempty
  proof: .of_image₂_right

@[to_additive]

中文:
引理 Nonempty.of_smul_right
  结论: (s • t).Nonempty -> t.Nonempty
  证明: .of_image₂_right

@[to_additive]
-/
@[to_additive] lemma Nonempty.of_smul_right : (s • t).Nonempty -> t.Nonempty := .of_image₂_right

@[to_additive]
/--
lemma `smul_singleton` / 引理 `smul_singleton`

English:
lemma smul_singleton
  given: (b : β)
  statement: s • ({b} : Finset β) = s.image (· • b)
  proof: image₂_singleton_right

@[to_additive]

中文:
引理 smul_singleton
  条件: (b : β)
  结论: s • ({b} : Finset β) = s.image (· • b)
  证明: image₂_singleton_right

@[to_additive]
-/
lemma smul_singleton (b : β) : s • ({b} : Finset β) = s.image (· • b) := image₂_singleton_right

@[to_additive]
/--
lemma `singleton_smul_singleton` / 引理 `singleton_smul_singleton`

English:
lemma singleton_smul_singleton
  given: (a : α) (b : β)
  statement: ({a} : Finset α) • ({b} : Finset β) = {a • b}
  proof: image₂_singleton

@[to_additive (attr := mono, gcongr)]

中文:
引理 singleton_smul_singleton
  条件: (a : α) (b : β)
  结论: ({a} : Finset α) • ({b} : Finset β) = {a • b}
  证明: image₂_singleton

@[to_additive (attr := mono, gcongr)]
-/
lemma singleton_smul_singleton (a : α) (b : β) : ({a} : Finset α) • ({b} : Finset β) = {a • b} :=
  image₂_singleton

@[to_additive (attr := mono, gcongr)]
/--
lemma `smul_subset_smul` / 引理 `smul_subset_smul`

English:
lemma smul_subset_smul
  statement: s₁ subseteq s₂ -> t₁ subseteq t₂ -> s₁ • t₁ subseteq s₂ • t₂
  proof: image₂_subset

中文:
引理 smul_subset_smul
  结论: s₁ subseteq s₂ -> t₁ subseteq t₂ -> s₁ • t₁ subseteq s₂ • t₂
  证明: image₂_subset
-/
lemma smul_subset_smul : s₁ subseteq s₂ -> t₁ subseteq t₂ -> s₁ • t₁ subseteq s₂ • t₂ := image₂_subset

/--
lemma `smul_subset_smul_left` / 引理 `smul_subset_smul_left`

English:
lemma smul_subset_smul_left
  statement: t₁ subseteq t₂ -> s • t₁ subseteq s • t₂
  proof: image₂_subset_left

中文:
引理 smul_subset_smul_left
  结论: t₁ subseteq t₂ -> s • t₁ subseteq s • t₂
  证明: image₂_subset_left
-/
@[to_additive] lemma smul_subset_smul_left : t₁ subseteq t₂ -> s • t₁ subseteq s • t₂ := image₂_subset_left
/--
lemma `smul_subset_smul_right` / 引理 `smul_subset_smul_right`

English:
lemma smul_subset_smul_right
  statement: s₁ subseteq s₂ -> s₁ • t subseteq s₂ • t
  proof: image₂_subset_right

中文:
引理 smul_subset_smul_right
  结论: s₁ subseteq s₂ -> s₁ • t subseteq s₂ • t
  证明: image₂_subset_right
-/
@[to_additive] lemma smul_subset_smul_right : s₁ subseteq s₂ -> s₁ • t subseteq s₂ • t := image₂_subset_right
/--
lemma `smul_subset_iff` / 引理 `smul_subset_iff`

English:
lemma smul_subset_iff
  statement: s • t subseteq u ↔ forall a in s, forall b in t, a • b in u
  proof: image₂_subset_iff

@[to_additive]

中文:
引理 smul_subset_iff
  结论: s • t subseteq u ↔ 对任意 a in s, 对任意 b in t, a • b in u
  证明: image₂_subset_iff

@[to_additive]
-/
@[to_additive] lemma smul_subset_iff : s • t subseteq u ↔ forall a in s, forall b in t, a • b in u := image₂_subset_iff

@[to_additive]
/--
lemma `union_smul` / 引理 `union_smul`

English:
lemma union_smul
  given: [DecidableEq α]
  statement: (s₁ union s₂) • t = s₁ • t union s₂ • t
  proof: image₂_union_left

@[to_additive]

中文:
引理 union_smul
  条件: [DecidableEq α]
  结论: (s₁ union s₂) • t = s₁ • t union s₂ • t
  证明: image₂_union_left

@[to_additive]
-/
lemma union_smul [DecidableEq α] : (s₁ union s₂) • t = s₁ • t union s₂ • t := image₂_union_left

@[to_additive]
/--
lemma `smul_union` / 引理 `smul_union`

English:
lemma smul_union
  statement: s • (t₁ union t₂) = s • t₁ union s • t₂
  proof: image₂_union_right

@[to_additive]

中文:
引理 smul_union
  结论: s • (t₁ union t₂) = s • t₁ union s • t₂
  证明: image₂_union_right

@[to_additive]
-/
lemma smul_union : s • (t₁ union t₂) = s • t₁ union s • t₂ := image₂_union_right

@[to_additive]
/--
lemma `inter_smul_subset` / 引理 `inter_smul_subset`

English:
lemma inter_smul_subset
  given: [DecidableEq α]
  statement: (s₁ inter s₂) • t subseteq s₁ • t inter s₂ • t
  proof: image₂_inter_subset_left

@[to_additive]

中文:
引理 inter_smul_subset
  条件: [DecidableEq α]
  结论: (s₁ inter s₂) • t subseteq s₁ • t inter s₂ • t
  证明: image₂_inter_subset_left

@[to_additive]
-/
lemma inter_smul_subset [DecidableEq α] : (s₁ inter s₂) • t subseteq s₁ • t inter s₂ • t :=
  image₂_inter_subset_left

@[to_additive]
/--
lemma `smul_inter_subset` / 引理 `smul_inter_subset`

English:
lemma smul_inter_subset
  statement: s • (t₁ inter t₂) subseteq s • t₁ inter s • t₂
  proof: image₂_inter_subset_right

@[to_additive]

中文:
引理 smul_inter_subset
  结论: s • (t₁ inter t₂) subseteq s • t₁ inter s • t₂
  证明: image₂_inter_subset_right

@[to_additive]
-/
lemma smul_inter_subset : s • (t₁ inter t₂) subseteq s • t₁ inter s • t₂ := image₂_inter_subset_right

@[to_additive]
/--
lemma `inter_smul_union_subset_union` / 引理 `inter_smul_union_subset_union`

English:
lemma inter_smul_union_subset_union
  given: [DecidableEq α]
  statement: (s₁ inter s₂) • (t₁ union t₂) subseteq s₁ • t₁ union s₂ • t₂
  proof: image₂_inter_union_subset_union

@[to_additive]

中文:
引理 inter_smul_union_subset_union
  条件: [DecidableEq α]
  结论: (s₁ inter s₂) • (t₁ union t₂) subseteq s₁ • t₁ union s₂ • t₂
  证明: image₂_inter_union_subset_union

@[to_additive]
-/
lemma inter_smul_union_subset_union [DecidableEq α] : (s₁ inter s₂) • (t₁ union t₂) subseteq s₁ • t₁ union s₂ • t₂ :=
  image₂_inter_union_subset_union

@[to_additive]
/--
lemma `union_smul_inter_subset_union` / 引理 `union_smul_inter_subset_union`

English:
lemma union_smul_inter_subset_union
  given: [DecidableEq α]
  statement: (s₁ union s₂) • (t₁ inter t₂) subseteq s₁ • t₁ union s₂ • t₂
  proof: image₂_union_inter_subset_union

中文:
引理 union_smul_inter_subset_union
  条件: [DecidableEq α]
  结论: (s₁ union s₂) • (t₁ inter t₂) subseteq s₁ • t₁ union s₂ • t₂
  证明: image₂_union_inter_subset_union
-/
lemma union_smul_inter_subset_union [DecidableEq α] : (s₁ union s₂) • (t₁ inter t₂) subseteq s₁ • t₁ union s₂ • t₂ :=
  image₂_union_inter_subset_union

/-- If a finset `u` is contained in the scalar product of two sets `s • t`, we can find two finsets
`s'`, `t'` such that `s' ⊆ s`, `t' ⊆ t` and `u ⊆ s' • t'`. -/
@[to_additive
/-- If a finset `u` is contained in the scalar sum of two sets `s +ᵥ t`, we can find two
finsets `s'`, `t'` such that `s' ⊆ s`, `t' ⊆ t` and `u ⊆ s' +ᵥ t'`. -/]
/--
lemma `subset_smul` / 引理 `subset_smul`

English:
lemma subset_smul
  given: {s : Set α} {t : Set β}
  proof: subset_set_image₂

中文:
引理 subset_smul
  条件: {s : Set α} {t : Set β}
  证明: subset_set_image₂
-/
lemma subset_smul {s : Set α} {t : Set β} :
    ↑u subseteq s • t -> exists (s' : Finset α) (t' : Finset β), ↑s' subseteq s ∧ ↑t' subseteq t ∧ u subseteq s' • t' :=
  subset_set_image₂

end SMul

/-! ### Translation/scaling of finsets -/

section SMul
variable [DecidableEq β] [SMul α β] {s s₁ s₂ t : Finset β} {a : α} {b : β}

/-- The scaling of a finset `s` by a scalar `a`: `a • s = {a • x | x ∈ s}`. -/
@[to_additive (attr := instance_reducible)
  /-- The translation of a finset `s` by a vector `a`: `a +ᵥ s = {a +ᵥ x | x ∈ s}`. -/]
/--
Definition of `smulFinset` / `smulFinset` 的定义

English:
definition smulFinset
  signature: : SMul α (Finset β) where smul a
  body: image (a • ·)

scoped[Pointwise] attribute [instance] Finset.smulFinset Finset.vaddFinset

中文:
定义 smulFinset
  签名: : SMul α (Finset β) where smul a
  定义体: image (a • ·)

scoped[Pointwise] attribute [instance] Finset.smulFinset Finset.vaddFinset
-/
protected def smulFinset : SMul α (Finset β) where smul a := image (a • ·)

scoped[Pointwise] attribute [instance] Finset.smulFinset Finset.vaddFinset

/--
lemma `smul_finset_def` / 引理 `smul_finset_def`

English:
lemma smul_finset_def
  statement: a • s = s.image (a • ·)
  proof: rfl

中文:
引理 smul_finset_def
  结论: a • s = s.image (a • ·)
  证明: rfl
-/
@[to_additive] lemma smul_finset_def : a • s = s.image (a • ·) := rfl

/--
lemma `image_smul` / 引理 `image_smul`

English:
lemma image_smul
  statement: s.image (a • ·) = a • s
  proof: rfl

@[to_additive]

中文:
引理 image_smul
  结论: s.image (a • ·) = a • s
  证明: rfl

@[to_additive]
-/
@[to_additive] lemma image_smul : s.image (a • ·) = a • s := rfl

@[to_additive]
/--
lemma `mem_smul_finset` / 引理 `mem_smul_finset`

English:
lemma mem_smul_finset
  given: {x : β}
  statement: x in a • s ↔ exists y, y in s ∧ a • y = x
  proof: by
  simp only [Finset.smul_finset_def, mem_image]

@[to_additive (attr := simp, norm_cast)]

中文:
引理 mem_smul_finset
  条件: {x : β}
  结论: x in a • s ↔ 存在 y, y in s ∧ a • y = x
  证明: by
  simp only [Finset.smul_finset_def, mem_image]

@[to_additive (attr := simp, norm_cast)]

Depends on / 依赖: Finset, Finset.smul_finset_def, mem_image, smul_finset_def
-/
lemma mem_smul_finset {x : β} : x in a • s ↔ exists y, y in s ∧ a • y = x := by
  simp only [Finset.smul_finset_def, mem_image]

@[to_additive (attr := simp, norm_cast)]
/--
lemma `coe_smul_finset` / 引理 `coe_smul_finset`

English:
lemma coe_smul_finset
  given: (a : α) (s : Finset β)
  statement: ↑(a • s) = a • (↑s : Set β)
  proof: coe_image

中文:
引理 coe_smul_finset
  条件: (a : α) (s : Finset β)
  结论: ↑(a • s) = a • (↑s : Set β)
  证明: coe_image

Depends on / 依赖: coe_image
-/
lemma coe_smul_finset (a : α) (s : Finset β) : ↑(a • s) = a • (↑s : Set β) := coe_image

/--
lemma `smul_mem_smul_finset` / 引理 `smul_mem_smul_finset`

English:
lemma smul_mem_smul_finset
  statement: b in s -> a • b in a • s
  proof: mem_image_of_mem _

中文:
引理 smul_mem_smul_finset
  结论: b in s -> a • b in a • s
  证明: mem_image_of_mem _
-/
@[to_additive] lemma smul_mem_smul_finset : b in s -> a • b in a • s := mem_image_of_mem _

/--
lemma `card_smul_finset_le` / 引理 `card_smul_finset_le`

English:
lemma card_smul_finset_le
  statement: #(a • s) <= #s
  proof: card_image_le
@[deprecated (since := "2026-04-16")] alias smul_finset_card_le := card_smul_finset_le
@[deprecated (since := "2026-04-16")] alias vadd_finset_card_le := card_vadd_finset_le

@[to_additive (attr := simp)]

中文:
引理 card_smul_finset_le
  结论: #(a • s) <= #s
  证明: card_image_le
@[deprecated (since := "2026-04-16")] alias smul_finset_card_le := card_smul_finset_le
@[deprecated (since := "2026-04-16")] alias vadd_finset_card_le := card_vadd_finset_le

@[to_additive (attr := simp)]

Depends on / 依赖: H.Normal, Normal, Subgroup, normal_comap
-/
@[to_additive] lemma card_smul_finset_le : #(a • s) <= #s := card_image_le
@[deprecated (since := "2026-04-16")] alias smul_finset_card_le := card_smul_finset_le
@[deprecated (since := "2026-04-16")] alias vadd_finset_card_le := card_vadd_finset_le

@[to_additive (attr := simp)]
/--
lemma `smul_finset_empty` / 引理 `smul_finset_empty`

English:
lemma smul_finset_empty
  given: (a : α)
  statement: a • (∅ : Finset β) = ∅
  proof: rfl

@[to_additive (attr := simp)]

中文:
引理 smul_finset_empty
  条件: (a : α)
  结论: a • (∅ : Finset β) = ∅
  证明: rfl

@[to_additive (attr := simp)]
-/
lemma smul_finset_empty (a : α) : a • (∅ : Finset β) = ∅ := rfl

@[to_additive (attr := simp)]
/--
lemma `smul_finset_eq_empty` / 引理 `smul_finset_eq_empty`

English:
lemma smul_finset_eq_empty
  statement: a • s = ∅ ↔ s = ∅
  proof: image_eq_empty

@[to_additive (attr := simp)]

中文:
引理 smul_finset_eq_empty
  结论: a • s = ∅ ↔ s = ∅
  证明: image_eq_empty

@[to_additive (attr := simp)]

Depends on / 依赖: N.Normal, Normal, Subgroup, image_eq_empty, normal_subgroupOf
-/
lemma smul_finset_eq_empty : a • s = ∅ ↔ s = ∅ := image_eq_empty

@[to_additive (attr := simp)]
/--
lemma `smul_finset_nonempty` / 引理 `smul_finset_nonempty`

English:
lemma smul_finset_nonempty
  statement: (a • s).Nonempty ↔ s.Nonempty
  proof: image_nonempty

@[to_additive (attr := aesop safe apply (rule_sets := [finsetNonempty]))]

中文:
引理 smul_finset_nonempty
  结论: (a • s).Nonempty ↔ s.Nonempty
  证明: image_nonempty

@[to_additive (attr := aesop safe apply (rule_sets := [finsetNonempty]))]

Depends on / 依赖: image_nonempty
-/
lemma smul_finset_nonempty : (a • s).Nonempty ↔ s.Nonempty := image_nonempty

@[to_additive (attr := aesop safe apply (rule_sets := [finsetNonempty]))]
/--
lemma `Nonempty.smul_finset` / 引理 `Nonempty.smul_finset`

English:
lemma Nonempty.smul_finset
  given: (hs : s.Nonempty)
  statement: (a • s).Nonempty
  proof: hs.image _

@[to_additive (attr := simp)]

中文:
引理 Nonempty.smul_finset
  条件: (hs : s.Nonempty)
  结论: (a • s).Nonempty
  证明: hs.image _

@[to_additive (attr := simp)]

Depends on / 依赖: hs.image
-/
lemma Nonempty.smul_finset (hs : s.Nonempty) : (a • s).Nonempty :=
  hs.image _

@[to_additive (attr := simp)]
/--
lemma `singleton_smul` / 引理 `singleton_smul`

English:
lemma singleton_smul
  given: (a : α)
  statement: ({a} : Finset α) • t = a • t
  proof: image₂_singleton_left

@[to_additive (attr := mono, gcongr)]

中文:
引理 singleton_smul
  条件: (a : α)
  结论: ({a} : Finset α) • t = a • t
  证明: image₂_singleton_left

@[to_additive (attr := mono, gcongr)]
-/
lemma singleton_smul (a : α) : ({a} : Finset α) • t = a • t := image₂_singleton_left

@[to_additive (attr := mono, gcongr)]
/--
lemma `smul_finset_subset_smul_finset` / 引理 `smul_finset_subset_smul_finset`

English:
lemma smul_finset_subset_smul_finset
  statement: s subseteq t -> a • s subseteq a • t
  proof: image_subset_image

@[to_additive (attr := simp)]

中文:
引理 smul_finset_subset_smul_finset
  结论: s subseteq t -> a • s subseteq a • t
  证明: image_subset_image

@[to_additive (attr := simp)]

Depends on / 依赖: image_subset_image
-/
lemma smul_finset_subset_smul_finset : s subseteq t -> a • s subseteq a • t := image_subset_image

@[to_additive (attr := simp)]
/--
lemma `smul_finset_singleton` / 引理 `smul_finset_singleton`

English:
lemma smul_finset_singleton
  given: (b : β)
  statement: a • ({b} : Finset β) = {a • b}
  proof: image_singleton ..

@[to_additive]

中文:
引理 smul_finset_singleton
  条件: (b : β)
  结论: a • ({b} : Finset β) = {a • b}
  证明: image_singleton ..

@[to_additive]

Depends on / 依赖: image_singleton
-/
lemma smul_finset_singleton (b : β) : a • ({b} : Finset β) = {a • b} := image_singleton ..

@[to_additive]
/--
lemma `smul_finset_union` / 引理 `smul_finset_union`

English:
lemma smul_finset_union
  statement: a • (s₁ union s₂) = a • s₁ union a • s₂
  proof: image_union _ _

@[to_additive]

中文:
引理 smul_finset_union
  结论: a • (s₁ union s₂) = a • s₁ union a • s₂
  证明: image_union _ _

@[to_additive]

Depends on / 依赖: image_union
-/
lemma smul_finset_union : a • (s₁ union s₂) = a • s₁ union a • s₂ := image_union _ _

@[to_additive]
/--
lemma `smul_finset_insert` / 引理 `smul_finset_insert`

English:
lemma smul_finset_insert
  given: (a : α) (b : β) (s : Finset β)
  statement: a • insert b s = insert (a • b) (a • s)
  proof: image_insert ..

@[to_additive]

中文:
引理 smul_finset_insert
  条件: (a : α) (b : β) (s : Finset β)
  结论: a • insert b s = insert (a • b) (a • s)
  证明: image_insert ..

@[to_additive]

Depends on / 依赖: image_insert
-/
lemma smul_finset_insert (a : α) (b : β) (s : Finset β) : a • insert b s = insert (a • b) (a • s) :=
  image_insert ..

@[to_additive]
/--
lemma `smul_finset_inter_subset` / 引理 `smul_finset_inter_subset`

English:
lemma smul_finset_inter_subset
  statement: a • (s₁ inter s₂) subseteq a • s₁ inter a • s₂
  proof: image_inter_subset _ _ _

@[to_additive]

中文:
引理 smul_finset_inter_subset
  结论: a • (s₁ inter s₂) subseteq a • s₁ inter a • s₂
  证明: image_inter_subset _ _ _

@[to_additive]

Depends on / 依赖: image_inter_subset
-/
lemma smul_finset_inter_subset : a • (s₁ inter s₂) subseteq a • s₁ inter a • s₂ := image_inter_subset _ _ _

@[to_additive]
/--
lemma `smul_finset_subset_smul` / 引理 `smul_finset_subset_smul`

English:
lemma smul_finset_subset_smul
  given: {s : Finset α}
  statement: a in s -> a • t subseteq s • t
  proof: image_subset_image₂_right

@[to_additive (attr := simp)]

中文:
引理 smul_finset_subset_smul
  条件: {s : Finset α}
  结论: a in s -> a • t subseteq s • t
  证明: image_subset_image₂_right

@[to_additive (attr := simp)]
-/
lemma smul_finset_subset_smul {s : Finset α} : a in s -> a • t subseteq s • t := image_subset_image₂_right

@[to_additive (attr := simp)]
/--
lemma `biUnion_smul_finset` / 引理 `biUnion_smul_finset`

English:
lemma biUnion_smul_finset
  given: (s : Finset α) (t : Finset β)
  statement: s.biUnion (· • t) = s • t
  proof: biUnion_image_left

中文:
引理 biUnion_smul_finset
  条件: (s : Finset α) (t : Finset β)
  结论: s.biUnion (· • t) = s • t
  证明: biUnion_image_left

Depends on / 依赖: biUnion_image_left
-/
lemma biUnion_smul_finset (s : Finset α) (t : Finset β) : s.biUnion (· • t) = s • t :=
  biUnion_image_left

end SMul

open scoped Pointwise

/-! ### Instances -/

open scoped Pointwise

/-! ### Scalar subtraction of finsets -/

section VSub

variable [VSub α β] [DecidableEq α] {s s₁ s₂ t t₁ t₂ : Finset β} {u : Finset α} {a : α} {b c : β}

/-- The pointwise subtraction of two finsets `s` and `t`: `s -ᵥ t = {x -ᵥ y | x ∈ s, y ∈ t}`. -/
@[instance_reducible]
/--
Definition of `vsub` / `vsub` 的定义

English:
definition vsub
  signature: : VSub (Finset α) (Finset β)
  body: ⟨image₂ (· -ᵥ ·)⟩

scoped[Pointwise] attribute [instance] Finset.vsub

中文:
定义 vsub
  签名: : VSub (Finset α) (Finset β)
  定义体: ⟨image₂ (· -ᵥ ·)⟩

scoped[Pointwise] attribute [instance] Finset.vsub
-/
protected def vsub : VSub (Finset α) (Finset β) :=
  ⟨image₂ (· -ᵥ ·)⟩

scoped[Pointwise] attribute [instance] Finset.vsub

/--
theorem `vsub_def` / 定理 `vsub_def`

English:
theorem vsub_def
  statement: s -ᵥ t = image₂ (· -ᵥ ·) s t
  proof: rfl

@[simp]

中文:
定理 vsub_def
  结论: s -ᵥ t = image₂ (· -ᵥ ·) s t
  证明: rfl

@[simp]
-/
theorem vsub_def : s -ᵥ t = image₂ (· -ᵥ ·) s t :=
  rfl

@[simp]
/--
theorem `image_vsub_product` / 定理 `image_vsub_product`

English:
theorem image_vsub_product
  statement: image₂ (· -ᵥ ·) s t = s -ᵥ t
  proof: rfl

中文:
定理 image_vsub_product
  结论: image₂ (· -ᵥ ·) s t = s -ᵥ t
  证明: rfl
-/
theorem image_vsub_product : image₂ (· -ᵥ ·) s t = s -ᵥ t :=
  rfl

/--
theorem `mem_vsub` / 定理 `mem_vsub`

English:
theorem mem_vsub
  statement: a in s -ᵥ t ↔ exists b in s, exists c in t, b -ᵥ c = a
  proof: mem_image₂

@[simp, norm_cast]

中文:
定理 mem_vsub
  结论: a in s -ᵥ t ↔ 存在 b in s, 存在 c in t, b -ᵥ c = a
  证明: mem_image₂

@[simp, norm_cast]
-/
theorem mem_vsub : a in s -ᵥ t ↔ exists b in s, exists c in t, b -ᵥ c = a :=
  mem_image₂

@[simp, norm_cast]
/--
theorem `coe_vsub` / 定理 `coe_vsub`

English:
theorem coe_vsub
  given: (s t : Finset β)
  statement: (↑(s -ᵥ t) : Set α) = (s : Set β) -ᵥ t
  proof: coe_image₂ _ _ _

中文:
定理 coe_vsub
  条件: (s t : Finset β)
  结论: (↑(s -ᵥ t) : Set α) = (s : Set β) -ᵥ t
  证明: coe_image₂ _ _ _
-/
theorem coe_vsub (s t : Finset β) : (↑(s -ᵥ t) : Set α) = (s : Set β) -ᵥ t :=
  coe_image₂ _ _ _

/--
theorem `vsub_mem_vsub` / 定理 `vsub_mem_vsub`

English:
theorem vsub_mem_vsub
  statement: b in s -> c in t -> b -ᵥ c in s -ᵥ t
  proof: mem_image₂_of_mem

中文:
定理 vsub_mem_vsub
  结论: b in s -> c in t -> b -ᵥ c in s -ᵥ t
  证明: mem_image₂_of_mem
-/
theorem vsub_mem_vsub : b in s -> c in t -> b -ᵥ c in s -ᵥ t :=
  mem_image₂_of_mem

/--
theorem `vsub_card_le` / 定理 `vsub_card_le`

English:
theorem vsub_card_le
  statement: #(s -ᵥ t : Finset α) <= #s * #t
  proof: card_image₂_le _ _ _

@[simp]

中文:
定理 vsub_card_le
  结论: #(s -ᵥ t : Finset α) <= #s * #t
  证明: card_image₂_le _ _ _

@[simp]
-/
theorem vsub_card_le : #(s -ᵥ t : Finset α) <= #s * #t :=
  card_image₂_le _ _ _

@[simp]
/--
theorem `empty_vsub` / 定理 `empty_vsub`

English:
theorem empty_vsub
  given: (t : Finset β)
  statement: (∅ : Finset β) -ᵥ t = ∅
  proof: image₂_empty_left

@[simp]

中文:
定理 empty_vsub
  条件: (t : Finset β)
  结论: (∅ : Finset β) -ᵥ t = ∅
  证明: image₂_empty_left

@[simp]
-/
theorem empty_vsub (t : Finset β) : (∅ : Finset β) -ᵥ t = ∅ :=
  image₂_empty_left

@[simp]
/--
theorem `vsub_empty` / 定理 `vsub_empty`

English:
theorem vsub_empty
  given: (s : Finset β)
  statement: s -ᵥ (∅ : Finset β) = ∅
  proof: image₂_empty_right

@[simp]

中文:
定理 vsub_empty
  条件: (s : Finset β)
  结论: s -ᵥ (∅ : Finset β) = ∅
  证明: image₂_empty_right

@[simp]
-/
theorem vsub_empty (s : Finset β) : s -ᵥ (∅ : Finset β) = ∅ :=
  image₂_empty_right

@[simp]
/--
theorem `vsub_eq_empty` / 定理 `vsub_eq_empty`

English:
theorem vsub_eq_empty
  statement: s -ᵥ t = ∅ ↔ s = ∅ ∨ t = ∅
  proof: image₂_eq_empty_iff

@[simp]

中文:
定理 vsub_eq_empty
  结论: s -ᵥ t = ∅ ↔ s = ∅ ∨ t = ∅
  证明: image₂_eq_empty_iff

@[simp]
-/
theorem vsub_eq_empty : s -ᵥ t = ∅ ↔ s = ∅ ∨ t = ∅ :=
  image₂_eq_empty_iff

@[simp]
/--
theorem `vsub_nonempty` / 定理 `vsub_nonempty`

English:
theorem vsub_nonempty
  statement: (s -ᵥ t : Finset α).Nonempty ↔ s.Nonempty ∧ t.Nonempty
  proof: image₂_nonempty_iff

@[aesop safe apply (rule_sets := [finsetNonempty])]

中文:
定理 vsub_nonempty
  结论: (s -ᵥ t : Finset α).Nonempty ↔ s.Nonempty ∧ t.Nonempty
  证明: image₂_nonempty_iff

@[aesop safe apply (rule_sets := [finsetNonempty])]
-/
theorem vsub_nonempty : (s -ᵥ t : Finset α).Nonempty ↔ s.Nonempty ∧ t.Nonempty :=
  image₂_nonempty_iff

@[aesop safe apply (rule_sets := [finsetNonempty])]
/--
theorem `Nonempty.vsub` / 定理 `Nonempty.vsub`

English:
theorem Nonempty.vsub
  statement: s.Nonempty -> t.Nonempty -> (s -ᵥ t : Finset α).Nonempty
  proof: Nonempty.image₂

中文:
定理 Nonempty.vsub
  结论: s.Nonempty -> t.Nonempty -> (s -ᵥ t : Finset α).Nonempty
  证明: Nonempty.image₂

Depends on / 依赖: Nonempty, Nonempty.image
-/
theorem Nonempty.vsub : s.Nonempty -> t.Nonempty -> (s -ᵥ t : Finset α).Nonempty :=
  Nonempty.image₂

/--
theorem `Nonempty.of_vsub_left` / 定理 `Nonempty.of_vsub_left`

English:
theorem Nonempty.of_vsub_left
  statement: (s -ᵥ t : Finset α).Nonempty -> s.Nonempty
  proof: Nonempty.of_image₂_left

中文:
定理 Nonempty.of_vsub_left
  结论: (s -ᵥ t : Finset α).Nonempty -> s.Nonempty
  证明: Nonempty.of_image₂_left

Depends on / 依赖: Nonempty, Nonempty.of_image
-/
theorem Nonempty.of_vsub_left : (s -ᵥ t : Finset α).Nonempty -> s.Nonempty :=
  Nonempty.of_image₂_left

/--
theorem `Nonempty.of_vsub_right` / 定理 `Nonempty.of_vsub_right`

English:
theorem Nonempty.of_vsub_right
  statement: (s -ᵥ t : Finset α).Nonempty -> t.Nonempty
  proof: Nonempty.of_image₂_right

@[simp]

中文:
定理 Nonempty.of_vsub_right
  结论: (s -ᵥ t : Finset α).Nonempty -> t.Nonempty
  证明: Nonempty.of_image₂_right

@[simp]

Depends on / 依赖: Nonempty, Nonempty.of_image
-/
theorem Nonempty.of_vsub_right : (s -ᵥ t : Finset α).Nonempty -> t.Nonempty :=
  Nonempty.of_image₂_right

@[simp]
/--
theorem `vsub_singleton` / 定理 `vsub_singleton`

English:
theorem vsub_singleton
  given: (b : β)
  statement: s -ᵥ ({b} : Finset β) = s.image (· -ᵥ b)
  proof: image₂_singleton_right

中文:
定理 vsub_singleton
  条件: (b : β)
  结论: s -ᵥ ({b} : Finset β) = s.image (· -ᵥ b)
  证明: image₂_singleton_right
-/
theorem vsub_singleton (b : β) : s -ᵥ ({b} : Finset β) = s.image (· -ᵥ b) :=
  image₂_singleton_right

/--
theorem `singleton_vsub` / 定理 `singleton_vsub`

English:
theorem singleton_vsub
  given: (a : β)
  statement: ({a} : Finset β) -ᵥ t = t.image (a -ᵥ ·)
  proof: image₂_singleton_left

中文:
定理 singleton_vsub
  条件: (a : β)
  结论: ({a} : Finset β) -ᵥ t = t.image (a -ᵥ ·)
  证明: image₂_singleton_left
-/
theorem singleton_vsub (a : β) : ({a} : Finset β) -ᵥ t = t.image (a -ᵥ ·) :=
  image₂_singleton_left

/--
theorem `singleton_vsub_singleton` / 定理 `singleton_vsub_singleton`

English:
theorem singleton_vsub_singleton
  given: (a b : β)
  statement: ({a} : Finset β) -ᵥ {b} = {a -ᵥ b}
  proof: image₂_singleton

@[mono, gcongr]

中文:
定理 singleton_vsub_singleton
  条件: (a b : β)
  结论: ({a} : Finset β) -ᵥ {b} = {a -ᵥ b}
  证明: image₂_singleton

@[mono, gcongr]
-/
theorem singleton_vsub_singleton (a b : β) : ({a} : Finset β) -ᵥ {b} = {a -ᵥ b} :=
  image₂_singleton

@[mono, gcongr]
/--
theorem `vsub_subset_vsub` / 定理 `vsub_subset_vsub`

English:
theorem vsub_subset_vsub
  statement: s₁ subseteq s₂ -> t₁ subseteq t₂ -> s₁ -ᵥ t₁ subseteq s₂ -ᵥ t₂
  proof: image₂_subset

中文:
定理 vsub_subset_vsub
  结论: s₁ subseteq s₂ -> t₁ subseteq t₂ -> s₁ -ᵥ t₁ subseteq s₂ -ᵥ t₂
  证明: image₂_subset
-/
theorem vsub_subset_vsub : s₁ subseteq s₂ -> t₁ subseteq t₂ -> s₁ -ᵥ t₁ subseteq s₂ -ᵥ t₂ :=
  image₂_subset

/--
theorem `vsub_subset_vsub_left` / 定理 `vsub_subset_vsub_left`

English:
theorem vsub_subset_vsub_left
  statement: t₁ subseteq t₂ -> s -ᵥ t₁ subseteq s -ᵥ t₂
  proof: image₂_subset_left

中文:
定理 vsub_subset_vsub_left
  结论: t₁ subseteq t₂ -> s -ᵥ t₁ subseteq s -ᵥ t₂
  证明: image₂_subset_left
-/
theorem vsub_subset_vsub_left : t₁ subseteq t₂ -> s -ᵥ t₁ subseteq s -ᵥ t₂ :=
  image₂_subset_left

/--
theorem `vsub_subset_vsub_right` / 定理 `vsub_subset_vsub_right`

English:
theorem vsub_subset_vsub_right
  statement: s₁ subseteq s₂ -> s₁ -ᵥ t subseteq s₂ -ᵥ t
  proof: image₂_subset_right

中文:
定理 vsub_subset_vsub_right
  结论: s₁ subseteq s₂ -> s₁ -ᵥ t subseteq s₂ -ᵥ t
  证明: image₂_subset_right
-/
theorem vsub_subset_vsub_right : s₁ subseteq s₂ -> s₁ -ᵥ t subseteq s₂ -ᵥ t :=
  image₂_subset_right

/--
theorem `vsub_subset_iff` / 定理 `vsub_subset_iff`

English:
theorem vsub_subset_iff
  statement: s -ᵥ t subseteq u ↔ forall x in s, forall y in t, x -ᵥ y in u
  proof: image₂_subset_iff

中文:
定理 vsub_subset_iff
  结论: s -ᵥ t subseteq u ↔ 对任意 x in s, 对任意 y in t, x -ᵥ y in u
  证明: image₂_subset_iff
-/
theorem vsub_subset_iff : s -ᵥ t subseteq u ↔ forall x in s, forall y in t, x -ᵥ y in u :=
  image₂_subset_iff

section

variable [DecidableEq β]

/--
theorem `union_vsub` / 定理 `union_vsub`

English:
theorem union_vsub
  statement: s₁ union s₂ -ᵥ t = s₁ -ᵥ t union (s₂ -ᵥ t)
  proof: image₂_union_left

中文:
定理 union_vsub
  结论: s₁ union s₂ -ᵥ t = s₁ -ᵥ t union (s₂ -ᵥ t)
  证明: image₂_union_left
-/
theorem union_vsub : s₁ union s₂ -ᵥ t = s₁ -ᵥ t union (s₂ -ᵥ t) :=
  image₂_union_left

/--
theorem `vsub_union` / 定理 `vsub_union`

English:
theorem vsub_union
  statement: s -ᵥ (t₁ union t₂) = s -ᵥ t₁ union (s -ᵥ t₂)
  proof: image₂_union_right

中文:
定理 vsub_union
  结论: s -ᵥ (t₁ union t₂) = s -ᵥ t₁ union (s -ᵥ t₂)
  证明: image₂_union_right
-/
theorem vsub_union : s -ᵥ (t₁ union t₂) = s -ᵥ t₁ union (s -ᵥ t₂) :=
  image₂_union_right

/--
theorem `inter_vsub_subset` / 定理 `inter_vsub_subset`

English:
theorem inter_vsub_subset
  statement: s₁ inter s₂ -ᵥ t subseteq (s₁ -ᵥ t) inter (s₂ -ᵥ t)
  proof: image₂_inter_subset_left

中文:
定理 inter_vsub_subset
  结论: s₁ inter s₂ -ᵥ t subseteq (s₁ -ᵥ t) inter (s₂ -ᵥ t)
  证明: image₂_inter_subset_left
-/
theorem inter_vsub_subset : s₁ inter s₂ -ᵥ t subseteq (s₁ -ᵥ t) inter (s₂ -ᵥ t) :=
  image₂_inter_subset_left

/--
theorem `vsub_inter_subset` / 定理 `vsub_inter_subset`

English:
theorem vsub_inter_subset
  statement: s -ᵥ t₁ inter t₂ subseteq (s -ᵥ t₁) inter (s -ᵥ t₂)
  proof: image₂_inter_subset_right

中文:
定理 vsub_inter_subset
  结论: s -ᵥ t₁ inter t₂ subseteq (s -ᵥ t₁) inter (s -ᵥ t₂)
  证明: image₂_inter_subset_right
-/
theorem vsub_inter_subset : s -ᵥ t₁ inter t₂ subseteq (s -ᵥ t₁) inter (s -ᵥ t₂) :=
  image₂_inter_subset_right

end

/--
theorem `subset_vsub` / 定理 `subset_vsub`

English:
theorem subset_vsub
  given: {s t : Set β}
  proof: subset_set_image₂

中文:
定理 subset_vsub
  条件: {s t : Set β}
  证明: subset_set_image₂
-/
theorem subset_vsub {s t : Set β} :
    ↑u subseteq s -ᵥ t -> exists s' t' : Finset β, ↑s' subseteq s ∧ ↑t' subseteq t ∧ u subseteq s' -ᵥ t' :=
  subset_set_image₂

end VSub

section SMul

variable [DecidableEq β] [DecidableEq γ] [SMul αᵐᵒᵖ β] [SMul β γ] [SMul α γ]

-- TODO: replace hypothesis and conclusion with a typeclass
@[to_additive]
/--
theorem `op_smul_finset_smul_eq_smul_smul_finset` / 定理 `op_smul_finset_smul_eq_smul_smul_finset`

English:
theorem op_smul_finset_smul_eq_smul_smul_finset
  statement: (a : α) (s : Finset β) (t : Finset γ)
  proof: by
  ext
  simp [mem_smul, mem_smul_finset, h]

中文:
定理 op_smul_finset_smul_eq_smul_smul_finset
  结论: (a : α) (s : Finset β) (t : Finset γ)
  证明: by
  ext
  simp [mem_smul, mem_smul_finset, h]

Depends on / 依赖: mem_smul, mem_smul_finset
-/
theorem op_smul_finset_smul_eq_smul_smul_finset (a : α) (s : Finset β) (t : Finset γ)
    (h : forall (a : α) (b : β) (c : γ), (op a • b) • c = b • a • c) : (op a • s) • t = s • a • t := by
  ext
  simp [mem_smul, mem_smul_finset, h]

end SMul

@[to_additive]
/--
theorem `image_smul_comm` / 定理 `image_smul_comm`

English:
theorem image_smul_comm
  statement: [DecidableEq β] [DecidableEq γ] [SMul α β] [SMul α γ] (f : β -> γ) (a : α)
  proof: image_comm

中文:
定理 image_smul_comm
  结论: [DecidableEq β] [DecidableEq γ] [SMul α β] [SMul α γ] (f : β -> γ) (a : α)
  证明: image_comm

Depends on / 依赖: image_comm
-/
theorem image_smul_comm [DecidableEq β] [DecidableEq γ] [SMul α β] [SMul α γ] (f : β -> γ) (a : α)
    (s : Finset β) : (forall b, f (a • b) = a • f b) -> (a • s).image f = a • s.image f :=
  image_comm

end Finset

open scoped Pointwise

namespace Set

section SMul

variable [SMul α β] [DecidableEq β] {s : Set α} {t : Set β}

@[to_additive (attr := simp)]
/--
theorem `toFinset_smul` / 定理 `toFinset_smul`

English:
theorem toFinset_smul
  given: (s : Set α) (t : Set β) [Fintype s] [Fintype t] [Fintype ↑(s • t)]
  proof: toFinset_image2 _ _ _

@[to_additive]

中文:
定理 toFinset_smul
  条件: (s : Set α) (t : Set β) [Fintype s] [Fintype t] [Fintype ↑(s • t)]
  证明: toFinset_image2 _ _ _

@[to_additive]

Depends on / 依赖: toFinset_image2
-/
theorem toFinset_smul (s : Set α) (t : Set β) [Fintype s] [Fintype t] [Fintype ↑(s • t)] :
    (s • t).toFinset = s.toFinset • t.toFinset :=
  toFinset_image2 _ _ _

@[to_additive]
/--
theorem `Finite.toFinset_smul` / 定理 `Finite.toFinset_smul`

English:
theorem Finite.toFinset_smul
  given: (hs : s.Finite) (ht : t.Finite) (hf := hs.smul ht)
  proof: Finite.toFinset_image2 _ _ _

中文:
定理 Finite.toFinset_smul
  条件: (hs : s.Finite) (ht : t.Finite) (hf := hs.smul ht)
  证明: Finite.toFinset_image2 _ _ _

Depends on / 依赖: hs.smul
-/
theorem Finite.toFinset_smul (hs : s.Finite) (ht : t.Finite) (hf := hs.smul ht) :
    hf.toFinset = hs.toFinset • ht.toFinset :=
  Finite.toFinset_image2 _ _ _

end SMul

section SMul

variable [DecidableEq β] [SMul α β] {a : α} {s : Set β}

@[to_additive (attr := simp)]
/--
theorem `toFinset_smul_set` / 定理 `toFinset_smul_set`

English:
theorem toFinset_smul_set
  given: (a : α) (s : Set β) [Fintype s] [Fintype ↑(a • s)]
  proof: toFinset_image _ _

@[to_additive]

中文:
定理 toFinset_smul_set
  条件: (a : α) (s : Set β) [Fintype s] [Fintype ↑(a • s)]
  证明: toFinset_image _ _

@[to_additive]

Depends on / 依赖: toFinset_image
-/
theorem toFinset_smul_set (a : α) (s : Set β) [Fintype s] [Fintype ↑(a • s)] :
    (a • s).toFinset = a • s.toFinset :=
  toFinset_image _ _

@[to_additive]
/--
theorem `Finite.toFinset_smul_set` / 定理 `Finite.toFinset_smul_set`

English:
theorem Finite.toFinset_smul_set
  given: (hs : s.Finite) (hf : (a • s).Finite := hs.smul_set)
  proof: Finite.toFinset_image _ _ _

中文:
定理 Finite.toFinset_smul_set
  条件: (hs : s.Finite) (hf : (a • s).Finite := hs.smul_set)
  证明: Finite.toFinset_image _ _ _

Depends on / 依赖: fast_instance, hs.smul_set, smul_set, toGroup
-/
theorem Finite.toFinset_smul_set (hs : s.Finite) (hf : (a • s).Finite := hs.smul_set) :
    hf.toFinset = a • hs.toFinset :=
  Finite.toFinset_image _ _ _

end SMul

section VSub

variable [DecidableEq α] [VSub α β] {s t : Set β}

@[simp]
/--
theorem `toFinset_vsub` / 定理 `toFinset_vsub`

English:
theorem toFinset_vsub
  given: (s t : Set β) [Fintype s] [Fintype t] [Fintype ↑(s -ᵥ t)]
  proof: toFinset_image2 _ _ _

中文:
定理 toFinset_vsub
  条件: (s t : Set β) [Fintype s] [Fintype t] [Fintype ↑(s -ᵥ t)]
  证明: toFinset_image2 _ _ _

Depends on / 依赖: CommGroup, SetLike, SubgroupClass, toCommGroup, toFinset_image2
-/
theorem toFinset_vsub (s t : Set β) [Fintype s] [Fintype t] [Fintype ↑(s -ᵥ t)] :
    (s -ᵥ t : Set α).toFinset = s.toFinset -ᵥ t.toFinset :=
  toFinset_image2 _ _ _

/--
theorem `Finite.toFinset_vsub` / 定理 `Finite.toFinset_vsub`

English:
theorem Finite.toFinset_vsub
  given: (hs : s.Finite) (ht : t.Finite) (hf := hs.vsub ht)
  proof: Finite.toFinset_image2 _ _ _

中文:
定理 Finite.toFinset_vsub
  条件: (hs : s.Finite) (ht : t.Finite) (hf := hs.vsub ht)
  证明: Finite.toFinset_image2 _ _ _

Depends on / 依赖: hs.vsub
-/
theorem Finite.toFinset_vsub (hs : s.Finite) (ht : t.Finite) (hf := hs.vsub ht) :
    hf.toFinset = hs.toFinset -ᵥ ht.toFinset :=
  Finite.toFinset_image2 _ _ _

end VSub

end Set
