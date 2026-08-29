/-
Copyright (c) 2021 Christopher Hoskin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Hoskin, Yaël Dillies
-/
module

public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Algebra.Notation

/-!
# Positive & negative parts

Mathematical structures possessing an absolute value often also possess a unique decomposition of
elements into "positive" and "negative" parts which are in some sense "disjoint" (e.g. the Jordan
decomposition of a measure).

This file provides instances of `PosPart` and `NegPart`, the positive and negative parts of an
element in a lattice ordered group.

## Main statements

* `posPart_sub_negPart`: Every element `a` can be decomposed into `a⁺ - a⁻`, the difference of its
  positive and negative parts.
* `posPart_inf_negPart_eq_zero`: The positive and negative parts are coprime.

## References

* [Birkhoff, Lattice-ordered Groups][birkhoff1942]
* [Bourbaki, Algebra II][bourbaki1981]
* [Fuchs, Partially Ordered Algebraic Systems][fuchs1963]
* [Zaanen, Lectures on "Riesz Spaces"][zaanen1966]
* [Banasiak, Banach Lattices in Applications][banasiak]

## Tags

positive part, negative part
-/

@[expose] public section

open Function

variable {α : Type*}

section Lattice
variable [Lattice α]

section DivInvMonoid
variable [DivInvMonoid α] {a b : α}

/-- The *positive part* of an element `a` in a lattice ordered group is `a ⊔ 1`, denoted `a⁺ᵐ`. -/
@[to_additive
/-- The *positive part* of an element `a` in a lattice ordered group is `a ⊔ 0`, denoted `a⁺`. -/]
/--
Instance `instOneLePart` / 实例 `instOneLePart`

English:
instance instOneLePart
  signature: : OneLePart α where
  body: a ⊔ 1

中文:
实例 instOneLePart
  签名: : OneLePart α where
  定义体: a ⊔ 1
-/
instance instOneLePart : OneLePart α where
  oneLePart a := a ⊔ 1

/-- The *negative part* of an element `a` in a lattice ordered group is `a⁻¹ ⊔ 1`, denoted `a⁻ᵐ `.
-/
@[to_additive
/-- The *negative part* of an element `a` in a lattice ordered group is `(-a) ⊔ 0`, denoted `a⁻`.
-/]
/--
Instance `instLeOnePart` / 实例 `instLeOnePart`

English:
instance instLeOnePart
  signature: : LeOnePart α where
  body: a⁻¹ ⊔ 1

中文:
实例 instLeOnePart
  签名: : LeOnePart α where
  定义体: a⁻¹ ⊔ 1
-/
instance instLeOnePart : LeOnePart α where
  leOnePart a := a⁻¹ ⊔ 1

/--
lemma `leOnePart_def` / 引理 `leOnePart_def`

English:
lemma leOnePart_def
  given: (a : α)
  statement: a⁻ᵐ = a⁻¹ ⊔ 1
  proof: rfl

中文:
引理 leOnePart_def
  条件: (a : α)
  结论: a⁻ᵐ = a⁻¹ ⊔ 1
  证明: rfl
-/
@[to_additive] lemma leOnePart_def (a : α) : a⁻ᵐ = a⁻¹ ⊔ 1 := rfl

/--
lemma `oneLePart_def` / 引理 `oneLePart_def`

English:
lemma oneLePart_def
  given: (a : α)
  statement: a⁺ᵐ = a ⊔ 1
  proof: rfl

中文:
引理 oneLePart_def
  条件: (a : α)
  结论: a⁺ᵐ = a ⊔ 1
  证明: rfl
-/
@[to_additive] lemma oneLePart_def (a : α) : a⁺ᵐ = a ⊔ 1 := rfl

/--
lemma `oneLePart_mono` / 引理 `oneLePart_mono`

English:
lemma oneLePart_mono
  statement: Monotone (·⁺ᵐ : α -> α)
  proof: fun _a _b hab => sup_le_sup_right hab _

中文:
引理 oneLePart_mono
  结论: Monotone (·⁺ᵐ : α -> α)
  证明: fun _a _b hab => sup_le_sup_right hab _
-/
@[to_additive] lemma oneLePart_mono : Monotone (·⁺ᵐ : α -> α) :=
  fun _a _b hab => sup_le_sup_right hab _

/--
lemma `oneLePart_one` / 引理 `oneLePart_one`

English:
lemma oneLePart_one
  statement: (1 : α)⁺ᵐ = 1
  proof: sup_idem _

@[to_additive (attr := simp) posPart_nonneg]

中文:
引理 oneLePart_one
  结论: (1 : α)⁺ᵐ = 1
  证明: sup_idem _

@[to_additive (attr := simp) posPart_nonneg]
-/
@[to_additive (attr := simp high)] lemma oneLePart_one : (1 : α)⁺ᵐ = 1 := sup_idem _

@[to_additive (attr := simp) posPart_nonneg]
/--
lemma `one_le_oneLePart` / 引理 `one_le_oneLePart`

English:
lemma one_le_oneLePart
  given: (a : α)
  statement: 1 <= a⁺ᵐ
  proof: le_sup_right

@[to_additive (attr := simp) negPart_nonneg]

中文:
引理 one_le_oneLePart
  条件: (a : α)
  结论: 1 <= a⁺ᵐ
  证明: le_sup_right

@[to_additive (attr := simp) negPart_nonneg]

Depends on / 依赖: le_sup_right
-/
lemma one_le_oneLePart (a : α) : 1 <= a⁺ᵐ := le_sup_right

@[to_additive (attr := simp) negPart_nonneg]
/--
lemma `one_le_leOnePart` / 引理 `one_le_leOnePart`

English:
lemma one_le_leOnePart
  given: (a : α)
  statement: 1 <= a⁻ᵐ
  proof: le_sup_right

中文:
引理 one_le_leOnePart
  条件: (a : α)
  结论: 1 <= a⁻ᵐ
  证明: le_sup_right

Depends on / 依赖: le_sup_right
-/
lemma one_le_leOnePart (a : α) : 1 <= a⁻ᵐ := le_sup_right

-- TODO: `to_additive` guesses `nonposPart`
/--
lemma `le_oneLePart` / 引理 `le_oneLePart`

English:
lemma le_oneLePart
  given: (a : α)
  statement: a <= a⁺ᵐ
  proof: le_sup_left

中文:
引理 le_oneLePart
  条件: (a : α)
  结论: a <= a⁺ᵐ
  证明: le_sup_left
-/
@[to_additive le_posPart] lemma le_oneLePart (a : α) : a <= a⁺ᵐ := le_sup_left

/--
lemma `inv_le_leOnePart` / 引理 `inv_le_leOnePart`

English:
lemma inv_le_leOnePart
  given: (a : α)
  statement: a⁻¹ <= a⁻ᵐ
  proof: le_sup_left

中文:
引理 inv_le_leOnePart
  条件: (a : α)
  结论: a⁻¹ <= a⁻ᵐ
  证明: le_sup_left
-/
@[to_additive] lemma inv_le_leOnePart (a : α) : a⁻¹ <= a⁻ᵐ := le_sup_left

/--
lemma `oneLePart_eq_self` / 引理 `oneLePart_eq_self`

English:
lemma oneLePart_eq_self
  statement: a⁺ᵐ = a ↔ 1 <= a
  proof: sup_eq_left

中文:
引理 oneLePart_eq_self
  结论: a⁺ᵐ = a ↔ 1 <= a
  证明: sup_eq_left
-/
@[to_additive (attr := simp)] lemma oneLePart_eq_self : a⁺ᵐ = a ↔ 1 <= a := sup_eq_left
/--
lemma `oneLePart_eq_one` / 引理 `oneLePart_eq_one`

English:
lemma oneLePart_eq_one
  statement: a⁺ᵐ = 1 ↔ a <= 1
  proof: sup_eq_right

@[to_additive (attr := simp)] alias ⟨_, oneLePart_of_one_le⟩ := oneLePart_eq_self
@[to_additive (attr := simp)] alias ⟨_, oneLePart_of_le_one⟩ := oneLePart_eq_one

中文:
引理 oneLePart_eq_one
  结论: a⁺ᵐ = 1 ↔ a <= 1
  证明: sup_eq_right

@[to_additive (attr := simp)] alias ⟨_, oneLePart_of_one_le⟩ := oneLePart_eq_self
@[to_additive (attr := simp)] alias ⟨_, oneLePart_of_le_one⟩ := oneLePart_eq_one
-/
@[to_additive (attr := simp)] lemma oneLePart_eq_one : a⁺ᵐ = 1 ↔ a <= 1 := sup_eq_right

@[to_additive (attr := simp)] alias ⟨_, oneLePart_of_one_le⟩ := oneLePart_eq_self
@[to_additive (attr := simp)] alias ⟨_, oneLePart_of_le_one⟩ := oneLePart_eq_one

/-- See also `leOnePart_eq_inv`. -/
@[to_additive /-- See also `negPart_eq_neg`. -/]
/--
lemma `leOnePart_eq_inv'` / 引理 `leOnePart_eq_inv'`

English:
lemma leOnePart_eq_inv'
  statement: a⁻ᵐ = a⁻¹ ↔ 1 <= a⁻¹
  proof: sup_eq_left

中文:
引理 leOnePart_eq_inv'
  结论: a⁻ᵐ = a⁻¹ ↔ 1 <= a⁻¹
  证明: sup_eq_left

Depends on / 依赖: sup_eq_left
-/
lemma leOnePart_eq_inv' : a⁻ᵐ = a⁻¹ ↔ 1 <= a⁻¹ := sup_eq_left

/-- See also `leOnePart_eq_one`. -/
@[to_additive /-- See also `negPart_eq_zero`. -/]
/--
lemma `leOnePart_eq_one'` / 引理 `leOnePart_eq_one'`

English:
lemma leOnePart_eq_one'
  statement: a⁻ᵐ = 1 ↔ a⁻¹ <= 1
  proof: sup_eq_right

中文:
引理 leOnePart_eq_one'
  结论: a⁻ᵐ = 1 ↔ a⁻¹ <= 1
  证明: sup_eq_right

Depends on / 依赖: sup_eq_right
-/
lemma leOnePart_eq_one' : a⁻ᵐ = 1 ↔ a⁻¹ <= 1 := sup_eq_right

/--
lemma `oneLePart_le_one` / 引理 `oneLePart_le_one`

English:
lemma oneLePart_le_one
  statement: a⁺ᵐ <= 1 ↔ a <= 1
  proof: by simp [oneLePart]

中文:
引理 oneLePart_le_one
  结论: a⁺ᵐ <= 1 ↔ a <= 1
  证明: by simp [oneLePart]
-/
@[to_additive] lemma oneLePart_le_one : a⁺ᵐ <= 1 ↔ a <= 1 := by simp [oneLePart]

/-- See also `leOnePart_le_one`. -/
@[to_additive /-- See also `negPart_nonpos`. -/]
/--
lemma `leOnePart_le_one'` / 引理 `leOnePart_le_one'`

English:
lemma leOnePart_le_one'
  statement: a⁻ᵐ <= 1 ↔ a⁻¹ <= 1
  proof: by simp [leOnePart]

中文:
引理 leOnePart_le_one'
  结论: a⁻ᵐ <= 1 ↔ a⁻¹ <= 1
  证明: by simp [leOnePart]

Depends on / 依赖: leOnePart
-/
lemma leOnePart_le_one' : a⁻ᵐ <= 1 ↔ a⁻¹ <= 1 := by simp [leOnePart]

/--
lemma `one_lt_oneLePart` / 引理 `one_lt_oneLePart`

English:
lemma one_lt_oneLePart
  given: (ha : 1 < a)
  statement: 1 < a⁺ᵐ
  proof: by
  rwa [oneLePart_eq_self.2 ha.le]

中文:
引理 one_lt_oneLePart
  条件: (ha : 1 < a)
  结论: 1 < a⁺ᵐ
  证明: by
  rwa [oneLePart_eq_self.2 ha.le]
-/
@[to_additive (attr := simp) posPart_pos] lemma one_lt_oneLePart (ha : 1 < a) : 1 < a⁺ᵐ := by
  rwa [oneLePart_eq_self.2 ha.le]

/--
lemma `oneLePart_inv` / 引理 `oneLePart_inv`

English:
lemma oneLePart_inv
  given: (a : α)
  statement: a⁻¹⁺ᵐ = a⁻ᵐ
  proof: rfl

中文:
引理 oneLePart_inv
  条件: (a : α)
  结论: a⁻¹⁺ᵐ = a⁻ᵐ
  证明: rfl
-/
@[to_additive (attr := simp)] lemma oneLePart_inv (a : α) : a⁻¹⁺ᵐ = a⁻ᵐ := rfl

/--
lemma `oneLePart_max` / 引理 `oneLePart_max`

English:
lemma oneLePart_max
  given: (a b : α)
  statement: (max a b)⁺ᵐ = max a⁺ᵐ b⁺ᵐ
  proof: by
  simp [oneLePart, sup_sup_distrib_right]

中文:
引理 oneLePart_max
  条件: (a b : α)
  结论: (max a b)⁺ᵐ = max a⁺ᵐ b⁺ᵐ
  证明: by
  simp [oneLePart, sup_sup_distrib_right]
-/
@[to_additive] lemma oneLePart_max (a b : α) : (max a b)⁺ᵐ = max a⁺ᵐ b⁺ᵐ := by
  simp [oneLePart, sup_sup_distrib_right]

end DivInvMonoid

section Group
variable [Group α] {a b : α}

/--
lemma `leOnePart_one` / 引理 `leOnePart_one`

English:
lemma leOnePart_one
  statement: (1 : α)⁻ᵐ = 1
  proof: by simp [leOnePart]

中文:
引理 leOnePart_one
  结论: (1 : α)⁻ᵐ = 1
  证明: by simp [leOnePart]
-/
@[to_additive (attr := simp)] lemma leOnePart_one : (1 : α)⁻ᵐ = 1 := by simp [leOnePart]

/--
lemma `leOnePart_inv` / 引理 `leOnePart_inv`

English:
lemma leOnePart_inv
  given: (a : α)
  statement: a⁻¹⁻ᵐ = a⁺ᵐ
  proof: by
  simp [oneLePart, leOnePart]

中文:
引理 leOnePart_inv
  条件: (a : α)
  结论: a⁻¹⁻ᵐ = a⁺ᵐ
  证明: by
  simp [oneLePart, leOnePart]
-/
@[to_additive (attr := simp)] lemma leOnePart_inv (a : α) : a⁻¹⁻ᵐ = a⁺ᵐ := by
  simp [oneLePart, leOnePart]

section MulLeftMono
variable [MulLeftMono α]

/--
lemma `leOnePart_eq_inv` / 引理 `leOnePart_eq_inv`

English:
lemma leOnePart_eq_inv
  statement: a⁻ᵐ = a⁻¹ ↔ a <= 1
  proof: by simp [leOnePart]

@[to_additive (attr := simp)]

中文:
引理 leOnePart_eq_inv
  结论: a⁻ᵐ = a⁻¹ ↔ a <= 1
  证明: by simp [leOnePart]

@[to_additive (attr := simp)]
-/
@[to_additive (attr := simp)] lemma leOnePart_eq_inv : a⁻ᵐ = a⁻¹ ↔ a <= 1 := by simp [leOnePart]

@[to_additive (attr := simp)]
/--
lemma `leOnePart_eq_one` / 引理 `leOnePart_eq_one`

English:
lemma leOnePart_eq_one
  statement: a⁻ᵐ = 1 ↔ 1 <= a
  proof: by simp [leOnePart_eq_one']

@[to_additive (attr := simp)] alias ⟨_, leOnePart_of_le_one⟩ := leOnePart_eq_inv
@[to_additive (attr := simp)] alias ⟨_, leOnePart_of_one_le⟩ := leOnePart_eq_one

中文:
引理 leOnePart_eq_one
  结论: a⁻ᵐ = 1 ↔ 1 <= a
  证明: by simp [leOnePart_eq_one']

@[to_additive (attr := simp)] alias ⟨_, leOnePart_of_le_one⟩ := leOnePart_eq_inv
@[to_additive (attr := simp)] alias ⟨_, leOnePart_of_one_le⟩ := leOnePart_eq_one

Depends on / 依赖: leOnePart_eq_one
-/
lemma leOnePart_eq_one : a⁻ᵐ = 1 ↔ 1 <= a := by simp [leOnePart_eq_one']

@[to_additive (attr := simp)] alias ⟨_, leOnePart_of_le_one⟩ := leOnePart_eq_inv
@[to_additive (attr := simp)] alias ⟨_, leOnePart_of_one_le⟩ := leOnePart_eq_one

/--
lemma `leOnePart_le_one` / 引理 `leOnePart_le_one`

English:
lemma leOnePart_le_one
  statement: a⁻ᵐ <= 1 ↔ 1 <= a
  proof: by simp [leOnePart]

中文:
引理 leOnePart_le_one
  结论: a⁻ᵐ <= 1 ↔ 1 <= a
  证明: by simp [leOnePart]
-/
@[to_additive] lemma leOnePart_le_one : a⁻ᵐ <= 1 ↔ 1 <= a := by simp [leOnePart]

/--
lemma `one_lt_leOnePart` / 引理 `one_lt_leOnePart`

English:
lemma one_lt_leOnePart
  given: (ha : a < 1)
  statement: 1 < a⁻ᵐ
  proof: by
  rwa [leOnePart_eq_inv.2 ha.le, one_lt_inv']

中文:
引理 one_lt_leOnePart
  条件: (ha : a < 1)
  结论: 1 < a⁻ᵐ
  证明: by
  rwa [leOnePart_eq_inv.2 ha.le, one_lt_inv']
-/
@[to_additive (attr := simp) negPart_pos] lemma one_lt_leOnePart (ha : a < 1) : 1 < a⁻ᵐ := by
  rwa [leOnePart_eq_inv.2 ha.le, one_lt_inv']

-- Bourbaki A.VI.12 Prop 9 a)
/--
lemma `oneLePart_div_leOnePart` / 引理 `oneLePart_div_leOnePart`

English:
lemma oneLePart_div_leOnePart
  given: (a : α)
  statement: a⁺ᵐ / a⁻ᵐ = a
  proof: by
  rw [div_eq_mul_inv]; rw [mul_inv_eq_iff_eq_mul]; rw [leOnePart_def]; rw [mul_sup]; rw [mul_one]; rw [mul_inv_cancel]; rw [sup_comm]; rw [oneLePart_def]

中文:
引理 oneLePart_div_leOnePart
  条件: (a : α)
  结论: a⁺ᵐ / a⁻ᵐ = a
  证明: by
  rw [div_eq_mul_inv]; rw [mul_inv_eq_iff_eq_mul]; rw [leOnePart_def]; rw [mul_sup]; rw [mul_one]; rw [mul_inv_cancel]; rw [sup_comm]; rw [oneLePart_def]
-/
@[to_additive (attr := simp)] lemma oneLePart_div_leOnePart (a : α) : a⁺ᵐ / a⁻ᵐ = a := by
  rw [div_eq_mul_inv]; rw [mul_inv_eq_iff_eq_mul]; rw [leOnePart_def]; rw [mul_sup]; rw [mul_one]; rw [mul_inv_cancel]; rw [sup_comm]; rw [oneLePart_def]

/--
lemma `leOnePart_div_oneLePart` / 引理 `leOnePart_div_oneLePart`

English:
lemma leOnePart_div_oneLePart
  given: (a : α)
  statement: a⁻ᵐ / a⁺ᵐ = a⁻¹
  proof: by
  rw [← inv_div]; rw [oneLePart_div_leOnePart]

@[to_additive]

中文:
引理 leOnePart_div_oneLePart
  条件: (a : α)
  结论: a⁻ᵐ / a⁺ᵐ = a⁻¹
  证明: by
  rw [← inv_div]; rw [oneLePart_div_leOnePart]

@[to_additive]
-/
@[to_additive (attr := simp)] lemma leOnePart_div_oneLePart (a : α) : a⁻ᵐ / a⁺ᵐ = a⁻¹ := by
  rw [← inv_div]; rw [oneLePart_div_leOnePart]

@[to_additive]
/--
lemma `oneLePart_leOnePart_injective` / 引理 `oneLePart_leOnePart_injective`

English:
lemma oneLePart_leOnePart_injective
  statement: Injective fun a : α => (a⁺ᵐ, a⁻ᵐ)
  proof: by
  simp only [Injective, Prod.mk.injEq, and_imp]
  rintro a b hpos hneg
  rw [← oneLePart_div_leOnePart a]; rw [← oneLePart_div_leOnePart b]; rw [hpos]; rw [hneg]

@[to_additive]

中文:
引理 oneLePart_leOnePart_injective
  结论: Injective fun a : α => (a⁺ᵐ, a⁻ᵐ)
  证明: by
  simp only [Injective, Prod.mk.injEq, and_imp]
  rintro a b hpos hneg
  rw [← oneLePart_div_leOnePart a]; rw [← oneLePart_div_leOnePart b]; rw [hpos]; rw [hneg]

@[to_additive]

Depends on / 依赖: Injective, Prod.mk.injEq, and_imp, oneLePart_div_leOnePart
-/
lemma oneLePart_leOnePart_injective : Injective fun a : α => (a⁺ᵐ, a⁻ᵐ) := by
  simp only [Injective, Prod.mk.injEq, and_imp]
  rintro a b hpos hneg
  rw [← oneLePart_div_leOnePart a]; rw [← oneLePart_div_leOnePart b]; rw [hpos]; rw [hneg]

@[to_additive]
/--
lemma `oneLePart_leOnePart_inj` / 引理 `oneLePart_leOnePart_inj`

English:
lemma oneLePart_leOnePart_inj
  statement: a⁺ᵐ = b⁺ᵐ ∧ a⁻ᵐ = b⁻ᵐ ↔ a = b
  proof: Prod.mk_inj.symm.trans oneLePart_leOnePart_injective.eq_iff

中文:
引理 oneLePart_leOnePart_inj
  结论: a⁺ᵐ = b⁺ᵐ ∧ a⁻ᵐ = b⁻ᵐ ↔ a = b
  证明: Prod.mk_inj.symm.trans oneLePart_leOnePart_injective.eq_iff

Depends on / 依赖: Prod.mk_inj.symm.trans, eq_iff, mk_inj, oneLePart_leOnePart_injective, oneLePart_leOnePart_injective.eq_iff
-/
lemma oneLePart_leOnePart_inj : a⁺ᵐ = b⁺ᵐ ∧ a⁻ᵐ = b⁻ᵐ ↔ a = b :=
  Prod.mk_inj.symm.trans oneLePart_leOnePart_injective.eq_iff

section MulRightMono
variable [MulRightMono α]

/--
lemma `leOnePart_anti` / 引理 `leOnePart_anti`

English:
lemma leOnePart_anti
  statement: Antitone (leOnePart : α -> α)
  proof: fun _a _b hab => sup_le_sup_right (inv_le_inv_iff.2 hab) _

@[to_additive]

中文:
引理 leOnePart_anti
  结论: Antitone (leOnePart : α -> α)
  证明: fun _a _b hab => sup_le_sup_right (inv_le_inv_iff.2 hab) _

@[to_additive]
-/
@[to_additive] lemma leOnePart_anti : Antitone (leOnePart : α -> α) :=
  fun _a _b hab => sup_le_sup_right (inv_le_inv_iff.2 hab) _

@[to_additive]
/--
lemma `leOnePart_eq_inv_inf_one` / 引理 `leOnePart_eq_inv_inf_one`

English:
lemma leOnePart_eq_inv_inf_one
  given: (a : α)
  statement: a⁻ᵐ = (a ⊓ 1)⁻¹
  proof: by
  rw [leOnePart_def]; rw [← inv_inj]; rw [inv_sup]; rw [inv_inv]; rw [inv_inv]; rw [inv_one]

中文:
引理 leOnePart_eq_inv_inf_one
  条件: (a : α)
  结论: a⁻ᵐ = (a ⊓ 1)⁻¹
  证明: by
  rw [leOnePart_def]; rw [← inv_inj]; rw [inv_sup]; rw [inv_inv]; rw [inv_inv]; rw [inv_one]

Depends on / 依赖: inv_inj, inv_inv, inv_one, inv_sup, leOnePart_def
-/
lemma leOnePart_eq_inv_inf_one (a : α) : a⁻ᵐ = (a ⊓ 1)⁻¹ := by
  rw [leOnePart_def]; rw [← inv_inj]; rw [inv_sup]; rw [inv_inv]; rw [inv_inv]; rw [inv_one]

-- Bourbaki A.VI.12 Prop 9 d)
/--
lemma `oneLePart_mul_leOnePart` / 引理 `oneLePart_mul_leOnePart`

English:
lemma oneLePart_mul_leOnePart
  given: (a : α)
  statement: a⁺ᵐ * a⁻ᵐ = |a|ₘ
  proof: by
  rw [oneLePart_def]; rw [sup_mul]; rw [one_mul]; rw [leOnePart_def]; rw [mul_sup]; rw [mul_one]; rw [mul_inv_cancel]; rw [sup_assoc]; rw [← sup_assoc a]; rw [sup_eq_right.2 le_sup_right]
exact sup_eq_left.2 one_le_mabs a

中文:
引理 oneLePart_mul_leOnePart
  条件: (a : α)
  结论: a⁺ᵐ * a⁻ᵐ = |a|ₘ
  证明: by
  rw [oneLePart_def]; rw [sup_mul]; rw [one_mul]; rw [leOnePart_def]; rw [mul_sup]; rw [mul_one]; rw [mul_inv_cancel]; rw [sup_assoc]; rw [← sup_assoc a]; rw [sup_eq_right.2 le_sup_right]
exact sup_eq_left.2 one_le_mabs a
-/
@[to_additive] lemma oneLePart_mul_leOnePart (a : α) : a⁺ᵐ * a⁻ᵐ = |a|ₘ := by
  rw [oneLePart_def]; rw [sup_mul]; rw [one_mul]; rw [leOnePart_def]; rw [mul_sup]; rw [mul_one]; rw [mul_inv_cancel]; rw [sup_assoc]; rw [← sup_assoc a]; rw [sup_eq_right.2 le_sup_right]
exact sup_eq_left.2 one_le_mabs a

/--
lemma `leOnePart_mul_oneLePart` / 引理 `leOnePart_mul_oneLePart`

English:
lemma leOnePart_mul_oneLePart
  given: (a : α)
  statement: a⁻ᵐ * a⁺ᵐ = |a|ₘ
  proof: by
  rw [oneLePart_def]; rw [mul_sup]; rw [mul_one]; rw [leOnePart_def]; rw [sup_mul]; rw [one_mul]; rw [inv_mul_cancel]; rw [sup_assoc]; rw [← @sup_assoc _ _ a]; rw [sup_eq_right.2 le_sup_right]
exact sup_eq_left.2 one_le_mabs a

中文:
引理 leOnePart_mul_oneLePart
  条件: (a : α)
  结论: a⁻ᵐ * a⁺ᵐ = |a|ₘ
  证明: by
  rw [oneLePart_def]; rw [mul_sup]; rw [mul_one]; rw [leOnePart_def]; rw [sup_mul]; rw [one_mul]; rw [inv_mul_cancel]; rw [sup_assoc]; rw [← @sup_assoc _ _ a]; rw [sup_eq_right.2 le_sup_right]
exact sup_eq_left.2 one_le_mabs a
-/
@[to_additive] lemma leOnePart_mul_oneLePart (a : α) : a⁻ᵐ * a⁺ᵐ = |a|ₘ := by
  rw [oneLePart_def]; rw [mul_sup]; rw [mul_one]; rw [leOnePart_def]; rw [sup_mul]; rw [one_mul]; rw [inv_mul_cancel]; rw [sup_assoc]; rw [← @sup_assoc _ _ a]; rw [sup_eq_right.2 le_sup_right]
exact sup_eq_left.2 one_le_mabs a

-- Bourbaki A.VI.12 Prop 9 a)
-- a⁺ᵐ ⊓ a⁻ᵐ = 0 (`a⁺` and `a⁻` are co-prime, and, since they are positive, disjoint)
/--
lemma `oneLePart_inf_leOnePart_eq_one` / 引理 `oneLePart_inf_leOnePart_eq_one`

English:
lemma oneLePart_inf_leOnePart_eq_one
  given: (a : α)
  statement: a⁺ᵐ ⊓ a⁻ᵐ = 1
  proof: by
  rw [← mul_left_inj a⁻ᵐ⁻¹]; rw [inf_mul]; rw [one_mul]; rw [mul_inv_cancel]; rw [← div_eq_mul_inv]; rw [oneLePart_div_leOnePart]; rw [leOnePart_eq_inv_inf_one]; rw [inv_inv]

中文:
引理 oneLePart_inf_leOnePart_eq_one
  条件: (a : α)
  结论: a⁺ᵐ ⊓ a⁻ᵐ = 1
  证明: by
  rw [← mul_left_inj a⁻ᵐ⁻¹]; rw [inf_mul]; rw [one_mul]; rw [mul_inv_cancel]; rw [← div_eq_mul_inv]; rw [oneLePart_div_leOnePart]; rw [leOnePart_eq_inv_inf_one]; rw [inv_inv]
-/
@[to_additive] lemma oneLePart_inf_leOnePart_eq_one (a : α) : a⁺ᵐ ⊓ a⁻ᵐ = 1 := by
  rw [← mul_left_inj a⁻ᵐ⁻¹]; rw [inf_mul]; rw [one_mul]; rw [mul_inv_cancel]; rw [← div_eq_mul_inv]; rw [oneLePart_div_leOnePart]; rw [leOnePart_eq_inv_inf_one]; rw [inv_inv]

/--
lemma `leOnePart_min` / 引理 `leOnePart_min`

English:
lemma leOnePart_min
  given: (a b : α)
  statement: (min a b)⁻ᵐ = max a⁻ᵐ b⁻ᵐ
  proof: by
  simp [leOnePart, inv_inf, sup_sup_distrib_right]

中文:
引理 leOnePart_min
  条件: (a b : α)
  结论: (min a b)⁻ᵐ = max a⁻ᵐ b⁻ᵐ
  证明: by
  simp [leOnePart, inv_inf, sup_sup_distrib_right]
-/
@[to_additive] lemma leOnePart_min (a b : α) : (min a b)⁻ᵐ = max a⁻ᵐ b⁻ᵐ := by
  simp [leOnePart, inv_inf, sup_sup_distrib_right]

end MulRightMono

end MulLeftMono

end Group

section CommGroup
variable [CommGroup α] [MulLeftMono α]

-- Bourbaki A.VI.12 (with a and b swapped)
/--
lemma `sup_eq_mul_oneLePart_div` / 引理 `sup_eq_mul_oneLePart_div`

English:
lemma sup_eq_mul_oneLePart_div
  given: (a b : α)
  statement: a ⊔ b = b * (a / b)⁺ᵐ
  proof: by
  simp [oneLePart, mul_sup]

中文:
引理 sup_eq_mul_oneLePart_div
  条件: (a b : α)
  结论: a ⊔ b = b * (a / b)⁺ᵐ
  证明: by
  simp [oneLePart, mul_sup]
-/
@[to_additive] lemma sup_eq_mul_oneLePart_div (a b : α) : a ⊔ b = b * (a / b)⁺ᵐ := by
  simp [oneLePart, mul_sup]

-- Bourbaki A.VI.12 (with a and b swapped)
/--
lemma `inf_eq_div_oneLePart_div` / 引理 `inf_eq_div_oneLePart_div`

English:
lemma inf_eq_div_oneLePart_div
  given: (a b : α)
  statement: a ⊓ b = a / (a / b)⁺ᵐ
  proof: by
  simp [oneLePart, div_sup, inf_comm]

中文:
引理 inf_eq_div_oneLePart_div
  条件: (a b : α)
  结论: a ⊓ b = a / (a / b)⁺ᵐ
  证明: by
  simp [oneLePart, div_sup, inf_comm]
-/
@[to_additive] lemma inf_eq_div_oneLePart_div (a b : α) : a ⊓ b = a / (a / b)⁺ᵐ := by
  simp [oneLePart, div_sup, inf_comm]

-- Bourbaki A.VI.12 Prop 9 c)
/--
lemma `le_iff_oneLePart_leOnePart` / 引理 `le_iff_oneLePart_leOnePart`

English:
lemma le_iff_oneLePart_leOnePart
  given: (a b : α)
  statement: a <= b ↔ a⁺ᵐ <= b⁺ᵐ ∧ b⁻ᵐ <= a⁻ᵐ
  proof: by
  refine ⟨fun h => ⟨oneLePart_mono h, leOnePart_anti h⟩, fun h => ?_⟩
  rw [← oneLePart_div_leOnePart a]; rw [← oneLePart_div_leOnePart b]
  exact div_le_div'' h.1 h.2

@[to_additive abs_add_eq_two_nsmul_posPart]

中文:
引理 le_iff_oneLePart_leOnePart
  条件: (a b : α)
  结论: a <= b ↔ a⁺ᵐ <= b⁺ᵐ ∧ b⁻ᵐ <= a⁻ᵐ
  证明: by
  refine ⟨fun h => ⟨oneLePart_mono h, leOnePart_anti h⟩, fun h => ?_⟩
  rw [← oneLePart_div_leOnePart a]; rw [← oneLePart_div_leOnePart b]
  exact div_le_div'' h.1 h.2

@[to_additive abs_add_eq_two_nsmul_posPart]
-/
@[to_additive] lemma le_iff_oneLePart_leOnePart (a b : α) : a <= b ↔ a⁺ᵐ <= b⁺ᵐ ∧ b⁻ᵐ <= a⁻ᵐ := by
  refine ⟨fun h => ⟨oneLePart_mono h, leOnePart_anti h⟩, fun h => ?_⟩
  rw [← oneLePart_div_leOnePart a]; rw [← oneLePart_div_leOnePart b]
  exact div_le_div'' h.1 h.2

@[to_additive abs_add_eq_two_nsmul_posPart]
/--
lemma `mabs_mul_eq_oneLePart_sq` / 引理 `mabs_mul_eq_oneLePart_sq`

English:
lemma mabs_mul_eq_oneLePart_sq
  given: (a : α)
  statement: |a|ₘ * a = a⁺ᵐ ^ 2
  proof: by
  rw [sq]; rw [← mul_mul_div_cancel a⁺ᵐ]; rw [oneLePart_mul_leOnePart]; rw [oneLePart_div_leOnePart]

@[to_additive add_abs_eq_two_nsmul_posPart]

中文:
引理 mabs_mul_eq_oneLePart_sq
  条件: (a : α)
  结论: |a|ₘ * a = a⁺ᵐ ^ 2
  证明: by
  rw [sq]; rw [← mul_mul_div_cancel a⁺ᵐ]; rw [oneLePart_mul_leOnePart]; rw [oneLePart_div_leOnePart]

@[to_additive add_abs_eq_two_nsmul_posPart]

Depends on / 依赖: mul_mul_div_cancel, oneLePart_div_leOnePart, oneLePart_mul_leOnePart
-/
lemma mabs_mul_eq_oneLePart_sq (a : α) : |a|ₘ * a = a⁺ᵐ ^ 2 := by
  rw [sq]; rw [← mul_mul_div_cancel a⁺ᵐ]; rw [oneLePart_mul_leOnePart]; rw [oneLePart_div_leOnePart]

@[to_additive add_abs_eq_two_nsmul_posPart]
/--
lemma `mul_mabs_eq_oneLePart_sq` / 引理 `mul_mabs_eq_oneLePart_sq`

English:
lemma mul_mabs_eq_oneLePart_sq
  given: (a : α)
  statement: a * |a|ₘ = a⁺ᵐ ^ 2
  proof: by
  rw [mul_comm]; rw [mabs_mul_eq_oneLePart_sq]

@[to_additive abs_sub_eq_two_nsmul_negPart]

中文:
引理 mul_mabs_eq_oneLePart_sq
  条件: (a : α)
  结论: a * |a|ₘ = a⁺ᵐ ^ 2
  证明: by
  rw [mul_comm]; rw [mabs_mul_eq_oneLePart_sq]

@[to_additive abs_sub_eq_two_nsmul_negPart]

Depends on / 依赖: mabs_mul_eq_oneLePart_sq, mul_comm
-/
lemma mul_mabs_eq_oneLePart_sq (a : α) : a * |a|ₘ = a⁺ᵐ ^ 2 := by
  rw [mul_comm]; rw [mabs_mul_eq_oneLePart_sq]

@[to_additive abs_sub_eq_two_nsmul_negPart]
/--
lemma `mabs_div_eq_leOnePart_sq` / 引理 `mabs_div_eq_leOnePart_sq`

English:
lemma mabs_div_eq_leOnePart_sq
  given: (a : α)
  statement: |a|ₘ / a = a⁻ᵐ ^ 2
  proof: by
  rw [sq]; rw [← mul_div_div_cancel]; rw [oneLePart_mul_leOnePart]; rw [oneLePart_div_leOnePart]

@[to_additive sub_abs_eq_neg_two_nsmul_negPart]

中文:
引理 mabs_div_eq_leOnePart_sq
  条件: (a : α)
  结论: |a|ₘ / a = a⁻ᵐ ^ 2
  证明: by
  rw [sq]; rw [← mul_div_div_cancel]; rw [oneLePart_mul_leOnePart]; rw [oneLePart_div_leOnePart]

@[to_additive sub_abs_eq_neg_two_nsmul_negPart]

Depends on / 依赖: mul_div_div_cancel, oneLePart_div_leOnePart, oneLePart_mul_leOnePart
-/
lemma mabs_div_eq_leOnePart_sq (a : α) : |a|ₘ / a = a⁻ᵐ ^ 2 := by
  rw [sq]; rw [← mul_div_div_cancel]; rw [oneLePart_mul_leOnePart]; rw [oneLePart_div_leOnePart]

@[to_additive sub_abs_eq_neg_two_nsmul_negPart]
/--
lemma `div_mabs_eq_inv_leOnePart_sq` / 引理 `div_mabs_eq_inv_leOnePart_sq`

English:
lemma div_mabs_eq_inv_leOnePart_sq
  given: (a : α)
  statement: a / |a|ₘ = (a⁻ᵐ ^ 2)⁻¹
  proof: by
  rw [← mabs_div_eq_leOnePart_sq]; rw [inv_div]

中文:
引理 div_mabs_eq_inv_leOnePart_sq
  条件: (a : α)
  结论: a / |a|ₘ = (a⁻ᵐ ^ 2)⁻¹
  证明: by
  rw [← mabs_div_eq_leOnePart_sq]; rw [inv_div]

Depends on / 依赖: inv_div, mabs_div_eq_leOnePart_sq
-/
lemma div_mabs_eq_inv_leOnePart_sq (a : α) : a / |a|ₘ = (a⁻ᵐ ^ 2)⁻¹ := by
  rw [← mabs_div_eq_leOnePart_sq]; rw [inv_div]

end CommGroup
end Lattice

section DistribLattice
variable [DistribLattice α] [Group α]

/--
lemma `oneLePart_min` / 引理 `oneLePart_min`

English:
lemma oneLePart_min
  given: (a b : α)
  statement: (min a b)⁺ᵐ = min a⁺ᵐ b⁺ᵐ
  proof: by
  simp [oneLePart, sup_inf_right]

中文:
引理 oneLePart_min
  条件: (a b : α)
  结论: (min a b)⁺ᵐ = min a⁺ᵐ b⁺ᵐ
  证明: by
  simp [oneLePart, sup_inf_right]
-/
@[to_additive] lemma oneLePart_min (a b : α) : (min a b)⁺ᵐ = min a⁺ᵐ b⁺ᵐ := by
  simp [oneLePart, sup_inf_right]

variable [MulLeftMono α] [MulRightMono α]

/--
lemma `leOnePart_max` / 引理 `leOnePart_max`

English:
lemma leOnePart_max
  given: (a b : α)
  statement: (max a b)⁻ᵐ = min a⁻ᵐ b⁻ᵐ
  proof: by
  simp [leOnePart, inv_sup, sup_inf_right]

中文:
引理 leOnePart_max
  条件: (a b : α)
  结论: (max a b)⁻ᵐ = min a⁻ᵐ b⁻ᵐ
  证明: by
  simp [leOnePart, inv_sup, sup_inf_right]
-/
@[to_additive] lemma leOnePart_max (a b : α) : (max a b)⁻ᵐ = min a⁻ᵐ b⁻ᵐ := by
  simp [leOnePart, inv_sup, sup_inf_right]

end DistribLattice

section LinearOrder
variable [LinearOrder α] [Group α] {a b : α}

/--
lemma `oneLePart_eq_ite` / 引理 `oneLePart_eq_ite`

English:
lemma oneLePart_eq_ite
  statement: a⁺ᵐ = if 1 <= a then a else 1
  proof: by
  rw [oneLePart_def]; rw [← maxDefault]; rw [← sup_eq_maxDefault]; simp_rw [sup_comm]

中文:
引理 oneLePart_eq_ite
  结论: a⁺ᵐ = if 1 <= a then a else 1
  证明: by
  rw [oneLePart_def]; rw [← maxDefault]; rw [← sup_eq_maxDefault]; simp_rw [sup_comm]
-/
@[to_additive] lemma oneLePart_eq_ite : a⁺ᵐ = if 1 <= a then a else 1 := by
  rw [oneLePart_def]; rw [← maxDefault]; rw [← sup_eq_maxDefault]; simp_rw [sup_comm]

/--
lemma `oneLePart_eq_ite_lt` / 引理 `oneLePart_eq_ite_lt`

English:
lemma oneLePart_eq_ite_lt
  statement: a⁺ᵐ = if 1 < a then a else 1
  proof: by
  grind [oneLePart_eq_ite]

中文:
引理 oneLePart_eq_ite_lt
  结论: a⁺ᵐ = if 1 < a then a else 1
  证明: by
  grind [oneLePart_eq_ite]
-/
@[to_additive] lemma oneLePart_eq_ite_lt : a⁺ᵐ = if 1 < a then a else 1 := by
  grind [oneLePart_eq_ite]

/--
lemma `one_lt_oneLePart_iff` / 引理 `one_lt_oneLePart_iff`

English:
lemma one_lt_oneLePart_iff
  statement: 1 < a⁺ᵐ ↔ 1 < a
  proof: lt_iff_lt_of_le_iff_le (one_le_oneLePart _).ge_iff_eq'.trans oneLePart_eq_one

@[to_additive posPart_eq_of_posPart_pos]

中文:
引理 one_lt_oneLePart_iff
  结论: 1 < a⁺ᵐ ↔ 1 < a
  证明: lt_iff_lt_of_le_iff_le (one_le_oneLePart _).ge_iff_eq'.trans oneLePart_eq_one

@[to_additive posPart_eq_of_posPart_pos]
-/
@[to_additive (attr := simp) posPart_pos_iff] lemma one_lt_oneLePart_iff : 1 < a⁺ᵐ ↔ 1 < a :=
lt_iff_lt_of_le_iff_le (one_le_oneLePart _).ge_iff_eq'.trans oneLePart_eq_one

@[to_additive posPart_eq_of_posPart_pos]
/--
lemma `oneLePart_of_one_lt_oneLePart` / 引理 `oneLePart_of_one_lt_oneLePart`

English:
lemma oneLePart_of_one_lt_oneLePart
  given: (ha : 1 < a⁺ᵐ)
  statement: a⁺ᵐ = a
  proof: by
  rw [oneLePart_def]; rw [right_lt_sup]; rw [not_le] at ha; exact oneLePart_eq_self.2 ha.le

中文:
引理 oneLePart_of_one_lt_oneLePart
  条件: (ha : 1 < a⁺ᵐ)
  结论: a⁺ᵐ = a
  证明: by
  rw [oneLePart_def]; rw [right_lt_sup]; rw [not_le] at ha; exact oneLePart_eq_self.2 ha.le

Depends on / 依赖: ha.le, not_le, oneLePart_def, oneLePart_eq_self, right_lt_sup
-/
lemma oneLePart_of_one_lt_oneLePart (ha : 1 < a⁺ᵐ) : a⁺ᵐ = a := by
  rw [oneLePart_def]; rw [right_lt_sup]; rw [not_le] at ha; exact oneLePart_eq_self.2 ha.le

/--
lemma `oneLePart_lt` / 引理 `oneLePart_lt`

English:
lemma oneLePart_lt
  statement: a⁺ᵐ < b ↔ a < b ∧ 1 < b
  proof: sup_lt_iff

中文:
引理 oneLePart_lt
  结论: a⁺ᵐ < b ↔ a < b ∧ 1 < b
  证明: sup_lt_iff
-/
@[to_additive (attr := simp)] lemma oneLePart_lt : a⁺ᵐ < b ↔ a < b ∧ 1 < b := sup_lt_iff

section covariantmul
variable [MulLeftMono α]

/--
lemma `leOnePart_eq_ite` / 引理 `leOnePart_eq_ite`

English:
lemma leOnePart_eq_ite
  statement: a⁻ᵐ = if a <= 1 then a⁻¹ else 1
  proof: by
  simp_rw [← one_le_inv']; rw [leOnePart_def, ← maxDefault, ← sup_eq_maxDefault]; simp_rw [sup_comm]

中文:
引理 leOnePart_eq_ite
  结论: a⁻ᵐ = if a <= 1 then a⁻¹ else 1
  证明: by
  simp_rw [← one_le_inv']; rw [leOnePart_def, ← maxDefault, ← sup_eq_maxDefault]; simp_rw [sup_comm]
-/
@[to_additive] lemma leOnePart_eq_ite : a⁻ᵐ = if a <= 1 then a⁻¹ else 1 := by
  simp_rw [← one_le_inv']; rw [leOnePart_def, ← maxDefault, ← sup_eq_maxDefault]; simp_rw [sup_comm]

/--
lemma `leOnePart_eq_ite_lt` / 引理 `leOnePart_eq_ite_lt`

English:
lemma leOnePart_eq_ite_lt
  statement: a⁻ᵐ = if a < 1 then a⁻¹ else 1
  proof: by
  grind [leOnePart_eq_ite, inv_one]

中文:
引理 leOnePart_eq_ite_lt
  结论: a⁻ᵐ = if a < 1 then a⁻¹ else 1
  证明: by
  grind [leOnePart_eq_ite, inv_one]
-/
@[to_additive] lemma leOnePart_eq_ite_lt : a⁻ᵐ = if a < 1 then a⁻¹ else 1 := by
  grind [leOnePart_eq_ite, inv_one]

/--
lemma `one_lt_leOnePart_iff` / 引理 `one_lt_leOnePart_iff`

English:
lemma one_lt_leOnePart_iff
  statement: 1 < a⁻ᵐ ↔ a < 1
  proof: lt_iff_lt_of_le_iff_le (one_le_leOnePart _).ge_iff_eq'.trans leOnePart_eq_one

中文:
引理 one_lt_leOnePart_iff
  结论: 1 < a⁻ᵐ ↔ a < 1
  证明: lt_iff_lt_of_le_iff_le (one_le_leOnePart _).ge_iff_eq'.trans leOnePart_eq_one
-/
@[to_additive (attr := simp) negPart_pos_iff] lemma one_lt_leOnePart_iff : 1 < a⁻ᵐ ↔ a < 1 :=
lt_iff_lt_of_le_iff_le (one_le_leOnePart _).ge_iff_eq'.trans leOnePart_eq_one

variable [MulRightMono α]

/--
lemma `leOnePart_lt` / 引理 `leOnePart_lt`

English:
lemma leOnePart_lt
  statement: a⁻ᵐ < b ↔ b⁻¹ < a ∧ 1 < b
  proof: sup_lt_iff.trans by rw [inv_lt']

中文:
引理 leOnePart_lt
  结论: a⁻ᵐ < b ↔ b⁻¹ < a ∧ 1 < b
  证明: sup_lt_iff.trans by rw [inv_lt']
-/
@[to_additive (attr := simp)] lemma leOnePart_lt : a⁻ᵐ < b ↔ b⁻¹ < a ∧ 1 < b :=
sup_lt_iff.trans by rw [inv_lt']

end covariantmul
end LinearOrder

namespace Pi
variable {ι : Type*} {α : ι -> Type*} [forall i, Lattice (α i)] [forall i, Group (α i)]

/--
lemma `oneLePart_apply` / 引理 `oneLePart_apply`

English:
lemma oneLePart_apply
  given: (f : forall i, α i) (i : ι)
  statement: f⁺ᵐ i = (f i)⁺ᵐ
  proof: rfl

中文:
引理 oneLePart_apply
  条件: (f : 对任意 i, α i) (i : ι)
  结论: f⁺ᵐ i = (f i)⁺ᵐ
  证明: rfl
-/
@[to_additive (attr := simp)] lemma oneLePart_apply (f : forall i, α i) (i : ι) : f⁺ᵐ i = (f i)⁺ᵐ := rfl
/--
lemma `leOnePart_apply` / 引理 `leOnePart_apply`

English:
lemma leOnePart_apply
  given: (f : forall i, α i) (i : ι)
  statement: f⁻ᵐ i = (f i)⁻ᵐ
  proof: rfl

中文:
引理 leOnePart_apply
  条件: (f : 对任意 i, α i) (i : ι)
  结论: f⁻ᵐ i = (f i)⁻ᵐ
  证明: rfl
-/
@[to_additive (attr := simp)] lemma leOnePart_apply (f : forall i, α i) (i : ι) : f⁻ᵐ i = (f i)⁻ᵐ := rfl

/--
lemma `oneLePart_def` / 引理 `oneLePart_def`

English:
lemma oneLePart_def
  given: (f : forall i, α i)
  statement: f⁺ᵐ = fun i => (f i)⁺ᵐ
  proof: rfl

中文:
引理 oneLePart_def
  条件: (f : 对任意 i, α i)
  结论: f⁺ᵐ = fun i => (f i)⁺ᵐ
  证明: rfl
-/
@[to_additive (attr := push ←)] lemma oneLePart_def (f : forall i, α i) : f⁺ᵐ = fun i => (f i)⁺ᵐ := rfl
/--
lemma `leOnePart_def` / 引理 `leOnePart_def`

English:
lemma leOnePart_def
  given: (f : forall i, α i)
  statement: f⁻ᵐ = fun i => (f i)⁻ᵐ
  proof: rfl

中文:
引理 leOnePart_def
  条件: (f : 对任意 i, α i)
  结论: f⁻ᵐ = fun i => (f i)⁻ᵐ
  证明: rfl
-/
@[to_additive (attr := push ←)] lemma leOnePart_def (f : forall i, α i) : f⁻ᵐ = fun i => (f i)⁻ᵐ := rfl

end Pi
