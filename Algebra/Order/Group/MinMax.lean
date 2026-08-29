/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl
-/
module

public import Mathlib.Algebra.Order.Group.Abs
public import Mathlib.Algebra.Order.Monoid.Unbundled.MinMax

/-!
# `min` and `max` in linearly ordered groups.
-/

public section


section

variable {α : Type*} [Group α] [LinearOrder α] [MulLeftMono α]

-- TODO: This duplicates `oneLePart_div_leOnePart`
@[to_additive (attr := simp)]
/--
theorem `max_one_div_max_inv_one_eq_self` / 定理 `max_one_div_max_inv_one_eq_self`

English:
theorem max_one_div_max_inv_one_eq_self
  given: (a : α)
  statement: max a 1 / max a⁻¹ 1 = a
  proof: by
  rcases le_total a 1 with (h | h) <;> simp [h]

alias max_zero_sub_eq_self := max_zero_sub_max_neg_zero_eq_self

@[to_additive]

中文:
定理 max_one_div_max_inv_one_eq_self
  条件: (a : α)
  结论: max a 1 / max a⁻¹ 1 = a
  证明: by
  rcases le_total a 1 with (h | h) <;> simp [h]

alias max_zero_sub_eq_self := max_zero_sub_max_neg_zero_eq_self

@[to_additive]

Depends on / 依赖: le_total
-/
theorem max_one_div_max_inv_one_eq_self (a : α) : max a 1 / max a⁻¹ 1 = a := by
  rcases le_total a 1 with (h | h) <;> simp [h]

alias max_zero_sub_eq_self := max_zero_sub_max_neg_zero_eq_self

@[to_additive]
/--
lemma `max_inv_one` / 引理 `max_inv_one`

English:
lemma max_inv_one
  given: (a : α)
  statement: max a⁻¹ 1 = a⁻¹ * max a 1
  proof: by
  rw [eq_inv_mul_iff_mul_eq]; rw [← eq_div_iff_mul_eq']; rw [max_one_div_max_inv_one_eq_self]

中文:
引理 max_inv_one
  条件: (a : α)
  结论: max a⁻¹ 1 = a⁻¹ * max a 1
  证明: by
  rw [eq_inv_mul_iff_mul_eq]; rw [← eq_div_iff_mul_eq']; rw [max_one_div_max_inv_one_eq_self]

Depends on / 依赖: eq_div_iff_mul_eq, eq_inv_mul_iff_mul_eq, max_one_div_max_inv_one_eq_self
-/
lemma max_inv_one (a : α) : max a⁻¹ 1 = a⁻¹ * max a 1 := by
  rw [eq_inv_mul_iff_mul_eq]; rw [← eq_div_iff_mul_eq']; rw [max_one_div_max_inv_one_eq_self]

end

section Inv

variable {G₀ : Type*} [Inv G₀] [LinearOrder G₀] {x y : G₀}

/--
lemma `min_inv_inv_le` / 引理 `min_inv_inv_le`

English:
lemma min_inv_inv_le
  statement: min x⁻¹ y⁻¹ <= (max x y)⁻¹
  proof: by
  cases le_total x y <;> simp_all

中文:
引理 min_inv_inv_le
  结论: min x⁻¹ y⁻¹ <= (max x y)⁻¹
  证明: by
  cases le_total x y <;> simp_all

Depends on / 依赖: le_total
-/
lemma min_inv_inv_le : min x⁻¹ y⁻¹ <= (max x y)⁻¹ := by
  cases le_total x y <;> simp_all

end Inv

section LinearOrderedCommGroup

variable {α : Type*} [CommGroup α] [LinearOrder α] [IsOrderedMonoid α]

@[to_additive min_neg_neg]
/--
theorem `min_inv_inv'` / 定理 `min_inv_inv'`

English:
theorem min_inv_inv'
  given: (a b : α)
  statement: min a⁻¹ b⁻¹ = (max a b)⁻¹
  proof: Eq.symm (@Monotone.map_max α αᵒᵈ _ _ Inv.inv a b) fun _ _ =>
    inv_le_inv_iff.mpr

@[to_additive max_neg_neg]

中文:
定理 min_inv_inv'
  条件: (a b : α)
  结论: min a⁻¹ b⁻¹ = (max a b)⁻¹
  证明: Eq.symm (@Monotone.map_max α αᵒᵈ _ _ Inv.inv a b) fun _ _ =>
    inv_le_inv_iff.mpr

@[to_additive max_neg_neg]

Depends on / 依赖: Eq.symm, Inv.inv, Monotone, Monotone.map_max, inv_le_inv_iff, inv_le_inv_iff.mpr, map_max
-/
theorem min_inv_inv' (a b : α) : min a⁻¹ b⁻¹ = (max a b)⁻¹ :=
Eq.symm (@Monotone.map_max α αᵒᵈ _ _ Inv.inv a b) fun _ _ =>
    inv_le_inv_iff.mpr

@[to_additive max_neg_neg]
/--
theorem `max_inv_inv'` / 定理 `max_inv_inv'`

English:
theorem max_inv_inv'
  given: (a b : α)
  statement: max a⁻¹ b⁻¹ = (min a b)⁻¹
  proof: Eq.symm (@Monotone.map_min α αᵒᵈ _ _ Inv.inv a b) fun _ _ =>
    inv_le_inv_iff.mpr

@[to_additive min_sub_sub_right]

中文:
定理 max_inv_inv'
  条件: (a b : α)
  结论: max a⁻¹ b⁻¹ = (min a b)⁻¹
  证明: Eq.symm (@Monotone.map_min α αᵒᵈ _ _ Inv.inv a b) fun _ _ =>
    inv_le_inv_iff.mpr

@[to_additive min_sub_sub_right]

Depends on / 依赖: Eq.symm, Inv.inv, Monotone, Monotone.map_min, inv_le_inv_iff, inv_le_inv_iff.mpr, map_min
-/
theorem max_inv_inv' (a b : α) : max a⁻¹ b⁻¹ = (min a b)⁻¹ :=
Eq.symm (@Monotone.map_min α αᵒᵈ _ _ Inv.inv a b) fun _ _ =>
    inv_le_inv_iff.mpr

@[to_additive min_sub_sub_right]
/--
theorem `min_div_div_right'` / 定理 `min_div_div_right'`

English:
theorem min_div_div_right'
  given: (a b c : α)
  statement: min (a / c) (b / c) = min a b / c
  proof: by
  simpa only [div_eq_mul_inv] using min_mul_mul_right a b c⁻¹

@[to_additive max_sub_sub_right]

中文:
定理 min_div_div_right'
  条件: (a b c : α)
  结论: min (a / c) (b / c) = min a b / c
  证明: by
  simpa only [div_eq_mul_inv] using min_mul_mul_right a b c⁻¹

@[to_additive max_sub_sub_right]

Depends on / 依赖: div_eq_mul_inv, min_mul_mul_right
-/
theorem min_div_div_right' (a b c : α) : min (a / c) (b / c) = min a b / c := by
  simpa only [div_eq_mul_inv] using min_mul_mul_right a b c⁻¹

@[to_additive max_sub_sub_right]
/--
theorem `max_div_div_right'` / 定理 `max_div_div_right'`

English:
theorem max_div_div_right'
  given: (a b c : α)
  statement: max (a / c) (b / c) = max a b / c
  proof: by
  simpa only [div_eq_mul_inv] using max_mul_mul_right a b c⁻¹

@[to_additive min_sub_sub_left]

中文:
定理 max_div_div_right'
  条件: (a b c : α)
  结论: max (a / c) (b / c) = max a b / c
  证明: by
  simpa only [div_eq_mul_inv] using max_mul_mul_right a b c⁻¹

@[to_additive min_sub_sub_left]

Depends on / 依赖: div_eq_mul_inv, max_mul_mul_right
-/
theorem max_div_div_right' (a b c : α) : max (a / c) (b / c) = max a b / c := by
  simpa only [div_eq_mul_inv] using max_mul_mul_right a b c⁻¹

@[to_additive min_sub_sub_left]
/--
theorem `min_div_div_left'` / 定理 `min_div_div_left'`

English:
theorem min_div_div_left'
  given: (a b c : α)
  statement: min (a / b) (a / c) = a / max b c
  proof: by
  simp only [div_eq_mul_inv, min_mul_mul_left, min_inv_inv']

@[to_additive max_sub_sub_left]

中文:
定理 min_div_div_left'
  条件: (a b c : α)
  结论: min (a / b) (a / c) = a / max b c
  证明: by
  simp only [div_eq_mul_inv, min_mul_mul_left, min_inv_inv']

@[to_additive max_sub_sub_left]

Depends on / 依赖: div_eq_mul_inv, min_inv_inv, min_mul_mul_left
-/
theorem min_div_div_left' (a b c : α) : min (a / b) (a / c) = a / max b c := by
  simp only [div_eq_mul_inv, min_mul_mul_left, min_inv_inv']

@[to_additive max_sub_sub_left]
/--
theorem `max_div_div_left'` / 定理 `max_div_div_left'`

English:
theorem max_div_div_left'
  given: (a b c : α)
  statement: max (a / b) (a / c) = a / min b c
  proof: by
  simp only [div_eq_mul_inv, max_mul_mul_left, max_inv_inv']

中文:
定理 max_div_div_left'
  条件: (a b c : α)
  结论: max (a / b) (a / c) = a / min b c
  证明: by
  simp only [div_eq_mul_inv, max_mul_mul_left, max_inv_inv']

Depends on / 依赖: div_eq_mul_inv, max_inv_inv, max_mul_mul_left
-/
theorem max_div_div_left' (a b c : α) : max (a / b) (a / c) = a / min b c := by
  simp only [div_eq_mul_inv, max_mul_mul_left, max_inv_inv']

end LinearOrderedCommGroup

section LinearOrderedAddCommGroup

variable {α : Type*} [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α]

/--
theorem `max_sub_max_le_max` / 定理 `max_sub_max_le_max`

English:
theorem max_sub_max_le_max
  given: (a b c d : α)
  statement: max a b - max c d <= max (a - c) (b - d)
  proof: by
  grind

中文:
定理 max_sub_max_le_max
  条件: (a b c d : α)
  结论: max a b - max c d <= max (a - c) (b - d)
  证明: by
  grind
-/
theorem max_sub_max_le_max (a b c d : α) : max a b - max c d <= max (a - c) (b - d) := by
  grind

/--
theorem `abs_max_sub_max_le_max` / 定理 `abs_max_sub_max_le_max`

English:
theorem abs_max_sub_max_le_max
  given: (a b c d : α)
  statement: |max a b - max c d| <= max |a - c| |b - d|
  proof: by
  refine abs_sub_le_iff.2 ⟨?_, ?_⟩
  · exact (max_sub_max_le_max _ _ _ _).trans (max_le_max (le_abs_self _) (le_abs_self _))
  · rw [abs_sub_comm a c, abs_sub_comm b d]
    exact (max_sub_max_le_max _ _ _ _).trans (max_le_max (le_abs_self _) (le_abs_self _))

中文:
定理 abs_max_sub_max_le_max
  条件: (a b c d : α)
  结论: |max a b - max c d| <= max |a - c| |b - d|
  证明: by
  refine abs_sub_le_iff.2 ⟨?_, ?_⟩
  · exact (max_sub_max_le_max _ _ _ _).trans (max_le_max (le_abs_self _) (le_abs_self _))
  · rw [abs_sub_comm a c, abs_sub_comm b d]
    exact (max_sub_max_le_max _ _ _ _).trans (max_le_max (le_abs_self _) (le_abs_self _))

Depends on / 依赖: abs_sub_comm, abs_sub_le_iff, le_abs_self, max_le_max, max_sub_max_le_max
-/
theorem abs_max_sub_max_le_max (a b c d : α) : |max a b - max c d| <= max |a - c| |b - d| := by
  refine abs_sub_le_iff.2 ⟨?_, ?_⟩
  · exact (max_sub_max_le_max _ _ _ _).trans (max_le_max (le_abs_self _) (le_abs_self _))
  · rw [abs_sub_comm a c, abs_sub_comm b d]
    exact (max_sub_max_le_max _ _ _ _).trans (max_le_max (le_abs_self _) (le_abs_self _))

/--
theorem `abs_min_sub_min_le_max` / 定理 `abs_min_sub_min_le_max`

English:
theorem abs_min_sub_min_le_max
  given: (a b c d : α)
  statement: |min a b - min c d| <= max |a - c| |b - d|
  proof: by
  simpa only [max_neg_neg, neg_sub_neg, abs_sub_comm] using
    abs_max_sub_max_le_max (-a) (-b) (-c) (-d)

中文:
定理 abs_min_sub_min_le_max
  条件: (a b c d : α)
  结论: |min a b - min c d| <= max |a - c| |b - d|
  证明: by
  simpa only [max_neg_neg, neg_sub_neg, abs_sub_comm] using
    abs_max_sub_max_le_max (-a) (-b) (-c) (-d)

Depends on / 依赖: abs_max_sub_max_le_max, abs_sub_comm, max_neg_neg, neg_sub_neg
-/
theorem abs_min_sub_min_le_max (a b c d : α) : |min a b - min c d| <= max |a - c| |b - d| := by
  simpa only [max_neg_neg, neg_sub_neg, abs_sub_comm] using
    abs_max_sub_max_le_max (-a) (-b) (-c) (-d)

/--
theorem `abs_max_sub_max_le_abs` / 定理 `abs_max_sub_max_le_abs`

English:
theorem abs_max_sub_max_le_abs
  given: (a b c : α)
  statement: |max a c - max b c| <= |a - b|
  proof: by
  simpa only [sub_self, abs_zero, max_eq_left (abs_nonneg (a - b))]
    using abs_max_sub_max_le_max a c b c

中文:
定理 abs_max_sub_max_le_abs
  条件: (a b c : α)
  结论: |max a c - max b c| <= |a - b|
  证明: by
  simpa only [sub_self, abs_zero, max_eq_left (abs_nonneg (a - b))]
    using abs_max_sub_max_le_max a c b c

Depends on / 依赖: abs_max_sub_max_le_max, abs_nonneg, abs_zero, max_eq_left, sub_self
-/
theorem abs_max_sub_max_le_abs (a b c : α) : |max a c - max b c| <= |a - b| := by
  simpa only [sub_self, abs_zero, max_eq_left (abs_nonneg (a - b))]
    using abs_max_sub_max_le_max a c b c

end LinearOrderedAddCommGroup
