/-
Copyright (c) 2019 Neil Strickland. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Neil Strickland
-/
module

public import Mathlib.Algebra.Field.GeomSum
public import Mathlib.Algebra.Order.Ring.Defs

/-!
# Partial sums of geometric series in an ordered field

This file upper- and lower-bounds the values of the geometric series $\sum_{i=0}^{n-1} x^i$ and
$\sum_{i=0}^{n-1} x^i y^{n-1-i}$ and variants thereof.
-/

public section

variable {K : Type*}

open Finset MulOpposite

section Semifield
variable [Semifield K] [LinearOrder K] [IsStrictOrderedRing K] [CanonicallyOrderedAdd K]
  [Sub K] [OrderedSub K] {x y : K}

/--
lemma `geom₂_sum_of_gt` / 引理 `geom₂_sum_of_gt`

English:
lemma geom₂_sum_of_gt
  given: (h : y < x) (n : Nat)
  proof: eq_div_of_mul_eq (tsub_pos_of_lt h).ne' (geom_sum₂_mul_of_ge h.le n)

中文:
引理 geom₂_sum_of_gt
  条件: (h : y < x) (n : 自然数)
  证明: eq_div_of_mul_eq (tsub_pos_of_lt h).ne' (geom_sum₂_mul_of_ge h.le n)

Depends on / 依赖: eq_div_of_mul_eq, h.le, tsub_pos_of_lt
-/
lemma geom₂_sum_of_gt (h : y < x) (n : Nat) :
    ∑ i in range n, x ^ i * y ^ (n - 1 - i) = (x ^ n - y ^ n) / (x - y) :=
  eq_div_of_mul_eq (tsub_pos_of_lt h).ne' (geom_sum₂_mul_of_ge h.le n)

/--
lemma `geom₂_sum_of_lt` / 引理 `geom₂_sum_of_lt`

English:
lemma geom₂_sum_of_lt
  given: (h : x < y) (n : Nat)
  proof: eq_div_of_mul_eq (tsub_pos_of_lt h).ne' (geom_sum₂_mul_of_le h.le n)

中文:
引理 geom₂_sum_of_lt
  条件: (h : x < y) (n : 自然数)
  证明: eq_div_of_mul_eq (tsub_pos_of_lt h).ne' (geom_sum₂_mul_of_le h.le n)

Depends on / 依赖: eq_div_of_mul_eq, h.le, tsub_pos_of_lt
-/
lemma geom₂_sum_of_lt (h : x < y) (n : Nat) :
    ∑ i in range n, x ^ i * y ^ (n - 1 - i) = (y ^ n - x ^ n) / (y - x) :=
  eq_div_of_mul_eq (tsub_pos_of_lt h).ne' (geom_sum₂_mul_of_le h.le n)

/--
lemma `geom_sum_of_one_lt` / 引理 `geom_sum_of_one_lt`

English:
lemma geom_sum_of_one_lt
  given: (h : 1 < x) (n : Nat)
  proof: eq_div_of_mul_eq (tsub_pos_of_lt h).ne' (geom_sum_mul_of_one_le h.le n)

中文:
引理 geom_sum_of_one_lt
  条件: (h : 1 < x) (n : 自然数)
  证明: eq_div_of_mul_eq (tsub_pos_of_lt h).ne' (geom_sum_mul_of_one_le h.le n)

Depends on / 依赖: eq_div_of_mul_eq, geom_sum_mul_of_one_le, h.le, tsub_pos_of_lt
-/
lemma geom_sum_of_one_lt (h : 1 < x) (n : Nat) :
    ∑ i in Finset.range n, x ^ i = (x ^ n - 1) / (x - 1) :=
  eq_div_of_mul_eq (tsub_pos_of_lt h).ne' (geom_sum_mul_of_one_le h.le n)

/--
lemma `geom_sum_of_lt_one` / 引理 `geom_sum_of_lt_one`

English:
lemma geom_sum_of_lt_one
  given: (h : x < 1) (n : Nat)
  proof: eq_div_of_mul_eq (tsub_pos_of_lt h).ne' (geom_sum_mul_of_le_one h.le n)

中文:
引理 geom_sum_of_lt_one
  条件: (h : x < 1) (n : 自然数)
  证明: eq_div_of_mul_eq (tsub_pos_of_lt h).ne' (geom_sum_mul_of_le_one h.le n)

Depends on / 依赖: Monotone, WithZero, WithZero.forall, eq_div_of_mul_eq, geom_sum_mul_of_le_one, h.le, tsub_pos_of_lt
-/
lemma geom_sum_of_lt_one (h : x < 1) (n : Nat) :
    ∑ i in Finset.range n, x ^ i = (1 - x ^ n) / (1 - x) :=
  eq_div_of_mul_eq (tsub_pos_of_lt h).ne' (geom_sum_mul_of_le_one h.le n)

/--
lemma `geom_sum_lt` / 引理 `geom_sum_lt`

English:
lemma geom_sum_lt
  given: (h0 : x != 0) (h1 : x < 1) (n : Nat)
  statement: ∑ i in range n, x ^ i < (1 - x)⁻¹
  proof: by
  rw [← pos_iff_ne_zero] at h0
  rw [geom_sum_of_lt_one h1]; rw [div_lt_iff₀]; rw [inv_mul_cancel₀]; rw [tsub_lt_self_iff]
  · exact ⟨h0.trans h1, pow_pos h0 n⟩
  · rwa [ne_eq, tsub_eq_zero_iff_le, not_le]
  · rwa [tsub_pos_iff_lt]

中文:
引理 geom_sum_lt
  条件: (h0 : x != 0) (h1 : x < 1) (n : 自然数)
  结论: ∑ i in range n, x ^ i < (1 - x)⁻¹
  证明: by
  rw [← pos_iff_ne_zero] at h0
  rw [geom_sum_of_lt_one h1]; rw [div_lt_iff₀]; rw [inv_mul_cancel₀]; rw [tsub_lt_self_iff]
  · exact ⟨h0.trans h1, pow_pos h0 n⟩
  · rwa [ne_eq, tsub_eq_zero_iff_le, not_le]
  · rwa [tsub_pos_iff_lt]

Depends on / 依赖: StrictMono, WithZero, WithZero.forall, geom_sum_of_lt_one, h0.trans, ne_eq, not_le, pos_iff_ne_zero, pow_pos, tsub_eq_zero_iff_le, tsub_lt_self_iff, tsub_pos_iff_lt
-/
lemma geom_sum_lt (h0 : x != 0) (h1 : x < 1) (n : Nat) : ∑ i in range n, x ^ i < (1 - x)⁻¹ := by
  rw [← pos_iff_ne_zero] at h0
  rw [geom_sum_of_lt_one h1]; rw [div_lt_iff₀]; rw [inv_mul_cancel₀]; rw [tsub_lt_self_iff]
  · exact ⟨h0.trans h1, pow_pos h0 n⟩
  · rwa [ne_eq, tsub_eq_zero_iff_le, not_le]
  · rwa [tsub_pos_iff_lt]

end Semifield

variable [Field K] [LinearOrder K] [IsStrictOrderedRing K] {x : K} {m n : Nat}

/--
lemma `geom_sum_Ico_le_of_lt_one` / 引理 `geom_sum_Ico_le_of_lt_one`

English:
lemma geom_sum_Ico_le_of_lt_one
  given: (hx : 0 <= x) (h'x : x < 1)
  proof: by
  rcases le_or_gt m n with (hmn | hmn)
  · rw [geom_sum_Ico' h'x.ne hmn]
    apply div_le_div₀ (pow_nonneg hx _) _ (sub_pos.2 h'x) le_rfl
    simpa using pow_nonneg hx _
  · rw [Ico_eq_empty, sum_empty]
    · apply div_nonneg (pow_nonneg hx _)
      simpa using h'x.le
    · simpa using hmn.le

中文:
引理 geom_sum_Ico_le_of_lt_one
  条件: (hx : 0 <= x) (h'x : x < 1)
  证明: by
  rcases le_or_gt m n with (hmn | hmn)
  · rw [geom_sum_Ico' h'x.ne hmn]
    apply div_le_div₀ (pow_nonneg hx _) _ (sub_pos.2 h'x) le_rfl
    simpa using pow_nonneg hx _
  · rw [Ico_eq_empty, sum_empty]
    · apply div_nonneg (pow_nonneg hx _)
      simpa using h'x.le
    · simpa using hmn.le

Depends on / 依赖: Ico_eq_empty, div_nonneg, geom_sum_Ico, hmn.le, le_or_gt, le_rfl, pow_nonneg, sub_pos, sum_empty, x.le, x.ne
-/
lemma geom_sum_Ico_le_of_lt_one (hx : 0 <= x) (h'x : x < 1) :
    ∑ i in Ico m n, x ^ i <= x ^ m / (1 - x) := by
  rcases le_or_gt m n with (hmn | hmn)
  · rw [geom_sum_Ico' h'x.ne hmn]
    apply div_le_div₀ (pow_nonneg hx _) _ (sub_pos.2 h'x) le_rfl
    simpa using pow_nonneg hx _
  · rw [Ico_eq_empty, sum_empty]
    · apply div_nonneg (pow_nonneg hx _)
      simpa using h'x.le
    · simpa using hmn.le
