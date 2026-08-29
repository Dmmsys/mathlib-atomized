/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg, Snir Broshi
-/
module

public import Mathlib.Analysis.Complex.IsIntegral
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.RingTheory.Polynomial.RationalRoot
public import Mathlib.NumberTheory.Real.Irrational
public import Mathlib.Tactic.Peel
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Qify

/-! # Niven's Theorem

This file proves Niven's theorem, stating that the only rational angles _in degrees_ which
also have rational cosines, are 0, 30 degrees, and 90 degrees - up to reflection and shifts
by π. Equivalently, the only rational numbers that occur as `cos(π * p / q)` are the five
values `{-1, -1/2, 0, 1/2, 1}`.
-/

public section

namespace IsIntegral

variable {α R : Type*} [DivisionRing α] [CharZero α] {q : Rat} {x : α}

@[simp]
/--
theorem `ratCast_iff` / 定理 `ratCast_iff`

English:
theorem ratCast_iff
  statement: IsIntegral Int (q : α) ↔ IsIntegral Int q
  proof: isIntegral_algebraMap_iff (FaithfulSMul.algebraMap_injective Rat α)

中文:
定理 ratCast_iff
  结论: 是整 整数 (q : α) ↔ 是整 整数 q
  证明: isIntegral_algebraMap_iff (FaithfulSMul.algebraMap_injective Rat α)

Depends on / 依赖: FaithfulSMul, FaithfulSMul.algebraMap_injective, algebraMap_injective, isIntegral_algebraMap_iff
-/
theorem ratCast_iff : IsIntegral Int (q : α) ↔ IsIntegral Int q :=
  isIntegral_algebraMap_iff (FaithfulSMul.algebraMap_injective Rat α)

/--
theorem `exists_int_iff_exists_rat` / 定理 `exists_int_iff_exists_rat`

English:
theorem exists_int_iff_exists_rat
  given: (h₁ : IsIntegral Int x)
  statement: (exists q : Rat, x = q) ↔ exists k : Int, x = k
  proof: by
  refine ⟨?_, fun ⟨w, h⟩ => ⟨w, by simp [h]⟩⟩
  rintro ⟨q, rfl⟩
  rw [ratCast_iff] at h₁
  peel IsIntegrallyClosed.algebraMap_eq_of_integral h₁ with h
  simp [← h]

中文:
定理 存在_int_iff_存在_rat
  条件: (h₁ : 是整 整数 x)
  结论: (存在 q : 有理数, x = q) ↔ 存在 k : 整数, x = k
  证明: by
  refine ⟨?_, fun ⟨w, h⟩ => ⟨w, by simp [h]⟩⟩
  rintro ⟨q, rfl⟩
  rw [ratCast_iff] at h₁
  peel IsIntegrallyClosed.algebraMap_eq_of_integral h₁ with h
  simp [← h]

Depends on / 依赖: IsIntegrallyClosed, IsIntegrallyClosed.algebraMap_eq_of_integral, algebraMap_eq_of_integral, ratCast_iff
-/
theorem exists_int_iff_exists_rat (h₁ : IsIntegral Int x) : (exists q : Rat, x = q) ↔ exists k : Int, x = k := by
  refine ⟨?_, fun ⟨w, h⟩ => ⟨w, by simp [h]⟩⟩
  rintro ⟨q, rfl⟩
  rw [ratCast_iff] at h₁
  peel IsIntegrallyClosed.algebraMap_eq_of_integral h₁ with h
  simp [← h]

end IsIntegral

variable {θ : Real}

open Real

section IsIntegral

namespace Complex

/--
lemma `exp_rat_mul_pi_mul_I_pow_two_mul_den` / 引理 `exp_rat_mul_pi_mul_I_pow_two_mul_den`

English:
lemma exp_rat_mul_pi_mul_I_pow_two_mul_den
  given: (q : Rat)
  statement: exp (q * π * I) ^ (2 * q.den) = 1
  proof: by
  nth_rw 1 [← q.num_div_den, ← exp_nat_mul]
  push_cast
  rw [show 2 * q.den * (q.num / q.den * π * I) = q.num * (2 * π * I) by field]; rw [exp_int_mul_two_pi_mul_I]

中文:
引理 exp_rat_mul_pi_mul_I_pow_two_mul_den
  条件: (q : 有理数)
  结论: exp (q * π * I) ^ (2 * q.den) = 1
  证明: by
  nth_rw 1 [← q.num_div_den, ← exp_nat_mul]
  push_cast
  rw [show 2 * q.den * (q.num / q.den * π * I) = q.num * (2 * π * I) by field]; rw [exp_int_mul_two_pi_mul_I]

Depends on / 依赖: exp_int_mul_two_pi_mul_I, exp_nat_mul, nth_rw, num_div_den, q.den, q.num, q.num_div_den
-/
lemma exp_rat_mul_pi_mul_I_pow_two_mul_den (q : Rat) : exp (q * π * I) ^ (2 * q.den) = 1 := by
  nth_rw 1 [← q.num_div_den, ← exp_nat_mul]
  push_cast
  rw [show 2 * q.den * (q.num / q.den * π * I) = q.num * (2 * π * I) by field]; rw [exp_int_mul_two_pi_mul_I]

/--
theorem `isIntegral_exp_rat_mul_pi_mul_I` / 定理 `isIntegral_exp_rat_mul_pi_mul_I`

English:
theorem isIntegral_exp_rat_mul_pi_mul_I
  given: (q : Rat)
  statement: IsIntegral Int exp q * π * I
  proof: by
  refine .of_pow (Nat.mul_pos zero_lt_two q.den_pos) ?_
  exact exp_rat_mul_pi_mul_I_pow_two_mul_den _ ▸ isIntegral_one

中文:
定理 is整数egral_exp_rat_mul_pi_mul_I
  条件: (q : 有理数)
  结论: 是整 整数 exp q * π * I
  证明: by
  refine .of_pow (Nat.mul_pos zero_lt_two q.den_pos) ?_
  exact exp_rat_mul_pi_mul_I_pow_two_mul_den _ ▸ isIntegral_one

Depends on / 依赖: Nat.mul_pos, den_pos, exp_rat_mul_pi_mul_I_pow_two_mul_den, isIntegral_one, mul_pos, of_pow, q.den_pos, zero_lt_two
-/
theorem isIntegral_exp_rat_mul_pi_mul_I (q : Rat) : IsIntegral Int exp q * π * I := by
  refine .of_pow (Nat.mul_pos zero_lt_two q.den_pos) ?_
  exact exp_rat_mul_pi_mul_I_pow_two_mul_den _ ▸ isIntegral_one

/--
theorem `isIntegral_exp_neg_rat_mul_pi_mul_I` / 定理 `isIntegral_exp_neg_rat_mul_pi_mul_I`

English:
theorem isIntegral_exp_neg_rat_mul_pi_mul_I
  given: (q : Rat)
  proof: by
  simpa using isIntegral_exp_rat_mul_pi_mul_I (-q)

中文:
定理 is整数egral_exp_neg_rat_mul_pi_mul_I
  条件: (q : 有理数)
  证明: by
  simpa using isIntegral_exp_rat_mul_pi_mul_I (-q)

Depends on / 依赖: isIntegral_exp_rat_mul_pi_mul_I
-/
theorem isIntegral_exp_neg_rat_mul_pi_mul_I (q : Rat) :
IsIntegral Int exp -(q * π) * I := by
  simpa using isIntegral_exp_rat_mul_pi_mul_I (-q)

/--
theorem `isIntegral_two_mul_sin_rat_mul_pi` / 定理 `isIntegral_two_mul_sin_rat_mul_pi`

English:
theorem isIntegral_two_mul_sin_rat_mul_pi
  given: (q : Rat)
  statement: IsIntegral Int 2 * sin (q * π)
  proof: by
  rw [sin.eq_1]; rw [mul_div_cancel₀ _ two_ne_zero]
  exact (isIntegral_exp_neg_rat_mul_pi_mul_I q).sub (isIntegral_exp_rat_mul_pi_mul_I q)
.mul isIntegral_int_I

中文:
定理 is整数egral_two_mul_sin_rat_mul_pi
  条件: (q : 有理数)
  结论: 是整 整数 2 * sin (q * π)
  证明: by
  rw [sin.eq_1]; rw [mul_div_cancel₀ _ two_ne_zero]
  exact (isIntegral_exp_neg_rat_mul_pi_mul_I q).sub (isIntegral_exp_rat_mul_pi_mul_I q)
.mul isIntegral_int_I

Depends on / 依赖: Embedding, Embedding.coeFn_mk, Finset, Finset.coe_map, Finset.pairwiseDisjoint_range_singleton.subset, Finset.sup_singleton_eq_self, PairwiseDisjoint, Set.PairwiseDisjoint.supIndep, Set.image_subset_range, bot_notMem, coeFn_mk, coe_map, eq_1, id_comp, image_subset_range, isIntegral_exp_neg_rat_mul_pi_mul_I, isIntegral_exp_rat_mul_pi_mul_I, isIntegral_int_I, pairwiseDisjoint_range_singleton, s.map
-/
theorem isIntegral_two_mul_sin_rat_mul_pi (q : Rat) : IsIntegral Int 2 * sin (q * π) := by
  rw [sin.eq_1]; rw [mul_div_cancel₀ _ two_ne_zero]
  exact (isIntegral_exp_neg_rat_mul_pi_mul_I q).sub (isIntegral_exp_rat_mul_pi_mul_I q)
.mul isIntegral_int_I

/--
theorem `isIntegral_two_mul_cos_rat_mul_pi` / 定理 `isIntegral_two_mul_cos_rat_mul_pi`

English:
theorem isIntegral_two_mul_cos_rat_mul_pi
  given: (q : Rat)
  statement: IsIntegral Int 2 * cos (q * π)
  proof: by
  rw [cos.eq_1]; rw [mul_div_cancel₀ _ two_ne_zero]
  exact (isIntegral_exp_rat_mul_pi_mul_I q).add (isIntegral_exp_neg_rat_mul_pi_mul_I q)

中文:
定理 is整数egral_two_mul_cos_rat_mul_pi
  条件: (q : 有理数)
  结论: 是整 整数 2 * cos (q * π)
  证明: by
  rw [cos.eq_1]; rw [mul_div_cancel₀ _ two_ne_zero]
  exact (isIntegral_exp_rat_mul_pi_mul_I q).add (isIntegral_exp_neg_rat_mul_pi_mul_I q)

Depends on / 依赖: cos.eq_1, eq_1, isIntegral_exp_neg_rat_mul_pi_mul_I, isIntegral_exp_rat_mul_pi_mul_I, two_ne_zero
-/
theorem isIntegral_two_mul_cos_rat_mul_pi (q : Rat) : IsIntegral Int 2 * cos (q * π) := by
  rw [cos.eq_1]; rw [mul_div_cancel₀ _ two_ne_zero]
  exact (isIntegral_exp_rat_mul_pi_mul_I q).add (isIntegral_exp_neg_rat_mul_pi_mul_I q)

/--
theorem `isAlgebraic_sin_rat_mul_pi` / 定理 `isAlgebraic_sin_rat_mul_pi`

English:
theorem isAlgebraic_sin_rat_mul_pi
  given: (q : Rat)
  statement: IsAlgebraic Int sin q * π
  proof: .of_mul (by simp) (isAlgebraic_algebraMap _) (isIntegral_two_mul_sin_rat_mul_pi q).isAlgebraic

中文:
定理 isAlgebraic_sin_rat_mul_pi
  条件: (q : 有理数)
  结论: 是代数 整数 sin q * π
  证明: .of_mul (by simp) (isAlgebraic_algebraMap _) (isIntegral_two_mul_sin_rat_mul_pi q).isAlgebraic

Depends on / 依赖: isAlgebraic, isAlgebraic_algebraMap, isIntegral_two_mul_sin_rat_mul_pi, of_mul
-/
theorem isAlgebraic_sin_rat_mul_pi (q : Rat) : IsAlgebraic Int sin q * π :=
  .of_mul (by simp) (isAlgebraic_algebraMap _) (isIntegral_two_mul_sin_rat_mul_pi q).isAlgebraic

/--
theorem `isAlgebraic_cos_rat_mul_pi` / 定理 `isAlgebraic_cos_rat_mul_pi`

English:
theorem isAlgebraic_cos_rat_mul_pi
  given: (q : Rat)
  statement: IsAlgebraic Int cos q * π
  proof: .of_mul (by simp) (isAlgebraic_algebraMap _) (isIntegral_two_mul_cos_rat_mul_pi q).isAlgebraic

中文:
定理 isAlgebraic_cos_rat_mul_pi
  条件: (q : 有理数)
  结论: 是代数 整数 cos q * π
  证明: .of_mul (by simp) (isAlgebraic_algebraMap _) (isIntegral_two_mul_cos_rat_mul_pi q).isAlgebraic

Depends on / 依赖: isAlgebraic, isAlgebraic_algebraMap, isIntegral_two_mul_cos_rat_mul_pi, of_mul
-/
theorem isAlgebraic_cos_rat_mul_pi (q : Rat) : IsAlgebraic Int cos q * π :=
  .of_mul (by simp) (isAlgebraic_algebraMap _) (isIntegral_two_mul_cos_rat_mul_pi q).isAlgebraic

/--
theorem `isAlgebraic_tan_rat_mul_pi` / 定理 `isAlgebraic_tan_rat_mul_pi`

English:
theorem isAlgebraic_tan_rat_mul_pi
  given: (q : Rat)
  statement: IsAlgebraic Int tan q * π
  proof: (isAlgebraic_sin_rat_mul_pi q).mul (isAlgebraic_cos_rat_mul_pi q).inv

中文:
定理 isAlgebraic_tan_rat_mul_pi
  条件: (q : 有理数)
  结论: 是代数 整数 tan q * π
  证明: (isAlgebraic_sin_rat_mul_pi q).mul (isAlgebraic_cos_rat_mul_pi q).inv

Depends on / 依赖: Finpartition, P.exists_mem, bot_le, exists_mem, isAlgebraic_cos_rat_mul_pi, isAlgebraic_sin_rat_mul_pi, mem_bot_iff, singleton_subset_iff
-/
theorem isAlgebraic_tan_rat_mul_pi (q : Rat) : IsAlgebraic Int tan q * π :=
  (isAlgebraic_sin_rat_mul_pi q).mul (isAlgebraic_cos_rat_mul_pi q).inv

end Complex

namespace Real

/--
theorem `isIntegral_two_mul_sin_rat_mul_pi` / 定理 `isIntegral_two_mul_sin_rat_mul_pi`

English:
theorem isIntegral_two_mul_sin_rat_mul_pi
  given: (q : Rat)
  statement: IsIntegral Int 2 * sin (q * π)
  proof: .mp by isIntegral_algebraMap_iff (B := Complex) RCLike.ofReal_injective
    simp [Complex.isIntegral_two_mul_sin_rat_mul_pi]

中文:
定理 is整数egral_two_mul_sin_rat_mul_pi
  条件: (q : 有理数)
  结论: 是整 整数 2 * sin (q * π)
  证明: .mp by isIntegral_algebraMap_iff (B := Complex) RCLike.ofReal_injective
    simp [Complex.isIntegral_two_mul_sin_rat_mul_pi]

Depends on / 依赖: Complex.isIntegral_two_mul_sin_rat_mul_pi, RCLike, RCLike.ofReal_injective, isIntegral_algebraMap_iff, isIntegral_two_mul_sin_rat_mul_pi, ofReal_injective
-/
theorem isIntegral_two_mul_sin_rat_mul_pi (q : Rat) : IsIntegral Int 2 * sin (q * π) :=
.mp by isIntegral_algebraMap_iff (B := Complex) RCLike.ofReal_injective
    simp [Complex.isIntegral_two_mul_sin_rat_mul_pi]

/--
theorem `isIntegral_two_mul_cos_rat_mul_pi` / 定理 `isIntegral_two_mul_cos_rat_mul_pi`

English:
theorem isIntegral_two_mul_cos_rat_mul_pi
  given: (q : Rat)
  statement: IsIntegral Int 2 * cos (q * π)
  proof: .mp by isIntegral_algebraMap_iff (B := Complex) RCLike.ofReal_injective
    simp [Complex.isIntegral_two_mul_cos_rat_mul_pi]

中文:
定理 is整数egral_two_mul_cos_rat_mul_pi
  条件: (q : 有理数)
  结论: 是整 整数 2 * cos (q * π)
  证明: .mp by isIntegral_algebraMap_iff (B := Complex) RCLike.ofReal_injective
    simp [Complex.isIntegral_two_mul_cos_rat_mul_pi]

Depends on / 依赖: Complex.isIntegral_two_mul_cos_rat_mul_pi, RCLike, RCLike.ofReal_injective, isIntegral_algebraMap_iff, isIntegral_two_mul_cos_rat_mul_pi, ofReal_injective
-/
theorem isIntegral_two_mul_cos_rat_mul_pi (q : Rat) : IsIntegral Int 2 * cos (q * π) :=
.mp by isIntegral_algebraMap_iff (B := Complex) RCLike.ofReal_injective
    simp [Complex.isIntegral_two_mul_cos_rat_mul_pi]

/--
theorem `isAlgebraic_sin_rat_mul_pi` / 定理 `isAlgebraic_sin_rat_mul_pi`

English:
theorem isAlgebraic_sin_rat_mul_pi
  given: (q : Rat)
  statement: IsAlgebraic Int sin q * π
  proof: .of_mul (by simp) (isAlgebraic_algebraMap _) (isIntegral_two_mul_sin_rat_mul_pi q).isAlgebraic

中文:
定理 isAlgebraic_sin_rat_mul_pi
  条件: (q : 有理数)
  结论: 是代数 整数 sin q * π
  证明: .of_mul (by simp) (isAlgebraic_algebraMap _) (isIntegral_two_mul_sin_rat_mul_pi q).isAlgebraic

Depends on / 依赖: isAlgebraic, isAlgebraic_algebraMap, isIntegral_two_mul_sin_rat_mul_pi, of_mul
-/
theorem isAlgebraic_sin_rat_mul_pi (q : Rat) : IsAlgebraic Int sin q * π :=
  .of_mul (by simp) (isAlgebraic_algebraMap _) (isIntegral_two_mul_sin_rat_mul_pi q).isAlgebraic

/--
theorem `isAlgebraic_cos_rat_mul_pi` / 定理 `isAlgebraic_cos_rat_mul_pi`

English:
theorem isAlgebraic_cos_rat_mul_pi
  given: (q : Rat)
  statement: IsAlgebraic Int cos q * π
  proof: .of_mul (by simp) (isAlgebraic_algebraMap _) (isIntegral_two_mul_cos_rat_mul_pi q).isAlgebraic

中文:
定理 isAlgebraic_cos_rat_mul_pi
  条件: (q : 有理数)
  结论: 是代数 整数 cos q * π
  证明: .of_mul (by simp) (isAlgebraic_algebraMap _) (isIntegral_two_mul_cos_rat_mul_pi q).isAlgebraic

Depends on / 依赖: isAlgebraic, isAlgebraic_algebraMap, isIntegral_two_mul_cos_rat_mul_pi, of_mul
-/
theorem isAlgebraic_cos_rat_mul_pi (q : Rat) : IsAlgebraic Int cos q * π :=
  .of_mul (by simp) (isAlgebraic_algebraMap _) (isIntegral_two_mul_cos_rat_mul_pi q).isAlgebraic

/--
theorem `isAlgebraic_tan_rat_mul_pi` / 定理 `isAlgebraic_tan_rat_mul_pi`

English:
theorem isAlgebraic_tan_rat_mul_pi
  given: (q : Rat)
  statement: IsAlgebraic Int tan q * π
  proof: .mp by isAlgebraic_algebraMap_iff (A := Complex) RCLike.ofReal_injective
    simp [Complex.isAlgebraic_tan_rat_mul_pi]

中文:
定理 isAlgebraic_tan_rat_mul_pi
  条件: (q : 有理数)
  结论: 是代数 整数 tan q * π
  证明: .mp by isAlgebraic_algebraMap_iff (A := Complex) RCLike.ofReal_injective
    simp [Complex.isAlgebraic_tan_rat_mul_pi]

Depends on / 依赖: Complex.isAlgebraic_tan_rat_mul_pi, RCLike, RCLike.ofReal_injective, isAlgebraic_algebraMap_iff, isAlgebraic_tan_rat_mul_pi, ofReal_injective
-/
theorem isAlgebraic_tan_rat_mul_pi (q : Rat) : IsAlgebraic Int tan q * π :=
.mp by isAlgebraic_algebraMap_iff (A := Complex) RCLike.ofReal_injective
    simp [Complex.isAlgebraic_tan_rat_mul_pi]

end Real

end IsIntegral

/--
theorem `niven` / 定理 `niven`

English:
theorem niven
  given: (hθ : exists r : Rat, θ = r * π) (hcos : exists q : Rat, cos θ = q)
  proof: by
  -- Since `2 cos θ ` is an algebraic integer and rational, it must be an integer.
  -- Hence, `2 cos θ ∈ {-2, -1, 0, 1, 2}`.
  obtain ⟨r, rfl⟩ := hθ
  obtain ⟨k, hk⟩ : exists k : Int, 2 * cos (r * π) = k := by
    rw [← (Real.isIntegral_two_mul_cos_rat_mul_pi r).exists_int_iff_exists_rat]
    ex

中文:
定理 niven
  条件: (hθ : 存在 r : 有理数, θ = r * π) (hcos : 存在 q : 有理数, cos θ = q)
  证明: by
  -- Since `2 cos θ ` is an algebraic integer and rational, it must be an integer.
  -- Hence, `2 cos θ ∈ {-2, -1, 0, 1, 2}`.
  obtain ⟨r, rfl⟩ := hθ
  obtain ⟨k, hk⟩ : exists k : Int, 2 * cos (r * π) = k := by
    rw [← (Real.isIntegral_two_mul_cos_rat_mul_pi r).exists_int_iff_exists_rat]
    ex
-/
theorem niven (hθ : exists r : Rat, θ = r * π) (hcos : exists q : Rat, cos θ = q) :
    cos θ in ({-1, -1 / 2, 0, 1 / 2, 1} : Set Real) := by
  -- Since `2 cos θ ` is an algebraic integer and rational, it must be an integer.
  -- Hence, `2 cos θ ∈ {-2, -1, 0, 1, 2}`.
  obtain ⟨r, rfl⟩ := hθ
  obtain ⟨k, hk⟩ : exists k : Int, 2 * cos (r * π) = k := by
    rw [← (Real.isIntegral_two_mul_cos_rat_mul_pi r).exists_int_iff_exists_rat]
    exact ⟨2 * hcos.choose, by push_cast; linarith [hcos.choose_spec]⟩
  -- Since k is an integer and `2 * cos (w * pi) = k`, we have $k ∈ {-2, -1, 0, 1, 2}$.
  have hk_values : k in Finset.Icc (-2 : Int) 2 := by
    rw [Finset.mem_Icc]
    rify
    constructor <;> linarith [hk, (r * π).neg_one_le_cos, (r * π).cos_le_one]
  rw [show cos (r * π) = k / 2 by grind]
  fin_cases hk_values <;> simp

/--
theorem `niven_sin` / 定理 `niven_sin`

English:
theorem niven_sin
  given: (hθ : exists r : Rat, θ = r * π) (hcos : exists q : Rat, sin θ = q)
  proof: by
  convert! ← niven (θ := θ - π / 2) ?_ ?_ using 1
  · exact cos_sub_pi_div_two θ
  · exact hθ.imp' (· - 1 / 2) (by intros; push_cast; linarith)
  · simpa [cos_sub_pi_div_two]

中文:
定理 niven_sin
  条件: (hθ : 存在 r : 有理数, θ = r * π) (hcos : 存在 q : 有理数, sin θ = q)
  证明: by
  convert! ← niven (θ := θ - π / 2) ?_ ?_ using 1
  · exact cos_sub_pi_div_two θ
  · exact hθ.imp' (· - 1 / 2) (by intros; push_cast; linarith)
  · simpa [cos_sub_pi_div_two]

Depends on / 依赖: convert, cos_sub_pi_div_two, intros
-/
theorem niven_sin (hθ : exists r : Rat, θ = r * π) (hcos : exists q : Rat, sin θ = q) :
    sin θ in ({-1, -1 / 2, 0, 1 / 2, 1} : Set Real) := by
  convert! ← niven (θ := θ - π / 2) ?_ ?_ using 1
  · exact cos_sub_pi_div_two θ
  · exact hθ.imp' (· - 1 / 2) (by intros; push_cast; linarith)
  · simpa [cos_sub_pi_div_two]

/--
theorem `niven_angle_eq` / 定理 `niven_angle_eq`

English:
theorem niven_angle_eq
  statement: (hθ : exists r : Rat, θ = r * π) (hcos : exists q : Rat, cos θ = q)
  proof: by
  rcases niven hθ hcos with h | h | h | h | h <;>
  -- define `h₂` appropriately for each proof branch
  [have h₂ := cos_pi;
    have h₂ : cos (π * (2 / 3)) = -1 / 2 := by
      have := cos_pi_sub (π / 3)
      have := cos_pi_div_three
      grind;;
    have h₂ := cos_pi_div_two;
    have h₂ := c

中文:
定理 niven_angle_eq
  结论: (hθ : 存在 r : 有理数, θ = r * π) (hcos : 存在 q : 有理数, cos θ = q)
  证明: by
  rcases niven hθ hcos with h | h | h | h | h <;>
  -- define `h₂` appropriately for each proof branch
  [have h₂ := cos_pi;
    have h₂ : cos (π * (2 / 3)) = -1 / 2 := by
      have := cos_pi_sub (π / 3)
      have := cos_pi_div_three
      grind;;
    have h₂ := cos_pi_div_two;
    have h₂ := c
-/
theorem niven_angle_eq (hθ : exists r : Rat, θ = r * π) (hcos : exists q : Rat, cos θ = q)
    (h_bnd : θ in Set.Icc 0 π) : θ in ({0, π / 3, π / 2, π * (2 / 3), π} : Set Real) := by
  rcases niven hθ hcos with h | h | h | h | h <;>
  -- define `h₂` appropriately for each proof branch
  [have h₂ := cos_pi;
    have h₂ : cos (π * (2 / 3)) = -1 / 2 := by
      have := cos_pi_sub (π / 3)
      have := cos_pi_div_three
      grind;;
    have h₂ := cos_pi_div_two;
    have h₂ := cos_pi_div_three;
    have h₂ := cos_zero] <;>
  simp [injOn_cos h_bnd ⟨by positivity, by linarith [pi_nonneg]⟩ (h₂ ▸ h)]

/--
theorem `niven_angle_div_pi_eq` / 定理 `niven_angle_div_pi_eq`

English:
theorem niven_angle_div_pi_eq
  statement: {r : Rat} (hcos : exists q : Rat, cos (r * π) = q)
  proof: by
.mem_set_image.mp apply smul_left_injective Rat pi_ne_zero
  replace h_bnd : (r : Real) * π in Set.Icc (0 * π) (1 * π) := by
    obtain ⟨hr, hr'⟩ := h_bnd; constructor <;> gcongr <;> norm_cast
  generalize h : (r : Real) * π = θ at *
  have := niven_angle_eq ⟨r, h.symm⟩ hcos (by simpa using h_bnd

中文:
定理 niven_angle_div_pi_eq
  结论: {r : 有理数} (hcos : 存在 q : 有理数, cos (r * π) = q)
  证明: by
.mem_set_image.mp apply smul_left_injective Rat pi_ne_zero
  replace h_bnd : (r : Real) * π in Set.Icc (0 * π) (1 * π) := by
    obtain ⟨hr, hr'⟩ := h_bnd; constructor <;> gcongr <;> norm_cast
  generalize h : (r : Real) * π = θ at *
  have := niven_angle_eq ⟨r, h.symm⟩ hcos (by simpa using h_bnd

Depends on / 依赖: Rat.smul_def, Set.Icc, generalize, h.symm, h_bnd, mem_set_image, mem_set_image.mp, niven_angle_eq, pi_ne_zero, replace, smul_def, smul_left_injective
-/
theorem niven_angle_div_pi_eq {r : Rat} (hcos : exists q : Rat, cos (r * π) = q)
    (h_bnd : r in Set.Icc 0 1) : r in ({0, 1 / 3, 1 / 2, 2 / 3, 1} : Set Rat) := by
.mem_set_image.mp apply smul_left_injective Rat pi_ne_zero
  replace h_bnd : (r : Real) * π in Set.Icc (0 * π) (1 * π) := by
    obtain ⟨hr, hr'⟩ := h_bnd; constructor <;> gcongr <;> norm_cast
  generalize h : (r : Real) * π = θ at *
  have := niven_angle_eq ⟨r, h.symm⟩ hcos (by simpa using h_bnd)
  simp_all [Rat.smul_def]
  grind

/--
theorem `niven_fract_angle_div_pi_eq` / 定理 `niven_fract_angle_div_pi_eq`

English:
theorem niven_fract_angle_div_pi_eq
  given: {r : Rat} (hcos : exists q : Rat, cos (r * π) = q)
  proof: by
  suffices Int.fract r in ({0, 1 / 3, 1 / 2, 2 / 3, 1} : Set Rat) by
    grind [ne_of_lt (Int.fract_lt_one r)]
  refine niven_angle_div_pi_eq (r := Int.fract r) ?_ (by simp [le_of_lt <| Int.fract_lt_one r])
  obtain ⟨q, hq⟩ := hcos
  exact ⟨(-1) ^ ⌊r⌋ * q, by rw [Int.fract]; push_cast; rw [sub_mu

中文:
定理 niven_fract_angle_div_pi_eq
  条件: {r : 有理数} (hcos : 存在 q : 有理数, cos (r * π) = q)
  证明: by
  suffices Int.fract r in ({0, 1 / 3, 1 / 2, 2 / 3, 1} : Set Rat) by
    grind [ne_of_lt (Int.fract_lt_one r)]
  refine niven_angle_div_pi_eq (r := Int.fract r) ?_ (by simp [le_of_lt <| Int.fract_lt_one r])
  obtain ⟨q, hq⟩ := hcos
  exact ⟨(-1) ^ ⌊r⌋ * q, by rw [Int.fract]; push_cast; rw [sub_mu

Depends on / 依赖: Int.fract, Int.fract_lt_one, cos_sub_int_mul_pi, fract_lt_one, le_of_lt, ne_of_lt, niven_angle_div_pi_eq, sub_mul
-/
theorem niven_fract_angle_div_pi_eq {r : Rat} (hcos : exists q : Rat, cos (r * π) = q) :
    Int.fract r in ({0, 1 / 3, 1 / 2, 2 / 3} : Set Rat) := by
  suffices Int.fract r in ({0, 1 / 3, 1 / 2, 2 / 3, 1} : Set Rat) by
    grind [ne_of_lt (Int.fract_lt_one r)]
  refine niven_angle_div_pi_eq (r := Int.fract r) ?_ (by simp [le_of_lt <| Int.fract_lt_one r])
  obtain ⟨q, hq⟩ := hcos
  exact ⟨(-1) ^ ⌊r⌋ * q, by rw [Int.fract]; push_cast; rw [sub_mul, cos_sub_int_mul_pi, hq]⟩

/--
theorem `irrational_cos_rat_mul_pi` / 定理 `irrational_cos_rat_mul_pi`

English:
theorem irrational_cos_rat_mul_pi
  given: {r : Rat} (hr : 3 < r.den)
  proof: by
  rw [← Rat.den_intFract] at hr
  by_contra! hnz
  rcases niven_fract_angle_div_pi_eq (exists_rat_of_not_irrational hnz) with (hr' | hr' | hr' | hr')
  all_goals (try rw [Set.mem_singleton_iff] at hr'); rw [hr'] at hr; norm_num at hr

中文:
定理 irrational_cos_rat_mul_pi
  条件: {r : 有理数} (hr : 3 < r.den)
  证明: by
  rw [← Rat.den_intFract] at hr
  by_contra! hnz
  rcases niven_fract_angle_div_pi_eq (exists_rat_of_not_irrational hnz) with (hr' | hr' | hr' | hr')
  all_goals (try rw [Set.mem_singleton_iff] at hr'); rw [hr'] at hr; norm_num at hr

Depends on / 依赖: Rat.den_intFract, Set.mem_singleton_iff, all_goals, den_intFract, exists_rat_of_not_irrational, mem_singleton_iff, niven_fract_angle_div_pi_eq
-/
theorem irrational_cos_rat_mul_pi {r : Rat} (hr : 3 < r.den) :
    Irrational (cos (r * π)) := by
  rw [← Rat.den_intFract] at hr
  by_contra! hnz
  rcases niven_fract_angle_div_pi_eq (exists_rat_of_not_irrational hnz) with (hr' | hr' | hr' | hr')
  all_goals (try rw [Set.mem_singleton_iff] at hr'); rw [hr'] at hr; norm_num at hr
