/-
Copyright (c) 2023 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser, Yaël Dillies
-/
module

public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# Trigonometric functions as sums of infinite series

In this file we express trigonometric functions in terms of their series expansion.

## Main results

* `Complex.hasSum_cos`, `Complex.cos_eq_tsum`: `Complex.cos` as the sum of an infinite series.
* `Real.hasSum_cos`, `Real.cos_eq_tsum`: `Real.cos` as the sum of an infinite series.
* `Complex.hasSum_sin`, `Complex.sin_eq_tsum`: `Complex.sin` as the sum of an infinite series.
* `Real.hasSum_sin`, `Real.sin_eq_tsum`: `Real.sin` as the sum of an infinite series.
-/

public section

open NormedSpace

open scoped Nat

/-! ### `cos` and `sin` for `ℝ` and `ℂ` -/


section SinCos

set_option backward.defeqAttrib.useBackward true in
/--
theorem `Complex.hasSum_cos'` / 定理 `Complex.hasSum_cos'`

English:
theorem Complex.hasSum_cos'
  given: (z : Complex)
  proof: by
  rw [Complex.cos]; rw [Complex.exp_eq_exp_Complex]
  have := ((expSeries_div_hasSum_exp (z * Complex.I)).add
    (expSeries_div_hasSum_exp (-z * Complex.I))).div_const 2
  replace := (Nat.divModEquiv 2).symm.hasSum_iff.mpr this
  dsimp [Function.comp_def] at this
  simp_rw [← mul_comm 2 _] at this
  refine this.prod_fiberwise fun k => ?_
  dsimp only
  convert! hasSum_fintype (_ : Fin 2 -> Complex) using 1
  rw [Fin.sum_univ_two]
  simp_rw [Fin.val_zero, Fin.val_one, add_zero, pow_succ, pow_mul, mul_pow, neg_sq, ← two_mul,
    neg_mul, mul_neg, neg_div, add_neg_cancel, zero_div, add_zero,
    mul_div_cancel_left₀ _ (two_ne_zero : (2 : Complex) != 0)]

中文:
定理 复形.hasSum_cos'
  条件: (z : 复形)
  证明: by
  rw [Complex.cos]; rw [Complex.exp_eq_exp_Complex]
  have := ((expSeries_div_hasSum_exp (z * Complex.I)).add
    (expSeries_div_hasSum_exp (-z * Complex.I))).div_const 2
  replace := (Nat.divModEquiv 2).symm.hasSum_iff.mpr this
  dsimp [Function.comp_def] at this
  simp_rw [← mul_comm 2 _] at this
  refine this.prod_fiberwise fun k => ?_
  dsimp only
  convert! hasSum_fintype (_ : Fin 2 -> Complex) using 1
  rw [Fin.sum_univ_two]
  simp_rw [Fin.val_zero, Fin.val_one, add_zero, pow_succ, pow_mul, mul_pow, neg_sq, ← two_mul,
    neg_mul, mul_neg, neg_div, add_neg_cancel, zero_div, add_zero,
    mul_div_cancel_left₀ _ (two_ne_zero : (2 : Complex) != 0)]

Depends on / 依赖: Complex.I, Complex.cos, Complex.exp_eq_exp_Complex, Fin.sum_univ_two, Fin.val_one, Fin.val_zero, Function, Function.comp_def, Nat.divModEquiv, add_zero, comp_def, convert, divModEquiv, div_const, expSeries_div_hasSum_exp, exp_eq_exp_Complex, hasSum_fintype, hasSum_iff, mul_comm, mul_pow
-/
theorem Complex.hasSum_cos' (z : Complex) :
    HasSum (fun n : Nat => (z * Complex.I) ^ (2 * n) / ↑(2 * n)!) (Complex.cos z) := by
  rw [Complex.cos]; rw [Complex.exp_eq_exp_Complex]
  have := ((expSeries_div_hasSum_exp (z * Complex.I)).add
    (expSeries_div_hasSum_exp (-z * Complex.I))).div_const 2
  replace := (Nat.divModEquiv 2).symm.hasSum_iff.mpr this
  dsimp [Function.comp_def] at this
  simp_rw [← mul_comm 2 _] at this
  refine this.prod_fiberwise fun k => ?_
  dsimp only
  convert! hasSum_fintype (_ : Fin 2 -> Complex) using 1
  rw [Fin.sum_univ_two]
  simp_rw [Fin.val_zero, Fin.val_one, add_zero, pow_succ, pow_mul, mul_pow, neg_sq, ← two_mul,
    neg_mul, mul_neg, neg_div, add_neg_cancel, zero_div, add_zero,
    mul_div_cancel_left₀ _ (two_ne_zero : (2 : Complex) != 0)]

set_option backward.defeqAttrib.useBackward true in
/--
theorem `Complex.hasSum_sin'` / 定理 `Complex.hasSum_sin'`

English:
theorem Complex.hasSum_sin'
  given: (z : Complex)
  proof: by
  rw [Complex.sin]; rw [Complex.exp_eq_exp_Complex]
  have := (((expSeries_div_hasSum_exp (-z * Complex.I)).sub
    (expSeries_div_hasSum_exp (z * Complex.I))).mul_right Complex.I).div_const 2
  replace := (Nat.divModEquiv 2).symm.hasSum_iff.mpr this
  dsimp [Function.comp_def] at this
  simp_rw [← mul_comm 2 _] at this
  refine this.prod_fiberwise fun k => ?_
  dsimp only
  convert! hasSum_fintype (_ : Fin 2 -> Complex) using 1
  rw [Fin.sum_univ_two]
  simp_rw [Fin.val_zero, Fin.val_one, add_zero, pow_succ, pow_mul, mul_pow, neg_sq, sub_self,
    zero_mul, zero_div, zero_add, neg_mul, mul_neg, neg_div, ← neg_add', ← two_mul,
    neg_mul, neg_div, mul_assoc, mul_div_cancel_left₀ _ (two_ne_zero : (2 : Complex) != 0), Complex.div_I]

中文:
定理 复形.hasSum_sin'
  条件: (z : 复形)
  证明: by
  rw [Complex.sin]; rw [Complex.exp_eq_exp_Complex]
  have := (((expSeries_div_hasSum_exp (-z * Complex.I)).sub
    (expSeries_div_hasSum_exp (z * Complex.I))).mul_right Complex.I).div_const 2
  replace := (Nat.divModEquiv 2).symm.hasSum_iff.mpr this
  dsimp [Function.comp_def] at this
  simp_rw [← mul_comm 2 _] at this
  refine this.prod_fiberwise fun k => ?_
  dsimp only
  convert! hasSum_fintype (_ : Fin 2 -> Complex) using 1
  rw [Fin.sum_univ_two]
  simp_rw [Fin.val_zero, Fin.val_one, add_zero, pow_succ, pow_mul, mul_pow, neg_sq, sub_self,
    zero_mul, zero_div, zero_add, neg_mul, mul_neg, neg_div, ← neg_add', ← two_mul,
    neg_mul, neg_div, mul_assoc, mul_div_cancel_left₀ _ (two_ne_zero : (2 : Complex) != 0), Complex.div_I]

Depends on / 依赖: Complex.I, Complex.exp_eq_exp_Complex, Complex.sin, Fin.sum_univ_two, Fin.val_one, Fin.val_zero, Function, Function.comp_def, Nat.divModEquiv, add_zero, comp_def, convert, divModEquiv, div_const, expSeries_div_hasSum_exp, exp_eq_exp_Complex, hasSum_fintype, hasSum_iff, mul_comm, mul_right
-/
theorem Complex.hasSum_sin' (z : Complex) :
    HasSum (fun n : Nat => (z * Complex.I) ^ (2 * n + 1) / ↑(2 * n + 1)! / Complex.I)
      (Complex.sin z) := by
  rw [Complex.sin]; rw [Complex.exp_eq_exp_Complex]
  have := (((expSeries_div_hasSum_exp (-z * Complex.I)).sub
    (expSeries_div_hasSum_exp (z * Complex.I))).mul_right Complex.I).div_const 2
  replace := (Nat.divModEquiv 2).symm.hasSum_iff.mpr this
  dsimp [Function.comp_def] at this
  simp_rw [← mul_comm 2 _] at this
  refine this.prod_fiberwise fun k => ?_
  dsimp only
  convert! hasSum_fintype (_ : Fin 2 -> Complex) using 1
  rw [Fin.sum_univ_two]
  simp_rw [Fin.val_zero, Fin.val_one, add_zero, pow_succ, pow_mul, mul_pow, neg_sq, sub_self,
    zero_mul, zero_div, zero_add, neg_mul, mul_neg, neg_div, ← neg_add', ← two_mul,
    neg_mul, neg_div, mul_assoc, mul_div_cancel_left₀ _ (two_ne_zero : (2 : Complex) != 0), Complex.div_I]

/--
theorem `Complex.hasSum_cos` / 定理 `Complex.hasSum_cos`

English:
theorem Complex.hasSum_cos
  given: (z : Complex)
  proof: by
  convert! Complex.hasSum_cos' z using 1
  simp_rw [mul_pow, pow_mul, Complex.I_sq, mul_comm]

中文:
定理 复形.hasSum_cos
  条件: (z : 复形)
  证明: by
  convert! Complex.hasSum_cos' z using 1
  simp_rw [mul_pow, pow_mul, Complex.I_sq, mul_comm]

Depends on / 依赖: Complex.I_sq, Complex.hasSum_cos, I_sq, convert, hasSum_cos, mul_comm, mul_pow, pow_mul, simp_rw
-/
theorem Complex.hasSum_cos (z : Complex) :
    HasSum (fun n : Nat => (-1) ^ n * z ^ (2 * n) / ↑(2 * n)!) (Complex.cos z) := by
  convert! Complex.hasSum_cos' z using 1
  simp_rw [mul_pow, pow_mul, Complex.I_sq, mul_comm]

/--
theorem `Complex.hasSum_sin` / 定理 `Complex.hasSum_sin`

English:
theorem Complex.hasSum_sin
  given: (z : Complex)
  proof: by
  convert! Complex.hasSum_sin' z using 1
  simp_rw [mul_pow, pow_succ, pow_mul, Complex.I_sq, ← mul_assoc, mul_div_assoc, div_right_comm,
    div_self Complex.I_ne_zero, mul_comm _ ((-1 : Complex) ^ _), mul_one_div, mul_div_assoc, mul_assoc]

中文:
定理 复形.hasSum_sin
  条件: (z : 复形)
  证明: by
  convert! Complex.hasSum_sin' z using 1
  simp_rw [mul_pow, pow_succ, pow_mul, Complex.I_sq, ← mul_assoc, mul_div_assoc, div_right_comm,
    div_self Complex.I_ne_zero, mul_comm _ ((-1 : Complex) ^ _), mul_one_div, mul_div_assoc, mul_assoc]

Depends on / 依赖: Complex.I_ne_zero, Complex.I_sq, Complex.hasSum_sin, I_ne_zero, I_sq, convert, div_right_comm, div_self, hasSum_sin, mul_assoc, mul_comm, mul_div_assoc, mul_one_div, mul_pow, pow_mul, pow_succ, simp_rw
-/
theorem Complex.hasSum_sin (z : Complex) :
    HasSum (fun n : Nat => (-1) ^ n * z ^ (2 * n + 1) / ↑(2 * n + 1)!) (Complex.sin z) := by
  convert! Complex.hasSum_sin' z using 1
  simp_rw [mul_pow, pow_succ, pow_mul, Complex.I_sq, ← mul_assoc, mul_div_assoc, div_right_comm,
    div_self Complex.I_ne_zero, mul_comm _ ((-1 : Complex) ^ _), mul_one_div, mul_div_assoc, mul_assoc]

/--
theorem `Complex.cos_eq_tsum'` / 定理 `Complex.cos_eq_tsum'`

English:
theorem Complex.cos_eq_tsum'
  given: (z : Complex)
  proof: (Complex.hasSum_cos' z).tsum_eq.symm

中文:
定理 复形.cos_eq_tsum'
  条件: (z : 复形)
  证明: (Complex.hasSum_cos' z).tsum_eq.symm

Depends on / 依赖: Complex.hasSum_cos, hasSum_cos, tsum_eq, tsum_eq.symm
-/
theorem Complex.cos_eq_tsum' (z : Complex) :
    Complex.cos z = ∑' n : Nat, (z * Complex.I) ^ (2 * n) / ↑(2 * n)! :=
  (Complex.hasSum_cos' z).tsum_eq.symm

/--
theorem `Complex.sin_eq_tsum'` / 定理 `Complex.sin_eq_tsum'`

English:
theorem Complex.sin_eq_tsum'
  given: (z : Complex)
  proof: (Complex.hasSum_sin' z).tsum_eq.symm

中文:
定理 复形.sin_eq_tsum'
  条件: (z : 复形)
  证明: (Complex.hasSum_sin' z).tsum_eq.symm

Depends on / 依赖: Complex.hasSum_sin, hasSum_sin, tsum_eq, tsum_eq.symm
-/
theorem Complex.sin_eq_tsum' (z : Complex) :
    Complex.sin z = ∑' n : Nat, (z * Complex.I) ^ (2 * n + 1) / ↑(2 * n + 1)! / Complex.I :=
  (Complex.hasSum_sin' z).tsum_eq.symm

/--
theorem `Complex.cos_eq_tsum` / 定理 `Complex.cos_eq_tsum`

English:
theorem Complex.cos_eq_tsum
  given: (z : Complex)
  proof: (Complex.hasSum_cos z).tsum_eq.symm

中文:
定理 复形.cos_eq_tsum
  条件: (z : 复形)
  证明: (Complex.hasSum_cos z).tsum_eq.symm

Depends on / 依赖: Complex.hasSum_cos, hasSum_cos, tsum_eq, tsum_eq.symm
-/
theorem Complex.cos_eq_tsum (z : Complex) :
    Complex.cos z = ∑' n : Nat, (-1) ^ n * z ^ (2 * n) / ↑(2 * n)! :=
  (Complex.hasSum_cos z).tsum_eq.symm

/--
theorem `Complex.sin_eq_tsum` / 定理 `Complex.sin_eq_tsum`

English:
theorem Complex.sin_eq_tsum
  given: (z : Complex)
  proof: (Complex.hasSum_sin z).tsum_eq.symm

中文:
定理 复形.sin_eq_tsum
  条件: (z : 复形)
  证明: (Complex.hasSum_sin z).tsum_eq.symm

Depends on / 依赖: Complex.hasSum_sin, hasSum_sin, tsum_eq, tsum_eq.symm
-/
theorem Complex.sin_eq_tsum (z : Complex) :
    Complex.sin z = ∑' n : Nat, (-1) ^ n * z ^ (2 * n + 1) / ↑(2 * n + 1)! :=
  (Complex.hasSum_sin z).tsum_eq.symm

/--
theorem `Real.hasSum_cos` / 定理 `Real.hasSum_cos`

English:
theorem Real.hasSum_cos
  given: (r : Real)
  proof: mod_cast Complex.hasSum_cos r

中文:
定理 实数.hasSum_cos
  条件: (r : 实数)
  证明: mod_cast Complex.hasSum_cos r

Depends on / 依赖: Complex.hasSum_cos, hasSum_cos, mod_cast
-/
theorem Real.hasSum_cos (r : Real) :
    HasSum (fun n : Nat => (-1) ^ n * r ^ (2 * n) / ↑(2 * n)!) (Real.cos r) :=
  mod_cast Complex.hasSum_cos r

/--
theorem `Real.hasSum_sin` / 定理 `Real.hasSum_sin`

English:
theorem Real.hasSum_sin
  given: (r : Real)
  proof: mod_cast Complex.hasSum_sin r

中文:
定理 实数.hasSum_sin
  条件: (r : 实数)
  证明: mod_cast Complex.hasSum_sin r

Depends on / 依赖: Complex.hasSum_sin, hasSum_sin, mod_cast
-/
theorem Real.hasSum_sin (r : Real) :
    HasSum (fun n : Nat => (-1) ^ n * r ^ (2 * n + 1) / ↑(2 * n + 1)!) (Real.sin r) :=
  mod_cast Complex.hasSum_sin r

/--
theorem `Real.cos_eq_tsum` / 定理 `Real.cos_eq_tsum`

English:
theorem Real.cos_eq_tsum
  given: (r : Real)
  statement: Real.cos r = ∑' n : Nat, (-1) ^ n * r ^ (2 * n) / ↑(2 * n)!
  proof: (Real.hasSum_cos r).tsum_eq.symm

中文:
定理 实数.cos_eq_tsum
  条件: (r : 实数)
  结论: 实数.cos r = ∑' n : 自然数, (-1) ^ n * r ^ (2 * n) / ↑(2 * n)!
  证明: (Real.hasSum_cos r).tsum_eq.symm

Depends on / 依赖: Real.hasSum_cos, hasSum_cos, tsum_eq, tsum_eq.symm
-/
theorem Real.cos_eq_tsum (r : Real) : Real.cos r = ∑' n : Nat, (-1) ^ n * r ^ (2 * n) / ↑(2 * n)! :=
  (Real.hasSum_cos r).tsum_eq.symm

/--
theorem `Real.sin_eq_tsum` / 定理 `Real.sin_eq_tsum`

English:
theorem Real.sin_eq_tsum
  given: (r : Real)
  proof: (Real.hasSum_sin r).tsum_eq.symm

中文:
定理 实数.sin_eq_tsum
  条件: (r : 实数)
  证明: (Real.hasSum_sin r).tsum_eq.symm

Depends on / 依赖: Real.hasSum_sin, hasSum_sin, tsum_eq, tsum_eq.symm
-/
theorem Real.sin_eq_tsum (r : Real) :
    Real.sin r = ∑' n : Nat, (-1) ^ n * r ^ (2 * n + 1) / ↑(2 * n + 1)! :=
  (Real.hasSum_sin r).tsum_eq.symm

end SinCos

/-! ### `cosh` and `sinh` for `ℝ` and `ℂ` -/

section SinhCosh
namespace Complex

/--
lemma `hasSum_cosh` / 引理 `hasSum_cosh`

English:
lemma hasSum_cosh
  given: (z : Complex)
  statement: HasSum (fun n => z ^ (2 * n) / ↑(2 * n)!) (cosh z)
  proof: by
  simpa [mul_assoc, cos_mul_I] using hasSum_cos' (z * I)

中文:
引理 hasSum_cosh
  条件: (z : 复形)
  结论: HasSum (fun n => z ^ (2 * n) / ↑(2 * n)!) (cosh z)
  证明: by
  simpa [mul_assoc, cos_mul_I] using hasSum_cos' (z * I)

Depends on / 依赖: cos_mul_I, hasSum_cos, mul_assoc
-/
lemma hasSum_cosh (z : Complex) : HasSum (fun n => z ^ (2 * n) / ↑(2 * n)!) (cosh z) := by
  simpa [mul_assoc, cos_mul_I] using hasSum_cos' (z * I)

/--
lemma `hasSum_sinh` / 引理 `hasSum_sinh`

English:
lemma hasSum_sinh
  given: (z : Complex)
  statement: HasSum (fun n => z ^ (2 * n + 1) / ↑(2 * n + 1)!) (sinh z)
  proof: by
  simpa [mul_assoc, sin_mul_I, neg_pow z, pow_add, pow_mul, neg_mul, neg_div]
    using (hasSum_sin' (z * I)).mul_right (-I)

中文:
引理 hasSum_sinh
  条件: (z : 复形)
  结论: HasSum (fun n => z ^ (2 * n + 1) / ↑(2 * n + 1)!) (sinh z)
  证明: by
  simpa [mul_assoc, sin_mul_I, neg_pow z, pow_add, pow_mul, neg_mul, neg_div]
    using (hasSum_sin' (z * I)).mul_right (-I)

Depends on / 依赖: hasSum_sin, mul_assoc, mul_right, neg_div, neg_mul, neg_pow, pow_add, pow_mul, sin_mul_I
-/
lemma hasSum_sinh (z : Complex) : HasSum (fun n => z ^ (2 * n + 1) / ↑(2 * n + 1)!) (sinh z) := by
  simpa [mul_assoc, sin_mul_I, neg_pow z, pow_add, pow_mul, neg_mul, neg_div]
    using (hasSum_sin' (z * I)).mul_right (-I)

/--
lemma `cosh_eq_tsum` / 引理 `cosh_eq_tsum`

English:
lemma cosh_eq_tsum
  given: (z : Complex)
  statement: cosh z = ∑' n, z ^ (2 * n) / ↑(2 * n)!
  proof: z.hasSum_cosh.tsum_eq.symm

中文:
引理 cosh_eq_tsum
  条件: (z : 复形)
  结论: cosh z = ∑' n, z ^ (2 * n) / ↑(2 * n)!
  证明: z.hasSum_cosh.tsum_eq.symm

Depends on / 依赖: hasSum_cosh, tsum_eq, z.hasSum_cosh.tsum_eq.symm
-/
lemma cosh_eq_tsum (z : Complex) : cosh z = ∑' n, z ^ (2 * n) / ↑(2 * n)! := z.hasSum_cosh.tsum_eq.symm

/--
lemma `sinh_eq_tsum` / 引理 `sinh_eq_tsum`

English:
lemma sinh_eq_tsum
  given: (z : Complex)
  statement: sinh z = ∑' n, z ^ (2 * n + 1) / ↑(2 * n + 1)!
  proof: z.hasSum_sinh.tsum_eq.symm

中文:
引理 sinh_eq_tsum
  条件: (z : 复形)
  结论: sinh z = ∑' n, z ^ (2 * n + 1) / ↑(2 * n + 1)!
  证明: z.hasSum_sinh.tsum_eq.symm

Depends on / 依赖: hasSum_sinh, tsum_eq, z.hasSum_sinh.tsum_eq.symm
-/
lemma sinh_eq_tsum (z : Complex) : sinh z = ∑' n, z ^ (2 * n + 1) / ↑(2 * n + 1)! :=
  z.hasSum_sinh.tsum_eq.symm

end Complex

namespace Real

/--
lemma `hasSum_cosh` / 引理 `hasSum_cosh`

English:
lemma hasSum_cosh
  given: (r : Real)
  statement: HasSum (fun n => r ^ (2 * n) / ↑(2 * n)!) (cosh r)
  proof: mod_cast Complex.hasSum_cosh r

中文:
引理 hasSum_cosh
  条件: (r : 实数)
  结论: HasSum (fun n => r ^ (2 * n) / ↑(2 * n)!) (cosh r)
  证明: mod_cast Complex.hasSum_cosh r

Depends on / 依赖: Complex.hasSum_cosh, hasSum_cosh, mod_cast
-/
lemma hasSum_cosh (r : Real) : HasSum (fun n => r ^ (2 * n) / ↑(2 * n)!) (cosh r) :=
  mod_cast Complex.hasSum_cosh r

/--
lemma `hasSum_sinh` / 引理 `hasSum_sinh`

English:
lemma hasSum_sinh
  given: (r : Real)
  statement: HasSum (fun n => r ^ (2 * n + 1) / ↑(2 * n + 1)!) (sinh r)
  proof: mod_cast Complex.hasSum_sinh r

中文:
引理 hasSum_sinh
  条件: (r : 实数)
  结论: HasSum (fun n => r ^ (2 * n + 1) / ↑(2 * n + 1)!) (sinh r)
  证明: mod_cast Complex.hasSum_sinh r

Depends on / 依赖: Complex.hasSum_sinh, hasSum_sinh, mod_cast
-/
lemma hasSum_sinh (r : Real) : HasSum (fun n => r ^ (2 * n + 1) / ↑(2 * n + 1)!) (sinh r) :=
  mod_cast Complex.hasSum_sinh r

/--
lemma `cosh_eq_tsum` / 引理 `cosh_eq_tsum`

English:
lemma cosh_eq_tsum
  given: (r : Real)
  statement: cosh r = ∑' n, r ^ (2 * n) / ↑(2 * n)!
  proof: r.hasSum_cosh.tsum_eq.symm

中文:
引理 cosh_eq_tsum
  条件: (r : 实数)
  结论: cosh r = ∑' n, r ^ (2 * n) / ↑(2 * n)!
  证明: r.hasSum_cosh.tsum_eq.symm

Depends on / 依赖: hasSum_cosh, r.hasSum_cosh.tsum_eq.symm, tsum_eq
-/
lemma cosh_eq_tsum (r : Real) : cosh r = ∑' n, r ^ (2 * n) / ↑(2 * n)! := r.hasSum_cosh.tsum_eq.symm

/--
lemma `sinh_eq_tsum` / 引理 `sinh_eq_tsum`

English:
lemma sinh_eq_tsum
  given: (r : Real)
  statement: sinh r = ∑' n, r ^ (2 * n + 1) / ↑(2 * n + 1)!
  proof: r.hasSum_sinh.tsum_eq.symm

中文:
引理 sinh_eq_tsum
  条件: (r : 实数)
  结论: sinh r = ∑' n, r ^ (2 * n + 1) / ↑(2 * n + 1)!
  证明: r.hasSum_sinh.tsum_eq.symm

Depends on / 依赖: hasSum_sinh, r.hasSum_sinh.tsum_eq.symm, tsum_eq
-/
lemma sinh_eq_tsum (r : Real) : sinh r = ∑' n, r ^ (2 * n + 1) / ↑(2 * n + 1)! :=
  r.hasSum_sinh.tsum_eq.symm

/--
lemma `cosh_le_exp_half_sq` / 引理 `cosh_le_exp_half_sq`

English:
lemma cosh_le_exp_half_sq
  given: (x : Real)
  statement: cosh x <= exp (x ^ 2 / 2)
  proof: by
  rw [cosh_eq_tsum]; rw [exp_eq_exp_Real]; rw [exp_eq_tsum Real]
refine x.hasSum_cosh.summable.tsum_le_tsum (fun i => ?_) expSeries_summable' (x ^ 2 / 2)
  simp only [div_pow, pow_mul, smul_eq_mul, inv_mul_eq_div, div_div]
  gcongr
  norm_cast
  exact Nat.two_pow_mul_factorial_le_factorial_two_mul _

中文:
引理 cosh_le_exp_half_sq
  条件: (x : 实数)
  结论: cosh x <= exp (x ^ 2 / 2)
  证明: by
  rw [cosh_eq_tsum]; rw [exp_eq_exp_Real]; rw [exp_eq_tsum Real]
refine x.hasSum_cosh.summable.tsum_le_tsum (fun i => ?_) expSeries_summable' (x ^ 2 / 2)
  simp only [div_pow, pow_mul, smul_eq_mul, inv_mul_eq_div, div_div]
  gcongr
  norm_cast
  exact Nat.two_pow_mul_factorial_le_factorial_two_mul _

Depends on / 依赖: Nat.two_pow_mul_factorial_le_factorial_two_mul, cosh_eq_tsum, div_div, div_pow, expSeries_summable, exp_eq_exp_Real, exp_eq_tsum, hasSum_cosh, inv_mul_eq_div, pow_mul, smul_eq_mul, summable, tsum_le_tsum, two_pow_mul_factorial_le_factorial_two_mul, x.hasSum_cosh.summable.tsum_le_tsum
-/
lemma cosh_le_exp_half_sq (x : Real) : cosh x <= exp (x ^ 2 / 2) := by
  rw [cosh_eq_tsum]; rw [exp_eq_exp_Real]; rw [exp_eq_tsum Real]
refine x.hasSum_cosh.summable.tsum_le_tsum (fun i => ?_) expSeries_summable' (x ^ 2 / 2)
  simp only [div_pow, pow_mul, smul_eq_mul, inv_mul_eq_div, div_div]
  gcongr
  norm_cast
  exact Nat.two_pow_mul_factorial_le_factorial_two_mul _

end Real
end SinhCosh
