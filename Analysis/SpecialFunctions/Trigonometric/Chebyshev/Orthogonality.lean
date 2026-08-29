/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuval Filmus
-/
module

public import Mathlib.RingTheory.Polynomial.Chebyshev
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.Algebra.Polynomial

/-!
# Chebyshev polynomials over the reals: orthogonality

Chebyshev T polynomials are orthogonal with respect to `√(1 - x ^ 2)⁻¹`.

## Main statements

* `integrable_measureT`: continuous functions are integrable with respect to Lebesgue measure
  scaled by `√(1 - x ^ 2)⁻¹` and restricted to `(-1, 1]`.
* `integral_eval_T_real_mul_evalT_real_measureT_of_ne`:
  if `n ≠ m` then the integral of `T_n * T_m` equals `0`.
* `integral_eval_T_real_mul_self_measureT_zero`:
  if `n = m = 0` then the integral equals `π`.
* `integral_eval_T_real_mul_self_measureT_of_ne_zero`:
  if `n = m ≠ 0` then the integral equals `π / 2`.

## TODO

* Prove that Chebyshev U polynomials are orthogonal with respect to `√(1 - x ^ 2)`
* Bundle Chebyshev T polynomials into a HilbertBasis for MeasureTheory.Lp ℝ 2 measureT

-/
public section

namespace Polynomial.Chebyshev

open Real intervalIntegral MeasureTheory

open scoped NNReal

/--
Definition of `measureT` / `measureT` 的定义

English:
definition measureT
  signature: : Measure Real
  body: (volume.withDensity
    fun x => ENNReal.ofNNReal (.mk (√(1 - x ^ 2)⁻¹) (by positivity))).restrict (Set.Ioc (-1) 1)

中文:
定义 measureT
  签名: : 测度 实数
  定义体: (volume.withDensity
    fun x => ENNReal.ofNNReal (.mk (√(1 - x ^ 2)⁻¹) (by positivity))).restrict (Set.Ioc (-1) 1)

Depends on / 依赖: ENNReal, ENNReal.ofNNReal, Set.Ioc, ofNNReal, restrict, volume, volume.withDensity, withDensity
-/
noncomputable def measureT : Measure Real :=
  (volume.withDensity
    fun x => ENNReal.ofNNReal (.mk (√(1 - x ^ 2)⁻¹) (by positivity))).restrict (Set.Ioc (-1) 1)

/--
theorem `integral_measureT` / 定理 `integral_measureT`

English:
theorem integral_measureT
  given: (f : Real -> Real)
  proof: by
  rw [integral_of_le (by norm_num)]; rw [measureT]; rw [restrict_withDensity (by measurability)]; rw [integral_withDensity_eq_integral_smul (by fun_prop)]
  congr! 2 with x hx
  simp [NNReal.smul_def, mul_comm]

中文:
定理 integral_measureT
  条件: (f : 实数 -> 实数)
  证明: by
  rw [integral_of_le (by norm_num)]; rw [measureT]; rw [restrict_withDensity (by measurability)]; rw [integral_withDensity_eq_integral_smul (by fun_prop)]
  congr! 2 with x hx
  simp [NNReal.smul_def, mul_comm]

Depends on / 依赖: NNReal, NNReal.smul_def, fun_prop, integral_of_le, integral_withDensity_eq_integral_smul, measurability, measureT, mul_comm, restrict_withDensity, smul_def
-/
theorem integral_measureT (f : Real -> Real) :
    ∫ x, f x ∂measureT = ∫ x in -1..1, f x * √(1 - x ^ 2)⁻¹ := by
  rw [integral_of_le (by norm_num)]; rw [measureT]; rw [restrict_withDensity (by measurability)]; rw [integral_withDensity_eq_integral_smul (by fun_prop)]
  congr! 2 with x hx
  simp [NNReal.smul_def, mul_comm]

/--
theorem `intervalIntegrable_sqrt_one_sub_sq_inv` / 定理 `intervalIntegrable_sqrt_one_sub_sq_inv`

English:
theorem intervalIntegrable_sqrt_one_sub_sq_inv
  proof: by
  rw [intervalIntegrable_iff]
  refine integrableOn_deriv_of_nonneg continuous_arccos.neg.continuousOn (fun x hx => ?_) (by simp)
  simpa using! (hasDerivAt_arccos (by aesop) (by aesop)).neg

中文:
定理 interval整数egrable_sqrt_one_sub_sq_inv
  证明: by
  rw [intervalIntegrable_iff]
  refine integrableOn_deriv_of_nonneg continuous_arccos.neg.continuousOn (fun x hx => ?_) (by simp)
  simpa using! (hasDerivAt_arccos (by aesop) (by aesop)).neg

Depends on / 依赖: continuousOn, continuous_arccos, continuous_arccos.neg.continuousOn, hasDerivAt_arccos, integrableOn_deriv_of_nonneg, intervalIntegrable_iff
-/
theorem intervalIntegrable_sqrt_one_sub_sq_inv :
    IntervalIntegrable (fun x => √(1 - x ^ 2)⁻¹) volume (-1) 1 := by
  rw [intervalIntegrable_iff]
  refine integrableOn_deriv_of_nonneg continuous_arccos.neg.continuousOn (fun x hx => ?_) (by simp)
  simpa using! (hasDerivAt_arccos (by aesop) (by aesop)).neg

/--
theorem `integrable_measureT` / 定理 `integrable_measureT`

English:
theorem integrable_measureT
  given: {f : Real -> Real} (hf : ContinuousOn f (Set.Icc (-1) 1))
  proof: by
  replace hf : ContinuousOn f (Set.uIcc (-1) 1) := by rwa [Set.uIcc_of_lt (by norm_num)]
  have := intervalIntegrable_sqrt_one_sub_sq_inv.continuousOn_mul hf
  rw [intervalIntegrable_iff]; rw [Set.uIoc_of_le (by norm_num)] at this
  rw [measureT]; rw [restrict_withDensity (by measurability)]; rw 

中文:
定理 integrable_measureT
  条件: {f : 实数 -> 实数} (hf : ContinuousOn f (集合.闭区间 (-1) 1))
  证明: by
  replace hf : ContinuousOn f (Set.uIcc (-1) 1) := by rwa [Set.uIcc_of_lt (by norm_num)]
  have := intervalIntegrable_sqrt_one_sub_sq_inv.continuousOn_mul hf
  rw [intervalIntegrable_iff]; rw [Set.uIoc_of_le (by norm_num)] at this
  rw [measureT]; rw [restrict_withDensity (by measurability)]; rw 

Depends on / 依赖: ContinuousOn, IntegrableOn, Set.uIcc, Set.uIcc_of_lt, Set.uIoc_of_le, continuousOn_mul, convert, fun_prop, integrable_withDensity_iff, intervalIntegrable_iff, intervalIntegrable_sqrt_one_sub_sq_inv, intervalIntegrable_sqrt_one_sub_sq_inv.continuousOn_mul, measurability, measureT, replace, restrict_withDensity, uIcc_of_lt, uIoc_of_le
-/
theorem integrable_measureT {f : Real -> Real} (hf : ContinuousOn f (Set.Icc (-1) 1)) :
    Integrable f measureT := by
  replace hf : ContinuousOn f (Set.uIcc (-1) 1) := by rwa [Set.uIcc_of_lt (by norm_num)]
  have := intervalIntegrable_sqrt_one_sub_sq_inv.continuousOn_mul hf
  rw [intervalIntegrable_iff]; rw [Set.uIoc_of_le (by norm_num)] at this
  rw [measureT]; rw [restrict_withDensity (by measurability)]; rw [integrable_withDensity_iff (by fun_prop) (by simp)]
  unfold IntegrableOn at this
  convert! this

open Set in
/--
theorem `integral_measureT_eq_integral_cos` / 定理 `integral_measureT_eq_integral_cos`

English:
theorem integral_measureT_eq_integral_cos
  given: {f : Real -> Real}
  proof: calc
  ∫ x, f x ∂measureT = ∫ x in -1..1, f x * √(1 - x ^ 2)⁻¹ := integral_measureT f
  _ = ∫ x in 1..-1, f x * -(√(1 - x ^ 2)⁻¹) := by
    rw [integral_symm]; rw [← intervalIntegral.integral_neg]
    simp
  _ = ∫ θ in (arccos 1)..(arccos (-1)), f (cos θ) := by
    rw [← integral_comp_mul_deriv_of_d

中文:
定理 integral_measureT_eq_integral_cos
  条件: {f : 实数 -> 实数}
  证明: calc
  ∫ x, f x ∂measureT = ∫ x in -1..1, f x * √(1 - x ^ 2)⁻¹ := integral_measureT f
  _ = ∫ x in 1..-1, f x * -(√(1 - x ^ 2)⁻¹) := by
    rw [integral_symm]; rw [← intervalIntegral.integral_neg]
    simp
  _ = ∫ θ in (arccos 1)..(arccos (-1)), f (cos θ) := by
    rw [← integral_comp_mul_deriv_of_d
-/
theorem integral_measureT_eq_integral_cos {f : Real -> Real} :
    ∫ x, f x ∂measureT = ∫ θ in 0..π, f (cos θ) := calc
  ∫ x, f x ∂measureT = ∫ x in -1..1, f x * √(1 - x ^ 2)⁻¹ := integral_measureT f
  _ = ∫ x in 1..-1, f x * -(√(1 - x ^ 2)⁻¹) := by
    rw [integral_symm]; rw [← intervalIntegral.integral_neg]
    simp
  _ = ∫ θ in (arccos 1)..(arccos (-1)), f (cos θ) := by
    rw [← integral_comp_mul_deriv_of_deriv_nonpos (f' := fun x => -(1 / √(1 - x ^ 2)))]
    · simp_rw [Function.comp_apply]
exact integral_congr fun x hx => by simp [cos_arccos (x := x) (by aesop) (by aesop)]
    · fun_prop
    · exact fun x hx => (hasDerivAt_arccos (by aesop) (by aesop))
    · simp
  _ = ∫ θ in 0..π, f (cos θ) := by simp

@[deprecated (since := "2026-03-19")]
alias integral_measureT_eq_integral_cos_of_continuous := integral_measureT_eq_integral_cos

/--
theorem `integral_eval_T_real_measureT_zero` / 定理 `integral_eval_T_real_measureT_zero`

English:
theorem integral_eval_T_real_measureT_zero
  proof: by
  rw [integral_measureT_eq_integral_cos]; simp

中文:
定理 integral_eval_T_real_measureT_zero
  证明: by
  rw [integral_measureT_eq_integral_cos]; simp

Depends on / 依赖: integral_measureT_eq_integral_cos
-/
theorem integral_eval_T_real_measureT_zero :
    ∫ x, (T Real 0).eval x ∂measureT = π := by
  rw [integral_measureT_eq_integral_cos]; simp

/--
theorem `integral_eval_T_real_measureT_of_ne_zero` / 定理 `integral_eval_T_real_measureT_of_ne_zero`

English:
theorem integral_eval_T_real_measureT_of_ne_zero
  given: {n : Int} (hn : n != 0)
  proof: by
  have hn' : (n : Real) != 0 := Int.cast_ne_zero.mpr hn
  suffices ∫ θ in 0..n * π, cos θ = 0 by
    rw [integral_measureT_eq_integral_cos]
    simp_rw [T_real_cos]
    rwa [integral_comp_mul_left _ (Int.cast_ne_zero.mpr hn), smul_eq_zero_iff_right (by aesop),
      mul_zero]
  trans ∫ θ in 0..n 

中文:
定理 integral_eval_T_real_measureT_of_ne_zero
  条件: {n : 整数} (hn : n != 0)
  证明: by
  have hn' : (n : Real) != 0 := Int.cast_ne_zero.mpr hn
  suffices ∫ θ in 0..n * π, cos θ = 0 by
    rw [integral_measureT_eq_integral_cos]
    simp_rw [T_real_cos]
    rwa [integral_comp_mul_left _ (Int.cast_ne_zero.mpr hn), smul_eq_zero_iff_right (by aesop),
      mul_zero]
  trans ∫ θ in 0..n 

Depends on / 依赖: Int.cast_ne_zero.mpr, T_real_cos, cast_ne_zero, contDiffOn, contDiff_sin, contDiff_sin.contDiffOn, deriv_sin, integral_, integral_comp_mul_left, integral_congr, integral_deriv_of_contDiffOn_Icc, integral_measureT_eq_integral_cos, mul_zero, simp_rw, smul_eq_zero_iff_right
-/
theorem integral_eval_T_real_measureT_of_ne_zero {n : Int} (hn : n != 0) :
    ∫ x, (T Real n).eval x ∂measureT = 0 := by
  have hn' : (n : Real) != 0 := Int.cast_ne_zero.mpr hn
  suffices ∫ θ in 0..n * π, cos θ = 0 by
    rw [integral_measureT_eq_integral_cos]
    simp_rw [T_real_cos]
    rwa [integral_comp_mul_left _ (Int.cast_ne_zero.mpr hn), smul_eq_zero_iff_right (by aesop),
      mul_zero]
  trans ∫ θ in 0..n * π, (deriv sin) θ
· refine integral_congr fun x hx => (congrFun deriv_sin x).symm
  by_cases! 0 <= n
  case pos => rw [integral_deriv_of_contDiffOn_Icc contDiff_sin.contDiffOn (by positivity)]; simp
  case neg hn =>
    rw [integral_symm]; rw [integral_deriv_of_contDiffOn_Icc contDiff_sin.contDiffOn]
    · simp
    exact mul_nonpos_of_nonpos_of_nonneg (Int.cast_nonpos.mpr <| le_of_lt hn) pi_nonneg

/--
theorem `integral_eval_T_real_mul_eval_T_real_measureT` / 定理 `integral_eval_T_real_mul_eval_T_real_measureT`

English:
theorem integral_eval_T_real_mul_eval_T_real_measureT
  given: (n m : Int)
  proof: by
  suffices ∫ x, (2 * T Real n * T Real m).eval x ∂measureT =
      (∫ x, (T Real (n + m)).eval x ∂measureT) +
      (∫ x, (T Real (n - m)).eval x ∂measureT) by
    simp_rw [eval_mul, eval_ofNat, mul_assoc] at this
    rw [MeasureTheory.integral_const_mul] at this
    grind
  simp_rw [T_mul_T, eva

中文:
定理 integral_eval_T_real_mul_eval_T_real_measureT
  条件: (n m : 整数)
  证明: by
  suffices ∫ x, (2 * T Real n * T Real m).eval x ∂measureT =
      (∫ x, (T Real (n + m)).eval x ∂measureT) +
      (∫ x, (T Real (n - m)).eval x ∂measureT) by
    simp_rw [eval_mul, eval_ofNat, mul_assoc] at this
    rw [MeasureTheory.integral_const_mul] at this
    grind
  simp_rw [T_mul_T, eva

Depends on / 依赖: F.map, F.map_id, MeasureTheory, MeasureTheory.integral_add, MeasureTheory.integral_const_mul, T_mul_T, eval_add, eval_mul, eval_ofNat, fun_prop, integrable_measureT, integral_add, integral_const_mul, map_id, measureT, mul_assoc, simp_rw
-/
theorem integral_eval_T_real_mul_eval_T_real_measureT (n m : Int) :
    ∫ x, (T Real n).eval x * (T Real m).eval x ∂measureT =
    ((∫ x, (T Real (n + m)).eval x ∂measureT) +
     (∫ x, (T Real (n - m)).eval x ∂measureT)) / 2 := by
  suffices ∫ x, (2 * T Real n * T Real m).eval x ∂measureT =
      (∫ x, (T Real (n + m)).eval x ∂measureT) +
      (∫ x, (T Real (n - m)).eval x ∂measureT) by
    simp_rw [eval_mul, eval_ofNat, mul_assoc] at this
    rw [MeasureTheory.integral_const_mul] at this
    grind
  simp_rw [T_mul_T, eval_add]
  rw [MeasureTheory.integral_add
    (integrable_measureT (by fun_prop)) (integrable_measureT (by fun_prop))]

/--
theorem `integral_eval_T_real_mul_eval_T_real_measureT_of_ne` / 定理 `integral_eval_T_real_mul_eval_T_real_measureT_of_ne`

English:
theorem integral_eval_T_real_mul_eval_T_real_measureT_of_ne
  given: {n m : Nat} (h : n != m)
  proof: by
  rw [integral_eval_T_real_mul_eval_T_real_measureT]; rw [integral_eval_T_real_measureT_of_ne_zero (by grind)]; rw [integral_eval_T_real_measureT_of_ne_zero (by grind)]
  simp

中文:
定理 integral_eval_T_real_mul_eval_T_real_measureT_of_ne
  条件: {n m : 自然数} (h : n != m)
  证明: by
  rw [integral_eval_T_real_mul_eval_T_real_measureT]; rw [integral_eval_T_real_measureT_of_ne_zero (by grind)]; rw [integral_eval_T_real_measureT_of_ne_zero (by grind)]
  simp

Depends on / 依赖: F.map, F.map_comp, integral_eval_T_real_measureT_of_ne_zero, integral_eval_T_real_mul_eval_T_real_measureT, map_comp
-/
theorem integral_eval_T_real_mul_eval_T_real_measureT_of_ne {n m : Nat} (h : n != m) :
    ∫ x, (T Real n).eval x * (T Real m).eval x ∂measureT = 0 := by
  rw [integral_eval_T_real_mul_eval_T_real_measureT]; rw [integral_eval_T_real_measureT_of_ne_zero (by grind)]; rw [integral_eval_T_real_measureT_of_ne_zero (by grind)]
  simp

/--
theorem `integral_eval_T_real_mul_self_measureT_zero` / 定理 `integral_eval_T_real_mul_self_measureT_zero`

English:
theorem integral_eval_T_real_mul_self_measureT_zero
  proof: by
  simp_rw [← eval_mul, show (T Real 0) * (T Real 0) = T Real 0 by simp]
  exact integral_eval_T_real_measureT_zero

中文:
定理 integral_eval_T_real_mul_self_measureT_zero
  证明: by
  simp_rw [← eval_mul, show (T Real 0) * (T Real 0) = T Real 0 by simp]
  exact integral_eval_T_real_measureT_zero

Depends on / 依赖: eval_mul, integral_eval_T_real_measureT_zero, simp_rw
-/
theorem integral_eval_T_real_mul_self_measureT_zero :
    ∫ x, (T Real 0).eval x * (T Real 0).eval x ∂measureT = π := by
  simp_rw [← eval_mul, show (T Real 0) * (T Real 0) = T Real 0 by simp]
  exact integral_eval_T_real_measureT_zero

/--
theorem `integral_T_real_mul_self_measureT_of_ne_zero` / 定理 `integral_T_real_mul_self_measureT_of_ne_zero`

English:
theorem integral_T_real_mul_self_measureT_of_ne_zero
  given: {n : Nat} (hn : n != 0)
  proof: by
  rw [integral_eval_T_real_mul_eval_T_real_measureT]; rw [integral_eval_T_real_measureT_of_ne_zero (by grind)]; rw [sub_self]; rw [integral_eval_T_real_measureT_zero]; rw [zero_add]

中文:
定理 integral_T_real_mul_self_measureT_of_ne_zero
  条件: {n : 自然数} (hn : n != 0)
  证明: by
  rw [integral_eval_T_real_mul_eval_T_real_measureT]; rw [integral_eval_T_real_measureT_of_ne_zero (by grind)]; rw [sub_self]; rw [integral_eval_T_real_measureT_zero]; rw [zero_add]

Depends on / 依赖: integral_eval_T_real_measureT_of_ne_zero, integral_eval_T_real_measureT_zero, integral_eval_T_real_mul_eval_T_real_measureT, sub_self, zero_add
-/
theorem integral_T_real_mul_self_measureT_of_ne_zero {n : Nat} (hn : n != 0) :
    ∫ x, (T Real n).eval x * (T Real n).eval x ∂measureT = π / 2 := by
  rw [integral_eval_T_real_mul_eval_T_real_measureT]; rw [integral_eval_T_real_measureT_of_ne_zero (by grind)]; rw [sub_self]; rw [integral_eval_T_real_measureT_zero]; rw [zero_add]

end Polynomial.Chebyshev
