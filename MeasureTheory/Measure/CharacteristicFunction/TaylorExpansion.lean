/-
Copyright (c) 2024 Thomas Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Zhu, Etienne Marion
-/
module

public import Mathlib.Analysis.Calculus.Taylor
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic

import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Probability.Notation

/-!
# Taylor expansion of the characteristic function

This file provides the Taylor expansion of the characteristic function of a measure at `0`.

## Main statements

* `taylorWithinEval_charFun_zero`: If a finite measure `μ` over `ℝ` admits a moment of order `n`,
  then the Taylor expansion of its characteristic function at `0` at order `n` is given by
  `t ↦ ∑ k ∈ Finset.range (n + 1), (k ! : ℂ)⁻¹ * (t * I) ^ k * ∫ x, x ^ k ∂μ`.

## Tags

characteristic function, Taylor expansion
-/

public section


open ProbabilityTheory Complex Set VectorFourier
open scoped Nat RealInnerProductSpace Topology

namespace MeasureTheory

section InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  {μ : Measure E} [IsFiniteMeasure μ]

/-- The characteristic function of a finite measure with a moment of order `n` is `C^n`.
See `contDiff_charFun'` for the version proving `C^∞` by assuming all moments exist. -/
@[fun_prop]
/--
theorem `contDiff_charFun` / 定理 `contDiff_charFun`

English:
theorem contDiff_charFun
  given: {n : Nat} (hint : MemLp id n μ)
  proof: by
  simp_rw [funext charFun_eq_fourierIntegral']
  refine (contDiff_fourierIntegral (L := innerSL Real) fun k hk => ?_).comp (by fun_prop)
  simp only [Pi.one_apply, one_mem, CStarRing.norm_of_mem_unitary, mul_one]
  refine MemLp.integrable_norm_pow' (hint.mono_exponent (by simp_all))

中文:
定理 contDiff_charFun
  条件: {n : 自然数} (hint : MemLp id n μ)
  证明: by
  simp_rw [funext charFun_eq_fourierIntegral']
  refine (contDiff_fourierIntegral (L := innerSL Real) fun k hk => ?_).comp (by fun_prop)
  simp only [Pi.one_apply, one_mem, CStarRing.norm_of_mem_unitary, mul_one]
  refine MemLp.integrable_norm_pow' (hint.mono_exponent (by simp_all))

Depends on / 依赖: CStarRing, CStarRing.norm_of_mem_unitary, MemLp.integrable_norm_pow, Pi.one_apply, charFun_eq_fourierIntegral, contDiff_fourierIntegral, fun_prop, hint.mono_exponent, innerSL, integrable_norm_pow, mono_exponent, mul_one, norm_of_mem_unitary, one_apply, one_mem, simp_rw
-/
theorem contDiff_charFun {n : Nat} (hint : MemLp id n μ) :
    ContDiff Real n (charFun μ) := by
  simp_rw [funext charFun_eq_fourierIntegral']
  refine (contDiff_fourierIntegral (L := innerSL Real) fun k hk => ?_).comp (by fun_prop)
  simp only [Pi.one_apply, one_mem, CStarRing.norm_of_mem_unitary, mul_one]
  refine MemLp.integrable_norm_pow' (hint.mono_exponent (by simp_all))

/-- The characteristic function of a measure with all moments is `C^∞`. See `contDiff_charFun`
for the version proving only `C^n` by only assuming that the moment of order `n` exists. -/
@[fun_prop]
/--
theorem `contDiff_charFun'` / 定理 `contDiff_charFun'`

English:
theorem contDiff_charFun'
  given: {n : Nat∞} (hint : forall (k : Nat), MemLp id k μ)
  proof: by
  simp_rw [funext charFun_eq_fourierIntegral']
  refine (contDiff_fourierIntegral (L := innerSL Real) fun k hk => ?_).comp (by fun_prop)
  simp only [Pi.one_apply, one_mem, CStarRing.norm_of_mem_unitary, mul_one]
  refine MemLp.integrable_norm_pow' ((hint k).mono_exponent (by simp_all))

@[fun_pr

中文:
定理 contDiff_charFun'
  条件: {n : 自然数∞} (hint : 对任意 (k : 自然数), MemLp id k μ)
  证明: by
  simp_rw [funext charFun_eq_fourierIntegral']
  refine (contDiff_fourierIntegral (L := innerSL Real) fun k hk => ?_).comp (by fun_prop)
  simp only [Pi.one_apply, one_mem, CStarRing.norm_of_mem_unitary, mul_one]
  refine MemLp.integrable_norm_pow' ((hint k).mono_exponent (by simp_all))

@[fun_pr

Depends on / 依赖: CStarRing, CStarRing.norm_of_mem_unitary, MemLp.integrable_norm_pow, Pi.one_apply, charFun_eq_fourierIntegral, contDiff_fourierIntegral, fun_prop, innerSL, integrable_norm_pow, mono_exponent, mul_one, norm_of_mem_unitary, one_apply, one_mem, simp_rw
-/
theorem contDiff_charFun' {n : Nat∞} (hint : forall (k : Nat), MemLp id k μ) :
    ContDiff Real n (charFun μ) := by
  simp_rw [funext charFun_eq_fourierIntegral']
  refine (contDiff_fourierIntegral (L := innerSL Real) fun k hk => ?_).comp (by fun_prop)
  simp only [Pi.one_apply, one_mem, CStarRing.norm_of_mem_unitary, mul_one]
  refine MemLp.integrable_norm_pow' ((hint k).mono_exponent (by simp_all))

@[fun_prop]
/--
lemma `continuous_charFun` / 引理 `continuous_charFun`

English:
lemma continuous_charFun
  statement: Continuous (charFun μ)
  proof: by
  refine contDiff_zero.1 (contDiff_charFun ?_)
  simpa using by fun_prop

中文:
引理 continuous_charFun
  结论: Continuous (charFun μ)
  证明: by
  refine contDiff_zero.1 (contDiff_charFun ?_)
  simpa using by fun_prop

Depends on / 依赖: contDiff_charFun, contDiff_zero, fun_prop
-/
lemma continuous_charFun : Continuous (charFun μ) := by
  refine contDiff_zero.1 (contDiff_charFun ?_)
  simpa using by fun_prop

/--
theorem `iteratedFDeriv_charFun` / 定理 `iteratedFDeriv_charFun`

English:
theorem iteratedFDeriv_charFun
  given: {n : Nat} {t : E} (hint : MemLp id n μ) (x : Fin n -> E)
  proof: by
  have h : innerₗ E = (innerSL Real).toLinearMap₁₂ := rfl
  have hint' (k : Nat) (hk : k <= (n : Nat∞)) : Integrable (fun x => ‖x‖ ^ k * ‖(1 : E -> Complex) x‖) μ := by
    simp only [Pi.one_apply, one_mem, CStarRing.norm_of_mem_unitary, mul_one]
    refine MemLp.integrable_norm_pow' (hint.mono_e

中文:
定理 iteratedFDeriv_charFun
  条件: {n : 自然数} {t : E} (hint : MemLp id n μ) (x : Fin n -> E)
  证明: by
  have h : innerₗ E = (innerSL Real).toLinearMap₁₂ := rfl
  have hint' (k : Nat) (hk : k <= (n : Nat∞)) : Integrable (fun x => ‖x‖ ^ k * ‖(1 : E -> Complex) x‖) μ := by
    simp only [Pi.one_apply, one_mem, CStarRing.norm_of_mem_unitary, mul_one]
    refine MemLp.integrable_norm_pow' (hint.mono_e

Depends on / 依赖: CStarRing, CStarRing.norm_of_mem_unitary, Integrable, MemLp.integrable_norm_pow, Pi.one_apply, charFun_eq_fourierIntegral, contDiff_fourierIntegral, hint.mono_exponent, innerSL, integrable_norm_pow, iteratedF, iteratedFDeriv_comp_const_smul, mono_exponent, mul_inv_rev, mul_one, neg_smul, norm_of_mem_unitary, one_apply, one_mem, simp_rw
-/
theorem iteratedFDeriv_charFun {n : Nat} {t : E} (hint : MemLp id n μ) (x : Fin n -> E) :
    iteratedFDeriv Real n (charFun μ) t x = I ^ n * ∫ y, (∏ i, ⟪y, x i⟫) * exp (⟪y, t⟫ * I) ∂μ := by
  have h : innerₗ E = (innerSL Real).toLinearMap₁₂ := rfl
  have hint' (k : Nat) (hk : k <= (n : Nat∞)) : Integrable (fun x => ‖x‖ ^ k * ‖(1 : E -> Complex) x‖) μ := by
    simp only [Pi.one_apply, one_mem, CStarRing.norm_of_mem_unitary, mul_one]
    refine MemLp.integrable_norm_pow' (hint.mono_exponent (by simp_all))
  simp_rw [funext charFun_eq_fourierIntegral']
  rw [iteratedFDeriv_comp_const_smul]
  swap
  · rw [h]
    exact contDiff_fourierIntegral _ hint'
  simp only [mul_inv_rev, neg_smul]
  rw [h]; rw [iteratedFDeriv_fourierIntegral _ hint' (by fun_prop) le_rfl]
  simp only [smul_apply, real_smul, ofReal_pow, ofReal_neg, ofReal_mul, ofReal_inv, ofReal_ofNat,
    ofReal_prod]
  rw [fourierIntegral_continuousMultilinearMap_apply Real.continuous_fourierChar]
  swap;
  · exact integrable_fourierPowSMulRight _ (by simpa using hint.integrable_norm_pow') (by fun_prop)
  simp only [fourierIntegral, Real.fourierChar, Circle.coe_exp, ofReal_mul,
    ofReal_ofNat, innerSL, map_neg, map_smul, ContinuousLinearMap.toLinearMap₁₂_apply_apply_apply,
    LinearMap.mkContinuous₂_apply, innerₛₗ_apply_apply, smul_eq_mul, neg_neg, AddChar.coe_mk,
    ofReal_inv, fourierPowSMulRight_apply, Pi.ofNat_apply, real_smul, ofReal_prod, mul_one,
    Circle.smul_def]
  simp_rw [mul_left_comm (exp _), integral_const_mul, ← mul_assoc, ← mul_pow]
  field_simp
  congr with
  ring

end InnerProductSpace

section Real

variable {μ : Measure Real} [IsFiniteMeasure μ]

/--
theorem `iteratedDeriv_charFun` / 定理 `iteratedDeriv_charFun`

English:
theorem iteratedDeriv_charFun
  given: {n : Nat} {t : Real} (hint : MemLp id n μ)
  proof: by
  rw [iteratedDeriv]; rw [iteratedFDeriv_charFun hint]
  simp

中文:
定理 iteratedDeriv_charFun
  条件: {n : 自然数} {t : 实数} (hint : MemLp id n μ)
  证明: by
  rw [iteratedDeriv]; rw [iteratedFDeriv_charFun hint]
  simp

Depends on / 依赖: iteratedDeriv, iteratedFDeriv_charFun
-/
theorem iteratedDeriv_charFun {n : Nat} {t : Real} (hint : MemLp id n μ) :
    iteratedDeriv n (charFun μ) t = I ^ n * ∫ x, x ^ n * exp (t * x * I) ∂μ := by
  rw [iteratedDeriv]; rw [iteratedFDeriv_charFun hint]
  simp

/--
theorem `iteratedDeriv_charFun_zero` / 定理 `iteratedDeriv_charFun_zero`

English:
theorem iteratedDeriv_charFun_zero
  given: {n : Nat} (hint : MemLp id n μ)
  proof: by
  simp [iteratedDeriv_charFun hint]
  norm_cast

中文:
定理 iteratedDeriv_charFun_zero
  条件: {n : 自然数} (hint : MemLp id n μ)
  证明: by
  simp [iteratedDeriv_charFun hint]
  norm_cast

Depends on / 依赖: iteratedDeriv_charFun
-/
theorem iteratedDeriv_charFun_zero {n : Nat} (hint : MemLp id n μ) :
    iteratedDeriv n (charFun μ) 0 = I ^ n * ∫ x, x ^ n ∂μ := by
  simp [iteratedDeriv_charFun hint]
  norm_cast

/--
lemma `taylorWithinEval_charFun_zero` / 引理 `taylorWithinEval_charFun_zero`

English:
lemma taylorWithinEval_charFun_zero
  given: {n : Nat} (hint : MemLp id n μ) (t : Real)
  proof: by
  simp_rw [taylor_within_apply, sub_zero, RCLike.real_smul_eq_coe_mul]
  refine Finset.sum_congr rfl fun k hkn => ?_
  push_cast
  have hint' : MemLp id k μ := hint.mono_exponent (by simp_all)
  simp [iteratedDeriv_charFun_zero hint', mul_pow, mul_comm, mul_assoc, mul_left_comm]

中文:
引理 taylorWithinEval_charFun_zero
  条件: {n : 自然数} (hint : MemLp id n μ) (t : 实数)
  证明: by
  simp_rw [taylor_within_apply, sub_zero, RCLike.real_smul_eq_coe_mul]
  refine Finset.sum_congr rfl fun k hkn => ?_
  push_cast
  have hint' : MemLp id k μ := hint.mono_exponent (by simp_all)
  simp [iteratedDeriv_charFun_zero hint', mul_pow, mul_comm, mul_assoc, mul_left_comm]

Depends on / 依赖: Finset, Finset.sum_congr, RCLike, RCLike.real_smul_eq_coe_mul, hint.mono_exponent, iteratedDeriv_charFun_zero, mono_exponent, mul_assoc, mul_comm, mul_left_comm, mul_pow, real_smul_eq_coe_mul, simp_rw, sub_zero, sum_congr, taylor_within_apply
-/
lemma taylorWithinEval_charFun_zero {n : Nat} (hint : MemLp id n μ) (t : Real) :
    taylorWithinEval (charFun μ) n univ 0 t
      = ∑ k in Finset.range (n + 1), (k ! : Complex)⁻¹ * (t * I) ^ k * ∫ x, x ^ k ∂μ := by
  simp_rw [taylor_within_apply, sub_zero, RCLike.real_smul_eq_coe_mul]
  refine Finset.sum_congr rfl fun k hkn => ?_
  push_cast
  have hint' : MemLp id k μ := hint.mono_exponent (by simp_all)
  simp [iteratedDeriv_charFun_zero hint', mul_pow, mul_comm, mul_assoc, mul_left_comm]

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {X : Ω -> Real}

/--
lemma `taylorWithinEval_charFun_two_zero` / 引理 `taylorWithinEval_charFun_two_zero`

English:
lemma taylorWithinEval_charFun_two_zero
  statement: (hX : AEMeasurable X P)
  proof: by
  have : IsProbabilityMeasure (P.map X) := Measure.isProbabilityMeasure_map hX
  convert! taylorWithinEval_charFun_zero hint t with x
  simp only [Pi.pow_apply, Nat.reduceAdd, Finset.sum_range_succ, Finset.range_one,
    Finset.sum_singleton, Nat.factorial_zero, Nat.cast_one, inv_one, pow_zero, m

中文:
引理 taylorWithinEval_charFun_two_zero
  结论: (hX : AEMeasurable X P)
  证明: by
  have : IsProbabilityMeasure (P.map X) := Measure.isProbabilityMeasure_map hX
  convert! taylorWithinEval_charFun_zero hint t with x
  simp only [Pi.pow_apply, Nat.reduceAdd, Finset.sum_range_succ, Finset.range_one,
    Finset.sum_singleton, Nat.factorial_zero, Nat.cast_one, inv_one, pow_zero, m

Depends on / 依赖: Finset, Finset.range_one, Finset.sum_range_succ, Finset.sum_singleton, IsProbabilityMeasure, Measure, Measure.isProbabilityMeasure_map, Nat.cast_ofNat, Nat.cast_one, Nat.factorial_one, Nat.factorial_two, Nat.factorial_zero, Nat.reduceAdd, P.map, Pi.pow_apply, any_goals, cast_ofNat, cast_one, convert, factorial_one
-/
lemma taylorWithinEval_charFun_two_zero (hX : AEMeasurable X P)
    (hint : MemLp id 2 (P.map X)) (t : Real) :
    taylorWithinEval (charFun (P.map X)) 2 univ 0 t =
      1 + (P[X] : Real) * t * I - (P[X ^ 2] : Real) * t ^ 2 / 2 := by
  have : IsProbabilityMeasure (P.map X) := Measure.isProbabilityMeasure_map hX
  convert! taylorWithinEval_charFun_zero hint t with x
  simp only [Pi.pow_apply, Nat.reduceAdd, Finset.sum_range_succ, Finset.range_one,
    Finset.sum_singleton, Nat.factorial_zero, Nat.cast_one, inv_one, pow_zero, mul_one,
    integral_const, probReal_univ, smul_eq_mul, ofReal_one, Nat.factorial_one, pow_one, one_mul,
    Nat.factorial_two, Nat.cast_ofNat]
  rw [integral_map]; rw [integral_map]
  any_goals fun_prop
  simp [field]
  ring

/--
lemma `taylorWithinEval_charFun_two_zero'` / 引理 `taylorWithinEval_charFun_two_zero'`

English:
lemma taylorWithinEval_charFun_two_zero'
  statement: (hX : AEMeasurable X P)
  proof: by
  rw [taylorWithinEval_charFun_two_zero hX]; rw [h0]; rw [h1]
  · simp
  refine (memLp_two_iff_integrable_sq (by fun_prop)).2 (.of_integral_ne_zero ?_)
  rw [integral_map]
  any_goals fun_prop
  simp [← Pi.pow_apply, h1]

中文:
引理 taylorWithinEval_charFun_two_zero'
  结论: (hX : AEMeasurable X P)
  证明: by
  rw [taylorWithinEval_charFun_two_zero hX]; rw [h0]; rw [h1]
  · simp
  refine (memLp_two_iff_integrable_sq (by fun_prop)).2 (.of_integral_ne_zero ?_)
  rw [integral_map]
  any_goals fun_prop
  simp [← Pi.pow_apply, h1]

Depends on / 依赖: Pi.pow_apply, any_goals, fun_prop, integral_map, memLp_two_iff_integrable_sq, of_integral_ne_zero, pow_apply, taylorWithinEval_charFun_two_zero
-/
lemma taylorWithinEval_charFun_two_zero' (hX : AEMeasurable X P)
    (h0 : P[X] = 0) (h1 : P[X ^ 2] = 1) (t : Real) :
    taylorWithinEval (charFun (P.map X)) 2 univ 0 t = 1 - t ^ 2 / 2 := by
  rw [taylorWithinEval_charFun_two_zero hX]; rw [h0]; rw [h1]
  · simp
  refine (memLp_two_iff_integrable_sq (by fun_prop)).2 (.of_integral_ne_zero ?_)
  rw [integral_map]
  any_goals fun_prop
  simp [← Pi.pow_apply, h1]

/--
lemma `taylor_charFun_two` / 引理 `taylor_charFun_two`

English:
lemma taylor_charFun_two
  given: (hX : AEMeasurable X P) (h0 : P[X] = 0) (h1 : P[X ^ 2] = 1)
  proof: by
  simp_rw [← taylorWithinEval_charFun_two_zero' (by fun_prop) h0 h1]
  convert! taylor_isLittleO_univ ?_
  · simp
refine contDiff_charFun
    (memLp_two_iff_integrable_sq (by fun_prop)).2 (.of_integral_ne_zero ?_)
  rw [integral_map]
  any_goals fun_prop
  simp_all

中文:
引理 taylor_charFun_two
  条件: (hX : AEMeasurable X P) (h0 : P[X] = 0) (h1 : P[X ^ 2] = 1)
  证明: by
  simp_rw [← taylorWithinEval_charFun_two_zero' (by fun_prop) h0 h1]
  convert! taylor_isLittleO_univ ?_
  · simp
refine contDiff_charFun
    (memLp_two_iff_integrable_sq (by fun_prop)).2 (.of_integral_ne_zero ?_)
  rw [integral_map]
  any_goals fun_prop
  simp_all

Depends on / 依赖: any_goals, contDiff_charFun, convert, fun_prop, integral_map, memLp_two_iff_integrable_sq, of_integral_ne_zero, simp_rw, taylorWithinEval_charFun_two_zero, taylor_isLittleO_univ
-/
lemma taylor_charFun_two (hX : AEMeasurable X P) (h0 : P[X] = 0) (h1 : P[X ^ 2] = 1) :
    (fun t => charFun (P.map X) t - (1 - t ^ 2 / 2)) =o[𝓝 0] fun t => t ^ 2 := by
  simp_rw [← taylorWithinEval_charFun_two_zero' (by fun_prop) h0 h1]
  convert! taylor_isLittleO_univ ?_
  · simp
refine contDiff_charFun
    (memLp_two_iff_integrable_sq (by fun_prop)).2 (.of_integral_ne_zero ?_)
  rw [integral_map]
  any_goals fun_prop
  simp_all

end Real

end MeasureTheory
