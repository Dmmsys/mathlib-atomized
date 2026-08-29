/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.Function.SpecialFunctions.Sinc
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic

/-!
# Integrals of characteristic functions

This file contains results about integrals of characteristic functions, and lemmas
relating the measure of some sets to integrals of characteristic functions.

## Main statements

* `integral_charFun_Icc`: `∫ t in -r..r, charFun μ t = 2 * r * ∫ x, sinc (r * x) ∂μ`
* `measureReal_abs_gt_le_integral_charFun`: bound on the measure of the set
  `{x | r < |x|}` in terms of the integral of the characteristic function of `μ`, for `μ` a
  probability measure on `ℝ`:
  `μ.real {x | r < |x|} ≤ 2⁻¹ * r * ‖∫ t in (-2 * r⁻¹)..(2 * r⁻¹), 1 - charFun μ t‖`
* `measureReal_abs_dual_gt_le_integral_charFunDual`: an application of the previous lemma in a
  normed space `E`, which gives for all `L : Dual ℝ E`,
  `μ.real {x | r < |L x|} ≤ 2⁻¹ * r * ‖∫ t in -2 * r⁻¹..2 * r⁻¹, 1 - charFunDual μ (t • L)‖`
* `measureReal_abs_inner_gt_le_integral_charFun`: an application in an inner product space,
  which gives for all `a`,
  `μ.real {x | r < |⟪a, x⟫|} ≤ 2⁻¹ * r * ‖∫ t in -2 * r⁻¹..2 * r⁻¹, 1 - charFun μ (t • a)‖`

-/

public section

open RealInnerProductSpace Real Complex NormedSpace

namespace MeasureTheory

section Real

variable {μ : Measure Real} {r : Real}

/--
lemma `integral_charFun_Icc` / 引理 `integral_charFun_Icc`

English:
lemma integral_charFun_Icc
  given: [IsFiniteMeasure μ] (hr : 0 < r)
  proof: by
  have h_int : Integrable (Function.uncurry fun (x y : Real) => cexp (x * y * I))
      ((volume.restrict (Set.uIoc (-r) r)).prod μ) := by
    simp only [neg_le_self_iff, hr.le, Set.uIoc_of_le]
    -- integrable since the function has norm 1 everywhere and the measure is finite
    rw [← integrable_norm_iff (by fun_prop)]
    suffices (fun a => ‖Function.uncurry (fun (x y : Real) => cexp (x * y * I)) a‖) = fun _ => 1 by
      rw [this]
      fun_prop
    ext p
    rw [← Prod.mk.eta (p := p)]
    norm_cast
    simp only [Function.uncurry_apply_pair, norm_exp_ofReal_mul_I]
  calc ∫ t in -r..r, charFun μ t
  _ = ∫ x in -r..r, ∫ y, cexp (x * y * I) ∂μ := by simp_rw [charFun_apply_real]
  _ = ∫ y, ∫ x in -r..r, cexp (x * y * I) ∂volume ∂μ := by
    rw [intervalIntegral_integral_swap h_int]
  _ = ∫ y, if r * y = 0 then 2 * (r : Complex)
      else y⁻¹ * ∫ x in -(y * r)..y * r, cexp (x * I) ∂volume ∂μ := by
    congr with y
    by_cases hy : y = 0
    · simp [hy, two_mul]
    simp only [mul_eq_zero, hr.ne', hy, or_self, ↓reduceIte, ofReal_inv]
    have h := intervalIntegral.integral_deriv_smul_comp (E := Complex) (a := -r) (b := r)
      (f := fun x => y * x) (f' := fun _ => y) (g := fun x => cexp (x * I)) ?_ (by fun_prop)
      (by fun_prop)
    swap
    · intro x hx
      simp_rw [mul_comm y]
      exact hasDerivAt_mul_const _
    simp only [Function.comp_apply, ofReal_mul, real_smul, intervalIntegral.integral_const_mul,
      mul_neg] at h
    rw [← h]; rw [← mul_assoc]
    norm_cast
    simp [mul_comm _ y, mul_inv_cancel₀ hy]
  _ = ∫ x, 2 * (r : Complex) * sinc (r * x) ∂μ := by
    congr with y
    rw [integral_exp_mul_I_eq_sinc]
    split_ifs with hry
    · simp [hry]
    have hy : y != 0 := fun hy => hry (by simp [hy])
    norm_cast
    field_simp
  _ = 2 * r * ∫ x, sinc (r * x) ∂μ := by
    norm_cast
    rw [← integral_const_mul]

中文:
引理 integral_charFun_Icc
  条件: [是有限测度 μ] (hr : 0 < r)
  证明: by
  have h_int : Integrable (Function.uncurry fun (x y : Real) => cexp (x * y * I))
      ((volume.restrict (Set.uIoc (-r) r)).prod μ) := by
    simp only [neg_le_self_iff, hr.le, Set.uIoc_of_le]
    -- integrable since the function has norm 1 everywhere and the measure is finite
    rw [← integrable_norm_iff (by fun_prop)]
    suffices (fun a => ‖Function.uncurry (fun (x y : Real) => cexp (x * y * I)) a‖) = fun _ => 1 by
      rw [this]
      fun_prop
    ext p
    rw [← Prod.mk.eta (p := p)]
    norm_cast
    simp only [Function.uncurry_apply_pair, norm_exp_ofReal_mul_I]
  calc ∫ t in -r..r, charFun μ t
  _ = ∫ x in -r..r, ∫ y, cexp (x * y * I) ∂μ := by simp_rw [charFun_apply_real]
  _ = ∫ y, ∫ x in -r..r, cexp (x * y * I) ∂volume ∂μ := by
    rw [intervalIntegral_integral_swap h_int]
  _ = ∫ y, if r * y = 0 then 2 * (r : Complex)
      else y⁻¹ * ∫ x in -(y * r)..y * r, cexp (x * I) ∂volume ∂μ := by
    congr with y
    by_cases hy : y = 0
    · simp [hy, two_mul]
    simp only [mul_eq_zero, hr.ne', hy, or_self, ↓reduceIte, ofReal_inv]
    have h := intervalIntegral.integral_deriv_smul_comp (E := Complex) (a := -r) (b := r)
      (f := fun x => y * x) (f' := fun _ => y) (g := fun x => cexp (x * I)) ?_ (by fun_prop)
      (by fun_prop)
    swap
    · intro x hx
      simp_rw [mul_comm y]
      exact hasDerivAt_mul_const _
    simp only [Function.comp_apply, ofReal_mul, real_smul, intervalIntegral.integral_const_mul,
      mul_neg] at h
    rw [← h]; rw [← mul_assoc]
    norm_cast
    simp [mul_comm _ y, mul_inv_cancel₀ hy]
  _ = ∫ x, 2 * (r : Complex) * sinc (r * x) ∂μ := by
    congr with y
    rw [integral_exp_mul_I_eq_sinc]
    split_ifs with hry
    · simp [hry]
    have hy : y != 0 := fun hy => hry (by simp [hy])
    norm_cast
    field_simp
  _ = 2 * r * ∫ x, sinc (r * x) ∂μ := by
    norm_cast
    rw [← integral_const_mul]

Depends on / 依赖: Function, Function.uncurry, Integrable, Set.uIoc, Set.uIoc_of_le, h_int, hr.le, neg_le_self_iff, restrict, uIoc_of_le, uncurry, volume, volume.restrict
-/
lemma integral_charFun_Icc [IsFiniteMeasure μ] (hr : 0 < r) :
    ∫ t in -r..r, charFun μ t = 2 * r * ∫ x, sinc (r * x) ∂μ := by
  have h_int : Integrable (Function.uncurry fun (x y : Real) => cexp (x * y * I))
      ((volume.restrict (Set.uIoc (-r) r)).prod μ) := by
    simp only [neg_le_self_iff, hr.le, Set.uIoc_of_le]
    -- integrable since the function has norm 1 everywhere and the measure is finite
    rw [← integrable_norm_iff (by fun_prop)]
    suffices (fun a => ‖Function.uncurry (fun (x y : Real) => cexp (x * y * I)) a‖) = fun _ => 1 by
      rw [this]
      fun_prop
    ext p
    rw [← Prod.mk.eta (p := p)]
    norm_cast
    simp only [Function.uncurry_apply_pair, norm_exp_ofReal_mul_I]
  calc ∫ t in -r..r, charFun μ t
  _ = ∫ x in -r..r, ∫ y, cexp (x * y * I) ∂μ := by simp_rw [charFun_apply_real]
  _ = ∫ y, ∫ x in -r..r, cexp (x * y * I) ∂volume ∂μ := by
    rw [intervalIntegral_integral_swap h_int]
  _ = ∫ y, if r * y = 0 then 2 * (r : Complex)
      else y⁻¹ * ∫ x in -(y * r)..y * r, cexp (x * I) ∂volume ∂μ := by
    congr with y
    by_cases hy : y = 0
    · simp [hy, two_mul]
    simp only [mul_eq_zero, hr.ne', hy, or_self, ↓reduceIte, ofReal_inv]
    have h := intervalIntegral.integral_deriv_smul_comp (E := Complex) (a := -r) (b := r)
      (f := fun x => y * x) (f' := fun _ => y) (g := fun x => cexp (x * I)) ?_ (by fun_prop)
      (by fun_prop)
    swap
    · intro x hx
      simp_rw [mul_comm y]
      exact hasDerivAt_mul_const _
    simp only [Function.comp_apply, ofReal_mul, real_smul, intervalIntegral.integral_const_mul,
      mul_neg] at h
    rw [← h]; rw [← mul_assoc]
    norm_cast
    simp [mul_comm _ y, mul_inv_cancel₀ hy]
  _ = ∫ x, 2 * (r : Complex) * sinc (r * x) ∂μ := by
    congr with y
    rw [integral_exp_mul_I_eq_sinc]
    split_ifs with hry
    · simp [hry]
    have hy : y != 0 := fun hy => hry (by simp [hy])
    norm_cast
    field_simp
  _ = 2 * r * ∫ x, sinc (r * x) ∂μ := by
    norm_cast
    rw [← integral_const_mul]

/--
lemma `measureReal_abs_gt_le_integral_charFun` / 引理 `measureReal_abs_gt_le_integral_charFun`

English:
lemma measureReal_abs_gt_le_integral_charFun
  given: [IsProbabilityMeasure μ] (hr : 0 < r)
  proof: by
  have integrable_sinc_const_mul (r : Real) : Integrable (fun x => sinc (r * x)) μ :=
    (integrable_map_measure stronglyMeasurable_sinc.aestronglyMeasurable (by fun_prop)).mp
      integrable_sinc
  calc μ.real {x | r < |x|}
  _ = μ.real {x | 2 < |2 * r⁻¹ * x|} := by
    congr 1 with x
    simp only [Set.mem_ofPred_eq, abs_mul, Nat.abs_ofNat]
    rw [abs_of_nonneg (a := r⁻¹) (by positivity)]; rw [mul_assoc]; rw [← inv_mul_lt_iff₀ (by positivity)]; rw [inv_mul_cancel₀ (by positivity)]; rw [lt_inv_mul_iff₀ (by positivity)]; rw [mul_one]
  _ = ∫ x in {x | 2 < |2 * r⁻¹ * x|}, 1 ∂μ := by simp
  _ = 2 * ∫ x in {x | 2 < |2 * r⁻¹ * x|}, 2⁻¹ ∂μ := by
    rw [← integral_const_mul]
    congr with _
    rw [mul_inv_cancel₀ (by positivity)]
  _ <= 2 * ∫ x in {x | 2 < |2 * r⁻¹ * x|}, 1 - sinc (2 * r⁻¹ * x) ∂μ := by
    gcongr (2 : Real) * ?_
    refine setIntegral_mono_on ?_
      ((integrable_const _).sub (integrable_sinc_const_mul _)).integrableOn ?_ fun x hx => ?_
· exact Integrable.integrableOn by fun_prop
    · exact MeasurableSet.preimage measurableSet_Ioi (by fun_prop)
    · have hx_ne : 2 * r⁻¹ * x != 0 := by
        intro hx0
        simp only [hx0, Set.mem_ofPred_eq, abs_zero] at hx
        linarith
      rw [le_sub_iff_add_le]; rw [← le_sub_iff_add_le']
      norm_num
      rw [one_div]
      refine (sinc_le_inv_abs hx_ne).trans ?_
      exact (inv_le_inv₀ (by positivity) (by positivity)).mpr (le_of_lt hx)
  _ <= 2 * ∫ x, 1 - sinc (2 * r⁻¹ * x) ∂μ := by
    grw [setIntegral_le_integral (by fun_prop) <| ae_of_all _ fun x => ?_]
    simp only [Pi.zero_apply, sub_nonneg]
    exact sinc_le_one (2 * r⁻¹ * x)
  _ <= 2 * ‖∫ x, 1 - sinc (2 * r⁻¹ * x) ∂μ‖ := by
    gcongr
    exact Real.le_norm_self _
  _ = 2⁻¹ * r *
      ‖2 * (r : Complex)⁻¹ + 2 * r⁻¹ - 2 * (2 * r⁻¹) * ∫ x, sinc (2 * r⁻¹ * x) ∂μ‖ := by
    norm_cast
    rw [← two_mul]; rw [mul_assoc 2]; rw [← mul_sub]; rw [norm_mul]; rw [Real.norm_ofNat]; rw [← mul_assoc]; rw [← mul_one_sub]; rw [norm_mul]; rw [Real.norm_of_nonneg (r := 2 * r⁻¹) (by positivity)]; rw [← mul_assoc]
    congr
    · ring_nf
      rw [mul_inv_cancel₀ (by positivity)]; rw [one_mul]
    · rw [integral_sub (integrable_const _) (integrable_sinc_const_mul _)]
      simp
  _ = 2⁻¹ * r * ‖∫ t in (-2 * r⁻¹)..(2 * r⁻¹), 1 - charFun μ t‖ := by
    rw [intervalIntegral.integral_sub intervalIntegrable_const intervalIntegrable_charFun]; rw [neg_mul]; rw [integral_charFun_Icc (by positivity)]
    simp

中文:
引理 measure实数_abs_gt_le_integral_charFun
  条件: [是概率测度 μ] (hr : 0 < r)
  证明: by
  have integrable_sinc_const_mul (r : Real) : Integrable (fun x => sinc (r * x)) μ :=
    (integrable_map_measure stronglyMeasurable_sinc.aestronglyMeasurable (by fun_prop)).mp
      integrable_sinc
  calc μ.real {x | r < |x|}
  _ = μ.real {x | 2 < |2 * r⁻¹ * x|} := by
    congr 1 with x
    simp only [Set.mem_ofPred_eq, abs_mul, Nat.abs_ofNat]
    rw [abs_of_nonneg (a := r⁻¹) (by positivity)]; rw [mul_assoc]; rw [← inv_mul_lt_iff₀ (by positivity)]; rw [inv_mul_cancel₀ (by positivity)]; rw [lt_inv_mul_iff₀ (by positivity)]; rw [mul_one]
  _ = ∫ x in {x | 2 < |2 * r⁻¹ * x|}, 1 ∂μ := by simp
  _ = 2 * ∫ x in {x | 2 < |2 * r⁻¹ * x|}, 2⁻¹ ∂μ := by
    rw [← integral_const_mul]
    congr with _
    rw [mul_inv_cancel₀ (by positivity)]
  _ <= 2 * ∫ x in {x | 2 < |2 * r⁻¹ * x|}, 1 - sinc (2 * r⁻¹ * x) ∂μ := by
    gcongr (2 : Real) * ?_
    refine setIntegral_mono_on ?_
      ((integrable_const _).sub (integrable_sinc_const_mul _)).integrableOn ?_ fun x hx => ?_
· exact Integrable.integrableOn by fun_prop
    · exact MeasurableSet.preimage measurableSet_Ioi (by fun_prop)
    · have hx_ne : 2 * r⁻¹ * x != 0 := by
        intro hx0
        simp only [hx0, Set.mem_ofPred_eq, abs_zero] at hx
        linarith
      rw [le_sub_iff_add_le]; rw [← le_sub_iff_add_le']
      norm_num
      rw [one_div]
      refine (sinc_le_inv_abs hx_ne).trans ?_
      exact (inv_le_inv₀ (by positivity) (by positivity)).mpr (le_of_lt hx)
  _ <= 2 * ∫ x, 1 - sinc (2 * r⁻¹ * x) ∂μ := by
    grw [setIntegral_le_integral (by fun_prop) <| ae_of_all _ fun x => ?_]
    simp only [Pi.zero_apply, sub_nonneg]
    exact sinc_le_one (2 * r⁻¹ * x)
  _ <= 2 * ‖∫ x, 1 - sinc (2 * r⁻¹ * x) ∂μ‖ := by
    gcongr
    exact Real.le_norm_self _
  _ = 2⁻¹ * r *
      ‖2 * (r : Complex)⁻¹ + 2 * r⁻¹ - 2 * (2 * r⁻¹) * ∫ x, sinc (2 * r⁻¹ * x) ∂μ‖ := by
    norm_cast
    rw [← two_mul]; rw [mul_assoc 2]; rw [← mul_sub]; rw [norm_mul]; rw [Real.norm_ofNat]; rw [← mul_assoc]; rw [← mul_one_sub]; rw [norm_mul]; rw [Real.norm_of_nonneg (r := 2 * r⁻¹) (by positivity)]; rw [← mul_assoc]
    congr
    · ring_nf
      rw [mul_inv_cancel₀ (by positivity)]; rw [one_mul]
    · rw [integral_sub (integrable_const _) (integrable_sinc_const_mul _)]
      simp
  _ = 2⁻¹ * r * ‖∫ t in (-2 * r⁻¹)..(2 * r⁻¹), 1 - charFun μ t‖ := by
    rw [intervalIntegral.integral_sub intervalIntegrable_const intervalIntegrable_charFun]; rw [neg_mul]; rw [integral_charFun_Icc (by positivity)]
    simp

Depends on / 依赖: Integrable, Nat.abs_ofNat, Set.mem_ofPred_eq, abs_mul, abs_ofNat, abs_of_nonneg, aestronglyMeasurable, fun_prop, integrable_map_measure, integrable_sinc, integrable_sinc_const_mul, mem_ofPred_eq, mul_assoc, positivit, stronglyMeasurable_sinc, stronglyMeasurable_sinc.aestronglyMeasurable
-/
lemma measureReal_abs_gt_le_integral_charFun [IsProbabilityMeasure μ] (hr : 0 < r) :
    μ.real {x | r < |x|} <= 2⁻¹ * r * ‖∫ t in (-2 * r⁻¹)..(2 * r⁻¹), 1 - charFun μ t‖ := by
  have integrable_sinc_const_mul (r : Real) : Integrable (fun x => sinc (r * x)) μ :=
    (integrable_map_measure stronglyMeasurable_sinc.aestronglyMeasurable (by fun_prop)).mp
      integrable_sinc
  calc μ.real {x | r < |x|}
  _ = μ.real {x | 2 < |2 * r⁻¹ * x|} := by
    congr 1 with x
    simp only [Set.mem_ofPred_eq, abs_mul, Nat.abs_ofNat]
    rw [abs_of_nonneg (a := r⁻¹) (by positivity)]; rw [mul_assoc]; rw [← inv_mul_lt_iff₀ (by positivity)]; rw [inv_mul_cancel₀ (by positivity)]; rw [lt_inv_mul_iff₀ (by positivity)]; rw [mul_one]
  _ = ∫ x in {x | 2 < |2 * r⁻¹ * x|}, 1 ∂μ := by simp
  _ = 2 * ∫ x in {x | 2 < |2 * r⁻¹ * x|}, 2⁻¹ ∂μ := by
    rw [← integral_const_mul]
    congr with _
    rw [mul_inv_cancel₀ (by positivity)]
  _ <= 2 * ∫ x in {x | 2 < |2 * r⁻¹ * x|}, 1 - sinc (2 * r⁻¹ * x) ∂μ := by
    gcongr (2 : Real) * ?_
    refine setIntegral_mono_on ?_
      ((integrable_const _).sub (integrable_sinc_const_mul _)).integrableOn ?_ fun x hx => ?_
· exact Integrable.integrableOn by fun_prop
    · exact MeasurableSet.preimage measurableSet_Ioi (by fun_prop)
    · have hx_ne : 2 * r⁻¹ * x != 0 := by
        intro hx0
        simp only [hx0, Set.mem_ofPred_eq, abs_zero] at hx
        linarith
      rw [le_sub_iff_add_le]; rw [← le_sub_iff_add_le']
      norm_num
      rw [one_div]
      refine (sinc_le_inv_abs hx_ne).trans ?_
      exact (inv_le_inv₀ (by positivity) (by positivity)).mpr (le_of_lt hx)
  _ <= 2 * ∫ x, 1 - sinc (2 * r⁻¹ * x) ∂μ := by
    grw [setIntegral_le_integral (by fun_prop) <| ae_of_all _ fun x => ?_]
    simp only [Pi.zero_apply, sub_nonneg]
    exact sinc_le_one (2 * r⁻¹ * x)
  _ <= 2 * ‖∫ x, 1 - sinc (2 * r⁻¹ * x) ∂μ‖ := by
    gcongr
    exact Real.le_norm_self _
  _ = 2⁻¹ * r *
      ‖2 * (r : Complex)⁻¹ + 2 * r⁻¹ - 2 * (2 * r⁻¹) * ∫ x, sinc (2 * r⁻¹ * x) ∂μ‖ := by
    norm_cast
    rw [← two_mul]; rw [mul_assoc 2]; rw [← mul_sub]; rw [norm_mul]; rw [Real.norm_ofNat]; rw [← mul_assoc]; rw [← mul_one_sub]; rw [norm_mul]; rw [Real.norm_of_nonneg (r := 2 * r⁻¹) (by positivity)]; rw [← mul_assoc]
    congr
    · ring_nf
      rw [mul_inv_cancel₀ (by positivity)]; rw [one_mul]
    · rw [integral_sub (integrable_const _) (integrable_sinc_const_mul _)]
      simp
  _ = 2⁻¹ * r * ‖∫ t in (-2 * r⁻¹)..(2 * r⁻¹), 1 - charFun μ t‖ := by
    rw [intervalIntegral.integral_sub intervalIntegrable_const intervalIntegrable_charFun]; rw [neg_mul]; rw [integral_charFun_Icc (by positivity)]
    simp

end Real

/--
lemma `measureReal_abs_dual_gt_le_integral_charFunDual` / 引理 `measureReal_abs_dual_gt_le_integral_charFunDual`

English:
lemma measureReal_abs_dual_gt_le_integral_charFunDual
  statement: {E : Type*} [NormedAddCommGroup E]
  proof: by
  have : IsProbabilityMeasure (μ.map L) := Measure.isProbabilityMeasure_map (by fun_prop)
  convert! measureReal_abs_gt_le_integral_charFun (μ := μ.map L) hr with x
  · rw [map_measureReal_apply (by fun_prop)]
    · simp
    · exact MeasurableSet.preimage measurableSet_Ioi (by fun_prop)
  · rw [charFun_map_eq_charFunDual_smul]

中文:
引理 measure实数_abs_dual_gt_le_integral_charFunDual
  结论: {E : 类型} [赋范交换加群 E]
  证明: by
  have : IsProbabilityMeasure (μ.map L) := Measure.isProbabilityMeasure_map (by fun_prop)
  convert! measureReal_abs_gt_le_integral_charFun (μ := μ.map L) hr with x
  · rw [map_measureReal_apply (by fun_prop)]
    · simp
    · exact MeasurableSet.preimage measurableSet_Ioi (by fun_prop)
  · rw [charFun_map_eq_charFunDual_smul]

Depends on / 依赖: IsProbabilityMeasure, MeasurableSet, MeasurableSet.preimage, Measure, Measure.isProbabilityMeasure_map, charFun_map_eq_charFunDual_smul, convert, fun_prop, isProbabilityMeasure_map, map_measureReal_apply, measurableSet_Ioi, measureReal_abs_gt_le_integral_charFun, preimage
-/
lemma measureReal_abs_dual_gt_le_integral_charFunDual {E : Type*} [NormedAddCommGroup E]
    [NormedSpace Real E] {mE : MeasurableSpace E} [OpensMeasurableSpace E]
    {μ : Measure E} [IsProbabilityMeasure μ] (L : StrongDual Real E) {r : Real} (hr : 0 < r) :
    μ.real {x | r < |L x|} <= 2⁻¹ * r * ‖∫ t in -2 * r⁻¹..2 * r⁻¹, 1 - charFunDual μ (t • L)‖ := by
  have : IsProbabilityMeasure (μ.map L) := Measure.isProbabilityMeasure_map (by fun_prop)
  convert! measureReal_abs_gt_le_integral_charFun (μ := μ.map L) hr with x
  · rw [map_measureReal_apply (by fun_prop)]
    · simp
    · exact MeasurableSet.preimage measurableSet_Ioi (by fun_prop)
  · rw [charFun_map_eq_charFunDual_smul]

/--
lemma `measureReal_abs_inner_gt_le_integral_charFun` / 引理 `measureReal_abs_inner_gt_le_integral_charFun`

English:
lemma measureReal_abs_inner_gt_le_integral_charFun
  statement: {E : Type*} [SeminormedAddCommGroup E]
  proof: by
  have : IsProbabilityMeasure (μ.map (fun x => ⟪a, x⟫)) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  convert! measureReal_abs_gt_le_integral_charFun (μ := μ.map (fun x => ⟪a, x⟫)) hr with x
  · rw [map_measureReal_apply (by fun_prop)]
    · simp
    · exact MeasurableSet.preimage measurableSet_Ioi (by fun_prop)
  · simp only [charFun_apply, inner_smul_right, conj_trivial, ofReal_mul, RCLike.inner_apply]
    rw [integral_map (by fun_prop) (by fun_prop)]
    simp_rw [real_inner_comm a]

中文:
引理 measure实数_abs_inner_gt_le_integral_charFun
  结论: {E : 类型} [SeminormedAddComm群 E]
  证明: by
  have : IsProbabilityMeasure (μ.map (fun x => ⟪a, x⟫)) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  convert! measureReal_abs_gt_le_integral_charFun (μ := μ.map (fun x => ⟪a, x⟫)) hr with x
  · rw [map_measureReal_apply (by fun_prop)]
    · simp
    · exact MeasurableSet.preimage measurableSet_Ioi (by fun_prop)
  · simp only [charFun_apply, inner_smul_right, conj_trivial, ofReal_mul, RCLike.inner_apply]
    rw [integral_map (by fun_prop) (by fun_prop)]
    simp_rw [real_inner_comm a]

Depends on / 依赖: IsProbabilityMeasure, MeasurableSet, MeasurableSet.preimage, Measure, Measure.isProbabilityMeasure_map, RCLike, RCLike.inner_apply, charFun_apply, conj_trivial, convert, fun_prop, inner_apply, inner_smul_right, integral_map, isProbabilityMeasure_map, map_measureReal_apply, measurableSet_Ioi, measureReal_abs_gt_le_integral_charFun, ofReal_mul, preimage
-/
lemma measureReal_abs_inner_gt_le_integral_charFun {E : Type*} [SeminormedAddCommGroup E]
    [InnerProductSpace Real E] {mE : MeasurableSpace E} [OpensMeasurableSpace E]
    {μ : Measure E} [IsProbabilityMeasure μ] {a : E} {r : Real} (hr : 0 < r) :
    μ.real {x | r < |⟪a, x⟫|} <= 2⁻¹ * r * ‖∫ t in -2 * r⁻¹..2 * r⁻¹, 1 - charFun μ (t • a)‖ := by
  have : IsProbabilityMeasure (μ.map (fun x => ⟪a, x⟫)) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  convert! measureReal_abs_gt_le_integral_charFun (μ := μ.map (fun x => ⟪a, x⟫)) hr with x
  · rw [map_measureReal_apply (by fun_prop)]
    · simp
    · exact MeasurableSet.preimage measurableSet_Ioi (by fun_prop)
  · simp only [charFun_apply, inner_smul_right, conj_trivial, ofReal_mul, RCLike.inner_apply]
    rw [integral_map (by fun_prop) (by fun_prop)]
    simp_rw [real_inner_comm a]

end MeasureTheory
