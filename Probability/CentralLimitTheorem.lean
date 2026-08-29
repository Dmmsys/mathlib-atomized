/-
Copyright (c) 2024 Thomas Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Zhu, Etienne Marion
-/
module

public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.MeasureTheory.Function.ConvergenceInDistribution

import Mathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion
import Mathlib.MeasureTheory.Measure.LevyConvergence
import Mathlib.Probability.Independence.CharacteristicFunction

/-!
# Central limit theorem

We prove the central limit theorem in dimension 1.

## Main statement

* `tendstoInDistribution_inv_sqrt_mul_sum_sub`: Given a sequence of random variables
  `X : ℕ → Ω → ℝ` that are independent, identically distributed with mean `μ` and variance `v`,
  and a random variable `Y : Ω' → ℝ` following `gaussianReal 0 v`, the sequence
  `n ↦ (√n)⁻¹ * (∑ k ∈ Finset.range n, X k ω - n * μ)` converges to `Y` in distribution.

## Tags

central limit theorem
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Complex Filter
open scoped Real Topology

namespace ProbabilityTheory

variable {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
  {P : Measure Ω} {P' : Measure Ω'} {X : Nat -> Ω -> Real} {Y : Ω' -> Real}

/--
lemma `charFun_inv_sqrt_mul_sum` / 引理 `charFun_inv_sqrt_mul_sum`

English:
lemma charFun_inv_sqrt_mul_sum
  statement: (hindep : iIndepFun X P)
  proof: by
  have mX n := (hident n).aemeasurable_fst
  rw [charFun_map_mul_comp]; rw [(hindep.restrict _).charFun_map_fun_finsetSum_eq_prod (fun _ _ => mX _)]
  · simp [fun i => (hident i).map_eq]
  · exact Finset.aemeasurable_fun_sum _ fun _ _ => mX _

中文:
引理 charFun_inv_sqrt_mul_sum
  结论: (hindep : iIndepFun X P)
  证明: by
  have mX n := (hident n).aemeasurable_fst
  rw [charFun_map_mul_comp]; rw [(hindep.restrict _).charFun_map_fun_finsetSum_eq_prod (fun _ _ => mX _)]
  · simp [fun i => (hident i).map_eq]
  · exact Finset.aemeasurable_fun_sum _ fun _ _ => mX _

Depends on / 依赖: Finset, Finset.aemeasurable_fun_sum, aemeasurable_fst, aemeasurable_fun_sum, charFun_map_fun_finsetSum_eq_prod, charFun_map_mul_comp, hident, hindep, hindep.restrict, map_eq, restrict
-/
lemma charFun_inv_sqrt_mul_sum (hindep : iIndepFun X P)
    (hident : forall (i : Nat), IdentDistrib (X i) (X 0) P P) {n : Nat} {t : Real} :
    charFun (P.map (fun ω => (√n)⁻¹ * ∑ k in Finset.range n, X k ω)) t =
      (charFun (P.map (X 0)) ((√n)⁻¹ * t)) ^ n := by
  have mX n := (hident n).aemeasurable_fst
  rw [charFun_map_mul_comp]; rw [(hindep.restrict _).charFun_map_fun_finsetSum_eq_prod (fun _ _ => mX _)]
  · simp [fun i => (hident i).map_eq]
  · exact Finset.aemeasurable_fun_sum _ fun _ _ => mX _

variable [IsProbabilityMeasure P]

/--
lemma `tendsto_charFun_inv_sqrt_mul_pow` / 引理 `tendsto_charFun_inv_sqrt_mul_pow`

English:
lemma tendsto_charFun_inv_sqrt_mul_pow
  statement: {X : Ω -> Real}
  proof: by
  apply tendsto_pow_exp_of_isLittleO_sub_add_div
  suffices (fun (n : Nat) => charFun (Measure.map X P) ((√n)⁻¹ * t) -
      (1 + (-(((√n)⁻¹ * t) ^ 2 / 2) : Complex))) =o[atTop] fun n => ((√n)⁻¹ * t) ^ 2 by
    have aux : (fun (n : Nat) => ‖(1 / n : Complex)‖) = fun (n : Nat) => ‖(1 / n : Real)‖ := by simp
    rw [← Asymptotics.isLittleO_norm_right]; rw [aux]; rw [Asymptotics.isLittleO_norm_right]
    refine .of_const_mul_right (c := t ^ 2) ?_
    convert! this using 4 with n <;> norm_cast <;> simp [field]
  have : Tendsto (fun (n : Nat) => (√n)⁻¹ * t) atTop (𝓝 0) := by
    rw [← zero_mul t]
    exact .mul_const t (tendsto_inv_atTop_zero.comp <| Real.tendsto_sqrt_atTop.comp <|
      tendsto_natCast_atTop_atTop)
  convert! (taylor_charFun_two hX h0 h1).comp_tendsto this using 2
  simp
  ring

中文:
引理 tendsto_charFun_inv_sqrt_mul_pow
  结论: {X : Ω -> 实数}
  证明: by
  apply tendsto_pow_exp_of_isLittleO_sub_add_div
  suffices (fun (n : Nat) => charFun (Measure.map X P) ((√n)⁻¹ * t) -
      (1 + (-(((√n)⁻¹ * t) ^ 2 / 2) : Complex))) =o[atTop] fun n => ((√n)⁻¹ * t) ^ 2 by
    have aux : (fun (n : Nat) => ‖(1 / n : Complex)‖) = fun (n : Nat) => ‖(1 / n : Real)‖ := by simp
    rw [← Asymptotics.isLittleO_norm_right]; rw [aux]; rw [Asymptotics.isLittleO_norm_right]
    refine .of_const_mul_right (c := t ^ 2) ?_
    convert! this using 4 with n <;> norm_cast <;> simp [field]
  have : Tendsto (fun (n : Nat) => (√n)⁻¹ * t) atTop (𝓝 0) := by
    rw [← zero_mul t]
    exact .mul_const t (tendsto_inv_atTop_zero.comp <| Real.tendsto_sqrt_atTop.comp <|
      tendsto_natCast_atTop_atTop)
  convert! (taylor_charFun_two hX h0 h1).comp_tendsto this using 2
  simp
  ring

Depends on / 依赖: Asymptotics, Asymptotics.isLittleO_norm_right, Measure, Measure.map, charFun, convert, isLittleO_norm_right, of_const_mul_right, tendsto_pow_exp_of_isLittleO_sub_add_div
-/
lemma tendsto_charFun_inv_sqrt_mul_pow {X : Ω -> Real}
    (hX : AEMeasurable X P) (h0 : P[X] = 0) (h1 : P[X ^ 2] = 1) (t : Real) :
    Tendsto (fun (n : Nat) => (charFun (P.map X) ((√n)⁻¹ * t)) ^ n) atTop (𝓝 (exp (- t ^ 2 / 2))) := by
  apply tendsto_pow_exp_of_isLittleO_sub_add_div
  suffices (fun (n : Nat) => charFun (Measure.map X P) ((√n)⁻¹ * t) -
      (1 + (-(((√n)⁻¹ * t) ^ 2 / 2) : Complex))) =o[atTop] fun n => ((√n)⁻¹ * t) ^ 2 by
    have aux : (fun (n : Nat) => ‖(1 / n : Complex)‖) = fun (n : Nat) => ‖(1 / n : Real)‖ := by simp
    rw [← Asymptotics.isLittleO_norm_right]; rw [aux]; rw [Asymptotics.isLittleO_norm_right]
    refine .of_const_mul_right (c := t ^ 2) ?_
    convert! this using 4 with n <;> norm_cast <;> simp [field]
  have : Tendsto (fun (n : Nat) => (√n)⁻¹ * t) atTop (𝓝 0) := by
    rw [← zero_mul t]
    exact .mul_const t (tendsto_inv_atTop_zero.comp <| Real.tendsto_sqrt_atTop.comp <|
      tendsto_natCast_atTop_atTop)
  convert! (taylor_charFun_two hX h0 h1).comp_tendsto this using 2
  simp
  ring

variable [IsProbabilityMeasure P']

/--
theorem `tendstoInDistribution_inv_sqrt_mul_sum` / 定理 `tendstoInDistribution_inv_sqrt_mul_sum`

English:
theorem tendstoInDistribution_inv_sqrt_mul_sum
  statement: (hY : HasLaw Y (gaussianReal 0 1) P')
  proof: .const_mul (Finset.aemeasurable_fun_sum _ fun _ _ => (hident _).aemeasurable_fst) _
  tendsto := by
    refine ProbabilityMeasure.tendsto_iff_tendsto_charFun.2 fun t => ?_
    rw! [hY.map_eq]
    simpa [charFun_inv_sqrt_mul_sum hindep hident, charFun_gaussianReal, neg_div] using
      tendsto_charFun_inv_sqrt_mul_pow (hident 0).aemeasurable_fst h0 h1 t

中文:
定理 tendstoInDistribution_inv_sqrt_mul_sum
  结论: (hY : 有Law Y (gaussian实数 0 1) P')
  证明: .const_mul (Finset.aemeasurable_fun_sum _ fun _ _ => (hident _).aemeasurable_fst) _
  tendsto := by
    refine ProbabilityMeasure.tendsto_iff_tendsto_charFun.2 fun t => ?_
    rw! [hY.map_eq]
    simpa [charFun_inv_sqrt_mul_sum hindep hident, charFun_gaussianReal, neg_div] using
      tendsto_charFun_inv_sqrt_mul_pow (hident 0).aemeasurable_fst h0 h1 t

Depends on / 依赖: Finset, Finset.aemeasurable_fun_sum, ProbabilityMeasure, ProbabilityMeasure.tendsto_iff_tendsto_charFun, aemeasurable_fst, aemeasurable_fun_sum, charFun_gaussianReal, charFun_inv_sqrt_mul_sum, const_mul, hY.map_eq, hident, hindep, map_eq, neg_div, tendsto, tendsto_charFun_inv_sqrt_mul_pow, tendsto_iff_tendsto_charFun
-/
theorem tendstoInDistribution_inv_sqrt_mul_sum (hY : HasLaw Y (gaussianReal 0 1) P')
    (h0 : P[X 0] = 0) (h1 : P[X 0 ^ 2] = 1) (hindep : iIndepFun X P)
    (hident : forall (i : Nat), IdentDistrib (X i) (X 0) P P) :
    TendstoInDistribution (fun (n : Nat) ω => (√n)⁻¹ * ∑ k in Finset.range n, X k ω) atTop Y
      (fun _ => P) P' where
  forall_aemeasurable n :=
    .const_mul (Finset.aemeasurable_fun_sum _ fun _ _ => (hident _).aemeasurable_fst) _
  tendsto := by
    refine ProbabilityMeasure.tendsto_iff_tendsto_charFun.2 fun t => ?_
    rw! [hY.map_eq]
    simpa [charFun_inv_sqrt_mul_sum hindep hident, charFun_gaussianReal, neg_div] using
      tendsto_charFun_inv_sqrt_mul_pow (hident 0).aemeasurable_fst h0 h1 t

/--
theorem `tendstoInDistribution_inv_sqrt_mul_var_mul_sum_sub` / 定理 `tendstoInDistribution_inv_sqrt_mul_var_mul_sum_sub`

English:
theorem tendstoInDistribution_inv_sqrt_mul_var_mul_sum_sub
  proof: by
  have mX0 := (hident 0).aemeasurable_fst
have intX0 : Integrable (X 0) P := memLp_one_iff_integrable.1
    (memLp_two_of_variance_ne_zero mX0.aestronglyMeasurable hX).mono_exponent (by simp)
  have (n : Nat) ω : (√(n * Var[X 0; P]))⁻¹ * (∑ k in Finset.range n, X k ω - n * P[X 0]) =
      (√n)⁻¹ * ∑ k in Finset.range n, (X k ω - P[X 0]) / √Var[X 0; P] := by
    rw [← Finset.sum_div]; rw [Finset.sum_sub_distrib]
    simp [field]
  simp_rw [this]
  convert! tendstoInDistribution_inv_sqrt_mul_sum hY ?_ ?_ ?_ ?_
  · rw [integral_div, integral_sub intX0 (by simp)]
    simp
  · simp only [Pi.pow_apply, div_pow]
    rw [integral_div]; rw [← variance_eq_integral mX0]; rw [Real.sq_sqrt (variance_nonneg _ _)]; rw [div_self hX]
  · exact hindep.comp (fun _ x => (x - P[X 0]) / √Var[X 0; P]) (by fun_prop)
  · convert! fun n => (hident n).comp (u := fun x => (x - P[X 0]) / √Var[X 0; P]) (by fun_prop)

中文:
定理 tendstoInDistribution_inv_sqrt_mul_var_mul_sum_sub
  证明: by
  have mX0 := (hident 0).aemeasurable_fst
have intX0 : Integrable (X 0) P := memLp_one_iff_integrable.1
    (memLp_two_of_variance_ne_zero mX0.aestronglyMeasurable hX).mono_exponent (by simp)
  have (n : Nat) ω : (√(n * Var[X 0; P]))⁻¹ * (∑ k in Finset.range n, X k ω - n * P[X 0]) =
      (√n)⁻¹ * ∑ k in Finset.range n, (X k ω - P[X 0]) / √Var[X 0; P] := by
    rw [← Finset.sum_div]; rw [Finset.sum_sub_distrib]
    simp [field]
  simp_rw [this]
  convert! tendstoInDistribution_inv_sqrt_mul_sum hY ?_ ?_ ?_ ?_
  · rw [integral_div, integral_sub intX0 (by simp)]
    simp
  · simp only [Pi.pow_apply, div_pow]
    rw [integral_div]; rw [← variance_eq_integral mX0]; rw [Real.sq_sqrt (variance_nonneg _ _)]; rw [div_self hX]
  · exact hindep.comp (fun _ x => (x - P[X 0]) / √Var[X 0; P]) (by fun_prop)
  · convert! fun n => (hident n).comp (u := fun x => (x - P[X 0]) / √Var[X 0; P]) (by fun_prop)
-/
private theorem tendstoInDistribution_inv_sqrt_mul_var_mul_sum_sub
    (hY : HasLaw Y (gaussianReal 0 1) P')
    (hX : Var[X 0; P] != 0) (hindep : iIndepFun X P)
    (hident : forall (i : Nat), IdentDistrib (X i) (X 0) P P) :
    TendstoInDistribution
      (fun (n : Nat) ω => (√(n * Var[X 0; P]))⁻¹ * (∑ k in Finset.range n, X k ω - n * P[X 0]))
      atTop Y (fun _ => P) P' := by
  have mX0 := (hident 0).aemeasurable_fst
have intX0 : Integrable (X 0) P := memLp_one_iff_integrable.1
    (memLp_two_of_variance_ne_zero mX0.aestronglyMeasurable hX).mono_exponent (by simp)
  have (n : Nat) ω : (√(n * Var[X 0; P]))⁻¹ * (∑ k in Finset.range n, X k ω - n * P[X 0]) =
      (√n)⁻¹ * ∑ k in Finset.range n, (X k ω - P[X 0]) / √Var[X 0; P] := by
    rw [← Finset.sum_div]; rw [Finset.sum_sub_distrib]
    simp [field]
  simp_rw [this]
  convert! tendstoInDistribution_inv_sqrt_mul_sum hY ?_ ?_ ?_ ?_
  · rw [integral_div, integral_sub intX0 (by simp)]
    simp
  · simp only [Pi.pow_apply, div_pow]
    rw [integral_div]; rw [← variance_eq_integral mX0]; rw [Real.sq_sqrt (variance_nonneg _ _)]; rw [div_self hX]
  · exact hindep.comp (fun _ x => (x - P[X 0]) / √Var[X 0; P]) (by fun_prop)
  · convert! fun n => (hident n).comp (u := fun x => (x - P[X 0]) / √Var[X 0; P]) (by fun_prop)

/-- **Central Limit Theorem:** Given a sequence of random variables `X : ℕ → Ω → ℝ` that are
independent, identically distributed with mean `μ` and variance `v`, and a random variable
`Y : Ω' → ℝ` following `gaussianReal 0 v`, the sequence
`n ↦ (√n)⁻¹ * (∑ k ∈ Finset.range n, X k ω - n * μ)` converges to `Y` in distribution. -/
@[wikidata Q190391]
/--
theorem `tendstoInDistribution_inv_sqrt_mul_sum_sub` / 定理 `tendstoInDistribution_inv_sqrt_mul_sum_sub`

English:
theorem tendstoInDistribution_inv_sqrt_mul_sum_sub
  proof: by
  obtain h | h := eq_or_ne Var[X 0; P] 0
  · have : forallᵐ ω ∂P, forall n, X n ω = P[X 0] := by
      refine ae_all_iff.2 fun n => ?_
      convert! (ae_eq_integral_of_variance_eq_zero ((hident n).memLp_iff.2 hX)) ?_ using 3
      · rw [(hident n).integral_eq]
      · rwa [(hident n).variance_eq]
    have mX (n : Nat) := (hident n).aemeasurable_fst
    refine tendstoInDistribution_of_identDistrib 0 (fun n => ?_) ?_
    · refine ⟨by fun_prop, by fun_prop, Measure.map_congr ?_⟩
      filter_upwards [this] with ω hω
      simp [hω]
    · exact ⟨by fun_prop, by fun_prop, by simp [hY.map_eq, h]⟩
  have : HasLaw (fun ω => Y ω / √Var[X 0; P]) (gaussianReal 0 1) P' := by
    convert! gaussianReal_div_const hY _
    · simp
    · ext; simp [h]
  convert!
    (tendstoInDistribution_inv_sqrt_mul_var_mul_sum_sub this h hindep hident).continuous_comp (g :=
      (√Var[X 0; P] * ·)) (by fun_prop)
  · simp [field] -- simp [field, hX] triggers the unused simp arguments linter
    field_simp [h]
  · ext
    simp [field] -- simp [field, hX] triggers the unused simp arguments linter
    field_simp [h]

中文:
定理 tendstoInDistribution_inv_sqrt_mul_sum_sub
  证明: by
  obtain h | h := eq_or_ne Var[X 0; P] 0
  · have : forallᵐ ω ∂P, forall n, X n ω = P[X 0] := by
      refine ae_all_iff.2 fun n => ?_
      convert! (ae_eq_integral_of_variance_eq_zero ((hident n).memLp_iff.2 hX)) ?_ using 3
      · rw [(hident n).integral_eq]
      · rwa [(hident n).variance_eq]
    have mX (n : Nat) := (hident n).aemeasurable_fst
    refine tendstoInDistribution_of_identDistrib 0 (fun n => ?_) ?_
    · refine ⟨by fun_prop, by fun_prop, Measure.map_congr ?_⟩
      filter_upwards [this] with ω hω
      simp [hω]
    · exact ⟨by fun_prop, by fun_prop, by simp [hY.map_eq, h]⟩
  have : HasLaw (fun ω => Y ω / √Var[X 0; P]) (gaussianReal 0 1) P' := by
    convert! gaussianReal_div_const hY _
    · simp
    · ext; simp [h]
  convert!
    (tendstoInDistribution_inv_sqrt_mul_var_mul_sum_sub this h hindep hident).continuous_comp (g :=
      (√Var[X 0; P] * ·)) (by fun_prop)
  · simp [field] -- simp [field, hX] triggers the unused simp arguments linter
    field_simp [h]
  · ext
    simp [field] -- simp [field, hX] triggers the unused simp arguments linter
    field_simp [h]

Depends on / 依赖: Measure, Measure.map_congr, ae_all_iff, ae_eq_integral_of_variance_eq_zero, aemeasurable_fst, convert, eq_or_ne, filter_upwards, fun_prop, hident, integral_eq, map_congr, memLp_iff, tendstoInDistribution_of_identDistrib, variance_eq
-/
theorem tendstoInDistribution_inv_sqrt_mul_sum_sub
    (hY : HasLaw Y (gaussianReal 0 Var[X 0; P].toNNReal) P')
    (hX : MemLp (X 0) 2 P) (hindep : iIndepFun X P)
    (hident : forall (i : Nat), IdentDistrib (X i) (X 0) P P) :
    TendstoInDistribution
      (fun (n : Nat) ω => (√n)⁻¹ * (∑ k in Finset.range n, X k ω - n * P[X 0]))
      atTop Y (fun _ => P) P' := by
  obtain h | h := eq_or_ne Var[X 0; P] 0
  · have : forallᵐ ω ∂P, forall n, X n ω = P[X 0] := by
      refine ae_all_iff.2 fun n => ?_
      convert! (ae_eq_integral_of_variance_eq_zero ((hident n).memLp_iff.2 hX)) ?_ using 3
      · rw [(hident n).integral_eq]
      · rwa [(hident n).variance_eq]
    have mX (n : Nat) := (hident n).aemeasurable_fst
    refine tendstoInDistribution_of_identDistrib 0 (fun n => ?_) ?_
    · refine ⟨by fun_prop, by fun_prop, Measure.map_congr ?_⟩
      filter_upwards [this] with ω hω
      simp [hω]
    · exact ⟨by fun_prop, by fun_prop, by simp [hY.map_eq, h]⟩
  have : HasLaw (fun ω => Y ω / √Var[X 0; P]) (gaussianReal 0 1) P' := by
    convert! gaussianReal_div_const hY _
    · simp
    · ext; simp [h]
  convert!
    (tendstoInDistribution_inv_sqrt_mul_var_mul_sum_sub this h hindep hident).continuous_comp (g :=
      (√Var[X 0; P] * ·)) (by fun_prop)
  · simp [field] -- simp [field, hX] triggers the unused simp arguments linter
    field_simp [h]
  · ext
    simp [field] -- simp [field, hX] triggers the unused simp arguments linter
    field_simp [h]

end ProbabilityTheory
