/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
-/
module

public import Mathlib.Analysis.Convex.Continuous
public import Mathlib.Analysis.Convex.Integral
public import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
public import Mathlib.Probability.Kernel.Composition.MeasureCompProd

import Mathlib.Analysis.Convex.Approximation
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Kernel.Composition.RadonNikodym

/-!
# Integrals of functions of Radon-Nikodym derivatives

## Main statements

* `mul_le_integral_rnDeriv_of_ac`: for a convex continuous function `f` on `[0, ∞)`, if `μ`
  is absolutely continuous with respect to `ν`, then
  `ν.real univ * f (μ.real univ / ν.real univ) ≤ ∫ x, f (μ.rnDeriv ν x).toReal ∂ν`.
* `ConvexOn.integrable_apply_rnDeriv_of_integrable_compProd`: for `f` a convex function on `[0, ∞)`,
  if `f ((μ ⊗ₘ κ).rnDeriv (ν ⊗ₘ η) (a, b))` is integrable, then `f (μ.rnDeriv ν a)` is integrable.

-/

public section


open Set ProbabilityTheory
open scoped ENNReal

namespace MeasureTheory

variable {𝓧 : Type*} {m𝓧 : MeasurableSpace 𝓧} {μ ν : Measure 𝓧} {f : Real -> Real}

@[fun_prop]
/--
lemma `Measure.integrable_toReal_rnDeriv` / 引理 `Measure.integrable_toReal_rnDeriv`

English:
lemma Measure.integrable_toReal_rnDeriv
  given: [IsFiniteMeasure μ]
  proof: integrable_toReal_of_lintegral_ne_top (Measure.measurable_rnDeriv _ _).aemeasurable
    (Measure.lintegral_rnDeriv_lt_top _ _).ne

中文:
引理 测度.integrable_to实数_rnDeriv
  条件: [是有限测度 μ]
  证明: integrable_toReal_of_lintegral_ne_top (Measure.measurable_rnDeriv _ _).aemeasurable
    (Measure.lintegral_rnDeriv_lt_top _ _).ne

Depends on / 依赖: Measure, Measure.lintegral_rnDeriv_lt_top, Measure.measurable_rnDeriv, aemeasurable, integrable_toReal_of_lintegral_ne_top, lintegral_rnDeriv_lt_top, measurable_rnDeriv
-/
lemma Measure.integrable_toReal_rnDeriv [IsFiniteMeasure μ] :
    Integrable (fun x => (μ.rnDeriv ν x).toReal) ν :=
  integrable_toReal_of_lintegral_ne_top (Measure.measurable_rnDeriv _ _).aemeasurable
    (Measure.lintegral_rnDeriv_lt_top _ _).ne

/--
lemma `le_integral_rnDeriv_of_ac` / 引理 `le_integral_rnDeriv_of_ac`

English:
lemma le_integral_rnDeriv_of_ac
  statement: [IsFiniteMeasure μ] [IsProbabilityMeasure ν]
  proof: by
  have hf_cont' : ContinuousOn f (Ici 0) := hf_cvx.continuousOn_Ici hf_cont
  calc f (μ.real univ)
    = f (∫ x, (μ.rnDeriv ν x).toReal ∂ν) := by rw [Measure.integral_toReal_rnDeriv hμν]
  _ <= ∫ x, f (μ.rnDeriv ν x).toReal ∂ν := by
    rw [← average_eq_integral]; rw [← average_eq_integral]
    e

中文:
引理 le_integral_rnDeriv_of_ac
  结论: [是有限测度 μ] [是概率测度 ν]
  证明: by
  have hf_cont' : ContinuousOn f (Ici 0) := hf_cvx.continuousOn_Ici hf_cont
  calc f (μ.real univ)
    = f (∫ x, (μ.rnDeriv ν x).toReal ∂ν) := by rw [Measure.integral_toReal_rnDeriv hμν]
  _ <= ∫ x, f (μ.rnDeriv ν x).toReal ∂ν := by
    rw [← average_eq_integral]; rw [← average_eq_integral]
    e

Depends on / 依赖: ContinuousOn, ConvexOn, ConvexOn.map_average_le, Measure, Measure.integrable_toReal_rnDeriv, Measure.integral_toReal_rnDeriv, Nonempty, average_eq_integral, continuousOn_Ici, hf_cont, hf_cvx, hf_cvx.continuousOn_Ici, hf_int, integrable_toReal_rnDeriv, integral_toReal_rnDeriv, isClosed_Ici, map_average_le, rnDeriv, toReal, top_nonempty
-/
lemma le_integral_rnDeriv_of_ac [IsFiniteMeasure μ] [IsProbabilityMeasure ν]
    (hf_cvx : ConvexOn Real (Ici 0) f) (hf_cont : ContinuousWithinAt f (Ici 0) 0)
    (hf_int : Integrable (fun x => f (μ.rnDeriv ν x).toReal) ν) (hμν : μ ≪ ν) :
    f (μ.real univ) <= ∫ x, f (μ.rnDeriv ν x).toReal ∂ν := by
  have hf_cont' : ContinuousOn f (Ici 0) := hf_cvx.continuousOn_Ici hf_cont
  calc f (μ.real univ)
    = f (∫ x, (μ.rnDeriv ν x).toReal ∂ν) := by rw [Measure.integral_toReal_rnDeriv hμν]
  _ <= ∫ x, f (μ.rnDeriv ν x).toReal ∂ν := by
    rw [← average_eq_integral]; rw [← average_eq_integral]
    exact ConvexOn.map_average_le hf_cvx hf_cont' isClosed_Ici (by simp)
      Measure.integrable_toReal_rnDeriv hf_int

/--
lemma `mul_le_integral_rnDeriv_of_ac` / 引理 `mul_le_integral_rnDeriv_of_ac`

English:
lemma mul_le_integral_rnDeriv_of_ac
  statement: [IsFiniteMeasure μ] [IsFiniteMeasure ν]
  proof: by
  by_cases hν : ν = 0
  · simp [hν]
  have : NeZero ν := ⟨hν⟩
  let μ' := (ν univ)⁻¹ • μ
  let ν' := (ν univ)⁻¹ • ν
  have : IsFiniteMeasure μ' := μ.smul_finite (by simp [hν])
  have hμν' : μ' ≪ ν' := hμν.smul _
  have h_rnDeriv_eq : μ'.rnDeriv ν' =ᵐ[ν] μ.rnDeriv ν := by
    have h1' : μ'.rnDeriv

中文:
引理 mul_le_integral_rnDeriv_of_ac
  结论: [是有限测度 μ] [是有限测度 ν]
  证明: by
  by_cases hν : ν = 0
  · simp [hν]
  have : NeZero ν := ⟨hν⟩
  let μ' := (ν univ)⁻¹ • μ
  let ν' := (ν univ)⁻¹ • ν
  have : IsFiniteMeasure μ' := μ.smul_finite (by simp [hν])
  have hμν' : μ' ≪ ν' := hμν.smul _
  have h_rnDeriv_eq : μ'.rnDeriv ν' =ᵐ[ν] μ.rnDeriv ν := by
    have h1' : μ'.rnDeriv

Depends on / 依赖: IsFiniteMeasure, Measure, Measure.ae_ennreal_smul_measure_eq, Measure.rnDeriv_smul_left_of_ne_top, NeZero, ae_ennreal_smul_measure_eq, h_rnDeriv_eq, rnDeriv, rnDeriv_smul_left_of_ne_top, smul_finite
-/
lemma mul_le_integral_rnDeriv_of_ac [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hf_cvx : ConvexOn Real (Ici 0) f) (hf_cont : ContinuousWithinAt f (Ici 0) 0)
    (hf_int : Integrable (fun x => f (μ.rnDeriv ν x).toReal) ν) (hμν : μ ≪ ν) :
    ν.real univ * f (μ.real univ / ν.real univ)
      <= ∫ x, f (μ.rnDeriv ν x).toReal ∂ν := by
  by_cases hν : ν = 0
  · simp [hν]
  have : NeZero ν := ⟨hν⟩
  let μ' := (ν univ)⁻¹ • μ
  let ν' := (ν univ)⁻¹ • ν
  have : IsFiniteMeasure μ' := μ.smul_finite (by simp [hν])
  have hμν' : μ' ≪ ν' := hμν.smul _
  have h_rnDeriv_eq : μ'.rnDeriv ν' =ᵐ[ν] μ.rnDeriv ν := by
    have h1' : μ'.rnDeriv ν' =ᵐ[ν'] (ν univ)⁻¹ • μ.rnDeriv ν' :=
      Measure.rnDeriv_smul_left_of_ne_top' (μ := ν') (ν := μ) (by simp [hν])
    have h1 : μ'.rnDeriv ν' =ᵐ[ν] (ν univ)⁻¹ • μ.rnDeriv ν' := by
      rwa [Measure.ae_ennreal_smul_measure_eq] at h1'
      simp
    have h2 : μ.rnDeriv ν' =ᵐ[ν] (ν univ)⁻¹⁻¹ • μ.rnDeriv ν :=
      Measure.rnDeriv_smul_right_of_ne_top' (μ := ν) (ν := μ) (by simp) (by simp [hν])
    filter_upwards [h1, h2] with x h1 h2
    rw [h1]; rw [Pi.smul_apply]; rw [smul_eq_mul]; rw [h2]
    simp only [inv_inv, Pi.smul_apply, smul_eq_mul]
    rw [← mul_assoc]; rw [ENNReal.inv_mul_cancel]; rw [one_mul]
    · simp [hν]
    · simp
  have h_eq : ∫ x, f (μ'.rnDeriv ν' x).toReal ∂ν'
      = (ν.real univ)⁻¹ * ∫ x, f ((μ.rnDeriv ν x).toReal) ∂ν := by
    rw [integral_smul_measure]; rw [smul_eq_mul]; rw [ENNReal.toReal_inv]
    congr 1
    refine integral_congr_ae ?_
    filter_upwards [h_rnDeriv_eq] with x hx
    rw [hx]
  have h : f (μ'.real univ) <= ∫ x, f (μ'.rnDeriv ν' x).toReal ∂ν' :=
    le_integral_rnDeriv_of_ac hf_cvx hf_cont ?_ hμν'
  swap
  · refine Integrable.smul_measure ?_ (by simp [hν])
    refine (integrable_congr ?_).mpr hf_int
    filter_upwards [h_rnDeriv_eq] with x hx
    rw [hx]
  rw [h_eq]; rw [mul_comm]; rw [← div_le_iff₀]; rw [div_eq_inv_mul]; rw [inv_inv] at h
  · convert! h
    · simp only [div_eq_inv_mul, Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul,
      ENNReal.toReal_inv, μ', measureReal_def]
  · simp [ENNReal.toReal_pos_iff, hν, measureReal_def]

section Integrable

variable {𝓨 : Type*} {m𝓨 : MeasurableSpace 𝓨} {κ η : Kernel 𝓧 𝓨} {f : Real -> Real}
  [IsFiniteMeasure μ] [IsFiniteMeasure ν]

/--
lemma `lintegral_rnDeriv_compProd` / 引理 `lintegral_rnDeriv_compProd`

English:
lemma lintegral_rnDeriv_compProd
  statement: [IsSFiniteKernel κ] [IsFiniteKernel η]
  proof: by
  refine ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite (by fun_prop) (κ.measurable_coe .univ) ?_
  intro s hs hsμ
  calc ∫⁻ a in s, ∫⁻ b, (μ otimesₘ κ).rnDeriv (μ otimesₘ η) (a, b) ∂(η a) ∂μ
  _ = ∫⁻ a in s, ∫⁻ b in univ, (μ otimesₘ κ).rnDeriv (μ otimesₘ η) (a, b) ∂(η a) ∂μ := by simp
  _ = ∫⁻ a

中文:
引理 lintegral_rnDeriv_compProd
  结论: [是SFiniteKernel κ] [是FiniteKernel η]
  证明: by
  refine ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite (by fun_prop) (κ.measurable_coe .univ) ?_
  intro s hs hsμ
  calc ∫⁻ a in s, ∫⁻ b, (μ otimesₘ κ).rnDeriv (μ otimesₘ η) (a, b) ∂(η a) ∂μ
  _ = ∫⁻ a in s, ∫⁻ b in univ, (μ otimesₘ κ).rnDeriv (μ otimesₘ η) (a, b) ∂(η a) ∂μ := by simp
  _ = ∫⁻ a

Depends on / 依赖: Measure, Measure.compProd_apply_prod, Measure.setLIntegral_compProd, Measure.setLIntegral_rnDeriv, ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite, compProd_apply_prod, fun_prop, measurable_coe, rnDeriv, setLIntegral_compProd, setLIntegral_rnDeriv
-/
lemma lintegral_rnDeriv_compProd [IsSFiniteKernel κ] [IsFiniteKernel η]
    (hκη : μ otimesₘ κ ≪ μ otimesₘ η) :
    forallᵐ a ∂μ, ∫⁻ b, (μ otimesₘ κ).rnDeriv (μ otimesₘ η) (a, b) ∂η a = κ a univ := by
  refine ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite (by fun_prop) (κ.measurable_coe .univ) ?_
  intro s hs hsμ
  calc ∫⁻ a in s, ∫⁻ b, (μ otimesₘ κ).rnDeriv (μ otimesₘ η) (a, b) ∂(η a) ∂μ
  _ = ∫⁻ a in s, ∫⁻ b in univ, (μ otimesₘ κ).rnDeriv (μ otimesₘ η) (a, b) ∂(η a) ∂μ := by simp
  _ = ∫⁻ a in s, (κ a) univ ∂μ := by
    rw [← Measure.setLIntegral_compProd (by fun_prop) hs .univ]; rw [Measure.setLIntegral_rnDeriv hκη]; rw [Measure.compProd_apply_prod hs .univ]

variable [IsMarkovKernel κ] [IsMarkovKernel η]

/--
lemma `_root_.ConvexOn.apply_rnDeriv_ae_le_integral` / 引理 `_root_.ConvexOn.apply_rnDeriv_ae_le_integral`

English:
lemma _root_.ConvexOn.apply_rnDeriv_ae_le_integral
  statement: (hf : StronglyMeasurable f)
  proof: by
  have hf_cont : ContinuousOn f (Ici 0) := hf_cvx.continuousOn_Ici hf_cont_at
  have h_lt_top : forallᵐ a ∂ν, forallᵐ b ∂η a, (μ otimesₘ κ).rnDeriv (ν otimesₘ η) (a, b) < ∞ :=
Measure.ae_ae_of_ae_compProd (μ otimesₘ κ).rnDeriv_lt_top (ν otimesₘ η)
  have h_integrable : Integrable (fun x => ((μ ot

中文:
引理 _root_.ConvexOn.apply_rnDeriv_ae_le_integral
  结论: (hf : StronglyMeasurable f)
  证明: by
  have hf_cont : ContinuousOn f (Ici 0) := hf_cvx.continuousOn_Ici hf_cont_at
  have h_lt_top : forallᵐ a ∂ν, forallᵐ b ∂η a, (μ otimesₘ κ).rnDeriv (ν otimesₘ η) (a, b) < ∞ :=
Measure.ae_ae_of_ae_compProd (μ otimesₘ κ).rnDeriv_lt_top (ν otimesₘ η)
  have h_integrable : Integrable (fun x => ((μ ot

Depends on / 依赖: ContinuousOn, Integrable, Measure, Measure.ae_ae_of_ae_compProd, Measure.integrable_compProd_iff, Measure.integrable_toReal_rnDeriv, StronglyMeasurable, StronglyMeasurable.aestronglyMeasu, ae_ae_of_ae_compProd, aestronglyMeasu, continuousOn_Ici, h_int, h_integrable, h_lt_top, hf_cont, hf_cont_at, hf_cvx, hf_cvx.continuousOn_Ici, integrable_compProd_iff, integrable_toReal_rnDeriv
-/
lemma _root_.ConvexOn.apply_rnDeriv_ae_le_integral (hf : StronglyMeasurable f)
    (hf_cvx : ConvexOn Real (Ici 0) f) (hf_cont_at : ContinuousWithinAt f (Ici 0) 0)
    (h_int : Integrable (fun p => f ((μ otimesₘ κ).rnDeriv (ν otimesₘ η) p).toReal) (ν otimesₘ η))
    (hκη : μ otimesₘ κ ≪ μ otimesₘ η) :
    (fun a => f (μ.rnDeriv ν a).toReal)
      <=ᵐ[ν] fun a => ∫ b, f ((μ otimesₘ κ).rnDeriv (ν otimesₘ η) (a, b)).toReal ∂(η a) := by
  have hf_cont : ContinuousOn f (Ici 0) := hf_cvx.continuousOn_Ici hf_cont_at
  have h_lt_top : forallᵐ a ∂ν, forallᵐ b ∂η a, (μ otimesₘ κ).rnDeriv (ν otimesₘ η) (a, b) < ∞ :=
Measure.ae_ae_of_ae_compProd (μ otimesₘ κ).rnDeriv_lt_top (ν otimesₘ η)
  have h_integrable : Integrable (fun x => ((μ otimesₘ κ).rnDeriv (ν otimesₘ η) x).toReal) (ν otimesₘ η) :=
    Measure.integrable_toReal_rnDeriv
  rw [Measure.integrable_compProd_iff] at h_integrable h_int
  rotate_left
  · exact StronglyMeasurable.aestronglyMeasurable (by fun_prop)
  · exact StronglyMeasurable.aestronglyMeasurable (by fun_prop)
  have h_ae1 : forallᵐ a ∂ν,
      μ.rnDeriv ν a * ∫⁻ b, (μ otimesₘ κ).rnDeriv (μ otimesₘ η) (a, b) ∂(η a) = μ.rnDeriv ν a := by
    filter_upwards [Measure.ae_rnDeriv_ne_zero_imp_of_ae _ (lintegral_rnDeriv_compProd hκη)]
      with a ha
    by_cases h0 : μ.rnDeriv ν a = 0
    · simp [h0]
    · simp [ha h0]
  have h_ae2 : forallᵐ a ∂ν, forallᵐ b ∂(η a), μ.rnDeriv ν a * (μ otimesₘ κ).rnDeriv (μ otimesₘ η) (a, b) =
      (μ otimesₘ κ).rnDeriv (ν otimesₘ η) (a, b) := by
    have h_compProd : (fun p => μ.rnDeriv ν p.1 * (μ otimesₘ κ).rnDeriv (μ otimesₘ η) p) =ᵐ[ν otimesₘ η]
        (μ otimesₘ κ).rnDeriv (ν otimesₘ η) := (rnDeriv_compProd hκη ν).symm
    rwa [Filter.EventuallyEq, Measure.ae_compProd_iff] at h_compProd
    simp only [measurableSet_setOfPred]
    fun_prop
  filter_upwards [h_ae1, h_ae2, h_lt_top, h_integrable.1, h_int.1]
    with a h_eq_one h_mul_eq h_lt_top h_int' h_int
  calc f (μ.rnDeriv ν a).toReal
    = f (μ.rnDeriv ν a * ∫⁻ b, (μ otimesₘ κ).rnDeriv (μ otimesₘ η) (a, b) ∂(η a)).toReal := by simp [h_eq_one]
  _ = f (∫⁻ b, (μ.rnDeriv ν a) * (μ otimesₘ κ).rnDeriv (μ otimesₘ η) (a, b) ∂(η a)).toReal := by
    rw [lintegral_const_mul _ (by fun_prop)]
  _ = f (∫⁻ b, (μ otimesₘ κ).rnDeriv (ν otimesₘ η) (a, b) ∂(η a)).toReal := by
    congr 2
    refine lintegral_congr_ae ?_
    filter_upwards [h_mul_eq] with b hb using hb
  _ = f (∫ b, ((μ otimesₘ κ).rnDeriv (ν otimesₘ η) (a, b)).toReal ∂(η a)) := by
    rw [integral_toReal (by fun_prop) h_lt_top]
  _ <= ∫ b, f ((μ otimesₘ κ).rnDeriv (ν otimesₘ η) (a, b)).toReal ∂(η a) := by
    rw [← average_eq_integral]; rw [← average_eq_integral]
    exact ConvexOn.map_average_le hf_cvx hf_cont isClosed_Ici (by simp) h_int' h_int

/--
lemma `_root_.ConvexOn.integrable_apply_rnDeriv_of_integrable_compProd` / 引理 `_root_.ConvexOn.integrable_apply_rnDeriv_of_integrable_compProd`

English:
lemma _root_.ConvexOn.integrable_apply_rnDeriv_of_integrable_compProd
  statement: (hf : StronglyMeasurable f)
  proof: by
  have hf_cont : ContinuousOn f (Ici 0) := hf_cvx.continuousOn_Ici hf_cont_at
  obtain ⟨c, c', h⟩ : exists c c', forall x, 0 <= x -> c * x + c' <= f x :=
    hf_cvx.exists_affine_le_real isClosed_Ici hf_cont.lowerSemicontinuousOn
  refine integrable_of_le_of_le (f := fun a => f (μ.rnDeriv ν a).to

中文:
引理 _root_.ConvexOn.integrable_apply_rnDeriv_of_integrable_compProd
  结论: (hf : StronglyMeasurable f)
  证明: by
  have hf_cont : ContinuousOn f (Ici 0) := hf_cvx.continuousOn_Ici hf_cont_at
  obtain ⟨c, c', h⟩ : exists c c', forall x, 0 <= x -> c * x + c' <= f x :=
    hf_cvx.exists_affine_le_real isClosed_Ici hf_cont.lowerSemicontinuousOn
  refine integrable_of_le_of_le (f := fun a => f (μ.rnDeriv ν a).to

Depends on / 依赖: ContinuousOn, StronglyMeasurable, StronglyMeasurable.aestronglyMeasurabl, aestronglyMeasurabl, continuousOn_Ici, exists_affine_le_real, fun_prop, hf_cont, hf_cont.lowerSemicontinuousOn, hf_cont_at, hf_cvx, hf_cvx.continuousOn_Ici, hf_cvx.exists_affine_le_real, integrable_of_le_of_le, isClosed_Ici, lowerSemicontinuousOn, rnDeriv, toReal
-/
lemma _root_.ConvexOn.integrable_apply_rnDeriv_of_integrable_compProd (hf : StronglyMeasurable f)
    (hf_cvx : ConvexOn Real (Ici 0) f) (hf_cont_at : ContinuousWithinAt f (Ici 0) 0)
    (hf_int : Integrable (fun p => f ((μ otimesₘ κ).rnDeriv (ν otimesₘ η) p).toReal) (ν otimesₘ η))
    (hκη : μ otimesₘ κ ≪ μ otimesₘ η) :
    Integrable (fun a => f (μ.rnDeriv ν a).toReal) ν := by
  have hf_cont : ContinuousOn f (Ici 0) := hf_cvx.continuousOn_Ici hf_cont_at
  obtain ⟨c, c', h⟩ : exists c c', forall x, 0 <= x -> c * x + c' <= f x :=
    hf_cvx.exists_affine_le_real isClosed_Ici hf_cont.lowerSemicontinuousOn
  refine integrable_of_le_of_le (f := fun a => f (μ.rnDeriv ν a).toReal)
    (g₁ := fun x => c * (μ.rnDeriv ν x).toReal + c')
    (g₂ := fun x => ∫ b, f ((μ otimesₘ κ).rnDeriv (ν otimesₘ η) (x, b)).toReal ∂(η x))
    ?_ ?_ ?_ (by fun_prop) ?_
  · exact StronglyMeasurable.aestronglyMeasurable (by fun_prop)
  · exact ae_of_all _ fun x => h _ ENNReal.toReal_nonneg
  · exact hf_cvx.apply_rnDeriv_ae_le_integral hf hf_cont_at hf_int hκη
  · exact hf_int.integral_compProd

end Integrable

end MeasureTheory
