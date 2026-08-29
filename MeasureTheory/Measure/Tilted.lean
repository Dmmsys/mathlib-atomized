/-
Copyright (c) 2023 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym

/-!
# Exponentially tilted measures

The exponential tilting of a measure `μ` on `α` by a function `f : α → ℝ` is the measure with
density `x ↦ exp (f x) / ∫ y, exp (f y) ∂μ` with respect to `μ`. This is sometimes also called
the Esscher transform.

The definition is mostly used for `f` linear, in which case the exponentially tilted measure belongs
to the natural exponential family of the base measure. Exponentially tilted measures for general `f`
can be used for example to establish variational expressions for the Kullback-Leibler divergence.

## Main definitions

* `Measure.tilted μ f`: exponential tilting of `μ` by `f`, equal to
  `μ.withDensity (fun x ↦ ENNReal.ofReal (exp (f x) / ∫ x, exp (f x) ∂μ))`.

-/

@[expose] public section

open Real

open scoped ENNReal NNReal

namespace MeasureTheory

variable {α : Type*} {mα : MeasurableSpace α} {μ : Measure α} {f : α -> Real}

/-- Exponentially tilted measure. When `x ↦ exp (f x)` is integrable, `μ.tilted f` is the
probability measure with density with respect to `μ` proportional to `exp (f x)`. Otherwise it is 0.
-/
noncomputable
/--
Definition of `Measure.tilted` / `Measure.tilted` 的定义

English:
definition Measure.tilted
  signature: (μ : Measure α) (f : α -> Real)
  body: μ.withDensity (fun x => ENNReal.ofReal (exp (f x) / ∫ x, exp (f x) ∂μ))

@[simp]

中文:
定义 测度.tilted
  签名: (μ : 测度 α) (f : α -> 实数)
  定义体: μ.withDensity (fun x => ENNReal.ofReal (exp (f x) / ∫ x, exp (f x) ∂μ))

@[simp]

Depends on / 依赖: ENNReal, ENNReal.ofReal, ofReal, withDensity
-/
def Measure.tilted (μ : Measure α) (f : α -> Real) : Measure α :=
  μ.withDensity (fun x => ENNReal.ofReal (exp (f x) / ∫ x, exp (f x) ∂μ))

@[simp]
/--
lemma `tilted_of_not_integrable` / 引理 `tilted_of_not_integrable`

English:
lemma tilted_of_not_integrable
  given: (hf : ¬ Integrable (fun x => exp (f x)) μ)
  statement: μ.tilted f = 0
  proof: by
  rw [Measure.tilted]; rw [integral_undef hf]
  simp

@[simp]

中文:
引理 tilted_of_not_integrable
  条件: (hf : ¬ 可积 (fun x => exp (f x)) μ)
  结论: μ.tilted f = 0
  证明: by
  rw [Measure.tilted]; rw [integral_undef hf]
  simp

@[simp]

Depends on / 依赖: Measure, Measure.tilted, integral_undef, tilted
-/
lemma tilted_of_not_integrable (hf : ¬ Integrable (fun x => exp (f x)) μ) : μ.tilted f = 0 := by
  rw [Measure.tilted]; rw [integral_undef hf]
  simp

@[simp]
/--
lemma `tilted_of_not_aemeasurable` / 引理 `tilted_of_not_aemeasurable`

English:
lemma tilted_of_not_aemeasurable
  given: (hf : ¬ AEMeasurable f μ)
  statement: μ.tilted f = 0
  proof: by
  refine tilted_of_not_integrable ?_
  suffices ¬ AEMeasurable (fun x => exp (f x)) μ by exact fun h => this h.1.aemeasurable
  exact fun h => hf (aemeasurable_of_aemeasurable_exp h)

@[simp]

中文:
引理 tilted_of_not_aemeasurable
  条件: (hf : ¬ 几乎处处可测 f μ)
  结论: μ.tilted f = 0
  证明: by
  refine tilted_of_not_integrable ?_
  suffices ¬ AEMeasurable (fun x => exp (f x)) μ by exact fun h => this h.1.aemeasurable
  exact fun h => hf (aemeasurable_of_aemeasurable_exp h)

@[simp]

Depends on / 依赖: AEMeasurable, aemeasurable, aemeasurable_of_aemeasurable_exp, tilted_of_not_integrable
-/
lemma tilted_of_not_aemeasurable (hf : ¬ AEMeasurable f μ) : μ.tilted f = 0 := by
  refine tilted_of_not_integrable ?_
  suffices ¬ AEMeasurable (fun x => exp (f x)) μ by exact fun h => this h.1.aemeasurable
  exact fun h => hf (aemeasurable_of_aemeasurable_exp h)

@[simp]
/--
lemma `tilted_zero_measure` / 引理 `tilted_zero_measure`

English:
lemma tilted_zero_measure
  given: (f : α -> Real)
  statement: (0 : Measure α).tilted f = 0
  proof: by simp [Measure.tilted]

@[simp]

中文:
引理 tilted_zero_measure
  条件: (f : α -> 实数)
  结论: (0 : 测度 α).tilted f = 0
  证明: by simp [Measure.tilted]

@[simp]

Depends on / 依赖: Measure, Measure.tilted, tilted
-/
lemma tilted_zero_measure (f : α -> Real) : (0 : Measure α).tilted f = 0 := by simp [Measure.tilted]

@[simp]
/--
lemma `tilted_const'` / 引理 `tilted_const'`

English:
lemma tilted_const'
  given: (μ : Measure α) (c : Real)
  proof: by
  cases eq_zero_or_neZero μ with
  | inl h => rw [h]; simp
  | inr h0 =>
    simp only [Measure.tilted, withDensity_const, integral_const, smul_eq_mul]
    by_cases h_univ : μ Set.univ = ∞
    · simp only [measureReal_def, h_univ, ENNReal.toReal_top, zero_mul, div_zero,
      ENNReal.ofReal_zero, zero_smul, ENNReal.inv_top]
    congr
    rw [div_eq_mul_inv]; rw [mul_inv]; rw [mul_comm]; rw [mul_assoc]; rw [inv_mul_cancel₀ (exp_pos _).ne']; rw [mul_one]; rw [measureReal_def]; rw [← ENNReal.toReal_inv]; rw [ENNReal.ofReal_toReal]
    simp [h0.out]

中文:
引理 tilted_const'
  条件: (μ : 测度 α) (c : 实数)
  证明: by
  cases eq_zero_or_neZero μ with
  | inl h => rw [h]; simp
  | inr h0 =>
    simp only [Measure.tilted, withDensity_const, integral_const, smul_eq_mul]
    by_cases h_univ : μ Set.univ = ∞
    · simp only [measureReal_def, h_univ, ENNReal.toReal_top, zero_mul, div_zero,
      ENNReal.ofReal_zero, zero_smul, ENNReal.inv_top]
    congr
    rw [div_eq_mul_inv]; rw [mul_inv]; rw [mul_comm]; rw [mul_assoc]; rw [inv_mul_cancel₀ (exp_pos _).ne']; rw [mul_one]; rw [measureReal_def]; rw [← ENNReal.toReal_inv]; rw [ENNReal.ofReal_toReal]
    simp [h0.out]

Depends on / 依赖: ENNReal, ENNReal.inv_top, ENNReal.ofReal_toR, ENNReal.ofReal_zero, ENNReal.toReal_inv, ENNReal.toReal_top, Measure, Measure.tilted, Set.univ, div_eq_mul_inv, div_zero, eq_zero_or_neZero, exp_pos, h_univ, integral_const, inv_top, measureReal_def, mul_assoc, mul_comm, mul_inv
-/
lemma tilted_const' (μ : Measure α) (c : Real) :
    μ.tilted (fun _ => c) = (μ Set.univ)⁻¹ • μ := by
  cases eq_zero_or_neZero μ with
  | inl h => rw [h]; simp
  | inr h0 =>
    simp only [Measure.tilted, withDensity_const, integral_const, smul_eq_mul]
    by_cases h_univ : μ Set.univ = ∞
    · simp only [measureReal_def, h_univ, ENNReal.toReal_top, zero_mul, div_zero,
      ENNReal.ofReal_zero, zero_smul, ENNReal.inv_top]
    congr
    rw [div_eq_mul_inv]; rw [mul_inv]; rw [mul_comm]; rw [mul_assoc]; rw [inv_mul_cancel₀ (exp_pos _).ne']; rw [mul_one]; rw [measureReal_def]; rw [← ENNReal.toReal_inv]; rw [ENNReal.ofReal_toReal]
    simp [h0.out]

/--
lemma `tilted_const` / 引理 `tilted_const`

English:
lemma tilted_const
  given: (μ : Measure α) [IsProbabilityMeasure μ] (c : Real)
  proof: by simp

@[simp]

中文:
引理 tilted_const
  条件: (μ : 测度 α) [是概率测度 μ] (c : 实数)
  证明: by simp

@[simp]
-/
lemma tilted_const (μ : Measure α) [IsProbabilityMeasure μ] (c : Real) :
    μ.tilted (fun _ => c) = μ := by simp

@[simp]
/--
lemma `tilted_zero'` / 引理 `tilted_zero'`

English:
lemma tilted_zero'
  given: (μ : Measure α)
  statement: μ.tilted 0 = (μ Set.univ)⁻¹ • μ
  proof: by
  change μ.tilted (fun _ => 0) = (μ Set.univ)⁻¹ • μ
  simp

中文:
引理 tilted_zero'
  条件: (μ : 测度 α)
  结论: μ.tilted 0 = (μ 集合.univ)⁻¹ • μ
  证明: by
  change μ.tilted (fun _ => 0) = (μ Set.univ)⁻¹ • μ
  simp

Depends on / 依赖: Set.univ, tilted
-/
lemma tilted_zero' (μ : Measure α) : μ.tilted 0 = (μ Set.univ)⁻¹ • μ := by
  change μ.tilted (fun _ => 0) = (μ Set.univ)⁻¹ • μ
  simp

/--
lemma `tilted_zero` / 引理 `tilted_zero`

English:
lemma tilted_zero
  given: (μ : Measure α) [IsProbabilityMeasure μ]
  statement: μ.tilted 0 = μ
  proof: by simp

中文:
引理 tilted_zero
  条件: (μ : 测度 α) [是概率测度 μ]
  结论: μ.tilted 0 = μ
  证明: by simp
-/
lemma tilted_zero (μ : Measure α) [IsProbabilityMeasure μ] : μ.tilted 0 = μ := by simp

/--
lemma `tilted_congr` / 引理 `tilted_congr`

English:
lemma tilted_congr
  given: {g : α -> Real} (hfg : f =ᵐ[μ] g)
  proof: by
  have h_int_eq : ∫ x, exp (f x) ∂μ = ∫ x, exp (g x) ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards [hfg] with x hx
    rw [hx]
  refine withDensity_congr_ae ?_
  filter_upwards [hfg] with x hx
  rw [h_int_eq]; rw [hx]

中文:
引理 tilted_congr
  条件: {g : α -> 实数} (hfg : f =ᵐ[μ] g)
  证明: by
  have h_int_eq : ∫ x, exp (f x) ∂μ = ∫ x, exp (g x) ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards [hfg] with x hx
    rw [hx]
  refine withDensity_congr_ae ?_
  filter_upwards [hfg] with x hx
  rw [h_int_eq]; rw [hx]

Depends on / 依赖: filter_upwards, h_int_eq, integral_congr_ae, withDensity_congr_ae
-/
lemma tilted_congr {g : α -> Real} (hfg : f =ᵐ[μ] g) :
    μ.tilted f = μ.tilted g := by
  have h_int_eq : ∫ x, exp (f x) ∂μ = ∫ x, exp (g x) ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards [hfg] with x hx
    rw [hx]
  refine withDensity_congr_ae ?_
  filter_upwards [hfg] with x hx
  rw [h_int_eq]; rw [hx]

/--
lemma `tilted_eq_withDensity_nnreal` / 引理 `tilted_eq_withDensity_nnreal`

English:
lemma tilted_eq_withDensity_nnreal
  given: (μ : Measure α) (f : α -> Real)
  proof: by
  rw [Measure.tilted]
  congr with x
  rw [ENNReal.ofReal_eq_coe_nnreal]

中文:
引理 tilted_eq_withDensity_nnreal
  条件: (μ : 测度 α) (f : α -> 实数)
  证明: by
  rw [Measure.tilted]
  congr with x
  rw [ENNReal.ofReal_eq_coe_nnreal]

Depends on / 依赖: ENNReal, ENNReal.ofReal_eq_coe_nnreal, Measure, Measure.tilted, ofReal_eq_coe_nnreal, tilted
-/
lemma tilted_eq_withDensity_nnreal (μ : Measure α) (f : α -> Real) :
    μ.tilted f = μ.withDensity (fun x => ((↑) : Real>=0 -> Real>=0∞)
      (.mk (exp (f x) / ∫ x, exp (f x) ∂μ) (by positivity))) := by
  rw [Measure.tilted]
  congr with x
  rw [ENNReal.ofReal_eq_coe_nnreal]

/--
lemma `tilted_apply'` / 引理 `tilted_apply'`

English:
lemma tilted_apply'
  given: (μ : Measure α) (f : α -> Real) {s : Set α} (hs : MeasurableSet s)
  proof: by
  rw [Measure.tilted]; rw [withDensity_apply _ hs]

中文:
引理 tilted_apply'
  条件: (μ : 测度 α) (f : α -> 实数) {s : 集合 α} (hs : 可测集 s)
  证明: by
  rw [Measure.tilted]; rw [withDensity_apply _ hs]

Depends on / 依赖: Measure, Measure.tilted, tilted, withDensity_apply
-/
lemma tilted_apply' (μ : Measure α) (f : α -> Real) {s : Set α} (hs : MeasurableSet s) :
    μ.tilted f s = ∫⁻ a in s, ENNReal.ofReal (exp (f a) / ∫ x, exp (f x) ∂μ) ∂μ := by
  rw [Measure.tilted]; rw [withDensity_apply _ hs]

/--
lemma `tilted_apply` / 引理 `tilted_apply`

English:
lemma tilted_apply
  given: (μ : Measure α) [SFinite μ] (f : α -> Real) (s : Set α)
  proof: by
  rw [Measure.tilted]; rw [withDensity_apply' _ s]

中文:
引理 tilted_apply
  条件: (μ : 测度 α) [SFinite μ] (f : α -> 实数) (s : 集合 α)
  证明: by
  rw [Measure.tilted]; rw [withDensity_apply' _ s]

Depends on / 依赖: Measure, Measure.tilted, tilted, withDensity_apply
-/
lemma tilted_apply (μ : Measure α) [SFinite μ] (f : α -> Real) (s : Set α) :
    μ.tilted f s = ∫⁻ a in s, ENNReal.ofReal (exp (f a) / ∫ x, exp (f x) ∂μ) ∂μ := by
  rw [Measure.tilted]; rw [withDensity_apply' _ s]

/--
lemma `tilted_apply_eq_ofReal_integral'` / 引理 `tilted_apply_eq_ofReal_integral'`

English:
lemma tilted_apply_eq_ofReal_integral'
  given: {s : Set α} (f : α -> Real) (hs : MeasurableSet s)
  proof: by
  by_cases hf : Integrable (fun x => exp (f x)) μ
  · rw [tilted_apply' _ _ hs, ← ofReal_integral_eq_lintegral_ofReal]
    · exact hf.integrableOn.div_const _
    · exact ae_of_all _ (fun _ => by positivity)
  · simp only [hf, not_false_eq_true, tilted_of_not_integrable, Measure.coe_zero,
      Pi.zero_apply, integral_undef hf, div_zero, integral_zero, ENNReal.ofReal_zero]

中文:
引理 tilted_apply_eq_of实数_integral'
  条件: {s : 集合 α} (f : α -> 实数) (hs : 可测集 s)
  证明: by
  by_cases hf : Integrable (fun x => exp (f x)) μ
  · rw [tilted_apply' _ _ hs, ← ofReal_integral_eq_lintegral_ofReal]
    · exact hf.integrableOn.div_const _
    · exact ae_of_all _ (fun _ => by positivity)
  · simp only [hf, not_false_eq_true, tilted_of_not_integrable, Measure.coe_zero,
      Pi.zero_apply, integral_undef hf, div_zero, integral_zero, ENNReal.ofReal_zero]

Depends on / 依赖: ENNReal, ENNReal.ofReal_zero, Integrable, Measure, Measure.coe_zero, Pi.zero_apply, ae_of_all, coe_zero, div_const, div_zero, hf.integrableOn.div_const, integrableOn, integral_undef, integral_zero, not_false_eq_true, ofReal_integral_eq_lintegral_ofReal, ofReal_zero, tilted_apply, tilted_of_not_integrable, zero_apply
-/
lemma tilted_apply_eq_ofReal_integral' {s : Set α} (f : α -> Real) (hs : MeasurableSet s) :
    μ.tilted f s = ENNReal.ofReal (∫ a in s, exp (f a) / ∫ x, exp (f x) ∂μ ∂μ) := by
  by_cases hf : Integrable (fun x => exp (f x)) μ
  · rw [tilted_apply' _ _ hs, ← ofReal_integral_eq_lintegral_ofReal]
    · exact hf.integrableOn.div_const _
    · exact ae_of_all _ (fun _ => by positivity)
  · simp only [hf, not_false_eq_true, tilted_of_not_integrable, Measure.coe_zero,
      Pi.zero_apply, integral_undef hf, div_zero, integral_zero, ENNReal.ofReal_zero]

/--
lemma `tilted_apply_eq_ofReal_integral` / 引理 `tilted_apply_eq_ofReal_integral`

English:
lemma tilted_apply_eq_ofReal_integral
  given: [SFinite μ] (f : α -> Real) (s : Set α)
  proof: by
  by_cases hf : Integrable (fun x => exp (f x)) μ
  · rw [tilted_apply _ _, ← ofReal_integral_eq_lintegral_ofReal]
    · exact hf.integrableOn.div_const _
    · exact ae_of_all _ (fun _ => by positivity)
  · simp [tilted_of_not_integrable hf, integral_undef hf]

中文:
引理 tilted_apply_eq_of实数_integral
  条件: [SFinite μ] (f : α -> 实数) (s : 集合 α)
  证明: by
  by_cases hf : Integrable (fun x => exp (f x)) μ
  · rw [tilted_apply _ _, ← ofReal_integral_eq_lintegral_ofReal]
    · exact hf.integrableOn.div_const _
    · exact ae_of_all _ (fun _ => by positivity)
  · simp [tilted_of_not_integrable hf, integral_undef hf]

Depends on / 依赖: Integrable, ae_of_all, div_const, hf.integrableOn.div_const, integrableOn, integral_undef, ofReal_integral_eq_lintegral_ofReal, tilted_apply, tilted_of_not_integrable
-/
lemma tilted_apply_eq_ofReal_integral [SFinite μ] (f : α -> Real) (s : Set α) :
    μ.tilted f s = ENNReal.ofReal (∫ a in s, exp (f a) / ∫ x, exp (f x) ∂μ ∂μ) := by
  by_cases hf : Integrable (fun x => exp (f x)) μ
  · rw [tilted_apply _ _, ← ofReal_integral_eq_lintegral_ofReal]
    · exact hf.integrableOn.div_const _
    · exact ae_of_all _ (fun _ => by positivity)
  · simp [tilted_of_not_integrable hf, integral_undef hf]

/--
lemma `isProbabilityMeasure_tilted` / 引理 `isProbabilityMeasure_tilted`

English:
lemma isProbabilityMeasure_tilted
  given: [NeZero μ] (hf : Integrable (fun x => exp (f x)) μ)
  proof: by
  constructor
  simp_rw [tilted_apply' _ _ MeasurableSet.univ, setLIntegral_univ,
    ENNReal.ofReal_div_of_pos (integral_exp_pos hf), div_eq_mul_inv]
  rw [lintegral_mul_const'' _ hf.1.aemeasurable.ennreal_ofReal]; rw [← ofReal_integral_eq_lintegral_ofReal hf (ae_of_all _ fun _ => (exp_pos _).le)]; rw [ENNReal.mul_inv_cancel]
  · simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    exact integral_exp_pos hf
  · simp

中文:
引理 isProbabilityMeasure_tilted
  条件: [NeZero μ] (hf : 可积 (fun x => exp (f x)) μ)
  证明: by
  constructor
  simp_rw [tilted_apply' _ _ MeasurableSet.univ, setLIntegral_univ,
    ENNReal.ofReal_div_of_pos (integral_exp_pos hf), div_eq_mul_inv]
  rw [lintegral_mul_const'' _ hf.1.aemeasurable.ennreal_ofReal]; rw [← ofReal_integral_eq_lintegral_ofReal hf (ae_of_all _ fun _ => (exp_pos _).le)]; rw [ENNReal.mul_inv_cancel]
  · simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    exact integral_exp_pos hf
  · simp

Depends on / 依赖: ENNReal, ENNReal.mul_inv_cancel, ENNReal.ofReal_div_of_pos, ENNReal.ofReal_eq_zero, MeasurableSet, MeasurableSet.univ, ae_of_all, aemeasurable, aemeasurable.ennreal_ofReal, div_eq_mul_inv, ennreal_ofReal, exp_pos, integral_exp_pos, lintegral_mul_const, mul_inv_cancel, ne_eq, not_le, ofReal_div_of_pos, ofReal_eq_zero, ofReal_integral_eq_lintegral_ofReal
-/
lemma isProbabilityMeasure_tilted [NeZero μ] (hf : Integrable (fun x => exp (f x)) μ) :
    IsProbabilityMeasure (μ.tilted f) := by
  constructor
  simp_rw [tilted_apply' _ _ MeasurableSet.univ, setLIntegral_univ,
    ENNReal.ofReal_div_of_pos (integral_exp_pos hf), div_eq_mul_inv]
  rw [lintegral_mul_const'' _ hf.1.aemeasurable.ennreal_ofReal]; rw [← ofReal_integral_eq_lintegral_ofReal hf (ae_of_all _ fun _ => (exp_pos _).le)]; rw [ENNReal.mul_inv_cancel]
  · simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    exact integral_exp_pos hf
  · simp

/--
Instance `isZeroOrProbabilityMeasure_tilted` / 实例 `isZeroOrProbabilityMeasure_tilted`

English:
instance isZeroOrProbabilityMeasure_tilted
  signature: : IsZeroOrProbabilityMeasure (μ.tilted f)
  body: by
  rcases eq_zero_or_neZero μ with hμ | hμ
  · simp only [hμ, tilted_zero_measure]
    infer_instance
  by_cases hf : Integrable (fun x => exp (f x)) μ
  · have := isProbabilityMeasure_tilted hf
    infer_instance
  · simp only [hf, not_false_eq_true, tilted_of_not_integrable]
    infer_instance

中文:
实例 isZeroOrProbabilityMeasure_tilted
  签名: : 是ZeroOrProbabilityMeasure (μ.tilted f)
  定义体: by
  rcases eq_zero_or_neZero μ with hμ | hμ
  · simp only [hμ, tilted_zero_measure]
    infer_instance
  by_cases hf : Integrable (fun x => exp (f x)) μ
  · have := isProbabilityMeasure_tilted hf
    infer_instance
  · simp only [hf, not_false_eq_true, tilted_of_not_integrable]
    infer_instance

Depends on / 依赖: Integrable, eq_zero_or_neZero, infer_instance, isProbabilityMeasure_tilted, not_false_eq_true, tilted_of_not_integrable, tilted_zero_measure
-/
instance isZeroOrProbabilityMeasure_tilted : IsZeroOrProbabilityMeasure (μ.tilted f) := by
  rcases eq_zero_or_neZero μ with hμ | hμ
  · simp only [hμ, tilted_zero_measure]
    infer_instance
  by_cases hf : Integrable (fun x => exp (f x)) μ
  · have := isProbabilityMeasure_tilted hf
    infer_instance
  · simp only [hf, not_false_eq_true, tilted_of_not_integrable]
    infer_instance

section lintegral

/--
lemma `setLIntegral_tilted'` / 引理 `setLIntegral_tilted'`

English:
lemma setLIntegral_tilted'
  given: (f : α -> Real) (g : α -> Real>=0∞) {s : Set α} (hs : MeasurableSet s)
  proof: by
  by_cases hf : AEMeasurable f μ
  · rw [Measure.tilted, setLIntegral_withDensity_eq_setLIntegral_mul_non_measurable₀]
    · simp only [Pi.mul_apply]
    · refine AEMeasurable.restrict ?_
      exact ((measurable_exp.comp_aemeasurable hf).div_const _).ennreal_ofReal
    · exact hs
    · filter_upwards
      simp only [ENNReal.ofReal_lt_top, implies_true]
  · have hf' : ¬ Integrable (fun x => exp (f x)) μ := by
      exact fun h => hf (aemeasurable_of_aemeasurable_exp h.1.aemeasurable)
    simp only [hf, not_false_eq_true, tilted_of_not_aemeasurable, Measure.restrict_zero,
      lintegral_zero_measure]
    rw [integral_undef hf']
    simp

中文:
引理 setL整数egral_tilted'
  条件: (f : α -> 实数) (g : α -> 实数>=0∞) {s : 集合 α} (hs : 可测集 s)
  证明: by
  by_cases hf : AEMeasurable f μ
  · rw [Measure.tilted, setLIntegral_withDensity_eq_setLIntegral_mul_non_measurable₀]
    · simp only [Pi.mul_apply]
    · refine AEMeasurable.restrict ?_
      exact ((measurable_exp.comp_aemeasurable hf).div_const _).ennreal_ofReal
    · exact hs
    · filter_upwards
      simp only [ENNReal.ofReal_lt_top, implies_true]
  · have hf' : ¬ Integrable (fun x => exp (f x)) μ := by
      exact fun h => hf (aemeasurable_of_aemeasurable_exp h.1.aemeasurable)
    simp only [hf, not_false_eq_true, tilted_of_not_aemeasurable, Measure.restrict_zero,
      lintegral_zero_measure]
    rw [integral_undef hf']
    simp

Depends on / 依赖: AEMeasurable, AEMeasurable.restrict, ENNReal, ENNReal.ofReal_lt_top, Integrable, Measure, Measure.tilted, Pi.mul_apply, aemeasurable, aemeasurable_of_aemeasurable_exp, comp_aemeasurable, div_const, ennreal_ofReal, filter_upwards, implies_true, measurable_exp, measurable_exp.comp_aemeasurable, mul_apply, not_false_eq_true, ofReal_lt_top
-/
lemma setLIntegral_tilted' (f : α -> Real) (g : α -> Real>=0∞) {s : Set α} (hs : MeasurableSet s) :
    ∫⁻ x in s, g x ∂(μ.tilted f)
      = ∫⁻ x in s, ENNReal.ofReal (exp (f x) / ∫ x, exp (f x) ∂μ) * g x ∂μ := by
  by_cases hf : AEMeasurable f μ
  · rw [Measure.tilted, setLIntegral_withDensity_eq_setLIntegral_mul_non_measurable₀]
    · simp only [Pi.mul_apply]
    · refine AEMeasurable.restrict ?_
      exact ((measurable_exp.comp_aemeasurable hf).div_const _).ennreal_ofReal
    · exact hs
    · filter_upwards
      simp only [ENNReal.ofReal_lt_top, implies_true]
  · have hf' : ¬ Integrable (fun x => exp (f x)) μ := by
      exact fun h => hf (aemeasurable_of_aemeasurable_exp h.1.aemeasurable)
    simp only [hf, not_false_eq_true, tilted_of_not_aemeasurable, Measure.restrict_zero,
      lintegral_zero_measure]
    rw [integral_undef hf']
    simp

/--
lemma `setLIntegral_tilted` / 引理 `setLIntegral_tilted`

English:
lemma setLIntegral_tilted
  given: [SFinite μ] (f : α -> Real) (g : α -> Real>=0∞) (s : Set α)
  proof: by
  by_cases hf : AEMeasurable f μ
  · rw [Measure.tilted, setLIntegral_withDensity_eq_setLIntegral_mul_non_measurable₀']
    · simp only [Pi.mul_apply]
    · refine AEMeasurable.restrict ?_
      exact ((measurable_exp.comp_aemeasurable hf).div_const _).ennreal_ofReal
    · filter_upwards
      simp only [ENNReal.ofReal_lt_top, implies_true]
  · have hf' : ¬ Integrable (fun x => exp (f x)) μ := by
      exact fun h => hf (aemeasurable_of_aemeasurable_exp h.1.aemeasurable)
    simp only [hf, not_false_eq_true, tilted_of_not_aemeasurable, Measure.restrict_zero,
      lintegral_zero_measure]
    rw [integral_undef hf']
    simp

中文:
引理 setL整数egral_tilted
  条件: [SFinite μ] (f : α -> 实数) (g : α -> 实数>=0∞) (s : 集合 α)
  证明: by
  by_cases hf : AEMeasurable f μ
  · rw [Measure.tilted, setLIntegral_withDensity_eq_setLIntegral_mul_non_measurable₀']
    · simp only [Pi.mul_apply]
    · refine AEMeasurable.restrict ?_
      exact ((measurable_exp.comp_aemeasurable hf).div_const _).ennreal_ofReal
    · filter_upwards
      simp only [ENNReal.ofReal_lt_top, implies_true]
  · have hf' : ¬ Integrable (fun x => exp (f x)) μ := by
      exact fun h => hf (aemeasurable_of_aemeasurable_exp h.1.aemeasurable)
    simp only [hf, not_false_eq_true, tilted_of_not_aemeasurable, Measure.restrict_zero,
      lintegral_zero_measure]
    rw [integral_undef hf']
    simp

Depends on / 依赖: AEMeasurable, AEMeasurable.restrict, ENNReal, ENNReal.ofReal_lt_top, Integrable, Measure, Measure.tilted, Pi.mul_apply, aemeasurable, aemeasurable_of_aemeasurable_exp, comp_aemeasurable, div_const, ennreal_ofReal, filter_upwards, implies_true, measurable_exp, measurable_exp.comp_aemeasurable, mul_apply, not_false_eq_true, ofReal_lt_top
-/
lemma setLIntegral_tilted [SFinite μ] (f : α -> Real) (g : α -> Real>=0∞) (s : Set α) :
    ∫⁻ x in s, g x ∂(μ.tilted f)
      = ∫⁻ x in s, ENNReal.ofReal (exp (f x) / ∫ x, exp (f x) ∂μ) * g x ∂μ := by
  by_cases hf : AEMeasurable f μ
  · rw [Measure.tilted, setLIntegral_withDensity_eq_setLIntegral_mul_non_measurable₀']
    · simp only [Pi.mul_apply]
    · refine AEMeasurable.restrict ?_
      exact ((measurable_exp.comp_aemeasurable hf).div_const _).ennreal_ofReal
    · filter_upwards
      simp only [ENNReal.ofReal_lt_top, implies_true]
  · have hf' : ¬ Integrable (fun x => exp (f x)) μ := by
      exact fun h => hf (aemeasurable_of_aemeasurable_exp h.1.aemeasurable)
    simp only [hf, not_false_eq_true, tilted_of_not_aemeasurable, Measure.restrict_zero,
      lintegral_zero_measure]
    rw [integral_undef hf']
    simp

/--
lemma `lintegral_tilted` / 引理 `lintegral_tilted`

English:
lemma lintegral_tilted
  given: (f : α -> Real) (g : α -> Real>=0∞)
  proof: by
  rw [← setLIntegral_univ]; rw [setLIntegral_tilted' f g MeasurableSet.univ]; rw [setLIntegral_univ]

中文:
引理 lintegral_tilted
  条件: (f : α -> 实数) (g : α -> 实数>=0∞)
  证明: by
  rw [← setLIntegral_univ]; rw [setLIntegral_tilted' f g MeasurableSet.univ]; rw [setLIntegral_univ]

Depends on / 依赖: MeasurableSet, MeasurableSet.univ, setLIntegral_tilted, setLIntegral_univ
-/
lemma lintegral_tilted (f : α -> Real) (g : α -> Real>=0∞) :
    ∫⁻ x, g x ∂(μ.tilted f)
      = ∫⁻ x, ENNReal.ofReal (exp (f x) / ∫ x, exp (f x) ∂μ) * (g x) ∂μ := by
  rw [← setLIntegral_univ]; rw [setLIntegral_tilted' f g MeasurableSet.univ]; rw [setLIntegral_univ]

end lintegral

section integral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]

/--
lemma `setIntegral_tilted'` / 引理 `setIntegral_tilted'`

English:
lemma setIntegral_tilted'
  given: (f : α -> Real) (g : α -> E) {s : Set α} (hs : MeasurableSet s)
  proof: by
  by_cases hf : AEMeasurable f μ
  · rw [tilted_eq_withDensity_nnreal, setIntegral_withDensity_eq_setIntegral_smul₀ _ _ hs]
    · congr
    · suffices AEMeasurable (fun x => exp (f x) / ∫ x, exp (f x) ∂μ) μ by
        rw [← aemeasurable_coe_nnreal_real_iff]
        refine AEMeasurable.restrict ?_
        simpa only [NNReal.coe_mk]
      exact (measurable_exp.comp_aemeasurable hf).div_const _
  · have hf' : ¬ Integrable (fun x => exp (f x)) μ := by
      exact fun h => hf (aemeasurable_of_aemeasurable_exp h.1.aemeasurable)
    simp only [hf, not_false_eq_true, tilted_of_not_aemeasurable, Measure.restrict_zero,
      integral_zero_measure]
    rw [integral_undef hf']
    simp

中文:
引理 set整数egral_tilted'
  条件: (f : α -> 实数) (g : α -> E) {s : 集合 α} (hs : 可测集 s)
  证明: by
  by_cases hf : AEMeasurable f μ
  · rw [tilted_eq_withDensity_nnreal, setIntegral_withDensity_eq_setIntegral_smul₀ _ _ hs]
    · congr
    · suffices AEMeasurable (fun x => exp (f x) / ∫ x, exp (f x) ∂μ) μ by
        rw [← aemeasurable_coe_nnreal_real_iff]
        refine AEMeasurable.restrict ?_
        simpa only [NNReal.coe_mk]
      exact (measurable_exp.comp_aemeasurable hf).div_const _
  · have hf' : ¬ Integrable (fun x => exp (f x)) μ := by
      exact fun h => hf (aemeasurable_of_aemeasurable_exp h.1.aemeasurable)
    simp only [hf, not_false_eq_true, tilted_of_not_aemeasurable, Measure.restrict_zero,
      integral_zero_measure]
    rw [integral_undef hf']
    simp

Depends on / 依赖: AEMeasurable, AEMeasurable.restrict, Integrable, NNReal, NNReal.coe_mk, aemeasurable, aemeasurable_coe_nnreal_real_iff, aemeasurable_of_aemeasurable_exp, coe_mk, comp_aemeasurable, div_const, measurable_exp, measurable_exp.comp_aemeasurable, not_, restrict, tilted_eq_withDensity_nnreal
-/
lemma setIntegral_tilted' (f : α -> Real) (g : α -> E) {s : Set α} (hs : MeasurableSet s) :
    ∫ x in s, g x ∂(μ.tilted f) = ∫ x in s, (exp (f x) / ∫ x, exp (f x) ∂μ) • (g x) ∂μ := by
  by_cases hf : AEMeasurable f μ
  · rw [tilted_eq_withDensity_nnreal, setIntegral_withDensity_eq_setIntegral_smul₀ _ _ hs]
    · congr
    · suffices AEMeasurable (fun x => exp (f x) / ∫ x, exp (f x) ∂μ) μ by
        rw [← aemeasurable_coe_nnreal_real_iff]
        refine AEMeasurable.restrict ?_
        simpa only [NNReal.coe_mk]
      exact (measurable_exp.comp_aemeasurable hf).div_const _
  · have hf' : ¬ Integrable (fun x => exp (f x)) μ := by
      exact fun h => hf (aemeasurable_of_aemeasurable_exp h.1.aemeasurable)
    simp only [hf, not_false_eq_true, tilted_of_not_aemeasurable, Measure.restrict_zero,
      integral_zero_measure]
    rw [integral_undef hf']
    simp

/--
lemma `setIntegral_tilted` / 引理 `setIntegral_tilted`

English:
lemma setIntegral_tilted
  given: [SFinite μ] (f : α -> Real) (g : α -> E) (s : Set α)
  proof: by
  by_cases hf : AEMeasurable f μ
  · rw [tilted_eq_withDensity_nnreal, setIntegral_withDensity_eq_setIntegral_smul₀']
    · congr
    · suffices AEMeasurable (fun x => exp (f x) / ∫ x, exp (f x) ∂μ) μ by
        rw [← aemeasurable_coe_nnreal_real_iff]
        refine AEMeasurable.restrict ?_
        simpa only [NNReal.coe_mk]
      exact (measurable_exp.comp_aemeasurable hf).div_const _
  · have hf' : ¬ Integrable (fun x => exp (f x)) μ := by
      exact fun h => hf (aemeasurable_of_aemeasurable_exp h.1.aemeasurable)
    simp only [hf, not_false_eq_true, tilted_of_not_aemeasurable, Measure.restrict_zero,
      integral_zero_measure]
    rw [integral_undef hf']
    simp

中文:
引理 set整数egral_tilted
  条件: [SFinite μ] (f : α -> 实数) (g : α -> E) (s : 集合 α)
  证明: by
  by_cases hf : AEMeasurable f μ
  · rw [tilted_eq_withDensity_nnreal, setIntegral_withDensity_eq_setIntegral_smul₀']
    · congr
    · suffices AEMeasurable (fun x => exp (f x) / ∫ x, exp (f x) ∂μ) μ by
        rw [← aemeasurable_coe_nnreal_real_iff]
        refine AEMeasurable.restrict ?_
        simpa only [NNReal.coe_mk]
      exact (measurable_exp.comp_aemeasurable hf).div_const _
  · have hf' : ¬ Integrable (fun x => exp (f x)) μ := by
      exact fun h => hf (aemeasurable_of_aemeasurable_exp h.1.aemeasurable)
    simp only [hf, not_false_eq_true, tilted_of_not_aemeasurable, Measure.restrict_zero,
      integral_zero_measure]
    rw [integral_undef hf']
    simp

Depends on / 依赖: AEMeasurable, AEMeasurable.restrict, Integrable, NNReal, NNReal.coe_mk, aemeasurable, aemeasurable_coe_nnreal_real_iff, aemeasurable_of_aemeasurable_exp, coe_mk, comp_aemeasurable, div_const, measurable_exp, measurable_exp.comp_aemeasurable, not_false_, restrict, tilted_eq_withDensity_nnreal
-/
lemma setIntegral_tilted [SFinite μ] (f : α -> Real) (g : α -> E) (s : Set α) :
    ∫ x in s, g x ∂(μ.tilted f) = ∫ x in s, (exp (f x) / ∫ x, exp (f x) ∂μ) • (g x) ∂μ := by
  by_cases hf : AEMeasurable f μ
  · rw [tilted_eq_withDensity_nnreal, setIntegral_withDensity_eq_setIntegral_smul₀']
    · congr
    · suffices AEMeasurable (fun x => exp (f x) / ∫ x, exp (f x) ∂μ) μ by
        rw [← aemeasurable_coe_nnreal_real_iff]
        refine AEMeasurable.restrict ?_
        simpa only [NNReal.coe_mk]
      exact (measurable_exp.comp_aemeasurable hf).div_const _
  · have hf' : ¬ Integrable (fun x => exp (f x)) μ := by
      exact fun h => hf (aemeasurable_of_aemeasurable_exp h.1.aemeasurable)
    simp only [hf, not_false_eq_true, tilted_of_not_aemeasurable, Measure.restrict_zero,
      integral_zero_measure]
    rw [integral_undef hf']
    simp

/--
lemma `integral_tilted` / 引理 `integral_tilted`

English:
lemma integral_tilted
  given: (f : α -> Real) (g : α -> E)
  proof: by
  rw [← setIntegral_univ]; rw [setIntegral_tilted' f g MeasurableSet.univ]; rw [setIntegral_univ]

中文:
引理 integral_tilted
  条件: (f : α -> 实数) (g : α -> E)
  证明: by
  rw [← setIntegral_univ]; rw [setIntegral_tilted' f g MeasurableSet.univ]; rw [setIntegral_univ]

Depends on / 依赖: MeasurableSet, MeasurableSet.univ, setIntegral_tilted, setIntegral_univ
-/
lemma integral_tilted (f : α -> Real) (g : α -> E) :
    ∫ x, g x ∂(μ.tilted f) = ∫ x, (exp (f x) / ∫ x, exp (f x) ∂μ) • (g x) ∂μ := by
  rw [← setIntegral_univ]; rw [setIntegral_tilted' f g MeasurableSet.univ]; rw [setIntegral_univ]

end integral

/--
lemma `integral_exp_tilted` / 引理 `integral_exp_tilted`

English:
lemma integral_exp_tilted
  given: (f g : α -> Real)
  proof: by
  cases eq_zero_or_neZero μ with
  | inl h => rw [h]; simp
  | inr h0 =>
    rw [integral_tilted f]
    simp_rw [smul_eq_mul]
    have : forall x, (exp (f x) / ∫ x, exp (f x) ∂μ) * exp (g x)
        = (exp ((f + g) x) / ∫ x, exp (f x) ∂μ) := by
      intro x
      rw [Pi.add_apply]; rw [exp_add]
      ring
    simp_rw [this, div_eq_mul_inv]
    rw [integral_mul_const]

中文:
引理 integral_exp_tilted
  条件: (f g : α -> 实数)
  证明: by
  cases eq_zero_or_neZero μ with
  | inl h => rw [h]; simp
  | inr h0 =>
    rw [integral_tilted f]
    simp_rw [smul_eq_mul]
    have : forall x, (exp (f x) / ∫ x, exp (f x) ∂μ) * exp (g x)
        = (exp ((f + g) x) / ∫ x, exp (f x) ∂μ) := by
      intro x
      rw [Pi.add_apply]; rw [exp_add]
      ring
    simp_rw [this, div_eq_mul_inv]
    rw [integral_mul_const]

Depends on / 依赖: Pi.add_apply, add_apply, div_eq_mul_inv, eq_zero_or_neZero, exp_add, integral_mul_const, integral_tilted, simp_rw, smul_eq_mul
-/
lemma integral_exp_tilted (f g : α -> Real) :
    ∫ x, exp (g x) ∂(μ.tilted f) = (∫ x, exp ((f + g) x) ∂μ) / ∫ x, exp (f x) ∂μ := by
  cases eq_zero_or_neZero μ with
  | inl h => rw [h]; simp
  | inr h0 =>
    rw [integral_tilted f]
    simp_rw [smul_eq_mul]
    have : forall x, (exp (f x) / ∫ x, exp (f x) ∂μ) * exp (g x)
        = (exp ((f + g) x) / ∫ x, exp (f x) ∂μ) := by
      intro x
      rw [Pi.add_apply]; rw [exp_add]
      ring
    simp_rw [this, div_eq_mul_inv]
    rw [integral_mul_const]

/--
lemma `tilted_tilted` / 引理 `tilted_tilted`

English:
lemma tilted_tilted
  given: (hf : Integrable (fun x => exp (f x)) μ) (g : α -> Real)
  proof: by
  cases eq_zero_or_neZero μ with
  | inl h => simp [h]
  | inr h0 =>
    ext1 s hs
    rw [tilted_apply' _ _ hs]; rw [tilted_apply' _ _ hs]; rw [setLIntegral_tilted' f _ hs]
    congr with x
    rw [← ENNReal.ofReal_mul (by positivity)]; rw [integral_exp_tilted f]; rw [Pi.add_apply]; rw [exp_add]
    congr 1
    simp only [Pi.add_apply]
    have := (integral_exp_pos hf).ne'
    simp [field]

中文:
引理 tilted_tilted
  条件: (hf : 可积 (fun x => exp (f x)) μ) (g : α -> 实数)
  证明: by
  cases eq_zero_or_neZero μ with
  | inl h => simp [h]
  | inr h0 =>
    ext1 s hs
    rw [tilted_apply' _ _ hs]; rw [tilted_apply' _ _ hs]; rw [setLIntegral_tilted' f _ hs]
    congr with x
    rw [← ENNReal.ofReal_mul (by positivity)]; rw [integral_exp_tilted f]; rw [Pi.add_apply]; rw [exp_add]
    congr 1
    simp only [Pi.add_apply]
    have := (integral_exp_pos hf).ne'
    simp [field]

Depends on / 依赖: ENNReal, ENNReal.ofReal_mul, Pi.add_apply, add_apply, eq_zero_or_neZero, exp_add, integral_exp_pos, integral_exp_tilted, ofReal_mul, setLIntegral_tilted, tilted_apply
-/
lemma tilted_tilted (hf : Integrable (fun x => exp (f x)) μ) (g : α -> Real) :
    (μ.tilted f).tilted g = μ.tilted (f + g) := by
  cases eq_zero_or_neZero μ with
  | inl h => simp [h]
  | inr h0 =>
    ext1 s hs
    rw [tilted_apply' _ _ hs]; rw [tilted_apply' _ _ hs]; rw [setLIntegral_tilted' f _ hs]
    congr with x
    rw [← ENNReal.ofReal_mul (by positivity)]; rw [integral_exp_tilted f]; rw [Pi.add_apply]; rw [exp_add]
    congr 1
    simp only [Pi.add_apply]
    have := (integral_exp_pos hf).ne'
    simp [field]

/--
lemma `tilted_comm` / 引理 `tilted_comm`

English:
lemma tilted_comm
  statement: (hf : Integrable (fun x => exp (f x)) μ) {g : α -> Real}
  proof: by
  rw [tilted_tilted hf]; rw [add_comm]; rw [tilted_tilted hg]

@[simp]

中文:
引理 tilted_comm
  结论: (hf : 可积 (fun x => exp (f x)) μ) {g : α -> 实数}
  证明: by
  rw [tilted_tilted hf]; rw [add_comm]; rw [tilted_tilted hg]

@[simp]

Depends on / 依赖: add_comm, tilted_tilted
-/
lemma tilted_comm (hf : Integrable (fun x => exp (f x)) μ) {g : α -> Real}
    (hg : Integrable (fun x => exp (g x)) μ) :
    (μ.tilted f).tilted g = (μ.tilted g).tilted f := by
  rw [tilted_tilted hf]; rw [add_comm]; rw [tilted_tilted hg]

@[simp]
/--
lemma `tilted_neg_same'` / 引理 `tilted_neg_same'`

English:
lemma tilted_neg_same'
  given: (hf : Integrable (fun x => exp (f x)) μ)
  proof: by
  rw [tilted_tilted hf]; simp

中文:
引理 tilted_neg_same'
  条件: (hf : 可积 (fun x => exp (f x)) μ)
  证明: by
  rw [tilted_tilted hf]; simp

Depends on / 依赖: tilted_tilted
-/
lemma tilted_neg_same' (hf : Integrable (fun x => exp (f x)) μ) :
    (μ.tilted f).tilted (-f) = (μ Set.univ)⁻¹ • μ := by
  rw [tilted_tilted hf]; simp

/--
lemma `tilted_neg_same` / 引理 `tilted_neg_same`

English:
lemma tilted_neg_same
  given: [IsProbabilityMeasure μ] (hf : Integrable (fun x => exp (f x)) μ)
  proof: by
  simp [hf]

中文:
引理 tilted_neg_same
  条件: [是概率测度 μ] (hf : 可积 (fun x => exp (f x)) μ)
  证明: by
  simp [hf]

Depends on / 依赖: ConcreteCategory, ConcreteCategory.hom, PartOrdEmb
-/
lemma tilted_neg_same [IsProbabilityMeasure μ] (hf : Integrable (fun x => exp (f x)) μ) :
    (μ.tilted f).tilted (-f) = μ := by
  simp [hf]

/--
lemma `tilted_absolutelyContinuous` / 引理 `tilted_absolutelyContinuous`

English:
lemma tilted_absolutelyContinuous
  given: (μ : Measure α) (f : α -> Real)
  statement: μ.tilted f ≪ μ
  proof: withDensity_absolutelyContinuous _ _

中文:
引理 tilted_absolutelyContinuous
  条件: (μ : 测度 α) (f : α -> 实数)
  结论: μ.tilted f ≪ μ
  证明: withDensity_absolutelyContinuous _ _

Depends on / 依赖: withDensity_absolutelyContinuous
-/
lemma tilted_absolutelyContinuous (μ : Measure α) (f : α -> Real) : μ.tilted f ≪ μ :=
  withDensity_absolutelyContinuous _ _

/--
lemma `absolutelyContinuous_tilted` / 引理 `absolutelyContinuous_tilted`

English:
lemma absolutelyContinuous_tilted
  given: (hf : Integrable (fun x => exp (f x)) μ)
  statement: μ ≪ μ.tilted f
  proof: by
  cases eq_zero_or_neZero μ with
  | inl h => simp only [h, tilted_zero_measure]; exact fun _ _ => by simp
  | inr h0 =>
    refine withDensity_absolutelyContinuous' ?_ ?_
    · exact (hf.1.aemeasurable.div_const _).ennreal_ofReal
    · filter_upwards
      simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
      exact fun _ => div_pos (exp_pos _) (integral_exp_pos hf)

中文:
引理 absolutelyContinuous_tilted
  条件: (hf : 可积 (fun x => exp (f x)) μ)
  结论: μ ≪ μ.tilted f
  证明: by
  cases eq_zero_or_neZero μ with
  | inl h => simp only [h, tilted_zero_measure]; exact fun _ _ => by simp
  | inr h0 =>
    refine withDensity_absolutelyContinuous' ?_ ?_
    · exact (hf.1.aemeasurable.div_const _).ennreal_ofReal
    · filter_upwards
      simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
      exact fun _ => div_pos (exp_pos _) (integral_exp_pos hf)

Depends on / 依赖: ENNReal, ENNReal.ofReal_eq_zero, aemeasurable, aemeasurable.div_const, div_const, div_pos, ennreal_ofReal, eq_zero_or_neZero, exp_pos, f.hom, filter_upwards, integral_exp_pos, ne_eq, not_le, ofReal_eq_zero, tilted_zero_measure, withDensity_absolutelyContinuous
-/
lemma absolutelyContinuous_tilted (hf : Integrable (fun x => exp (f x)) μ) : μ ≪ μ.tilted f := by
  cases eq_zero_or_neZero μ with
  | inl h => simp only [h, tilted_zero_measure]; exact fun _ _ => by simp
  | inr h0 =>
    refine withDensity_absolutelyContinuous' ?_ ?_
    · exact (hf.1.aemeasurable.div_const _).ennreal_ofReal
    · filter_upwards
      simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
      exact fun _ => div_pos (exp_pos _) (integral_exp_pos hf)

/--
lemma `integrable_tilted_iff` / 引理 `integrable_tilted_iff`

English:
lemma integrable_tilted_iff
  statement: {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  proof: by
  by_cases hμ : μ = 0
  · simp [hμ]
  have hf_meas : AEMeasurable f μ := aemeasurable_of_aemeasurable_exp hf.1.aemeasurable
  rw [Measure.tilted]; rw [integrable_withDensity_iff_integrable_smul₀' (by fun_prop) (by simp)]
  calc Integrable (fun x => (ENNReal.ofReal (exp (f x) / ∫ a, exp (f a) ∂μ)).toReal • g x) μ
  _ ↔ Integrable (fun x => (exp (f x) / ∫ a, exp (f a) ∂μ) • g x) μ := by
    congr! with a
    rw [ENNReal.toReal_ofReal]
    positivity
  _ ↔ Integrable (fun x => (∫ a, exp (f a) ∂μ)⁻¹ • exp (f x) • g x) μ := by
    congr! 2 with a
    rw [smul_smul]; rw [div_eq_inv_mul]
  _ ↔ Integrable (fun x => exp (f x) • g x) μ := by
    rw [integrable_fun_smul_iff]
    simp only [ne_eq, inv_eq_zero]
    have : NeZero μ := ⟨hμ⟩
    exact (integral_exp_pos hf).ne'

中文:
引理 integrable_tilted_iff
  结论: {E : 类型} [赋范交换加群 E] [赋范空间 实数 E]
  证明: by
  by_cases hμ : μ = 0
  · simp [hμ]
  have hf_meas : AEMeasurable f μ := aemeasurable_of_aemeasurable_exp hf.1.aemeasurable
  rw [Measure.tilted]; rw [integrable_withDensity_iff_integrable_smul₀' (by fun_prop) (by simp)]
  calc Integrable (fun x => (ENNReal.ofReal (exp (f x) / ∫ a, exp (f a) ∂μ)).toReal • g x) μ
  _ ↔ Integrable (fun x => (exp (f x) / ∫ a, exp (f a) ∂μ) • g x) μ := by
    congr! with a
    rw [ENNReal.toReal_ofReal]
    positivity
  _ ↔ Integrable (fun x => (∫ a, exp (f a) ∂μ)⁻¹ • exp (f x) • g x) μ := by
    congr! 2 with a
    rw [smul_smul]; rw [div_eq_inv_mul]
  _ ↔ Integrable (fun x => exp (f x) • g x) μ := by
    rw [integrable_fun_smul_iff]
    simp only [ne_eq, inv_eq_zero]
    have : NeZero μ := ⟨hμ⟩
    exact (integral_exp_pos hf).ne'

Depends on / 依赖: AEMeasurable, ENNReal, ENNReal.ofReal, ENNReal.toReal_ofReal, Integrable, Measure, Measure.tilted, aemeasurable, aemeasurable_of_aemeasurable_exp, fun_prop, hf_meas, ofReal, tilted, toReal, toReal_ofReal
-/
lemma integrable_tilted_iff {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    {f : α -> Real} (hf : Integrable (fun x => exp (f x)) μ) (g : α -> E) :
    Integrable g (μ.tilted f) ↔ Integrable (fun x => exp (f x) • g x) μ := by
  by_cases hμ : μ = 0
  · simp [hμ]
  have hf_meas : AEMeasurable f μ := aemeasurable_of_aemeasurable_exp hf.1.aemeasurable
  rw [Measure.tilted]; rw [integrable_withDensity_iff_integrable_smul₀' (by fun_prop) (by simp)]
  calc Integrable (fun x => (ENNReal.ofReal (exp (f x) / ∫ a, exp (f a) ∂μ)).toReal • g x) μ
  _ ↔ Integrable (fun x => (exp (f x) / ∫ a, exp (f a) ∂μ) • g x) μ := by
    congr! with a
    rw [ENNReal.toReal_ofReal]
    positivity
  _ ↔ Integrable (fun x => (∫ a, exp (f a) ∂μ)⁻¹ • exp (f x) • g x) μ := by
    congr! 2 with a
    rw [smul_smul]; rw [div_eq_inv_mul]
  _ ↔ Integrable (fun x => exp (f x) • g x) μ := by
    rw [integrable_fun_smul_iff]
    simp only [ne_eq, inv_eq_zero]
    have : NeZero μ := ⟨hμ⟩
    exact (integral_exp_pos hf).ne'

/--
lemma `rnDeriv_tilted_right` / 引理 `rnDeriv_tilted_right`

English:
lemma rnDeriv_tilted_right
  statement: (μ ν : Measure α) [SigmaFinite μ] [SigmaFinite ν]
  proof: by
  cases eq_zero_or_neZero ν with
  | inl h => simp_rw [h, ae_zero, Filter.EventuallyEq]; exact Filter.eventually_bot
  | inr h0 =>
    refine (Measure.rnDeriv_withDensity_right μ ν ?_ ?_ ?_).trans ?_
    · exact (hf.1.aemeasurable.div_const _).ennreal_ofReal
    · filter_upwards
      simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
      exact fun _ => div_pos (exp_pos _) (integral_exp_pos hf)
    · refine ae_of_all _ (by simp)
    · filter_upwards with x
      congr
      rw [← ENNReal.ofReal_inv_of_pos]; rw [inv_div']; rw [← exp_neg]; rw [div_eq_mul_inv]; rw [inv_inv]
      exact div_pos (exp_pos _) (integral_exp_pos hf)

中文:
引理 rnDeriv_tilted_right
  结论: (μ ν : 测度 α) [σ有限 μ] [σ有限 ν]
  证明: by
  cases eq_zero_or_neZero ν with
  | inl h => simp_rw [h, ae_zero, Filter.EventuallyEq]; exact Filter.eventually_bot
  | inr h0 =>
    refine (Measure.rnDeriv_withDensity_right μ ν ?_ ?_ ?_).trans ?_
    · exact (hf.1.aemeasurable.div_const _).ennreal_ofReal
    · filter_upwards
      simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
      exact fun _ => div_pos (exp_pos _) (integral_exp_pos hf)
    · refine ae_of_all _ (by simp)
    · filter_upwards with x
      congr
      rw [← ENNReal.ofReal_inv_of_pos]; rw [inv_div']; rw [← exp_neg]; rw [div_eq_mul_inv]; rw [inv_inv]
      exact div_pos (exp_pos _) (integral_exp_pos hf)

Depends on / 依赖: ENNReal, ENNReal.ofReal_eq_zero, ENNReal.ofReal_inv_of_pos, EventuallyEq, Filter, Filter.EventuallyEq, Filter.eventually_bot, Measure, Measure.rnDeriv_withDensity_right, ae_of_all, ae_zero, aemeasurable, aemeasurable.div_const, div_const, div_pos, ennreal_ofReal, eq_zero_or_neZero, eventually_bot, exp_neg, exp_pos
-/
lemma rnDeriv_tilted_right (μ ν : Measure α) [SigmaFinite μ] [SigmaFinite ν]
    (hf : Integrable (fun x => exp (f x)) ν) :
    μ.rnDeriv (ν.tilted f)
      =ᵐ[ν] fun x => ENNReal.ofReal (exp (-f x) * ∫ x, exp (f x) ∂ν) * μ.rnDeriv ν x := by
  cases eq_zero_or_neZero ν with
  | inl h => simp_rw [h, ae_zero, Filter.EventuallyEq]; exact Filter.eventually_bot
  | inr h0 =>
    refine (Measure.rnDeriv_withDensity_right μ ν ?_ ?_ ?_).trans ?_
    · exact (hf.1.aemeasurable.div_const _).ennreal_ofReal
    · filter_upwards
      simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
      exact fun _ => div_pos (exp_pos _) (integral_exp_pos hf)
    · refine ae_of_all _ (by simp)
    · filter_upwards with x
      congr
      rw [← ENNReal.ofReal_inv_of_pos]; rw [inv_div']; rw [← exp_neg]; rw [div_eq_mul_inv]; rw [inv_inv]
      exact div_pos (exp_pos _) (integral_exp_pos hf)

/--
lemma `toReal_rnDeriv_tilted_right` / 引理 `toReal_rnDeriv_tilted_right`

English:
lemma toReal_rnDeriv_tilted_right
  statement: (μ ν : Measure α) [SigmaFinite μ] [SigmaFinite ν]
  proof: by
  filter_upwards [rnDeriv_tilted_right μ ν hf] with x hx
  rw [hx]
  simp only [ENNReal.toReal_mul, mul_eq_mul_right_iff, ENNReal.toReal_ofReal_eq_iff]
  exact Or.inl (by positivity)

中文:
引理 to实数_rnDeriv_tilted_right
  结论: (μ ν : 测度 α) [σ有限 μ] [σ有限 ν]
  证明: by
  filter_upwards [rnDeriv_tilted_right μ ν hf] with x hx
  rw [hx]
  simp only [ENNReal.toReal_mul, mul_eq_mul_right_iff, ENNReal.toReal_ofReal_eq_iff]
  exact Or.inl (by positivity)

Depends on / 依赖: ENNReal, ENNReal.toReal_mul, ENNReal.toReal_ofReal_eq_iff, Or.inl, filter_upwards, mul_eq_mul_right_iff, rnDeriv_tilted_right, toReal_mul, toReal_ofReal_eq_iff
-/
lemma toReal_rnDeriv_tilted_right (μ ν : Measure α) [SigmaFinite μ] [SigmaFinite ν]
    (hf : Integrable (fun x => exp (f x)) ν) :
    (fun x => (μ.rnDeriv (ν.tilted f) x).toReal)
      =ᵐ[ν] fun x => exp (-f x) * (∫ x, exp (f x) ∂ν) * (μ.rnDeriv ν x).toReal := by
  filter_upwards [rnDeriv_tilted_right μ ν hf] with x hx
  rw [hx]
  simp only [ENNReal.toReal_mul, mul_eq_mul_right_iff, ENNReal.toReal_ofReal_eq_iff]
  exact Or.inl (by positivity)

variable (μ) in
/--
lemma `rnDeriv_tilted_left` / 引理 `rnDeriv_tilted_left`

English:
lemma rnDeriv_tilted_left
  given: {ν : Measure α} [SigmaFinite μ] [SigmaFinite ν] (hfν : AEMeasurable f ν)
  proof: by
  let g := fun x => ENNReal.ofReal (exp (f x) / (∫ x, exp (f x) ∂μ))
  refine Measure.rnDeriv_withDensity_left (μ := μ) (ν := ν) (f := g) ?_ ?_
  · exact ((measurable_exp.comp_aemeasurable hfν).div_const _).ennreal_ofReal
  · exact ae_of_all _ (fun x => by simp [g])

中文:
引理 rnDeriv_tilted_left
  条件: {ν : 测度 α} [σ有限 μ] [σ有限 ν] (hfν : 几乎处处可测 f ν)
  证明: by
  let g := fun x => ENNReal.ofReal (exp (f x) / (∫ x, exp (f x) ∂μ))
  refine Measure.rnDeriv_withDensity_left (μ := μ) (ν := ν) (f := g) ?_ ?_
  · exact ((measurable_exp.comp_aemeasurable hfν).div_const _).ennreal_ofReal
  · exact ae_of_all _ (fun x => by simp [g])

Depends on / 依赖: ENNReal, ENNReal.ofReal, Measure, Measure.rnDeriv_withDensity_left, ae_of_all, comp_aemeasurable, div_const, ennreal_ofReal, measurable_exp, measurable_exp.comp_aemeasurable, ofReal, rnDeriv_withDensity_left
-/
lemma rnDeriv_tilted_left {ν : Measure α} [SigmaFinite μ] [SigmaFinite ν] (hfν : AEMeasurable f ν) :
    (μ.tilted f).rnDeriv ν
      =ᵐ[ν] fun x => ENNReal.ofReal (exp (f x) / (∫ x, exp (f x) ∂μ)) * μ.rnDeriv ν x := by
  let g := fun x => ENNReal.ofReal (exp (f x) / (∫ x, exp (f x) ∂μ))
  refine Measure.rnDeriv_withDensity_left (μ := μ) (ν := ν) (f := g) ?_ ?_
  · exact ((measurable_exp.comp_aemeasurable hfν).div_const _).ennreal_ofReal
  · exact ae_of_all _ (fun x => by simp [g])

variable (μ) in
/--
lemma `toReal_rnDeriv_tilted_left` / 引理 `toReal_rnDeriv_tilted_left`

English:
lemma toReal_rnDeriv_tilted_left
  statement: {ν : Measure α} [SigmaFinite μ] [SigmaFinite ν]
  proof: by
  filter_upwards [rnDeriv_tilted_left μ hfν] with x hx
  rw [hx]
  simp only [ENNReal.toReal_mul, mul_eq_mul_right_iff, ENNReal.toReal_ofReal_eq_iff]
  exact Or.inl (by positivity)

中文:
引理 to实数_rnDeriv_tilted_left
  结论: {ν : 测度 α} [σ有限 μ] [σ有限 ν]
  证明: by
  filter_upwards [rnDeriv_tilted_left μ hfν] with x hx
  rw [hx]
  simp only [ENNReal.toReal_mul, mul_eq_mul_right_iff, ENNReal.toReal_ofReal_eq_iff]
  exact Or.inl (by positivity)

Depends on / 依赖: ENNReal, ENNReal.toReal_mul, ENNReal.toReal_ofReal_eq_iff, Or.inl, filter_upwards, mul_eq_mul_right_iff, rnDeriv_tilted_left, toReal_mul, toReal_ofReal_eq_iff
-/
lemma toReal_rnDeriv_tilted_left {ν : Measure α} [SigmaFinite μ] [SigmaFinite ν]
    (hfν : AEMeasurable f ν) :
    (fun x => ((μ.tilted f).rnDeriv ν x).toReal)
      =ᵐ[ν] fun x => exp (f x) / (∫ x, exp (f x) ∂μ) * (μ.rnDeriv ν x).toReal := by
  filter_upwards [rnDeriv_tilted_left μ hfν] with x hx
  rw [hx]
  simp only [ENNReal.toReal_mul, mul_eq_mul_right_iff, ENNReal.toReal_ofReal_eq_iff]
  exact Or.inl (by positivity)

/--
lemma `rnDeriv_tilted_left_self` / 引理 `rnDeriv_tilted_left_self`

English:
lemma rnDeriv_tilted_left_self
  given: [SigmaFinite μ] (hf : AEMeasurable f μ)
  proof: by
  refine (rnDeriv_tilted_left μ hf).trans ?_
  filter_upwards [Measure.rnDeriv_self μ] with x hx
  rw [hx]; rw [mul_one]

中文:
引理 rnDeriv_tilted_left_self
  条件: [σ有限 μ] (hf : 几乎处处可测 f μ)
  证明: by
  refine (rnDeriv_tilted_left μ hf).trans ?_
  filter_upwards [Measure.rnDeriv_self μ] with x hx
  rw [hx]; rw [mul_one]

Depends on / 依赖: Measure, Measure.rnDeriv_self, filter_upwards, mul_one, rnDeriv_self, rnDeriv_tilted_left
-/
lemma rnDeriv_tilted_left_self [SigmaFinite μ] (hf : AEMeasurable f μ) :
    (μ.tilted f).rnDeriv μ =ᵐ[μ] fun x => ENNReal.ofReal (exp (f x) / ∫ x, exp (f x) ∂μ) := by
  refine (rnDeriv_tilted_left μ hf).trans ?_
  filter_upwards [Measure.rnDeriv_self μ] with x hx
  rw [hx]; rw [mul_one]

/--
lemma `log_rnDeriv_tilted_left_self` / 引理 `log_rnDeriv_tilted_left_self`

English:
lemma log_rnDeriv_tilted_left_self
  given: [SigmaFinite μ] (hf : Integrable (fun x => exp (f x)) μ)
  proof: by
  cases eq_zero_or_neZero μ with
  | inl h => simp_rw [h, ae_zero, Filter.EventuallyEq]; exact Filter.eventually_bot
  | inr h0 =>
    have hf' : AEMeasurable f μ := aemeasurable_of_aemeasurable_exp hf.1.aemeasurable
    filter_upwards [rnDeriv_tilted_left_self hf'] with x hx
    rw [hx]; rw [ENNReal.toReal_ofReal (by positivity)]; rw [log_div (exp_pos _).ne']; rw [log_exp]
    exact (integral_exp_pos hf).ne'

中文:
引理 log_rnDeriv_tilted_left_self
  条件: [σ有限 μ] (hf : 可积 (fun x => exp (f x)) μ)
  证明: by
  cases eq_zero_or_neZero μ with
  | inl h => simp_rw [h, ae_zero, Filter.EventuallyEq]; exact Filter.eventually_bot
  | inr h0 =>
    have hf' : AEMeasurable f μ := aemeasurable_of_aemeasurable_exp hf.1.aemeasurable
    filter_upwards [rnDeriv_tilted_left_self hf'] with x hx
    rw [hx]; rw [ENNReal.toReal_ofReal (by positivity)]; rw [log_div (exp_pos _).ne']; rw [log_exp]
    exact (integral_exp_pos hf).ne'

Depends on / 依赖: AEMeasurable, ENNReal, ENNReal.toReal_ofReal, EventuallyEq, Filter, Filter.EventuallyEq, Filter.eventually_bot, ae_zero, aemeasurable, aemeasurable_of_aemeasurable_exp, eq_zero_or_neZero, eventually_bot, exp_pos, filter_upwards, integral_exp_pos, log_div, log_exp, rnDeriv_tilted_left_self, simp_rw, toReal_ofReal
-/
lemma log_rnDeriv_tilted_left_self [SigmaFinite μ] (hf : Integrable (fun x => exp (f x)) μ) :
    (fun x => log ((μ.tilted f).rnDeriv μ x).toReal)
      =ᵐ[μ] fun x => f x - log (∫ x, exp (f x) ∂μ) := by
  cases eq_zero_or_neZero μ with
  | inl h => simp_rw [h, ae_zero, Filter.EventuallyEq]; exact Filter.eventually_bot
  | inr h0 =>
    have hf' : AEMeasurable f μ := aemeasurable_of_aemeasurable_exp hf.1.aemeasurable
    filter_upwards [rnDeriv_tilted_left_self hf'] with x hx
    rw [hx]; rw [ENNReal.toReal_ofReal (by positivity)]; rw [log_div (exp_pos _).ne']; rw [log_exp]
    exact (integral_exp_pos hf).ne'

end MeasureTheory
