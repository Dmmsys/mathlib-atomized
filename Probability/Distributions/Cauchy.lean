/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis

import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! # Cauchy Distribution over ℝ

Define the Cauchy distribution with location parameter `x₀` and scale parameter `γ`.

Note that we use "location" and "scale" to refer to these parameters in theorem names.

## Main definition

* `cauchyPDFReal`: the function `x₀ γ x ↦ π⁻¹ * γ * ((x - x₀) ^ 2 + γ ^ 2)⁻¹`,
  which is the probability density function of a Cauchy distribution with location parameter `x₀`
  and scale parameter `γ` (when `γ ≠ 0`).
* `cauchyPDF`: `ℝ≥0∞`-valued pdf, `cauchyPDF μ v x = ENNReal.ofReal (cauchyPDFReal μ v x)`.
* `cauchyMeasure`: a Cauchy measure on `ℝ`, parametrized by a location parameter `x₀ : ℝ` and a
  scale parameter `γ : ℝ≥0`. If `γ = 0`, this is `dirac x₀`, otherwise it is defined as the
  measure with density `cauchyPDF x₀ γ` with respect to the Lebesgue measure.

-/

@[expose] public section

open scoped Real ENNReal NNReal

open MeasureTheory Measure

namespace ProbabilityTheory

section CauchyPDF

/--
Definition of `cauchyPDFReal` / `cauchyPDFReal` 的定义

English:
definition cauchyPDFReal
  signature: (x₀ : Real) (γ : Real>=0) (x : Real)
  body: π⁻¹ * γ * ((x - x₀) ^ 2 + γ ^ 2)⁻¹

@[deprecated (since := "2026-03-06")] alias _root_Probability.CauchyPDFReal := cauchyPDFReal

@[simp]

中文:
定义 cauchyPDFReal
  签名: (x₀ : 实数) (γ : 实数>=0) (x : 实数)
  定义体: π⁻¹ * γ * ((x - x₀) ^ 2 + γ ^ 2)⁻¹

@[deprecated (since := "2026-03-06")] alias _root_Probability.CauchyPDFReal := cauchyPDFReal

@[simp]
-/
noncomputable def cauchyPDFReal (x₀ : Real) (γ : Real>=0) (x : Real) : Real :=
  π⁻¹ * γ * ((x - x₀) ^ 2 + γ ^ 2)⁻¹

@[deprecated (since := "2026-03-06")] alias _root_Probability.CauchyPDFReal := cauchyPDFReal

@[simp]
/--
lemma `cauchyPDFReal_scale_zero` / 引理 `cauchyPDFReal_scale_zero`

English:
lemma cauchyPDFReal_scale_zero
  given: (x₀ : Real)
  statement: cauchyPDFReal x₀ 0 = 0
  proof: by
  ext
  simp [cauchyPDFReal]

@[deprecated (since := "2026-03-06")]
alias _root_Probability.CauchyPDFReal_scale_zero := cauchyPDFReal_scale_zero

中文:
引理 cauchyPDFReal_scale_zero
  条件: (x₀ : 实数)
  结论: cauchyPDF实数 x₀ 0 = 0
  证明: by
  ext
  simp [cauchyPDFReal]

@[deprecated (since := "2026-03-06")]
alias _root_Probability.CauchyPDFReal_scale_zero := cauchyPDFReal_scale_zero

Depends on / 依赖: cauchyPDFReal
-/
lemma cauchyPDFReal_scale_zero (x₀ : Real) : cauchyPDFReal x₀ 0 = 0 := by
  ext
  simp [cauchyPDFReal]

@[deprecated (since := "2026-03-06")]
alias _root_Probability.CauchyPDFReal_scale_zero := cauchyPDFReal_scale_zero

/--
lemma `cauchyPDFReal_def` / 引理 `cauchyPDFReal_def`

English:
lemma cauchyPDFReal_def
  given: (x₀ : Real) (γ : Real>=0) (x : Real)
  proof: by rfl

@[deprecated (since := "2026-03-06")]
alias _root_Probability.CauchyPDFReal_def := cauchyPDFReal_def

中文:
引理 cauchyPDFReal_def
  条件: (x₀ : 实数) (γ : 实数>=0) (x : 实数)
  证明: by rfl

@[deprecated (since := "2026-03-06")]
alias _root_Probability.CauchyPDFReal_def := cauchyPDFReal_def
-/
lemma cauchyPDFReal_def (x₀ : Real) (γ : Real>=0) (x : Real) :
    cauchyPDFReal x₀ γ x = π⁻¹ * γ * ((x - x₀) ^ 2 + γ ^ 2)⁻¹ := by rfl

@[deprecated (since := "2026-03-06")]
alias _root_Probability.CauchyPDFReal_def := cauchyPDFReal_def

/--
lemma `cauchyPDFReal_def'` / 引理 `cauchyPDFReal_def'`

English:
lemma cauchyPDFReal_def'
  given: (x₀ : Real) (γ : Real>=0) (x : Real)
  proof: by
  rw [cauchyPDFReal_def]
  by_cases h : γ = 0
  · simp [h]
  simp
  field

@[deprecated (since := "2026-03-06")]
alias _root_Probability.CauchyPDFReal_def' := cauchyPDFReal_def'

中文:
引理 cauchyPDFReal_def'
  条件: (x₀ : 实数) (γ : 实数>=0) (x : 实数)
  证明: by
  rw [cauchyPDFReal_def]
  by_cases h : γ = 0
  · simp [h]
  simp
  field

@[deprecated (since := "2026-03-06")]
alias _root_Probability.CauchyPDFReal_def' := cauchyPDFReal_def'

Depends on / 依赖: cauchyPDFReal_def
-/
lemma cauchyPDFReal_def' (x₀ : Real) (γ : Real>=0) (x : Real) :
    cauchyPDFReal x₀ γ x = π⁻¹ * γ⁻¹ * (1 + ((x - x₀) / γ) ^ 2)⁻¹ := by
  rw [cauchyPDFReal_def]
  by_cases h : γ = 0
  · simp [h]
  simp
  field

@[deprecated (since := "2026-03-06")]
alias _root_Probability.CauchyPDFReal_def' := cauchyPDFReal_def'

/--
Definition of `cauchyPDF` / `cauchyPDF` 的定义

English:
definition cauchyPDF
  signature: (x₀ : Real) (γ : Real>=0) (x : Real)
  body: ENNReal.ofReal (cauchyPDFReal x₀ γ x)

@[deprecated (since := "2026-03-06")]
alias _root_Probability.CauchyPDF := cauchyPDF

@[simp]

中文:
定义 cauchyPDF
  签名: (x₀ : 实数) (γ : 实数>=0) (x : 实数)
  定义体: ENNReal.ofReal (cauchyPDFReal x₀ γ x)

@[deprecated (since := "2026-03-06")]
alias _root_Probability.CauchyPDF := cauchyPDF

@[simp]

Depends on / 依赖: ENNReal, ENNReal.ofReal, cauchyPDFReal, ofReal
-/
noncomputable def cauchyPDF (x₀ : Real) (γ : Real>=0) (x : Real) : Real>=0∞ :=
  ENNReal.ofReal (cauchyPDFReal x₀ γ x)

@[deprecated (since := "2026-03-06")]
alias _root_Probability.CauchyPDF := cauchyPDF

@[simp]
/--
lemma `cauchyPDF_scale_zero` / 引理 `cauchyPDF_scale_zero`

English:
lemma cauchyPDF_scale_zero
  given: (x₀ : Real)
  statement: cauchyPDF x₀ 0 = 0
  proof: by
  ext
  simp [cauchyPDF]

@[deprecated (since := "2026-03-06")]
alias _root_Probability.CauchyPDF_scale_zero := cauchyPDF_scale_zero

中文:
引理 cauchyPDF_scale_zero
  条件: (x₀ : 实数)
  结论: cauchyPDF x₀ 0 = 0
  证明: by
  ext
  simp [cauchyPDF]

@[deprecated (since := "2026-03-06")]
alias _root_Probability.CauchyPDF_scale_zero := cauchyPDF_scale_zero

Depends on / 依赖: cauchyPDF
-/
lemma cauchyPDF_scale_zero (x₀ : Real) : cauchyPDF x₀ 0 = 0 := by
  ext
  simp [cauchyPDF]

@[deprecated (since := "2026-03-06")]
alias _root_Probability.CauchyPDF_scale_zero := cauchyPDF_scale_zero

/--
lemma `cauchyPDF_def` / 引理 `cauchyPDF_def`

English:
lemma cauchyPDF_def
  given: (x₀ : Real) (γ : Real>=0) (x : Real)
  proof: by rfl

@[deprecated (since := "2026-03-06")]
alias _root_Probability.CauchyPDF_def := cauchyPDF_def

@[fun_prop]

中文:
引理 cauchyPDF_def
  条件: (x₀ : 实数) (γ : 实数>=0) (x : 实数)
  证明: by rfl

@[deprecated (since := "2026-03-06")]
alias _root_Probability.CauchyPDF_def := cauchyPDF_def

@[fun_prop]
-/
lemma cauchyPDF_def (x₀ : Real) (γ : Real>=0) (x : Real) :
  cauchyPDF x₀ γ x = ENNReal.ofReal (cauchyPDFReal x₀ γ x) := by rfl

@[deprecated (since := "2026-03-06")]
alias _root_Probability.CauchyPDF_def := cauchyPDF_def

@[fun_prop]
/--
lemma `measurable_cauchyPDFReal` / 引理 `measurable_cauchyPDFReal`

English:
lemma measurable_cauchyPDFReal
  given: (x₀ : Real) (γ : Real>=0)
  statement: Measurable (cauchyPDFReal x₀ γ)
  proof: by
  unfold cauchyPDFReal
  fun_prop

@[deprecated (since := "2026-03-06")]
alias _root_Probability.measurable_cauchyPDFReal := measurable_cauchyPDFReal

@[fun_prop]

中文:
引理 measurable_cauchyPDFReal
  条件: (x₀ : 实数) (γ : 实数>=0)
  结论: Measurable (cauchyPDF实数 x₀ γ)
  证明: by
  unfold cauchyPDFReal
  fun_prop

@[deprecated (since := "2026-03-06")]
alias _root_Probability.measurable_cauchyPDFReal := measurable_cauchyPDFReal

@[fun_prop]

Depends on / 依赖: cauchyPDFReal, fun_prop
-/
lemma measurable_cauchyPDFReal (x₀ : Real) (γ : Real>=0) : Measurable (cauchyPDFReal x₀ γ) := by
  unfold cauchyPDFReal
  fun_prop

@[deprecated (since := "2026-03-06")]
alias _root_Probability.measurable_cauchyPDFReal := measurable_cauchyPDFReal

@[fun_prop]
/--
lemma `stronglyMeasurable_cauchyPDFReal` / 引理 `stronglyMeasurable_cauchyPDFReal`

English:
lemma stronglyMeasurable_cauchyPDFReal
  given: (x₀ : Real) (γ : Real>=0)
  proof: by fun_prop

@[deprecated (since := "2026-03-06")]
alias _root_Probability.stronglyMeasurable_cauchyPDFReal := stronglyMeasurable_cauchyPDFReal

@[fun_prop]

中文:
引理 stronglyMeasurable_cauchyPDFReal
  条件: (x₀ : 实数) (γ : 实数>=0)
  证明: by fun_prop

@[deprecated (since := "2026-03-06")]
alias _root_Probability.stronglyMeasurable_cauchyPDFReal := stronglyMeasurable_cauchyPDFReal

@[fun_prop]

Depends on / 依赖: fun_prop
-/
lemma stronglyMeasurable_cauchyPDFReal (x₀ : Real) (γ : Real>=0) :
    StronglyMeasurable (cauchyPDFReal x₀ γ) := by fun_prop

@[deprecated (since := "2026-03-06")]
alias _root_Probability.stronglyMeasurable_cauchyPDFReal := stronglyMeasurable_cauchyPDFReal

@[fun_prop]
/--
lemma `measurable_cauchyPDF` / 引理 `measurable_cauchyPDF`

English:
lemma measurable_cauchyPDF
  given: (x₀ : Real) (γ : Real>=0)
  statement: Measurable (cauchyPDF x₀ γ)
  proof: by
  unfold cauchyPDF
  fun_prop

@[deprecated (since := "2026-03-06")]
alias _root_Probability.measurable_cauchyPDF := measurable_cauchyPDF

@[fun_prop]

中文:
引理 measurable_cauchyPDF
  条件: (x₀ : 实数) (γ : 实数>=0)
  结论: Measurable (cauchyPDF x₀ γ)
  证明: by
  unfold cauchyPDF
  fun_prop

@[deprecated (since := "2026-03-06")]
alias _root_Probability.measurable_cauchyPDF := measurable_cauchyPDF

@[fun_prop]

Depends on / 依赖: cauchyPDF, fun_prop
-/
lemma measurable_cauchyPDF (x₀ : Real) (γ : Real>=0) : Measurable (cauchyPDF x₀ γ) := by
  unfold cauchyPDF
  fun_prop

@[deprecated (since := "2026-03-06")]
alias _root_Probability.measurable_cauchyPDF := measurable_cauchyPDF

@[fun_prop]
/--
lemma `stronglyMeasurable_cauchyPDF` / 引理 `stronglyMeasurable_cauchyPDF`

English:
lemma stronglyMeasurable_cauchyPDF
  given: (x₀ : Real) (γ : Real>=0)
  proof: by fun_prop

@[deprecated (since := "2026-03-06")]
alias _root_Probability.stronglyMeasurable_cauchyPDF := stronglyMeasurable_cauchyPDF

中文:
引理 stronglyMeasurable_cauchyPDF
  条件: (x₀ : 实数) (γ : 实数>=0)
  证明: by fun_prop

@[deprecated (since := "2026-03-06")]
alias _root_Probability.stronglyMeasurable_cauchyPDF := stronglyMeasurable_cauchyPDF

Depends on / 依赖: fun_prop
-/
lemma stronglyMeasurable_cauchyPDF (x₀ : Real) (γ : Real>=0) :
    StronglyMeasurable (cauchyPDF x₀ γ) := by fun_prop

@[deprecated (since := "2026-03-06")]
alias _root_Probability.stronglyMeasurable_cauchyPDF := stronglyMeasurable_cauchyPDF

/--
lemma `cauchyPDF_pos` / 引理 `cauchyPDF_pos`

English:
lemma cauchyPDF_pos
  given: (x₀ : Real) {γ : Real>=0} (hγ : γ != 0) (x : Real)
  statement: 0 < cauchyPDFReal x₀ γ x
  proof: by
  rw [cauchyPDFReal_def]
  positivity

@[deprecated (since := "2026-03-06")]
alias _root_Probability.cauchyPDF_pos := cauchyPDF_pos

中文:
引理 cauchyPDF_pos
  条件: (x₀ : 实数) {γ : 实数>=0} (hγ : γ != 0) (x : 实数)
  结论: 0 < cauchyPDF实数 x₀ γ x
  证明: by
  rw [cauchyPDFReal_def]
  positivity

@[deprecated (since := "2026-03-06")]
alias _root_Probability.cauchyPDF_pos := cauchyPDF_pos

Depends on / 依赖: cauchyPDFReal_def
-/
lemma cauchyPDF_pos (x₀ : Real) {γ : Real>=0} (hγ : γ != 0) (x : Real) : 0 < cauchyPDFReal x₀ γ x := by
  rw [cauchyPDFReal_def]
  positivity

@[deprecated (since := "2026-03-06")]
alias _root_Probability.cauchyPDF_pos := cauchyPDF_pos

/--
lemma `integral_cauchyPDFReal_eq_one` / 引理 `integral_cauchyPDFReal_eq_one`

English:
lemma integral_cauchyPDFReal_eq_one
  given: (x₀ : Real) {γ : Real>=0} (hγ : γ != 0)
  proof: by
  simp [cauchyPDFReal_def', NNReal.coe_inv, integral_const_mul,
    integral_sub_right_eq_self (f := fun x : Real => (1 + (x / ↑γ) ^ 2)⁻¹),
    integral_comp_div (g := fun x : Real => (1 + x ^ 2)⁻¹)]
  field

@[deprecated (since := "2026-03-06")]
alias _root_Probability.integral_cauchyPDFReal := 

中文:
引理 integral_cauchyPDFReal_eq_one
  条件: (x₀ : 实数) {γ : 实数>=0} (hγ : γ != 0)
  证明: by
  simp [cauchyPDFReal_def', NNReal.coe_inv, integral_const_mul,
    integral_sub_right_eq_self (f := fun x : Real => (1 + (x / ↑γ) ^ 2)⁻¹),
    integral_comp_div (g := fun x : Real => (1 + x ^ 2)⁻¹)]
  field

@[deprecated (since := "2026-03-06")]
alias _root_Probability.integral_cauchyPDFReal := 

Depends on / 依赖: NNReal, NNReal.coe_inv, cauchyPDFReal_def, coe_inv, integral_comp_div, integral_const_mul, integral_sub_right_eq_self
-/
lemma integral_cauchyPDFReal_eq_one (x₀ : Real) {γ : Real>=0} (hγ : γ != 0) :
    ∫ x, cauchyPDFReal x₀ γ x = 1 := by
  simp [cauchyPDFReal_def', NNReal.coe_inv, integral_const_mul,
    integral_sub_right_eq_self (f := fun x : Real => (1 + (x / ↑γ) ^ 2)⁻¹),
    integral_comp_div (g := fun x : Real => (1 + x ^ 2)⁻¹)]
  field

@[deprecated (since := "2026-03-06")]
alias _root_Probability.integral_cauchyPDFReal := integral_cauchyPDFReal_eq_one

@[fun_prop]
/--
lemma `integrable_cauchyPDFReal` / 引理 `integrable_cauchyPDFReal`

English:
lemma integrable_cauchyPDFReal
  given: (x₀ : Real) {γ : Real>=0}
  proof: by
  by_cases! h : γ = 0
  · simp only [h, cauchyPDFReal_scale_zero]
    exact integrable_zero _ _ _
  apply Integrable.of_integral_ne_zero
  simp [h, integral_cauchyPDFReal_eq_one]

@[deprecated (since := "2026-03-06")]
alias _root_Probability.integrable_cauchyPDFReal := integrable_cauchyPDFReal

中文:
引理 integrable_cauchyPDFReal
  条件: (x₀ : 实数) {γ : 实数>=0}
  证明: by
  by_cases! h : γ = 0
  · simp only [h, cauchyPDFReal_scale_zero]
    exact integrable_zero _ _ _
  apply Integrable.of_integral_ne_zero
  simp [h, integral_cauchyPDFReal_eq_one]

@[deprecated (since := "2026-03-06")]
alias _root_Probability.integrable_cauchyPDFReal := integrable_cauchyPDFReal

Depends on / 依赖: Integrable, Integrable.of_integral_ne_zero, cauchyPDFReal_scale_zero, integrable_zero, integral_cauchyPDFReal_eq_one, of_integral_ne_zero
-/
lemma integrable_cauchyPDFReal (x₀ : Real) {γ : Real>=0} :
    Integrable (cauchyPDFReal x₀ γ) := by
  by_cases! h : γ = 0
  · simp only [h, cauchyPDFReal_scale_zero]
    exact integrable_zero _ _ _
  apply Integrable.of_integral_ne_zero
  simp [h, integral_cauchyPDFReal_eq_one]

@[deprecated (since := "2026-03-06")]
alias _root_Probability.integrable_cauchyPDFReal := integrable_cauchyPDFReal

/-- The pdf of the cauchy distribution integrates to 1. -/
@[simp]
/--
lemma `lintegral_cauchyPDF_eq_one` / 引理 `lintegral_cauchyPDF_eq_one`

English:
lemma lintegral_cauchyPDF_eq_one
  given: (x₀ : Real) {γ : Real>=0} (hγ : γ != 0)
  proof: by
  unfold cauchyPDF
  rw [← ENNReal.toReal_eq_one_iff]; rw [← integral_eq_lintegral_of_nonneg_ae
    (ae_of_all _ fun x => (cauchyPDF_pos x₀ hγ x).le) (by fun_prop)]; rw [integral_cauchyPDFReal_eq_one x₀ hγ]

@[deprecated (since := "2026-03-06")]
alias _root_Probability.lintegral_cauchyPDF_eq_one 

中文:
引理 lintegral_cauchyPDF_eq_one
  条件: (x₀ : 实数) {γ : 实数>=0} (hγ : γ != 0)
  证明: by
  unfold cauchyPDF
  rw [← ENNReal.toReal_eq_one_iff]; rw [← integral_eq_lintegral_of_nonneg_ae
    (ae_of_all _ fun x => (cauchyPDF_pos x₀ hγ x).le) (by fun_prop)]; rw [integral_cauchyPDFReal_eq_one x₀ hγ]

@[deprecated (since := "2026-03-06")]
alias _root_Probability.lintegral_cauchyPDF_eq_one 

Depends on / 依赖: ENNReal, ENNReal.toReal_eq_one_iff, ae_of_all, cauchyPDF, cauchyPDF_pos, fun_prop, integral_cauchyPDFReal_eq_one, integral_eq_lintegral_of_nonneg_ae, toReal_eq_one_iff
-/
lemma lintegral_cauchyPDF_eq_one (x₀ : Real) {γ : Real>=0} (hγ : γ != 0) :
    ∫⁻ x, cauchyPDF x₀ γ x = 1 := by
  unfold cauchyPDF
  rw [← ENNReal.toReal_eq_one_iff]; rw [← integral_eq_lintegral_of_nonneg_ae
    (ae_of_all _ fun x => (cauchyPDF_pos x₀ hγ x).le) (by fun_prop)]; rw [integral_cauchyPDFReal_eq_one x₀ hγ]

@[deprecated (since := "2026-03-06")]
alias _root_Probability.lintegral_cauchyPDF_eq_one := lintegral_cauchyPDF_eq_one

end CauchyPDF

section CauchyMeasure

/--
Definition of `cauchyMeasure` / `cauchyMeasure` 的定义

English:
definition cauchyMeasure
  signature: (x₀ : Real) (γ : Real>=0)
  body: if γ = 0 then dirac x₀ else volume.withDensity (cauchyPDF x₀ γ)

@[deprecated (since := "2026-03-06")]
alias _root_Probability.cauchyMeasure := cauchyMeasure

中文:
定义 cauchyMeasure
  签名: (x₀ : 实数) (γ : 实数>=0)
  定义体: if γ = 0 then dirac x₀ else volume.withDensity (cauchyPDF x₀ γ)

@[deprecated (since := "2026-03-06")]
alias _root_Probability.cauchyMeasure := cauchyMeasure

Depends on / 依赖: cauchyPDF, volume, volume.withDensity, withDensity
-/
noncomputable def cauchyMeasure (x₀ : Real) (γ : Real>=0) : Measure Real :=
  if γ = 0 then dirac x₀ else volume.withDensity (cauchyPDF x₀ γ)

@[deprecated (since := "2026-03-06")]
alias _root_Probability.cauchyMeasure := cauchyMeasure

/--
lemma `cauchyMeasure_of_scale_ne_zero` / 引理 `cauchyMeasure_of_scale_ne_zero`

English:
lemma cauchyMeasure_of_scale_ne_zero
  given: (x₀ : Real) {γ : Real>=0} (hγ : γ != 0)
  proof: if_neg hγ

@[deprecated (since := "2026-03-06")]
alias _root_Probability.cauchyMeasure_of_scale_ne_zero := cauchyMeasure_of_scale_ne_zero

@[simp]

中文:
引理 cauchyMeasure_of_scale_ne_zero
  条件: (x₀ : 实数) {γ : 实数>=0} (hγ : γ != 0)
  证明: if_neg hγ

@[deprecated (since := "2026-03-06")]
alias _root_Probability.cauchyMeasure_of_scale_ne_zero := cauchyMeasure_of_scale_ne_zero

@[simp]

Depends on / 依赖: if_neg
-/
lemma cauchyMeasure_of_scale_ne_zero (x₀ : Real) {γ : Real>=0} (hγ : γ != 0) :
    cauchyMeasure x₀ γ = volume.withDensity (cauchyPDF x₀ γ) := if_neg hγ

@[deprecated (since := "2026-03-06")]
alias _root_Probability.cauchyMeasure_of_scale_ne_zero := cauchyMeasure_of_scale_ne_zero

@[simp]
/--
lemma `cauchyMeasure_zero_scale` / 引理 `cauchyMeasure_zero_scale`

English:
lemma cauchyMeasure_zero_scale
  given: (x₀ : Real)
  statement: cauchyMeasure x₀ 0 = dirac x₀
  proof: if_pos rfl

@[deprecated (since := "2026-03-06")]
alias _root_Probability.cauchyMeasure_zero_scale := cauchyMeasure_zero_scale

中文:
引理 cauchyMeasure_zero_scale
  条件: (x₀ : 实数)
  结论: cauchyMeasure x₀ 0 = dirac x₀
  证明: if_pos rfl

@[deprecated (since := "2026-03-06")]
alias _root_Probability.cauchyMeasure_zero_scale := cauchyMeasure_zero_scale

Depends on / 依赖: if_pos
-/
lemma cauchyMeasure_zero_scale (x₀ : Real) : cauchyMeasure x₀ 0 = dirac x₀ := if_pos rfl

@[deprecated (since := "2026-03-06")]
alias _root_Probability.cauchyMeasure_zero_scale := cauchyMeasure_zero_scale

/--
Instance `instIsProbabilityMeasure_cauchyMeasure` / 实例 `instIsProbabilityMeasure_cauchyMeasure`

English:
instance instIsProbabilityMeasure_cauchyMeasure
  signature: (x₀ : Real) (γ : Real>=0)
  body: by by_cases h : γ = 0 <;> simp [cauchyMeasure_of_scale_ne_zero, h]

@[deprecated (since := "2026-03-06")]
alias _root_Probability.instIsProbabilityMeasure_cauchyMeasure :=
  instIsProbabilityMeasure_cauchyMeasure

中文:
实例 instIsProbabilityMeasure_cauchyMeasure
  签名: (x₀ : 实数) (γ : 实数>=0)
  定义体: by by_cases h : γ = 0 <;> simp [cauchyMeasure_of_scale_ne_zero, h]

@[deprecated (since := "2026-03-06")]
alias _root_Probability.instIsProbabilityMeasure_cauchyMeasure :=
  instIsProbabilityMeasure_cauchyMeasure

Depends on / 依赖: cauchyMeasure_of_scale_ne_zero
-/
instance instIsProbabilityMeasure_cauchyMeasure (x₀ : Real) (γ : Real>=0) :
    IsProbabilityMeasure (cauchyMeasure x₀ γ) where
  measure_univ := by by_cases h : γ = 0 <;> simp [cauchyMeasure_of_scale_ne_zero, h]

@[deprecated (since := "2026-03-06")]
alias _root_Probability.instIsProbabilityMeasure_cauchyMeasure :=
  instIsProbabilityMeasure_cauchyMeasure

end CauchyMeasure

end ProbabilityTheory
