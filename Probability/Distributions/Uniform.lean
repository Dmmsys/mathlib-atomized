/-
Copyright (c) 2024 Josha Dekker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josha Dekker, Devon Tuma, Kexing Ying
-/
module

public import Mathlib.Probability.Density
public import Mathlib.Probability.ConditionalProbability
public import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# Uniform distributions and probability mass functions

This file defines two related notions of uniform distributions, which will be unified in the future.

## Uniform distributions

Defines the uniform distribution for any set with finite measure.

### Main definitions
* `IsUniform X s ℙ μ` : A random variable `X` has uniform distribution on `s` under `ℙ` if the
  push-forward measure agrees with the rescaled restricted measure `μ`.

## Uniform probability mass functions

This file defines a number of uniform `PMF` distributions from various inputs,
  uniformly drawing from the corresponding object.

### Main definitions
`PMF.uniformOfFinset` gives each element in the set equal probability,
  with `0` probability for elements not in the set.

`PMF.uniformOfFintype` gives all elements equal probability,
  equal to the inverse of the size of the `Fintype`.

`PMF.ofMultiset` draws randomly from the given `Multiset`, treating duplicate values as distinct.
  Each probability is given by the count of the element divided by the size of the `Multiset`

## TODO
* Refactor the `PMF` definitions to come from a `uniformMeasure` on a `Finset`/`Fintype`/`Multiset`.
-/

@[expose] public section

open scoped Finset MeasureTheory NNReal ENNReal

-- TODO: We can't `open ProbabilityTheory` without opening the `ProbabilityTheory` scope :(
open TopologicalSpace MeasureTheory.Measure PMF

noncomputable section

namespace MeasureTheory

variable {E : Type*} [MeasurableSpace E] {μ : Measure E}

namespace pdf

variable {Ω : Type*}
variable {_ : MeasurableSpace Ω} {ℙ : Measure Ω}

/--
Definition of `IsUniform` / `IsUniform` 的定义

English:
definition IsUniform
  signature: (X : Ω -> E) (s : Set E) (ℙ : Measure Ω) (μ : Measure E := by volume_tac)
  body: map X ℙ = ProbabilityTheory.cond μ s

中文:
定义 是一致
  签名: (X : Ω -> E) (s : 集合 E) (ℙ : 测度 Ω) (μ : 测度 E := by volume_tac)
  定义体: map X ℙ = ProbabilityTheory.cond μ s

Depends on / 依赖: ProbabilityTheory, ProbabilityTheory.cond, volume_tac
-/
def IsUniform (X : Ω -> E) (s : Set E) (ℙ : Measure Ω) (μ : Measure E := by volume_tac) :=
  map X ℙ = ProbabilityTheory.cond μ s

namespace IsUniform

/--
theorem `aemeasurable` / 定理 `aemeasurable`

English:
theorem aemeasurable
  statement: {X : Ω -> E} {s : Set E} (hns : μ s != 0) (hnt : μ s != ∞)
  proof: by
  dsimp [IsUniform, ProbabilityTheory.cond] at hu
  by_contra h
  rw [map_of_not_aemeasurable h] at hu
  apply zero_ne_one' Real>=0∞
  calc
    0 = (0 : Measure E) Set.univ := rfl
    _ = _ := by rw [hu, Measure.smul_apply, restrict_apply MeasurableSet.univ,
      Set.univ_inter, smul_eq_mul, ENN

中文:
定理 aemeasurable
  结论: {X : Ω -> E} {s : 集合 E} (hns : μ s != 0) (hnt : μ s != ∞)
  证明: by
  dsimp [IsUniform, ProbabilityTheory.cond] at hu
  by_contra h
  rw [map_of_not_aemeasurable h] at hu
  apply zero_ne_one' Real>=0∞
  calc
    0 = (0 : Measure E) Set.univ := rfl
    _ = _ := by rw [hu, Measure.smul_apply, restrict_apply MeasurableSet.univ,
      Set.univ_inter, smul_eq_mul, ENN

Depends on / 依赖: ENNReal, ENNReal.inv_mul_cancel, IsUniform, MeasurableSet, MeasurableSet.univ, Measure, Measure.smul_apply, ProbabilityTheory, ProbabilityTheory.cond, Set.univ, Set.univ_inter, inv_mul_cancel, map_of_not_aemeasurable, restrict_apply, smul_apply, smul_eq_mul, univ_inter, zero_ne_one
-/
theorem aemeasurable {X : Ω -> E} {s : Set E} (hns : μ s != 0) (hnt : μ s != ∞)
    (hu : IsUniform X s ℙ μ) : AEMeasurable X ℙ := by
  dsimp [IsUniform, ProbabilityTheory.cond] at hu
  by_contra h
  rw [map_of_not_aemeasurable h] at hu
  apply zero_ne_one' Real>=0∞
  calc
    0 = (0 : Measure E) Set.univ := rfl
    _ = _ := by rw [hu, Measure.smul_apply, restrict_apply MeasurableSet.univ,
      Set.univ_inter, smul_eq_mul, ENNReal.inv_mul_cancel hns hnt]

/--
theorem `absolutelyContinuous` / 定理 `absolutelyContinuous`

English:
theorem absolutelyContinuous
  given: {X : Ω -> E} {s : Set E} (hu : IsUniform X s ℙ μ)
  statement: map X ℙ ≪ μ
  proof: by
  rw [hu]; exact ProbabilityTheory.cond_absolutelyContinuous

中文:
定理 absolutelyContinuous
  条件: {X : Ω -> E} {s : 集合 E} (hu : 是一致 X s ℙ μ)
  结论: map X ℙ ≪ μ
  证明: by
  rw [hu]; exact ProbabilityTheory.cond_absolutelyContinuous

Depends on / 依赖: ProbabilityTheory, ProbabilityTheory.cond_absolutelyContinuous, cond_absolutelyContinuous
-/
theorem absolutelyContinuous {X : Ω -> E} {s : Set E} (hu : IsUniform X s ℙ μ) : map X ℙ ≪ μ := by
  rw [hu]; exact ProbabilityTheory.cond_absolutelyContinuous

/--
theorem `measure_preimage` / 定理 `measure_preimage`

English:
theorem measure_preimage
  statement: {X : Ω -> E} {s : Set E} (hns : μ s != 0) (hnt : μ s != ∞)
  proof: by
  rwa [← map_apply_of_aemeasurable (hu.aemeasurable hns hnt) hA, hu, ProbabilityTheory.cond_apply',
    ENNReal.div_eq_inv_mul]

中文:
定理 measure_preimage
  结论: {X : Ω -> E} {s : 集合 E} (hns : μ s != 0) (hnt : μ s != ∞)
  证明: by
  rwa [← map_apply_of_aemeasurable (hu.aemeasurable hns hnt) hA, hu, ProbabilityTheory.cond_apply',
    ENNReal.div_eq_inv_mul]

Depends on / 依赖: ENNReal, ENNReal.div_eq_inv_mul, ProbabilityTheory, ProbabilityTheory.cond_apply, aemeasurable, cond_apply, div_eq_inv_mul, hu.aemeasurable, map_apply_of_aemeasurable
-/
theorem measure_preimage {X : Ω -> E} {s : Set E} (hns : μ s != 0) (hnt : μ s != ∞)
    (hu : IsUniform X s ℙ μ) {A : Set E} (hA : MeasurableSet A) :
    ℙ (X ⁻¹' A) = μ (s inter A) / μ s := by
  rwa [← map_apply_of_aemeasurable (hu.aemeasurable hns hnt) hA, hu, ProbabilityTheory.cond_apply',
    ENNReal.div_eq_inv_mul]

/--
theorem `isProbabilityMeasure` / 定理 `isProbabilityMeasure`

English:
theorem isProbabilityMeasure
  statement: {X : Ω -> E} {s : Set E} (hns : μ s != 0) (hnt : μ s != ∞)
  proof: ⟨by
    have : X ⁻¹' Set.univ = Set.univ := Set.preimage_univ
    rw [← this]; rw [hu.measure_preimage hns hnt MeasurableSet.univ]; rw [Set.inter_univ]; rw [ENNReal.div_self hns hnt]⟩

中文:
定理 isProbabilityMeasure
  结论: {X : Ω -> E} {s : 集合 E} (hns : μ s != 0) (hnt : μ s != ∞)
  证明: ⟨by
    have : X ⁻¹' Set.univ = Set.univ := Set.preimage_univ
    rw [← this]; rw [hu.measure_preimage hns hnt MeasurableSet.univ]; rw [Set.inter_univ]; rw [ENNReal.div_self hns hnt]⟩

Depends on / 依赖: ENNReal, ENNReal.div_self, MeasurableSet, MeasurableSet.univ, Set.inter_univ, Set.preimage_univ, Set.univ, div_self, hu.measure_preimage, inter_univ, measure_preimage, preimage_univ
-/
theorem isProbabilityMeasure {X : Ω -> E} {s : Set E} (hns : μ s != 0) (hnt : μ s != ∞)
    (hu : IsUniform X s ℙ μ) : IsProbabilityMeasure ℙ :=
  ⟨by
    have : X ⁻¹' Set.univ = Set.univ := Set.preimage_univ
    rw [← this]; rw [hu.measure_preimage hns hnt MeasurableSet.univ]; rw [Set.inter_univ]; rw [ENNReal.div_self hns hnt]⟩

/--
theorem `toMeasurable_iff` / 定理 `toMeasurable_iff`

English:
theorem toMeasurable_iff
  given: {X : Ω -> E} {s : Set E}
  proof: by
  unfold IsUniform
  rw [ProbabilityTheory.cond_toMeasurable_eq]

中文:
定理 toMeasurable_iff
  条件: {X : Ω -> E} {s : 集合 E}
  证明: by
  unfold IsUniform
  rw [ProbabilityTheory.cond_toMeasurable_eq]

Depends on / 依赖: IsUniform, ProbabilityTheory, ProbabilityTheory.cond_toMeasurable_eq, cond_toMeasurable_eq
-/
theorem toMeasurable_iff {X : Ω -> E} {s : Set E} :
    IsUniform X (toMeasurable μ s) ℙ μ ↔ IsUniform X s ℙ μ := by
  unfold IsUniform
  rw [ProbabilityTheory.cond_toMeasurable_eq]

/--
theorem `toMeasurable` / 定理 `toMeasurable`

English:
theorem toMeasurable
  given: {X : Ω -> E} {s : Set E} (hu : IsUniform X s ℙ μ)
  proof: toMeasurable_iff.mpr hu

中文:
定理 toMeasurable
  条件: {X : Ω -> E} {s : 集合 E} (hu : 是一致 X s ℙ μ)
  证明: toMeasurable_iff.mpr hu
-/
protected theorem toMeasurable {X : Ω -> E} {s : Set E} (hu : IsUniform X s ℙ μ) :
    IsUniform X (toMeasurable μ s) ℙ μ :=
  toMeasurable_iff.mpr hu

/--
theorem `hasPDF` / 定理 `hasPDF`

English:
theorem hasPDF
  statement: {X : Ω -> E} {s : Set E} (hns : μ s != 0) (hnt : μ s != ∞)
  proof: by
  let t := toMeasurable μ s
apply hasPDF_of_map_eq_withDensity (hu.aemeasurable hns hnt) (t.indicator ((μ t)⁻¹ • 1))
    (measurable_one.aemeasurable.const_smul (μ t)⁻¹).indicator (measurableSet_toMeasurable μ s)
  rw [hu]; rw [withDensity_indicator (measurableSet_toMeasurable μ s)]; rw [withDens

中文:
定理 hasPDF
  结论: {X : Ω -> E} {s : 集合 E} (hns : μ s != 0) (hnt : μ s != ∞)
  证明: by
  let t := toMeasurable μ s
apply hasPDF_of_map_eq_withDensity (hu.aemeasurable hns hnt) (t.indicator ((μ t)⁻¹ • 1))
    (measurable_one.aemeasurable.const_smul (μ t)⁻¹).indicator (measurableSet_toMeasurable μ s)
  rw [hu]; rw [withDensity_indicator (measurableSet_toMeasurable μ s)]; rw [withDens

Depends on / 依赖: ProbabilityTheory, ProbabilityTheory.cond, aemeasurable, const_smul, hasPDF_of_map_eq_withDensity, hu.aemeasurable, indicator, measurableSet_toMeasurable, measurable_one, measurable_one.aemeasurable.const_smul, measure_toMeasurable, restrict_toMeasurable, t.indicator, toMeasurable, withDensity_indicator, withDensity_one, withDensity_smul
-/
theorem hasPDF {X : Ω -> E} {s : Set E} (hns : μ s != 0) (hnt : μ s != ∞)
    (hu : IsUniform X s ℙ μ) : HasPDF X ℙ μ := by
  let t := toMeasurable μ s
apply hasPDF_of_map_eq_withDensity (hu.aemeasurable hns hnt) (t.indicator ((μ t)⁻¹ • 1))
    (measurable_one.aemeasurable.const_smul (μ t)⁻¹).indicator (measurableSet_toMeasurable μ s)
  rw [hu]; rw [withDensity_indicator (measurableSet_toMeasurable μ s)]; rw [withDensity_smul _ measurable_one]; rw [withDensity_one]; rw [restrict_toMeasurable hnt]; rw [measure_toMeasurable]; rw [ProbabilityTheory.cond]

/--
theorem `pdf_eq_zero_of_measure_eq_zero_or_top` / 定理 `pdf_eq_zero_of_measure_eq_zero_or_top`

English:
theorem pdf_eq_zero_of_measure_eq_zero_or_top
  statement: {X : Ω -> E} {s : Set E}
  proof: by
  rcases hμs with H | H
  · simp only [IsUniform, ProbabilityTheory.cond, H, ENNReal.inv_zero, restrict_eq_zero.mpr H,
    smul_zero] at hu
    simp [pdf, hu]
  · simp only [IsUniform, ProbabilityTheory.cond, H, ENNReal.inv_top, zero_smul] at hu
    simp [pdf, hu]

中文:
定理 pdf_eq_zero_of_measure_eq_zero_or_top
  结论: {X : Ω -> E} {s : 集合 E}
  证明: by
  rcases hμs with H | H
  · simp only [IsUniform, ProbabilityTheory.cond, H, ENNReal.inv_zero, restrict_eq_zero.mpr H,
    smul_zero] at hu
    simp [pdf, hu]
  · simp only [IsUniform, ProbabilityTheory.cond, H, ENNReal.inv_top, zero_smul] at hu
    simp [pdf, hu]

Depends on / 依赖: ENNReal, ENNReal.inv_top, ENNReal.inv_zero, IsUniform, ProbabilityTheory, ProbabilityTheory.cond, inv_top, inv_zero, restrict_eq_zero, restrict_eq_zero.mpr, smul_zero, zero_smul
-/
theorem pdf_eq_zero_of_measure_eq_zero_or_top {X : Ω -> E} {s : Set E}
    (hu : IsUniform X s ℙ μ) (hμs : μ s = 0 ∨ μ s = ∞) : pdf X ℙ μ =ᵐ[μ] 0 := by
  rcases hμs with H | H
  · simp only [IsUniform, ProbabilityTheory.cond, H, ENNReal.inv_zero, restrict_eq_zero.mpr H,
    smul_zero] at hu
    simp [pdf, hu]
  · simp only [IsUniform, ProbabilityTheory.cond, H, ENNReal.inv_top, zero_smul] at hu
    simp [pdf, hu]

/--
theorem `pdf_eq` / 定理 `pdf_eq`

English:
theorem pdf_eq
  statement: {X : Ω -> E} {s : Set E} (hms : MeasurableSet s)
  proof: by
  by_cases hnt : μ s = ∞
  · simp [pdf_eq_zero_of_measure_eq_zero_or_top hu (Or.inr hnt), hnt]
  by_cases hns : μ s = 0
  · filter_upwards [measure_eq_zero_iff_ae_notMem.mp hns,
      pdf_eq_zero_of_measure_eq_zero_or_top hu (Or.inl hns)] with x hx h'x
    simp [hx, h'x, hns]
  have : HasPDF X ℙ 

中文:
定理 pdf_eq
  结论: {X : Ω -> E} {s : 集合 E} (hms : 可测集 s)
  证明: by
  by_cases hnt : μ s = ∞
  · simp [pdf_eq_zero_of_measure_eq_zero_or_top hu (Or.inr hnt), hnt]
  by_cases hns : μ s = 0
  · filter_upwards [measure_eq_zero_iff_ae_notMem.mp hns,
      pdf_eq_zero_of_measure_eq_zero_or_top hu (Or.inl hns)] with x hx h'x
    simp [hx, h'x, hns]
  have : HasPDF X ℙ 

Depends on / 依赖: HasPDF, IsProbabilityMeasure, Or.inl, Or.inr, eq_of_map_eq_withDensity, filter_upwards, hasPDF, isProbabilityMeasure, measurable_one, measure_eq_zero_iff_ae_notMem, measure_eq_zero_iff_ae_notMem.mp, pdf_eq_zero_of_measure_eq_zero_or_top, withDensity_indicator, withDensity_one, withDensity_smul
-/
theorem pdf_eq {X : Ω -> E} {s : Set E} (hms : MeasurableSet s)
    (hu : IsUniform X s ℙ μ) : pdf X ℙ μ =ᵐ[μ] s.indicator ((μ s)⁻¹ • (1 : E -> Real>=0∞)) := by
  by_cases hnt : μ s = ∞
  · simp [pdf_eq_zero_of_measure_eq_zero_or_top hu (Or.inr hnt), hnt]
  by_cases hns : μ s = 0
  · filter_upwards [measure_eq_zero_iff_ae_notMem.mp hns,
      pdf_eq_zero_of_measure_eq_zero_or_top hu (Or.inl hns)] with x hx h'x
    simp [hx, h'x, hns]
  have : HasPDF X ℙ μ := hasPDF hns hnt hu
  have : IsProbabilityMeasure ℙ := isProbabilityMeasure hns hnt hu
  apply (eq_of_map_eq_withDensity _ _).mp
  · rw [hu, withDensity_indicator hms, withDensity_smul _ measurable_one, withDensity_one,
      ProbabilityTheory.cond]
  · exact (measurable_one.aemeasurable.const_smul (μ s)⁻¹).indicator hms

/--
theorem `pdf_toReal_ae_eq` / 定理 `pdf_toReal_ae_eq`

English:
theorem pdf_toReal_ae_eq
  statement: {X : Ω -> E} {s : Set E} (hms : MeasurableSet s)
  proof: Filter.EventuallyEq.fun_comp (pdf_eq hms hX) ENNReal.toReal

中文:
定理 pdf_to实数_ae_eq
  结论: {X : Ω -> E} {s : 集合 E} (hms : 可测集 s)
  证明: Filter.EventuallyEq.fun_comp (pdf_eq hms hX) ENNReal.toReal

Depends on / 依赖: ENNReal, ENNReal.toReal, EventuallyEq, Filter, Filter.EventuallyEq.fun_comp, fun_comp, pdf_eq, toReal
-/
theorem pdf_toReal_ae_eq {X : Ω -> E} {s : Set E} (hms : MeasurableSet s)
    (hX : IsUniform X s ℙ μ) :
    (fun x => (pdf X ℙ μ x).toReal) =ᵐ[μ] fun x =>
      (s.indicator ((μ s)⁻¹ • (1 : E -> Real>=0∞)) x).toReal :=
  Filter.EventuallyEq.fun_comp (pdf_eq hms hX) ENNReal.toReal

variable {X : Ω -> Real} {s : Set Real}

/--
theorem `mul_pdf_integrable` / 定理 `mul_pdf_integrable`

English:
theorem mul_pdf_integrable
  given: (hcs : IsCompact s) (huX : IsUniform X s ℙ)
  proof: by
  by_cases hnt : volume s = 0 ∨ volume s = ∞
  · have I : Integrable (fun x => x * ENNReal.toReal (0)) := by simp
    apply I.congr
    filter_upwards [pdf_eq_zero_of_measure_eq_zero_or_top huX hnt] with x hx
    simp [hx]
  simp only [not_or] at hnt
  have : IsProbabilityMeasure ℙ := isProbabili

中文:
定理 mul_pdf_integrable
  条件: (hcs : 是紧集 s) (huX : 是一致 X s ℙ)
  证明: by
  by_cases hnt : volume s = 0 ∨ volume s = ∞
  · have I : Integrable (fun x => x * ENNReal.toReal (0)) := by simp
    apply I.congr
    filter_upwards [pdf_eq_zero_of_measure_eq_zero_or_top huX hnt] with x hx
    simp [hx]
  simp only [not_or] at hnt
  have : IsProbabilityMeasure ℙ := isProbabili

Depends on / 依赖: ENNReal, ENNReal.toReal, I.congr, Integrable, IsProbabilityMeasure, aemeasurable, aemeasurable.ennreal_toReal.aestronglyMeasurable, aestronglyMeasurable, aestronglyMeasurable_id, aestronglyMeasurable_id.mul, ennreal_toReal, filter_upwards, hasFiniteIntegral_mul, hcs.measurableSet, isProbabilityMeasure, measurableSet, measurable_pdf, not_or, pdf_eq, pdf_eq_zero_of_measure_eq_zero_or_top
-/
theorem mul_pdf_integrable (hcs : IsCompact s) (huX : IsUniform X s ℙ) :
    Integrable fun x : Real => x * (pdf X ℙ volume x).toReal := by
  by_cases hnt : volume s = 0 ∨ volume s = ∞
  · have I : Integrable (fun x => x * ENNReal.toReal (0)) := by simp
    apply I.congr
    filter_upwards [pdf_eq_zero_of_measure_eq_zero_or_top huX hnt] with x hx
    simp [hx]
  simp only [not_or] at hnt
  have : IsProbabilityMeasure ℙ := isProbabilityMeasure hnt.1 hnt.2 huX
  constructor
  · exact aestronglyMeasurable_id.mul
      (measurable_pdf X ℙ).aemeasurable.ennreal_toReal.aestronglyMeasurable
  refine hasFiniteIntegral_mul (pdf_eq hcs.measurableSet huX) ?_
  set ind := (volume s)⁻¹ • (1 : Real -> Real>=0∞)
  have : forall x, ‖x‖ₑ * s.indicator ind x = s.indicator (fun x => ‖x‖ₑ * ind x) x := fun x =>
    (s.indicator_mul_right (fun x => ↑‖x‖₊) ind).symm
  simp only [ind, this, lintegral_indicator hcs.measurableSet, mul_one, smul_eq_mul,
    Pi.one_apply, Pi.smul_apply]
  rw [lintegral_mul_const _ measurable_enorm]
  exact ENNReal.mul_ne_top (setLIntegral_lt_top_of_isCompact hnt.2 hcs continuous_nnnorm).ne
    (ENNReal.inv_lt_top.2 (pos_iff_ne_zero.mpr hnt.1)).ne

/--
theorem `integral_eq` / 定理 `integral_eq`

English:
theorem integral_eq
  given: (huX : IsUniform X s ℙ)
  proof: by
  rw [← smul_eq_mul]; rw [← integral_smul_measure]
  dsimp only [IsUniform, ProbabilityTheory.cond] at huX
  rw [← huX]
  by_cases hX : AEMeasurable X ℙ
  · exact (integral_map hX aestronglyMeasurable_id).symm
  · rw [map_of_not_aemeasurable hX, integral_zero_measure, integral_non_aestronglyMeasu

中文:
定理 integral_eq
  条件: (huX : 是一致 X s ℙ)
  证明: by
  rw [← smul_eq_mul]; rw [← integral_smul_measure]
  dsimp only [IsUniform, ProbabilityTheory.cond] at huX
  rw [← huX]
  by_cases hX : AEMeasurable X ℙ
  · exact (integral_map hX aestronglyMeasurable_id).symm
  · rw [map_of_not_aemeasurable hX, integral_zero_measure, integral_non_aestronglyMeasu

Depends on / 依赖: AEMeasurable, IsUniform, ProbabilityTheory, ProbabilityTheory.cond, aestronglyMeasurable_id, aestronglyMeasurable_iff_aemeasurable, integral_map, integral_non_aestronglyMeasurable, integral_smul_measure, integral_zero_measure, map_of_not_aemeasurable, smul_eq_mul
-/
theorem integral_eq (huX : IsUniform X s ℙ) :
    ∫ x, X x ∂ℙ = (volume s)⁻¹.toReal * ∫ x in s, x := by
  rw [← smul_eq_mul]; rw [← integral_smul_measure]
  dsimp only [IsUniform, ProbabilityTheory.cond] at huX
  rw [← huX]
  by_cases hX : AEMeasurable X ℙ
  · exact (integral_map hX aestronglyMeasurable_id).symm
  · rw [map_of_not_aemeasurable hX, integral_zero_measure, integral_non_aestronglyMeasurable]
    rwa [aestronglyMeasurable_iff_aemeasurable]

end IsUniform

variable {X : Ω -> E}

/--
lemma `IsUniform.cond` / 引理 `IsUniform.cond`

English:
lemma IsUniform.cond
  given: {s : Set E}
  proof: map_id

中文:
引理 是一致.cond
  条件: {s : 集合 E}
  证明: map_id

Depends on / 依赖: map_id
-/
lemma IsUniform.cond {s : Set E} :
    IsUniform (id : E -> E) s (ProbabilityTheory.cond μ s) μ :=
  map_id

/--
Definition of `uniformPDF` / `uniformPDF` 的定义

English:
definition uniformPDF
  signature: (s : Set E) (x : E) (μ : Measure E := by volume_tac)
  body: s.indicator ((μ s)⁻¹ • (1 : E -> Real>=0∞)) x

中文:
定义 uniformPDF
  签名: (s : 集合 E) (x : E) (μ : 测度 E := by volume_tac)
  定义体: s.indicator ((μ s)⁻¹ • (1 : E -> Real>=0∞)) x

Depends on / 依赖: indicator, s.indicator, volume_tac
-/
def uniformPDF (s : Set E) (x : E) (μ : Measure E := by volume_tac) : Real>=0∞ :=
  s.indicator ((μ s)⁻¹ • (1 : E -> Real>=0∞)) x

/--
lemma `uniformPDF_eq_pdf` / 引理 `uniformPDF_eq_pdf`

English:
lemma uniformPDF_eq_pdf
  given: {s : Set E} (hs : MeasurableSet s) (hu : pdf.IsUniform X s ℙ μ)
  proof: (hu.pdf_eq hs).symm.trans (ae_eq_refl _)

中文:
引理 uniformPDF_eq_pdf
  条件: {s : 集合 E} (hs : 可测集 s) (hu : pdf.是一致 X s ℙ μ)
  证明: (hu.pdf_eq hs).symm.trans (ae_eq_refl _)

Depends on / 依赖: ae_eq_refl, hu.pdf_eq, pdf_eq, symm.trans
-/
lemma uniformPDF_eq_pdf {s : Set E} (hs : MeasurableSet s) (hu : pdf.IsUniform X s ℙ μ) :
    (fun x => uniformPDF s x μ) =ᵐ[μ] pdf X ℙ μ :=
  (hu.pdf_eq hs).symm.trans (ae_eq_refl _)

open scoped Classical in
/--
lemma `uniformPDF_ite` / 引理 `uniformPDF_ite`

English:
lemma uniformPDF_ite
  given: {s : Set E} {x : E}
  proof: by
  norm_num [uniformPDF, Set.indicator]

中文:
引理 uniformPDF_ite
  条件: {s : 集合 E} {x : E}
  证明: by
  norm_num [uniformPDF, Set.indicator]

Depends on / 依赖: Set.indicator, indicator, uniformPDF
-/
lemma uniformPDF_ite {s : Set E} {x : E} :
    uniformPDF s x μ = if x in s then (μ s)⁻¹ else 0 := by
  norm_num [uniformPDF, Set.indicator]

end pdf

end MeasureTheory

namespace PMF

variable {α : Type*}

open scoped NNReal ENNReal

section UniformOfFinset

/--
Definition of `uniformOfFinset` / `uniformOfFinset` 的定义

English:
definition uniformOfFinset
  signature: (s : Finset α) (hs : s.Nonempty)
  body: by
  classical
  refine ofFinset (fun a => if a in s then s.card⁻¹ else 0) s ?_ ?_
  · simp only [Finset.sum_ite_mem, Finset.inter_self, Finset.sum_const, nsmul_eq_mul]
    have : (s.card : Real>=0∞) != 0 := by
      simpa only [Ne, Nat.cast_eq_zero, Finset.card_eq_zero] using
        Finset.nonempt

中文:
定义 uniformOfFinset
  签名: (s : 有限集 α) (hs : s.非空)
  定义体: by
  classical
  refine ofFinset (fun a => if a in s then s.card⁻¹ else 0) s ?_ ?_
  · simp only [Finset.sum_ite_mem, Finset.inter_self, Finset.sum_const, nsmul_eq_mul]
    have : (s.card : Real>=0∞) != 0 := by
      simpa only [Ne, Nat.cast_eq_zero, Finset.card_eq_zero] using
        Finset.nonempt

Depends on / 依赖: ENNReal, ENNReal.mul_inv_cancel, ENNReal.natCast_ne_top, Finset, Finset.card_eq_zero, Finset.inter_self, Finset.nonempty_iff_ne_empty, Finset.sum_const, Finset.sum_ite_mem, Nat.cast_eq_zero, card_eq_zero, cast_eq_zero, classical, if_false, inter_self, mul_inv_cancel, natCast_ne_top, nonempty_iff_ne_empty, nsmul_eq_mul, ofFinset
-/
def uniformOfFinset (s : Finset α) (hs : s.Nonempty) : PMF α := by
  classical
  refine ofFinset (fun a => if a in s then s.card⁻¹ else 0) s ?_ ?_
  · simp only [Finset.sum_ite_mem, Finset.inter_self, Finset.sum_const, nsmul_eq_mul]
    have : (s.card : Real>=0∞) != 0 := by
      simpa only [Ne, Nat.cast_eq_zero, Finset.card_eq_zero] using
        Finset.nonempty_iff_ne_empty.1 hs
exact ENNReal.mul_inv_cancel this ENNReal.natCast_ne_top s.card
  · exact fun x hx => by simp only [hx, if_false]

variable {s : Finset α} (hs : s.Nonempty) {a : α}

open scoped Classical in
@[simp]
/--
theorem `uniformOfFinset_apply` / 定理 `uniformOfFinset_apply`

English:
theorem uniformOfFinset_apply
  given: (a : α)
  proof: rfl

中文:
定理 uniformOfFinset_apply
  条件: (a : α)
  证明: rfl
-/
theorem uniformOfFinset_apply (a : α) :
    uniformOfFinset s hs a = if a in s then (s.card : Real>=0∞)⁻¹ else 0 :=
  rfl

/--
theorem `uniformOfFinset_apply_of_mem` / 定理 `uniformOfFinset_apply_of_mem`

English:
theorem uniformOfFinset_apply_of_mem
  given: (ha : a in s)
  statement: uniformOfFinset s hs a = (s.card : Real>=0∞)⁻¹
  proof: by
  simp [ha]

中文:
定理 uniformOfFinset_apply_of_mem
  条件: (ha : a in s)
  结论: uniformOfFinset s hs a = (s.card : 实数>=0∞)⁻¹
  证明: by
  simp [ha]
-/
theorem uniformOfFinset_apply_of_mem (ha : a in s) : uniformOfFinset s hs a = (s.card : Real>=0∞)⁻¹ := by
  simp [ha]

/--
theorem `uniformOfFinset_apply_of_notMem` / 定理 `uniformOfFinset_apply_of_notMem`

English:
theorem uniformOfFinset_apply_of_notMem
  given: (ha : a ∉ s)
  statement: uniformOfFinset s hs a = 0
  proof: by simp [ha]

中文:
定理 uniformOfFinset_apply_of_notMem
  条件: (ha : a ∉ s)
  结论: uniformOfFinset s hs a = 0
  证明: by simp [ha]
-/
theorem uniformOfFinset_apply_of_notMem (ha : a ∉ s) : uniformOfFinset s hs a = 0 := by simp [ha]

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
theorem `support_uniformOfFinset` / 定理 `support_uniformOfFinset`

English:
theorem support_uniformOfFinset
  statement: (uniformOfFinset s hs).support = s
  proof: Set.ext
    (by
      let ⟨a, ha⟩ := hs
      simp [mem_support_iff])

中文:
定理 support_uniformOfFinset
  结论: (uniformOfFinset s hs).support = s
  证明: Set.ext
    (by
      let ⟨a, ha⟩ := hs
      simp [mem_support_iff])

Depends on / 依赖: Set.ext, mem_support_iff
-/
theorem support_uniformOfFinset : (uniformOfFinset s hs).support = s :=
  Set.ext
    (by
      let ⟨a, ha⟩ := hs
      simp [mem_support_iff])

/--
theorem `mem_support_uniformOfFinset_iff` / 定理 `mem_support_uniformOfFinset_iff`

English:
theorem mem_support_uniformOfFinset_iff
  given: (a : α)
  statement: a in (uniformOfFinset s hs).support ↔ a in s
  proof: by
  simp

中文:
定理 mem_support_uniformOfFinset_iff
  条件: (a : α)
  结论: a in (uniformOfFinset s hs).support ↔ a in s
  证明: by
  simp
-/
theorem mem_support_uniformOfFinset_iff (a : α) : a in (uniformOfFinset s hs).support ↔ a in s := by
  simp

section Measure

variable (t : Set α)

open scoped Classical in
@[simp]
/--
theorem `toOuterMeasure_uniformOfFinset_apply` / 定理 `toOuterMeasure_uniformOfFinset_apply`

English:
theorem toOuterMeasure_uniformOfFinset_apply
  proof: calc
    (uniformOfFinset s hs).toOuterMeasure t = ∑' x, if x in t then uniformOfFinset s hs x else 0 :=
      toOuterMeasure_apply (uniformOfFinset s hs) t
    _ = ∑' x, if x in s ∧ x in t then (#s : Real>=0∞)⁻¹ else 0 :=
      tsum_congr fun x => by simp_rw [uniformOfFinset_apply, ← ite_and, and_c

中文:
定理 toOuterMeasure_uniformOfFinset_apply
  证明: calc
    (uniformOfFinset s hs).toOuterMeasure t = ∑' x, if x in t then uniformOfFinset s hs x else 0 :=
      toOuterMeasure_apply (uniformOfFinset s hs) t
    _ = ∑' x, if x in s ∧ x in t then (#s : Real>=0∞)⁻¹ else 0 :=
      tsum_congr fun x => by simp_rw [uniformOfFinset_apply, ← ite_and, and_c

Depends on / 依赖: Finset, Finset.mem_filter, Finset.sum_congr, and_comm, if_neg, ite_and, mem_filter, simp_rw, sum_congr, toOuterMeasure, toOuterMeasure_apply, tsum_congr, tsum_eq_sum, uniformOfFinset, uniformOfFinset_apply
-/
theorem toOuterMeasure_uniformOfFinset_apply :
    (uniformOfFinset s hs).toOuterMeasure t = #{x in s | x in t} / #s :=
  calc
    (uniformOfFinset s hs).toOuterMeasure t = ∑' x, if x in t then uniformOfFinset s hs x else 0 :=
      toOuterMeasure_apply (uniformOfFinset s hs) t
    _ = ∑' x, if x in s ∧ x in t then (#s : Real>=0∞)⁻¹ else 0 :=
      tsum_congr fun x => by simp_rw [uniformOfFinset_apply, ← ite_and, and_comm]
    _ = ∑ x in s with x in t, if x in s ∧ x in t then (#s : Real>=0∞)⁻¹ else 0 :=
      tsum_eq_sum fun _ hx => if_neg fun h => hx (Finset.mem_filter.2 h)
    _ = ∑ x in s with x in t, (#s : Real>=0∞)⁻¹ :=
      Finset.sum_congr rfl fun x hx => by
        have : x in s ∧ x in t := by simpa using hx
        simp only [this, and_self_iff, if_true]
    _ = #{x in s | x in t} / #s := by
        simp only [div_eq_mul_inv, Finset.sum_const, nsmul_eq_mul]

open scoped Classical in
@[simp]
/--
theorem `toMeasure_uniformOfFinset_apply` / 定理 `toMeasure_uniformOfFinset_apply`

English:
theorem toMeasure_uniformOfFinset_apply
  given: [MeasurableSpace α] (ht : MeasurableSet t)
  proof: (toMeasure_apply_eq_toOuterMeasure_apply _ ht).trans (toOuterMeasure_uniformOfFinset_apply hs t)

中文:
定理 toMeasure_uniformOfFinset_apply
  条件: [可测空间 α] (ht : 可测集 t)
  证明: (toMeasure_apply_eq_toOuterMeasure_apply _ ht).trans (toOuterMeasure_uniformOfFinset_apply hs t)

Depends on / 依赖: toMeasure_apply_eq_toOuterMeasure_apply, toOuterMeasure_uniformOfFinset_apply
-/
theorem toMeasure_uniformOfFinset_apply [MeasurableSpace α] (ht : MeasurableSet t) :
    (uniformOfFinset s hs).toMeasure t = #{x in s | x in t} / #s :=
  (toMeasure_apply_eq_toOuterMeasure_apply _ ht).trans (toOuterMeasure_uniformOfFinset_apply hs t)

end Measure

end UniformOfFinset

section UniformOfFintype

/--
Definition of `uniformOfFintype` / `uniformOfFintype` 的定义

English:
definition uniformOfFintype
  signature: (α : Type*) [Fintype α] [Nonempty α]
  body: uniformOfFinset Finset.univ Finset.univ_nonempty

中文:
定义 uniformOfFintype
  签名: (α : 类型) [有限类型 α] [非空 α]
  定义体: uniformOfFinset Finset.univ Finset.univ_nonempty

Depends on / 依赖: Finset, Finset.univ, Finset.univ_nonempty, uniformOfFinset, univ_nonempty
-/
def uniformOfFintype (α : Type*) [Fintype α] [Nonempty α] : PMF α :=
  uniformOfFinset Finset.univ Finset.univ_nonempty

variable [Fintype α] [Nonempty α]

@[simp]
/--
theorem `uniformOfFintype_apply` / 定理 `uniformOfFintype_apply`

English:
theorem uniformOfFintype_apply
  given: (a : α)
  statement: uniformOfFintype α a = (Fintype.card α : Real>=0∞)⁻¹
  proof: by
  simp [uniformOfFintype, Finset.mem_univ, uniformOfFinset_apply]

@[simp]

中文:
定理 uniformOfFintype_apply
  条件: (a : α)
  结论: uniformOfFintype α a = (有限类型.card α : 实数>=0∞)⁻¹
  证明: by
  simp [uniformOfFintype, Finset.mem_univ, uniformOfFinset_apply]

@[simp]

Depends on / 依赖: Finset, Finset.mem_univ, mem_univ, uniformOfFinset_apply, uniformOfFintype
-/
theorem uniformOfFintype_apply (a : α) : uniformOfFintype α a = (Fintype.card α : Real>=0∞)⁻¹ := by
  simp [uniformOfFintype, Finset.mem_univ, uniformOfFinset_apply]

@[simp]
/--
theorem `support_uniformOfFintype` / 定理 `support_uniformOfFintype`

English:
theorem support_uniformOfFintype
  given: (α : Type*) [Fintype α] [Nonempty α]
  proof: Set.ext fun x => by simp [mem_support_iff]

中文:
定理 support_uniformOfFintype
  条件: (α : 类型) [有限类型 α] [非空 α]
  证明: Set.ext fun x => by simp [mem_support_iff]

Depends on / 依赖: Set.ext, mem_support_iff
-/
theorem support_uniformOfFintype (α : Type*) [Fintype α] [Nonempty α] :
    (uniformOfFintype α).support = ⊤ :=
  Set.ext fun x => by simp [mem_support_iff]

/--
theorem `mem_support_uniformOfFintype` / 定理 `mem_support_uniformOfFintype`

English:
theorem mem_support_uniformOfFintype
  given: (a : α)
  statement: a in (uniformOfFintype α).support
  proof: by simp

中文:
定理 mem_support_uniformOfFintype
  条件: (a : α)
  结论: a in (uniformOfFintype α).support
  证明: by simp
-/
theorem mem_support_uniformOfFintype (a : α) : a in (uniformOfFintype α).support := by simp

section Measure

variable (s : Set α)

/--
theorem `toOuterMeasure_uniformOfFintype_apply` / 定理 `toOuterMeasure_uniformOfFintype_apply`

English:
theorem toOuterMeasure_uniformOfFintype_apply
  given: [Fintype s]
  proof: by
  classical
  rw [uniformOfFintype]; rw [toOuterMeasure_uniformOfFinset_apply]; rw [Fintype.card_subtype]; rw [Finset.card_univ]

中文:
定理 toOuterMeasure_uniformOfFintype_apply
  条件: [有限类型 s]
  证明: by
  classical
  rw [uniformOfFintype]; rw [toOuterMeasure_uniformOfFinset_apply]; rw [Fintype.card_subtype]; rw [Finset.card_univ]

Depends on / 依赖: Finset, Finset.card_univ, Fintype, Fintype.card_subtype, card_subtype, card_univ, classical, toOuterMeasure_uniformOfFinset_apply, uniformOfFintype
-/
theorem toOuterMeasure_uniformOfFintype_apply [Fintype s] :
    (uniformOfFintype α).toOuterMeasure s = Fintype.card s / Fintype.card α := by
  classical
  rw [uniformOfFintype]; rw [toOuterMeasure_uniformOfFinset_apply]; rw [Fintype.card_subtype]; rw [Finset.card_univ]

/--
theorem `toMeasure_uniformOfFintype_apply` / 定理 `toMeasure_uniformOfFintype_apply`

English:
theorem toMeasure_uniformOfFintype_apply
  given: [MeasurableSpace α] (hs : MeasurableSet s) [Fintype s]
  proof: by
  classical
  simp [uniformOfFintype, Fintype.card_subtype, hs]

中文:
定理 toMeasure_uniformOfFintype_apply
  条件: [可测空间 α] (hs : 可测集 s) [有限类型 s]
  证明: by
  classical
  simp [uniformOfFintype, Fintype.card_subtype, hs]

Depends on / 依赖: Fintype, Fintype.card_subtype, card_subtype, classical, uniformOfFintype
-/
theorem toMeasure_uniformOfFintype_apply [MeasurableSpace α] (hs : MeasurableSet s) [Fintype s] :
    (uniformOfFintype α).toMeasure s = Fintype.card s / Fintype.card α := by
  classical
  simp [uniformOfFintype, Fintype.card_subtype, hs]

end Measure

end UniformOfFintype

section OfMultiset

open scoped Classical in
/--
Definition of `ofMultiset` / `ofMultiset` 的定义

English:
definition ofMultiset
  signature: (s : Multiset α) (hs : s != 0)
  body: ⟨fun a => s.count a / (Multiset.card s),
    ENNReal.summable.hasSum_iff.2
      (calc
        (∑' b : α, (s.count b : Real>=0∞) / (Multiset.card s))
          = (Multiset.card s : Real>=0∞)⁻¹ * ∑' b, (s.count b : Real>=0∞) := by
            simp_rw [ENNReal.div_eq_inv_mul, ENNReal.tsum_mul_left]
  

中文:
定义 ofMultiset
  签名: (s : Multiset α) (hs : s != 0)
  定义体: ⟨fun a => s.count a / (Multiset.card s),
    ENNReal.summable.hasSum_iff.2
      (calc
        (∑' b : α, (s.count b : Real>=0∞) / (Multiset.card s))
          = (Multiset.card s : Real>=0∞)⁻¹ * ∑' b, (s.count b : Real>=0∞) := by
            simp_rw [ENNReal.div_eq_inv_mul, ENNReal.tsum_mul_left]
  

Depends on / 依赖: ENNReal, ENNReal.div_eq_inv_mul, ENNReal.summable.hasSum_iff, ENNReal.tsum_mul_left, Multiset, Multiset.card, Multiset.count_eq_zero, Multiset.mem_toFinset, Nat.cast_eq_zero, cast_eq_zero, congr_arg, count_eq_zero, div_eq_inv_mul, hasSum_iff, mem_toFinset, s.count, s.toFinset, simp_rw, summable, toFinset
-/
def ofMultiset (s : Multiset α) (hs : s != 0) : PMF α :=
  ⟨fun a => s.count a / (Multiset.card s),
    ENNReal.summable.hasSum_iff.2
      (calc
        (∑' b : α, (s.count b : Real>=0∞) / (Multiset.card s))
          = (Multiset.card s : Real>=0∞)⁻¹ * ∑' b, (s.count b : Real>=0∞) := by
            simp_rw [ENNReal.div_eq_inv_mul, ENNReal.tsum_mul_left]
        _ = (Multiset.card s : Real>=0∞)⁻¹ * ∑ b in s.toFinset, (s.count b : Real>=0∞) :=
          (congr_arg (fun x => (Multiset.card s : Real>=0∞)⁻¹ * x)
            (tsum_eq_sum fun a ha =>
Nat.cast_eq_zero.2 by rwa [Multiset.count_eq_zero, ← Multiset.mem_toFinset]))
        _ = 1 := by
          rw [← Nat.cast_sum]; rw [Multiset.toFinset_sum_count_eq s]; rw [ENNReal.inv_mul_cancel (Nat.cast_ne_zero.2 (hs ∘ Multiset.card_eq_zero.1))
              (ENNReal.natCast_ne_top _)]
        )⟩

variable {s : Multiset α} (hs : s != 0)

open scoped Classical in
@[simp]
/--
theorem `ofMultiset_apply` / 定理 `ofMultiset_apply`

English:
theorem ofMultiset_apply
  given: (a : α)
  statement: ofMultiset s hs a = s.count a / (Multiset.card s)
  proof: rfl

中文:
定理 ofMultiset_apply
  条件: (a : α)
  结论: ofMultiset s hs a = s.count a / (Multiset.card s)
  证明: rfl
-/
theorem ofMultiset_apply (a : α) : ofMultiset s hs a = s.count a / (Multiset.card s) :=
  rfl

open scoped Classical in
@[simp]
/--
theorem `support_ofMultiset` / 定理 `support_ofMultiset`

English:
theorem support_ofMultiset
  statement: (ofMultiset s hs).support = s.toFinset
  proof: Set.ext (by simp [mem_support_iff])

中文:
定理 support_ofMultiset
  结论: (ofMultiset s hs).support = s.toFinset
  证明: Set.ext (by simp [mem_support_iff])

Depends on / 依赖: Set.ext, mem_support_iff
-/
theorem support_ofMultiset : (ofMultiset s hs).support = s.toFinset :=
  Set.ext (by simp [mem_support_iff])

open scoped Classical in
/--
theorem `mem_support_ofMultiset_iff` / 定理 `mem_support_ofMultiset_iff`

English:
theorem mem_support_ofMultiset_iff
  given: (a : α)
  statement: a in (ofMultiset s hs).support ↔ a in s.toFinset
  proof: by
  simp

中文:
定理 mem_support_ofMultiset_iff
  条件: (a : α)
  结论: a in (ofMultiset s hs).support ↔ a in s.toFinset
  证明: by
  simp
-/
theorem mem_support_ofMultiset_iff (a : α) : a in (ofMultiset s hs).support ↔ a in s.toFinset := by
  simp

/--
theorem `ofMultiset_apply_of_notMem` / 定理 `ofMultiset_apply_of_notMem`

English:
theorem ofMultiset_apply_of_notMem
  given: {a : α} (ha : a ∉ s)
  statement: ofMultiset s hs a = 0
  proof: by
  simpa only [ofMultiset_apply, ENNReal.div_eq_zero_iff, Nat.cast_eq_zero, Multiset.count_eq_zero,
    ENNReal.natCast_ne_top, or_false] using ha

中文:
定理 ofMultiset_apply_of_notMem
  条件: {a : α} (ha : a ∉ s)
  结论: ofMultiset s hs a = 0
  证明: by
  simpa only [ofMultiset_apply, ENNReal.div_eq_zero_iff, Nat.cast_eq_zero, Multiset.count_eq_zero,
    ENNReal.natCast_ne_top, or_false] using ha

Depends on / 依赖: ENNReal, ENNReal.div_eq_zero_iff, ENNReal.natCast_ne_top, Multiset, Multiset.count_eq_zero, Nat.cast_eq_zero, cast_eq_zero, count_eq_zero, div_eq_zero_iff, natCast_ne_top, ofMultiset_apply, or_false
-/
theorem ofMultiset_apply_of_notMem {a : α} (ha : a ∉ s) : ofMultiset s hs a = 0 := by
  simpa only [ofMultiset_apply, ENNReal.div_eq_zero_iff, Nat.cast_eq_zero, Multiset.count_eq_zero,
    ENNReal.natCast_ne_top, or_false] using ha

section Measure

variable (t : Set α)

open scoped Classical in
@[simp]
/--
theorem `toOuterMeasure_ofMultiset_apply` / 定理 `toOuterMeasure_ofMultiset_apply`

English:
theorem toOuterMeasure_ofMultiset_apply
  proof: by
  simp_rw [div_eq_mul_inv, ← ENNReal.tsum_mul_right, toOuterMeasure_apply]
  refine tsum_congr fun x => ?_
  by_cases hx : x in t <;> simp [Set.indicator, hx, div_eq_mul_inv]

中文:
定理 toOuterMeasure_ofMultiset_apply
  证明: by
  simp_rw [div_eq_mul_inv, ← ENNReal.tsum_mul_right, toOuterMeasure_apply]
  refine tsum_congr fun x => ?_
  by_cases hx : x in t <;> simp [Set.indicator, hx, div_eq_mul_inv]

Depends on / 依赖: ENNReal, ENNReal.tsum_mul_right, Set.indicator, div_eq_mul_inv, indicator, simp_rw, toOuterMeasure_apply, tsum_congr, tsum_mul_right
-/
theorem toOuterMeasure_ofMultiset_apply :
    (ofMultiset s hs).toOuterMeasure t =
      (∑' x, (s.filter (· in t)).count x : Real>=0∞) / (Multiset.card s) := by
  simp_rw [div_eq_mul_inv, ← ENNReal.tsum_mul_right, toOuterMeasure_apply]
  refine tsum_congr fun x => ?_
  by_cases hx : x in t <;> simp [Set.indicator, hx, div_eq_mul_inv]

open scoped Classical in
@[simp]
/--
theorem `toMeasure_ofMultiset_apply` / 定理 `toMeasure_ofMultiset_apply`

English:
theorem toMeasure_ofMultiset_apply
  given: [MeasurableSpace α] (ht : MeasurableSet t)
  proof: (toMeasure_apply_eq_toOuterMeasure_apply _ ht).trans (toOuterMeasure_ofMultiset_apply hs t)

中文:
定理 toMeasure_ofMultiset_apply
  条件: [可测空间 α] (ht : 可测集 t)
  证明: (toMeasure_apply_eq_toOuterMeasure_apply _ ht).trans (toOuterMeasure_ofMultiset_apply hs t)

Depends on / 依赖: toMeasure_apply_eq_toOuterMeasure_apply, toOuterMeasure_ofMultiset_apply
-/
theorem toMeasure_ofMultiset_apply [MeasurableSpace α] (ht : MeasurableSet t) :
    (ofMultiset s hs).toMeasure t = (∑' x, (s.filter (· in t)).count x : Real>=0∞) / (Multiset.card s) :=
  (toMeasure_apply_eq_toOuterMeasure_apply _ ht).trans (toOuterMeasure_ofMultiset_apply hs t)

end Measure

end OfMultiset

end PMF
