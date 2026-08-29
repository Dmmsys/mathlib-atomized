/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

/-!
# Lp seminorm with respect to trimmed measure

In this file we prove basic properties of the Lp-seminorm of a function
with respect to the restriction of a measure to a sub-σ-algebra.
-/

public section

namespace MeasureTheory

open Filter
open scoped ENNReal

variable {α E ε : Type*} {m m0 : MeasurableSpace α} {p : Real>=0∞} {q : Real} {μ : Measure α}
  [NormedAddCommGroup E] [TopologicalSpace ε] [ContinuousENorm ε]

/--
theorem `eLpNorm'_trim` / 定理 `eLpNorm'_trim`

English:
theorem eLpNorm'_trim
  given: (hm : m <= m0) {f : α -> ε} (hf : StronglyMeasurable[m] f)
  proof: by
  simp_rw [eLpNorm']
  congr 1
  exact lintegral_trim hm (by fun_prop)

中文:
定理 eLpNorm'_trim
  条件: (hm : m <= m0) {f : α -> ε} (hf : StronglyMeasurable[m] f)
  证明: by
  simp_rw [eLpNorm']
  congr 1
  exact lintegral_trim hm (by fun_prop)
-/
theorem eLpNorm'_trim (hm : m <= m0) {f : α -> ε} (hf : StronglyMeasurable[m] f) :
    eLpNorm' f q (μ.trim hm) = eLpNorm' f q μ := by
  simp_rw [eLpNorm']
  congr 1
  exact lintegral_trim hm (by fun_prop)

/--
theorem `limsup_trim` / 定理 `limsup_trim`

English:
theorem limsup_trim
  given: (hm : m <= m0) {f : α -> Real>=0∞} (hf : Measurable[m] f)
  proof: by
  simp_rw [limsup_eq]
  suffices h_set_eq : { a : Real>=0∞ | forallᵐ n ∂μ.trim hm, f n <= a } = { a : Real>=0∞ | forallᵐ n ∂μ, f n <= a } by
    rw [h_set_eq]
  ext1 a
  suffices h_meas_eq : μ { x | ¬f x <= a } = μ.trim hm { x | ¬f x <= a } by
    simp_rw [Set.mem_ofPred_eq, ae_iff, h_meas_eq]
  

中文:
定理 limsup_trim
  条件: (hm : m <= m0) {f : α -> 实数>=0∞} (hf : 可测[m] f)
  证明: by
  simp_rw [limsup_eq]
  suffices h_set_eq : { a : Real>=0∞ | forallᵐ n ∂μ.trim hm, f n <= a } = { a : Real>=0∞ | forallᵐ n ∂μ, f n <= a } by
    rw [h_set_eq]
  ext1 a
  suffices h_meas_eq : μ { x | ¬f x <= a } = μ.trim hm { x | ¬f x <= a } by
    simp_rw [Set.mem_ofPred_eq, ae_iff, h_meas_eq]
  

Depends on / 依赖: Set.mem_ofPred_eq, ae_iff, h_meas_eq, h_set_eq, limsup_eq, measurableSet_le, measurable_const, mem_ofPred_eq, simp_rw, trim_measurableSet_eq
-/
theorem limsup_trim (hm : m <= m0) {f : α -> Real>=0∞} (hf : Measurable[m] f) :
    limsup f (ae (μ.trim hm)) = limsup f (ae μ) := by
  simp_rw [limsup_eq]
  suffices h_set_eq : { a : Real>=0∞ | forallᵐ n ∂μ.trim hm, f n <= a } = { a : Real>=0∞ | forallᵐ n ∂μ, f n <= a } by
    rw [h_set_eq]
  ext1 a
  suffices h_meas_eq : μ { x | ¬f x <= a } = μ.trim hm { x | ¬f x <= a } by
    simp_rw [Set.mem_ofPred_eq, ae_iff, h_meas_eq]
  refine (trim_measurableSet_eq hm ?_).symm
  exact (measurableSet_le hf measurable_const).compl

/--
theorem `essSup_trim` / 定理 `essSup_trim`

English:
theorem essSup_trim
  given: (hm : m <= m0) {f : α -> Real>=0∞} (hf : Measurable[m] f)
  proof: by
  simp_rw [essSup]
  exact limsup_trim hm hf

中文:
定理 essSup_trim
  条件: (hm : m <= m0) {f : α -> 实数>=0∞} (hf : 可测[m] f)
  证明: by
  simp_rw [essSup]
  exact limsup_trim hm hf

Depends on / 依赖: essSup, limsup_trim, simp_rw
-/
theorem essSup_trim (hm : m <= m0) {f : α -> Real>=0∞} (hf : Measurable[m] f) :
    essSup f (μ.trim hm) = essSup f μ := by
  simp_rw [essSup]
  exact limsup_trim hm hf

/--
theorem `eLpNormEssSup_trim` / 定理 `eLpNormEssSup_trim`

English:
theorem eLpNormEssSup_trim
  given: (hm : m <= m0) {f : α -> ε} (hf : StronglyMeasurable[m] f)
  proof: essSup_trim _ (@StronglyMeasurable.enorm _ m _ _ _ _ hf)

中文:
定理 eLpNormEssSup_trim
  条件: (hm : m <= m0) {f : α -> ε} (hf : StronglyMeasurable[m] f)
  证明: essSup_trim _ (@StronglyMeasurable.enorm _ m _ _ _ _ hf)

Depends on / 依赖: StronglyMeasurable, StronglyMeasurable.enorm, essSup_trim
-/
theorem eLpNormEssSup_trim (hm : m <= m0) {f : α -> ε} (hf : StronglyMeasurable[m] f) :
    eLpNormEssSup f (μ.trim hm) = eLpNormEssSup f μ :=
  essSup_trim _ (@StronglyMeasurable.enorm _ m _ _ _ _ hf)

/--
theorem `eLpNorm_trim` / 定理 `eLpNorm_trim`

English:
theorem eLpNorm_trim
  given: (hm : m <= m0) {f : α -> ε} (hf : StronglyMeasurable[m] f)
  proof: by
  by_cases h0 : p = 0
  · simp [h0]
  by_cases h_top : p = ∞
  · simpa only [h_top, eLpNorm_exponent_top] using eLpNormEssSup_trim hm hf
  simpa only [eLpNorm_eq_eLpNorm' h0 h_top] using eLpNorm'_trim hm hf

中文:
定理 eLpNorm_trim
  条件: (hm : m <= m0) {f : α -> ε} (hf : StronglyMeasurable[m] f)
  证明: by
  by_cases h0 : p = 0
  · simp [h0]
  by_cases h_top : p = ∞
  · simpa only [h_top, eLpNorm_exponent_top] using eLpNormEssSup_trim hm hf
  simpa only [eLpNorm_eq_eLpNorm' h0 h_top] using eLpNorm'_trim hm hf

Depends on / 依赖: _trim, eLpNorm, eLpNormEssSup_trim, eLpNorm_eq_eLpNorm, eLpNorm_exponent_top, h_top
-/
theorem eLpNorm_trim (hm : m <= m0) {f : α -> ε} (hf : StronglyMeasurable[m] f) :
    eLpNorm f p (μ.trim hm) = eLpNorm f p μ := by
  by_cases h0 : p = 0
  · simp [h0]
  by_cases h_top : p = ∞
  · simpa only [h_top, eLpNorm_exponent_top] using eLpNormEssSup_trim hm hf
  simpa only [eLpNorm_eq_eLpNorm' h0 h_top] using eLpNorm'_trim hm hf

/--
theorem `eLpNorm_trim_ae` / 定理 `eLpNorm_trim_ae`

English:
theorem eLpNorm_trim_ae
  given: (hm : m <= m0) {f : α -> ε} (hf : AEStronglyMeasurable[m] f (μ.trim hm))
  proof: by
  rw [eLpNorm_congr_ae hf.ae_eq_mk]; rw [eLpNorm_congr_ae (ae_eq_of_ae_eq_trim hf.ae_eq_mk)]
  exact eLpNorm_trim hm hf.stronglyMeasurable_mk

中文:
定理 eLpNorm_trim_ae
  条件: (hm : m <= m0) {f : α -> ε} (hf : AEStronglyMeasurable[m] f (μ.trim hm))
  证明: by
  rw [eLpNorm_congr_ae hf.ae_eq_mk]; rw [eLpNorm_congr_ae (ae_eq_of_ae_eq_trim hf.ae_eq_mk)]
  exact eLpNorm_trim hm hf.stronglyMeasurable_mk

Depends on / 依赖: ae_eq_mk, ae_eq_of_ae_eq_trim, eLpNorm_congr_ae, eLpNorm_trim, hf.ae_eq_mk, hf.stronglyMeasurable_mk, stronglyMeasurable_mk
-/
theorem eLpNorm_trim_ae (hm : m <= m0) {f : α -> ε} (hf : AEStronglyMeasurable[m] f (μ.trim hm)) :
    eLpNorm f p (μ.trim hm) = eLpNorm f p μ := by
  rw [eLpNorm_congr_ae hf.ae_eq_mk]; rw [eLpNorm_congr_ae (ae_eq_of_ae_eq_trim hf.ae_eq_mk)]
  exact eLpNorm_trim hm hf.stronglyMeasurable_mk

/--
theorem `memLp_of_memLp_trim` / 定理 `memLp_of_memLp_trim`

English:
theorem memLp_of_memLp_trim
  given: (hm : m <= m0) {f : α -> ε} (hf : MemLp f p (μ.trim hm))
  statement: MemLp f p μ
  proof: ⟨aestronglyMeasurable_of_aestronglyMeasurable_trim hm hf.1,
    (le_of_eq (eLpNorm_trim_ae hm hf.1).symm).trans_lt hf.2⟩

中文:
定理 memLp_of_memLp_trim
  条件: (hm : m <= m0) {f : α -> ε} (hf : MemLp f p (μ.trim hm))
  结论: MemLp f p μ
  证明: ⟨aestronglyMeasurable_of_aestronglyMeasurable_trim hm hf.1,
    (le_of_eq (eLpNorm_trim_ae hm hf.1).symm).trans_lt hf.2⟩

Depends on / 依赖: aestronglyMeasurable_of_aestronglyMeasurable_trim, eLpNorm_trim_ae, le_of_eq, trans_lt
-/
theorem memLp_of_memLp_trim (hm : m <= m0) {f : α -> ε} (hf : MemLp f p (μ.trim hm)) : MemLp f p μ :=
  ⟨aestronglyMeasurable_of_aestronglyMeasurable_trim hm hf.1,
    (le_of_eq (eLpNorm_trim_ae hm hf.1).symm).trans_lt hf.2⟩

end MeasureTheory
