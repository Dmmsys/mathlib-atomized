/-
Copyright (c) 2020 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Sébastien Gouëzel
-/
module

public import Mathlib.Data.Fintype.Order
public import Mathlib.MeasureTheory.Function.AEEqFun
public import Mathlib.MeasureTheory.Function.LpSeminorm.Defs
public import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

/-!
# Basic theorems about ℒp space
-/

public section
noncomputable section

open TopologicalSpace MeasureTheory Filter

open scoped NNReal ENNReal Topology ComplexConjugate

variable {α ε ε' E F G : Type*} {m m0 : MeasurableSpace α} {p : Real>=0∞} {q : Real} {μ ν : Measure α}
  [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedAddCommGroup G] [ENorm ε] [ENorm ε']

namespace MeasureTheory

section Lp

section Top

/--
theorem `MemLp.eLpNorm_lt_top` / 定理 `MemLp.eLpNorm_lt_top`

English:
theorem MemLp.eLpNorm_lt_top
  given: [TopologicalSpace ε] {f : α -> ε} (hfp : MemLp f p μ)
  proof: hfp.2

@[aesop (rule_sets := [finiteness]) unsafe 95% apply]

中文:
定理 MemLp.eLpNorm_lt_top
  条件: [拓扑空间 ε] {f : α -> ε} (hfp : MemLp f p μ)
  证明: hfp.2

@[aesop (rule_sets := [finiteness]) unsafe 95% apply]
-/
theorem MemLp.eLpNorm_lt_top [TopologicalSpace ε] {f : α -> ε} (hfp : MemLp f p μ) :
    eLpNorm f p μ < ∞ :=
  hfp.2

@[aesop (rule_sets := [finiteness]) unsafe 95% apply]
/--
theorem `MemLp.eLpNorm_ne_top` / 定理 `MemLp.eLpNorm_ne_top`

English:
theorem MemLp.eLpNorm_ne_top
  given: [TopologicalSpace ε] {f : α -> ε} (hfp : MemLp f p μ)
  proof: hfp.2.ne

中文:
定理 MemLp.eLpNorm_ne_top
  条件: [拓扑空间 ε] {f : α -> ε} (hfp : MemLp f p μ)
  证明: hfp.2.ne
-/
theorem MemLp.eLpNorm_ne_top [TopologicalSpace ε] {f : α -> ε} (hfp : MemLp f p μ) :
    eLpNorm f p μ != ∞ :=
  hfp.2.ne

/--
theorem `lintegral_rpow_enorm_lt_top_of_eLpNorm'_lt_top` / 定理 `lintegral_rpow_enorm_lt_top_of_eLpNorm'_lt_top`

English:
theorem lintegral_rpow_enorm_lt_top_of_eLpNorm'_lt_top
  statement: {f : α -> ε} (hq0_lt : 0 < q)
  proof: by
  rw [lintegral_rpow_enorm_eq_rpow_eLpNorm' hq0_lt]
  exact ENNReal.rpow_lt_top_of_nonneg (le_of_lt hq0_lt) (ne_of_lt hfq)

中文:
定理 lintegral_rpow_enorm_lt_top_of_eLpNorm'_lt_top
  结论: {f : α -> ε} (hq0_lt : 0 < q)
  证明: by
  rw [lintegral_rpow_enorm_eq_rpow_eLpNorm' hq0_lt]
  exact ENNReal.rpow_lt_top_of_nonneg (le_of_lt hq0_lt) (ne_of_lt hfq)

Depends on / 依赖: ENNReal, ENNReal.rpow_lt_top_of_nonneg, hq0_lt, le_of_lt, lintegral_rpow_enorm_eq_rpow_eLpNorm, ne_of_lt, rpow_lt_top_of_nonneg
-/
theorem lintegral_rpow_enorm_lt_top_of_eLpNorm'_lt_top {f : α -> ε} (hq0_lt : 0 < q)
    (hfq : eLpNorm' f q μ < ∞) : ∫⁻ a, ‖f a‖ₑ ^ q ∂μ < ∞ := by
  rw [lintegral_rpow_enorm_eq_rpow_eLpNorm' hq0_lt]
  exact ENNReal.rpow_lt_top_of_nonneg (le_of_lt hq0_lt) (ne_of_lt hfq)

/--
theorem `lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top` / 定理 `lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top`

English:
theorem lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top
  statement: {f : α -> ε} (hp_ne_zero : p != 0)
  proof: by
  apply lintegral_rpow_enorm_lt_top_of_eLpNorm'_lt_top
  · exact ENNReal.toReal_pos hp_ne_zero hp_ne_top
  · simpa [eLpNorm_eq_eLpNorm' hp_ne_zero hp_ne_top] using hfp

中文:
定理 lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top
  结论: {f : α -> ε} (hp_ne_zero : p != 0)
  证明: by
  apply lintegral_rpow_enorm_lt_top_of_eLpNorm'_lt_top
  · exact ENNReal.toReal_pos hp_ne_zero hp_ne_top
  · simpa [eLpNorm_eq_eLpNorm' hp_ne_zero hp_ne_top] using hfp

Depends on / 依赖: ENNReal, ENNReal.toReal_pos, _lt_top, eLpNorm_eq_eLpNorm, hp_ne_top, hp_ne_zero, lintegral_rpow_enorm_lt_top_of_eLpNorm, toReal_pos
-/
theorem lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top {f : α -> ε} (hp_ne_zero : p != 0)
    (hp_ne_top : p != ∞) (hfp : eLpNorm f p μ < ∞) : ∫⁻ a, ‖f a‖ₑ ^ p.toReal ∂μ < ∞ := by
  apply lintegral_rpow_enorm_lt_top_of_eLpNorm'_lt_top
  · exact ENNReal.toReal_pos hp_ne_zero hp_ne_top
  · simpa [eLpNorm_eq_eLpNorm' hp_ne_zero hp_ne_top] using hfp

/--
theorem `eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top` / 定理 `eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top`

English:
theorem eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top
  statement: {f : α -> ε} (hp_ne_zero : p != 0)
  proof: ⟨lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top hp_ne_zero hp_ne_top, by
    intro h
    have hp' := ENNReal.toReal_pos hp_ne_zero hp_ne_top
    have : 0 < 1 / p.toReal := div_pos zero_lt_one hp'
    simpa [eLpNorm_eq_lintegral_rpow_enorm_toReal hp_ne_zero hp_ne_top] using
      ENNReal.rpow_lt_top_of_nonneg (le_of_lt this) (ne_of_lt h)⟩

中文:
定理 eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top
  结论: {f : α -> ε} (hp_ne_zero : p != 0)
  证明: ⟨lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top hp_ne_zero hp_ne_top, by
    intro h
    have hp' := ENNReal.toReal_pos hp_ne_zero hp_ne_top
    have : 0 < 1 / p.toReal := div_pos zero_lt_one hp'
    simpa [eLpNorm_eq_lintegral_rpow_enorm_toReal hp_ne_zero hp_ne_top] using
      ENNReal.rpow_lt_top_of_nonneg (le_of_lt this) (ne_of_lt h)⟩

Depends on / 依赖: ENNReal, ENNReal.rpow_lt_top_of_nonneg, ENNReal.toReal_pos, div_pos, eLpNorm_eq_lintegral_rpow_enorm_toReal, hp_ne_top, hp_ne_zero, le_of_lt, lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top, ne_of_lt, p.toReal, rpow_lt_top_of_nonneg, toReal, toReal_pos, zero_lt_one
-/
theorem eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top {f : α -> ε} (hp_ne_zero : p != 0)
    (hp_ne_top : p != ∞) : eLpNorm f p μ < ∞ ↔ ∫⁻ a, (‖f a‖ₑ) ^ p.toReal ∂μ < ∞ :=
  ⟨lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top hp_ne_zero hp_ne_top, by
    intro h
    have hp' := ENNReal.toReal_pos hp_ne_zero hp_ne_top
    have : 0 < 1 / p.toReal := div_pos zero_lt_one hp'
    simpa [eLpNorm_eq_lintegral_rpow_enorm_toReal hp_ne_zero hp_ne_top] using
      ENNReal.rpow_lt_top_of_nonneg (le_of_lt this) (ne_of_lt h)⟩

end Top

section Zero

@[simp]
/--
theorem `eLpNorm'_exponent_zero` / 定理 `eLpNorm'_exponent_zero`

English:
theorem eLpNorm'_exponent_zero
  given: {f : α -> ε}
  statement: eLpNorm' f 0 μ = 1
  proof: by
  rw [eLpNorm']; rw [div_zero]; rw [ENNReal.rpow_zero]

@[simp]

中文:
定理 eLpNorm'_exponent_zero
  条件: {f : α -> ε}
  结论: eLpNorm' f 0 μ = 1
  证明: by
  rw [eLpNorm']; rw [div_zero]; rw [ENNReal.rpow_zero]

@[simp]

Depends on / 依赖: ENNReal, ENNReal.rpow_zero, div_zero, eLpNorm, rpow_zero
-/
theorem eLpNorm'_exponent_zero {f : α -> ε} : eLpNorm' f 0 μ = 1 := by
  rw [eLpNorm']; rw [div_zero]; rw [ENNReal.rpow_zero]

@[simp]
/--
theorem `eLpNorm_exponent_zero` / 定理 `eLpNorm_exponent_zero`

English:
theorem eLpNorm_exponent_zero
  given: {f : α -> ε}
  statement: eLpNorm f 0 μ = 0
  proof: by simp [eLpNorm]

@[simp]

中文:
定理 eLpNorm_exponent_zero
  条件: {f : α -> ε}
  结论: eLpNorm f 0 μ = 0
  证明: by simp [eLpNorm]

@[simp]

Depends on / 依赖: eLpNorm
-/
theorem eLpNorm_exponent_zero {f : α -> ε} : eLpNorm f 0 μ = 0 := by simp [eLpNorm]

@[simp]
/--
theorem `memLp_zero_iff_aestronglyMeasurable` / 定理 `memLp_zero_iff_aestronglyMeasurable`

English:
theorem memLp_zero_iff_aestronglyMeasurable
  given: [TopologicalSpace ε] {f : α -> ε}
  proof: by simp [MemLp, eLpNorm_exponent_zero]

中文:
定理 memLp_zero_iff_aestronglyMeasurable
  条件: [拓扑空间 ε] {f : α -> ε}
  证明: by simp [MemLp, eLpNorm_exponent_zero]

Depends on / 依赖: eLpNorm_exponent_zero
-/
theorem memLp_zero_iff_aestronglyMeasurable [TopologicalSpace ε] {f : α -> ε} :
    MemLp f 0 μ ↔ AEStronglyMeasurable f μ := by simp [MemLp, eLpNorm_exponent_zero]

section ESeminormedAddMonoid

variable {ε : Type*} [TopologicalSpace ε] [ESeminormedAddMonoid ε]

@[simp]
/--
theorem `eLpNorm'_zero` / 定理 `eLpNorm'_zero`

English:
theorem eLpNorm'_zero
  given: (hp0_lt : 0 < q)
  statement: eLpNorm' (0 : α -> ε) q μ = 0
  proof: by
  simp [eLpNorm'_eq_lintegral_enorm, hp0_lt]

@[simp]

中文:
定理 eLpNorm'_zero
  条件: (hp0_lt : 0 < q)
  结论: eLpNorm' (0 : α -> ε) q μ = 0
  证明: by
  simp [eLpNorm'_eq_lintegral_enorm, hp0_lt]

@[simp]
-/
theorem eLpNorm'_zero (hp0_lt : 0 < q) : eLpNorm' (0 : α -> ε) q μ = 0 := by
  simp [eLpNorm'_eq_lintegral_enorm, hp0_lt]

@[simp]
/--
theorem `eLpNorm'_zero'` / 定理 `eLpNorm'_zero'`

English:
theorem eLpNorm'_zero'
  given: (hq0_ne : q != 0) (hμ : μ != 0)
  statement: eLpNorm' (0 : α -> ε) q μ = 0
  proof: by
  rcases le_or_gt 0 q with hq0 | hq_neg
  · exact eLpNorm'_zero (lt_of_le_of_ne hq0 hq0_ne.symm)
  · simp [eLpNorm'_eq_lintegral_enorm, hμ, hq_neg]

@[simp]

中文:
定理 eLpNorm'_zero'
  条件: (hq0_ne : q != 0) (hμ : μ != 0)
  结论: eLpNorm' (0 : α -> ε) q μ = 0
  证明: by
  rcases le_or_gt 0 q with hq0 | hq_neg
  · exact eLpNorm'_zero (lt_of_le_of_ne hq0 hq0_ne.symm)
  · simp [eLpNorm'_eq_lintegral_enorm, hμ, hq_neg]

@[simp]
-/
theorem eLpNorm'_zero' (hq0_ne : q != 0) (hμ : μ != 0) : eLpNorm' (0 : α -> ε) q μ = 0 := by
  rcases le_or_gt 0 q with hq0 | hq_neg
  · exact eLpNorm'_zero (lt_of_le_of_ne hq0 hq0_ne.symm)
  · simp [eLpNorm'_eq_lintegral_enorm, hμ, hq_neg]

@[simp]
/--
theorem `eLpNormEssSup_zero` / 定理 `eLpNormEssSup_zero`

English:
theorem eLpNormEssSup_zero
  statement: eLpNormEssSup (0 : α -> ε) μ = 0
  proof: by
  simp [eLpNormEssSup, ← bot_eq_zero', essSup_const_bot]

@[simp]

中文:
定理 eLpNormEssSup_zero
  结论: eLpNormEssSup (0 : α -> ε) μ = 0
  证明: by
  simp [eLpNormEssSup, ← bot_eq_zero', essSup_const_bot]

@[simp]

Depends on / 依赖: bot_eq_zero, eLpNormEssSup, essSup_const_bot
-/
theorem eLpNormEssSup_zero : eLpNormEssSup (0 : α -> ε) μ = 0 := by
  simp [eLpNormEssSup, ← bot_eq_zero', essSup_const_bot]

@[simp]
/--
theorem `eLpNorm_zero` / 定理 `eLpNorm_zero`

English:
theorem eLpNorm_zero
  statement: eLpNorm (0 : α -> ε) p μ = 0
  proof: by
  by_cases h0 : p = 0
  · simp [h0]
  by_cases h_top : p = ∞
  · simp only [h_top, eLpNorm_exponent_top, eLpNormEssSup_zero]
  rw [← Ne] at h0
  simp [eLpNorm_eq_eLpNorm' h0 h_top, ENNReal.toReal_pos h0 h_top]

@[simp]

中文:
定理 eLpNorm_zero
  结论: eLpNorm (0 : α -> ε) p μ = 0
  证明: by
  by_cases h0 : p = 0
  · simp [h0]
  by_cases h_top : p = ∞
  · simp only [h_top, eLpNorm_exponent_top, eLpNormEssSup_zero]
  rw [← Ne] at h0
  simp [eLpNorm_eq_eLpNorm' h0 h_top, ENNReal.toReal_pos h0 h_top]

@[simp]

Depends on / 依赖: ENNReal, ENNReal.toReal_pos, eLpNormEssSup_zero, eLpNorm_eq_eLpNorm, eLpNorm_exponent_top, h_top, toReal_pos
-/
theorem eLpNorm_zero : eLpNorm (0 : α -> ε) p μ = 0 := by
  by_cases h0 : p = 0
  · simp [h0]
  by_cases h_top : p = ∞
  · simp only [h_top, eLpNorm_exponent_top, eLpNormEssSup_zero]
  rw [← Ne] at h0
  simp [eLpNorm_eq_eLpNorm' h0 h_top, ENNReal.toReal_pos h0 h_top]

@[simp]
/--
theorem `eLpNorm_zero'` / 定理 `eLpNorm_zero'`

English:
theorem eLpNorm_zero'
  statement: eLpNorm (fun _ : α => (0 : ε)) p μ = 0
  proof: eLpNorm_zero

中文:
定理 eLpNorm_zero'
  结论: eLpNorm (fun _ : α => (0 : ε)) p μ = 0
  证明: eLpNorm_zero

Depends on / 依赖: eLpNorm_zero
-/
theorem eLpNorm_zero' : eLpNorm (fun _ : α => (0 : ε)) p μ = 0 := eLpNorm_zero

/--
lemma `MemLp.zero` / 引理 `MemLp.zero`

English:
lemma MemLp.zero
  statement: MemLp (0 : α -> ε) p μ
  proof: ⟨aestronglyMeasurable_zero, by rw [eLpNorm_zero]; exact ENNReal.coe_lt_top⟩

中文:
引理 MemLp.zero
  结论: MemLp (0 : α -> ε) p μ
  证明: ⟨aestronglyMeasurable_zero, by rw [eLpNorm_zero]; exact ENNReal.coe_lt_top⟩
-/
@[simp] lemma MemLp.zero : MemLp (0 : α -> ε) p μ :=
  ⟨aestronglyMeasurable_zero, by rw [eLpNorm_zero]; exact ENNReal.coe_lt_top⟩

/--
lemma `MemLp.zero'` / 引理 `MemLp.zero'`

English:
lemma MemLp.zero'
  statement: MemLp (fun _ : α => (0 : ε)) p μ
  proof: MemLp.zero

中文:
引理 MemLp.zero'
  结论: MemLp (fun _ : α => (0 : ε)) p μ
  证明: MemLp.zero
-/
@[simp] lemma MemLp.zero' : MemLp (fun _ : α => (0 : ε)) p μ := MemLp.zero

variable [MeasurableSpace α]

/--
theorem `eLpNorm'_measure_zero_of_pos` / 定理 `eLpNorm'_measure_zero_of_pos`

English:
theorem eLpNorm'_measure_zero_of_pos
  given: {f : α -> ε} (hq_pos : 0 < q)
  proof: by simp [eLpNorm', hq_pos]

中文:
定理 eLpNorm'_measure_zero_of_pos
  条件: {f : α -> ε} (hq_pos : 0 < q)
  证明: by simp [eLpNorm', hq_pos]
-/
theorem eLpNorm'_measure_zero_of_pos {f : α -> ε} (hq_pos : 0 < q) :
    eLpNorm' f q (0 : Measure α) = 0 := by simp [eLpNorm', hq_pos]

/--
theorem `eLpNorm'_measure_zero_of_exponent_zero` / 定理 `eLpNorm'_measure_zero_of_exponent_zero`

English:
theorem eLpNorm'_measure_zero_of_exponent_zero
  given: {f : α -> ε}
  statement: eLpNorm' f 0 (0 : Measure α) = 1
  proof: by
  simp [eLpNorm']

中文:
定理 eLpNorm'_measure_zero_of_exponent_zero
  条件: {f : α -> ε}
  结论: eLpNorm' f 0 (0 : 测度 α) = 1
  证明: by
  simp [eLpNorm']
-/
theorem eLpNorm'_measure_zero_of_exponent_zero {f : α -> ε} : eLpNorm' f 0 (0 : Measure α) = 1 := by
  simp [eLpNorm']

/--
theorem `eLpNorm'_measure_zero_of_neg` / 定理 `eLpNorm'_measure_zero_of_neg`

English:
theorem eLpNorm'_measure_zero_of_neg
  given: {f : α -> ε} (hq_neg : q < 0)
  proof: by simp [eLpNorm', hq_neg]

中文:
定理 eLpNorm'_measure_zero_of_neg
  条件: {f : α -> ε} (hq_neg : q < 0)
  证明: by simp [eLpNorm', hq_neg]
-/
theorem eLpNorm'_measure_zero_of_neg {f : α -> ε} (hq_neg : q < 0) :
    eLpNorm' f q (0 : Measure α) = ∞ := by simp [eLpNorm', hq_neg]

end ESeminormedAddMonoid

@[simp]
/--
theorem `eLpNormEssSup_measure_zero` / 定理 `eLpNormEssSup_measure_zero`

English:
theorem eLpNormEssSup_measure_zero
  given: {f : α -> ε}
  statement: eLpNormEssSup f (0 : Measure α) = 0
  proof: by
  simp [eLpNormEssSup]

@[simp]

中文:
定理 eLpNormEssSup_measure_zero
  条件: {f : α -> ε}
  结论: eLpNormEssSup f (0 : 测度 α) = 0
  证明: by
  simp [eLpNormEssSup]

@[simp]

Depends on / 依赖: eLpNormEssSup
-/
theorem eLpNormEssSup_measure_zero {f : α -> ε} : eLpNormEssSup f (0 : Measure α) = 0 := by
  simp [eLpNormEssSup]

@[simp]
/--
theorem `eLpNorm_measure_zero` / 定理 `eLpNorm_measure_zero`

English:
theorem eLpNorm_measure_zero
  given: {f : α -> ε}
  statement: eLpNorm f p (0 : Measure α) = 0
  proof: by
  by_cases h0 : p = 0
  · simp [h0]
  by_cases h_top : p = ∞
  · simp [h_top]
  rw [← Ne] at h0
  simp [eLpNorm_eq_eLpNorm' h0 h_top, eLpNorm', ENNReal.toReal_pos h0 h_top]

中文:
定理 eLpNorm_measure_zero
  条件: {f : α -> ε}
  结论: eLpNorm f p (0 : 测度 α) = 0
  证明: by
  by_cases h0 : p = 0
  · simp [h0]
  by_cases h_top : p = ∞
  · simp [h_top]
  rw [← Ne] at h0
  simp [eLpNorm_eq_eLpNorm' h0 h_top, eLpNorm', ENNReal.toReal_pos h0 h_top]

Depends on / 依赖: ENNReal, ENNReal.toReal_pos, Free.of_equiv, I.den, I.equivNum, LinearEquiv, LinearEquiv.restrictScalars, coe_ne_zero, eLpNorm, eLpNorm_eq_eLpNorm, equivNum, h_top, nonZeroDivisors, nonZeroDivisors.coe_ne_zero, of_equiv, restrictScalars, toReal_pos
-/
theorem eLpNorm_measure_zero {f : α -> ε} : eLpNorm f p (0 : Measure α) = 0 := by
  by_cases h0 : p = 0
  · simp [h0]
  by_cases h_top : p = ∞
  · simp [h_top]
  rw [← Ne] at h0
  simp [eLpNorm_eq_eLpNorm' h0 h_top, eLpNorm', ENNReal.toReal_pos h0 h_top]

section ContinuousENorm

variable {ε : Type*} [TopologicalSpace ε] [ContinuousENorm ε]

/--
lemma `memLp_measure_zero` / 引理 `memLp_measure_zero`

English:
lemma memLp_measure_zero
  given: {f : α -> ε}
  statement: MemLp f p (0 : Measure α)
  proof: by
  simp [MemLp]

中文:
引理 memLp_measure_zero
  条件: {f : α -> ε}
  结论: MemLp f p (0 : 测度 α)
  证明: by
  simp [MemLp]

Depends on / 依赖: Finite, I.den, I.equivNum, LinearEquiv, LinearEquiv.restrictScalars, LinearEquiv.surjective, Module, Module.Finite.of_surjective, coe_ne_zero, equivNum, nonZeroDivisors, nonZeroDivisors.coe_ne_zero, of_surjective, restrictScalars, surjective, symm.toLinearMap, toLinearMap
-/
@[simp] lemma memLp_measure_zero {f : α -> ε} : MemLp f p (0 : Measure α) := by
  simp [MemLp]

end ContinuousENorm

end Zero

section Neg

@[simp]
/--
theorem `eLpNorm'_neg` / 定理 `eLpNorm'_neg`

English:
theorem eLpNorm'_neg
  given: (f : α -> F) (q : Real) (μ : Measure α)
  statement: eLpNorm' (-f) q μ = eLpNorm' f q μ
  proof: by
  simp [eLpNorm'_eq_lintegral_enorm]

@[simp]

中文:
定理 eLpNorm'_neg
  条件: (f : α -> F) (q : 实数) (μ : 测度 α)
  结论: eLpNorm' (-f) q μ = eLpNorm' f q μ
  证明: by
  simp [eLpNorm'_eq_lintegral_enorm]

@[simp]

Depends on / 依赖: Algebra, Algebra.algebraMapSubmonoid, Algebra.lmul, Algebra.lmul_isUnit_iff, Ideal.absNorm, Ideal.mul_mem_right, Int.cast_ne_zero, IsLocalization, IsLocalization.mem_coeSubmodule, IsLocalization.surj, absNorm, algebraMap, algebraMapSubmonoid, cast_ne_zero, coe_ne_zero, commutes, eq_intCast, isUnit_iff_ne_zero, lmul_isUnit_iff, mem_coeSubmodule
-/
theorem eLpNorm'_neg (f : α -> F) (q : Real) (μ : Measure α) : eLpNorm' (-f) q μ = eLpNorm' f q μ := by
  simp [eLpNorm'_eq_lintegral_enorm]

@[simp]
/--
theorem `eLpNorm_neg` / 定理 `eLpNorm_neg`

English:
theorem eLpNorm_neg
  given: (f : α -> F) (p : Real>=0∞) (μ : Measure α)
  statement: eLpNorm (-f) p μ = eLpNorm f p μ
  proof: by
  by_cases h0 : p = 0
  · simp [h0]
  by_cases h_top : p = ∞
  · simp [h_top, eLpNormEssSup_eq_essSup_enorm]
  simp [eLpNorm_eq_eLpNorm' h0 h_top]

中文:
定理 eLpNorm_neg
  条件: (f : α -> F) (p : 实数>=0∞) (μ : 测度 α)
  结论: eLpNorm (-f) p μ = eLpNorm f p μ
  证明: by
  by_cases h0 : p = 0
  · simp [h0]
  by_cases h_top : p = ∞
  · simp [h_top, eLpNormEssSup_eq_essSup_enorm]
  simp [eLpNorm_eq_eLpNorm' h0 h_top]

Depends on / 依赖: eLpNormEssSup_eq_essSup_enorm, eLpNorm_eq_eLpNorm, h_top
-/
theorem eLpNorm_neg (f : α -> F) (p : Real>=0∞) (μ : Measure α) : eLpNorm (-f) p μ = eLpNorm f p μ := by
  by_cases h0 : p = 0
  · simp [h0]
  by_cases h_top : p = ∞
  · simp [h_top, eLpNormEssSup_eq_essSup_enorm]
  simp [eLpNorm_eq_eLpNorm' h0 h_top]

/--
lemma `eLpNorm_sub_comm` / 引理 `eLpNorm_sub_comm`

English:
lemma eLpNorm_sub_comm
  given: (f g : α -> E) (p : Real>=0∞) (μ : Measure α)
  proof: by simp [← eLpNorm_neg (f := f - g)]

中文:
引理 eLpNorm_sub_comm
  条件: (f g : α -> E) (p : 实数>=0∞) (μ : 测度 α)
  证明: by simp [← eLpNorm_neg (f := f - g)]

Depends on / 依赖: eLpNorm_neg
-/
lemma eLpNorm_sub_comm (f g : α -> E) (p : Real>=0∞) (μ : Measure α) :
    eLpNorm (f - g) p μ = eLpNorm (g - f) p μ := by simp [← eLpNorm_neg (f := f - g)]

/--
theorem `MemLp.neg` / 定理 `MemLp.neg`

English:
theorem MemLp.neg
  given: {f : α -> E} (hf : MemLp f p μ)
  statement: MemLp (-f) p μ
  proof: ⟨AEStronglyMeasurable.neg hf.1, by simp [hf.right]⟩

中文:
定理 MemLp.neg
  条件: {f : α -> E} (hf : MemLp f p μ)
  结论: MemLp (-f) p μ
  证明: ⟨AEStronglyMeasurable.neg hf.1, by simp [hf.right]⟩

Depends on / 依赖: AEStronglyMeasurable, AEStronglyMeasurable.neg, hf.right
-/
theorem MemLp.neg {f : α -> E} (hf : MemLp f p μ) : MemLp (-f) p μ :=
  ⟨AEStronglyMeasurable.neg hf.1, by simp [hf.right]⟩

/--
theorem `memLp_neg_iff` / 定理 `memLp_neg_iff`

English:
theorem memLp_neg_iff
  given: {f : α -> E}
  statement: MemLp (-f) p μ ↔ MemLp f p μ
  proof: ⟨fun h => neg_neg f ▸ h.neg, MemLp.neg⟩

中文:
定理 memLp_neg_iff
  条件: {f : α -> E}
  结论: MemLp (-f) p μ ↔ MemLp f p μ
  证明: ⟨fun h => neg_neg f ▸ h.neg, MemLp.neg⟩

Depends on / 依赖: MemLp.neg, h.neg, neg_neg
-/
theorem memLp_neg_iff {f : α -> E} : MemLp (-f) p μ ↔ MemLp f p μ :=
  ⟨fun h => neg_neg f ▸ h.neg, MemLp.neg⟩

end Neg

section Const

variable {ε' ε'' : Type*} [TopologicalSpace ε'] [ContinuousENorm ε']
  [TopologicalSpace ε''] [ESeminormedAddMonoid ε'']

/--
theorem `eLpNorm'_const` / 定理 `eLpNorm'_const`

English:
theorem eLpNorm'_const
  given: (c : ε) (hq_pos : 0 < q)
  proof: by
  rw [eLpNorm'_eq_lintegral_enorm]; rw [lintegral_const]; rw [ENNReal.mul_rpow_of_nonneg _ _ (by simp [hq_pos.le] : 0 <= 1 / q)]
  congr
  rw [← ENNReal.rpow_mul]
  suffices hq_cancel : q * (1 / q) = 1 by rw [hq_cancel, ENNReal.rpow_one]
  rw [one_div]; rw [mul_inv_cancel₀ (ne_of_lt hq_pos).symm]

中文:
定理 eLpNorm'_const
  条件: (c : ε) (hq_pos : 0 < q)
  证明: by
  rw [eLpNorm'_eq_lintegral_enorm]; rw [lintegral_const]; rw [ENNReal.mul_rpow_of_nonneg _ _ (by simp [hq_pos.le] : 0 <= 1 / q)]
  congr
  rw [← ENNReal.rpow_mul]
  suffices hq_cancel : q * (1 / q) = 1 by rw [hq_cancel, ENNReal.rpow_one]
  rw [one_div]; rw [mul_inv_cancel₀ (ne_of_lt hq_pos).symm]
-/
theorem eLpNorm'_const (c : ε) (hq_pos : 0 < q) :
    eLpNorm' (fun _ : α => c) q μ = ‖c‖ₑ * μ Set.univ ^ (1 / q) := by
  rw [eLpNorm'_eq_lintegral_enorm]; rw [lintegral_const]; rw [ENNReal.mul_rpow_of_nonneg _ _ (by simp [hq_pos.le] : 0 <= 1 / q)]
  congr
  rw [← ENNReal.rpow_mul]
  suffices hq_cancel : q * (1 / q) = 1 by rw [hq_cancel, ENNReal.rpow_one]
  rw [one_div]; rw [mul_inv_cancel₀ (ne_of_lt hq_pos).symm]

-- Generalising this to ESeminormedAddMonoid requires a case analysis whether ‖c‖ₑ = ⊤,
-- and will happen in a future PR.
/--
theorem `eLpNorm'_const'` / 定理 `eLpNorm'_const'`

English:
theorem eLpNorm'_const'
  given: [IsFiniteMeasure μ] (c : F) (hc_ne_zero : c != 0) (hq_ne_zero : q != 0)
  proof: by
  rw [eLpNorm'_eq_lintegral_enorm]; rw [lintegral_const]; rw [ENNReal.mul_rpow_of_ne_top _ (by finiteness)]
  · congr
    rw [← ENNReal.rpow_mul]
    suffices hp_cancel : q * (1 / q) = 1 by rw [hp_cancel, ENNReal.rpow_one]
    rw [one_div]; rw [mul_inv_cancel₀ hq_ne_zero]
  · finiteness [show ‖c‖ₑ != 0 by simp [hc_ne_zero]]

中文:
定理 eLpNorm'_const'
  条件: [是有限测度 μ] (c : F) (hc_ne_zero : c != 0) (hq_ne_zero : q != 0)
  证明: by
  rw [eLpNorm'_eq_lintegral_enorm]; rw [lintegral_const]; rw [ENNReal.mul_rpow_of_ne_top _ (by finiteness)]
  · congr
    rw [← ENNReal.rpow_mul]
    suffices hp_cancel : q * (1 / q) = 1 by rw [hp_cancel, ENNReal.rpow_one]
    rw [one_div]; rw [mul_inv_cancel₀ hq_ne_zero]
  · finiteness [show ‖c‖ₑ != 0 by simp [hc_ne_zero]]
-/
theorem eLpNorm'_const' [IsFiniteMeasure μ] (c : F) (hc_ne_zero : c != 0) (hq_ne_zero : q != 0) :
    eLpNorm' (fun _ : α => c) q μ = ‖c‖ₑ * μ Set.univ ^ (1 / q) := by
  rw [eLpNorm'_eq_lintegral_enorm]; rw [lintegral_const]; rw [ENNReal.mul_rpow_of_ne_top _ (by finiteness)]
  · congr
    rw [← ENNReal.rpow_mul]
    suffices hp_cancel : q * (1 / q) = 1 by rw [hp_cancel, ENNReal.rpow_one]
    rw [one_div]; rw [mul_inv_cancel₀ hq_ne_zero]
  · finiteness [show ‖c‖ₑ != 0 by simp [hc_ne_zero]]

/--
theorem `eLpNormEssSup_const` / 定理 `eLpNormEssSup_const`

English:
theorem eLpNormEssSup_const
  given: (c : ε) (hμ : μ != 0)
  statement: eLpNormEssSup (fun _ : α => c) μ = ‖c‖ₑ
  proof: by
  rw [eLpNormEssSup_eq_essSup_enorm]; rw [essSup_const _ hμ]

中文:
定理 eLpNormEssSup_const
  条件: (c : ε) (hμ : μ != 0)
  结论: eLpNormEssSup (fun _ : α => c) μ = ‖c‖ₑ
  证明: by
  rw [eLpNormEssSup_eq_essSup_enorm]; rw [essSup_const _ hμ]

Depends on / 依赖: eLpNormEssSup_eq_essSup_enorm, essSup_const
-/
theorem eLpNormEssSup_const (c : ε) (hμ : μ != 0) : eLpNormEssSup (fun _ : α => c) μ = ‖c‖ₑ := by
  rw [eLpNormEssSup_eq_essSup_enorm]; rw [essSup_const _ hμ]

/--
theorem `eLpNorm'_const_of_isProbabilityMeasure` / 定理 `eLpNorm'_const_of_isProbabilityMeasure`

English:
theorem eLpNorm'_const_of_isProbabilityMeasure
  given: (c : ε) (hq_pos : 0 < q) [IsProbabilityMeasure μ]
  proof: by simp [eLpNorm'_const c hq_pos, measure_univ]

中文:
定理 eLpNorm'_const_of_isProbabilityMeasure
  条件: (c : ε) (hq_pos : 0 < q) [是概率测度 μ]
  证明: by simp [eLpNorm'_const c hq_pos, measure_univ]
-/
theorem eLpNorm'_const_of_isProbabilityMeasure (c : ε) (hq_pos : 0 < q) [IsProbabilityMeasure μ] :
    eLpNorm' (fun _ : α => c) q μ = ‖c‖ₑ := by simp [eLpNorm'_const c hq_pos, measure_univ]

/--
theorem `eLpNorm_const` / 定理 `eLpNorm_const`

English:
theorem eLpNorm_const
  given: (c : ε) (h0 : p != 0) (hμ : μ != 0)
  proof: by
  by_cases h_top : p = ∞
  · simp [h_top, eLpNormEssSup_const c hμ]
  simp [eLpNorm_eq_eLpNorm' h0 h_top, eLpNorm'_const, ENNReal.toReal_pos h0 h_top]

中文:
定理 eLpNorm_const
  条件: (c : ε) (h0 : p != 0) (hμ : μ != 0)
  证明: by
  by_cases h_top : p = ∞
  · simp [h_top, eLpNormEssSup_const c hμ]
  simp [eLpNorm_eq_eLpNorm' h0 h_top, eLpNorm'_const, ENNReal.toReal_pos h0 h_top]

Depends on / 依赖: ENNReal, ENNReal.toReal_pos, _const, eLpNorm, eLpNormEssSup_const, eLpNorm_eq_eLpNorm, h_top, toReal_pos
-/
theorem eLpNorm_const (c : ε) (h0 : p != 0) (hμ : μ != 0) :
    eLpNorm (fun _ : α => c) p μ = ‖c‖ₑ * μ Set.univ ^ (1 / ENNReal.toReal p) := by
  by_cases h_top : p = ∞
  · simp [h_top, eLpNormEssSup_const c hμ]
  simp [eLpNorm_eq_eLpNorm' h0 h_top, eLpNorm'_const, ENNReal.toReal_pos h0 h_top]

/--
theorem `eLpNorm_const'` / 定理 `eLpNorm_const'`

English:
theorem eLpNorm_const'
  given: (c : ε) (h0 : p != 0) (h_top : p != ∞)
  proof: by
  simp [eLpNorm_eq_eLpNorm' h0 h_top, eLpNorm'_const, ENNReal.toReal_pos h0 h_top]

中文:
定理 eLpNorm_const'
  条件: (c : ε) (h0 : p != 0) (h_top : p != ∞)
  证明: by
  simp [eLpNorm_eq_eLpNorm' h0 h_top, eLpNorm'_const, ENNReal.toReal_pos h0 h_top]

Depends on / 依赖: ENNReal, ENNReal.toReal_pos, _const, eLpNorm, eLpNorm_eq_eLpNorm, h_top, toReal_pos
-/
theorem eLpNorm_const' (c : ε) (h0 : p != 0) (h_top : p != ∞) :
    eLpNorm (fun _ : α => c) p μ = ‖c‖ₑ * μ Set.univ ^ (1 / ENNReal.toReal p) := by
  simp [eLpNorm_eq_eLpNorm' h0 h_top, eLpNorm'_const, ENNReal.toReal_pos h0 h_top]

-- NB. If ‖c‖ₑ = ∞ and μ is finite, this claim is false: the right has side is true,
-- but the left-hand side is false (as the norm is infinite).
/--
theorem `eLpNorm_const_lt_top_iff_enorm` / 定理 `eLpNorm_const_lt_top_iff_enorm`

English:
theorem eLpNorm_const_lt_top_iff_enorm
  statement: {c : ε''} (hc' : ‖c‖ₑ != ∞)
  proof: by
  have hp : 0 < p.toReal := ENNReal.toReal_pos hp_ne_zero hp_ne_top
  by_cases hμ : μ = 0
  · simp only [hμ, Measure.coe_zero, Pi.zero_apply, or_true, ENNReal.zero_lt_top,
      eLpNorm_measure_zero]
  by_cases hc : ‖c‖ₑ = 0
  · rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top hp_ne_zero hp_ne_top]
    simp [hc, ENNReal.zero_rpow_of_pos hp]
  rw [eLpNorm_const' c hp_ne_zero hp_ne_top]
  obtain hμ_top | hμ_ne_top := eq_or_ne (μ .univ) ∞
  · simp [hc, hμ_top, hp]
  rw [ENNReal.mul_lt_top_iff]
  simpa [hμ, hc, hμ_ne_top, hμ_ne_top.lt_top, hc'.lt_top] using by finiteness

中文:
定理 eLpNorm_const_lt_top_iff_enorm
  结论: {c : ε''} (hc' : ‖c‖ₑ != ∞)
  证明: by
  have hp : 0 < p.toReal := ENNReal.toReal_pos hp_ne_zero hp_ne_top
  by_cases hμ : μ = 0
  · simp only [hμ, Measure.coe_zero, Pi.zero_apply, or_true, ENNReal.zero_lt_top,
      eLpNorm_measure_zero]
  by_cases hc : ‖c‖ₑ = 0
  · rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top hp_ne_zero hp_ne_top]
    simp [hc, ENNReal.zero_rpow_of_pos hp]
  rw [eLpNorm_const' c hp_ne_zero hp_ne_top]
  obtain hμ_top | hμ_ne_top := eq_or_ne (μ .univ) ∞
  · simp [hc, hμ_top, hp]
  rw [ENNReal.mul_lt_top_iff]
  simpa [hμ, hc, hμ_ne_top, hμ_ne_top.lt_top, hc'.lt_top] using by finiteness

Depends on / 依赖: ENNReal, ENNReal.mul_lt_top_iff, ENNReal.toReal_pos, ENNReal.zero_lt_top, ENNReal.zero_rpow_of_pos, Measure, Measure.coe_zero, Pi.zero_apply, coe_zero, eLpNorm_const, eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top, eLpNorm_measure_zero, eq_or_ne, hp_ne_top, hp_ne_zero, mul_lt_top_iff, or_true, p.toReal, toReal, toReal_pos
-/
theorem eLpNorm_const_lt_top_iff_enorm {c : ε''} (hc' : ‖c‖ₑ != ∞)
    {p : Real>=0∞} (hp_ne_zero : p != 0) (hp_ne_top : p != ∞) :
    eLpNorm (fun _ : α => c) p μ < ∞ ↔ ‖c‖ₑ = 0 ∨ μ Set.univ < ∞ := by
  have hp : 0 < p.toReal := ENNReal.toReal_pos hp_ne_zero hp_ne_top
  by_cases hμ : μ = 0
  · simp only [hμ, Measure.coe_zero, Pi.zero_apply, or_true, ENNReal.zero_lt_top,
      eLpNorm_measure_zero]
  by_cases hc : ‖c‖ₑ = 0
  · rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top hp_ne_zero hp_ne_top]
    simp [hc, ENNReal.zero_rpow_of_pos hp]
  rw [eLpNorm_const' c hp_ne_zero hp_ne_top]
  obtain hμ_top | hμ_ne_top := eq_or_ne (μ .univ) ∞
  · simp [hc, hμ_top, hp]
  rw [ENNReal.mul_lt_top_iff]
  simpa [hμ, hc, hμ_ne_top, hμ_ne_top.lt_top, hc'.lt_top] using by finiteness

/--
theorem `eLpNorm_const_lt_top_iff` / 定理 `eLpNorm_const_lt_top_iff`

English:
theorem eLpNorm_const_lt_top_iff
  given: {p : Real>=0∞} {c : F} (hp_ne_zero : p != 0) (hp_ne_top : p != ∞)
  proof: by
  rw [eLpNorm_const_lt_top_iff_enorm enorm_ne_top hp_ne_zero hp_ne_top]; simp

中文:
定理 eLpNorm_const_lt_top_iff
  条件: {p : 实数>=0∞} {c : F} (hp_ne_zero : p != 0) (hp_ne_top : p != ∞)
  证明: by
  rw [eLpNorm_const_lt_top_iff_enorm enorm_ne_top hp_ne_zero hp_ne_top]; simp

Depends on / 依赖: eLpNorm_const_lt_top_iff_enorm, enorm_ne_top, hp_ne_top, hp_ne_zero
-/
theorem eLpNorm_const_lt_top_iff {p : Real>=0∞} {c : F} (hp_ne_zero : p != 0) (hp_ne_top : p != ∞) :
    eLpNorm (fun _ : α => c) p μ < ∞ ↔ c = 0 ∨ μ Set.univ < ∞ := by
  rw [eLpNorm_const_lt_top_iff_enorm enorm_ne_top hp_ne_zero hp_ne_top]; simp

/--
theorem `memLp_const_enorm` / 定理 `memLp_const_enorm`

English:
theorem memLp_const_enorm
  given: {c : ε'} (hc : ‖c‖ₑ != ⊤) [IsFiniteMeasure μ]
  proof: by
  refine ⟨aestronglyMeasurable_const, ?_⟩
  by_cases h0 : p = 0
  · simp [h0]
  by_cases hμ : μ = 0
  · simp [hμ]
  rw [eLpNorm_const c h0 hμ]
  finiteness

中文:
定理 memLp_const_enorm
  条件: {c : ε'} (hc : ‖c‖ₑ != ⊤) [是有限测度 μ]
  证明: by
  refine ⟨aestronglyMeasurable_const, ?_⟩
  by_cases h0 : p = 0
  · simp [h0]
  by_cases hμ : μ = 0
  · simp [hμ]
  rw [eLpNorm_const c h0 hμ]
  finiteness

Depends on / 依赖: aestronglyMeasurable_const, eLpNorm_const, finiteness
-/
theorem memLp_const_enorm {c : ε'} (hc : ‖c‖ₑ != ⊤) [IsFiniteMeasure μ] :
    MemLp (fun _ : α => c) p μ := by
  refine ⟨aestronglyMeasurable_const, ?_⟩
  by_cases h0 : p = 0
  · simp [h0]
  by_cases hμ : μ = 0
  · simp [hμ]
  rw [eLpNorm_const c h0 hμ]
  finiteness

/--
theorem `memLp_const` / 定理 `memLp_const`

English:
theorem memLp_const
  given: (c : E) [IsFiniteMeasure μ]
  statement: MemLp (fun _ : α => c) p μ
  proof: memLp_const_enorm enorm_ne_top

中文:
定理 memLp_const
  条件: (c : E) [是有限测度 μ]
  结论: MemLp (fun _ : α => c) p μ
  证明: memLp_const_enorm enorm_ne_top

Depends on / 依赖: enorm_ne_top, memLp_const_enorm
-/
theorem memLp_const (c : E) [IsFiniteMeasure μ] : MemLp (fun _ : α => c) p μ :=
  memLp_const_enorm enorm_ne_top

/--
theorem `memLp_top_const_enorm` / 定理 `memLp_top_const_enorm`

English:
theorem memLp_top_const_enorm
  given: {c : ε'} (hc : ‖c‖ₑ != ⊤)
  proof: ⟨aestronglyMeasurable_const, by by_cases h : μ = 0 <;> simp [eLpNorm_const _, h, hc.lt_top]⟩

中文:
定理 memLp_top_const_enorm
  条件: {c : ε'} (hc : ‖c‖ₑ != ⊤)
  证明: ⟨aestronglyMeasurable_const, by by_cases h : μ = 0 <;> simp [eLpNorm_const _, h, hc.lt_top]⟩

Depends on / 依赖: aestronglyMeasurable_const, eLpNorm_const, hc.lt_top, lt_top
-/
theorem memLp_top_const_enorm {c : ε'} (hc : ‖c‖ₑ != ⊤) :
    MemLp (fun _ : α => c) ∞ μ :=
  ⟨aestronglyMeasurable_const, by by_cases h : μ = 0 <;> simp [eLpNorm_const _, h, hc.lt_top]⟩

/--
theorem `memLp_top_const` / 定理 `memLp_top_const`

English:
theorem memLp_top_const
  given: (c : E)
  statement: MemLp (fun _ : α => c) ∞ μ
  proof: memLp_top_const_enorm enorm_ne_top

中文:
定理 memLp_top_const
  条件: (c : E)
  结论: MemLp (fun _ : α => c) ∞ μ
  证明: memLp_top_const_enorm enorm_ne_top

Depends on / 依赖: enorm_ne_top, memLp_top_const_enorm
-/
theorem memLp_top_const (c : E) : MemLp (fun _ : α => c) ∞ μ :=
  memLp_top_const_enorm enorm_ne_top

/--
theorem `memLp_const_iff_enorm` / 定理 `memLp_const_iff_enorm`

English:
theorem memLp_const_iff_enorm
  proof: by
  simp_all [MemLp, aestronglyMeasurable_const,
    eLpNorm_const_lt_top_iff_enorm hc hp_ne_zero hp_ne_top]

中文:
定理 memLp_const_iff_enorm
  证明: by
  simp_all [MemLp, aestronglyMeasurable_const,
    eLpNorm_const_lt_top_iff_enorm hc hp_ne_zero hp_ne_top]

Depends on / 依赖: aestronglyMeasurable_const, eLpNorm_const_lt_top_iff_enorm, hp_ne_top, hp_ne_zero
-/
theorem memLp_const_iff_enorm
    {p : Real>=0∞} {c : ε''} (hc : ‖c‖ₑ != ⊤) (hp_ne_zero : p != 0) (hp_ne_top : p != ∞) :
    MemLp (fun _ : α => c) p μ ↔ ‖c‖ₑ = 0 ∨ μ Set.univ < ∞ := by
  simp_all [MemLp, aestronglyMeasurable_const,
    eLpNorm_const_lt_top_iff_enorm hc hp_ne_zero hp_ne_top]

/--
theorem `memLp_const_iff` / 定理 `memLp_const_iff`

English:
theorem memLp_const_iff
  given: {p : Real>=0∞} {c : E} (hp_ne_zero : p != 0) (hp_ne_top : p != ∞)
  proof: by
  rw [memLp_const_iff_enorm enorm_ne_top hp_ne_zero hp_ne_top]; simp

中文:
定理 memLp_const_iff
  条件: {p : 实数>=0∞} {c : E} (hp_ne_zero : p != 0) (hp_ne_top : p != ∞)
  证明: by
  rw [memLp_const_iff_enorm enorm_ne_top hp_ne_zero hp_ne_top]; simp

Depends on / 依赖: enorm_ne_top, hp_ne_top, hp_ne_zero, memLp_const_iff_enorm
-/
theorem memLp_const_iff {p : Real>=0∞} {c : E} (hp_ne_zero : p != 0) (hp_ne_top : p != ∞) :
    MemLp (fun _ : α => c) p μ ↔ c = 0 ∨ μ Set.univ < ∞ := by
  rw [memLp_const_iff_enorm enorm_ne_top hp_ne_zero hp_ne_top]; simp

end Const

variable {f : α -> F}

/--
lemma `eLpNorm'_mono_enorm_ae` / 引理 `eLpNorm'_mono_enorm_ae`

English:
lemma eLpNorm'_mono_enorm_ae
  given: {f : α -> ε} {g : α -> ε'} (hq : 0 <= q) (h : forallᵐ x ∂μ, ‖f x‖ₑ <= ‖g x‖ₑ)
  proof: by
  simp only [eLpNorm'_eq_lintegral_enorm]
  gcongr ?_ ^ (1 / q)
  refine lintegral_mono_ae (h.mono fun x hx => ?_)
  gcongr

中文:
引理 eLpNorm'_mono_enorm_ae
  条件: {f : α -> ε} {g : α -> ε'} (hq : 0 <= q) (h : 对任意ᵐ x ∂μ, ‖f x‖ₑ <= ‖g x‖ₑ)
  证明: by
  simp only [eLpNorm'_eq_lintegral_enorm]
  gcongr ?_ ^ (1 / q)
  refine lintegral_mono_ae (h.mono fun x hx => ?_)
  gcongr
-/
lemma eLpNorm'_mono_enorm_ae {f : α -> ε} {g : α -> ε'} (hq : 0 <= q) (h : forallᵐ x ∂μ, ‖f x‖ₑ <= ‖g x‖ₑ) :
    eLpNorm' f q μ <= eLpNorm' g q μ := by
  simp only [eLpNorm'_eq_lintegral_enorm]
  gcongr ?_ ^ (1 / q)
  refine lintegral_mono_ae (h.mono fun x hx => ?_)
  gcongr

/--
lemma `eLpNorm'_mono_nnnorm_ae` / 引理 `eLpNorm'_mono_nnnorm_ae`

English:
lemma eLpNorm'_mono_nnnorm_ae
  given: {f : α -> F} {g : α -> G} (hq : 0 <= q) (h : forallᵐ x ∂μ, ‖f x‖₊ <= ‖g x‖₊)
  proof: eLpNorm'_mono_enorm_ae hq h.mono fun _ hx => ENNReal.coe_le_coe.mpr hx

中文:
引理 eLpNorm'_mono_nnnorm_ae
  条件: {f : α -> F} {g : α -> G} (hq : 0 <= q) (h : 对任意ᵐ x ∂μ, ‖f x‖₊ <= ‖g x‖₊)
  证明: eLpNorm'_mono_enorm_ae hq h.mono fun _ hx => ENNReal.coe_le_coe.mpr hx
-/
lemma eLpNorm'_mono_nnnorm_ae {f : α -> F} {g : α -> G} (hq : 0 <= q) (h : forallᵐ x ∂μ, ‖f x‖₊ <= ‖g x‖₊) :
    eLpNorm' f q μ <= eLpNorm' g q μ :=
eLpNorm'_mono_enorm_ae hq h.mono fun _ hx => ENNReal.coe_le_coe.mpr hx

/--
theorem `eLpNorm'_mono_ae` / 定理 `eLpNorm'_mono_ae`

English:
theorem eLpNorm'_mono_ae
  given: {f : α -> F} {g : α -> G} (hq : 0 <= q) (h : forallᵐ x ∂μ, ‖f x‖ <= ‖g x‖)
  proof: eLpNorm'_mono_enorm_ae hq (by simpa only [enorm_le_iff_norm_le] using h)

中文:
定理 eLpNorm'_mono_ae
  条件: {f : α -> F} {g : α -> G} (hq : 0 <= q) (h : 对任意ᵐ x ∂μ, ‖f x‖ <= ‖g x‖)
  证明: eLpNorm'_mono_enorm_ae hq (by simpa only [enorm_le_iff_norm_le] using h)
-/
theorem eLpNorm'_mono_ae {f : α -> F} {g : α -> G} (hq : 0 <= q) (h : forallᵐ x ∂μ, ‖f x‖ <= ‖g x‖) :
    eLpNorm' f q μ <= eLpNorm' g q μ :=
  eLpNorm'_mono_enorm_ae hq (by simpa only [enorm_le_iff_norm_le] using h)

/--
theorem `eLpNorm'_congr_enorm_ae` / 定理 `eLpNorm'_congr_enorm_ae`

English:
theorem eLpNorm'_congr_enorm_ae
  given: {f : α -> ε} {g : α -> ε'} (hfg : forallᵐ x ∂μ, ‖f x‖ₑ = ‖g x‖ₑ)
  proof: by
  have : (‖f ·‖ₑ ^ q) =ᵐ[μ] (‖g ·‖ₑ ^ q) := hfg.mono fun x hx => by simp [hx]
  simp only [eLpNorm'_eq_lintegral_enorm, lintegral_congr_ae this]

中文:
定理 eLpNorm'_congr_enorm_ae
  条件: {f : α -> ε} {g : α -> ε'} (hfg : 对任意ᵐ x ∂μ, ‖f x‖ₑ = ‖g x‖ₑ)
  证明: by
  have : (‖f ·‖ₑ ^ q) =ᵐ[μ] (‖g ·‖ₑ ^ q) := hfg.mono fun x hx => by simp [hx]
  simp only [eLpNorm'_eq_lintegral_enorm, lintegral_congr_ae this]
-/
theorem eLpNorm'_congr_enorm_ae {f : α -> ε} {g : α -> ε'} (hfg : forallᵐ x ∂μ, ‖f x‖ₑ = ‖g x‖ₑ) :
    eLpNorm' f q μ = eLpNorm' g q μ := by
  have : (‖f ·‖ₑ ^ q) =ᵐ[μ] (‖g ·‖ₑ ^ q) := hfg.mono fun x hx => by simp [hx]
  simp only [eLpNorm'_eq_lintegral_enorm, lintegral_congr_ae this]

/--
theorem `eLpNorm'_congr_nnnorm_ae` / 定理 `eLpNorm'_congr_nnnorm_ae`

English:
theorem eLpNorm'_congr_nnnorm_ae
  given: {f : α -> F} {g : α -> G} (hfg : forallᵐ x ∂μ, ‖f x‖₊ = ‖g x‖₊)
  proof: by
  have : (‖f ·‖ₑ ^ q) =ᵐ[μ] (‖g ·‖ₑ ^ q) := hfg.mono fun x hx => by simp [enorm, hx]
  simp only [eLpNorm'_eq_lintegral_enorm, lintegral_congr_ae this]

中文:
定理 eLpNorm'_congr_nnnorm_ae
  条件: {f : α -> F} {g : α -> G} (hfg : 对任意ᵐ x ∂μ, ‖f x‖₊ = ‖g x‖₊)
  证明: by
  have : (‖f ·‖ₑ ^ q) =ᵐ[μ] (‖g ·‖ₑ ^ q) := hfg.mono fun x hx => by simp [enorm, hx]
  simp only [eLpNorm'_eq_lintegral_enorm, lintegral_congr_ae this]
-/
theorem eLpNorm'_congr_nnnorm_ae {f : α -> F} {g : α -> G} (hfg : forallᵐ x ∂μ, ‖f x‖₊ = ‖g x‖₊) :
    eLpNorm' f q μ = eLpNorm' g q μ := by
  have : (‖f ·‖ₑ ^ q) =ᵐ[μ] (‖g ·‖ₑ ^ q) := hfg.mono fun x hx => by simp [enorm, hx]
  simp only [eLpNorm'_eq_lintegral_enorm, lintegral_congr_ae this]

/--
theorem `eLpNorm'_congr_norm_ae` / 定理 `eLpNorm'_congr_norm_ae`

English:
theorem eLpNorm'_congr_norm_ae
  given: {f : α -> F} {g : α -> G} (hfg : forallᵐ x ∂μ, ‖f x‖ = ‖g x‖)
  proof: eLpNorm'_congr_nnnorm_ae hfg.mono fun _x hx => NNReal.eq hx

中文:
定理 eLpNorm'_congr_norm_ae
  条件: {f : α -> F} {g : α -> G} (hfg : 对任意ᵐ x ∂μ, ‖f x‖ = ‖g x‖)
  证明: eLpNorm'_congr_nnnorm_ae hfg.mono fun _x hx => NNReal.eq hx
-/
theorem eLpNorm'_congr_norm_ae {f : α -> F} {g : α -> G} (hfg : forallᵐ x ∂μ, ‖f x‖ = ‖g x‖) :
    eLpNorm' f q μ = eLpNorm' g q μ :=
eLpNorm'_congr_nnnorm_ae hfg.mono fun _x hx => NNReal.eq hx

/--
theorem `eLpNorm'_congr_ae` / 定理 `eLpNorm'_congr_ae`

English:
theorem eLpNorm'_congr_ae
  given: {f g : α -> ε} (hfg : f =ᵐ[μ] g)
  statement: eLpNorm' f q μ = eLpNorm' g q μ
  proof: eLpNorm'_congr_enorm_ae (hfg.fun_comp _)

中文:
定理 eLpNorm'_congr_ae
  条件: {f g : α -> ε} (hfg : f =ᵐ[μ] g)
  结论: eLpNorm' f q μ = eLpNorm' g q μ
  证明: eLpNorm'_congr_enorm_ae (hfg.fun_comp _)
-/
theorem eLpNorm'_congr_ae {f g : α -> ε} (hfg : f =ᵐ[μ] g) : eLpNorm' f q μ = eLpNorm' g q μ :=
  eLpNorm'_congr_enorm_ae (hfg.fun_comp _)

/--
theorem `eLpNormEssSup_congr_ae` / 定理 `eLpNormEssSup_congr_ae`

English:
theorem eLpNormEssSup_congr_ae
  given: {f g : α -> ε} (hfg : f =ᵐ[μ] g)
  proof: essSup_congr_ae (hfg.fun_comp enorm)

中文:
定理 eLpNormEssSup_congr_ae
  条件: {f g : α -> ε} (hfg : f =ᵐ[μ] g)
  证明: essSup_congr_ae (hfg.fun_comp enorm)

Depends on / 依赖: essSup_congr_ae, fun_comp, hfg.fun_comp
-/
theorem eLpNormEssSup_congr_ae {f g : α -> ε} (hfg : f =ᵐ[μ] g) :
    eLpNormEssSup f μ = eLpNormEssSup g μ :=
  essSup_congr_ae (hfg.fun_comp enorm)

/--
theorem `eLpNormEssSup_mono_enorm_ae` / 定理 `eLpNormEssSup_mono_enorm_ae`

English:
theorem eLpNormEssSup_mono_enorm_ae
  given: {f : α -> ε} {g : α -> ε'} (hfg : forallᵐ x ∂μ, ‖f x‖ₑ <= ‖g x‖ₑ)
  proof: essSup_mono_ae hfg

中文:
定理 eLpNormEssSup_mono_enorm_ae
  条件: {f : α -> ε} {g : α -> ε'} (hfg : 对任意ᵐ x ∂μ, ‖f x‖ₑ <= ‖g x‖ₑ)
  证明: essSup_mono_ae hfg

Depends on / 依赖: essSup_mono_ae
-/
theorem eLpNormEssSup_mono_enorm_ae {f : α -> ε} {g : α -> ε'} (hfg : forallᵐ x ∂μ, ‖f x‖ₑ <= ‖g x‖ₑ) :
    eLpNormEssSup f μ <= eLpNormEssSup g μ :=
essSup_mono_ae hfg

/--
theorem `eLpNormEssSup_mono_nnnorm_ae` / 定理 `eLpNormEssSup_mono_nnnorm_ae`

English:
theorem eLpNormEssSup_mono_nnnorm_ae
  given: {f : α -> F} {g : α -> G} (hfg : forallᵐ x ∂μ, ‖f x‖₊ <= ‖g x‖₊)
  proof: essSup_mono_ae hfg.mono fun _x hx => ENNReal.coe_le_coe.mpr hx

中文:
定理 eLpNormEssSup_mono_nnnorm_ae
  条件: {f : α -> F} {g : α -> G} (hfg : 对任意ᵐ x ∂μ, ‖f x‖₊ <= ‖g x‖₊)
  证明: essSup_mono_ae hfg.mono fun _x hx => ENNReal.coe_le_coe.mpr hx

Depends on / 依赖: ENNReal, ENNReal.coe_le_coe.mpr, coe_le_coe, essSup_mono_ae, hfg.mono
-/
theorem eLpNormEssSup_mono_nnnorm_ae {f : α -> F} {g : α -> G} (hfg : forallᵐ x ∂μ, ‖f x‖₊ <= ‖g x‖₊) :
    eLpNormEssSup f μ <= eLpNormEssSup g μ :=
essSup_mono_ae hfg.mono fun _x hx => ENNReal.coe_le_coe.mpr hx

/--
theorem `eLpNorm_mono_enorm_ae` / 定理 `eLpNorm_mono_enorm_ae`

English:
theorem eLpNorm_mono_enorm_ae
  given: {f : α -> ε} {g : α -> ε'} (h : forallᵐ x ∂μ, ‖f x‖ₑ <= ‖g x‖ₑ)
  proof: by
  simp only [eLpNorm]
  split_ifs
  · exact le_rfl
  · exact eLpNormEssSup_mono_enorm_ae h
  · exact eLpNorm'_mono_enorm_ae ENNReal.toReal_nonneg h

中文:
定理 eLpNorm_mono_enorm_ae
  条件: {f : α -> ε} {g : α -> ε'} (h : 对任意ᵐ x ∂μ, ‖f x‖ₑ <= ‖g x‖ₑ)
  证明: by
  simp only [eLpNorm]
  split_ifs
  · exact le_rfl
  · exact eLpNormEssSup_mono_enorm_ae h
  · exact eLpNorm'_mono_enorm_ae ENNReal.toReal_nonneg h

Depends on / 依赖: ENNReal, ENNReal.toReal_nonneg, _mono_enorm_ae, eLpNorm, eLpNormEssSup_mono_enorm_ae, le_rfl, split_ifs, toReal_nonneg
-/
theorem eLpNorm_mono_enorm_ae {f : α -> ε} {g : α -> ε'} (h : forallᵐ x ∂μ, ‖f x‖ₑ <= ‖g x‖ₑ) :
    eLpNorm f p μ <= eLpNorm g p μ := by
  simp only [eLpNorm]
  split_ifs
  · exact le_rfl
  · exact eLpNormEssSup_mono_enorm_ae h
  · exact eLpNorm'_mono_enorm_ae ENNReal.toReal_nonneg h

/--
theorem `eLpNorm_mono_nnnorm_ae` / 定理 `eLpNorm_mono_nnnorm_ae`

English:
theorem eLpNorm_mono_nnnorm_ae
  given: {f : α -> F} {g : α -> G} (h : forallᵐ x ∂μ, ‖f x‖₊ <= ‖g x‖₊)
  proof: eLpNorm_mono_enorm_ae h.mono fun _ hx => ENNReal.coe_le_coe.mpr hx

中文:
定理 eLpNorm_mono_nnnorm_ae
  条件: {f : α -> F} {g : α -> G} (h : 对任意ᵐ x ∂μ, ‖f x‖₊ <= ‖g x‖₊)
  证明: eLpNorm_mono_enorm_ae h.mono fun _ hx => ENNReal.coe_le_coe.mpr hx

Depends on / 依赖: ENNReal, ENNReal.coe_le_coe.mpr, coe_le_coe, eLpNorm_mono_enorm_ae, h.mono
-/
theorem eLpNorm_mono_nnnorm_ae {f : α -> F} {g : α -> G} (h : forallᵐ x ∂μ, ‖f x‖₊ <= ‖g x‖₊) :
    eLpNorm f p μ <= eLpNorm g p μ :=
eLpNorm_mono_enorm_ae h.mono fun _ hx => ENNReal.coe_le_coe.mpr hx

/--
theorem `eLpNorm_mono_ae` / 定理 `eLpNorm_mono_ae`

English:
theorem eLpNorm_mono_ae
  given: {f : α -> F} {g : α -> G} (h : forallᵐ x ∂μ, ‖f x‖ <= ‖g x‖)
  proof: eLpNorm_mono_enorm_ae (by simpa only [enorm_le_iff_norm_le] using h)

@[deprecated (since := "2026-06-24")] alias eLpNorm_mono_ae' := eLpNorm_mono_enorm_ae

中文:
定理 eLpNorm_mono_ae
  条件: {f : α -> F} {g : α -> G} (h : 对任意ᵐ x ∂μ, ‖f x‖ <= ‖g x‖)
  证明: eLpNorm_mono_enorm_ae (by simpa only [enorm_le_iff_norm_le] using h)

@[deprecated (since := "2026-06-24")] alias eLpNorm_mono_ae' := eLpNorm_mono_enorm_ae

Depends on / 依赖: eLpNorm_mono_enorm_ae, enorm_le_iff_norm_le
-/
theorem eLpNorm_mono_ae {f : α -> F} {g : α -> G} (h : forallᵐ x ∂μ, ‖f x‖ <= ‖g x‖) :
    eLpNorm f p μ <= eLpNorm g p μ :=
  eLpNorm_mono_enorm_ae (by simpa only [enorm_le_iff_norm_le] using h)

@[deprecated (since := "2026-06-24")] alias eLpNorm_mono_ae' := eLpNorm_mono_enorm_ae

/--
theorem `eLpNorm_mono_ae_real` / 定理 `eLpNorm_mono_ae_real`

English:
theorem eLpNorm_mono_ae_real
  given: {f : α -> F} {g : α -> Real} (h : forallᵐ x ∂μ, ‖f x‖ <= g x)
  proof: eLpNorm_mono_ae h.mono fun _x hx =>
    hx.trans ((le_abs_self _).trans (Real.norm_eq_abs _).symm.le)

中文:
定理 eLpNorm_mono_ae_real
  条件: {f : α -> F} {g : α -> 实数} (h : 对任意ᵐ x ∂μ, ‖f x‖ <= g x)
  证明: eLpNorm_mono_ae h.mono fun _x hx =>
    hx.trans ((le_abs_self _).trans (Real.norm_eq_abs _).symm.le)

Depends on / 依赖: Real.norm_eq_abs, eLpNorm_mono_ae, h.mono, hx.trans, le_abs_self, norm_eq_abs, symm.le
-/
theorem eLpNorm_mono_ae_real {f : α -> F} {g : α -> Real} (h : forallᵐ x ∂μ, ‖f x‖ <= g x) :
    eLpNorm f p μ <= eLpNorm g p μ :=
eLpNorm_mono_ae h.mono fun _x hx =>
    hx.trans ((le_abs_self _).trans (Real.norm_eq_abs _).symm.le)

/--
theorem `eLpNorm_mono_enorm` / 定理 `eLpNorm_mono_enorm`

English:
theorem eLpNorm_mono_enorm
  given: {f : α -> ε} {g : α -> ε'} (h : forall x, ‖f x‖ₑ <= ‖g x‖ₑ)
  proof: eLpNorm_mono_enorm_ae (Eventually.of_forall h)

中文:
定理 eLpNorm_mono_enorm
  条件: {f : α -> ε} {g : α -> ε'} (h : 对任意 x, ‖f x‖ₑ <= ‖g x‖ₑ)
  证明: eLpNorm_mono_enorm_ae (Eventually.of_forall h)

Depends on / 依赖: Eventually, Eventually.of_forall, eLpNorm_mono_enorm_ae, of_forall
-/
theorem eLpNorm_mono_enorm {f : α -> ε} {g : α -> ε'} (h : forall x, ‖f x‖ₑ <= ‖g x‖ₑ) :
    eLpNorm f p μ <= eLpNorm g p μ :=
  eLpNorm_mono_enorm_ae (Eventually.of_forall h)

/--
theorem `eLpNorm_mono_nnnorm` / 定理 `eLpNorm_mono_nnnorm`

English:
theorem eLpNorm_mono_nnnorm
  given: {f : α -> F} {g : α -> G} (h : forall x, ‖f x‖₊ <= ‖g x‖₊)
  proof: eLpNorm_mono_nnnorm_ae (Eventually.of_forall h)

中文:
定理 eLpNorm_mono_nnnorm
  条件: {f : α -> F} {g : α -> G} (h : 对任意 x, ‖f x‖₊ <= ‖g x‖₊)
  证明: eLpNorm_mono_nnnorm_ae (Eventually.of_forall h)

Depends on / 依赖: Eventually, Eventually.of_forall, eLpNorm_mono_nnnorm_ae, of_forall
-/
theorem eLpNorm_mono_nnnorm {f : α -> F} {g : α -> G} (h : forall x, ‖f x‖₊ <= ‖g x‖₊) :
    eLpNorm f p μ <= eLpNorm g p μ :=
  eLpNorm_mono_nnnorm_ae (Eventually.of_forall h)

/--
theorem `eLpNorm_mono` / 定理 `eLpNorm_mono`

English:
theorem eLpNorm_mono
  given: {f : α -> F} {g : α -> G} (h : forall x, ‖f x‖ <= ‖g x‖)
  proof: eLpNorm_mono_ae (Eventually.of_forall h)

中文:
定理 eLpNorm_mono
  条件: {f : α -> F} {g : α -> G} (h : 对任意 x, ‖f x‖ <= ‖g x‖)
  证明: eLpNorm_mono_ae (Eventually.of_forall h)

Depends on / 依赖: Eventually, Eventually.of_forall, eLpNorm_mono_ae, of_forall
-/
theorem eLpNorm_mono {f : α -> F} {g : α -> G} (h : forall x, ‖f x‖ <= ‖g x‖) :
    eLpNorm f p μ <= eLpNorm g p μ :=
  eLpNorm_mono_ae (Eventually.of_forall h)

/--
theorem `eLpNorm_mono_real` / 定理 `eLpNorm_mono_real`

English:
theorem eLpNorm_mono_real
  given: {f : α -> F} {g : α -> Real} (h : forall x, ‖f x‖ <= g x)
  proof: eLpNorm_mono_ae_real (Eventually.of_forall h)

中文:
定理 eLpNorm_mono_real
  条件: {f : α -> F} {g : α -> 实数} (h : 对任意 x, ‖f x‖ <= g x)
  证明: eLpNorm_mono_ae_real (Eventually.of_forall h)

Depends on / 依赖: Eventually, Eventually.of_forall, eLpNorm_mono_ae_real, of_forall
-/
theorem eLpNorm_mono_real {f : α -> F} {g : α -> Real} (h : forall x, ‖f x‖ <= g x) :
    eLpNorm f p μ <= eLpNorm g p μ :=
  eLpNorm_mono_ae_real (Eventually.of_forall h)

/--
theorem `eLpNormEssSup_le_of_ae_enorm_bound` / 定理 `eLpNormEssSup_le_of_ae_enorm_bound`

English:
theorem eLpNormEssSup_le_of_ae_enorm_bound
  given: {f : α -> ε} {C : Real>=0∞} (hfC : forallᵐ x ∂μ, ‖f x‖ₑ <= C)
  proof: essSup_le_of_ae_le C hfC

中文:
定理 eLpNormEssSup_le_of_ae_enorm_bound
  条件: {f : α -> ε} {C : 实数>=0∞} (hfC : 对任意ᵐ x ∂μ, ‖f x‖ₑ <= C)
  证明: essSup_le_of_ae_le C hfC

Depends on / 依赖: essSup_le_of_ae_le
-/
theorem eLpNormEssSup_le_of_ae_enorm_bound {f : α -> ε} {C : Real>=0∞} (hfC : forallᵐ x ∂μ, ‖f x‖ₑ <= C) :
    eLpNormEssSup f μ <= C :=
  essSup_le_of_ae_le C hfC

/--
theorem `eLpNormEssSup_le_of_ae_nnnorm_bound` / 定理 `eLpNormEssSup_le_of_ae_nnnorm_bound`

English:
theorem eLpNormEssSup_le_of_ae_nnnorm_bound
  given: {f : α -> F} {C : Real>=0} (hfC : forallᵐ x ∂μ, ‖f x‖₊ <= C)
  proof: essSup_le_of_ae_le (C : Real>=0∞) hfC.mono fun _x hx => ENNReal.coe_le_coe.mpr hx

中文:
定理 eLpNormEssSup_le_of_ae_nnnorm_bound
  条件: {f : α -> F} {C : 实数>=0} (hfC : 对任意ᵐ x ∂μ, ‖f x‖₊ <= C)
  证明: essSup_le_of_ae_le (C : Real>=0∞) hfC.mono fun _x hx => ENNReal.coe_le_coe.mpr hx

Depends on / 依赖: ENNReal, ENNReal.coe_le_coe.mpr, coe_le_coe, essSup_le_of_ae_le, hfC.mono
-/
theorem eLpNormEssSup_le_of_ae_nnnorm_bound {f : α -> F} {C : Real>=0} (hfC : forallᵐ x ∂μ, ‖f x‖₊ <= C) :
    eLpNormEssSup f μ <= C :=
essSup_le_of_ae_le (C : Real>=0∞) hfC.mono fun _x hx => ENNReal.coe_le_coe.mpr hx

/--
theorem `eLpNormEssSup_le_of_ae_bound` / 定理 `eLpNormEssSup_le_of_ae_bound`

English:
theorem eLpNormEssSup_le_of_ae_bound
  given: {f : α -> F} {C : Real} (hfC : forallᵐ x ∂μ, ‖f x‖ <= C)
  proof: eLpNormEssSup_le_of_ae_nnnorm_bound hfC.mono fun _x hx => hx.trans C.le_coe_toNNReal

中文:
定理 eLpNormEssSup_le_of_ae_bound
  条件: {f : α -> F} {C : 实数} (hfC : 对任意ᵐ x ∂μ, ‖f x‖ <= C)
  证明: eLpNormEssSup_le_of_ae_nnnorm_bound hfC.mono fun _x hx => hx.trans C.le_coe_toNNReal

Depends on / 依赖: C.le_coe_toNNReal, eLpNormEssSup_le_of_ae_nnnorm_bound, hfC.mono, hx.trans, le_coe_toNNReal
-/
theorem eLpNormEssSup_le_of_ae_bound {f : α -> F} {C : Real} (hfC : forallᵐ x ∂μ, ‖f x‖ <= C) :
    eLpNormEssSup f μ <= ENNReal.ofReal C :=
eLpNormEssSup_le_of_ae_nnnorm_bound hfC.mono fun _x hx => hx.trans C.le_coe_toNNReal

/--
theorem `eLpNormEssSup_lt_top_of_ae_enorm_bound` / 定理 `eLpNormEssSup_lt_top_of_ae_enorm_bound`

English:
theorem eLpNormEssSup_lt_top_of_ae_enorm_bound
  given: {f : α -> ε} {C : Real>=0} (hfC : forallᵐ x ∂μ, ‖f x‖ₑ <= C)
  proof: (eLpNormEssSup_le_of_ae_enorm_bound hfC).trans_lt ENNReal.coe_lt_top

中文:
定理 eLpNormEssSup_lt_top_of_ae_enorm_bound
  条件: {f : α -> ε} {C : 实数>=0} (hfC : 对任意ᵐ x ∂μ, ‖f x‖ₑ <= C)
  证明: (eLpNormEssSup_le_of_ae_enorm_bound hfC).trans_lt ENNReal.coe_lt_top

Depends on / 依赖: ENNReal, ENNReal.coe_lt_top, coe_lt_top, eLpNormEssSup_le_of_ae_enorm_bound, trans_lt
-/
theorem eLpNormEssSup_lt_top_of_ae_enorm_bound {f : α -> ε} {C : Real>=0} (hfC : forallᵐ x ∂μ, ‖f x‖ₑ <= C) :
    eLpNormEssSup f μ < ∞ :=
  (eLpNormEssSup_le_of_ae_enorm_bound hfC).trans_lt ENNReal.coe_lt_top

/--
theorem `eLpNormEssSup_lt_top_of_ae_nnnorm_bound` / 定理 `eLpNormEssSup_lt_top_of_ae_nnnorm_bound`

English:
theorem eLpNormEssSup_lt_top_of_ae_nnnorm_bound
  given: {f : α -> F} {C : Real>=0} (hfC : forallᵐ x ∂μ, ‖f x‖₊ <= C)
  proof: (eLpNormEssSup_le_of_ae_nnnorm_bound hfC).trans_lt ENNReal.coe_lt_top

中文:
定理 eLpNormEssSup_lt_top_of_ae_nnnorm_bound
  条件: {f : α -> F} {C : 实数>=0} (hfC : 对任意ᵐ x ∂μ, ‖f x‖₊ <= C)
  证明: (eLpNormEssSup_le_of_ae_nnnorm_bound hfC).trans_lt ENNReal.coe_lt_top

Depends on / 依赖: ENNReal, ENNReal.coe_lt_top, coe_lt_top, eLpNormEssSup_le_of_ae_nnnorm_bound, trans_lt
-/
theorem eLpNormEssSup_lt_top_of_ae_nnnorm_bound {f : α -> F} {C : Real>=0} (hfC : forallᵐ x ∂μ, ‖f x‖₊ <= C) :
    eLpNormEssSup f μ < ∞ :=
  (eLpNormEssSup_le_of_ae_nnnorm_bound hfC).trans_lt ENNReal.coe_lt_top

/--
theorem `eLpNormEssSup_lt_top_of_ae_bound` / 定理 `eLpNormEssSup_lt_top_of_ae_bound`

English:
theorem eLpNormEssSup_lt_top_of_ae_bound
  given: {f : α -> F} {C : Real} (hfC : forallᵐ x ∂μ, ‖f x‖ <= C)
  proof: (eLpNormEssSup_le_of_ae_bound hfC).trans_lt ENNReal.ofReal_lt_top

中文:
定理 eLpNormEssSup_lt_top_of_ae_bound
  条件: {f : α -> F} {C : 实数} (hfC : 对任意ᵐ x ∂μ, ‖f x‖ <= C)
  证明: (eLpNormEssSup_le_of_ae_bound hfC).trans_lt ENNReal.ofReal_lt_top

Depends on / 依赖: ENNReal, ENNReal.ofReal_lt_top, eLpNormEssSup_le_of_ae_bound, ofReal_lt_top, trans_lt
-/
theorem eLpNormEssSup_lt_top_of_ae_bound {f : α -> F} {C : Real} (hfC : forallᵐ x ∂μ, ‖f x‖ <= C) :
    eLpNormEssSup f μ < ∞ :=
  (eLpNormEssSup_le_of_ae_bound hfC).trans_lt ENNReal.ofReal_lt_top

/--
theorem `eLpNorm_le_of_ae_enorm_bound` / 定理 `eLpNorm_le_of_ae_enorm_bound`

English:
theorem eLpNorm_le_of_ae_enorm_bound
  statement: {ε} [TopologicalSpace ε] [ESeminormedAddMonoid ε]
  proof: by
  rcases eq_zero_or_neZero μ with rfl | hμ
  · simp
  by_cases hp : p = 0
  · simp [hp]
  have : forallᵐ x ∂μ, ‖f x‖ₑ <= ‖C‖ₑ := hfC.mono fun x hx => hx.trans (le_refl C)
  refine (eLpNorm_mono_enorm_ae this).trans_eq ?_
  rw [eLpNorm_const _ hp (NeZero.ne μ)]; rw [one_div]; rw [enorm_eq_self]; rw [smul_eq_mul]

中文:
定理 eLpNorm_le_of_ae_enorm_bound
  结论: {ε} [拓扑空间 ε] [ESeminormedAdd幺半群 ε]
  证明: by
  rcases eq_zero_or_neZero μ with rfl | hμ
  · simp
  by_cases hp : p = 0
  · simp [hp]
  have : forallᵐ x ∂μ, ‖f x‖ₑ <= ‖C‖ₑ := hfC.mono fun x hx => hx.trans (le_refl C)
  refine (eLpNorm_mono_enorm_ae this).trans_eq ?_
  rw [eLpNorm_const _ hp (NeZero.ne μ)]; rw [one_div]; rw [enorm_eq_self]; rw [smul_eq_mul]

Depends on / 依赖: NeZero, NeZero.ne, eLpNorm_const, eLpNorm_mono_enorm_ae, enorm_eq_self, eq_zero_or_neZero, hfC.mono, hx.trans, le_refl, one_div, smul_eq_mul, trans_eq
-/
theorem eLpNorm_le_of_ae_enorm_bound {ε} [TopologicalSpace ε] [ESeminormedAddMonoid ε]
    {f : α -> ε} {C : Real>=0∞} (hfC : forallᵐ x ∂μ, ‖f x‖ₑ <= C) :
    eLpNorm f p μ <= C • μ Set.univ ^ p.toReal⁻¹ := by
  rcases eq_zero_or_neZero μ with rfl | hμ
  · simp
  by_cases hp : p = 0
  · simp [hp]
  have : forallᵐ x ∂μ, ‖f x‖ₑ <= ‖C‖ₑ := hfC.mono fun x hx => hx.trans (le_refl C)
  refine (eLpNorm_mono_enorm_ae this).trans_eq ?_
  rw [eLpNorm_const _ hp (NeZero.ne μ)]; rw [one_div]; rw [enorm_eq_self]; rw [smul_eq_mul]

/--
theorem `eLpNorm_le_of_ae_nnnorm_bound` / 定理 `eLpNorm_le_of_ae_nnnorm_bound`

English:
theorem eLpNorm_le_of_ae_nnnorm_bound
  given: {f : α -> F} {C : Real>=0} (hfC : forallᵐ x ∂μ, ‖f x‖₊ <= C)
  proof: by
  simpa [C.enorm_eq, ENNReal.smul_def, smul_eq_mul] using
    (eLpNorm_le_of_ae_enorm_bound (f := f) (C := (C : Real>=0∞))
      (hfC.mono fun _ hx => by simpa using hx))

中文:
定理 eLpNorm_le_of_ae_nnnorm_bound
  条件: {f : α -> F} {C : 实数>=0} (hfC : 对任意ᵐ x ∂μ, ‖f x‖₊ <= C)
  证明: by
  simpa [C.enorm_eq, ENNReal.smul_def, smul_eq_mul] using
    (eLpNorm_le_of_ae_enorm_bound (f := f) (C := (C : Real>=0∞))
      (hfC.mono fun _ hx => by simpa using hx))

Depends on / 依赖: C.enorm_eq, ENNReal, ENNReal.smul_def, eLpNorm_le_of_ae_enorm_bound, enorm_eq, hfC.mono, smul_def, smul_eq_mul
-/
theorem eLpNorm_le_of_ae_nnnorm_bound {f : α -> F} {C : Real>=0} (hfC : forallᵐ x ∂μ, ‖f x‖₊ <= C) :
    eLpNorm f p μ <= C • μ Set.univ ^ p.toReal⁻¹ := by
  simpa [C.enorm_eq, ENNReal.smul_def, smul_eq_mul] using
    (eLpNorm_le_of_ae_enorm_bound (f := f) (C := (C : Real>=0∞))
      (hfC.mono fun _ hx => by simpa using hx))

/--
theorem `eLpNorm_le_of_ae_bound` / 定理 `eLpNorm_le_of_ae_bound`

English:
theorem eLpNorm_le_of_ae_bound
  given: {f : α -> F} {C : Real} (hfC : forallᵐ x ∂μ, ‖f x‖ <= C)
  proof: by
  rw [← mul_comm]
  exact eLpNorm_le_of_ae_nnnorm_bound (hfC.mono fun x hx => hx.trans C.le_coe_toNNReal)

中文:
定理 eLpNorm_le_of_ae_bound
  条件: {f : α -> F} {C : 实数} (hfC : 对任意ᵐ x ∂μ, ‖f x‖ <= C)
  证明: by
  rw [← mul_comm]
  exact eLpNorm_le_of_ae_nnnorm_bound (hfC.mono fun x hx => hx.trans C.le_coe_toNNReal)

Depends on / 依赖: C.le_coe_toNNReal, eLpNorm_le_of_ae_nnnorm_bound, hfC.mono, hx.trans, le_coe_toNNReal, mul_comm
-/
theorem eLpNorm_le_of_ae_bound {f : α -> F} {C : Real} (hfC : forallᵐ x ∂μ, ‖f x‖ <= C) :
    eLpNorm f p μ <= μ Set.univ ^ p.toReal⁻¹ * ENNReal.ofReal C := by
  rw [← mul_comm]
  exact eLpNorm_le_of_ae_nnnorm_bound (hfC.mono fun x hx => hx.trans C.le_coe_toNNReal)

/--
theorem `eLpNorm_congr_enorm_ae` / 定理 `eLpNorm_congr_enorm_ae`

English:
theorem eLpNorm_congr_enorm_ae
  given: {f : α -> ε} {g : α -> ε'} (hfg : forallᵐ x ∂μ, ‖f x‖ₑ = ‖g x‖ₑ)
  proof: le_antisymm (eLpNorm_mono_enorm_ae <| EventuallyEq.le hfg)
    (eLpNorm_mono_enorm_ae <| (EventuallyEq.symm hfg).le)

中文:
定理 eLpNorm_congr_enorm_ae
  条件: {f : α -> ε} {g : α -> ε'} (hfg : 对任意ᵐ x ∂μ, ‖f x‖ₑ = ‖g x‖ₑ)
  证明: le_antisymm (eLpNorm_mono_enorm_ae <| EventuallyEq.le hfg)
    (eLpNorm_mono_enorm_ae <| (EventuallyEq.symm hfg).le)

Depends on / 依赖: EventuallyEq, EventuallyEq.le, EventuallyEq.symm, eLpNorm_mono_enorm_ae, le_antisymm
-/
theorem eLpNorm_congr_enorm_ae {f : α -> ε} {g : α -> ε'} (hfg : forallᵐ x ∂μ, ‖f x‖ₑ = ‖g x‖ₑ) :
    eLpNorm f p μ = eLpNorm g p μ :=
  le_antisymm (eLpNorm_mono_enorm_ae <| EventuallyEq.le hfg)
    (eLpNorm_mono_enorm_ae <| (EventuallyEq.symm hfg).le)

/--
theorem `eLpNorm_congr_nnnorm_ae` / 定理 `eLpNorm_congr_nnnorm_ae`

English:
theorem eLpNorm_congr_nnnorm_ae
  given: {f : α -> F} {g : α -> G} (hfg : forallᵐ x ∂μ, ‖f x‖₊ = ‖g x‖₊)
  proof: le_antisymm (eLpNorm_mono_nnnorm_ae <| EventuallyEq.le hfg)
    (eLpNorm_mono_nnnorm_ae <| (EventuallyEq.symm hfg).le)

中文:
定理 eLpNorm_congr_nnnorm_ae
  条件: {f : α -> F} {g : α -> G} (hfg : 对任意ᵐ x ∂μ, ‖f x‖₊ = ‖g x‖₊)
  证明: le_antisymm (eLpNorm_mono_nnnorm_ae <| EventuallyEq.le hfg)
    (eLpNorm_mono_nnnorm_ae <| (EventuallyEq.symm hfg).le)

Depends on / 依赖: EventuallyEq, EventuallyEq.le, EventuallyEq.symm, eLpNorm_mono_nnnorm_ae, le_antisymm
-/
theorem eLpNorm_congr_nnnorm_ae {f : α -> F} {g : α -> G} (hfg : forallᵐ x ∂μ, ‖f x‖₊ = ‖g x‖₊) :
    eLpNorm f p μ = eLpNorm g p μ :=
  le_antisymm (eLpNorm_mono_nnnorm_ae <| EventuallyEq.le hfg)
    (eLpNorm_mono_nnnorm_ae <| (EventuallyEq.symm hfg).le)

/--
theorem `eLpNorm_congr_norm_ae` / 定理 `eLpNorm_congr_norm_ae`

English:
theorem eLpNorm_congr_norm_ae
  given: {f : α -> F} {g : α -> G} (hfg : forallᵐ x ∂μ, ‖f x‖ = ‖g x‖)
  proof: eLpNorm_congr_nnnorm_ae hfg.mono fun _x hx => NNReal.eq hx

中文:
定理 eLpNorm_congr_norm_ae
  条件: {f : α -> F} {g : α -> G} (hfg : 对任意ᵐ x ∂μ, ‖f x‖ = ‖g x‖)
  证明: eLpNorm_congr_nnnorm_ae hfg.mono fun _x hx => NNReal.eq hx

Depends on / 依赖: NNReal, NNReal.eq, eLpNorm_congr_nnnorm_ae, hfg.mono
-/
theorem eLpNorm_congr_norm_ae {f : α -> F} {g : α -> G} (hfg : forallᵐ x ∂μ, ‖f x‖ = ‖g x‖) :
    eLpNorm f p μ = eLpNorm g p μ :=
eLpNorm_congr_nnnorm_ae hfg.mono fun _x hx => NNReal.eq hx

open scoped symmDiff in
/--
theorem `eLpNorm_indicator_sub_indicator` / 定理 `eLpNorm_indicator_sub_indicator`

English:
theorem eLpNorm_indicator_sub_indicator
  given: (s t : Set α) (f : α -> E)
  proof: eLpNorm_congr_norm_ae ae_of_all _ fun x => by simp [Set.apply_indicator_symmDiff norm_neg]

@[simp]

中文:
定理 eLpNorm_indicator_sub_indicator
  条件: (s t : 集合 α) (f : α -> E)
  证明: eLpNorm_congr_norm_ae ae_of_all _ fun x => by simp [Set.apply_indicator_symmDiff norm_neg]

@[simp]

Depends on / 依赖: Set.apply_indicator_symmDiff, ae_of_all, apply_indicator_symmDiff, eLpNorm_congr_norm_ae, norm_neg
-/
theorem eLpNorm_indicator_sub_indicator (s t : Set α) (f : α -> E) :
    eLpNorm (s.indicator f - t.indicator f) p μ = eLpNorm ((s ∆ t).indicator f) p μ :=
eLpNorm_congr_norm_ae ae_of_all _ fun x => by simp [Set.apply_indicator_symmDiff norm_neg]

@[simp]
/--
theorem `eLpNorm'_norm` / 定理 `eLpNorm'_norm`

English:
theorem eLpNorm'_norm
  given: {f : α -> F}
  statement: eLpNorm' (fun a => ‖f a‖) q μ = eLpNorm' f q μ
  proof: by
  simp [eLpNorm'_eq_lintegral_enorm]

@[simp]

中文:
定理 eLpNorm'_norm
  条件: {f : α -> F}
  结论: eLpNorm' (fun a => ‖f a‖) q μ = eLpNorm' f q μ
  证明: by
  simp [eLpNorm'_eq_lintegral_enorm]

@[simp]
-/
theorem eLpNorm'_norm {f : α -> F} : eLpNorm' (fun a => ‖f a‖) q μ = eLpNorm' f q μ := by
  simp [eLpNorm'_eq_lintegral_enorm]

@[simp]
/--
theorem `eLpNorm'_enorm` / 定理 `eLpNorm'_enorm`

English:
theorem eLpNorm'_enorm
  given: {f : α -> ε}
  statement: eLpNorm' (fun a => ‖f a‖ₑ) q μ = eLpNorm' f q μ
  proof: by
  simp [eLpNorm'_eq_lintegral_enorm]

@[simp]

中文:
定理 eLpNorm'_enorm
  条件: {f : α -> ε}
  结论: eLpNorm' (fun a => ‖f a‖ₑ) q μ = eLpNorm' f q μ
  证明: by
  simp [eLpNorm'_eq_lintegral_enorm]

@[simp]
-/
theorem eLpNorm'_enorm {f : α -> ε} : eLpNorm' (fun a => ‖f a‖ₑ) q μ = eLpNorm' f q μ := by
  simp [eLpNorm'_eq_lintegral_enorm]

@[simp]
/--
theorem `eLpNorm_norm` / 定理 `eLpNorm_norm`

English:
theorem eLpNorm_norm
  given: (f : α -> F)
  statement: eLpNorm (fun x => ‖f x‖) p μ = eLpNorm f p μ
  proof: eLpNorm_congr_norm_ae Eventually.of_forall fun _ => norm_norm _

@[simp]

中文:
定理 eLpNorm_norm
  条件: (f : α -> F)
  结论: eLpNorm (fun x => ‖f x‖) p μ = eLpNorm f p μ
  证明: eLpNorm_congr_norm_ae Eventually.of_forall fun _ => norm_norm _

@[simp]

Depends on / 依赖: Eventually, Eventually.of_forall, eLpNorm_congr_norm_ae, norm_norm, of_forall
-/
theorem eLpNorm_norm (f : α -> F) : eLpNorm (fun x => ‖f x‖) p μ = eLpNorm f p μ :=
eLpNorm_congr_norm_ae Eventually.of_forall fun _ => norm_norm _

@[simp]
/--
theorem `eLpNorm_enorm` / 定理 `eLpNorm_enorm`

English:
theorem eLpNorm_enorm
  given: (f : α -> ε)
  statement: eLpNorm (fun x => ‖f x‖ₑ) p μ = eLpNorm f p μ
  proof: eLpNorm_congr_enorm_ae Eventually.of_forall fun _ => enorm_enorm _

中文:
定理 eLpNorm_enorm
  条件: (f : α -> ε)
  结论: eLpNorm (fun x => ‖f x‖ₑ) p μ = eLpNorm f p μ
  证明: eLpNorm_congr_enorm_ae Eventually.of_forall fun _ => enorm_enorm _

Depends on / 依赖: Eventually, Eventually.of_forall, eLpNorm_congr_enorm_ae, enorm_enorm, of_forall
-/
theorem eLpNorm_enorm (f : α -> ε) : eLpNorm (fun x => ‖f x‖ₑ) p μ = eLpNorm f p μ :=
eLpNorm_congr_enorm_ae Eventually.of_forall fun _ => enorm_enorm _

/--
theorem `eLpNorm'_enorm_rpow` / 定理 `eLpNorm'_enorm_rpow`

English:
theorem eLpNorm'_enorm_rpow
  given: (f : α -> ε) (p q : Real) (hq_pos : 0 < q)
  proof: by
  simp_rw [eLpNorm', ← ENNReal.rpow_mul, ← one_div_mul_one_div, one_div,
    mul_assoc, inv_mul_cancel₀ hq_pos.ne.symm, mul_one, enorm_eq_self, ← ENNReal.rpow_mul, mul_comm]

中文:
定理 eLpNorm'_enorm_rpow
  条件: (f : α -> ε) (p q : 实数) (hq_pos : 0 < q)
  证明: by
  simp_rw [eLpNorm', ← ENNReal.rpow_mul, ← one_div_mul_one_div, one_div,
    mul_assoc, inv_mul_cancel₀ hq_pos.ne.symm, mul_one, enorm_eq_self, ← ENNReal.rpow_mul, mul_comm]
-/
theorem eLpNorm'_enorm_rpow (f : α -> ε) (p q : Real) (hq_pos : 0 < q) :
    eLpNorm' (‖f ·‖ₑ ^ q) p μ = eLpNorm' f (p * q) μ ^ q := by
  simp_rw [eLpNorm', ← ENNReal.rpow_mul, ← one_div_mul_one_div, one_div,
    mul_assoc, inv_mul_cancel₀ hq_pos.ne.symm, mul_one, enorm_eq_self, ← ENNReal.rpow_mul, mul_comm]

/--
lemma `eLpNorm_ofReal` / 引理 `eLpNorm_ofReal`

English:
lemma eLpNorm_ofReal
  given: (f : α -> Real) (hf : forallᵐ x ∂μ, 0 <= f x)
  proof: eLpNorm_congr_enorm_ae hf.mono fun _x hx => Real.enorm_ofReal_of_nonneg hx

中文:
引理 eLpNorm_of实数
  条件: (f : α -> 实数) (hf : 对任意ᵐ x ∂μ, 0 <= f x)
  证明: eLpNorm_congr_enorm_ae hf.mono fun _x hx => Real.enorm_ofReal_of_nonneg hx

Depends on / 依赖: Real.enorm_ofReal_of_nonneg, eLpNorm_congr_enorm_ae, enorm_ofReal_of_nonneg, hf.mono
-/
lemma eLpNorm_ofReal (f : α -> Real) (hf : forallᵐ x ∂μ, 0 <= f x) :
    eLpNorm (ENNReal.ofReal ∘ f) p μ = eLpNorm f p μ :=
eLpNorm_congr_enorm_ae hf.mono fun _x hx => Real.enorm_ofReal_of_nonneg hx

/--
theorem `eLpNorm'_norm_rpow` / 定理 `eLpNorm'_norm_rpow`

English:
theorem eLpNorm'_norm_rpow
  given: (f : α -> F) (p q : Real) (hq_pos : 0 < q)
  proof: by
  simp_rw [eLpNorm', ← ENNReal.rpow_mul, ← one_div_mul_one_div, one_div,
    mul_assoc, inv_mul_cancel₀ hq_pos.ne.symm, mul_one, ← ofReal_norm,
    Real.norm_eq_abs, abs_eq_self.mpr (Real.rpow_nonneg (norm_nonneg _) _), mul_comm p,
    ← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hq_pos.le, ENNReal.rpow_mul]

中文:
定理 eLpNorm'_norm_rpow
  条件: (f : α -> F) (p q : 实数) (hq_pos : 0 < q)
  证明: by
  simp_rw [eLpNorm', ← ENNReal.rpow_mul, ← one_div_mul_one_div, one_div,
    mul_assoc, inv_mul_cancel₀ hq_pos.ne.symm, mul_one, ← ofReal_norm,
    Real.norm_eq_abs, abs_eq_self.mpr (Real.rpow_nonneg (norm_nonneg _) _), mul_comm p,
    ← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hq_pos.le, ENNReal.rpow_mul]
-/
theorem eLpNorm'_norm_rpow (f : α -> F) (p q : Real) (hq_pos : 0 < q) :
    eLpNorm' (fun x => ‖f x‖ ^ q) p μ = eLpNorm' f (p * q) μ ^ q := by
  simp_rw [eLpNorm', ← ENNReal.rpow_mul, ← one_div_mul_one_div, one_div,
    mul_assoc, inv_mul_cancel₀ hq_pos.ne.symm, mul_one, ← ofReal_norm,
    Real.norm_eq_abs, abs_eq_self.mpr (Real.rpow_nonneg (norm_nonneg _) _), mul_comm p,
    ← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hq_pos.le, ENNReal.rpow_mul]

/--
theorem `eLpNorm_enorm_rpow` / 定理 `eLpNorm_enorm_rpow`

English:
theorem eLpNorm_enorm_rpow
  given: (f : α -> ε) (hq_pos : 0 < q)
  proof: by
  by_cases h0 : p = 0
  · simp [h0, ENNReal.zero_rpow_of_pos hq_pos]
  by_cases hp_top : p = ∞
  · simp only [hp_top, eLpNorm_exponent_top, ENNReal.top_mul', hq_pos.not_ge,
      ENNReal.ofReal_eq_zero, if_false, eLpNorm_exponent_top, eLpNormEssSup_eq_essSup_enorm]
    have h_rpow : essSup (‖‖f ·‖ₑ ^ q‖ₑ) μ = essSup (‖f ·‖ₑ ^ q) μ := by congr
    rw [h_rpow]
    have h_rpow_mono := ENNReal.strictMono_rpow_of_pos hq_pos
    have h_rpow_surj := (ENNReal.rpow_left_bijective hq_pos.ne.symm).2
    let iso := h_rpow_mono.orderIsoOfSurjective _ h_rpow_surj
    exact (iso.essSup_apply (fun x => ‖f x‖ₑ) μ).symm
  rw [eLpNorm_eq_eLpNorm' h0 hp_top]; rw [eLpNorm_eq_eLpNorm' _ (by finiteness)]
  swap
  · refine mul_ne_zero h0 ?_
    rwa [Ne, ENNReal.ofReal_eq_zero, not_le]
  rw [ENNReal.toReal_mul]; rw [ENNReal.toReal_ofReal hq_pos.le]
  exact eLpNorm'_enorm_rpow f p.toReal q hq_pos

中文:
定理 eLpNorm_enorm_rpow
  条件: (f : α -> ε) (hq_pos : 0 < q)
  证明: by
  by_cases h0 : p = 0
  · simp [h0, ENNReal.zero_rpow_of_pos hq_pos]
  by_cases hp_top : p = ∞
  · simp only [hp_top, eLpNorm_exponent_top, ENNReal.top_mul', hq_pos.not_ge,
      ENNReal.ofReal_eq_zero, if_false, eLpNorm_exponent_top, eLpNormEssSup_eq_essSup_enorm]
    have h_rpow : essSup (‖‖f ·‖ₑ ^ q‖ₑ) μ = essSup (‖f ·‖ₑ ^ q) μ := by congr
    rw [h_rpow]
    have h_rpow_mono := ENNReal.strictMono_rpow_of_pos hq_pos
    have h_rpow_surj := (ENNReal.rpow_left_bijective hq_pos.ne.symm).2
    let iso := h_rpow_mono.orderIsoOfSurjective _ h_rpow_surj
    exact (iso.essSup_apply (fun x => ‖f x‖ₑ) μ).symm
  rw [eLpNorm_eq_eLpNorm' h0 hp_top]; rw [eLpNorm_eq_eLpNorm' _ (by finiteness)]
  swap
  · refine mul_ne_zero h0 ?_
    rwa [Ne, ENNReal.ofReal_eq_zero, not_le]
  rw [ENNReal.toReal_mul]; rw [ENNReal.toReal_ofReal hq_pos.le]
  exact eLpNorm'_enorm_rpow f p.toReal q hq_pos

Depends on / 依赖: ENNReal, ENNReal.ofReal_eq_zero, ENNReal.rpow_left_bijective, ENNReal.strictMono_rpow_of_pos, ENNReal.top_mul, ENNReal.zero_rpow_of_pos, eLpNormEssSup_eq_essSup_enorm, eLpNorm_exponent_top, essSup, h_rpow, h_rpow_mono, h_rpow_mono.orderIsoOf, h_rpow_surj, hp_top, hq_pos, hq_pos.ne.symm, hq_pos.not_ge, if_false, not_ge, ofReal_eq_zero
-/
theorem eLpNorm_enorm_rpow (f : α -> ε) (hq_pos : 0 < q) :
    eLpNorm (‖f ·‖ₑ ^ q) p μ = eLpNorm f (p * ENNReal.ofReal q) μ ^ q := by
  by_cases h0 : p = 0
  · simp [h0, ENNReal.zero_rpow_of_pos hq_pos]
  by_cases hp_top : p = ∞
  · simp only [hp_top, eLpNorm_exponent_top, ENNReal.top_mul', hq_pos.not_ge,
      ENNReal.ofReal_eq_zero, if_false, eLpNorm_exponent_top, eLpNormEssSup_eq_essSup_enorm]
    have h_rpow : essSup (‖‖f ·‖ₑ ^ q‖ₑ) μ = essSup (‖f ·‖ₑ ^ q) μ := by congr
    rw [h_rpow]
    have h_rpow_mono := ENNReal.strictMono_rpow_of_pos hq_pos
    have h_rpow_surj := (ENNReal.rpow_left_bijective hq_pos.ne.symm).2
    let iso := h_rpow_mono.orderIsoOfSurjective _ h_rpow_surj
    exact (iso.essSup_apply (fun x => ‖f x‖ₑ) μ).symm
  rw [eLpNorm_eq_eLpNorm' h0 hp_top]; rw [eLpNorm_eq_eLpNorm' _ (by finiteness)]
  swap
  · refine mul_ne_zero h0 ?_
    rwa [Ne, ENNReal.ofReal_eq_zero, not_le]
  rw [ENNReal.toReal_mul]; rw [ENNReal.toReal_ofReal hq_pos.le]
  exact eLpNorm'_enorm_rpow f p.toReal q hq_pos

/--
theorem `eLpNorm_norm_rpow` / 定理 `eLpNorm_norm_rpow`

English:
theorem eLpNorm_norm_rpow
  given: (f : α -> F) (hq_pos : 0 < q)
  proof: by
  rw [← eLpNorm_enorm_rpow f hq_pos]
  symm
  convert! eLpNorm_ofReal (fun x => ‖f x‖ ^ q) (by filter_upwards with x using by positivity)
  rw [Function.comp_apply]; rw [← ofReal_norm]
  exact ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity)

中文:
定理 eLpNorm_norm_rpow
  条件: (f : α -> F) (hq_pos : 0 < q)
  证明: by
  rw [← eLpNorm_enorm_rpow f hq_pos]
  symm
  convert! eLpNorm_ofReal (fun x => ‖f x‖ ^ q) (by filter_upwards with x using by positivity)
  rw [Function.comp_apply]; rw [← ofReal_norm]
  exact ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity)

Depends on / 依赖: ENNReal, ENNReal.ofReal_rpow_of_nonneg, Function, Function.comp_apply, comp_apply, convert, eLpNorm_enorm_rpow, eLpNorm_ofReal, filter_upwards, hq_pos, ofReal_norm, ofReal_rpow_of_nonneg
-/
theorem eLpNorm_norm_rpow (f : α -> F) (hq_pos : 0 < q) :
    eLpNorm (fun x => ‖f x‖ ^ q) p μ = eLpNorm f (p * ENNReal.ofReal q) μ ^ q := by
  rw [← eLpNorm_enorm_rpow f hq_pos]
  symm
  convert! eLpNorm_ofReal (fun x => ‖f x‖ ^ q) (by filter_upwards with x using by positivity)
  rw [Function.comp_apply]; rw [← ofReal_norm]
  exact ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity)

/--
theorem `eLpNorm_congr_ae` / 定理 `eLpNorm_congr_ae`

English:
theorem eLpNorm_congr_ae
  given: {f g : α -> ε} (hfg : f =ᵐ[μ] g)
  statement: eLpNorm f p μ = eLpNorm g p μ
  proof: eLpNorm_congr_enorm_ae hfg.mono fun _x hx => hx ▸ rfl

中文:
定理 eLpNorm_congr_ae
  条件: {f g : α -> ε} (hfg : f =ᵐ[μ] g)
  结论: eLpNorm f p μ = eLpNorm g p μ
  证明: eLpNorm_congr_enorm_ae hfg.mono fun _x hx => hx ▸ rfl

Depends on / 依赖: eLpNorm_congr_enorm_ae, hfg.mono
-/
theorem eLpNorm_congr_ae {f g : α -> ε} (hfg : f =ᵐ[μ] g) : eLpNorm f p μ = eLpNorm g p μ :=
eLpNorm_congr_enorm_ae hfg.mono fun _x hx => hx ▸ rfl

/--
theorem `memLp_congr_ae` / 定理 `memLp_congr_ae`

English:
theorem memLp_congr_ae
  given: [TopologicalSpace ε] {f g : α -> ε} (hfg : f =ᵐ[μ] g)
  proof: by
  simp only [MemLp, eLpNorm_congr_ae hfg, aestronglyMeasurable_congr hfg]

中文:
定理 memLp_congr_ae
  条件: [拓扑空间 ε] {f g : α -> ε} (hfg : f =ᵐ[μ] g)
  证明: by
  simp only [MemLp, eLpNorm_congr_ae hfg, aestronglyMeasurable_congr hfg]

Depends on / 依赖: aestronglyMeasurable_congr, eLpNorm_congr_ae
-/
theorem memLp_congr_ae [TopologicalSpace ε] {f g : α -> ε} (hfg : f =ᵐ[μ] g) :
    MemLp f p μ ↔ MemLp g p μ := by
  simp only [MemLp, eLpNorm_congr_ae hfg, aestronglyMeasurable_congr hfg]

/--
theorem `MemLp.ae_eq` / 定理 `MemLp.ae_eq`

English:
theorem MemLp.ae_eq
  given: [TopologicalSpace ε] {f g : α -> ε} (hfg : f =ᵐ[μ] g) (hf_Lp : MemLp f p μ)
  proof: (memLp_congr_ae hfg).1 hf_Lp

中文:
定理 MemLp.ae_eq
  条件: [拓扑空间 ε] {f g : α -> ε} (hfg : f =ᵐ[μ] g) (hf_Lp : MemLp f p μ)
  证明: (memLp_congr_ae hfg).1 hf_Lp

Depends on / 依赖: hf_Lp, memLp_congr_ae
-/
theorem MemLp.ae_eq [TopologicalSpace ε] {f g : α -> ε} (hfg : f =ᵐ[μ] g) (hf_Lp : MemLp f p μ) :
    MemLp g p μ :=
  (memLp_congr_ae hfg).1 hf_Lp

section ContinuousENorm

variable {ε ε' : Type*}
  [TopologicalSpace ε] [TopologicalSpace ε'] [ContinuousENorm ε] [ContinuousENorm ε']

/--
theorem `MemLp.of_le_enorm` / 定理 `MemLp.of_le_enorm`

English:
theorem MemLp.of_le_enorm
  statement: {f : α -> ε} {g : α -> ε'} (hg : MemLp g p μ)
  proof: ⟨hf, (eLpNorm_mono_enorm_ae hfg).trans_lt (by finiteness)⟩

中文:
定理 MemLp.of_le_enorm
  结论: {f : α -> ε} {g : α -> ε'} (hg : MemLp g p μ)
  证明: ⟨hf, (eLpNorm_mono_enorm_ae hfg).trans_lt (by finiteness)⟩

Depends on / 依赖: eLpNorm_mono_enorm_ae, finiteness, trans_lt
-/
theorem MemLp.of_le_enorm {f : α -> ε} {g : α -> ε'} (hg : MemLp g p μ)
    (hf : AEStronglyMeasurable f μ) (hfg : forallᵐ x ∂μ, ‖f x‖ₑ <= ‖g x‖ₑ) : MemLp f p μ :=
  ⟨hf, (eLpNorm_mono_enorm_ae hfg).trans_lt (by finiteness)⟩

/--
theorem `MemLp.of_le` / 定理 `MemLp.of_le`

English:
theorem MemLp.of_le
  statement: {f : α -> E} {g : α -> F} (hg : MemLp g p μ) (hf : AEStronglyMeasurable f μ)
  proof: ⟨hf, (eLpNorm_mono_ae hfg).trans_lt (by finiteness)⟩

alias MemLp.mono := MemLp.of_le

中文:
定理 MemLp.of_le
  结论: {f : α -> E} {g : α -> F} (hg : MemLp g p μ) (hf : AEStronglyMeasurable f μ)
  证明: ⟨hf, (eLpNorm_mono_ae hfg).trans_lt (by finiteness)⟩

alias MemLp.mono := MemLp.of_le

Depends on / 依赖: eLpNorm_mono_ae, finiteness, trans_lt
-/
theorem MemLp.of_le {f : α -> E} {g : α -> F} (hg : MemLp g p μ) (hf : AEStronglyMeasurable f μ)
    (hfg : forallᵐ x ∂μ, ‖f x‖ <= ‖g x‖) : MemLp f p μ :=
  ⟨hf, (eLpNorm_mono_ae hfg).trans_lt (by finiteness)⟩

alias MemLp.mono := MemLp.of_le

/--
theorem `MemLp.mono'_enorm` / 定理 `MemLp.mono'_enorm`

English:
theorem MemLp.mono'_enorm
  statement: {f : α -> ε} {g : α -> Real>=0∞}
  proof: MemLp.of_le_enorm hg hf h.mono fun _x hx => le_trans hx le_rfl

中文:
定理 MemLp.mono'_enorm
  结论: {f : α -> ε} {g : α -> 实数>=0∞}
  证明: MemLp.of_le_enorm hg hf h.mono fun _x hx => le_trans hx le_rfl

Depends on / 依赖: MemLp.of_le_enorm, h.mono, le_rfl, le_trans, of_le_enorm
-/
theorem MemLp.mono'_enorm {f : α -> ε} {g : α -> Real>=0∞}
    (hg : MemLp g p μ) (hf : AEStronglyMeasurable f μ) (h : forallᵐ a ∂μ, ‖f a‖ₑ <= g a) : MemLp f p μ :=
MemLp.of_le_enorm hg hf h.mono fun _x hx => le_trans hx le_rfl

/--
theorem `MemLp.mono'` / 定理 `MemLp.mono'`

English:
theorem MemLp.mono'
  statement: {f : α -> E} {g : α -> Real} (hg : MemLp g p μ) (hf : AEStronglyMeasurable f μ)
  proof: hg.of_le hf h.mono fun _x hx => le_trans hx (le_abs_self _)

中文:
定理 MemLp.mono'
  结论: {f : α -> E} {g : α -> 实数} (hg : MemLp g p μ) (hf : AEStronglyMeasurable f μ)
  证明: hg.of_le hf h.mono fun _x hx => le_trans hx (le_abs_self _)
-/
theorem MemLp.mono' {f : α -> E} {g : α -> Real} (hg : MemLp g p μ) (hf : AEStronglyMeasurable f μ)
    (h : forallᵐ a ∂μ, ‖f a‖ <= g a) : MemLp f p μ :=
hg.of_le hf h.mono fun _x hx => le_trans hx (le_abs_self _)

/--
theorem `MemLp.congr_enorm` / 定理 `MemLp.congr_enorm`

English:
theorem MemLp.congr_enorm
  statement: {f : α -> ε} {g : α -> ε'} (hf : MemLp f p μ)
  proof: hf.of_le_enorm hg EventuallyEq.le EventuallyEq.symm h

中文:
定理 MemLp.congr_enorm
  结论: {f : α -> ε} {g : α -> ε'} (hf : MemLp f p μ)
  证明: hf.of_le_enorm hg EventuallyEq.le EventuallyEq.symm h

Depends on / 依赖: EventuallyEq, EventuallyEq.le, EventuallyEq.symm, hf.of_le_enorm, of_le_enorm
-/
theorem MemLp.congr_enorm {f : α -> ε} {g : α -> ε'} (hf : MemLp f p μ)
    (hg : AEStronglyMeasurable g μ) (h : forallᵐ a ∂μ, ‖f a‖ₑ = ‖g a‖ₑ) : MemLp g p μ :=
hf.of_le_enorm hg EventuallyEq.le EventuallyEq.symm h

/--
theorem `MemLp.congr_norm` / 定理 `MemLp.congr_norm`

English:
theorem MemLp.congr_norm
  statement: {f : α -> E} {g : α -> F} (hf : MemLp f p μ) (hg : AEStronglyMeasurable g μ)
  proof: hf.mono hg EventuallyEq.le EventuallyEq.symm h

中文:
定理 MemLp.congr_norm
  结论: {f : α -> E} {g : α -> F} (hf : MemLp f p μ) (hg : AEStronglyMeasurable g μ)
  证明: hf.mono hg EventuallyEq.le EventuallyEq.symm h

Depends on / 依赖: EventuallyEq, EventuallyEq.le, EventuallyEq.symm, hf.mono
-/
theorem MemLp.congr_norm {f : α -> E} {g : α -> F} (hf : MemLp f p μ) (hg : AEStronglyMeasurable g μ)
    (h : forallᵐ a ∂μ, ‖f a‖ = ‖g a‖) : MemLp g p μ :=
hf.mono hg EventuallyEq.le EventuallyEq.symm h

/--
theorem `memLp_congr_enorm` / 定理 `memLp_congr_enorm`

English:
theorem memLp_congr_enorm
  statement: {f : α -> ε} {g : α -> ε'} (hf : AEStronglyMeasurable f μ)
  proof: ⟨fun h2f => h2f.congr_enorm hg h, fun h2g => h2g.congr_enorm hf EventuallyEq.symm h⟩

中文:
定理 memLp_congr_enorm
  结论: {f : α -> ε} {g : α -> ε'} (hf : AEStronglyMeasurable f μ)
  证明: ⟨fun h2f => h2f.congr_enorm hg h, fun h2g => h2g.congr_enorm hf EventuallyEq.symm h⟩

Depends on / 依赖: EventuallyEq, EventuallyEq.symm, congr_enorm, h2f.congr_enorm, h2g.congr_enorm
-/
theorem memLp_congr_enorm {f : α -> ε} {g : α -> ε'} (hf : AEStronglyMeasurable f μ)
    (hg : AEStronglyMeasurable g μ) (h : forallᵐ a ∂μ, ‖f a‖ₑ = ‖g a‖ₑ) : MemLp f p μ ↔ MemLp g p μ :=
⟨fun h2f => h2f.congr_enorm hg h, fun h2g => h2g.congr_enorm hf EventuallyEq.symm h⟩

/--
theorem `memLp_congr_norm` / 定理 `memLp_congr_norm`

English:
theorem memLp_congr_norm
  statement: {f : α -> E} {g : α -> F} (hf : AEStronglyMeasurable f μ)
  proof: ⟨fun h2f => h2f.congr_norm hg h, fun h2g => h2g.congr_norm hf EventuallyEq.symm h⟩

中文:
定理 memLp_congr_norm
  结论: {f : α -> E} {g : α -> F} (hf : AEStronglyMeasurable f μ)
  证明: ⟨fun h2f => h2f.congr_norm hg h, fun h2g => h2g.congr_norm hf EventuallyEq.symm h⟩

Depends on / 依赖: EventuallyEq, EventuallyEq.symm, congr_norm, h2f.congr_norm, h2g.congr_norm
-/
theorem memLp_congr_norm {f : α -> E} {g : α -> F} (hf : AEStronglyMeasurable f μ)
    (hg : AEStronglyMeasurable g μ) (h : forallᵐ a ∂μ, ‖f a‖ = ‖g a‖) : MemLp f p μ ↔ MemLp g p μ :=
⟨fun h2f => h2f.congr_norm hg h, fun h2g => h2g.congr_norm hf EventuallyEq.symm h⟩

/--
theorem `memLp_top_of_bound_enorm` / 定理 `memLp_top_of_bound_enorm`

English:
theorem memLp_top_of_bound_enorm
  statement: {f : α -> ε} (hf : AEStronglyMeasurable f μ) (C : Real>=0)
  proof: ⟨hf, by
    rw [eLpNorm_exponent_top]
    exact eLpNormEssSup_lt_top_of_ae_enorm_bound hfC⟩

中文:
定理 memLp_top_of_bound_enorm
  结论: {f : α -> ε} (hf : AEStronglyMeasurable f μ) (C : 实数>=0)
  证明: ⟨hf, by
    rw [eLpNorm_exponent_top]
    exact eLpNormEssSup_lt_top_of_ae_enorm_bound hfC⟩

Depends on / 依赖: eLpNormEssSup_lt_top_of_ae_enorm_bound, eLpNorm_exponent_top
-/
theorem memLp_top_of_bound_enorm {f : α -> ε} (hf : AEStronglyMeasurable f μ) (C : Real>=0)
    (hfC : forallᵐ x ∂μ, ‖f x‖ₑ <= C) : MemLp f ∞ μ :=
  ⟨hf, by
    rw [eLpNorm_exponent_top]
    exact eLpNormEssSup_lt_top_of_ae_enorm_bound hfC⟩

/--
theorem `memLp_top_of_bound` / 定理 `memLp_top_of_bound`

English:
theorem memLp_top_of_bound
  statement: {f : α -> E} (hf : AEStronglyMeasurable f μ) (C : Real)
  proof: ⟨hf, by
    rw [eLpNorm_exponent_top]
    exact eLpNormEssSup_lt_top_of_ae_bound hfC⟩

中文:
定理 memLp_top_of_bound
  结论: {f : α -> E} (hf : AEStronglyMeasurable f μ) (C : 实数)
  证明: ⟨hf, by
    rw [eLpNorm_exponent_top]
    exact eLpNormEssSup_lt_top_of_ae_bound hfC⟩

Depends on / 依赖: eLpNormEssSup_lt_top_of_ae_bound, eLpNorm_exponent_top
-/
theorem memLp_top_of_bound {f : α -> E} (hf : AEStronglyMeasurable f μ) (C : Real)
    (hfC : forallᵐ x ∂μ, ‖f x‖ <= C) : MemLp f ∞ μ :=
  ⟨hf, by
    rw [eLpNorm_exponent_top]
    exact eLpNormEssSup_lt_top_of_ae_bound hfC⟩

/--
theorem `MemLp.of_enorm_bound` / 定理 `MemLp.of_enorm_bound`

English:
theorem MemLp.of_enorm_bound
  statement: [IsFiniteMeasure μ] {f : α -> ε} (hf : AEStronglyMeasurable f μ)
  proof: by
apply (memLp_const_enorm hC).of_le_enorm (ε' := Real>=0∞) hf hfC.mono fun _x hx => ?_
  rw [enorm_eq_self]; exact hx

中文:
定理 MemLp.of_enorm_bound
  结论: [是有限测度 μ] {f : α -> ε} (hf : AEStronglyMeasurable f μ)
  证明: by
apply (memLp_const_enorm hC).of_le_enorm (ε' := Real>=0∞) hf hfC.mono fun _x hx => ?_
  rw [enorm_eq_self]; exact hx

Depends on / 依赖: enorm_eq_self, hfC.mono, memLp_const_enorm, of_le_enorm
-/
theorem MemLp.of_enorm_bound [IsFiniteMeasure μ] {f : α -> ε} (hf : AEStronglyMeasurable f μ)
    {C : Real>=0∞} (hC : C != ∞) (hfC : forallᵐ x ∂μ, ‖f x‖ₑ <= C) : MemLp f p μ := by
apply (memLp_const_enorm hC).of_le_enorm (ε' := Real>=0∞) hf hfC.mono fun _x hx => ?_
  rw [enorm_eq_self]; exact hx

/--
theorem `MemLp.of_bound` / 定理 `MemLp.of_bound`

English:
theorem MemLp.of_bound
  statement: [IsFiniteMeasure μ] {f : α -> E} (hf : AEStronglyMeasurable f μ) (C : Real)
  proof: (memLp_const C).of_le hf (hfC.mono fun _x hx => le_trans hx (le_abs_self _))

中文:
定理 MemLp.of_bound
  结论: [是有限测度 μ] {f : α -> E} (hf : AEStronglyMeasurable f μ) (C : 实数)
  证明: (memLp_const C).of_le hf (hfC.mono fun _x hx => le_trans hx (le_abs_self _))

Depends on / 依赖: hfC.mono, le_abs_self, le_trans, memLp_const, of_le
-/
theorem MemLp.of_bound [IsFiniteMeasure μ] {f : α -> E} (hf : AEStronglyMeasurable f μ) (C : Real)
    (hfC : forallᵐ x ∂μ, ‖f x‖ <= C) : MemLp f p μ :=
  (memLp_const C).of_le hf (hfC.mono fun _x hx => le_trans hx (le_abs_self _))

/--
theorem `memLp_of_bounded` / 定理 `memLp_of_bounded`

English:
theorem memLp_of_bounded
  statement: [IsFiniteMeasure μ]
  proof: have ha : forallᵐ x ∂μ, a <= f x := h.mono fun ω h => h.1
  have hb : forallᵐ x ∂μ, f x <= b := h.mono fun ω h => h.2
  (memLp_const (max |a| |b|)).mono' hX (by filter_upwards [ha, hb] with x using abs_le_max_abs_abs)

@[gcongr, mono]

中文:
定理 memLp_of_bounded
  结论: [是有限测度 μ]
  证明: have ha : forallᵐ x ∂μ, a <= f x := h.mono fun ω h => h.1
  have hb : forallᵐ x ∂μ, f x <= b := h.mono fun ω h => h.2
  (memLp_const (max |a| |b|)).mono' hX (by filter_upwards [ha, hb] with x using abs_le_max_abs_abs)

@[gcongr, mono]

Depends on / 依赖: abs_le_max_abs_abs, filter_upwards, h.mono, memLp_const
-/
theorem memLp_of_bounded [IsFiniteMeasure μ]
    {a b : Real} {f : α -> Real} (h : forallᵐ x ∂μ, f x in Set.Icc a b)
    (hX : AEStronglyMeasurable f μ) (p : ENNReal) : MemLp f p μ :=
  have ha : forallᵐ x ∂μ, a <= f x := h.mono fun ω h => h.1
  have hb : forallᵐ x ∂μ, f x <= b := h.mono fun ω h => h.2
  (memLp_const (max |a| |b|)).mono' hX (by filter_upwards [ha, hb] with x using abs_le_max_abs_abs)

@[gcongr, mono]
/--
theorem `eLpNorm'_mono_measure` / 定理 `eLpNorm'_mono_measure`

English:
theorem eLpNorm'_mono_measure
  given: (f : α -> ε) (hμν : ν <= μ) (hq : 0 <= q)
  proof: by
  simp_rw [eLpNorm']
  gcongr

@[gcongr, mono]

中文:
定理 eLpNorm'_mono_measure
  条件: (f : α -> ε) (hμν : ν <= μ) (hq : 0 <= q)
  证明: by
  simp_rw [eLpNorm']
  gcongr

@[gcongr, mono]
-/
theorem eLpNorm'_mono_measure (f : α -> ε) (hμν : ν <= μ) (hq : 0 <= q) :
    eLpNorm' f q ν <= eLpNorm' f q μ := by
  simp_rw [eLpNorm']
  gcongr

@[gcongr, mono]
/--
theorem `eLpNormEssSup_mono_measure` / 定理 `eLpNormEssSup_mono_measure`

English:
theorem eLpNormEssSup_mono_measure
  given: (f : α -> ε) (hμν : ν ≪ μ)
  proof: by
  simp_rw [eLpNormEssSup]
  exact essSup_mono_measure hμν

@[gcongr, mono]

中文:
定理 eLpNormEssSup_mono_measure
  条件: (f : α -> ε) (hμν : ν ≪ μ)
  证明: by
  simp_rw [eLpNormEssSup]
  exact essSup_mono_measure hμν

@[gcongr, mono]

Depends on / 依赖: eLpNormEssSup, essSup_mono_measure, simp_rw
-/
theorem eLpNormEssSup_mono_measure (f : α -> ε) (hμν : ν ≪ μ) :
    eLpNormEssSup f ν <= eLpNormEssSup f μ := by
  simp_rw [eLpNormEssSup]
  exact essSup_mono_measure hμν

@[gcongr, mono]
/--
theorem `eLpNorm_mono_measure` / 定理 `eLpNorm_mono_measure`

English:
theorem eLpNorm_mono_measure
  given: (f : α -> ε) (hμν : ν <= μ)
  statement: eLpNorm f p ν <= eLpNorm f p μ
  proof: by
  by_cases hp0 : p = 0
  · simp [hp0]
  by_cases hp_top : p = ∞
  · simp [hp_top, eLpNormEssSup_mono_measure f (Measure.absolutelyContinuous_of_le hμν)]
  simp_rw [eLpNorm_eq_eLpNorm' hp0 hp_top]
  exact eLpNorm'_mono_measure f hμν ENNReal.toReal_nonneg

中文:
定理 eLpNorm_mono_measure
  条件: (f : α -> ε) (hμν : ν <= μ)
  结论: eLpNorm f p ν <= eLpNorm f p μ
  证明: by
  by_cases hp0 : p = 0
  · simp [hp0]
  by_cases hp_top : p = ∞
  · simp [hp_top, eLpNormEssSup_mono_measure f (Measure.absolutelyContinuous_of_le hμν)]
  simp_rw [eLpNorm_eq_eLpNorm' hp0 hp_top]
  exact eLpNorm'_mono_measure f hμν ENNReal.toReal_nonneg

Depends on / 依赖: ENNReal, ENNReal.toReal_nonneg, Measure, Measure.absolutelyContinuous_of_le, _mono_measure, absolutelyContinuous_of_le, eLpNorm, eLpNormEssSup_mono_measure, eLpNorm_eq_eLpNorm, hp_top, simp_rw, toReal_nonneg
-/
theorem eLpNorm_mono_measure (f : α -> ε) (hμν : ν <= μ) : eLpNorm f p ν <= eLpNorm f p μ := by
  by_cases hp0 : p = 0
  · simp [hp0]
  by_cases hp_top : p = ∞
  · simp [hp_top, eLpNormEssSup_mono_measure f (Measure.absolutelyContinuous_of_le hμν)]
  simp_rw [eLpNorm_eq_eLpNorm' hp0 hp_top]
  exact eLpNorm'_mono_measure f hμν ENNReal.toReal_nonneg

/--
theorem `MemLp.mono_measure` / 定理 `MemLp.mono_measure`

English:
theorem MemLp.mono_measure
  given: {f : α -> ε} (hμν : ν <= μ) (hf : MemLp f p μ)
  proof: ⟨hf.1.mono_measure hμν, (eLpNorm_mono_measure f hμν).trans_lt hf.2⟩

中文:
定理 MemLp.mono_measure
  条件: {f : α -> ε} (hμν : ν <= μ) (hf : MemLp f p μ)
  证明: ⟨hf.1.mono_measure hμν, (eLpNorm_mono_measure f hμν).trans_lt hf.2⟩

Depends on / 依赖: eLpNorm_mono_measure, mono_measure, trans_lt
-/
theorem MemLp.mono_measure {f : α -> ε} (hμν : ν <= μ) (hf : MemLp f p μ) :
    MemLp f p ν :=
  ⟨hf.1.mono_measure hμν, (eLpNorm_mono_measure f hμν).trans_lt hf.2⟩

end ContinuousENorm

section ENormedAddMonoid

variable {ε : Type*} [TopologicalSpace ε] [ENormedAddMonoid ε]

/--
theorem `eLpNorm_restrict_eq_of_support_subset` / 定理 `eLpNorm_restrict_eq_of_support_subset`

English:
theorem eLpNorm_restrict_eq_of_support_subset
  given: {s : Set α} {f : α -> ε} (hsf : f.support subseteq s)
  proof: by
  by_cases hp0 : p = 0
  · simp [hp0]
  by_cases hp_top : p = ∞
  · simp only [hp_top, eLpNorm_exponent_top, eLpNormEssSup_eq_essSup_enorm]
exact ENNReal.essSup_restrict_eq_of_support_subset fun x hx => hsf enorm_ne_zero.1 hx
  · simp_rw [eLpNorm_eq_eLpNorm' hp0 hp_top, eLpNorm'_eq_lintegral_enorm]
    congr 1
    apply setLIntegral_eq_of_support_subset
    have : ¬(p.toReal <= 0) := by simpa only [not_le] using ENNReal.toReal_pos hp0 hp_top
    simpa [this] using hsf

中文:
定理 eLpNorm_restrict_eq_of_support_subset
  条件: {s : 集合 α} {f : α -> ε} (hsf : f.support subseteq s)
  证明: by
  by_cases hp0 : p = 0
  · simp [hp0]
  by_cases hp_top : p = ∞
  · simp only [hp_top, eLpNorm_exponent_top, eLpNormEssSup_eq_essSup_enorm]
exact ENNReal.essSup_restrict_eq_of_support_subset fun x hx => hsf enorm_ne_zero.1 hx
  · simp_rw [eLpNorm_eq_eLpNorm' hp0 hp_top, eLpNorm'_eq_lintegral_enorm]
    congr 1
    apply setLIntegral_eq_of_support_subset
    have : ¬(p.toReal <= 0) := by simpa only [not_le] using ENNReal.toReal_pos hp0 hp_top
    simpa [this] using hsf

Depends on / 依赖: ENNReal, ENNReal.essSup_restrict_eq_of_support_subset, ENNReal.toReal_pos, _eq_lintegral_enorm, eLpNorm, eLpNormEssSup_eq_essSup_enorm, eLpNorm_eq_eLpNorm, eLpNorm_exponent_top, enorm_ne_zero, essSup_restrict_eq_of_support_subset, hp_top, not_le, p.toReal, setLIntegral_eq_of_support_subset, simp_rw, toReal, toReal_pos
-/
theorem eLpNorm_restrict_eq_of_support_subset {s : Set α} {f : α -> ε} (hsf : f.support subseteq s) :
    eLpNorm f p (μ.restrict s) = eLpNorm f p μ := by
  by_cases hp0 : p = 0
  · simp [hp0]
  by_cases hp_top : p = ∞
  · simp only [hp_top, eLpNorm_exponent_top, eLpNormEssSup_eq_essSup_enorm]
exact ENNReal.essSup_restrict_eq_of_support_subset fun x hx => hsf enorm_ne_zero.1 hx
  · simp_rw [eLpNorm_eq_eLpNorm' hp0 hp_top, eLpNorm'_eq_lintegral_enorm]
    congr 1
    apply setLIntegral_eq_of_support_subset
    have : ¬(p.toReal <= 0) := by simpa only [not_le] using ENNReal.toReal_pos hp0 hp_top
    simpa [this] using hsf

end ENormedAddMonoid

section ContinuousENorm

variable {ε : Type*} [TopologicalSpace ε] [ContinuousENorm ε]

/--
theorem `MemLp.restrict` / 定理 `MemLp.restrict`

English:
theorem MemLp.restrict
  given: (s : Set α) {f : α -> ε} (hf : MemLp f p μ)
  proof: hf.mono_measure Measure.restrict_le_self

中文:
定理 MemLp.restrict
  条件: (s : 集合 α) {f : α -> ε} (hf : MemLp f p μ)
  证明: hf.mono_measure Measure.restrict_le_self

Depends on / 依赖: Measure, Measure.restrict_le_self, hf.mono_measure, mono_measure, restrict_le_self
-/
theorem MemLp.restrict (s : Set α) {f : α -> ε} (hf : MemLp f p μ) :
    MemLp f p (μ.restrict s) :=
  hf.mono_measure Measure.restrict_le_self

/--
theorem `eLpNorm'_smul_measure` / 定理 `eLpNorm'_smul_measure`

English:
theorem eLpNorm'_smul_measure
  given: {p : Real} (hp : 0 <= p) {f : α -> ε} (c : Real>=0∞)
  proof: by
  simp [eLpNorm', ENNReal.mul_rpow_of_nonneg, hp]

中文:
定理 eLpNorm'_smul_measure
  条件: {p : 实数} (hp : 0 <= p) {f : α -> ε} (c : 实数>=0∞)
  证明: by
  simp [eLpNorm', ENNReal.mul_rpow_of_nonneg, hp]
-/
theorem eLpNorm'_smul_measure {p : Real} (hp : 0 <= p) {f : α -> ε} (c : Real>=0∞) :
    eLpNorm' f p (c • μ) = c ^ (1 / p) * eLpNorm' f p μ := by
  simp [eLpNorm', ENNReal.mul_rpow_of_nonneg, hp]

end ContinuousENorm

section SMul
variable {R : Type*} [Semiring R] [IsDomain R] [Module R Real>=0∞] [IsScalarTower R Real>=0∞ Real>=0∞]
  [Module.IsTorsionFree R Real>=0∞] {c : R}

/--
lemma `eLpNormEssSup_smul_measure` / 引理 `eLpNormEssSup_smul_measure`

English:
lemma eLpNormEssSup_smul_measure
  given: (hc : c != 0) (f : α -> ε)
  proof: by
  simp_rw [eLpNormEssSup]
  exact essSup_smul_measure hc _

中文:
引理 eLpNormEssSup_smul_measure
  条件: (hc : c != 0) (f : α -> ε)
  证明: by
  simp_rw [eLpNormEssSup]
  exact essSup_smul_measure hc _
-/
@[simp] lemma eLpNormEssSup_smul_measure (hc : c != 0) (f : α -> ε) :
    eLpNormEssSup f (c • μ) = eLpNormEssSup f μ := by
  simp_rw [eLpNormEssSup]
  exact essSup_smul_measure hc _

end SMul

/--
lemma `eLpNormEssSup_ennreal_smul_measure` / 引理 `eLpNormEssSup_ennreal_smul_measure`

English:
lemma eLpNormEssSup_ennreal_smul_measure
  given: {c : Real>=0∞} (hc : c != 0) (f : α -> ε)
  proof: by
  simp_rw [eLpNormEssSup]; exact essSup_ennreal_smul_measure hc _

中文:
引理 eLpNormEssSup_ennreal_smul_measure
  条件: {c : 实数>=0∞} (hc : c != 0) (f : α -> ε)
  证明: by
  simp_rw [eLpNormEssSup]; exact essSup_ennreal_smul_measure hc _
-/
@[simp] lemma eLpNormEssSup_ennreal_smul_measure {c : Real>=0∞} (hc : c != 0) (f : α -> ε) :
    eLpNormEssSup f (c • μ) = eLpNormEssSup f μ := by
  simp_rw [eLpNormEssSup]; exact essSup_ennreal_smul_measure hc _

section ContinuousENorm

variable {ε : Type*} [TopologicalSpace ε] [ContinuousENorm ε]

/--
theorem `eLpNorm_smul_measure_of_ne_zero_of_ne_top` / 定理 `eLpNorm_smul_measure_of_ne_zero_of_ne_top`

English:
theorem eLpNorm_smul_measure_of_ne_zero_of_ne_top
  statement: {p : Real>=0∞} (hp_ne_zero : p != 0)
  proof: by
  simp_rw [eLpNorm_eq_eLpNorm' hp_ne_zero hp_ne_top]
  rw [eLpNorm'_smul_measure ENNReal.toReal_nonneg]
  congr
  simp_rw [one_div]
  rw [ENNReal.toReal_inv]

中文:
定理 eLpNorm_smul_measure_of_ne_zero_of_ne_top
  结论: {p : 实数>=0∞} (hp_ne_zero : p != 0)
  证明: by
  simp_rw [eLpNorm_eq_eLpNorm' hp_ne_zero hp_ne_top]
  rw [eLpNorm'_smul_measure ENNReal.toReal_nonneg]
  congr
  simp_rw [one_div]
  rw [ENNReal.toReal_inv]
-/
private theorem eLpNorm_smul_measure_of_ne_zero_of_ne_top {p : Real>=0∞} (hp_ne_zero : p != 0)
    (hp_ne_top : p != ∞) {f : α -> ε} (c : Real>=0∞) :
    eLpNorm f p (c • μ) = c ^ (1 / p).toReal • eLpNorm f p μ := by
  simp_rw [eLpNorm_eq_eLpNorm' hp_ne_zero hp_ne_top]
  rw [eLpNorm'_smul_measure ENNReal.toReal_nonneg]
  congr
  simp_rw [one_div]
  rw [ENNReal.toReal_inv]

/--
theorem `eLpNorm_smul_measure_of_ne_zero` / 定理 `eLpNorm_smul_measure_of_ne_zero`

English:
theorem eLpNorm_smul_measure_of_ne_zero
  statement: {c : Real>=0∞} (hc : c != 0) (f : α -> ε) (p : Real>=0∞)
  proof: by
  by_cases hp0 : p = 0
  · simp [hp0]
  by_cases hp_top : p = ∞
  · simp [*]
  exact eLpNorm_smul_measure_of_ne_zero_of_ne_top hp0 hp_top c

中文:
定理 eLpNorm_smul_measure_of_ne_zero
  结论: {c : 实数>=0∞} (hc : c != 0) (f : α -> ε) (p : 实数>=0∞)
  证明: by
  by_cases hp0 : p = 0
  · simp [hp0]
  by_cases hp_top : p = ∞
  · simp [*]
  exact eLpNorm_smul_measure_of_ne_zero_of_ne_top hp0 hp_top c

Depends on / 依赖: eLpNorm_smul_measure_of_ne_zero_of_ne_top, hp_top
-/
theorem eLpNorm_smul_measure_of_ne_zero {c : Real>=0∞} (hc : c != 0) (f : α -> ε) (p : Real>=0∞)
    (μ : Measure α) : eLpNorm f p (c • μ) = c ^ (1 / p).toReal • eLpNorm f p μ := by
  by_cases hp0 : p = 0
  · simp [hp0]
  by_cases hp_top : p = ∞
  · simp [*]
  exact eLpNorm_smul_measure_of_ne_zero_of_ne_top hp0 hp_top c

/--
theorem `eLpNorm_smul_measure_le` / 定理 `eLpNorm_smul_measure_le`

English:
theorem eLpNorm_smul_measure_le
  given: (c : Real>=0∞) (f : α -> ε) (p : Real>=0∞) (μ : Measure α)
  proof: by
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  · exact (eLpNorm_smul_measure_of_ne_zero hc f p μ).le

中文:
定理 eLpNorm_smul_measure_le
  条件: (c : 实数>=0∞) (f : α -> ε) (p : 实数>=0∞) (μ : 测度 α)
  证明: by
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  · exact (eLpNorm_smul_measure_of_ne_zero hc f p μ).le

Depends on / 依赖: eLpNorm_smul_measure_of_ne_zero, eq_or_ne
-/
theorem eLpNorm_smul_measure_le (c : Real>=0∞) (f : α -> ε) (p : Real>=0∞) (μ : Measure α) :
    eLpNorm f p (c • μ) <= c ^ (1 / p).toReal • eLpNorm f p μ := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  · exact (eLpNorm_smul_measure_of_ne_zero hc f p μ).le

/--
lemma `eLpNorm_smul_measure_of_ne_zero'` / 引理 `eLpNorm_smul_measure_of_ne_zero'`

English:
lemma eLpNorm_smul_measure_of_ne_zero'
  statement: {c : Real>=0} (hc : c != 0) (f : α -> ε) (p : Real>=0∞)
  proof: (eLpNorm_smul_measure_of_ne_zero (ENNReal.coe_ne_zero.2 hc) ..).trans (by simp; norm_cast)

中文:
引理 eLpNorm_smul_measure_of_ne_zero'
  结论: {c : 实数>=0} (hc : c != 0) (f : α -> ε) (p : 实数>=0∞)
  证明: (eLpNorm_smul_measure_of_ne_zero (ENNReal.coe_ne_zero.2 hc) ..).trans (by simp; norm_cast)

Depends on / 依赖: ENNReal, ENNReal.coe_ne_zero, coe_ne_zero, eLpNorm_smul_measure_of_ne_zero
-/
lemma eLpNorm_smul_measure_of_ne_zero' {c : Real>=0} (hc : c != 0) (f : α -> ε) (p : Real>=0∞)
    (μ : Measure α) : eLpNorm f p (c • μ) = c ^ p.toReal⁻¹ • eLpNorm f p μ :=
  (eLpNorm_smul_measure_of_ne_zero (ENNReal.coe_ne_zero.2 hc) ..).trans (by simp; norm_cast)

/--
theorem `eLpNorm_smul_measure_of_ne_top` / 定理 `eLpNorm_smul_measure_of_ne_top`

English:
theorem eLpNorm_smul_measure_of_ne_top
  given: {p : Real>=0∞} (hp_ne_top : p != ∞) (f : α -> ε) (c : Real>=0∞)
  proof: by
  by_cases hp0 : p = 0
  · simp [hp0]
  · exact eLpNorm_smul_measure_of_ne_zero_of_ne_top hp0 hp_ne_top c

中文:
定理 eLpNorm_smul_measure_of_ne_top
  条件: {p : 实数>=0∞} (hp_ne_top : p != ∞) (f : α -> ε) (c : 实数>=0∞)
  证明: by
  by_cases hp0 : p = 0
  · simp [hp0]
  · exact eLpNorm_smul_measure_of_ne_zero_of_ne_top hp0 hp_ne_top c

Depends on / 依赖: eLpNorm_smul_measure_of_ne_zero_of_ne_top, hp_ne_top
-/
theorem eLpNorm_smul_measure_of_ne_top {p : Real>=0∞} (hp_ne_top : p != ∞) (f : α -> ε) (c : Real>=0∞) :
    eLpNorm f p (c • μ) = c ^ (1 / p).toReal • eLpNorm f p μ := by
  by_cases hp0 : p = 0
  · simp [hp0]
  · exact eLpNorm_smul_measure_of_ne_zero_of_ne_top hp0 hp_ne_top c

/--
lemma `eLpNorm_smul_measure_of_ne_top'` / 引理 `eLpNorm_smul_measure_of_ne_top'`

English:
lemma eLpNorm_smul_measure_of_ne_top'
  given: (hp : p != ∞) (c : Real>=0) (f : α -> ε)
  proof: by
  have : 0 <= p.toReal⁻¹ := by positivity
  refine (eLpNorm_smul_measure_of_ne_top hp ..).trans ?_
  simp [ENNReal.smul_def, ENNReal.coe_rpow_of_nonneg, this]

中文:
引理 eLpNorm_smul_measure_of_ne_top'
  条件: (hp : p != ∞) (c : 实数>=0) (f : α -> ε)
  证明: by
  have : 0 <= p.toReal⁻¹ := by positivity
  refine (eLpNorm_smul_measure_of_ne_top hp ..).trans ?_
  simp [ENNReal.smul_def, ENNReal.coe_rpow_of_nonneg, this]

Depends on / 依赖: ENNReal, ENNReal.coe_rpow_of_nonneg, ENNReal.smul_def, coe_rpow_of_nonneg, eLpNorm_smul_measure_of_ne_top, p.toReal, smul_def, toReal
-/
lemma eLpNorm_smul_measure_of_ne_top' (hp : p != ∞) (c : Real>=0) (f : α -> ε) :
    eLpNorm f p (c • μ) = c ^ p.toReal⁻¹ • eLpNorm f p μ := by
  have : 0 <= p.toReal⁻¹ := by positivity
  refine (eLpNorm_smul_measure_of_ne_top hp ..).trans ?_
  simp [ENNReal.smul_def, ENNReal.coe_rpow_of_nonneg, this]

/--
theorem `eLpNorm_one_smul_measure` / 定理 `eLpNorm_one_smul_measure`

English:
theorem eLpNorm_one_smul_measure
  given: {f : α -> ε} (c : Real>=0∞)
  proof: by
  rw [eLpNorm_smul_measure_of_ne_top] <;> simp

中文:
定理 eLpNorm_one_smul_measure
  条件: {f : α -> ε} (c : 实数>=0∞)
  证明: by
  rw [eLpNorm_smul_measure_of_ne_top] <;> simp

Depends on / 依赖: eLpNorm_smul_measure_of_ne_top
-/
theorem eLpNorm_one_smul_measure {f : α -> ε} (c : Real>=0∞) :
    eLpNorm f 1 (c • μ) = c * eLpNorm f 1 μ := by
  rw [eLpNorm_smul_measure_of_ne_top] <;> simp

/--
theorem `eLpNorm_le_of_measure_le_smul` / 定理 `eLpNorm_le_of_measure_le_smul`

English:
theorem eLpNorm_le_of_measure_le_smul
  statement: {c : Real>=0∞}
  proof: by
  grw [h, eLpNorm_smul_measure_le]

中文:
定理 eLpNorm_le_of_measure_le_smul
  结论: {c : 实数>=0∞}
  证明: by
  grw [h, eLpNorm_smul_measure_le]

Depends on / 依赖: eLpNorm_smul_measure_le
-/
theorem eLpNorm_le_of_measure_le_smul {c : Real>=0∞}
    {μ μ' : Measure α} (h : μ' <= c • μ) {f : α -> ε} {p : Real>=0∞} :
    eLpNorm f p μ' <= c ^ (1 / p).toReal • eLpNorm f p μ := by
  grw [h, eLpNorm_smul_measure_le]

/--
theorem `MemLp.of_measure_le_smul` / 定理 `MemLp.of_measure_le_smul`

English:
theorem MemLp.of_measure_le_smul
  statement: {μ' : Measure α} {c : Real>=0∞} (hc : c != ∞)
  proof: by
  refine ⟨hf.1.mono_ac (Measure.absolutelyContinuous_of_le_smul hμ'_le), ?_⟩
  grw [eLpNorm_le_of_measure_le_smul hμ'_le]
  exact ENNReal.mul_lt_top (Ne.lt_top (by simp [hc])) hf.2

中文:
定理 MemLp.of_measure_le_smul
  结论: {μ' : 测度 α} {c : 实数>=0∞} (hc : c != ∞)
  证明: by
  refine ⟨hf.1.mono_ac (Measure.absolutelyContinuous_of_le_smul hμ'_le), ?_⟩
  grw [eLpNorm_le_of_measure_le_smul hμ'_le]
  exact ENNReal.mul_lt_top (Ne.lt_top (by simp [hc])) hf.2

Depends on / 依赖: ENNReal, ENNReal.mul_lt_top, Measure, Measure.absolutelyContinuous_of_le_smul, Ne.lt_top, absolutelyContinuous_of_le_smul, eLpNorm_le_of_measure_le_smul, lt_top, mono_ac, mul_lt_top
-/
theorem MemLp.of_measure_le_smul {μ' : Measure α} {c : Real>=0∞} (hc : c != ∞)
    (hμ'_le : μ' <= c • μ) {f : α -> ε} (hf : MemLp f p μ) : MemLp f p μ' := by
  refine ⟨hf.1.mono_ac (Measure.absolutelyContinuous_of_le_smul hμ'_le), ?_⟩
  grw [eLpNorm_le_of_measure_le_smul hμ'_le]
  exact ENNReal.mul_lt_top (Ne.lt_top (by simp [hc])) hf.2

/--
theorem `MemLp.smul_measure` / 定理 `MemLp.smul_measure`

English:
theorem MemLp.smul_measure
  given: {f : α -> ε} {c : Real>=0∞} (hf : MemLp f p μ) (hc : c != ∞)
  proof: hf.of_measure_le_smul hc le_rfl

中文:
定理 MemLp.smul_measure
  条件: {f : α -> ε} {c : 实数>=0∞} (hf : MemLp f p μ) (hc : c != ∞)
  证明: hf.of_measure_le_smul hc le_rfl

Depends on / 依赖: hf.of_measure_le_smul, le_rfl, of_measure_le_smul
-/
theorem MemLp.smul_measure {f : α -> ε} {c : Real>=0∞} (hf : MemLp f p μ) (hc : c != ∞) :
    MemLp f p (c • μ) :=
  hf.of_measure_le_smul hc le_rfl

variable {ε : Type*} [ENorm ε] in
/--
theorem `eLpNorm_one_add_measure` / 定理 `eLpNorm_one_add_measure`

English:
theorem eLpNorm_one_add_measure
  given: (f : α -> ε) (μ ν : Measure α)
  proof: by
  simp_rw [eLpNorm_one_eq_lintegral_enorm]
  rw [lintegral_add_measure _ μ ν]

中文:
定理 eLpNorm_one_add_measure
  条件: (f : α -> ε) (μ ν : 测度 α)
  证明: by
  simp_rw [eLpNorm_one_eq_lintegral_enorm]
  rw [lintegral_add_measure _ μ ν]

Depends on / 依赖: eLpNorm_one_eq_lintegral_enorm, lintegral_add_measure, simp_rw
-/
theorem eLpNorm_one_add_measure (f : α -> ε) (μ ν : Measure α) :
    eLpNorm f 1 (μ + ν) = eLpNorm f 1 μ + eLpNorm f 1 ν := by
  simp_rw [eLpNorm_one_eq_lintegral_enorm]
  rw [lintegral_add_measure _ μ ν]

/--
theorem `eLpNorm_le_add_measure_right` / 定理 `eLpNorm_le_add_measure_right`

English:
theorem eLpNorm_le_add_measure_right
  given: (f : α -> ε) (μ ν : Measure α) {p : Real>=0∞}
  proof: by
  grw [← Measure.le_add_right le_rfl]

中文:
定理 eLpNorm_le_add_measure_right
  条件: (f : α -> ε) (μ ν : 测度 α) {p : 实数>=0∞}
  证明: by
  grw [← Measure.le_add_right le_rfl]

Depends on / 依赖: Measure, Measure.le_add_right, le_add_right, le_rfl
-/
theorem eLpNorm_le_add_measure_right (f : α -> ε) (μ ν : Measure α) {p : Real>=0∞} :
    eLpNorm f p μ <= eLpNorm f p (μ + ν) := by
  grw [← Measure.le_add_right le_rfl]

/--
theorem `eLpNorm_le_add_measure_left` / 定理 `eLpNorm_le_add_measure_left`

English:
theorem eLpNorm_le_add_measure_left
  given: (f : α -> ε) (μ ν : Measure α) {p : Real>=0∞}
  proof: by
  grw [← Measure.le_add_left le_rfl]

中文:
定理 eLpNorm_le_add_measure_left
  条件: (f : α -> ε) (μ ν : 测度 α) {p : 实数>=0∞}
  证明: by
  grw [← Measure.le_add_left le_rfl]

Depends on / 依赖: Measure, Measure.le_add_left, le_add_left, le_rfl
-/
theorem eLpNorm_le_add_measure_left (f : α -> ε) (μ ν : Measure α) {p : Real>=0∞} :
    eLpNorm f p ν <= eLpNorm f p (μ + ν) := by
  grw [← Measure.le_add_left le_rfl]

variable {ε : Type*} [ENorm ε] in
/--
lemma `eLpNormEssSup_eq_iSup` / 引理 `eLpNormEssSup_eq_iSup`

English:
lemma eLpNormEssSup_eq_iSup
  given: (hμ : forall a, μ {a} != 0) (f : α -> ε)
  statement: eLpNormEssSup f μ = ⨆ a, ‖f a‖ₑ
  proof: essSup_eq_iSup hμ _

中文:
引理 eLpNormEssSup_eq_iSup
  条件: (hμ : 对任意 a, μ {a} != 0) (f : α -> ε)
  结论: eLpNormEssSup f μ = ⨆ a, ‖f a‖ₑ
  证明: essSup_eq_iSup hμ _

Depends on / 依赖: essSup_eq_iSup
-/
lemma eLpNormEssSup_eq_iSup (hμ : forall a, μ {a} != 0) (f : α -> ε) : eLpNormEssSup f μ = ⨆ a, ‖f a‖ₑ :=
  essSup_eq_iSup hμ _

variable {ε : Type*} [ENorm ε] in
/--
lemma `eLpNormEssSup_count` / 引理 `eLpNormEssSup_count`

English:
lemma eLpNormEssSup_count
  given: [MeasurableSingletonClass α] (f : α -> ε)
  proof: essSup_count _

中文:
引理 eLpNormEssSup_count
  条件: [MeasurableSingleton类 α] (f : α -> ε)
  证明: essSup_count _
-/
@[simp] lemma eLpNormEssSup_count [MeasurableSingletonClass α] (f : α -> ε) :
    eLpNormEssSup f .count = ⨆ a, ‖f a‖ₑ := essSup_count _

/--
theorem `MemLp.left_of_add_measure` / 定理 `MemLp.left_of_add_measure`

English:
theorem MemLp.left_of_add_measure
  given: {f : α -> ε} (h : MemLp f p (μ + ν))
  proof: h.mono_measure Measure.le_add_right le_refl _

中文:
定理 MemLp.left_of_add_measure
  条件: {f : α -> ε} (h : MemLp f p (μ + ν))
  证明: h.mono_measure Measure.le_add_right le_refl _

Depends on / 依赖: Measure, Measure.le_add_right, h.mono_measure, le_add_right, le_refl, mono_measure
-/
theorem MemLp.left_of_add_measure {f : α -> ε} (h : MemLp f p (μ + ν)) :
    MemLp f p μ :=
h.mono_measure Measure.le_add_right le_refl _

/--
theorem `MemLp.right_of_add_measure` / 定理 `MemLp.right_of_add_measure`

English:
theorem MemLp.right_of_add_measure
  given: {f : α -> ε} (h : MemLp f p (μ + ν))
  proof: h.mono_measure Measure.le_add_left le_refl _

中文:
定理 MemLp.right_of_add_measure
  条件: {f : α -> ε} (h : MemLp f p (μ + ν))
  证明: h.mono_measure Measure.le_add_left le_refl _

Depends on / 依赖: Measure, Measure.le_add_left, h.mono_measure, le_add_left, le_refl, mono_measure
-/
theorem MemLp.right_of_add_measure {f : α -> ε} (h : MemLp f p (μ + ν)) :
    MemLp f p ν :=
h.mono_measure Measure.le_add_left le_refl _

/--
theorem `MemLp.enorm` / 定理 `MemLp.enorm`

English:
theorem MemLp.enorm
  given: {f : α -> ε} (h : MemLp f p μ)
  statement: MemLp (‖f ·‖ₑ) p μ
  proof: ⟨h.aestronglyMeasurable.enorm.aestronglyMeasurable,
    by simp_rw [MeasureTheory.eLpNorm_enorm, h.eLpNorm_lt_top]⟩

中文:
定理 MemLp.enorm
  条件: {f : α -> ε} (h : MemLp f p μ)
  结论: MemLp (‖f ·‖ₑ) p μ
  证明: ⟨h.aestronglyMeasurable.enorm.aestronglyMeasurable,
    by simp_rw [MeasureTheory.eLpNorm_enorm, h.eLpNorm_lt_top]⟩

Depends on / 依赖: MeasureTheory, MeasureTheory.eLpNorm_enorm, aestronglyMeasurable, eLpNorm_enorm, eLpNorm_lt_top, h.aestronglyMeasurable.enorm.aestronglyMeasurable, h.eLpNorm_lt_top, simp_rw
-/
theorem MemLp.enorm {f : α -> ε} (h : MemLp f p μ) : MemLp (‖f ·‖ₑ) p μ :=
  ⟨h.aestronglyMeasurable.enorm.aestronglyMeasurable,
    by simp_rw [MeasureTheory.eLpNorm_enorm, h.eLpNorm_lt_top]⟩

/--
theorem `MemLp.norm` / 定理 `MemLp.norm`

English:
theorem MemLp.norm
  given: {f : α -> E} (h : MemLp f p μ)
  statement: MemLp (fun x => ‖f x‖) p μ
  proof: h.of_le h.aestronglyMeasurable.norm (Eventually.of_forall fun x => by simp)

中文:
定理 MemLp.norm
  条件: {f : α -> E} (h : MemLp f p μ)
  结论: MemLp (fun x => ‖f x‖) p μ
  证明: h.of_le h.aestronglyMeasurable.norm (Eventually.of_forall fun x => by simp)

Depends on / 依赖: Eventually, Eventually.of_forall, aestronglyMeasurable, h.aestronglyMeasurable.norm, h.of_le, of_forall, of_le
-/
theorem MemLp.norm {f : α -> E} (h : MemLp f p μ) : MemLp (fun x => ‖f x‖) p μ :=
  h.of_le h.aestronglyMeasurable.norm (Eventually.of_forall fun x => by simp)

/--
theorem `memLp_enorm_iff` / 定理 `memLp_enorm_iff`

English:
theorem memLp_enorm_iff
  given: {f : α -> ε} (hf : AEStronglyMeasurable f μ)
  proof: ⟨fun h => ⟨hf, by rw [← eLpNorm_enorm]; exact h.2⟩, fun h => h.enorm⟩

中文:
定理 memLp_enorm_iff
  条件: {f : α -> ε} (hf : AEStronglyMeasurable f μ)
  证明: ⟨fun h => ⟨hf, by rw [← eLpNorm_enorm]; exact h.2⟩, fun h => h.enorm⟩

Depends on / 依赖: eLpNorm_enorm, h.enorm
-/
theorem memLp_enorm_iff {f : α -> ε} (hf : AEStronglyMeasurable f μ) :
    MemLp (‖f ·‖ₑ) p μ ↔ MemLp f p μ :=
  ⟨fun h => ⟨hf, by rw [← eLpNorm_enorm]; exact h.2⟩, fun h => h.enorm⟩

/--
theorem `memLp_norm_iff` / 定理 `memLp_norm_iff`

English:
theorem memLp_norm_iff
  given: {f : α -> E} (hf : AEStronglyMeasurable f μ)
  proof: ⟨fun h => ⟨hf, by rw [← eLpNorm_norm]; exact h.2⟩, fun h => h.norm⟩

中文:
定理 memLp_norm_iff
  条件: {f : α -> E} (hf : AEStronglyMeasurable f μ)
  证明: ⟨fun h => ⟨hf, by rw [← eLpNorm_norm]; exact h.2⟩, fun h => h.norm⟩

Depends on / 依赖: eLpNorm_norm, h.norm
-/
theorem memLp_norm_iff {f : α -> E} (hf : AEStronglyMeasurable f μ) :
    MemLp (fun x => ‖f x‖) p μ ↔ MemLp f p μ :=
  ⟨fun h => ⟨hf, by rw [← eLpNorm_norm]; exact h.2⟩, fun h => h.norm⟩

end ContinuousENorm

section ESeminormedAddMonoid

variable {ε : Type*} [TopologicalSpace ε] [ESeminormedAddMonoid ε]

/--
theorem `eLpNorm'_eq_zero_of_ae_zero` / 定理 `eLpNorm'_eq_zero_of_ae_zero`

English:
theorem eLpNorm'_eq_zero_of_ae_zero
  given: {f : α -> ε} (hq0_lt : 0 < q) (hf_zero : f =ᵐ[μ] 0)
  proof: by rw [eLpNorm'_congr_ae hf_zero, eLpNorm'_zero hq0_lt]

中文:
定理 eLpNorm'_eq_zero_of_ae_zero
  条件: {f : α -> ε} (hq0_lt : 0 < q) (hf_zero : f =ᵐ[μ] 0)
  证明: by rw [eLpNorm'_congr_ae hf_zero, eLpNorm'_zero hq0_lt]
-/
theorem eLpNorm'_eq_zero_of_ae_zero {f : α -> ε} (hq0_lt : 0 < q) (hf_zero : f =ᵐ[μ] 0) :
    eLpNorm' f q μ = 0 := by rw [eLpNorm'_congr_ae hf_zero, eLpNorm'_zero hq0_lt]

/--
theorem `eLpNorm'_eq_zero_of_ae_zero'` / 定理 `eLpNorm'_eq_zero_of_ae_zero'`

English:
theorem eLpNorm'_eq_zero_of_ae_zero'
  statement: (hq0_ne : q != 0) (hμ : μ != 0) {f : α -> ε}
  proof: by rw [eLpNorm'_congr_ae hf_zero, eLpNorm'_zero' hq0_ne hμ]

中文:
定理 eLpNorm'_eq_zero_of_ae_zero'
  结论: (hq0_ne : q != 0) (hμ : μ != 0) {f : α -> ε}
  证明: by rw [eLpNorm'_congr_ae hf_zero, eLpNorm'_zero' hq0_ne hμ]
-/
theorem eLpNorm'_eq_zero_of_ae_zero' (hq0_ne : q != 0) (hμ : μ != 0) {f : α -> ε}
    (hf_zero : f =ᵐ[μ] 0) :
    eLpNorm' f q μ = 0 := by rw [eLpNorm'_congr_ae hf_zero, eLpNorm'_zero' hq0_ne hμ]

/--
theorem `eLpNorm_eq_zero_of_ae_zero` / 定理 `eLpNorm_eq_zero_of_ae_zero`

English:
theorem eLpNorm_eq_zero_of_ae_zero
  given: {f : α -> ε} (hf : f =ᵐ[μ] 0)
  statement: eLpNorm f p μ = 0
  proof: by
  rw [← eLpNorm_zero (p := p) (μ := μ) (α := α) (ε := ε)]
  exact eLpNorm_congr_ae hf

中文:
定理 eLpNorm_eq_zero_of_ae_zero
  条件: {f : α -> ε} (hf : f =ᵐ[μ] 0)
  结论: eLpNorm f p μ = 0
  证明: by
  rw [← eLpNorm_zero (p := p) (μ := μ) (α := α) (ε := ε)]
  exact eLpNorm_congr_ae hf

Depends on / 依赖: eLpNorm_congr_ae, eLpNorm_zero
-/
theorem eLpNorm_eq_zero_of_ae_zero {f : α -> ε} (hf : f =ᵐ[μ] 0) : eLpNorm f p μ = 0 := by
  rw [← eLpNorm_zero (p := p) (μ := μ) (α := α) (ε := ε)]
  exact eLpNorm_congr_ae hf

/--
theorem `eLpNorm'_eq_zero_of_ae_eq_zero` / 定理 `eLpNorm'_eq_zero_of_ae_eq_zero`

English:
theorem eLpNorm'_eq_zero_of_ae_eq_zero
  statement: {f : α -> ε} {p : Real} (hp : 0 < p)
  proof: by
  rw [← eLpNorm'_zero hp (μ := μ) (ε := ε)]
  exact eLpNorm'_congr_enorm_ae (by simp [hf])

中文:
定理 eLpNorm'_eq_zero_of_ae_eq_zero
  结论: {f : α -> ε} {p : 实数} (hp : 0 < p)
  证明: by
  rw [← eLpNorm'_zero hp (μ := μ) (ε := ε)]
  exact eLpNorm'_congr_enorm_ae (by simp [hf])
-/
theorem eLpNorm'_eq_zero_of_ae_eq_zero {f : α -> ε} {p : Real} (hp : 0 < p)
    (hf : forallᵐ (x : α) ∂μ, ‖f x‖ₑ = 0) : eLpNorm' f p μ = 0 := by
  rw [← eLpNorm'_zero hp (μ := μ) (ε := ε)]
  exact eLpNorm'_congr_enorm_ae (by simp [hf])

variable {ε : Type*} [ENorm ε] in
/--
theorem `ae_le_eLpNormEssSup` / 定理 `ae_le_eLpNormEssSup`

English:
theorem ae_le_eLpNormEssSup
  given: {f : α -> ε}
  statement: forallᵐ y ∂μ, ‖f y‖ₑ <= eLpNormEssSup f μ
  proof: ae_le_essSup

中文:
定理 ae_le_eLpNormEssSup
  条件: {f : α -> ε}
  结论: 对任意ᵐ y ∂μ, ‖f y‖ₑ <= eLpNormEssSup f μ
  证明: ae_le_essSup

Depends on / 依赖: ae_le_essSup
-/
theorem ae_le_eLpNormEssSup {f : α -> ε} : forallᵐ y ∂μ, ‖f y‖ₑ <= eLpNormEssSup f μ :=
  ae_le_essSup

-- NB. Changing this lemma to use ‖‖ₑ makes it false (only => still holds);
-- unlike a nnnorm, the enorm can be ∞.
/--
lemma `eLpNormEssSup_lt_top_iff_isBoundedUnder` / 引理 `eLpNormEssSup_lt_top_iff_isBoundedUnder`

English:
lemma eLpNormEssSup_lt_top_iff_isBoundedUnder
  proof: ⟨(eLpNormEssSup f μ).toNNReal, by
    simp_rw [← ENNReal.coe_le_coe, ENNReal.coe_toNNReal h.ne]; exact ae_le_eLpNormEssSup⟩
  mpr := by rintro ⟨C, hC⟩; exact eLpNormEssSup_lt_top_of_ae_nnnorm_bound (C := C) hC

中文:
引理 eLpNormEssSup_lt_top_iff_isBoundedUnder
  证明: ⟨(eLpNormEssSup f μ).toNNReal, by
    simp_rw [← ENNReal.coe_le_coe, ENNReal.coe_toNNReal h.ne]; exact ae_le_eLpNormEssSup⟩
  mpr := by rintro ⟨C, hC⟩; exact eLpNormEssSup_lt_top_of_ae_nnnorm_bound (C := C) hC

Depends on / 依赖: ENNReal, ENNReal.coe_le_coe, ENNReal.coe_toNNReal, ae_le_eLpNormEssSup, coe_le_coe, coe_toNNReal, eLpNormEssSup, eLpNormEssSup_lt_top_of_ae_nnnorm_bound, h.ne, simp_rw, toNNReal
-/
lemma eLpNormEssSup_lt_top_iff_isBoundedUnder :
    eLpNormEssSup f μ < ⊤ ↔ IsBoundedUnder (· <= ·) (ae μ) fun x => ‖f x‖₊ where
  mp h := ⟨(eLpNormEssSup f μ).toNNReal, by
    simp_rw [← ENNReal.coe_le_coe, ENNReal.coe_toNNReal h.ne]; exact ae_le_eLpNormEssSup⟩
  mpr := by rintro ⟨C, hC⟩; exact eLpNormEssSup_lt_top_of_ae_nnnorm_bound (C := C) hC

variable {ε : Type*} [ENorm ε] in
/--
theorem `meas_eLpNormEssSup_lt` / 定理 `meas_eLpNormEssSup_lt`

English:
theorem meas_eLpNormEssSup_lt
  given: {f : α -> ε}
  statement: μ { y | eLpNormEssSup f μ < ‖f y‖ₑ } = 0
  proof: meas_essSup_lt

中文:
定理 meas_eLpNormEssSup_lt
  条件: {f : α -> ε}
  结论: μ { y | eLpNormEssSup f μ < ‖f y‖ₑ } = 0
  证明: meas_essSup_lt

Depends on / 依赖: meas_essSup_lt
-/
theorem meas_eLpNormEssSup_lt {f : α -> ε} : μ { y | eLpNormEssSup f μ < ‖f y‖ₑ } = 0 :=
  meas_essSup_lt

/--
lemma `eLpNorm_lt_top_of_finite` / 引理 `eLpNorm_lt_top_of_finite`

English:
lemma eLpNorm_lt_top_of_finite
  given: [Finite α] [IsFiniteMeasure μ]
  statement: eLpNorm f p μ < ∞
  proof: by
  obtain rfl | hp₀ := eq_or_ne p 0
  · simp
  obtain rfl | hp := eq_or_ne p ∞
  · simp only [eLpNorm_exponent_top, eLpNormEssSup_lt_top_iff_isBoundedUnder]
    exact .le_of_finite
  rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top hp₀ hp]
  refine IsFiniteMeasure.lintegral_lt_top_of_bounded_to_ennreal μ ?_
  simp_rw [enorm, ← ENNReal.coe_rpow_of_nonneg _ ENNReal.toReal_nonneg]
  norm_cast
  exact Finite.exists_le _

中文:
引理 eLpNorm_lt_top_of_finite
  条件: [有限 α] [是有限测度 μ]
  结论: eLpNorm f p μ < ∞
  证明: by
  obtain rfl | hp₀ := eq_or_ne p 0
  · simp
  obtain rfl | hp := eq_or_ne p ∞
  · simp only [eLpNorm_exponent_top, eLpNormEssSup_lt_top_iff_isBoundedUnder]
    exact .le_of_finite
  rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top hp₀ hp]
  refine IsFiniteMeasure.lintegral_lt_top_of_bounded_to_ennreal μ ?_
  simp_rw [enorm, ← ENNReal.coe_rpow_of_nonneg _ ENNReal.toReal_nonneg]
  norm_cast
  exact Finite.exists_le _

Depends on / 依赖: ENNReal, ENNReal.coe_rpow_of_nonneg, ENNReal.toReal_nonneg, Finite, Finite.exists_le, IsFiniteMeasure, IsFiniteMeasure.lintegral_lt_top_of_bounded_to_ennreal, coe_rpow_of_nonneg, eLpNormEssSup_lt_top_iff_isBoundedUnder, eLpNorm_exponent_top, eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top, eq_or_ne, exists_le, le_of_finite, lintegral_lt_top_of_bounded_to_ennreal, simp_rw, toReal_nonneg
-/
lemma eLpNorm_lt_top_of_finite [Finite α] [IsFiniteMeasure μ] : eLpNorm f p μ < ∞ := by
  obtain rfl | hp₀ := eq_or_ne p 0
  · simp
  obtain rfl | hp := eq_or_ne p ∞
  · simp only [eLpNorm_exponent_top, eLpNormEssSup_lt_top_iff_isBoundedUnder]
    exact .le_of_finite
  rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top hp₀ hp]
  refine IsFiniteMeasure.lintegral_lt_top_of_bounded_to_ennreal μ ?_
  simp_rw [enorm, ← ENNReal.coe_rpow_of_nonneg _ ENNReal.toReal_nonneg]
  norm_cast
  exact Finite.exists_le _

/--
lemma `MemLp.of_discrete` / 引理 `MemLp.of_discrete`

English:
lemma MemLp.of_discrete
  given: [DiscreteMeasurableSpace α] [Finite α] [IsFiniteMeasure μ]
  proof: let ⟨C, hC⟩ := Finite.exists_le (‖f ·‖₊); .of_bound .of_discrete C .of_forall hC

中文:
引理 MemLp.of_discrete
  条件: [DiscreteMeasurable空间 α] [有限 α] [是有限测度 μ]
  证明: let ⟨C, hC⟩ := Finite.exists_le (‖f ·‖₊); .of_bound .of_discrete C .of_forall hC
-/
@[simp] lemma MemLp.of_discrete [DiscreteMeasurableSpace α] [Finite α] [IsFiniteMeasure μ] :
    MemLp f p μ :=
let ⟨C, hC⟩ := Finite.exists_le (‖f ·‖₊); .of_bound .of_discrete C .of_forall hC

/--
lemma `eLpNorm_of_isEmpty` / 引理 `eLpNorm_of_isEmpty`

English:
lemma eLpNorm_of_isEmpty
  given: [IsEmpty α] (f : α -> ε) (p : Real>=0∞)
  statement: eLpNorm f p μ = 0
  proof: by
  simp [Subsingleton.elim f 0]

中文:
引理 eLpNorm_of_isEmpty
  条件: [是空 α] (f : α -> ε) (p : 实数>=0∞)
  结论: eLpNorm f p μ = 0
  证明: by
  simp [Subsingleton.elim f 0]
-/
@[simp] lemma eLpNorm_of_isEmpty [IsEmpty α] (f : α -> ε) (p : Real>=0∞) : eLpNorm f p μ = 0 := by
  simp [Subsingleton.elim f 0]

end ESeminormedAddMonoid

section ENormedAddMonoid

variable {ε : Type*} [TopologicalSpace ε] [ENormedAddMonoid ε]

/--
theorem `ae_eq_zero_of_eLpNorm'_eq_zero` / 定理 `ae_eq_zero_of_eLpNorm'_eq_zero`

English:
theorem ae_eq_zero_of_eLpNorm'_eq_zero
  statement: {f : α -> ε} (hq0 : 0 <= q) (hf : AEStronglyMeasurable f μ)
  proof: by
  simp only [eLpNorm'_eq_lintegral_enorm, lintegral_eq_zero_iff' (hf.enorm.pow_const q), one_div,
    ENNReal.rpow_eq_zero_iff, inv_pos, inv_neg'', hq0.not_gt, and_false, or_false] at h
  refine h.left.mono fun x hx => ?_
  simp only [Pi.ofNat_apply, ENNReal.rpow_eq_zero_iff, enorm_eq_zero, h.2.not_gt, and_false,
    or_false] at hx
  simp [hx.1]

中文:
定理 ae_eq_zero_of_eLpNorm'_eq_zero
  结论: {f : α -> ε} (hq0 : 0 <= q) (hf : AEStronglyMeasurable f μ)
  证明: by
  simp only [eLpNorm'_eq_lintegral_enorm, lintegral_eq_zero_iff' (hf.enorm.pow_const q), one_div,
    ENNReal.rpow_eq_zero_iff, inv_pos, inv_neg'', hq0.not_gt, and_false, or_false] at h
  refine h.left.mono fun x hx => ?_
  simp only [Pi.ofNat_apply, ENNReal.rpow_eq_zero_iff, enorm_eq_zero, h.2.not_gt, and_false,
    or_false] at hx
  simp [hx.1]

Depends on / 依赖: ENNReal, ENNReal.rpow_eq_zero_iff, Pi.ofNat_apply, _eq_lintegral_enorm, and_false, eLpNorm, enorm_eq_zero, h.left.mono, hf.enorm.pow_const, hq0.not_gt, inv_neg, inv_pos, lintegral_eq_zero_iff, not_gt, ofNat_apply, one_div, or_false, pow_const, rpow_eq_zero_iff
-/
theorem ae_eq_zero_of_eLpNorm'_eq_zero {f : α -> ε} (hq0 : 0 <= q) (hf : AEStronglyMeasurable f μ)
    (h : eLpNorm' f q μ = 0) : f =ᵐ[μ] 0 := by
  simp only [eLpNorm'_eq_lintegral_enorm, lintegral_eq_zero_iff' (hf.enorm.pow_const q), one_div,
    ENNReal.rpow_eq_zero_iff, inv_pos, inv_neg'', hq0.not_gt, and_false, or_false] at h
  refine h.left.mono fun x hx => ?_
  simp only [Pi.ofNat_apply, ENNReal.rpow_eq_zero_iff, enorm_eq_zero, h.2.not_gt, and_false,
    or_false] at hx
  simp [hx.1]

/--
theorem `eLpNorm'_eq_zero_iff` / 定理 `eLpNorm'_eq_zero_iff`

English:
theorem eLpNorm'_eq_zero_iff
  given: (hq0_lt : 0 < q) {f : α -> ε} (hf : AEStronglyMeasurable f μ)
  proof: ⟨ae_eq_zero_of_eLpNorm'_eq_zero (le_of_lt hq0_lt) hf, eLpNorm'_eq_zero_of_ae_zero hq0_lt⟩

中文:
定理 eLpNorm'_eq_zero_iff
  条件: (hq0_lt : 0 < q) {f : α -> ε} (hf : AEStronglyMeasurable f μ)
  证明: ⟨ae_eq_zero_of_eLpNorm'_eq_zero (le_of_lt hq0_lt) hf, eLpNorm'_eq_zero_of_ae_zero hq0_lt⟩
-/
theorem eLpNorm'_eq_zero_iff (hq0_lt : 0 < q) {f : α -> ε} (hf : AEStronglyMeasurable f μ) :
    eLpNorm' f q μ = 0 ↔ f =ᵐ[μ] 0 :=
  ⟨ae_eq_zero_of_eLpNorm'_eq_zero (le_of_lt hq0_lt) hf, eLpNorm'_eq_zero_of_ae_zero hq0_lt⟩

variable {ε : Type*} [ENorm ε] in
/--
theorem `enorm_ae_le_eLpNormEssSup` / 定理 `enorm_ae_le_eLpNormEssSup`

English:
theorem enorm_ae_le_eLpNormEssSup
  given: {_ : MeasurableSpace α} (f : α -> ε) (μ : Measure α)
  proof: ENNReal.ae_le_essSup fun x => ‖f x‖ₑ

@[simp]

中文:
定理 enorm_ae_le_eLpNormEssSup
  条件: {_ : 可测空间 α} (f : α -> ε) (μ : 测度 α)
  证明: ENNReal.ae_le_essSup fun x => ‖f x‖ₑ

@[simp]

Depends on / 依赖: ENNReal, ENNReal.ae_le_essSup, ae_le_essSup
-/
theorem enorm_ae_le_eLpNormEssSup {_ : MeasurableSpace α} (f : α -> ε) (μ : Measure α) :
    forallᵐ x ∂μ, ‖f x‖ₑ <= eLpNormEssSup f μ :=
  ENNReal.ae_le_essSup fun x => ‖f x‖ₑ

@[simp]
/--
theorem `eLpNormEssSup_eq_zero_iff` / 定理 `eLpNormEssSup_eq_zero_iff`

English:
theorem eLpNormEssSup_eq_zero_iff
  given: {f : α -> ε}
  statement: eLpNormEssSup f μ = 0 ↔ f =ᵐ[μ] 0
  proof: by
  simp [EventuallyEq, eLpNormEssSup_eq_essSup_enorm]

中文:
定理 eLpNormEssSup_eq_zero_iff
  条件: {f : α -> ε}
  结论: eLpNormEssSup f μ = 0 ↔ f =ᵐ[μ] 0
  证明: by
  simp [EventuallyEq, eLpNormEssSup_eq_essSup_enorm]

Depends on / 依赖: EventuallyEq, eLpNormEssSup_eq_essSup_enorm
-/
theorem eLpNormEssSup_eq_zero_iff {f : α -> ε} : eLpNormEssSup f μ = 0 ↔ f =ᵐ[μ] 0 := by
  simp [EventuallyEq, eLpNormEssSup_eq_essSup_enorm]

/--
theorem `eLpNorm_eq_zero_iff` / 定理 `eLpNorm_eq_zero_iff`

English:
theorem eLpNorm_eq_zero_iff
  given: {f : α -> ε} (hf : AEStronglyMeasurable f μ) (h0 : p != 0)
  proof: by
  by_cases h_top : p = ∞
  · rw [h_top, eLpNorm_exponent_top, eLpNormEssSup_eq_zero_iff]
  rw [eLpNorm_eq_eLpNorm' h0 h_top]
  exact eLpNorm'_eq_zero_iff (ENNReal.toReal_pos h0 h_top) hf

中文:
定理 eLpNorm_eq_zero_iff
  条件: {f : α -> ε} (hf : AEStronglyMeasurable f μ) (h0 : p != 0)
  证明: by
  by_cases h_top : p = ∞
  · rw [h_top, eLpNorm_exponent_top, eLpNormEssSup_eq_zero_iff]
  rw [eLpNorm_eq_eLpNorm' h0 h_top]
  exact eLpNorm'_eq_zero_iff (ENNReal.toReal_pos h0 h_top) hf

Depends on / 依赖: ENNReal, ENNReal.toReal_pos, _eq_zero_iff, eLpNorm, eLpNormEssSup_eq_zero_iff, eLpNorm_eq_eLpNorm, eLpNorm_exponent_top, h_top, toReal_pos
-/
theorem eLpNorm_eq_zero_iff {f : α -> ε} (hf : AEStronglyMeasurable f μ) (h0 : p != 0) :
    eLpNorm f p μ = 0 ↔ f =ᵐ[μ] 0 := by
  by_cases h_top : p = ∞
  · rw [h_top, eLpNorm_exponent_top, eLpNormEssSup_eq_zero_iff]
  rw [eLpNorm_eq_eLpNorm' h0 h_top]
  exact eLpNorm'_eq_zero_iff (ENNReal.toReal_pos h0 h_top) hf

end ENormedAddMonoid

section MapMeasure

variable {ε : Type*} [TopologicalSpace ε] [ContinuousENorm ε]
  {β : Type*} {mβ : MeasurableSpace β} {f : α -> β} {g : β -> ε}

/--
theorem `eLpNormEssSup_map_measure` / 定理 `eLpNormEssSup_map_measure`

English:
theorem eLpNormEssSup_map_measure
  statement: (hg : AEStronglyMeasurable g (Measure.map f μ))
  proof: essSup_map_measure hg.enorm hf

中文:
定理 eLpNormEssSup_map_measure
  结论: (hg : AEStronglyMeasurable g (测度.map f μ))
  证明: essSup_map_measure hg.enorm hf

Depends on / 依赖: essSup_map_measure, hg.enorm
-/
theorem eLpNormEssSup_map_measure (hg : AEStronglyMeasurable g (Measure.map f μ))
    (hf : AEMeasurable f μ) : eLpNormEssSup g (Measure.map f μ) = eLpNormEssSup (g ∘ f) μ :=
  essSup_map_measure hg.enorm hf

/--
theorem `eLpNorm_map_measure` / 定理 `eLpNorm_map_measure`

English:
theorem eLpNorm_map_measure
  statement: (hg : AEStronglyMeasurable g (Measure.map f μ))
  proof: by
  by_cases hp_zero : p = 0
  · simp only [hp_zero, eLpNorm_exponent_zero]
  by_cases hp_top : p = ∞
  · simp_rw [hp_top, eLpNorm_exponent_top]
    exact eLpNormEssSup_map_measure hg hf
  simp_rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp_zero hp_top,
    lintegral_map' (hg.enorm.pow_const p.toReal) hf, Function.comp_apply]

中文:
定理 eLpNorm_map_measure
  结论: (hg : AEStronglyMeasurable g (测度.map f μ))
  证明: by
  by_cases hp_zero : p = 0
  · simp only [hp_zero, eLpNorm_exponent_zero]
  by_cases hp_top : p = ∞
  · simp_rw [hp_top, eLpNorm_exponent_top]
    exact eLpNormEssSup_map_measure hg hf
  simp_rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp_zero hp_top,
    lintegral_map' (hg.enorm.pow_const p.toReal) hf, Function.comp_apply]

Depends on / 依赖: Function, Function.comp_apply, comp_apply, eLpNormEssSup_map_measure, eLpNorm_eq_lintegral_rpow_enorm_toReal, eLpNorm_exponent_top, eLpNorm_exponent_zero, hg.enorm.pow_const, hp_top, hp_zero, lintegral_map, p.toReal, pow_const, simp_rw, toReal
-/
theorem eLpNorm_map_measure (hg : AEStronglyMeasurable g (Measure.map f μ))
    (hf : AEMeasurable f μ) : eLpNorm g p (Measure.map f μ) = eLpNorm (g ∘ f) p μ := by
  by_cases hp_zero : p = 0
  · simp only [hp_zero, eLpNorm_exponent_zero]
  by_cases hp_top : p = ∞
  · simp_rw [hp_top, eLpNorm_exponent_top]
    exact eLpNormEssSup_map_measure hg hf
  simp_rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp_zero hp_top,
    lintegral_map' (hg.enorm.pow_const p.toReal) hf, Function.comp_apply]

/--
theorem `memLp_map_measure_iff` / 定理 `memLp_map_measure_iff`

English:
theorem memLp_map_measure_iff
  statement: (hg : AEStronglyMeasurable g (Measure.map f μ))
  proof: by
  simp [MemLp, eLpNorm_map_measure hg hf, hg.comp_aemeasurable hf, hg]

中文:
定理 memLp_map_measure_iff
  结论: (hg : AEStronglyMeasurable g (测度.map f μ))
  证明: by
  simp [MemLp, eLpNorm_map_measure hg hf, hg.comp_aemeasurable hf, hg]

Depends on / 依赖: comp_aemeasurable, eLpNorm_map_measure, hg.comp_aemeasurable
-/
theorem memLp_map_measure_iff (hg : AEStronglyMeasurable g (Measure.map f μ))
    (hf : AEMeasurable f μ) : MemLp g p (Measure.map f μ) ↔ MemLp (g ∘ f) p μ := by
  simp [MemLp, eLpNorm_map_measure hg hf, hg.comp_aemeasurable hf, hg]

/--
theorem `MemLp.comp_of_map` / 定理 `MemLp.comp_of_map`

English:
theorem MemLp.comp_of_map
  given: (hg : MemLp g p (Measure.map f μ)) (hf : AEMeasurable f μ)
  proof: (memLp_map_measure_iff hg.aestronglyMeasurable hf).1 hg

中文:
定理 MemLp.comp_of_map
  条件: (hg : MemLp g p (测度.map f μ)) (hf : 几乎处处可测 f μ)
  证明: (memLp_map_measure_iff hg.aestronglyMeasurable hf).1 hg

Depends on / 依赖: aestronglyMeasurable, hg.aestronglyMeasurable, memLp_map_measure_iff
-/
theorem MemLp.comp_of_map (hg : MemLp g p (Measure.map f μ)) (hf : AEMeasurable f μ) :
    MemLp (g ∘ f) p μ :=
  (memLp_map_measure_iff hg.aestronglyMeasurable hf).1 hg

/--
theorem `eLpNorm_comp_measurePreserving` / 定理 `eLpNorm_comp_measurePreserving`

English:
theorem eLpNorm_comp_measurePreserving
  statement: {ν : MeasureTheory.Measure β} (hg : AEStronglyMeasurable g ν)
  proof: Eq.symm hf.map_eq ▸ eLpNorm_map_measure (hf.map_eq ▸ hg) hf.aemeasurable

中文:
定理 eLpNorm_comp_measurePreserving
  结论: {ν : 测度论.测度 β} (hg : AEStronglyMeasurable g ν)
  证明: Eq.symm hf.map_eq ▸ eLpNorm_map_measure (hf.map_eq ▸ hg) hf.aemeasurable

Depends on / 依赖: Eq.symm, aemeasurable, eLpNorm_map_measure, hf.aemeasurable, hf.map_eq, map_eq
-/
theorem eLpNorm_comp_measurePreserving {ν : MeasureTheory.Measure β} (hg : AEStronglyMeasurable g ν)
    (hf : MeasurePreserving f μ ν) : eLpNorm (g ∘ f) p μ = eLpNorm g p ν :=
Eq.symm hf.map_eq ▸ eLpNorm_map_measure (hf.map_eq ▸ hg) hf.aemeasurable

/--
theorem `AEEqFun.eLpNorm_compMeasurePreserving` / 定理 `AEEqFun.eLpNorm_compMeasurePreserving`

English:
theorem AEEqFun.eLpNorm_compMeasurePreserving
  statement: {ν : MeasureTheory.Measure β} (g : β ->ₘ[ν] E)
  proof: by
  rw [eLpNorm_congr_ae (g.coeFn_compMeasurePreserving _)]
  exact eLpNorm_comp_measurePreserving g.aestronglyMeasurable hf

中文:
定理 AEEqFun.eLpNorm_compMeasurePreserving
  结论: {ν : 测度论.测度 β} (g : β ->ₘ[ν] E)
  证明: by
  rw [eLpNorm_congr_ae (g.coeFn_compMeasurePreserving _)]
  exact eLpNorm_comp_measurePreserving g.aestronglyMeasurable hf

Depends on / 依赖: aestronglyMeasurable, coeFn_compMeasurePreserving, eLpNorm_comp_measurePreserving, eLpNorm_congr_ae, g.aestronglyMeasurable, g.coeFn_compMeasurePreserving
-/
theorem AEEqFun.eLpNorm_compMeasurePreserving {ν : MeasureTheory.Measure β} (g : β ->ₘ[ν] E)
    (hf : MeasurePreserving f μ ν) :
    eLpNorm (g.compMeasurePreserving f hf) p μ = eLpNorm g p ν := by
  rw [eLpNorm_congr_ae (g.coeFn_compMeasurePreserving _)]
  exact eLpNorm_comp_measurePreserving g.aestronglyMeasurable hf

/--
theorem `MemLp.comp_measurePreserving` / 定理 `MemLp.comp_measurePreserving`

English:
theorem MemLp.comp_measurePreserving
  statement: {ν : MeasureTheory.Measure β} (hg : MemLp g p ν)
  proof: .comp_of_map (hf.map_eq.symm ▸ hg) hf.aemeasurable

中文:
定理 MemLp.comp_measurePreserving
  结论: {ν : 测度论.测度 β} (hg : MemLp g p ν)
  证明: .comp_of_map (hf.map_eq.symm ▸ hg) hf.aemeasurable

Depends on / 依赖: aemeasurable, comp_of_map, hf.aemeasurable, hf.map_eq.symm, map_eq
-/
theorem MemLp.comp_measurePreserving {ν : MeasureTheory.Measure β} (hg : MemLp g p ν)
    (hf : MeasurePreserving f μ ν) : MemLp (g ∘ f) p μ :=
  .comp_of_map (hf.map_eq.symm ▸ hg) hf.aemeasurable

/--
theorem `_root_.MeasurableEmbedding.eLpNormEssSup_map_measure` / 定理 `_root_.MeasurableEmbedding.eLpNormEssSup_map_measure`

English:
theorem _root_.MeasurableEmbedding.eLpNormEssSup_map_measure
  given: (hf : MeasurableEmbedding f)
  proof: hf.essSup_map_measure

中文:
定理 _root_.可测嵌入.eLpNormEssSup_map_measure
  条件: (hf : 可测嵌入 f)
  证明: hf.essSup_map_measure

Depends on / 依赖: essSup_map_measure, hf.essSup_map_measure
-/
theorem _root_.MeasurableEmbedding.eLpNormEssSup_map_measure (hf : MeasurableEmbedding f) :
    eLpNormEssSup g (Measure.map f μ) = eLpNormEssSup (g ∘ f) μ :=
  hf.essSup_map_measure

/--
theorem `_root_.MeasurableEmbedding.eLpNorm_map_measure` / 定理 `_root_.MeasurableEmbedding.eLpNorm_map_measure`

English:
theorem _root_.MeasurableEmbedding.eLpNorm_map_measure
  given: (hf : MeasurableEmbedding f)
  proof: by
  by_cases hp_zero : p = 0
  · simp only [hp_zero, eLpNorm_exponent_zero]
  by_cases hp : p = ∞
  · simp_rw [hp, eLpNorm_exponent_top]
    exact hf.essSup_map_measure
  · simp [eLpNorm_eq_lintegral_rpow_enorm_toReal hp_zero hp, hf.lintegral_map]

中文:
定理 _root_.可测嵌入.eLpNorm_map_measure
  条件: (hf : 可测嵌入 f)
  证明: by
  by_cases hp_zero : p = 0
  · simp only [hp_zero, eLpNorm_exponent_zero]
  by_cases hp : p = ∞
  · simp_rw [hp, eLpNorm_exponent_top]
    exact hf.essSup_map_measure
  · simp [eLpNorm_eq_lintegral_rpow_enorm_toReal hp_zero hp, hf.lintegral_map]

Depends on / 依赖: eLpNorm_eq_lintegral_rpow_enorm_toReal, eLpNorm_exponent_top, eLpNorm_exponent_zero, essSup_map_measure, hf.essSup_map_measure, hf.lintegral_map, hp_zero, lintegral_map, simp_rw
-/
theorem _root_.MeasurableEmbedding.eLpNorm_map_measure (hf : MeasurableEmbedding f) :
    eLpNorm g p (Measure.map f μ) = eLpNorm (g ∘ f) p μ := by
  by_cases hp_zero : p = 0
  · simp only [hp_zero, eLpNorm_exponent_zero]
  by_cases hp : p = ∞
  · simp_rw [hp, eLpNorm_exponent_top]
    exact hf.essSup_map_measure
  · simp [eLpNorm_eq_lintegral_rpow_enorm_toReal hp_zero hp, hf.lintegral_map]

/--
theorem `_root_.MeasurableEmbedding.memLp_map_measure_iff` / 定理 `_root_.MeasurableEmbedding.memLp_map_measure_iff`

English:
theorem _root_.MeasurableEmbedding.memLp_map_measure_iff
  given: (hf : MeasurableEmbedding f)
  proof: by
  simp_rw [MemLp, hf.aestronglyMeasurable_map_iff, hf.eLpNorm_map_measure]

中文:
定理 _root_.可测嵌入.memLp_map_measure_iff
  条件: (hf : 可测嵌入 f)
  证明: by
  simp_rw [MemLp, hf.aestronglyMeasurable_map_iff, hf.eLpNorm_map_measure]

Depends on / 依赖: aestronglyMeasurable_map_iff, eLpNorm_map_measure, hf.aestronglyMeasurable_map_iff, hf.eLpNorm_map_measure, simp_rw
-/
theorem _root_.MeasurableEmbedding.memLp_map_measure_iff (hf : MeasurableEmbedding f) :
    MemLp g p (Measure.map f μ) ↔ MemLp (g ∘ f) p μ := by
  simp_rw [MemLp, hf.aestronglyMeasurable_map_iff, hf.eLpNorm_map_measure]

/--
theorem `_root_.MeasurableEquiv.memLp_map_measure_iff` / 定理 `_root_.MeasurableEquiv.memLp_map_measure_iff`

English:
theorem _root_.MeasurableEquiv.memLp_map_measure_iff
  given: (f : α ≃ᵐ β)
  proof: f.measurableEmbedding.memLp_map_measure_iff

中文:
定理 _root_.可测等价.memLp_map_measure_iff
  条件: (f : α ≃ᵐ β)
  证明: f.measurableEmbedding.memLp_map_measure_iff

Depends on / 依赖: f.measurableEmbedding.memLp_map_measure_iff, measurableEmbedding, memLp_map_measure_iff
-/
theorem _root_.MeasurableEquiv.memLp_map_measure_iff (f : α ≃ᵐ β) :
    MemLp g p (Measure.map f μ) ↔ MemLp (g ∘ f) p μ :=
  f.measurableEmbedding.memLp_map_measure_iff

end MapMeasure

section Liminf

variable [MeasurableSpace E] [OpensMeasurableSpace E] {R : Real>=0}

/--
theorem `ae_bdd_liminf_atTop_rpow_of_eLpNorm_bdd` / 定理 `ae_bdd_liminf_atTop_rpow_of_eLpNorm_bdd`

English:
theorem ae_bdd_liminf_atTop_rpow_of_eLpNorm_bdd
  statement: {p : Real>=0∞} {f : Nat -> α -> E}
  proof: by
  by_cases hp0 : p.toReal = 0
  · simp only [hp0, ENNReal.rpow_zero]
    filter_upwards with _
    rw [liminf_const (1 : Real>=0∞)]
    exact ENNReal.one_lt_top
  have hp : p != 0 := fun h => by simp [h] at hp0
  have hp' : p != ∞ := fun h => by simp [h] at hp0
  refine
    ae_lt_top (.liminf fun n => (hfmeas n).nnnorm.coe_nnreal_ennreal.pow_const p.toReal)
      (lt_of_le_of_lt
          (lintegral_liminf_le fun n => (hfmeas n).nnnorm.coe_nnreal_ennreal.pow_const p.toReal)
          (lt_of_le_of_lt ?_ (by finiteness : (R : Real>=0∞) ^ p.toReal < ∞))).ne
  simp_rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp hp', one_div] at hbdd
  simp_rw [liminf_eq, eventually_atTop]
  exact
    sSup_le fun b ⟨a, ha⟩ =>
      (ha a le_rfl).trans ((ENNReal.rpow_inv_le_iff (ENNReal.toReal_pos hp hp')).1 (hbdd _))

中文:
定理 ae_bdd_liminf_atTop_rpow_of_eLpNorm_bdd
  结论: {p : 实数>=0∞} {f : 自然数 -> α -> E}
  证明: by
  by_cases hp0 : p.toReal = 0
  · simp only [hp0, ENNReal.rpow_zero]
    filter_upwards with _
    rw [liminf_const (1 : Real>=0∞)]
    exact ENNReal.one_lt_top
  have hp : p != 0 := fun h => by simp [h] at hp0
  have hp' : p != ∞ := fun h => by simp [h] at hp0
  refine
    ae_lt_top (.liminf fun n => (hfmeas n).nnnorm.coe_nnreal_ennreal.pow_const p.toReal)
      (lt_of_le_of_lt
          (lintegral_liminf_le fun n => (hfmeas n).nnnorm.coe_nnreal_ennreal.pow_const p.toReal)
          (lt_of_le_of_lt ?_ (by finiteness : (R : Real>=0∞) ^ p.toReal < ∞))).ne
  simp_rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp hp', one_div] at hbdd
  simp_rw [liminf_eq, eventually_atTop]
  exact
    sSup_le fun b ⟨a, ha⟩ =>
      (ha a le_rfl).trans ((ENNReal.rpow_inv_le_iff (ENNReal.toReal_pos hp hp')).1 (hbdd _))

Depends on / 依赖: ENNReal, ENNReal.one_lt_top, ENNReal.rpow_zero, ae_lt_top, coe_nnreal_ennreal, filter_upwards, finiteness, hfmeas, liminf, liminf_const, lintegral_liminf_le, lt_of_le_of_lt, nnnorm, nnnorm.coe_nnreal_ennreal.pow_const, one_lt_top, p.toRea, p.toReal, pow_const, rpow_zero, toReal
-/
theorem ae_bdd_liminf_atTop_rpow_of_eLpNorm_bdd {p : Real>=0∞} {f : Nat -> α -> E}
    (hfmeas : forall n, Measurable (f n)) (hbdd : forall n, eLpNorm (f n) p μ <= R) :
    forallᵐ x ∂μ, liminf (fun n => ((‖f n x‖ₑ) ^ p.toReal : Real>=0∞)) atTop < ∞ := by
  by_cases hp0 : p.toReal = 0
  · simp only [hp0, ENNReal.rpow_zero]
    filter_upwards with _
    rw [liminf_const (1 : Real>=0∞)]
    exact ENNReal.one_lt_top
  have hp : p != 0 := fun h => by simp [h] at hp0
  have hp' : p != ∞ := fun h => by simp [h] at hp0
  refine
    ae_lt_top (.liminf fun n => (hfmeas n).nnnorm.coe_nnreal_ennreal.pow_const p.toReal)
      (lt_of_le_of_lt
          (lintegral_liminf_le fun n => (hfmeas n).nnnorm.coe_nnreal_ennreal.pow_const p.toReal)
          (lt_of_le_of_lt ?_ (by finiteness : (R : Real>=0∞) ^ p.toReal < ∞))).ne
  simp_rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp hp', one_div] at hbdd
  simp_rw [liminf_eq, eventually_atTop]
  exact
    sSup_le fun b ⟨a, ha⟩ =>
      (ha a le_rfl).trans ((ENNReal.rpow_inv_le_iff (ENNReal.toReal_pos hp hp')).1 (hbdd _))

/--
theorem `ae_bdd_liminf_atTop_of_eLpNorm_bdd` / 定理 `ae_bdd_liminf_atTop_of_eLpNorm_bdd`

English:
theorem ae_bdd_liminf_atTop_of_eLpNorm_bdd
  statement: {p : Real>=0∞} (hp : p != 0) {f : Nat -> α -> E}
  proof: by
  by_cases hp' : p = ∞
  · subst hp'
    simp_rw [eLpNorm_exponent_top] at hbdd
    have : forall n, forallᵐ x ∂μ, (‖f n x‖ₑ) < R + 1 := fun n =>
      ae_lt_of_essSup_lt
        (lt_of_le_of_lt (hbdd n) <| ENNReal.lt_add_right ENNReal.coe_ne_top one_ne_zero)
    rw [← ae_all_iff] at this
    filter_upwards [this] with x hx using lt_of_le_of_lt
        (liminf_le_of_frequently_le' <| Frequently.of_forall fun n => (hx n).le)
        (ENNReal.add_lt_top.2 ⟨ENNReal.coe_lt_top, ENNReal.one_lt_top⟩)
  filter_upwards [ae_bdd_liminf_atTop_rpow_of_eLpNorm_bdd hfmeas hbdd] with x hx
  have hppos : 0 < p.toReal := ENNReal.toReal_pos hp hp'
  have :
    liminf (fun n => (‖f n x‖ₑ) ^ p.toReal) atTop =
      liminf (fun n => (‖f n x‖ₑ)) atTop ^ p.toReal := by
    change
      liminf (fun n => ENNReal.orderIsoRpow p.toReal hppos (‖f n x‖ₑ)) atTop =
        ENNReal.orderIsoRpow p.toReal hppos (liminf (fun n => (‖f n x‖ₑ)) atTop)
    refine (OrderIso.liminf_apply (ENNReal.orderIsoRpow p.toReal _) ?_ ?_ ?_ ?_).symm <;>
      isBoundedDefault
  rw [this] at hx
  rw [← ENNReal.rpow_one (liminf (‖f · x‖ₑ) atTop)]; rw [← mul_inv_cancel₀ hppos.ne.symm]; rw [ENNReal.rpow_mul]
  exact ENNReal.rpow_lt_top_of_nonneg (inv_nonneg.2 hppos.le) hx.ne

中文:
定理 ae_bdd_liminf_atTop_of_eLpNorm_bdd
  结论: {p : 实数>=0∞} (hp : p != 0) {f : 自然数 -> α -> E}
  证明: by
  by_cases hp' : p = ∞
  · subst hp'
    simp_rw [eLpNorm_exponent_top] at hbdd
    have : forall n, forallᵐ x ∂μ, (‖f n x‖ₑ) < R + 1 := fun n =>
      ae_lt_of_essSup_lt
        (lt_of_le_of_lt (hbdd n) <| ENNReal.lt_add_right ENNReal.coe_ne_top one_ne_zero)
    rw [← ae_all_iff] at this
    filter_upwards [this] with x hx using lt_of_le_of_lt
        (liminf_le_of_frequently_le' <| Frequently.of_forall fun n => (hx n).le)
        (ENNReal.add_lt_top.2 ⟨ENNReal.coe_lt_top, ENNReal.one_lt_top⟩)
  filter_upwards [ae_bdd_liminf_atTop_rpow_of_eLpNorm_bdd hfmeas hbdd] with x hx
  have hppos : 0 < p.toReal := ENNReal.toReal_pos hp hp'
  have :
    liminf (fun n => (‖f n x‖ₑ) ^ p.toReal) atTop =
      liminf (fun n => (‖f n x‖ₑ)) atTop ^ p.toReal := by
    change
      liminf (fun n => ENNReal.orderIsoRpow p.toReal hppos (‖f n x‖ₑ)) atTop =
        ENNReal.orderIsoRpow p.toReal hppos (liminf (fun n => (‖f n x‖ₑ)) atTop)
    refine (OrderIso.liminf_apply (ENNReal.orderIsoRpow p.toReal _) ?_ ?_ ?_ ?_).symm <;>
      isBoundedDefault
  rw [this] at hx
  rw [← ENNReal.rpow_one (liminf (‖f · x‖ₑ) atTop)]; rw [← mul_inv_cancel₀ hppos.ne.symm]; rw [ENNReal.rpow_mul]
  exact ENNReal.rpow_lt_top_of_nonneg (inv_nonneg.2 hppos.le) hx.ne

Depends on / 依赖: ENNReal, ENNReal.add_lt_top, ENNReal.coe_lt_top, ENNReal.coe_ne_top, ENNReal.lt_add_right, ENNReal.one_lt_top, Frequently, Frequently.of_forall, add_lt_top, ae_all_iff, ae_bdd_liminf_atTop_rpow_of_eLp, ae_lt_of_essSup_lt, coe_lt_top, coe_ne_top, eLpNorm_exponent_top, filter_upwards, liminf_le_of_frequently_le, lt_add_right, lt_of_le_of_lt, of_forall
-/
theorem ae_bdd_liminf_atTop_of_eLpNorm_bdd {p : Real>=0∞} (hp : p != 0) {f : Nat -> α -> E}
    (hfmeas : forall n, Measurable (f n)) (hbdd : forall n, eLpNorm (f n) p μ <= R) :
    forallᵐ x ∂μ, liminf (fun n => (‖f n x‖ₑ)) atTop < ∞ := by
  by_cases hp' : p = ∞
  · subst hp'
    simp_rw [eLpNorm_exponent_top] at hbdd
    have : forall n, forallᵐ x ∂μ, (‖f n x‖ₑ) < R + 1 := fun n =>
      ae_lt_of_essSup_lt
        (lt_of_le_of_lt (hbdd n) <| ENNReal.lt_add_right ENNReal.coe_ne_top one_ne_zero)
    rw [← ae_all_iff] at this
    filter_upwards [this] with x hx using lt_of_le_of_lt
        (liminf_le_of_frequently_le' <| Frequently.of_forall fun n => (hx n).le)
        (ENNReal.add_lt_top.2 ⟨ENNReal.coe_lt_top, ENNReal.one_lt_top⟩)
  filter_upwards [ae_bdd_liminf_atTop_rpow_of_eLpNorm_bdd hfmeas hbdd] with x hx
  have hppos : 0 < p.toReal := ENNReal.toReal_pos hp hp'
  have :
    liminf (fun n => (‖f n x‖ₑ) ^ p.toReal) atTop =
      liminf (fun n => (‖f n x‖ₑ)) atTop ^ p.toReal := by
    change
      liminf (fun n => ENNReal.orderIsoRpow p.toReal hppos (‖f n x‖ₑ)) atTop =
        ENNReal.orderIsoRpow p.toReal hppos (liminf (fun n => (‖f n x‖ₑ)) atTop)
    refine (OrderIso.liminf_apply (ENNReal.orderIsoRpow p.toReal _) ?_ ?_ ?_ ?_).symm <;>
      isBoundedDefault
  rw [this] at hx
  rw [← ENNReal.rpow_one (liminf (‖f · x‖ₑ) atTop)]; rw [← mul_inv_cancel₀ hppos.ne.symm]; rw [ENNReal.rpow_mul]
  exact ENNReal.rpow_lt_top_of_nonneg (inv_nonneg.2 hppos.le) hx.ne

end Liminf

/--
theorem `_root_.Continuous.memLp_top_of_hasCompactSupport` / 定理 `_root_.Continuous.memLp_top_of_hasCompactSupport`

English:
theorem _root_.Continuous.memLp_top_of_hasCompactSupport
  proof: by
  borelize E
  rcases hf.bounded_above_of_compact_support h'f with ⟨C, hC⟩
  apply memLp_top_of_bound ?_ C (Filter.Eventually.of_forall hC)
  exact (hf.stronglyMeasurable_of_hasCompactSupport h'f).aestronglyMeasurable

中文:
定理 _root_.连续.memLp_top_of_hasCompactSupport
  证明: by
  borelize E
  rcases hf.bounded_above_of_compact_support h'f with ⟨C, hC⟩
  apply memLp_top_of_bound ?_ C (Filter.Eventually.of_forall hC)
  exact (hf.stronglyMeasurable_of_hasCompactSupport h'f).aestronglyMeasurable

Depends on / 依赖: Eventually, Filter, Filter.Eventually.of_forall, aestronglyMeasurable, borelize, bounded_above_of_compact_support, hf.bounded_above_of_compact_support, hf.stronglyMeasurable_of_hasCompactSupport, memLp_top_of_bound, of_forall, stronglyMeasurable_of_hasCompactSupport
-/
theorem _root_.Continuous.memLp_top_of_hasCompactSupport
    {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    {f : X -> E} (hf : Continuous f) (h'f : HasCompactSupport f) (μ : Measure X) : MemLp f ⊤ μ := by
  borelize E
  rcases hf.bounded_above_of_compact_support h'f with ⟨C, hC⟩
  apply memLp_top_of_bound ?_ C (Filter.Eventually.of_forall hC)
  exact (hf.stronglyMeasurable_of_hasCompactSupport h'f).aestronglyMeasurable

end Lp
end MeasureTheory
