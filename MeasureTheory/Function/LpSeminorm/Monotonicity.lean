/-
Copyright (c) 2020 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Sébastien Gouëzel
-/
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

/-!
# Monotonicity and ℒp seminorms
-/

public noncomputable section

open TopologicalSpace MeasureTheory Filter

open scoped NNReal ENNReal ComplexConjugate

variable {α E F G : Type*} {m : MeasurableSpace α} {p : Real>=0∞} {q : Real} {μ : Measure α}
  [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedAddCommGroup G]

namespace MeasureTheory

section Monotonicity

variable {ε ε' : Type*} [TopologicalSpace ε] [ContinuousENorm ε]
  [TopologicalSpace ε'] [ContinuousENorm ε']

/--
theorem `eLpNorm'_le_nnreal_smul_eLpNorm'_of_ae_le_mul` / 定理 `eLpNorm'_le_nnreal_smul_eLpNorm'_of_ae_le_mul`

English:
theorem eLpNorm'_le_nnreal_smul_eLpNorm'_of_ae_le_mul
  statement: {f : α -> F} {g : α -> G} {c : Real>=0}
  proof: by
  simp_rw [eLpNorm'_eq_lintegral_enorm]
  rw [← ENNReal.rpow_le_rpow_iff hp]; rw [ENNReal.smul_def]; rw [smul_eq_mul]; rw [ENNReal.mul_rpow_of_nonneg _ _ hp.le]
  simp_rw [← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hp.ne', ENNReal.rpow_one, enorm,
    ← ENNReal.coe_rpow_of_nonneg _ hp.le, ← lintegral_const_mul' _ _ ENNReal.coe_ne_top,
    ← ENNReal.coe_mul]
  apply lintegral_mono_ae
  filter_upwards [h] with x hx
  rw [← NNReal.mul_rpow]
  gcongr

中文:
定理 eLpNorm'_le_nnreal_smul_eLpNorm'_of_ae_le_mul
  结论: {f : α -> F} {g : α -> G} {c : 实数>=0}
  证明: by
  simp_rw [eLpNorm'_eq_lintegral_enorm]
  rw [← ENNReal.rpow_le_rpow_iff hp]; rw [ENNReal.smul_def]; rw [smul_eq_mul]; rw [ENNReal.mul_rpow_of_nonneg _ _ hp.le]
  simp_rw [← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hp.ne', ENNReal.rpow_one, enorm,
    ← ENNReal.coe_rpow_of_nonneg _ hp.le, ← lintegral_const_mul' _ _ ENNReal.coe_ne_top,
    ← ENNReal.coe_mul]
  apply lintegral_mono_ae
  filter_upwards [h] with x hx
  rw [← NNReal.mul_rpow]
  gcongr
-/
theorem eLpNorm'_le_nnreal_smul_eLpNorm'_of_ae_le_mul {f : α -> F} {g : α -> G} {c : Real>=0}
    (h : forallᵐ x ∂μ, ‖f x‖₊ <= c * ‖g x‖₊) {p : Real} (hp : 0 < p) :
    eLpNorm' f p μ <= c • eLpNorm' g p μ := by
  simp_rw [eLpNorm'_eq_lintegral_enorm]
  rw [← ENNReal.rpow_le_rpow_iff hp]; rw [ENNReal.smul_def]; rw [smul_eq_mul]; rw [ENNReal.mul_rpow_of_nonneg _ _ hp.le]
  simp_rw [← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hp.ne', ENNReal.rpow_one, enorm,
    ← ENNReal.coe_rpow_of_nonneg _ hp.le, ← lintegral_const_mul' _ _ ENNReal.coe_ne_top,
    ← ENNReal.coe_mul]
  apply lintegral_mono_ae
  filter_upwards [h] with x hx
  rw [← NNReal.mul_rpow]
  gcongr

-- TODO: eventually, deprecate and remove the nnnorm version
/--
theorem `eLpNorm'_le_nnreal_smul_eLpNorm'_of_ae_le_mul'` / 定理 `eLpNorm'_le_nnreal_smul_eLpNorm'_of_ae_le_mul'`

English:
theorem eLpNorm'_le_nnreal_smul_eLpNorm'_of_ae_le_mul'
  statement: {f : α -> ε} {g : α -> ε'} {c : Real>=0}
  proof: by
  simp_rw [eLpNorm'_eq_lintegral_enorm]
  rw [← ENNReal.rpow_le_rpow_iff hp]; rw [ENNReal.smul_def]; rw [smul_eq_mul]; rw [ENNReal.mul_rpow_of_nonneg _ _ hp.le]
  simp_rw [← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hp.ne', ENNReal.rpow_one,
    ← ENNReal.coe_rpow_of_nonneg _ hp.le, ← lintegral_const_mul' _ _ ENNReal.coe_ne_top]
  apply lintegral_mono_ae
  have aux (x) : (↑c) ^ p * ‖g x‖ₑ ^ p = (↑c * ‖g x‖ₑ) ^ p := by
    have : ¬(p < 0) := by linarith
    simp [ENNReal.mul_rpow_eq_ite, this]
  simpa [ENNReal.coe_rpow_of_nonneg _ hp.le, aux, ENNReal.rpow_le_rpow_iff hp]

中文:
定理 eLpNorm'_le_nnreal_smul_eLpNorm'_of_ae_le_mul'
  结论: {f : α -> ε} {g : α -> ε'} {c : 实数>=0}
  证明: by
  simp_rw [eLpNorm'_eq_lintegral_enorm]
  rw [← ENNReal.rpow_le_rpow_iff hp]; rw [ENNReal.smul_def]; rw [smul_eq_mul]; rw [ENNReal.mul_rpow_of_nonneg _ _ hp.le]
  simp_rw [← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hp.ne', ENNReal.rpow_one,
    ← ENNReal.coe_rpow_of_nonneg _ hp.le, ← lintegral_const_mul' _ _ ENNReal.coe_ne_top]
  apply lintegral_mono_ae
  have aux (x) : (↑c) ^ p * ‖g x‖ₑ ^ p = (↑c * ‖g x‖ₑ) ^ p := by
    have : ¬(p < 0) := by linarith
    simp [ENNReal.mul_rpow_eq_ite, this]
  simpa [ENNReal.coe_rpow_of_nonneg _ hp.le, aux, ENNReal.rpow_le_rpow_iff hp]
-/
theorem eLpNorm'_le_nnreal_smul_eLpNorm'_of_ae_le_mul' {f : α -> ε} {g : α -> ε'} {c : Real>=0}
    (h : forallᵐ x ∂μ, ‖f x‖ₑ <= c * ‖g x‖ₑ) {p : Real} (hp : 0 < p) :
    eLpNorm' f p μ <= c • eLpNorm' g p μ := by
  simp_rw [eLpNorm'_eq_lintegral_enorm]
  rw [← ENNReal.rpow_le_rpow_iff hp]; rw [ENNReal.smul_def]; rw [smul_eq_mul]; rw [ENNReal.mul_rpow_of_nonneg _ _ hp.le]
  simp_rw [← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hp.ne', ENNReal.rpow_one,
    ← ENNReal.coe_rpow_of_nonneg _ hp.le, ← lintegral_const_mul' _ _ ENNReal.coe_ne_top]
  apply lintegral_mono_ae
  have aux (x) : (↑c) ^ p * ‖g x‖ₑ ^ p = (↑c * ‖g x‖ₑ) ^ p := by
    have : ¬(p < 0) := by linarith
    simp [ENNReal.mul_rpow_eq_ite, this]
  simpa [ENNReal.coe_rpow_of_nonneg _ hp.le, aux, ENNReal.rpow_le_rpow_iff hp]

section ESeminormedAddMonoid

variable {ε : Type*} [TopologicalSpace ε] [ESeminormedAddMonoid ε]

/--
theorem `eLpNorm'_le_mul_eLpNorm'_of_ae_le_mul` / 定理 `eLpNorm'_le_mul_eLpNorm'_of_ae_le_mul`

English:
theorem eLpNorm'_le_mul_eLpNorm'_of_ae_le_mul
  statement: {f : α -> ε} {c : Real>=0∞} {g : α -> ε'} {p : Real}
  proof: by
  have hp' : ¬(p < 0) := by linarith
  by_cases hc : c = ⊤
  · by_cases hg' : eLpNorm' g p μ = 0
    · have : forallᵐ (x : α) ∂μ, ‖g x‖ₑ = 0 := by
        simp only [eLpNorm'_eq_lintegral_enorm, one_div, ENNReal.rpow_eq_zero_iff, inv_pos, hp,
          and_true, inv_neg'', hp', and_false, or_false] at hg'
        rw [MeasureTheory.lintegral_eq_zero_iff' (by fun_prop)] at hg'
        exact hg'.mono fun x hx => by simpa [hp, hp'] using hx
      have : forallᵐ (x : α) ∂μ, ‖f x‖ₑ = 0 := (this.and h).mono fun x ⟨h, h'⟩ => by simp_all
      simpa only [hg', mul_zero, nonpos_iff_eq_zero] using eLpNorm'_eq_zero_of_ae_eq_zero hp this
    · simp_all
  have : c ^ p != ⊤ := by simp [hp.le, hc]
  simp_rw [eLpNorm'_eq_lintegral_enorm]
  rw [← ENNReal.rpow_le_rpow_iff hp]; rw [ENNReal.mul_rpow_of_nonneg _ _ hp.le]
  simp_rw [← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hp.ne', ENNReal.rpow_one,
    ← lintegral_const_mul' _ _ this]
  apply lintegral_mono_ae
  have aux (x) : (↑c) ^ p * ‖g x‖ₑ ^ p = (↑c * ‖g x‖ₑ) ^ p := by
    simp [ENNReal.mul_rpow_eq_ite, hp']
  simpa [ENNReal.coe_rpow_of_nonneg _ hp.le, aux, ENNReal.rpow_le_rpow_iff hp]

中文:
定理 eLpNorm'_le_mul_eLpNorm'_of_ae_le_mul
  结论: {f : α -> ε} {c : 实数>=0∞} {g : α -> ε'} {p : 实数}
  证明: by
  have hp' : ¬(p < 0) := by linarith
  by_cases hc : c = ⊤
  · by_cases hg' : eLpNorm' g p μ = 0
    · have : forallᵐ (x : α) ∂μ, ‖g x‖ₑ = 0 := by
        simp only [eLpNorm'_eq_lintegral_enorm, one_div, ENNReal.rpow_eq_zero_iff, inv_pos, hp,
          and_true, inv_neg'', hp', and_false, or_false] at hg'
        rw [MeasureTheory.lintegral_eq_zero_iff' (by fun_prop)] at hg'
        exact hg'.mono fun x hx => by simpa [hp, hp'] using hx
      have : forallᵐ (x : α) ∂μ, ‖f x‖ₑ = 0 := (this.and h).mono fun x ⟨h, h'⟩ => by simp_all
      simpa only [hg', mul_zero, nonpos_iff_eq_zero] using eLpNorm'_eq_zero_of_ae_eq_zero hp this
    · simp_all
  have : c ^ p != ⊤ := by simp [hp.le, hc]
  simp_rw [eLpNorm'_eq_lintegral_enorm]
  rw [← ENNReal.rpow_le_rpow_iff hp]; rw [ENNReal.mul_rpow_of_nonneg _ _ hp.le]
  simp_rw [← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hp.ne', ENNReal.rpow_one,
    ← lintegral_const_mul' _ _ this]
  apply lintegral_mono_ae
  have aux (x) : (↑c) ^ p * ‖g x‖ₑ ^ p = (↑c * ‖g x‖ₑ) ^ p := by
    simp [ENNReal.mul_rpow_eq_ite, hp']
  simpa [ENNReal.coe_rpow_of_nonneg _ hp.le, aux, ENNReal.rpow_le_rpow_iff hp]
-/
theorem eLpNorm'_le_mul_eLpNorm'_of_ae_le_mul {f : α -> ε} {c : Real>=0∞} {g : α -> ε'} {p : Real}
    (hg : AEStronglyMeasurable g μ) (h : forallᵐ x ∂μ, ‖f x‖ₑ <= c * ‖g x‖ₑ) (hp : 0 < p) :
    eLpNorm' f p μ <= c * eLpNorm' g p μ := by
  have hp' : ¬(p < 0) := by linarith
  by_cases hc : c = ⊤
  · by_cases hg' : eLpNorm' g p μ = 0
    · have : forallᵐ (x : α) ∂μ, ‖g x‖ₑ = 0 := by
        simp only [eLpNorm'_eq_lintegral_enorm, one_div, ENNReal.rpow_eq_zero_iff, inv_pos, hp,
          and_true, inv_neg'', hp', and_false, or_false] at hg'
        rw [MeasureTheory.lintegral_eq_zero_iff' (by fun_prop)] at hg'
        exact hg'.mono fun x hx => by simpa [hp, hp'] using hx
      have : forallᵐ (x : α) ∂μ, ‖f x‖ₑ = 0 := (this.and h).mono fun x ⟨h, h'⟩ => by simp_all
      simpa only [hg', mul_zero, nonpos_iff_eq_zero] using eLpNorm'_eq_zero_of_ae_eq_zero hp this
    · simp_all
  have : c ^ p != ⊤ := by simp [hp.le, hc]
  simp_rw [eLpNorm'_eq_lintegral_enorm]
  rw [← ENNReal.rpow_le_rpow_iff hp]; rw [ENNReal.mul_rpow_of_nonneg _ _ hp.le]
  simp_rw [← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hp.ne', ENNReal.rpow_one,
    ← lintegral_const_mul' _ _ this]
  apply lintegral_mono_ae
  have aux (x) : (↑c) ^ p * ‖g x‖ₑ ^ p = (↑c * ‖g x‖ₑ) ^ p := by
    simp [ENNReal.mul_rpow_eq_ite, hp']
  simpa [ENNReal.coe_rpow_of_nonneg _ hp.le, aux, ENNReal.rpow_le_rpow_iff hp]

end ESeminormedAddMonoid

-- TODO: eventually, deprecate and remove the nnnorm version
/--
theorem `eLpNormEssSup_le_nnreal_smul_eLpNormEssSup_of_ae_le_mul'` / 定理 `eLpNormEssSup_le_nnreal_smul_eLpNormEssSup_of_ae_le_mul'`

English:
theorem eLpNormEssSup_le_nnreal_smul_eLpNormEssSup_of_ae_le_mul'
  statement: {f : α -> ε} {g : α -> ε'} {c : Real>=0∞}
  proof: calc
essSup (‖f ·‖ₑ) μ <= essSup (c * ‖g ·‖ₑ) μ := essSup_mono_ae h
    _ = c • essSup (‖g ·‖ₑ) μ := ENNReal.essSup_const_mul

中文:
定理 eLpNormEssSup_le_nnreal_smul_eLpNormEssSup_of_ae_le_mul'
  结论: {f : α -> ε} {g : α -> ε'} {c : 实数>=0∞}
  证明: calc
essSup (‖f ·‖ₑ) μ <= essSup (c * ‖g ·‖ₑ) μ := essSup_mono_ae h
    _ = c • essSup (‖g ·‖ₑ) μ := ENNReal.essSup_const_mul

Depends on / 依赖: ENNReal, ENNReal.essSup_const_mul, essSup, essSup_const_mul, essSup_mono_ae
-/
theorem eLpNormEssSup_le_nnreal_smul_eLpNormEssSup_of_ae_le_mul' {f : α -> ε} {g : α -> ε'} {c : Real>=0∞}
    (h : forallᵐ x ∂μ, ‖f x‖ₑ <= c * ‖g x‖ₑ) : eLpNormEssSup f μ <= c • eLpNormEssSup g μ :=
  calc
essSup (‖f ·‖ₑ) μ <= essSup (c * ‖g ·‖ₑ) μ := essSup_mono_ae h
    _ = c • essSup (‖g ·‖ₑ) μ := ENNReal.essSup_const_mul

/--
theorem `eLpNormEssSup_le_nnreal_smul_eLpNormEssSup_of_ae_le_mul` / 定理 `eLpNormEssSup_le_nnreal_smul_eLpNormEssSup_of_ae_le_mul`

English:
theorem eLpNormEssSup_le_nnreal_smul_eLpNormEssSup_of_ae_le_mul
  statement: {f : α -> F} {g : α -> G} {c : Real>=0}
  proof: calc
    essSup (‖f ·‖ₑ) μ <= essSup (fun x => (↑(c * ‖g x‖₊) : Real>=0∞)) μ :=
essSup_mono_ae h.mono fun _ hx => ENNReal.coe_le_coe.mpr hx
    _ = essSup (c * ‖g ·‖ₑ) μ := by simp_rw [ENNReal.coe_mul, enorm]
    _ = c • essSup (‖g ·‖ₑ) μ := ENNReal.essSup_const_mul

中文:
定理 eLpNormEssSup_le_nnreal_smul_eLpNormEssSup_of_ae_le_mul
  结论: {f : α -> F} {g : α -> G} {c : 实数>=0}
  证明: calc
    essSup (‖f ·‖ₑ) μ <= essSup (fun x => (↑(c * ‖g x‖₊) : Real>=0∞)) μ :=
essSup_mono_ae h.mono fun _ hx => ENNReal.coe_le_coe.mpr hx
    _ = essSup (c * ‖g ·‖ₑ) μ := by simp_rw [ENNReal.coe_mul, enorm]
    _ = c • essSup (‖g ·‖ₑ) μ := ENNReal.essSup_const_mul

Depends on / 依赖: ENNReal, ENNReal.coe_le_coe.mpr, ENNReal.coe_mul, ENNReal.essSup_const_mul, coe_le_coe, coe_mul, essSup, essSup_const_mul, essSup_mono_ae, h.mono, simp_rw
-/
theorem eLpNormEssSup_le_nnreal_smul_eLpNormEssSup_of_ae_le_mul {f : α -> F} {g : α -> G} {c : Real>=0}
    (h : forallᵐ x ∂μ, ‖f x‖₊ <= c * ‖g x‖₊) : eLpNormEssSup f μ <= c • eLpNormEssSup g μ :=
  calc
    essSup (‖f ·‖ₑ) μ <= essSup (fun x => (↑(c * ‖g x‖₊) : Real>=0∞)) μ :=
essSup_mono_ae h.mono fun _ hx => ENNReal.coe_le_coe.mpr hx
    _ = essSup (c * ‖g ·‖ₑ) μ := by simp_rw [ENNReal.coe_mul, enorm]
    _ = c • essSup (‖g ·‖ₑ) μ := ENNReal.essSup_const_mul

-- TODO: eventually, deprecate and remove the nnnorm version
/--
theorem `eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul'` / 定理 `eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul'`

English:
theorem eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul'
  statement: {f : α -> ε} {g : α -> ε'} {c : Real>=0}
  proof: by
  by_cases h0 : p = 0
  · simp [h0]
  by_cases h_top : p = ∞
  · rw [h_top]
    exact eLpNormEssSup_le_nnreal_smul_eLpNormEssSup_of_ae_le_mul' h
  simp_rw [eLpNorm_eq_eLpNorm' h0 h_top]
  exact eLpNorm'_le_nnreal_smul_eLpNorm'_of_ae_le_mul' h (ENNReal.toReal_pos h0 h_top)

中文:
定理 eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul'
  结论: {f : α -> ε} {g : α -> ε'} {c : 实数>=0}
  证明: by
  by_cases h0 : p = 0
  · simp [h0]
  by_cases h_top : p = ∞
  · rw [h_top]
    exact eLpNormEssSup_le_nnreal_smul_eLpNormEssSup_of_ae_le_mul' h
  simp_rw [eLpNorm_eq_eLpNorm' h0 h_top]
  exact eLpNorm'_le_nnreal_smul_eLpNorm'_of_ae_le_mul' h (ENNReal.toReal_pos h0 h_top)

Depends on / 依赖: ENNReal, ENNReal.toReal_pos, _le_nnreal_smul_eLpNorm, _of_ae_le_mul, eLpNorm, eLpNormEssSup_le_nnreal_smul_eLpNormEssSup_of_ae_le_mul, eLpNorm_eq_eLpNorm, h_top, simp_rw, toReal_pos
-/
theorem eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul' {f : α -> ε} {g : α -> ε'} {c : Real>=0}
    (h : forallᵐ x ∂μ, ‖f x‖ₑ <= c * ‖g x‖ₑ) (p : Real>=0∞) : eLpNorm f p μ <= c • eLpNorm g p μ := by
  by_cases h0 : p = 0
  · simp [h0]
  by_cases h_top : p = ∞
  · rw [h_top]
    exact eLpNormEssSup_le_nnreal_smul_eLpNormEssSup_of_ae_le_mul' h
  simp_rw [eLpNorm_eq_eLpNorm' h0 h_top]
  exact eLpNorm'_le_nnreal_smul_eLpNorm'_of_ae_le_mul' h (ENNReal.toReal_pos h0 h_top)

/--
theorem `eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul` / 定理 `eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul`

English:
theorem eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul
  statement: {f : α -> F} {g : α -> G} {c : Real>=0}
  proof: by
  by_cases h0 : p = 0
  · simp [h0]
  by_cases h_top : p = ∞
  · rw [h_top]
    exact eLpNormEssSup_le_nnreal_smul_eLpNormEssSup_of_ae_le_mul h
  simp_rw [eLpNorm_eq_eLpNorm' h0 h_top]
  exact eLpNorm'_le_nnreal_smul_eLpNorm'_of_ae_le_mul h (ENNReal.toReal_pos h0 h_top)

中文:
定理 eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul
  结论: {f : α -> F} {g : α -> G} {c : 实数>=0}
  证明: by
  by_cases h0 : p = 0
  · simp [h0]
  by_cases h_top : p = ∞
  · rw [h_top]
    exact eLpNormEssSup_le_nnreal_smul_eLpNormEssSup_of_ae_le_mul h
  simp_rw [eLpNorm_eq_eLpNorm' h0 h_top]
  exact eLpNorm'_le_nnreal_smul_eLpNorm'_of_ae_le_mul h (ENNReal.toReal_pos h0 h_top)

Depends on / 依赖: ENNReal, ENNReal.toReal_pos, _le_nnreal_smul_eLpNorm, _of_ae_le_mul, eLpNorm, eLpNormEssSup_le_nnreal_smul_eLpNormEssSup_of_ae_le_mul, eLpNorm_eq_eLpNorm, h_top, simp_rw, toReal_pos
-/
theorem eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul {f : α -> F} {g : α -> G} {c : Real>=0}
    (h : forallᵐ x ∂μ, ‖f x‖₊ <= c * ‖g x‖₊) (p : Real>=0∞) : eLpNorm f p μ <= c • eLpNorm g p μ := by
  by_cases h0 : p = 0
  · simp [h0]
  by_cases h_top : p = ∞
  · rw [h_top]
    exact eLpNormEssSup_le_nnreal_smul_eLpNormEssSup_of_ae_le_mul h
  simp_rw [eLpNorm_eq_eLpNorm' h0 h_top]
  exact eLpNorm'_le_nnreal_smul_eLpNorm'_of_ae_le_mul h (ENNReal.toReal_pos h0 h_top)

-- TODO: add the whole family of lemmas?
/--
theorem `le_mul_iff_eq_zero_of_nonneg_of_neg_of_nonneg` / 定理 `le_mul_iff_eq_zero_of_nonneg_of_neg_of_nonneg`

English:
theorem le_mul_iff_eq_zero_of_nonneg_of_neg_of_nonneg
  statement: {α}
  proof: by
  constructor
  · intro h
    exact
      ⟨(h.trans (mul_nonpos_of_nonpos_of_nonneg hb.le hc)).antisymm ha,
        (nonpos_of_mul_nonneg_right (ha.trans h) hb).antisymm hc⟩
  · rintro ⟨rfl, rfl⟩
    rw [mul_zero]

中文:
定理 le_mul_iff_eq_zero_of_nonneg_of_neg_of_nonneg
  结论: {α}
  证明: by
  constructor
  · intro h
    exact
      ⟨(h.trans (mul_nonpos_of_nonpos_of_nonneg hb.le hc)).antisymm ha,
        (nonpos_of_mul_nonneg_right (ha.trans h) hb).antisymm hc⟩
  · rintro ⟨rfl, rfl⟩
    rw [mul_zero]
-/
private theorem le_mul_iff_eq_zero_of_nonneg_of_neg_of_nonneg {α}
    [Semiring α] [LinearOrder α] [IsStrictOrderedRing α]
    {a b c : α} (ha : 0 <= a) (hb : b < 0) (hc : 0 <= c) : a <= b * c ↔ a = 0 ∧ c = 0 := by
  constructor
  · intro h
    exact
      ⟨(h.trans (mul_nonpos_of_nonpos_of_nonneg hb.le hc)).antisymm ha,
        (nonpos_of_mul_nonneg_right (ha.trans h) hb).antisymm hc⟩
  · rintro ⟨rfl, rfl⟩
    rw [mul_zero]

/--
theorem `eLpNorm_eq_zero_and_zero_of_ae_le_mul_neg` / 定理 `eLpNorm_eq_zero_and_zero_of_ae_le_mul_neg`

English:
theorem eLpNorm_eq_zero_and_zero_of_ae_le_mul_neg
  statement: {f : α -> F} {g : α -> G} {c : Real}
  proof: by
  simp_rw [le_mul_iff_eq_zero_of_nonneg_of_neg_of_nonneg (norm_nonneg _) hc (norm_nonneg _),
    norm_eq_zero, eventually_and] at h
  change f =ᵐ[μ] 0 ∧ g =ᵐ[μ] 0 at h
  simp [eLpNorm_congr_ae h.1, eLpNorm_congr_ae h.2]

中文:
定理 eLpNorm_eq_zero_and_zero_of_ae_le_mul_neg
  结论: {f : α -> F} {g : α -> G} {c : 实数}
  证明: by
  simp_rw [le_mul_iff_eq_zero_of_nonneg_of_neg_of_nonneg (norm_nonneg _) hc (norm_nonneg _),
    norm_eq_zero, eventually_and] at h
  change f =ᵐ[μ] 0 ∧ g =ᵐ[μ] 0 at h
  simp [eLpNorm_congr_ae h.1, eLpNorm_congr_ae h.2]

Depends on / 依赖: eLpNorm_congr_ae, eventually_and, le_mul_iff_eq_zero_of_nonneg_of_neg_of_nonneg, norm_eq_zero, norm_nonneg, simp_rw
-/
theorem eLpNorm_eq_zero_and_zero_of_ae_le_mul_neg {f : α -> F} {g : α -> G} {c : Real}
    (h : forallᵐ x ∂μ, ‖f x‖ <= c * ‖g x‖) (hc : c < 0) (p : Real>=0∞) :
    eLpNorm f p μ = 0 ∧ eLpNorm g p μ = 0 := by
  simp_rw [le_mul_iff_eq_zero_of_nonneg_of_neg_of_nonneg (norm_nonneg _) hc (norm_nonneg _),
    norm_eq_zero, eventually_and] at h
  change f =ᵐ[μ] 0 ∧ g =ᵐ[μ] 0 at h
  simp [eLpNorm_congr_ae h.1, eLpNorm_congr_ae h.2]

/--
theorem `eLpNorm_le_mul_eLpNorm_of_ae_le_mul` / 定理 `eLpNorm_le_mul_eLpNorm_of_ae_le_mul`

English:
theorem eLpNorm_le_mul_eLpNorm_of_ae_le_mul
  statement: {f : α -> F} {g : α -> G} {c : Real}
  proof: eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul
    (h.mono fun _x hx => hx.trans <| mul_le_mul_of_nonneg_right c.le_coe_toNNReal (norm_nonneg _)) _

中文:
定理 eLpNorm_le_mul_eLpNorm_of_ae_le_mul
  结论: {f : α -> F} {g : α -> G} {c : 实数}
  证明: eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul
    (h.mono fun _x hx => hx.trans <| mul_le_mul_of_nonneg_right c.le_coe_toNNReal (norm_nonneg _)) _

Depends on / 依赖: c.le_coe_toNNReal, eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul, h.mono, hx.trans, le_coe_toNNReal, mul_le_mul_of_nonneg_right, norm_nonneg
-/
theorem eLpNorm_le_mul_eLpNorm_of_ae_le_mul {f : α -> F} {g : α -> G} {c : Real}
    (h : forallᵐ x ∂μ, ‖f x‖ <= c * ‖g x‖) (p : Real>=0∞) :
    eLpNorm f p μ <= ENNReal.ofReal c * eLpNorm g p μ :=
  eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul
    (h.mono fun _x hx => hx.trans <| mul_le_mul_of_nonneg_right c.le_coe_toNNReal (norm_nonneg _)) _

-- TODO: eventually, deprecate and remove the nnnorm version
/--
theorem `eLpNorm_le_mul_eLpNorm_of_ae_le_mul'` / 定理 `eLpNorm_le_mul_eLpNorm_of_ae_le_mul'`

English:
theorem eLpNorm_le_mul_eLpNorm_of_ae_le_mul'
  statement: {f : α -> ε} {g : α -> ε'} {c : Real>=0}
  proof: by
  apply eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul' h

中文:
定理 eLpNorm_le_mul_eLpNorm_of_ae_le_mul'
  结论: {f : α -> ε} {g : α -> ε'} {c : 实数>=0}
  证明: by
  apply eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul' h

Depends on / 依赖: eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul
-/
theorem eLpNorm_le_mul_eLpNorm_of_ae_le_mul' {f : α -> ε} {g : α -> ε'} {c : Real>=0}
    (h : forallᵐ x ∂μ, ‖f x‖ₑ <= c * ‖g x‖ₑ) (p : Real>=0∞) :
    eLpNorm f p μ <= c * eLpNorm g p μ := by
  apply eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul' h

variable {ε : Type*} [TopologicalSpace ε] [ESeminormedAddMonoid ε] in
/--
theorem `eLpNorm_le_mul_eLpNorm_of_ae_le_mul''` / 定理 `eLpNorm_le_mul_eLpNorm_of_ae_le_mul''`

English:
theorem eLpNorm_le_mul_eLpNorm_of_ae_le_mul''
  statement: {f : α -> ε} {c : Real>=0∞} {g : α -> ε'} (p : Real>=0∞)
  proof: by
  by_cases h₀ : p = 0
  · simp [h₀]
  simp only [eLpNorm, h₀, ↓reduceIte, mul_ite]
  by_cases hp' : p = ⊤
  · simpa [hp'] using eLpNormEssSup_le_nnreal_smul_eLpNormEssSup_of_ae_le_mul' h
  · simpa [hp'] using eLpNorm'_le_mul_eLpNorm'_of_ae_le_mul hg h (ENNReal.toReal_pos h₀ hp')

中文:
定理 eLpNorm_le_mul_eLpNorm_of_ae_le_mul''
  结论: {f : α -> ε} {c : 实数>=0∞} {g : α -> ε'} (p : 实数>=0∞)
  证明: by
  by_cases h₀ : p = 0
  · simp [h₀]
  simp only [eLpNorm, h₀, ↓reduceIte, mul_ite]
  by_cases hp' : p = ⊤
  · simpa [hp'] using eLpNormEssSup_le_nnreal_smul_eLpNormEssSup_of_ae_le_mul' h
  · simpa [hp'] using eLpNorm'_le_mul_eLpNorm'_of_ae_le_mul hg h (ENNReal.toReal_pos h₀ hp')

Depends on / 依赖: ENNReal, ENNReal.toReal_pos, _le_mul_eLpNorm, _of_ae_le_mul, eLpNorm, eLpNormEssSup_le_nnreal_smul_eLpNormEssSup_of_ae_le_mul, mul_ite, reduceIte, toReal_pos
-/
theorem eLpNorm_le_mul_eLpNorm_of_ae_le_mul'' {f : α -> ε} {c : Real>=0∞} {g : α -> ε'} (p : Real>=0∞)
    (hg : AEStronglyMeasurable g μ) (h : forallᵐ x ∂μ, ‖f x‖ₑ <= c * ‖g x‖ₑ) :
    eLpNorm f p μ <= c * eLpNorm g p μ := by
  by_cases h₀ : p = 0
  · simp [h₀]
  simp only [eLpNorm, h₀, ↓reduceIte, mul_ite]
  by_cases hp' : p = ⊤
  · simpa [hp'] using eLpNormEssSup_le_nnreal_smul_eLpNormEssSup_of_ae_le_mul' h
  · simpa [hp'] using eLpNorm'_le_mul_eLpNorm'_of_ae_le_mul hg h (ENNReal.toReal_pos h₀ hp')

/--
theorem `MemLp.of_nnnorm_le_mul` / 定理 `MemLp.of_nnnorm_le_mul`

English:
theorem MemLp.of_nnnorm_le_mul
  statement: {f : α -> E} {g : α -> F} {c : Real>=0} (hg : MemLp g p μ)
  proof: ⟨hf, (eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul hfg p).trans_lt
      ENNReal.mul_lt_top ENNReal.coe_lt_top (by finiteness)⟩

中文:
定理 MemLp.of_nnnorm_le_mul
  结论: {f : α -> E} {g : α -> F} {c : 实数>=0} (hg : MemLp g p μ)
  证明: ⟨hf, (eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul hfg p).trans_lt
      ENNReal.mul_lt_top ENNReal.coe_lt_top (by finiteness)⟩

Depends on / 依赖: ENNReal, ENNReal.coe_lt_top, ENNReal.mul_lt_top, coe_lt_top, eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul, finiteness, mul_lt_top, trans_lt
-/
theorem MemLp.of_nnnorm_le_mul {f : α -> E} {g : α -> F} {c : Real>=0} (hg : MemLp g p μ)
    (hf : AEStronglyMeasurable f μ) (hfg : forallᵐ x ∂μ, ‖f x‖₊ <= c * ‖g x‖₊) : MemLp f p μ :=
⟨hf, (eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul hfg p).trans_lt
      ENNReal.mul_lt_top ENNReal.coe_lt_top (by finiteness)⟩

/--
theorem `MemLp.of_enorm_le_mul` / 定理 `MemLp.of_enorm_le_mul`

English:
theorem MemLp.of_enorm_le_mul
  proof: ⟨hf, (eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul' hfg p).trans_lt
      ENNReal.mul_lt_top ENNReal.coe_lt_top (by finiteness)⟩

中文:
定理 MemLp.of_enorm_le_mul
  证明: ⟨hf, (eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul' hfg p).trans_lt
      ENNReal.mul_lt_top ENNReal.coe_lt_top (by finiteness)⟩

Depends on / 依赖: ENNReal, ENNReal.coe_lt_top, ENNReal.mul_lt_top, coe_lt_top, eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul, finiteness, mul_lt_top, trans_lt
-/
theorem MemLp.of_enorm_le_mul
    {f : α -> ε} {g : α -> ε'} {c : Real>=0} (hg : MemLp g p μ)
    (hf : AEStronglyMeasurable f μ) (hfg : forallᵐ x ∂μ, ‖f x‖ₑ <= c * ‖g x‖ₑ) : MemLp f p μ :=
⟨hf, (eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul' hfg p).trans_lt
      ENNReal.mul_lt_top ENNReal.coe_lt_top (by finiteness)⟩

/--
theorem `MemLp.of_le_mul` / 定理 `MemLp.of_le_mul`

English:
theorem MemLp.of_le_mul
  statement: {f : α -> E} {g : α -> F} {c : Real} (hg : MemLp g p μ)
  proof: ⟨hf,
(eLpNorm_le_mul_eLpNorm_of_ae_le_mul hfg p).trans_lt
      ENNReal.mul_lt_top ENNReal.ofReal_lt_top (by finiteness)⟩

中文:
定理 MemLp.of_le_mul
  结论: {f : α -> E} {g : α -> F} {c : 实数} (hg : MemLp g p μ)
  证明: ⟨hf,
(eLpNorm_le_mul_eLpNorm_of_ae_le_mul hfg p).trans_lt
      ENNReal.mul_lt_top ENNReal.ofReal_lt_top (by finiteness)⟩

Depends on / 依赖: ENNReal, ENNReal.mul_lt_top, ENNReal.ofReal_lt_top, eLpNorm_le_mul_eLpNorm_of_ae_le_mul, finiteness, mul_lt_top, ofReal_lt_top, trans_lt
-/
theorem MemLp.of_le_mul {f : α -> E} {g : α -> F} {c : Real} (hg : MemLp g p μ)
    (hf : AEStronglyMeasurable f μ) (hfg : forallᵐ x ∂μ, ‖f x‖ <= c * ‖g x‖) : MemLp f p μ :=
  ⟨hf,
(eLpNorm_le_mul_eLpNorm_of_ae_le_mul hfg p).trans_lt
      ENNReal.mul_lt_top ENNReal.ofReal_lt_top (by finiteness)⟩

-- TODO: eventually, deprecate and remove the nnnorm version
/--
theorem `MemLp.of_le_mul'` / 定理 `MemLp.of_le_mul'`

English:
theorem MemLp.of_le_mul'
  statement: {f : α -> ε} {g : α -> ε'} {c : Real>=0} (hg : MemLp g p μ)
  proof: ⟨hf, (eLpNorm_le_mul_eLpNorm_of_ae_le_mul' hfg p).trans_lt
      ENNReal.mul_lt_top ENNReal.coe_lt_top (by finiteness)⟩

中文:
定理 MemLp.of_le_mul'
  结论: {f : α -> ε} {g : α -> ε'} {c : 实数>=0} (hg : MemLp g p μ)
  证明: ⟨hf, (eLpNorm_le_mul_eLpNorm_of_ae_le_mul' hfg p).trans_lt
      ENNReal.mul_lt_top ENNReal.coe_lt_top (by finiteness)⟩

Depends on / 依赖: ENNReal, ENNReal.coe_lt_top, ENNReal.mul_lt_top, coe_lt_top, eLpNorm_le_mul_eLpNorm_of_ae_le_mul, finiteness, mul_lt_top, trans_lt
-/
theorem MemLp.of_le_mul' {f : α -> ε} {g : α -> ε'} {c : Real>=0} (hg : MemLp g p μ)
    (hf : AEStronglyMeasurable f μ) (hfg : forallᵐ x ∂μ, ‖f x‖ₑ <= c * ‖g x‖ₑ) : MemLp f p μ :=
⟨hf, (eLpNorm_le_mul_eLpNorm_of_ae_le_mul' hfg p).trans_lt
      ENNReal.mul_lt_top ENNReal.coe_lt_top (by finiteness)⟩

end Monotonicity

/--
theorem `le_eLpNorm_of_bddBelow` / 定理 `le_eLpNorm_of_bddBelow`

English:
theorem le_eLpNorm_of_bddBelow
  statement: (hp : p != 0) (hp' : p != ∞) {f : α -> F} (C : Real>=0) {s : Set α}
  proof: by
  rw [ENNReal.smul_def]; rw [smul_eq_mul]; rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp hp']; rw [one_div]; rw [ENNReal.le_rpow_inv_iff (ENNReal.toReal_pos hp hp')]; rw [ENNReal.mul_rpow_of_nonneg _ _ ENNReal.toReal_nonneg]; rw [← ENNReal.rpow_mul]; rw [inv_mul_cancel₀ (ENNReal.toReal_pos hp hp').ne']; rw [ENNReal.rpow_one]; rw [← setLIntegral_const]; rw [← lintegral_indicator hs]
  refine lintegral_mono_ae ?_
  filter_upwards [hf] with x hx
  by_cases hxs : x in s
  · simp only [Set.indicator_of_mem, hxs, true_implies] at hx ⊢
    gcongr
    rwa [coe_le_enorm]
  · simp [Set.indicator_of_notMem hxs]

中文:
定理 le_eLpNorm_of_bddBelow
  结论: (hp : p != 0) (hp' : p != ∞) {f : α -> F} (C : 实数>=0) {s : 集合 α}
  证明: by
  rw [ENNReal.smul_def]; rw [smul_eq_mul]; rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp hp']; rw [one_div]; rw [ENNReal.le_rpow_inv_iff (ENNReal.toReal_pos hp hp')]; rw [ENNReal.mul_rpow_of_nonneg _ _ ENNReal.toReal_nonneg]; rw [← ENNReal.rpow_mul]; rw [inv_mul_cancel₀ (ENNReal.toReal_pos hp hp').ne']; rw [ENNReal.rpow_one]; rw [← setLIntegral_const]; rw [← lintegral_indicator hs]
  refine lintegral_mono_ae ?_
  filter_upwards [hf] with x hx
  by_cases hxs : x in s
  · simp only [Set.indicator_of_mem, hxs, true_implies] at hx ⊢
    gcongr
    rwa [coe_le_enorm]
  · simp [Set.indicator_of_notMem hxs]

Depends on / 依赖: ENNReal, ENNReal.le_rpow_inv_iff, ENNReal.mul_rpow_of_nonneg, ENNReal.rpow_mul, ENNReal.rpow_one, ENNReal.smul_def, ENNReal.toReal_nonneg, ENNReal.toReal_pos, Set.indicator_of_mem, eLpNorm_eq_lintegral_rpow_enorm_toReal, filter_upwards, indicator_of_mem, le_rpow_inv_iff, lintegral_indicator, lintegral_mono_ae, mul_rpow_of_nonneg, one_div, rpow_mul, rpow_one, setLIntegral_const
-/
theorem le_eLpNorm_of_bddBelow (hp : p != 0) (hp' : p != ∞) {f : α -> F} (C : Real>=0) {s : Set α}
    (hs : MeasurableSet s) (hf : forallᵐ x ∂μ, x in s -> C <= ‖f x‖₊) :
    C • μ s ^ (1 / p.toReal) <= eLpNorm f p μ := by
  rw [ENNReal.smul_def]; rw [smul_eq_mul]; rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp hp']; rw [one_div]; rw [ENNReal.le_rpow_inv_iff (ENNReal.toReal_pos hp hp')]; rw [ENNReal.mul_rpow_of_nonneg _ _ ENNReal.toReal_nonneg]; rw [← ENNReal.rpow_mul]; rw [inv_mul_cancel₀ (ENNReal.toReal_pos hp hp').ne']; rw [ENNReal.rpow_one]; rw [← setLIntegral_const]; rw [← lintegral_indicator hs]
  refine lintegral_mono_ae ?_
  filter_upwards [hf] with x hx
  by_cases hxs : x in s
  · simp only [Set.indicator_of_mem, hxs, true_implies] at hx ⊢
    gcongr
    rwa [coe_le_enorm]
  · simp [Set.indicator_of_notMem hxs]

section Star

variable {R : Type*} [NormedAddCommGroup R] [StarAddMonoid R] [NormedStarGroup R]

@[simp]
/--
theorem `eLpNorm_star` / 定理 `eLpNorm_star`

English:
theorem eLpNorm_star
  given: {p : Real>=0∞} {f : α -> R}
  statement: eLpNorm (star f) p μ = eLpNorm f p μ
  proof: eLpNorm_congr_norm_ae .of_forall by simp

@[simp]

中文:
定理 eLpNorm_star
  条件: {p : 实数>=0∞} {f : α -> R}
  结论: eLpNorm (star f) p μ = eLpNorm f p μ
  证明: eLpNorm_congr_norm_ae .of_forall by simp

@[simp]

Depends on / 依赖: eLpNorm_congr_norm_ae, of_forall
-/
theorem eLpNorm_star {p : Real>=0∞} {f : α -> R} : eLpNorm (star f) p μ = eLpNorm f p μ :=
eLpNorm_congr_norm_ae .of_forall by simp

@[simp]
/--
theorem `AEEqFun.eLpNorm_star` / 定理 `AEEqFun.eLpNorm_star`

English:
theorem AEEqFun.eLpNorm_star
  given: {p : Real>=0∞} {f : α ->ₘ[μ] R}
  statement: eLpNorm (star f : α ->ₘ[μ] R) p μ =
  proof: eLpNorm_congr_ae (coeFn_star f)

中文:
定理 AEEqFun.eLpNorm_star
  条件: {p : 实数>=0∞} {f : α ->ₘ[μ] R}
  结论: eLpNorm (star f : α ->ₘ[μ] R) p μ =
  证明: eLpNorm_congr_ae (coeFn_star f)

Depends on / 依赖: coeFn_star, eLpNorm_congr_ae
-/
theorem AEEqFun.eLpNorm_star {p : Real>=0∞} {f : α ->ₘ[μ] R} : eLpNorm (star f : α ->ₘ[μ] R) p μ =
.trans by simp eLpNorm f p μ := eLpNorm_congr_ae (coeFn_star f)

/--
theorem `MemLp.star` / 定理 `MemLp.star`

English:
theorem MemLp.star
  given: {p : Real>=0∞} {f : α -> R} (hf : MemLp f p μ)
  statement: MemLp (star f) p μ
  proof: ⟨hf.1.star, by simpa using hf.2⟩

中文:
定理 MemLp.star
  条件: {p : 实数>=0∞} {f : α -> R} (hf : MemLp f p μ)
  结论: MemLp (star f) p μ
  证明: ⟨hf.1.star, by simpa using hf.2⟩
-/
protected theorem MemLp.star {p : Real>=0∞} {f : α -> R} (hf : MemLp f p μ) : MemLp (star f) p μ :=
  ⟨hf.1.star, by simpa using hf.2⟩

end Star

section RCLike

variable {𝕜 : Type*} [RCLike 𝕜] {f : α -> 𝕜}

/--
lemma `eLpNorm_conj` / 引理 `eLpNorm_conj`

English:
lemma eLpNorm_conj
  given: (f : α -> 𝕜) (p : Real>=0∞) (μ : Measure α)
  proof: by simp [← eLpNorm_norm]

中文:
引理 eLpNorm_conj
  条件: (f : α -> 𝕜) (p : 实数>=0∞) (μ : 测度 α)
  证明: by simp [← eLpNorm_norm]
-/
@[simp] lemma eLpNorm_conj (f : α -> 𝕜) (p : Real>=0∞) (μ : Measure α) :
    eLpNorm (conj f) p μ = eLpNorm f p μ := by simp [← eLpNorm_norm]

/--
theorem `MemLp.re` / 定理 `MemLp.re`

English:
theorem MemLp.re
  given: (hf : MemLp f p μ)
  statement: MemLp (fun x => RCLike.re (f x)) p μ
  proof: by
  have : forall x, ‖RCLike.re (f x)‖ <= 1 * ‖f x‖ := by
    intro x
    rw [one_mul]
    exact RCLike.norm_re_le_norm (f x)
  refine hf.of_le_mul ?_ (Eventually.of_forall this)
  exact RCLike.continuous_re.comp_aestronglyMeasurable hf.1

中文:
定理 MemLp.re
  条件: (hf : MemLp f p μ)
  结论: MemLp (fun x => RCLike.re (f x)) p μ
  证明: by
  have : forall x, ‖RCLike.re (f x)‖ <= 1 * ‖f x‖ := by
    intro x
    rw [one_mul]
    exact RCLike.norm_re_le_norm (f x)
  refine hf.of_le_mul ?_ (Eventually.of_forall this)
  exact RCLike.continuous_re.comp_aestronglyMeasurable hf.1

Depends on / 依赖: Eventually, Eventually.of_forall, RCLike, RCLike.continuous_re.comp_aestronglyMeasurable, RCLike.norm_re_le_norm, RCLike.re, comp_aestronglyMeasurable, continuous_re, hf.of_le_mul, norm_re_le_norm, of_forall, of_le_mul, one_mul
-/
theorem MemLp.re (hf : MemLp f p μ) : MemLp (fun x => RCLike.re (f x)) p μ := by
  have : forall x, ‖RCLike.re (f x)‖ <= 1 * ‖f x‖ := by
    intro x
    rw [one_mul]
    exact RCLike.norm_re_le_norm (f x)
  refine hf.of_le_mul ?_ (Eventually.of_forall this)
  exact RCLike.continuous_re.comp_aestronglyMeasurable hf.1

/--
theorem `MemLp.im` / 定理 `MemLp.im`

English:
theorem MemLp.im
  given: (hf : MemLp f p μ)
  statement: MemLp (fun x => RCLike.im (f x)) p μ
  proof: by
  have : forall x, ‖RCLike.im (f x)‖ <= 1 * ‖f x‖ := by
    intro x
    rw [one_mul]
    exact RCLike.norm_im_le_norm (f x)
  refine hf.of_le_mul ?_ (Eventually.of_forall this)
  exact RCLike.continuous_im.comp_aestronglyMeasurable hf.1

中文:
定理 MemLp.im
  条件: (hf : MemLp f p μ)
  结论: MemLp (fun x => RCLike.im (f x)) p μ
  证明: by
  have : forall x, ‖RCLike.im (f x)‖ <= 1 * ‖f x‖ := by
    intro x
    rw [one_mul]
    exact RCLike.norm_im_le_norm (f x)
  refine hf.of_le_mul ?_ (Eventually.of_forall this)
  exact RCLike.continuous_im.comp_aestronglyMeasurable hf.1

Depends on / 依赖: Eventually, Eventually.of_forall, RCLike, RCLike.continuous_im.comp_aestronglyMeasurable, RCLike.im, RCLike.norm_im_le_norm, comp_aestronglyMeasurable, continuous_im, hf.of_le_mul, norm_im_le_norm, of_forall, of_le_mul, one_mul
-/
theorem MemLp.im (hf : MemLp f p μ) : MemLp (fun x => RCLike.im (f x)) p μ := by
  have : forall x, ‖RCLike.im (f x)‖ <= 1 * ‖f x‖ := by
    intro x
    rw [one_mul]
    exact RCLike.norm_im_le_norm (f x)
  refine hf.of_le_mul ?_ (Eventually.of_forall this)
  exact RCLike.continuous_im.comp_aestronglyMeasurable hf.1

end RCLike

end MeasureTheory
