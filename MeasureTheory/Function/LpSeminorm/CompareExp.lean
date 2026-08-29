/-
Copyright (c) 2020 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Eric Wieser
-/
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
public import Mathlib.MeasureTheory.Function.LpSeminorm.SMul
public import Mathlib.MeasureTheory.Integral.MeanInequalities

/-!
# Compare Lp seminorms for different values of `p`

In this file we compare `MeasureTheory.eLpNorm'` and `MeasureTheory.eLpNorm` for different
exponents.
-/

public section

open Filter ENNReal
open scoped Topology

namespace MeasureTheory

section SameSpace

variable {α ε ε' : Type*} {m : MeasurableSpace α} {μ : Measure α} {f : α -> ε}
  [TopologicalSpace ε] [ContinuousENorm ε]
  [TopologicalSpace ε'] [ESeminormedAddMonoid ε']

/--
theorem `eLpNorm'_le_eLpNorm'_mul_rpow_measure_univ` / 定理 `eLpNorm'_le_eLpNorm'_mul_rpow_measure_univ`

English:
theorem eLpNorm'_le_eLpNorm'_mul_rpow_measure_univ
  statement: {p q : Real} (hp0_lt : 0 < p) (hpq : p <= q)
  proof: by
  have hq0_lt : 0 < q := lt_of_lt_of_le hp0_lt hpq
  by_cases hpq_eq : p = q
  · rw [hpq_eq, sub_self, ENNReal.rpow_zero, mul_one]
  have hpq : p < q := lt_of_le_of_ne hpq hpq_eq
  let g := fun _ : α => (1 : Real>=0∞)
  have h_rw : (∫⁻ a, ‖f a‖ₑ ^ p ∂μ) = ∫⁻ a, (‖f a‖ₑ * g a) ^ p ∂μ :=
    linteg

中文:
定理 eLpNorm'_le_eLpNorm'_mul_rpow_measure_univ
  结论: {p q : 实数} (hp0_lt : 0 < p) (hpq : p <= q)
  证明: by
  have hq0_lt : 0 < q := lt_of_lt_of_le hp0_lt hpq
  by_cases hpq_eq : p = q
  · rw [hpq_eq, sub_self, ENNReal.rpow_zero, mul_one]
  have hpq : p < q := lt_of_le_of_ne hpq hpq_eq
  let g := fun _ : α => (1 : Real>=0∞)
  have h_rw : (∫⁻ a, ‖f a‖ₑ ^ p ∂μ) = ∫⁻ a, (‖f a‖ₑ * g a) ^ p ∂μ :=
    linteg
-/
theorem eLpNorm'_le_eLpNorm'_mul_rpow_measure_univ {p q : Real} (hp0_lt : 0 < p) (hpq : p <= q)
    (hf : AEStronglyMeasurable f μ) :
    eLpNorm' f p μ <= eLpNorm' f q μ * μ Set.univ ^ (1 / p - 1 / q) := by
  have hq0_lt : 0 < q := lt_of_lt_of_le hp0_lt hpq
  by_cases hpq_eq : p = q
  · rw [hpq_eq, sub_self, ENNReal.rpow_zero, mul_one]
  have hpq : p < q := lt_of_le_of_ne hpq hpq_eq
  let g := fun _ : α => (1 : Real>=0∞)
  have h_rw : (∫⁻ a, ‖f a‖ₑ ^ p ∂μ) = ∫⁻ a, (‖f a‖ₑ * g a) ^ p ∂μ :=
    lintegral_congr fun a => by simp [g]
  repeat' rw [eLpNorm'_eq_lintegral_enorm]
  rw [h_rw]
  let r := p * q / (q - p)
  have hpqr : 1 / p = 1 / q + 1 / r := by simp [field]
  calc
    (∫⁻ a : α, (‖f a‖ₑ * g a) ^ p ∂μ) ^ (1 / p) <=
        (∫⁻ a : α, ‖f a‖ₑ ^ q ∂μ) ^ (1 / q) * (∫⁻ a : α, g a ^ r ∂μ) ^ (1 / r) :=
      ENNReal.lintegral_Lp_mul_le_Lq_mul_Lr hp0_lt hpq hpqr μ hf.enorm aemeasurable_const
    _ = (∫⁻ a : α, ‖f a‖ₑ ^ q ∂μ) ^ (1 / q) * μ Set.univ ^ (1 / p - 1 / q) := by
      rw [hpqr]; simp [r, g]

/--
theorem `eLpNorm'_le_eLpNormEssSup_mul_rpow_measure_univ` / 定理 `eLpNorm'_le_eLpNormEssSup_mul_rpow_measure_univ`

English:
theorem eLpNorm'_le_eLpNormEssSup_mul_rpow_measure_univ
  given: {q : Real} (hq_pos : 0 < q)
  proof: by
  have h_le : (∫⁻ a : α, ‖f a‖ₑ ^ q ∂μ) <= ∫⁻ _ : α, eLpNormEssSup f μ ^ q ∂μ := by
    refine lintegral_mono_ae ?_
    have h_nnnorm_le_eLpNorm_ess_sup := enorm_ae_le_eLpNormEssSup f μ
    exact h_nnnorm_le_eLpNorm_ess_sup.mono fun x hx => by gcongr
  rw [eLpNorm']; rw [← ENNReal.rpow_one (eLpNo

中文:
定理 eLpNorm'_le_eLpNormEssSup_mul_rpow_measure_univ
  条件: {q : 实数} (hq_pos : 0 < q)
  证明: by
  have h_le : (∫⁻ a : α, ‖f a‖ₑ ^ q ∂μ) <= ∫⁻ _ : α, eLpNormEssSup f μ ^ q ∂μ := by
    refine lintegral_mono_ae ?_
    have h_nnnorm_le_eLpNorm_ess_sup := enorm_ae_le_eLpNormEssSup f μ
    exact h_nnnorm_le_eLpNorm_ess_sup.mono fun x hx => by gcongr
  rw [eLpNorm']; rw [← ENNReal.rpow_one (eLpNo
-/
theorem eLpNorm'_le_eLpNormEssSup_mul_rpow_measure_univ {q : Real} (hq_pos : 0 < q) :
    eLpNorm' f q μ <= eLpNormEssSup f μ * μ Set.univ ^ (1 / q) := by
  have h_le : (∫⁻ a : α, ‖f a‖ₑ ^ q ∂μ) <= ∫⁻ _ : α, eLpNormEssSup f μ ^ q ∂μ := by
    refine lintegral_mono_ae ?_
    have h_nnnorm_le_eLpNorm_ess_sup := enorm_ae_le_eLpNormEssSup f μ
    exact h_nnnorm_le_eLpNorm_ess_sup.mono fun x hx => by gcongr
  rw [eLpNorm']; rw [← ENNReal.rpow_one (eLpNormEssSup f μ)]
  nth_rw 2 [← mul_inv_cancel₀ (ne_of_lt hq_pos).symm]
  rw [ENNReal.rpow_mul]; rw [one_div]; rw [← ENNReal.mul_rpow_of_nonneg _ _ (by simp [hq_pos.le] : 0 <= q⁻¹)]
  gcongr
  rwa [lintegral_const] at h_le

/--
theorem `eLpNorm_le_eLpNorm_mul_rpow_measure_univ` / 定理 `eLpNorm_le_eLpNorm_mul_rpow_measure_univ`

English:
theorem eLpNorm_le_eLpNorm_mul_rpow_measure_univ
  statement: {p q : Real>=0∞} (hpq : p <= q)
  proof: by
  obtain rfl | hp0 := eq_or_ne p 0
  · simp
  have hq0_lt : 0 < q := hp0.pos.trans_le hpq
  obtain rfl | hq_top := eq_or_ne q ∞
  · simp only [_root_.div_zero, one_div, ENNReal.toReal_top, sub_zero]
    obtain rfl | hp_top := eq_or_ne p ∞
    · simp
    rw [eLpNorm_eq_eLpNorm' hp0 hp_top]
    hav

中文:
定理 eLpNorm_le_eLpNorm_mul_rpow_measure_univ
  结论: {p q : 实数>=0∞} (hpq : p <= q)
  证明: by
  obtain rfl | hp0 := eq_or_ne p 0
  · simp
  have hq0_lt : 0 < q := hp0.pos.trans_le hpq
  obtain rfl | hq_top := eq_or_ne q ∞
  · simp only [_root_.div_zero, one_div, ENNReal.toReal_top, sub_zero]
    obtain rfl | hp_top := eq_or_ne p ∞
    · simp
    rw [eLpNorm_eq_eLpNorm' hp0 hp_top]
    hav

Depends on / 依赖: ENNReal, ENNReal.toReal_pos, ENNReal.toReal_top, _le_eLpNormEssSup_mul_rpow_measure_univ, _root_, _root_.div_zero, div_zero, eLpNorm, eLpNorm_eq_eLpNorm, eq_or_ne, hp0.pos.trans_le, hp_lt_top, hp_pos, hp_top, hpq.trans_lt, hq0_lt, hq_top, le_of_eq, lt_top_iff_ne_top, lt_top_iff_ne_top.mpr
-/
theorem eLpNorm_le_eLpNorm_mul_rpow_measure_univ {p q : Real>=0∞} (hpq : p <= q)
    (hf : AEStronglyMeasurable f μ) :
    eLpNorm f p μ <= eLpNorm f q μ * μ Set.univ ^ (1 / p.toReal - 1 / q.toReal) := by
  obtain rfl | hp0 := eq_or_ne p 0
  · simp
  have hq0_lt : 0 < q := hp0.pos.trans_le hpq
  obtain rfl | hq_top := eq_or_ne q ∞
  · simp only [_root_.div_zero, one_div, ENNReal.toReal_top, sub_zero]
    obtain rfl | hp_top := eq_or_ne p ∞
    · simp
    rw [eLpNorm_eq_eLpNorm' hp0 hp_top]
    have hp_pos : 0 < p.toReal := ENNReal.toReal_pos hp0 hp_top
    refine (eLpNorm'_le_eLpNormEssSup_mul_rpow_measure_univ hp_pos).trans (le_of_eq ?_)
    congr
    exact one_div _
  have hp_lt_top : p < ∞ := hpq.trans_lt (lt_top_iff_ne_top.mpr hq_top)
  have hp_pos : 0 < p.toReal := ENNReal.toReal_pos hp0 hp_lt_top.ne
  rw [eLpNorm_eq_eLpNorm' hp0 hp_lt_top.ne]; rw [eLpNorm_eq_eLpNorm' hq0_lt.ne.symm hq_top]
  have hpq_real : p.toReal <= q.toReal := ENNReal.toReal_mono hq_top hpq
  exact eLpNorm'_le_eLpNorm'_mul_rpow_measure_univ hp_pos hpq_real hf

/--
theorem `eLpNorm'_le_eLpNorm'_of_exponent_le` / 定理 `eLpNorm'_le_eLpNorm'_of_exponent_le`

English:
theorem eLpNorm'_le_eLpNorm'_of_exponent_le
  statement: {p q : Real} (hp0_lt : 0 < p)
  proof: by
  have h_le_μ := eLpNorm'_le_eLpNorm'_mul_rpow_measure_univ hp0_lt hpq hf
  rwa [measure_univ, ENNReal.one_rpow, mul_one] at h_le_μ

中文:
定理 eLpNorm'_le_eLpNorm'_of_exponent_le
  结论: {p q : 实数} (hp0_lt : 0 < p)
  证明: by
  have h_le_μ := eLpNorm'_le_eLpNorm'_mul_rpow_measure_univ hp0_lt hpq hf
  rwa [measure_univ, ENNReal.one_rpow, mul_one] at h_le_μ
-/
theorem eLpNorm'_le_eLpNorm'_of_exponent_le {p q : Real} (hp0_lt : 0 < p)
    (hpq : p <= q) (μ : Measure α) [IsProbabilityMeasure μ] (hf : AEStronglyMeasurable f μ) :
    eLpNorm' f p μ <= eLpNorm' f q μ := by
  have h_le_μ := eLpNorm'_le_eLpNorm'_mul_rpow_measure_univ hp0_lt hpq hf
  rwa [measure_univ, ENNReal.one_rpow, mul_one] at h_le_μ

/--
theorem `eLpNorm'_le_eLpNormEssSup` / 定理 `eLpNorm'_le_eLpNormEssSup`

English:
theorem eLpNorm'_le_eLpNormEssSup
  given: {q : Real} (hq_pos : 0 < q) [IsProbabilityMeasure μ]
  proof: (eLpNorm'_le_eLpNormEssSup_mul_rpow_measure_univ hq_pos).trans_eq (by simp [measure_univ])

中文:
定理 eLpNorm'_le_eLpNormEssSup
  条件: {q : 实数} (hq_pos : 0 < q) [IsProbabilityMeasure μ]
  证明: (eLpNorm'_le_eLpNormEssSup_mul_rpow_measure_univ hq_pos).trans_eq (by simp [measure_univ])
-/
theorem eLpNorm'_le_eLpNormEssSup {q : Real} (hq_pos : 0 < q) [IsProbabilityMeasure μ] :
    eLpNorm' f q μ <= eLpNormEssSup f μ :=
  (eLpNorm'_le_eLpNormEssSup_mul_rpow_measure_univ hq_pos).trans_eq (by simp [measure_univ])

/--
theorem `eLpNorm_le_eLpNorm_of_exponent_le` / 定理 `eLpNorm_le_eLpNorm_of_exponent_le`

English:
theorem eLpNorm_le_eLpNorm_of_exponent_le
  statement: {p q : Real>=0∞} (hpq : p <= q) [IsProbabilityMeasure μ]
  proof: (eLpNorm_le_eLpNorm_mul_rpow_measure_univ hpq hf).trans (le_of_eq (by simp [measure_univ]))

中文:
定理 eLpNorm_le_eLpNorm_of_exponent_le
  结论: {p q : 实数>=0∞} (hpq : p <= q) [IsProbabilityMeasure μ]
  证明: (eLpNorm_le_eLpNorm_mul_rpow_measure_univ hpq hf).trans (le_of_eq (by simp [measure_univ]))

Depends on / 依赖: eLpNorm_le_eLpNorm_mul_rpow_measure_univ, le_of_eq, measure_univ
-/
theorem eLpNorm_le_eLpNorm_of_exponent_le {p q : Real>=0∞} (hpq : p <= q) [IsProbabilityMeasure μ]
    (hf : AEStronglyMeasurable f μ) : eLpNorm f p μ <= eLpNorm f q μ :=
  (eLpNorm_le_eLpNorm_mul_rpow_measure_univ hpq hf).trans (le_of_eq (by simp [measure_univ]))

/--
theorem `eLpNorm'_lt_top_of_eLpNorm'_lt_top_of_exponent_le` / 定理 `eLpNorm'_lt_top_of_eLpNorm'_lt_top_of_exponent_le`

English:
theorem eLpNorm'_lt_top_of_eLpNorm'_lt_top_of_exponent_le
  statement: {p q : Real} [IsFiniteMeasure μ]
  proof: by
  rcases le_or_gt p 0 with hp_nonpos | hp_pos
  · rw [le_antisymm hp_nonpos hp_nonneg]
    simp
  have hq_pos : 0 < q := lt_of_lt_of_le hp_pos hpq
  calc
    eLpNorm' f p μ <= eLpNorm' f q μ * μ Set.univ ^ (1 / p - 1 / q) :=
      eLpNorm'_le_eLpNorm'_mul_rpow_measure_univ hp_pos hpq hf
    _ < ∞

中文:
定理 eLpNorm'_lt_top_of_eLpNorm'_lt_top_of_exponent_le
  结论: {p q : 实数} [IsFiniteMeasure μ]
  证明: by
  rcases le_or_gt p 0 with hp_nonpos | hp_pos
  · rw [le_antisymm hp_nonpos hp_nonneg]
    simp
  have hq_pos : 0 < q := lt_of_lt_of_le hp_pos hpq
  calc
    eLpNorm' f p μ <= eLpNorm' f q μ * μ Set.univ ^ (1 / p - 1 / q) :=
      eLpNorm'_le_eLpNorm'_mul_rpow_measure_univ hp_pos hpq hf
    _ < ∞
-/
theorem eLpNorm'_lt_top_of_eLpNorm'_lt_top_of_exponent_le {p q : Real} [IsFiniteMeasure μ]
    (hf : AEStronglyMeasurable f μ) (hfq_lt_top : eLpNorm' f q μ < ∞) (hp_nonneg : 0 <= p)
    (hpq : p <= q) : eLpNorm' f p μ < ∞ := by
  rcases le_or_gt p 0 with hp_nonpos | hp_pos
  · rw [le_antisymm hp_nonpos hp_nonneg]
    simp
  have hq_pos : 0 < q := lt_of_lt_of_le hp_pos hpq
  calc
    eLpNorm' f p μ <= eLpNorm' f q μ * μ Set.univ ^ (1 / p - 1 / q) :=
      eLpNorm'_le_eLpNorm'_mul_rpow_measure_univ hp_pos hpq hf
    _ < ∞ := by
      rw [ENNReal.mul_lt_top_iff]
      refine Or.inl ⟨hfq_lt_top, ENNReal.rpow_lt_top_of_nonneg ?_ (by finiteness)⟩
      rwa [le_sub_comm, sub_zero, one_div, one_div, inv_le_inv₀ hq_pos hp_pos]

/--
theorem `MemLp.mono_exponent` / 定理 `MemLp.mono_exponent`

English:
theorem MemLp.mono_exponent
  statement: {p q : Real>=0∞} [IsFiniteMeasure μ] (hfq : MemLp f q μ)
  proof: by
  obtain ⟨hfq_m, hfq_lt_top⟩ := hfq
  by_cases hp0 : p = 0
  · rwa [hp0, memLp_zero_iff_aestronglyMeasurable]
  rw [← Ne] at hp0
  refine ⟨hfq_m, ?_⟩
  by_cases hp_top : p = ∞
  · have hq_top : q = ∞ := by rwa [hp_top, top_le_iff] at hpq
    rw [hp_top]
    rwa [hq_top] at hfq_lt_top
  have hp_po

中文:
定理 MemLp.mono_exponent
  结论: {p q : 实数>=0∞} [IsFiniteMeasure μ] (hfq : MemLp f q μ)
  证明: by
  obtain ⟨hfq_m, hfq_lt_top⟩ := hfq
  by_cases hp0 : p = 0
  · rwa [hp0, memLp_zero_iff_aestronglyMeasurable]
  rw [← Ne] at hp0
  refine ⟨hfq_m, ?_⟩
  by_cases hp_top : p = ∞
  · have hq_top : q = ∞ := by rwa [hp_top, top_le_iff] at hpq
    rw [hp_top]
    rwa [hq_top] at hfq_lt_top
  have hp_po

Depends on / 依赖: ENNReal, ENNReal.toReal_pos, _le_eLpNormEssSup_mul_rpow_m, eLpNorm, eLpNorm_eq_eLpNorm, eLpNorm_exponent_top, hfq_lt_top, hfq_m, hp_pos, hp_top, hq_top, lt_of_le_of_lt, memLp_zero_iff_aestronglyMeasurable, p.toReal, toReal, toReal_pos, top_le_iff
-/
theorem MemLp.mono_exponent {p q : Real>=0∞} [IsFiniteMeasure μ] (hfq : MemLp f q μ)
    (hpq : p <= q) : MemLp f p μ := by
  obtain ⟨hfq_m, hfq_lt_top⟩ := hfq
  by_cases hp0 : p = 0
  · rwa [hp0, memLp_zero_iff_aestronglyMeasurable]
  rw [← Ne] at hp0
  refine ⟨hfq_m, ?_⟩
  by_cases hp_top : p = ∞
  · have hq_top : q = ∞ := by rwa [hp_top, top_le_iff] at hpq
    rw [hp_top]
    rwa [hq_top] at hfq_lt_top
  have hp_pos : 0 < p.toReal := ENNReal.toReal_pos hp0 hp_top
  by_cases hq_top : q = ∞
  · rw [eLpNorm_eq_eLpNorm' hp0 hp_top]
    rw [hq_top]; rw [eLpNorm_exponent_top] at hfq_lt_top
    refine lt_of_le_of_lt (eLpNorm'_le_eLpNormEssSup_mul_rpow_measure_univ hp_pos) ?_
    refine ENNReal.mul_lt_top hfq_lt_top ?_
    exact ENNReal.rpow_lt_top_of_nonneg (by simp [hp_pos.le]) (by finiteness)
  have hq0 : q != 0 := by
    by_contra hq_eq_zero
    obtain rfl : p = 0 := le_antisymm (by rwa [hq_eq_zero] at hpq) zero_le
    rw [ENNReal.toReal_zero] at hp_pos
    exact (lt_irrefl _) hp_pos
  have hpq_real : p.toReal <= q.toReal := ENNReal.toReal_mono hq_top hpq
  rw [eLpNorm_eq_eLpNorm' hp0 hp_top]
  rw [eLpNorm_eq_eLpNorm' hq0 hq_top] at hfq_lt_top
  exact eLpNorm'_lt_top_of_eLpNorm'_lt_top_of_exponent_le hfq_m hfq_lt_top hp_pos.le hpq_real

/--
lemma `MemLp.mono_exponent_of_measure_support_ne_top` / 引理 `MemLp.mono_exponent_of_measure_support_ne_top`

English:
lemma MemLp.mono_exponent_of_measure_support_ne_top
  statement: {p q : Real>=0∞} {f : α -> ε'} (hfq : MemLp f q μ)
  proof: by
  have : (toMeasurable μ s).indicator f = f := by
    apply Set.indicator_eq_self.2
    apply Function.support_subset_iff'.2 fun x hx => hf x ?_
    contrapose hx
    exact subset_toMeasurable μ s hx
  rw [← this]; rw [memLp_indicator_iff_restrict (measurableSet_toMeasurable μ s)] at hfq ⊢
  have

中文:
引理 MemLp.mono_exponent_of_measure_support_ne_top
  结论: {p q : 实数>=0∞} {f : α -> ε'} (hfq : MemLp f q μ)
  证明: by
  have : (toMeasurable μ s).indicator f = f := by
    apply Set.indicator_eq_self.2
    apply Function.support_subset_iff'.2 fun x hx => hf x ?_
    contrapose hx
    exact subset_toMeasurable μ s hx
  rw [← this]; rw [memLp_indicator_iff_restrict (measurableSet_toMeasurable μ s)] at hfq ⊢
  have

Depends on / 依赖: Function, Function.support_subset_iff, Set.indicator_eq_self, contrapose, hfq.mono_exponent, indicator, indicator_eq_self, lt_top_iff_ne_top, measurableSet_toMeasurable, memLp_indicator_iff_restrict, mono_exponent, subset_toMeasurable, support_subset_iff, toMeasurable
-/
lemma MemLp.mono_exponent_of_measure_support_ne_top {p q : Real>=0∞} {f : α -> ε'} (hfq : MemLp f q μ)
    {s : Set α} (hf : forall x, x ∉ s -> f x = 0) (hs : μ s != ∞) (hpq : p <= q) : MemLp f p μ := by
  have : (toMeasurable μ s).indicator f = f := by
    apply Set.indicator_eq_self.2
    apply Function.support_subset_iff'.2 fun x hx => hf x ?_
    contrapose hx
    exact subset_toMeasurable μ s hx
  rw [← this]; rw [memLp_indicator_iff_restrict (measurableSet_toMeasurable μ s)] at hfq ⊢
  have : Fact (μ (toMeasurable μ s) < ∞) := ⟨by simpa [lt_top_iff_ne_top] using hs⟩
  exact hfq.mono_exponent hpq

end SameSpace

section Bilinear

variable {α E F G : Type*} {m : MeasurableSpace α}
  [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedAddCommGroup G] {μ : Measure α}
  {f : α -> E} {g : α -> F}

open NNReal

/--
theorem `eLpNorm_le_eLpNorm_top_mul_eLpNorm` / 定理 `eLpNorm_le_eLpNorm_top_mul_eLpNorm`

English:
theorem eLpNorm_le_eLpNorm_top_mul_eLpNorm
  statement: (p : Real>=0∞) (f : α -> E) {g : α -> F}
  proof: by
  calc
    eLpNorm (fun x => b (f x) (g x)) p μ <= eLpNorm (fun x => (c : Real) • ‖f x‖ * ‖g x‖) p μ :=
      eLpNorm_mono_ae_real h
    _ <= c * eLpNorm f ∞ μ * eLpNorm g p μ := ?_
  simp only [smul_mul_assoc, ← Pi.smul_def, eLpNorm_const_smul]
  rw [Real.enorm_eq_ofReal c.coe_nonneg]; rw [ENNRe

中文:
定理 eLpNorm_le_eLpNorm_top_mul_eLpNorm
  结论: (p : 实数>=0∞) (f : α -> E) {g : α -> F}
  证明: by
  calc
    eLpNorm (fun x => b (f x) (g x)) p μ <= eLpNorm (fun x => (c : Real) • ‖f x‖ * ‖g x‖) p μ :=
      eLpNorm_mono_ae_real h
    _ <= c * eLpNorm f ∞ μ * eLpNorm g p μ := ?_
  simp only [smul_mul_assoc, ← Pi.smul_def, eLpNorm_const_smul]
  rw [Real.enorm_eq_ofReal c.coe_nonneg]; rw [ENNRe

Depends on / 依赖: ENNReal, ENNReal.ofReal_coe_nnreal, ENNReal.trichotomy, Pi.smul_def, Real.enorm_eq_ofReal, c.coe_nonneg, coe_nonneg, eLpNorm, eLpNormEssSup_eq_essSup_enorm, eLpNorm_const_smul, eLpNorm_exponent_top, eLpNorm_mono_ae_real, eLpNorm_norm, enorm_eq_ofReal, enorm_mul, mul_assoc, ofReal_coe_nnreal, simp_rw, smul_def, smul_mul_assoc
-/
theorem eLpNorm_le_eLpNorm_top_mul_eLpNorm (p : Real>=0∞) (f : α -> E) {g : α -> F}
    (hg : AEStronglyMeasurable g μ) (b : E -> F -> G) (c : Real>=0)
    (h : forallᵐ x ∂μ, ‖b (f x) (g x)‖₊ <= c * ‖f x‖₊ * ‖g x‖₊) :
    eLpNorm (fun x => b (f x) (g x)) p μ <= c * eLpNorm f ∞ μ * eLpNorm g p μ := by
  calc
    eLpNorm (fun x => b (f x) (g x)) p μ <= eLpNorm (fun x => (c : Real) • ‖f x‖ * ‖g x‖) p μ :=
      eLpNorm_mono_ae_real h
    _ <= c * eLpNorm f ∞ μ * eLpNorm g p μ := ?_
  simp only [smul_mul_assoc, ← Pi.smul_def, eLpNorm_const_smul]
  rw [Real.enorm_eq_ofReal c.coe_nonneg]; rw [ENNReal.ofReal_coe_nnreal]; rw [mul_assoc]
  gcongr
  obtain (rfl | rfl | hp) := ENNReal.trichotomy p
  · simp
  · rw [← eLpNorm_norm f, ← eLpNorm_norm g]
    simp_rw [eLpNorm_exponent_top, eLpNormEssSup_eq_essSup_enorm, enorm_mul, enorm_norm]
    exact ENNReal.essSup_mul_le (‖f ·‖ₑ) (‖g ·‖ₑ)
  obtain ⟨hp₁, hp₂⟩ := ENNReal.toReal_pos_iff.mp hp
  simp_rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp₁.ne' hp₂.ne, eLpNorm_exponent_top,
    eLpNormEssSup, one_div, ENNReal.rpow_inv_le_iff hp, enorm_mul, enorm_norm]
  rw [ENNReal.mul_rpow_of_nonneg (hz := hp.le)]; rw [ENNReal.rpow_inv_rpow hp.ne']; rw [← lintegral_const_mul'' _ (by fun_prop)]
  simp only [← ENNReal.mul_rpow_of_nonneg (hz := hp.le)]
  apply lintegral_mono_ae
  filter_upwards [h, enorm_ae_le_eLpNormEssSup f μ] with x hb hf
  gcongr
  exact hf

/--
theorem `eLpNorm_le_eLpNorm_mul_eLpNorm_top` / 定理 `eLpNorm_le_eLpNorm_mul_eLpNorm_top`

English:
theorem eLpNorm_le_eLpNorm_mul_eLpNorm_top
  statement: (p : Real>=0∞) {f : α -> E} (hf : AEStronglyMeasurable f μ)
  proof: calc
    eLpNorm (fun x => b (f x) (g x)) p μ <= c * eLpNorm g ∞ μ * eLpNorm f p μ :=
eLpNorm_le_eLpNorm_top_mul_eLpNorm p g hf (flip b) c by
        convert! h using 3 with x
        simp only [mul_assoc, mul_comm ‖f x‖₊]
    _ = c * eLpNorm f p μ * eLpNorm g ∞ μ := by
      simp only [mul_assoc]; 

中文:
定理 eLpNorm_le_eLpNorm_mul_eLpNorm_top
  结论: (p : 实数>=0∞) {f : α -> E} (hf : AEStronglyMeasurable f μ)
  证明: calc
    eLpNorm (fun x => b (f x) (g x)) p μ <= c * eLpNorm g ∞ μ * eLpNorm f p μ :=
eLpNorm_le_eLpNorm_top_mul_eLpNorm p g hf (flip b) c by
        convert! h using 3 with x
        simp only [mul_assoc, mul_comm ‖f x‖₊]
    _ = c * eLpNorm f p μ * eLpNorm g ∞ μ := by
      simp only [mul_assoc]; 

Depends on / 依赖: convert, eLpNorm, eLpNorm_le_eLpNorm_top_mul_eLpNorm, mul_assoc, mul_comm
-/
theorem eLpNorm_le_eLpNorm_mul_eLpNorm_top (p : Real>=0∞) {f : α -> E} (hf : AEStronglyMeasurable f μ)
    (g : α -> F) (b : E -> F -> G) (c : Real>=0)
    (h : forallᵐ x ∂μ, ‖b (f x) (g x)‖₊ <= c * ‖f x‖₊ * ‖g x‖₊) :
    eLpNorm (fun x => b (f x) (g x)) p μ <= c * eLpNorm f p μ * eLpNorm g ∞ μ :=
  calc
    eLpNorm (fun x => b (f x) (g x)) p μ <= c * eLpNorm g ∞ μ * eLpNorm f p μ :=
eLpNorm_le_eLpNorm_top_mul_eLpNorm p g hf (flip b) c by
        convert! h using 3 with x
        simp only [mul_assoc, mul_comm ‖f x‖₊]
    _ = c * eLpNorm f p μ * eLpNorm g ∞ μ := by
      simp only [mul_assoc]; rw [mul_comm (eLpNorm _ _ _)]

/--
theorem `eLpNorm'_le_eLpNorm'_mul_eLpNorm'` / 定理 `eLpNorm'_le_eLpNorm'_mul_eLpNorm'`

English:
theorem eLpNorm'_le_eLpNorm'_mul_eLpNorm'
  statement: {p q r : Real} (hf : AEStronglyMeasurable f μ)
  proof: by
  calc
    eLpNorm' (fun x => b (f x) (g x)) r μ
      <= eLpNorm' (fun x => (c : Real) • ‖f x‖ * ‖g x‖) r μ := by
      simp only [eLpNorm']
      gcongr ?_ ^ _
refine lintegral_mono_ae h.mono fun a ha => ?_
      gcongr
      simp only [enorm_eq_nnnorm, ENNReal.coe_le_coe]
      simpa using! ha

中文:
定理 eLpNorm'_le_eLpNorm'_mul_eLpNorm'
  结论: {p q r : 实数} (hf : AEStronglyMeasurable f μ)
  证明: by
  calc
    eLpNorm' (fun x => b (f x) (g x)) r μ
      <= eLpNorm' (fun x => (c : Real) • ‖f x‖ * ‖g x‖) r μ := by
      simp only [eLpNorm']
      gcongr ?_ ^ _
refine lintegral_mono_ae h.mono fun a ha => ?_
      gcongr
      simp only [enorm_eq_nnnorm, ENNReal.coe_le_coe]
      simpa using! ha
-/
theorem eLpNorm'_le_eLpNorm'_mul_eLpNorm' {p q r : Real} (hf : AEStronglyMeasurable f μ)
    (hg : AEStronglyMeasurable g μ) (b : E -> F -> G) (c : Real>=0)
    (h : forallᵐ x ∂μ, ‖b (f x) (g x)‖₊ <= c * ‖f x‖₊ * ‖g x‖₊) (hro_lt : 0 < r) (hrp : r < p)
    (hpqr : 1 / r = 1 / p + 1 / q) :
    eLpNorm' (fun x => b (f x) (g x)) r μ <= c * eLpNorm' f p μ * eLpNorm' g q μ := by
  calc
    eLpNorm' (fun x => b (f x) (g x)) r μ
      <= eLpNorm' (fun x => (c : Real) • ‖f x‖ * ‖g x‖) r μ := by
      simp only [eLpNorm']
      gcongr ?_ ^ _
refine lintegral_mono_ae h.mono fun a ha => ?_
      gcongr
      simp only [enorm_eq_nnnorm, ENNReal.coe_le_coe]
      simpa using! ha
    _ <= c * eLpNorm' f p μ * eLpNorm' g q μ := by
      simp only [smul_mul_assoc, ← Pi.smul_def, eLpNorm'_const_smul _ hro_lt]
      rw [Real.enorm_eq_ofReal c.coe_nonneg]; rw [ENNReal.ofReal_coe_nnreal]; rw [mul_assoc]
      gcongr
      simpa only [eLpNorm', enorm_mul, enorm_norm] using!
        ENNReal.lintegral_Lp_mul_le_Lq_mul_Lr hro_lt hrp hpqr μ hf.enorm hg.enorm

/--
theorem `eLpNorm_le_eLpNorm_mul_eLpNorm_of_nnnorm` / 定理 `eLpNorm_le_eLpNorm_mul_eLpNorm_of_nnnorm`

English:
theorem eLpNorm_le_eLpNorm_mul_eLpNorm_of_nnnorm
  statement: {p q r : Real>=0∞}
  proof: by
  have hpqr := hpqr.one_div_eq
  obtain (rfl | rfl | hp) := ENNReal.trichotomy p
  · simp_all
  · have : r = q := by simpa using hpqr
    exact this ▸ eLpNorm_le_eLpNorm_top_mul_eLpNorm r f hg b c h
  obtain (rfl | rfl | hq) := ENNReal.trichotomy q
  · simp_all
  · have : r = p := by simpa using 

中文:
定理 eLpNorm_le_eLpNorm_mul_eLpNorm_of_nnnorm
  结论: {p q r : 实数>=0∞}
  证明: by
  have hpqr := hpqr.one_div_eq
  obtain (rfl | rfl | hp) := ENNReal.trichotomy p
  · simp_all
  · have : r = q := by simpa using hpqr
    exact this ▸ eLpNorm_le_eLpNorm_top_mul_eLpNorm r f hg b c h
  obtain (rfl | rfl | hq) := ENNReal.trichotomy q
  · simp_all
  · have : r = p := by simpa using 

Depends on / 依赖: ENNReal, ENNReal.toReal_pos_iff.mp, ENNReal.trichotomy, eLpNorm_le_eLpNorm_mul_eLpNorm_top, eLpNorm_le_eLpNorm_top_mul_eLpNorm, hpqr.one_div_eq, one_div_eq, p.toReal, q.toR, r.toReal, toReal, toReal_pos_iff, trichotomy
-/
theorem eLpNorm_le_eLpNorm_mul_eLpNorm_of_nnnorm {p q r : Real>=0∞}
    (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ) (b : E -> F -> G) (c : Real>=0)
    (h : forallᵐ x ∂μ, ‖b (f x) (g x)‖₊ <= c * ‖f x‖₊ * ‖g x‖₊) [hpqr : HolderTriple p q r] :
    eLpNorm (fun x => b (f x) (g x)) r μ <= c * eLpNorm f p μ * eLpNorm g q μ := by
  have hpqr := hpqr.one_div_eq
  obtain (rfl | rfl | hp) := ENNReal.trichotomy p
  · simp_all
  · have : r = q := by simpa using hpqr
    exact this ▸ eLpNorm_le_eLpNorm_top_mul_eLpNorm r f hg b c h
  obtain (rfl | rfl | hq) := ENNReal.trichotomy q
  · simp_all
  · have : r = p := by simpa using hpqr
    exact this ▸ eLpNorm_le_eLpNorm_mul_eLpNorm_top p hf g b c h
  obtain ⟨hp₁, hp₂⟩ := ENNReal.toReal_pos_iff.mp hp
  obtain ⟨hq₁, hq₂⟩ := ENNReal.toReal_pos_iff.mp hq
  have hpqr' : 1 / r.toReal = 1 / p.toReal + 1 / q.toReal := by
    have := congr(ENNReal.toReal $(hpqr))
    rw [ENNReal.toReal_add (by simpa using hp₁.ne') (by simpa using hq₁.ne')] at this
    simpa
have hr : 0 < r.toReal := one_div_pos.mp by rw [hpqr']; positivity
  obtain ⟨hr₁, hr₂⟩ := ENNReal.toReal_pos_iff.mp hr
have hrp : r.toReal < p.toReal := lt_of_one_div_lt_one_div hp
    hpqr' ▸ lt_add_of_pos_right _ (by positivity)
  rw [eLpNorm_eq_eLpNorm']; rw [eLpNorm_eq_eLpNorm']; rw [eLpNorm_eq_eLpNorm']
  · exact eLpNorm'_le_eLpNorm'_mul_eLpNorm' hf hg b c h hr hrp hpqr'
  all_goals first | positivity | finiteness

/--
theorem `eLpNorm_le_eLpNorm_mul_eLpNorm'_of_norm` / 定理 `eLpNorm_le_eLpNorm_mul_eLpNorm'_of_norm`

English:
theorem eLpNorm_le_eLpNorm_mul_eLpNorm'_of_norm
  statement: {p q r : Real>=0∞} (hf : AEStronglyMeasurable f μ)
  proof: eLpNorm_le_eLpNorm_mul_eLpNorm_of_nnnorm hf hg b c h

中文:
定理 eLpNorm_le_eLpNorm_mul_eLpNorm'_of_norm
  结论: {p q r : 实数>=0∞} (hf : AEStronglyMeasurable f μ)
  证明: eLpNorm_le_eLpNorm_mul_eLpNorm_of_nnnorm hf hg b c h

Depends on / 依赖: eLpNorm_le_eLpNorm_mul_eLpNorm_of_nnnorm
-/
theorem eLpNorm_le_eLpNorm_mul_eLpNorm'_of_norm {p q r : Real>=0∞} (hf : AEStronglyMeasurable f μ)
    (hg : AEStronglyMeasurable g μ) (b : E -> F -> G) (c : Real>=0)
    (h : forallᵐ x ∂μ, ‖b (f x) (g x)‖ <= c * ‖f x‖ * ‖g x‖) [hpqr : HolderTriple p q r] :
    eLpNorm (fun x => b (f x) (g x)) r μ <= c * eLpNorm f p μ * eLpNorm g q μ :=
  eLpNorm_le_eLpNorm_mul_eLpNorm_of_nnnorm hf hg b c h

open NNReal in
/--
theorem `MemLp.of_bilin` / 定理 `MemLp.of_bilin`

English:
theorem MemLp.of_bilin
  statement: {p q r : Real>=0∞} {f : α -> E} {g : α -> F} (b : E -> F -> G) (c : Real>=0)
  proof: by
  refine ⟨h, ?_⟩
  apply (eLpNorm_le_eLpNorm_mul_eLpNorm_of_nnnorm hf.1 hg.1 b c hb (hpqr := hpqr)).trans_lt
  finiteness [hf.2, hg.2]

中文:
定理 MemLp.of_bilin
  结论: {p q r : 实数>=0∞} {f : α -> E} {g : α -> F} (b : E -> F -> G) (c : 实数>=0)
  证明: by
  refine ⟨h, ?_⟩
  apply (eLpNorm_le_eLpNorm_mul_eLpNorm_of_nnnorm hf.1 hg.1 b c hb (hpqr := hpqr)).trans_lt
  finiteness [hf.2, hg.2]

Depends on / 依赖: eLpNorm_le_eLpNorm_mul_eLpNorm_of_nnnorm, finiteness, trans_lt
-/
theorem MemLp.of_bilin {p q r : Real>=0∞} {f : α -> E} {g : α -> F} (b : E -> F -> G) (c : Real>=0)
    (hf : MemLp f p μ) (hg : MemLp g q μ)
    (h : AEStronglyMeasurable (fun x => b (f x) (g x)) μ)
    (hb : forallᵐ (x : α) ∂μ, ‖b (f x) (g x)‖₊ <= c * ‖f x‖₊ * ‖g x‖₊)
    [hpqr : HolderTriple p q r] :
    MemLp (fun x => b (f x) (g x)) r μ := by
  refine ⟨h, ?_⟩
  apply (eLpNorm_le_eLpNorm_mul_eLpNorm_of_nnnorm hf.1 hg.1 b c hb (hpqr := hpqr)).trans_lt
  finiteness [hf.2, hg.2]

end Bilinear

section IsBoundedSMul

variable {𝕜 α E F : Type*} {m : MeasurableSpace α} {μ : Measure α} [NormedRing 𝕜]
  [NormedAddCommGroup E] [MulActionWithZero 𝕜 E] [IsBoundedSMul 𝕜 E]
  [NormedAddCommGroup F] [MulActionWithZero 𝕜 F] [IsBoundedSMul 𝕜 F] {f : α -> E}

/--
theorem `eLpNorm_smul_le_eLpNorm_top_mul_eLpNorm` / 定理 `eLpNorm_smul_le_eLpNorm_top_mul_eLpNorm`

English:
theorem eLpNorm_smul_le_eLpNorm_top_mul_eLpNorm
  statement: (p : Real>=0∞) (hf : AEStronglyMeasurable f μ)
  proof: by
  simpa using! (eLpNorm_le_eLpNorm_top_mul_eLpNorm p φ hf (· • ·) 1
    (.of_forall fun _ => by simpa using! nnnorm_smul_le _ _) :)

中文:
定理 eLpNorm_smul_le_eLpNorm_top_mul_eLpNorm
  结论: (p : 实数>=0∞) (hf : AEStronglyMeasurable f μ)
  证明: by
  simpa using! (eLpNorm_le_eLpNorm_top_mul_eLpNorm p φ hf (· • ·) 1
    (.of_forall fun _ => by simpa using! nnnorm_smul_le _ _) :)

Depends on / 依赖: eLpNorm_le_eLpNorm_top_mul_eLpNorm, nnnorm_smul_le, of_forall
-/
theorem eLpNorm_smul_le_eLpNorm_top_mul_eLpNorm (p : Real>=0∞) (hf : AEStronglyMeasurable f μ)
    (φ : α -> 𝕜) : eLpNorm (φ • f) p μ <= eLpNorm φ ∞ μ * eLpNorm f p μ := by
  simpa using! (eLpNorm_le_eLpNorm_top_mul_eLpNorm p φ hf (· • ·) 1
    (.of_forall fun _ => by simpa using! nnnorm_smul_le _ _) :)

/--
theorem `eLpNorm_smul_le_eLpNorm_mul_eLpNorm_top` / 定理 `eLpNorm_smul_le_eLpNorm_mul_eLpNorm_top`

English:
theorem eLpNorm_smul_le_eLpNorm_mul_eLpNorm_top
  statement: (p : Real>=0∞) (f : α -> E) {φ : α -> 𝕜}
  proof: by
  simpa using! (eLpNorm_le_eLpNorm_mul_eLpNorm_top p hφ f (· • ·) 1
    (.of_forall fun _ => by simpa using! nnnorm_smul_le _ _) :)

中文:
定理 eLpNorm_smul_le_eLpNorm_mul_eLpNorm_top
  结论: (p : 实数>=0∞) (f : α -> E) {φ : α -> 𝕜}
  证明: by
  simpa using! (eLpNorm_le_eLpNorm_mul_eLpNorm_top p hφ f (· • ·) 1
    (.of_forall fun _ => by simpa using! nnnorm_smul_le _ _) :)

Depends on / 依赖: eLpNorm_le_eLpNorm_mul_eLpNorm_top, nnnorm_smul_le, of_forall
-/
theorem eLpNorm_smul_le_eLpNorm_mul_eLpNorm_top (p : Real>=0∞) (f : α -> E) {φ : α -> 𝕜}
    (hφ : AEStronglyMeasurable φ μ) : eLpNorm (φ • f) p μ <= eLpNorm φ p μ * eLpNorm f ∞ μ := by
  simpa using! (eLpNorm_le_eLpNorm_mul_eLpNorm_top p hφ f (· • ·) 1
    (.of_forall fun _ => by simpa using! nnnorm_smul_le _ _) :)

/--
theorem `eLpNorm'_smul_le_mul_eLpNorm'` / 定理 `eLpNorm'_smul_le_mul_eLpNorm'`

English:
theorem eLpNorm'_smul_le_mul_eLpNorm'
  statement: {p q r : Real} {f : α -> E} (hf : AEStronglyMeasurable f μ)
  proof: by
  simpa using! eLpNorm'_le_eLpNorm'_mul_eLpNorm' hφ hf (· • ·) 1
    (.of_forall fun _ => by simpa using! nnnorm_smul_le _ _)
    hp0_lt hpq hpqr

中文:
定理 eLpNorm'_smul_le_mul_eLpNorm'
  结论: {p q r : 实数} {f : α -> E} (hf : AEStronglyMeasurable f μ)
  证明: by
  simpa using! eLpNorm'_le_eLpNorm'_mul_eLpNorm' hφ hf (· • ·) 1
    (.of_forall fun _ => by simpa using! nnnorm_smul_le _ _)
    hp0_lt hpq hpqr
-/
theorem eLpNorm'_smul_le_mul_eLpNorm' {p q r : Real} {f : α -> E} (hf : AEStronglyMeasurable f μ)
    {φ : α -> 𝕜} (hφ : AEStronglyMeasurable φ μ) (hp0_lt : 0 < p) (hpq : p < q)
    (hpqr : 1 / p = 1 / q + 1 / r) : eLpNorm' (φ • f) p μ <= eLpNorm' φ q μ * eLpNorm' f r μ := by
  simpa using! eLpNorm'_le_eLpNorm'_mul_eLpNorm' hφ hf (· • ·) 1
    (.of_forall fun _ => by simpa using! nnnorm_smul_le _ _)
    hp0_lt hpq hpqr

/--
theorem `eLpNorm_smul_le_mul_eLpNorm` / 定理 `eLpNorm_smul_le_mul_eLpNorm`

English:
theorem eLpNorm_smul_le_mul_eLpNorm
  statement: {p q r : Real>=0∞} {f : α -> E} (hf : AEStronglyMeasurable f μ)
  proof: by
  simpa using! (eLpNorm_le_eLpNorm_mul_eLpNorm_of_nnnorm hφ hf (· • ·) 1
      (.of_forall fun _ => by simpa using! nnnorm_smul_le _ _) : _)

中文:
定理 eLpNorm_smul_le_mul_eLpNorm
  结论: {p q r : 实数>=0∞} {f : α -> E} (hf : AEStronglyMeasurable f μ)
  证明: by
  simpa using! (eLpNorm_le_eLpNorm_mul_eLpNorm_of_nnnorm hφ hf (· • ·) 1
      (.of_forall fun _ => by simpa using! nnnorm_smul_le _ _) : _)

Depends on / 依赖: eLpNorm_le_eLpNorm_mul_eLpNorm_of_nnnorm, nnnorm_smul_le, of_forall
-/
theorem eLpNorm_smul_le_mul_eLpNorm {p q r : Real>=0∞} {f : α -> E} (hf : AEStronglyMeasurable f μ)
    {φ : α -> 𝕜} (hφ : AEStronglyMeasurable φ μ) [hpqr : HolderTriple p q r] :
    eLpNorm (φ • f) r μ <= eLpNorm φ p μ * eLpNorm f q μ := by
  simpa using! (eLpNorm_le_eLpNorm_mul_eLpNorm_of_nnnorm hφ hf (· • ·) 1
      (.of_forall fun _ => by simpa using! nnnorm_smul_le _ _) : _)

/--
theorem `MemLp.smul` / 定理 `MemLp.smul`

English:
theorem MemLp.smul
  statement: {p q r : Real>=0∞} {f : α -> E} {φ : α -> 𝕜} (hf : MemLp f q μ) (hφ : MemLp φ p μ)
  proof: ⟨hφ.1.smul hf.1,
.trans_lt eLpNorm_smul_le_mul_eLpNorm hf.1 hφ.1
      ENNReal.mul_lt_top hφ.eLpNorm_lt_top hf.eLpNorm_lt_top⟩

中文:
定理 MemLp.smul
  结论: {p q r : 实数>=0∞} {f : α -> E} {φ : α -> 𝕜} (hf : MemLp f q μ) (hφ : MemLp φ p μ)
  证明: ⟨hφ.1.smul hf.1,
.trans_lt eLpNorm_smul_le_mul_eLpNorm hf.1 hφ.1
      ENNReal.mul_lt_top hφ.eLpNorm_lt_top hf.eLpNorm_lt_top⟩

Depends on / 依赖: ENNReal, ENNReal.mul_lt_top, eLpNorm_lt_top, eLpNorm_smul_le_mul_eLpNorm, hf.eLpNorm_lt_top, mul_lt_top, trans_lt
-/
theorem MemLp.smul {p q r : Real>=0∞} {f : α -> E} {φ : α -> 𝕜} (hf : MemLp f q μ) (hφ : MemLp φ p μ)
    [hpqr : HolderTriple p q r] : MemLp (φ • f) r μ :=
  ⟨hφ.1.smul hf.1,
.trans_lt eLpNorm_smul_le_mul_eLpNorm hf.1 hφ.1
      ENNReal.mul_lt_top hφ.eLpNorm_lt_top hf.eLpNorm_lt_top⟩

end IsBoundedSMul

section Mul

variable {α : Type*} {_ : MeasurableSpace α} {𝕜 : Type*} [NormedRing 𝕜] {μ : Measure α}
  {p q r : Real>=0∞} {f : α -> 𝕜} {φ : α -> 𝕜}

/--
theorem `MemLp.mul` / 定理 `MemLp.mul`

English:
theorem MemLp.mul
  given: (hf : MemLp f q μ) (hφ : MemLp φ p μ) [hpqr : HolderTriple p q r]
  proof: MemLp.smul hf hφ

中文:
定理 MemLp.mul
  条件: (hf : MemLp f q μ) (hφ : MemLp φ p μ) [hpqr : HolderTriple p q r]
  证明: MemLp.smul hf hφ

Depends on / 依赖: MemLp.smul
-/
theorem MemLp.mul (hf : MemLp f q μ) (hφ : MemLp φ p μ) [hpqr : HolderTriple p q r] :
    MemLp (φ * f) r μ :=
  MemLp.smul hf hφ

/--
theorem `MemLp.mul'` / 定理 `MemLp.mul'`

English:
theorem MemLp.mul'
  given: (hf : MemLp f q μ) (hφ : MemLp φ p μ) [hpqr : HolderTriple p q r]
  proof: MemLp.smul hf hφ

中文:
定理 MemLp.mul'
  条件: (hf : MemLp f q μ) (hφ : MemLp φ p μ) [hpqr : HolderTriple p q r]
  证明: MemLp.smul hf hφ

Depends on / 依赖: MemLp.smul
-/
theorem MemLp.mul' (hf : MemLp f q μ) (hφ : MemLp φ p μ) [hpqr : HolderTriple p q r] :
    MemLp (fun x => φ x * f x) r μ :=
  MemLp.smul hf hφ

end Mul

section Prod
variable {ι α 𝕜 : Type*} {_ : MeasurableSpace α} [NormedCommRing 𝕜] {μ : Measure α} {f : ι -> α -> 𝕜}
  {p : ι -> Real>=0∞} {s : Finset ι}

open Finset in
/--
lemma `MemLp.prod` / 引理 `MemLp.prod`

English:
lemma MemLp.prod
  given: (hf : forall i in s, MemLp (f i) (p i) μ)
  proof: by
  induction s using cons_induction with
  | empty =>
    by_cases hμ : μ = 0 <;>
      simp [MemLp, eLpNormEssSup_const, hμ, aestronglyMeasurable_const, Pi.one_def]
  | cons i s hi ih =>
    rw [prod_cons]
    exact (ih <| forall_of_forall_cons hf).mul (hf i <| mem_cons_self ..) (hpqr := ⟨by simp

中文:
引理 MemLp.prod
  条件: (hf : 对任意 i in s, MemLp (f i) (p i) μ)
  证明: by
  induction s using cons_induction with
  | empty =>
    by_cases hμ : μ = 0 <;>
      simp [MemLp, eLpNormEssSup_const, hμ, aestronglyMeasurable_const, Pi.one_def]
  | cons i s hi ih =>
    rw [prod_cons]
    exact (ih <| forall_of_forall_cons hf).mul (hf i <| mem_cons_self ..) (hpqr := ⟨by simp
-/
protected lemma MemLp.prod (hf : forall i in s, MemLp (f i) (p i) μ) :
    MemLp (∏ i in s, f i) (∑ i in s, (p i)⁻¹)⁻¹ μ := by
  induction s using cons_induction with
  | empty =>
    by_cases hμ : μ = 0 <;>
      simp [MemLp, eLpNormEssSup_const, hμ, aestronglyMeasurable_const, Pi.one_def]
  | cons i s hi ih =>
    rw [prod_cons]
    exact (ih <| forall_of_forall_cons hf).mul (hf i <| mem_cons_self ..) (hpqr := ⟨by simp⟩)

/--
lemma `MemLp.prod'` / 引理 `MemLp.prod'`

English:
lemma MemLp.prod'
  given: (hf : forall i in s, MemLp (f i) (p i) μ)
  proof: by
  simpa [Finset.prod_fn] using MemLp.prod hf

中文:
引理 MemLp.prod'
  条件: (hf : 对任意 i in s, MemLp (f i) (p i) μ)
  证明: by
  simpa [Finset.prod_fn] using MemLp.prod hf
-/
protected lemma MemLp.prod' (hf : forall i in s, MemLp (f i) (p i) μ) :
    MemLp (fun ω => ∏ i in s, f i ω) (∑ i in s, (p i)⁻¹)⁻¹ μ := by
  simpa [Finset.prod_fn] using MemLp.prod hf

end Prod
end MeasureTheory
