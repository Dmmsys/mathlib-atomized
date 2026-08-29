/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Integral.MeanInequalities

/-!
# Triangle inequality for `Lp`-seminorm

In this file we prove several versions of the triangle inequality for the `Lp` seminorm,
as well as simple corollaries.
-/

public section

open Filter ENNReal
open scoped Topology

namespace MeasureTheory

variable {α E ε ε' : Type*} {m : MeasurableSpace α} [NormedAddCommGroup E]
  [TopologicalSpace ε] [ESeminormedAddMonoid ε] [TopologicalSpace ε'] [ESeminormedAddCommMonoid ε']
  {p : Real>=0∞} {q : Real} {μ : Measure α} {f g : α -> ε}

/--
theorem `eLpNorm'_add_le` / 定理 `eLpNorm'_add_le`

English:
theorem eLpNorm'_add_le
  statement: (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ)
  proof: calc
    (∫⁻ a, ‖(f + g) a‖ₑ ^ q ∂μ) ^ (1 / q) <= (∫⁻ a, ((‖f ·‖ₑ) + (‖g ·‖ₑ)) a ^ q ∂μ) ^ (1 / q) := by
      gcongr with a
      simp only [Pi.add_apply, enorm_add_le]
    _ <= eLpNorm' f q μ + eLpNorm' g q μ := ENNReal.lintegral_Lp_add_le hf.enorm hg.enorm hq1

中文:
定理 eLpNorm'_add_le
  结论: (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ)
  证明: calc
    (∫⁻ a, ‖(f + g) a‖ₑ ^ q ∂μ) ^ (1 / q) <= (∫⁻ a, ((‖f ·‖ₑ) + (‖g ·‖ₑ)) a ^ q ∂μ) ^ (1 / q) := by
      gcongr with a
      simp only [Pi.add_apply, enorm_add_le]
    _ <= eLpNorm' f q μ + eLpNorm' g q μ := ENNReal.lintegral_Lp_add_le hf.enorm hg.enorm hq1
-/
theorem eLpNorm'_add_le (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ)
    (hq1 : 1 <= q) : eLpNorm' (f + g) q μ <= eLpNorm' f q μ + eLpNorm' g q μ :=
  calc
    (∫⁻ a, ‖(f + g) a‖ₑ ^ q ∂μ) ^ (1 / q) <= (∫⁻ a, ((‖f ·‖ₑ) + (‖g ·‖ₑ)) a ^ q ∂μ) ^ (1 / q) := by
      gcongr with a
      simp only [Pi.add_apply, enorm_add_le]
    _ <= eLpNorm' f q μ + eLpNorm' g q μ := ENNReal.lintegral_Lp_add_le hf.enorm hg.enorm hq1

/--
theorem `eLpNorm'_add_le_of_le_one` / 定理 `eLpNorm'_add_le_of_le_one`

English:
theorem eLpNorm'_add_le_of_le_one
  given: (hf : AEStronglyMeasurable f μ) (hq0 : 0 <= q) (hq1 : q <= 1)
  proof: calc
    (∫⁻ a, ‖(f + g) a‖ₑ ^ q ∂μ) ^ (1 / q) <= (∫⁻ a, (((‖f ·‖ₑ)) + (‖g ·‖ₑ)) a ^ q ∂μ) ^ (1 / q) := by
      gcongr with a
      simp only [Pi.add_apply, enorm_add_le]
    _ <= (2 : Real>=0∞) ^ (1 / q - 1) * (eLpNorm' f q μ + eLpNorm' g q μ) :=
      ENNReal.lintegral_Lp_add_le_of_le_one hf.enorm hq0 hq1

中文:
定理 eLpNorm'_add_le_of_le_one
  条件: (hf : AEStronglyMeasurable f μ) (hq0 : 0 <= q) (hq1 : q <= 1)
  证明: calc
    (∫⁻ a, ‖(f + g) a‖ₑ ^ q ∂μ) ^ (1 / q) <= (∫⁻ a, (((‖f ·‖ₑ)) + (‖g ·‖ₑ)) a ^ q ∂μ) ^ (1 / q) := by
      gcongr with a
      simp only [Pi.add_apply, enorm_add_le]
    _ <= (2 : Real>=0∞) ^ (1 / q - 1) * (eLpNorm' f q μ + eLpNorm' g q μ) :=
      ENNReal.lintegral_Lp_add_le_of_le_one hf.enorm hq0 hq1
-/
theorem eLpNorm'_add_le_of_le_one (hf : AEStronglyMeasurable f μ) (hq0 : 0 <= q) (hq1 : q <= 1) :
    eLpNorm' (f + g) q μ <= 2 ^ (1 / q - 1) * (eLpNorm' f q μ + eLpNorm' g q μ) :=
  calc
    (∫⁻ a, ‖(f + g) a‖ₑ ^ q ∂μ) ^ (1 / q) <= (∫⁻ a, (((‖f ·‖ₑ)) + (‖g ·‖ₑ)) a ^ q ∂μ) ^ (1 / q) := by
      gcongr with a
      simp only [Pi.add_apply, enorm_add_le]
    _ <= (2 : Real>=0∞) ^ (1 / q - 1) * (eLpNorm' f q μ + eLpNorm' g q μ) :=
      ENNReal.lintegral_Lp_add_le_of_le_one hf.enorm hq0 hq1

/--
theorem `eLpNormEssSup_add_le` / 定理 `eLpNormEssSup_add_le`

English:
theorem eLpNormEssSup_add_le
  proof: by
  refine le_trans (essSup_mono_ae (Eventually.of_forall fun x => ?_)) (ENNReal.essSup_add_le _ _)
  simp_rw [Pi.add_apply]
  exact enorm_add_le _ _

中文:
定理 eLpNormEssSup_add_le
  证明: by
  refine le_trans (essSup_mono_ae (Eventually.of_forall fun x => ?_)) (ENNReal.essSup_add_le _ _)
  simp_rw [Pi.add_apply]
  exact enorm_add_le _ _

Depends on / 依赖: ENNReal, ENNReal.essSup_add_le, Eventually, Eventually.of_forall, Pi.add_apply, add_apply, enorm_add_le, essSup_add_le, essSup_mono_ae, le_trans, of_forall, simp_rw
-/
theorem eLpNormEssSup_add_le :
    eLpNormEssSup (f + g) μ <= eLpNormEssSup f μ + eLpNormEssSup g μ := by
  refine le_trans (essSup_mono_ae (Eventually.of_forall fun x => ?_)) (ENNReal.essSup_add_le _ _)
  simp_rw [Pi.add_apply]
  exact enorm_add_le _ _

/--
theorem `eLpNorm_add_le` / 定理 `eLpNorm_add_le`

English:
theorem eLpNorm_add_le
  statement: (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ)
  proof: by
  by_cases hp0 : p = 0
  · simp [hp0]
  by_cases hp_top : p = ∞
  · simp [hp_top, eLpNormEssSup_add_le]
  have hp1_real : 1 <= p.toReal := by
    rwa [← ENNReal.toReal_one, ENNReal.toReal_le_toReal ENNReal.one_ne_top hp_top]
  repeat rw [eLpNorm_eq_eLpNorm' hp0 hp_top]
  exact eLpNorm'_add_le hf hg hp1_real

中文:
定理 eLpNorm_add_le
  结论: (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ)
  证明: by
  by_cases hp0 : p = 0
  · simp [hp0]
  by_cases hp_top : p = ∞
  · simp [hp_top, eLpNormEssSup_add_le]
  have hp1_real : 1 <= p.toReal := by
    rwa [← ENNReal.toReal_one, ENNReal.toReal_le_toReal ENNReal.one_ne_top hp_top]
  repeat rw [eLpNorm_eq_eLpNorm' hp0 hp_top]
  exact eLpNorm'_add_le hf hg hp1_real

Depends on / 依赖: ENNReal, ENNReal.one_ne_top, ENNReal.toReal_le_toReal, ENNReal.toReal_one, _add_le, eLpNorm, eLpNormEssSup_add_le, eLpNorm_eq_eLpNorm, hp1_real, hp_top, one_ne_top, p.toReal, repeat, toReal, toReal_le_toReal, toReal_one
-/
theorem eLpNorm_add_le (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ)
    (hp1 : 1 <= p) : eLpNorm (f + g) p μ <= eLpNorm f p μ + eLpNorm g p μ := by
  by_cases hp0 : p = 0
  · simp [hp0]
  by_cases hp_top : p = ∞
  · simp [hp_top, eLpNormEssSup_add_le]
  have hp1_real : 1 <= p.toReal := by
    rwa [← ENNReal.toReal_one, ENNReal.toReal_le_toReal ENNReal.one_ne_top hp_top]
  repeat rw [eLpNorm_eq_eLpNorm' hp0 hp_top]
  exact eLpNorm'_add_le hf hg hp1_real

/--
theorem `eLpNorm_add_le'` / 定理 `eLpNorm_add_le'`

English:
theorem eLpNorm_add_le'
  statement: (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ)
  proof: by
  rcases eq_or_ne p 0 with (rfl | hp)
  · simp
  rcases lt_or_ge p 1 with (h'p | h'p)
  · simp only [eLpNorm_eq_eLpNorm' hp (h'p.trans ENNReal.one_lt_top).ne]
    convert! eLpNorm'_add_le_of_le_one hf ENNReal.toReal_nonneg _
    · have : p in Set.Ioo (0 : Real>=0∞) 1 := ⟨hp.bot_lt, h'p⟩
      simp only [LpAddConst, if_pos this]
    · simpa using ENNReal.toReal_mono ENNReal.one_ne_top h'p.le
  · simpa [LpAddConst_of_one_le h'p] using eLpNorm_add_le hf hg h'p

中文:
定理 eLpNorm_add_le'
  结论: (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ)
  证明: by
  rcases eq_or_ne p 0 with (rfl | hp)
  · simp
  rcases lt_or_ge p 1 with (h'p | h'p)
  · simp only [eLpNorm_eq_eLpNorm' hp (h'p.trans ENNReal.one_lt_top).ne]
    convert! eLpNorm'_add_le_of_le_one hf ENNReal.toReal_nonneg _
    · have : p in Set.Ioo (0 : Real>=0∞) 1 := ⟨hp.bot_lt, h'p⟩
      simp only [LpAddConst, if_pos this]
    · simpa using ENNReal.toReal_mono ENNReal.one_ne_top h'p.le
  · simpa [LpAddConst_of_one_le h'p] using eLpNorm_add_le hf hg h'p

Depends on / 依赖: ENNReal, ENNReal.one_lt_top, ENNReal.one_ne_top, ENNReal.toReal_mono, ENNReal.toReal_nonneg, LpAddConst, LpAddConst_of_one_le, Set.Ioo, _add_le_of_le_one, bot_lt, convert, eLpNorm, eLpNorm_add_le, eLpNorm_eq_eLpNorm, eq_or_ne, hp.bot_lt, if_pos, lt_or_ge, one_lt_top, one_ne_top
-/
theorem eLpNorm_add_le' (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ)
    (p : Real>=0∞) :
    eLpNorm (f + g) p μ <= LpAddConst p * (eLpNorm f p μ + eLpNorm g p μ) := by
  rcases eq_or_ne p 0 with (rfl | hp)
  · simp
  rcases lt_or_ge p 1 with (h'p | h'p)
  · simp only [eLpNorm_eq_eLpNorm' hp (h'p.trans ENNReal.one_lt_top).ne]
    convert! eLpNorm'_add_le_of_le_one hf ENNReal.toReal_nonneg _
    · have : p in Set.Ioo (0 : Real>=0∞) 1 := ⟨hp.bot_lt, h'p⟩
      simp only [LpAddConst, if_pos this]
    · simpa using ENNReal.toReal_mono ENNReal.one_ne_top h'p.le
  · simpa [LpAddConst_of_one_le h'p] using eLpNorm_add_le hf hg h'p

variable (μ ε) in
/--
theorem `exists_Lp_half` / 定理 `exists_Lp_half`

English:
theorem exists_Lp_half
  given: (p : Real>=0∞) {δ : Real>=0∞} (hδ : δ != 0)
  proof: by
  have :
    Tendsto (fun η : Real>=0∞ => LpAddConst p * (η + η)) (𝓝[>] 0)
        (𝓝 (LpAddConst p * (0 + 0))) :=
    (ENNReal.Tendsto.const_mul (tendsto_id.add tendsto_id)
          (Or.inr (LpAddConst_lt_top p).ne)).mono_left
      nhdsWithin_le_nhds
  simp only [add_zero, mul_zero] at this
  rcases (((tendsto_order.1 this).2 δ hδ.bot_lt).and self_mem_nhdsWithin).exists with ⟨η, hη, ηpos⟩
  refine ⟨η, ηpos, fun f g hf hg Hf Hg => ?_⟩
  calc
    eLpNorm (f + g) p μ <= LpAddConst p * (eLpNorm f p μ + eLpNorm g p μ) :=
      eLpNorm_add_le' hf hg p
    _ <= LpAddConst p * (η + η) := by gcongr
    _ < δ := hη

中文:
定理 存在_Lp_half
  条件: (p : 实数>=0∞) {δ : 实数>=0∞} (hδ : δ != 0)
  证明: by
  have :
    Tendsto (fun η : Real>=0∞ => LpAddConst p * (η + η)) (𝓝[>] 0)
        (𝓝 (LpAddConst p * (0 + 0))) :=
    (ENNReal.Tendsto.const_mul (tendsto_id.add tendsto_id)
          (Or.inr (LpAddConst_lt_top p).ne)).mono_left
      nhdsWithin_le_nhds
  simp only [add_zero, mul_zero] at this
  rcases (((tendsto_order.1 this).2 δ hδ.bot_lt).and self_mem_nhdsWithin).exists with ⟨η, hη, ηpos⟩
  refine ⟨η, ηpos, fun f g hf hg Hf Hg => ?_⟩
  calc
    eLpNorm (f + g) p μ <= LpAddConst p * (eLpNorm f p μ + eLpNorm g p μ) :=
      eLpNorm_add_le' hf hg p
    _ <= LpAddConst p * (η + η) := by gcongr
    _ < δ := hη

Depends on / 依赖: ENNReal, ENNReal.Tendsto.const_mul, LpAddConst, LpAddConst_lt_top, Or.inr, Tendsto, add_zero, bot_lt, const_mul, eLpNorm, eLpNorm_add_le, mono_left, mul_zero, nhdsWithin_le_nhds, self_mem_nhdsWithin, tendsto_id, tendsto_id.add, tendsto_order
-/
theorem exists_Lp_half (p : Real>=0∞) {δ : Real>=0∞} (hδ : δ != 0) :
    exists η : Real>=0∞,
      0 < η ∧
        forall (f g : α -> ε), AEStronglyMeasurable f μ -> AEStronglyMeasurable g μ ->
          eLpNorm f p μ <= η -> eLpNorm g p μ <= η -> eLpNorm (f + g) p μ < δ := by
  have :
    Tendsto (fun η : Real>=0∞ => LpAddConst p * (η + η)) (𝓝[>] 0)
        (𝓝 (LpAddConst p * (0 + 0))) :=
    (ENNReal.Tendsto.const_mul (tendsto_id.add tendsto_id)
          (Or.inr (LpAddConst_lt_top p).ne)).mono_left
      nhdsWithin_le_nhds
  simp only [add_zero, mul_zero] at this
  rcases (((tendsto_order.1 this).2 δ hδ.bot_lt).and self_mem_nhdsWithin).exists with ⟨η, hη, ηpos⟩
  refine ⟨η, ηpos, fun f g hf hg Hf Hg => ?_⟩
  calc
    eLpNorm (f + g) p μ <= LpAddConst p * (eLpNorm f p μ + eLpNorm g p μ) :=
      eLpNorm_add_le' hf hg p
    _ <= LpAddConst p * (η + η) := by gcongr
    _ < δ := hη

/--
theorem `eLpNorm_sub_le'` / 定理 `eLpNorm_sub_le'`

English:
theorem eLpNorm_sub_le'
  statement: {f g : α -> E}
  proof: by
  simpa only [sub_eq_add_neg, eLpNorm_neg] using eLpNorm_add_le' hf hg.neg p

中文:
定理 eLpNorm_sub_le'
  结论: {f g : α -> E}
  证明: by
  simpa only [sub_eq_add_neg, eLpNorm_neg] using eLpNorm_add_le' hf hg.neg p

Depends on / 依赖: eLpNorm_add_le, eLpNorm_neg, hg.neg, sub_eq_add_neg
-/
theorem eLpNorm_sub_le' {f g : α -> E}
    (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ)
    (p : Real>=0∞) :
    eLpNorm (f - g) p μ <= LpAddConst p * (eLpNorm f p μ + eLpNorm g p μ) := by
  simpa only [sub_eq_add_neg, eLpNorm_neg] using eLpNorm_add_le' hf hg.neg p

/--
theorem `eLpNorm_sub_le` / 定理 `eLpNorm_sub_le`

English:
theorem eLpNorm_sub_le
  statement: {f g : α -> E} (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ)
  proof: by
  simpa [LpAddConst_of_one_le hp] using eLpNorm_sub_le' hf hg p

中文:
定理 eLpNorm_sub_le
  结论: {f g : α -> E} (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ)
  证明: by
  simpa [LpAddConst_of_one_le hp] using eLpNorm_sub_le' hf hg p

Depends on / 依赖: LpAddConst_of_one_le, eLpNorm_sub_le
-/
theorem eLpNorm_sub_le {f g : α -> E} (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ)
    (hp : 1 <= p) : eLpNorm (f - g) p μ <= eLpNorm f p μ + eLpNorm g p μ := by
  simpa [LpAddConst_of_one_le hp] using eLpNorm_sub_le' hf hg p

/--
theorem `eLpNorm_add_lt_top` / 定理 `eLpNorm_add_lt_top`

English:
theorem eLpNorm_add_lt_top
  given: (hf : MemLp f p μ) (hg : MemLp g p μ)
  proof: calc
    eLpNorm (f + g) p μ <= LpAddConst p * (eLpNorm f p μ + eLpNorm g p μ) :=
      eLpNorm_add_le' hf.aestronglyMeasurable hg.aestronglyMeasurable p
    _ < ∞ := by
      apply ENNReal.mul_lt_top (LpAddConst_lt_top p)
      exact ENNReal.add_lt_top.2 ⟨hf.2, hg.2⟩

中文:
定理 eLpNorm_add_lt_top
  条件: (hf : MemLp f p μ) (hg : MemLp g p μ)
  证明: calc
    eLpNorm (f + g) p μ <= LpAddConst p * (eLpNorm f p μ + eLpNorm g p μ) :=
      eLpNorm_add_le' hf.aestronglyMeasurable hg.aestronglyMeasurable p
    _ < ∞ := by
      apply ENNReal.mul_lt_top (LpAddConst_lt_top p)
      exact ENNReal.add_lt_top.2 ⟨hf.2, hg.2⟩

Depends on / 依赖: ENNReal, ENNReal.add_lt_top, ENNReal.mul_lt_top, LpAddConst, LpAddConst_lt_top, add_lt_top, aestronglyMeasurable, eLpNorm, eLpNorm_add_le, hf.aestronglyMeasurable, hg.aestronglyMeasurable, mul_lt_top
-/
theorem eLpNorm_add_lt_top (hf : MemLp f p μ) (hg : MemLp g p μ) :
    eLpNorm (f + g) p μ < ∞ :=
  calc
    eLpNorm (f + g) p μ <= LpAddConst p * (eLpNorm f p μ + eLpNorm g p μ) :=
      eLpNorm_add_le' hf.aestronglyMeasurable hg.aestronglyMeasurable p
    _ < ∞ := by
      apply ENNReal.mul_lt_top (LpAddConst_lt_top p)
      exact ENNReal.add_lt_top.2 ⟨hf.2, hg.2⟩

/--
theorem `eLpNorm'_sum_le` / 定理 `eLpNorm'_sum_le`

English:
theorem eLpNorm'_sum_le
  statement: [ContinuousAdd ε'] {ι} {f : ι -> α -> ε'} {s : Finset ι}
  proof: Finset.le_sum_of_subadditive_on_pred (fun f : α -> ε' => eLpNorm' f q μ)
    (fun f => AEStronglyMeasurable f μ) (eLpNorm'_zero (zero_lt_one.trans_le hq1)).le
    (fun _f _g hf hg => eLpNorm'_add_le hf hg hq1) (fun _f _g hf hg => hf.add hg) _ hfs

中文:
定理 eLpNorm'_sum_le
  结论: [连续加法 ε'] {ι} {f : ι -> α -> ε'} {s : 有限集 ι}
  证明: Finset.le_sum_of_subadditive_on_pred (fun f : α -> ε' => eLpNorm' f q μ)
    (fun f => AEStronglyMeasurable f μ) (eLpNorm'_zero (zero_lt_one.trans_le hq1)).le
    (fun _f _g hf hg => eLpNorm'_add_le hf hg hq1) (fun _f _g hf hg => hf.add hg) _ hfs
-/
theorem eLpNorm'_sum_le [ContinuousAdd ε'] {ι} {f : ι -> α -> ε'} {s : Finset ι}
    (hfs : forall i, i in s -> AEStronglyMeasurable (f i) μ) (hq1 : 1 <= q) :
    eLpNorm' (∑ i in s, f i) q μ <= ∑ i in s, eLpNorm' (f i) q μ :=
  Finset.le_sum_of_subadditive_on_pred (fun f : α -> ε' => eLpNorm' f q μ)
    (fun f => AEStronglyMeasurable f μ) (eLpNorm'_zero (zero_lt_one.trans_le hq1)).le
    (fun _f _g hf hg => eLpNorm'_add_le hf hg hq1) (fun _f _g hf hg => hf.add hg) _ hfs

/--
theorem `eLpNorm_sum_le` / 定理 `eLpNorm_sum_le`

English:
theorem eLpNorm_sum_le
  statement: [ContinuousAdd ε'] {ι} {f : ι -> α -> ε'} {s : Finset ι}
  proof: Finset.le_sum_of_subadditive_on_pred (fun f : α -> ε' => eLpNorm f p μ)
    (fun f => AEStronglyMeasurable f μ) eLpNorm_zero.le
    (fun _f _g hf hg => eLpNorm_add_le hf hg hp1)
    (fun _f _g hf hg => hf.add hg) _ hfs

中文:
定理 eLpNorm_sum_le
  结论: [连续加法 ε'] {ι} {f : ι -> α -> ε'} {s : 有限集 ι}
  证明: Finset.le_sum_of_subadditive_on_pred (fun f : α -> ε' => eLpNorm f p μ)
    (fun f => AEStronglyMeasurable f μ) eLpNorm_zero.le
    (fun _f _g hf hg => eLpNorm_add_le hf hg hp1)
    (fun _f _g hf hg => hf.add hg) _ hfs

Depends on / 依赖: AEStronglyMeasurable, Finset, Finset.le_sum_of_subadditive_on_pred, eLpNorm, eLpNorm_add_le, eLpNorm_zero, eLpNorm_zero.le, hf.add, le_sum_of_subadditive_on_pred
-/
theorem eLpNorm_sum_le [ContinuousAdd ε'] {ι} {f : ι -> α -> ε'} {s : Finset ι}
    (hfs : forall i, i in s -> AEStronglyMeasurable (f i) μ) (hp1 : 1 <= p) :
    eLpNorm (∑ i in s, f i) p μ <= ∑ i in s, eLpNorm (f i) p μ :=
  Finset.le_sum_of_subadditive_on_pred (fun f : α -> ε' => eLpNorm f p μ)
    (fun f => AEStronglyMeasurable f μ) eLpNorm_zero.le
    (fun _f _g hf hg => eLpNorm_add_le hf hg hp1)
    (fun _f _g hf hg => hf.add hg) _ hfs

-- TODO: We can prove `eLpNorm_expect_le` once we have `Module ℚ≥0 ℝ≥0∞`

/--
theorem `MemLp.add` / 定理 `MemLp.add`

English:
theorem MemLp.add
  given: [ContinuousAdd ε] (hf : MemLp f p μ) (hg : MemLp g p μ)
  statement: MemLp (f + g) p μ
  proof: ⟨AEStronglyMeasurable.add hf.1 hg.1, eLpNorm_add_lt_top hf hg⟩

中文:
定理 MemLp.add
  条件: [连续加法 ε] (hf : MemLp f p μ) (hg : MemLp g p μ)
  结论: MemLp (f + g) p μ
  证明: ⟨AEStronglyMeasurable.add hf.1 hg.1, eLpNorm_add_lt_top hf hg⟩

Depends on / 依赖: AEStronglyMeasurable, AEStronglyMeasurable.add, eLpNorm_add_lt_top
-/
theorem MemLp.add [ContinuousAdd ε] (hf : MemLp f p μ) (hg : MemLp g p μ) : MemLp (f + g) p μ :=
  ⟨AEStronglyMeasurable.add hf.1 hg.1, eLpNorm_add_lt_top hf hg⟩

/--
theorem `MemLp.sub` / 定理 `MemLp.sub`

English:
theorem MemLp.sub
  given: {f g : α -> E} (hf : MemLp f p μ) (hg : MemLp g p μ)
  statement: MemLp (f - g) p μ
  proof: by
  rw [sub_eq_add_neg]
  exact hf.add hg.neg

中文:
定理 MemLp.sub
  条件: {f g : α -> E} (hf : MemLp f p μ) (hg : MemLp g p μ)
  结论: MemLp (f - g) p μ
  证明: by
  rw [sub_eq_add_neg]
  exact hf.add hg.neg

Depends on / 依赖: hf.add, hg.neg, sub_eq_add_neg
-/
theorem MemLp.sub {f g : α -> E} (hf : MemLp f p μ) (hg : MemLp g p μ) : MemLp (f - g) p μ := by
  rw [sub_eq_add_neg]
  exact hf.add hg.neg

/--
theorem `memLp_finsetSum` / 定理 `memLp_finsetSum`

English:
theorem memLp_finsetSum
  statement: [ContinuousAdd ε']
  proof: by
  have : DecidableEq ι := Classical.decEq _
  revert hf
  refine Finset.induction_on s ?_ ?_
  · simp
  · intro i s his ih hf
    simp only [his, Finset.sum_insert, not_false_iff]
    exact (hf i (s.mem_insert_self i)).add (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))

@[deprecated (since := "2026-04-08")] alias memLp_finset_sum := memLp_finsetSum

中文:
定理 memLp_finsetSum
  结论: [连续加法 ε']
  证明: by
  have : DecidableEq ι := Classical.decEq _
  revert hf
  refine Finset.induction_on s ?_ ?_
  · simp
  · intro i s his ih hf
    simp only [his, Finset.sum_insert, not_false_iff]
    exact (hf i (s.mem_insert_self i)).add (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))

@[deprecated (since := "2026-04-08")] alias memLp_finset_sum := memLp_finsetSum

Depends on / 依赖: Classical, Classical.decEq, DecidableEq, Finset, Finset.induction_on, Finset.mem_insert_of_mem, Finset.sum_insert, induction_on, mem_insert_of_mem, mem_insert_self, not_false_iff, revert, s.mem_insert_self, sum_insert
-/
theorem memLp_finsetSum [ContinuousAdd ε']
    {ι} (s : Finset ι) {f : ι -> α -> ε'} (hf : forall i in s, MemLp (f i) p μ) :
    MemLp (fun a => ∑ i in s, f i a) p μ := by
  have : DecidableEq ι := Classical.decEq _
  revert hf
  refine Finset.induction_on s ?_ ?_
  · simp
  · intro i s his ih hf
    simp only [his, Finset.sum_insert, not_false_iff]
    exact (hf i (s.mem_insert_self i)).add (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))

@[deprecated (since := "2026-04-08")] alias memLp_finset_sum := memLp_finsetSum

/--
theorem `memLp_finsetSum'` / 定理 `memLp_finsetSum'`

English:
theorem memLp_finsetSum'
  statement: [ContinuousAdd ε']
  proof: by
  convert! memLp_finsetSum s hf using 1
  ext x
  simp

@[deprecated (since := "2026-04-08")] alias memLp_finset_sum' := memLp_finsetSum'

中文:
定理 memLp_finsetSum'
  结论: [连续加法 ε']
  证明: by
  convert! memLp_finsetSum s hf using 1
  ext x
  simp

@[deprecated (since := "2026-04-08")] alias memLp_finset_sum' := memLp_finsetSum'

Depends on / 依赖: convert, memLp_finsetSum
-/
theorem memLp_finsetSum' [ContinuousAdd ε']
    {ι} (s : Finset ι) {f : ι -> α -> ε'} (hf : forall i in s, MemLp (f i) p μ) :
    MemLp (∑ i in s, f i) p μ := by
  convert! memLp_finsetSum s hf using 1
  ext x
  simp

@[deprecated (since := "2026-04-08")] alias memLp_finset_sum' := memLp_finsetSum'

end MeasureTheory
