/-
Copyright (c) 2023 Igor Khavkine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Khavkine
-/
module

public import Mathlib.MeasureTheory.Function.UniformIntegrable

/-!
# Uniform tightness

This file contains the definitions for uniform tightness for a family of Lp functions.
It is used as a hypothesis to the version of Vitali's convergence theorem for Lp spaces
that works also for spaces of infinite measure. This version of Vitali's theorem
is also proved later in the file.

## Main definitions

* `MeasureTheory.UnifTight`:
  A sequence of functions `f` is uniformly tight in `L^p` if for all `ε > 0`, there
  exists some measurable set `s` with finite measure such that the Lp-norm of
  `f i` restricted to `sᶜ` is smaller than `ε` for all `i`.

## Main results

* `MeasureTheory.unifTight_finite`: a finite sequence of Lp functions is uniformly
  tight.
* `MeasureTheory.tendsto_Lp_of_tendsto_ae`: a sequence of Lp functions which is uniformly
  integrable and uniformly tight converges in Lp if it converges almost everywhere.
* `MeasureTheory.tendstoInMeasure_iff_tendsto_Lp`: Vitali convergence theorem:
  a sequence of Lp functions converges in Lp if and only if it is uniformly integrable,
  uniformly tight and converges in measure.

## Tags

uniformly integrable, uniformly tight, Vitali convergence theorem
-/

@[expose] public section

namespace MeasureTheory

open Set Filter Topology MeasureTheory NNReal ENNReal

variable {α β ι : Type*} {m : MeasurableSpace α} {μ : Measure α} [NormedAddCommGroup β]

section UnifTight

/- This follows closely the `UnifIntegrable` section
from `Mathlib/MeasureTheory/Function/UniformIntegrable.lean`. -/

variable {f g : ι -> α -> β} {p : Real>=0∞}

/--
Definition of `UnifTight` / `UnifTight` 的定义

English:
definition UnifTight
  signature: {_ : MeasurableSpace α} (f : ι -> α -> β) (p : Real>=0∞) (μ : Measure α)
  body: forall ⦃ε : Real>=0⦄, 0 < ε -> exists s : Set α, μ s != ∞ ∧ forall i, eLpNorm (sᶜ.indicator (f i)) p μ <= ε

中文:
定义 UnifTight
  签名: {_ : MeasurableSpace α} (f : ι -> α -> β) (p : 实数>=0∞) (μ : Measure α)
  定义体: forall ⦃ε : Real>=0⦄, 0 < ε -> exists s : Set α, μ s != ∞ ∧ forall i, eLpNorm (sᶜ.indicator (f i)) p μ <= ε

Depends on / 依赖: eLpNorm, indicator
-/
def UnifTight {_ : MeasurableSpace α} (f : ι -> α -> β) (p : Real>=0∞) (μ : Measure α) : Prop :=
  forall ⦃ε : Real>=0⦄, 0 < ε -> exists s : Set α, μ s != ∞ ∧ forall i, eLpNorm (sᶜ.indicator (f i)) p μ <= ε

/--
theorem `unifTight_iff_ennreal` / 定理 `unifTight_iff_ennreal`

English:
theorem unifTight_iff_ennreal
  given: {_ : MeasurableSpace α} (f : ι -> α -> β) (p : Real>=0∞) (μ : Measure α)
  proof: by
  simp only [ENNReal.forall_ennreal, ENNReal.coe_pos]
  refine (and_iff_left ?_).symm
  simp only [zero_lt_top, le_top, implies_true, and_true, true_implies]
  use ∅; simpa only [measure_empty] using zero_ne_top

中文:
定理 unifTight_iff_ennreal
  条件: {_ : MeasurableSpace α} (f : ι -> α -> β) (p : 实数>=0∞) (μ : Measure α)
  证明: by
  simp only [ENNReal.forall_ennreal, ENNReal.coe_pos]
  refine (and_iff_left ?_).symm
  simp only [zero_lt_top, le_top, implies_true, and_true, true_implies]
  use ∅; simpa only [measure_empty] using zero_ne_top

Depends on / 依赖: ENNReal, ENNReal.coe_pos, ENNReal.forall_ennreal, and_iff_left, and_true, coe_pos, forall_ennreal, implies_true, le_top, measure_empty, true_implies, zero_lt_top, zero_ne_top
-/
theorem unifTight_iff_ennreal {_ : MeasurableSpace α} (f : ι -> α -> β) (p : Real>=0∞) (μ : Measure α) :
    UnifTight f p μ ↔ forall ⦃ε : Real>=0∞⦄, 0 < ε -> exists s : Set α,
      μ s != ∞ ∧ forall i, eLpNorm (sᶜ.indicator (f i)) p μ <= ε := by
  simp only [ENNReal.forall_ennreal, ENNReal.coe_pos]
  refine (and_iff_left ?_).symm
  simp only [zero_lt_top, le_top, implies_true, and_true, true_implies]
  use ∅; simpa only [measure_empty] using zero_ne_top

/--
theorem `unifTight_iff_real` / 定理 `unifTight_iff_real`

English:
theorem unifTight_iff_real
  given: {_ : MeasurableSpace α} (f : ι -> α -> β) (p : Real>=0∞) (μ : Measure α)
  proof: by
  refine ⟨fun hut rε hrε => hut (Real.toNNReal_pos.mpr hrε), fun hut ε hε => ?_⟩
  obtain ⟨s, hμs, hfε⟩ := hut hε
  use s, hμs; intro i
  exact (hfε i).trans_eq (ofReal_coe_nnreal (p := ε))

中文:
定理 unifTight_iff_real
  条件: {_ : MeasurableSpace α} (f : ι -> α -> β) (p : 实数>=0∞) (μ : Measure α)
  证明: by
  refine ⟨fun hut rε hrε => hut (Real.toNNReal_pos.mpr hrε), fun hut ε hε => ?_⟩
  obtain ⟨s, hμs, hfε⟩ := hut hε
  use s, hμs; intro i
  exact (hfε i).trans_eq (ofReal_coe_nnreal (p := ε))

Depends on / 依赖: Real.toNNReal_pos.mpr, ofReal_coe_nnreal, toNNReal_pos, trans_eq
-/
theorem unifTight_iff_real {_ : MeasurableSpace α} (f : ι -> α -> β) (p : Real>=0∞) (μ : Measure α) :
    UnifTight f p μ ↔ forall ⦃ε : Real⦄, 0 < ε -> exists s : Set α,
      μ s != ∞ ∧ forall i, eLpNorm (sᶜ.indicator (f i)) p μ <= .ofReal ε := by
  refine ⟨fun hut rε hrε => hut (Real.toNNReal_pos.mpr hrε), fun hut ε hε => ?_⟩
  obtain ⟨s, hμs, hfε⟩ := hut hε
  use s, hμs; intro i
  exact (hfε i).trans_eq (ofReal_coe_nnreal (p := ε))

namespace UnifTight

/--
theorem `eventually_cofinite_indicator` / 定理 `eventually_cofinite_indicator`

English:
theorem eventually_cofinite_indicator
  given: (hf : UnifTight f p μ) {ε : Real>=0∞} (hε : ε != 0)
  proof: by
  by_cases hε_top : ε = ∞
  · subst hε_top; simp
  rcases hf (pos_iff_ne_zero.2 (toNNReal_ne_zero.mpr ⟨hε,hε_top⟩)) with ⟨s, hμs, hfs⟩
  refine (eventually_smallSets' ?_).2 ⟨sᶜ, ?_, fun i => (coe_toNNReal hε_top) ▸ hfs i⟩
  · intro s t hst ht i
    exact (eLpNorm_mono <| norm_indicator_le_of_subs

中文:
定理 eventually_cofinite_indicator
  条件: (hf : UnifTight f p μ) {ε : 实数>=0∞} (hε : ε != 0)
  证明: by
  by_cases hε_top : ε = ∞
  · subst hε_top; simp
  rcases hf (pos_iff_ne_zero.2 (toNNReal_ne_zero.mpr ⟨hε,hε_top⟩)) with ⟨s, hμs, hfs⟩
  refine (eventually_smallSets' ?_).2 ⟨sᶜ, ?_, fun i => (coe_toNNReal hε_top) ▸ hfs i⟩
  · intro s t hst ht i
    exact (eLpNorm_mono <| norm_indicator_le_of_subs

Depends on / 依赖: Measure, Measure.compl_mem_cofinite, coe_toNNReal, compl_mem_cofinite, eLpNorm_mono, eventually_smallSets, lt_top_iff_ne_top, norm_indicator_le_of_subset, pos_iff_ne_zero, toNNReal_ne_zero, toNNReal_ne_zero.mpr
-/
theorem eventually_cofinite_indicator (hf : UnifTight f p μ) {ε : Real>=0∞} (hε : ε != 0) :
    forallᶠ s in μ.cofinite.smallSets, forall i, eLpNorm (s.indicator (f i)) p μ <= ε := by
  by_cases hε_top : ε = ∞
  · subst hε_top; simp
  rcases hf (pos_iff_ne_zero.2 (toNNReal_ne_zero.mpr ⟨hε,hε_top⟩)) with ⟨s, hμs, hfs⟩
  refine (eventually_smallSets' ?_).2 ⟨sᶜ, ?_, fun i => (coe_toNNReal hε_top) ▸ hfs i⟩
  · intro s t hst ht i
    exact (eLpNorm_mono <| norm_indicator_le_of_subset hst _).trans (ht i)
  · rwa [Measure.compl_mem_cofinite, lt_top_iff_ne_top]

/--
theorem `exists_measurableSet_indicator` / 定理 `exists_measurableSet_indicator`

English:
theorem exists_measurableSet_indicator
  given: (hf : UnifTight f p μ) {ε : Real>=0∞} (hε : ε != 0)
  proof: let ⟨s, hμs, hsm, hfs⟩ := (hf.eventually_cofinite_indicator hε).exists_measurable_mem_of_smallSets
  ⟨sᶜ, hsm.compl, hμs, by rwa [compl_compl s]⟩

中文:
定理 exists_measurableSet_indicator
  条件: (hf : UnifTight f p μ) {ε : 实数>=0∞} (hε : ε != 0)
  证明: let ⟨s, hμs, hsm, hfs⟩ := (hf.eventually_cofinite_indicator hε).exists_measurable_mem_of_smallSets
  ⟨sᶜ, hsm.compl, hμs, by rwa [compl_compl s]⟩
-/
protected theorem exists_measurableSet_indicator (hf : UnifTight f p μ) {ε : Real>=0∞} (hε : ε != 0) :
    exists s, MeasurableSet s ∧ μ s < ∞ ∧ forall i, eLpNorm (sᶜ.indicator (f i)) p μ <= ε :=
  let ⟨s, hμs, hsm, hfs⟩ := (hf.eventually_cofinite_indicator hε).exists_measurable_mem_of_smallSets
  ⟨sᶜ, hsm.compl, hμs, by rwa [compl_compl s]⟩

/--
theorem `add` / 定理 `add`

English:
theorem add
  statement: (hf : UnifTight f p μ) (hg : UnifTight g p μ)
  proof: fun ε hε => by
  rcases exists_Lp_half β μ p (coe_ne_zero.mpr hε.ne') with ⟨η, hη_pos, hη⟩
  by_cases hη_top : η = ∞
  · replace hη := hη_top ▸ hη
    refine ⟨∅, (by simp), fun i => ?_⟩
    simp only [compl_empty, indicator_univ, Pi.add_apply]
    exact (hη (f i) (g i) (hf_meas i) (hg_meas i) le_top

中文:
定理 add
  结论: (hf : UnifTight f p μ) (hg : UnifTight g p μ)
  证明: fun ε hε => by
  rcases exists_Lp_half β μ p (coe_ne_zero.mpr hε.ne') with ⟨η, hη_pos, hη⟩
  by_cases hη_top : η = ∞
  · replace hη := hη_top ▸ hη
    refine ⟨∅, (by simp), fun i => ?_⟩
    simp only [compl_empty, indicator_univ, Pi.add_apply]
    exact (hη (f i) (g i) (hf_meas i) (hg_meas i) le_top
-/
protected theorem add (hf : UnifTight f p μ) (hg : UnifTight g p μ)
    (hf_meas : forall i, AEStronglyMeasurable (f i) μ) (hg_meas : forall i, AEStronglyMeasurable (g i) μ) :
    UnifTight (f + g) p μ := fun ε hε => by
  rcases exists_Lp_half β μ p (coe_ne_zero.mpr hε.ne') with ⟨η, hη_pos, hη⟩
  by_cases hη_top : η = ∞
  · replace hη := hη_top ▸ hη
    refine ⟨∅, (by simp), fun i => ?_⟩
    simp only [compl_empty, indicator_univ, Pi.add_apply]
    exact (hη (f i) (g i) (hf_meas i) (hg_meas i) le_top le_top).le
  obtain ⟨s, hμs, hsm, hfs, hgs⟩ :
      exists s in μ.cofinite, MeasurableSet s ∧
        (forall i, eLpNorm (s.indicator (f i)) p μ <= η) ∧
        (forall i, eLpNorm (s.indicator (g i)) p μ <= η) :=
    ((hf.eventually_cofinite_indicator hη_pos.ne').and
      (hg.eventually_cofinite_indicator hη_pos.ne')).exists_measurable_mem_of_smallSets
  refine ⟨sᶜ, ne_of_lt hμs, fun i => ?_⟩
  have η_cast : ↑η.toNNReal = η := coe_toNNReal hη_top
  calc
    eLpNorm (indicator sᶜᶜ (f i + g i)) p μ
      = eLpNorm (indicator s (f i) + indicator s (g i)) p μ := by rw [compl_compl, indicator_add']
_ <= ε := le_of_lt
      hη _ _ ((hf_meas i).indicator hsm) ((hg_meas i).indicator hsm)
        (η_cast ▸ hfs i) (η_cast ▸ hgs i)

/--
theorem `neg` / 定理 `neg`

English:
theorem neg
  given: (hf : UnifTight f p μ)
  statement: UnifTight (-f) p μ
  proof: by
  simp_rw [UnifTight, Pi.neg_apply, Set.indicator_neg', eLpNorm_neg]
  exact hf

中文:
定理 neg
  条件: (hf : UnifTight f p μ)
  结论: UnifTight (-f) p μ
  证明: by
  simp_rw [UnifTight, Pi.neg_apply, Set.indicator_neg', eLpNorm_neg]
  exact hf
-/
protected theorem neg (hf : UnifTight f p μ) : UnifTight (-f) p μ := by
  simp_rw [UnifTight, Pi.neg_apply, Set.indicator_neg', eLpNorm_neg]
  exact hf

/--
theorem `sub` / 定理 `sub`

English:
theorem sub
  statement: (hf : UnifTight f p μ) (hg : UnifTight g p μ)
  proof: by
  rw [sub_eq_add_neg]
  exact hf.add hg.neg hf_meas fun i => (hg_meas i).neg

中文:
定理 sub
  结论: (hf : UnifTight f p μ) (hg : UnifTight g p μ)
  证明: by
  rw [sub_eq_add_neg]
  exact hf.add hg.neg hf_meas fun i => (hg_meas i).neg
-/
protected theorem sub (hf : UnifTight f p μ) (hg : UnifTight g p μ)
    (hf_meas : forall i, AEStronglyMeasurable (f i) μ) (hg_meas : forall i, AEStronglyMeasurable (g i) μ) :
    UnifTight (f - g) p μ := by
  rw [sub_eq_add_neg]
  exact hf.add hg.neg hf_meas fun i => (hg_meas i).neg

/--
theorem `aeeq` / 定理 `aeeq`

English:
theorem aeeq
  given: (hf : UnifTight f p μ) (hfg : forall n, f n =ᵐ[μ] g n)
  proof: by
  intro ε hε
  obtain ⟨s, hμs, hfε⟩ := hf hε
  refine ⟨s, hμs, fun n => (le_of_eq <| eLpNorm_congr_ae ?_).trans (hfε n)⟩
  filter_upwards [hfg n] with x hx
  simp only [indicator, mem_compl_iff, hx]

中文:
定理 aeeq
  条件: (hf : UnifTight f p μ) (hfg : 对任意 n, f n =ᵐ[μ] g n)
  证明: by
  intro ε hε
  obtain ⟨s, hμs, hfε⟩ := hf hε
  refine ⟨s, hμs, fun n => (le_of_eq <| eLpNorm_congr_ae ?_).trans (hfε n)⟩
  filter_upwards [hfg n] with x hx
  simp only [indicator, mem_compl_iff, hx]
-/
protected theorem aeeq (hf : UnifTight f p μ) (hfg : forall n, f n =ᵐ[μ] g n) :
    UnifTight g p μ := by
  intro ε hε
  obtain ⟨s, hμs, hfε⟩ := hf hε
  refine ⟨s, hμs, fun n => (le_of_eq <| eLpNorm_congr_ae ?_).trans (hfε n)⟩
  filter_upwards [hfg n] with x hx
  simp only [indicator, mem_compl_iff, hx]

end UnifTight

/--
theorem `unifTight_congr_ae` / 定理 `unifTight_congr_ae`

English:
theorem unifTight_congr_ae
  given: {g : ι -> α -> β} (hfg : forall n, f n =ᵐ[μ] g n)
  proof: ⟨fun h => h.aeeq hfg, fun h => h.aeeq fun i => (hfg i).symm⟩

中文:
定理 unifTight_congr_ae
  条件: {g : ι -> α -> β} (hfg : 对任意 n, f n =ᵐ[μ] g n)
  证明: ⟨fun h => h.aeeq hfg, fun h => h.aeeq fun i => (hfg i).symm⟩

Depends on / 依赖: h.aeeq
-/
theorem unifTight_congr_ae {g : ι -> α -> β} (hfg : forall n, f n =ᵐ[μ] g n) :
    UnifTight f p μ ↔ UnifTight g p μ :=
  ⟨fun h => h.aeeq hfg, fun h => h.aeeq fun i => (hfg i).symm⟩

/--
theorem `unifTight_const` / 定理 `unifTight_const`

English:
theorem unifTight_const
  given: {g : α -> β} (hp_ne_top : p != ∞) (hg : MemLp g p μ)
  proof: by
  intro ε hε
  by_cases hε_top : ε = ∞
  · exact ⟨∅, (by simp), fun _ => hε_top.symm ▸ le_top⟩
  obtain ⟨s, _, hμs, hgε⟩ := hg.exists_eLpNorm_indicator_compl_lt hp_ne_top (coe_ne_zero.mpr hε.ne')
  exact ⟨s, ne_of_lt hμs, fun _ => hgε.le⟩

中文:
定理 unifTight_const
  条件: {g : α -> β} (hp_ne_top : p != ∞) (hg : MemLp g p μ)
  证明: by
  intro ε hε
  by_cases hε_top : ε = ∞
  · exact ⟨∅, (by simp), fun _ => hε_top.symm ▸ le_top⟩
  obtain ⟨s, _, hμs, hgε⟩ := hg.exists_eLpNorm_indicator_compl_lt hp_ne_top (coe_ne_zero.mpr hε.ne')
  exact ⟨s, ne_of_lt hμs, fun _ => hgε.le⟩

Depends on / 依赖: _top.symm, coe_ne_zero, coe_ne_zero.mpr, exists_eLpNorm_indicator_compl_lt, hg.exists_eLpNorm_indicator_compl_lt, hp_ne_top, le_top, ne_of_lt
-/
theorem unifTight_const {g : α -> β} (hp_ne_top : p != ∞) (hg : MemLp g p μ) :
    UnifTight (fun _ : ι => g) p μ := by
  intro ε hε
  by_cases hε_top : ε = ∞
  · exact ⟨∅, (by simp), fun _ => hε_top.symm ▸ le_top⟩
  obtain ⟨s, _, hμs, hgε⟩ := hg.exists_eLpNorm_indicator_compl_lt hp_ne_top (coe_ne_zero.mpr hε.ne')
  exact ⟨s, ne_of_lt hμs, fun _ => hgε.le⟩

/--
theorem `unifTight_of_subsingleton` / 定理 `unifTight_of_subsingleton`

English:
theorem unifTight_of_subsingleton
  statement: [Subsingleton ι] (hp_top : p != ∞)
  proof: fun ε hε => by
  by_cases hε_top : ε = ∞
  · exact ⟨∅, by simp, fun _ => hε_top.symm ▸ le_top⟩
  by_cases hι : Nonempty ι
case neg => exact ⟨∅, (by simp), fun i => False.elim hι Nonempty.intro i⟩
  obtain ⟨i⟩ := hι
  obtain ⟨s, _, hμs, hfε⟩ := (hf i).exists_eLpNorm_indicator_compl_lt hp_top (coe_ne_

中文:
定理 unifTight_of_subsingleton
  结论: [Subsingleton ι] (hp_top : p != ∞)
  证明: fun ε hε => by
  by_cases hε_top : ε = ∞
  · exact ⟨∅, by simp, fun _ => hε_top.symm ▸ le_top⟩
  by_cases hι : Nonempty ι
case neg => exact ⟨∅, (by simp), fun i => False.elim hι Nonempty.intro i⟩
  obtain ⟨i⟩ := hι
  obtain ⟨s, _, hμs, hfε⟩ := (hf i).exists_eLpNorm_indicator_compl_lt hp_top (coe_ne_

Depends on / 依赖: False.elim, Nonempty, Nonempty.intro, _top.symm, coe_ne_zero, convert, exists_eLpNorm_indicator_compl_lt, hp_top, le_top, ne_of_lt
-/
theorem unifTight_of_subsingleton [Subsingleton ι] (hp_top : p != ∞)
    {f : ι -> α -> β} (hf : forall i, MemLp (f i) p μ) : UnifTight f p μ := fun ε hε => by
  by_cases hε_top : ε = ∞
  · exact ⟨∅, by simp, fun _ => hε_top.symm ▸ le_top⟩
  by_cases hι : Nonempty ι
case neg => exact ⟨∅, (by simp), fun i => False.elim hι Nonempty.intro i⟩
  obtain ⟨i⟩ := hι
  obtain ⟨s, _, hμs, hfε⟩ := (hf i).exists_eLpNorm_indicator_compl_lt hp_top (coe_ne_zero.2 hε.ne')
  refine ⟨s, ne_of_lt hμs, fun j => ?_⟩
  convert! hfε.le

/--
theorem `unifTight_fin` / 定理 `unifTight_fin`

English:
theorem unifTight_fin
  statement: (hp_top : p != ∞) {n : Nat} {f : Fin n -> α -> β}
  proof: by
  revert f
  induction n with
  | zero => exact fun {f} hf => unifTight_of_subsingleton hp_top hf
  | succ n h =>
    intro f hfLp ε hε
    by_cases hε_top : ε = ∞
    · exact ⟨∅, (by simp), fun _ => hε_top.symm ▸ le_top⟩
    let g : Fin n -> α -> β := fun k => f k.castSucc
    have hgLp : forall

中文:
定理 unifTight_fin
  结论: (hp_top : p != ∞) {n : 自然数} {f : Fin n -> α -> β}
  证明: by
  revert f
  induction n with
  | zero => exact fun {f} hf => unifTight_of_subsingleton hp_top hf
  | succ n h =>
    intro f hfLp ε hε
    by_cases hε_top : ε = ∞
    · exact ⟨∅, (by simp), fun _ => hε_top.symm ▸ le_top⟩
    let g : Fin n -> α -> β := fun k => f k.castSucc
    have hgLp : forall
-/
private theorem unifTight_fin (hp_top : p != ∞) {n : Nat} {f : Fin n -> α -> β}
    (hf : forall i, MemLp (f i) p μ) : UnifTight f p μ := by
  revert f
  induction n with
  | zero => exact fun {f} hf => unifTight_of_subsingleton hp_top hf
  | succ n h =>
    intro f hfLp ε hε
    by_cases hε_top : ε = ∞
    · exact ⟨∅, (by simp), fun _ => hε_top.symm ▸ le_top⟩
    let g : Fin n -> α -> β := fun k => f k.castSucc
    have hgLp : forall i, MemLp (g i) p μ := fun i => hfLp i.castSucc
    obtain ⟨S, hμS, hFε⟩ := h hgLp hε
    obtain ⟨s, _, hμs, hfε⟩ :=
      (hfLp (Fin.last n)).exists_eLpNorm_indicator_compl_lt hp_top (coe_ne_zero.2 hε.ne')
    refine ⟨s union S, (by finiteness), fun i => ?_⟩
    by_cases! hi : i.val < n
    · rw [show f i = g ⟨i.val, hi⟩ from rfl, compl_union, ← indicator_indicator]
      apply (eLpNorm_indicator_le _).trans
      exact hFε (Fin.castLT i hi)
    · obtain rfl : i = Fin.last n := Fin.ext (le_antisymm i.is_le hi)
      rw [compl_union]; rw [inter_comm]; rw [← indicator_indicator]
      exact (eLpNorm_indicator_le _).trans hfε.le

/--
theorem `unifTight_finite` / 定理 `unifTight_finite`

English:
theorem unifTight_finite
  statement: [Finite ι] (hp_top : p != ∞) {f : ι -> α -> β}
  proof: fun ε hε => by
  obtain ⟨n, hn⟩ := Finite.exists_equiv_fin ι
  set g : Fin n -> α -> β := f ∘ hn.some.symm
  have hg : forall i, MemLp (g i) p μ := fun _ => hf _
  obtain ⟨s, hμs, hfε⟩ := unifTight_fin hp_top hg hε
  refine ⟨s, hμs, fun i => ?_⟩
  simpa only [g, Function.comp_apply, Equiv.symm_apply

中文:
定理 unifTight_finite
  结论: [Finite ι] (hp_top : p != ∞) {f : ι -> α -> β}
  证明: fun ε hε => by
  obtain ⟨n, hn⟩ := Finite.exists_equiv_fin ι
  set g : Fin n -> α -> β := f ∘ hn.some.symm
  have hg : forall i, MemLp (g i) p μ := fun _ => hf _
  obtain ⟨s, hμs, hfε⟩ := unifTight_fin hp_top hg hε
  refine ⟨s, hμs, fun i => ?_⟩
  simpa only [g, Function.comp_apply, Equiv.symm_apply

Depends on / 依赖: Equiv.symm_apply_apply, Finite, Finite.exists_equiv_fin, Function, Function.comp_apply, comp_apply, exists_equiv_fin, hn.some, hn.some.symm, hp_top, symm_apply_apply, unifTight_fin
-/
theorem unifTight_finite [Finite ι] (hp_top : p != ∞) {f : ι -> α -> β}
    (hf : forall i, MemLp (f i) p μ) : UnifTight f p μ := fun ε hε => by
  obtain ⟨n, hn⟩ := Finite.exists_equiv_fin ι
  set g : Fin n -> α -> β := f ∘ hn.some.symm
  have hg : forall i, MemLp (g i) p μ := fun _ => hf _
  obtain ⟨s, hμs, hfε⟩ := unifTight_fin hp_top hg hε
  refine ⟨s, hμs, fun i => ?_⟩
  simpa only [g, Function.comp_apply, Equiv.symm_apply_apply] using hfε (hn.some i)

end UnifTight

section VitaliConvergence

variable {μ : Measure α} {p : Real>=0∞} {f : Nat -> α -> β} {g : α -> β}

/-! Both directions and an iff version of Vitali's convergence theorem on measure spaces
of not necessarily finite volume. See `Thm III.6.15` of Dunford & Schwartz, Part I (1958). -/

/- We start with the reverse direction. We only need to show that uniform tightness follows
from convergence in Lp. Mathlib already has the analogous `unifIntegrable_of_tendsto_Lp`
and `tendstoInMeasure_of_tendsto_eLpNorm`. -/

/--
theorem `unifTight_of_tendsto_Lp_zero` / 定理 `unifTight_of_tendsto_Lp_zero`

English:
theorem unifTight_of_tendsto_Lp_zero
  statement: (hp' : p != ∞) (hf : forall n, MemLp (f n) p μ)
  proof: by
  intro ε hε
  rw [ENNReal.tendsto_atTop_zero] at hf_tendsto
  obtain ⟨N, hNε⟩ := hf_tendsto ε (by simpa only [gt_iff_lt, ENNReal.coe_pos])
  let F : Fin N -> α -> β := fun n => f n
  have hF : forall n, MemLp (F n) p μ := fun n => hf n
  obtain ⟨s, hμs, hFε⟩ := unifTight_fin hp' hF hε
  refine ⟨

中文:
定理 unifTight_of_tendsto_Lp_zero
  结论: (hp' : p != ∞) (hf : 对任意 n, MemLp (f n) p μ)
  证明: by
  intro ε hε
  rw [ENNReal.tendsto_atTop_zero] at hf_tendsto
  obtain ⟨N, hNε⟩ := hf_tendsto ε (by simpa only [gt_iff_lt, ENNReal.coe_pos])
  let F : Fin N -> α -> β := fun n => f n
  have hF : forall n, MemLp (F n) p μ := fun n => hf n
  obtain ⟨s, hμs, hFε⟩ := unifTight_fin hp' hF hε
  refine ⟨
-/
private theorem unifTight_of_tendsto_Lp_zero (hp' : p != ∞) (hf : forall n, MemLp (f n) p μ)
    (hf_tendsto : Tendsto (fun n => eLpNorm (f n) p μ) atTop (𝓝 0)) : UnifTight f p μ := by
  intro ε hε
  rw [ENNReal.tendsto_atTop_zero] at hf_tendsto
  obtain ⟨N, hNε⟩ := hf_tendsto ε (by simpa only [gt_iff_lt, ENNReal.coe_pos])
  let F : Fin N -> α -> β := fun n => f n
  have hF : forall n, MemLp (F n) p μ := fun n => hf n
  obtain ⟨s, hμs, hFε⟩ := unifTight_fin hp' hF hε
  refine ⟨s, hμs, fun n => ?_⟩
  by_cases! hn : n < N
  · exact hFε ⟨n, hn⟩
  · exact (eLpNorm_indicator_le _).trans (hNε n hn)

/--
theorem `unifTight_of_tendsto_Lp` / 定理 `unifTight_of_tendsto_Lp`

English:
theorem unifTight_of_tendsto_Lp
  statement: (hp' : p != ∞) (hf : forall n, MemLp (f n) p μ)
  proof: by
  have : f = (fun _ => g) + fun n => f n - g := by ext1 n; simp
  rw [this]
  refine UnifTight.add ?_ ?_ (fun _ => hg.aestronglyMeasurable)
      fun n => (hf n).1.sub hg.aestronglyMeasurable
  · exact unifTight_const hp' hg
  · exact unifTight_of_tendsto_Lp_zero hp' (fun n => (hf n).sub hg) hfg

中文:
定理 unifTight_of_tendsto_Lp
  结论: (hp' : p != ∞) (hf : 对任意 n, MemLp (f n) p μ)
  证明: by
  have : f = (fun _ => g) + fun n => f n - g := by ext1 n; simp
  rw [this]
  refine UnifTight.add ?_ ?_ (fun _ => hg.aestronglyMeasurable)
      fun n => (hf n).1.sub hg.aestronglyMeasurable
  · exact unifTight_const hp' hg
  · exact unifTight_of_tendsto_Lp_zero hp' (fun n => (hf n).sub hg) hfg
-/
private theorem unifTight_of_tendsto_Lp (hp' : p != ∞) (hf : forall n, MemLp (f n) p μ)
    (hg : MemLp g p μ) (hfg : Tendsto (fun n => eLpNorm (f n - g) p μ) atTop (𝓝 0)) :
    UnifTight f p μ := by
  have : f = (fun _ => g) + fun n => f n - g := by ext1 n; simp
  rw [this]
  refine UnifTight.add ?_ ?_ (fun _ => hg.aestronglyMeasurable)
      fun n => (hf n).1.sub hg.aestronglyMeasurable
  · exact unifTight_const hp' hg
  · exact unifTight_of_tendsto_Lp_zero hp' (fun n => (hf n).sub hg) hfg

set_option linter.style.whitespace false in -- manual alignment is not recognised
/- Next we deal with the forward direction. The `MemLp` and `TendstoInMeasure` hypotheses
are unwrapped and strengthened (by known lemmas) to also have the `StronglyMeasurable`
and a.e. convergence hypotheses. The bulk of the proof is done under these stronger hypotheses. -/

/--
theorem `tendsto_Lp_of_tendsto_ae_of_meas` / 定理 `tendsto_Lp_of_tendsto_ae_of_meas`

English:
theorem tendsto_Lp_of_tendsto_ae_of_meas
  statement: (hp : 1 <= p) (hp' : p != ∞)
  proof: by
  rw [ENNReal.tendsto_atTop_zero]
  intro ε hε
  by_cases hfinε : ε != ∞; swap
  · rw [not_ne_iff.mp hfinε]; exact ⟨0, fun n _ => le_top⟩
  obtain rfl | hμ := eq_or_ne μ 0
  · simp
  have hε' : 0 < ε / 3 := ENNReal.div_pos hε.ne' (ofNat_ne_top)
  -- use tightness to divide the domain into interio

中文:
定理 tendsto_Lp_of_tendsto_ae_of_meas
  结论: (hp : 1 <= p) (hp' : p != ∞)
  证明: by
  rw [ENNReal.tendsto_atTop_zero]
  intro ε hε
  by_cases hfinε : ε != ∞; swap
  · rw [not_ne_iff.mp hfinε]; exact ⟨0, fun n _ => le_top⟩
  obtain rfl | hμ := eq_or_ne μ 0
  · simp
  have hε' : 0 < ε / 3 := ENNReal.div_pos hε.ne' (ofNat_ne_top)
  -- use tightness to divide the domain into interio
-/
private theorem tendsto_Lp_of_tendsto_ae_of_meas (hp : 1 <= p) (hp' : p != ∞)
    {f : Nat -> α -> β} {g : α -> β} (hf : forall n, StronglyMeasurable (f n)) (hg : StronglyMeasurable g)
    (hg' : MemLp g p μ) (hui : UnifIntegrable f p μ) (hut : UnifTight f p μ)
    (hfg : forallᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (g x))) :
    Tendsto (fun n => eLpNorm (f n - g) p μ) atTop (𝓝 0) := by
  rw [ENNReal.tendsto_atTop_zero]
  intro ε hε
  by_cases hfinε : ε != ∞; swap
  · rw [not_ne_iff.mp hfinε]; exact ⟨0, fun n _ => le_top⟩
  obtain rfl | hμ := eq_or_ne μ 0
  · simp
  have hε' : 0 < ε / 3 := ENNReal.div_pos hε.ne' (ofNat_ne_top)
  -- use tightness to divide the domain into interior and exterior
  obtain ⟨Eg, hmEg, hμEg, hgε⟩ := MemLp.exists_eLpNorm_indicator_compl_lt hp' hg' hε'.ne'
  obtain ⟨Ef, hmEf, hμEf, hfε⟩ := hut.exists_measurableSet_indicator hε'.ne'
  have hmE := hmEf.union hmEg
  have hfmE := (measure_union_le Ef Eg).trans_lt (add_lt_top.mpr ⟨hμEf, hμEg⟩)
  set E : Set α := Ef union Eg
  -- use uniform integrability to get control on the limit over E
  have hgE' := MemLp.restrict E hg'
  have huiE := hui.restrict E
  have hfgE : (forallᵐ x ∂(μ.restrict E), Tendsto (fun n => f n x) atTop (𝓝 (g x))) :=
    ae_restrict_of_ae hfg
  -- `tendsto_Lp_of_tendsto_ae_of_meas` needs to
  -- synthesize an argument `[IsFiniteMeasure (μ.restrict E)]`.
  -- It is enough to have in the context a term of `Fact (μ E < ∞)`, which is our `ffmE` below,
  -- which is automatically fed into `Restrict.isFiniteInstance`.
  have ffmE := Fact.mk hfmE
  have hInner := tendsto_Lp_finite_of_tendsto_ae_of_meas hp hp' hf hg hgE' huiE hfgE
  rw [ENNReal.tendsto_atTop_zero] at hInner
  -- get a sufficiently large N for given ε, and consider any n ≥ N
  obtain ⟨N, hfngε⟩ := hInner (ε / 3) hε'
  use N; intro n hn
  -- get interior estimates
  have hmfngE : AEStronglyMeasurable _ μ := (((hf n).sub hg).indicator hmE).aestronglyMeasurable
  have hfngEε := calc
    eLpNorm (E.indicator (f n - g)) p μ
      = eLpNorm (f n - g) p (μ.restrict E) := eLpNorm_indicator_eq_eLpNorm_restrict hmE
    _ <= ε / 3 := hfngε n hn
  -- get exterior estimates
  have hmgEc : AEStronglyMeasurable _ μ := (hg.indicator hmE.compl).aestronglyMeasurable
  have hgEcε := calc
    eLpNorm (Eᶜ.indicator g) p μ
      <= eLpNorm (Efᶜ.indicator (Egᶜ.indicator g)) p μ := by
        unfold E; rw [compl_union, ← indicator_indicator]
    _ <= eLpNorm (Egᶜ.indicator g) p μ := eLpNorm_indicator_le _
    _ <= ε / 3 := hgε.le
  have hmfnEc : AEStronglyMeasurable _ μ := ((hf n).indicator hmE.compl).aestronglyMeasurable
  have hfnEcε : eLpNorm (Eᶜ.indicator (f n)) p μ <= ε / 3 := calc
    eLpNorm (Eᶜ.indicator (f n)) p μ
      <= eLpNorm (Egᶜ.indicator (Efᶜ.indicator (f n))) p μ := by
        unfold E; rw [compl_union, inter_comm, ← indicator_indicator]
    _ <= eLpNorm (Efᶜ.indicator (f n)) p μ := eLpNorm_indicator_le _
    _ <= ε / 3 := hfε n
  have hmfngEc : AEStronglyMeasurable _ μ :=
    (((hf n).sub hg).indicator hmE.compl).aestronglyMeasurable
  have hfngEcε := calc
    eLpNorm (Eᶜ.indicator (f n - g)) p μ
      = eLpNorm (Eᶜ.indicator (f n) - Eᶜ.indicator g) p μ := by
        rw [(Eᶜ.indicator_sub' _ _)]
    _ <= eLpNorm (Eᶜ.indicator (f n)) p μ + eLpNorm (Eᶜ.indicator g) p μ := by
        apply eLpNorm_sub_le (by assumption) (by assumption) hp
    _ <= ε / 3 + ε / 3 := add_le_add hfnEcε hgEcε
  -- finally, combine interior and exterior estimates
  calc
    eLpNorm (f n - g) p μ
      = eLpNorm (Eᶜ.indicator (f n - g) + E.indicator (f n - g)) p μ := by
        congr; exact (E.indicator_compl_add_self _).symm
    _ <= eLpNorm (indicator Eᶜ (f n - g)) p μ + eLpNorm (indicator E (f n - g)) p μ := by
        apply eLpNorm_add_le (by assumption) (by assumption) hp
    _ <= (ε / 3 + ε / 3) + ε / 3 := add_le_add hfngEcε hfngEε
    _ = ε := by simp only [ENNReal.add_thirds]

/--
theorem `ae_tendsto_ae_congr` / 定理 `ae_tendsto_ae_congr`

English:
theorem ae_tendsto_ae_congr
  statement: {f f' : Nat -> α -> β} {g g' : α -> β}
  proof: by
  have hff'' := eventually_countable_forall.mpr hff'
  filter_upwards [hff'', hgg', hfg] with x hff'x hgg'x hfgx
  apply Tendsto.congr hff'x
  rw [← hgg'x]; exact hfgx

中文:
定理 ae_tendsto_ae_congr
  结论: {f f' : 自然数 -> α -> β} {g g' : α -> β}
  证明: by
  have hff'' := eventually_countable_forall.mpr hff'
  filter_upwards [hff'', hgg', hfg] with x hff'x hgg'x hfgx
  apply Tendsto.congr hff'x
  rw [← hgg'x]; exact hfgx
-/
private theorem ae_tendsto_ae_congr {f f' : Nat -> α -> β} {g g' : α -> β}
    (hff' : forall (n : Nat), f n =ᵐ[μ] f' n) (hgg' : g =ᵐ[μ] g')
    (hfg : forallᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (g x))) :
    forallᵐ x ∂μ, Tendsto (fun n => f' n x) atTop (𝓝 (g' x)) := by
  have hff'' := eventually_countable_forall.mpr hff'
  filter_upwards [hff'', hgg', hfg] with x hff'x hgg'x hfgx
  apply Tendsto.congr hff'x
  rw [← hgg'x]; exact hfgx

/--
theorem `tendsto_Lp_of_tendsto_ae` / 定理 `tendsto_Lp_of_tendsto_ae`

English:
theorem tendsto_Lp_of_tendsto_ae
  statement: (hp : 1 <= p) (hp' : p != ∞)
  proof: by
  -- come up with an a.e. equal strongly measurable replacement `f` for `g`
  have hf := fun n => (haef n).stronglyMeasurable_mk
  have hff' := fun n => (haef n).ae_eq_mk (μ := μ)
  have hui' := hui.ae_eq hff'
  have hut' := hut.aeeq hff'
  have hg := hg'.aestronglyMeasurable.stronglyMeasurable_m

中文:
定理 tendsto_Lp_of_tendsto_ae
  结论: (hp : 1 <= p) (hp' : p != ∞)
  证明: by
  -- come up with an a.e. equal strongly measurable replacement `f` for `g`
  have hf := fun n => (haef n).stronglyMeasurable_mk
  have hff' := fun n => (haef n).ae_eq_mk (μ := μ)
  have hui' := hui.ae_eq hff'
  have hut' := hut.aeeq hff'
  have hg := hg'.aestronglyMeasurable.stronglyMeasurable_m
-/
theorem tendsto_Lp_of_tendsto_ae (hp : 1 <= p) (hp' : p != ∞)
    {f : Nat -> α -> β} {g : α -> β} (haef : forall n, AEStronglyMeasurable (f n) μ)
    (hg' : MemLp g p μ) (hui : UnifIntegrable f p μ) (hut : UnifTight f p μ)
    (hfg : forallᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (g x))) :
    Tendsto (fun n => eLpNorm (f n - g) p μ) atTop (𝓝 0) := by
  -- come up with an a.e. equal strongly measurable replacement `f` for `g`
  have hf := fun n => (haef n).stronglyMeasurable_mk
  have hff' := fun n => (haef n).ae_eq_mk (μ := μ)
  have hui' := hui.ae_eq hff'
  have hut' := hut.aeeq hff'
  have hg := hg'.aestronglyMeasurable.stronglyMeasurable_mk
  have hgg' := hg'.aestronglyMeasurable.ae_eq_mk (μ := μ)
  have hg'' := hg'.ae_eq hgg'
  have haefg' := ae_tendsto_ae_congr hff' hgg' hfg
  set f' := fun n => (haef n).mk (μ := μ)
  set g' := hg'.aestronglyMeasurable.mk (μ := μ)
  have haefg (n : Nat) : f n - g =ᵐ[μ] f' n - g' := (hff' n).sub hgg'
  have hsnfg (n : Nat) := eLpNorm_congr_ae (p := p) (haefg n)
  apply Filter.Tendsto.congr (fun n => (hsnfg n).symm)
  exact tendsto_Lp_of_tendsto_ae_of_meas hp hp' hf hg hg'' hui' hut' haefg'

/--
theorem `tendsto_Lp_of_tendstoInMeasure` / 定理 `tendsto_Lp_of_tendstoInMeasure`

English:
theorem tendsto_Lp_of_tendstoInMeasure
  statement: (hp : 1 <= p) (hp' : p != ∞)
  proof: by
  refine tendsto_of_subseq_tendsto fun ns hns => ?_
  obtain ⟨ms, _, hms'⟩ := TendstoInMeasure.exists_seq_tendsto_ae fun ε hε => (hfg ε hε).comp hns
  exact ⟨ms,
    tendsto_Lp_of_tendsto_ae hp hp' (fun _ => hf _) hg
      (fun ε hε => -- `UnifIntegrable` on a subsequence
        let ⟨δ, hδ, hδ'⟩

中文:
定理 tendsto_Lp_of_tendstoInMeasure
  结论: (hp : 1 <= p) (hp' : p != ∞)
  证明: by
  refine tendsto_of_subseq_tendsto fun ns hns => ?_
  obtain ⟨ms, _, hms'⟩ := TendstoInMeasure.exists_seq_tendsto_ae fun ε hε => (hfg ε hε).comp hns
  exact ⟨ms,
    tendsto_Lp_of_tendsto_ae hp hp' (fun _ => hf _) hg
      (fun ε hε => -- `UnifIntegrable` on a subsequence
        let ⟨δ, hδ, hδ'⟩

Depends on / 依赖: TendstoInMeasure, TendstoInMeasure.exists_seq_tendsto_ae, UnifIntegrable, UnifTight, exists_seq_tendsto_ae, subsequence, tendsto_Lp_of_tendsto_ae, tendsto_of_subseq_tendsto
-/
theorem tendsto_Lp_of_tendstoInMeasure (hp : 1 <= p) (hp' : p != ∞)
    (hf : forall n, AEStronglyMeasurable (f n) μ) (hg : MemLp g p μ)
    (hui : UnifIntegrable f p μ) (hut : UnifTight f p μ)
    (hfg : TendstoInMeasure μ f atTop g) : Tendsto (fun n => eLpNorm (f n - g) p μ) atTop (𝓝 0) := by
  refine tendsto_of_subseq_tendsto fun ns hns => ?_
  obtain ⟨ms, _, hms'⟩ := TendstoInMeasure.exists_seq_tendsto_ae fun ε hε => (hfg ε hε).comp hns
  exact ⟨ms,
    tendsto_Lp_of_tendsto_ae hp hp' (fun _ => hf _) hg
      (fun ε hε => -- `UnifIntegrable` on a subsequence
        let ⟨δ, hδ, hδ'⟩ := hui hε
        ⟨δ, hδ, fun i s hs hμs => hδ' _ s hs hμs⟩)
      (fun ε hε => -- `UnifTight` on a subsequence
        let ⟨s, hμs, hfε⟩ := hut hε
        ⟨s, hμs, fun i => hfε _⟩)
      hms'⟩

/--
theorem `tendstoInMeasure_iff_tendsto_Lp` / 定理 `tendstoInMeasure_iff_tendsto_Lp`

English:
theorem tendstoInMeasure_iff_tendsto_Lp
  statement: (hp : 1 <= p) (hp' : p != ∞)
  proof: tendsto_Lp_of_tendstoInMeasure hp hp' (fun n => (hf n).1) hg h.2.1 h.2.2 h.1
  mpr h := ⟨tendstoInMeasure_of_tendsto_eLpNorm (lt_of_lt_of_le zero_lt_one hp).ne'
        (fun n => (hf n).aestronglyMeasurable) hg.aestronglyMeasurable h,
      unifIntegrable_of_tendsto_Lp hp hp' hf hg h,
      unifTigh

中文:
定理 tendstoInMeasure_iff_tendsto_Lp
  结论: (hp : 1 <= p) (hp' : p != ∞)
  证明: tendsto_Lp_of_tendstoInMeasure hp hp' (fun n => (hf n).1) hg h.2.1 h.2.2 h.1
  mpr h := ⟨tendstoInMeasure_of_tendsto_eLpNorm (lt_of_lt_of_le zero_lt_one hp).ne'
        (fun n => (hf n).aestronglyMeasurable) hg.aestronglyMeasurable h,
      unifIntegrable_of_tendsto_Lp hp hp' hf hg h,
      unifTigh

Depends on / 依赖: tendsto_Lp_of_tendstoInMeasure
-/
theorem tendstoInMeasure_iff_tendsto_Lp (hp : 1 <= p) (hp' : p != ∞)
    (hf : forall n, MemLp (f n) p μ) (hg : MemLp g p μ) :
    TendstoInMeasure μ f atTop g ∧ UnifIntegrable f p μ ∧ UnifTight f p μ
      ↔ Tendsto (fun n => eLpNorm (f n - g) p μ) atTop (𝓝 0) where
  mp h := tendsto_Lp_of_tendstoInMeasure hp hp' (fun n => (hf n).1) hg h.2.1 h.2.2 h.1
  mpr h := ⟨tendstoInMeasure_of_tendsto_eLpNorm (lt_of_lt_of_le zero_lt_one hp).ne'
        (fun n => (hf n).aestronglyMeasurable) hg.aestronglyMeasurable h,
      unifIntegrable_of_tendsto_Lp hp hp' hf hg h,
      unifTight_of_tendsto_Lp hp' hf hg h⟩

end VitaliConvergence
end MeasureTheory
