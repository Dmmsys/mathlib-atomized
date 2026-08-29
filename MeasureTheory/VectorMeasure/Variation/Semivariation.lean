/-
Copyright (c) 2026 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.MeasureTheory.VectorMeasure.Variation.Basic

import Mathlib.Analysis.Normed.Module.HahnBanach

/-!
# The semivariation of a vector measure

The semivariation of a vector measure is the supremum of the variations of its push-forwards
to `ℝ` through all linear forms of norm at most `1`. The interest of this notion is that, in the
reals, any set has nonnegative or nonpositive measure, so that the variation is realized by
a subset (up to a factor of at most `2`). This property is inherited by the semivariation in
general: one has the inequalities
```
‖μ s‖ₑ ≤ μ.semivariation s ≤ 2 sup_{t ⊆ s} ‖μ t‖ₑ
```

The notion of semivariation can in particular be used to show that any vector measure is bounded:
there exists `C < ∞` such that `‖μ s‖ ≤ C` for all `s`.

## Main results

* `μ.semivariation`: the semivariation of the vector measure `μ`.
* `exists_subset_lt_enorm_apply_of_lt_semivariation`: given `s`, there exists `t ⊆ s` such that
  `μ.semivariation s ≤ 2 ‖μ t‖ₑ` up to an arbitrarily small error.
* `μ.bound`: the semivariation of `univ`, in `ℝ≥0`. It is finite by definition.
* `enorm_apply_le_bound`: the inequality `‖μ s‖ₑ ≤ μ.bound`, uniformly in `s`.

## References

* [J. Diestel and J.J. Uhl, Vector Measures][DiestelUhl1977]

-/

public section

open scoped ENNReal Function Topology NNReal
open Set Filter

namespace MeasureTheory.VectorMeasure

variable {X E : Type*} [NormedAddCommGroup E] [NormedSpace Real E] {mX : MeasurableSpace X}
  {μ : VectorMeasure X E} {s t : Set X}

/--
Definition of `semivariation` / `semivariation` 的定义

English:
definition semivariation
  signature: (μ : VectorMeasure X E) (s : Set X)
  body: ⨆ ℓ in {ℓ : StrongDual Real E | ‖ℓ‖ₑ <= 1}, (μ.mapRange (ℓ : E ->+ Real) ℓ.continuous).variation s

中文:
定义 semivariation
  签名: (μ : 向量测度 X E) (s : 集合 X)
  定义体: ⨆ ℓ in {ℓ : StrongDual Real E | ‖ℓ‖ₑ <= 1}, (μ.mapRange (ℓ : E ->+ Real) ℓ.continuous).variation s

Depends on / 依赖: StrongDual, continuous, mapRange, variation
-/
noncomputable def semivariation (μ : VectorMeasure X E) (s : Set X) : Real>=0∞ :=
  ⨆ ℓ in {ℓ : StrongDual Real E | ‖ℓ‖ₑ <= 1}, (μ.mapRange (ℓ : E ->+ Real) ℓ.continuous).variation s

/--
lemma `semivariation_union_le` / 引理 `semivariation_union_le`

English:
lemma semivariation_union_le
  proof: by
  simp only [semivariation, iSup_le_iff]
  intro ℓ hℓ
  apply (measure_union_le _ _).trans
  gcongr <;> apply le_biSup _ hℓ

中文:
引理 semivariation_union_le
  证明: by
  simp only [semivariation, iSup_le_iff]
  intro ℓ hℓ
  apply (measure_union_le _ _).trans
  gcongr <;> apply le_biSup _ hℓ

Depends on / 依赖: iSup_le_iff, le_biSup, measure_union_le, semivariation
-/
lemma semivariation_union_le :
    μ.semivariation (s union t) <= μ.semivariation s + μ.semivariation t := by
  simp only [semivariation, iSup_le_iff]
  intro ℓ hℓ
  apply (measure_union_le _ _).trans
  gcongr <;> apply le_biSup _ hℓ

/--
lemma `semivariation_mono` / 引理 `semivariation_mono`

English:
lemma semivariation_mono
  given: (hst : s subseteq t)
  statement: μ.semivariation s <= μ.semivariation t
  proof: by
  simp only [semivariation, iSup_le_iff]
  intro ℓ hℓ
  apply (measure_mono hst).trans
  apply le_biSup _ hℓ

中文:
引理 semivariation_mono
  条件: (hst : s subseteq t)
  结论: μ.semivariation s <= μ.semivariation t
  证明: by
  simp only [semivariation, iSup_le_iff]
  intro ℓ hℓ
  apply (measure_mono hst).trans
  apply le_biSup _ hℓ

Depends on / 依赖: iSup_le_iff, le_biSup, measure_mono, semivariation
-/
lemma semivariation_mono (hst : s subseteq t) : μ.semivariation s <= μ.semivariation t := by
  simp only [semivariation, iSup_le_iff]
  intro ℓ hℓ
  apply (measure_mono hst).trans
  apply le_biSup _ hℓ

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `semivariation_le_variation` / 引理 `semivariation_le_variation`

English:
lemma semivariation_le_variation
  statement: μ.semivariation s <= μ.variation s
  proof: by
  simp only [semivariation, iSup_le_iff]
  intro ℓ hℓ
  suffices (μ.mapRange (ℓ : E ->+ Real) ℓ.continuous).variation <= μ.variation from this s
  apply variation_le_of_forall_enorm_le (fun t ht => ?_)
  simp only [mapRange_apply, AddMonoidHom.coe_coe]
  apply le_trans ?_ (enorm_measure_le_variation _ _)
  exact (ContinuousLinearMap.le_opENorm _ _).trans (mul_le_of_le_one_left (by positivity) hℓ)

中文:
引理 semivariation_le_variation
  结论: μ.semivariation s <= μ.variation s
  证明: by
  simp only [semivariation, iSup_le_iff]
  intro ℓ hℓ
  suffices (μ.mapRange (ℓ : E ->+ Real) ℓ.continuous).variation <= μ.variation from this s
  apply variation_le_of_forall_enorm_le (fun t ht => ?_)
  simp only [mapRange_apply, AddMonoidHom.coe_coe]
  apply le_trans ?_ (enorm_measure_le_variation _ _)
  exact (ContinuousLinearMap.le_opENorm _ _).trans (mul_le_of_le_one_left (by positivity) hℓ)

Depends on / 依赖: AddMonoidHom, AddMonoidHom.coe_coe, ContinuousLinearMap, ContinuousLinearMap.le_opENorm, coe_coe, continuous, enorm_measure_le_variation, iSup_le_iff, le_opENorm, le_trans, mapRange, mapRange_apply, mul_le_of_le_one_left, semivariation, variation, variation_le_of_forall_enorm_le
-/
lemma semivariation_le_variation : μ.semivariation s <= μ.variation s := by
  simp only [semivariation, iSup_le_iff]
  intro ℓ hℓ
  suffices (μ.mapRange (ℓ : E ->+ Real) ℓ.continuous).variation <= μ.variation from this s
  apply variation_le_of_forall_enorm_le (fun t ht => ?_)
  simp only [mapRange_apply, AddMonoidHom.coe_coe]
  apply le_trans ?_ (enorm_measure_le_variation _ _)
  exact (ContinuousLinearMap.le_opENorm _ _).trans (mul_le_of_le_one_left (by positivity) hℓ)

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `enorm_apply_le_semivariation` / 引理 `enorm_apply_le_semivariation`

English:
lemma enorm_apply_le_semivariation
  statement: ‖μ s‖ₑ <= μ.semivariation s
  proof: by
  by_cases hs : MeasurableSet s; swap
  · simp [not_measurable, hs]
  obtain ⟨ℓ, ℓ_norm, hℓ⟩ : exists ℓ : StrongDual Real E, ‖ℓ‖ <= 1 ∧ ℓ (μ s) = ‖μ s‖ :=
    exists_dual_vector'' _ _
  have h'ℓ : ℓ in {ℓ : StrongDual Real E | ‖ℓ‖ₑ <= 1} := by
    simp [enorm_eq_nnnorm, ← NNReal.coe_le_one, ℓ_norm]
  calc ‖μ s‖ₑ
  _ = ‖(μ.mapRange (ℓ : E ->+ Real) ℓ.continuous) s‖ₑ := by simp [← ofReal_norm, hℓ]
  _ <= (μ.mapRange (ℓ : E ->+ Real) ℓ.continuous).variation s := enorm_measure_le_variation _ _
  _ <= μ.semivariation s := by apply le_biSup _ h'ℓ

中文:
引理 enorm_apply_le_semivariation
  结论: ‖μ s‖ₑ <= μ.semivariation s
  证明: by
  by_cases hs : MeasurableSet s; swap
  · simp [not_measurable, hs]
  obtain ⟨ℓ, ℓ_norm, hℓ⟩ : exists ℓ : StrongDual Real E, ‖ℓ‖ <= 1 ∧ ℓ (μ s) = ‖μ s‖ :=
    exists_dual_vector'' _ _
  have h'ℓ : ℓ in {ℓ : StrongDual Real E | ‖ℓ‖ₑ <= 1} := by
    simp [enorm_eq_nnnorm, ← NNReal.coe_le_one, ℓ_norm]
  calc ‖μ s‖ₑ
  _ = ‖(μ.mapRange (ℓ : E ->+ Real) ℓ.continuous) s‖ₑ := by simp [← ofReal_norm, hℓ]
  _ <= (μ.mapRange (ℓ : E ->+ Real) ℓ.continuous).variation s := enorm_measure_le_variation _ _
  _ <= μ.semivariation s := by apply le_biSup _ h'ℓ

Depends on / 依赖: MeasurableSet, NNReal, NNReal.coe_le_one, StrongDual, coe_le_one, continuous, enorm_eq_nnnorm, enorm_measure_le_variation, exists_dual_vector, mapRange, not_measurable, ofReal_norm, semivariation, variation
-/
lemma enorm_apply_le_semivariation : ‖μ s‖ₑ <= μ.semivariation s := by
  by_cases hs : MeasurableSet s; swap
  · simp [not_measurable, hs]
  obtain ⟨ℓ, ℓ_norm, hℓ⟩ : exists ℓ : StrongDual Real E, ‖ℓ‖ <= 1 ∧ ℓ (μ s) = ‖μ s‖ :=
    exists_dual_vector'' _ _
  have h'ℓ : ℓ in {ℓ : StrongDual Real E | ‖ℓ‖ₑ <= 1} := by
    simp [enorm_eq_nnnorm, ← NNReal.coe_le_one, ℓ_norm]
  calc ‖μ s‖ₑ
  _ = ‖(μ.mapRange (ℓ : E ->+ Real) ℓ.continuous) s‖ₑ := by simp [← ofReal_norm, hℓ]
  _ <= (μ.mapRange (ℓ : E ->+ Real) ℓ.continuous).variation s := enorm_measure_le_variation _ _
  _ <= μ.semivariation s := by apply le_biSup _ h'ℓ

/--
lemma `enorm_apply_le_semivariation_of_subset` / 引理 `enorm_apply_le_semivariation_of_subset`

English:
lemma enorm_apply_le_semivariation_of_subset
  given: (hst : s subseteq t)
  proof: enorm_apply_le_semivariation.trans (semivariation_mono hst)

中文:
引理 enorm_apply_le_semivariation_of_subset
  条件: (hst : s subseteq t)
  证明: enorm_apply_le_semivariation.trans (semivariation_mono hst)

Depends on / 依赖: enorm_apply_le_semivariation, enorm_apply_le_semivariation.trans, semivariation_mono
-/
lemma enorm_apply_le_semivariation_of_subset (hst : s subseteq t) :
    ‖μ s‖ₑ <= μ.semivariation t :=
  enorm_apply_le_semivariation.trans (semivariation_mono hst)

/--
lemma `exists_subset_lt_enorm_apply_of_lt_semivariation` / 引理 `exists_subset_lt_enorm_apply_of_lt_semivariation`

English:
lemma exists_subset_lt_enorm_apply_of_lt_semivariation
  statement: (hs : MeasurableSet s)
  proof: by
  obtain ⟨ℓ, hℓ, h'ℓ⟩ : exists ℓ in {ℓ : StrongDual Real E | ‖ℓ‖ₑ <= 1},
    a < (μ.mapRange (ℓ : E ->+ Real) ℓ.continuous).variation s := lt_biSup_iff.1 ha
  obtain ⟨t, ts, t_meas, ht⟩ :
      exists t subseteq s, MeasurableSet t ∧ a < 2 * ‖μ.mapRange (ℓ : E ->+ Real) ℓ.continuous t‖ₑ :=
    SignedMeasure.exists_subset_lt_enorm_apply_of_lt_variation _ hs h'ℓ
  refine ⟨t, ts, t_meas, ht.trans_le ?_⟩
  gcongr
  exact (ContinuousLinearMap.le_opENorm _ _).trans (mul_le_of_le_one_left (by positivity) hℓ)

中文:
引理 存在_subset_lt_enorm_apply_of_lt_semivariation
  结论: (hs : 可测集 s)
  证明: by
  obtain ⟨ℓ, hℓ, h'ℓ⟩ : exists ℓ in {ℓ : StrongDual Real E | ‖ℓ‖ₑ <= 1},
    a < (μ.mapRange (ℓ : E ->+ Real) ℓ.continuous).variation s := lt_biSup_iff.1 ha
  obtain ⟨t, ts, t_meas, ht⟩ :
      exists t subseteq s, MeasurableSet t ∧ a < 2 * ‖μ.mapRange (ℓ : E ->+ Real) ℓ.continuous t‖ₑ :=
    SignedMeasure.exists_subset_lt_enorm_apply_of_lt_variation _ hs h'ℓ
  refine ⟨t, ts, t_meas, ht.trans_le ?_⟩
  gcongr
  exact (ContinuousLinearMap.le_opENorm _ _).trans (mul_le_of_le_one_left (by positivity) hℓ)

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.le_opENorm, MeasurableSet, SignedMeasure, SignedMeasure.exists_subset_lt_enorm_apply_of_lt_variation, StrongDual, continuous, exists_subset_lt_enorm_apply_of_lt_variation, ht.trans_le, le_opENorm, lt_biSup_iff, mapRange, mul_le_of_le_one_left, subseteq, t_meas, trans_le, variation
-/
lemma exists_subset_lt_enorm_apply_of_lt_semivariation (hs : MeasurableSet s)
    {a : Real>=0∞} (ha : a < μ.semivariation s) :
    exists t subseteq s, MeasurableSet t ∧ a < 2 * ‖μ t‖ₑ := by
  obtain ⟨ℓ, hℓ, h'ℓ⟩ : exists ℓ in {ℓ : StrongDual Real E | ‖ℓ‖ₑ <= 1},
    a < (μ.mapRange (ℓ : E ->+ Real) ℓ.continuous).variation s := lt_biSup_iff.1 ha
  obtain ⟨t, ts, t_meas, ht⟩ :
      exists t subseteq s, MeasurableSet t ∧ a < 2 * ‖μ.mapRange (ℓ : E ->+ Real) ℓ.continuous t‖ₑ :=
    SignedMeasure.exists_subset_lt_enorm_apply_of_lt_variation _ hs h'ℓ
  refine ⟨t, ts, t_meas, ht.trans_le ?_⟩
  gcongr
  exact (ContinuousLinearMap.le_opENorm _ _).trans (mul_le_of_le_one_left (by positivity) hℓ)

/--
lemma `exists_one_le_enorm_apply_of_semivariation_eq_top` / 引理 `exists_one_le_enorm_apply_of_semivariation_eq_top`

English:
lemma exists_one_le_enorm_apply_of_semivariation_eq_top
  proof: by
  obtain ⟨t, ts, t_meas, ht⟩ : exists t subseteq s, MeasurableSet t ∧ 2 * ‖μ s‖ₑ + 2 < 2 * ‖μ t‖ₑ := by
    apply exists_subset_lt_enorm_apply_of_lt_semivariation hs
    rw [h's]
    finiteness
  have h't : 1 + ‖μ s‖ₑ <= ‖μ t‖ₑ := by
    apply (ENNReal.mul_le_mul_iff_right (a := 2) (by simp) (by simp)).1
    rw [mul_add]; rw [add_comm]; rw [mul_one]
    exact ht.le
  have I : ∞ <= μ.semivariation t + μ.semivariation (s \ t) := by
    rw [← h's]
    apply le_trans (semivariation_mono (by simp)) semivariation_union_le
  simp only [top_le_iff, ENNReal.add_eq_top] at I
  rcases I with hI | hI
  · refine ⟨t, t_meas, ts, hI, ?_⟩
    have : 1 + ‖μ s‖ₑ <= ‖μ (s \ t)‖ₑ + ‖μ s‖ₑ := by
      apply h't.trans
      have : μ t = μ s - μ (s \ t) := by rw [← of_add_of_sdiff t_meas hs ts]; abel
      rw [this]; rw [add_comm]
      exact enorm_sub_le
    rwa [ENNReal.add_le_add_iff_right (by simp)] at this
  · refine ⟨s \ t, hs.diff t_meas, sdiff_subset, hI, ?_⟩
    simp only [_root_.sdiff_sdiff_right_self, ts, inf_of_le_right]
    exact le_trans (by simp) h't

中文:
引理 存在_one_le_enorm_apply_of_semivariation_eq_top
  证明: by
  obtain ⟨t, ts, t_meas, ht⟩ : exists t subseteq s, MeasurableSet t ∧ 2 * ‖μ s‖ₑ + 2 < 2 * ‖μ t‖ₑ := by
    apply exists_subset_lt_enorm_apply_of_lt_semivariation hs
    rw [h's]
    finiteness
  have h't : 1 + ‖μ s‖ₑ <= ‖μ t‖ₑ := by
    apply (ENNReal.mul_le_mul_iff_right (a := 2) (by simp) (by simp)).1
    rw [mul_add]; rw [add_comm]; rw [mul_one]
    exact ht.le
  have I : ∞ <= μ.semivariation t + μ.semivariation (s \ t) := by
    rw [← h's]
    apply le_trans (semivariation_mono (by simp)) semivariation_union_le
  simp only [top_le_iff, ENNReal.add_eq_top] at I
  rcases I with hI | hI
  · refine ⟨t, t_meas, ts, hI, ?_⟩
    have : 1 + ‖μ s‖ₑ <= ‖μ (s \ t)‖ₑ + ‖μ s‖ₑ := by
      apply h't.trans
      have : μ t = μ s - μ (s \ t) := by rw [← of_add_of_sdiff t_meas hs ts]; abel
      rw [this]; rw [add_comm]
      exact enorm_sub_le
    rwa [ENNReal.add_le_add_iff_right (by simp)] at this
  · refine ⟨s \ t, hs.diff t_meas, sdiff_subset, hI, ?_⟩
    simp only [_root_.sdiff_sdiff_right_self, ts, inf_of_le_right]
    exact le_trans (by simp) h't
-/
private lemma exists_one_le_enorm_apply_of_semivariation_eq_top
    (hs : MeasurableSet s) (h's : μ.semivariation s = ∞) :
    exists t, MeasurableSet t ∧ t subseteq s ∧ μ.semivariation t = ∞ ∧ 1 <= ‖μ (s \ t)‖ₑ := by
  obtain ⟨t, ts, t_meas, ht⟩ : exists t subseteq s, MeasurableSet t ∧ 2 * ‖μ s‖ₑ + 2 < 2 * ‖μ t‖ₑ := by
    apply exists_subset_lt_enorm_apply_of_lt_semivariation hs
    rw [h's]
    finiteness
  have h't : 1 + ‖μ s‖ₑ <= ‖μ t‖ₑ := by
    apply (ENNReal.mul_le_mul_iff_right (a := 2) (by simp) (by simp)).1
    rw [mul_add]; rw [add_comm]; rw [mul_one]
    exact ht.le
  have I : ∞ <= μ.semivariation t + μ.semivariation (s \ t) := by
    rw [← h's]
    apply le_trans (semivariation_mono (by simp)) semivariation_union_le
  simp only [top_le_iff, ENNReal.add_eq_top] at I
  rcases I with hI | hI
  · refine ⟨t, t_meas, ts, hI, ?_⟩
    have : 1 + ‖μ s‖ₑ <= ‖μ (s \ t)‖ₑ + ‖μ s‖ₑ := by
      apply h't.trans
      have : μ t = μ s - μ (s \ t) := by rw [← of_add_of_sdiff t_meas hs ts]; abel
      rw [this]; rw [add_comm]
      exact enorm_sub_le
    rwa [ENNReal.add_le_add_iff_right (by simp)] at this
  · refine ⟨s \ t, hs.diff t_meas, sdiff_subset, hI, ?_⟩
    simp only [_root_.sdiff_sdiff_right_self, ts, inf_of_le_right]
    exact le_trans (by simp) h't

/--
lemma `semivariation_univ_lt_top` / 引理 `semivariation_univ_lt_top`

English:
lemma semivariation_univ_lt_top
  statement: μ.semivariation univ < ∞
  proof: by
  apply Ne.lt_top (fun h => ?_)
  have A (s : Set X) (hs : MeasurableSet s) (h's : μ.semivariation s = ∞) :
      exists t, MeasurableSet t ∧ t subseteq s ∧ μ.semivariation t = ∞ ∧ 1 <= ‖μ (s \ t)‖ₑ :=
    exists_one_le_enorm_apply_of_semivariation_eq_top hs h's
  choose! t t_meas t_subs t_var ht using A
  let s n := t^[n] univ
  have hs n : MeasurableSet (s n) ∧ μ.semivariation (s n) = ∞ := by
    induction n with
    | zero => simp [s, h]
    | succ n ih =>
      simp only [Function.iterate_succ', Function.comp_apply, s]
      exact ⟨t_meas _ ih.1 ih.2, t_var _ ih.1 ih.2⟩
  let u n := s n \ s (n + 1)
  have hu n : 1 <= ‖μ (u n)‖ₑ := by
    simp only [Function.iterate_succ', Function.comp_apply, u, s]
    exact ht _ (hs n).1 (hs n).2
  have s_anti : Antitone s := by
    apply antitone_nat_of_succ_le (fun n => ?_)
    simp only [Function.iterate_succ', Function.comp_apply, s]
    apply t_subs _ (hs n).1 (hs n).2
  have u_disj : Pairwise (Disjoint on u) := by
    apply (pairwise_disjoint_on _).2 (fun m n hmn => ?_)
    have : Disjoint (u m) (s (m + 1)) := by simp [u, disjoint_sdiff_left]
    apply this.mono_right
    simp only [sdiff_le_iff, sup_eq_union, u]
    exact Subset.trans (s_anti (by grind)) subset_union_right
  have : HasSum (fun i => μ (u i)) (μ (⋃ i, u i)) :=
    hasSum_of_disjoint_iUnion (fun n => (hs n).1.diff (hs (n + 1)).1) u_disj
  have : Tendsto (fun x => ‖μ (u x)‖ₑ) atTop (𝓝 0) :=
    tendsto_zero_iff_enorm_tendsto_zero.1 this.summable.tendsto_atTop_zero
  obtain ⟨n, hn⟩ : exists n, ‖μ (u n)‖ₑ < 1 := ((tendsto_order.1 this).2 _ zero_lt_one).exists
  order [hu n]

中文:
引理 semivariation_univ_lt_top
  结论: μ.semivariation univ < ∞
  证明: by
  apply Ne.lt_top (fun h => ?_)
  have A (s : Set X) (hs : MeasurableSet s) (h's : μ.semivariation s = ∞) :
      exists t, MeasurableSet t ∧ t subseteq s ∧ μ.semivariation t = ∞ ∧ 1 <= ‖μ (s \ t)‖ₑ :=
    exists_one_le_enorm_apply_of_semivariation_eq_top hs h's
  choose! t t_meas t_subs t_var ht using A
  let s n := t^[n] univ
  have hs n : MeasurableSet (s n) ∧ μ.semivariation (s n) = ∞ := by
    induction n with
    | zero => simp [s, h]
    | succ n ih =>
      simp only [Function.iterate_succ', Function.comp_apply, s]
      exact ⟨t_meas _ ih.1 ih.2, t_var _ ih.1 ih.2⟩
  let u n := s n \ s (n + 1)
  have hu n : 1 <= ‖μ (u n)‖ₑ := by
    simp only [Function.iterate_succ', Function.comp_apply, u, s]
    exact ht _ (hs n).1 (hs n).2
  have s_anti : Antitone s := by
    apply antitone_nat_of_succ_le (fun n => ?_)
    simp only [Function.iterate_succ', Function.comp_apply, s]
    apply t_subs _ (hs n).1 (hs n).2
  have u_disj : Pairwise (Disjoint on u) := by
    apply (pairwise_disjoint_on _).2 (fun m n hmn => ?_)
    have : Disjoint (u m) (s (m + 1)) := by simp [u, disjoint_sdiff_left]
    apply this.mono_right
    simp only [sdiff_le_iff, sup_eq_union, u]
    exact Subset.trans (s_anti (by grind)) subset_union_right
  have : HasSum (fun i => μ (u i)) (μ (⋃ i, u i)) :=
    hasSum_of_disjoint_iUnion (fun n => (hs n).1.diff (hs (n + 1)).1) u_disj
  have : Tendsto (fun x => ‖μ (u x)‖ₑ) atTop (𝓝 0) :=
    tendsto_zero_iff_enorm_tendsto_zero.1 this.summable.tendsto_atTop_zero
  obtain ⟨n, hn⟩ : exists n, ‖μ (u n)‖ₑ < 1 := ((tendsto_order.1 this).2 _ zero_lt_one).exists
  order [hu n]
-/
private lemma semivariation_univ_lt_top : μ.semivariation univ < ∞ := by
  apply Ne.lt_top (fun h => ?_)
  have A (s : Set X) (hs : MeasurableSet s) (h's : μ.semivariation s = ∞) :
      exists t, MeasurableSet t ∧ t subseteq s ∧ μ.semivariation t = ∞ ∧ 1 <= ‖μ (s \ t)‖ₑ :=
    exists_one_le_enorm_apply_of_semivariation_eq_top hs h's
  choose! t t_meas t_subs t_var ht using A
  let s n := t^[n] univ
  have hs n : MeasurableSet (s n) ∧ μ.semivariation (s n) = ∞ := by
    induction n with
    | zero => simp [s, h]
    | succ n ih =>
      simp only [Function.iterate_succ', Function.comp_apply, s]
      exact ⟨t_meas _ ih.1 ih.2, t_var _ ih.1 ih.2⟩
  let u n := s n \ s (n + 1)
  have hu n : 1 <= ‖μ (u n)‖ₑ := by
    simp only [Function.iterate_succ', Function.comp_apply, u, s]
    exact ht _ (hs n).1 (hs n).2
  have s_anti : Antitone s := by
    apply antitone_nat_of_succ_le (fun n => ?_)
    simp only [Function.iterate_succ', Function.comp_apply, s]
    apply t_subs _ (hs n).1 (hs n).2
  have u_disj : Pairwise (Disjoint on u) := by
    apply (pairwise_disjoint_on _).2 (fun m n hmn => ?_)
    have : Disjoint (u m) (s (m + 1)) := by simp [u, disjoint_sdiff_left]
    apply this.mono_right
    simp only [sdiff_le_iff, sup_eq_union, u]
    exact Subset.trans (s_anti (by grind)) subset_union_right
  have : HasSum (fun i => μ (u i)) (μ (⋃ i, u i)) :=
    hasSum_of_disjoint_iUnion (fun n => (hs n).1.diff (hs (n + 1)).1) u_disj
  have : Tendsto (fun x => ‖μ (u x)‖ₑ) atTop (𝓝 0) :=
    tendsto_zero_iff_enorm_tendsto_zero.1 this.summable.tendsto_atTop_zero
  obtain ⟨n, hn⟩ : exists n, ‖μ (u n)‖ₑ < 1 := ((tendsto_order.1 this).2 _ zero_lt_one).exists
  order [hu n]

variable (μ) in
/--
Definition of `noncomputable` / `noncomputable` 的定义

English:
definition noncomputable
  signature: def bound
  body: (μ.semivariation univ).toNNReal

中文:
定义 noncomputable
  签名: def bound
  定义体: (μ.semivariation univ).toNNReal
-/
protected noncomputable def bound : Real>=0 := (μ.semivariation univ).toNNReal

/--
lemma `semivariation_apply_le_bound` / 引理 `semivariation_apply_le_bound`

English:
lemma semivariation_apply_le_bound
  statement: μ.semivariation s <= μ.bound
  proof: by
  apply (semivariation_mono (subset_univ _)).trans_eq
  simp only [VectorMeasure.bound]
  rw [ENNReal.coe_toNNReal semivariation_univ_lt_top.ne]

中文:
引理 semivariation_apply_le_bound
  结论: μ.semivariation s <= μ.bound
  证明: by
  apply (semivariation_mono (subset_univ _)).trans_eq
  simp only [VectorMeasure.bound]
  rw [ENNReal.coe_toNNReal semivariation_univ_lt_top.ne]

Depends on / 依赖: ENNReal, ENNReal.coe_toNNReal, VectorMeasure, VectorMeasure.bound, coe_toNNReal, semivariation_mono, semivariation_univ_lt_top, semivariation_univ_lt_top.ne, subset_univ, trans_eq
-/
lemma semivariation_apply_le_bound : μ.semivariation s <= μ.bound := by
  apply (semivariation_mono (subset_univ _)).trans_eq
  simp only [VectorMeasure.bound]
  rw [ENNReal.coe_toNNReal semivariation_univ_lt_top.ne]

/--
lemma `enorm_apply_le_bound` / 引理 `enorm_apply_le_bound`

English:
lemma enorm_apply_le_bound
  statement: ‖μ s‖ₑ <= μ.bound
  proof: (enorm_apply_le_semivariation).trans semivariation_apply_le_bound

中文:
引理 enorm_apply_le_bound
  结论: ‖μ s‖ₑ <= μ.bound
  证明: (enorm_apply_le_semivariation).trans semivariation_apply_le_bound

Depends on / 依赖: enorm_apply_le_semivariation, semivariation_apply_le_bound
-/
lemma enorm_apply_le_bound : ‖μ s‖ₑ <= μ.bound :=
  (enorm_apply_le_semivariation).trans semivariation_apply_le_bound

/--
lemma `nnnorm_apply_le_bound` / 引理 `nnnorm_apply_le_bound`

English:
lemma nnnorm_apply_le_bound
  statement: ‖μ s‖₊ <= μ.bound
  proof: by
  rw [← ENNReal.coe_le_coe]; rw [← enorm_eq_nnnorm]
  exact enorm_apply_le_bound

中文:
引理 nnnorm_apply_le_bound
  结论: ‖μ s‖₊ <= μ.bound
  证明: by
  rw [← ENNReal.coe_le_coe]; rw [← enorm_eq_nnnorm]
  exact enorm_apply_le_bound

Depends on / 依赖: ENNReal, ENNReal.coe_le_coe, coe_le_coe, enorm_apply_le_bound, enorm_eq_nnnorm
-/
lemma nnnorm_apply_le_bound : ‖μ s‖₊ <= μ.bound := by
  rw [← ENNReal.coe_le_coe]; rw [← enorm_eq_nnnorm]
  exact enorm_apply_le_bound

/--
lemma `norm_apply_le_bound` / 引理 `norm_apply_le_bound`

English:
lemma norm_apply_le_bound
  statement: ‖μ s‖ <= μ.bound
  proof: by
  simpa [← coe_nnnorm] using nnnorm_apply_le_bound

中文:
引理 norm_apply_le_bound
  结论: ‖μ s‖ <= μ.bound
  证明: by
  simpa [← coe_nnnorm] using nnnorm_apply_le_bound

Depends on / 依赖: coe_nnnorm, nnnorm_apply_le_bound
-/
lemma norm_apply_le_bound : ‖μ s‖ <= μ.bound := by
  simpa [← coe_nnnorm] using nnnorm_apply_le_bound

end MeasureTheory.VectorMeasure
