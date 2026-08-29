/-
Copyright (c) 2026 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
public import Mathlib.MeasureTheory.SetSemiring
import Mathlib.Topology.MetricSpace.Lipschitz

/-!
# Measured sets

Consider a measure `μ` on a measurable space. One can define an extended distance on the space
of measurable sets, by `edist s t := μ (s ∆ t)`. In this file, we introduce this definition
on the type synonym `MeasuredSets μ`, and we prove that `μ` is a continuous function on this space.

We also give a density criterion for this distance,
in `exists_measure_symmDiff_lt_of_generateFrom_isSetRing`: given a ring of sets `C` covering the
space modulo `0` and generating the measurable space structure, then any measurable set can be
approximated by elements of `C`.
Note that the covering condition is necessary: for a counterexample otherwise, take `{0, 1}` with
the counting measure and `C = {∅, {0}}`. Then the set `{1}` can not be approximated by
an element of `C`.
-/

@[expose] public section

open MeasurableSpace Set Filter
open scoped symmDiff ENNReal Topology

namespace MeasureTheory

variable {α : Type*} [mα : MeasurableSpace α] {μ : Measure α}

set_option linter.unusedVariables false in
/-- The subtype of all measurable sets. We denote it as `MeasuredSets μ`, with an explicit but
unused parameter `μ`, to be able to define a distance on it given by `edist s t = μ (s ∆ t)` -/
@[nolint unusedArguments]
/--
Definition of `MeasuredSets` / `MeasuredSets` 的定义

English:
definition MeasuredSets
  signature: (μ : Measure α)
  body: {s : Set α // MeasurableSet s}

中文:
定义 MeasuredSets
  签名: (μ : 测度 α)
  定义体: {s : Set α // MeasurableSet s}

Depends on / 依赖: MeasurableSet
-/
def MeasuredSets (μ : Measure α) : Type _ := {s : Set α // MeasurableSet s}

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SetLike (MeasuredSets μ) α
  body: s.1
  coe_injective := Subtype.coe_injective

中文:
实例 :
  签名: 集合状 (MeasuredSets μ) α
  定义体: s.1
  coe_injective := Subtype.coe_injective
-/
instance : SetLike (MeasuredSets μ) α where
  coe s := s.1
  coe_injective := Subtype.coe_injective

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PseudoEMetricSpace (MeasuredSets μ)
  body: μ ((s : Set α) ∆ t)
  edist_self := by simp
  edist_comm := by grind
  edist_triangle s t u := measure_symmDiff_le _ _ _

中文:
实例 :
  签名: PseudoEMetric空间 (MeasuredSets μ)
  定义体: μ ((s : Set α) ∆ t)
  edist_self := by simp
  edist_comm := by grind
  edist_triangle s t u := measure_symmDiff_le _ _ _
-/
noncomputable instance : PseudoEMetricSpace (MeasuredSets μ) where
  edist s t := μ ((s : Set α) ∆ t)
  edist_self := by simp
  edist_comm := by grind
  edist_triangle s t u := measure_symmDiff_le _ _ _

/--
lemma `MeasuredSets.edist_def` / 引理 `MeasuredSets.edist_def`

English:
lemma MeasuredSets.edist_def
  given: (s t : MeasuredSets μ)
  statement: edist s t = μ ((s : Set α) ∆ t)
  proof: rfl

中文:
引理 MeasuredSets.edist_def
  条件: (s t : MeasuredSets μ)
  结论: edist s t = μ ((s : 集合 α) ∆ t)
  证明: rfl
-/
lemma MeasuredSets.edist_def (s t : MeasuredSets μ) : edist s t = μ ((s : Set α) ∆ t) := rfl

/--
lemma `MeasuredSets.sub_le_edist` / 引理 `MeasuredSets.sub_le_edist`

English:
lemma MeasuredSets.sub_le_edist
  given: (s t : MeasuredSets μ)
  statement: μ s - μ t <= edist s t
  proof: le_measure_sdiff.trans measure_mono subset_union_left

中文:
引理 MeasuredSets.sub_le_edist
  条件: (s t : MeasuredSets μ)
  结论: μ s - μ t <= edist s t
  证明: le_measure_sdiff.trans measure_mono subset_union_left

Depends on / 依赖: le_measure_sdiff, le_measure_sdiff.trans, measure_mono, subset_union_left
-/
lemma MeasuredSets.sub_le_edist (s t : MeasuredSets μ) : μ s - μ t <= edist s t :=
le_measure_sdiff.trans measure_mono subset_union_left

/--
lemma `MeasuredSets.continuous_measure` / 引理 `MeasuredSets.continuous_measure`

English:
lemma MeasuredSets.continuous_measure
  statement: Continuous (fun (s : MeasuredSets μ) => μ s)
  proof: by
  refine continuous_of_le_add_edist 1 ENNReal.one_ne_top fun s t => ?_
  rw [one_mul]; rw [← tsub_le_iff_left]
  exact sub_le_edist s t

中文:
引理 MeasuredSets.continuous_measure
  结论: 连续 (fun (s : MeasuredSets μ) => μ s)
  证明: by
  refine continuous_of_le_add_edist 1 ENNReal.one_ne_top fun s t => ?_
  rw [one_mul]; rw [← tsub_le_iff_left]
  exact sub_le_edist s t

Depends on / 依赖: ENNReal, ENNReal.one_ne_top, continuous_of_le_add_edist, one_mul, one_ne_top, sub_le_edist, tsub_le_iff_left
-/
lemma MeasuredSets.continuous_measure : Continuous (fun (s : MeasuredSets μ) => μ s) := by
  refine continuous_of_le_add_edist 1 ENNReal.one_ne_top fun s t => ?_
  rw [one_mul]; rw [← tsub_le_iff_left]
  exact sub_le_edist s t

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsFiniteMeasure
  signature: μ] : PseudoMetricSpace (MeasuredSets μ)
  body: PseudoEMetricSpace.toPseudoMetricSpaceOfDist
    (fun s t => μ.real ((s : Set α) ∆ t)) (fun s t => ENNReal.toReal_nonneg)
    (fun s t => by simp [Measure.real, MeasuredSets.edist_def])

中文:
实例 [是有限测度
  签名: μ] : 伪度量空间 (MeasuredSets μ)
  定义体: PseudoEMetricSpace.toPseudoMetricSpaceOfDist
    (fun s t => μ.real ((s : Set α) ∆ t)) (fun s t => ENNReal.toReal_nonneg)
    (fun s t => by simp [Measure.real, MeasuredSets.edist_def])

Depends on / 依赖: ENNReal, ENNReal.toReal_nonneg, Measure, Measure.real, MeasuredSets, MeasuredSets.edist_def, PseudoEMetricSpace, PseudoEMetricSpace.toPseudoMetricSpaceOfDist, edist_def, toPseudoMetricSpaceOfDist, toReal_nonneg
-/
noncomputable instance [IsFiniteMeasure μ] : PseudoMetricSpace (MeasuredSets μ) :=
  PseudoEMetricSpace.toPseudoMetricSpaceOfDist
    (fun s t => μ.real ((s : Set α) ∆ t)) (fun s t => ENNReal.toReal_nonneg)
    (fun s t => by simp [Measure.real, MeasuredSets.edist_def])

/--
lemma `MeasuredSets.dist_def` / 引理 `MeasuredSets.dist_def`

English:
lemma MeasuredSets.dist_def
  given: [IsFiniteMeasure μ] (s t : MeasuredSets μ)
  proof: rfl

中文:
引理 MeasuredSets.dist_def
  条件: [是有限测度 μ] (s t : MeasuredSets μ)
  证明: rfl
-/
lemma MeasuredSets.dist_def [IsFiniteMeasure μ] (s t : MeasuredSets μ) :
    dist s t = μ.real ((s : Set α) ∆ t) := rfl

/--
lemma `MeasuredSets.real_sub_real_le_dist` / 引理 `MeasuredSets.real_sub_real_le_dist`

English:
lemma MeasuredSets.real_sub_real_le_dist
  given: [IsFiniteMeasure μ] (s t : MeasuredSets μ)
  proof: by
  grw [dist_edist, ← sub_le_edist]
  exacts [ENNReal.le_toReal_sub (measure_ne_top _ _), edist_ne_top _ _]

中文:
引理 MeasuredSets.real_sub_real_le_dist
  条件: [是有限测度 μ] (s t : MeasuredSets μ)
  证明: by
  grw [dist_edist, ← sub_le_edist]
  exacts [ENNReal.le_toReal_sub (measure_ne_top _ _), edist_ne_top _ _]

Depends on / 依赖: ENNReal, ENNReal.le_toReal_sub, dist_edist, edist_ne_top, exacts, le_toReal_sub, measure_ne_top, sub_le_edist
-/
lemma MeasuredSets.real_sub_real_le_dist [IsFiniteMeasure μ] (s t : MeasuredSets μ) :
    μ.real s - μ.real t <= dist s t := by
  grw [dist_edist, ← sub_le_edist]
  exacts [ENNReal.le_toReal_sub (measure_ne_top _ _), edist_ne_top _ _]

/--
lemma `MeasuredSets.lipschitzWith_measureReal` / 引理 `MeasuredSets.lipschitzWith_measureReal`

English:
lemma MeasuredSets.lipschitzWith_measureReal
  given: [IsFiniteMeasure μ]
  proof: .of_le_add fun s t => sub_le_iff_le_add'.mp real_sub_real_le_dist s t

中文:
引理 MeasuredSets.lipschitzWith_measure实数
  条件: [是有限测度 μ]
  证明: .of_le_add fun s t => sub_le_iff_le_add'.mp real_sub_real_le_dist s t

Depends on / 依赖: of_le_add, real_sub_real_le_dist, sub_le_iff_le_add
-/
lemma MeasuredSets.lipschitzWith_measureReal [IsFiniteMeasure μ] :
    LipschitzWith 1 (fun s : MeasuredSets μ => μ.real s) :=
.of_le_add fun s t => sub_le_iff_le_add'.mp real_sub_real_le_dist s t

/--
lemma `exists_measure_symmDiff_lt_of_generateFrom_isSetRing` / 引理 `exists_measure_symmDiff_lt_of_generateFrom_isSetRing`

English:
lemma exists_measure_symmDiff_lt_of_generateFrom_isSetRing
  statement: [IsFiniteMeasure μ]
  proof: by
  /- We check that the set of sets satisfying the conclusion of the lemma for all positive
  `ε` contains `C` and is stable under complement and disjoint union. It follows that it is
  all the sigma-algebra, as desired. -/
  apply MeasurableSpace.induction_on_inter (C := fun s hs => forall (ε : R

中文:
引理 存在_measure_symmDiff_lt_of_generateFrom_isSetRing
  结论: [是有限测度 μ]
  证明: by
  /- We check that the set of sets satisfying the conclusion of the lemma for all positive
  `ε` contains `C` and is stable under complement and disjoint union. It follows that it is
  all the sigma-algebra, as desired. -/
  apply MeasurableSpace.induction_on_inter (C := fun s hs => forall (ε : R
-/
lemma exists_measure_symmDiff_lt_of_generateFrom_isSetRing [IsFiniteMeasure μ]
    {C : Set (Set α)} (hC : IsSetRing C)
    (h'C : exists D : Set (Set α), D.Countable ∧ D subseteq C ∧ μ (⋃₀ D)ᶜ = 0) (h : mα = generateFrom C)
    {s : Set α} (hs : MeasurableSet s) {ε : Real>=0∞} (hε : 0 < ε) :
    exists t in C, μ (t ∆ s) < ε := by
  /- We check that the set of sets satisfying the conclusion of the lemma for all positive
  `ε` contains `C` and is stable under complement and disjoint union. It follows that it is
  all the sigma-algebra, as desired. -/
  apply MeasurableSpace.induction_on_inter (C := fun s hs => forall (ε : Real>=0∞) (hε : 0 < ε),
    exists t in C, μ (t ∆ s) < ε) h hC.isSetSemiring.isPiSystem ?_ ?_ ?_ ?_ s hs ε hε
  · intro ε εpos
    exact ⟨∅, hC.empty_mem, by simp [εpos]⟩
  · intro s hs ε εpos
    exact ⟨s, hs, by simp [εpos]⟩
  · /- To check the stability under complement, we use the condition `h'C` which guarantees
    that the space is almost an element of `C`. If `t` approximates `s`, then `univ \ t`
    approximates well `sᶜ`, and therefore `t' \ t` approximates well `sᶜ` when `t'` is a good
    enough approximation to `univ`. As `t' \ t` belongs to `C` when `t` and `t'` do, this
    concludes this step. -/
    intro s hs h's ε εpos
    obtain ⟨t, tC, ht⟩ : exists t in C, μ (t ∆ s) < ε / 2 := h's _ (ENNReal.half_pos εpos.ne')
    obtain ⟨t', t'C, ht'⟩ : exists t' in C, μ (t'ᶜ) < ε / 2 := by
      obtain ⟨D, D_count, DC, hD, Dne⟩ :
          exists D : Set (Set α), D.Countable ∧ D subseteq C ∧ μ (⋃₀ D)ᶜ = 0 ∧ D.Nonempty := by
        rcases h'C with ⟨D, D_count, DC, hD⟩
        refine ⟨D union {∅}, D_count.union (by simp), ?_⟩
        simp only [union_subset_iff, DC, singleton_subset_iff, true_and, and_true, hC.empty_mem]
        simp only [union_singleton, sUnion_insert, empty_union, insert_nonempty, and_true, hD]
      obtain ⟨f, hf⟩ : exists f : Nat -> Set α, D = Set.range f := Set.Countable.exists_eq_range D_count Dne
      have fC n : Set.accumulate f n in C := hC.accumulate_mem (fun n => DC (by simp [hf])) n
      have : Tendsto (fun n => μ (Set.accumulate f n)ᶜ) atTop (𝓝 0) := by
        have : ⋃₀ D = ⋃ n, Set.accumulate f n := by simp [hf, iUnion_accumulate]
        rw [show (⋃₀ D)ᶜ = ⋂ n]; rw [(Set.accumulate f n)ᶜ by simp [this]; rw [accumulate]] at hD
        rw [← hD]
        apply tendsto_measure_iInter_atTop (fun i => ?_)
          (fun i j hij => by simpa using monotone_accumulate hij) ⟨0, by simp⟩
        apply MeasurableSet.nullMeasurableSet
        rw [h]
        exact (measurableSet_generateFrom (fC i)).compl
      obtain ⟨n, hn⟩ : exists n, μ (accumulate f n)ᶜ < ε / 2 :=
        ((tendsto_order.1 this).2 _ (ENNReal.half_pos εpos.ne')).exists
      exact ⟨accumulate f n, fC n, hn⟩
    refine ⟨t' \ t, hC.sdiff_mem t'C tC, ?_⟩
    calc μ ((t' \ t) ∆ sᶜ)
      _ <= μ (t ∆ s union t'ᶜ) := by gcongr; grind
      _ <= μ (t ∆ s) + μ (t'ᶜ) := measure_union_le _ _
      _ < ε / 2 + ε / 2 := by gcongr
      _ = ε := ENNReal.add_halves ε
  · /- To check the stability under disjoint union, approximate `f n` by a set `t n ∈ C`. Then
    `⋃ i, f i` is well approximated by `U i < n, f i` for large enough `n`, which is itself
    well approximated by `⋃ i < n, t i`. As this set belongs to `C`, this concludes this step. -/
    intro f f_disj f_meas hf ε εpos
    rcases ENNReal.exists_pos_sum_of_countable' (ENNReal.half_pos εpos.ne').ne' Nat with ⟨δ, δpos, hδ⟩
    have A i : exists t in C, μ (t ∆ (f i)) < δ i := hf i _ (δpos i)
    choose! t tC ht using A
    have : Tendsto (fun n => μ (⋃ i in Ici n, f i)) atTop (𝓝 0) :=
      tendsto_measure_biUnion_Ici_zero_of_pairwise_disjoint
        (fun i => (f_meas i).nullMeasurableSet) f_disj
    obtain ⟨n, hn⟩ : exists n, μ (⋃ i in Ici n, f i) < ε / 2 :=
      ((tendsto_order.1 this).2 _ (ENNReal.half_pos εpos.ne')).exists
    refine ⟨⋃ i in Finset.range n, t i, hC.biUnion_mem _ (fun i hi => tC _), ?_⟩
    calc μ ((⋃ i in Finset.range n, t i) ∆ (⋃ i, f i))
    _ <= μ ((⋃ i in Finset.range n, (t i) ∆ (f i)) union ⋃ i in Ici n, f i) := by
      gcongr
      intro x hx
      simp only [Finset.mem_range, mem_symmDiff, mem_iUnion, exists_prop, not_exists, not_and,
        mem_Ici, mem_union] at hx ⊢
      grind
    _ <= ∑ i in Finset.range n, μ (t i ∆ f i) + μ (⋃ i in Ici n, f i) := by
      apply (measure_union_le _ _).trans
      gcongr
      apply measure_biUnion_finset_le
    _ <= ∑ i in Finset.range n, δ i + μ (⋃ i in Ici n, f i) := by
      gcongr with i; exact (ht i).le
    _ <= ∑' i, δ i + μ (⋃ i in Ici n, f i) := by
      gcongr; exact ENNReal.sum_le_tsum (Finset.range n)
    _ < ε / 2 + ε / 2 := by gcongr
    _ = ε := ENNReal.add_halves ε

/--
lemma `exists_measure_symmDiff_lt_of_generateFrom_isSetSemiring` / 引理 `exists_measure_symmDiff_lt_of_generateFrom_isSetSemiring`

English:
lemma exists_measure_symmDiff_lt_of_generateFrom_isSetSemiring
  statement: [IsFiniteMeasure μ]
  proof: by
  apply exists_measure_symmDiff_lt_of_generateFrom_isSetRing hC.isSetRing_supClosure ?_ ?_ hs hε
  · rcases h'C with ⟨D, D_count, DC, hD⟩
    exact ⟨D, D_count, DC.trans subset_supClosure, hD⟩
  · rw [h]
    apply le_antisymm (generateFrom_mono subset_supClosure)
    apply generateFrom_le (fun t 

中文:
引理 存在_measure_symmDiff_lt_of_generateFrom_isSetSemiring
  结论: [是有限测度 μ]
  证明: by
  apply exists_measure_symmDiff_lt_of_generateFrom_isSetRing hC.isSetRing_supClosure ?_ ?_ hs hε
  · rcases h'C with ⟨D, D_count, DC, hD⟩
    exact ⟨D, D_count, DC.trans subset_supClosure, hD⟩
  · rw [h]
    apply le_antisymm (generateFrom_mono subset_supClosure)
    apply generateFrom_le (fun t 

Depends on / 依赖: DC.trans, D_count, exists_measure_symmDiff_lt_of_generateFrom_isSetRing, generateFrom_le, generateFrom_mono, hC.isSetRing_supClosure, isSetRing_supClosure, le_antisymm, measurableSet_generateFrom_of_mem_supClosure, subset_supClosure
-/
lemma exists_measure_symmDiff_lt_of_generateFrom_isSetSemiring [IsFiniteMeasure μ]
    {C : Set (Set α)} (hC : IsSetSemiring C)
    (h'C : exists D : Set (Set α), D.Countable ∧ D subseteq C ∧ μ (⋃₀ D)ᶜ = 0) (h : mα = generateFrom C)
    {s : Set α} (hs : MeasurableSet s) {ε : Real>=0∞} (hε : 0 < ε) :
    exists t in supClosure C, μ (t ∆ s) < ε := by
  apply exists_measure_symmDiff_lt_of_generateFrom_isSetRing hC.isSetRing_supClosure ?_ ?_ hs hε
  · rcases h'C with ⟨D, D_count, DC, hD⟩
    exact ⟨D, D_count, DC.trans subset_supClosure, hD⟩
  · rw [h]
    apply le_antisymm (generateFrom_mono subset_supClosure)
    apply generateFrom_le (fun t ht => ?_)
    apply measurableSet_generateFrom_of_mem_supClosure ht

/--
lemma `dense_of_generateFrom_isSetRing` / 引理 `dense_of_generateFrom_isSetRing`

English:
lemma dense_of_generateFrom_isSetRing
  statement: [IsFiniteMeasure μ]
  proof: by
  rw [EMetric.dense_iff]
  rintro s ε εpos
  rcases exists_measure_symmDiff_lt_of_generateFrom_isSetRing hC h'C h s.2 εpos with ⟨t, tC, ht⟩
  have t_meas : MeasurableSet t := by rw [h]; exact measurableSet_generateFrom tC
  refine ⟨⟨t, t_meas⟩, ?_, tC⟩
  simpa [MeasuredSets.edist_def] using! ht

中文:
引理 dense_of_generateFrom_isSetRing
  结论: [是有限测度 μ]
  证明: by
  rw [EMetric.dense_iff]
  rintro s ε εpos
  rcases exists_measure_symmDiff_lt_of_generateFrom_isSetRing hC h'C h s.2 εpos with ⟨t, tC, ht⟩
  have t_meas : MeasurableSet t := by rw [h]; exact measurableSet_generateFrom tC
  refine ⟨⟨t, t_meas⟩, ?_, tC⟩
  simpa [MeasuredSets.edist_def] using! ht

Depends on / 依赖: EMetric, EMetric.dense_iff, MeasurableSet, MeasuredSets, MeasuredSets.edist_def, dense_iff, edist_def, exists_measure_symmDiff_lt_of_generateFrom_isSetRing, measurableSet_generateFrom, t_meas
-/
lemma dense_of_generateFrom_isSetRing [IsFiniteMeasure μ]
    {C : Set (Set α)} (hC : IsSetRing C)
    (h'C : exists D : Set (Set α), D.Countable ∧ D subseteq C ∧ μ (⋃₀ D)ᶜ = 0) (h : mα = generateFrom C) :
    Dense ((SetLike.coe : MeasuredSets μ -> Set α) ⁻¹' C) := by
  rw [EMetric.dense_iff]
  rintro s ε εpos
  rcases exists_measure_symmDiff_lt_of_generateFrom_isSetRing hC h'C h s.2 εpos with ⟨t, tC, ht⟩
  have t_meas : MeasurableSet t := by rw [h]; exact measurableSet_generateFrom tC
  refine ⟨⟨t, t_meas⟩, ?_, tC⟩
  simpa [MeasuredSets.edist_def] using! ht

/--
lemma `dense_of_generateFrom_isSetSemiring` / 引理 `dense_of_generateFrom_isSetSemiring`

English:
lemma dense_of_generateFrom_isSetSemiring
  statement: [IsFiniteMeasure μ]
  proof: by
  rw [EMetric.dense_iff]
  rintro s ε εpos
  rcases exists_measure_symmDiff_lt_of_generateFrom_isSetSemiring hC h'C h s.2 εpos
    with ⟨t, tC, ht⟩
  refine ⟨⟨t, ?_⟩, by simpa [MeasuredSets.edist_def] using! ht, tC⟩
  rw [h]
  exact measurableSet_generateFrom_of_mem_supClosure tC

中文:
引理 dense_of_generateFrom_isSetSemiring
  结论: [是有限测度 μ]
  证明: by
  rw [EMetric.dense_iff]
  rintro s ε εpos
  rcases exists_measure_symmDiff_lt_of_generateFrom_isSetSemiring hC h'C h s.2 εpos
    with ⟨t, tC, ht⟩
  refine ⟨⟨t, ?_⟩, by simpa [MeasuredSets.edist_def] using! ht, tC⟩
  rw [h]
  exact measurableSet_generateFrom_of_mem_supClosure tC

Depends on / 依赖: EMetric, EMetric.dense_iff, MeasuredSets, MeasuredSets.edist_def, dense_iff, edist_def, exists_measure_symmDiff_lt_of_generateFrom_isSetSemiring, measurableSet_generateFrom_of_mem_supClosure
-/
lemma dense_of_generateFrom_isSetSemiring [IsFiniteMeasure μ]
    {C : Set (Set α)} (hC : IsSetSemiring C)
    (h'C : exists D : Set (Set α), D.Countable ∧ D subseteq C ∧ μ (⋃₀ D)ᶜ = 0) (h : mα = generateFrom C) :
    Dense ((SetLike.coe : MeasuredSets μ -> Set α) ⁻¹' (supClosure C)) := by
  rw [EMetric.dense_iff]
  rintro s ε εpos
  rcases exists_measure_symmDiff_lt_of_generateFrom_isSetSemiring hC h'C h s.2 εpos
    with ⟨t, tC, ht⟩
  refine ⟨⟨t, ?_⟩, by simpa [MeasuredSets.edist_def] using! ht, tC⟩
  rw [h]
  exact measurableSet_generateFrom_of_mem_supClosure tC

end MeasureTheory
