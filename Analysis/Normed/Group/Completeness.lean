/-
Copyright (c) 2023 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/
module

public import Mathlib.Analysis.Normed.Group.Uniform
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Completeness of normed groups

This file includes a completeness criterion for normed additive groups in terms of convergent
series.

## Main results

* `NormedAddCommGroup.completeSpace_of_summable_imp_tendsto`: A normed additive group is
  complete if any absolutely convergent series converges in the space.

## References

* [bergh_lofstrom_1976] `NormedAddCommGroup.completeSpace_of_summable_imp_tendsto` and
  `NormedAddCommGroup.summable_imp_tendsto_of_complete` correspond to the two directions of
  Lemma 2.2.1.

## Tags

CompleteSpace, CauchySeq
-/

public section

open scoped Topology
open Filter Finset

section Metric

variable {α : Type*} [PseudoMetricSpace α]

/--
lemma `Metric.exists_subseq_summable_dist_of_cauchySeq` / 引理 `Metric.exists_subseq_summable_dist_of_cauchySeq`

English:
lemma Metric.exists_subseq_summable_dist_of_cauchySeq
  given: (u : Nat -> α) (hu : CauchySeq u)
  proof: by
  obtain ⟨f, hf₁, hf₂⟩ := Metric.exists_subseq_bounded_of_cauchySeq u hu
    (fun n => (1 / (2 : Real)) ^ n) (fun n => by positivity)
  refine ⟨f, hf₁, ?_⟩
  refine Summable.of_nonneg_of_le (fun n => by positivity) ?_ summable_geometric_two
exact fun n => le_of_lt hf₂ n (f (n + 1)) hf₁.monotone (

中文:
引理 Metric.存在_subseq_summable_dist_of_cauchySeq
  条件: (u : 自然数 -> α) (hu : CauchySeq u)
  证明: by
  obtain ⟨f, hf₁, hf₂⟩ := Metric.exists_subseq_bounded_of_cauchySeq u hu
    (fun n => (1 / (2 : Real)) ^ n) (fun n => by positivity)
  refine ⟨f, hf₁, ?_⟩
  refine Summable.of_nonneg_of_le (fun n => by positivity) ?_ summable_geometric_two
exact fun n => le_of_lt hf₂ n (f (n + 1)) hf₁.monotone (

Depends on / 依赖: Metric, Metric.exists_subseq_bounded_of_cauchySeq, Nat.le_add_right, Summable, Summable.of_nonneg_of_le, exists_subseq_bounded_of_cauchySeq, le_add_right, le_of_lt, monotone, of_nonneg_of_le, summable_geometric_two
-/
lemma Metric.exists_subseq_summable_dist_of_cauchySeq (u : Nat -> α) (hu : CauchySeq u) :
    exists f : Nat -> Nat, StrictMono f ∧ Summable fun i => dist (u (f (i + 1))) (u (f i)) := by
  obtain ⟨f, hf₁, hf₂⟩ := Metric.exists_subseq_bounded_of_cauchySeq u hu
    (fun n => (1 / (2 : Real)) ^ n) (fun n => by positivity)
  refine ⟨f, hf₁, ?_⟩
  refine Summable.of_nonneg_of_le (fun n => by positivity) ?_ summable_geometric_two
exact fun n => le_of_lt hf₂ n (f (n + 1)) hf₁.monotone (Nat.le_add_right n 1)

end Metric

section Normed

variable {E : Type*} [NormedAddCommGroup E]

/--
lemma `NormedAddCommGroup.completeSpace_of_summable_imp_tendsto` / 引理 `NormedAddCommGroup.completeSpace_of_summable_imp_tendsto`

English:
lemma NormedAddCommGroup.completeSpace_of_summable_imp_tendsto
  proof: by
  apply Metric.complete_of_cauchySeq_tendsto
  intro u hu
  obtain ⟨f, hf₁, hf₂⟩ := Metric.exists_subseq_summable_dist_of_cauchySeq u hu
  simp only [dist_eq_norm] at hf₂
  let v n := u (f (n + 1)) - u (f n)
  have hv_sum : (fun n => (∑ i in range n, v i)) = fun n => u (f n) - u (f 0) := by
    e

中文:
引理 赋范交换加群.completeSpace_of_summable_imp_tendsto
  证明: by
  apply Metric.complete_of_cauchySeq_tendsto
  intro u hu
  obtain ⟨f, hf₁, hf₂⟩ := Metric.exists_subseq_summable_dist_of_cauchySeq u hu
  simp only [dist_eq_norm] at hf₂
  let v n := u (f (n + 1)) - u (f n)
  have hv_sum : (fun n => (∑ i in range n, v i)) = fun n => u (f n) - u (f 0) := by
    e

Depends on / 依赖: Metric, Metric.complete_of_cauchySeq_tendsto, Metric.exists_subseq_summable_dist_of_cauchySeq, Tendsto, complete_of_cauchySeq_tendsto, dist_eq_norm, exists_subseq_summable_dist_of_cauchySeq, hv_sum, sum_range_sub, tendsto_atTop, tendsto_nhds_of_cauchySeq_of_subseq
-/
lemma NormedAddCommGroup.completeSpace_of_summable_imp_tendsto
    (h : forall u : Nat -> E,
      Summable (‖u ·‖) -> exists a, Tendsto (fun n => ∑ i in range n, u i) atTop (𝓝 a)) :
    CompleteSpace E := by
  apply Metric.complete_of_cauchySeq_tendsto
  intro u hu
  obtain ⟨f, hf₁, hf₂⟩ := Metric.exists_subseq_summable_dist_of_cauchySeq u hu
  simp only [dist_eq_norm] at hf₂
  let v n := u (f (n + 1)) - u (f n)
  have hv_sum : (fun n => (∑ i in range n, v i)) = fun n => u (f n) - u (f 0) := by
    ext n
    exact sum_range_sub (u ∘ f) n
  obtain ⟨a, ha⟩ := h v hf₂
  refine ⟨a + u (f 0), ?_⟩
  refine tendsto_nhds_of_cauchySeq_of_subseq hu hf₁.tendsto_atTop ?_
  rw [hv_sum] at ha
  have h₁ : Tendsto (fun n => u (f n) - u (f 0) + u (f 0)) atTop (𝓝 (a + u (f 0))) :=
    Tendsto.add_const _ ha
  simpa only [sub_add_cancel] using! h₁

/--
lemma `NormedAddCommGroup.summable_imp_tendsto_of_complete` / 引理 `NormedAddCommGroup.summable_imp_tendsto_of_complete`

English:
lemma NormedAddCommGroup.summable_imp_tendsto_of_complete
  statement: [CompleteSpace E] (u : Nat -> E)
  proof: by
refine cauchySeq_tendsto_of_complete cauchySeq_of_summable_dist ?_
  simp [dist_eq_norm, sum_range_succ, hu]

中文:
引理 赋范交换加群.summable_imp_tendsto_of_complete
  结论: [完备空间 E] (u : 自然数 -> E)
  证明: by
refine cauchySeq_tendsto_of_complete cauchySeq_of_summable_dist ?_
  simp [dist_eq_norm, sum_range_succ, hu]

Depends on / 依赖: cauchySeq_of_summable_dist, cauchySeq_tendsto_of_complete, dist_eq_norm, sum_range_succ
-/
lemma NormedAddCommGroup.summable_imp_tendsto_of_complete [CompleteSpace E] (u : Nat -> E)
    (hu : Summable (‖u ·‖)) : exists a, Tendsto (fun n => ∑ i in range n, u i) atTop (𝓝 a) := by
refine cauchySeq_tendsto_of_complete cauchySeq_of_summable_dist ?_
  simp [dist_eq_norm, sum_range_succ, hu]

/--
lemma `NormedAddCommGroup.summable_imp_tendsto_iff_completeSpace` / 引理 `NormedAddCommGroup.summable_imp_tendsto_iff_completeSpace`

English:
lemma NormedAddCommGroup.summable_imp_tendsto_iff_completeSpace
  proof: ⟨completeSpace_of_summable_imp_tendsto, fun _ u hu => summable_imp_tendsto_of_complete u hu⟩

中文:
引理 赋范交换加群.summable_imp_tendsto_iff_completeSpace
  证明: ⟨completeSpace_of_summable_imp_tendsto, fun _ u hu => summable_imp_tendsto_of_complete u hu⟩

Depends on / 依赖: completeSpace_of_summable_imp_tendsto, summable_imp_tendsto_of_complete
-/
lemma NormedAddCommGroup.summable_imp_tendsto_iff_completeSpace :
    (forall u : Nat -> E, Summable (‖u ·‖) -> exists a, Tendsto (fun n => ∑ i in range n, u i) atTop (𝓝 a))
     ↔ CompleteSpace E :=
  ⟨completeSpace_of_summable_imp_tendsto, fun _ u hu => summable_imp_tendsto_of_complete u hu⟩

end Normed
