/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
module

public import Mathlib.MeasureTheory.OuterMeasure.Defs
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# Outer Measures

An outer measure is a function `μ : Set α → ℝ≥0∞`, from the powerset of a type to the extended
nonnegative real numbers that satisfies the following conditions:
1. `μ ∅ = 0`;
2. `μ` is monotone;
3. `μ` is countably subadditive. This means that the outer measure of a countable union is at most
   the sum of the outer measure on the individual sets.

Note that we do not need `α` to be measurable to define an outer measure.

## References

<https://en.wikipedia.org/wiki/Outer_measure>

## Tags

outer measure
-/

public section


noncomputable section

open Set Function Filter
open scoped NNReal Topology ENNReal

namespace MeasureTheory

section OuterMeasureClass

variable {α ι F : Type*} [FunLike F (Set α) Real>=0∞] [OuterMeasureClass F α]
  {μ : F} {s t : Set α}

@[simp]
/--
theorem `measure_empty` / 定理 `measure_empty`

English:
theorem measure_empty
  statement: μ ∅ = 0
  proof: OuterMeasureClass.measure_empty μ

@[mono, gcongr]

中文:
定理 measure_empty
  结论: μ ∅ = 0
  证明: OuterMeasureClass.measure_empty μ

@[mono, gcongr]

Depends on / 依赖: OuterMeasureClass, OuterMeasureClass.measure_empty, measure_empty
-/
theorem measure_empty : μ ∅ = 0 := OuterMeasureClass.measure_empty μ

@[mono, gcongr]
/--
theorem `measure_mono` / 定理 `measure_mono`

English:
theorem measure_mono
  given: (h : s subseteq t)
  statement: μ s <= μ t
  proof: OuterMeasureClass.measure_mono μ h

中文:
定理 measure_mono
  条件: (h : s subseteq t)
  结论: μ s <= μ t
  证明: OuterMeasureClass.measure_mono μ h

Depends on / 依赖: CompleteLattice, CompleteLattice.toConditionallyCompleteLattice, OuterMeasureClass, OuterMeasureClass.measure_mono, measure_mono, toConditionallyCompleteLattice
-/
theorem measure_mono (h : s subseteq t) : μ s <= μ t :=
  OuterMeasureClass.measure_mono μ h

/--
theorem `measure_mono_null` / 定理 `measure_mono_null`

English:
theorem measure_mono_null
  given: (h : s subseteq t) (ht : μ t = 0)
  statement: μ s = 0
  proof: eq_bot_mono (measure_mono h) ht

中文:
定理 measure_mono_null
  条件: (h : s subseteq t) (ht : μ t = 0)
  结论: μ s = 0
  证明: eq_bot_mono (measure_mono h) ht

Depends on / 依赖: CompleteLinearOrder, CompleteLinearOrder.toConditionallyCompleteLinearOrderBot, eq_bot_mono, measure_mono, toConditionallyCompleteLinearOrderBot
-/
theorem measure_mono_null (h : s subseteq t) (ht : μ t = 0) : μ s = 0 :=
  eq_bot_mono (measure_mono h) ht

/--
lemma `pos_mono` / 引理 `pos_mono`

English:
lemma pos_mono
  given: ⦃s t
  statement: Set α⦄ (h : s subseteq t) (hs : 0 < μ s) :
  proof: hs.trans_le measure_mono h

中文:
引理 pos_mono
  条件: ⦃s t
  结论: 集合 α⦄ (h : s subseteq t) (hs : 0 < μ s) :
  证明: hs.trans_le measure_mono h

Depends on / 依赖: hs.trans_le, measure_mono, trans_le
-/
lemma pos_mono ⦃s t : Set α⦄ (h : s subseteq t) (hs : 0 < μ s) :
0 < μ t := hs.trans_le measure_mono h

/--
lemma `measure_eq_top_mono` / 引理 `measure_eq_top_mono`

English:
lemma measure_eq_top_mono
  given: (h : s subseteq t) (hs : μ s = ∞)
  statement: μ t = ∞
  proof: eq_top_mono (measure_mono h) hs

中文:
引理 measure_eq_top_mono
  条件: (h : s subseteq t) (hs : μ s = ∞)
  结论: μ t = ∞
  证明: eq_top_mono (measure_mono h) hs

Depends on / 依赖: ConditionallyCompleteLinearOrder, ConditionallyCompleteLinearOrder.csInf_of_not_bddBelow, csInf_of_not_bddBelow, eq_top_mono, measure_mono
-/
lemma measure_eq_top_mono (h : s subseteq t) (hs : μ s = ∞) : μ t = ∞ := eq_top_mono (measure_mono h) hs
/--
lemma `measure_lt_top_mono` / 引理 `measure_lt_top_mono`

English:
lemma measure_lt_top_mono
  given: (h : s subseteq t) (ht : μ t < ∞)
  statement: μ s < ∞
  proof: (measure_mono h).trans_lt ht

中文:
引理 measure_lt_top_mono
  条件: (h : s subseteq t) (ht : μ t < ∞)
  结论: μ s < ∞
  证明: (measure_mono h).trans_lt ht

Depends on / 依赖: measure_mono, trans_lt
-/
lemma measure_lt_top_mono (h : s subseteq t) (ht : μ t < ∞) : μ s < ∞ := (measure_mono h).trans_lt ht

/--
theorem `measure_pos_of_superset` / 定理 `measure_pos_of_superset`

English:
theorem measure_pos_of_superset
  given: (h : s subseteq t) (hs : μ s != 0)
  statement: 0 < μ t
  proof: hs.bot_lt.trans_le (measure_mono h)

中文:
定理 measure_pos_of_superset
  条件: (h : s subseteq t) (hs : μ s != 0)
  结论: 0 < μ t
  证明: hs.bot_lt.trans_le (measure_mono h)

Depends on / 依赖: bot_lt, hs.bot_lt.trans_le, measure_mono, trans_le
-/
theorem measure_pos_of_superset (h : s subseteq t) (hs : μ s != 0) : 0 < μ t :=
  hs.bot_lt.trans_le (measure_mono h)

/--
theorem `measure_iUnion_le` / 定理 `measure_iUnion_le`

English:
theorem measure_iUnion_le
  given: [Countable ι] (s : ι -> Set α)
  statement: μ (⋃ i, s i) <= ∑' i, μ (s i)
  proof: by
  refine rel_iSup_tsum μ measure_empty (· <= ·) (fun t => ?_) _
  calc
    μ (⋃ i, t i) = μ (⋃ i, disjointed t i) := by rw [iUnion_disjointed]
    _ <= ∑' i, μ (disjointed t i) :=
      OuterMeasureClass.measure_iUnion_nat_le _ _ (disjoint_disjointed _)
    _ <= ∑' i, μ (t i) := by gcongr; exact 

中文:
定理 measure_iUnion_le
  条件: [可数 ι] (s : ι -> 集合 α)
  结论: μ (⋃ i, s i) <= ∑' i, μ (s i)
  证明: by
  refine rel_iSup_tsum μ measure_empty (· <= ·) (fun t => ?_) _
  calc
    μ (⋃ i, t i) = μ (⋃ i, disjointed t i) := by rw [iUnion_disjointed]
    _ <= ∑' i, μ (disjointed t i) :=
      OuterMeasureClass.measure_iUnion_nat_le _ _ (disjoint_disjointed _)
    _ <= ∑' i, μ (t i) := by gcongr; exact 

Depends on / 依赖: OuterMeasureClass, OuterMeasureClass.measure_iUnion_nat_le, disjoint_disjointed, disjointed, disjointed_subset, iUnion_disjointed, measure_empty, measure_iUnion_nat_le, rel_iSup_tsum
-/
theorem measure_iUnion_le [Countable ι] (s : ι -> Set α) : μ (⋃ i, s i) <= ∑' i, μ (s i) := by
  refine rel_iSup_tsum μ measure_empty (· <= ·) (fun t => ?_) _
  calc
    μ (⋃ i, t i) = μ (⋃ i, disjointed t i) := by rw [iUnion_disjointed]
    _ <= ∑' i, μ (disjointed t i) :=
      OuterMeasureClass.measure_iUnion_nat_le _ _ (disjoint_disjointed _)
    _ <= ∑' i, μ (t i) := by gcongr; exact disjointed_subset ..

/--
theorem `measure_biUnion_le` / 定理 `measure_biUnion_le`

English:
theorem measure_biUnion_le
  given: {I : Set ι} (μ : F) (hI : I.Countable) (s : ι -> Set α)
  proof: by
  have := hI.to_subtype
  rw [biUnion_eq_iUnion]
  apply measure_iUnion_le

中文:
定理 measure_biUnion_le
  条件: {I : 集合 ι} (μ : F) (hI : I.可数) (s : ι -> 集合 α)
  证明: by
  have := hI.to_subtype
  rw [biUnion_eq_iUnion]
  apply measure_iUnion_le

Depends on / 依赖: biUnion_eq_iUnion, hI.to_subtype, measure_iUnion_le, to_subtype
-/
theorem measure_biUnion_le {I : Set ι} (μ : F) (hI : I.Countable) (s : ι -> Set α) :
    μ (⋃ i in I, s i) <= ∑' i : I, μ (s i) := by
  have := hI.to_subtype
  rw [biUnion_eq_iUnion]
  apply measure_iUnion_le

/--
theorem `measure_biUnion_finset_le` / 定理 `measure_biUnion_finset_le`

English:
theorem measure_biUnion_finset_le
  given: (I : Finset ι) (s : ι -> Set α)
  proof: (measure_biUnion_le μ I.countable_toSet s).trans_eq I.tsum_subtype (μ <| s ·)

中文:
定理 measure_biUnion_finset_le
  条件: (I : 有限集 ι) (s : ι -> 集合 α)
  证明: (measure_biUnion_le μ I.countable_toSet s).trans_eq I.tsum_subtype (μ <| s ·)

Depends on / 依赖: I.countable_toSet, I.tsum_subtype, countable_toSet, measure_biUnion_le, trans_eq, tsum_subtype
-/
theorem measure_biUnion_finset_le (I : Finset ι) (s : ι -> Set α) :
    μ (⋃ i in I, s i) <= ∑ i in I, μ (s i) :=
(measure_biUnion_le μ I.countable_toSet s).trans_eq I.tsum_subtype (μ <| s ·)

/--
theorem `measure_iUnion_fintype_le` / 定理 `measure_iUnion_fintype_le`

English:
theorem measure_iUnion_fintype_le
  given: [Fintype ι] (μ : F) (s : ι -> Set α)
  proof: by
  simpa using measure_biUnion_finset_le Finset.univ s

中文:
定理 measure_iUnion_fintype_le
  条件: [有限类型 ι] (μ : F) (s : ι -> 集合 α)
  证明: by
  simpa using measure_biUnion_finset_le Finset.univ s

Depends on / 依赖: Finset, Finset.univ, measure_biUnion_finset_le
-/
theorem measure_iUnion_fintype_le [Fintype ι] (μ : F) (s : ι -> Set α) :
    μ (⋃ i, s i) <= ∑ i, μ (s i) := by
  simpa using measure_biUnion_finset_le Finset.univ s

/--
theorem `measure_union_le` / 定理 `measure_union_le`

English:
theorem measure_union_le
  given: (s t : Set α)
  statement: μ (s union t) <= μ s + μ t
  proof: by
  simpa [union_eq_iUnion] using measure_iUnion_fintype_le μ (cond · s t)

中文:
定理 measure_union_le
  条件: (s t : 集合 α)
  结论: μ (s union t) <= μ s + μ t
  证明: by
  simpa [union_eq_iUnion] using measure_iUnion_fintype_le μ (cond · s t)

Depends on / 依赖: measure_iUnion_fintype_le, union_eq_iUnion
-/
theorem measure_union_le (s t : Set α) : μ (s union t) <= μ s + μ t := by
  simpa [union_eq_iUnion] using measure_iUnion_fintype_le μ (cond · s t)

/--
lemma `measure_univ_le_add_compl` / 引理 `measure_univ_le_add_compl`

English:
lemma measure_univ_le_add_compl
  given: (s : Set α)
  statement: μ univ <= μ s + μ sᶜ
  proof: s.union_compl_self ▸ measure_union_le s sᶜ

中文:
引理 measure_univ_le_add_compl
  条件: (s : 集合 α)
  结论: μ univ <= μ s + μ sᶜ
  证明: s.union_compl_self ▸ measure_union_le s sᶜ

Depends on / 依赖: ConditionallyCompleteLattice, ConditionallyCompleteLattice.toConditionallyCompletePartialOrder, measure_union_le, s.union_compl_self, toConditionallyCompletePartialOrder, union_compl_self
-/
lemma measure_univ_le_add_compl (s : Set α) : μ univ <= μ s + μ sᶜ :=
  s.union_compl_self ▸ measure_union_le s sᶜ

/--
theorem `measure_le_inter_add_sdiff` / 定理 `measure_le_inter_add_sdiff`

English:
theorem measure_le_inter_add_sdiff
  given: (μ : F) (s t : Set α)
  statement: μ s <= μ (s inter t) + μ (s \ t)
  proof: by
  simpa using measure_union_le (s inter t) (s \ t)

@[deprecated (since := "2026-06-03")] alias measure_le_inter_add_diff := measure_le_inter_add_sdiff

中文:
定理 measure_le_inter_add_sdiff
  条件: (μ : F) (s t : 集合 α)
  结论: μ s <= μ (s inter t) + μ (s \ t)
  证明: by
  simpa using measure_union_le (s inter t) (s \ t)

@[deprecated (since := "2026-06-03")] alias measure_le_inter_add_diff := measure_le_inter_add_sdiff

Depends on / 依赖: measure_union_le
-/
theorem measure_le_inter_add_sdiff (μ : F) (s t : Set α) : μ s <= μ (s inter t) + μ (s \ t) := by
  simpa using measure_union_le (s inter t) (s \ t)

@[deprecated (since := "2026-06-03")] alias measure_le_inter_add_diff := measure_le_inter_add_sdiff

/--
theorem `measure_sdiff_null` / 定理 `measure_sdiff_null`

English:
theorem measure_sdiff_null
  given: (ht : μ t = 0)
  statement: μ (s \ t) = μ s
  proof: (measure_mono sdiff_subset).antisymm calc
    μ s <= μ (s inter t) + μ (s \ t) := measure_le_inter_add_sdiff _ _ _
    _ <= μ t + μ (s \ t) := by gcongr; apply inter_subset_right
    _ = μ (s \ t) := by simp [ht]

@[deprecated (since := "2026-06-03")] alias measure_diff_null := measure_sdiff_null

中文:
定理 measure_sdiff_null
  条件: (ht : μ t = 0)
  结论: μ (s \ t) = μ s
  证明: (measure_mono sdiff_subset).antisymm calc
    μ s <= μ (s inter t) + μ (s \ t) := measure_le_inter_add_sdiff _ _ _
    _ <= μ t + μ (s \ t) := by gcongr; apply inter_subset_right
    _ = μ (s \ t) := by simp [ht]

@[deprecated (since := "2026-06-03")] alias measure_diff_null := measure_sdiff_null

Depends on / 依赖: antisymm, inter_subset_right, measure_le_inter_add_sdiff, measure_mono, sdiff_subset
-/
theorem measure_sdiff_null (ht : μ t = 0) : μ (s \ t) = μ s :=
(measure_mono sdiff_subset).antisymm calc
    μ s <= μ (s inter t) + μ (s \ t) := measure_le_inter_add_sdiff _ _ _
    _ <= μ t + μ (s \ t) := by gcongr; apply inter_subset_right
    _ = μ (s \ t) := by simp [ht]

@[deprecated (since := "2026-06-03")] alias measure_diff_null := measure_sdiff_null

/--
theorem `measure_biUnion_null_iff` / 定理 `measure_biUnion_null_iff`

English:
theorem measure_biUnion_null_iff
  given: {I : Set ι} (hI : I.Countable) {s : ι -> Set α}
  proof: by
  refine ⟨fun h i hi => measure_mono_null (subset_biUnion_of_mem hi) h, fun h => ?_⟩
  have _ := hI.to_subtype
  simpa [h] using measure_iUnion_le (μ := μ) fun x : I => s x

中文:
定理 measure_biUnion_null_iff
  条件: {I : 集合 ι} (hI : I.可数) {s : ι -> 集合 α}
  证明: by
  refine ⟨fun h i hi => measure_mono_null (subset_biUnion_of_mem hi) h, fun h => ?_⟩
  have _ := hI.to_subtype
  simpa [h] using measure_iUnion_le (μ := μ) fun x : I => s x

Depends on / 依赖: hI.to_subtype, measure_iUnion_le, measure_mono_null, subset_biUnion_of_mem, to_subtype
-/
theorem measure_biUnion_null_iff {I : Set ι} (hI : I.Countable) {s : ι -> Set α} :
    μ (⋃ i in I, s i) = 0 ↔ forall i in I, μ (s i) = 0 := by
  refine ⟨fun h i hi => measure_mono_null (subset_biUnion_of_mem hi) h, fun h => ?_⟩
  have _ := hI.to_subtype
  simpa [h] using measure_iUnion_le (μ := μ) fun x : I => s x

/--
theorem `measure_sUnion_null_iff` / 定理 `measure_sUnion_null_iff`

English:
theorem measure_sUnion_null_iff
  given: {S : Set (Set α)} (hS : S.Countable)
  proof: by
  rw [sUnion_eq_biUnion]; rw [measure_biUnion_null_iff hS]

@[simp]

中文:
定理 measure_sUnion_null_iff
  条件: {S : 集合 (集合 α)} (hS : S.可数)
  证明: by
  rw [sUnion_eq_biUnion]; rw [measure_biUnion_null_iff hS]

@[simp]

Depends on / 依赖: measure_biUnion_null_iff, sUnion_eq_biUnion
-/
theorem measure_sUnion_null_iff {S : Set (Set α)} (hS : S.Countable) :
    μ (⋃₀ S) = 0 ↔ forall s in S, μ s = 0 := by
  rw [sUnion_eq_biUnion]; rw [measure_biUnion_null_iff hS]

@[simp]
/--
theorem `measure_iUnion_null_iff` / 定理 `measure_iUnion_null_iff`

English:
theorem measure_iUnion_null_iff
  given: {ι : Sort*} [Countable ι] {s : ι -> Set α}
  proof: by
  rw [← sUnion_range]; rw [measure_sUnion_null_iff (countable_range s)]; rw [forall_mem_range]

alias ⟨_, measure_iUnion_null⟩ := measure_iUnion_null_iff

@[simp]

中文:
定理 measure_iUnion_null_iff
  条件: {ι : 类型层*} [可数 ι] {s : ι -> 集合 α}
  证明: by
  rw [← sUnion_range]; rw [measure_sUnion_null_iff (countable_range s)]; rw [forall_mem_range]

alias ⟨_, measure_iUnion_null⟩ := measure_iUnion_null_iff

@[simp]

Depends on / 依赖: countable_range, forall_mem_range, measure_sUnion_null_iff, sUnion_range
-/
theorem measure_iUnion_null_iff {ι : Sort*} [Countable ι] {s : ι -> Set α} :
    μ (⋃ i, s i) = 0 ↔ forall i, μ (s i) = 0 := by
  rw [← sUnion_range]; rw [measure_sUnion_null_iff (countable_range s)]; rw [forall_mem_range]

alias ⟨_, measure_iUnion_null⟩ := measure_iUnion_null_iff

@[simp]
/--
theorem `measure_union_null_iff` / 定理 `measure_union_null_iff`

English:
theorem measure_union_null_iff
  statement: μ (s union t) = 0 ↔ μ s = 0 ∧ μ t = 0
  proof: by
  simp [union_eq_iUnion, and_comm]

中文:
定理 measure_union_null_iff
  结论: μ (s union t) = 0 ↔ μ s = 0 ∧ μ t = 0
  证明: by
  simp [union_eq_iUnion, and_comm]

Depends on / 依赖: and_comm, union_eq_iUnion
-/
theorem measure_union_null_iff : μ (s union t) = 0 ↔ μ s = 0 ∧ μ t = 0 := by
  simp [union_eq_iUnion, and_comm]

/--
theorem `measure_union_null` / 定理 `measure_union_null`

English:
theorem measure_union_null
  given: (hs : μ s = 0) (ht : μ t = 0)
  statement: μ (s union t) = 0
  proof: by simp [*]

中文:
定理 measure_union_null
  条件: (hs : μ s = 0) (ht : μ t = 0)
  结论: μ (s union t) = 0
  证明: by simp [*]
-/
theorem measure_union_null (hs : μ s = 0) (ht : μ t = 0) : μ (s union t) = 0 := by simp [*]

/--
lemma `measure_null_iff_singleton` / 引理 `measure_null_iff_singleton`

English:
lemma measure_null_iff_singleton
  given: (hs : s.Countable)
  statement: μ s = 0 ↔ forall x in s, μ {x} = 0
  proof: by
  rw [← measure_biUnion_null_iff hs]; rw [biUnion_of_singleton]

中文:
引理 measure_null_iff_singleton
  条件: (hs : s.可数)
  结论: μ s = 0 ↔ 对任意 x in s, μ {x} = 0
  证明: by
  rw [← measure_biUnion_null_iff hs]; rw [biUnion_of_singleton]

Depends on / 依赖: biUnion_of_singleton, measure_biUnion_null_iff
-/
lemma measure_null_iff_singleton (hs : s.Countable) : μ s = 0 ↔ forall x in s, μ {x} = 0 := by
  rw [← measure_biUnion_null_iff hs]; rw [biUnion_of_singleton]

/--
theorem `measure_iUnion_of_tendsto_zero` / 定理 `measure_iUnion_of_tendsto_zero`

English:
theorem measure_iUnion_of_tendsto_zero
  statement: {ι} (μ : F) {s : ι -> Set α} (l : Filter ι) [NeBot l]
  proof: by
refine le_antisymm ?_ iSup_le fun n => measure_mono subset_iUnion _ _
  set S := ⋃ n, s n
  set M := ⨆ n, μ (s n)
  have A : forall k, μ S <= M + μ (S \ s k) := fun k => calc
    μ S <= μ (S inter s k) + μ (S \ s k) := measure_le_inter_add_sdiff _ _ _
    _ <= μ (s k) + μ (S \ s k) := by gcongr; 

中文:
定理 measure_iUnion_of_tendsto_zero
  结论: {ι} (μ : F) {s : ι -> 集合 α} (l : 滤子 ι) [NeBot l]
  证明: by
refine le_antisymm ?_ iSup_le fun n => measure_mono subset_iUnion _ _
  set S := ⋃ n, s n
  set M := ⨆ n, μ (s n)
  have A : forall k, μ S <= M + μ (S \ s k) := fun k => calc
    μ S <= μ (S inter s k) + μ (S \ s k) := measure_le_inter_add_sdiff _ _ _
    _ <= μ (s k) + μ (S \ s k) := by gcongr; 

Depends on / 依赖: Tendsto, ge_of_tendsto, iSup_le, inter_subset_right, le_antisymm, le_iSup, measure_le_inter_add_sdiff, measure_mono, subset_iUnion, tendsto_const_nhds, tendsto_const_nhds.add
-/
theorem measure_iUnion_of_tendsto_zero {ι} (μ : F) {s : ι -> Set α} (l : Filter ι) [NeBot l]
    (h0 : Tendsto (fun k => μ ((⋃ n, s n) \ s k)) l (𝓝 0)) : μ (⋃ n, s n) = ⨆ n, μ (s n) := by
refine le_antisymm ?_ iSup_le fun n => measure_mono subset_iUnion _ _
  set S := ⋃ n, s n
  set M := ⨆ n, μ (s n)
  have A : forall k, μ S <= M + μ (S \ s k) := fun k => calc
    μ S <= μ (S inter s k) + μ (S \ s k) := measure_le_inter_add_sdiff _ _ _
    _ <= μ (s k) + μ (S \ s k) := by gcongr; apply inter_subset_right
    _ <= M + μ (S \ s k) := by gcongr; exact le_iSup (μ ∘ s) k
  have B : Tendsto (fun k => M + μ (S \ s k)) l (𝓝 M) := by simpa using tendsto_const_nhds.add h0
  exact ge_of_tendsto' B A

/--
theorem `measure_null_of_locally_null` / 定理 `measure_null_of_locally_null`

English:
theorem measure_null_of_locally_null
  statement: [TopologicalSpace α] [SecondCountableTopology α]
  proof: by
  choose! u hxu hu₀ using hs
  choose t ht using TopologicalSpace.countable_cover_nhdsWithin hxu
  rcases ht with ⟨ts, t_count, ht⟩
  apply measure_mono_null ht
  exact (measure_biUnion_null_iff t_count).2 fun x hx => hu₀ x (ts hx)

中文:
定理 measure_null_of_locally_null
  结论: [拓扑空间 α] [第二可数拓扑 α]
  证明: by
  choose! u hxu hu₀ using hs
  choose t ht using TopologicalSpace.countable_cover_nhdsWithin hxu
  rcases ht with ⟨ts, t_count, ht⟩
  apply measure_mono_null ht
  exact (measure_biUnion_null_iff t_count).2 fun x hx => hu₀ x (ts hx)

Depends on / 依赖: TopologicalSpace, TopologicalSpace.countable_cover_nhdsWithin, countable_cover_nhdsWithin, measure_biUnion_null_iff, measure_mono_null, t_count
-/
theorem measure_null_of_locally_null [TopologicalSpace α] [SecondCountableTopology α]
    (s : Set α) (hs : forall x in s, exists u in 𝓝[s] x, μ u = 0) : μ s = 0 := by
  choose! u hxu hu₀ using hs
  choose t ht using TopologicalSpace.countable_cover_nhdsWithin hxu
  rcases ht with ⟨ts, t_count, ht⟩
  apply measure_mono_null ht
  exact (measure_biUnion_null_iff t_count).2 fun x hx => hu₀ x (ts hx)

/--
theorem `exists_mem_forall_mem_nhdsWithin_pos_measure` / 定理 `exists_mem_forall_mem_nhdsWithin_pos_measure`

English:
theorem exists_mem_forall_mem_nhdsWithin_pos_measure
  statement: [TopologicalSpace α]
  proof: by
  contrapose! hs
  simp only [nonpos_iff_eq_zero] at hs
  exact measure_null_of_locally_null s hs

中文:
定理 存在_mem_对任意_mem_nhdsWithin_pos_measure
  结论: [拓扑空间 α]
  证明: by
  contrapose! hs
  simp only [nonpos_iff_eq_zero] at hs
  exact measure_null_of_locally_null s hs

Depends on / 依赖: contrapose, measure_null_of_locally_null, nonpos_iff_eq_zero
-/
theorem exists_mem_forall_mem_nhdsWithin_pos_measure [TopologicalSpace α]
    [SecondCountableTopology α] {s : Set α} (hs : μ s != 0) :
    exists x in s, forall t in 𝓝[s] x, 0 < μ t := by
  contrapose! hs
  simp only [nonpos_iff_eq_zero] at hs
  exact measure_null_of_locally_null s hs

end OuterMeasureClass

namespace OuterMeasure

variable {α β : Type*} {m : OuterMeasure α}

/--
theorem `iUnion_of_tendsto_zero` / 定理 `iUnion_of_tendsto_zero`

English:
theorem iUnion_of_tendsto_zero
  statement: {ι} (m : OuterMeasure α) {s : ι -> Set α} (l : Filter ι) [NeBot l]
  proof: measure_iUnion_of_tendsto_zero m l h0

中文:
定理 iUnion_of_tendsto_zero
  结论: {ι} (m : 外测度 α) {s : ι -> 集合 α} (l : 滤子 ι) [NeBot l]
  证明: measure_iUnion_of_tendsto_zero m l h0

Depends on / 依赖: measure_iUnion_of_tendsto_zero
-/
theorem iUnion_of_tendsto_zero {ι} (m : OuterMeasure α) {s : ι -> Set α} (l : Filter ι) [NeBot l]
    (h0 : Tendsto (fun k => m ((⋃ n, s n) \ s k)) l (𝓝 0)) : m (⋃ n, s n) = ⨆ n, m (s n) :=
  measure_iUnion_of_tendsto_zero m l h0

/--
theorem `iUnion_nat_of_monotone_of_tsum_ne_top` / 定理 `iUnion_nat_of_monotone_of_tsum_ne_top`

English:
theorem iUnion_nat_of_monotone_of_tsum_ne_top
  statement: (m : OuterMeasure α) {s : Nat -> Set α}
  proof: by
  classical
  refine measure_iUnion_of_tendsto_zero m atTop ?_
  refine tendsto_nhds_bot_mono' (ENNReal.tendsto_sum_nat_add _ h0) fun n => ?_
  refine (m.mono ?_).trans (measure_iUnion_le _)
  -- Current goal: `(⋃ k, s k) \ s n ⊆ ⋃ k, s (k + n + 1) \ s (k + n)`
  have h' : Monotone s := @monotone

中文:
定理 iUnion_nat_of_monotone_of_tsum_ne_top
  结论: (m : 外测度 α) {s : 自然数 -> 集合 α}
  证明: by
  classical
  refine measure_iUnion_of_tendsto_zero m atTop ?_
  refine tendsto_nhds_bot_mono' (ENNReal.tendsto_sum_nat_add _ h0) fun n => ?_
  refine (m.mono ?_).trans (measure_iUnion_le _)
  -- Current goal: `(⋃ k, s k) \ s n ⊆ ⋃ k, s (k + n + 1) \ s (k + n)`
  have h' : Monotone s := @monotone

Depends on / 依赖: ENNReal, ENNReal.tendsto_sum_nat_add, classical, m.mono, measure_iUnion_le, measure_iUnion_of_tendsto_zero, tendsto_nhds_bot_mono, tendsto_sum_nat_add
-/
theorem iUnion_nat_of_monotone_of_tsum_ne_top (m : OuterMeasure α) {s : Nat -> Set α}
    (h_mono : forall n, s n subseteq s (n + 1)) (h0 : (∑' k, m (s (k + 1) \ s k)) != ∞) :
    m (⋃ n, s n) = ⨆ n, m (s n) := by
  classical
  refine measure_iUnion_of_tendsto_zero m atTop ?_
  refine tendsto_nhds_bot_mono' (ENNReal.tendsto_sum_nat_add _ h0) fun n => ?_
  refine (m.mono ?_).trans (measure_iUnion_le _)
  -- Current goal: `(⋃ k, s k) \ s n ⊆ ⋃ k, s (k + n + 1) \ s (k + n)`
  have h' : Monotone s := @monotone_nat_of_le_succ (Set α) _ _ h_mono
  simp only [sdiff_subset_iff, iUnion_subset_iff]
  intro i x hx
  have : exists i, x in s i := by exists i
  rcases Nat.findX this with ⟨j, hj, hlt⟩
  clear hx i
  rcases le_or_gt j n with hjn | hnj
  · exact Or.inl (h' hjn hj)
  have : j - (n + 1) + n + 1 = j := by lia
  refine Or.inr (mem_iUnion.2 ⟨j - (n + 1), ?_, hlt _ ?_⟩)
  · rwa [this]
  · rw [← Nat.succ_le_iff, Nat.succ_eq_add_one, this]

/--
theorem `coe_fn_injective` / 定理 `coe_fn_injective`

English:
theorem coe_fn_injective
  statement: Injective fun (μ : OuterMeasure α) (s : Set α) => μ s
  proof: DFunLike.coe_injective

@[ext]

中文:
定理 coe_fn_injective
  结论: 单射 fun (μ : 外测度 α) (s : 集合 α) => μ s
  证明: DFunLike.coe_injective

@[ext]

Depends on / 依赖: DFunLike, DFunLike.coe_injective, coe_injective
-/
theorem coe_fn_injective : Injective fun (μ : OuterMeasure α) (s : Set α) => μ s :=
  DFunLike.coe_injective

@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: {μ₁ μ₂ : OuterMeasure α} (h : forall s, μ₁ s = μ₂ s)
  statement: μ₁ = μ₂
  proof: DFunLike.ext _ _ h

中文:
定理 ext
  条件: {μ₁ μ₂ : 外测度 α} (h : 对任意 s, μ₁ s = μ₂ s)
  结论: μ₁ = μ₂
  证明: DFunLike.ext _ _ h

Depends on / 依赖: DFunLike, DFunLike.ext
-/
theorem ext {μ₁ μ₂ : OuterMeasure α} (h : forall s, μ₁ s = μ₂ s) : μ₁ = μ₂ :=
  DFunLike.ext _ _ h

/--
theorem `ext_nonempty` / 定理 `ext_nonempty`

English:
theorem ext_nonempty
  given: {μ₁ μ₂ : OuterMeasure α} (h : forall s : Set α, s.Nonempty -> μ₁ s = μ₂ s)
  proof: ext fun s => s.eq_empty_or_nonempty.elim (fun he => by simp [he]) (h s)

中文:
定理 ext_nonempty
  条件: {μ₁ μ₂ : 外测度 α} (h : 对任意 s : 集合 α, s.非空 -> μ₁ s = μ₂ s)
  证明: ext fun s => s.eq_empty_or_nonempty.elim (fun he => by simp [he]) (h s)

Depends on / 依赖: eq_empty_or_nonempty, s.eq_empty_or_nonempty.elim
-/
theorem ext_nonempty {μ₁ μ₂ : OuterMeasure α} (h : forall s : Set α, s.Nonempty -> μ₁ s = μ₂ s) :
    μ₁ = μ₂ :=
  ext fun s => s.eq_empty_or_nonempty.elim (fun he => by simp [he]) (h s)

end OuterMeasure

end MeasureTheory
