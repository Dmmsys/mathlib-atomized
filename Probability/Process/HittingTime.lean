/-
Copyright (c) 2022 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying, Rémy Degenne
-/
module

public import Mathlib.Probability.Process.Stopping
public import Mathlib.Tactic.AdaptationNote

/-!
# Hitting times

Given a stochastic process, the hitting time provides the first time the process "hits" some
subset of the state space. The hitting time is a stopping time in the case that the time index is
discrete and the process is strongly adapted (this is true in a far more general setting however
we have only proved it for the discrete case so far).

## Main definition

* `MeasureTheory.hittingBtwn u s n m`: the first time a stochastic process `u` enters a set `s`
  after time `n` and before time `m`
* `MeasureTheory.hittingAfter u s n`: the first time a stochastic process `u` enters a set `s`
  after time `n`

## Main results

* `MeasureTheory.Adapted.isStoppingTime_hittingBtwn`: a discrete hitting time of an adapted process
  is a stopping time
* `MeasureTheory.Adapted.isStoppingTime_hittingAfter`: a discrete hitting time of a adapted process
  is a stopping time

-/

@[expose] public section


open Filter Order TopologicalSpace

open scoped MeasureTheory NNReal ENNReal Topology

namespace MeasureTheory

variable {Ω β ι : Type*} {m : MeasurableSpace Ω}

section Basic

variable [Preorder ι] [InfSet ι] {u : ι -> Ω -> β}

open scoped Classical in
/--
Definition of `hittingBtwn` / `hittingBtwn` 的定义

English:
definition hittingBtwn
  signature: (u : ι -> Ω -> β)
  body: fun x => if exists j in Set.Icc n m, u j x in s
    then sInf (Set.Icc n m inter {i : ι | u i x in s}) else m

中文:
定义 hittingBtwn
  签名: (u : ι -> Ω -> β)
  定义体: fun x => if exists j in Set.Icc n m, u j x in s
    then sInf (Set.Icc n m inter {i : ι | u i x in s}) else m

Depends on / 依赖: Set.Icc
-/
noncomputable def hittingBtwn (u : ι -> Ω -> β)
    (s : Set β) (n m : ι) : Ω -> ι :=
  fun x => if exists j in Set.Icc n m, u j x in s
    then sInf (Set.Icc n m inter {i : ι | u i x in s}) else m

open scoped Classical in
/--
Definition of `hittingAfter` / `hittingAfter` 的定义

English:
definition hittingAfter
  signature: (u : ι -> Ω -> β) (s : Set β) (n : ι)
  body: fun x => if exists j, n <= j ∧ u j x in s then (sInf {i : ι | n <= i ∧ u i x in s} : ι) else ⊤

中文:
定义 hittingAfter
  签名: (u : ι -> Ω -> β) (s : Set β) (n : ι)
  定义体: fun x => if exists j, n <= j ∧ u j x in s then (sInf {i : ι | n <= i ∧ u i x in s} : ι) else ⊤
-/
noncomputable def hittingAfter (u : ι -> Ω -> β) (s : Set β) (n : ι) :
    Ω -> WithTop ι :=
  fun x => if exists j, n <= j ∧ u j x in s then (sInf {i : ι | n <= i ∧ u i x in s} : ι) else ⊤

open scoped Classical in
/--
theorem `hittingBtwn_def` / 定理 `hittingBtwn_def`

English:
theorem hittingBtwn_def
  given: (u : ι -> Ω -> β) (s : Set β) (n m : ι)
  proof: rfl

中文:
定理 hittingBtwn_def
  条件: (u : ι -> Ω -> β) (s : Set β) (n m : ι)
  证明: rfl
-/
theorem hittingBtwn_def (u : ι -> Ω -> β) (s : Set β) (n m : ι) :
    hittingBtwn u s n m =
    fun x => if exists j in Set.Icc n m, u j x in s then sInf (Set.Icc n m inter {i : ι | u i x in s}) else m :=
  rfl

open scoped Classical in
/--
lemma `hittingAfter_def` / 引理 `hittingAfter_def`

English:
lemma hittingAfter_def
  given: (u : ι -> Ω -> β) (s : Set β) (n : ι)
  proof: rfl

@[simp]

中文:
引理 hittingAfter_def
  条件: (u : ι -> Ω -> β) (s : Set β) (n : ι)
  证明: rfl

@[simp]
-/
lemma hittingAfter_def (u : ι -> Ω -> β) (s : Set β) (n : ι) :
    hittingAfter u s n =
    fun x => if exists j, n <= j ∧ u j x in s
      then ((sInf {i : ι | n <= i ∧ u i x in s} : ι) : WithTop ι) else ⊤ := rfl

@[simp]
/--
lemma `hittingBtwn_empty` / 引理 `hittingBtwn_empty`

English:
lemma hittingBtwn_empty
  given: (n m : ι)
  statement: hittingBtwn u ∅ n m = fun _ => m
  proof: by ext; simp [hittingBtwn]

@[simp]

中文:
引理 hittingBtwn_empty
  条件: (n m : ι)
  结论: hittingBtwn u ∅ n m = fun _ => m
  证明: by ext; simp [hittingBtwn]

@[simp]

Depends on / 依赖: hittingBtwn
-/
lemma hittingBtwn_empty (n m : ι) : hittingBtwn u ∅ n m = fun _ => m := by ext; simp [hittingBtwn]

@[simp]
/--
lemma `hittingAfter_empty` / 引理 `hittingAfter_empty`

English:
lemma hittingAfter_empty
  given: (n : ι)
  statement: hittingAfter u ∅ n = fun _ => ⊤
  proof: by ext; simp [hittingAfter]

@[simp]

中文:
引理 hittingAfter_empty
  条件: (n : ι)
  结论: hittingAfter u ∅ n = fun _ => ⊤
  证明: by ext; simp [hittingAfter]

@[simp]

Depends on / 依赖: hittingAfter
-/
lemma hittingAfter_empty (n : ι) : hittingAfter u ∅ n = fun _ => ⊤ := by ext; simp [hittingAfter]

@[simp]
/--
lemma `hittingBtwn_univ` / 引理 `hittingBtwn_univ`

English:
lemma hittingBtwn_univ
  given: {ι : Type*} [ConditionallyCompleteLinearOrder ι] {u : ι -> Ω -> β} (n m : ι)
  proof: by
  ext ω
  simp only [hittingBtwn_def, Set.mem_Icc, Set.mem_univ, and_true, Set.ofPred_true, Set.inter_univ]
  by_cases hnm : n <= m <;> simp [hnm] <;> grind

@[simp]

中文:
引理 hittingBtwn_univ
  条件: {ι : 类型} [ConditionallyCompleteLinearOrder ι] {u : ι -> Ω -> β} (n m : ι)
  证明: by
  ext ω
  simp only [hittingBtwn_def, Set.mem_Icc, Set.mem_univ, and_true, Set.ofPred_true, Set.inter_univ]
  by_cases hnm : n <= m <;> simp [hnm] <;> grind

@[simp]

Depends on / 依赖: Set.inter_univ, Set.mem_Icc, Set.mem_univ, Set.ofPred_true, and_true, hittingBtwn_def, inter_univ, mem_Icc, mem_univ, ofPred_true
-/
lemma hittingBtwn_univ {ι : Type*} [ConditionallyCompleteLinearOrder ι] {u : ι -> Ω -> β} (n m : ι) :
    hittingBtwn u .univ n m = fun _ => min n m := by
  ext ω
  simp only [hittingBtwn_def, Set.mem_Icc, Set.mem_univ, and_true, Set.ofPred_true, Set.inter_univ]
  by_cases hnm : n <= m <;> simp [hnm] <;> grind

@[simp]
/--
lemma `hittingAfter_univ` / 引理 `hittingAfter_univ`

English:
lemma hittingAfter_univ
  given: {ι : Type*} [ConditionallyCompleteLattice ι] {u : ι -> Ω -> β} (n : ι)
  proof: by
  ext ω
  classical
  simp only [hittingAfter_def, Set.mem_univ, and_true]
  rw [if_pos ⟨n]; rw [le_rfl⟩]
  exact_mod_cast csInf_Ici

中文:
引理 hittingAfter_univ
  条件: {ι : 类型} [ConditionallyCompleteLattice ι] {u : ι -> Ω -> β} (n : ι)
  证明: by
  ext ω
  classical
  simp only [hittingAfter_def, Set.mem_univ, and_true]
  rw [if_pos ⟨n]; rw [le_rfl⟩]
  exact_mod_cast csInf_Ici

Depends on / 依赖: Set.mem_univ, and_true, classical, csInf_Ici, hittingAfter_def, if_pos, le_rfl, mem_univ
-/
lemma hittingAfter_univ {ι : Type*} [ConditionallyCompleteLattice ι] {u : ι -> Ω -> β} (n : ι) :
    hittingAfter u .univ n = fun _ => (n : WithTop ι) := by
  ext ω
  classical
  simp only [hittingAfter_def, Set.mem_univ, and_true]
  rw [if_pos ⟨n]; rw [le_rfl⟩]
  exact_mod_cast csInf_Ici

end Basic

section Inequalities

variable [ConditionallyCompleteLinearOrder ι] {u : ι -> Ω -> β} {s : Set β} {n i : ι} {ω : Ω}

/--
theorem `hittingBtwn_of_lt` / 定理 `hittingBtwn_of_lt`

English:
theorem hittingBtwn_of_lt
  given: {m : ι} (h : m < n)
  statement: hittingBtwn u s n m ω = m
  proof: by
  grind [hittingBtwn, not_le, Set.Icc_eq_empty]

中文:
定理 hittingBtwn_of_lt
  条件: {m : ι} (h : m < n)
  结论: hittingBtwn u s n m ω = m
  证明: by
  grind [hittingBtwn, not_le, Set.Icc_eq_empty]

Depends on / 依赖: Icc_eq_empty, Set.Icc_eq_empty, hittingBtwn, not_le
-/
theorem hittingBtwn_of_lt {m : ι} (h : m < n) : hittingBtwn u s n m ω = m := by
  grind [hittingBtwn, not_le, Set.Icc_eq_empty]

/--
theorem `hittingBtwn_le` / 定理 `hittingBtwn_le`

English:
theorem hittingBtwn_le
  given: {m : ι} (ω : Ω)
  statement: hittingBtwn u s n m ω <= m
  proof: by
  simp only [hittingBtwn]
  split_ifs with h
  · obtain ⟨j, hj₁, hj₂⟩ := h
    change j in {i | u i ω in s} at hj₂
    exact (csInf_le (BddBelow.inter_of_left bddBelow_Icc) (Set.mem_inter hj₁ hj₂)).trans hj₁.2
  · exact le_rfl

中文:
定理 hittingBtwn_le
  条件: {m : ι} (ω : Ω)
  结论: hittingBtwn u s n m ω <= m
  证明: by
  simp only [hittingBtwn]
  split_ifs with h
  · obtain ⟨j, hj₁, hj₂⟩ := h
    change j in {i | u i ω in s} at hj₂
    exact (csInf_le (BddBelow.inter_of_left bddBelow_Icc) (Set.mem_inter hj₁ hj₂)).trans hj₁.2
  · exact le_rfl

Depends on / 依赖: BddBelow, BddBelow.inter_of_left, Set.mem_inter, bddBelow_Icc, csInf_le, hittingBtwn, inter_of_left, le_rfl, mem_inter, split_ifs
-/
theorem hittingBtwn_le {m : ι} (ω : Ω) : hittingBtwn u s n m ω <= m := by
  simp only [hittingBtwn]
  split_ifs with h
  · obtain ⟨j, hj₁, hj₂⟩ := h
    change j in {i | u i ω in s} at hj₂
    exact (csInf_le (BddBelow.inter_of_left bddBelow_Icc) (Set.mem_inter hj₁ hj₂)).trans hj₁.2
  · exact le_rfl

/--
theorem `notMem_of_lt_hittingBtwn` / 定理 `notMem_of_lt_hittingBtwn`

English:
theorem notMem_of_lt_hittingBtwn
  given: {m k : ι} (hk₁ : k < hittingBtwn u s n m ω) (hk₂ : n <= k)
  proof: by
  intro h
have hexists : exists j in Set.Icc n m, u j ω in s := ⟨k, ⟨hk₂, le_trans hk₁.le hittingBtwn_le _⟩, h⟩
  refine not_le.2 hk₁ ?_
  simp_rw [hittingBtwn, if_pos hexists]
exact csInf_le bddBelow_Icc.inter_of_left ⟨⟨hk₂, le_trans hk₁.le hittingBtwn_le _⟩, h⟩

中文:
定理 notMem_of_lt_hittingBtwn
  条件: {m k : ι} (hk₁ : k < hittingBtwn u s n m ω) (hk₂ : n <= k)
  证明: by
  intro h
have hexists : exists j in Set.Icc n m, u j ω in s := ⟨k, ⟨hk₂, le_trans hk₁.le hittingBtwn_le _⟩, h⟩
  refine not_le.2 hk₁ ?_
  simp_rw [hittingBtwn, if_pos hexists]
exact csInf_le bddBelow_Icc.inter_of_left ⟨⟨hk₂, le_trans hk₁.le hittingBtwn_le _⟩, h⟩

Depends on / 依赖: Set.Icc, bddBelow_Icc, bddBelow_Icc.inter_of_left, csInf_le, hexists, hittingBtwn, hittingBtwn_le, if_pos, inter_of_left, le_trans, not_le, simp_rw
-/
theorem notMem_of_lt_hittingBtwn {m k : ι} (hk₁ : k < hittingBtwn u s n m ω) (hk₂ : n <= k) :
    u k ω ∉ s := by
  intro h
have hexists : exists j in Set.Icc n m, u j ω in s := ⟨k, ⟨hk₂, le_trans hk₁.le hittingBtwn_le _⟩, h⟩
  refine not_le.2 hk₁ ?_
  simp_rw [hittingBtwn, if_pos hexists]
exact csInf_le bddBelow_Icc.inter_of_left ⟨⟨hk₂, le_trans hk₁.le hittingBtwn_le _⟩, h⟩

/--
theorem `notMem_of_lt_hittingAfter` / 定理 `notMem_of_lt_hittingAfter`

English:
theorem notMem_of_lt_hittingAfter
  given: {k : ι} (hk₁ : k < hittingAfter u s n ω) (hk₂ : n <= k)
  proof: by
  refine fun h => not_le.2 hk₁ ?_
  rw [hittingAfter]; rw [if_pos ⟨k]; rw [hk₂]; rw [h⟩]
  exact_mod_cast csInf_le bddBelow_Ici.inter_of_left ⟨hk₂, h⟩

中文:
定理 notMem_of_lt_hittingAfter
  条件: {k : ι} (hk₁ : k < hittingAfter u s n ω) (hk₂ : n <= k)
  证明: by
  refine fun h => not_le.2 hk₁ ?_
  rw [hittingAfter]; rw [if_pos ⟨k]; rw [hk₂]; rw [h⟩]
  exact_mod_cast csInf_le bddBelow_Ici.inter_of_left ⟨hk₂, h⟩

Depends on / 依赖: bddBelow_Ici, bddBelow_Ici.inter_of_left, csInf_le, hittingAfter, if_pos, inter_of_left, not_le
-/
theorem notMem_of_lt_hittingAfter {k : ι} (hk₁ : k < hittingAfter u s n ω) (hk₂ : n <= k) :
    u k ω ∉ s := by
  refine fun h => not_le.2 hk₁ ?_
  rw [hittingAfter]; rw [if_pos ⟨k]; rw [hk₂]; rw [h⟩]
  exact_mod_cast csInf_le bddBelow_Ici.inter_of_left ⟨hk₂, h⟩

/--
theorem `hittingBtwn_eq_end_iff` / 定理 `hittingBtwn_eq_end_iff`

English:
theorem hittingBtwn_eq_end_iff
  given: {m : ι}
  statement: hittingBtwn u s n m ω = m ↔
  proof: by
  classical
  rw [hittingBtwn]; rw [ite_eq_right_iff]

中文:
定理 hittingBtwn_eq_end_iff
  条件: {m : ι}
  结论: hittingBtwn u s n m ω = m ↔
  证明: by
  classical
  rw [hittingBtwn]; rw [ite_eq_right_iff]

Depends on / 依赖: classical, hittingBtwn, ite_eq_right_iff
-/
theorem hittingBtwn_eq_end_iff {m : ι} : hittingBtwn u s n m ω = m ↔
    (exists j in Set.Icc n m, u j ω in s) -> sInf (Set.Icc n m inter {i : ι | u i ω in s}) = m := by
  classical
  rw [hittingBtwn]; rw [ite_eq_right_iff]

/--
lemma `hittingAfter_eq_top_iff` / 引理 `hittingAfter_eq_top_iff`

English:
lemma hittingAfter_eq_top_iff
  statement: hittingAfter u s n ω = ⊤ ↔ forall j, n <= j -> u j ω ∉ s
  proof: by
  simp [hittingAfter]

中文:
引理 hittingAfter_eq_top_iff
  结论: hittingAfter u s n ω = ⊤ ↔ 对任意 j, n <= j -> u j ω ∉ s
  证明: by
  simp [hittingAfter]

Depends on / 依赖: hittingAfter
-/
lemma hittingAfter_eq_top_iff : hittingAfter u s n ω = ⊤ ↔ forall j, n <= j -> u j ω ∉ s := by
  simp [hittingAfter]

/--
theorem `hittingBtwn_of_le` / 定理 `hittingBtwn_of_le`

English:
theorem hittingBtwn_of_le
  given: {m : ι} (hmn : m <= n)
  statement: hittingBtwn u s n m ω = m
  proof: by
  obtain rfl | h := le_iff_eq_or_lt.1 hmn
  · classical
    rw [hittingBtwn]; rw [ite_eq_right_iff]; rw [forall_exists_index]
    conv => intro; rw [Set.mem_Icc, Set.Icc_self, and_imp, and_imp]
    intro i hi₁ hi₂ hi
    rw [Set.inter_eq_left.2]; rw [csInf_singleton]
    exact Set.singleton_subse

中文:
定理 hittingBtwn_of_le
  条件: {m : ι} (hmn : m <= n)
  结论: hittingBtwn u s n m ω = m
  证明: by
  obtain rfl | h := le_iff_eq_or_lt.1 hmn
  · classical
    rw [hittingBtwn]; rw [ite_eq_right_iff]; rw [forall_exists_index]
    conv => intro; rw [Set.mem_Icc, Set.Icc_self, and_imp, and_imp]
    intro i hi₁ hi₂ hi
    rw [Set.inter_eq_left.2]; rw [csInf_singleton]
    exact Set.singleton_subse

Depends on / 依赖: Icc_self, Set.Icc_self, Set.inter_eq_left, Set.mem_Icc, Set.singleton_subset_iff, and_imp, classical, csInf_singleton, forall_exists_index, hittingBtwn, hittingBtwn_of_lt, inter_eq_left, ite_eq_right_iff, le_antisymm, le_iff_eq_or_lt, mem_Icc, singleton_subset_iff
-/
theorem hittingBtwn_of_le {m : ι} (hmn : m <= n) : hittingBtwn u s n m ω = m := by
  obtain rfl | h := le_iff_eq_or_lt.1 hmn
  · classical
    rw [hittingBtwn]; rw [ite_eq_right_iff]; rw [forall_exists_index]
    conv => intro; rw [Set.mem_Icc, Set.Icc_self, and_imp, and_imp]
    intro i hi₁ hi₂ hi
    rw [Set.inter_eq_left.2]; rw [csInf_singleton]
    exact Set.singleton_subset_iff.2 (le_antisymm hi₂ hi₁ ▸ hi)
  · exact hittingBtwn_of_lt h

/--
theorem `le_hittingBtwn` / 定理 `le_hittingBtwn`

English:
theorem le_hittingBtwn
  given: {m : ι} (hnm : n <= m) (ω : Ω)
  statement: n <= hittingBtwn u s n m ω
  proof: by
  simp only [hittingBtwn]
  split_ifs with h
  · refine le_csInf ?_ fun b hb => ?_
    · obtain ⟨k, hk_Icc, hk_s⟩ := h
      exact ⟨k, hk_Icc, hk_s⟩
    · rw [Set.mem_inter_iff] at hb
      exact hb.1.1
  · exact hnm

中文:
定理 le_hittingBtwn
  条件: {m : ι} (hnm : n <= m) (ω : Ω)
  结论: n <= hittingBtwn u s n m ω
  证明: by
  simp only [hittingBtwn]
  split_ifs with h
  · refine le_csInf ?_ fun b hb => ?_
    · obtain ⟨k, hk_Icc, hk_s⟩ := h
      exact ⟨k, hk_Icc, hk_s⟩
    · rw [Set.mem_inter_iff] at hb
      exact hb.1.1
  · exact hnm

Depends on / 依赖: Set.mem_inter_iff, hittingBtwn, hk_Icc, hk_s, le_csInf, mem_inter_iff, split_ifs
-/
theorem le_hittingBtwn {m : ι} (hnm : n <= m) (ω : Ω) : n <= hittingBtwn u s n m ω := by
  simp only [hittingBtwn]
  split_ifs with h
  · refine le_csInf ?_ fun b hb => ?_
    · obtain ⟨k, hk_Icc, hk_s⟩ := h
      exact ⟨k, hk_Icc, hk_s⟩
    · rw [Set.mem_inter_iff] at hb
      exact hb.1.1
  · exact hnm

/--
lemma `le_hittingAfter` / 引理 `le_hittingAfter`

English:
lemma le_hittingAfter
  given: (ω : Ω)
  statement: n <= hittingAfter u s n ω
  proof: by
  simp only [hittingAfter]
  split_ifs with h
  · exact_mod_cast le_csInf h fun b hb => hb.1
  · simp

中文:
引理 le_hittingAfter
  条件: (ω : Ω)
  结论: n <= hittingAfter u s n ω
  证明: by
  simp only [hittingAfter]
  split_ifs with h
  · exact_mod_cast le_csInf h fun b hb => hb.1
  · simp

Depends on / 依赖: hittingAfter, le_csInf, split_ifs
-/
lemma le_hittingAfter (ω : Ω) : n <= hittingAfter u s n ω := by
  simp only [hittingAfter]
  split_ifs with h
  · exact_mod_cast le_csInf h fun b hb => hb.1
  · simp

/--
theorem `le_hittingBtwn_of_exists` / 定理 `le_hittingBtwn_of_exists`

English:
theorem le_hittingBtwn_of_exists
  given: {m : ι} (h_exists : exists j in Set.Icc n m, u j ω in s)
  proof: by
  refine le_hittingBtwn ?_ ω
  by_contra h
  rw [Set.Icc_eq_empty_of_lt (not_le.mp h)] at h_exists
  simp at h_exists

中文:
定理 le_hittingBtwn_of_exists
  条件: {m : ι} (h_存在 : 存在 j in Set.Icc n m, u j ω in s)
  证明: by
  refine le_hittingBtwn ?_ ω
  by_contra h
  rw [Set.Icc_eq_empty_of_lt (not_le.mp h)] at h_exists
  simp at h_exists

Depends on / 依赖: Icc_eq_empty_of_lt, Set.Icc_eq_empty_of_lt, h_exists, le_hittingBtwn, not_le, not_le.mp
-/
theorem le_hittingBtwn_of_exists {m : ι} (h_exists : exists j in Set.Icc n m, u j ω in s) :
    n <= hittingBtwn u s n m ω := by
  refine le_hittingBtwn ?_ ω
  by_contra h
  rw [Set.Icc_eq_empty_of_lt (not_le.mp h)] at h_exists
  simp at h_exists

/--
theorem `hittingBtwn_mem_Icc` / 定理 `hittingBtwn_mem_Icc`

English:
theorem hittingBtwn_mem_Icc
  given: {m : ι} (hnm : n <= m) (ω : Ω)
  statement: hittingBtwn u s n m ω in Set.Icc n m
  proof: ⟨le_hittingBtwn hnm ω, hittingBtwn_le ω⟩

中文:
定理 hittingBtwn_mem_Icc
  条件: {m : ι} (hnm : n <= m) (ω : Ω)
  结论: hittingBtwn u s n m ω in Set.Icc n m
  证明: ⟨le_hittingBtwn hnm ω, hittingBtwn_le ω⟩

Depends on / 依赖: hittingBtwn_le, le_hittingBtwn
-/
theorem hittingBtwn_mem_Icc {m : ι} (hnm : n <= m) (ω : Ω) : hittingBtwn u s n m ω in Set.Icc n m :=
  ⟨le_hittingBtwn hnm ω, hittingBtwn_le ω⟩

/--
theorem `hittingBtwn_mem_set` / 定理 `hittingBtwn_mem_set`

English:
theorem hittingBtwn_mem_set
  given: [WellFoundedLT ι] {m : ι} (h_exists : exists j in Set.Icc n m, u j ω in s)
  proof: by
  simp_rw [hittingBtwn, if_pos h_exists]
  have h_nonempty : (Set.Icc n m inter {i : ι | u i ω in s}).Nonempty := by
    obtain ⟨k, hk₁, hk₂⟩ := h_exists
    exact ⟨k, Set.mem_inter hk₁ hk₂⟩
  have h_mem := csInf_mem h_nonempty
  rw [Set.mem_inter_iff] at h_mem
  exact h_mem.2

中文:
定理 hittingBtwn_mem_set
  条件: [WellFoundedLT ι] {m : ι} (h_存在 : 存在 j in Set.Icc n m, u j ω in s)
  证明: by
  simp_rw [hittingBtwn, if_pos h_exists]
  have h_nonempty : (Set.Icc n m inter {i : ι | u i ω in s}).Nonempty := by
    obtain ⟨k, hk₁, hk₂⟩ := h_exists
    exact ⟨k, Set.mem_inter hk₁ hk₂⟩
  have h_mem := csInf_mem h_nonempty
  rw [Set.mem_inter_iff] at h_mem
  exact h_mem.2

Depends on / 依赖: Nonempty, Set.Icc, Set.mem_inter, Set.mem_inter_iff, csInf_mem, h_exists, h_mem, h_nonempty, hittingBtwn, if_pos, mem_inter, mem_inter_iff, simp_rw
-/
theorem hittingBtwn_mem_set [WellFoundedLT ι] {m : ι} (h_exists : exists j in Set.Icc n m, u j ω in s) :
    u (hittingBtwn u s n m ω) ω in s := by
  simp_rw [hittingBtwn, if_pos h_exists]
  have h_nonempty : (Set.Icc n m inter {i : ι | u i ω in s}).Nonempty := by
    obtain ⟨k, hk₁, hk₂⟩ := h_exists
    exact ⟨k, Set.mem_inter hk₁ hk₂⟩
  have h_mem := csInf_mem h_nonempty
  rw [Set.mem_inter_iff] at h_mem
  exact h_mem.2

/--
lemma `hittingAfter_mem_set` / 引理 `hittingAfter_mem_set`

English:
lemma hittingAfter_mem_set
  given: [WellFoundedLT ι] (h_exists : exists j, n <= j ∧ u j ω in s)
  proof: by
  rw [hittingAfter]; rw [if_pos h_exists]
  have h_nonempty : {i : ι | n <= i ∧ u i ω in s}.Nonempty := by
    obtain ⟨k, hk₁, hk₂⟩ := h_exists
    exact ⟨k, Set.mem_inter hk₁ hk₂⟩
  exact (csInf_mem h_nonempty).2

中文:
引理 hittingAfter_mem_set
  条件: [WellFoundedLT ι] (h_存在 : 存在 j, n <= j ∧ u j ω in s)
  证明: by
  rw [hittingAfter]; rw [if_pos h_exists]
  have h_nonempty : {i : ι | n <= i ∧ u i ω in s}.Nonempty := by
    obtain ⟨k, hk₁, hk₂⟩ := h_exists
    exact ⟨k, Set.mem_inter hk₁ hk₂⟩
  exact (csInf_mem h_nonempty).2

Depends on / 依赖: Nonempty, Set.mem_inter, csInf_mem, h_exists, h_nonempty, hittingAfter, if_pos, mem_inter
-/
lemma hittingAfter_mem_set [WellFoundedLT ι] (h_exists : exists j, n <= j ∧ u j ω in s) :
    u (hittingAfter u s n ω).untopA ω in s := by
  rw [hittingAfter]; rw [if_pos h_exists]
  have h_nonempty : {i : ι | n <= i ∧ u i ω in s}.Nonempty := by
    obtain ⟨k, hk₁, hk₂⟩ := h_exists
    exact ⟨k, Set.mem_inter hk₁ hk₂⟩
  exact (csInf_mem h_nonempty).2

/--
theorem `hittingBtwn_mem_set_of_hittingBtwn_lt` / 定理 `hittingBtwn_mem_set_of_hittingBtwn_lt`

English:
theorem hittingBtwn_mem_set_of_hittingBtwn_lt
  statement: [WellFoundedLT ι] {m : ι}
  proof: by
  by_cases h : exists j in Set.Icc n m, u j ω in s
  · exact hittingBtwn_mem_set h
  · simp_rw [hittingBtwn, if_neg h] at hl
    exact False.elim (hl.ne rfl)

中文:
定理 hittingBtwn_mem_set_of_hittingBtwn_lt
  结论: [WellFoundedLT ι] {m : ι}
  证明: by
  by_cases h : exists j in Set.Icc n m, u j ω in s
  · exact hittingBtwn_mem_set h
  · simp_rw [hittingBtwn, if_neg h] at hl
    exact False.elim (hl.ne rfl)

Depends on / 依赖: False.elim, Set.Icc, hittingBtwn, hittingBtwn_mem_set, hl.ne, if_neg, simp_rw
-/
theorem hittingBtwn_mem_set_of_hittingBtwn_lt [WellFoundedLT ι] {m : ι}
    (hl : hittingBtwn u s n m ω < m) :
    u (hittingBtwn u s n m ω) ω in s := by
  by_cases h : exists j in Set.Icc n m, u j ω in s
  · exact hittingBtwn_mem_set h
  · simp_rw [hittingBtwn, if_neg h] at hl
    exact False.elim (hl.ne rfl)

/--
lemma `hittingAfter_mem_set_of_ne_top` / 引理 `hittingAfter_mem_set_of_ne_top`

English:
lemma hittingAfter_mem_set_of_ne_top
  given: [WellFoundedLT ι] (hl : hittingAfter u s n ω != ⊤)
  proof: by
  simp only [ne_eq, hittingAfter_eq_top_iff, not_forall, not_not] at hl
  obtain ⟨j, hj₁, hj₂⟩ := hl
  exact hittingAfter_mem_set ⟨j, hj₁, hj₂⟩

中文:
引理 hittingAfter_mem_set_of_ne_top
  条件: [WellFoundedLT ι] (hl : hittingAfter u s n ω != ⊤)
  证明: by
  simp only [ne_eq, hittingAfter_eq_top_iff, not_forall, not_not] at hl
  obtain ⟨j, hj₁, hj₂⟩ := hl
  exact hittingAfter_mem_set ⟨j, hj₁, hj₂⟩

Depends on / 依赖: hittingAfter_eq_top_iff, hittingAfter_mem_set, ne_eq, not_forall, not_not
-/
lemma hittingAfter_mem_set_of_ne_top [WellFoundedLT ι] (hl : hittingAfter u s n ω != ⊤) :
    u (hittingAfter u s n ω).untopA ω in s := by
  simp only [ne_eq, hittingAfter_eq_top_iff, not_forall, not_not] at hl
  obtain ⟨j, hj₁, hj₂⟩ := hl
  exact hittingAfter_mem_set ⟨j, hj₁, hj₂⟩

/--
theorem `hittingBtwn_le_of_mem` / 定理 `hittingBtwn_le_of_mem`

English:
theorem hittingBtwn_le_of_mem
  given: {m : ι} (hin : n <= i) (him : i <= m) (his : u i ω in s)
  proof: by
  have h_exists : exists k in Set.Icc n m, u k ω in s := ⟨i, ⟨hin, him⟩, his⟩
  simp_rw [hittingBtwn, if_pos h_exists]
  exact csInf_le (BddBelow.inter_of_left bddBelow_Icc) (Set.mem_inter ⟨hin, him⟩ his)

中文:
定理 hittingBtwn_le_of_mem
  条件: {m : ι} (hin : n <= i) (him : i <= m) (his : u i ω in s)
  证明: by
  have h_exists : exists k in Set.Icc n m, u k ω in s := ⟨i, ⟨hin, him⟩, his⟩
  simp_rw [hittingBtwn, if_pos h_exists]
  exact csInf_le (BddBelow.inter_of_left bddBelow_Icc) (Set.mem_inter ⟨hin, him⟩ his)

Depends on / 依赖: BddBelow, BddBelow.inter_of_left, Set.Icc, Set.mem_inter, bddBelow_Icc, csInf_le, h_exists, hittingBtwn, if_pos, inter_of_left, mem_inter, simp_rw
-/
theorem hittingBtwn_le_of_mem {m : ι} (hin : n <= i) (him : i <= m) (his : u i ω in s) :
    hittingBtwn u s n m ω <= i := by
  have h_exists : exists k in Set.Icc n m, u k ω in s := ⟨i, ⟨hin, him⟩, his⟩
  simp_rw [hittingBtwn, if_pos h_exists]
  exact csInf_le (BddBelow.inter_of_left bddBelow_Icc) (Set.mem_inter ⟨hin, him⟩ his)

/--
lemma `hittingAfter_le_of_mem` / 引理 `hittingAfter_le_of_mem`

English:
lemma hittingAfter_le_of_mem
  given: (hin : n <= i) (his : u i ω in s)
  proof: by
  have h_exists : exists k, n <= k ∧ u k ω in s := ⟨i, hin, his⟩
  rw [hittingAfter]; rw [if_pos h_exists]
  exact_mod_cast csInf_le (BddBelow.inter_of_left bddBelow_Ici) (Set.mem_inter hin his)

中文:
引理 hittingAfter_le_of_mem
  条件: (hin : n <= i) (his : u i ω in s)
  证明: by
  have h_exists : exists k, n <= k ∧ u k ω in s := ⟨i, hin, his⟩
  rw [hittingAfter]; rw [if_pos h_exists]
  exact_mod_cast csInf_le (BddBelow.inter_of_left bddBelow_Ici) (Set.mem_inter hin his)

Depends on / 依赖: BddBelow, BddBelow.inter_of_left, Set.mem_inter, bddBelow_Ici, csInf_le, h_exists, hittingAfter, if_pos, inter_of_left, mem_inter
-/
lemma hittingAfter_le_of_mem (hin : n <= i) (his : u i ω in s) :
    hittingAfter u s n ω <= i := by
  have h_exists : exists k, n <= k ∧ u k ω in s := ⟨i, hin, his⟩
  rw [hittingAfter]; rw [if_pos h_exists]
  exact_mod_cast csInf_le (BddBelow.inter_of_left bddBelow_Ici) (Set.mem_inter hin his)

/--
theorem `hittingBtwn_le_iff_of_exists` / 定理 `hittingBtwn_le_iff_of_exists`

English:
theorem hittingBtwn_le_iff_of_exists
  statement: [WellFoundedLT ι] {m : ι}
  proof: by
  constructor <;> intro h'
  · exact ⟨hittingBtwn u s n m ω, ⟨le_hittingBtwn_of_exists h_exists, h'⟩,
      hittingBtwn_mem_set h_exists⟩
  · have h'' : exists k in Set.Icc n (min m i), u k ω in s := by
      obtain ⟨k₁, hk₁_mem, hk₁_s⟩ := h_exists
      obtain ⟨k₂, hk₂_mem, hk₂_s⟩ := h'
      re

中文:
定理 hittingBtwn_le_iff_of_exists
  结论: [WellFoundedLT ι] {m : ι}
  证明: by
  constructor <;> intro h'
  · exact ⟨hittingBtwn u s n m ω, ⟨le_hittingBtwn_of_exists h_exists, h'⟩,
      hittingBtwn_mem_set h_exists⟩
  · have h'' : exists k in Set.Icc n (min m i), u k ω in s := by
      obtain ⟨k₁, hk₁_mem, hk₁_s⟩ := h_exists
      obtain ⟨k₂, hk₂_mem, hk₂_s⟩ := h'
      re

Depends on / 依赖: Set.Icc, h_exists, hittingBtwn, hittingBtwn_, hittingBtwn_mem_set, le_hittingBtwn_of_exists, le_min, le_trans, min_le_min, min_le_right, min_rec
-/
theorem hittingBtwn_le_iff_of_exists [WellFoundedLT ι] {m : ι}
    (h_exists : exists j in Set.Icc n m, u j ω in s) :
    hittingBtwn u s n m ω <= i ↔ exists j in Set.Icc n i, u j ω in s := by
  constructor <;> intro h'
  · exact ⟨hittingBtwn u s n m ω, ⟨le_hittingBtwn_of_exists h_exists, h'⟩,
      hittingBtwn_mem_set h_exists⟩
  · have h'' : exists k in Set.Icc n (min m i), u k ω in s := by
      obtain ⟨k₁, hk₁_mem, hk₁_s⟩ := h_exists
      obtain ⟨k₂, hk₂_mem, hk₂_s⟩ := h'
      refine ⟨min k₁ k₂, ⟨le_min hk₁_mem.1 hk₂_mem.1, min_le_min hk₁_mem.2 hk₂_mem.2⟩, ?_⟩
      exact min_rec' (fun j => u j ω in s) hk₁_s hk₂_s
    obtain ⟨k, hk₁, hk₂⟩ := h''
    refine le_trans ?_ (hk₁.2.trans (min_le_right _ _))
    exact hittingBtwn_le_of_mem hk₁.1 (hk₁.2.trans (min_le_left _ _)) hk₂

/--
lemma `hittingAfter_le_iff` / 引理 `hittingAfter_le_iff`

English:
lemma hittingAfter_le_iff
  given: [WellFoundedLT ι]
  proof: by
  constructor <;> intro h'
  · have h_top : hittingAfter u s n ω != ⊤ := fun h => by simp [h] at h'
    have h_le := le_hittingAfter (u := u) (s := s) (n := n) ω
    refine ⟨(hittingAfter u s n ω).untopA, ?_, hittingAfter_mem_set_of_ne_top h_top⟩
    lift (hittingAfter u s n ω) to ι using h_top w

中文:
引理 hittingAfter_le_iff
  条件: [WellFoundedLT ι]
  证明: by
  constructor <;> intro h'
  · have h_top : hittingAfter u s n ω != ⊤ := fun h => by simp [h] at h'
    have h_le := le_hittingAfter (u := u) (s := s) (n := n) ω
    refine ⟨(hittingAfter u s n ω).untopA, ?_, hittingAfter_mem_set_of_ne_top h_top⟩
    lift (hittingAfter u s n ω) to ι using h_top w

Depends on / 依赖: WithTop, h_le, h_top, hittingAfter, hittingAfter_le_of_mem, hittingAfter_mem_set_of_ne_top, le_hittingAfter, le_trans, mod_cast, untopA
-/
lemma hittingAfter_le_iff [WellFoundedLT ι] :
    hittingAfter u s n ω <= i ↔ exists j in Set.Icc n i, u j ω in s := by
  constructor <;> intro h'
  · have h_top : hittingAfter u s n ω != ⊤ := fun h => by simp [h] at h'
    have h_le := le_hittingAfter (u := u) (s := s) (n := n) ω
    refine ⟨(hittingAfter u s n ω).untopA, ?_, hittingAfter_mem_set_of_ne_top h_top⟩
    lift (hittingAfter u s n ω) to ι using h_top with i'
    norm_cast at h' h_le
  · obtain ⟨j, hj₁, hj₂⟩ := h'
    refine le_trans ?_ (mod_cast hj₁.2 : (j : WithTop ι) <= i)
    exact hittingAfter_le_of_mem hj₁.1 hj₂

/--
theorem `hittingBtwn_le_iff_of_lt` / 定理 `hittingBtwn_le_iff_of_lt`

English:
theorem hittingBtwn_le_iff_of_lt
  given: [WellFoundedLT ι] {m : ι} (i : ι) (hi : i < m)
  proof: by
  by_cases h_exists : exists j in Set.Icc n m, u j ω in s
  · rw [hittingBtwn_le_iff_of_exists h_exists]
  · simp_rw [hittingBtwn, if_neg h_exists]
    push Not at h_exists
    simp only [not_le.mpr hi, Set.mem_Icc, false_iff, not_exists, not_and, and_imp]
    exact fun k hkn hki => h_exists k ⟨h

中文:
定理 hittingBtwn_le_iff_of_lt
  条件: [WellFoundedLT ι] {m : ι} (i : ι) (hi : i < m)
  证明: by
  by_cases h_exists : exists j in Set.Icc n m, u j ω in s
  · rw [hittingBtwn_le_iff_of_exists h_exists]
  · simp_rw [hittingBtwn, if_neg h_exists]
    push Not at h_exists
    simp only [not_le.mpr hi, Set.mem_Icc, false_iff, not_exists, not_and, and_imp]
    exact fun k hkn hki => h_exists k ⟨h

Depends on / 依赖: Set.Icc, Set.mem_Icc, and_imp, false_iff, h_exists, hi.le, hittingBtwn, hittingBtwn_le_iff_of_exists, hki.trans, if_neg, mem_Icc, not_and, not_exists, not_le, not_le.mpr, simp_rw
-/
theorem hittingBtwn_le_iff_of_lt [WellFoundedLT ι] {m : ι} (i : ι) (hi : i < m) :
    hittingBtwn u s n m ω <= i ↔ exists j in Set.Icc n i, u j ω in s := by
  by_cases h_exists : exists j in Set.Icc n m, u j ω in s
  · rw [hittingBtwn_le_iff_of_exists h_exists]
  · simp_rw [hittingBtwn, if_neg h_exists]
    push Not at h_exists
    simp only [not_le.mpr hi, Set.mem_Icc, false_iff, not_exists, not_and, and_imp]
    exact fun k hkn hki => h_exists k ⟨hkn, hki.trans hi.le⟩

/--
theorem `hittingBtwn_lt_iff` / 定理 `hittingBtwn_lt_iff`

English:
theorem hittingBtwn_lt_iff
  given: {m : ι} (i : ι) (hi : i <= m)
  proof: by
  constructor <;> intro h'
  · have h : exists j in Set.Icc n m, u j ω in s := by
      by_contra h
      simp_rw [hittingBtwn, if_neg h, ← not_le] at h'
      exact h' hi
    have hni : n < i := (le_hittingBtwn_of_exists h).trans_lt h'
    have h_le := le_hittingBtwn (u := u) (s := s) (hni.le.tr

中文:
定理 hittingBtwn_lt_iff
  条件: {m : ι} (i : ι) (hi : i <= m)
  证明: by
  constructor <;> intro h'
  · have h : exists j in Set.Icc n m, u j ω in s := by
      by_contra h
      simp_rw [hittingBtwn, if_neg h, ← not_le] at h'
      exact h' hi
    have hni : n < i := (le_hittingBtwn_of_exists h).trans_lt h'
    have h_le := le_hittingBtwn (u := u) (s := s) (hni.le.tr

Depends on / 依赖: Set.Icc, Set.mem_Icc, Set.mem_inter_iff, Set.mem_ofPred_eq, csInf_lt_iff, h_le, hittingBtwn, hni.le.trans, if_neg, if_pos, le_hittingBtwn, le_hittingBtwn_of_exists, mem_Icc, mem_inter_iff, mem_lowerBounds, mem_ofPred_eq, not_le, rotate_left, simp_rw, trans_lt
-/
theorem hittingBtwn_lt_iff {m : ι} (i : ι) (hi : i <= m) :
    hittingBtwn u s n m ω < i ↔ exists j in Set.Ico n i, u j ω in s := by
  constructor <;> intro h'
  · have h : exists j in Set.Icc n m, u j ω in s := by
      by_contra h
      simp_rw [hittingBtwn, if_neg h, ← not_le] at h'
      exact h' hi
    have hni : n < i := (le_hittingBtwn_of_exists h).trans_lt h'
    have h_le := le_hittingBtwn (u := u) (s := s) (hni.le.trans hi) ω
    rw [hittingBtwn]; rw [if_pos h]; rw [csInf_lt_iff] at h'
    rotate_left
    · exact ⟨n, by simp [mem_lowerBounds]; grind⟩
    · exact h
    simp only [Set.mem_inter_iff, Set.mem_Icc, Set.mem_ofPred_eq] at h'
    obtain ⟨j, ⟨⟨hnj, hjm⟩, hj_mem⟩, hji⟩ := h'
    exact ⟨j, ⟨hnj, hji⟩, hj_mem⟩
  · obtain ⟨k, hk₁, hk₂⟩ := h'
    refine lt_of_le_of_lt ?_ hk₁.2
    exact hittingBtwn_le_of_mem hk₁.1 (hk₁.2.le.trans hi) hk₂

/--
lemma `hittingAfter_lt_iff` / 引理 `hittingAfter_lt_iff`

English:
lemma hittingAfter_lt_iff
  proof: by
  constructor <;> intro h'
  · have h_top : hittingAfter u s n ω != ⊤ := fun h => by simp [h] at h'
    have h_exists : exists j, n <= j ∧ u j ω in s := by
      rw [ne_eq]; rw [hittingAfter_eq_top_iff] at h_top
      push Not at h_top
      exact h_top
    have h_le := le_hittingAfter (u := u) (

中文:
引理 hittingAfter_lt_iff
  证明: by
  constructor <;> intro h'
  · have h_top : hittingAfter u s n ω != ⊤ := fun h => by simp [h] at h'
    have h_exists : exists j, n <= j ∧ u j ω in s := by
      rw [ne_eq]; rw [hittingAfter_eq_top_iff] at h_top
      push Not at h_top
      exact h_top
    have h_le := le_hittingAfter (u := u) (

Depends on / 依赖: Set.mem_ofPred_eq, csInf_lt_iff, h_exists, h_le, h_top, hittingAfter, hittingAfter_eq_top_iff, if_pos, le_hittingAfter, mem_lowerBounds, mem_ofPred_eq, ne_eq, rotate_left
-/
lemma hittingAfter_lt_iff :
    hittingAfter u s n ω < i ↔ exists j in Set.Ico n i, u j ω in s := by
  constructor <;> intro h'
  · have h_top : hittingAfter u s n ω != ⊤ := fun h => by simp [h] at h'
    have h_exists : exists j, n <= j ∧ u j ω in s := by
      rw [ne_eq]; rw [hittingAfter_eq_top_iff] at h_top
      push Not at h_top
      exact h_top
    have h_le := le_hittingAfter (u := u) (s := s) (n := n) ω
    rw [hittingAfter]; rw [if_pos h_exists] at h'
    norm_cast at h'
    rw [csInf_lt_iff] at h'
    rotate_left
    · exact ⟨n, by simp [mem_lowerBounds]; grind⟩
    · exact h_exists
    simp only [Set.mem_ofPred_eq] at h'
    obtain ⟨j, hj₁, hj₂⟩ := h'
    exact ⟨j, ⟨hj₁.1, hj₂⟩, hj₁.2⟩
  · obtain ⟨j, hj₁, hj₂⟩ := h'
    refine lt_of_le_of_lt ?_ (mod_cast hj₁.2 : (j : WithTop ι) < i)
    exact hittingAfter_le_of_mem hj₁.1 hj₂

/--
theorem `hittingBtwn_eq_hittingBtwn_of_exists` / 定理 `hittingBtwn_eq_hittingBtwn_of_exists`

English:
theorem hittingBtwn_eq_hittingBtwn_of_exists
  statement: {m₁ m₂ : ι} (h : m₁ <= m₂)
  proof: by
  simp only [hittingBtwn, if_pos h']
  obtain ⟨j, hj₁, hj₂⟩ := h'
  rw [if_pos]
  · refine le_antisymm ?_ (by gcongr; exacts [bddBelow_Icc.inter_of_left, ⟨j, hj₁, hj₂⟩])
    refine le_csInf ⟨j, Set.Icc_subset_Icc_right h hj₁, hj₂⟩ fun i hi => ?_
    by_cases hi' : i <= m₁
    · exact csInf_le bdd

中文:
定理 hittingBtwn_eq_hittingBtwn_of_exists
  结论: {m₁ m₂ : ι} (h : m₁ <= m₂)
  证明: by
  simp only [hittingBtwn, if_pos h']
  obtain ⟨j, hj₁, hj₂⟩ := h'
  rw [if_pos]
  · refine le_antisymm ?_ (by gcongr; exacts [bddBelow_Icc.inter_of_left, ⟨j, hj₁, hj₂⟩])
    refine le_csInf ⟨j, Set.Icc_subset_Icc_right h hj₁, hj₂⟩ fun i hi => ?_
    by_cases hi' : i <= m₁
    · exact csInf_le bdd

Depends on / 依赖: Icc_subset_Icc_right, Set.Icc_subset_Icc_right, bddBelow_Icc, bddBelow_Icc.inter_of_left, csInf_le, exacts, hittingBtwn, if_pos, inter_of_left, le_antisymm, le_csInf, le_of_not_ge
-/
theorem hittingBtwn_eq_hittingBtwn_of_exists {m₁ m₂ : ι} (h : m₁ <= m₂)
    (h' : exists j in Set.Icc n m₁, u j ω in s) : hittingBtwn u s n m₁ ω = hittingBtwn u s n m₂ ω := by
  simp only [hittingBtwn, if_pos h']
  obtain ⟨j, hj₁, hj₂⟩ := h'
  rw [if_pos]
  · refine le_antisymm ?_ (by gcongr; exacts [bddBelow_Icc.inter_of_left, ⟨j, hj₁, hj₂⟩])
    refine le_csInf ⟨j, Set.Icc_subset_Icc_right h hj₁, hj₂⟩ fun i hi => ?_
    by_cases hi' : i <= m₁
    · exact csInf_le bddBelow_Icc.inter_of_left ⟨⟨hi.1.1, hi'⟩, hi.2⟩
    · change j in {i | u i ω in s} at hj₂
      exact ((csInf_le bddBelow_Icc.inter_of_left ⟨hj₁, hj₂⟩).trans hj₁.2).trans (le_of_not_ge hi')
  exact ⟨j, ⟨hj₁.1, hj₁.2.trans h⟩, hj₂⟩

/--
lemma `hittingBtwn_anti` / 引理 `hittingBtwn_anti`

English:
lemma hittingBtwn_anti
  given: (u : ι -> Ω -> β) (n m : ι)
  statement: Antitone (hittingBtwn u · n m)
  proof: by
  intro E F hEF ω
  simp only [hittingBtwn_def]
  split_ifs with hF hE hE
  · gcongr
    exact ⟨n, by simp [mem_lowerBounds]; grind⟩
  · obtain ⟨t, ht⟩ := hF
    exact csInf_le_of_le ⟨n, by simp [mem_lowerBounds]; grind⟩ ht ht.1.2
  · obtain ⟨t, ht⟩ := hE
    exact absurd ⟨t, ht.1, hEF ht.2⟩ hF
 

中文:
引理 hittingBtwn_anti
  条件: (u : ι -> Ω -> β) (n m : ι)
  结论: Antitone (hittingBtwn u · n m)
  证明: by
  intro E F hEF ω
  simp only [hittingBtwn_def]
  split_ifs with hF hE hE
  · gcongr
    exact ⟨n, by simp [mem_lowerBounds]; grind⟩
  · obtain ⟨t, ht⟩ := hF
    exact csInf_le_of_le ⟨n, by simp [mem_lowerBounds]; grind⟩ ht ht.1.2
  · obtain ⟨t, ht⟩ := hE
    exact absurd ⟨t, ht.1, hEF ht.2⟩ hF
 

Depends on / 依赖: absurd, csInf_le_of_le, hittingBtwn_def, mem_lowerBounds, split_ifs
-/
lemma hittingBtwn_anti (u : ι -> Ω -> β) (n m : ι) : Antitone (hittingBtwn u · n m) := by
  intro E F hEF ω
  simp only [hittingBtwn_def]
  split_ifs with hF hE hE
  · gcongr
    exact ⟨n, by simp [mem_lowerBounds]; grind⟩
  · obtain ⟨t, ht⟩ := hF
    exact csInf_le_of_le ⟨n, by simp [mem_lowerBounds]; grind⟩ ht ht.1.2
  · obtain ⟨t, ht⟩ := hE
    exact absurd ⟨t, ht.1, hEF ht.2⟩ hF
  · simp

/--
lemma `hittingAfter_anti` / 引理 `hittingAfter_anti`

English:
lemma hittingAfter_anti
  given: (u : ι -> Ω -> β) (n : ι)
  statement: Antitone (hittingAfter u · n)
  proof: by
  intro E F hEF ω
  simp only [hittingAfter_def]
  split_ifs with hF hE hE
  · norm_cast
    gcongr
    exact ⟨n, by simp only [mem_lowerBounds]; grind⟩
  · simp
  · obtain ⟨t, ht⟩ := hE
    exact absurd ⟨t, ht.1, hEF ht.2⟩ hF
  · simp

中文:
引理 hittingAfter_anti
  条件: (u : ι -> Ω -> β) (n : ι)
  结论: Antitone (hittingAfter u · n)
  证明: by
  intro E F hEF ω
  simp only [hittingAfter_def]
  split_ifs with hF hE hE
  · norm_cast
    gcongr
    exact ⟨n, by simp only [mem_lowerBounds]; grind⟩
  · simp
  · obtain ⟨t, ht⟩ := hE
    exact absurd ⟨t, ht.1, hEF ht.2⟩ hF
  · simp

Depends on / 依赖: absurd, hittingAfter_def, mem_lowerBounds, split_ifs
-/
lemma hittingAfter_anti (u : ι -> Ω -> β) (n : ι) : Antitone (hittingAfter u · n) := by
  intro E F hEF ω
  simp only [hittingAfter_def]
  split_ifs with hF hE hE
  · norm_cast
    gcongr
    exact ⟨n, by simp only [mem_lowerBounds]; grind⟩
  · simp
  · obtain ⟨t, ht⟩ := hE
    exact absurd ⟨t, ht.1, hEF ht.2⟩ hF
  · simp

/--
lemma `hittingBtwn_apply_anti` / 引理 `hittingBtwn_apply_anti`

English:
lemma hittingBtwn_apply_anti
  given: (u : ι -> Ω -> β) (n m : ι) (ω : Ω)
  proof: fun _ _ hEF => hittingBtwn_anti u n m hEF ω

中文:
引理 hittingBtwn_apply_anti
  条件: (u : ι -> Ω -> β) (n m : ι) (ω : Ω)
  证明: fun _ _ hEF => hittingBtwn_anti u n m hEF ω

Depends on / 依赖: hittingBtwn_anti
-/
lemma hittingBtwn_apply_anti (u : ι -> Ω -> β) (n m : ι) (ω : Ω) :
    Antitone (hittingBtwn u · n m ω) := fun _ _ hEF => hittingBtwn_anti u n m hEF ω

/--
lemma `hittingAfter_apply_anti` / 引理 `hittingAfter_apply_anti`

English:
lemma hittingAfter_apply_anti
  given: (u : ι -> Ω -> β) (n : ι) (ω : Ω)
  proof: fun _ _ hst => hittingAfter_anti u n hst ω

中文:
引理 hittingAfter_apply_anti
  条件: (u : ι -> Ω -> β) (n : ι) (ω : Ω)
  证明: fun _ _ hst => hittingAfter_anti u n hst ω

Depends on / 依赖: hittingAfter_anti
-/
lemma hittingAfter_apply_anti (u : ι -> Ω -> β) (n : ι) (ω : Ω) :
    Antitone (hittingAfter u · n ω) := fun _ _ hst => hittingAfter_anti u n hst ω

/--
theorem `hittingBtwn_mono_right` / 定理 `hittingBtwn_mono_right`

English:
theorem hittingBtwn_mono_right
  given: (u : ι -> Ω -> β) (s : Set β) (n : ι)
  proof: by
  intro m₁ m₂ hm
  by_cases h : exists j in Set.Icc n m₁, u j ω in s
  · exact (hittingBtwn_eq_hittingBtwn_of_exists hm h).le
  · simp_rw [hittingBtwn, if_neg h]
    split_ifs with h'
    · obtain ⟨j, hj₁, hj₂⟩ := h'
      refine le_csInf ⟨j, hj₁, hj₂⟩ ?_
      by_contra! ⟨i, hi₁, hi₂⟩
      exac

中文:
定理 hittingBtwn_mono_right
  条件: (u : ι -> Ω -> β) (s : Set β) (n : ι)
  证明: by
  intro m₁ m₂ hm
  by_cases h : exists j in Set.Icc n m₁, u j ω in s
  · exact (hittingBtwn_eq_hittingBtwn_of_exists hm h).le
  · simp_rw [hittingBtwn, if_neg h]
    split_ifs with h'
    · obtain ⟨j, hj₁, hj₂⟩ := h'
      refine le_csInf ⟨j, hj₁, hj₂⟩ ?_
      by_contra! ⟨i, hi₁, hi₂⟩
      exac

Depends on / 依赖: Set.Icc, hittingBtwn, hittingBtwn_eq_hittingBtwn_of_exists, if_neg, le_csInf, simp_rw, split_ifs
-/
theorem hittingBtwn_mono_right (u : ι -> Ω -> β) (s : Set β) (n : ι) :
    Monotone (hittingBtwn u s n · ω) := by
  intro m₁ m₂ hm
  by_cases h : exists j in Set.Icc n m₁, u j ω in s
  · exact (hittingBtwn_eq_hittingBtwn_of_exists hm h).le
  · simp_rw [hittingBtwn, if_neg h]
    split_ifs with h'
    · obtain ⟨j, hj₁, hj₂⟩ := h'
      refine le_csInf ⟨j, hj₁, hj₂⟩ ?_
      by_contra! ⟨i, hi₁, hi₂⟩
      exact h ⟨i, ⟨hi₁.1.1, hi₂.le⟩, hi₁.2⟩
    · exact hm

/--
lemma `hittingBtwn_mono_left` / 引理 `hittingBtwn_mono_left`

English:
lemma hittingBtwn_mono_left
  given: (u : ι -> Ω -> β) (s : Set β) (m : ι)
  proof: by
  intro n n' hnn' ω
  simp only [hittingBtwn]
  split_ifs with h_n h_n' h_n'
  · gcongr
    exacts [⟨n, by simp [mem_lowerBounds]; grind⟩]
  · obtain ⟨t, ht⟩ := h_n
    exact csInf_le_of_le ⟨n, by simp [mem_lowerBounds]; grind⟩ ht ht.1.2
  · have ⟨t, ht⟩ := h_n'
    exact absurd ⟨t, ⟨hnn'.trans h

中文:
引理 hittingBtwn_mono_left
  条件: (u : ι -> Ω -> β) (s : Set β) (m : ι)
  证明: by
  intro n n' hnn' ω
  simp only [hittingBtwn]
  split_ifs with h_n h_n' h_n'
  · gcongr
    exacts [⟨n, by simp [mem_lowerBounds]; grind⟩]
  · obtain ⟨t, ht⟩ := h_n
    exact csInf_le_of_le ⟨n, by simp [mem_lowerBounds]; grind⟩ ht ht.1.2
  · have ⟨t, ht⟩ := h_n'
    exact absurd ⟨t, ⟨hnn'.trans h

Depends on / 依赖: absurd, csInf_le_of_le, exacts, hittingBtwn, mem_lowerBounds, split_ifs
-/
lemma hittingBtwn_mono_left (u : ι -> Ω -> β) (s : Set β) (m : ι) :
    Monotone (hittingBtwn u s · m) := by
  intro n n' hnn' ω
  simp only [hittingBtwn]
  split_ifs with h_n h_n' h_n'
  · gcongr
    exacts [⟨n, by simp [mem_lowerBounds]; grind⟩]
  · obtain ⟨t, ht⟩ := h_n
    exact csInf_le_of_le ⟨n, by simp [mem_lowerBounds]; grind⟩ ht ht.1.2
  · have ⟨t, ht⟩ := h_n'
    exact absurd ⟨t, ⟨hnn'.trans ht.1.1, ht.1.2⟩, ht.2⟩ h_n
  · simp

/--
lemma `hittingAfter_mono` / 引理 `hittingAfter_mono`

English:
lemma hittingAfter_mono
  given: (u : ι -> Ω -> β) (s : Set β)
  statement: Monotone (hittingAfter u s)
  proof: by
  intro n m hnm ω
  simp only [hittingAfter]
  split_ifs with h_n h_m h_m
  · norm_cast
    gcongr
    exacts [⟨n, by simp [mem_lowerBounds]; grind⟩]
  · simp
  · have ⟨t, ht⟩ := h_m
    exact absurd ⟨t, hnm.trans ht.1, ht.2⟩ h_n
  · simp

中文:
引理 hittingAfter_mono
  条件: (u : ι -> Ω -> β) (s : Set β)
  结论: Monotone (hittingAfter u s)
  证明: by
  intro n m hnm ω
  simp only [hittingAfter]
  split_ifs with h_n h_m h_m
  · norm_cast
    gcongr
    exacts [⟨n, by simp [mem_lowerBounds]; grind⟩]
  · simp
  · have ⟨t, ht⟩ := h_m
    exact absurd ⟨t, hnm.trans ht.1, ht.2⟩ h_n
  · simp

Depends on / 依赖: absurd, exacts, hittingAfter, hnm.trans, mem_lowerBounds, split_ifs
-/
lemma hittingAfter_mono (u : ι -> Ω -> β) (s : Set β) : Monotone (hittingAfter u s) := by
  intro n m hnm ω
  simp only [hittingAfter]
  split_ifs with h_n h_m h_m
  · norm_cast
    gcongr
    exacts [⟨n, by simp [mem_lowerBounds]; grind⟩]
  · simp
  · have ⟨t, ht⟩ := h_m
    exact absurd ⟨t, hnm.trans ht.1, ht.2⟩ h_n
  · simp

/--
lemma `hittingBtwn_apply_mono_right` / 引理 `hittingBtwn_apply_mono_right`

English:
lemma hittingBtwn_apply_mono_right
  given: (u : ι -> Ω -> β) (s : Set β) (n : ι) (ω : Ω)
  proof: fun _ _ hnn' => hittingBtwn_mono_right u s n hnn'

中文:
引理 hittingBtwn_apply_mono_right
  条件: (u : ι -> Ω -> β) (s : Set β) (n : ι) (ω : Ω)
  证明: fun _ _ hnn' => hittingBtwn_mono_right u s n hnn'

Depends on / 依赖: hittingBtwn_mono_right
-/
lemma hittingBtwn_apply_mono_right (u : ι -> Ω -> β) (s : Set β) (n : ι) (ω : Ω) :
    Monotone (hittingBtwn u s n · ω) := fun _ _ hnn' => hittingBtwn_mono_right u s n hnn'

/--
lemma `hittingBtwn_apply_mono_left` / 引理 `hittingBtwn_apply_mono_left`

English:
lemma hittingBtwn_apply_mono_left
  given: (u : ι -> Ω -> β) (s : Set β) (m : ι) (ω : Ω)
  proof: fun _ _ hnn' => hittingBtwn_mono_left u s m hnn' ω

中文:
引理 hittingBtwn_apply_mono_left
  条件: (u : ι -> Ω -> β) (s : Set β) (m : ι) (ω : Ω)
  证明: fun _ _ hnn' => hittingBtwn_mono_left u s m hnn' ω

Depends on / 依赖: hittingBtwn_mono_left
-/
lemma hittingBtwn_apply_mono_left (u : ι -> Ω -> β) (s : Set β) (m : ι) (ω : Ω) :
    Monotone (hittingBtwn u s · m ω) := fun _ _ hnn' => hittingBtwn_mono_left u s m hnn' ω

/--
lemma `hittingAfter_apply_mono` / 引理 `hittingAfter_apply_mono`

English:
lemma hittingAfter_apply_mono
  given: (u : ι -> Ω -> β) (s : Set β) (ω : Ω)
  proof: fun _ _ hnm => hittingAfter_mono u s hnm ω

中文:
引理 hittingAfter_apply_mono
  条件: (u : ι -> Ω -> β) (s : Set β) (ω : Ω)
  证明: fun _ _ hnm => hittingAfter_mono u s hnm ω

Depends on / 依赖: hittingAfter_mono
-/
lemma hittingAfter_apply_mono (u : ι -> Ω -> β) (s : Set β) (ω : Ω) :
    Monotone (hittingAfter u s · ω) := fun _ _ hnm => hittingAfter_mono u s hnm ω

end Inequalities

/--
theorem `Adapted.isStoppingTime_hittingBtwn` / 定理 `Adapted.isStoppingTime_hittingBtwn`

English:
theorem Adapted.isStoppingTime_hittingBtwn
  statement: [ConditionallyCompleteLinearOrder ι] [WellFoundedLT ι]
  proof: by
  intro i
  rcases le_or_gt n' i with hi | hi
  · have h_le : forall ω, hittingBtwn u s n n' ω <= i := fun x => (hittingBtwn_le x).trans hi
    simp [h_le]
  · have h_set_eq_Union : {ω | hittingBtwn u s n n' ω <= i} = ⋃ j in Set.Icc n i, u j ⁻¹' s := by
      ext; simp [hittingBtwn_le_iff_of_lt _

中文:
定理 Adapted.isStoppingTime_hittingBtwn
  结论: [ConditionallyCompleteLinearOrder ι] [WellFoundedLT ι]
  证明: by
  intro i
  rcases le_or_gt n' i with hi | hi
  · have h_le : forall ω, hittingBtwn u s n n' ω <= i := fun x => (hittingBtwn_le x).trans hi
    simp [h_le]
  · have h_set_eq_Union : {ω | hittingBtwn u s n n' ω <= i} = ⋃ j in Set.Icc n i, u j ⁻¹' s := by
      ext; simp [hittingBtwn_le_iff_of_lt _

Depends on / 依赖: MeasurableSet, MeasurableSet.iUnion, Set.Icc, f.mono, h_le, h_set_eq_Union, hittingBtwn, hittingBtwn_le, hittingBtwn_le_iff_of_lt, iUnion, le_or_gt
-/
theorem Adapted.isStoppingTime_hittingBtwn [ConditionallyCompleteLinearOrder ι] [WellFoundedLT ι]
    [Countable ι] {_ : MeasurableSpace β} {f : Filtration ι m} {u : ι -> Ω -> β} {s : Set β}
    {n n' : ι} (hu : Adapted f u) (hs : MeasurableSet s) :
    IsStoppingTime f (fun ω => (hittingBtwn u s n n' ω : ι)) := by
  intro i
  rcases le_or_gt n' i with hi | hi
  · have h_le : forall ω, hittingBtwn u s n n' ω <= i := fun x => (hittingBtwn_le x).trans hi
    simp [h_le]
  · have h_set_eq_Union : {ω | hittingBtwn u s n n' ω <= i} = ⋃ j in Set.Icc n i, u j ⁻¹' s := by
      ext; simp [hittingBtwn_le_iff_of_lt _ hi]
    simpa [h_set_eq_Union] using MeasurableSet.iUnion fun j =>
      MeasurableSet.iUnion fun hj => f.mono hj.2 _ ((hu j) hs)

@[deprecated (since := "2026-01-25")]
alias hittingBtwn_isStoppingTime := Adapted.isStoppingTime_hittingBtwn

/--
theorem `Adapted.isStoppingTime_hittingAfter` / 定理 `Adapted.isStoppingTime_hittingAfter`

English:
theorem Adapted.isStoppingTime_hittingAfter
  statement: [ConditionallyCompleteLinearOrder ι]
  proof: by
  intro i
  have h_set_eq_Union : {ω | hittingAfter u s n ω <= i} = ⋃ j in Set.Icc n i, u j ⁻¹' s := by
    ext; simp [hittingAfter_le_iff]
  simpa [h_set_eq_Union] using MeasurableSet.iUnion fun j =>
    MeasurableSet.iUnion fun hj => f.mono hj.2 _ ((hu j) hs)

@[deprecated (since := "2026-01-25

中文:
定理 Adapted.isStoppingTime_hittingAfter
  结论: [ConditionallyCompleteLinearOrder ι]
  证明: by
  intro i
  have h_set_eq_Union : {ω | hittingAfter u s n ω <= i} = ⋃ j in Set.Icc n i, u j ⁻¹' s := by
    ext; simp [hittingAfter_le_iff]
  simpa [h_set_eq_Union] using MeasurableSet.iUnion fun j =>
    MeasurableSet.iUnion fun hj => f.mono hj.2 _ ((hu j) hs)

@[deprecated (since := "2026-01-25

Depends on / 依赖: MeasurableSet, MeasurableSet.iUnion, Set.Icc, f.mono, h_set_eq_Union, hittingAfter, hittingAfter_le_iff, iUnion
-/
theorem Adapted.isStoppingTime_hittingAfter [ConditionallyCompleteLinearOrder ι]
    [WellFoundedLT ι] [Countable ι] {_ : MeasurableSpace β} {f : Filtration ι m} {u : ι -> Ω -> β}
    {s : Set β} {n : ι} (hu : Adapted f u) (hs : MeasurableSet s) :
    IsStoppingTime f (hittingAfter u s n) := by
  intro i
  have h_set_eq_Union : {ω | hittingAfter u s n ω <= i} = ⋃ j in Set.Icc n i, u j ⁻¹' s := by
    ext; simp [hittingAfter_le_iff]
  simpa [h_set_eq_Union] using MeasurableSet.iUnion fun j =>
    MeasurableSet.iUnion fun hj => f.mono hj.2 _ ((hu j) hs)

@[deprecated (since := "2026-01-25")]
alias hittingAfter_isStoppingTime := Adapted.isStoppingTime_hittingAfter

/--
theorem `stoppedValue_hittingBtwn_mem` / 定理 `stoppedValue_hittingBtwn_mem`

English:
theorem stoppedValue_hittingBtwn_mem
  statement: [ConditionallyCompleteLinearOrder ι] [WellFoundedLT ι]
  proof: by
  simp only [stoppedValue, hittingBtwn, if_pos h]
  obtain ⟨j, hj₁, hj₂⟩ := h
  have : sInf (Set.Icc n m inter {i | u i ω in s}) in Set.Icc n m inter {i | u i ω in s} :=
    csInf_mem (Set.nonempty_of_mem ⟨hj₁, hj₂⟩)
  exact this.2

中文:
定理 stoppedValue_hittingBtwn_mem
  结论: [ConditionallyCompleteLinearOrder ι] [WellFoundedLT ι]
  证明: by
  simp only [stoppedValue, hittingBtwn, if_pos h]
  obtain ⟨j, hj₁, hj₂⟩ := h
  have : sInf (Set.Icc n m inter {i | u i ω in s}) in Set.Icc n m inter {i | u i ω in s} :=
    csInf_mem (Set.nonempty_of_mem ⟨hj₁, hj₂⟩)
  exact this.2

Depends on / 依赖: Set.Icc, Set.nonempty_of_mem, csInf_mem, hittingBtwn, if_pos, nonempty_of_mem, stoppedValue
-/
theorem stoppedValue_hittingBtwn_mem [ConditionallyCompleteLinearOrder ι] [WellFoundedLT ι]
    {u : ι -> Ω -> β} {s : Set β} {n m : ι} {ω : Ω} (h : exists j in Set.Icc n m, u j ω in s) :
    stoppedValue u (fun ω => (hittingBtwn u s n m ω : ι)) ω in s := by
  simp only [stoppedValue, hittingBtwn, if_pos h]
  obtain ⟨j, hj₁, hj₂⟩ := h
  have : sInf (Set.Icc n m inter {i | u i ω in s}) in Set.Icc n m inter {i | u i ω in s} :=
    csInf_mem (Set.nonempty_of_mem ⟨hj₁, hj₂⟩)
  exact this.2

/--
theorem `Adapted.isStoppingTime_hittingBtwn_isStoppingTime` / 定理 `Adapted.isStoppingTime_hittingBtwn_isStoppingTime`

English:
theorem Adapted.isStoppingTime_hittingBtwn_isStoppingTime
  statement: [ConditionallyCompleteLinearOrder ι]
  proof: by
  intro n
  have h₁ : {x | hittingBtwn u s (τ x).untopA N x <= n} =
    (⋃ i <= n, {x | τ x = i} inter {x | hittingBtwn u s i N x <= n}) union
      ⋃ i > n, {x | τ x = i} inter {x | hittingBtwn u s i N x <= n} := by
    ext x
    simp only [Set.mem_ofPred_eq, gt_iff_lt, Set.mem_union, Set.mem_iU

中文:
定理 Adapted.isStoppingTime_hittingBtwn_isStoppingTime
  结论: [ConditionallyCompleteLinearOrder ι]
  证明: by
  intro n
  have h₁ : {x | hittingBtwn u s (τ x).untopA N x <= n} =
    (⋃ i <= n, {x | τ x = i} inter {x | hittingBtwn u s i N x <= n}) union
      ⋃ i > n, {x | τ x = i} inter {x | hittingBtwn u s i N x <= n} := by
    ext x
    simp only [Set.mem_ofPred_eq, gt_iff_lt, Set.mem_union, Set.mem_iU

Depends on / 依赖: Set.mem_iUnion, Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_union, exists_and_left, exists_prop, ext_fourfold, gt_iff_lt, h_top, hittingBtwn, le_or_gt, mem_iUnion, mem_inter_iff, mem_ofPred_eq, mem_union, or_and_right, specialize, untopA
-/
theorem Adapted.isStoppingTime_hittingBtwn_isStoppingTime [ConditionallyCompleteLinearOrder ι]
    [WellFoundedLT ι] [Countable ι] [TopologicalSpace ι] [OrderTopology ι]
    [FirstCountableTopology ι] [MeasurableSpace β] {f : Filtration ι m} {u : ι -> Ω -> β}
    {τ : Ω -> WithTop ι} (hτ : IsStoppingTime f τ)
    {N : ι} (hτbdd : forall x, τ x <= N) {s : Set β} (hs : MeasurableSet s) (hf : Adapted f u) :
    IsStoppingTime f fun x => (hittingBtwn u s (τ x).untopA N x : ι) := by
  intro n
  have h₁ : {x | hittingBtwn u s (τ x).untopA N x <= n} =
    (⋃ i <= n, {x | τ x = i} inter {x | hittingBtwn u s i N x <= n}) union
      ⋃ i > n, {x | τ x = i} inter {x | hittingBtwn u s i N x <= n} := by
    ext x
    simp only [Set.mem_ofPred_eq, gt_iff_lt, Set.mem_union, Set.mem_iUnion, Set.mem_inter_iff,
      exists_and_left, exists_prop]
    specialize hτbdd x
    have h_top : τ x != ⊤ := fun h => by simp [h] at hτbdd
    lift τ x to ι using h_top with t
    simp [← or_and_right, le_or_gt]
  have h₂ : ⋃ i > n, {x | τ x = i} inter {x | hittingBtwn u s i N x <= n} = ∅ := by
    ext x
    simp only [gt_iff_lt, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_ofPred_eq, exists_prop,
      Set.mem_empty_iff_false, iff_false, not_exists, not_and, not_le]
refine fun m hm hτ => hm.trans_le le_hittingBtwn ?_ x
    specialize hτbdd x
    have h_top : τ x != ⊤ := fun h => by simp [h] at hτbdd
    lift τ x to ι using h_top with t
    rw [hτ] at hτbdd
    exact mod_cast hτbdd
  simp only [WithTop.coe_le_coe, h₁, h₂, Set.union_empty]
  refine MeasurableSet.iUnion fun i => MeasurableSet.iUnion fun hi =>
    (f.mono hi _ (hτ.measurableSet_eq i)).inter ?_
  simpa using hf.isStoppingTime_hittingBtwn hs n

@[deprecated (since := "2026-01-25")]
alias isStoppingTime_hittingBtwn_isStoppingTime := Adapted.isStoppingTime_hittingBtwn_isStoppingTime

section CompleteLattice

variable [CompleteLattice ι] {u : ι -> Ω -> β} {s : Set β}

/--
theorem `hittingBtwn_eq_sInf` / 定理 `hittingBtwn_eq_sInf`

English:
theorem hittingBtwn_eq_sInf
  given: (ω : Ω)
  statement: hittingBtwn u s ⊥ ⊤ ω = sInf {i : ι | u i ω in s}
  proof: by
  simp only [hittingBtwn, Set.Icc_bot,
    Set.Iic_top, Set.univ_inter, ite_eq_left_iff, not_exists]
  intro h_notMem_s
  symm
  rw [sInf_eq_top]
  simp only [Set.mem_univ, true_and] at h_notMem_s
  exact fun i hi_mem_s => absurd hi_mem_s (h_notMem_s i)

中文:
定理 hittingBtwn_eq_sInf
  条件: (ω : Ω)
  结论: hittingBtwn u s ⊥ ⊤ ω = sInf {i : ι | u i ω in s}
  证明: by
  simp only [hittingBtwn, Set.Icc_bot,
    Set.Iic_top, Set.univ_inter, ite_eq_left_iff, not_exists]
  intro h_notMem_s
  symm
  rw [sInf_eq_top]
  simp only [Set.mem_univ, true_and] at h_notMem_s
  exact fun i hi_mem_s => absurd hi_mem_s (h_notMem_s i)

Depends on / 依赖: Icc_bot, Iic_top, Set.Icc_bot, Set.Iic_top, Set.mem_univ, Set.univ_inter, absurd, h_notMem_s, hi_mem_s, hittingBtwn, ite_eq_left_iff, mem_univ, not_exists, sInf_eq_top, true_and, univ_inter
-/
theorem hittingBtwn_eq_sInf (ω : Ω) : hittingBtwn u s ⊥ ⊤ ω = sInf {i : ι | u i ω in s} := by
  simp only [hittingBtwn, Set.Icc_bot,
    Set.Iic_top, Set.univ_inter, ite_eq_left_iff, not_exists]
  intro h_notMem_s
  symm
  rw [sInf_eq_top]
  simp only [Set.mem_univ, true_and] at h_notMem_s
  exact fun i hi_mem_s => absurd hi_mem_s (h_notMem_s i)

/--
lemma `hittingAfter_eq_sInf` / 引理 `hittingAfter_eq_sInf`

English:
lemma hittingAfter_eq_sInf
  given: [forall ω, Decidable (exists j, u j ω in s)] (ω : Ω)
  proof: by
  simp [hittingAfter]

中文:
引理 hittingAfter_eq_sInf
  条件: [对任意 ω, Decidable (存在 j, u j ω in s)] (ω : Ω)
  证明: by
  simp [hittingAfter]

Depends on / 依赖: hittingAfter
-/
lemma hittingAfter_eq_sInf [forall ω, Decidable (exists j, u j ω in s)] (ω : Ω) :
    hittingAfter u s ⊥ ω
      = if exists j, u j ω in s then ((sInf {i : ι | u i ω in s} : ι) : WithTop ι)
        else (⊤ : WithTop ι) := by
  simp [hittingAfter]

end CompleteLattice

section ConditionallyCompleteLinearOrderBot

variable [ConditionallyCompleteLinearOrderBot ι] [WellFoundedLT ι]
variable {u : ι -> Ω -> β} {s : Set β}

/--
theorem `hittingBtwn_bot_le_iff` / 定理 `hittingBtwn_bot_le_iff`

English:
theorem hittingBtwn_bot_le_iff
  given: {i n : ι} {ω : Ω} (hx : exists j, j <= n ∧ u j ω in s)
  proof: by
  rcases lt_or_ge i n with hi | hi
  · rw [hittingBtwn_le_iff_of_lt _ hi]
    simp
  · simp only [(hittingBtwn_le ω).trans hi, true_iff]
    obtain ⟨j, hj₁, hj₂⟩ := hx
    exact ⟨j, hj₁.trans hi, hj₂⟩

中文:
定理 hittingBtwn_bot_le_iff
  条件: {i n : ι} {ω : Ω} (hx : 存在 j, j <= n ∧ u j ω in s)
  证明: by
  rcases lt_or_ge i n with hi | hi
  · rw [hittingBtwn_le_iff_of_lt _ hi]
    simp
  · simp only [(hittingBtwn_le ω).trans hi, true_iff]
    obtain ⟨j, hj₁, hj₂⟩ := hx
    exact ⟨j, hj₁.trans hi, hj₂⟩

Depends on / 依赖: hittingBtwn_le, hittingBtwn_le_iff_of_lt, lt_or_ge, true_iff
-/
theorem hittingBtwn_bot_le_iff {i n : ι} {ω : Ω} (hx : exists j, j <= n ∧ u j ω in s) :
    hittingBtwn u s ⊥ n ω <= i ↔ exists j <= i, u j ω in s := by
  rcases lt_or_ge i n with hi | hi
  · rw [hittingBtwn_le_iff_of_lt _ hi]
    simp
  · simp only [(hittingBtwn_le ω).trans hi, true_iff]
    obtain ⟨j, hj₁, hj₂⟩ := hx
    exact ⟨j, hj₁.trans hi, hj₂⟩

/--
theorem `hittingAfter_bot_le_iff` / 定理 `hittingAfter_bot_le_iff`

English:
theorem hittingAfter_bot_le_iff
  given: {i : ι} {ω : Ω}
  proof: by
  simp [hittingAfter_le_iff]

中文:
定理 hittingAfter_bot_le_iff
  条件: {i : ι} {ω : Ω}
  证明: by
  simp [hittingAfter_le_iff]

Depends on / 依赖: hittingAfter_le_iff
-/
theorem hittingAfter_bot_le_iff {i : ι} {ω : Ω} :
    hittingAfter u s ⊥ ω <= i ↔ exists j <= i, u j ω in s := by
  simp [hittingAfter_le_iff]

end ConditionallyCompleteLinearOrderBot

end MeasureTheory
