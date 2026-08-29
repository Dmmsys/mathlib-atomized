/-
Copyright (c) 2023 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Peter Pfaffelhuber
-/
module

public import Mathlib.MeasureTheory.PiSystem
public import Mathlib.Order.Partition.Finpartition
public import Mathlib.Order.SupClosed

/-! # Semirings and rings of sets

A semi-ring of sets `C` (in the sense of measure theory) is a family of sets containing `∅`,
stable by intersection and such that for all `s, t ∈ C`, `t \ s` is equal to a disjoint union of
finitely many sets in `C`. Note that a semi-ring of sets may not contain unions.

An important example of a semi-ring of sets is intervals in `ℝ`. The intersection of two intervals
is an interval (possibly empty). The union of two intervals may not be an interval.
The set difference of two intervals may not be an interval, but it will be a disjoint union of
two intervals.

A ring of sets is a set of sets containing `∅`, stable by union, set difference and intersection.

## Main definitions

* `MeasureTheory.IsSetSemiring C`: property of being a semi-ring of sets.
* `MeasureTheory.IsSetSemiring.disjointOfDiff hs ht`: for `s, t` in a semi-ring `C`
  (with `hC : IsSetSemiring C`) with `hs : s ∈ C`, `ht : t ∈ C`, this is a `Finset` of
  pairwise disjoint sets such that `s \ t = ⋃₀ hC.disjointOfDiff hs ht`.
* `MeasureTheory.IsSetSemiring.disjointOfDiffUnion hs hI`: for `hs : s ∈ C` and a finset
  `I` of sets in `C` (with `hI : ↑I ⊆ C`), this is a `Finset` of pairwise disjoint sets such that
  `s \ ⋃₀ I = ⋃₀ hC.disjointOfDiffUnion hs hI`.
* `MeasureTheory.IsSetSemiring.disjointOfUnion hJ`: for `hJ ⊆ C`, this is a
  `Finset` of pairwise disjoint sets such that `⋃₀ J = ⋃₀ hC.disjointOfUnion hJ`.

* `MeasureTheory.IsSetRing`: property of being a ring of sets.

## Main statements

* `MeasureTheory.IsSetSemiring.exists_disjoint_finset_sdiff_eq`: the existence of the `Finset` given
  by the definition `IsSetSemiring.disjointOfDiffUnion` (see above).
* `MeasureTheory.IsSetSemiring.disjointOfUnion_props`: In a `hC : IsSetSemiring C`,
  for a `J : Finset (Set α)` with `J ⊆ C`, there is
  for every `x in J` some `K x ⊆ C` finite, such that
  * `⋃ x ∈ J, K x` are pairwise disjoint and do not contain ∅,
  * `⋃ s ∈ K x, s ⊆ x`,
  * `⋃ x ∈ J, x = ⋃ x ∈ J, ⋃ s ∈ K x, s`.

-/

public section

open Finset Set

namespace MeasureTheory

variable {α : Type*} {C : Set (Set α)} {s t : Set α}

/--
Definition of `IsSetSemiring` / `IsSetSemiring` 的定义

English:
structure IsSetSemiring
  parameters: (C : Set (Set α))
  axioms and operations (3):
    - empty_mem : ∅ in C
    - inter_mem : forall s in C, forall t in C, s inter t in C
    - sdiff_eq_sUnion' : forall s in C, forall t in C, exists I : Finset (Set α), ↑I subseteq C ∧ PairwiseDisjoint (I : Set (Set α)) id ∧ s \ t = ⋃₀ I

中文:
结构 是SetSemiring
  参数: (C : 集合 (集合 α))
  公理与运算 (3 个):
    - empty_mem : ∅ in C
    - inter_mem : 对任意 s in C, 对任意 t in C, s inter t in C
    - sdiff_eq_sUnion' : 对任意 s in C, 对任意 t in C, 存在 I : 有限集 (集合 α), ↑I subseteq C ∧ PairwiseDisjoint (I : 集合 (集合 α)) id ∧ s \ t = ⋃₀ I
-/
structure IsSetSemiring (C : Set (Set α)) : Prop where
  empty_mem : ∅ in C
  inter_mem : forall s in C, forall t in C, s inter t in C
  sdiff_eq_sUnion' : forall s in C, forall t in C,
    exists I : Finset (Set α), ↑I subseteq C ∧ PairwiseDisjoint (I : Set (Set α)) id ∧ s \ t = ⋃₀ I

/--
Definition of `IsSetRing` / `IsSetRing` 的定义

English:
structure IsSetRing
  parameters: (C : Set (Set α))
  axioms and operations (3):
    - empty_mem : ∅ in C
    - union_mem(⦃s t) : Set α⦄ : s in C -> t in C -> s union t in C
    - sdiff_mem(⦃s t) : Set α⦄ : s in C -> t in C -> s \ t in C

中文:
结构 是集合环
  参数: (C : 集合 (集合 α))
  公理与运算 (3 个):
    - empty_mem : ∅ in C
    - union_mem(⦃s t) : 集合 α⦄ : s in C -> t in C -> s union t in C
    - sdiff_mem(⦃s t) : 集合 α⦄ : s in C -> t in C -> s \ t in C
-/
structure IsSetRing (C : Set (Set α)) : Prop where
  empty_mem : ∅ in C
  union_mem ⦃s t : Set α⦄ : s in C -> t in C -> s union t in C
  sdiff_mem ⦃s t : Set α⦄ : s in C -> t in C -> s \ t in C

namespace IsSetRing

/--
lemma `inter_mem` / 引理 `inter_mem`

English:
lemma inter_mem
  given: (hC : IsSetRing C) (hs : s in C) (ht : t in C)
  statement: s inter t in C
  proof: by
  rw [← sdiff_sdiff_right_self]; exact hC.sdiff_mem hs (hC.sdiff_mem hs ht)

中文:
引理 inter_mem
  条件: (hC : 是集合环 C) (hs : s in C) (ht : t in C)
  结论: s inter t in C
  证明: by
  rw [← sdiff_sdiff_right_self]; exact hC.sdiff_mem hs (hC.sdiff_mem hs ht)

Depends on / 依赖: hC.sdiff_mem, sdiff_mem, sdiff_sdiff_right_self
-/
lemma inter_mem (hC : IsSetRing C) (hs : s in C) (ht : t in C) : s inter t in C := by
  rw [← sdiff_sdiff_right_self]; exact hC.sdiff_mem hs (hC.sdiff_mem hs ht)

/--
lemma `isSetSemiring` / 引理 `isSetSemiring`

English:
lemma isSetSemiring
  given: (hC : IsSetRing C)
  statement: IsSetSemiring C where
  proof: hC.empty_mem
  inter_mem := fun _ hs _ ht => hC.inter_mem hs ht
  sdiff_eq_sUnion' := by
    refine fun s hs t ht => ⟨{s \ t}, ?_, ?_, ?_⟩
    · simp only [coe_singleton, Set.singleton_subset_iff]
      exact hC.sdiff_mem hs ht
    · simp only [coe_singleton, pairwiseDisjoint_singleton]
    · simp o

中文:
引理 isSetSemiring
  条件: (hC : 是集合环 C)
  结论: 是SetSemiring C where
  证明: hC.empty_mem
  inter_mem := fun _ hs _ ht => hC.inter_mem hs ht
  sdiff_eq_sUnion' := by
    refine fun s hs t ht => ⟨{s \ t}, ?_, ?_, ?_⟩
    · simp only [coe_singleton, Set.singleton_subset_iff]
      exact hC.sdiff_mem hs ht
    · simp only [coe_singleton, pairwiseDisjoint_singleton]
    · simp o

Depends on / 依赖: empty_mem, hC.empty_mem
-/
lemma isSetSemiring (hC : IsSetRing C) : IsSetSemiring C where
  empty_mem := hC.empty_mem
  inter_mem := fun _ hs _ ht => hC.inter_mem hs ht
  sdiff_eq_sUnion' := by
    refine fun s hs t ht => ⟨{s \ t}, ?_, ?_, ?_⟩
    · simp only [coe_singleton, Set.singleton_subset_iff]
      exact hC.sdiff_mem hs ht
    · simp only [coe_singleton, pairwiseDisjoint_singleton]
    · simp only [coe_singleton, sUnion_singleton]

/--
lemma `biUnion_mem` / 引理 `biUnion_mem`

English:
lemma biUnion_mem
  statement: {ι : Type*} (hC : IsSetRing C) {s : ι -> Set α}
  proof: by
  classical
  induction S using Finset.induction with
  | empty => simp [hC.empty_mem]
  | insert i S _ h =>
    simp_rw [← Finset.mem_coe, Finset.coe_insert, Set.biUnion_insert]
    refine hC.union_mem (hs i (mem_insert_self i S)) ?_
    exact h (fun n hnS => hs n (mem_insert_of_mem hnS))

中文:
引理 biUnion_mem
  结论: {ι : 类型} (hC : 是集合环 C) {s : ι -> 集合 α}
  证明: by
  classical
  induction S using Finset.induction with
  | empty => simp [hC.empty_mem]
  | insert i S _ h =>
    simp_rw [← Finset.mem_coe, Finset.coe_insert, Set.biUnion_insert]
    refine hC.union_mem (hs i (mem_insert_self i S)) ?_
    exact h (fun n hnS => hs n (mem_insert_of_mem hnS))

Depends on / 依赖: Finset, Finset.coe_insert, Finset.induction, Finset.mem_coe, Set.biUnion_insert, biUnion_insert, classical, coe_insert, empty_mem, hC.empty_mem, hC.union_mem, insert, mem_coe, mem_insert_of_mem, mem_insert_self, simp_rw, union_mem
-/
lemma biUnion_mem {ι : Type*} (hC : IsSetRing C) {s : ι -> Set α}
    (S : Finset ι) (hs : forall n in S, s n in C) :
    ⋃ i in S, s i in C := by
  classical
  induction S using Finset.induction with
  | empty => simp [hC.empty_mem]
  | insert i S _ h =>
    simp_rw [← Finset.mem_coe, Finset.coe_insert, Set.biUnion_insert]
    refine hC.union_mem (hs i (mem_insert_self i S)) ?_
    exact h (fun n hnS => hs n (mem_insert_of_mem hnS))

/--
lemma `biInter_mem` / 引理 `biInter_mem`

English:
lemma biInter_mem
  statement: {ι : Type*} (hC : IsSetRing C) {s : ι -> Set α}
  proof: by
  classical
  induction hS using Finset.Nonempty.cons_induction with
  | singleton => simpa using hs
  | cons i S hiS _ h =>
    simp_rw [← Finset.mem_coe, Finset.coe_cons, Set.biInter_insert]
    simp only [cons_eq_insert, Finset.mem_insert, forall_eq_or_imp] at hs
    refine hC.inter_mem hs.1 ?

中文:
引理 bi整数er_mem
  结论: {ι : 类型} (hC : 是集合环 C) {s : ι -> 集合 α}
  证明: by
  classical
  induction hS using Finset.Nonempty.cons_induction with
  | singleton => simpa using hs
  | cons i S hiS _ h =>
    simp_rw [← Finset.mem_coe, Finset.coe_cons, Set.biInter_insert]
    simp only [cons_eq_insert, Finset.mem_insert, forall_eq_or_imp] at hs
    refine hC.inter_mem hs.1 ?

Depends on / 依赖: Finset, Finset.Nonempty.cons_induction, Finset.coe_cons, Finset.mem_coe, Finset.mem_insert, Nonempty, Set.biInter_insert, biInter_insert, classical, coe_cons, cons_eq_insert, cons_induction, forall_eq_or_imp, hC.inter_mem, inter_mem, mem_coe, mem_insert, simp_rw, singleton
-/
lemma biInter_mem {ι : Type*} (hC : IsSetRing C) {s : ι -> Set α}
    (S : Finset ι) (hS : S.Nonempty) (hs : forall n in S, s n in C) :
    ⋂ i in S, s i in C := by
  classical
  induction hS using Finset.Nonempty.cons_induction with
  | singleton => simpa using hs
  | cons i S hiS _ h =>
    simp_rw [← Finset.mem_coe, Finset.coe_cons, Set.biInter_insert]
    simp only [cons_eq_insert, Finset.mem_insert, forall_eq_or_imp] at hs
    refine hC.inter_mem hs.1 ?_
    exact h (fun n hnS => hs.2 n hnS)

/--
lemma `finsetSup_mem` / 引理 `finsetSup_mem`

English:
lemma finsetSup_mem
  statement: (hC : IsSetRing C) {ι : Type*} {s : ι -> Set α} {t : Finset ι}
  proof: by
  simpa using biUnion_mem hC _ hs

中文:
引理 finsetSup_mem
  结论: (hC : 是集合环 C) {ι : 类型} {s : ι -> 集合 α} {t : 有限集 ι}
  证明: by
  simpa using biUnion_mem hC _ hs

Depends on / 依赖: biUnion_mem
-/
lemma finsetSup_mem (hC : IsSetRing C) {ι : Type*} {s : ι -> Set α} {t : Finset ι}
    (hs : forall i in t, s i in C) :
    t.sup s in C := by
  simpa using biUnion_mem hC _ hs

/--
lemma `partialSups_mem` / 引理 `partialSups_mem`

English:
lemma partialSups_mem
  statement: {ι : Type*} [Preorder ι] [LocallyFiniteOrderBot ι]
  proof: by
  simpa only [partialSups_apply, sup'_eq_sup] using hC.finsetSup_mem (fun i hi => hs i)

中文:
引理 partialSups_mem
  结论: {ι : 类型} [预序 ι] [LocallyFiniteOrderBot ι]
  证明: by
  simpa only [partialSups_apply, sup'_eq_sup] using hC.finsetSup_mem (fun i hi => hs i)

Depends on / 依赖: _eq_sup, finsetSup_mem, hC.finsetSup_mem, partialSups_apply
-/
lemma partialSups_mem {ι : Type*} [Preorder ι] [LocallyFiniteOrderBot ι]
    (hC : IsSetRing C) {s : ι -> Set α} (hs : forall n, s n in C) (n : ι) :
    partialSups s n in C := by
  simpa only [partialSups_apply, sup'_eq_sup] using hC.finsetSup_mem (fun i hi => hs i)

/--
lemma `disjointed_mem` / 引理 `disjointed_mem`

English:
lemma disjointed_mem
  statement: {ι : Type*} [Preorder ι] [LocallyFiniteOrderBot ι]
  proof: disjointedRec (fun _ j ht => hC.sdiff_mem ht <| hs j) (hs i)

中文:
引理 disjointed_mem
  结论: {ι : 类型} [预序 ι] [LocallyFiniteOrderBot ι]
  证明: disjointedRec (fun _ j ht => hC.sdiff_mem ht <| hs j) (hs i)

Depends on / 依赖: disjointedRec, hC.sdiff_mem, sdiff_mem
-/
lemma disjointed_mem {ι : Type*} [Preorder ι] [LocallyFiniteOrderBot ι]
    (hC : IsSetRing C) {s : ι -> Set α} (hs : forall j, s j in C) (i : ι) :
    disjointed s i in C :=
  disjointedRec (fun _ j ht => hC.sdiff_mem ht <| hs j) (hs i)

/--
theorem `iUnion_le_mem` / 定理 `iUnion_le_mem`

English:
theorem iUnion_le_mem
  given: (hC : IsSetRing C) {s : Nat -> Set α} (hs : forall n, s n in C) (n : Nat)
  proof: by
  induction n with
  | zero => simp [hs 0]
  | succ n hn => rw [biUnion_le_succ]; exact hC.union_mem hn (hs _)

中文:
定理 iUnion_le_mem
  条件: (hC : 是集合环 C) {s : 自然数 -> 集合 α} (hs : 对任意 n, s n in C) (n : 自然数)
  证明: by
  induction n with
  | zero => simp [hs 0]
  | succ n hn => rw [biUnion_le_succ]; exact hC.union_mem hn (hs _)

Depends on / 依赖: biUnion_le_succ, hC.union_mem, union_mem
-/
theorem iUnion_le_mem (hC : IsSetRing C) {s : Nat -> Set α} (hs : forall n, s n in C) (n : Nat) :
    (⋃ i <= n, s i) in C := by
  induction n with
  | zero => simp [hs 0]
  | succ n hn => rw [biUnion_le_succ]; exact hC.union_mem hn (hs _)

/--
theorem `iInter_le_mem` / 定理 `iInter_le_mem`

English:
theorem iInter_le_mem
  given: (hC : IsSetRing C) {s : Nat -> Set α} (hs : forall n, s n in C) (n : Nat)
  proof: by
  induction n with
  | zero => simp [hs 0]
  | succ n hn => rw [biInter_le_succ]; exact hC.inter_mem hn (hs _)

中文:
定理 i整数er_le_mem
  条件: (hC : 是集合环 C) {s : 自然数 -> 集合 α} (hs : 对任意 n, s n in C) (n : 自然数)
  证明: by
  induction n with
  | zero => simp [hs 0]
  | succ n hn => rw [biInter_le_succ]; exact hC.inter_mem hn (hs _)

Depends on / 依赖: biInter_le_succ, hC.inter_mem, inter_mem
-/
theorem iInter_le_mem (hC : IsSetRing C) {s : Nat -> Set α} (hs : forall n, s n in C) (n : Nat) :
    (⋂ i <= n, s i) in C := by
  induction n with
  | zero => simp [hs 0]
  | succ n hn => rw [biInter_le_succ]; exact hC.inter_mem hn (hs _)

/--
theorem `accumulate_mem` / 定理 `accumulate_mem`

English:
theorem accumulate_mem
  given: (hC : IsSetRing C) {s : Nat -> Set α} (hs : forall i, s i in C) (n : Nat)
  proof: by
  induction n with
  | zero => simp [hs 0]
  | succ n hn => rw [accumulate_succ]; exact hC.union_mem hn (hs _)

中文:
定理 accumulate_mem
  条件: (hC : 是集合环 C) {s : 自然数 -> 集合 α} (hs : 对任意 i, s i in C) (n : 自然数)
  证明: by
  induction n with
  | zero => simp [hs 0]
  | succ n hn => rw [accumulate_succ]; exact hC.union_mem hn (hs _)

Depends on / 依赖: accumulate_succ, hC.union_mem, union_mem
-/
theorem accumulate_mem (hC : IsSetRing C) {s : Nat -> Set α} (hs : forall i, s i in C) (n : Nat) :
    accumulate s n in C := by
  induction n with
  | zero => simp [hs 0]
  | succ n hn => rw [accumulate_succ]; exact hC.union_mem hn (hs _)

end IsSetRing

namespace IsSetSemiring

/--
lemma `isPiSystem` / 引理 `isPiSystem`

English:
lemma isPiSystem
  given: (hC : IsSetSemiring C)
  statement: IsPiSystem C
  proof: fun s hs t ht _ => hC.inter_mem s hs t ht

中文:
引理 isPiSystem
  条件: (hC : 是SetSemiring C)
  结论: IsPiSystem C
  证明: fun s hs t ht _ => hC.inter_mem s hs t ht

Depends on / 依赖: hC.inter_mem, inter_mem
-/
lemma isPiSystem (hC : IsSetSemiring C) : IsPiSystem C := fun s hs t ht _ => hC.inter_mem s hs t ht

/--
theorem `exists_finpartition_sdiff` / 定理 `exists_finpartition_sdiff`

English:
theorem exists_finpartition_sdiff
  given: (hC : IsSetSemiring C) (hs : s in C) (ht : t in C)
  proof: by
  obtain ⟨I, hIC, hI, hst⟩ := hC.sdiff_eq_sUnion' s hs t ht
  refine ⟨.ofErase I (supIndep_iff_pairwiseDisjoint.mpr hI) ?_, ?_⟩
  · rw [sup_id_eq_sSup, sSup_eq_sUnion, hst]
  · grw [Finpartition.ofErase_parts, Finset.erase_subset, hIC]

@[deprecated (since := "2026-06-03")] alias exists_finpartit

中文:
定理 存在_finpartition_sdiff
  条件: (hC : 是SetSemiring C) (hs : s in C) (ht : t in C)
  证明: by
  obtain ⟨I, hIC, hI, hst⟩ := hC.sdiff_eq_sUnion' s hs t ht
  refine ⟨.ofErase I (supIndep_iff_pairwiseDisjoint.mpr hI) ?_, ?_⟩
  · rw [sup_id_eq_sSup, sSup_eq_sUnion, hst]
  · grw [Finpartition.ofErase_parts, Finset.erase_subset, hIC]

@[deprecated (since := "2026-06-03")] alias exists_finpartit

Depends on / 依赖: Finpartition, Finpartition.ofErase_parts, Finset, Finset.erase_subset, erase_subset, hC.sdiff_eq_sUnion, ofErase, ofErase_parts, sSup_eq_sUnion, sdiff_eq_sUnion, supIndep_iff_pairwiseDisjoint, supIndep_iff_pairwiseDisjoint.mpr, sup_id_eq_sSup
-/
theorem exists_finpartition_sdiff (hC : IsSetSemiring C) (hs : s in C) (ht : t in C) :
    exists P : Finpartition (s \ t), ↑P.parts subseteq C := by
  obtain ⟨I, hIC, hI, hst⟩ := hC.sdiff_eq_sUnion' s hs t ht
  refine ⟨.ofErase I (supIndep_iff_pairwiseDisjoint.mpr hI) ?_, ?_⟩
  · rw [sup_id_eq_sSup, sSup_eq_sUnion, hst]
  · grw [Finpartition.ofErase_parts, Finset.erase_subset, hIC]

@[deprecated (since := "2026-06-03")] alias exists_finpartition_diff := exists_finpartition_sdiff

/--
theorem `mem_supClosure_iff` / 定理 `mem_supClosure_iff`

English:
theorem mem_supClosure_iff
  given: (hC : IsSetSemiring C)
  proof: by
    rintro ⟨S, hS, hSC, rfl⟩
    rw [sup'_eq_sup]
    clear hS
    induction S using Finset.induction with
    | empty =>
      rw [sup_empty]
      exact ⟨.empty _, hSC⟩
    | insert s S _ ih =>
      rw [coe_insert]; rw [insert_subset_iff] at hSC
      obtain ⟨hsC, hSC⟩ := hSC
      obtain ⟨P, 

中文:
定理 mem_supClosure_iff
  条件: (hC : 是SetSemiring C)
  证明: by
    rintro ⟨S, hS, hSC, rfl⟩
    rw [sup'_eq_sup]
    clear hS
    induction S using Finset.induction with
    | empty =>
      rw [sup_empty]
      exact ⟨.empty _, hSC⟩
    | insert s S _ ih =>
      rw [coe_insert]; rw [insert_subset_iff] at hSC
      obtain ⟨hsC, hSC⟩ := hSC
      obtain ⟨P, 

Depends on / 依赖: Finpartition, Finpartition.mem_avo, Finset, Finset.induction, P.avoid, Q.parts, _eq_sup, coe_insert, eq_or_ne, insert, insert_subset_iff, mem_avo, simp_rw, subseteq, sup_bot_eq, sup_comm, sup_empty, sup_insert
-/
theorem mem_supClosure_iff (hC : IsSetSemiring C) :
    s in supClosure C ↔ exists P : Finpartition s, ↑P.parts subseteq C where
  mp := by
    rintro ⟨S, hS, hSC, rfl⟩
    rw [sup'_eq_sup]
    clear hS
    induction S using Finset.induction with
    | empty =>
      rw [sup_empty]
      exact ⟨.empty _, hSC⟩
    | insert s S _ ih =>
      rw [coe_insert]; rw [insert_subset_iff] at hSC
      obtain ⟨hsC, hSC⟩ := hSC
      obtain ⟨P, hP⟩ := ih hSC
      rw [sup_insert]; rw [sup_comm]; rw [id]
      rcases eq_or_ne s ⊥ with rfl | hs
      · rw [sup_bot_eq]; exact ⟨P, hP⟩
      choose Q hQ using show forall t in (P.avoid s).parts, exists Q : Finpartition t, ↑Q.parts subseteq C by
        simp_rw [Finpartition.mem_avoid]
        rintro _ ⟨t, ht, -, rfl⟩
        exact hC.exists_finpartition_sdiff (hP ht) hsC
.extend hs disjoint_sdiff_left (sdiff_sup_self _ _) .bind Q exists P.avoid s
      rw [Finpartition.extend_parts]; rw [coe_insert]; rw [insert_subset_iff]; rw [Finpartition.bind_parts]; rw [coe_biUnion]; rw [iUnion₂_subset_iff]; rw [Subtype.forall]
      exact ⟨hsC, fun t ht _ => hQ t ht⟩
  mpr := by
    intro ⟨P, hP⟩
    rw [← P.sup_parts]; rw [sup_id_set_eq_sUnion]
    exact supClosed_supClosure.sSup_mem
      (Finset.finite_toSet _)
      (subset_supClosure hC.empty_mem)
      (hP.trans subset_supClosure)

/--
theorem `sdiff_mem_supClosure` / 定理 `sdiff_mem_supClosure`

English:
theorem sdiff_mem_supClosure
  given: (hC : IsSetSemiring C) (hs : s in C) (ht : t in C)
  proof: hC.mem_supClosure_iff.mpr hC.exists_finpartition_sdiff hs ht

@[deprecated (since := "2026-06-03")] alias diff_mem_supClosure := sdiff_mem_supClosure

中文:
定理 sdiff_mem_supClosure
  条件: (hC : 是SetSemiring C) (hs : s in C) (ht : t in C)
  证明: hC.mem_supClosure_iff.mpr hC.exists_finpartition_sdiff hs ht

@[deprecated (since := "2026-06-03")] alias diff_mem_supClosure := sdiff_mem_supClosure

Depends on / 依赖: exists_finpartition_sdiff, hC.exists_finpartition_sdiff, hC.mem_supClosure_iff.mpr, mem_supClosure_iff
-/
theorem sdiff_mem_supClosure (hC : IsSetSemiring C) (hs : s in C) (ht : t in C) :
    s \ t in supClosure C :=
hC.mem_supClosure_iff.mpr hC.exists_finpartition_sdiff hs ht

@[deprecated (since := "2026-06-03")] alias diff_mem_supClosure := sdiff_mem_supClosure

/--
theorem `isSetRing_supClosure` / 定理 `isSetRing_supClosure`

English:
theorem isSetRing_supClosure
  given: (hC : IsSetSemiring C)
  statement: IsSetRing (supClosure C) where
  proof: subset_supClosure hC.empty_mem
  union_mem _ _ h₁ h₂ := supClosed_supClosure h₁ h₂
  sdiff_mem := by
    rintro s _ hs ⟨T, hT, hTC, rfl⟩
    rw [sup'_eq_sup]
    clear hT
    induction T using Finset.induction generalizing s with
    | empty => simpa
    | insert t T _ ih =>
      simp_rw [sup_inser

中文:
定理 isSetRing_supClosure
  条件: (hC : 是SetSemiring C)
  结论: 是集合环 (supClosure C) where
  证明: subset_supClosure hC.empty_mem
  union_mem _ _ h₁ h₂ := supClosed_supClosure h₁ h₂
  sdiff_mem := by
    rintro s _ hs ⟨T, hT, hTC, rfl⟩
    rw [sup'_eq_sup]
    clear hT
    induction T using Finset.induction generalizing s with
    | empty => simpa
    | insert t T _ ih =>
      simp_rw [sup_inser

Depends on / 依赖: empty_mem, hC.empty_mem, subset_supClosure
-/
theorem isSetRing_supClosure (hC : IsSetSemiring C) : IsSetRing (supClosure C) where
  empty_mem := subset_supClosure hC.empty_mem
  union_mem _ _ h₁ h₂ := supClosed_supClosure h₁ h₂
  sdiff_mem := by
    rintro s _ hs ⟨T, hT, hTC, rfl⟩
    rw [sup'_eq_sup]
    clear hT
    induction T using Finset.induction generalizing s with
    | empty => simpa
    | insert t T _ ih =>
      simp_rw [sup_insert, id, sup_eq_union, ← sdiff_sdiff]
      rw [coe_insert]; rw [insert_subset_iff] at hTC
      obtain ⟨htC, hTC⟩ := hTC
      refine ih ?_ hTC
      obtain ⟨S, hS, hSC, rfl⟩ := hs
      rw [sup'_eq_sup]; rw [← Finset.sup_sdiff_right]
      refine supClosed_supClosure.finsetSup_mem hS fun s hs => ?_
      exact hC.sdiff_mem_supClosure (hSC hs) htC

section disjointOfDiff

/--
Definition of `disjointOfDiff` / `disjointOfDiff` 的定义

English:
definition disjointOfDiff
  signature: (hC : IsSetSemiring C) (hs : s in C) (ht : t in C)
  body: (hC.exists_finpartition_sdiff hs ht).choose.parts

中文:
定义 disjointOfDiff
  签名: (hC : 是SetSemiring C) (hs : s in C) (ht : t in C)
  定义体: (hC.exists_finpartition_sdiff hs ht).choose.parts

Depends on / 依赖: choose.parts, exists_finpartition_sdiff, hC.exists_finpartition_sdiff
-/
noncomputable def disjointOfDiff (hC : IsSetSemiring C) (hs : s in C) (ht : t in C) :
    Finset (Set α) :=
  (hC.exists_finpartition_sdiff hs ht).choose.parts

/--
lemma `empty_notMem_disjointOfDiff` / 引理 `empty_notMem_disjointOfDiff`

English:
lemma empty_notMem_disjointOfDiff
  given: (hC : IsSetSemiring C) (hs : s in C) (ht : t in C)
  proof: Finpartition.bot_notMem _

中文:
引理 empty_notMem_disjointOfDiff
  条件: (hC : 是SetSemiring C) (hs : s in C) (ht : t in C)
  证明: Finpartition.bot_notMem _

Depends on / 依赖: Finpartition, Finpartition.bot_notMem, bot_notMem
-/
lemma empty_notMem_disjointOfDiff (hC : IsSetSemiring C) (hs : s in C) (ht : t in C) :
    ∅ ∉ hC.disjointOfDiff hs ht :=
  Finpartition.bot_notMem _

/--
lemma `subset_disjointOfDiff` / 引理 `subset_disjointOfDiff`

English:
lemma subset_disjointOfDiff
  given: (hC : IsSetSemiring C) (hs : s in C) (ht : t in C)
  proof: (hC.exists_finpartition_sdiff hs ht).choose_spec

中文:
引理 subset_disjointOfDiff
  条件: (hC : 是SetSemiring C) (hs : s in C) (ht : t in C)
  证明: (hC.exists_finpartition_sdiff hs ht).choose_spec

Depends on / 依赖: choose_spec, exists_finpartition_sdiff, hC.exists_finpartition_sdiff
-/
lemma subset_disjointOfDiff (hC : IsSetSemiring C) (hs : s in C) (ht : t in C) :
    ↑(hC.disjointOfDiff hs ht) subseteq C :=
  (hC.exists_finpartition_sdiff hs ht).choose_spec

/--
lemma `pairwiseDisjoint_disjointOfDiff` / 引理 `pairwiseDisjoint_disjointOfDiff`

English:
lemma pairwiseDisjoint_disjointOfDiff
  given: (hC : IsSetSemiring C) (hs : s in C) (ht : t in C)
  proof: .pairwiseDisjoint Finpartition.supIndep _

中文:
引理 pairwiseDisjoint_disjointOfDiff
  条件: (hC : 是SetSemiring C) (hs : s in C) (ht : t in C)
  证明: .pairwiseDisjoint Finpartition.supIndep _

Depends on / 依赖: Finpartition, Finpartition.supIndep, pairwiseDisjoint, supIndep
-/
lemma pairwiseDisjoint_disjointOfDiff (hC : IsSetSemiring C) (hs : s in C) (ht : t in C) :
    PairwiseDisjoint (hC.disjointOfDiff hs ht : Set (Set α)) id :=
.pairwiseDisjoint Finpartition.supIndep _

/--
lemma `sUnion_disjointOfDiff` / 引理 `sUnion_disjointOfDiff`

English:
lemma sUnion_disjointOfDiff
  given: (hC : IsSetSemiring C) (hs : s in C) (ht : t in C)
  proof: (sup_id_eq_sSup _).symm.trans (Finpartition.sup_parts _)

中文:
引理 sUnion_disjointOfDiff
  条件: (hC : 是SetSemiring C) (hs : s in C) (ht : t in C)
  证明: (sup_id_eq_sSup _).symm.trans (Finpartition.sup_parts _)

Depends on / 依赖: Finpartition, Finpartition.sup_parts, sup_id_eq_sSup, sup_parts, symm.trans
-/
lemma sUnion_disjointOfDiff (hC : IsSetSemiring C) (hs : s in C) (ht : t in C) :
    ⋃₀ hC.disjointOfDiff hs ht = s \ t :=
  (sup_id_eq_sSup _).symm.trans (Finpartition.sup_parts _)

/--
lemma `notMem_disjointOfDiff` / 引理 `notMem_disjointOfDiff`

English:
lemma notMem_disjointOfDiff
  given: (hC : IsSetSemiring C) (hs : s in C) (ht : t in C)
  proof: by
  intro hs_mem
  cases disjoint_sdiff_self_right.eq_bot_of_le (Finpartition.le _ hs_mem)
  exact hC.empty_notMem_disjointOfDiff hs ht hs_mem

中文:
引理 notMem_disjointOfDiff
  条件: (hC : 是SetSemiring C) (hs : s in C) (ht : t in C)
  证明: by
  intro hs_mem
  cases disjoint_sdiff_self_right.eq_bot_of_le (Finpartition.le _ hs_mem)
  exact hC.empty_notMem_disjointOfDiff hs ht hs_mem

Depends on / 依赖: Finpartition, Finpartition.le, disjoint_sdiff_self_right, disjoint_sdiff_self_right.eq_bot_of_le, empty_notMem_disjointOfDiff, eq_bot_of_le, hC.empty_notMem_disjointOfDiff, hs_mem
-/
lemma notMem_disjointOfDiff (hC : IsSetSemiring C) (hs : s in C) (ht : t in C) :
    t ∉ hC.disjointOfDiff hs ht := by
  intro hs_mem
  cases disjoint_sdiff_self_right.eq_bot_of_le (Finpartition.le _ hs_mem)
  exact hC.empty_notMem_disjointOfDiff hs ht hs_mem

/--
lemma `sUnion_insert_disjointOfDiff` / 引理 `sUnion_insert_disjointOfDiff`

English:
lemma sUnion_insert_disjointOfDiff
  statement: (hC : IsSetSemiring C) (hs : s in C)
  proof: by
  conv_rhs => rw [← union_sdiff_cancel hst, ← hC.sUnion_disjointOfDiff hs ht]
  simp only [sUnion_insert]

中文:
引理 sUnion_insert_disjointOfDiff
  结论: (hC : 是SetSemiring C) (hs : s in C)
  证明: by
  conv_rhs => rw [← union_sdiff_cancel hst, ← hC.sUnion_disjointOfDiff hs ht]
  simp only [sUnion_insert]

Depends on / 依赖: conv_rhs, hC.sUnion_disjointOfDiff, sUnion_disjointOfDiff, sUnion_insert, union_sdiff_cancel
-/
lemma sUnion_insert_disjointOfDiff (hC : IsSetSemiring C) (hs : s in C)
    (ht : t in C) (hst : t subseteq s) :
    ⋃₀ insert t (hC.disjointOfDiff hs ht) = s := by
  conv_rhs => rw [← union_sdiff_cancel hst, ← hC.sUnion_disjointOfDiff hs ht]
  simp only [sUnion_insert]

/--
lemma `disjoint_sUnion_disjointOfDiff` / 引理 `disjoint_sUnion_disjointOfDiff`

English:
lemma disjoint_sUnion_disjointOfDiff
  given: (hC : IsSetSemiring C) (hs : s in C) (ht : t in C)
  proof: by
  rw [hC.sUnion_disjointOfDiff]
  exact disjoint_sdiff_right

中文:
引理 disjoint_sUnion_disjointOfDiff
  条件: (hC : 是SetSemiring C) (hs : s in C) (ht : t in C)
  证明: by
  rw [hC.sUnion_disjointOfDiff]
  exact disjoint_sdiff_right

Depends on / 依赖: disjoint_sdiff_right, hC.sUnion_disjointOfDiff, sUnion_disjointOfDiff
-/
lemma disjoint_sUnion_disjointOfDiff (hC : IsSetSemiring C) (hs : s in C) (ht : t in C) :
    Disjoint t (⋃₀ hC.disjointOfDiff hs ht) := by
  rw [hC.sUnion_disjointOfDiff]
  exact disjoint_sdiff_right

/--
lemma `pairwiseDisjoint_insert_disjointOfDiff` / 引理 `pairwiseDisjoint_insert_disjointOfDiff`

English:
lemma pairwiseDisjoint_insert_disjointOfDiff
  statement: (hC : IsSetSemiring C) (hs : s in C)
  proof: by
  have h := hC.pairwiseDisjoint_disjointOfDiff hs ht
  refine PairwiseDisjoint.insert_of_notMem h (hC.notMem_disjointOfDiff hs ht) fun u hu => ?_
  simp_rw [id]
  refine Disjoint.mono_right ?_ (hC.disjoint_sUnion_disjointOfDiff hs ht)
  exact subset_sUnion_of_mem hu

中文:
引理 pairwiseDisjoint_insert_disjointOfDiff
  结论: (hC : 是SetSemiring C) (hs : s in C)
  证明: by
  have h := hC.pairwiseDisjoint_disjointOfDiff hs ht
  refine PairwiseDisjoint.insert_of_notMem h (hC.notMem_disjointOfDiff hs ht) fun u hu => ?_
  simp_rw [id]
  refine Disjoint.mono_right ?_ (hC.disjoint_sUnion_disjointOfDiff hs ht)
  exact subset_sUnion_of_mem hu

Depends on / 依赖: Disjoint, Disjoint.mono_right, PairwiseDisjoint, PairwiseDisjoint.insert_of_notMem, disjoint_sUnion_disjointOfDiff, hC.disjoint_sUnion_disjointOfDiff, hC.notMem_disjointOfDiff, hC.pairwiseDisjoint_disjointOfDiff, insert_of_notMem, mono_right, notMem_disjointOfDiff, pairwiseDisjoint_disjointOfDiff, simp_rw, subset_sUnion_of_mem
-/
lemma pairwiseDisjoint_insert_disjointOfDiff (hC : IsSetSemiring C) (hs : s in C)
    (ht : t in C) :
    PairwiseDisjoint (insert t (hC.disjointOfDiff hs ht) : Set (Set α)) id := by
  have h := hC.pairwiseDisjoint_disjointOfDiff hs ht
  refine PairwiseDisjoint.insert_of_notMem h (hC.notMem_disjointOfDiff hs ht) fun u hu => ?_
  simp_rw [id]
  refine Disjoint.mono_right ?_ (hC.disjoint_sUnion_disjointOfDiff hs ht)
  exact subset_sUnion_of_mem hu

end disjointOfDiff

section disjointOfDiffUnion

variable {I : Finset (Set α)}

/--
theorem `exists_finpartition_sdiff_sUnion` / 定理 `exists_finpartition_sdiff_sUnion`

English:
theorem exists_finpartition_sdiff_sUnion
  given: (hC : IsSetSemiring C) (hs : s in C) (hI : ↑I subseteq C)
  proof: by
  rw [← hC.mem_supClosure_iff]; rw [← sSup_eq_sUnion]; rw [← sup_id_eq_sSup]
  have hC' := hC.isSetRing_supClosure
exact hC'.sdiff_mem (subset_supClosure hs) hC'.finsetSup_mem hI.trans subset_supClosure

中文:
定理 存在_finpartition_sdiff_sUnion
  条件: (hC : 是SetSemiring C) (hs : s in C) (hI : ↑I subseteq C)
  证明: by
  rw [← hC.mem_supClosure_iff]; rw [← sSup_eq_sUnion]; rw [← sup_id_eq_sSup]
  have hC' := hC.isSetRing_supClosure
exact hC'.sdiff_mem (subset_supClosure hs) hC'.finsetSup_mem hI.trans subset_supClosure
-/
private theorem exists_finpartition_sdiff_sUnion (hC : IsSetSemiring C) (hs : s in C) (hI : ↑I subseteq C) :
    exists P : Finpartition (s \ ⋃₀ I), ↑P.parts subseteq C := by
  rw [← hC.mem_supClosure_iff]; rw [← sSup_eq_sUnion]; rw [← sup_id_eq_sSup]
  have hC' := hC.isSetRing_supClosure
exact hC'.sdiff_mem (subset_supClosure hs) hC'.finsetSup_mem hI.trans subset_supClosure

/--
Definition of `disjointOfDiffUnion` / `disjointOfDiffUnion` 的定义

English:
definition disjointOfDiffUnion
  signature: (hC : IsSetSemiring C) (hs : s in C) (hI : ↑I subseteq C)
  body: (hC.exists_finpartition_sdiff_sUnion hs hI).choose.parts

中文:
定义 disjointOfDiffUnion
  签名: (hC : 是SetSemiring C) (hs : s in C) (hI : ↑I subseteq C)
  定义体: (hC.exists_finpartition_sdiff_sUnion hs hI).choose.parts

Depends on / 依赖: choose.parts, exists_finpartition_sdiff_sUnion, hC.exists_finpartition_sdiff_sUnion
-/
noncomputable def disjointOfDiffUnion (hC : IsSetSemiring C) (hs : s in C) (hI : ↑I subseteq C) :
    Finset (Set α) :=
  (hC.exists_finpartition_sdiff_sUnion hs hI).choose.parts

/--
lemma `empty_notMem_disjointOfDiffUnion` / 引理 `empty_notMem_disjointOfDiffUnion`

English:
lemma empty_notMem_disjointOfDiffUnion
  statement: (hC : IsSetSemiring C) (hs : s in C)
  proof: Finpartition.bot_notMem _

中文:
引理 empty_notMem_disjointOfDiffUnion
  结论: (hC : 是SetSemiring C) (hs : s in C)
  证明: Finpartition.bot_notMem _

Depends on / 依赖: Finpartition, Finpartition.bot_notMem, bot_notMem
-/
lemma empty_notMem_disjointOfDiffUnion (hC : IsSetSemiring C) (hs : s in C)
    (hI : ↑I subseteq C) :
    ∅ ∉ hC.disjointOfDiffUnion hs hI :=
  Finpartition.bot_notMem _

/--
lemma `disjointOfDiffUnion_subset` / 引理 `disjointOfDiffUnion_subset`

English:
lemma disjointOfDiffUnion_subset
  given: (hC : IsSetSemiring C) (hs : s in C) (hI : ↑I subseteq C)
  proof: (hC.exists_finpartition_sdiff_sUnion hs hI).choose_spec

中文:
引理 disjointOfDiffUnion_subset
  条件: (hC : 是SetSemiring C) (hs : s in C) (hI : ↑I subseteq C)
  证明: (hC.exists_finpartition_sdiff_sUnion hs hI).choose_spec

Depends on / 依赖: choose_spec, exists_finpartition_sdiff_sUnion, hC.exists_finpartition_sdiff_sUnion
-/
lemma disjointOfDiffUnion_subset (hC : IsSetSemiring C) (hs : s in C) (hI : ↑I subseteq C) :
    ↑(hC.disjointOfDiffUnion hs hI) subseteq C :=
  (hC.exists_finpartition_sdiff_sUnion hs hI).choose_spec

/--
lemma `pairwiseDisjoint_disjointOfDiffUnion` / 引理 `pairwiseDisjoint_disjointOfDiffUnion`

English:
lemma pairwiseDisjoint_disjointOfDiffUnion
  statement: (hC : IsSetSemiring C) (hs : s in C)
  proof: (Finpartition.supIndep _).pairwiseDisjoint

中文:
引理 pairwiseDisjoint_disjointOfDiffUnion
  结论: (hC : 是SetSemiring C) (hs : s in C)
  证明: (Finpartition.supIndep _).pairwiseDisjoint

Depends on / 依赖: Finpartition, Finpartition.supIndep, pairwiseDisjoint, supIndep
-/
lemma pairwiseDisjoint_disjointOfDiffUnion (hC : IsSetSemiring C) (hs : s in C)
    (hI : ↑I subseteq C) : PairwiseDisjoint (hC.disjointOfDiffUnion hs hI : Set (Set α)) id :=
  (Finpartition.supIndep _).pairwiseDisjoint

/--
lemma `sdiff_sUnion_eq_sUnion_disjointOfDiffUnion` / 引理 `sdiff_sUnion_eq_sUnion_disjointOfDiffUnion`

English:
lemma sdiff_sUnion_eq_sUnion_disjointOfDiffUnion
  statement: (hC : IsSetSemiring C) (hs : s in C)
  proof: (Finpartition.sup_parts _).symm.trans (sup_id_eq_sSup _)

@[deprecated (since := "2026-06-03")]
alias diff_sUnion_eq_sUnion_disjointOfDiffUnion := sdiff_sUnion_eq_sUnion_disjointOfDiffUnion

中文:
引理 sdiff_sUnion_eq_sUnion_disjointOfDiffUnion
  结论: (hC : 是SetSemiring C) (hs : s in C)
  证明: (Finpartition.sup_parts _).symm.trans (sup_id_eq_sSup _)

@[deprecated (since := "2026-06-03")]
alias diff_sUnion_eq_sUnion_disjointOfDiffUnion := sdiff_sUnion_eq_sUnion_disjointOfDiffUnion

Depends on / 依赖: Finpartition, Finpartition.sup_parts, sup_id_eq_sSup, sup_parts, symm.trans
-/
lemma sdiff_sUnion_eq_sUnion_disjointOfDiffUnion (hC : IsSetSemiring C) (hs : s in C)
    (hI : ↑I subseteq C) : s \ ⋃₀ I = ⋃₀ hC.disjointOfDiffUnion hs hI :=
  (Finpartition.sup_parts _).symm.trans (sup_id_eq_sSup _)

@[deprecated (since := "2026-06-03")]
alias diff_sUnion_eq_sUnion_disjointOfDiffUnion := sdiff_sUnion_eq_sUnion_disjointOfDiffUnion

/--
lemma `exists_disjoint_finset_sdiff_eq` / 引理 `exists_disjoint_finset_sdiff_eq`

English:
lemma exists_disjoint_finset_sdiff_eq
  given: (hC : IsSetSemiring C) (hs : s in C) (hI : ↑I subseteq C)
  proof: ⟨hC.disjointOfDiffUnion hs hI,
   hC.disjointOfDiffUnion_subset hs hI,
   hC.pairwiseDisjoint_disjointOfDiffUnion hs hI,
   hC.sdiff_sUnion_eq_sUnion_disjointOfDiffUnion hs hI⟩

@[deprecated (since := "2026-06-03")]
alias exists_disjoint_finset_diff_eq := exists_disjoint_finset_sdiff_eq

中文:
引理 存在_disjoint_finset_sdiff_eq
  条件: (hC : 是SetSemiring C) (hs : s in C) (hI : ↑I subseteq C)
  证明: ⟨hC.disjointOfDiffUnion hs hI,
   hC.disjointOfDiffUnion_subset hs hI,
   hC.pairwiseDisjoint_disjointOfDiffUnion hs hI,
   hC.sdiff_sUnion_eq_sUnion_disjointOfDiffUnion hs hI⟩

@[deprecated (since := "2026-06-03")]
alias exists_disjoint_finset_diff_eq := exists_disjoint_finset_sdiff_eq

Depends on / 依赖: disjointOfDiffUnion, disjointOfDiffUnion_subset, hC.disjointOfDiffUnion, hC.disjointOfDiffUnion_subset, hC.pairwiseDisjoint_disjointOfDiffUnion, hC.sdiff_sUnion_eq_sUnion_disjointOfDiffUnion, pairwiseDisjoint_disjointOfDiffUnion, sdiff_sUnion_eq_sUnion_disjointOfDiffUnion
-/
lemma exists_disjoint_finset_sdiff_eq (hC : IsSetSemiring C) (hs : s in C) (hI : ↑I subseteq C) :
    exists J : Finset (Set α), ↑J subseteq C ∧ PairwiseDisjoint (J : Set (Set α)) id ∧
      s \ ⋃₀ I = ⋃₀ J :=
  ⟨hC.disjointOfDiffUnion hs hI,
   hC.disjointOfDiffUnion_subset hs hI,
   hC.pairwiseDisjoint_disjointOfDiffUnion hs hI,
   hC.sdiff_sUnion_eq_sUnion_disjointOfDiffUnion hs hI⟩

@[deprecated (since := "2026-06-03")]
alias exists_disjoint_finset_diff_eq := exists_disjoint_finset_sdiff_eq

/--
lemma `sUnion_disjointOfDiffUnion_subset` / 引理 `sUnion_disjointOfDiffUnion_subset`

English:
lemma sUnion_disjointOfDiffUnion_subset
  statement: (hC : IsSetSemiring C) (hs : s in C)
  proof: by
  rw [← hC.sdiff_sUnion_eq_sUnion_disjointOfDiffUnion]
  exact sdiff_subset

中文:
引理 sUnion_disjointOfDiffUnion_subset
  结论: (hC : 是SetSemiring C) (hs : s in C)
  证明: by
  rw [← hC.sdiff_sUnion_eq_sUnion_disjointOfDiffUnion]
  exact sdiff_subset

Depends on / 依赖: hC.sdiff_sUnion_eq_sUnion_disjointOfDiffUnion, sdiff_sUnion_eq_sUnion_disjointOfDiffUnion, sdiff_subset
-/
lemma sUnion_disjointOfDiffUnion_subset (hC : IsSetSemiring C) (hs : s in C)
    (hI : ↑I subseteq C) : ⋃₀ (hC.disjointOfDiffUnion hs hI : Set (Set α)) subseteq s := by
  rw [← hC.sdiff_sUnion_eq_sUnion_disjointOfDiffUnion]
  exact sdiff_subset

/--
lemma `subset_of_diffUnion_disjointOfDiffUnion` / 引理 `subset_of_diffUnion_disjointOfDiffUnion`

English:
lemma subset_of_diffUnion_disjointOfDiffUnion
  statement: (hC : IsSetSemiring C) (hs : s in C) (hI : ↑I subseteq C)
  proof: by
  revert t ht
  rw [← sUnion_subset_iff]; rw [hC.sdiff_sUnion_eq_sUnion_disjointOfDiffUnion hs hI]

中文:
引理 subset_of_diffUnion_disjointOfDiffUnion
  结论: (hC : 是SetSemiring C) (hs : s in C) (hI : ↑I subseteq C)
  证明: by
  revert t ht
  rw [← sUnion_subset_iff]; rw [hC.sdiff_sUnion_eq_sUnion_disjointOfDiffUnion hs hI]

Depends on / 依赖: hC.sdiff_sUnion_eq_sUnion_disjointOfDiffUnion, revert, sUnion_subset_iff, sdiff_sUnion_eq_sUnion_disjointOfDiffUnion
-/
lemma subset_of_diffUnion_disjointOfDiffUnion (hC : IsSetSemiring C) (hs : s in C) (hI : ↑I subseteq C)
    (t : Set α) (ht : t in (hC.disjointOfDiffUnion hs hI : Set (Set α))) :
    t subseteq s \ ⋃₀ I := by
  revert t ht
  rw [← sUnion_subset_iff]; rw [hC.sdiff_sUnion_eq_sUnion_disjointOfDiffUnion hs hI]

/--
lemma `subset_of_mem_disjointOfDiffUnion` / 引理 `subset_of_mem_disjointOfDiffUnion`

English:
lemma subset_of_mem_disjointOfDiffUnion
  statement: (hC : IsSetSemiring C) {I : Finset (Set α)}
  proof: by
apply le_trans hC.subset_of_diffUnion_disjointOfDiffUnion hs hI t ht
  exact sdiff_le (a := s) (b := ⋃₀ I)

中文:
引理 subset_of_mem_disjointOfDiffUnion
  结论: (hC : 是SetSemiring C) {I : 有限集 (集合 α)}
  证明: by
apply le_trans hC.subset_of_diffUnion_disjointOfDiffUnion hs hI t ht
  exact sdiff_le (a := s) (b := ⋃₀ I)

Depends on / 依赖: hC.subset_of_diffUnion_disjointOfDiffUnion, le_trans, sdiff_le, subset_of_diffUnion_disjointOfDiffUnion
-/
lemma subset_of_mem_disjointOfDiffUnion (hC : IsSetSemiring C) {I : Finset (Set α)}
    (hs : s in C) (hI : ↑I subseteq C) (t : Set α)
    (ht : t in (hC.disjointOfDiffUnion hs hI : Set (Set α))) :
    t subseteq s := by
apply le_trans hC.subset_of_diffUnion_disjointOfDiffUnion hs hI t ht
  exact sdiff_le (a := s) (b := ⋃₀ I)

/--
lemma `disjoint_sUnion_disjointOfDiffUnion` / 引理 `disjoint_sUnion_disjointOfDiffUnion`

English:
lemma disjoint_sUnion_disjointOfDiffUnion
  statement: (hC : IsSetSemiring C) (hs : s in C)
  proof: by
  rw [← hC.sdiff_sUnion_eq_sUnion_disjointOfDiffUnion]; exact Set.disjoint_sdiff_right

中文:
引理 disjoint_sUnion_disjointOfDiffUnion
  结论: (hC : 是SetSemiring C) (hs : s in C)
  证明: by
  rw [← hC.sdiff_sUnion_eq_sUnion_disjointOfDiffUnion]; exact Set.disjoint_sdiff_right

Depends on / 依赖: Set.disjoint_sdiff_right, disjoint_sdiff_right, hC.sdiff_sUnion_eq_sUnion_disjointOfDiffUnion, sdiff_sUnion_eq_sUnion_disjointOfDiffUnion
-/
lemma disjoint_sUnion_disjointOfDiffUnion (hC : IsSetSemiring C) (hs : s in C)
    (hI : ↑I subseteq C) :
    Disjoint (⋃₀ (I : Set (Set α))) (⋃₀ hC.disjointOfDiffUnion hs hI) := by
  rw [← hC.sdiff_sUnion_eq_sUnion_disjointOfDiffUnion]; exact Set.disjoint_sdiff_right

/--
lemma `disjoint_disjointOfDiffUnion` / 引理 `disjoint_disjointOfDiffUnion`

English:
lemma disjoint_disjointOfDiffUnion
  given: (hC : IsSetSemiring C) (hs : s in C) (hI : ↑I subseteq C)
  proof: by
  by_contra h
  rw [Finset.not_disjoint_iff] at h
  obtain ⟨u, huI, hu_disjointOfDiffUnion⟩ := h
  have h_disj : u <= ⊥ :=
    hC.disjoint_sUnion_disjointOfDiffUnion hs hI (subset_sUnion_of_mem huI)
    (subset_sUnion_of_mem hu_disjointOfDiffUnion)
  simp only [Set.bot_eq_empty, subset_empty_iff]

中文:
引理 disjoint_disjointOfDiffUnion
  条件: (hC : 是SetSemiring C) (hs : s in C) (hI : ↑I subseteq C)
  证明: by
  by_contra h
  rw [Finset.not_disjoint_iff] at h
  obtain ⟨u, huI, hu_disjointOfDiffUnion⟩ := h
  have h_disj : u <= ⊥ :=
    hC.disjoint_sUnion_disjointOfDiffUnion hs hI (subset_sUnion_of_mem huI)
    (subset_sUnion_of_mem hu_disjointOfDiffUnion)
  simp only [Set.bot_eq_empty, subset_empty_iff]

Depends on / 依赖: Finset, Finset.not_disjoint_iff, Set.bot_eq_empty, bot_eq_empty, disjoint_sUnion_disjointOfDiffUnion, empty_notMem_disjointOfDiffUnion, hC.disjoint_sUnion_disjointOfDiffUnion, hC.empty_notMem_disjointOfDiffUnion, h_disj, hu_disjointOfDiffUnion, not_disjoint_iff, subset_empty_iff, subset_sUnion_of_mem
-/
lemma disjoint_disjointOfDiffUnion (hC : IsSetSemiring C) (hs : s in C) (hI : ↑I subseteq C) :
    Disjoint I (hC.disjointOfDiffUnion hs hI) := by
  by_contra h
  rw [Finset.not_disjoint_iff] at h
  obtain ⟨u, huI, hu_disjointOfDiffUnion⟩ := h
  have h_disj : u <= ⊥ :=
    hC.disjoint_sUnion_disjointOfDiffUnion hs hI (subset_sUnion_of_mem huI)
    (subset_sUnion_of_mem hu_disjointOfDiffUnion)
  simp only [Set.bot_eq_empty, subset_empty_iff] at h_disj
  refine hC.empty_notMem_disjointOfDiffUnion hs hI ?_
  rwa [h_disj] at hu_disjointOfDiffUnion

/--
lemma `pairwiseDisjoint_union_disjointOfDiffUnion` / 引理 `pairwiseDisjoint_union_disjointOfDiffUnion`

English:
lemma pairwiseDisjoint_union_disjointOfDiffUnion
  statement: (hC : IsSetSemiring C) (hs : s in C)
  proof: by
  rw [pairwiseDisjoint_union]
  refine ⟨h_dis, hC.pairwiseDisjoint_disjointOfDiffUnion hs hI, fun u hu v hv _ => ?_⟩
  simp_rw [id]
  exact disjoint_of_subset (subset_sUnion_of_mem hu) (subset_sUnion_of_mem hv)
    (hC.disjoint_sUnion_disjointOfDiffUnion hs hI)

中文:
引理 pairwiseDisjoint_union_disjointOfDiffUnion
  结论: (hC : 是SetSemiring C) (hs : s in C)
  证明: by
  rw [pairwiseDisjoint_union]
  refine ⟨h_dis, hC.pairwiseDisjoint_disjointOfDiffUnion hs hI, fun u hu v hv _ => ?_⟩
  simp_rw [id]
  exact disjoint_of_subset (subset_sUnion_of_mem hu) (subset_sUnion_of_mem hv)
    (hC.disjoint_sUnion_disjointOfDiffUnion hs hI)

Depends on / 依赖: disjoint_of_subset, disjoint_sUnion_disjointOfDiffUnion, hC.disjoint_sUnion_disjointOfDiffUnion, hC.pairwiseDisjoint_disjointOfDiffUnion, h_dis, pairwiseDisjoint_disjointOfDiffUnion, pairwiseDisjoint_union, simp_rw, subset_sUnion_of_mem
-/
lemma pairwiseDisjoint_union_disjointOfDiffUnion (hC : IsSetSemiring C) (hs : s in C)
    (hI : ↑I subseteq C) (h_dis : PairwiseDisjoint (I : Set (Set α)) id) :
    PairwiseDisjoint (I union hC.disjointOfDiffUnion hs hI : Set (Set α)) id := by
  rw [pairwiseDisjoint_union]
  refine ⟨h_dis, hC.pairwiseDisjoint_disjointOfDiffUnion hs hI, fun u hu v hv _ => ?_⟩
  simp_rw [id]
  exact disjoint_of_subset (subset_sUnion_of_mem hu) (subset_sUnion_of_mem hv)
    (hC.disjoint_sUnion_disjointOfDiffUnion hs hI)

/--
lemma `sUnion_union_sUnion_disjointOfDiffUnion_of_subset` / 引理 `sUnion_union_sUnion_disjointOfDiffUnion_of_subset`

English:
lemma sUnion_union_sUnion_disjointOfDiffUnion_of_subset
  statement: (hC : IsSetSemiring C)
  proof: by
  conv_rhs => rw [← union_sdiff_cancel (Set.sUnion_subset hI_ss : ⋃₀ ↑I subseteq s),
    hC.sdiff_sUnion_eq_sUnion_disjointOfDiffUnion hs hI]

中文:
引理 sUnion_union_sUnion_disjointOfDiffUnion_of_subset
  结论: (hC : 是SetSemiring C)
  证明: by
  conv_rhs => rw [← union_sdiff_cancel (Set.sUnion_subset hI_ss : ⋃₀ ↑I subseteq s),
    hC.sdiff_sUnion_eq_sUnion_disjointOfDiffUnion hs hI]

Depends on / 依赖: Set.sUnion_subset, conv_rhs, hC.sdiff_sUnion_eq_sUnion_disjointOfDiffUnion, hI_ss, sUnion_subset, sdiff_sUnion_eq_sUnion_disjointOfDiffUnion, subseteq, union_sdiff_cancel
-/
lemma sUnion_union_sUnion_disjointOfDiffUnion_of_subset (hC : IsSetSemiring C)
    (hs : s in C) (hI : ↑I subseteq C) (hI_ss : forall t in I, t subseteq s) :
    ⋃₀ I union ⋃₀ hC.disjointOfDiffUnion hs hI = s := by
  conv_rhs => rw [← union_sdiff_cancel (Set.sUnion_subset hI_ss : ⋃₀ ↑I subseteq s),
    hC.sdiff_sUnion_eq_sUnion_disjointOfDiffUnion hs hI]

/--
lemma `sUnion_union_disjointOfDiffUnion_of_subset` / 引理 `sUnion_union_disjointOfDiffUnion_of_subset`

English:
lemma sUnion_union_disjointOfDiffUnion_of_subset
  statement: (hC : IsSetSemiring C) (hs : s in C)
  proof: by
  conv_rhs => rw [← sUnion_union_sUnion_disjointOfDiffUnion_of_subset hC hs hI hI_ss]
  simp_rw [coe_union]
  rw [sUnion_union]

中文:
引理 sUnion_union_disjointOfDiffUnion_of_subset
  结论: (hC : 是SetSemiring C) (hs : s in C)
  证明: by
  conv_rhs => rw [← sUnion_union_sUnion_disjointOfDiffUnion_of_subset hC hs hI hI_ss]
  simp_rw [coe_union]
  rw [sUnion_union]

Depends on / 依赖: coe_union, conv_rhs, hI_ss, sUnion_union, sUnion_union_sUnion_disjointOfDiffUnion_of_subset, simp_rw
-/
lemma sUnion_union_disjointOfDiffUnion_of_subset (hC : IsSetSemiring C) (hs : s in C)
    (hI : ↑I subseteq C) (hI_ss : forall t in I, t subseteq s) :
    ⋃₀ ↑(I union hC.disjointOfDiffUnion hs hI) = s := by
  conv_rhs => rw [← sUnion_union_sUnion_disjointOfDiffUnion_of_subset hC hs hI hI_ss]
  simp_rw [coe_union]
  rw [sUnion_union]

end disjointOfDiffUnion

section disjointOfUnion


variable {j : Set α} {J : Finset (Set α)}

open MeasureTheory Order

/--
theorem `exists_partition_disjointed` / 定理 `exists_partition_disjointed`

English:
theorem exists_partition_disjointed
  given: (hC : IsSetSemiring C) (hJ : ↑J subseteq C) (j : J)
  proof: hC.mem_supClosure_iff.mp
    hC.isSetRing_supClosure.disjointed_mem (fun _ => subset_supClosure (hJ (Subtype.coe_prop _))) _

中文:
定理 存在_partition_disjointed
  条件: (hC : 是SetSemiring C) (hJ : ↑J subseteq C) (j : J)
  证明: hC.mem_supClosure_iff.mp
    hC.isSetRing_supClosure.disjointed_mem (fun _ => subset_supClosure (hJ (Subtype.coe_prop _))) _
-/
private theorem exists_partition_disjointed (hC : IsSetSemiring C) (hJ : ↑J subseteq C) (j : J) :
    exists P : Finpartition (disjointed (fun i => (J.equivFin.symm i : Set α)) (J.equivFin j)),
      ↑P.parts subseteq C :=
hC.mem_supClosure_iff.mp
    hC.isSetRing_supClosure.disjointed_mem (fun _ => subset_supClosure (hJ (Subtype.coe_prop _))) _

/--
Definition of `disjointOfUnion` / `disjointOfUnion` 的定义

English:
definition disjointOfUnion
  signature: (hC : IsSetSemiring C) (hJ : ↑J subseteq C) (j : Set α)
  body: if hj : j in J then (hC.exists_partition_disjointed hJ ⟨j, hj⟩).choose.parts else ∅

中文:
定义 disjointOfUnion
  签名: (hC : 是SetSemiring C) (hJ : ↑J subseteq C) (j : 集合 α)
  定义体: if hj : j in J then (hC.exists_partition_disjointed hJ ⟨j, hj⟩).choose.parts else ∅

Depends on / 依赖: choose.parts, exists_partition_disjointed, hC.exists_partition_disjointed
-/
noncomputable def disjointOfUnion (hC : IsSetSemiring C) (hJ : ↑J subseteq C) (j : Set α) :
    Finset (Set α) :=
  if hj : j in J then (hC.exists_partition_disjointed hJ ⟨j, hj⟩).choose.parts else ∅

/--
theorem `disjointOfUnion_coe` / 定理 `disjointOfUnion_coe`

English:
theorem disjointOfUnion_coe
  given: (hC : IsSetSemiring C) (hJ : ↑J subseteq C) (j : J)
  proof: by
  rw [disjointOfUnion]; rw [dif_pos j.2]

中文:
定理 disjointOfUnion_coe
  条件: (hC : 是SetSemiring C) (hJ : ↑J subseteq C) (j : J)
  证明: by
  rw [disjointOfUnion]; rw [dif_pos j.2]
-/
private theorem disjointOfUnion_coe (hC : IsSetSemiring C) (hJ : ↑J subseteq C) (j : J) :
    hC.disjointOfUnion hJ j = (hC.exists_partition_disjointed hJ j).choose.parts := by
  rw [disjointOfUnion]; rw [dif_pos j.2]

/--
lemma `pairwiseDisjoint_disjointOfUnion` / 引理 `pairwiseDisjoint_disjointOfUnion`

English:
lemma pairwiseDisjoint_disjointOfUnion
  given: (hC : IsSetSemiring C) (hJ : ↑J subseteq C)
  proof: by
  refine Pairwise.set_of_subtype _ _ fun j k hjk => ?_
  simp_rw [Function.onFun, hC.disjointOfUnion_coe hJ, Finset.disjoint_iff_ne]
exact fun s hs t ht => Disjoint.ne (Finpartition.ne_bot _ hs)
.mono (Finpartition.le _ hs) (Finpartition.le _ ht)
disjoint_disjointed _ J.equivFin.injective.ne hjk

中文:
引理 pairwiseDisjoint_disjointOfUnion
  条件: (hC : 是SetSemiring C) (hJ : ↑J subseteq C)
  证明: by
  refine Pairwise.set_of_subtype _ _ fun j k hjk => ?_
  simp_rw [Function.onFun, hC.disjointOfUnion_coe hJ, Finset.disjoint_iff_ne]
exact fun s hs t ht => Disjoint.ne (Finpartition.ne_bot _ hs)
.mono (Finpartition.le _ hs) (Finpartition.le _ ht)
disjoint_disjointed _ J.equivFin.injective.ne hjk

Depends on / 依赖: Disjoint, Disjoint.ne, Finpartition, Finpartition.le, Finpartition.ne_bot, Finset, Finset.disjoint_iff_ne, Function, Function.onFun, J.equivFin.injective.ne, Pairwise, Pairwise.set_of_subtype, disjointOfUnion_coe, disjoint_disjointed, disjoint_iff_ne, equivFin, hC.disjointOfUnion_coe, injective, ne_bot, set_of_subtype
-/
lemma pairwiseDisjoint_disjointOfUnion (hC : IsSetSemiring C) (hJ : ↑J subseteq C) :
    PairwiseDisjoint J (hC.disjointOfUnion hJ) := by
  refine Pairwise.set_of_subtype _ _ fun j k hjk => ?_
  simp_rw [Function.onFun, hC.disjointOfUnion_coe hJ, Finset.disjoint_iff_ne]
exact fun s hs t ht => Disjoint.ne (Finpartition.ne_bot _ hs)
.mono (Finpartition.le _ hs) (Finpartition.le _ ht)
disjoint_disjointed _ J.equivFin.injective.ne hjk

/--
lemma `disjointOfUnion_subset` / 引理 `disjointOfUnion_subset`

English:
lemma disjointOfUnion_subset
  given: (hC : IsSetSemiring C) (hJ : ↑J subseteq C) (hj : j in J)
  proof: by
  lift j to J using hj
  rw [hC.disjointOfUnion_coe hJ]
  exact (hC.exists_partition_disjointed hJ j).choose_spec

中文:
引理 disjointOfUnion_subset
  条件: (hC : 是SetSemiring C) (hJ : ↑J subseteq C) (hj : j in J)
  证明: by
  lift j to J using hj
  rw [hC.disjointOfUnion_coe hJ]
  exact (hC.exists_partition_disjointed hJ j).choose_spec

Depends on / 依赖: choose_spec, disjointOfUnion_coe, exists_partition_disjointed, hC.disjointOfUnion_coe, hC.exists_partition_disjointed
-/
lemma disjointOfUnion_subset (hC : IsSetSemiring C) (hJ : ↑J subseteq C) (hj : j in J) :
    (disjointOfUnion hC hJ j : Set (Set α)) subseteq C := by
  lift j to J using hj
  rw [hC.disjointOfUnion_coe hJ]
  exact (hC.exists_partition_disjointed hJ j).choose_spec

/--
lemma `pairwiseDisjoint_disjointOfUnion_of_mem` / 引理 `pairwiseDisjoint_disjointOfUnion_of_mem`

English:
lemma pairwiseDisjoint_disjointOfUnion_of_mem
  given: (hC : IsSetSemiring C) (hJ : ↑J subseteq C) (hj : j in J)
  proof: by
  lift j to J using hj
  rw [disjointOfUnion_coe]; rw [← supIndep_iff_pairwiseDisjoint]
  exact Finpartition.supIndep _

中文:
引理 pairwiseDisjoint_disjointOfUnion_of_mem
  条件: (hC : 是SetSemiring C) (hJ : ↑J subseteq C) (hj : j in J)
  证明: by
  lift j to J using hj
  rw [disjointOfUnion_coe]; rw [← supIndep_iff_pairwiseDisjoint]
  exact Finpartition.supIndep _

Depends on / 依赖: Finpartition, Finpartition.supIndep, disjointOfUnion_coe, supIndep, supIndep_iff_pairwiseDisjoint
-/
lemma pairwiseDisjoint_disjointOfUnion_of_mem (hC : IsSetSemiring C) (hJ : ↑J subseteq C) (hj : j in J) :
    PairwiseDisjoint (hC.disjointOfUnion hJ j : Set (Set α)) id := by
  lift j to J using hj
  rw [disjointOfUnion_coe]; rw [← supIndep_iff_pairwiseDisjoint]
  exact Finpartition.supIndep _

/--
lemma `pairwiseDisjoint_biUnion_disjointOfUnion` / 引理 `pairwiseDisjoint_biUnion_disjointOfUnion`

English:
lemma pairwiseDisjoint_biUnion_disjointOfUnion
  given: (hC : IsSetSemiring C) (hJ : ↑J subseteq C)
  proof: by
  simp_rw [← SetLike.mem_coe]
  refine Set.PairwiseDisjoint.biUnion
    (Pairwise.set_of_subtype _ _ ?_)
    (fun _ => hC.pairwiseDisjoint_disjointOfUnion_of_mem hJ)
  simp_rw [Function.onFun, disjointOfUnion_coe, SetLike.mem_coe, ← Finset.sup_eq_iSup,
    Finpartition.sup_parts]
  exact (disjoin

中文:
引理 pairwiseDisjoint_biUnion_disjointOfUnion
  条件: (hC : 是SetSemiring C) (hJ : ↑J subseteq C)
  证明: by
  simp_rw [← SetLike.mem_coe]
  refine Set.PairwiseDisjoint.biUnion
    (Pairwise.set_of_subtype _ _ ?_)
    (fun _ => hC.pairwiseDisjoint_disjointOfUnion_of_mem hJ)
  simp_rw [Function.onFun, disjointOfUnion_coe, SetLike.mem_coe, ← Finset.sup_eq_iSup,
    Finpartition.sup_parts]
  exact (disjoin

Depends on / 依赖: Finpartition, Finpartition.sup_parts, Finset, Finset.sup_eq_iSup, Function, Function.onFun, J.equivFin.injective, Pairwise, Pairwise.set_of_subtype, PairwiseDisjoint, Set.PairwiseDisjoint.biUnion, SetLike, SetLike.mem_coe, biUnion, comp_of_injective, disjointOfUnion_coe, disjoint_disjointed, equivFin, hC.pairwiseDisjoint_disjointOfUnion_of_mem, injective
-/
lemma pairwiseDisjoint_biUnion_disjointOfUnion (hC : IsSetSemiring C) (hJ : ↑J subseteq C) :
    PairwiseDisjoint (⋃ x in J, (hC.disjointOfUnion hJ x : Set (Set α))) id := by
  simp_rw [← SetLike.mem_coe]
  refine Set.PairwiseDisjoint.biUnion
    (Pairwise.set_of_subtype _ _ ?_)
    (fun _ => hC.pairwiseDisjoint_disjointOfUnion_of_mem hJ)
  simp_rw [Function.onFun, disjointOfUnion_coe, SetLike.mem_coe, ← Finset.sup_eq_iSup,
    Finpartition.sup_parts]
  exact (disjoint_disjointed _).comp_of_injective J.equivFin.injective

/--
lemma `disjointOfUnion_subset_of_mem` / 引理 `disjointOfUnion_subset_of_mem`

English:
lemma disjointOfUnion_subset_of_mem
  given: (hC : IsSetSemiring C) (hJ : ↑J subseteq C) (hj : j in J)
  proof: by
  lift j to J using hj
  grw [disjointOfUnion_coe, ← Finset.sup_id_set_eq_sUnion, Finpartition.sup_parts,
    disjointed_subset, Equiv.symm_apply_apply]

中文:
引理 disjointOfUnion_subset_of_mem
  条件: (hC : 是SetSemiring C) (hJ : ↑J subseteq C) (hj : j in J)
  证明: by
  lift j to J using hj
  grw [disjointOfUnion_coe, ← Finset.sup_id_set_eq_sUnion, Finpartition.sup_parts,
    disjointed_subset, Equiv.symm_apply_apply]

Depends on / 依赖: Equiv.symm_apply_apply, Finpartition, Finpartition.sup_parts, Finset, Finset.sup_id_set_eq_sUnion, disjointOfUnion_coe, disjointed_subset, sup_id_set_eq_sUnion, sup_parts, symm_apply_apply
-/
lemma disjointOfUnion_subset_of_mem (hC : IsSetSemiring C) (hJ : ↑J subseteq C) (hj : j in J) :
    ⋃₀ hC.disjointOfUnion hJ j subseteq j := by
  lift j to J using hj
  grw [disjointOfUnion_coe, ← Finset.sup_id_set_eq_sUnion, Finpartition.sup_parts,
    disjointed_subset, Equiv.symm_apply_apply]

/--
lemma `subset_of_mem_disjointOfUnion` / 引理 `subset_of_mem_disjointOfUnion`

English:
lemma subset_of_mem_disjointOfUnion
  statement: (hC : IsSetSemiring C) (hJ : ↑J subseteq C) (hj : j in J) {x : Set α}
  proof: sUnion_subset_iff.mp (hC.disjointOfUnion_subset_of_mem hJ hj) x hx

中文:
引理 subset_of_mem_disjointOfUnion
  结论: (hC : 是SetSemiring C) (hJ : ↑J subseteq C) (hj : j in J) {x : 集合 α}
  证明: sUnion_subset_iff.mp (hC.disjointOfUnion_subset_of_mem hJ hj) x hx

Depends on / 依赖: IsTrans, IsTrans.trans, disjointOfUnion_subset_of_mem, hC.disjointOfUnion_subset_of_mem, sUnion_subset_iff, sUnion_subset_iff.mp
-/
lemma subset_of_mem_disjointOfUnion (hC : IsSetSemiring C) (hJ : ↑J subseteq C) (hj : j in J) {x : Set α}
    (hx : x in (hC.disjointOfUnion hJ) j) : x subseteq j :=
  sUnion_subset_iff.mp (hC.disjointOfUnion_subset_of_mem hJ hj) x hx

/--
lemma `empty_notMem_disjointOfUnion` / 引理 `empty_notMem_disjointOfUnion`

English:
lemma empty_notMem_disjointOfUnion
  given: (hC : IsSetSemiring C) (hJ : ↑J subseteq C) (hj : j in J)
  proof: by
  lift j to J using hj
  rw [disjointOfUnion_coe]
  exact Finpartition.bot_notMem _

中文:
引理 empty_notMem_disjointOfUnion
  条件: (hC : 是SetSemiring C) (hJ : ↑J subseteq C) (hj : j in J)
  证明: by
  lift j to J using hj
  rw [disjointOfUnion_coe]
  exact Finpartition.bot_notMem _

Depends on / 依赖: Finpartition, Finpartition.bot_notMem, IsTrans, bot_notMem, disjointOfUnion_coe
-/
lemma empty_notMem_disjointOfUnion (hC : IsSetSemiring C) (hJ : ↑J subseteq C) (hj : j in J) :
    ∅ ∉ hC.disjointOfUnion hJ j := by
  lift j to J using hj
  rw [disjointOfUnion_coe]
  exact Finpartition.bot_notMem _

/--
lemma `sUnion_disjointOfUnion` / 引理 `sUnion_disjointOfUnion`

English:
lemma sUnion_disjointOfUnion
  given: (hC : IsSetSemiring C) (hJ : ↑J subseteq C)
  proof: by
  simp_rw [sUnion_iUnion, ← iSup_eq_iUnion, iSup_subtype', disjointOfUnion_coe,
    ← Finset.sup_id_set_eq_sUnion, Finpartition.sup_parts, J.equivFin.surjective.iSup_comp,
    iSup_disjointed, J.equivFin.symm.surjective.iSup_comp, iSup_subtype, Finset.sup_eq_iSup, id]

中文:
引理 sUnion_disjointOfUnion
  条件: (hC : 是SetSemiring C) (hJ : ↑J subseteq C)
  证明: by
  simp_rw [sUnion_iUnion, ← iSup_eq_iUnion, iSup_subtype', disjointOfUnion_coe,
    ← Finset.sup_id_set_eq_sUnion, Finpartition.sup_parts, J.equivFin.surjective.iSup_comp,
    iSup_disjointed, J.equivFin.symm.surjective.iSup_comp, iSup_subtype, Finset.sup_eq_iSup, id]

Depends on / 依赖: Finpartition, Finpartition.sup_parts, Finset, Finset.sup_eq_iSup, Finset.sup_id_set_eq_sUnion, J.equivFin.surjective.iSup_comp, J.equivFin.symm.surjective.iSup_comp, disjointOfUnion_coe, equivFin, iSup_comp, iSup_disjointed, iSup_eq_iUnion, iSup_subtype, sUnion_iUnion, simp_rw, sup_eq_iSup, sup_id_set_eq_sUnion, sup_parts, surjective
-/
lemma sUnion_disjointOfUnion (hC : IsSetSemiring C) (hJ : ↑J subseteq C) :
    ⋃₀ ⋃ x in J, (hC.disjointOfUnion hJ x : Set (Set α)) = ⋃₀ J := by
  simp_rw [sUnion_iUnion, ← iSup_eq_iUnion, iSup_subtype', disjointOfUnion_coe,
    ← Finset.sup_id_set_eq_sUnion, Finpartition.sup_parts, J.equivFin.surjective.iSup_comp,
    iSup_disjointed, J.equivFin.symm.surjective.iSup_comp, iSup_subtype, Finset.sup_eq_iSup, id]

/--
theorem `disjointOfUnion_props` / 定理 `disjointOfUnion_props`

English:
theorem disjointOfUnion_props
  given: (hC : IsSetSemiring C) (h1 : ↑J subseteq C)
  proof: ⟨hC.disjointOfUnion h1,
   hC.pairwiseDisjoint_disjointOfUnion h1,
   fun _ => hC.disjointOfUnion_subset h1,
   hC.pairwiseDisjoint_biUnion_disjointOfUnion h1,
   fun _ => hC.disjointOfUnion_subset_of_mem h1,
   fun _ => hC.empty_notMem_disjointOfUnion h1,
   (hC.sUnion_disjointOfUnion h1).symm⟩

中文:
定理 disjointOfUnion_props
  条件: (hC : 是SetSemiring C) (h1 : ↑J subseteq C)
  证明: ⟨hC.disjointOfUnion h1,
   hC.pairwiseDisjoint_disjointOfUnion h1,
   fun _ => hC.disjointOfUnion_subset h1,
   hC.pairwiseDisjoint_biUnion_disjointOfUnion h1,
   fun _ => hC.disjointOfUnion_subset_of_mem h1,
   fun _ => hC.empty_notMem_disjointOfUnion h1,
   (hC.sUnion_disjointOfUnion h1).symm⟩

Depends on / 依赖: disjointOfUnion, disjointOfUnion_subset, disjointOfUnion_subset_of_mem, empty_notMem_disjointOfUnion, hC.disjointOfUnion, hC.disjointOfUnion_subset, hC.disjointOfUnion_subset_of_mem, hC.empty_notMem_disjointOfUnion, hC.pairwiseDisjoint_biUnion_disjointOfUnion, hC.pairwiseDisjoint_disjointOfUnion, hC.sUnion_disjointOfUnion, pairwiseDisjoint_biUnion_disjointOfUnion, pairwiseDisjoint_disjointOfUnion, sUnion_disjointOfUnion
-/
theorem disjointOfUnion_props (hC : IsSetSemiring C) (h1 : ↑J subseteq C) :
    exists K : Set α -> Finset (Set α),
      PairwiseDisjoint J K
      ∧ (forall i in J, ↑(K i) subseteq C)
      ∧ PairwiseDisjoint (⋃ x in J, (K x : Set (Set α))) id
      ∧ (forall j in J, ⋃₀ K j subseteq j)
      ∧ (forall j in J, ∅ ∉ K j)
      ∧ ⋃₀ J = ⋃₀ (⋃ x in J, (K x : Set (Set α))) :=
  ⟨hC.disjointOfUnion h1,
   hC.pairwiseDisjoint_disjointOfUnion h1,
   fun _ => hC.disjointOfUnion_subset h1,
   hC.pairwiseDisjoint_biUnion_disjointOfUnion h1,
   fun _ => hC.disjointOfUnion_subset_of_mem h1,
   fun _ => hC.empty_notMem_disjointOfUnion h1,
   (hC.sUnion_disjointOfUnion h1).symm⟩

end disjointOfUnion

/--
lemma `_root_.Set.Ioc_mem_ofPred_Ioc_le` / 引理 `_root_.Set.Ioc_mem_ofPred_Ioc_le`

English:
lemma _root_.Set.Ioc_mem_ofPred_Ioc_le
  given: [LinearOrder α] (u v : α)
  proof: ⟨u, max u v, by grind, by grind⟩

中文:
引理 _root_.集合.Ioc_mem_ofPred_Ioc_le
  条件: [线性序 α] (u v : α)
  证明: ⟨u, max u v, by grind, by grind⟩
-/
private lemma _root_.Set.Ioc_mem_ofPred_Ioc_le [LinearOrder α] (u v : α) :
    Set.Ioc u v in {s : Set α | exists u v, u <= v ∧ s = Set.Ioc u v} :=
  ⟨u, max u v, by grind, by grind⟩

/--
lemma `Ioc` / 引理 `Ioc`

English:
lemma Ioc
  given: [LinearOrder α] [Nonempty α]
  proof: by
    inhabit α
    exact ⟨default, default, le_rfl, by simp⟩
  inter_mem := by
    rintro s ⟨u, v, huv, rfl⟩ t ⟨u', v', hu'v', rfl⟩
    rw [Set.Ioc_inter_Ioc]
    apply Ioc_mem_ofPred_Ioc_le
  sdiff_eq_sUnion' := by
    rintro s ⟨u, v, huv, rfl⟩ t ⟨u', v', hu'v', rfl⟩
    rcases le_or_gt u' u with

中文:
引理 左开右闭区间
  条件: [线性序 α] [非空 α]
  证明: by
    inhabit α
    exact ⟨default, default, le_rfl, by simp⟩
  inter_mem := by
    rintro s ⟨u, v, huv, rfl⟩ t ⟨u', v', hu'v', rfl⟩
    rw [Set.Ioc_inter_Ioc]
    apply Ioc_mem_ofPred_Ioc_le
  sdiff_eq_sUnion' := by
    rintro s ⟨u, v, huv, rfl⟩ t ⟨u', v', hu'v', rfl⟩
    rcases le_or_gt u' u with
-/
protected lemma Ioc [LinearOrder α] [Nonempty α] :
    IsSetSemiring {s : Set α | exists u v, u <= v ∧ s = Set.Ioc u v} where
  empty_mem := by
    inhabit α
    exact ⟨default, default, le_rfl, by simp⟩
  inter_mem := by
    rintro s ⟨u, v, huv, rfl⟩ t ⟨u', v', hu'v', rfl⟩
    rw [Set.Ioc_inter_Ioc]
    apply Ioc_mem_ofPred_Ioc_le
  sdiff_eq_sUnion' := by
    rintro s ⟨u, v, huv, rfl⟩ t ⟨u', v', hu'v', rfl⟩
    rcases le_or_gt u' u with hu | hu
    · rcases Ioc_mem_ofPred_Ioc_le (max u v') v with ⟨u'', v'', h'', heq⟩
      exists {Set.Ioc u'' v''}
      grind [coe_singleton, pairwiseDisjoint_singleton]
    rcases le_or_gt v v' with hv | hv
    · rcases Ioc_mem_ofPred_Ioc_le u (min u' v) with ⟨u'', v'', h'', heq⟩
      exists {Set.Ioc u'' v''}
      grind [coe_singleton, pairwiseDisjoint_singleton]
    rw [show Set.Ioc u v \ Set.Ioc u' v' = Set.Ioc u u' union Set.Ioc v' v by grind]
    refine ⟨{Set.Ioc u u', Set.Ioc v' v}, by grind, ?_, by simp⟩
    intro a ha b hb hab
    simp [Function.onFun]
    grind

end IsSetSemiring

end MeasureTheory
