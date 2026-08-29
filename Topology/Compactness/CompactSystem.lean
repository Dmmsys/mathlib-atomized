/-
Copyright (c) 2025 Peter Pfaffelhuber. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Peter Pfaffelhuber
-/
module

public import Mathlib.MeasureTheory.PiSystem
public import Mathlib.Topology.Separation.Hausdorff

/-!
# Compact systems

This file defines compact systems of sets.

## Main definitions

* `IsCompactSystem`: A set of sets is a compact system if, whenever a countable subfamily has empty
  intersection, then finitely many of them already have empty intersection.

## Main results

* `isCompactSystem_insert_univ_iff`: A set system is a compact system iff inserting `univ`
  gives a compact system.
* `isCompactSystem_isCompact_isClosed`: The set of closed and compact sets is a compact system.
* `isCompactSystem_isCompact`: In a `T2Space`, the set of compact sets is a compact system.
-/

@[expose] public section

open Set Finset Nat

variable {α : Type*} {S : Set (Set α)} {C : Nat -> Set α}

section definition

/--
Definition of `IsCompactSystem` / `IsCompactSystem` 的定义

English:
definition IsCompactSystem
  signature: (S : Set (Set α))
  body: forall C : Nat -> Set α, (forall i, C i in S) -> ⋂ i, C i = ∅ -> exists (n : Nat), dissipate C n = ∅

中文:
定义 IsCompactSystem
  签名: (S : Set (Set α))
  定义体: forall C : Nat -> Set α, (forall i, C i in S) -> ⋂ i, C i = ∅ -> exists (n : Nat), dissipate C n = ∅

Depends on / 依赖: dissipate
-/
def IsCompactSystem (S : Set (Set α)) : Prop :=
  forall C : Nat -> Set α, (forall i, C i in S) -> ⋂ i, C i = ∅ -> exists (n : Nat), dissipate C n = ∅

end definition

namespace IsCompactSystem

/--
lemma `of_nonempty_iInter` / 引理 `of_nonempty_iInter`

English:
lemma of_nonempty_iInter
  proof: by
  intro C hC
  contrapose!
  exact h C hC

中文:
引理 of_nonempty_iInter
  证明: by
  intro C hC
  contrapose!
  exact h C hC

Depends on / 依赖: contrapose
-/
lemma of_nonempty_iInter
    (h : forall C : Nat -> Set α, (forall i, C i in S) -> (forall n, (dissipate C n).Nonempty) -> (⋂ i, C i).Nonempty) :
    IsCompactSystem S := by
  intro C hC
  contrapose!
  exact h C hC

/--
lemma `nonempty_iInter` / 引理 `nonempty_iInter`

English:
lemma nonempty_iInter
  statement: (hp : IsCompactSystem S) {C : Nat -> Set α} (hC : forall i, C i in S)
  proof: by
  revert h_nonempty
  contrapose!
  exact hp C hC

中文:
引理 nonempty_iInter
  结论: (hp : IsCompactSystem S) {C : 自然数 -> Set α} (hC : 对任意 i, C i in S)
  证明: by
  revert h_nonempty
  contrapose!
  exact hp C hC

Depends on / 依赖: contrapose, h_nonempty, revert
-/
lemma nonempty_iInter (hp : IsCompactSystem S) {C : Nat -> Set α} (hC : forall i, C i in S)
    (h_nonempty : forall n, (dissipate C n).Nonempty) :
    (⋂ i, C i).Nonempty := by
  revert h_nonempty
  contrapose!
  exact hp C hC

/--
theorem `iff_nonempty_iInter` / 定理 `iff_nonempty_iInter`

English:
theorem iff_nonempty_iInter
  given: (S : Set (Set α))
  proof: ⟨nonempty_iInter, of_nonempty_iInter⟩

@[simp]

中文:
定理 iff_nonempty_iInter
  条件: (S : Set (Set α))
  证明: ⟨nonempty_iInter, of_nonempty_iInter⟩

@[simp]

Depends on / 依赖: nonempty_iInter, of_nonempty_iInter
-/
theorem iff_nonempty_iInter (S : Set (Set α)) :
    IsCompactSystem S ↔
      forall C : Nat -> Set α, (forall i, C i in S) -> (forall n, (dissipate C n).Nonempty) -> (⋂ i, C i).Nonempty :=
  ⟨nonempty_iInter, of_nonempty_iInter⟩

@[simp]
/--
lemma `of_IsEmpty` / 引理 `of_IsEmpty`

English:
lemma of_IsEmpty
  given: [IsEmpty α] (S : Set (Set α))
  statement: IsCompactSystem S
  proof: fun s _ _ => ⟨0, Set.eq_empty_of_isEmpty (dissipate s 0)⟩

中文:
引理 of_IsEmpty
  条件: [IsEmpty α] (S : Set (Set α))
  结论: IsCompactSystem S
  证明: fun s _ _ => ⟨0, Set.eq_empty_of_isEmpty (dissipate s 0)⟩

Depends on / 依赖: Set.eq_empty_of_isEmpty, dissipate, eq_empty_of_isEmpty
-/
lemma of_IsEmpty [IsEmpty α] (S : Set (Set α)) : IsCompactSystem S :=
  fun s _ _ => ⟨0, Set.eq_empty_of_isEmpty (dissipate s 0)⟩

/--
theorem `mono` / 定理 `mono`

English:
theorem mono
  given: {T : Set (Set α)} (hT : IsCompactSystem T) (hST : S subseteq T)
  proof: fun C hC1 hC2 => hT C (fun i => hST (hC1 i)) hC2

中文:
定理 mono
  条件: {T : Set (Set α)} (hT : IsCompactSystem T) (hST : S subseteq T)
  证明: fun C hC1 hC2 => hT C (fun i => hST (hC1 i)) hC2
-/
theorem mono {T : Set (Set α)} (hT : IsCompactSystem T) (hST : S subseteq T) :
    IsCompactSystem S := fun C hC1 hC2 => hT C (fun i => hST (hC1 i)) hC2

/--
lemma `insert_empty` / 引理 `insert_empty`

English:
lemma insert_empty
  given: (h : IsCompactSystem S)
  statement: IsCompactSystem (insert ∅ S)
  proof: by
  intro s h' hd
  by_cases! g : exists n, s n = ∅
  · use g.choose
    rw [← subset_empty_iff] at hd ⊢
    exact (dissipate_subset le_rfl).trans g.choose_spec.le
  · exact h s (fun i => (mem_of_mem_insert_of_ne (h' i) (g i).ne_empty)) hd

中文:
引理 insert_empty
  条件: (h : IsCompactSystem S)
  结论: IsCompactSystem (insert ∅ S)
  证明: by
  intro s h' hd
  by_cases! g : exists n, s n = ∅
  · use g.choose
    rw [← subset_empty_iff] at hd ⊢
    exact (dissipate_subset le_rfl).trans g.choose_spec.le
  · exact h s (fun i => (mem_of_mem_insert_of_ne (h' i) (g i).ne_empty)) hd

Depends on / 依赖: choose_spec, dissipate_subset, g.choose, g.choose_spec.le, le_rfl, mem_of_mem_insert_of_ne, ne_empty, subset_empty_iff
-/
lemma insert_empty (h : IsCompactSystem S) : IsCompactSystem (insert ∅ S) := by
  intro s h' hd
  by_cases! g : exists n, s n = ∅
  · use g.choose
    rw [← subset_empty_iff] at hd ⊢
    exact (dissipate_subset le_rfl).trans g.choose_spec.le
  · exact h s (fun i => (mem_of_mem_insert_of_ne (h' i) (g i).ne_empty)) hd

/--
lemma `insert_univ` / 引理 `insert_univ`

English:
lemma insert_univ
  given: (h : IsCompactSystem S)
  statement: IsCompactSystem (insert univ S)
  proof: by
  rcases isEmpty_or_nonempty α with hα | _
  · simp
  rw [IsCompactSystem.iff_nonempty_iInter] at h ⊢
  intro s h' hd
  by_cases! h₀ : forall n, s n ∉ S
  · simp_all
  classical
  let n := Nat.find h₀
  let s' := fun i => if s i in S then s i else s n
  have h₁ : forall i, s' i in S := by grind
 

中文:
引理 insert_univ
  条件: (h : IsCompactSystem S)
  结论: IsCompactSystem (insert univ S)
  证明: by
  rcases isEmpty_or_nonempty α with hα | _
  · simp
  rw [IsCompactSystem.iff_nonempty_iInter] at h ⊢
  intro s h' hd
  by_cases! h₀ : forall n, s n ∉ S
  · simp_all
  classical
  let n := Nat.find h₀
  let s' := fun i => if s i in S then s i else s n
  have h₁ : forall i, s' i in S := by grind
 

Depends on / 依赖: IsCompactSystem, IsCompactSystem.iff_nonempty_iInter, Nat.find, classical, dissipate, iff_nonempty_iInter, isEmpty_or_nonempty
-/
lemma insert_univ (h : IsCompactSystem S) : IsCompactSystem (insert univ S) := by
  rcases isEmpty_or_nonempty α with hα | _
  · simp
  rw [IsCompactSystem.iff_nonempty_iInter] at h ⊢
  intro s h' hd
  by_cases! h₀ : forall n, s n ∉ S
  · simp_all
  classical
  let n := Nat.find h₀
  let s' := fun i => if s i in S then s i else s n
  have h₁ : forall i, s' i in S := by grind
  have h₂ : ⋂ i, s i = ⋂ i, s' i := by ext; simp; grind
  apply h₂ ▸ h s' h₁
  by_contra! ⟨j, hj⟩
  have h₃ (v : Nat) (hv : n <= v) : dissipate s v = dissipate s' v := by ext; simp; grind
  have h₇ : dissipate s' (max j n) = ∅ := by
    rw [← subset_empty_iff] at hj ⊢
    exact (antitone_dissipate (Nat.le_max_left j n)).trans hj
  specialize h₃ (max j n) (Nat.le_max_right j n)
  specialize hd (max j n)
  simp [h₃, h₇] at hd

end IsCompactSystem

/--
lemma `isCompactSystem_iff_nonempty_iInter_of_lt` / 引理 `isCompactSystem_iff_nonempty_iInter_of_lt`

English:
lemma isCompactSystem_iff_nonempty_iInter_of_lt
  given: (S : Set (Set α))
  proof: by
  simp_rw [IsCompactSystem.iff_nonempty_iInter]
  refine ⟨fun h C hi h'=> h C hi (fun n => dissipate_eq_biInter_lt ▸ (h' (n + 1))),
    fun h C hi h' => h C hi ?_⟩
  simp_rw [Set.nonempty_iff_ne_empty] at h' ⊢
  refine fun n g => h' n ?_
  simp_rw [← subset_empty_iff, dissipate] at g ⊢
  exact le

中文:
引理 isCompactSystem_iff_nonempty_iInter_of_lt
  条件: (S : Set (Set α))
  证明: by
  simp_rw [IsCompactSystem.iff_nonempty_iInter]
  refine ⟨fun h C hi h'=> h C hi (fun n => dissipate_eq_biInter_lt ▸ (h' (n + 1))),
    fun h C hi h' => h C hi ?_⟩
  simp_rw [Set.nonempty_iff_ne_empty] at h' ⊢
  refine fun n g => h' n ?_
  simp_rw [← subset_empty_iff, dissipate] at g ⊢
  exact le

Depends on / 依赖: IsCompactSystem, IsCompactSystem.iff_nonempty_iInter, Set.nonempty_iff_ne_empty, dissipate, dissipate_eq_biInter_lt, iff_nonempty_iInter, le_trans, nonempty_iff_ne_empty, simp_rw, subset_empty_iff
-/
lemma isCompactSystem_iff_nonempty_iInter_of_lt (S : Set (Set α)) :
    IsCompactSystem S ↔
      forall C : Nat -> Set α, (forall i, C i in S) -> (forall n, (⋂ k < n, C k).Nonempty) -> (⋂ i, C i).Nonempty := by
  simp_rw [IsCompactSystem.iff_nonempty_iInter]
  refine ⟨fun h C hi h'=> h C hi (fun n => dissipate_eq_biInter_lt ▸ (h' (n + 1))),
    fun h C hi h' => h C hi ?_⟩
  simp_rw [Set.nonempty_iff_ne_empty] at h' ⊢
  refine fun n g => h' n ?_
  simp_rw [← subset_empty_iff, dissipate] at g ⊢
  exact le_trans (fun x => by simp; grind) g

/--
lemma `isCompactSystem_insert_empty_iff` / 引理 `isCompactSystem_insert_empty_iff`

English:
lemma isCompactSystem_insert_empty_iff
  proof: ⟨fun h => h.mono (subset_insert _ _), .insert_empty⟩

中文:
引理 isCompactSystem_insert_empty_iff
  证明: ⟨fun h => h.mono (subset_insert _ _), .insert_empty⟩

Depends on / 依赖: h.mono, insert_empty, subset_insert
-/
lemma isCompactSystem_insert_empty_iff :
    IsCompactSystem (insert ∅ S) ↔ IsCompactSystem S :=
  ⟨fun h => h.mono (subset_insert _ _), .insert_empty⟩

/--
lemma `isCompactSystem_insert_univ_iff` / 引理 `isCompactSystem_insert_univ_iff`

English:
lemma isCompactSystem_insert_univ_iff
  statement: IsCompactSystem (insert univ S) ↔ IsCompactSystem S
  proof: ⟨fun h => h.mono (subset_insert _ _), .insert_univ⟩

中文:
引理 isCompactSystem_insert_univ_iff
  结论: IsCompactSystem (insert univ S) ↔ IsCompactSystem S
  证明: ⟨fun h => h.mono (subset_insert _ _), .insert_univ⟩

Depends on / 依赖: h.mono, insert_univ, subset_insert
-/
lemma isCompactSystem_insert_univ_iff : IsCompactSystem (insert univ S) ↔ IsCompactSystem S :=
  ⟨fun h => h.mono (subset_insert _ _), .insert_univ⟩

/--
theorem `isCompactSystem_iff_of_directed` / 定理 `isCompactSystem_iff_of_directed`

English:
theorem isCompactSystem_iff_of_directed
  given: (hpi : IsPiSystem S)
  proof: by
  rw [← isCompactSystem_insert_empty_iff]
  refine ⟨fun h => fun C hdi hi => ?_, fun h C h1 h2 => ?_⟩
  · rw [← exists_dissipate_eq_empty_iff_of_directed hdi]
    exact h C (by simp [hi])
  rw [← biInter_le_eq_iInter] at h2
  suffices (forall n, dissipate C n in S ∨ dissipate C n = ∅) ∧ (⋂ n, dis

中文:
定理 isCompactSystem_iff_of_directed
  条件: (hpi : IsPiSystem S)
  证明: by
  rw [← isCompactSystem_insert_empty_iff]
  refine ⟨fun h => fun C hdi hi => ?_, fun h C h1 h2 => ?_⟩
  · rw [← exists_dissipate_eq_empty_iff_of_directed hdi]
    exact h C (by simp [hi])
  rw [← biInter_le_eq_iInter] at h2
  suffices (forall n, dissipate C n in S ∨ dissipate C n = ∅) ∧ (⋂ n, dis

Depends on / 依赖: biInter_le_eq_iInter, directed_dissipate, dissipate, exists_dissipate_eq_empty_iff_of_directed, isCompactSystem_insert_empty_iff
-/
theorem isCompactSystem_iff_of_directed (hpi : IsPiSystem S) :
    IsCompactSystem S ↔
      forall (C : Nat -> Set α), Directed (· ⊇ ·) C -> (forall i, C i in S) -> ⋂ i, C i = ∅ -> exists n, C n = ∅ := by
  rw [← isCompactSystem_insert_empty_iff]
  refine ⟨fun h => fun C hdi hi => ?_, fun h C h1 h2 => ?_⟩
  · rw [← exists_dissipate_eq_empty_iff_of_directed hdi]
    exact h C (by simp [hi])
  rw [← biInter_le_eq_iInter] at h2
  suffices (forall n, dissipate C n in S ∨ dissipate C n = ∅) ∧ (⋂ n, dissipate C n = ∅) by
    by_cases! f : forall n, dissipate C n in S
    · exact h (dissipate C) directed_dissipate f this.2
    · obtain ⟨n, hn⟩ := f
      exact ⟨n, by simpa [hn] using this.1 n⟩
  refine ⟨fun n => ?_, h2⟩
  by_cases g : (dissipate C n).Nonempty
  · simpa [or_comm] using hpi.insert_empty.dissipate_mem h1 n g
  · exact .inr (Set.not_nonempty_iff_eq_empty.mp g)

/--
theorem `isCompactSystem_iff_nonempty_iInter_of_directed` / 定理 `isCompactSystem_iff_nonempty_iInter_of_directed`

English:
theorem isCompactSystem_iff_nonempty_iInter_of_directed
  given: (hpi : IsPiSystem S)
  proof: by
  rw [isCompactSystem_iff_of_directed hpi]
  refine ⟨fun h1 C h3 h4 => ?_, fun h1 C h3 s => ?_⟩ <;> contrapose!
  · exact h1 C h3 h4
  · exact h1 C h3 s

中文:
定理 isCompactSystem_iff_nonempty_iInter_of_directed
  条件: (hpi : IsPiSystem S)
  证明: by
  rw [isCompactSystem_iff_of_directed hpi]
  refine ⟨fun h1 C h3 h4 => ?_, fun h1 C h3 s => ?_⟩ <;> contrapose!
  · exact h1 C h3 h4
  · exact h1 C h3 s

Depends on / 依赖: contrapose, isCompactSystem_iff_of_directed
-/
theorem isCompactSystem_iff_nonempty_iInter_of_directed (hpi : IsPiSystem S) :
    IsCompactSystem S ↔
    forall (C : Nat -> Set α), (Directed (· ⊇ ·) C) -> (forall i, C i in S) -> (forall n, (C n).Nonempty) ->
      (⋂ i, C i).Nonempty := by
  rw [isCompactSystem_iff_of_directed hpi]
  refine ⟨fun h1 C h3 h4 => ?_, fun h1 C h3 s => ?_⟩ <;> contrapose!
  · exact h1 C h3 h4
  · exact h1 C h3 s

section IsCompactIsClosed

/--
theorem `isCompactSystem_isCompact_isClosed` / 定理 `isCompactSystem_isCompact_isClosed`

English:
theorem isCompactSystem_isCompact_isClosed
  given: (α : Type*) [TopologicalSpace α]
  proof: by
  refine IsCompactSystem.of_nonempty_iInter fun C hC_cc h_nonempty => ?_
  rw [← iInter_dissipate]
  refine IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed (Set.dissipate C)
    (fun n => ?_) h_nonempty ?_ (fun n => isClosed_biInter (fun i _ => (hC_cc i).2))
  · exact Set.antito

中文:
定理 isCompactSystem_isCompact_isClosed
  条件: (α : 类型) [TopologicalSpace α]
  证明: by
  refine IsCompactSystem.of_nonempty_iInter fun C hC_cc h_nonempty => ?_
  rw [← iInter_dissipate]
  refine IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed (Set.dissipate C)
    (fun n => ?_) h_nonempty ?_ (fun n => isClosed_biInter (fun i _ => (hC_cc i).2))
  · exact Set.antito

Depends on / 依赖: IsCompact, IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed, IsCompactSystem, IsCompactSystem.of_nonempty_iInter, Set.antitone_dissipate, Set.dissipate, antitone_dissipate, dissipate, hC_cc, h_nonempty, iInter_dissipate, isClosed_biInter, nonempty_iInter_of_sequence_nonempty_isCompact_isClosed, of_nonempty_iInter
-/
theorem isCompactSystem_isCompact_isClosed (α : Type*) [TopologicalSpace α] :
    IsCompactSystem {s : Set α | IsCompact s ∧ IsClosed s} := by
  refine IsCompactSystem.of_nonempty_iInter fun C hC_cc h_nonempty => ?_
  rw [← iInter_dissipate]
  refine IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed (Set.dissipate C)
    (fun n => ?_) h_nonempty ?_ (fun n => isClosed_biInter (fun i _ => (hC_cc i).2))
  · exact Set.antitone_dissipate (by lia)
  · simpa using (hC_cc 0).1

/--
theorem `isCompactSystem_isCompact` / 定理 `isCompactSystem_isCompact`

English:
theorem isCompactSystem_isCompact
  given: (α : Type*) [TopologicalSpace α] [T2Space α]
  proof: by
  convert! isCompactSystem_isCompact_isClosed α with s
  simpa using IsCompact.isClosed

中文:
定理 isCompactSystem_isCompact
  条件: (α : 类型) [TopologicalSpace α] [T2Space α]
  证明: by
  convert! isCompactSystem_isCompact_isClosed α with s
  simpa using IsCompact.isClosed

Depends on / 依赖: IsCompact, IsCompact.isClosed, convert, isClosed, isCompactSystem_isCompact_isClosed
-/
theorem isCompactSystem_isCompact (α : Type*) [TopologicalSpace α] [T2Space α] :
    IsCompactSystem {s : Set α | IsCompact s} := by
  convert! isCompactSystem_isCompact_isClosed α with s
  simpa using IsCompact.isClosed

/--
theorem `isCompactSystem_insert_univ_isCompact_isClosed` / 定理 `isCompactSystem_insert_univ_isCompact_isClosed`

English:
theorem isCompactSystem_insert_univ_isCompact_isClosed
  given: (α : Type*) [TopologicalSpace α]
  proof: (isCompactSystem_isCompact_isClosed α).insert_univ

中文:
定理 isCompactSystem_insert_univ_isCompact_isClosed
  条件: (α : 类型) [TopologicalSpace α]
  证明: (isCompactSystem_isCompact_isClosed α).insert_univ

Depends on / 依赖: insert_univ, isCompactSystem_isCompact_isClosed
-/
theorem isCompactSystem_insert_univ_isCompact_isClosed (α : Type*) [TopologicalSpace α] :
    IsCompactSystem (insert univ {s : Set α | IsCompact s ∧ IsClosed s}) :=
  (isCompactSystem_isCompact_isClosed α).insert_univ

end IsCompactIsClosed
