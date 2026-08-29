/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Data.Set.Finite.Lattice

/-!
# Partitions based on membership of a sequence of sets

Let `f : ℕ → Set α` be a sequence of sets. For `n : ℕ`, we can form the set of points that are in
`f 0 ∪ f 1 ∪ ... ∪ f (n-1)`; then the set of points in `(f 0)ᶜ ∪ f 1 ∪ ... ∪ f (n-1)` and so on for
all 2^n choices of a set or its complement. The at most 2^n sets we obtain form a partition
of `univ : Set α`. We call that partition `memPartition f n` (the membership partition of `f`).
For `n = 0` we set `memPartition f 0 = {univ}`.

The partition `memPartition f (n + 1)` is finer than `memPartition f n`.

## Main definitions

* `memPartition f n`: the membership partition of the first `n` sets in `f`.
* `memPartitionSet`: `memPartitionSet f n x` is the set in the partition `memPartition f n` to
  which `x` belongs.

## Main statements

* `disjoint_memPartition`: the sets in `memPartition f n` are disjoint
* `sUnion_memPartition`: the union of the sets in `memPartition f n` is `univ`
* `finite_memPartition`: `memPartition f n` is finite

-/

@[expose] public section

open Set

variable {α : Type*}

/--
Definition of `memPartition` / `memPartition` 的定义

English:
definition memPartition
  signature: (f : Nat -> Set α)

中文:
定义 memPartition
  签名: (f : 自然数 -> 集合 α)
-/
def memPartition (f : Nat -> Set α) : Nat -> Set (Set α)
  | 0 => {univ}
  | n + 1 => {s | exists u in memPartition f n, s = u inter f n ∨ s = u \ f n}

@[simp]
/--
lemma `memPartition_zero` / 引理 `memPartition_zero`

English:
lemma memPartition_zero
  given: (f : Nat -> Set α)
  statement: memPartition f 0 = {univ}
  proof: rfl

中文:
引理 memPartition_zero
  条件: (f : 自然数 -> 集合 α)
  结论: memPartition f 0 = {univ}
  证明: rfl
-/
lemma memPartition_zero (f : Nat -> Set α) : memPartition f 0 = {univ} := rfl

/--
lemma `memPartition_succ` / 引理 `memPartition_succ`

English:
lemma memPartition_succ
  given: (f : Nat -> Set α) (n : Nat)
  proof: rfl

中文:
引理 memPartition_succ
  条件: (f : 自然数 -> 集合 α) (n : 自然数)
  证明: rfl
-/
lemma memPartition_succ (f : Nat -> Set α) (n : Nat) :
    memPartition f (n + 1) = {s | exists u in memPartition f n, s = u inter f n ∨ s = u \ f n} :=
  rfl

/--
lemma `disjoint_memPartition` / 引理 `disjoint_memPartition`

English:
lemma disjoint_memPartition
  statement: (f : Nat -> Set α) (n : Nat) {u v : Set α}
  proof: by
  revert u v
  induction n with
  | zero =>
    intro u v hu hv huv
    simp only [memPartition_zero, mem_singleton_iff] at hu hv
    rw [hu]; rw [hv] at huv
    exact absurd rfl huv
  | succ n ih =>
    intro u v hu hv huv
    rw [memPartition_succ] at hu hv
    obtain ⟨u', hu', hu'_eq⟩ := hu
    obtain ⟨v', hv', hv'_eq⟩ := hv
    rcases hu'_eq with rfl | rfl <;> rcases hv'_eq with rfl | rfl
    · refine Disjoint.mono inter_subset_left inter_subset_left (ih hu' hv' ?_)
      exact fun huv' => huv (huv' ▸ rfl)
    · exact Disjoint.mono_left inter_subset_right Set.disjoint_sdiff_right
    · exact Disjoint.mono_right inter_subset_right Set.disjoint_sdiff_left
    · refine Disjoint.mono sdiff_subset sdiff_subset (ih hu' hv' ?_)
      exact fun huv' => huv (huv' ▸ rfl)

@[simp]

中文:
引理 disjoint_memPartition
  结论: (f : 自然数 -> 集合 α) (n : 自然数) {u v : 集合 α}
  证明: by
  revert u v
  induction n with
  | zero =>
    intro u v hu hv huv
    simp only [memPartition_zero, mem_singleton_iff] at hu hv
    rw [hu]; rw [hv] at huv
    exact absurd rfl huv
  | succ n ih =>
    intro u v hu hv huv
    rw [memPartition_succ] at hu hv
    obtain ⟨u', hu', hu'_eq⟩ := hu
    obtain ⟨v', hv', hv'_eq⟩ := hv
    rcases hu'_eq with rfl | rfl <;> rcases hv'_eq with rfl | rfl
    · refine Disjoint.mono inter_subset_left inter_subset_left (ih hu' hv' ?_)
      exact fun huv' => huv (huv' ▸ rfl)
    · exact Disjoint.mono_left inter_subset_right Set.disjoint_sdiff_right
    · exact Disjoint.mono_right inter_subset_right Set.disjoint_sdiff_left
    · refine Disjoint.mono sdiff_subset sdiff_subset (ih hu' hv' ?_)
      exact fun huv' => huv (huv' ▸ rfl)

@[simp]

Depends on / 依赖: Disjoint, Disjoint.mono, Disjoint.mono_left, absurd, inter_su, inter_subset_left, memPartition_succ, memPartition_zero, mem_singleton_iff, mono_left, revert
-/
lemma disjoint_memPartition (f : Nat -> Set α) (n : Nat) {u v : Set α}
    (hu : u in memPartition f n) (hv : v in memPartition f n) (huv : u != v) :
    Disjoint u v := by
  revert u v
  induction n with
  | zero =>
    intro u v hu hv huv
    simp only [memPartition_zero, mem_singleton_iff] at hu hv
    rw [hu]; rw [hv] at huv
    exact absurd rfl huv
  | succ n ih =>
    intro u v hu hv huv
    rw [memPartition_succ] at hu hv
    obtain ⟨u', hu', hu'_eq⟩ := hu
    obtain ⟨v', hv', hv'_eq⟩ := hv
    rcases hu'_eq with rfl | rfl <;> rcases hv'_eq with rfl | rfl
    · refine Disjoint.mono inter_subset_left inter_subset_left (ih hu' hv' ?_)
      exact fun huv' => huv (huv' ▸ rfl)
    · exact Disjoint.mono_left inter_subset_right Set.disjoint_sdiff_right
    · exact Disjoint.mono_right inter_subset_right Set.disjoint_sdiff_left
    · refine Disjoint.mono sdiff_subset sdiff_subset (ih hu' hv' ?_)
      exact fun huv' => huv (huv' ▸ rfl)

@[simp]
/--
lemma `sUnion_memPartition` / 引理 `sUnion_memPartition`

English:
lemma sUnion_memPartition
  given: (f : Nat -> Set α) (n : Nat)
  statement: ⋃₀ memPartition f n = univ
  proof: by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [memPartition_succ]
    ext x
    have : x in ⋃₀ memPartition f n := by simp [ih]
    simp only [mem_sUnion, mem_univ,
      iff_true] at this ⊢
    obtain ⟨t, ht, hxt⟩ := this
    by_cases hxf : x in f n
    · exact ⟨t inter f n, ⟨t, ht, Or.inl rfl⟩, hxt, hxf⟩
    · exact ⟨t \ f n, ⟨t, ht, Or.inr rfl⟩, hxt, hxf⟩

中文:
引理 sUnion_memPartition
  条件: (f : 自然数 -> 集合 α) (n : 自然数)
  结论: ⋃₀ memPartition f n = univ
  证明: by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [memPartition_succ]
    ext x
    have : x in ⋃₀ memPartition f n := by simp [ih]
    simp only [mem_sUnion, mem_univ,
      iff_true] at this ⊢
    obtain ⟨t, ht, hxt⟩ := this
    by_cases hxf : x in f n
    · exact ⟨t inter f n, ⟨t, ht, Or.inl rfl⟩, hxt, hxf⟩
    · exact ⟨t \ f n, ⟨t, ht, Or.inr rfl⟩, hxt, hxf⟩

Depends on / 依赖: Or.inl, Or.inr, iff_true, memPartition, memPartition_succ, mem_sUnion, mem_univ
-/
lemma sUnion_memPartition (f : Nat -> Set α) (n : Nat) : ⋃₀ memPartition f n = univ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [memPartition_succ]
    ext x
    have : x in ⋃₀ memPartition f n := by simp [ih]
    simp only [mem_sUnion, mem_univ,
      iff_true] at this ⊢
    obtain ⟨t, ht, hxt⟩ := this
    by_cases hxf : x in f n
    · exact ⟨t inter f n, ⟨t, ht, Or.inl rfl⟩, hxt, hxf⟩
    · exact ⟨t \ f n, ⟨t, ht, Or.inr rfl⟩, hxt, hxf⟩

/--
lemma `finite_memPartition` / 引理 `finite_memPartition`

English:
lemma finite_memPartition
  given: (f : Nat -> Set α) (n : Nat)
  statement: Set.Finite (memPartition f n)
  proof: by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [memPartition_succ]
    have : Finite (memPartition f n) := Set.finite_coe_iff.mp ih
    rw [← Set.finite_coe_iff]
    simp_rw [ofPred_exists, ← exists_prop, ofPred_exists, ofPred_or]
    refine Finite.Set.finite_biUnion (memPartition f n) _ (fun u _ => ?_)
    rw [Set.finite_coe_iff]
    simp

中文:
引理 finite_memPartition
  条件: (f : 自然数 -> 集合 α) (n : 自然数)
  结论: 集合.有限 (memPartition f n)
  证明: by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [memPartition_succ]
    have : Finite (memPartition f n) := Set.finite_coe_iff.mp ih
    rw [← Set.finite_coe_iff]
    simp_rw [ofPred_exists, ← exists_prop, ofPred_exists, ofPred_or]
    refine Finite.Set.finite_biUnion (memPartition f n) _ (fun u _ => ?_)
    rw [Set.finite_coe_iff]
    simp

Depends on / 依赖: Finite, Finite.Set.finite_biUnion, Set.finite_coe_iff, Set.finite_coe_iff.mp, exists_prop, finite_biUnion, finite_coe_iff, memPartition, memPartition_succ, ofPred_exists, ofPred_or, simp_rw
-/
lemma finite_memPartition (f : Nat -> Set α) (n : Nat) : Set.Finite (memPartition f n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [memPartition_succ]
    have : Finite (memPartition f n) := Set.finite_coe_iff.mp ih
    rw [← Set.finite_coe_iff]
    simp_rw [ofPred_exists, ← exists_prop, ofPred_exists, ofPred_or]
    refine Finite.Set.finite_biUnion (memPartition f n) _ (fun u _ => ?_)
    rw [Set.finite_coe_iff]
    simp

/--
Instance `instFinite_memPartition` / 实例 `instFinite_memPartition`

English:
instance instFinite_memPartition
  signature: (f : Nat -> Set α) (n : Nat)
  body: Set.finite_coe_iff.mp (finite_memPartition _ _)

noncomputable

中文:
实例 instFinite_memPartition
  签名: (f : 自然数 -> 集合 α) (n : 自然数)
  定义体: Set.finite_coe_iff.mp (finite_memPartition _ _)

noncomputable

Depends on / 依赖: Set.finite_coe_iff.mp, finite_coe_iff, finite_memPartition
-/
instance instFinite_memPartition (f : Nat -> Set α) (n : Nat) : Finite (memPartition f n) :=
  Set.finite_coe_iff.mp (finite_memPartition _ _)

noncomputable
/--
Instance `instFintype_memPartition` / 实例 `instFintype_memPartition`

English:
instance instFintype_memPartition
  signature: (f : Nat -> Set α) (n : Nat)
  body: (finite_memPartition f n).fintype

中文:
实例 instFintype_memPartition
  签名: (f : 自然数 -> 集合 α) (n : 自然数)
  定义体: (finite_memPartition f n).fintype

Depends on / 依赖: finite_memPartition, fintype
-/
instance instFintype_memPartition (f : Nat -> Set α) (n : Nat) : Fintype (memPartition f n) :=
  (finite_memPartition f n).fintype

open scoped Classical in
-- Note: `Set` has no computational content, but Lean still attempts to compile it.
-- See https://github.com/leanprover/lean4/issues/14084.
/--
Definition of `memPartitionSet` / `memPartitionSet` 的定义

English:
definition memPartitionSet
  signature: (f : Nat -> Set α)

中文:
定义 memPartitionSet
  签名: (f : 自然数 -> 集合 α)
-/
noncomputable def memPartitionSet (f : Nat -> Set α) : Nat -> α -> Set α
  | 0 => fun _ => univ
  | n + 1 => fun a => if a in f n then memPartitionSet f n a inter f n else memPartitionSet f n a \ f n

@[simp]
/--
lemma `memPartitionSet_zero` / 引理 `memPartitionSet_zero`

English:
lemma memPartitionSet_zero
  given: (f : Nat -> Set α) (a : α)
  statement: memPartitionSet f 0 a = univ
  proof: by
  simp [memPartitionSet]

中文:
引理 memPartitionSet_zero
  条件: (f : 自然数 -> 集合 α) (a : α)
  结论: memPartitionSet f 0 a = univ
  证明: by
  simp [memPartitionSet]

Depends on / 依赖: memPartitionSet
-/
lemma memPartitionSet_zero (f : Nat -> Set α) (a : α) : memPartitionSet f 0 a = univ := by
  simp [memPartitionSet]

/--
lemma `memPartitionSet_succ` / 引理 `memPartitionSet_succ`

English:
lemma memPartitionSet_succ
  given: (f : Nat -> Set α) (n : Nat) (a : α) [Decidable (a in f n)]
  proof: by
  simp [memPartitionSet]

中文:
引理 memPartitionSet_succ
  条件: (f : 自然数 -> 集合 α) (n : 自然数) (a : α) [可判定 (a in f n)]
  证明: by
  simp [memPartitionSet]

Depends on / 依赖: memPartitionSet
-/
lemma memPartitionSet_succ (f : Nat -> Set α) (n : Nat) (a : α) [Decidable (a in f n)] :
    memPartitionSet f (n + 1) a
      = if a in f n then memPartitionSet f n a inter f n else memPartitionSet f n a \ f n := by
  simp [memPartitionSet]

/--
lemma `memPartitionSet_mem` / 引理 `memPartitionSet_mem`

English:
lemma memPartitionSet_mem
  given: (f : Nat -> Set α) (n : Nat) (a : α)
  proof: by
  induction n with
  | zero => simp [memPartitionSet]
  | succ n ih =>
    classical
    rw [memPartitionSet_succ]; rw [memPartition_succ]
    refine ⟨memPartitionSet f n a, ?_⟩
    split_ifs <;> simp [ih]

中文:
引理 memPartitionSet_mem
  条件: (f : 自然数 -> 集合 α) (n : 自然数) (a : α)
  证明: by
  induction n with
  | zero => simp [memPartitionSet]
  | succ n ih =>
    classical
    rw [memPartitionSet_succ]; rw [memPartition_succ]
    refine ⟨memPartitionSet f n a, ?_⟩
    split_ifs <;> simp [ih]

Depends on / 依赖: classical, memPartitionSet, memPartitionSet_succ, memPartition_succ, split_ifs
-/
lemma memPartitionSet_mem (f : Nat -> Set α) (n : Nat) (a : α) :
    memPartitionSet f n a in memPartition f n := by
  induction n with
  | zero => simp [memPartitionSet]
  | succ n ih =>
    classical
    rw [memPartitionSet_succ]; rw [memPartition_succ]
    refine ⟨memPartitionSet f n a, ?_⟩
    split_ifs <;> simp [ih]

/--
lemma `mem_memPartitionSet` / 引理 `mem_memPartitionSet`

English:
lemma mem_memPartitionSet
  given: (f : Nat -> Set α) (n : Nat) (a : α)
  statement: a in memPartitionSet f n a
  proof: by
  induction n with
  | zero => simp [memPartitionSet]
  | succ n ih =>
    classical
    rw [memPartitionSet_succ]
    split_ifs with h <;> exact ⟨ih, h⟩

中文:
引理 mem_memPartitionSet
  条件: (f : 自然数 -> 集合 α) (n : 自然数) (a : α)
  结论: a in memPartitionSet f n a
  证明: by
  induction n with
  | zero => simp [memPartitionSet]
  | succ n ih =>
    classical
    rw [memPartitionSet_succ]
    split_ifs with h <;> exact ⟨ih, h⟩

Depends on / 依赖: classical, memPartitionSet, memPartitionSet_succ, split_ifs
-/
lemma mem_memPartitionSet (f : Nat -> Set α) (n : Nat) (a : α) : a in memPartitionSet f n a := by
  induction n with
  | zero => simp [memPartitionSet]
  | succ n ih =>
    classical
    rw [memPartitionSet_succ]
    split_ifs with h <;> exact ⟨ih, h⟩

/--
lemma `memPartitionSet_eq_iff` / 引理 `memPartitionSet_eq_iff`

English:
lemma memPartitionSet_eq_iff
  statement: {f : Nat -> Set α} {n : Nat} (a : α) {s : Set α}
  proof: by
  refine ⟨fun h => h ▸ mem_memPartitionSet f n a, fun h => ?_⟩
  by_contra h_ne
  have h_disj : Disjoint s (memPartitionSet f n a) :=
    disjoint_memPartition f n hs (memPartitionSet_mem f n a) (Ne.symm h_ne)
  refine absurd h_disj ?_
  rw [not_disjoint_iff_nonempty_inter]
  exact ⟨a, h, mem_memPartitionSet f n a⟩

中文:
引理 memPartitionSet_eq_iff
  结论: {f : 自然数 -> 集合 α} {n : 自然数} (a : α) {s : 集合 α}
  证明: by
  refine ⟨fun h => h ▸ mem_memPartitionSet f n a, fun h => ?_⟩
  by_contra h_ne
  have h_disj : Disjoint s (memPartitionSet f n a) :=
    disjoint_memPartition f n hs (memPartitionSet_mem f n a) (Ne.symm h_ne)
  refine absurd h_disj ?_
  rw [not_disjoint_iff_nonempty_inter]
  exact ⟨a, h, mem_memPartitionSet f n a⟩

Depends on / 依赖: Disjoint, Ne.symm, absurd, disjoint_memPartition, h_disj, h_ne, memPartitionSet, memPartitionSet_mem, mem_memPartitionSet, not_disjoint_iff_nonempty_inter
-/
lemma memPartitionSet_eq_iff {f : Nat -> Set α} {n : Nat} (a : α) {s : Set α}
    (hs : s in memPartition f n) :
    memPartitionSet f n a = s ↔ a in s := by
  refine ⟨fun h => h ▸ mem_memPartitionSet f n a, fun h => ?_⟩
  by_contra h_ne
  have h_disj : Disjoint s (memPartitionSet f n a) :=
    disjoint_memPartition f n hs (memPartitionSet_mem f n a) (Ne.symm h_ne)
  refine absurd h_disj ?_
  rw [not_disjoint_iff_nonempty_inter]
  exact ⟨a, h, mem_memPartitionSet f n a⟩

/--
lemma `memPartitionSet_of_mem` / 引理 `memPartitionSet_of_mem`

English:
lemma memPartitionSet_of_mem
  statement: {f : Nat -> Set α} {n : Nat} {a : α} {s : Set α}
  proof: (memPartitionSet_eq_iff a hs).mpr ha

中文:
引理 memPartitionSet_of_mem
  结论: {f : 自然数 -> 集合 α} {n : 自然数} {a : α} {s : 集合 α}
  证明: (memPartitionSet_eq_iff a hs).mpr ha

Depends on / 依赖: memPartitionSet_eq_iff
-/
lemma memPartitionSet_of_mem {f : Nat -> Set α} {n : Nat} {a : α} {s : Set α}
    (hs : s in memPartition f n) (ha : a in s) :
    memPartitionSet f n a = s :=
  (memPartitionSet_eq_iff a hs).mpr ha
