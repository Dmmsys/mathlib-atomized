/-
Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/

module

public import Mathlib.Order.Lattice.Nat
public import Mathlib.Order.PartialSups

/-!
# Accumulate

The function `accumulate` takes `s : α → Set β` with `LE α` and returns `⋃ y ≤ x, s y`.
It is related to `dissipate s := ⋂ y ≤ x, s y`.

`accumulate` is closely related to the function `partialSups`, although these two functions have
slightly different typeclass assumptions and API. `partialSups_eq_accumulate` shows
that they coincide on `ℕ`.
-/

@[expose] public section

variable {α β : Type*} {s : α -> Set β}

namespace Set

/--
Definition of `accumulate` / `accumulate` 的定义

English:
definition accumulate
  signature: [LE α] (s : α -> Set β) (x : α)
  body: ⋃ y <= x, s y

中文:
定义 accumulate
  签名: [LE α] (s : α -> Set β) (x : α)
  定义体: ⋃ y <= x, s y
-/
def accumulate [LE α] (s : α -> Set β) (x : α) : Set β :=
  ⋃ y <= x, s y

/--
theorem `accumulate_def` / 定理 `accumulate_def`

English:
theorem accumulate_def
  given: [LE α] {x : α}
  statement: accumulate s x = ⋃ y <= x, s y
  proof: rfl

中文:
定理 accumulate_def
  条件: [LE α] {x : α}
  结论: accumulate s x = ⋃ y <= x, s y
  证明: rfl
-/
theorem accumulate_def [LE α] {x : α} : accumulate s x = ⋃ y <= x, s y :=
  rfl

/--
theorem `accumulate_eq_biInter_lt` / 定理 `accumulate_eq_biInter_lt`

English:
theorem accumulate_eq_biInter_lt
  given: {s : Nat -> Set β} {n : Nat}
  statement: accumulate s n = ⋃ k < n + 1, s k
  proof: by
  simp_rw [Nat.lt_add_one_iff, accumulate]

@[simp]

中文:
定理 accumulate_eq_biInter_lt
  条件: {s : 自然数 -> Set β} {n : 自然数}
  结论: accumulate s n = ⋃ k < n + 1, s k
  证明: by
  simp_rw [Nat.lt_add_one_iff, accumulate]

@[simp]

Depends on / 依赖: Nat.lt_add_one_iff, accumulate, lt_add_one_iff, simp_rw
-/
theorem accumulate_eq_biInter_lt {s : Nat -> Set β} {n : Nat} : accumulate s n = ⋃ k < n + 1, s k := by
  simp_rw [Nat.lt_add_one_iff, accumulate]

@[simp]
/--
theorem `mem_accumulate` / 定理 `mem_accumulate`

English:
theorem mem_accumulate
  given: [LE α] {x : α} {z : β}
  statement: z in accumulate s x ↔ exists y <= x, z in s y
  proof: by
  simp_rw [accumulate_def, mem_iUnion₂, exists_prop]

中文:
定理 mem_accumulate
  条件: [LE α] {x : α} {z : β}
  结论: z in accumulate s x ↔ 存在 y <= x, z in s y
  证明: by
  simp_rw [accumulate_def, mem_iUnion₂, exists_prop]

Depends on / 依赖: accumulate_def, exists_prop, simp_rw
-/
theorem mem_accumulate [LE α] {x : α} {z : β} : z in accumulate s x ↔ exists y <= x, z in s y := by
  simp_rw [accumulate_def, mem_iUnion₂, exists_prop]

/--
theorem `subset_accumulate` / 定理 `subset_accumulate`

English:
theorem subset_accumulate
  given: [Preorder α] {x : α}
  statement: s x subseteq accumulate s x
  proof: fun _ => mem_biUnion le_rfl

中文:
定理 subset_accumulate
  条件: [Preorder α] {x : α}
  结论: s x subseteq accumulate s x
  证明: fun _ => mem_biUnion le_rfl

Depends on / 依赖: le_rfl, mem_biUnion
-/
theorem subset_accumulate [Preorder α] {x : α} : s x subseteq accumulate s x := fun _ => mem_biUnion le_rfl

/--
theorem `accumulate_subset_iUnion` / 定理 `accumulate_subset_iUnion`

English:
theorem accumulate_subset_iUnion
  given: [LE α] (x : α)
  statement: accumulate s x subseteq ⋃ i, s i
  proof: (biUnion_subset_biUnion_left (subset_univ _)).trans_eq (biUnion_univ _)

中文:
定理 accumulate_subset_iUnion
  条件: [LE α] (x : α)
  结论: accumulate s x subseteq ⋃ i, s i
  证明: (biUnion_subset_biUnion_left (subset_univ _)).trans_eq (biUnion_univ _)

Depends on / 依赖: biUnion_subset_biUnion_left, biUnion_univ, subset_univ, trans_eq
-/
theorem accumulate_subset_iUnion [LE α] (x : α) : accumulate s x subseteq ⋃ i, s i :=
  (biUnion_subset_biUnion_left (subset_univ _)).trans_eq (biUnion_univ _)

/--
theorem `monotone_accumulate` / 定理 `monotone_accumulate`

English:
theorem monotone_accumulate
  given: [Preorder α]
  statement: Monotone (accumulate s)
  proof: fun _ _ hxy =>
  biUnion_subset_biUnion_left fun _ hz => le_trans hz hxy

@[gcongr]

中文:
定理 monotone_accumulate
  条件: [Preorder α]
  结论: Monotone (accumulate s)
  证明: fun _ _ hxy =>
  biUnion_subset_biUnion_left fun _ hz => le_trans hz hxy

@[gcongr]
-/
theorem monotone_accumulate [Preorder α] : Monotone (accumulate s) := fun _ _ hxy =>
  biUnion_subset_biUnion_left fun _ hz => le_trans hz hxy

@[gcongr]
/--
theorem `accumulate_subset_accumulate` / 定理 `accumulate_subset_accumulate`

English:
theorem accumulate_subset_accumulate
  given: [Preorder α] {x y} (h : x <= y)
  proof: monotone_accumulate h

@[simp]

中文:
定理 accumulate_subset_accumulate
  条件: [Preorder α] {x y} (h : x <= y)
  证明: monotone_accumulate h

@[simp]

Depends on / 依赖: monotone_accumulate
-/
theorem accumulate_subset_accumulate [Preorder α] {x y} (h : x <= y) :
    accumulate s x subseteq accumulate s y :=
  monotone_accumulate h

@[simp]
/--
theorem `biUnion_accumulate` / 定理 `biUnion_accumulate`

English:
theorem biUnion_accumulate
  given: [Preorder α] (x : α)
  statement: ⋃ y <= x, accumulate s y = ⋃ y <= x, s y
  proof: by
  apply Subset.antisymm
  · exact iUnion₂_subset fun y hy => monotone_accumulate hy
  · exact iUnion₂_mono fun y _ => subset_accumulate

@[simp]

中文:
定理 biUnion_accumulate
  条件: [Preorder α] (x : α)
  结论: ⋃ y <= x, accumulate s y = ⋃ y <= x, s y
  证明: by
  apply Subset.antisymm
  · exact iUnion₂_subset fun y hy => monotone_accumulate hy
  · exact iUnion₂_mono fun y _ => subset_accumulate

@[simp]

Depends on / 依赖: Subset, Subset.antisymm, antisymm, monotone_accumulate, subset_accumulate
-/
theorem biUnion_accumulate [Preorder α] (x : α) : ⋃ y <= x, accumulate s y = ⋃ y <= x, s y := by
  apply Subset.antisymm
  · exact iUnion₂_subset fun y hy => monotone_accumulate hy
  · exact iUnion₂_mono fun y _ => subset_accumulate

@[simp]
/--
theorem `iUnion_accumulate` / 定理 `iUnion_accumulate`

English:
theorem iUnion_accumulate
  given: [Preorder α]
  statement: ⋃ x, accumulate s x = ⋃ x, s x
  proof: by
  apply Subset.antisymm
  · simp only [subset_def, mem_iUnion, exists_imp, mem_accumulate]
    intro z x x' ⟨_, hz⟩
    exact ⟨x', hz⟩
  · exact iUnion_mono fun i => subset_accumulate

@[simp]

中文:
定理 iUnion_accumulate
  条件: [Preorder α]
  结论: ⋃ x, accumulate s x = ⋃ x, s x
  证明: by
  apply Subset.antisymm
  · simp only [subset_def, mem_iUnion, exists_imp, mem_accumulate]
    intro z x x' ⟨_, hz⟩
    exact ⟨x', hz⟩
  · exact iUnion_mono fun i => subset_accumulate

@[simp]

Depends on / 依赖: Subset, Subset.antisymm, antisymm, exists_imp, iUnion_mono, mem_accumulate, mem_iUnion, subset_accumulate, subset_def
-/
theorem iUnion_accumulate [Preorder α] : ⋃ x, accumulate s x = ⋃ x, s x := by
  apply Subset.antisymm
  · simp only [subset_def, mem_iUnion, exists_imp, mem_accumulate]
    intro z x x' ⟨_, hz⟩
    exact ⟨x', hz⟩
  · exact iUnion_mono fun i => subset_accumulate

@[simp]
/--
lemma `accumulate_bot` / 引理 `accumulate_bot`

English:
lemma accumulate_bot
  given: [PartialOrder α] [OrderBot α] (s : α -> Set β)
  statement: accumulate s ⊥ = s ⊥
  proof: by
  simp [Set.accumulate_def]

@[simp]

中文:
引理 accumulate_bot
  条件: [PartialOrder α] [OrderBot α] (s : α -> Set β)
  结论: accumulate s ⊥ = s ⊥
  证明: by
  simp [Set.accumulate_def]

@[simp]

Depends on / 依赖: Set.accumulate_def, accumulate_def
-/
lemma accumulate_bot [PartialOrder α] [OrderBot α] (s : α -> Set β) : accumulate s ⊥ = s ⊥ := by
  simp [Set.accumulate_def]

@[simp]
/--
lemma `accumulate_zero_nat` / 引理 `accumulate_zero_nat`

English:
lemma accumulate_zero_nat
  given: (s : Nat -> Set β)
  statement: accumulate s 0 = s 0
  proof: by
  simp [accumulate_def]

中文:
引理 accumulate_zero_nat
  条件: (s : 自然数 -> Set β)
  结论: accumulate s 0 = s 0
  证明: by
  simp [accumulate_def]

Depends on / 依赖: accumulate_def
-/
lemma accumulate_zero_nat (s : Nat -> Set β) : accumulate s 0 = s 0 := by
  simp [accumulate_def]

open Function in
/--
theorem `disjoint_accumulate` / 定理 `disjoint_accumulate`

English:
theorem disjoint_accumulate
  given: [Preorder α] (hs : Pairwise (Disjoint on s)) {i j : α} (hij : i < j)
  proof: by
  apply disjoint_left.2 (fun x hx => ?_)
  simp only [accumulate, mem_iUnion, exists_prop] at hx
  rcases hx with ⟨k, hk, hx⟩
  exact disjoint_left.1 (hs (hk.trans_lt hij).ne) hx

@[simp]

中文:
定理 disjoint_accumulate
  条件: [Preorder α] (hs : Pairwise (Disjoint on s)) {i j : α} (hij : i < j)
  证明: by
  apply disjoint_left.2 (fun x hx => ?_)
  simp only [accumulate, mem_iUnion, exists_prop] at hx
  rcases hx with ⟨k, hk, hx⟩
  exact disjoint_left.1 (hs (hk.trans_lt hij).ne) hx

@[simp]

Depends on / 依赖: accumulate, disjoint_left, exists_prop, hk.trans_lt, mem_iUnion, trans_lt
-/
theorem disjoint_accumulate [Preorder α] (hs : Pairwise (Disjoint on s)) {i j : α} (hij : i < j) :
    Disjoint (accumulate s i) (s j) := by
  apply disjoint_left.2 (fun x hx => ?_)
  simp only [accumulate, mem_iUnion, exists_prop] at hx
  rcases hx with ⟨k, hk, hx⟩
  exact disjoint_left.1 (hs (hk.trans_lt hij).ne) hx

@[simp]
/--
theorem `accumulate_succ` / 定理 `accumulate_succ`

English:
theorem accumulate_succ
  given: (u : Nat -> Set α) (n : Nat)
  proof: biUnion_le_succ u n

中文:
定理 accumulate_succ
  条件: (u : 自然数 -> Set α) (n : 自然数)
  证明: biUnion_le_succ u n

Depends on / 依赖: biUnion_le_succ
-/
theorem accumulate_succ (u : Nat -> Set α) (n : Nat) :
    accumulate u (n + 1) = accumulate u n union u (n + 1) := biUnion_le_succ u n

/--
lemma `partialSups_eq_accumulate` / 引理 `partialSups_eq_accumulate`

English:
lemma partialSups_eq_accumulate
  given: (f : Nat -> Set α)
  proof: by
  ext n
  simp [partialSups_eq_sup_range, accumulate, Nat.lt_succ_iff]

中文:
引理 partialSups_eq_accumulate
  条件: (f : 自然数 -> Set α)
  证明: by
  ext n
  simp [partialSups_eq_sup_range, accumulate, Nat.lt_succ_iff]

Depends on / 依赖: Nat.lt_succ_iff, accumulate, lt_succ_iff, partialSups_eq_sup_range
-/
lemma partialSups_eq_accumulate (f : Nat -> Set α) :
    partialSups f = accumulate f := by
  ext n
  simp [partialSups_eq_sup_range, accumulate, Nat.lt_succ_iff]

/--
lemma `exists_subset_accumulate_of_directed` / 引理 `exists_subset_accumulate_of_directed`

English:
lemma exists_subset_accumulate_of_directed
  statement: {s : Nat -> Set α}
  proof: by
  induction n with
  | zero => use 0; simp [accumulate_def]
  | succ n hn =>
    obtain ⟨m, hm⟩ := hn
    obtain ⟨k, hk⟩ := hd m (n + 1)
    simp at hk
    exact ⟨k, by simp; grind⟩

中文:
引理 exists_subset_accumulate_of_directed
  结论: {s : 自然数 -> Set α}
  证明: by
  induction n with
  | zero => use 0; simp [accumulate_def]
  | succ n hn =>
    obtain ⟨m, hm⟩ := hn
    obtain ⟨k, hk⟩ := hd m (n + 1)
    simp at hk
    exact ⟨k, by simp; grind⟩

Depends on / 依赖: accumulate_def
-/
lemma exists_subset_accumulate_of_directed {s : Nat -> Set α}
  (hd : Directed (· subseteq ·) s) (n : Nat) : exists m, accumulate s n subseteq s m := by
  induction n with
  | zero => use 0; simp [accumulate_def]
  | succ n hn =>
    obtain ⟨m, hm⟩ := hn
    obtain ⟨k, hk⟩ := hd m (n + 1)
    simp at hk
    exact ⟨k, by simp; grind⟩

/--
lemma `directed_accumulate` / 引理 `directed_accumulate`

English:
lemma directed_accumulate
  given: {s : Nat -> Set α}
  statement: Directed (· subseteq ·) (accumulate s)
  proof: monotone_accumulate.directed_le

中文:
引理 directed_accumulate
  条件: {s : 自然数 -> Set α}
  结论: Directed (· subseteq ·) (accumulate s)
  证明: monotone_accumulate.directed_le

Depends on / 依赖: directed_le, monotone_accumulate, monotone_accumulate.directed_le
-/
lemma directed_accumulate {s : Nat -> Set α} : Directed (· subseteq ·) (accumulate s) :=
  monotone_accumulate.directed_le

/--
lemma `exists_accumulate_eq_univ_iff_of_directed` / 引理 `exists_accumulate_eq_univ_iff_of_directed`

English:
lemma exists_accumulate_eq_univ_iff_of_directed
  given: {s : Nat -> Set α} (hd : Directed (· subseteq ·) s)
  proof: by
  refine ⟨?_, fun ⟨n, hn⟩ => ⟨n,
    subset_antisymm (subset_univ _) (hn.symm.le.trans subset_accumulate)⟩⟩
  contrapose!
  intro h n
  obtain ⟨m, hm⟩ := exists_subset_accumulate_of_directed hd n
  grind

中文:
引理 exists_accumulate_eq_univ_iff_of_directed
  条件: {s : 自然数 -> Set α} (hd : Directed (· subseteq ·) s)
  证明: by
  refine ⟨?_, fun ⟨n, hn⟩ => ⟨n,
    subset_antisymm (subset_univ _) (hn.symm.le.trans subset_accumulate)⟩⟩
  contrapose!
  intro h n
  obtain ⟨m, hm⟩ := exists_subset_accumulate_of_directed hd n
  grind

Depends on / 依赖: contrapose, exists_subset_accumulate_of_directed, hn.symm.le.trans, subset_accumulate, subset_antisymm, subset_univ
-/
lemma exists_accumulate_eq_univ_iff_of_directed {s : Nat -> Set α} (hd : Directed (· subseteq ·) s) :
    (exists n, accumulate s n = univ) ↔ exists n, s n = univ := by
  refine ⟨?_, fun ⟨n, hn⟩ => ⟨n,
    subset_antisymm (subset_univ _) (hn.symm.le.trans subset_accumulate)⟩⟩
  contrapose!
  intro h n
  obtain ⟨m, hm⟩ := exists_subset_accumulate_of_directed hd n
  grind

end Set
