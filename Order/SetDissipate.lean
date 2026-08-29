/-
Copyright (c) 2026 Peter Pfaffelhuber. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Pfaffelhuber
-/

module

public import Mathlib.Order.SetAccumulate

/-!
# Dissipate

The function `dissipate` takes `s : α → Set β` with `LE α` and returns `⋂ y ≤ x, s y`.
It is related to `accumulate s := ⋃ y ≤ x, s y`.

-/

@[expose] public section

variable {α β : Type*} {s : α -> Set β}

namespace Set

/--
Definition of `dissipate` / `dissipate` 的定义

English:
definition dissipate
  signature: [LE α] (s : α -> Set β) (x : α)
  body: ⋂ y <= x, s y

中文:
定义 dissipate
  签名: [LE α] (s : α -> Set β) (x : α)
  定义体: ⋂ y <= x, s y
-/
def dissipate [LE α] (s : α -> Set β) (x : α) : Set β :=
  ⋂ y <= x, s y

/--
theorem `dissipate_def` / 定理 `dissipate_def`

English:
theorem dissipate_def
  given: [LE α] {x : α}
  statement: dissipate s x = ⋂ y <= x, s y
  proof: rfl

中文:
定理 dissipate_def
  条件: [LE α] {x : α}
  结论: dissipate s x = ⋂ y <= x, s y
  证明: rfl
-/
theorem dissipate_def [LE α] {x : α} : dissipate s x = ⋂ y <= x, s y := rfl

/--
theorem `dissipate_eq_biInter_lt` / 定理 `dissipate_eq_biInter_lt`

English:
theorem dissipate_eq_biInter_lt
  given: {s : Nat -> Set β} {n : Nat}
  statement: dissipate s n = ⋂ k < n + 1, s k
  proof: by
  simp_rw [Nat.lt_add_one_iff, dissipate]

@[simp]

中文:
定理 dissipate_eq_biInter_lt
  条件: {s : 自然数 -> Set β} {n : 自然数}
  结论: dissipate s n = ⋂ k < n + 1, s k
  证明: by
  simp_rw [Nat.lt_add_one_iff, dissipate]

@[simp]

Depends on / 依赖: Nat.lt_add_one_iff, dissipate, lt_add_one_iff, simp_rw
-/
theorem dissipate_eq_biInter_lt {s : Nat -> Set β} {n : Nat} : dissipate s n = ⋂ k < n + 1, s k := by
  simp_rw [Nat.lt_add_one_iff, dissipate]

@[simp]
/--
theorem `mem_dissipate` / 定理 `mem_dissipate`

English:
theorem mem_dissipate
  given: [LE α] {x : α} {z : β}
  statement: z in dissipate s x ↔ forall y <= x, z in s y
  proof: by
  simp [dissipate_def]

中文:
定理 mem_dissipate
  条件: [LE α] {x : α} {z : β}
  结论: z in dissipate s x ↔ 对任意 y <= x, z in s y
  证明: by
  simp [dissipate_def]

Depends on / 依赖: dissipate_def
-/
theorem mem_dissipate [LE α] {x : α} {z : β} : z in dissipate s x ↔ forall y <= x, z in s y := by
  simp [dissipate_def]

/--
theorem `dissipate_subset` / 定理 `dissipate_subset`

English:
theorem dissipate_subset
  given: [LE α] {x y : α} (hy : y <= x)
  statement: dissipate s x subseteq s y
  proof: biInter_subset_of_mem hy

中文:
定理 dissipate_subset
  条件: [LE α] {x y : α} (hy : y <= x)
  结论: dissipate s x subseteq s y
  证明: biInter_subset_of_mem hy

Depends on / 依赖: biInter_subset_of_mem
-/
theorem dissipate_subset [LE α] {x y : α} (hy : y <= x) : dissipate s x subseteq s y :=
  biInter_subset_of_mem hy

/--
theorem `iInter_subset_dissipate` / 定理 `iInter_subset_dissipate`

English:
theorem iInter_subset_dissipate
  given: [LE α] (x : α)
  statement: ⋂ i, s i subseteq dissipate s x
  proof: by
  simp only [dissipate, subset_iInter_iff]
  exact fun x h => iInter_subset_of_subset x fun ⦃a⦄ a => a

中文:
定理 iInter_subset_dissipate
  条件: [LE α] (x : α)
  结论: ⋂ i, s i subseteq dissipate s x
  证明: by
  simp only [dissipate, subset_iInter_iff]
  exact fun x h => iInter_subset_of_subset x fun ⦃a⦄ a => a

Depends on / 依赖: dissipate, iInter_subset_of_subset, subset_iInter_iff
-/
theorem iInter_subset_dissipate [LE α] (x : α) : ⋂ i, s i subseteq dissipate s x := by
  simp only [dissipate, subset_iInter_iff]
  exact fun x h => iInter_subset_of_subset x fun ⦃a⦄ a => a

/--
theorem `antitone_dissipate` / 定理 `antitone_dissipate`

English:
theorem antitone_dissipate
  given: [Preorder α]
  statement: Antitone (dissipate s)
  proof: fun _ _ hab => biInter_subset_biInter_left fun _ hz => le_trans hz hab

@[gcongr]

中文:
定理 antitone_dissipate
  条件: [Preorder α]
  结论: Antitone (dissipate s)
  证明: fun _ _ hab => biInter_subset_biInter_left fun _ hz => le_trans hz hab

@[gcongr]

Depends on / 依赖: biInter_subset_biInter_left, le_trans
-/
theorem antitone_dissipate [Preorder α] : Antitone (dissipate s) :=
  fun _ _ hab => biInter_subset_biInter_left fun _ hz => le_trans hz hab

@[gcongr]
/--
theorem `dissipate_subset_dissipate` / 定理 `dissipate_subset_dissipate`

English:
theorem dissipate_subset_dissipate
  given: [Preorder α] {x y} (h : y <= x)
  proof: antitone_dissipate h

@[simp]

中文:
定理 dissipate_subset_dissipate
  条件: [Preorder α] {x y} (h : y <= x)
  证明: antitone_dissipate h

@[simp]

Depends on / 依赖: antitone_dissipate
-/
theorem dissipate_subset_dissipate [Preorder α] {x y} (h : y <= x) :
    dissipate s x subseteq dissipate s y :=
  antitone_dissipate h

@[simp]
/--
theorem `biInter_dissipate` / 定理 `biInter_dissipate`

English:
theorem biInter_dissipate
  given: [Preorder α] {s : α -> Set β} {x : α}
  proof: by
  apply Subset.antisymm
  · apply iInter_mono fun z y hy => ?_
    simp only [mem_iInter, mem_dissipate] at *
    exact fun h => hy h z le_rfl
  · simp only [subset_iInter_iff]
    exact fun i j => dissipate_subset_dissipate j

@[simp]

中文:
定理 biInter_dissipate
  条件: [Preorder α] {s : α -> Set β} {x : α}
  证明: by
  apply Subset.antisymm
  · apply iInter_mono fun z y hy => ?_
    simp only [mem_iInter, mem_dissipate] at *
    exact fun h => hy h z le_rfl
  · simp only [subset_iInter_iff]
    exact fun i j => dissipate_subset_dissipate j

@[simp]

Depends on / 依赖: Subset, Subset.antisymm, antisymm, dissipate_subset_dissipate, iInter_mono, le_rfl, mem_dissipate, mem_iInter, subset_iInter_iff
-/
theorem biInter_dissipate [Preorder α] {s : α -> Set β} {x : α} :
    ⋂ y, ⋂ (_ : y <= x), dissipate s y = dissipate s x := by
  apply Subset.antisymm
  · apply iInter_mono fun z y hy => ?_
    simp only [mem_iInter, mem_dissipate] at *
    exact fun h => hy h z le_rfl
  · simp only [subset_iInter_iff]
    exact fun i j => dissipate_subset_dissipate j

@[simp]
/--
theorem `iInter_dissipate` / 定理 `iInter_dissipate`

English:
theorem iInter_dissipate
  given: [Preorder α]
  statement: ⋂ x, dissipate s x = ⋂ x, s x
  proof: by
  apply Subset.antisymm <;> simp_rw [subset_def, dissipate_def, mem_iInter]
  · exact fun z h x' => h x' x' le_rfl
  · exact fun z h x' y hy => h y

@[simp]

中文:
定理 iInter_dissipate
  条件: [Preorder α]
  结论: ⋂ x, dissipate s x = ⋂ x, s x
  证明: by
  apply Subset.antisymm <;> simp_rw [subset_def, dissipate_def, mem_iInter]
  · exact fun z h x' => h x' x' le_rfl
  · exact fun z h x' y hy => h y

@[simp]

Depends on / 依赖: Subset, Subset.antisymm, antisymm, dissipate_def, le_rfl, mem_iInter, simp_rw, subset_def
-/
theorem iInter_dissipate [Preorder α] : ⋂ x, dissipate s x = ⋂ x, s x := by
  apply Subset.antisymm <;> simp_rw [subset_def, dissipate_def, mem_iInter]
  · exact fun z h x' => h x' x' le_rfl
  · exact fun z h x' y hy => h y

@[simp]
/--
lemma `dissipate_bot` / 引理 `dissipate_bot`

English:
lemma dissipate_bot
  given: [PartialOrder α] [OrderBot α] (s : α -> Set β)
  statement: dissipate s ⊥ = s ⊥
  proof: by
  simp [dissipate_def]

@[simp]

中文:
引理 dissipate_bot
  条件: [PartialOrder α] [OrderBot α] (s : α -> Set β)
  结论: dissipate s ⊥ = s ⊥
  证明: by
  simp [dissipate_def]

@[simp]

Depends on / 依赖: dissipate_def
-/
lemma dissipate_bot [PartialOrder α] [OrderBot α] (s : α -> Set β) : dissipate s ⊥ = s ⊥ := by
  simp [dissipate_def]

@[simp]
/--
lemma `dissipate_zero_nat` / 引理 `dissipate_zero_nat`

English:
lemma dissipate_zero_nat
  given: (s : Nat -> Set β)
  statement: dissipate s 0 = s 0
  proof: by
  simp [dissipate_def]

@[simp]

中文:
引理 dissipate_zero_nat
  条件: (s : 自然数 -> Set β)
  结论: dissipate s 0 = s 0
  证明: by
  simp [dissipate_def]

@[simp]

Depends on / 依赖: dissipate_def
-/
lemma dissipate_zero_nat (s : Nat -> Set β) : dissipate s 0 = s 0 := by
  simp [dissipate_def]

@[simp]
/--
theorem `dissipate_succ` / 定理 `dissipate_succ`

English:
theorem dissipate_succ
  given: (s : Nat -> Set α) (n : Nat)
  proof: by
  ext x
  simp_all only [dissipate_def, mem_iInter, mem_inter_iff]
  grind

中文:
定理 dissipate_succ
  条件: (s : 自然数 -> Set α) (n : 自然数)
  证明: by
  ext x
  simp_all only [dissipate_def, mem_iInter, mem_inter_iff]
  grind

Depends on / 依赖: dissipate_def, mem_iInter, mem_inter_iff
-/
theorem dissipate_succ (s : Nat -> Set α) (n : Nat) :
  dissipate s (n + 1) = (dissipate s n) inter s (n + 1) := by
  ext x
  simp_all only [dissipate_def, mem_iInter, mem_inter_iff]
  grind

/--
lemma `exists_subset_dissipate_of_directed` / 引理 `exists_subset_dissipate_of_directed`

English:
lemma exists_subset_dissipate_of_directed
  statement: {s : Nat -> Set α}
  proof: by
  induction n with
  | zero => use 0; simp [dissipate_def]
  | succ n hn =>
    obtain ⟨m, hm⟩ := hn
    obtain ⟨k, hk⟩ := hd m (n + 1)
    exact ⟨k, by simp; grind⟩

中文:
引理 exists_subset_dissipate_of_directed
  结论: {s : 自然数 -> Set α}
  证明: by
  induction n with
  | zero => use 0; simp [dissipate_def]
  | succ n hn =>
    obtain ⟨m, hm⟩ := hn
    obtain ⟨k, hk⟩ := hd m (n + 1)
    exact ⟨k, by simp; grind⟩

Depends on / 依赖: dissipate_def
-/
lemma exists_subset_dissipate_of_directed {s : Nat -> Set α}
  (hd : Directed (· ⊇ ·) s) (n : Nat) : exists m, s m subseteq dissipate s n := by
  induction n with
  | zero => use 0; simp [dissipate_def]
  | succ n hn =>
    obtain ⟨m, hm⟩ := hn
    obtain ⟨k, hk⟩ := hd m (n + 1)
    exact ⟨k, by simp; grind⟩

/--
lemma `directed_dissipate` / 引理 `directed_dissipate`

English:
lemma directed_dissipate
  given: {s : Nat -> Set α}
  statement: Directed (· ⊇ ·) (dissipate s)
  proof: antitone_dissipate.directed_ge

中文:
引理 directed_dissipate
  条件: {s : 自然数 -> Set α}
  结论: Directed (· ⊇ ·) (dissipate s)
  证明: antitone_dissipate.directed_ge

Depends on / 依赖: antitone_dissipate, antitone_dissipate.directed_ge, directed_ge
-/
lemma directed_dissipate {s : Nat -> Set α} : Directed (· ⊇ ·) (dissipate s) :=
  antitone_dissipate.directed_ge

/--
lemma `exists_dissipate_eq_empty_iff_of_directed` / 引理 `exists_dissipate_eq_empty_iff_of_directed`

English:
lemma exists_dissipate_eq_empty_iff_of_directed
  given: {s : Nat -> Set α} (hd : Directed (· ⊇ ·) s)
  proof: by
  refine ⟨?_, fun ⟨n, hn⟩ => ⟨n, subset_eq_empty (dissipate_subset le_rfl) hn⟩⟩
  contrapose!
  intro h n
  obtain ⟨m, hm⟩ := exists_subset_dissipate_of_directed hd n
  exact (h m).mono hm

中文:
引理 exists_dissipate_eq_empty_iff_of_directed
  条件: {s : 自然数 -> Set α} (hd : Directed (· ⊇ ·) s)
  证明: by
  refine ⟨?_, fun ⟨n, hn⟩ => ⟨n, subset_eq_empty (dissipate_subset le_rfl) hn⟩⟩
  contrapose!
  intro h n
  obtain ⟨m, hm⟩ := exists_subset_dissipate_of_directed hd n
  exact (h m).mono hm

Depends on / 依赖: contrapose, dissipate_subset, exists_subset_dissipate_of_directed, le_rfl, subset_eq_empty
-/
lemma exists_dissipate_eq_empty_iff_of_directed {s : Nat -> Set α} (hd : Directed (· ⊇ ·) s) :
    (exists n, dissipate s n = ∅) ↔ exists n, s n = ∅ := by
  refine ⟨?_, fun ⟨n, hn⟩ => ⟨n, subset_eq_empty (dissipate_subset le_rfl) hn⟩⟩
  contrapose!
  intro h n
  obtain ⟨m, hm⟩ := exists_subset_dissipate_of_directed hd n
  exact (h m).mono hm

end Set
