/-
Copyright (c) 2021 Alena Gusakov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alena Gusakov, Jeremy Tan
-/
module

public import Mathlib.Combinatorics.Enumerative.DoubleCounting
public import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
public import Mathlib.Combinatorics.SimpleGraph.Diam

/-!
# Strongly regular graphs

## Main definitions

* `G.IsSRGWith n k ℓ μ` (see `SimpleGraph.IsSRGWith`) is a structure for
  a `SimpleGraph` satisfying the following conditions:
  * The cardinality of the vertex set is `n`
  * `G` is a regular graph with degree `k`
  * The number of common neighbors between any two adjacent vertices in `G` is `ℓ`
  * The number of common neighbors between any two nonadjacent vertices in `G` is `μ`

## Main theorems

* `IsSRGWith.compl`: the complement of a strongly regular graph is strongly regular.
* `IsSRGWith.param_eq`: `k * (k - ℓ - 1) = (n - k - 1) * μ` when `0 < n`.
* `IsSRGWith.matrix_eq`: let `A` and `C` be `G`'s and `Gᶜ`'s adjacency matrices respectively and
  `I` be the identity matrix, then `A ^ 2 = k • I + ℓ • A + μ • C`.
-/

public section


open Finset

universe u

namespace SimpleGraph

variable {V : Type u} [Fintype V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/--
Definition of `IsSRGWith` / `IsSRGWith` 的定义

English:
structure IsSRGWith
  parameters: (n k ℓ μ : Nat)
  axioms and operations (4):
    - card : Fintype.card V = n
    - regular : G.IsRegularOfDegree k
    - of_adj : forall v w, G.Adj v w -> Fintype.card (G.commonNeighbors v w) = ℓ
    - of_not_adj : Pairwise fun v w => ¬G.Adj v w -> Fintype.card (G.commonNeighbors v w) = μ

中文:
结构 是SRGWith
  参数: (n k ℓ μ : 自然数)
  公理与运算 (4 个):
    - card : 有限类型.card V = n
    - regular : G.IsRegularOfDegree k
    - of_adj : 对任意 v w, G.伴随 v w -> 有限类型.card (G.commonNeighbors v w) = ℓ
    - of_not_adj : 两两 fun v w => ¬G.伴随 v w -> 有限类型.card (G.commonNeighbors v w) = μ
-/
structure IsSRGWith (n k ℓ μ : Nat) : Prop where
  card : Fintype.card V = n
  regular : G.IsRegularOfDegree k
  of_adj : forall v w, G.Adj v w -> Fintype.card (G.commonNeighbors v w) = ℓ
  of_not_adj : Pairwise fun v w => ¬G.Adj v w -> Fintype.card (G.commonNeighbors v w) = μ

variable {G} {n k ℓ μ : Nat}

/--
theorem `bot_strongly_regular` / 定理 `bot_strongly_regular`

English:
theorem bot_strongly_regular
  statement: (⊥ : SimpleGraph V).IsSRGWith (Fintype.card V) 0 ℓ 0 where
  proof: rfl
  regular := .bot
  of_adj _ _ h := h.elim
  of_not_adj v w _ := by
    simp only [card_eq_zero, Fintype.card_ofFinset, forall_true_left, not_false_iff, bot_adj]
    ext
    simp

中文:
定理 bot_strongly_regular
  结论: (⊥ : 简单图 V).是SRGWith (有限类型.card V) 0 ℓ 0 where
  证明: rfl
  regular := .bot
  of_adj _ _ h := h.elim
  of_not_adj v w _ := by
    simp only [card_eq_zero, Fintype.card_ofFinset, forall_true_left, not_false_iff, bot_adj]
    ext
    simp
-/
theorem bot_strongly_regular : (⊥ : SimpleGraph V).IsSRGWith (Fintype.card V) 0 ℓ 0 where
  card := rfl
  regular := .bot
  of_adj _ _ h := h.elim
  of_not_adj v w _ := by
    simp only [card_eq_zero, Fintype.card_ofFinset, forall_true_left, not_false_iff, bot_adj]
    ext
    simp

/--
theorem `IsSRGWith.ediam_eq_two` / 定理 `IsSRGWith.ediam_eq_two`

English:
theorem IsSRGWith.ediam_eq_two
  given: [Nontrivial V] (h : G.IsSRGWith n k ℓ μ) (ht : G != ⊤) (hm : μ != 0)
  proof: by
  apply le_antisymm
  · rw [ediam_le_iff]
    intro u v
    by_contra! hc
    obtain ⟨hn, ha, he⟩ := two_lt_edist_iff.mp hc
    have h := h.of_not_adj hn ha
    simp_all
  · by_contra
    have := not_subsingleton V
    simp_all [Order.le_one_iff]

中文:
定理 是SRGWith.ediam_eq_two
  条件: [非平凡 V] (h : G.是SRGWith n k ℓ μ) (ht : G != ⊤) (hm : μ != 0)
  证明: by
  apply le_antisymm
  · rw [ediam_le_iff]
    intro u v
    by_contra! hc
    obtain ⟨hn, ha, he⟩ := two_lt_edist_iff.mp hc
    have h := h.of_not_adj hn ha
    simp_all
  · by_contra
    have := not_subsingleton V
    simp_all [Order.le_one_iff]

Depends on / 依赖: Order.le_one_iff, ediam_le_iff, h.of_not_adj, le_antisymm, le_one_iff, not_subsingleton, of_not_adj, two_lt_edist_iff, two_lt_edist_iff.mp
-/
theorem IsSRGWith.ediam_eq_two [Nontrivial V] (h : G.IsSRGWith n k ℓ μ) (ht : G != ⊤) (hm : μ != 0) :
    G.ediam = 2 := by
  apply le_antisymm
  · rw [ediam_le_iff]
    intro u v
    by_contra! hc
    obtain ⟨hn, ha, he⟩ := two_lt_edist_iff.mp hc
    have h := h.of_not_adj hn ha
    simp_all
  · by_contra
    have := not_subsingleton V
    simp_all [Order.le_one_iff]

/-- **Conway's 99-graph problem** (from https://oeis.org/A248380/a248380.pdf)
can be reformulated as the existence of a strongly regular graph with params (99, 14, 1, 2).
This is an open problem, and has no known proof of existence. -/
proof_wanted conway_99 : exists (α : Type) (_ : Fintype α) (g : SimpleGraph α) (_ : DecidableRel g.Adj),
    IsSRGWith g 99 14 1 2

variable [DecidableEq V]

/--
theorem `IsSRGWith.top` / 定理 `IsSRGWith.top`

English:
theorem IsSRGWith.top
  proof: rfl
  regular := IsRegularOfDegree.top
  of_adj _ _ := card_commonNeighbors_top
  of_not_adj v w h h' := (h' ((top_adj v w).2 h)).elim

中文:
定理 是SRGWith.top
  证明: rfl
  regular := IsRegularOfDegree.top
  of_adj _ _ := card_commonNeighbors_top
  of_not_adj v w h h' := (h' ((top_adj v w).2 h)).elim
-/
theorem IsSRGWith.top :
    (⊤ : SimpleGraph V).IsSRGWith (Fintype.card V) (Fintype.card V - 1) (Fintype.card V - 2) μ where
  card := rfl
  regular := IsRegularOfDegree.top
  of_adj _ _ := card_commonNeighbors_top
  of_not_adj v w h h' := (h' ((top_adj v w).2 h)).elim

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `IsSRGWith.card_neighborFinset_union_eq` / 定理 `IsSRGWith.card_neighborFinset_union_eq`

English:
theorem IsSRGWith.card_neighborFinset_union_eq
  given: {v w : V} (h : G.IsSRGWith n k ℓ μ)
  proof: by
  apply Nat.add_right_cancel (m := Fintype.card (G.commonNeighbors v w))
  rw [Nat.sub_add_cancel]; rw [← Set.toFinset_card]
  · simp [commonNeighbors, ← neighborFinset_def, Finset.card_union_add_card_inter,
      h.regular.degree_eq, two_mul]
  · apply le_trans (card_commonNeighbors_le_degree_le

中文:
定理 是SRGWith.card_neighborFinset_union_eq
  条件: {v w : V} (h : G.是SRGWith n k ℓ μ)
  证明: by
  apply Nat.add_right_cancel (m := Fintype.card (G.commonNeighbors v w))
  rw [Nat.sub_add_cancel]; rw [← Set.toFinset_card]
  · simp [commonNeighbors, ← neighborFinset_def, Finset.card_union_add_card_inter,
      h.regular.degree_eq, two_mul]
  · apply le_trans (card_commonNeighbors_le_degree_le

Depends on / 依赖: Finset, Finset.card_union_add_card_inter, Fintype, Fintype.card, G.commonNeighbors, Nat.add_right_cancel, Nat.sub_add_cancel, Set.toFinset_card, add_right_cancel, card_commonNeighbors_le_degree_left, card_union_add_card_inter, commonNeighbors, degree_eq, h.regular.degree_eq, le_trans, neighborFinset_def, regular, sub_add_cancel, toFinset_card, two_mul
-/
theorem IsSRGWith.card_neighborFinset_union_eq {v w : V} (h : G.IsSRGWith n k ℓ μ) :
    #(G.neighborFinset v union G.neighborFinset w) =
      2 * k - Fintype.card (G.commonNeighbors v w) := by
  apply Nat.add_right_cancel (m := Fintype.card (G.commonNeighbors v w))
  rw [Nat.sub_add_cancel]; rw [← Set.toFinset_card]
  · simp [commonNeighbors, ← neighborFinset_def, Finset.card_union_add_card_inter,
      h.regular.degree_eq, two_mul]
  · apply le_trans (card_commonNeighbors_le_degree_left _ _ _)
    simp [h.regular.degree_eq, two_mul]

/--
theorem `IsSRGWith.card_neighborFinset_union_of_not_adj` / 定理 `IsSRGWith.card_neighborFinset_union_of_not_adj`

English:
theorem IsSRGWith.card_neighborFinset_union_of_not_adj
  statement: {v w : V} (h : G.IsSRGWith n k ℓ μ)
  proof: by
  rw [← h.of_not_adj hne ha]
  exact h.card_neighborFinset_union_eq

中文:
定理 是SRGWith.card_neighborFinset_union_of_not_adj
  结论: {v w : V} (h : G.是SRGWith n k ℓ μ)
  证明: by
  rw [← h.of_not_adj hne ha]
  exact h.card_neighborFinset_union_eq

Depends on / 依赖: card_neighborFinset_union_eq, h.card_neighborFinset_union_eq, h.of_not_adj, of_not_adj
-/
theorem IsSRGWith.card_neighborFinset_union_of_not_adj {v w : V} (h : G.IsSRGWith n k ℓ μ)
    (hne : v != w) (ha : ¬G.Adj v w) :
    #(G.neighborFinset v union G.neighborFinset w) = 2 * k - μ := by
  rw [← h.of_not_adj hne ha]
  exact h.card_neighborFinset_union_eq

/--
theorem `IsSRGWith.card_neighborFinset_union_of_adj` / 定理 `IsSRGWith.card_neighborFinset_union_of_adj`

English:
theorem IsSRGWith.card_neighborFinset_union_of_adj
  statement: {v w : V} (h : G.IsSRGWith n k ℓ μ)
  proof: by
  rw [← h.of_adj v w ha]
  exact h.card_neighborFinset_union_eq

中文:
定理 是SRGWith.card_neighborFinset_union_of_adj
  结论: {v w : V} (h : G.是SRGWith n k ℓ μ)
  证明: by
  rw [← h.of_adj v w ha]
  exact h.card_neighborFinset_union_eq

Depends on / 依赖: card_neighborFinset_union_eq, h.card_neighborFinset_union_eq, h.of_adj, of_adj
-/
theorem IsSRGWith.card_neighborFinset_union_of_adj {v w : V} (h : G.IsSRGWith n k ℓ μ)
    (ha : G.Adj v w) : #(G.neighborFinset v union G.neighborFinset w) = 2 * k - ℓ := by
  rw [← h.of_adj v w ha]
  exact h.card_neighborFinset_union_eq

/--
theorem `compl_neighborFinset_sdiff_inter_eq` / 定理 `compl_neighborFinset_sdiff_inter_eq`

English:
theorem compl_neighborFinset_sdiff_inter_eq
  given: {v w : V}
  proof: by
  grind

中文:
定理 compl_neighborFinset_sdiff_inter_eq
  条件: {v w : V}
  证明: by
  grind
-/
theorem compl_neighborFinset_sdiff_inter_eq {v w : V} :
    (G.neighborFinset v)ᶜ \ {v} inter ((G.neighborFinset w)ᶜ \ {w}) =
      ((G.neighborFinset v)ᶜ inter (G.neighborFinset w)ᶜ) \ ({w} union {v}) := by
  grind

/--
theorem `sdiff_compl_neighborFinset_inter_eq` / 定理 `sdiff_compl_neighborFinset_inter_eq`

English:
theorem sdiff_compl_neighborFinset_inter_eq
  given: {v w : V} (h : G.Adj v w)
  proof: by
  simpa using ⟨h, adj_symm _ h⟩

中文:
定理 sdiff_compl_neighborFinset_inter_eq
  条件: {v w : V} (h : G.伴随 v w)
  证明: by
  simpa using ⟨h, adj_symm _ h⟩

Depends on / 依赖: adj_symm
-/
theorem sdiff_compl_neighborFinset_inter_eq {v w : V} (h : G.Adj v w) :
    ((G.neighborFinset v)ᶜ inter (G.neighborFinset w)ᶜ) \ ({w} union {v}) =
      (G.neighborFinset v)ᶜ inter (G.neighborFinset w)ᶜ := by
  simpa using ⟨h, adj_symm _ h⟩

/--
theorem `IsSRGWith.compl_is_regular` / 定理 `IsSRGWith.compl_is_regular`

English:
theorem IsSRGWith.compl_is_regular
  given: (h : G.IsSRGWith n k ℓ μ)
  proof: by
  rw [← h.card]; rw [Nat.sub_sub]; rw [add_comm]; rw [← Nat.sub_sub]
  exact h.regular.compl

中文:
定理 是SRGWith.compl_is_regular
  条件: (h : G.是SRGWith n k ℓ μ)
  证明: by
  rw [← h.card]; rw [Nat.sub_sub]; rw [add_comm]; rw [← Nat.sub_sub]
  exact h.regular.compl

Depends on / 依赖: Nat.sub_sub, add_comm, h.card, h.regular.compl, regular, sub_sub
-/
theorem IsSRGWith.compl_is_regular (h : G.IsSRGWith n k ℓ μ) :
    Gᶜ.IsRegularOfDegree (n - k - 1) := by
  rw [← h.card]; rw [Nat.sub_sub]; rw [add_comm]; rw [← Nat.sub_sub]
  exact h.regular.compl

/--
theorem `IsSRGWith.card_commonNeighbors_eq_of_adj_compl` / 定理 `IsSRGWith.card_commonNeighbors_eq_of_adj_compl`

English:
theorem IsSRGWith.card_commonNeighbors_eq_of_adj_compl
  statement: (h : G.IsSRGWith n k ℓ μ) {v w : V}
  proof: by
  simp only [← Set.toFinset_card, commonNeighbors, Set.toFinset_inter, neighborSet_compl,
    Set.toFinset_sdiff, Set.toFinset_singleton, Set.toFinset_compl, ← neighborFinset_def]
  simp_rw [compl_neighborFinset_sdiff_inter_eq]
  have hne : v != w := ne_of_adj _ ha
  rw [compl_adj] at ha
  rw [ca

中文:
定理 是SRGWith.card_commonNeighbors_eq_of_adj_compl
  结论: (h : G.是SRGWith n k ℓ μ) {v w : V}
  证明: by
  simp only [← Set.toFinset_card, commonNeighbors, Set.toFinset_inter, neighborSet_compl,
    Set.toFinset_sdiff, Set.toFinset_singleton, Set.toFinset_compl, ← neighborFinset_def]
  simp_rw [compl_neighborFinset_sdiff_inter_eq]
  have hne : v != w := ne_of_adj _ ha
  rw [compl_adj] at ha
  rw [ca

Depends on / 依赖: Finset, Finset.compl_union, Set.toFinset_card, Set.toFinset_compl, Set.toFinset_inter, Set.toFinset_sdiff, Set.toFinset_singleton, card_compl, card_insert_of_notMem, card_neighborFinset_union_of_not_adj, card_sdiff_of_subset, card_singleton, commonNeighbors, compl_adj, compl_neighborFinset_sdiff_inter_eq, compl_union, h.card, h.card_neighborFinset_union_of_not_adj, hne.symm, insert_eq
-/
theorem IsSRGWith.card_commonNeighbors_eq_of_adj_compl (h : G.IsSRGWith n k ℓ μ) {v w : V}
    (ha : Gᶜ.Adj v w) : Fintype.card (Gᶜ.commonNeighbors v w) = n - (2 * k - μ) - 2 := by
  simp only [← Set.toFinset_card, commonNeighbors, Set.toFinset_inter, neighborSet_compl,
    Set.toFinset_sdiff, Set.toFinset_singleton, Set.toFinset_compl, ← neighborFinset_def]
  simp_rw [compl_neighborFinset_sdiff_inter_eq]
  have hne : v != w := ne_of_adj _ ha
  rw [compl_adj] at ha
  rw [card_sdiff_of_subset]; rw [← insert_eq]; rw [card_insert_of_notMem]; rw [card_singleton]; rw [← Finset.compl_union]
  · rw [card_compl, h.card_neighborFinset_union_of_not_adj hne ha.2, ← h.card]
  · simp only [hne.symm, not_false_iff, mem_singleton]
  · intro u
    simp only [mem_union, mem_compl, mem_neighborFinset, mem_inter, mem_singleton]
    rintro (rfl | rfl) <;> simpa [adj_comm] using ha.2

/--
theorem `IsSRGWith.card_commonNeighbors_eq_of_not_adj_compl` / 定理 `IsSRGWith.card_commonNeighbors_eq_of_not_adj_compl`

English:
theorem IsSRGWith.card_commonNeighbors_eq_of_not_adj_compl
  statement: (h : G.IsSRGWith n k ℓ μ) {v w : V}
  proof: by
  simp only [← Set.toFinset_card, commonNeighbors, Set.toFinset_inter, neighborSet_compl,
    Set.toFinset_sdiff, Set.toFinset_singleton, Set.toFinset_compl, ← neighborFinset_def]
  simp only [not_and, Classical.not_not, compl_adj] at hna
  have h2' := hna hn
  simp_rw [compl_neighborFinset_sdiff

中文:
定理 是SRGWith.card_commonNeighbors_eq_of_not_adj_compl
  结论: (h : G.是SRGWith n k ℓ μ) {v w : V}
  证明: by
  simp only [← Set.toFinset_card, commonNeighbors, Set.toFinset_inter, neighborSet_compl,
    Set.toFinset_sdiff, Set.toFinset_singleton, Set.toFinset_compl, ← neighborFinset_def]
  simp only [not_and, Classical.not_not, compl_adj] at hna
  have h2' := hna hn
  simp_rw [compl_neighborFinset_sdiff

Depends on / 依赖: Classical, Classical.not_not, Finset, Finset.compl_union, Set.toFinset_card, Set.toFinset_compl, Set.toFinset_inter, Set.toFinset_sdiff, Set.toFinset_singleton, card_compl, card_neighborFinset_union_of_adj, commonNeighbors, compl_adj, compl_neighborFinset_sdiff_inter_eq, compl_union, h.card, h.card_neighborFinset_union_of_adj, neighborFinset_def, neighborSet_compl, not_and
-/
theorem IsSRGWith.card_commonNeighbors_eq_of_not_adj_compl (h : G.IsSRGWith n k ℓ μ) {v w : V}
    (hn : v != w) (hna : ¬Gᶜ.Adj v w) :
    Fintype.card (Gᶜ.commonNeighbors v w) = n - (2 * k - ℓ) := by
  simp only [← Set.toFinset_card, commonNeighbors, Set.toFinset_inter, neighborSet_compl,
    Set.toFinset_sdiff, Set.toFinset_singleton, Set.toFinset_compl, ← neighborFinset_def]
  simp only [not_and, Classical.not_not, compl_adj] at hna
  have h2' := hna hn
  simp_rw [compl_neighborFinset_sdiff_inter_eq, sdiff_compl_neighborFinset_inter_eq h2']
  rwa [← Finset.compl_union, card_compl, h.card_neighborFinset_union_of_adj, ← h.card]

/--
theorem `IsSRGWith.compl` / 定理 `IsSRGWith.compl`

English:
theorem IsSRGWith.compl
  given: (h : G.IsSRGWith n k ℓ μ)
  proof: h.card
  regular := h.compl_is_regular
  of_adj _ _ := h.card_commonNeighbors_eq_of_adj_compl
  of_not_adj _ _ := h.card_commonNeighbors_eq_of_not_adj_compl

中文:
定理 是SRGWith.compl
  条件: (h : G.是SRGWith n k ℓ μ)
  证明: h.card
  regular := h.compl_is_regular
  of_adj _ _ := h.card_commonNeighbors_eq_of_adj_compl
  of_not_adj _ _ := h.card_commonNeighbors_eq_of_not_adj_compl

Depends on / 依赖: h.card
-/
theorem IsSRGWith.compl (h : G.IsSRGWith n k ℓ μ) :
    Gᶜ.IsSRGWith n (n - k - 1) (n - (2 * k - μ) - 2) (n - (2 * k - ℓ)) where
  card := h.card
  regular := h.compl_is_regular
  of_adj _ _ := h.card_commonNeighbors_eq_of_adj_compl
  of_not_adj _ _ := h.card_commonNeighbors_eq_of_not_adj_compl

/--
theorem `IsSRGWith.param_eq` / 定理 `IsSRGWith.param_eq`

English:
theorem IsSRGWith.param_eq
  proof: by
  let := Classical.decEq V
  rw [← h.card]; rw [Fintype.card_pos_iff] at hn
  obtain ⟨v⟩ := hn
  convert! card_mul_eq_card_mul G.Adj (s := G.neighborFinset v) (t := Gᶜ.neighborFinset v) _ _
  · simp [h.regular v]
  · simp [h.compl.regular v]
  · intro w hw
    rw [mem_neighborFinset] at hw
    si

中文:
定理 是SRGWith.param_eq
  证明: by
  let := Classical.decEq V
  rw [← h.card]; rw [Fintype.card_pos_iff] at hn
  obtain ⟨v⟩ := hn
  convert! card_mul_eq_card_mul G.Adj (s := G.neighborFinset v) (t := Gᶜ.neighborFinset v) _ _
  · simp [h.regular v]
  · simp [h.compl.regular v]
  · intro w hw
    rw [mem_neighborFinset] at hw
    si

Depends on / 依赖: Classical, Classical.decEq, Fintype, Fintype.card_pos_iff, G.Adj, G.neighborFinset, G.not, bipartiteAbove, card_mul_eq_card_mul, card_pos_iff, convert, filter_mem_eq_inter, h.card, h.compl.regular, h.regular, hw.symm, mem_neighborFinset, mem_sdiff, neighborFinset, regular
-/
theorem IsSRGWith.param_eq
    {V : Type u} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : G.IsSRGWith n k ℓ μ) (hn : 0 < n) :
    k * (k - ℓ - 1) = (n - k - 1) * μ := by
  let := Classical.decEq V
  rw [← h.card]; rw [Fintype.card_pos_iff] at hn
  obtain ⟨v⟩ := hn
  convert! card_mul_eq_card_mul G.Adj (s := G.neighborFinset v) (t := Gᶜ.neighborFinset v) _ _
  · simp [h.regular v]
  · simp [h.compl.regular v]
  · intro w hw
    rw [mem_neighborFinset] at hw
    simp_rw [bipartiteAbove, ← mem_neighborFinset, filter_mem_eq_inter]
    have s : {v} subseteq G.neighborFinset w \ G.neighborFinset v := by
      rw [singleton_subset_iff]; rw [mem_sdiff]; rw [mem_neighborFinset]
      exact ⟨hw.symm, G.notMem_neighborFinset_self v⟩
    rw [inter_comm]; rw [neighborFinset_compl]; rw [← inter_sdiff_assoc]; rw [← sdiff_eq_inter_compl]; rw [card_sdiff_of_subset s]; rw [card_singleton]; rw [← sdiff_inter_self_left]; rw [card_sdiff_of_subset inter_subset_left]
    congr
    · simp [h.regular w]
    · simp_rw [inter_comm, neighborFinset_def, ← Set.toFinset_inter, ← h.of_adj v w hw,
        ← Set.toFinset_card]
      congr!
  · intro w hw
    simp_rw [neighborFinset_compl, mem_sdiff, mem_compl, mem_singleton, mem_neighborFinset,
      ← Ne.eq_def] at hw
    simp_rw [bipartiteBelow, adj_comm, ← mem_neighborFinset, filter_mem_eq_inter,
      neighborFinset_def, ← Set.toFinset_inter, ← h.of_not_adj hw.2.symm hw.1,
      ← Set.toFinset_card]
    congr!

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `IsSRGWith.matrix_eq` / 定理 `IsSRGWith.matrix_eq`

English:
theorem IsSRGWith.matrix_eq
  given: {α : Type*} [Semiring α] (h : G.IsSRGWith n k ℓ μ)
  proof: by
  ext v w
  simp only [adjMatrix_pow_apply_eq_card_walk, Matrix.add_apply, Matrix.smul_apply,
    adjMatrix_apply, compl_adj]
  rw [@Fintype.card_congr _ _ (G.fintypeSetWalkLength v w 2) _
    (G.walkLengthTwoEquivCommonNeighbors v w)]
  obtain rfl | hn := eq_or_ne v w
  · rw [← Set.toFinset_card

中文:
定理 是SRGWith.matrix_eq
  条件: {α : 类型} [半环 α] (h : G.是SRGWith n k ℓ μ)
  证明: by
  ext v w
  simp only [adjMatrix_pow_apply_eq_card_walk, Matrix.add_apply, Matrix.smul_apply,
    adjMatrix_apply, compl_adj]
  rw [@Fintype.card_congr _ _ (G.fintypeSetWalkLength v w 2) _
    (G.walkLengthTwoEquivCommonNeighbors v w)]
  obtain rfl | hn := eq_or_ne v w
  · rw [← Set.toFinset_card

Depends on / 依赖: Fintype, Fintype.card_congr, G.Adj, G.fintypeSetWalkLength, G.walkLengthTwoEquivCommonNeighbors, Matrix, Matrix.add_apply, Matrix.one_apply_ne, Matrix.smul_apply, Set.toFinset_card, add_apply, add_zero, adjMatrix_apply, adjMatrix_pow_apply_eq_card_walk, card_congr, commonNeighbors, compl_adj, eq_or_ne, fintypeSetWalkLength, h.regular
-/
theorem IsSRGWith.matrix_eq {α : Type*} [Semiring α] (h : G.IsSRGWith n k ℓ μ) :
    G.adjMatrix α ^ 2 = k • (1 : Matrix V V α) + ℓ • G.adjMatrix α + μ • Gᶜ.adjMatrix α := by
  ext v w
  simp only [adjMatrix_pow_apply_eq_card_walk, Matrix.add_apply, Matrix.smul_apply,
    adjMatrix_apply, compl_adj]
  rw [@Fintype.card_congr _ _ (G.fintypeSetWalkLength v w 2) _
    (G.walkLengthTwoEquivCommonNeighbors v w)]
  obtain rfl | hn := eq_or_ne v w
  · rw [← Set.toFinset_card]
    simp [commonNeighbors, ← neighborFinset_def, h.regular v]
  · simp only [Matrix.one_apply_ne' hn.symm, ne_eq, hn]
    by_cases ha : G.Adj v w <;>
      simp only [ha, ite_true, ite_false, add_zero, zero_add, nsmul_eq_mul, smul_zero, mul_one,
        not_true_eq_false, not_false_eq_true, and_false, and_self]
    · rw [h.of_adj v w ha]
    · rw [h.of_not_adj hn ha]

end SimpleGraph
