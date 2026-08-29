/-
Copyright (c) 2024 John Talbot and Lian Bremner Tattersall. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Talbot, Lian Bremner Tattersall
-/
module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Combinatorics.SimpleGraph.CompleteMultipartite
public import Mathlib.Tactic.Linarith
/-!
# Five-wheel like graphs

This file defines an `IsFiveWheelLike` structure in a graph, and describes properties of these
structures as well as graphs which avoid this structure. These have two key uses:
* We use them to prove that a maximally `Kᵣ₊₁`-free graph is `r`-colorable iff it is
  complete-multipartite: `colorable_iff_isCompleteMultipartite_of_maximal_cliqueFree`.
* They play a key role in Brandt's proof of the Andrásfai-Erdős-Sós theorem, which is where they
  first appeared. We give this proof below, see `colorable_of_cliqueFree_lt_minDegree`.

If `G` is maximally `Kᵣ₊₂`-free and `¬ G.Adj x y` (with `x ≠ y`) then there exists an `r`-set `s`
such that `s ∪ {x}` and `s ∪ {y}` are both `r + 1`-cliques.

If `¬ G.IsCompleteMultipartite` then it contains a `G.IsPathGraph3Compl v w₁ w₂` consisting of
an edge `w₁w₂` and a vertex `v` such that `vw₁` and `vw₂` are non-edges.

Hence any maximally `Kᵣ₊₂`-free graph that is not complete-multipartite must contain distinct
vertices `v, w₁, w₂`, together with `r`-sets `s` and `t`, such that `{v, w₁, w₂}` induces the
single edge `w₁w₂`, `s ∪ t` is disjoint from `{v, w₁, w₂}`, and `s ∪ {v}`, `t ∪ {v}`, `s ∪ {w₁}` and
`t ∪ {w₂}` are all `r + 1`-cliques.

This leads to the definition of an `IsFiveWheelLike` structure which can be found in any maximally
`Kᵣ₊₂`-free graph that is not complete-multipartite (see
`exists_isFiveWheelLike_of_maximal_cliqueFree_not_isCompleteMultipartite`).

One key parameter in any such structure is the number of vertices common to all of the cliques: we
denote this quantity by `k = #(s ∩ t)` (and we will refer to such a structure as `Wᵣ,ₖ` below.)

The first interesting cases of such structures are `W₁,₀` and `W₂,₁`: `W₁,₀` is a 5-cycle,
while `W₂,₁` is a 5-cycle with an extra central hub vertex adjacent to all other vertices
(i.e. `W₂,₁` resembles a wheel with five spokes).

```
                 `W₁,₀` v `W₂,₁` v
                           / \ / | \
                          s t s ─ u ─ t
                           \ / \ / \ /
                           w₁ ─ w₂ w₁ ─ w₂
```

## Main definitions

* `SimpleGraph.IsFiveWheelLike`: predicate for `v w₁ w₂ s t` to form a 5-wheel-like subgraph of
  `G` with `r`-sets `s` and `t`, and vertices `v w₁ w₂` forming an `IsPathGraph3Compl` and
  `#(s ∩ t) = k`.

* `SimpleGraph.FiveWheelLikeFree`: predicate for `G` to have no `IsFiveWheelLike r k` subgraph.

## Implementation notes
The definitions of `IsFiveWheelLike` and `IsFiveWheelLikeFree` in this file have `r` shifted by two
compared to the definitions in Brandt **On the structure of graphs with bounded clique number**

The definition of `IsFiveWheelLike` does not contain the facts that `#s = r` and `#t = r` but we
deduce these later as `card_left` and `card_right`.

Although `#(s ∩ t)` can easily be derived from `s` and `t` we include the `IsFiveWheelLike` field
`card_inter : #(s ∩ t) = k` to match the informal / paper definitions and to simplify some
statements of results and match our definition of `IsFiveWheelLikeFree`.

The vertex set of an `IsFiveWheel` structure `Wᵣ,ₖ` is `{v, w₁, w₂} ∪ s ∪ t : Finset α`.
We will need to refer to this consistently and choose the following formulation:
`{v} ∪ ({w₁} ∪ ({w₂} ∪ (s ∪ t)))` which is definitionally equal to
`insert v <| insert w₁ <| insert w₂ <| s ∪ t`.

## References

* [B. Andrásfai, P Erdős, V. T. Sós
  **On the connection between chromatic number, maximal clique, and minimal degree of a graph**
  https://doi.org/10.1016/0012-365X(74)90133-2][andrasfaiErdosSos1974]

* [S. Brandt **On the structure of graphs with bounded clique number**
  https://doi.org/10.1007/s00493-003-0042-z][brandt2003]
-/

@[expose] public section

local notation "‖" x "‖" => Fintype.card x

open Finset SimpleGraph

variable {α : Type*} {a b c : α} {s : Finset α} {G : SimpleGraph α} {r k : Nat}

namespace SimpleGraph

section withDecEq
variable [DecidableEq α]

/--
lemma `IsNClique.insert_insert` / 引理 `IsNClique.insert_insert`

English:
lemma IsNClique.insert_insert
  statement: (h1 : G.IsNClique r (insert a s))
  proof: by
  apply h1.insert (fun b hb => ?_)
  obtain (rfl | h) := mem_insert.1 hb
  · exact ha.symm
· exact h2.1 (mem_insert_self _ s) (mem_insert_of_mem h) fun h' => (h3 (h' ▸ h)).elim

中文:
引理 IsNClique.insert_insert
  结论: (h1 : G.IsNClique r (insert a s))
  证明: by
  apply h1.insert (fun b hb => ?_)
  obtain (rfl | h) := mem_insert.1 hb
  · exact ha.symm
· exact h2.1 (mem_insert_self _ s) (mem_insert_of_mem h) fun h' => (h3 (h' ▸ h)).elim
-/
private lemma IsNClique.insert_insert (h1 : G.IsNClique r (insert a s))
    (h2 : G.IsNClique r (insert b s)) (h3 : b ∉ s) (ha : G.Adj a b) :
    G.IsNClique (r + 1) (insert b (insert a s)) := by
  apply h1.insert (fun b hb => ?_)
  obtain (rfl | h) := mem_insert.1 hb
  · exact ha.symm
· exact h2.1 (mem_insert_self _ s) (mem_insert_of_mem h) fun h' => (h3 (h' ▸ h)).elim

/--
lemma `IsNClique.insert_insert_erase` / 引理 `IsNClique.insert_insert_erase`

English:
lemma IsNClique.insert_insert_erase
  statement: (hs : G.IsNClique r (insert a s)) (hc : c in s)
  proof: by
  rw [insert_comm]; rw [← erase_insert_of_ne (fun h : a = c => ha (h ▸ hc) |>.elim)]
  simp_rw [adj_comm, ← notMem_singleton] at hd
  exact hs.insert_erase (fun _ h => hd _ (mem_sdiff.1 h).1 (mem_sdiff.1 h).2) (mem_insert_of_mem hc)

中文:
引理 IsNClique.insert_insert_erase
  结论: (hs : G.IsNClique r (insert a s)) (hc : c in s)
  证明: by
  rw [insert_comm]; rw [← erase_insert_of_ne (fun h : a = c => ha (h ▸ hc) |>.elim)]
  simp_rw [adj_comm, ← notMem_singleton] at hd
  exact hs.insert_erase (fun _ h => hd _ (mem_sdiff.1 h).1 (mem_sdiff.1 h).2) (mem_insert_of_mem hc)
-/
private lemma IsNClique.insert_insert_erase (hs : G.IsNClique r (insert a s)) (hc : c in s)
    (ha : a ∉ s) (hd : forall w in insert a s, w != c -> G.Adj w b) :
    G.IsNClique r (insert a (insert b (erase s c))) := by
  rw [insert_comm]; rw [← erase_insert_of_ne (fun h : a = c => ha (h ▸ hc) |>.elim)]
  simp_rw [adj_comm, ← notMem_singleton] at hd
  exact hs.insert_erase (fun _ h => hd _ (mem_sdiff.1 h).1 (mem_sdiff.1 h).2) (mem_insert_of_mem hc)

/--
An `IsFiveWheelLike r k v w₁ w₂ s t` structure in `G` consists of vertices `v w₁ w₂` and `r`-sets
`s` and `t` such that `{v, w₁, w₂}` induces the single edge `w₁w₂` (i.e. they form an
`IsPathGraph3Compl`), `v, w₁, w₂ ∉ s ∪ t`, `s ∪ {v}, t ∪ {v}, s ∪ {w₁}, t ∪ {w₂}` are all
`(r + 1)`-cliques and `#(s ∩ t) = k`. (If `G` is maximally `(r + 2)`-cliquefree and not complete
multipartite then `G` will contain such a structure: see
`exists_isFiveWheelLike_of_maximal_cliqueFree_not_isCompleteMultipartite`.)
-/
@[grind]
/--
Definition of `IsFiveWheelLike` / `IsFiveWheelLike` 的定义

English:
structure IsFiveWheelLike
  parameters: (G : SimpleGraph α) (r k : Nat) (v w₁ w₂ : α) (s t : Finset α)
  axioms and operations (10):
    - isPathGraph3Compl : G.IsPathGraph3Compl v w₁ w₂
    - notMem_left : v ∉ s
    - notMem_right : v ∉ t
    - fst_notMem : w₁ ∉ s
    - snd_notMem : w₂ ∉ t
    - isNClique_left : G.IsNClique (r + 1) (insert v s)
    - isNClique_fst_left : G.IsNClique (r + 1) (insert w₁ s)
    - isNClique_right : G.IsNClique (r + 1) (insert v t)
    - isNClique_snd_right : G.IsNClique (r + 1) (insert w₂ t)
    - card_inter : #(s inter t) = k

中文:
结构 IsFiveWheelLike
  参数: (G : SimpleGraph α) (r k : 自然数) (v w₁ w₂ : α) (s t : Finset α)
  公理与运算 (10 个):
    - isPathGraph3Compl : G.IsPathGraph3Compl v w₁ w₂
    - notMem_left : v ∉ s
    - notMem_right : v ∉ t
    - fst_notMem : w₁ ∉ s
    - snd_notMem : w₂ ∉ t
    - isNClique_left : G.IsNClique (r + 1) (insert v s)
    - isNClique_fst_left : G.IsNClique (r + 1) (insert w₁ s)
    - isNClique_right : G.IsNClique (r + 1) (insert v t)
    - isNClique_snd_right : G.IsNClique (r + 1) (insert w₂ t)
    - card_inter : #(s inter t) = k
-/
structure IsFiveWheelLike (G : SimpleGraph α) (r k : Nat) (v w₁ w₂ : α) (s t : Finset α) :
    Prop where
  /-- `{v, w₁, w₂}` induces the single edge `w₁w₂` -/
  isPathGraph3Compl : G.IsPathGraph3Compl v w₁ w₂
  notMem_left : v ∉ s
  notMem_right : v ∉ t
  fst_notMem : w₁ ∉ s
  snd_notMem : w₂ ∉ t
  isNClique_left : G.IsNClique (r + 1) (insert v s)
  isNClique_fst_left : G.IsNClique (r + 1) (insert w₁ s)
  isNClique_right : G.IsNClique (r + 1) (insert v t)
  isNClique_snd_right : G.IsNClique (r + 1) (insert w₂ t)
  card_inter : #(s inter t) = k

/--
lemma `exists_isFiveWheelLike_of_maximal_cliqueFree_not_isCompleteMultipartite` / 引理 `exists_isFiveWheelLike_of_maximal_cliqueFree_not_isCompleteMultipartite`

English:
lemma exists_isFiveWheelLike_of_maximal_cliqueFree_not_isCompleteMultipartite
  proof: by
  obtain ⟨v, w₁, w₂, p3⟩ := exists_isPathGraph3Compl_of_not_isCompleteMultipartite hnc
  obtain ⟨s, h1, h2, h3, h4⟩ := exists_of_maximal_cliqueFree_not_adj h p3.ne_fst p3.not_adj_fst
  obtain ⟨t, h5, h6, h7, h8⟩ := exists_of_maximal_cliqueFree_not_adj h p3.ne_snd p3.not_adj_snd
  exact ⟨_, _, _, 

中文:
引理 exists_isFiveWheelLike_of_maximal_cliqueFree_not_isCompleteMultipartite
  证明: by
  obtain ⟨v, w₁, w₂, p3⟩ := exists_isPathGraph3Compl_of_not_isCompleteMultipartite hnc
  obtain ⟨s, h1, h2, h3, h4⟩ := exists_of_maximal_cliqueFree_not_adj h p3.ne_fst p3.not_adj_fst
  obtain ⟨t, h5, h6, h7, h8⟩ := exists_of_maximal_cliqueFree_not_adj h p3.ne_snd p3.not_adj_snd
  exact ⟨_, _, _, 

Depends on / 依赖: exists_isPathGraph3Compl_of_not_isCompleteMultipartite, exists_of_maximal_cliqueFree_not_adj, ne_fst, ne_snd, not_adj_fst, not_adj_snd, p3.ne_fst, p3.ne_snd, p3.not_adj_fst, p3.not_adj_snd
-/
lemma exists_isFiveWheelLike_of_maximal_cliqueFree_not_isCompleteMultipartite
    (h : Maximal (fun H => H.CliqueFree (r + 2)) G) (hnc : ¬ G.IsCompleteMultipartite) :
    exists v w₁ w₂ s t, G.IsFiveWheelLike r #(s inter t) v w₁ w₂ s t := by
  obtain ⟨v, w₁, w₂, p3⟩ := exists_isPathGraph3Compl_of_not_isCompleteMultipartite hnc
  obtain ⟨s, h1, h2, h3, h4⟩ := exists_of_maximal_cliqueFree_not_adj h p3.ne_fst p3.not_adj_fst
  obtain ⟨t, h5, h6, h7, h8⟩ := exists_of_maximal_cliqueFree_not_adj h p3.ne_snd p3.not_adj_snd
  exact ⟨_, _, _, _, _, p3, h1, h5, h2, h6, h3, h4, h7, h8, rfl⟩

/--
Definition of `FiveWheelLikeFree` / `FiveWheelLikeFree` 的定义

English:
definition FiveWheelLikeFree
  signature: (G : SimpleGraph α) (r k : Nat)
  body: forall {v w₁ w₂ s t}, ¬ G.IsFiveWheelLike r k v w₁ w₂ s t

中文:
定义 FiveWheelLikeFree
  签名: (G : SimpleGraph α) (r k : 自然数)
  定义体: forall {v w₁ w₂ s t}, ¬ G.IsFiveWheelLike r k v w₁ w₂ s t

Depends on / 依赖: G.IsFiveWheelLike, IsFiveWheelLike
-/
def FiveWheelLikeFree (G : SimpleGraph α) (r k : Nat) : Prop :=
  forall {v w₁ w₂ s t}, ¬ G.IsFiveWheelLike r k v w₁ w₂ s t

namespace IsFiveWheelLike

variable {v w₁ w₂ : α} {t : Finset α} (hw : G.IsFiveWheelLike r k v w₁ w₂ s t)

include hw

/--
lemma `symm` / 引理 `symm`

English:
lemma symm
  statement: G.IsFiveWheelLike r k v w₂ w₁ t s
  proof: let ⟨p2, d1, d2, d3, d4, c1, c2, c3, c4, hk⟩ := hw
  ⟨p2.symm, d2, d1, d4, d3, c3, c4, c1, c2, by rwa [inter_comm]⟩

@[grind ->]

中文:
引理 symm
  结论: G.IsFiveWheelLike r k v w₂ w₁ t s
  证明: let ⟨p2, d1, d2, d3, d4, c1, c2, c3, c4, hk⟩ := hw
  ⟨p2.symm, d2, d1, d4, d3, c3, c4, c1, c2, by rwa [inter_comm]⟩

@[grind ->]
-/
@[symm] lemma symm : G.IsFiveWheelLike r k v w₂ w₁ t s :=
  let ⟨p2, d1, d2, d3, d4, c1, c2, c3, c4, hk⟩ := hw
  ⟨p2.symm, d2, d1, d4, d3, c3, c4, c1, c2, by rwa [inter_comm]⟩

@[grind ->]
/--
lemma `fst_notMem_right` / 引理 `fst_notMem_right`

English:
lemma fst_notMem_right
  statement: w₁ ∉ t
  proof: fun h => hw.isPathGraph3Compl.not_adj_fst hw.isNClique_right.1 (mem_insert_self ..)
    (mem_insert_of_mem h) hw.isPathGraph3Compl.ne_fst

@[grind ->]

中文:
引理 fst_notMem_right
  结论: w₁ ∉ t
  证明: fun h => hw.isPathGraph3Compl.not_adj_fst hw.isNClique_right.1 (mem_insert_self ..)
    (mem_insert_of_mem h) hw.isPathGraph3Compl.ne_fst

@[grind ->]

Depends on / 依赖: hw.isNClique_right, hw.isPathGraph3Compl.ne_fst, hw.isPathGraph3Compl.not_adj_fst, isNClique_right, isPathGraph3Compl, mem_insert_of_mem, mem_insert_self, ne_fst, not_adj_fst
-/
lemma fst_notMem_right : w₁ ∉ t :=
fun h => hw.isPathGraph3Compl.not_adj_fst hw.isNClique_right.1 (mem_insert_self ..)
    (mem_insert_of_mem h) hw.isPathGraph3Compl.ne_fst

@[grind ->]
/--
lemma `snd_notMem_left` / 引理 `snd_notMem_left`

English:
lemma snd_notMem_left
  statement: w₂ ∉ s
  proof: hw.symm.fst_notMem_right

中文:
引理 snd_notMem_left
  结论: w₂ ∉ s
  证明: hw.symm.fst_notMem_right

Depends on / 依赖: fst_notMem_right, hw.symm.fst_notMem_right
-/
lemma snd_notMem_left : w₂ ∉ s := hw.symm.fst_notMem_right

/--
lemma `not_colorable_succ` / 引理 `not_colorable_succ`

English:
lemma not_colorable_succ
  statement: ¬ G.Colorable (r + 1)
  proof: by
  intro ⟨C⟩
  have h := C.surjOn_of_card_le_isClique hw.isNClique_fst_left.1 (by simp [hw.isNClique_fst_left.2])
  have := C.surjOn_of_card_le_isClique hw.isNClique_snd_right.1 (by simp [hw.isNClique_snd_right.2])
  -- Since `C` is an `r + 1`-coloring and `insert w₁ s` is an `r + 1`-clique, it co

中文:
引理 not_colorable_succ
  结论: ¬ G.Colorable (r + 1)
  证明: by
  intro ⟨C⟩
  have h := C.surjOn_of_card_le_isClique hw.isNClique_fst_left.1 (by simp [hw.isNClique_fst_left.2])
  have := C.surjOn_of_card_le_isClique hw.isNClique_snd_right.1 (by simp [hw.isNClique_snd_right.2])
  -- Since `C` is an `r + 1`-coloring and `insert w₁ s` is an `r + 1`-clique, it co

Depends on / 依赖: C.surjOn_of_card_le_isClique, hw.isNClique_fst_left, hw.isNClique_snd_right, isNClique_fst_left, isNClique_snd_right, surjOn_of_card_le_isClique
-/
lemma not_colorable_succ : ¬ G.Colorable (r + 1) := by
  intro ⟨C⟩
  have h := C.surjOn_of_card_le_isClique hw.isNClique_fst_left.1 (by simp [hw.isNClique_fst_left.2])
  have := C.surjOn_of_card_le_isClique hw.isNClique_snd_right.1 (by simp [hw.isNClique_snd_right.2])
  -- Since `C` is an `r + 1`-coloring and `insert w₁ s` is an `r + 1`-clique, it contains a vertex
  -- `x` which shares its color with `v`
  obtain ⟨x, hx, hcx⟩ := h (a := C v) trivial
  -- Similarly there is a vertex `y` in `insert w₂ t` which shares its color with `v`.
  obtain ⟨y, hy, hcy⟩ := this (a := C v) trivial
  rw [coe_insert] at *
  -- However since `insert v s` and `insert v t` are cliques, we must have `x = w₁` and `y = w₂`.
  cases hx with
  | inl hx =>
    cases hy with
    | inl hy =>
    -- But this is a contradiction since `w₁` and `w₂` are adjacent.
      subst_vars; exact C.valid hw.isPathGraph3Compl.adj (hcy ▸ hcx)
    | inr hy =>
      apply (C.valid _ hcy.symm).elim
      exact hw.isNClique_right.1 (by simp) (by simp [hy]) fun h => hw.notMem_right (h ▸ hy)
  | inr hx =>
    apply (C.valid _ hcx.symm).elim
    exact hw.isNClique_left.1 (by simp) (by simp [hx]) fun h => hw.notMem_left (h ▸ hx)

@[grind ->]
/--
lemma `card_left` / 引理 `card_left`

English:
lemma card_left
  statement: s.card = r
  proof: by
  simp [← Nat.succ_inj, ← hw.isNClique_left.2, hw.notMem_left]

@[grind ->]

中文:
引理 card_left
  结论: s.card = r
  证明: by
  simp [← Nat.succ_inj, ← hw.isNClique_left.2, hw.notMem_left]

@[grind ->]

Depends on / 依赖: Nat.succ_inj, hw.isNClique_left, hw.notMem_left, isNClique_left, notMem_left, succ_inj
-/
lemma card_left : s.card = r := by
  simp [← Nat.succ_inj, ← hw.isNClique_left.2, hw.notMem_left]

@[grind ->]
/--
lemma `card_right` / 引理 `card_right`

English:
lemma card_right
  statement: t.card = r
  proof: hw.symm.card_left

中文:
引理 card_right
  结论: t.card = r
  证明: hw.symm.card_left

Depends on / 依赖: card_left, hw.symm.card_left
-/
lemma card_right : t.card = r := hw.symm.card_left

/--
lemma `card_inter_lt_of_cliqueFree` / 引理 `card_inter_lt_of_cliqueFree`

English:
lemma card_inter_lt_of_cliqueFree
  given: (h : G.CliqueFree (r + 2))
  statement: k < r
  proof: by
  contrapose! h
  -- If `r ≤ k` then `s = t` and so `s ∪ {w₁, w₂}` is an `r + 2`-clique, a contradiction.
  have hs := eq_of_subset_of_card_le inter_subset_left (hw.card_inter ▸ hw.card_left ▸ h)
  have := eq_of_subset_of_card_le inter_subset_right (hw.card_inter ▸ hw.card_right ▸ h)
  exact (hw.

中文:
引理 card_inter_lt_of_cliqueFree
  条件: (h : G.CliqueFree (r + 2))
  结论: k < r
  证明: by
  contrapose! h
  -- If `r ≤ k` then `s = t` and so `s ∪ {w₁, w₂}` is an `r + 2`-clique, a contradiction.
  have hs := eq_of_subset_of_card_le inter_subset_left (hw.card_inter ▸ hw.card_left ▸ h)
  have := eq_of_subset_of_card_le inter_subset_right (hw.card_inter ▸ hw.card_right ▸ h)
  exact (hw.

Depends on / 依赖: contrapose
-/
lemma card_inter_lt_of_cliqueFree (h : G.CliqueFree (r + 2)) : k < r := by
  contrapose! h
  -- If `r ≤ k` then `s = t` and so `s ∪ {w₁, w₂}` is an `r + 2`-clique, a contradiction.
  have hs := eq_of_subset_of_card_le inter_subset_left (hw.card_inter ▸ hw.card_left ▸ h)
  have := eq_of_subset_of_card_le inter_subset_right (hw.card_inter ▸ hw.card_right ▸ h)
  exact (hw.isNClique_fst_left.insert_insert (hs ▸ this.symm ▸ hw.isNClique_snd_right)
    hw.snd_notMem_left hw.isPathGraph3Compl.adj).not_cliqueFree

end IsFiveWheelLike

/--
lemma `exists_max_isFiveWheelLike_of_maximal_cliqueFree_not_isCompleteMultipartite` / 引理 `exists_max_isFiveWheelLike_of_maximal_cliqueFree_not_isCompleteMultipartite`

English:
lemma exists_max_isFiveWheelLike_of_maximal_cliqueFree_not_isCompleteMultipartite
  proof: by
  obtain ⟨_, _, _, s, t, hw⟩ :=
    exists_isFiveWheelLike_of_maximal_cliqueFree_not_isCompleteMultipartite h hnc
  let P : Nat -> Prop := fun k => exists v w₁ w₂ s t, G.IsFiveWheelLike r k v w₁ w₂ s t
  have hk : P #(s inter t) := ⟨_, _, _, _, _, hw⟩
  classical
  obtain ⟨_, _, _, _, _, hw⟩ := N

中文:
引理 exists_max_isFiveWheelLike_of_maximal_cliqueFree_not_isCompleteMultipartite
  证明: by
  obtain ⟨_, _, _, s, t, hw⟩ :=
    exists_isFiveWheelLike_of_maximal_cliqueFree_not_isCompleteMultipartite h hnc
  let P : Nat -> Prop := fun k => exists v w₁ w₂ s t, G.IsFiveWheelLike r k v w₁ w₂ s t
  have hk : P #(s inter t) := ⟨_, _, _, _, _, hw⟩
  classical
  obtain ⟨_, _, _, _, _, hw⟩ := N

Depends on / 依赖: G.IsFiveWheelLike, IsFiveWheelLike, Nat.findGreatest_spec, Nat.le_findGreatest, card_inter_lt_of_cliqueFre, card_inter_lt_of_cliqueFree, classical, exists_isFiveWheelLike_of_maximal_cliqueFree_not_isCompleteMultipartite, findGreatest_spec, hj.not_ge, hv.card_inter_lt_of_cliqueFre, hw.card_inter_lt_of_cliqueFree, le_findGreatest, not_ge
-/
lemma exists_max_isFiveWheelLike_of_maximal_cliqueFree_not_isCompleteMultipartite
    (h : Maximal (fun H => H.CliqueFree (r + 2)) G) (hnc : ¬ G.IsCompleteMultipartite) :
    exists k v w₁ w₂ s t, G.IsFiveWheelLike r k v w₁ w₂ s t ∧ k < r ∧
      forall j, k < j -> G.FiveWheelLikeFree r j := by
  obtain ⟨_, _, _, s, t, hw⟩ :=
    exists_isFiveWheelLike_of_maximal_cliqueFree_not_isCompleteMultipartite h hnc
  let P : Nat -> Prop := fun k => exists v w₁ w₂ s t, G.IsFiveWheelLike r k v w₁ w₂ s t
  have hk : P #(s inter t) := ⟨_, _, _, _, _, hw⟩
  classical
  obtain ⟨_, _, _, _, _, hw⟩ := Nat.findGreatest_spec (hw.card_inter_lt_of_cliqueFree h.1).le hk
  exact ⟨_, _, _, _, _, _, hw, hw.card_inter_lt_of_cliqueFree h.1,
fun _ hj _ _ _ _ _ hv => hj.not_ge Nat.le_findGreatest
           (hv.card_inter_lt_of_cliqueFree h.1).le ⟨_, _, _, _, _, hv⟩⟩

/--
lemma `CliqueFree.fiveWheelLikeFree_of_le` / 引理 `CliqueFree.fiveWheelLikeFree_of_le`

English:
lemma CliqueFree.fiveWheelLikeFree_of_le
  given: (h : G.CliqueFree (r + 2)) (hk : r <= k)
  proof: fun hw => (hw.card_inter_lt_of_cliqueFree h).not_ge hk

中文:
引理 CliqueFree.fiveWheelLikeFree_of_le
  条件: (h : G.CliqueFree (r + 2)) (hk : r <= k)
  证明: fun hw => (hw.card_inter_lt_of_cliqueFree h).not_ge hk

Depends on / 依赖: card_inter_lt_of_cliqueFree, hw.card_inter_lt_of_cliqueFree, not_ge
-/
lemma CliqueFree.fiveWheelLikeFree_of_le (h : G.CliqueFree (r + 2)) (hk : r <= k) :
    G.FiveWheelLikeFree r k := fun hw => (hw.card_inter_lt_of_cliqueFree h).not_ge hk

end withDecEq

/--
theorem `colorable_iff_isCompleteMultipartite_of_maximal_cliqueFree` / 定理 `colorable_iff_isCompleteMultipartite_of_maximal_cliqueFree`

English:
theorem colorable_iff_isCompleteMultipartite_of_maximal_cliqueFree
  proof: by
  classical
  match r with
.elim' x⟩, | 0 => exact ⟨fun _ => ⟨fun x => cliqueFree_one.1 h.1
fun _ => G.colorable_zero_iff.2 cliqueFree_one.1 h.1⟩
  | r + 1 =>
    refine ⟨fun hc => ?_, fun hc => hc.colorable_of_cliqueFree h.1⟩
    contrapose hc
    obtain ⟨_, _, _, _, _, hw⟩ :=
      exists_isFiv

中文:
定理 colorable_iff_isCompleteMultipartite_of_maximal_cliqueFree
  证明: by
  classical
  match r with
.elim' x⟩, | 0 => exact ⟨fun _ => ⟨fun x => cliqueFree_one.1 h.1
fun _ => G.colorable_zero_iff.2 cliqueFree_one.1 h.1⟩
  | r + 1 =>
    refine ⟨fun hc => ?_, fun hc => hc.colorable_of_cliqueFree h.1⟩
    contrapose hc
    obtain ⟨_, _, _, _, _, hw⟩ :=
      exists_isFiv

Depends on / 依赖: G.colorable_zero_iff, classical, cliqueFree_one, colorable_of_cliqueFree, colorable_zero_iff, contrapose, exists_isFiveWheelLike_of_maximal_cliqueFree_not_isCompleteMultipartite, hc.colorable_of_cliqueFree, hw.not_colorable_succ, not_colorable_succ
-/
theorem colorable_iff_isCompleteMultipartite_of_maximal_cliqueFree
    (h : Maximal (fun H => H.CliqueFree (r + 1)) G) : G.Colorable r ↔ G.IsCompleteMultipartite := by
  classical
  match r with
.elim' x⟩, | 0 => exact ⟨fun _ => ⟨fun x => cliqueFree_one.1 h.1
fun _ => G.colorable_zero_iff.2 cliqueFree_one.1 h.1⟩
  | r + 1 =>
    refine ⟨fun hc => ?_, fun hc => hc.colorable_of_cliqueFree h.1⟩
    contrapose hc
    obtain ⟨_, _, _, _, _, hw⟩ :=
      exists_isFiveWheelLike_of_maximal_cliqueFree_not_isCompleteMultipartite h hc
    exact hw.not_colorable_succ

section AES
variable {i j n : Nat} {d x v w₁ w₂ : α} {s t : Finset α}

section Counting

/--
lemma `sum_degree_le_of_le_not_adj` / 引理 `sum_degree_le_of_le_not_adj`

English:
lemma sum_degree_le_of_le_not_adj
  statement: [Fintype α] [DecidableEq α] [DecidableRel G.Adj]
  proof: calc
  _ = ∑ v, #(G.neighborFinset v inter W) := by
    simp_rw [degree, card_eq_sum_ones]
    exact sum_comm' (by simp [and_comm, adj_comm])
  _ <= _ := by
    simp_rw [← union_compl X, sum_union disjoint_compl_right (s₁ := X), neighborFinset_eq_filter,
             filter_inter, univ_inter, card_e

中文:
引理 sum_degree_le_of_le_not_adj
  结论: [Fintype α] [DecidableEq α] [DecidableRel G.Adj]
  证明: calc
  _ = ∑ v, #(G.neighborFinset v inter W) := by
    simp_rw [degree, card_eq_sum_ones]
    exact sum_comm' (by simp [and_comm, adj_comm])
  _ <= _ := by
    simp_rw [← union_compl X, sum_union disjoint_compl_right (s₁ := X), neighborFinset_eq_filter,
             filter_inter, univ_inter, card_e
-/
private lemma sum_degree_le_of_le_not_adj [Fintype α] [DecidableEq α] [DecidableRel G.Adj]
    {W X : Finset α} (hx : forall x in X, i <= #{z in W | ¬ G.Adj x z})
    (hxc : forall y in Xᶜ, j <= #{z in W | ¬ G.Adj y z}) :
    ∑ w in W, G.degree w <= #X * (#W - i) + #Xᶜ * (#W - j) := calc
  _ = ∑ v, #(G.neighborFinset v inter W) := by
    simp_rw [degree, card_eq_sum_ones]
    exact sum_comm' (by simp [and_comm, adj_comm])
  _ <= _ := by
    simp_rw [← union_compl X, sum_union disjoint_compl_right (s₁ := X), neighborFinset_eq_filter,
             filter_inter, univ_inter, card_eq_sum_ones X, card_eq_sum_ones Xᶜ, sum_mul, one_mul]
    gcongr <;> grind [card_filter_add_card_filter_not]

end Counting

namespace IsFiveWheelLike

variable [DecidableEq α] (hw : G.IsFiveWheelLike r k v w₁ w₂ s t) (hcf : G.CliqueFree (r + 2))

include hw hcf

/--
lemma `exist_not_adj_of_adj_inter` / 引理 `exist_not_adj_of_adj_inter`

English:
lemma exist_not_adj_of_adj_inter
  given: (hW : forall ⦃y⦄, y in s inter t -> G.Adj x y)
  proof: by
  obtain ⟨a, ha, haj⟩ := hw.isNClique_fst_left.exists_not_adj_of_cliqueFree_succ hcf x
  obtain ⟨b, hb, hbj⟩ := hw.isNClique_snd_right.exists_not_adj_of_cliqueFree_succ hcf x
  obtain ⟨c, hc, hcj⟩ := hw.isNClique_left.exists_not_adj_of_cliqueFree_succ hcf x
  obtain ⟨d, hd, hdj⟩ := hw.isNClique_r

中文:
引理 exist_not_adj_of_adj_inter
  条件: (hW : 对任意 ⦃y⦄, y in s inter t -> G.Adj x y)
  证明: by
  obtain ⟨a, ha, haj⟩ := hw.isNClique_fst_left.exists_not_adj_of_cliqueFree_succ hcf x
  obtain ⟨b, hb, hbj⟩ := hw.isNClique_snd_right.exists_not_adj_of_cliqueFree_succ hcf x
  obtain ⟨c, hc, hcj⟩ := hw.isNClique_left.exists_not_adj_of_cliqueFree_succ hcf x
  obtain ⟨d, hd, hdj⟩ := hw.isNClique_r
-/
private lemma exist_not_adj_of_adj_inter (hW : forall ⦃y⦄, y in s inter t -> G.Adj x y) :
    exists a b c d, a in insert w₁ s ∧ ¬ G.Adj x a ∧ b in insert w₂ t ∧ ¬ G.Adj x b ∧ c in insert v s ∧
    ¬ G.Adj x c ∧ d in insert v t ∧ ¬ G.Adj x d ∧ a != b ∧ a != d ∧ b != c ∧ a ∉ t ∧ b ∉ s := by
  obtain ⟨a, ha, haj⟩ := hw.isNClique_fst_left.exists_not_adj_of_cliqueFree_succ hcf x
  obtain ⟨b, hb, hbj⟩ := hw.isNClique_snd_right.exists_not_adj_of_cliqueFree_succ hcf x
  obtain ⟨c, hc, hcj⟩ := hw.isNClique_left.exists_not_adj_of_cliqueFree_succ hcf x
  obtain ⟨d, hd, hdj⟩ := hw.isNClique_right.exists_not_adj_of_cliqueFree_succ hcf x
  exact ⟨_, _, _, _, ha, haj, hb, hbj, hc, hcj, hd, hdj, by grind⟩

variable [DecidableRel G.Adj]

/--
lemma `exists_isFiveWheelLike_succ_of_not_adj_le_two` / 引理 `exists_isFiveWheelLike_succ_of_not_adj_le_two`

English:
lemma exists_isFiveWheelLike_succ_of_not_adj_le_two
  statement: (hW : forall ⦃y⦄, y in s inter t -> G.Adj x y)
  proof: by
  obtain ⟨a, b, c, d, ha, haj, hb, hbj, hc, hcj, hd, hdj, hab, had, hbc, hat, hbs⟩ :=
    hw.exist_not_adj_of_adj_inter hcf hW
  -- Let `W` denote the vertices of the copy of `Wᵣ,ₖ` in `G`
  let W := {v} union ({w₁} union ({w₂} union (s union t)))
  have ⟨hca, hdb⟩ : c = a ∧ d = b := by
    by_co

中文:
引理 exists_isFiveWheelLike_succ_of_not_adj_le_two
  结论: (hW : 对任意 ⦃y⦄, y in s inter t -> G.Adj x y)
  证明: by
  obtain ⟨a, b, c, d, ha, haj, hb, hbj, hc, hcj, hd, hdj, hab, had, hbc, hat, hbs⟩ :=
    hw.exist_not_adj_of_adj_inter hcf hW
  -- Let `W` denote the vertices of the copy of `Wᵣ,ₖ` in `G`
  let W := {v} union ({w₁} union ({w₂} union (s union t)))
  have ⟨hca, hdb⟩ : c = a ∧ d = b := by
    by_co

Depends on / 依赖: exist_not_adj_of_adj_inter, hw.exist_not_adj_of_adj_inter
-/
lemma exists_isFiveWheelLike_succ_of_not_adj_le_two (hW : forall ⦃y⦄, y in s inter t -> G.Adj x y)
    (h2 : #{z in {v} union ({w₁} union ({w₂} union (s union t))) | ¬ G.Adj x z} <= 2) :
    exists a b, G.IsFiveWheelLike r (k + 1) v w₁ w₂ (insert x (s.erase a)) (insert x (t.erase b)) := by
  obtain ⟨a, b, c, d, ha, haj, hb, hbj, hc, hcj, hd, hdj, hab, had, hbc, hat, hbs⟩ :=
    hw.exist_not_adj_of_adj_inter hcf hW
  -- Let `W` denote the vertices of the copy of `Wᵣ,ₖ` in `G`
  let W := {v} union ({w₁} union ({w₂} union (s union t)))
  have ⟨hca, hdb⟩ : c = a ∧ d = b := by
    by_contra! hf
apply h2.not_gt two_lt_card_iff.2 _
    by_cases h : a = c
    · exact ⟨a, b, d, by grind⟩
    · exact ⟨a, b, c, by grind⟩
  simp_rw [hca, hdb, mem_insert] at *
  have ⟨has, hbt, hav, hbv, haw, hbw⟩ : a in s ∧ b in t ∧ a != v ∧ b != v ∧ a != w₂ ∧ b != w₁ := by grind
  have ⟨hxv, hxw₁, hxw₂⟩ : v != x ∧ w₁ != x ∧ w₂ != x := by
    refine ⟨?_, ?_, ?_⟩
    · by_cases hax : x = a <;> rintro rfl
      · grind
· exact haj hw.isNClique_left.1 (mem_insert_self ..) (mem_insert_of_mem has) hax
    · by_cases hax : x = a <;> rintro rfl
      · grind
· exact haj hw.isNClique_fst_left.1 (mem_insert_self ..) (mem_insert_of_mem has) hax
    · by_cases hbx : x = b <;> rintro rfl
      · grind
· exact hbj hw.isNClique_snd_right.1 (mem_insert_self ..) (mem_insert_of_mem hbt) hbx
  -- Since `x` is not adjacent to `a` and `b` but is adjacent to all but at most two vertices
  -- from `W` we have `∀ w ∈ W, w ≠ a → w ≠ b → G.Adj w x`
  have wa : forall ⦃w⦄, w in W -> w != a -> w != b -> G.Adj w x := by
    intro _ hz haz hbz
    by_contra! hf
    apply h2.not_gt
    exact two_lt_card.2 ⟨_, by simp [has, hcj], _, by simp [hbt, hdj], _,
                         mem_filter.2 ⟨hz, by rwa [adj_comm] at hf⟩, hab, haz.symm, hbz.symm⟩
  have ⟨h1s, h2t⟩ : insert w₁ s subseteq W ∧ insert w₂ t subseteq W := by grind
  -- We now check that we can build a `Wᵣ,ₖ₊₁` by inserting `x` and erasing `a` and `b`
  refine ⟨a, b, ⟨by grind, by grind, by grind, by grind, by grind, ?h5, ?h6, ?h7, ?h8, ?h9⟩⟩
  -- Check that the new cliques are indeed cliques
  case h5 => exact hw.isNClique_left.insert_insert_erase has hw.notMem_left fun _ hz hZ =>
               wa ((insert_subset_insert _ fun _ hx => (by simp [hx])) hz) hZ
fun h => hbv (mem_insert.1 (h ▸ hz)).resolve_right hbs
  case h6 => exact hw.isNClique_fst_left.insert_insert_erase has hw.fst_notMem fun _ hz hZ =>
wa (h1s hz) hZ fun h => hbw (mem_insert.1 (h ▸ hz)).resolve_right hbs
  case h7 => exact hw.isNClique_right.insert_insert_erase hbt hw.notMem_right fun _ hz hZ =>
               wa ((insert_subset_insert _ fun _ hx => (by simp [hx])) hz)
                 (fun h => hav <| (mem_insert.1 (h ▸ hz)).resolve_right hat) hZ
  case h8 => exact hw.isNClique_snd_right.insert_insert_erase hbt hw.snd_notMem fun _ hz hZ =>
               wa (h2t hz) (fun h => haw <| (mem_insert.1 (h ▸ hz)).resolve_right hat) hZ
  case h9 =>
    -- Finally check that this new `IsFiveWheelLike` structure has `k + 1` common clique
    -- vertices i.e. `#((insert x (s.erase a)) ∩ (insert x (s.erase b))) = k + 1`.
    rw [← insert_inter_distrib]; rw [erase_inter]; rw [inter_erase]; rw [erase_eq_of_notMem <|
notMem_mono inter_subset_left hbs]; rw [erase_eq_of_notMem notMem_mono inter_subset_right hat]; rw [card_insert_of_notMem (fun h => G.irrefl (hW h))]; rw [hw.card_inter]

/--
lemma `minDegree_le_of_cliqueFree_fiveWheelLikeFree_succ` / 引理 `minDegree_le_of_cliqueFree_fiveWheelLikeFree_succ`

English:
lemma minDegree_le_of_cliqueFree_fiveWheelLikeFree_succ
  statement: [Fintype α]
  proof: by
  let X : Finset α := {x | forall ⦃y⦄, y in s inter t -> G.Adj x y}
  let W := {v} union ({w₁} union ({w₂} union (s union t)))
  -- Any vertex in `X` has at least 3 non-neighbors in `W` (otherwise we could build a bigger wheel)
  have dXle : forall x in X, 3 <= #{z in W | ¬ G.Adj x z} := by
    i

中文:
引理 minDegree_le_of_cliqueFree_fiveWheelLikeFree_succ
  结论: [Fintype α]
  证明: by
  let X : Finset α := {x | forall ⦃y⦄, y in s inter t -> G.Adj x y}
  let W := {v} union ({w₁} union ({w₂} union (s union t)))
  -- Any vertex in `X` has at least 3 non-neighbors in `W` (otherwise we could build a bigger wheel)
  have dXle : forall x in X, 3 <= #{z in W | ¬ G.Adj x z} := by
    i

Depends on / 依赖: Finset, G.Adj
-/
lemma minDegree_le_of_cliqueFree_fiveWheelLikeFree_succ [Fintype α]
    (hm : G.FiveWheelLikeFree r (k + 1)) : G.minDegree <= (2 * r + k) * ‖α‖ / (2 * r + k + 3) := by
  let X : Finset α := {x | forall ⦃y⦄, y in s inter t -> G.Adj x y}
  let W := {v} union ({w₁} union ({w₂} union (s union t)))
  -- Any vertex in `X` has at least 3 non-neighbors in `W` (otherwise we could build a bigger wheel)
  have dXle : forall x in X, 3 <= #{z in W | ¬ G.Adj x z} := by
    intro _ hx
    by_contra! h
    obtain ⟨_, _, hW⟩ := hw.exists_isFiveWheelLike_succ_of_not_adj_le_two hcf
(by simpa [X] using hx) Nat.le_of_succ_le_succ h
    exact hm hW
  -- Since `G` is `Kᵣ₊₂`-free and contains a `Wᵣ,ₖ`, every vertex is not adjacent to at least one
  -- wheel vertex.
  have one_le (x : α) : 1 <= #{z in {v} union ({w₁} union ({w₂} union (s union t))) | ¬ G.Adj x z} :=
    let ⟨_, hz⟩ := hw.isNClique_fst_left.exists_not_adj_of_cliqueFree_succ hcf x
    card_pos.2 ⟨_, mem_filter.2 ⟨by grind, hz.2⟩⟩
  -- Since every vertex has at least one non-neighbor in `W` we now have the following upper bound
  -- `∑ w ∈ W, H.degree w ≤ #X * (#W - 3) + #Xᶜ * (#W - 1)`
  have bdW := sum_degree_le_of_le_not_adj dXle (fun y _ => one_le y)
  -- By the definition of `X`, any `x ∈ Xᶜ` has at least one non-neighbour in `X`.
  have xcle : forall x in Xᶜ, 1 <= #{z in s inter t | ¬ G.Adj x z} := by
    intro x hx
    apply card_pos.2
    obtain ⟨_, hy⟩ : exists y in s inter t, ¬ G.Adj x y := by
      contrapose! hx
      simpa [X] using hx
    exact ⟨_, mem_filter.2 hy⟩
  -- So we also have an upper bound on the degree sum over `s ∩ t`
  -- `∑ w ∈ s ∩ t, H.degree w ≤ #Xᶜ * (#(s ∩ t) - 1) + #X * #(s ∩ t)`
  have bdX := sum_degree_le_of_le_not_adj xcle (fun _ _ => Nat.zero_le _)
  rw [compl_compl]; rw [tsub_zero]; rw [add_comm] at bdX
  rw [Nat.le_div_iff_mul_le <| Nat.add_pos_right _ zero_lt_three]
  have Wc : #W + k = 2 * r + 3 := by grind
  -- The sum of the degree sum over `W` and twice the degree sum over `s ∩ t`
  -- is at least `G.minDegree * (#W + 2 * #(s ∩ t))` which implies the result
  calc
    _ <= ∑ w in W, G.degree w + 2 * ∑ w in s inter t, G.degree w := by
      simp_rw [add_assoc, add_comm k, ← add_assoc, ← Wc, add_assoc, ← two_mul, mul_add,
               ← hw.card_inter, card_eq_sum_ones, ← mul_assoc, mul_sum, mul_one, mul_comm 2]
      gcongr with i <;> exact minDegree_le_degree ..
    _ <= (#X * (#W - 3) + #Xᶜ * (#W - 1)) + 2 * (#X * #(s inter t) + #Xᶜ * (#(s inter t) - 1)) := by gcongr
    _ = #X * (#W - 3 + 2 * k) + #Xᶜ * ((#W - 1) + 2 * (k - 1)) := by grind
    _ <= _ := by
        by_cases hk : k = 0 -- so `s ∩ t = ∅` and hence `Xᶜ = ∅`
        · have Xu : X = univ := by
            rw [← hw.card_inter]; rw [card_eq_zero] at hk
            exact eq_univ_of_forall fun _ => by simp [X, hk]
          subst k
          rw [add_zero] at Wc
          simp [Xu, Wc, mul_comm]
        have w3 : 3 <= #W := two_lt_card.2 ⟨_, mem_insert_self .., _, by simp [W], _, by simp [W],
          hw.isPathGraph3Compl.ne_fst, hw.isPathGraph3Compl.ne_snd, hw.isPathGraph3Compl.fst_ne_snd⟩
        have hap : #W - 1 + 2 * (k - 1) = #W - 3 + 2 * k := by lia
        rw [hap]; rw [← add_mul]; rw [card_add_card_compl]; rw [mul_comm]; rw [two_mul]; rw [← add_assoc]
        gcongr
        lia

end IsFiveWheelLike

/--
theorem `colorable_of_cliqueFree_lt_minDegree` / 定理 `colorable_of_cliqueFree_lt_minDegree`

English:
theorem colorable_of_cliqueFree_lt_minDegree
  statement: [Fintype α] [DecidableRel G.Adj]
  proof: by
  match r with
  | 0 | 1 => aesop
  | r + 2 =>
    classical
    -- There is an edge maximal `Kᵣ₊₃`-free supergraph `H` of `G`
    obtain ⟨H, hle, hmcf⟩ := @Finite.exists_le_maximal _ _ _ (fun H => H.CliqueFree (r + 3)) G hf
    -- If `H` is `r + 2`-colorable then so is `G`
    apply Colorable.mo

中文:
定理 colorable_of_cliqueFree_lt_minDegree
  结论: [Fintype α] [DecidableRel G.Adj]
  证明: by
  match r with
  | 0 | 1 => aesop
  | r + 2 =>
    classical
    -- There is an edge maximal `Kᵣ₊₃`-free supergraph `H` of `G`
    obtain ⟨H, hle, hmcf⟩ := @Finite.exists_le_maximal _ _ _ (fun H => H.CliqueFree (r + 3)) G hf
    -- If `H` is `r + 2`-colorable then so is `G`
    apply Colorable.mo

Depends on / 依赖: classical
-/
theorem colorable_of_cliqueFree_lt_minDegree [Fintype α] [DecidableRel G.Adj]
    (hf : G.CliqueFree (r + 1)) (hd : (3 * r - 4) * ‖α‖ / (3 * r - 1) < G.minDegree) :
    G.Colorable r := by
  match r with
  | 0 | 1 => aesop
  | r + 2 =>
    classical
    -- There is an edge maximal `Kᵣ₊₃`-free supergraph `H` of `G`
    obtain ⟨H, hle, hmcf⟩ := @Finite.exists_le_maximal _ _ _ (fun H => H.CliqueFree (r + 3)) G hf
    -- If `H` is `r + 2`-colorable then so is `G`
    apply Colorable.mono_left hle
    -- Suppose, for a contradiction, that `H` is not `r + 2`-colorable
    by_contra! hnotcol
    -- so `H` is not complete-multipartite
have hn : ¬ H.IsCompleteMultipartite := fun hc => hnotcol hc.colorable_of_cliqueFree hmcf.1
    -- Hence `H` contains `Wᵣ₊₁,ₖ` but not `Wᵣ₊₁,ₖ₊₁`, for some `k < r + 1`
    obtain ⟨k, _, _, _, _, _, hw, hlt, hm⟩ :=
      exists_max_isFiveWheelLike_of_maximal_cliqueFree_not_isCompleteMultipartite hmcf hn
    -- But the minimum degree of `G`, and hence of `H`, is too large for it to be `Wᵣ₊₁,ₖ₊₁`-free,
    -- a contradiction.
have hD := hw.minDegree_le_of_cliqueFree_fiveWheelLikeFree_succ hmcf.1 hm _ lt_add_one _
    have : (2 * (r + 1) + k) * ‖α‖ / (2 * (r + 1) + k + 3) <= (3 * r + 2) * ‖α‖ / (3 * r + 5) := by
      apply (Nat.le_div_iff_mul_le <| Nat.succ_pos _).2
 (mul_le_mul_iff_right₀ (_ + 2).succ_pos).1 _
      rw [← mul_assoc]; rw [mul_comm (2 * r + 2 + k + 3)]; rw [mul_comm _ (_ * ‖α‖)]
      apply (Nat.mul_le_mul_right _ (Nat.div_mul_le_self ..)).trans
      nlinarith
exact (hd.trans_le <| minDegree_le_minDegree hle).not_ge hD.trans this

end AES
end SimpleGraph
