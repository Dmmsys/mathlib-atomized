/-
Copyright (c) 2023 Jeremy Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Tan
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.Combinatorics.SimpleGraph.Subgraph

/-!
# Local graph operations

This file defines some single-graph operations that modify a finite number of vertices
and proves basic theorems about them. When the graph itself has a finite number of vertices
we also prove theorems about the number of edges in the modified graphs.

## Main definitions

* `G.replaceVertex s t` is `G` with `t` replaced by a copy of `s`,
  removing the `s-t` edge if present.
* `edge s t` is the graph with a single `s-t` edge. Adding this edge to a graph `G` is then
  `G ⊔ edge s t`.
-/

@[expose] public section


open Finset

namespace SimpleGraph

variable {V : Type*} (G : SimpleGraph V) (s t : V)

section ReplaceVertex

variable [DecidableEq V]

/--
Definition of `replaceVertex` / `replaceVertex` 的定义

English:
definition replaceVertex
  signature: : SimpleGraph V where
  body: if v = t then if w = t then False else G.Adj s w
                      else if w = t then G.Adj v s else G.Adj v w
  symm.symm v w := by split_ifs <;> simp [adj_comm]

中文:
定义 replaceVertex
  签名: : 简单图 V where
  定义体: if v = t then if w = t then False else G.Adj s w
                      else if w = t then G.Adj v s else G.Adj v w
  symm.symm v w := by split_ifs <;> simp [adj_comm]

Depends on / 依赖: G.Adj
-/
def replaceVertex : SimpleGraph V where
  Adj v w := if v = t then if w = t then False else G.Adj s w
                      else if w = t then G.Adj v s else G.Adj v w
  symm.symm v w := by split_ifs <;> simp [adj_comm]

/--
lemma `not_adj_replaceVertex_same` / 引理 `not_adj_replaceVertex_same`

English:
lemma not_adj_replaceVertex_same
  statement: ¬(G.replaceVertex s t).Adj s t
  proof: by simp [replaceVertex]

中文:
引理 not_adj_replaceVertex_same
  结论: ¬(G.replaceVertex s t).伴随 s t
  证明: by simp [replaceVertex]

Depends on / 依赖: replaceVertex
-/
lemma not_adj_replaceVertex_same : ¬(G.replaceVertex s t).Adj s t := by simp [replaceVertex]

/--
lemma `replaceVertex_self` / 引理 `replaceVertex_self`

English:
lemma replaceVertex_self
  statement: G.replaceVertex s s = G
  proof: by
  ext; unfold replaceVertex; aesop (add simp or_iff_not_imp_left)

中文:
引理 replaceVertex_self
  结论: G.replaceVertex s s = G
  证明: by
  ext; unfold replaceVertex; aesop (add simp or_iff_not_imp_left)
-/
@[simp] lemma replaceVertex_self : G.replaceVertex s s = G := by
  ext; unfold replaceVertex; aesop (add simp or_iff_not_imp_left)

variable {t}

/--
lemma `adj_replaceVertex_iff_of_ne_left` / 引理 `adj_replaceVertex_iff_of_ne_left`

English:
lemma adj_replaceVertex_iff_of_ne_left
  given: {w : V} (hw : w != t)
  proof: by simp [replaceVertex, hw]

中文:
引理 adj_replaceVertex_iff_of_ne_left
  条件: {w : V} (hw : w != t)
  证明: by simp [replaceVertex, hw]

Depends on / 依赖: replaceVertex
-/
lemma adj_replaceVertex_iff_of_ne_left {w : V} (hw : w != t) :
    (G.replaceVertex s t).Adj s w ↔ G.Adj s w := by simp [replaceVertex, hw]

/--
lemma `adj_replaceVertex_iff_of_ne_right` / 引理 `adj_replaceVertex_iff_of_ne_right`

English:
lemma adj_replaceVertex_iff_of_ne_right
  given: {w : V} (hw : w != t)
  proof: by simp [replaceVertex, hw]

中文:
引理 adj_replaceVertex_iff_of_ne_right
  条件: {w : V} (hw : w != t)
  证明: by simp [replaceVertex, hw]

Depends on / 依赖: replaceVertex
-/
lemma adj_replaceVertex_iff_of_ne_right {w : V} (hw : w != t) :
    (G.replaceVertex s t).Adj t w ↔ G.Adj s w := by simp [replaceVertex, hw]

/--
lemma `adj_replaceVertex_iff_of_ne` / 引理 `adj_replaceVertex_iff_of_ne`

English:
lemma adj_replaceVertex_iff_of_ne
  given: {v w : V} (hv : v != t) (hw : w != t)
  proof: by simp [replaceVertex, hv, hw]

中文:
引理 adj_replaceVertex_iff_of_ne
  条件: {v w : V} (hv : v != t) (hw : w != t)
  证明: by simp [replaceVertex, hv, hw]

Depends on / 依赖: replaceVertex
-/
lemma adj_replaceVertex_iff_of_ne {v w : V} (hv : v != t) (hw : w != t) :
    (G.replaceVertex s t).Adj v w ↔ G.Adj v w := by simp [replaceVertex, hv, hw]

variable {s}

/--
theorem `edgeSet_replaceVertex_of_not_adj` / 定理 `edgeSet_replaceVertex_of_not_adj`

English:
theorem edgeSet_replaceVertex_of_not_adj
  given: (hn : ¬G.Adj s t)
  statement: (G.replaceVertex s t).edgeSet =
  proof: by
  ext e; refine e.inductionOn ?_
  simp only [replaceVertex, mem_edgeSet, Set.mem_union, Set.mem_sdiff, mk'_mem_incidenceSet_iff]
  intros; split_ifs; exacts [by simp_all, by aesop, by rw [adj_comm]; aesop, by grind]

中文:
定理 edgeSet_replaceVertex_of_not_adj
  条件: (hn : ¬G.伴随 s t)
  结论: (G.replaceVertex s t).edgeSet =
  证明: by
  ext e; refine e.inductionOn ?_
  simp only [replaceVertex, mem_edgeSet, Set.mem_union, Set.mem_sdiff, mk'_mem_incidenceSet_iff]
  intros; split_ifs; exacts [by simp_all, by aesop, by rw [adj_comm]; aesop, by grind]

Depends on / 依赖: Set.mem_sdiff, Set.mem_union, _mem_incidenceSet_iff, adj_comm, e.inductionOn, exacts, inductionOn, intros, mem_edgeSet, mem_sdiff, mem_union, replaceVertex, split_ifs
-/
theorem edgeSet_replaceVertex_of_not_adj (hn : ¬G.Adj s t) : (G.replaceVertex s t).edgeSet =
    G.edgeSet \ G.incidenceSet t union (s(·, t)) '' (G.neighborSet s) := by
  ext e; refine e.inductionOn ?_
  simp only [replaceVertex, mem_edgeSet, Set.mem_union, Set.mem_sdiff, mk'_mem_incidenceSet_iff]
  intros; split_ifs; exacts [by simp_all, by aesop, by rw [adj_comm]; aesop, by grind]

/--
theorem `edgeSet_replaceVertex_of_adj` / 定理 `edgeSet_replaceVertex_of_adj`

English:
theorem edgeSet_replaceVertex_of_adj
  given: (ha : G.Adj s t)
  statement: (G.replaceVertex s t).edgeSet =
  proof: by
  ext e; refine e.inductionOn ?_
  simp only [replaceVertex, mem_edgeSet, Set.mem_union, Set.mem_sdiff, mk'_mem_incidenceSet_iff]
  intros; split_ifs; exacts [by simp_all, by aesop, by rw [adj_comm]; aesop, by grind]

中文:
定理 edgeSet_replaceVertex_of_adj
  条件: (ha : G.伴随 s t)
  结论: (G.replaceVertex s t).edgeSet =
  证明: by
  ext e; refine e.inductionOn ?_
  simp only [replaceVertex, mem_edgeSet, Set.mem_union, Set.mem_sdiff, mk'_mem_incidenceSet_iff]
  intros; split_ifs; exacts [by simp_all, by aesop, by rw [adj_comm]; aesop, by grind]

Depends on / 依赖: Set.mem_sdiff, Set.mem_union, _mem_incidenceSet_iff, adj_comm, e.inductionOn, exacts, inductionOn, intros, mem_edgeSet, mem_sdiff, mem_union, replaceVertex, split_ifs
-/
theorem edgeSet_replaceVertex_of_adj (ha : G.Adj s t) : (G.replaceVertex s t).edgeSet =
    (G.edgeSet \ G.incidenceSet t union (s(·, t)) '' (G.neighborSet s)) \ {s(t, t)} := by
  ext e; refine e.inductionOn ?_
  simp only [replaceVertex, mem_edgeSet, Set.mem_union, Set.mem_sdiff, mk'_mem_incidenceSet_iff]
  intros; split_ifs; exacts [by simp_all, by aesop, by rw [adj_comm]; aesop, by grind]

variable [Fintype V] [DecidableRel G.Adj]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: DecidableRel (G.replaceVertex s t).Adj
  body: inferInstanceAs DecidableRel (mk _ _ _).Adj

中文:
实例 :
  签名: DecidableRel (G.replaceVertex s t).伴随
  定义体: inferInstanceAs DecidableRel (mk _ _ _).Adj

Depends on / 依赖: DecidableRel
-/
instance : DecidableRel (G.replaceVertex s t).Adj := inferInstanceAs DecidableRel (mk _ _ _).Adj

/--
theorem `edgeFinset_replaceVertex_of_not_adj` / 定理 `edgeFinset_replaceVertex_of_not_adj`

English:
theorem edgeFinset_replaceVertex_of_not_adj
  given: (hn : ¬G.Adj s t)
  statement: (G.replaceVertex s t).edgeFinset =
  proof: by
  apply Finset.coe_injective
  push_cast
  exact G.edgeSet_replaceVertex_of_not_adj hn

中文:
定理 edgeFinset_replaceVertex_of_not_adj
  条件: (hn : ¬G.伴随 s t)
  结论: (G.replaceVertex s t).edgeFinset =
  证明: by
  apply Finset.coe_injective
  push_cast
  exact G.edgeSet_replaceVertex_of_not_adj hn

Depends on / 依赖: Finset, Finset.coe_injective, G.edgeSet_replaceVertex_of_not_adj, coe_injective, edgeSet_replaceVertex_of_not_adj
-/
theorem edgeFinset_replaceVertex_of_not_adj (hn : ¬G.Adj s t) : (G.replaceVertex s t).edgeFinset =
    G.edgeFinset \ G.incidenceFinset t union (G.neighborFinset s).image (s(·, t)) := by
  apply Finset.coe_injective
  push_cast
  exact G.edgeSet_replaceVertex_of_not_adj hn

/--
theorem `edgeFinset_replaceVertex_of_adj` / 定理 `edgeFinset_replaceVertex_of_adj`

English:
theorem edgeFinset_replaceVertex_of_adj
  given: (ha : G.Adj s t)
  statement: (G.replaceVertex s t).edgeFinset =
  proof: by
  apply Finset.coe_injective
  push_cast
  exact G.edgeSet_replaceVertex_of_adj ha

中文:
定理 edgeFinset_replaceVertex_of_adj
  条件: (ha : G.伴随 s t)
  结论: (G.replaceVertex s t).edgeFinset =
  证明: by
  apply Finset.coe_injective
  push_cast
  exact G.edgeSet_replaceVertex_of_adj ha

Depends on / 依赖: Finset, Finset.coe_injective, G.edgeSet_replaceVertex_of_adj, coe_injective, edgeSet_replaceVertex_of_adj
-/
theorem edgeFinset_replaceVertex_of_adj (ha : G.Adj s t) : (G.replaceVertex s t).edgeFinset =
    (G.edgeFinset \ G.incidenceFinset t union (G.neighborFinset s).image (s(·, t))) \ {s(t, t)} := by
  apply Finset.coe_injective
  push_cast
  exact G.edgeSet_replaceVertex_of_adj ha

/--
lemma `disjoint_sdiff_neighborFinset_image` / 引理 `disjoint_sdiff_neighborFinset_image`

English:
lemma disjoint_sdiff_neighborFinset_image
  proof: by
  rw [disjoint_iff_ne]
  intro e he
  have : t ∉ e := by
    rw [mem_sdiff]; rw [mem_incidenceFinset] at he
    obtain ⟨_, h⟩ := he
    contrapose h
    simp_all [incidenceSet]
  aesop

中文:
引理 disjoint_sdiff_neighborFinset_image
  证明: by
  rw [disjoint_iff_ne]
  intro e he
  have : t ∉ e := by
    rw [mem_sdiff]; rw [mem_incidenceFinset] at he
    obtain ⟨_, h⟩ := he
    contrapose h
    simp_all [incidenceSet]
  aesop

Depends on / 依赖: contrapose, disjoint_iff_ne, incidenceSet, mem_incidenceFinset, mem_sdiff
-/
lemma disjoint_sdiff_neighborFinset_image :
    Disjoint (G.edgeFinset \ G.incidenceFinset t) ((G.neighborFinset s).image (s(·, t))) := by
  rw [disjoint_iff_ne]
  intro e he
  have : t ∉ e := by
    rw [mem_sdiff]; rw [mem_incidenceFinset] at he
    obtain ⟨_, h⟩ := he
    contrapose h
    simp_all [incidenceSet]
  aesop

/--
theorem `card_edgeFinset_replaceVertex_of_not_adj` / 定理 `card_edgeFinset_replaceVertex_of_not_adj`

English:
theorem card_edgeFinset_replaceVertex_of_not_adj
  given: (hn : ¬G.Adj s t)
  proof: by
  have inc : G.incidenceFinset t subseteq G.edgeFinset := by simp [incidenceFinset, incidenceSet_subset]
  rw [G.edgeFinset_replaceVertex_of_not_adj hn]; rw [card_union_of_disjoint G.disjoint_sdiff_neighborFinset_image]; rw [card_sdiff_of_subset inc]; rw [← Nat.sub_add_comm card_le_card inc]; rw 

中文:
定理 card_edgeFinset_replaceVertex_of_not_adj
  条件: (hn : ¬G.伴随 s t)
  证明: by
  have inc : G.incidenceFinset t subseteq G.edgeFinset := by simp [incidenceFinset, incidenceSet_subset]
  rw [G.edgeFinset_replaceVertex_of_not_adj hn]; rw [card_union_of_disjoint G.disjoint_sdiff_neighborFinset_image]; rw [card_sdiff_of_subset inc]; rw [← Nat.sub_add_comm card_le_card inc]; rw 

Depends on / 依赖: Function, Function.Injective, G.disjoint_sdiff_neighborFinset_image, G.edgeFinset, G.edgeFinset_replaceVertex_of_not_adj, G.incidenceFinset, Injective, Nat.sub_add_comm, card_image_of_injective, card_incidenceFinset_eq_degree, card_le_card, card_neighborFinset_eq_degree, card_sdiff_of_subset, card_union_of_disjoint, disjoint_sdiff_neighborFinset_image, edgeFinset, edgeFinset_replaceVertex_of_not_adj, incidenceFinset, incidenceSet_subset, sub_add_comm
-/
theorem card_edgeFinset_replaceVertex_of_not_adj (hn : ¬G.Adj s t) :
    #(G.replaceVertex s t).edgeFinset = #G.edgeFinset + G.degree s - G.degree t := by
  have inc : G.incidenceFinset t subseteq G.edgeFinset := by simp [incidenceFinset, incidenceSet_subset]
  rw [G.edgeFinset_replaceVertex_of_not_adj hn]; rw [card_union_of_disjoint G.disjoint_sdiff_neighborFinset_image]; rw [card_sdiff_of_subset inc]; rw [← Nat.sub_add_comm card_le_card inc]; rw [card_incidenceFinset_eq_degree]
  congr 2
  rw [card_image_of_injective]; rw [card_neighborFinset_eq_degree]
  unfold Function.Injective
  aesop

/--
theorem `card_edgeFinset_replaceVertex_of_adj` / 定理 `card_edgeFinset_replaceVertex_of_adj`

English:
theorem card_edgeFinset_replaceVertex_of_adj
  given: (ha : G.Adj s t)
  proof: by
  have inc : G.incidenceFinset t subseteq G.edgeFinset := by simp [incidenceFinset, incidenceSet_subset]
  rw [G.edgeFinset_replaceVertex_of_adj ha]; rw [card_sdiff_of_subset (by simp [ha]),
    card_union_of_disjoint G.disjoint_sdiff_neighborFinset_image, card_sdiff_of_subset inc,
← Nat.sub_add_

中文:
定理 card_edgeFinset_replaceVertex_of_adj
  条件: (ha : G.伴随 s t)
  证明: by
  have inc : G.incidenceFinset t subseteq G.edgeFinset := by simp [incidenceFinset, incidenceSet_subset]
  rw [G.edgeFinset_replaceVertex_of_adj ha]; rw [card_sdiff_of_subset (by simp [ha]),
    card_union_of_disjoint G.disjoint_sdiff_neighborFinset_image, card_sdiff_of_subset inc,
← Nat.sub_add_

Depends on / 依赖: Function, Function.Injective, G.disjoint_sdiff_neighborFinset_image, G.edgeFinset, G.edgeFinset_replaceVertex_of_adj, G.incidenceFinset, Injective, Nat.sub_add_comm, card_image_of_injective, card_incidenceFinset_eq_degree, card_le_card, card_neighborFinset_eq_degree, card_sdiff_of_subset, card_union_of_disjoint, disjoint_sdiff_neighborFinset_image, edgeFinset, edgeFinset_replaceVertex_of_adj, incidenceFinset, incidenceSet_subset, sub_add_comm
-/
theorem card_edgeFinset_replaceVertex_of_adj (ha : G.Adj s t) :
    #(G.replaceVertex s t).edgeFinset = #G.edgeFinset + G.degree s - G.degree t - 1 := by
  have inc : G.incidenceFinset t subseteq G.edgeFinset := by simp [incidenceFinset, incidenceSet_subset]
  rw [G.edgeFinset_replaceVertex_of_adj ha]; rw [card_sdiff_of_subset (by simp [ha]),
    card_union_of_disjoint G.disjoint_sdiff_neighborFinset_image, card_sdiff_of_subset inc,
← Nat.sub_add_comm card_le_card inc, card_incidenceFinset_eq_degree]
  congr 2
  rw [card_image_of_injective]; rw [card_neighborFinset_eq_degree]
  unfold Function.Injective
  aesop

end ReplaceVertex

section AddEdge

/--
Definition of `edge` / `edge` 的定义

English:
definition edge
  signature: : SimpleGraph V
  body: fromEdgeSet {s(s, t)}

@[grind =]

中文:
定义 edge
  签名: : 简单图 V
  定义体: fromEdgeSet {s(s, t)}

@[grind =]

Depends on / 依赖: fromEdgeSet
-/
def edge : SimpleGraph V := fromEdgeSet {s(s, t)}

@[grind =]
/--
lemma `edge_adj` / 引理 `edge_adj`

English:
lemma edge_adj
  given: (v w : V)
  statement: (edge s t).Adj v w ↔ (v = s ∧ w = t ∨ v = t ∧ w = s) ∧ v != w
  proof: by
  rw [edge]; rw [fromEdgeSet_adj]; rw [Set.mem_singleton_iff]; rw [Sym2.eq_iff]

中文:
引理 edge_adj
  条件: (v w : V)
  结论: (edge s t).伴随 v w ↔ (v = s ∧ w = t ∨ v = t ∧ w = s) ∧ v != w
  证明: by
  rw [edge]; rw [fromEdgeSet_adj]; rw [Set.mem_singleton_iff]; rw [Sym2.eq_iff]

Depends on / 依赖: Set.mem_singleton_iff, Sym2.eq_iff, eq_iff, fromEdgeSet_adj, mem_singleton_iff
-/
lemma edge_adj (v w : V) : (edge s t).Adj v w ↔ (v = s ∧ w = t ∨ v = t ∧ w = s) ∧ v != w := by
  rw [edge]; rw [fromEdgeSet_adj]; rw [Set.mem_singleton_iff]; rw [Sym2.eq_iff]

/--
lemma `adj_edge` / 引理 `adj_edge`

English:
lemma adj_edge
  given: {v w : V}
  statement: (edge s t).Adj v w ↔ s(s, t) = s(v, w) ∧ v != w
  proof: by
  grind

中文:
引理 adj_edge
  条件: {v w : V}
  结论: (edge s t).伴随 v w ↔ s(s, t) = s(v, w) ∧ v != w
  证明: by
  grind
-/
lemma adj_edge {v w : V} : (edge s t).Adj v w ↔ s(s, t) = s(v, w) ∧ v != w := by
  grind

/--
lemma `edge_comm` / 引理 `edge_comm`

English:
lemma edge_comm
  statement: edge s t = edge t s
  proof: by
  rw [edge]; rw [edge]; rw [Sym2.eq_swap]

中文:
引理 edge_comm
  结论: edge s t = edge t s
  证明: by
  rw [edge]; rw [edge]; rw [Sym2.eq_swap]

Depends on / 依赖: Sym2.eq_swap, eq_swap
-/
lemma edge_comm : edge s t = edge t s := by
  rw [edge]; rw [edge]; rw [Sym2.eq_swap]

/--
lemma `edge_le` / 引理 `edge_le`

English:
lemma edge_le
  statement: edge s t <= G ↔ {s(s, t)} \ Sym2.diagSet subseteq G.edgeSet
  proof: by simp [edge]

中文:
引理 edge_le
  结论: edge s t <= G ↔ {s(s, t)} \ Sym2.diagSet subseteq G.edgeSet
  证明: by simp [edge]
-/
@[simp] lemma edge_le : edge s t <= G ↔ {s(s, t)} \ Sym2.diagSet subseteq G.edgeSet := by simp [edge]

variable [DecidableEq V] in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: DecidableRel (edge s t).Adj
  body: fun _ _ => by
  rw [edge_adj]; infer_instance

@[simp]

中文:
实例 :
  签名: DecidableRel (edge s t).伴随
  定义体: fun _ _ => by
  rw [edge_adj]; infer_instance

@[simp]

Depends on / 依赖: edge_adj, infer_instance
-/
instance : DecidableRel (edge s t).Adj := fun _ _ => by
  rw [edge_adj]; infer_instance

@[simp]
/--
lemma `edge_self_eq_bot` / 引理 `edge_self_eq_bot`

English:
lemma edge_self_eq_bot
  statement: edge s s = ⊥
  proof: by
  ext; rw [edge_adj]; simp_all

中文:
引理 edge_self_eq_bot
  结论: edge s s = ⊥
  证明: by
  ext; rw [edge_adj]; simp_all

Depends on / 依赖: edge_adj
-/
lemma edge_self_eq_bot : edge s s = ⊥ := by
  ext; rw [edge_adj]; simp_all

/--
lemma `sup_edge_self` / 引理 `sup_edge_self`

English:
lemma sup_edge_self
  statement: G ⊔ edge s s = G
  proof: by simp

中文:
引理 sup_edge_self
  结论: G ⊔ edge s s = G
  证明: by simp
-/
lemma sup_edge_self : G ⊔ edge s s = G := by simp

/--
lemma `lt_sup_edge` / 引理 `lt_sup_edge`

English:
lemma lt_sup_edge
  given: (hne : s != t) (hn : ¬ G.Adj s t)
  statement: G < G ⊔ edge s t
  proof: left_lt_sup.2 fun h => hn h (edge_adj ..).mpr ⟨Or.inl ⟨rfl, rfl⟩, hne⟩

中文:
引理 lt_sup_edge
  条件: (hne : s != t) (hn : ¬ G.伴随 s t)
  结论: G < G ⊔ edge s t
  证明: left_lt_sup.2 fun h => hn h (edge_adj ..).mpr ⟨Or.inl ⟨rfl, rfl⟩, hne⟩

Depends on / 依赖: Or.inl, edge_adj, left_lt_sup
-/
lemma lt_sup_edge (hne : s != t) (hn : ¬ G.Adj s t) : G < G ⊔ edge s t :=
left_lt_sup.2 fun h => hn h (edge_adj ..).mpr ⟨Or.inl ⟨rfl, rfl⟩, hne⟩

/--
lemma `edge_le_iff` / 引理 `edge_le_iff`

English:
lemma edge_le_iff
  given: {v w : V}
  statement: edge v w <= G ↔ v = w ∨ G.Adj v w
  proof: by
  obtain h | h := eq_or_ne v w
  · simp [h]
· refine ⟨fun h => .inr h (by simp_all [edge_adj]), fun hadj v' w' hvw' => ?_⟩
    grind [adj_symm]

@[simp]

中文:
引理 edge_le_iff
  条件: {v w : V}
  结论: edge v w <= G ↔ v = w ∨ G.伴随 v w
  证明: by
  obtain h | h := eq_or_ne v w
  · simp [h]
· refine ⟨fun h => .inr h (by simp_all [edge_adj]), fun hadj v' w' hvw' => ?_⟩
    grind [adj_symm]

@[simp]

Depends on / 依赖: adj_symm, edge_adj, eq_or_ne
-/
lemma edge_le_iff {v w : V} : edge v w <= G ↔ v = w ∨ G.Adj v w := by
  obtain h | h := eq_or_ne v w
  · simp [h]
· refine ⟨fun h => .inr h (by simp_all [edge_adj]), fun hadj v' w' hvw' => ?_⟩
    grind [adj_symm]

@[simp]
/--
lemma `edgeSet_edge` / 引理 `edgeSet_edge`

English:
lemma edgeSet_edge
  given: (v w : V)
  statement: (edge v w).edgeSet = {s(v, w)} \ Sym2.diagSet
  proof: by simp [edge]

中文:
引理 edgeSet_edge
  条件: (v w : V)
  结论: (edge v w).edgeSet = {s(v, w)} \ Sym2.diagSet
  证明: by simp [edge]
-/
lemma edgeSet_edge (v w : V) : (edge v w).edgeSet = {s(v, w)} \ Sym2.diagSet := by simp [edge]

/--
lemma `edgeSet_edge_subset` / 引理 `edgeSet_edge_subset`

English:
lemma edgeSet_edge_subset
  given: {v w : V}
  statement: (edge v w).edgeSet subseteq {s(v, w)}
  proof: by simp [edge]

中文:
引理 edgeSet_edge_subset
  条件: {v w : V}
  结论: (edge v w).edgeSet subseteq {s(v, w)}
  证明: by simp [edge]
-/
lemma edgeSet_edge_subset {v w : V} : (edge v w).edgeSet subseteq {s(v, w)} := by simp [edge]

variable {s t}

/--
lemma `edgeSet_edge_of_ne` / 引理 `edgeSet_edge_of_ne`

English:
lemma edgeSet_edge_of_ne
  given: (h : s != t)
  statement: (edge s t).edgeSet = {s(s, t)}
  proof: by simpa [edge]

@[deprecated (since := "2026-03-18")] alias edge_edgeSet_of_ne := edgeSet_edge_of_ne

中文:
引理 edgeSet_edge_of_ne
  条件: (h : s != t)
  结论: (edge s t).edgeSet = {s(s, t)}
  证明: by simpa [edge]

@[deprecated (since := "2026-03-18")] alias edge_edgeSet_of_ne := edgeSet_edge_of_ne
-/
lemma edgeSet_edge_of_ne (h : s != t) : (edge s t).edgeSet = {s(s, t)} := by simpa [edge]

@[deprecated (since := "2026-03-18")] alias edge_edgeSet_of_ne := edgeSet_edge_of_ne

/--
lemma `sup_edge_of_adj` / 引理 `sup_edge_of_adj`

English:
lemma sup_edge_of_adj
  given: (h : G.Adj s t)
  statement: G ⊔ edge s t = G
  proof: by
  simp [h]

中文:
引理 sup_edge_of_adj
  条件: (h : G.伴随 s t)
  结论: G ⊔ edge s t = G
  证明: by
  simp [h]
-/
lemma sup_edge_of_adj (h : G.Adj s t) : G ⊔ edge s t = G := by
  simp [h]

/--
lemma `deleteEdges_edge` / 引理 `deleteEdges_edge`

English:
lemma deleteEdges_edge
  given: {u v : V} {s : Set (Sym2 V)} (h : s(u, v) in s)
  proof: by simp [edge, Set.sdiff_subset_iff, h]

中文:
引理 deleteEdges_edge
  条件: {u v : V} {s : 集合 (Sym2 V)} (h : s(u, v) in s)
  证明: by simp [edge, Set.sdiff_subset_iff, h]
-/
@[simp] lemma deleteEdges_edge {u v : V} {s : Set (Sym2 V)} (h : s(u, v) in s) :
    (edge u v).deleteEdges s = ⊥ := by simp [edge, Set.sdiff_subset_iff, h]

/--
lemma `disjoint_edge` / 引理 `disjoint_edge`

English:
lemma disjoint_edge
  given: {u v : V}
  statement: Disjoint G (edge u v) ↔ ¬G.Adj u v
  proof: by
  rcases eq_or_ne u v with rfl | h
  · simp [edge_self_eq_bot]
  simp [← disjoint_edgeSet, edgeSet_edge_of_ne h]

中文:
引理 disjoint_edge
  条件: {u v : V}
  结论: Disjoint G (edge u v) ↔ ¬G.伴随 u v
  证明: by
  rcases eq_or_ne u v with rfl | h
  · simp [edge_self_eq_bot]
  simp [← disjoint_edgeSet, edgeSet_edge_of_ne h]

Depends on / 依赖: disjoint_edgeSet, edgeSet_edge_of_ne, edge_self_eq_bot, eq_or_ne
-/
lemma disjoint_edge {u v : V} : Disjoint G (edge u v) ↔ ¬G.Adj u v := by
  rcases eq_or_ne u v with rfl | h
  · simp [edge_self_eq_bot]
  simp [← disjoint_edgeSet, edgeSet_edge_of_ne h]

/--
lemma `sdiff_edge` / 引理 `sdiff_edge`

English:
lemma sdiff_edge
  given: {u v : V} (h : ¬G.Adj u v)
  statement: G \ edge u v = G
  proof: by
  simp [disjoint_edge, h]

中文:
引理 sdiff_edge
  条件: {u v : V} (h : ¬G.伴随 u v)
  结论: G \ edge u v = G
  证明: by
  simp [disjoint_edge, h]

Depends on / 依赖: disjoint_edge
-/
lemma sdiff_edge {u v : V} (h : ¬G.Adj u v) : G \ edge u v = G := by
  simp [disjoint_edge, h]

/--
theorem `biSup_fromEdgeSet_singleton_eq` / 定理 `biSup_fromEdgeSet_singleton_eq`

English:
theorem biSup_fromEdgeSet_singleton_eq
  statement: ⨆ e in G.edgeSet, fromEdgeSet {e} = G
  proof: by
  simp_rw [← edgeSet_inj, ← iSup_subtype'', edgeSet_iSup, edgeSet_fromEdgeSet, ← Set.iUnion_sdiff,
    Set.iUnion_coe_set, Set.biUnion_of_singleton]
.sdiff_eq_left exact Set.disjoint_left.mpr G.edgeSet_subset_compl_diagSet

中文:
定理 biSup_fromEdgeSet_singleton_eq
  结论: ⨆ e in G.edgeSet, fromEdgeSet {e} = G
  证明: by
  simp_rw [← edgeSet_inj, ← iSup_subtype'', edgeSet_iSup, edgeSet_fromEdgeSet, ← Set.iUnion_sdiff,
    Set.iUnion_coe_set, Set.biUnion_of_singleton]
.sdiff_eq_left exact Set.disjoint_left.mpr G.edgeSet_subset_compl_diagSet

Depends on / 依赖: G.edgeSet_subset_compl_diagSet, Set.biUnion_of_singleton, Set.disjoint_left.mpr, Set.iUnion_coe_set, Set.iUnion_sdiff, biUnion_of_singleton, disjoint_left, edgeSet_fromEdgeSet, edgeSet_iSup, edgeSet_inj, edgeSet_subset_compl_diagSet, iSup_subtype, iUnion_coe_set, iUnion_sdiff, sdiff_eq_left, simp_rw
-/
theorem biSup_fromEdgeSet_singleton_eq : ⨆ e in G.edgeSet, fromEdgeSet {e} = G := by
  simp_rw [← edgeSet_inj, ← iSup_subtype'', edgeSet_iSup, edgeSet_fromEdgeSet, ← Set.iUnion_sdiff,
    Set.iUnion_coe_set, Set.biUnion_of_singleton]
.sdiff_eq_left exact Set.disjoint_left.mpr G.edgeSet_subset_compl_diagSet

/--
theorem `sSup_edge_eq` / 定理 `sSup_edge_eq`

English:
theorem sSup_edge_eq
  statement: sSup { edge u v | (u : V) (v : V) (_ : G.Adj u v) } = G
  proof: by
  refine .trans ?_ G.biSup_fromEdgeSet_singleton_eq
  simp_rw [edge, ← iSup_subtype'', iSup, Set.range, Subtype.exists, Sym2.exists, mem_edgeSet]

中文:
定理 sSup_edge_eq
  结论: sSup { edge u v | (u : V) (v : V) (_ : G.伴随 u v) } = G
  证明: by
  refine .trans ?_ G.biSup_fromEdgeSet_singleton_eq
  simp_rw [edge, ← iSup_subtype'', iSup, Set.range, Subtype.exists, Sym2.exists, mem_edgeSet]

Depends on / 依赖: G.biSup_fromEdgeSet_singleton_eq, Set.range, Subtype, Subtype.exists, Sym2.exists, biSup_fromEdgeSet_singleton_eq, iSup_subtype, mem_edgeSet, simp_rw
-/
theorem sSup_edge_eq : sSup { edge u v | (u : V) (v : V) (_ : G.Adj u v) } = G := by
  refine .trans ?_ G.biSup_fromEdgeSet_singleton_eq
  simp_rw [edge, ← iSup_subtype'', iSup, Set.range, Subtype.exists, Sym2.exists, mem_edgeSet]

/--
theorem `Subgraph.spanningCoe_sup_edge_le` / 定理 `Subgraph.spanningCoe_sup_edge_le`

English:
theorem Subgraph.spanningCoe_sup_edge_le
  given: {H : Subgraph (G ⊔ edge s t)} (h : ¬ H.Adj s t)
  proof: by
  intro v w hvw
  grind [adj_congr_of_sym2]

中文:
定理 子图.spanningCoe_sup_edge_le
  条件: {H : 子图 (G ⊔ edge s t)} (h : ¬ H.伴随 s t)
  证明: by
  intro v w hvw
  grind [adj_congr_of_sym2]

Depends on / 依赖: adj_congr_of_sym2
-/
theorem Subgraph.spanningCoe_sup_edge_le {H : Subgraph (G ⊔ edge s t)} (h : ¬ H.Adj s t) :
    H.spanningCoe <= G := by
  intro v w hvw
  grind [adj_congr_of_sym2]

variable [Fintype V] [DecidableRel G.Adj]

variable [DecidableEq V] in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Fintype (edge s t).edgeSet
  body: by rw [edge]; infer_instance

中文:
实例 :
  签名: 有限类型 (edge s t).edgeSet
  定义体: by rw [edge]; infer_instance

Depends on / 依赖: infer_instance
-/
instance : Fintype (edge s t).edgeSet := by rw [edge]; infer_instance

/--
theorem `edgeFinset_sup_edge` / 定理 `edgeFinset_sup_edge`

English:
theorem edgeFinset_sup_edge
  given: [Fintype (edgeSet (G ⊔ edge s t))] (hn : ¬G.Adj s t) (h : s != t)
  proof: by
  classical
  simp [edgeFinset, edgeSet_edge_of_ne h]

中文:
定理 edgeFinset_sup_edge
  条件: [有限类型 (edgeSet (G ⊔ edge s t))] (hn : ¬G.伴随 s t) (h : s != t)
  证明: by
  classical
  simp [edgeFinset, edgeSet_edge_of_ne h]

Depends on / 依赖: classical, edgeFinset, edgeSet_edge_of_ne
-/
theorem edgeFinset_sup_edge [Fintype (edgeSet (G ⊔ edge s t))] (hn : ¬G.Adj s t) (h : s != t) :
    (G ⊔ edge s t).edgeFinset = G.edgeFinset.cons s(s, t) (by simp_all) := by
  classical
  simp [edgeFinset, edgeSet_edge_of_ne h]

/--
theorem `card_edgeFinset_sup_edge` / 定理 `card_edgeFinset_sup_edge`

English:
theorem card_edgeFinset_sup_edge
  given: [Fintype (edgeSet (G ⊔ edge s t))] (hn : ¬G.Adj s t) (h : s != t)
  proof: by
  rw [G.edgeFinset_sup_edge hn h]; rw [card_cons]

中文:
定理 card_edgeFinset_sup_edge
  条件: [有限类型 (edgeSet (G ⊔ edge s t))] (hn : ¬G.伴随 s t) (h : s != t)
  证明: by
  rw [G.edgeFinset_sup_edge hn h]; rw [card_cons]

Depends on / 依赖: G.edgeFinset_sup_edge, card_cons, edgeFinset_sup_edge
-/
theorem card_edgeFinset_sup_edge [Fintype (edgeSet (G ⊔ edge s t))] (hn : ¬G.Adj s t) (h : s != t) :
    #(G ⊔ edge s t).edgeFinset = #G.edgeFinset + 1 := by
  rw [G.edgeFinset_sup_edge hn h]; rw [card_cons]

end AddEdge

end SimpleGraph
