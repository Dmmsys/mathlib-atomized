/-
Copyright (c) 2022 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Bipartite
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.EdgeConnectivity
public import Mathlib.Combinatorics.SimpleGraph.CycleGraph
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
public import Mathlib.Combinatorics.SimpleGraph.Metric

/-!

# Acyclic graphs and trees

This module introduces *acyclic graphs* (a.k.a. *forests*) and *trees*.

## Main definitions

* `SimpleGraph.IsAcyclic` is a predicate for a graph having no cyclic walks.
* `SimpleGraph.IsTree` is a predicate for a graph being a tree (a connected acyclic graph).

## Main statements

* `SimpleGraph.isAcyclic_iff_path_unique` characterizes acyclicity in terms of uniqueness of
  paths between pairs of vertices.
* `SimpleGraph.isAcyclic_iff_forall_edge_isBridge` characterizes acyclicity in terms of every
  edge being a bridge edge.
* `SimpleGraph.isTree_iff_existsUnique_path` characterizes trees in terms of existence and
  uniqueness of paths between pairs of vertices from a nonempty vertex type.

## References

The structure of the proofs for `SimpleGraph.IsAcyclic` and `SimpleGraph.IsTree`, including
supporting lemmas about `SimpleGraph.IsBridge`, generally follows the high-level description
for these theorems for multigraphs from [Chou1994].

## Tags

acyclic graphs, trees
-/

@[expose] public section


namespace SimpleGraph

open Walk

variable {V V' : Type*} (G : SimpleGraph V) (G' : SimpleGraph V')

/--
Definition of `IsAcyclic` / `IsAcyclic` 的定义

English:
definition IsAcyclic
  signature: : Prop
  body: forall ⦃v : V⦄ (c : G.Walk v v), ¬c.IsCycle

中文:
定义 IsAcyclic
  签名: : 命题
  定义体: forall ⦃v : V⦄ (c : G.Walk v v), ¬c.IsCycle

Depends on / 依赖: G.Walk, IsCycle, c.IsCycle
-/
def IsAcyclic : Prop := forall ⦃v : V⦄ (c : G.Walk v v), ¬c.IsCycle

/-- A *tree* is a connected acyclic graph. -/
@[mk_iff]
/--
Definition of `IsTree` / `IsTree` 的定义

English:
structure IsTree
  parameters: : Prop extends
  axioms and operations (1):
    - isAcyclic : G.IsAcyclic

中文:
结构 是树
  参数: : 命题 extends
  公理与运算 (1 个):
    - isAcyclic : G.IsAcyclic
-/
structure IsTree : Prop extends
  connected : G.Connected where
  /-- A tree is acyclic. -/
  isAcyclic : G.IsAcyclic

@[deprecated (since := "2026-03-18")] alias IsTree.isConnected := IsTree.connected
@[deprecated (since := "2026-03-18")] alias IsTree.IsAcyclic := IsTree.isAcyclic

variable {G G'}

/--
lemma `isAcyclic_bot` / 引理 `isAcyclic_bot`

English:
lemma isAcyclic_bot
  statement: IsAcyclic (⊥ : SimpleGraph V)
  proof: fun _a _w hw => hw.ne_bot rfl

中文:
引理 isAcyclic_bot
  结论: IsAcyclic (⊥ : 简单图 V)
  证明: fun _a _w hw => hw.ne_bot rfl
-/
@[simp] lemma isAcyclic_bot : IsAcyclic (⊥ : SimpleGraph V) := fun _a _w hw => hw.ne_bot rfl

/--
lemma `IsAcyclic.comap` / 引理 `IsAcyclic.comap`

English:
lemma IsAcyclic.comap
  given: (f : G ->g G') (hinj : Function.Injective f) (h : G'.IsAcyclic)
  proof: fun _ _ => mt (.map hinj) (h _)

中文:
引理 IsAcyclic.comap
  条件: (f : G ->g G') (hinj : 函数.单射 f) (h : G'.IsAcyclic)
  证明: fun _ _ => mt (.map hinj) (h _)
-/
lemma IsAcyclic.comap (f : G ->g G') (hinj : Function.Injective f) (h : G'.IsAcyclic) :
    G.IsAcyclic :=
  fun _ _ => mt (.map hinj) (h _)

/--
lemma `IsAcyclic.embedding` / 引理 `IsAcyclic.embedding`

English:
lemma IsAcyclic.embedding
  given: (f : G ↪g G') (h : G'.IsAcyclic)
  statement: G.IsAcyclic
  proof: h.comap f f.injective

中文:
引理 IsAcyclic.embedding
  条件: (f : G ↪g G') (h : G'.IsAcyclic)
  结论: G.IsAcyclic
  证明: h.comap f f.injective

Depends on / 依赖: f.injective, h.comap, injective
-/
lemma IsAcyclic.embedding (f : G ↪g G') (h : G'.IsAcyclic) : G.IsAcyclic :=
  h.comap f f.injective

/--
lemma `Iso.isAcyclic_iff` / 引理 `Iso.isAcyclic_iff`

English:
lemma Iso.isAcyclic_iff
  given: (f : G ≃g G')
  statement: G.IsAcyclic ↔ G'.IsAcyclic
  proof: ⟨fun h => h.embedding f.symm, fun h => h.embedding f⟩

中文:
引理 同构.isAcyclic_iff
  条件: (f : G ≃g G')
  结论: G.IsAcyclic ↔ G'.IsAcyclic
  证明: ⟨fun h => h.embedding f.symm, fun h => h.embedding f⟩

Depends on / 依赖: embedding, f.symm, h.embedding
-/
lemma Iso.isAcyclic_iff (f : G ≃g G') : G.IsAcyclic ↔ G'.IsAcyclic :=
  ⟨fun h => h.embedding f.symm, fun h => h.embedding f⟩

/--
lemma `Iso.isTree_iff` / 引理 `Iso.isTree_iff`

English:
lemma Iso.isTree_iff
  given: (f : G ≃g G')
  statement: G.IsTree ↔ G'.IsTree
  proof: ⟨fun ⟨hc, ha⟩ => ⟨f.connected_iff.mp hc, f.isAcyclic_iff.mp ha⟩,
   fun ⟨hc, ha⟩ => ⟨f.connected_iff.mpr hc, f.isAcyclic_iff.mpr ha⟩⟩

中文:
引理 同构.isTree_iff
  条件: (f : G ≃g G')
  结论: G.是树 ↔ G'.是树
  证明: ⟨fun ⟨hc, ha⟩ => ⟨f.connected_iff.mp hc, f.isAcyclic_iff.mp ha⟩,
   fun ⟨hc, ha⟩ => ⟨f.connected_iff.mpr hc, f.isAcyclic_iff.mpr ha⟩⟩

Depends on / 依赖: connected_iff, f.connected_iff.mp, f.connected_iff.mpr, f.isAcyclic_iff.mp, f.isAcyclic_iff.mpr, isAcyclic_iff
-/
lemma Iso.isTree_iff (f : G ≃g G') : G.IsTree ↔ G'.IsTree :=
  ⟨fun ⟨hc, ha⟩ => ⟨f.connected_iff.mp hc, f.isAcyclic_iff.mp ha⟩,
   fun ⟨hc, ha⟩ => ⟨f.connected_iff.mpr hc, f.isAcyclic_iff.mpr ha⟩⟩

/--
lemma `IsAcyclic.of_map` / 引理 `IsAcyclic.of_map`

English:
lemma IsAcyclic.of_map
  given: (f : V ↪ V') (h : G.map f |>.IsAcyclic)
  statement: G.IsAcyclic
  proof: h.embedding SimpleGraph.Embedding.map ..

.IsAcyclic := lemma IsAcyclic.of_comap (f : V' ↪ V) (h : G.IsAcyclic) : G.comap f
h.embedding SimpleGraph.Embedding.comap ..

中文:
引理 IsAcyclic.of_map
  条件: (f : V ↪ V') (h : G.map f |>.IsAcyclic)
  结论: G.IsAcyclic
  证明: h.embedding SimpleGraph.Embedding.map ..

.IsAcyclic := lemma IsAcyclic.of_comap (f : V' ↪ V) (h : G.IsAcyclic) : G.comap f
h.embedding SimpleGraph.Embedding.comap ..

Depends on / 依赖: Embedding, SimpleGraph, SimpleGraph.Embedding.map, embedding, h.embedding
-/
lemma IsAcyclic.of_map (f : V ↪ V') (h : G.map f |>.IsAcyclic) : G.IsAcyclic :=
h.embedding SimpleGraph.Embedding.map ..

.IsAcyclic := lemma IsAcyclic.of_comap (f : V' ↪ V) (h : G.IsAcyclic) : G.comap f
h.embedding SimpleGraph.Embedding.comap ..

/-- A graph induced from an acyclic graph is acyclic. -/
.IsAcyclic := lemma IsAcyclic.induce (h : G.IsAcyclic) (s : Set V) : G.induce s
  h.of_comap _

/--
lemma `IsAcyclic.subgraph` / 引理 `IsAcyclic.subgraph`

English:
lemma IsAcyclic.subgraph
  given: (h : G.IsAcyclic) (H : G.Subgraph)
  statement: H.coe.IsAcyclic
  proof: h.comap _ H.hom_injective

中文:
引理 IsAcyclic.subgraph
  条件: (h : G.IsAcyclic) (H : G.子图)
  结论: H.coe.IsAcyclic
  证明: h.comap _ H.hom_injective

Depends on / 依赖: H.hom_injective, h.comap, hom_injective
-/
lemma IsAcyclic.subgraph (h : G.IsAcyclic) (H : G.Subgraph) : H.coe.IsAcyclic :=
  h.comap _ H.hom_injective

/--
lemma `IsAcyclic.anti` / 引理 `IsAcyclic.anti`

English:
lemma IsAcyclic.anti
  given: {G' : SimpleGraph V} (hsub : G <= G') (h : G'.IsAcyclic)
  statement: G.IsAcyclic
  proof: h.comap ⟨_, fun h => hsub h⟩ Function.injective_id

中文:
引理 IsAcyclic.anti
  条件: {G' : 简单图 V} (hsub : G <= G') (h : G'.IsAcyclic)
  结论: G.IsAcyclic
  证明: h.comap ⟨_, fun h => hsub h⟩ Function.injective_id

Depends on / 依赖: Function, Function.injective_id, h.comap, injective_id
-/
lemma IsAcyclic.anti {G' : SimpleGraph V} (hsub : G <= G') (h : G'.IsAcyclic) : G.IsAcyclic :=
  h.comap ⟨_, fun h => hsub h⟩ Function.injective_id

/--
lemma `Walk.exists_mem_contains_edges_of_directed` / 引理 `Walk.exists_mem_contains_edges_of_directed`

English:
lemma Walk.exists_mem_contains_edges_of_directed
  statement: (Hs : Set <| SimpleGraph V)
  proof: by
  induction p with
  | nil => exact ⟨hHs.some, hHs.some_mem, by simp⟩
  | @cons u v w h_adj p ih =>
    obtain ⟨H₁, hH₁, ih⟩ := ih
    obtain ⟨H₂, hH₂, h_adj⟩ : exists H₂ in Hs, H₂.Adj u v := h_adj
    obtain ⟨H, hH, h₁, h₂⟩ := h_dir H₁ hH₁ H₂ hH₂
    simpa using ⟨H, hH, (le_iff_adj.mp h₂) _ _ h_adj, fun a ha => edgeSet_mono h₁ (ih a ha)⟩

中文:
引理 途径.存在_mem_contains_edges_of_directed
  结论: (Hs : 集合 <| 简单图 V)
  证明: by
  induction p with
  | nil => exact ⟨hHs.some, hHs.some_mem, by simp⟩
  | @cons u v w h_adj p ih =>
    obtain ⟨H₁, hH₁, ih⟩ := ih
    obtain ⟨H₂, hH₂, h_adj⟩ : exists H₂ in Hs, H₂.Adj u v := h_adj
    obtain ⟨H, hH, h₁, h₂⟩ := h_dir H₁ hH₁ H₂ hH₂
    simpa using ⟨H, hH, (le_iff_adj.mp h₂) _ _ h_adj, fun a ha => edgeSet_mono h₁ (ih a ha)⟩
-/
private lemma Walk.exists_mem_contains_edges_of_directed (Hs : Set <| SimpleGraph V)
    (hHs : Hs.Nonempty) (h_dir : DirectedOn (· <= ·) Hs) {u v : V} (p : (sSup Hs).Walk u v) :
    exists H in Hs, forall e in p.edges, e in H.edgeSet := by
  induction p with
  | nil => exact ⟨hHs.some, hHs.some_mem, by simp⟩
  | @cons u v w h_adj p ih =>
    obtain ⟨H₁, hH₁, ih⟩ := ih
    obtain ⟨H₂, hH₂, h_adj⟩ : exists H₂ in Hs, H₂.Adj u v := h_adj
    obtain ⟨H, hH, h₁, h₂⟩ := h_dir H₁ hH₁ H₂ hH₂
    simpa using ⟨H, hH, (le_iff_adj.mp h₂) _ _ h_adj, fun a ha => edgeSet_mono h₁ (ih a ha)⟩

/--
lemma `isAcyclic_sSup_of_isAcyclic_directedOn` / 引理 `isAcyclic_sSup_of_isAcyclic_directedOn`

English:
lemma isAcyclic_sSup_of_isAcyclic_directedOn
  statement: (Hs : Set <| SimpleGraph V)
  proof: by
  rcases Hs.eq_empty_or_nonempty with rfl | hnemp
  · simp
  · intro u p hp
    obtain ⟨H, hH, hpH⟩ := p.exists_mem_contains_edges_of_directed Hs hnemp h_dir
exact h_acyc H hH (p.transfer H hpH) Walk.IsCycle.transfer hp hpH

中文:
引理 isAcyclic_sSup_of_isAcyclic_directedOn
  结论: (Hs : 集合 <| 简单图 V)
  证明: by
  rcases Hs.eq_empty_or_nonempty with rfl | hnemp
  · simp
  · intro u p hp
    obtain ⟨H, hH, hpH⟩ := p.exists_mem_contains_edges_of_directed Hs hnemp h_dir
exact h_acyc H hH (p.transfer H hpH) Walk.IsCycle.transfer hp hpH

Depends on / 依赖: Hs.eq_empty_or_nonempty, IsCycle, Walk.IsCycle.transfer, eq_empty_or_nonempty, exists_mem_contains_edges_of_directed, h_acyc, h_dir, p.exists_mem_contains_edges_of_directed, p.transfer, transfer
-/
lemma isAcyclic_sSup_of_isAcyclic_directedOn (Hs : Set <| SimpleGraph V)
    (h_acyc : forall H in Hs, H.IsAcyclic) (h_dir : DirectedOn (· <= ·) Hs) : IsAcyclic (sSup Hs) := by
  rcases Hs.eq_empty_or_nonempty with rfl | hnemp
  · simp
  · intro u p hp
    obtain ⟨H, hH, hpH⟩ := p.exists_mem_contains_edges_of_directed Hs hnemp h_dir
exact h_acyc H hH (p.transfer H hpH) Walk.IsCycle.transfer hp hpH

/--
theorem `exists_maximal_isAcyclic_of_le_isAcyclic` / 定理 `exists_maximal_isAcyclic_of_le_isAcyclic`

English:
theorem exists_maximal_isAcyclic_of_le_isAcyclic
  proof: by
  refine zorn_le_nonempty₀ {H | H <= G ∧ H.IsAcyclic} (fun c hcs hc y hy => ?_) _ ⟨hHG, hH⟩
  refine ⟨sSup c, ⟨?_, ?_⟩, fun _ => le_sSup⟩
  · grind [sSup_le_iff]
  · exact isAcyclic_sSup_of_isAcyclic_directedOn c (by grind) hc.directedOn

中文:
定理 存在_maximal_isAcyclic_of_le_isAcyclic
  证明: by
  refine zorn_le_nonempty₀ {H | H <= G ∧ H.IsAcyclic} (fun c hcs hc y hy => ?_) _ ⟨hHG, hH⟩
  refine ⟨sSup c, ⟨?_, ?_⟩, fun _ => le_sSup⟩
  · grind [sSup_le_iff]
  · exact isAcyclic_sSup_of_isAcyclic_directedOn c (by grind) hc.directedOn

Depends on / 依赖: H.IsAcyclic, IsAcyclic, directedOn, hc.directedOn, isAcyclic_sSup_of_isAcyclic_directedOn, le_sSup, sSup_le_iff
-/
theorem exists_maximal_isAcyclic_of_le_isAcyclic
    {H : SimpleGraph V} (hHG : H <= G) (hH : H.IsAcyclic) :
    exists H' : SimpleGraph V, H <= H' ∧ Maximal (fun H => H <= G ∧ H.IsAcyclic) H' := by
  refine zorn_le_nonempty₀ {H | H <= G ∧ H.IsAcyclic} (fun c hcs hc y hy => ?_) _ ⟨hHG, hH⟩
  refine ⟨sSup c, ⟨?_, ?_⟩, fun _ => le_sSup⟩
  · grind [sSup_le_iff]
  · exact isAcyclic_sSup_of_isAcyclic_directedOn c (by grind) hc.directedOn

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `IsAcyclic.isTree_connectedComponent` / 引理 `IsAcyclic.isTree_connectedComponent`

English:
lemma IsAcyclic.isTree_connectedComponent
  given: (h : G.IsAcyclic) (c : G.ConnectedComponent)
  proof: c.connected_toSimpleGraph
isAcyclic := h.comap c.toSimpleGraph_hom by simp [ConnectedComponent.toSimpleGraph_hom]

中文:
引理 IsAcyclic.isTree_connectedComponent
  条件: (h : G.IsAcyclic) (c : G.ConnectedComponent)
  证明: c.connected_toSimpleGraph
isAcyclic := h.comap c.toSimpleGraph_hom by simp [ConnectedComponent.toSimpleGraph_hom]

Depends on / 依赖: c.connected_toSimpleGraph, connected_toSimpleGraph
-/
lemma IsAcyclic.isTree_connectedComponent (h : G.IsAcyclic) (c : G.ConnectedComponent) :
    c.toSimpleGraph.IsTree where
  connected := c.connected_toSimpleGraph
isAcyclic := h.comap c.toSimpleGraph_hom by simp [ConnectedComponent.toSimpleGraph_hom]

/--
theorem `IsAcyclic.of_card_le_two` / 定理 `IsAcyclic.of_card_le_two`

English:
theorem IsAcyclic.of_card_le_two
  given: (h : ENat.card V <= 2)
  statement: G.IsAcyclic
  proof: by
  intro v p hp
  have := hp.three_le_length
have := Nat.cast_le.mp hp.support_nodup.length_le_enatCard.trans h
  rw [List.length_tail]; rw [p.length_support] at this
  lia

中文:
定理 IsAcyclic.of_card_le_two
  条件: (h : E自然数.card V <= 2)
  结论: G.IsAcyclic
  证明: by
  intro v p hp
  have := hp.three_le_length
have := Nat.cast_le.mp hp.support_nodup.length_le_enatCard.trans h
  rw [List.length_tail]; rw [p.length_support] at this
  lia

Depends on / 依赖: List.length_tail, Nat.cast_le.mp, cast_le, hp.support_nodup.length_le_enatCard.trans, hp.three_le_length, length_le_enatCard, length_support, length_tail, p.length_support, support_nodup, three_le_length
-/
theorem IsAcyclic.of_card_le_two (h : ENat.card V <= 2) : G.IsAcyclic := by
  intro v p hp
  have := hp.three_le_length
have := Nat.cast_le.mp hp.support_nodup.length_le_enatCard.trans h
  rw [List.length_tail]; rw [p.length_support] at this
  lia

/--
lemma `IsAcyclic.of_subsingleton` / 引理 `IsAcyclic.of_subsingleton`

English:
lemma IsAcyclic.of_subsingleton
  given: [Subsingleton V] {G : SimpleGraph V}
  statement: G.IsAcyclic
  proof: .of_card_le_two ENat.card_le_one.trans one_le_two

中文:
引理 IsAcyclic.of_subsingleton
  条件: [子单例 V] {G : 简单图 V}
  结论: G.IsAcyclic
  证明: .of_card_le_two ENat.card_le_one.trans one_le_two

Depends on / 依赖: ENat.card_le_one.trans, card_le_one, of_card_le_two, one_le_two
-/
lemma IsAcyclic.of_subsingleton [Subsingleton V] {G : SimpleGraph V} : G.IsAcyclic :=
.of_card_le_two ENat.card_le_one.trans one_le_two

/--
lemma `Subgraph.isAcyclic_coe_bot` / 引理 `Subgraph.isAcyclic_coe_bot`

English:
lemma Subgraph.isAcyclic_coe_bot
  given: (G : SimpleGraph V)
  statement: (⊥ : G.Subgraph).coe.IsAcyclic
  proof: @IsAcyclic.of_subsingleton _ (Set.isEmpty_coe_sort.mpr rfl).instSubsingleton _

中文:
引理 子图.isAcyclic_coe_bot
  条件: (G : 简单图 V)
  结论: (⊥ : G.子图).coe.IsAcyclic
  证明: @IsAcyclic.of_subsingleton _ (Set.isEmpty_coe_sort.mpr rfl).instSubsingleton _

Depends on / 依赖: IsAcyclic, IsAcyclic.of_subsingleton, Set.isEmpty_coe_sort.mpr, instSubsingleton, isEmpty_coe_sort, of_subsingleton
-/
lemma Subgraph.isAcyclic_coe_bot (G : SimpleGraph V) : (⊥ : G.Subgraph).coe.IsAcyclic :=
  @IsAcyclic.of_subsingleton _ (Set.isEmpty_coe_sort.mpr rfl).instSubsingleton _

/--
lemma `IsTree.of_subsingleton` / 引理 `IsTree.of_subsingleton`

English:
lemma IsTree.of_subsingleton
  given: [Nonempty V] [Subsingleton V] {G : SimpleGraph V}
  statement: G.IsTree
  proof: ⟨.of_subsingleton, .of_subsingleton⟩

中文:
引理 是树.of_subsingleton
  条件: [非空 V] [子单例 V] {G : 简单图 V}
  结论: G.是树
  证明: ⟨.of_subsingleton, .of_subsingleton⟩

Depends on / 依赖: of_subsingleton
-/
lemma IsTree.of_subsingleton [Nonempty V] [Subsingleton V] {G : SimpleGraph V} : G.IsTree :=
  ⟨.of_subsingleton, .of_subsingleton⟩

/--
theorem `IsTree.coe_singletonSubgraph` / 定理 `IsTree.coe_singletonSubgraph`

English:
theorem IsTree.coe_singletonSubgraph
  given: (G : SimpleGraph V) (v : V)
  proof: G.singletonSubgraph v
  .of_subsingleton

中文:
定理 是树.coe_singletonSubgraph
  条件: (G : 简单图 V) (v : V)
  证明: G.singletonSubgraph v
  .of_subsingleton

Depends on / 依赖: G.singletonSubgraph, singletonSubgraph
-/
theorem IsTree.coe_singletonSubgraph (G : SimpleGraph V) (v : V) :
.coe.IsTree := G.singletonSubgraph v
  .of_subsingleton

set_option backward.defeqAttrib.useBackward true in
.coe.IsTree := by theorem IsTree.coe_subgraphOfAdj {u v : V} (h : G.Adj u v) : G.subgraphOfAdj h
  refine ⟨Subgraph.subgraphOfAdj_connected h, fun w p hp => ?_⟩
  have : _ = _ := p.adj_snd hp.not_nil
  have : _ = _ := p.adj_penultimate hp.not_nil
  #adaptation_note /-- Before https://github.com/leanprover/lean4/pull/13166
  (replacing grind's canonicalizer with a type-directed normalizer), `grind` closed this goal.
  It is not yet clear whether this is due to defeq abuse in Mathlib or a problem in the new
  canonicalizer; a minimization would help. The original proof was:
  `grind [Sym2.eq_iff, IsCycle.snd_ne_penultimate]` -/
  simp_all
  grind [IsCycle.snd_ne_penultimate]

/--
theorem `isAcyclic_iff_forall_isBridge` / 定理 `isAcyclic_iff_forall_isBridge`

English:
theorem isAcyclic_iff_forall_isBridge
  statement: G.IsAcyclic ↔ forall ⦃e⦄, e in G.edgeSet -> G.IsBridge e where
  proof: isBridge_iff_forall_cycle_notMem he
  mpr hG v c hc := by
obtain ⟨e, he⟩ := c.edges.exists_mem_of_ne_nil by simp [hc.not_nil]
    exact (hG <| c.edges_subset_edgeSet he).notMem_edges_of_isCycle hc he

中文:
定理 isAcyclic_iff_对任意_isBridge
  结论: G.IsAcyclic ↔ 对任意 ⦃e⦄, e in G.edgeSet -> G.IsBridge e where
  证明: isBridge_iff_forall_cycle_notMem he
  mpr hG v c hc := by
obtain ⟨e, he⟩ := c.edges.exists_mem_of_ne_nil by simp [hc.not_nil]
    exact (hG <| c.edges_subset_edgeSet he).notMem_edges_of_isCycle hc he

Depends on / 依赖: isBridge_iff_forall_cycle_notMem
-/
theorem isAcyclic_iff_forall_isBridge : G.IsAcyclic ↔ forall ⦃e⦄, e in G.edgeSet -> G.IsBridge e where
.elim .mpr fun v p hc => hG p hc mp hG e he := isBridge_iff_forall_cycle_notMem he
  mpr hG v c hc := by
obtain ⟨e, he⟩ := c.edges.exists_mem_of_ne_nil by simp [hc.not_nil]
    exact (hG <| c.edges_subset_edgeSet he).notMem_edges_of_isCycle hc he

/--
lemma `isAcyclic_iff_forall_adj_isBridge` / 引理 `isAcyclic_iff_forall_adj_isBridge`

English:
lemma isAcyclic_iff_forall_adj_isBridge
  proof: by
  simp [isAcyclic_iff_forall_isBridge, Sym2.forall]

@[deprecated (since := "2026-06-04")]
alias isAcyclic_iff_forall_edge_isBridge := isAcyclic_iff_forall_isBridge

中文:
引理 isAcyclic_iff_对任意_adj_isBridge
  证明: by
  simp [isAcyclic_iff_forall_isBridge, Sym2.forall]

@[deprecated (since := "2026-06-04")]
alias isAcyclic_iff_forall_edge_isBridge := isAcyclic_iff_forall_isBridge

Depends on / 依赖: Sym2.forall, isAcyclic_iff_forall_isBridge
-/
lemma isAcyclic_iff_forall_adj_isBridge :
    G.IsAcyclic ↔ forall ⦃v w : V⦄, G.Adj v w -> G.IsBridge s(v, w) := by
  simp [isAcyclic_iff_forall_isBridge, Sym2.forall]

@[deprecated (since := "2026-06-04")]
alias isAcyclic_iff_forall_edge_isBridge := isAcyclic_iff_forall_isBridge

/--
theorem `isAcyclic_iff_subsingleton_path` / 定理 `isAcyclic_iff_subsingleton_path`

English:
theorem isAcyclic_iff_subsingleton_path
  statement: G.IsAcyclic ↔ forall u v, Subsingleton (G.Path u v)
  proof: by
  refine ⟨fun h u v => ⟨fun p q => ?_⟩, fun h v c hc => ?_⟩
  · have := p.isPath.exists_isCycle_of_ne q.isPath
    grind [IsAcyclic, Subtype.coe_inj]
.elim ⟨_, hc.isPath_tail⟩ ⟨_, .of_adj .symm⟩ c.adj_snd hc.not_nil · have := h _ v
    grind [length_cons, length_nil, hc.three_le_length, c.length_tail_add_one hc.not_nil]

alias ⟨IsAcyclic.subsingleton_path, _⟩ := isAcyclic_iff_subsingleton_path

@[deprecated IsAcyclic.subsingleton_path (since := "2026-06-30")]

中文:
定理 isAcyclic_iff_subsingleton_path
  结论: G.IsAcyclic ↔ 对任意 u v, 子单例 (G.道路 u v)
  证明: by
  refine ⟨fun h u v => ⟨fun p q => ?_⟩, fun h v c hc => ?_⟩
  · have := p.isPath.exists_isCycle_of_ne q.isPath
    grind [IsAcyclic, Subtype.coe_inj]
.elim ⟨_, hc.isPath_tail⟩ ⟨_, .of_adj .symm⟩ c.adj_snd hc.not_nil · have := h _ v
    grind [length_cons, length_nil, hc.three_le_length, c.length_tail_add_one hc.not_nil]

alias ⟨IsAcyclic.subsingleton_path, _⟩ := isAcyclic_iff_subsingleton_path

@[deprecated IsAcyclic.subsingleton_path (since := "2026-06-30")]

Depends on / 依赖: IsAcyclic, Subtype, Subtype.coe_inj, adj_snd, c.adj_snd, c.length_tail_add_one, coe_inj, exists_isCycle_of_ne, hc.isPath_tail, hc.not_nil, hc.three_le_length, isPath, isPath_tail, length_cons, length_nil, length_tail_add_one, not_nil, of_adj, p.isPath.exists_isCycle_of_ne, q.isPath
-/
theorem isAcyclic_iff_subsingleton_path : G.IsAcyclic ↔ forall u v, Subsingleton (G.Path u v) := by
  refine ⟨fun h u v => ⟨fun p q => ?_⟩, fun h v c hc => ?_⟩
  · have := p.isPath.exists_isCycle_of_ne q.isPath
    grind [IsAcyclic, Subtype.coe_inj]
.elim ⟨_, hc.isPath_tail⟩ ⟨_, .of_adj .symm⟩ c.adj_snd hc.not_nil · have := h _ v
    grind [length_cons, length_nil, hc.three_le_length, c.length_tail_add_one hc.not_nil]

alias ⟨IsAcyclic.subsingleton_path, _⟩ := isAcyclic_iff_subsingleton_path

@[deprecated IsAcyclic.subsingleton_path (since := "2026-06-30")]
/--
theorem `IsAcyclic.path_unique` / 定理 `IsAcyclic.path_unique`

English:
theorem IsAcyclic.path_unique
  given: {G : SimpleGraph V} (h : G.IsAcyclic) {v w : V} (p q : G.Path v w)
  proof: .elim p q h.subsingleton_path v w

@[deprecated isAcyclic_iff_subsingleton_path (since := "2026-06-30")]

中文:
定理 IsAcyclic.path_unique
  条件: {G : 简单图 V} (h : G.IsAcyclic) {v w : V} (p q : G.道路 v w)
  证明: .elim p q h.subsingleton_path v w

@[deprecated isAcyclic_iff_subsingleton_path (since := "2026-06-30")]

Depends on / 依赖: h.subsingleton_path, subsingleton_path
-/
theorem IsAcyclic.path_unique {G : SimpleGraph V} (h : G.IsAcyclic) {v w : V} (p q : G.Path v w) :
    p = q :=
.elim p q h.subsingleton_path v w

@[deprecated isAcyclic_iff_subsingleton_path (since := "2026-06-30")]
/--
theorem `isAcyclic_of_path_unique` / 定理 `isAcyclic_of_path_unique`

English:
theorem isAcyclic_of_path_unique
  given: (h : forall (v w : V) (p q : G.Path v w), p = q)
  statement: G.IsAcyclic
  proof: isAcyclic_iff_subsingleton_path.mpr (⟨h · ·⟩)

@[deprecated isAcyclic_iff_subsingleton_path (since := "2026-06-30")]

中文:
定理 isAcyclic_of_path_unique
  条件: (h : 对任意 (v w : V) (p q : G.道路 v w), p = q)
  结论: G.IsAcyclic
  证明: isAcyclic_iff_subsingleton_path.mpr (⟨h · ·⟩)

@[deprecated isAcyclic_iff_subsingleton_path (since := "2026-06-30")]

Depends on / 依赖: isAcyclic_iff_subsingleton_path, isAcyclic_iff_subsingleton_path.mpr
-/
theorem isAcyclic_of_path_unique (h : forall (v w : V) (p q : G.Path v w), p = q) : G.IsAcyclic :=
  isAcyclic_iff_subsingleton_path.mpr (⟨h · ·⟩)

@[deprecated isAcyclic_iff_subsingleton_path (since := "2026-06-30")]
/--
theorem `isAcyclic_iff_path_unique` / 定理 `isAcyclic_iff_path_unique`

English:
theorem isAcyclic_iff_path_unique
  statement: G.IsAcyclic ↔ forall ⦃v w : V⦄ (p q : G.Path v w), p = q
  proof: isAcyclic_iff_subsingleton_path.trans forall₂_congr fun _ _ => subsingleton_iff

中文:
定理 isAcyclic_iff_path_unique
  结论: G.IsAcyclic ↔ 对任意 ⦃v w : V⦄ (p q : G.道路 v w), p = q
  证明: isAcyclic_iff_subsingleton_path.trans forall₂_congr fun _ _ => subsingleton_iff

Depends on / 依赖: isAcyclic_iff_subsingleton_path, isAcyclic_iff_subsingleton_path.trans, subsingleton_iff
-/
theorem isAcyclic_iff_path_unique : G.IsAcyclic ↔ forall ⦃v w : V⦄ (p q : G.Path v w), p = q :=
isAcyclic_iff_subsingleton_path.trans forall₂_congr fun _ _ => subsingleton_iff

/--
theorem `IsAcyclic.eq_snd_of_adj_start` / 定理 `IsAcyclic.eq_snd_of_adj_start`

English:
theorem IsAcyclic.eq_snd_of_adj_start
  statement: (h : G.IsAcyclic) {u v w : V} {p : G.Walk u v} (hp : p.IsPath)
  proof: by
  classical
.elim ⟨_, hp.takeUntil hsupp⟩ .singleton hadj have := h.subsingleton_path u w
  grind [p.getVert_length_takeUntil hsupp, Path.singleton_coe, length]

中文:
定理 IsAcyclic.eq_snd_of_adj_start
  结论: (h : G.IsAcyclic) {u v w : V} {p : G.途径 u v} (hp : p.是道路)
  证明: by
  classical
.elim ⟨_, hp.takeUntil hsupp⟩ .singleton hadj have := h.subsingleton_path u w
  grind [p.getVert_length_takeUntil hsupp, Path.singleton_coe, length]

Depends on / 依赖: Path.singleton_coe, classical, getVert_length_takeUntil, h.subsingleton_path, hp.takeUntil, length, p.getVert_length_takeUntil, singleton, singleton_coe, subsingleton_path, takeUntil
-/
theorem IsAcyclic.eq_snd_of_adj_start (h : G.IsAcyclic) {u v w : V} {p : G.Walk u v} (hp : p.IsPath)
    (hadj : G.Adj u w) (hsupp : w in p.support) : w = p.snd := by
  classical
.elim ⟨_, hp.takeUntil hsupp⟩ .singleton hadj have := h.subsingleton_path u w
  grind [p.getVert_length_takeUntil hsupp, Path.singleton_coe, length]

/--
theorem `IsAcyclic.eq_penultimate_of_adj_end` / 定理 `IsAcyclic.eq_penultimate_of_adj_end`

English:
theorem IsAcyclic.eq_penultimate_of_adj_end
  statement: (h : G.IsAcyclic) {u v w : V} {p : G.Walk u v}
  proof: by
  rw [← snd_reverse]
  apply h.eq_snd_of_adj_start hp.reverse hadj
  simpa

中文:
定理 IsAcyclic.eq_penultimate_of_adj_end
  结论: (h : G.IsAcyclic) {u v w : V} {p : G.途径 u v}
  证明: by
  rw [← snd_reverse]
  apply h.eq_snd_of_adj_start hp.reverse hadj
  simpa

Depends on / 依赖: eq_snd_of_adj_start, h.eq_snd_of_adj_start, hp.reverse, reverse, snd_reverse
-/
theorem IsAcyclic.eq_penultimate_of_adj_end (h : G.IsAcyclic) {u v w : V} {p : G.Walk u v}
    (hp : p.IsPath) (hadj : G.Adj v w) (hsupp : w in p.support) : w = p.penultimate := by
  rw [← snd_reverse]
  apply h.eq_snd_of_adj_start hp.reverse hadj
  simpa

/--
lemma `IsAcyclic.mem_support_of_ne_mem_support_of_adj_of_isPath` / 引理 `IsAcyclic.mem_support_of_ne_mem_support_of_adj_of_isPath`

English:
lemma IsAcyclic.mem_support_of_ne_mem_support_of_adj_of_isPath
  statement: (hG : G.IsAcyclic) {u v w : V}
  proof: by
  rw [Subtype.mk.inj <| hG.subsingleton_path u v |>.elim ⟨p]; rw [hp⟩ ⟨_]; rw [hq.concat hv hadj.symm⟩]
  exact q.support_subset_support_concat _ q.end_mem_support

中文:
引理 IsAcyclic.mem_support_of_ne_mem_support_of_adj_of_isPath
  结论: (hG : G.IsAcyclic) {u v w : V}
  证明: by
  rw [Subtype.mk.inj <| hG.subsingleton_path u v |>.elim ⟨p]; rw [hp⟩ ⟨_]; rw [hq.concat hv hadj.symm⟩]
  exact q.support_subset_support_concat _ q.end_mem_support

Depends on / 依赖: Subtype, Subtype.mk.inj, concat, end_mem_support, hG.subsingleton_path, hadj.symm, hq.concat, q.end_mem_support, q.support_subset_support_concat, subsingleton_path, support_subset_support_concat
-/
lemma IsAcyclic.mem_support_of_ne_mem_support_of_adj_of_isPath (hG : G.IsAcyclic) {u v w : V}
    {p : G.Walk u v} {q : G.Walk u w} (hp : p.IsPath) (hq : q.IsPath) (hadj : G.Adj v w)
    (hv : v ∉ q.support) : w in p.support := by
  rw [Subtype.mk.inj <| hG.subsingleton_path u v |>.elim ⟨p]; rw [hp⟩ ⟨_]; rw [hq.concat hv hadj.symm⟩]
  exact q.support_subset_support_concat _ q.end_mem_support

/--
lemma `IsAcyclic.ne_mem_support_of_support_of_adj_of_isPath` / 引理 `IsAcyclic.ne_mem_support_of_support_of_adj_of_isPath`

English:
lemma IsAcyclic.ne_mem_support_of_support_of_adj_of_isPath
  statement: (hG : G.IsAcyclic) {u v w : V}
  proof: by
  obtain ⟨p₀, p₁, hp₀, hp₁, happend⟩ := hp.mem_support_iff_exists_append.mp hw
  rw [← Subtype.mk.inj <| hG.subsingleton_path u w |>.elim ⟨p₀]; rw [hp₀⟩ ⟨q]; rw [hq⟩]
  exact fun hxp => (happend ▸ hp).ne_of_mem_support_of_append hadj.symm.ne' hxp
    (p₁.end_mem_support) rfl

中文:
引理 IsAcyclic.ne_mem_support_of_support_of_adj_of_isPath
  结论: (hG : G.IsAcyclic) {u v w : V}
  证明: by
  obtain ⟨p₀, p₁, hp₀, hp₁, happend⟩ := hp.mem_support_iff_exists_append.mp hw
  rw [← Subtype.mk.inj <| hG.subsingleton_path u w |>.elim ⟨p₀]; rw [hp₀⟩ ⟨q]; rw [hq⟩]
  exact fun hxp => (happend ▸ hp).ne_of_mem_support_of_append hadj.symm.ne' hxp
    (p₁.end_mem_support) rfl

Depends on / 依赖: Subtype, Subtype.mk.inj, end_mem_support, hG.subsingleton_path, hadj.symm.ne, happend, hp.mem_support_iff_exists_append.mp, mem_support_iff_exists_append, ne_of_mem_support_of_append, subsingleton_path
-/
lemma IsAcyclic.ne_mem_support_of_support_of_adj_of_isPath (hG : G.IsAcyclic) {u v w : V}
    {p : G.Walk u v} {q : G.Walk u w} (hp : p.IsPath) (hq : q.IsPath) (hadj : G.Adj v w)
    (hw : w in p.support) : v ∉ q.support := by
  obtain ⟨p₀, p₁, hp₀, hp₁, happend⟩ := hp.mem_support_iff_exists_append.mp hw
  rw [← Subtype.mk.inj <| hG.subsingleton_path u w |>.elim ⟨p₀]; rw [hp₀⟩ ⟨q]; rw [hq⟩]
  exact fun hxp => (happend ▸ hp).ne_of_mem_support_of_append hadj.symm.ne' hxp
    (p₁.end_mem_support) rfl

/--
lemma `IsAcyclic.path_concat` / 引理 `IsAcyclic.path_concat`

English:
lemma IsAcyclic.path_concat
  statement: (hG : G.IsAcyclic) {u v w : V} {p : G.Walk u v} {q : G.Walk u w}
  proof: by
  have hw : w ∉ p.support := hG.ne_mem_support_of_support_of_adj_of_isPath hq hp hadj.symm hv
exact Subtype.mk.inj .elim ⟨q, hq⟩ ⟨_, hp.concat hw hadj⟩ hG.subsingleton_path u w

中文:
引理 IsAcyclic.path_concat
  结论: (hG : G.IsAcyclic) {u v w : V} {p : G.途径 u v} {q : G.途径 u w}
  证明: by
  have hw : w ∉ p.support := hG.ne_mem_support_of_support_of_adj_of_isPath hq hp hadj.symm hv
exact Subtype.mk.inj .elim ⟨q, hq⟩ ⟨_, hp.concat hw hadj⟩ hG.subsingleton_path u w

Depends on / 依赖: Subtype, Subtype.mk.inj, concat, hG.ne_mem_support_of_support_of_adj_of_isPath, hG.subsingleton_path, hadj.symm, hp.concat, ne_mem_support_of_support_of_adj_of_isPath, p.support, subsingleton_path, support
-/
lemma IsAcyclic.path_concat (hG : G.IsAcyclic) {u v w : V} {p : G.Walk u v} {q : G.Walk u w}
    (hp : p.IsPath) (hq : q.IsPath) (hadj : G.Adj v w) (hv : v in q.support) :
    q = p.concat hadj := by
  have hw : w ∉ p.support := hG.ne_mem_support_of_support_of_adj_of_isPath hq hp hadj.symm hv
exact Subtype.mk.inj .elim ⟨q, hq⟩ ⟨_, hp.concat hw hadj⟩ hG.subsingleton_path u w

/--
theorem `isTree_iff_existsUnique_path` / 定理 `isTree_iff_existsUnique_path`

English:
theorem isTree_iff_existsUnique_path
  proof: by
  classical
  simp_rw [isTree_iff, isAcyclic_iff_subsingleton_path, subsingleton_iff]
  constructor
  · rintro ⟨hc, hu⟩
    refine ⟨hc.nonempty, ?_⟩
    intro v w
    let q := (hc v w).some.toPath
    use q
    simp only [true_and, Path.isPath]
    intro p hp
    specialize hu v w ⟨p, hp⟩ q
    exact Subtype.ext_iff.mp hu
  · rintro ⟨hV, h⟩
    refine ⟨Connected.mk ?_, ?_⟩
    · intro v w
      obtain ⟨p, _⟩ := h v w
      exact p.reachable
    · rintro v w ⟨p, hp⟩ ⟨q, hq⟩
      simp only [ExistsUnique.unique (h v w) hp hq]

中文:
定理 isTree_iff_存在Unique_path
  证明: by
  classical
  simp_rw [isTree_iff, isAcyclic_iff_subsingleton_path, subsingleton_iff]
  constructor
  · rintro ⟨hc, hu⟩
    refine ⟨hc.nonempty, ?_⟩
    intro v w
    let q := (hc v w).some.toPath
    use q
    simp only [true_and, Path.isPath]
    intro p hp
    specialize hu v w ⟨p, hp⟩ q
    exact Subtype.ext_iff.mp hu
  · rintro ⟨hV, h⟩
    refine ⟨Connected.mk ?_, ?_⟩
    · intro v w
      obtain ⟨p, _⟩ := h v w
      exact p.reachable
    · rintro v w ⟨p, hp⟩ ⟨q, hq⟩
      simp only [ExistsUnique.unique (h v w) hp hq]

Depends on / 依赖: Connected, Connected.mk, ExistsUnique, ExistsUnique.unique, Path.isPath, Subtype, Subtype.ext_iff.mp, classical, ext_iff, hc.nonempty, isAcyclic_iff_subsingleton_path, isPath, isTree_iff, nonempty, p.reachable, reachable, simp_rw, some.toPath, specialize, subsingleton_iff
-/
theorem isTree_iff_existsUnique_path :
    G.IsTree ↔ Nonempty V ∧ forall v w : V, exists! p : G.Walk v w, p.IsPath := by
  classical
  simp_rw [isTree_iff, isAcyclic_iff_subsingleton_path, subsingleton_iff]
  constructor
  · rintro ⟨hc, hu⟩
    refine ⟨hc.nonempty, ?_⟩
    intro v w
    let q := (hc v w).some.toPath
    use q
    simp only [true_and, Path.isPath]
    intro p hp
    specialize hu v w ⟨p, hp⟩ q
    exact Subtype.ext_iff.mp hu
  · rintro ⟨hV, h⟩
    refine ⟨Connected.mk ?_, ?_⟩
    · intro v w
      obtain ⟨p, _⟩ := h v w
      exact p.reachable
    · rintro v w ⟨p, hp⟩ ⟨q, hq⟩
      simp only [ExistsUnique.unique (h v w) hp hq]

/--
lemma `IsTree.existsUnique_path` / 引理 `IsTree.existsUnique_path`

English:
lemma IsTree.existsUnique_path
  given: (hG : G.IsTree)
  statement: forall v w, exists! p : G.Walk v w, p.IsPath
  proof: (isTree_iff_existsUnique_path.1 hG).2

中文:
引理 是树.存在Unique_path
  条件: (hG : G.是树)
  结论: 对任意 v w, 存在! p : G.途径 v w, p.是道路
  证明: (isTree_iff_existsUnique_path.1 hG).2

Depends on / 依赖: isTree_iff_existsUnique_path
-/
lemma IsTree.existsUnique_path (hG : G.IsTree) : forall v w, exists! p : G.Walk v w, p.IsPath :=
  (isTree_iff_existsUnique_path.1 hG).2

/--
theorem `IsAcyclic.isPath_iff_isChain` / 定理 `IsAcyclic.isPath_iff_isChain`

English:
theorem IsAcyclic.isPath_iff_isChain
  given: (hG : G.IsAcyclic) {v w : V} (p : G.Walk v w)
  proof: by
  classical
  refine ⟨fun h => (edges_nodup_of_support_nodup <| p.isPath_def.mp h).isChain, fun h => ?_⟩
  induction p with
  | nil => simp
  | @cons u' v' _ head tail ih =>
    have hcc := List.isChain_cons.mp (edges_cons _ _ ▸ h)
.mpr ⟨ih hcc.2, ?_⟩ refine cons_isPath_iff head tail
    rcases tail.length.eq_zero_or_pos with h' | h'
    · simp [nil_iff_support_eq.mp (length_eq_zero_iff.mp h'), head.ne]
    · by_contra hh
apply hG cons head (tail.takeUntil u' hh)
      simp only [isCycle_def, isTrail_def, edges_cons, List.nodup_cons, ne_eq, reduceCtorEq,
        not_false_eq_true, support_cons, List.tail_cons, true_and]
.support.tail.Nodup := have : cons head (tail.takeUntil u' hh)
.sublist List.IsInfix.sublist tail.isPath_def.mp (ih hcc.2)
          ⟨[], (tail.dropUntil u' hh).support.tail, by simp [← support_append]⟩
      refine ⟨⟨?_, edges_nodup_of_support_nodup this⟩, this⟩
      by_contra hhh
      refine hcc.1 s(u', v') ?_ rfl
      rw [← tail.cons_tail_eq (by simp [not_nil_iff_lt_length]; rw [h'])]
.eq_snd_of_mem_edges (Sym2.eq_swap ▸ hhh) have := IsPath.mk' this
      simp [this, snd_takeUntil head.ne]

中文:
定理 IsAcyclic.isPath_iff_isChain
  条件: (hG : G.IsAcyclic) {v w : V} (p : G.途径 v w)
  证明: by
  classical
  refine ⟨fun h => (edges_nodup_of_support_nodup <| p.isPath_def.mp h).isChain, fun h => ?_⟩
  induction p with
  | nil => simp
  | @cons u' v' _ head tail ih =>
    have hcc := List.isChain_cons.mp (edges_cons _ _ ▸ h)
.mpr ⟨ih hcc.2, ?_⟩ refine cons_isPath_iff head tail
    rcases tail.length.eq_zero_or_pos with h' | h'
    · simp [nil_iff_support_eq.mp (length_eq_zero_iff.mp h'), head.ne]
    · by_contra hh
apply hG cons head (tail.takeUntil u' hh)
      simp only [isCycle_def, isTrail_def, edges_cons, List.nodup_cons, ne_eq, reduceCtorEq,
        not_false_eq_true, support_cons, List.tail_cons, true_and]
.support.tail.Nodup := have : cons head (tail.takeUntil u' hh)
.sublist List.IsInfix.sublist tail.isPath_def.mp (ih hcc.2)
          ⟨[], (tail.dropUntil u' hh).support.tail, by simp [← support_append]⟩
      refine ⟨⟨?_, edges_nodup_of_support_nodup this⟩, this⟩
      by_contra hhh
      refine hcc.1 s(u', v') ?_ rfl
      rw [← tail.cons_tail_eq (by simp [not_nil_iff_lt_length]; rw [h'])]
.eq_snd_of_mem_edges (Sym2.eq_swap ▸ hhh) have := IsPath.mk' this
      simp [this, snd_takeUntil head.ne]

Depends on / 依赖: List.isChain_cons.mp, List.n, classical, cons_isPath_iff, edges_cons, edges_nodup_of_support_nodup, eq_zero_or_pos, head.ne, isChain, isChain_cons, isCycle_def, isPath_def, isTrail_def, length, length_eq_zero_iff, length_eq_zero_iff.mp, nil_iff_support_eq, nil_iff_support_eq.mp, p.isPath_def.mp, tail.length.eq_zero_or_pos
-/
theorem IsAcyclic.isPath_iff_isChain (hG : G.IsAcyclic) {v w : V} (p : G.Walk v w) :
     p.IsPath ↔ List.IsChain (· != ·) p.edges := by
  classical
  refine ⟨fun h => (edges_nodup_of_support_nodup <| p.isPath_def.mp h).isChain, fun h => ?_⟩
  induction p with
  | nil => simp
  | @cons u' v' _ head tail ih =>
    have hcc := List.isChain_cons.mp (edges_cons _ _ ▸ h)
.mpr ⟨ih hcc.2, ?_⟩ refine cons_isPath_iff head tail
    rcases tail.length.eq_zero_or_pos with h' | h'
    · simp [nil_iff_support_eq.mp (length_eq_zero_iff.mp h'), head.ne]
    · by_contra hh
apply hG cons head (tail.takeUntil u' hh)
      simp only [isCycle_def, isTrail_def, edges_cons, List.nodup_cons, ne_eq, reduceCtorEq,
        not_false_eq_true, support_cons, List.tail_cons, true_and]
.support.tail.Nodup := have : cons head (tail.takeUntil u' hh)
.sublist List.IsInfix.sublist tail.isPath_def.mp (ih hcc.2)
          ⟨[], (tail.dropUntil u' hh).support.tail, by simp [← support_append]⟩
      refine ⟨⟨?_, edges_nodup_of_support_nodup this⟩, this⟩
      by_contra hhh
      refine hcc.1 s(u', v') ?_ rfl
      rw [← tail.cons_tail_eq (by simp [not_nil_iff_lt_length]; rw [h'])]
.eq_snd_of_mem_edges (Sym2.eq_swap ▸ hhh) have := IsPath.mk' this
      simp [this, snd_takeUntil head.ne]

/--
theorem `IsAcyclic.isPath_iff_isTrail` / 定理 `IsAcyclic.isPath_iff_isTrail`

English:
theorem IsAcyclic.isPath_iff_isTrail
  given: (hG : G.IsAcyclic) {v w : V} (p : G.Walk v w)
  proof: .mpr .isChain⟩ p.isTrail_def.mp h ⟨IsPath.isTrail, fun h => hG.isPath_iff_isChain p

中文:
定理 IsAcyclic.isPath_iff_isTrail
  条件: (hG : G.IsAcyclic) {v w : V} (p : G.途径 v w)
  证明: .mpr .isChain⟩ p.isTrail_def.mp h ⟨IsPath.isTrail, fun h => hG.isPath_iff_isChain p

Depends on / 依赖: IsPath, IsPath.isTrail, hG.isPath_iff_isChain, isChain, isPath_iff_isChain, isTrail, isTrail_def, p.isTrail_def.mp
-/
theorem IsAcyclic.isPath_iff_isTrail (hG : G.IsAcyclic) {v w : V} (p : G.Walk v w) :
    p.IsPath ↔ p.IsTrail :=
.mpr .isChain⟩ p.isTrail_def.mp h ⟨IsPath.isTrail, fun h => hG.isPath_iff_isChain p

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `IsTree.card_edgeFinset` / 引理 `IsTree.card_edgeFinset`

English:
lemma IsTree.card_edgeFinset
  given: [Fintype V] [Fintype G.edgeSet] (hG : G.IsTree)
  proof: by
  have := hG.connected.nonempty
  inhabit V
  classical
  have : Finset.card ({default} : Finset V)ᶜ + 1 = Fintype.card V := by
    rw [Finset.card_compl]; rw [Finset.card_singleton]; rw [Nat.sub_add_cancel Fintype.card_pos]
  rw [← this]; rw [add_left_inj]
  choose f hf hf' using (hG.existsUnique_path · default)
refine Eq.symm Finset.card_bij
          (fun w hw => ((f w).firstDart <| ?notNil).edge)
          (fun a ha => ?memEdges) ?inj ?surj
  case notNil => exact not_nil_of_ne (by simpa using hw)
  case memEdges => simp
  case inj =>
    intro a ha b hb h
    wlog h' : (f a).length <= (f b).length generalizing a b
    · exact Eq.symm (this _ hb _ ha h.symm (le_of_not_ge h'))
    rw [dart_edge_eq_iff] at h
    obtain (h | h) := h
    · exact (congrArg (·.fst) h)
    · have h1 : ((f a).firstDart <| not_nil_of_ne (by simpa using ha)).snd = b :=
        congrArg (·.snd) h
      have h3 := congrArg length (hf' _ ((f _).tail.copy h1 rfl) ?_)
      · rw [length_copy, ← add_left_inj 1,
          length_tail_add_one (not_nil_of_ne (by simpa using ha))] at h3
        lia
      · simp only [isPath_copy]
        exact (hf _).tail
  case surj =>
    simp only [mem_edgeFinset, Finset.mem_compl, Finset.mem_singleton, Sym2.forall, mem_edgeSet]
    intro x y h
    wlog h' : (f x).length <= (f y).length generalizing x y
    · rw [Sym2.eq_swap]
      exact this y x h.symm (le_of_not_ge h')
refine ⟨y, ?_, dart_edge_eq_mk'_iff.2 Or.inr ?_⟩
    · rintro rfl
      rw [← hf' _ nil IsPath.nil]; rw [length_nil]; rw [← hf' _ (.cons h .nil) (IsPath.nil.cons <| by simpa using h.ne)]; rw [length_cons]; rw [length_nil] at h'
      simp at h'
    rw [← hf' _ (.cons h.symm (f x)) ((cons_isPath_iff _ _).2 ⟨hf _]; rw [fun hy => ?contra⟩)]
    · simp
    case contra =>
      suffices (f x).takeUntil y hy = .cons h .nil by
        rw [← take_spec _ hy] at h'
        simp [this, hf' _ _ ((hf _).dropUntil hy)] at h'
      refine (hG.existsUnique_path _ _).unique ((hf _).takeUntil _) ?_
      simp [h.ne]

中文:
引理 是树.card_edgeFinset
  条件: [有限类型 V] [有限类型 G.edgeSet] (hG : G.是树)
  证明: by
  have := hG.connected.nonempty
  inhabit V
  classical
  have : Finset.card ({default} : Finset V)ᶜ + 1 = Fintype.card V := by
    rw [Finset.card_compl]; rw [Finset.card_singleton]; rw [Nat.sub_add_cancel Fintype.card_pos]
  rw [← this]; rw [add_left_inj]
  choose f hf hf' using (hG.existsUnique_path · default)
refine Eq.symm Finset.card_bij
          (fun w hw => ((f w).firstDart <| ?notNil).edge)
          (fun a ha => ?memEdges) ?inj ?surj
  case notNil => exact not_nil_of_ne (by simpa using hw)
  case memEdges => simp
  case inj =>
    intro a ha b hb h
    wlog h' : (f a).length <= (f b).length generalizing a b
    · exact Eq.symm (this _ hb _ ha h.symm (le_of_not_ge h'))
    rw [dart_edge_eq_iff] at h
    obtain (h | h) := h
    · exact (congrArg (·.fst) h)
    · have h1 : ((f a).firstDart <| not_nil_of_ne (by simpa using ha)).snd = b :=
        congrArg (·.snd) h
      have h3 := congrArg length (hf' _ ((f _).tail.copy h1 rfl) ?_)
      · rw [length_copy, ← add_left_inj 1,
          length_tail_add_one (not_nil_of_ne (by simpa using ha))] at h3
        lia
      · simp only [isPath_copy]
        exact (hf _).tail
  case surj =>
    simp only [mem_edgeFinset, Finset.mem_compl, Finset.mem_singleton, Sym2.forall, mem_edgeSet]
    intro x y h
    wlog h' : (f x).length <= (f y).length generalizing x y
    · rw [Sym2.eq_swap]
      exact this y x h.symm (le_of_not_ge h')
refine ⟨y, ?_, dart_edge_eq_mk'_iff.2 Or.inr ?_⟩
    · rintro rfl
      rw [← hf' _ nil IsPath.nil]; rw [length_nil]; rw [← hf' _ (.cons h .nil) (IsPath.nil.cons <| by simpa using h.ne)]; rw [length_cons]; rw [length_nil] at h'
      simp at h'
    rw [← hf' _ (.cons h.symm (f x)) ((cons_isPath_iff _ _).2 ⟨hf _]; rw [fun hy => ?contra⟩)]
    · simp
    case contra =>
      suffices (f x).takeUntil y hy = .cons h .nil by
        rw [← take_spec _ hy] at h'
        simp [this, hf' _ _ ((hf _).dropUntil hy)] at h'
      refine (hG.existsUnique_path _ _).unique ((hf _).takeUntil _) ?_
      simp [h.ne]

Depends on / 依赖: Eq.symm, Finset, Finset.card, Finset.card_bij, Finset.card_compl, Finset.card_singleton, Fintype, Fintype.card, Fintype.card_pos, Nat.sub_add_cancel, add_left_inj, card_bij, card_compl, card_pos, card_singleton, classical, connected, existsUnique_path, firstDart, hG.connected.nonempty
-/
lemma IsTree.card_edgeFinset [Fintype V] [Fintype G.edgeSet] (hG : G.IsTree) :
    Finset.card G.edgeFinset + 1 = Fintype.card V := by
  have := hG.connected.nonempty
  inhabit V
  classical
  have : Finset.card ({default} : Finset V)ᶜ + 1 = Fintype.card V := by
    rw [Finset.card_compl]; rw [Finset.card_singleton]; rw [Nat.sub_add_cancel Fintype.card_pos]
  rw [← this]; rw [add_left_inj]
  choose f hf hf' using (hG.existsUnique_path · default)
refine Eq.symm Finset.card_bij
          (fun w hw => ((f w).firstDart <| ?notNil).edge)
          (fun a ha => ?memEdges) ?inj ?surj
  case notNil => exact not_nil_of_ne (by simpa using hw)
  case memEdges => simp
  case inj =>
    intro a ha b hb h
    wlog h' : (f a).length <= (f b).length generalizing a b
    · exact Eq.symm (this _ hb _ ha h.symm (le_of_not_ge h'))
    rw [dart_edge_eq_iff] at h
    obtain (h | h) := h
    · exact (congrArg (·.fst) h)
    · have h1 : ((f a).firstDart <| not_nil_of_ne (by simpa using ha)).snd = b :=
        congrArg (·.snd) h
      have h3 := congrArg length (hf' _ ((f _).tail.copy h1 rfl) ?_)
      · rw [length_copy, ← add_left_inj 1,
          length_tail_add_one (not_nil_of_ne (by simpa using ha))] at h3
        lia
      · simp only [isPath_copy]
        exact (hf _).tail
  case surj =>
    simp only [mem_edgeFinset, Finset.mem_compl, Finset.mem_singleton, Sym2.forall, mem_edgeSet]
    intro x y h
    wlog h' : (f x).length <= (f y).length generalizing x y
    · rw [Sym2.eq_swap]
      exact this y x h.symm (le_of_not_ge h')
refine ⟨y, ?_, dart_edge_eq_mk'_iff.2 Or.inr ?_⟩
    · rintro rfl
      rw [← hf' _ nil IsPath.nil]; rw [length_nil]; rw [← hf' _ (.cons h .nil) (IsPath.nil.cons <| by simpa using h.ne)]; rw [length_cons]; rw [length_nil] at h'
      simp at h'
    rw [← hf' _ (.cons h.symm (f x)) ((cons_isPath_iff _ _).2 ⟨hf _]; rw [fun hy => ?contra⟩)]
    · simp
    case contra =>
      suffices (f x).takeUntil y hy = .cons h .nil by
        rw [← take_spec _ hy] at h'
        simp [this, hf' _ _ ((hf _).dropUntil hy)] at h'
      refine (hG.existsUnique_path _ _).unique ((hf _).takeUntil _) ?_
      simp [h.ne]

/--
lemma `isTree_of_minimal_connected` / 引理 `isTree_of_minimal_connected`

English:
lemma isTree_of_minimal_connected
  given: (h : Minimal Connected G)
  statement: IsTree G
  proof: by
  rw [isTree_iff]; rw [and_iff_right h.prop]; rw [isAcyclic_iff_forall_adj_isBridge]
  exact fun _ _ _ => by_contra fun hbr => h.not_prop_of_lt
    (by simpa [deleteEdges, ← edgeSet_ssubset_edgeSet])
 h.prop.connected_delete_edge_of_not_isBridge hbr

中文:
引理 isTree_of_minimal_connected
  条件: (h : 极小 连通 G)
  结论: 是树 G
  证明: by
  rw [isTree_iff]; rw [and_iff_right h.prop]; rw [isAcyclic_iff_forall_adj_isBridge]
  exact fun _ _ _ => by_contra fun hbr => h.not_prop_of_lt
    (by simpa [deleteEdges, ← edgeSet_ssubset_edgeSet])
 h.prop.connected_delete_edge_of_not_isBridge hbr

Depends on / 依赖: and_iff_right, connected_delete_edge_of_not_isBridge, deleteEdges, edgeSet_ssubset_edgeSet, h.not_prop_of_lt, h.prop, h.prop.connected_delete_edge_of_not_isBridge, isAcyclic_iff_forall_adj_isBridge, isTree_iff, not_prop_of_lt
-/
lemma isTree_of_minimal_connected (h : Minimal Connected G) : IsTree G := by
  rw [isTree_iff]; rw [and_iff_right h.prop]; rw [isAcyclic_iff_forall_adj_isBridge]
  exact fun _ _ _ => by_contra fun hbr => h.not_prop_of_lt
    (by simpa [deleteEdges, ← edgeSet_ssubset_edgeSet])
 h.prop.connected_delete_edge_of_not_isBridge hbr

set_option backward.isDefEq.respectTransparency false in
/--
lemma `isTree_iff_minimal_connected` / 引理 `isTree_iff_minimal_connected`

English:
lemma isTree_iff_minimal_connected
  statement: IsTree G ↔ Minimal Connected G
  proof: by
  refine ⟨fun htree => ⟨htree.connected, fun G' h' hle u v hadj => ?_⟩, isTree_of_minimal_connected⟩
  have ⟨p, hp⟩ := h'.exists_isPath u v
have := congrArg Walk.edges congrArg Subtype.val
.elim ⟨p.mapLe hle, hp.mapLe hle⟩ Path.singleton hadj htree.isAcyclic.subsingleton_path u v
  simp only [edges_map, Hom.coe_ofLE, Sym2.map_id, List.map_id_fun, id_eq] at this
  simp [this, p.adj_of_mem_edges]

中文:
引理 isTree_iff_minimal_connected
  结论: 是树 G ↔ 极小 连通 G
  证明: by
  refine ⟨fun htree => ⟨htree.connected, fun G' h' hle u v hadj => ?_⟩, isTree_of_minimal_connected⟩
  have ⟨p, hp⟩ := h'.exists_isPath u v
have := congrArg Walk.edges congrArg Subtype.val
.elim ⟨p.mapLe hle, hp.mapLe hle⟩ Path.singleton hadj htree.isAcyclic.subsingleton_path u v
  simp only [edges_map, Hom.coe_ofLE, Sym2.map_id, List.map_id_fun, id_eq] at this
  simp [this, p.adj_of_mem_edges]

Depends on / 依赖: Hom.coe_ofLE, List.map_id_fun, Path.singleton, Subtype, Subtype.val, Sym2.map_id, Walk.edges, adj_of_mem_edges, coe_ofLE, connected, edges_map, exists_isPath, hp.mapLe, htree.connected, htree.isAcyclic.subsingleton_path, id_eq, isAcyclic, isTree_of_minimal_connected, map_id, map_id_fun
-/
lemma isTree_iff_minimal_connected : IsTree G ↔ Minimal Connected G := by
  refine ⟨fun htree => ⟨htree.connected, fun G' h' hle u v hadj => ?_⟩, isTree_of_minimal_connected⟩
  have ⟨p, hp⟩ := h'.exists_isPath u v
have := congrArg Walk.edges congrArg Subtype.val
.elim ⟨p.mapLe hle, hp.mapLe hle⟩ Path.singleton hadj htree.isAcyclic.subsingleton_path u v
  simp only [edges_map, Hom.coe_ofLE, Sym2.map_id, List.map_id_fun, id_eq] at this
  simp [this, p.adj_of_mem_edges]

/--
theorem `IsAcyclic.sup_edge_of_not_reachable` / 定理 `IsAcyclic.sup_edge_of_not_reachable`

English:
theorem IsAcyclic.sup_edge_of_not_reachable
  statement: {u v : V} (hnreach : ¬G.Reachable u v)
  proof: by
  grind [isAcyclic_iff_forall_isBridge, IsBridge.sup_edge_of_not_reachable_of_isBridge,
    edgeSet_sup, edgeSet_edge, IsBridge.of_not_reachable, isBridge_sup_edge]

@[deprecated (since := "2026-03-18")]
alias IsAcyclic.isAcyclic_sup_fromEdgeSet_of_not_reachable := IsAcyclic.sup_edge_of_not_reachable

中文:
定理 IsAcyclic.sup_edge_of_not_reachable
  结论: {u v : V} (hnreach : ¬G.Reachable u v)
  证明: by
  grind [isAcyclic_iff_forall_isBridge, IsBridge.sup_edge_of_not_reachable_of_isBridge,
    edgeSet_sup, edgeSet_edge, IsBridge.of_not_reachable, isBridge_sup_edge]

@[deprecated (since := "2026-03-18")]
alias IsAcyclic.isAcyclic_sup_fromEdgeSet_of_not_reachable := IsAcyclic.sup_edge_of_not_reachable

Depends on / 依赖: IsBridge, IsBridge.of_not_reachable, IsBridge.sup_edge_of_not_reachable_of_isBridge, edgeSet_edge, edgeSet_sup, isAcyclic_iff_forall_isBridge, isBridge_sup_edge, of_not_reachable, sup_edge_of_not_reachable_of_isBridge
-/
theorem IsAcyclic.sup_edge_of_not_reachable {u v : V} (hnreach : ¬G.Reachable u v)
    (hacyc : G.IsAcyclic) : (G ⊔ edge u v).IsAcyclic := by
  grind [isAcyclic_iff_forall_isBridge, IsBridge.sup_edge_of_not_reachable_of_isBridge,
    edgeSet_sup, edgeSet_edge, IsBridge.of_not_reachable, isBridge_sup_edge]

@[deprecated (since := "2026-03-18")]
alias IsAcyclic.isAcyclic_sup_fromEdgeSet_of_not_reachable := IsAcyclic.sup_edge_of_not_reachable

/--
theorem `isAcyclic_add_edge_iff_of_not_reachable` / 定理 `isAcyclic_add_edge_iff_of_not_reachable`

English:
theorem isAcyclic_add_edge_iff_of_not_reachable
  given: (x y : V) (hxy : ¬ G.Reachable x y)
  proof: ⟨.anti le_sup_left, .sup_edge_of_not_reachable hxy⟩

中文:
定理 isAcyclic_add_edge_iff_of_not_reachable
  条件: (x y : V) (hxy : ¬ G.Reachable x y)
  证明: ⟨.anti le_sup_left, .sup_edge_of_not_reachable hxy⟩

Depends on / 依赖: le_sup_left, sup_edge_of_not_reachable
-/
theorem isAcyclic_add_edge_iff_of_not_reachable (x y : V) (hxy : ¬ G.Reachable x y) :
    (G ⊔ edge x y).IsAcyclic ↔ IsAcyclic G :=
  ⟨.anti le_sup_left, .sup_edge_of_not_reachable hxy⟩

/--
theorem `isAcyclic_sup_fromEdgeSet_iff` / 定理 `isAcyclic_sup_fromEdgeSet_iff`

English:
theorem isAcyclic_sup_fromEdgeSet_iff
  given: {u v : V}
  proof: by
  by_cases huv : u = v
  · grind [sup_eq_left, edge_le, Sym2.mem_diagSet, Sym2.mk_isDiag_iff]
  by_cases hadj : G.Adj u v
  · grind [sup_eq_left, edge_le, mem_edgeSet]
refine ⟨?_, fun ⟨hacyc, hreach⟩ => hacyc.sup_edge_of_not_reachable by grind⟩
  refine fun hacyc => ⟨hacyc.anti le_sup_left, fun hreach => False.elim ?_⟩
  refine isAcyclic_iff_forall_isBridge.mp (e := s(u, v)) hacyc (by simp [huv]) ?_
  convert! hreach
  simp [deleteEdges_sup, hadj]

中文:
定理 isAcyclic_sup_fromEdgeSet_iff
  条件: {u v : V}
  证明: by
  by_cases huv : u = v
  · grind [sup_eq_left, edge_le, Sym2.mem_diagSet, Sym2.mk_isDiag_iff]
  by_cases hadj : G.Adj u v
  · grind [sup_eq_left, edge_le, mem_edgeSet]
refine ⟨?_, fun ⟨hacyc, hreach⟩ => hacyc.sup_edge_of_not_reachable by grind⟩
  refine fun hacyc => ⟨hacyc.anti le_sup_left, fun hreach => False.elim ?_⟩
  refine isAcyclic_iff_forall_isBridge.mp (e := s(u, v)) hacyc (by simp [huv]) ?_
  convert! hreach
  simp [deleteEdges_sup, hadj]

Depends on / 依赖: False.elim, G.Adj, Sym2.mem_diagSet, Sym2.mk_isDiag_iff, convert, deleteEdges_sup, edge_le, hacyc.anti, hacyc.sup_edge_of_not_reachable, hreach, isAcyclic_iff_forall_isBridge, isAcyclic_iff_forall_isBridge.mp, le_sup_left, mem_diagSet, mem_edgeSet, mk_isDiag_iff, sup_edge_of_not_reachable, sup_eq_left
-/
theorem isAcyclic_sup_fromEdgeSet_iff {u v : V} :
    (G ⊔ edge u v).IsAcyclic ↔
      G.IsAcyclic ∧ (G.Reachable u v -> u = v ∨ G.Adj u v) := by
  by_cases huv : u = v
  · grind [sup_eq_left, edge_le, Sym2.mem_diagSet, Sym2.mk_isDiag_iff]
  by_cases hadj : G.Adj u v
  · grind [sup_eq_left, edge_le, mem_edgeSet]
refine ⟨?_, fun ⟨hacyc, hreach⟩ => hacyc.sup_edge_of_not_reachable by grind⟩
  refine fun hacyc => ⟨hacyc.anti le_sup_left, fun hreach => False.elim ?_⟩
  refine isAcyclic_iff_forall_isBridge.mp (e := s(u, v)) hacyc (by simp [huv]) ?_
  convert! hreach
  simp [deleteEdges_sup, hadj]

/--
lemma `reachable_eq_of_maximal_isAcyclic` / 引理 `reachable_eq_of_maximal_isAcyclic`

English:
lemma reachable_eq_of_maximal_isAcyclic
  statement: (F : SimpleGraph V)
  proof: by
  ext u v
  refine ⟨.mono h.prop.left, fun ⟨p⟩ => ?_⟩
  by_contra
  let s : F.ConnectedComponent := .mk _ u
  have : v ∉ s := this ∘ s.reachable_of_mem_supp rfl
  have : exists d in p.darts, d.fst in s ∧ d.snd ∉ s := p.exists_boundary_dart s rfl this
  rcases this with ⟨⟨⟨u', v'⟩, huv⟩, _, hu, hv⟩
have : ¬F.Reachable v' u' := mt ConnectedComponent.sound .mp hu ▸ hv s.mem_supp_iff u'
  suffices F ⊔ edge v' u' <= F by grind [Adj.reachable, sup_le_iff, le_iff_adj]
  refine h.le_of_ge ⟨?_, h.prop.right.sup_edge_of_not_reachable this⟩ le_sup_left
  grind [Maximal, sup_le, le_iff_adj, huv.symm]

中文:
引理 reachable_eq_of_maximal_isAcyclic
  结论: (F : 简单图 V)
  证明: by
  ext u v
  refine ⟨.mono h.prop.left, fun ⟨p⟩ => ?_⟩
  by_contra
  let s : F.ConnectedComponent := .mk _ u
  have : v ∉ s := this ∘ s.reachable_of_mem_supp rfl
  have : exists d in p.darts, d.fst in s ∧ d.snd ∉ s := p.exists_boundary_dart s rfl this
  rcases this with ⟨⟨⟨u', v'⟩, huv⟩, _, hu, hv⟩
have : ¬F.Reachable v' u' := mt ConnectedComponent.sound .mp hu ▸ hv s.mem_supp_iff u'
  suffices F ⊔ edge v' u' <= F by grind [Adj.reachable, sup_le_iff, le_iff_adj]
  refine h.le_of_ge ⟨?_, h.prop.right.sup_edge_of_not_reachable this⟩ le_sup_left
  grind [Maximal, sup_le, le_iff_adj, huv.symm]

Depends on / 依赖: Adj.reachable, ConnectedComponent, ConnectedComponent.sound, F.ConnectedComponent, F.Reachable, Reachable, d.fst, d.snd, exists_boundary_dart, h.le_of_ge, h.prop.left, h.prop.right.sup_edge_of, le_iff_adj, le_of_ge, mem_supp_iff, p.darts, p.exists_boundary_dart, reachable, reachable_of_mem_supp, s.mem_supp_iff
-/
lemma reachable_eq_of_maximal_isAcyclic (F : SimpleGraph V)
    (h : Maximal (fun H => H <= G ∧ H.IsAcyclic) F) : F.Reachable = G.Reachable := by
  ext u v
  refine ⟨.mono h.prop.left, fun ⟨p⟩ => ?_⟩
  by_contra
  let s : F.ConnectedComponent := .mk _ u
  have : v ∉ s := this ∘ s.reachable_of_mem_supp rfl
  have : exists d in p.darts, d.fst in s ∧ d.snd ∉ s := p.exists_boundary_dart s rfl this
  rcases this with ⟨⟨⟨u', v'⟩, huv⟩, _, hu, hv⟩
have : ¬F.Reachable v' u' := mt ConnectedComponent.sound .mp hu ▸ hv s.mem_supp_iff u'
  suffices F ⊔ edge v' u' <= F by grind [Adj.reachable, sup_le_iff, le_iff_adj]
  refine h.le_of_ge ⟨?_, h.prop.right.sup_edge_of_not_reachable this⟩ le_sup_left
  grind [Maximal, sup_le, le_iff_adj, huv.symm]

/--
theorem `maximal_isAcyclic_iff_reachable_eq` / 定理 `maximal_isAcyclic_iff_reachable_eq`

English:
theorem maximal_isAcyclic_iff_reachable_eq
  given: {F : SimpleGraph V} (hle : F <= G) (hF : F.IsAcyclic)
  proof: by
  refine ⟨reachable_eq_of_maximal_isAcyclic F, fun h => ?_⟩
  by_contra
  have ⟨H, hFH, hHG, hH⟩ := exists_gt_of_not_maximal ⟨hle, hF⟩ this
have ⟨e, heH, heF⟩ := Set.exists_of_ssubset edgeSet_strict_mono hFH
  have h_bridge : (F ⊔ fromEdgeSet {e}).IsBridge e := by
refine isAcyclic_iff_forall_isBridge.mp ?_ by simp [H.not_isDiag_of_mem_edgeSet heH]
exact hH.anti sup_le_iff.mpr ⟨hFH.le, H.fromEdgeSet_le.mpr by grind⟩
  have : (F ⊔ fromEdgeSet {e}).deleteEdges {e} = F := by simpa using heF
  cases e
  rw [isBridge_iff]; rw [this]; rw [h] at h_bridge
exact h_bridge .reachable hHG heH

中文:
定理 maximal_isAcyclic_iff_reachable_eq
  条件: {F : 简单图 V} (hle : F <= G) (hF : F.IsAcyclic)
  证明: by
  refine ⟨reachable_eq_of_maximal_isAcyclic F, fun h => ?_⟩
  by_contra
  have ⟨H, hFH, hHG, hH⟩ := exists_gt_of_not_maximal ⟨hle, hF⟩ this
have ⟨e, heH, heF⟩ := Set.exists_of_ssubset edgeSet_strict_mono hFH
  have h_bridge : (F ⊔ fromEdgeSet {e}).IsBridge e := by
refine isAcyclic_iff_forall_isBridge.mp ?_ by simp [H.not_isDiag_of_mem_edgeSet heH]
exact hH.anti sup_le_iff.mpr ⟨hFH.le, H.fromEdgeSet_le.mpr by grind⟩
  have : (F ⊔ fromEdgeSet {e}).deleteEdges {e} = F := by simpa using heF
  cases e
  rw [isBridge_iff]; rw [this]; rw [h] at h_bridge
exact h_bridge .reachable hHG heH

Depends on / 依赖: H.fromEdgeSet_le.mpr, H.not_isDiag_of_mem_edgeSet, IsBridge, Set.exists_of_ssubset, deleteEdges, edgeSet_strict_mono, exists_gt_of_not_maximal, exists_of_ssubset, fromEdgeSet, fromEdgeSet_le, hFH.le, hH.anti, h_bridge, isAcyclic_iff_forall_isBridge, isAcyclic_iff_forall_isBridge.mp, not_isDiag_of_mem_edgeSet, reachable_eq_of_maximal_isAcyclic, sup_le_iff, sup_le_iff.mpr
-/
theorem maximal_isAcyclic_iff_reachable_eq {F : SimpleGraph V} (hle : F <= G) (hF : F.IsAcyclic) :
    Maximal (fun F => F <= G ∧ F.IsAcyclic) F ↔ F.Reachable = G.Reachable := by
  refine ⟨reachable_eq_of_maximal_isAcyclic F, fun h => ?_⟩
  by_contra
  have ⟨H, hFH, hHG, hH⟩ := exists_gt_of_not_maximal ⟨hle, hF⟩ this
have ⟨e, heH, heF⟩ := Set.exists_of_ssubset edgeSet_strict_mono hFH
  have h_bridge : (F ⊔ fromEdgeSet {e}).IsBridge e := by
refine isAcyclic_iff_forall_isBridge.mp ?_ by simp [H.not_isDiag_of_mem_edgeSet heH]
exact hH.anti sup_le_iff.mpr ⟨hFH.le, H.fromEdgeSet_le.mpr by grind⟩
  have : (F ⊔ fromEdgeSet {e}).deleteEdges {e} = F := by simpa using heF
  cases e
  rw [isBridge_iff]; rw [this]; rw [h] at h_bridge
exact h_bridge .reachable hHG heH

/--
theorem `Connected.maximal_le_isAcyclic_iff_isTree` / 定理 `Connected.maximal_le_isAcyclic_iff_isTree`

English:
theorem Connected.maximal_le_isAcyclic_iff_isTree
  statement: {T : SimpleGraph V} (hG : G.Connected)
  proof: by
  have := hG.nonempty
  refine ⟨fun h => ⟨⟨fun u v => ?_⟩, h.1.2⟩, fun hT' => ?_⟩
  · exact G.reachable_eq_of_maximal_isAcyclic T h ▸ hG.preconnected u v
  · rw [maximal_isAcyclic_iff_reachable_eq hT hT'.isAcyclic,
      T.preconnected_iff_reachable_eq_top.mp hT'.preconnected,
      G.preconnected_iff_reachable_eq_top.mp hG.preconnected]

@[simp]

中文:
定理 连通.maximal_le_isAcyclic_iff_isTree
  结论: {T : 简单图 V} (hG : G.连通)
  证明: by
  have := hG.nonempty
  refine ⟨fun h => ⟨⟨fun u v => ?_⟩, h.1.2⟩, fun hT' => ?_⟩
  · exact G.reachable_eq_of_maximal_isAcyclic T h ▸ hG.preconnected u v
  · rw [maximal_isAcyclic_iff_reachable_eq hT hT'.isAcyclic,
      T.preconnected_iff_reachable_eq_top.mp hT'.preconnected,
      G.preconnected_iff_reachable_eq_top.mp hG.preconnected]

@[simp]

Depends on / 依赖: G.preconnected_iff_reachable_eq_top.mp, G.reachable_eq_of_maximal_isAcyclic, T.preconnected_iff_reachable_eq_top.mp, hG.nonempty, hG.preconnected, isAcyclic, maximal_isAcyclic_iff_reachable_eq, nonempty, preconnected, preconnected_iff_reachable_eq_top, reachable_eq_of_maximal_isAcyclic
-/
theorem Connected.maximal_le_isAcyclic_iff_isTree {T : SimpleGraph V} (hG : G.Connected)
    (hT : T <= G) : Maximal (fun H => H <= G ∧ H.IsAcyclic) T ↔ T.IsTree := by
  have := hG.nonempty
  refine ⟨fun h => ⟨⟨fun u v => ?_⟩, h.1.2⟩, fun hT' => ?_⟩
  · exact G.reachable_eq_of_maximal_isAcyclic T h ▸ hG.preconnected u v
  · rw [maximal_isAcyclic_iff_reachable_eq hT hT'.isAcyclic,
      T.preconnected_iff_reachable_eq_top.mp hT'.preconnected,
      G.preconnected_iff_reachable_eq_top.mp hG.preconnected]

@[simp]
/--
theorem `maximal_isAcyclic_iff_isTree` / 定理 `maximal_isAcyclic_iff_isTree`

English:
theorem maximal_isAcyclic_iff_isTree
  given: [Nonempty V] {T : SimpleGraph V}
  proof: by
  simp [← connected_top.maximal_le_isAcyclic_iff_isTree le_top]

中文:
定理 maximal_isAcyclic_iff_isTree
  条件: [非空 V] {T : 简单图 V}
  证明: by
  simp [← connected_top.maximal_le_isAcyclic_iff_isTree le_top]

Depends on / 依赖: connected_top, connected_top.maximal_le_isAcyclic_iff_isTree, le_top, maximal_le_isAcyclic_iff_isTree
-/
theorem maximal_isAcyclic_iff_isTree [Nonempty V] {T : SimpleGraph V} :
    Maximal IsAcyclic T ↔ T.IsTree := by
  simp [← connected_top.maximal_le_isAcyclic_iff_isTree le_top]

/--
theorem `isTree_iff_maximal_isAcyclic` / 定理 `isTree_iff_maximal_isAcyclic`

English:
theorem isTree_iff_maximal_isAcyclic
  statement: G.IsTree ↔ Nonempty V ∧ Maximal IsAcyclic G
  proof: by
  refine ⟨fun h => ?_, fun ⟨_, h⟩ => G.maximal_isAcyclic_iff_isTree.mp h⟩
  have := h.nonempty
  exact ⟨this, G.maximal_isAcyclic_iff_isTree.mpr h⟩

中文:
定理 isTree_iff_maximal_isAcyclic
  结论: G.是树 ↔ 非空 V ∧ 极大 IsAcyclic G
  证明: by
  refine ⟨fun h => ?_, fun ⟨_, h⟩ => G.maximal_isAcyclic_iff_isTree.mp h⟩
  have := h.nonempty
  exact ⟨this, G.maximal_isAcyclic_iff_isTree.mpr h⟩

Depends on / 依赖: G.maximal_isAcyclic_iff_isTree.mp, G.maximal_isAcyclic_iff_isTree.mpr, h.nonempty, maximal_isAcyclic_iff_isTree, nonempty
-/
theorem isTree_iff_maximal_isAcyclic : G.IsTree ↔ Nonempty V ∧ Maximal IsAcyclic G := by
  refine ⟨fun h => ?_, fun ⟨_, h⟩ => G.maximal_isAcyclic_iff_isTree.mp h⟩
  have := h.nonempty
  exact ⟨this, G.maximal_isAcyclic_iff_isTree.mpr h⟩

/--
theorem `exists_isAcyclic_reachable_eq_le_of_le_of_isAcyclic` / 定理 `exists_isAcyclic_reachable_eq_le_of_le_of_isAcyclic`

English:
theorem exists_isAcyclic_reachable_eq_le_of_le_of_isAcyclic
  statement: {H : SimpleGraph V} (hH_le : H <= G)
  proof: by
  obtain ⟨F, hF⟩ := G.exists_maximal_isAcyclic_of_le_isAcyclic hH_le hH_isAcyclic
  grind [maximal_isAcyclic_iff_reachable_eq, Maximal]

中文:
定理 存在_isAcyclic_reachable_eq_le_of_le_of_isAcyclic
  结论: {H : 简单图 V} (hH_le : H <= G)
  证明: by
  obtain ⟨F, hF⟩ := G.exists_maximal_isAcyclic_of_le_isAcyclic hH_le hH_isAcyclic
  grind [maximal_isAcyclic_iff_reachable_eq, Maximal]

Depends on / 依赖: G.exists_maximal_isAcyclic_of_le_isAcyclic, Maximal, exists_maximal_isAcyclic_of_le_isAcyclic, hH_isAcyclic, hH_le, maximal_isAcyclic_iff_reachable_eq
-/
theorem exists_isAcyclic_reachable_eq_le_of_le_of_isAcyclic {H : SimpleGraph V} (hH_le : H <= G)
    (hH_isAcyclic : H.IsAcyclic) :
    exists F : SimpleGraph V, H <= F ∧ F <= G ∧ F.IsAcyclic ∧ F.Reachable = G.Reachable := by
  obtain ⟨F, hF⟩ := G.exists_maximal_isAcyclic_of_le_isAcyclic hH_le hH_isAcyclic
  grind [maximal_isAcyclic_iff_reachable_eq, Maximal]

/--
theorem `exists_isAcyclic_reachable_eq_le` / 定理 `exists_isAcyclic_reachable_eq_le`

English:
theorem exists_isAcyclic_reachable_eq_le
  proof: by
  obtain ⟨F, hF⟩ := G.exists_isAcyclic_reachable_eq_le_of_le_of_isAcyclic bot_le isAcyclic_bot
  grind

中文:
定理 存在_isAcyclic_reachable_eq_le
  证明: by
  obtain ⟨F, hF⟩ := G.exists_isAcyclic_reachable_eq_le_of_le_of_isAcyclic bot_le isAcyclic_bot
  grind

Depends on / 依赖: G.exists_isAcyclic_reachable_eq_le_of_le_of_isAcyclic, bot_le, exists_isAcyclic_reachable_eq_le_of_le_of_isAcyclic, isAcyclic_bot
-/
theorem exists_isAcyclic_reachable_eq_le :
    exists F <= G, F.IsAcyclic ∧ F.Reachable = G.Reachable := by
  obtain ⟨F, hF⟩ := G.exists_isAcyclic_reachable_eq_le_of_le_of_isAcyclic bot_le isAcyclic_bot
  grind

/--
lemma `Connected.exists_isTree_le_of_le_of_isAcyclic` / 引理 `Connected.exists_isTree_le_of_le_of_isAcyclic`

English:
lemma Connected.exists_isTree_le_of_le_of_isAcyclic
  statement: {H : SimpleGraph V} (h : G.Connected)
  proof: by
  obtain ⟨F, hF⟩ := G.exists_isAcyclic_reachable_eq_le_of_le_of_isAcyclic hH_le hH_isAcyclic
  grind [IsTree, Connected, preconnected_iff_reachable_eq_top]

中文:
引理 连通.存在_isTree_le_of_le_of_isAcyclic
  结论: {H : 简单图 V} (h : G.连通)
  证明: by
  obtain ⟨F, hF⟩ := G.exists_isAcyclic_reachable_eq_le_of_le_of_isAcyclic hH_le hH_isAcyclic
  grind [IsTree, Connected, preconnected_iff_reachable_eq_top]

Depends on / 依赖: Connected, G.exists_isAcyclic_reachable_eq_le_of_le_of_isAcyclic, IsTree, exists_isAcyclic_reachable_eq_le_of_le_of_isAcyclic, hH_isAcyclic, hH_le, preconnected_iff_reachable_eq_top
-/
lemma Connected.exists_isTree_le_of_le_of_isAcyclic {H : SimpleGraph V} (h : G.Connected)
    (hH_le : H <= G) (hH_isAcyclic : H.IsAcyclic) :
    exists F : SimpleGraph V, H <= F ∧ F <= G ∧ F.IsTree := by
  obtain ⟨F, hF⟩ := G.exists_isAcyclic_reachable_eq_le_of_le_of_isAcyclic hH_le hH_isAcyclic
  grind [IsTree, Connected, preconnected_iff_reachable_eq_top]

/--
lemma `Connected.exists_isTree_le` / 引理 `Connected.exists_isTree_le`

English:
lemma Connected.exists_isTree_le
  given: (h : G.Connected)
  statement: exists T <= G, IsTree T
  proof: by
  obtain ⟨F, hF⟩ := G.exists_isAcyclic_reachable_eq_le_of_le_of_isAcyclic bot_le isAcyclic_bot
  grind [IsTree, Connected, preconnected_iff_reachable_eq_top]

中文:
引理 连通.存在_isTree_le
  条件: (h : G.连通)
  结论: 存在 T <= G, 是树 T
  证明: by
  obtain ⟨F, hF⟩ := G.exists_isAcyclic_reachable_eq_le_of_le_of_isAcyclic bot_le isAcyclic_bot
  grind [IsTree, Connected, preconnected_iff_reachable_eq_top]

Depends on / 依赖: Connected, G.exists_isAcyclic_reachable_eq_le_of_le_of_isAcyclic, IsTree, bot_le, exists_isAcyclic_reachable_eq_le_of_le_of_isAcyclic, isAcyclic_bot, preconnected_iff_reachable_eq_top
-/
lemma Connected.exists_isTree_le (h : G.Connected) : exists T <= G, IsTree T := by
  obtain ⟨F, hF⟩ := G.exists_isAcyclic_reachable_eq_le_of_le_of_isAcyclic bot_le isAcyclic_bot
  grind [IsTree, Connected, preconnected_iff_reachable_eq_top]

/--
lemma `Connected.card_vert_le_card_edgeSet_add_one` / 引理 `Connected.card_vert_le_card_edgeSet_add_one`

English:
lemma Connected.card_vert_le_card_edgeSet_add_one
  given: (h : G.Connected)
  proof: by
  obtain hV | hV := (finite_or_infinite V).symm
  · simp
  have := Fintype.ofFinite
  obtain ⟨T, hle, hT⟩ := h.exists_isTree_le
  rw [Nat.card_eq_fintype_card]; rw [← hT.card_edgeFinset]; rw [add_le_add_iff_right]; rw [Nat.card_eq_fintype_card]; rw [← edgeFinset_card]
exact Finset.card_mono by simpa

中文:
引理 连通.card_vert_le_card_edgeSet_add_one
  条件: (h : G.连通)
  证明: by
  obtain hV | hV := (finite_or_infinite V).symm
  · simp
  have := Fintype.ofFinite
  obtain ⟨T, hle, hT⟩ := h.exists_isTree_le
  rw [Nat.card_eq_fintype_card]; rw [← hT.card_edgeFinset]; rw [add_le_add_iff_right]; rw [Nat.card_eq_fintype_card]; rw [← edgeFinset_card]
exact Finset.card_mono by simpa

Depends on / 依赖: Finset, Finset.card_mono, Fintype, Fintype.ofFinite, Nat.card_eq_fintype_card, add_le_add_iff_right, card_edgeFinset, card_eq_fintype_card, card_mono, edgeFinset_card, exists_isTree_le, finite_or_infinite, h.exists_isTree_le, hT.card_edgeFinset, ofFinite
-/
lemma Connected.card_vert_le_card_edgeSet_add_one (h : G.Connected) :
    Nat.card V <= Nat.card G.edgeSet + 1 := by
  obtain hV | hV := (finite_or_infinite V).symm
  · simp
  have := Fintype.ofFinite
  obtain ⟨T, hle, hT⟩ := h.exists_isTree_le
  rw [Nat.card_eq_fintype_card]; rw [← hT.card_edgeFinset]; rw [add_le_add_iff_right]; rw [Nat.card_eq_fintype_card]; rw [← edgeFinset_card]
exact Finset.card_mono by simpa

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `isTree_iff_connected_and_card` / 引理 `isTree_iff_connected_and_card`

English:
lemma isTree_iff_connected_and_card
  given: [Finite V]
  proof: by
  have := Fintype.ofFinite V
  classical
  refine ⟨fun h => ⟨h.connected, by simpa [edgeFinset] using h.card_edgeFinset⟩,
    fun ⟨h₁, h₂⟩ => ⟨h₁, ?_⟩⟩
  simp_rw [isAcyclic_iff_forall_adj_isBridge]
  refine fun x y h => by_contra fun hbr =>
    (h₁.connected_delete_edge_of_not_isBridge hbr).card_vert_le_card_edgeSet_add_one.not_gt ?_
  rw [Nat.card_eq_fintype_card]; rw [← edgeFinset_card]; rw [← h₂]; rw [Nat.card_eq_fintype_card]; rw [← edgeFinset_card]; rw [add_lt_add_iff_right]
exact Finset.card_lt_card by simpa [deleteEdges, edgeFinset]

中文:
引理 isTree_iff_connected_and_card
  条件: [有限 V]
  证明: by
  have := Fintype.ofFinite V
  classical
  refine ⟨fun h => ⟨h.connected, by simpa [edgeFinset] using h.card_edgeFinset⟩,
    fun ⟨h₁, h₂⟩ => ⟨h₁, ?_⟩⟩
  simp_rw [isAcyclic_iff_forall_adj_isBridge]
  refine fun x y h => by_contra fun hbr =>
    (h₁.connected_delete_edge_of_not_isBridge hbr).card_vert_le_card_edgeSet_add_one.not_gt ?_
  rw [Nat.card_eq_fintype_card]; rw [← edgeFinset_card]; rw [← h₂]; rw [Nat.card_eq_fintype_card]; rw [← edgeFinset_card]; rw [add_lt_add_iff_right]
exact Finset.card_lt_card by simpa [deleteEdges, edgeFinset]

Depends on / 依赖: Finset, Finset.card_lt_card, Fintype, Fintype.ofFinite, Nat.card_eq_fintype_card, add_lt_add_iff_right, card_edgeFinset, card_eq_fintype_card, card_lt_card, card_vert_le_card_edgeSet_add_one, card_vert_le_card_edgeSet_add_one.not_gt, classical, connected, connected_delete_edge_of_not_isBridge, edgeFinset, edgeFinset_card, h.card_edgeFinset, h.connected, isAcyclic_iff_forall_adj_isBridge, not_gt
-/
lemma isTree_iff_connected_and_card [Finite V] :
    G.IsTree ↔ G.Connected ∧ Nat.card G.edgeSet + 1 = Nat.card V := by
  have := Fintype.ofFinite V
  classical
  refine ⟨fun h => ⟨h.connected, by simpa [edgeFinset] using h.card_edgeFinset⟩,
    fun ⟨h₁, h₂⟩ => ⟨h₁, ?_⟩⟩
  simp_rw [isAcyclic_iff_forall_adj_isBridge]
  refine fun x y h => by_contra fun hbr =>
    (h₁.connected_delete_edge_of_not_isBridge hbr).card_vert_le_card_edgeSet_add_one.not_gt ?_
  rw [Nat.card_eq_fintype_card]; rw [← edgeFinset_card]; rw [← h₂]; rw [Nat.card_eq_fintype_card]; rw [← edgeFinset_card]; rw [add_lt_add_iff_right]
exact Finset.card_lt_card by simpa [deleteEdges, edgeFinset]

/--
lemma `IsTree.minDegree_eq_one_of_nontrivial` / 引理 `IsTree.minDegree_eq_one_of_nontrivial`

English:
lemma IsTree.minDegree_eq_one_of_nontrivial
  statement: (h : G.IsTree) [Fintype V] [Nontrivial V]
  proof: by
  by_cases q : 2 <= G.minDegree
  · have := h.card_edgeFinset
    have := G.sum_degrees_eq_twice_card_edges
    have hle : ∑ v : V, 2 <= ∑ v, G.degree v := by
      gcongr
      exact le_trans q (G.minDegree_le_degree _)
    rw [Finset.sum_const]; rw [Finset.card_univ]; rw [smul_eq_mul] at hle
    lia
  · have := h.preconnected.minDegree_pos_of_nontrivial
    lia

中文:
引理 是树.minDegree_eq_one_of_nontrivial
  结论: (h : G.是树) [有限类型 V] [非平凡 V]
  证明: by
  by_cases q : 2 <= G.minDegree
  · have := h.card_edgeFinset
    have := G.sum_degrees_eq_twice_card_edges
    have hle : ∑ v : V, 2 <= ∑ v, G.degree v := by
      gcongr
      exact le_trans q (G.minDegree_le_degree _)
    rw [Finset.sum_const]; rw [Finset.card_univ]; rw [smul_eq_mul] at hle
    lia
  · have := h.preconnected.minDegree_pos_of_nontrivial
    lia

Depends on / 依赖: Finset, Finset.card_univ, Finset.sum_const, G.degree, G.minDegree, G.minDegree_le_degree, G.sum_degrees_eq_twice_card_edges, card_edgeFinset, card_univ, degree, h.card_edgeFinset, h.preconnected.minDegree_pos_of_nontrivial, le_trans, minDegree, minDegree_le_degree, minDegree_pos_of_nontrivial, preconnected, smul_eq_mul, sum_const, sum_degrees_eq_twice_card_edges
-/
lemma IsTree.minDegree_eq_one_of_nontrivial (h : G.IsTree) [Fintype V] [Nontrivial V]
    [DecidableRel G.Adj] : G.minDegree = 1 := by
  by_cases q : 2 <= G.minDegree
  · have := h.card_edgeFinset
    have := G.sum_degrees_eq_twice_card_edges
    have hle : ∑ v : V, 2 <= ∑ v, G.degree v := by
      gcongr
      exact le_trans q (G.minDegree_le_degree _)
    rw [Finset.sum_const]; rw [Finset.card_univ]; rw [smul_eq_mul] at hle
    lia
  · have := h.preconnected.minDegree_pos_of_nontrivial
    lia

/--
lemma `IsTree.exists_vert_degree_one_of_nontrivial` / 引理 `IsTree.exists_vert_degree_one_of_nontrivial`

English:
lemma IsTree.exists_vert_degree_one_of_nontrivial
  statement: [Fintype V] [Nontrivial V] [DecidableRel G.Adj]
  proof: by
  grind [G.exists_minimal_degree_vertex, minDegree_eq_one_of_nontrivial]

中文:
引理 是树.存在_vert_degree_one_of_nontrivial
  结论: [有限类型 V] [非平凡 V] [DecidableRel G.伴随]
  证明: by
  grind [G.exists_minimal_degree_vertex, minDegree_eq_one_of_nontrivial]

Depends on / 依赖: G.exists_minimal_degree_vertex, exists_minimal_degree_vertex, minDegree_eq_one_of_nontrivial
-/
lemma IsTree.exists_vert_degree_one_of_nontrivial [Fintype V] [Nontrivial V] [DecidableRel G.Adj]
    (h : G.IsTree) : exists v, G.degree v = 1 := by
  grind [G.exists_minimal_degree_vertex, minDegree_eq_one_of_nontrivial]

/--
theorem `IsTree.exists_ne_and_degree_eq_one` / 定理 `IsTree.exists_ne_and_degree_eq_one`

English:
theorem IsTree.exists_ne_and_degree_eq_one
  statement: [Nontrivial V] [Finite G.edgeSet] [G.LocallyFinite]
  proof: by
  have ⟨u, v, p, hp, hmax⟩ := exists_isPath_forall_isPath_length_le_length G
  have ⟨u', v', hne⟩ := exists_pair_ne V
  have ⟨p', hp'⟩ := h.connected.exists_isPath u' v'
  have hnil : ¬p.Nil := by grind
  refine ⟨u, v, hp.nil_iff_eq.not.mp hnil, ?_, ?_⟩ <;>
    rw [degree_eq_one_iff_existsUnique_adj]
  · refine ⟨_, p.adj_snd hnil, fun w hadj => ?_⟩
    apply h.isAcyclic.eq_snd_of_adj_start hp hadj
    have : ¬(p.cons hadj.symm).IsPath := by grind [length_cons]
    grind [hp.cons]
.symm, fun w hadj => ?_⟩ · refine ⟨_, p.adj_penultimate hnil
    apply h.isAcyclic.eq_penultimate_of_adj_end hp hadj
    have : ¬(p.concat hadj).IsPath := by grind [length_concat]
    grind [hp.concat]

中文:
定理 是树.存在_ne_and_degree_eq_one
  结论: [非平凡 V] [有限 G.edgeSet] [G.局部有限]
  证明: by
  have ⟨u, v, p, hp, hmax⟩ := exists_isPath_forall_isPath_length_le_length G
  have ⟨u', v', hne⟩ := exists_pair_ne V
  have ⟨p', hp'⟩ := h.connected.exists_isPath u' v'
  have hnil : ¬p.Nil := by grind
  refine ⟨u, v, hp.nil_iff_eq.not.mp hnil, ?_, ?_⟩ <;>
    rw [degree_eq_one_iff_existsUnique_adj]
  · refine ⟨_, p.adj_snd hnil, fun w hadj => ?_⟩
    apply h.isAcyclic.eq_snd_of_adj_start hp hadj
    have : ¬(p.cons hadj.symm).IsPath := by grind [length_cons]
    grind [hp.cons]
.symm, fun w hadj => ?_⟩ · refine ⟨_, p.adj_penultimate hnil
    apply h.isAcyclic.eq_penultimate_of_adj_end hp hadj
    have : ¬(p.concat hadj).IsPath := by grind [length_concat]
    grind [hp.concat]

Depends on / 依赖: IsPath, adj_snd, connected, degree_eq_one_iff_existsUnique_adj, eq_snd_of_adj_start, exists_isPath, exists_isPath_forall_isPath_length_le_length, exists_pair_ne, h.connected.exists_isPath, h.isAcyclic.eq_snd_of_adj_start, hadj.symm, hp.cons, hp.nil_iff_eq.not.mp, isAcyclic, length_cons, nil_iff_eq, p.Nil, p.adj_snd, p.cons
-/
theorem IsTree.exists_ne_and_degree_eq_one [Nontrivial V] [Finite G.edgeSet] [G.LocallyFinite]
    (h : G.IsTree) : exists u v, u != v ∧ G.degree u = 1 ∧ G.degree v = 1 := by
  have ⟨u, v, p, hp, hmax⟩ := exists_isPath_forall_isPath_length_le_length G
  have ⟨u', v', hne⟩ := exists_pair_ne V
  have ⟨p', hp'⟩ := h.connected.exists_isPath u' v'
  have hnil : ¬p.Nil := by grind
  refine ⟨u, v, hp.nil_iff_eq.not.mp hnil, ?_, ?_⟩ <;>
    rw [degree_eq_one_iff_existsUnique_adj]
  · refine ⟨_, p.adj_snd hnil, fun w hadj => ?_⟩
    apply h.isAcyclic.eq_snd_of_adj_start hp hadj
    have : ¬(p.cons hadj.symm).IsPath := by grind [length_cons]
    grind [hp.cons]
.symm, fun w hadj => ?_⟩ · refine ⟨_, p.adj_penultimate hnil
    apply h.isAcyclic.eq_penultimate_of_adj_end hp hadj
    have : ¬(p.concat hadj).IsPath := by grind [length_concat]
    grind [hp.concat]

/--
lemma `Connected.induce_compl_singleton_of_degree_eq_one` / 引理 `Connected.induce_compl_singleton_of_degree_eq_one`

English:
lemma Connected.induce_compl_singleton_of_degree_eq_one
  statement: (hconn : G.Connected) {v : V}
  proof: by
  obtain ⟨u, adj_vu, hu⟩ := degree_eq_one_iff_existsUnique_adj.mp hdeg
  refine (connected_iff _).mpr ⟨?_, u, by aesop⟩
  /- There exists a walk between any two vertices w and x in G.induce {v}ᶜ
  via the unique vertex u adjacent to vertex v. -/
  intro w x
  obtain ⟨pwu, hpwu⟩ := hconn.exists_isPath w u
  obtain ⟨pux, hpux⟩ := hconn.exists_isPath u x
  rw [Reachable]; rw [← exists_true_iff_nonempty]
  classical
  use ((pwu.append pux).toPath.val.induce {v}ᶜ ?_).copy (SetCoe.ext rfl) (SetCoe.ext rfl)
  /- Each path between vertex u and another vertex in G.induce {v}ᶜ
  is contained in G.induce {v}ᶜ. -/
  intro z hz
  rw [Set.mem_compl_iff]; rw [Set.mem_singleton_iff]
  obtain ⟨pwz, pzx, p_eq_pwzx⟩ := mem_support_iff_exists_append.mp hz
  /- Prove vertex v is not in the path formed from the concatenated walks
  by showing that vertex u must then be passed twice. -/
  by_contra
  subst_vars
  refine List.nodup_iff_forall_not_duplicate.mp (pwu.append pux).toPath.nodup_support u ?_
  rw [p_eq_pwzx]; rw [support_append]; rw [List.duplicate_iff_two_le_count]; rw [List.count_append]
  have := List.one_le_count_iff.mpr (pwz.getVert_mem_support (pwz.length - 1))
  simp only [hu _ (pwz.adj_penultimate (not_nil_of_ne (by aesop))).symm] at this
  have := List.one_le_count_iff.mpr (pzx.snd_mem_tail_support (not_nil_of_ne (by aesop)))
  rw [hu _ (pzx.adj_snd (not_nil_of_ne (by aesop)))] at this
  lia

中文:
引理 连通.induce_compl_singleton_of_degree_eq_one
  结论: (hconn : G.连通) {v : V}
  证明: by
  obtain ⟨u, adj_vu, hu⟩ := degree_eq_one_iff_existsUnique_adj.mp hdeg
  refine (connected_iff _).mpr ⟨?_, u, by aesop⟩
  /- There exists a walk between any two vertices w and x in G.induce {v}ᶜ
  via the unique vertex u adjacent to vertex v. -/
  intro w x
  obtain ⟨pwu, hpwu⟩ := hconn.exists_isPath w u
  obtain ⟨pux, hpux⟩ := hconn.exists_isPath u x
  rw [Reachable]; rw [← exists_true_iff_nonempty]
  classical
  use ((pwu.append pux).toPath.val.induce {v}ᶜ ?_).copy (SetCoe.ext rfl) (SetCoe.ext rfl)
  /- Each path between vertex u and another vertex in G.induce {v}ᶜ
  is contained in G.induce {v}ᶜ. -/
  intro z hz
  rw [Set.mem_compl_iff]; rw [Set.mem_singleton_iff]
  obtain ⟨pwz, pzx, p_eq_pwzx⟩ := mem_support_iff_exists_append.mp hz
  /- Prove vertex v is not in the path formed from the concatenated walks
  by showing that vertex u must then be passed twice. -/
  by_contra
  subst_vars
  refine List.nodup_iff_forall_not_duplicate.mp (pwu.append pux).toPath.nodup_support u ?_
  rw [p_eq_pwzx]; rw [support_append]; rw [List.duplicate_iff_two_le_count]; rw [List.count_append]
  have := List.one_le_count_iff.mpr (pwz.getVert_mem_support (pwz.length - 1))
  simp only [hu _ (pwz.adj_penultimate (not_nil_of_ne (by aesop))).symm] at this
  have := List.one_le_count_iff.mpr (pzx.snd_mem_tail_support (not_nil_of_ne (by aesop)))
  rw [hu _ (pzx.adj_snd (not_nil_of_ne (by aesop)))] at this
  lia

Depends on / 依赖: adj_vu, connected_iff, degree_eq_one_iff_existsUnique_adj, degree_eq_one_iff_existsUnique_adj.mp
-/
lemma Connected.induce_compl_singleton_of_degree_eq_one (hconn : G.Connected) {v : V}
    [Fintype ↑(G.neighborSet v)] (hdeg : G.degree v = 1) : (G.induce {v}ᶜ).Connected := by
  obtain ⟨u, adj_vu, hu⟩ := degree_eq_one_iff_existsUnique_adj.mp hdeg
  refine (connected_iff _).mpr ⟨?_, u, by aesop⟩
  /- There exists a walk between any two vertices w and x in G.induce {v}ᶜ
  via the unique vertex u adjacent to vertex v. -/
  intro w x
  obtain ⟨pwu, hpwu⟩ := hconn.exists_isPath w u
  obtain ⟨pux, hpux⟩ := hconn.exists_isPath u x
  rw [Reachable]; rw [← exists_true_iff_nonempty]
  classical
  use ((pwu.append pux).toPath.val.induce {v}ᶜ ?_).copy (SetCoe.ext rfl) (SetCoe.ext rfl)
  /- Each path between vertex u and another vertex in G.induce {v}ᶜ
  is contained in G.induce {v}ᶜ. -/
  intro z hz
  rw [Set.mem_compl_iff]; rw [Set.mem_singleton_iff]
  obtain ⟨pwz, pzx, p_eq_pwzx⟩ := mem_support_iff_exists_append.mp hz
  /- Prove vertex v is not in the path formed from the concatenated walks
  by showing that vertex u must then be passed twice. -/
  by_contra
  subst_vars
  refine List.nodup_iff_forall_not_duplicate.mp (pwu.append pux).toPath.nodup_support u ?_
  rw [p_eq_pwzx]; rw [support_append]; rw [List.duplicate_iff_two_le_count]; rw [List.count_append]
  have := List.one_le_count_iff.mpr (pwz.getVert_mem_support (pwz.length - 1))
  simp only [hu _ (pwz.adj_penultimate (not_nil_of_ne (by aesop))).symm] at this
  have := List.one_le_count_iff.mpr (pzx.snd_mem_tail_support (not_nil_of_ne (by aesop)))
  rw [hu _ (pzx.adj_snd (not_nil_of_ne (by aesop)))] at this
  lia

/--
lemma `Connected.exists_connected_induce_compl_singleton_of_finite_nontrivial` / 引理 `Connected.exists_connected_induce_compl_singleton_of_finite_nontrivial`

English:
lemma Connected.exists_connected_induce_compl_singleton_of_finite_nontrivial
  proof: by
  obtain ⟨T, _, T_isTree⟩ := hconn.exists_isTree_le
  have ⟨hT, _⟩ := T_isTree
  have := Fintype.ofFinite V
  classical
  obtain ⟨v, hv⟩ := T_isTree.exists_vert_degree_one_of_nontrivial
  exact ⟨v, (hT.induce_compl_singleton_of_degree_eq_one hv).mono (by tauto)⟩

中文:
引理 连通.存在_connected_induce_compl_singleton_of_finite_nontrivial
  证明: by
  obtain ⟨T, _, T_isTree⟩ := hconn.exists_isTree_le
  have ⟨hT, _⟩ := T_isTree
  have := Fintype.ofFinite V
  classical
  obtain ⟨v, hv⟩ := T_isTree.exists_vert_degree_one_of_nontrivial
  exact ⟨v, (hT.induce_compl_singleton_of_degree_eq_one hv).mono (by tauto)⟩

Depends on / 依赖: Fintype, Fintype.ofFinite, T_isTree, T_isTree.exists_vert_degree_one_of_nontrivial, classical, exists_isTree_le, exists_vert_degree_one_of_nontrivial, hT.induce_compl_singleton_of_degree_eq_one, hconn.exists_isTree_le, induce_compl_singleton_of_degree_eq_one, ofFinite
-/
lemma Connected.exists_connected_induce_compl_singleton_of_finite_nontrivial
    [Finite V] [Nontrivial V] (hconn : G.Connected) : exists v : V, (G.induce {v}ᶜ).Connected := by
  obtain ⟨T, _, T_isTree⟩ := hconn.exists_isTree_le
  have ⟨hT, _⟩ := T_isTree
  have := Fintype.ofFinite V
  classical
  obtain ⟨v, hv⟩ := T_isTree.exists_vert_degree_one_of_nontrivial
  exact ⟨v, (hT.induce_compl_singleton_of_degree_eq_one hv).mono (by tauto)⟩

/--
lemma `Connected.exists_preconnected_induce_compl_singleton_of_finite` / 引理 `Connected.exists_preconnected_induce_compl_singleton_of_finite`

English:
lemma Connected.exists_preconnected_induce_compl_singleton_of_finite
  statement: [Finite V]
  proof: by
  nontriviality V using hconn.nonempty
  obtain ⟨v, hv⟩ := hconn.exists_connected_induce_compl_singleton_of_finite_nontrivial
  exact ⟨v, hv.preconnected⟩

中文:
引理 连通.存在_preconnected_induce_compl_singleton_of_finite
  结论: [有限 V]
  证明: by
  nontriviality V using hconn.nonempty
  obtain ⟨v, hv⟩ := hconn.exists_connected_induce_compl_singleton_of_finite_nontrivial
  exact ⟨v, hv.preconnected⟩

Depends on / 依赖: MulAction, MulAction.compHom, compHom, exists_connected_induce_compl_singleton_of_finite_nontrivial, fast_instance, hconn.exists_connected_induce_compl_singleton_of_finite_nontrivial, hconn.nonempty, hv.preconnected, nonempty, nontriviality, ofNNRealHom, ofNNRealHom.toMonoidHom, preconnected, toMonoidHom
-/
lemma Connected.exists_preconnected_induce_compl_singleton_of_finite [Finite V]
    (hconn : G.Connected) : exists v : V, (G.induce {v}ᶜ).Preconnected := by
  nontriviality V using hconn.nonempty
  obtain ⟨v, hv⟩ := hconn.exists_connected_induce_compl_singleton_of_finite_nontrivial
  exact ⟨v, hv.preconnected⟩

/--
lemma `IsAcyclic.dist_ne_of_adj` / 引理 `IsAcyclic.dist_ne_of_adj`

English:
lemma IsAcyclic.dist_ne_of_adj
  statement: (hG : G.IsAcyclic) {u v w : V} (hadj : G.Adj v w)
  proof: by
  obtain ⟨p, hp, hp'⟩ := hreach.exists_path_of_dist
.exists_path_of_dist obtain ⟨q, hq, hq'⟩ := hreach.trans hadj.reachable
  rw [← hp']; rw [← hq']
  by_cases hw : w in p.support
  · rw [hG.path_concat hq hp hadj.symm hw, q.length_concat]
    exact q.length.ne_add_one.symm
  · have hv : v in q.support := hG.mem_support_of_ne_mem_support_of_adj_of_isPath hq hp
      hadj.symm hw
    rw [hG.path_concat hp hq hadj hv]; rw [p.length_concat]
    exact p.length.ne_add_one

中文:
引理 IsAcyclic.dist_ne_of_adj
  结论: (hG : G.IsAcyclic) {u v w : V} (hadj : G.伴随 v w)
  证明: by
  obtain ⟨p, hp, hp'⟩ := hreach.exists_path_of_dist
.exists_path_of_dist obtain ⟨q, hq, hq'⟩ := hreach.trans hadj.reachable
  rw [← hp']; rw [← hq']
  by_cases hw : w in p.support
  · rw [hG.path_concat hq hp hadj.symm hw, q.length_concat]
    exact q.length.ne_add_one.symm
  · have hv : v in q.support := hG.mem_support_of_ne_mem_support_of_adj_of_isPath hq hp
      hadj.symm hw
    rw [hG.path_concat hp hq hadj hv]; rw [p.length_concat]
    exact p.length.ne_add_one

Depends on / 依赖: exists_path_of_dist, hG.mem_support_of_ne_mem_support_of_adj_of_isPath, hG.path_concat, hadj.reachable, hadj.symm, hreach, hreach.exists_path_of_dist, hreach.trans, length, length_concat, mem_support_of_ne_mem_support_of_adj_of_isPath, ne_add_one, p.length.ne_add_one, p.length_concat, p.support, path_concat, q.length.ne_add_one.symm, q.length_concat, q.support, reachable
-/
lemma IsAcyclic.dist_ne_of_adj (hG : G.IsAcyclic) {u v w : V} (hadj : G.Adj v w)
    (hreach : G.Reachable u v) : G.dist u v != G.dist u w := by
  obtain ⟨p, hp, hp'⟩ := hreach.exists_path_of_dist
.exists_path_of_dist obtain ⟨q, hq, hq'⟩ := hreach.trans hadj.reachable
  rw [← hp']; rw [← hq']
  by_cases hw : w in p.support
  · rw [hG.path_concat hq hp hadj.symm hw, q.length_concat]
    exact q.length.ne_add_one.symm
  · have hv : v in q.support := hG.mem_support_of_ne_mem_support_of_adj_of_isPath hq hp
      hadj.symm hw
    rw [hG.path_concat hp hq hadj hv]; rw [p.length_concat]
    exact p.length.ne_add_one

/--
lemma `IsTree.dist_ne_of_adj` / 引理 `IsTree.dist_ne_of_adj`

English:
lemma IsTree.dist_ne_of_adj
  given: (hG : G.IsTree) (u : V) {v w : V} (hadj : G.Adj v w)
  proof: hG.isAcyclic.dist_ne_of_adj hadj hG.connected u v

中文:
引理 是树.dist_ne_of_adj
  条件: (hG : G.是树) (u : V) {v w : V} (hadj : G.伴随 v w)
  证明: hG.isAcyclic.dist_ne_of_adj hadj hG.connected u v

Depends on / 依赖: connected, dist_ne_of_adj, hG.connected, hG.isAcyclic.dist_ne_of_adj, isAcyclic
-/
lemma IsTree.dist_ne_of_adj (hG : G.IsTree) (u : V) {v w : V} (hadj : G.Adj v w) :
    G.dist u v != G.dist u w :=
hG.isAcyclic.dist_ne_of_adj hadj hG.connected u v

/--
lemma `IsAcyclic.dist_eq_dist_add_one_of_adj_of_reachable` / 引理 `IsAcyclic.dist_eq_dist_add_one_of_adj_of_reachable`

English:
lemma IsAcyclic.dist_eq_dist_add_one_of_adj_of_reachable
  proof: by
  grind [dist_ne_of_adj, Adj.diff_dist_adj]

中文:
引理 IsAcyclic.dist_eq_dist_add_one_of_adj_of_reachable
  证明: by
  grind [dist_ne_of_adj, Adj.diff_dist_adj]

Depends on / 依赖: Adj.diff_dist_adj, diff_dist_adj, dist_ne_of_adj, smul_assoc
-/
lemma IsAcyclic.dist_eq_dist_add_one_of_adj_of_reachable
    (hG : G.IsAcyclic) (u : V) {v w : V} (hadj : G.Adj v w) (hreach : G.Reachable u v) :
    G.dist u v = G.dist u w + 1 ∨ G.dist u w = G.dist u v + 1 := by
  grind [dist_ne_of_adj, Adj.diff_dist_adj]

/--
lemma `IsTree.dist_eq_dist_add_one_of_adj` / 引理 `IsTree.dist_eq_dist_add_one_of_adj`

English:
lemma IsTree.dist_eq_dist_add_one_of_adj
  given: (hG : G.IsTree) (u : V) {v w : V} (hadj : G.Adj v w)
  proof: by
  grind [dist_ne_of_adj, Adj.diff_dist_adj]

中文:
引理 是树.dist_eq_dist_add_one_of_adj
  条件: (hG : G.是树) (u : V) {v w : V} (hadj : G.伴随 v w)
  证明: by
  grind [dist_ne_of_adj, Adj.diff_dist_adj]

Depends on / 依赖: Adj.diff_dist_adj, diff_dist_adj, dist_ne_of_adj
-/
lemma IsTree.dist_eq_dist_add_one_of_adj (hG : G.IsTree) (u : V) {v w : V} (hadj : G.Adj v w) :
    G.dist u v = G.dist u w + 1 ∨ G.dist u w = G.dist u v + 1 := by
  grind [dist_ne_of_adj, Adj.diff_dist_adj]

/--
Definition of `IsTree.coloringTwoOfVert` / `IsTree.coloringTwoOfVert` 的定义

English:
definition IsTree.coloringTwoOfVert
  signature: (hG : G.IsTree) (u : V)
  body: Coloring.mk (fun v => ⟨G.dist u v % 2, Nat.mod_lt (G.dist u v) Nat.zero_lt_two⟩) by
    grind [dist_eq_dist_add_one_of_adj]

中文:
定义 是树.coloringTwoOfVert
  签名: (hG : G.是树) (u : V)
  定义体: Coloring.mk (fun v => ⟨G.dist u v % 2, Nat.mod_lt (G.dist u v) Nat.zero_lt_two⟩) by
    grind [dist_eq_dist_add_one_of_adj]

Depends on / 依赖: Coloring, Coloring.mk, G.dist, Nat.mod_lt, Nat.zero_lt_two, dist_eq_dist_add_one_of_adj, mod_lt, zero_lt_two
-/
noncomputable def IsTree.coloringTwoOfVert (hG : G.IsTree) (u : V) : G.Coloring (Fin 2) :=
Coloring.mk (fun v => ⟨G.dist u v % 2, Nat.mod_lt (G.dist u v) Nat.zero_lt_two⟩) by
    grind [dist_eq_dist_add_one_of_adj]

/--
Definition of `IsTree.coloringTwo` / `IsTree.coloringTwo` 的定义

English:
definition IsTree.coloringTwo
  signature: (hG : G.IsTree)
  body: hG.coloringTwoOfVert hG.connected.nonempty.some

中文:
定义 是树.coloringTwo
  签名: (hG : G.是树)
  定义体: hG.coloringTwoOfVert hG.connected.nonempty.some

Depends on / 依赖: DistribMulAction, DistribMulAction.compHom, coloringTwoOfVert, compHom, connected, fast_instance, hG.coloringTwoOfVert, hG.connected.nonempty.some, nonempty, ofNNRealHom, ofNNRealHom.toMonoidHom, toMonoidHom
-/
noncomputable def IsTree.coloringTwo (hG : G.IsTree) : G.Coloring (Fin 2) :=
  hG.coloringTwoOfVert hG.connected.nonempty.some

/--
lemma `IsTree.isBipartite` / 引理 `IsTree.isBipartite`

English:
lemma IsTree.isBipartite
  given: (hG : G.IsTree)
  statement: G.IsBipartite
  proof: ⟨hG.coloringTwo⟩

中文:
引理 是树.isBipartite
  条件: (hG : G.是树)
  结论: G.IsBipartite
  证明: ⟨hG.coloringTwo⟩

Depends on / 依赖: Module, Module.compHom, coloringTwo, compHom, fast_instance, hG.coloringTwo, ofNNRealHom
-/
lemma IsTree.isBipartite (hG : G.IsTree) : G.IsBipartite :=
  ⟨hG.coloringTwo⟩

/--
Definition of `IsAcyclic.coloringTwoOfVerts` / `IsAcyclic.coloringTwoOfVerts` 的定义

English:
definition IsAcyclic.coloringTwoOfVerts
  signature: (hG : G.IsAcyclic) (verts : G.ConnectedComponent -> V)
  body: let u := verts G.connectedComponentMk v
    ⟨G.dist u v % 2, Nat.mod_lt (G.dist u v) Nat.zero_lt_two⟩
  map_rel' := by
    intro u v hadj
    have := ConnectedComponent.sound hadj.reachable
have := hG.dist_eq_dist_add_one_of_adj_of_reachable _ hadj ConnectedComponent.exact h _
    grind [top_adj]

中文:
定义 IsAcyclic.coloringTwoOfVerts
  签名: (hG : G.IsAcyclic) (verts : G.ConnectedComponent -> V)
  定义体: let u := verts G.connectedComponentMk v
    ⟨G.dist u v % 2, Nat.mod_lt (G.dist u v) Nat.zero_lt_two⟩
  map_rel' := by
    intro u v hadj
    have := ConnectedComponent.sound hadj.reachable
have := hG.dist_eq_dist_add_one_of_adj_of_reachable _ hadj ConnectedComponent.exact h _
    grind [top_adj]

Depends on / 依赖: Algebra, Algebra.commutes, Algebra.smul_def, ConnectedComponent, ConnectedComponent.exact, ConnectedComponent.sound, G.connectedComponentMk, G.dist, Nat.mod_lt, Nat.zero_lt_two, algebraMap, commutes, connectedComponentMk, dist_eq_dist_add_one_of_adj_of_reachable, hG.dist_eq_dist_add_one_of_adj_of_reachable, hadj.reachable, map_rel, mod_lt, ofNNRealHom, reachable
-/
noncomputable def IsAcyclic.coloringTwoOfVerts (hG : G.IsAcyclic) (verts : G.ConnectedComponent -> V)
    (h : forall C, verts C in C) : G.Coloring (Fin 2) where
  toFun v :=
let u := verts G.connectedComponentMk v
    ⟨G.dist u v % 2, Nat.mod_lt (G.dist u v) Nat.zero_lt_two⟩
  map_rel' := by
    intro u v hadj
    have := ConnectedComponent.sound hadj.reachable
have := hG.dist_eq_dist_add_one_of_adj_of_reachable _ hadj ConnectedComponent.exact h _
    grind [top_adj]

/--
Definition of `IsAcyclic.coloringTwo` / `IsAcyclic.coloringTwo` 的定义

English:
definition IsAcyclic.coloringTwo
  signature: (hG : G.IsAcyclic)
  body: hG.coloringTwoOfVerts (·.nonempty_supp.some) (·.nonempty_supp.some_mem)

中文:
定义 IsAcyclic.coloringTwo
  签名: (hG : G.IsAcyclic)
  定义体: hG.coloringTwoOfVerts (·.nonempty_supp.some) (·.nonempty_supp.some_mem)

Depends on / 依赖: coloringTwoOfVerts, hG.coloringTwoOfVerts, nonempty_supp, nonempty_supp.some, nonempty_supp.some_mem, some_mem
-/
noncomputable def IsAcyclic.coloringTwo (hG : G.IsAcyclic) : G.Coloring (Fin 2) :=
  hG.coloringTwoOfVerts (·.nonempty_supp.some) (·.nonempty_supp.some_mem)

/--
lemma `IsAcyclic.isBipartite` / 引理 `IsAcyclic.isBipartite`

English:
lemma IsAcyclic.isBipartite
  given: (hG : G.IsAcyclic)
  statement: G.IsBipartite
  proof: ⟨hG.coloringTwo⟩

中文:
引理 IsAcyclic.isBipartite
  条件: (hG : G.IsAcyclic)
  结论: G.IsBipartite
  证明: ⟨hG.coloringTwo⟩

Depends on / 依赖: coloringTwo, hG.coloringTwo
-/
lemma IsAcyclic.isBipartite (hG : G.IsAcyclic) : G.IsBipartite :=
  ⟨hG.coloringTwo⟩

/--
lemma `IsAcyclic.colorable_two` / 引理 `IsAcyclic.colorable_two`

English:
lemma IsAcyclic.colorable_two
  given: (hG : G.IsAcyclic)
  statement: G.Colorable 2
  proof: hG.isBipartite

中文:
引理 IsAcyclic.colorable_two
  条件: (hG : G.IsAcyclic)
  结论: G.Colorable 2
  证明: hG.isBipartite

Depends on / 依赖: hG.isBipartite, isBipartite
-/
lemma IsAcyclic.colorable_two (hG : G.IsAcyclic) : G.Colorable 2 :=
  hG.isBipartite

/--
lemma `IsTree.colorable_two` / 引理 `IsTree.colorable_two`

English:
lemma IsTree.colorable_two
  given: (hG : G.IsTree)
  statement: G.Colorable 2
  proof: hG.isAcyclic.colorable_two

中文:
引理 是树.colorable_two
  条件: (hG : G.是树)
  结论: G.Colorable 2
  证明: hG.isAcyclic.colorable_two

Depends on / 依赖: colorable_two, hG.isAcyclic.colorable_two, isAcyclic
-/
lemma IsTree.colorable_two (hG : G.IsTree) : G.Colorable 2 :=
  hG.isAcyclic.colorable_two

/--
lemma `IsAcyclic.chromaticNumber_le_two` / 引理 `IsAcyclic.chromaticNumber_le_two`

English:
lemma IsAcyclic.chromaticNumber_le_two
  given: (hG : G.IsAcyclic)
  statement: G.chromaticNumber <= 2
  proof: hG.colorable_two.chromaticNumber_le

中文:
引理 IsAcyclic.chromaticNumber_le_two
  条件: (hG : G.IsAcyclic)
  结论: G.chromaticNumber <= 2
  证明: hG.colorable_two.chromaticNumber_le

Depends on / 依赖: chromaticNumber_le, colorable_two, hG.colorable_two.chromaticNumber_le
-/
lemma IsAcyclic.chromaticNumber_le_two (hG : G.IsAcyclic) : G.chromaticNumber <= 2 :=
  hG.colorable_two.chromaticNumber_le

/--
lemma `IsTree.chromaticNumber_le_two` / 引理 `IsTree.chromaticNumber_le_two`

English:
lemma IsTree.chromaticNumber_le_two
  given: (hG : G.IsTree)
  statement: G.chromaticNumber <= 2
  proof: hG.colorable_two.chromaticNumber_le

中文:
引理 是树.chromaticNumber_le_two
  条件: (hG : G.是树)
  结论: G.chromaticNumber <= 2
  证明: hG.colorable_two.chromaticNumber_le

Depends on / 依赖: chromaticNumber_le, colorable_two, hG.colorable_two.chromaticNumber_le
-/
lemma IsTree.chromaticNumber_le_two (hG : G.IsTree) : G.chromaticNumber <= 2 :=
  hG.colorable_two.chromaticNumber_le

/--
lemma `exists_isCycle_of_two_le_isEdgeReachable` / 引理 `exists_isCycle_of_two_le_isEdgeReachable`

English:
lemma exists_isCycle_of_two_le_isEdgeReachable
  statement: {u v : V} (huv : u != v) {n : Nat} (hn : 2 <= n)
  proof: by
  classical
  obtain ⟨w, hw, h⟩ := exists_adj_isEdgeReachable_two huv (h.anti hn)
  have := @h {s(u, w)} (by simp)
  obtain ⟨w, p, hp₁, hp₂⟩ := adj_and_reachable_delete_edges_iff_exists_cycle.mp ⟨hw, this⟩
  exact ⟨p.rotate _ (p.fst_mem_support_of_mem_edges hp₂), hp₁.rotate _⟩

中文:
引理 存在_isCycle_of_two_le_isEdgeReachable
  结论: {u v : V} (huv : u != v) {n : 自然数} (hn : 2 <= n)
  证明: by
  classical
  obtain ⟨w, hw, h⟩ := exists_adj_isEdgeReachable_two huv (h.anti hn)
  have := @h {s(u, w)} (by simp)
  obtain ⟨w, p, hp₁, hp₂⟩ := adj_and_reachable_delete_edges_iff_exists_cycle.mp ⟨hw, this⟩
  exact ⟨p.rotate _ (p.fst_mem_support_of_mem_edges hp₂), hp₁.rotate _⟩

Depends on / 依赖: adj_and_reachable_delete_edges_iff_exists_cycle, adj_and_reachable_delete_edges_iff_exists_cycle.mp, classical, exists_adj_isEdgeReachable_two, fst_mem_support_of_mem_edges, h.anti, p.fst_mem_support_of_mem_edges, p.rotate, rotate
-/
lemma exists_isCycle_of_two_le_isEdgeReachable {u v : V} (huv : u != v) {n : Nat} (hn : 2 <= n)
    (h : G.IsEdgeReachable n u v) : exists w : G.Walk u u, w.IsCycle := by
  classical
  obtain ⟨w, hw, h⟩ := exists_adj_isEdgeReachable_two huv (h.anti hn)
  have := @h {s(u, w)} (by simp)
  obtain ⟨w, p, hp₁, hp₂⟩ := adj_and_reachable_delete_edges_iff_exists_cycle.mp ⟨hw, this⟩
  exact ⟨p.rotate _ (p.fst_mem_support_of_mem_edges hp₂), hp₁.rotate _⟩

/--
lemma `isAcyclic_iff_pairwise_not_isEdgeReachable_two` / 引理 `isAcyclic_iff_pairwise_not_isEdgeReachable_two`

English:
lemma isAcyclic_iff_pairwise_not_isEdgeReachable_two
  proof: by
  refine ⟨fun h _ _ hne he => ?_, fun h => ?_⟩
  · obtain ⟨w, hw⟩ := exists_isCycle_of_two_le_isEdgeReachable hne le_rfl he
    exact h w hw
  · rw [isAcyclic_iff_forall_isBridge]
    rintro ⟨u, v⟩ huv
    exact (isBridge_iff_not_isEdgeReachable_two huv).mpr (h huv.ne)

中文:
引理 isAcyclic_iff_pairwise_not_isEdgeReachable_two
  证明: by
  refine ⟨fun h _ _ hne he => ?_, fun h => ?_⟩
  · obtain ⟨w, hw⟩ := exists_isCycle_of_two_le_isEdgeReachable hne le_rfl he
    exact h w hw
  · rw [isAcyclic_iff_forall_isBridge]
    rintro ⟨u, v⟩ huv
    exact (isBridge_iff_not_isEdgeReachable_two huv).mpr (h huv.ne)

Depends on / 依赖: exists_isCycle_of_two_le_isEdgeReachable, huv.ne, isAcyclic_iff_forall_isBridge, isBridge_iff_not_isEdgeReachable_two, le_rfl
-/
lemma isAcyclic_iff_pairwise_not_isEdgeReachable_two :
    G.IsAcyclic ↔ Pairwise (¬G.IsEdgeReachable 2 · ·) := by
  refine ⟨fun h _ _ hne he => ?_, fun h => ?_⟩
  · obtain ⟨w, hw⟩ := exists_isCycle_of_two_le_isEdgeReachable hne le_rfl he
    exact h w hw
  · rw [isAcyclic_iff_forall_isBridge]
    rintro ⟨u, v⟩ huv
    exact (isBridge_iff_not_isEdgeReachable_two huv).mpr (h huv.ne)

/--
theorem `isAcyclic_iff_free_cycleGraph` / 定理 `isAcyclic_iff_free_cycleGraph`

English:
theorem isAcyclic_iff_free_cycleGraph
  statement: G.IsAcyclic ↔ forall n >= 3, (cycleGraph n).Free G
  proof: by
  refine ⟨fun h n hn hle => ?_, fun h v p hcyc => h p.length hcyc.three_le_length ?_⟩
.mp hle · have ⟨v, p, hcyc, hlen⟩ := cycleGraph_isContained_iff hn
    exact h p hcyc
.mpr ⟨v, p, hcyc, rfl⟩ · exact cycleGraph_isContained_iff hcyc.three_le_length

中文:
定理 isAcyclic_iff_free_cycleGraph
  结论: G.IsAcyclic ↔ 对任意 n >= 3, (cycleGraph n).自由 G
  证明: by
  refine ⟨fun h n hn hle => ?_, fun h v p hcyc => h p.length hcyc.three_le_length ?_⟩
.mp hle · have ⟨v, p, hcyc, hlen⟩ := cycleGraph_isContained_iff hn
    exact h p hcyc
.mpr ⟨v, p, hcyc, rfl⟩ · exact cycleGraph_isContained_iff hcyc.three_le_length

Depends on / 依赖: cycleGraph_isContained_iff, hcyc.three_le_length, length, p.length, three_le_length
-/
theorem isAcyclic_iff_free_cycleGraph : G.IsAcyclic ↔ forall n >= 3, (cycleGraph n).Free G := by
  refine ⟨fun h n hn hle => ?_, fun h v p hcyc => h p.length hcyc.three_le_length ?_⟩
.mp hle · have ⟨v, p, hcyc, hlen⟩ := cycleGraph_isContained_iff hn
    exact h p hcyc
.mpr ⟨v, p, hcyc, rfl⟩ · exact cycleGraph_isContained_iff hcyc.three_le_length

/--
theorem `IsAcyclic.cliqueFree` / 定理 `IsAcyclic.cliqueFree`

English:
theorem IsAcyclic.cliqueFree
  given: (h : G.IsAcyclic) {n : Nat} (hn : 3 <= n)
  statement: G.CliqueFree n
  proof: by
.not_right.mpr fun hle => ?_ refine not_cliqueFree_iff_top_isContained n
exact isAcyclic_iff_free_cycleGraph.mp h n hn hle.trans' .of_le le_top

中文:
定理 IsAcyclic.cliqueFree
  条件: (h : G.IsAcyclic) {n : 自然数} (hn : 3 <= n)
  结论: G.CliqueFree n
  证明: by
.not_right.mpr fun hle => ?_ refine not_cliqueFree_iff_top_isContained n
exact isAcyclic_iff_free_cycleGraph.mp h n hn hle.trans' .of_le le_top

Depends on / 依赖: hle.trans, isAcyclic_iff_free_cycleGraph, isAcyclic_iff_free_cycleGraph.mp, le_top, not_cliqueFree_iff_top_isContained, not_right, not_right.mpr, of_le
-/
theorem IsAcyclic.cliqueFree (h : G.IsAcyclic) {n : Nat} (hn : 3 <= n) : G.CliqueFree n := by
.not_right.mpr fun hle => ?_ refine not_cliqueFree_iff_top_isContained n
exact isAcyclic_iff_free_cycleGraph.mp h n hn hle.trans' .of_le le_top

end SimpleGraph
