/-
Copyright (c) 2020 Alena Gusakov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alena Gusakov, Arthur Paulino, Kyle Miller, Pim Otte
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
public import Mathlib.Combinatorics.SimpleGraph.Operations
public import Mathlib.Data.Set.Card.Arithmetic
public import Mathlib.Data.Set.Functor

/-!
# Matchings

A *matching* for a simple graph is a set of disjoint pairs of adjacent vertices, and the set of all
the vertices in a matching is called its *support* (and sometimes the vertices in the support are
said to be *saturated* by the matching). A *perfect matching* is a matching whose support contains
every vertex of the graph.

In this module, we represent a matching as a subgraph whose vertices are each incident to at most
one edge, and the edges of the subgraph represent the paired vertices.

## Main definitions

* `SimpleGraph.Subgraph.IsMatching`: `M.IsMatching` means that `M` is a matching of its
  underlying graph.

* `SimpleGraph.Subgraph.IsPerfectMatching` defines when a subgraph `M` of a simple graph is a
  perfect matching, denoted `M.IsPerfectMatching`.

* `SimpleGraph.IsMatchingFree` means that a graph `G` has no perfect matchings.

* `SimpleGraph.IsCycles` means that a graph consists of cycles (including cycles of length 0,
  also known as isolated vertices)

* `SimpleGraph.IsAlternating` means that edges in a graph `G` are alternatingly
  included and not included in some other graph `G'`

## TODO

* Define an `other` function and prove useful results about it (https://leanprover.zulipchat.com/#narrow/stream/252551-graph-theory/topic/matchings/near/266205863)

* Provide a bicoloring for matchings (https://leanprover.zulipchat.com/#narrow/stream/252551-graph-theory/topic/matchings/near/265495120)

* Tutte's Theorem
-/

@[expose] public section

assert_not_exists Field TwoSidedIdeal

open Function

namespace SimpleGraph
variable {V W : Type*} {G G' : SimpleGraph V} {M M' : Subgraph G} {u v w : V}

namespace Subgraph

/--
Definition of `IsMatching` / `IsMatching` 的定义

English:
definition IsMatching
  signature: (M : Subgraph G)
  body: forall ⦃v⦄, v in M.verts -> exists! w, M.Adj v w

中文:
定义 IsMatching
  签名: (M : 子图 G)
  定义体: forall ⦃v⦄, v in M.verts -> exists! w, M.Adj v w

Depends on / 依赖: M.Adj, M.verts
-/
def IsMatching (M : Subgraph G) : Prop := forall ⦃v⦄, v in M.verts -> exists! w, M.Adj v w

/--
Definition of `IsMatching.toEdge` / `IsMatching.toEdge` 的定义

English:
definition IsMatching.toEdge
  signature: (h : M.IsMatching) (v : M.verts)
  body: ⟨s(v, (h v.property).choose), (h v.property).choose_spec.1⟩

中文:
定义 IsMatching.toEdge
  签名: (h : M.IsMatching) (v : M.verts)
  定义体: ⟨s(v, (h v.property).choose), (h v.property).choose_spec.1⟩

Depends on / 依赖: choose_spec, property, v.property
-/
noncomputable def IsMatching.toEdge (h : M.IsMatching) (v : M.verts) : M.edgeSet :=
  ⟨s(v, (h v.property).choose), (h v.property).choose_spec.1⟩

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `IsMatching.toEdge_eq_of_adj` / 定理 `IsMatching.toEdge_eq_of_adj`

English:
theorem IsMatching.toEdge_eq_of_adj
  given: (h : M.IsMatching) (hvw : M.Adj v w)
  proof: by
  rw [IsMatching.toEdge]; rw [Subtype.mk_eq_mk]; rw [← h hvw.fst_mem |>.choose_spec.right w hvw]

中文:
定理 IsMatching.toEdge_eq_of_adj
  条件: (h : M.IsMatching) (hvw : M.伴随 v w)
  证明: by
  rw [IsMatching.toEdge]; rw [Subtype.mk_eq_mk]; rw [← h hvw.fst_mem |>.choose_spec.right w hvw]

Depends on / 依赖: IsMatching, IsMatching.toEdge, Subtype, Subtype.mk_eq_mk, choose_spec, choose_spec.right, fst_mem, hvw.fst_mem, mk_eq_mk, toEdge
-/
theorem IsMatching.toEdge_eq_of_adj (h : M.IsMatching) (hvw : M.Adj v w) :
    h.toEdge ⟨v, hvw.fst_mem⟩ = ⟨s(v, w), hvw⟩ := by
  rw [IsMatching.toEdge]; rw [Subtype.mk_eq_mk]; rw [← h hvw.fst_mem |>.choose_spec.right w hvw]

/--
theorem `IsMatching.toEdge.surjective` / 定理 `IsMatching.toEdge.surjective`

English:
theorem IsMatching.toEdge.surjective
  given: (h : M.IsMatching)
  statement: Surjective h.toEdge
  proof: by
  rintro ⟨⟨x, y⟩, he⟩
  exact ⟨⟨x, M.edge_vert he⟩, h.toEdge_eq_of_adj he⟩

中文:
定理 IsMatching.toEdge.surjective
  条件: (h : M.IsMatching)
  结论: 满射 h.toEdge
  证明: by
  rintro ⟨⟨x, y⟩, he⟩
  exact ⟨⟨x, M.edge_vert he⟩, h.toEdge_eq_of_adj he⟩

Depends on / 依赖: M.edge_vert, edge_vert, h.toEdge_eq_of_adj, toEdge_eq_of_adj
-/
theorem IsMatching.toEdge.surjective (h : M.IsMatching) : Surjective h.toEdge := by
  rintro ⟨⟨x, y⟩, he⟩
  exact ⟨⟨x, M.edge_vert he⟩, h.toEdge_eq_of_adj he⟩

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `IsMatching.toEdge_eq_toEdge_of_adj` / 定理 `IsMatching.toEdge_eq_toEdge_of_adj`

English:
theorem IsMatching.toEdge_eq_toEdge_of_adj
  given: (h : M.IsMatching) (ha : M.Adj v w)
  proof: by
  rw [h.toEdge_eq_of_adj ha]; rw [h.toEdge_eq_of_adj ha.symm]; rw [Subtype.mk_eq_mk]; rw [Sym2.eq_swap]

中文:
定理 IsMatching.toEdge_eq_toEdge_of_adj
  条件: (h : M.IsMatching) (ha : M.伴随 v w)
  证明: by
  rw [h.toEdge_eq_of_adj ha]; rw [h.toEdge_eq_of_adj ha.symm]; rw [Subtype.mk_eq_mk]; rw [Sym2.eq_swap]

Depends on / 依赖: Subtype, Subtype.mk_eq_mk, Sym2.eq_swap, eq_swap, h.toEdge_eq_of_adj, ha.symm, mk_eq_mk, toEdge_eq_of_adj
-/
theorem IsMatching.toEdge_eq_toEdge_of_adj (h : M.IsMatching) (ha : M.Adj v w) :
    h.toEdge ⟨v, ha.fst_mem⟩ = h.toEdge ⟨w, ha.snd_mem⟩ := by
  rw [h.toEdge_eq_of_adj ha]; rw [h.toEdge_eq_of_adj ha.symm]; rw [Subtype.mk_eq_mk]; rw [Sym2.eq_swap]

/--
theorem `IsMatching.mem_coe_toEdge` / 定理 `IsMatching.mem_coe_toEdge`

English:
theorem IsMatching.mem_coe_toEdge
  given: (h : M.IsMatching) {v : V} (hv : v in M.verts)
  proof: .choose, rfl⟩ ⟨h hv

中文:
定理 IsMatching.mem_coe_toEdge
  条件: (h : M.IsMatching) {v : V} (hv : v in M.verts)
  证明: .choose, rfl⟩ ⟨h hv
-/
theorem IsMatching.mem_coe_toEdge (h : M.IsMatching) {v : V} (hv : v in M.verts) :
    v in (h.toEdge ⟨v, hv⟩ : Sym2 V) :=
.choose, rfl⟩ ⟨h hv

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `IsMatching.toEdge_preimage_singleton` / 定理 `IsMatching.toEdge_preimage_singleton`

English:
theorem IsMatching.toEdge_preimage_singleton
  given: (h : M.IsMatching) (huv : M.Adj u v)
  proof: by
  refine Set.ext fun w => ⟨fun hw => ?_, fun hw => ?_⟩
  · grind [h.mem_coe_toEdge w.property]
  · rcases hw with rfl | rfl
    · simp [h.toEdge_eq_of_adj huv]
    · simp [h.toEdge_eq_of_adj huv.symm]

中文:
定理 IsMatching.toEdge_preimage_singleton
  条件: (h : M.IsMatching) (huv : M.伴随 u v)
  证明: by
  refine Set.ext fun w => ⟨fun hw => ?_, fun hw => ?_⟩
  · grind [h.mem_coe_toEdge w.property]
  · rcases hw with rfl | rfl
    · simp [h.toEdge_eq_of_adj huv]
    · simp [h.toEdge_eq_of_adj huv.symm]

Depends on / 依赖: Set.ext, h.mem_coe_toEdge, h.toEdge_eq_of_adj, huv.symm, mem_coe_toEdge, property, toEdge_eq_of_adj, w.property
-/
theorem IsMatching.toEdge_preimage_singleton (h : M.IsMatching) (huv : M.Adj u v) :
    h.toEdge ⁻¹' {⟨s(u, v), huv⟩} = {⟨u, huv.fst_mem⟩, ⟨v, huv.snd_mem⟩} := by
  refine Set.ext fun w => ⟨fun hw => ?_, fun hw => ?_⟩
  · grind [h.mem_coe_toEdge w.property]
  · rcases hw with rfl | rfl
    · simp [h.toEdge_eq_of_adj huv]
    · simp [h.toEdge_eq_of_adj huv.symm]

/--
lemma `IsMatching.map_ofLE` / 引理 `IsMatching.map_ofLE`

English:
lemma IsMatching.map_ofLE
  given: (h : M.IsMatching) (hGG' : G <= G')
  proof: by
  intro _ hv
.mp hv obtain ⟨_, hv, hv'⟩ := Set.mem_image _ _ _
  obtain ⟨w, hw⟩ := h hv
  use w
  simpa using hv' ▸ hw

中文:
引理 IsMatching.map_ofLE
  条件: (h : M.IsMatching) (hGG' : G <= G')
  证明: by
  intro _ hv
.mp hv obtain ⟨_, hv, hv'⟩ := Set.mem_image _ _ _
  obtain ⟨w, hw⟩ := h hv
  use w
  simpa using hv' ▸ hw

Depends on / 依赖: Set.mem_image, mem_image
-/
lemma IsMatching.map_ofLE (h : M.IsMatching) (hGG' : G <= G') :
    (M.map (Hom.ofLE hGG')).IsMatching := by
  intro _ hv
.mp hv obtain ⟨_, hv, hv'⟩ := Set.mem_image _ _ _
  obtain ⟨w, hw⟩ := h hv
  use w
  simpa using hv' ▸ hw

/--
lemma `IsMatching.eq_of_adj_left` / 引理 `IsMatching.eq_of_adj_left`

English:
lemma IsMatching.eq_of_adj_left
  given: (hM : M.IsMatching) (huv : M.Adj u v) (huw : M.Adj u w)
  statement: v = w
  proof: (hM <| M.edge_vert huv).unique huv huw

中文:
引理 IsMatching.eq_of_adj_left
  条件: (hM : M.IsMatching) (huv : M.伴随 u v) (huw : M.伴随 u w)
  结论: v = w
  证明: (hM <| M.edge_vert huv).unique huv huw

Depends on / 依赖: M.edge_vert, edge_vert, unique
-/
lemma IsMatching.eq_of_adj_left (hM : M.IsMatching) (huv : M.Adj u v) (huw : M.Adj u w) : v = w :=
  (hM <| M.edge_vert huv).unique huv huw

/--
lemma `IsMatching.eq_of_adj_right` / 引理 `IsMatching.eq_of_adj_right`

English:
lemma IsMatching.eq_of_adj_right
  given: (hM : M.IsMatching) (huw : M.Adj u w) (hvw : M.Adj v w)
  statement: u = v
  proof: hM.eq_of_adj_left huw.symm hvw.symm

中文:
引理 IsMatching.eq_of_adj_right
  条件: (hM : M.IsMatching) (huw : M.伴随 u w) (hvw : M.伴随 v w)
  结论: u = v
  证明: hM.eq_of_adj_left huw.symm hvw.symm

Depends on / 依赖: eq_of_adj_left, hM.eq_of_adj_left, huw.symm, hvw.symm
-/
lemma IsMatching.eq_of_adj_right (hM : M.IsMatching) (huw : M.Adj u w) (hvw : M.Adj v w) : u = v :=
  hM.eq_of_adj_left huw.symm hvw.symm

/--
lemma `IsMatching.not_adj_left_of_ne` / 引理 `IsMatching.not_adj_left_of_ne`

English:
lemma IsMatching.not_adj_left_of_ne
  given: (hM : M.IsMatching) (hvw : v != w) (huv : M.Adj u v)
  proof: fun huw => hvw hM.eq_of_adj_left huv huw

中文:
引理 IsMatching.not_adj_left_of_ne
  条件: (hM : M.IsMatching) (hvw : v != w) (huv : M.伴随 u v)
  证明: fun huw => hvw hM.eq_of_adj_left huv huw

Depends on / 依赖: eq_of_adj_left, hM.eq_of_adj_left
-/
lemma IsMatching.not_adj_left_of_ne (hM : M.IsMatching) (hvw : v != w) (huv : M.Adj u v) :
¬M.Adj u w := fun huw => hvw hM.eq_of_adj_left huv huw

/--
lemma `IsMatching.not_adj_right_of_ne` / 引理 `IsMatching.not_adj_right_of_ne`

English:
lemma IsMatching.not_adj_right_of_ne
  given: (hM : M.IsMatching) (huv : u != v) (huw : M.Adj u w)
  proof: fun hvw => huv hM.eq_of_adj_right huw hvw

中文:
引理 IsMatching.not_adj_right_of_ne
  条件: (hM : M.IsMatching) (huv : u != v) (huw : M.伴随 u w)
  证明: fun hvw => huv hM.eq_of_adj_right huw hvw

Depends on / 依赖: eq_of_adj_right, hM.eq_of_adj_right
-/
lemma IsMatching.not_adj_right_of_ne (hM : M.IsMatching) (huv : u != v) (huw : M.Adj u w) :
¬M.Adj v w := fun hvw => huv hM.eq_of_adj_right huw hvw

/--
lemma `IsMatching.sup` / 引理 `IsMatching.sup`

English:
lemma IsMatching.sup
  statement: (hM : M.IsMatching) (hM' : M'.IsMatching)
  proof: by
  intro v hv
  have aux {N N' : Subgraph G} (hN : N.IsMatching) (hd : Disjoint N.support N'.support)
    (hmN : v in N.verts) : exists! w, (N ⊔ N').Adj v w := by
    obtain ⟨w, hw⟩ := hN hmN
    use w
    refine ⟨sup_adj.mpr (.inl hw.1), ?_⟩
    intro y hy
    cases hy with
    | inl h => exact h

中文:
引理 IsMatching.上确界
  结论: (hM : M.IsMatching) (hM' : M'.IsMatching)
  证明: by
  intro v hv
  have aux {N N' : Subgraph G} (hN : N.IsMatching) (hd : Disjoint N.support N'.support)
    (hmN : v in N.verts) : exists! w, (N ⊔ N').Adj v w := by
    obtain ⟨w, hw⟩ := hN hmN
    use w
    refine ⟨sup_adj.mpr (.inl hw.1), ?_⟩
    intro y hy
    cases hy with
    | inl h => exact h

Depends on / 依赖: Disjoint, IsMatching, N.IsMatching, N.support, N.verts, Set.disjoint_left, Set.mem_or_mem_of_mem_union, Subgraph, disjoint_left, mem_or_mem_of_mem_union, mem_support, sup_adj, sup_adj.mpr, sup_comm, support
-/
lemma IsMatching.sup (hM : M.IsMatching) (hM' : M'.IsMatching)
    (hd : Disjoint M.support M'.support) : (M ⊔ M').IsMatching := by
  intro v hv
  have aux {N N' : Subgraph G} (hN : N.IsMatching) (hd : Disjoint N.support N'.support)
    (hmN : v in N.verts) : exists! w, (N ⊔ N').Adj v w := by
    obtain ⟨w, hw⟩ := hN hmN
    use w
    refine ⟨sup_adj.mpr (.inl hw.1), ?_⟩
    intro y hy
    cases hy with
    | inl h => exact hw.2 y h
    | inr h =>
      rw [Set.disjoint_left] at hd
      simpa [(mem_support _).mpr ⟨w, hw.1⟩, (mem_support _).mpr ⟨y, h⟩] using @hd v
  cases Set.mem_or_mem_of_mem_union hv with
  | inl hmM => exact aux hM hd hmM
  | inr hmM' =>
    rw [sup_comm]
    exact aux hM' (Disjoint.symm hd) hmM'

/--
lemma `IsMatching.iSup` / 引理 `IsMatching.iSup`

English:
lemma IsMatching.iSup
  statement: {ι : Sort _} {f : ι -> Subgraph G} (hM : (i : ι) -> (f i).IsMatching)
  proof: by
  intro v hv
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (verts_iSup ▸ hv)
  obtain ⟨w, hw⟩ := hM i hi
  use w
  refine ⟨iSup_adj.mpr ⟨i, hw.1⟩, ?_⟩
  intro y hy
  obtain ⟨i', hi'⟩ := iSup_adj.mp hy
  by_cases heq : i = i'
  · exact hw.2 y (heq.symm ▸ hi')
  · have := hd heq
    simp only [Set.disjoint

中文:
引理 IsMatching.iSup
  结论: {ι : 类型层 _} {f : ι -> 子图 G} (hM : (i : ι) -> (f i).IsMatching)
  证明: by
  intro v hv
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (verts_iSup ▸ hv)
  obtain ⟨w, hw⟩ := hM i hi
  use w
  refine ⟨iSup_adj.mpr ⟨i, hw.1⟩, ?_⟩
  intro y hy
  obtain ⟨i', hi'⟩ := iSup_adj.mp hy
  by_cases heq : i = i'
  · exact hw.2 y (heq.symm ▸ hi')
  · have := hd heq
    simp only [Set.disjoint

Depends on / 依赖: Set.disjoint_left, Set.mem_iUnion.mp, disjoint_left, heq.symm, iSup_adj, iSup_adj.mp, iSup_adj.mpr, mem_iUnion, mem_support, verts_iSup
-/
lemma IsMatching.iSup {ι : Sort _} {f : ι -> Subgraph G} (hM : (i : ι) -> (f i).IsMatching)
    (hd : Pairwise fun i j => Disjoint (f i).support (f j).support) :
    (⨆ i, f i).IsMatching := by
  intro v hv
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (verts_iSup ▸ hv)
  obtain ⟨w, hw⟩ := hM i hi
  use w
  refine ⟨iSup_adj.mpr ⟨i, hw.1⟩, ?_⟩
  intro y hy
  obtain ⟨i', hi'⟩ := iSup_adj.mp hy
  by_cases heq : i = i'
  · exact hw.2 y (heq.symm ▸ hi')
  · have := hd heq
    simp only [Set.disjoint_left] at this
    simpa [(mem_support _).mpr ⟨w, hw.1⟩, (mem_support _).mpr ⟨y, hi'⟩] using @this v

/--
lemma `IsMatching.subgraphOfAdj` / 引理 `IsMatching.subgraphOfAdj`

English:
lemma IsMatching.subgraphOfAdj
  given: (h : G.Adj v w)
  statement: (G.subgraphOfAdj h).IsMatching
  proof: by
  intro _ hv
  rw [subgraphOfAdj_verts]; rw [Set.mem_insert_iff]; rw [Set.mem_singleton_iff] at hv
  cases hv with
  | inl => use w; aesop
  | inr => use v; aesop

中文:
引理 IsMatching.subgraphOfAdj
  条件: (h : G.伴随 v w)
  结论: (G.subgraphOfAdj h).IsMatching
  证明: by
  intro _ hv
  rw [subgraphOfAdj_verts]; rw [Set.mem_insert_iff]; rw [Set.mem_singleton_iff] at hv
  cases hv with
  | inl => use w; aesop
  | inr => use v; aesop

Depends on / 依赖: Set.mem_insert_iff, Set.mem_singleton_iff, mem_insert_iff, mem_singleton_iff, subgraphOfAdj_verts
-/
lemma IsMatching.subgraphOfAdj (h : G.Adj v w) : (G.subgraphOfAdj h).IsMatching := by
  intro _ hv
  rw [subgraphOfAdj_verts]; rw [Set.mem_insert_iff]; rw [Set.mem_singleton_iff] at hv
  cases hv with
  | inl => use w; aesop
  | inr => use v; aesop

/--
lemma `IsMatching.coeSubgraph` / 引理 `IsMatching.coeSubgraph`

English:
lemma IsMatching.coeSubgraph
  given: {G' : Subgraph G} {M : Subgraph G'.coe} (hM : M.IsMatching)
  proof: by
  intro _ hv
obtain ⟨w, hw⟩ := hM Set.mem_of_mem_image_val (Subgraph.verts_coeSubgraph M).symm ▸ hv
  use w
  refine ⟨?_, fun y hy => ?_⟩
· obtain ⟨v, hv⟩ := (Set.mem_image _ _ _).mp (Subgraph.verts_coeSubgraph M).symm ▸ hv
    simp only [coeSubgraph_adj, Subtype.coe_eta, Subtype.coe_prop, exists

中文:
引理 IsMatching.coeSubgraph
  条件: {G' : 子图 G} {M : 子图 G'.coe} (hM : M.IsMatching)
  证明: by
  intro _ hv
obtain ⟨w, hw⟩ := hM Set.mem_of_mem_image_val (Subgraph.verts_coeSubgraph M).symm ▸ hv
  use w
  refine ⟨?_, fun y hy => ?_⟩
· obtain ⟨v, hv⟩ := (Set.mem_image _ _ _).mp (Subgraph.verts_coeSubgraph M).symm ▸ hv
    simp only [coeSubgraph_adj, Subtype.coe_eta, Subtype.coe_prop, exists

Depends on / 依赖: Set.mem_image, Set.mem_of_mem_image_val, Subgraph, Subgraph.verts_coeSubgraph, Subtype, Subtype.coe_eta, Subtype.coe_prop, coeSubgraph_adj, coe_eta, coe_prop, exists_const, mem_image, mem_of_mem_image_val, verts_coeSubgraph
-/
lemma IsMatching.coeSubgraph {G' : Subgraph G} {M : Subgraph G'.coe} (hM : M.IsMatching) :
    (Subgraph.coeSubgraph M).IsMatching := by
  intro _ hv
obtain ⟨w, hw⟩ := hM Set.mem_of_mem_image_val (Subgraph.verts_coeSubgraph M).symm ▸ hv
  use w
  refine ⟨?_, fun y hy => ?_⟩
· obtain ⟨v, hv⟩ := (Set.mem_image _ _ _).mp (Subgraph.verts_coeSubgraph M).symm ▸ hv
    simp only [coeSubgraph_adj, Subtype.coe_eta, Subtype.coe_prop, exists_const]
    exact ⟨hv.2 ▸ v.2, hw.1⟩
  · obtain ⟨_, hw', hvw⟩ := (coeSubgraph_adj _ _ _).mp hy
    rw [← hw.2 ⟨y]; rw [hw'⟩ hvw]

/--
lemma `IsMatching.exists_of_disjoint_sets_of_equiv` / 引理 `IsMatching.exists_of_disjoint_sets_of_equiv`

English:
lemma IsMatching.exists_of_disjoint_sets_of_equiv
  statement: {s t : Set V} (h : Disjoint s t)
  proof: by
  use {
    verts := s union t
    Adj := fun v w => (exists h : v in s, f ⟨v, h⟩ = w) ∨ (exists h : w in s, f ⟨w, h⟩ = v)
    adj_sub := by
      intro v w h
      obtain (⟨hv, rfl⟩ | ⟨hw, rfl⟩) := h
      · exact hadj ⟨v, _⟩
      · exact (hadj ⟨w, _⟩).symm
    edge_vert := by grind }
  simp on

中文:
引理 IsMatching.存在_of_disjoint_sets_of_equiv
  结论: {s t : 集合 V} (h : Disjoint s t)
  证明: by
  use {
    verts := s union t
    Adj := fun v w => (exists h : v in s, f ⟨v, h⟩ = w) ∨ (exists h : w in s, f ⟨w, h⟩ = v)
    adj_sub := by
      intro v w h
      obtain (⟨hv, rfl⟩ | ⟨hw, rfl⟩) := h
      · exact hadj ⟨v, _⟩
      · exact (hadj ⟨w, _⟩).symm
    edge_vert := by grind }
  simp on

Depends on / 依赖: IsMatching, Set.mem_union, Subgraph, Subgraph.IsMatching, adj_sub, coe_pro, edge_vert, exists_const, exists_true_left, h.ne_of_mem, mem_union, ne_of_mem, true_and, true_or
-/
lemma IsMatching.exists_of_disjoint_sets_of_equiv {s t : Set V} (h : Disjoint s t)
    (f : s ≃ t) (hadj : forall v : s, G.Adj v (f v)) :
    exists M : Subgraph G, M.verts = s union t ∧ M.IsMatching := by
  use {
    verts := s union t
    Adj := fun v w => (exists h : v in s, f ⟨v, h⟩ = w) ∨ (exists h : w in s, f ⟨w, h⟩ = v)
    adj_sub := by
      intro v w h
      obtain (⟨hv, rfl⟩ | ⟨hw, rfl⟩) := h
      · exact hadj ⟨v, _⟩
      · exact (hadj ⟨w, _⟩).symm
    edge_vert := by grind }
  simp only [Subgraph.IsMatching, Set.mem_union, true_and]
  intro v hv
  rcases hv with hl | hr
  · use f ⟨v, hl⟩
    simp only [hl, exists_const, true_or, exists_true_left, true_and]
    rintro y (rfl | ⟨hys, rfl⟩)
    · rfl
    · exact (h.ne_of_mem hl (f ⟨y, hys⟩).coe_prop rfl).elim
  · use f.symm ⟨v, hr⟩
    simp only [Subtype.coe_eta, Equiv.apply_symm_apply, Subtype.coe_prop, exists_const, or_true,
      true_and]
    rintro y (⟨hy, rfl⟩ | ⟨hy, rfl⟩)
    · exact (h.ne_of_mem hy hr rfl).elim
    · simp

/--
lemma `IsMatching.map` / 引理 `IsMatching.map`

English:
lemma IsMatching.map
  statement: {G' : SimpleGraph W} {M : Subgraph G} (f : G ->g G')
  proof: by
  rintro _ ⟨v, hv, rfl⟩
  obtain ⟨v', hv'⟩ := hM hv
  use f v'
  refine ⟨⟨v, v', hv'.1, rfl, rfl⟩, ?_⟩
  rintro _ ⟨w, w', hw, hw', rfl⟩
  cases hf hw'.symm
  rw [hv'.2 w' hw]

@[simp]

中文:
引理 IsMatching.map
  结论: {G' : 简单图 W} {M : 子图 G} (f : G ->g G')
  证明: by
  rintro _ ⟨v, hv, rfl⟩
  obtain ⟨v', hv'⟩ := hM hv
  use f v'
  refine ⟨⟨v, v', hv'.1, rfl, rfl⟩, ?_⟩
  rintro _ ⟨w, w', hw, hw', rfl⟩
  cases hf hw'.symm
  rw [hv'.2 w' hw]

@[simp]
-/
protected lemma IsMatching.map {G' : SimpleGraph W} {M : Subgraph G} (f : G ->g G')
    (hf : Injective f) (hM : M.IsMatching) : (M.map f).IsMatching := by
  rintro _ ⟨v, hv, rfl⟩
  obtain ⟨v', hv'⟩ := hM hv
  use f v'
  refine ⟨⟨v, v', hv'.1, rfl, rfl⟩, ?_⟩
  rintro _ ⟨w, w', hw, hw', rfl⟩
  cases hf hw'.symm
  rw [hv'.2 w' hw]

@[simp]
/--
lemma `Iso.isMatching_map` / 引理 `Iso.isMatching_map`

English:
lemma Iso.isMatching_map
  given: {G' : SimpleGraph W} {M : Subgraph G} (f : G ≃g G')
  proof: by simpa [← map_comp] using h.map f.symm.toHom f.symm.injective
  mpr := .map f.toHom f.injective

中文:
引理 同构.isMatching_map
  条件: {G' : 简单图 W} {M : 子图 G} (f : G ≃g G')
  证明: by simpa [← map_comp] using h.map f.symm.toHom f.symm.injective
  mpr := .map f.toHom f.injective

Depends on / 依赖: f.injective, f.symm.injective, f.symm.toHom, f.toHom, h.map, injective, map_comp
-/
lemma Iso.isMatching_map {G' : SimpleGraph W} {M : Subgraph G} (f : G ≃g G') :
    (M.map f.toHom).IsMatching ↔ M.IsMatching where
  mp h := by simpa [← map_comp] using h.map f.symm.toHom f.symm.injective
  mpr := .map f.toHom f.injective

/--
theorem `IsMatching.verts_eq_biUnion_edgeSet` / 定理 `IsMatching.verts_eq_biUnion_edgeSet`

English:
theorem IsMatching.verts_eq_biUnion_edgeSet
  given: {M : G.Subgraph} (h : M.IsMatching)
  proof: by
  refine Set.ext fun v => .trans ⟨fun hv => ?_, fun ⟨e, he, hv⟩ => ?_⟩ Set.mem_iUnion₂.symm
  · have ⟨u, he, _⟩ := h hv
    exact ⟨s(v, u), he, Sym2.mem_mk_left ..⟩
  · exact mem_verts_of_mem_edge he hv

中文:
定理 IsMatching.verts_eq_biUnion_edgeSet
  条件: {M : G.子图} (h : M.IsMatching)
  证明: by
  refine Set.ext fun v => .trans ⟨fun hv => ?_, fun ⟨e, he, hv⟩ => ?_⟩ Set.mem_iUnion₂.symm
  · have ⟨u, he, _⟩ := h hv
    exact ⟨s(v, u), he, Sym2.mem_mk_left ..⟩
  · exact mem_verts_of_mem_edge he hv

Depends on / 依赖: Set.ext, Set.mem_iUnion, Sym2.mem_mk_left, mem_mk_left, mem_verts_of_mem_edge
-/
theorem IsMatching.verts_eq_biUnion_edgeSet {M : G.Subgraph} (h : M.IsMatching) :
    M.verts = ⋃ e in M.edgeSet, (e : Set V) := by
  refine Set.ext fun v => .trans ⟨fun hv => ?_, fun ⟨e, he, hv⟩ => ?_⟩ Set.mem_iUnion₂.symm
  · have ⟨u, he, _⟩ := h hv
    exact ⟨s(v, u), he, Sym2.mem_mk_left ..⟩
  · exact mem_verts_of_mem_edge he hv

/--
theorem `IsMatching.injOn_edgeSet` / 定理 `IsMatching.injOn_edgeSet`

English:
theorem IsMatching.injOn_edgeSet
  statement: (Set.ofPred IsMatching).InjOn (edgeSet (G := G))
  proof: by
refine fun M₁ h₁ M₂ h₂ h => Subgraph.ext ?_ .mp h Sym2.fromRel_eq_fromRel_iff_eq ..
  rw [h₁.verts_eq_biUnion_edgeSet]; rw [h₂.verts_eq_biUnion_edgeSet]; rw [h]

中文:
定理 IsMatching.injOn_edgeSet
  结论: (集合.ofPred IsMatching).单射限制 (edgeSet (G := G))
  证明: by
refine fun M₁ h₁ M₂ h₂ h => Subgraph.ext ?_ .mp h Sym2.fromRel_eq_fromRel_iff_eq ..
  rw [h₁.verts_eq_biUnion_edgeSet]; rw [h₂.verts_eq_biUnion_edgeSet]; rw [h]

Depends on / 依赖: Subgraph, Subgraph.ext, Sym2.fromRel_eq_fromRel_iff_eq, fromRel_eq_fromRel_iff_eq, verts_eq_biUnion_edgeSet
-/
theorem IsMatching.injOn_edgeSet : (Set.ofPred IsMatching).InjOn (edgeSet (G := G)) := by
refine fun M₁ h₁ M₂ h₂ h => Subgraph.ext ?_ .mp h Sym2.fromRel_eq_fromRel_iff_eq ..
  rw [h₁.verts_eq_biUnion_edgeSet]; rw [h₂.verts_eq_biUnion_edgeSet]; rw [h]

/--
theorem `IsMatching.strictMonoOn_edgeSet` / 定理 `IsMatching.strictMonoOn_edgeSet`

English:
theorem IsMatching.strictMonoOn_edgeSet
  statement: StrictMonoOn (edgeSet (G := G)) (Set.ofPred IsMatching)
  proof: .strictMonoOn_of_injOn injOn_edgeSet edgeSet_monotone.monotoneOn _

中文:
定理 IsMatching.strictMonoOn_edgeSet
  结论: StrictMonoOn (edgeSet (G := G)) (集合.ofPred IsMatching)
  证明: .strictMonoOn_of_injOn injOn_edgeSet edgeSet_monotone.monotoneOn _

Depends on / 依赖: IsMatching, Set.ofPred, ofPred
-/
theorem IsMatching.strictMonoOn_edgeSet : StrictMonoOn (edgeSet (G := G)) (Set.ofPred IsMatching) :=
.strictMonoOn_of_injOn injOn_edgeSet edgeSet_monotone.monotoneOn _

/--
Definition of `IsPerfectMatching` / `IsPerfectMatching` 的定义

English:
definition IsPerfectMatching
  signature: (M : G.Subgraph)
  body: M.IsMatching ∧ M.IsSpanning

中文:
定义 IsPerfectMatching
  签名: (M : G.子图)
  定义体: M.IsMatching ∧ M.IsSpanning

Depends on / 依赖: IsMatching, IsSpanning, M.IsMatching, M.IsSpanning
-/
def IsPerfectMatching (M : G.Subgraph) : Prop := M.IsMatching ∧ M.IsSpanning

/--
theorem `IsMatching.support_eq_verts` / 定理 `IsMatching.support_eq_verts`

English:
theorem IsMatching.support_eq_verts
  given: (h : M.IsMatching)
  statement: M.support = M.verts
  proof: by
  refine M.support_subset_verts.antisymm fun v hv => ?_
  obtain ⟨w, hvw, -⟩ := h hv
  exact ⟨_, hvw⟩

中文:
定理 IsMatching.support_eq_verts
  条件: (h : M.IsMatching)
  结论: M.support = M.verts
  证明: by
  refine M.support_subset_verts.antisymm fun v hv => ?_
  obtain ⟨w, hvw, -⟩ := h hv
  exact ⟨_, hvw⟩

Depends on / 依赖: M.support_subset_verts.antisymm, antisymm, support_subset_verts
-/
theorem IsMatching.support_eq_verts (h : M.IsMatching) : M.support = M.verts := by
  refine M.support_subset_verts.antisymm fun v hv => ?_
  obtain ⟨w, hvw, -⟩ := h hv
  exact ⟨_, hvw⟩

/--
theorem `isMatching_iff_forall_degree` / 定理 `isMatching_iff_forall_degree`

English:
theorem isMatching_iff_forall_degree
  given: [forall v, Fintype (M.neighborSet v)]
  proof: by
  simp only [degree_eq_one_iff_existsUnique_adj, IsMatching]

中文:
定理 isMatching_iff_对任意_degree
  条件: [对任意 v, 有限类型 (M.neighborSet v)]
  证明: by
  simp only [degree_eq_one_iff_existsUnique_adj, IsMatching]

Depends on / 依赖: IsMatching, degree_eq_one_iff_existsUnique_adj
-/
theorem isMatching_iff_forall_degree [forall v, Fintype (M.neighborSet v)] :
    M.IsMatching ↔ forall v : V, v in M.verts -> M.degree v = 1 := by
  simp only [degree_eq_one_iff_existsUnique_adj, IsMatching]

/--
theorem `IsMatching.even_card` / 定理 `IsMatching.even_card`

English:
theorem IsMatching.even_card
  given: [Fintype M.verts] (h : M.IsMatching)
  statement: Even M.verts.toFinset.card
  proof: by
  classical
  rw [isMatching_iff_forall_degree] at h
  use M.coe.edgeFinset.card
  rw [← two_mul]; rw [← M.coe.sum_degrees_eq_twice_card_edges]
  simp [h, Finset.card_univ]

中文:
定理 IsMatching.even_card
  条件: [有限类型 M.verts] (h : M.IsMatching)
  结论: Even M.verts.toFinset.card
  证明: by
  classical
  rw [isMatching_iff_forall_degree] at h
  use M.coe.edgeFinset.card
  rw [← two_mul]; rw [← M.coe.sum_degrees_eq_twice_card_edges]
  simp [h, Finset.card_univ]

Depends on / 依赖: Finset, Finset.card_univ, M.coe.edgeFinset.card, M.coe.sum_degrees_eq_twice_card_edges, card_univ, classical, edgeFinset, isMatching_iff_forall_degree, sum_degrees_eq_twice_card_edges, two_mul
-/
theorem IsMatching.even_card [Fintype M.verts] (h : M.IsMatching) : Even M.verts.toFinset.card := by
  classical
  rw [isMatching_iff_forall_degree] at h
  use M.coe.edgeFinset.card
  rw [← two_mul]; rw [← M.coe.sum_degrees_eq_twice_card_edges]
  simp [h, Finset.card_univ]

/--
theorem `isPerfectMatching_iff` / 定理 `isPerfectMatching_iff`

English:
theorem isPerfectMatching_iff
  statement: M.IsPerfectMatching ↔ forall v, exists! w, M.Adj v w
  proof: by
  refine ⟨?_, fun hm => ⟨fun v _ => hm v, fun v => ?_⟩⟩
  · rintro ⟨hm, hs⟩ v
    exact hm (hs v)
  · obtain ⟨w, hw, -⟩ := hm v
    exact M.edge_vert hw

中文:
定理 isPerfectMatching_iff
  结论: M.IsPerfectMatching ↔ 对任意 v, 存在! w, M.伴随 v w
  证明: by
  refine ⟨?_, fun hm => ⟨fun v _ => hm v, fun v => ?_⟩⟩
  · rintro ⟨hm, hs⟩ v
    exact hm (hs v)
  · obtain ⟨w, hw, -⟩ := hm v
    exact M.edge_vert hw

Depends on / 依赖: M.edge_vert, edge_vert
-/
theorem isPerfectMatching_iff : M.IsPerfectMatching ↔ forall v, exists! w, M.Adj v w := by
  refine ⟨?_, fun hm => ⟨fun v _ => hm v, fun v => ?_⟩⟩
  · rintro ⟨hm, hs⟩ v
    exact hm (hs v)
  · obtain ⟨w, hw, -⟩ := hm v
    exact M.edge_vert hw

/--
theorem `isPerfectMatching_iff_forall_degree` / 定理 `isPerfectMatching_iff_forall_degree`

English:
theorem isPerfectMatching_iff_forall_degree
  given: [forall v, Fintype (M.neighborSet v)]
  proof: by
  simp [degree_eq_one_iff_existsUnique_adj, isPerfectMatching_iff]

中文:
定理 isPerfectMatching_iff_对任意_degree
  条件: [对任意 v, 有限类型 (M.neighborSet v)]
  证明: by
  simp [degree_eq_one_iff_existsUnique_adj, isPerfectMatching_iff]

Depends on / 依赖: degree_eq_one_iff_existsUnique_adj, isPerfectMatching_iff
-/
theorem isPerfectMatching_iff_forall_degree [forall v, Fintype (M.neighborSet v)] :
    M.IsPerfectMatching ↔ forall v, M.degree v = 1 := by
  simp [degree_eq_one_iff_existsUnique_adj, isPerfectMatching_iff]

/--
theorem `IsPerfectMatching.even_card` / 定理 `IsPerfectMatching.even_card`

English:
theorem IsPerfectMatching.even_card
  given: [Fintype V] (h : M.IsPerfectMatching)
  proof: by
  classical
  simpa only [h.2.card_verts] using IsMatching.even_card h.1

中文:
定理 IsPerfectMatching.even_card
  条件: [有限类型 V] (h : M.IsPerfectMatching)
  证明: by
  classical
  simpa only [h.2.card_verts] using IsMatching.even_card h.1

Depends on / 依赖: IsMatching, IsMatching.even_card, card_verts, classical, even_card
-/
theorem IsPerfectMatching.even_card [Fintype V] (h : M.IsPerfectMatching) :
    Even (Fintype.card V) := by
  classical
  simpa only [h.2.card_verts] using IsMatching.even_card h.1

/--
lemma `IsMatching.induce_connectedComponent` / 引理 `IsMatching.induce_connectedComponent`

English:
lemma IsMatching.induce_connectedComponent
  given: (h : M.IsMatching) (c : ConnectedComponent G)
  proof: by
  intro _ hv
  obtain ⟨hv, rfl⟩ := hv
  obtain ⟨w, hvw, hw⟩ := h hv
  use w
  simpa [hv, hvw, M.edge_vert hvw.symm, (M.adj_sub hvw).symm.reachable] using fun _ _ _ => hw _

中文:
引理 IsMatching.induce_connectedComponent
  条件: (h : M.IsMatching) (c : ConnectedComponent G)
  证明: by
  intro _ hv
  obtain ⟨hv, rfl⟩ := hv
  obtain ⟨w, hvw, hw⟩ := h hv
  use w
  simpa [hv, hvw, M.edge_vert hvw.symm, (M.adj_sub hvw).symm.reachable] using fun _ _ _ => hw _

Depends on / 依赖: M.adj_sub, M.edge_vert, adj_sub, edge_vert, hvw.symm, reachable, symm.reachable
-/
lemma IsMatching.induce_connectedComponent (h : M.IsMatching) (c : ConnectedComponent G) :
    (M.induce (M.verts inter c.supp)).IsMatching := by
  intro _ hv
  obtain ⟨hv, rfl⟩ := hv
  obtain ⟨w, hvw, hw⟩ := h hv
  use w
  simpa [hv, hvw, M.edge_vert hvw.symm, (M.adj_sub hvw).symm.reachable] using fun _ _ _ => hw _

/--
lemma `IsPerfectMatching.induce_connectedComponent_isMatching` / 引理 `IsPerfectMatching.induce_connectedComponent_isMatching`

English:
lemma IsPerfectMatching.induce_connectedComponent_isMatching
  statement: (h : M.IsPerfectMatching)
  proof: by
  simpa [h.2.verts_eq_univ] using h.1.induce_connectedComponent c

@[simp]

中文:
引理 IsPerfectMatching.induce_connectedComponent_isMatching
  结论: (h : M.IsPerfectMatching)
  证明: by
  simpa [h.2.verts_eq_univ] using h.1.induce_connectedComponent c

@[simp]

Depends on / 依赖: induce_connectedComponent, verts_eq_univ
-/
lemma IsPerfectMatching.induce_connectedComponent_isMatching (h : M.IsPerfectMatching)
    (c : ConnectedComponent G) : (M.induce c.supp).IsMatching := by
  simpa [h.2.verts_eq_univ] using h.1.induce_connectedComponent c

@[simp]
/--
lemma `IsPerfectMatching.toSubgraph_iff` / 引理 `IsPerfectMatching.toSubgraph_iff`

English:
lemma IsPerfectMatching.toSubgraph_iff
  given: (h : M.spanningCoe <= G')
  proof: by
  simp only [isPerfectMatching_iff, toSubgraph_adj, spanningCoe_adj]

中文:
引理 IsPerfectMatching.toSubgraph_iff
  条件: (h : M.spanningCoe <= G')
  证明: by
  simp only [isPerfectMatching_iff, toSubgraph_adj, spanningCoe_adj]

Depends on / 依赖: isPerfectMatching_iff, spanningCoe_adj, toSubgraph_adj
-/
lemma IsPerfectMatching.toSubgraph_iff (h : M.spanningCoe <= G') :
    (G'.toSubgraph M.spanningCoe h).IsPerfectMatching ↔ M.IsPerfectMatching := by
  simp only [isPerfectMatching_iff, toSubgraph_adj, spanningCoe_adj]

end Subgraph

/--
lemma `IsClique.even_iff_exists_isMatching` / 引理 `IsClique.even_iff_exists_isMatching`

English:
lemma IsClique.even_iff_exists_isMatching
  statement: {u : Set V} (hc : G.IsClique u)
  proof: by
  refine ⟨fun h => ?_, by
    rintro ⟨M, rfl, hMr⟩
    simpa [Set.ncard_eq_toFinset_card _ hu, Set.toFinite_toFinset,
      ← Set.toFinset_card] using! @hMr.even_card _ _ _ hu.fintype⟩
  obtain ⟨t, u, rfl, hd, hcard⟩ := Set.exists_union_disjoint_ncard_eq_of_even h
  obtain ⟨f⟩ : Nonempty (t ≃ u) 

中文:
引理 IsClique.even_iff_存在_isMatching
  结论: {u : 集合 V} (hc : G.IsClique u)
  证明: by
  refine ⟨fun h => ?_, by
    rintro ⟨M, rfl, hMr⟩
    simpa [Set.ncard_eq_toFinset_card _ hu, Set.toFinite_toFinset,
      ← Set.toFinset_card] using! @hMr.even_card _ _ _ hu.fintype⟩
  obtain ⟨t, u, rfl, hd, hcard⟩ := Set.exists_union_disjoint_ncard_eq_of_even h
  obtain ⟨f⟩ : Nonempty (t ≃ u) 

Depends on / 依赖: Cardinal, Cardinal.eq, IsMatching, Nat.cast, Nonempty, Set.exists_union_disjoint_ncard_eq_of_even, Set.finite_union.mp, Set.ncard_eq_toFinset_card, Set.toFinite_toFinset, Set.toFinset_card, Subgraph, Subgraph.IsMatching.exists_of_disjoint_sets_of_equiv, cast_ncard, even_card, exists_of_disjoint_sets_of_equiv, exists_union_disjoint_ncard_eq_of_even, finite_union, fintype, hMr.even_card, hu.fintype
-/
lemma IsClique.even_iff_exists_isMatching {u : Set V} (hc : G.IsClique u)
    (hu : u.Finite) : Even u.ncard ↔ exists (M : Subgraph G), M.verts = u ∧ M.IsMatching := by
  refine ⟨fun h => ?_, by
    rintro ⟨M, rfl, hMr⟩
    simpa [Set.ncard_eq_toFinset_card _ hu, Set.toFinite_toFinset,
      ← Set.toFinset_card] using! @hMr.even_card _ _ _ hu.fintype⟩
  obtain ⟨t, u, rfl, hd, hcard⟩ := Set.exists_union_disjoint_ncard_eq_of_even h
  obtain ⟨f⟩ : Nonempty (t ≃ u) := by
    rw [← Cardinal.eq]; rw [← t.cast_ncard (Set.finite_union.mp hu).1]; rw [← u.cast_ncard (Set.finite_union.mp hu).2]
    exact congrArg Nat.cast hcard
  exact Subgraph.IsMatching.exists_of_disjoint_sets_of_equiv hd f
fun v => hc (by simp) (by simp) hd.ne_of_mem (by simp) (by simp)

namespace ConnectedComponent

section Finite

/--
lemma `even_card_of_isPerfectMatching` / 引理 `even_card_of_isPerfectMatching`

English:
lemma even_card_of_isPerfectMatching
  statement: [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
  proof: by
  #adaptation_note /-- https://github.com/leanprover/lean4/pull/5020
  some instances that use the chain of coercions
  `[SetLike X], X → Set α → Sort _` are
  blocked by the discrimination tree. This can be fixed by redeclaring the instance for `X`
  using the double coercion but the proper fix 

中文:
引理 even_card_of_isPerfectMatching
  结论: [有限类型 V] [DecidableEq V] [DecidableRel G.伴随]
  证明: by
  #adaptation_note /-- https://github.com/leanprover/lean4/pull/5020
  some instances that use the chain of coercions
  `[SetLike X], X → Set α → Sort _` are
  blocked by the discrimination tree. This can be fixed by redeclaring the instance for `X`
  using the double coercion but the proper fix 

Depends on / 依赖: DecidablePred, G.instDecidableMemSupp, M.induce, SetLike, adaptation_note, blocked, c.supp, coercion, coercions, discrimination, double, even_card, github, github.com, hM.induce_connectedComponent_isMatching, induce, induce_connectedComponent_isMatching, instDecidableMemSupp, instance, instances
-/
lemma even_card_of_isPerfectMatching [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (c : ConnectedComponent G) (hM : M.IsPerfectMatching) :
    Even (Fintype.card c.supp) := by
  #adaptation_note /-- https://github.com/leanprover/lean4/pull/5020
  some instances that use the chain of coercions
  `[SetLike X], X → Set α → Sort _` are
  blocked by the discrimination tree. This can be fixed by redeclaring the instance for `X`
  using the double coercion but the proper fix seems to avoid the double coercion. -/
  let : DecidablePred fun x => x in (M.induce c.supp).verts := fun a => G.instDecidableMemSupp c a
  have := (hM.induce_connectedComponent_isMatching c).even_card
  simp only [Subgraph.induce_verts, Set.toFinset_card] at this
  exact this

/--
lemma `odd_matches_node_outside` / 引理 `odd_matches_node_outside`

English:
lemma odd_matches_node_outside
  statement: [Finite V] {u : Set V}
  proof: by
  by_contra! h
  have hMmatch : (M.induce c.val.supp).IsMatching := by
    intro v hv
    obtain ⟨w, hw⟩ := hM.1 (hM.2 v)
    obtain ⟨⟨v', hv'⟩, ⟨hv, rfl⟩⟩ := hv
    use w
    have hwnu : w ∉ u := fun hw' => h w hw' ⟨v', hv'⟩ (hw.1) hv
    refine ⟨⟨⟨⟨v', hv'⟩, hv, rfl⟩, ?_, hw.1⟩, fun _ hy => hw.

中文:
引理 odd_matches_node_outside
  结论: [有限 V] {u : 集合 V}
  证明: by
  by_contra! h
  have hMmatch : (M.induce c.val.supp).IsMatching := by
    intro v hv
    obtain ⟨w, hw⟩ := hM.1 (hM.2 v)
    obtain ⟨⟨v', hv'⟩, ⟨hv, rfl⟩⟩ := hv
    use w
    have hwnu : w ∉ u := fun hw' => h w hw' ⟨v', hv'⟩ (hw.1) hv
    refine ⟨⟨⟨⟨v', hv'⟩, hv, rfl⟩, ?_, hw.1⟩, fun _ hy => hw.

Depends on / 依赖: ConnectedComponent, ConnectedComponent.mem_coe_supp_of_adj, IsMatching, M.induce, Set.mem_sdiff, Set.mem_univ, Subgraph, Subgraph.induce_adj, Subgraph.induce_verts, Subgraph.verts_top, c.val.supp, hMmatch, induce, induce_adj, induce_verts, mem_coe_supp_of_adj, mem_sdiff, mem_univ, not_false, true_and
-/
lemma odd_matches_node_outside [Finite V] {u : Set V}
    (hM : M.IsPerfectMatching) (c : (Subgraph.deleteVerts ⊤ u).coe.oddComponents) :
    existsᵉ (w in u) (v : ((⊤ : G.Subgraph).deleteVerts u).verts), M.Adj v w ∧ v in c.val.supp := by
  by_contra! h
  have hMmatch : (M.induce c.val.supp).IsMatching := by
    intro v hv
    obtain ⟨w, hw⟩ := hM.1 (hM.2 v)
    obtain ⟨⟨v', hv'⟩, ⟨hv, rfl⟩⟩ := hv
    use w
    have hwnu : w ∉ u := fun hw' => h w hw' ⟨v', hv'⟩ (hw.1) hv
    refine ⟨⟨⟨⟨v', hv'⟩, hv, rfl⟩, ?_, hw.1⟩, fun _ hy => hw.2 _ hy.2.2⟩
    apply ConnectedComponent.mem_coe_supp_of_adj ⟨⟨v', hv'⟩, ⟨hv, rfl⟩⟩ ⟨by trivial, hwnu⟩
    simp only [Subgraph.induce_verts, Subgraph.verts_top, Set.mem_sdiff, Set.mem_univ, true_and,
      Subgraph.induce_adj, hwnu, not_false_eq_true, and_self, Subgraph.top_adj, M.adj_sub hw.1,
      and_true] at hv' ⊢
    trivial
  apply Nat.not_even_iff_odd.2 c.prop
  have : Fintype ↑(Subgraph.induce M (Subtype.val '' supp c.val)).verts := Fintype.ofFinite _
  classical
  have := Fintype.ofFinite c.val.supp
  simpa [Finset.card_image_of_injective] using hMmatch.even_card

end Finite
end ConnectedComponent

/--
Definition of `IsMatchingFree` / `IsMatchingFree` 的定义

English:
definition IsMatchingFree
  signature: (G : SimpleGraph V)
  body: forall M : Subgraph G, ¬ M.IsPerfectMatching

中文:
定义 IsMatchingFree
  签名: (G : 简单图 V)
  定义体: forall M : Subgraph G, ¬ M.IsPerfectMatching

Depends on / 依赖: IsPerfectMatching, M.IsPerfectMatching, Subgraph
-/
def IsMatchingFree (G : SimpleGraph V) := forall M : Subgraph G, ¬ M.IsPerfectMatching

/--
lemma `IsMatchingFree.mono` / 引理 `IsMatchingFree.mono`

English:
lemma IsMatchingFree.mono
  given: {G G' : SimpleGraph V} (h : G <= G') (hmf : G'.IsMatchingFree)
  proof: by
  intro x
  by_contra! hc
  apply hmf (x.map (SimpleGraph.Hom.ofLE h))
  refine ⟨hc.1.map_ofLE h, ?_⟩
  intro v
  simp only [Subgraph.map_verts, Hom.coe_ofLE, id_eq, Set.image_id']
  exact hc.2 v

中文:
引理 IsMatchingFree.mono
  条件: {G G' : 简单图 V} (h : G <= G') (hmf : G'.IsMatchingFree)
  证明: by
  intro x
  by_contra! hc
  apply hmf (x.map (SimpleGraph.Hom.ofLE h))
  refine ⟨hc.1.map_ofLE h, ?_⟩
  intro v
  simp only [Subgraph.map_verts, Hom.coe_ofLE, id_eq, Set.image_id']
  exact hc.2 v

Depends on / 依赖: Hom.coe_ofLE, Set.image_id, SimpleGraph, SimpleGraph.Hom.ofLE, Subgraph, Subgraph.map_verts, coe_ofLE, id_eq, image_id, map_ofLE, map_verts, x.map
-/
lemma IsMatchingFree.mono {G G' : SimpleGraph V} (h : G <= G') (hmf : G'.IsMatchingFree) :
    G.IsMatchingFree := by
  intro x
  by_contra! hc
  apply hmf (x.map (SimpleGraph.Hom.ofLE h))
  refine ⟨hc.1.map_ofLE h, ?_⟩
  intro v
  simp only [Subgraph.map_verts, Hom.coe_ofLE, id_eq, Set.image_id']
  exact hc.2 v

/--
lemma `exists_maximal_isMatchingFree` / 引理 `exists_maximal_isMatchingFree`

English:
lemma exists_maximal_isMatchingFree
  given: [Finite V] (h : G.IsMatchingFree)
  proof: by
  simp_rw [← @not_forall_not _ Subgraph.IsPerfectMatching]
  obtain ⟨Gmax, hGmax⟩ := Finite.exists_le_maximal h
  exact ⟨Gmax, ⟨hGmax.1, ⟨hGmax.2.prop, fun _ h' => hGmax.2.not_prop_of_gt h'⟩⟩⟩

中文:
引理 存在_maximal_isMatchingFree
  条件: [有限 V] (h : G.IsMatchingFree)
  证明: by
  simp_rw [← @not_forall_not _ Subgraph.IsPerfectMatching]
  obtain ⟨Gmax, hGmax⟩ := Finite.exists_le_maximal h
  exact ⟨Gmax, ⟨hGmax.1, ⟨hGmax.2.prop, fun _ h' => hGmax.2.not_prop_of_gt h'⟩⟩⟩

Depends on / 依赖: Finite, Finite.exists_le_maximal, IsPerfectMatching, Subgraph, Subgraph.IsPerfectMatching, exists_le_maximal, not_forall_not, not_prop_of_gt, simp_rw
-/
lemma exists_maximal_isMatchingFree [Finite V] (h : G.IsMatchingFree) :
    exists Gmax : SimpleGraph V, G <= Gmax ∧ Gmax.IsMatchingFree ∧
      forall G', G' > Gmax -> exists M : Subgraph G', M.IsPerfectMatching := by
  simp_rw [← @not_forall_not _ Subgraph.IsPerfectMatching]
  obtain ⟨Gmax, hGmax⟩ := Finite.exists_le_maximal h
  exact ⟨Gmax, ⟨hGmax.1, ⟨hGmax.2.prop, fun _ h' => hGmax.2.not_prop_of_gt h'⟩⟩⟩

/--
Definition of `IsCycles` / `IsCycles` 的定义

English:
definition IsCycles
  signature: (G : SimpleGraph V)
  body: forall ⦃v⦄, (G.neighborSet v).Nonempty -> (G.neighborSet v).ncard = 2

中文:
定义 IsCycles
  签名: (G : 简单图 V)
  定义体: forall ⦃v⦄, (G.neighborSet v).Nonempty -> (G.neighborSet v).ncard = 2

Depends on / 依赖: G.neighborSet, Nonempty, neighborSet
-/
def IsCycles (G : SimpleGraph V) := forall ⦃v⦄, (G.neighborSet v).Nonempty -> (G.neighborSet v).ncard = 2

/--
lemma `IsCycles.other_adj_of_adj` / 引理 `IsCycles.other_adj_of_adj`

English:
lemma IsCycles.other_adj_of_adj
  given: (h : G.IsCycles) (hadj : G.Adj v w)
  proof: by
  simp_rw [← SimpleGraph.mem_neighborSet] at hadj ⊢
  have := h ⟨w, hadj⟩
  obtain ⟨w', hww'⟩ := (G.neighborSet v).exists_ne_of_one_lt_ncard (by lia) w
  exact ⟨w', ⟨hww'.2.symm, hww'.1⟩⟩

中文:
引理 IsCycles.other_adj_of_adj
  条件: (h : G.IsCycles) (hadj : G.伴随 v w)
  证明: by
  simp_rw [← SimpleGraph.mem_neighborSet] at hadj ⊢
  have := h ⟨w, hadj⟩
  obtain ⟨w', hww'⟩ := (G.neighborSet v).exists_ne_of_one_lt_ncard (by lia) w
  exact ⟨w', ⟨hww'.2.symm, hww'.1⟩⟩

Depends on / 依赖: G.neighborSet, SimpleGraph, SimpleGraph.mem_neighborSet, exists_ne_of_one_lt_ncard, mem_neighborSet, neighborSet, simp_rw
-/
lemma IsCycles.other_adj_of_adj (h : G.IsCycles) (hadj : G.Adj v w) :
    exists w', w != w' ∧ G.Adj v w' := by
  simp_rw [← SimpleGraph.mem_neighborSet] at hadj ⊢
  have := h ⟨w, hadj⟩
  obtain ⟨w', hww'⟩ := (G.neighborSet v).exists_ne_of_one_lt_ncard (by lia) w
  exact ⟨w', ⟨hww'.2.symm, hww'.1⟩⟩

/--
lemma `IsCycles.existsUnique_ne_adj` / 引理 `IsCycles.existsUnique_ne_adj`

English:
lemma IsCycles.existsUnique_ne_adj
  given: (h : G.IsCycles) (hadj : G.Adj v w)
  proof: by
  obtain ⟨w', ⟨hww, hww'⟩⟩ := h.other_adj_of_adj hadj
  use w'
  refine ⟨⟨hww, hww'⟩, ?_⟩
  intro y ⟨hwy, hwy'⟩
  obtain ⟨x, y', hxy'⟩ := Set.ncard_eq_two.mp (h ⟨w, hadj⟩)
  simp_rw [← SimpleGraph.mem_neighborSet] at *
  grind

中文:
引理 IsCycles.存在Unique_ne_adj
  条件: (h : G.IsCycles) (hadj : G.伴随 v w)
  证明: by
  obtain ⟨w', ⟨hww, hww'⟩⟩ := h.other_adj_of_adj hadj
  use w'
  refine ⟨⟨hww, hww'⟩, ?_⟩
  intro y ⟨hwy, hwy'⟩
  obtain ⟨x, y', hxy'⟩ := Set.ncard_eq_two.mp (h ⟨w, hadj⟩)
  simp_rw [← SimpleGraph.mem_neighborSet] at *
  grind

Depends on / 依赖: Set.ncard_eq_two.mp, SimpleGraph, SimpleGraph.mem_neighborSet, h.other_adj_of_adj, mem_neighborSet, ncard_eq_two, other_adj_of_adj, simp_rw
-/
lemma IsCycles.existsUnique_ne_adj (h : G.IsCycles) (hadj : G.Adj v w) :
    exists! w', w != w' ∧ G.Adj v w' := by
  obtain ⟨w', ⟨hww, hww'⟩⟩ := h.other_adj_of_adj hadj
  use w'
  refine ⟨⟨hww, hww'⟩, ?_⟩
  intro y ⟨hwy, hwy'⟩
  obtain ⟨x, y', hxy'⟩ := Set.ncard_eq_two.mp (h ⟨w, hadj⟩)
  simp_rw [← SimpleGraph.mem_neighborSet] at *
  grind

/--
lemma `IsCycles.toSimpleGraph` / 引理 `IsCycles.toSimpleGraph`

English:
lemma IsCycles.toSimpleGraph
  given: (c : G.ConnectedComponent) (h : G.IsCycles)
  proof: by
  intro v ⟨w, hw⟩
  rw [mem_neighborSet]; rw [c.adj_spanningCoe_toSimpleGraph] at hw
  rw [← h ⟨w]; rw [hw.2⟩]
  congr 1
  ext w'
  simp only [mem_neighborSet, c.adj_spanningCoe_toSimpleGraph, hw, true_and]

中文:
引理 IsCycles.toSimpleGraph
  条件: (c : G.ConnectedComponent) (h : G.IsCycles)
  证明: by
  intro v ⟨w, hw⟩
  rw [mem_neighborSet]; rw [c.adj_spanningCoe_toSimpleGraph] at hw
  rw [← h ⟨w]; rw [hw.2⟩]
  congr 1
  ext w'
  simp only [mem_neighborSet, c.adj_spanningCoe_toSimpleGraph, hw, true_and]

Depends on / 依赖: adj_spanningCoe_toSimpleGraph, c.adj_spanningCoe_toSimpleGraph, mem_neighborSet, true_and
-/
lemma IsCycles.toSimpleGraph (c : G.ConnectedComponent) (h : G.IsCycles) :
    c.toSimpleGraph.spanningCoe.IsCycles := by
  intro v ⟨w, hw⟩
  rw [mem_neighborSet]; rw [c.adj_spanningCoe_toSimpleGraph] at hw
  rw [← h ⟨w]; rw [hw.2⟩]
  congr 1
  ext w'
  simp only [mem_neighborSet, c.adj_spanningCoe_toSimpleGraph, hw, true_and]

/--
lemma `Walk.IsCycle.isCycles_spanningCoe_toSubgraph` / 引理 `Walk.IsCycle.isCycles_spanningCoe_toSubgraph`

English:
lemma Walk.IsCycle.isCycles_spanningCoe_toSubgraph
  given: {u : V} {p : G.Walk u u} (hpc : p.IsCycle)
  proof: by
  intro v hv
  apply hpc.ncard_neighborSet_toSubgraph_eq_two
  obtain ⟨_, hw⟩ := hv
exact p.mem_verts_toSubgraph.mp p.toSubgraph.edge_vert hw

中文:
引理 途径.是环.isCycles_spanningCoe_toSubgraph
  条件: {u : V} {p : G.途径 u u} (hpc : p.是环)
  证明: by
  intro v hv
  apply hpc.ncard_neighborSet_toSubgraph_eq_two
  obtain ⟨_, hw⟩ := hv
exact p.mem_verts_toSubgraph.mp p.toSubgraph.edge_vert hw

Depends on / 依赖: edge_vert, hpc.ncard_neighborSet_toSubgraph_eq_two, mem_verts_toSubgraph, ncard_neighborSet_toSubgraph_eq_two, p.mem_verts_toSubgraph.mp, p.toSubgraph.edge_vert, toSubgraph
-/
lemma Walk.IsCycle.isCycles_spanningCoe_toSubgraph {u : V} {p : G.Walk u u} (hpc : p.IsCycle) :
    p.toSubgraph.spanningCoe.IsCycles := by
  intro v hv
  apply hpc.ncard_neighborSet_toSubgraph_eq_two
  obtain ⟨_, hw⟩ := hv
exact p.mem_verts_toSubgraph.mp p.toSubgraph.edge_vert hw

set_option backward.isDefEq.respectTransparency false in
/--
lemma `Walk.IsPath.isCycles_spanningCoe_toSubgraph_sup_edge` / 引理 `Walk.IsPath.isCycles_spanningCoe_toSubgraph_sup_edge`

English:
lemma Walk.IsPath.isCycles_spanningCoe_toSubgraph_sup_edge
  statement: {u v} {p : G.Walk u v} (hp : p.IsPath)
  proof: by
  let c := (p.mapLe (OrderTop.le_top G)).cons (by simp [h.symm] : (completeGraph V).Adj v u)
  have : p.toSubgraph.spanningCoe ⊔ edge v u = c.toSubgraph.spanningCoe := by
    ext w x
    simp only [sup_adj, Subgraph.spanningCoe_adj, completeGraph_eq_top, edge_adj, c,
      Walk.toSubgraph, Subgra

中文:
引理 途径.是道路.isCycles_spanningCoe_toSubgraph_sup_edge
  结论: {u v} {p : G.途径 u v} (hp : p.是道路)
  证明: by
  let c := (p.mapLe (OrderTop.le_top G)).cons (by simp [h.symm] : (completeGraph V).Adj v u)
  have : p.toSubgraph.spanningCoe ⊔ edge v u = c.toSubgraph.spanningCoe := by
    ext w x
    simp only [sup_adj, Subgraph.spanningCoe_adj, completeGraph_eq_top, edge_adj, c,
      Walk.toSubgraph, Subgra

Depends on / 依赖: IsCycle, IsCycle.isCycles_spanningCoe_toSubgraph, OrderTop, OrderTop.le_top, Subgraph, Subgraph.spanningCoe_adj, Subgraph.sup_adj, Walk.cons_isCycle_iff, Walk.toSubgraph, adj_toSubgraph_mapLe, c.toSubgraph.spanningCoe, completeGraph, completeGraph_eq_top, cons_isCycle_iff, edge_adj, h.symm, isCycles_spanningCoe_toSubgraph, le_top, p.mapLe, p.toSubgraph.spanningCoe
-/
lemma Walk.IsPath.isCycles_spanningCoe_toSubgraph_sup_edge {u v} {p : G.Walk u v} (hp : p.IsPath)
    (h : u != v) (hs : s(v, u) ∉ p.edges) : (p.toSubgraph.spanningCoe ⊔ edge v u).IsCycles := by
  let c := (p.mapLe (OrderTop.le_top G)).cons (by simp [h.symm] : (completeGraph V).Adj v u)
  have : p.toSubgraph.spanningCoe ⊔ edge v u = c.toSubgraph.spanningCoe := by
    ext w x
    simp only [sup_adj, Subgraph.spanningCoe_adj, completeGraph_eq_top, edge_adj, c,
      Walk.toSubgraph, Subgraph.sup_adj, subgraphOfAdj_adj, adj_toSubgraph_mapLe]
    grind
  exact this ▸ IsCycle.isCycles_spanningCoe_toSubgraph (by simp [Walk.cons_isCycle_iff, c, hp, hs])

/--
lemma `Walk.IsCycle.adj_toSubgraph_iff_of_isCycles` / 引理 `Walk.IsCycle.adj_toSubgraph_iff_of_isCycles`

English:
lemma Walk.IsCycle.adj_toSubgraph_iff_of_isCycles
  statement: [LocallyFinite G] {u} {p : G.Walk u u}
  proof: by
  refine fun w => Subgraph.adj_iff_of_neighborSet_equiv (?_ : Nonempty _).some (Set.toFinite _)
  have := hp.ncard_neighborSet_toSubgraph_eq_two (by aesop)
  rw [← Cardinal.eq]; rw [← Set.cast_ncard (Set.toFinite _)]; rw [← Set.cast_ncard (finite_neighborSet_toSubgraph p)]; rw [hcyc
      (Set.No

中文:
引理 途径.是环.adj_toSubgraph_iff_of_isCycles
  结论: [局部有限 G] {u} {p : G.途径 u u}
  证明: by
  refine fun w => Subgraph.adj_iff_of_neighborSet_equiv (?_ : Nonempty _).some (Set.toFinite _)
  have := hp.ncard_neighborSet_toSubgraph_eq_two (by aesop)
  rw [← Cardinal.eq]; rw [← Set.cast_ncard (Set.toFinite _)]; rw [← Set.cast_ncard (finite_neighborSet_toSubgraph p)]; rw [hcyc
      (Set.No

Depends on / 依赖: Cardinal, Cardinal.eq, Nonempty, Set.Nonempty.mono, Set.cast_ncard, Set.nonempty_of_ncard_ne_zero, Set.toFinite, Subgraph, Subgraph.adj_iff_of_neighborSet_equiv, adj_iff_of_neighborSet_equiv, cast_ncard, finite_neighborSet_toSubgraph, hp.ncard_neighborSet_toSubgraph_eq_two, ncard_neighborSet_toSubgraph_eq_two, neighborSet_subset, nonempty_of_ncard_ne_zero, p.toSubgraph.neighborSet_subset, toFinite, toSubgraph
-/
lemma Walk.IsCycle.adj_toSubgraph_iff_of_isCycles [LocallyFinite G] {u} {p : G.Walk u u}
    (hp : p.IsCycle) (hcyc : G.IsCycles) (hv : v in p.toSubgraph.verts) :
    forall w, p.toSubgraph.Adj v w ↔ G.Adj v w := by
  refine fun w => Subgraph.adj_iff_of_neighborSet_equiv (?_ : Nonempty _).some (Set.toFinite _)
  have := hp.ncard_neighborSet_toSubgraph_eq_two (by aesop)
  rw [← Cardinal.eq]; rw [← Set.cast_ncard (Set.toFinite _)]; rw [← Set.cast_ncard (finite_neighborSet_toSubgraph p)]; rw [hcyc
      (Set.Nonempty.mono (p.toSubgraph.neighborSet_subset v) <|
Set.nonempty_of_ncard_ne_zero by simp [this]),
    this]

open scoped symmDiff

/--
lemma `Subgraph.IsPerfectMatching.symmDiff_isCycles` / 引理 `Subgraph.IsPerfectMatching.symmDiff_isCycles`

English:
lemma Subgraph.IsPerfectMatching.symmDiff_isCycles
  proof: by
  intro v
  obtain ⟨w, hw⟩ := hM.1 (hM.2 v)
  obtain ⟨w', hw'⟩ := hM'.1 (hM'.2 v)
  simp only [symmDiff_def, Set.ncard_eq_two, ne_eq, imp_iff_not_or, Set.not_nonempty_iff_eq_empty,
    Set.eq_empty_iff_forall_notMem, SimpleGraph.mem_neighborSet, SimpleGraph.sup_adj, sdiff_adj,
    spanningCoe_adj

中文:
引理 子图.IsPerfectMatching.symmDiff_isCycles
  证明: by
  intro v
  obtain ⟨w, hw⟩ := hM.1 (hM.2 v)
  obtain ⟨w', hw'⟩ := hM'.1 (hM'.2 v)
  simp only [symmDiff_def, Set.ncard_eq_two, ne_eq, imp_iff_not_or, Set.not_nonempty_iff_eq_empty,
    Set.eq_empty_iff_forall_notMem, SimpleGraph.mem_neighborSet, SimpleGraph.sup_adj, sdiff_adj,
    spanningCoe_adj

Depends on / 依赖: Set.eq_empty_iff_forall_notMem, Set.ncard_eq_two, Set.not_nonempty_iff_eq_empty, SimpleGraph, SimpleGraph.mem_neighborSet, SimpleGraph.sup_adj, eq_empty_iff_forall_notMem, imp_iff_not_or, mem_neighborSet, ncard_eq_two, ne_eq, not_and, not_nonempty_iff_eq_empty, not_not, not_or, sdiff_adj, spanningCoe_adj, sup_adj, symmDiff_def
-/
lemma Subgraph.IsPerfectMatching.symmDiff_isCycles
    {M : Subgraph G} {M' : Subgraph G'} (hM : M.IsPerfectMatching)
    (hM' : M'.IsPerfectMatching) : (M.spanningCoe ∆ M'.spanningCoe).IsCycles := by
  intro v
  obtain ⟨w, hw⟩ := hM.1 (hM.2 v)
  obtain ⟨w', hw'⟩ := hM'.1 (hM'.2 v)
  simp only [symmDiff_def, Set.ncard_eq_two, ne_eq, imp_iff_not_or, Set.not_nonempty_iff_eq_empty,
    Set.eq_empty_iff_forall_notMem, SimpleGraph.mem_neighborSet, SimpleGraph.sup_adj, sdiff_adj,
    spanningCoe_adj, not_or, not_and, not_not]
  by_cases hww' : w = w'
  · simp_all [← imp_iff_not_or]
  · right
    use w, w'
    aesop

/--
lemma `IsCycles.snd_of_mem_support_of_isPath_of_adj` / 引理 `IsCycles.snd_of_mem_support_of_isPath_of_adj`

English:
lemma IsCycles.snd_of_mem_support_of_isPath_of_adj
  statement: [Finite V] {v w w' : V}
  proof: by
  apply hp.snd_of_toSubgraph_adj
  rw [Walk.mem_support_iff_exists_getVert] at hw'
  obtain ⟨n, ⟨rfl, hnl⟩⟩ := hw'
  by_cases hn : n = 0 ∨ n = p.length
  · aesop
  have e : G.neighborSet (p.getVert n) ≃ p.toSubgraph.neighborSet (p.getVert n) := by
    refine @Classical.ofNonempty _ ?_
    rw [← C

中文:
引理 IsCycles.snd_of_mem_support_of_isPath_of_adj
  结论: [有限 V] {v w w' : V}
  证明: by
  apply hp.snd_of_toSubgraph_adj
  rw [Walk.mem_support_iff_exists_getVert] at hw'
  obtain ⟨n, ⟨rfl, hnl⟩⟩ := hw'
  by_cases hn : n = 0 ∨ n = p.length
  · aesop
  have e : G.neighborSet (p.getVert n) ≃ p.toSubgraph.neighborSet (p.getVert n) := by
    refine @Classical.ofNonempty _ ?_
    rw [← C

Depends on / 依赖: Cardinal, Cardinal.eq, Classical, Classical.ofNonempty, G.neighborSet, Set.cast_ncard, Set.nonempty_of_mem, Set.toFinite, Subgraph, Walk.mem_support_iff_exists_getVert, cast_ncard, getVert, hadj.symm, hp.ncard_neighborSet_toSubgraph_internal_eq_two, hp.snd_of_toSubgraph_adj, length, mem_support_iff_exists_getVert, ncard_neighborSet_toSubgraph_internal_eq_two, neighborSet, nonempty_of_mem
-/
lemma IsCycles.snd_of_mem_support_of_isPath_of_adj [Finite V] {v w w' : V}
    (hcyc : G.IsCycles) (p : G.Walk v w) (hw : w != w') (hw' : w' in p.support) (hp : p.IsPath)
    (hadj : G.Adj v w') : p.snd = w' := by
  apply hp.snd_of_toSubgraph_adj
  rw [Walk.mem_support_iff_exists_getVert] at hw'
  obtain ⟨n, ⟨rfl, hnl⟩⟩ := hw'
  by_cases hn : n = 0 ∨ n = p.length
  · aesop
  have e : G.neighborSet (p.getVert n) ≃ p.toSubgraph.neighborSet (p.getVert n) := by
    refine @Classical.ofNonempty _ ?_
    rw [← Cardinal.eq]; rw [← Set.cast_ncard (Set.toFinite _)]; rw [← Set.cast_ncard (Set.toFinite _)]; rw [hp.ncard_neighborSet_toSubgraph_internal_eq_two (by lia) (by lia)]; rw [hcyc (Set.nonempty_of_mem hadj.symm)]
  rw [Subgraph.adj_comm]; rw [Subgraph.adj_iff_of_neighborSet_equiv e (Set.toFinite _)]
  exact hadj.symm

/--
lemma `IsCycles.reachable_sdiff_toSubgraph_spanningCoe_aux` / 引理 `IsCycles.reachable_sdiff_toSubgraph_spanningCoe_aux`

English:
lemma IsCycles.reachable_sdiff_toSubgraph_spanningCoe_aux
  statement: [Finite V] {v w : V}
  proof: by
  -- Consider the case when p is nil
  by_cases hvw : v = w
  · subst hvw
    use .nil
  have hpn : ¬p.Nil := Walk.not_nil_of_ne hvw
  obtain ⟨w', ⟨hw'1, hw'2⟩, hwu⟩ := hcyc.existsUnique_ne_adj
    (p.toSubgraph_adj_snd hpn).adj_sub
  -- The edge (v, w) can't be in p, because then it would be the

中文:
引理 IsCycles.reachable_sdiff_toSubgraph_spanningCoe_aux
  结论: [有限 V] {v w : V}
  证明: by
  -- Consider the case when p is nil
  by_cases hvw : v = w
  · subst hvw
    use .nil
  have hpn : ¬p.Nil := Walk.not_nil_of_ne hvw
  obtain ⟨w', ⟨hw'1, hw'2⟩, hwu⟩ := hcyc.existsUnique_ne_adj
    (p.toSubgraph_adj_snd hpn).adj_sub
  -- The edge (v, w) can't be in p, because then it would be the
-/
private lemma IsCycles.reachable_sdiff_toSubgraph_spanningCoe_aux [Finite V] {v w : V}
    (hcyc : G.IsCycles) (p : G.Walk v w) (hp : p.IsPath) :
    (G \ p.toSubgraph.spanningCoe).Reachable w v := by
  -- Consider the case when p is nil
  by_cases hvw : v = w
  · subst hvw
    use .nil
  have hpn : ¬p.Nil := Walk.not_nil_of_ne hvw
  obtain ⟨w', ⟨hw'1, hw'2⟩, hwu⟩ := hcyc.existsUnique_ne_adj
    (p.toSubgraph_adj_snd hpn).adj_sub
  -- The edge (v, w) can't be in p, because then it would be the second node
  have hnpvw' : ¬ p.toSubgraph.Adj v w' := by
    intro h
    exact hw'1 (hp.snd_of_toSubgraph_adj h)
  -- If w = w', then the reachability can be proved with just one edge
  by_cases hww' : w = w'
  · subst hww'
    have : (G \ p.toSubgraph.spanningCoe).Adj w v := by
      simp only [sdiff_adj, Subgraph.spanningCoe_adj]
      exact ⟨hw'2.symm, fun h => hnpvw' h.symm⟩
    exact this.reachable
  -- Construct the walk needed recursively by extending p
  have hle : (G \ (p.cons hw'2.symm).toSubgraph.spanningCoe) <= (G \ p.toSubgraph.spanningCoe) := by
    apply sdiff_le_sdiff (by rfl) ?hcd
    simp
  have hp'p : (p.cons hw'2.symm).IsPath := by
    rw [Walk.cons_isPath_iff]
    refine ⟨hp, fun hw' => ?_⟩
    exact hw'1 (hcyc.snd_of_mem_support_of_isPath_of_adj _ hww' hw' hp hw'2)
  have : (G \ p.toSubgraph.spanningCoe).Adj w' v := by
    simp only [sdiff_adj, Subgraph.spanningCoe_adj]
    refine ⟨hw'2.symm, fun h => ?_⟩
    exact hnpvw' h.symm
  use (((hcyc.reachable_sdiff_toSubgraph_spanningCoe_aux
    (p.cons hw'2.symm) hp'p).some).mapLe hle).append this.toWalk
termination_by Nat.card V + 1 - p.length
decreasing_by
  have := Fintype.ofFinite V
  simp_wf
  have := Walk.IsPath.length_lt hp
  lia

/--
lemma `IsCycles.reachable_sdiff_toSubgraph_spanningCoe` / 引理 `IsCycles.reachable_sdiff_toSubgraph_spanningCoe`

English:
lemma IsCycles.reachable_sdiff_toSubgraph_spanningCoe
  statement: [Finite V] {v w : V} (hcyc : G.IsCycles)
  proof: by
  have : Fintype V := Fintype.ofFinite V
  exact reachable_sdiff_toSubgraph_spanningCoe_aux hcyc p hp

中文:
引理 IsCycles.reachable_sdiff_toSubgraph_spanningCoe
  结论: [有限 V] {v w : V} (hcyc : G.IsCycles)
  证明: by
  have : Fintype V := Fintype.ofFinite V
  exact reachable_sdiff_toSubgraph_spanningCoe_aux hcyc p hp

Depends on / 依赖: Fintype, Fintype.ofFinite, ofFinite, reachable_sdiff_toSubgraph_spanningCoe_aux
-/
lemma IsCycles.reachable_sdiff_toSubgraph_spanningCoe [Finite V] {v w : V} (hcyc : G.IsCycles)
    (p : G.Walk v w) (hp : p.IsPath) : (G \ p.toSubgraph.spanningCoe).Reachable w v := by
  have : Fintype V := Fintype.ofFinite V
  exact reachable_sdiff_toSubgraph_spanningCoe_aux hcyc p hp

/--
lemma `IsCycles.reachable_deleteEdges` / 引理 `IsCycles.reachable_deleteEdges`

English:
lemma IsCycles.reachable_deleteEdges
  statement: [Finite V] (hadj : G.Adj v w)
  proof: by
  have : fromEdgeSet {s(v, w)} = hadj.toWalk.toSubgraph.spanningCoe := by
    simp only [Walk.toSubgraph, singletonSubgraph_le_iff, subgraphOfAdj_verts, Set.mem_insert_iff,
      Set.mem_singleton_iff, or_true, sup_of_le_left]
    exact (Subgraph.spanningCoe_subgraphOfAdj hadj).symm
  rw [show G.

中文:
引理 IsCycles.reachable_deleteEdges
  结论: [有限 V] (hadj : G.伴随 v w)
  证明: by
  have : fromEdgeSet {s(v, w)} = hadj.toWalk.toSubgraph.spanningCoe := by
    simp only [Walk.toSubgraph, singletonSubgraph_le_iff, subgraphOfAdj_verts, Set.mem_insert_iff,
      Set.mem_singleton_iff, or_true, sup_of_le_left]
    exact (Subgraph.spanningCoe_subgraphOfAdj hadj).symm
  rw [show G.

Depends on / 依赖: G.deleteEdges, IsPath, Set.mem_insert_iff, Set.mem_singleton_iff, Subgraph, Subgraph.spanningCoe_subgraphOfAdj, Walk.IsPath.of_adj, Walk.toSubgraph, deleteEdges, fromEdgeSet, hadj.toWalk, hadj.toWalk.toSubgraph.spanningCoe, hcyc.reachable_sdiff_toSubgraph_spanningCoe, mem_insert_iff, mem_singleton_iff, of_adj, or_true, reachable_sdiff_toSubgraph_spanningCoe, singletonSubgraph_le_iff, spanningCoe
-/
lemma IsCycles.reachable_deleteEdges [Finite V] (hadj : G.Adj v w)
    (hcyc : G.IsCycles) : (G.deleteEdges {s(v, w)}).Reachable v w := by
  have : fromEdgeSet {s(v, w)} = hadj.toWalk.toSubgraph.spanningCoe := by
    simp only [Walk.toSubgraph, singletonSubgraph_le_iff, subgraphOfAdj_verts, Set.mem_insert_iff,
      Set.mem_singleton_iff, or_true, sup_of_le_left]
    exact (Subgraph.spanningCoe_subgraphOfAdj hadj).symm
  rw [show G.deleteEdges {s(v]; rw [w)} = G \ fromEdgeSet {s(v]; rw [w)} by rfl]
  exact this ▸ (hcyc.reachable_sdiff_toSubgraph_spanningCoe hadj.toWalk
    (Walk.IsPath.of_adj hadj)).symm

/--
lemma `IsCycles.exists_cycle_toSubgraph_verts_eq_connectedComponentSupp` / 引理 `IsCycles.exists_cycle_toSubgraph_verts_eq_connectedComponentSupp`

English:
lemma IsCycles.exists_cycle_toSubgraph_verts_eq_connectedComponentSupp
  statement: [Finite V]
  proof: by
  classical
  obtain ⟨w, hw⟩ := hn
  obtain ⟨u, p, hp⟩ := SimpleGraph.adj_and_reachable_delete_edges_iff_exists_cycle.mp
    ⟨hw, h.reachable_deleteEdges hw⟩
  have hvp : v in p.support := SimpleGraph.Walk.fst_mem_support_of_mem_edges _ hp.2
  have : p.toSubgraph.verts = c.supp := by
    obtain ⟨

中文:
引理 IsCycles.存在_cycle_toSubgraph_verts_eq_connectedComponentSupp
  结论: [有限 V]
  证明: by
  classical
  obtain ⟨w, hw⟩ := hn
  obtain ⟨u, p, hp⟩ := SimpleGraph.adj_and_reachable_delete_edges_iff_exists_cycle.mp
    ⟨hw, h.reachable_deleteEdges hw⟩
  have hvp : v in p.support := SimpleGraph.Walk.fst_mem_support_of_mem_edges _ hp.2
  have : p.toSubgraph.verts = c.supp := by
    obtain ⟨

Depends on / 依赖: G.neighborSet, Nonempty, Set.toFinite, SimpleGraph, SimpleGraph.Walk.fst_mem_support_of_mem_edges, SimpleGraph.adj_and_reachable_delete_edges_iff_exists_cycle.mp, Subgraph, Subgraph.adj_iff_of_neighborSet_equiv, adj_and_reachable_delete_edges_iff_exists_cycle, adj_iff_of_neighborSet_equiv, c.supp, classical, exists_verts_eq_connectedComponentSupp, fst_mem_support_of_mem_edges, h.reachable_deleteEdges, neighborSet, p.support, p.toSubgraph.verts, p.toSubgraph_connected.exists_verts_eq_connectedComponentSupp, reachable_deleteEdges
-/
lemma IsCycles.exists_cycle_toSubgraph_verts_eq_connectedComponentSupp [Finite V]
    {c : G.ConnectedComponent} (h : G.IsCycles) (hv : v in c.supp)
    (hn : (G.neighborSet v).Nonempty) :
    exists (p : G.Walk v v), p.IsCycle ∧ p.toSubgraph.verts = c.supp := by
  classical
  obtain ⟨w, hw⟩ := hn
  obtain ⟨u, p, hp⟩ := SimpleGraph.adj_and_reachable_delete_edges_iff_exists_cycle.mp
    ⟨hw, h.reachable_deleteEdges hw⟩
  have hvp : v in p.support := SimpleGraph.Walk.fst_mem_support_of_mem_edges _ hp.2
  have : p.toSubgraph.verts = c.supp := by
    obtain ⟨c', hc'⟩ := p.toSubgraph_connected.exists_verts_eq_connectedComponentSupp (by
      intro v hv w hadj
      refine (Subgraph.adj_iff_of_neighborSet_equiv ?_ (Set.toFinite _)).mpr hadj
      have : (G.neighborSet v).Nonempty := by
        rw [Walk.mem_verts_toSubgraph] at hv
        refine (Set.nonempty_of_ncard_ne_zero ?_).mono (p.toSubgraph.neighborSet_subset v)
        rw [hp.1.ncard_neighborSet_toSubgraph_eq_two hv]
        lia
      refine @Classical.ofNonempty _ ?_
      rw [← Cardinal.eq]; rw [← Set.cast_ncard (Set.toFinite _)]; rw [← Set.cast_ncard (Set.toFinite _)]; rw [h this]; rw [hp.1.ncard_neighborSet_toSubgraph_eq_two (p.mem_verts_toSubgraph.mp hv)])
    rw [hc']
    have : v in c'.supp := by
      rw [← hc']; rw [Walk.mem_verts_toSubgraph]
      exact hvp
    simp_all
  use p.rotate v hvp
  rw [← this]
  exact ⟨hp.1.rotate _, by simp⟩

/--
Definition of `IsAlternating` / `IsAlternating` 的定义

English:
definition IsAlternating
  signature: (G G' : SimpleGraph V)
  body: forall ⦃v w w' : V⦄, w != w' -> G.Adj v w -> G.Adj v w' -> (G'.Adj v w ↔ ¬ G'.Adj v w')

中文:
定义 IsAlternating
  签名: (G G' : 简单图 V)
  定义体: forall ⦃v w w' : V⦄, w != w' -> G.Adj v w -> G.Adj v w' -> (G'.Adj v w ↔ ¬ G'.Adj v w')

Depends on / 依赖: G.Adj
-/
def IsAlternating (G G' : SimpleGraph V) :=
  forall ⦃v w w' : V⦄, w != w' -> G.Adj v w -> G.Adj v w' -> (G'.Adj v w ↔ ¬ G'.Adj v w')

/--
lemma `IsAlternating.mono` / 引理 `IsAlternating.mono`

English:
lemma IsAlternating.mono
  given: {G'' : SimpleGraph V} (halt : G.IsAlternating G') (h : G'' <= G)
  proof: fun _ _ _ hww' hvw hvw' => halt hww' (h hvw) (h hvw')

中文:
引理 IsAlternating.mono
  条件: {G'' : 简单图 V} (halt : G.IsAlternating G') (h : G'' <= G)
  证明: fun _ _ _ hww' hvw hvw' => halt hww' (h hvw) (h hvw')
-/
lemma IsAlternating.mono {G'' : SimpleGraph V} (halt : G.IsAlternating G') (h : G'' <= G) :
    G''.IsAlternating G' := fun _ _ _ hww' hvw hvw' => halt hww' (h hvw) (h hvw')

/--
lemma `IsAlternating.spanningCoe` / 引理 `IsAlternating.spanningCoe`

English:
lemma IsAlternating.spanningCoe
  given: (halt : G.IsAlternating G') (H : Subgraph G)
  proof: by
  intro v w w' hww' hvw hvv'
  simp only [Subgraph.spanningCoe_adj] at hvw hvv'
  exact halt hww' hvw.adj_sub hvv'.adj_sub

中文:
引理 IsAlternating.spanningCoe
  条件: (halt : G.IsAlternating G') (H : 子图 G)
  证明: by
  intro v w w' hww' hvw hvv'
  simp only [Subgraph.spanningCoe_adj] at hvw hvv'
  exact halt hww' hvw.adj_sub hvv'.adj_sub

Depends on / 依赖: Subgraph, Subgraph.spanningCoe_adj, adj_sub, hvw.adj_sub, spanningCoe_adj
-/
lemma IsAlternating.spanningCoe (halt : G.IsAlternating G') (H : Subgraph G) :
    H.spanningCoe.IsAlternating G' := by
  intro v w w' hww' hvw hvv'
  simp only [Subgraph.spanningCoe_adj] at hvw hvv'
  exact halt hww' hvw.adj_sub hvv'.adj_sub

/--
lemma `IsAlternating.sup_edge` / 引理 `IsAlternating.sup_edge`

English:
lemma IsAlternating.sup_edge
  statement: {u x : V} (halt : G.IsAlternating G') (hnadj : ¬G'.Adj u x)
  proof: by
  by_cases hadj : G.Adj u x
  · rwa [sup_edge_of_adj G hadj]
  intro v w w' hww' hvw hvv'
  simp only [sup_adj, edge_adj] at hvw hvv'
  obtain hl | hr := hvw <;> obtain h1 | h2 := hvv'
  · exact halt hww' hl h1
  · rw [G'.adj_congr_of_sym2 (by grind : s(v, w') = s(u, x))]
    simp only [hnadj, no

中文:
引理 IsAlternating.sup_edge
  结论: {u x : V} (halt : G.IsAlternating G') (hnadj : ¬G'.伴随 u x)
  证明: by
  by_cases hadj : G.Adj u x
  · rwa [sup_edge_of_adj G hadj]
  intro v w w' hww' hvw hvv'
  simp only [sup_adj, edge_adj] at hvw hvv'
  obtain hl | hr := hvw <;> obtain h1 | h2 := hvv'
  · exact halt hww' hl h1
  · rw [G'.adj_congr_of_sym2 (by grind : s(v, w') = s(u, x))]
    simp only [hnadj, no

Depends on / 依赖: G.Adj, adj_congr_of_sym2, edge_adj, false_iff, hl.symm, iff_true, not_false_eq_true, not_not, sup_adj, sup_edge_of_adj
-/
lemma IsAlternating.sup_edge {u x : V} (halt : G.IsAlternating G') (hnadj : ¬G'.Adj u x)
    (hu' : forall u', u' != u -> G.Adj x u' -> G'.Adj x u')
    (hx' : forall x', x' != x -> G.Adj x' u -> G'.Adj x' u) : (G ⊔ edge u x).IsAlternating G' := by
  by_cases hadj : G.Adj u x
  · rwa [sup_edge_of_adj G hadj]
  intro v w w' hww' hvw hvv'
  simp only [sup_adj, edge_adj] at hvw hvv'
  obtain hl | hr := hvw <;> obtain h1 | h2 := hvv'
  · exact halt hww' hl h1
  · rw [G'.adj_congr_of_sym2 (by grind : s(v, w') = s(u, x))]
    simp only [hnadj, not_false_eq_true, iff_true]
    rcases h2.1 with ⟨rfl, rfl⟩ | ⟨h2r1, h2r2⟩
    · exact (hx' _ hww' hl.symm).symm
    · simp_all
  · rw [G'.adj_congr_of_sym2 (by grind : s(v, w) = s(u, x))]
    simp only [hnadj, false_iff, not_not]
    rcases hr.1 with ⟨rfl, rfl⟩ | ⟨hrr1, hrr2⟩
    · exact (hx' _ hww'.symm h1.symm).symm
    · grind
  · grind

set_option backward.isDefEq.respectTransparency false in
/--
lemma `Subgraph.IsPerfectMatching.symmDiff_of_isAlternating` / 引理 `Subgraph.IsPerfectMatching.symmDiff_of_isAlternating`

English:
lemma Subgraph.IsPerfectMatching.symmDiff_of_isAlternating
  statement: (hM : M.IsPerfectMatching)
  proof: by
  rw [Subgraph.isPerfectMatching_iff]
  intro v
  simp only [symmDiff_def]
  obtain ⟨w, hw⟩ := hM.1 (hM.2 v)
  by_cases h : G'.Adj v w
  · obtain ⟨w', hw'⟩ := hG'cyc.other_adj_of_adj h
    have hmadj : M.Adj v w ↔ ¬M.Adj v w' := by simpa using hG' hw'.1 h hw'.2
    use w'
    simp only [Subgraph.

中文:
引理 子图.IsPerfectMatching.symmDiff_of_isAlternating
  结论: (hM : M.IsPerfectMatching)
  证明: by
  rw [Subgraph.isPerfectMatching_iff]
  intro v
  simp only [symmDiff_def]
  obtain ⟨w, hw⟩ := hM.1 (hM.2 v)
  by_cases h : G'.Adj v w
  · obtain ⟨w', hw'⟩ := hG'cyc.other_adj_of_adj h
    have hmadj : M.Adj v w ↔ ¬M.Adj v w' := by simpa using hG' hw'.1 h hw'.2
    use w'
    simp only [Subgraph.

Depends on / 依赖: M.Adj, SimpleGraph, SimpleGraph.sup_adj, Subgraph, Subgraph.isPerfectMatching_iff, Subgraph.spanningCoe_adj, Subgraph.top_adj, and_self, cyc.other_adj_, cyc.other_adj_of_adj, hmadj.mp, isPerfectMatching_iff, not_false_eq_true, not_true_eq_false, or_true, other_adj_, other_adj_of_adj, sdiff_adj, spanningCoe_adj, sup_adj
-/
lemma Subgraph.IsPerfectMatching.symmDiff_of_isAlternating (hM : M.IsPerfectMatching)
    (hG' : G'.IsAlternating M.spanningCoe) (hG'cyc : G'.IsCycles) :
    (⊤ : Subgraph (M.spanningCoe ∆ G')).IsPerfectMatching := by
  rw [Subgraph.isPerfectMatching_iff]
  intro v
  simp only [symmDiff_def]
  obtain ⟨w, hw⟩ := hM.1 (hM.2 v)
  by_cases h : G'.Adj v w
  · obtain ⟨w', hw'⟩ := hG'cyc.other_adj_of_adj h
    have hmadj : M.Adj v w ↔ ¬M.Adj v w' := by simpa using hG' hw'.1 h hw'.2
    use w'
    simp only [Subgraph.top_adj, SimpleGraph.sup_adj, sdiff_adj, Subgraph.spanningCoe_adj,
      hmadj.mp hw.1, hw'.2, not_true_eq_false, and_self, not_false_eq_true, or_true, true_and]
    rintro y (hl | hr)
    · grind
    · obtain ⟨w'', hw''⟩ := hG'cyc.other_adj_of_adj hr.1
      by_contra! hc
      simp_all [show M.Adj v y ↔ ¬M.Adj v w' by simpa using hG' hc hr.1 hw'.2]
  · use w
    simp only [Subgraph.top_adj, SimpleGraph.sup_adj, sdiff_adj, Subgraph.spanningCoe_adj, hw.1, h,
      not_false_eq_true, and_self, not_true_eq_false, or_false, true_and]
    rintro y (hl | hr)
    · exact hw.2 _ hl.1
    · have ⟨w', hw'⟩ := hG'cyc.other_adj_of_adj hr.1
      simp_all [show M.Adj v y ↔ ¬M.Adj v w' by simpa using hG' hw'.1 hr.1 hw'.2]

/--
lemma `Subgraph.IsPerfectMatching.isAlternating_symmDiff_left` / 引理 `Subgraph.IsPerfectMatching.isAlternating_symmDiff_left`

English:
lemma Subgraph.IsPerfectMatching.isAlternating_symmDiff_left
  statement: {M' : Subgraph G'}
  proof: by
  intro v w w' hww' hvw hvw'
  obtain ⟨v1, hm1, hv1⟩ := hM.1 (hM.2 v)
  obtain ⟨v2, hm2, hv2⟩ := hM'.1 (hM'.2 v)
  simp only [symmDiff_def] at *
  aesop

中文:
引理 子图.IsPerfectMatching.isAlternating_symmDiff_left
  结论: {M' : 子图 G'}
  证明: by
  intro v w w' hww' hvw hvw'
  obtain ⟨v1, hm1, hv1⟩ := hM.1 (hM.2 v)
  obtain ⟨v2, hm2, hv2⟩ := hM'.1 (hM'.2 v)
  simp only [symmDiff_def] at *
  aesop

Depends on / 依赖: symmDiff_def
-/
lemma Subgraph.IsPerfectMatching.isAlternating_symmDiff_left {M' : Subgraph G'}
    (hM : M.IsPerfectMatching) (hM' : M'.IsPerfectMatching) :
    (M.spanningCoe ∆ M'.spanningCoe).IsAlternating M.spanningCoe := by
  intro v w w' hww' hvw hvw'
  obtain ⟨v1, hm1, hv1⟩ := hM.1 (hM.2 v)
  obtain ⟨v2, hm2, hv2⟩ := hM'.1 (hM'.2 v)
  simp only [symmDiff_def] at *
  aesop

/--
lemma `Subgraph.IsPerfectMatching.isAlternating_symmDiff_right` / 引理 `Subgraph.IsPerfectMatching.isAlternating_symmDiff_right`

English:
lemma Subgraph.IsPerfectMatching.isAlternating_symmDiff_right
  proof: by
  simpa [symmDiff_comm] using isAlternating_symmDiff_left hM' hM

中文:
引理 子图.IsPerfectMatching.isAlternating_symmDiff_right
  证明: by
  simpa [symmDiff_comm] using isAlternating_symmDiff_left hM' hM

Depends on / 依赖: isAlternating_symmDiff_left, symmDiff_comm
-/
lemma Subgraph.IsPerfectMatching.isAlternating_symmDiff_right
    {M' : Subgraph G'} (hM : M.IsPerfectMatching) (hM' : M'.IsPerfectMatching) :
    (M.spanningCoe ∆ M'.spanningCoe).IsAlternating M'.spanningCoe := by
  simpa [symmDiff_comm] using isAlternating_symmDiff_left hM' hM

end SimpleGraph
