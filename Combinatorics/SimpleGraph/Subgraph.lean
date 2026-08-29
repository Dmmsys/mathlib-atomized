/-
Copyright (c) 2021 Hunter Monroe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hunter Monroe, Kyle Miller, Alena Gusakov
-/
module

public import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
public import Mathlib.Data.Fintype.Powerset

/-!
# Subgraphs of a simple graph

A subgraph of a simple graph consists of subsets of the graph's vertices and edges such that the
endpoints of each edge are present in the vertex subset. The edge subset is formalized as a
sub-relation of the adjacency relation of the simple graph.

## Main definitions

* `Subgraph G` is the type of subgraphs of a `G : SimpleGraph V`.

* `Subgraph.neighborSet`, `Subgraph.incidenceSet`, and `Subgraph.degree` are like their
  `SimpleGraph` counterparts, but they refer to vertices from `G` to avoid subtype coercions.

* `Subgraph.coe` is the coercion from a `G' : Subgraph G` to a `SimpleGraph G'.verts`.
  (In Lean 3 this could not be a `Coe` instance since the destination type depends on `G'`.)

* `Subgraph.IsSpanning` for whether a subgraph is a spanning subgraph and
  `Subgraph.IsInduced` for whether a subgraph is an induced subgraph.

* Instances for `DistribLattice G.Subgraph` and `BoundedOrder (Subgraph G)`.

* `SimpleGraph.toSubgraph`: If a `SimpleGraph` is a subgraph of another, then you can turn it
  into a member of the larger graph's `SimpleGraph.Subgraph` type.

* Graph homomorphisms from a subgraph to a graph (`Subgraph.map_top`) and between subgraphs
  (`Subgraph.map`).

## Implementation notes

* Recall that subgraphs are not determined by their vertex sets, so `SetLike` does not apply to
  this kind of subobject.

## TODO

* Images of graph homomorphisms as subgraphs.

-/

@[expose] public section


universe u v

namespace SimpleGraph

/-- A subgraph of a `SimpleGraph` is a subset of vertices along with a restriction of the adjacency
relation that is symmetric and is supported by the vertex subset. They also form a bounded lattice.

Thinking of `V → V → Prop` as `Set (V × V)`, a set of darts (i.e., half-edges), then
`Subgraph.adj_sub` is that the darts of a subgraph are a subset of the darts of `G`. -/
@[ext]
/--
Definition of `Subgraph` / `Subgraph` 的定义

English:
structure Subgraph
  parameters: {V : Type u} (G : SimpleGraph V)
  axioms and operations (5):
    - verts : Set V
    - Adj : V -> V -> Prop
    - adj_sub : forall {v w : V}, Adj v w -> G.Adj v w
    - edge_vert : forall {v w : V}, Adj v w -> v in verts
    - symm : Std.Symm Adj  [default: by aesop_graph]

中文:
结构 Subgraph
  参数: {V : 类型u} (G : SimpleGraph V)
  公理与运算 (5 个):
    - verts : Set V
    - Adj : V -> V -> 命题
    - adj_sub : 对任意 {v w : V}, Adj v w -> G.Adj v w
    - edge_vert : 对任意 {v w : V}, Adj v w -> v in verts
    - symm : Std.Symm Adj  [默认: by aesop_graph]

Depends on / 依赖: aesop_graph
-/
structure Subgraph {V : Type u} (G : SimpleGraph V) where
  /-- Vertices of the subgraph -/
  verts : Set V
  /-- Edges of the subgraph -/
  Adj : V -> V -> Prop
  adj_sub : forall {v w : V}, Adj v w -> G.Adj v w
  edge_vert : forall {v w : V}, Adj v w -> v in verts
  symm : Std.Symm Adj := by aesop_graph

initialize_simps_projections SimpleGraph.Subgraph (Adj -> adj)

variable {ι : Sort*} {V : Type u} {W : Type v}

/-- The one-vertex subgraph. -/
@[simps]
/--
Definition of `singletonSubgraph` / `singletonSubgraph` 的定义

English:
definition singletonSubgraph
  signature: (G : SimpleGraph V) (v : V)
  body: {v}
  Adj := ⊥
  adj_sub := False.elim
  edge_vert := False.elim

中文:
定义 singletonSubgraph
  签名: (G : SimpleGraph V) (v : V)
  定义体: {v}
  Adj := ⊥
  adj_sub := False.elim
  edge_vert := False.elim
-/
protected def singletonSubgraph (G : SimpleGraph V) (v : V) : G.Subgraph where
  verts := {v}
  Adj := ⊥
  adj_sub := False.elim
  edge_vert := False.elim

/-- The one-edge subgraph. -/
@[simps]
/--
Definition of `subgraphOfAdj` / `subgraphOfAdj` 的定义

English:
definition subgraphOfAdj
  signature: (G : SimpleGraph V) {v w : V} (hvw : G.Adj v w)
  body: {v, w}
  Adj a b := s(v, w) = s(a, b)
  adj_sub h := by
    rw [← G.mem_edgeSet]; rw [← h]
    exact hvw
  edge_vert {a b} h := by
    apply_fun fun e => a in e at h
    simp only [Sym2.mem_iff, true_or, eq_iff_iff, iff_true] at h
    exact h

中文:
定义 subgraphOfAdj
  签名: (G : SimpleGraph V) {v w : V} (hvw : G.Adj v w)
  定义体: {v, w}
  Adj a b := s(v, w) = s(a, b)
  adj_sub h := by
    rw [← G.mem_edgeSet]; rw [← h]
    exact hvw
  edge_vert {a b} h := by
    apply_fun fun e => a in e at h
    simp only [Sym2.mem_iff, true_or, eq_iff_iff, iff_true] at h
    exact h
-/
def subgraphOfAdj (G : SimpleGraph V) {v w : V} (hvw : G.Adj v w) : G.Subgraph where
  verts := {v, w}
  Adj a b := s(v, w) = s(a, b)
  adj_sub h := by
    rw [← G.mem_edgeSet]; rw [← h]
    exact hvw
  edge_vert {a b} h := by
    apply_fun fun e => a in e at h
    simp only [Sym2.mem_iff, true_or, eq_iff_iff, iff_true] at h
    exact h

namespace Subgraph

variable {G : SimpleGraph V} {G₁ G₂ : G.Subgraph} {a b : V}

/--
theorem `loopless` / 定理 `loopless`

English:
theorem loopless
  given: (G' : Subgraph G)
  statement: Std.Irrefl G'.Adj where
  proof: G.irrefl G'.adj_sub hadj

中文:
定理 loopless
  条件: (G' : Subgraph G)
  结论: Std.Irrefl G'.Adj where
  证明: G.irrefl G'.adj_sub hadj
-/
protected theorem loopless (G' : Subgraph G) : Std.Irrefl G'.Adj where
irrefl _ hadj := G.irrefl G'.adj_sub hadj

/--
theorem `adj_comm` / 定理 `adj_comm`

English:
theorem adj_comm
  given: (G' : Subgraph G) (v w : V)
  statement: G'.Adj v w ↔ G'.Adj w v
  proof: G'.symm.iff v w

@[symm]

中文:
定理 adj_comm
  条件: (G' : Subgraph G) (v w : V)
  结论: G'.Adj v w ↔ G'.Adj w v
  证明: G'.symm.iff v w

@[symm]

Depends on / 依赖: symm.iff
-/
theorem adj_comm (G' : Subgraph G) (v w : V) : G'.Adj v w ↔ G'.Adj w v :=
  G'.symm.iff v w

@[symm]
/--
theorem `adj_symm` / 定理 `adj_symm`

English:
theorem adj_symm
  given: (G' : Subgraph G) {u v : V} (h : G'.Adj u v)
  statement: G'.Adj v u
  proof: G'.symm.symm u v h

中文:
定理 adj_symm
  条件: (G' : Subgraph G) {u v : V} (h : G'.Adj u v)
  结论: G'.Adj v u
  证明: G'.symm.symm u v h

Depends on / 依赖: symm.symm
-/
theorem adj_symm (G' : Subgraph G) {u v : V} (h : G'.Adj u v) : G'.Adj v u :=
  G'.symm.symm u v h

/--
theorem `Adj.symm` / 定理 `Adj.symm`

English:
theorem Adj.symm
  given: {G' : Subgraph G} {u v : V} (h : G'.Adj u v)
  statement: G'.Adj v u
  proof: G'.adj_symm h

@[grind ->]

中文:
定理 Adj.symm
  条件: {G' : Subgraph G} {u v : V} (h : G'.Adj u v)
  结论: G'.Adj v u
  证明: G'.adj_symm h

@[grind ->]
-/
protected theorem Adj.symm {G' : Subgraph G} {u v : V} (h : G'.Adj u v) : G'.Adj v u :=
  G'.adj_symm h

@[grind ->]
/--
theorem `Adj.adj_sub` / 定理 `Adj.adj_sub`

English:
theorem Adj.adj_sub
  given: {H : G.Subgraph} {u v : V} (h : H.Adj u v)
  statement: G.Adj u v
  proof: H.adj_sub h

中文:
定理 Adj.adj_sub
  条件: {H : G.Subgraph} {u v : V} (h : H.Adj u v)
  结论: G.Adj u v
  证明: H.adj_sub h
-/
protected theorem Adj.adj_sub {H : G.Subgraph} {u v : V} (h : H.Adj u v) : G.Adj u v :=
  H.adj_sub h

/--
theorem `Adj.fst_mem` / 定理 `Adj.fst_mem`

English:
theorem Adj.fst_mem
  given: {H : G.Subgraph} {u v : V} (h : H.Adj u v)
  statement: u in H.verts
  proof: H.edge_vert h

中文:
定理 Adj.fst_mem
  条件: {H : G.Subgraph} {u v : V} (h : H.Adj u v)
  结论: u in H.verts
  证明: H.edge_vert h
-/
protected theorem Adj.fst_mem {H : G.Subgraph} {u v : V} (h : H.Adj u v) : u in H.verts :=
  H.edge_vert h

/--
theorem `Adj.snd_mem` / 定理 `Adj.snd_mem`

English:
theorem Adj.snd_mem
  given: {H : G.Subgraph} {u v : V} (h : H.Adj u v)
  statement: v in H.verts
  proof: h.symm.fst_mem

中文:
定理 Adj.snd_mem
  条件: {H : G.Subgraph} {u v : V} (h : H.Adj u v)
  结论: v in H.verts
  证明: h.symm.fst_mem
-/
protected theorem Adj.snd_mem {H : G.Subgraph} {u v : V} (h : H.Adj u v) : v in H.verts :=
  h.symm.fst_mem

/--
theorem `Adj.ne` / 定理 `Adj.ne`

English:
theorem Adj.ne
  given: {H : G.Subgraph} {u v : V} (h : H.Adj u v)
  statement: u != v
  proof: h.adj_sub.ne

中文:
定理 Adj.ne
  条件: {H : G.Subgraph} {u v : V} (h : H.Adj u v)
  结论: u != v
  证明: h.adj_sub.ne
-/
protected theorem Adj.ne {H : G.Subgraph} {u v : V} (h : H.Adj u v) : u != v :=
  h.adj_sub.ne

/--
theorem `adj_congr_of_sym2` / 定理 `adj_congr_of_sym2`

English:
theorem adj_congr_of_sym2
  given: {H : G.Subgraph} {u v w x : V} (h2 : s(u, v) = s(w, x))
  proof: by
  simp only [Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk] at h2
  rcases h2 with hl | hr
  · rw [hl.1, hl.2]
  · rw [hr.1, hr.2, Subgraph.adj_comm]

中文:
定理 adj_congr_of_sym2
  条件: {H : G.Subgraph} {u v w x : V} (h2 : s(u, v) = s(w, x))
  证明: by
  simp only [Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk] at h2
  rcases h2 with hl | hr
  · rw [hl.1, hl.2]
  · rw [hr.1, hr.2, Subgraph.adj_comm]

Depends on / 依赖: Prod.mk.injEq, Prod.swap_prod_mk, Subgraph, Subgraph.adj_comm, Sym2.eq, Sym2.rel_iff, adj_comm, rel_iff, swap_prod_mk
-/
theorem adj_congr_of_sym2 {H : G.Subgraph} {u v w x : V} (h2 : s(u, v) = s(w, x)) :
    H.Adj u v ↔ H.Adj w x := by
  simp only [Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk] at h2
  rcases h2 with hl | hr
  · rw [hl.1, hl.2]
  · rw [hr.1, hr.2, Subgraph.adj_comm]

/-- Coercion from `G' : Subgraph G` to a `SimpleGraph G'.verts`. -/
@[simps]
/--
Definition of `coe` / `coe` 的定义

English:
definition coe
  signature: (G' : Subgraph G)
  body: G'.Adj v w
  symm := G'.symm.comap Subtype.val
  loopless.irrefl _ hadj := G.irrefl hadj.adj_sub

@[simp]

中文:
定义 coe
  签名: (G' : Subgraph G)
  定义体: G'.Adj v w
  symm := G'.symm.comap Subtype.val
  loopless.irrefl _ hadj := G.irrefl hadj.adj_sub

@[simp]
-/
protected def coe (G' : Subgraph G) : SimpleGraph G'.verts where
  Adj v w := G'.Adj v w
  symm := G'.symm.comap Subtype.val
  loopless.irrefl _ hadj := G.irrefl hadj.adj_sub

@[simp]
/--
theorem `Adj.adj_sub'` / 定理 `Adj.adj_sub'`

English:
theorem Adj.adj_sub'
  given: (G' : Subgraph G) (u v : G'.verts) (h : G'.Adj u v)
  statement: G.Adj u v
  proof: G'.adj_sub h

中文:
定理 Adj.adj_sub'
  条件: (G' : Subgraph G) (u v : G'.verts) (h : G'.Adj u v)
  结论: G.Adj u v
  证明: G'.adj_sub h

Depends on / 依赖: adj_sub
-/
theorem Adj.adj_sub' (G' : Subgraph G) (u v : G'.verts) (h : G'.Adj u v) : G.Adj u v :=
  G'.adj_sub h

/--
theorem `coe_adj_sub` / 定理 `coe_adj_sub`

English:
theorem coe_adj_sub
  given: (G' : Subgraph G) (u v : G'.verts) (h : G'.coe.Adj u v)
  statement: G.Adj u v
  proof: G'.adj_sub h

中文:
定理 coe_adj_sub
  条件: (G' : Subgraph G) (u v : G'.verts) (h : G'.coe.Adj u v)
  结论: G.Adj u v
  证明: G'.adj_sub h

Depends on / 依赖: adj_sub
-/
theorem coe_adj_sub (G' : Subgraph G) (u v : G'.verts) (h : G'.coe.Adj u v) : G.Adj u v :=
  G'.adj_sub h

-- Given `h : H.Adj u v`, then `h.coe : H.coe.Adj ⟨u, _⟩ ⟨v, _⟩`.
/--
theorem `Adj.coe` / 定理 `Adj.coe`

English:
theorem Adj.coe
  given: {H : G.Subgraph} {u v : V} (h : H.Adj u v)
  proof: h

中文:
定理 Adj.coe
  条件: {H : G.Subgraph} {u v : V} (h : H.Adj u v)
  证明: h
-/
protected theorem Adj.coe {H : G.Subgraph} {u v : V} (h : H.Adj u v) :
    H.coe.Adj ⟨u, H.edge_vert h⟩ ⟨v, H.edge_vert h.symm⟩ := h

instance (G : SimpleGraph V) (H : Subgraph G) [DecidableRel H.Adj] : DecidableRel H.coe.Adj :=
  fun a b => ‹DecidableRel H.Adj› _ _

/--
Definition of `IsSpanning` / `IsSpanning` 的定义

English:
definition IsSpanning
  signature: (G' : Subgraph G)
  body: forall v : V, v in G'.verts

中文:
定义 IsSpanning
  签名: (G' : Subgraph G)
  定义体: forall v : V, v in G'.verts
-/
def IsSpanning (G' : Subgraph G) : Prop :=
  forall v : V, v in G'.verts

/--
theorem `isSpanning_iff` / 定理 `isSpanning_iff`

English:
theorem isSpanning_iff
  given: {G' : Subgraph G}
  statement: G'.IsSpanning ↔ G'.verts = Set.univ
  proof: Set.eq_univ_iff_forall.symm

protected alias ⟨IsSpanning.verts_eq_univ, _⟩ := isSpanning_iff

中文:
定理 isSpanning_iff
  条件: {G' : Subgraph G}
  结论: G'.IsSpanning ↔ G'.verts = Set.univ
  证明: Set.eq_univ_iff_forall.symm

protected alias ⟨IsSpanning.verts_eq_univ, _⟩ := isSpanning_iff

Depends on / 依赖: Set.eq_univ_iff_forall.symm, eq_univ_iff_forall
-/
theorem isSpanning_iff {G' : Subgraph G} : G'.IsSpanning ↔ G'.verts = Set.univ :=
  Set.eq_univ_iff_forall.symm

protected alias ⟨IsSpanning.verts_eq_univ, _⟩ := isSpanning_iff

/-- Coercion from `Subgraph G` to `SimpleGraph V`. If `G'` is a spanning
subgraph, then `G'.spanningCoe` yields an isomorphic graph.
In general, this adds in all vertices from `V` as isolated vertices. -/
@[simps]
/--
Definition of `spanningCoe` / `spanningCoe` 的定义

English:
definition spanningCoe
  signature: (G' : Subgraph G)
  body: G'.Adj
  symm := G'.symm
  loopless.irrefl _ hadj := G.irrefl hadj.adj_sub

中文:
定义 spanningCoe
  签名: (G' : Subgraph G)
  定义体: G'.Adj
  symm := G'.symm
  loopless.irrefl _ hadj := G.irrefl hadj.adj_sub
-/
protected def spanningCoe (G' : Subgraph G) : SimpleGraph V where
  Adj := G'.Adj
  symm := G'.symm
  loopless.irrefl _ hadj := G.irrefl hadj.adj_sub

attribute [grind =] Subgraph.spanningCoe_adj

@[simp]
/--
lemma `spanningCoe_coe` / 引理 `spanningCoe_coe`

English:
lemma spanningCoe_coe
  given: (G' : G.Subgraph)
  statement: G'.coe.spanningCoe = G'.spanningCoe
  proof: by
  ext
  simp only [map_adj, Function.Embedding.subtype_apply, Subtype.exists]
  grind [coe_adj, edge_vert, adj_symm]

中文:
引理 spanningCoe_coe
  条件: (G' : G.Subgraph)
  结论: G'.coe.spanningCoe = G'.spanningCoe
  证明: by
  ext
  simp only [map_adj, Function.Embedding.subtype_apply, Subtype.exists]
  grind [coe_adj, edge_vert, adj_symm]

Depends on / 依赖: Embedding, Function, Function.Embedding.subtype_apply, Subtype, Subtype.exists, adj_symm, coe_adj, edge_vert, map_adj, subtype_apply
-/
lemma spanningCoe_coe (G' : G.Subgraph) : G'.coe.spanningCoe = G'.spanningCoe := by
  ext
  simp only [map_adj, Function.Embedding.subtype_apply, Subtype.exists]
  grind [coe_adj, edge_vert, adj_symm]

/--
theorem `Adj.of_spanningCoe` / 定理 `Adj.of_spanningCoe`

English:
theorem Adj.of_spanningCoe
  given: {G' : Subgraph G} {u v : G'.verts} (h : G'.spanningCoe.Adj u v)
  proof: G'.adj_sub h

中文:
定理 Adj.of_spanningCoe
  条件: {G' : Subgraph G} {u v : G'.verts} (h : G'.spanningCoe.Adj u v)
  证明: G'.adj_sub h

Depends on / 依赖: adj_sub
-/
theorem Adj.of_spanningCoe {G' : Subgraph G} {u v : G'.verts} (h : G'.spanningCoe.Adj u v) :
    G.Adj u v :=
  G'.adj_sub h

/--
lemma `spanningCoe_le` / 引理 `spanningCoe_le`

English:
lemma spanningCoe_le
  given: (G' : G.Subgraph)
  statement: G'.spanningCoe <= G
  proof: fun _ _ => G'.3

中文:
引理 spanningCoe_le
  条件: (G' : G.Subgraph)
  结论: G'.spanningCoe <= G
  证明: fun _ _ => G'.3
-/
lemma spanningCoe_le (G' : G.Subgraph) : G'.spanningCoe <= G := fun _ _ => G'.3

/--
theorem `spanningCoe_inj` / 定理 `spanningCoe_inj`

English:
theorem spanningCoe_inj
  statement: G₁.spanningCoe = G₂.spanningCoe ↔ G₁.Adj = G₂.Adj
  proof: by
  simp [Subgraph.spanningCoe]

中文:
定理 spanningCoe_inj
  结论: G₁.spanningCoe = G₂.spanningCoe ↔ G₁.Adj = G₂.Adj
  证明: by
  simp [Subgraph.spanningCoe]

Depends on / 依赖: Subgraph, Subgraph.spanningCoe, spanningCoe
-/
theorem spanningCoe_inj : G₁.spanningCoe = G₂.spanningCoe ↔ G₁.Adj = G₂.Adj := by
  simp [Subgraph.spanningCoe]

/--
lemma `mem_of_adj_spanningCoe` / 引理 `mem_of_adj_spanningCoe`

English:
lemma mem_of_adj_spanningCoe
  statement: {v w : V} {s : Set V} (G : SimpleGraph s)
  proof: by aesop

@[simp]

中文:
引理 mem_of_adj_spanningCoe
  结论: {v w : V} {s : Set V} (G : SimpleGraph s)
  证明: by aesop

@[simp]
-/
lemma mem_of_adj_spanningCoe {v w : V} {s : Set V} (G : SimpleGraph s)
    (hadj : G.spanningCoe.Adj v w) : v in s := by aesop

@[simp]
/--
lemma `spanningCoe_subgraphOfAdj` / 引理 `spanningCoe_subgraphOfAdj`

English:
lemma spanningCoe_subgraphOfAdj
  given: {v w : V} (hadj : G.Adj v w)
  proof: by
  ext v w
  aesop

中文:
引理 spanningCoe_subgraphOfAdj
  条件: {v w : V} (hadj : G.Adj v w)
  证明: by
  ext v w
  aesop
-/
lemma spanningCoe_subgraphOfAdj {v w : V} (hadj : G.Adj v w) :
    (G.subgraphOfAdj hadj).spanningCoe = fromEdgeSet {s(v, w)} := by
  ext v w
  aesop

/-- `coe` can be embedded in `spanningCoe`. -/
@[simps]
/--
Definition of `coeEmbeddingSpanningCoe` / `coeEmbeddingSpanningCoe` 的定义

English:
definition coeEmbeddingSpanningCoe
  signature: (G' : Subgraph G)
  body: Subtype.val
  inj' := Subtype.val_injective
  map_rel_iff' := .rfl

中文:
定义 coeEmbeddingSpanningCoe
  签名: (G' : Subgraph G)
  定义体: Subtype.val
  inj' := Subtype.val_injective
  map_rel_iff' := .rfl

Depends on / 依赖: Subtype, Subtype.val
-/
def coeEmbeddingSpanningCoe (G' : Subgraph G) : G'.coe ↪g G'.spanningCoe where
  toFun := Subtype.val
  inj' := Subtype.val_injective
  map_rel_iff' := .rfl

/-- `spanningCoe` is equivalent to `coe` for a subgraph that `IsSpanning`. -/
@[simps]
/--
Definition of `spanningCoeEquivCoeOfSpanning` / `spanningCoeEquivCoeOfSpanning` 的定义

English:
definition spanningCoeEquivCoeOfSpanning
  signature: (G' : Subgraph G) (h : G'.IsSpanning)
  body: ⟨v, h v⟩
  invFun v := v
  map_rel_iff' := Iff.rfl

中文:
定义 spanningCoeEquivCoeOfSpanning
  签名: (G' : Subgraph G) (h : G'.IsSpanning)
  定义体: ⟨v, h v⟩
  invFun v := v
  map_rel_iff' := Iff.rfl
-/
def spanningCoeEquivCoeOfSpanning (G' : Subgraph G) (h : G'.IsSpanning) :
    G'.spanningCoe ≃g G'.coe where
  toFun v := ⟨v, h v⟩
  invFun v := v
  map_rel_iff' := Iff.rfl

/--
Definition of `IsInduced` / `IsInduced` 的定义

English:
definition IsInduced
  signature: (G' : Subgraph G)
  body: forall ⦃v⦄, v in G'.verts -> forall ⦃w⦄, w in G'.verts -> G.Adj v w -> G'.Adj v w

中文:
定义 IsInduced
  签名: (G' : Subgraph G)
  定义体: forall ⦃v⦄, v in G'.verts -> forall ⦃w⦄, w in G'.verts -> G.Adj v w -> G'.Adj v w

Depends on / 依赖: G.Adj
-/
def IsInduced (G' : Subgraph G) : Prop :=
  forall ⦃v⦄, v in G'.verts -> forall ⦃w⦄, w in G'.verts -> G.Adj v w -> G'.Adj v w

/--
lemma `IsInduced.adj` / 引理 `IsInduced.adj`

English:
lemma IsInduced.adj
  given: {G' : G.Subgraph} (hG' : G'.IsInduced) {a b : G'.verts}
  proof: ⟨coe_adj_sub _ _ _, hG' a.2 b.2⟩

中文:
引理 IsInduced.adj
  条件: {G' : G.Subgraph} (hG' : G'.IsInduced) {a b : G'.verts}
  证明: ⟨coe_adj_sub _ _ _, hG' a.2 b.2⟩
-/
@[simp] protected lemma IsInduced.adj {G' : G.Subgraph} (hG' : G'.IsInduced) {a b : G'.verts} :
    G'.Adj a b ↔ G.Adj a b :=
  ⟨coe_adj_sub _ _ _, hG' a.2 b.2⟩

/--
Definition of `support` / `support` 的定义

English:
definition support
  signature: (H : Subgraph G)
  body: SetRel.dom {(v, w) | H.Adj v w}

中文:
定义 support
  签名: (H : Subgraph G)
  定义体: SetRel.dom {(v, w) | H.Adj v w}

Depends on / 依赖: H.Adj, SetRel, SetRel.dom
-/
def support (H : Subgraph G) : Set V := SetRel.dom {(v, w) | H.Adj v w}

/--
theorem `mem_support` / 定理 `mem_support`

English:
theorem mem_support
  given: (H : Subgraph G) {v : V}
  statement: v in H.support ↔ exists w, H.Adj v w
  proof: Iff.rfl

中文:
定理 mem_support
  条件: (H : Subgraph G) {v : V}
  结论: v in H.support ↔ 存在 w, H.Adj v w
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_support (H : Subgraph G) {v : V} : v in H.support ↔ exists w, H.Adj v w := Iff.rfl

/--
theorem `support_subset_verts` / 定理 `support_subset_verts`

English:
theorem support_subset_verts
  given: (H : Subgraph G)
  statement: H.support subseteq H.verts
  proof: fun _ ⟨_, h⟩ => H.edge_vert h

中文:
定理 support_subset_verts
  条件: (H : Subgraph G)
  结论: H.support subseteq H.verts
  证明: fun _ ⟨_, h⟩ => H.edge_vert h

Depends on / 依赖: H.edge_vert, edge_vert
-/
theorem support_subset_verts (H : Subgraph G) : H.support subseteq H.verts :=
  fun _ ⟨_, h⟩ => H.edge_vert h

/--
Definition of `neighborSet` / `neighborSet` 的定义

English:
definition neighborSet
  signature: (G' : Subgraph G) (v : V)
  body: {w | G'.Adj v w}

中文:
定义 neighborSet
  签名: (G' : Subgraph G) (v : V)
  定义体: {w | G'.Adj v w}
-/
def neighborSet (G' : Subgraph G) (v : V) : Set V := {w | G'.Adj v w}

/--
theorem `neighborSet_subset` / 定理 `neighborSet_subset`

English:
theorem neighborSet_subset
  given: (G' : Subgraph G) (v : V)
  statement: G'.neighborSet v subseteq G.neighborSet v
  proof: fun _ => G'.adj_sub

中文:
定理 neighborSet_subset
  条件: (G' : Subgraph G) (v : V)
  结论: G'.neighborSet v subseteq G.neighborSet v
  证明: fun _ => G'.adj_sub

Depends on / 依赖: adj_sub
-/
theorem neighborSet_subset (G' : Subgraph G) (v : V) : G'.neighborSet v subseteq G.neighborSet v :=
  fun _ => G'.adj_sub

/--
theorem `neighborSet_subset_verts` / 定理 `neighborSet_subset_verts`

English:
theorem neighborSet_subset_verts
  given: (G' : Subgraph G) (v : V)
  statement: G'.neighborSet v subseteq G'.verts
  proof: fun _ h => G'.edge_vert (adj_symm G' h)

@[simp]

中文:
定理 neighborSet_subset_verts
  条件: (G' : Subgraph G) (v : V)
  结论: G'.neighborSet v subseteq G'.verts
  证明: fun _ h => G'.edge_vert (adj_symm G' h)

@[simp]

Depends on / 依赖: adj_symm, edge_vert
-/
theorem neighborSet_subset_verts (G' : Subgraph G) (v : V) : G'.neighborSet v subseteq G'.verts :=
  fun _ h => G'.edge_vert (adj_symm G' h)

@[simp]
/--
theorem `mem_neighborSet` / 定理 `mem_neighborSet`

English:
theorem mem_neighborSet
  given: (G' : Subgraph G) (v w : V)
  statement: w in G'.neighborSet v ↔ G'.Adj v w
  proof: Iff.rfl

中文:
定理 mem_neighborSet
  条件: (G' : Subgraph G) (v w : V)
  结论: w in G'.neighborSet v ↔ G'.Adj v w
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_neighborSet (G' : Subgraph G) (v w : V) : w in G'.neighborSet v ↔ G'.Adj v w := Iff.rfl

/--
Definition of `coeNeighborSetEquiv` / `coeNeighborSetEquiv` 的定义

English:
definition coeNeighborSetEquiv
  signature: {G' : Subgraph G} (v : G'.verts)
  body: ⟨w, w.2⟩
  invFun w := ⟨⟨w, G'.edge_vert (G'.adj_symm w.2)⟩, w.2⟩

中文:
定义 coeNeighborSetEquiv
  签名: {G' : Subgraph G} (v : G'.verts)
  定义体: ⟨w, w.2⟩
  invFun w := ⟨⟨w, G'.edge_vert (G'.adj_symm w.2)⟩, w.2⟩
-/
def coeNeighborSetEquiv {G' : Subgraph G} (v : G'.verts) :
    G'.coe.neighborSet v ≃ G'.neighborSet v where
  toFun w := ⟨w, w.2⟩
  invFun w := ⟨⟨w, G'.edge_vert (G'.adj_symm w.2)⟩, w.2⟩

/--
Definition of `edgeSet` / `edgeSet` 的定义

English:
definition edgeSet
  signature: (G' : Subgraph G)
  body: Sym2.fromRel G'.symm

中文:
定义 edgeSet
  签名: (G' : Subgraph G)
  定义体: Sym2.fromRel G'.symm

Depends on / 依赖: Sym2.fromRel, fromRel
-/
def edgeSet (G' : Subgraph G) : Set (Sym2 V) := Sym2.fromRel G'.symm

/--
theorem `edgeSet_subset` / 定理 `edgeSet_subset`

English:
theorem edgeSet_subset
  given: (G' : Subgraph G)
  statement: G'.edgeSet subseteq G.edgeSet
  proof: Sym2.ind (fun _ _ => G'.adj_sub)

@[simp]

中文:
定理 edgeSet_subset
  条件: (G' : Subgraph G)
  结论: G'.edgeSet subseteq G.edgeSet
  证明: Sym2.ind (fun _ _ => G'.adj_sub)

@[simp]

Depends on / 依赖: Sym2.ind, adj_sub
-/
theorem edgeSet_subset (G' : Subgraph G) : G'.edgeSet subseteq G.edgeSet :=
  Sym2.ind (fun _ _ => G'.adj_sub)

@[simp]
/--
lemma `mem_edgeSet` / 引理 `mem_edgeSet`

English:
lemma mem_edgeSet
  given: {G' : Subgraph G} {v w : V}
  statement: s(v, w) in G'.edgeSet ↔ G'.Adj v w
  proof: .rfl

中文:
引理 mem_edgeSet
  条件: {G' : Subgraph G} {v w : V}
  结论: s(v, w) in G'.edgeSet ↔ G'.Adj v w
  证明: .rfl
-/
protected lemma mem_edgeSet {G' : Subgraph G} {v w : V} : s(v, w) in G'.edgeSet ↔ G'.Adj v w := .rfl

/--
lemma `edgeSet_coe` / 引理 `edgeSet_coe`

English:
lemma edgeSet_coe
  given: {G' : G.Subgraph}
  statement: G'.coe.edgeSet = Sym2.map (↑) ⁻¹' G'.edgeSet
  proof: by
  ext e; induction e using Sym2.ind; simp

中文:
引理 edgeSet_coe
  条件: {G' : G.Subgraph}
  结论: G'.coe.edgeSet = Sym2.map (↑) ⁻¹' G'.edgeSet
  证明: by
  ext e; induction e using Sym2.ind; simp
-/
@[simp] lemma edgeSet_coe {G' : G.Subgraph} : G'.coe.edgeSet = Sym2.map (↑) ⁻¹' G'.edgeSet := by
  ext e; induction e using Sym2.ind; simp

/--
lemma `image_coe_edgeSet_coe` / 引理 `image_coe_edgeSet_coe`

English:
lemma image_coe_edgeSet_coe
  given: (G' : G.Subgraph)
  statement: Sym2.map (↑) '' G'.coe.edgeSet = G'.edgeSet
  proof: by
  rw [edgeSet_coe]; rw [Set.image_preimage_eq_iff]
  rintro e he
  induction e using Sym2.ind with | h a b =>
  rw [Subgraph.mem_edgeSet] at he
  exact ⟨s(⟨a, edge_vert _ he⟩, ⟨b, edge_vert _ he.symm⟩), Sym2.map_mk ..⟩

@[simp]

中文:
引理 image_coe_edgeSet_coe
  条件: (G' : G.Subgraph)
  结论: Sym2.map (↑) '' G'.coe.edgeSet = G'.edgeSet
  证明: by
  rw [edgeSet_coe]; rw [Set.image_preimage_eq_iff]
  rintro e he
  induction e using Sym2.ind with | h a b =>
  rw [Subgraph.mem_edgeSet] at he
  exact ⟨s(⟨a, edge_vert _ he⟩, ⟨b, edge_vert _ he.symm⟩), Sym2.map_mk ..⟩

@[simp]

Depends on / 依赖: Set.image_preimage_eq_iff, Subgraph, Subgraph.mem_edgeSet, Sym2.ind, Sym2.map_mk, edgeSet_coe, edge_vert, he.symm, image_preimage_eq_iff, map_mk, mem_edgeSet
-/
lemma image_coe_edgeSet_coe (G' : G.Subgraph) : Sym2.map (↑) '' G'.coe.edgeSet = G'.edgeSet := by
  rw [edgeSet_coe]; rw [Set.image_preimage_eq_iff]
  rintro e he
  induction e using Sym2.ind with | h a b =>
  rw [Subgraph.mem_edgeSet] at he
  exact ⟨s(⟨a, edge_vert _ he⟩, ⟨b, edge_vert _ he.symm⟩), Sym2.map_mk ..⟩

@[simp]
/--
lemma `edgeSet_spanningCoe` / 引理 `edgeSet_spanningCoe`

English:
lemma edgeSet_spanningCoe
  given: (G' : G.Subgraph)
  statement: G'.spanningCoe.edgeSet = G'.edgeSet
  proof: by
  rfl

中文:
引理 edgeSet_spanningCoe
  条件: (G' : G.Subgraph)
  结论: G'.spanningCoe.edgeSet = G'.edgeSet
  证明: by
  rfl
-/
lemma edgeSet_spanningCoe (G' : G.Subgraph) : G'.spanningCoe.edgeSet = G'.edgeSet := by
  rfl

/--
theorem `mem_verts_of_mem_edge` / 定理 `mem_verts_of_mem_edge`

English:
theorem mem_verts_of_mem_edge
  statement: {G' : Subgraph G} {e : Sym2 V} {v : V} (he : e in G'.edgeSet)
  proof: by
  induction e
  rcases Sym2.mem_iff.mp hv with (rfl | rfl)
  · exact G'.edge_vert he
· exact G'.edge_vert G'.adj_symm he

中文:
定理 mem_verts_of_mem_edge
  结论: {G' : Subgraph G} {e : Sym2 V} {v : V} (he : e in G'.edgeSet)
  证明: by
  induction e
  rcases Sym2.mem_iff.mp hv with (rfl | rfl)
  · exact G'.edge_vert he
· exact G'.edge_vert G'.adj_symm he

Depends on / 依赖: Sym2.mem_iff.mp, adj_symm, edge_vert, mem_iff
-/
theorem mem_verts_of_mem_edge {G' : Subgraph G} {e : Sym2 V} {v : V} (he : e in G'.edgeSet)
    (hv : v in e) : v in G'.verts := by
  induction e
  rcases Sym2.mem_iff.mp hv with (rfl | rfl)
  · exact G'.edge_vert he
· exact G'.edge_vert G'.adj_symm he

/--
Definition of `incidenceSet` / `incidenceSet` 的定义

English:
definition incidenceSet
  signature: (G' : Subgraph G) (v : V)
  body: {e in G'.edgeSet | v in e}

中文:
定义 incidenceSet
  签名: (G' : Subgraph G) (v : V)
  定义体: {e in G'.edgeSet | v in e}

Depends on / 依赖: edgeSet
-/
def incidenceSet (G' : Subgraph G) (v : V) : Set (Sym2 V) := {e in G'.edgeSet | v in e}

/--
theorem `incidenceSet_subset_incidenceSet` / 定理 `incidenceSet_subset_incidenceSet`

English:
theorem incidenceSet_subset_incidenceSet
  given: (G' : Subgraph G) (v : V)
  proof: fun _ h => ⟨G'.edgeSet_subset h.1, h.2⟩

中文:
定理 incidenceSet_subset_incidenceSet
  条件: (G' : Subgraph G) (v : V)
  证明: fun _ h => ⟨G'.edgeSet_subset h.1, h.2⟩

Depends on / 依赖: edgeSet_subset
-/
theorem incidenceSet_subset_incidenceSet (G' : Subgraph G) (v : V) :
    G'.incidenceSet v subseteq G.incidenceSet v :=
  fun _ h => ⟨G'.edgeSet_subset h.1, h.2⟩

/--
theorem `incidenceSet_subset` / 定理 `incidenceSet_subset`

English:
theorem incidenceSet_subset
  given: (G' : Subgraph G) (v : V)
  statement: G'.incidenceSet v subseteq G'.edgeSet
  proof: fun _ h => h.1

中文:
定理 incidenceSet_subset
  条件: (G' : Subgraph G) (v : V)
  结论: G'.incidenceSet v subseteq G'.edgeSet
  证明: fun _ h => h.1
-/
theorem incidenceSet_subset (G' : Subgraph G) (v : V) : G'.incidenceSet v subseteq G'.edgeSet :=
  fun _ h => h.1

/--
Definition of `vert` / `vert` 的定义

English:
abbreviation vert
  signature: (G' : Subgraph G) (v : V) (h : v in G'.verts)
  body: ⟨v, h⟩

中文:
缩写 vert
  签名: (G' : Subgraph G) (v : V) (h : v in G'.verts)
  定义体: ⟨v, h⟩
-/
abbrev vert (G' : Subgraph G) (v : V) (h : v in G'.verts) : G'.verts := ⟨v, h⟩

/--
Definition of `copy` / `copy` 的定义

English:
definition copy
  signature: (G' : Subgraph G) (V'' : Set V) (hV : V'' = G'.verts)
  body: V''
  Adj := adj'
  adj_sub := hadj.symm ▸ G'.adj_sub
  edge_vert := hV.symm ▸ hadj.symm ▸ G'.edge_vert
  symm := hadj.symm ▸ G'.symm

中文:
定义 copy
  签名: (G' : Subgraph G) (V'' : Set V) (hV : V'' = G'.verts)
  定义体: V''
  Adj := adj'
  adj_sub := hadj.symm ▸ G'.adj_sub
  edge_vert := hV.symm ▸ hadj.symm ▸ G'.edge_vert
  symm := hadj.symm ▸ G'.symm
-/
def copy (G' : Subgraph G) (V'' : Set V) (hV : V'' = G'.verts)
    (adj' : V -> V -> Prop) (hadj : adj' = G'.Adj) : Subgraph G where
  verts := V''
  Adj := adj'
  adj_sub := hadj.symm ▸ G'.adj_sub
  edge_vert := hV.symm ▸ hadj.symm ▸ G'.edge_vert
  symm := hadj.symm ▸ G'.symm

/--
theorem `copy_eq` / 定理 `copy_eq`

English:
theorem copy_eq
  statement: (G' : Subgraph G) (V'' : Set V) (hV : V'' = G'.verts)
  proof: Subgraph.ext hV hadj

中文:
定理 copy_eq
  结论: (G' : Subgraph G) (V'' : Set V) (hV : V'' = G'.verts)
  证明: Subgraph.ext hV hadj

Depends on / 依赖: Subgraph, Subgraph.ext
-/
theorem copy_eq (G' : Subgraph G) (V'' : Set V) (hV : V'' = G'.verts)
    (adj' : V -> V -> Prop) (hadj : adj' = G'.Adj) : G'.copy V'' hV adj' hadj = G' :=
  Subgraph.ext hV hadj

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Max G.Subgraph
  body: { verts := G₁.verts union G₂.verts
      Adj := G₁.Adj ⊔ G₂.Adj
      adj_sub := fun hab => Or.elim hab (fun h => G₁.adj_sub h) fun h => G₂.adj_sub h
      edge_vert := Or.imp (fun h => G₁.edge_vert h) fun h => G₂.edge_vert h
      symm.symm _ _ := Or.imp G₁.adj_symm G₂.adj_symm }

中文:
实例 :
  签名: Max G.Subgraph
  定义体: { verts := G₁.verts union G₂.verts
      Adj := G₁.Adj ⊔ G₂.Adj
      adj_sub := fun hab => Or.elim hab (fun h => G₁.adj_sub h) fun h => G₂.adj_sub h
      edge_vert := Or.imp (fun h => G₁.edge_vert h) fun h => G₂.edge_vert h
      symm.symm _ _ := Or.imp G₁.adj_symm G₂.adj_symm }

Depends on / 依赖: Or.elim, Or.imp, adj_sub, adj_symm, edge_vert, symm.symm
-/
instance : Max G.Subgraph where
  max G₁ G₂ :=
    { verts := G₁.verts union G₂.verts
      Adj := G₁.Adj ⊔ G₂.Adj
      adj_sub := fun hab => Or.elim hab (fun h => G₁.adj_sub h) fun h => G₂.adj_sub h
      edge_vert := Or.imp (fun h => G₁.edge_vert h) fun h => G₂.edge_vert h
      symm.symm _ _ := Or.imp G₁.adj_symm G₂.adj_symm }

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Min G.Subgraph
  body: { verts := G₁.verts inter G₂.verts
      Adj := G₁.Adj ⊓ G₂.Adj
      adj_sub := fun hab => G₁.adj_sub hab.1
      edge_vert := And.imp (fun h => G₁.edge_vert h) fun h => G₂.edge_vert h
      symm.symm _ _ := And.imp G₁.adj_symm G₂.adj_symm }

中文:
实例 :
  签名: Min G.Subgraph
  定义体: { verts := G₁.verts inter G₂.verts
      Adj := G₁.Adj ⊓ G₂.Adj
      adj_sub := fun hab => G₁.adj_sub hab.1
      edge_vert := And.imp (fun h => G₁.edge_vert h) fun h => G₂.edge_vert h
      symm.symm _ _ := And.imp G₁.adj_symm G₂.adj_symm }

Depends on / 依赖: And.imp, adj_sub, adj_symm, edge_vert, symm.symm
-/
instance : Min G.Subgraph where
  min G₁ G₂ :=
    { verts := G₁.verts inter G₂.verts
      Adj := G₁.Adj ⊓ G₂.Adj
      adj_sub := fun hab => G₁.adj_sub hab.1
      edge_vert := And.imp (fun h => G₁.edge_vert h) fun h => G₂.edge_vert h
      symm.symm _ _ := And.imp G₁.adj_symm G₂.adj_symm }

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Top G.Subgraph
  body: Set.univ
  top.Adj := G.Adj
  top.adj_sub := id
  top.edge_vert := @fun v _ _ => Set.mem_univ v
  top.symm := G.symm

中文:
实例 :
  签名: Top G.Subgraph
  定义体: Set.univ
  top.Adj := G.Adj
  top.adj_sub := id
  top.edge_vert := @fun v _ _ => Set.mem_univ v
  top.symm := G.symm

Depends on / 依赖: Set.univ
-/
instance : Top G.Subgraph where
  top.verts := Set.univ
  top.Adj := G.Adj
  top.adj_sub := id
  top.edge_vert := @fun v _ _ => Set.mem_univ v
  top.symm := G.symm

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Bot G.Subgraph
  body: ∅
  bot.Adj := ⊥
  bot.adj_sub := False.elim
  bot.edge_vert := False.elim

中文:
实例 :
  签名: Bot G.Subgraph
  定义体: ∅
  bot.Adj := ⊥
  bot.adj_sub := False.elim
  bot.edge_vert := False.elim
-/
instance : Bot G.Subgraph where
  bot.verts := ∅
  bot.Adj := ⊥
  bot.adj_sub := False.elim
  bot.edge_vert := False.elim

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SupSet G.Subgraph
  body: { verts := ⋃ G' in s, verts G'
      Adj := fun a b => exists G' in s, Adj G' a b
      adj_sub := by
        rintro a b ⟨G', -, hab⟩
        exact G'.adj_sub hab
      edge_vert := by
        rintro a b ⟨G', hG', hab⟩
        exact Set.mem_iUnion₂_of_mem hG' (G'.edge_vert hab)
      symm.symm a b h

中文:
实例 :
  签名: SupSet G.Subgraph
  定义体: { verts := ⋃ G' in s, verts G'
      Adj := fun a b => exists G' in s, Adj G' a b
      adj_sub := by
        rintro a b ⟨G', -, hab⟩
        exact G'.adj_sub hab
      edge_vert := by
        rintro a b ⟨G', hG', hab⟩
        exact Set.mem_iUnion₂_of_mem hG' (G'.edge_vert hab)
      symm.symm a b h

Depends on / 依赖: Set.mem_iUnion, adj_comm, adj_sub, edge_vert, symm.symm
-/
instance : SupSet G.Subgraph where
  sSup s :=
    { verts := ⋃ G' in s, verts G'
      Adj := fun a b => exists G' in s, Adj G' a b
      adj_sub := by
        rintro a b ⟨G', -, hab⟩
        exact G'.adj_sub hab
      edge_vert := by
        rintro a b ⟨G', hG', hab⟩
        exact Set.mem_iUnion₂_of_mem hG' (G'.edge_vert hab)
      symm.symm a b h := by simpa [adj_comm] using h }

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: InfSet G.Subgraph
  body: { verts := ⋂ G' in s, verts G'
      Adj := fun a b => (forall ⦃G'⦄, G' in s -> Adj G' a b) ∧ G.Adj a b
      adj_sub := And.right
edge_vert := fun hab => Set.mem_iInter₂_of_mem fun G' hG' => G'.edge_vert hab.1 hG'
      symm.symm _ _ := And.imp (forall₂_imp fun _ _ => Adj.symm) G.adj_symm }

@[simp

中文:
实例 :
  签名: InfSet G.Subgraph
  定义体: { verts := ⋂ G' in s, verts G'
      Adj := fun a b => (forall ⦃G'⦄, G' in s -> Adj G' a b) ∧ G.Adj a b
      adj_sub := And.right
edge_vert := fun hab => Set.mem_iInter₂_of_mem fun G' hG' => G'.edge_vert hab.1 hG'
      symm.symm _ _ := And.imp (forall₂_imp fun _ _ => Adj.symm) G.adj_symm }

@[simp

Depends on / 依赖: Adj.symm, And.imp, And.right, G.Adj, G.adj_symm, Set.mem_iInter, adj_sub, adj_symm, edge_vert, symm.symm
-/
instance : InfSet G.Subgraph where
  sInf s :=
    { verts := ⋂ G' in s, verts G'
      Adj := fun a b => (forall ⦃G'⦄, G' in s -> Adj G' a b) ∧ G.Adj a b
      adj_sub := And.right
edge_vert := fun hab => Set.mem_iInter₂_of_mem fun G' hG' => G'.edge_vert hab.1 hG'
      symm.symm _ _ := And.imp (forall₂_imp fun _ _ => Adj.symm) G.adj_symm }

@[simp]
/--
theorem `sup_adj` / 定理 `sup_adj`

English:
theorem sup_adj
  statement: (G₁ ⊔ G₂).Adj a b ↔ G₁.Adj a b ∨ G₂.Adj a b
  proof: Iff.rfl

@[simp]

中文:
定理 sup_adj
  结论: (G₁ ⊔ G₂).Adj a b ↔ G₁.Adj a b ∨ G₂.Adj a b
  证明: Iff.rfl

@[simp]

Depends on / 依赖: Iff.rfl
-/
theorem sup_adj : (G₁ ⊔ G₂).Adj a b ↔ G₁.Adj a b ∨ G₂.Adj a b :=
  Iff.rfl

@[simp]
/--
theorem `inf_adj` / 定理 `inf_adj`

English:
theorem inf_adj
  statement: (G₁ ⊓ G₂).Adj a b ↔ G₁.Adj a b ∧ G₂.Adj a b
  proof: Iff.rfl

@[simp]

中文:
定理 inf_adj
  结论: (G₁ ⊓ G₂).Adj a b ↔ G₁.Adj a b ∧ G₂.Adj a b
  证明: Iff.rfl

@[simp]

Depends on / 依赖: Iff.rfl
-/
theorem inf_adj : (G₁ ⊓ G₂).Adj a b ↔ G₁.Adj a b ∧ G₂.Adj a b :=
  Iff.rfl

@[simp]
/--
theorem `top_adj` / 定理 `top_adj`

English:
theorem top_adj
  statement: (⊤ : Subgraph G).Adj a b ↔ G.Adj a b
  proof: Iff.rfl

@[simp]

中文:
定理 top_adj
  结论: (⊤ : Subgraph G).Adj a b ↔ G.Adj a b
  证明: Iff.rfl

@[simp]

Depends on / 依赖: Iff.rfl
-/
theorem top_adj : (⊤ : Subgraph G).Adj a b ↔ G.Adj a b :=
  Iff.rfl

@[simp]
/--
theorem `not_bot_adj` / 定理 `not_bot_adj`

English:
theorem not_bot_adj
  statement: ¬ (⊥ : Subgraph G).Adj a b
  proof: not_false

@[simp]

中文:
定理 not_bot_adj
  结论: ¬ (⊥ : Subgraph G).Adj a b
  证明: not_false

@[simp]

Depends on / 依赖: not_false
-/
theorem not_bot_adj : ¬ (⊥ : Subgraph G).Adj a b :=
  not_false

@[simp]
/--
theorem `verts_sup` / 定理 `verts_sup`

English:
theorem verts_sup
  given: (G₁ G₂ : G.Subgraph)
  statement: (G₁ ⊔ G₂).verts = G₁.verts union G₂.verts
  proof: rfl

@[simp]

中文:
定理 verts_sup
  条件: (G₁ G₂ : G.Subgraph)
  结论: (G₁ ⊔ G₂).verts = G₁.verts union G₂.verts
  证明: rfl

@[simp]
-/
theorem verts_sup (G₁ G₂ : G.Subgraph) : (G₁ ⊔ G₂).verts = G₁.verts union G₂.verts :=
  rfl

@[simp]
/--
theorem `verts_inf` / 定理 `verts_inf`

English:
theorem verts_inf
  given: (G₁ G₂ : G.Subgraph)
  statement: (G₁ ⊓ G₂).verts = G₁.verts inter G₂.verts
  proof: rfl

@[simp]

中文:
定理 verts_inf
  条件: (G₁ G₂ : G.Subgraph)
  结论: (G₁ ⊓ G₂).verts = G₁.verts inter G₂.verts
  证明: rfl

@[simp]
-/
theorem verts_inf (G₁ G₂ : G.Subgraph) : (G₁ ⊓ G₂).verts = G₁.verts inter G₂.verts :=
  rfl

@[simp]
/--
theorem `verts_top` / 定理 `verts_top`

English:
theorem verts_top
  statement: (⊤ : G.Subgraph).verts = Set.univ
  proof: rfl

@[simp]

中文:
定理 verts_top
  结论: (⊤ : G.Subgraph).verts = Set.univ
  证明: rfl

@[simp]
-/
theorem verts_top : (⊤ : G.Subgraph).verts = Set.univ :=
  rfl

@[simp]
/--
theorem `verts_bot` / 定理 `verts_bot`

English:
theorem verts_bot
  statement: (⊥ : G.Subgraph).verts = ∅
  proof: rfl

中文:
定理 verts_bot
  结论: (⊥ : G.Subgraph).verts = ∅
  证明: rfl
-/
theorem verts_bot : (⊥ : G.Subgraph).verts = ∅ :=
  rfl

/--
theorem `eq_bot_iff_verts_eq_empty` / 定理 `eq_bot_iff_verts_eq_empty`

English:
theorem eq_bot_iff_verts_eq_empty
  given: (G' : G.Subgraph)
  statement: G' = ⊥ ↔ G'.verts = ∅
  proof: ⟨(· ▸ verts_bot), fun h => Subgraph.ext (h ▸ verts_bot (G := G))
    funext₂ fun _ _ => propext ⟨fun h' => (h ▸ h'.fst_mem :), False.elim⟩⟩

中文:
定理 eq_bot_iff_verts_eq_empty
  条件: (G' : G.Subgraph)
  结论: G' = ⊥ ↔ G'.verts = ∅
  证明: ⟨(· ▸ verts_bot), fun h => Subgraph.ext (h ▸ verts_bot (G := G))
    funext₂ fun _ _ => propext ⟨fun h' => (h ▸ h'.fst_mem :), False.elim⟩⟩

Depends on / 依赖: False.elim, Subgraph, Subgraph.ext, fst_mem, propext, verts_bot
-/
theorem eq_bot_iff_verts_eq_empty (G' : G.Subgraph) : G' = ⊥ ↔ G'.verts = ∅ :=
⟨(· ▸ verts_bot), fun h => Subgraph.ext (h ▸ verts_bot (G := G))
    funext₂ fun _ _ => propext ⟨fun h' => (h ▸ h'.fst_mem :), False.elim⟩⟩

/--
theorem `ne_bot_iff_nonempty_verts` / 定理 `ne_bot_iff_nonempty_verts`

English:
theorem ne_bot_iff_nonempty_verts
  given: (G' : G.Subgraph)
  statement: G' != ⊥ ↔ G'.verts.Nonempty
  proof: G'.eq_bot_iff_verts_eq_empty.not.trans Set.nonempty_iff_ne_empty.symm

@[simp]

中文:
定理 ne_bot_iff_nonempty_verts
  条件: (G' : G.Subgraph)
  结论: G' != ⊥ ↔ G'.verts.Nonempty
  证明: G'.eq_bot_iff_verts_eq_empty.not.trans Set.nonempty_iff_ne_empty.symm

@[simp]

Depends on / 依赖: Set.nonempty_iff_ne_empty.symm, eq_bot_iff_verts_eq_empty, eq_bot_iff_verts_eq_empty.not.trans, nonempty_iff_ne_empty
-/
theorem ne_bot_iff_nonempty_verts (G' : G.Subgraph) : G' != ⊥ ↔ G'.verts.Nonempty :=
G'.eq_bot_iff_verts_eq_empty.not.trans Set.nonempty_iff_ne_empty.symm

@[simp]
/--
theorem `sSup_adj` / 定理 `sSup_adj`

English:
theorem sSup_adj
  given: {s : Set G.Subgraph}
  statement: (sSup s).Adj a b ↔ exists G in s, Adj G a b
  proof: Iff.rfl

@[simp]

中文:
定理 sSup_adj
  条件: {s : Set G.Subgraph}
  结论: (sSup s).Adj a b ↔ 存在 G in s, Adj G a b
  证明: Iff.rfl

@[simp]

Depends on / 依赖: Iff.rfl
-/
theorem sSup_adj {s : Set G.Subgraph} : (sSup s).Adj a b ↔ exists G in s, Adj G a b :=
  Iff.rfl

@[simp]
/--
theorem `sInf_adj` / 定理 `sInf_adj`

English:
theorem sInf_adj
  given: {s : Set G.Subgraph}
  statement: (sInf s).Adj a b ↔ (forall G' in s, Adj G' a b) ∧ G.Adj a b
  proof: Iff.rfl

@[simp]

中文:
定理 sInf_adj
  条件: {s : Set G.Subgraph}
  结论: (sInf s).Adj a b ↔ (对任意 G' in s, Adj G' a b) ∧ G.Adj a b
  证明: Iff.rfl

@[simp]

Depends on / 依赖: Iff.rfl
-/
theorem sInf_adj {s : Set G.Subgraph} : (sInf s).Adj a b ↔ (forall G' in s, Adj G' a b) ∧ G.Adj a b :=
  Iff.rfl

@[simp]
/--
theorem `iSup_adj` / 定理 `iSup_adj`

English:
theorem iSup_adj
  given: {f : ι -> G.Subgraph}
  statement: (⨆ i, f i).Adj a b ↔ exists i, (f i).Adj a b
  proof: by
  simp [iSup]

@[simp]

中文:
定理 iSup_adj
  条件: {f : ι -> G.Subgraph}
  结论: (⨆ i, f i).Adj a b ↔ 存在 i, (f i).Adj a b
  证明: by
  simp [iSup]

@[simp]
-/
theorem iSup_adj {f : ι -> G.Subgraph} : (⨆ i, f i).Adj a b ↔ exists i, (f i).Adj a b := by
  simp [iSup]

@[simp]
/--
theorem `iInf_adj` / 定理 `iInf_adj`

English:
theorem iInf_adj
  given: {f : ι -> G.Subgraph}
  statement: (⨅ i, f i).Adj a b ↔ (forall i, (f i).Adj a b) ∧ G.Adj a b
  proof: by
  simp [iInf]

中文:
定理 iInf_adj
  条件: {f : ι -> G.Subgraph}
  结论: (⨅ i, f i).Adj a b ↔ (对任意 i, (f i).Adj a b) ∧ G.Adj a b
  证明: by
  simp [iInf]

Depends on / 依赖: Finset, Finset.min, Function, Function.comp_def, coe_inf, comp_def, id_eq, mem_of_min
-/
theorem iInf_adj {f : ι -> G.Subgraph} : (⨅ i, f i).Adj a b ↔ (forall i, (f i).Adj a b) ∧ G.Adj a b := by
  simp [iInf]

/--
theorem `sInf_adj_of_nonempty` / 定理 `sInf_adj_of_nonempty`

English:
theorem sInf_adj_of_nonempty
  given: {s : Set G.Subgraph} (hs : s.Nonempty)
  proof: sInf_adj.trans
and_iff_left_of_imp by
      obtain ⟨G', hG'⟩ := hs
      exact fun h => G'.adj_sub (h _ hG')

中文:
定理 sInf_adj_of_nonempty
  条件: {s : Set G.Subgraph} (hs : s.Nonempty)
  证明: sInf_adj.trans
and_iff_left_of_imp by
      obtain ⟨G', hG'⟩ := hs
      exact fun h => G'.adj_sub (h _ hG')

Depends on / 依赖: WithTop, WithTop.coe_untop, adj_sub, and_iff_left_of_imp, coe_untop, min_le_of_eq, sInf_adj, sInf_adj.trans
-/
theorem sInf_adj_of_nonempty {s : Set G.Subgraph} (hs : s.Nonempty) :
    (sInf s).Adj a b ↔ forall G' in s, Adj G' a b :=
sInf_adj.trans
and_iff_left_of_imp by
      obtain ⟨G', hG'⟩ := hs
      exact fun h => G'.adj_sub (h _ hG')

/--
theorem `iInf_adj_of_nonempty` / 定理 `iInf_adj_of_nonempty`

English:
theorem iInf_adj_of_nonempty
  given: [Nonempty ι] {f : ι -> G.Subgraph}
  proof: by
  rw [iInf]; rw [sInf_adj_of_nonempty (Set.range_nonempty _)]
  simp

@[simp]

中文:
定理 iInf_adj_of_nonempty
  条件: [Nonempty ι] {f : ι -> G.Subgraph}
  证明: by
  rw [iInf]; rw [sInf_adj_of_nonempty (Set.range_nonempty _)]
  simp

@[simp]

Depends on / 依赖: Set.range_nonempty, range_nonempty, sInf_adj_of_nonempty
-/
theorem iInf_adj_of_nonempty [Nonempty ι] {f : ι -> G.Subgraph} :
    (⨅ i, f i).Adj a b ↔ forall i, (f i).Adj a b := by
  rw [iInf]; rw [sInf_adj_of_nonempty (Set.range_nonempty _)]
  simp

@[simp]
/--
theorem `verts_sSup` / 定理 `verts_sSup`

English:
theorem verts_sSup
  given: (s : Set G.Subgraph)
  statement: (sSup s).verts = ⋃ G' in s, verts G'
  proof: rfl

@[simp]

中文:
定理 verts_sSup
  条件: (s : Set G.Subgraph)
  结论: (sSup s).verts = ⋃ G' in s, verts G'
  证明: rfl

@[simp]
-/
theorem verts_sSup (s : Set G.Subgraph) : (sSup s).verts = ⋃ G' in s, verts G' :=
  rfl

@[simp]
/--
theorem `verts_sInf` / 定理 `verts_sInf`

English:
theorem verts_sInf
  given: (s : Set G.Subgraph)
  statement: (sInf s).verts = ⋂ G' in s, verts G'
  proof: rfl

@[simp]

中文:
定理 verts_sInf
  条件: (s : Set G.Subgraph)
  结论: (sInf s).verts = ⋂ G' in s, verts G'
  证明: rfl

@[simp]

Depends on / 依赖: isLeast_min, le_isGLB_iff
-/
theorem verts_sInf (s : Set G.Subgraph) : (sInf s).verts = ⋂ G' in s, verts G' :=
  rfl

@[simp]
/--
theorem `verts_iSup` / 定理 `verts_iSup`

English:
theorem verts_iSup
  given: {f : ι -> G.Subgraph}
  statement: (⨆ i, f i).verts = ⋃ i, (f i).verts
  proof: by simp [iSup]

@[simp]

中文:
定理 verts_iSup
  条件: {f : ι -> G.Subgraph}
  结论: (⨆ i, f i).verts = ⋃ i, (f i).verts
  证明: by simp [iSup]

@[simp]
-/
theorem verts_iSup {f : ι -> G.Subgraph} : (⨆ i, f i).verts = ⋃ i, (f i).verts := by simp [iSup]

@[simp]
/--
theorem `verts_iInf` / 定理 `verts_iInf`

English:
theorem verts_iInf
  given: {f : ι -> G.Subgraph}
  statement: (⨅ i, f i).verts = ⋂ i, (f i).verts
  proof: by simp [iInf]

中文:
定理 verts_iInf
  条件: {f : ι -> G.Subgraph}
  结论: (⨅ i, f i).verts = ⋂ i, (f i).verts
  证明: by simp [iInf]

Depends on / 依赖: Finset, Finset.max, Function, Function.comp_def, coe_sup, comp_def, id_eq, mem_of_max
-/
theorem verts_iInf {f : ι -> G.Subgraph} : (⨅ i, f i).verts = ⋂ i, (f i).verts := by simp [iInf]

/--
lemma `coe_bot` / 引理 `coe_bot`

English:
lemma coe_bot
  statement: (⊥ : G.Subgraph).coe = ⊥
  proof: rfl

中文:
引理 coe_bot
  结论: (⊥ : G.Subgraph).coe = ⊥
  证明: rfl
-/
@[simp] lemma coe_bot : (⊥ : G.Subgraph).coe = ⊥ := rfl

/--
lemma `IsInduced.top` / 引理 `IsInduced.top`

English:
lemma IsInduced.top
  statement: (⊤ : G.Subgraph).IsInduced
  proof: fun _ _ _ _ => id

中文:
引理 IsInduced.top
  结论: (⊤ : G.Subgraph).IsInduced
  证明: fun _ _ _ _ => id

Depends on / 依赖: _mem
-/
@[simp] lemma IsInduced.top : (⊤ : G.Subgraph).IsInduced := fun _ _ _ _ => id

/--
Definition of `topIso` / `topIso` 的定义

English:
definition topIso
  signature: : (⊤ : G.Subgraph).coe ≃g G where
  body: (↑)
  invFun a := ⟨a, Set.mem_univ _⟩
  left_inv _ := Subtype.eta ..
  map_rel_iff' := .rfl

中文:
定义 topIso
  签名: : (⊤ : G.Subgraph).coe ≃g G where
  定义体: (↑)
  invFun a := ⟨a, Set.mem_univ _⟩
  left_inv _ := Subtype.eta ..
  map_rel_iff' := .rfl
-/
def topIso : (⊤ : G.Subgraph).coe ≃g G where
  toFun := (↑)
  invFun a := ⟨a, Set.mem_univ _⟩
  left_inv _ := Subtype.eta ..
  map_rel_iff' := .rfl

/--
theorem `verts_spanningCoe_injective` / 定理 `verts_spanningCoe_injective`

English:
theorem verts_spanningCoe_injective
  proof: by
  intro G₁ G₂ h
  rw [Prod.ext_iff] at h
  exact Subgraph.ext h.1 (spanningCoe_inj.1 h.2)

中文:
定理 verts_spanningCoe_injective
  证明: by
  intro G₁ G₂ h
  rw [Prod.ext_iff] at h
  exact Subgraph.ext h.1 (spanningCoe_inj.1 h.2)

Depends on / 依赖: Prod.ext_iff, Subgraph, Subgraph.ext, ext_iff, isGreatest_max, isLUB_le_iff, spanningCoe_inj
-/
theorem verts_spanningCoe_injective :
    (fun G' : Subgraph G => (G'.verts, G'.spanningCoe)).Injective := by
  intro G₁ G₂ h
  rw [Prod.ext_iff] at h
  exact Subgraph.ext h.1 (spanningCoe_inj.1 h.2)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PartialOrder G.Subgraph
  body: PartialOrder.lift _ verts_spanningCoe_injective
  le x y := x.verts subseteq y.verts ∧ forall ⦃v w : V⦄, x.Adj v w -> y.Adj v w

中文:
实例 :
  签名: PartialOrder G.Subgraph
  定义体: PartialOrder.lift _ verts_spanningCoe_injective
  le x y := x.verts subseteq y.verts ∧ forall ⦃v w : V⦄, x.Adj v w -> y.Adj v w

Depends on / 依赖: PartialOrder, PartialOrder.lift, _mem, le_max, s.le_max, s.max, trans_lt, verts_spanningCoe_injective
-/
instance : PartialOrder G.Subgraph where
  __ := PartialOrder.lift _ verts_spanningCoe_injective
  le x y := x.verts subseteq y.verts ∧ forall ⦃v w : V⦄, x.Adj v w -> y.Adj v w

/--
Instance `distribLattice` / 实例 `distribLattice`

English:
instance distribLattice
  signature: : DistribLattice G.Subgraph
  body: verts_spanningCoe_injective.distribLattice _ .rfl .rfl (fun _ _ => rfl) fun _ _ => rfl

中文:
实例 distribLattice
  签名: : DistribLattice G.Subgraph
  定义体: verts_spanningCoe_injective.distribLattice _ .rfl .rfl (fun _ _ => rfl) fun _ _ => rfl

Depends on / 依赖: distribLattice, verts_spanningCoe_injective, verts_spanningCoe_injective.distribLattice
-/
instance distribLattice : DistribLattice G.Subgraph :=
  verts_spanningCoe_injective.distribLattice _ .rfl .rfl (fun _ _ => rfl) fun _ _ => rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: BoundedOrder (Subgraph G)
  body: ⟨Set.subset_univ _, fun _ _ => x.adj_sub⟩
  bot_le _ := ⟨Set.empty_subset _, fun _ _ => False.elim⟩

中文:
实例 :
  签名: BoundedOrder (Subgraph G)
  定义体: ⟨Set.subset_univ _, fun _ _ => x.adj_sub⟩
  bot_le _ := ⟨Set.empty_subset _, fun _ _ => False.elim⟩

Depends on / 依赖: Set.subset_univ, adj_sub, subset_univ, x.adj_sub
-/
instance : BoundedOrder (Subgraph G) where
  le_top x := ⟨Set.subset_univ _, fun _ _ => x.adj_sub⟩
  bot_le _ := ⟨Set.empty_subset _, fun _ _ => False.elim⟩

set_option linter.unusedVariables false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CompleteLattice (Subgraph G)
  body: ⟨fun G' hG' => ⟨Set.subset_biUnion_of_mem hG', fun _ _ hab => ⟨G', hG', hab⟩⟩,
      fun G' hG' =>
        ⟨Set.iUnion₂_subset fun _ hH => (hG' hH).1, fun a b ⟨H, hH, hab⟩ => (hG' hH).2 hab⟩⟩
  isGLB_sInf _ :=
    ⟨fun G' hG' => ⟨Set.iInter₂_subset G' hG', fun _ _ hab => hab.1 hG'⟩,
      fun G' hG'

中文:
实例 :
  签名: CompleteLattice (Subgraph G)
  定义体: ⟨fun G' hG' => ⟨Set.subset_biUnion_of_mem hG', fun _ _ hab => ⟨G', hG', hab⟩⟩,
      fun G' hG' =>
        ⟨Set.iUnion₂_subset fun _ hH => (hG' hH).1, fun a b ⟨H, hH, hab⟩ => (hG' hH).2 hab⟩⟩
  isGLB_sInf _ :=
    ⟨fun G' hG' => ⟨Set.iInter₂_subset G' hG', fun _ _ hab => hab.1 hG'⟩,
      fun G' hG'

Depends on / 依赖: Set.iInter, Set.iUnion, Set.subset_biUnion_of_mem, Set.subset_iInter, adj_sub, isGLB_sInf, subset_biUnion_of_mem
-/
instance : CompleteLattice (Subgraph G) where
  isLUB_sSup _ :=
    ⟨fun G' hG' => ⟨Set.subset_biUnion_of_mem hG', fun _ _ hab => ⟨G', hG', hab⟩⟩,
      fun G' hG' =>
        ⟨Set.iUnion₂_subset fun _ hH => (hG' hH).1, fun a b ⟨H, hH, hab⟩ => (hG' hH).2 hab⟩⟩
  isGLB_sInf _ :=
    ⟨fun G' hG' => ⟨Set.iInter₂_subset G' hG', fun _ _ hab => hab.1 hG'⟩,
      fun G' hG' =>
        ⟨Set.subset_iInter₂ fun _ hH => (hG' hH).1, fun _ _ hab =>
         ⟨fun _ hH => (hG' hH).2 hab, G'.adj_sub hab⟩⟩⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CompletelyDistribLattice G.Subgraph
  body: fast_instance% .ofMinimalAxioms {
    iInf_iSup_eq f := Subgraph.ext (by simpa using! iInf_iSup_eq)
      (by ext; simp [Classical.skolem]) }

中文:
实例 :
  签名: CompletelyDistribLattice G.Subgraph
  定义体: fast_instance% .ofMinimalAxioms {
    iInf_iSup_eq f := Subgraph.ext (by simpa using! iInf_iSup_eq)
      (by ext; simp [Classical.skolem]) }

Depends on / 依赖: Classical, Classical.skolem, Subgraph, Subgraph.ext, fast_instance, iInf_iSup_eq, ofMinimalAxioms, skolem
-/
instance : CompletelyDistribLattice G.Subgraph :=
  fast_instance% .ofMinimalAxioms {
    iInf_iSup_eq f := Subgraph.ext (by simpa using! iInf_iSup_eq)
      (by ext; simp [Classical.skolem]) }

/--
lemma `verts_mono` / 引理 `verts_mono`

English:
lemma verts_mono
  given: {H H' : G.Subgraph} (h : H <= H')
  statement: H.verts subseteq H'.verts
  proof: h.1

中文:
引理 verts_mono
  条件: {H H' : G.Subgraph} (h : H <= H')
  结论: H.verts subseteq H'.verts
  证明: h.1

Depends on / 依赖: _mem, le_antisymm, le_min
-/
@[gcongr] lemma verts_mono {H H' : G.Subgraph} (h : H <= H') : H.verts subseteq H'.verts := h.1
/--
lemma `verts_monotone` / 引理 `verts_monotone`

English:
lemma verts_monotone
  statement: Monotone (verts : G.Subgraph -> Set V)
  proof: fun _ _ h => h.1

@[simps]

中文:
引理 verts_monotone
  结论: Monotone (verts : G.Subgraph -> Set V)
  证明: fun _ _ h => h.1

@[simps]

Depends on / 依赖: _mem, le_antisymm, le_max
-/
lemma verts_monotone : Monotone (verts : G.Subgraph -> Set V) := fun _ _ h => h.1

@[simps]
/--
Instance `subgraphInhabited` / 实例 `subgraphInhabited`

English:
instance subgraphInhabited
  signature: : Inhabited (Subgraph G)
  body: ⟨⊥⟩

@[simp]

中文:
实例 subgraphInhabited
  签名: : Inhabited (Subgraph G)
  定义体: ⟨⊥⟩

@[simp]

Depends on / 依赖: _mem
-/
instance subgraphInhabited : Inhabited (Subgraph G) := ⟨⊥⟩

@[simp]
/--
theorem `neighborSet_sup` / 定理 `neighborSet_sup`

English:
theorem neighborSet_sup
  given: {H H' : G.Subgraph} (v : V)
  proof: rfl

@[simp]

中文:
定理 neighborSet_sup
  条件: {H H' : G.Subgraph} (v : V)
  证明: rfl

@[simp]

Depends on / 依赖: isGLB_lt_isLUB_of_ne, isGreatest_max, isLeast_min, s.isGreatest_max, s.isLeast_min
-/
theorem neighborSet_sup {H H' : G.Subgraph} (v : V) :
    (H ⊔ H').neighborSet v = H.neighborSet v union H'.neighborSet v := rfl

@[simp]
/--
theorem `neighborSet_inf` / 定理 `neighborSet_inf`

English:
theorem neighborSet_inf
  given: {H H' : G.Subgraph} (v : V)
  proof: rfl

@[simp]

中文:
定理 neighborSet_inf
  条件: {H H' : G.Subgraph} (v : V)
  证明: rfl

@[simp]

Depends on / 依赖: _lt_max, one_lt_card, s.min
-/
theorem neighborSet_inf {H H' : G.Subgraph} (v : V) :
    (H ⊓ H').neighborSet v = H.neighborSet v inter H'.neighborSet v := rfl

@[simp]
/--
theorem `neighborSet_top` / 定理 `neighborSet_top`

English:
theorem neighborSet_top
  given: (v : V)
  statement: (⊤ : G.Subgraph).neighborSet v = G.neighborSet v
  proof: rfl

@[simp]

中文:
定理 neighborSet_top
  条件: (v : V)
  结论: (⊤ : G.Subgraph).neighborSet v = G.neighborSet v
  证明: rfl

@[simp]

Depends on / 依赖: _union
-/
theorem neighborSet_top (v : V) : (⊤ : G.Subgraph).neighborSet v = G.neighborSet v := rfl

@[simp]
/--
theorem `neighborSet_bot` / 定理 `neighborSet_bot`

English:
theorem neighborSet_bot
  given: (v : V)
  statement: (⊥ : G.Subgraph).neighborSet v = ∅
  proof: rfl

@[simp]

中文:
定理 neighborSet_bot
  条件: (v : V)
  结论: (⊥ : G.Subgraph).neighborSet v = ∅
  证明: rfl

@[simp]

Depends on / 依赖: _union
-/
theorem neighborSet_bot (v : V) : (⊥ : G.Subgraph).neighborSet v = ∅ := rfl

@[simp]
/--
theorem `neighborSet_sSup` / 定理 `neighborSet_sSup`

English:
theorem neighborSet_sSup
  given: (s : Set G.Subgraph) (v : V)
  proof: by
  ext
  simp

@[simp]

中文:
定理 neighborSet_sSup
  条件: (s : Set G.Subgraph) (v : V)
  证明: by
  ext
  simp

@[simp]
-/
theorem neighborSet_sSup (s : Set G.Subgraph) (v : V) :
    (sSup s).neighborSet v = ⋃ G' in s, neighborSet G' v := by
  ext
  simp

@[simp]
/--
theorem `neighborSet_sInf` / 定理 `neighborSet_sInf`

English:
theorem neighborSet_sInf
  given: (s : Set G.Subgraph) (v : V)
  proof: by
  ext
  simp

@[simp]

中文:
定理 neighborSet_sInf
  条件: (s : Set G.Subgraph) (v : V)
  证明: by
  ext
  simp

@[simp]
-/
theorem neighborSet_sInf (s : Set G.Subgraph) (v : V) :
    (sInf s).neighborSet v = (⋂ G' in s, neighborSet G' v) inter G.neighborSet v := by
  ext
  simp

@[simp]
/--
theorem `neighborSet_iSup` / 定理 `neighborSet_iSup`

English:
theorem neighborSet_iSup
  given: (f : ι -> G.Subgraph) (v : V)
  proof: by simp [iSup]

@[simp]

中文:
定理 neighborSet_iSup
  条件: (f : ι -> G.Subgraph) (v : V)
  证明: by simp [iSup]

@[simp]
-/
theorem neighborSet_iSup (f : ι -> G.Subgraph) (v : V) :
    (⨆ i, f i).neighborSet v = ⋃ i, (f i).neighborSet v := by simp [iSup]

@[simp]
/--
theorem `neighborSet_iInf` / 定理 `neighborSet_iInf`

English:
theorem neighborSet_iInf
  given: (f : ι -> G.Subgraph) (v : V)
  proof: by simp [iInf]

@[simp]

中文:
定理 neighborSet_iInf
  条件: (f : ι -> G.Subgraph) (v : V)
  证明: by simp [iInf]

@[simp]
-/
theorem neighborSet_iInf (f : ι -> G.Subgraph) (v : V) :
    (⨅ i, f i).neighborSet v = (⋂ i, (f i).neighborSet v) inter G.neighborSet v := by simp [iInf]

@[simp]
/--
theorem `edgeSet_top` / 定理 `edgeSet_top`

English:
theorem edgeSet_top
  statement: (⊤ : Subgraph G).edgeSet = G.edgeSet
  proof: rfl

@[simp]

中文:
定理 edgeSet_top
  结论: (⊤ : Subgraph G).edgeSet = G.edgeSet
  证明: rfl

@[simp]
-/
theorem edgeSet_top : (⊤ : Subgraph G).edgeSet = G.edgeSet := rfl

@[simp]
/--
theorem `edgeSet_bot` / 定理 `edgeSet_bot`

English:
theorem edgeSet_bot
  statement: (⊥ : Subgraph G).edgeSet = ∅
  proof: Set.ext Sym2.ind (by simp)

@[simp]

中文:
定理 edgeSet_bot
  结论: (⊥ : Subgraph G).edgeSet = ∅
  证明: Set.ext Sym2.ind (by simp)

@[simp]

Depends on / 依赖: Set.ext, Sym2.ind
-/
theorem edgeSet_bot : (⊥ : Subgraph G).edgeSet = ∅ :=
Set.ext Sym2.ind (by simp)

@[simp]
/--
theorem `edgeSet_inf` / 定理 `edgeSet_inf`

English:
theorem edgeSet_inf
  given: {H₁ H₂ : Subgraph G}
  statement: (H₁ ⊓ H₂).edgeSet = H₁.edgeSet inter H₂.edgeSet
  proof: Set.ext Sym2.ind (by simp)

@[simp]

中文:
定理 edgeSet_inf
  条件: {H₁ H₂ : Subgraph G}
  结论: (H₁ ⊓ H₂).edgeSet = H₁.edgeSet inter H₂.edgeSet
  证明: Set.ext Sym2.ind (by simp)

@[simp]

Depends on / 依赖: Set.ext, Sym2.ind
-/
theorem edgeSet_inf {H₁ H₂ : Subgraph G} : (H₁ ⊓ H₂).edgeSet = H₁.edgeSet inter H₂.edgeSet :=
Set.ext Sym2.ind (by simp)

@[simp]
/--
theorem `edgeSet_sup` / 定理 `edgeSet_sup`

English:
theorem edgeSet_sup
  given: {H₁ H₂ : Subgraph G}
  statement: (H₁ ⊔ H₂).edgeSet = H₁.edgeSet union H₂.edgeSet
  proof: Set.ext Sym2.ind (by simp)

@[simp]

中文:
定理 edgeSet_sup
  条件: {H₁ H₂ : Subgraph G}
  结论: (H₁ ⊔ H₂).edgeSet = H₁.edgeSet union H₂.edgeSet
  证明: Set.ext Sym2.ind (by simp)

@[simp]

Depends on / 依赖: Set.ext, Sym2.ind
-/
theorem edgeSet_sup {H₁ H₂ : Subgraph G} : (H₁ ⊔ H₂).edgeSet = H₁.edgeSet union H₂.edgeSet :=
Set.ext Sym2.ind (by simp)

@[simp]
/--
theorem `edgeSet_sSup` / 定理 `edgeSet_sSup`

English:
theorem edgeSet_sSup
  given: (s : Set G.Subgraph)
  statement: (sSup s).edgeSet = ⋃ G' in s, edgeSet G'
  proof: by
  ext e
  induction e
  simp

@[simp]

中文:
定理 edgeSet_sSup
  条件: (s : Set G.Subgraph)
  结论: (sSup s).edgeSet = ⋃ G' in s, edgeSet G'
  证明: by
  ext e
  induction e
  simp

@[simp]

Depends on / 依赖: _mem, le_max, s.max
-/
theorem edgeSet_sSup (s : Set G.Subgraph) : (sSup s).edgeSet = ⋃ G' in s, edgeSet G' := by
  ext e
  induction e
  simp

@[simp]
/--
theorem `edgeSet_sInf` / 定理 `edgeSet_sInf`

English:
theorem edgeSet_sInf
  given: (s : Set G.Subgraph)
  proof: by
  ext e
  induction e
  simp

@[simp]

中文:
定理 edgeSet_sInf
  条件: (s : Set G.Subgraph)
  证明: by
  ext e
  induction e
  simp

@[simp]

Depends on / 依赖: _mem, s.min
-/
theorem edgeSet_sInf (s : Set G.Subgraph) :
    (sInf s).edgeSet = (⋂ G' in s, edgeSet G') inter G.edgeSet := by
  ext e
  induction e
  simp

@[simp]
/--
theorem `edgeSet_iSup` / 定理 `edgeSet_iSup`

English:
theorem edgeSet_iSup
  given: (f : ι -> G.Subgraph)
  proof: by simp [iSup]

@[simp]

中文:
定理 edgeSet_iSup
  条件: (f : ι -> G.Subgraph)
  证明: by simp [iSup]

@[simp]
-/
theorem edgeSet_iSup (f : ι -> G.Subgraph) :
    (⨆ i, f i).edgeSet = ⋃ i, (f i).edgeSet := by simp [iSup]

@[simp]
/--
theorem `edgeSet_iInf` / 定理 `edgeSet_iInf`

English:
theorem edgeSet_iInf
  given: (f : ι -> G.Subgraph)
  proof: by
  simp [iInf]

@[simp]

中文:
定理 edgeSet_iInf
  条件: (f : ι -> G.Subgraph)
  证明: by
  simp [iInf]

@[simp]
-/
theorem edgeSet_iInf (f : ι -> G.Subgraph) :
    (⨅ i, f i).edgeSet = (⋂ i, (f i).edgeSet) inter G.edgeSet := by
  simp [iInf]

@[simp]
/--
theorem `spanningCoe_top` / 定理 `spanningCoe_top`

English:
theorem spanningCoe_top
  statement: (⊤ : Subgraph G).spanningCoe = G
  proof: rfl

@[simp]

中文:
定理 spanningCoe_top
  结论: (⊤ : Subgraph G).spanningCoe = G
  证明: rfl

@[simp]
-/
theorem spanningCoe_top : (⊤ : Subgraph G).spanningCoe = G := rfl

@[simp]
/--
theorem `spanningCoe_bot` / 定理 `spanningCoe_bot`

English:
theorem spanningCoe_bot
  statement: (⊥ : Subgraph G).spanningCoe = ⊥
  proof: rfl

中文:
定理 spanningCoe_bot
  结论: (⊥ : Subgraph G).spanningCoe = ⊥
  证明: rfl

Depends on / 依赖: _of_mem_erase_max, lt_max
-/
theorem spanningCoe_bot : (⊥ : Subgraph G).spanningCoe = ⊥ := rfl

/-- Turn a subgraph of a `SimpleGraph` into a member of its subgraph type. -/
@[simps]
/--
Definition of `_root_.SimpleGraph.toSubgraph` / `_root_.SimpleGraph.toSubgraph` 的定义

English:
definition _root_.SimpleGraph.toSubgraph
  signature: (H : SimpleGraph V) (h : H <= G)
  body: Set.univ
  Adj := H.Adj
  adj_sub e := h e
  edge_vert _ := Set.mem_univ _
  symm := H.symm

中文:
定义 _root_.SimpleGraph.toSubgraph
  签名: (H : SimpleGraph V) (h : H <= G)
  定义体: Set.univ
  Adj := H.Adj
  adj_sub e := h e
  edge_vert _ := Set.mem_univ _
  symm := H.symm

Depends on / 依赖: Set.univ, _comp, _eq_sup, _image, apply_sup, hf.map_max, map_max
-/
def _root_.SimpleGraph.toSubgraph (H : SimpleGraph V) (h : H <= G) : G.Subgraph where
  verts := Set.univ
  Adj := H.Adj
  adj_sub e := h e
  edge_vert _ := Set.mem_univ _
  symm := H.symm

/--
theorem `support_mono` / 定理 `support_mono`

English:
theorem support_mono
  given: {H H' : Subgraph G} (h : H <= H')
  statement: H.support subseteq H'.support
  proof: SetRel.dom_mono fun _ hvw => h.2 hvw

中文:
定理 support_mono
  条件: {H H' : Subgraph G} (h : H <= H')
  结论: H.support subseteq H'.support
  证明: SetRel.dom_mono fun _ hvw => h.2 hvw

Depends on / 依赖: SetRel, SetRel.dom_mono, dom_mono
-/
theorem support_mono {H H' : Subgraph G} (h : H <= H') : H.support subseteq H'.support :=
  SetRel.dom_mono fun _ hvw => h.2 hvw

/--
theorem `_root_.SimpleGraph.toSubgraph.isSpanning` / 定理 `_root_.SimpleGraph.toSubgraph.isSpanning`

English:
theorem _root_.SimpleGraph.toSubgraph.isSpanning
  given: (H : SimpleGraph V) (h : H <= G)
  proof: Set.mem_univ

中文:
定理 _root_.SimpleGraph.toSubgraph.isSpanning
  条件: (H : SimpleGraph V) (h : H <= G)
  证明: Set.mem_univ

Depends on / 依赖: Set.mem_univ, _comp, _eq_inf, _image, apply_inf, hf.map_min, map_min, mem_univ
-/
theorem _root_.SimpleGraph.toSubgraph.isSpanning (H : SimpleGraph V) (h : H <= G) :
    (toSubgraph H h).IsSpanning :=
  Set.mem_univ

/--
theorem `spanningCoe_le_of_le` / 定理 `spanningCoe_le_of_le`

English:
theorem spanningCoe_le_of_le
  given: {H H' : Subgraph G} (h : H <= H')
  statement: H.spanningCoe <= H'.spanningCoe
  proof: h.2

@[simp]

中文:
定理 spanningCoe_le_of_le
  条件: {H H' : Subgraph G} (h : H <= H')
  结论: H.spanningCoe <= H'.spanningCoe
  证明: h.2

@[simp]
-/
theorem spanningCoe_le_of_le {H H' : Subgraph G} (h : H <= H') : H.spanningCoe <= H'.spanningCoe :=
  h.2

@[simp]
/--
lemma `sup_spanningCoe` / 引理 `sup_spanningCoe`

English:
lemma sup_spanningCoe
  given: (H H' : Subgraph G)
  proof: rfl

中文:
引理 sup_spanningCoe
  条件: (H H' : Subgraph G)
  证明: rfl
-/
lemma sup_spanningCoe (H H' : Subgraph G) :
    (H ⊔ H').spanningCoe = H.spanningCoe ⊔ H'.spanningCoe := rfl

/--
Definition of `botIso` / `botIso` 的定义

English:
definition botIso
  signature: : (⊥ : Subgraph G).coe ≃g emptyGraph Empty where
  body: v.property.elim
  invFun v := v.elim
  left_inv := fun ⟨_, h⟩ => h.elim
  right_inv v := v.elim
  map_rel_iff' := Iff.rfl

中文:
定义 botIso
  签名: : (⊥ : Subgraph G).coe ≃g emptyGraph Empty where
  定义体: v.property.elim
  invFun v := v.elim
  left_inv := fun ⟨_, h⟩ => h.elim
  right_inv v := v.elim
  map_rel_iff' := Iff.rfl

Depends on / 依赖: property, v.property.elim
-/
def botIso : (⊥ : Subgraph G).coe ≃g emptyGraph Empty where
  toFun v := v.property.elim
  invFun v := v.elim
  left_inv := fun ⟨_, h⟩ => h.elim
  right_inv v := v.elim
  map_rel_iff' := Iff.rfl

/--
theorem `edgeSet_mono` / 定理 `edgeSet_mono`

English:
theorem edgeSet_mono
  given: {H₁ H₂ : Subgraph G} (h : H₁ <= H₂)
  statement: H₁.edgeSet <= H₂.edgeSet
  proof: Sym2.ind h.2

中文:
定理 edgeSet_mono
  条件: {H₁ H₂ : Subgraph G} (h : H₁ <= H₂)
  结论: H₁.edgeSet <= H₂.edgeSet
  证明: Sym2.ind h.2

Depends on / 依赖: Sym2.ind
-/
theorem edgeSet_mono {H₁ H₂ : Subgraph G} (h : H₁ <= H₂) : H₁.edgeSet <= H₂.edgeSet :=
  Sym2.ind h.2

/--
theorem `edgeSet_monotone` / 定理 `edgeSet_monotone`

English:
theorem edgeSet_monotone
  statement: Monotone (edgeSet (G := G))
  proof: fun _ _ => edgeSet_mono

中文:
定理 edgeSet_monotone
  结论: Monotone (edgeSet (G := G))
  证明: fun _ _ => edgeSet_mono
-/
theorem edgeSet_monotone : Monotone (edgeSet (G := G)) :=
  fun _ _ => edgeSet_mono

/--
theorem `_root_.Disjoint.edgeSet` / 定理 `_root_.Disjoint.edgeSet`

English:
theorem _root_.Disjoint.edgeSet
  given: {H₁ H₂ : Subgraph G} (h : Disjoint H₁ H₂)
  proof: disjoint_iff_inf_le.mpr by simpa using edgeSet_mono h.le_bot

@[simp]

中文:
定理 _root_.Disjoint.edgeSet
  条件: {H₁ H₂ : Subgraph G} (h : Disjoint H₁ H₂)
  证明: disjoint_iff_inf_le.mpr by simpa using edgeSet_mono h.le_bot

@[simp]

Depends on / 依赖: disjoint_iff_inf_le, disjoint_iff_inf_le.mpr, edgeSet_mono, h.le_bot, le_bot
-/
theorem _root_.Disjoint.edgeSet {H₁ H₂ : Subgraph G} (h : Disjoint H₁ H₂) :
    Disjoint H₁.edgeSet H₂.edgeSet :=
disjoint_iff_inf_le.mpr by simpa using edgeSet_mono h.le_bot

@[simp]
/--
lemma `disjoint_verts_iff_disjoint` / 引理 `disjoint_verts_iff_disjoint`

English:
lemma disjoint_verts_iff_disjoint
  given: {H H' : Subgraph G}
  proof: by
  constructor
  · rintro hdisj M' ⟨hsub₀, _⟩ ⟨hsub₁, _⟩
    rw [le_bot_iff]
    ext
    · grind [verts_bot]
    · exact ⟨(hdisj hsub₀ hsub₁ <| M'.edge_vert · :), False.elim⟩
  · intro hdisj S h₀ h₁ v hvS
    let M' : Subgraph G := { verts := {v}, Adj := ⊥, adj_sub := by simp, edge_vert := by simp

中文:
引理 disjoint_verts_iff_disjoint
  条件: {H H' : Subgraph G}
  证明: by
  constructor
  · rintro hdisj M' ⟨hsub₀, _⟩ ⟨hsub₁, _⟩
    rw [le_bot_iff]
    ext
    · grind [verts_bot]
    · exact ⟨(hdisj hsub₀ hsub₁ <| M'.edge_vert · :), False.elim⟩
  · intro hdisj S h₀ h₁ v hvS
    let M' : Subgraph G := { verts := {v}, Adj := ⊥, adj_sub := by simp, edge_vert := by simp

Depends on / 依赖: False.elim, M.verts, Set.mem_singleton, Subgraph, adj_sub, edge_vert, le_bot_iff, mem_singleton, verts_bot
-/
lemma disjoint_verts_iff_disjoint {H H' : Subgraph G} :
    Disjoint H.verts H'.verts ↔ Disjoint H H' := by
  constructor
  · rintro hdisj M' ⟨hsub₀, _⟩ ⟨hsub₁, _⟩
    rw [le_bot_iff]
    ext
    · grind [verts_bot]
    · exact ⟨(hdisj hsub₀ hsub₁ <| M'.edge_vert · :), False.elim⟩
  · intro hdisj S h₀ h₁ v hvS
    let M' : Subgraph G := { verts := {v}, Adj := ⊥, adj_sub := by simp, edge_vert := by simp }
    have hle {M : Subgraph G} (h : v in M.verts) : M' <= M := by constructor <;> simp [h, M']
.left Set.mem_singleton v exact hdisj (hle <| h₀ hvS) (hle <| h₁ hvS)

section map
variable {G' : SimpleGraph W} {f : G ->g G'}

/-- Graph homomorphisms induce a covariant function on subgraphs. -/
@[simps]
/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: (f : G ->g G') (H : G.Subgraph)
  body: f '' H.verts
  Adj := Relation.Map H.Adj f f
  adj_sub := by
    rintro _ _ ⟨u, v, h, rfl, rfl⟩
    exact f.map_rel (H.adj_sub h)
  edge_vert := by
    rintro _ _ ⟨u, v, h, rfl, rfl⟩
    exact Set.mem_image_of_mem _ (H.edge_vert h)
  symm.symm := by
    rintro _ _ ⟨u, v, h, rfl, rfl⟩
    exact ⟨v, u

中文:
定义 map
  签名: (f : G ->g G') (H : G.Subgraph)
  定义体: f '' H.verts
  Adj := Relation.Map H.Adj f f
  adj_sub := by
    rintro _ _ ⟨u, v, h, rfl, rfl⟩
    exact f.map_rel (H.adj_sub h)
  edge_vert := by
    rintro _ _ ⟨u, v, h, rfl, rfl⟩
    exact Set.mem_image_of_mem _ (H.edge_vert h)
  symm.symm := by
    rintro _ _ ⟨u, v, h, rfl, rfl⟩
    exact ⟨v, u

Depends on / 依赖: _mem, ne_of_mem_erase
-/
protected def map (f : G ->g G') (H : G.Subgraph) : G'.Subgraph where
  verts := f '' H.verts
  Adj := Relation.Map H.Adj f f
  adj_sub := by
    rintro _ _ ⟨u, v, h, rfl, rfl⟩
    exact f.map_rel (H.adj_sub h)
  edge_vert := by
    rintro _ _ ⟨u, v, h, rfl, rfl⟩
    exact Set.mem_image_of_mem _ (H.edge_vert h)
  symm.symm := by
    rintro _ _ ⟨u, v, h, rfl, rfl⟩
    exact ⟨v, u, h.symm, rfl, rfl⟩

/--
lemma `map_id` / 引理 `map_id`

English:
lemma map_id
  given: (H : G.Subgraph)
  statement: H.map Hom.id = H
  proof: by ext <;> simp

中文:
引理 map_id
  条件: (H : G.Subgraph)
  结论: H.map Hom.id = H
  证明: by ext <;> simp

Depends on / 依赖: _mem, ne_of_mem_erase
-/
@[simp] lemma map_id (H : G.Subgraph) : H.map Hom.id = H := by ext <;> simp

/--
lemma `map_comp` / 引理 `map_comp`

English:
lemma map_comp
  given: {U : Type*} {G'' : SimpleGraph U} (H : G.Subgraph) (f : G ->g G') (g : G' ->g G'')
  proof: by ext <;> simp [Subgraph.map]

中文:
引理 map_comp
  条件: {U : 类型} {G'' : SimpleGraph U} (H : G.Subgraph) (f : G ->g G') (g : G' ->g G'')
  证明: by ext <;> simp [Subgraph.map]

Depends on / 依赖: Subgraph, Subgraph.map
-/
lemma map_comp {U : Type*} {G'' : SimpleGraph U} (H : G.Subgraph) (f : G ->g G') (g : G' ->g G'') :
    H.map (g.comp f) = (H.map f).map g := by ext <;> simp [Subgraph.map]

/--
lemma `map_mono` / 引理 `map_mono`

English:
lemma map_mono
  given: {H₁ H₂ : G.Subgraph} (hH : H₁ <= H₂)
  statement: H₁.map f <= H₂.map f
  proof: by
  constructor
  · intro
    simp only [map_verts, Set.mem_image, forall_exists_index, and_imp]
    rintro v hv rfl
    exact ⟨_, hH.1 hv, rfl⟩
  · rintro _ _ ⟨u, v, ha, rfl, rfl⟩
    exact ⟨_, _, hH.2 ha, rfl, rfl⟩

中文:
引理 map_mono
  条件: {H₁ H₂ : G.Subgraph} (hH : H₁ <= H₂)
  结论: H₁.map f <= H₂.map f
  证明: by
  constructor
  · intro
    simp only [map_verts, Set.mem_image, forall_exists_index, and_imp]
    rintro v hv rfl
    exact ⟨_, hH.1 hv, rfl⟩
  · rintro _ _ ⟨u, v, ha, rfl, rfl⟩
    exact ⟨_, _, hH.2 ha, rfl, rfl⟩
-/
@[gcongr] lemma map_mono {H₁ H₂ : G.Subgraph} (hH : H₁ <= H₂) : H₁.map f <= H₂.map f := by
  constructor
  · intro
    simp only [map_verts, Set.mem_image, forall_exists_index, and_imp]
    rintro v hv rfl
    exact ⟨_, hH.1 hv, rfl⟩
  · rintro _ _ ⟨u, v, ha, rfl, rfl⟩
    exact ⟨_, _, hH.2 ha, rfl, rfl⟩

/--
lemma `map_monotone` / 引理 `map_monotone`

English:
lemma map_monotone
  statement: Monotone (Subgraph.map f)
  proof: fun _ _ => map_mono

中文:
引理 map_monotone
  结论: Monotone (Subgraph.map f)
  证明: fun _ _ => map_mono

Depends on / 依赖: map_mono
-/
lemma map_monotone : Monotone (Subgraph.map f) := fun _ _ => map_mono

/--
theorem `map_sup` / 定理 `map_sup`

English:
theorem map_sup
  given: (f : G ->g G') (H₁ H₂ : G.Subgraph)
  statement: (H₁ ⊔ H₂).map f = H₁.map f ⊔ H₂.map f
  proof: by
  ext <;> simp [Set.image_union, map_adj, sup_adj, Relation.Map, or_and_right, exists_or]

中文:
定理 map_sup
  条件: (f : G ->g G') (H₁ H₂ : G.Subgraph)
  结论: (H₁ ⊔ H₂).map f = H₁.map f ⊔ H₂.map f
  证明: by
  ext <;> simp [Set.image_union, map_adj, sup_adj, Relation.Map, or_and_right, exists_or]

Depends on / 依赖: Relation, Relation.Map, Set.image_union, exists_or, image_union, map_adj, or_and_right, sup_adj
-/
theorem map_sup (f : G ->g G') (H₁ H₂ : G.Subgraph) : (H₁ ⊔ H₂).map f = H₁.map f ⊔ H₂.map f := by
  ext <;> simp [Set.image_union, map_adj, sup_adj, Relation.Map, or_and_right, exists_or]

/--
lemma `map_iso_top` / 引理 `map_iso_top`

English:
lemma map_iso_top
  given: {H : SimpleGraph W} (e : G ≃g H)
  statement: Subgraph.map e.toHom ⊤ = ⊤
  proof: by
  ext <;> simp [Relation.Map, ← e.eq_symm_apply, ← e.map_rel_iff]

中文:
引理 map_iso_top
  条件: {H : SimpleGraph W} (e : G ≃g H)
  结论: Subgraph.map e.toHom ⊤ = ⊤
  证明: by
  ext <;> simp [Relation.Map, ← e.eq_symm_apply, ← e.map_rel_iff]
-/
@[simp] lemma map_iso_top {H : SimpleGraph W} (e : G ≃g H) : Subgraph.map e.toHom ⊤ = ⊤ := by
  ext <;> simp [Relation.Map, ← e.eq_symm_apply, ← e.map_rel_iff]

/--
lemma `edgeSet_map` / 引理 `edgeSet_map`

English:
lemma edgeSet_map
  given: (f : G ->g G') (H : G.Subgraph)
  proof: Sym2.fromRel_relationMap ..

中文:
引理 edgeSet_map
  条件: (f : G ->g G') (H : G.Subgraph)
  证明: Sym2.fromRel_relationMap ..
-/
@[simp] lemma edgeSet_map (f : G ->g G') (H : G.Subgraph) :
    (H.map f).edgeSet = Sym2.map f '' H.edgeSet := Sym2.fromRel_relationMap ..

end map

/-- Graph homomorphisms induce a contravariant function on subgraphs. -/
@[simps]
/--
Definition of `comap` / `comap` 的定义

English:
definition comap
  signature: {G' : SimpleGraph W} (f : G ->g G') (H : G'.Subgraph)
  body: f ⁻¹' H.verts
  Adj u v := G.Adj u v ∧ H.Adj (f u) (f v)
  adj_sub h := h.1
  edge_vert h := Set.mem_preimage.1 (H.edge_vert h.2)
  symm.symm _ _ h := ⟨h.left.symm, h.right.symm⟩

中文:
定义 comap
  签名: {G' : SimpleGraph W} (f : G ->g G') (H : G'.Subgraph)
  定义体: f ⁻¹' H.verts
  Adj u v := G.Adj u v ∧ H.Adj (f u) (f v)
  adj_sub h := h.1
  edge_vert h := Set.mem_preimage.1 (H.edge_vert h.2)
  symm.symm _ _ h := ⟨h.left.symm, h.right.symm⟩
-/
protected def comap {G' : SimpleGraph W} (f : G ->g G') (H : G'.Subgraph) : G.Subgraph where
  verts := f ⁻¹' H.verts
  Adj u v := G.Adj u v ∧ H.Adj (f u) (f v)
  adj_sub h := h.1
  edge_vert h := Set.mem_preimage.1 (H.edge_vert h.2)
  symm.symm _ _ h := ⟨h.left.symm, h.right.symm⟩

/--
theorem `comap_monotone` / 定理 `comap_monotone`

English:
theorem comap_monotone
  given: {G' : SimpleGraph W} (f : G ->g G')
  statement: Monotone (Subgraph.comap f)
  proof: by
  intro H H' h
  constructor
  · intro
    simp only [comap_verts, Set.mem_preimage]
    apply h.1
  · intro v w
    simp +contextual only [comap_adj, and_imp, true_and]
    intro
    apply h.2

中文:
定理 comap_monotone
  条件: {G' : SimpleGraph W} (f : G ->g G')
  结论: Monotone (Subgraph.comap f)
  证明: by
  intro H H' h
  constructor
  · intro
    simp only [comap_verts, Set.mem_preimage]
    apply h.1
  · intro v w
    simp +contextual only [comap_adj, and_imp, true_and]
    intro
    apply h.2

Depends on / 依赖: Set.mem_preimage, and_imp, comap_adj, comap_verts, contextual, mem_preimage, true_and
-/
theorem comap_monotone {G' : SimpleGraph W} (f : G ->g G') : Monotone (Subgraph.comap f) := by
  intro H H' h
  constructor
  · intro
    simp only [comap_verts, Set.mem_preimage]
    apply h.1
  · intro v w
    simp +contextual only [comap_adj, and_imp, true_and]
    intro
    apply h.2

/--
lemma `comap_equiv_top` / 引理 `comap_equiv_top`

English:
lemma comap_equiv_top
  given: {H : SimpleGraph W} (f : G ->g H)
  statement: Subgraph.comap f ⊤ = ⊤
  proof: by
  ext <;> simp +contextual [f.map_adj]

中文:
引理 comap_equiv_top
  条件: {H : SimpleGraph W} (f : G ->g H)
  结论: Subgraph.comap f ⊤ = ⊤
  证明: by
  ext <;> simp +contextual [f.map_adj]
-/
@[simp] lemma comap_equiv_top {H : SimpleGraph W} (f : G ->g H) : Subgraph.comap f ⊤ = ⊤ := by
  ext <;> simp +contextual [f.map_adj]

/--
theorem `map_le_iff_le_comap` / 定理 `map_le_iff_le_comap`

English:
theorem map_le_iff_le_comap
  given: {G' : SimpleGraph W} (f : G ->g G') (H : G.Subgraph) (H' : G'.Subgraph)
  proof: by
  refine ⟨fun h => ⟨fun v hv => ?_, fun v w hvw => ?_⟩, fun h => ⟨fun v => ?_, fun v w => ?_⟩⟩
  · simp only [comap_verts, Set.mem_preimage]
    exact h.1 ⟨v, hv, rfl⟩
  · simp only [H.adj_sub hvw, comap_adj, true_and]
    exact h.2 ⟨v, w, hvw, rfl, rfl⟩
  · simp only [map_verts, Set.mem_image, f

中文:
定理 map_le_iff_le_comap
  条件: {G' : SimpleGraph W} (f : G ->g G') (H : G.Subgraph) (H' : G'.Subgraph)
  证明: by
  refine ⟨fun h => ⟨fun v hv => ?_, fun v w hvw => ?_⟩, fun h => ⟨fun v => ?_, fun v w => ?_⟩⟩
  · simp only [comap_verts, Set.mem_preimage]
    exact h.1 ⟨v, hv, rfl⟩
  · simp only [H.adj_sub hvw, comap_adj, true_and]
    exact h.2 ⟨v, w, hvw, rfl, rfl⟩
  · simp only [map_verts, Set.mem_image, f

Depends on / 依赖: H.adj_sub, Relation, Relation.Map, Set.mem_image, Set.mem_preimage, adj_sub, and_imp, comap_adj, comap_verts, forall_exists_index, map_adj, map_verts, mem_image, mem_preimage, true_and
-/
theorem map_le_iff_le_comap {G' : SimpleGraph W} (f : G ->g G') (H : G.Subgraph) (H' : G'.Subgraph) :
    H.map f <= H' ↔ H <= H'.comap f := by
  refine ⟨fun h => ⟨fun v hv => ?_, fun v w hvw => ?_⟩, fun h => ⟨fun v => ?_, fun v w => ?_⟩⟩
  · simp only [comap_verts, Set.mem_preimage]
    exact h.1 ⟨v, hv, rfl⟩
  · simp only [H.adj_sub hvw, comap_adj, true_and]
    exact h.2 ⟨v, w, hvw, rfl, rfl⟩
  · simp only [map_verts, Set.mem_image, forall_exists_index, and_imp]
    rintro w hw rfl
    exact h.1 hw
  · simp only [Relation.Map, map_adj, forall_exists_index, and_imp]
    rintro u u' hu rfl rfl
    exact (h.2 hu).2

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [DecidableEq
  signature: V] [Fintype V] [DecidableRel G.Adj] : Fintype G.Subgraph
  body: by
  refine .ofBijective
    (α := {H : Finset V × (V -> V -> Bool) //
      (forall a b, H.2 a b -> G.Adj a b) ∧ (forall a b, H.2 a b -> a in H.1) ∧ forall a b, H.2 a b = H.2 b a})
    (fun H => ⟨H.1.1, fun a b => H.1.2 a b, @H.2.1, @H.2.2.1, by simp [symm_def, H.2.2.2]⟩)
    ⟨?_, fun H => ?_⟩
  · 

中文:
实例 [DecidableEq
  签名: V] [Fintype V] [DecidableRel G.Adj] : Fintype G.Subgraph
  定义体: by
  refine .ofBijective
    (α := {H : Finset V × (V -> V -> Bool) //
      (forall a b, H.2 a b -> G.Adj a b) ∧ (forall a b, H.2 a b -> a in H.1) ∧ forall a b, H.2 a b = H.2 b a})
    (fun H => ⟨H.1.1, fun a b => H.1.2 a b, @H.2.1, @H.2.2.1, by simp [symm_def, H.2.2.2]⟩)
    ⟨?_, fun H => ?_⟩
  · 

Depends on / 依赖: Finset, G.Adj, H.Adj, H.adj_comm, H.adj_sub, H.edge_vert, H.verts.toFinset, adj_comm, adj_sub, classical, edge_vert, funext_iff, ofBijective, symm_def, toFinset
-/
instance [DecidableEq V] [Fintype V] [DecidableRel G.Adj] : Fintype G.Subgraph := by
  refine .ofBijective
    (α := {H : Finset V × (V -> V -> Bool) //
      (forall a b, H.2 a b -> G.Adj a b) ∧ (forall a b, H.2 a b -> a in H.1) ∧ forall a b, H.2 a b = H.2 b a})
    (fun H => ⟨H.1.1, fun a b => H.1.2 a b, @H.2.1, @H.2.2.1, by simp [symm_def, H.2.2.2]⟩)
    ⟨?_, fun H => ?_⟩
  · rintro ⟨⟨_, _⟩, -⟩ ⟨⟨_, _⟩, -⟩
    simp [funext_iff]
  · classical
    exact ⟨⟨(H.verts.toFinset, fun a b => H.Adj a b), fun a b => by simpa using H.adj_sub,
      fun a b => by simpa using H.edge_vert, by simp [H.adj_comm]⟩, by simp⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Finite
  signature: V] : Finite G.Subgraph
  body: by classical cases nonempty_fintype V; infer_instance

中文:
实例 [Finite
  签名: V] : Finite G.Subgraph
  定义体: by classical cases nonempty_fintype V; infer_instance

Depends on / 依赖: classical, infer_instance, nonempty_fintype
-/
instance [Finite V] : Finite G.Subgraph := by classical cases nonempty_fintype V; infer_instance

/-- Given two subgraphs, one a subgraph of the other, there is an induced injective homomorphism of
the subgraphs as graphs. -/
@[simps]
/--
Definition of `inclusion` / `inclusion` 的定义

English:
definition inclusion
  signature: {x y : Subgraph G} (h : x <= y)
  body: ⟨↑v, And.left h v.property⟩
  map_rel' hvw := h.2 hvw

中文:
定义 inclusion
  签名: {x y : Subgraph G} (h : x <= y)
  定义体: ⟨↑v, And.left h v.property⟩
  map_rel' hvw := h.2 hvw

Depends on / 依赖: And.left, property, v.property
-/
def inclusion {x y : Subgraph G} (h : x <= y) : x.coe ->g y.coe where
  toFun v := ⟨↑v, And.left h v.property⟩
  map_rel' hvw := h.2 hvw

/--
theorem `inclusion.injective` / 定理 `inclusion.injective`

English:
theorem inclusion.injective
  given: {x y : Subgraph G} (h : x <= y)
  statement: Function.Injective (inclusion h)
  proof: fun _ _ h => Subtype.ext congr(Subtype.val $h)

中文:
定理 inclusion.injective
  条件: {x y : Subgraph G} (h : x <= y)
  结论: Function.Injective (inclusion h)
  证明: fun _ _ h => Subtype.ext congr(Subtype.val $h)

Depends on / 依赖: Subtype, Subtype.ext, Subtype.val
-/
theorem inclusion.injective {x y : Subgraph G} (h : x <= y) : Function.Injective (inclusion h) :=
  fun _ _ h => Subtype.ext congr(Subtype.val $h)

/-- There is an induced injective homomorphism of a subgraph of `G` into `G`. -/
@[simps]
/--
Definition of `hom` / `hom` 的定义

English:
definition hom
  signature: (x : Subgraph G)
  body: v
  map_rel' := x.adj_sub

中文:
定义 hom
  签名: (x : Subgraph G)
  定义体: v
  map_rel' := x.adj_sub
-/
protected def hom (x : Subgraph G) : x.coe ->g G where
  toFun v := v
  map_rel' := x.adj_sub

/--
lemma `coe_hom` / 引理 `coe_hom`

English:
lemma coe_hom
  given: (x : Subgraph G)
  proof: rfl

中文:
引理 coe_hom
  条件: (x : Subgraph G)
  证明: rfl
-/
@[simp] lemma coe_hom (x : Subgraph G) :
    (x.hom : x.verts -> V) = (fun (v : x.verts) => (v : V)) := rfl

/--
theorem `hom_injective` / 定理 `hom_injective`

English:
theorem hom_injective
  given: {x : Subgraph G}
  statement: Function.Injective x.hom
  proof: fun _ _ => Subtype.ext

中文:
定理 hom_injective
  条件: {x : Subgraph G}
  结论: Function.Injective x.hom
  证明: fun _ _ => Subtype.ext

Depends on / 依赖: Subtype, Subtype.ext
-/
theorem hom_injective {x : Subgraph G} : Function.Injective x.hom :=
  fun _ _ => Subtype.ext

/--
lemma `map_hom_top` / 引理 `map_hom_top`

English:
lemma map_hom_top
  given: (G' : G.Subgraph)
  statement: Subgraph.map G'.hom ⊤ = G'
  proof: by
  aesop (add unfold safe Relation.Map, unsafe G'.edge_vert, unsafe Adj.symm)

中文:
引理 map_hom_top
  条件: (G' : G.Subgraph)
  结论: Subgraph.map G'.hom ⊤ = G'
  证明: by
  aesop (add unfold safe Relation.Map, unsafe G'.edge_vert, unsafe Adj.symm)
-/
@[simp] lemma map_hom_top (G' : G.Subgraph) : Subgraph.map G'.hom ⊤ = G' := by
  aesop (add unfold safe Relation.Map, unsafe G'.edge_vert, unsafe Adj.symm)

/-- There is an induced injective homomorphism of a subgraph of `G` as
a spanning subgraph into `G`. -/
@[simps]
/--
Definition of `spanningHom` / `spanningHom` 的定义

English:
definition spanningHom
  signature: (x : Subgraph G)
  body: id
  map_rel' := x.adj_sub

中文:
定义 spanningHom
  签名: (x : Subgraph G)
  定义体: id
  map_rel' := x.adj_sub
-/
def spanningHom (x : Subgraph G) : x.spanningCoe ->g G where
  toFun := id
  map_rel' := x.adj_sub

/--
theorem `spanningHom_injective` / 定理 `spanningHom_injective`

English:
theorem spanningHom_injective
  given: {x : Subgraph G}
  statement: Function.Injective x.spanningHom
  proof: fun _ _ => id

中文:
定理 spanningHom_injective
  条件: {x : Subgraph G}
  结论: Function.Injective x.spanningHom
  证明: fun _ _ => id
-/
theorem spanningHom_injective {x : Subgraph G} : Function.Injective x.spanningHom :=
  fun _ _ => id

/--
theorem `neighborSet_subset_of_subgraph` / 定理 `neighborSet_subset_of_subgraph`

English:
theorem neighborSet_subset_of_subgraph
  given: {x y : Subgraph G} (h : x <= y) (v : V)
  proof: fun _ h' => h.2 h'

中文:
定理 neighborSet_subset_of_subgraph
  条件: {x y : Subgraph G} (h : x <= y) (v : V)
  证明: fun _ h' => h.2 h'
-/
theorem neighborSet_subset_of_subgraph {x y : Subgraph G} (h : x <= y) (v : V) :
    x.neighborSet v subseteq y.neighborSet v :=
  fun _ h' => h.2 h'

/--
Instance `neighborSet.decidablePred` / 实例 `neighborSet.decidablePred`

English:
instance neighborSet.decidablePred
  signature: (G' : Subgraph G) [h : DecidableRel G'.Adj] (v : V)
  body: h v

中文:
实例 neighborSet.decidablePred
  签名: (G' : Subgraph G) [h : DecidableRel G'.Adj] (v : V)
  定义体: h v
-/
instance neighborSet.decidablePred (G' : Subgraph G) [h : DecidableRel G'.Adj] (v : V) :
    DecidablePred (· in G'.neighborSet v) :=
  h v

/--
Instance `finiteAt` / 实例 `finiteAt`

English:
instance finiteAt
  signature: {G' : Subgraph G} (v : G'.verts) [DecidableRel G'.Adj]
  body: Set.fintypeSubset (G.neighborSet v) (G'.neighborSet_subset v)

中文:
实例 finiteAt
  签名: {G' : Subgraph G} (v : G'.verts) [DecidableRel G'.Adj]
  定义体: Set.fintypeSubset (G.neighborSet v) (G'.neighborSet_subset v)

Depends on / 依赖: G.neighborSet, Set.fintypeSubset, fintypeSubset, neighborSet, neighborSet_subset
-/
instance finiteAt {G' : Subgraph G} (v : G'.verts) [DecidableRel G'.Adj]
    [Fintype (G.neighborSet v)] : Fintype (G'.neighborSet v) :=
  Set.fintypeSubset (G.neighborSet v) (G'.neighborSet_subset v)

/-- If a subgraph is locally finite at a vertex, then so are subgraphs of that subgraph.

This is not an instance because `G''` cannot be inferred. -/
@[instance_reducible]
/--
Definition of `finiteAtOfSubgraph` / `finiteAtOfSubgraph` 的定义

English:
definition finiteAtOfSubgraph
  signature: {G' G'' : Subgraph G} [DecidableRel G'.Adj] (h : G' <= G'') (v : G'.verts)
  body: Set.fintypeSubset (G''.neighborSet v) (neighborSet_subset_of_subgraph h v)

中文:
定义 finiteAtOfSubgraph
  签名: {G' G'' : Subgraph G} [DecidableRel G'.Adj] (h : G' <= G'') (v : G'.verts)
  定义体: Set.fintypeSubset (G''.neighborSet v) (neighborSet_subset_of_subgraph h v)

Depends on / 依赖: Set.fintypeSubset, fintypeSubset, neighborSet, neighborSet_subset_of_subgraph
-/
def finiteAtOfSubgraph {G' G'' : Subgraph G} [DecidableRel G'.Adj] (h : G' <= G'') (v : G'.verts)
    [Fintype (G''.neighborSet v)] : Fintype (G'.neighborSet v) :=
  Set.fintypeSubset (G''.neighborSet v) (neighborSet_subset_of_subgraph h v)

instance (G' : Subgraph G) [Fintype G'.verts] (v : V) [DecidablePred (· in G'.neighborSet v)] :
    Fintype (G'.neighborSet v) :=
  Set.fintypeSubset G'.verts (neighborSet_subset_verts G' v)

/--
Instance `coeFiniteAt` / 实例 `coeFiniteAt`

English:
instance coeFiniteAt
  signature: {G' : Subgraph G} (v : G'.verts) [Fintype (G'.neighborSet v)]
  body: Fintype.ofEquiv _ (coeNeighborSetEquiv v).symm

中文:
实例 coeFiniteAt
  签名: {G' : Subgraph G} (v : G'.verts) [Fintype (G'.neighborSet v)]
  定义体: Fintype.ofEquiv _ (coeNeighborSetEquiv v).symm

Depends on / 依赖: Fintype, Fintype.ofEquiv, coeNeighborSetEquiv, ofEquiv
-/
instance coeFiniteAt {G' : Subgraph G} (v : G'.verts) [Fintype (G'.neighborSet v)] :
    Fintype (G'.coe.neighborSet v) :=
  Fintype.ofEquiv _ (coeNeighborSetEquiv v).symm

/--
theorem `IsSpanning.card_verts` / 定理 `IsSpanning.card_verts`

English:
theorem IsSpanning.card_verts
  given: [Fintype V] {G' : Subgraph G} [Fintype G'.verts] (h : G'.IsSpanning)
  proof: by
  simp only [isSpanning_iff.1 h, Set.toFinset_univ]
  congr

中文:
定理 IsSpanning.card_verts
  条件: [Fintype V] {G' : Subgraph G} [Fintype G'.verts] (h : G'.IsSpanning)
  证明: by
  simp only [isSpanning_iff.1 h, Set.toFinset_univ]
  congr

Depends on / 依赖: Set.toFinset_univ, isSpanning_iff, toFinset_univ
-/
theorem IsSpanning.card_verts [Fintype V] {G' : Subgraph G} [Fintype G'.verts] (h : G'.IsSpanning) :
    G'.verts.toFinset.card = Fintype.card V := by
  simp only [isSpanning_iff.1 h, Set.toFinset_univ]
  congr

/--
Definition of `degree` / `degree` 的定义

English:
definition degree
  signature: (G' : Subgraph G) (v : V) [Fintype (G'.neighborSet v)]
  body: Fintype.card (G'.neighborSet v)

中文:
定义 degree
  签名: (G' : Subgraph G) (v : V) [Fintype (G'.neighborSet v)]
  定义体: Fintype.card (G'.neighborSet v)

Depends on / 依赖: Fintype, Fintype.card, neighborSet
-/
def degree (G' : Subgraph G) (v : V) [Fintype (G'.neighborSet v)] : Nat :=
  Fintype.card (G'.neighborSet v)

/--
theorem `finset_card_neighborSet_eq_degree` / 定理 `finset_card_neighborSet_eq_degree`

English:
theorem finset_card_neighborSet_eq_degree
  given: {G' : Subgraph G} {v : V} [Fintype (G'.neighborSet v)]
  proof: by
  rw [degree]; rw [Set.toFinset_card]

中文:
定理 finset_card_neighborSet_eq_degree
  条件: {G' : Subgraph G} {v : V} [Fintype (G'.neighborSet v)]
  证明: by
  rw [degree]; rw [Set.toFinset_card]

Depends on / 依赖: Set.toFinset_card, degree, toFinset_card
-/
theorem finset_card_neighborSet_eq_degree {G' : Subgraph G} {v : V} [Fintype (G'.neighborSet v)] :
    (G'.neighborSet v).toFinset.card = G'.degree v := by
  rw [degree]; rw [Set.toFinset_card]

/--
theorem `degree_of_notMem_verts` / 定理 `degree_of_notMem_verts`

English:
theorem degree_of_notMem_verts
  statement: {G' : Subgraph G} {v : V} [Fintype (G'.neighborSet v)]
  proof: by
  rw [degree]; rw [Fintype.card_eq_zero_iff]; rw [isEmpty_subtype]
  intro w
  by_contra hw
  exact h hw.fst_mem

中文:
定理 degree_of_notMem_verts
  结论: {G' : Subgraph G} {v : V} [Fintype (G'.neighborSet v)]
  证明: by
  rw [degree]; rw [Fintype.card_eq_zero_iff]; rw [isEmpty_subtype]
  intro w
  by_contra hw
  exact h hw.fst_mem

Depends on / 依赖: Fintype, Fintype.card_eq_zero_iff, card_eq_zero_iff, degree, fst_mem, hw.fst_mem, isEmpty_subtype
-/
theorem degree_of_notMem_verts {G' : Subgraph G} {v : V} [Fintype (G'.neighborSet v)]
    (h : v ∉ G'.verts) : G'.degree v = 0 := by
  rw [degree]; rw [Fintype.card_eq_zero_iff]; rw [isEmpty_subtype]
  intro w
  by_contra hw
  exact h hw.fst_mem

/--
theorem `degree_le` / 定理 `degree_le`

English:
theorem degree_le
  statement: (G' : Subgraph G) (v : V) [Fintype (G'.neighborSet v)]
  proof: by
  rw [← card_neighborSet_eq_degree]
  exact Set.card_le_card (G'.neighborSet_subset v)

中文:
定理 degree_le
  结论: (G' : Subgraph G) (v : V) [Fintype (G'.neighborSet v)]
  证明: by
  rw [← card_neighborSet_eq_degree]
  exact Set.card_le_card (G'.neighborSet_subset v)

Depends on / 依赖: Set.card_le_card, card_le_card, card_neighborSet_eq_degree, neighborSet_subset
-/
theorem degree_le (G' : Subgraph G) (v : V) [Fintype (G'.neighborSet v)]
    [Fintype (G.neighborSet v)] : G'.degree v <= G.degree v := by
  rw [← card_neighborSet_eq_degree]
  exact Set.card_le_card (G'.neighborSet_subset v)

/--
theorem `degree_le'` / 定理 `degree_le'`

English:
theorem degree_le'
  statement: (G' G'' : Subgraph G) (h : G' <= G'') (v : V) [Fintype (G'.neighborSet v)]
  proof: Set.card_le_card (neighborSet_subset_of_subgraph h v)

@[simp]

中文:
定理 degree_le'
  结论: (G' G'' : Subgraph G) (h : G' <= G'') (v : V) [Fintype (G'.neighborSet v)]
  证明: Set.card_le_card (neighborSet_subset_of_subgraph h v)

@[simp]

Depends on / 依赖: Set.card_le_card, card_le_card, neighborSet_subset_of_subgraph
-/
theorem degree_le' (G' G'' : Subgraph G) (h : G' <= G'') (v : V) [Fintype (G'.neighborSet v)]
    [Fintype (G''.neighborSet v)] : G'.degree v <= G''.degree v :=
  Set.card_le_card (neighborSet_subset_of_subgraph h v)

@[simp]
/--
theorem `coe_degree` / 定理 `coe_degree`

English:
theorem coe_degree
  statement: (G' : Subgraph G) (v : G'.verts) [Fintype (G'.coe.neighborSet v)]
  proof: by
  rw [← card_neighborSet_eq_degree]
  exact Fintype.card_congr (coeNeighborSetEquiv v)

@[simp]

中文:
定理 coe_degree
  结论: (G' : Subgraph G) (v : G'.verts) [Fintype (G'.coe.neighborSet v)]
  证明: by
  rw [← card_neighborSet_eq_degree]
  exact Fintype.card_congr (coeNeighborSetEquiv v)

@[simp]

Depends on / 依赖: Fintype, Fintype.card_congr, card_congr, card_neighborSet_eq_degree, coeNeighborSetEquiv
-/
theorem coe_degree (G' : Subgraph G) (v : G'.verts) [Fintype (G'.coe.neighborSet v)]
    [Fintype (G'.neighborSet v)] : G'.coe.degree v = G'.degree v := by
  rw [← card_neighborSet_eq_degree]
  exact Fintype.card_congr (coeNeighborSetEquiv v)

@[simp]
/--
theorem `degree_spanningCoe` / 定理 `degree_spanningCoe`

English:
theorem degree_spanningCoe
  statement: {G' : G.Subgraph} (v : V) [Fintype (G'.neighborSet v)]
  proof: by
  rw [← card_neighborSet_eq_degree]; rw [Subgraph.degree]
  congr!

中文:
定理 degree_spanningCoe
  结论: {G' : G.Subgraph} (v : V) [Fintype (G'.neighborSet v)]
  证明: by
  rw [← card_neighborSet_eq_degree]; rw [Subgraph.degree]
  congr!

Depends on / 依赖: Subgraph, Subgraph.degree, card_neighborSet_eq_degree, degree
-/
theorem degree_spanningCoe {G' : G.Subgraph} (v : V) [Fintype (G'.neighborSet v)]
    [Fintype (G'.spanningCoe.neighborSet v)] : G'.spanningCoe.degree v = G'.degree v := by
  rw [← card_neighborSet_eq_degree]; rw [Subgraph.degree]
  congr!

/--
theorem `degree_pos_iff_exists_adj` / 定理 `degree_pos_iff_exists_adj`

English:
theorem degree_pos_iff_exists_adj
  given: {G' : Subgraph G} {v : V} [Fintype (G'.neighborSet v)]
  proof: by
  simp only [degree, Fintype.card_pos_iff, nonempty_subtype, mem_neighborSet]

中文:
定理 degree_pos_iff_exists_adj
  条件: {G' : Subgraph G} {v : V} [Fintype (G'.neighborSet v)]
  证明: by
  simp only [degree, Fintype.card_pos_iff, nonempty_subtype, mem_neighborSet]

Depends on / 依赖: Fintype, Fintype.card_pos_iff, card_pos_iff, degree, mem_neighborSet, nonempty_subtype
-/
theorem degree_pos_iff_exists_adj {G' : Subgraph G} {v : V} [Fintype (G'.neighborSet v)] :
    0 < G'.degree v ↔ exists w, G'.Adj v w := by
  simp only [degree, Fintype.card_pos_iff, nonempty_subtype, mem_neighborSet]

/--
theorem `degree_eq_zero_of_subsingleton` / 定理 `degree_eq_zero_of_subsingleton`

English:
theorem degree_eq_zero_of_subsingleton
  statement: (G' : Subgraph G) (v : V) [Fintype (G'.neighborSet v)]
  proof: by
  by_cases hv : v in G'.verts
  · rw [← G'.coe_degree ⟨v, hv⟩]
    have := (Set.subsingleton_coe _).mpr hG
    exact G'.coe.degree_eq_zero_of_subsingleton ⟨v, hv⟩
  · exact degree_of_notMem_verts hv

中文:
定理 degree_eq_zero_of_subsingleton
  结论: (G' : Subgraph G) (v : V) [Fintype (G'.neighborSet v)]
  证明: by
  by_cases hv : v in G'.verts
  · rw [← G'.coe_degree ⟨v, hv⟩]
    have := (Set.subsingleton_coe _).mpr hG
    exact G'.coe.degree_eq_zero_of_subsingleton ⟨v, hv⟩
  · exact degree_of_notMem_verts hv

Depends on / 依赖: Set.subsingleton_coe, coe.degree_eq_zero_of_subsingleton, coe_degree, degree_eq_zero_of_subsingleton, degree_of_notMem_verts, subsingleton_coe
-/
theorem degree_eq_zero_of_subsingleton (G' : Subgraph G) (v : V) [Fintype (G'.neighborSet v)]
    (hG : G'.verts.Subsingleton) : G'.degree v = 0 := by
  by_cases hv : v in G'.verts
  · rw [← G'.coe_degree ⟨v, hv⟩]
    have := (Set.subsingleton_coe _).mpr hG
    exact G'.coe.degree_eq_zero_of_subsingleton ⟨v, hv⟩
  · exact degree_of_notMem_verts hv

/--
theorem `degree_eq_one_iff_existsUnique_adj` / 定理 `degree_eq_one_iff_existsUnique_adj`

English:
theorem degree_eq_one_iff_existsUnique_adj
  given: {G' : Subgraph G} {v : V} [Fintype (G'.neighborSet v)]
  proof: by
  rw [← finset_card_neighborSet_eq_degree]; rw [Finset.card_eq_one]; rw [Finset.singleton_iff_unique_mem]
  simp only [Set.mem_toFinset, mem_neighborSet]

中文:
定理 degree_eq_one_iff_existsUnique_adj
  条件: {G' : Subgraph G} {v : V} [Fintype (G'.neighborSet v)]
  证明: by
  rw [← finset_card_neighborSet_eq_degree]; rw [Finset.card_eq_one]; rw [Finset.singleton_iff_unique_mem]
  simp only [Set.mem_toFinset, mem_neighborSet]

Depends on / 依赖: Finset, Finset.card_eq_one, Finset.singleton_iff_unique_mem, Set.mem_toFinset, card_eq_one, finset_card_neighborSet_eq_degree, mem_neighborSet, mem_toFinset, singleton_iff_unique_mem
-/
theorem degree_eq_one_iff_existsUnique_adj {G' : Subgraph G} {v : V} [Fintype (G'.neighborSet v)] :
    G'.degree v = 1 ↔ exists! w : V, G'.Adj v w := by
  rw [← finset_card_neighborSet_eq_degree]; rw [Finset.card_eq_one]; rw [Finset.singleton_iff_unique_mem]
  simp only [Set.mem_toFinset, mem_neighborSet]

/--
theorem `nontrivial_verts_of_degree_ne_zero` / 定理 `nontrivial_verts_of_degree_ne_zero`

English:
theorem nontrivial_verts_of_degree_ne_zero
  statement: {G' : Subgraph G} {v : V} [Fintype (G'.neighborSet v)]
  proof: by
  by_contra
  simp_all [G'.degree_eq_zero_of_subsingleton v]

中文:
定理 nontrivial_verts_of_degree_ne_zero
  结论: {G' : Subgraph G} {v : V} [Fintype (G'.neighborSet v)]
  证明: by
  by_contra
  simp_all [G'.degree_eq_zero_of_subsingleton v]

Depends on / 依赖: degree_eq_zero_of_subsingleton
-/
theorem nontrivial_verts_of_degree_ne_zero {G' : Subgraph G} {v : V} [Fintype (G'.neighborSet v)]
    (h : G'.degree v != 0) : Nontrivial G'.verts := by
  by_contra
  simp_all [G'.degree_eq_zero_of_subsingleton v]

/--
lemma `neighborSet_eq_of_equiv` / 引理 `neighborSet_eq_of_equiv`

English:
lemma neighborSet_eq_of_equiv
  statement: {v : V} {H : Subgraph G}
  proof: by
  lift H.neighborSet v to Finset V using h.set_finite_iff.mp hfin with s hs
  lift G.neighborSet v to Finset V using hfin with t ht
refine congrArg _ Finset.eq_of_subset_of_card_le ?_ (Finset.card_eq_of_equiv h).le
  rw [← Finset.coe_subset]; rw [hs]; rw [ht]
  exact H.neighborSet_subset _

中文:
引理 neighborSet_eq_of_equiv
  结论: {v : V} {H : Subgraph G}
  证明: by
  lift H.neighborSet v to Finset V using h.set_finite_iff.mp hfin with s hs
  lift G.neighborSet v to Finset V using hfin with t ht
refine congrArg _ Finset.eq_of_subset_of_card_le ?_ (Finset.card_eq_of_equiv h).le
  rw [← Finset.coe_subset]; rw [hs]; rw [ht]
  exact H.neighborSet_subset _

Depends on / 依赖: Finset, Finset.card_eq_of_equiv, Finset.coe_subset, Finset.eq_of_subset_of_card_le, G.neighborSet, H.neighborSet, H.neighborSet_subset, card_eq_of_equiv, coe_subset, eq_of_subset_of_card_le, h.set_finite_iff.mp, neighborSet, neighborSet_subset, set_finite_iff
-/
lemma neighborSet_eq_of_equiv {v : V} {H : Subgraph G}
    (h : G.neighborSet v ≃ H.neighborSet v) (hfin : (G.neighborSet v).Finite) :
    H.neighborSet v = G.neighborSet v := by
  lift H.neighborSet v to Finset V using h.set_finite_iff.mp hfin with s hs
  lift G.neighborSet v to Finset V using hfin with t ht
refine congrArg _ Finset.eq_of_subset_of_card_le ?_ (Finset.card_eq_of_equiv h).le
  rw [← Finset.coe_subset]; rw [hs]; rw [ht]
  exact H.neighborSet_subset _

/--
lemma `adj_iff_of_neighborSet_equiv` / 引理 `adj_iff_of_neighborSet_equiv`

English:
lemma adj_iff_of_neighborSet_equiv
  statement: {v : V} {H : Subgraph G}
  proof: Set.ext_iff.mp (neighborSet_eq_of_equiv h hfin) _

中文:
引理 adj_iff_of_neighborSet_equiv
  结论: {v : V} {H : Subgraph G}
  证明: Set.ext_iff.mp (neighborSet_eq_of_equiv h hfin) _

Depends on / 依赖: Set.ext_iff.mp, ext_iff, neighborSet_eq_of_equiv
-/
lemma adj_iff_of_neighborSet_equiv {v : V} {H : Subgraph G}
    (h : G.neighborSet v ≃ H.neighborSet v) (hfin : (G.neighborSet v).Finite) :
    forall {w}, H.Adj v w ↔ G.Adj v w :=
  Set.ext_iff.mp (neighborSet_eq_of_equiv h hfin) _

end Subgraph

/--
theorem `card_neighborSet_toSubgraph` / 定理 `card_neighborSet_toSubgraph`

English:
theorem card_neighborSet_toSubgraph
  statement: (G H : SimpleGraph V) (h : H <= G)
  proof: by
  refine (Finset.card_eq_of_equiv_fintype ?_).symm
  simp only [mem_neighborFinset]
  rfl

@[simp]

中文:
定理 card_neighborSet_toSubgraph
  结论: (G H : SimpleGraph V) (h : H <= G)
  证明: by
  refine (Finset.card_eq_of_equiv_fintype ?_).symm
  simp only [mem_neighborFinset]
  rfl

@[simp]

Depends on / 依赖: Finset, Finset.card_eq_of_equiv_fintype, card_eq_of_equiv_fintype, mem_neighborFinset
-/
theorem card_neighborSet_toSubgraph (G H : SimpleGraph V) (h : H <= G)
    (v : V) [Fintype ↑((toSubgraph H h).neighborSet v)] [Fintype ↑(H.neighborSet v)] :
    Fintype.card ↑((toSubgraph H h).neighborSet v) = H.degree v := by
  refine (Finset.card_eq_of_equiv_fintype ?_).symm
  simp only [mem_neighborFinset]
  rfl

@[simp]
/--
lemma `degree_toSubgraph` / 引理 `degree_toSubgraph`

English:
lemma degree_toSubgraph
  statement: (G H : SimpleGraph V) (h : H <= G) {v : V}
  proof: by
  simp [Subgraph.degree, card_neighborSet_toSubgraph]

中文:
引理 degree_toSubgraph
  结论: (G H : SimpleGraph V) (h : H <= G) {v : V}
  证明: by
  simp [Subgraph.degree, card_neighborSet_toSubgraph]

Depends on / 依赖: Subgraph, Subgraph.degree, card_neighborSet_toSubgraph, degree
-/
lemma degree_toSubgraph (G H : SimpleGraph V) (h : H <= G) {v : V}
    [Fintype ↑((toSubgraph H h).neighborSet v)] [Fintype ↑(H.neighborSet v)] :
    (toSubgraph H h).degree v = H.degree v := by
  simp [Subgraph.degree, card_neighborSet_toSubgraph]

section MkProperties

/-! ### Properties of `singletonSubgraph` and `subgraphOfAdj` -/


variable {G : SimpleGraph V} {G' : SimpleGraph W}

instance (v : V) : Unique (G.singletonSubgraph v).verts :=
  Set.uniqueSingleton _

@[simp]
/--
theorem `singletonSubgraph_le_iff` / 定理 `singletonSubgraph_le_iff`

English:
theorem singletonSubgraph_le_iff
  given: (v : V) (H : G.Subgraph)
  proof: by
  refine ⟨fun h => h.1 (Set.mem_singleton v), ?_⟩
  intro h
  constructor
  · rwa [singletonSubgraph_verts, Set.singleton_subset_iff]
  · exact fun _ _ => False.elim

@[simp]

中文:
定理 singletonSubgraph_le_iff
  条件: (v : V) (H : G.Subgraph)
  证明: by
  refine ⟨fun h => h.1 (Set.mem_singleton v), ?_⟩
  intro h
  constructor
  · rwa [singletonSubgraph_verts, Set.singleton_subset_iff]
  · exact fun _ _ => False.elim

@[simp]

Depends on / 依赖: False.elim, Set.mem_singleton, Set.singleton_subset_iff, mem_singleton, singletonSubgraph_verts, singleton_subset_iff
-/
theorem singletonSubgraph_le_iff (v : V) (H : G.Subgraph) :
    G.singletonSubgraph v <= H ↔ v in H.verts := by
  refine ⟨fun h => h.1 (Set.mem_singleton v), ?_⟩
  intro h
  constructor
  · rwa [singletonSubgraph_verts, Set.singleton_subset_iff]
  · exact fun _ _ => False.elim

@[simp]
/--
theorem `map_singletonSubgraph` / 定理 `map_singletonSubgraph`

English:
theorem map_singletonSubgraph
  given: (f : G ->g G') {v : V}
  proof: by
  ext <;> simp only [Relation.Map, Subgraph.map_adj, singletonSubgraph_adj, Pi.bot_apply,
    exists_and_left, and_iff_left_iff_imp, Subgraph.map_verts,
    singletonSubgraph_verts, Set.image_singleton]
  exact False.elim

@[simp]

中文:
定理 map_singletonSubgraph
  条件: (f : G ->g G') {v : V}
  证明: by
  ext <;> simp only [Relation.Map, Subgraph.map_adj, singletonSubgraph_adj, Pi.bot_apply,
    exists_and_left, and_iff_left_iff_imp, Subgraph.map_verts,
    singletonSubgraph_verts, Set.image_singleton]
  exact False.elim

@[simp]

Depends on / 依赖: False.elim, Pi.bot_apply, Relation, Relation.Map, Set.image_singleton, Subgraph, Subgraph.map_adj, Subgraph.map_verts, and_iff_left_iff_imp, bot_apply, exists_and_left, image_singleton, map_adj, map_verts, singletonSubgraph_adj, singletonSubgraph_verts
-/
theorem map_singletonSubgraph (f : G ->g G') {v : V} :
    Subgraph.map f (G.singletonSubgraph v) = G'.singletonSubgraph (f v) := by
  ext <;> simp only [Relation.Map, Subgraph.map_adj, singletonSubgraph_adj, Pi.bot_apply,
    exists_and_left, and_iff_left_iff_imp, Subgraph.map_verts,
    singletonSubgraph_verts, Set.image_singleton]
  exact False.elim

@[simp]
/--
theorem `neighborSet_singletonSubgraph` / 定理 `neighborSet_singletonSubgraph`

English:
theorem neighborSet_singletonSubgraph
  given: (v w : V)
  statement: (G.singletonSubgraph v).neighborSet w = ∅
  proof: rfl

@[simp]

中文:
定理 neighborSet_singletonSubgraph
  条件: (v w : V)
  结论: (G.singletonSubgraph v).neighborSet w = ∅
  证明: rfl

@[simp]
-/
theorem neighborSet_singletonSubgraph (v w : V) : (G.singletonSubgraph v).neighborSet w = ∅ :=
  rfl

@[simp]
/--
theorem `edgeSet_singletonSubgraph` / 定理 `edgeSet_singletonSubgraph`

English:
theorem edgeSet_singletonSubgraph
  given: (v : V)
  statement: (G.singletonSubgraph v).edgeSet = ∅
  proof: Sym2.fromRel_bot

中文:
定理 edgeSet_singletonSubgraph
  条件: (v : V)
  结论: (G.singletonSubgraph v).edgeSet = ∅
  证明: Sym2.fromRel_bot

Depends on / 依赖: Sym2.fromRel_bot, fromRel_bot
-/
theorem edgeSet_singletonSubgraph (v : V) : (G.singletonSubgraph v).edgeSet = ∅ :=
  Sym2.fromRel_bot

/--
theorem `eq_singletonSubgraph_iff_verts_eq` / 定理 `eq_singletonSubgraph_iff_verts_eq`

English:
theorem eq_singletonSubgraph_iff_verts_eq
  given: (H : G.Subgraph) {v : V}
  proof: by
  refine ⟨fun h => by rw [h, singletonSubgraph_verts], fun h => ?_⟩
  ext
  · rw [h, singletonSubgraph_verts]
  · simp only [Prop.bot_eq_false, singletonSubgraph_adj, Pi.bot_apply, iff_false]
    intro ha
    have ha1 := ha.fst_mem
    have ha2 := ha.snd_mem
    rw [h]; rw [Set.mem_singleton_iff]

中文:
定理 eq_singletonSubgraph_iff_verts_eq
  条件: (H : G.Subgraph) {v : V}
  证明: by
  refine ⟨fun h => by rw [h, singletonSubgraph_verts], fun h => ?_⟩
  ext
  · rw [h, singletonSubgraph_verts]
  · simp only [Prop.bot_eq_false, singletonSubgraph_adj, Pi.bot_apply, iff_false]
    intro ha
    have ha1 := ha.fst_mem
    have ha2 := ha.snd_mem
    rw [h]; rw [Set.mem_singleton_iff]

Depends on / 依赖: Pi.bot_apply, Prop.bot_eq_false, Set.mem_singleton_iff, bot_apply, bot_eq_false, fst_mem, ha.fst_mem, ha.ne, ha.snd_mem, iff_false, mem_singleton_iff, singletonSubgraph_adj, singletonSubgraph_verts, snd_mem
-/
theorem eq_singletonSubgraph_iff_verts_eq (H : G.Subgraph) {v : V} :
    H = G.singletonSubgraph v ↔ H.verts = {v} := by
  refine ⟨fun h => by rw [h, singletonSubgraph_verts], fun h => ?_⟩
  ext
  · rw [h, singletonSubgraph_verts]
  · simp only [Prop.bot_eq_false, singletonSubgraph_adj, Pi.bot_apply, iff_false]
    intro ha
    have ha1 := ha.fst_mem
    have ha2 := ha.snd_mem
    rw [h]; rw [Set.mem_singleton_iff] at ha1 ha2
    subst_vars
    exact ha.ne rfl

/--
Instance `nonempty_subgraphOfAdj_verts` / 实例 `nonempty_subgraphOfAdj_verts`

English:
instance nonempty_subgraphOfAdj_verts
  signature: {v w : V} (hvw : G.Adj v w)
  body: ⟨⟨v, by simp⟩⟩

中文:
实例 nonempty_subgraphOfAdj_verts
  签名: {v w : V} (hvw : G.Adj v w)
  定义体: ⟨⟨v, by simp⟩⟩
-/
instance nonempty_subgraphOfAdj_verts {v w : V} (hvw : G.Adj v w) :
    Nonempty (G.subgraphOfAdj hvw).verts :=
  ⟨⟨v, by simp⟩⟩

/--
theorem `subgraphOfAdj_adj_self` / 定理 `subgraphOfAdj_adj_self`

English:
theorem subgraphOfAdj_adj_self
  given: {u v : V} (h : G.Adj u v)
  statement: (G.subgraphOfAdj h).Adj u v
  proof: rfl

@[simp]

中文:
定理 subgraphOfAdj_adj_self
  条件: {u v : V} (h : G.Adj u v)
  结论: (G.subgraphOfAdj h).Adj u v
  证明: rfl

@[simp]
-/
theorem subgraphOfAdj_adj_self {u v : V} (h : G.Adj u v) : (G.subgraphOfAdj h).Adj u v :=
  rfl

@[simp]
/--
theorem `edgeSet_subgraphOfAdj` / 定理 `edgeSet_subgraphOfAdj`

English:
theorem edgeSet_subgraphOfAdj
  given: {v w : V} (hvw : G.Adj v w)
  proof: by
  ext e
  refine e.ind ?_
  simp only [eq_comm, Set.mem_singleton_iff, Subgraph.mem_edgeSet, subgraphOfAdj_adj,
    forall₂_true_iff]

中文:
定理 edgeSet_subgraphOfAdj
  条件: {v w : V} (hvw : G.Adj v w)
  证明: by
  ext e
  refine e.ind ?_
  simp only [eq_comm, Set.mem_singleton_iff, Subgraph.mem_edgeSet, subgraphOfAdj_adj,
    forall₂_true_iff]

Depends on / 依赖: Set.mem_singleton_iff, Subgraph, Subgraph.mem_edgeSet, e.ind, eq_comm, mem_edgeSet, mem_singleton_iff, subgraphOfAdj_adj
-/
theorem edgeSet_subgraphOfAdj {v w : V} (hvw : G.Adj v w) :
    (G.subgraphOfAdj hvw).edgeSet = {s(v, w)} := by
  ext e
  refine e.ind ?_
  simp only [eq_comm, Set.mem_singleton_iff, Subgraph.mem_edgeSet, subgraphOfAdj_adj,
    forall₂_true_iff]

/--
lemma `subgraphOfAdj_le_of_adj` / 引理 `subgraphOfAdj_le_of_adj`

English:
lemma subgraphOfAdj_le_of_adj
  given: {v w : V} (H : G.Subgraph) (h : H.Adj v w)
  proof: by
  constructor
  · grind [subgraphOfAdj_verts, h.fst_mem, h.snd_mem]
  · grind [subgraphOfAdj_adj, h.symm]

@[simp]

中文:
引理 subgraphOfAdj_le_of_adj
  条件: {v w : V} (H : G.Subgraph) (h : H.Adj v w)
  证明: by
  constructor
  · grind [subgraphOfAdj_verts, h.fst_mem, h.snd_mem]
  · grind [subgraphOfAdj_adj, h.symm]

@[simp]

Depends on / 依赖: fst_mem, h.fst_mem, h.snd_mem, h.symm, snd_mem, subgraphOfAdj_adj, subgraphOfAdj_verts
-/
lemma subgraphOfAdj_le_of_adj {v w : V} (H : G.Subgraph) (h : H.Adj v w) :
    G.subgraphOfAdj (H.adj_sub h) <= H := by
  constructor
  · grind [subgraphOfAdj_verts, h.fst_mem, h.snd_mem]
  · grind [subgraphOfAdj_adj, h.symm]

@[simp]
/--
theorem `subgraphOfAdj_le_iff` / 定理 `subgraphOfAdj_le_iff`

English:
theorem subgraphOfAdj_le_iff
  given: {u v : V} (h : G.Adj u v) (H : G.Subgraph)
  proof: ⟨fun hle => hle.right subgraphOfAdj_adj_self h, subgraphOfAdj_le_of_adj H⟩

中文:
定理 subgraphOfAdj_le_iff
  条件: {u v : V} (h : G.Adj u v) (H : G.Subgraph)
  证明: ⟨fun hle => hle.right subgraphOfAdj_adj_self h, subgraphOfAdj_le_of_adj H⟩

Depends on / 依赖: hle.right, subgraphOfAdj_adj_self, subgraphOfAdj_le_of_adj
-/
theorem subgraphOfAdj_le_iff {u v : V} (h : G.Adj u v) (H : G.Subgraph) :
    G.subgraphOfAdj h <= H ↔ H.Adj u v :=
⟨fun hle => hle.right subgraphOfAdj_adj_self h, subgraphOfAdj_le_of_adj H⟩

/--
theorem `subgraphOfAdj_symm` / 定理 `subgraphOfAdj_symm`

English:
theorem subgraphOfAdj_symm
  given: {v w : V} (hvw : G.Adj v w)
  proof: by
  ext <;> simp [or_comm, and_comm]

@[simp]

中文:
定理 subgraphOfAdj_symm
  条件: {v w : V} (hvw : G.Adj v w)
  证明: by
  ext <;> simp [or_comm, and_comm]

@[simp]

Depends on / 依赖: and_comm, or_comm
-/
theorem subgraphOfAdj_symm {v w : V} (hvw : G.Adj v w) :
    G.subgraphOfAdj hvw.symm = G.subgraphOfAdj hvw := by
  ext <;> simp [or_comm, and_comm]

@[simp]
/--
theorem `map_subgraphOfAdj` / 定理 `map_subgraphOfAdj`

English:
theorem map_subgraphOfAdj
  given: (f : G ->g G') {v w : V} (hvw : G.Adj v w)
  proof: by
  ext <;> grind [Subgraph.map_verts, subgraphOfAdj_verts, Relation.Map, Subgraph.map_adj,
    subgraphOfAdj_adj]

中文:
定理 map_subgraphOfAdj
  条件: (f : G ->g G') {v w : V} (hvw : G.Adj v w)
  证明: by
  ext <;> grind [Subgraph.map_verts, subgraphOfAdj_verts, Relation.Map, Subgraph.map_adj,
    subgraphOfAdj_adj]

Depends on / 依赖: Relation, Relation.Map, Subgraph, Subgraph.map_adj, Subgraph.map_verts, map_adj, map_verts, subgraphOfAdj_adj, subgraphOfAdj_verts
-/
theorem map_subgraphOfAdj (f : G ->g G') {v w : V} (hvw : G.Adj v w) :
    Subgraph.map f (G.subgraphOfAdj hvw) = G'.subgraphOfAdj (f.map_adj hvw) := by
  ext <;> grind [Subgraph.map_verts, subgraphOfAdj_verts, Relation.Map, Subgraph.map_adj,
    subgraphOfAdj_adj]

/--
theorem `neighborSet_subgraphOfAdj_subset` / 定理 `neighborSet_subgraphOfAdj_subset`

English:
theorem neighborSet_subgraphOfAdj_subset
  given: {u v w : V} (hvw : G.Adj v w)
  proof: (G.subgraphOfAdj hvw).neighborSet_subset_verts _

@[simp]

中文:
定理 neighborSet_subgraphOfAdj_subset
  条件: {u v w : V} (hvw : G.Adj v w)
  证明: (G.subgraphOfAdj hvw).neighborSet_subset_verts _

@[simp]

Depends on / 依赖: G.subgraphOfAdj, neighborSet_subset_verts, subgraphOfAdj
-/
theorem neighborSet_subgraphOfAdj_subset {u v w : V} (hvw : G.Adj v w) :
    (G.subgraphOfAdj hvw).neighborSet u subseteq {v, w} :=
  (G.subgraphOfAdj hvw).neighborSet_subset_verts _

@[simp]
/--
theorem `neighborSet_fst_subgraphOfAdj` / 定理 `neighborSet_fst_subgraphOfAdj`

English:
theorem neighborSet_fst_subgraphOfAdj
  given: {v w : V} (hvw : G.Adj v w)
  proof: by
  ext u
  suffices w = u ↔ u = w by simpa [hvw.ne.symm] using this
  rw [eq_comm]

@[simp]

中文:
定理 neighborSet_fst_subgraphOfAdj
  条件: {v w : V} (hvw : G.Adj v w)
  证明: by
  ext u
  suffices w = u ↔ u = w by simpa [hvw.ne.symm] using this
  rw [eq_comm]

@[simp]

Depends on / 依赖: eq_comm, hvw.ne.symm
-/
theorem neighborSet_fst_subgraphOfAdj {v w : V} (hvw : G.Adj v w) :
    (G.subgraphOfAdj hvw).neighborSet v = {w} := by
  ext u
  suffices w = u ↔ u = w by simpa [hvw.ne.symm] using this
  rw [eq_comm]

@[simp]
/--
theorem `neighborSet_snd_subgraphOfAdj` / 定理 `neighborSet_snd_subgraphOfAdj`

English:
theorem neighborSet_snd_subgraphOfAdj
  given: {v w : V} (hvw : G.Adj v w)
  proof: by
  rw [subgraphOfAdj_symm hvw.symm]
  exact neighborSet_fst_subgraphOfAdj hvw.symm

@[simp]

中文:
定理 neighborSet_snd_subgraphOfAdj
  条件: {v w : V} (hvw : G.Adj v w)
  证明: by
  rw [subgraphOfAdj_symm hvw.symm]
  exact neighborSet_fst_subgraphOfAdj hvw.symm

@[simp]

Depends on / 依赖: hvw.symm, neighborSet_fst_subgraphOfAdj, subgraphOfAdj_symm
-/
theorem neighborSet_snd_subgraphOfAdj {v w : V} (hvw : G.Adj v w) :
    (G.subgraphOfAdj hvw).neighborSet w = {v} := by
  rw [subgraphOfAdj_symm hvw.symm]
  exact neighborSet_fst_subgraphOfAdj hvw.symm

@[simp]
/--
theorem `neighborSet_subgraphOfAdj_of_ne_of_ne` / 定理 `neighborSet_subgraphOfAdj_of_ne_of_ne`

English:
theorem neighborSet_subgraphOfAdj_of_ne_of_ne
  statement: {u v w : V} (hvw : G.Adj v w) (hv : u != v)
  proof: by
  ext
  simp [hv.symm, hw.symm]

中文:
定理 neighborSet_subgraphOfAdj_of_ne_of_ne
  结论: {u v w : V} (hvw : G.Adj v w) (hv : u != v)
  证明: by
  ext
  simp [hv.symm, hw.symm]

Depends on / 依赖: hv.symm, hw.symm
-/
theorem neighborSet_subgraphOfAdj_of_ne_of_ne {u v w : V} (hvw : G.Adj v w) (hv : u != v)
    (hw : u != w) : (G.subgraphOfAdj hvw).neighborSet u = ∅ := by
  ext
  simp [hv.symm, hw.symm]

/--
theorem `neighborSet_subgraphOfAdj` / 定理 `neighborSet_subgraphOfAdj`

English:
theorem neighborSet_subgraphOfAdj
  given: [DecidableEq V] {u v w : V} (hvw : G.Adj v w)
  proof: by
  split_ifs <;> subst_vars <;> simp [*]

中文:
定理 neighborSet_subgraphOfAdj
  条件: [DecidableEq V] {u v w : V} (hvw : G.Adj v w)
  证明: by
  split_ifs <;> subst_vars <;> simp [*]

Depends on / 依赖: split_ifs
-/
theorem neighborSet_subgraphOfAdj [DecidableEq V] {u v w : V} (hvw : G.Adj v w) :
    (G.subgraphOfAdj hvw).neighborSet u =
    (if u = v then {w} else ∅) union if u = w then {v} else ∅ := by
  split_ifs <;> subst_vars <;> simp [*]

/--
theorem `singletonSubgraph_fst_le_subgraphOfAdj` / 定理 `singletonSubgraph_fst_le_subgraphOfAdj`

English:
theorem singletonSubgraph_fst_le_subgraphOfAdj
  given: {u v : V} {h : G.Adj u v}
  proof: by
  simp

中文:
定理 singletonSubgraph_fst_le_subgraphOfAdj
  条件: {u v : V} {h : G.Adj u v}
  证明: by
  simp
-/
theorem singletonSubgraph_fst_le_subgraphOfAdj {u v : V} {h : G.Adj u v} :
    G.singletonSubgraph u <= G.subgraphOfAdj h := by
  simp

/--
theorem `singletonSubgraph_snd_le_subgraphOfAdj` / 定理 `singletonSubgraph_snd_le_subgraphOfAdj`

English:
theorem singletonSubgraph_snd_le_subgraphOfAdj
  given: {u v : V} {h : G.Adj u v}
  proof: by
  simp

@[simp]

中文:
定理 singletonSubgraph_snd_le_subgraphOfAdj
  条件: {u v : V} {h : G.Adj u v}
  证明: by
  simp

@[simp]
-/
theorem singletonSubgraph_snd_le_subgraphOfAdj {u v : V} {h : G.Adj u v} :
    G.singletonSubgraph v <= G.subgraphOfAdj h := by
  simp

@[simp]
/--
lemma `support_subgraphOfAdj` / 引理 `support_subgraphOfAdj`

English:
lemma support_subgraphOfAdj
  given: {u v : V} (h : G.Adj u v)
  proof: by
  ext
  rw [Subgraph.mem_support]
  simp only [subgraphOfAdj_adj, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk]
  refine ⟨?_, fun h => h.elim (fun hl => ⟨v, .inl ⟨hl.symm, rfl⟩⟩) fun hr => ⟨u, .inr ⟨rfl, hr.symm⟩⟩⟩
  rintro ⟨_, hw⟩
  exact hw.elim (fun h1 => .inl h1.1.symm) fun hr => 

中文:
引理 support_subgraphOfAdj
  条件: {u v : V} (h : G.Adj u v)
  证明: by
  ext
  rw [Subgraph.mem_support]
  simp only [subgraphOfAdj_adj, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk]
  refine ⟨?_, fun h => h.elim (fun hl => ⟨v, .inl ⟨hl.symm, rfl⟩⟩) fun hr => ⟨u, .inr ⟨rfl, hr.symm⟩⟩⟩
  rintro ⟨_, hw⟩
  exact hw.elim (fun h1 => .inl h1.1.symm) fun hr => 

Depends on / 依赖: Prod.mk.injEq, Prod.swap_prod_mk, Subgraph, Subgraph.mem_support, Sym2.eq, Sym2.rel_iff, h.elim, hl.symm, hr.symm, hw.elim, mem_support, rel_iff, subgraphOfAdj_adj, swap_prod_mk
-/
lemma support_subgraphOfAdj {u v : V} (h : G.Adj u v) :
    (G.subgraphOfAdj h).support = {u, v} := by
  ext
  rw [Subgraph.mem_support]
  simp only [subgraphOfAdj_adj, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk]
  refine ⟨?_, fun h => h.elim (fun hl => ⟨v, .inl ⟨hl.symm, rfl⟩⟩) fun hr => ⟨u, .inr ⟨rfl, hr.symm⟩⟩⟩
  rintro ⟨_, hw⟩
  exact hw.elim (fun h1 => .inl h1.1.symm) fun hr => .inr hr.2.symm

end MkProperties

namespace Subgraph

variable {G : SimpleGraph V}

/-! ### Subgraphs of subgraphs -/


/--
Definition of `coeSubgraph` / `coeSubgraph` 的定义

English:
abbreviation coeSubgraph
  signature: {G' : G.Subgraph}
  body: Subgraph.map G'.hom

中文:
缩写 coeSubgraph
  签名: {G' : G.Subgraph}
  定义体: Subgraph.map G'.hom
-/
protected abbrev coeSubgraph {G' : G.Subgraph} : G'.coe.Subgraph -> G.Subgraph :=
  Subgraph.map G'.hom

/--
Definition of `restrict` / `restrict` 的定义

English:
abbreviation restrict
  signature: {G' : G.Subgraph}
  body: Subgraph.comap G'.hom

@[simp]

中文:
缩写 restrict
  签名: {G' : G.Subgraph}
  定义体: Subgraph.comap G'.hom

@[simp]
-/
protected abbrev restrict {G' : G.Subgraph} : G.Subgraph -> G'.coe.Subgraph :=
  Subgraph.comap G'.hom

@[simp]
/--
lemma `verts_coeSubgraph` / 引理 `verts_coeSubgraph`

English:
lemma verts_coeSubgraph
  given: {G' : Subgraph G} (G'' : Subgraph G'.coe)
  proof: rfl

中文:
引理 verts_coeSubgraph
  条件: {G' : Subgraph G} (G'' : Subgraph G'.coe)
  证明: rfl
-/
lemma verts_coeSubgraph {G' : Subgraph G} (G'' : Subgraph G'.coe) :
    (Subgraph.coeSubgraph G'').verts = (G''.verts : Set V) := rfl

/--
lemma `coeSubgraph_adj` / 引理 `coeSubgraph_adj`

English:
lemma coeSubgraph_adj
  given: {G' : G.Subgraph} (G'' : G'.coe.Subgraph) (v w : V)
  proof: by
  simp [Relation.Map]

中文:
引理 coeSubgraph_adj
  条件: {G' : G.Subgraph} (G'' : G'.coe.Subgraph) (v w : V)
  证明: by
  simp [Relation.Map]

Depends on / 依赖: Relation, Relation.Map
-/
lemma coeSubgraph_adj {G' : G.Subgraph} (G'' : G'.coe.Subgraph) (v w : V) :
    (G'.coeSubgraph G'').Adj v w ↔
      exists (hv : v in G'.verts) (hw : w in G'.verts), G''.Adj ⟨v, hv⟩ ⟨w, hw⟩ := by
  simp [Relation.Map]

/--
lemma `restrict_adj` / 引理 `restrict_adj`

English:
lemma restrict_adj
  given: {G' G'' : G.Subgraph} (v w : G'.verts)
  proof: Iff.rfl

中文:
引理 restrict_adj
  条件: {G' G'' : G.Subgraph} (v w : G'.verts)
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
lemma restrict_adj {G' G'' : G.Subgraph} (v w : G'.verts) :
    (G'.restrict G'').Adj v w ↔ G'.Adj v w ∧ G''.Adj v w := Iff.rfl

/--
theorem `restrict_coeSubgraph` / 定理 `restrict_coeSubgraph`

English:
theorem restrict_coeSubgraph
  given: {G' : G.Subgraph} (G'' : G'.coe.Subgraph)
  proof: by
  ext
  · simp
  · rw [restrict_adj, coeSubgraph_adj]
    simpa using G''.adj_sub

中文:
定理 restrict_coeSubgraph
  条件: {G' : G.Subgraph} (G'' : G'.coe.Subgraph)
  证明: by
  ext
  · simp
  · rw [restrict_adj, coeSubgraph_adj]
    simpa using G''.adj_sub

Depends on / 依赖: adj_sub, coeSubgraph_adj, restrict_adj
-/
theorem restrict_coeSubgraph {G' : G.Subgraph} (G'' : G'.coe.Subgraph) :
    Subgraph.restrict (Subgraph.coeSubgraph G'') = G'' := by
  ext
  · simp
  · rw [restrict_adj, coeSubgraph_adj]
    simpa using G''.adj_sub

/--
theorem `coeSubgraph_injective` / 定理 `coeSubgraph_injective`

English:
theorem coeSubgraph_injective
  given: (G' : G.Subgraph)
  proof: Function.LeftInverse.injective restrict_coeSubgraph

中文:
定理 coeSubgraph_injective
  条件: (G' : G.Subgraph)
  证明: Function.LeftInverse.injective restrict_coeSubgraph

Depends on / 依赖: Function, Function.LeftInverse.injective, LeftInverse, injective, restrict_coeSubgraph
-/
theorem coeSubgraph_injective (G' : G.Subgraph) :
    Function.Injective (Subgraph.coeSubgraph : G'.coe.Subgraph -> G.Subgraph) :=
  Function.LeftInverse.injective restrict_coeSubgraph

/--
lemma `coeSubgraph_le` / 引理 `coeSubgraph_le`

English:
lemma coeSubgraph_le
  given: {H : G.Subgraph} (H' : H.coe.Subgraph)
  proof: by
  constructor
  · simp
  · rintro v w ⟨_, _, h, rfl, rfl⟩
    exact H'.adj_sub h

中文:
引理 coeSubgraph_le
  条件: {H : G.Subgraph} (H' : H.coe.Subgraph)
  证明: by
  constructor
  · simp
  · rintro v w ⟨_, _, h, rfl, rfl⟩
    exact H'.adj_sub h

Depends on / 依赖: adj_sub
-/
lemma coeSubgraph_le {H : G.Subgraph} (H' : H.coe.Subgraph) :
    Subgraph.coeSubgraph H' <= H := by
  constructor
  · simp
  · rintro v w ⟨_, _, h, rfl, rfl⟩
    exact H'.adj_sub h

/--
lemma `coeSubgraph_restrict_eq` / 引理 `coeSubgraph_restrict_eq`

English:
lemma coeSubgraph_restrict_eq
  given: {H : G.Subgraph} (H' : G.Subgraph)
  proof: by
  ext
  · simp
  · simp_rw [coeSubgraph_adj, restrict_adj]
    simp only [exists_and_left, exists_prop, inf_adj, and_congr_right_iff]
    intro h
    simp [H.edge_vert h, H.edge_vert h.symm]

中文:
引理 coeSubgraph_restrict_eq
  条件: {H : G.Subgraph} (H' : G.Subgraph)
  证明: by
  ext
  · simp
  · simp_rw [coeSubgraph_adj, restrict_adj]
    simp only [exists_and_left, exists_prop, inf_adj, and_congr_right_iff]
    intro h
    simp [H.edge_vert h, H.edge_vert h.symm]

Depends on / 依赖: H.edge_vert, and_congr_right_iff, coeSubgraph_adj, edge_vert, exists_and_left, exists_prop, h.symm, inf_adj, restrict_adj, simp_rw
-/
lemma coeSubgraph_restrict_eq {H : G.Subgraph} (H' : G.Subgraph) :
    Subgraph.coeSubgraph (H.restrict H') = H ⊓ H' := by
  ext
  · simp
  · simp_rw [coeSubgraph_adj, restrict_adj]
    simp only [exists_and_left, exists_prop, inf_adj, and_congr_right_iff]
    intro h
    simp [H.edge_vert h, H.edge_vert h.symm]

/-! ### Edge deletion -/


/--
Definition of `deleteEdges` / `deleteEdges` 的定义

English:
definition deleteEdges
  signature: (G' : G.Subgraph) (s : Set (Sym2 V))
  body: G'.verts
  Adj := G'.Adj \ Sym2.ToRel s
  adj_sub h' := G'.adj_sub h'.1
  edge_vert h' := G'.edge_vert h'.1
  symm.symm a b := by simp [G'.adj_comm, Sym2.eq_swap]

中文:
定义 deleteEdges
  签名: (G' : G.Subgraph) (s : Set (Sym2 V))
  定义体: G'.verts
  Adj := G'.Adj \ Sym2.ToRel s
  adj_sub h' := G'.adj_sub h'.1
  edge_vert h' := G'.edge_vert h'.1
  symm.symm a b := by simp [G'.adj_comm, Sym2.eq_swap]
-/
def deleteEdges (G' : G.Subgraph) (s : Set (Sym2 V)) : G.Subgraph where
  verts := G'.verts
  Adj := G'.Adj \ Sym2.ToRel s
  adj_sub h' := G'.adj_sub h'.1
  edge_vert h' := G'.edge_vert h'.1
  symm.symm a b := by simp [G'.adj_comm, Sym2.eq_swap]

section DeleteEdges

variable {G' : G.Subgraph} (s : Set (Sym2 V))

@[simp]
/--
theorem `deleteEdges_verts` / 定理 `deleteEdges_verts`

English:
theorem deleteEdges_verts
  statement: (G'.deleteEdges s).verts = G'.verts
  proof: rfl

@[simp]

中文:
定理 deleteEdges_verts
  结论: (G'.deleteEdges s).verts = G'.verts
  证明: rfl

@[simp]
-/
theorem deleteEdges_verts : (G'.deleteEdges s).verts = G'.verts :=
  rfl

@[simp]
/--
theorem `deleteEdges_adj` / 定理 `deleteEdges_adj`

English:
theorem deleteEdges_adj
  given: (v w : V)
  statement: (G'.deleteEdges s).Adj v w ↔ G'.Adj v w ∧ s(v, w) ∉ s
  proof: Iff.rfl

@[simp]

中文:
定理 deleteEdges_adj
  条件: (v w : V)
  结论: (G'.deleteEdges s).Adj v w ↔ G'.Adj v w ∧ s(v, w) ∉ s
  证明: Iff.rfl

@[simp]

Depends on / 依赖: Iff.rfl
-/
theorem deleteEdges_adj (v w : V) : (G'.deleteEdges s).Adj v w ↔ G'.Adj v w ∧ s(v, w) ∉ s :=
  Iff.rfl

@[simp]
/--
theorem `deleteEdges_deleteEdges` / 定理 `deleteEdges_deleteEdges`

English:
theorem deleteEdges_deleteEdges
  given: (s s' : Set (Sym2 V))
  proof: by
  ext <;> simp [and_assoc, not_or]

@[simp]

中文:
定理 deleteEdges_deleteEdges
  条件: (s s' : Set (Sym2 V))
  证明: by
  ext <;> simp [and_assoc, not_or]

@[simp]

Depends on / 依赖: and_assoc, not_or
-/
theorem deleteEdges_deleteEdges (s s' : Set (Sym2 V)) :
    (G'.deleteEdges s).deleteEdges s' = G'.deleteEdges (s union s') := by
  ext <;> simp [and_assoc, not_or]

@[simp]
/--
theorem `deleteEdges_empty_eq` / 定理 `deleteEdges_empty_eq`

English:
theorem deleteEdges_empty_eq
  statement: G'.deleteEdges ∅ = G'
  proof: by
  ext <;> simp

@[simp]

中文:
定理 deleteEdges_empty_eq
  结论: G'.deleteEdges ∅ = G'
  证明: by
  ext <;> simp

@[simp]
-/
theorem deleteEdges_empty_eq : G'.deleteEdges ∅ = G' := by
  ext <;> simp

@[simp]
/--
theorem `deleteEdges_spanningCoe_eq` / 定理 `deleteEdges_spanningCoe_eq`

English:
theorem deleteEdges_spanningCoe_eq
  proof: by
  ext
  simp

中文:
定理 deleteEdges_spanningCoe_eq
  证明: by
  ext
  simp
-/
theorem deleteEdges_spanningCoe_eq :
    G'.spanningCoe.deleteEdges s = (G'.deleteEdges s).spanningCoe := by
  ext
  simp

set_option backward.isDefEq.respectTransparency false in
/--
theorem `deleteEdges_coe_eq` / 定理 `deleteEdges_coe_eq`

English:
theorem deleteEdges_coe_eq
  given: (s : Set (Sym2 G'.verts))
  proof: by
  ext ⟨v, hv⟩ ⟨w, hw⟩
  simp only [SimpleGraph.deleteEdges_adj, coe_adj, deleteEdges_adj, Set.mem_image, not_exists,
    not_and, and_congr_right_iff]
  intro
  constructor
  · intro hs
    refine Sym2.ind ?_
    rintro ⟨v', hv'⟩ ⟨w', hw'⟩
    simp only [Sym2.map_mk, Sym2.eq]
    contrapose
    r

中文:
定理 deleteEdges_coe_eq
  条件: (s : Set (Sym2 G'.verts))
  证明: by
  ext ⟨v, hv⟩ ⟨w, hw⟩
  simp only [SimpleGraph.deleteEdges_adj, coe_adj, deleteEdges_adj, Set.mem_image, not_exists,
    not_and, and_congr_right_iff]
  intro
  constructor
  · intro hs
    refine Sym2.ind ?_
    rintro ⟨v', hv'⟩ ⟨w', hw'⟩
    simp only [Sym2.map_mk, Sym2.eq]
    contrapose
    r

Depends on / 依赖: Set.mem_image, SimpleGraph, SimpleGraph.deleteEdges_adj, Sym2.eq, Sym2.eq_swap, Sym2.ind, Sym2.map_mk, and_congr_right_iff, coe_adj, contrapose, deleteEdges_adj, eq_swap, map_mk, mem_image, not_and, not_exists
-/
theorem deleteEdges_coe_eq (s : Set (Sym2 G'.verts)) :
    G'.coe.deleteEdges s = (G'.deleteEdges (Sym2.map (↑) '' s)).coe := by
  ext ⟨v, hv⟩ ⟨w, hw⟩
  simp only [SimpleGraph.deleteEdges_adj, coe_adj, deleteEdges_adj, Set.mem_image, not_exists,
    not_and, and_congr_right_iff]
  intro
  constructor
  · intro hs
    refine Sym2.ind ?_
    rintro ⟨v', hv'⟩ ⟨w', hw'⟩
    simp only [Sym2.map_mk, Sym2.eq]
    contrapose
    rintro (_ | _) <;> simpa only [Sym2.eq_swap]
  · intro h' hs
    exact h' _ hs rfl

set_option backward.isDefEq.respectTransparency false in
/--
theorem `coe_deleteEdges_eq` / 定理 `coe_deleteEdges_eq`

English:
theorem coe_deleteEdges_eq
  given: (s : Set (Sym2 V))
  proof: by
  ext ⟨v, hv⟩ ⟨w, hw⟩
  simp

中文:
定理 coe_deleteEdges_eq
  条件: (s : Set (Sym2 V))
  证明: by
  ext ⟨v, hv⟩ ⟨w, hw⟩
  simp
-/
theorem coe_deleteEdges_eq (s : Set (Sym2 V)) :
    (G'.deleteEdges s).coe = G'.coe.deleteEdges (Sym2.map (↑) ⁻¹' s) := by
  ext ⟨v, hv⟩ ⟨w, hw⟩
  simp

/--
theorem `deleteEdges_le` / 定理 `deleteEdges_le`

English:
theorem deleteEdges_le
  statement: G'.deleteEdges s <= G'
  proof: by
  constructor <;> simp +contextual

中文:
定理 deleteEdges_le
  结论: G'.deleteEdges s <= G'
  证明: by
  constructor <;> simp +contextual

Depends on / 依赖: contextual
-/
theorem deleteEdges_le : G'.deleteEdges s <= G' := by
  constructor <;> simp +contextual

/--
theorem `deleteEdges_le_of_le` / 定理 `deleteEdges_le_of_le`

English:
theorem deleteEdges_le_of_le
  given: {s s' : Set (Sym2 V)} (h : s subseteq s')
  proof: by
  constructor <;> simp +contextual only [deleteEdges_verts, deleteEdges_adj,
    true_and, and_imp, subset_rfl]
  exact fun _ _ _ hs' hs => hs' (h hs)

@[simp]

中文:
定理 deleteEdges_le_of_le
  条件: {s s' : Set (Sym2 V)} (h : s subseteq s')
  证明: by
  constructor <;> simp +contextual only [deleteEdges_verts, deleteEdges_adj,
    true_and, and_imp, subset_rfl]
  exact fun _ _ _ hs' hs => hs' (h hs)

@[simp]

Depends on / 依赖: and_imp, contextual, deleteEdges_adj, deleteEdges_verts, subset_rfl, true_and
-/
theorem deleteEdges_le_of_le {s s' : Set (Sym2 V)} (h : s subseteq s') :
    G'.deleteEdges s' <= G'.deleteEdges s := by
  constructor <;> simp +contextual only [deleteEdges_verts, deleteEdges_adj,
    true_and, and_imp, subset_rfl]
  exact fun _ _ _ hs' hs => hs' (h hs)

@[simp]
/--
theorem `deleteEdges_inter_edgeSet_left_eq` / 定理 `deleteEdges_inter_edgeSet_left_eq`

English:
theorem deleteEdges_inter_edgeSet_left_eq
  proof: by
  ext <;> simp +contextual

@[simp]

中文:
定理 deleteEdges_inter_edgeSet_left_eq
  证明: by
  ext <;> simp +contextual

@[simp]

Depends on / 依赖: contextual
-/
theorem deleteEdges_inter_edgeSet_left_eq :
    G'.deleteEdges (G'.edgeSet inter s) = G'.deleteEdges s := by
  ext <;> simp +contextual

@[simp]
/--
theorem `deleteEdges_inter_edgeSet_right_eq` / 定理 `deleteEdges_inter_edgeSet_right_eq`

English:
theorem deleteEdges_inter_edgeSet_right_eq
  proof: by
  ext <;> simp +contextual [imp_false]

中文:
定理 deleteEdges_inter_edgeSet_right_eq
  证明: by
  ext <;> simp +contextual [imp_false]

Depends on / 依赖: contextual, imp_false
-/
theorem deleteEdges_inter_edgeSet_right_eq :
    G'.deleteEdges (s inter G'.edgeSet) = G'.deleteEdges s := by
  ext <;> simp +contextual [imp_false]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `coe_deleteEdges_le` / 定理 `coe_deleteEdges_le`

English:
theorem coe_deleteEdges_le
  statement: (G'.deleteEdges s).coe <= (G'.coe : SimpleGraph G'.verts)
  proof: by
  intro v w
  simp +contextual

中文:
定理 coe_deleteEdges_le
  结论: (G'.deleteEdges s).coe <= (G'.coe : SimpleGraph G'.verts)
  证明: by
  intro v w
  simp +contextual

Depends on / 依赖: contextual
-/
theorem coe_deleteEdges_le : (G'.deleteEdges s).coe <= (G'.coe : SimpleGraph G'.verts) := by
  intro v w
  simp +contextual

/--
theorem `spanningCoe_deleteEdges_le` / 定理 `spanningCoe_deleteEdges_le`

English:
theorem spanningCoe_deleteEdges_le
  given: (G' : G.Subgraph) (s : Set (Sym2 V))
  proof: spanningCoe_le_of_le (deleteEdges_le s)

中文:
定理 spanningCoe_deleteEdges_le
  条件: (G' : G.Subgraph) (s : Set (Sym2 V))
  证明: spanningCoe_le_of_le (deleteEdges_le s)

Depends on / 依赖: deleteEdges_le, spanningCoe_le_of_le
-/
theorem spanningCoe_deleteEdges_le (G' : G.Subgraph) (s : Set (Sym2 V)) :
    (G'.deleteEdges s).spanningCoe <= G'.spanningCoe :=
  spanningCoe_le_of_le (deleteEdges_le s)

end DeleteEdges

/-! ### Induced subgraphs -/


/- Given a subgraph, we can change its vertex set while removing any invalid edges, which
gives induced subgraphs. See also `SimpleGraph.induce` for the `SimpleGraph` version, which,
unlike for subgraphs, results in a graph with a different vertex type. -/
/-- The induced subgraph of a subgraph. The expectation is that `s ⊆ G'.verts` for the usual
notion of an induced subgraph, but, in general, `s` is taken to be the new vertex set and edges
are induced from the subgraph `G'`. -/
@[simps]
/--
Definition of `induce` / `induce` 的定义

English:
definition induce
  signature: (G' : G.Subgraph) (s : Set V)
  body: s
  Adj u v := u in s ∧ v in s ∧ G'.Adj u v
  adj_sub h := G'.adj_sub h.2.2
  edge_vert h := h.1
  symm.symm _ _ h := ⟨h.2.1, h.1, h.2.2.symm⟩

中文:
定义 induce
  签名: (G' : G.Subgraph) (s : Set V)
  定义体: s
  Adj u v := u in s ∧ v in s ∧ G'.Adj u v
  adj_sub h := G'.adj_sub h.2.2
  edge_vert h := h.1
  symm.symm _ _ h := ⟨h.2.1, h.1, h.2.2.symm⟩
-/
def induce (G' : G.Subgraph) (s : Set V) : G.Subgraph where
  verts := s
  Adj u v := u in s ∧ v in s ∧ G'.Adj u v
  adj_sub h := G'.adj_sub h.2.2
  edge_vert h := h.1
  symm.symm _ _ h := ⟨h.2.1, h.1, h.2.2.symm⟩

set_option backward.isDefEq.respectTransparency false in
/--
theorem `_root_.SimpleGraph.induce_eq_coe_induce_top` / 定理 `_root_.SimpleGraph.induce_eq_coe_induce_top`

English:
theorem _root_.SimpleGraph.induce_eq_coe_induce_top
  given: (s : Set V)
  proof: by
  ext
  simp

中文:
定理 _root_.SimpleGraph.induce_eq_coe_induce_top
  条件: (s : Set V)
  证明: by
  ext
  simp
-/
theorem _root_.SimpleGraph.induce_eq_coe_induce_top (s : Set V) :
    G.induce s = ((⊤ : G.Subgraph).induce s).coe := by
  ext
  simp

/--
lemma `_root_.SimpleGraph.spanningCoe_induce_top` / 引理 `_root_.SimpleGraph.spanningCoe_induce_top`

English:
lemma _root_.SimpleGraph.spanningCoe_induce_top
  given: (s : Set V)
  proof: by
  #adaptation_note /-- Before https://github.com/leanprover/lean4/pull/13166
  (replacing grind's canonicalizer with a type-directed normalizer), `grind` closed this goal.
  It is not yet clear whether this is due to defeq abuse in Mathlib or a problem in the new
  canonicalizer; a minimization w

中文:
引理 _root_.SimpleGraph.spanningCoe_induce_top
  条件: (s : Set V)
  证明: by
  #adaptation_note /-- Before https://github.com/leanprover/lean4/pull/13166
  (replacing grind's canonicalizer with a type-directed normalizer), `grind` closed this goal.
  It is not yet clear whether this is due to defeq abuse in Mathlib or a problem in the new
  canonicalizer; a minimization w

Depends on / 依赖: Before, Mathlib, Subgraph, Subgraph.spanningCoe_coe, adaptation_note, canonicalizer, closed, directed, github, github.com, induce_eq_coe_induce_top, leanprover, minimization, normalizer, original, problem, replacing, spanningCoe_coe, whether
-/
lemma _root_.SimpleGraph.spanningCoe_induce_top (s : Set V) :
    ((⊤ : G.Subgraph).induce s).spanningCoe = (G.induce s).spanningCoe := by
  #adaptation_note /-- Before https://github.com/leanprover/lean4/pull/13166
  (replacing grind's canonicalizer with a type-directed normalizer), `grind` closed this goal.
  It is not yet clear whether this is due to defeq abuse in Mathlib or a problem in the new
  canonicalizer; a minimization would help. The original proof was:
  `grind [induce_eq_coe_induce_top, Subgraph.spanningCoe_coe]` -/
  rw [induce_eq_coe_induce_top]
  exact (Subgraph.spanningCoe_coe _).symm

section Induce

variable {G' G'' : G.Subgraph} {s s' : Set V}

@[simp]
/--
theorem `IsInduced.induce_top_verts` / 定理 `IsInduced.induce_top_verts`

English:
theorem IsInduced.induce_top_verts
  given: (h : G'.IsInduced)
  statement: induce ⊤ G'.verts = G'
  proof: Subgraph.ext rfl funext₂ fun _ _ => propext
    ⟨fun ⟨hu, hv, h'⟩ => h hu hv h', fun h => ⟨G'.edge_vert h, G'.edge_vert h.symm, h.adj_sub⟩⟩

中文:
定理 IsInduced.induce_top_verts
  条件: (h : G'.IsInduced)
  结论: induce ⊤ G'.verts = G'
  证明: Subgraph.ext rfl funext₂ fun _ _ => propext
    ⟨fun ⟨hu, hv, h'⟩ => h hu hv h', fun h => ⟨G'.edge_vert h, G'.edge_vert h.symm, h.adj_sub⟩⟩

Depends on / 依赖: Subgraph, Subgraph.ext, adj_sub, edge_vert, h.adj_sub, h.symm, propext
-/
theorem IsInduced.induce_top_verts (h : G'.IsInduced) : induce ⊤ G'.verts = G' :=
Subgraph.ext rfl funext₂ fun _ _ => propext
    ⟨fun ⟨hu, hv, h'⟩ => h hu hv h', fun h => ⟨G'.edge_vert h, G'.edge_vert h.symm, h.adj_sub⟩⟩

/--
theorem `isInduced_iff_exists_eq_induce_top` / 定理 `isInduced_iff_exists_eq_induce_top`

English:
theorem isInduced_iff_exists_eq_induce_top
  given: (G' : G.Subgraph)
  proof: by
  refine ⟨fun h => ⟨G'.verts, h.induce_top_verts.symm⟩, fun ⟨s, h⟩ _ hu _ hv hadj => ?_⟩
  rw [h]; rw [(h ▸ rfl : s = G'.verts)]
  exact ⟨hu, hv, hadj⟩

@[gcongr]

中文:
定理 isInduced_iff_exists_eq_induce_top
  条件: (G' : G.Subgraph)
  证明: by
  refine ⟨fun h => ⟨G'.verts, h.induce_top_verts.symm⟩, fun ⟨s, h⟩ _ hu _ hv hadj => ?_⟩
  rw [h]; rw [(h ▸ rfl : s = G'.verts)]
  exact ⟨hu, hv, hadj⟩

@[gcongr]

Depends on / 依赖: h.induce_top_verts.symm, induce_top_verts
-/
theorem isInduced_iff_exists_eq_induce_top (G' : G.Subgraph) :
    G'.IsInduced ↔ exists s, G' = induce ⊤ s := by
  refine ⟨fun h => ⟨G'.verts, h.induce_top_verts.symm⟩, fun ⟨s, h⟩ _ hu _ hv hadj => ?_⟩
  rw [h]; rw [(h ▸ rfl : s = G'.verts)]
  exact ⟨hu, hv, hadj⟩

@[gcongr]
/--
theorem `induce_mono` / 定理 `induce_mono`

English:
theorem induce_mono
  given: (hg : G' <= G'') (hs : s subseteq s')
  statement: G'.induce s <= G''.induce s'
  proof: by
  constructor
  · simp [hs]
  · simp +contextual only [induce_adj, and_imp]
    intro v w hv hw ha
    exact ⟨hs hv, hs hw, hg.2 ha⟩

@[gcongr, mono]

中文:
定理 induce_mono
  条件: (hg : G' <= G'') (hs : s subseteq s')
  结论: G'.induce s <= G''.induce s'
  证明: by
  constructor
  · simp [hs]
  · simp +contextual only [induce_adj, and_imp]
    intro v w hv hw ha
    exact ⟨hs hv, hs hw, hg.2 ha⟩

@[gcongr, mono]

Depends on / 依赖: and_imp, contextual, induce_adj
-/
theorem induce_mono (hg : G' <= G'') (hs : s subseteq s') : G'.induce s <= G''.induce s' := by
  constructor
  · simp [hs]
  · simp +contextual only [induce_adj, and_imp]
    intro v w hv hw ha
    exact ⟨hs hv, hs hw, hg.2 ha⟩

@[gcongr, mono]
/--
theorem `induce_mono_left` / 定理 `induce_mono_left`

English:
theorem induce_mono_left
  given: (hg : G' <= G'')
  statement: G'.induce s <= G''.induce s
  proof: induce_mono hg subset_rfl

@[gcongr, mono]

中文:
定理 induce_mono_left
  条件: (hg : G' <= G'')
  结论: G'.induce s <= G''.induce s
  证明: induce_mono hg subset_rfl

@[gcongr, mono]

Depends on / 依赖: induce_mono, subset_rfl
-/
theorem induce_mono_left (hg : G' <= G'') : G'.induce s <= G''.induce s :=
  induce_mono hg subset_rfl

@[gcongr, mono]
/--
theorem `induce_mono_right` / 定理 `induce_mono_right`

English:
theorem induce_mono_right
  given: (hs : s subseteq s')
  statement: G'.induce s <= G'.induce s'
  proof: induce_mono le_rfl hs

@[simp]

中文:
定理 induce_mono_right
  条件: (hs : s subseteq s')
  结论: G'.induce s <= G'.induce s'
  证明: induce_mono le_rfl hs

@[simp]

Depends on / 依赖: induce_mono, le_rfl
-/
theorem induce_mono_right (hs : s subseteq s') : G'.induce s <= G'.induce s' :=
  induce_mono le_rfl hs

@[simp]
/--
theorem `induce_empty` / 定理 `induce_empty`

English:
theorem induce_empty
  statement: G'.induce ∅ = ⊥
  proof: by
  ext <;> simp

@[simp]

中文:
定理 induce_empty
  结论: G'.induce ∅ = ⊥
  证明: by
  ext <;> simp

@[simp]
-/
theorem induce_empty : G'.induce ∅ = ⊥ := by
  ext <;> simp

@[simp]
/--
theorem `induce_self_verts` / 定理 `induce_self_verts`

English:
theorem induce_self_verts
  statement: G'.induce G'.verts = G'
  proof: by
  ext
  · simp
  · constructor <;>
      simp +contextual only [induce_adj, imp_true_iff, and_true]
    exact fun ha => ⟨G'.edge_vert ha, G'.edge_vert ha.symm⟩

中文:
定理 induce_self_verts
  结论: G'.induce G'.verts = G'
  证明: by
  ext
  · simp
  · constructor <;>
      simp +contextual only [induce_adj, imp_true_iff, and_true]
    exact fun ha => ⟨G'.edge_vert ha, G'.edge_vert ha.symm⟩

Depends on / 依赖: and_true, contextual, edge_vert, ha.symm, imp_true_iff, induce_adj
-/
theorem induce_self_verts : G'.induce G'.verts = G' := by
  ext
  · simp
  · constructor <;>
      simp +contextual only [induce_adj, imp_true_iff, and_true]
    exact fun ha => ⟨G'.edge_vert ha, G'.edge_vert ha.symm⟩

/--
lemma `le_induce_top_verts` / 引理 `le_induce_top_verts`

English:
lemma le_induce_top_verts
  statement: G' <= (⊤ : G.Subgraph).induce G'.verts
  proof: calc G' = G'.induce G'.verts := Subgraph.induce_self_verts.symm
       _ <= (⊤ : G.Subgraph).induce G'.verts := Subgraph.induce_mono_left le_top

中文:
引理 le_induce_top_verts
  结论: G' <= (⊤ : G.Subgraph).induce G'.verts
  证明: calc G' = G'.induce G'.verts := Subgraph.induce_self_verts.symm
       _ <= (⊤ : G.Subgraph).induce G'.verts := Subgraph.induce_mono_left le_top

Depends on / 依赖: G.Subgraph, Subgraph, Subgraph.induce_mono_left, Subgraph.induce_self_verts.symm, induce, induce_mono_left, induce_self_verts, le_top
-/
lemma le_induce_top_verts : G' <= (⊤ : G.Subgraph).induce G'.verts :=
  calc G' = G'.induce G'.verts := Subgraph.induce_self_verts.symm
       _ <= (⊤ : G.Subgraph).induce G'.verts := Subgraph.induce_mono_left le_top

/--
lemma `le_induce_union` / 引理 `le_induce_union`

English:
lemma le_induce_union
  statement: G'.induce s ⊔ G'.induce s' <= G'.induce (s union s')
  proof: by
  constructor
  · simp
  · simp only [sup_adj, induce_adj, Set.mem_union]
    rintro v w (h | h) <;> simp [h]

中文:
引理 le_induce_union
  结论: G'.induce s ⊔ G'.induce s' <= G'.induce (s union s')
  证明: by
  constructor
  · simp
  · simp only [sup_adj, induce_adj, Set.mem_union]
    rintro v w (h | h) <;> simp [h]

Depends on / 依赖: Set.mem_union, induce_adj, mem_union, sup_adj
-/
lemma le_induce_union : G'.induce s ⊔ G'.induce s' <= G'.induce (s union s') := by
  constructor
  · simp
  · simp only [sup_adj, induce_adj, Set.mem_union]
    rintro v w (h | h) <;> simp [h]

/--
lemma `le_induce_union_left` / 引理 `le_induce_union_left`

English:
lemma le_induce_union_left
  statement: G'.induce s <= G'.induce (s union s')
  proof: by
  exact (sup_le_iff.mp le_induce_union).1

中文:
引理 le_induce_union_left
  结论: G'.induce s <= G'.induce (s union s')
  证明: by
  exact (sup_le_iff.mp le_induce_union).1

Depends on / 依赖: le_induce_union, sup_le_iff, sup_le_iff.mp
-/
lemma le_induce_union_left : G'.induce s <= G'.induce (s union s') := by
  exact (sup_le_iff.mp le_induce_union).1

/--
lemma `le_induce_union_right` / 引理 `le_induce_union_right`

English:
lemma le_induce_union_right
  statement: G'.induce s' <= G'.induce (s union s')
  proof: by
  exact (sup_le_iff.mp le_induce_union).2

中文:
引理 le_induce_union_right
  结论: G'.induce s' <= G'.induce (s union s')
  证明: by
  exact (sup_le_iff.mp le_induce_union).2

Depends on / 依赖: le_induce_union, sup_le_iff, sup_le_iff.mp
-/
lemma le_induce_union_right : G'.induce s' <= G'.induce (s union s') := by
  exact (sup_le_iff.mp le_induce_union).2

/--
theorem `singletonSubgraph_eq_induce` / 定理 `singletonSubgraph_eq_induce`

English:
theorem singletonSubgraph_eq_induce
  given: {v : V}
  proof: by
  ext <;> simp +contextual [-Set.bot_eq_empty, Prop.bot_eq_false]

中文:
定理 singletonSubgraph_eq_induce
  条件: {v : V}
  证明: by
  ext <;> simp +contextual [-Set.bot_eq_empty, Prop.bot_eq_false]

Depends on / 依赖: Prop.bot_eq_false, Set.bot_eq_empty, bot_eq_empty, bot_eq_false, contextual
-/
theorem singletonSubgraph_eq_induce {v : V} :
    G.singletonSubgraph v = (⊤ : G.Subgraph).induce {v} := by
  ext <;> simp +contextual [-Set.bot_eq_empty, Prop.bot_eq_false]

/--
theorem `subgraphOfAdj_eq_induce` / 定理 `subgraphOfAdj_eq_induce`

English:
theorem subgraphOfAdj_eq_induce
  given: {v w : V} (hvw : G.Adj v w)
  proof: by
  ext
  · simp
  · constructor
    · intro h
      simp only [subgraphOfAdj_adj, Sym2.eq, Sym2.rel_iff] at h
      obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := h <;> simp [hvw, hvw.symm]
    · intro h
      simp only [induce_adj, Set.mem_insert_iff, Set.mem_singleton_iff, top_adj] at h
      obtain ⟨rfl | r

中文:
定理 subgraphOfAdj_eq_induce
  条件: {v w : V} (hvw : G.Adj v w)
  证明: by
  ext
  · simp
  · constructor
    · intro h
      simp only [subgraphOfAdj_adj, Sym2.eq, Sym2.rel_iff] at h
      obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := h <;> simp [hvw, hvw.symm]
    · intro h
      simp only [induce_adj, Set.mem_insert_iff, Set.mem_singleton_iff, top_adj] at h
      obtain ⟨rfl | r

Depends on / 依赖: Set.mem_insert_iff, Set.mem_singleton_iff, Sym2.eq, Sym2.rel_iff, ha.ne, hvw.symm, induce_adj, mem_insert_iff, mem_singleton_iff, rel_iff, subgraphOfAdj_adj, top_adj
-/
theorem subgraphOfAdj_eq_induce {v w : V} (hvw : G.Adj v w) :
    G.subgraphOfAdj hvw = (⊤ : G.Subgraph).induce {v, w} := by
  ext
  · simp
  · constructor
    · intro h
      simp only [subgraphOfAdj_adj, Sym2.eq, Sym2.rel_iff] at h
      obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := h <;> simp [hvw, hvw.symm]
    · intro h
      simp only [induce_adj, Set.mem_insert_iff, Set.mem_singleton_iff, top_adj] at h
      obtain ⟨rfl | rfl, rfl | rfl, ha⟩ := h <;> first | exact (ha.ne rfl).elim | simp

/--
Instance `instDecidableRel_induce_adj` / 实例 `instDecidableRel_induce_adj`

English:
instance instDecidableRel_induce_adj
  signature: (s : Set V) [forall a, Decidable (a in s)] [DecidableRel G'.Adj]
  body: fun _ _ => instDecidableAnd

中文:
实例 instDecidableRel_induce_adj
  签名: (s : Set V) [对任意 a, Decidable (a in s)] [DecidableRel G'.Adj]
  定义体: fun _ _ => instDecidableAnd

Depends on / 依赖: instDecidableAnd
-/
instance instDecidableRel_induce_adj (s : Set V) [forall a, Decidable (a in s)] [DecidableRel G'.Adj] :
    DecidableRel (G'.induce s).Adj :=
  fun _ _ => instDecidableAnd

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `coeInduceIso` / `coeInduceIso` 的定义

English:
definition coeInduceIso
  signature: (s : Set V) (h : s subseteq G'.verts)
  body: fun ⟨v, hv⟩ => ⟨⟨v, h hv⟩, by simp at hv; aesop⟩
  invFun := fun ⟨v, hv⟩ => ⟨v, hv⟩
  map_rel_iff' := by simp

中文:
定义 coeInduceIso
  签名: (s : Set V) (h : s subseteq G'.verts)
  定义体: fun ⟨v, hv⟩ => ⟨⟨v, h hv⟩, by simp at hv; aesop⟩
  invFun := fun ⟨v, hv⟩ => ⟨v, hv⟩
  map_rel_iff' := by simp
-/
def coeInduceIso (s : Set V) (h : s subseteq G'.verts) :
    (G'.induce s).coe ≃g G'.coe.induce {v : G'.verts | ↑v in s} where
  toFun := fun ⟨v, hv⟩ => ⟨⟨v, h hv⟩, by simp at hv; aesop⟩
  invFun := fun ⟨v, hv⟩ => ⟨v, hv⟩
  map_rel_iff' := by simp

end Induce

/--
Definition of `deleteVerts` / `deleteVerts` 的定义

English:
abbreviation deleteVerts
  signature: (G' : G.Subgraph) (s : Set V)
  body: G'.induce (G'.verts \ s)

中文:
缩写 deleteVerts
  签名: (G' : G.Subgraph) (s : Set V)
  定义体: G'.induce (G'.verts \ s)

Depends on / 依赖: induce
-/
abbrev deleteVerts (G' : G.Subgraph) (s : Set V) : G.Subgraph :=
  G'.induce (G'.verts \ s)

section DeleteVerts

variable {G' : G.Subgraph} {s : Set V}

/--
theorem `deleteVerts_verts` / 定理 `deleteVerts_verts`

English:
theorem deleteVerts_verts
  statement: (G'.deleteVerts s).verts = G'.verts \ s
  proof: rfl

中文:
定理 deleteVerts_verts
  结论: (G'.deleteVerts s).verts = G'.verts \ s
  证明: rfl
-/
theorem deleteVerts_verts : (G'.deleteVerts s).verts = G'.verts \ s :=
  rfl

/--
theorem `deleteVerts_adj` / 定理 `deleteVerts_adj`

English:
theorem deleteVerts_adj
  given: {u v : V}
  proof: by
  simp [and_assoc]

@[simp]

中文:
定理 deleteVerts_adj
  条件: {u v : V}
  证明: by
  simp [and_assoc]

@[simp]

Depends on / 依赖: and_assoc
-/
theorem deleteVerts_adj {u v : V} :
    (G'.deleteVerts s).Adj u v ↔ u in G'.verts ∧ u ∉ s ∧ v in G'.verts ∧ v ∉ s ∧ G'.Adj u v := by
  simp [and_assoc]

@[simp]
/--
theorem `deleteVerts_deleteVerts` / 定理 `deleteVerts_deleteVerts`

English:
theorem deleteVerts_deleteVerts
  given: (s s' : Set V)
  proof: by
  ext <;> simp +contextual [not_or, and_assoc]

@[simp]

中文:
定理 deleteVerts_deleteVerts
  条件: (s s' : Set V)
  证明: by
  ext <;> simp +contextual [not_or, and_assoc]

@[simp]

Depends on / 依赖: and_assoc, contextual, not_or
-/
theorem deleteVerts_deleteVerts (s s' : Set V) :
    (G'.deleteVerts s).deleteVerts s' = G'.deleteVerts (s union s') := by
  ext <;> simp +contextual [not_or, and_assoc]

@[simp]
/--
theorem `deleteVerts_empty` / 定理 `deleteVerts_empty`

English:
theorem deleteVerts_empty
  statement: G'.deleteVerts ∅ = G'
  proof: by
  simp [deleteVerts]

中文:
定理 deleteVerts_empty
  结论: G'.deleteVerts ∅ = G'
  证明: by
  simp [deleteVerts]

Depends on / 依赖: deleteVerts
-/
theorem deleteVerts_empty : G'.deleteVerts ∅ = G' := by
  simp [deleteVerts]

/--
theorem `deleteVerts_le` / 定理 `deleteVerts_le`

English:
theorem deleteVerts_le
  statement: G'.deleteVerts s <= G'
  proof: by
  constructor <;> simp

@[gcongr, mono]

中文:
定理 deleteVerts_le
  结论: G'.deleteVerts s <= G'
  证明: by
  constructor <;> simp

@[gcongr, mono]
-/
theorem deleteVerts_le : G'.deleteVerts s <= G' := by
  constructor <;> simp

@[gcongr, mono]
/--
theorem `deleteVerts_mono` / 定理 `deleteVerts_mono`

English:
theorem deleteVerts_mono
  given: {G' G'' : G.Subgraph} (h : G' <= G'')
  proof: induce_mono h (Set.sdiff_subset_sdiff_left h.1)

中文:
定理 deleteVerts_mono
  条件: {G' G'' : G.Subgraph} (h : G' <= G'')
  证明: induce_mono h (Set.sdiff_subset_sdiff_left h.1)

Depends on / 依赖: Set.sdiff_subset_sdiff_left, induce_mono, sdiff_subset_sdiff_left
-/
theorem deleteVerts_mono {G' G'' : G.Subgraph} (h : G' <= G'') :
    G'.deleteVerts s <= G''.deleteVerts s :=
  induce_mono h (Set.sdiff_subset_sdiff_left h.1)

set_option backward.isDefEq.respectTransparency false in
@[mono]
/--
lemma `deleteVerts_mono'` / 引理 `deleteVerts_mono'`

English:
lemma deleteVerts_mono'
  given: {G' : SimpleGraph V} (u : Set V) (h : G <= G')
  proof: by
  intro v w hvw
  aesop

@[gcongr, mono]

中文:
引理 deleteVerts_mono'
  条件: {G' : SimpleGraph V} (u : Set V) (h : G <= G')
  证明: by
  intro v w hvw
  aesop

@[gcongr, mono]
-/
lemma deleteVerts_mono' {G' : SimpleGraph V} (u : Set V) (h : G <= G') :
    ((⊤ : Subgraph G).deleteVerts u).coe <= ((⊤ : Subgraph G').deleteVerts u).coe := by
  intro v w hvw
  aesop

@[gcongr, mono]
/--
theorem `deleteVerts_anti` / 定理 `deleteVerts_anti`

English:
theorem deleteVerts_anti
  given: {s s' : Set V} (h : s subseteq s')
  statement: G'.deleteVerts s' <= G'.deleteVerts s
  proof: induce_mono (le_refl _) (Set.sdiff_subset_sdiff_right h)

@[simp]

中文:
定理 deleteVerts_anti
  条件: {s s' : Set V} (h : s subseteq s')
  结论: G'.deleteVerts s' <= G'.deleteVerts s
  证明: induce_mono (le_refl _) (Set.sdiff_subset_sdiff_right h)

@[simp]

Depends on / 依赖: Set.sdiff_subset_sdiff_right, induce_mono, le_refl, sdiff_subset_sdiff_right
-/
theorem deleteVerts_anti {s s' : Set V} (h : s subseteq s') : G'.deleteVerts s' <= G'.deleteVerts s :=
  induce_mono (le_refl _) (Set.sdiff_subset_sdiff_right h)

@[simp]
/--
theorem `deleteVerts_inter_verts_left_eq` / 定理 `deleteVerts_inter_verts_left_eq`

English:
theorem deleteVerts_inter_verts_left_eq
  statement: G'.deleteVerts (G'.verts inter s) = G'.deleteVerts s
  proof: by
  ext <;> simp +contextual

@[simp]

中文:
定理 deleteVerts_inter_verts_left_eq
  结论: G'.deleteVerts (G'.verts inter s) = G'.deleteVerts s
  证明: by
  ext <;> simp +contextual

@[simp]

Depends on / 依赖: _le_iff, contextual
-/
theorem deleteVerts_inter_verts_left_eq : G'.deleteVerts (G'.verts inter s) = G'.deleteVerts s := by
  ext <;> simp +contextual

@[simp]
/--
theorem `deleteVerts_inter_verts_set_right_eq` / 定理 `deleteVerts_inter_verts_set_right_eq`

English:
theorem deleteVerts_inter_verts_set_right_eq
  proof: by
  ext <;> simp +contextual

中文:
定理 deleteVerts_inter_verts_set_right_eq
  证明: by
  ext <;> simp +contextual

Depends on / 依赖: _image, _product_left, contextual
-/
theorem deleteVerts_inter_verts_set_right_eq :
    G'.deleteVerts (s inter G'.verts) = G'.deleteVerts s := by
  ext <;> simp +contextual

/--
Instance `instDecidableRel_deleteVerts_adj` / 实例 `instDecidableRel_deleteVerts_adj`

English:
instance instDecidableRel_deleteVerts_adj
  signature: (u : Set V) [r : DecidableRel G.Adj]
  body: fun x y =>
    if h : G.Adj x y
    then
.isTrue SimpleGraph.Subgraph.Adj.coe Subgraph.deleteVerts_adj.mpr
        ⟨by trivial, x.2.2, by trivial, y.2.2, h⟩
    else
.isFalse fun hadj => h Subgraph.coe_adj_sub _ _ _ hadj

中文:
实例 instDecidableRel_deleteVerts_adj
  签名: (u : Set V) [r : DecidableRel G.Adj]
  定义体: fun x y =>
    if h : G.Adj x y
    then
.isTrue SimpleGraph.Subgraph.Adj.coe Subgraph.deleteVerts_adj.mpr
        ⟨by trivial, x.2.2, by trivial, y.2.2, h⟩
    else
.isFalse fun hadj => h Subgraph.coe_adj_sub _ _ _ hadj

Depends on / 依赖: G.Adj, SimpleGraph, SimpleGraph.Subgraph.Adj.coe, Subgraph, Subgraph.coe_adj_sub, Subgraph.deleteVerts_adj.mpr, _image, _product_right, coe_adj_sub, deleteVerts_adj, isFalse, isTrue
-/
instance instDecidableRel_deleteVerts_adj (u : Set V) [r : DecidableRel G.Adj] :
    DecidableRel ((⊤ : G.Subgraph).deleteVerts u).coe.Adj :=
  fun x y =>
    if h : G.Adj x y
    then
.isTrue SimpleGraph.Subgraph.Adj.coe Subgraph.deleteVerts_adj.mpr
        ⟨by trivial, x.2.2, by trivial, y.2.2, h⟩
    else
.isFalse fun hadj => h Subgraph.coe_adj_sub _ _ _ hadj

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `coeDeleteVertsIso` / `coeDeleteVertsIso` 的定义

English:
definition coeDeleteVertsIso
  signature: (s : Set V)
  body: fun ⟨v, hv⟩ => ⟨⟨v, Set.mem_of_mem_inter_left hv⟩, by aesop⟩
  invFun := fun ⟨v, hv⟩ => ⟨v, by simp_all⟩
  map_rel_iff' := by simp

中文:
定义 coeDeleteVertsIso
  签名: (s : Set V)
  定义体: fun ⟨v, hv⟩ => ⟨⟨v, Set.mem_of_mem_inter_left hv⟩, by aesop⟩
  invFun := fun ⟨v, hv⟩ => ⟨v, by simp_all⟩
  map_rel_iff' := by simp

Depends on / 依赖: Set.mem_of_mem_inter_left, mem_of_mem_inter_left
-/
def coeDeleteVertsIso (s : Set V) :
    (G'.deleteVerts s).coe ≃g G'.coe.induce {v : G'.verts | ↑v ∉ s} where
  toFun := fun ⟨v, hv⟩ => ⟨⟨v, Set.mem_of_mem_inter_left hv⟩, by aesop⟩
  invFun := fun ⟨v, hv⟩ => ⟨v, by simp_all⟩
  map_rel_iff' := by simp

end DeleteVerts

end Subgraph

end SimpleGraph
