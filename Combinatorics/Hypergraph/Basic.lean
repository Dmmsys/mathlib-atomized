/-
Copyright (c) 2026 Evan Spotte-Smith, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Evan Spotte-Smith, Bhavik Mehta
-/
module
public import Mathlib.Data.Set.Basic
public import Mathlib.Data.Set.Card

/-!
# Undirected hypergraphs

An *undirected hypergraph* (here abbreviated as *hypergraph*) `H` is a generalization of a graph
(see `Mathlib.Combinatorics.Graph` or `Mathlib.Combinatorics.SimpleGraph`) and consists of a set of
*vertices*, usually denoted `V` or `V(H)`, and a set of *hyperedges*, here called *edges* and
denoted `E` or `E(H)`. In contrast with a graph, where edges are unordered pairs of vertices, in
hypergraphs, edges are unordered sets of vertices; i.e., they are subsets of the vertex set `V`.

A hypergraph where `V = ∅` and `E = ∅` is *empty*, denoted `⊥`. A hypergraph with a nonempty
vertex set (`V ≠ ∅`) and empty edge set is *trivial*. A hypergraph where the edge set is the power
set of the vertex set (or, equivalently, where all possible subsets of the vertex sets are in the
edge set) is *complete*.

If a edge `e` contains only one vertex (i.e., `|e| = 1`), then it is a *loop*.

This module defines `Hypergraph α` for a vertex type `α` (edges are defined as `Set (Set α)`).

## Main definitions

* `Hypergraph α` is the type of undirected hypergraphs with vertices of type `α` and edges of type
  `Set α`. In addition to vertices and hyperedges, a `Hypergraph` must have the property that all
  edges are subsets of the vertex set.

For `H : Hypergraph α`:

* `H.vertexSet` (abbrev. `V(H)`) denotes the vertex set of `H` as a term in `Set α`.
* `H.edgeSet` (abbrev. `E(H)`) denotes the edge set of `H` as a term in `Set (Set α)`. Hyperedges
  must be subsets of `V(H)`.
* `H.Adj x y` means that there exists some edge containing both `x` and `y` (or, in other
  words, `x` and `y` are incident to some shared edge `e`).
* `H.EAdj e f` means that there exists some vertex that is incident to the edges `e` and
  `f : Set α`.

## Implementation details

This implementation is heavily inspired by Peter Nelson and Jun Kwon's `Graph` implementation,
which was in turn inspired by `Matroid`.

Paraphrasing `Mathlib.Combinatorics.Graph.Basic`:
"The main tradeoff is that parts of the API will need to care about whether a term
`x : α` or `e : Set α` is a 'real' vertex or edge of the graph, rather than something outside
the vertex or edge set. This is an issue, but is likely amenable to automation."

Because `edgeSet` is a `Set (Set α)`, rather than a multiset, here we are assuming that
all hypergraphs are *without repeated edge*.

-/

public section

open Set

variable {α β γ : Type*} {x y : α} {e e' f : Set α}

/--
An undirected hypergraph with vertices of type `α` and edges of type `Set α`, as described by vertex
and edge sets `vertexSet : Set α` and `edgeSet : Set (Set α)`.

The requirement `subset_vertexSet_of_mem_edgeSet` ensures that all vertices in edges are part of
`vertexSet`, i.e., all edges are subsets of the `vertexSet`.
-/
@[ext]
/--
Definition of `Hypergraph` / `Hypergraph` 的定义

English:
structure Hypergraph
  parameters: (α : Type*)
  axioms and operations (3):
    - vertexSet : Set α
    - edgeSet : Set (Set α)
    - subset_vertexSet_of_mem_edgeSet' : forall ⦃e⦄, e in edgeSet -> e subseteq vertexSet

中文:
结构 超图
  参数: (α : 类型)
  公理与运算 (3 个):
    - vertexSet : 集合 α
    - edgeSet : 集合 (集合 α)
    - subset_vertexSet_of_mem_edgeSet' : 对任意 ⦃e⦄, e in edgeSet -> e subseteq vertexSet
-/
structure Hypergraph (α : Type*) where
  /-- The vertex set -/
  vertexSet : Set α
  /-- The edge set -/
  edgeSet : Set (Set α)
  /-- All edges must be subsets of the vertex set -/
  subset_vertexSet_of_mem_edgeSet' : forall ⦃e⦄, e in edgeSet -> e subseteq vertexSet

namespace Hypergraph

variable {H : Hypergraph α}

/-! ## Notation -/

/-- `V(H)` denotes the `vertexSet` of a hypergraph `H` -/
scoped notation "V(" H ")" => Hypergraph.vertexSet H

/-- `E(H)` denotes the `edgeSet` of a hypergraph `H` -/
scoped notation "E(" H ")" => Hypergraph.edgeSet H


/-! ## Vertex-Hyperedge Incidence -/

@[simp]
/--
lemma `subset_vertexSet_of_mem_edgeSet` / 引理 `subset_vertexSet_of_mem_edgeSet`

English:
lemma subset_vertexSet_of_mem_edgeSet
  given: (he : e in E(H))
  statement: e subseteq V(H)
  proof: H.subset_vertexSet_of_mem_edgeSet' he

alias _root_.Membership.mem.subset_vertexSet := subset_vertexSet_of_mem_edgeSet

中文:
引理 subset_vertexSet_of_mem_edgeSet
  条件: (he : e in E(H))
  结论: e subseteq V(H)
  证明: H.subset_vertexSet_of_mem_edgeSet' he

alias _root_.Membership.mem.subset_vertexSet := subset_vertexSet_of_mem_edgeSet

Depends on / 依赖: H.subset_vertexSet_of_mem_edgeSet, subset_vertexSet_of_mem_edgeSet
-/
lemma subset_vertexSet_of_mem_edgeSet (he : e in E(H)) : e subseteq V(H) :=
  H.subset_vertexSet_of_mem_edgeSet' he

alias _root_.Membership.mem.subset_vertexSet := subset_vertexSet_of_mem_edgeSet

/--
lemma `edgeSet_subset_powerset_vertexSet` / 引理 `edgeSet_subset_powerset_vertexSet`

English:
lemma edgeSet_subset_powerset_vertexSet
  given: {H : Hypergraph α}
  statement: E(H) subseteq V(H).powerset
  proof: fun _ => subset_vertexSet_of_mem_edgeSet

中文:
引理 edgeSet_subset_powerset_vertexSet
  条件: {H : 超图 α}
  结论: E(H) subseteq V(H).powerset
  证明: fun _ => subset_vertexSet_of_mem_edgeSet

Depends on / 依赖: Nonempty, subset_vertexSet_of_mem_edgeSet
-/
lemma edgeSet_subset_powerset_vertexSet {H : Hypergraph α} : E(H) subseteq V(H).powerset :=
  fun _ => subset_vertexSet_of_mem_edgeSet

/--
lemma `mem_vertexSet_of_mem_edgeSet` / 引理 `mem_vertexSet_of_mem_edgeSet`

English:
lemma mem_vertexSet_of_mem_edgeSet
  given: (he : e in E(H)) (hx : x in e)
  statement: x in V(H)
  proof: H.subset_vertexSet_of_mem_edgeSet he hx

中文:
引理 mem_vertexSet_of_mem_edgeSet
  条件: (he : e in E(H)) (hx : x in e)
  结论: x in V(H)
  证明: H.subset_vertexSet_of_mem_edgeSet he hx

Depends on / 依赖: H.subset_vertexSet_of_mem_edgeSet, subset_vertexSet_of_mem_edgeSet
-/
lemma mem_vertexSet_of_mem_edgeSet (he : e in E(H)) (hx : x in e) : x in V(H) :=
  H.subset_vertexSet_of_mem_edgeSet he hx

/--
lemma `edgeSet.ext_iff` / 引理 `edgeSet.ext_iff`

English:
lemma edgeSet.ext_iff
  given: (he : e in E(H)) (he' : e' in E(H))
  statement: e = e' ↔ forall x in V(H), x in e ↔ x in e'
  proof: by
  grind [he.subset_vertexSet, he'.subset_vertexSet]

中文:
引理 edgeSet.ext_iff
  条件: (he : e in E(H)) (he' : e' in E(H))
  结论: e = e' ↔ 对任意 x in V(H), x in e ↔ x in e'
  证明: by
  grind [he.subset_vertexSet, he'.subset_vertexSet]

Depends on / 依赖: he.subset_vertexSet, subset_vertexSet
-/
lemma edgeSet.ext_iff (he : e in E(H)) (he' : e' in E(H)) : e = e' ↔ forall x in V(H), x in e ↔ x in e' := by
  grind [he.subset_vertexSet, he'.subset_vertexSet]

/--
lemma `sUnion_edgeSet_subset_vertexSet` / 引理 `sUnion_edgeSet_subset_vertexSet`

English:
lemma sUnion_edgeSet_subset_vertexSet
  statement: ⋃₀ E(H) subseteq V(H)
  proof: subset_powerset_iff.mp edgeSet_subset_powerset_vertexSet

中文:
引理 sUnion_edgeSet_subset_vertexSet
  结论: ⋃₀ E(H) subseteq V(H)
  证明: subset_powerset_iff.mp edgeSet_subset_powerset_vertexSet

Depends on / 依赖: edgeSet_subset_powerset_vertexSet, subset_powerset_iff, subset_powerset_iff.mp
-/
lemma sUnion_edgeSet_subset_vertexSet : ⋃₀ E(H) subseteq V(H) :=
  subset_powerset_iff.mp edgeSet_subset_powerset_vertexSet

/-! ## Vertex and Hyperedge Adjacency -/

/--
Predicate for adjacency. Two vertices `x` and `y` are adjacent if there is some edge `e ∈ E(H)`
where `x` and `y` are both incident to `e`.

Note that we do not need to explicitly check that `x, y ∈ V(H)` here because a vertex that is not in
the vertex set cannot be incident to any edge.
-/
@[expose]
/--
Definition of `Adj` / `Adj` 的定义

English:
definition Adj
  signature: (H : Hypergraph α) (x : α) (y : α)
  body: exists e in E(H), x in e ∧ y in e

中文:
定义 伴随
  签名: (H : 超图 α) (x : α) (y : α)
  定义体: exists e in E(H), x in e ∧ y in e
-/
def Adj (H : Hypergraph α) (x : α) (y : α) : Prop :=
  exists e in E(H), x in e ∧ y in e

/--
lemma `Adj.symm` / 引理 `Adj.symm`

English:
lemma Adj.symm
  given: (h : H.Adj x y)
  statement: H.Adj y x
  proof: by grind [Adj]

中文:
引理 伴随.symm
  条件: (h : H.伴随 x y)
  结论: H.伴随 y x
  证明: by grind [Adj]
-/
lemma Adj.symm (h : H.Adj x y) : H.Adj y x := by grind [Adj]

/--
lemma `adj_comm` / 引理 `adj_comm`

English:
lemma adj_comm
  given: (x y : α)
  statement: H.Adj x y ↔ H.Adj y x
  proof: ⟨.symm, .symm⟩

中文:
引理 adj_comm
  条件: (x y : α)
  结论: H.伴随 x y ↔ H.伴随 y x
  证明: ⟨.symm, .symm⟩
-/
lemma adj_comm (x y : α) : H.Adj x y ↔ H.Adj y x := ⟨.symm, .symm⟩

/--
Predicate for edge adjacency. Analogous to `Hypergraph.Adj`, edges `e` and `f` are
adjacent if there is some vertex `x ∈ V(H)` where `x` is incident to both `e` and `f`.
-/
@[expose]
/--
Definition of `EAdj` / `EAdj` 的定义

English:
definition EAdj
  signature: (H : Hypergraph α) (e : Set α) (f : Set α)
  body: e in E(H) ∧ f in E(H) ∧ exists x, x in e ∧ x in f

中文:
定义 EAdj
  签名: (H : 超图 α) (e : 集合 α) (f : 集合 α)
  定义体: e in E(H) ∧ f in E(H) ∧ exists x, x in e ∧ x in f
-/
def EAdj (H : Hypergraph α) (e : Set α) (f : Set α) : Prop :=
  e in E(H) ∧ f in E(H) ∧ exists x, x in e ∧ x in f

/--
lemma `EAdj.exists_vertex` / 引理 `EAdj.exists_vertex`

English:
lemma EAdj.exists_vertex
  given: (h : H.EAdj e f)
  statement: exists x in V(H), x in e ∧ x in f
  proof: by
  obtain ⟨x, hx⟩ := h.2.2
  exact ⟨x, mem_vertexSet_of_mem_edgeSet h.1 hx.1, hx⟩

中文:
引理 EAdj.存在_vertex
  条件: (h : H.EAdj e f)
  结论: 存在 x in V(H), x in e ∧ x in f
  证明: by
  obtain ⟨x, hx⟩ := h.2.2
  exact ⟨x, mem_vertexSet_of_mem_edgeSet h.1 hx.1, hx⟩

Depends on / 依赖: mem_vertexSet_of_mem_edgeSet
-/
lemma EAdj.exists_vertex (h : H.EAdj e f) : exists x in V(H), x in e ∧ x in f := by
  obtain ⟨x, hx⟩ := h.2.2
  exact ⟨x, mem_vertexSet_of_mem_edgeSet h.1 hx.1, hx⟩

/--
lemma `EAdj.symm` / 引理 `EAdj.symm`

English:
lemma EAdj.symm
  given: (h : H.EAdj e f)
  statement: H.EAdj f e
  proof: by grind [EAdj]

中文:
引理 EAdj.symm
  条件: (h : H.EAdj e f)
  结论: H.EAdj f e
  证明: by grind [EAdj]
-/
lemma EAdj.symm (h : H.EAdj e f) : H.EAdj f e := by grind [EAdj]

/--
lemma `EAdj.inter_nonempty` / 引理 `EAdj.inter_nonempty`

English:
lemma EAdj.inter_nonempty
  given: (hef : H.EAdj e f)
  statement: (e inter f).Nonempty
  proof: Set.inter_nonempty.mpr hef.2.2

中文:
引理 EAdj.inter_nonempty
  条件: (hef : H.EAdj e f)
  结论: (e inter f).非空
  证明: Set.inter_nonempty.mpr hef.2.2

Depends on / 依赖: Set.inter_nonempty.mpr, inter_nonempty
-/
lemma EAdj.inter_nonempty (hef : H.EAdj e f) : (e inter f).Nonempty :=
  Set.inter_nonempty.mpr hef.2.2

/--
lemma `eAdj_comm` / 引理 `eAdj_comm`

English:
lemma eAdj_comm
  given: (e f)
  statement: H.EAdj e f ↔ H.EAdj f e
  proof: ⟨.symm, .symm⟩

中文:
引理 eAdj_comm
  条件: (e f)
  结论: H.EAdj e f ↔ H.EAdj f e
  证明: ⟨.symm, .symm⟩
-/
lemma eAdj_comm (e f) : H.EAdj e f ↔ H.EAdj f e := ⟨.symm, .symm⟩

/-! ## Basic Hypergraph Definitions & Predicates-/

/-- The *image* of a hypergraph `H : Hypergraph α` under a function `f : α → β` is the hypergraph
`Hᶠ : Hypergraph β` where the vertex set of `Hᶠ` is the image of `V(H)` under `f` and the edge set
of `Hᶠ` is the set of images of the edges (subsets of vertices) in `E(H)`. -/
@[simps, expose]
/--
Definition of `image` / `image` 的定义

English:
definition image
  signature: (H : Hypergraph α) (f : α -> β)
  body: V(H).image f
  edgeSet := E(H).image (Set.image f)
  subset_vertexSet_of_mem_edgeSet' := by
    rintro - ⟨e, he, rfl⟩
    exact image_mono he.subset_vertexSet

中文:
定义 像
  签名: (H : 超图 α) (f : α -> β)
  定义体: V(H).image f
  edgeSet := E(H).image (Set.image f)
  subset_vertexSet_of_mem_edgeSet' := by
    rintro - ⟨e, he, rfl⟩
    exact image_mono he.subset_vertexSet

Depends on / 依赖: Erased
-/
protected def image (H : Hypergraph α) (f : α -> β) : Hypergraph β where
  vertexSet := V(H).image f
  edgeSet := E(H).image (Set.image f)
  subset_vertexSet_of_mem_edgeSet' := by
    rintro - ⟨e, he, rfl⟩
    exact image_mono he.subset_vertexSet

/--
lemma `mem_edgeSet_image` / 引理 `mem_edgeSet_image`

English:
lemma mem_edgeSet_image
  given: {f : α -> β} {e : Set β}
  statement: e in E(H.image f) ↔ exists e' in E(H), f '' e' = e
  proof: .rfl

中文:
引理 mem_edgeSet_image
  条件: {f : α -> β} {e : 集合 β}
  结论: e in E(H.像 f) ↔ 存在 e' in E(H), f '' e' = e
  证明: .rfl

Depends on / 依赖: Erased
-/
lemma mem_edgeSet_image {f : α -> β} {e : Set β} : e in E(H.image f) ↔ exists e' in E(H), f '' e' = e :=
  .rfl

/--
lemma `image_mem_edgeSet_image` / 引理 `image_mem_edgeSet_image`

English:
lemma image_mem_edgeSet_image
  given: {f : α -> β} (he : e in E(H))
  statement: e.image f in E(H.image f)
  proof: mem_image_of_mem _ he

中文:
引理 image_mem_edgeSet_image
  条件: {f : α -> β} (he : e in E(H))
  结论: e.像 f in E(H.像 f)
  证明: mem_image_of_mem _ he

Depends on / 依赖: mem_image_of_mem
-/
lemma image_mem_edgeSet_image {f : α -> β} (he : e in E(H)) : e.image f in E(H.image f) :=
  mem_image_of_mem _ he

/--
lemma `image_image` / 引理 `image_image`

English:
lemma image_image
  given: {f : α -> β} {g : β -> γ} (H : Hypergraph α)
  proof: by
  ext <;> simp [Set.image_image]

中文:
引理 image_image
  条件: {f : α -> β} {g : β -> γ} (H : 超图 α)
  证明: by
  ext <;> simp [Set.image_image]

Depends on / 依赖: Set.image_image, image_image
-/
lemma image_image {f : α -> β} {g : β -> γ} (H : Hypergraph α) :
    (H.image f).image g = H.image (g ∘ f) := by
  ext <;> simp [Set.image_image]

/-- A vertex is isolated if it is not incident to any edges (including loops). -/
@[expose]
/--
Definition of `IsIsolated` / `IsIsolated` 的定义

English:
definition IsIsolated
  signature: (H : Hypergraph α) (x : α)
  body: forall e in E(H), x ∉ e

中文:
定义 IsIsolated
  签名: (H : 超图 α) (x : α)
  定义体: forall e in E(H), x ∉ e

Depends on / 依赖: choice
-/
def IsIsolated (H : Hypergraph α) (x : α) : Prop := forall e in E(H), x ∉ e

/--
lemma `sUnion_edgeSet_eq_vertexSet_iff_all_vertex_not_isolated` / 引理 `sUnion_edgeSet_eq_vertexSet_iff_all_vertex_not_isolated`

English:
lemma sUnion_edgeSet_eq_vertexSet_iff_all_vertex_not_isolated
  proof: by
  grind [IsIsolated, mem_vertexSet_of_mem_edgeSet]

中文:
引理 sUnion_edgeSet_eq_vertexSet_iff_all_vertex_not_isolated
  证明: by
  grind [IsIsolated, mem_vertexSet_of_mem_edgeSet]

Depends on / 依赖: IsIsolated, mem_vertexSet_of_mem_edgeSet
-/
lemma sUnion_edgeSet_eq_vertexSet_iff_all_vertex_not_isolated :
    ⋃₀ E(H) = V(H) ↔ forall x in V(H), ¬IsIsolated H x := by
  grind [IsIsolated, mem_vertexSet_of_mem_edgeSet]

/-- A loop is an edge whose associated vertex subset consists of a single vertex. -/
@[expose]
/--
Definition of `IsLoop` / `IsLoop` 的定义

English:
definition IsLoop
  signature: (H : Hypergraph α) (e : Set α)
  body: e in E(H) ∧ exists x, e = {x}

中文:
定义 IsLoop
  签名: (H : 超图 α) (e : 集合 α)
  定义体: e in E(H) ∧ exists x, e = {x}
-/
def IsLoop (H : Hypergraph α) (e : Set α) : Prop := e in E(H) ∧ exists x, e = {x}

/--
lemma `isLoop_iff_mem_edgeSet_and_singleton` / 引理 `isLoop_iff_mem_edgeSet_and_singleton`

English:
lemma isLoop_iff_mem_edgeSet_and_singleton
  statement: H.IsLoop e ↔ (e in E(H) ∧ exists x, e = {x})
  proof: .rfl

中文:
引理 isLoop_iff_mem_edgeSet_and_singleton
  结论: H.IsLoop e ↔ (e in E(H) ∧ 存在 x, e = {x})
  证明: .rfl
-/
lemma isLoop_iff_mem_edgeSet_and_singleton : H.IsLoop e ↔ (e in E(H) ∧ exists x, e = {x}) := .rfl

/--
lemma `isLoop_iff_mem_and_ncard_one` / 引理 `isLoop_iff_mem_and_ncard_one`

English:
lemma isLoop_iff_mem_and_ncard_one
  statement: H.IsLoop e ↔ (e in E(H) ∧ Set.ncard e = 1)
  proof: by
  grind [IsLoop, ncard_eq_one, mem_vertexSet_of_mem_edgeSet]

中文:
引理 isLoop_iff_mem_and_ncard_one
  结论: H.IsLoop e ↔ (e in E(H) ∧ 集合.ncard e = 1)
  证明: by
  grind [IsLoop, ncard_eq_one, mem_vertexSet_of_mem_edgeSet]

Depends on / 依赖: IsLoop, mem_vertexSet_of_mem_edgeSet, ncard_eq_one
-/
lemma isLoop_iff_mem_and_ncard_one : H.IsLoop e ↔ (e in E(H) ∧ Set.ncard e = 1) := by
  grind [IsLoop, ncard_eq_one, mem_vertexSet_of_mem_edgeSet]

/--
lemma `IsLoop.ncard_one` / 引理 `IsLoop.ncard_one`

English:
lemma IsLoop.ncard_one
  given: (h : H.IsLoop e)
  statement: Set.ncard e = 1
  proof: (isLoop_iff_mem_and_ncard_one.mp h).2

中文:
引理 IsLoop.ncard_one
  条件: (h : H.IsLoop e)
  结论: 集合.ncard e = 1
  证明: (isLoop_iff_mem_and_ncard_one.mp h).2

Depends on / 依赖: isLoop_iff_mem_and_ncard_one, isLoop_iff_mem_and_ncard_one.mp
-/
lemma IsLoop.ncard_one (h : H.IsLoop e) : Set.ncard e = 1 := (isLoop_iff_mem_and_ncard_one.mp h).2

/-- A hypergraph is nonempty if it has at least one vertex or at least one edge. -/
@[expose]
/--
Definition of `IsNonempty` / `IsNonempty` 的定义

English:
definition IsNonempty
  signature: (H : Hypergraph α)
  body: V(H).Nonempty ∨ E(H).Nonempty

中文:
定义 IsNonempty
  签名: (H : 超图 α)
  定义体: V(H).Nonempty ∨ E(H).Nonempty

Depends on / 依赖: Nonempty
-/
def IsNonempty (H : Hypergraph α) : Prop := V(H).Nonempty ∨ E(H).Nonempty

/-- The empty hypergraph (bottom) on a type. -/
@[simps]
instance (α : Type*) : Bot (Hypergraph α) where
  bot.vertexSet := ∅
  bot.edgeSet := ∅
  bot.subset_vertexSet_of_mem_edgeSet' := by simp

@[simp]
/--
lemma `IsNonempty.of_nonempty_vertexSet` / 引理 `IsNonempty.of_nonempty_vertexSet`

English:
lemma IsNonempty.of_nonempty_vertexSet
  given: (hV : V(H).Nonempty)
  statement: H.IsNonempty
  proof: .inl hV

@[simp]

中文:
引理 IsNonempty.of_nonempty_vertexSet
  条件: (hV : V(H).非空)
  结论: H.IsNonempty
  证明: .inl hV

@[simp]
-/
lemma IsNonempty.of_nonempty_vertexSet (hV : V(H).Nonempty) : H.IsNonempty :=
  .inl hV

@[simp]
/--
lemma `IsNonempty.of_nonempty_edgeSet` / 引理 `IsNonempty.of_nonempty_edgeSet`

English:
lemma IsNonempty.of_nonempty_edgeSet
  given: (hE : E(H).Nonempty)
  statement: H.IsNonempty
  proof: .inr hE

@[simp]

中文:
引理 IsNonempty.of_nonempty_edgeSet
  条件: (hE : E(H).非空)
  结论: H.IsNonempty
  证明: .inr hE

@[simp]
-/
lemma IsNonempty.of_nonempty_edgeSet (hE : E(H).Nonempty) : H.IsNonempty :=
  .inr hE

@[simp]
/--
theorem `ne_bot_iff` / 定理 `ne_bot_iff`

English:
theorem ne_bot_iff
  statement: H != ⊥ ↔ H.IsNonempty
  proof: by
  simp [IsNonempty, Set.nonempty_iff_ne_empty, Hypergraph.ext_iff]
  grind [bot_vertexSet, bot_edgeSet]

alias ⟨_, IsNonempty.ne_bot⟩ := ne_bot_iff

@[simp]

中文:
定理 ne_bot_iff
  结论: H != ⊥ ↔ H.IsNonempty
  证明: by
  simp [IsNonempty, Set.nonempty_iff_ne_empty, Hypergraph.ext_iff]
  grind [bot_vertexSet, bot_edgeSet]

alias ⟨_, IsNonempty.ne_bot⟩ := ne_bot_iff

@[simp]

Depends on / 依赖: Hypergraph, Hypergraph.ext_iff, IsNonempty, Set.nonempty_iff_ne_empty, bot_edgeSet, bot_vertexSet, ext_iff, nonempty_iff_ne_empty
-/
theorem ne_bot_iff : H != ⊥ ↔ H.IsNonempty := by
  simp [IsNonempty, Set.nonempty_iff_ne_empty, Hypergraph.ext_iff]
  grind [bot_vertexSet, bot_edgeSet]

alias ⟨_, IsNonempty.ne_bot⟩ := ne_bot_iff

@[simp]
/--
theorem `not_isNonempty_iff` / 定理 `not_isNonempty_iff`

English:
theorem not_isNonempty_iff
  statement: ¬H.IsNonempty ↔ H = ⊥
  proof: not_iff_comm.mp ne_bot_iff

中文:
定理 not_isNonempty_iff
  结论: ¬H.IsNonempty ↔ H = ⊥
  证明: not_iff_comm.mp ne_bot_iff

Depends on / 依赖: ne_bot_iff, not_iff_comm, not_iff_comm.mp
-/
theorem not_isNonempty_iff : ¬H.IsNonempty ↔ H = ⊥ :=
  not_iff_comm.mp ne_bot_iff

variable (H) in
/--
lemma `eq_bot_or_isNonempty` / 引理 `eq_bot_or_isNonempty`

English:
lemma eq_bot_or_isNonempty
  statement: H = ⊥ ∨ H.IsNonempty
  proof: by
  have h : (V(H) = ∅ ∧ E(H) = ∅) ∨ (V(H).Nonempty ∨ E(H).Nonempty) := by grind [Set.Nonempty]
  cases h with
  | inl empty => (
    left
    apply Hypergraph.ext empty.1 empty.2
  )
  | inr nonempty => (
    right
    grind [IsNonempty]
  )

中文:
引理 eq_bot_or_isNonempty
  结论: H = ⊥ ∨ H.IsNonempty
  证明: by
  have h : (V(H) = ∅ ∧ E(H) = ∅) ∨ (V(H).Nonempty ∨ E(H).Nonempty) := by grind [Set.Nonempty]
  cases h with
  | inl empty => (
    left
    apply Hypergraph.ext empty.1 empty.2
  )
  | inr nonempty => (
    right
    grind [IsNonempty]
  )

Depends on / 依赖: Hypergraph, Hypergraph.ext, IsNonempty, Nonempty, Set.Nonempty, nonempty
-/
lemma eq_bot_or_isNonempty : H = ⊥ ∨ H.IsNonempty := by
  have h : (V(H) = ∅ ∧ E(H) = ∅) ∨ (V(H).Nonempty ∨ E(H).Nonempty) := by grind [Set.Nonempty]
  cases h with
  | inl empty => (
    left
    apply Hypergraph.ext empty.1 empty.2
  )
  | inr nonempty => (
    right
    grind [IsNonempty]
  )

/-- A hypergraph is trivial if it has at least one vertex but no edges. -/
@[expose]
/--
Definition of `IsTrivial` / `IsTrivial` 的定义

English:
definition IsTrivial
  signature: (H : Hypergraph α)
  body: Set.Nonempty V(H) ∧ E(H) = ∅

中文:
定义 是平凡
  签名: (H : 超图 α)
  定义体: Set.Nonempty V(H) ∧ E(H) = ∅

Depends on / 依赖: Nonempty, Set.Nonempty
-/
def IsTrivial (H : Hypergraph α) : Prop := Set.Nonempty V(H) ∧ E(H) = ∅

/-- The trivial hypergraph with a given vertex set is defined by having no edges on that vertex
set. -/
@[simps, expose]
/--
Definition of `trivialOn` / `trivialOn` 的定义

English:
definition trivialOn
  signature: (f : Set α)
  body: f
  edgeSet := ∅
  subset_vertexSet_of_mem_edgeSet' := by simp

中文:
定义 trivialOn
  签名: (f : 集合 α)
  定义体: f
  edgeSet := ∅
  subset_vertexSet_of_mem_edgeSet' := by simp
-/
def trivialOn (f : Set α) : Hypergraph α where
  vertexSet := f
  edgeSet := ∅
  subset_vertexSet_of_mem_edgeSet' := by simp

/--
lemma `IsTrivial.trivialOn` / 引理 `IsTrivial.trivialOn`

English:
lemma IsTrivial.trivialOn
  given: (hf : Set.Nonempty f)
  proof: by
  grind [trivialOn, IsTrivial]

中文:
引理 是平凡.trivialOn
  条件: (hf : 集合.非空 f)
  证明: by
  grind [trivialOn, IsTrivial]

Depends on / 依赖: IsTrivial, trivialOn
-/
lemma IsTrivial.trivialOn (hf : Set.Nonempty f) :
    IsTrivial (trivialOn f) := by
  grind [trivialOn, IsTrivial]

/--
lemma `IsTrivial.isNonempty` / 引理 `IsTrivial.isNonempty`

English:
lemma IsTrivial.isNonempty
  given: (h : IsTrivial H)
  statement: IsNonempty H
  proof: by
  grind [IsNonempty, IsTrivial, Set.nonempty_iff_ne_empty]

中文:
引理 是平凡.isNonempty
  条件: (h : 是平凡 H)
  结论: IsNonempty H
  证明: by
  grind [IsNonempty, IsTrivial, Set.nonempty_iff_ne_empty]

Depends on / 依赖: IsNonempty, IsTrivial, Set.nonempty_iff_ne_empty, nonempty_iff_ne_empty
-/
lemma IsTrivial.isNonempty (h : IsTrivial H) : IsNonempty H := by
  grind [IsNonempty, IsTrivial, Set.nonempty_iff_ne_empty]

/--
lemma `IsTrivial.not_mem_edgeSet` / 引理 `IsTrivial.not_mem_edgeSet`

English:
lemma IsTrivial.not_mem_edgeSet
  given: (h : H.IsTrivial)
  statement: e ∉ E(H)
  proof: by grind [IsTrivial]

中文:
引理 是平凡.not_mem_edgeSet
  条件: (h : H.是平凡)
  结论: e ∉ E(H)
  证明: by grind [IsTrivial]

Depends on / 依赖: IsTrivial
-/
lemma IsTrivial.not_mem_edgeSet (h : H.IsTrivial) : e ∉ E(H) := by grind [IsTrivial]

/-- A hypergraph is complete if every subset of the vertex set is in the edge set. -/
@[expose]
/--
Definition of `IsComplete` / `IsComplete` 的定义

English:
definition IsComplete
  signature: (H : Hypergraph α)
  body: forall e subseteq V(H), e in E(H)

中文:
定义 是完备
  签名: (H : 超图 α)
  定义体: forall e subseteq V(H), e in E(H)

Depends on / 依赖: subseteq
-/
def IsComplete (H : Hypergraph α) : Prop := forall e subseteq V(H), e in E(H)

/-- The complete hypergraph with a given vertex set, which has each subset of the vertex set as an
edge. -/
@[simps, expose]
/--
Definition of `completeOn` / `completeOn` 的定义

English:
definition completeOn
  signature: (f : Set α)
  body: f
  edgeSet := 𝒫 f
  subset_vertexSet_of_mem_edgeSet' := by simp

中文:
定义 completeOn
  签名: (f : 集合 α)
  定义体: f
  edgeSet := 𝒫 f
  subset_vertexSet_of_mem_edgeSet' := by simp
-/
def completeOn (f : Set α) : Hypergraph α where
  vertexSet := f
  edgeSet := 𝒫 f
  subset_vertexSet_of_mem_edgeSet' := by simp

/--
lemma `mem_completeOn` / 引理 `mem_completeOn`

English:
lemma mem_completeOn
  statement: e in E(completeOn f) ↔ e subseteq f
  proof: by simp

中文:
引理 mem_completeOn
  结论: e in E(completeOn f) ↔ e subseteq f
  证明: by simp
-/
lemma mem_completeOn : e in E(completeOn f) ↔ e subseteq f := by simp

/--
lemma `IsComplete.mem_iff` / 引理 `IsComplete.mem_iff`

English:
lemma IsComplete.mem_iff
  given: (h : H.IsComplete)
  statement: e in E(H) ↔ e subseteq V(H)
  proof: by
  grind [IsComplete, subset_vertexSet_of_mem_edgeSet]

中文:
引理 是完备.mem_iff
  条件: (h : H.是完备)
  结论: e in E(H) ↔ e subseteq V(H)
  证明: by
  grind [IsComplete, subset_vertexSet_of_mem_edgeSet]

Depends on / 依赖: IsComplete, subset_vertexSet_of_mem_edgeSet
-/
lemma IsComplete.mem_iff (h : H.IsComplete) : e in E(H) ↔ e subseteq V(H) := by
  grind [IsComplete, subset_vertexSet_of_mem_edgeSet]

/--
lemma `IsComplete.completeOn` / 引理 `IsComplete.completeOn`

English:
lemma IsComplete.completeOn
  given: (f : Set α)
  statement: (completeOn f).IsComplete
  proof: fun _ a => a

中文:
引理 是完备.completeOn
  条件: (f : 集合 α)
  结论: (completeOn f).是完备
  证明: fun _ a => a
-/
lemma IsComplete.completeOn (f : Set α) : (completeOn f).IsComplete := fun _ a => a

/--
lemma `IsComplete.isNonempty` / 引理 `IsComplete.isNonempty`

English:
lemma IsComplete.isNonempty
  given: (h : H.IsComplete)
  statement: H.IsNonempty
  proof: Or.inr ⟨∅, h ∅ (Set.empty_subset _)⟩

中文:
引理 是完备.isNonempty
  条件: (h : H.是完备)
  结论: H.IsNonempty
  证明: Or.inr ⟨∅, h ∅ (Set.empty_subset _)⟩

Depends on / 依赖: Or.inr, Set.empty_subset, empty_subset
-/
lemma IsComplete.isNonempty (h : H.IsComplete) : H.IsNonempty :=
  Or.inr ⟨∅, h ∅ (Set.empty_subset _)⟩

/--
lemma `IsComplete.not_isTrivial` / 引理 `IsComplete.not_isTrivial`

English:
lemma IsComplete.not_isTrivial
  given: (h : H.IsComplete)
  statement: ¬ H.IsTrivial
  proof: by
  intro hH
  exact hH.not_mem_edgeSet (h ∅ (Set.empty_subset _))

中文:
引理 是完备.not_isTrivial
  条件: (h : H.是完备)
  结论: ¬ H.是平凡
  证明: by
  intro hH
  exact hH.not_mem_edgeSet (h ∅ (Set.empty_subset _))

Depends on / 依赖: Set.empty_subset, empty_subset, hH.not_mem_edgeSet, not_mem_edgeSet
-/
lemma IsComplete.not_isTrivial (h : H.IsComplete) : ¬ H.IsTrivial := by
  intro hH
  exact hH.not_mem_edgeSet (h ∅ (Set.empty_subset _))

/--
lemma `not_isTrivial_completeOn` / 引理 `not_isTrivial_completeOn`

English:
lemma not_isTrivial_completeOn
  given: (f : Set α)
  statement: ¬ (completeOn f).IsTrivial
  proof: (IsComplete.completeOn f).not_isTrivial

中文:
引理 not_isTrivial_completeOn
  条件: (f : 集合 α)
  结论: ¬ (completeOn f).是平凡
  证明: (IsComplete.completeOn f).not_isTrivial

Depends on / 依赖: IsComplete, IsComplete.completeOn, completeOn, not_isTrivial
-/
lemma not_isTrivial_completeOn (f : Set α) : ¬ (completeOn f).IsTrivial :=
  (IsComplete.completeOn f).not_isTrivial

end Hypergraph
