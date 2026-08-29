/-
Copyright (c) 2026 Jun Kwon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Kwon, Peter Nelson
-/
module

public import Mathlib.Combinatorics.Graph.Subgraph
public import Mathlib.Combinatorics.SimpleGraph.Maps

/-!
# Simple graphs

This file defines two type classes for graphs `Graph α β`: `Loopless` and `Simple`.

## Main definitions
- `Loopless`: a graph is loopless if it has no loops
- `Simple`: a graph is simple if it has no multiple edges between the same pair of vertices
- `toSimpleGraph`: a function that constructs a `SimpleGraph V(G)` from a Graph `G`
- `ofSimpleGraph`: a function that constructs a `Graph α (Sym2 α)` from a `SimpleGraph α`

TODO: Show `ofSimpleGraph (toSimpleGraph G)` is isomorphic to `G` when isomorphism on `Graph` is
defined.
-/

public section

variable {α β : Type*} {G H : Graph α β} {u v : α} {e f : β} {X Y : Set α}

open Set SimpleGraph

namespace Graph

section Loopless

/-- A loopless graph is one where the ends of every edge are distinct. -/
@[mk_iff]
/--
Definition of `Loopless` / `Loopless` 的定义

English:
class Loopless
  parameters: (G : Graph α β)
  axioms and operations (1):
    - not_isLoopAt : forall e x, ¬ G.IsLoopAt e x

中文:
类 无环
  参数: (G : 图 α β)
  公理与运算 (1 个):
    - not_isLoopAt : 对任意 e x, ¬ G.IsLoopAt e x

Depends on / 依赖: Bitraversable, Bitraversable.isLawfulTraversable, LawfulBitraversable, isLawfulTraversable
-/
protected class Loopless (G : Graph α β) : Prop where
  not_isLoopAt : forall e x, ¬ G.IsLoopAt e x

@[simp]
/--
lemma `not_isLoopAt` / 引理 `not_isLoopAt`

English:
lemma not_isLoopAt
  given: (G : Graph α β) [G.Loopless] (e : β) (x : α)
  statement: ¬ G.IsLoopAt e x
  proof: Loopless.not_isLoopAt e x

中文:
引理 not_isLoopAt
  条件: (G : 图 α β) [G.无环] (e : β) (x : α)
  结论: ¬ G.IsLoopAt e x
  证明: Loopless.not_isLoopAt e x

Depends on / 依赖: Loopless, Loopless.not_isLoopAt, not_isLoopAt
-/
lemma not_isLoopAt (G : Graph α β) [G.Loopless] (e : β) (x : α) : ¬ G.IsLoopAt e x :=
  Loopless.not_isLoopAt e x

/--
lemma `not_adj_self` / 引理 `not_adj_self`

English:
lemma not_adj_self
  given: (G : Graph α β) [G.Loopless] (x : α)
  statement: ¬ G.Adj x x
  proof: fun ⟨e, he⟩ => Loopless.not_isLoopAt e x he

中文:
引理 not_adj_self
  条件: (G : 图 α β) [G.无环] (x : α)
  结论: ¬ G.伴随 x x
  证明: fun ⟨e, he⟩ => Loopless.not_isLoopAt e x he

Depends on / 依赖: Loopless, Loopless.not_isLoopAt, not_isLoopAt
-/
lemma not_adj_self (G : Graph α β) [G.Loopless] (x : α) : ¬ G.Adj x x :=
  fun ⟨e, he⟩ => Loopless.not_isLoopAt e x he

/--
lemma `Adj.ne` / 引理 `Adj.ne`

English:
lemma Adj.ne
  given: [G.Loopless] (hxy : G.Adj u v)
  statement: u != v
  proof: fun h => G.not_adj_self u h ▸ hxy

中文:
引理 伴随.ne
  条件: [G.无环] (hxy : G.伴随 u v)
  结论: u != v
  证明: fun h => G.not_adj_self u h ▸ hxy

Depends on / 依赖: G.not_adj_self, not_adj_self
-/
lemma Adj.ne [G.Loopless] (hxy : G.Adj u v) : u != v := fun h => G.not_adj_self u h ▸ hxy

/--
lemma `IsLink.ne` / 引理 `IsLink.ne`

English:
lemma IsLink.ne
  given: [G.Loopless] (he : G.IsLink e u v)
  statement: u != v
  proof: Adj.ne ⟨e, he⟩

中文:
引理 IsLink.ne
  条件: [G.无环] (he : G.IsLink e u v)
  结论: u != v
  证明: Adj.ne ⟨e, he⟩

Depends on / 依赖: Adj.ne
-/
lemma IsLink.ne [G.Loopless] (he : G.IsLink e u v) : u != v := Adj.ne ⟨e, he⟩

/--
lemma `loopless_iff_forall_ne_of_adj` / 引理 `loopless_iff_forall_ne_of_adj`

English:
lemma loopless_iff_forall_ne_of_adj
  statement: G.Loopless ↔ forall u v, G.Adj u v -> u != v
  proof: ⟨fun _ _ _ h => h.ne, fun h => ⟨fun _ x hex => h x x hex.adj rfl⟩⟩

中文:
引理 loopless_iff_对任意_ne_of_adj
  结论: G.无环 ↔ 对任意 u v, G.伴随 u v -> u != v
  证明: ⟨fun _ _ _ h => h.ne, fun h => ⟨fun _ x hex => h x x hex.adj rfl⟩⟩

Depends on / 依赖: h.ne, hex.adj
-/
lemma loopless_iff_forall_ne_of_adj : G.Loopless ↔ forall u v, G.Adj u v -> u != v :=
  ⟨fun _ _ _ h => h.ne, fun h => ⟨fun _ x hex => h x x hex.adj rfl⟩⟩

/--
lemma `vertexSet_nontrivial_of_edgeSet_nonempty_of_loopless` / 引理 `vertexSet_nontrivial_of_edgeSet_nonempty_of_loopless`

English:
lemma vertexSet_nontrivial_of_edgeSet_nonempty_of_loopless
  given: [G.Loopless] (hE : E(G).Nonempty)
  proof: by
  obtain ⟨e, he⟩ := hE
  obtain ⟨x, y, hxy⟩ := exists_isLink_of_mem_edgeSet he
  exact ⟨x, hxy.left_mem, y, hxy.right_mem, hxy.adj.ne⟩

中文:
引理 vertexSet_nontrivial_of_edgeSet_nonempty_of_loopless
  条件: [G.无环] (hE : E(G).非空)
  证明: by
  obtain ⟨e, he⟩ := hE
  obtain ⟨x, y, hxy⟩ := exists_isLink_of_mem_edgeSet he
  exact ⟨x, hxy.left_mem, y, hxy.right_mem, hxy.adj.ne⟩

Depends on / 依赖: exists_isLink_of_mem_edgeSet, hxy.adj.ne, hxy.left_mem, hxy.right_mem, left_mem, right_mem
-/
lemma vertexSet_nontrivial_of_edgeSet_nonempty_of_loopless [G.Loopless] (hE : E(G).Nonempty) :
    V(G).Nontrivial := by
  obtain ⟨e, he⟩ := hE
  obtain ⟨x, y, hxy⟩ := exists_isLink_of_mem_edgeSet he
  exact ⟨x, hxy.left_mem, y, hxy.right_mem, hxy.adj.ne⟩

/--
lemma `Loopless.anti` / 引理 `Loopless.anti`

English:
lemma Loopless.anti
  given: [hG : G.Loopless] (hle : H <= G)
  statement: H.Loopless
  proof: by
  rw [loopless_iff_forall_ne_of_adj] at hG ⊢
exact fun x y hxy => hG x y hxy.mono hle

@[simp]

中文:
引理 无环.anti
  条件: [hG : G.无环] (hle : H <= G)
  结论: H.无环
  证明: by
  rw [loopless_iff_forall_ne_of_adj] at hG ⊢
exact fun x y hxy => hG x y hxy.mono hle

@[simp]

Depends on / 依赖: hxy.mono, loopless_iff_forall_ne_of_adj
-/
lemma Loopless.anti [hG : G.Loopless] (hle : H <= G) : H.Loopless := by
  rw [loopless_iff_forall_ne_of_adj] at hG ⊢
exact fun x y hxy => hG x y hxy.mono hle

@[simp]
/--
lemma `Inc.isNonloopAt` / 引理 `Inc.isNonloopAt`

English:
lemma Inc.isNonloopAt
  given: [G.Loopless] (h : G.Inc e u)
  statement: G.IsNonloopAt e u
  proof: h.isLoopAt_or_isNonloopAt.resolve_left (Loopless.not_isLoopAt _ _)

中文:
引理 Inc.isNonloopAt
  条件: [G.无环] (h : G.Inc e u)
  结论: G.IsNonloopAt e u
  证明: h.isLoopAt_or_isNonloopAt.resolve_left (Loopless.not_isLoopAt _ _)

Depends on / 依赖: Loopless, Loopless.not_isLoopAt, h.isLoopAt_or_isNonloopAt.resolve_left, isLoopAt_or_isNonloopAt, not_isLoopAt, resolve_left
-/
lemma Inc.isNonloopAt [G.Loopless] (h : G.Inc e u) : G.IsNonloopAt e u :=
  h.isLoopAt_or_isNonloopAt.resolve_left (Loopless.not_isLoopAt _ _)

end Loopless

section Simple

/-- A `Simple` graph is a `Loopless` graph where no pair of vertices are the ends of more than one
edge. -/
@[mk_iff]
/--
Definition of `Simple` / `Simple` 的定义

English:
class Simple
  parameters: (G : Graph α β)
  extends: G.Loopless
  axioms and operations (1):
    - eq_of_isLink : forall ⦃e f x y⦄, G.IsLink e x y -> G.IsLink f x y -> e = f

中文:
类 单
  参数: (G : 图 α β)
  继承: G.无环
  公理与运算 (1 个):
    - eq_of_isLink : 对任意 ⦃e f x y⦄, G.IsLink e x y -> G.IsLink f x y -> e = f
-/
class Simple (G : Graph α β) : Prop extends G.Loopless where
  eq_of_isLink : forall ⦃e f x y⦄, G.IsLink e x y -> G.IsLink f x y -> e = f

variable [G.Simple]

/--
lemma `IsLink.eq` / 引理 `IsLink.eq`

English:
lemma IsLink.eq
  given: (h : G.IsLink e u v) (h' : G.IsLink f u v)
  statement: e = f
  proof: Simple.eq_of_isLink h h'

中文:
引理 IsLink.eq
  条件: (h : G.IsLink e u v) (h' : G.IsLink f u v)
  结论: e = f
  证明: Simple.eq_of_isLink h h'

Depends on / 依赖: Simple, Simple.eq_of_isLink, eq_of_isLink
-/
lemma IsLink.eq (h : G.IsLink e u v) (h' : G.IsLink f u v) : e = f :=
  Simple.eq_of_isLink h h'

/--
lemma `Simple.anti` / 引理 `Simple.anti`

English:
lemma Simple.anti
  given: (hle : H <= G)
  statement: H.Simple where
  proof: by simp [toLoopless.anti hle]
  eq_of_isLink e f x y he hf := (he.mono hle).eq (hf.mono hle)

中文:
引理 单.anti
  条件: (hle : H <= G)
  结论: H.单 where
  证明: by simp [toLoopless.anti hle]
  eq_of_isLink e f x y he hf := (he.mono hle).eq (hf.mono hle)

Depends on / 依赖: eq_of_isLink, he.mono, hf.mono, toLoopless, toLoopless.anti
-/
lemma Simple.anti (hle : H <= G) : H.Simple where
  not_isLoopAt e x := by simp [toLoopless.anti hle]
  eq_of_isLink e f x y he hf := (he.mono hle).eq (hf.mono hle)

instance (V : Set α) : (Graph.noEdge V β).Simple where
  not_isLoopAt := by simp [IsLoopAt]
  eq_of_isLink := by simp

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (⊥ : Graph α β).Simple
  body: inferInstanceAs (Graph.noEdge _ β).Simple

中文:
实例 :
  签名: (⊥ : 图 α β).单
  定义体: inferInstanceAs (Graph.noEdge _ β).Simple

Depends on / 依赖: Graph.noEdge, Simple, noEdge
-/
instance : (⊥ : Graph α β).Simple := inferInstanceAs (Graph.noEdge _ β).Simple

end Simple

section toSimpleGraph

/-- Construct a simple graph from a graph. -/
@[expose, simps (attr := grind =)]
/--
Definition of `toSimpleGraph` / `toSimpleGraph` 的定义

English:
definition toSimpleGraph
  signature: (G : Graph α β)
  body: u != v ∧ G.Adj u v
  symm := ⟨fun u v => by grind [adj_comm]⟩

中文:
定义 toSimpleGraph
  签名: (G : 图 α β)
  定义体: u != v ∧ G.Adj u v
  symm := ⟨fun u v => by grind [adj_comm]⟩

Depends on / 依赖: G.Adj
-/
def toSimpleGraph (G : Graph α β) : SimpleGraph V(G) where
  Adj u v := u != v ∧ G.Adj u v
  symm := ⟨fun u v => by grind [adj_comm]⟩

/--
lemma `toSimpleGraph_adj_iff` / 引理 `toSimpleGraph_adj_iff`

English:
lemma toSimpleGraph_adj_iff
  given: [G.Loopless] (u v : V(G))
  statement: G.toSimpleGraph.Adj u v ↔ G.Adj u v
  proof: by
  grind [Adj.ne]

中文:
引理 toSimpleGraph_adj_iff
  条件: [G.无环] (u v : V(G))
  结论: G.toSimpleGraph.伴随 u v ↔ G.伴随 u v
  证明: by
  grind [Adj.ne]

Depends on / 依赖: Adj.ne
-/
lemma toSimpleGraph_adj_iff [G.Loopless] (u v : V(G)) : G.toSimpleGraph.Adj u v ↔ G.Adj u v := by
  grind [Adj.ne]

/--
lemma `toSimpleGraph_mono` / 引理 `toSimpleGraph_mono`

English:
lemma toSimpleGraph_mono
  given: (h : G <=s H)
  statement: G.toSimpleGraph <= h.vertexSet_eq ▸ H.toSimpleGraph
  proof: by
  rintro u v hadj
  match G, H with
  | ⟨GV, GL, GE, _, _, _, _⟩, ⟨HV, HL, HE, _, _, _, _⟩ =>
    obtain ⟨hne, hadj⟩ := toSimpleGraph_adj .. ▸ hadj
    obtain ⟨hle, h⟩ := h
    simp only at h
    subst GV
    simp [toSimpleGraph_adj, hne, hadj.mono hle]

中文:
引理 toSimpleGraph_mono
  条件: (h : G <=s H)
  结论: G.toSimpleGraph <= h.vertexSet_eq ▸ H.toSimpleGraph
  证明: by
  rintro u v hadj
  match G, H with
  | ⟨GV, GL, GE, _, _, _, _⟩, ⟨HV, HL, HE, _, _, _, _⟩ =>
    obtain ⟨hne, hadj⟩ := toSimpleGraph_adj .. ▸ hadj
    obtain ⟨hle, h⟩ := h
    simp only at h
    subst GV
    simp [toSimpleGraph_adj, hne, hadj.mono hle]

Depends on / 依赖: hadj.mono, toSimpleGraph_adj
-/
lemma toSimpleGraph_mono (h : G <=s H) : G.toSimpleGraph <= h.vertexSet_eq ▸ H.toSimpleGraph := by
  rintro u v hadj
  match G, H with
  | ⟨GV, GL, GE, _, _, _, _⟩, ⟨HV, HL, HE, _, _, _, _⟩ =>
    obtain ⟨hne, hadj⟩ := toSimpleGraph_adj .. ▸ hadj
    obtain ⟨hle, h⟩ := h
    simp only at h
    subst GV
    simp [toSimpleGraph_adj, hne, hadj.mono hle]

/-- Construct a graph from a simple graph. It has every element of the vertex type as a vertex. -/
@[expose, simps (attr := grind =)]
/--
Definition of `ofSimpleGraph` / `ofSimpleGraph` 的定义

English:
definition ofSimpleGraph
  signature: (G : SimpleGraph α)
  body: Set.univ
  edgeSet := G.edgeSet
  IsLink e x y := e = s(x, y) ∧ e in G.edgeSet
  isLink_symm e he := ⟨fun u v => by simp [Sym2.eq_swap]⟩
  eq_or_eq_of_isLink_of_isLink e u v x y he hf := by grind
  edge_mem_iff_exists_isLink e := by induction e with | h u v => grind

@[simp]

中文:
定义 ofSimpleGraph
  签名: (G : 简单图 α)
  定义体: Set.univ
  edgeSet := G.edgeSet
  IsLink e x y := e = s(x, y) ∧ e in G.edgeSet
  isLink_symm e he := ⟨fun u v => by simp [Sym2.eq_swap]⟩
  eq_or_eq_of_isLink_of_isLink e u v x y he hf := by grind
  edge_mem_iff_exists_isLink e := by induction e with | h u v => grind

@[simp]

Depends on / 依赖: Set.univ
-/
def ofSimpleGraph (G : SimpleGraph α) : Graph α (Sym2 α) where
  vertexSet := Set.univ
  edgeSet := G.edgeSet
  IsLink e x y := e = s(x, y) ∧ e in G.edgeSet
  isLink_symm e he := ⟨fun u v => by simp [Sym2.eq_swap]⟩
  eq_or_eq_of_isLink_of_isLink e u v x y he hf := by grind
  edge_mem_iff_exists_isLink e := by induction e with | h u v => grind

@[simp]
/--
lemma `ofSimpleGraph_adj_iff` / 引理 `ofSimpleGraph_adj_iff`

English:
lemma ofSimpleGraph_adj_iff
  given: {G : SimpleGraph α} (u v : α)
  proof: by simp [Adj]

中文:
引理 ofSimpleGraph_adj_iff
  条件: {G : 简单图 α} (u v : α)
  证明: by simp [Adj]
-/
lemma ofSimpleGraph_adj_iff {G : SimpleGraph α} (u v : α) :
    (ofSimpleGraph G).Adj u v ↔ G.Adj u v := by simp [Adj]

/--
Definition of `toSimpleGraphOfSimpleGraphIso` / `toSimpleGraphOfSimpleGraphIso` 的定义

English:
definition toSimpleGraphOfSimpleGraphIso
  signature: (G : SimpleGraph α)
  body: by
  use Equiv.Set.univ α
  refine ⟨fun h => ⟨fun h' => h.ne (congrArg Subtype.val h'), ?_⟩, fun ⟨_, h⟩ => ?_⟩ <;>
    revert h <;> rw [ofSimpleGraph_adj_iff] <;> exact id

中文:
定义 toSimpleGraphOfSimpleGraphIso
  签名: (G : 简单图 α)
  定义体: by
  use Equiv.Set.univ α
  refine ⟨fun h => ⟨fun h' => h.ne (congrArg Subtype.val h'), ?_⟩, fun ⟨_, h⟩ => ?_⟩ <;>
    revert h <;> rw [ofSimpleGraph_adj_iff] <;> exact id

Depends on / 依赖: Equiv.Set.univ, Subtype, Subtype.val, h.ne, ofSimpleGraph_adj_iff, revert
-/
def toSimpleGraphOfSimpleGraphIso (G : SimpleGraph α) :
    (toSimpleGraph (ofSimpleGraph G)) ≃g G := by
  use Equiv.Set.univ α
  refine ⟨fun h => ⟨fun h' => h.ne (congrArg Subtype.val h'), ?_⟩, fun ⟨_, h⟩ => ?_⟩ <;>
    revert h <;> rw [ofSimpleGraph_adj_iff] <;> exact id

end toSimpleGraph

end Graph
