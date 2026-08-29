/-
Copyright (c) 2020 Aaron Anderson, Jalex Stark, Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson, Jalex Stark, Kyle Miller, Alena Gusakov, Hunter Monroe
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Init
public import Mathlib.Data.Finite.Prod
public import Mathlib.Data.Rel
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Sym.Sym2
public import Mathlib.Order.CompleteBooleanAlgebra
public import Mathlib.Tactic.CrossRefAttribute

import Mathlib.Data.Set.Lattice

/-!
# Simple graphs

This module defines simple graphs on a vertex type `V` as an irreflexive symmetric relation.

## Main definitions

* `SimpleGraph` is a structure for symmetric, irreflexive relations.

* `SimpleGraph.neighborSet` is the `Set` of vertices adjacent to a given vertex.

* `SimpleGraph.commonNeighbors` is the intersection of the neighbor sets of two given vertices.

* `SimpleGraph.incidenceSet` is the `Set` of edges containing a given vertex.

* `CompleteAtomicBooleanAlgebra` instance: Under the subgraph relation, `SimpleGraph` forms a
  `CompleteAtomicBooleanAlgebra`. In other words, this is the complete lattice of spanning subgraphs
  of the complete graph.

## TODO

* This is the simplest notion of an unoriented graph.
  This should eventually fit into a more complete combinatorics hierarchy which includes
  multigraphs and directed graphs.
  We begin with simple graphs in order to start learning what the combinatorics hierarchy should
  look like.
-/

@[expose] public section

attribute [aesop norm (rule_sets := [SimpleGraph])] symm_def
attribute [aesop norm (rule_sets := [SimpleGraph])] irrefl_def

/--
A variant of the `aesop` tactic for use in the graph library. Changes relative
to standard `aesop`:

- We use the `SimpleGraph` rule set in addition to the default rule sets.
- We instruct Aesop's `intro` rule to unfold with `default` transparency.
- We instruct Aesop to fail if it can't fully solve the goal. This allows us to
  use `aesop_graph` for auto-params.
-/
macro (name := aesop_graph) "aesop_graph" c:Aesop.tactic_clause* : tactic =>
  `(tactic|
aesop c*
      (config := { introsTransparency? := some .default, terminal := true })
      (rule_sets := [$(Lean.mkIdent `SimpleGraph):ident]))

/--
Use `aesop_graph?` to pass along a `Try this` suggestion when using `aesop_graph`
-/
macro (name := aesop_graph?) "aesop_graph?" c:Aesop.tactic_clause* : tactic =>
  `(tactic|
aesop? c*
      (config := { introsTransparency? := some .default, terminal := true })
      (rule_sets := [$(Lean.mkIdent `SimpleGraph):ident]))

/--
A variant of `aesop_graph` which does not fail if it is unable to solve the goal.
Use this only for exploration! Nonterminal Aesop is even worse than nonterminal `simp`.
-/
macro (name := aesop_graph_nonterminal) "aesop_graph_nonterminal" c:Aesop.tactic_clause* : tactic =>
  `(tactic|
aesop c*
      (config := { introsTransparency? := some .default, warnOnNonterminal := false })
      (rule_sets := [$(Lean.mkIdent `SimpleGraph):ident]))

open Finset Function

universe u v w

/-- A simple graph is an irreflexive symmetric relation `Adj` on a vertex type `V`.
The relation describes which pairs of vertices are adjacent.
There is exactly one edge for every pair of adjacent vertices;
see `SimpleGraph.edgeSet` for the corresponding edge set.
-/
@[ext, aesop safe constructors (rule_sets := [SimpleGraph]), wikidata Q141488]
/--
Definition of `SimpleGraph` / `SimpleGraph` 的定义

English:
structure SimpleGraph
  parameters: (V : Type u)
  axioms and operations (3):
    - Adj : V -> V -> Prop
    - symm : Std.Symm Adj  [default: by aesop_graph]
    - loopless : Std.Irrefl Adj  [default: by aesop_graph]

中文:
结构 SimpleGraph
  参数: (V : 类型u)
  公理与运算 (3 个):
    - Adj : V -> V -> 命题
    - symm : Std.Symm Adj  [默认: by aesop_graph]
    - loopless : Std.Irrefl Adj  [默认: by aesop_graph]

Depends on / 依赖: Irrefl, Std.Irrefl, aesop_graph, loopless
-/
structure SimpleGraph (V : Type u) where
  /-- The adjacency relation of a simple graph. -/
  Adj : V -> V -> Prop
  symm : Std.Symm Adj := by aesop_graph
  loopless : Std.Irrefl Adj := by aesop_graph

initialize_simps_projections SimpleGraph (Adj -> adj)

set_option backward.isDefEq.respectTransparency false in
/-- Constructor for simple graphs using a symmetric irreflexive Boolean function. -/
@[simps]
/--
Definition of `SimpleGraph.mk'` / `SimpleGraph.mk'` 的定义

English:
definition SimpleGraph.mk'
  signature: {V : Type u}
  body: ⟨fun v w => x.1 v w, ⟨fun v w => by simp [x.2.1]⟩, ⟨fun v => by simp [x.2.2]⟩⟩
  inj' := by
    rintro ⟨adj, _⟩ ⟨adj', _⟩
    simp only [mk.injEq, Subtype.mk.injEq]
    intro h
    funext v w
    simpa [Bool.coe_iff_coe] using congr_fun₂ h v w

中文:
定义 SimpleGraph.mk'
  签名: {V : 类型u}
  定义体: ⟨fun v w => x.1 v w, ⟨fun v w => by simp [x.2.1]⟩, ⟨fun v => by simp [x.2.2]⟩⟩
  inj' := by
    rintro ⟨adj, _⟩ ⟨adj', _⟩
    simp only [mk.injEq, Subtype.mk.injEq]
    intro h
    funext v w
    simpa [Bool.coe_iff_coe] using congr_fun₂ h v w
-/
def SimpleGraph.mk' {V : Type u} :
    {adj : V -> V -> Bool // (forall x y, adj x y = adj y x) ∧ (forall x, ¬ adj x x)} ↪ SimpleGraph V where
  toFun x := ⟨fun v w => x.1 v w, ⟨fun v w => by simp [x.2.1]⟩, ⟨fun v => by simp [x.2.2]⟩⟩
  inj' := by
    rintro ⟨adj, _⟩ ⟨adj', _⟩
    simp only [mk.injEq, Subtype.mk.injEq]
    intro h
    funext v w
    simpa [Bool.coe_iff_coe] using congr_fun₂ h v w

/-- We can enumerate simple graphs by enumerating all functions `V → V → Bool`
and filtering on whether they are symmetric and irreflexive. -/
instance {V : Type u} [Fintype V] [DecidableEq V] : Fintype (SimpleGraph V) where
  elems := Finset.univ.map SimpleGraph.mk'
  complete := by
    classical
    rintro ⟨Adj, hs, hi⟩
    simp only [mem_map, mem_univ, true_and, Subtype.exists, Bool.not_eq_true]
    refine ⟨fun v w => Adj v w, ⟨?_, ?_⟩, ?_⟩
    · simp [hs.iff]
    · intro v; simp [hi.irrefl v]
    · ext
      simp

/--
Instance `SimpleGraph.instFinite` / 实例 `SimpleGraph.instFinite`

English:
instance SimpleGraph.instFinite
  signature: {V : Type u} [Finite V]
  body: .of_injective SimpleGraph.Adj fun _ _ => SimpleGraph.ext

中文:
实例 SimpleGraph.instFinite
  签名: {V : 类型u} [Finite V]
  定义体: .of_injective SimpleGraph.Adj fun _ _ => SimpleGraph.ext

Depends on / 依赖: SimpleGraph, SimpleGraph.Adj, SimpleGraph.ext, of_injective
-/
instance SimpleGraph.instFinite {V : Type u} [Finite V] : Finite (SimpleGraph V) :=
  .of_injective SimpleGraph.Adj fun _ _ => SimpleGraph.ext

/--
Definition of `SimpleGraph.fromRel` / `SimpleGraph.fromRel` 的定义

English:
definition SimpleGraph.fromRel
  signature: {V : Type u} (r : V -> V -> Prop)
  body: a != b ∧ (r a b ∨ r b a)

@[simp]

中文:
定义 SimpleGraph.fromRel
  签名: {V : 类型u} (r : V -> V -> 命题)
  定义体: a != b ∧ (r a b ∨ r b a)

@[simp]
-/
def SimpleGraph.fromRel {V : Type u} (r : V -> V -> Prop) : SimpleGraph V where
  Adj a b := a != b ∧ (r a b ∨ r b a)

@[simp]
/--
theorem `SimpleGraph.fromRel_adj` / 定理 `SimpleGraph.fromRel_adj`

English:
theorem SimpleGraph.fromRel_adj
  given: {V : Type u} (r : V -> V -> Prop) (v w : V)
  proof: Iff.rfl

中文:
定理 SimpleGraph.fromRel_adj
  条件: {V : 类型u} (r : V -> V -> 命题) (v w : V)
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem SimpleGraph.fromRel_adj {V : Type u} (r : V -> V -> Prop) (v w : V) :
    (SimpleGraph.fromRel r).Adj v w ↔ v != w ∧ (r v w ∨ r w v) :=
  Iff.rfl

attribute [aesop safe (rule_sets := [SimpleGraph])] Ne.symm
attribute [aesop safe (rule_sets := [SimpleGraph])] Ne.irrefl

instance {V : Type u} [DecidableEq V] (r : V -> V -> Prop)
    [DecidableRel r] : DecidableRel (SimpleGraph.fromRel r).Adj :=
  inferInstanceAs (DecidableRel fun a b => a != b ∧ (r a b ∨ r b a))

/-- Two vertices are adjacent in the complete bipartite graph on two vertex types
if and only if they are not from the same side.
Any bipartite graph may be regarded as a subgraph of one of these. -/
@[simps]
/--
Definition of `completeBipartiteGraph` / `completeBipartiteGraph` 的定义

English:
definition completeBipartiteGraph
  signature: (V W : Type*)
  body: v.isLeft ∧ w.isRight ∨ v.isRight ∧ w.isLeft

中文:
定义 completeBipartiteGraph
  签名: (V W : 类型)
  定义体: v.isLeft ∧ w.isRight ∨ v.isRight ∧ w.isLeft

Depends on / 依赖: isLeft, isRight, v.isLeft, v.isRight, w.isLeft, w.isRight
-/
def completeBipartiteGraph (V W : Type*) : SimpleGraph (V oplus W) where
  Adj v w := v.isLeft ∧ w.isRight ∨ v.isRight ∧ w.isLeft

namespace SimpleGraph

variable {ι : Sort*} {V : Type u} (G H : SimpleGraph V) {a b c u v w : V} {e : Sym2 V}

@[simp]
/--
theorem `irrefl` / 定理 `irrefl`

English:
theorem irrefl
  given: {v : V}
  statement: ¬G.Adj v v
  proof: G.loopless.irrefl v

中文:
定理 irrefl
  条件: {v : V}
  结论: ¬G.Adj v v
  证明: G.loopless.irrefl v
-/
protected theorem irrefl {v : V} : ¬G.Adj v v :=
  G.loopless.irrefl v

/--
theorem `adj_comm` / 定理 `adj_comm`

English:
theorem adj_comm
  given: (u v : V)
  statement: G.Adj u v ↔ G.Adj v u
  proof: G.symm.iff u v

@[symm]

中文:
定理 adj_comm
  条件: (u v : V)
  结论: G.Adj u v ↔ G.Adj v u
  证明: G.symm.iff u v

@[symm]

Depends on / 依赖: G.symm.iff
-/
theorem adj_comm (u v : V) : G.Adj u v ↔ G.Adj v u :=
  G.symm.iff u v

@[symm]
/--
theorem `adj_symm` / 定理 `adj_symm`

English:
theorem adj_symm
  given: (h : G.Adj u v)
  statement: G.Adj v u
  proof: G.symm.symm u v h

中文:
定理 adj_symm
  条件: (h : G.Adj u v)
  结论: G.Adj v u
  证明: G.symm.symm u v h

Depends on / 依赖: G.symm.symm
-/
theorem adj_symm (h : G.Adj u v) : G.Adj v u :=
  G.symm.symm u v h

/--
theorem `Adj.symm` / 定理 `Adj.symm`

English:
theorem Adj.symm
  given: {G : SimpleGraph V} {u v : V} (h : G.Adj u v)
  statement: G.Adj v u
  proof: G.adj_symm h

中文:
定理 Adj.symm
  条件: {G : SimpleGraph V} {u v : V} (h : G.Adj u v)
  结论: G.Adj v u
  证明: G.adj_symm h
-/
theorem Adj.symm {G : SimpleGraph V} {u v : V} (h : G.Adj u v) : G.Adj v u :=
  G.adj_symm h

/--
theorem `ne_of_adj` / 定理 `ne_of_adj`

English:
theorem ne_of_adj
  given: (h : G.Adj a b)
  statement: a != b
  proof: by
  rintro rfl
  exact G.irrefl h

中文:
定理 ne_of_adj
  条件: (h : G.Adj a b)
  结论: a != b
  证明: by
  rintro rfl
  exact G.irrefl h

Depends on / 依赖: G.irrefl, irrefl
-/
theorem ne_of_adj (h : G.Adj a b) : a != b := by
  rintro rfl
  exact G.irrefl h

/--
theorem `Adj.ne` / 定理 `Adj.ne`

English:
theorem Adj.ne
  given: {G : SimpleGraph V} {a b : V} (h : G.Adj a b)
  statement: a != b
  proof: G.ne_of_adj h

中文:
定理 Adj.ne
  条件: {G : SimpleGraph V} {a b : V} (h : G.Adj a b)
  结论: a != b
  证明: G.ne_of_adj h
-/
protected theorem Adj.ne {G : SimpleGraph V} {a b : V} (h : G.Adj a b) : a != b :=
  G.ne_of_adj h

/--
theorem `Adj.ne'` / 定理 `Adj.ne'`

English:
theorem Adj.ne'
  given: {G : SimpleGraph V} {a b : V} (h : G.Adj a b)
  statement: b != a
  proof: h.ne.symm

中文:
定理 Adj.ne'
  条件: {G : SimpleGraph V} {a b : V} (h : G.Adj a b)
  结论: b != a
  证明: h.ne.symm
-/
protected theorem Adj.ne' {G : SimpleGraph V} {a b : V} (h : G.Adj a b) : b != a :=
  h.ne.symm

/--
theorem `ne_of_adj_of_not_adj` / 定理 `ne_of_adj_of_not_adj`

English:
theorem ne_of_adj_of_not_adj
  given: {v w x : V} (h : G.Adj v x) (hn : ¬G.Adj w x)
  statement: v != w
  proof: fun h' =>
  hn (h' ▸ h)

中文:
定理 ne_of_adj_of_not_adj
  条件: {v w x : V} (h : G.Adj v x) (hn : ¬G.Adj w x)
  结论: v != w
  证明: fun h' =>
  hn (h' ▸ h)
-/
theorem ne_of_adj_of_not_adj {v w x : V} (h : G.Adj v x) (hn : ¬G.Adj w x) : v != w := fun h' =>
  hn (h' ▸ h)

/--
theorem `adj_injective` / 定理 `adj_injective`

English:
theorem adj_injective
  statement: Injective (Adj : SimpleGraph V -> V -> V -> Prop)
  proof: fun _ _ => SimpleGraph.ext

@[simp]

中文:
定理 adj_injective
  结论: Injective (Adj : SimpleGraph V -> V -> V -> 命题)
  证明: fun _ _ => SimpleGraph.ext

@[simp]

Depends on / 依赖: SimpleGraph, SimpleGraph.ext
-/
theorem adj_injective : Injective (Adj : SimpleGraph V -> V -> V -> Prop) :=
  fun _ _ => SimpleGraph.ext

@[simp]
/--
theorem `adj_inj` / 定理 `adj_inj`

English:
theorem adj_inj
  given: {G H : SimpleGraph V}
  statement: G.Adj = H.Adj ↔ G = H
  proof: adj_injective.eq_iff

中文:
定理 adj_inj
  条件: {G H : SimpleGraph V}
  结论: G.Adj = H.Adj ↔ G = H
  证明: adj_injective.eq_iff

Depends on / 依赖: adj_injective, adj_injective.eq_iff, eq_iff
-/
theorem adj_inj {G H : SimpleGraph V} : G.Adj = H.Adj ↔ G = H :=
  adj_injective.eq_iff

/--
theorem `adj_congr_of_sym2` / 定理 `adj_congr_of_sym2`

English:
theorem adj_congr_of_sym2
  given: {u v w x : V} (h : s(u, v) = s(w, x))
  statement: G.Adj u v ↔ G.Adj w x
  proof: by
  simp only [Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk] at h
  rcases h with hl | hr
  · rw [hl.1, hl.2]
  · rw [hr.1, hr.2, adj_comm]

中文:
定理 adj_congr_of_sym2
  条件: {u v w x : V} (h : s(u, v) = s(w, x))
  结论: G.Adj u v ↔ G.Adj w x
  证明: by
  simp only [Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk] at h
  rcases h with hl | hr
  · rw [hl.1, hl.2]
  · rw [hr.1, hr.2, adj_comm]

Depends on / 依赖: Prod.mk.injEq, Prod.swap_prod_mk, Sym2.eq, Sym2.rel_iff, adj_comm, rel_iff, swap_prod_mk
-/
theorem adj_congr_of_sym2 {u v w x : V} (h : s(u, v) = s(w, x)) : G.Adj u v ↔ G.Adj w x := by
  simp only [Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk] at h
  rcases h with hl | hr
  · rw [hl.1, hl.2]
  · rw [hr.1, hr.2, adj_comm]

/--
Instance `symm_adj` / 实例 `symm_adj`

English:
instance symm_adj
  signature: (f : ι -> V)
  body: .symm

中文:
实例 symm_adj
  签名: (f : ι -> V)
  定义体: .symm
-/
instance symm_adj (f : ι -> V) : Std.Symm fun i j => G.Adj (f i) (f j) where symm _ _ := .symm

section Order

/-- The relation that one `SimpleGraph` is a subgraph of another.
Note that this should be spelled `≤`. -/
@[deprecated "use `<=` instead" (since := "2026-03-25")]
/--
Definition of `IsSubgraph` / `IsSubgraph` 的定义

English:
definition IsSubgraph
  signature: (x y : SimpleGraph V)
  body: forall ⦃v w : V⦄, x.Adj v w -> y.Adj v w

中文:
定义 IsSubgraph
  签名: (x y : SimpleGraph V)
  定义体: forall ⦃v w : V⦄, x.Adj v w -> y.Adj v w

Depends on / 依赖: x.Adj, y.Adj
-/
def IsSubgraph (x y : SimpleGraph V) : Prop :=
  forall ⦃v w : V⦄, x.Adj v w -> y.Adj v w

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LE (SimpleGraph V)
  body: forall ⦃v w : V⦄, x.Adj v w -> y.Adj v w

中文:
实例 :
  签名: LE (SimpleGraph V)
  定义体: forall ⦃v w : V⦄, x.Adj v w -> y.Adj v w

Depends on / 依赖: x.Adj, y.Adj
-/
instance : LE (SimpleGraph V) where
  le x y := forall ⦃v w : V⦄, x.Adj v w -> y.Adj v w

/--
lemma `le_iff_adj` / 引理 `le_iff_adj`

English:
lemma le_iff_adj
  given: {G H : SimpleGraph V}
  statement: G <= H ↔ forall v w, G.Adj v w -> H.Adj v w
  proof: .rfl

中文:
引理 le_iff_adj
  条件: {G H : SimpleGraph V}
  结论: G <= H ↔ 对任意 v w, G.Adj v w -> H.Adj v w
  证明: .rfl
-/
lemma le_iff_adj {G H : SimpleGraph V} : G <= H ↔ forall v w, G.Adj v w -> H.Adj v w := .rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Max (SimpleGraph V)
  body: { Adj := x.Adj ⊔ y.Adj
      symm.symm v w h := by rwa [Pi.sup_apply, Pi.sup_apply, x.adj_comm, y.adj_comm] }

@[simp, grind =]

中文:
实例 :
  签名: Max (SimpleGraph V)
  定义体: { Adj := x.Adj ⊔ y.Adj
      symm.symm v w h := by rwa [Pi.sup_apply, Pi.sup_apply, x.adj_comm, y.adj_comm] }

@[simp, grind =]

Depends on / 依赖: Pi.sup_apply, adj_comm, sup_apply, symm.symm, x.Adj, x.adj_comm, y.Adj, y.adj_comm
-/
instance : Max (SimpleGraph V) where
  max x y :=
    { Adj := x.Adj ⊔ y.Adj
      symm.symm v w h := by rwa [Pi.sup_apply, Pi.sup_apply, x.adj_comm, y.adj_comm] }

@[simp, grind =]
/--
theorem `sup_adj` / 定理 `sup_adj`

English:
theorem sup_adj
  given: (x y : SimpleGraph V) (v w : V)
  statement: (x ⊔ y).Adj v w ↔ x.Adj v w ∨ y.Adj v w
  proof: Iff.rfl

中文:
定理 sup_adj
  条件: (x y : SimpleGraph V) (v w : V)
  结论: (x ⊔ y).Adj v w ↔ x.Adj v w ∨ y.Adj v w
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem sup_adj (x y : SimpleGraph V) (v w : V) : (x ⊔ y).Adj v w ↔ x.Adj v w ∨ y.Adj v w :=
  Iff.rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Min (SimpleGraph V)
  body: { Adj := x.Adj ⊓ y.Adj
      symm.symm v w h := by rwa [Pi.inf_apply, Pi.inf_apply, x.adj_comm, y.adj_comm] }

@[simp]

中文:
实例 :
  签名: Min (SimpleGraph V)
  定义体: { Adj := x.Adj ⊓ y.Adj
      symm.symm v w h := by rwa [Pi.inf_apply, Pi.inf_apply, x.adj_comm, y.adj_comm] }

@[simp]

Depends on / 依赖: Pi.inf_apply, adj_comm, inf_apply, symm.symm, x.Adj, x.adj_comm, y.Adj, y.adj_comm
-/
instance : Min (SimpleGraph V) where
  min x y :=
    { Adj := x.Adj ⊓ y.Adj
      symm.symm v w h := by rwa [Pi.inf_apply, Pi.inf_apply, x.adj_comm, y.adj_comm] }

@[simp]
/--
theorem `inf_adj` / 定理 `inf_adj`

English:
theorem inf_adj
  given: (x y : SimpleGraph V) (v w : V)
  statement: (x ⊓ y).Adj v w ↔ x.Adj v w ∧ y.Adj v w
  proof: Iff.rfl

中文:
定理 inf_adj
  条件: (x y : SimpleGraph V) (v w : V)
  结论: (x ⊓ y).Adj v w ↔ x.Adj v w ∧ y.Adj v w
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem inf_adj (x y : SimpleGraph V) (v w : V) : (x ⊓ y).Adj v w ↔ x.Adj v w ∧ y.Adj v w :=
  Iff.rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Compl (SimpleGraph V)
  body: { Adj v w := v != w ∧ ¬G.Adj v w
      symm.symm v w := fun ⟨hne, _⟩ => ⟨hne.symm, by rwa [adj_comm]⟩ }

@[simp]

中文:
实例 :
  签名: Compl (SimpleGraph V)
  定义体: { Adj v w := v != w ∧ ¬G.Adj v w
      symm.symm v w := fun ⟨hne, _⟩ => ⟨hne.symm, by rwa [adj_comm]⟩ }

@[simp]

Depends on / 依赖: G.Adj, adj_comm, hne.symm, symm.symm
-/
instance : Compl (SimpleGraph V) where
  compl G :=
    { Adj v w := v != w ∧ ¬G.Adj v w
      symm.symm v w := fun ⟨hne, _⟩ => ⟨hne.symm, by rwa [adj_comm]⟩ }

@[simp]
/--
theorem `compl_adj` / 定理 `compl_adj`

English:
theorem compl_adj
  given: (G : SimpleGraph V) (v w : V)
  statement: Gᶜ.Adj v w ↔ v != w ∧ ¬G.Adj v w
  proof: Iff.rfl

中文:
定理 compl_adj
  条件: (G : SimpleGraph V) (v w : V)
  结论: Gᶜ.Adj v w ↔ v != w ∧ ¬G.Adj v w
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem compl_adj (G : SimpleGraph V) (v w : V) : Gᶜ.Adj v w ↔ v != w ∧ ¬G.Adj v w :=
  Iff.rfl

/--
Instance `sdiff` / 实例 `sdiff`

English:
instance sdiff
  signature: : SDiff (SimpleGraph V) where
  body: { Adj := x.Adj \ y.Adj
      symm.symm v w h := by change x.Adj w v ∧ ¬y.Adj w v; rwa [x.adj_comm, y.adj_comm] }

@[simp]

中文:
实例 sdiff
  签名: : SDiff (SimpleGraph V) where
  定义体: { Adj := x.Adj \ y.Adj
      symm.symm v w h := by change x.Adj w v ∧ ¬y.Adj w v; rwa [x.adj_comm, y.adj_comm] }

@[simp]

Depends on / 依赖: adj_comm, symm.symm, x.Adj, x.adj_comm, y.Adj, y.adj_comm
-/
instance sdiff : SDiff (SimpleGraph V) where
  sdiff x y :=
    { Adj := x.Adj \ y.Adj
      symm.symm v w h := by change x.Adj w v ∧ ¬y.Adj w v; rwa [x.adj_comm, y.adj_comm] }

@[simp]
/--
theorem `sdiff_adj` / 定理 `sdiff_adj`

English:
theorem sdiff_adj
  given: (x y : SimpleGraph V) (v w : V)
  statement: (x \ y).Adj v w ↔ x.Adj v w ∧ ¬y.Adj v w
  proof: Iff.rfl

中文:
定理 sdiff_adj
  条件: (x y : SimpleGraph V) (v w : V)
  结论: (x \ y).Adj v w ↔ x.Adj v w ∧ ¬y.Adj v w
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem sdiff_adj (x y : SimpleGraph V) (v w : V) : (x \ y).Adj v w ↔ x.Adj v w ∧ ¬y.Adj v w :=
  Iff.rfl

/--
Instance `supSet` / 实例 `supSet`

English:
instance supSet
  signature: : SupSet (SimpleGraph V) where
  body: { Adj a b := exists G in s, Adj G a b
      symm.symm _ _ := Exists.imp fun _ => And.imp_right Adj.symm }

中文:
实例 supSet
  签名: : SupSet (SimpleGraph V) where
  定义体: { Adj a b := exists G in s, Adj G a b
      symm.symm _ _ := Exists.imp fun _ => And.imp_right Adj.symm }

Depends on / 依赖: Adj.symm, And.imp_right, Exists, Exists.imp, imp_right, symm.symm
-/
instance supSet : SupSet (SimpleGraph V) where
  sSup s :=
    { Adj a b := exists G in s, Adj G a b
      symm.symm _ _ := Exists.imp fun _ => And.imp_right Adj.symm }

/--
Instance `infSet` / 实例 `infSet`

English:
instance infSet
  signature: : InfSet (SimpleGraph V) where
  body: { Adj a b := (forall ⦃G⦄, G in s -> Adj G a b) ∧ a != b
      symm.symm _ _ := And.imp (forall₂_imp fun _ _ => Adj.symm) Ne.symm }

@[simp]

中文:
实例 infSet
  签名: : InfSet (SimpleGraph V) where
  定义体: { Adj a b := (forall ⦃G⦄, G in s -> Adj G a b) ∧ a != b
      symm.symm _ _ := And.imp (forall₂_imp fun _ _ => Adj.symm) Ne.symm }

@[simp]

Depends on / 依赖: Adj.symm, And.imp, Ne.symm, symm.symm
-/
instance infSet : InfSet (SimpleGraph V) where
  sInf s :=
    { Adj a b := (forall ⦃G⦄, G in s -> Adj G a b) ∧ a != b
      symm.symm _ _ := And.imp (forall₂_imp fun _ _ => Adj.symm) Ne.symm }

@[simp]
/--
theorem `sSup_adj` / 定理 `sSup_adj`

English:
theorem sSup_adj
  given: {s : Set (SimpleGraph V)} {a b : V}
  statement: (sSup s).Adj a b ↔ exists G in s, Adj G a b
  proof: Iff.rfl

@[simp]

中文:
定理 sSup_adj
  条件: {s : Set (SimpleGraph V)} {a b : V}
  结论: (sSup s).Adj a b ↔ 存在 G in s, Adj G a b
  证明: Iff.rfl

@[simp]

Depends on / 依赖: Iff.rfl
-/
theorem sSup_adj {s : Set (SimpleGraph V)} {a b : V} : (sSup s).Adj a b ↔ exists G in s, Adj G a b :=
  Iff.rfl

@[simp]
/--
theorem `sInf_adj` / 定理 `sInf_adj`

English:
theorem sInf_adj
  given: {s : Set (SimpleGraph V)}
  statement: (sInf s).Adj a b ↔ (forall G in s, Adj G a b) ∧ a != b
  proof: Iff.rfl

@[simp]

中文:
定理 sInf_adj
  条件: {s : Set (SimpleGraph V)}
  结论: (sInf s).Adj a b ↔ (对任意 G in s, Adj G a b) ∧ a != b
  证明: Iff.rfl

@[simp]

Depends on / 依赖: Iff.rfl
-/
theorem sInf_adj {s : Set (SimpleGraph V)} : (sInf s).Adj a b ↔ (forall G in s, Adj G a b) ∧ a != b :=
  Iff.rfl

@[simp]
/--
theorem `iSup_adj` / 定理 `iSup_adj`

English:
theorem iSup_adj
  given: {f : ι -> SimpleGraph V}
  statement: (⨆ i, f i).Adj a b ↔ exists i, (f i).Adj a b
  proof: by simp [iSup]

@[simp]

中文:
定理 iSup_adj
  条件: {f : ι -> SimpleGraph V}
  结论: (⨆ i, f i).Adj a b ↔ 存在 i, (f i).Adj a b
  证明: by simp [iSup]

@[simp]
-/
theorem iSup_adj {f : ι -> SimpleGraph V} : (⨆ i, f i).Adj a b ↔ exists i, (f i).Adj a b := by simp [iSup]

@[simp]
/--
theorem `iInf_adj` / 定理 `iInf_adj`

English:
theorem iInf_adj
  given: {f : ι -> SimpleGraph V}
  statement: (⨅ i, f i).Adj a b ↔ (forall i, (f i).Adj a b) ∧ a != b
  proof: by
  simp [iInf]

中文:
定理 iInf_adj
  条件: {f : ι -> SimpleGraph V}
  结论: (⨅ i, f i).Adj a b ↔ (对任意 i, (f i).Adj a b) ∧ a != b
  证明: by
  simp [iInf]
-/
theorem iInf_adj {f : ι -> SimpleGraph V} : (⨅ i, f i).Adj a b ↔ (forall i, (f i).Adj a b) ∧ a != b := by
  simp [iInf]

/--
theorem `sInf_adj_of_nonempty` / 定理 `sInf_adj_of_nonempty`

English:
theorem sInf_adj_of_nonempty
  given: {s : Set (SimpleGraph V)} (hs : s.Nonempty)
  proof: sInf_adj.trans
and_iff_left_of_imp by
      obtain ⟨G, hG⟩ := hs
      exact fun h => (h _ hG).ne

中文:
定理 sInf_adj_of_nonempty
  条件: {s : Set (SimpleGraph V)} (hs : s.Nonempty)
  证明: sInf_adj.trans
and_iff_left_of_imp by
      obtain ⟨G, hG⟩ := hs
      exact fun h => (h _ hG).ne

Depends on / 依赖: and_iff_left_of_imp, sInf_adj, sInf_adj.trans
-/
theorem sInf_adj_of_nonempty {s : Set (SimpleGraph V)} (hs : s.Nonempty) :
    (sInf s).Adj a b ↔ forall G in s, Adj G a b :=
sInf_adj.trans
and_iff_left_of_imp by
      obtain ⟨G, hG⟩ := hs
      exact fun h => (h _ hG).ne

/--
theorem `iInf_adj_of_nonempty` / 定理 `iInf_adj_of_nonempty`

English:
theorem iInf_adj_of_nonempty
  given: [Nonempty ι] {f : ι -> SimpleGraph V}
  proof: by
  rw [iInf]; rw [sInf_adj_of_nonempty (Set.range_nonempty _)]; rw [Set.forall_mem_range]

中文:
定理 iInf_adj_of_nonempty
  条件: [Nonempty ι] {f : ι -> SimpleGraph V}
  证明: by
  rw [iInf]; rw [sInf_adj_of_nonempty (Set.range_nonempty _)]; rw [Set.forall_mem_range]

Depends on / 依赖: Set.forall_mem_range, Set.range_nonempty, forall_mem_range, range_nonempty, sInf_adj_of_nonempty
-/
theorem iInf_adj_of_nonempty [Nonempty ι] {f : ι -> SimpleGraph V} :
    (⨅ i, f i).Adj a b ↔ forall i, (f i).Adj a b := by
  rw [iInf]; rw [sInf_adj_of_nonempty (Set.range_nonempty _)]; rw [Set.forall_mem_range]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PartialOrder (SimpleGraph V)
  body: fast_instance% PartialOrder.lift _ adj_injective

中文:
实例 :
  签名: PartialOrder (SimpleGraph V)
  定义体: fast_instance% PartialOrder.lift _ adj_injective

Depends on / 依赖: PartialOrder, PartialOrder.lift, adj_injective, fast_instance
-/
instance : PartialOrder (SimpleGraph V) :=
  fast_instance% PartialOrder.lift _ adj_injective

/--
Instance `distribLattice` / 实例 `distribLattice`

English:
instance distribLattice
  signature: : DistribLattice (SimpleGraph V)
  body: adj_injective.distribLattice _ .rfl .rfl (fun _ _ => rfl) fun _ _ => rfl

中文:
实例 distribLattice
  签名: : DistribLattice (SimpleGraph V)
  定义体: adj_injective.distribLattice _ .rfl .rfl (fun _ _ => rfl) fun _ _ => rfl

Depends on / 依赖: adj_injective, adj_injective.distribLattice, distribLattice
-/
instance distribLattice : DistribLattice (SimpleGraph V) :=
  adj_injective.distribLattice _ .rfl .rfl (fun _ _ => rfl) fun _ _ => rfl

/--
Instance `completeAtomicBooleanAlgebra` / 实例 `completeAtomicBooleanAlgebra`

English:
instance completeAtomicBooleanAlgebra
  signature: : CompleteAtomicBooleanAlgebra (SimpleGraph V) where
  body: Ne
  bot.Adj _ _ := False
  le_top x _ _ h := x.ne_of_adj h
  bot_le _ _ _ h := h.elim
  sdiff_eq x y := by
    ext v w
    refine ⟨fun h => ⟨h.1, ⟨?_, h.2⟩⟩, fun h => ⟨h.1, h.2.2⟩⟩
    rintro rfl
    exact x.irrefl h.1
inf_compl_le_bot _ _ _ h := False.elim h.2.2 h.1
  top_le_sup_compl G v w hvw :=

中文:
实例 completeAtomicBooleanAlgebra
  签名: : CompleteAtomic布尔eanAlgebra (SimpleGraph V) where
  定义体: Ne
  bot.Adj _ _ := False
  le_top x _ _ h := x.ne_of_adj h
  bot_le _ _ _ h := h.elim
  sdiff_eq x y := by
    ext v w
    refine ⟨fun h => ⟨h.1, ⟨?_, h.2⟩⟩, fun h => ⟨h.1, h.2.2⟩⟩
    rintro rfl
    exact x.irrefl h.1
inf_compl_le_bot _ _ _ h := False.elim h.2.2 h.1
  top_le_sup_compl G v w hvw :=
-/
instance completeAtomicBooleanAlgebra : CompleteAtomicBooleanAlgebra (SimpleGraph V) where
  top.Adj := Ne
  bot.Adj _ _ := False
  le_top x _ _ h := x.ne_of_adj h
  bot_le _ _ _ h := h.elim
  sdiff_eq x y := by
    ext v w
    refine ⟨fun h => ⟨h.1, ⟨?_, h.2⟩⟩, fun h => ⟨h.1, h.2.2⟩⟩
    rintro rfl
    exact x.irrefl h.1
inf_compl_le_bot _ _ _ h := False.elim h.2.2 h.1
  top_le_sup_compl G v w hvw := by
    by_cases h : G.Adj v w
    · exact Or.inl h
    · exact Or.inr ⟨hvw, h⟩
  isLUB_sSup _ := ⟨fun G hG _ _ hab => ⟨G, hG, hab⟩, fun _ hG _ _ ⟨_, hH, hab⟩ => hG hH hab⟩
  isGLB_sInf _ := ⟨fun _ hG _ _ hab => hab.1 hG, fun _ hG _ _ hab => ⟨fun _ hH => hG hH hab, hab.ne⟩⟩
  iInf_iSup_eq f := by ext; simp [Classical.skolem]

/-- The complete graph on a type `V` is the simple graph with all pairs of distinct vertices. -/
@[wikidata Q45715]
/--
Definition of `completeGraph` / `completeGraph` 的定义

English:
abbreviation completeGraph
  signature: (V : Type u)
  body: ⊤

中文:
缩写 completeGraph
  签名: (V : 类型u)
  定义体: ⊤
-/
abbrev completeGraph (V : Type u) : SimpleGraph V := ⊤

/--
Definition of `emptyGraph` / `emptyGraph` 的定义

English:
abbreviation emptyGraph
  signature: (V : Type u)
  body: ⊥

@[simp]

中文:
缩写 emptyGraph
  签名: (V : 类型u)
  定义体: ⊥

@[simp]
-/
abbrev emptyGraph (V : Type u) : SimpleGraph V := ⊥

@[simp]
/--
theorem `top_adj` / 定理 `top_adj`

English:
theorem top_adj
  given: (v w : V)
  statement: (⊤ : SimpleGraph V).Adj v w ↔ v != w
  proof: Iff.rfl

@[simp]

中文:
定理 top_adj
  条件: (v w : V)
  结论: (⊤ : SimpleGraph V).Adj v w ↔ v != w
  证明: Iff.rfl

@[simp]

Depends on / 依赖: Iff.rfl
-/
theorem top_adj (v w : V) : (⊤ : SimpleGraph V).Adj v w ↔ v != w :=
  Iff.rfl

@[simp]
/--
theorem `bot_adj` / 定理 `bot_adj`

English:
theorem bot_adj
  given: (v w : V)
  statement: (⊥ : SimpleGraph V).Adj v w ↔ False
  proof: Iff.rfl

@[simp]

中文:
定理 bot_adj
  条件: (v w : V)
  结论: (⊥ : SimpleGraph V).Adj v w ↔ False
  证明: Iff.rfl

@[simp]

Depends on / 依赖: Iff.rfl
-/
theorem bot_adj (v w : V) : (⊥ : SimpleGraph V).Adj v w ↔ False :=
  Iff.rfl

@[simp]
/--
theorem `completeGraph_eq_top` / 定理 `completeGraph_eq_top`

English:
theorem completeGraph_eq_top
  given: (V : Type u)
  statement: completeGraph V = ⊤
  proof: rfl

@[simp]

中文:
定理 completeGraph_eq_top
  条件: (V : 类型u)
  结论: completeGraph V = ⊤
  证明: rfl

@[simp]
-/
theorem completeGraph_eq_top (V : Type u) : completeGraph V = ⊤ :=
  rfl

@[simp]
/--
theorem `emptyGraph_eq_bot` / 定理 `emptyGraph_eq_bot`

English:
theorem emptyGraph_eq_bot
  given: (V : Type u)
  statement: emptyGraph V = ⊥
  proof: rfl

中文:
定理 emptyGraph_eq_bot
  条件: (V : 类型u)
  结论: emptyGraph V = ⊥
  证明: rfl
-/
theorem emptyGraph_eq_bot (V : Type u) : emptyGraph V = ⊥ :=
  rfl

variable {G}

/--
theorem `eq_bot_iff_forall_not_adj` / 定理 `eq_bot_iff_forall_not_adj`

English:
theorem eq_bot_iff_forall_not_adj
  statement: G = ⊥ ↔ forall a b : V, ¬G.Adj a b
  proof: by
  simp [← le_bot_iff, le_iff_adj]

中文:
定理 eq_bot_iff_forall_not_adj
  结论: G = ⊥ ↔ 对任意 a b : V, ¬G.Adj a b
  证明: by
  simp [← le_bot_iff, le_iff_adj]

Depends on / 依赖: le_bot_iff, le_iff_adj
-/
theorem eq_bot_iff_forall_not_adj : G = ⊥ ↔ forall a b : V, ¬G.Adj a b := by
  simp [← le_bot_iff, le_iff_adj]

/--
theorem `ne_bot_iff_exists_adj` / 定理 `ne_bot_iff_exists_adj`

English:
theorem ne_bot_iff_exists_adj
  statement: G != ⊥ ↔ exists a b : V, G.Adj a b
  proof: by
  simp [eq_bot_iff_forall_not_adj]

中文:
定理 ne_bot_iff_exists_adj
  结论: G != ⊥ ↔ 存在 a b : V, G.Adj a b
  证明: by
  simp [eq_bot_iff_forall_not_adj]

Depends on / 依赖: eq_bot_iff_forall_not_adj
-/
theorem ne_bot_iff_exists_adj : G != ⊥ ↔ exists a b : V, G.Adj a b := by
  simp [eq_bot_iff_forall_not_adj]

/--
theorem `eq_top_iff_forall_ne_adj` / 定理 `eq_top_iff_forall_ne_adj`

English:
theorem eq_top_iff_forall_ne_adj
  statement: G = ⊤ ↔ forall a b : V, a != b -> G.Adj a b
  proof: by
  simp [← top_le_iff, le_iff_adj]

中文:
定理 eq_top_iff_forall_ne_adj
  结论: G = ⊤ ↔ 对任意 a b : V, a != b -> G.Adj a b
  证明: by
  simp [← top_le_iff, le_iff_adj]

Depends on / 依赖: le_iff_adj, top_le_iff
-/
theorem eq_top_iff_forall_ne_adj : G = ⊤ ↔ forall a b : V, a != b -> G.Adj a b := by
  simp [← top_le_iff, le_iff_adj]

/--
theorem `ne_top_iff_exists_not_adj` / 定理 `ne_top_iff_exists_not_adj`

English:
theorem ne_top_iff_exists_not_adj
  statement: G != ⊤ ↔ exists a b : V, a != b ∧ ¬G.Adj a b
  proof: by
  simp [eq_top_iff_forall_ne_adj]

中文:
定理 ne_top_iff_exists_not_adj
  结论: G != ⊤ ↔ 存在 a b : V, a != b ∧ ¬G.Adj a b
  证明: by
  simp [eq_top_iff_forall_ne_adj]

Depends on / 依赖: eq_top_iff_forall_ne_adj
-/
theorem ne_top_iff_exists_not_adj : G != ⊤ ↔ exists a b : V, a != b ∧ ¬G.Adj a b := by
  simp [eq_top_iff_forall_ne_adj]

variable (G)

@[simps]
instance (V : Type u) : Inhabited (SimpleGraph V) :=
  ⟨⊥⟩

/--
Instance `uniqueOfSubsingleton` / 实例 `uniqueOfSubsingleton`

English:
instance uniqueOfSubsingleton
  signature: [Subsingleton V]
  body: ⊥
  uniq G := by ext a b; have := Subsingleton.elim a b; simp [this]

中文:
实例 uniqueOfSubsingleton
  签名: [Subsingleton V]
  定义体: ⊥
  uniq G := by ext a b; have := Subsingleton.elim a b; simp [this]
-/
instance uniqueOfSubsingleton [Subsingleton V] : Unique (SimpleGraph V) where
  default := ⊥
  uniq G := by ext a b; have := Subsingleton.elim a b; simp [this]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Nontrivial
  signature: V] : Nontrivial (SimpleGraph V)
  body: ⟨⟨⊥, ⊤, fun h => not_subsingleton V ⟨by simpa only [← adj_inj, funext_iff, bot_adj,
    top_adj, ne_eq, eq_iff_iff, false_iff, not_not] using h⟩⟩⟩

中文:
实例 [Nontrivial
  签名: V] : Nontrivial (SimpleGraph V)
  定义体: ⟨⟨⊥, ⊤, fun h => not_subsingleton V ⟨by simpa only [← adj_inj, funext_iff, bot_adj,
    top_adj, ne_eq, eq_iff_iff, false_iff, not_not] using h⟩⟩⟩

Depends on / 依赖: adj_inj, bot_adj, eq_iff_iff, false_iff, funext_iff, ne_eq, not_not, not_subsingleton, top_adj
-/
instance [Nontrivial V] : Nontrivial (SimpleGraph V) :=
  ⟨⟨⊥, ⊤, fun h => not_subsingleton V ⟨by simpa only [← adj_inj, funext_iff, bot_adj,
    top_adj, ne_eq, eq_iff_iff, false_iff, not_not] using h⟩⟩⟩

section Decidable

variable (V) (H : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel H.Adj]

/--
Instance `Bot.adjDecidable` / 实例 `Bot.adjDecidable`

English:
instance Bot.adjDecidable
  signature: : DecidableRel (⊥ : SimpleGraph V).Adj
  body: inferInstanceAs DecidableRel fun _ _ => False

中文:
实例 Bot.adjDecidable
  签名: : DecidableRel (⊥ : SimpleGraph V).Adj
  定义体: inferInstanceAs DecidableRel fun _ _ => False
-/
instance Bot.adjDecidable : DecidableRel (⊥ : SimpleGraph V).Adj :=
inferInstanceAs DecidableRel fun _ _ => False

/--
Instance `Sup.adjDecidable` / 实例 `Sup.adjDecidable`

English:
instance Sup.adjDecidable
  signature: : DecidableRel (G ⊔ H).Adj
  body: inferInstanceAs DecidableRel fun v w => G.Adj v w ∨ H.Adj v w

中文:
实例 Sup.adjDecidable
  签名: : DecidableRel (G ⊔ H).Adj
  定义体: inferInstanceAs DecidableRel fun v w => G.Adj v w ∨ H.Adj v w
-/
instance Sup.adjDecidable : DecidableRel (G ⊔ H).Adj :=
inferInstanceAs DecidableRel fun v w => G.Adj v w ∨ H.Adj v w

/--
Instance `Inf.adjDecidable` / 实例 `Inf.adjDecidable`

English:
instance Inf.adjDecidable
  signature: : DecidableRel (G ⊓ H).Adj
  body: inferInstanceAs DecidableRel fun v w => G.Adj v w ∧ H.Adj v w

中文:
实例 Inf.adjDecidable
  签名: : DecidableRel (G ⊓ H).Adj
  定义体: inferInstanceAs DecidableRel fun v w => G.Adj v w ∧ H.Adj v w
-/
instance Inf.adjDecidable : DecidableRel (G ⊓ H).Adj :=
inferInstanceAs DecidableRel fun v w => G.Adj v w ∧ H.Adj v w

/--
Instance `Sdiff.adjDecidable` / 实例 `Sdiff.adjDecidable`

English:
instance Sdiff.adjDecidable
  signature: : DecidableRel (G \ H).Adj
  body: inferInstanceAs DecidableRel fun v w => G.Adj v w ∧ ¬H.Adj v w

中文:
实例 Sdiff.adjDecidable
  签名: : DecidableRel (G \ H).Adj
  定义体: inferInstanceAs DecidableRel fun v w => G.Adj v w ∧ ¬H.Adj v w

Depends on / 依赖: DecidableRel, G.Adj, H.Adj
-/
instance Sdiff.adjDecidable : DecidableRel (G \ H).Adj :=
inferInstanceAs DecidableRel fun v w => G.Adj v w ∧ ¬H.Adj v w

variable [DecidableEq V]

/--
Instance `Top.adjDecidable` / 实例 `Top.adjDecidable`

English:
instance Top.adjDecidable
  signature: : DecidableRel (⊤ : SimpleGraph V).Adj
  body: inferInstanceAs DecidableRel fun v w => v != w

中文:
实例 Top.adjDecidable
  签名: : DecidableRel (⊤ : SimpleGraph V).Adj
  定义体: inferInstanceAs DecidableRel fun v w => v != w
-/
instance Top.adjDecidable : DecidableRel (⊤ : SimpleGraph V).Adj :=
inferInstanceAs DecidableRel fun v w => v != w

/--
Instance `Compl.adjDecidable` / 实例 `Compl.adjDecidable`

English:
instance Compl.adjDecidable
  signature: : DecidableRel (Gᶜ.Adj)
  body: inferInstanceAs DecidableRel fun v w => v != w ∧ ¬G.Adj v w

中文:
实例 Compl.adjDecidable
  签名: : DecidableRel (Gᶜ.Adj)
  定义体: inferInstanceAs DecidableRel fun v w => v != w ∧ ¬G.Adj v w
-/
instance Compl.adjDecidable : DecidableRel (Gᶜ.Adj) :=
inferInstanceAs DecidableRel fun v w => v != w ∧ ¬G.Adj v w

end Decidable

end Order

/--
Definition of `support` / `support` 的定义

English:
definition support
  signature: : Set V
  body: SetRel.dom {(u, v) : V × V | G.Adj u v}

中文:
定义 support
  签名: : Set V
  定义体: SetRel.dom {(u, v) : V × V | G.Adj u v}

Depends on / 依赖: G.Adj, SetRel, SetRel.dom
-/
def support : Set V :=
  SetRel.dom {(u, v) : V × V | G.Adj u v}

/--
theorem `mem_support` / 定理 `mem_support`

English:
theorem mem_support
  given: {v : V}
  statement: v in G.support ↔ exists w, G.Adj v w
  proof: Iff.rfl

中文:
定理 mem_support
  条件: {v : V}
  结论: v in G.support ↔ 存在 w, G.Adj v w
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_support {v : V} : v in G.support ↔ exists w, G.Adj v w :=
  Iff.rfl

variable {G} in
/--
theorem `Adj.mem_support_left` / 定理 `Adj.mem_support_left`

English:
theorem Adj.mem_support_left
  given: (hadj : G.Adj u v)
  statement: u in G.support
  proof: G.mem_support.mpr ⟨v, hadj⟩

中文:
定理 Adj.mem_support_left
  条件: (hadj : G.Adj u v)
  结论: u in G.support
  证明: G.mem_support.mpr ⟨v, hadj⟩

Depends on / 依赖: G.mem_support.mpr, mem_support
-/
theorem Adj.mem_support_left (hadj : G.Adj u v) : u in G.support :=
  G.mem_support.mpr ⟨v, hadj⟩

variable {G} in
/--
theorem `Adj.mem_support_right` / 定理 `Adj.mem_support_right`

English:
theorem Adj.mem_support_right
  given: (hadj : G.Adj u v)
  statement: v in G.support
  proof: hadj.symm.mem_support_left

@[gcongr]

中文:
定理 Adj.mem_support_right
  条件: (hadj : G.Adj u v)
  结论: v in G.support
  证明: hadj.symm.mem_support_left

@[gcongr]

Depends on / 依赖: hadj.symm.mem_support_left, mem_support_left
-/
theorem Adj.mem_support_right (hadj : G.Adj u v) : v in G.support :=
  hadj.symm.mem_support_left

@[gcongr]
/--
theorem `support_mono` / 定理 `support_mono`

English:
theorem support_mono
  given: {G G' : SimpleGraph V} (h : G <= G')
  statement: G.support subseteq G'.support
  proof: SetRel.dom_mono fun _uv huv => h huv

中文:
定理 support_mono
  条件: {G G' : SimpleGraph V} (h : G <= G')
  结论: G.support subseteq G'.support
  证明: SetRel.dom_mono fun _uv huv => h huv

Depends on / 依赖: SetRel, SetRel.dom_mono, dom_mono
-/
theorem support_mono {G G' : SimpleGraph V} (h : G <= G') : G.support subseteq G'.support :=
  SetRel.dom_mono fun _uv huv => h huv

/--
theorem `Adj.left_mem_support` / 定理 `Adj.left_mem_support`

English:
theorem Adj.left_mem_support
  given: (hadj : G.Adj u v)
  statement: u in G.support
  proof: ⟨v, hadj⟩

中文:
定理 Adj.left_mem_support
  条件: (hadj : G.Adj u v)
  结论: u in G.support
  证明: ⟨v, hadj⟩
-/
theorem Adj.left_mem_support (hadj : G.Adj u v) : u in G.support :=
  ⟨v, hadj⟩

/--
theorem `Adj.right_mem_support` / 定理 `Adj.right_mem_support`

English:
theorem Adj.right_mem_support
  given: (hadj : G.Adj u v)
  statement: v in G.support
  proof: hadj.symm.left_mem_support

中文:
定理 Adj.right_mem_support
  条件: (hadj : G.Adj u v)
  结论: v in G.support
  证明: hadj.symm.left_mem_support

Depends on / 依赖: hadj.symm.left_mem_support, left_mem_support
-/
theorem Adj.right_mem_support (hadj : G.Adj u v) : v in G.support :=
  hadj.symm.left_mem_support

/--
theorem `support_top_of_nontrivial` / 定理 `support_top_of_nontrivial`

English:
theorem support_top_of_nontrivial
  given: [Nontrivial V]
  statement: (⊤ : SimpleGraph V).support = Set.univ
  proof: .imp fun _v₂ h => h.symm Set.eq_univ_of_forall fun v₁ => exists_ne v₁

中文:
定理 support_top_of_nontrivial
  条件: [Nontrivial V]
  结论: (⊤ : SimpleGraph V).support = Set.univ
  证明: .imp fun _v₂ h => h.symm Set.eq_univ_of_forall fun v₁ => exists_ne v₁

Depends on / 依赖: Set.eq_univ_of_forall, eq_univ_of_forall, exists_ne, h.symm
-/
theorem support_top_of_nontrivial [Nontrivial V] : (⊤ : SimpleGraph V).support = Set.univ :=
.imp fun _v₂ h => h.symm Set.eq_univ_of_forall fun v₁ => exists_ne v₁

/-- The support of the empty graph is empty. -/
@[simp]
/--
theorem `support_bot` / 定理 `support_bot`

English:
theorem support_bot
  statement: (⊥ : SimpleGraph V).support = ∅
  proof: SetRel.dom_eq_empty_iff.mpr Set.empty_def.symm

中文:
定理 support_bot
  结论: (⊥ : SimpleGraph V).support = ∅
  证明: SetRel.dom_eq_empty_iff.mpr Set.empty_def.symm

Depends on / 依赖: Set.empty_def.symm, SetRel, SetRel.dom_eq_empty_iff.mpr, dom_eq_empty_iff, empty_def
-/
theorem support_bot : (⊥ : SimpleGraph V).support = ∅ :=
SetRel.dom_eq_empty_iff.mpr Set.empty_def.symm

/-- Only the empty graph has empty support. -/
@[simp]
/--
theorem `support_eq_bot_iff` / 定理 `support_eq_bot_iff`

English:
theorem support_eq_bot_iff
  statement: G.support = ∅ ↔ G = ⊥
  proof: ⟨fun h => eq_bot_iff_forall_not_adj.mpr fun v w nadj =>
.elim, .mp nadj Set.ext_iff.mp (SetRel.dom_eq_empty_iff.mp h) (v, w)
   (· ▸ support_bot)⟩

中文:
定理 support_eq_bot_iff
  结论: G.support = ∅ ↔ G = ⊥
  证明: ⟨fun h => eq_bot_iff_forall_not_adj.mpr fun v w nadj =>
.elim, .mp nadj Set.ext_iff.mp (SetRel.dom_eq_empty_iff.mp h) (v, w)
   (· ▸ support_bot)⟩

Depends on / 依赖: Set.ext_iff.mp, SetRel, SetRel.dom_eq_empty_iff.mp, dom_eq_empty_iff, eq_bot_iff_forall_not_adj, eq_bot_iff_forall_not_adj.mpr, ext_iff, support_bot
-/
theorem support_eq_bot_iff : G.support = ∅ ↔ G = ⊥ :=
  ⟨fun h => eq_bot_iff_forall_not_adj.mpr fun v w nadj =>
.elim, .mp nadj Set.ext_iff.mp (SetRel.dom_eq_empty_iff.mp h) (v, w)
   (· ▸ support_bot)⟩

/-- The support of a graph is empty if there at most one vertex. -/
@[simp]
/--
theorem `support_of_subsingleton` / 定理 `support_of_subsingleton`

English:
theorem support_of_subsingleton
  given: [Subsingleton V]
  statement: G.support = ∅
  proof: uniqueOfSubsingleton.uniq G ▸ support_bot

中文:
定理 support_of_subsingleton
  条件: [Subsingleton V]
  结论: G.support = ∅
  证明: uniqueOfSubsingleton.uniq G ▸ support_bot

Depends on / 依赖: support_bot, uniqueOfSubsingleton, uniqueOfSubsingleton.uniq
-/
theorem support_of_subsingleton [Subsingleton V] : G.support = ∅ :=
  uniqueOfSubsingleton.uniq G ▸ support_bot

/--
Definition of `neighborSet` / `neighborSet` 的定义

English:
definition neighborSet
  signature: (v : V)
  body: {w | G.Adj v w}

中文:
定义 neighborSet
  签名: (v : V)
  定义体: {w | G.Adj v w}

Depends on / 依赖: G.Adj
-/
def neighborSet (v : V) : Set V := {w | G.Adj v w}

/--
Instance `neighborSet.memDecidable` / 实例 `neighborSet.memDecidable`

English:
instance neighborSet.memDecidable
  signature: (v : V) [DecidableRel G.Adj]
  body: inferInstanceAs DecidablePred (Adj G v)

中文:
实例 neighborSet.memDecidable
  签名: (v : V) [DecidableRel G.Adj]
  定义体: inferInstanceAs DecidablePred (Adj G v)

Depends on / 依赖: DecidablePred
-/
instance neighborSet.memDecidable (v : V) [DecidableRel G.Adj] :
    DecidablePred (· in G.neighborSet v) :=
inferInstanceAs DecidablePred (Adj G v)

/--
lemma `neighborSet_subset_support` / 引理 `neighborSet_subset_support`

English:
lemma neighborSet_subset_support
  given: (v : V)
  statement: G.neighborSet v subseteq G.support
  proof: fun _ hadj => ⟨v, hadj.symm⟩

中文:
引理 neighborSet_subset_support
  条件: (v : V)
  结论: G.neighborSet v subseteq G.support
  证明: fun _ hadj => ⟨v, hadj.symm⟩

Depends on / 依赖: hadj.symm
-/
lemma neighborSet_subset_support (v : V) : G.neighborSet v subseteq G.support :=
  fun _ hadj => ⟨v, hadj.symm⟩

section EdgeSet

variable {G₁ G₂ : SimpleGraph V}

-- Porting note: We need a separate definition so that dot notation works.
/--
Definition of `edgeSetEmbedding` / `edgeSetEmbedding` 的定义

English:
definition edgeSetEmbedding
  signature: (V : Type*)
  body: OrderEmbedding.ofMapLEIff (fun G => Sym2.fromRel G.symm) fun _ _ =>
    ⟨fun h a b => @h s(a, b), fun h e => Sym2.ind @h e⟩

中文:
定义 edgeSetEmbedding
  签名: (V : 类型)
  定义体: OrderEmbedding.ofMapLEIff (fun G => Sym2.fromRel G.symm) fun _ _ =>
    ⟨fun h a b => @h s(a, b), fun h e => Sym2.ind @h e⟩

Depends on / 依赖: G.symm, OrderEmbedding, OrderEmbedding.ofMapLEIff, Sym2.fromRel, Sym2.ind, fromRel, ofMapLEIff
-/
def edgeSetEmbedding (V : Type*) : SimpleGraph V ↪o Set (Sym2 V) :=
  OrderEmbedding.ofMapLEIff (fun G => Sym2.fromRel G.symm) fun _ _ =>
    ⟨fun h a b => @h s(a, b), fun h e => Sym2.ind @h e⟩

/--
Definition of `edgeSet` / `edgeSet` 的定义

English:
abbreviation edgeSet
  signature: (G : SimpleGraph V)
  body: edgeSetEmbedding V G

@[simp]

中文:
缩写 edgeSet
  签名: (G : SimpleGraph V)
  定义体: edgeSetEmbedding V G

@[simp]

Depends on / 依赖: edgeSetEmbedding
-/
abbrev edgeSet (G : SimpleGraph V) : Set (Sym2 V) := edgeSetEmbedding V G

@[simp]
/--
theorem `mem_edgeSet` / 定理 `mem_edgeSet`

English:
theorem mem_edgeSet
  statement: s(v, w) in G.edgeSet ↔ G.Adj v w
  proof: Iff.rfl

中文:
定理 mem_edgeSet
  结论: s(v, w) in G.edgeSet ↔ G.Adj v w
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_edgeSet : s(v, w) in G.edgeSet ↔ G.Adj v w :=
  Iff.rfl

/--
theorem `not_isDiag_of_mem_edgeSet` / 定理 `not_isDiag_of_mem_edgeSet`

English:
theorem not_isDiag_of_mem_edgeSet
  statement: e in edgeSet G -> ¬e.IsDiag
  proof: Sym2.ind (fun _ _ => Adj.ne) e

中文:
定理 not_isDiag_of_mem_edgeSet
  结论: e in edgeSet G -> ¬e.IsDiag
  证明: Sym2.ind (fun _ _ => Adj.ne) e

Depends on / 依赖: Adj.ne, Sym2.ind
-/
theorem not_isDiag_of_mem_edgeSet : e in edgeSet G -> ¬e.IsDiag :=
  Sym2.ind (fun _ _ => Adj.ne) e

/--
lemma `not_mem_edgeSet_of_isDiag` / 引理 `not_mem_edgeSet_of_isDiag`

English:
lemma not_mem_edgeSet_of_isDiag
  statement: e.IsDiag -> e ∉ edgeSet G
  proof: imp_not_comm.1 G.not_isDiag_of_mem_edgeSet

alias _root_.Sym2.IsDiag.not_mem_edgeSet := not_mem_edgeSet_of_isDiag

中文:
引理 not_mem_edgeSet_of_isDiag
  结论: e.IsDiag -> e ∉ edgeSet G
  证明: imp_not_comm.1 G.not_isDiag_of_mem_edgeSet

alias _root_.Sym2.IsDiag.not_mem_edgeSet := not_mem_edgeSet_of_isDiag
-/
@[simp] lemma not_mem_edgeSet_of_isDiag : e.IsDiag -> e ∉ edgeSet G :=
  imp_not_comm.1 G.not_isDiag_of_mem_edgeSet

alias _root_.Sym2.IsDiag.not_mem_edgeSet := not_mem_edgeSet_of_isDiag

/--
theorem `edgeSet_inj` / 定理 `edgeSet_inj`

English:
theorem edgeSet_inj
  statement: G₁.edgeSet = G₂.edgeSet ↔ G₁ = G₂
  proof: (edgeSetEmbedding V).eq_iff_eq

中文:
定理 edgeSet_inj
  结论: G₁.edgeSet = G₂.edgeSet ↔ G₁ = G₂
  证明: (edgeSetEmbedding V).eq_iff_eq

Depends on / 依赖: edgeSetEmbedding, eq_iff_eq
-/
theorem edgeSet_inj : G₁.edgeSet = G₂.edgeSet ↔ G₁ = G₂ := (edgeSetEmbedding V).eq_iff_eq

/--
theorem `edgeSet_subset_edgeSet` / 定理 `edgeSet_subset_edgeSet`

English:
theorem edgeSet_subset_edgeSet
  statement: edgeSet G₁ subseteq edgeSet G₂ ↔ G₁ <= G₂
  proof: by simp

中文:
定理 edgeSet_subset_edgeSet
  结论: edgeSet G₁ subseteq edgeSet G₂ ↔ G₁ <= G₂
  证明: by simp
-/
theorem edgeSet_subset_edgeSet : edgeSet G₁ subseteq edgeSet G₂ ↔ G₁ <= G₂ := by simp

/--
theorem `edgeSet_ssubset_edgeSet` / 定理 `edgeSet_ssubset_edgeSet`

English:
theorem edgeSet_ssubset_edgeSet
  statement: edgeSet G₁ ⊂ edgeSet G₂ ↔ G₁ < G₂
  proof: by simp

中文:
定理 edgeSet_ssubset_edgeSet
  结论: edgeSet G₁ ⊂ edgeSet G₂ ↔ G₁ < G₂
  证明: by simp
-/
theorem edgeSet_ssubset_edgeSet : edgeSet G₁ ⊂ edgeSet G₂ ↔ G₁ < G₂ := by simp

/--
theorem `edgeSet_injective` / 定理 `edgeSet_injective`

English:
theorem edgeSet_injective
  statement: Injective (edgeSet : SimpleGraph V -> Set (Sym2 V))
  proof: (edgeSetEmbedding V).injective

@[gcongr] alias ⟨_, edgeSet_mono⟩ := edgeSet_subset_edgeSet

@[gcongr] alias ⟨_, edgeSet_strict_mono⟩ := edgeSet_ssubset_edgeSet

中文:
定理 edgeSet_injective
  结论: Injective (edgeSet : SimpleGraph V -> Set (Sym2 V))
  证明: (edgeSetEmbedding V).injective

@[gcongr] alias ⟨_, edgeSet_mono⟩ := edgeSet_subset_edgeSet

@[gcongr] alias ⟨_, edgeSet_strict_mono⟩ := edgeSet_ssubset_edgeSet

Depends on / 依赖: edgeSetEmbedding, injective
-/
theorem edgeSet_injective : Injective (edgeSet : SimpleGraph V -> Set (Sym2 V)) :=
  (edgeSetEmbedding V).injective

@[gcongr] alias ⟨_, edgeSet_mono⟩ := edgeSet_subset_edgeSet

@[gcongr] alias ⟨_, edgeSet_strict_mono⟩ := edgeSet_ssubset_edgeSet

attribute [mono] edgeSet_mono edgeSet_strict_mono

variable (G₁ G₂)

@[simp]
/--
theorem `edgeSet_bot` / 定理 `edgeSet_bot`

English:
theorem edgeSet_bot
  statement: (⊥ : SimpleGraph V).edgeSet = ∅
  proof: Sym2.fromRel_bot

@[simp]

中文:
定理 edgeSet_bot
  结论: (⊥ : SimpleGraph V).edgeSet = ∅
  证明: Sym2.fromRel_bot

@[simp]

Depends on / 依赖: Sym2.fromRel_bot, fromRel_bot
-/
theorem edgeSet_bot : (⊥ : SimpleGraph V).edgeSet = ∅ :=
  Sym2.fromRel_bot

@[simp]
/--
theorem `edgeSet_top` / 定理 `edgeSet_top`

English:
theorem edgeSet_top
  statement: (⊤ : SimpleGraph V).edgeSet = Sym2.diagSetᶜ
  proof: Sym2.diagSet_compl_eq_fromRel_ne.symm

@[simp]

中文:
定理 edgeSet_top
  结论: (⊤ : SimpleGraph V).edgeSet = Sym2.diagSetᶜ
  证明: Sym2.diagSet_compl_eq_fromRel_ne.symm

@[simp]

Depends on / 依赖: Sym2.diagSet_compl_eq_fromRel_ne.symm, diagSet_compl_eq_fromRel_ne
-/
theorem edgeSet_top : (⊤ : SimpleGraph V).edgeSet = Sym2.diagSetᶜ :=
  Sym2.diagSet_compl_eq_fromRel_ne.symm

@[simp]
/--
theorem `edgeSet_subset_compl_diagSet` / 定理 `edgeSet_subset_compl_diagSet`

English:
theorem edgeSet_subset_compl_diagSet
  statement: G.edgeSet subseteq Sym2.diagSetᶜ
  proof: by
  simpa [Set.subset_compl_iff_disjoint_left, edgeSet, edgeSetEmbedding] using G.loopless

@[simp]

中文:
定理 edgeSet_subset_compl_diagSet
  结论: G.edgeSet subseteq Sym2.diagSetᶜ
  证明: by
  simpa [Set.subset_compl_iff_disjoint_left, edgeSet, edgeSetEmbedding] using G.loopless

@[simp]

Depends on / 依赖: G.loopless, Set.subset_compl_iff_disjoint_left, edgeSet, edgeSetEmbedding, loopless, subset_compl_iff_disjoint_left
-/
theorem edgeSet_subset_compl_diagSet : G.edgeSet subseteq Sym2.diagSetᶜ := by
  simpa [Set.subset_compl_iff_disjoint_left, edgeSet, edgeSetEmbedding] using G.loopless

@[simp]
/--
theorem `edgeSet_sup` / 定理 `edgeSet_sup`

English:
theorem edgeSet_sup
  statement: (G₁ ⊔ G₂).edgeSet = G₁.edgeSet union G₂.edgeSet
  proof: by
  ext ⟨x, y⟩
  rfl

@[simp]

中文:
定理 edgeSet_sup
  结论: (G₁ ⊔ G₂).edgeSet = G₁.edgeSet union G₂.edgeSet
  证明: by
  ext ⟨x, y⟩
  rfl

@[simp]
-/
theorem edgeSet_sup : (G₁ ⊔ G₂).edgeSet = G₁.edgeSet union G₂.edgeSet := by
  ext ⟨x, y⟩
  rfl

@[simp]
/--
theorem `edgeSet_inf` / 定理 `edgeSet_inf`

English:
theorem edgeSet_inf
  statement: (G₁ ⊓ G₂).edgeSet = G₁.edgeSet inter G₂.edgeSet
  proof: by
  ext ⟨x, y⟩
  rfl

中文:
定理 edgeSet_inf
  结论: (G₁ ⊓ G₂).edgeSet = G₁.edgeSet inter G₂.edgeSet
  证明: by
  ext ⟨x, y⟩
  rfl
-/
theorem edgeSet_inf : (G₁ ⊓ G₂).edgeSet = G₁.edgeSet inter G₂.edgeSet := by
  ext ⟨x, y⟩
  rfl

/--
theorem `edgeSet_sSup` / 定理 `edgeSet_sSup`

English:
theorem edgeSet_sSup
  given: {s : Set (SimpleGraph V)}
  statement: (sSup s).edgeSet = ⋃₀ (edgeSet '' s)
  proof: by
  ext ⟨x, y⟩
  simp

中文:
定理 edgeSet_sSup
  条件: {s : Set (SimpleGraph V)}
  结论: (sSup s).edgeSet = ⋃₀ (edgeSet '' s)
  证明: by
  ext ⟨x, y⟩
  simp
-/
theorem edgeSet_sSup {s : Set (SimpleGraph V)} : (sSup s).edgeSet = ⋃₀ (edgeSet '' s) := by
  ext ⟨x, y⟩
  simp

/--
theorem `edgeSet_sInf` / 定理 `edgeSet_sInf`

English:
theorem edgeSet_sInf
  given: {s : Set (SimpleGraph V)} (h : s.Nonempty)
  proof: by
  ext ⟨x, y⟩
  have ⟨G, hG⟩ := h
  simpa using (· G hG |>.ne)

中文:
定理 edgeSet_sInf
  条件: {s : Set (SimpleGraph V)} (h : s.Nonempty)
  证明: by
  ext ⟨x, y⟩
  have ⟨G, hG⟩ := h
  simpa using (· G hG |>.ne)
-/
theorem edgeSet_sInf {s : Set (SimpleGraph V)} (h : s.Nonempty) :
    (sInf s).edgeSet = ⋂₀ (edgeSet '' s) := by
  ext ⟨x, y⟩
  have ⟨G, hG⟩ := h
  simpa using (· G hG |>.ne)

/--
theorem `edgeSet_iSup` / 定理 `edgeSet_iSup`

English:
theorem edgeSet_iSup
  given: {ι : Sort*} {f : ι -> SimpleGraph V}
  proof: by
  ext ⟨x, y⟩
  simp

中文:
定理 edgeSet_iSup
  条件: {ι : Sort*} {f : ι -> SimpleGraph V}
  证明: by
  ext ⟨x, y⟩
  simp
-/
theorem edgeSet_iSup {ι : Sort*} {f : ι -> SimpleGraph V} :
    (⨆ i, f i).edgeSet = ⋃ i, (f i).edgeSet := by
  ext ⟨x, y⟩
  simp

/--
theorem `edgeSet_iInf` / 定理 `edgeSet_iInf`

English:
theorem edgeSet_iInf
  given: {ι : Sort*} [Nonempty ι] {f : ι -> SimpleGraph V}
  proof: by
  ext ⟨x, y⟩
  have ⟨i⟩ := ‹Nonempty ι›
  simpa using (· i |>.ne)

@[simp]

中文:
定理 edgeSet_iInf
  条件: {ι : Sort*} [Nonempty ι] {f : ι -> SimpleGraph V}
  证明: by
  ext ⟨x, y⟩
  have ⟨i⟩ := ‹Nonempty ι›
  simpa using (· i |>.ne)

@[simp]

Depends on / 依赖: Nonempty
-/
theorem edgeSet_iInf {ι : Sort*} [Nonempty ι] {f : ι -> SimpleGraph V} :
    (⨅ i, f i).edgeSet = ⋂ i, (f i).edgeSet := by
  ext ⟨x, y⟩
  have ⟨i⟩ := ‹Nonempty ι›
  simpa using (· i |>.ne)

@[simp]
/--
theorem `edgeSet_sdiff` / 定理 `edgeSet_sdiff`

English:
theorem edgeSet_sdiff
  statement: (G₁ \ G₂).edgeSet = G₁.edgeSet \ G₂.edgeSet
  proof: by
  ext ⟨x, y⟩
  rfl

中文:
定理 edgeSet_sdiff
  结论: (G₁ \ G₂).edgeSet = G₁.edgeSet \ G₂.edgeSet
  证明: by
  ext ⟨x, y⟩
  rfl
-/
theorem edgeSet_sdiff : (G₁ \ G₂).edgeSet = G₁.edgeSet \ G₂.edgeSet := by
  ext ⟨x, y⟩
  rfl

variable {G G₁ G₂}

/--
lemma `disjoint_edgeSet` / 引理 `disjoint_edgeSet`

English:
lemma disjoint_edgeSet
  statement: Disjoint G₁.edgeSet G₂.edgeSet ↔ Disjoint G₁ G₂
  proof: by
  rw [Set.disjoint_iff]; rw [disjoint_iff_inf_le]; rw [← edgeSet_inf]; rw [← edgeSet_bot]; rw [OrderEmbedding.le_iff_le]

中文:
引理 disjoint_edgeSet
  结论: Disjoint G₁.edgeSet G₂.edgeSet ↔ Disjoint G₁ G₂
  证明: by
  rw [Set.disjoint_iff]; rw [disjoint_iff_inf_le]; rw [← edgeSet_inf]; rw [← edgeSet_bot]; rw [OrderEmbedding.le_iff_le]
-/
@[simp] lemma disjoint_edgeSet : Disjoint G₁.edgeSet G₂.edgeSet ↔ Disjoint G₁ G₂ := by
  rw [Set.disjoint_iff]; rw [disjoint_iff_inf_le]; rw [← edgeSet_inf]; rw [← edgeSet_bot]; rw [OrderEmbedding.le_iff_le]

/--
theorem `disjoint_of_disjoint_support` / 定理 `disjoint_of_disjoint_support`

English:
theorem disjoint_of_disjoint_support
  given: (h : Disjoint G.support H.support)
  statement: Disjoint G H
  proof: by
  simp_rw [Set.disjoint_left, mem_support] at h
  rw [← disjoint_edgeSet]; rw [Set.disjoint_left]; rw [Sym2.forall]
  grind [mem_edgeSet]

中文:
定理 disjoint_of_disjoint_support
  条件: (h : Disjoint G.support H.support)
  结论: Disjoint G H
  证明: by
  simp_rw [Set.disjoint_left, mem_support] at h
  rw [← disjoint_edgeSet]; rw [Set.disjoint_left]; rw [Sym2.forall]
  grind [mem_edgeSet]

Depends on / 依赖: Set.disjoint_left, Sym2.forall, disjoint_edgeSet, disjoint_left, mem_edgeSet, mem_support, simp_rw
-/
theorem disjoint_of_disjoint_support (h : Disjoint G.support H.support) : Disjoint G H := by
  simp_rw [Set.disjoint_left, mem_support] at h
  rw [← disjoint_edgeSet]; rw [Set.disjoint_left]; rw [Sym2.forall]
  grind [mem_edgeSet]

/--
lemma `edgeSet_eq_empty` / 引理 `edgeSet_eq_empty`

English:
lemma edgeSet_eq_empty
  statement: G.edgeSet = ∅ ↔ G = ⊥
  proof: by rw [← edgeSet_bot, edgeSet_inj]

中文:
引理 edgeSet_eq_empty
  结论: G.edgeSet = ∅ ↔ G = ⊥
  证明: by rw [← edgeSet_bot, edgeSet_inj]
-/
@[simp] lemma edgeSet_eq_empty : G.edgeSet = ∅ ↔ G = ⊥ := by rw [← edgeSet_bot, edgeSet_inj]

/--
lemma `edgeSet_nonempty` / 引理 `edgeSet_nonempty`

English:
lemma edgeSet_nonempty
  statement: G.edgeSet.Nonempty ↔ G != ⊥
  proof: by
  rw [Set.nonempty_iff_ne_empty]; rw [edgeSet_eq_empty.ne]

中文:
引理 edgeSet_nonempty
  结论: G.edgeSet.Nonempty ↔ G != ⊥
  证明: by
  rw [Set.nonempty_iff_ne_empty]; rw [edgeSet_eq_empty.ne]
-/
@[simp] lemma edgeSet_nonempty : G.edgeSet.Nonempty ↔ G != ⊥ := by
  rw [Set.nonempty_iff_ne_empty]; rw [edgeSet_eq_empty.ne]

/-- This lemma, combined with `edgeSet_sdiff` and `edgeSet_fromEdgeSet`,
allows proving `(G \ fromEdgeSet s).edgeSet = G.edgeSet \ s` by `simp`. -/
@[simp]
/--
theorem `edgeSet_sdiff_sdiff_isDiag` / 定理 `edgeSet_sdiff_sdiff_isDiag`

English:
theorem edgeSet_sdiff_sdiff_isDiag
  given: (G : SimpleGraph V) (s : Set (Sym2 V))
  proof: by
  grind [Sym2.mem_diagSet, not_isDiag_of_mem_edgeSet]

中文:
定理 edgeSet_sdiff_sdiff_isDiag
  条件: (G : SimpleGraph V) (s : Set (Sym2 V))
  证明: by
  grind [Sym2.mem_diagSet, not_isDiag_of_mem_edgeSet]

Depends on / 依赖: Sym2.mem_diagSet, mem_diagSet, not_isDiag_of_mem_edgeSet
-/
theorem edgeSet_sdiff_sdiff_isDiag (G : SimpleGraph V) (s : Set (Sym2 V)) :
    G.edgeSet \ (s \ Sym2.diagSet) = G.edgeSet \ s := by
  grind [Sym2.mem_diagSet, not_isDiag_of_mem_edgeSet]

/--
theorem `adj_iff_exists_edge` / 定理 `adj_iff_exists_edge`

English:
theorem adj_iff_exists_edge
  given: {v w : V}
  statement: G.Adj v w ↔ v != w ∧ exists e in G.edgeSet, v in e ∧ w in e
  proof: by
  refine ⟨fun _ => ⟨G.ne_of_adj ‹_›, s(v, w), by simpa⟩, ?_⟩
  rintro ⟨hne, e, he, hv⟩
  rw [Sym2.mem_and_mem_iff hne] at hv
  subst e
  rwa [mem_edgeSet] at he

中文:
定理 adj_iff_exists_edge
  条件: {v w : V}
  结论: G.Adj v w ↔ v != w ∧ 存在 e in G.edgeSet, v in e ∧ w in e
  证明: by
  refine ⟨fun _ => ⟨G.ne_of_adj ‹_›, s(v, w), by simpa⟩, ?_⟩
  rintro ⟨hne, e, he, hv⟩
  rw [Sym2.mem_and_mem_iff hne] at hv
  subst e
  rwa [mem_edgeSet] at he

Depends on / 依赖: G.ne_of_adj, Sym2.mem_and_mem_iff, mem_and_mem_iff, mem_edgeSet, ne_of_adj
-/
theorem adj_iff_exists_edge {v w : V} : G.Adj v w ↔ v != w ∧ exists e in G.edgeSet, v in e ∧ w in e := by
  refine ⟨fun _ => ⟨G.ne_of_adj ‹_›, s(v, w), by simpa⟩, ?_⟩
  rintro ⟨hne, e, he, hv⟩
  rw [Sym2.mem_and_mem_iff hne] at hv
  subst e
  rwa [mem_edgeSet] at he

/--
theorem `adj_iff_exists_edge_coe` / 定理 `adj_iff_exists_edge_coe`

English:
theorem adj_iff_exists_edge_coe
  statement: G.Adj a b ↔ exists e : G.edgeSet, e.val = s(a, b)
  proof: by
  simp only [mem_edgeSet, exists_prop, SetCoe.exists, exists_eq_right]

@[simp]

中文:
定理 adj_iff_exists_edge_coe
  结论: G.Adj a b ↔ 存在 e : G.edgeSet, e.val = s(a, b)
  证明: by
  simp only [mem_edgeSet, exists_prop, SetCoe.exists, exists_eq_right]

@[simp]

Depends on / 依赖: SetCoe, SetCoe.exists, exists_eq_right, exists_prop, mem_edgeSet
-/
theorem adj_iff_exists_edge_coe : G.Adj a b ↔ exists e : G.edgeSet, e.val = s(a, b) := by
  simp only [mem_edgeSet, exists_prop, SetCoe.exists, exists_eq_right]

@[simp]
/--
theorem `edgeSet_subset_sym2_iff` / 定理 `edgeSet_subset_sym2_iff`

English:
theorem edgeSet_subset_sym2_iff
  given: {s : Set V}
  proof: by
  refine ⟨fun h u hu => ?_, fun h e hadj => ?_⟩
  · have ⟨v, huv⟩ := hu
    exact (Set.mk_mem_sym2_iff.mp <| h huv).left
  · cases e
    exact ⟨h hadj.mem_support_left, h hadj.mem_support_right⟩

中文:
定理 edgeSet_subset_sym2_iff
  条件: {s : Set V}
  证明: by
  refine ⟨fun h u hu => ?_, fun h e hadj => ?_⟩
  · have ⟨v, huv⟩ := hu
    exact (Set.mk_mem_sym2_iff.mp <| h huv).left
  · cases e
    exact ⟨h hadj.mem_support_left, h hadj.mem_support_right⟩

Depends on / 依赖: Set.mk_mem_sym2_iff.mp, hadj.mem_support_left, hadj.mem_support_right, mem_support_left, mem_support_right, mk_mem_sym2_iff
-/
theorem edgeSet_subset_sym2_iff {s : Set V} :
    G.edgeSet subseteq s.sym2 ↔ G.support subseteq s := by
  refine ⟨fun h u hu => ?_, fun h e hadj => ?_⟩
  · have ⟨v, huv⟩ := hu
    exact (Set.mk_mem_sym2_iff.mp <| h huv).left
  · cases e
    exact ⟨h hadj.mem_support_left, h hadj.mem_support_right⟩

variable (G G₁ G₂)

/--
theorem `edge_other_ne` / 定理 `edge_other_ne`

English:
theorem edge_other_ne
  given: {e : Sym2 V} (he : e in G.edgeSet) {v : V} (h : v in e)
  proof: by
  rw [← Sym2.other_spec h]; rw [Sym2.eq_swap] at he
  exact G.ne_of_adj he

中文:
定理 edge_other_ne
  条件: {e : Sym2 V} (he : e in G.edgeSet) {v : V} (h : v in e)
  证明: by
  rw [← Sym2.other_spec h]; rw [Sym2.eq_swap] at he
  exact G.ne_of_adj he

Depends on / 依赖: G.ne_of_adj, Sym2.eq_swap, Sym2.other_spec, eq_swap, ne_of_adj, other_spec
-/
theorem edge_other_ne {e : Sym2 V} (he : e in G.edgeSet) {v : V} (h : v in e) :
    Sym2.Mem.other h != v := by
  rw [← Sym2.other_spec h]; rw [Sym2.eq_swap] at he
  exact G.ne_of_adj he

/--
Instance `decidableMemEdgeSet` / 实例 `decidableMemEdgeSet`

English:
instance decidableMemEdgeSet
  signature: [DecidableRel G.Adj]
  body: Sym2.fromRel.decidablePred G.symm

中文:
实例 decidableMemEdgeSet
  签名: [DecidableRel G.Adj]
  定义体: Sym2.fromRel.decidablePred G.symm

Depends on / 依赖: G.symm, Sym2.fromRel.decidablePred, decidablePred, fromRel
-/
instance decidableMemEdgeSet [DecidableRel G.Adj] : DecidablePred (· in G.edgeSet) :=
  Sym2.fromRel.decidablePred G.symm

/--
Instance `fintypeEdgeSet` / 实例 `fintypeEdgeSet`

English:
instance fintypeEdgeSet
  signature: [Fintype (Sym2 V)] [DecidableRel G.Adj]
  body: Subtype.fintype _

中文:
实例 fintypeEdgeSet
  签名: [Fintype (Sym2 V)] [DecidableRel G.Adj]
  定义体: Subtype.fintype _

Depends on / 依赖: Subtype, Subtype.fintype, fintype
-/
instance fintypeEdgeSet [Fintype (Sym2 V)] [DecidableRel G.Adj] : Fintype G.edgeSet :=
  Subtype.fintype _

/--
Instance `fintypeEdgeSetBot` / 实例 `fintypeEdgeSetBot`

English:
instance fintypeEdgeSetBot
  signature: : Fintype (⊥ : SimpleGraph V).edgeSet
  body: by
  rw [edgeSet_bot]
  infer_instance

中文:
实例 fintypeEdgeSetBot
  签名: : Fintype (⊥ : SimpleGraph V).edgeSet
  定义体: by
  rw [edgeSet_bot]
  infer_instance

Depends on / 依赖: edgeSet_bot, infer_instance
-/
instance fintypeEdgeSetBot : Fintype (⊥ : SimpleGraph V).edgeSet := by
  rw [edgeSet_bot]
  infer_instance

/--
Instance `fintypeEdgeSetSup` / 实例 `fintypeEdgeSetSup`

English:
instance fintypeEdgeSetSup
  signature: [DecidableEq V] [Fintype G₁.edgeSet] [Fintype G₂.edgeSet]
  body: by
  rw [edgeSet_sup]
  infer_instance

中文:
实例 fintypeEdgeSetSup
  签名: [DecidableEq V] [Fintype G₁.edgeSet] [Fintype G₂.edgeSet]
  定义体: by
  rw [edgeSet_sup]
  infer_instance

Depends on / 依赖: edgeSet_sup, infer_instance
-/
instance fintypeEdgeSetSup [DecidableEq V] [Fintype G₁.edgeSet] [Fintype G₂.edgeSet] :
    Fintype (G₁ ⊔ G₂).edgeSet := by
  rw [edgeSet_sup]
  infer_instance

/--
Instance `fintypeEdgeSetInf` / 实例 `fintypeEdgeSetInf`

English:
instance fintypeEdgeSetInf
  signature: [DecidableEq V] [Fintype G₁.edgeSet] [Fintype G₂.edgeSet]
  body: by
  rw [edgeSet_inf]
  exact Set.fintypeInter _ _

中文:
实例 fintypeEdgeSetInf
  签名: [DecidableEq V] [Fintype G₁.edgeSet] [Fintype G₂.edgeSet]
  定义体: by
  rw [edgeSet_inf]
  exact Set.fintypeInter _ _

Depends on / 依赖: Set.fintypeInter, edgeSet_inf, fintypeInter
-/
instance fintypeEdgeSetInf [DecidableEq V] [Fintype G₁.edgeSet] [Fintype G₂.edgeSet] :
    Fintype (G₁ ⊓ G₂).edgeSet := by
  rw [edgeSet_inf]
  exact Set.fintypeInter _ _

/--
Instance `fintypeEdgeSetSdiff` / 实例 `fintypeEdgeSetSdiff`

English:
instance fintypeEdgeSetSdiff
  signature: [DecidableEq V] [Fintype G₁.edgeSet] [Fintype G₂.edgeSet]
  body: by
  rw [edgeSet_sdiff]
  exact Set.fintypeDiff _ _

中文:
实例 fintypeEdgeSetSdiff
  签名: [DecidableEq V] [Fintype G₁.edgeSet] [Fintype G₂.edgeSet]
  定义体: by
  rw [edgeSet_sdiff]
  exact Set.fintypeDiff _ _

Depends on / 依赖: Set.fintypeDiff, edgeSet_sdiff, fintypeDiff
-/
instance fintypeEdgeSetSdiff [DecidableEq V] [Fintype G₁.edgeSet] [Fintype G₂.edgeSet] :
    Fintype (G₁ \ G₂).edgeSet := by
  rw [edgeSet_sdiff]
  exact Set.fintypeDiff _ _

end EdgeSet

section FromEdgeSet

variable (s : Set (Sym2 V))

/--
Definition of `fromEdgeSet` / `fromEdgeSet` 的定义

English:
definition fromEdgeSet
  signature: : SimpleGraph V where
  body: Sym2.ToRel s ⊓ Ne
.symm u v h.left, h.right.symm⟩ symm.symm u v h := ⟨Sym2.toRel_symm s

中文:
定义 fromEdgeSet
  签名: : SimpleGraph V where
  定义体: Sym2.ToRel s ⊓ Ne
.symm u v h.left, h.right.symm⟩ symm.symm u v h := ⟨Sym2.toRel_symm s

Depends on / 依赖: Sym2.ToRel
-/
def fromEdgeSet : SimpleGraph V where
  Adj := Sym2.ToRel s ⊓ Ne
.symm u v h.left, h.right.symm⟩ symm.symm u v h := ⟨Sym2.toRel_symm s

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [DecidablePred
  signature: (· in s)] [DecidableEq V] : DecidableRel (fromEdgeSet s).Adj
  body: inferInstanceAs DecidableRel fun v w => s(v, w) in s ∧ v != w

@[simp]

中文:
实例 [DecidablePred
  签名: (· in s)] [DecidableEq V] : DecidableRel (fromEdgeSet s).Adj
  定义体: inferInstanceAs DecidableRel fun v w => s(v, w) in s ∧ v != w

@[simp]

Depends on / 依赖: DecidableRel
-/
instance [DecidablePred (· in s)] [DecidableEq V] : DecidableRel (fromEdgeSet s).Adj :=
inferInstanceAs DecidableRel fun v w => s(v, w) in s ∧ v != w

@[simp]
/--
theorem `fromEdgeSet_adj` / 定理 `fromEdgeSet_adj`

English:
theorem fromEdgeSet_adj
  statement: (fromEdgeSet s).Adj v w ↔ s(v, w) in s ∧ v != w
  proof: Iff.rfl

中文:
定理 fromEdgeSet_adj
  结论: (fromEdgeSet s).Adj v w ↔ s(v, w) in s ∧ v != w
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem fromEdgeSet_adj : (fromEdgeSet s).Adj v w ↔ s(v, w) in s ∧ v != w :=
  Iff.rfl

-- Note: we need to make sure `fromEdgeSet_adj` and this lemma are confluent.
-- In particular, both yield `s(u, v) ∈ (fromEdgeSet s).edgeSet` ==> `s(v, w) ∈ s ∧ v ≠ w`.
@[simp]
/--
theorem `edgeSet_fromEdgeSet` / 定理 `edgeSet_fromEdgeSet`

English:
theorem edgeSet_fromEdgeSet
  statement: (fromEdgeSet s).edgeSet = s \ Sym2.diagSet
  proof: by
  ext e
  exact Sym2.ind (by simp) e

@[simp]

中文:
定理 edgeSet_fromEdgeSet
  结论: (fromEdgeSet s).edgeSet = s \ Sym2.diagSet
  证明: by
  ext e
  exact Sym2.ind (by simp) e

@[simp]

Depends on / 依赖: Sym2.ind
-/
theorem edgeSet_fromEdgeSet : (fromEdgeSet s).edgeSet = s \ Sym2.diagSet := by
  ext e
  exact Sym2.ind (by simp) e

@[simp]
/--
theorem `fromEdgeSet_edgeSet` / 定理 `fromEdgeSet_edgeSet`

English:
theorem fromEdgeSet_edgeSet
  statement: fromEdgeSet G.edgeSet = G
  proof: by
  ext v w
  exact ⟨fun h => h.1, fun h => ⟨h, G.ne_of_adj h⟩⟩

中文:
定理 fromEdgeSet_edgeSet
  结论: fromEdgeSet G.edgeSet = G
  证明: by
  ext v w
  exact ⟨fun h => h.1, fun h => ⟨h, G.ne_of_adj h⟩⟩

Depends on / 依赖: G.ne_of_adj, ne_of_adj
-/
theorem fromEdgeSet_edgeSet : fromEdgeSet G.edgeSet = G := by
  ext v w
  exact ⟨fun h => h.1, fun h => ⟨h, G.ne_of_adj h⟩⟩

/--
lemma `le_fromEdgeSet_iff` / 引理 `le_fromEdgeSet_iff`

English:
lemma le_fromEdgeSet_iff
  statement: G <= fromEdgeSet s ↔ G.edgeSet subseteq s
  proof: by
  simp [← edgeSet_subset_edgeSet, Set.subset_def]; grind [not_isDiag_of_mem_edgeSet]

中文:
引理 le_fromEdgeSet_iff
  结论: G <= fromEdgeSet s ↔ G.edgeSet subseteq s
  证明: by
  simp [← edgeSet_subset_edgeSet, Set.subset_def]; grind [not_isDiag_of_mem_edgeSet]
-/
@[simp] lemma le_fromEdgeSet_iff : G <= fromEdgeSet s ↔ G.edgeSet subseteq s := by
  simp [← edgeSet_subset_edgeSet, Set.subset_def]; grind [not_isDiag_of_mem_edgeSet]

/--
lemma `fromEdgeSet_le` / 引理 `fromEdgeSet_le`

English:
lemma fromEdgeSet_le
  given: {s : Set (Sym2 V)}
  proof: by simp [← edgeSet_subset_edgeSet]

中文:
引理 fromEdgeSet_le
  条件: {s : Set (Sym2 V)}
  证明: by simp [← edgeSet_subset_edgeSet]
-/
@[simp] lemma fromEdgeSet_le {s : Set (Sym2 V)} :
    fromEdgeSet s <= G ↔ s \ Sym2.diagSet subseteq G.edgeSet := by simp [← edgeSet_subset_edgeSet]

/--
lemma `edgeSet_eq_iff` / 引理 `edgeSet_eq_iff`

English:
lemma edgeSet_eq_iff
  statement: G.edgeSet = s ↔ G = fromEdgeSet s ∧ Disjoint s Sym2.diagSet where
  proof: by rintro rfl; simp +contextual [Set.disjoint_right]
  mpr := by rintro ⟨rfl, hs⟩; simp [hs]

@[simp]

中文:
引理 edgeSet_eq_iff
  结论: G.edgeSet = s ↔ G = fromEdgeSet s ∧ Disjoint s Sym2.diagSet where
  证明: by rintro rfl; simp +contextual [Set.disjoint_right]
  mpr := by rintro ⟨rfl, hs⟩; simp [hs]

@[simp]

Depends on / 依赖: Set.disjoint_right, contextual, disjoint_right
-/
lemma edgeSet_eq_iff : G.edgeSet = s ↔ G = fromEdgeSet s ∧ Disjoint s Sym2.diagSet where
  mp := by rintro rfl; simp +contextual [Set.disjoint_right]
  mpr := by rintro ⟨rfl, hs⟩; simp [hs]

@[simp]
/--
theorem `fromEdgeSet_empty` / 定理 `fromEdgeSet_empty`

English:
theorem fromEdgeSet_empty
  statement: fromEdgeSet (∅ : Set (Sym2 V)) = ⊥
  proof: by
  ext v w
  simp only [fromEdgeSet_adj, Set.mem_empty_iff_false, false_and, bot_adj]

中文:
定理 fromEdgeSet_empty
  结论: fromEdgeSet (∅ : Set (Sym2 V)) = ⊥
  证明: by
  ext v w
  simp only [fromEdgeSet_adj, Set.mem_empty_iff_false, false_and, bot_adj]

Depends on / 依赖: Set.mem_empty_iff_false, bot_adj, false_and, fromEdgeSet_adj, mem_empty_iff_false
-/
theorem fromEdgeSet_empty : fromEdgeSet (∅ : Set (Sym2 V)) = ⊥ := by
  ext v w
  simp only [fromEdgeSet_adj, Set.mem_empty_iff_false, false_and, bot_adj]

/--
lemma `fromEdgeSet_not_isDiag` / 引理 `fromEdgeSet_not_isDiag`

English:
lemma fromEdgeSet_not_isDiag
  statement: @fromEdgeSet V Sym2.diagSetᶜ = ⊤
  proof: by ext; simp

@[simp]

中文:
引理 fromEdgeSet_not_isDiag
  结论: @fromEdgeSet V Sym2.diagSetᶜ = ⊤
  证明: by ext; simp

@[simp]
-/
@[simp] lemma fromEdgeSet_not_isDiag : @fromEdgeSet V Sym2.diagSetᶜ = ⊤ := by ext; simp

@[simp]
/--
theorem `fromEdgeSet_univ` / 定理 `fromEdgeSet_univ`

English:
theorem fromEdgeSet_univ
  statement: fromEdgeSet (Set.univ : Set (Sym2 V)) = ⊤
  proof: by
  ext v w
  simp only [fromEdgeSet_adj, Set.mem_univ, true_and, top_adj]

@[simp]

中文:
定理 fromEdgeSet_univ
  结论: fromEdgeSet (Set.univ : Set (Sym2 V)) = ⊤
  证明: by
  ext v w
  simp only [fromEdgeSet_adj, Set.mem_univ, true_and, top_adj]

@[simp]

Depends on / 依赖: Set.mem_univ, fromEdgeSet_adj, mem_univ, top_adj, true_and
-/
theorem fromEdgeSet_univ : fromEdgeSet (Set.univ : Set (Sym2 V)) = ⊤ := by
  ext v w
  simp only [fromEdgeSet_adj, Set.mem_univ, true_and, top_adj]

@[simp]
/--
theorem `fromEdgeSet_inter` / 定理 `fromEdgeSet_inter`

English:
theorem fromEdgeSet_inter
  given: (s t : Set (Sym2 V))
  proof: by
  ext v w
  simp only [fromEdgeSet_adj, Set.mem_inter_iff, Ne, inf_adj]
  tauto

@[simp]

中文:
定理 fromEdgeSet_inter
  条件: (s t : Set (Sym2 V))
  证明: by
  ext v w
  simp only [fromEdgeSet_adj, Set.mem_inter_iff, Ne, inf_adj]
  tauto

@[simp]

Depends on / 依赖: Set.mem_inter_iff, fromEdgeSet_adj, inf_adj, mem_inter_iff
-/
theorem fromEdgeSet_inter (s t : Set (Sym2 V)) :
    fromEdgeSet (s inter t) = fromEdgeSet s ⊓ fromEdgeSet t := by
  ext v w
  simp only [fromEdgeSet_adj, Set.mem_inter_iff, Ne, inf_adj]
  tauto

@[simp]
/--
theorem `fromEdgeSet_union` / 定理 `fromEdgeSet_union`

English:
theorem fromEdgeSet_union
  given: (s t : Set (Sym2 V))
  proof: by
  ext v w
  simp [Set.mem_union, or_and_right]

中文:
定理 fromEdgeSet_union
  条件: (s t : Set (Sym2 V))
  证明: by
  ext v w
  simp [Set.mem_union, or_and_right]

Depends on / 依赖: Set.mem_union, mem_union, or_and_right
-/
theorem fromEdgeSet_union (s t : Set (Sym2 V)) :
    fromEdgeSet (s union t) = fromEdgeSet s ⊔ fromEdgeSet t := by
  ext v w
  simp [Set.mem_union, or_and_right]

/--
theorem `fromEdgeSet_sUnion` / 定理 `fromEdgeSet_sUnion`

English:
theorem fromEdgeSet_sUnion
  given: {s : Set (Set (Sym2 V))}
  proof: by
  ext u v
  simp
  grind

中文:
定理 fromEdgeSet_sUnion
  条件: {s : Set (Set (Sym2 V))}
  证明: by
  ext u v
  simp
  grind
-/
theorem fromEdgeSet_sUnion {s : Set (Set (Sym2 V))} :
    fromEdgeSet (⋃₀ s) = sSup (fromEdgeSet '' s) := by
  ext u v
  simp
  grind

/--
theorem `fromEdgeSet_iUnion` / 定理 `fromEdgeSet_iUnion`

English:
theorem fromEdgeSet_iUnion
  given: {ι : Sort*} {f : ι -> Set (Sym2 V)}
  proof: by
  ext u v
  simp

中文:
定理 fromEdgeSet_iUnion
  条件: {ι : Sort*} {f : ι -> Set (Sym2 V)}
  证明: by
  ext u v
  simp
-/
theorem fromEdgeSet_iUnion {ι : Sort*} {f : ι -> Set (Sym2 V)} :
    fromEdgeSet (⋃ i, f i) = ⨆ i, fromEdgeSet (f i) := by
  ext u v
  simp

/--
theorem `fromEdgeSet_sInter` / 定理 `fromEdgeSet_sInter`

English:
theorem fromEdgeSet_sInter
  given: {s : Set (Set (Sym2 V))}
  proof: by
  ext u v
  simp_all

中文:
定理 fromEdgeSet_sInter
  条件: {s : Set (Set (Sym2 V))}
  证明: by
  ext u v
  simp_all
-/
theorem fromEdgeSet_sInter {s : Set (Set (Sym2 V))} :
    fromEdgeSet (⋂₀ s) = sInf (fromEdgeSet '' s) := by
  ext u v
  simp_all

/--
theorem `fromEdgeSet_iInter` / 定理 `fromEdgeSet_iInter`

English:
theorem fromEdgeSet_iInter
  given: {ι : Sort*} {f : ι -> Set (Sym2 V)}
  proof: by
  ext u v
  simp_all

@[simp]

中文:
定理 fromEdgeSet_iInter
  条件: {ι : Sort*} {f : ι -> Set (Sym2 V)}
  证明: by
  ext u v
  simp_all

@[simp]
-/
theorem fromEdgeSet_iInter {ι : Sort*} {f : ι -> Set (Sym2 V)} :
    fromEdgeSet (⋂ i, f i) = ⨅ i, fromEdgeSet (f i) := by
  ext u v
  simp_all

@[simp]
/--
theorem `fromEdgeSet_sdiff` / 定理 `fromEdgeSet_sdiff`

English:
theorem fromEdgeSet_sdiff
  given: (s t : Set (Sym2 V))
  proof: by
  ext v w
  constructor <;> simp +contextual

@[gcongr, mono]

中文:
定理 fromEdgeSet_sdiff
  条件: (s t : Set (Sym2 V))
  证明: by
  ext v w
  constructor <;> simp +contextual

@[gcongr, mono]

Depends on / 依赖: contextual
-/
theorem fromEdgeSet_sdiff (s t : Set (Sym2 V)) :
    fromEdgeSet (s \ t) = fromEdgeSet s \ fromEdgeSet t := by
  ext v w
  constructor <;> simp +contextual

@[gcongr, mono]
/--
theorem `fromEdgeSet_mono` / 定理 `fromEdgeSet_mono`

English:
theorem fromEdgeSet_mono
  given: {s t : Set (Sym2 V)} (h : s subseteq t)
  statement: fromEdgeSet s <= fromEdgeSet t
  proof: by
  simp only [le_fromEdgeSet_iff, edgeSet_fromEdgeSet]; grw [h]; exact sdiff_le

中文:
定理 fromEdgeSet_mono
  条件: {s t : Set (Sym2 V)} (h : s subseteq t)
  结论: fromEdgeSet s <= fromEdgeSet t
  证明: by
  simp only [le_fromEdgeSet_iff, edgeSet_fromEdgeSet]; grw [h]; exact sdiff_le

Depends on / 依赖: edgeSet_fromEdgeSet, le_fromEdgeSet_iff, sdiff_le
-/
theorem fromEdgeSet_mono {s t : Set (Sym2 V)} (h : s subseteq t) : fromEdgeSet s <= fromEdgeSet t := by
  simp only [le_fromEdgeSet_iff, edgeSet_fromEdgeSet]; grw [h]; exact sdiff_le

/--
lemma `disjoint_fromEdgeSet` / 引理 `disjoint_fromEdgeSet`

English:
lemma disjoint_fromEdgeSet
  statement: Disjoint G (fromEdgeSet s) ↔ Disjoint G.edgeSet s
  proof: by
  conv_rhs => rw [← Set.sdiff_union_inter s Sym2.diagSet]
  rw [← disjoint_edgeSet]; rw [edgeSet_fromEdgeSet]
  grind [edgeSet_subset_compl_diagSet]

中文:
引理 disjoint_fromEdgeSet
  结论: Disjoint G (fromEdgeSet s) ↔ Disjoint G.edgeSet s
  证明: by
  conv_rhs => rw [← Set.sdiff_union_inter s Sym2.diagSet]
  rw [← disjoint_edgeSet]; rw [edgeSet_fromEdgeSet]
  grind [edgeSet_subset_compl_diagSet]
-/
@[simp] lemma disjoint_fromEdgeSet : Disjoint G (fromEdgeSet s) ↔ Disjoint G.edgeSet s := by
  conv_rhs => rw [← Set.sdiff_union_inter s Sym2.diagSet]
  rw [← disjoint_edgeSet]; rw [edgeSet_fromEdgeSet]
  grind [edgeSet_subset_compl_diagSet]

/--
lemma `fromEdgeSet_disjoint` / 引理 `fromEdgeSet_disjoint`

English:
lemma fromEdgeSet_disjoint
  statement: Disjoint (fromEdgeSet s) G ↔ Disjoint s G.edgeSet
  proof: by
  rw [disjoint_comm]; rw [disjoint_fromEdgeSet]; rw [disjoint_comm]

中文:
引理 fromEdgeSet_disjoint
  结论: Disjoint (fromEdgeSet s) G ↔ Disjoint s G.edgeSet
  证明: by
  rw [disjoint_comm]; rw [disjoint_fromEdgeSet]; rw [disjoint_comm]
-/
@[simp] lemma fromEdgeSet_disjoint : Disjoint (fromEdgeSet s) G ↔ Disjoint s G.edgeSet := by
  rw [disjoint_comm]; rw [disjoint_fromEdgeSet]; rw [disjoint_comm]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [DecidableEq
  signature: V] [Fintype s] : Fintype (fromEdgeSet s).edgeSet
  body: by
  rw [edgeSet_fromEdgeSet s]
  infer_instance

中文:
实例 [DecidableEq
  签名: V] [Fintype s] : Fintype (fromEdgeSet s).edgeSet
  定义体: by
  rw [edgeSet_fromEdgeSet s]
  infer_instance

Depends on / 依赖: edgeSet_fromEdgeSet, infer_instance
-/
instance [DecidableEq V] [Fintype s] : Fintype (fromEdgeSet s).edgeSet := by
  rw [edgeSet_fromEdgeSet s]
  infer_instance

end FromEdgeSet

/--
theorem `disjoint_left` / 定理 `disjoint_left`

English:
theorem disjoint_left
  given: {G H : SimpleGraph V}
  statement: Disjoint G H ↔ forall x y, G.Adj x y -> ¬H.Adj x y
  proof: by
  simp [← disjoint_edgeSet, Set.disjoint_left, Sym2.forall]

中文:
定理 disjoint_left
  条件: {G H : SimpleGraph V}
  结论: Disjoint G H ↔ 对任意 x y, G.Adj x y -> ¬H.Adj x y
  证明: by
  simp [← disjoint_edgeSet, Set.disjoint_left, Sym2.forall]

Depends on / 依赖: Set.disjoint_left, Sym2.forall, disjoint_edgeSet, disjoint_left
-/
theorem disjoint_left {G H : SimpleGraph V} : Disjoint G H ↔ forall x y, G.Adj x y -> ¬H.Adj x y := by
  simp [← disjoint_edgeSet, Set.disjoint_left, Sym2.forall]

/-! ### Incidence set -/


/--
Definition of `incidenceSet` / `incidenceSet` 的定义

English:
definition incidenceSet
  signature: (v : V)
  body: { e in G.edgeSet | v in e }

中文:
定义 incidenceSet
  签名: (v : V)
  定义体: { e in G.edgeSet | v in e }

Depends on / 依赖: G.edgeSet, edgeSet
-/
def incidenceSet (v : V) : Set (Sym2 V) :=
  { e in G.edgeSet | v in e }

/--
theorem `incidenceSet_subset` / 定理 `incidenceSet_subset`

English:
theorem incidenceSet_subset
  given: (v : V)
  statement: G.incidenceSet v subseteq G.edgeSet
  proof: fun _ h => h.1

中文:
定理 incidenceSet_subset
  条件: (v : V)
  结论: G.incidenceSet v subseteq G.edgeSet
  证明: fun _ h => h.1
-/
theorem incidenceSet_subset (v : V) : G.incidenceSet v subseteq G.edgeSet := fun _ h => h.1

/--
theorem `mk'_mem_incidenceSet_iff` / 定理 `mk'_mem_incidenceSet_iff`

English:
theorem mk'_mem_incidenceSet_iff
  statement: s(b, c) in G.incidenceSet a ↔ G.Adj b c ∧ (a = b ∨ a = c)
  proof: and_congr_right' Sym2.mem_iff

中文:
定理 mk'_mem_incidenceSet_iff
  结论: s(b, c) in G.incidenceSet a ↔ G.Adj b c ∧ (a = b ∨ a = c)
  证明: and_congr_right' Sym2.mem_iff
-/
theorem mk'_mem_incidenceSet_iff : s(b, c) in G.incidenceSet a ↔ G.Adj b c ∧ (a = b ∨ a = c) :=
  and_congr_right' Sym2.mem_iff

/--
theorem `mk'_mem_incidenceSet_left_iff` / 定理 `mk'_mem_incidenceSet_left_iff`

English:
theorem mk'_mem_incidenceSet_left_iff
  statement: s(a, b) in G.incidenceSet a ↔ G.Adj a b
  proof: and_iff_left Sym2.mem_mk_left _ _

中文:
定理 mk'_mem_incidenceSet_left_iff
  结论: s(a, b) in G.incidenceSet a ↔ G.Adj a b
  证明: and_iff_left Sym2.mem_mk_left _ _
-/
theorem mk'_mem_incidenceSet_left_iff : s(a, b) in G.incidenceSet a ↔ G.Adj a b :=
and_iff_left Sym2.mem_mk_left _ _

/--
theorem `mk'_mem_incidenceSet_right_iff` / 定理 `mk'_mem_incidenceSet_right_iff`

English:
theorem mk'_mem_incidenceSet_right_iff
  statement: s(a, b) in G.incidenceSet b ↔ G.Adj a b
  proof: and_iff_left Sym2.mem_mk_right _ _

中文:
定理 mk'_mem_incidenceSet_right_iff
  结论: s(a, b) in G.incidenceSet b ↔ G.Adj a b
  证明: and_iff_left Sym2.mem_mk_right _ _
-/
theorem mk'_mem_incidenceSet_right_iff : s(a, b) in G.incidenceSet b ↔ G.Adj a b :=
and_iff_left Sym2.mem_mk_right _ _

/--
theorem `edge_mem_incidenceSet_iff` / 定理 `edge_mem_incidenceSet_iff`

English:
theorem edge_mem_incidenceSet_iff
  given: {e : G.edgeSet}
  statement: ↑e in G.incidenceSet a ↔ a in (e : Sym2 V)
  proof: and_iff_right e.2

中文:
定理 edge_mem_incidenceSet_iff
  条件: {e : G.edgeSet}
  结论: ↑e in G.incidenceSet a ↔ a in (e : Sym2 V)
  证明: and_iff_right e.2

Depends on / 依赖: and_iff_right
-/
theorem edge_mem_incidenceSet_iff {e : G.edgeSet} : ↑e in G.incidenceSet a ↔ a in (e : Sym2 V) :=
  and_iff_right e.2

/--
theorem `iUnion_incidenceSet` / 定理 `iUnion_incidenceSet`

English:
theorem iUnion_incidenceSet
  statement: ⋃ v, G.incidenceSet v = G.edgeSet
  proof: by
  ext ⟨_, _⟩
  simp [mk'_mem_incidenceSet_iff]

中文:
定理 iUnion_incidenceSet
  结论: ⋃ v, G.incidenceSet v = G.edgeSet
  证明: by
  ext ⟨_, _⟩
  simp [mk'_mem_incidenceSet_iff]

Depends on / 依赖: _mem_incidenceSet_iff
-/
theorem iUnion_incidenceSet : ⋃ v, G.incidenceSet v = G.edgeSet := by
  ext ⟨_, _⟩
  simp [mk'_mem_incidenceSet_iff]

variable {G H} in
/--
theorem `disjoint_incidenceSet` / 定理 `disjoint_incidenceSet`

English:
theorem disjoint_incidenceSet
  proof: by
  simp_rw [← disjoint_edgeSet, ← iUnion_incidenceSet, Set.disjoint_iUnion_left,
    Set.disjoint_iUnion_right, Set.disjoint_left, Sym2.forall]
  grind [mk'_mem_incidenceSet_iff]

中文:
定理 disjoint_incidenceSet
  证明: by
  simp_rw [← disjoint_edgeSet, ← iUnion_incidenceSet, Set.disjoint_iUnion_left,
    Set.disjoint_iUnion_right, Set.disjoint_left, Sym2.forall]
  grind [mk'_mem_incidenceSet_iff]

Depends on / 依赖: Set.disjoint_iUnion_left, Set.disjoint_iUnion_right, Set.disjoint_left, Sym2.forall, _mem_incidenceSet_iff, disjoint_edgeSet, disjoint_iUnion_left, disjoint_iUnion_right, disjoint_left, iUnion_incidenceSet, simp_rw
-/
theorem disjoint_incidenceSet :
    (forall v, Disjoint (G.incidenceSet v) (H.incidenceSet v)) ↔ Disjoint G H := by
  simp_rw [← disjoint_edgeSet, ← iUnion_incidenceSet, Set.disjoint_iUnion_left,
    Set.disjoint_iUnion_right, Set.disjoint_left, Sym2.forall]
  grind [mk'_mem_incidenceSet_iff]

/--
theorem `incidenceSet_inter_incidenceSet_subset` / 定理 `incidenceSet_inter_incidenceSet_subset`

English:
theorem incidenceSet_inter_incidenceSet_subset
  given: (h : a != b)
  proof: fun _e he =>
  (Sym2.mem_and_mem_iff h).1 ⟨he.1.2, he.2.2⟩

中文:
定理 incidenceSet_inter_incidenceSet_subset
  条件: (h : a != b)
  证明: fun _e he =>
  (Sym2.mem_and_mem_iff h).1 ⟨he.1.2, he.2.2⟩
-/
theorem incidenceSet_inter_incidenceSet_subset (h : a != b) :
    G.incidenceSet a inter G.incidenceSet b subseteq {s(a, b)} := fun _e he =>
  (Sym2.mem_and_mem_iff h).1 ⟨he.1.2, he.2.2⟩

/--
theorem `incidenceSet_inter_incidenceSet_of_adj` / 定理 `incidenceSet_inter_incidenceSet_of_adj`

English:
theorem incidenceSet_inter_incidenceSet_of_adj
  given: (h : G.Adj a b)
  proof: by
  refine (G.incidenceSet_inter_incidenceSet_subset <| h.ne).antisymm ?_
  rintro _ (rfl : _ = s(a, b))
  exact ⟨G.mk'_mem_incidenceSet_left_iff.2 h, G.mk'_mem_incidenceSet_right_iff.2 h⟩

中文:
定理 incidenceSet_inter_incidenceSet_of_adj
  条件: (h : G.Adj a b)
  证明: by
  refine (G.incidenceSet_inter_incidenceSet_subset <| h.ne).antisymm ?_
  rintro _ (rfl : _ = s(a, b))
  exact ⟨G.mk'_mem_incidenceSet_left_iff.2 h, G.mk'_mem_incidenceSet_right_iff.2 h⟩

Depends on / 依赖: G.incidenceSet_inter_incidenceSet_subset, G.mk, _mem_incidenceSet_left_iff, _mem_incidenceSet_right_iff, antisymm, h.ne, incidenceSet_inter_incidenceSet_subset
-/
theorem incidenceSet_inter_incidenceSet_of_adj (h : G.Adj a b) :
    G.incidenceSet a inter G.incidenceSet b = {s(a, b)} := by
  refine (G.incidenceSet_inter_incidenceSet_subset <| h.ne).antisymm ?_
  rintro _ (rfl : _ = s(a, b))
  exact ⟨G.mk'_mem_incidenceSet_left_iff.2 h, G.mk'_mem_incidenceSet_right_iff.2 h⟩

/--
theorem `adj_of_mem_incidenceSet` / 定理 `adj_of_mem_incidenceSet`

English:
theorem adj_of_mem_incidenceSet
  statement: (h : a != b) (ha : e in G.incidenceSet a)
  proof: by
  rwa [← mk'_mem_incidenceSet_left_iff, ←
Set.mem_singleton_iff.1 G.incidenceSet_inter_incidenceSet_subset h ⟨ha, hb⟩]

中文:
定理 adj_of_mem_incidenceSet
  结论: (h : a != b) (ha : e in G.incidenceSet a)
  证明: by
  rwa [← mk'_mem_incidenceSet_left_iff, ←
Set.mem_singleton_iff.1 G.incidenceSet_inter_incidenceSet_subset h ⟨ha, hb⟩]

Depends on / 依赖: G.incidenceSet_inter_incidenceSet_subset, Set.mem_singleton_iff, _mem_incidenceSet_left_iff, incidenceSet_inter_incidenceSet_subset, mem_singleton_iff
-/
theorem adj_of_mem_incidenceSet (h : a != b) (ha : e in G.incidenceSet a)
    (hb : e in G.incidenceSet b) : G.Adj a b := by
  rwa [← mk'_mem_incidenceSet_left_iff, ←
Set.mem_singleton_iff.1 G.incidenceSet_inter_incidenceSet_subset h ⟨ha, hb⟩]

/--
theorem `incidenceSet_inter_incidenceSet_of_not_adj` / 定理 `incidenceSet_inter_incidenceSet_of_not_adj`

English:
theorem incidenceSet_inter_incidenceSet_of_not_adj
  given: (h : ¬G.Adj a b) (hn : a != b)
  proof: by
  simp_rw [Set.eq_empty_iff_forall_notMem, Set.mem_inter_iff, not_and]
  intro u ha hb
  exact h (G.adj_of_mem_incidenceSet hn ha hb)

中文:
定理 incidenceSet_inter_incidenceSet_of_not_adj
  条件: (h : ¬G.Adj a b) (hn : a != b)
  证明: by
  simp_rw [Set.eq_empty_iff_forall_notMem, Set.mem_inter_iff, not_and]
  intro u ha hb
  exact h (G.adj_of_mem_incidenceSet hn ha hb)

Depends on / 依赖: G.adj_of_mem_incidenceSet, Set.eq_empty_iff_forall_notMem, Set.mem_inter_iff, adj_of_mem_incidenceSet, eq_empty_iff_forall_notMem, mem_inter_iff, not_and, simp_rw
-/
theorem incidenceSet_inter_incidenceSet_of_not_adj (h : ¬G.Adj a b) (hn : a != b) :
    G.incidenceSet a inter G.incidenceSet b = ∅ := by
  simp_rw [Set.eq_empty_iff_forall_notMem, Set.mem_inter_iff, not_and]
  intro u ha hb
  exact h (G.adj_of_mem_incidenceSet hn ha hb)

/--
Instance `decidableMemIncidenceSet` / 实例 `decidableMemIncidenceSet`

English:
instance decidableMemIncidenceSet
  signature: [DecidableEq V] [DecidableRel G.Adj] (v : V)
  body: inferInstanceAs DecidablePred fun e => e in G.edgeSet ∧ v in e

@[simp]

中文:
实例 decidableMemIncidenceSet
  签名: [DecidableEq V] [DecidableRel G.Adj] (v : V)
  定义体: inferInstanceAs DecidablePred fun e => e in G.edgeSet ∧ v in e

@[simp]

Depends on / 依赖: DecidablePred, G.edgeSet, edgeSet
-/
instance decidableMemIncidenceSet [DecidableEq V] [DecidableRel G.Adj] (v : V) :
    DecidablePred (· in G.incidenceSet v) :=
inferInstanceAs DecidablePred fun e => e in G.edgeSet ∧ v in e

@[simp]
/--
theorem `mem_neighborSet` / 定理 `mem_neighborSet`

English:
theorem mem_neighborSet
  given: (v w : V)
  statement: w in G.neighborSet v ↔ G.Adj v w
  proof: Iff.rfl

中文:
定理 mem_neighborSet
  条件: (v w : V)
  结论: w in G.neighborSet v ↔ G.Adj v w
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_neighborSet (v w : V) : w in G.neighborSet v ↔ G.Adj v w :=
  Iff.rfl

/--
lemma `notMem_neighborSet_self` / 引理 `notMem_neighborSet_self`

English:
lemma notMem_neighborSet_self
  statement: a ∉ G.neighborSet a
  proof: by simp

中文:
引理 notMem_neighborSet_self
  结论: a ∉ G.neighborSet a
  证明: by simp
-/
lemma notMem_neighborSet_self : a ∉ G.neighborSet a := by simp

variable {G} in
/--
theorem `nonempty_neighborSet` / 定理 `nonempty_neighborSet`

English:
theorem nonempty_neighborSet
  statement: (G.neighborSet v).Nonempty ↔ exists u, G.Adj v u
  proof: .rfl

中文:
定理 nonempty_neighborSet
  结论: (G.neighborSet v).Nonempty ↔ 存在 u, G.Adj v u
  证明: .rfl
-/
theorem nonempty_neighborSet : (G.neighborSet v).Nonempty ↔ exists u, G.Adj v u :=
  .rfl

variable (v) in
/--
theorem `neighborSet_subset_compl` / 定理 `neighborSet_subset_compl`

English:
theorem neighborSet_subset_compl
  statement: G.neighborSet v subseteq {v}ᶜ
  proof: by
  simp

中文:
定理 neighborSet_subset_compl
  结论: G.neighborSet v subseteq {v}ᶜ
  证明: by
  simp
-/
theorem neighborSet_subset_compl : G.neighborSet v subseteq {v}ᶜ := by
  simp

variable (v) in
/--
theorem `neighborSet_ne_univ` / 定理 `neighborSet_ne_univ`

English:
theorem neighborSet_ne_univ
  statement: G.neighborSet v != .univ
  proof: .mpr ⟨v, G.notMem_neighborSet_self⟩ Set.ne_univ_iff_exists_notMem _

中文:
定理 neighborSet_ne_univ
  结论: G.neighborSet v != .univ
  证明: .mpr ⟨v, G.notMem_neighborSet_self⟩ Set.ne_univ_iff_exists_notMem _

Depends on / 依赖: G.notMem_neighborSet_self, Set.ne_univ_iff_exists_notMem, ne_univ_iff_exists_notMem, notMem_neighborSet_self
-/
theorem neighborSet_ne_univ : G.neighborSet v != .univ :=
.mpr ⟨v, G.notMem_neighborSet_self⟩ Set.ne_univ_iff_exists_notMem _

variable {G H} in
/--
theorem `disjoint_neighborSet` / 定理 `disjoint_neighborSet`

English:
theorem disjoint_neighborSet
  proof: by
  simp_rw [← disjoint_edgeSet, Set.disjoint_left, mem_neighborSet, Sym2.forall, mem_edgeSet]

@[simp]

中文:
定理 disjoint_neighborSet
  证明: by
  simp_rw [← disjoint_edgeSet, Set.disjoint_left, mem_neighborSet, Sym2.forall, mem_edgeSet]

@[simp]

Depends on / 依赖: Set.disjoint_left, Sym2.forall, disjoint_edgeSet, disjoint_left, mem_edgeSet, mem_neighborSet, simp_rw
-/
theorem disjoint_neighborSet :
    (forall v, Disjoint (G.neighborSet v) (H.neighborSet v)) ↔ Disjoint G H := by
  simp_rw [← disjoint_edgeSet, Set.disjoint_left, mem_neighborSet, Sym2.forall, mem_edgeSet]

@[simp]
/--
theorem `neighborSet_sup` / 定理 `neighborSet_sup`

English:
theorem neighborSet_sup
  given: {G₁ G₂ : SimpleGraph V} (v : V)
  proof: rfl

@[simp]

中文:
定理 neighborSet_sup
  条件: {G₁ G₂ : SimpleGraph V} (v : V)
  证明: rfl

@[simp]
-/
theorem neighborSet_sup {G₁ G₂ : SimpleGraph V} (v : V) :
    (G₁ ⊔ G₂).neighborSet v = G₁.neighborSet v union G₂.neighborSet v :=
  rfl

@[simp]
/--
theorem `neighborSet_inf` / 定理 `neighborSet_inf`

English:
theorem neighborSet_inf
  given: {G₁ G₂ : SimpleGraph V} (v : V)
  proof: rfl

@[simp]

中文:
定理 neighborSet_inf
  条件: {G₁ G₂ : SimpleGraph V} (v : V)
  证明: rfl

@[simp]
-/
theorem neighborSet_inf {G₁ G₂ : SimpleGraph V} (v : V) :
    (G₁ ⊓ G₂).neighborSet v = G₁.neighborSet v inter G₂.neighborSet v :=
  rfl

@[simp]
/--
theorem `neighborSet_sdiff` / 定理 `neighborSet_sdiff`

English:
theorem neighborSet_sdiff
  given: {G₁ G₂ : SimpleGraph V} (v : V)
  proof: rfl

@[simp]

中文:
定理 neighborSet_sdiff
  条件: {G₁ G₂ : SimpleGraph V} (v : V)
  证明: rfl

@[simp]
-/
theorem neighborSet_sdiff {G₁ G₂ : SimpleGraph V} (v : V) :
    (G₁ \ G₂).neighborSet v = G₁.neighborSet v \ G₂.neighborSet v :=
  rfl

@[simp]
/--
theorem `neighborSet_iSup` / 定理 `neighborSet_iSup`

English:
theorem neighborSet_iSup
  given: {s : ι -> SimpleGraph V} (v : V)
  proof: by
  ext; simp

@[simp]

中文:
定理 neighborSet_iSup
  条件: {s : ι -> SimpleGraph V} (v : V)
  证明: by
  ext; simp

@[simp]
-/
theorem neighborSet_iSup {s : ι -> SimpleGraph V} (v : V) :
    (⨆ i, s i).neighborSet v = ⋃ i, (s i).neighborSet v := by
  ext; simp

@[simp]
/--
theorem `neighborSet_iInf` / 定理 `neighborSet_iInf`

English:
theorem neighborSet_iInf
  given: [Nonempty ι] {s : ι -> SimpleGraph V} (v : V)
  proof: by
  ext
  simp_rw [Set.mem_iInter, mem_neighborSet, iInf_adj_of_nonempty]

@[simp]

中文:
定理 neighborSet_iInf
  条件: [Nonempty ι] {s : ι -> SimpleGraph V} (v : V)
  证明: by
  ext
  simp_rw [Set.mem_iInter, mem_neighborSet, iInf_adj_of_nonempty]

@[simp]

Depends on / 依赖: Set.mem_iInter, iInf_adj_of_nonempty, mem_iInter, mem_neighborSet, simp_rw
-/
theorem neighborSet_iInf [Nonempty ι] {s : ι -> SimpleGraph V} (v : V) :
    (⨅ i, s i).neighborSet v = ⋂ i, (s i).neighborSet v := by
  ext
  simp_rw [Set.mem_iInter, mem_neighborSet, iInf_adj_of_nonempty]

@[simp]
/--
theorem `mem_incidenceSet` / 定理 `mem_incidenceSet`

English:
theorem mem_incidenceSet
  given: (v w : V)
  statement: s(v, w) in G.incidenceSet v ↔ G.Adj v w
  proof: by
  simp [incidenceSet]

中文:
定理 mem_incidenceSet
  条件: (v w : V)
  结论: s(v, w) in G.incidenceSet v ↔ G.Adj v w
  证明: by
  simp [incidenceSet]

Depends on / 依赖: incidenceSet
-/
theorem mem_incidenceSet (v w : V) : s(v, w) in G.incidenceSet v ↔ G.Adj v w := by
  simp [incidenceSet]

/--
theorem `mem_incidence_iff_neighbor` / 定理 `mem_incidence_iff_neighbor`

English:
theorem mem_incidence_iff_neighbor
  given: {v w : V}
  proof: by
  simp only [mem_incidenceSet, mem_neighborSet]

中文:
定理 mem_incidence_iff_neighbor
  条件: {v w : V}
  证明: by
  simp only [mem_incidenceSet, mem_neighborSet]

Depends on / 依赖: mem_incidenceSet, mem_neighborSet
-/
theorem mem_incidence_iff_neighbor {v w : V} :
    s(v, w) in G.incidenceSet v ↔ w in G.neighborSet v := by
  simp only [mem_incidenceSet, mem_neighborSet]

/--
theorem `adj_incidenceSet_inter` / 定理 `adj_incidenceSet_inter`

English:
theorem adj_incidenceSet_inter
  given: {v : V} {e : Sym2 V} (he : e in G.edgeSet) (h : v in e)
  proof: by
  ext e'
  simp only [incidenceSet, Set.mem_sep_iff, Set.mem_inter_iff, Set.mem_singleton_iff]
  refine ⟨fun h' => ?_, ?_⟩
  · rw [← Sym2.other_spec h]
    exact (Sym2.mem_and_mem_iff (edge_other_ne G he h).symm).mp ⟨h'.1.2, h'.2.2⟩
  · rintro rfl
    exact ⟨⟨he, h⟩, he, Sym2.other_mem _⟩

中文:
定理 adj_incidenceSet_inter
  条件: {v : V} {e : Sym2 V} (he : e in G.edgeSet) (h : v in e)
  证明: by
  ext e'
  simp only [incidenceSet, Set.mem_sep_iff, Set.mem_inter_iff, Set.mem_singleton_iff]
  refine ⟨fun h' => ?_, ?_⟩
  · rw [← Sym2.other_spec h]
    exact (Sym2.mem_and_mem_iff (edge_other_ne G he h).symm).mp ⟨h'.1.2, h'.2.2⟩
  · rintro rfl
    exact ⟨⟨he, h⟩, he, Sym2.other_mem _⟩

Depends on / 依赖: Set.mem_inter_iff, Set.mem_sep_iff, Set.mem_singleton_iff, Sym2.mem_and_mem_iff, Sym2.other_mem, Sym2.other_spec, edge_other_ne, incidenceSet, mem_and_mem_iff, mem_inter_iff, mem_sep_iff, mem_singleton_iff, other_mem, other_spec
-/
theorem adj_incidenceSet_inter {v : V} {e : Sym2 V} (he : e in G.edgeSet) (h : v in e) :
    G.incidenceSet v inter G.incidenceSet (Sym2.Mem.other h) = {e} := by
  ext e'
  simp only [incidenceSet, Set.mem_sep_iff, Set.mem_inter_iff, Set.mem_singleton_iff]
  refine ⟨fun h' => ?_, ?_⟩
  · rw [← Sym2.other_spec h]
    exact (Sym2.mem_and_mem_iff (edge_other_ne G he h).symm).mp ⟨h'.1.2, h'.2.2⟩
  · rintro rfl
    exact ⟨⟨he, h⟩, he, Sym2.other_mem _⟩

/--
theorem `compl_neighborSet_disjoint` / 定理 `compl_neighborSet_disjoint`

English:
theorem compl_neighborSet_disjoint
  given: (G : SimpleGraph V) (v : V)
  proof: by
  rw [Set.disjoint_iff]
  rintro w ⟨h, h'⟩
  rw [mem_neighborSet]; rw [compl_adj] at h'
  exact h'.2 h

中文:
定理 compl_neighborSet_disjoint
  条件: (G : SimpleGraph V) (v : V)
  证明: by
  rw [Set.disjoint_iff]
  rintro w ⟨h, h'⟩
  rw [mem_neighborSet]; rw [compl_adj] at h'
  exact h'.2 h

Depends on / 依赖: Set.disjoint_iff, compl_adj, disjoint_iff, mem_neighborSet
-/
theorem compl_neighborSet_disjoint (G : SimpleGraph V) (v : V) :
    Disjoint (G.neighborSet v) (Gᶜ.neighborSet v) := by
  rw [Set.disjoint_iff]
  rintro w ⟨h, h'⟩
  rw [mem_neighborSet]; rw [compl_adj] at h'
  exact h'.2 h

/--
theorem `neighborSet_union_compl_neighborSet_eq` / 定理 `neighborSet_union_compl_neighborSet_eq`

English:
theorem neighborSet_union_compl_neighborSet_eq
  given: (G : SimpleGraph V) (v : V)
  proof: by
  ext w
  have h := @ne_of_adj _ G
  simp_rw [Set.mem_union, mem_neighborSet, compl_adj, Set.mem_compl_iff, Set.mem_singleton_iff]
  tauto

中文:
定理 neighborSet_union_compl_neighborSet_eq
  条件: (G : SimpleGraph V) (v : V)
  证明: by
  ext w
  have h := @ne_of_adj _ G
  simp_rw [Set.mem_union, mem_neighborSet, compl_adj, Set.mem_compl_iff, Set.mem_singleton_iff]
  tauto

Depends on / 依赖: Set.mem_compl_iff, Set.mem_singleton_iff, Set.mem_union, compl_adj, mem_compl_iff, mem_neighborSet, mem_singleton_iff, mem_union, ne_of_adj, simp_rw
-/
theorem neighborSet_union_compl_neighborSet_eq (G : SimpleGraph V) (v : V) :
    G.neighborSet v union Gᶜ.neighborSet v = {v}ᶜ := by
  ext w
  have h := @ne_of_adj _ G
  simp_rw [Set.mem_union, mem_neighborSet, compl_adj, Set.mem_compl_iff, Set.mem_singleton_iff]
  tauto

/--
theorem `card_neighborSet_union_compl_neighborSet` / 定理 `card_neighborSet_union_compl_neighborSet`

English:
theorem card_neighborSet_union_compl_neighborSet
  statement: [Fintype V] (G : SimpleGraph V) (v : V)
  proof: by
  classical simp_rw [neighborSet_union_compl_neighborSet_eq, Set.toFinset_compl,
      Finset.card_compl, Set.toFinset_card, Set.card_singleton]

中文:
定理 card_neighborSet_union_compl_neighborSet
  结论: [Fintype V] (G : SimpleGraph V) (v : V)
  证明: by
  classical simp_rw [neighborSet_union_compl_neighborSet_eq, Set.toFinset_compl,
      Finset.card_compl, Set.toFinset_card, Set.card_singleton]

Depends on / 依赖: Finset, Finset.card_compl, Set.card_singleton, Set.toFinset_card, Set.toFinset_compl, card_compl, card_singleton, classical, neighborSet_union_compl_neighborSet_eq, simp_rw, toFinset_card, toFinset_compl
-/
theorem card_neighborSet_union_compl_neighborSet [Fintype V] (G : SimpleGraph V) (v : V)
    [Fintype (G.neighborSet v union Gᶜ.neighborSet v : Set V)] :
    #(G.neighborSet v union Gᶜ.neighborSet v).toFinset = Fintype.card V - 1 := by
  classical simp_rw [neighborSet_union_compl_neighborSet_eq, Set.toFinset_compl,
      Finset.card_compl, Set.toFinset_card, Set.card_singleton]

/--
theorem `neighborSet_compl` / 定理 `neighborSet_compl`

English:
theorem neighborSet_compl
  given: (G : SimpleGraph V) (v : V)
  proof: by
  ext w
  simp [and_comm, eq_comm]

中文:
定理 neighborSet_compl
  条件: (G : SimpleGraph V) (v : V)
  证明: by
  ext w
  simp [and_comm, eq_comm]

Depends on / 依赖: and_comm, eq_comm
-/
theorem neighborSet_compl (G : SimpleGraph V) (v : V) :
    Gᶜ.neighborSet v = (G.neighborSet v)ᶜ \ {v} := by
  ext w
  simp [and_comm, eq_comm]

variable {G} in
@[gcongr]
/--
theorem `neighborSet_mono` / 定理 `neighborSet_mono`

English:
theorem neighborSet_mono
  given: {G' : SimpleGraph V} (hle : G <= G') (v : V)
  proof: fun _ hadj => hle hadj

@[simp]

中文:
定理 neighborSet_mono
  条件: {G' : SimpleGraph V} (hle : G <= G') (v : V)
  证明: fun _ hadj => hle hadj

@[simp]
-/
theorem neighborSet_mono {G' : SimpleGraph V} (hle : G <= G') (v : V) :
    G.neighborSet v subseteq G'.neighborSet v :=
  fun _ hadj => hle hadj

@[simp]
/--
theorem `neighborSet_top` / 定理 `neighborSet_top`

English:
theorem neighborSet_top
  statement: neighborSet ⊤ v = {v}ᶜ
  proof: by
  grind [mem_neighborSet, top_adj]

中文:
定理 neighborSet_top
  结论: neighborSet ⊤ v = {v}ᶜ
  证明: by
  grind [mem_neighborSet, top_adj]

Depends on / 依赖: mem_neighborSet, top_adj
-/
theorem neighborSet_top : neighborSet ⊤ v = {v}ᶜ := by
  grind [mem_neighborSet, top_adj]

/--
theorem `neighborSet_bot` / 定理 `neighborSet_bot`

English:
theorem neighborSet_bot
  statement: neighborSet ⊥ v = ∅
  proof: by
  grind [mem_neighborSet, bot_adj]

中文:
定理 neighborSet_bot
  结论: neighborSet ⊥ v = ∅
  证明: by
  grind [mem_neighborSet, bot_adj]

Depends on / 依赖: bot_adj, mem_neighborSet
-/
theorem neighborSet_bot : neighborSet ⊥ v = ∅ := by
  grind [mem_neighborSet, bot_adj]

variable {G} in
/--
theorem `Adj.nontrivial` / 定理 `Adj.nontrivial`

English:
theorem Adj.nontrivial
  given: (hadj : G.Adj u v)
  statement: Nontrivial V
  proof: ⟨u, v, hadj.ne⟩

中文:
定理 Adj.nontrivial
  条件: (hadj : G.Adj u v)
  结论: Nontrivial V
  证明: ⟨u, v, hadj.ne⟩

Depends on / 依赖: hadj.ne
-/
theorem Adj.nontrivial (hadj : G.Adj u v) : Nontrivial V :=
  ⟨u, v, hadj.ne⟩

/--
Definition of `commonNeighbors` / `commonNeighbors` 的定义

English:
definition commonNeighbors
  signature: (v w : V)
  body: G.neighborSet v inter G.neighborSet w

中文:
定义 commonNeighbors
  签名: (v w : V)
  定义体: G.neighborSet v inter G.neighborSet w

Depends on / 依赖: G.neighborSet, neighborSet
-/
def commonNeighbors (v w : V) : Set V :=
  G.neighborSet v inter G.neighborSet w

/--
theorem `commonNeighbors_eq` / 定理 `commonNeighbors_eq`

English:
theorem commonNeighbors_eq
  given: (v w : V)
  statement: G.commonNeighbors v w = G.neighborSet v inter G.neighborSet w
  proof: rfl

中文:
定理 commonNeighbors_eq
  条件: (v w : V)
  结论: G.commonNeighbors v w = G.neighborSet v inter G.neighborSet w
  证明: rfl
-/
theorem commonNeighbors_eq (v w : V) : G.commonNeighbors v w = G.neighborSet v inter G.neighborSet w :=
  rfl

/--
theorem `mem_commonNeighbors` / 定理 `mem_commonNeighbors`

English:
theorem mem_commonNeighbors
  given: {u v w : V}
  statement: u in G.commonNeighbors v w ↔ G.Adj v u ∧ G.Adj w u
  proof: Iff.rfl

中文:
定理 mem_commonNeighbors
  条件: {u v w : V}
  结论: u in G.commonNeighbors v w ↔ G.Adj v u ∧ G.Adj w u
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_commonNeighbors {u v w : V} : u in G.commonNeighbors v w ↔ G.Adj v u ∧ G.Adj w u :=
  Iff.rfl

/--
theorem `commonNeighbors_symm` / 定理 `commonNeighbors_symm`

English:
theorem commonNeighbors_symm
  given: (v w : V)
  statement: G.commonNeighbors v w = G.commonNeighbors w v
  proof: Set.inter_comm _ _

中文:
定理 commonNeighbors_symm
  条件: (v w : V)
  结论: G.commonNeighbors v w = G.commonNeighbors w v
  证明: Set.inter_comm _ _

Depends on / 依赖: Set.inter_comm, inter_comm
-/
theorem commonNeighbors_symm (v w : V) : G.commonNeighbors v w = G.commonNeighbors w v :=
  Set.inter_comm _ _

/--
theorem `notMem_commonNeighbors_left` / 定理 `notMem_commonNeighbors_left`

English:
theorem notMem_commonNeighbors_left
  given: (v w : V)
  statement: v ∉ G.commonNeighbors v w
  proof: fun h =>
  ne_of_adj G h.1 rfl

中文:
定理 notMem_commonNeighbors_left
  条件: (v w : V)
  结论: v ∉ G.commonNeighbors v w
  证明: fun h =>
  ne_of_adj G h.1 rfl
-/
theorem notMem_commonNeighbors_left (v w : V) : v ∉ G.commonNeighbors v w := fun h =>
  ne_of_adj G h.1 rfl

/--
theorem `notMem_commonNeighbors_right` / 定理 `notMem_commonNeighbors_right`

English:
theorem notMem_commonNeighbors_right
  given: (v w : V)
  statement: w ∉ G.commonNeighbors v w
  proof: fun h =>
  ne_of_adj G h.2 rfl

中文:
定理 notMem_commonNeighbors_right
  条件: (v w : V)
  结论: w ∉ G.commonNeighbors v w
  证明: fun h =>
  ne_of_adj G h.2 rfl
-/
theorem notMem_commonNeighbors_right (v w : V) : w ∉ G.commonNeighbors v w := fun h =>
  ne_of_adj G h.2 rfl

/--
theorem `commonNeighbors_subset_neighborSet_left` / 定理 `commonNeighbors_subset_neighborSet_left`

English:
theorem commonNeighbors_subset_neighborSet_left
  given: (v w : V)
  proof: Set.inter_subset_left

中文:
定理 commonNeighbors_subset_neighborSet_left
  条件: (v w : V)
  证明: Set.inter_subset_left

Depends on / 依赖: Set.inter_subset_left, inter_subset_left
-/
theorem commonNeighbors_subset_neighborSet_left (v w : V) :
    G.commonNeighbors v w subseteq G.neighborSet v :=
  Set.inter_subset_left

/--
theorem `commonNeighbors_subset_neighborSet_right` / 定理 `commonNeighbors_subset_neighborSet_right`

English:
theorem commonNeighbors_subset_neighborSet_right
  given: (v w : V)
  proof: Set.inter_subset_right

中文:
定理 commonNeighbors_subset_neighborSet_right
  条件: (v w : V)
  证明: Set.inter_subset_right

Depends on / 依赖: Set.inter_subset_right, inter_subset_right
-/
theorem commonNeighbors_subset_neighborSet_right (v w : V) :
    G.commonNeighbors v w subseteq G.neighborSet w :=
  Set.inter_subset_right

/--
Instance `decidableMemCommonNeighbors` / 实例 `decidableMemCommonNeighbors`

English:
instance decidableMemCommonNeighbors
  signature: [DecidableRel G.Adj] (v w : V)
  body: inferInstanceAs DecidablePred fun u => u in G.neighborSet v ∧ u in G.neighborSet w

中文:
实例 decidableMemCommonNeighbors
  签名: [DecidableRel G.Adj] (v w : V)
  定义体: inferInstanceAs DecidablePred fun u => u in G.neighborSet v ∧ u in G.neighborSet w

Depends on / 依赖: DecidablePred, G.neighborSet, neighborSet
-/
instance decidableMemCommonNeighbors [DecidableRel G.Adj] (v w : V) :
    DecidablePred (· in G.commonNeighbors v w) :=
inferInstanceAs DecidablePred fun u => u in G.neighborSet v ∧ u in G.neighborSet w

variable {G H} in
/--
theorem `disjoint_commonNeighbors` / 定理 `disjoint_commonNeighbors`

English:
theorem disjoint_commonNeighbors
  proof: by
  simp_rw [← disjoint_edgeSet, Set.disjoint_left, mem_commonNeighbors, Sym2.forall, mem_edgeSet]
  grind

中文:
定理 disjoint_commonNeighbors
  证明: by
  simp_rw [← disjoint_edgeSet, Set.disjoint_left, mem_commonNeighbors, Sym2.forall, mem_edgeSet]
  grind

Depends on / 依赖: Set.disjoint_left, Sym2.forall, disjoint_edgeSet, disjoint_left, mem_commonNeighbors, mem_edgeSet, simp_rw
-/
theorem disjoint_commonNeighbors :
    (forall u v, Disjoint (G.commonNeighbors u v) (H.commonNeighbors u v)) ↔ Disjoint G H := by
  simp_rw [← disjoint_edgeSet, Set.disjoint_left, mem_commonNeighbors, Sym2.forall, mem_edgeSet]
  grind

/--
theorem `commonNeighbors_top_eq` / 定理 `commonNeighbors_top_eq`

English:
theorem commonNeighbors_top_eq
  given: {v w : V}
  proof: by
  ext u
  simp [commonNeighbors, eq_comm, not_or]

@[simp]

中文:
定理 commonNeighbors_top_eq
  条件: {v w : V}
  证明: by
  ext u
  simp [commonNeighbors, eq_comm, not_or]

@[simp]

Depends on / 依赖: commonNeighbors, eq_comm, not_or
-/
theorem commonNeighbors_top_eq {v w : V} :
    (⊤ : SimpleGraph V).commonNeighbors v w = Set.univ \ {v, w} := by
  ext u
  simp [commonNeighbors, eq_comm, not_or]

@[simp]
/--
theorem `commonNeighbors_bot_eq` / 定理 `commonNeighbors_bot_eq`

English:
theorem commonNeighbors_bot_eq
  statement: commonNeighbors ⊥ u v = ∅
  proof: by
  simp [commonNeighbors, neighborSet_bot]

中文:
定理 commonNeighbors_bot_eq
  结论: commonNeighbors ⊥ u v = ∅
  证明: by
  simp [commonNeighbors, neighborSet_bot]

Depends on / 依赖: commonNeighbors, neighborSet_bot
-/
theorem commonNeighbors_bot_eq : commonNeighbors ⊥ u v = ∅ := by
  simp [commonNeighbors, neighborSet_bot]

section Incidence

variable [DecidableEq V]

/--
Definition of `otherVertexOfIncident` / `otherVertexOfIncident` 的定义

English:
definition otherVertexOfIncident
  signature: {v : V} {e : Sym2 V} (h : e in G.incidenceSet v)
  body: Sym2.Mem.other' h.2

中文:
定义 otherVertexOfIncident
  签名: {v : V} {e : Sym2 V} (h : e in G.incidenceSet v)
  定义体: Sym2.Mem.other' h.2

Depends on / 依赖: Sym2.Mem.other
-/
def otherVertexOfIncident {v : V} {e : Sym2 V} (h : e in G.incidenceSet v) : V :=
  Sym2.Mem.other' h.2

/--
theorem `edge_other_incident_set` / 定理 `edge_other_incident_set`

English:
theorem edge_other_incident_set
  given: {v : V} {e : Sym2 V} (h : e in G.incidenceSet v)
  proof: by
  use h.1
  simp [otherVertexOfIncident, Sym2.other_mem']

中文:
定理 edge_other_incident_set
  条件: {v : V} {e : Sym2 V} (h : e in G.incidenceSet v)
  证明: by
  use h.1
  simp [otherVertexOfIncident, Sym2.other_mem']

Depends on / 依赖: Sym2.other_mem, otherVertexOfIncident, other_mem
-/
theorem edge_other_incident_set {v : V} {e : Sym2 V} (h : e in G.incidenceSet v) :
    e in G.incidenceSet (G.otherVertexOfIncident h) := by
  use h.1
  simp [otherVertexOfIncident, Sym2.other_mem']

/--
theorem `incidence_other_prop` / 定理 `incidence_other_prop`

English:
theorem incidence_other_prop
  given: {v : V} {e : Sym2 V} (h : e in G.incidenceSet v)
  proof: by
  obtain ⟨he, hv⟩ := h
  rwa [← Sym2.other_spec' hv, mem_edgeSet] at he

@[simp]

中文:
定理 incidence_other_prop
  条件: {v : V} {e : Sym2 V} (h : e in G.incidenceSet v)
  证明: by
  obtain ⟨he, hv⟩ := h
  rwa [← Sym2.other_spec' hv, mem_edgeSet] at he

@[simp]

Depends on / 依赖: Sym2.other_spec, mem_edgeSet, other_spec
-/
theorem incidence_other_prop {v : V} {e : Sym2 V} (h : e in G.incidenceSet v) :
    G.otherVertexOfIncident h in G.neighborSet v := by
  obtain ⟨he, hv⟩ := h
  rwa [← Sym2.other_spec' hv, mem_edgeSet] at he

@[simp]
/--
theorem `incidence_other_neighbor_edge` / 定理 `incidence_other_neighbor_edge`

English:
theorem incidence_other_neighbor_edge
  given: {v w : V} (h : w in G.neighborSet v)
  proof: Sym2.congr_right.mp (Sym2.other_spec' (G.mem_incidence_iff_neighbor.mpr h).right)

中文:
定理 incidence_other_neighbor_edge
  条件: {v w : V} (h : w in G.neighborSet v)
  证明: Sym2.congr_right.mp (Sym2.other_spec' (G.mem_incidence_iff_neighbor.mpr h).right)

Depends on / 依赖: G.mem_incidence_iff_neighbor.mpr, Sym2.congr_right.mp, Sym2.other_spec, congr_right, mem_incidence_iff_neighbor, other_spec
-/
theorem incidence_other_neighbor_edge {v w : V} (h : w in G.neighborSet v) :
    G.otherVertexOfIncident (G.mem_incidence_iff_neighbor.mpr h) = w :=
  Sym2.congr_right.mp (Sym2.other_spec' (G.mem_incidence_iff_neighbor.mpr h).right)

/-- There is an equivalence between the set of edges incident to a given
vertex and the set of vertices adjacent to the vertex. -/
@[simps]
/--
Definition of `incidenceSetEquivNeighborSet` / `incidenceSetEquivNeighborSet` 的定义

English:
definition incidenceSetEquivNeighborSet
  signature: (v : V)
  body: ⟨G.otherVertexOfIncident e.2, G.incidence_other_prop e.2⟩
  invFun w := ⟨s(v, w.1), G.mem_incidence_iff_neighbor.mpr w.2⟩
  left_inv x := by simp [otherVertexOfIncident]
  right_inv := fun ⟨w, hw⟩ => by
    simp only [Subtype.mk.injEq]
    exact incidence_other_neighbor_edge _ hw

中文:
定义 incidenceSetEquivNeighborSet
  签名: (v : V)
  定义体: ⟨G.otherVertexOfIncident e.2, G.incidence_other_prop e.2⟩
  invFun w := ⟨s(v, w.1), G.mem_incidence_iff_neighbor.mpr w.2⟩
  left_inv x := by simp [otherVertexOfIncident]
  right_inv := fun ⟨w, hw⟩ => by
    simp only [Subtype.mk.injEq]
    exact incidence_other_neighbor_edge _ hw

Depends on / 依赖: G.incidence_other_prop, G.otherVertexOfIncident, incidence_other_prop, otherVertexOfIncident
-/
def incidenceSetEquivNeighborSet (v : V) : G.incidenceSet v ≃ G.neighborSet v where
  toFun e := ⟨G.otherVertexOfIncident e.2, G.incidence_other_prop e.2⟩
  invFun w := ⟨s(v, w.1), G.mem_incidence_iff_neighbor.mpr w.2⟩
  left_inv x := by simp [otherVertexOfIncident]
  right_inv := fun ⟨w, hw⟩ => by
    simp only [Subtype.mk.injEq]
    exact incidence_other_neighbor_edge _ hw

end Incidence

section IsCompleteBetween

variable {s t : Set V}

/--
Definition of `IsCompleteBetween` / `IsCompleteBetween` 的定义

English:
definition IsCompleteBetween
  signature: (G : SimpleGraph V) (s t : Set V)
  body: forall ⦃v₁⦄, v₁ in s -> forall ⦃v₂⦄, v₂ in t -> G.Adj v₁ v₂

中文:
定义 IsCompleteBetween
  签名: (G : SimpleGraph V) (s t : Set V)
  定义体: forall ⦃v₁⦄, v₁ in s -> forall ⦃v₂⦄, v₂ in t -> G.Adj v₁ v₂

Depends on / 依赖: G.Adj
-/
def IsCompleteBetween (G : SimpleGraph V) (s t : Set V) :=
  forall ⦃v₁⦄, v₁ in s -> forall ⦃v₂⦄, v₂ in t -> G.Adj v₁ v₂

/--
theorem `IsCompleteBetween.disjoint` / 定理 `IsCompleteBetween.disjoint`

English:
theorem IsCompleteBetween.disjoint
  given: (h : G.IsCompleteBetween s t)
  statement: Disjoint s t
  proof: Set.disjoint_left.mpr fun _v hv₁ hv₂ => G.irrefl (h hv₁ hv₂)

中文:
定理 IsCompleteBetween.disjoint
  条件: (h : G.IsCompleteBetween s t)
  结论: Disjoint s t
  证明: Set.disjoint_left.mpr fun _v hv₁ hv₂ => G.irrefl (h hv₁ hv₂)

Depends on / 依赖: G.irrefl, Set.disjoint_left.mpr, disjoint_left, irrefl
-/
theorem IsCompleteBetween.disjoint (h : G.IsCompleteBetween s t) : Disjoint s t :=
  Set.disjoint_left.mpr fun _v hv₁ hv₂ => G.irrefl (h hv₁ hv₂)

/--
theorem `isCompleteBetween_comm` / 定理 `isCompleteBetween_comm`

English:
theorem isCompleteBetween_comm
  statement: G.IsCompleteBetween s t ↔ G.IsCompleteBetween t s where
  proof: (h h₂ h₁).symm
  mpr h _ h₁ _ h₂ := (h h₂ h₁).symm

alias ⟨IsCompleteBetween.symm, _⟩ := isCompleteBetween_comm

中文:
定理 isCompleteBetween_comm
  结论: G.IsCompleteBetween s t ↔ G.IsCompleteBetween t s where
  证明: (h h₂ h₁).symm
  mpr h _ h₁ _ h₂ := (h h₂ h₁).symm

alias ⟨IsCompleteBetween.symm, _⟩ := isCompleteBetween_comm
-/
theorem isCompleteBetween_comm : G.IsCompleteBetween s t ↔ G.IsCompleteBetween t s where
  mp h _ h₁ _ h₂ := (h h₂ h₁).symm
  mpr h _ h₁ _ h₂ := (h h₂ h₁).symm

alias ⟨IsCompleteBetween.symm, _⟩ := isCompleteBetween_comm

end IsCompleteBetween

section Subsingleton

/--
theorem `subsingleton_iff` / 定理 `subsingleton_iff`

English:
theorem subsingleton_iff
  statement: Subsingleton (SimpleGraph V) ↔ Subsingleton V
  proof: by
  refine ⟨fun h => ?_, fun _ => Unique.instSubsingleton⟩
  contrapose! h
  exact instNontrivial

中文:
定理 subsingleton_iff
  结论: Subsingleton (SimpleGraph V) ↔ Subsingleton V
  证明: by
  refine ⟨fun h => ?_, fun _ => Unique.instSubsingleton⟩
  contrapose! h
  exact instNontrivial
-/
protected theorem subsingleton_iff : Subsingleton (SimpleGraph V) ↔ Subsingleton V := by
  refine ⟨fun h => ?_, fun _ => Unique.instSubsingleton⟩
  contrapose! h
  exact instNontrivial

/--
theorem `nontrivial_iff` / 定理 `nontrivial_iff`

English:
theorem nontrivial_iff
  statement: Nontrivial (SimpleGraph V) ↔ Nontrivial V
  proof: by
  refine ⟨fun h => ?_, fun _ => instNontrivial⟩
  contrapose! h
  exact Unique.instSubsingleton

中文:
定理 nontrivial_iff
  结论: Nontrivial (SimpleGraph V) ↔ Nontrivial V
  证明: by
  refine ⟨fun h => ?_, fun _ => instNontrivial⟩
  contrapose! h
  exact Unique.instSubsingleton
-/
protected theorem nontrivial_iff : Nontrivial (SimpleGraph V) ↔ Nontrivial V := by
  refine ⟨fun h => ?_, fun _ => instNontrivial⟩
  contrapose! h
  exact Unique.instSubsingleton

end Subsingleton

/--
Definition of `IsIsolated` / `IsIsolated` 的定义

English:
definition IsIsolated
  signature: (G : SimpleGraph V) (v : V)
  body: forall w, ¬ G.Adj v w

中文:
定义 IsIsolated
  签名: (G : SimpleGraph V) (v : V)
  定义体: forall w, ¬ G.Adj v w

Depends on / 依赖: G.Adj
-/
def IsIsolated (G : SimpleGraph V) (v : V) : Prop := forall w, ¬ G.Adj v w

/--
lemma `neighborSet_eq_empty` / 引理 `neighborSet_eq_empty`

English:
lemma neighborSet_eq_empty
  statement: G.neighborSet v = ∅ ↔ G.IsIsolated v
  proof: by
  simp [neighborSet, IsIsolated, Set.ext_iff]

中文:
引理 neighborSet_eq_empty
  结论: G.neighborSet v = ∅ ↔ G.IsIsolated v
  证明: by
  simp [neighborSet, IsIsolated, Set.ext_iff]
-/
@[simp] lemma neighborSet_eq_empty : G.neighborSet v = ∅ ↔ G.IsIsolated v := by
  simp [neighborSet, IsIsolated, Set.ext_iff]

/--
lemma `neighborSet_nonempty` / 引理 `neighborSet_nonempty`

English:
lemma neighborSet_nonempty
  statement: (G.neighborSet v).Nonempty ↔ ¬ G.IsIsolated v
  proof: by
  simp [Set.nonempty_iff_ne_empty]

protected alias ⟨IsIsolated.of_neighborSet_eq_empty, IsIsolated.neighborSet_eq_empty⟩ :=
  neighborSet_eq_empty

中文:
引理 neighborSet_nonempty
  结论: (G.neighborSet v).Nonempty ↔ ¬ G.IsIsolated v
  证明: by
  simp [Set.nonempty_iff_ne_empty]

protected alias ⟨IsIsolated.of_neighborSet_eq_empty, IsIsolated.neighborSet_eq_empty⟩ :=
  neighborSet_eq_empty
-/
@[simp] lemma neighborSet_nonempty : (G.neighborSet v).Nonempty ↔ ¬ G.IsIsolated v := by
  simp [Set.nonempty_iff_ne_empty]

protected alias ⟨IsIsolated.of_neighborSet_eq_empty, IsIsolated.neighborSet_eq_empty⟩ :=
  neighborSet_eq_empty

attribute [simp] IsIsolated.neighborSet_eq_empty

/--
lemma `mem_support_iff_not_isIsolated` / 引理 `mem_support_iff_not_isIsolated`

English:
lemma mem_support_iff_not_isIsolated
  statement: v in G.support ↔ ¬ G.IsIsolated v
  proof: by
  simp [mem_support, IsIsolated]

@[simp]

中文:
引理 mem_support_iff_not_isIsolated
  结论: v in G.support ↔ ¬ G.IsIsolated v
  证明: by
  simp [mem_support, IsIsolated]

@[simp]

Depends on / 依赖: IsIsolated, mem_support
-/
lemma mem_support_iff_not_isIsolated : v in G.support ↔ ¬ G.IsIsolated v := by
  simp [mem_support, IsIsolated]

@[simp]
/--
theorem `notMem_support_iff_isIsolated` / 定理 `notMem_support_iff_isIsolated`

English:
theorem notMem_support_iff_isIsolated
  statement: v ∉ G.support ↔ G.IsIsolated v
  proof: by
  simp [mem_support_iff_not_isIsolated]

中文:
定理 notMem_support_iff_isIsolated
  结论: v ∉ G.support ↔ G.IsIsolated v
  证明: by
  simp [mem_support_iff_not_isIsolated]

Depends on / 依赖: mem_support_iff_not_isIsolated
-/
theorem notMem_support_iff_isIsolated : v ∉ G.support ↔ G.IsIsolated v := by
  simp [mem_support_iff_not_isIsolated]

variable {G} in
/--
theorem `exists_adj_iff_not_isIsolated` / 定理 `exists_adj_iff_not_isIsolated`

English:
theorem exists_adj_iff_not_isIsolated
  statement: (exists u, G.Adj v u) ↔ ¬G.IsIsolated v
  proof: by
  simp [IsIsolated]

@[simp]

中文:
定理 exists_adj_iff_not_isIsolated
  结论: (存在 u, G.Adj v u) ↔ ¬G.IsIsolated v
  证明: by
  simp [IsIsolated]

@[simp]

Depends on / 依赖: IsIsolated
-/
theorem exists_adj_iff_not_isIsolated : (exists u, G.Adj v u) ↔ ¬G.IsIsolated v := by
  simp [IsIsolated]

@[simp]
/--
theorem `IsIsolated.of_subsingleton` / 定理 `IsIsolated.of_subsingleton`

English:
theorem IsIsolated.of_subsingleton
  given: [Subsingleton V] (G : SimpleGraph V) (v : V)
  proof: fun _ hadj => not_nontrivial V hadj.nontrivial

中文:
定理 IsIsolated.of_subsingleton
  条件: [Subsingleton V] (G : SimpleGraph V) (v : V)
  证明: fun _ hadj => not_nontrivial V hadj.nontrivial

Depends on / 依赖: hadj.nontrivial, nontrivial, not_nontrivial
-/
theorem IsIsolated.of_subsingleton [Subsingleton V] (G : SimpleGraph V) (v : V) :
    G.IsIsolated v :=
  fun _ hadj => not_nontrivial V hadj.nontrivial

variable {G} in
/--
theorem `nontrivial_of_not_isIsolated` / 定理 `nontrivial_of_not_isIsolated`

English:
theorem nontrivial_of_not_isIsolated
  given: (h : ¬G.IsIsolated v)
  statement: Nontrivial V
  proof: .elim fun _ => Adj.nontrivial exists_adj_iff_not_isIsolated.mpr h

中文:
定理 nontrivial_of_not_isIsolated
  条件: (h : ¬G.IsIsolated v)
  结论: Nontrivial V
  证明: .elim fun _ => Adj.nontrivial exists_adj_iff_not_isIsolated.mpr h

Depends on / 依赖: Adj.nontrivial, exists_adj_iff_not_isIsolated, exists_adj_iff_not_isIsolated.mpr, nontrivial
-/
theorem nontrivial_of_not_isIsolated (h : ¬G.IsIsolated v) : Nontrivial V :=
.elim fun _ => Adj.nontrivial exists_adj_iff_not_isIsolated.mpr h

variable {G} in
/--
theorem `Adj.not_isIsolated_left` / 定理 `Adj.not_isIsolated_left`

English:
theorem Adj.not_isIsolated_left
  given: (h : G.Adj u v)
  statement: ¬G.IsIsolated u
  proof: exists_adj_iff_not_isIsolated.mp ⟨_, h⟩

中文:
定理 Adj.not_isIsolated_left
  条件: (h : G.Adj u v)
  结论: ¬G.IsIsolated u
  证明: exists_adj_iff_not_isIsolated.mp ⟨_, h⟩

Depends on / 依赖: exists_adj_iff_not_isIsolated, exists_adj_iff_not_isIsolated.mp
-/
theorem Adj.not_isIsolated_left (h : G.Adj u v) : ¬G.IsIsolated u :=
  exists_adj_iff_not_isIsolated.mp ⟨_, h⟩

variable {G} in
/--
theorem `Adj.not_isIsolated_right` / 定理 `Adj.not_isIsolated_right`

English:
theorem Adj.not_isIsolated_right
  given: (h : G.Adj u v)
  statement: ¬G.IsIsolated v
  proof: h.symm.not_isIsolated_left

@[simp]

中文:
定理 Adj.not_isIsolated_right
  条件: (h : G.Adj u v)
  结论: ¬G.IsIsolated v
  证明: h.symm.not_isIsolated_left

@[simp]

Depends on / 依赖: h.symm.not_isIsolated_left, not_isIsolated_left
-/
theorem Adj.not_isIsolated_right (h : G.Adj u v) : ¬G.IsIsolated v :=
  h.symm.not_isIsolated_left

@[simp]
/--
theorem `IsIsolated.bot` / 定理 `IsIsolated.bot`

English:
theorem IsIsolated.bot
  statement: IsIsolated ⊥ v
  proof: .mp neighborSet_bot neighborSet_eq_empty _

@[deprecated (since := "2026-06-19")]
alias isIsolated_bot := IsIsolated.bot

中文:
定理 IsIsolated.bot
  结论: IsIsolated ⊥ v
  证明: .mp neighborSet_bot neighborSet_eq_empty _

@[deprecated (since := "2026-06-19")]
alias isIsolated_bot := IsIsolated.bot
-/
protected theorem IsIsolated.bot : IsIsolated ⊥ v :=
.mp neighborSet_bot neighborSet_eq_empty _

@[deprecated (since := "2026-06-19")]
alias isIsolated_bot := IsIsolated.bot

/--
theorem `eq_bot_iff_isIsolated` / 定理 `eq_bot_iff_isIsolated`

English:
theorem eq_bot_iff_isIsolated
  statement: G = ⊥ ↔ forall v, G.IsIsolated v
  proof: by
  simp [eq_bot_iff_forall_not_adj, ← neighborSet_eq_empty, Set.eq_empty_iff_forall_notMem]

中文:
定理 eq_bot_iff_isIsolated
  结论: G = ⊥ ↔ 对任意 v, G.IsIsolated v
  证明: by
  simp [eq_bot_iff_forall_not_adj, ← neighborSet_eq_empty, Set.eq_empty_iff_forall_notMem]

Depends on / 依赖: Set.eq_empty_iff_forall_notMem, eq_bot_iff_forall_not_adj, eq_empty_iff_forall_notMem, neighborSet_eq_empty
-/
theorem eq_bot_iff_isIsolated : G = ⊥ ↔ forall v, G.IsIsolated v := by
  simp [eq_bot_iff_forall_not_adj, ← neighborSet_eq_empty, Set.eq_empty_iff_forall_notMem]

section IsUniversal

variable {G}

/--
Definition of `IsUniversal` / `IsUniversal` 的定义

English:
definition IsUniversal
  signature: (G : SimpleGraph V) (v : V)
  body: forall ⦃w⦄, v != w -> G.Adj v w

中文:
定义 IsUniversal
  签名: (G : SimpleGraph V) (v : V)
  定义体: forall ⦃w⦄, v != w -> G.Adj v w

Depends on / 依赖: G.Adj
-/
def IsUniversal (G : SimpleGraph V) (v : V) : Prop := forall ⦃w⦄, v != w -> G.Adj v w

/--
lemma `insert_neighborSet_eq_univ` / 引理 `insert_neighborSet_eq_univ`

English:
lemma insert_neighborSet_eq_univ
  proof: by
  simp only [Set.ext_iff, Set.mem_insert_iff, mem_neighborSet, IsUniversal]
  grind

中文:
引理 insert_neighborSet_eq_univ
  证明: by
  simp only [Set.ext_iff, Set.mem_insert_iff, mem_neighborSet, IsUniversal]
  grind
-/
@[simp] lemma insert_neighborSet_eq_univ :
    insert v (G.neighborSet v) = Set.univ ↔ G.IsUniversal v := by
  simp only [Set.ext_iff, Set.mem_insert_iff, mem_neighborSet, IsUniversal]
  grind

/--
lemma `neighborSet_eq_compl_singleton` / 引理 `neighborSet_eq_compl_singleton`

English:
lemma neighborSet_eq_compl_singleton
  statement: G.neighborSet v = {v}ᶜ ↔ G.IsUniversal v
  proof: by
  grind [insert_neighborSet_eq_univ, notMem_neighborSet_self]

protected alias ⟨IsUniversal.of_neighborSet_eq, IsUniversal.neighborSet_eq⟩ :=
  neighborSet_eq_compl_singleton

@[simp]

中文:
引理 neighborSet_eq_compl_singleton
  结论: G.neighborSet v = {v}ᶜ ↔ G.IsUniversal v
  证明: by
  grind [insert_neighborSet_eq_univ, notMem_neighborSet_self]

protected alias ⟨IsUniversal.of_neighborSet_eq, IsUniversal.neighborSet_eq⟩ :=
  neighborSet_eq_compl_singleton

@[simp]
-/
@[simp] lemma neighborSet_eq_compl_singleton : G.neighborSet v = {v}ᶜ ↔ G.IsUniversal v := by
  grind [insert_neighborSet_eq_univ, notMem_neighborSet_self]

protected alias ⟨IsUniversal.of_neighborSet_eq, IsUniversal.neighborSet_eq⟩ :=
  neighborSet_eq_compl_singleton

@[simp]
/--
theorem `IsUniversal.of_subsingleton` / 定理 `IsUniversal.of_subsingleton`

English:
theorem IsUniversal.of_subsingleton
  given: [Subsingleton V]
  statement: G.IsUniversal v
  proof: fun _ hne => False.elim hne (Subsingleton.elim ..)

中文:
定理 IsUniversal.of_subsingleton
  条件: [Subsingleton V]
  结论: G.IsUniversal v
  证明: fun _ hne => False.elim hne (Subsingleton.elim ..)

Depends on / 依赖: False.elim, Subsingleton, Subsingleton.elim
-/
theorem IsUniversal.of_subsingleton [Subsingleton V] : G.IsUniversal v :=
fun _ hne => False.elim hne (Subsingleton.elim ..)

/--
theorem `IsUniversal.not_isIsolated` / 定理 `IsUniversal.not_isIsolated`

English:
theorem IsUniversal.not_isIsolated
  given: [Nontrivial V] (h : G.IsUniversal v) (w : V)
  proof: by
  by_cases h' : v = w
  · obtain ⟨u, hu⟩ := exists_ne v
    exact h' ▸ Adj.not_isIsolated_left (h hu.symm)
  · exact Adj.not_isIsolated_right (h h')

中文:
定理 IsUniversal.not_isIsolated
  条件: [Nontrivial V] (h : G.IsUniversal v) (w : V)
  证明: by
  by_cases h' : v = w
  · obtain ⟨u, hu⟩ := exists_ne v
    exact h' ▸ Adj.not_isIsolated_left (h hu.symm)
  · exact Adj.not_isIsolated_right (h h')

Depends on / 依赖: Adj.not_isIsolated_left, Adj.not_isIsolated_right, exists_ne, hu.symm, not_isIsolated_left, not_isIsolated_right
-/
theorem IsUniversal.not_isIsolated [Nontrivial V] (h : G.IsUniversal v) (w : V) :
    ¬G.IsIsolated w := by
  by_cases h' : v = w
  · obtain ⟨u, hu⟩ := exists_ne v
    exact h' ▸ Adj.not_isIsolated_left (h hu.symm)
  · exact Adj.not_isIsolated_right (h h')

/--
theorem `IsIsolated.not_isUniversal` / 定理 `IsIsolated.not_isUniversal`

English:
theorem IsIsolated.not_isUniversal
  given: [Nontrivial V] (h : G.IsIsolated v) (w : V)
  proof: by
  contrapose! h
  exact h.not_isIsolated v

@[simp]

中文:
定理 IsIsolated.not_isUniversal
  条件: [Nontrivial V] (h : G.IsIsolated v) (w : V)
  证明: by
  contrapose! h
  exact h.not_isIsolated v

@[simp]

Depends on / 依赖: contrapose, h.not_isIsolated, not_isIsolated
-/
theorem IsIsolated.not_isUniversal [Nontrivial V] (h : G.IsIsolated v) (w : V) :
    ¬G.IsUniversal w := by
  contrapose! h
  exact h.not_isIsolated v

@[simp]
/--
theorem `isUniversal_compl_iff_isIsolated` / 定理 `isUniversal_compl_iff_isIsolated`

English:
theorem isUniversal_compl_iff_isIsolated
  statement: Gᶜ.IsUniversal v ↔ G.IsIsolated v
  proof: by
  refine ⟨fun h x hx => ?_, fun h x hx => ?_⟩
  · simpa [hx] using h hx.ne
  · simpa [hx] using h x

alias ⟨IsIsolated.of_isUniversal_compl, _⟩ := isUniversal_compl_iff_isIsolated

@[simp]

中文:
定理 isUniversal_compl_iff_isIsolated
  结论: Gᶜ.IsUniversal v ↔ G.IsIsolated v
  证明: by
  refine ⟨fun h x hx => ?_, fun h x hx => ?_⟩
  · simpa [hx] using h hx.ne
  · simpa [hx] using h x

alias ⟨IsIsolated.of_isUniversal_compl, _⟩ := isUniversal_compl_iff_isIsolated

@[simp]

Depends on / 依赖: hx.ne
-/
theorem isUniversal_compl_iff_isIsolated : Gᶜ.IsUniversal v ↔ G.IsIsolated v := by
  refine ⟨fun h x hx => ?_, fun h x hx => ?_⟩
  · simpa [hx] using h hx.ne
  · simpa [hx] using h x

alias ⟨IsIsolated.of_isUniversal_compl, _⟩ := isUniversal_compl_iff_isIsolated

@[simp]
/--
theorem `isIsolated_compl_iff_isUniversal` / 定理 `isIsolated_compl_iff_isUniversal`

English:
theorem isIsolated_compl_iff_isUniversal
  statement: Gᶜ.IsIsolated v ↔ G.IsUniversal v
  proof: by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · simpa using isUniversal_compl_iff_isIsolated.mpr h
  · exact isUniversal_compl_iff_isIsolated.mp (by simpa)

alias ⟨IsUniversal.of_isIsolated_compl, _⟩ := isIsolated_compl_iff_isUniversal

中文:
定理 isIsolated_compl_iff_isUniversal
  结论: Gᶜ.IsIsolated v ↔ G.IsUniversal v
  证明: by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · simpa using isUniversal_compl_iff_isIsolated.mpr h
  · exact isUniversal_compl_iff_isIsolated.mp (by simpa)

alias ⟨IsUniversal.of_isIsolated_compl, _⟩ := isIsolated_compl_iff_isUniversal

Depends on / 依赖: isUniversal_compl_iff_isIsolated, isUniversal_compl_iff_isIsolated.mp, isUniversal_compl_iff_isIsolated.mpr
-/
theorem isIsolated_compl_iff_isUniversal : Gᶜ.IsIsolated v ↔ G.IsUniversal v := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · simpa using isUniversal_compl_iff_isIsolated.mpr h
  · exact isUniversal_compl_iff_isIsolated.mp (by simpa)

alias ⟨IsUniversal.of_isIsolated_compl, _⟩ := isIsolated_compl_iff_isUniversal

/--
theorem `eq_top_iff_forall_isUniversal` / 定理 `eq_top_iff_forall_isUniversal`

English:
theorem eq_top_iff_forall_isUniversal
  statement: G = ⊤ ↔ forall v, G.IsUniversal v
  proof: by
  simp [eq_top_iff_forall_ne_adj, IsUniversal]

@[simp]

中文:
定理 eq_top_iff_forall_isUniversal
  结论: G = ⊤ ↔ 对任意 v, G.IsUniversal v
  证明: by
  simp [eq_top_iff_forall_ne_adj, IsUniversal]

@[simp]

Depends on / 依赖: IsUniversal, eq_top_iff_forall_ne_adj
-/
theorem eq_top_iff_forall_isUniversal : G = ⊤ ↔ forall v, G.IsUniversal v := by
  simp [eq_top_iff_forall_ne_adj, IsUniversal]

@[simp]
/--
theorem `IsUniversal.top` / 定理 `IsUniversal.top`

English:
theorem IsUniversal.top
  statement: IsUniversal ⊤ v
  proof: eq_top_iff_forall_isUniversal.mp rfl v

中文:
定理 IsUniversal.top
  结论: IsUniversal ⊤ v
  证明: eq_top_iff_forall_isUniversal.mp rfl v
-/
protected theorem IsUniversal.top : IsUniversal ⊤ v :=
  eq_top_iff_forall_isUniversal.mp rfl v

end IsUniversal

end SimpleGraph
