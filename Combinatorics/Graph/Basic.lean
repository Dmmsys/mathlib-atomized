/-
Copyright (c) 2025 Peter Nelson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Nelson, Jun Kwon
-/
module

public import Mathlib.Data.Set.Basic
public import Mathlib.Data.Sym.Sym2

/-!
# Multigraphs

A multigraph is a set of vertices and a set of edges,
together with incidence data that associates each edge `e`
with an unordered pair `s(x,y)` of vertices called the *ends* of `e`.
The pair of `e` and `s(x,y)` is called a *link*.
The vertices `x` and `y` may be equal, in which case `e` is a *loop*.
There may be more than one edge with the same ends.

If a multigraph has no loops and has at most one edge for every given ends, it is called *simple*,
and these objects are also formalized as `SimpleGraph`.

This module defines `Graph α β` for a vertex type `α` and an edge type `β`,
and gives basic API for incidence, adjacency and extensionality.
The design broadly follows [Chou1994].

## Main definitions

For `G : Graph α β`, ...

* `V(G)` denotes the vertex set of `G` as a term in `Set α`.
* `E(G)` denotes the edge set of `G` as a term in `Set β`.
* `G.IsLink e x y` means that the edge `e : β` has vertices `x : α` and `y : α` as its ends.
* `G.Inc e x` means that the edge `e : β` has `x` as one of its ends.
* `G.Adj x y` means that there is an edge `e` having `x` and `y` as its ends.
* `G.IsLoopAt e x` means that `e` is a loop edge with both ends equal to `x`.
* `G.IsNonloopAt e x` means that `e` is a non-loop edge with one end equal to `x`.
* `G.incidenceSet x` is the set of edges incident to `x`.
* `G.loopSet x` is the set of loops with both ends equal to `x`.
* `G.copy` creates a definitional copy of a graph with propositionally equal data.
* `G.Compatible H` means that `G` and `H` agree on the incidence relation for their shared edges.
* `Graph.noEdge V` is the graph with vertex set `V` and no edges.
* `Graph.bouquet v E` is the graph with vertex set `{v}` and edge set `E`,
  where every edge is a loop at `v`.
* `Graph.banana u v E` is the graph with vertex set `{u, v}` and edge set `E`,
  where every edge connects `u` and `v`.

## Implementation notes

Unlike the design of `SimpleGraph`, the vertex and edge sets of `G` are modelled as sets
`V(G) : Set α` and `E(G) : Set β`, within ambient types, rather than being types themselves.
This mimics the 'embedded set' design used in `Matroid`, which seems to be more convenient for
formalizing real-world proofs in combinatorics.

A specific advantage is that this allows subgraphs of `G : Graph α β` to also exist on
an equal footing with `G` as terms in `Graph α β`,
and so there is no need for a `Graph.subgraph` type and all the associated
definitions and canonical coercion maps. The same will go for minors and the various other
partial orders on multigraphs.

The main tradeoff is that parts of the API will need to care about whether a term
`x : α` or `e : β` is a 'real' vertex or edge of the graph, rather than something outside
the vertex or edge set. This is an issue, but is likely amenable to automation.

## Notation

Reflecting written mathematics, we use the compact notations `V(G)` and `E(G)` to
refer to the `vertexSet` and `edgeSet` of `G : Graph α β`.
If `G.IsLink e x y` then we refer to `e` as `edge` and `x` and `y` as `left` and `right` in names.
-/

@[expose] public section

variable {α β : Type*} {x y z u v w : α} {e f : β}

open Set

/--
Definition of `Graph` / `Graph` 的定义

English:
structure Graph
  parameters: (α β : Type*)
  axioms and operations (7):
    - vertexSet : Set α
    - IsLink : β -> α -> α -> Prop
    - edgeSet : Set β  [default: {e | exists x y, IsLink e x y}]
    - isLink_symm : forall ⦃e⦄, e in edgeSet -> Std.Symm (IsLink e)
    - eq_or_eq_of_isLink_of_isLink : forall ⦃e x y v w⦄, IsLink e x y -> IsLink e v w -> x = v ∨ x = w
    - edge_mem_iff_exists_isLink : forall e, e in edgeSet ↔ exists x y, IsLink e x y  [default: by exact fun _ => Iff.rfl]
    - left_mem_of_isLink : forall ⦃e x y⦄, IsLink e x y -> x in vertexSet  [default: by grind]

中文:
结构 图
  参数: (α β : 类型)
  公理与运算 (7 个):
    - vertexSet : 集合 α
    - IsLink : β -> α -> α -> 命题
    - edgeSet : 集合 β  [默认: {e | exists x y, IsLink e x y}]
    - isLink_symm : 对任意 ⦃e⦄, e in edgeSet -> Std.Symm (IsLink e)
    - eq_or_eq_of_isLink_of_isLink : 对任意 ⦃e x y v w⦄, IsLink e x y -> IsLink e v w -> x = v ∨ x = w
    - edge_mem_iff_exists_isLink : 对任意 e, e in edgeSet ↔ 存在 x y, IsLink e x y  [默认: by exact fun _ => Iff.rfl]
    - left_mem_of_isLink : 对任意 ⦃e x y⦄, IsLink e x y -> x in vertexSet  [默认: by grind]

Depends on / 依赖: IsLink
-/
structure Graph (α β : Type*) where
  /-- The vertex set. -/
  vertexSet : Set α
  /-- The binary incidence predicate, stating that `x` and `y` are the ends of an edge `e`.
  If `G.IsLink e x y` then we refer to `e` as `edge` and `x` and `y` as `left` and `right`. -/
  IsLink : β -> α -> α -> Prop
  /-- The edge set. -/
  edgeSet : Set β := {e | exists x y, IsLink e x y}
  /-- If `e` goes from `x` to `y`, it goes from `y` to `x`. -/
  isLink_symm : forall ⦃e⦄, e in edgeSet -> Std.Symm (IsLink e)
  /-- An edge is incident with at most one pair of vertices. -/
  eq_or_eq_of_isLink_of_isLink : forall ⦃e x y v w⦄, IsLink e x y -> IsLink e v w -> x = v ∨ x = w
  /-- An edge `e` is incident to something if and only if `e` is in the edge set. -/
  edge_mem_iff_exists_isLink : forall e, e in edgeSet ↔ exists x y, IsLink e x y := by exact fun _ => Iff.rfl
  /-- If some edge `e` is incident to `x`, then `x ∈ V`. -/
  left_mem_of_isLink : forall ⦃e x y⦄, IsLink e x y -> x in vertexSet := by grind

initialize_simps_projections Graph (as_prefix edgeSet, as_prefix vertexSet, IsLink -> isLink)

namespace Graph

variable {G H : Graph α β}

/-- `V(G)` denotes the `vertexSet` of a graph `G`. -/
scoped notation "V(" G ")" => Graph.vertexSet G

/-- `E(G)` denotes the `edgeSet` of a graph `G`. -/
scoped notation "E(" G ")" => Graph.edgeSet G


/--
lemma `IsLink.edge_mem` / 引理 `IsLink.edge_mem`

English:
lemma IsLink.edge_mem
  given: (h : G.IsLink e x y)
  statement: e in E(G)
  proof: (edge_mem_iff_exists_isLink ..).2 ⟨x, y, h⟩

@[simp]

中文:
引理 IsLink.edge_mem
  条件: (h : G.IsLink e x y)
  结论: e in E(G)
  证明: (edge_mem_iff_exists_isLink ..).2 ⟨x, y, h⟩

@[simp]

Depends on / 依赖: edge_mem_iff_exists_isLink
-/
lemma IsLink.edge_mem (h : G.IsLink e x y) : e in E(G) :=
  (edge_mem_iff_exists_isLink ..).2 ⟨x, y, h⟩

@[simp]
/--
lemma `not_isLink_of_notMem_edgeSet` / 引理 `not_isLink_of_notMem_edgeSet`

English:
lemma not_isLink_of_notMem_edgeSet
  given: (he : e ∉ E(G))
  statement: ¬ G.IsLink e x y
  proof: mt IsLink.edge_mem he

中文:
引理 not_isLink_of_notMem_edgeSet
  条件: (he : e ∉ E(G))
  结论: ¬ G.IsLink e x y
  证明: mt IsLink.edge_mem he

Depends on / 依赖: IsLink, IsLink.edge_mem, edge_mem
-/
lemma not_isLink_of_notMem_edgeSet (he : e ∉ E(G)) : ¬ G.IsLink e x y :=
  mt IsLink.edge_mem he

/--
lemma `IsLink.symm` / 引理 `IsLink.symm`

English:
lemma IsLink.symm
  given: (h : G.IsLink e x y)
  statement: G.IsLink e y x
  proof: .symm x y h G.isLink_symm h.edge_mem

@[grind ->]

中文:
引理 IsLink.symm
  条件: (h : G.IsLink e x y)
  结论: G.IsLink e y x
  证明: .symm x y h G.isLink_symm h.edge_mem

@[grind ->]
-/
protected lemma IsLink.symm (h : G.IsLink e x y) : G.IsLink e y x :=
.symm x y h G.isLink_symm h.edge_mem

@[grind ->]
/--
lemma `IsLink.left_mem` / 引理 `IsLink.left_mem`

English:
lemma IsLink.left_mem
  given: (h : G.IsLink e x y)
  statement: x in V(G)
  proof: G.left_mem_of_isLink h

@[grind ->]

中文:
引理 IsLink.left_mem
  条件: (h : G.IsLink e x y)
  结论: x in V(G)
  证明: G.left_mem_of_isLink h

@[grind ->]

Depends on / 依赖: G.left_mem_of_isLink, left_mem_of_isLink
-/
lemma IsLink.left_mem (h : G.IsLink e x y) : x in V(G) :=
  G.left_mem_of_isLink h

@[grind ->]
/--
lemma `IsLink.right_mem` / 引理 `IsLink.right_mem`

English:
lemma IsLink.right_mem
  given: (h : G.IsLink e x y)
  statement: y in V(G)
  proof: h.symm.left_mem

中文:
引理 IsLink.right_mem
  条件: (h : G.IsLink e x y)
  结论: y in V(G)
  证明: h.symm.left_mem

Depends on / 依赖: h.symm.left_mem, left_mem
-/
lemma IsLink.right_mem (h : G.IsLink e x y) : y in V(G) :=
  h.symm.left_mem

/--
lemma `isLink_comm` / 引理 `isLink_comm`

English:
lemma isLink_comm
  statement: G.IsLink e x y ↔ G.IsLink e y x
  proof: ⟨.symm, .symm⟩

中文:
引理 isLink_comm
  结论: G.IsLink e x y ↔ G.IsLink e y x
  证明: ⟨.symm, .symm⟩
-/
lemma isLink_comm : G.IsLink e x y ↔ G.IsLink e y x :=
  ⟨.symm, .symm⟩

/--
lemma `exists_isLink_of_mem_edgeSet` / 引理 `exists_isLink_of_mem_edgeSet`

English:
lemma exists_isLink_of_mem_edgeSet
  given: (h : e in E(G))
  statement: exists x y, G.IsLink e x y
  proof: (edge_mem_iff_exists_isLink ..).1 h

中文:
引理 存在_isLink_of_mem_edgeSet
  条件: (h : e in E(G))
  结论: 存在 x y, G.IsLink e x y
  证明: (edge_mem_iff_exists_isLink ..).1 h

Depends on / 依赖: edge_mem_iff_exists_isLink
-/
lemma exists_isLink_of_mem_edgeSet (h : e in E(G)) : exists x y, G.IsLink e x y :=
  (edge_mem_iff_exists_isLink ..).1 h

/--
lemma `edgeSet_eq_setOfPred_exists_isLink` / 引理 `edgeSet_eq_setOfPred_exists_isLink`

English:
lemma edgeSet_eq_setOfPred_exists_isLink
  statement: E(G) = {e | exists x y, G.IsLink e x y}
  proof: Set.ext G.edge_mem_iff_exists_isLink

@[deprecated (since := "2026-07-09")]
alias edgeSet_eq_setOf_exists_isLink := edgeSet_eq_setOfPred_exists_isLink

中文:
引理 edgeSet_eq_setOfPred_存在_isLink
  结论: E(G) = {e | 存在 x y, G.IsLink e x y}
  证明: Set.ext G.edge_mem_iff_exists_isLink

@[deprecated (since := "2026-07-09")]
alias edgeSet_eq_setOf_exists_isLink := edgeSet_eq_setOfPred_exists_isLink

Depends on / 依赖: G.edge_mem_iff_exists_isLink, Set.ext, edge_mem_iff_exists_isLink
-/
lemma edgeSet_eq_setOfPred_exists_isLink : E(G) = {e | exists x y, G.IsLink e x y} :=
  Set.ext G.edge_mem_iff_exists_isLink

@[deprecated (since := "2026-07-09")]
alias edgeSet_eq_setOf_exists_isLink := edgeSet_eq_setOfPred_exists_isLink

/--
lemma `IsLink.left_eq_or_eq` / 引理 `IsLink.left_eq_or_eq`

English:
lemma IsLink.left_eq_or_eq
  given: (h : G.IsLink e x y) (h' : G.IsLink e z w)
  statement: x = z ∨ x = w
  proof: G.eq_or_eq_of_isLink_of_isLink h h'

中文:
引理 IsLink.left_eq_or_eq
  条件: (h : G.IsLink e x y) (h' : G.IsLink e z w)
  结论: x = z ∨ x = w
  证明: G.eq_or_eq_of_isLink_of_isLink h h'

Depends on / 依赖: G.eq_or_eq_of_isLink_of_isLink, eq_or_eq_of_isLink_of_isLink
-/
lemma IsLink.left_eq_or_eq (h : G.IsLink e x y) (h' : G.IsLink e z w) : x = z ∨ x = w :=
  G.eq_or_eq_of_isLink_of_isLink h h'

/--
lemma `IsLink.right_eq_or_eq` / 引理 `IsLink.right_eq_or_eq`

English:
lemma IsLink.right_eq_or_eq
  given: (h : G.IsLink e x y) (h' : G.IsLink e z w)
  statement: y = z ∨ y = w
  proof: h.symm.left_eq_or_eq h'

中文:
引理 IsLink.right_eq_or_eq
  条件: (h : G.IsLink e x y) (h' : G.IsLink e z w)
  结论: y = z ∨ y = w
  证明: h.symm.left_eq_or_eq h'

Depends on / 依赖: h.symm.left_eq_or_eq, left_eq_or_eq
-/
lemma IsLink.right_eq_or_eq (h : G.IsLink e x y) (h' : G.IsLink e z w) : y = z ∨ y = w :=
  h.symm.left_eq_or_eq h'

/--
lemma `IsLink.left_eq_of_right_ne` / 引理 `IsLink.left_eq_of_right_ne`

English:
lemma IsLink.left_eq_of_right_ne
  given: (h : G.IsLink e x y) (h' : G.IsLink e z w) (hzx : x != z)
  proof: (h.left_eq_or_eq h').elim (False.elim ∘ hzx) id

中文:
引理 IsLink.left_eq_of_right_ne
  条件: (h : G.IsLink e x y) (h' : G.IsLink e z w) (hzx : x != z)
  证明: (h.left_eq_or_eq h').elim (False.elim ∘ hzx) id

Depends on / 依赖: False.elim, h.left_eq_or_eq, left_eq_or_eq
-/
lemma IsLink.left_eq_of_right_ne (h : G.IsLink e x y) (h' : G.IsLink e z w) (hzx : x != z) :
    x = w :=
  (h.left_eq_or_eq h').elim (False.elim ∘ hzx) id

/--
lemma `IsLink.right_unique` / 引理 `IsLink.right_unique`

English:
lemma IsLink.right_unique
  given: (h : G.IsLink e x y) (h' : G.IsLink e x z)
  statement: y = z
  proof: by
  obtain rfl | rfl := h.right_eq_or_eq h'.symm
  · rfl
  obtain rfl | rfl := h'.right_eq_or_eq h.symm <;> rfl

中文:
引理 IsLink.right_unique
  条件: (h : G.IsLink e x y) (h' : G.IsLink e x z)
  结论: y = z
  证明: by
  obtain rfl | rfl := h.right_eq_or_eq h'.symm
  · rfl
  obtain rfl | rfl := h'.right_eq_or_eq h.symm <;> rfl

Depends on / 依赖: h.right_eq_or_eq, h.symm, right_eq_or_eq
-/
lemma IsLink.right_unique (h : G.IsLink e x y) (h' : G.IsLink e x z) : y = z := by
  obtain rfl | rfl := h.right_eq_or_eq h'.symm
  · rfl
  obtain rfl | rfl := h'.right_eq_or_eq h.symm <;> rfl

/--
lemma `IsLink.left_unique` / 引理 `IsLink.left_unique`

English:
lemma IsLink.left_unique
  given: (h : G.IsLink e x z) (h' : G.IsLink e y z)
  statement: x = y
  proof: h.symm.right_unique h'.symm

中文:
引理 IsLink.left_unique
  条件: (h : G.IsLink e x z) (h' : G.IsLink e y z)
  结论: x = y
  证明: h.symm.right_unique h'.symm

Depends on / 依赖: h.symm.right_unique, right_unique
-/
lemma IsLink.left_unique (h : G.IsLink e x z) (h' : G.IsLink e y z) : x = y :=
  h.symm.right_unique h'.symm

/--
lemma `IsLink.eq_and_eq_or_eq_and_eq` / 引理 `IsLink.eq_and_eq_or_eq_and_eq`

English:
lemma IsLink.eq_and_eq_or_eq_and_eq
  statement: {x' y' : α} (h : G.IsLink e x y)
  proof: by
  obtain rfl | rfl := h.left_eq_or_eq h'
  · simp [h.right_unique h']
  simp [h'.symm.right_unique h]

中文:
引理 IsLink.eq_and_eq_or_eq_and_eq
  结论: {x' y' : α} (h : G.IsLink e x y)
  证明: by
  obtain rfl | rfl := h.left_eq_or_eq h'
  · simp [h.right_unique h']
  simp [h'.symm.right_unique h]

Depends on / 依赖: h.left_eq_or_eq, h.right_unique, left_eq_or_eq, right_unique, symm.right_unique
-/
lemma IsLink.eq_and_eq_or_eq_and_eq {x' y' : α} (h : G.IsLink e x y)
    (h' : G.IsLink e x' y') : (x = x' ∧ y = y') ∨ (x = y' ∧ y = x') := by
  obtain rfl | rfl := h.left_eq_or_eq h'
  · simp [h.right_unique h']
  simp [h'.symm.right_unique h]

/--
lemma `IsLink.isLink_iff` / 引理 `IsLink.isLink_iff`

English:
lemma IsLink.isLink_iff
  given: (h : G.IsLink e x y) {x' y' : α}
  proof: by
  refine ⟨h.eq_and_eq_or_eq_and_eq, ?_⟩
  rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
  · assumption
  exact h.symm

中文:
引理 IsLink.isLink_iff
  条件: (h : G.IsLink e x y) {x' y' : α}
  证明: by
  refine ⟨h.eq_and_eq_or_eq_and_eq, ?_⟩
  rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
  · assumption
  exact h.symm

Depends on / 依赖: eq_and_eq_or_eq_and_eq, h.eq_and_eq_or_eq_and_eq, h.symm
-/
lemma IsLink.isLink_iff (h : G.IsLink e x y) {x' y' : α} :
    G.IsLink e x' y' ↔ (x = x' ∧ y = y') ∨ (x = y' ∧ y = x') := by
  refine ⟨h.eq_and_eq_or_eq_and_eq, ?_⟩
  rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
  · assumption
  exact h.symm

/--
lemma `IsLink.isLink_iff_sym2_eq` / 引理 `IsLink.isLink_iff_sym2_eq`

English:
lemma IsLink.isLink_iff_sym2_eq
  given: (h : G.IsLink e x y) {x' y' : α}
  proof: by
  rw [h.isLink_iff]; rw [Sym2.eq_iff]

中文:
引理 IsLink.isLink_iff_sym2_eq
  条件: (h : G.IsLink e x y) {x' y' : α}
  证明: by
  rw [h.isLink_iff]; rw [Sym2.eq_iff]

Depends on / 依赖: Sym2.eq_iff, eq_iff, h.isLink_iff, isLink_iff
-/
lemma IsLink.isLink_iff_sym2_eq (h : G.IsLink e x y) {x' y' : α} :
    G.IsLink e x' y' ↔ s(x, y) = s(x', y') := by
  rw [h.isLink_iff]; rw [Sym2.eq_iff]

/-! ### Edge-vertex incidence -/

/--
Definition of `Inc` / `Inc` 的定义

English:
definition Inc
  signature: (G : Graph α β) (e : β) (x : α)
  body: exists y, G.IsLink e x y

中文:
定义 Inc
  签名: (G : 图 α β) (e : β) (x : α)
  定义体: exists y, G.IsLink e x y

Depends on / 依赖: G.IsLink, IsLink
-/
def Inc (G : Graph α β) (e : β) (x : α) : Prop := exists y, G.IsLink e x y

-- Cannot be @[simp] because `x` cannot be inferred by `simp`.
/--
lemma `Inc.edge_mem` / 引理 `Inc.edge_mem`

English:
lemma Inc.edge_mem
  given: (h : G.Inc e x)
  statement: e in E(G)
  proof: h.choose_spec.edge_mem

@[simp]

中文:
引理 Inc.edge_mem
  条件: (h : G.Inc e x)
  结论: e in E(G)
  证明: h.choose_spec.edge_mem

@[simp]

Depends on / 依赖: choose_spec, edge_mem, h.choose_spec.edge_mem
-/
lemma Inc.edge_mem (h : G.Inc e x) : e in E(G) :=
  h.choose_spec.edge_mem

@[simp]
/--
lemma `not_inc_of_notMem_edgeSet` / 引理 `not_inc_of_notMem_edgeSet`

English:
lemma not_inc_of_notMem_edgeSet
  given: (he : e ∉ E(G))
  statement: ¬ G.Inc e x
  proof: mt Inc.edge_mem he

中文:
引理 not_inc_of_notMem_edgeSet
  条件: (he : e ∉ E(G))
  结论: ¬ G.Inc e x
  证明: mt Inc.edge_mem he

Depends on / 依赖: Inc.edge_mem, edge_mem
-/
lemma not_inc_of_notMem_edgeSet (he : e ∉ E(G)) : ¬ G.Inc e x :=
  mt Inc.edge_mem he

-- Cannot be @[simp] because `e` cannot be inferred by `simp`.
/--
lemma `Inc.vertex_mem` / 引理 `Inc.vertex_mem`

English:
lemma Inc.vertex_mem
  given: (h : G.Inc e x)
  statement: x in V(G)
  proof: h.choose_spec.left_mem

中文:
引理 Inc.vertex_mem
  条件: (h : G.Inc e x)
  结论: x in V(G)
  证明: h.choose_spec.left_mem

Depends on / 依赖: choose_spec, h.choose_spec.left_mem, left_mem
-/
lemma Inc.vertex_mem (h : G.Inc e x) : x in V(G) :=
  h.choose_spec.left_mem

-- Cannot be @[simp] because `y` cannot be inferred by `simp`.
/--
lemma `IsLink.inc_left` / 引理 `IsLink.inc_left`

English:
lemma IsLink.inc_left
  given: (h : G.IsLink e x y)
  statement: G.Inc e x
  proof: ⟨y, h⟩

中文:
引理 IsLink.inc_left
  条件: (h : G.IsLink e x y)
  结论: G.Inc e x
  证明: ⟨y, h⟩
-/
lemma IsLink.inc_left (h : G.IsLink e x y) : G.Inc e x :=
  ⟨y, h⟩

-- Cannot be @[simp] because `x` cannot be inferred by `simp`.
/--
lemma `IsLink.inc_right` / 引理 `IsLink.inc_right`

English:
lemma IsLink.inc_right
  given: (h : G.IsLink e x y)
  statement: G.Inc e y
  proof: ⟨x, h.symm⟩

中文:
引理 IsLink.inc_right
  条件: (h : G.IsLink e x y)
  结论: G.Inc e y
  证明: ⟨x, h.symm⟩

Depends on / 依赖: h.symm
-/
lemma IsLink.inc_right (h : G.IsLink e x y) : G.Inc e y :=
  ⟨x, h.symm⟩

/--
lemma `Inc.eq_or_eq_of_isLink` / 引理 `Inc.eq_or_eq_of_isLink`

English:
lemma Inc.eq_or_eq_of_isLink
  given: (h : G.Inc e x) (h' : G.IsLink e y z)
  statement: x = y ∨ x = z
  proof: h.choose_spec.left_eq_or_eq h'

中文:
引理 Inc.eq_or_eq_of_isLink
  条件: (h : G.Inc e x) (h' : G.IsLink e y z)
  结论: x = y ∨ x = z
  证明: h.choose_spec.left_eq_or_eq h'

Depends on / 依赖: choose_spec, h.choose_spec.left_eq_or_eq, left_eq_or_eq
-/
lemma Inc.eq_or_eq_of_isLink (h : G.Inc e x) (h' : G.IsLink e y z) : x = y ∨ x = z :=
  h.choose_spec.left_eq_or_eq h'

/--
lemma `Inc.eq_of_isLink_of_ne_left` / 引理 `Inc.eq_of_isLink_of_ne_left`

English:
lemma Inc.eq_of_isLink_of_ne_left
  given: (h : G.Inc e x) (h' : G.IsLink e y z) (hxy : x != y)
  statement: x = z
  proof: (h.eq_or_eq_of_isLink h').elim (False.elim ∘ hxy) id

中文:
引理 Inc.eq_of_isLink_of_ne_left
  条件: (h : G.Inc e x) (h' : G.IsLink e y z) (hxy : x != y)
  结论: x = z
  证明: (h.eq_or_eq_of_isLink h').elim (False.elim ∘ hxy) id

Depends on / 依赖: False.elim, eq_or_eq_of_isLink, h.eq_or_eq_of_isLink
-/
lemma Inc.eq_of_isLink_of_ne_left (h : G.Inc e x) (h' : G.IsLink e y z) (hxy : x != y) : x = z :=
  (h.eq_or_eq_of_isLink h').elim (False.elim ∘ hxy) id

/--
lemma `IsLink.isLink_iff_eq` / 引理 `IsLink.isLink_iff_eq`

English:
lemma IsLink.isLink_iff_eq
  given: (h : G.IsLink e x y)
  statement: G.IsLink e x z ↔ z = y
  proof: ⟨fun h' => h'.right_unique h, fun h' => h' ▸ h⟩

中文:
引理 IsLink.isLink_iff_eq
  条件: (h : G.IsLink e x y)
  结论: G.IsLink e x z ↔ z = y
  证明: ⟨fun h' => h'.right_unique h, fun h' => h' ▸ h⟩

Depends on / 依赖: right_unique
-/
lemma IsLink.isLink_iff_eq (h : G.IsLink e x y) : G.IsLink e x z ↔ z = y :=
  ⟨fun h' => h'.right_unique h, fun h' => h' ▸ h⟩

/--
lemma `isLink_iff_inc` / 引理 `isLink_iff_inc`

English:
lemma isLink_iff_inc
  statement: G.IsLink e x y ↔ G.Inc e x ∧ G.Inc e y ∧ forall z, G.Inc e z -> z = x ∨ z = y
  proof: by
  refine ⟨fun h => ⟨h.inc_left, h.inc_right, fun z h' => h'.eq_or_eq_of_isLink h⟩, ?_⟩
  rintro ⟨⟨x', hx'⟩, ⟨y', hy'⟩, h⟩
  obtain rfl | rfl := h _ hx'.inc_right
  · obtain rfl | rfl := hx'.left_eq_or_eq hy'
    · assumption
    exact hy'.symm
  assumption

中文:
引理 isLink_iff_inc
  结论: G.IsLink e x y ↔ G.Inc e x ∧ G.Inc e y ∧ 对任意 z, G.Inc e z -> z = x ∨ z = y
  证明: by
  refine ⟨fun h => ⟨h.inc_left, h.inc_right, fun z h' => h'.eq_or_eq_of_isLink h⟩, ?_⟩
  rintro ⟨⟨x', hx'⟩, ⟨y', hy'⟩, h⟩
  obtain rfl | rfl := h _ hx'.inc_right
  · obtain rfl | rfl := hx'.left_eq_or_eq hy'
    · assumption
    exact hy'.symm
  assumption

Depends on / 依赖: eq_or_eq_of_isLink, h.inc_left, h.inc_right, inc_left, inc_right, left_eq_or_eq
-/
lemma isLink_iff_inc : G.IsLink e x y ↔ G.Inc e x ∧ G.Inc e y ∧ forall z, G.Inc e z -> z = x ∨ z = y := by
  refine ⟨fun h => ⟨h.inc_left, h.inc_right, fun z h' => h'.eq_or_eq_of_isLink h⟩, ?_⟩
  rintro ⟨⟨x', hx'⟩, ⟨y', hy'⟩, h⟩
  obtain rfl | rfl := h _ hx'.inc_right
  · obtain rfl | rfl := hx'.left_eq_or_eq hy'
    · assumption
    exact hy'.symm
  assumption

/--
Definition of `noncomputable` / `noncomputable` 的定义

English:
definition noncomputable
  signature: def Inc.other (h : G.Inc e x)
  body: h.choose

@[simp]

中文:
定义 noncomputable
  签名: def Inc.other (h : G.Inc e x)
  定义体: h.choose

@[simp]
-/
protected noncomputable def Inc.other (h : G.Inc e x) : α := h.choose

@[simp]
/--
lemma `Inc.isLink_other` / 引理 `Inc.isLink_other`

English:
lemma Inc.isLink_other
  given: (h : G.Inc e x)
  statement: G.IsLink e x h.other
  proof: h.choose_spec

@[simp]

中文:
引理 Inc.isLink_other
  条件: (h : G.Inc e x)
  结论: G.IsLink e x h.other
  证明: h.choose_spec

@[simp]

Depends on / 依赖: choose_spec, h.choose_spec
-/
lemma Inc.isLink_other (h : G.Inc e x) : G.IsLink e x h.other :=
  h.choose_spec

@[simp]
/--
lemma `Inc.inc_other` / 引理 `Inc.inc_other`

English:
lemma Inc.inc_other
  given: (h : G.Inc e x)
  statement: G.Inc e h.other
  proof: h.isLink_other.inc_right

中文:
引理 Inc.inc_other
  条件: (h : G.Inc e x)
  结论: G.Inc e h.other
  证明: h.isLink_other.inc_right

Depends on / 依赖: h.isLink_other.inc_right, inc_right, isLink_other
-/
lemma Inc.inc_other (h : G.Inc e x) : G.Inc e h.other :=
  h.isLink_other.inc_right

/--
lemma `Inc.eq_or_eq_or_eq` / 引理 `Inc.eq_or_eq_or_eq`

English:
lemma Inc.eq_or_eq_or_eq
  given: (hx : G.Inc e x) (hy : G.Inc e y) (hz : G.Inc e z)
  proof: by
  by_contra! ⟨hxy, hxz, hyz⟩
  obtain ⟨x', hx'⟩ := hx
  obtain rfl := hy.eq_of_isLink_of_ne_left hx' hxy.symm
  obtain rfl := hz.eq_of_isLink_of_ne_left hx' hxz.symm
  exact hyz rfl

中文:
引理 Inc.eq_or_eq_or_eq
  条件: (hx : G.Inc e x) (hy : G.Inc e y) (hz : G.Inc e z)
  证明: by
  by_contra! ⟨hxy, hxz, hyz⟩
  obtain ⟨x', hx'⟩ := hx
  obtain rfl := hy.eq_of_isLink_of_ne_left hx' hxy.symm
  obtain rfl := hz.eq_of_isLink_of_ne_left hx' hxz.symm
  exact hyz rfl

Depends on / 依赖: eq_of_isLink_of_ne_left, hxy.symm, hxz.symm, hy.eq_of_isLink_of_ne_left, hz.eq_of_isLink_of_ne_left
-/
lemma Inc.eq_or_eq_or_eq (hx : G.Inc e x) (hy : G.Inc e y) (hz : G.Inc e z) :
    x = y ∨ x = z ∨ y = z := by
  by_contra! ⟨hxy, hxz, hyz⟩
  obtain ⟨x', hx'⟩ := hx
  obtain rfl := hy.eq_of_isLink_of_ne_left hx' hxy.symm
  obtain rfl := hz.eq_of_isLink_of_ne_left hx' hxz.symm
  exact hyz rfl

/--
lemma `inc_eq_inc_iff_isLink_eq_isLink` / 引理 `inc_eq_inc_iff_isLink_eq_isLink`

English:
lemma inc_eq_inc_iff_isLink_eq_isLink
  given: {G₁ G₂ : Graph α β}
  proof: by
  constructor <;> rintro h
  · ext x y
    rw [isLink_iff_inc]; rw [isLink_iff_inc]; rw [h]
  · simp [funext_iff, Inc, h]

中文:
引理 inc_eq_inc_iff_isLink_eq_isLink
  条件: {G₁ G₂ : 图 α β}
  证明: by
  constructor <;> rintro h
  · ext x y
    rw [isLink_iff_inc]; rw [isLink_iff_inc]; rw [h]
  · simp [funext_iff, Inc, h]

Depends on / 依赖: funext_iff, isLink_iff_inc
-/
lemma inc_eq_inc_iff_isLink_eq_isLink {G₁ G₂ : Graph α β} :
    G₁.Inc e = G₂.Inc f ↔ G₁.IsLink e = G₂.IsLink f := by
  constructor <;> rintro h
  · ext x y
    rw [isLink_iff_inc]; rw [isLink_iff_inc]; rw [h]
  · simp [funext_iff, Inc, h]

/--
Definition of `IsLoopAt` / `IsLoopAt` 的定义

English:
definition IsLoopAt
  signature: (G : Graph α β) (e : β) (x : α)
  body: G.IsLink e x x

@[simp]

中文:
定义 IsLoopAt
  签名: (G : 图 α β) (e : β) (x : α)
  定义体: G.IsLink e x x

@[simp]

Depends on / 依赖: G.IsLink, IsLink
-/
def IsLoopAt (G : Graph α β) (e : β) (x : α) : Prop := G.IsLink e x x

@[simp]
/--
lemma `isLink_self_iff` / 引理 `isLink_self_iff`

English:
lemma isLink_self_iff
  statement: G.IsLink e x x ↔ G.IsLoopAt e x
  proof: Iff.rfl

中文:
引理 isLink_self_iff
  结论: G.IsLink e x x ↔ G.IsLoopAt e x
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
lemma isLink_self_iff : G.IsLink e x x ↔ G.IsLoopAt e x := Iff.rfl

/--
lemma `IsLoopAt.inc` / 引理 `IsLoopAt.inc`

English:
lemma IsLoopAt.inc
  given: (h : G.IsLoopAt e x)
  statement: G.Inc e x
  proof: IsLink.inc_left h

中文:
引理 IsLoopAt.inc
  条件: (h : G.IsLoopAt e x)
  结论: G.Inc e x
  证明: IsLink.inc_left h

Depends on / 依赖: IsLink, IsLink.inc_left, inc_left
-/
lemma IsLoopAt.inc (h : G.IsLoopAt e x) : G.Inc e x :=
  IsLink.inc_left h

/--
lemma `IsLoopAt.eq_of_inc` / 引理 `IsLoopAt.eq_of_inc`

English:
lemma IsLoopAt.eq_of_inc
  given: (h : G.IsLoopAt e x) (h' : G.Inc e y)
  statement: x = y
  proof: by
  obtain rfl | rfl := h'.eq_or_eq_of_isLink h <;> rfl

中文:
引理 IsLoopAt.eq_of_inc
  条件: (h : G.IsLoopAt e x) (h' : G.Inc e y)
  结论: x = y
  证明: by
  obtain rfl | rfl := h'.eq_or_eq_of_isLink h <;> rfl

Depends on / 依赖: eq_or_eq_of_isLink
-/
lemma IsLoopAt.eq_of_inc (h : G.IsLoopAt e x) (h' : G.Inc e y) : x = y := by
  obtain rfl | rfl := h'.eq_or_eq_of_isLink h <;> rfl

-- Cannot be @[simp] because `x` cannot be inferred by `simp`.
/--
lemma `IsLoopAt.edge_mem` / 引理 `IsLoopAt.edge_mem`

English:
lemma IsLoopAt.edge_mem
  given: (h : G.IsLoopAt e x)
  statement: e in E(G)
  proof: h.inc.edge_mem

中文:
引理 IsLoopAt.edge_mem
  条件: (h : G.IsLoopAt e x)
  结论: e in E(G)
  证明: h.inc.edge_mem

Depends on / 依赖: edge_mem, h.inc.edge_mem
-/
lemma IsLoopAt.edge_mem (h : G.IsLoopAt e x) : e in E(G) :=
  h.inc.edge_mem

-- Cannot be @[simp] because `e` cannot be inferred by `simp`.
/--
lemma `IsLoopAt.vertex_mem` / 引理 `IsLoopAt.vertex_mem`

English:
lemma IsLoopAt.vertex_mem
  given: (h : G.IsLoopAt e x)
  statement: x in V(G)
  proof: h.inc.vertex_mem

中文:
引理 IsLoopAt.vertex_mem
  条件: (h : G.IsLoopAt e x)
  结论: x in V(G)
  证明: h.inc.vertex_mem

Depends on / 依赖: h.inc.vertex_mem, vertex_mem
-/
lemma IsLoopAt.vertex_mem (h : G.IsLoopAt e x) : x in V(G) :=
  h.inc.vertex_mem

/--
Definition of `IsNonloopAt` / `IsNonloopAt` 的定义

English:
definition IsNonloopAt
  signature: (G : Graph α β) (e : β) (x : α)
  body: exists y != x, G.IsLink e x y

中文:
定义 IsNonloopAt
  签名: (G : 图 α β) (e : β) (x : α)
  定义体: exists y != x, G.IsLink e x y

Depends on / 依赖: G.IsLink, IsLink
-/
def IsNonloopAt (G : Graph α β) (e : β) (x : α) : Prop := exists y != x, G.IsLink e x y

/--
lemma `IsNonloopAt.inc` / 引理 `IsNonloopAt.inc`

English:
lemma IsNonloopAt.inc
  given: (h : G.IsNonloopAt e x)
  statement: G.Inc e x
  proof: h.choose_spec.2.inc_left

中文:
引理 IsNonloopAt.inc
  条件: (h : G.IsNonloopAt e x)
  结论: G.Inc e x
  证明: h.choose_spec.2.inc_left

Depends on / 依赖: choose_spec, h.choose_spec, inc_left
-/
lemma IsNonloopAt.inc (h : G.IsNonloopAt e x) : G.Inc e x :=
  h.choose_spec.2.inc_left

-- Cannot be @[simp] because `x` cannot be inferred by `simp`.
/--
lemma `IsNonloopAt.edge_mem` / 引理 `IsNonloopAt.edge_mem`

English:
lemma IsNonloopAt.edge_mem
  given: (h : G.IsNonloopAt e x)
  statement: e in E(G)
  proof: h.inc.edge_mem

中文:
引理 IsNonloopAt.edge_mem
  条件: (h : G.IsNonloopAt e x)
  结论: e in E(G)
  证明: h.inc.edge_mem

Depends on / 依赖: edge_mem, h.inc.edge_mem
-/
lemma IsNonloopAt.edge_mem (h : G.IsNonloopAt e x) : e in E(G) :=
  h.inc.edge_mem

-- Cannot be @[simp] because `e` cannot be inferred by `simp`.
/--
lemma `IsNonloopAt.vertex_mem` / 引理 `IsNonloopAt.vertex_mem`

English:
lemma IsNonloopAt.vertex_mem
  given: (h : G.IsNonloopAt e x)
  statement: x in V(G)
  proof: h.inc.vertex_mem

中文:
引理 IsNonloopAt.vertex_mem
  条件: (h : G.IsNonloopAt e x)
  结论: x in V(G)
  证明: h.inc.vertex_mem

Depends on / 依赖: h.inc.vertex_mem, vertex_mem
-/
lemma IsNonloopAt.vertex_mem (h : G.IsNonloopAt e x) : x in V(G) :=
  h.inc.vertex_mem

/--
lemma `IsLoopAt.not_isNonloopAt` / 引理 `IsLoopAt.not_isNonloopAt`

English:
lemma IsLoopAt.not_isNonloopAt
  given: (h : G.IsLoopAt e x) (y : α)
  statement: ¬ G.IsNonloopAt e y
  proof: by
  rintro ⟨z, hyz, hy⟩
  rw [← h.eq_of_inc hy.inc_left]; rw [← h.eq_of_inc hy.inc_right] at hyz
  exact hyz rfl

中文:
引理 IsLoopAt.not_isNonloopAt
  条件: (h : G.IsLoopAt e x) (y : α)
  结论: ¬ G.IsNonloopAt e y
  证明: by
  rintro ⟨z, hyz, hy⟩
  rw [← h.eq_of_inc hy.inc_left]; rw [← h.eq_of_inc hy.inc_right] at hyz
  exact hyz rfl

Depends on / 依赖: eq_of_inc, h.eq_of_inc, hy.inc_left, hy.inc_right, inc_left, inc_right
-/
lemma IsLoopAt.not_isNonloopAt (h : G.IsLoopAt e x) (y : α) : ¬ G.IsNonloopAt e y := by
  rintro ⟨z, hyz, hy⟩
  rw [← h.eq_of_inc hy.inc_left]; rw [← h.eq_of_inc hy.inc_right] at hyz
  exact hyz rfl

/--
lemma `IsNonloopAt.not_isLoopAt` / 引理 `IsNonloopAt.not_isLoopAt`

English:
lemma IsNonloopAt.not_isLoopAt
  given: (h : G.IsNonloopAt e x) (y : α)
  statement: ¬ G.IsLoopAt e y
  proof: fun h' => h'.not_isNonloopAt x h

中文:
引理 IsNonloopAt.not_isLoopAt
  条件: (h : G.IsNonloopAt e x) (y : α)
  结论: ¬ G.IsLoopAt e y
  证明: fun h' => h'.not_isNonloopAt x h

Depends on / 依赖: not_isNonloopAt
-/
lemma IsNonloopAt.not_isLoopAt (h : G.IsNonloopAt e x) (y : α) : ¬ G.IsLoopAt e y :=
  fun h' => h'.not_isNonloopAt x h

/--
lemma `isNonloopAt_iff_inc_not_isLoopAt` / 引理 `isNonloopAt_iff_inc_not_isLoopAt`

English:
lemma isNonloopAt_iff_inc_not_isLoopAt
  statement: G.IsNonloopAt e x ↔ G.Inc e x ∧ ¬ G.IsLoopAt e x
  proof: ⟨fun h => ⟨h.inc, h.not_isLoopAt _⟩, fun ⟨⟨y, hy⟩, hn⟩ => ⟨y, mt (fun h => h ▸ hy) hn, hy⟩⟩

中文:
引理 isNonloopAt_iff_inc_not_isLoopAt
  结论: G.IsNonloopAt e x ↔ G.Inc e x ∧ ¬ G.IsLoopAt e x
  证明: ⟨fun h => ⟨h.inc, h.not_isLoopAt _⟩, fun ⟨⟨y, hy⟩, hn⟩ => ⟨y, mt (fun h => h ▸ hy) hn, hy⟩⟩

Depends on / 依赖: h.inc, h.not_isLoopAt, not_isLoopAt
-/
lemma isNonloopAt_iff_inc_not_isLoopAt : G.IsNonloopAt e x ↔ G.Inc e x ∧ ¬ G.IsLoopAt e x :=
  ⟨fun h => ⟨h.inc, h.not_isLoopAt _⟩, fun ⟨⟨y, hy⟩, hn⟩ => ⟨y, mt (fun h => h ▸ hy) hn, hy⟩⟩

/--
lemma `isLoopAt_iff_inc_not_isNonloopAt` / 引理 `isLoopAt_iff_inc_not_isNonloopAt`

English:
lemma isLoopAt_iff_inc_not_isNonloopAt
  statement: G.IsLoopAt e x ↔ G.Inc e x ∧ ¬ G.IsNonloopAt e x
  proof: by
  simp +contextual [isNonloopAt_iff_inc_not_isLoopAt, iff_def, IsLoopAt.inc]

中文:
引理 isLoopAt_iff_inc_not_isNonloopAt
  结论: G.IsLoopAt e x ↔ G.Inc e x ∧ ¬ G.IsNonloopAt e x
  证明: by
  simp +contextual [isNonloopAt_iff_inc_not_isLoopAt, iff_def, IsLoopAt.inc]

Depends on / 依赖: IsLoopAt, IsLoopAt.inc, contextual, iff_def, isNonloopAt_iff_inc_not_isLoopAt
-/
lemma isLoopAt_iff_inc_not_isNonloopAt : G.IsLoopAt e x ↔ G.Inc e x ∧ ¬ G.IsNonloopAt e x := by
  simp +contextual [isNonloopAt_iff_inc_not_isLoopAt, iff_def, IsLoopAt.inc]

/--
lemma `Inc.isLoopAt_or_isNonloopAt` / 引理 `Inc.isLoopAt_or_isNonloopAt`

English:
lemma Inc.isLoopAt_or_isNonloopAt
  given: (h : G.Inc e x)
  statement: G.IsLoopAt e x ∨ G.IsNonloopAt e x
  proof: by
  simp [isNonloopAt_iff_inc_not_isLoopAt, h, em]

中文:
引理 Inc.isLoopAt_or_isNonloopAt
  条件: (h : G.Inc e x)
  结论: G.IsLoopAt e x ∨ G.IsNonloopAt e x
  证明: by
  simp [isNonloopAt_iff_inc_not_isLoopAt, h, em]

Depends on / 依赖: isNonloopAt_iff_inc_not_isLoopAt
-/
lemma Inc.isLoopAt_or_isNonloopAt (h : G.Inc e x) : G.IsLoopAt e x ∨ G.IsNonloopAt e x := by
  simp [isNonloopAt_iff_inc_not_isLoopAt, h, em]

/-! ### Adjacency -/

/--
Definition of `Adj` / `Adj` 的定义

English:
definition Adj
  signature: (G : Graph α β) (x y : α)
  body: exists e, G.IsLink e x y

@[symm]

中文:
定义 伴随
  签名: (G : 图 α β) (x y : α)
  定义体: exists e, G.IsLink e x y

@[symm]

Depends on / 依赖: G.IsLink, IsLink
-/
def Adj (G : Graph α β) (x y : α) : Prop := exists e, G.IsLink e x y

@[symm]
/--
lemma `Adj.symm` / 引理 `Adj.symm`

English:
lemma Adj.symm
  given: (h : G.Adj x y)
  statement: G.Adj y x
  proof: ⟨_, h.choose_spec.symm⟩

中文:
引理 伴随.symm
  条件: (h : G.伴随 x y)
  结论: G.伴随 y x
  证明: ⟨_, h.choose_spec.symm⟩
-/
protected lemma Adj.symm (h : G.Adj x y) : G.Adj y x :=
  ⟨_, h.choose_spec.symm⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Std.Symm G.Adj
  body: Adj.symm

中文:
实例 :
  签名: Std.Symm G.伴随
  定义体: Adj.symm

Depends on / 依赖: Adj.symm
-/
instance : Std.Symm G.Adj where
  symm _ _ := Adj.symm

/--
lemma `adj_comm` / 引理 `adj_comm`

English:
lemma adj_comm
  given: (x y)
  statement: G.Adj x y ↔ G.Adj y x
  proof: ⟨.symm, .symm⟩

中文:
引理 adj_comm
  条件: (x y)
  结论: G.伴随 x y ↔ G.伴随 y x
  证明: ⟨.symm, .symm⟩
-/
lemma adj_comm (x y) : G.Adj x y ↔ G.Adj y x :=
  ⟨.symm, .symm⟩

-- Cannot be @[simp] because `y` cannot be inferred by `simp`.
/--
lemma `Adj.left_mem` / 引理 `Adj.left_mem`

English:
lemma Adj.left_mem
  given: (h : G.Adj x y)
  statement: x in V(G)
  proof: h.choose_spec.left_mem

中文:
引理 伴随.left_mem
  条件: (h : G.伴随 x y)
  结论: x in V(G)
  证明: h.choose_spec.left_mem

Depends on / 依赖: choose_spec, h.choose_spec.left_mem, left_mem
-/
lemma Adj.left_mem (h : G.Adj x y) : x in V(G) :=
  h.choose_spec.left_mem

-- Cannot be @[simp] because `x` cannot be inferred by `simp`.
/--
lemma `Adj.right_mem` / 引理 `Adj.right_mem`

English:
lemma Adj.right_mem
  given: (h : G.Adj x y)
  statement: y in V(G)
  proof: h.symm.left_mem

中文:
引理 伴随.right_mem
  条件: (h : G.伴随 x y)
  结论: y in V(G)
  证明: h.symm.left_mem

Depends on / 依赖: h.symm.left_mem, left_mem
-/
lemma Adj.right_mem (h : G.Adj x y) : y in V(G) :=
  h.symm.left_mem

/--
lemma `IsLink.adj` / 引理 `IsLink.adj`

English:
lemma IsLink.adj
  given: (h : G.IsLink e x y)
  statement: G.Adj x y
  proof: ⟨e, h⟩

中文:
引理 IsLink.adj
  条件: (h : G.IsLink e x y)
  结论: G.伴随 x y
  证明: ⟨e, h⟩
-/
lemma IsLink.adj (h : G.IsLink e x y) : G.Adj x y :=
  ⟨e, h⟩

/-! ### Extensionality -/

/-- `edgeSet` can be determined using `IsLink`, so the graph constructed from `G.vertexSet` and
`G.IsLink` using any value for `edgeSet` is equal to `G` itself. -/
@[simp]
/--
lemma `mk_eq_self` / 引理 `mk_eq_self`

English:
lemma mk_eq_self
  given: (G : Graph α β) {E : Set β} (hE : forall e, e in E ↔ exists x y, G.IsLink e x y)
  proof: by
  obtain rfl : E = E(G) := by simp [Set.ext_iff, hE, G.edge_mem_iff_exists_isLink]
  cases G with | _ _ _ _ _ _ h _ => simp

中文:
引理 mk_eq_self
  条件: (G : 图 α β) {E : 集合 β} (hE : 对任意 e, e in E ↔ 存在 x y, G.IsLink e x y)
  证明: by
  obtain rfl : E = E(G) := by simp [Set.ext_iff, hE, G.edge_mem_iff_exists_isLink]
  cases G with | _ _ _ _ _ _ h _ => simp

Depends on / 依赖: G.edge_mem_iff_exists_isLink, Set.ext_iff, edge_mem_iff_exists_isLink, ext_iff
-/
lemma mk_eq_self (G : Graph α β) {E : Set β} (hE : forall e, e in E ↔ exists x y, G.IsLink e x y) :
    Graph.mk V(G) G.IsLink E
    (by simpa [show E = E(G) by simp [Set.ext_iff, hE, G.edge_mem_iff_exists_isLink]]
      using G.isLink_symm)
    (fun _ _ _ _ _ h h' => h.left_eq_or_eq h') hE
    (fun _ _ _ => IsLink.left_mem) = G := by
  obtain rfl : E = E(G) := by simp [Set.ext_iff, hE, G.edge_mem_iff_exists_isLink]
  cases G with | _ _ _ _ _ _ h _ => simp

/-- Two graphs with the same vertex set and binary incidences are equal.
(We use this as the default extensionality lemma rather than adding `@[ext]`
to the definition of `Graph`, so it doesn't require equality of the edge sets.) -/
@[ext]
/--
lemma `ext` / 引理 `ext`

English:
lemma ext
  statement: {G₁ G₂ : Graph α β} (hV : V(G₁) = V(G₂))
  proof: by
  rw [← G₁.mk_eq_self G₁.edge_mem_iff_exists_isLink]; rw [← G₂.mk_eq_self G₂.edge_mem_iff_exists_isLink]
  convert! rfl using 2
  · exact hV.symm
  · simp [funext_iff, h]
  simp [edgeSet_eq_setOfPred_exists_isLink, h]

中文:
引理 ext
  结论: {G₁ G₂ : 图 α β} (hV : V(G₁) = V(G₂))
  证明: by
  rw [← G₁.mk_eq_self G₁.edge_mem_iff_exists_isLink]; rw [← G₂.mk_eq_self G₂.edge_mem_iff_exists_isLink]
  convert! rfl using 2
  · exact hV.symm
  · simp [funext_iff, h]
  simp [edgeSet_eq_setOfPred_exists_isLink, h]
-/
protected lemma ext {G₁ G₂ : Graph α β} (hV : V(G₁) = V(G₂))
    (h : forall e x y, G₁.IsLink e x y ↔ G₂.IsLink e x y) : G₁ = G₂ := by
  rw [← G₁.mk_eq_self G₁.edge_mem_iff_exists_isLink]; rw [← G₂.mk_eq_self G₂.edge_mem_iff_exists_isLink]
  convert! rfl using 2
  · exact hV.symm
  · simp [funext_iff, h]
  simp [edgeSet_eq_setOfPred_exists_isLink, h]

/--
lemma `ext_inc` / 引理 `ext_inc`

English:
lemma ext_inc
  given: {G₁ G₂ : Graph α β} (hV : V(G₁) = V(G₂)) (h : forall e x, G₁.Inc e x ↔ G₂.Inc e x)
  proof: Graph.ext hV fun _ _ _ => by simp_rw [isLink_iff_inc, h]

中文:
引理 ext_inc
  条件: {G₁ G₂ : 图 α β} (hV : V(G₁) = V(G₂)) (h : 对任意 e x, G₁.Inc e x ↔ G₂.Inc e x)
  证明: Graph.ext hV fun _ _ _ => by simp_rw [isLink_iff_inc, h]

Depends on / 依赖: Graph.ext, isLink_iff_inc, simp_rw
-/
lemma ext_inc {G₁ G₂ : Graph α β} (hV : V(G₁) = V(G₂)) (h : forall e x, G₁.Inc e x ↔ G₂.Inc e x) :
    G₁ = G₂ :=
  Graph.ext hV fun _ _ _ => by simp_rw [isLink_iff_inc, h]

/-- `Graph.copy` produces a graph equal to `G` but with provided definitional choices
for `vertexSet`, `edgeSet`, and `IsLink`. This is mainly useful for improving
definitional equalities while keeping the same underlying graph. -/
@[simps -isSimp]
/--
Definition of `copy` / `copy` 的定义

English:
definition copy
  signature: (G : Graph α β) {vertexSet : Set α} {edgeSet : Set β} {IsLink : β -> α -> α -> Prop}
  body: vertexSet
  edgeSet := edgeSet
  IsLink := IsLink
  isLink_symm e he := by
    simp_rw [symm_def, ← hIsLink]
    exact (G.isLink_symm <| hedgeSet ▸ he).symm
  eq_or_eq_of_isLink_of_isLink := by
    simp_rw [← hIsLink]
    exact G.eq_or_eq_of_isLink_of_isLink
  edge_mem_iff_exists_isLink := by
    simp_rw [← hIsLink, ← hedgeSet]
    exact G.edge_mem_iff_exists_isLink
  left_mem_of_isLink := by
    simp_rw [← hIsLink, ← hvertexSet]
    exact G.left_mem_of_isLink

@[simp]

中文:
定义 copy
  签名: (G : 图 α β) {vertexSet : 集合 α} {edgeSet : 集合 β} {IsLink : β -> α -> α -> 命题}
  定义体: vertexSet
  edgeSet := edgeSet
  IsLink := IsLink
  isLink_symm e he := by
    simp_rw [symm_def, ← hIsLink]
    exact (G.isLink_symm <| hedgeSet ▸ he).symm
  eq_or_eq_of_isLink_of_isLink := by
    simp_rw [← hIsLink]
    exact G.eq_or_eq_of_isLink_of_isLink
  edge_mem_iff_exists_isLink := by
    simp_rw [← hIsLink, ← hedgeSet]
    exact G.edge_mem_iff_exists_isLink
  left_mem_of_isLink := by
    simp_rw [← hIsLink, ← hvertexSet]
    exact G.left_mem_of_isLink

@[simp]

Depends on / 依赖: vertexSet
-/
def copy (G : Graph α β) {vertexSet : Set α} {edgeSet : Set β} {IsLink : β -> α -> α -> Prop}
    (hvertexSet : V(G) = vertexSet) (hedgeSet : E(G) = edgeSet)
    (hIsLink : forall e x y, G.IsLink e x y ↔ IsLink e x y) : Graph α β where
  vertexSet := vertexSet
  edgeSet := edgeSet
  IsLink := IsLink
  isLink_symm e he := by
    simp_rw [symm_def, ← hIsLink]
    exact (G.isLink_symm <| hedgeSet ▸ he).symm
  eq_or_eq_of_isLink_of_isLink := by
    simp_rw [← hIsLink]
    exact G.eq_or_eq_of_isLink_of_isLink
  edge_mem_iff_exists_isLink := by
    simp_rw [← hIsLink, ← hedgeSet]
    exact G.edge_mem_iff_exists_isLink
  left_mem_of_isLink := by
    simp_rw [← hIsLink, ← hvertexSet]
    exact G.left_mem_of_isLink

@[simp]
/--
lemma `copy_eq` / 引理 `copy_eq`

English:
lemma copy_eq
  statement: (G : Graph α β) {V : Set α} {E : Set β} {IsLink : β -> α -> α -> Prop}
  proof: by
  ext <;> simp_all [copy]

中文:
引理 copy_eq
  结论: (G : 图 α β) {V : 集合 α} {E : 集合 β} {IsLink : β -> α -> α -> 命题}
  证明: by
  ext <;> simp_all [copy]
-/
lemma copy_eq (G : Graph α β) {V : Set α} {E : Set β} {IsLink : β -> α -> α -> Prop}
    (hV : V(G) = V) (hE : E(G) = E) (h_isLink : forall e x y, G.IsLink e x y ↔ IsLink e x y) :
    G.copy hV hE h_isLink = G := by
  ext <;> simp_all [copy]

/-! ### Sets of edges or loops incident to a vertex -/

/--
Definition of `incidenceSet` / `incidenceSet` 的定义

English:
definition incidenceSet
  signature: (x : α)
  body: {e | G.Inc e x}

@[simp]

中文:
定义 incidenceSet
  签名: (x : α)
  定义体: {e | G.Inc e x}

@[simp]

Depends on / 依赖: G.Inc
-/
def incidenceSet (x : α) : Set β := {e | G.Inc e x}

@[simp]
/--
theorem `mem_incidenceSet` / 定理 `mem_incidenceSet`

English:
theorem mem_incidenceSet
  given: (x : α) (e : β)
  statement: e in G.incidenceSet x ↔ G.Inc e x
  proof: Iff.rfl

中文:
定理 mem_incidenceSet
  条件: (x : α) (e : β)
  结论: e in G.incidenceSet x ↔ G.Inc e x
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_incidenceSet (x : α) (e : β) : e in G.incidenceSet x ↔ G.Inc e x :=
  Iff.rfl

/--
theorem `incidenceSet_subset_edgeSet` / 定理 `incidenceSet_subset_edgeSet`

English:
theorem incidenceSet_subset_edgeSet
  given: (x : α)
  statement: G.incidenceSet x subseteq E(G)
  proof: fun _ ⟨_, hy⟩ => hy.edge_mem

中文:
定理 incidenceSet_subset_edgeSet
  条件: (x : α)
  结论: G.incidenceSet x subseteq E(G)
  证明: fun _ ⟨_, hy⟩ => hy.edge_mem

Depends on / 依赖: edge_mem, hy.edge_mem
-/
theorem incidenceSet_subset_edgeSet (x : α) : G.incidenceSet x subseteq E(G) :=
  fun _ ⟨_, hy⟩ => hy.edge_mem

/--
Definition of `loopSet` / `loopSet` 的定义

English:
definition loopSet
  signature: (x : α)
  body: {e | G.IsLoopAt e x}

@[simp]

中文:
定义 loopSet
  签名: (x : α)
  定义体: {e | G.IsLoopAt e x}

@[simp]

Depends on / 依赖: G.IsLoopAt, IsLoopAt
-/
def loopSet (x : α) : Set β := {e | G.IsLoopAt e x}

@[simp]
/--
theorem `mem_loopSet` / 定理 `mem_loopSet`

English:
theorem mem_loopSet
  given: (x : α) (e : β)
  statement: e in G.loopSet x ↔ G.IsLoopAt e x
  proof: Iff.rfl

中文:
定理 mem_loopSet
  条件: (x : α) (e : β)
  结论: e in G.loopSet x ↔ G.IsLoopAt e x
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_loopSet (x : α) (e : β) : e in G.loopSet x ↔ G.IsLoopAt e x :=
  Iff.rfl

/--
theorem `loopSet_subset_incidenceSet` / 定理 `loopSet_subset_incidenceSet`

English:
theorem loopSet_subset_incidenceSet
  given: (x : α)
  statement: G.loopSet x subseteq G.incidenceSet x
  proof: fun _ he => ⟨x, he⟩

中文:
定理 loopSet_subset_incidenceSet
  条件: (x : α)
  结论: G.loopSet x subseteq G.incidenceSet x
  证明: fun _ he => ⟨x, he⟩
-/
theorem loopSet_subset_incidenceSet (x : α) : G.loopSet x subseteq G.incidenceSet x := fun _ he => ⟨x, he⟩

/-!
### Compatibility of Graphs

We define two graphs to be `Compatible` if for each edge belonging to their shared edge set,
the incidence relation (i.e., which pairs of vertices it links) is the same in both graphs.
-/

/--
Definition of `Compatible` / `Compatible` 的定义

English:
definition Compatible
  signature: (G H : Graph α β)
  body: forall ⦃e⦄, e in E(G) -> e in E(H) -> forall x y, G.IsLink e x y ↔ H.IsLink e x y

中文:
定义 余mpatible
  签名: (G H : 图 α β)
  定义体: forall ⦃e⦄, e in E(G) -> e in E(H) -> forall x y, G.IsLink e x y ↔ H.IsLink e x y

Depends on / 依赖: G.IsLink, H.IsLink, IsLink
-/
def Compatible (G H : Graph α β) : Prop :=
  forall ⦃e⦄, e in E(G) -> e in E(H) -> forall x y, G.IsLink e x y ↔ H.IsLink e x y

/--
lemma `Compatible.isLink_congr` / 引理 `Compatible.isLink_congr`

English:
lemma Compatible.isLink_congr
  given: (heG : e in E(G)) (heH : e in E(H)) (h : G.Compatible H) {x y : α}
  proof: h heG heH x y

中文:
引理 余mpatible.isLink_congr
  条件: (heG : e in E(G)) (heH : e in E(H)) (h : G.余mpatible H) {x y : α}
  证明: h heG heH x y
-/
lemma Compatible.isLink_congr (heG : e in E(G)) (heH : e in E(H)) (h : G.Compatible H) {x y : α} :
    G.IsLink e x y ↔ H.IsLink e x y :=
  h heG heH x y

/--
lemma `Compatible.refl` / 引理 `Compatible.refl`

English:
lemma Compatible.refl
  given: (G : Graph α β)
  statement: G.Compatible G
  proof: fun _ _ _ _ _ => .rfl

@[simp]

中文:
引理 余mpatible.refl
  条件: (G : 图 α β)
  结论: G.余mpatible G
  证明: fun _ _ _ _ _ => .rfl

@[simp]
-/
lemma Compatible.refl (G : Graph α β) : G.Compatible G :=
  fun _ _ _ _ _ => .rfl

@[simp]
/--
lemma `Compatible.rfl` / 引理 `Compatible.rfl`

English:
lemma Compatible.rfl
  given: {G : Graph α β}
  statement: G.Compatible G
  proof: .refl _

中文:
引理 余mpatible.rfl
  条件: {G : 图 α β}
  结论: G.余mpatible G
  证明: .refl _
-/
lemma Compatible.rfl {G : Graph α β} : G.Compatible G := .refl _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Std.Refl (Compatible : Graph α β -> Graph α β -> Prop)
  body: .rfl

@[symm]

中文:
实例 :
  签名: Std.Refl (余mpatible : 图 α β -> 图 α β -> 命题)
  定义体: .rfl

@[symm]
-/
instance : Std.Refl (Compatible : Graph α β -> Graph α β -> Prop) where
  refl _ := .rfl

@[symm]
/--
lemma `Compatible.symm` / 引理 `Compatible.symm`

English:
lemma Compatible.symm
  given: (h : G.Compatible H)
  statement: H.Compatible G
  proof: fun _ heH heG x y => (h heG heH x y).symm

中文:
引理 余mpatible.symm
  条件: (h : G.余mpatible H)
  结论: H.余mpatible G
  证明: fun _ heH heG x y => (h heG heH x y).symm
-/
lemma Compatible.symm (h : G.Compatible H) : H.Compatible G :=
  fun _ heH heG x y => (h heG heH x y).symm

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Std.Symm (Compatible : Graph α β -> Graph α β -> Prop)
  body: Compatible.symm

中文:
实例 :
  签名: Std.Symm (余mpatible : 图 α β -> 图 α β -> 命题)
  定义体: Compatible.symm

Depends on / 依赖: Compatible, Compatible.symm
-/
instance : Std.Symm (Compatible : Graph α β -> Graph α β -> Prop) where
  symm _ _ := Compatible.symm

/--
lemma `IsLink.of_compatible` / 引理 `IsLink.of_compatible`

English:
lemma IsLink.of_compatible
  given: (hGH : G.Compatible H) (heH : e in E(H)) (h : G.IsLink e x y)
  proof: (hGH h.edge_mem heH x y).mp h

中文:
引理 IsLink.of_compatible
  条件: (hGH : G.余mpatible H) (heH : e in E(H)) (h : G.IsLink e x y)
  证明: (hGH h.edge_mem heH x y).mp h

Depends on / 依赖: edge_mem, h.edge_mem
-/
lemma IsLink.of_compatible (hGH : G.Compatible H) (heH : e in E(H)) (h : G.IsLink e x y) :
    H.IsLink e x y :=
  (hGH h.edge_mem heH x y).mp h

/--
lemma `Compatible.of_disjoint_edgeSet` / 引理 `Compatible.of_disjoint_edgeSet`

English:
lemma Compatible.of_disjoint_edgeSet
  given: (h : Disjoint E(G) E(H))
  statement: Compatible G H
  proof: .elim fun _ heG heH _ _ => h.notMem_of_mem_left heG heH

中文:
引理 余mpatible.of_disjoint_edgeSet
  条件: (h : Disjoint E(G) E(H))
  结论: 余mpatible G H
  证明: .elim fun _ heG heH _ _ => h.notMem_of_mem_left heG heH

Depends on / 依赖: h.notMem_of_mem_left, notMem_of_mem_left
-/
lemma Compatible.of_disjoint_edgeSet (h : Disjoint E(G) E(H)) : Compatible G H :=
.elim fun _ heG heH _ _ => h.notMem_of_mem_left heG heH

/--
lemma `Inc.of_compatible` / 引理 `Inc.of_compatible`

English:
lemma Inc.of_compatible
  given: (hGH : G.Compatible H) (heH : e in E(H)) (h : G.Inc e x)
  statement: H.Inc e x
  proof: by
  obtain ⟨y, hy⟩ := h
  exact ⟨y, hy.of_compatible hGH heH⟩

中文:
引理 Inc.of_compatible
  条件: (hGH : G.余mpatible H) (heH : e in E(H)) (h : G.Inc e x)
  结论: H.Inc e x
  证明: by
  obtain ⟨y, hy⟩ := h
  exact ⟨y, hy.of_compatible hGH heH⟩

Depends on / 依赖: hy.of_compatible, of_compatible
-/
lemma Inc.of_compatible (hGH : G.Compatible H) (heH : e in E(H)) (h : G.Inc e x) : H.Inc e x := by
  obtain ⟨y, hy⟩ := h
  exact ⟨y, hy.of_compatible hGH heH⟩

/--
lemma `IsLoopAt.of_compatible` / 引理 `IsLoopAt.of_compatible`

English:
lemma IsLoopAt.of_compatible
  given: (hGH : G.Compatible H) (heH : e in E(H)) (h : G.IsLoopAt e x)
  proof: IsLink.of_compatible hGH heH h

中文:
引理 IsLoopAt.of_compatible
  条件: (hGH : G.余mpatible H) (heH : e in E(H)) (h : G.IsLoopAt e x)
  证明: IsLink.of_compatible hGH heH h

Depends on / 依赖: IsLink, IsLink.of_compatible, of_compatible
-/
lemma IsLoopAt.of_compatible (hGH : G.Compatible H) (heH : e in E(H)) (h : G.IsLoopAt e x) :
    H.IsLoopAt e x :=
  IsLink.of_compatible hGH heH h

/--
lemma `IsNonloopAt.of_compatible` / 引理 `IsNonloopAt.of_compatible`

English:
lemma IsNonloopAt.of_compatible
  given: (hGH : G.Compatible H) (heH : e in E(H)) (h : G.IsNonloopAt e x)
  proof: by
  obtain ⟨y, hne, hy⟩ := h
  exact ⟨y, hne, hy.of_compatible hGH heH⟩

中文:
引理 IsNonloopAt.of_compatible
  条件: (hGH : G.余mpatible H) (heH : e in E(H)) (h : G.IsNonloopAt e x)
  证明: by
  obtain ⟨y, hne, hy⟩ := h
  exact ⟨y, hne, hy.of_compatible hGH heH⟩

Depends on / 依赖: hy.of_compatible, of_compatible
-/
lemma IsNonloopAt.of_compatible (hGH : G.Compatible H) (heH : e in E(H)) (h : G.IsNonloopAt e x) :
    H.IsNonloopAt e x := by
  obtain ⟨y, hne, hy⟩ := h
  exact ⟨y, hne, hy.of_compatible hGH heH⟩

/-! ### Graphs with no edges -/

/-- The graph with vertex set `vertexSet` and no edges -/
@[simps (attr := grind =) vertexSet edgeSet]
/--
Definition of `noEdge` / `noEdge` 的定义

English:
definition noEdge
  signature: (vertexSet : Set α) (β : Type*)
  body: vertexSet
  edgeSet := ∅
  IsLink _ _ _ := False
  isLink_symm := by simp
  eq_or_eq_of_isLink_of_isLink := by simp
  edge_mem_iff_exists_isLink := by simp

中文:
定义 noEdge
  签名: (vertexSet : 集合 α) (β : 类型)
  定义体: vertexSet
  edgeSet := ∅
  IsLink _ _ _ := False
  isLink_symm := by simp
  eq_or_eq_of_isLink_of_isLink := by simp
  edge_mem_iff_exists_isLink := by simp

Depends on / 依赖: vertexSet
-/
def noEdge (vertexSet : Set α) (β : Type*) : Graph α β where
  vertexSet := vertexSet
  edgeSet := ∅
  IsLink _ _ _ := False
  isLink_symm := by simp
  eq_or_eq_of_isLink_of_isLink := by simp
  edge_mem_iff_exists_isLink := by simp

/--
theorem `noEdge_isLink` / 定理 `noEdge_isLink`

English:
theorem noEdge_isLink
  given: (vertexSet : Set α) (β : Type*) (e : β) (x y : α)
  proof: Iff.rfl

中文:
定理 noEdge_isLink
  条件: (vertexSet : 集合 α) (β : 类型) (e : β) (x y : α)
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem noEdge_isLink (vertexSet : Set α) (β : Type*) (e : β) (x y : α) :
    (noEdge vertexSet β).IsLink e x y ↔ False := Iff.rfl

variable {vertexSet : Set α} {edgeSet : Set β}

/--
lemma `edgeSet_eq_empty` / 引理 `edgeSet_eq_empty`

English:
lemma edgeSet_eq_empty
  statement: E(G) = ∅ ↔ G = noEdge V(G) β
  proof: by
  refine ⟨fun h => Graph.ext rfl ?_, fun h => by rw [h, edgeSet_noEdge]⟩
  simp only [noEdge_isLink, iff_false]
  refine fun e x y he => ?_
  have := h ▸ he.edge_mem
  simp at this

中文:
引理 edgeSet_eq_empty
  结论: E(G) = ∅ ↔ G = noEdge V(G) β
  证明: by
  refine ⟨fun h => Graph.ext rfl ?_, fun h => by rw [h, edgeSet_noEdge]⟩
  simp only [noEdge_isLink, iff_false]
  refine fun e x y he => ?_
  have := h ▸ he.edge_mem
  simp at this

Depends on / 依赖: Graph.ext, edgeSet_noEdge, edge_mem, he.edge_mem, iff_false, noEdge_isLink
-/
lemma edgeSet_eq_empty : E(G) = ∅ ↔ G = noEdge V(G) β := by
  refine ⟨fun h => Graph.ext rfl ?_, fun h => by rw [h, edgeSet_noEdge]⟩
  simp only [noEdge_isLink, iff_false]
  refine fun e x y he => ?_
  have := h ▸ he.edge_mem
  simp at this

/-! ### Graphs with two vertices -/

/-- A graph with exactly two vertices and no loops. -/
@[simps (attr := grind =)]
/--
Definition of `banana` / `banana` 的定义

English:
definition banana
  signature: (u v : α) (edgeSet : Set β)
  body: {u, v}
  edgeSet := edgeSet
  IsLink e x y := e in edgeSet ∧ ((x = u ∧ y = v) ∨ (x = v ∧ y = u))
  isLink_symm := by aesop (add simp symm_def)
  eq_or_eq_of_isLink_of_isLink := by aesop
  edge_mem_iff_exists_isLink := by aesop

@[simp]

中文:
定义 banana
  签名: (u v : α) (edgeSet : 集合 β)
  定义体: {u, v}
  edgeSet := edgeSet
  IsLink e x y := e in edgeSet ∧ ((x = u ∧ y = v) ∨ (x = v ∧ y = u))
  isLink_symm := by aesop (add simp symm_def)
  eq_or_eq_of_isLink_of_isLink := by aesop
  edge_mem_iff_exists_isLink := by aesop

@[simp]
-/
def banana (u v : α) (edgeSet : Set β) : Graph α β where
  vertexSet := {u, v}
  edgeSet := edgeSet
  IsLink e x y := e in edgeSet ∧ ((x = u ∧ y = v) ∨ (x = v ∧ y = u))
  isLink_symm := by aesop (add simp symm_def)
  eq_or_eq_of_isLink_of_isLink := by aesop
  edge_mem_iff_exists_isLink := by aesop

@[simp]
/--
lemma `banana_inc` / 引理 `banana_inc`

English:
lemma banana_inc
  statement: (banana u v edgeSet).Inc e x ↔ e in edgeSet ∧ (x = u ∨ x = v)
  proof: by
  simp only [Inc, banana_isLink, exists_and_left, and_congr_right_iff]
  aesop

中文:
引理 banana_inc
  结论: (banana u v edgeSet).Inc e x ↔ e in edgeSet ∧ (x = u ∨ x = v)
  证明: by
  simp only [Inc, banana_isLink, exists_and_left, and_congr_right_iff]
  aesop

Depends on / 依赖: and_congr_right_iff, banana_isLink, exists_and_left
-/
lemma banana_inc : (banana u v edgeSet).Inc e x ↔ e in edgeSet ∧ (x = u ∨ x = v) := by
  simp only [Inc, banana_isLink, exists_and_left, and_congr_right_iff]
  aesop

/--
lemma `banana_comm` / 引理 `banana_comm`

English:
lemma banana_comm
  given: (u v : α) (edgeSet : Set β)
  statement: banana u v edgeSet = banana v u edgeSet
  proof: Graph.ext_inc (pair_comm ..) by simp [or_comm]

@[simp]

中文:
引理 banana_comm
  条件: (u v : α) (edgeSet : 集合 β)
  结论: banana u v edgeSet = banana v u edgeSet
  证明: Graph.ext_inc (pair_comm ..) by simp [or_comm]

@[simp]

Depends on / 依赖: Graph.ext_inc, ext_inc, or_comm, pair_comm
-/
lemma banana_comm (u v : α) (edgeSet : Set β) : banana u v edgeSet = banana v u edgeSet :=
Graph.ext_inc (pair_comm ..) by simp [or_comm]

@[simp]
/--
lemma `banana_isNonloopAt` / 引理 `banana_isNonloopAt`

English:
lemma banana_isNonloopAt
  proof: by
  simp_rw [isNonloopAt_iff_inc_not_isLoopAt, ← isLink_self_iff, banana_isLink, banana_inc]
  aesop

@[simp]

中文:
引理 banana_isNonloopAt
  证明: by
  simp_rw [isNonloopAt_iff_inc_not_isLoopAt, ← isLink_self_iff, banana_isLink, banana_inc]
  aesop

@[simp]

Depends on / 依赖: banana_inc, banana_isLink, isLink_self_iff, isNonloopAt_iff_inc_not_isLoopAt, simp_rw
-/
lemma banana_isNonloopAt :
    (banana u v edgeSet).IsNonloopAt e x ↔ e in edgeSet ∧ (x = u ∨ x = v) ∧ u != v := by
  simp_rw [isNonloopAt_iff_inc_not_isLoopAt, ← isLink_self_iff, banana_isLink, banana_inc]
  aesop

@[simp]
/--
lemma `banana_isLoopAt` / 引理 `banana_isLoopAt`

English:
lemma banana_isLoopAt
  statement: (banana u v edgeSet).IsLoopAt e x ↔ e in edgeSet ∧ x = u ∧ u = v
  proof: by
  simp only [← isLink_self_iff, banana_isLink, and_congr_right_iff]
  aesop

@[simp]

中文:
引理 banana_isLoopAt
  结论: (banana u v edgeSet).IsLoopAt e x ↔ e in edgeSet ∧ x = u ∧ u = v
  证明: by
  simp only [← isLink_self_iff, banana_isLink, and_congr_right_iff]
  aesop

@[simp]

Depends on / 依赖: and_congr_right_iff, banana_isLink, isLink_self_iff
-/
lemma banana_isLoopAt : (banana u v edgeSet).IsLoopAt e x ↔ e in edgeSet ∧ x = u ∧ u = v := by
  simp only [← isLink_self_iff, banana_isLink, and_congr_right_iff]
  aesop

@[simp]
/--
lemma `banana_adj` / 引理 `banana_adj`

English:
lemma banana_adj
  statement: (banana u v edgeSet).Adj x y ↔ edgeSet.Nonempty ∧ s(x, y) = s(u, v)
  proof: by
  simp only [Adj, banana_isLink, exists_and_right, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq,
    Prod.swap_prod_mk, and_congr_left_iff]
  exact fun _ => Iff.rfl

@[simp]

中文:
引理 banana_adj
  结论: (banana u v edgeSet).伴随 x y ↔ edgeSet.非空 ∧ s(x, y) = s(u, v)
  证明: by
  simp only [Adj, banana_isLink, exists_and_right, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq,
    Prod.swap_prod_mk, and_congr_left_iff]
  exact fun _ => Iff.rfl

@[simp]

Depends on / 依赖: Iff.rfl, Prod.mk.injEq, Prod.swap_prod_mk, Sym2.eq, Sym2.rel_iff, and_congr_left_iff, banana_isLink, exists_and_right, randFin, rel_iff, swap_prod_mk
-/
lemma banana_adj : (banana u v edgeSet).Adj x y ↔ edgeSet.Nonempty ∧ s(x, y) = s(u, v) := by
  simp only [Adj, banana_isLink, exists_and_right, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq,
    Prod.swap_prod_mk, and_congr_left_iff]
  exact fun _ => Iff.rfl

@[simp]
/--
lemma `banana_empty` / 引理 `banana_empty`

English:
lemma banana_empty
  statement: banana u v ∅ = Graph.noEdge {u, v} β
  proof: by
  ext <;> simp

中文:
引理 banana_empty
  结论: banana u v ∅ = 图.noEdge {u, v} β
  证明: by
  ext <;> simp
-/
lemma banana_empty : banana u v ∅ = Graph.noEdge {u, v} β := by
  ext <;> simp

/-! ### Graphs with one vertex -/

/--
Definition of `bouquet` / `bouquet` 的定义

English:
abbreviation bouquet
  signature: (v : α) (edgeSet : Set β)
  body: banana v v edgeSet

中文:
缩写 bouquet
  签名: (v : α) (edgeSet : 集合 β)
  定义体: banana v v edgeSet

Depends on / 依赖: banana, edgeSet
-/
abbrev bouquet (v : α) (edgeSet : Set β) : Graph α β :=
  banana v v edgeSet

/--
lemma `vertexSet_bouquet` / 引理 `vertexSet_bouquet`

English:
lemma vertexSet_bouquet
  given: (v : α) (edgeSet : Set β)
  statement: V(bouquet v edgeSet) = {v}
  proof: by simp

@[deprecated (since := "2026-04-09")] alias bouquet_vertexSet := vertexSet_bouquet

中文:
引理 vertexSet_bouquet
  条件: (v : α) (edgeSet : 集合 β)
  结论: V(bouquet v edgeSet) = {v}
  证明: by simp

@[deprecated (since := "2026-04-09")] alias bouquet_vertexSet := vertexSet_bouquet

Depends on / 依赖: ULiftable, ULiftable.up, random
-/
lemma vertexSet_bouquet (v : α) (edgeSet : Set β) : V(bouquet v edgeSet) = {v} := by simp

@[deprecated (since := "2026-04-09")] alias bouquet_vertexSet := vertexSet_bouquet

/--
lemma `bouquet_isLink` / 引理 `bouquet_isLink`

English:
lemma bouquet_isLink
  given: (v : α) (edgeSet : Set β)
  proof: by simp

中文:
引理 bouquet_isLink
  条件: (v : α) (edgeSet : 集合 β)
  证明: by simp
-/
lemma bouquet_isLink (v : α) (edgeSet : Set β) :
    (bouquet v edgeSet).IsLink e x y ↔ e in edgeSet ∧ x = v ∧ y = v := by simp

/--
lemma `bouquet_inc` / 引理 `bouquet_inc`

English:
lemma bouquet_inc
  given: (v : α) (edgeSet : Set β)
  proof: by simp

中文:
引理 bouquet_inc
  条件: (v : α) (edgeSet : 集合 β)
  证明: by simp
-/
lemma bouquet_inc (v : α) (edgeSet : Set β) :
    (bouquet v edgeSet).Inc e x ↔ e in edgeSet ∧ x = v := by simp

/--
lemma `bouquet_adj` / 引理 `bouquet_adj`

English:
lemma bouquet_adj
  given: (v : α) (edgeSet : Set β)
  proof: by simp

中文:
引理 bouquet_adj
  条件: (v : α) (edgeSet : 集合 β)
  证明: by simp
-/
lemma bouquet_adj (v : α) (edgeSet : Set β) :
    (bouquet v edgeSet).Adj x y ↔ edgeSet.Nonempty ∧ x = v ∧ y = v := by simp

/--
lemma `bouquet_isLoopAt` / 引理 `bouquet_isLoopAt`

English:
lemma bouquet_isLoopAt
  given: (v : α) (edgeSet : Set β)
  proof: by simp

中文:
引理 bouquet_isLoopAt
  条件: (v : α) (edgeSet : 集合 β)
  证明: by simp
-/
lemma bouquet_isLoopAt (v : α) (edgeSet : Set β) :
    (bouquet v edgeSet).IsLoopAt e x ↔ e in edgeSet ∧ x = v := by simp

/--
lemma `not_isNonloopAt_bouquet` / 引理 `not_isNonloopAt_bouquet`

English:
lemma not_isNonloopAt_bouquet
  statement: ¬ (bouquet v edgeSet).IsNonloopAt e x
  proof: by
  simp +contextual [IsNonloopAt, eq_comm]

中文:
引理 not_isNonloopAt_bouquet
  结论: ¬ (bouquet v edgeSet).IsNonloopAt e x
  证明: by
  simp +contextual [IsNonloopAt, eq_comm]

Depends on / 依赖: IsNonloopAt, contextual, eq_comm
-/
lemma not_isNonloopAt_bouquet : ¬ (bouquet v edgeSet).IsNonloopAt e x := by
  simp +contextual [IsNonloopAt, eq_comm]

/--
lemma `eq_bouquet_of_subsingleton` / 引理 `eq_bouquet_of_subsingleton`

English:
lemma eq_bouquet_of_subsingleton
  given: (hv : v in V(G)) (hss : V(G).Subsingleton)
  proof: by
  have hrw := hss.eq_singleton_of_mem hv
  refine Graph.ext_inc (by simpa) fun e x => ⟨fun h => ?_, fun h => ?_⟩
  · simp [← mem_singleton_iff, ← hrw, h.edge_mem, h.vertex_mem]
  simp only [bouquet_inc] at h
  obtain ⟨z, w, hzw⟩ := exists_isLink_of_mem_edgeSet h.1
  rw [h.2]; rw [← show z = v from (show z in {v} from hrw ▸ hzw.left_mem)]
  exact hzw.inc_left

中文:
引理 eq_bouquet_of_subsingleton
  条件: (hv : v in V(G)) (hss : V(G).子单例)
  证明: by
  have hrw := hss.eq_singleton_of_mem hv
  refine Graph.ext_inc (by simpa) fun e x => ⟨fun h => ?_, fun h => ?_⟩
  · simp [← mem_singleton_iff, ← hrw, h.edge_mem, h.vertex_mem]
  simp only [bouquet_inc] at h
  obtain ⟨z, w, hzw⟩ := exists_isLink_of_mem_edgeSet h.1
  rw [h.2]; rw [← show z = v from (show z in {v} from hrw ▸ hzw.left_mem)]
  exact hzw.inc_left

Depends on / 依赖: Graph.ext_inc, bouquet_inc, edge_mem, eq_singleton_of_mem, exists_isLink_of_mem_edgeSet, ext_inc, h.edge_mem, h.vertex_mem, hss.eq_singleton_of_mem, hzw.inc_left, hzw.left_mem, inc_left, left_mem, mem_singleton_iff, vertex_mem
-/
lemma eq_bouquet_of_subsingleton (hv : v in V(G)) (hss : V(G).Subsingleton) :
    G = bouquet v E(G) := by
  have hrw := hss.eq_singleton_of_mem hv
  refine Graph.ext_inc (by simpa) fun e x => ⟨fun h => ?_, fun h => ?_⟩
  · simp [← mem_singleton_iff, ← hrw, h.edge_mem, h.vertex_mem]
  simp only [bouquet_inc] at h
  obtain ⟨z, w, hzw⟩ := exists_isLink_of_mem_edgeSet h.1
  rw [h.2]; rw [← show z = v from (show z in {v} from hrw ▸ hzw.left_mem)]
  exact hzw.inc_left

/--
lemma `eq_bouquet_iff` / 引理 `eq_bouquet_iff`

English:
lemma eq_bouquet_iff
  statement: G = bouquet v E(G) ↔ V(G) = {v}
  proof: ⟨fun h => h ▸ vertexSet_bouquet v _,
    fun h => eq_bouquet_of_subsingleton (by simp [h]) (by simp [h])⟩

中文:
引理 eq_bouquet_iff
  结论: G = bouquet v E(G) ↔ V(G) = {v}
  证明: ⟨fun h => h ▸ vertexSet_bouquet v _,
    fun h => eq_bouquet_of_subsingleton (by simp [h]) (by simp [h])⟩

Depends on / 依赖: eq_bouquet_of_subsingleton, vertexSet_bouquet
-/
lemma eq_bouquet_iff : G = bouquet v E(G) ↔ V(G) = {v} :=
  ⟨fun h => h ▸ vertexSet_bouquet v _,
    fun h => eq_bouquet_of_subsingleton (by simp [h]) (by simp [h])⟩

/--
lemma `exists_eq_bouquet` / 引理 `exists_eq_bouquet`

English:
lemma exists_eq_bouquet
  given: (hne : V(G).Nonempty) (hss : V(G).Subsingleton)
  statement: exists x F, G = bouquet x F
  proof: ⟨_, _, eq_bouquet_of_subsingleton hne.some_mem hss⟩

中文:
引理 存在_eq_bouquet
  条件: (hne : V(G).非空) (hss : V(G).子单例)
  结论: 存在 x F, G = bouquet x F
  证明: ⟨_, _, eq_bouquet_of_subsingleton hne.some_mem hss⟩

Depends on / 依赖: eq_bouquet_of_subsingleton, hne.some_mem, some_mem
-/
lemma exists_eq_bouquet (hne : V(G).Nonempty) (hss : V(G).Subsingleton) : exists x F, G = bouquet x F :=
  ⟨_, _, eq_bouquet_of_subsingleton hne.some_mem hss⟩

/--
lemma `bouquet_empty` / 引理 `bouquet_empty`

English:
lemma bouquet_empty
  given: (v : α)
  statement: bouquet v ∅ = noEdge {v} β
  proof: by simp

中文:
引理 bouquet_empty
  条件: (v : α)
  结论: bouquet v ∅ = noEdge {v} β
  证明: by simp
-/
lemma bouquet_empty (v : α) : bouquet v ∅ = noEdge {v} β := by simp

end Graph
