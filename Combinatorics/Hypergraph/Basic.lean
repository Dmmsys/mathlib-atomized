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
/-
**Hypergraph** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Type u_4 → Type u_4
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An undirected hypergraph with vertices of type `α` and edges of type `Set α`, as
 described by vertex
and edge sets `vertexSet : Set α` and `edgeSet : Set (Set α)`.

The requirement `subset_vertexSet_of_mem_edgeSet` ensures that all vertices in e
dges are part of
`vertexSet`, i.e., all edges are subsets of the `vertexSet`.
-/
structure Hypergraph (α : Type*) where
  /-- The vertex set -/
  vertexSet : Set α
  /-- The edge set -/
  edgeSet : Set (Set α)
  /-- All edges must be subsets of the vertex set -/
  subset_vertexSet_of_mem_edgeSet' : ∀ ⦃e⦄, e ∈ edgeSet → e ⊆ vertexSet

namespace Hypergraph

variable {H : Hypergraph α}

/-! ## Notation -/

/-- `V(H)` denotes the `vertexSet` of a hypergraph `H` -/
scoped notation "V(" H ")" => Hypergraph.vertexSet H

/-- `E(H)` denotes the `edgeSet` of a hypergraph `H` -/
scoped notation "E(" H ")" => Hypergraph.edgeSet H


/-! ## Vertex-Hyperedge Incidence -/

@[simp]
/-
**Hypergraph.subset_vertexSet_of_mem_edgeSet** 是 Mathlib 中的一个引理，位于命名空间 `Hypergra
ph`。
形式化陈述：subset_vertexSet_of_mem_edgeSet (he : e in E(H)) : e subseteq V(H)
参数：he : e in E(H)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Hypergraph.subset_vertexSet_of_mem_edgeSet'`：∀ {α : Type u_4} (self : Hy
pergraph α) ⦃e : Set α⦄, e ∈ self.edgeSet → e ⊆ self.vertexSet

--- 原说明 ---
## Vertex-Hyperedge Incidence
-/
lemma subset_vertexSet_of_mem_edgeSet (he : e ∈ E(H)) : e ⊆ V(H) :=
  H.subset_vertexSet_of_mem_edgeSet' he

alias _root_.Membership.mem.subset_vertexSet := subset_vertexSet_of_mem_edgeSet
/-
**Hypergraph.edgeSet_subset_powerset_vertexSet** 是 Mathlib 中的一个引理，位于命名空间 `Hyperg
raph`。
形式化陈述：edgeSet_subset_powerset_vertexSet {H : Hypergraph α} : E(H) subseteq V(H).
powerset
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Hypergraph.subset_vertexSet_of_mem_edgeSet`：subset_vertexSet_of_mem_edge
Set (he : e in E(H)) : e subseteq V(H)
-/
lemma edgeSet_subset_powerset_vertexSet {H : Hypergraph α} : E(H) ⊆ V(H).powerset :=
  fun _ ↦ subset_vertexSet_of_mem_edgeSet
/-
**Hypergraph.mem_vertexSet_of_mem_edgeSet** 是 Mathlib 中的一个引理，位于命名空间 `Hypergraph`
。
形式化陈述：mem_vertexSet_of_mem_edgeSet (he : e in E(H)) (hx : x in e) : x in V(H)
参数：he : e in E(H)；hx : x in e。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Hypergraph.subset_vertexSet_of_mem_edgeSet`：subset_vertexSet_of_mem_edge
Set (he : e in E(H)) : e subseteq V(H)
-/
lemma mem_vertexSet_of_mem_edgeSet (he : e ∈ E(H)) (hx : x ∈ e) : x ∈ V(H) :=
  H.subset_vertexSet_of_mem_edgeSet he hx
/-
**Hypergraph.edgeSet.ext_iff** 是 Mathlib 中的一个定理，位于命名空间 `Hypergraph.edgeSet`。
形式化陈述：∀ {α : Type u_1} {e e' : Set α} {H : Hypergraph α},   e ∈ H.edgeSet → e' ∈
 H.edgeSet → (e = e' ↔ ∀ x ∈ H.vertexSet, x ∈ e ↔ x ∈ e')
参数：e = e' ↔ ∀ x ∈ H.vertexSet, x ∈ e ↔ x ∈ e'。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma edgeSet.ext_iff (he : e ∈ E(H)) (he' : e' ∈ E(H)) : e = e' ↔ ∀ x ∈ V(H), x ∈ e ↔ x ∈ e' := by
  grind [he.subset_vertexSet, he'.subset_vertexSet]
/-
**Hypergraph.sUnion_edgeSet_subset_vertexSet** 是 Mathlib 中的一个引理，位于命名空间 `Hypergra
ph`。
形式化陈述：sUnion_edgeSet_subset_vertexSet : ⋃₀ E(H) subseteq V(H)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.subset_powerset_iff`：subset_powerset_iff {s : Set (Set α)} {t : Set 
α} : s subseteq 𝒫 t ↔ ⋃₀ s subseteq t
· 使用引理 `Hypergraph.edgeSet_subset_powerset_vertexSet`：edgeSet_subset_powerset_ve
rtexSet {H : Hypergraph α} : E(H) subseteq V(H).powerset
-/
lemma sUnion_edgeSet_subset_vertexSet : ⋃₀ E(H) ⊆ V(H) :=
  subset_powerset_iff.mp edgeSet_subset_powerset_vertexSet

/-! ## Vertex and Hyperedge Adjacency -/

/--
Predicate for adjacency. Two vertices `x` and `y` are adjacent if there is some edge `e ∈ E(H)`
where `x` and `y` are both incident to `e`.

Note that we do not need to explicitly check that `x, y ∈ V(H)` here because a vertex that is not in
the vertex set cannot be incident to any edge.
-/
@[expose]
/-
**Hypergraph.Adj** 是 Mathlib 中的一个定义，位于命名空间 `Hypergraph`。
形式化陈述：Adj (H : Hypergraph α) (x : α) (y : α) : Prop
参数：H : Hypergraph α；x : α；y : α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Predicate for adjacency. Two vertices `x` and `y` are adjacent if there is some 
edge `e ∈ E(H)`
where `x` and `y` are both incident to `e`.

Note that we do not need to explicitly check that `x, y ∈ V(H)` here because a v
ertex that is not in
the vertex set cannot be incident to any edge.
-/
def Adj (H : Hypergraph α) (x : α) (y : α) : Prop :=
  ∃ e ∈ E(H), x ∈ e ∧ y ∈ e
/-
**Hypergraph.Adj.symm** 是 Mathlib 中的一个定理，位于命名空间 `Hypergraph.Adj`。
形式化陈述：∀ {α : Type u_1} {x y : α} {H : Hypergraph α}, H.Adj x y → H.Adj y x
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Adj.symm (h : H.Adj x y) : H.Adj y x := by grind [Adj]
/-
**Hypergraph.adj_comm** 是 Mathlib 中的一个引理，位于命名空间 `Hypergraph`。
形式化陈述：adj_comm (x y : α) : H.Adj x y ↔ H.Adj y x
参数：x y : α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Hypergraph.Adj.symm`：∀ {α : Type u_1} {x y : α} {H : Hypergraph α}, H.Ad
j x y → H.Adj y x
-/
lemma adj_comm (x y : α) : H.Adj x y ↔ H.Adj y x := ⟨.symm, .symm⟩

/--
Predicate for edge adjacency. Analogous to `Hypergraph.Adj`, edges `e` and `f` are
adjacent if there is some vertex `x ∈ V(H)` where `x` is incident to both `e` and `f`.
-/
@[expose]
/-
**Hypergraph.EAdj** 是 Mathlib 中的一个定义，位于命名空间 `Hypergraph`。
形式化陈述：EAdj (H : Hypergraph α) (e : Set α) (f : Set α) : Prop
参数：H : Hypergraph α；e : Set α；f : Set α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Predicate for edge adjacency. Analogous to `Hypergraph.Adj`, edges `e` and `f` a
re
adjacent if there is some vertex `x ∈ V(H)` where `x` is incident to both `e` an
d `f`.
-/
def EAdj (H : Hypergraph α) (e : Set α) (f : Set α) : Prop :=
  e ∈ E(H) ∧ f ∈ E(H) ∧ ∃ x, x ∈ e ∧ x ∈ f
/-
**Hypergraph.EAdj.exists_vertex** 是 Mathlib 中的一个定理，位于命名空间 `Hypergraph.EAdj`。
形式化陈述：∀ {α : Type u_1} {e f : Set α} {H : Hypergraph α}, H.EAdj e f → ∃ x ∈ H.ve
rtexSet, x ∈ e ∧ x ∈ f
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用引理 `Hypergraph.mem_vertexSet_of_mem_edgeSet`：mem_vertexSet_of_mem_edgeSet (h
e : e in E(H)) (hx : x in e) : x in V(H)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
lemma EAdj.exists_vertex (h : H.EAdj e f) : ∃ x ∈ V(H), x ∈ e ∧ x ∈ f := by
  obtain ⟨x, hx⟩ := h.2.2
  exact ⟨x, mem_vertexSet_of_mem_edgeSet h.1 hx.1, hx⟩
/-
**Hypergraph.EAdj.symm** 是 Mathlib 中的一个定理，位于命名空间 `Hypergraph.EAdj`。
形式化陈述：∀ {α : Type u_1} {e f : Set α} {H : Hypergraph α}, H.EAdj e f → H.EAdj f e
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma EAdj.symm (h : H.EAdj e f) : H.EAdj f e := by grind [EAdj]
/-
**Hypergraph.EAdj.inter_nonempty** 是 Mathlib 中的一个定理，位于命名空间 `Hypergraph.EAdj`。
形式化陈述：∀ {α : Type u_1} {e f : Set α} {H : Hypergraph α}, H.EAdj e f → (e ∩ f).No
nempty
参数：e ∩ f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.inter_nonempty`：inter_nonempty : (s inter t).Nonempty ↔ exists x, x 
in s ∧ x in t
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
lemma EAdj.inter_nonempty (hef : H.EAdj e f) : (e ∩ f).Nonempty :=
  Set.inter_nonempty.mpr hef.2.2
/-
**Hypergraph.eAdj_comm** 是 Mathlib 中的一个引理，位于命名空间 `Hypergraph`。
形式化陈述：eAdj_comm (e f) : H.EAdj e f ↔ H.EAdj f e
参数：e f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Hypergraph.EAdj.symm`：∀ {α : Type u_1} {e f : Set α} {H : Hypergraph α},
 H.EAdj e f → H.EAdj f e
-/
lemma eAdj_comm (e f) : H.EAdj e f ↔ H.EAdj f e := ⟨.symm, .symm⟩

/-! ## Basic Hypergraph Definitions & Predicates-/

/-- The *image* of a hypergraph `H : Hypergraph α` under a function `f : α → β` is the hypergraph
`Hᶠ : Hypergraph β` where the vertex set of `Hᶠ` is the image of `V(H)` under `f` and the edge set
of `Hᶠ` is the set of images of the edges (subsets of vertices) in `E(H)`. -/
@[simps, expose]
/-
**Hypergraph.image** 是 Mathlib 中的一个定义，位于命名空间 `Hypergraph`。
形式化陈述：{α : Type u_1} → {β : Type u_2} → Hypergraph α → (α → β) → Hypergraph β
参数：α → β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The *image* of a hypergraph `H : Hypergraph α` under a function `f : α → β` is t
he hypergraph
`Hᶠ : Hypergraph β` where the vertex set of `Hᶠ` is the image of `V(H)` under `f
` and the edge set
of `Hᶠ` is the set of images of the edges (subsets of vertices) in `E(H)`.
-/
protected def image (H : Hypergraph α) (f : α → β) : Hypergraph β where
  vertexSet := V(H).image f
  edgeSet := E(H).image (Set.image f)
  subset_vertexSet_of_mem_edgeSet' := by
    rintro - ⟨e, he, rfl⟩
    exact image_mono he.subset_vertexSet
/-
**Hypergraph.mem_edgeSet_image** 是 Mathlib 中的一个引理，位于命名空间 `Hypergraph`。
形式化陈述：mem_edgeSet_image {f : α -> β} {e : Set β} : e in E(H.image f) ↔ exists e'
 in E(H), f '' e' = e
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma mem_edgeSet_image {f : α → β} {e : Set β} : e ∈ E(H.image f) ↔ ∃ e' ∈ E(H), f '' e' = e :=
  .rfl
/-
**Hypergraph.image_mem_edgeSet_image** 是 Mathlib 中的一个引理，位于命名空间 `Hypergraph`。
形式化陈述：image_mem_edgeSet_image {f : α -> β} (he : e in E(H)) : e.image f in E(H.i
mage f)
参数：he : e in E(H)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
-/
lemma image_mem_edgeSet_image {f : α → β} (he : e ∈ E(H)) : e.image f ∈ E(H.image f) :=
  mem_image_of_mem _ he
/-
**Hypergraph.image_image** 是 Mathlib 中的一个引理，位于命名空间 `Hypergraph`。
形式化陈述：image_image {f : α -> β} {g : β -> γ} (H : Hypergraph α) : (H.image f).ima
ge g = H.image (g ∘ f)
参数：H : Hypergraph α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Hypergraph.ext`：∀ {α : Type u_4} {x y : Hypergraph α}, x.vertexSet = y.v
ertexSet → x.edgeSet = y.edgeSet → x = y
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Hypergraph.image_vertexSet`：∀ {α : Type u_1} {β : Type u_2} (H : Hypergr
aph α) (f : α → β), (H.image f).vertexSet = f '' H.vertexSet
· 使用定理 `Set.image_image`：image_image (g : β -> γ) (f : α -> β) (s : Set α) : g '
' f '' s = (fun x => g (f x)) '' s
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Hypergraph.image_edgeSet`：∀ {α : Type u_1} {β : Type u_2} (H : Hypergrap
h α) (f : α → β), (H.image f).edgeSet = Set.image f '' H.edgeSet
-/
lemma image_image {f : α → β} {g : β → γ} (H : Hypergraph α) :
    (H.image f).image g = H.image (g ∘ f) := by
  ext <;> simp [Set.image_image]

/-- A vertex is isolated if it is not incident to any edges (including loops). -/
@[expose]
/-
**Hypergraph.IsIsolated** 是 Mathlib 中的一个定义，位于命名空间 `Hypergraph`。
形式化陈述：IsIsolated (H : Hypergraph α) (x : α) : Prop
参数：H : Hypergraph α；x : α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A vertex is isolated if it is not incident to any edges (including loops).
-/
def IsIsolated (H : Hypergraph α) (x : α) : Prop := ∀ e ∈ E(H), x ∉ e
/-
**Hypergraph.sUnion_edgeSet_eq_vertexSet_iff_all_vertex_not_isolated** 是 Mathlib
 中的一个引理，位于命名空间 `Hypergraph`。
形式化陈述：sUnion_edgeSet_eq_vertexSet_iff_all_vertex_not_isolated : ⋃₀ E(H) = V(H) ↔
 forall x in V(H), ¬IsIsolated H x
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma sUnion_edgeSet_eq_vertexSet_iff_all_vertex_not_isolated :
    ⋃₀ E(H) = V(H) ↔ ∀ x ∈ V(H), ¬IsIsolated H x := by
  grind [IsIsolated, mem_vertexSet_of_mem_edgeSet]

/-- A loop is an edge whose associated vertex subset consists of a single vertex. -/
@[expose]
/-
**Hypergraph.IsLoop** 是 Mathlib 中的一个定义，位于命名空间 `Hypergraph`。
形式化陈述：IsLoop (H : Hypergraph α) (e : Set α) : Prop
参数：H : Hypergraph α；e : Set α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A loop is an edge whose associated vertex subset consists of a single vertex.
-/
def IsLoop (H : Hypergraph α) (e : Set α) : Prop := e ∈ E(H) ∧ ∃ x, e = {x}
/-
**Hypergraph.isLoop_iff_mem_edgeSet_and_singleton** 是 Mathlib 中的一个引理，位于命名空间 `Hyp
ergraph`。
形式化陈述：isLoop_iff_mem_edgeSet_and_singleton : H.IsLoop e ↔ (e in E(H) ∧ exists x,
 e = {x})
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma isLoop_iff_mem_edgeSet_and_singleton : H.IsLoop e ↔ (e ∈ E(H) ∧ ∃ x, e = {x}) := .rfl
/-
**Hypergraph.isLoop_iff_mem_and_ncard_one** 是 Mathlib 中的一个引理，位于命名空间 `Hypergraph`
。
形式化陈述：isLoop_iff_mem_and_ncard_one : H.IsLoop e ↔ (e in E(H) ∧ Set.ncard e = 1)
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma isLoop_iff_mem_and_ncard_one : H.IsLoop e ↔ (e ∈ E(H) ∧ Set.ncard e = 1) := by
  grind [IsLoop, ncard_eq_one, mem_vertexSet_of_mem_edgeSet]
/-
**Hypergraph.IsLoop.ncard_one** 是 Mathlib 中的一个定理，位于命名空间 `Hypergraph.IsLoop`。
形式化陈述：∀ {α : Type u_1} {e : Set α} {H : Hypergraph α}, H.IsLoop e → e.ncard = 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Hypergraph.isLoop_iff_mem_and_ncard_one`：isLoop_iff_mem_and_ncard_one : 
H.IsLoop e ↔ (e in E(H) ∧ Set.ncard e = 1)
-/
lemma IsLoop.ncard_one (h : H.IsLoop e) : Set.ncard e = 1 := (isLoop_iff_mem_and_ncard_one.mp h).2

/-- A hypergraph is nonempty if it has at least one vertex or at least one edge. -/
@[expose]
/-
**Hypergraph.IsNonempty** 是 Mathlib 中的一个定义，位于命名空间 `Hypergraph`。
形式化陈述：IsNonempty (H : Hypergraph α) : Prop
参数：H : Hypergraph α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A hypergraph is nonempty if it has at least one vertex or at least one edge.
-/
def IsNonempty (H : Hypergraph α) : Prop := V(H).Nonempty ∨ E(H).Nonempty

/-- The empty hypergraph (bottom) on a type. -/
@[simps]
/-
**Hypergraph.** 是 Mathlib 中的一个实例，位于命名空间 `Hypergraph`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The empty hypergraph (bottom) on a type.
-/
instance (α : Type*) : Bot (Hypergraph α) where
  bot.vertexSet := ∅
  bot.edgeSet := ∅
  bot.subset_vertexSet_of_mem_edgeSet' := by simp

@[simp]
/-
**Hypergraph.IsNonempty.of_nonempty_vertexSet** 是 Mathlib 中的一个定理，位于命名空间 `Hypergr
aph.IsNonempty`。
形式化陈述：∀ {α : Type u_1} {H : Hypergraph α}, H.vertexSet.Nonempty → H.IsNonempty
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma IsNonempty.of_nonempty_vertexSet (hV : V(H).Nonempty) : H.IsNonempty :=
  .inl hV

@[simp]
/-
**Hypergraph.IsNonempty.of_nonempty_edgeSet** 是 Mathlib 中的一个定理，位于命名空间 `Hypergrap
h.IsNonempty`。
形式化陈述：∀ {α : Type u_1} {H : Hypergraph α}, H.edgeSet.Nonempty → H.IsNonempty
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma IsNonempty.of_nonempty_edgeSet (hE : E(H).Nonempty) : H.IsNonempty :=
  .inr hE

@[simp]
/-
**Hypergraph.ne_bot_iff** 是 Mathlib 中的一个定理，位于命名空间 `Hypergraph`。
形式化陈述：ne_bot_iff : H != ⊥ ↔ H.IsNonempty
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
-/
theorem ne_bot_iff : H ≠ ⊥ ↔ H.IsNonempty := by
  simp [IsNonempty, Set.nonempty_iff_ne_empty, Hypergraph.ext_iff]
  grind [bot_vertexSet, bot_edgeSet]

alias ⟨_, IsNonempty.ne_bot⟩ := ne_bot_iff

@[simp]
/-
**Hypergraph.not_isNonempty_iff** 是 Mathlib 中的一个定理，位于命名空间 `Hypergraph`。
形式化陈述：not_isNonempty_iff : ¬H.IsNonempty ↔ H = ⊥
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_iff_comm`：not_iff_comm : (¬a ↔ b) ↔ (¬b ↔ a)
· 使用定理 `Hypergraph.ne_bot_iff`：ne_bot_iff : H != ⊥ ↔ H.IsNonempty
-/
theorem not_isNonempty_iff : ¬H.IsNonempty ↔ H = ⊥ :=
  not_iff_comm.mp ne_bot_iff

variable (H) in
/-
**Hypergraph.eq_bot_or_isNonempty** 是 Mathlib 中的一个引理，位于命名空间 `Hypergraph`。
形式化陈述：eq_bot_or_isNonempty : H = ⊥ ∨ H.IsNonempty
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Hypergraph.ext`：∀ {α : Type u_4} {x y : Hypergraph α}, x.vertexSet = y.v
ertexSet → x.edgeSet = y.edgeSet → x = y
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
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
/-
**Hypergraph.IsTrivial** 是 Mathlib 中的一个定义，位于命名空间 `Hypergraph`。
形式化陈述：IsTrivial (H : Hypergraph α) : Prop
参数：H : Hypergraph α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A hypergraph is trivial if it has at least one vertex but no edges.
-/
def IsTrivial (H : Hypergraph α) : Prop := Set.Nonempty V(H) ∧ E(H) = ∅

/-- The trivial hypergraph with a given vertex set is defined by having no edges on that vertex
set. -/
@[simps, expose]
/-
**Hypergraph.trivialOn** 是 Mathlib 中的一个定义，位于命名空间 `Hypergraph`。
形式化陈述：trivialOn (f : Set α) : Hypergraph α where vertexSet
参数：f : Set α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The trivial hypergraph with a given vertex set is defined by having no edges on 
that vertex
set.
-/
def trivialOn (f : Set α) : Hypergraph α where
  vertexSet := f
  edgeSet := ∅
  subset_vertexSet_of_mem_edgeSet' := by simp
/-
**Hypergraph.IsTrivial.trivialOn** 是 Mathlib 中的一个定理，位于命名空间 `Hypergraph.IsTrivial
`。
形式化陈述：∀ {α : Type u_1} {f : Set α}, f.Nonempty → (Hypergraph.trivialOn f).IsTriv
ial
参数：Hypergraph.trivialOn f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma IsTrivial.trivialOn (hf : Set.Nonempty f) :
    IsTrivial (trivialOn f) := by
  grind [trivialOn, IsTrivial]
/-
**Hypergraph.IsTrivial.isNonempty** 是 Mathlib 中的一个定理，位于命名空间 `Hypergraph.IsTrivia
l`。
形式化陈述：∀ {α : Type u_1} {H : Hypergraph α}, H.IsTrivial → H.IsNonempty
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma IsTrivial.isNonempty (h : IsTrivial H) : IsNonempty H := by
  grind [IsNonempty, IsTrivial, Set.nonempty_iff_ne_empty]
/-
**Hypergraph.IsTrivial.not_mem_edgeSet** 是 Mathlib 中的一个定理，位于命名空间 `Hypergraph.IsT
rivial`。
形式化陈述：∀ {α : Type u_1} {e : Set α} {H : Hypergraph α}, H.IsTrivial → e ∉ H.edgeS
et
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma IsTrivial.not_mem_edgeSet (h : H.IsTrivial) : e ∉ E(H) := by grind [IsTrivial]

/-- A hypergraph is complete if every subset of the vertex set is in the edge set. -/
@[expose]
/-
**Hypergraph.IsComplete** 是 Mathlib 中的一个定义，位于命名空间 `Hypergraph`。
形式化陈述：IsComplete (H : Hypergraph α) : Prop
参数：H : Hypergraph α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A hypergraph is complete if every subset of the vertex set is in the edge set.
-/
def IsComplete (H : Hypergraph α) : Prop := ∀ e ⊆ V(H), e ∈ E(H)

/-- The complete hypergraph with a given vertex set, which has each subset of the vertex set as an
edge. -/
@[simps, expose]
/-
**Hypergraph.completeOn** 是 Mathlib 中的一个定义，位于命名空间 `Hypergraph`。
形式化陈述：completeOn (f : Set α) : Hypergraph α where vertexSet
参数：f : Set α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The complete hypergraph with a given vertex set, which has each subset of the ve
rtex set as an
edge.
-/
def completeOn (f : Set α) : Hypergraph α where
  vertexSet := f
  edgeSet := 𝒫 f
  subset_vertexSet_of_mem_edgeSet' := by simp
/-
**Hypergraph.mem_completeOn** 是 Mathlib 中的一个引理，位于命名空间 `Hypergraph`。
形式化陈述：mem_completeOn : e in E(completeOn f) ↔ e subseteq f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Hypergraph.completeOn_edgeSet`：∀ {α : Type u_1} (f : Set α), (Hypergraph
.completeOn f).edgeSet = 𝒫 f
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma mem_completeOn : e ∈ E(completeOn f) ↔ e ⊆ f := by simp
/-
**Hypergraph.IsComplete.mem_iff** 是 Mathlib 中的一个定理，位于命名空间 `Hypergraph.IsComplete
`。
形式化陈述：∀ {α : Type u_1} {e : Set α} {H : Hypergraph α}, H.IsComplete → (e ∈ H.edg
eSet ↔ e ⊆ H.vertexSet)
参数：e ∈ H.edgeSet ↔ e ⊆ H.vertexSet。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma IsComplete.mem_iff (h : H.IsComplete) : e ∈ E(H) ↔ e ⊆ V(H) := by
  grind [IsComplete, subset_vertexSet_of_mem_edgeSet]
/-
**Hypergraph.IsComplete.completeOn** 是 Mathlib 中的一个定理，位于命名空间 `Hypergraph.IsCompl
ete`。
形式化陈述：∀ {α : Type u_1} (f : Set α), (Hypergraph.completeOn f).IsComplete
参数：f : Set α；Hypergraph.completeOn f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma IsComplete.completeOn (f : Set α) : (completeOn f).IsComplete := fun _ a ↦ a
/-
**Hypergraph.IsComplete.isNonempty** 是 Mathlib 中的一个定理，位于命名空间 `Hypergraph.IsCompl
ete`。
形式化陈述：∀ {α : Type u_1} {H : Hypergraph α}, H.IsComplete → H.IsNonempty
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.empty_subset`：empty_subset (s : Set α) : ∅ subseteq s
-/
lemma IsComplete.isNonempty (h : H.IsComplete) : H.IsNonempty :=
  Or.inr ⟨∅, h ∅ (Set.empty_subset _)⟩
/-
**Hypergraph.IsComplete.not_isTrivial** 是 Mathlib 中的一个定理，位于命名空间 `Hypergraph.IsCo
mplete`。
形式化陈述：∀ {α : Type u_1} {H : Hypergraph α}, H.IsComplete → ¬H.IsTrivial
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Hypergraph.IsTrivial.not_mem_edgeSet`：∀ {α : Type u_1} {e : Set α} {H : 
Hypergraph α}, H.IsTrivial → e ∉ H.edgeSet
· 使用定理 `Set.empty_subset`：empty_subset (s : Set α) : ∅ subseteq s
-/
lemma IsComplete.not_isTrivial (h : H.IsComplete) : ¬ H.IsTrivial := by
  intro hH
  exact hH.not_mem_edgeSet (h ∅ (Set.empty_subset _))
/-
**Hypergraph.not_isTrivial_completeOn** 是 Mathlib 中的一个引理，位于命名空间 `Hypergraph`。
形式化陈述：not_isTrivial_completeOn (f : Set α) : ¬ (completeOn f).IsTrivial
参数：f : Set α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Hypergraph.IsComplete.not_isTrivial`：∀ {α : Type u_1} {H : Hypergraph α}
, H.IsComplete → ¬H.IsTrivial
· 使用定理 `Hypergraph.IsComplete.completeOn`：∀ {α : Type u_1} (f : Set α), (Hypergr
aph.completeOn f).IsComplete
-/
lemma not_isTrivial_completeOn (f : Set α) : ¬ (completeOn f).IsTrivial :=
  (IsComplete.completeOn f).not_isTrivial

end Hypergraph

