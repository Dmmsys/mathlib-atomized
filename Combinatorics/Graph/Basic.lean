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

/-- A multigraph with vertices of type `α` and edges of type `β`,
as described by vertex and edge sets `vertexSet : Set α` and `edgeSet : Set β`,
and a predicate `IsLink` describing whether an edge `e : β` has vertices `x y : α` as its ends.

The `edgeSet` structure field can be inferred from `IsLink`
via `edge_mem_iff_exists_isLink` (and this structure provides default values
for `edgeSet` and `edge_mem_iff_exists_isLink` that use `IsLink`).
While the field is not strictly necessary, when defining a graph we often
immediately know what the edge set should be,
and furthermore having `edgeSet` separate can be convenient for
definitional equality reasons.
-/
/-
**Graph** 是 Mathlib 中的一个结构，位于命名空间 ``。
形式化陈述：Graph (α β : Type*) where /-- The vertex set. -/ vertexSet : Set α /-- The
 binary incidence predicate, stating that `x` and `y` are the ends of an edge `e
`. If `G.IsLink e x y` then we refer to `e` as `edge` and `x` and `y` as `left` 
and `right`. -/ IsLink : β -> α -> α -> Prop /-- The edge set. -/ edgeSet : Set 
β
参数：α β : Type*。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A multigraph with vertices of type `α` and edges of type `β`,
as described by vertex and edge sets `vertexSet : Set α` and `edgeSet : Set β`,
and a predicate `IsLink` describing whether an edge `e : β` has vertices `x y : 
α` as its ends.

The `edgeSet` structure field can be inferred from `IsLink`
via `edge_mem_iff_exists_isLink` (and this structure provides default values
for `edgeSet` and `edge_mem_iff_exists_isLink` that use `IsLink`).
While the field is not strictly necessary, when defining a graph we often
immediately know what the edge set should be,
and furthermore having `edgeSet` separate can be convenient for
definitional equality reasons.
-/
structure Graph (α β : Type*) where
  /-- The vertex set. -/
  vertexSet : Set α
  /-- The binary incidence predicate, stating that `x` and `y` are the ends of an edge `e`.
  If `G.IsLink e x y` then we refer to `e` as `edge` and `x` and `y` as `left` and `right`. -/
  IsLink : β → α → α → Prop
  /-- The edge set. -/
  edgeSet : Set β := {e | ∃ x y, IsLink e x y}
  /-- If `e` goes from `x` to `y`, it goes from `y` to `x`. -/
  isLink_symm : ∀ ⦃e⦄, e ∈ edgeSet → Std.Symm (IsLink e)
  /-- An edge is incident with at most one pair of vertices. -/
  eq_or_eq_of_isLink_of_isLink : ∀ ⦃e x y v w⦄, IsLink e x y → IsLink e v w → x = v ∨ x = w
  /-- An edge `e` is incident to something if and only if `e` is in the edge set. -/
  edge_mem_iff_exists_isLink : ∀ e, e ∈ edgeSet ↔ ∃ x y, IsLink e x y := by exact fun _ ↦ Iff.rfl
  /-- If some edge `e` is incident to `x`, then `x ∈ V`. -/
  left_mem_of_isLink : ∀ ⦃e x y⦄, IsLink e x y → x ∈ vertexSet := by grind

initialize_simps_projections Graph (as_prefix edgeSet, as_prefix vertexSet, IsLink → isLink)

namespace Graph

variable {G H : Graph α β}

/-- `V(G)` denotes the `vertexSet` of a graph `G`. -/
scoped notation "V(" G ")" => Graph.vertexSet G

/-- `E(G)` denotes the `edgeSet` of a graph `G`. -/
scoped notation "E(" G ")" => Graph.edgeSet G

/-! ### Edge-vertex-vertex incidence -/

/-
**Graph.IsLink.edge_mem** 是 Mathlib 中的一个定理，位于命名空间 `Graph.IsLink`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {x y : α} {e : β} {G : Graph α β}, G.IsLin
k e x y → e ∈ G.edgeSet
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Graph.edge_mem_iff_exists_isLink`：∀ {α : Type u_3} {β : Type u_4} (self 
: Graph α β) (e : β), e ∈ self.edgeSet ↔ ∃ x y, self.IsLink e x y

--- 原说明 ---
### Edge-vertex-vertex incidence
-/
lemma IsLink.edge_mem (h : G.IsLink e x y) : e ∈ E(G) :=
  (edge_mem_iff_exists_isLink ..).2 ⟨x, y, h⟩

@[simp]
/-
**Graph.not_isLink_of_notMem_edgeSet** 是 Mathlib 中的一个引理，位于命名空间 `Graph`。
形式化陈述：not_isLink_of_notMem_edgeSet (he : e ∉ E(G)) : ¬ G.IsLink e x y
参数：he : e ∉ E(G)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Graph.IsLink.edge_mem`：∀ {α : Type u_1} {β : Type u_2} {x y : α} {e : β}
 {G : Graph α β}, G.IsLink e x y → e ∈ G.edgeSet
-/
lemma not_isLink_of_notMem_edgeSet (he : e ∉ E(G)) : ¬ G.IsLink e x y :=
  mt IsLink.edge_mem he
/-
**Graph.IsLink.symm** 是 Mathlib 中的一个定理，位于命名空间 `Graph.IsLink`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {x y : α} {e : β} {G : Graph α β}, G.IsLin
k e x y → G.IsLink e y x
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Std.Symm.symm`：∀ {α : Sort u} {r : α → α → Prop} [self : Std.Symm r] (a 
b : α), r a b → r b a
· 使用定理 `Graph.isLink_symm`：∀ {α : Type u_3} {β : Type u_4} (self : Graph α β) ⦃e
 : β⦄, e ∈ self.edgeSet → Std.Symm (self.IsLink e)
· 使用定理 `Graph.IsLink.edge_mem`：∀ {α : Type u_1} {β : Type u_2} {x y : α} {e : β}
 {G : Graph α β}, G.IsLink e x y → e ∈ G.edgeSet
-/
protected lemma IsLink.symm (h : G.IsLink e x y) : G.IsLink e y x :=
  G.isLink_symm h.edge_mem |>.symm x y h

@[grind →]
/-
**Graph.IsLink.left_mem** 是 Mathlib 中的一个定理，位于命名空间 `Graph.IsLink`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {x y : α} {e : β} {G : Graph α β}, G.IsLin
k e x y → x ∈ G.vertexSet
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Graph.left_mem_of_isLink`：∀ {α : Type u_3} {β : Type u_4} (self : Graph 
α β) ⦃e : β⦄ ⦃x y : α⦄, self.IsLink e x y → x ∈ self.vertexSet
-/
lemma IsLink.left_mem (h : G.IsLink e x y) : x ∈ V(G) :=
  G.left_mem_of_isLink h

@[grind →]
/-
**Graph.IsLink.right_mem** 是 Mathlib 中的一个定理，位于命名空间 `Graph.IsLink`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {x y : α} {e : β} {G : Graph α β}, G.IsLin
k e x y → y ∈ G.vertexSet
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Graph.IsLink.left_mem`：∀ {α : Type u_1} {β : Type u_2} {x y : α} {e : β}
 {G : Graph α β}, G.IsLink e x y → x ∈ G.vertexSet
· 使用定理 `Graph.IsLink.symm`：∀ {α : Type u_1} {β : Type u_2} {x y : α} {e : β} {G 
: Graph α β}, G.IsLink e x y → G.IsLink e y x
-/
lemma IsLink.right_mem (h : G.IsLink e x y) : y ∈ V(G) :=
  h.symm.left_mem
/-
**Graph.isLink_comm** 是 Mathlib 中的一个引理，位于命名空间 `Graph`。
形式化陈述：isLink_comm : G.IsLink e x y ↔ G.IsLink e y x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Graph.IsLink.symm`：∀ {α : Type u_1} {β : Type u_2} {x y : α} {e : β} {G 
: Graph α β}, G.IsLink e x y → G.IsLink e y x
-/
lemma isLink_comm : G.IsLink e x y ↔ G.IsLink e y x :=
  ⟨.symm, .symm⟩
/-
**Graph.exists_isLink_of_mem_edgeSet** 是 Mathlib 中的一个引理，位于命名空间 `Graph`。
形式化陈述：exists_isLink_of_mem_edgeSet (h : e in E(G)) : exists x y, G.IsLink e x y
参数：h : e in E(G)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Graph.edge_mem_iff_exists_isLink`：∀ {α : Type u_3} {β : Type u_4} (self 
: Graph α β) (e : β), e ∈ self.edgeSet ↔ ∃ x y, self.IsLink e x y
-/
lemma exists_isLink_of_mem_edgeSet (h : e ∈ E(G)) : ∃ x y, G.IsLink e x y :=
  (edge_mem_iff_exists_isLink ..).1 h
/-
**Graph.edgeSet_eq_setOfPred_exists_isLink** 是 Mathlib 中的一个引理，位于命名空间 `Graph`。
形式化陈述：edgeSet_eq_setOfPred_exists_isLink : E(G) = {e | exists x y, G.IsLink e x 
y}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Graph.edge_mem_iff_exists_isLink`：∀ {α : Type u_3} {β : Type u_4} (self 
: Graph α β) (e : β), e ∈ self.edgeSet ↔ ∃ x y, self.IsLink e x y
-/
lemma edgeSet_eq_setOfPred_exists_isLink : E(G) = {e | ∃ x y, G.IsLink e x y} :=
  Set.ext G.edge_mem_iff_exists_isLink

@[deprecated (since := "2026-07-09")]
alias edgeSet_eq_setOf_exists_isLink := edgeSet_eq_setOfPred_exists_isLink
/-
**Graph.IsLink.left_eq_or_eq** 是 Mathlib 中的一个定理，位于命名空间 `Graph.IsLink`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {x y z w : α} {e : β} {G : Graph α β}, G.I
sLink e x y → G.IsLink e z w → x = z ∨ x = w
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Graph.eq_or_eq_of_isLink_of_isLink`：∀ {α : Type u_3} {β : Type u_4} (sel
f : Graph α β) ⦃e : β⦄ ⦃x y v w : α⦄,   self.IsLink e x y → self.IsLink e v w → 
x = v ∨ x = w
-/
lemma IsLink.left_eq_or_eq (h : G.IsLink e x y) (h' : G.IsLink e z w) : x = z ∨ x = w :=
  G.eq_or_eq_of_isLink_of_isLink h h'
/-
**Graph.IsLink.right_eq_or_eq** 是 Mathlib 中的一个定理，位于命名空间 `Graph.IsLink`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {x y z w : α} {e : β} {G : Graph α β}, G.I
sLink e x y → G.IsLink e z w → y = z ∨ y = w
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Graph.IsLink.left_eq_or_eq`：∀ {α : Type u_1} {β : Type u_2} {x y z w : α
} {e : β} {G : Graph α β}, G.IsLink e x y → G.IsLink e z w → x = z ∨ x = w
· 使用定理 `Graph.IsLink.symm`：∀ {α : Type u_1} {β : Type u_2} {x y : α} {e : β} {G 
: Graph α β}, G.IsLink e x y → G.IsLink e y x
-/
lemma IsLink.right_eq_or_eq (h : G.IsLink e x y) (h' : G.IsLink e z w) : y = z ∨ y = w :=
  h.symm.left_eq_or_eq h'
/-
**Graph.IsLink.left_eq_of_right_ne** 是 Mathlib 中的一个定理，位于命名空间 `Graph.IsLink`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {x y z w : α} {e : β} {G : Graph α β}, G.I
sLink e x y → G.IsLink e z w → x ≠ z → x = w
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `Graph.IsLink.left_eq_or_eq`：∀ {α : Type u_1} {β : Type u_2} {x y z w : α
} {e : β} {G : Graph α β}, G.IsLink e x y → G.IsLink e z w → x = z ∨ x = w
-/
lemma IsLink.left_eq_of_right_ne (h : G.IsLink e x y) (h' : G.IsLink e z w) (hzx : x ≠ z) :
    x = w :=
  (h.left_eq_or_eq h').elim (False.elim ∘ hzx) id
/-
**Graph.IsLink.right_unique** 是 Mathlib 中的一个定理，位于命名空间 `Graph.IsLink`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {x y z : α} {e : β} {G : Graph α β}, G.IsL
ink e x y → G.IsLink e x z → y = z
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Graph.IsLink.right_eq_or_eq`：∀ {α : Type u_1} {β : Type u_2} {x y z w : 
α} {e : β} {G : Graph α β}, G.IsLink e x y → G.IsLink e z w → y = z ∨ y = w
· 使用定理 `Graph.IsLink.symm`：∀ {α : Type u_1} {β : Type u_2} {x y : α} {e : β} {G 
: Graph α β}, G.IsLink e x y → G.IsLink e y x
-/
lemma IsLink.right_unique (h : G.IsLink e x y) (h' : G.IsLink e x z) : y = z := by
  obtain rfl | rfl := h.right_eq_or_eq h'.symm
  · rfl
  obtain rfl | rfl := h'.right_eq_or_eq h.symm <;> rfl
/-
**Graph.IsLink.left_unique** 是 Mathlib 中的一个定理，位于命名空间 `Graph.IsLink`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {x y z : α} {e : β} {G : Graph α β}, G.IsL
ink e x z → G.IsLink e y z → x = y
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Graph.IsLink.right_unique`：∀ {α : Type u_1} {β : Type u_2} {x y z : α} {
e : β} {G : Graph α β}, G.IsLink e x y → G.IsLink e x z → y = z
· 使用定理 `Graph.IsLink.symm`：∀ {α : Type u_1} {β : Type u_2} {x y : α} {e : β} {G 
: Graph α β}, G.IsLink e x y → G.IsLink e y x
-/
lemma IsLink.left_unique (h : G.IsLink e x z) (h' : G.IsLink e y z) : x = y :=
  h.symm.right_unique h'.symm
/-
**Graph.IsLink.eq_and_eq_or_eq_and_eq** 是 Mathlib 中的一个定理，位于命名空间 `Graph.IsLink`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {x y : α} {e : β} {G : Graph α β} {x' y' :
 α},   G.IsLink e x y → G.IsLink e x' y' → x = x' ∧ y = y' ∨ x = y' ∧ y = x'
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Graph.IsLink.left_eq_or_eq`：∀ {α : Type u_1} {β : Type u_2} {x y z w : α
} {e : β} {G : Graph α β}, G.IsLink e x y → G.IsLink e z w → x = z ∨ x = w
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Graph.IsLink.right_unique`：∀ {α : Type u_1} {β : Type u_2} {x y z : α} {
e : β} {G : Graph α β}, G.IsLink e x y → G.IsLink e x z → y = z
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `Graph.IsLink.symm`：∀ {α : Type u_1} {β : Type u_2} {x y : α} {e : β} {G 
: Graph α β}, G.IsLink e x y → G.IsLink e y x
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
-/
lemma IsLink.eq_and_eq_or_eq_and_eq {x' y' : α} (h : G.IsLink e x y)
    (h' : G.IsLink e x' y') : (x = x' ∧ y = y') ∨ (x = y' ∧ y = x') := by
  obtain rfl | rfl := h.left_eq_or_eq h'
  · simp [h.right_unique h']
  simp [h'.symm.right_unique h]
/-
**Graph.IsLink.isLink_iff** 是 Mathlib 中的一个定理，位于命名空间 `Graph.IsLink`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {x y : α} {e : β} {G : Graph α β},   G.IsL
ink e x y → ∀ {x' y' : α}, G.IsLink e x' y' ↔ x = x' ∧ y = y' ∨ x = y' ∧ y = x'
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Graph.IsLink.eq_and_eq_or_eq_and_eq`：∀ {α : Type u_1} {β : Type u_2} {x 
y : α} {e : β} {G : Graph α β} {x' y' : α},   G.IsLink e x y → G.IsLink e x' y' 
→ x = x' ∧ y = y' ∨ x = y…
· 使用定理 `Graph.IsLink.symm`：∀ {α : Type u_1} {β : Type u_2} {x y : α} {e : β} {G 
: Graph α β}, G.IsLink e x y → G.IsLink e y x
-/
lemma IsLink.isLink_iff (h : G.IsLink e x y) {x' y' : α} :
    G.IsLink e x' y' ↔ (x = x' ∧ y = y') ∨ (x = y' ∧ y = x') := by
  refine ⟨h.eq_and_eq_or_eq_and_eq, ?_⟩
  rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
  · assumption
  exact h.symm
/-
**Graph.IsLink.isLink_iff_sym2_eq** 是 Mathlib 中的一个定理，位于命名空间 `Graph.IsLink`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {x y : α} {e : β} {G : Graph α β},   G.IsL
ink e x y → ∀ {x' y' : α}, G.IsLink e x' y' ↔ s(x, y) = s(x', y')
参数：x, y；x', y'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Graph.IsLink.isLink_iff`：∀ {α : Type u_1} {β : Type u_2} {x y : α} {e : 
β} {G : Graph α β},   G.IsLink e x y → ∀ {x' y' : α}, G.IsLink e x' y' ↔ x = x' 
∧ y = y' ∨ x …
· 使用定理 `Sym2.eq_iff`：eq_iff {x y z w : α} : s(x, y) = s(z, w) ↔ x = z ∧ y = w ∨ 
x = w ∧ y = z
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma IsLink.isLink_iff_sym2_eq (h : G.IsLink e x y) {x' y' : α} :
    G.IsLink e x' y' ↔ s(x, y) = s(x', y') := by
  rw [h.isLink_iff, Sym2.eq_iff]

/-! ### Edge-vertex incidence -/

/-- The unary incidence predicate of `G`. `G.Inc e x` means that the vertex `x`
is one or both of the ends of the edge `e`.
In the `Inc` namespace, we use `edge` and `vertex` to refer to `e` and `x`. -/
/-
**Graph.Inc** 是 Mathlib 中的一个定义，位于命名空间 `Graph`。
形式化陈述：Inc (G : Graph α β) (e : β) (x : α) : Prop
参数：G : Graph α β；e : β；x : α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The unary incidence predicate of `G`. `G.Inc e x` means that the vertex `x`
is one or both of the ends of the edge `e`.
In the `Inc` namespace, we use `edge` and `vertex` to refer to `e` and `x`.
-/
def Inc (G : Graph α β) (e : β) (x : α) : Prop := ∃ y, G.IsLink e x y

-- Cannot be @[simp] because `x` cannot be inferred by `simp`.
/-
**Graph.Inc.edge_mem** 是 Mathlib 中的一个定理，位于命名空间 `Graph.Inc`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {x : α} {e : β} {G : Graph α β}, G.Inc e x
 → e ∈ G.edgeSet
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Graph.IsLink.edge_mem`：∀ {α : Type u_1} {β : Type u_2} {x y : α} {e : β}
 {G : Graph α β}, G.IsLink e x y → e ∈ G.edgeSet
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
-/
lemma Inc.edge_mem (h : G.Inc e x) : e ∈ E(G) :=
  h.choose_spec.edge_mem

@[simp]
/-
**Graph.not_inc_of_notMem_edgeSet** 是 Mathlib 中的一个引理，位于命名空间 `Graph`。
形式化陈述：not_inc_of_notMem_edgeSet (he : e ∉ E(G)) : ¬ G.Inc e x
参数：he : e ∉ E(G)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Graph.Inc.edge_mem`：∀ {α : Type u_1} {β : Type u_2} {x : α} {e : β} {G :
 Graph α β}, G.Inc e x → e ∈ G.edgeSet
-/
lemma not_inc_of_notMem_edgeSet (he : e ∉ E(G)) : ¬ G.Inc e x :=
  mt Inc.edge_mem he

-- Cannot be @[simp] because `e` cannot be inferred by `simp`.
/-
**Graph.Inc.vertex_mem** 是 Mathlib 中的一个定理，位于命名空间 `Graph.Inc`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {x : α} {e : β} {G : Graph α β}, G.Inc e x
 → x ∈ G.vertexSet
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Graph.IsLink.left_mem`：∀ {α : Type u_1} {β : Type u_2} {x y : α} {e : β}
 {G : Graph α β}, G.IsLink e x y → x ∈ G.vertexSet
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
-/
lemma Inc.vertex_mem (h : G.Inc e x) : x ∈ V(G) :=
  h.choose_spec.left_mem

-- Cannot be @[simp] because `y` cannot be inferred by `simp`.
/-
**Graph.IsLink.inc_left** 是 Mathlib 中的一个定理，位于命名空间 `Graph.IsLink`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {x y : α} {e : β} {G : Graph α β}, G.IsLin
k e x y → G.Inc e x
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma IsLink.inc_left (h : G.IsLink e x y) : G.Inc e x :=
  ⟨y, h⟩

-- Cannot be @[simp] because `x` cannot be inferred by `simp`.
/-
**Graph.IsLink.inc_right** 是 Mathlib 中的一个定理，位于命名空间 `Graph.IsLink`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {x y : α} {e : β} {G : Graph α β}, G.IsLin
k e x y → G.Inc e y
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Graph.IsLink.symm`：∀ {α : Type u_1} {β : Type u_2} {x y : α} {e : β} {G 
: Graph α β}, G.IsLink e x y → G.IsLink e y x
-/
lemma IsLink.inc_right (h : G.IsLink e x y) : G.Inc e y :=
  ⟨x, h.symm⟩
/-
**Graph.Inc.eq_or_eq_of_isLink** 是 Mathlib 中的一个定理，位于命名空间 `Graph.Inc`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {x y z : α} {e : β} {G : Graph α β}, G.Inc
 e x → G.IsLink e y z → x = y ∨ x = z
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Graph.IsLink.left_eq_or_eq`：∀ {α : Type u_1} {β : Type u_2} {x y z w : α
} {e : β} {G : Graph α β}, G.IsLink e x y → G.IsLink e z w → x = z ∨ x = w
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
-/
lemma Inc.eq_or_eq_of_isLink (h : G.Inc e x) (h' : G.IsLink e y z) : x = y ∨ x = z :=
  h.choose_spec.left_eq_or_eq h'
/-
**Graph.Inc.eq_of_isLink_of_ne_left** 是 Mathlib 中的一个定理，位于命名空间 `Graph.Inc`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {x y z : α} {e : β} {G : Graph α β}, G.Inc
 e x → G.IsLink e y z → x ≠ y → x = z
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `Graph.Inc.eq_or_eq_of_isLink`：∀ {α : Type u_1} {β : Type u_2} {x y z : α
} {e : β} {G : Graph α β}, G.Inc e x → G.IsLink e y z → x = y ∨ x = z
-/
lemma Inc.eq_of_isLink_of_ne_left (h : G.Inc e x) (h' : G.IsLink e y z) (hxy : x ≠ y) : x = z :=
  (h.eq_or_eq_of_isLink h').elim (False.elim ∘ hxy) id
/-
**Graph.IsLink.isLink_iff_eq** 是 Mathlib 中的一个定理，位于命名空间 `Graph.IsLink`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {x y z : α} {e : β} {G : Graph α β}, G.IsL
ink e x y → (G.IsLink e x z ↔ z = y)
参数：G.IsLink e x z ↔ z = y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Graph.IsLink.right_unique`：∀ {α : Type u_1} {β : Type u_2} {x y z : α} {
e : β} {G : Graph α β}, G.IsLink e x y → G.IsLink e x z → y = z
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma IsLink.isLink_iff_eq (h : G.IsLink e x y) : G.IsLink e x z ↔ z = y :=
  ⟨fun h' ↦ h'.right_unique h, fun h' ↦ h' ▸ h⟩

/-- The binary incidence predicate can be expressed in terms of the unary one. -/
/-
**Graph.isLink_iff_inc** 是 Mathlib 中的一个引理，位于命名空间 `Graph`。
形式化陈述：isLink_iff_inc : G.IsLink e x y ↔ G.Inc e x ∧ G.Inc e y ∧ forall z, G.Inc 
e z -> z = x ∨ z = y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Graph.IsLink.inc_left`：∀ {α : Type u_1} {β : Type u_2} {x y : α} {e : β}
 {G : Graph α β}, G.IsLink e x y → G.Inc e x
· 使用定理 `Graph.IsLink.inc_right`：∀ {α : Type u_1} {β : Type u_2} {x y : α} {e : β
} {G : Graph α β}, G.IsLink e x y → G.Inc e y
· 使用定理 `Graph.Inc.eq_or_eq_of_isLink`：∀ {α : Type u_1} {β : Type u_2} {x y z : α
} {e : β} {G : Graph α β}, G.Inc e x → G.IsLink e y z → x = y ∨ x = z
· 使用定理 `Graph.IsLink.left_eq_or_eq`：∀ {α : Type u_1} {β : Type u_2} {x y z w : α
} {e : β} {G : Graph α β}, G.IsLink e x y → G.IsLink e z w → x = z ∨ x = w
· 使用定理 `Graph.IsLink.symm`：∀ {α : Type u_1} {β : Type u_2} {x y : α} {e : β} {G 
: Graph α β}, G.IsLink e x y → G.IsLink e y x

--- 原说明 ---
The binary incidence predicate can be expressed in terms of the unary one.
-/
lemma isLink_iff_inc : G.IsLink e x y ↔ G.Inc e x ∧ G.Inc e y ∧ ∀ z, G.Inc e z → z = x ∨ z = y := by
  refine ⟨fun h ↦ ⟨h.inc_left, h.inc_right, fun z h' ↦ h'.eq_or_eq_of_isLink h⟩, ?_⟩
  rintro ⟨⟨x', hx'⟩, ⟨y', hy'⟩, h⟩
  obtain rfl | rfl := h _ hx'.inc_right
  · obtain rfl | rfl := hx'.left_eq_or_eq hy'
    · assumption
    exact hy'.symm
  assumption

/-- Given a proof that the edge `e` is incident with the vertex `x` in `G`,
noncomputably find the other end of `e`. (If `e` is a loop, this is equal to `x` itself). -/
/-
**Graph.Inc.other** 是 Mathlib 中的一个定义，位于命名空间 `Graph.Inc`。
形式化陈述：{α : Type u_1} → {β : Type u_2} → {x : α} → {e : β} → {G : Graph α β} → G.
Inc e x → α
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a proof that the edge `e` is incident with the vertex `x` in `G`,
noncomputably find the other end of `e`. (If `e` is a loop, this is equal to `x`
 itself).
-/
protected noncomputable def Inc.other (h : G.Inc e x) : α := h.choose

@[simp]
/-
**Graph.Inc.isLink_other** 是 Mathlib 中的一个定理，位于命名空间 `Graph.Inc`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {x : α} {e : β} {G : Graph α β} (h : G.Inc
 e x), G.IsLink e x h.other
参数：h : G.Inc e x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
-/
lemma Inc.isLink_other (h : G.Inc e x) : G.IsLink e x h.other :=
  h.choose_spec

@[simp]
/-
**Graph.Inc.inc_other** 是 Mathlib 中的一个定理，位于命名空间 `Graph.Inc`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {x : α} {e : β} {G : Graph α β} (h : G.Inc
 e x), G.Inc e h.other
参数：h : G.Inc e x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Graph.IsLink.inc_right`：∀ {α : Type u_1} {β : Type u_2} {x y : α} {e : β
} {G : Graph α β}, G.IsLink e x y → G.Inc e y
· 使用定理 `Graph.Inc.isLink_other`：∀ {α : Type u_1} {β : Type u_2} {x : α} {e : β} 
{G : Graph α β} (h : G.Inc e x), G.IsLink e x h.other
-/
lemma Inc.inc_other (h : G.Inc e x) : G.Inc e h.other :=
  h.isLink_other.inc_right
/-
**Graph.Inc.eq_or_eq_or_eq** 是 Mathlib 中的一个定理，位于命名空间 `Graph.Inc`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {x y z : α} {e : β} {G : Graph α β},   G.I
nc e x → G.Inc e y → G.Inc e z → x = y ∨ x = z ∨ y = z
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Graph.Inc.eq_of_isLink_of_ne_left`：∀ {α : Type u_1} {β : Type u_2} {x y 
z : α} {e : β} {G : Graph α β}, G.Inc e x → G.IsLink e y z → x ≠ y → x = z
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
-/
lemma Inc.eq_or_eq_or_eq (hx : G.Inc e x) (hy : G.Inc e y) (hz : G.Inc e z) :
    x = y ∨ x = z ∨ y = z := by
  by_contra! ⟨hxy, hxz, hyz⟩
  obtain ⟨x', hx'⟩ := hx
  obtain rfl := hy.eq_of_isLink_of_ne_left hx' hxy.symm
  obtain rfl := hz.eq_of_isLink_of_ne_left hx' hxz.symm
  exact hyz rfl
/-
**Graph.inc_eq_inc_iff_isLink_eq_isLink** 是 Mathlib 中的一个引理，位于命名空间 `Graph`。
形式化陈述：inc_eq_inc_iff_isLink_eq_isLink {G₁ G₂ : Graph α β} : G₁.Inc e = G₂.Inc f 
↔ G₁.IsLink e = G₂.IsLink f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Graph.isLink_iff_inc`：isLink_iff_inc : G.IsLink e x y ↔ G.Inc e x ∧ G.In
c e y ∧ forall z, G.Inc e z -> z = x ∨ z = y
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma inc_eq_inc_iff_isLink_eq_isLink {G₁ G₂ : Graph α β} :
    G₁.Inc e = G₂.Inc f ↔ G₁.IsLink e = G₂.IsLink f := by
  constructor <;> rintro h
  · ext x y
    rw [isLink_iff_inc, isLink_iff_inc, h]
  · simp [funext_iff, Inc, h]

/-- `G.IsLoopAt e x` means that both ends of the edge `e` are equal to the vertex `x`. -/
/-
**Graph.IsLoopAt** 是 Mathlib 中的一个定义，位于命名空间 `Graph`。
形式化陈述：IsLoopAt (G : Graph α β) (e : β) (x : α) : Prop
参数：G : Graph α β；e : β；x : α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`G.IsLoopAt e x` means that both ends of the edge `e` are equal to the vertex `x
`.
-/
def IsLoopAt (G : Graph α β) (e : β) (x : α) : Prop := G.IsLink e x x

@[simp]
/-
**Graph.isLink_self_iff** 是 Mathlib 中的一个引理，位于命名空间 `Graph`。
形式化陈述：isLink_self_iff : G.IsLink e x x ↔ G.IsLoopAt e x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma isLink_self_iff : G.IsLink e x x ↔ G.IsLoopAt e x := Iff.rfl
/-
**Graph.IsLoopAt.inc** 是 Mathlib 中的一个定理，位于命名空间 `Graph.IsLoopAt`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {x : α} {e : β} {G : Graph α β}, G.IsLoopA
t e x → G.Inc e x
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Graph.IsLink.inc_left`：∀ {α : Type u_1} {β : Type u_2} {x y : α} {e : β}
 {G : Graph α β}, G.IsLink e x y → G.Inc e x
-/
lemma IsLoopAt.inc (h : G.IsLoopAt e x) : G.Inc e x :=
  IsLink.inc_left h
/-
**Graph.IsLoopAt.eq_of_inc** 是 Mathlib 中的一个定理，位于命名空间 `Graph.IsLoopAt`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {x y : α} {e : β} {G : Graph α β}, G.IsLoo
pAt e x → G.Inc e y → x = y
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Graph.Inc.eq_or_eq_of_isLink`：∀ {α : Type u_1} {β : Type u_2} {x y z : α
} {e : β} {G : Graph α β}, G.Inc e x → G.IsLink e y z → x = y ∨ x = z
-/
lemma IsLoopAt.eq_of_inc (h : G.IsLoopAt e x) (h' : G.Inc e y) : x = y := by
  obtain rfl | rfl := h'.eq_or_eq_of_isLink h <;> rfl

-- Cannot be @[simp] because `x` cannot be inferred by `simp`.
/-
**Graph.IsLoopAt.edge_mem** 是 Mathlib 中的一个定理，位于命名空间 `Graph.IsLoopAt`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {x : α} {e : β} {G : Graph α β}, G.IsLoopA
t e x → e ∈ G.edgeSet
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Graph.Inc.edge_mem`：∀ {α : Type u_1} {β : Type u_2} {x : α} {e : β} {G :
 Graph α β}, G.Inc e x → e ∈ G.edgeSet
· 使用定理 `Graph.IsLoopAt.inc`：∀ {α : Type u_1} {β : Type u_2} {x : α} {e : β} {G :
 Graph α β}, G.IsLoopAt e x → G.Inc e x
-/
lemma IsLoopAt.edge_mem (h : G.IsLoopAt e x) : e ∈ E(G) :=
  h.inc.edge_mem

-- Cannot be @[simp] because `e` cannot be inferred by `simp`.
/-
**Graph.IsLoopAt.vertex_mem** 是 Mathlib 中的一个定理，位于命名空间 `Graph.IsLoopAt`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {x : α} {e : β} {G : Graph α β}, G.IsLoopA
t e x → x ∈ G.vertexSet
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Graph.Inc.vertex_mem`：∀ {α : Type u_1} {β : Type u_2} {x : α} {e : β} {G
 : Graph α β}, G.Inc e x → x ∈ G.vertexSet
· 使用定理 `Graph.IsLoopAt.inc`：∀ {α : Type u_1} {β : Type u_2} {x : α} {e : β} {G :
 Graph α β}, G.IsLoopAt e x → G.Inc e x
-/
lemma IsLoopAt.vertex_mem (h : G.IsLoopAt e x) : x ∈ V(G) :=
  h.inc.vertex_mem

/-- `G.IsNonloopAt e x` means that the vertex `x` is one but not both of the ends of the edge =`e`,
or equivalently that `e` is incident with `x` but not a loop at `x` -
see `Graph.isNonloopAt_iff_inc_not_isLoopAt`. -/
/-
**Graph.IsNonloopAt** 是 Mathlib 中的一个定义，位于命名空间 `Graph`。
形式化陈述：IsNonloopAt (G : Graph α β) (e : β) (x : α) : Prop
参数：G : Graph α β；e : β；x : α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`G.IsNonloopAt e x` means that the vertex `x` is one but not both of the ends of
 the edge =`e`,
or equivalently that `e` is incident with `x` but not a loop at `x` -
see `Graph.isNonloopAt_iff_inc_not_isLoopAt`.
-/
def IsNonloopAt (G : Graph α β) (e : β) (x : α) : Prop := ∃ y ≠ x, G.IsLink e x y
/-
**Graph.IsNonloopAt.inc** 是 Mathlib 中的一个定理，位于命名空间 `Graph.IsNonloopAt`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {x : α} {e : β} {G : Graph α β}, G.IsNonlo
opAt e x → G.Inc e x
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Graph.IsLink.inc_left`：∀ {α : Type u_1} {β : Type u_2} {x y : α} {e : β}
 {G : Graph α β}, G.IsLink e x y → G.Inc e x
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
-/
lemma IsNonloopAt.inc (h : G.IsNonloopAt e x) : G.Inc e x :=
  h.choose_spec.2.inc_left

-- Cannot be @[simp] because `x` cannot be inferred by `simp`.
/-
**Graph.IsNonloopAt.edge_mem** 是 Mathlib 中的一个定理，位于命名空间 `Graph.IsNonloopAt`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {x : α} {e : β} {G : Graph α β}, G.IsNonlo
opAt e x → e ∈ G.edgeSet
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Graph.Inc.edge_mem`：∀ {α : Type u_1} {β : Type u_2} {x : α} {e : β} {G :
 Graph α β}, G.Inc e x → e ∈ G.edgeSet
· 使用定理 `Graph.IsNonloopAt.inc`：∀ {α : Type u_1} {β : Type u_2} {x : α} {e : β} {
G : Graph α β}, G.IsNonloopAt e x → G.Inc e x
-/
lemma IsNonloopAt.edge_mem (h : G.IsNonloopAt e x) : e ∈ E(G) :=
  h.inc.edge_mem

-- Cannot be @[simp] because `e` cannot be inferred by `simp`.
/-
**Graph.IsNonloopAt.vertex_mem** 是 Mathlib 中的一个定理，位于命名空间 `Graph.IsNonloopAt`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {x : α} {e : β} {G : Graph α β}, G.IsNonlo
opAt e x → x ∈ G.vertexSet
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Graph.Inc.vertex_mem`：∀ {α : Type u_1} {β : Type u_2} {x : α} {e : β} {G
 : Graph α β}, G.Inc e x → x ∈ G.vertexSet
· 使用定理 `Graph.IsNonloopAt.inc`：∀ {α : Type u_1} {β : Type u_2} {x : α} {e : β} {
G : Graph α β}, G.IsNonloopAt e x → G.Inc e x
-/
lemma IsNonloopAt.vertex_mem (h : G.IsNonloopAt e x) : x ∈ V(G) :=
  h.inc.vertex_mem
/-
**Graph.IsLoopAt.not_isNonloopAt** 是 Mathlib 中的一个定理，位于命名空间 `Graph.IsLoopAt`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {x : α} {e : β} {G : Graph α β}, G.IsLoopA
t e x → ∀ (y : α), ¬G.IsNonloopAt e y
参数：y : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Graph.IsLoopAt.eq_of_inc`：∀ {α : Type u_1} {β : Type u_2} {x y : α} {e :
 β} {G : Graph α β}, G.IsLoopAt e x → G.Inc e y → x = y
· 使用定理 `Graph.IsLink.inc_right`：∀ {α : Type u_1} {β : Type u_2} {x y : α} {e : β
} {G : Graph α β}, G.IsLink e x y → G.Inc e y
· 使用定理 `Graph.IsLink.inc_left`：∀ {α : Type u_1} {β : Type u_2} {x y : α} {e : β}
 {G : Graph α β}, G.IsLink e x y → G.Inc e x
-/
lemma IsLoopAt.not_isNonloopAt (h : G.IsLoopAt e x) (y : α) : ¬ G.IsNonloopAt e y := by
  rintro ⟨z, hyz, hy⟩
  rw [← h.eq_of_inc hy.inc_left, ← h.eq_of_inc hy.inc_right] at hyz
  exact hyz rfl
/-
**Graph.IsNonloopAt.not_isLoopAt** 是 Mathlib 中的一个定理，位于命名空间 `Graph.IsNonloopAt`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {x : α} {e : β} {G : Graph α β}, G.IsNonlo
opAt e x → ∀ (y : α), ¬G.IsLoopAt e y
参数：y : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Graph.IsLoopAt.not_isNonloopAt`：∀ {α : Type u_1} {β : Type u_2} {x : α} 
{e : β} {G : Graph α β}, G.IsLoopAt e x → ∀ (y : α), ¬G.IsNonloopAt e y
-/
lemma IsNonloopAt.not_isLoopAt (h : G.IsNonloopAt e x) (y : α) : ¬ G.IsLoopAt e y :=
  fun h' ↦ h'.not_isNonloopAt x h
/-
**Graph.isNonloopAt_iff_inc_not_isLoopAt** 是 Mathlib 中的一个引理，位于命名空间 `Graph`。
形式化陈述：isNonloopAt_iff_inc_not_isLoopAt : G.IsNonloopAt e x ↔ G.Inc e x ∧ ¬ G.IsL
oopAt e x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Graph.IsNonloopAt.inc`：∀ {α : Type u_1} {β : Type u_2} {x : α} {e : β} {
G : Graph α β}, G.IsNonloopAt e x → G.Inc e x
· 使用定理 `Graph.IsNonloopAt.not_isLoopAt`：∀ {α : Type u_1} {β : Type u_2} {x : α} 
{e : β} {G : Graph α β}, G.IsNonloopAt e x → ∀ (y : α), ¬G.IsLoopAt e y
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma isNonloopAt_iff_inc_not_isLoopAt : G.IsNonloopAt e x ↔ G.Inc e x ∧ ¬ G.IsLoopAt e x :=
  ⟨fun h ↦ ⟨h.inc, h.not_isLoopAt _⟩, fun ⟨⟨y, hy⟩, hn⟩ ↦ ⟨y, mt (fun h ↦ h ▸ hy) hn, hy⟩⟩
/-
**Graph.isLoopAt_iff_inc_not_isNonloopAt** 是 Mathlib 中的一个引理，位于命名空间 `Graph`。
形式化陈述：isLoopAt_iff_inc_not_isNonloopAt : G.IsLoopAt e x ↔ G.Inc e x ∧ ¬ G.IsNonl
oopAt e x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma isLoopAt_iff_inc_not_isNonloopAt : G.IsLoopAt e x ↔ G.Inc e x ∧ ¬ G.IsNonloopAt e x := by
  simp +contextual [isNonloopAt_iff_inc_not_isLoopAt, iff_def, IsLoopAt.inc]
/-
**Graph.Inc.isLoopAt_or_isNonloopAt** 是 Mathlib 中的一个定理，位于命名空间 `Graph.Inc`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {x : α} {e : β} {G : Graph α β}, G.Inc e x
 → G.IsLoopAt e x ∨ G.IsNonloopAt e x
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
-/
lemma Inc.isLoopAt_or_isNonloopAt (h : G.Inc e x) : G.IsLoopAt e x ∨ G.IsNonloopAt e x := by
  simp [isNonloopAt_iff_inc_not_isLoopAt, h, em]

/-! ### Adjacency -/

/-- `G.Adj x y` means that `G` has an edge whose ends are the vertices `x` and `y`. -/
/-
**Graph.Adj** 是 Mathlib 中的一个定义，位于命名空间 `Graph`。
形式化陈述：Adj (G : Graph α β) (x y : α) : Prop
参数：G : Graph α β；x y : α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`G.Adj x y` means that `G` has an edge whose ends are the vertices `x` and `y`.
-/
def Adj (G : Graph α β) (x y : α) : Prop := ∃ e, G.IsLink e x y

@[symm]
/-
**Graph.Adj.symm** 是 Mathlib 中的一个定理，位于命名空间 `Graph.Adj`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {x y : α} {G : Graph α β}, G.Adj x y → G.A
dj y x
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Graph.IsLink.symm`：∀ {α : Type u_1} {β : Type u_2} {x y : α} {e : β} {G 
: Graph α β}, G.IsLink e x y → G.IsLink e y x
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
-/
protected lemma Adj.symm (h : G.Adj x y) : G.Adj y x :=
  ⟨_, h.choose_spec.symm⟩
/-
**Graph.** 是 Mathlib 中的一个实例，位于命名空间 `Graph`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Std.Symm G.Adj where
  symm _ _ := Adj.symm
/-
**Graph.adj_comm** 是 Mathlib 中的一个引理，位于命名空间 `Graph`。
形式化陈述：adj_comm (x y) : G.Adj x y ↔ G.Adj y x
参数：x y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Graph.Adj.symm`：∀ {α : Type u_1} {β : Type u_2} {x y : α} {G : Graph α β
}, G.Adj x y → G.Adj y x
-/
lemma adj_comm (x y) : G.Adj x y ↔ G.Adj y x :=
  ⟨.symm, .symm⟩

-- Cannot be @[simp] because `y` cannot be inferred by `simp`.
/-
**Graph.Adj.left_mem** 是 Mathlib 中的一个定理，位于命名空间 `Graph.Adj`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {x y : α} {G : Graph α β}, G.Adj x y → x ∈
 G.vertexSet
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Graph.IsLink.left_mem`：∀ {α : Type u_1} {β : Type u_2} {x y : α} {e : β}
 {G : Graph α β}, G.IsLink e x y → x ∈ G.vertexSet
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
-/
lemma Adj.left_mem (h : G.Adj x y) : x ∈ V(G) :=
  h.choose_spec.left_mem

-- Cannot be @[simp] because `x` cannot be inferred by `simp`.
/-
**Graph.Adj.right_mem** 是 Mathlib 中的一个定理，位于命名空间 `Graph.Adj`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {x y : α} {G : Graph α β}, G.Adj x y → y ∈
 G.vertexSet
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Graph.Adj.left_mem`：∀ {α : Type u_1} {β : Type u_2} {x y : α} {G : Graph
 α β}, G.Adj x y → x ∈ G.vertexSet
· 使用定理 `Graph.Adj.symm`：∀ {α : Type u_1} {β : Type u_2} {x y : α} {G : Graph α β
}, G.Adj x y → G.Adj y x
-/
lemma Adj.right_mem (h : G.Adj x y) : y ∈ V(G) :=
  h.symm.left_mem
/-
**Graph.IsLink.adj** 是 Mathlib 中的一个定理，位于命名空间 `Graph.IsLink`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {x y : α} {e : β} {G : Graph α β}, G.IsLin
k e x y → G.Adj x y
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma IsLink.adj (h : G.IsLink e x y) : G.Adj x y :=
  ⟨e, h⟩

/-! ### Extensionality -/

/-- `edgeSet` can be determined using `IsLink`, so the graph constructed from `G.vertexSet` and
`G.IsLink` using any value for `edgeSet` is equal to `G` itself. -/
@[simp]
/-
**Graph.mk_eq_self** 是 Mathlib 中的一个引理，位于命名空间 `Graph`。
形式化陈述：mk_eq_self (G : Graph α β) {E : Set β} (hE : forall e, e in E ↔ exists x y
, G.IsLink e x y) : Graph.mk V(G) G.IsLink E (by simpa [show E = E(G) by simp [S
et.ext_iff, hE, G.edge_mem_iff_exists_isLink]] using G.isLink_symm) (fun _ _ _ _
 _ h h' => h.left_eq_or_eq h') hE (fun _ _ _ => IsLink.left_mem) = G
参数：G : Graph α β；hE : forall e, e in E ↔ exists x y, G.IsLink e x y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Graph.IsLink.left_eq_or_eq`：∀ {α : Type u_1} {β : Type u_2} {x y z w : α
} {e : β} {G : Graph α β}, G.IsLink e x y → G.IsLink e z w → x = z ∨ x = w
· 使用定理 `Graph.IsLink.left_mem`：∀ {α : Type u_1} {β : Type u_2} {x y : α} {e : β}
 {G : Graph α β}, G.IsLink e x y → x ∈ G.vertexSet
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Graph.edge_mem_iff_exists_isLink`：∀ {α : Type u_3} {β : Type u_4} (self 
: Graph α β) (e : β), e ∈ self.edgeSet ↔ ∃ x y, self.IsLink e x y
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True

--- 原说明 ---
`edgeSet` can be determined using `IsLink`, so the graph constructed from `G.ver
texSet` and
`G.IsLink` using any value for `edgeSet` is equal to `G` itself.
-/
lemma mk_eq_self (G : Graph α β) {E : Set β} (hE : ∀ e, e ∈ E ↔ ∃ x y, G.IsLink e x y) :
    Graph.mk V(G) G.IsLink E
    (by simpa [show E = E(G) by simp [Set.ext_iff, hE, G.edge_mem_iff_exists_isLink]]
      using G.isLink_symm)
    (fun _ _ _ _ _ h h' ↦ h.left_eq_or_eq h') hE
    (fun _ _ _ ↦ IsLink.left_mem) = G := by
  obtain rfl : E = E(G) := by simp [Set.ext_iff, hE, G.edge_mem_iff_exists_isLink]
  cases G with | _ _ _ _ _ _ h _ => simp

/-- Two graphs with the same vertex set and binary incidences are equal.
(We use this as the default extensionality lemma rather than adding `@[ext]`
to the definition of `Graph`, so it doesn't require equality of the edge sets.) -/
@[ext]
/-
**Graph.ext** 是 Mathlib 中的一个定理，位于命名空间 `Graph`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {G₁ G₂ : Graph α β},   G₁.vertexSet = G₂.v
ertexSet → (∀ (e : β) (x y : α), G₁.IsLink e x y ↔ G₂.IsLink e x y) → G₁ = G₂
参数：∀ (e : β) (x y : α), G₁.IsLink e x y ↔ G₂.IsLink e x y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Graph.edge_mem_iff_exists_isLink`：∀ {α : Type u_3} {β : Type u_4} (self 
: Graph α β) (e : β), e ∈ self.edgeSet ↔ ∃ x y, self.IsLink e x y
· 使用定理 `Graph.IsLink.left_eq_or_eq`：∀ {α : Type u_1} {β : Type u_2} {x y z w : α
} {e : β} {G : Graph α β}, G.IsLink e x y → G.IsLink e z w → x = z ∨ x = w
· 使用定理 `Graph.IsLink.left_mem`：∀ {α : Type u_1} {β : Type u_2} {x y : α} {e : β}
 {G : Graph α β}, G.IsLink e x y → x ∈ G.vertexSet
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Graph.mk_eq_self`：mk_eq_self (G : Graph α β) {E : Set β} (hE : forall e,
 e in E ↔ exists x y, G.IsLink e x y) : Graph.mk V(G) G.IsLink E (by simpa [show
 E = E…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `Graph.edgeSet_eq_setOfPred_exists_isLink`：edgeSet_eq_setOfPred_exists_is
Link : E(G) = {e | exists x y, G.IsLink e x y}
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g

--- 原说明 ---
Two graphs with the same vertex set and binary incidences are equal.
(We use this as the default extensionality lemma rather than adding `@[ext]`
to the definition of `Graph`, so it doesn't require equality of the edge sets.)
-/
protected lemma ext {G₁ G₂ : Graph α β} (hV : V(G₁) = V(G₂))
    (h : ∀ e x y, G₁.IsLink e x y ↔ G₂.IsLink e x y) : G₁ = G₂ := by
  rw [← G₁.mk_eq_self G₁.edge_mem_iff_exists_isLink, ← G₂.mk_eq_self G₂.edge_mem_iff_exists_isLink]
  convert! rfl using 2
  · exact hV.symm
  · simp [funext_iff, h]
  simp [edgeSet_eq_setOfPred_exists_isLink, h]

/-- Two graphs with the same vertex set and unary incidences are equal. -/
/-
**Graph.ext_inc** 是 Mathlib 中的一个引理，位于命名空间 `Graph`。
形式化陈述：ext_inc {G₁ G₂ : Graph α β} (hV : V(G₁) = V(G₂)) (h : forall e x, G₁.Inc e
 x ↔ G₂.Inc e x) : G₁ = G₂
参数：hV : V(G₁) = V(G₂)；h : forall e x, G₁.Inc e x ↔ G₂.Inc e x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Graph.ext`：∀ {α : Type u_1} {β : Type u_2} {G₁ G₂ : Graph α β},   G₁.ver
texSet = G₂.vertexSet → (∀ (e : β) (x y : α), G₁.IsLink e x y ↔ G₂.IsLink e x y…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
Two graphs with the same vertex set and unary incidences are equal.
-/
lemma ext_inc {G₁ G₂ : Graph α β} (hV : V(G₁) = V(G₂)) (h : ∀ e x, G₁.Inc e x ↔ G₂.Inc e x) :
    G₁ = G₂ :=
  Graph.ext hV fun _ _ _ ↦ by simp_rw [isLink_iff_inc, h]

/-- `Graph.copy` produces a graph equal to `G` but with provided definitional choices
for `vertexSet`, `edgeSet`, and `IsLink`. This is mainly useful for improving
definitional equalities while keeping the same underlying graph. -/
@[simps -isSimp]
/-
**Graph.copy** 是 Mathlib 中的一个定义，位于命名空间 `Graph`。
形式化陈述：copy (G : Graph α β) {vertexSet : Set α} {edgeSet : Set β} {IsLink : β -> 
α -> α -> Prop} (hvertexSet : V(G) = vertexSet) (hedgeSet : E(G) = edgeSet) (hIs
Link : forall e x y, G.IsLink e x y ↔ IsLink e x y) : Graph α β where vertexSet
参数：G : Graph α β；hvertexSet : V(G) = vertexSet；hedgeSet : E(G) = edgeSet；hIsLink
 : forall e x y, G.IsLink e x y ↔ IsLink e x y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Graph.copy` produces a graph equal to `G` but with provided definitional choice
s
for `vertexSet`, `edgeSet`, and `IsLink`. This is mainly useful for improving
definitional equalities while keeping the same underlying graph.
-/
def copy (G : Graph α β) {vertexSet : Set α} {edgeSet : Set β} {IsLink : β → α → α → Prop}
    (hvertexSet : V(G) = vertexSet) (hedgeSet : E(G) = edgeSet)
    (hIsLink : ∀ e x y, G.IsLink e x y ↔ IsLink e x y) : Graph α β where
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
/-
**Graph.copy_eq** 是 Mathlib 中的一个引理，位于命名空间 `Graph`。
形式化陈述：copy_eq (G : Graph α β) {V : Set α} {E : Set β} {IsLink : β -> α -> α -> P
rop} (hV : V(G) = V) (hE : E(G) = E) (h_isLink : forall e x y, G.IsLink e x y ↔ 
IsLink e x y) : G.copy hV hE h_isLink = G
参数：G : Graph α β；hV : V(G) = V；hE : E(G) = E；h_isLink : forall e x y, G.IsLink e
 x y ↔ IsLink e x y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Graph.ext`：∀ {α : Type u_1} {β : Type u_2} {G₁ G₂ : Graph α β},   G₁.ver
texSet = G₂.vertexSet → (∀ (e : β) (x y : α), G₁.IsLink e x y ↔ G₂.IsLink e x y…
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma copy_eq (G : Graph α β) {V : Set α} {E : Set β} {IsLink : β → α → α → Prop}
    (hV : V(G) = V) (hE : E(G) = E) (h_isLink : ∀ e x y, G.IsLink e x y ↔ IsLink e x y) :
    G.copy hV hE h_isLink = G := by
  ext <;> simp_all [copy]

/-! ### Sets of edges or loops incident to a vertex -/

/-- `G.incidenceSet x` is the set of edges incident to `x` in `G`. -/
/-
**Graph.incidenceSet** 是 Mathlib 中的一个定义，位于命名空间 `Graph`。
形式化陈述：incidenceSet (x : α) : Set β
参数：x : α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`G.incidenceSet x` is the set of edges incident to `x` in `G`.
-/
def incidenceSet (x : α) : Set β := {e | G.Inc e x}

@[simp]
/-
**Graph.mem_incidenceSet** 是 Mathlib 中的一个定理，位于命名空间 `Graph`。
形式化陈述：mem_incidenceSet (x : α) (e : β) : e in G.incidenceSet x ↔ G.Inc e x
参数：x : α；e : β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_incidenceSet (x : α) (e : β) : e ∈ G.incidenceSet x ↔ G.Inc e x :=
  Iff.rfl
/-
**Graph.incidenceSet_subset_edgeSet** 是 Mathlib 中的一个定理，位于命名空间 `Graph`。
形式化陈述：incidenceSet_subset_edgeSet (x : α) : G.incidenceSet x subseteq E(G)
参数：x : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Graph.IsLink.edge_mem`：∀ {α : Type u_1} {β : Type u_2} {x y : α} {e : β}
 {G : Graph α β}, G.IsLink e x y → e ∈ G.edgeSet
-/
theorem incidenceSet_subset_edgeSet (x : α) : G.incidenceSet x ⊆ E(G) :=
  fun _ ⟨_, hy⟩ ↦ hy.edge_mem

/-- `G.loopSet x` is the set of loops at `x` in `G`. -/
/-
**Graph.loopSet** 是 Mathlib 中的一个定义，位于命名空间 `Graph`。
形式化陈述：loopSet (x : α) : Set β
参数：x : α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`G.loopSet x` is the set of loops at `x` in `G`.
-/
def loopSet (x : α) : Set β := {e | G.IsLoopAt e x}

@[simp]
/-
**Graph.mem_loopSet** 是 Mathlib 中的一个定理，位于命名空间 `Graph`。
形式化陈述：mem_loopSet (x : α) (e : β) : e in G.loopSet x ↔ G.IsLoopAt e x
参数：x : α；e : β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_loopSet (x : α) (e : β) : e ∈ G.loopSet x ↔ G.IsLoopAt e x :=
  Iff.rfl

/-- The loopSet is included in the incidenceSet. -/
/-
**Graph.loopSet_subset_incidenceSet** 是 Mathlib 中的一个定理，位于命名空间 `Graph`。
形式化陈述：loopSet_subset_incidenceSet (x : α) : G.loopSet x subseteq G.incidenceSet 
x
参数：x : α。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The loopSet is included in the incidenceSet.
-/
theorem loopSet_subset_incidenceSet (x : α) : G.loopSet x ⊆ G.incidenceSet x := fun _ he ↦ ⟨x, he⟩

/-!
### Compatibility of Graphs

We define two graphs to be `Compatible` if for each edge belonging to their shared edge set,
the incidence relation (i.e., which pairs of vertices it links) is the same in both graphs.
-/

/-- Two graphs are compatible if their shared edges have the same ends in both graphs. -/
/-
**Graph.Compatible** 是 Mathlib 中的一个定义，位于命名空间 `Graph`。
形式化陈述：Compatible (G H : Graph α β) : Prop
参数：G H : Graph α β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Two graphs are compatible if their shared edges have the same ends in both graph
s.
-/
def Compatible (G H : Graph α β) : Prop :=
  ∀ ⦃e⦄, e ∈ E(G) → e ∈ E(H) → ∀ x y, G.IsLink e x y ↔ H.IsLink e x y
/-
**Graph.Compatible.isLink_congr** 是 Mathlib 中的一个定理，位于命名空间 `Graph.Compatible`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {e : β} {G H : Graph α β},   e ∈ G.edgeSet
 → e ∈ H.edgeSet → G.Compatible H → ∀ {x y : α}, G.IsLink e x y ↔ H.IsLink e x y
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Compatible.isLink_congr (heG : e ∈ E(G)) (heH : e ∈ E(H)) (h : G.Compatible H) {x y : α} :
    G.IsLink e x y ↔ H.IsLink e x y :=
  h heG heH x y
/-
**Graph.Compatible.refl** 是 Mathlib 中的一个定理，位于命名空间 `Graph.Compatible`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} (G : Graph α β), G.Compatible G
参数：G : Graph α β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma Compatible.refl (G : Graph α β) : G.Compatible G :=
  fun _ _ _ _ _ => .rfl

@[simp]
/-
**Graph.Compatible.rfl** 是 Mathlib 中的一个定理，位于命名空间 `Graph.Compatible`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {G : Graph α β}, G.Compatible G
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Graph.Compatible.refl`：∀ {α : Type u_1} {β : Type u_2} (G : Graph α β), 
G.Compatible G
-/
lemma Compatible.rfl {G : Graph α β} : G.Compatible G := .refl _
/-
**Graph.** 是 Mathlib 中的一个实例，位于命名空间 `Graph`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Std.Refl (Compatible : Graph α β → Graph α β → Prop) where
  refl _ := .rfl

@[symm]
/-
**Graph.Compatible.symm** 是 Mathlib 中的一个定理，位于命名空间 `Graph.Compatible`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {G H : Graph α β}, G.Compatible H → H.Comp
atible G
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
-/
lemma Compatible.symm (h : G.Compatible H) : H.Compatible G :=
  fun _ heH heG x y => (h heG heH x y).symm
/-
**Graph.** 是 Mathlib 中的一个实例，位于命名空间 `Graph`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Std.Symm (Compatible : Graph α β → Graph α β → Prop) where
  symm _ _ := Compatible.symm
/-
**Graph.IsLink.of_compatible** 是 Mathlib 中的一个定理，位于命名空间 `Graph.IsLink`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {x y : α} {e : β} {G H : Graph α β},   G.C
ompatible H → e ∈ H.edgeSet → G.IsLink e x y → H.IsLink e x y
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Graph.IsLink.edge_mem`：∀ {α : Type u_1} {β : Type u_2} {x y : α} {e : β}
 {G : Graph α β}, G.IsLink e x y → e ∈ G.edgeSet
-/
lemma IsLink.of_compatible (hGH : G.Compatible H) (heH : e ∈ E(H)) (h : G.IsLink e x y) :
    H.IsLink e x y :=
  (hGH h.edge_mem heH x y).mp h
/-
**Graph.Compatible.of_disjoint_edgeSet** 是 Mathlib 中的一个定理，位于命名空间 `Graph.Compatib
le`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {G H : Graph α β}, Disjoint G.edgeSet H.ed
geSet → G.Compatible H
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Disjoint.notMem_of_mem_left`：∀ {α : Type u} {s t : Set α}, Disjoint s t 
→ ∀ ⦃a : α⦄, a ∈ s → a ∉ t
-/
lemma Compatible.of_disjoint_edgeSet (h : Disjoint E(G) E(H)) : Compatible G H :=
  fun _ heG heH _ _ ↦ h.notMem_of_mem_left heG heH |>.elim
/-
**Graph.Inc.of_compatible** 是 Mathlib 中的一个定理，位于命名空间 `Graph.Inc`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {x : α} {e : β} {G H : Graph α β},   G.Com
patible H → e ∈ H.edgeSet → G.Inc e x → H.Inc e x
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Graph.IsLink.of_compatible`：∀ {α : Type u_1} {β : Type u_2} {x y : α} {e
 : β} {G H : Graph α β},   G.Compatible H → e ∈ H.edgeSet → G.IsLink e x y → H.I
sLink e x y
-/
lemma Inc.of_compatible (hGH : G.Compatible H) (heH : e ∈ E(H)) (h : G.Inc e x) : H.Inc e x := by
  obtain ⟨y, hy⟩ := h
  exact ⟨y, hy.of_compatible hGH heH⟩
/-
**Graph.IsLoopAt.of_compatible** 是 Mathlib 中的一个定理，位于命名空间 `Graph.IsLoopAt`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {x : α} {e : β} {G H : Graph α β},   G.Com
patible H → e ∈ H.edgeSet → G.IsLoopAt e x → H.IsLoopAt e x
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Graph.IsLink.of_compatible`：∀ {α : Type u_1} {β : Type u_2} {x y : α} {e
 : β} {G H : Graph α β},   G.Compatible H → e ∈ H.edgeSet → G.IsLink e x y → H.I
sLink e x y
-/
lemma IsLoopAt.of_compatible (hGH : G.Compatible H) (heH : e ∈ E(H)) (h : G.IsLoopAt e x) :
    H.IsLoopAt e x :=
  IsLink.of_compatible hGH heH h
/-
**Graph.IsNonloopAt.of_compatible** 是 Mathlib 中的一个定理，位于命名空间 `Graph.IsNonloopAt`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {x : α} {e : β} {G H : Graph α β},   G.Com
patible H → e ∈ H.edgeSet → G.IsNonloopAt e x → H.IsNonloopAt e x
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Graph.IsLink.of_compatible`：∀ {α : Type u_1} {β : Type u_2} {x y : α} {e
 : β} {G H : Graph α β},   G.Compatible H → e ∈ H.edgeSet → G.IsLink e x y → H.I
sLink e x y
-/
lemma IsNonloopAt.of_compatible (hGH : G.Compatible H) (heH : e ∈ E(H)) (h : G.IsNonloopAt e x) :
    H.IsNonloopAt e x := by
  obtain ⟨y, hne, hy⟩ := h
  exact ⟨y, hne, hy.of_compatible hGH heH⟩

/-! ### Graphs with no edges -/

/-- The graph with vertex set `vertexSet` and no edges -/
@[simps (attr := grind =) vertexSet edgeSet]
/-
**Graph.noEdge** 是 Mathlib 中的一个定义，位于命名空间 `Graph`。
形式化陈述：noEdge (vertexSet : Set α) (β : Type*) : Graph α β where vertexSet
参数：vertexSet : Set α；β : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The graph with vertex set `vertexSet` and no edges
-/
def noEdge (vertexSet : Set α) (β : Type*) : Graph α β where
  vertexSet := vertexSet
  edgeSet := ∅
  IsLink _ _ _ := False
  isLink_symm := by simp
  eq_or_eq_of_isLink_of_isLink := by simp
  edge_mem_iff_exists_isLink := by simp
/-
**Graph.noEdge_isLink** 是 Mathlib 中的一个定理，位于命名空间 `Graph`。
形式化陈述：noEdge_isLink (vertexSet : Set α) (β : Type*) (e : β) (x y : α) : (noEdge 
vertexSet β).IsLink e x y ↔ False
参数：vertexSet : Set α；β : Type*；e : β；x y : α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem noEdge_isLink (vertexSet : Set α) (β : Type*) (e : β) (x y : α) :
    (noEdge vertexSet β).IsLink e x y ↔ False := Iff.rfl

variable {vertexSet : Set α} {edgeSet : Set β}
/-
**Graph.edgeSet_eq_empty** 是 Mathlib 中的一个引理，位于命名空间 `Graph`。
形式化陈述：edgeSet_eq_empty : E(G) = ∅ ↔ G = noEdge V(G) β
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Graph.ext`：∀ {α : Type u_1} {β : Type u_2} {G₁ G₂ : Graph α β},   G₁.ver
texSet = G₂.vertexSet → (∀ (e : β) (x y : α), G₁.IsLink e x y ↔ G₂.IsLink e x y…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_false`：∀ (p : Prop), (p ↔ False) = ¬p
· 使用定理 `Graph.IsLink.edge_mem`：∀ {α : Type u_1} {β : Type u_2} {x y : α} {e : β}
 {G : Graph α β}, G.IsLink e x y → e ∈ G.edgeSet
· 使用定理 `Graph.edgeSet_noEdge`：∀ {α : Type u_1} (vertexSet : Set α) (β : Type u_3
), (Graph.noEdge vertexSet β).edgeSet = ∅
-/
lemma edgeSet_eq_empty : E(G) = ∅ ↔ G = noEdge V(G) β := by
  refine ⟨fun h ↦ Graph.ext rfl ?_, fun h ↦ by rw [h, edgeSet_noEdge]⟩
  simp only [noEdge_isLink, iff_false]
  refine fun e x y he ↦ ?_
  have := h ▸ he.edge_mem
  simp at this

/-! ### Graphs with two vertices -/

/-- A graph with exactly two vertices and no loops. -/
@[simps (attr := grind =)]
/-
**Graph.banana** 是 Mathlib 中的一个定义，位于命名空间 `Graph`。
形式化陈述：banana (u v : α) (edgeSet : Set β) : Graph α β where vertexSet
参数：u v : α；edgeSet : Set β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A graph with exactly two vertices and no loops.
-/
def banana (u v : α) (edgeSet : Set β) : Graph α β where
  vertexSet := {u, v}
  edgeSet := edgeSet
  IsLink e x y := e ∈ edgeSet ∧ ((x = u ∧ y = v) ∨ (x = v ∧ y = u))
  isLink_symm := by aesop (add simp symm_def)
  eq_or_eq_of_isLink_of_isLink := by aesop
  edge_mem_iff_exists_isLink := by aesop

@[simp]
/-
**Graph.banana_inc** 是 Mathlib 中的一个引理，位于命名空间 `Graph`。
形式化陈述：banana_inc : (banana u v edgeSet).Inc e x ↔ e in edgeSet ∧ (x = u ∨ x = v)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Graph.banana_isLink`：∀ {α : Type u_1} {β : Type u_2} (u v : α) (edgeSet 
: Set β) (e : β) (x y : α),   (Graph.banana u v edgeSet).IsLink e x y = (e ∈ edg
eSet ∧ (x…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
-/
lemma banana_inc : (banana u v edgeSet).Inc e x ↔ e ∈ edgeSet ∧ (x = u ∨ x = v) := by
  simp only [Inc, banana_isLink, exists_and_left, and_congr_right_iff]
  aesop
/-
**Graph.banana_comm** 是 Mathlib 中的一个引理，位于命名空间 `Graph`。
形式化陈述：banana_comm (u v : α) (edgeSet : Set β) : banana u v edgeSet = banana v u 
edgeSet
参数：u v : α；edgeSet : Set β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Graph.ext_inc`：ext_inc {G₁ G₂ : Graph α β} (hV : V(G₁) = V(G₂)) (h : for
all e x, G₁.Inc e x ↔ G₂.Inc e x) : G₁ = G₂
· 使用定理 `Set.pair_comm`：pair_comm (a b : α) : ({a, b} : Set α) = {b, a}
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma banana_comm (u v : α) (edgeSet : Set β) : banana u v edgeSet = banana v u edgeSet :=
  Graph.ext_inc (pair_comm ..) <| by simp [or_comm]

@[simp]
/-
**Graph.banana_isNonloopAt** 是 Mathlib 中的一个引理，位于命名空间 `Graph`。
形式化陈述：banana_isNonloopAt : (banana u v edgeSet).IsNonloopAt e x ↔ e in edgeSet ∧
 (x = u ∨ x = v) ∧ u != v
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Graph.banana_isLink`：∀ {α : Type u_1} {β : Type u_2} (u v : α) (edgeSet 
: Set β) (e : β) (x y : α),   (Graph.banana u v edgeSet).IsLink e x y = (e ∈ edg
eSet ∧ (x…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Aesop.BuiltinRules.not_intro`：∀ {P : Prop}, (P → False) → ¬P
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
-/
lemma banana_isNonloopAt :
    (banana u v edgeSet).IsNonloopAt e x ↔ e ∈ edgeSet ∧ (x = u ∨ x = v) ∧ u ≠ v := by
  simp_rw [isNonloopAt_iff_inc_not_isLoopAt, ← isLink_self_iff, banana_isLink, banana_inc]
  aesop

@[simp]
/-
**Graph.banana_isLoopAt** 是 Mathlib 中的一个引理，位于命名空间 `Graph`。
形式化陈述：banana_isLoopAt : (banana u v edgeSet).IsLoopAt e x ↔ e in edgeSet ∧ x = u
 ∧ u = v
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Graph.banana_isLink`：∀ {α : Type u_1} {β : Type u_2} (u v : α) (edgeSet 
: Set β) (e : β) (x y : α),   (Graph.banana u v edgeSet).IsLink e x y = (e ∈ edg
eSet ∧ (x…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
-/
lemma banana_isLoopAt : (banana u v edgeSet).IsLoopAt e x ↔ e ∈ edgeSet ∧ x = u ∧ u = v := by
  simp only [← isLink_self_iff, banana_isLink, and_congr_right_iff]
  aesop

@[simp]
/-
**Graph.banana_adj** 是 Mathlib 中的一个引理，位于命名空间 `Graph`。
形式化陈述：banana_adj : (banana u v edgeSet).Adj x y ↔ edgeSet.Nonempty ∧ s(x, y) = s
(u, v)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Graph.banana_isLink`：∀ {α : Type u_1} {β : Type u_2} (u v : α) (edgeSet 
: Set β) (e : β) (x y : α),   (Graph.banana u v edgeSet).IsLink e x y = (e ∈ edg
eSet ∧ (x…
· 使用定理 `Prod.mk.injEq`：∀ {α : Type u} {β : Type v} (fst : α) (snd : β) (fst_1 : 
α) (snd_1 : β),   ((fst, snd) = (fst_1, snd_1)) = (fst = fst_1 ∧ snd = snd_1)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma banana_adj : (banana u v edgeSet).Adj x y ↔ edgeSet.Nonempty ∧ s(x, y) = s(u, v) := by
  simp only [Adj, banana_isLink, exists_and_right, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq,
    Prod.swap_prod_mk, and_congr_left_iff]
  exact fun _ ↦ Iff.rfl

@[simp]
/-
**Graph.banana_empty** 是 Mathlib 中的一个引理，位于命名空间 `Graph`。
形式化陈述：banana_empty : banana u v ∅ = Graph.noEdge {u, v} β
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Graph.ext`：∀ {α : Type u_1} {β : Type u_2} {G₁ G₂ : Graph α β},   G₁.ver
texSet = G₂.vertexSet → (∀ (e : β) (x y : α), G₁.IsLink e x y ↔ G₂.IsLink e x y…
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Graph.vertexSet_banana`：∀ {α : Type u_1} {β : Type u_2} (u v : α) (edgeS
et : Set β), (Graph.banana u v edgeSet).vertexSet = {u, v}
· 使用定理 `Graph.vertexSet_noEdge`：∀ {α : Type u_1} (vertexSet : Set α) (β : Type u
_3), (Graph.noEdge vertexSet β).vertexSet = vertexSet
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Graph.edgeSet_banana`：∀ {α : Type u_1} {β : Type u_2} (u v : α) (edgeSet
 : Set β), (Graph.banana u v edgeSet).edgeSet = edgeSet
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Graph.edgeSet_noEdge`：∀ {α : Type u_1} (vertexSet : Set α) (β : Type u_3
), (Graph.noEdge vertexSet β).edgeSet = ∅
-/
lemma banana_empty : banana u v ∅ = Graph.noEdge {u, v} β := by
  ext <;> simp

/-! ### Graphs with one vertex  -/

/-- A graph with one vertex and loops at that vertex. This is an abbreviation for the special case
  of `banana` where the two vertices are the same. Most lemmas about `bouquet` should instead be
  proved using `banana` instead. -/
/-
**Graph.bouquet** 是 Mathlib 中的一个缩写定义，位于命名空间 `Graph`。
形式化陈述：bouquet (v : α) (edgeSet : Set β) : Graph α β
参数：v : α；edgeSet : Set β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A graph with one vertex and loops at that vertex. This is an abbreviation for th
e special case
  of `banana` where the two vertices are the same. Most lemmas about `bouquet` s
hould instead be
  proved using `banana` instead.
-/
abbrev bouquet (v : α) (edgeSet : Set β) : Graph α β :=
  banana v v edgeSet
/-
**Graph.vertexSet_bouquet** 是 Mathlib 中的一个引理，位于命名空间 `Graph`。
形式化陈述：vertexSet_bouquet (v : α) (edgeSet : Set β) : V(bouquet v edgeSet) = {v}
参数：v : α；edgeSet : Set β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Graph.vertexSet_banana`：∀ {α : Type u_1} {β : Type u_2} (u v : α) (edgeS
et : Set β), (Graph.banana u v edgeSet).vertexSet = {u, v}
· 使用定理 `Set.insert_eq_of_mem`：insert_eq_of_mem {a : α} {s : Set α} (h : a in s) 
: insert a s = s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma vertexSet_bouquet (v : α) (edgeSet : Set β) : V(bouquet v edgeSet) = {v} := by simp

@[deprecated (since := "2026-04-09")] alias bouquet_vertexSet := vertexSet_bouquet
/-
**Graph.bouquet_isLink** 是 Mathlib 中的一个引理，位于命名空间 `Graph`。
形式化陈述：bouquet_isLink (v : α) (edgeSet : Set β) : (bouquet v edgeSet).IsLink e x 
y ↔ e in edgeSet ∧ x = v ∧ y = v
参数：v : α；edgeSet : Set β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Graph.banana_isLink`：∀ {α : Type u_1} {β : Type u_2} (u v : α) (edgeSet 
: Set β) (e : β) (x y : α),   (Graph.banana u v edgeSet).IsLink e x y = (e ∈ edg
eSet ∧ (x…
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma bouquet_isLink (v : α) (edgeSet : Set β) :
    (bouquet v edgeSet).IsLink e x y ↔ e ∈ edgeSet ∧ x = v ∧ y = v := by simp
/-
**Graph.bouquet_inc** 是 Mathlib 中的一个引理，位于命名空间 `Graph`。
形式化陈述：bouquet_inc (v : α) (edgeSet : Set β) : (bouquet v edgeSet).Inc e x ↔ e in
 edgeSet ∧ x = v
参数：v : α；edgeSet : Set β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma bouquet_inc (v : α) (edgeSet : Set β) :
    (bouquet v edgeSet).Inc e x ↔ e ∈ edgeSet ∧ x = v := by simp
/-
**Graph.bouquet_adj** 是 Mathlib 中的一个引理，位于命名空间 `Graph`。
形式化陈述：bouquet_adj (v : α) (edgeSet : Set β) : (bouquet v edgeSet).Adj x y ↔ edge
Set.Nonempty ∧ x = v ∧ y = v
参数：v : α；edgeSet : Set β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Prod.mk.injEq`：∀ {α : Type u} {β : Type v} (fst : α) (snd : β) (fst_1 : 
α) (snd_1 : β),   ((fst, snd) = (fst_1, snd_1)) = (fst = fst_1 ∧ snd = snd_1)
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma bouquet_adj (v : α) (edgeSet : Set β) :
    (bouquet v edgeSet).Adj x y ↔ edgeSet.Nonempty ∧ x = v ∧ y = v := by simp
/-
**Graph.bouquet_isLoopAt** 是 Mathlib 中的一个引理，位于命名空间 `Graph`。
形式化陈述：bouquet_isLoopAt (v : α) (edgeSet : Set β) : (bouquet v edgeSet).IsLoopAt 
e x ↔ e in edgeSet ∧ x = v
参数：v : α；edgeSet : Set β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma bouquet_isLoopAt (v : α) (edgeSet : Set β) :
    (bouquet v edgeSet).IsLoopAt e x ↔ e ∈ edgeSet ∧ x = v := by simp
/-
**Graph.not_isNonloopAt_bouquet** 是 Mathlib 中的一个引理，位于命名空间 `Graph`。
形式化陈述：not_isNonloopAt_bouquet : ¬ (bouquet v edgeSet).IsNonloopAt e x
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Graph.banana_isLink`：∀ {α : Type u_1} {β : Type u_2} (u v : α) (edgeSet 
: Set β) (e : β) (x y : α),   (Graph.banana u v edgeSet).IsLink e x y = (e ∈ edg
eSet ∧ (x…
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `Exists.elim`：∀ {α : Sort u} {p : α → Prop} {b : Prop}, (∃ x, p x) → (∀ (
a : α), p a → b) → b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma not_isNonloopAt_bouquet : ¬ (bouquet v edgeSet).IsNonloopAt e x := by
  simp +contextual [IsNonloopAt, eq_comm]

/-- Every graph on just one vertex is a bouquet on that vertex. -/
/-
**Graph.eq_bouquet_of_subsingleton** 是 Mathlib 中的一个引理，位于命名空间 `Graph`。
形式化陈述：eq_bouquet_of_subsingleton (hv : v in V(G)) (hss : V(G).Subsingleton) : G 
= bouquet v E(G)
参数：hv : v in V(G)；hss : V(G).Subsingleton。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subsingleton.eq_singleton_of_mem`：∀ {α : Type u} {s : Set α}, s.Subs
ingleton → ∀ {x : α}, x ∈ s → s = {x}
· 使用引理 `Graph.ext_inc`：ext_inc {G₁ G₂ : Graph α β} (hV : V(G₁) = V(G₂)) (h : for
all e x, G₁.Inc e x ↔ G₂.Inc e x) : G₁ = G₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Graph.vertexSet_banana`：∀ {α : Type u_1} {β : Type u_2} (u v : α) (edgeS
et : Set β), (Graph.banana u v edgeSet).vertexSet = {u, v}
· 使用定理 `Set.insert_eq_of_mem`：insert_eq_of_mem {a : α} {s : Set α} (h : a in s) 
: insert a s = s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Graph.Inc.edge_mem`：∀ {α : Type u_1} {β : Type u_2} {x : α} {e : β} {G :
 Graph α β}, G.Inc e x → e ∈ G.edgeSet
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Graph.Inc.vertex_mem`：∀ {α : Type u_1} {β : Type u_2} {x : α} {e : β} {G
 : Graph α β}, G.Inc e x → x ∈ G.vertexSet
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用引理 `Graph.exists_isLink_of_mem_edgeSet`：exists_isLink_of_mem_edgeSet (h : e 
in E(G)) : exists x y, G.IsLink e x y
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Graph.IsLink.left_mem`：∀ {α : Type u_1} {β : Type u_2} {x y : α} {e : β}
 {G : Graph α β}, G.IsLink e x y → x ∈ G.vertexSet
· 使用定理 `Graph.IsLink.inc_left`：∀ {α : Type u_1} {β : Type u_2} {x y : α} {e : β}
 {G : Graph α β}, G.IsLink e x y → G.Inc e x

--- 原说明 ---
Every graph on just one vertex is a bouquet on that vertex.
-/
lemma eq_bouquet_of_subsingleton (hv : v ∈ V(G)) (hss : V(G).Subsingleton) :
    G = bouquet v E(G) := by
  have hrw := hss.eq_singleton_of_mem hv
  refine Graph.ext_inc (by simpa) fun e x ↦ ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · simp [← mem_singleton_iff, ← hrw, h.edge_mem, h.vertex_mem]
  simp only [bouquet_inc] at h
  obtain ⟨z, w, hzw⟩ := exists_isLink_of_mem_edgeSet h.1
  rw [h.2, ← show z = v from (show z ∈ {v} from hrw ▸ hzw.left_mem)]
  exact hzw.inc_left
/-
**Graph.eq_bouquet_iff** 是 Mathlib 中的一个引理，位于命名空间 `Graph`。
形式化陈述：eq_bouquet_iff : G = bouquet v E(G) ↔ V(G) = {v}
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Graph.vertexSet_bouquet`：vertexSet_bouquet (v : α) (edgeSet : Set β) : V
(bouquet v edgeSet) = {v}
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Graph.eq_bouquet_of_subsingleton`：eq_bouquet_of_subsingleton (hv : v in 
V(G)) (hss : V(G).Subsingleton) : G = bouquet v E(G)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma eq_bouquet_iff : G = bouquet v E(G) ↔ V(G) = {v} :=
  ⟨fun h ↦ h ▸ vertexSet_bouquet v _,
    fun h ↦ eq_bouquet_of_subsingleton (by simp [h]) (by simp [h])⟩

/-- Every graph on just one vertex is a bouquet on that vertex. -/
/-
**Graph.exists_eq_bouquet** 是 Mathlib 中的一个引理，位于命名空间 `Graph`。
形式化陈述：exists_eq_bouquet (hne : V(G).Nonempty) (hss : V(G).Subsingleton) : exists
 x F, G = bouquet x F
参数：hne : V(G).Nonempty；hss : V(G).Subsingleton。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Graph.eq_bouquet_of_subsingleton`：eq_bouquet_of_subsingleton (hv : v in 
V(G)) (hss : V(G).Subsingleton) : G = bouquet v E(G)
· 使用定理 `Set.Nonempty.some_mem`：∀ {α : Type u} {s : Set α} (h : s.Nonempty), h.so
me ∈ s

--- 原说明 ---
Every graph on just one vertex is a bouquet on that vertex.
-/
lemma exists_eq_bouquet (hne : V(G).Nonempty) (hss : V(G).Subsingleton) : ∃ x F, G = bouquet x F :=
  ⟨_, _, eq_bouquet_of_subsingleton hne.some_mem hss⟩
/-
**Graph.bouquet_empty** 是 Mathlib 中的一个引理，位于命名空间 `Graph`。
形式化陈述：bouquet_empty (v : α) : bouquet v ∅ = noEdge {v} β
参数：v : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Graph.banana_empty`：banana_empty : banana u v ∅ = Graph.noEdge {u, v} β
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Set.insert_eq_of_mem`：insert_eq_of_mem {a : α} {s : Set α} (h : a in s) 
: insert a s = s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma bouquet_empty (v : α) : bouquet v ∅ = noEdge {v} β := by simp

end Graph

