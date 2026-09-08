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
    aesop $c*
      (config := { introsTransparency? := some .default, terminal := true })
      (rule_sets := [$(Lean.mkIdent `SimpleGraph):ident]))

/--
Use `aesop_graph?` to pass along a `Try this` suggestion when using `aesop_graph`
-/
macro (name := aesop_graph?) "aesop_graph?" c:Aesop.tactic_clause* : tactic =>
  `(tactic|
    aesop? $c*
      (config := { introsTransparency? := some .default, terminal := true })
      (rule_sets := [$(Lean.mkIdent `SimpleGraph):ident]))

/--
A variant of `aesop_graph` which does not fail if it is unable to solve the goal.
Use this only for exploration! Nonterminal Aesop is even worse than nonterminal `simp`.
-/
macro (name := aesop_graph_nonterminal) "aesop_graph_nonterminal" c:Aesop.tactic_clause* : tactic =>
  `(tactic|
    aesop $c*
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
/-
**SimpleGraph** 是 Mathlib 中的一个结构，位于命名空间 ``。
形式化陈述：SimpleGraph (V : Type u) where /-- The adjacency relation of a simple grap
h. -/ Adj : V -> V -> Prop symm : Std.Symm Adj
参数：V : Type u。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A simple graph is an irreflexive symmetric relation `Adj` on a vertex type `V`.
The relation describes which pairs of vertices are adjacent.
There is exactly one edge for every pair of adjacent vertices;
see `SimpleGraph.edgeSet` for the corresponding edge set.
-/
structure SimpleGraph (V : Type u) where
  /-- The adjacency relation of a simple graph. -/
  Adj : V → V → Prop
  symm : Std.Symm Adj := by aesop_graph
  loopless : Std.Irrefl Adj := by aesop_graph

initialize_simps_projections SimpleGraph (Adj → adj)

set_option backward.isDefEq.respectTransparency false in
/-- Constructor for simple graphs using a symmetric irreflexive Boolean function. -/
@[simps]
/-
**SimpleGraph.mk'** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：SimpleGraph.mk' {V : Type u} : {adj : V -> V -> Bool // (forall x y, adj x
 y = adj y x) ∧ (forall x, ¬ adj x x)} ↪ SimpleGraph V where toFun x
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructor for simple graphs using a symmetric irreflexive Boolean function.
-/
def SimpleGraph.mk' {V : Type u} :
    {adj : V → V → Bool // (∀ x y, adj x y = adj y x) ∧ (∀ x, ¬ adj x x)} ↪ SimpleGraph V where
  toFun x := ⟨fun v w ↦ x.1 v w, ⟨fun v w ↦ by simp [x.2.1]⟩, ⟨fun v ↦ by simp [x.2.2]⟩⟩
  inj' := by
    rintro ⟨adj, _⟩ ⟨adj', _⟩
    simp only [mk.injEq, Subtype.mk.injEq]
    intro h
    funext v w
    simpa [Bool.coe_iff_coe] using congr_fun₂ h v w

/-- We can enumerate simple graphs by enumerating all functions `V → V → Bool`
and filtering on whether they are symmetric and irreflexive. -/
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We can enumerate simple graphs by enumerating all functions `V → V → Bool`
and filtering on whether they are symmetric and irreflexive.
-/
instance {V : Type u} [Fintype V] [DecidableEq V] : Fintype (SimpleGraph V) where
  elems := Finset.univ.map SimpleGraph.mk'
  complete := by
    classical
    rintro ⟨Adj, hs, hi⟩
    simp only [mem_map, mem_univ, true_and, Subtype.exists, Bool.not_eq_true]
    refine ⟨fun v w ↦ Adj v w, ⟨?_, ?_⟩, ?_⟩
    · simp [hs.iff]
    · intro v; simp [hi.irrefl v]
    · ext
      simp

/-- There are finitely many simple graphs on a given finite type. -/
/-
**SimpleGraph.instFinite** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：SimpleGraph.instFinite {V : Type u} [Finite V] : Finite (SimpleGraph V)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_injective`：Finite.of_injective {α β : Sort*} [Finite β] (f : α
 -> β) (H : Injective f) : Finite α
· 使用定理 `SimpleGraph.ext`：∀ {V : Type u} {x y : SimpleGraph V}, x.Adj = y.Adj → x
 = y

--- 原说明 ---
There are finitely many simple graphs on a given finite type.
-/
instance SimpleGraph.instFinite {V : Type u} [Finite V] : Finite (SimpleGraph V) :=
  .of_injective SimpleGraph.Adj fun _ _ ↦ SimpleGraph.ext

/-- Construct the simple graph induced by the given relation. It
symmetrizes the relation and makes it irreflexive. -/
/-
**SimpleGraph.fromRel** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：SimpleGraph.fromRel {V : Type u} (r : V -> V -> Prop) : SimpleGraph V wher
e Adj a b
参数：r : V -> V -> Prop。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct the simple graph induced by the given relation. It
symmetrizes the relation and makes it irreflexive.
-/
def SimpleGraph.fromRel {V : Type u} (r : V → V → Prop) : SimpleGraph V where
  Adj a b := a ≠ b ∧ (r a b ∨ r b a)

@[simp]
/-
**SimpleGraph.fromRel_adj** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：SimpleGraph.fromRel_adj {V : Type u} (r : V -> V -> Prop) (v w : V) : (Sim
pleGraph.fromRel r).Adj v w ↔ v != w ∧ (r v w ∨ r w v)
参数：r : V -> V -> Prop；v w : V。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem SimpleGraph.fromRel_adj {V : Type u} (r : V → V → Prop) (v w : V) :
    (SimpleGraph.fromRel r).Adj v w ↔ v ≠ w ∧ (r v w ∨ r w v) :=
  Iff.rfl

attribute [aesop safe (rule_sets := [SimpleGraph])] Ne.symm
attribute [aesop safe (rule_sets := [SimpleGraph])] Ne.irrefl
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {V : Type u} [DecidableEq V] (r : V → V → Prop)
    [DecidableRel r] : DecidableRel (SimpleGraph.fromRel r).Adj :=
  inferInstanceAs (DecidableRel fun a b ↦ a ≠ b ∧ (r a b ∨ r b a))

/-- Two vertices are adjacent in the complete bipartite graph on two vertex types
if and only if they are not from the same side.
Any bipartite graph may be regarded as a subgraph of one of these. -/
@[simps]
/-
**completeBipartiteGraph** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：completeBipartiteGraph (V W : Type*) : SimpleGraph (V oplus W) where Adj v
 w
参数：V W : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Two vertices are adjacent in the complete bipartite graph on two vertex types
if and only if they are not from the same side.
Any bipartite graph may be regarded as a subgraph of one of these.
-/
def completeBipartiteGraph (V W : Type*) : SimpleGraph (V ⊕ W) where
  Adj v w := v.isLeft ∧ w.isRight ∨ v.isRight ∧ w.isLeft

namespace SimpleGraph

variable {ι : Sort*} {V : Type u} (G H : SimpleGraph V) {a b c u v w : V} {e : Sym2 V}

@[simp]
/-
**SimpleGraph.irrefl** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：∀ {V : Type u} (G : SimpleGraph V) {v : V}, ¬G.Adj v v
参数：G : SimpleGraph V。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Std.Irrefl.irrefl`：∀ {α : Sort u} {r : α → α → Prop} [self : Std.Irrefl 
r] (a : α), ¬r a a
· 使用定理 `SimpleGraph.loopless`：∀ {V : Type u} (self : SimpleGraph V), Std.Irrefl 
self.Adj
-/
protected theorem irrefl {v : V} : ¬G.Adj v v :=
  G.loopless.irrefl v
/-
**SimpleGraph.adj_comm** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：adj_comm (u v : V) : G.Adj u v ↔ G.Adj v u
参数：u v : V。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Std.Symm.iff`：∀ {α : Type u_1} {r : α → α → Prop} [Std.Symm r] (x y : α)
, r x y ↔ r y x
· 使用定理 `SimpleGraph.symm`：∀ {V : Type u} (self : SimpleGraph V), Std.Symm self.A
dj
-/
theorem adj_comm (u v : V) : G.Adj u v ↔ G.Adj v u :=
  G.symm.iff u v

@[symm]
/-
**SimpleGraph.adj_symm** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：adj_symm (h : G.Adj u v) : G.Adj v u
参数：h : G.Adj u v。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Std.Symm.symm`：∀ {α : Sort u} {r : α → α → Prop} [self : Std.Symm r] (a 
b : α), r a b → r b a
· 使用定理 `SimpleGraph.symm`：∀ {V : Type u} (self : SimpleGraph V), Std.Symm self.A
dj
-/
theorem adj_symm (h : G.Adj u v) : G.Adj v u :=
  G.symm.symm u v h
/-
**SimpleGraph.Adj.symm** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Adj`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} {u v : V}, G.Adj u v → G.Adj v u
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.adj_symm`：adj_symm (h : G.Adj u v) : G.Adj v u
-/
theorem Adj.symm {G : SimpleGraph V} {u v : V} (h : G.Adj u v) : G.Adj v u :=
  G.adj_symm h
/-
**SimpleGraph.ne_of_adj** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：ne_of_adj (h : G.Adj a b) : a != b
参数：h : G.Adj a b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.irrefl`：∀ {V : Type u} (G : SimpleGraph V) {v : V}, ¬G.Adj v
 v
-/
theorem ne_of_adj (h : G.Adj a b) : a ≠ b := by
  rintro rfl
  exact G.irrefl h
/-
**SimpleGraph.Adj.ne** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Adj`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} {a b : V}, G.Adj a b → a ≠ b
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.ne_of_adj`：ne_of_adj (h : G.Adj a b) : a != b
-/
protected theorem Adj.ne {G : SimpleGraph V} {a b : V} (h : G.Adj a b) : a ≠ b :=
  G.ne_of_adj h
/-
**SimpleGraph.Adj.ne'** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Adj`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} {a b : V}, G.Adj a b → b ≠ a
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `SimpleGraph.Adj.ne`：∀ {V : Type u} {G : SimpleGraph V} {a b : V}, G.Adj 
a b → a ≠ b
-/
protected theorem Adj.ne' {G : SimpleGraph V} {a b : V} (h : G.Adj a b) : b ≠ a :=
  h.ne.symm
/-
**SimpleGraph.ne_of_adj_of_not_adj** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：ne_of_adj_of_not_adj {v w x : V} (h : G.Adj v x) (hn : ¬G.Adj w x) : v != 
w
参数：h : G.Adj v x；hn : ¬G.Adj w x。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ne_of_adj_of_not_adj {v w x : V} (h : G.Adj v x) (hn : ¬G.Adj w x) : v ≠ w := fun h' =>
  hn (h' ▸ h)
/-
**SimpleGraph.adj_injective** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：adj_injective : Injective (Adj : SimpleGraph V -> V -> V -> Prop)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.ext`：∀ {V : Type u} {x y : SimpleGraph V}, x.Adj = y.Adj → x
 = y
-/
theorem adj_injective : Injective (Adj : SimpleGraph V → V → V → Prop) :=
  fun _ _ => SimpleGraph.ext

@[simp]
/-
**SimpleGraph.adj_inj** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：adj_inj {G H : SimpleGraph V} : G.Adj = H.Adj ↔ G = H
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `SimpleGraph.adj_injective`：adj_injective : Injective (Adj : SimpleGraph 
V -> V -> V -> Prop)
-/
theorem adj_inj {G H : SimpleGraph V} : G.Adj = H.Adj ↔ G = H :=
  adj_injective.eq_iff
/-
**SimpleGraph.adj_congr_of_sym2** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：adj_congr_of_sym2 {u v w x : V} (h : s(u, v) = s(w, x)) : G.Adj u v ↔ G.Ad
j w x
参数：h : s(u, v) = s(w, x)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Prod.mk.injEq`：∀ {α : Type u} {β : Type v} (fst : α) (snd : β) (fst_1 : 
α) (snd_1 : β),   ((fst, snd) = (fst_1, snd_1)) = (fst = fst_1 ∧ snd = snd_1)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `SimpleGraph.adj_comm`：adj_comm (u v : V) : G.Adj u v ↔ G.Adj v u
-/
theorem adj_congr_of_sym2 {u v w x : V} (h : s(u, v) = s(w, x)) : G.Adj u v ↔ G.Adj w x := by
  simp only [Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk] at h
  rcases h with hl | hr
  · rw [hl.1, hl.2]
  · rw [hr.1, hr.2, adj_comm]
/-
**SimpleGraph.symm_adj** 是 Mathlib 中的一个实例，位于命名空间 `SimpleGraph`。
形式化陈述：symm_adj (f : ι -> V) : Std.Symm fun i j => G.Adj (f i) (f j) where symm _
 _
参数：f : ι -> V。
该定义给出了一等式。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Adj.symm`：∀ {V : Type u} {G : SimpleGraph V} {u v : V}, G.Ad
j u v → G.Adj v u
-/
instance symm_adj (f : ι → V) : Std.Symm fun i j ↦ G.Adj (f i) (f j) where symm _ _ := .symm

section Order

/-- The relation that one `SimpleGraph` is a subgraph of another.
Note that this should be spelled `≤`. -/
@[deprecated "use `≤` instead" (since := "2026-03-25")]
/-
**SimpleGraph.IsSubgraph** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph`。
形式化陈述：IsSubgraph (x y : SimpleGraph V) : Prop
参数：x y : SimpleGraph V。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The relation that one `SimpleGraph` is a subgraph of another.
Note that this should be spelled `≤`.
-/
def IsSubgraph (x y : SimpleGraph V) : Prop :=
  ∀ ⦃v w : V⦄, x.Adj v w → y.Adj v w

/-- For graphs `G`, `H`, `G ≤ H` iff `∀ a b, G.Adj a b → H.Adj a b`. -/
/-
**SimpleGraph.** 是 Mathlib 中的一个实例，位于命名空间 `SimpleGraph`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For graphs `G`, `H`, `G ≤ H` iff `∀ a b, G.Adj a b → H.Adj a b`.
-/
instance : LE (SimpleGraph V) where
  le x y := ∀ ⦃v w : V⦄, x.Adj v w → y.Adj v w
/-
**SimpleGraph.le_iff_adj** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
形式化陈述：le_iff_adj {G H : SimpleGraph V} : G <= H ↔ forall v w, G.Adj v w -> H.Adj
 v w
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma le_iff_adj {G H : SimpleGraph V} : G ≤ H ↔ ∀ v w, G.Adj v w → H.Adj v w := .rfl

/-- The supremum of two graphs `x ⊔ y` has edges where either `x` or `y` have edges. -/
/-
**SimpleGraph.** 是 Mathlib 中的一个实例，位于命名空间 `SimpleGraph`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The supremum of two graphs `x ⊔ y` has edges where either `x` or `y` have edges.
-/
instance : Max (SimpleGraph V) where
  max x y :=
    { Adj := x.Adj ⊔ y.Adj
      symm.symm v w h := by rwa [Pi.sup_apply, Pi.sup_apply, x.adj_comm, y.adj_comm] }

@[simp, grind =]
/-
**SimpleGraph.sup_adj** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：sup_adj (x y : SimpleGraph V) (v w : V) : (x ⊔ y).Adj v w ↔ x.Adj v w ∨ y.
Adj v w
参数：x y : SimpleGraph V；v w : V。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem sup_adj (x y : SimpleGraph V) (v w : V) : (x ⊔ y).Adj v w ↔ x.Adj v w ∨ y.Adj v w :=
  Iff.rfl

/-- The infimum of two graphs `x ⊓ y` has edges where both `x` and `y` have edges. -/
/-
**SimpleGraph.** 是 Mathlib 中的一个实例，位于命名空间 `SimpleGraph`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The infimum of two graphs `x ⊓ y` has edges where both `x` and `y` have edges.
-/
instance : Min (SimpleGraph V) where
  min x y :=
    { Adj := x.Adj ⊓ y.Adj
      symm.symm v w h := by rwa [Pi.inf_apply, Pi.inf_apply, x.adj_comm, y.adj_comm] }

@[simp]
/-
**SimpleGraph.inf_adj** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：inf_adj (x y : SimpleGraph V) (v w : V) : (x ⊓ y).Adj v w ↔ x.Adj v w ∧ y.
Adj v w
参数：x y : SimpleGraph V；v w : V。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem inf_adj (x y : SimpleGraph V) (v w : V) : (x ⊓ y).Adj v w ↔ x.Adj v w ∧ y.Adj v w :=
  Iff.rfl

/-- We define `Gᶜ` to be the `SimpleGraph V` such that no two adjacent vertices in `G`
are adjacent in the complement, and every nonadjacent pair of vertices is adjacent
(still ensuring that vertices are not adjacent to themselves). -/
/-
**SimpleGraph.** 是 Mathlib 中的一个实例，位于命名空间 `SimpleGraph`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We define `Gᶜ` to be the `SimpleGraph V` such that no two adjacent vertices in `
G`
are adjacent in the complement, and every nonadjacent pair of vertices is adjace
nt
(still ensuring that vertices are not adjacent to themselves).
-/
instance : Compl (SimpleGraph V) where
  compl G :=
    { Adj v w := v ≠ w ∧ ¬G.Adj v w
      symm.symm v w := fun ⟨hne, _⟩ ↦ ⟨hne.symm, by rwa [adj_comm]⟩ }

@[simp]
/-
**SimpleGraph.compl_adj** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：compl_adj (G : SimpleGraph V) (v w : V) : Gᶜ.Adj v w ↔ v != w ∧ ¬G.Adj v w
参数：G : SimpleGraph V；v w : V。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem compl_adj (G : SimpleGraph V) (v w : V) : Gᶜ.Adj v w ↔ v ≠ w ∧ ¬G.Adj v w :=
  Iff.rfl

/-- The difference of two graphs `x \ y` has the edges of `x` with the edges of `y` removed. -/
/-
**SimpleGraph.sdiff** 是 Mathlib 中的一个实例，位于命名空间 `SimpleGraph`。
形式化陈述：sdiff : SDiff (SimpleGraph V) where sdiff x y
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The difference of two graphs `x \ y` has the edges of `x` with the edges of `y` 
removed.
-/
instance sdiff : SDiff (SimpleGraph V) where
  sdiff x y :=
    { Adj := x.Adj \ y.Adj
      symm.symm v w h := by change x.Adj w v ∧ ¬y.Adj w v; rwa [x.adj_comm, y.adj_comm] }

@[simp]
/-
**SimpleGraph.sdiff_adj** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：sdiff_adj (x y : SimpleGraph V) (v w : V) : (x \ y).Adj v w ↔ x.Adj v w ∧ 
¬y.Adj v w
参数：x y : SimpleGraph V；v w : V。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem sdiff_adj (x y : SimpleGraph V) (v w : V) : (x \ y).Adj v w ↔ x.Adj v w ∧ ¬y.Adj v w :=
  Iff.rfl
/-
**SimpleGraph.supSet** 是 Mathlib 中的一个实例，位于命名空间 `SimpleGraph`。
形式化陈述：supSet : SupSet (SimpleGraph V) where sSup s
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance supSet : SupSet (SimpleGraph V) where
  sSup s :=
    { Adj a b := ∃ G ∈ s, Adj G a b
      symm.symm _ _ := Exists.imp fun _ ↦ And.imp_right Adj.symm }
/-
**SimpleGraph.infSet** 是 Mathlib 中的一个实例，位于命名空间 `SimpleGraph`。
形式化陈述：infSet : InfSet (SimpleGraph V) where sInf s
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance infSet : InfSet (SimpleGraph V) where
  sInf s :=
    { Adj a b := (∀ ⦃G⦄, G ∈ s → Adj G a b) ∧ a ≠ b
      symm.symm _ _  := And.imp (forall₂_imp fun _ _ ↦ Adj.symm) Ne.symm }

@[simp]
/-
**SimpleGraph.sSup_adj** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：sSup_adj {s : Set (SimpleGraph V)} {a b : V} : (sSup s).Adj a b ↔ exists G
 in s, Adj G a b
参数：SimpleGraph V。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem sSup_adj {s : Set (SimpleGraph V)} {a b : V} : (sSup s).Adj a b ↔ ∃ G ∈ s, Adj G a b :=
  Iff.rfl

@[simp]
/-
**SimpleGraph.sInf_adj** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：sInf_adj {s : Set (SimpleGraph V)} : (sInf s).Adj a b ↔ (forall G in s, Ad
j G a b) ∧ a != b
参数：SimpleGraph V。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem sInf_adj {s : Set (SimpleGraph V)} : (sInf s).Adj a b ↔ (∀ G ∈ s, Adj G a b) ∧ a ≠ b :=
  Iff.rfl

@[simp]
/-
**SimpleGraph.iSup_adj** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：iSup_adj {f : ι -> SimpleGraph V} : (⨆ i, f i).Adj a b ↔ exists i, (f i).A
dj a b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem iSup_adj {f : ι → SimpleGraph V} : (⨆ i, f i).Adj a b ↔ ∃ i, (f i).Adj a b := by simp [iSup]

@[simp]
/-
**SimpleGraph.iInf_adj** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：iInf_adj {f : ι -> SimpleGraph V} : (⨅ i, f i).Adj a b ↔ (forall i, (f i).
Adj a b) ∧ a != b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem iInf_adj {f : ι → SimpleGraph V} : (⨅ i, f i).Adj a b ↔ (∀ i, (f i).Adj a b) ∧ a ≠ b := by
  simp [iInf]
/-
**SimpleGraph.sInf_adj_of_nonempty** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：sInf_adj_of_nonempty {s : Set (SimpleGraph V)} (hs : s.Nonempty) : (sInf s
).Adj a b ↔ forall G in s, Adj G a b
参数：SimpleGraph V；hs : s.Nonempty。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `SimpleGraph.sInf_adj`：sInf_adj {s : Set (SimpleGraph V)} : (sInf s).Adj 
a b ↔ (forall G in s, Adj G a b) ∧ a != b
· 使用定理 `and_iff_left_of_imp`：∀ {a b : Prop}, (a → b) → (a ∧ b ↔ a)
· 使用定理 `SimpleGraph.Adj.ne`：∀ {V : Type u} {G : SimpleGraph V} {a b : V}, G.Adj 
a b → a ≠ b
-/
theorem sInf_adj_of_nonempty {s : Set (SimpleGraph V)} (hs : s.Nonempty) :
    (sInf s).Adj a b ↔ ∀ G ∈ s, Adj G a b :=
  sInf_adj.trans <|
    and_iff_left_of_imp <| by
      obtain ⟨G, hG⟩ := hs
      exact fun h => (h _ hG).ne
/-
**SimpleGraph.iInf_adj_of_nonempty** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：iInf_adj_of_nonempty [Nonempty ι] {f : ι -> SimpleGraph V} : (⨅ i, f i).Ad
j a b ↔ forall i, (f i).Adj a b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iInf.eq_1`：∀ {α : Type u} {ι : Sort v} [inst : InfSet α] (s : ι → α), iI
nf s = sInf (Set.range s)
· 使用定理 `SimpleGraph.sInf_adj_of_nonempty`：sInf_adj_of_nonempty {s : Set (SimpleG
raph V)} (hs : s.Nonempty) : (sInf s).Adj a b ↔ forall G in s, Adj G a b
· 使用定理 `Set.range_nonempty`：range_nonempty [h : Nonempty ι] (f : ι -> α) : (rang
e f).Nonempty
· 使用定理 `Set.forall_mem_range`：forall_mem_range {p : α -> Prop} : (forall a in ra
nge f, p a) ↔ forall i, p (f i)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem iInf_adj_of_nonempty [Nonempty ι] {f : ι → SimpleGraph V} :
    (⨅ i, f i).Adj a b ↔ ∀ i, (f i).Adj a b := by
  rw [iInf, sInf_adj_of_nonempty (Set.range_nonempty _), Set.forall_mem_range]
/-
**SimpleGraph.** 是 Mathlib 中的一个实例，位于命名空间 `SimpleGraph`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : PartialOrder (SimpleGraph V) :=
  fast_instance% PartialOrder.lift _ adj_injective
/-
**SimpleGraph.distribLattice** 是 Mathlib 中的一个实例，位于命名空间 `SimpleGraph`。
形式化陈述：distribLattice : DistribLattice (SimpleGraph V)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.adj_injective`：adj_injective : Injective (Adj : SimpleGraph 
V -> V -> V -> Prop)
-/
instance distribLattice : DistribLattice (SimpleGraph V) :=
  adj_injective.distribLattice _ .rfl .rfl (fun _ _ ↦ rfl) fun _ _ ↦ rfl
/-
**SimpleGraph.completeAtomicBooleanAlgebra** 是 Mathlib 中的一个实例，位于命名空间 `SimpleGrap
h`。
形式化陈述：completeAtomicBooleanAlgebra : CompleteAtomicBooleanAlgebra (SimpleGraph V
) where top.Adj
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.ne_of_adj`：ne_of_adj (h : G.Adj a b) : a != b
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
  inf_compl_le_bot _ _ _ h := False.elim <| h.2.2 h.1
  top_le_sup_compl G v w hvw := by
    by_cases h : G.Adj v w
    · exact Or.inl h
    · exact Or.inr ⟨hvw, h⟩
  isLUB_sSup _ := ⟨fun G hG _ _ hab ↦ ⟨G, hG, hab⟩, fun _ hG _ _ ⟨_, hH, hab⟩ ↦ hG hH hab⟩
  isGLB_sInf _ := ⟨fun _ hG _ _ hab ↦ hab.1 hG, fun _ hG _ _ hab ↦ ⟨fun _ hH => hG hH hab, hab.ne⟩⟩
  iInf_iSup_eq f := by ext; simp [Classical.skolem]

/-- The complete graph on a type `V` is the simple graph with all pairs of distinct vertices. -/
@[wikidata Q45715]
/-
**SimpleGraph.completeGraph** 是 Mathlib 中的一个缩写定义，位于命名空间 `SimpleGraph`。
形式化陈述：completeGraph (V : Type u) : SimpleGraph V
参数：V : Type u。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The complete graph on a type `V` is the simple graph with all pairs of distinct 
vertices.
-/
abbrev completeGraph (V : Type u) : SimpleGraph V := ⊤

/-- The graph with no edges on a given vertex type `V`. -/
/-
**SimpleGraph.emptyGraph** 是 Mathlib 中的一个缩写定义，位于命名空间 `SimpleGraph`。
形式化陈述：emptyGraph (V : Type u) : SimpleGraph V
参数：V : Type u。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The graph with no edges on a given vertex type `V`.
-/
abbrev emptyGraph (V : Type u) : SimpleGraph V := ⊥

@[simp]
/-
**SimpleGraph.top_adj** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：top_adj (v w : V) : (⊤ : SimpleGraph V).Adj v w ↔ v != w
参数：v w : V。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem top_adj (v w : V) : (⊤ : SimpleGraph V).Adj v w ↔ v ≠ w :=
  Iff.rfl

@[simp]
/-
**SimpleGraph.bot_adj** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：bot_adj (v w : V) : (⊥ : SimpleGraph V).Adj v w ↔ False
参数：v w : V。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem bot_adj (v w : V) : (⊥ : SimpleGraph V).Adj v w ↔ False :=
  Iff.rfl

@[simp]
/-
**SimpleGraph.completeGraph_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：completeGraph_eq_top (V : Type u) : completeGraph V = ⊤
参数：V : Type u。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem completeGraph_eq_top (V : Type u) : completeGraph V = ⊤ :=
  rfl

@[simp]
/-
**SimpleGraph.emptyGraph_eq_bot** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：emptyGraph_eq_bot (V : Type u) : emptyGraph V = ⊥
参数：V : Type u。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem emptyGraph_eq_bot (V : Type u) : emptyGraph V = ⊥ :=
  rfl

variable {G}
/-
**SimpleGraph.eq_bot_iff_forall_not_adj** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：eq_bot_iff_forall_not_adj : G = ⊥ ↔ forall a b : V, ¬G.Adj a b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem eq_bot_iff_forall_not_adj : G = ⊥ ↔ ∀ a b : V, ¬G.Adj a b := by
  simp [← le_bot_iff, le_iff_adj]
/-
**SimpleGraph.ne_bot_iff_exists_adj** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：ne_bot_iff_exists_adj : G != ⊥ ↔ exists a b : V, G.Adj a b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem ne_bot_iff_exists_adj : G ≠ ⊥ ↔ ∃ a b : V, G.Adj a b := by
  simp [eq_bot_iff_forall_not_adj]
/-
**SimpleGraph.eq_top_iff_forall_ne_adj** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：eq_top_iff_forall_ne_adj : G = ⊤ ↔ forall a b : V, a != b -> G.Adj a b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem eq_top_iff_forall_ne_adj : G = ⊤ ↔ ∀ a b : V, a ≠ b → G.Adj a b := by
  simp [← top_le_iff, le_iff_adj]
/-
**SimpleGraph.ne_top_iff_exists_not_adj** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：ne_top_iff_exists_not_adj : G != ⊤ ↔ exists a b : V, a != b ∧ ¬G.Adj a b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem ne_top_iff_exists_not_adj : G ≠ ⊤ ↔ ∃ a b : V, a ≠ b ∧ ¬G.Adj a b := by
  simp [eq_top_iff_forall_ne_adj]

variable (G)

@[simps]
/-
**SimpleGraph.** 是 Mathlib 中的一个实例，位于命名空间 `SimpleGraph`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (V : Type u) : Inhabited (SimpleGraph V) :=
  ⟨⊥⟩
/-
**SimpleGraph.uniqueOfSubsingleton** 是 Mathlib 中的一个实例，位于命名空间 `SimpleGraph`。
形式化陈述：uniqueOfSubsingleton [Subsingleton V] : Unique (SimpleGraph V) where defau
lt
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance uniqueOfSubsingleton [Subsingleton V] : Unique (SimpleGraph V) where
  default := ⊥
  uniq G := by ext a b; have := Subsingleton.elim a b; simp [this]
/-
**SimpleGraph.** 是 Mathlib 中的一个实例，位于命名空间 `SimpleGraph`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Nontrivial V] : Nontrivial (SimpleGraph V) :=
  ⟨⟨⊥, ⊤, fun h ↦ not_subsingleton V ⟨by simpa only [← adj_inj, funext_iff, bot_adj,
    top_adj, ne_eq, eq_iff_iff, false_iff, not_not] using h⟩⟩⟩

section Decidable

variable (V) (H : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel H.Adj]

/-
**SimpleGraph.Bot.adjDecidable** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph.Bot`。
形式化陈述：(V : Type u) → DecidableRel ⊥.Adj
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Bot.adjDecidable : DecidableRel (⊥ : SimpleGraph V).Adj :=
  inferInstanceAs <| DecidableRel fun _ _ => False
/-
**SimpleGraph.Sup.adjDecidable** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph.Sup`。
形式化陈述：(V : Type u) → (G H : SimpleGraph V) → [DecidableRel G.Adj] → [DecidableRe
l H.Adj] → DecidableRel (G ⊔ H).Adj
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Sup.adjDecidable : DecidableRel (G ⊔ H).Adj :=
  inferInstanceAs <| DecidableRel fun v w => G.Adj v w ∨ H.Adj v w
/-
**SimpleGraph.Inf.adjDecidable** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph.Inf`。
形式化陈述：(V : Type u) → (G H : SimpleGraph V) → [DecidableRel G.Adj] → [DecidableRe
l H.Adj] → DecidableRel (G ⊓ H).Adj
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Inf.adjDecidable : DecidableRel (G ⊓ H).Adj :=
  inferInstanceAs <| DecidableRel fun v w => G.Adj v w ∧ H.Adj v w
/-
**SimpleGraph.Sdiff.adjDecidable** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph.Sdiff`。
形式化陈述：(V : Type u) → (G H : SimpleGraph V) → [DecidableRel G.Adj] → [DecidableRe
l H.Adj] → DecidableRel (G \ H).Adj
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Sdiff.adjDecidable : DecidableRel (G \ H).Adj :=
  inferInstanceAs <| DecidableRel fun v w => G.Adj v w ∧ ¬H.Adj v w

variable [DecidableEq V]
/-
**SimpleGraph.Top.adjDecidable** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph.Top`。
形式化陈述：(V : Type u) → [DecidableEq V] → DecidableRel ⊤.Adj
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Top.adjDecidable : DecidableRel (⊤ : SimpleGraph V).Adj :=
  inferInstanceAs <| DecidableRel fun v w => v ≠ w
/-
**SimpleGraph.Compl.adjDecidable** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph.Compl`。
形式化陈述：(V : Type u) → (G : SimpleGraph V) → [DecidableRel G.Adj] → [DecidableEq V
] → DecidableRel Gᶜ.Adj
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Compl.adjDecidable : DecidableRel (Gᶜ.Adj) :=
  inferInstanceAs <| DecidableRel fun v w => v ≠ w ∧ ¬G.Adj v w

end Decidable

end Order

/-- `G.support` is the set of vertices that form edges in `G`. -/
/-
**SimpleGraph.support** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph`。
形式化陈述：support : Set V
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`G.support` is the set of vertices that form edges in `G`.
-/
def support : Set V :=
  SetRel.dom {(u, v) : V × V | G.Adj u v}
/-
**SimpleGraph.mem_support** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：mem_support {v : V} : v in G.support ↔ exists w, G.Adj v w
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_support {v : V} : v ∈ G.support ↔ ∃ w, G.Adj v w :=
  Iff.rfl

variable {G} in
/-
**SimpleGraph.Adj.mem_support_left** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Adj`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} {u v : V}, G.Adj u v → u ∈ G.support
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `SimpleGraph.mem_support`：mem_support {v : V} : v in G.support ↔ exists w
, G.Adj v w
-/
theorem Adj.mem_support_left (hadj : G.Adj u v) : u ∈ G.support :=
  G.mem_support.mpr ⟨v, hadj⟩

variable {G} in
/-
**SimpleGraph.Adj.mem_support_right** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Adj`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} {u v : V}, G.Adj u v → v ∈ G.support
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Adj.mem_support_left`：∀ {V : Type u} {G : SimpleGraph V} {u 
v : V}, G.Adj u v → u ∈ G.support
· 使用定理 `SimpleGraph.Adj.symm`：∀ {V : Type u} {G : SimpleGraph V} {u v : V}, G.Ad
j u v → G.Adj v u
-/
theorem Adj.mem_support_right (hadj : G.Adj u v) : v ∈ G.support :=
  hadj.symm.mem_support_left

@[gcongr]
/-
**SimpleGraph.support_mono** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：support_mono {G G' : SimpleGraph V} (h : G <= G') : G.support subseteq G'.
support
参数：h : G <= G'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetRel.dom_mono`：∀ {α : Type u_1} {β : Type u_2} {R₁ R₂ : SetRel α β}, R
₁ ⊆ R₂ → R₁.dom ⊆ R₂.dom
-/
theorem support_mono {G G' : SimpleGraph V} (h : G ≤ G') : G.support ⊆ G'.support :=
  SetRel.dom_mono fun _uv huv ↦ h huv
/-
**SimpleGraph.Adj.left_mem_support** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Adj`。
形式化陈述：∀ {V : Type u} (G : SimpleGraph V) {u v : V}, G.Adj u v → u ∈ G.support
参数：G : SimpleGraph V。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Adj.left_mem_support (hadj : G.Adj u v) : u ∈ G.support :=
  ⟨v, hadj⟩
/-
**SimpleGraph.Adj.right_mem_support** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Adj`。
形式化陈述：∀ {V : Type u} (G : SimpleGraph V) {u v : V}, G.Adj u v → v ∈ G.support
参数：G : SimpleGraph V。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Adj.left_mem_support`：∀ {V : Type u} (G : SimpleGraph V) {u 
v : V}, G.Adj u v → u ∈ G.support
· 使用定理 `SimpleGraph.Adj.symm`：∀ {V : Type u} {G : SimpleGraph V} {u v : V}, G.Ad
j u v → G.Adj v u
-/
theorem Adj.right_mem_support (hadj : G.Adj u v) : v ∈ G.support :=
  hadj.symm.left_mem_support

/-- All vertices are in the support of the complete graph if there is more than one vertex. -/
/-
**SimpleGraph.support_top_of_nontrivial** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：support_top_of_nontrivial [Nontrivial V] : (⊤ : SimpleGraph V).support = S
et.univ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.eq_univ_of_forall`：eq_univ_of_forall {s : Set α} : (forall x, x in s
) -> s = univ
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `exists_ne`：exists_ne [Nontrivial α] (x : α) : exists y, y != x

--- 原说明 ---
All vertices are in the support of the complete graph if there is more than one 
vertex.
-/
theorem support_top_of_nontrivial [Nontrivial V] : (⊤ : SimpleGraph V).support = Set.univ :=
  Set.eq_univ_of_forall fun v₁ => exists_ne v₁ |>.imp fun _v₂ h => h.symm

/-- The support of the empty graph is empty. -/
@[simp]
/-
**SimpleGraph.support_bot** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：support_bot : (⊥ : SimpleGraph V).support = ∅
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `SetRel.dom_eq_empty_iff`：∀ {α : Type u_1} {β : Type u_2} {R : SetRel α β
}, R.dom = ∅ ↔ R = ∅
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.empty_def`：empty_def : (∅ : Set α) = { _x : α | False }

--- 原说明 ---
The support of the empty graph is empty.
-/
theorem support_bot : (⊥ : SimpleGraph V).support = ∅ :=
  SetRel.dom_eq_empty_iff.mpr <| Set.empty_def.symm

/-- Only the empty graph has empty support. -/
@[simp]
/-
**SimpleGraph.support_eq_bot_iff** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：support_eq_bot_iff : G.support = ∅ ↔ G = ⊥
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `SimpleGraph.eq_bot_iff_forall_not_adj`：eq_bot_iff_forall_not_adj : G = ⊥
 ↔ forall a b : V, ¬G.Adj a b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.ext_iff`：∀ {α : Type u} {a b : Set α}, a = b ↔ ∀ (x : α), x ∈ a ↔ x 
∈ b
· 使用定理 `SetRel.dom_eq_empty_iff`：∀ {α : Type u_1} {β : Type u_2} {R : SetRel α β
}, R.dom = ∅ ↔ R = ∅
· 使用定理 `SimpleGraph.support_bot`：support_bot : (⊥ : SimpleGraph V).support = ∅
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
Only the empty graph has empty support.
-/
theorem support_eq_bot_iff : G.support = ∅ ↔ G = ⊥ :=
  ⟨fun h ↦ eq_bot_iff_forall_not_adj.mpr fun v w nadj ↦
    Set.ext_iff.mp (SetRel.dom_eq_empty_iff.mp h) (v, w) |>.mp nadj |>.elim,
   (· ▸ support_bot)⟩

/-- The support of a graph is empty if there at most one vertex. -/
@[simp]
/-
**SimpleGraph.support_of_subsingleton** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：support_of_subsingleton [Subsingleton V] : G.support = ∅
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.support_bot`：support_bot : (⊥ : SimpleGraph V).support = ∅
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Unique.uniq`：∀ {α : Sort u} (self : Unique α) (a : α), a = default

--- 原说明 ---
The support of a graph is empty if there at most one vertex.
-/
theorem support_of_subsingleton [Subsingleton V] : G.support = ∅ :=
  uniqueOfSubsingleton.uniq G ▸ support_bot

/-- `G.neighborSet v` is the set of vertices adjacent to `v` in `G`. -/
/-
**SimpleGraph.neighborSet** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph`。
形式化陈述：neighborSet (v : V) : Set V
参数：v : V。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`G.neighborSet v` is the set of vertices adjacent to `v` in `G`.
-/
def neighborSet (v : V) : Set V := {w | G.Adj v w}
/-
**SimpleGraph.neighborSet.memDecidable** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph.ne
ighborSet`。
形式化陈述：{V : Type u} → (G : SimpleGraph V) → (v : V) → [DecidableRel G.Adj] → Deci
dablePred fun x => x ∈ G.neighborSet v
参数：G : SimpleGraph V；v : V。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance neighborSet.memDecidable (v : V) [DecidableRel G.Adj] :
    DecidablePred (· ∈ G.neighborSet v) :=
  inferInstanceAs <| DecidablePred (Adj G v)
/-
**SimpleGraph.neighborSet_subset_support** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`
。
形式化陈述：neighborSet_subset_support (v : V) : G.neighborSet v subseteq G.support
参数：v : V。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Adj.symm`：∀ {V : Type u} {G : SimpleGraph V} {u v : V}, G.Ad
j u v → G.Adj v u
-/
lemma neighborSet_subset_support (v : V) : G.neighborSet v ⊆ G.support :=
  fun _ hadj ↦ ⟨v, hadj.symm⟩

section EdgeSet

variable {G₁ G₂ : SimpleGraph V}

/-- The edges of G consist of the unordered pairs of vertices related by
`G.Adj`. This is the order embedding; for the edge set of a particular graph, see
`SimpleGraph.edgeSet`.

The way `edgeSet` is defined is such that `mem_edgeSet` is proved by `Iff.rfl`.
(That is, `s(v, w) ∈ G.edgeSet` is definitionally equal to `G.Adj v w`.)
-/
-- Porting note: We need a separate definition so that dot notation works.
/-
**SimpleGraph.edgeSetEmbedding** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph`。
形式化陈述：edgeSetEmbedding (V : Type*) : SimpleGraph V ↪o Set (Sym2 V)
参数：V : Type*。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.symm`：∀ {V : Type u} (self : SimpleGraph V), Std.Symm self.A
dj
-/
def edgeSetEmbedding (V : Type*) : SimpleGraph V ↪o Set (Sym2 V) :=
  OrderEmbedding.ofMapLEIff (fun G => Sym2.fromRel G.symm) fun _ _ =>
    ⟨fun h a b => @h s(a, b), fun h e => Sym2.ind @h e⟩

/-- `G.edgeSet` is the edge set for `G`.
This is an abbreviation for `edgeSetEmbedding G` that permits dot notation. -/
/-
**SimpleGraph.edgeSet** 是 Mathlib 中的一个缩写定义，位于命名空间 `SimpleGraph`。
形式化陈述：edgeSet (G : SimpleGraph V) : Set (Sym2 V)
参数：G : SimpleGraph V。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`G.edgeSet` is the edge set for `G`.
This is an abbreviation for `edgeSetEmbedding G` that permits dot notation.
-/
abbrev edgeSet (G : SimpleGraph V) : Set (Sym2 V) := edgeSetEmbedding V G

@[simp]
/-
**SimpleGraph.mem_edgeSet** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：mem_edgeSet : s(v, w) in G.edgeSet ↔ G.Adj v w
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_edgeSet : s(v, w) ∈ G.edgeSet ↔ G.Adj v w :=
  Iff.rfl
/-
**SimpleGraph.not_isDiag_of_mem_edgeSet** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：not_isDiag_of_mem_edgeSet : e in edgeSet G -> ¬e.IsDiag
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Sym2.ind`：∀ {α : Type u_1} {f : Sym2 α → Prop}, (∀ (x y : α), f s(x, y))
 → ∀ (i : Sym2 α), f i
· 使用定理 `SimpleGraph.Adj.ne`：∀ {V : Type u} {G : SimpleGraph V} {a b : V}, G.Adj 
a b → a ≠ b
-/
theorem not_isDiag_of_mem_edgeSet : e ∈ edgeSet G → ¬e.IsDiag :=
  Sym2.ind (fun _ _ => Adj.ne) e
/-
**SimpleGraph.not_mem_edgeSet_of_isDiag** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：∀ {V : Type u} (G : SimpleGraph V) {e : Sym2 V}, e.IsDiag → e ∉ G.edgeSet
参数：G : SimpleGraph V。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `imp_not_comm`：∀ {a b : Prop}, a → ¬b ↔ b → ¬a
· 使用定理 `SimpleGraph.not_isDiag_of_mem_edgeSet`：not_isDiag_of_mem_edgeSet : e in 
edgeSet G -> ¬e.IsDiag
-/
@[simp] lemma not_mem_edgeSet_of_isDiag : e.IsDiag → e ∉ edgeSet G :=
  imp_not_comm.1 G.not_isDiag_of_mem_edgeSet

alias _root_.Sym2.IsDiag.not_mem_edgeSet := not_mem_edgeSet_of_isDiag
/-
**SimpleGraph.edgeSet_inj** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：edgeSet_inj : G₁.edgeSet = G₂.edgeSet ↔ G₁ = G₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderEmbedding.eq_iff_eq`：eq_iff_eq {a b} : f a = f b ↔ a = b
-/
theorem edgeSet_inj : G₁.edgeSet = G₂.edgeSet ↔ G₁ = G₂ := (edgeSetEmbedding V).eq_iff_eq
/-
**SimpleGraph.edgeSet_subset_edgeSet** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：edgeSet_subset_edgeSet : edgeSet G₁ subseteq edgeSet G₂ ↔ G₁ <= G₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem edgeSet_subset_edgeSet : edgeSet G₁ ⊆ edgeSet G₂ ↔ G₁ ≤ G₂ := by simp
/-
**SimpleGraph.edgeSet_ssubset_edgeSet** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：edgeSet_ssubset_edgeSet : edgeSet G₁ ⊂ edgeSet G₂ ↔ G₁ < G₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem edgeSet_ssubset_edgeSet : edgeSet G₁ ⊂ edgeSet G₂ ↔ G₁ < G₂ := by simp
/-
**SimpleGraph.edgeSet_injective** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：edgeSet_injective : Injective (edgeSet : SimpleGraph V -> Set (Sym2 V))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RelEmbedding.injective`：injective (f : r ↪r s) : Injective f
-/
theorem edgeSet_injective : Injective (edgeSet : SimpleGraph V → Set (Sym2 V)) :=
  (edgeSetEmbedding V).injective

@[gcongr] alias ⟨_, edgeSet_mono⟩ := edgeSet_subset_edgeSet

@[gcongr] alias ⟨_, edgeSet_strict_mono⟩ := edgeSet_ssubset_edgeSet

attribute [mono] edgeSet_mono edgeSet_strict_mono

variable (G₁ G₂)

@[simp]
/-
**SimpleGraph.edgeSet_bot** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：edgeSet_bot : (⊥ : SimpleGraph V).edgeSet = ∅
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Sym2.fromRel_bot`：fromRel_bot : fromRel (α
-/
theorem edgeSet_bot : (⊥ : SimpleGraph V).edgeSet = ∅ :=
  Sym2.fromRel_bot

@[simp]
/-
**SimpleGraph.edgeSet_top** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：edgeSet_top : (⊤ : SimpleGraph V).edgeSet = Sym2.diagSetᶜ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.instSymmSwapProp`：∀ {α : Sort u_1} (r : α → α → Prop) [Std.Symm
 r], Std.Symm (Function.swap r)
· 使用定理 `instSymmNe_mathlib`：∀ (α : Sort u_1), Std.Symm Ne
· 使用引理 `Sym2.diagSet_compl_eq_fromRel_ne`：diagSet_compl_eq_fromRel_ne : diagSetᶜ
 = fromRel (α
-/
theorem edgeSet_top : (⊤ : SimpleGraph V).edgeSet = Sym2.diagSetᶜ :=
  Sym2.diagSet_compl_eq_fromRel_ne.symm

@[simp]
/-
**SimpleGraph.edgeSet_subset_compl_diagSet** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGrap
h`。
形式化陈述：edgeSet_subset_compl_diagSet : G.edgeSet subseteq Sym2.diagSetᶜ
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `SimpleGraph.symm`：∀ {V : Type u} (self : SimpleGraph V), Std.Symm self.A
dj
· 使用定理 `SimpleGraph.loopless`：∀ {V : Type u} (self : SimpleGraph V), Std.Irrefl 
self.Adj
-/
theorem edgeSet_subset_compl_diagSet : G.edgeSet ⊆ Sym2.diagSetᶜ := by
  simpa [Set.subset_compl_iff_disjoint_left, edgeSet, edgeSetEmbedding] using G.loopless

@[simp]
/-
**SimpleGraph.edgeSet_sup** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：edgeSet_sup : (G₁ ⊔ G₂).edgeSet = G₁.edgeSet union G₂.edgeSet
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem edgeSet_sup : (G₁ ⊔ G₂).edgeSet = G₁.edgeSet ∪ G₂.edgeSet := by
  ext ⟨x, y⟩
  rfl

@[simp]
/-
**SimpleGraph.edgeSet_inf** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：edgeSet_inf : (G₁ ⊓ G₂).edgeSet = G₁.edgeSet inter G₂.edgeSet
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem edgeSet_inf : (G₁ ⊓ G₂).edgeSet = G₁.edgeSet ∩ G₂.edgeSet := by
  ext ⟨x, y⟩
  rfl
/-
**SimpleGraph.edgeSet_sSup** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：edgeSet_sSup {s : Set (SimpleGraph V)} : (sSup s).edgeSet = ⋃₀ (edgeSet ''
 s)
参数：SimpleGraph V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.sUnion_image`：sUnion_image (f : α -> Set β) (s : Set α) : ⋃₀ (f '' s
) = ⋃ a in s, f a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem edgeSet_sSup {s : Set (SimpleGraph V)} : (sSup s).edgeSet = ⋃₀ (edgeSet '' s) := by
  ext ⟨x, y⟩
  simp
/-
**SimpleGraph.edgeSet_sInf** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：edgeSet_sInf {s : Set (SimpleGraph V)} (h : s.Nonempty) : (sInf s).edgeSet
 = ⋂₀ (edgeSet '' s)
参数：SimpleGraph V；h : s.Nonempty。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.sInter_image`：sInter_image (f : α -> Set β) (s : Set α) : ⋂₀ (f '' s
) = ⋂ a in s, f a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `SimpleGraph.Adj.ne`：∀ {V : Type u} {G : SimpleGraph V} {a b : V}, G.Adj 
a b → a ≠ b
-/
theorem edgeSet_sInf {s : Set (SimpleGraph V)} (h : s.Nonempty) :
    (sInf s).edgeSet = ⋂₀ (edgeSet '' s) := by
  ext ⟨x, y⟩
  have ⟨G, hG⟩ := h
  simpa using (· G hG |>.ne)
/-
**SimpleGraph.edgeSet_iSup** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：edgeSet_iSup {ι : Sort*} {f : ι -> SimpleGraph V} : (⨆ i, f i).edgeSet = ⋃
 i, (f i).edgeSet
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem edgeSet_iSup {ι : Sort*} {f : ι → SimpleGraph V} :
    (⨆ i, f i).edgeSet = ⋃ i, (f i).edgeSet := by
  ext ⟨x, y⟩
  simp
/-
**SimpleGraph.edgeSet_iInf** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：edgeSet_iInf {ι : Sort*} [Nonempty ι] {f : ι -> SimpleGraph V} : (⨅ i, f i
).edgeSet = ⋂ i, (f i).edgeSet
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `SimpleGraph.Adj.ne`：∀ {V : Type u} {G : SimpleGraph V} {a b : V}, G.Adj 
a b → a ≠ b
-/
theorem edgeSet_iInf {ι : Sort*} [Nonempty ι] {f : ι → SimpleGraph V} :
    (⨅ i, f i).edgeSet = ⋂ i, (f i).edgeSet := by
  ext ⟨x, y⟩
  have ⟨i⟩ := ‹Nonempty ι›
  simpa using (· i |>.ne)

@[simp]
/-
**SimpleGraph.edgeSet_sdiff** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：edgeSet_sdiff : (G₁ \ G₂).edgeSet = G₁.edgeSet \ G₂.edgeSet
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem edgeSet_sdiff : (G₁ \ G₂).edgeSet = G₁.edgeSet \ G₂.edgeSet := by
  ext ⟨x, y⟩
  rfl

variable {G G₁ G₂}
/-
**SimpleGraph.disjoint_edgeSet** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：∀ {V : Type u} {G₁ G₂ : SimpleGraph V}, Disjoint G₁.edgeSet G₂.edgeSet ↔ D
isjoint G₁ G₂
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.disjoint_iff`：∀ {α : Type u} {s t : Set α}, Disjoint s t ↔ s ∩ t ⊆ ∅
· 使用定理 `disjoint_iff_inf_le`：disjoint_iff_inf_le : Disjoint a b ↔ a ⊓ b <= ⊥
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SimpleGraph.edgeSet_inf`：edgeSet_inf : (G₁ ⊓ G₂).edgeSet = G₁.edgeSet in
ter G₂.edgeSet
· 使用定理 `SimpleGraph.edgeSet_bot`：edgeSet_bot : (⊥ : SimpleGraph V).edgeSet = ∅
· 使用定理 `OrderEmbedding.le_iff_le`：le_iff_le {a b} : f a <= f b ↔ a <= b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma disjoint_edgeSet : Disjoint G₁.edgeSet G₂.edgeSet ↔ Disjoint G₁ G₂ := by
  rw [Set.disjoint_iff, disjoint_iff_inf_le, ← edgeSet_inf, ← edgeSet_bot, OrderEmbedding.le_iff_le]
/-
**SimpleGraph.disjoint_of_disjoint_support** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGrap
h`。
形式化陈述：disjoint_of_disjoint_support (h : Disjoint G.support H.support) : Disjoint
 G H
参数：h : Disjoint G.support H.support。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SimpleGraph.disjoint_edgeSet`：∀ {V : Type u} {G₁ G₂ : SimpleGraph V}, Di
sjoint G₁.edgeSet G₂.edgeSet ↔ Disjoint G₁ G₂
· 使用定理 `Set.disjoint_left`：disjoint_left : Disjoint s t ↔ forall ⦃a⦄, a in s -> 
a ∉ t
· 使用定理 `Sym2.forall`：∀ {α : Type u_4} {f : Sym2 α → Prop}, (∀ (x : Sym2 α), f x)
 ↔ ∀ (x y : α), f s(x, y)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
theorem disjoint_of_disjoint_support (h : Disjoint G.support H.support) : Disjoint G H := by
  simp_rw [Set.disjoint_left, mem_support] at h
  rw [← disjoint_edgeSet, Set.disjoint_left, Sym2.forall]
  grind [mem_edgeSet]
/-
**SimpleGraph.edgeSet_eq_empty** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V}, G.edgeSet = ∅ ↔ G = ⊥
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SimpleGraph.edgeSet_bot`：edgeSet_bot : (⊥ : SimpleGraph V).edgeSet = ∅
· 使用定理 `SimpleGraph.edgeSet_inj`：edgeSet_inj : G₁.edgeSet = G₂.edgeSet ↔ G₁ = G₂
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma edgeSet_eq_empty : G.edgeSet = ∅ ↔ G = ⊥ := by rw [← edgeSet_bot, edgeSet_inj]
/-
**SimpleGraph.edgeSet_nonempty** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V}, G.edgeSet.Nonempty ↔ G ≠ ⊥
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.nonempty_iff_ne_empty`：nonempty_iff_ne_empty : s.Nonempty ↔ s != ∅
· 使用定理 `Iff.ne`：∀ {α : Sort u_1} {β : Sort u_2} {a b : α} {c d : β}, (a = b ↔ c 
= d) → (a ≠ b ↔ c ≠ d)
· 使用定理 `SimpleGraph.edgeSet_eq_empty`：∀ {V : Type u} {G : SimpleGraph V}, G.edge
Set = ∅ ↔ G = ⊥
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma edgeSet_nonempty : G.edgeSet.Nonempty ↔ G ≠ ⊥ := by
  rw [Set.nonempty_iff_ne_empty, edgeSet_eq_empty.ne]

/-- This lemma, combined with `edgeSet_sdiff` and `edgeSet_fromEdgeSet`,
allows proving `(G \ fromEdgeSet s).edgeSet = G.edgeSet \ s` by `simp`. -/
@[simp]
/-
**SimpleGraph.edgeSet_sdiff_sdiff_isDiag** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`
。
形式化陈述：edgeSet_sdiff_sdiff_isDiag (G : SimpleGraph V) (s : Set (Sym2 V)) : G.edge
Set \ (s \ Sym2.diagSet) = G.edgeSet \ s
参数：G : SimpleGraph V；s : Set (Sym2 V)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This lemma, combined with `edgeSet_sdiff` and `edgeSet_fromEdgeSet`,
allows proving `(G \ fromEdgeSet s).edgeSet = G.edgeSet \ s` by `simp`.
-/
theorem edgeSet_sdiff_sdiff_isDiag (G : SimpleGraph V) (s : Set (Sym2 V)) :
    G.edgeSet \ (s \ Sym2.diagSet) = G.edgeSet \ s := by
  grind [Sym2.mem_diagSet, not_isDiag_of_mem_edgeSet]

/-- Two vertices are adjacent iff there is an edge between them. The
condition `v ≠ w` ensures they are different endpoints of the edge,
which is necessary since when `v = w` the existential
`∃ (e ∈ G.edgeSet), v ∈ e ∧ w ∈ e` is satisfied by every edge
incident to `v`. -/
/-
**SimpleGraph.adj_iff_exists_edge** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：adj_iff_exists_edge {v w : V} : G.Adj v w ↔ v != w ∧ exists e in G.edgeSet
, v in e ∧ w in e
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.ne_of_adj`：ne_of_adj (h : G.Adj a b) : a != b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `SimpleGraph.mem_edgeSet`：mem_edgeSet : s(v, w) in G.edgeSet ↔ G.Adj v w
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Sym2.mem_and_mem_iff`：mem_and_mem_iff {x y : α} {z : Sym2 α} (hne : x !=
 y) : x in z ∧ y in z ↔ z = s(x, y)

--- 原说明 ---
Two vertices are adjacent iff there is an edge between them. The
condition `v ≠ w` ensures they are different endpoints of the edge,
which is necessary since when `v = w` the existential
`∃ (e ∈ G.edgeSet), v ∈ e ∧ w ∈ e` is satisfied by every edge
incident to `v`.
-/
theorem adj_iff_exists_edge {v w : V} : G.Adj v w ↔ v ≠ w ∧ ∃ e ∈ G.edgeSet, v ∈ e ∧ w ∈ e := by
  refine ⟨fun _ => ⟨G.ne_of_adj ‹_›, s(v, w), by simpa⟩, ?_⟩
  rintro ⟨hne, e, he, hv⟩
  rw [Sym2.mem_and_mem_iff hne] at hv
  subst e
  rwa [mem_edgeSet] at he
/-
**SimpleGraph.adj_iff_exists_edge_coe** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：adj_iff_exists_edge_coe : G.Adj a b ↔ exists e : G.edgeSet, e.val = s(a, b
)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem adj_iff_exists_edge_coe : G.Adj a b ↔ ∃ e : G.edgeSet, e.val = s(a, b) := by
  simp only [mem_edgeSet, exists_prop, SetCoe.exists, exists_eq_right]

@[simp]
/-
**SimpleGraph.edgeSet_subset_sym2_iff** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：edgeSet_subset_sym2_iff {s : Set V} : G.edgeSet subseteq s.sym2 ↔ G.suppor
t subseteq s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.mk_mem_sym2_iff`：∀ {α : Type u_1} {s : Set α} {x y : α}, s(x, y) ∈ s
.sym2 ↔ x ∈ s ∧ y ∈ s
· 使用定理 `Sym2.ind`：∀ {α : Type u_1} {f : Sym2 α → Prop}, (∀ (x y : α), f s(x, y))
 → ∀ (i : Sym2 α), f i
· 使用定理 `SimpleGraph.Adj.mem_support_left`：∀ {V : Type u} {G : SimpleGraph V} {u 
v : V}, G.Adj u v → u ∈ G.support
· 使用定理 `SimpleGraph.Adj.mem_support_right`：∀ {V : Type u} {G : SimpleGraph V} {u
 v : V}, G.Adj u v → v ∈ G.support
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem edgeSet_subset_sym2_iff {s : Set V} :
    G.edgeSet ⊆ s.sym2 ↔ G.support ⊆ s := by
  refine ⟨fun h u hu ↦ ?_, fun h e hadj ↦ ?_⟩
  · have ⟨v, huv⟩ := hu
    exact (Set.mk_mem_sym2_iff.mp <| h huv).left
  · cases e
    exact ⟨h hadj.mem_support_left, h hadj.mem_support_right⟩

variable (G G₁ G₂)
/-
**SimpleGraph.edge_other_ne** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：edge_other_ne {e : Sym2 V} (he : e in G.edgeSet) {v : V} (h : v in e) : Sy
m2.Mem.other h != v
参数：he : e in G.edgeSet；h : v in e。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.ne_of_adj`：ne_of_adj (h : G.Adj a b) : a != b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Sym2.eq_swap`：eq_swap {a b : α} : s(a, b) = s(b, a)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Sym2.other_spec`：other_spec {a : α} {z : Sym2 α} (h : a in z) : s(a, Mem
.other h) = z
-/
theorem edge_other_ne {e : Sym2 V} (he : e ∈ G.edgeSet) {v : V} (h : v ∈ e) :
    Sym2.Mem.other h ≠ v := by
  rw [← Sym2.other_spec h, Sym2.eq_swap] at he
  exact G.ne_of_adj he
/-
**SimpleGraph.decidableMemEdgeSet** 是 Mathlib 中的一个实例，位于命名空间 `SimpleGraph`。
形式化陈述：decidableMemEdgeSet [DecidableRel G.Adj] : DecidablePred (· in G.edgeSet)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.symm`：∀ {V : Type u} (self : SimpleGraph V), Std.Symm self.A
dj
-/
instance decidableMemEdgeSet [DecidableRel G.Adj] : DecidablePred (· ∈ G.edgeSet) :=
  Sym2.fromRel.decidablePred G.symm
/-
**SimpleGraph.fintypeEdgeSet** 是 Mathlib 中的一个实例，位于命名空间 `SimpleGraph`。
形式化陈述：fintypeEdgeSet [Fintype (Sym2 V)] [DecidableRel G.Adj] : Fintype G.edgeSet
参数：Sym2 V。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance fintypeEdgeSet [Fintype (Sym2 V)] [DecidableRel G.Adj] : Fintype G.edgeSet :=
  Subtype.fintype _
/-
**SimpleGraph.fintypeEdgeSetBot** 是 Mathlib 中的一个实例，位于命名空间 `SimpleGraph`。
形式化陈述：fintypeEdgeSetBot : Fintype (⊥ : SimpleGraph V).edgeSet
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance fintypeEdgeSetBot : Fintype (⊥ : SimpleGraph V).edgeSet := by
  rw [edgeSet_bot]
  infer_instance
/-
**SimpleGraph.fintypeEdgeSetSup** 是 Mathlib 中的一个实例，位于命名空间 `SimpleGraph`。
形式化陈述：fintypeEdgeSetSup [DecidableEq V] [Fintype G₁.edgeSet] [Fintype G₂.edgeSet
] : Fintype (G₁ ⊔ G₂).edgeSet
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance fintypeEdgeSetSup [DecidableEq V] [Fintype G₁.edgeSet] [Fintype G₂.edgeSet] :
    Fintype (G₁ ⊔ G₂).edgeSet := by
  rw [edgeSet_sup]
  infer_instance
/-
**SimpleGraph.fintypeEdgeSetInf** 是 Mathlib 中的一个实例，位于命名空间 `SimpleGraph`。
形式化陈述：fintypeEdgeSetInf [DecidableEq V] [Fintype G₁.edgeSet] [Fintype G₂.edgeSet
] : Fintype (G₁ ⊓ G₂).edgeSet
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance fintypeEdgeSetInf [DecidableEq V] [Fintype G₁.edgeSet] [Fintype G₂.edgeSet] :
    Fintype (G₁ ⊓ G₂).edgeSet := by
  rw [edgeSet_inf]
  exact Set.fintypeInter _ _
/-
**SimpleGraph.fintypeEdgeSetSdiff** 是 Mathlib 中的一个实例，位于命名空间 `SimpleGraph`。
形式化陈述：fintypeEdgeSetSdiff [DecidableEq V] [Fintype G₁.edgeSet] [Fintype G₂.edgeS
et] : Fintype (G₁ \ G₂).edgeSet
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance fintypeEdgeSetSdiff [DecidableEq V] [Fintype G₁.edgeSet] [Fintype G₂.edgeSet] :
    Fintype (G₁ \ G₂).edgeSet := by
  rw [edgeSet_sdiff]
  exact Set.fintypeDiff _ _

end EdgeSet

section FromEdgeSet

variable (s : Set (Sym2 V))

/-- `fromEdgeSet` constructs a `SimpleGraph` from a set of edges, without loops. -/
/-
**SimpleGraph.fromEdgeSet** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph`。
形式化陈述：fromEdgeSet : SimpleGraph V where Adj
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`fromEdgeSet` constructs a `SimpleGraph` from a set of edges, without loops.
-/
def fromEdgeSet : SimpleGraph V where
  Adj := Sym2.ToRel s ⊓ Ne
  symm.symm u v h := ⟨Sym2.toRel_symm s |>.symm u v h.left, h.right.symm⟩
/-
**SimpleGraph.** 是 Mathlib 中的一个实例，位于命名空间 `SimpleGraph`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [DecidablePred (· ∈ s)] [DecidableEq V] : DecidableRel (fromEdgeSet s).Adj :=
  inferInstanceAs <| DecidableRel fun v w ↦ s(v, w) ∈ s ∧ v ≠ w

@[simp]
/-
**SimpleGraph.fromEdgeSet_adj** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：fromEdgeSet_adj : (fromEdgeSet s).Adj v w ↔ s(v, w) in s ∧ v != w
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem fromEdgeSet_adj : (fromEdgeSet s).Adj v w ↔ s(v, w) ∈ s ∧ v ≠ w :=
  Iff.rfl

-- Note: we need to make sure `fromEdgeSet_adj` and this lemma are confluent.
-- In particular, both yield `s(u, v) ∈ (fromEdgeSet s).edgeSet` ==> `s(v, w) ∈ s ∧ v ≠ w`.
@[simp]
/-
**SimpleGraph.edgeSet_fromEdgeSet** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：edgeSet_fromEdgeSet : (fromEdgeSet s).edgeSet = s \ Sym2.diagSet
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Sym2.ind`：∀ {α : Type u_1} {f : Sym2 α → Prop}, (∀ (x y : α), f s(x, y))
 → ∀ (i : Sym2 α), f i
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
theorem edgeSet_fromEdgeSet : (fromEdgeSet s).edgeSet = s \ Sym2.diagSet := by
  ext e
  exact Sym2.ind (by simp) e

@[simp]
/-
**SimpleGraph.fromEdgeSet_edgeSet** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：fromEdgeSet_edgeSet : fromEdgeSet G.edgeSet = G
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.ext`：∀ {V : Type u} {x y : SimpleGraph V}, x.Adj = y.Adj → x
 = y
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `SimpleGraph.ne_of_adj`：ne_of_adj (h : G.Adj a b) : a != b
-/
theorem fromEdgeSet_edgeSet : fromEdgeSet G.edgeSet = G := by
  ext v w
  exact ⟨fun h => h.1, fun h => ⟨h, G.ne_of_adj h⟩⟩
/-
**SimpleGraph.le_fromEdgeSet_iff** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：∀ {V : Type u} (G : SimpleGraph V) (s : Set (Sym2 V)), G ≤ SimpleGraph.fro
mEdgeSet s ↔ G.edgeSet ⊆ s
参数：G : SimpleGraph V；s : Set (Sym2 V)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `SimpleGraph.edgeSet_fromEdgeSet`：edgeSet_fromEdgeSet : (fromEdgeSet s).e
dgeSet = s \ Sym2.diagSet
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
@[simp] lemma le_fromEdgeSet_iff : G ≤ fromEdgeSet s ↔ G.edgeSet ⊆ s := by
  simp [← edgeSet_subset_edgeSet, Set.subset_def]; grind [not_isDiag_of_mem_edgeSet]
/-
**SimpleGraph.fromEdgeSet_le** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：∀ {V : Type u} (G : SimpleGraph V) {s : Set (Sym2 V)}, SimpleGraph.fromEdg
eSet s ≤ G ↔ s \ Sym2.diagSet ⊆ G.edgeSet
参数：G : SimpleGraph V；Sym2 V。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `SimpleGraph.edgeSet_fromEdgeSet`：edgeSet_fromEdgeSet : (fromEdgeSet s).e
dgeSet = s \ Sym2.diagSet
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma fromEdgeSet_le {s : Set (Sym2 V)} :
    fromEdgeSet s ≤ G ↔ s \ Sym2.diagSet ⊆ G.edgeSet := by simp [← edgeSet_subset_edgeSet]
/-
**SimpleGraph.edgeSet_eq_iff** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
形式化陈述：edgeSet_eq_iff : G.edgeSet = s ↔ G = fromEdgeSet s ∧ Disjoint s Sym2.diagS
et where mp
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.fromEdgeSet_edgeSet`：fromEdgeSet_edgeSet : fromEdgeSet G.edg
eSet = G
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `SimpleGraph.edgeSet_fromEdgeSet`：edgeSet_fromEdgeSet : (fromEdgeSet s).e
dgeSet = s \ Sym2.diagSet
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma edgeSet_eq_iff : G.edgeSet = s ↔ G = fromEdgeSet s ∧ Disjoint s Sym2.diagSet where
  mp := by rintro rfl; simp +contextual [Set.disjoint_right]
  mpr := by rintro ⟨rfl, hs⟩; simp [hs]

@[simp]
/-
**SimpleGraph.fromEdgeSet_empty** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：fromEdgeSet_empty : fromEdgeSet (∅ : Set (Sym2 V)) = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.ext`：∀ {V : Type u} {x y : SimpleGraph V}, x.Adj = y.Adj → x
 = y
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem fromEdgeSet_empty : fromEdgeSet (∅ : Set (Sym2 V)) = ⊥ := by
  ext v w
  simp only [fromEdgeSet_adj, Set.mem_empty_iff_false, false_and, bot_adj]
/-
**SimpleGraph.fromEdgeSet_not_isDiag** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：∀ {V : Type u}, SimpleGraph.fromEdgeSet Sym2.diagSetᶜ = ⊤
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.ext`：∀ {V : Type u} {x y : SimpleGraph V}, x.Adj = y.Adj → x
 = y
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma fromEdgeSet_not_isDiag : @fromEdgeSet V Sym2.diagSetᶜ = ⊤ := by ext; simp

@[simp]
/-
**SimpleGraph.fromEdgeSet_univ** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：fromEdgeSet_univ : fromEdgeSet (Set.univ : Set (Sym2 V)) = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.ext`：∀ {V : Type u} {x y : SimpleGraph V}, x.Adj = y.Adj → x
 = y
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem fromEdgeSet_univ : fromEdgeSet (Set.univ : Set (Sym2 V)) = ⊤ := by
  ext v w
  simp only [fromEdgeSet_adj, Set.mem_univ, true_and, top_adj]

@[simp]
/-
**SimpleGraph.fromEdgeSet_inter** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：fromEdgeSet_inter (s t : Set (Sym2 V)) : fromEdgeSet (s inter t) = fromEdg
eSet s ⊓ fromEdgeSet t
参数：s t : Set (Sym2 V)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.ext`：∀ {V : Type u} {x y : SimpleGraph V}, x.Adj = y.Adj → x
 = y
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
-/
theorem fromEdgeSet_inter (s t : Set (Sym2 V)) :
    fromEdgeSet (s ∩ t) = fromEdgeSet s ⊓ fromEdgeSet t := by
  ext v w
  simp only [fromEdgeSet_adj, Set.mem_inter_iff, Ne, inf_adj]
  tauto

@[simp]
/-
**SimpleGraph.fromEdgeSet_union** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：fromEdgeSet_union (s t : Set (Sym2 V)) : fromEdgeSet (s union t) = fromEdg
eSet s ⊔ fromEdgeSet t
参数：s t : Set (Sym2 V)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.ext`：∀ {V : Type u} {x y : SimpleGraph V}, x.Adj = y.Adj → x
 = y
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem fromEdgeSet_union (s t : Set (Sym2 V)) :
    fromEdgeSet (s ∪ t) = fromEdgeSet s ⊔ fromEdgeSet t := by
  ext v w
  simp [Set.mem_union, or_and_right]
/-
**SimpleGraph.fromEdgeSet_sUnion** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：fromEdgeSet_sUnion {s : Set (Set (Sym2 V))} : fromEdgeSet (⋃₀ s) = sSup (f
romEdgeSet '' s)
参数：Set (Sym2 V)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.ext`：∀ {V : Type u} {x y : SimpleGraph V}, x.Adj = y.Adj → x
 = y
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
-/
theorem fromEdgeSet_sUnion {s : Set (Set (Sym2 V))} :
    fromEdgeSet (⋃₀ s) = sSup (fromEdgeSet '' s) := by
  ext u v
  simp
  grind
/-
**SimpleGraph.fromEdgeSet_iUnion** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：fromEdgeSet_iUnion {ι : Sort*} {f : ι -> Set (Sym2 V)} : fromEdgeSet (⋃ i,
 f i) = ⨆ i, fromEdgeSet (f i)
参数：Sym2 V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.ext`：∀ {V : Type u} {x y : SimpleGraph V}, x.Adj = y.Adj → x
 = y
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem fromEdgeSet_iUnion {ι : Sort*} {f : ι → Set (Sym2 V)} :
    fromEdgeSet (⋃ i, f i) = ⨆ i, fromEdgeSet (f i) := by
  ext u v
  simp
/-
**SimpleGraph.fromEdgeSet_sInter** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：fromEdgeSet_sInter {s : Set (Set (Sym2 V))} : fromEdgeSet (⋂₀ s) = sInf (f
romEdgeSet '' s)
参数：Set (Sym2 V)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.ext`：∀ {V : Type u} {x y : SimpleGraph V}, x.Adj = y.Adj → x
 = y
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem fromEdgeSet_sInter {s : Set (Set (Sym2 V))} :
    fromEdgeSet (⋂₀ s) = sInf (fromEdgeSet '' s) := by
  ext u v
  simp_all
/-
**SimpleGraph.fromEdgeSet_iInter** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：fromEdgeSet_iInter {ι : Sort*} {f : ι -> Set (Sym2 V)} : fromEdgeSet (⋂ i,
 f i) = ⨅ i, fromEdgeSet (f i)
参数：Sym2 V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.ext`：∀ {V : Type u} {x y : SimpleGraph V}, x.Adj = y.Adj → x
 = y
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem fromEdgeSet_iInter {ι : Sort*} {f : ι → Set (Sym2 V)} :
    fromEdgeSet (⋂ i, f i) = ⨅ i, fromEdgeSet (f i) := by
  ext u v
  simp_all

@[simp]
/-
**SimpleGraph.fromEdgeSet_sdiff** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：fromEdgeSet_sdiff (s t : Set (Sym2 V)) : fromEdgeSet (s \ t) = fromEdgeSet
 s \ fromEdgeSet t
参数：s t : Set (Sym2 V)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.ext`：∀ {V : Type u} {x y : SimpleGraph V}, x.Adj = y.Adj → x
 = y
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
-/
theorem fromEdgeSet_sdiff (s t : Set (Sym2 V)) :
    fromEdgeSet (s \ t) = fromEdgeSet s \ fromEdgeSet t := by
  ext v w
  constructor <;> simp +contextual

@[gcongr, mono]
/-
**SimpleGraph.fromEdgeSet_mono** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：fromEdgeSet_mono {s t : Set (Sym2 V)} (h : s subseteq t) : fromEdgeSet s <
= fromEdgeSet t
参数：Sym2 V；h : s subseteq t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.edgeSet_fromEdgeSet`：edgeSet_fromEdgeSet : (fromEdgeSet s).e
dgeSet = s \ Sym2.diagSet
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `sdiff_le_sdiff`：∀ {α : Type u_2} [inst : GeneralizedCoheytingAlgebra α] 
{a b c d : α}, d ≤ c → b ≤ a → d \ a ≤ c \ b
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `sdiff_le`：∀ {α : Type u_2} [inst : GeneralizedCoheytingAlgebra α] {a b :
 α}, a \ b ≤ a
-/
theorem fromEdgeSet_mono {s t : Set (Sym2 V)} (h : s ⊆ t) : fromEdgeSet s ≤ fromEdgeSet t := by
  simp only [le_fromEdgeSet_iff, edgeSet_fromEdgeSet]; grw [h]; exact sdiff_le
/-
**SimpleGraph.disjoint_fromEdgeSet** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：∀ {V : Type u} (G : SimpleGraph V) (s : Set (Sym2 V)), Disjoint G (SimpleG
raph.fromEdgeSet s) ↔ Disjoint G.edgeSet s
参数：G : SimpleGraph V；s : Set (Sym2 V)；SimpleGraph.fromEdgeSet s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.sdiff_union_inter`：sdiff_union_inter (s t : Set α) : s \ t union s i
nter t = s
· 使用定理 `SimpleGraph.disjoint_edgeSet`：∀ {V : Type u} {G₁ G₂ : SimpleGraph V}, Di
sjoint G₁.edgeSet G₂.edgeSet ↔ Disjoint G₁ G₂
· 使用定理 `SimpleGraph.edgeSet_fromEdgeSet`：edgeSet_fromEdgeSet : (fromEdgeSet s).e
dgeSet = s \ Sym2.diagSet
-/
@[simp] lemma disjoint_fromEdgeSet : Disjoint G (fromEdgeSet s) ↔ Disjoint G.edgeSet s := by
  conv_rhs => rw [← Set.sdiff_union_inter s Sym2.diagSet]
  rw [← disjoint_edgeSet, edgeSet_fromEdgeSet]
  grind [edgeSet_subset_compl_diagSet]
/-
**SimpleGraph.fromEdgeSet_disjoint** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：∀ {V : Type u} (G : SimpleGraph V) (s : Set (Sym2 V)), Disjoint (SimpleGra
ph.fromEdgeSet s) G ↔ Disjoint s G.edgeSet
参数：G : SimpleGraph V；s : Set (Sym2 V)；SimpleGraph.fromEdgeSet s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `disjoint_comm`：disjoint_comm : Disjoint a b ↔ Disjoint b a
· 使用定理 `SimpleGraph.disjoint_fromEdgeSet`：∀ {V : Type u} (G : SimpleGraph V) (s 
: Set (Sym2 V)), Disjoint G (SimpleGraph.fromEdgeSet s) ↔ Disjoint G.edgeSet s
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma fromEdgeSet_disjoint : Disjoint (fromEdgeSet s) G ↔ Disjoint s G.edgeSet := by
  rw [disjoint_comm, disjoint_fromEdgeSet, disjoint_comm]
/-
**SimpleGraph.** 是 Mathlib 中的一个实例，位于命名空间 `SimpleGraph`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [DecidableEq V] [Fintype s] : Fintype (fromEdgeSet s).edgeSet := by
  rw [edgeSet_fromEdgeSet s]
  infer_instance

end FromEdgeSet

/-
**SimpleGraph.disjoint_left** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：disjoint_left {G H : SimpleGraph V} : Disjoint G H ↔ forall x y, G.Adj x y
 -> ¬H.Adj x y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem disjoint_left {G H : SimpleGraph V} : Disjoint G H ↔ ∀ x y, G.Adj x y → ¬H.Adj x y := by
  simp [← disjoint_edgeSet, Set.disjoint_left, Sym2.forall]

/-! ### Incidence set -/


/-- Set of edges incident to a given vertex, aka incidence set. -/
/-
**SimpleGraph.incidenceSet** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph`。
形式化陈述：incidenceSet (v : V) : Set (Sym2 V)
参数：v : V。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Set of edges incident to a given vertex, aka incidence set.
-/
def incidenceSet (v : V) : Set (Sym2 V) :=
  { e ∈ G.edgeSet | v ∈ e }
/-
**SimpleGraph.incidenceSet_subset** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：incidenceSet_subset (v : V) : G.incidenceSet v subseteq G.edgeSet
参数：v : V。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem incidenceSet_subset (v : V) : G.incidenceSet v ⊆ G.edgeSet := fun _ h => h.1
/-
**SimpleGraph.mk'_mem_incidenceSet_iff** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：∀ {V : Type u} (G : SimpleGraph V) {a b c : V}, s(b, c) ∈ G.incidenceSet a
 ↔ G.Adj b c ∧ (a = b ∨ a = c)
参数：G : SimpleGraph V；b, c；a = b ∨ a = c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `and_congr_right'`：∀ {b c a : Prop}, (b ↔ c) → (a ∧ b ↔ a ∧ c)
· 使用定理 `Sym2.mem_iff`：mem_iff {a b c : α} : a in s(b, c) ↔ a = b ∨ a = c
-/
theorem mk'_mem_incidenceSet_iff : s(b, c) ∈ G.incidenceSet a ↔ G.Adj b c ∧ (a = b ∨ a = c) :=
  and_congr_right' Sym2.mem_iff
/-
**SimpleGraph.mk'_mem_incidenceSet_left_iff** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGra
ph`。
形式化陈述：∀ {V : Type u} (G : SimpleGraph V) {a b : V}, s(a, b) ∈ G.incidenceSet a ↔
 G.Adj a b
参数：G : SimpleGraph V；a, b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `and_iff_left`：∀ {b a : Prop}, b → (a ∧ b ↔ a)
· 使用定理 `Sym2.mem_mk_left`：mem_mk_left (x y : α) : x in s(x, y)
-/
theorem mk'_mem_incidenceSet_left_iff : s(a, b) ∈ G.incidenceSet a ↔ G.Adj a b :=
  and_iff_left <| Sym2.mem_mk_left _ _
/-
**SimpleGraph.mk'_mem_incidenceSet_right_iff** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGr
aph`。
形式化陈述：∀ {V : Type u} (G : SimpleGraph V) {a b : V}, s(a, b) ∈ G.incidenceSet b ↔
 G.Adj a b
参数：G : SimpleGraph V；a, b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `and_iff_left`：∀ {b a : Prop}, b → (a ∧ b ↔ a)
· 使用定理 `Sym2.mem_mk_right`：mem_mk_right (x y : α) : y in s(x, y)
-/
theorem mk'_mem_incidenceSet_right_iff : s(a, b) ∈ G.incidenceSet b ↔ G.Adj a b :=
  and_iff_left <| Sym2.mem_mk_right _ _
/-
**SimpleGraph.edge_mem_incidenceSet_iff** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：edge_mem_incidenceSet_iff {e : G.edgeSet} : ↑e in G.incidenceSet a ↔ a in 
(e : Sym2 V)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `and_iff_right`：∀ {a b : Prop}, a → (a ∧ b ↔ b)
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem edge_mem_incidenceSet_iff {e : G.edgeSet} : ↑e ∈ G.incidenceSet a ↔ a ∈ (e : Sym2 V) :=
  and_iff_right e.2
/-
**SimpleGraph.iUnion_incidenceSet** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：iUnion_incidenceSet : ⋃ v, G.incidenceSet v = G.edgeSet
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem iUnion_incidenceSet : ⋃ v, G.incidenceSet v = G.edgeSet := by
  ext ⟨_, _⟩
  simp [mk'_mem_incidenceSet_iff]

variable {G H} in
/-
**SimpleGraph.disjoint_incidenceSet** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：disjoint_incidenceSet : (forall v, Disjoint (G.incidenceSet v) (H.incidenc
eSet v)) ↔ Disjoint G H
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
-/
theorem disjoint_incidenceSet :
    (∀ v, Disjoint (G.incidenceSet v) (H.incidenceSet v)) ↔ Disjoint G H := by
  simp_rw [← disjoint_edgeSet, ← iUnion_incidenceSet, Set.disjoint_iUnion_left,
    Set.disjoint_iUnion_right, Set.disjoint_left, Sym2.forall]
  grind [mk'_mem_incidenceSet_iff]
/-
**SimpleGraph.incidenceSet_inter_incidenceSet_subset** 是 Mathlib 中的一个定理，位于命名空间 `
SimpleGraph`。
形式化陈述：incidenceSet_inter_incidenceSet_subset (h : a != b) : G.incidenceSet a int
er G.incidenceSet b subseteq {s(a, b)}
参数：h : a != b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Sym2.mem_and_mem_iff`：mem_and_mem_iff {x y : α} {z : Sym2 α} (hne : x !=
 y) : x in z ∧ y in z ↔ z = s(x, y)
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem incidenceSet_inter_incidenceSet_subset (h : a ≠ b) :
    G.incidenceSet a ∩ G.incidenceSet b ⊆ {s(a, b)} := fun _e he =>
  (Sym2.mem_and_mem_iff h).1 ⟨he.1.2, he.2.2⟩
/-
**SimpleGraph.incidenceSet_inter_incidenceSet_of_adj** 是 Mathlib 中的一个定理，位于命名空间 `
SimpleGraph`。
形式化陈述：incidenceSet_inter_incidenceSet_of_adj (h : G.Adj a b) : G.incidenceSet a 
inter G.incidenceSet b = {s(a, b)}
参数：h : G.Adj a b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `SimpleGraph.incidenceSet_inter_incidenceSet_subset`：incidenceSet_inter_i
ncidenceSet_subset (h : a != b) : G.incidenceSet a inter G.incidenceSet b subset
eq {s(a, b)}
· 使用定理 `SimpleGraph.Adj.ne`：∀ {V : Type u} {G : SimpleGraph V} {a b : V}, G.Adj 
a b → a ≠ b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `SimpleGraph.mk'_mem_incidenceSet_left_iff`：∀ {V : Type u} (G : SimpleGra
ph V) {a b : V}, s(a, b) ∈ G.incidenceSet a ↔ G.Adj a b
· 使用定理 `SimpleGraph.mk'_mem_incidenceSet_right_iff`：∀ {V : Type u} (G : SimpleGr
aph V) {a b : V}, s(a, b) ∈ G.incidenceSet b ↔ G.Adj a b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem incidenceSet_inter_incidenceSet_of_adj (h : G.Adj a b) :
    G.incidenceSet a ∩ G.incidenceSet b = {s(a, b)} := by
  refine (G.incidenceSet_inter_incidenceSet_subset <| h.ne).antisymm ?_
  rintro _ (rfl : _ = s(a, b))
  exact ⟨G.mk'_mem_incidenceSet_left_iff.2 h, G.mk'_mem_incidenceSet_right_iff.2 h⟩
/-
**SimpleGraph.adj_of_mem_incidenceSet** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：adj_of_mem_incidenceSet (h : a != b) (ha : e in G.incidenceSet a) (hb : e 
in G.incidenceSet b) : G.Adj a b
参数：h : a != b；ha : e in G.incidenceSet a；hb : e in G.incidenceSet b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SimpleGraph.mk'_mem_incidenceSet_left_iff`：∀ {V : Type u} (G : SimpleGra
ph V) {a b : V}, s(a, b) ∈ G.incidenceSet a ↔ G.Adj a b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.mem_singleton_iff`：mem_singleton_iff {a b : α} : a in ({b} : Set α) 
↔ a = b
· 使用定理 `SimpleGraph.incidenceSet_inter_incidenceSet_subset`：incidenceSet_inter_i
ncidenceSet_subset (h : a != b) : G.incidenceSet a inter G.incidenceSet b subset
eq {s(a, b)}
-/
theorem adj_of_mem_incidenceSet (h : a ≠ b) (ha : e ∈ G.incidenceSet a)
    (hb : e ∈ G.incidenceSet b) : G.Adj a b := by
  rwa [← mk'_mem_incidenceSet_left_iff, ←
    Set.mem_singleton_iff.1 <| G.incidenceSet_inter_incidenceSet_subset h ⟨ha, hb⟩]
/-
**SimpleGraph.incidenceSet_inter_incidenceSet_of_not_adj** 是 Mathlib 中的一个定理，位于命名
空间 `SimpleGraph`。
形式化陈述：incidenceSet_inter_incidenceSet_of_not_adj (h : ¬G.Adj a b) (hn : a != b) 
: G.incidenceSet a inter G.incidenceSet b = ∅
参数：h : ¬G.Adj a b；hn : a != b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.adj_of_mem_incidenceSet`：adj_of_mem_incidenceSet (h : a != b
) (ha : e in G.incidenceSet a) (hb : e in G.incidenceSet b) : G.Adj a b
-/
theorem incidenceSet_inter_incidenceSet_of_not_adj (h : ¬G.Adj a b) (hn : a ≠ b) :
    G.incidenceSet a ∩ G.incidenceSet b = ∅ := by
  simp_rw [Set.eq_empty_iff_forall_notMem, Set.mem_inter_iff, not_and]
  intro u ha hb
  exact h (G.adj_of_mem_incidenceSet hn ha hb)
/-
**SimpleGraph.decidableMemIncidenceSet** 是 Mathlib 中的一个实例，位于命名空间 `SimpleGraph`。
形式化陈述：decidableMemIncidenceSet [DecidableEq V] [DecidableRel G.Adj] (v : V) : De
cidablePred (· in G.incidenceSet v)
参数：v : V。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance decidableMemIncidenceSet [DecidableEq V] [DecidableRel G.Adj] (v : V) :
    DecidablePred (· ∈ G.incidenceSet v) :=
  inferInstanceAs <| DecidablePred fun e => e ∈ G.edgeSet ∧ v ∈ e

@[simp]
/-
**SimpleGraph.mem_neighborSet** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：mem_neighborSet (v w : V) : w in G.neighborSet v ↔ G.Adj v w
参数：v w : V。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_neighborSet (v w : V) : w ∈ G.neighborSet v ↔ G.Adj v w :=
  Iff.rfl
/-
**SimpleGraph.notMem_neighborSet_self** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
形式化陈述：notMem_neighborSet_self : a ∉ G.neighborSet a
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
lemma notMem_neighborSet_self : a ∉ G.neighborSet a := by simp

variable {G} in
/-
**SimpleGraph.nonempty_neighborSet** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：nonempty_neighborSet : (G.neighborSet v).Nonempty ↔ exists u, G.Adj v u
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem nonempty_neighborSet : (G.neighborSet v).Nonempty ↔ ∃ u, G.Adj v u :=
  .rfl

variable (v) in
/-
**SimpleGraph.neighborSet_subset_compl** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：neighborSet_subset_compl : G.neighborSet v subseteq {v}ᶜ
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem neighborSet_subset_compl : G.neighborSet v ⊆ {v}ᶜ := by
  simp

variable (v) in
/-
**SimpleGraph.neighborSet_ne_univ** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：neighborSet_ne_univ : G.neighborSet v != .univ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.ne_univ_iff_exists_notMem`：ne_univ_iff_exists_notMem {α : Type*} (s 
: Set α) : s != univ ↔ exists a, a ∉ s
· 使用引理 `SimpleGraph.notMem_neighborSet_self`：notMem_neighborSet_self : a ∉ G.nei
ghborSet a
-/
theorem neighborSet_ne_univ : G.neighborSet v ≠ .univ :=
  Set.ne_univ_iff_exists_notMem _ |>.mpr ⟨v, G.notMem_neighborSet_self⟩

variable {G H} in
/-
**SimpleGraph.disjoint_neighborSet** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：disjoint_neighborSet : (forall v, Disjoint (G.neighborSet v) (H.neighborSe
t v)) ↔ Disjoint G H
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem disjoint_neighborSet :
    (∀ v, Disjoint (G.neighborSet v) (H.neighborSet v)) ↔ Disjoint G H := by
  simp_rw [← disjoint_edgeSet, Set.disjoint_left, mem_neighborSet, Sym2.forall, mem_edgeSet]

@[simp]
/-
**SimpleGraph.neighborSet_sup** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：neighborSet_sup {G₁ G₂ : SimpleGraph V} (v : V) : (G₁ ⊔ G₂).neighborSet v 
= G₁.neighborSet v union G₂.neighborSet v
参数：v : V。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem neighborSet_sup {G₁ G₂ : SimpleGraph V} (v : V) :
    (G₁ ⊔ G₂).neighborSet v = G₁.neighborSet v ∪ G₂.neighborSet v :=
  rfl

@[simp]
/-
**SimpleGraph.neighborSet_inf** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：neighborSet_inf {G₁ G₂ : SimpleGraph V} (v : V) : (G₁ ⊓ G₂).neighborSet v 
= G₁.neighborSet v inter G₂.neighborSet v
参数：v : V。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem neighborSet_inf {G₁ G₂ : SimpleGraph V} (v : V) :
    (G₁ ⊓ G₂).neighborSet v = G₁.neighborSet v ∩ G₂.neighborSet v :=
  rfl

@[simp]
/-
**SimpleGraph.neighborSet_sdiff** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：neighborSet_sdiff {G₁ G₂ : SimpleGraph V} (v : V) : (G₁ \ G₂).neighborSet 
v = G₁.neighborSet v \ G₂.neighborSet v
参数：v : V。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem neighborSet_sdiff {G₁ G₂ : SimpleGraph V} (v : V) :
    (G₁ \ G₂).neighborSet v = G₁.neighborSet v \ G₂.neighborSet v :=
  rfl

@[simp]
/-
**SimpleGraph.neighborSet_iSup** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：neighborSet_iSup {s : ι -> SimpleGraph V} (v : V) : (⨆ i, s i).neighborSet
 v = ⋃ i, (s i).neighborSet v
参数：v : V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem neighborSet_iSup {s : ι → SimpleGraph V} (v : V) :
    (⨆ i, s i).neighborSet v = ⋃ i, (s i).neighborSet v := by
  ext; simp

@[simp]
/-
**SimpleGraph.neighborSet_iInf** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：neighborSet_iInf [Nonempty ι] {s : ι -> SimpleGraph V} (v : V) : (⨅ i, s i
).neighborSet v = ⋂ i, (s i).neighborSet v
参数：v : V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem neighborSet_iInf [Nonempty ι] {s : ι → SimpleGraph V} (v : V) :
    (⨅ i, s i).neighborSet v = ⋂ i, (s i).neighborSet v := by
  ext
  simp_rw [Set.mem_iInter, mem_neighborSet, iInf_adj_of_nonempty]

@[simp]
/-
**SimpleGraph.mem_incidenceSet** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：mem_incidenceSet (v w : V) : s(v, w) in G.incidenceSet v ↔ G.Adj v w
参数：v w : V。
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
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_incidenceSet (v w : V) : s(v, w) ∈ G.incidenceSet v ↔ G.Adj v w := by
  simp [incidenceSet]
/-
**SimpleGraph.mem_incidence_iff_neighbor** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`
。
形式化陈述：mem_incidence_iff_neighbor {v w : V} : s(v, w) in G.incidenceSet v ↔ w in 
G.neighborSet v
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_incidence_iff_neighbor {v w : V} :
    s(v, w) ∈ G.incidenceSet v ↔ w ∈ G.neighborSet v := by
  simp only [mem_incidenceSet, mem_neighborSet]
/-
**SimpleGraph.adj_incidenceSet_inter** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：adj_incidenceSet_inter {v : V} {e : Sym2 V} (he : e in G.edgeSet) (h : v i
n e) : G.incidenceSet v inter G.incidenceSet (Sym2.Mem.other h) = {e}
参数：he : e in G.edgeSet；h : v in e。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Sym2.other_spec`：other_spec {a : α} {z : Sym2 α} (h : a in z) : s(a, Mem
.other h) = z
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Sym2.mem_and_mem_iff`：mem_and_mem_iff {x y : α} {z : Sym2 α} (hne : x !=
 y) : x in z ∧ y in z ↔ z = s(x, y)
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `SimpleGraph.edge_other_ne`：edge_other_ne {e : Sym2 V} (he : e in G.edgeS
et) {v : V} (h : v in e) : Sym2.Mem.other h != v
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Sym2.other_mem`：other_mem {a : α} {z : Sym2 α} (h : a in z) : Mem.other 
h in z
-/
theorem adj_incidenceSet_inter {v : V} {e : Sym2 V} (he : e ∈ G.edgeSet) (h : v ∈ e) :
    G.incidenceSet v ∩ G.incidenceSet (Sym2.Mem.other h) = {e} := by
  ext e'
  simp only [incidenceSet, Set.mem_sep_iff, Set.mem_inter_iff, Set.mem_singleton_iff]
  refine ⟨fun h' => ?_, ?_⟩
  · rw [← Sym2.other_spec h]
    exact (Sym2.mem_and_mem_iff (edge_other_ne G he h).symm).mp ⟨h'.1.2, h'.2.2⟩
  · rintro rfl
    exact ⟨⟨he, h⟩, he, Sym2.other_mem _⟩
/-
**SimpleGraph.compl_neighborSet_disjoint** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`
。
形式化陈述：compl_neighborSet_disjoint (G : SimpleGraph V) (v : V) : Disjoint (G.neigh
borSet v) (Gᶜ.neighborSet v)
参数：G : SimpleGraph V；v : V。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.disjoint_iff`：∀ {α : Type u} {s t : Set α}, Disjoint s t ↔ s ∩ t ⊆ ∅
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `SimpleGraph.compl_adj`：compl_adj (G : SimpleGraph V) (v w : V) : Gᶜ.Adj 
v w ↔ v != w ∧ ¬G.Adj v w
· 使用定理 `SimpleGraph.mem_neighborSet`：mem_neighborSet (v w : V) : w in G.neighbor
Set v ↔ G.Adj v w
-/
theorem compl_neighborSet_disjoint (G : SimpleGraph V) (v : V) :
    Disjoint (G.neighborSet v) (Gᶜ.neighborSet v) := by
  rw [Set.disjoint_iff]
  rintro w ⟨h, h'⟩
  rw [mem_neighborSet, compl_adj] at h'
  exact h'.2 h
/-
**SimpleGraph.neighborSet_union_compl_neighborSet_eq** 是 Mathlib 中的一个定理，位于命名空间 `
SimpleGraph`。
形式化陈述：neighborSet_union_compl_neighborSet_eq (G : SimpleGraph V) (v : V) : G.nei
ghborSet v union Gᶜ.neighborSet v = {v}ᶜ
参数：G : SimpleGraph V；v : V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `SimpleGraph.ne_of_adj`：ne_of_adj (h : G.Adj a b) : a != b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Classical.or_iff_not_imp_left`：∀ {a b : Prop}, a ∨ b ↔ ¬a → b
-/
theorem neighborSet_union_compl_neighborSet_eq (G : SimpleGraph V) (v : V) :
    G.neighborSet v ∪ Gᶜ.neighborSet v = {v}ᶜ := by
  ext w
  have h := @ne_of_adj _ G
  simp_rw [Set.mem_union, mem_neighborSet, compl_adj, Set.mem_compl_iff, Set.mem_singleton_iff]
  tauto
/-
**SimpleGraph.card_neighborSet_union_compl_neighborSet** 是 Mathlib 中的一个定理，位于命名空间
 `SimpleGraph`。
形式化陈述：card_neighborSet_union_compl_neighborSet [Fintype V] (G : SimpleGraph V) (
v : V) [Fintype (G.neighborSet v union Gᶜ.neighborSet v : Set V)] : #(G.neighbor
Set v union Gᶜ.neighborSet v).toFinset = Fintype.card V - 1
参数：G : SimpleGraph V；v : V；G.neighborSet v union Gᶜ.neighborSet v : Set V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.toFinset_congr`：toFinset_congr {s t : Set α} [Fintype s] [Fintype t]
 (h : s = t) : toFinset s = toFinset t
· 使用定理 `SimpleGraph.neighborSet_union_compl_neighborSet_eq`：neighborSet_union_co
mpl_neighborSet_eq (G : SimpleGraph V) (v : V) : G.neighborSet v union Gᶜ.neighb
orSet v = {v}ᶜ
· 使用定理 `Set.toFinset_compl`：toFinset_compl [Fintype α] [Fintype (sᶜ : Set _)] : 
sᶜ.toFinset = s.toFinsetᶜ
· 使用定理 `Finset.card_compl`：Finset.card_compl [DecidableEq α] [Fintype α] (s : Fi
nset α) : #sᶜ = Fintype.card α - #s
· 使用定理 `Set.toFinset_card`：toFinset_card {α : Type*} (s : Set α) [Fintype s] : s
.toFinset.card = Fintype.card s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem card_neighborSet_union_compl_neighborSet [Fintype V] (G : SimpleGraph V) (v : V)
    [Fintype (G.neighborSet v ∪ Gᶜ.neighborSet v : Set V)] :
    #(G.neighborSet v ∪ Gᶜ.neighborSet v).toFinset = Fintype.card V - 1 := by
  classical simp_rw [neighborSet_union_compl_neighborSet_eq, Set.toFinset_compl,
      Finset.card_compl, Set.toFinset_card, Set.card_singleton]
/-
**SimpleGraph.neighborSet_compl** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：neighborSet_compl (G : SimpleGraph V) (v : V) : Gᶜ.neighborSet v = (G.neig
hborSet v)ᶜ \ {v}
参数：G : SimpleGraph V；v : V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem neighborSet_compl (G : SimpleGraph V) (v : V) :
    Gᶜ.neighborSet v = (G.neighborSet v)ᶜ \ {v} := by
  ext w
  simp [and_comm, eq_comm]

variable {G} in
@[gcongr]
/-
**SimpleGraph.neighborSet_mono** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：neighborSet_mono {G' : SimpleGraph V} (hle : G <= G') (v : V) : G.neighbor
Set v subseteq G'.neighborSet v
参数：hle : G <= G'；v : V。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem neighborSet_mono {G' : SimpleGraph V} (hle : G ≤ G') (v : V) :
    G.neighborSet v ⊆ G'.neighborSet v :=
  fun _ hadj ↦ hle hadj

@[simp]
/-
**SimpleGraph.neighborSet_top** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：neighborSet_top : neighborSet ⊤ v = {v}ᶜ
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem neighborSet_top : neighborSet ⊤ v = {v}ᶜ := by
  grind [mem_neighborSet, top_adj]
/-
**SimpleGraph.neighborSet_bot** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：neighborSet_bot : neighborSet ⊥ v = ∅
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem neighborSet_bot : neighborSet ⊥ v = ∅ := by
  grind [mem_neighborSet, bot_adj]

variable {G} in
/-
**SimpleGraph.Adj.nontrivial** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Adj`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} {u v : V}, G.Adj u v → Nontrivial V
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Adj.ne`：∀ {V : Type u} {G : SimpleGraph V} {a b : V}, G.Adj 
a b → a ≠ b
-/
theorem Adj.nontrivial (hadj : G.Adj u v) : Nontrivial V :=
  ⟨u, v, hadj.ne⟩

/-- The set of common neighbors between two vertices `v` and `w` in a graph `G` is the
intersection of the neighbor sets of `v` and `w`. -/
/-
**SimpleGraph.commonNeighbors** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph`。
形式化陈述：commonNeighbors (v w : V) : Set V
参数：v w : V。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The set of common neighbors between two vertices `v` and `w` in a graph `G` is t
he
intersection of the neighbor sets of `v` and `w`.
-/
def commonNeighbors (v w : V) : Set V :=
  G.neighborSet v ∩ G.neighborSet w
/-
**SimpleGraph.commonNeighbors_eq** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：commonNeighbors_eq (v w : V) : G.commonNeighbors v w = G.neighborSet v int
er G.neighborSet w
参数：v w : V。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem commonNeighbors_eq (v w : V) : G.commonNeighbors v w = G.neighborSet v ∩ G.neighborSet w :=
  rfl
/-
**SimpleGraph.mem_commonNeighbors** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：mem_commonNeighbors {u v w : V} : u in G.commonNeighbors v w ↔ G.Adj v u ∧
 G.Adj w u
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_commonNeighbors {u v w : V} : u ∈ G.commonNeighbors v w ↔ G.Adj v u ∧ G.Adj w u :=
  Iff.rfl
/-
**SimpleGraph.commonNeighbors_symm** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：commonNeighbors_symm (v w : V) : G.commonNeighbors v w = G.commonNeighbors
 w v
参数：v w : V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
-/
theorem commonNeighbors_symm (v w : V) : G.commonNeighbors v w = G.commonNeighbors w v :=
  Set.inter_comm _ _
/-
**SimpleGraph.notMem_commonNeighbors_left** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph
`。
形式化陈述：notMem_commonNeighbors_left (v w : V) : v ∉ G.commonNeighbors v w
参数：v w : V。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.ne_of_adj`：ne_of_adj (h : G.Adj a b) : a != b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem notMem_commonNeighbors_left (v w : V) : v ∉ G.commonNeighbors v w := fun h =>
  ne_of_adj G h.1 rfl
/-
**SimpleGraph.notMem_commonNeighbors_right** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGrap
h`。
形式化陈述：notMem_commonNeighbors_right (v w : V) : w ∉ G.commonNeighbors v w
参数：v w : V。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.ne_of_adj`：ne_of_adj (h : G.Adj a b) : a != b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem notMem_commonNeighbors_right (v w : V) : w ∉ G.commonNeighbors v w := fun h =>
  ne_of_adj G h.2 rfl
/-
**SimpleGraph.commonNeighbors_subset_neighborSet_left** 是 Mathlib 中的一个定理，位于命名空间 
`SimpleGraph`。
形式化陈述：commonNeighbors_subset_neighborSet_left (v w : V) : G.commonNeighbors v w 
subseteq G.neighborSet v
参数：v w : V。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
-/
theorem commonNeighbors_subset_neighborSet_left (v w : V) :
    G.commonNeighbors v w ⊆ G.neighborSet v :=
  Set.inter_subset_left
/-
**SimpleGraph.commonNeighbors_subset_neighborSet_right** 是 Mathlib 中的一个定理，位于命名空间
 `SimpleGraph`。
形式化陈述：commonNeighbors_subset_neighborSet_right (v w : V) : G.commonNeighbors v w
 subseteq G.neighborSet w
参数：v w : V。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
-/
theorem commonNeighbors_subset_neighborSet_right (v w : V) :
    G.commonNeighbors v w ⊆ G.neighborSet w :=
  Set.inter_subset_right
/-
**SimpleGraph.decidableMemCommonNeighbors** 是 Mathlib 中的一个实例，位于命名空间 `SimpleGraph
`。
形式化陈述：decidableMemCommonNeighbors [DecidableRel G.Adj] (v w : V) : DecidablePred
 (· in G.commonNeighbors v w)
参数：v w : V。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance decidableMemCommonNeighbors [DecidableRel G.Adj] (v w : V) :
    DecidablePred (· ∈ G.commonNeighbors v w) :=
  inferInstanceAs <| DecidablePred fun u => u ∈ G.neighborSet v ∧ u ∈ G.neighborSet w

variable {G H} in
/-
**SimpleGraph.disjoint_commonNeighbors** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：disjoint_commonNeighbors : (forall u v, Disjoint (G.commonNeighbors u v) (
H.commonNeighbors u v)) ↔ Disjoint G H
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
theorem disjoint_commonNeighbors :
    (∀ u v, Disjoint (G.commonNeighbors u v) (H.commonNeighbors u v)) ↔ Disjoint G H := by
  simp_rw [← disjoint_edgeSet, Set.disjoint_left, mem_commonNeighbors, Sym2.forall, mem_edgeSet]
  grind
/-
**SimpleGraph.commonNeighbors_top_eq** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：commonNeighbors_top_eq {v w : V} : (⊤ : SimpleGraph V).commonNeighbors v w
 = Set.univ \ {v, w}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `SimpleGraph.neighborSet_top`：neighborSet_top : neighborSet ⊤ v = {v}ᶜ
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem commonNeighbors_top_eq {v w : V} :
    (⊤ : SimpleGraph V).commonNeighbors v w = Set.univ \ {v, w} := by
  ext u
  simp [commonNeighbors, eq_comm, not_or]

@[simp]
/-
**SimpleGraph.commonNeighbors_bot_eq** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：commonNeighbors_bot_eq : commonNeighbors ⊥ u v = ∅
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `SimpleGraph.neighborSet_bot`：neighborSet_bot : neighborSet ⊥ v = ∅
· 使用定理 `Set.inter_self`：inter_self (a : Set α) : a inter a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem commonNeighbors_bot_eq : commonNeighbors ⊥ u v = ∅ := by
  simp [commonNeighbors, neighborSet_bot]

section Incidence

variable [DecidableEq V]

/-- Given an edge incident to a particular vertex, get the other vertex on the edge. -/
/-
**SimpleGraph.otherVertexOfIncident** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph`。
形式化陈述：otherVertexOfIncident {v : V} {e : Sym2 V} (h : e in G.incidenceSet v) : V
参数：h : e in G.incidenceSet v。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given an edge incident to a particular vertex, get the other vertex on the edge.
-/
def otherVertexOfIncident {v : V} {e : Sym2 V} (h : e ∈ G.incidenceSet v) : V :=
  Sym2.Mem.other' h.2
/-
**SimpleGraph.edge_other_incident_set** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：edge_other_incident_set {v : V} {e : Sym2 V} (h : e in G.incidenceSet v) :
 e in G.incidenceSet (G.otherVertexOfIncident h)
参数：h : e in G.incidenceSet v。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
-/
theorem edge_other_incident_set {v : V} {e : Sym2 V} (h : e ∈ G.incidenceSet v) :
    e ∈ G.incidenceSet (G.otherVertexOfIncident h) := by
  use h.1
  simp [otherVertexOfIncident, Sym2.other_mem']
/-
**SimpleGraph.incidence_other_prop** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：incidence_other_prop {v : V} {e : Sym2 V} (h : e in G.incidenceSet v) : G.
otherVertexOfIncident h in G.neighborSet v
参数：h : e in G.incidenceSet v。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.mem_edgeSet`：mem_edgeSet : s(v, w) in G.edgeSet ↔ G.Adj v w
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Sym2.other_spec'`：other_spec' [DecidableEq α] {a : α} {z : Sym2 α} (h : 
a in z) : s(a, Mem.other' h) = z
-/
theorem incidence_other_prop {v : V} {e : Sym2 V} (h : e ∈ G.incidenceSet v) :
    G.otherVertexOfIncident h ∈ G.neighborSet v := by
  obtain ⟨he, hv⟩ := h
  rwa [← Sym2.other_spec' hv, mem_edgeSet] at he

@[simp]
/-
**SimpleGraph.incidence_other_neighbor_edge** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGra
ph`。
形式化陈述：incidence_other_neighbor_edge {v w : V} (h : w in G.neighborSet v) : G.oth
erVertexOfIncident (G.mem_incidence_iff_neighbor.mpr h) = w
参数：h : w in G.neighborSet v。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `SimpleGraph.mem_incidence_iff_neighbor`：mem_incidence_iff_neighbor {v w 
: V} : s(v, w) in G.incidenceSet v ↔ w in G.neighborSet v
· 使用定理 `Sym2.congr_right`：congr_right {a b c : α} : s(a, b) = s(a, c) ↔ b = c
· 使用定理 `Sym2.other_spec'`：other_spec' [DecidableEq α] {a : α} {z : Sym2 α} (h : 
a in z) : s(a, Mem.other' h) = z
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem incidence_other_neighbor_edge {v w : V} (h : w ∈ G.neighborSet v) :
    G.otherVertexOfIncident (G.mem_incidence_iff_neighbor.mpr h) = w :=
  Sym2.congr_right.mp (Sym2.other_spec' (G.mem_incidence_iff_neighbor.mpr h).right)

/-- There is an equivalence between the set of edges incident to a given
vertex and the set of vertices adjacent to the vertex. -/
@[simps]
/-
**SimpleGraph.incidenceSetEquivNeighborSet** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGrap
h`。
形式化陈述：incidenceSetEquivNeighborSet (v : V) : G.incidenceSet v ≃ G.neighborSet v 
where toFun e
参数：v : V。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
There is an equivalence between the set of edges incident to a given
vertex and the set of vertices adjacent to the vertex.
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

/-- The condition that the portion of the simple graph `G` _between_ `s` and `t` is complete, that
is, every vertex in `s` is adjacent to every vertex in `t`, and vice versa. -/
/-
**SimpleGraph.IsCompleteBetween** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph`。
形式化陈述：IsCompleteBetween (G : SimpleGraph V) (s t : Set V)
参数：G : SimpleGraph V；s t : Set V。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The condition that the portion of the simple graph `G` _between_ `s` and `t` is 
complete, that
is, every vertex in `s` is adjacent to every vertex in `t`, and vice versa.
-/
def IsCompleteBetween (G : SimpleGraph V) (s t : Set V) :=
  ∀ ⦃v₁⦄, v₁ ∈ s → ∀ ⦃v₂⦄, v₂ ∈ t → G.Adj v₁ v₂
/-
**SimpleGraph.IsCompleteBetween.disjoint** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.
IsCompleteBetween`。
形式化陈述：∀ {V : Type u} (G : SimpleGraph V) {s t : Set V}, G.IsCompleteBetween s t 
→ Disjoint s t
参数：G : SimpleGraph V。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.disjoint_left`：disjoint_left : Disjoint s t ↔ forall ⦃a⦄, a in s -> 
a ∉ t
· 使用定理 `SimpleGraph.irrefl`：∀ {V : Type u} (G : SimpleGraph V) {v : V}, ¬G.Adj v
 v
-/
theorem IsCompleteBetween.disjoint (h : G.IsCompleteBetween s t) : Disjoint s t :=
  Set.disjoint_left.mpr fun _v hv₁ hv₂ ↦ G.irrefl (h hv₁ hv₂)
/-
**SimpleGraph.isCompleteBetween_comm** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：isCompleteBetween_comm : G.IsCompleteBetween s t ↔ G.IsCompleteBetween t s
 where mp h _ h₁ _ h₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Adj.symm`：∀ {V : Type u} {G : SimpleGraph V} {u v : V}, G.Ad
j u v → G.Adj v u
-/
theorem isCompleteBetween_comm : G.IsCompleteBetween s t ↔ G.IsCompleteBetween t s where
  mp h _ h₁ _ h₂ := (h h₂ h₁).symm
  mpr h _ h₁ _ h₂ := (h h₂ h₁).symm

alias ⟨IsCompleteBetween.symm, _⟩ := isCompleteBetween_comm

end IsCompleteBetween

section Subsingleton

/-
**SimpleGraph.subsingleton_iff** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：∀ {V : Type u}, Subsingleton (SimpleGraph V) ↔ Subsingleton V
参数：SimpleGraph V。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `SimpleGraph.instNontrivial`：∀ {V : Type u} [Nontrivial V], Nontrivial (S
impleGraph V)
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
-/
protected theorem subsingleton_iff : Subsingleton (SimpleGraph V) ↔ Subsingleton V := by
  refine ⟨fun h ↦ ?_, fun _ ↦ Unique.instSubsingleton⟩
  contrapose! h
  exact instNontrivial
/-
**SimpleGraph.nontrivial_iff** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：∀ {V : Type u}, Nontrivial (SimpleGraph V) ↔ Nontrivial V
参数：SimpleGraph V。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `SimpleGraph.instNontrivial`：∀ {V : Type u} [Nontrivial V], Nontrivial (S
impleGraph V)
-/
protected theorem nontrivial_iff : Nontrivial (SimpleGraph V) ↔ Nontrivial V := by
  refine ⟨fun h ↦ ?_, fun _ ↦ instNontrivial⟩
  contrapose! h
  exact Unique.instSubsingleton

end Subsingleton

/-- A vertex in a graph is isolated if it's adjacent to no other vertex. -/
/-
**SimpleGraph.IsIsolated** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph`。
形式化陈述：IsIsolated (G : SimpleGraph V) (v : V) : Prop
参数：G : SimpleGraph V；v : V。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A vertex in a graph is isolated if it's adjacent to no other vertex.
-/
def IsIsolated (G : SimpleGraph V) (v : V) : Prop := ∀ w, ¬ G.Adj v w
/-
**SimpleGraph.neighborSet_eq_empty** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：∀ {V : Type u} (G : SimpleGraph V) {v : V}, G.neighborSet v = ∅ ↔ G.IsIsol
ated v
参数：G : SimpleGraph V。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_false`：∀ (p : Prop), (p ↔ False) = ¬p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma neighborSet_eq_empty : G.neighborSet v = ∅ ↔ G.IsIsolated v := by
  simp [neighborSet, IsIsolated, Set.ext_iff]
/-
**SimpleGraph.neighborSet_nonempty** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：∀ {V : Type u} (G : SimpleGraph V) {v : V}, (G.neighborSet v).Nonempty ↔ ¬
G.IsIsolated v
参数：G : SimpleGraph V；G.neighborSet v。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma neighborSet_nonempty : (G.neighborSet v).Nonempty ↔ ¬ G.IsIsolated v := by
  simp [Set.nonempty_iff_ne_empty]

protected alias ⟨IsIsolated.of_neighborSet_eq_empty, IsIsolated.neighborSet_eq_empty⟩ :=
  neighborSet_eq_empty

attribute [simp] IsIsolated.neighborSet_eq_empty
/-
**SimpleGraph.mem_support_iff_not_isIsolated** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGr
aph`。
形式化陈述：mem_support_iff_not_isIsolated : v in G.support ↔ ¬ G.IsIsolated v
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma mem_support_iff_not_isIsolated : v ∈ G.support ↔ ¬ G.IsIsolated v := by
  simp [mem_support, IsIsolated]

@[simp]
/-
**SimpleGraph.notMem_support_iff_isIsolated** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGra
ph`。
形式化陈述：notMem_support_iff_isIsolated : v ∉ G.support ↔ G.IsIsolated v
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem notMem_support_iff_isIsolated : v ∉ G.support ↔ G.IsIsolated v := by
  simp [mem_support_iff_not_isIsolated]

variable {G} in
/-
**SimpleGraph.exists_adj_iff_not_isIsolated** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGra
ph`。
形式化陈述：exists_adj_iff_not_isIsolated : (exists u, G.Adj v u) ↔ ¬G.IsIsolated v
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem exists_adj_iff_not_isIsolated : (∃ u, G.Adj v u) ↔ ¬G.IsIsolated v := by
  simp [IsIsolated]

@[simp]
/-
**SimpleGraph.IsIsolated.of_subsingleton** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.
IsIsolated`。
形式化陈述：∀ {V : Type u} [Subsingleton V] (G : SimpleGraph V) (v : V), G.IsIsolated 
v
参数：G : SimpleGraph V；v : V。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `not_nontrivial`：not_nontrivial (α) [Subsingleton α] : ¬Nontrivial α
· 使用定理 `SimpleGraph.Adj.nontrivial`：∀ {V : Type u} {G : SimpleGraph V} {u v : V}
, G.Adj u v → Nontrivial V
-/
theorem IsIsolated.of_subsingleton [Subsingleton V] (G : SimpleGraph V) (v : V) :
    G.IsIsolated v :=
  fun _ hadj ↦ not_nontrivial V hadj.nontrivial

variable {G} in
/-
**SimpleGraph.nontrivial_of_not_isIsolated** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGrap
h`。
形式化陈述：nontrivial_of_not_isIsolated (h : ¬G.IsIsolated v) : Nontrivial V
参数：h : ¬G.IsIsolated v。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Exists.elim`：∀ {α : Sort u} {p : α → Prop} {b : Prop}, (∃ x, p x) → (∀ (
a : α), p a → b) → b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `SimpleGraph.exists_adj_iff_not_isIsolated`：exists_adj_iff_not_isIsolated
 : (exists u, G.Adj v u) ↔ ¬G.IsIsolated v
· 使用定理 `SimpleGraph.Adj.nontrivial`：∀ {V : Type u} {G : SimpleGraph V} {u v : V}
, G.Adj u v → Nontrivial V
-/
theorem nontrivial_of_not_isIsolated (h : ¬G.IsIsolated v) : Nontrivial V :=
  exists_adj_iff_not_isIsolated.mpr h |>.elim fun _ ↦ Adj.nontrivial

variable {G} in
/-
**SimpleGraph.Adj.not_isIsolated_left** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Adj
`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} {u v : V}, G.Adj u v → ¬G.IsIsolated u
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `SimpleGraph.exists_adj_iff_not_isIsolated`：exists_adj_iff_not_isIsolated
 : (exists u, G.Adj v u) ↔ ¬G.IsIsolated v
-/
theorem Adj.not_isIsolated_left (h : G.Adj u v) : ¬G.IsIsolated u :=
  exists_adj_iff_not_isIsolated.mp ⟨_, h⟩

variable {G} in
/-
**SimpleGraph.Adj.not_isIsolated_right** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Ad
j`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} {u v : V}, G.Adj u v → ¬G.IsIsolated v
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Adj.not_isIsolated_left`：∀ {V : Type u} {G : SimpleGraph V} 
{u v : V}, G.Adj u v → ¬G.IsIsolated u
· 使用定理 `SimpleGraph.Adj.symm`：∀ {V : Type u} {G : SimpleGraph V} {u v : V}, G.Ad
j u v → G.Adj v u
-/
theorem Adj.not_isIsolated_right (h : G.Adj u v) : ¬G.IsIsolated v :=
  h.symm.not_isIsolated_left

@[simp]
/-
**SimpleGraph.IsIsolated.bot** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.IsIsolated`。
形式化陈述：∀ {V : Type u} {v : V}, ⊥.IsIsolated v
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `SimpleGraph.neighborSet_eq_empty`：∀ {V : Type u} (G : SimpleGraph V) {v 
: V}, G.neighborSet v = ∅ ↔ G.IsIsolated v
· 使用定理 `SimpleGraph.neighborSet_bot`：neighborSet_bot : neighborSet ⊥ v = ∅
-/
protected theorem IsIsolated.bot : IsIsolated ⊥ v :=
  neighborSet_eq_empty _ |>.mp neighborSet_bot

@[deprecated (since := "2026-06-19")]
alias isIsolated_bot := IsIsolated.bot
/-
**SimpleGraph.eq_bot_iff_isIsolated** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：eq_bot_iff_isIsolated : G = ⊥ ↔ forall v, G.IsIsolated v
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem eq_bot_iff_isIsolated : G = ⊥ ↔ ∀ v, G.IsIsolated v := by
  simp [eq_bot_iff_forall_not_adj, ← neighborSet_eq_empty, Set.eq_empty_iff_forall_notMem]

section IsUniversal

variable {G}

/-- A vertex in a graph is universal if it's adjacent to every other vertex. -/
/-
**SimpleGraph.IsUniversal** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph`。
形式化陈述：IsUniversal (G : SimpleGraph V) (v : V) : Prop
参数：G : SimpleGraph V；v : V。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A vertex in a graph is universal if it's adjacent to every other vertex.
-/
def IsUniversal (G : SimpleGraph V) (v : V) : Prop := ∀ ⦃w⦄, v ≠ w → G.Adj v w
/-
**SimpleGraph.insert_neighborSet_eq_univ** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`
。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} {v : V}, insert v (G.neighborSet v) = S
et.univ ↔ G.IsUniversal v
参数：G.neighborSet v。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
-/
@[simp] lemma insert_neighborSet_eq_univ :
    insert v (G.neighborSet v) = Set.univ ↔ G.IsUniversal v := by
  simp only [Set.ext_iff, Set.mem_insert_iff, mem_neighborSet, IsUniversal]
  grind
/-
**SimpleGraph.neighborSet_eq_compl_singleton** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGr
aph`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} {v : V}, G.neighborSet v = {v}ᶜ ↔ G.IsU
niversal v
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma neighborSet_eq_compl_singleton : G.neighborSet v = {v}ᶜ ↔ G.IsUniversal v := by
  grind [insert_neighborSet_eq_univ, notMem_neighborSet_self]

protected alias ⟨IsUniversal.of_neighborSet_eq, IsUniversal.neighborSet_eq⟩ :=
  neighborSet_eq_compl_singleton

@[simp]
/-
**SimpleGraph.IsUniversal.of_subsingleton** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph
.IsUniversal`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} {v : V} [Subsingleton V], G.IsUniversal
 v
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
-/
theorem IsUniversal.of_subsingleton [Subsingleton V] : G.IsUniversal v :=
  fun _ hne ↦ False.elim <| hne (Subsingleton.elim ..)
/-
**SimpleGraph.IsUniversal.not_isIsolated** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.
IsUniversal`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} {v : V} [Nontrivial V], G.IsUniversal v
 → ∀ (w : V), ¬G.IsIsolated w
参数：w : V。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_ne`：exists_ne [Nontrivial α] (x : α) : exists y, y != x
· 使用定理 `SimpleGraph.Adj.not_isIsolated_left`：∀ {V : Type u} {G : SimpleGraph V} 
{u v : V}, G.Adj u v → ¬G.IsIsolated u
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `SimpleGraph.Adj.not_isIsolated_right`：∀ {V : Type u} {G : SimpleGraph V}
 {u v : V}, G.Adj u v → ¬G.IsIsolated v
-/
theorem IsUniversal.not_isIsolated [Nontrivial V] (h : G.IsUniversal v) (w : V) :
    ¬G.IsIsolated w := by
  by_cases h' : v = w
  · obtain ⟨u, hu⟩ := exists_ne v
    exact h' ▸ Adj.not_isIsolated_left (h hu.symm)
  · exact Adj.not_isIsolated_right (h h')
/-
**SimpleGraph.IsIsolated.not_isUniversal** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.
IsIsolated`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} {v : V} [Nontrivial V], G.IsIsolated v 
→ ∀ (w : V), ¬G.IsUniversal w
参数：w : V。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₃`：contrapose₃ {p q : Prop} : (q -> 
¬ p) -> (p -> ¬ q)
· 使用定理 `SimpleGraph.IsUniversal.not_isIsolated`：∀ {V : Type u} {G : SimpleGraph 
V} {v : V} [Nontrivial V], G.IsUniversal v → ∀ (w : V), ¬G.IsIsolated w
-/
theorem IsIsolated.not_isUniversal [Nontrivial V] (h : G.IsIsolated v) (w : V) :
    ¬G.IsUniversal w := by
  contrapose! h
  exact h.not_isIsolated v

@[simp]
/-
**SimpleGraph.isUniversal_compl_iff_isIsolated** 是 Mathlib 中的一个定理，位于命名空间 `Simple
Graph`。
形式化陈述：isUniversal_compl_iff_isIsolated : Gᶜ.IsUniversal v ↔ G.IsIsolated v
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `SimpleGraph.Adj.ne`：∀ {V : Type u} {G : SimpleGraph V} {a b : V}, G.Adj 
a b → a ≠ b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
-/
theorem isUniversal_compl_iff_isIsolated : Gᶜ.IsUniversal v ↔ G.IsIsolated v := by
  refine ⟨fun h x hx ↦ ?_, fun h x hx ↦ ?_⟩
  · simpa [hx] using h hx.ne
  · simpa [hx] using h x

alias ⟨IsIsolated.of_isUniversal_compl, _⟩ := isUniversal_compl_iff_isIsolated

@[simp]
/-
**SimpleGraph.isIsolated_compl_iff_isUniversal** 是 Mathlib 中的一个定理，位于命名空间 `Simple
Graph`。
形式化陈述：isIsolated_compl_iff_isUniversal : Gᶜ.IsIsolated v ↔ G.IsUniversal v
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `compl_compl`：compl_compl (x : α) : xᶜᶜ = x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `SimpleGraph.isUniversal_compl_iff_isIsolated`：isUniversal_compl_iff_isIs
olated : Gᶜ.IsUniversal v ↔ G.IsIsolated v
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
-/
theorem isIsolated_compl_iff_isUniversal : Gᶜ.IsIsolated v ↔ G.IsUniversal v := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · simpa using isUniversal_compl_iff_isIsolated.mpr h
  · exact isUniversal_compl_iff_isIsolated.mp (by simpa)

alias ⟨IsUniversal.of_isIsolated_compl, _⟩ := isIsolated_compl_iff_isUniversal
/-
**SimpleGraph.eq_top_iff_forall_isUniversal** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGra
ph`。
形式化陈述：eq_top_iff_forall_isUniversal : G = ⊤ ↔ forall v, G.IsUniversal v
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem eq_top_iff_forall_isUniversal : G = ⊤ ↔ ∀ v, G.IsUniversal v := by
  simp [eq_top_iff_forall_ne_adj, IsUniversal]

@[simp]
/-
**SimpleGraph.IsUniversal.top** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.IsUniversal
`。
形式化陈述：∀ {V : Type u} {v : V}, ⊤.IsUniversal v
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `SimpleGraph.eq_top_iff_forall_isUniversal`：eq_top_iff_forall_isUniversal
 : G = ⊤ ↔ forall v, G.IsUniversal v
-/
protected theorem IsUniversal.top : IsUniversal ⊤ v :=
  eq_top_iff_forall_isUniversal.mp rfl v

end IsUniversal

end SimpleGraph

