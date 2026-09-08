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
relation that is symmetric and is supported by the vertex subset.  They also form a bounded lattice.

Thinking of `V → V → Prop` as `Set (V × V)`, a set of darts (i.e., half-edges), then
`Subgraph.adj_sub` is that the darts of a subgraph are a subset of the darts of `G`. -/
@[ext]
/-
**SimpleGraph.Subgraph** 是 Mathlib 中的一个结构，位于命名空间 `SimpleGraph`。
形式化陈述：Subgraph {V : Type u} (G : SimpleGraph V) where /-- Vertices of the subgra
ph -/ verts : Set V /-- Edges of the subgraph -/ Adj : V -> V -> Prop adj_sub : 
forall {v w : V}, Adj v w -> G.Adj v w edge_vert : forall {v w : V}, Adj v w -> 
v in verts symm : Std.Symm Adj
参数：G : SimpleGraph V。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A subgraph of a `SimpleGraph` is a subset of vertices along with a restriction o
f the adjacency
relation that is symmetric and is supported by the vertex subset.  They also for
m a bounded lattice.

Thinking of `V → V → Prop` as `Set (V × V)`, a set of darts (i.e., half-edges), 
then
`Subgraph.adj_sub` is that the darts of a subgraph are a subset of the darts of 
`G`.
-/
structure Subgraph {V : Type u} (G : SimpleGraph V) where
  /-- Vertices of the subgraph -/
  verts : Set V
  /-- Edges of the subgraph -/
  Adj : V → V → Prop
  adj_sub : ∀ {v w : V}, Adj v w → G.Adj v w
  edge_vert : ∀ {v w : V}, Adj v w → v ∈ verts
  symm : Std.Symm Adj := by aesop_graph

initialize_simps_projections SimpleGraph.Subgraph (Adj → adj)

variable {ι : Sort*} {V : Type u} {W : Type v}

/-- The one-vertex subgraph. -/
@[simps]
/-
**SimpleGraph.singletonSubgraph** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph`。
形式化陈述：{V : Type u} → (G : SimpleGraph V) → V → G.Subgraph
参数：G : SimpleGraph V。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The one-vertex subgraph.
-/
protected def singletonSubgraph (G : SimpleGraph V) (v : V) : G.Subgraph where
  verts := {v}
  Adj := ⊥
  adj_sub := False.elim
  edge_vert := False.elim

/-- The one-edge subgraph. -/
@[simps]
/-
**SimpleGraph.subgraphOfAdj** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph`。
形式化陈述：subgraphOfAdj (G : SimpleGraph V) {v w : V} (hvw : G.Adj v w) : G.Subgraph
 where verts
参数：G : SimpleGraph V；hvw : G.Adj v w。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The one-edge subgraph.
-/
def subgraphOfAdj (G : SimpleGraph V) {v w : V} (hvw : G.Adj v w) : G.Subgraph where
  verts := {v, w}
  Adj a b := s(v, w) = s(a, b)
  adj_sub h := by
    rw [← G.mem_edgeSet, ← h]
    exact hvw
  edge_vert {a b} h := by
    apply_fun fun e ↦ a ∈ e at h
    simp only [Sym2.mem_iff, true_or, eq_iff_iff, iff_true] at h
    exact h

namespace Subgraph

variable {G : SimpleGraph V} {G₁ G₂ : G.Subgraph} {a b : V}

/-
**SimpleGraph.Subgraph.loopless** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Subgraph`
。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} (G' : G.Subgraph), Std.Irrefl G'.Adj
参数：G' : G.Subgraph。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.irrefl`：∀ {V : Type u} (G : SimpleGraph V) {v : V}, ¬G.Adj v
 v
· 使用定理 `SimpleGraph.Subgraph.adj_sub`：∀ {V : Type u} {G : SimpleGraph V} (self :
 G.Subgraph) {v w : V}, self.Adj v w → G.Adj v w
-/
protected theorem loopless (G' : Subgraph G) : Std.Irrefl G'.Adj where
  irrefl _ hadj := G.irrefl <| G'.adj_sub hadj
/-
**SimpleGraph.Subgraph.adj_comm** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Subgraph`
。
形式化陈述：adj_comm (G' : Subgraph G) (v w : V) : G'.Adj v w ↔ G'.Adj w v
参数：G' : Subgraph G；v w : V。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Std.Symm.iff`：∀ {α : Type u_1} {r : α → α → Prop} [Std.Symm r] (x y : α)
, r x y ↔ r y x
· 使用定理 `SimpleGraph.Subgraph.symm`：∀ {V : Type u} {G : SimpleGraph V} (self : G.
Subgraph), Std.Symm self.Adj
-/
theorem adj_comm (G' : Subgraph G) (v w : V) : G'.Adj v w ↔ G'.Adj w v :=
  G'.symm.iff v w

@[symm]
/-
**SimpleGraph.Subgraph.adj_symm** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Subgraph`
。
形式化陈述：adj_symm (G' : Subgraph G) {u v : V} (h : G'.Adj u v) : G'.Adj v u
参数：G' : Subgraph G；h : G'.Adj u v。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Std.Symm.symm`：∀ {α : Sort u} {r : α → α → Prop} [self : Std.Symm r] (a 
b : α), r a b → r b a
· 使用定理 `SimpleGraph.Subgraph.symm`：∀ {V : Type u} {G : SimpleGraph V} (self : G.
Subgraph), Std.Symm self.Adj
-/
theorem adj_symm (G' : Subgraph G) {u v : V} (h : G'.Adj u v) : G'.Adj v u :=
  G'.symm.symm u v h
/-
**SimpleGraph.Subgraph.Adj.symm** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Subgraph.
Adj`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} {G' : G.Subgraph} {u v : V}, G'.Adj u v
 → G'.Adj v u
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Subgraph.adj_symm`：adj_symm (G' : Subgraph G) {u v : V} (h :
 G'.Adj u v) : G'.Adj v u
-/
protected theorem Adj.symm {G' : Subgraph G} {u v : V} (h : G'.Adj u v) : G'.Adj v u :=
  G'.adj_symm h

@[grind →]
/-
**SimpleGraph.Subgraph.Adj.adj_sub** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Subgra
ph.Adj`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} {H : G.Subgraph} {u v : V}, H.Adj u v →
 G.Adj u v
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Subgraph.adj_sub`：∀ {V : Type u} {G : SimpleGraph V} (self :
 G.Subgraph) {v w : V}, self.Adj v w → G.Adj v w
-/
protected theorem Adj.adj_sub {H : G.Subgraph} {u v : V} (h : H.Adj u v) : G.Adj u v :=
  H.adj_sub h
/-
**SimpleGraph.Subgraph.Adj.fst_mem** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Subgra
ph.Adj`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} {H : G.Subgraph} {u v : V}, H.Adj u v →
 u ∈ H.verts
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Subgraph.edge_vert`：∀ {V : Type u} {G : SimpleGraph V} (self
 : G.Subgraph) {v w : V}, self.Adj v w → v ∈ self.verts
-/
protected theorem Adj.fst_mem {H : G.Subgraph} {u v : V} (h : H.Adj u v) : u ∈ H.verts :=
  H.edge_vert h
/-
**SimpleGraph.Subgraph.Adj.snd_mem** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Subgra
ph.Adj`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} {H : G.Subgraph} {u v : V}, H.Adj u v →
 v ∈ H.verts
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Subgraph.Adj.fst_mem`：∀ {V : Type u} {G : SimpleGraph V} {H 
: G.Subgraph} {u v : V}, H.Adj u v → u ∈ H.verts
· 使用定理 `SimpleGraph.Subgraph.Adj.symm`：∀ {V : Type u} {G : SimpleGraph V} {G' : 
G.Subgraph} {u v : V}, G'.Adj u v → G'.Adj v u
-/
protected theorem Adj.snd_mem {H : G.Subgraph} {u v : V} (h : H.Adj u v) : v ∈ H.verts :=
  h.symm.fst_mem
/-
**SimpleGraph.Subgraph.Adj.ne** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Subgraph.Ad
j`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} {H : G.Subgraph} {u v : V}, H.Adj u v →
 u ≠ v
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Adj.ne`：∀ {V : Type u} {G : SimpleGraph V} {a b : V}, G.Adj 
a b → a ≠ b
· 使用定理 `SimpleGraph.Subgraph.Adj.adj_sub`：∀ {V : Type u} {G : SimpleGraph V} {H 
: G.Subgraph} {u v : V}, H.Adj u v → G.Adj u v
-/
protected theorem Adj.ne {H : G.Subgraph} {u v : V} (h : H.Adj u v) : u ≠ v :=
  h.adj_sub.ne
/-
**SimpleGraph.Subgraph.adj_congr_of_sym2** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.
Subgraph`。
形式化陈述：adj_congr_of_sym2 {H : G.Subgraph} {u v w x : V} (h2 : s(u, v) = s(w, x)) 
: H.Adj u v ↔ H.Adj w x
参数：h2 : s(u, v) = s(w, x)。
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
· 使用定理 `SimpleGraph.Subgraph.adj_comm`：adj_comm (G' : Subgraph G) (v w : V) : G'
.Adj v w ↔ G'.Adj w v
-/
theorem adj_congr_of_sym2 {H : G.Subgraph} {u v w x : V} (h2 : s(u, v) = s(w, x)) :
    H.Adj u v ↔ H.Adj w x := by
  simp only [Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk] at h2
  rcases h2 with hl | hr
  · rw [hl.1, hl.2]
  · rw [hr.1, hr.2, Subgraph.adj_comm]

/-- Coercion from `G' : Subgraph G` to a `SimpleGraph G'.verts`. -/
@[simps]
/-
**SimpleGraph.Subgraph.coe** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph.Subgraph`。
形式化陈述：{V : Type u} → {G : SimpleGraph V} → (G' : G.Subgraph) → SimpleGraph ↑G'.v
erts
参数：G' : G.Subgraph。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Coercion from `G' : Subgraph G` to a `SimpleGraph G'.verts`.
-/
protected def coe (G' : Subgraph G) : SimpleGraph G'.verts where
  Adj v w := G'.Adj v w
  symm := G'.symm.comap Subtype.val
  loopless.irrefl _ hadj := G.irrefl hadj.adj_sub

@[simp]
/-
**SimpleGraph.Subgraph.Adj.adj_sub'** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Subgr
aph.Adj`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} (G' : G.Subgraph) (u v : ↑G'.verts), G'
.Adj ↑u ↑v → G.Adj ↑u ↑v
参数：G' : G.Subgraph；u v : ↑G'.verts。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Subgraph.adj_sub`：∀ {V : Type u} {G : SimpleGraph V} (self :
 G.Subgraph) {v w : V}, self.Adj v w → G.Adj v w
-/
theorem Adj.adj_sub' (G' : Subgraph G) (u v : G'.verts) (h : G'.Adj u v) : G.Adj u v :=
  G'.adj_sub h
/-
**SimpleGraph.Subgraph.coe_adj_sub** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Subgra
ph`。
形式化陈述：coe_adj_sub (G' : Subgraph G) (u v : G'.verts) (h : G'.coe.Adj u v) : G.Ad
j u v
参数：G' : Subgraph G；u v : G'.verts；h : G'.coe.Adj u v。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Subgraph.adj_sub`：∀ {V : Type u} {G : SimpleGraph V} (self :
 G.Subgraph) {v w : V}, self.Adj v w → G.Adj v w
-/
theorem coe_adj_sub (G' : Subgraph G) (u v : G'.verts) (h : G'.coe.Adj u v) : G.Adj u v :=
  G'.adj_sub h

-- Given `h : H.Adj u v`, then `h.coe : H.coe.Adj ⟨u, _⟩ ⟨v, _⟩`.
/-
**SimpleGraph.Subgraph.Adj.coe** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Subgraph.A
dj`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} {H : G.Subgraph} {u v : V} (h : H.Adj u
 v), H.coe.Adj ⟨u, ⋯⟩ ⟨v, ⋯⟩
参数：h : H.Adj u v。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem Adj.coe {H : G.Subgraph} {u v : V} (h : H.Adj u v) :
    H.coe.Adj ⟨u, H.edge_vert h⟩ ⟨v, H.edge_vert h.symm⟩ := h
/-
**SimpleGraph.Subgraph.** 是 Mathlib 中的一个实例，位于命名空间 `SimpleGraph.Subgraph`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (G : SimpleGraph V) (H : Subgraph G) [DecidableRel H.Adj] : DecidableRel H.coe.Adj :=
  fun a b ↦ ‹DecidableRel H.Adj› _ _

/-- A subgraph is called a *spanning subgraph* if it contains all the vertices of `G`. -/
/-
**SimpleGraph.Subgraph.IsSpanning** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph.Subgrap
h`。
形式化陈述：IsSpanning (G' : Subgraph G) : Prop
参数：G' : Subgraph G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A subgraph is called a *spanning subgraph* if it contains all the vertices of `G
`.
-/
def IsSpanning (G' : Subgraph G) : Prop :=
  ∀ v : V, v ∈ G'.verts
/-
**SimpleGraph.Subgraph.isSpanning_iff** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Sub
graph`。
形式化陈述：isSpanning_iff {G' : Subgraph G} : G'.IsSpanning ↔ G'.verts = Set.univ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Set.eq_univ_iff_forall`：eq_univ_iff_forall {s : Set α} : s = univ ↔ fora
ll x, x in s
-/
theorem isSpanning_iff {G' : Subgraph G} : G'.IsSpanning ↔ G'.verts = Set.univ :=
  Set.eq_univ_iff_forall.symm

protected alias ⟨IsSpanning.verts_eq_univ, _⟩ := isSpanning_iff

/-- Coercion from `Subgraph G` to `SimpleGraph V`.  If `G'` is a spanning
subgraph, then `G'.spanningCoe` yields an isomorphic graph.
In general, this adds in all vertices from `V` as isolated vertices. -/
@[simps]
/-
**SimpleGraph.Subgraph.spanningCoe** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph.Subgra
ph`。
形式化陈述：{V : Type u} → {G : SimpleGraph V} → G.Subgraph → SimpleGraph V
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Subgraph.symm`：∀ {V : Type u} {G : SimpleGraph V} (self : G.
Subgraph), Std.Symm self.Adj

--- 原说明 ---
Coercion from `Subgraph G` to `SimpleGraph V`.  If `G'` is a spanning
subgraph, then `G'.spanningCoe` yields an isomorphic graph.
In general, this adds in all vertices from `V` as isolated vertices.
-/
protected def spanningCoe (G' : Subgraph G) : SimpleGraph V where
  Adj := G'.Adj
  symm := G'.symm
  loopless.irrefl _ hadj := G.irrefl hadj.adj_sub

attribute [grind =] Subgraph.spanningCoe_adj

@[simp]
/-
**SimpleGraph.Subgraph.spanningCoe_coe** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph.Su
bgraph`。
形式化陈述：spanningCoe_coe (G' : G.Subgraph) : G'.coe.spanningCoe = G'.spanningCoe
参数：G' : G.Subgraph。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.ext`：∀ {V : Type u} {x y : SimpleGraph V}, x.Adj = y.Adj → x
 = y
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
-/
lemma spanningCoe_coe (G' : G.Subgraph) : G'.coe.spanningCoe = G'.spanningCoe := by
  ext
  simp only [map_adj, Function.Embedding.subtype_apply, Subtype.exists]
  grind [coe_adj, edge_vert, adj_symm]
/-
**SimpleGraph.Subgraph.Adj.of_spanningCoe** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph
.Subgraph.Adj`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} {G' : G.Subgraph} {u v : ↑G'.verts}, G'
.spanningCoe.Adj ↑u ↑v → G.Adj ↑u ↑v
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Subgraph.adj_sub`：∀ {V : Type u} {G : SimpleGraph V} (self :
 G.Subgraph) {v w : V}, self.Adj v w → G.Adj v w
-/
theorem Adj.of_spanningCoe {G' : Subgraph G} {u v : G'.verts} (h : G'.spanningCoe.Adj u v) :
    G.Adj u v :=
  G'.adj_sub h
/-
**SimpleGraph.Subgraph.spanningCoe_le** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph.Sub
graph`。
形式化陈述：spanningCoe_le (G' : G.Subgraph) : G'.spanningCoe <= G
参数：G' : G.Subgraph。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Subgraph.adj_sub`：∀ {V : Type u} {G : SimpleGraph V} (self :
 G.Subgraph) {v w : V}, self.Adj v w → G.Adj v w
-/
lemma spanningCoe_le (G' : G.Subgraph) : G'.spanningCoe ≤ G := fun _ _ ↦ G'.3
/-
**SimpleGraph.Subgraph.spanningCoe_inj** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Su
bgraph`。
形式化陈述：spanningCoe_inj : G₁.spanningCoe = G₂.spanningCoe ↔ G₁.Adj = G₂.Adj
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.mk.injEq`：∀ {V : Type u} (Adj : V → V → Prop) (symm : autoPa
ram (Std.Symm Adj) SimpleGraph.symm._autoParam)   (loopless : autoParam (Std.Irr
efl Adj) S…
· 使用定理 `SimpleGraph.Subgraph.symm`：∀ {V : Type u} {G : SimpleGraph V} (self : G.
Subgraph), Std.Symm self.Adj
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem spanningCoe_inj : G₁.spanningCoe = G₂.spanningCoe ↔ G₁.Adj = G₂.Adj := by
  simp [Subgraph.spanningCoe]
/-
**SimpleGraph.Subgraph.mem_of_adj_spanningCoe** 是 Mathlib 中的一个引理，位于命名空间 `SimpleG
raph.Subgraph`。
形式化陈述：mem_of_adj_spanningCoe {v w : V} {s : Set V} (G : SimpleGraph s) (hadj : G
.spanningCoe.Adj v w) : v in s
参数：G : SimpleGraph s；hadj : G.spanningCoe.Adj v w。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
-/
lemma mem_of_adj_spanningCoe {v w : V} {s : Set V} (G : SimpleGraph s)
    (hadj : G.spanningCoe.Adj v w) : v ∈ s := by aesop

@[simp]
/-
**SimpleGraph.Subgraph.spanningCoe_subgraphOfAdj** 是 Mathlib 中的一个引理，位于命名空间 `Simp
leGraph.Subgraph`。
形式化陈述：spanningCoe_subgraphOfAdj {v w : V} (hadj : G.Adj v w) : (G.subgraphOfAdj 
hadj).spanningCoe = fromEdgeSet {s(v, w)}
参数：hadj : G.Adj v w。
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
· 使用定理 `SimpleGraph.Subgraph.spanningCoe_adj`：∀ {V : Type u} {G : SimpleGraph V}
 (G' : G.Subgraph) (a a_1 : V), G'.spanningCoe.Adj a a_1 = G'.Adj a a_1
· 使用定理 `SimpleGraph.subgraphOfAdj_adj`：∀ {V : Type u} (G : SimpleGraph V) {v w :
 V} (hvw : G.Adj v w) (a b : V),   (G.subgraphOfAdj hvw).Adj a b = (s(v, w) = s(
a, b))
· 使用定理 `Prod.mk.injEq`：∀ {α : Type u} {β : Type v} (fst : α) (snd : β) (fst_1 : 
α) (snd_1 : β),   ((fst, snd) = (fst_1, snd_1)) = (fst = fst_1 ∧ snd = snd_1)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `Aesop.BuiltinRules.not_intro`：∀ {P : Prop}, (P → False) → ¬P
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
-/
lemma spanningCoe_subgraphOfAdj {v w : V} (hadj : G.Adj v w) :
    (G.subgraphOfAdj hadj).spanningCoe = fromEdgeSet {s(v, w)} := by
  ext v w
  aesop

/-- `coe` can be embedded in `spanningCoe`. -/
@[simps]
/-
**SimpleGraph.Subgraph.coeEmbeddingSpanningCoe** 是 Mathlib 中的一个定义，位于命名空间 `Simple
Graph.Subgraph`。
形式化陈述：coeEmbeddingSpanningCoe (G' : Subgraph G) : G'.coe ↪g G'.spanningCoe where
 toFun
参数：G' : Subgraph G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`coe` can be embedded in `spanningCoe`.
-/
def coeEmbeddingSpanningCoe (G' : Subgraph G) : G'.coe ↪g G'.spanningCoe where
  toFun := Subtype.val
  inj' := Subtype.val_injective
  map_rel_iff' := .rfl

/-- `spanningCoe` is equivalent to `coe` for a subgraph that `IsSpanning`. -/
@[simps]
/-
**SimpleGraph.Subgraph.spanningCoeEquivCoeOfSpanning** 是 Mathlib 中的一个定义，位于命名空间 `
SimpleGraph.Subgraph`。
形式化陈述：spanningCoeEquivCoeOfSpanning (G' : Subgraph G) (h : G'.IsSpanning) : G'.s
panningCoe ≃g G'.coe where toFun v
参数：G' : Subgraph G；h : G'.IsSpanning。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`spanningCoe` is equivalent to `coe` for a subgraph that `IsSpanning`.
-/
def spanningCoeEquivCoeOfSpanning (G' : Subgraph G) (h : G'.IsSpanning) :
    G'.spanningCoe ≃g G'.coe where
  toFun v := ⟨v, h v⟩
  invFun v := v
  map_rel_iff' := Iff.rfl

/-- A subgraph is called an *induced subgraph* if vertices of `G'` are adjacent if
they are adjacent in `G`. -/
/-
**SimpleGraph.Subgraph.IsInduced** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph.Subgraph
`。
形式化陈述：IsInduced (G' : Subgraph G) : Prop
参数：G' : Subgraph G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A subgraph is called an *induced subgraph* if vertices of `G'` are adjacent if
they are adjacent in `G`.
-/
def IsInduced (G' : Subgraph G) : Prop :=
  ∀ ⦃v⦄, v ∈ G'.verts → ∀ ⦃w⦄, w ∈ G'.verts → G.Adj v w → G'.Adj v w
/-
**SimpleGraph.Subgraph.IsInduced.adj** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Subg
raph.IsInduced`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} {G' : G.Subgraph}, G'.IsInduced → ∀ {a 
b : ↑G'.verts}, G'.Adj ↑a ↑b ↔ G.Adj ↑a ↑b
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Subgraph.coe_adj_sub`：coe_adj_sub (G' : Subgraph G) (u v : G
'.verts) (h : G'.coe.Adj u v) : G.Adj u v
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
@[simp] protected lemma IsInduced.adj {G' : G.Subgraph} (hG' : G'.IsInduced) {a b : G'.verts} :
    G'.Adj a b ↔ G.Adj a b :=
  ⟨coe_adj_sub _ _ _, hG' a.2 b.2⟩

/-- `H.support` is the set of vertices that form edges in the subgraph `H`. -/
/-
**SimpleGraph.Subgraph.support** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph.Subgraph`。
形式化陈述：support (H : Subgraph G) : Set V
参数：H : Subgraph G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`H.support` is the set of vertices that form edges in the subgraph `H`.
-/
def support (H : Subgraph G) : Set V := SetRel.dom {(v, w) | H.Adj v w}
/-
**SimpleGraph.Subgraph.mem_support** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Subgra
ph`。
形式化陈述：mem_support (H : Subgraph G) {v : V} : v in H.support ↔ exists w, H.Adj v 
w
参数：H : Subgraph G。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_support (H : Subgraph G) {v : V} : v ∈ H.support ↔ ∃ w, H.Adj v w := Iff.rfl
/-
**SimpleGraph.Subgraph.support_subset_verts** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGra
ph.Subgraph`。
形式化陈述：support_subset_verts (H : Subgraph G) : H.support subseteq H.verts
参数：H : Subgraph G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Subgraph.edge_vert`：∀ {V : Type u} {G : SimpleGraph V} (self
 : G.Subgraph) {v w : V}, self.Adj v w → v ∈ self.verts
-/
theorem support_subset_verts (H : Subgraph G) : H.support ⊆ H.verts :=
  fun _ ⟨_, h⟩ ↦ H.edge_vert h

/-- `G'.neighborSet v` is the set of vertices adjacent to `v` in `G'`. -/
/-
**SimpleGraph.Subgraph.neighborSet** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph.Subgra
ph`。
形式化陈述：neighborSet (G' : Subgraph G) (v : V) : Set V
参数：G' : Subgraph G；v : V。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`G'.neighborSet v` is the set of vertices adjacent to `v` in `G'`.
-/
def neighborSet (G' : Subgraph G) (v : V) : Set V := {w | G'.Adj v w}
/-
**SimpleGraph.Subgraph.neighborSet_subset** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph
.Subgraph`。
形式化陈述：neighborSet_subset (G' : Subgraph G) (v : V) : G'.neighborSet v subseteq G
.neighborSet v
参数：G' : Subgraph G；v : V。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Subgraph.adj_sub`：∀ {V : Type u} {G : SimpleGraph V} (self :
 G.Subgraph) {v w : V}, self.Adj v w → G.Adj v w
-/
theorem neighborSet_subset (G' : Subgraph G) (v : V) : G'.neighborSet v ⊆ G.neighborSet v :=
  fun _ ↦ G'.adj_sub
/-
**SimpleGraph.Subgraph.neighborSet_subset_verts** 是 Mathlib 中的一个定理，位于命名空间 `Simpl
eGraph.Subgraph`。
形式化陈述：neighborSet_subset_verts (G' : Subgraph G) (v : V) : G'.neighborSet v subs
eteq G'.verts
参数：G' : Subgraph G；v : V。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Subgraph.edge_vert`：∀ {V : Type u} {G : SimpleGraph V} (self
 : G.Subgraph) {v w : V}, self.Adj v w → v ∈ self.verts
· 使用定理 `SimpleGraph.Subgraph.adj_symm`：adj_symm (G' : Subgraph G) {u v : V} (h :
 G'.Adj u v) : G'.Adj v u
-/
theorem neighborSet_subset_verts (G' : Subgraph G) (v : V) : G'.neighborSet v ⊆ G'.verts :=
  fun _ h ↦ G'.edge_vert (adj_symm G' h)

@[simp]
/-
**SimpleGraph.Subgraph.mem_neighborSet** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Su
bgraph`。
形式化陈述：mem_neighborSet (G' : Subgraph G) (v w : V) : w in G'.neighborSet v ↔ G'.A
dj v w
参数：G' : Subgraph G；v w : V。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_neighborSet (G' : Subgraph G) (v w : V) : w ∈ G'.neighborSet v ↔ G'.Adj v w := Iff.rfl

/-- A subgraph as a graph has equivalent neighbor sets. -/
/-
**SimpleGraph.Subgraph.coeNeighborSetEquiv** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGrap
h.Subgraph`。
形式化陈述：coeNeighborSetEquiv {G' : Subgraph G} (v : G'.verts) : G'.coe.neighborSet 
v ≃ G'.neighborSet v where toFun w
参数：v : G'.verts。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A subgraph as a graph has equivalent neighbor sets.
-/
def coeNeighborSetEquiv {G' : Subgraph G} (v : G'.verts) :
    G'.coe.neighborSet v ≃ G'.neighborSet v where
  toFun w := ⟨w, w.2⟩
  invFun w := ⟨⟨w, G'.edge_vert (G'.adj_symm w.2)⟩, w.2⟩

/-- The edge set of `G'` consists of a subset of edges of `G`. -/
/-
**SimpleGraph.Subgraph.edgeSet** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph.Subgraph`。
形式化陈述：edgeSet (G' : Subgraph G) : Set (Sym2 V)
参数：G' : Subgraph G。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Subgraph.symm`：∀ {V : Type u} {G : SimpleGraph V} (self : G.
Subgraph), Std.Symm self.Adj

--- 原说明 ---
The edge set of `G'` consists of a subset of edges of `G`.
-/
def edgeSet (G' : Subgraph G) : Set (Sym2 V) := Sym2.fromRel G'.symm
/-
**SimpleGraph.Subgraph.edgeSet_subset** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Sub
graph`。
形式化陈述：edgeSet_subset (G' : Subgraph G) : G'.edgeSet subseteq G.edgeSet
参数：G' : Subgraph G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Sym2.ind`：∀ {α : Type u_1} {f : Sym2 α → Prop}, (∀ (x y : α), f s(x, y))
 → ∀ (i : Sym2 α), f i
· 使用定理 `SimpleGraph.Subgraph.adj_sub`：∀ {V : Type u} {G : SimpleGraph V} (self :
 G.Subgraph) {v w : V}, self.Adj v w → G.Adj v w
-/
theorem edgeSet_subset (G' : Subgraph G) : G'.edgeSet ⊆ G.edgeSet :=
  Sym2.ind (fun _ _ ↦ G'.adj_sub)

@[simp]
/-
**SimpleGraph.Subgraph.mem_edgeSet** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Subgra
ph`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} {G' : G.Subgraph} {v w : V}, s(v, w) ∈ 
G'.edgeSet ↔ G'.Adj v w
参数：v, w。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
protected lemma mem_edgeSet {G' : Subgraph G} {v w : V} : s(v, w) ∈ G'.edgeSet ↔ G'.Adj v w := .rfl
/-
**SimpleGraph.Subgraph.edgeSet_coe** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Subgra
ph`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} {G' : G.Subgraph}, G'.coe.edgeSet = Sym
2.map Subtype.val ⁻¹' G'.edgeSet
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Sym2.ind`：∀ {α : Type u_1} {f : Sym2 α → Prop}, (∀ (x y : α), f s(x, y))
 → ∀ (i : Sym2 α), f i
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.Subgraph.coe_adj`：∀ {V : Type u} {G : SimpleGraph V} (G' : G
.Subgraph) (v w : ↑G'.verts), G'.coe.Adj v w = G'.Adj ↑v ↑w
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma edgeSet_coe {G' : G.Subgraph} : G'.coe.edgeSet = Sym2.map (↑) ⁻¹' G'.edgeSet := by
  ext e; induction e using Sym2.ind; simp
/-
**SimpleGraph.Subgraph.image_coe_edgeSet_coe** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGr
aph.Subgraph`。
形式化陈述：image_coe_edgeSet_coe (G' : G.Subgraph) : Sym2.map (↑) '' G'.coe.edgeSet =
 G'.edgeSet
参数：G' : G.Subgraph。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.Subgraph.edgeSet_coe`：∀ {V : Type u} {G : SimpleGraph V} {G'
 : G.Subgraph}, G'.coe.edgeSet = Sym2.map Subtype.val ⁻¹' G'.edgeSet
· 使用定理 `Set.image_preimage_eq_iff`：image_preimage_eq_iff {f : α -> β} {s : Set β
} : f '' f ⁻¹' s = s ↔ s subseteq range f
· 使用定理 `Sym2.ind`：∀ {α : Type u_1} {f : Sym2 α → Prop}, (∀ (x y : α), f s(x, y))
 → ∀ (i : Sym2 α), f i
· 使用定理 `SimpleGraph.Subgraph.edge_vert`：∀ {V : Type u} {G : SimpleGraph V} (self
 : G.Subgraph) {v w : V}, self.Adj v w → v ∈ self.verts
· 使用定理 `SimpleGraph.Subgraph.mem_edgeSet`：∀ {V : Type u} {G : SimpleGraph V} {G'
 : G.Subgraph} {v w : V}, s(v, w) ∈ G'.edgeSet ↔ G'.Adj v w
· 使用定理 `SimpleGraph.Subgraph.Adj.symm`：∀ {V : Type u} {G : SimpleGraph V} {G' : 
G.Subgraph} {u v : V}, G'.Adj u v → G'.Adj v u
· 使用定理 `Sym2.map_mk`：map_mk (f : α -> β) (a b : α) : map f s(a, b) = s(f a, f b)
-/
lemma image_coe_edgeSet_coe (G' : G.Subgraph) : Sym2.map (↑) '' G'.coe.edgeSet = G'.edgeSet := by
  rw [edgeSet_coe, Set.image_preimage_eq_iff]
  rintro e he
  induction e using Sym2.ind with | h a b =>
  rw [Subgraph.mem_edgeSet] at he
  exact ⟨s(⟨a, edge_vert _ he⟩, ⟨b, edge_vert _ he.symm⟩), Sym2.map_mk ..⟩

@[simp]
/-
**SimpleGraph.Subgraph.edgeSet_spanningCoe** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGrap
h.Subgraph`。
形式化陈述：edgeSet_spanningCoe (G' : G.Subgraph) : G'.spanningCoe.edgeSet = G'.edgeSe
t
参数：G' : G.Subgraph。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma edgeSet_spanningCoe (G' : G.Subgraph) : G'.spanningCoe.edgeSet = G'.edgeSet := by
  rfl
/-
**SimpleGraph.Subgraph.mem_verts_of_mem_edge** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGr
aph.Subgraph`。
形式化陈述：mem_verts_of_mem_edge {G' : Subgraph G} {e : Sym2 V} {v : V} (he : e in G'
.edgeSet) (hv : v in e) : v in G'.verts
参数：he : e in G'.edgeSet；hv : v in e。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Sym2.ind`：∀ {α : Type u_1} {f : Sym2 α → Prop}, (∀ (x y : α), f s(x, y))
 → ∀ (i : Sym2 α), f i
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Sym2.mem_iff`：mem_iff {a b c : α} : a in s(b, c) ↔ a = b ∨ a = c
· 使用定理 `SimpleGraph.Subgraph.edge_vert`：∀ {V : Type u} {G : SimpleGraph V} (self
 : G.Subgraph) {v w : V}, self.Adj v w → v ∈ self.verts
· 使用定理 `SimpleGraph.Subgraph.adj_symm`：adj_symm (G' : Subgraph G) {u v : V} (h :
 G'.Adj u v) : G'.Adj v u
-/
theorem mem_verts_of_mem_edge {G' : Subgraph G} {e : Sym2 V} {v : V} (he : e ∈ G'.edgeSet)
    (hv : v ∈ e) : v ∈ G'.verts := by
  induction e
  rcases Sym2.mem_iff.mp hv with (rfl | rfl)
  · exact G'.edge_vert he
  · exact G'.edge_vert <| G'.adj_symm he

/-- The `incidenceSet` is the set of edges incident to a given vertex. -/
/-
**SimpleGraph.Subgraph.incidenceSet** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph.Subgr
aph`。
形式化陈述：incidenceSet (G' : Subgraph G) (v : V) : Set (Sym2 V)
参数：G' : Subgraph G；v : V。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `incidenceSet` is the set of edges incident to a given vertex.
-/
def incidenceSet (G' : Subgraph G) (v : V) : Set (Sym2 V) := {e ∈ G'.edgeSet | v ∈ e}
/-
**SimpleGraph.Subgraph.incidenceSet_subset_incidenceSet** 是 Mathlib 中的一个定理，位于命名空
间 `SimpleGraph.Subgraph`。
形式化陈述：incidenceSet_subset_incidenceSet (G' : Subgraph G) (v : V) : G'.incidenceS
et v subseteq G.incidenceSet v
参数：G' : Subgraph G；v : V。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Subgraph.edgeSet_subset`：edgeSet_subset (G' : Subgraph G) : 
G'.edgeSet subseteq G.edgeSet
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem incidenceSet_subset_incidenceSet (G' : Subgraph G) (v : V) :
    G'.incidenceSet v ⊆ G.incidenceSet v :=
  fun _ h ↦ ⟨G'.edgeSet_subset h.1, h.2⟩
/-
**SimpleGraph.Subgraph.incidenceSet_subset** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGrap
h.Subgraph`。
形式化陈述：incidenceSet_subset (G' : Subgraph G) (v : V) : G'.incidenceSet v subseteq
 G'.edgeSet
参数：G' : Subgraph G；v : V。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem incidenceSet_subset (G' : Subgraph G) (v : V) : G'.incidenceSet v ⊆ G'.edgeSet :=
  fun _ h ↦ h.1

/-- Give a vertex as an element of the subgraph's vertex type. -/
/-
**SimpleGraph.Subgraph.vert** 是 Mathlib 中的一个缩写定义，位于命名空间 `SimpleGraph.Subgraph`。
形式化陈述：vert (G' : Subgraph G) (v : V) (h : v in G'.verts) : G'.verts
参数：G' : Subgraph G；v : V；h : v in G'.verts。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Give a vertex as an element of the subgraph's vertex type.
-/
abbrev vert (G' : Subgraph G) (v : V) (h : v ∈ G'.verts) : G'.verts := ⟨v, h⟩

/--
Create an equal copy of a subgraph (see `copy_eq`) with possibly different definitional equalities.
See Note [range copy pattern].
-/
/-
**SimpleGraph.Subgraph.copy** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph.Subgraph`。
形式化陈述：copy (G' : Subgraph G) (V'' : Set V) (hV : V'' = G'.verts) (adj' : V -> V 
-> Prop) (hadj : adj' = G'.Adj) : Subgraph G where verts
参数：G' : Subgraph G；V'' : Set V；hV : V'' = G'.verts；adj' : V -> V -> Prop；hadj : 
adj' = G'.Adj。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Create an equal copy of a subgraph (see `copy_eq`) with possibly different defin
itional equalities.
See Note [range copy pattern].
-/
def copy (G' : Subgraph G) (V'' : Set V) (hV : V'' = G'.verts)
    (adj' : V → V → Prop) (hadj : adj' = G'.Adj) : Subgraph G where
  verts := V''
  Adj := adj'
  adj_sub := hadj.symm ▸ G'.adj_sub
  edge_vert := hV.symm ▸ hadj.symm ▸ G'.edge_vert
  symm := hadj.symm ▸ G'.symm
/-
**SimpleGraph.Subgraph.copy_eq** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Subgraph`。
形式化陈述：copy_eq (G' : Subgraph G) (V'' : Set V) (hV : V'' = G'.verts) (adj' : V ->
 V -> Prop) (hadj : adj' = G'.Adj) : G'.copy V'' hV adj' hadj = G'
参数：G' : Subgraph G；V'' : Set V；hV : V'' = G'.verts；adj' : V -> V -> Prop；hadj : 
adj' = G'.Adj。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Subgraph.ext`：∀ {V : Type u} {G : SimpleGraph V} {x y : G.Su
bgraph}, x.verts = y.verts → x.Adj = y.Adj → x = y
-/
theorem copy_eq (G' : Subgraph G) (V'' : Set V) (hV : V'' = G'.verts)
    (adj' : V → V → Prop) (hadj : adj' = G'.Adj) : G'.copy V'' hV adj' hadj = G' :=
  Subgraph.ext hV hadj

/-- The union of two subgraphs. -/
/-
**SimpleGraph.Subgraph.** 是 Mathlib 中的一个实例，位于命名空间 `SimpleGraph.Subgraph`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The union of two subgraphs.
-/
instance : Max G.Subgraph where
  max G₁ G₂ :=
    { verts := G₁.verts ∪ G₂.verts
      Adj := G₁.Adj ⊔ G₂.Adj
      adj_sub := fun hab => Or.elim hab (fun h => G₁.adj_sub h) fun h => G₂.adj_sub h
      edge_vert := Or.imp (fun h => G₁.edge_vert h) fun h => G₂.edge_vert h
      symm.symm _ _ := Or.imp G₁.adj_symm G₂.adj_symm }

/-- The intersection of two subgraphs. -/
/-
**SimpleGraph.Subgraph.** 是 Mathlib 中的一个实例，位于命名空间 `SimpleGraph.Subgraph`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The intersection of two subgraphs.
-/
instance : Min G.Subgraph where
  min G₁ G₂ :=
    { verts := G₁.verts ∩ G₂.verts
      Adj := G₁.Adj ⊓ G₂.Adj
      adj_sub := fun hab => G₁.adj_sub hab.1
      edge_vert := And.imp (fun h => G₁.edge_vert h) fun h => G₂.edge_vert h
      symm.symm _ _ := And.imp G₁.adj_symm G₂.adj_symm }

/-- The `top` subgraph is `G` as a subgraph of itself. -/
/-
**SimpleGraph.Subgraph.** 是 Mathlib 中的一个实例，位于命名空间 `SimpleGraph.Subgraph`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `top` subgraph is `G` as a subgraph of itself.
-/
instance : Top G.Subgraph where
  top.verts := Set.univ
  top.Adj := G.Adj
  top.adj_sub := id
  top.edge_vert := @fun v _ _ => Set.mem_univ v
  top.symm := G.symm

/-- The `bot` subgraph is the subgraph with no vertices or edges. -/
/-
**SimpleGraph.Subgraph.** 是 Mathlib 中的一个实例，位于命名空间 `SimpleGraph.Subgraph`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `bot` subgraph is the subgraph with no vertices or edges.
-/
instance : Bot G.Subgraph where
  bot.verts := ∅
  bot.Adj := ⊥
  bot.adj_sub := False.elim
  bot.edge_vert := False.elim
/-
**SimpleGraph.Subgraph.** 是 Mathlib 中的一个实例，位于命名空间 `SimpleGraph.Subgraph`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SupSet G.Subgraph where
  sSup s :=
    { verts := ⋃ G' ∈ s, verts G'
      Adj := fun a b => ∃ G' ∈ s, Adj G' a b
      adj_sub := by
        rintro a b ⟨G', -, hab⟩
        exact G'.adj_sub hab
      edge_vert := by
        rintro a b ⟨G', hG', hab⟩
        exact Set.mem_iUnion₂_of_mem hG' (G'.edge_vert hab)
      symm.symm a b h := by simpa [adj_comm] using h }
/-
**SimpleGraph.Subgraph.** 是 Mathlib 中的一个实例，位于命名空间 `SimpleGraph.Subgraph`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : InfSet G.Subgraph where
  sInf s :=
    { verts := ⋂ G' ∈ s, verts G'
      Adj := fun a b => (∀ ⦃G'⦄, G' ∈ s → Adj G' a b) ∧ G.Adj a b
      adj_sub := And.right
      edge_vert := fun hab => Set.mem_iInter₂_of_mem fun G' hG' => G'.edge_vert <| hab.1 hG'
      symm.symm _ _ := And.imp (forall₂_imp fun _ _ ↦ Adj.symm) G.adj_symm }

@[simp]
/-
**SimpleGraph.Subgraph.sup_adj** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Subgraph`。
形式化陈述：sup_adj : (G₁ ⊔ G₂).Adj a b ↔ G₁.Adj a b ∨ G₂.Adj a b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem sup_adj : (G₁ ⊔ G₂).Adj a b ↔ G₁.Adj a b ∨ G₂.Adj a b :=
  Iff.rfl

@[simp]
/-
**SimpleGraph.Subgraph.inf_adj** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Subgraph`。
形式化陈述：inf_adj : (G₁ ⊓ G₂).Adj a b ↔ G₁.Adj a b ∧ G₂.Adj a b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem inf_adj : (G₁ ⊓ G₂).Adj a b ↔ G₁.Adj a b ∧ G₂.Adj a b :=
  Iff.rfl

@[simp]
/-
**SimpleGraph.Subgraph.top_adj** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Subgraph`。
形式化陈述：top_adj : (⊤ : Subgraph G).Adj a b ↔ G.Adj a b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem top_adj : (⊤ : Subgraph G).Adj a b ↔ G.Adj a b :=
  Iff.rfl

@[simp]
/-
**SimpleGraph.Subgraph.not_bot_adj** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Subgra
ph`。
形式化陈述：not_bot_adj : ¬ (⊥ : Subgraph G).Adj a b
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `not_false`：¬False
-/
theorem not_bot_adj : ¬ (⊥ : Subgraph G).Adj a b :=
  not_false

@[simp]
/-
**SimpleGraph.Subgraph.verts_sup** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Subgraph
`。
形式化陈述：verts_sup (G₁ G₂ : G.Subgraph) : (G₁ ⊔ G₂).verts = G₁.verts union G₂.verts
参数：G₁ G₂ : G.Subgraph。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem verts_sup (G₁ G₂ : G.Subgraph) : (G₁ ⊔ G₂).verts = G₁.verts ∪ G₂.verts :=
  rfl

@[simp]
/-
**SimpleGraph.Subgraph.verts_inf** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Subgraph
`。
形式化陈述：verts_inf (G₁ G₂ : G.Subgraph) : (G₁ ⊓ G₂).verts = G₁.verts inter G₂.verts
参数：G₁ G₂ : G.Subgraph。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem verts_inf (G₁ G₂ : G.Subgraph) : (G₁ ⊓ G₂).verts = G₁.verts ∩ G₂.verts :=
  rfl

@[simp]
/-
**SimpleGraph.Subgraph.verts_top** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Subgraph
`。
形式化陈述：verts_top : (⊤ : G.Subgraph).verts = Set.univ
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem verts_top : (⊤ : G.Subgraph).verts = Set.univ :=
  rfl

@[simp]
/-
**SimpleGraph.Subgraph.verts_bot** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Subgraph
`。
形式化陈述：verts_bot : (⊥ : G.Subgraph).verts = ∅
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem verts_bot : (⊥ : G.Subgraph).verts = ∅ :=
  rfl
/-
**SimpleGraph.Subgraph.eq_bot_iff_verts_eq_empty** 是 Mathlib 中的一个定理，位于命名空间 `Simp
leGraph.Subgraph`。
形式化陈述：eq_bot_iff_verts_eq_empty (G' : G.Subgraph) : G' = ⊥ ↔ G'.verts = ∅
参数：G' : G.Subgraph。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Subgraph.verts_bot`：verts_bot : (⊥ : G.Subgraph).verts = ∅
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SimpleGraph.Subgraph.ext`：∀ {V : Type u} {G : SimpleGraph V} {x y : G.Su
bgraph}, x.verts = y.verts → x.Adj = y.Adj → x = y
· 使用定理 `funext₂`：∀ {α : Sort u_1} {β : α → Sort u_2} {γ : (a : α) → β a → Sort u
_3} {f g : (a : α) → (b : β a) → γ a b},   (∀ (a : α) (b : β a), f a b = g a …
· 使用定理 `SimpleGraph.Subgraph.Adj.fst_mem`：∀ {V : Type u} {G : SimpleGraph V} {H 
: G.Subgraph} {u v : V}, H.Adj u v → u ∈ H.verts
-/
theorem eq_bot_iff_verts_eq_empty (G' : G.Subgraph) : G' = ⊥ ↔ G'.verts = ∅ :=
  ⟨(· ▸ verts_bot), fun h ↦ Subgraph.ext (h ▸ verts_bot (G := G)) <|
    funext₂ fun _ _ ↦ propext ⟨fun h' ↦ (h ▸ h'.fst_mem :), False.elim⟩⟩
/-
**SimpleGraph.Subgraph.ne_bot_iff_nonempty_verts** 是 Mathlib 中的一个定理，位于命名空间 `Simp
leGraph.Subgraph`。
形式化陈述：ne_bot_iff_nonempty_verts (G' : G.Subgraph) : G' != ⊥ ↔ G'.verts.Nonempty
参数：G' : G.Subgraph。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `SimpleGraph.Subgraph.eq_bot_iff_verts_eq_empty`：eq_bot_iff_verts_eq_empt
y (G' : G.Subgraph) : G' = ⊥ ↔ G'.verts = ∅
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Set.nonempty_iff_ne_empty`：nonempty_iff_ne_empty : s.Nonempty ↔ s != ∅
-/
theorem ne_bot_iff_nonempty_verts (G' : G.Subgraph) : G' ≠ ⊥ ↔ G'.verts.Nonempty :=
  G'.eq_bot_iff_verts_eq_empty.not.trans <| Set.nonempty_iff_ne_empty.symm

@[simp]
/-
**SimpleGraph.Subgraph.sSup_adj** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Subgraph`
。
形式化陈述：sSup_adj {s : Set G.Subgraph} : (sSup s).Adj a b ↔ exists G in s, Adj G a 
b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem sSup_adj {s : Set G.Subgraph} : (sSup s).Adj a b ↔ ∃ G ∈ s, Adj G a b :=
  Iff.rfl

@[simp]
/-
**SimpleGraph.Subgraph.sInf_adj** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Subgraph`
。
形式化陈述：sInf_adj {s : Set G.Subgraph} : (sInf s).Adj a b ↔ (forall G' in s, Adj G'
 a b) ∧ G.Adj a b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem sInf_adj {s : Set G.Subgraph} : (sInf s).Adj a b ↔ (∀ G' ∈ s, Adj G' a b) ∧ G.Adj a b :=
  Iff.rfl

@[simp]
/-
**SimpleGraph.Subgraph.iSup_adj** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Subgraph`
。
形式化陈述：iSup_adj {f : ι -> G.Subgraph} : (⨆ i, f i).Adj a b ↔ exists i, (f i).Adj 
a b
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
theorem iSup_adj {f : ι → G.Subgraph} : (⨆ i, f i).Adj a b ↔ ∃ i, (f i).Adj a b := by
  simp [iSup]

@[simp]
/-
**SimpleGraph.Subgraph.iInf_adj** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Subgraph`
。
形式化陈述：iInf_adj {f : ι -> G.Subgraph} : (⨅ i, f i).Adj a b ↔ (forall i, (f i).Adj
 a b) ∧ G.Adj a b
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
theorem iInf_adj {f : ι → G.Subgraph} : (⨅ i, f i).Adj a b ↔ (∀ i, (f i).Adj a b) ∧ G.Adj a b := by
  simp [iInf]
/-
**SimpleGraph.Subgraph.sInf_adj_of_nonempty** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGra
ph.Subgraph`。
形式化陈述：sInf_adj_of_nonempty {s : Set G.Subgraph} (hs : s.Nonempty) : (sInf s).Adj
 a b ↔ forall G' in s, Adj G' a b
参数：hs : s.Nonempty。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `SimpleGraph.Subgraph.sInf_adj`：sInf_adj {s : Set G.Subgraph} : (sInf s).
Adj a b ↔ (forall G' in s, Adj G' a b) ∧ G.Adj a b
· 使用定理 `and_iff_left_of_imp`：∀ {a b : Prop}, (a → b) → (a ∧ b ↔ a)
· 使用定理 `SimpleGraph.Subgraph.adj_sub`：∀ {V : Type u} {G : SimpleGraph V} (self :
 G.Subgraph) {v w : V}, self.Adj v w → G.Adj v w
-/
theorem sInf_adj_of_nonempty {s : Set G.Subgraph} (hs : s.Nonempty) :
    (sInf s).Adj a b ↔ ∀ G' ∈ s, Adj G' a b :=
  sInf_adj.trans <|
    and_iff_left_of_imp <| by
      obtain ⟨G', hG'⟩ := hs
      exact fun h => G'.adj_sub (h _ hG')
/-
**SimpleGraph.Subgraph.iInf_adj_of_nonempty** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGra
ph.Subgraph`。
形式化陈述：iInf_adj_of_nonempty [Nonempty ι] {f : ι -> G.Subgraph} : (⨅ i, f i).Adj a
 b ↔ forall i, (f i).Adj a b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iInf.eq_1`：∀ {α : Type u} {ι : Sort v} [inst : InfSet α] (s : ι → α), iI
nf s = sInf (Set.range s)
· 使用定理 `SimpleGraph.Subgraph.sInf_adj_of_nonempty`：sInf_adj_of_nonempty {s : Set
 G.Subgraph} (hs : s.Nonempty) : (sInf s).Adj a b ↔ forall G' in s, Adj G' a b
· 使用定理 `Set.range_nonempty`：range_nonempty [h : Nonempty ι] (f : ι -> α) : (rang
e f).Nonempty
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem iInf_adj_of_nonempty [Nonempty ι] {f : ι → G.Subgraph} :
    (⨅ i, f i).Adj a b ↔ ∀ i, (f i).Adj a b := by
  rw [iInf, sInf_adj_of_nonempty (Set.range_nonempty _)]
  simp

@[simp]
/-
**SimpleGraph.Subgraph.verts_sSup** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Subgrap
h`。
形式化陈述：verts_sSup (s : Set G.Subgraph) : (sSup s).verts = ⋃ G' in s, verts G'
参数：s : Set G.Subgraph。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem verts_sSup (s : Set G.Subgraph) : (sSup s).verts = ⋃ G' ∈ s, verts G' :=
  rfl

@[simp]
/-
**SimpleGraph.Subgraph.verts_sInf** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Subgrap
h`。
形式化陈述：verts_sInf (s : Set G.Subgraph) : (sInf s).verts = ⋂ G' in s, verts G'
参数：s : Set G.Subgraph。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem verts_sInf (s : Set G.Subgraph) : (sInf s).verts = ⋂ G' ∈ s, verts G' :=
  rfl

@[simp]
/-
**SimpleGraph.Subgraph.verts_iSup** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Subgrap
h`。
形式化陈述：verts_iSup {f : ι -> G.Subgraph} : (⨆ i, f i).verts = ⋃ i, (f i).verts
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Set.iUnion_exists`：iUnion_exists {p : ι -> Prop} {f : Exists p -> Set α}
 : ⋃ x, f x = ⋃ (i) (h : p i), f ⟨i, h⟩
· 使用定理 `Set.iUnion_iUnion_eq'`：iUnion_iUnion_eq' {f : ι -> α} {g : α -> Set β} :
 ⋃ (x) (y) (_ : f y = x), g x = ⋃ y, g (f y)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem verts_iSup {f : ι → G.Subgraph} : (⨆ i, f i).verts = ⋃ i, (f i).verts := by simp [iSup]

@[simp]
/-
**SimpleGraph.Subgraph.verts_iInf** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Subgrap
h`。
形式化陈述：verts_iInf {f : ι -> G.Subgraph} : (⨅ i, f i).verts = ⋂ i, (f i).verts
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iInter_congr_Prop`：iInter_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iInter f₁ 
= iInter f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Set.iInter_exists`：iInter_exists {p : ι -> Prop} {f : Exists p -> Set α}
 : ⋂ x, f x = ⋂ (i) (h : p i), f ⟨i, h⟩
· 使用定理 `Set.iInter_iInter_eq'`：iInter_iInter_eq' {f : ι -> α} {g : α -> Set β} :
 ⋂ (x) (y) (_ : f y = x), g x = ⋂ y, g (f y)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem verts_iInf {f : ι → G.Subgraph} : (⨅ i, f i).verts = ⋂ i, (f i).verts := by simp [iInf]
/-
**SimpleGraph.Subgraph.coe_bot** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Subgraph`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V}, ⊥.coe = ⊥
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma coe_bot : (⊥ : G.Subgraph).coe = ⊥ := rfl
/-
**SimpleGraph.Subgraph.IsInduced.top** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Subg
raph.IsInduced`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V}, ⊤.IsInduced
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma IsInduced.top : (⊤ : G.Subgraph).IsInduced := fun _ _ _ _ ↦ id

/-- The graph isomorphism between the top element of `G.subgraph` and `G`. -/
/-
**SimpleGraph.Subgraph.topIso** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph.Subgraph`。
形式化陈述：topIso : (⊤ : G.Subgraph).coe ≃g G where toFun
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α

--- 原说明 ---
The graph isomorphism between the top element of `G.subgraph` and `G`.
-/
def topIso : (⊤ : G.Subgraph).coe ≃g G where
  toFun := (↑)
  invFun a := ⟨a, Set.mem_univ _⟩
  left_inv _ := Subtype.eta ..
  map_rel_iff' := .rfl
/-
**SimpleGraph.Subgraph.verts_spanningCoe_injective** 是 Mathlib 中的一个定理，位于命名空间 `Si
mpleGraph.Subgraph`。
形式化陈述：verts_spanningCoe_injective : (fun G' : Subgraph G => (G'.verts, G'.spanni
ngCoe)).Injective
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Subgraph.ext`：∀ {V : Type u} {G : SimpleGraph V} {x y : G.Su
bgraph}, x.verts = y.verts → x.Adj = y.Adj → x = y
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Prod.ext_iff`：∀ {α : Type u} {β : Type v} {x y : α × β}, x = y ↔ x.1 = y
.1 ∧ x.2 = y.2
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `SimpleGraph.Subgraph.spanningCoe_inj`：spanningCoe_inj : G₁.spanningCoe =
 G₂.spanningCoe ↔ G₁.Adj = G₂.Adj
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem verts_spanningCoe_injective :
    (fun G' : Subgraph G => (G'.verts, G'.spanningCoe)).Injective := by
  intro G₁ G₂ h
  rw [Prod.ext_iff] at h
  exact Subgraph.ext h.1 (spanningCoe_inj.1 h.2)

/-- For subgraphs `G₁`, `G₂`, `G₁ ≤ G₂` iff `G₁.verts ⊆ G₂.verts` and
`∀ a b, G₁.adj a b → G₂.adj a b`. -/
/-
**SimpleGraph.Subgraph.** 是 Mathlib 中的一个实例，位于命名空间 `SimpleGraph.Subgraph`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For subgraphs `G₁`, `G₂`, `G₁ ≤ G₂` iff `G₁.verts ⊆ G₂.verts` and
`∀ a b, G₁.adj a b → G₂.adj a b`.
-/
instance : PartialOrder G.Subgraph where
  __ := PartialOrder.lift _ verts_spanningCoe_injective
  le x y := x.verts ⊆ y.verts ∧ ∀ ⦃v w : V⦄, x.Adj v w → y.Adj v w
/-
**SimpleGraph.Subgraph.distribLattice** 是 Mathlib 中的一个实例，位于命名空间 `SimpleGraph.Sub
graph`。
形式化陈述：distribLattice : DistribLattice G.Subgraph
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Subgraph.verts_spanningCoe_injective`：verts_spanningCoe_inje
ctive : (fun G' : Subgraph G => (G'.verts, G'.spanningCoe)).Injective
-/
instance distribLattice : DistribLattice G.Subgraph :=
  verts_spanningCoe_injective.distribLattice _ .rfl .rfl (fun _ _ ↦ rfl) fun _ _ ↦ rfl
/-
**SimpleGraph.Subgraph.** 是 Mathlib 中的一个实例，位于命名空间 `SimpleGraph.Subgraph`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : BoundedOrder (Subgraph G) where
  le_top x := ⟨Set.subset_univ _, fun _ _ => x.adj_sub⟩
  bot_le _ := ⟨Set.empty_subset _, fun _ _ => False.elim⟩

set_option linter.unusedVariables false in
/-
**SimpleGraph.Subgraph.** 是 Mathlib 中的一个实例，位于命名空间 `SimpleGraph.Subgraph`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CompleteLattice (Subgraph G) where
  isLUB_sSup _ :=
    ⟨fun G' hG' ↦ ⟨Set.subset_biUnion_of_mem hG', fun _ _ hab => ⟨G', hG', hab⟩⟩,
      fun G' hG' ↦
        ⟨Set.iUnion₂_subset fun _ hH => (hG' hH).1, fun a b ⟨H, hH, hab⟩ ↦ (hG' hH).2 hab⟩⟩
  isGLB_sInf _ :=
    ⟨fun G' hG' ↦ ⟨Set.iInter₂_subset G' hG', fun _ _ hab => hab.1 hG'⟩,
      fun G' hG' ↦
        ⟨Set.subset_iInter₂ fun _ hH => (hG' hH).1, fun _ _ hab =>
         ⟨fun _ hH => (hG' hH).2 hab, G'.adj_sub hab⟩⟩⟩

/-- Note that subgraphs do not form a Boolean algebra, because of `verts`. -/
/-
**SimpleGraph.Subgraph.** 是 Mathlib 中的一个实例，位于命名空间 `SimpleGraph.Subgraph`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Note that subgraphs do not form a Boolean algebra, because of `verts`.
-/
instance : CompletelyDistribLattice G.Subgraph :=
  fast_instance% .ofMinimalAxioms {
    iInf_iSup_eq f := Subgraph.ext (by simpa using! iInf_iSup_eq)
      (by ext; simp [Classical.skolem]) }
/-
**SimpleGraph.Subgraph.verts_mono** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Subgrap
h`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} {H H' : G.Subgraph}, H ≤ H' → H.verts ⊆
 H'.verts
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
@[gcongr] lemma verts_mono {H H' : G.Subgraph} (h : H ≤ H') : H.verts ⊆ H'.verts := h.1
/-
**SimpleGraph.Subgraph.verts_monotone** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph.Sub
graph`。
形式化陈述：verts_monotone : Monotone (verts : G.Subgraph -> Set V)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
lemma verts_monotone : Monotone (verts : G.Subgraph → Set V) := fun _ _ h ↦ h.1

@[simps]
/-
**SimpleGraph.Subgraph.subgraphInhabited** 是 Mathlib 中的一个实例，位于命名空间 `SimpleGraph.
Subgraph`。
形式化陈述：subgraphInhabited : Inhabited (Subgraph G)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance subgraphInhabited : Inhabited (Subgraph G) := ⟨⊥⟩

@[simp]
/-
**SimpleGraph.Subgraph.neighborSet_sup** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Su
bgraph`。
形式化陈述：neighborSet_sup {H H' : G.Subgraph} (v : V) : (H ⊔ H').neighborSet v = H.n
eighborSet v union H'.neighborSet v
参数：v : V。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem neighborSet_sup {H H' : G.Subgraph} (v : V) :
    (H ⊔ H').neighborSet v = H.neighborSet v ∪ H'.neighborSet v := rfl

@[simp]
/-
**SimpleGraph.Subgraph.neighborSet_inf** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Su
bgraph`。
形式化陈述：neighborSet_inf {H H' : G.Subgraph} (v : V) : (H ⊓ H').neighborSet v = H.n
eighborSet v inter H'.neighborSet v
参数：v : V。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem neighborSet_inf {H H' : G.Subgraph} (v : V) :
    (H ⊓ H').neighborSet v = H.neighborSet v ∩ H'.neighborSet v := rfl

@[simp]
/-
**SimpleGraph.Subgraph.neighborSet_top** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Su
bgraph`。
形式化陈述：neighborSet_top (v : V) : (⊤ : G.Subgraph).neighborSet v = G.neighborSet v
参数：v : V。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem neighborSet_top (v : V) : (⊤ : G.Subgraph).neighborSet v = G.neighborSet v := rfl

@[simp]
/-
**SimpleGraph.Subgraph.neighborSet_bot** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Su
bgraph`。
形式化陈述：neighborSet_bot (v : V) : (⊥ : G.Subgraph).neighborSet v = ∅
参数：v : V。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem neighborSet_bot (v : V) : (⊥ : G.Subgraph).neighborSet v = ∅ := rfl

@[simp]
/-
**SimpleGraph.Subgraph.neighborSet_sSup** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.S
ubgraph`。
形式化陈述：neighborSet_sSup (s : Set G.Subgraph) (v : V) : (sSup s).neighborSet v = ⋃
 G' in s, neighborSet G' v
参数：s : Set G.Subgraph；v : V。
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
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem neighborSet_sSup (s : Set G.Subgraph) (v : V) :
    (sSup s).neighborSet v = ⋃ G' ∈ s, neighborSet G' v := by
  ext
  simp

@[simp]
/-
**SimpleGraph.Subgraph.neighborSet_sInf** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.S
ubgraph`。
形式化陈述：neighborSet_sInf (s : Set G.Subgraph) (v : V) : (sInf s).neighborSet v = (
⋂ G' in s, neighborSet G' v) inter G.neighborSet v
参数：s : Set G.Subgraph；v : V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem neighborSet_sInf (s : Set G.Subgraph) (v : V) :
    (sInf s).neighborSet v = (⋂ G' ∈ s, neighborSet G' v) ∩ G.neighborSet v := by
  ext
  simp

@[simp]
/-
**SimpleGraph.Subgraph.neighborSet_iSup** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.S
ubgraph`。
形式化陈述：neighborSet_iSup (f : ι -> G.Subgraph) (v : V) : (⨆ i, f i).neighborSet v 
= ⋃ i, (f i).neighborSet v
参数：f : ι -> G.Subgraph；v : V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.Subgraph.neighborSet_sSup`：neighborSet_sSup (s : Set G.Subgr
aph) (v : V) : (sSup s).neighborSet v = ⋃ G' in s, neighborSet G' v
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Set.iUnion_exists`：iUnion_exists {p : ι -> Prop} {f : Exists p -> Set α}
 : ⋃ x, f x = ⋃ (i) (h : p i), f ⟨i, h⟩
· 使用定理 `Set.iUnion_iUnion_eq'`：iUnion_iUnion_eq' {f : ι -> α} {g : α -> Set β} :
 ⋃ (x) (y) (_ : f y = x), g x = ⋃ y, g (f y)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem neighborSet_iSup (f : ι → G.Subgraph) (v : V) :
    (⨆ i, f i).neighborSet v = ⋃ i, (f i).neighborSet v := by simp [iSup]

@[simp]
/-
**SimpleGraph.Subgraph.neighborSet_iInf** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.S
ubgraph`。
形式化陈述：neighborSet_iInf (f : ι -> G.Subgraph) (v : V) : (⨅ i, f i).neighborSet v 
= (⋂ i, (f i).neighborSet v) inter G.neighborSet v
参数：f : ι -> G.Subgraph；v : V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.Subgraph.neighborSet_sInf`：neighborSet_sInf (s : Set G.Subgr
aph) (v : V) : (sInf s).neighborSet v = (⋂ G' in s, neighborSet G' v) inter G.ne
ighborSet v
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iInter_congr_Prop`：iInter_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iInter f₁ 
= iInter f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Set.iInter_exists`：iInter_exists {p : ι -> Prop} {f : Exists p -> Set α}
 : ⋂ x, f x = ⋂ (i) (h : p i), f ⟨i, h⟩
· 使用定理 `Set.iInter_iInter_eq'`：iInter_iInter_eq' {f : ι -> α} {g : α -> Set β} :
 ⋂ (x) (y) (_ : f y = x), g x = ⋂ y, g (f y)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem neighborSet_iInf (f : ι → G.Subgraph) (v : V) :
    (⨅ i, f i).neighborSet v = (⋂ i, (f i).neighborSet v) ∩ G.neighborSet v := by simp [iInf]

@[simp]
/-
**SimpleGraph.Subgraph.edgeSet_top** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Subgra
ph`。
形式化陈述：edgeSet_top : (⊤ : Subgraph G).edgeSet = G.edgeSet
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem edgeSet_top : (⊤ : Subgraph G).edgeSet = G.edgeSet := rfl

@[simp]
/-
**SimpleGraph.Subgraph.edgeSet_bot** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Subgra
ph`。
形式化陈述：edgeSet_bot : (⊥ : Subgraph G).edgeSet = ∅
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
theorem edgeSet_bot : (⊥ : Subgraph G).edgeSet = ∅ :=
  Set.ext <| Sym2.ind (by simp)

@[simp]
/-
**SimpleGraph.Subgraph.edgeSet_inf** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Subgra
ph`。
形式化陈述：edgeSet_inf {H₁ H₂ : Subgraph G} : (H₁ ⊓ H₂).edgeSet = H₁.edgeSet inter H₂
.edgeSet
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
theorem edgeSet_inf {H₁ H₂ : Subgraph G} : (H₁ ⊓ H₂).edgeSet = H₁.edgeSet ∩ H₂.edgeSet :=
  Set.ext <| Sym2.ind (by simp)

@[simp]
/-
**SimpleGraph.Subgraph.edgeSet_sup** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Subgra
ph`。
形式化陈述：edgeSet_sup {H₁ H₂ : Subgraph G} : (H₁ ⊔ H₂).edgeSet = H₁.edgeSet union H₂
.edgeSet
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
theorem edgeSet_sup {H₁ H₂ : Subgraph G} : (H₁ ⊔ H₂).edgeSet = H₁.edgeSet ∪ H₂.edgeSet :=
  Set.ext <| Sym2.ind (by simp)

@[simp]
/-
**SimpleGraph.Subgraph.edgeSet_sSup** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Subgr
aph`。
形式化陈述：edgeSet_sSup (s : Set G.Subgraph) : (sSup s).edgeSet = ⋃ G' in s, edgeSet 
G'
参数：s : Set G.Subgraph。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Sym2.ind`：∀ {α : Type u_1} {f : Sym2 α → Prop}, (∀ (x y : α), f s(x, y))
 → ∀ (i : Sym2 α), f i
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem edgeSet_sSup (s : Set G.Subgraph) : (sSup s).edgeSet = ⋃ G' ∈ s, edgeSet G' := by
  ext e
  induction e
  simp

@[simp]
/-
**SimpleGraph.Subgraph.edgeSet_sInf** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Subgr
aph`。
形式化陈述：edgeSet_sInf (s : Set G.Subgraph) : (sInf s).edgeSet = (⋂ G' in s, edgeSet
 G') inter G.edgeSet
参数：s : Set G.Subgraph。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Sym2.ind`：∀ {α : Type u_1} {f : Sym2 α → Prop}, (∀ (x y : α), f s(x, y))
 → ∀ (i : Sym2 α), f i
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem edgeSet_sInf (s : Set G.Subgraph) :
    (sInf s).edgeSet = (⋂ G' ∈ s, edgeSet G') ∩ G.edgeSet := by
  ext e
  induction e
  simp

@[simp]
/-
**SimpleGraph.Subgraph.edgeSet_iSup** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Subgr
aph`。
形式化陈述：edgeSet_iSup (f : ι -> G.Subgraph) : (⨆ i, f i).edgeSet = ⋃ i, (f i).edgeS
et
参数：f : ι -> G.Subgraph。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.Subgraph.edgeSet_sSup`：edgeSet_sSup (s : Set G.Subgraph) : (
sSup s).edgeSet = ⋃ G' in s, edgeSet G'
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Set.iUnion_exists`：iUnion_exists {p : ι -> Prop} {f : Exists p -> Set α}
 : ⋃ x, f x = ⋃ (i) (h : p i), f ⟨i, h⟩
· 使用定理 `Set.iUnion_iUnion_eq'`：iUnion_iUnion_eq' {f : ι -> α} {g : α -> Set β} :
 ⋃ (x) (y) (_ : f y = x), g x = ⋃ y, g (f y)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem edgeSet_iSup (f : ι → G.Subgraph) :
    (⨆ i, f i).edgeSet = ⋃ i, (f i).edgeSet := by simp [iSup]

@[simp]
/-
**SimpleGraph.Subgraph.edgeSet_iInf** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Subgr
aph`。
形式化陈述：edgeSet_iInf (f : ι -> G.Subgraph) : (⨅ i, f i).edgeSet = (⋂ i, (f i).edge
Set) inter G.edgeSet
参数：f : ι -> G.Subgraph。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.Subgraph.edgeSet_sInf`：edgeSet_sInf (s : Set G.Subgraph) : (
sInf s).edgeSet = (⋂ G' in s, edgeSet G') inter G.edgeSet
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iInter_congr_Prop`：iInter_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iInter f₁ 
= iInter f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Set.iInter_exists`：iInter_exists {p : ι -> Prop} {f : Exists p -> Set α}
 : ⋂ x, f x = ⋂ (i) (h : p i), f ⟨i, h⟩
· 使用定理 `Set.iInter_iInter_eq'`：iInter_iInter_eq' {f : ι -> α} {g : α -> Set β} :
 ⋂ (x) (y) (_ : f y = x), g x = ⋂ y, g (f y)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem edgeSet_iInf (f : ι → G.Subgraph) :
    (⨅ i, f i).edgeSet = (⋂ i, (f i).edgeSet) ∩ G.edgeSet := by
  simp [iInf]

@[simp]
/-
**SimpleGraph.Subgraph.spanningCoe_top** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Su
bgraph`。
形式化陈述：spanningCoe_top : (⊤ : Subgraph G).spanningCoe = G
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem spanningCoe_top : (⊤ : Subgraph G).spanningCoe = G := rfl

@[simp]
/-
**SimpleGraph.Subgraph.spanningCoe_bot** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Su
bgraph`。
形式化陈述：spanningCoe_bot : (⊥ : Subgraph G).spanningCoe = ⊥
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem spanningCoe_bot : (⊥ : Subgraph G).spanningCoe = ⊥ := rfl

/-- Turn a subgraph of a `SimpleGraph` into a member of its subgraph type. -/
@[simps]
/-
**SimpleGraph.Subgraph._root_.SimpleGraph.toSubgraph** 是 Mathlib 中的一个定义，位于命名空间 `
SimpleGraph.Subgraph`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Turn a subgraph of a `SimpleGraph` into a member of its subgraph type.
-/
def _root_.SimpleGraph.toSubgraph (H : SimpleGraph V) (h : H ≤ G) : G.Subgraph where
  verts := Set.univ
  Adj := H.Adj
  adj_sub e := h e
  edge_vert _ := Set.mem_univ _
  symm := H.symm
/-
**SimpleGraph.Subgraph.support_mono** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Subgr
aph`。
形式化陈述：support_mono {H H' : Subgraph G} (h : H <= H') : H.support subseteq H'.sup
port
参数：h : H <= H'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetRel.dom_mono`：∀ {α : Type u_1} {β : Type u_2} {R₁ R₂ : SetRel α β}, R
₁ ⊆ R₂ → R₁.dom ⊆ R₂.dom
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem support_mono {H H' : Subgraph G} (h : H ≤ H') : H.support ⊆ H'.support :=
  SetRel.dom_mono fun _ hvw ↦ h.2 hvw
/-
**SimpleGraph.Subgraph._root_.SimpleGraph.toSubgraph.isSpanning** 是 Mathlib 中的一个
定理，位于命名空间 `SimpleGraph.Subgraph`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.SimpleGraph.toSubgraph.isSpanning (H : SimpleGraph V) (h : H ≤ G) :
    (toSubgraph H h).IsSpanning :=
  Set.mem_univ
/-
**SimpleGraph.Subgraph.spanningCoe_le_of_le** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGra
ph.Subgraph`。
形式化陈述：spanningCoe_le_of_le {H H' : Subgraph G} (h : H <= H') : H.spanningCoe <= 
H'.spanningCoe
参数：h : H <= H'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem spanningCoe_le_of_le {H H' : Subgraph G} (h : H ≤ H') : H.spanningCoe ≤ H'.spanningCoe :=
  h.2

@[simp]
/-
**SimpleGraph.Subgraph.sup_spanningCoe** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph.Su
bgraph`。
形式化陈述：sup_spanningCoe (H H' : Subgraph G) : (H ⊔ H').spanningCoe = H.spanningCoe
 ⊔ H'.spanningCoe
参数：H H' : Subgraph G。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma sup_spanningCoe (H H' : Subgraph G) :
    (H ⊔ H').spanningCoe = H.spanningCoe ⊔ H'.spanningCoe := rfl

/-- The bottom of the `Subgraph G` lattice is isomorphic to the empty graph on the empty
vertex type. -/
/-
**SimpleGraph.Subgraph.botIso** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph.Subgraph`。
形式化陈述：botIso : (⊥ : Subgraph G).coe ≃g emptyGraph Empty where toFun v
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The bottom of the `Subgraph G` lattice is isomorphic to the empty graph on the e
mpty
vertex type.
-/
def botIso : (⊥ : Subgraph G).coe ≃g emptyGraph Empty where
  toFun v := v.property.elim
  invFun v := v.elim
  left_inv := fun ⟨_, h⟩ ↦ h.elim
  right_inv v := v.elim
  map_rel_iff' := Iff.rfl
/-
**SimpleGraph.Subgraph.edgeSet_mono** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Subgr
aph`。
形式化陈述：edgeSet_mono {H₁ H₂ : Subgraph G} (h : H₁ <= H₂) : H₁.edgeSet <= H₂.edgeSe
t
参数：h : H₁ <= H₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Sym2.ind`：∀ {α : Type u_1} {f : Sym2 α → Prop}, (∀ (x y : α), f s(x, y))
 → ∀ (i : Sym2 α), f i
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem edgeSet_mono {H₁ H₂ : Subgraph G} (h : H₁ ≤ H₂) : H₁.edgeSet ≤ H₂.edgeSet :=
  Sym2.ind h.2
/-
**SimpleGraph.Subgraph.edgeSet_monotone** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.S
ubgraph`。
形式化陈述：edgeSet_monotone : Monotone (edgeSet (G
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Subgraph.edgeSet_mono`：edgeSet_mono {H₁ H₂ : Subgraph G} (h 
: H₁ <= H₂) : H₁.edgeSet <= H₂.edgeSet
-/
theorem edgeSet_monotone : Monotone (edgeSet (G := G)) :=
  fun _ _ ↦ edgeSet_mono
/-
**SimpleGraph.Subgraph._root_.Disjoint.edgeSet** 是 Mathlib 中的一个定理，位于命名空间 `Simple
Graph.Subgraph`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Disjoint.edgeSet {H₁ H₂ : Subgraph G} (h : Disjoint H₁ H₂) :
    Disjoint H₁.edgeSet H₂.edgeSet :=
  disjoint_iff_inf_le.mpr <| by simpa using edgeSet_mono h.le_bot

@[simp]
/-
**SimpleGraph.Subgraph.disjoint_verts_iff_disjoint** 是 Mathlib 中的一个引理，位于命名空间 `Si
mpleGraph.Subgraph`。
形式化陈述：disjoint_verts_iff_disjoint {H H' : Subgraph G} : Disjoint H.verts H'.vert
s ↔ Disjoint H H'
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `le_bot_iff`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a ≤ ⊥ ↔ a = ⊥
· 使用定理 `SimpleGraph.Subgraph.ext`：∀ {V : Type u} {G : SimpleGraph V} {x y : G.Su
bgraph}, x.verts = y.verts → x.Adj = y.Adj → x = y
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `SimpleGraph.Subgraph.edge_vert`：∀ {V : Type u} {G : SimpleGraph V} (self
 : G.Subgraph) {v w : V}, self.Adj v w → v ∈ self.verts
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Set.mem_singleton`：mem_singleton (a : α) : a in ({a} : Set α)
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
    have hle {M : Subgraph G} (h : v ∈ M.verts) : M' ≤ M := by constructor <;> simp [h, M']
    exact hdisj (hle <| h₀ hvS) (hle <| h₁ hvS) |>.left <| Set.mem_singleton v

section map
variable {G' : SimpleGraph W} {f : G →g G'}

/-- Graph homomorphisms induce a covariant function on subgraphs. -/
@[simps]
/-
**SimpleGraph.Subgraph.map** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph.Subgraph`。
形式化陈述：{V : Type u} → {W : Type v} → {G : SimpleGraph V} → {G' : SimpleGraph W} →
 G →g G' → G.Subgraph → G'.Subgraph
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Graph homomorphisms induce a covariant function on subgraphs.
-/
protected def map (f : G →g G') (H : G.Subgraph) : G'.Subgraph where
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
/-
**SimpleGraph.Subgraph.map_id** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Subgraph`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} (H : G.Subgraph), SimpleGraph.Subgraph.
map SimpleGraph.Hom.id H = H
参数：H : G.Subgraph。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Subgraph.ext`：∀ {V : Type u} {G : SimpleGraph V} {x y : G.Su
bgraph}, x.verts = y.verts → x.Adj = y.Adj → x = y
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.Subgraph.map_verts`：∀ {V : Type u} {W : Type v} {G : SimpleG
raph V} {G' : SimpleGraph W} (f : G →g G') (H : G.Subgraph),   (SimpleGraph.Subg
raph.map f H).verts …
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `RelHom.id_apply`：∀ {α : Type u_1} (r : α → α → Prop) (x : α), (RelHom.id
 r) x = x
· 使用定理 `Set.image_id'`：image_id' (s : Set α) : (fun x => x) '' s = s
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `SimpleGraph.Subgraph.map_adj`：∀ {V : Type u} {W : Type v} {G : SimpleGra
ph V} {G' : SimpleGraph W} (f : G →g G') (H : G.Subgraph) (a a_1 : W),   (Simple
Graph.Subgraph.map…
· 使用定理 `Relation.map_id_id`：∀ {α : Type u_1} {β : Type u_2} (r : α → β → Prop), 
Relation.Map r id id = r
-/
@[simp] lemma map_id (H : G.Subgraph) : H.map Hom.id = H := by ext <;> simp
/-
**SimpleGraph.Subgraph.map_comp** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph.Subgraph`
。
形式化陈述：map_comp {U : Type*} {G'' : SimpleGraph U} (H : G.Subgraph) (f : G ->g G')
 (g : G' ->g G'') : H.map (g.comp f) = (H.map f).map g
参数：H : G.Subgraph；f : G ->g G'；g : G' ->g G''。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Subgraph.ext`：∀ {V : Type u} {G : SimpleGraph V} {x y : G.Su
bgraph}, x.verts = y.verts → x.Adj = y.Adj → x = y
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `RelHom.comp_apply`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {r : α
 → α → Prop} {s : β → β → Prop} {t : γ → γ → Prop} (g : s →r t)   (f : r →r s) (
x : α),…
· 使用定理 `SimpleGraph.Subgraph.mk.congr_simp`：∀ {V : Type u} {G : SimpleGraph V} (
verts verts_1 : Set V) (e_verts : verts = verts_1) (Adj Adj_1 : V → V → Prop)   
(e_Adj : Adj = Adj_1) (a…
· 使用定理 `Relation.map_map`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {δ : Ty
pe u_4} {ε : Type u_5} {ζ : Type u_6} (r : α → β → Prop)   (f₁ : α → γ) (g₁ : β 
→ δ) (…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma map_comp {U : Type*} {G'' : SimpleGraph U} (H : G.Subgraph) (f : G →g G') (g : G' →g G'') :
    H.map (g.comp f) = (H.map f).map g := by ext <;> simp [Subgraph.map]
/-
**SimpleGraph.Subgraph.map_mono** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Subgraph`
。
形式化陈述：∀ {V : Type u} {W : Type v} {G : SimpleGraph V} {G' : SimpleGraph W} {f : 
G →g G'} {H₁ H₂ : G.Subgraph},   H₁ ≤ H₂ → SimpleGraph.Subgraph.map f H₁ ≤ Simpl
eGraph.Subgraph.map f H₂
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.Subgraph.map_verts`：∀ {V : Type u} {W : Type v} {G : SimpleG
raph V} {G' : SimpleGraph W} (f : G →g G') (H : G.Subgraph),   (SimpleGraph.Subg
raph.map f H).verts …
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
@[gcongr] lemma map_mono {H₁ H₂ : G.Subgraph} (hH : H₁ ≤ H₂) : H₁.map f ≤ H₂.map f := by
  constructor
  · intro
    simp only [map_verts, Set.mem_image, forall_exists_index, and_imp]
    rintro v hv rfl
    exact ⟨_, hH.1 hv, rfl⟩
  · rintro _ _ ⟨u, v, ha, rfl, rfl⟩
    exact ⟨_, _, hH.2 ha, rfl, rfl⟩
/-
**SimpleGraph.Subgraph.map_monotone** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph.Subgr
aph`。
形式化陈述：map_monotone : Monotone (Subgraph.map f)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Subgraph.map_mono`：∀ {V : Type u} {W : Type v} {G : SimpleGr
aph V} {G' : SimpleGraph W} {f : G →g G'} {H₁ H₂ : G.Subgraph},   H₁ ≤ H₂ → Simp
leGraph.Subgraph.ma…
-/
lemma map_monotone : Monotone (Subgraph.map f) := fun _ _ ↦ map_mono
/-
**SimpleGraph.Subgraph.map_sup** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Subgraph`。
形式化陈述：map_sup (f : G ->g G') (H₁ H₂ : G.Subgraph) : (H₁ ⊔ H₂).map f = H₁.map f ⊔
 H₂.map f
参数：f : G ->g G'；H₁ H₂ : G.Subgraph。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Subgraph.ext`：∀ {V : Type u} {G : SimpleGraph V} {x y : G.Su
bgraph}, x.verts = y.verts → x.Adj = y.Adj → x = y
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `SimpleGraph.Subgraph.map_verts`：∀ {V : Type u} {W : Type v} {G : SimpleG
raph V} {G' : SimpleGraph W} (f : G →g G') (H : G.Subgraph),   (SimpleGraph.Subg
raph.map f H).verts …
· 使用定理 `Set.image_union`：image_union (f : α -> β) (s t : Set α) : f '' (s union 
t) = f '' s union f '' t
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `SimpleGraph.Subgraph.map_adj`：∀ {V : Type u} {W : Type v} {G : SimpleGra
ph V} {G' : SimpleGraph W} (f : G →g G') (H : G.Subgraph) (a a_1 : W),   (Simple
Graph.Subgraph.map…
-/
theorem map_sup (f : G →g G') (H₁ H₂ : G.Subgraph) : (H₁ ⊔ H₂).map f = H₁.map f ⊔ H₂.map f := by
  ext <;> simp [Set.image_union, map_adj, sup_adj, Relation.Map, or_and_right, exists_or]
/-
**SimpleGraph.Subgraph.map_iso_top** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Subgra
ph`。
形式化陈述：∀ {V : Type u} {W : Type v} {G : SimpleGraph V} {H : SimpleGraph W} (e : G
 ≃g H), SimpleGraph.Subgraph.map e.toHom ⊤ = ⊤
参数：e : G ≃g H。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Subgraph.ext`：∀ {V : Type u} {G : SimpleGraph V} {x y : G.Su
bgraph}, x.verts = y.verts → x.Adj = y.Adj → x = y
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `SimpleGraph.Subgraph.map_verts`：∀ {V : Type u} {W : Type v} {G : SimpleG
raph V} {G' : SimpleGraph W} (f : G →g G') (H : G.Subgraph),   (SimpleGraph.Subg
raph.map f H).verts …
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
· 使用定理 `EquivLike.range_eq_univ`：range_eq_univ {α : Type*} {β : Type*} {E : Type
*} [EquivLike E α β] (e : E) : range e = univ
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `SimpleGraph.Subgraph.map_adj`：∀ {V : Type u} {W : Type v} {G : SimpleGra
ph V} {G' : SimpleGraph W} (f : G →g G') (H : G.Subgraph) (a a_1 : W),   (Simple
Graph.Subgraph.map…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RelIso.map_rel_iff`：map_rel_iff (f : r ≃r s) {a b} : s (f a) (f b) ↔ r a
 b
· 使用引理 `RelIso.eq_symm_apply`：eq_symm_apply (e : r ≃r s) {x y} : y = e.symm x ↔ 
e y = x
· 使用定理 `RelIso.apply_symm_apply`：∀ {α : Type u_1} {β : Type u_2} {r : α → α → Pr
op} {s : β → β → Prop} (e : r ≃r s) (x : β), e (e.symm x) = x
-/
@[simp] lemma map_iso_top {H : SimpleGraph W} (e : G ≃g H) : Subgraph.map e.toHom ⊤ = ⊤ := by
  ext <;> simp [Relation.Map, ← e.eq_symm_apply, ← e.map_rel_iff]
/-
**SimpleGraph.Subgraph.edgeSet_map** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Subgra
ph`。
形式化陈述：∀ {V : Type u} {W : Type v} {G : SimpleGraph V} {G' : SimpleGraph W} (f : 
G →g G') (H : G.Subgraph),   (SimpleGraph.Subgraph.map f H).edgeSet = Sym2.map ⇑
f '' H.edgeSet
参数：f : G →g G'；H : G.Subgraph；SimpleGraph.Subgraph.map f H。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Sym2.fromRel_relationMap`：fromRel_relationMap {r : α -> α -> Prop} (hr :
 Std.Symm r) (f : α -> β) : fromRel (hr.map f) = Sym2.map f '' Sym2.fromRel hr
· 使用定理 `SimpleGraph.Subgraph.symm`：∀ {V : Type u} {G : SimpleGraph V} (self : G.
Subgraph), Std.Symm self.Adj
-/
@[simp] lemma edgeSet_map (f : G →g G') (H : G.Subgraph) :
    (H.map f).edgeSet = Sym2.map f '' H.edgeSet := Sym2.fromRel_relationMap ..

end map

/-- Graph homomorphisms induce a contravariant function on subgraphs. -/
@[simps]
/-
**SimpleGraph.Subgraph.comap** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph.Subgraph`。
形式化陈述：{V : Type u} → {W : Type v} → {G : SimpleGraph V} → {G' : SimpleGraph W} →
 G →g G' → G'.Subgraph → G.Subgraph
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Graph homomorphisms induce a contravariant function on subgraphs.
-/
protected def comap {G' : SimpleGraph W} (f : G →g G') (H : G'.Subgraph) : G.Subgraph where
  verts := f ⁻¹' H.verts
  Adj u v := G.Adj u v ∧ H.Adj (f u) (f v)
  adj_sub h := h.1
  edge_vert h := Set.mem_preimage.1 (H.edge_vert h.2)
  symm.symm _ _ h := ⟨h.left.symm, h.right.symm⟩
/-
**SimpleGraph.Subgraph.comap_monotone** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Sub
graph`。
形式化陈述：comap_monotone {G' : SimpleGraph W} (f : G ->g G') : Monotone (Subgraph.co
map f)
参数：f : G ->g G'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.Subgraph.comap_verts`：∀ {V : Type u} {W : Type v} {G : Simpl
eGraph V} {G' : SimpleGraph W} (f : G →g G') (H : G'.Subgraph),   (SimpleGraph.S
ubgraph.comap f H).ver…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `SimpleGraph.Subgraph.comap_adj`：∀ {V : Type u} {W : Type v} {G : SimpleG
raph V} {G' : SimpleGraph W} (f : G →g G') (H : G'.Subgraph) (u v : V),   (Simpl
eGraph.Subgraph.coma…
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem comap_monotone {G' : SimpleGraph W} (f : G →g G') : Monotone (Subgraph.comap f) := by
  intro H H' h
  constructor
  · intro
    simp only [comap_verts, Set.mem_preimage]
    apply h.1
  · intro v w
    simp +contextual only [comap_adj, and_imp, true_and]
    intro
    apply h.2
/-
**SimpleGraph.Subgraph.comap_equiv_top** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Su
bgraph`。
形式化陈述：∀ {V : Type u} {W : Type v} {G : SimpleGraph V} {H : SimpleGraph W} (f : G
 →g H), SimpleGraph.Subgraph.comap f ⊤ = ⊤
参数：f : G →g H。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Subgraph.ext`：∀ {V : Type u} {G : SimpleGraph V} {x y : G.Su
bgraph}, x.verts = y.verts → x.Adj = y.Adj → x = y
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `SimpleGraph.Subgraph.comap_verts`：∀ {V : Type u} {W : Type v} {G : Simpl
eGraph V} {G' : SimpleGraph W} (f : G →g G') (H : G'.Subgraph),   (SimpleGraph.S
ubgraph.comap f H).ver…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `SimpleGraph.Subgraph.comap_adj`：∀ {V : Type u} {W : Type v} {G : SimpleG
raph V} {G' : SimpleGraph W} (f : G →g G') (H : G'.Subgraph) (u v : V),   (Simpl
eGraph.Subgraph.coma…
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `SimpleGraph.Hom.map_adj`：map_adj {v w : V} (h : G.Adj v w) : G'.Adj (f v
) (f w)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
@[simp] lemma comap_equiv_top {H : SimpleGraph W} (f : G →g H) : Subgraph.comap f ⊤ = ⊤ := by
  ext <;> simp +contextual [f.map_adj]
/-
**SimpleGraph.Subgraph.map_le_iff_le_comap** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGrap
h.Subgraph`。
形式化陈述：map_le_iff_le_comap {G' : SimpleGraph W} (f : G ->g G') (H : G.Subgraph) (
H' : G'.Subgraph) : H.map f <= H' ↔ H <= H'.comap f
参数：f : G ->g G'；H : G.Subgraph；H' : G'.Subgraph。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.Subgraph.comap_verts`：∀ {V : Type u} {W : Type v} {G : Simpl
eGraph V} {G' : SimpleGraph W} (f : G →g G') (H : G'.Subgraph),   (SimpleGraph.S
ubgraph.comap f H).ver…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `SimpleGraph.Subgraph.comap_adj`：∀ {V : Type u} {W : Type v} {G : SimpleG
raph V} {G' : SimpleGraph W} (f : G →g G') (H : G'.Subgraph) (u v : V),   (Simpl
eGraph.Subgraph.coma…
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `SimpleGraph.Subgraph.adj_sub`：∀ {V : Type u} {G : SimpleGraph V} (self :
 G.Subgraph) {v w : V}, self.Adj v w → G.Adj v w
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `SimpleGraph.Subgraph.map_verts`：∀ {V : Type u} {W : Type v} {G : SimpleG
raph V} {G' : SimpleGraph W} (f : G →g G') (H : G.Subgraph),   (SimpleGraph.Subg
raph.map f H).verts …
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `SimpleGraph.Subgraph.map_adj`：∀ {V : Type u} {W : Type v} {G : SimpleGra
ph V} {G' : SimpleGraph W} (f : G →g G') (H : G.Subgraph) (a a_1 : W),   (Simple
Graph.Subgraph.map…
-/
theorem map_le_iff_le_comap {G' : SimpleGraph W} (f : G →g G') (H : G.Subgraph) (H' : G'.Subgraph) :
    H.map f ≤ H' ↔ H ≤ H'.comap f := by
  refine ⟨fun h ↦ ⟨fun v hv ↦ ?_, fun v w hvw ↦ ?_⟩, fun h ↦ ⟨fun v ↦ ?_, fun v w ↦ ?_⟩⟩
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
/-
**SimpleGraph.Subgraph.** 是 Mathlib 中的一个实例，位于命名空间 `SimpleGraph.Subgraph`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [DecidableEq V] [Fintype V] [DecidableRel G.Adj] : Fintype G.Subgraph := by
  refine .ofBijective
    (α := {H : Finset V × (V → V → Bool) //
      (∀ a b, H.2 a b → G.Adj a b) ∧ (∀ a b, H.2 a b → a ∈ H.1) ∧ ∀ a b, H.2 a b = H.2 b a})
    (fun H ↦ ⟨H.1.1, fun a b ↦ H.1.2 a b, @H.2.1, @H.2.2.1, by simp [symm_def, H.2.2.2]⟩)
    ⟨?_, fun H ↦ ?_⟩
  · rintro ⟨⟨_, _⟩, -⟩ ⟨⟨_, _⟩, -⟩
    simp [funext_iff]
  · classical
    exact ⟨⟨(H.verts.toFinset, fun a b ↦ H.Adj a b), fun a b ↦ by simpa using H.adj_sub,
      fun a b ↦ by simpa using H.edge_vert, by simp [H.adj_comm]⟩, by simp⟩
/-
**SimpleGraph.Subgraph.** 是 Mathlib 中的一个实例，位于命名空间 `SimpleGraph.Subgraph`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Finite V] : Finite G.Subgraph := by classical cases nonempty_fintype V; infer_instance

/-- Given two subgraphs, one a subgraph of the other, there is an induced injective homomorphism of
the subgraphs as graphs. -/
@[simps]
/-
**SimpleGraph.Subgraph.inclusion** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph.Subgraph
`。
形式化陈述：inclusion {x y : Subgraph G} (h : x <= y) : x.coe ->g y.coe where toFun v
参数：h : x <= y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given two subgraphs, one a subgraph of the other, there is an induced injective 
homomorphism of
the subgraphs as graphs.
-/
def inclusion {x y : Subgraph G} (h : x ≤ y) : x.coe →g y.coe where
  toFun v := ⟨↑v, And.left h v.property⟩
  map_rel' hvw := h.2 hvw
/-
**SimpleGraph.Subgraph.inclusion.injective** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGrap
h.Subgraph.inclusion`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} {x y : G.Subgraph} (h : x ≤ y),   Funct
ion.Injective ⇑(SimpleGraph.Subgraph.inclusion h)
参数：h : x ≤ y；SimpleGraph.Subgraph.inclusion h。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem inclusion.injective {x y : Subgraph G} (h : x ≤ y) : Function.Injective (inclusion h) :=
  fun _ _ h ↦ Subtype.ext congr(Subtype.val $h)

/-- There is an induced injective homomorphism of a subgraph of `G` into `G`. -/
@[simps]
/-
**SimpleGraph.Subgraph.hom** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph.Subgraph`。
形式化陈述：{V : Type u} → {G : SimpleGraph V} → (x : G.Subgraph) → x.coe →g G
参数：x : G.Subgraph。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
There is an induced injective homomorphism of a subgraph of `G` into `G`.
-/
protected def hom (x : Subgraph G) : x.coe →g G where
  toFun v := v
  map_rel' := x.adj_sub
/-
**SimpleGraph.Subgraph.coe_hom** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Subgraph`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} (x : G.Subgraph), ⇑x.hom = fun v => ↑v
参数：x : G.Subgraph。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma coe_hom (x : Subgraph G) :
    (x.hom : x.verts → V) = (fun (v : x.verts) => (v : V)) := rfl
/-
**SimpleGraph.Subgraph.hom_injective** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Subg
raph`。
形式化陈述：hom_injective {x : Subgraph G} : Function.Injective x.hom
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
-/
theorem hom_injective {x : Subgraph G} : Function.Injective x.hom :=
  fun _ _ ↦ Subtype.ext
/-
**SimpleGraph.Subgraph.map_hom_top** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Subgra
ph`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} (G' : G.Subgraph), SimpleGraph.Subgraph
.map G'.hom ⊤ = G'
参数：G' : G.Subgraph。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Subgraph.ext`：∀ {V : Type u} {G : SimpleGraph V} {x y : G.Su
bgraph}, x.verts = y.verts → x.Adj = y.Adj → x = y
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.Subgraph.map_verts`：∀ {V : Type u} {W : Type v} {G : SimpleG
raph V} {G' : SimpleGraph W} (f : G →g G') (H : G.Subgraph),   (SimpleGraph.Subg
raph.map f H).verts …
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `SimpleGraph.Subgraph.hom_apply`：∀ {V : Type u} {G : SimpleGraph V} (x : 
G.Subgraph) (v : ↑x.verts), x.hom v = ↑v
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
· 使用定理 `Subtype.range_coe_subtype`：range_coe_subtype {p : α -> Prop} : range ((↑
) : Subtype p -> α) = { x | p x }
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `SimpleGraph.Subgraph.map_adj`：∀ {V : Type u} {W : Type v} {G : SimpleGra
ph V} {G' : SimpleGraph W} (f : G →g G') (H : G.Subgraph) (a a_1 : W),   (Simple
Graph.Subgraph.map…
· 使用定理 `SimpleGraph.Subgraph.coe_adj`：∀ {V : Type u} {G : SimpleGraph V} (G' : G
.Subgraph) (v w : ↑G'.verts), G'.coe.Adj v w = G'.Adj ↑v ↑w
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Exists.elim`：∀ {α : Sort u} {p : α → Prop} {b : Prop}, (∃ x, p x) → (∀ (
a : α), p a → b) → b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `SimpleGraph.Subgraph.edge_vert`：∀ {V : Type u} {G : SimpleGraph V} (self
 : G.Subgraph) {v w : V}, self.Adj v w → v ∈ self.verts
· 使用定理 `SimpleGraph.Subgraph.Adj.symm`：∀ {V : Type u} {G : SimpleGraph V} {G' : 
G.Subgraph} {u v : V}, G'.Adj u v → G'.Adj v u
-/
@[simp] lemma map_hom_top (G' : G.Subgraph) : Subgraph.map G'.hom ⊤ = G' := by
  aesop (add unfold safe Relation.Map, unsafe G'.edge_vert, unsafe Adj.symm)

/-- There is an induced injective homomorphism of a subgraph of `G` as
a spanning subgraph into `G`. -/
@[simps]
/-
**SimpleGraph.Subgraph.spanningHom** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph.Subgra
ph`。
形式化陈述：spanningHom (x : Subgraph G) : x.spanningCoe ->g G where toFun
参数：x : Subgraph G。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Subgraph.adj_sub`：∀ {V : Type u} {G : SimpleGraph V} (self :
 G.Subgraph) {v w : V}, self.Adj v w → G.Adj v w

--- 原说明 ---
There is an induced injective homomorphism of a subgraph of `G` as
a spanning subgraph into `G`.
-/
def spanningHom (x : Subgraph G) : x.spanningCoe →g G where
  toFun := id
  map_rel' := x.adj_sub
/-
**SimpleGraph.Subgraph.spanningHom_injective** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGr
aph.Subgraph`。
形式化陈述：spanningHom_injective {x : Subgraph G} : Function.Injective x.spanningHom
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem spanningHom_injective {x : Subgraph G} : Function.Injective x.spanningHom :=
  fun _ _ ↦ id
/-
**SimpleGraph.Subgraph.neighborSet_subset_of_subgraph** 是 Mathlib 中的一个定理，位于命名空间 
`SimpleGraph.Subgraph`。
形式化陈述：neighborSet_subset_of_subgraph {x y : Subgraph G} (h : x <= y) (v : V) : x
.neighborSet v subseteq y.neighborSet v
参数：h : x <= y；v : V。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem neighborSet_subset_of_subgraph {x y : Subgraph G} (h : x ≤ y) (v : V) :
    x.neighborSet v ⊆ y.neighborSet v :=
  fun _ h' ↦ h.2 h'
/-
**SimpleGraph.Subgraph.neighborSet.decidablePred** 是 Mathlib 中的一个定义，位于命名空间 `Simp
leGraph.Subgraph.neighborSet`。
形式化陈述：{V : Type u} →   {G : SimpleGraph V} →     (G' : G.Subgraph) → [h : Decida
bleRel G'.Adj] → (v : V) → DecidablePred fun x => x ∈ G'.neighborSet v
参数：G' : G.Subgraph；v : V。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance neighborSet.decidablePred (G' : Subgraph G) [h : DecidableRel G'.Adj] (v : V) :
    DecidablePred (· ∈ G'.neighborSet v) :=
  h v

/-- If a graph is locally finite at a vertex, then so is a subgraph of that graph. -/
/-
**SimpleGraph.Subgraph.finiteAt** 是 Mathlib 中的一个实例，位于命名空间 `SimpleGraph.Subgraph`
。
形式化陈述：finiteAt {G' : Subgraph G} (v : G'.verts) [DecidableRel G'.Adj] [Fintype (
G.neighborSet v)] : Fintype (G'.neighborSet v)
参数：v : G'.verts；G.neighborSet v。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If a graph is locally finite at a vertex, then so is a subgraph of that graph.
-/
instance finiteAt {G' : Subgraph G} (v : G'.verts) [DecidableRel G'.Adj]
    [Fintype (G.neighborSet v)] : Fintype (G'.neighborSet v) :=
  Set.fintypeSubset (G.neighborSet v) (G'.neighborSet_subset v)

/-- If a subgraph is locally finite at a vertex, then so are subgraphs of that subgraph.

This is not an instance because `G''` cannot be inferred. -/
@[instance_reducible]
/-
**SimpleGraph.Subgraph.finiteAtOfSubgraph** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph
.Subgraph`。
形式化陈述：finiteAtOfSubgraph {G' G'' : Subgraph G} [DecidableRel G'.Adj] (h : G' <= 
G'') (v : G'.verts) [Fintype (G''.neighborSet v)] : Fintype (G'.neighborSet v)
参数：h : G' <= G''；v : G'.verts；G''.neighborSet v。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If a subgraph is locally finite at a vertex, then so are subgraphs of that subgr
aph.

This is not an instance because `G''` cannot be inferred.
-/
def finiteAtOfSubgraph {G' G'' : Subgraph G} [DecidableRel G'.Adj] (h : G' ≤ G'') (v : G'.verts)
    [Fintype (G''.neighborSet v)] : Fintype (G'.neighborSet v) :=
  Set.fintypeSubset (G''.neighborSet v) (neighborSet_subset_of_subgraph h v)
/-
**SimpleGraph.Subgraph.** 是 Mathlib 中的一个实例，位于命名空间 `SimpleGraph.Subgraph`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (G' : Subgraph G) [Fintype G'.verts] (v : V) [DecidablePred (· ∈ G'.neighborSet v)] :
    Fintype (G'.neighborSet v) :=
  Set.fintypeSubset G'.verts (neighborSet_subset_verts G' v)
/-
**SimpleGraph.Subgraph.coeFiniteAt** 是 Mathlib 中的一个实例，位于命名空间 `SimpleGraph.Subgra
ph`。
形式化陈述：coeFiniteAt {G' : Subgraph G} (v : G'.verts) [Fintype (G'.neighborSet v)] 
: Fintype (G'.coe.neighborSet v)
参数：v : G'.verts；G'.neighborSet v。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
instance coeFiniteAt {G' : Subgraph G} (v : G'.verts) [Fintype (G'.neighborSet v)] :
    Fintype (G'.coe.neighborSet v) :=
  Fintype.ofEquiv _ (coeNeighborSetEquiv v).symm
/-
**SimpleGraph.Subgraph.IsSpanning.card_verts** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGr
aph.Subgraph.IsSpanning`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} [inst : Fintype V] {G' : G.Subgraph} [i
nst_1 : Fintype ↑G'.verts],   G'.IsSpanning → G'.verts.toFinset.card = Fintype.c
ard V
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.toFinset_congr`：toFinset_congr {s t : Set α} [Fintype s] [Fintype t]
 (h : s = t) : toFinset s = toFinset t
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `SimpleGraph.Subgraph.isSpanning_iff`：isSpanning_iff {G' : Subgraph G} : 
G'.IsSpanning ↔ G'.verts = Set.univ
· 使用定理 `Set.toFinset_univ`：toFinset_univ [Fintype α] [Fintype (Set.univ : Set α)
] : (Set.univ : Set α).toFinset = Finset.univ
-/
theorem IsSpanning.card_verts [Fintype V] {G' : Subgraph G} [Fintype G'.verts] (h : G'.IsSpanning) :
    G'.verts.toFinset.card = Fintype.card V := by
  simp only [isSpanning_iff.1 h, Set.toFinset_univ]
  congr

/-- The degree of a vertex in a subgraph. It's zero for vertices outside the subgraph. -/
/-
**SimpleGraph.Subgraph.degree** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph.Subgraph`。
形式化陈述：degree (G' : Subgraph G) (v : V) [Fintype (G'.neighborSet v)] : Nat
参数：G' : Subgraph G；v : V；G'.neighborSet v。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The degree of a vertex in a subgraph. It's zero for vertices outside the subgrap
h.
-/
def degree (G' : Subgraph G) (v : V) [Fintype (G'.neighborSet v)] : ℕ :=
  Fintype.card (G'.neighborSet v)
/-
**SimpleGraph.Subgraph.finset_card_neighborSet_eq_degree** 是 Mathlib 中的一个定理，位于命名
空间 `SimpleGraph.Subgraph`。
形式化陈述：finset_card_neighborSet_eq_degree {G' : Subgraph G} {v : V} [Fintype (G'.n
eighborSet v)] : (G'.neighborSet v).toFinset.card = G'.degree v
参数：G'.neighborSet v。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.Subgraph.degree.eq_1`：∀ {V : Type u} {G : SimpleGraph V} (G'
 : G.Subgraph) (v : V) [inst : Fintype ↑(G'.neighborSet v)],   G'.degree v = Fin
type.card ↑(G'.neighbo…
· 使用定理 `Set.toFinset_card`：toFinset_card {α : Type*} (s : Set α) [Fintype s] : s
.toFinset.card = Fintype.card s
-/
theorem finset_card_neighborSet_eq_degree {G' : Subgraph G} {v : V} [Fintype (G'.neighborSet v)] :
    (G'.neighborSet v).toFinset.card = G'.degree v := by
  rw [degree, Set.toFinset_card]
/-
**SimpleGraph.Subgraph.degree_of_notMem_verts** 是 Mathlib 中的一个定理，位于命名空间 `SimpleG
raph.Subgraph`。
形式化陈述：degree_of_notMem_verts {G' : Subgraph G} {v : V} [Fintype (G'.neighborSet 
v)] (h : v ∉ G'.verts) : G'.degree v = 0
参数：G'.neighborSet v；h : v ∉ G'.verts。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.Subgraph.degree.eq_1`：∀ {V : Type u} {G : SimpleGraph V} (G'
 : G.Subgraph) (v : V) [inst : Fintype ↑(G'.neighborSet v)],   G'.degree v = Fin
type.card ↑(G'.neighbo…
· 使用定理 `Fintype.card_eq_zero_iff`：card_eq_zero_iff : card α = 0 ↔ IsEmpty α
· 使用定理 `isEmpty_subtype`：isEmpty_subtype (p : α -> Prop) : IsEmpty (Subtype p) ↔
 forall x, ¬p x
· 使用定理 `SimpleGraph.Subgraph.Adj.fst_mem`：∀ {V : Type u} {G : SimpleGraph V} {H 
: G.Subgraph} {u v : V}, H.Adj u v → u ∈ H.verts
-/
theorem degree_of_notMem_verts {G' : Subgraph G} {v : V} [Fintype (G'.neighborSet v)]
    (h : v ∉ G'.verts) : G'.degree v = 0 := by
  rw [degree, Fintype.card_eq_zero_iff, isEmpty_subtype]
  intro w
  by_contra hw
  exact h hw.fst_mem
/-
**SimpleGraph.Subgraph.degree_le** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Subgraph
`。
形式化陈述：degree_le (G' : Subgraph G) (v : V) [Fintype (G'.neighborSet v)] [Fintype 
(G.neighborSet v)] : G'.degree v <= G.degree v
参数：G' : Subgraph G；v : V；G'.neighborSet v；G.neighborSet v。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SimpleGraph.card_neighborSet_eq_degree`：card_neighborSet_eq_degree : Fin
type.card (G.neighborSet v) = G.degree v
· 使用定理 `Set.card_le_card`：card_le_card {s t : Set α} [Fintype s] [Fintype t] (hs
ub : s subseteq t) : Fintype.card s <= Fintype.card t
· 使用定理 `SimpleGraph.Subgraph.neighborSet_subset`：neighborSet_subset (G' : Subgra
ph G) (v : V) : G'.neighborSet v subseteq G.neighborSet v
-/
theorem degree_le (G' : Subgraph G) (v : V) [Fintype (G'.neighborSet v)]
    [Fintype (G.neighborSet v)] : G'.degree v ≤ G.degree v := by
  rw [← card_neighborSet_eq_degree]
  exact Set.card_le_card (G'.neighborSet_subset v)
/-
**SimpleGraph.Subgraph.degree_le'** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Subgrap
h`。
形式化陈述：degree_le' (G' G'' : Subgraph G) (h : G' <= G'') (v : V) [Fintype (G'.neig
hborSet v)] [Fintype (G''.neighborSet v)] : G'.degree v <= G''.degree v
参数：G' G'' : Subgraph G；h : G' <= G''；v : V；G'.neighborSet v；G''.neighborSet v。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.card_le_card`：card_le_card {s t : Set α} [Fintype s] [Fintype t] (hs
ub : s subseteq t) : Fintype.card s <= Fintype.card t
· 使用定理 `SimpleGraph.Subgraph.neighborSet_subset_of_subgraph`：neighborSet_subset_
of_subgraph {x y : Subgraph G} (h : x <= y) (v : V) : x.neighborSet v subseteq y
.neighborSet v
-/
theorem degree_le' (G' G'' : Subgraph G) (h : G' ≤ G'') (v : V) [Fintype (G'.neighborSet v)]
    [Fintype (G''.neighborSet v)] : G'.degree v ≤ G''.degree v :=
  Set.card_le_card (neighborSet_subset_of_subgraph h v)

@[simp]
/-
**SimpleGraph.Subgraph.coe_degree** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Subgrap
h`。
形式化陈述：coe_degree (G' : Subgraph G) (v : G'.verts) [Fintype (G'.coe.neighborSet v
)] [Fintype (G'.neighborSet v)] : G'.coe.degree v = G'.degree v
参数：G' : Subgraph G；v : G'.verts；G'.coe.neighborSet v；G'.neighborSet v。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SimpleGraph.card_neighborSet_eq_degree`：card_neighborSet_eq_degree : Fin
type.card (G.neighborSet v) = G.degree v
· 使用定理 `Fintype.card_congr`：card_congr {α β} [Fintype α] [Fintype β] (f : α ≃ β)
 : card α = card β
-/
theorem coe_degree (G' : Subgraph G) (v : G'.verts) [Fintype (G'.coe.neighborSet v)]
    [Fintype (G'.neighborSet v)] : G'.coe.degree v = G'.degree v := by
  rw [← card_neighborSet_eq_degree]
  exact Fintype.card_congr (coeNeighborSetEquiv v)

@[simp]
/-
**SimpleGraph.Subgraph.degree_spanningCoe** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph
.Subgraph`。
形式化陈述：degree_spanningCoe {G' : G.Subgraph} (v : V) [Fintype (G'.neighborSet v)] 
[Fintype (G'.spanningCoe.neighborSet v)] : G'.spanningCoe.degree v = G'.degree v
参数：v : V；G'.neighborSet v；G'.spanningCoe.neighborSet v。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SimpleGraph.card_neighborSet_eq_degree`：card_neighborSet_eq_degree : Fin
type.card (G.neighborSet v) = G.degree v
· 使用定理 `SimpleGraph.Subgraph.degree.eq_1`：∀ {V : Type u} {G : SimpleGraph V} (G'
 : G.Subgraph) (v : V) [inst : Fintype ↑(G'.neighborSet v)],   G'.degree v = Fin
type.card ↑(G'.neighbo…
· 使用定理 `Fintype.card_congr'`：card_congr' {α β} [Fintype α] [Fintype β] (h : α = 
β) : card α = card β
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
-/
theorem degree_spanningCoe {G' : G.Subgraph} (v : V) [Fintype (G'.neighborSet v)]
    [Fintype (G'.spanningCoe.neighborSet v)] : G'.spanningCoe.degree v = G'.degree v := by
  rw [← card_neighborSet_eq_degree, Subgraph.degree]
  congr!
/-
**SimpleGraph.Subgraph.degree_pos_iff_exists_adj** 是 Mathlib 中的一个定理，位于命名空间 `Simp
leGraph.Subgraph`。
形式化陈述：degree_pos_iff_exists_adj {G' : Subgraph G} {v : V} [Fintype (G'.neighborS
et v)] : 0 < G'.degree v ↔ exists w, G'.Adj v w
参数：G'.neighborSet v。
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
theorem degree_pos_iff_exists_adj {G' : Subgraph G} {v : V} [Fintype (G'.neighborSet v)] :
    0 < G'.degree v ↔ ∃ w, G'.Adj v w := by
  simp only [degree, Fintype.card_pos_iff, nonempty_subtype, mem_neighborSet]
/-
**SimpleGraph.Subgraph.degree_eq_zero_of_subsingleton** 是 Mathlib 中的一个定理，位于命名空间 
`SimpleGraph.Subgraph`。
形式化陈述：degree_eq_zero_of_subsingleton (G' : Subgraph G) (v : V) [Fintype (G'.neig
hborSet v)] (hG : G'.verts.Subsingleton) : G'.degree v = 0
参数：G' : Subgraph G；v : V；G'.neighborSet v；hG : G'.verts.Subsingleton。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SimpleGraph.Subgraph.coe_degree`：coe_degree (G' : Subgraph G) (v : G'.ve
rts) [Fintype (G'.coe.neighborSet v)] [Fintype (G'.neighborSet v)] : G'.coe.degr
ee v = G'.degree v
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.subsingleton_coe`：subsingleton_coe (s : Set α) : Subsingleton s ↔ s.
Subsingleton
· 使用定理 `SimpleGraph.degree_eq_zero_of_subsingleton`：degree_eq_zero_of_subsinglet
on {G : SimpleGraph V} (v : V) [Fintype (G.neighborSet v)] [Subsingleton V] : G.
degree v = 0
· 使用定理 `SimpleGraph.Subgraph.degree_of_notMem_verts`：degree_of_notMem_verts {G' 
: Subgraph G} {v : V} [Fintype (G'.neighborSet v)] (h : v ∉ G'.verts) : G'.degre
e v = 0
-/
theorem degree_eq_zero_of_subsingleton (G' : Subgraph G) (v : V) [Fintype (G'.neighborSet v)]
    (hG : G'.verts.Subsingleton) : G'.degree v = 0 := by
  by_cases hv : v ∈ G'.verts
  · rw [← G'.coe_degree ⟨v, hv⟩]
    have := (Set.subsingleton_coe _).mpr hG
    exact G'.coe.degree_eq_zero_of_subsingleton ⟨v, hv⟩
  · exact degree_of_notMem_verts hv
/-
**SimpleGraph.Subgraph.degree_eq_one_iff_existsUnique_adj** 是 Mathlib 中的一个定理，位于命
名空间 `SimpleGraph.Subgraph`。
形式化陈述：degree_eq_one_iff_existsUnique_adj {G' : Subgraph G} {v : V} [Fintype (G'.
neighborSet v)] : G'.degree v = 1 ↔ exists! w : V, G'.Adj v w
参数：G'.neighborSet v。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SimpleGraph.Subgraph.finset_card_neighborSet_eq_degree`：finset_card_neig
hborSet_eq_degree {G' : Subgraph G} {v : V} [Fintype (G'.neighborSet v)] : (G'.n
eighborSet v).toFinset.card = G'.degree v
· 使用定理 `Finset.card_eq_one`：card_eq_one : #s = 1 ↔ exists a, s = {a}
· 使用定理 `Finset.singleton_iff_unique_mem`：singleton_iff_unique_mem (s : Finset α)
 : (exists a, s = {a}) ↔ exists! a, a in s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem degree_eq_one_iff_existsUnique_adj {G' : Subgraph G} {v : V} [Fintype (G'.neighborSet v)] :
    G'.degree v = 1 ↔ ∃! w : V, G'.Adj v w := by
  rw [← finset_card_neighborSet_eq_degree, Finset.card_eq_one, Finset.singleton_iff_unique_mem]
  simp only [Set.mem_toFinset, mem_neighborSet]
/-
**SimpleGraph.Subgraph.nontrivial_verts_of_degree_ne_zero** 是 Mathlib 中的一个定理，位于命
名空间 `SimpleGraph.Subgraph`。
形式化陈述：nontrivial_verts_of_degree_ne_zero {G' : Subgraph G} {v : V} [Fintype (G'.
neighborSet v)] (h : G'.degree v != 0) : Nontrivial G'.verts
参数：G'.neighborSet v；h : G'.degree v != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `SimpleGraph.Subgraph.degree_eq_zero_of_subsingleton`：degree_eq_zero_of_s
ubsingleton (G' : Subgraph G) (v : V) [Fintype (G'.neighborSet v)] (hG : G'.vert
s.Subsingleton) : G'.degree v = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
-/
theorem nontrivial_verts_of_degree_ne_zero {G' : Subgraph G} {v : V} [Fintype (G'.neighborSet v)]
    (h : G'.degree v ≠ 0) : Nontrivial G'.verts := by
  by_contra
  simp_all [G'.degree_eq_zero_of_subsingleton v]
/-
**SimpleGraph.Subgraph.neighborSet_eq_of_equiv** 是 Mathlib 中的一个引理，位于命名空间 `Simple
Graph.Subgraph`。
形式化陈述：neighborSet_eq_of_equiv {v : V} {H : Subgraph G} (h : G.neighborSet v ≃ H.
neighborSet v) (hfin : (G.neighborSet v).Finite) : H.neighborSet v = G.neighborS
et v
参数：h : G.neighborSet v ≃ H.neighborSet v；hfin : (G.neighborSet v).Finite。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `Set.instCanLiftFinsetCoeFinite`：∀ {α : Type u}, CanLift (Set α) (Finset 
α) SetLike.coe Set.Finite
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Equiv.set_finite_iff`：Equiv.set_finite_iff {s : Set α} {t : Set β} (hst 
: s ≃ t) : s.Finite ↔ t.Finite
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.eq_of_subset_of_card_le`：eq_of_subset_of_card_le (h : s subseteq 
t) (h₂ : #t <= #s) : s = t
· 使用定理 `Finset.coe_subset`：coe_subset {s₁ s₂ : Finset α} : (s₁ : Set α) subseteq
 s₂ ↔ s₁ subseteq s₂
· 使用定理 `SimpleGraph.Subgraph.neighborSet_subset`：neighborSet_subset (G' : Subgra
ph G) (v : V) : G'.neighborSet v subseteq G.neighborSet v
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Finset.card_eq_of_equiv`：Finset.card_eq_of_equiv {s : Finset α} {t : Fin
set β} (i : s ≃ t) : #s = #t
-/
lemma neighborSet_eq_of_equiv {v : V} {H : Subgraph G}
    (h : G.neighborSet v ≃ H.neighborSet v) (hfin : (G.neighborSet v).Finite) :
    H.neighborSet v = G.neighborSet v := by
  lift H.neighborSet v to Finset V using h.set_finite_iff.mp hfin with s hs
  lift G.neighborSet v to Finset V using hfin with t ht
  refine congrArg _ <| Finset.eq_of_subset_of_card_le ?_ (Finset.card_eq_of_equiv h).le
  rw [← Finset.coe_subset, hs, ht]
  exact H.neighborSet_subset _
/-
**SimpleGraph.Subgraph.adj_iff_of_neighborSet_equiv** 是 Mathlib 中的一个引理，位于命名空间 `S
impleGraph.Subgraph`。
形式化陈述：adj_iff_of_neighborSet_equiv {v : V} {H : Subgraph G} (h : G.neighborSet v
 ≃ H.neighborSet v) (hfin : (G.neighborSet v).Finite) : forall {w}, H.Adj v w ↔ 
G.Adj v w
参数：h : G.neighborSet v ≃ H.neighborSet v；hfin : (G.neighborSet v).Finite。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.ext_iff`：∀ {α : Type u} {a b : Set α}, a = b ↔ ∀ (x : α), x ∈ a ↔ x 
∈ b
· 使用引理 `SimpleGraph.Subgraph.neighborSet_eq_of_equiv`：neighborSet_eq_of_equiv {v
 : V} {H : Subgraph G} (h : G.neighborSet v ≃ H.neighborSet v) (hfin : (G.neighb
orSet v).Finite) : H.neighborSet v…
-/
lemma adj_iff_of_neighborSet_equiv {v : V} {H : Subgraph G}
    (h : G.neighborSet v ≃ H.neighborSet v) (hfin : (G.neighborSet v).Finite) :
    ∀ {w}, H.Adj v w ↔ G.Adj v w :=
  Set.ext_iff.mp (neighborSet_eq_of_equiv h hfin) _

end Subgraph

/-
**SimpleGraph.card_neighborSet_toSubgraph** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph
`。
形式化陈述：card_neighborSet_toSubgraph (G H : SimpleGraph V) (h : H <= G) (v : V) [Fi
ntype ↑((toSubgraph H h).neighborSet v)] [Fintype ↑(H.neighborSet v)] : Fintype.
card ↑((toSubgraph H h).neighborSet v) = H.degree v
参数：G H : SimpleGraph V；h : H <= G；v : V；(toSubgraph H h).neighborSet v；H.neighbo
rSet v。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.card_eq_of_equiv_fintype`：Finset.card_eq_of_equiv_fintype {s : Fi
nset α} [Fintype β] (i : s ≃ β) : #s = Fintype.card β
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
-/
theorem card_neighborSet_toSubgraph (G H : SimpleGraph V) (h : H ≤ G)
    (v : V) [Fintype ↑((toSubgraph H h).neighborSet v)] [Fintype ↑(H.neighborSet v)] :
    Fintype.card ↑((toSubgraph H h).neighborSet v) = H.degree v := by
  refine (Finset.card_eq_of_equiv_fintype ?_).symm
  simp only [mem_neighborFinset]
  rfl

@[simp]
/-
**SimpleGraph.degree_toSubgraph** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
形式化陈述：degree_toSubgraph (G H : SimpleGraph V) (h : H <= G) {v : V} [Fintype ↑((t
oSubgraph H h).neighborSet v)] [Fintype ↑(H.neighborSet v)] : (toSubgraph H h).d
egree v = H.degree v
参数：G H : SimpleGraph V；h : H <= G；(toSubgraph H h).neighborSet v；H.neighborSet v
。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.card_neighborSet_toSubgraph`：card_neighborSet_toSubgraph (G 
H : SimpleGraph V) (h : H <= G) (v : V) [Fintype ↑((toSubgraph H h).neighborSet 
v)] [Fintype ↑(H.neighborSet …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma degree_toSubgraph (G H : SimpleGraph V) (h : H ≤ G) {v : V}
    [Fintype ↑((toSubgraph H h).neighborSet v)] [Fintype ↑(H.neighborSet v)] :
    (toSubgraph H h).degree v = H.degree v := by
  simp [Subgraph.degree, card_neighborSet_toSubgraph]

section MkProperties

/-! ### Properties of `singletonSubgraph` and `subgraphOfAdj` -/


variable {G : SimpleGraph V} {G' : SimpleGraph W}

/-
**SimpleGraph.** 是 Mathlib 中的一个实例，位于命名空间 `SimpleGraph`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (v : V) : Unique (G.singletonSubgraph v).verts :=
  Set.uniqueSingleton _

@[simp]
/-
**SimpleGraph.singletonSubgraph_le_iff** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：singletonSubgraph_le_iff (v : V) (H : G.Subgraph) : G.singletonSubgraph v 
<= H ↔ v in H.verts
参数：v : V；H : G.Subgraph。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Set.mem_singleton`：mem_singleton (a : α) : a in ({a} : Set α)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.singletonSubgraph_verts`：∀ {V : Type u} (G : SimpleGraph V) 
(v : V), (G.singletonSubgraph v).verts = {v}
· 使用定理 `Set.singleton_subset_iff`：singleton_subset_iff {a : α} {s : Set α} : {a}
 subseteq s ↔ a in s
-/
theorem singletonSubgraph_le_iff (v : V) (H : G.Subgraph) :
    G.singletonSubgraph v ≤ H ↔ v ∈ H.verts := by
  refine ⟨fun h ↦ h.1 (Set.mem_singleton v), ?_⟩
  intro h
  constructor
  · rwa [singletonSubgraph_verts, Set.singleton_subset_iff]
  · exact fun _ _ ↦ False.elim

@[simp]
/-
**SimpleGraph.map_singletonSubgraph** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：map_singletonSubgraph (f : G ->g G') {v : V} : Subgraph.map f (G.singleton
Subgraph v) = G'.singletonSubgraph (f v)
参数：f : G ->g G'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Subgraph.ext`：∀ {V : Type u} {G : SimpleGraph V} {x y : G.Su
bgraph}, x.verts = y.verts → x.Adj = y.Adj → x = y
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `SimpleGraph.Subgraph.map_verts`：∀ {V : Type u} {W : Type v} {G : SimpleG
raph V} {G' : SimpleGraph W} (f : G →g G') (H : G.Subgraph),   (SimpleGraph.Subg
raph.map f H).verts …
· 使用定理 `SimpleGraph.singletonSubgraph_verts`：∀ {V : Type u} (G : SimpleGraph V) 
(v : V), (G.singletonSubgraph v).verts = {v}
· 使用定理 `Set.image_singleton`：image_singleton {f : α -> β} {a : α} : f '' {a} = {
f a}
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `SimpleGraph.Subgraph.map_adj`：∀ {V : Type u} {W : Type v} {G : SimpleGra
ph V} {G' : SimpleGraph W} (f : G →g G') (H : G.Subgraph) (a a_1 : W),   (Simple
Graph.Subgraph.map…
· 使用定理 `SimpleGraph.singletonSubgraph_adj`：∀ {V : Type u} (G : SimpleGraph V) (v
 a a_1 : V), (G.singletonSubgraph v).Adj a a_1 = ⊥ a a_1
-/
theorem map_singletonSubgraph (f : G →g G') {v : V} :
    Subgraph.map f (G.singletonSubgraph v) = G'.singletonSubgraph (f v) := by
  ext <;> simp only [Relation.Map, Subgraph.map_adj, singletonSubgraph_adj, Pi.bot_apply,
    exists_and_left, and_iff_left_iff_imp, Subgraph.map_verts,
    singletonSubgraph_verts, Set.image_singleton]
  exact False.elim

@[simp]
/-
**SimpleGraph.neighborSet_singletonSubgraph** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGra
ph`。
形式化陈述：neighborSet_singletonSubgraph (v w : V) : (G.singletonSubgraph v).neighbor
Set w = ∅
参数：v w : V。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem neighborSet_singletonSubgraph (v w : V) : (G.singletonSubgraph v).neighborSet w = ∅ :=
  rfl

@[simp]
/-
**SimpleGraph.edgeSet_singletonSubgraph** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：edgeSet_singletonSubgraph (v : V) : (G.singletonSubgraph v).edgeSet = ∅
参数：v : V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Sym2.fromRel_bot`：fromRel_bot : fromRel (α
-/
theorem edgeSet_singletonSubgraph (v : V) : (G.singletonSubgraph v).edgeSet = ∅ :=
  Sym2.fromRel_bot
/-
**SimpleGraph.eq_singletonSubgraph_iff_verts_eq** 是 Mathlib 中的一个定理，位于命名空间 `Simpl
eGraph`。
形式化陈述：eq_singletonSubgraph_iff_verts_eq (H : G.Subgraph) {v : V} : H = G.singlet
onSubgraph v ↔ H.verts = {v}
参数：H : G.Subgraph。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.singletonSubgraph_verts`：∀ {V : Type u} (G : SimpleGraph V) 
(v : V), (G.singletonSubgraph v).verts = {v}
· 使用定理 `SimpleGraph.Subgraph.ext`：∀ {V : Type u} {G : SimpleGraph V} {x y : G.Su
bgraph}, x.verts = y.verts → x.Adj = y.Adj → x = y
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `SimpleGraph.singletonSubgraph_adj`：∀ {V : Type u} (G : SimpleGraph V) (v
 a a_1 : V), (G.singletonSubgraph v).Adj a a_1 = ⊥ a a_1
· 使用定理 `iff_false`：∀ (p : Prop), (p ↔ False) = ¬p
· 使用定理 `SimpleGraph.Subgraph.Adj.fst_mem`：∀ {V : Type u} {G : SimpleGraph V} {H 
: G.Subgraph} {u v : V}, H.Adj u v → u ∈ H.verts
· 使用定理 `SimpleGraph.Subgraph.Adj.snd_mem`：∀ {V : Type u} {G : SimpleGraph V} {H 
: G.Subgraph} {u v : V}, H.Adj u v → v ∈ H.verts
· 使用定理 `SimpleGraph.Subgraph.Adj.ne`：∀ {V : Type u} {G : SimpleGraph V} {H : G.S
ubgraph} {u v : V}, H.Adj u v → u ≠ v
· 使用定理 `Set.mem_singleton_iff`：mem_singleton_iff {a b : α} : a in ({b} : Set α) 
↔ a = b
-/
theorem eq_singletonSubgraph_iff_verts_eq (H : G.Subgraph) {v : V} :
    H = G.singletonSubgraph v ↔ H.verts = {v} := by
  refine ⟨fun h ↦ by rw [h, singletonSubgraph_verts], fun h ↦ ?_⟩
  ext
  · rw [h, singletonSubgraph_verts]
  · simp only [Prop.bot_eq_false, singletonSubgraph_adj, Pi.bot_apply, iff_false]
    intro ha
    have ha1 := ha.fst_mem
    have ha2 := ha.snd_mem
    rw [h, Set.mem_singleton_iff] at ha1 ha2
    subst_vars
    exact ha.ne rfl
/-
**SimpleGraph.nonempty_subgraphOfAdj_verts** 是 Mathlib 中的一个实例，位于命名空间 `SimpleGrap
h`。
形式化陈述：nonempty_subgraphOfAdj_verts {v w : V} (hvw : G.Adj v w) : Nonempty (G.sub
graphOfAdj hvw).verts
参数：hvw : G.Adj v w。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.subgraphOfAdj_verts`：∀ {V : Type u} (G : SimpleGraph V) {v w
 : V} (hvw : G.Adj v w), (G.subgraphOfAdj hvw).verts = {v, w}
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
-/
instance nonempty_subgraphOfAdj_verts {v w : V} (hvw : G.Adj v w) :
    Nonempty (G.subgraphOfAdj hvw).verts :=
  ⟨⟨v, by simp⟩⟩
/-
**SimpleGraph.subgraphOfAdj_adj_self** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：subgraphOfAdj_adj_self {u v : V} (h : G.Adj u v) : (G.subgraphOfAdj h).Adj
 u v
参数：h : G.Adj u v。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem subgraphOfAdj_adj_self {u v : V} (h : G.Adj u v) : (G.subgraphOfAdj h).Adj u v :=
  rfl

@[simp]
/-
**SimpleGraph.edgeSet_subgraphOfAdj** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：edgeSet_subgraphOfAdj {v w : V} (hvw : G.Adj v w) : (G.subgraphOfAdj hvw).
edgeSet = {s(v, w)}
参数：hvw : G.Adj v w。
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
· 使用定理 `SimpleGraph.subgraphOfAdj_adj`：∀ {V : Type u} (G : SimpleGraph V) {v w :
 V} (hvw : G.Adj v w) (a b : V),   (G.subgraphOfAdj hvw).Adj a b = (s(v, w) = s(
a, b))
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem edgeSet_subgraphOfAdj {v w : V} (hvw : G.Adj v w) :
    (G.subgraphOfAdj hvw).edgeSet = {s(v, w)} := by
  ext e
  refine e.ind ?_
  simp only [eq_comm, Set.mem_singleton_iff, Subgraph.mem_edgeSet, subgraphOfAdj_adj,
    forall₂_true_iff]
/-
**SimpleGraph.subgraphOfAdj_le_of_adj** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
形式化陈述：subgraphOfAdj_le_of_adj {v w : V} (H : G.Subgraph) (h : H.Adj v w) : G.sub
graphOfAdj (H.adj_sub h) <= H
参数：H : G.Subgraph；h : H.Adj v w。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Subgraph.adj_sub`：∀ {V : Type u} {G : SimpleGraph V} (self :
 G.Subgraph) {v w : V}, self.Adj v w → G.Adj v w
-/
lemma subgraphOfAdj_le_of_adj {v w : V} (H : G.Subgraph) (h : H.Adj v w) :
    G.subgraphOfAdj (H.adj_sub h) ≤ H := by
  constructor
  · grind [subgraphOfAdj_verts, h.fst_mem, h.snd_mem]
  · grind [subgraphOfAdj_adj, h.symm]

@[simp]
/-
**SimpleGraph.subgraphOfAdj_le_iff** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：subgraphOfAdj_le_iff {u v : V} (h : G.Adj u v) (H : G.Subgraph) : G.subgra
phOfAdj h <= H ↔ H.Adj u v
参数：h : G.Adj u v；H : G.Subgraph。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `SimpleGraph.subgraphOfAdj_adj_self`：subgraphOfAdj_adj_self {u v : V} (h 
: G.Adj u v) : (G.subgraphOfAdj h).Adj u v
· 使用引理 `SimpleGraph.subgraphOfAdj_le_of_adj`：subgraphOfAdj_le_of_adj {v w : V} (
H : G.Subgraph) (h : H.Adj v w) : G.subgraphOfAdj (H.adj_sub h) <= H
-/
theorem subgraphOfAdj_le_iff {u v : V} (h : G.Adj u v) (H : G.Subgraph) :
    G.subgraphOfAdj h ≤ H ↔ H.Adj u v :=
  ⟨fun hle ↦ hle.right <| subgraphOfAdj_adj_self h, subgraphOfAdj_le_of_adj H⟩
/-
**SimpleGraph.subgraphOfAdj_symm** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：subgraphOfAdj_symm {v w : V} (hvw : G.Adj v w) : G.subgraphOfAdj hvw.symm 
= G.subgraphOfAdj hvw
参数：hvw : G.Adj v w。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Subgraph.ext`：∀ {V : Type u} {G : SimpleGraph V} {x y : G.Su
bgraph}, x.verts = y.verts → x.Adj = y.Adj → x = y
· 使用定理 `SimpleGraph.Adj.symm`：∀ {V : Type u} {G : SimpleGraph V} {u v : V}, G.Ad
j u v → G.Adj v u
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `SimpleGraph.subgraphOfAdj_verts`：∀ {V : Type u} (G : SimpleGraph V) {v w
 : V} (hvw : G.Adj v w), (G.subgraphOfAdj hvw).verts = {v, w}
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `SimpleGraph.subgraphOfAdj_adj`：∀ {V : Type u} (G : SimpleGraph V) {v w :
 V} (hvw : G.Adj v w) (a b : V),   (G.subgraphOfAdj hvw).Adj a b = (s(v, w) = s(
a, b))
· 使用定理 `Prod.mk.injEq`：∀ {α : Type u} {β : Type v} (fst : α) (snd : β) (fst_1 : 
α) (snd_1 : β),   ((fst, snd) = (fst_1, snd_1)) = (fst = fst_1 ∧ snd = snd_1)
-/
theorem subgraphOfAdj_symm {v w : V} (hvw : G.Adj v w) :
    G.subgraphOfAdj hvw.symm = G.subgraphOfAdj hvw := by
  ext <;> simp [or_comm, and_comm]

@[simp]
/-
**SimpleGraph.map_subgraphOfAdj** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：map_subgraphOfAdj (f : G ->g G') {v w : V} (hvw : G.Adj v w) : Subgraph.ma
p f (G.subgraphOfAdj hvw) = G'.subgraphOfAdj (f.map_adj hvw)
参数：f : G ->g G'；hvw : G.Adj v w。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Subgraph.ext`：∀ {V : Type u} {G : SimpleGraph V} {x y : G.Su
bgraph}, x.verts = y.verts → x.Adj = y.Adj → x = y
· 使用定理 `SimpleGraph.Hom.map_adj`：map_adj {v w : V} (h : G.Adj v w) : G'.Adj (f v
) (f w)
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem map_subgraphOfAdj (f : G →g G') {v w : V} (hvw : G.Adj v w) :
    Subgraph.map f (G.subgraphOfAdj hvw) = G'.subgraphOfAdj (f.map_adj hvw) := by
  ext <;> grind [Subgraph.map_verts, subgraphOfAdj_verts, Relation.Map, Subgraph.map_adj,
    subgraphOfAdj_adj]
/-
**SimpleGraph.neighborSet_subgraphOfAdj_subset** 是 Mathlib 中的一个定理，位于命名空间 `Simple
Graph`。
形式化陈述：neighborSet_subgraphOfAdj_subset {u v w : V} (hvw : G.Adj v w) : (G.subgra
phOfAdj hvw).neighborSet u subseteq {v, w}
参数：hvw : G.Adj v w。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Subgraph.neighborSet_subset_verts`：neighborSet_subset_verts 
(G' : Subgraph G) (v : V) : G'.neighborSet v subseteq G'.verts
-/
theorem neighborSet_subgraphOfAdj_subset {u v w : V} (hvw : G.Adj v w) :
    (G.subgraphOfAdj hvw).neighborSet u ⊆ {v, w} :=
  (G.subgraphOfAdj hvw).neighborSet_subset_verts _

@[simp]
/-
**SimpleGraph.neighborSet_fst_subgraphOfAdj** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGra
ph`。
形式化陈述：neighborSet_fst_subgraphOfAdj {v w : V} (hvw : G.Adj v w) : (G.subgraphOfA
dj hvw).neighborSet v = {w}
参数：hvw : G.Adj v w。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `SimpleGraph.subgraphOfAdj_adj`：∀ {V : Type u} (G : SimpleGraph V) {v w :
 V} (hvw : G.Adj v w) (a b : V),   (G.subgraphOfAdj hvw).Adj a b = (s(v, w) = s(
a, b))
· 使用定理 `Prod.mk.injEq`：∀ {α : Type u} {β : Type v} (fst : α) (snd : β) (fst_1 : 
α) (snd_1 : β),   ((fst, snd) = (fst_1, snd_1)) = (fst = fst_1 ∧ snd = snd_1)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `SimpleGraph.Adj.ne`：∀ {V : Type u} {G : SimpleGraph V} {a b : V}, G.Adj 
a b → a ≠ b
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
-/
theorem neighborSet_fst_subgraphOfAdj {v w : V} (hvw : G.Adj v w) :
    (G.subgraphOfAdj hvw).neighborSet v = {w} := by
  ext u
  suffices w = u ↔ u = w by simpa [hvw.ne.symm] using this
  rw [eq_comm]

@[simp]
/-
**SimpleGraph.neighborSet_snd_subgraphOfAdj** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGra
ph`。
形式化陈述：neighborSet_snd_subgraphOfAdj {v w : V} (hvw : G.Adj v w) : (G.subgraphOfA
dj hvw).neighborSet w = {v}
参数：hvw : G.Adj v w。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Adj.symm`：∀ {V : Type u} {G : SimpleGraph V} {u v : V}, G.Ad
j u v → G.Adj v u
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.subgraphOfAdj_symm`：subgraphOfAdj_symm {v w : V} (hvw : G.Ad
j v w) : G.subgraphOfAdj hvw.symm = G.subgraphOfAdj hvw
· 使用定理 `SimpleGraph.neighborSet_fst_subgraphOfAdj`：neighborSet_fst_subgraphOfAdj
 {v w : V} (hvw : G.Adj v w) : (G.subgraphOfAdj hvw).neighborSet v = {w}
-/
theorem neighborSet_snd_subgraphOfAdj {v w : V} (hvw : G.Adj v w) :
    (G.subgraphOfAdj hvw).neighborSet w = {v} := by
  rw [subgraphOfAdj_symm hvw.symm]
  exact neighborSet_fst_subgraphOfAdj hvw.symm

@[simp]
/-
**SimpleGraph.neighborSet_subgraphOfAdj_of_ne_of_ne** 是 Mathlib 中的一个定理，位于命名空间 `S
impleGraph`。
形式化陈述：neighborSet_subgraphOfAdj_of_ne_of_ne {u v w : V} (hvw : G.Adj v w) (hv : 
u != v) (hw : u != w) : (G.subgraphOfAdj hvw).neighborSet u = ∅
参数：hvw : G.Adj v w；hv : u != v；hw : u != w。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.subgraphOfAdj_adj`：∀ {V : Type u} (G : SimpleGraph V) {v w :
 V} (hvw : G.Adj v w) (a b : V),   (G.subgraphOfAdj hvw).Adj a b = (s(v, w) = s(
a, b))
· 使用定理 `Prod.mk.injEq`：∀ {α : Type u} {β : Type v} (fst : α) (snd : β) (fst_1 : 
α) (snd_1 : β),   ((fst, snd) = (fst_1, snd_1)) = (fst = fst_1 ∧ snd = snd_1)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem neighborSet_subgraphOfAdj_of_ne_of_ne {u v w : V} (hvw : G.Adj v w) (hv : u ≠ v)
    (hw : u ≠ w) : (G.subgraphOfAdj hvw).neighborSet u = ∅ := by
  ext
  simp [hv.symm, hw.symm]
/-
**SimpleGraph.neighborSet_subgraphOfAdj** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：neighborSet_subgraphOfAdj [DecidableEq V] {u v w : V} (hvw : G.Adj v w) : 
(G.subgraphOfAdj hvw).neighborSet u = (if u = v then {w} else ∅) union if u = w 
then {v} else ∅
参数：hvw : G.Adj v w。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `SimpleGraph.neighborSet_fst_subgraphOfAdj`：neighborSet_fst_subgraphOfAdj
 {v w : V} (hvw : G.Adj v w) : (G.subgraphOfAdj hvw).neighborSet v = {w}
· 使用定理 `Set.union_self`：union_self (a : Set α) : a union a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Set.union_empty`：union_empty (a : Set α) : a union ∅ = a
· 使用定理 `SimpleGraph.neighborSet_snd_subgraphOfAdj`：neighborSet_snd_subgraphOfAdj
 {v w : V} (hvw : G.Adj v w) : (G.subgraphOfAdj hvw).neighborSet w = {v}
· 使用定理 `Set.union_singleton`：union_singleton : s union {a} = insert a s
· 使用定理 `LawfulSingleton.insert_empty_eq`：∀ {α : Type u} {β : Type v} {inst : Emp
tyCollection β} {inst_1 : Insert α β} {inst_2 : Singleton α β}   [self : LawfulS
ingleton α β] (x : α)…
· 使用定理 `Set.instLawfulSingleton`：∀ {α : Type u_1}, LawfulSingleton α (Set α)
· 使用定理 `SimpleGraph.neighborSet_subgraphOfAdj_of_ne_of_ne`：neighborSet_subgraphO
fAdj_of_ne_of_ne {u v w : V} (hvw : G.Adj v w) (hv : u != v) (hw : u != w) : (G.
subgraphOfAdj hvw).neighborSet u = ∅
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem neighborSet_subgraphOfAdj [DecidableEq V] {u v w : V} (hvw : G.Adj v w) :
    (G.subgraphOfAdj hvw).neighborSet u =
    (if u = v then {w} else ∅) ∪ if u = w then {v} else ∅ := by
  split_ifs <;> subst_vars <;> simp [*]
/-
**SimpleGraph.singletonSubgraph_fst_le_subgraphOfAdj** 是 Mathlib 中的一个定理，位于命名空间 `
SimpleGraph`。
形式化陈述：singletonSubgraph_fst_le_subgraphOfAdj {u v : V} {h : G.Adj u v} : G.singl
etonSubgraph u <= G.subgraphOfAdj h
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.subgraphOfAdj_verts`：∀ {V : Type u} (G : SimpleGraph V) {v w
 : V} (hvw : G.Adj v w), (G.subgraphOfAdj hvw).verts = {v, w}
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
-/
theorem singletonSubgraph_fst_le_subgraphOfAdj {u v : V} {h : G.Adj u v} :
    G.singletonSubgraph u ≤ G.subgraphOfAdj h := by
  simp
/-
**SimpleGraph.singletonSubgraph_snd_le_subgraphOfAdj** 是 Mathlib 中的一个定理，位于命名空间 `
SimpleGraph`。
形式化陈述：singletonSubgraph_snd_le_subgraphOfAdj {u v : V} {h : G.Adj u v} : G.singl
etonSubgraph v <= G.subgraphOfAdj h
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.subgraphOfAdj_verts`：∀ {V : Type u} (G : SimpleGraph V) {v w
 : V} (hvw : G.Adj v w), (G.subgraphOfAdj hvw).verts = {v, w}
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
-/
theorem singletonSubgraph_snd_le_subgraphOfAdj {u v : V} {h : G.Adj u v} :
    G.singletonSubgraph v ≤ G.subgraphOfAdj h := by
  simp

@[simp]
/-
**SimpleGraph.support_subgraphOfAdj** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
形式化陈述：support_subgraphOfAdj {u v : V} (h : G.Adj u v) : (G.subgraphOfAdj h).supp
ort = {u, v}
参数：h : G.Adj u v。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.Subgraph.mem_support`：mem_support (H : Subgraph G) {v : V} :
 v in H.support ↔ exists w, H.Adj v w
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `SimpleGraph.subgraphOfAdj_adj`：∀ {V : Type u} (G : SimpleGraph V) {v w :
 V} (hvw : G.Adj v w) (a b : V),   (G.subgraphOfAdj hvw).Adj a b = (s(v, w) = s(
a, b))
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Prod.mk.injEq`：∀ {α : Type u} {β : Type v} (fst : α) (snd : β) (fst_1 : 
α) (snd_1 : β),   ((fst, snd) = (fst_1, snd_1)) = (fst = fst_1 ∧ snd = snd_1)
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
lemma support_subgraphOfAdj {u v : V} (h : G.Adj u v) :
    (G.subgraphOfAdj h).support = {u, v} := by
  ext
  rw [Subgraph.mem_support]
  simp only [subgraphOfAdj_adj, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk]
  refine ⟨?_, fun h ↦ h.elim (fun hl ↦ ⟨v, .inl ⟨hl.symm, rfl⟩⟩) fun hr ↦ ⟨u, .inr ⟨rfl, hr.symm⟩⟩⟩
  rintro ⟨_, hw⟩
  exact hw.elim (fun h1 ↦ .inl h1.1.symm) fun hr ↦ .inr hr.2.symm

end MkProperties

namespace Subgraph

variable {G : SimpleGraph V}

/-! ### Subgraphs of subgraphs -/


/-- Given a subgraph of a subgraph of `G`, construct a subgraph of `G`. -/
/-
**SimpleGraph.Subgraph.coeSubgraph** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph.Subgra
ph`。
形式化陈述：{V : Type u} → {G : SimpleGraph V} → {G' : G.Subgraph} → G'.coe.Subgraph →
 G.Subgraph
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a subgraph of a subgraph of `G`, construct a subgraph of `G`.
-/
protected abbrev coeSubgraph {G' : G.Subgraph} : G'.coe.Subgraph → G.Subgraph :=
  Subgraph.map G'.hom

/-- Given a subgraph of `G`, restrict it to being a subgraph of another subgraph `G'` by
taking the portion of `G` that intersects `G'`. -/
/-
**SimpleGraph.Subgraph.restrict** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph.Subgraph`
。
形式化陈述：{V : Type u} → {G : SimpleGraph V} → {G' : G.Subgraph} → G.Subgraph → G'.c
oe.Subgraph
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a subgraph of `G`, restrict it to being a subgraph of another subgraph `G'
` by
taking the portion of `G` that intersects `G'`.
-/
protected abbrev restrict {G' : G.Subgraph} : G.Subgraph → G'.coe.Subgraph :=
  Subgraph.comap G'.hom

@[simp]
/-
**SimpleGraph.Subgraph.verts_coeSubgraph** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph.
Subgraph`。
形式化陈述：verts_coeSubgraph {G' : Subgraph G} (G'' : Subgraph G'.coe) : (Subgraph.co
eSubgraph G'').verts = (G''.verts : Set V)
参数：G'' : Subgraph G'.coe。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma verts_coeSubgraph {G' : Subgraph G} (G'' : Subgraph G'.coe) :
    (Subgraph.coeSubgraph G'').verts = (G''.verts : Set V) := rfl
/-
**SimpleGraph.Subgraph.coeSubgraph_adj** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph.Su
bgraph`。
形式化陈述：coeSubgraph_adj {G' : G.Subgraph} (G'' : G'.coe.Subgraph) (v w : V) : (G'.
coeSubgraph G'').Adj v w ↔ exists (hv : v in G'.verts) (hw : w in G'.verts), G''
.Adj ⟨v, hv⟩ ⟨w, hw⟩
参数：G'' : G'.coe.Subgraph；v w : V。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.Subgraph.map_adj`：∀ {V : Type u} {W : Type v} {G : SimpleGra
ph V} {G' : SimpleGraph W} (f : G →g G') (H : G.Subgraph) (a a_1 : W),   (Simple
Graph.Subgraph.map…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `SimpleGraph.Subgraph.hom_apply`：∀ {V : Type u} {G : SimpleGraph V} (x : 
G.Subgraph) (v : ↑x.verts), x.hom v = ↑v
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma coeSubgraph_adj {G' : G.Subgraph} (G'' : G'.coe.Subgraph) (v w : V) :
    (G'.coeSubgraph G'').Adj v w ↔
      ∃ (hv : v ∈ G'.verts) (hw : w ∈ G'.verts), G''.Adj ⟨v, hv⟩ ⟨w, hw⟩ := by
  simp [Relation.Map]
/-
**SimpleGraph.Subgraph.restrict_adj** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph.Subgr
aph`。
形式化陈述：restrict_adj {G' G'' : G.Subgraph} (v w : G'.verts) : (G'.restrict G'').Ad
j v w ↔ G'.Adj v w ∧ G''.Adj v w
参数：v w : G'.verts。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma restrict_adj {G' G'' : G.Subgraph} (v w : G'.verts) :
    (G'.restrict G'').Adj v w ↔ G'.Adj v w ∧ G''.Adj v w := Iff.rfl
/-
**SimpleGraph.Subgraph.restrict_coeSubgraph** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGra
ph.Subgraph`。
形式化陈述：restrict_coeSubgraph {G' : G.Subgraph} (G'' : G'.coe.Subgraph) : Subgraph.
restrict (Subgraph.coeSubgraph G'') = G''
参数：G'' : G'.coe.Subgraph。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Subgraph.ext`：∀ {V : Type u} {G : SimpleGraph V} {x y : G.Su
bgraph}, x.verts = y.verts → x.Adj = y.Adj → x = y
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.Subgraph.comap_verts`：∀ {V : Type u} {W : Type v} {G : Simpl
eGraph V} {G' : SimpleGraph W} (f : G →g G') (H : G'.Subgraph),   (SimpleGraph.S
ubgraph.comap f H).ver…
· 使用定理 `SimpleGraph.Subgraph.map_verts`：∀ {V : Type u} {W : Type v} {G : SimpleG
raph V} {G' : SimpleGraph W} (f : G →g G') (H : G.Subgraph),   (SimpleGraph.Subg
raph.map f H).verts …
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `SimpleGraph.Subgraph.hom_apply`：∀ {V : Type u} {G : SimpleGraph V} (x : 
G.Subgraph) (v : ↑x.verts), x.hom v = ↑v
· 使用定理 `Set.preimage_image_eq`：preimage_image_eq {f : α -> β} (s : Set α) (h : I
njective f) : f ⁻¹' f '' s = s
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `SimpleGraph.Subgraph.restrict_adj`：restrict_adj {G' G'' : G.Subgraph} (v
 w : G'.verts) : (G'.restrict G'').Adj v w ↔ G'.Adj v w ∧ G''.Adj v w
· 使用引理 `SimpleGraph.Subgraph.coeSubgraph_adj`：coeSubgraph_adj {G' : G.Subgraph} 
(G'' : G'.coe.Subgraph) (v w : V) : (G'.coeSubgraph G'').Adj v w ↔ exists (hv : 
v in G'.verts) (hw : w in …
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Subtype.coe_eta`：coe_eta (a : { a // p a }) (h : p a) : mk (↑a) h = a
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `SimpleGraph.Subgraph.coe_adj`：∀ {V : Type u} {G : SimpleGraph V} (G' : G
.Subgraph) (v w : ↑G'.verts), G'.coe.Adj v w = G'.Adj ↑v ↑w
· 使用定理 `SimpleGraph.Subgraph.adj_sub`：∀ {V : Type u} {G : SimpleGraph V} (self :
 G.Subgraph) {v w : V}, self.Adj v w → G.Adj v w
-/
theorem restrict_coeSubgraph {G' : G.Subgraph} (G'' : G'.coe.Subgraph) :
    Subgraph.restrict (Subgraph.coeSubgraph G'') = G'' := by
  ext
  · simp
  · rw [restrict_adj, coeSubgraph_adj]
    simpa using G''.adj_sub
/-
**SimpleGraph.Subgraph.coeSubgraph_injective** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGr
aph.Subgraph`。
形式化陈述：coeSubgraph_injective (G' : G.Subgraph) : Function.Injective (Subgraph.coe
Subgraph : G'.coe.Subgraph -> G.Subgraph)
参数：G' : G.Subgraph。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.LeftInverse.injective`：∀ {α : Sort u_1} {β : Sort u_2} {g : β →
 α} {f : α → β}, Function.LeftInverse g f → Function.Injective f
· 使用定理 `SimpleGraph.Subgraph.restrict_coeSubgraph`：restrict_coeSubgraph {G' : G.
Subgraph} (G'' : G'.coe.Subgraph) : Subgraph.restrict (Subgraph.coeSubgraph G'')
 = G''
-/
theorem coeSubgraph_injective (G' : G.Subgraph) :
    Function.Injective (Subgraph.coeSubgraph : G'.coe.Subgraph → G.Subgraph) :=
  Function.LeftInverse.injective restrict_coeSubgraph
/-
**SimpleGraph.Subgraph.coeSubgraph_le** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph.Sub
graph`。
形式化陈述：coeSubgraph_le {H : G.Subgraph} (H' : H.coe.Subgraph) : Subgraph.coeSubgra
ph H' <= H
参数：H' : H.coe.Subgraph。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.Subgraph.map_verts`：∀ {V : Type u} {W : Type v} {G : SimpleG
raph V} {G' : SimpleGraph W} (f : G →g G') (H : G.Subgraph),   (SimpleGraph.Subg
raph.map f H).verts …
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `SimpleGraph.Subgraph.hom_apply`：∀ {V : Type u} {G : SimpleGraph V} (x : 
G.Subgraph) (v : ↑x.verts), x.hom v = ↑v
· 使用定理 `Subtype.coe_preimage_self`：coe_preimage_self (s : Set α) : ((↑) : s -> α
) ⁻¹' s = univ
· 使用定理 `SimpleGraph.Subgraph.adj_sub`：∀ {V : Type u} {G : SimpleGraph V} (self :
 G.Subgraph) {v w : V}, self.Adj v w → G.Adj v w
-/
lemma coeSubgraph_le {H : G.Subgraph} (H' : H.coe.Subgraph) :
    Subgraph.coeSubgraph H' ≤ H := by
  constructor
  · simp
  · rintro v w ⟨_, _, h, rfl, rfl⟩
    exact H'.adj_sub h
/-
**SimpleGraph.Subgraph.coeSubgraph_restrict_eq** 是 Mathlib 中的一个引理，位于命名空间 `Simple
Graph.Subgraph`。
形式化陈述：coeSubgraph_restrict_eq {H : G.Subgraph} (H' : G.Subgraph) : Subgraph.coeS
ubgraph (H.restrict H') = H ⊓ H'
参数：H' : G.Subgraph。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Subgraph.ext`：∀ {V : Type u} {G : SimpleGraph V} {x y : G.Su
bgraph}, x.verts = y.verts → x.Adj = y.Adj → x = y
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `SimpleGraph.Subgraph.map_verts`：∀ {V : Type u} {W : Type v} {G : SimpleG
raph V} {G' : SimpleGraph W} (f : G →g G') (H : G.Subgraph),   (SimpleGraph.Subg
raph.map f H).verts …
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `SimpleGraph.Subgraph.hom_apply`：∀ {V : Type u} {G : SimpleGraph V} (x : 
G.Subgraph) (v : ↑x.verts), x.hom v = ↑v
· 使用定理 `SimpleGraph.Subgraph.comap_verts`：∀ {V : Type u} {W : Type v} {G : Simpl
eGraph V} {G' : SimpleGraph W} (f : G →g G') (H : G'.Subgraph),   (SimpleGraph.S
ubgraph.comap f H).ver…
· 使用定理 `Subtype.image_preimage_coe`：image_preimage_coe (s t : Set α) : ((↑) : s 
-> α) '' ((↑) : s -> α) ⁻¹' t = s inter t
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `SimpleGraph.Subgraph.edge_vert`：∀ {V : Type u} {G : SimpleGraph V} (self
 : G.Subgraph) {v w : V}, self.Adj v w → v ∈ self.verts
· 使用定理 `SimpleGraph.Subgraph.Adj.symm`：∀ {V : Type u} {G : SimpleGraph V} {G' : 
G.Subgraph} {u v : V}, G'.Adj u v → G'.Adj v u
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
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


/-- Given a subgraph `G'` and a set of vertex pairs, remove all of the corresponding edges
from its edge set, if present.

See also: `SimpleGraph.deleteEdges`. -/
/-
**SimpleGraph.Subgraph.deleteEdges** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph.Subgra
ph`。
形式化陈述：deleteEdges (G' : G.Subgraph) (s : Set (Sym2 V)) : G.Subgraph where verts
参数：G' : G.Subgraph；s : Set (Sym2 V)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a subgraph `G'` and a set of vertex pairs, remove all of the corresponding
 edges
from its edge set, if present.

See also: `SimpleGraph.deleteEdges`.
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
/-
**SimpleGraph.Subgraph.deleteEdges_verts** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.
Subgraph`。
形式化陈述：deleteEdges_verts : (G'.deleteEdges s).verts = G'.verts
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem deleteEdges_verts : (G'.deleteEdges s).verts = G'.verts :=
  rfl

@[simp]
/-
**SimpleGraph.Subgraph.deleteEdges_adj** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Su
bgraph`。
形式化陈述：deleteEdges_adj (v w : V) : (G'.deleteEdges s).Adj v w ↔ G'.Adj v w ∧ s(v,
 w) ∉ s
参数：v w : V。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem deleteEdges_adj (v w : V) : (G'.deleteEdges s).Adj v w ↔ G'.Adj v w ∧ s(v, w) ∉ s :=
  Iff.rfl

@[simp]
/-
**SimpleGraph.Subgraph.deleteEdges_deleteEdges** 是 Mathlib 中的一个定理，位于命名空间 `Simple
Graph.Subgraph`。
形式化陈述：deleteEdges_deleteEdges (s s' : Set (Sym2 V)) : (G'.deleteEdges s).deleteE
dges s' = G'.deleteEdges (s union s')
参数：s s' : Set (Sym2 V)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Subgraph.ext`：∀ {V : Type u} {G : SimpleGraph V} {x y : G.Su
bgraph}, x.verts = y.verts → x.Adj = y.Adj → x = y
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
-/
theorem deleteEdges_deleteEdges (s s' : Set (Sym2 V)) :
    (G'.deleteEdges s).deleteEdges s' = G'.deleteEdges (s ∪ s') := by
  ext <;> simp [and_assoc, not_or]

@[simp]
/-
**SimpleGraph.Subgraph.deleteEdges_empty_eq** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGra
ph.Subgraph`。
形式化陈述：deleteEdges_empty_eq : G'.deleteEdges ∅ = G'
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Subgraph.ext`：∀ {V : Type u} {G : SimpleGraph V} {x y : G.Su
bgraph}, x.verts = y.verts → x.Adj = y.Adj → x = y
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
-/
theorem deleteEdges_empty_eq : G'.deleteEdges ∅ = G' := by
  ext <;> simp

@[simp]
/-
**SimpleGraph.Subgraph.deleteEdges_spanningCoe_eq** 是 Mathlib 中的一个定理，位于命名空间 `Sim
pleGraph.Subgraph`。
形式化陈述：deleteEdges_spanningCoe_eq : G'.spanningCoe.deleteEdges s = (G'.deleteEdge
s s).spanningCoe
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
· 使用定理 `SimpleGraph.Subgraph.spanningCoe_adj`：∀ {V : Type u} {G : SimpleGraph V}
 (G' : G.Subgraph) (a a_1 : V), G'.spanningCoe.Adj a a_1 = G'.Adj a a_1
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem deleteEdges_spanningCoe_eq :
    G'.spanningCoe.deleteEdges s = (G'.deleteEdges s).spanningCoe := by
  ext
  simp

set_option backward.isDefEq.respectTransparency false in
/-
**SimpleGraph.Subgraph.deleteEdges_coe_eq** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph
.Subgraph`。
形式化陈述：deleteEdges_coe_eq (s : Set (Sym2 G'.verts)) : G'.coe.deleteEdges s = (G'.
deleteEdges (Sym2.map (↑) '' s)).coe
参数：s : Set (Sym2 G'.verts)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.ext`：∀ {V : Type u} {x y : SimpleGraph V}, x.Adj = y.Adj → x
 = y
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `SimpleGraph.Subgraph.coe_adj`：∀ {V : Type u} {G : SimpleGraph V} (G' : G
.Subgraph) (v w : ↑G'.verts), G'.coe.Adj v w = G'.Adj ↑v ↑w
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Sym2.ind`：∀ {α : Type u_1} {f : Sym2 α → Prop}, (∀ (x y : α), f s(x, y))
 → ∀ (i : Sym2 α), f i
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₃`：contrapose₃ {p q : Prop} : (q -> 
¬ p) -> (p -> ¬ q)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Sym2.eq_swap`：eq_swap {a b : α} : s(a, b) = s(b, a)
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
/-
**SimpleGraph.Subgraph.coe_deleteEdges_eq** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph
.Subgraph`。
形式化陈述：coe_deleteEdges_eq (s : Set (Sym2 V)) : (G'.deleteEdges s).coe = G'.coe.de
leteEdges (Sym2.map (↑) ⁻¹' s)
参数：s : Set (Sym2 V)。
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
· 使用定理 `SimpleGraph.Subgraph.coe_adj`：∀ {V : Type u} {G : SimpleGraph V} (G' : G
.Subgraph) (v w : ↑G'.verts), G'.coe.Adj v w = G'.Adj ↑v ↑w
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem coe_deleteEdges_eq (s : Set (Sym2 V)) :
    (G'.deleteEdges s).coe = G'.coe.deleteEdges (Sym2.map (↑) ⁻¹' s) := by
  ext ⟨v, hv⟩ ⟨w, hw⟩
  simp
/-
**SimpleGraph.Subgraph.deleteEdges_le** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Sub
graph`。
形式化陈述：deleteEdges_le : G'.deleteEdges s <= G'
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem deleteEdges_le : G'.deleteEdges s ≤ G' := by
  constructor <;> simp +contextual
/-
**SimpleGraph.Subgraph.deleteEdges_le_of_le** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGra
ph.Subgraph`。
形式化陈述：deleteEdges_le_of_le {s s' : Set (Sym2 V)} (h : s subseteq s') : G'.delete
Edges s' <= G'.deleteEdges s
参数：Sym2 V；h : s subseteq s'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
-/
theorem deleteEdges_le_of_le {s s' : Set (Sym2 V)} (h : s ⊆ s') :
    G'.deleteEdges s' ≤ G'.deleteEdges s := by
  constructor <;> simp +contextual only [deleteEdges_verts, deleteEdges_adj,
    true_and, and_imp, subset_rfl]
  exact fun _ _ _ hs' hs ↦ hs' (h hs)

@[simp]
/-
**SimpleGraph.Subgraph.deleteEdges_inter_edgeSet_left_eq** 是 Mathlib 中的一个定理，位于命名
空间 `SimpleGraph.Subgraph`。
形式化陈述：deleteEdges_inter_edgeSet_left_eq : G'.deleteEdges (G'.edgeSet inter s) = 
G'.deleteEdges s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Subgraph.ext`：∀ {V : Type u} {G : SimpleGraph V} {x y : G.Su
bgraph}, x.verts = y.verts → x.Adj = y.Adj → x = y
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem deleteEdges_inter_edgeSet_left_eq :
    G'.deleteEdges (G'.edgeSet ∩ s) = G'.deleteEdges s := by
  ext <;> simp +contextual

@[simp]
/-
**SimpleGraph.Subgraph.deleteEdges_inter_edgeSet_right_eq** 是 Mathlib 中的一个定理，位于命
名空间 `SimpleGraph.Subgraph`。
形式化陈述：deleteEdges_inter_edgeSet_right_eq : G'.deleteEdges (s inter G'.edgeSet) =
 G'.deleteEdges s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Subgraph.ext`：∀ {V : Type u} {G : SimpleGraph V} {x y : G.Su
bgraph}, x.verts = y.verts → x.Adj = y.Adj → x = y
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem deleteEdges_inter_edgeSet_right_eq :
    G'.deleteEdges (s ∩ G'.edgeSet) = G'.deleteEdges s := by
  ext <;> simp +contextual [imp_false]

set_option backward.isDefEq.respectTransparency false in
/-
**SimpleGraph.Subgraph.coe_deleteEdges_le** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph
.Subgraph`。
形式化陈述：coe_deleteEdges_le : (G'.deleteEdges s).coe <= (G'.coe : SimpleGraph G'.ve
rts)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `SimpleGraph.Subgraph.coe_adj`：∀ {V : Type u} {G : SimpleGraph V} (G' : G
.Subgraph) (v w : ↑G'.verts), G'.coe.Adj v w = G'.Adj ↑v ↑w
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem coe_deleteEdges_le : (G'.deleteEdges s).coe ≤ (G'.coe : SimpleGraph G'.verts) := by
  intro v w
  simp +contextual
/-
**SimpleGraph.Subgraph.spanningCoe_deleteEdges_le** 是 Mathlib 中的一个定理，位于命名空间 `Sim
pleGraph.Subgraph`。
形式化陈述：spanningCoe_deleteEdges_le (G' : G.Subgraph) (s : Set (Sym2 V)) : (G'.dele
teEdges s).spanningCoe <= G'.spanningCoe
参数：G' : G.Subgraph；s : Set (Sym2 V)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Subgraph.spanningCoe_le_of_le`：spanningCoe_le_of_le {H H' : 
Subgraph G} (h : H <= H') : H.spanningCoe <= H'.spanningCoe
· 使用定理 `SimpleGraph.Subgraph.deleteEdges_le`：deleteEdges_le : G'.deleteEdges s <
= G'
-/
theorem spanningCoe_deleteEdges_le (G' : G.Subgraph) (s : Set (Sym2 V)) :
    (G'.deleteEdges s).spanningCoe ≤ G'.spanningCoe :=
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
/-
**SimpleGraph.Subgraph.induce** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph.Subgraph`。
形式化陈述：induce (G' : G.Subgraph) (s : Set V) : G.Subgraph where verts
参数：G' : G.Subgraph；s : Set V。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The induced subgraph of a subgraph. The expectation is that `s ⊆ G'.verts` for t
he usual
notion of an induced subgraph, but, in general, `s` is taken to be the new verte
x set and edges
are induced from the subgraph `G'`.
-/
def induce (G' : G.Subgraph) (s : Set V) : G.Subgraph where
  verts := s
  Adj u v := u ∈ s ∧ v ∈ s ∧ G'.Adj u v
  adj_sub h := G'.adj_sub h.2.2
  edge_vert h := h.1
  symm.symm _ _ h := ⟨h.2.1, h.1, h.2.2.symm⟩

set_option backward.isDefEq.respectTransparency false in
/-
**SimpleGraph.Subgraph._root_.SimpleGraph.induce_eq_coe_induce_top** 是 Mathlib 中
的一个定理，位于命名空间 `SimpleGraph.Subgraph`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.SimpleGraph.induce_eq_coe_induce_top (s : Set V) :
    G.induce s = ((⊤ : G.Subgraph).induce s).coe := by
  ext
  simp
/-
**SimpleGraph.Subgraph._root_.SimpleGraph.spanningCoe_induce_top** 是 Mathlib 中的一
个引理，位于命名空间 `SimpleGraph.Subgraph`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
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
/-
**SimpleGraph.Subgraph.IsInduced.induce_top_verts** 是 Mathlib 中的一个定理，位于命名空间 `Sim
pleGraph.Subgraph.IsInduced`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} {G' : G.Subgraph}, G'.IsInduced → ⊤.ind
uce G'.verts = G'
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Subgraph.ext`：∀ {V : Type u} {G : SimpleGraph V} {x y : G.Su
bgraph}, x.verts = y.verts → x.Adj = y.Adj → x = y
· 使用定理 `funext₂`：∀ {α : Sort u_1} {β : α → Sort u_2} {γ : (a : α) → β a → Sort u
_3} {f g : (a : α) → (b : β a) → γ a b},   (∀ (a : α) (b : β a), f a b = g a …
· 使用定理 `SimpleGraph.Subgraph.edge_vert`：∀ {V : Type u} {G : SimpleGraph V} (self
 : G.Subgraph) {v w : V}, self.Adj v w → v ∈ self.verts
· 使用定理 `SimpleGraph.Subgraph.Adj.symm`：∀ {V : Type u} {G : SimpleGraph V} {G' : 
G.Subgraph} {u v : V}, G'.Adj u v → G'.Adj v u
· 使用定理 `SimpleGraph.Subgraph.Adj.adj_sub`：∀ {V : Type u} {G : SimpleGraph V} {H 
: G.Subgraph} {u v : V}, H.Adj u v → G.Adj u v
-/
theorem IsInduced.induce_top_verts (h : G'.IsInduced) : induce ⊤ G'.verts = G' :=
  Subgraph.ext rfl <| funext₂ fun _ _ ↦ propext
    ⟨fun ⟨hu, hv, h'⟩ ↦ h hu hv h', fun h ↦ ⟨G'.edge_vert h, G'.edge_vert h.symm, h.adj_sub⟩⟩
/-
**SimpleGraph.Subgraph.isInduced_iff_exists_eq_induce_top** 是 Mathlib 中的一个定理，位于命
名空间 `SimpleGraph.Subgraph`。
形式化陈述：isInduced_iff_exists_eq_induce_top (G' : G.Subgraph) : G'.IsInduced ↔ exis
ts s, G' = induce ⊤ s
参数：G' : G.Subgraph。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SimpleGraph.Subgraph.IsInduced.induce_top_verts`：∀ {V : Type u} {G : Sim
pleGraph V} {G' : G.Subgraph}, G'.IsInduced → ⊤.induce G'.verts = G'
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem isInduced_iff_exists_eq_induce_top (G' : G.Subgraph) :
    G'.IsInduced ↔ ∃ s, G' = induce ⊤ s := by
  refine ⟨fun h ↦ ⟨G'.verts, h.induce_top_verts.symm⟩, fun ⟨s, h⟩ _ hu _ hv hadj ↦ ?_⟩
  rw [h, (h ▸ rfl : s = G'.verts)]
  exact ⟨hu, hv, hadj⟩

@[gcongr]
/-
**SimpleGraph.Subgraph.induce_mono** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Subgra
ph`。
形式化陈述：induce_mono (hg : G' <= G'') (hs : s subseteq s') : G'.induce s <= G''.ind
uce s'
参数：hg : G' <= G''；hs : s subseteq s'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.Subgraph.induce_verts`：∀ {V : Type u} {G : SimpleGraph V} (G
' : G.Subgraph) (s : Set V), (G'.induce s).verts = s
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `SimpleGraph.Subgraph.induce_adj`：∀ {V : Type u} {G : SimpleGraph V} (G' 
: G.Subgraph) (s : Set V) (u v : V),   (G'.induce s).Adj u v = (u ∈ s ∧ v ∈ s ∧ 
G'.Adj u v)
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem induce_mono (hg : G' ≤ G'') (hs : s ⊆ s') : G'.induce s ≤ G''.induce s' := by
  constructor
  · simp [hs]
  · simp +contextual only [induce_adj, and_imp]
    intro v w hv hw ha
    exact ⟨hs hv, hs hw, hg.2 ha⟩

@[gcongr, mono]
/-
**SimpleGraph.Subgraph.induce_mono_left** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.S
ubgraph`。
形式化陈述：induce_mono_left (hg : G' <= G'') : G'.induce s <= G''.induce s
参数：hg : G' <= G''。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Subgraph.induce_mono`：induce_mono (hg : G' <= G'') (hs : s s
ubseteq s') : G'.induce s <= G''.induce s'
· 使用定理 `subset_rfl`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preorde
r α] {a : α}, a ⊆ a
-/
theorem induce_mono_left (hg : G' ≤ G'') : G'.induce s ≤ G''.induce s :=
  induce_mono hg subset_rfl

@[gcongr, mono]
/-
**SimpleGraph.Subgraph.induce_mono_right** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.
Subgraph`。
形式化陈述：induce_mono_right (hs : s subseteq s') : G'.induce s <= G'.induce s'
参数：hs : s subseteq s'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Subgraph.induce_mono`：induce_mono (hg : G' <= G'') (hs : s s
ubseteq s') : G'.induce s <= G''.induce s'
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem induce_mono_right (hs : s ⊆ s') : G'.induce s ≤ G'.induce s' :=
  induce_mono le_rfl hs

@[simp]
/-
**SimpleGraph.Subgraph.induce_empty** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Subgr
aph`。
形式化陈述：induce_empty : G'.induce ∅ = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Subgraph.ext`：∀ {V : Type u} {G : SimpleGraph V} {x y : G.Su
bgraph}, x.verts = y.verts → x.Adj = y.Adj → x = y
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `SimpleGraph.Subgraph.induce_verts`：∀ {V : Type u} {G : SimpleGraph V} (G
' : G.Subgraph) (s : Set V), (G'.induce s).verts = s
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `SimpleGraph.Subgraph.induce_adj`：∀ {V : Type u} {G : SimpleGraph V} (G' 
: G.Subgraph) (s : Set V) (u v : V),   (G'.induce s).Adj u v = (u ∈ s ∧ v ∈ s ∧ 
G'.Adj u v)
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
theorem induce_empty : G'.induce ∅ = ⊥ := by
  ext <;> simp

@[simp]
/-
**SimpleGraph.Subgraph.induce_self_verts** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.
Subgraph`。
形式化陈述：induce_self_verts : G'.induce G'.verts = G'
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Subgraph.ext`：∀ {V : Type u} {G : SimpleGraph V} {x y : G.Su
bgraph}, x.verts = y.verts → x.Adj = y.Adj → x = y
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.Subgraph.induce_verts`：∀ {V : Type u} {G : SimpleGraph V} (G
' : G.Subgraph) (s : Set V), (G'.induce s).verts = s
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `SimpleGraph.Subgraph.induce_adj`：∀ {V : Type u} {G : SimpleGraph V} (G' 
: G.Subgraph) (s : Set V) (u v : V),   (G'.induce s).Adj u v = (u ∈ s ∧ v ∈ s ∧ 
G'.Adj u v)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `SimpleGraph.Subgraph.edge_vert`：∀ {V : Type u} {G : SimpleGraph V} (self
 : G.Subgraph) {v w : V}, self.Adj v w → v ∈ self.verts
· 使用定理 `SimpleGraph.Subgraph.Adj.symm`：∀ {V : Type u} {G : SimpleGraph V} {G' : 
G.Subgraph} {u v : V}, G'.Adj u v → G'.Adj v u
-/
theorem induce_self_verts : G'.induce G'.verts = G' := by
  ext
  · simp
  · constructor <;>
      simp +contextual only [induce_adj, imp_true_iff, and_true]
    exact fun ha ↦ ⟨G'.edge_vert ha, G'.edge_vert ha.symm⟩
/-
**SimpleGraph.Subgraph.le_induce_top_verts** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGrap
h.Subgraph`。
形式化陈述：le_induce_top_verts : G' <= (⊤ : G.Subgraph).induce G'.verts
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SimpleGraph.Subgraph.induce_self_verts`：induce_self_verts : G'.induce G'
.verts = G'
· 使用定理 `SimpleGraph.Subgraph.induce_mono_left`：induce_mono_left (hg : G' <= G'')
 : G'.induce s <= G''.induce s
· 使用定理 `le_top`：le_top : a <= ⊤
-/
lemma le_induce_top_verts : G' ≤ (⊤ : G.Subgraph).induce G'.verts :=
  calc G' = G'.induce G'.verts := Subgraph.induce_self_verts.symm
       _ ≤ (⊤ : G.Subgraph).induce G'.verts := Subgraph.induce_mono_left le_top
/-
**SimpleGraph.Subgraph.le_induce_union** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph.Su
bgraph`。
形式化陈述：le_induce_union : G'.induce s ⊔ G'.induce s' <= G'.induce (s union s')
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.Subgraph.induce_verts`：∀ {V : Type u} {G : SimpleGraph V} (G
' : G.Subgraph) (s : Set V), (G'.induce s).verts = s
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `SimpleGraph.Subgraph.induce_adj`：∀ {V : Type u} {G : SimpleGraph V} (G' 
: G.Subgraph) (s : Set V) (u v : V),   (G'.induce s).Adj u v = (u ∈ s ∧ v ∈ s ∧ 
G'.Adj u v)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
-/
lemma le_induce_union : G'.induce s ⊔ G'.induce s' ≤ G'.induce (s ∪ s') := by
  constructor
  · simp
  · simp only [sup_adj, induce_adj, Set.mem_union]
    rintro v w (h | h) <;> simp [h]
/-
**SimpleGraph.Subgraph.le_induce_union_left** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGra
ph.Subgraph`。
形式化陈述：le_induce_union_left : G'.induce s <= G'.induce (s union s')
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `sup_le_iff`：sup_le_iff : a ⊔ b <= c ↔ a <= c ∧ b <= c
· 使用引理 `SimpleGraph.Subgraph.le_induce_union`：le_induce_union : G'.induce s ⊔ G'
.induce s' <= G'.induce (s union s')
-/
lemma le_induce_union_left : G'.induce s ≤ G'.induce (s ∪ s') := by
  exact (sup_le_iff.mp le_induce_union).1
/-
**SimpleGraph.Subgraph.le_induce_union_right** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGr
aph.Subgraph`。
形式化陈述：le_induce_union_right : G'.induce s' <= G'.induce (s union s')
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `sup_le_iff`：sup_le_iff : a ⊔ b <= c ↔ a <= c ∧ b <= c
· 使用引理 `SimpleGraph.Subgraph.le_induce_union`：le_induce_union : G'.induce s ⊔ G'
.induce s' <= G'.induce (s union s')
-/
lemma le_induce_union_right : G'.induce s' ≤ G'.induce (s ∪ s') := by
  exact (sup_le_iff.mp le_induce_union).2
/-
**SimpleGraph.Subgraph.singletonSubgraph_eq_induce** 是 Mathlib 中的一个定理，位于命名空间 `Si
mpleGraph.Subgraph`。
形式化陈述：singletonSubgraph_eq_induce {v : V} : G.singletonSubgraph v = (⊤ : G.Subgr
aph).induce {v}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Subgraph.ext`：∀ {V : Type u} {G : SimpleGraph V} {x y : G.Su
bgraph}, x.verts = y.verts → x.Adj = y.Adj → x = y
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `SimpleGraph.singletonSubgraph_verts`：∀ {V : Type u} (G : SimpleGraph V) 
(v : V), (G.singletonSubgraph v).verts = {v}
· 使用定理 `SimpleGraph.Subgraph.induce_verts`：∀ {V : Type u} {G : SimpleGraph V} (G
' : G.Subgraph) (s : Set V), (G'.induce s).verts = s
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `SimpleGraph.singletonSubgraph_adj`：∀ {V : Type u} (G : SimpleGraph V) (v
 a a_1 : V), (G.singletonSubgraph v).Adj a a_1 = ⊥ a a_1
· 使用定理 `SimpleGraph.Subgraph.induce_adj`：∀ {V : Type u} {G : SimpleGraph V} (G' 
: G.Subgraph) (s : Set V) (u v : V),   (G'.induce s).Adj u v = (u ∈ s ∧ v ∈ s ∧ 
G'.Adj u v)
· 使用定理 `false_iff`：∀ (p : Prop), (False ↔ p) = ¬p
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem singletonSubgraph_eq_induce {v : V} :
    G.singletonSubgraph v = (⊤ : G.Subgraph).induce {v} := by
  ext <;> simp +contextual [-Set.bot_eq_empty, Prop.bot_eq_false]
/-
**SimpleGraph.Subgraph.subgraphOfAdj_eq_induce** 是 Mathlib 中的一个定理，位于命名空间 `Simple
Graph.Subgraph`。
形式化陈述：subgraphOfAdj_eq_induce {v w : V} (hvw : G.Adj v w) : G.subgraphOfAdj hvw 
= (⊤ : G.Subgraph).induce {v, w}
参数：hvw : G.Adj v w。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Subgraph.ext`：∀ {V : Type u} {G : SimpleGraph V} {x y : G.Su
bgraph}, x.verts = y.verts → x.Adj = y.Adj → x = y
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `SimpleGraph.subgraphOfAdj_verts`：∀ {V : Type u} (G : SimpleGraph V) {v w
 : V} (hvw : G.Adj v w), (G.subgraphOfAdj hvw).verts = {v, w}
· 使用定理 `SimpleGraph.Subgraph.induce_verts`：∀ {V : Type u} {G : SimpleGraph V} (G
' : G.Subgraph) (s : Set V), (G'.induce s).verts = s
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `SimpleGraph.subgraphOfAdj_adj`：∀ {V : Type u} (G : SimpleGraph V) {v w :
 V} (hvw : G.Adj v w) (a b : V),   (G.subgraphOfAdj hvw).Adj a b = (s(v, w) = s(
a, b))
· 使用定理 `SimpleGraph.Subgraph.induce_adj`：∀ {V : Type u} {G : SimpleGraph V} (G' 
: G.Subgraph) (s : Set V) (u v : V),   (G'.induce s).Adj u v = (u ∈ s ∧ v ∈ s ∧ 
G'.Adj u v)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `SimpleGraph.Adj.symm`：∀ {V : Type u} {G : SimpleGraph V} {u v : V}, G.Ad
j u v → G.Adj v u
· 使用定理 `SimpleGraph.Adj.ne`：∀ {V : Type u} {G : SimpleGraph V} {a b : V}, G.Adj 
a b → a ≠ b
· 使用定理 `Prod.mk.injEq`：∀ {α : Type u} {β : Type v} (fst : α) (snd : β) (fst_1 : 
α) (snd_1 : β),   ((fst, snd) = (fst_1, snd_1)) = (fst = fst_1 ∧ snd = snd_1)
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
/-
**SimpleGraph.Subgraph.instDecidableRel_induce_adj** 是 Mathlib 中的一个实例，位于命名空间 `Si
mpleGraph.Subgraph`。
形式化陈述：instDecidableRel_induce_adj (s : Set V) [forall a, Decidable (a in s)] [De
cidableRel G'.Adj] : DecidableRel (G'.induce s).Adj
参数：s : Set V；a in s。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instDecidableRel_induce_adj (s : Set V) [∀ a, Decidable (a ∈ s)] [DecidableRel G'.Adj] :
    DecidableRel (G'.induce s).Adj :=
  fun _ _ ↦ instDecidableAnd

set_option backward.isDefEq.respectTransparency false in
/-- Equivalence between an induced subgraph and its corresponding simple graph. -/
/-
**SimpleGraph.Subgraph.coeInduceIso** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph.Subgr
aph`。
形式化陈述：coeInduceIso (s : Set V) (h : s subseteq G'.verts) : (G'.induce s).coe ≃g 
G'.coe.induce {v : G'.verts | ↑v in s} where toFun
参数：s : Set V；h : s subseteq G'.verts。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Equivalence between an induced subgraph and its corresponding simple graph.
-/
def coeInduceIso (s : Set V) (h : s ⊆ G'.verts) :
    (G'.induce s).coe ≃g G'.coe.induce {v : G'.verts | ↑v ∈ s} where
  toFun := fun ⟨v, hv⟩ ↦ ⟨⟨v, h hv⟩, by simp at hv; aesop⟩
  invFun := fun ⟨v, hv⟩ ↦ ⟨v, hv⟩
  map_rel_iff' := by simp

end Induce

/-- Given a subgraph and a set of vertices, delete all the vertices from the subgraph,
if present. Any edges incident to the deleted vertices are deleted as well. -/
/-
**SimpleGraph.Subgraph.deleteVerts** 是 Mathlib 中的一个缩写定义，位于命名空间 `SimpleGraph.Subg
raph`。
形式化陈述：deleteVerts (G' : G.Subgraph) (s : Set V) : G.Subgraph
参数：G' : G.Subgraph；s : Set V。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a subgraph and a set of vertices, delete all the vertices from the subgrap
h,
if present. Any edges incident to the deleted vertices are deleted as well.
-/
abbrev deleteVerts (G' : G.Subgraph) (s : Set V) : G.Subgraph :=
  G'.induce (G'.verts \ s)

section DeleteVerts

variable {G' : G.Subgraph} {s : Set V}

/-
**SimpleGraph.Subgraph.deleteVerts_verts** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.
Subgraph`。
形式化陈述：deleteVerts_verts : (G'.deleteVerts s).verts = G'.verts \ s
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem deleteVerts_verts : (G'.deleteVerts s).verts = G'.verts \ s :=
  rfl
/-
**SimpleGraph.Subgraph.deleteVerts_adj** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Su
bgraph`。
形式化陈述：deleteVerts_adj {u v : V} : (G'.deleteVerts s).Adj u v ↔ u in G'.verts ∧ u
 ∉ s ∧ v in G'.verts ∧ v ∉ s ∧ G'.Adj u v
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.Subgraph.induce_adj`：∀ {V : Type u} {G : SimpleGraph V} (G' 
: G.Subgraph) (s : Set V) (u v : V),   (G'.induce s).Adj u v = (u ∈ s ∧ v ∈ s ∧ 
G'.Adj u v)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem deleteVerts_adj {u v : V} :
    (G'.deleteVerts s).Adj u v ↔ u ∈ G'.verts ∧ u ∉ s ∧ v ∈ G'.verts ∧ v ∉ s ∧ G'.Adj u v := by
  simp [and_assoc]

@[simp]
/-
**SimpleGraph.Subgraph.deleteVerts_deleteVerts** 是 Mathlib 中的一个定理，位于命名空间 `Simple
Graph.Subgraph`。
形式化陈述：deleteVerts_deleteVerts (s s' : Set V) : (G'.deleteVerts s).deleteVerts s'
 = G'.deleteVerts (s union s')
参数：s s' : Set V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Subgraph.ext`：∀ {V : Type u} {G : SimpleGraph V} {x y : G.Su
bgraph}, x.verts = y.verts → x.Adj = y.Adj → x = y
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `SimpleGraph.Subgraph.induce_verts`：∀ {V : Type u} {G : SimpleGraph V} (G
' : G.Subgraph) (s : Set V), (G'.induce s).verts = s
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `SimpleGraph.Subgraph.induce_adj`：∀ {V : Type u} {G : SimpleGraph V} (G' 
: G.Subgraph) (s : Set V) (u v : V),   (G'.induce s).Adj u v = (u ∈ s ∧ v ∈ s ∧ 
G'.Adj u v)
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem deleteVerts_deleteVerts (s s' : Set V) :
    (G'.deleteVerts s).deleteVerts s' = G'.deleteVerts (s ∪ s') := by
  ext <;> simp +contextual [not_or, and_assoc]

@[simp]
/-
**SimpleGraph.Subgraph.deleteVerts_empty** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.
Subgraph`。
形式化陈述：deleteVerts_empty : G'.deleteVerts ∅ = G'
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.sdiff_empty`：sdiff_empty {s : Set α} : s \ ∅ = s
· 使用定理 `SimpleGraph.Subgraph.induce_self_verts`：induce_self_verts : G'.induce G'
.verts = G'
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem deleteVerts_empty : G'.deleteVerts ∅ = G' := by
  simp [deleteVerts]
/-
**SimpleGraph.Subgraph.deleteVerts_le** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Sub
graph`。
形式化陈述：deleteVerts_le : G'.deleteVerts s <= G'
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.Subgraph.induce_verts`：∀ {V : Type u} {G : SimpleGraph V} (G
' : G.Subgraph) (s : Set V), (G'.induce s).verts = s
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `SimpleGraph.Subgraph.induce_adj`：∀ {V : Type u} {G : SimpleGraph V} (G' 
: G.Subgraph) (s : Set V) (u v : V),   (G'.induce s).Adj u v = (u ∈ s ∧ v ∈ s ∧ 
G'.Adj u v)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem deleteVerts_le : G'.deleteVerts s ≤ G' := by
  constructor <;> simp

@[gcongr, mono]
/-
**SimpleGraph.Subgraph.deleteVerts_mono** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.S
ubgraph`。
形式化陈述：deleteVerts_mono {G' G'' : G.Subgraph} (h : G' <= G'') : G'.deleteVerts s 
<= G''.deleteVerts s
参数：h : G' <= G''。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Subgraph.induce_mono`：induce_mono (hg : G' <= G'') (hs : s s
ubseteq s') : G'.induce s <= G''.induce s'
· 使用定理 `Set.sdiff_subset_sdiff_left`：sdiff_subset_sdiff_left {s₁ s₂ t : Set α} (
h : s₁ subseteq s₂) : s₁ \ t subseteq s₂ \ t
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem deleteVerts_mono {G' G'' : G.Subgraph} (h : G' ≤ G'') :
    G'.deleteVerts s ≤ G''.deleteVerts s :=
  induce_mono h (Set.sdiff_subset_sdiff_left h.1)

set_option backward.isDefEq.respectTransparency false in
@[mono]
/-
**SimpleGraph.Subgraph.deleteVerts_mono'** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph.
Subgraph`。
形式化陈述：deleteVerts_mono' {G' : SimpleGraph V} (u : Set V) (h : G <= G') : ((⊤ : S
ubgraph G).deleteVerts u).coe <= ((⊤ : Subgraph G').deleteVerts u).coe
参数：u : Set V；h : G <= G'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `SimpleGraph.Subgraph.coe_adj`：∀ {V : Type u} {G : SimpleGraph V} (G' : G
.Subgraph) (v w : ↑G'.verts), G'.coe.Adj v w = G'.Adj ↑v ↑w
· 使用定理 `SimpleGraph.Subgraph.induce_adj`：∀ {V : Type u} {G : SimpleGraph V} (G' 
: G.Subgraph) (s : Set V) (u v : V),   (G'.induce s).Adj u v = (u ∈ s ∧ v ∈ s ∧ 
G'.Adj u v)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
-/
lemma deleteVerts_mono' {G' : SimpleGraph V} (u : Set V) (h : G ≤ G') :
    ((⊤ : Subgraph G).deleteVerts u).coe ≤ ((⊤ : Subgraph G').deleteVerts u).coe := by
  intro v w hvw
  aesop

@[gcongr, mono]
/-
**SimpleGraph.Subgraph.deleteVerts_anti** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.S
ubgraph`。
形式化陈述：deleteVerts_anti {s s' : Set V} (h : s subseteq s') : G'.deleteVerts s' <=
 G'.deleteVerts s
参数：h : s subseteq s'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Subgraph.induce_mono`：induce_mono (hg : G' <= G'') (hs : s s
ubseteq s') : G'.induce s <= G''.induce s'
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Set.sdiff_subset_sdiff_right`：sdiff_subset_sdiff_right {s t u : Set α} (
h : t subseteq u) : s \ u subseteq s \ t
-/
theorem deleteVerts_anti {s s' : Set V} (h : s ⊆ s') : G'.deleteVerts s' ≤ G'.deleteVerts s :=
  induce_mono (le_refl _) (Set.sdiff_subset_sdiff_right h)

@[simp]
/-
**SimpleGraph.Subgraph.deleteVerts_inter_verts_left_eq** 是 Mathlib 中的一个定理，位于命名空间
 `SimpleGraph.Subgraph`。
形式化陈述：deleteVerts_inter_verts_left_eq : G'.deleteVerts (G'.verts inter s) = G'.d
eleteVerts s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Subgraph.ext`：∀ {V : Type u} {G : SimpleGraph V} {x y : G.Su
bgraph}, x.verts = y.verts → x.Adj = y.Adj → x = y
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `SimpleGraph.Subgraph.induce_verts`：∀ {V : Type u} {G : SimpleGraph V} (G
' : G.Subgraph) (s : Set V), (G'.induce s).verts = s
· 使用定理 `Set.sdiff_self_inter`：sdiff_self_inter {s t : Set α} : s \ (s inter t) =
 s \ t
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `SimpleGraph.Subgraph.induce_adj`：∀ {V : Type u} {G : SimpleGraph V} (G' 
: G.Subgraph) (s : Set V) (u v : V),   (G'.induce s).Adj u v = (u ∈ s ∧ v ∈ s ∧ 
G'.Adj u v)
-/
theorem deleteVerts_inter_verts_left_eq : G'.deleteVerts (G'.verts ∩ s) = G'.deleteVerts s := by
  ext <;> simp +contextual

@[simp]
/-
**SimpleGraph.Subgraph.deleteVerts_inter_verts_set_right_eq** 是 Mathlib 中的一个定理，位
于命名空间 `SimpleGraph.Subgraph`。
形式化陈述：deleteVerts_inter_verts_set_right_eq : G'.deleteVerts (s inter G'.verts) =
 G'.deleteVerts s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Subgraph.ext`：∀ {V : Type u} {G : SimpleGraph V} {x y : G.Su
bgraph}, x.verts = y.verts → x.Adj = y.Adj → x = y
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `SimpleGraph.Subgraph.induce_verts`：∀ {V : Type u} {G : SimpleGraph V} (G
' : G.Subgraph) (s : Set V), (G'.induce s).verts = s
· 使用定理 `Set.sdiff_inter_self_eq_sdiff`：sdiff_inter_self_eq_sdiff {s t : Set α} :
 s \ (t inter s) = s \ t
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `SimpleGraph.Subgraph.induce_adj`：∀ {V : Type u} {G : SimpleGraph V} (G' 
: G.Subgraph) (s : Set V) (u v : V),   (G'.induce s).Adj u v = (u ∈ s ∧ v ∈ s ∧ 
G'.Adj u v)
-/
theorem deleteVerts_inter_verts_set_right_eq :
    G'.deleteVerts (s ∩ G'.verts) = G'.deleteVerts s := by
  ext <;> simp +contextual
/-
**SimpleGraph.Subgraph.instDecidableRel_deleteVerts_adj** 是 Mathlib 中的一个实例，位于命名空
间 `SimpleGraph.Subgraph`。
形式化陈述：instDecidableRel_deleteVerts_adj (u : Set V) [r : DecidableRel G.Adj] : De
cidableRel ((⊤ : G.Subgraph).deleteVerts u).coe.Adj
参数：u : Set V。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instDecidableRel_deleteVerts_adj (u : Set V) [r : DecidableRel G.Adj] :
    DecidableRel ((⊤ : G.Subgraph).deleteVerts u).coe.Adj :=
  fun x y =>
    if h : G.Adj x y
    then
      .isTrue <| SimpleGraph.Subgraph.Adj.coe <| Subgraph.deleteVerts_adj.mpr
        ⟨by trivial, x.2.2, by trivial, y.2.2, h⟩
    else
      .isFalse <| fun hadj ↦ h <| Subgraph.coe_adj_sub _ _ _ hadj

set_option backward.isDefEq.respectTransparency false in
/-- Equivalence between a subgraph with deleted vertices and its corresponding simple graph. -/
/-
**SimpleGraph.Subgraph.coeDeleteVertsIso** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph.
Subgraph`。
形式化陈述：coeDeleteVertsIso (s : Set V) : (G'.deleteVerts s).coe ≃g G'.coe.induce {v
 : G'.verts | ↑v ∉ s} where toFun
参数：s : Set V。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Equivalence between a subgraph with deleted vertices and its corresponding simpl
e graph.
-/
def coeDeleteVertsIso (s : Set V) :
    (G'.deleteVerts s).coe ≃g G'.coe.induce {v : G'.verts | ↑v ∉ s} where
  toFun := fun ⟨v, hv⟩ ↦ ⟨⟨v, Set.mem_of_mem_inter_left hv⟩, by aesop⟩
  invFun := fun ⟨v, hv⟩ ↦ ⟨v, by simp_all⟩
  map_rel_iff' := by simp

end DeleteVerts

end Subgraph

end SimpleGraph

