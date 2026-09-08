/-
Copyright (c) 2022 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Bipartite
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.EdgeConnectivity
public import Mathlib.Combinatorics.SimpleGraph.CycleGraph
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
public import Mathlib.Combinatorics.SimpleGraph.Metric

/-!

# Acyclic graphs and trees

This module introduces *acyclic graphs* (a.k.a. *forests*) and *trees*.

## Main definitions

* `SimpleGraph.IsAcyclic` is a predicate for a graph having no cyclic walks.
* `SimpleGraph.IsTree` is a predicate for a graph being a tree (a connected acyclic graph).

## Main statements

* `SimpleGraph.isAcyclic_iff_path_unique` characterizes acyclicity in terms of uniqueness of
  paths between pairs of vertices.
* `SimpleGraph.isAcyclic_iff_forall_edge_isBridge` characterizes acyclicity in terms of every
  edge being a bridge edge.
* `SimpleGraph.isTree_iff_existsUnique_path` characterizes trees in terms of existence and
  uniqueness of paths between pairs of vertices from a nonempty vertex type.

## References

The structure of the proofs for `SimpleGraph.IsAcyclic` and `SimpleGraph.IsTree`, including
supporting lemmas about `SimpleGraph.IsBridge`, generally follows the high-level description
for these theorems for multigraphs from [Chou1994].

## Tags

acyclic graphs, trees
-/

@[expose] public section


namespace SimpleGraph

open Walk

variable {V V' : Type*} (G : SimpleGraph V) (G' : SimpleGraph V')

/-- A graph is *acyclic* (or a *forest*) if it has no cycles. -/
/-
**SimpleGraph.IsAcyclic** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph`。
形式化陈述：IsAcyclic : Prop
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A graph is *acyclic* (or a *forest*) if it has no cycles.
-/
def IsAcyclic : Prop := ∀ ⦃v : V⦄ (c : G.Walk v v), ¬c.IsCycle

/-- A *tree* is a connected acyclic graph. -/
@[mk_iff]
/-
**SimpleGraph.IsTree** 是 Mathlib 中的一个归纳类型，位于命名空间 `SimpleGraph`。
形式化陈述：{V : Type u_1} → SimpleGraph V → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A *tree* is a connected acyclic graph.
-/
structure IsTree : Prop extends
  connected : G.Connected where
  /-- A tree is acyclic. -/
  isAcyclic : G.IsAcyclic

@[deprecated (since := "2026-03-18")] alias IsTree.isConnected := IsTree.connected
@[deprecated (since := "2026-03-18")] alias IsTree.IsAcyclic := IsTree.isAcyclic

variable {G G'}
/-
**SimpleGraph.isAcyclic_bot** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：∀ {V : Type u_1}, ⊥.IsAcyclic
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Walk.IsCircuit.ne_bot`：∀ {V : Type u} {G : SimpleGraph V} {u
 : V} {p : G.Walk u u}, p.IsCircuit → G ≠ ⊥
· 使用定理 `SimpleGraph.Walk.IsCycle.isCircuit`：∀ {V : Type u} {G : SimpleGraph V} {
u : V} {p : G.Walk u u}, p.IsCycle → p.IsCircuit
-/
@[simp] lemma isAcyclic_bot : IsAcyclic (⊥ : SimpleGraph V) := fun _a _w hw ↦ hw.ne_bot rfl

/-- A graph that has an injective homomorphism to an acyclic graph is acyclic. -/
/-
**SimpleGraph.IsAcyclic.comap** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.IsAcyclic`。
形式化陈述：∀ {V : Type u_1} {V' : Type u_2} {G : SimpleGraph V} {G' : SimpleGraph V'}
 (f : G →g G'),   Function.Injective ⇑f → G'.IsAcyclic → G.IsAcyclic
参数：f : G →g G'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `SimpleGraph.Walk.IsCycle.map`：∀ {V : Type u} {V' : Type v} {G : SimpleGr
aph V} {G' : SimpleGraph V'} {f : G →g G'} {u : V} {p : G.Walk u u},   Function.
Injective ⇑f → p.I…

--- 原说明 ---
A graph that has an injective homomorphism to an acyclic graph is acyclic.
-/
lemma IsAcyclic.comap (f : G →g G') (hinj : Function.Injective f) (h : G'.IsAcyclic) :
    G.IsAcyclic :=
  fun _ _ ↦ mt (.map hinj) (h _)
/-
**SimpleGraph.IsAcyclic.embedding** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.IsAcycl
ic`。
形式化陈述：∀ {V : Type u_1} {V' : Type u_2} {G : SimpleGraph V} {G' : SimpleGraph V'}
 (f : G ↪g G'), G'.IsAcyclic → G.IsAcyclic
参数：f : G ↪g G'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.IsAcyclic.comap`：∀ {V : Type u_1} {V' : Type u_2} {G : Simpl
eGraph V} {G' : SimpleGraph V'} (f : G →g G'),   Function.Injective ⇑f → G'.IsAc
yclic → G.IsAcycl…
· 使用定理 `RelEmbedding.injective`：injective (f : r ↪r s) : Injective f
-/
lemma IsAcyclic.embedding (f : G ↪g G') (h : G'.IsAcyclic) : G.IsAcyclic :=
  h.comap f f.injective

/-- Isomorphic graphs are acyclic together. -/
/-
**SimpleGraph.Iso.isAcyclic_iff** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Iso`。
形式化陈述：∀ {V : Type u_1} {V' : Type u_2} {G : SimpleGraph V} {G' : SimpleGraph V'}
 (f : G ≃g G'), G.IsAcyclic ↔ G'.IsAcyclic
参数：f : G ≃g G'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.IsAcyclic.embedding`：∀ {V : Type u_1} {V' : Type u_2} {G : S
impleGraph V} {G' : SimpleGraph V'} (f : G ↪g G'), G'.IsAcyclic → G.IsAcyclic

--- 原说明 ---
Isomorphic graphs are acyclic together.
-/
lemma Iso.isAcyclic_iff (f : G ≃g G') : G.IsAcyclic ↔ G'.IsAcyclic :=
  ⟨fun h ↦ h.embedding f.symm, fun h ↦ h.embedding f⟩

/-- Isomorphic graphs are trees together. -/
/-
**SimpleGraph.Iso.isTree_iff** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Iso`。
形式化陈述：∀ {V : Type u_1} {V' : Type u_2} {G : SimpleGraph V} {G' : SimpleGraph V'}
 (f : G ≃g G'), G.IsTree ↔ G'.IsTree
参数：f : G ≃g G'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `SimpleGraph.Iso.connected_iff`：∀ {V : Type u} {V' : Type v} {G : SimpleG
raph V} {H : SimpleGraph V'} (e : G ≃g H), G.Connected ↔ H.Connected
· 使用定理 `SimpleGraph.Iso.isAcyclic_iff`：∀ {V : Type u_1} {V' : Type u_2} {G : Sim
pleGraph V} {G' : SimpleGraph V'} (f : G ≃g G'), G.IsAcyclic ↔ G'.IsAcyclic
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a

--- 原说明 ---
Isomorphic graphs are trees together.
-/
lemma Iso.isTree_iff (f : G ≃g G') : G.IsTree ↔ G'.IsTree :=
  ⟨fun ⟨hc, ha⟩ ↦ ⟨f.connected_iff.mp hc, f.isAcyclic_iff.mp ha⟩,
   fun ⟨hc, ha⟩ ↦ ⟨f.connected_iff.mpr hc, f.isAcyclic_iff.mpr ha⟩⟩
/-
**SimpleGraph.IsAcyclic.of_map** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.IsAcyclic`
。
形式化陈述：∀ {V : Type u_1} {V' : Type u_2} {G : SimpleGraph V} (f : V ↪ V'), (Simple
Graph.map (⇑f) G).IsAcyclic → G.IsAcyclic
参数：f : V ↪ V'；SimpleGraph.map (⇑f) G。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.IsAcyclic.embedding`：∀ {V : Type u_1} {V' : Type u_2} {G : S
impleGraph V} {G' : SimpleGraph V'} (f : G ↪g G'), G'.IsAcyclic → G.IsAcyclic
-/
lemma IsAcyclic.of_map (f : V ↪ V') (h : G.map f |>.IsAcyclic) : G.IsAcyclic :=
  h.embedding <| SimpleGraph.Embedding.map ..
/-
**SimpleGraph.IsAcyclic.of_comap** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.IsAcycli
c`。
形式化陈述：∀ {V : Type u_1} {V' : Type u_2} {G : SimpleGraph V} (f : V' ↪ V), G.IsAcy
clic → (SimpleGraph.comap (⇑f) G).IsAcyclic
参数：f : V' ↪ V；SimpleGraph.comap (⇑f) G。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.IsAcyclic.embedding`：∀ {V : Type u_1} {V' : Type u_2} {G : S
impleGraph V} {G' : SimpleGraph V'} (f : G ↪g G'), G'.IsAcyclic → G.IsAcyclic
-/
lemma IsAcyclic.of_comap (f : V' ↪ V) (h : G.IsAcyclic) : G.comap f |>.IsAcyclic :=
  h.embedding <| SimpleGraph.Embedding.comap ..

/-- A graph induced from an acyclic graph is acyclic. -/
/-
**SimpleGraph.IsAcyclic.induce** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.IsAcyclic`
。
形式化陈述：∀ {V : Type u_1} {G : SimpleGraph V}, G.IsAcyclic → ∀ (s : Set V), (Simple
Graph.induce s G).IsAcyclic
参数：s : Set V；SimpleGraph.induce s G。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.IsAcyclic.of_comap`：∀ {V : Type u_1} {V' : Type u_2} {G : Si
mpleGraph V} (f : V' ↪ V), G.IsAcyclic → (SimpleGraph.comap (⇑f) G).IsAcyclic

--- 原说明 ---
A graph induced from an acyclic graph is acyclic.
-/
lemma IsAcyclic.induce (h : G.IsAcyclic) (s : Set V) : G.induce s |>.IsAcyclic :=
  h.of_comap _

/-- A subgraph of an acyclic graph is acyclic. -/
/-
**SimpleGraph.IsAcyclic.subgraph** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.IsAcycli
c`。
形式化陈述：∀ {V : Type u_1} {G : SimpleGraph V}, G.IsAcyclic → ∀ (H : G.Subgraph), H.
coe.IsAcyclic
参数：H : G.Subgraph。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.IsAcyclic.comap`：∀ {V : Type u_1} {V' : Type u_2} {G : Simpl
eGraph V} {G' : SimpleGraph V'} (f : G →g G'),   Function.Injective ⇑f → G'.IsAc
yclic → G.IsAcycl…
· 使用定理 `SimpleGraph.Subgraph.hom_injective`：hom_injective {x : Subgraph G} : Fun
ction.Injective x.hom

--- 原说明 ---
A subgraph of an acyclic graph is acyclic.
-/
lemma IsAcyclic.subgraph (h : G.IsAcyclic) (H : G.Subgraph) : H.coe.IsAcyclic :=
  h.comap _ H.hom_injective

/-- A spanning subgraph of an acyclic graph is acyclic. -/
/-
**SimpleGraph.IsAcyclic.anti** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.IsAcyclic`。
形式化陈述：∀ {V : Type u_1} {G G' : SimpleGraph V}, G ≤ G' → G'.IsAcyclic → G.IsAcycl
ic
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.IsAcyclic.comap`：∀ {V : Type u_1} {V' : Type u_2} {G : Simpl
eGraph V} {G' : SimpleGraph V'} (f : G →g G'),   Function.Injective ⇑f → G'.IsAc
yclic → G.IsAcycl…
· 使用定理 `Function.injective_id`：∀ {α : Sort u_1}, Function.Injective id

--- 原说明 ---
A spanning subgraph of an acyclic graph is acyclic.
-/
lemma IsAcyclic.anti {G' : SimpleGraph V} (hsub : G ≤ G') (h : G'.IsAcyclic) : G.IsAcyclic :=
  h.comap ⟨_, fun h ↦ hsub h⟩ Function.injective_id
/-
**SimpleGraph.Walk.exists_mem_contains_edges_of_directed** 是 Mathlib 中的一个引理，位于命名
空间 `SimpleGraph`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma Walk.exists_mem_contains_edges_of_directed (Hs : Set <| SimpleGraph V)
    (hHs : Hs.Nonempty) (h_dir : DirectedOn (· ≤ ·) Hs) {u v : V} (p : (sSup Hs).Walk u v) :
    ∃ H ∈ Hs, ∀ e ∈ p.edges, e ∈ H.edgeSet := by
  induction p with
  | nil => exact ⟨hHs.some, hHs.some_mem, by simp⟩
  | @cons u v w h_adj p ih =>
    obtain ⟨H₁, hH₁, ih⟩ := ih
    obtain ⟨H₂, hH₂, h_adj⟩ : ∃ H₂ ∈ Hs, H₂.Adj u v := h_adj
    obtain ⟨H, hH, h₁, h₂⟩ := h_dir H₁ hH₁ H₂ hH₂
    simpa using ⟨H, hH, (le_iff_adj.mp h₂) _ _ h_adj, fun a ha => edgeSet_mono h₁ (ih a ha)⟩

/-- The directed supremum of acyclic graphs is acyclic. -/
/-
**SimpleGraph.isAcyclic_sSup_of_isAcyclic_directedOn** 是 Mathlib 中的一个引理，位于命名空间 `
SimpleGraph`。
形式化陈述：isAcyclic_sSup_of_isAcyclic_directedOn (Hs : Set <| SimpleGraph V) (h_acyc
 : forall H in Hs, H.IsAcyclic) (h_dir : DirectedOn (· <= ·) Hs) : IsAcyclic (sS
up Hs)
参数：Hs : Set <| SimpleGraph V；h_acyc : forall H in Hs, H.IsAcyclic；h_dir : Direct
edOn (· <= ·) Hs。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Set α) : s = ∅ ∨ s.N
onempty
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sSup_empty`：sSup_empty : sSup ∅ = (⊥ : α)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `_private.Mathlib.Combinatorics.SimpleGraph.Acyclic.0.SimpleGraph.Walk.ex
ists_mem_contains_edges_of_directed`：∀ {V : Type u_1} (Hs : Set (SimpleGraph V))
,   Hs.Nonempty →     DirectedOn (fun x1 x2 => x1 ≤ x2) Hs → ∀ {u v : V} (p : (s
Sup Hs).Walk u v)…
· 使用定理 `SimpleGraph.Walk.IsCycle.transfer`：∀ {V : Type u} {G : SimpleGraph V} {u
 : V} {H : SimpleGraph V} {q : G.Walk u u},   q.IsCycle → ∀ (hq : ∀ e ∈ q.edges,
 e ∈ H.edgeSet), (q.tra…

--- 原说明 ---
The directed supremum of acyclic graphs is acyclic.
-/
lemma isAcyclic_sSup_of_isAcyclic_directedOn (Hs : Set <| SimpleGraph V)
    (h_acyc : ∀ H ∈ Hs, H.IsAcyclic) (h_dir : DirectedOn (· ≤ ·) Hs) : IsAcyclic (sSup Hs) := by
  rcases Hs.eq_empty_or_nonempty with rfl | hnemp
  · simp
  · intro u p hp
    obtain ⟨H, hH, hpH⟩ := p.exists_mem_contains_edges_of_directed Hs hnemp h_dir
    exact h_acyc H hH (p.transfer H hpH) <| Walk.IsCycle.transfer hp hpH

/-- Every acyclic subgraph `H ≤ G` is contained in a maximal such subgraph. -/
/-
**SimpleGraph.exists_maximal_isAcyclic_of_le_isAcyclic** 是 Mathlib 中的一个定理，位于命名空间
 `SimpleGraph`。
形式化陈述：exists_maximal_isAcyclic_of_le_isAcyclic {H : SimpleGraph V} (hHG : H <= G
) (hH : H.IsAcyclic) : exists H' : SimpleGraph V, H <= H' ∧ Maximal (fun H => H 
<= G ∧ H.IsAcyclic) H'
参数：hHG : H <= G；hH : H.IsAcyclic。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `zorn_le_nonempty₀`：zorn_le_nonempty₀ (s : Set α) (ih : forall c subseteq
 s, IsChain (· <= ·) c -> forall y in c, exists ub in s, forall z in c, z <= ub)
 (x : α…
· 使用引理 `SimpleGraph.isAcyclic_sSup_of_isAcyclic_directedOn`：isAcyclic_sSup_of_is
Acyclic_directedOn (Hs : Set <| SimpleGraph V) (h_acyc : forall H in Hs, H.IsAcy
clic) (h_dir : DirectedOn (· <= ·) Hs) :…
· 使用定理 `IsChain.directedOn`：IsChain.directedOn (H : IsChain r s) : DirectedOn r 
s
· 使用定理 `le_sSup`：le_sSup (h : a in s) : a <= sSup s

--- 原说明 ---
Every acyclic subgraph `H ≤ G` is contained in a maximal such subgraph.
-/
theorem exists_maximal_isAcyclic_of_le_isAcyclic
    {H : SimpleGraph V} (hHG : H ≤ G) (hH : H.IsAcyclic) :
    ∃ H' : SimpleGraph V, H ≤ H' ∧ Maximal (fun H => H ≤ G ∧ H.IsAcyclic) H' := by
  refine zorn_le_nonempty₀ {H | H ≤ G ∧ H.IsAcyclic} (fun c hcs hc y hy ↦ ?_) _ ⟨hHG, hH⟩
  refine ⟨sSup c, ⟨?_, ?_⟩, fun _ ↦ le_sSup⟩
  · grind [sSup_le_iff]
  · exact isAcyclic_sSup_of_isAcyclic_directedOn c (by grind) hc.directedOn

set_option backward.isDefEq.respectTransparency.types false in
/-- A connected component of an acyclic graph is a tree. -/
/-
**SimpleGraph.IsAcyclic.isTree_connectedComponent** 是 Mathlib 中的一个定理，位于命名空间 `Sim
pleGraph.IsAcyclic`。
形式化陈述：∀ {V : Type u_1} {G : SimpleGraph V}, G.IsAcyclic → ∀ (c : G.ConnectedComp
onent), c.toSimpleGraph.IsTree
参数：c : G.ConnectedComponent。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SimpleGraph.ConnectedComponent.connected_toSimpleGraph`：connected_toSimp
leGraph (C : ConnectedComponent G) : (C.toSimpleGraph).Connected where preconnec
ted
· 使用定理 `SimpleGraph.IsAcyclic.comap`：∀ {V : Type u_1} {V' : Type u_2} {G : Simpl
eGraph V} {G' : SimpleGraph V'} (f : G →g G'),   Function.Injective ⇑f → G'.IsAc
yclic → G.IsAcycl…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p

--- 原说明 ---
A connected component of an acyclic graph is a tree.
-/
lemma IsAcyclic.isTree_connectedComponent (h : G.IsAcyclic) (c : G.ConnectedComponent) :
    c.toSimpleGraph.IsTree where
  connected := c.connected_toSimpleGraph
  isAcyclic := h.comap c.toSimpleGraph_hom <| by simp [ConnectedComponent.toSimpleGraph_hom]
/-
**SimpleGraph.IsAcyclic.of_card_le_two** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Is
Acyclic`。
形式化陈述：∀ {V : Type u_1} {G : SimpleGraph V}, ENat.card V ≤ 2 → G.IsAcyclic
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `SimpleGraph.Walk.IsCircuit.three_le_length`：∀ {V : Type u} {G : SimpleGr
aph V} {v : V} {p : G.Walk v v}, p.IsCircuit → 3 ≤ p.length
· 使用定理 `SimpleGraph.Walk.IsCycle.isCircuit`：∀ {V : Type u} {G : SimpleGraph V} {
u : V} {p : G.Walk u u}, p.IsCycle → p.IsCircuit
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.cast_le`：cast_le : (m : α) <= n ↔ m <= n
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `instIsOrderedRingENat`：IsOrderedRing ℕ∞
· 使用定理 `instZeroLEOneClassENat`：ZeroLEOneClass ℕ∞
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `List.Nodup.length_le_enatCard`：length_le_enatCard : l.length <= ENat.car
d α
· 使用定理 `SimpleGraph.Walk.IsCycle.support_nodup`：∀ {V : Type u} {G : SimpleGraph 
V} {u : V} {p : G.Walk u u}, p.IsCycle → p.support.tail.Nodup
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.Walk.length_support`：length_support {u v : V} (p : G.Walk u 
v) : p.support.length = p.length + 1
· 使用定理 `List.length_tail`：∀ {α : Type u_1} {l : List α}, l.tail.length = l.lengt
h - 1
-/
theorem IsAcyclic.of_card_le_two (h : ENat.card V ≤ 2) : G.IsAcyclic := by
  intro v p hp
  have := hp.three_le_length
  have := Nat.cast_le.mp <| hp.support_nodup.length_le_enatCard.trans h
  rw [List.length_tail, p.length_support] at this
  lia
/-
**SimpleGraph.IsAcyclic.of_subsingleton** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.I
sAcyclic`。
形式化陈述：∀ {V : Type u_1} [Subsingleton V] {G : SimpleGraph V}, G.IsAcyclic
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.IsAcyclic.of_card_le_two`：∀ {V : Type u_1} {G : SimpleGraph 
V}, ENat.card V ≤ 2 → G.IsAcyclic
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `ENat.card_le_one`：∀ {α : Type u_1} [Subsingleton α], ENat.card α ≤ 1
· 使用引理 `one_le_two`：one_le_two [LE α] [ZeroLEOneClass α] [AddLeftMono α] : (1 : 
α) <= 2
· 使用定理 `instZeroLEOneClassENat`：ZeroLEOneClass ℕ∞
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `instIsOrderedRingENat`：IsOrderedRing ℕ∞
-/
lemma IsAcyclic.of_subsingleton [Subsingleton V] {G : SimpleGraph V} : G.IsAcyclic :=
  .of_card_le_two <| ENat.card_le_one.trans one_le_two
/-
**SimpleGraph.Subgraph.isAcyclic_coe_bot** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.
Subgraph`。
形式化陈述：∀ {V : Type u_1} (G : SimpleGraph V), ⊥.coe.IsAcyclic
参数：G : SimpleGraph V。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.IsAcyclic.of_subsingleton`：∀ {V : Type u_1} [Subsingleton V]
 {G : SimpleGraph V}, G.IsAcyclic
· 使用定理 `IsEmpty.instSubsingleton`：∀ {α : Sort u} [IsEmpty α], Subsingleton α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.isEmpty_coe_sort`：isEmpty_coe_sort {s : Set α} : IsEmpty (↥s) ↔ s = 
∅
-/
lemma Subgraph.isAcyclic_coe_bot (G : SimpleGraph V) : (⊥ : G.Subgraph).coe.IsAcyclic :=
  @IsAcyclic.of_subsingleton _ (Set.isEmpty_coe_sort.mpr rfl).instSubsingleton _
/-
**SimpleGraph.IsTree.of_subsingleton** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.IsTr
ee`。
形式化陈述：∀ {V : Type u_1} [Nonempty V] [Subsingleton V] {G : SimpleGraph V}, G.IsTr
ee
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Connected.of_subsingleton`：∀ {V : Type u} {G : SimpleGraph V
} [Nonempty V] [Subsingleton V], G.Connected
· 使用定理 `SimpleGraph.IsAcyclic.of_subsingleton`：∀ {V : Type u_1} [Subsingleton V]
 {G : SimpleGraph V}, G.IsAcyclic
-/
lemma IsTree.of_subsingleton [Nonempty V] [Subsingleton V] {G : SimpleGraph V} : G.IsTree :=
  ⟨.of_subsingleton, .of_subsingleton⟩
/-
**SimpleGraph.IsTree.coe_singletonSubgraph** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGrap
h.IsTree`。
形式化陈述：∀ {V : Type u_1} (G : SimpleGraph V) (v : V), (G.singletonSubgraph v).coe.
IsTree
参数：G : SimpleGraph V；v : V；G.singletonSubgraph v。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.IsTree.of_subsingleton`：∀ {V : Type u_1} [Nonempty V] [Subsi
ngleton V] {G : SimpleGraph V}, G.IsTree
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
-/
theorem IsTree.coe_singletonSubgraph (G : SimpleGraph V) (v : V) :
    G.singletonSubgraph v |>.coe.IsTree :=
  .of_subsingleton

set_option backward.defeqAttrib.useBackward true in
/-
**SimpleGraph.IsTree.coe_subgraphOfAdj** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Is
Tree`。
形式化陈述：∀ {V : Type u_1} {G : SimpleGraph V} {u v : V} (h : G.Adj u v), (G.subgrap
hOfAdj h).coe.IsTree
参数：h : G.Adj u v；G.subgraphOfAdj h。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Subgraph.Connected.coe`：∀ {V : Type u} {G : SimpleGraph V} {
H : G.Subgraph}, H.Connected → H.coe.Connected
· 使用定理 `SimpleGraph.Subgraph.subgraphOfAdj_connected`：subgraphOfAdj_connected {v
 w : V} (hvw : G.Adj v w) : (G.subgraphOfAdj hvw).Connected
· 使用定理 `SimpleGraph.Walk.adj_snd`：∀ {V : Type u} {G : SimpleGraph V} {v w : V} {
p : G.Walk v w}, ¬p.Nil → G.Adj v p.snd
· 使用定理 `SimpleGraph.Walk.IsCycle.not_nil`：∀ {V : Type u} {G : SimpleGraph V} {v 
: V} {p : G.Walk v v}, p.IsCycle → ¬p.Nil
· 使用引理 `SimpleGraph.Walk.adj_penultimate`：adj_penultimate {p : G.Walk v w} (hp :
 ¬ p.Nil) : G.Adj p.penultimate w
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Prod.mk.injEq`：∀ {α : Type u} {β : Type v} (fst : α) (snd : β) (fst_1 : 
α) (snd_1 : β),   ((fst, snd) = (fst_1, snd_1)) = (fst = fst_1 ∧ snd = snd_1)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
-/
theorem IsTree.coe_subgraphOfAdj {u v : V} (h : G.Adj u v) : G.subgraphOfAdj h |>.coe.IsTree := by
  refine ⟨Subgraph.subgraphOfAdj_connected h, fun w p hp ↦ ?_⟩
  have : _ = _ := p.adj_snd hp.not_nil
  have : _ = _ := p.adj_penultimate hp.not_nil
  #adaptation_note /-- Before https://github.com/leanprover/lean4/pull/13166
  (replacing grind's canonicalizer with a type-directed normalizer), `grind` closed this goal.
  It is not yet clear whether this is due to defeq abuse in Mathlib or a problem in the new
  canonicalizer; a minimization would help. The original proof was:
  `grind [Sym2.eq_iff, IsCycle.snd_ne_penultimate]` -/
  simp_all
  grind [IsCycle.snd_ne_penultimate]
/-
**SimpleGraph.isAcyclic_iff_forall_isBridge** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGra
ph`。
形式化陈述：isAcyclic_iff_forall_isBridge : G.IsAcyclic ↔ forall ⦃e⦄, e in G.edgeSet -
> G.IsBridge e where .elim .mpr fun v p hc => hG p hc mp hG e he
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `SimpleGraph.isBridge_iff_forall_cycle_notMem`：isBridge_iff_forall_cycle_
notMem {e : Sym2 V} (he : e in G.edgeSet) : G.IsBridge e ↔ forall ⦃u : V⦄ (p : G
.Walk u u), p.IsCycle -> e ∉ p.edg…
· 使用定理 `List.exists_mem_of_ne_nil`：∀ {α : Type u_1} (l : List α), l ≠ [] → ∃ x, 
x ∈ l
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `SimpleGraph.Walk.IsCycle.not_nil`：∀ {V : Type u} {G : SimpleGraph V} {v 
: V} {p : G.Walk v v}, p.IsCycle → ¬p.Nil
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `SimpleGraph.IsBridge.notMem_edges_of_isCycle`：∀ {V : Type u} {G : Simple
Graph V} {e : Sym2 V} {u : V} {p : G.Walk u u}, G.IsBridge e → p.IsCycle → e ∉ p
.edges
· 使用定理 `SimpleGraph.Walk.edges_subset_edgeSet`：∀ {V : Type u} {G : SimpleGraph V
} {u v : V} (p : G.Walk u v) ⦃e : Sym2 V⦄, e ∈ p.edges → e ∈ G.edgeSet
-/
theorem isAcyclic_iff_forall_isBridge : G.IsAcyclic ↔ ∀ ⦃e⦄, e ∈ G.edgeSet → G.IsBridge e where
  mp hG e he := isBridge_iff_forall_cycle_notMem he |>.mpr fun v p hc ↦ hG p hc |>.elim
  mpr hG v c hc := by
    obtain ⟨e, he⟩ := c.edges.exists_mem_of_ne_nil <| by simp [hc.not_nil]
    exact (hG <| c.edges_subset_edgeSet he).notMem_edges_of_isCycle hc he
/-
**SimpleGraph.isAcyclic_iff_forall_adj_isBridge** 是 Mathlib 中的一个引理，位于命名空间 `Simpl
eGraph`。
形式化陈述：isAcyclic_iff_forall_adj_isBridge : G.IsAcyclic ↔ forall ⦃v w : V⦄, G.Adj 
v w -> G.IsBridge s(v, w)
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
lemma isAcyclic_iff_forall_adj_isBridge :
    G.IsAcyclic ↔ ∀ ⦃v w : V⦄, G.Adj v w → G.IsBridge s(v, w) := by
  simp [isAcyclic_iff_forall_isBridge, Sym2.forall]

@[deprecated (since := "2026-06-04")]
alias isAcyclic_iff_forall_edge_isBridge := isAcyclic_iff_forall_isBridge
/-
**SimpleGraph.isAcyclic_iff_subsingleton_path** 是 Mathlib 中的一个定理，位于命名空间 `SimpleG
raph`。
形式化陈述：isAcyclic_iff_subsingleton_path : G.IsAcyclic ↔ forall u v, Subsingleton (
G.Path u v)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Walk.IsPath.exists_isCycle_of_ne`：∀ {V : Type u} {G : Simple
Graph V} {u v : V} {p q : G.Walk u v},   p.IsPath → q.IsPath → p ≠ q → ∃ u' v' p
' q', p'.IsSubwalk p ∧ q'.IsSubwal…
· 使用定理 `SimpleGraph.Path.isPath`：∀ {V : Type u} {G : SimpleGraph V} {u v : V} (p
 : G.Path u v), (↑p).IsPath
· 使用定理 `SimpleGraph.Walk.IsCycle.isPath_tail`：∀ {V : Type u} {G : SimpleGraph V}
 {u : V} {p : G.Walk u u}, p.IsCycle → p.tail.IsPath
· 使用定理 `SimpleGraph.Adj.symm`：∀ {V : Type u} {G : SimpleGraph V} {u v : V}, G.Ad
j u v → G.Adj v u
· 使用定理 `SimpleGraph.Walk.adj_snd`：∀ {V : Type u} {G : SimpleGraph V} {v w : V} {
p : G.Walk v w}, ¬p.Nil → G.Adj v p.snd
· 使用定理 `SimpleGraph.Walk.IsCycle.not_nil`：∀ {V : Type u} {G : SimpleGraph V} {v 
: V} {p : G.Walk v v}, p.IsCycle → ¬p.Nil
· 使用定理 `SimpleGraph.Walk.IsPath.of_adj`：∀ {V : Type u} {G : SimpleGraph V} {u v 
: V} (h : G.Adj u v), h.toWalk.IsPath
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
-/
theorem isAcyclic_iff_subsingleton_path : G.IsAcyclic ↔ ∀ u v, Subsingleton (G.Path u v) := by
  refine ⟨fun h u v ↦ ⟨fun p q ↦ ?_⟩, fun h v c hc ↦ ?_⟩
  · have := p.isPath.exists_isCycle_of_ne q.isPath
    grind [IsAcyclic, Subtype.coe_inj]
  · have := h _ v |>.elim ⟨_, hc.isPath_tail⟩ ⟨_, .of_adj <| c.adj_snd hc.not_nil |>.symm⟩
    grind [length_cons, length_nil, hc.three_le_length, c.length_tail_add_one hc.not_nil]

alias ⟨IsAcyclic.subsingleton_path, _⟩ := isAcyclic_iff_subsingleton_path

@[deprecated IsAcyclic.subsingleton_path (since := "2026-06-30")]
/-
**SimpleGraph.IsAcyclic.path_unique** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.IsAcy
clic`。
形式化陈述：∀ {V : Type u_1} {G : SimpleGraph V}, G.IsAcyclic → ∀ {v w : V} (p q : G.P
ath v w), p = q
参数：p q : G.Path v w。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `SimpleGraph.IsAcyclic.subsingleton_path`：∀ {V : Type u_1} {G : SimpleGra
ph V}, G.IsAcyclic → ∀ (u v : V), Subsingleton (G.Path u v)
-/
theorem IsAcyclic.path_unique {G : SimpleGraph V} (h : G.IsAcyclic) {v w : V} (p q : G.Path v w) :
    p = q :=
  h.subsingleton_path v w |>.elim p q

@[deprecated isAcyclic_iff_subsingleton_path (since := "2026-06-30")]
/-
**SimpleGraph.isAcyclic_of_path_unique** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：isAcyclic_of_path_unique (h : forall (v w : V) (p q : G.Path v w), p = q) 
: G.IsAcyclic
参数：h : forall (v w : V) (p q : G.Path v w), p = q。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `SimpleGraph.isAcyclic_iff_subsingleton_path`：isAcyclic_iff_subsingleton_
path : G.IsAcyclic ↔ forall u v, Subsingleton (G.Path u v)
-/
theorem isAcyclic_of_path_unique (h : ∀ (v w : V) (p q : G.Path v w), p = q) : G.IsAcyclic :=
  isAcyclic_iff_subsingleton_path.mpr (⟨h · ·⟩)

@[deprecated isAcyclic_iff_subsingleton_path (since := "2026-06-30")]
/-
**SimpleGraph.isAcyclic_iff_path_unique** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：isAcyclic_iff_path_unique : G.IsAcyclic ↔ forall ⦃v w : V⦄ (p q : G.Path v
 w), p = q
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `SimpleGraph.isAcyclic_iff_subsingleton_path`：isAcyclic_iff_subsingleton_
path : G.IsAcyclic ↔ forall u v, Subsingleton (G.Path u v)
· 使用定理 `forall₂_congr`：∀ {α : Sort u_1} {β : α → Sort u_2} {p q : (a : α) → β a 
→ Prop},   (∀ (a : α) (b : β a), p a b ↔ q a b) → ((∀ (a : α) (b : β a), p a b) 
↔ ∀…
· 使用定理 `subsingleton_iff`：subsingleton_iff : Subsingleton α ↔ forall x y : α, x 
= y
-/
theorem isAcyclic_iff_path_unique : G.IsAcyclic ↔ ∀ ⦃v w : V⦄ (p q : G.Path v w), p = q :=
  isAcyclic_iff_subsingleton_path.trans <| forall₂_congr fun _ _ ↦ subsingleton_iff
/-
**SimpleGraph.IsAcyclic.eq_snd_of_adj_start** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGra
ph.IsAcyclic`。
形式化陈述：∀ {V : Type u_1} {G : SimpleGraph V},   G.IsAcyclic → ∀ {u v w : V} {p : G
.Walk u v}, p.IsPath → G.Adj u w → w ∈ p.support → w = p.snd
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Walk.IsPath.takeUntil`：∀ {V : Type u} {G : SimpleGraph V} [i
nst : DecidableEq V] {u v w : V} {p : G.Walk v w},   p.IsPath → ∀ (h : u ∈ p.sup
port), (p.takeUntil u h…
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `SimpleGraph.IsAcyclic.subsingleton_path`：∀ {V : Type u_1} {G : SimpleGra
ph V}, G.IsAcyclic → ∀ (u v : V), Subsingleton (G.Path u v)
-/
theorem IsAcyclic.eq_snd_of_adj_start (h : G.IsAcyclic) {u v w : V} {p : G.Walk u v} (hp : p.IsPath)
    (hadj : G.Adj u w) (hsupp : w ∈ p.support) : w = p.snd := by
  classical
  have := h.subsingleton_path u w |>.elim ⟨_, hp.takeUntil hsupp⟩ <| .singleton hadj
  grind [p.getVert_length_takeUntil hsupp, Path.singleton_coe, length]
/-
**SimpleGraph.IsAcyclic.eq_penultimate_of_adj_end** 是 Mathlib 中的一个定理，位于命名空间 `Sim
pleGraph.IsAcyclic`。
形式化陈述：∀ {V : Type u_1} {G : SimpleGraph V},   G.IsAcyclic → ∀ {u v w : V} {p : G
.Walk u v}, p.IsPath → G.Adj v w → w ∈ p.support → w = p.penultimate
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `SimpleGraph.Walk.snd_reverse`：snd_reverse (p : G.Walk u v) : p.reverse.s
nd = p.penultimate
· 使用定理 `SimpleGraph.IsAcyclic.eq_snd_of_adj_start`：∀ {V : Type u_1} {G : SimpleG
raph V},   G.IsAcyclic → ∀ {u v w : V} {p : G.Walk u v}, p.IsPath → G.Adj u w → 
w ∈ p.support → w = p.snd
· 使用定理 `SimpleGraph.Walk.IsPath.reverse`：∀ {V : Type u} {G : SimpleGraph V} {u v
 : V} {p : G.Walk u v}, p.IsPath → p.reverse.IsPath
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `SimpleGraph.Walk.support_reverse`：support_reverse {u v : V} (p : G.Walk 
u v) : p.reverse.support = p.support.reverse
-/
theorem IsAcyclic.eq_penultimate_of_adj_end (h : G.IsAcyclic) {u v w : V} {p : G.Walk u v}
    (hp : p.IsPath) (hadj : G.Adj v w) (hsupp : w ∈ p.support) : w = p.penultimate := by
  rw [← snd_reverse]
  apply h.eq_snd_of_adj_start hp.reverse hadj
  simpa
/-
**SimpleGraph.IsAcyclic.mem_support_of_ne_mem_support_of_adj_of_isPath** 是 Mathl
ib 中的一个定理，位于命名空间 `SimpleGraph.IsAcyclic`。
形式化陈述：∀ {V : Type u_1} {G : SimpleGraph V},   G.IsAcyclic →     ∀ {u v w : V} {p
 : G.Walk u v} {q : G.Walk u w}, p.IsPath → q.IsPath → G.Adj v w → v ∉ q.support
 → w ∈ p.support
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Adj.symm`：∀ {V : Type u} {G : SimpleGraph V} {u v : V}, G.Ad
j u v → G.Adj v u
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subtype.mk.inj`：∀ {α : Sort u} {p : α → Prop} {val : α} {property : p va
l} {val_1 : α} {property_1 : p val_1},   ⟨val, property⟩ = ⟨val_1, property_1⟩ →
 val…
· 使用定理 `SimpleGraph.Walk.IsPath.concat`：∀ {V : Type u} {G : SimpleGraph V} {u v 
w : V} {p : G.Walk u v},   p.IsPath → w ∉ p.support → ∀ (h : G.Adj v w), (p.conc
at h).IsPath
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `SimpleGraph.IsAcyclic.subsingleton_path`：∀ {V : Type u_1} {G : SimpleGra
ph V}, G.IsAcyclic → ∀ (u v : V), Subsingleton (G.Path u v)
· 使用定理 `SimpleGraph.Walk.support_subset_support_concat`：support_subset_support_c
oncat {u v w : V} (p : G.Walk u v) (hadj : G.Adj v w) : p.support subseteq (p.co
ncat hadj).support
· 使用定理 `SimpleGraph.Walk.end_mem_support`：end_mem_support {u v : V} (p : G.Walk 
u v) : v in p.support
-/
lemma IsAcyclic.mem_support_of_ne_mem_support_of_adj_of_isPath (hG : G.IsAcyclic) {u v w : V}
    {p : G.Walk u v} {q : G.Walk u w} (hp : p.IsPath) (hq : q.IsPath) (hadj : G.Adj v w)
    (hv : v ∉ q.support) : w ∈ p.support := by
  rw [Subtype.mk.inj <| hG.subsingleton_path u v |>.elim ⟨p, hp⟩ ⟨_, hq.concat hv hadj.symm⟩]
  exact q.support_subset_support_concat _ q.end_mem_support
/-
**SimpleGraph.IsAcyclic.ne_mem_support_of_support_of_adj_of_isPath** 是 Mathlib 中
的一个定理，位于命名空间 `SimpleGraph.IsAcyclic`。
形式化陈述：∀ {V : Type u_1} {G : SimpleGraph V},   G.IsAcyclic →     ∀ {u v w : V} {p
 : G.Walk u v} {q : G.Walk u w}, p.IsPath → q.IsPath → G.Adj v w → w ∈ p.support
 → v ∉ q.support
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `SimpleGraph.Walk.IsPath.mem_support_iff_exists_append`：∀ {V : Type u} {G
 : SimpleGraph V} {u v w : V} {p : G.Walk u v},   p.IsPath → (w ∈ p.support ↔ ∃ 
q r, q.IsPath ∧ r.IsPath ∧ p = q.append r)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subtype.mk.inj`：∀ {α : Sort u} {p : α → Prop} {val : α} {property : p va
l} {val_1 : α} {property_1 : p val_1},   ⟨val, property⟩ = ⟨val_1, property_1⟩ →
 val…
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `SimpleGraph.IsAcyclic.subsingleton_path`：∀ {V : Type u_1} {G : SimpleGra
ph V}, G.IsAcyclic → ∀ (u v : V), Subsingleton (G.Path u v)
· 使用定理 `SimpleGraph.Walk.IsPath.ne_of_mem_support_of_append`：∀ {V : Type u} {G :
 SimpleGraph V} {u v w : V} {p : G.Walk u v} {q : G.Walk v w},   (p.append q).Is
Path → ∀ {x y : V}, y ≠ v → x ∈ p.support…
· 使用定理 `SimpleGraph.Adj.ne'`：∀ {V : Type u} {G : SimpleGraph V} {a b : V}, G.Adj
 a b → b ≠ a
· 使用定理 `SimpleGraph.Adj.symm`：∀ {V : Type u} {G : SimpleGraph V} {u v : V}, G.Ad
j u v → G.Adj v u
· 使用定理 `SimpleGraph.Walk.end_mem_support`：end_mem_support {u v : V} (p : G.Walk 
u v) : v in p.support
-/
lemma IsAcyclic.ne_mem_support_of_support_of_adj_of_isPath (hG : G.IsAcyclic) {u v w : V}
    {p : G.Walk u v} {q : G.Walk u w} (hp : p.IsPath) (hq : q.IsPath) (hadj : G.Adj v w)
    (hw : w ∈ p.support) : v ∉ q.support := by
  obtain ⟨p₀, p₁, hp₀, hp₁, happend⟩ := hp.mem_support_iff_exists_append.mp hw
  rw [← Subtype.mk.inj <| hG.subsingleton_path u w |>.elim ⟨p₀, hp₀⟩ ⟨q, hq⟩]
  exact fun hxp => (happend ▸ hp).ne_of_mem_support_of_append hadj.symm.ne' hxp
    (p₁.end_mem_support) rfl
/-
**SimpleGraph.IsAcyclic.path_concat** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.IsAcy
clic`。
形式化陈述：∀ {V : Type u_1} {G : SimpleGraph V},   G.IsAcyclic →     ∀ {u v w : V} {p
 : G.Walk u v} {q : G.Walk u w},       p.IsPath → q.IsPath → ∀ (hadj : G.Adj v w
), v ∈ q.support → q = p.concat hadj
参数：hadj : G.Adj v w。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.IsAcyclic.ne_mem_support_of_support_of_adj_of_isPath`：∀ {V :
 Type u_1} {G : SimpleGraph V},   G.IsAcyclic →     ∀ {u v w : V} {p : G.Walk u 
v} {q : G.Walk u w}, p.IsPath → q.IsPath → G.Adj v w →…
· 使用定理 `SimpleGraph.Adj.symm`：∀ {V : Type u} {G : SimpleGraph V} {u v : V}, G.Ad
j u v → G.Adj v u
· 使用定理 `Subtype.mk.inj`：∀ {α : Sort u} {p : α → Prop} {val : α} {property : p va
l} {val_1 : α} {property_1 : p val_1},   ⟨val, property⟩ = ⟨val_1, property_1⟩ →
 val…
· 使用定理 `SimpleGraph.Walk.IsPath.concat`：∀ {V : Type u} {G : SimpleGraph V} {u v 
w : V} {p : G.Walk u v},   p.IsPath → w ∉ p.support → ∀ (h : G.Adj v w), (p.conc
at h).IsPath
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `SimpleGraph.IsAcyclic.subsingleton_path`：∀ {V : Type u_1} {G : SimpleGra
ph V}, G.IsAcyclic → ∀ (u v : V), Subsingleton (G.Path u v)
-/
lemma IsAcyclic.path_concat (hG : G.IsAcyclic) {u v w : V} {p : G.Walk u v} {q : G.Walk u w}
    (hp : p.IsPath) (hq : q.IsPath) (hadj : G.Adj v w) (hv : v ∈ q.support) :
    q = p.concat hadj := by
  have hw : w ∉ p.support := hG.ne_mem_support_of_support_of_adj_of_isPath hq hp hadj.symm hv
  exact Subtype.mk.inj <| hG.subsingleton_path u w |>.elim ⟨q, hq⟩ ⟨_, hp.concat hw hadj⟩
/-
**SimpleGraph.isTree_iff_existsUnique_path** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGrap
h`。
形式化陈述：isTree_iff_existsUnique_path : G.IsTree ↔ Nonempty V ∧ forall v w : V, exi
sts! p : G.Walk v w, p.IsPath
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `SimpleGraph.Connected.nonempty`：∀ {V : Type u} {G : SimpleGraph V}, G.Co
nnected → Nonempty V
· 使用定理 `SimpleGraph.Connected.preconnected`：∀ {V : Type u} {G : SimpleGraph V}, 
G.Connected → G.Preconnected
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Subtype.ext_iff`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, a
1 = a2 ↔ ↑a1 = ↑a2
· 使用定理 `SimpleGraph.Walk.reachable`：∀ {V : Type u} {G : SimpleGraph V} {u v : V}
 (p : G.Walk u v), G.Reachable u v
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `ExistsUnique.unique`：ExistsUnique.unique {p : α -> Prop} (h : exists! x,
 p x) {y₁ y₂ : α} (py₁ : p y₁) (py₂ : p y₂) : y₁ = y₂
· 使用定理 `Subtype.mk.congr_simp`：∀ {α : Sort u} {p : α → Prop} (val val_1 : α) (e_
val : val = val_1) (property : p val), ⟨val, property⟩ = ⟨val_1, ⋯⟩
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem isTree_iff_existsUnique_path :
    G.IsTree ↔ Nonempty V ∧ ∀ v w : V, ∃! p : G.Walk v w, p.IsPath := by
  classical
  simp_rw [isTree_iff, isAcyclic_iff_subsingleton_path, subsingleton_iff]
  constructor
  · rintro ⟨hc, hu⟩
    refine ⟨hc.nonempty, ?_⟩
    intro v w
    let q := (hc v w).some.toPath
    use q
    simp only [true_and, Path.isPath]
    intro p hp
    specialize hu v w ⟨p, hp⟩ q
    exact Subtype.ext_iff.mp hu
  · rintro ⟨hV, h⟩
    refine ⟨Connected.mk ?_, ?_⟩
    · intro v w
      obtain ⟨p, _⟩ := h v w
      exact p.reachable
    · rintro v w ⟨p, hp⟩ ⟨q, hq⟩
      simp only [ExistsUnique.unique (h v w) hp hq]
/-
**SimpleGraph.IsTree.existsUnique_path** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Is
Tree`。
形式化陈述：∀ {V : Type u_1} {G : SimpleGraph V}, G.IsTree → ∀ (v w : V), ∃! p, p.IsPa
th
参数：v w : V。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `SimpleGraph.isTree_iff_existsUnique_path`：isTree_iff_existsUnique_path :
 G.IsTree ↔ Nonempty V ∧ forall v w : V, exists! p : G.Walk v w, p.IsPath
-/
lemma IsTree.existsUnique_path (hG : G.IsTree) : ∀ v w, ∃! p : G.Walk v w, p.IsPath :=
  (isTree_iff_existsUnique_path.1 hG).2
/-
**SimpleGraph.IsAcyclic.isPath_iff_isChain** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGrap
h.IsAcyclic`。
形式化陈述：∀ {V : Type u_1} {G : SimpleGraph V},   G.IsAcyclic → ∀ {v w : V} (p : G.W
alk v w), p.IsPath ↔ List.IsChain (fun x1 x2 => x1 ≠ x2) p.edges
参数：p : G.Walk v w；fun x1 x2 => x1 ≠ x2。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.Pairwise.isChain`：∀ {α : Type u_1} {R : α → α → Prop} {l : List α},
 List.Pairwise R l → List.IsChain R l
· 使用定理 `SimpleGraph.Walk.edges_nodup_of_support_nodup`：edges_nodup_of_support_no
dup {u v : V} {p : G.Walk u v} (h : p.support.Nodup) : p.edges.Nodup
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `SimpleGraph.Walk.isPath_def`：isPath_def {u v : V} (p : G.Walk u v) : p.I
sPath ↔ p.support.Nodup
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `List.isChain_cons`：isChain_cons {x l} : IsChain R (x :: l) ↔ (forall y i
n head? l, R x y) ∧ IsChain R l
· 使用定理 `SimpleGraph.Walk.edges_cons`：edges_cons {u v w : V} (h : G.Adj u v) (p :
 G.Walk v w) : (cons h p).edges = s(u, v) :: p.edges
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `SimpleGraph.Walk.cons_isPath_iff`：cons_isPath_iff {u v w : V} (h : G.Adj
 u v) (p : G.Walk v w) : (cons h p).IsPath ↔ p.IsPath ∧ u ∉ p.support
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Nat.eq_zero_or_pos`：∀ (n : ℕ), n = 0 ∨ n > 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `SimpleGraph.Walk.nil_iff_support_eq`：nil_iff_support_eq {p : G.Walk v w}
 : p.Nil ↔ p.support = [v]
· 使用定理 `SimpleGraph.Walk.length_eq_zero_iff`：length_eq_zero_iff {p : G.Walk u v}
 : p.length = 0 ↔ p.Nil
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `SimpleGraph.Adj.ne`：∀ {V : Type u} {G : SimpleGraph V} {a b : V}, G.Adj 
a b → a ≠ b
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `List.Nodup.sublist`：∀ {α : Type u_1} {l₁ l₂ : List α}, l₁.Sublist l₂ → l
₂.Nodup → l₁.Nodup
· 使用定理 `List.IsInfix.sublist`：∀ {α : Type u_1} {l₁ l₂ : List α}, l₁ <:+: l₂ → l₁
.Sublist l₂
· 使用定理 `SimpleGraph.Walk.take_spec`：take_spec {u v w : V} (p : G.Walk v w) (h : 
u in p.support) : (p.takeUntil u h).append (p.dropUntil u h) = p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `SimpleGraph.Walk.adj_snd`：∀ {V : Type u} {G : SimpleGraph V} {v w : V} {
p : G.Walk v w}, ¬p.Nil → G.Adj v p.snd
（共 41 条，此处仅展示前 30 条）
-/
theorem IsAcyclic.isPath_iff_isChain (hG : G.IsAcyclic) {v w : V} (p : G.Walk v w) :
     p.IsPath ↔ List.IsChain (· ≠ ·) p.edges := by
  classical
  refine ⟨fun h ↦ (edges_nodup_of_support_nodup <| p.isPath_def.mp h).isChain, fun h ↦ ?_⟩
  induction p with
  | nil => simp
  | @cons u' v' _ head tail ih =>
    have hcc := List.isChain_cons.mp (edges_cons _ _ ▸ h)
    refine cons_isPath_iff head tail |>.mpr ⟨ih hcc.2, ?_⟩
    rcases tail.length.eq_zero_or_pos with h' | h'
    · simp [nil_iff_support_eq.mp (length_eq_zero_iff.mp h'), head.ne]
    · by_contra hh
      apply hG <| cons head (tail.takeUntil u' hh)
      simp only [isCycle_def, isTrail_def, edges_cons, List.nodup_cons, ne_eq, reduceCtorEq,
        not_false_eq_true, support_cons, List.tail_cons, true_and]
      have : cons head (tail.takeUntil u' hh) |>.support.tail.Nodup :=
        tail.isPath_def.mp (ih hcc.2) |>.sublist <| List.IsInfix.sublist
          ⟨[], (tail.dropUntil u' hh).support.tail, by simp [← support_append]⟩
      refine ⟨⟨?_, edges_nodup_of_support_nodup this⟩, this⟩
      by_contra hhh
      refine hcc.1 s(u', v') ?_ rfl
      rw [← tail.cons_tail_eq (by simp [not_nil_iff_lt_length, h'])]
      have := IsPath.mk' this |>.eq_snd_of_mem_edges (Sym2.eq_swap ▸ hhh)
      simp [this, snd_takeUntil head.ne]
/-
**SimpleGraph.IsAcyclic.isPath_iff_isTrail** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGrap
h.IsAcyclic`。
形式化陈述：∀ {V : Type u_1} {G : SimpleGraph V}, G.IsAcyclic → ∀ {v w : V} (p : G.Wal
k v w), p.IsPath ↔ p.IsTrail
参数：p : G.Walk v w。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Walk.IsPath.isTrail`：∀ {V : Type u} {G : SimpleGraph V} {u v
 : V} {p : G.Walk u v}, p.IsPath → p.IsTrail
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `SimpleGraph.IsAcyclic.isPath_iff_isChain`：∀ {V : Type u_1} {G : SimpleGr
aph V},   G.IsAcyclic → ∀ {v w : V} (p : G.Walk v w), p.IsPath ↔ List.IsChain (f
un x1 x2 => x1 ≠ x2) p.edges
· 使用定理 `List.Pairwise.isChain`：∀ {α : Type u_1} {R : α → α → Prop} {l : List α},
 List.Pairwise R l → List.IsChain R l
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `SimpleGraph.Walk.isTrail_def`：∀ {V : Type u} {G : SimpleGraph V} {u v : 
V} (p : G.Walk u v), p.IsTrail ↔ p.edges.Nodup
-/
theorem IsAcyclic.isPath_iff_isTrail (hG : G.IsAcyclic) {v w : V} (p : G.Walk v w) :
    p.IsPath ↔ p.IsTrail :=
  ⟨IsPath.isTrail, fun h ↦ hG.isPath_iff_isChain p |>.mpr <| p.isTrail_def.mp h |>.isChain⟩

set_option backward.isDefEq.respectTransparency.types false in
/-
**SimpleGraph.IsTree.card_edgeFinset** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.IsTr
ee`。
形式化陈述：∀ {V : Type u_1} {G : SimpleGraph V} [inst : Fintype V] [inst_1 : Fintype 
↑G.edgeSet],   G.IsTree → G.edgeFinset.card + 1 = Fintype.card V
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Connected.nonempty`：∀ {V : Type u} {G : SimpleGraph V}, G.Co
nnected → Nonempty V
· 使用定理 `SimpleGraph.IsTree.connected`：∀ {V : Type u_1} {G : SimpleGraph V}, G.Is
Tree → G.Connected
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.card_compl`：Finset.card_compl [DecidableEq α] [Fintype α] (s : Fi
nset α) : #sᶜ = Fintype.card α - #s
· 使用定理 `Finset.card_singleton`：card_singleton (a : α) : #{a} = 1
· 使用定理 `Nat.sub_add_cancel`：∀ {n m : ℕ}, m ≤ n → n - m + m = n
· 使用定理 `Fintype.card_pos`：card_pos [h : Nonempty α] : 0 < card α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_left_inj`：∀ {G : Type u_1} [inst : Add G] [IsRightCancelAdd G] (a : 
G) {b c : G}, b + a = c + a ↔ b = c
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用引理 `Finset.card_bij`：card_bij (i : forall a in s, β) (hi : forall a ha, i a 
ha in t) (i_inj : forall a₁ ha₁ a₂ ha₂, i a₁ ha₁ = i a₂ ha₂ -> a₁ = a₂) (i_surj 
: for…
· 使用引理 `SimpleGraph.Walk.not_nil_of_ne`：not_nil_of_ne {p : G.Walk v w} : v != w 
-> ¬ p.Nil
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `SimpleGraph.dart_edge_eq_iff`：dart_edge_eq_iff : forall d₁ d₂ : G.Dart, 
d₁.edge = d₂.edge ↔ d₁ = d₂ ∨ d₁ = d₂.symm
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `SimpleGraph.Walk.IsPath.tail`：∀ {V : Type u} {G : SimpleGraph V} {u v : 
V} {p : G.Walk u v}, p.IsPath → p.tail.IsPath
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用引理 `SimpleGraph.Walk.length_tail_add_one`：length_tail_add_one {p : G.Walk u 
v} (hp : ¬ p.Nil) : p.tail.length + 1 = p.length
· 使用定理 `SimpleGraph.Walk.length_copy`：length_copy {u v u' v'} (p : G.Walk u v) (
hu : u = u') (hv : v = v') : (p.copy hu hv).length = p.length
· 使用定理 `le_of_not_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b 
→ b ≤ a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
（共 62 条，此处仅展示前 30 条）
-/
lemma IsTree.card_edgeFinset [Fintype V] [Fintype G.edgeSet] (hG : G.IsTree) :
    Finset.card G.edgeFinset + 1 = Fintype.card V := by
  have := hG.connected.nonempty
  inhabit V
  classical
  have : Finset.card ({default} : Finset V)ᶜ + 1 = Fintype.card V := by
    rw [Finset.card_compl, Finset.card_singleton, Nat.sub_add_cancel Fintype.card_pos]
  rw [← this, add_left_inj]
  choose f hf hf' using (hG.existsUnique_path · default)
  refine Eq.symm <| Finset.card_bij
          (fun w hw => ((f w).firstDart <| ?notNil).edge)
          (fun a ha => ?memEdges) ?inj ?surj
  case notNil => exact not_nil_of_ne (by simpa using hw)
  case memEdges => simp
  case inj =>
    intro a ha b hb h
    wlog h' : (f a).length ≤ (f b).length generalizing a b
    · exact Eq.symm (this _ hb _ ha h.symm (le_of_not_ge h'))
    rw [dart_edge_eq_iff] at h
    obtain (h | h) := h
    · exact (congrArg (·.fst) h)
    · have h1 : ((f a).firstDart <| not_nil_of_ne (by simpa using ha)).snd = b :=
        congrArg (·.snd) h
      have h3 := congrArg length (hf' _ ((f _).tail.copy h1 rfl) ?_)
      · rw [length_copy, ← add_left_inj 1,
          length_tail_add_one (not_nil_of_ne (by simpa using ha))] at h3
        lia
      · simp only [isPath_copy]
        exact (hf _).tail
  case surj =>
    simp only [mem_edgeFinset, Finset.mem_compl, Finset.mem_singleton, Sym2.forall, mem_edgeSet]
    intro x y h
    wlog h' : (f x).length ≤ (f y).length generalizing x y
    · rw [Sym2.eq_swap]
      exact this y x h.symm (le_of_not_ge h')
    refine ⟨y, ?_, dart_edge_eq_mk'_iff.2 <| Or.inr ?_⟩
    · rintro rfl
      rw [← hf' _ nil IsPath.nil, length_nil,
          ← hf' _ (.cons h .nil) (IsPath.nil.cons <| by simpa using h.ne),
          length_cons, length_nil] at h'
      simp at h'
    rw [← hf' _ (.cons h.symm (f x)) ((cons_isPath_iff _ _).2 ⟨hf _, fun hy => ?contra⟩)]
    · simp
    case contra =>
      suffices (f x).takeUntil y hy = .cons h .nil by
        rw [← take_spec _ hy] at h'
        simp [this, hf' _ _ ((hf _).dropUntil hy)] at h'
      refine (hG.existsUnique_path _ _).unique ((hf _).takeUntil _) ?_
      simp [h.ne]

/-- A minimally connected graph is a tree. -/
/-
**SimpleGraph.isTree_of_minimal_connected** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph
`。
形式化陈述：isTree_of_minimal_connected (h : Minimal Connected G) : IsTree G
参数：h : Minimal Connected G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.isTree_iff`：∀ {V : Type u_1} (G : SimpleGraph V), G.IsTree ↔
 G.Connected ∧ G.IsAcyclic
· 使用定理 `and_iff_right`：∀ {a b : Prop}, a → (a ∧ b ↔ b)
· 使用引理 `Minimal.prop`：Minimal.prop (h : Minimal P x) : P x
· 使用引理 `SimpleGraph.isAcyclic_iff_forall_adj_isBridge`：isAcyclic_iff_forall_adj_
isBridge : G.IsAcyclic ↔ forall ⦃v w : V⦄, G.Adj v w -> G.IsBridge s(v, w)
· 使用定理 `by_contra`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `Minimal.not_prop_of_lt`：Minimal.not_prop_of_lt (h : Minimal P x) (hlt : 
y < x) : ¬ P y
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `SimpleGraph.edgeSet_sdiff`：edgeSet_sdiff : (G₁ \ G₂).edgeSet = G₁.edgeSe
t \ G₂.edgeSet
· 使用定理 `SimpleGraph.edgeSet_fromEdgeSet`：edgeSet_fromEdgeSet : (fromEdgeSet s).e
dgeSet = s \ Sym2.diagSet
· 使用定理 `SimpleGraph.edgeSet_sdiff_sdiff_isDiag`：edgeSet_sdiff_sdiff_isDiag (G : 
SimpleGraph V) (s : Set (Sym2 V)) : G.edgeSet \ (s \ Sym2.diagSet) = G.edgeSet \
 s
· 使用定理 `SimpleGraph.Connected.connected_delete_edge_of_not_isBridge`：∀ {V : Type
 u} {G : SimpleGraph V}, G.Connected → ∀ {x y : V}, ¬G.IsBridge s(x, y) → (G.del
eteEdges {s(x, y)}).Connected

--- 原说明 ---
A minimally connected graph is a tree.
-/
lemma isTree_of_minimal_connected (h : Minimal Connected G) : IsTree G := by
  rw [isTree_iff, and_iff_right h.prop, isAcyclic_iff_forall_adj_isBridge]
  exact fun _ _ _ ↦ by_contra fun hbr ↦ h.not_prop_of_lt
    (by simpa [deleteEdges, ← edgeSet_ssubset_edgeSet])
    <| h.prop.connected_delete_edge_of_not_isBridge hbr

set_option backward.isDefEq.respectTransparency false in
/-
**SimpleGraph.isTree_iff_minimal_connected** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGrap
h`。
形式化陈述：isTree_iff_minimal_connected : IsTree G ↔ Minimal Connected G
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.IsTree.connected`：∀ {V : Type u_1} {G : SimpleGraph V}, G.Is
Tree → G.Connected
· 使用定理 `SimpleGraph.Connected.exists_isPath`：∀ {V : Type u} {G : SimpleGraph V},
 G.Connected → ∀ (u v : V), ∃ p, p.IsPath
· 使用定理 `SimpleGraph.Walk.IsPath.mapLe`：∀ {V : Type u} {G G' : SimpleGraph V} (h 
: G ≤ G') {u v : V} {p : G.Walk u v},   p.IsPath → (SimpleGraph.Walk.mapLe h p).
IsPath
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `SimpleGraph.IsAcyclic.subsingleton_path`：∀ {V : Type u_1} {G : SimpleGra
ph V}, G.IsAcyclic → ∀ (u v : V), Subsingleton (G.Path u v)
· 使用定理 `SimpleGraph.IsTree.isAcyclic`：∀ {V : Type u_1} {G : SimpleGraph V}, G.Is
Tree → G.IsAcyclic
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `SimpleGraph.Walk.adj_of_mem_edges`：adj_of_mem_edges {u v x y : V} (p : G
.Walk u v) (h : s(x, y) in p.edges) : G.Adj x y
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `SimpleGraph.Walk.edges_map`：edges_map : (p.map f).edges = p.edges.map (S
ym2.map f)
· 使用定理 `Sym2.map_id`：map_id : map (@id α) = id
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `List.map_id_fun`：∀ {α : Type u_1}, List.map id = id
· 使用定理 `SimpleGraph.Path.singleton_coe`：∀ {V : Type u} {G : SimpleGraph V} {u v 
: V} (h : G.Adj u v),   ↑(SimpleGraph.Path.singleton h) = SimpleGraph.Walk.cons 
h SimpleGraph.Walk.n…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用引理 `SimpleGraph.isTree_of_minimal_connected`：isTree_of_minimal_connected (h 
: Minimal Connected G) : IsTree G
-/
lemma isTree_iff_minimal_connected : IsTree G ↔ Minimal Connected G := by
  refine ⟨fun htree ↦ ⟨htree.connected, fun G' h' hle u v hadj ↦ ?_⟩, isTree_of_minimal_connected⟩
  have ⟨p, hp⟩ := h'.exists_isPath u v
  have := congrArg Walk.edges <| congrArg Subtype.val <|
    htree.isAcyclic.subsingleton_path u v |>.elim ⟨p.mapLe hle, hp.mapLe hle⟩ <| Path.singleton hadj
  simp only [edges_map, Hom.coe_ofLE, Sym2.map_id, List.map_id_fun, id_eq] at this
  simp [this, p.adj_of_mem_edges]

/-- Connecting two unreachable vertices by an edge preserves acyclicity. -/
/-
**SimpleGraph.IsAcyclic.sup_edge_of_not_reachable** 是 Mathlib 中的一个定理，位于命名空间 `Sim
pleGraph.IsAcyclic`。
形式化陈述：∀ {V : Type u_1} {G : SimpleGraph V} {u v : V}, ¬G.Reachable u v → G.IsAcy
clic → (G ⊔ SimpleGraph.edge u v).IsAcyclic
参数：G ⊔ SimpleGraph.edge u v。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Connecting two unreachable vertices by an edge preserves acyclicity.
-/
theorem IsAcyclic.sup_edge_of_not_reachable {u v : V} (hnreach : ¬G.Reachable u v)
    (hacyc : G.IsAcyclic) : (G ⊔ edge u v).IsAcyclic := by
  grind [isAcyclic_iff_forall_isBridge, IsBridge.sup_edge_of_not_reachable_of_isBridge,
    edgeSet_sup, edgeSet_edge, IsBridge.of_not_reachable, isBridge_sup_edge]

@[deprecated (since := "2026-03-18")]
alias IsAcyclic.isAcyclic_sup_fromEdgeSet_of_not_reachable := IsAcyclic.sup_edge_of_not_reachable
/-
**SimpleGraph.isAcyclic_add_edge_iff_of_not_reachable** 是 Mathlib 中的一个定理，位于命名空间 
`SimpleGraph`。
形式化陈述：isAcyclic_add_edge_iff_of_not_reachable (x y : V) (hxy : ¬ G.Reachable x y
) : (G ⊔ edge x y).IsAcyclic ↔ IsAcyclic G
参数：x y : V；hxy : ¬ G.Reachable x y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.IsAcyclic.anti`：∀ {V : Type u_1} {G G' : SimpleGraph V}, G ≤
 G' → G'.IsAcyclic → G.IsAcyclic
· 使用定理 `le_sup_left`：le_sup_left : a <= a ⊔ b
· 使用定理 `SimpleGraph.IsAcyclic.sup_edge_of_not_reachable`：∀ {V : Type u_1} {G : S
impleGraph V} {u v : V}, ¬G.Reachable u v → G.IsAcyclic → (G ⊔ SimpleGraph.edge 
u v).IsAcyclic
-/
theorem isAcyclic_add_edge_iff_of_not_reachable (x y : V) (hxy : ¬ G.Reachable x y) :
    (G ⊔ edge x y).IsAcyclic ↔ IsAcyclic G :=
  ⟨.anti le_sup_left, .sup_edge_of_not_reachable hxy⟩

/-- Adding an edge results in an acyclic graph iff the original graph was acyclic and
the edge connects vertices that previously had no path between them. -/
/-
**SimpleGraph.isAcyclic_sup_fromEdgeSet_iff** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGra
ph`。
形式化陈述：isAcyclic_sup_fromEdgeSet_iff {u v : V} : (G ⊔ edge u v).IsAcyclic ↔ G.IsA
cyclic ∧ (G.Reachable u v -> u = v ∨ G.Adj u v)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.IsAcyclic.anti`：∀ {V : Type u_1} {G G' : SimpleGraph V}, G ≤
 G' → G'.IsAcyclic → G.IsAcyclic
· 使用定理 `le_sup_left`：le_sup_left : a <= a ⊔ b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `SimpleGraph.isAcyclic_iff_forall_isBridge`：isAcyclic_iff_forall_isBridge
 : G.IsAcyclic ↔ forall ⦃e⦄, e in G.edgeSet -> G.IsBridge e where .elim .mpr fun
 v p hc => hG p hc mp hG e he
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.edgeSet_sup`：edgeSet_sup : (G₁ ⊔ G₂).edgeSet = G₁.edgeSet un
ion G₂.edgeSet
· 使用引理 `SimpleGraph.edgeSet_edge`：edgeSet_edge (v w : V) : (edge v w).edgeSet = 
{s(v, w)} \ Sym2.diagSet
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SimpleGraph.deleteEdges_sup`：∀ {V : Type u_1} (G H : SimpleGraph V) (s :
 Set (Sym2 V)), (G ⊔ H).deleteEdges s = G.deleteEdges s ⊔ H.deleteEdges s
· 使用定理 `SimpleGraph.deleteEdges_edge`：∀ {V : Type u_1} {u v : V} {s : Set (Sym2 
V)}, s(u, v) ∈ s → (SimpleGraph.edge u v).deleteEdges s = ⊥
· 使用定理 `sup_of_le_left`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, b ≤ 
a → a ⊔ b = a
· 使用定理 `SimpleGraph.IsAcyclic.sup_edge_of_not_reachable`：∀ {V : Type u_1} {G : S
impleGraph V} {u v : V}, ¬G.Reachable u v → G.IsAcyclic → (G ⊔ SimpleGraph.edge 
u v).IsAcyclic

--- 原说明 ---
Adding an edge results in an acyclic graph iff the original graph was acyclic an
d
the edge connects vertices that previously had no path between them.
-/
theorem isAcyclic_sup_fromEdgeSet_iff {u v : V} :
    (G ⊔ edge u v).IsAcyclic ↔
      G.IsAcyclic ∧ (G.Reachable u v → u = v ∨ G.Adj u v) := by
  by_cases huv : u = v
  · grind [sup_eq_left, edge_le, Sym2.mem_diagSet, Sym2.mk_isDiag_iff]
  by_cases hadj : G.Adj u v
  · grind [sup_eq_left, edge_le, mem_edgeSet]
  refine ⟨?_, fun ⟨hacyc, hreach⟩ ↦ hacyc.sup_edge_of_not_reachable <| by grind⟩
  refine fun hacyc ↦ ⟨hacyc.anti le_sup_left, fun hreach ↦ False.elim ?_⟩
  refine isAcyclic_iff_forall_isBridge.mp (e := s(u, v)) hacyc (by simp [huv]) ?_
  convert! hreach
  simp [deleteEdges_sup, hadj]

/--
The reachability relation of a maximal acyclic subgraph agrees with that of the larger graph.
-/
/-
**SimpleGraph.reachable_eq_of_maximal_isAcyclic** 是 Mathlib 中的一个引理，位于命名空间 `Simpl
eGraph`。
形式化陈述：reachable_eq_of_maximal_isAcyclic (F : SimpleGraph V) (h : Maximal (fun H 
=> H <= G ∧ H.IsAcyclic) F) : F.Reachable = G.Reachable
参数：F : SimpleGraph V；h : Maximal (fun H => H <= G ∧ H.IsAcyclic) F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `SimpleGraph.Reachable.mono`：∀ {V : Type u} {u v : V} {G G' : SimpleGraph
 V}, G ≤ G' → G.Reachable u v → G'.Reachable u v
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Maximal.prop`：∀ {α : Type u_1} [inst : LE α] {P : α → Prop} {x : α}, Max
imal P x → P x
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用引理 `SimpleGraph.ConnectedComponent.reachable_of_mem_supp`：reachable_of_mem_s
upp {G : SimpleGraph V} (C : G.ConnectedComponent) {u v : V} (hu : u in C.supp) 
(hv : v in C.supp) : G.Reachable u v
· 使用定理 `SimpleGraph.Walk.exists_boundary_dart`：exists_boundary_dart {u v : V} (p
 : G.Walk u v) (S : Set V) (uS : u in S) (vS : v ∉ S) : exists d : G.Dart, d in 
p.darts ∧ d.fst in S ∧ d.sn…
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `SimpleGraph.ConnectedComponent.sound`：∀ {V : Type u} {G : SimpleGraph V}
 {v w : V}, G.Reachable v w → G.connectedComponentMk v = G.connectedComponentMk 
w
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `SimpleGraph.ConnectedComponent.mem_supp_iff`：mem_supp_iff (C : G.Connect
edComponent) (v : V) : v in C.supp ↔ G.connectedComponentMk v = C
· 使用定理 `Maximal.le_of_ge`：∀ {α : Type u_1} [inst : LE α] {P : α → Prop} {x y : α
}, Maximal P x → P y → x ≤ y → y ≤ x
· 使用定理 `SimpleGraph.IsAcyclic.sup_edge_of_not_reachable`：∀ {V : Type u_1} {G : S
impleGraph V} {u v : V}, ¬G.Reachable u v → G.IsAcyclic → (G ⊔ SimpleGraph.edge 
u v).IsAcyclic
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `le_sup_left`：le_sup_left : a <= a ⊔ b

--- 原说明 ---
The reachability relation of a maximal acyclic subgraph agrees with that of the 
larger graph.
-/
lemma reachable_eq_of_maximal_isAcyclic (F : SimpleGraph V)
    (h : Maximal (fun H ↦ H ≤ G ∧ H.IsAcyclic) F) : F.Reachable = G.Reachable := by
  ext u v
  refine ⟨.mono h.prop.left, fun ⟨p⟩ ↦ ?_⟩
  by_contra
  let s : F.ConnectedComponent := .mk _ u
  have : v ∉ s := this ∘ s.reachable_of_mem_supp rfl
  have : ∃ d ∈ p.darts, d.fst ∈ s ∧ d.snd ∉ s := p.exists_boundary_dart s rfl this
  rcases this with ⟨⟨⟨u', v'⟩, huv⟩, _, hu, hv⟩
  have : ¬F.Reachable v' u' := mt ConnectedComponent.sound <| s.mem_supp_iff u' |>.mp hu ▸ hv
  suffices F ⊔ edge v' u' ≤ F by grind [Adj.reachable, sup_le_iff, le_iff_adj]
  refine h.le_of_ge ⟨?_, h.prop.right.sup_edge_of_not_reachable this⟩ le_sup_left
  grind [Maximal, sup_le, le_iff_adj, huv.symm]

/-- A subgraph is maximal acyclic iff its reachability relation agrees with the larger graph. -/
/-
**SimpleGraph.maximal_isAcyclic_iff_reachable_eq** 是 Mathlib 中的一个定理，位于命名空间 `Simp
leGraph`。
形式化陈述：maximal_isAcyclic_iff_reachable_eq {F : SimpleGraph V} (hle : F <= G) (hF 
: F.IsAcyclic) : Maximal (fun F => F <= G ∧ F.IsAcyclic) F ↔ F.Reachable = G.Rea
chable
参数：hle : F <= G；hF : F.IsAcyclic。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SimpleGraph.reachable_eq_of_maximal_isAcyclic`：reachable_eq_of_maximal_i
sAcyclic (F : SimpleGraph V) (h : Maximal (fun H => H <= G ∧ H.IsAcyclic) F) : F
.Reachable = G.Reachable
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `exists_gt_of_not_maximal`：∀ {α : Type u_2} {P : α → Prop} {x : α} [inst 
: Preorder α], P x → ¬Maximal P x → ∃ y, x < y ∧ P y
· 使用定理 `Set.exists_of_ssubset`：exists_of_ssubset {s t : Set α} (h : s ⊂ t) : exi
sts x in t, x ∉ s
· 使用定理 `SimpleGraph.edgeSet_strict_mono`：∀ {V : Type u} {G₁ G₂ : SimpleGraph V},
 G₁ < G₂ → G₁.edgeSet ⊂ G₂.edgeSet
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `SimpleGraph.isAcyclic_iff_forall_isBridge`：isAcyclic_iff_forall_isBridge
 : G.IsAcyclic ↔ forall ⦃e⦄, e in G.edgeSet -> G.IsBridge e where .elim .mpr fun
 v p hc => hG p hc mp hG e he
· 使用定理 `SimpleGraph.IsAcyclic.anti`：∀ {V : Type u_1} {G G' : SimpleGraph V}, G ≤
 G' → G'.IsAcyclic → G.IsAcyclic
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `sup_le_iff`：sup_le_iff : a ⊔ b <= c ↔ a <= c ∧ b <= c
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `SimpleGraph.fromEdgeSet_le`：∀ {V : Type u} (G : SimpleGraph V) {s : Set 
(Sym2 V)}, SimpleGraph.fromEdgeSet s ≤ G ↔ s \ Sym2.diagSet ⊆ G.edgeSet
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.edgeSet_sup`：edgeSet_sup : (G₁ ⊔ G₂).edgeSet = G₁.edgeSet un
ion G₂.edgeSet
· 使用定理 `SimpleGraph.edgeSet_fromEdgeSet`：edgeSet_fromEdgeSet : (fromEdgeSet s).e
dgeSet = s \ Sym2.diagSet
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `SimpleGraph.not_isDiag_of_mem_edgeSet`：not_isDiag_of_mem_edgeSet : e in 
edgeSet G -> ¬e.IsDiag
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `SimpleGraph.deleteEdges_sup`：∀ {V : Type u_1} (G H : SimpleGraph V) (s :
 Set (Sym2 V)), (G ⊔ H).deleteEdges s = G.deleteEdges s ⊔ H.deleteEdges s
· 使用定理 `SimpleGraph.deleteEdges_fromEdgeSet`：∀ {V : Type u_1} (s t : Set (Sym2 V
)), (SimpleGraph.fromEdgeSet s).deleteEdges t = SimpleGraph.fromEdgeSet (s \ t)
· 使用定理 `sdiff_self`：∀ {α : Type u_2} [inst : GeneralizedCoheytingAlgebra α] {a :
 α}, a \ a = ⊥
· 使用定理 `SimpleGraph.fromEdgeSet_empty`：fromEdgeSet_empty : fromEdgeSet (∅ : Set 
(Sym2 V)) = ⊥
· 使用定理 `sup_of_le_left`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, b ≤ 
a → a ⊔ b = a
（共 34 条，此处仅展示前 30 条）

--- 原说明 ---
A subgraph is maximal acyclic iff its reachability relation agrees with the larg
er graph.
-/
theorem maximal_isAcyclic_iff_reachable_eq {F : SimpleGraph V} (hle : F ≤ G) (hF : F.IsAcyclic) :
    Maximal (fun F ↦ F ≤ G ∧ F.IsAcyclic) F ↔ F.Reachable = G.Reachable := by
  refine ⟨reachable_eq_of_maximal_isAcyclic F, fun h ↦ ?_⟩
  by_contra
  have ⟨H, hFH, hHG, hH⟩ := exists_gt_of_not_maximal ⟨hle, hF⟩ this
  have ⟨e, heH, heF⟩ := Set.exists_of_ssubset <| edgeSet_strict_mono hFH
  have h_bridge : (F ⊔ fromEdgeSet {e}).IsBridge e := by
    refine isAcyclic_iff_forall_isBridge.mp ?_ <| by simp [H.not_isDiag_of_mem_edgeSet heH]
    exact hH.anti <| sup_le_iff.mpr ⟨hFH.le, H.fromEdgeSet_le.mpr <| by grind⟩
  have : (F ⊔ fromEdgeSet {e}).deleteEdges {e} = F := by simpa using heF
  cases e
  rw [isBridge_iff, this, h] at h_bridge
  exact h_bridge <| hHG heH |>.reachable

/-- A subgraph of a connected graph is maximal acyclic iff it is a tree. -/
/-
**SimpleGraph.Connected.maximal_le_isAcyclic_iff_isTree** 是 Mathlib 中的一个定理，位于命名空
间 `SimpleGraph.Connected`。
形式化陈述：∀ {V : Type u_1} {G T : SimpleGraph V}, G.Connected → T ≤ G → (Maximal (fu
n H => H ≤ G ∧ H.IsAcyclic) T ↔ T.IsTree)
参数：Maximal (fun H => H ≤ G ∧ H.IsAcyclic) T ↔ T.IsTree。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Connected.nonempty`：∀ {V : Type u} {G : SimpleGraph V}, G.Co
nnected → Nonempty V
· 使用定理 `SimpleGraph.Connected.preconnected`：∀ {V : Type u} {G : SimpleGraph V}, 
G.Connected → G.Preconnected
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `SimpleGraph.reachable_eq_of_maximal_isAcyclic`：reachable_eq_of_maximal_i
sAcyclic (F : SimpleGraph V) (h : Maximal (fun H => H <= G ∧ H.IsAcyclic) F) : F
.Reachable = G.Reachable
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.maximal_isAcyclic_iff_reachable_eq`：maximal_isAcyclic_iff_re
achable_eq {F : SimpleGraph V} (hle : F <= G) (hF : F.IsAcyclic) : Maximal (fun 
F => F <= G ∧ F.IsAcyclic) F ↔ F.Rea…
· 使用定理 `SimpleGraph.IsTree.isAcyclic`：∀ {V : Type u_1} {G : SimpleGraph V}, G.Is
Tree → G.IsAcyclic
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `SimpleGraph.preconnected_iff_reachable_eq_top`：preconnected_iff_reachabl
e_eq_top : G.Preconnected ↔ G.Reachable = ⊤
· 使用定理 `SimpleGraph.IsTree.connected`：∀ {V : Type u_1} {G : SimpleGraph V}, G.Is
Tree → G.Connected

--- 原说明 ---
A subgraph of a connected graph is maximal acyclic iff it is a tree.
-/
theorem Connected.maximal_le_isAcyclic_iff_isTree {T : SimpleGraph V} (hG : G.Connected)
    (hT : T ≤ G) : Maximal (fun H ↦ H ≤ G ∧ H.IsAcyclic) T ↔ T.IsTree := by
  have := hG.nonempty
  refine ⟨fun h ↦ ⟨⟨fun u v ↦ ?_⟩, h.1.2⟩, fun hT' ↦ ?_⟩
  · exact G.reachable_eq_of_maximal_isAcyclic T h ▸ hG.preconnected u v
  · rw [maximal_isAcyclic_iff_reachable_eq hT hT'.isAcyclic,
      T.preconnected_iff_reachable_eq_top.mp hT'.preconnected,
      G.preconnected_iff_reachable_eq_top.mp hG.preconnected]

@[simp]
/-
**SimpleGraph.maximal_isAcyclic_iff_isTree** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGrap
h`。
形式化陈述：maximal_isAcyclic_iff_isTree [Nonempty V] {T : SimpleGraph V} : Maximal Is
Acyclic T ↔ T.IsTree
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SimpleGraph.Connected.maximal_le_isAcyclic_iff_isTree`：∀ {V : Type u_1} 
{G T : SimpleGraph V}, G.Connected → T ≤ G → (Maximal (fun H => H ≤ G ∧ H.IsAcyc
lic) T ↔ T.IsTree)
· 使用定理 `SimpleGraph.connected_top`：∀ {V : Type u} [Nonempty V], (SimpleGraph.com
pleteGraph V).Connected
· 使用定理 `le_top`：le_top : a <= ⊤
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem maximal_isAcyclic_iff_isTree [Nonempty V] {T : SimpleGraph V} :
    Maximal IsAcyclic T ↔ T.IsTree := by
  simp [← connected_top.maximal_le_isAcyclic_iff_isTree le_top]

/-- A maximally acyclic graph is a tree. This is similar to `maximal_isAcyclic_iff_isTree` except
with `Nonempty V` as part of the iff rather than an assumption. -/
/-
**SimpleGraph.isTree_iff_maximal_isAcyclic** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGrap
h`。
形式化陈述：isTree_iff_maximal_isAcyclic : G.IsTree ↔ Nonempty V ∧ Maximal IsAcyclic G
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Connected.nonempty`：∀ {V : Type u} {G : SimpleGraph V}, G.Co
nnected → Nonempty V
· 使用定理 `SimpleGraph.IsTree.connected`：∀ {V : Type u_1} {G : SimpleGraph V}, G.Is
Tree → G.Connected
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `SimpleGraph.maximal_isAcyclic_iff_isTree`：maximal_isAcyclic_iff_isTree [
Nonempty V] {T : SimpleGraph V} : Maximal IsAcyclic T ↔ T.IsTree
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b

--- 原说明 ---
A maximally acyclic graph is a tree. This is similar to `maximal_isAcyclic_iff_i
sTree` except
with `Nonempty V` as part of the iff rather than an assumption.
-/
theorem isTree_iff_maximal_isAcyclic : G.IsTree ↔ Nonempty V ∧ Maximal IsAcyclic G := by
  refine ⟨fun h ↦ ?_, fun ⟨_, h⟩ ↦ G.maximal_isAcyclic_iff_isTree.mp h⟩
  have := h.nonempty
  exact ⟨this, G.maximal_isAcyclic_iff_isTree.mpr h⟩

/-- Every acyclic subgraph can be extended to a spanning forest. -/
/-
**SimpleGraph.exists_isAcyclic_reachable_eq_le_of_le_of_isAcyclic** 是 Mathlib 中的
一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：exists_isAcyclic_reachable_eq_le_of_le_of_isAcyclic {H : SimpleGraph V} (h
H_le : H <= G) (hH_isAcyclic : H.IsAcyclic) : exists F : SimpleGraph V, H <= F ∧
 F <= G ∧ F.IsAcyclic ∧ F.Reachable = G.Reachable
参数：hH_le : H <= G；hH_isAcyclic : H.IsAcyclic。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.exists_maximal_isAcyclic_of_le_isAcyclic`：exists_maximal_isA
cyclic_of_le_isAcyclic {H : SimpleGraph V} (hHG : H <= G) (hH : H.IsAcyclic) : e
xists H' : SimpleGraph V, H <= H' ∧ Maxima…

--- 原说明 ---
Every acyclic subgraph can be extended to a spanning forest.
-/
theorem exists_isAcyclic_reachable_eq_le_of_le_of_isAcyclic {H : SimpleGraph V} (hH_le : H ≤ G)
    (hH_isAcyclic : H.IsAcyclic) :
    ∃ F : SimpleGraph V, H ≤ F ∧ F ≤ G ∧ F.IsAcyclic ∧ F.Reachable = G.Reachable := by
  obtain ⟨F, hF⟩ := G.exists_maximal_isAcyclic_of_le_isAcyclic hH_le hH_isAcyclic
  grind [maximal_isAcyclic_iff_reachable_eq, Maximal]

/-- Every graph has a spanning forest. -/
/-
**SimpleGraph.exists_isAcyclic_reachable_eq_le** 是 Mathlib 中的一个定理，位于命名空间 `Simple
Graph`。
形式化陈述：exists_isAcyclic_reachable_eq_le : exists F <= G, F.IsAcyclic ∧ F.Reachabl
e = G.Reachable
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.exists_isAcyclic_reachable_eq_le_of_le_of_isAcyclic`：exists_
isAcyclic_reachable_eq_le_of_le_of_isAcyclic {H : SimpleGraph V} (hH_le : H <= G
) (hH_isAcyclic : H.IsAcyclic) : exists F : SimpleGra…
· 使用定理 `bot_le`：∀ {α : Type u} [inst : LE α] [inst_1 : OrderBot α] {a : α}, ⊥ ≤ 
a
· 使用定理 `SimpleGraph.isAcyclic_bot`：∀ {V : Type u_1}, ⊥.IsAcyclic

--- 原说明 ---
Every graph has a spanning forest.
-/
theorem exists_isAcyclic_reachable_eq_le :
    ∃ F ≤ G, F.IsAcyclic ∧ F.Reachable = G.Reachable := by
  obtain ⟨F, hF⟩ := G.exists_isAcyclic_reachable_eq_le_of_le_of_isAcyclic bot_le isAcyclic_bot
  grind

/-- Every acyclic subgraph of a connected graph can be extended to a spanning tree. -/
/-
**SimpleGraph.Connected.exists_isTree_le_of_le_of_isAcyclic** 是 Mathlib 中的一个定理，位
于命名空间 `SimpleGraph.Connected`。
形式化陈述：∀ {V : Type u_1} {G H : SimpleGraph V}, G.Connected → H ≤ G → H.IsAcyclic 
→ ∃ F, H ≤ F ∧ F ≤ G ∧ F.IsTree
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.exists_isAcyclic_reachable_eq_le_of_le_of_isAcyclic`：exists_
isAcyclic_reachable_eq_le_of_le_of_isAcyclic {H : SimpleGraph V} (hH_le : H <= G
) (hH_isAcyclic : H.IsAcyclic) : exists F : SimpleGra…

--- 原说明 ---
Every acyclic subgraph of a connected graph can be extended to a spanning tree.
-/
lemma Connected.exists_isTree_le_of_le_of_isAcyclic {H : SimpleGraph V} (h : G.Connected)
    (hH_le : H ≤ G) (hH_isAcyclic : H.IsAcyclic) :
    ∃ F : SimpleGraph V, H ≤ F ∧ F ≤ G ∧ F.IsTree := by
  obtain ⟨F, hF⟩ := G.exists_isAcyclic_reachable_eq_le_of_le_of_isAcyclic hH_le hH_isAcyclic
  grind [IsTree, Connected, preconnected_iff_reachable_eq_top]

/-- Every connected graph has a spanning tree. -/
/-
**SimpleGraph.Connected.exists_isTree_le** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.
Connected`。
形式化陈述：∀ {V : Type u_1} {G : SimpleGraph V}, G.Connected → ∃ T ≤ G, T.IsTree
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.exists_isAcyclic_reachable_eq_le_of_le_of_isAcyclic`：exists_
isAcyclic_reachable_eq_le_of_le_of_isAcyclic {H : SimpleGraph V} (hH_le : H <= G
) (hH_isAcyclic : H.IsAcyclic) : exists F : SimpleGra…
· 使用定理 `bot_le`：∀ {α : Type u} [inst : LE α] [inst_1 : OrderBot α] {a : α}, ⊥ ≤ 
a
· 使用定理 `SimpleGraph.isAcyclic_bot`：∀ {V : Type u_1}, ⊥.IsAcyclic

--- 原说明 ---
Every connected graph has a spanning tree.
-/
lemma Connected.exists_isTree_le (h : G.Connected) : ∃ T ≤ G, IsTree T := by
  obtain ⟨F, hF⟩ := G.exists_isAcyclic_reachable_eq_le_of_le_of_isAcyclic bot_le isAcyclic_bot
  grind [IsTree, Connected, preconnected_iff_reachable_eq_top]

/-- Every connected graph on `n` vertices has at least `n-1` edges. -/
/-
**SimpleGraph.Connected.card_vert_le_card_edgeSet_add_one** 是 Mathlib 中的一个定理，位于命
名空间 `SimpleGraph.Connected`。
形式化陈述：∀ {V : Type u_1} {G : SimpleGraph V}, G.Connected → Nat.card V ≤ Nat.card 
↑G.edgeSet + 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.symm`：∀ {a b : Prop}, a ∨ b → b ∨ a
· 使用定理 `finite_or_infinite`：finite_or_infinite (α : Sort*) : Finite α ∨ Infinite
 α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.card_eq_zero_of_infinite`：∀ {α : Type u_1} [Infinite α], Nat.card α 
= 0
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsRightCancelAdd.addRightReflectLE_of_addRightReflectLT`：∀ (N : Type u_2
) [inst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightReflect
LT N],   AddRightReflectLE N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `contravariant_swap_add_of_contravariant_add`：∀ (N : Type u_2) (r : N → N
 → Prop) [inst : AddCommSemigroup N] [ContravariantClass N N (fun x1 x2 => x1 + 
x2) r],   ContravariantClass N N …
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `SimpleGraph.Connected.exists_isTree_le`：∀ {V : Type u_1} {G : SimpleGrap
h V}, G.Connected → ∃ T ≤ G, T.IsTree
· 使用定理 `Nat.card_eq_fintype_card`：card_eq_fintype_card [Fintype α] : Nat.card α 
= Fintype.card α
· 使用定理 `Finite.instProd`：∀ {α : Type u_1} {β : Type u_2} [Finite α] [Finite β], 
Finite (α × β)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SimpleGraph.IsTree.card_edgeFinset`：∀ {V : Type u_1} {G : SimpleGraph V}
 [inst : Fintype V] [inst_1 : Fintype ↑G.edgeSet],   G.IsTree → G.edgeFinset.car
d + 1 = Fintype.card V
· 使用定理 `add_le_add_iff_right`：∀ {α : Type u_1} [inst : Add α] [inst_1 : LE α] [A
ddRightMono α] [AddRightReflectLE α] (a : α) {b c : α},   b + a ≤ c + a ↔ b ≤ c
· 使用定理 `SimpleGraph.edgeFinset_card`：edgeFinset_card : #G.edgeFinset = Fintype.c
ard G.edgeSet
· 使用定理 `Finset.card_mono`：card_mono : Monotone (@card α)

--- 原说明 ---
Every connected graph on `n` vertices has at least `n-1` edges.
-/
lemma Connected.card_vert_le_card_edgeSet_add_one (h : G.Connected) :
    Nat.card V ≤ Nat.card G.edgeSet + 1 := by
  obtain hV | hV := (finite_or_infinite V).symm
  · simp
  have := Fintype.ofFinite
  obtain ⟨T, hle, hT⟩ := h.exists_isTree_le
  rw [Nat.card_eq_fintype_card, ← hT.card_edgeFinset, add_le_add_iff_right,
    Nat.card_eq_fintype_card, ← edgeFinset_card]
  exact Finset.card_mono <| by simpa

set_option backward.isDefEq.respectTransparency.types false in
/-
**SimpleGraph.isTree_iff_connected_and_card** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGra
ph`。
形式化陈述：isTree_iff_connected_and_card [Finite V] : G.IsTree ↔ G.Connected ∧ Nat.ca
rd G.edgeSet + 1 = Nat.card V
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.IsTree.connected`：∀ {V : Type u_1} {G : SimpleGraph V}, G.Is
Tree → G.Connected
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.card_eq_fintype_card`：card_eq_fintype_card [Fintype α] : Nat.card α 
= Fintype.card α
· 使用定理 `Fintype.card_ofFinset`：card_ofFinset {p : Set α} (s : Finset α) (H : for
all x, x in s ↔ x in p) : @Fintype.card p (ofFinset s H) = #s
· 使用定理 `Set.toFinset_card`：toFinset_card {α : Type*} (s : Set α) [Fintype s] : s
.toFinset.card = Fintype.card s
· 使用定理 `SimpleGraph.IsTree.card_edgeFinset`：∀ {V : Type u_1} {G : SimpleGraph V}
 [inst : Fintype V] [inst_1 : Fintype ↑G.edgeSet],   G.IsTree → G.edgeFinset.car
d + 1 = Fintype.card V
· 使用定理 `by_contra`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `LE.le.not_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ≤ b → ¬b
 < a
· 使用定理 `SimpleGraph.Connected.card_vert_le_card_edgeSet_add_one`：∀ {V : Type u_1
} {G : SimpleGraph V}, G.Connected → Nat.card V ≤ Nat.card ↑G.edgeSet + 1
· 使用定理 `SimpleGraph.Connected.connected_delete_edge_of_not_isBridge`：∀ {V : Type
 u} {G : SimpleGraph V}, G.Connected → ∀ {x y : V}, ¬G.IsBridge s(x, y) → (G.del
eteEdges {s(x, y)}).Connected
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SimpleGraph.edgeFinset_card`：edgeFinset_card : #G.edgeFinset = Fintype.c
ard G.edgeSet
· 使用定理 `add_lt_add_iff_right`：∀ {α : Type u_1} [inst : Add α] [inst_1 : LT α] [A
ddRightStrictMono α] [AddRightReflectLT α] (a : α) {b c : α},   b + a < c + a ↔ 
b < c
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `contravariant_swap_add_of_contravariant_add`：∀ (N : Type u_2) (r : N → N
 → Prop) [inst : AddCommSemigroup N] [ContravariantClass N N (fun x1 x2 => x1 + 
x2) r],   ContravariantClass N N …
· 使用定理 `Finset.card_lt_card`：∀ {α : Type u_1} {s t : Finset α}, s ⊂ t → s.card <
 t.card
· 使用定理 `Set.toFinset_congr`：toFinset_congr {s t : Set α} [Fintype s] [Fintype t]
 (h : s = t) : toFinset s = toFinset t
· 使用定理 `SimpleGraph.edgeSet_sdiff`：edgeSet_sdiff : (G₁ \ G₂).edgeSet = G₁.edgeSe
t \ G₂.edgeSet
· 使用定理 `SimpleGraph.edgeSet_fromEdgeSet`：edgeSet_fromEdgeSet : (fromEdgeSet s).e
dgeSet = s \ Sym2.diagSet
· 使用定理 `SimpleGraph.edgeSet_sdiff_sdiff_isDiag`：edgeSet_sdiff_sdiff_isDiag (G : 
SimpleGraph V) (s : Set (Sym2 V)) : G.edgeSet \ (s \ Sym2.diagSet) = G.edgeSet \
 s
· 使用定理 `Set.toFinset_sdiff`：toFinset_sdiff [Fintype (s \ t : Set _)] : (s \ t).t
oFinset = s.toFinset \ t.toFinset
（共 34 条，此处仅展示前 30 条）
-/
lemma isTree_iff_connected_and_card [Finite V] :
    G.IsTree ↔ G.Connected ∧ Nat.card G.edgeSet + 1 = Nat.card V := by
  have := Fintype.ofFinite V
  classical
  refine ⟨fun h ↦ ⟨h.connected, by simpa [edgeFinset] using h.card_edgeFinset⟩,
    fun ⟨h₁, h₂⟩ ↦ ⟨h₁, ?_⟩⟩
  simp_rw [isAcyclic_iff_forall_adj_isBridge]
  refine fun x y h ↦ by_contra fun hbr ↦
    (h₁.connected_delete_edge_of_not_isBridge hbr).card_vert_le_card_edgeSet_add_one.not_gt ?_
  rw [Nat.card_eq_fintype_card, ← edgeFinset_card, ← h₂, Nat.card_eq_fintype_card,
    ← edgeFinset_card, add_lt_add_iff_right]
  exact Finset.card_lt_card <| by simpa [deleteEdges, edgeFinset]

/-- The minimum degree of all vertices in a nontrivial tree is one. -/
/-
**SimpleGraph.IsTree.minDegree_eq_one_of_nontrivial** 是 Mathlib 中的一个定理，位于命名空间 `S
impleGraph.IsTree`。
形式化陈述：∀ {V : Type u_1} {G : SimpleGraph V},   G.IsTree → ∀ [inst : Fintype V] [N
ontrivial V] [inst_2 : DecidableRel G.Adj], G.minDegree = 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.IsTree.card_edgeFinset`：∀ {V : Type u_1} {G : SimpleGraph V}
 [inst : Fintype V] [inst_1 : Fintype ↑G.edgeSet],   G.IsTree → G.edgeFinset.car
d + 1 = Fintype.card V
· 使用定理 `SimpleGraph.sum_degrees_eq_twice_card_edges`：sum_degrees_eq_twice_card_e
dges : ∑ v, G.degree v = 2 * #G.edgeFinset
· 使用定理 `Finset.sum_le_sum`：∀ {ι : Type u_1} {N : Type u_5} [inst : AddCommMonoid
 N] [inst_1 : Preorder N] {f g : ι → N} {s : Finset ι}   [AddLeftMono N], (∀ i ∈
 s, f i…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `SimpleGraph.minDegree_le_degree`：minDegree_le_degree [DecidableRel G.Adj
] (v : V) : G.minDegree <= G.degree v
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用定理 `Finset.card_univ`：Finset.card_univ [Fintype α] : #(univ : Finset α) = Fi
ntype.card α
· 使用定理 `Finset.sum_const`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst :
 AddCommMonoid M] (b : M), ∑ _x ∈ s, b = s.card • b
· 使用定理 `SimpleGraph.Preconnected.minDegree_pos_of_nontrivial`：∀ {V : Type u} [No
ntrivial V] [inst : Fintype V] {G : SimpleGraph V} [inst_1 : DecidableRel G.Adj]
,   G.Preconnected → 0 < G.minDegree
· 使用定理 `SimpleGraph.Connected.preconnected`：∀ {V : Type u} {G : SimpleGraph V}, 
G.Connected → G.Preconnected
· 使用定理 `SimpleGraph.IsTree.connected`：∀ {V : Type u_1} {G : SimpleGraph V}, G.Is
Tree → G.Connected

--- 原说明 ---
The minimum degree of all vertices in a nontrivial tree is one.
-/
lemma IsTree.minDegree_eq_one_of_nontrivial (h : G.IsTree) [Fintype V] [Nontrivial V]
    [DecidableRel G.Adj] : G.minDegree = 1 := by
  by_cases q : 2 ≤ G.minDegree
  · have := h.card_edgeFinset
    have := G.sum_degrees_eq_twice_card_edges
    have hle : ∑ v : V, 2 ≤ ∑ v, G.degree v := by
      gcongr
      exact le_trans q (G.minDegree_le_degree _)
    rw [Finset.sum_const, Finset.card_univ, smul_eq_mul] at hle
    lia
  · have := h.preconnected.minDegree_pos_of_nontrivial
    lia

/-- A nontrivial tree has a vertex of degree one. -/
/-
**SimpleGraph.IsTree.exists_vert_degree_one_of_nontrivial** 是 Mathlib 中的一个定理，位于命
名空间 `SimpleGraph.IsTree`。
形式化陈述：∀ {V : Type u_1} {G : SimpleGraph V} [inst : Fintype V] [Nontrivial V] [in
st_2 : DecidableRel G.Adj],   G.IsTree → ∃ v, G.degree v = 1
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A nontrivial tree has a vertex of degree one.
-/
lemma IsTree.exists_vert_degree_one_of_nontrivial [Fintype V] [Nontrivial V] [DecidableRel G.Adj]
    (h : G.IsTree) : ∃ v, G.degree v = 1 := by
  grind [G.exists_minimal_degree_vertex, minDegree_eq_one_of_nontrivial]

/-- A nontrivial finite tree has at least two leaves. -/
/-
**SimpleGraph.IsTree.exists_ne_and_degree_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `Simp
leGraph.IsTree`。
形式化陈述：∀ {V : Type u_1} {G : SimpleGraph V} [Nontrivial V] [Finite ↑G.edgeSet] [i
nst : G.LocallyFinite],   G.IsTree → ∃ u v, u ≠ v ∧ G.degree u = 1 ∧ G.degree v 
= 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SimpleGraph.Walk.exists_isPath_forall_isPath_length_le_length`：exists_is
Path_forall_isPath_length_le_length (G : SimpleGraph V) [N : Nonempty V] [Finite
 G.edgeSet] : exists (u v : V) (p : G.Walk u v) (_ …
· 使用定理 `Nontrivial.to_nonempty`：∀ {α : Type u_1} [Nontrivial α], Nonempty α
· 使用定理 `exists_pair_ne`：exists_pair_ne (α : Type*) [Nontrivial α] : exists x y :
 α, x != y
· 使用定理 `SimpleGraph.Connected.exists_isPath`：∀ {V : Type u} {G : SimpleGraph V},
 G.Connected → ∀ (u v : V), ∃ p, p.IsPath
· 使用定理 `SimpleGraph.IsTree.connected`：∀ {V : Type u_1} {G : SimpleGraph V}, G.Is
Tree → G.Connected
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `SimpleGraph.Walk.IsPath.nil_iff_eq`：∀ {V : Type u} {G : SimpleGraph V} {
u v : V} {p : G.Walk u v}, p.IsPath → (p.Nil ↔ u = v)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.degree_eq_one_iff_existsUnique_adj`：degree_eq_one_iff_exists
Unique_adj {G : SimpleGraph V} {v : V} [Fintype (G.neighborSet v)] : G.degree v 
= 1 ↔ exists! w : V, G.Adj v w
· 使用定理 `SimpleGraph.Walk.adj_snd`：∀ {V : Type u} {G : SimpleGraph V} {v w : V} {
p : G.Walk v w}, ¬p.Nil → G.Adj v p.snd
· 使用定理 `SimpleGraph.IsAcyclic.eq_snd_of_adj_start`：∀ {V : Type u_1} {G : SimpleG
raph V},   G.IsAcyclic → ∀ {u v w : V} {p : G.Walk u v}, p.IsPath → G.Adj u w → 
w ∈ p.support → w = p.snd
· 使用定理 `SimpleGraph.IsTree.isAcyclic`：∀ {V : Type u_1} {G : SimpleGraph V}, G.Is
Tree → G.IsAcyclic
· 使用定理 `SimpleGraph.Adj.symm`：∀ {V : Type u} {G : SimpleGraph V} {u v : V}, G.Ad
j u v → G.Adj v u
· 使用引理 `SimpleGraph.Walk.adj_penultimate`：adj_penultimate {p : G.Walk v w} (hp :
 ¬ p.Nil) : G.Adj p.penultimate w
· 使用定理 `SimpleGraph.IsAcyclic.eq_penultimate_of_adj_end`：∀ {V : Type u_1} {G : S
impleGraph V},   G.IsAcyclic → ∀ {u v w : V} {p : G.Walk u v}, p.IsPath → G.Adj 
v w → w ∈ p.support → w = p.penultima…

--- 原说明 ---
A nontrivial finite tree has at least two leaves.
-/
theorem IsTree.exists_ne_and_degree_eq_one [Nontrivial V] [Finite G.edgeSet] [G.LocallyFinite]
    (h : G.IsTree) : ∃ u v, u ≠ v ∧ G.degree u = 1 ∧ G.degree v = 1 := by
  have ⟨u, v, p, hp, hmax⟩ := exists_isPath_forall_isPath_length_le_length G
  have ⟨u', v', hne⟩ := exists_pair_ne V
  have ⟨p', hp'⟩ := h.connected.exists_isPath u' v'
  have hnil : ¬p.Nil := by grind
  refine ⟨u, v, hp.nil_iff_eq.not.mp hnil, ?_, ?_⟩ <;>
    rw [degree_eq_one_iff_existsUnique_adj]
  · refine ⟨_, p.adj_snd hnil, fun w hadj ↦ ?_⟩
    apply h.isAcyclic.eq_snd_of_adj_start hp hadj
    have : ¬(p.cons hadj.symm).IsPath := by grind [length_cons]
    grind [hp.cons]
  · refine ⟨_, p.adj_penultimate hnil |>.symm, fun w hadj ↦ ?_⟩
    apply h.isAcyclic.eq_penultimate_of_adj_end hp hadj
    have : ¬(p.concat hadj).IsPath := by grind [length_concat]
    grind [hp.concat]

/-- The graph resulting from removing a vertex of degree one from a connected graph is connected. -/
/-
**SimpleGraph.Connected.induce_compl_singleton_of_degree_eq_one** 是 Mathlib 中的一个
定理，位于命名空间 `SimpleGraph.Connected`。
形式化陈述：∀ {V : Type u_1} {G : SimpleGraph V},   G.Connected → ∀ {v : V} [inst : Fi
ntype ↑(G.neighborSet v)], G.degree v = 1 → (SimpleGraph.induce {v}ᶜ G).Connecte
d
参数：G.neighborSet v；SimpleGraph.induce {v}ᶜ G。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `SimpleGraph.degree_eq_one_iff_existsUnique_adj`：degree_eq_one_iff_exists
Unique_adj {G : SimpleGraph V} {v : V} [Fintype (G.neighborSet v)] : G.degree v 
= 1 ↔ exists! w : V, G.Adj v w
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `SimpleGraph.connected_iff`：∀ {V : Type u} (G : SimpleGraph V), G.Connect
ed ↔ G.Preconnected ∧ Nonempty V
· 使用定理 `SimpleGraph.Connected.exists_isPath`：∀ {V : Type u} {G : SimpleGraph V},
 G.Connected → ∀ (u v : V), ∃ p, p.IsPath
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.Reachable.eq_1`：∀ {V : Type u} (G : SimpleGraph V) (u v : V)
, G.Reachable u v = Nonempty (G.Walk u v)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `exists_true_iff_nonempty`：exists_true_iff_nonempty {α : Sort*} : (exists
 _ : α, True) ↔ Nonempty α
· 使用定理 `Set.mem_compl_iff`：mem_compl_iff (s : Set α) (x : α) : x in sᶜ ↔ x ∉ s
· 使用定理 `Set.mem_singleton_iff`：mem_singleton_iff {a b : α} : a in ({b} : Set α) 
↔ a = b
· 使用定理 `SimpleGraph.Walk.mem_support_iff_exists_append`：mem_support_iff_exists_a
ppend {V : Type u} {G : SimpleGraph V} {u v w : V} {p : G.Walk u v} : w in p.sup
port ↔ exists (q : G.Walk u w) (r : …
· 使用定理 `SimpleGraph.Walk.start_mem_support`：start_mem_support {u v : V} (p : G.W
alk u v) : u in p.support
· 使用定理 `List.nodup_iff_forall_not_duplicate`：nodup_iff_forall_not_duplicate : No
dup l ↔ forall x : α, ¬x in+ l
· 使用定理 `SimpleGraph.Path.nodup_support`：nodup_support {u v : V} (p : G.Path u v)
 : (p : G.Walk u v).support.Nodup
· 使用定理 `SimpleGraph.Walk.support_append`：support_append {u v w : V} (p : G.Walk 
u v) (p' : G.Walk v w) : (p.append p').support = p.support ++ p'.support.tail
· 使用定理 `List.duplicate_iff_two_le_count`：duplicate_iff_two_le_count [DecidableEq
 α] : x in+ l ↔ 2 <= count x l
· 使用定理 `List.count_append`：∀ {α : Type u_1} [inst : BEq α] {a : α} {l₁ l₂ : List
 α}, List.count a (l₁ ++ l₂) = List.count a l₁ + List.count a l₂
· 使用定理 `List.one_le_count_iff`：∀ {α : Type u_1} [inst : BEq α] [LawfulBEq α] {a 
: α} {l : List α}, 1 ≤ List.count a l ↔ a ∈ l
· 使用定理 `instLawfulBEq`：∀ {α : Type u_1} [inst : DecidableEq α], LawfulBEq α
· 使用定理 `SimpleGraph.Walk.getVert_mem_support`：getVert_mem_support {u v : V} (p :
 G.Walk u v) (i : Nat) : p.getVert i in p.support
· 使用引理 `SimpleGraph.Walk.snd_mem_tail_support`：snd_mem_tail_support {u v : V} {p
 : G.Walk u v} (h : ¬p.Nil) : p.snd in p.support.tail
· 使用引理 `SimpleGraph.Walk.not_nil_of_ne`：not_nil_of_ne {p : G.Walk v w} : v != w 
-> ¬ p.Nil
· 使用定理 `Aesop.BuiltinRules.not_intro`：∀ {P : Prop}, (P → False) → ¬P
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `SimpleGraph.Adj.symm`：∀ {V : Type u} {G : SimpleGraph V} {u v : V}, G.Ad
j u v → G.Adj v u
· 使用引理 `SimpleGraph.Walk.adj_penultimate`：adj_penultimate {p : G.Walk v w} (hp :
 ¬ p.Nil) : G.Adj p.penultimate w
（共 33 条，此处仅展示前 30 条）

--- 原说明 ---
The graph resulting from removing a vertex of degree one from a connected graph 
is connected.
-/
lemma Connected.induce_compl_singleton_of_degree_eq_one (hconn : G.Connected) {v : V}
    [Fintype ↑(G.neighborSet v)] (hdeg : G.degree v = 1) : (G.induce {v}ᶜ).Connected := by
  obtain ⟨u, adj_vu, hu⟩ := degree_eq_one_iff_existsUnique_adj.mp hdeg
  refine (connected_iff _).mpr ⟨?_, u, by aesop⟩
  /- There exists a walk between any two vertices w and x in G.induce {v}ᶜ
  via the unique vertex u adjacent to vertex v. -/
  intro w x
  obtain ⟨pwu, hpwu⟩ := hconn.exists_isPath w u
  obtain ⟨pux, hpux⟩ := hconn.exists_isPath u x
  rw [Reachable, ← exists_true_iff_nonempty]
  classical
  use ((pwu.append pux).toPath.val.induce {v}ᶜ ?_).copy (SetCoe.ext rfl) (SetCoe.ext rfl)
  /- Each path between vertex u and another vertex in G.induce {v}ᶜ
  is contained in G.induce {v}ᶜ. -/
  intro z hz
  rw [Set.mem_compl_iff, Set.mem_singleton_iff]
  obtain ⟨pwz, pzx, p_eq_pwzx⟩ := mem_support_iff_exists_append.mp hz
  /- Prove vertex v is not in the path formed from the concatenated walks
  by showing that vertex u must then be passed twice. -/
  by_contra
  subst_vars
  refine List.nodup_iff_forall_not_duplicate.mp (pwu.append pux).toPath.nodup_support u ?_
  rw [p_eq_pwzx, support_append, List.duplicate_iff_two_le_count, List.count_append]
  have := List.one_le_count_iff.mpr (pwz.getVert_mem_support (pwz.length - 1))
  simp only [hu _ (pwz.adj_penultimate (not_nil_of_ne (by aesop))).symm] at this
  have := List.one_le_count_iff.mpr (pzx.snd_mem_tail_support (not_nil_of_ne (by aesop)))
  rw [hu _ (pzx.adj_snd (not_nil_of_ne (by aesop)))] at this
  lia

/-- A finite nontrivial connected graph contains a vertex that leaves the graph connected if
removed. -/
/-
**SimpleGraph.Connected.exists_connected_induce_compl_singleton_of_finite_nontri
vial** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Connected`。
形式化陈述：∀ {V : Type u_1} {G : SimpleGraph V} [Finite V] [Nontrivial V], G.Connecte
d → ∃ v, (SimpleGraph.induce {v}ᶜ G).Connected
参数：SimpleGraph.induce {v}ᶜ G。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Connected.exists_isTree_le`：∀ {V : Type u_1} {G : SimpleGrap
h V}, G.Connected → ∃ T ≤ G, T.IsTree
· 使用定理 `SimpleGraph.IsTree.exists_vert_degree_one_of_nontrivial`：∀ {V : Type u_1
} {G : SimpleGraph V} [inst : Fintype V] [Nontrivial V] [inst_2 : DecidableRel G
.Adj],   G.IsTree → ∃ v, G.degree v = 1
· 使用定理 `SimpleGraph.Connected.mono`：∀ {V : Type u} {G G' : SimpleGraph V}, G ≤ G
' → G.Connected → G'.Connected
· 使用定理 `SimpleGraph.Connected.induce_compl_singleton_of_degree_eq_one`：∀ {V : Ty
pe u_1} {G : SimpleGraph V},   G.Connected → ∀ {v : V} [inst : Fintype ↑(G.neigh
borSet v)], G.degree v = 1 → (SimpleGraph.induce {v…

--- 原说明 ---
A finite nontrivial connected graph contains a vertex that leaves the graph conn
ected if
removed.
-/
lemma Connected.exists_connected_induce_compl_singleton_of_finite_nontrivial
    [Finite V] [Nontrivial V] (hconn : G.Connected) : ∃ v : V, (G.induce {v}ᶜ).Connected := by
  obtain ⟨T, _, T_isTree⟩ := hconn.exists_isTree_le
  have ⟨hT, _⟩ := T_isTree
  have := Fintype.ofFinite V
  classical
  obtain ⟨v, hv⟩ := T_isTree.exists_vert_degree_one_of_nontrivial
  exact ⟨v, (hT.induce_compl_singleton_of_degree_eq_one hv).mono (by tauto)⟩

/-- A finite connected graph contains a vertex that leaves the graph preconnected if removed. -/
/-
**SimpleGraph.Connected.exists_preconnected_induce_compl_singleton_of_finite** 是
 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Connected`。
形式化陈述：∀ {V : Type u_1} {G : SimpleGraph V} [Finite V], G.Connected → ∃ v, (Simpl
eGraph.induce {v}ᶜ G).Preconnected
参数：SimpleGraph.induce {v}ᶜ G。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `SimpleGraph.Connected.nonempty`：∀ {V : Type u} {G : SimpleGraph V}, G.Co
nnected → Nonempty V
· 使用定理 `SimpleGraph.Connected.exists_connected_induce_compl_singleton_of_finite_
nontrivial`：∀ {V : Type u_1} {G : SimpleGraph V} [Finite V] [Nontrivial V], G.Co
nnected → ∃ v, (SimpleGraph.induce {v}ᶜ G).Connected
· 使用定理 `SimpleGraph.Connected.preconnected`：∀ {V : Type u} {G : SimpleGraph V}, 
G.Connected → G.Preconnected

--- 原说明 ---
A finite connected graph contains a vertex that leaves the graph preconnected if
 removed.
-/
lemma Connected.exists_preconnected_induce_compl_singleton_of_finite [Finite V]
    (hconn : G.Connected) : ∃ v : V, (G.induce {v}ᶜ).Preconnected := by
  nontriviality V using hconn.nonempty
  obtain ⟨v, hv⟩ := hconn.exists_connected_induce_compl_singleton_of_finite_nontrivial
  exact ⟨v, hv.preconnected⟩
/-
**SimpleGraph.IsAcyclic.dist_ne_of_adj** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Is
Acyclic`。
形式化陈述：∀ {V : Type u_1} {G : SimpleGraph V}, G.IsAcyclic → ∀ {u v w : V}, G.Adj v
 w → G.Reachable u v → G.dist u v ≠ G.dist u w
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Reachable.exists_path_of_dist`：∀ {V : Type u_1} {G : SimpleG
raph V} {u v : V}, G.Reachable u v → ∃ p, p.IsPath ∧ p.length = G.dist u v
· 使用定理 `SimpleGraph.Reachable.trans`：∀ {V : Type u} {G : SimpleGraph V} {u v w :
 V}, G.Reachable u v → G.Reachable v w → G.Reachable u w
· 使用定理 `SimpleGraph.Adj.reachable`：∀ {V : Type u} {G : SimpleGraph V} {u v : V},
 G.Adj u v → G.Reachable u v
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `instLawfulBEq`：∀ {α : Type u_1} [inst : DecidableEq α], LawfulBEq α
· 使用定理 `SimpleGraph.Adj.symm`：∀ {V : Type u} {G : SimpleGraph V} {u v : V}, G.Ad
j u v → G.Adj v u
· 使用定理 `SimpleGraph.IsAcyclic.path_concat`：∀ {V : Type u_1} {G : SimpleGraph V},
   G.IsAcyclic →     ∀ {u v w : V} {p : G.Walk u v} {q : G.Walk u w},       p.Is
Path → q.IsPath → ∀ (ha…
· 使用定理 `SimpleGraph.Walk.length_concat`：length_concat {u v w : V} (p : G.Walk u 
v) (h : G.Adj v w) : (p.concat h).length = p.length + 1
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `Nat.ne_add_one`：∀ (n : ℕ), n ≠ n + 1
· 使用定理 `SimpleGraph.IsAcyclic.mem_support_of_ne_mem_support_of_adj_of_isPath`：∀ 
{V : Type u_1} {G : SimpleGraph V},   G.IsAcyclic →     ∀ {u v w : V} {p : G.Wal
k u v} {q : G.Walk u w}, p.IsPath → q.IsPath → G.Adj v w →…
-/
lemma IsAcyclic.dist_ne_of_adj (hG : G.IsAcyclic) {u v w : V} (hadj : G.Adj v w)
    (hreach : G.Reachable u v) : G.dist u v ≠ G.dist u w := by
  obtain ⟨p, hp, hp'⟩ := hreach.exists_path_of_dist
  obtain ⟨q, hq, hq'⟩ := hreach.trans hadj.reachable |>.exists_path_of_dist
  rw [← hp', ← hq']
  by_cases hw : w ∈ p.support
  · rw [hG.path_concat hq hp hadj.symm hw, q.length_concat]
    exact q.length.ne_add_one.symm
  · have hv : v ∈ q.support := hG.mem_support_of_ne_mem_support_of_adj_of_isPath hq hp
      hadj.symm hw
    rw [hG.path_concat hp hq hadj hv, p.length_concat]
    exact p.length.ne_add_one
/-
**SimpleGraph.IsTree.dist_ne_of_adj** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.IsTre
e`。
形式化陈述：∀ {V : Type u_1} {G : SimpleGraph V}, G.IsTree → ∀ (u : V) {v w : V}, G.Ad
j v w → G.dist u v ≠ G.dist u w
参数：u : V。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.IsAcyclic.dist_ne_of_adj`：∀ {V : Type u_1} {G : SimpleGraph 
V}, G.IsAcyclic → ∀ {u v w : V}, G.Adj v w → G.Reachable u v → G.dist u v ≠ G.di
st u w
· 使用定理 `SimpleGraph.IsTree.isAcyclic`：∀ {V : Type u_1} {G : SimpleGraph V}, G.Is
Tree → G.IsAcyclic
· 使用定理 `SimpleGraph.Connected.preconnected`：∀ {V : Type u} {G : SimpleGraph V}, 
G.Connected → G.Preconnected
· 使用定理 `SimpleGraph.IsTree.connected`：∀ {V : Type u_1} {G : SimpleGraph V}, G.Is
Tree → G.Connected
-/
lemma IsTree.dist_ne_of_adj (hG : G.IsTree) (u : V) {v w : V} (hadj : G.Adj v w) :
    G.dist u v ≠ G.dist u w :=
  hG.isAcyclic.dist_ne_of_adj hadj <| hG.connected u v
/-
**SimpleGraph.IsAcyclic.dist_eq_dist_add_one_of_adj_of_reachable** 是 Mathlib 中的一
个定理，位于命名空间 `SimpleGraph.IsAcyclic`。
形式化陈述：∀ {V : Type u_1} {G : SimpleGraph V},   G.IsAcyclic →     ∀ (u : V) {v w :
 V}, G.Adj v w → G.Reachable u v → G.dist u v = G.dist u w + 1 ∨ G.dist u w = G.
dist u v + 1
参数：u : V。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma IsAcyclic.dist_eq_dist_add_one_of_adj_of_reachable
    (hG : G.IsAcyclic) (u : V) {v w : V} (hadj : G.Adj v w) (hreach : G.Reachable u v) :
    G.dist u v = G.dist u w + 1 ∨ G.dist u w = G.dist u v + 1 := by
  grind [dist_ne_of_adj, Adj.diff_dist_adj]
/-
**SimpleGraph.IsTree.dist_eq_dist_add_one_of_adj** 是 Mathlib 中的一个定理，位于命名空间 `Simp
leGraph.IsTree`。
形式化陈述：∀ {V : Type u_1} {G : SimpleGraph V},   G.IsTree → ∀ (u : V) {v w : V}, G.
Adj v w → G.dist u v = G.dist u w + 1 ∨ G.dist u w = G.dist u v + 1
参数：u : V。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma IsTree.dist_eq_dist_add_one_of_adj (hG : G.IsTree) (u : V) {v w : V} (hadj : G.Adj v w) :
    G.dist u v = G.dist u w + 1 ∨ G.dist u w = G.dist u v + 1 := by
  grind [dist_ne_of_adj, Adj.diff_dist_adj]

/-- The unique two-coloring of a tree that colors the given vertex with zero -/
/-
**SimpleGraph.IsTree.coloringTwoOfVert** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph.Is
Tree`。
形式化陈述：{V : Type u_1} → {G : SimpleGraph V} → G.IsTree → V → G.Coloring (Fin 2)
参数：Fin 2。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The unique two-coloring of a tree that colors the given vertex with zero
-/
noncomputable def IsTree.coloringTwoOfVert (hG : G.IsTree) (u : V) : G.Coloring (Fin 2) :=
  Coloring.mk (fun v ↦ ⟨G.dist u v % 2, Nat.mod_lt (G.dist u v) Nat.zero_lt_two⟩) <| by
    grind [dist_eq_dist_add_one_of_adj]

/-- Arbitrary coloring with two colors for a tree -/
/-
**SimpleGraph.IsTree.coloringTwo** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph.IsTree`。
形式化陈述：{V : Type u_1} → {G : SimpleGraph V} → G.IsTree → G.Coloring (Fin 2)
参数：Fin 2。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Arbitrary coloring with two colors for a tree
-/
noncomputable def IsTree.coloringTwo (hG : G.IsTree) : G.Coloring (Fin 2) :=
  hG.coloringTwoOfVert hG.connected.nonempty.some
/-
**SimpleGraph.IsTree.isBipartite** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.IsTree`。
形式化陈述：∀ {V : Type u_1} {G : SimpleGraph V}, G.IsTree → G.IsBipartite
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma IsTree.isBipartite (hG : G.IsTree) : G.IsBipartite :=
  ⟨hG.coloringTwo⟩

/-- The unique two-coloring of a forest that colors the given vertices with zero -/
/-
**SimpleGraph.IsAcyclic.coloringTwoOfVerts** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGrap
h.IsAcyclic`。
形式化陈述：{V : Type u_1} →   {G : SimpleGraph V} →     G.IsAcyclic → (verts : G.Conn
ectedComponent → V) → (∀ (C : G.ConnectedComponent), verts C ∈ C) → G.Coloring (
Fin 2)
参数：verts : G.ConnectedComponent → V；∀ (C : G.ConnectedComponent), verts C ∈ C；Fi
n 2。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The unique two-coloring of a forest that colors the given vertices with zero
-/
noncomputable def IsAcyclic.coloringTwoOfVerts (hG : G.IsAcyclic) (verts : G.ConnectedComponent → V)
    (h : ∀ C, verts C ∈ C) : G.Coloring (Fin 2) where
  toFun v :=
    let u := verts <| G.connectedComponentMk v
    ⟨G.dist u v % 2, Nat.mod_lt (G.dist u v) Nat.zero_lt_two⟩
  map_rel' := by
    intro u v hadj
    have := ConnectedComponent.sound hadj.reachable
    have := hG.dist_eq_dist_add_one_of_adj_of_reachable _ hadj <| ConnectedComponent.exact <| h _
    grind [top_adj]

/-- Arbitrary coloring with two colors for a forest -/
/-
**SimpleGraph.IsAcyclic.coloringTwo** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph.IsAcy
clic`。
形式化陈述：{V : Type u_1} → {G : SimpleGraph V} → G.IsAcyclic → G.Coloring (Fin 2)
参数：Fin 2。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.ConnectedComponent.nonempty_supp`：nonempty_supp (C : G.Conne
ctedComponent) : C.supp.Nonempty

--- 原说明 ---
Arbitrary coloring with two colors for a forest
-/
noncomputable def IsAcyclic.coloringTwo (hG : G.IsAcyclic) : G.Coloring (Fin 2) :=
  hG.coloringTwoOfVerts (·.nonempty_supp.some) (·.nonempty_supp.some_mem)
/-
**SimpleGraph.IsAcyclic.isBipartite** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.IsAcy
clic`。
形式化陈述：∀ {V : Type u_1} {G : SimpleGraph V}, G.IsAcyclic → G.IsBipartite
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma IsAcyclic.isBipartite (hG : G.IsAcyclic) : G.IsBipartite :=
  ⟨hG.coloringTwo⟩

/-- An acyclic graph (forest) is 2-colorable. -/
/-
**SimpleGraph.IsAcyclic.colorable_two** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.IsA
cyclic`。
形式化陈述：∀ {V : Type u_1} {G : SimpleGraph V}, G.IsAcyclic → G.Colorable 2
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.IsAcyclic.isBipartite`：∀ {V : Type u_1} {G : SimpleGraph V},
 G.IsAcyclic → G.IsBipartite

--- 原说明 ---
An acyclic graph (forest) is 2-colorable.
-/
lemma IsAcyclic.colorable_two (hG : G.IsAcyclic) : G.Colorable 2 :=
  hG.isBipartite

/-- A tree is 2-colorable. -/
/-
**SimpleGraph.IsTree.colorable_two** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.IsTree
`。
形式化陈述：∀ {V : Type u_1} {G : SimpleGraph V}, G.IsTree → G.Colorable 2
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.IsAcyclic.colorable_two`：∀ {V : Type u_1} {G : SimpleGraph V
}, G.IsAcyclic → G.Colorable 2
· 使用定理 `SimpleGraph.IsTree.isAcyclic`：∀ {V : Type u_1} {G : SimpleGraph V}, G.Is
Tree → G.IsAcyclic

--- 原说明 ---
A tree is 2-colorable.
-/
lemma IsTree.colorable_two (hG : G.IsTree) : G.Colorable 2 :=
  hG.isAcyclic.colorable_two

/-- The chromatic number of an acyclic graph (forest) is at most 2. -/
/-
**SimpleGraph.IsAcyclic.chromaticNumber_le_two** 是 Mathlib 中的一个定理，位于命名空间 `Simple
Graph.IsAcyclic`。
形式化陈述：∀ {V : Type u_1} {G : SimpleGraph V}, G.IsAcyclic → G.chromaticNumber ≤ 2
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Colorable.chromaticNumber_le`：∀ {V : Type u} {G : SimpleGrap
h V} {n : ℕ}, G.Colorable n → G.chromaticNumber ≤ ↑n
· 使用定理 `SimpleGraph.IsAcyclic.colorable_two`：∀ {V : Type u_1} {G : SimpleGraph V
}, G.IsAcyclic → G.Colorable 2

--- 原说明 ---
The chromatic number of an acyclic graph (forest) is at most 2.
-/
lemma IsAcyclic.chromaticNumber_le_two (hG : G.IsAcyclic) : G.chromaticNumber ≤ 2 :=
  hG.colorable_two.chromaticNumber_le

/-- The chromatic number of a tree is at most 2. -/
/-
**SimpleGraph.IsTree.chromaticNumber_le_two** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGra
ph.IsTree`。
形式化陈述：∀ {V : Type u_1} {G : SimpleGraph V}, G.IsTree → G.chromaticNumber ≤ 2
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Colorable.chromaticNumber_le`：∀ {V : Type u} {G : SimpleGrap
h V} {n : ℕ}, G.Colorable n → G.chromaticNumber ≤ ↑n
· 使用定理 `SimpleGraph.IsTree.colorable_two`：∀ {V : Type u_1} {G : SimpleGraph V}, 
G.IsTree → G.Colorable 2

--- 原说明 ---
The chromatic number of a tree is at most 2.
-/
lemma IsTree.chromaticNumber_le_two (hG : G.IsTree) : G.chromaticNumber ≤ 2 :=
  hG.colorable_two.chromaticNumber_le
/-
**SimpleGraph.exists_isCycle_of_two_le_isEdgeReachable** 是 Mathlib 中的一个引理，位于命名空间
 `SimpleGraph`。
形式化陈述：exists_isCycle_of_two_le_isEdgeReachable {u v : V} (huv : u != v) {n : Nat
} (hn : 2 <= n) (h : G.IsEdgeReachable n u v) : exists w : G.Walk u u, w.IsCycle
参数：huv : u != v；hn : 2 <= n；h : G.IsEdgeReachable n u v。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SimpleGraph.exists_adj_isEdgeReachable_two`：exists_adj_isEdgeReachable_t
wo (hne : u != v) (h : G.IsEdgeReachable 2 u v) : exists w : V, G.Adj u w ∧ G.Is
EdgeReachable 2 u w
· 使用定理 `SimpleGraph.IsEdgeReachable.anti`：∀ {V : Type u_1} {G : SimpleGraph V} {
k l : ℕ} {u v : V}, k ≤ l → G.IsEdgeReachable l u v → G.IsEdgeReachable k u v
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.encard_singleton`：∀ {α : Type u_1} (e : α), {e}.encard = 1
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `instIsOrderedRingENat`：IsOrderedRing ℕ∞
· 使用定理 `instZeroLEOneClassENat`：ZeroLEOneClass ℕ∞
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `SimpleGraph.adj_and_reachable_delete_edges_iff_exists_cycle`：adj_and_rea
chable_delete_edges_iff_exists_cycle {v w : V} : G.Adj v w ∧ (G.deleteEdges {s(v
, w)}).Reachable v w ↔ exists (u : V) (p : G.Walk…
· 使用定理 `SimpleGraph.Walk.fst_mem_support_of_mem_edges`：fst_mem_support_of_mem_ed
ges {t u v w : V} (p : G.Walk v w) (he : s(t, u) in p.edges) : t in p.support
· 使用定理 `SimpleGraph.Walk.IsCycle.rotate`：∀ {V : Type u} {G : SimpleGraph V} {u v
 : V} [inst : DecidableEq V] {c : G.Walk v v} (hu : u ∈ c.support),   c.IsCycle 
→ (c.rotate u hu).IsC…
-/
lemma exists_isCycle_of_two_le_isEdgeReachable {u v : V} (huv : u ≠ v) {n : ℕ} (hn : 2 ≤ n)
    (h : G.IsEdgeReachable n u v) : ∃ w : G.Walk u u, w.IsCycle := by
  classical
  obtain ⟨w, hw, h⟩ := exists_adj_isEdgeReachable_two huv (h.anti hn)
  have := @h {s(u, w)} (by simp)
  obtain ⟨w, p, hp₁, hp₂⟩ := adj_and_reachable_delete_edges_iff_exists_cycle.mp ⟨hw, this⟩
  exact ⟨p.rotate _ (p.fst_mem_support_of_mem_edges hp₂), hp₁.rotate _⟩
/-
**SimpleGraph.isAcyclic_iff_pairwise_not_isEdgeReachable_two** 是 Mathlib 中的一个引理，
位于命名空间 `SimpleGraph`。
形式化陈述：isAcyclic_iff_pairwise_not_isEdgeReachable_two : G.IsAcyclic ↔ Pairwise (¬
G.IsEdgeReachable 2 · ·)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SimpleGraph.exists_isCycle_of_two_le_isEdgeReachable`：exists_isCycle_of_
two_le_isEdgeReachable {u v : V} (huv : u != v) {n : Nat} (hn : 2 <= n) (h : G.I
sEdgeReachable n u v) : exists w : G.Walk …
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.isAcyclic_iff_forall_isBridge`：isAcyclic_iff_forall_isBridge
 : G.IsAcyclic ↔ forall ⦃e⦄, e in G.edgeSet -> G.IsBridge e where .elim .mpr fun
 v p hc => hG p hc mp hG e he
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `SimpleGraph.isBridge_iff_not_isEdgeReachable_two`：isBridge_iff_not_isEdg
eReachable_two (huv : G.Adj u v) : G.IsBridge s(u, v) ↔ ¬G.IsEdgeReachable 2 u v
· 使用定理 `SimpleGraph.Adj.ne`：∀ {V : Type u} {G : SimpleGraph V} {a b : V}, G.Adj 
a b → a ≠ b
-/
lemma isAcyclic_iff_pairwise_not_isEdgeReachable_two :
    G.IsAcyclic ↔ Pairwise (¬G.IsEdgeReachable 2 · ·) := by
  refine ⟨fun h _ _ hne he ↦ ?_, fun h ↦ ?_⟩
  · obtain ⟨w, hw⟩ := exists_isCycle_of_two_le_isEdgeReachable hne le_rfl he
    exact h w hw
  · rw [isAcyclic_iff_forall_isBridge]
    rintro ⟨u, v⟩ huv
    exact (isBridge_iff_not_isEdgeReachable_two huv).mpr (h huv.ne)
/-
**SimpleGraph.isAcyclic_iff_free_cycleGraph** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGra
ph`。
形式化陈述：isAcyclic_iff_free_cycleGraph : G.IsAcyclic ↔ forall n >= 3, (cycleGraph n
).Free G
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `SimpleGraph.cycleGraph_isContained_iff`：cycleGraph_isContained_iff {n : 
Nat} (hn : 2 < n) : cycleGraph n ⊑ G ↔ exists (v : V) (p : G.Walk v v), p.IsCycl
e ∧ p.length = n
· 使用定理 `SimpleGraph.Walk.IsCircuit.three_le_length`：∀ {V : Type u} {G : SimpleGr
aph V} {v : V} {p : G.Walk v v}, p.IsCircuit → 3 ≤ p.length
· 使用定理 `SimpleGraph.Walk.IsCycle.isCircuit`：∀ {V : Type u} {G : SimpleGraph V} {
u : V} {p : G.Walk u u}, p.IsCycle → p.IsCircuit
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
-/
theorem isAcyclic_iff_free_cycleGraph : G.IsAcyclic ↔ ∀ n ≥ 3, (cycleGraph n).Free G := by
  refine ⟨fun h n hn hle ↦ ?_, fun h v p hcyc ↦ h p.length hcyc.three_le_length ?_⟩
  · have ⟨v, p, hcyc, hlen⟩ := cycleGraph_isContained_iff hn |>.mp hle
    exact h p hcyc
  · exact cycleGraph_isContained_iff hcyc.three_le_length |>.mpr ⟨v, p, hcyc, rfl⟩
/-
**SimpleGraph.IsAcyclic.cliqueFree** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.IsAcyc
lic`。
形式化陈述：∀ {V : Type u_1} {G : SimpleGraph V}, G.IsAcyclic → ∀ {n : ℕ}, 3 ≤ n → G.C
liqueFree n
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.not_right`：Iff.not_right (h : ¬a ↔ b) : a ↔ ¬b
· 使用定理 `SimpleGraph.not_cliqueFree_iff_top_isContained`：not_cliqueFree_iff_top_i
sContained (n : Nat) : ¬G.CliqueFree n ↔ completeGraph (Fin n) ⊑ G
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `SimpleGraph.isAcyclic_iff_free_cycleGraph`：isAcyclic_iff_free_cycleGraph
 : G.IsAcyclic ↔ forall n >= 3, (cycleGraph n).Free G
· 使用定理 `SimpleGraph.IsContained.trans'`：∀ {α : Type u_4} {β : Type u_5} {γ : Typ
e u_6} {A : SimpleGraph α} {B : SimpleGraph β} {C : SimpleGraph γ},   B.IsContai
ned C → A.IsContaine…
· 使用定理 `SimpleGraph.IsContained.of_le`：∀ {V : Type u_1} {G₁ G₂ : SimpleGraph V},
 G₁ ≤ G₂ → G₁.IsContained G₂
· 使用定理 `le_top`：le_top : a <= ⊤
-/
theorem IsAcyclic.cliqueFree (h : G.IsAcyclic) {n : ℕ} (hn : 3 ≤ n) : G.CliqueFree n := by
  refine not_cliqueFree_iff_top_isContained n |>.not_right.mpr fun hle ↦ ?_
  exact isAcyclic_iff_free_cycleGraph.mp h n hn <| hle.trans' <| .of_le le_top

end SimpleGraph

