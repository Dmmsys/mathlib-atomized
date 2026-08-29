/-
Copyright (c) 2024 Kyle Miller, Jack Cheverton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller, Jack Cheverton, Jeremy Tan
-/
module

public import Mathlib.Order.CompleteBooleanAlgebra
public import Mathlib.Data.Fintype.Pi

/-!
# Digraphs

This module defines directed graphs on a vertex type `V`,
which is the same notion as a relation `V → V → Prop`.
While this might be too simple of a notion to deserve the grandeur of a new definition,
the intention here is to develop relations using the language of graph theory.

Note that in this treatment, a digraph may have self loops.

The type `Digraph V` is structurally equivalent to `Quiver.{0} V`,
but a difference between these is that `Quiver` is a class —
its purpose is to attach a quiver structure to a particular type `V`.
In contrast, for `Digraph V` we are interested in working with the entire lattice
of digraphs on `V`.

## Main definitions

* `Digraph` is a structure for relations. Unlike `SimpleGraph`, the relation does not need to be
  symmetric or irreflexive.

* `CompleteAtomicBooleanAlgebra` instance: Under the subgraph relation, `Digraph` forms a
  `CompleteAtomicBooleanAlgebra`. In other words, this is the complete lattice of spanning subgraphs
  of the complete graph.
-/

@[expose] public section

open Finset Function

/--
A digraph is a relation `Adj` on a vertex type `V`.
The relation describes which pairs of vertices are adjacent.

In this treatment, a digraph may have self-loops.
-/
@[ext]
/--
Definition of `Digraph` / `Digraph` 的定义

English:
structure Digraph
  parameters: (V : Type*)
  axioms and operations (1):
    - Adj : V -> V -> Prop

中文:
结构 有向图
  参数: (V : 类型)
  公理与运算 (1 个):
    - Adj : V -> V -> 命题
-/
structure Digraph (V : Type*) where
  /-- The adjacency relation of a digraph. -/
  Adj : V -> V -> Prop

/--
Constructor for digraphs using a Boolean function.
This is useful for creating a digraph with a decidable `Adj` relation,
and it's used in the construction of the `Fintype (Digraph V)` instance.
-/
@[simps]
/--
Definition of `Digraph.mk'` / `Digraph.mk'` 的定义

English:
definition Digraph.mk'
  signature: {V : Type*}
  body: ⟨fun v w => x v w⟩
  inj' adj adj' := by
    simp_rw [mk.injEq]
    intro h
    funext v w
    simpa only [eq_iff_iff, Bool.coe_iff_coe] using congr($h v w)

中文:
定义 有向图.mk'
  签名: {V : 类型}
  定义体: ⟨fun v w => x v w⟩
  inj' adj adj' := by
    simp_rw [mk.injEq]
    intro h
    funext v w
    simpa only [eq_iff_iff, Bool.coe_iff_coe] using congr($h v w)
-/
def Digraph.mk' {V : Type*} : (V -> V -> Bool) ↪ Digraph V where
  toFun x := ⟨fun v w => x v w⟩
  inj' adj adj' := by
    simp_rw [mk.injEq]
    intro h
    funext v w
    simpa only [eq_iff_iff, Bool.coe_iff_coe] using congr($h v w)

instance {V : Type*} (adj : V -> V -> Bool) : DecidableRel (Digraph.mk' adj).Adj :=
inferInstanceAs DecidableRel (fun v w => adj v w)

instance {V : Type*} [DecidableEq V] [Fintype V] : Fintype (Digraph V) :=
Fintype.ofBijective Digraph.mk' by
    classical
    refine ⟨Embedding.injective _, ?_⟩
    intro G
    use fun v w => G.Adj v w
    ext v w
    simp

namespace Digraph

/--
Definition of `completeDigraph` / `completeDigraph` 的定义

English:
definition completeDigraph
  signature: (V : Type*)
  body: ⊤

中文:
定义 completeDigraph
  签名: (V : 类型)
  定义体: ⊤
-/
protected def completeDigraph (V : Type*) : Digraph V where Adj := ⊤

/--
Definition of `emptyDigraph` / `emptyDigraph` 的定义

English:
definition emptyDigraph
  signature: (V : Type*)
  body: False

中文:
定义 emptyDigraph
  签名: (V : 类型)
  定义体: False
-/
protected def emptyDigraph (V : Type*) : Digraph V where Adj _ _ := False

/--
Two vertices are adjacent in the complete bipartite digraph on two vertex types
if and only if they are not from the same side.
Any bipartite digraph may be regarded as a subgraph of one of these.
-/
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
def completeBipartiteGraph (V W : Type*) : Digraph (Sum V W) where
  Adj v w := v.isLeft ∧ w.isRight ∨ v.isRight ∧ w.isLeft

variable {ι : Sort*} {V : Type*} (G : Digraph V) {a b : V}

/--
theorem `adj_injective` / 定理 `adj_injective`

English:
theorem adj_injective
  statement: Injective (Adj : Digraph V -> V -> V -> Prop)
  proof: fun _ _ => Digraph.ext

中文:
定理 adj_injective
  结论: 单射 (伴随 : 有向图 V -> V -> V -> 命题)
  证明: fun _ _ => Digraph.ext

Depends on / 依赖: Digraph, Digraph.ext
-/
theorem adj_injective : Injective (Adj : Digraph V -> V -> V -> Prop) := fun _ _ => Digraph.ext

/--
theorem `adj_inj` / 定理 `adj_inj`

English:
theorem adj_inj
  given: {G H : Digraph V}
  statement: G.Adj = H.Adj ↔ G = H
  proof: Digraph.ext_iff.symm

中文:
定理 adj_inj
  条件: {G H : 有向图 V}
  结论: G.伴随 = H.伴随 ↔ G = H
  证明: Digraph.ext_iff.symm
-/
@[simp] theorem adj_inj {G H : Digraph V} : G.Adj = H.Adj ↔ G = H := Digraph.ext_iff.symm

section Order

/--
Definition of `IsSubgraph` / `IsSubgraph` 的定义

English:
definition IsSubgraph
  signature: (x y : Digraph V)
  body: forall ⦃v w : V⦄, x.Adj v w -> y.Adj v w

中文:
定义 是子图
  签名: (x y : 有向图 V)
  定义体: forall ⦃v w : V⦄, x.Adj v w -> y.Adj v w
-/
protected def IsSubgraph (x y : Digraph V) : Prop :=
  forall ⦃v w : V⦄, x.Adj v w -> y.Adj v w

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LE (Digraph V)
  body: ⟨Digraph.IsSubgraph⟩

@[simp]

中文:
实例 :
  签名: LE (有向图 V)
  定义体: ⟨Digraph.IsSubgraph⟩

@[simp]

Depends on / 依赖: Digraph, Digraph.IsSubgraph, IsSubgraph
-/
instance : LE (Digraph V) := ⟨Digraph.IsSubgraph⟩

@[simp]
/--
theorem `isSubgraph_eq_le` / 定理 `isSubgraph_eq_le`

English:
theorem isSubgraph_eq_le
  statement: (Digraph.IsSubgraph : Digraph V -> Digraph V -> Prop) = (· <= ·)
  proof: rfl

中文:
定理 isSubgraph_eq_le
  结论: (有向图.是子图 : 有向图 V -> 有向图 V -> 命题) = (· <= ·)
  证明: rfl
-/
theorem isSubgraph_eq_le : (Digraph.IsSubgraph : Digraph V -> Digraph V -> Prop) = (· <= ·) := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Max (Digraph V)
  body: { Adj := x.Adj ⊔ y.Adj }

@[simp]

中文:
实例 :
  签名: 最大值 (有向图 V)
  定义体: { Adj := x.Adj ⊔ y.Adj }

@[simp]

Depends on / 依赖: x.Adj, y.Adj
-/
instance : Max (Digraph V) where
  max x y := { Adj := x.Adj ⊔ y.Adj }

@[simp]
/--
theorem `sup_adj` / 定理 `sup_adj`

English:
theorem sup_adj
  given: (x y : Digraph V) (v w : V)
  statement: (x ⊔ y).Adj v w ↔ x.Adj v w ∨ y.Adj v w
  proof: Iff.rfl

中文:
定理 sup_adj
  条件: (x y : 有向图 V) (v w : V)
  结论: (x ⊔ y).伴随 v w ↔ x.伴随 v w ∨ y.伴随 v w
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem sup_adj (x y : Digraph V) (v w : V) : (x ⊔ y).Adj v w ↔ x.Adj v w ∨ y.Adj v w := Iff.rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Min (Digraph V)
  body: { Adj := x.Adj ⊓ y.Adj }

@[simp]

中文:
实例 :
  签名: 最小值 (有向图 V)
  定义体: { Adj := x.Adj ⊓ y.Adj }

@[simp]

Depends on / 依赖: x.Adj, y.Adj
-/
instance : Min (Digraph V) where
  min x y := { Adj := x.Adj ⊓ y.Adj }

@[simp]
/--
theorem `inf_adj` / 定理 `inf_adj`

English:
theorem inf_adj
  given: (x y : Digraph V) (v w : V)
  statement: (x ⊓ y).Adj v w ↔ x.Adj v w ∧ y.Adj v w
  proof: Iff.rfl

中文:
定理 inf_adj
  条件: (x y : 有向图 V) (v w : V)
  结论: (x ⊓ y).伴随 v w ↔ x.伴随 v w ∧ y.伴随 v w
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem inf_adj (x y : Digraph V) (v w : V) : (x ⊓ y).Adj v w ↔ x.Adj v w ∧ y.Adj v w := Iff.rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Compl (Digraph V)
  body: { Adj := fun v w => ¬G.Adj v w }

中文:
实例 :
  签名: 补集 (有向图 V)
  定义体: { Adj := fun v w => ¬G.Adj v w }

Depends on / 依赖: G.Adj
-/
instance : Compl (Digraph V) where
  compl G := { Adj := fun v w => ¬G.Adj v w }

/--
theorem `compl_adj` / 定理 `compl_adj`

English:
theorem compl_adj
  given: (G : Digraph V) (v w : V)
  statement: Gᶜ.Adj v w ↔ ¬G.Adj v w
  proof: Iff.rfl

中文:
定理 compl_adj
  条件: (G : 有向图 V) (v w : V)
  结论: Gᶜ.伴随 v w ↔ ¬G.伴随 v w
  证明: Iff.rfl
-/
@[simp] theorem compl_adj (G : Digraph V) (v w : V) : Gᶜ.Adj v w ↔ ¬G.Adj v w := Iff.rfl

/--
Instance `sdiff` / 实例 `sdiff`

English:
instance sdiff
  signature: : SDiff (Digraph V) where
  body: { Adj := x.Adj \ y.Adj }

@[simp]

中文:
实例 sdiff
  签名: : 对称差 (有向图 V) where
  定义体: { Adj := x.Adj \ y.Adj }

@[simp]

Depends on / 依赖: x.Adj, y.Adj
-/
instance sdiff : SDiff (Digraph V) where
  sdiff x y := { Adj := x.Adj \ y.Adj }

@[simp]
/--
theorem `sdiff_adj` / 定理 `sdiff_adj`

English:
theorem sdiff_adj
  given: (x y : Digraph V) (v w : V)
  statement: (x \ y).Adj v w ↔ x.Adj v w ∧ ¬y.Adj v w
  proof: Iff.rfl

中文:
定理 sdiff_adj
  条件: (x y : 有向图 V) (v w : V)
  结论: (x \ y).伴随 v w ↔ x.伴随 v w ∧ ¬y.伴随 v w
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem sdiff_adj (x y : Digraph V) (v w : V) : (x \ y).Adj v w ↔ x.Adj v w ∧ ¬y.Adj v w := Iff.rfl

/--
Instance `supSet` / 实例 `supSet`

English:
instance supSet
  signature: : SupSet (Digraph V) where
  body: { Adj := fun a b => exists G in s, Adj G a b }

中文:
实例 supSet
  签名: : 上确界集 (有向图 V) where
  定义体: { Adj := fun a b => exists G in s, Adj G a b }
-/
instance supSet : SupSet (Digraph V) where
  sSup s := { Adj := fun a b => exists G in s, Adj G a b }

/--
Instance `infSet` / 实例 `infSet`

English:
instance infSet
  signature: : InfSet (Digraph V) where
  body: { Adj := fun a b => (forall ⦃G⦄, G in s -> Adj G a b) }

@[simp]

中文:
实例 infSet
  签名: : 下确界集 (有向图 V) where
  定义体: { Adj := fun a b => (forall ⦃G⦄, G in s -> Adj G a b) }

@[simp]
-/
instance infSet : InfSet (Digraph V) where
  sInf s := { Adj := fun a b => (forall ⦃G⦄, G in s -> Adj G a b) }

@[simp]
/--
theorem `sSup_adj` / 定理 `sSup_adj`

English:
theorem sSup_adj
  given: {s : Set (Digraph V)}
  statement: (sSup s).Adj a b ↔ exists G in s, Adj G a b
  proof: Iff.rfl

@[simp]

中文:
定理 sSup_adj
  条件: {s : 集合 (有向图 V)}
  结论: (sSup s).伴随 a b ↔ 存在 G in s, 伴随 G a b
  证明: Iff.rfl

@[simp]

Depends on / 依赖: Iff.rfl
-/
theorem sSup_adj {s : Set (Digraph V)} : (sSup s).Adj a b ↔ exists G in s, Adj G a b := Iff.rfl

@[simp]
/--
theorem `sInf_adj` / 定理 `sInf_adj`

English:
theorem sInf_adj
  given: {s : Set (Digraph V)}
  statement: (sInf s).Adj a b ↔ forall G in s, Adj G a b
  proof: Iff.rfl

@[simp]

中文:
定理 sInf_adj
  条件: {s : 集合 (有向图 V)}
  结论: (sInf s).伴随 a b ↔ 对任意 G in s, 伴随 G a b
  证明: Iff.rfl

@[simp]

Depends on / 依赖: Iff.rfl
-/
theorem sInf_adj {s : Set (Digraph V)} : (sInf s).Adj a b ↔ forall G in s, Adj G a b := Iff.rfl

@[simp]
/--
theorem `iSup_adj` / 定理 `iSup_adj`

English:
theorem iSup_adj
  given: {f : ι -> Digraph V}
  statement: (⨆ i, f i).Adj a b ↔ exists i, (f i).Adj a b
  proof: by simp [iSup]

@[simp]

中文:
定理 iSup_adj
  条件: {f : ι -> 有向图 V}
  结论: (⨆ i, f i).伴随 a b ↔ 存在 i, (f i).伴随 a b
  证明: by simp [iSup]

@[simp]
-/
theorem iSup_adj {f : ι -> Digraph V} : (⨆ i, f i).Adj a b ↔ exists i, (f i).Adj a b := by simp [iSup]

@[simp]
/--
theorem `iInf_adj` / 定理 `iInf_adj`

English:
theorem iInf_adj
  given: {f : ι -> Digraph V}
  statement: (⨅ i, f i).Adj a b ↔ (forall i, (f i).Adj a b)
  proof: by simp [iInf]

中文:
定理 iInf_adj
  条件: {f : ι -> 有向图 V}
  结论: (⨅ i, f i).伴随 a b ↔ (对任意 i, (f i).伴随 a b)
  证明: by simp [iInf]
-/
theorem iInf_adj {f : ι -> Digraph V} : (⨅ i, f i).Adj a b ↔ (forall i, (f i).Adj a b) := by simp [iInf]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PartialOrder (Digraph V)
  body: fast_instance% PartialOrder.lift _ adj_injective

中文:
实例 :
  签名: 偏序 (有向图 V)
  定义体: fast_instance% PartialOrder.lift _ adj_injective

Depends on / 依赖: PartialOrder, PartialOrder.lift, adj_injective, fast_instance
-/
instance : PartialOrder (Digraph V) := fast_instance% PartialOrder.lift _ adj_injective

/--
Instance `distribLattice` / 实例 `distribLattice`

English:
instance distribLattice
  signature: : DistribLattice (Digraph V)
  body: fast_instance%
  adj_injective.distribLattice _ .rfl .rfl (fun _ _ => rfl) fun _ _ => rfl

中文:
实例 distribLattice
  签名: : Distrib格 (有向图 V)
  定义体: fast_instance%
  adj_injective.distribLattice _ .rfl .rfl (fun _ _ => rfl) fun _ _ => rfl

Depends on / 依赖: fast_instance
-/
instance distribLattice : DistribLattice (Digraph V) := fast_instance%
  adj_injective.distribLattice _ .rfl .rfl (fun _ _ => rfl) fun _ _ => rfl

/--
Instance `completeAtomicBooleanAlgebra` / 实例 `completeAtomicBooleanAlgebra`

English:
instance completeAtomicBooleanAlgebra
  signature: : CompleteAtomicBooleanAlgebra (Digraph V) where
  body: Digraph.completeDigraph V
  bot := Digraph.emptyDigraph V
  le_top _ _ _ _ := trivial
  bot_le _ _ _ h := h.elim
  inf_compl_le_bot _ _ _ h := absurd h.1 h.2
  top_le_sup_compl G v w _ := by tauto
  isLUB_sSup _ := ⟨fun G hG _ _ hab => ⟨G, hG, hab⟩, fun _ hG _ _ ⟨_, hH, hab⟩ => hG hH hab⟩
  isGLB_sInf _ := ⟨fun _ hG _ _ hab => hab hG, fun _ hG _ _ hab _ hH => hG hH hab⟩
  iInf_iSup_eq f := by ext; simp [Classical.skolem]

中文:
实例 completeAtomic布尔eanAlgebra
  签名: : 余mpleteAtomic布尔ean代数 (有向图 V) where
  定义体: Digraph.completeDigraph V
  bot := Digraph.emptyDigraph V
  le_top _ _ _ _ := trivial
  bot_le _ _ _ h := h.elim
  inf_compl_le_bot _ _ _ h := absurd h.1 h.2
  top_le_sup_compl G v w _ := by tauto
  isLUB_sSup _ := ⟨fun G hG _ _ hab => ⟨G, hG, hab⟩, fun _ hG _ _ ⟨_, hH, hab⟩ => hG hH hab⟩
  isGLB_sInf _ := ⟨fun _ hG _ _ hab => hab hG, fun _ hG _ _ hab _ hH => hG hH hab⟩
  iInf_iSup_eq f := by ext; simp [Classical.skolem]

Depends on / 依赖: Digraph, Digraph.completeDigraph, completeDigraph
-/
instance completeAtomicBooleanAlgebra : CompleteAtomicBooleanAlgebra (Digraph V) where
  top := Digraph.completeDigraph V
  bot := Digraph.emptyDigraph V
  le_top _ _ _ _ := trivial
  bot_le _ _ _ h := h.elim
  inf_compl_le_bot _ _ _ h := absurd h.1 h.2
  top_le_sup_compl G v w _ := by tauto
  isLUB_sSup _ := ⟨fun G hG _ _ hab => ⟨G, hG, hab⟩, fun _ hG _ _ ⟨_, hH, hab⟩ => hG hH hab⟩
  isGLB_sInf _ := ⟨fun _ hG _ _ hab => hab hG, fun _ hG _ _ hab _ hH => hG hH hab⟩
  iInf_iSup_eq f := by ext; simp [Classical.skolem]

/--
theorem `top_adj` / 定理 `top_adj`

English:
theorem top_adj
  given: (v w : V)
  statement: (⊤ : Digraph V).Adj v w
  proof: trivial

中文:
定理 top_adj
  条件: (v w : V)
  结论: (⊤ : 有向图 V).伴随 v w
  证明: trivial
-/
@[simp] theorem top_adj (v w : V) : (⊤ : Digraph V).Adj v w := trivial

/--
theorem `bot_adj` / 定理 `bot_adj`

English:
theorem bot_adj
  given: (v w : V)
  statement: (⊥ : Digraph V).Adj v w ↔ False
  proof: Iff.rfl

中文:
定理 bot_adj
  条件: (v w : V)
  结论: (⊥ : 有向图 V).伴随 v w ↔ 假
  证明: Iff.rfl
-/
@[simp] theorem bot_adj (v w : V) : (⊥ : Digraph V).Adj v w ↔ False := Iff.rfl

/--
theorem `completeDigraph_eq_top` / 定理 `completeDigraph_eq_top`

English:
theorem completeDigraph_eq_top
  given: (V : Type*)
  statement: Digraph.completeDigraph V = ⊤
  proof: rfl

中文:
定理 completeDigraph_eq_top
  条件: (V : 类型)
  结论: 有向图.completeDigraph V = ⊤
  证明: rfl
-/
@[simp] theorem completeDigraph_eq_top (V : Type*) : Digraph.completeDigraph V = ⊤ := rfl

/--
theorem `emptyDigraph_eq_bot` / 定理 `emptyDigraph_eq_bot`

English:
theorem emptyDigraph_eq_bot
  given: (V : Type*)
  statement: Digraph.emptyDigraph V = ⊥
  proof: rfl

中文:
定理 emptyDigraph_eq_bot
  条件: (V : 类型)
  结论: 有向图.emptyDigraph V = ⊥
  证明: rfl
-/
@[simp] theorem emptyDigraph_eq_bot (V : Type*) : Digraph.emptyDigraph V = ⊥ := rfl

@[simps] instance (V : Type*) : Inhabited (Digraph V) := ⟨⊥⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsEmpty
  signature: V] : Unique (Digraph V) where
  body: ⊥
  uniq G := by ext1; congr!

中文:
实例 [是空
  签名: V] : 唯一 (有向图 V) where
  定义体: ⊥
  uniq G := by ext1; congr!
-/
instance [IsEmpty V] : Unique (Digraph V) where
  default := ⊥
  uniq G := by ext1; congr!

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Nonempty
  signature: V] : Nontrivial (Digraph V)
  body: by
  use ⊥, ⊤
  have v := Classical.arbitrary V
  exact ne_of_apply_ne (·.Adj v v) (by simp)

中文:
实例 [非空
  签名: V] : 非平凡 (有向图 V)
  定义体: by
  use ⊥, ⊤
  have v := Classical.arbitrary V
  exact ne_of_apply_ne (·.Adj v v) (by simp)

Depends on / 依赖: Classical, Classical.arbitrary, arbitrary, ne_of_apply_ne
-/
instance [Nonempty V] : Nontrivial (Digraph V) := by
  use ⊥, ⊤
  have v := Classical.arbitrary V
  exact ne_of_apply_ne (·.Adj v v) (by simp)

section Decidable

variable (V) (H : Digraph V) [DecidableRel G.Adj] [DecidableRel H.Adj]

/--
Instance `Bot.adjDecidable` / 实例 `Bot.adjDecidable`

English:
instance Bot.adjDecidable
  signature: : DecidableRel (⊥ : Digraph V).Adj
  body: inferInstanceAs DecidableRel fun _ _ => False

中文:
实例 底元素.adjDecidable
  签名: : DecidableRel (⊥ : 有向图 V).伴随
  定义体: inferInstanceAs DecidableRel fun _ _ => False

Depends on / 依赖: DecidableRel
-/
instance Bot.adjDecidable : DecidableRel (⊥ : Digraph V).Adj :=
inferInstanceAs DecidableRel fun _ _ => False

/--
Instance `Sup.adjDecidable` / 实例 `Sup.adjDecidable`

English:
instance Sup.adjDecidable
  signature: : DecidableRel (G ⊔ H).Adj
  body: inferInstanceAs DecidableRel fun v w => G.Adj v w ∨ H.Adj v w

中文:
实例 上确界.adjDecidable
  签名: : DecidableRel (G ⊔ H).伴随
  定义体: inferInstanceAs DecidableRel fun v w => G.Adj v w ∨ H.Adj v w

Depends on / 依赖: DecidableRel, G.Adj, H.Adj
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
实例 下确界.adjDecidable
  签名: : DecidableRel (G ⊓ H).伴随
  定义体: inferInstanceAs DecidableRel fun v w => G.Adj v w ∧ H.Adj v w

Depends on / 依赖: DecidableRel, G.Adj, H.Adj
-/
instance Inf.adjDecidable : DecidableRel (G ⊓ H).Adj :=
inferInstanceAs DecidableRel fun v w => G.Adj v w ∧ H.Adj v w

/--
Instance `SDiff.adjDecidable` / 实例 `SDiff.adjDecidable`

English:
instance SDiff.adjDecidable
  signature: : DecidableRel (G \ H).Adj
  body: inferInstanceAs DecidableRel fun v w => G.Adj v w ∧ ¬H.Adj v w

中文:
实例 对称差.adjDecidable
  签名: : DecidableRel (G \ H).伴随
  定义体: inferInstanceAs DecidableRel fun v w => G.Adj v w ∧ ¬H.Adj v w

Depends on / 依赖: DecidableRel, G.Adj, H.Adj
-/
instance SDiff.adjDecidable : DecidableRel (G \ H).Adj :=
inferInstanceAs DecidableRel fun v w => G.Adj v w ∧ ¬H.Adj v w

/--
Instance `Top.adjDecidable` / 实例 `Top.adjDecidable`

English:
instance Top.adjDecidable
  signature: : DecidableRel (⊤ : Digraph V).Adj
  body: inferInstanceAs DecidableRel fun _ _ => True

中文:
实例 顶元素.adjDecidable
  签名: : DecidableRel (⊤ : 有向图 V).伴随
  定义体: inferInstanceAs DecidableRel fun _ _ => True

Depends on / 依赖: DecidableRel
-/
instance Top.adjDecidable : DecidableRel (⊤ : Digraph V).Adj :=
inferInstanceAs DecidableRel fun _ _ => True

/--
Instance `Compl.adjDecidable` / 实例 `Compl.adjDecidable`

English:
instance Compl.adjDecidable
  signature: : DecidableRel (Gᶜ.Adj)
  body: inferInstanceAs DecidableRel fun v w => ¬G.Adj v w

中文:
实例 补集.adjDecidable
  签名: : DecidableRel (Gᶜ.伴随)
  定义体: inferInstanceAs DecidableRel fun v w => ¬G.Adj v w

Depends on / 依赖: DecidableRel, G.Adj
-/
instance Compl.adjDecidable : DecidableRel (Gᶜ.Adj) :=
inferInstanceAs DecidableRel fun v w => ¬G.Adj v w

end Decidable

end Order

end Digraph
