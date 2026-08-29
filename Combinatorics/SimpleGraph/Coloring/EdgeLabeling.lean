/-
Copyright (c) 2023 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Olivia Röhrig
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Data.Fintype.BigOperators

/-!
# Edge labelings

This module defines labelings of the edges of a graph.

## Main definitions

- `SimpleGraph.EdgeLabeling`: An assignment of a label from a given type to each edge of the graph.

- `SimpleGraph.EdgeLabeling.labelGraph`: the graph consisting of all edges with a given label.
-/

@[expose] public section

open Finset
open Fintype (card)

namespace SimpleGraph

variable {V V' : Type*} {G : SimpleGraph V} {G' : SimpleGraph V'} {K K' : Type*}

/--
Definition of `EdgeLabeling` / `EdgeLabeling` 的定义

English:
definition EdgeLabeling
  signature: (G : SimpleGraph V) (K : Type*)
  body: G.edgeSet -> K

中文:
定义 EdgeLabeling
  签名: (G : 简单图 V) (K : 类型)
  定义体: G.edgeSet -> K

Depends on / 依赖: G.edgeSet, edgeSet
-/
def EdgeLabeling (G : SimpleGraph V) (K : Type*) :=
  G.edgeSet -> K

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [DecidableEq
  signature: V] [Fintype G.edgeSet] [Fintype K] : Fintype (EdgeLabeling G K)
  body: inferInstanceAs Fintype (G.edgeSet -> K)

中文:
实例 [DecidableEq
  签名: V] [有限类型 G.edgeSet] [有限类型 K] : 有限类型 (EdgeLabeling G K)
  定义体: inferInstanceAs Fintype (G.edgeSet -> K)

Depends on / 依赖: Fintype, G.edgeSet, edgeSet
-/
instance [DecidableEq V] [Fintype G.edgeSet] [Fintype K] : Fintype (EdgeLabeling G K) :=
inferInstanceAs Fintype (G.edgeSet -> K)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Finite
  signature: G.edgeSet] [Finite K] : Finite (EdgeLabeling G K)
  body: Pi.finite

中文:
实例 [有限
  签名: G.edgeSet] [有限 K] : 有限 (EdgeLabeling G K)
  定义体: Pi.finite

Depends on / 依赖: Pi.finite, finite
-/
instance [Finite G.edgeSet] [Finite K] : Finite (EdgeLabeling G K) :=
  Pi.finite

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Nonempty
  signature: K] : Nonempty (EdgeLabeling G K)
  body: Pi.instNonempty

中文:
实例 [非空
  签名: K] : 非空 (EdgeLabeling G K)
  定义体: Pi.instNonempty

Depends on / 依赖: Pi.instNonempty, instNonempty
-/
instance [Nonempty K] : Nonempty (EdgeLabeling G K) :=
  Pi.instNonempty

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Inhabited
  signature: K] : Inhabited (EdgeLabeling G K)
  body: inferInstanceAs Inhabited (G.edgeSet -> K)

中文:
实例 [可居
  签名: K] : 可居 (EdgeLabeling G K)
  定义体: inferInstanceAs Inhabited (G.edgeSet -> K)

Depends on / 依赖: G.edgeSet, Inhabited, edgeSet
-/
instance [Inhabited K] : Inhabited (EdgeLabeling G K) :=
inferInstanceAs Inhabited (G.edgeSet -> K)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Subsingleton
  signature: K] : Subsingleton (EdgeLabeling G K)
  body: Pi.instSubsingleton

中文:
实例 [子单例
  签名: K] : 子单例 (EdgeLabeling G K)
  定义体: Pi.instSubsingleton

Depends on / 依赖: Pi.instSubsingleton, instSubsingleton
-/
instance [Subsingleton K] : Subsingleton (EdgeLabeling G K) :=
  Pi.instSubsingleton

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Nonempty
  signature: G.edgeSet] [Nontrivial K] : Nontrivial (EdgeLabeling G K)
  body: Function.nontrivial

中文:
实例 [非空
  签名: G.edgeSet] [非平凡 K] : 非平凡 (EdgeLabeling G K)
  定义体: Function.nontrivial

Depends on / 依赖: Function, Function.nontrivial, nontrivial
-/
instance [Nonempty G.edgeSet] [Nontrivial K] : Nontrivial (EdgeLabeling G K) :=
  Function.nontrivial

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Unique
  signature: K] : Unique (EdgeLabeling G K)
  body: inferInstanceAs Unique (G.edgeSet -> K)

中文:
实例 [唯一
  签名: K] : 唯一 (EdgeLabeling G K)
  定义体: inferInstanceAs Unique (G.edgeSet -> K)

Depends on / 依赖: G.edgeSet, Unique, edgeSet
-/
instance [Unique K] : Unique (EdgeLabeling G K) :=
inferInstanceAs Unique (G.edgeSet -> K)

/--
Definition of `TopEdgeLabeling` / `TopEdgeLabeling` 的定义

English:
abbreviation TopEdgeLabeling
  signature: (V K : Type*)
  body: EdgeLabeling (⊤ : SimpleGraph V) K

中文:
缩写 TopEdgeLabeling
  签名: (V K : 类型)
  定义体: EdgeLabeling (⊤ : SimpleGraph V) K

Depends on / 依赖: EdgeLabeling, SimpleGraph
-/
abbrev TopEdgeLabeling (V K : Type*) :=
  EdgeLabeling (⊤ : SimpleGraph V) K

/--
theorem `card_topEdgeLabeling` / 定理 `card_topEdgeLabeling`

English:
theorem card_topEdgeLabeling
  given: [DecidableEq V] [Fintype V] [Fintype K]
  proof: Fintype.card_fun.trans (by rw [← edgeFinset_card, card_edgeFinset_top_eq_card_choose_two])

中文:
定理 card_topEdgeLabeling
  条件: [DecidableEq V] [有限类型 V] [有限类型 K]
  证明: Fintype.card_fun.trans (by rw [← edgeFinset_card, card_edgeFinset_top_eq_card_choose_two])

Depends on / 依赖: Fintype, Fintype.card_fun.trans, card_edgeFinset_top_eq_card_choose_two, card_fun, edgeFinset_card
-/
theorem card_topEdgeLabeling [DecidableEq V] [Fintype V] [Fintype K] :
    card (TopEdgeLabeling V K) = card K ^ (card V).choose 2 :=
  Fintype.card_fun.trans (by rw [← edgeFinset_card, card_edgeFinset_top_eq_card_choose_two])

namespace EdgeLabeling

/--
Definition of `get` / `get` 的定义

English:
definition get
  signature: (C : EdgeLabeling G K) (x y : V) (h : G.Adj x y)
  body: C ⟨s(x, y), h⟩

中文:
定义 get
  签名: (C : EdgeLabeling G K) (x y : V) (h : G.伴随 x y)
  定义体: C ⟨s(x, y), h⟩
-/
def get (C : EdgeLabeling G K) (x y : V) (h : G.Adj x y) : K :=
  C ⟨s(x, y), h⟩

/--
lemma `get_eq` / 引理 `get_eq`

English:
lemma get_eq
  given: (C : EdgeLabeling G K) (x y : V) (h : G.Adj x y)
  statement: C.get x y h = C ⟨s(x, y), h⟩
  proof: rfl

中文:
引理 get_eq
  条件: (C : EdgeLabeling G K) (x y : V) (h : G.伴随 x y)
  结论: C.get x y h = C ⟨s(x, y), h⟩
  证明: rfl
-/
lemma get_eq (C : EdgeLabeling G K) (x y : V) (h : G.Adj x y) : C.get x y h = C ⟨s(x, y), h⟩ :=
  rfl

variable {C : EdgeLabeling G K}

/--
theorem `get_comm` / 定理 `get_comm`

English:
theorem get_comm
  given: (x y : V) (h)
  statement: C.get y x h = C.get x y h.symm
  proof: by
  simp [EdgeLabeling.get, Sym2.eq_swap]

@[ext]

中文:
定理 get_comm
  条件: (x y : V) (h)
  结论: C.get y x h = C.get x y h.symm
  证明: by
  simp [EdgeLabeling.get, Sym2.eq_swap]

@[ext]

Depends on / 依赖: EdgeLabeling, EdgeLabeling.get, Sym2.eq_swap, eq_swap
-/
theorem get_comm (x y : V) (h) : C.get y x h = C.get x y h.symm := by
  simp [EdgeLabeling.get, Sym2.eq_swap]

@[ext]
/--
theorem `ext_get` / 定理 `ext_get`

English:
theorem ext_get
  statement: {C' : EdgeLabeling G K}
  proof: by
  funext ⟨e, he⟩
  induction e using Sym2.inductionOn
  exact h _ _ he

中文:
定理 ext_get
  结论: {C' : EdgeLabeling G K}
  证明: by
  funext ⟨e, he⟩
  induction e using Sym2.inductionOn
  exact h _ _ he

Depends on / 依赖: Sym2.inductionOn, inductionOn
-/
theorem ext_get {C' : EdgeLabeling G K}
    (h : forall x y, (h : G.Adj x y) -> C.get x y h = C'.get x y h) : C = C' := by
  funext ⟨e, he⟩
  induction e using Sym2.inductionOn
  exact h _ _ he

/--
Definition of `compRight` / `compRight` 的定义

English:
definition compRight
  signature: (C : EdgeLabeling G K) (f : K -> K')
  body: f ∘ C

中文:
定义 compRight
  签名: (C : EdgeLabeling G K) (f : K -> K')
  定义体: f ∘ C
-/
def compRight (C : EdgeLabeling G K) (f : K -> K') : EdgeLabeling G K' :=
  f ∘ C

/--
Definition of `pullback` / `pullback` 的定义

English:
definition pullback
  signature: (C : EdgeLabeling G K) (f : G' ->g G)
  body: C ∘ f.mapEdgeSet

@[simp]

中文:
定义 pullback
  签名: (C : EdgeLabeling G K) (f : G' ->g G)
  定义体: C ∘ f.mapEdgeSet

@[simp]

Depends on / 依赖: f.mapEdgeSet, mapEdgeSet
-/
def pullback (C : EdgeLabeling G K) (f : G' ->g G) : EdgeLabeling G' K :=
  C ∘ f.mapEdgeSet

@[simp]
/--
theorem `pullback_apply` / 定理 `pullback_apply`

English:
theorem pullback_apply
  given: {f : G' ->g G} e
  statement: C.pullback f e = C (f.mapEdgeSet e)
  proof: rfl

@[simp]

中文:
定理 pullback_apply
  条件: {f : G' ->g G} e
  结论: C.pullback f e = C (f.mapEdgeSet e)
  证明: rfl

@[simp]
-/
theorem pullback_apply {f : G' ->g G} e : C.pullback f e = C (f.mapEdgeSet e) :=
  rfl

@[simp]
/--
theorem `get_pullback` / 定理 `get_pullback`

English:
theorem get_pullback
  given: {f : G' ↪g G} (x y) (h : G'.Adj x y)
  proof: rfl

@[simp]

中文:
定理 get_pullback
  条件: {f : G' ↪g G} (x y) (h : G'.伴随 x y)
  证明: rfl

@[simp]
-/
theorem get_pullback {f : G' ↪g G} (x y) (h : G'.Adj x y) :
    (C.pullback f).get x y h = C.get (f x) (f y) (by simpa) :=
  rfl

@[simp]
/--
theorem `compRight_apply` / 定理 `compRight_apply`

English:
theorem compRight_apply
  given: (f : K -> K') (e)
  statement: C.compRight f e = f (C e)
  proof: rfl

@[simp]

中文:
定理 compRight_apply
  条件: (f : K -> K') (e)
  结论: C.compRight f e = f (C e)
  证明: rfl

@[simp]
-/
theorem compRight_apply (f : K -> K') (e) : C.compRight f e = f (C e) :=
  rfl

@[simp]
/--
theorem `compRight_get` / 定理 `compRight_get`

English:
theorem compRight_get
  given: (f : K -> K') (x y) (h : G.Adj x y)
  proof: rfl

中文:
定理 compRight_get
  条件: (f : K -> K') (x y) (h : G.伴随 x y)
  证明: rfl
-/
theorem compRight_get (f : K -> K') (x y) (h : G.Adj x y) :
    (C.compRight f).get x y h = f (C.get x y h) :=
  rfl

/--
Definition of `mk` / `mk` 的定义

English:
definition mk
  signature: (f : forall x y : V, G.Adj x y -> K)

中文:
定义 mk
  签名: (f : 对任意 x y : V, G.伴随 x y -> K)
-/
def mk (f : forall x y : V, G.Adj x y -> K)
    (f_symm : forall (x y : V) (H : G.Adj x y), f y x H.symm = f x y H) : EdgeLabeling G K
  | ⟨e, he⟩ => by
    revert he
    refine Sym2.hrec f (fun a b => ?_) e
    apply Function.hfunext (by simp [adj_comm])
    grind

/--
theorem `get_mk` / 定理 `get_mk`

English:
theorem get_mk
  given: (f : forall x y : V, G.Adj x y -> K) (f_symm) (x y : V) (h : G.Adj x y)
  proof: rfl

中文:
定理 get_mk
  条件: (f : 对任意 x y : V, G.伴随 x y -> K) (f_symm) (x y : V) (h : G.伴随 x y)
  证明: rfl
-/
theorem get_mk (f : forall x y : V, G.Adj x y -> K) (f_symm) (x y : V) (h : G.Adj x y) :
    (mk f f_symm).get x y h = f x y h :=
  rfl

/--
Definition of `labelGraph` / `labelGraph` 的定义

English:
definition labelGraph
  signature: (C : EdgeLabeling G K) (k : K)
  body: SimpleGraph.fromEdgeSet {e | exists h : e in G.edgeSet, C ⟨e, h⟩ = k}

中文:
定义 labelGraph
  签名: (C : EdgeLabeling G K) (k : K)
  定义体: SimpleGraph.fromEdgeSet {e | exists h : e in G.edgeSet, C ⟨e, h⟩ = k}

Depends on / 依赖: G.edgeSet, SimpleGraph, SimpleGraph.fromEdgeSet, edgeSet, fromEdgeSet
-/
def labelGraph (C : EdgeLabeling G K) (k : K) : SimpleGraph V :=
  SimpleGraph.fromEdgeSet {e | exists h : e in G.edgeSet, C ⟨e, h⟩ = k}

/--
theorem `labelGraph_adj` / 定理 `labelGraph_adj`

English:
theorem labelGraph_adj
  given: {C : EdgeLabeling G K} {k : K} (x y : V)
  proof: by
  rw [EdgeLabeling.labelGraph]
  simp only [mem_edgeSet, fromEdgeSet_adj, Set.mem_ofPred_eq, Ne.eq_def]
  grind [Adj.ne]

中文:
定理 labelGraph_adj
  条件: {C : EdgeLabeling G K} {k : K} (x y : V)
  证明: by
  rw [EdgeLabeling.labelGraph]
  simp only [mem_edgeSet, fromEdgeSet_adj, Set.mem_ofPred_eq, Ne.eq_def]
  grind [Adj.ne]

Depends on / 依赖: Adj.ne, EdgeLabeling, EdgeLabeling.labelGraph, Ne.eq_def, Set.mem_ofPred_eq, eq_def, fromEdgeSet_adj, labelGraph, mem_edgeSet, mem_ofPred_eq
-/
theorem labelGraph_adj {C : EdgeLabeling G K} {k : K} (x y : V) :
    (C.labelGraph k).Adj x y ↔ exists H : G.Adj x y, C ⟨s(x, y), H⟩ = k := by
  rw [EdgeLabeling.labelGraph]
  simp only [mem_edgeSet, fromEdgeSet_adj, Set.mem_ofPred_eq, Ne.eq_def]
  grind [Adj.ne]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [DecidableRel
  signature: G.Adj] [DecidableEq K] (k
  body: fun _ _ =>
  decidable_of_iff' _ (EdgeLabeling.labelGraph_adj _ _)

中文:
实例 [DecidableRel
  签名: G.伴随] [DecidableEq K] (k
  定义体: fun _ _ =>
  decidable_of_iff' _ (EdgeLabeling.labelGraph_adj _ _)
-/
instance [DecidableRel G.Adj] [DecidableEq K] (k : K) {C : EdgeLabeling G K} :
    DecidableRel (C.labelGraph k).Adj := fun _ _ =>
  decidable_of_iff' _ (EdgeLabeling.labelGraph_adj _ _)

/--
theorem `labelGraph_le` / 定理 `labelGraph_le`

English:
theorem labelGraph_le
  given: (C : EdgeLabeling G K) {k : K}
  statement: C.labelGraph k <= G
  proof: by
  intro x y
  grind [labelGraph_adj]

中文:
定理 labelGraph_le
  条件: (C : EdgeLabeling G K) {k : K}
  结论: C.labelGraph k <= G
  证明: by
  intro x y
  grind [labelGraph_adj]

Depends on / 依赖: labelGraph_adj
-/
theorem labelGraph_le (C : EdgeLabeling G K) {k : K} : C.labelGraph k <= G := by
  intro x y
  grind [labelGraph_adj]

/--
theorem `pairwise_disjoint_labelGraph` / 定理 `pairwise_disjoint_labelGraph`

English:
theorem pairwise_disjoint_labelGraph
  given: {C : EdgeLabeling G K}
  proof: by
  intro _ _ h
  rw [disjoint_left]
  grind [labelGraph_adj]

中文:
定理 pairwise_disjoint_labelGraph
  条件: {C : EdgeLabeling G K}
  证明: by
  intro _ _ h
  rw [disjoint_left]
  grind [labelGraph_adj]

Depends on / 依赖: disjoint_left, labelGraph_adj
-/
theorem pairwise_disjoint_labelGraph {C : EdgeLabeling G K} :
    Pairwise fun k l => Disjoint (C.labelGraph k) (C.labelGraph l) := by
  intro _ _ h
  rw [disjoint_left]
  grind [labelGraph_adj]

/--
theorem `pairwiseDisjoint_univ_labelGraph` / 定理 `pairwiseDisjoint_univ_labelGraph`

English:
theorem pairwiseDisjoint_univ_labelGraph
  given: {C : EdgeLabeling G K}
  proof: by
  intro _ _ _ _ h
  exact pairwise_disjoint_labelGraph h

中文:
定理 pairwiseDisjoint_univ_labelGraph
  条件: {C : EdgeLabeling G K}
  证明: by
  intro _ _ _ _ h
  exact pairwise_disjoint_labelGraph h

Depends on / 依赖: pairwise_disjoint_labelGraph
-/
theorem pairwiseDisjoint_univ_labelGraph {C : EdgeLabeling G K} :
    Set.PairwiseDisjoint (@Set.univ K) C.labelGraph := by
  intro _ _ _ _ h
  exact pairwise_disjoint_labelGraph h

/--
theorem `iSup_labelGraph` / 定理 `iSup_labelGraph`

English:
theorem iSup_labelGraph
  given: (C : EdgeLabeling G K)
  statement: ⨆ k : K, C.labelGraph k = G
  proof: by
  ext x y
  simp only [iSup_adj, EdgeLabeling.labelGraph_adj]
  grind

中文:
定理 iSup_labelGraph
  条件: (C : EdgeLabeling G K)
  结论: ⨆ k : K, C.labelGraph k = G
  证明: by
  ext x y
  simp only [iSup_adj, EdgeLabeling.labelGraph_adj]
  grind

Depends on / 依赖: EdgeLabeling, EdgeLabeling.labelGraph_adj, iSup_adj, labelGraph_adj
-/
theorem iSup_labelGraph (C : EdgeLabeling G K) : ⨆ k : K, C.labelGraph k = G := by
  ext x y
  simp only [iSup_adj, EdgeLabeling.labelGraph_adj]
  grind

end EdgeLabeling

namespace TopEdgeLabeling

/--
Definition of `pullback` / `pullback` 的定义

English:
abbreviation pullback
  signature: (C : TopEdgeLabeling V K) (f : V' ↪ V)
  body: EdgeLabeling.pullback C ⟨f, by simp⟩

@[simp]

中文:
缩写 pullback
  签名: (C : TopEdgeLabeling V K) (f : V' ↪ V)
  定义体: EdgeLabeling.pullback C ⟨f, by simp⟩

@[simp]

Depends on / 依赖: EdgeLabeling, EdgeLabeling.pullback, pullback
-/
abbrev pullback (C : TopEdgeLabeling V K) (f : V' ↪ V) : TopEdgeLabeling V' K :=
  EdgeLabeling.pullback C ⟨f, by simp⟩

@[simp]
/--
theorem `labelGraph_adj` / 定理 `labelGraph_adj`

English:
theorem labelGraph_adj
  given: {C : TopEdgeLabeling V K} {k : K} (x y : V)
  proof: by
  simp [EdgeLabeling.labelGraph_adj, EdgeLabeling.get_eq]

中文:
定理 labelGraph_adj
  条件: {C : TopEdgeLabeling V K} {k : K} (x y : V)
  证明: by
  simp [EdgeLabeling.labelGraph_adj, EdgeLabeling.get_eq]

Depends on / 依赖: EdgeLabeling, EdgeLabeling.get_eq, EdgeLabeling.labelGraph_adj, get_eq, labelGraph_adj
-/
theorem labelGraph_adj {C : TopEdgeLabeling V K} {k : K} (x y : V) :
    (C.labelGraph k).Adj x y ↔ exists H : x != y, C.get x y H = k := by
  simp [EdgeLabeling.labelGraph_adj, EdgeLabeling.get_eq]

end TopEdgeLabeling

/--
Definition of `toTopEdgeLabeling` / `toTopEdgeLabeling` 的定义

English:
definition toTopEdgeLabeling
  signature: (G : SimpleGraph V) [DecidableRel G.Adj]
  body: EdgeLabeling.mk (fun x y _ => if G.Adj x y then 1 else 0) (by simp [G.adj_comm])

@[simp]

中文:
定义 toTopEdgeLabeling
  签名: (G : 简单图 V) [DecidableRel G.伴随]
  定义体: EdgeLabeling.mk (fun x y _ => if G.Adj x y then 1 else 0) (by simp [G.adj_comm])

@[simp]

Depends on / 依赖: EdgeLabeling, EdgeLabeling.mk, G.Adj, G.adj_comm, adj_comm
-/
def toTopEdgeLabeling (G : SimpleGraph V) [DecidableRel G.Adj] : TopEdgeLabeling V (Fin 2) :=
  EdgeLabeling.mk (fun x y _ => if G.Adj x y then 1 else 0) (by simp [G.adj_comm])

@[simp]
/--
theorem `toTopEdgeLabeling_get` / 定理 `toTopEdgeLabeling_get`

English:
theorem toTopEdgeLabeling_get
  given: {G : SimpleGraph V} [DecidableRel G.Adj] {x y : V} (H : x != y)
  proof: rfl

@[simp]

中文:
定理 toTopEdgeLabeling_get
  条件: {G : 简单图 V} [DecidableRel G.伴随] {x y : V} (H : x != y)
  证明: rfl

@[simp]
-/
theorem toTopEdgeLabeling_get {G : SimpleGraph V} [DecidableRel G.Adj] {x y : V} (H : x != y) :
    G.toTopEdgeLabeling.get x y H = if G.Adj x y then 1 else 0 :=
  rfl

@[simp]
/--
theorem `toTopEdgeLabeling_labelGraph` / 定理 `toTopEdgeLabeling_labelGraph`

English:
theorem toTopEdgeLabeling_labelGraph
  given: (G : SimpleGraph V) [DecidableRel G.Adj]
  proof: by ext x y; simpa [imp_false] using G.ne_of_adj

@[simp]

中文:
定理 toTopEdgeLabeling_labelGraph
  条件: (G : 简单图 V) [DecidableRel G.伴随]
  证明: by ext x y; simpa [imp_false] using G.ne_of_adj

@[simp]

Depends on / 依赖: G.ne_of_adj, imp_false, ne_of_adj
-/
theorem toTopEdgeLabeling_labelGraph (G : SimpleGraph V) [DecidableRel G.Adj] :
    G.toTopEdgeLabeling.labelGraph 1 = G := by ext x y; simpa [imp_false] using G.ne_of_adj

@[simp]
/--
theorem `toTopEdgeLabeling_labelGraph_compl` / 定理 `toTopEdgeLabeling_labelGraph_compl`

English:
theorem toTopEdgeLabeling_labelGraph_compl
  given: (G : SimpleGraph V) [DecidableRel G.Adj]
  proof: by ext x y; simp [imp_false]

中文:
定理 toTopEdgeLabeling_labelGraph_compl
  条件: (G : 简单图 V) [DecidableRel G.伴随]
  证明: by ext x y; simp [imp_false]

Depends on / 依赖: imp_false
-/
theorem toTopEdgeLabeling_labelGraph_compl (G : SimpleGraph V) [DecidableRel G.Adj] :
    G.toTopEdgeLabeling.labelGraph 0 = Gᶜ := by ext x y; simp [imp_false]

/--
theorem `TopEdgeLabeling.labelGraph_toTopEdgeLabeling` / 定理 `TopEdgeLabeling.labelGraph_toTopEdgeLabeling`

English:
theorem TopEdgeLabeling.labelGraph_toTopEdgeLabeling
  statement: [DecidableEq V]
  proof: by
  refine EdgeLabeling.ext_get ?_
  grind [toTopEdgeLabeling_get, TopEdgeLabeling.labelGraph_adj, Adj.ne]

中文:
定理 TopEdgeLabeling.labelGraph_toTopEdgeLabeling
  结论: [DecidableEq V]
  证明: by
  refine EdgeLabeling.ext_get ?_
  grind [toTopEdgeLabeling_get, TopEdgeLabeling.labelGraph_adj, Adj.ne]

Depends on / 依赖: Adj.ne, EdgeLabeling, EdgeLabeling.ext_get, TopEdgeLabeling, TopEdgeLabeling.labelGraph_adj, ext_get, labelGraph_adj, toTopEdgeLabeling_get
-/
theorem TopEdgeLabeling.labelGraph_toTopEdgeLabeling [DecidableEq V]
    (C : TopEdgeLabeling V (Fin 2)) : (C.labelGraph 1).toTopEdgeLabeling = C := by
  refine EdgeLabeling.ext_get ?_
  grind [toTopEdgeLabeling_get, TopEdgeLabeling.labelGraph_adj, Adj.ne]

end SimpleGraph
