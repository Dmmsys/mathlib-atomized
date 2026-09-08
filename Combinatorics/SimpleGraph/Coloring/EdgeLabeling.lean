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

/-- An edge labeling of a simple graph `G` with labels in type `K`. Sometimes this is called an
edge-coloring, but we reserve that terminology for labelings where incident edges cannot share a
label.
-/
/-
**SimpleGraph.EdgeLabeling** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph`。
形式化陈述：EdgeLabeling (G : SimpleGraph V) (K : Type*)
参数：G : SimpleGraph V；K : Type*。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An edge labeling of a simple graph `G` with labels in type `K`. Sometimes this i
s called an
edge-coloring, but we reserve that terminology for labelings where incident edge
s cannot share a
label.
-/
def EdgeLabeling (G : SimpleGraph V) (K : Type*) :=
  G.edgeSet → K
/-
**SimpleGraph.** 是 Mathlib 中的一个实例，位于命名空间 `SimpleGraph`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [DecidableEq V] [Fintype G.edgeSet] [Fintype K] : Fintype (EdgeLabeling G K) :=
  inferInstanceAs <| Fintype (G.edgeSet → K)
/-
**SimpleGraph.** 是 Mathlib 中的一个实例，位于命名空间 `SimpleGraph`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Finite G.edgeSet] [Finite K] : Finite (EdgeLabeling G K) :=
  Pi.finite
/-
**SimpleGraph.** 是 Mathlib 中的一个实例，位于命名空间 `SimpleGraph`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Nonempty K] : Nonempty (EdgeLabeling G K) :=
  Pi.instNonempty
/-
**SimpleGraph.** 是 Mathlib 中的一个实例，位于命名空间 `SimpleGraph`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Inhabited K] : Inhabited (EdgeLabeling G K) :=
  inferInstanceAs <| Inhabited (G.edgeSet → K)
/-
**SimpleGraph.** 是 Mathlib 中的一个实例，位于命名空间 `SimpleGraph`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Subsingleton K] : Subsingleton (EdgeLabeling G K) :=
  Pi.instSubsingleton
/-
**SimpleGraph.** 是 Mathlib 中的一个实例，位于命名空间 `SimpleGraph`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Nonempty G.edgeSet] [Nontrivial K] : Nontrivial (EdgeLabeling G K) :=
  Function.nontrivial
/-
**SimpleGraph.** 是 Mathlib 中的一个实例，位于命名空间 `SimpleGraph`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Unique K] : Unique (EdgeLabeling G K) :=
  inferInstanceAs <| Unique (G.edgeSet → K)

/--
An edge labeling of the complete graph on `V` with labels in type `K`.
-/
/-
**SimpleGraph.TopEdgeLabeling** 是 Mathlib 中的一个缩写定义，位于命名空间 `SimpleGraph`。
形式化陈述：TopEdgeLabeling (V K : Type*)
参数：V K : Type*。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An edge labeling of the complete graph on `V` with labels in type `K`.
-/
abbrev TopEdgeLabeling (V K : Type*) :=
  EdgeLabeling (⊤ : SimpleGraph V) K
/-
**SimpleGraph.card_topEdgeLabeling** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：card_topEdgeLabeling [DecidableEq V] [Fintype V] [Fintype K] : card (TopEd
geLabeling V K) = card K ^ (card V).choose 2
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Fintype.card_fun`：Fintype.card_fun [DecidableEq α] [Fintype α] [Fintype 
β] : Fintype.card (α -> β) = Fintype.card β ^ Fintype.card α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SimpleGraph.edgeFinset_card`：edgeFinset_card : #G.edgeFinset = Fintype.c
ard G.edgeSet
· 使用定理 `SimpleGraph.card_edgeFinset_top_eq_card_choose_two`：card_edgeFinset_top_
eq_card_choose_two [DecidableEq V] : #(⊤ : SimpleGraph V).edgeFinset = (Fintype.
card V).choose 2
-/
theorem card_topEdgeLabeling [DecidableEq V] [Fintype V] [Fintype K] :
    card (TopEdgeLabeling V K) = card K ^ (card V).choose 2 :=
  Fintype.card_fun.trans (by rw [← edgeFinset_card, card_edgeFinset_top_eq_card_choose_two])

namespace EdgeLabeling

/--
Convenience function to get the color of the edge `x ~ y` in the coloring of the complete graph
on `V`.
-/
/-
**SimpleGraph.EdgeLabeling.get** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph.EdgeLabeli
ng`。
形式化陈述：get (C : EdgeLabeling G K) (x y : V) (h : G.Adj x y) : K
参数：C : EdgeLabeling G K；x y : V；h : G.Adj x y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Convenience function to get the color of the edge `x ~ y` in the coloring of the
 complete graph
on `V`.
-/
def get (C : EdgeLabeling G K) (x y : V) (h : G.Adj x y) : K :=
  C ⟨s(x, y), h⟩
/-
**SimpleGraph.EdgeLabeling.get_eq** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph.EdgeLab
eling`。
形式化陈述：get_eq (C : EdgeLabeling G K) (x y : V) (h : G.Adj x y) : C.get x y h = C 
⟨s(x, y), h⟩
参数：C : EdgeLabeling G K；x y : V；h : G.Adj x y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma get_eq (C : EdgeLabeling G K) (x y : V) (h : G.Adj x y) : C.get x y h = C ⟨s(x, y), h⟩ :=
  rfl

variable {C : EdgeLabeling G K}
/-
**SimpleGraph.EdgeLabeling.get_comm** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.EdgeL
abeling`。
形式化陈述：get_comm (x y : V) (h) : C.get y x h = C.get x y h.symm
参数：x y : V；h。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `SimpleGraph.Adj.symm`：∀ {V : Type u} {G : SimpleGraph V} {u v : V}, G.Ad
j u v → G.Adj v u
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Sym2.eq_swap`：eq_swap {a b : α} : s(a, b) = s(b, a)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subtype.mk.congr_simp`：∀ {α : Sort u} {p : α → Prop} (val val_1 : α) (e_
val : val = val_1) (property : p val), ⟨val, property⟩ = ⟨val_1, ⋯⟩
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem get_comm (x y : V) (h) : C.get y x h = C.get x y h.symm := by
  simp [EdgeLabeling.get, Sym2.eq_swap]

@[ext]
/-
**SimpleGraph.EdgeLabeling.ext_get** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.EdgeLa
beling`。
形式化陈述：ext_get {C' : EdgeLabeling G K} (h : forall x y, (h : G.Adj x y) -> C.get 
x y h = C'.get x y h) : C = C'
参数：h : forall x y, (h : G.Adj x y) -> C.get x y h = C'.get x y h。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Sym2.inductionOn`：∀ {α : Type u_1} {f : Sym2 α → Prop} (i : Sym2 α), (∀ 
(x y : α), f s(x, y)) → f i
-/
theorem ext_get {C' : EdgeLabeling G K}
    (h : ∀ x y, (h : G.Adj x y) → C.get x y h = C'.get x y h) : C = C' := by
  funext ⟨e, he⟩
  induction e using Sym2.inductionOn
  exact h _ _ he

/-- Compose an edge-labeling with a function on the color set. -/
/-
**SimpleGraph.EdgeLabeling.compRight** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph.Edge
Labeling`。
形式化陈述：compRight (C : EdgeLabeling G K) (f : K -> K') : EdgeLabeling G K'
参数：C : EdgeLabeling G K；f : K -> K'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Compose an edge-labeling with a function on the color set.
-/
def compRight (C : EdgeLabeling G K) (f : K → K') : EdgeLabeling G K' :=
  f ∘ C

/-- Compose an edge-labeling with a graph embedding. -/
/-
**SimpleGraph.EdgeLabeling.pullback** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph.EdgeL
abeling`。
形式化陈述：pullback (C : EdgeLabeling G K) (f : G' ->g G) : EdgeLabeling G' K
参数：C : EdgeLabeling G K；f : G' ->g G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Compose an edge-labeling with a graph embedding.
-/
def pullback (C : EdgeLabeling G K) (f : G' →g G) : EdgeLabeling G' K :=
  C ∘ f.mapEdgeSet

@[simp]
/-
**SimpleGraph.EdgeLabeling.pullback_apply** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph
.EdgeLabeling`。
形式化陈述：pullback_apply {f : G' ->g G} e : C.pullback f e = C (f.mapEdgeSet e)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem pullback_apply {f : G' →g G} e : C.pullback f e = C (f.mapEdgeSet e) :=
  rfl

@[simp]
/-
**SimpleGraph.EdgeLabeling.get_pullback** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.E
dgeLabeling`。
形式化陈述：get_pullback {f : G' ↪g G} (x y) (h : G'.Adj x y) : (C.pullback f).get x y
 h = C.get (f x) (f y) (by simpa)
参数：x y；h : G'.Adj x y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem get_pullback {f : G' ↪g G} (x y) (h : G'.Adj x y) :
    (C.pullback f).get x y h = C.get (f x) (f y) (by simpa) :=
  rfl

@[simp]
/-
**SimpleGraph.EdgeLabeling.compRight_apply** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGrap
h.EdgeLabeling`。
形式化陈述：compRight_apply (f : K -> K') (e) : C.compRight f e = f (C e)
参数：f : K -> K'；e。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem compRight_apply (f : K → K') (e) : C.compRight f e = f (C e) :=
  rfl

@[simp]
/-
**SimpleGraph.EdgeLabeling.compRight_get** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.
EdgeLabeling`。
形式化陈述：compRight_get (f : K -> K') (x y) (h : G.Adj x y) : (C.compRight f).get x 
y h = f (C.get x y h)
参数：f : K -> K'；x y；h : G.Adj x y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem compRight_get (f : K → K') (x y) (h : G.Adj x y) :
    (C.compRight f).get x y h = f (C.get x y h) :=
  rfl

/-- Construct an edge labeling from a symmetric function on adjacent vertices. -/
/-
**SimpleGraph.EdgeLabeling.mk** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph.EdgeLabelin
g`。
形式化陈述：{V : Type u_1} →   {G : SimpleGraph V} →     {K : Type u_3} →       (f : (
x y : V) → G.Adj x y → K) → (∀ (x y : V) (H : G.Adj x y), f y x ⋯ = f x y H) → G
.EdgeLabeling K
参数：f : (x y : V) → G.Adj x y → K；∀ (x y : V) (H : G.Adj x y), f y x ⋯ = f x y H。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Adj.symm`：∀ {V : Type u} {G : SimpleGraph V} {u v : V}, G.Ad
j u v → G.Adj v u

--- 原说明 ---
Construct an edge labeling from a symmetric function on adjacent vertices.
-/
def mk (f : ∀ x y : V, G.Adj x y → K)
    (f_symm : ∀ (x y : V) (H : G.Adj x y), f y x H.symm = f x y H) : EdgeLabeling G K
  | ⟨e, he⟩ => by
    revert he
    refine Sym2.hrec f (fun a b ↦ ?_) e
    apply Function.hfunext (by simp [adj_comm])
    grind
/-
**SimpleGraph.EdgeLabeling.get_mk** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.EdgeLab
eling`。
形式化陈述：get_mk (f : forall x y : V, G.Adj x y -> K) (f_symm) (x y : V) (h : G.Adj 
x y) : (mk f f_symm).get x y h = f x y h
参数：f : forall x y : V, G.Adj x y -> K；f_symm；x y : V；h : G.Adj x y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Adj.symm`：∀ {V : Type u} {G : SimpleGraph V} {u v : V}, G.Ad
j u v → G.Adj v u
-/
theorem get_mk (f : ∀ x y : V, G.Adj x y → K) (f_symm) (x y : V) (h : G.Adj x y) :
    (mk f f_symm).get x y h = f x y h :=
  rfl

/--
Given an edge labeling and a choice of label `k`, construct the graph corresponding to the edges
labeled `k`.
-/
/-
**SimpleGraph.EdgeLabeling.labelGraph** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph.Edg
eLabeling`。
形式化陈述：labelGraph (C : EdgeLabeling G K) (k : K) : SimpleGraph V
参数：C : EdgeLabeling G K；k : K。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given an edge labeling and a choice of label `k`, construct the graph correspond
ing to the edges
labeled `k`.
-/
def labelGraph (C : EdgeLabeling G K) (k : K) : SimpleGraph V :=
  SimpleGraph.fromEdgeSet {e | ∃ h : e ∈ G.edgeSet, C ⟨e, h⟩ = k}
/-
**SimpleGraph.EdgeLabeling.labelGraph_adj** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph
.EdgeLabeling`。
形式化陈述：labelGraph_adj {C : EdgeLabeling G K} {k : K} (x y : V) : (C.labelGraph k)
.Adj x y ↔ exists H : G.Adj x y, C ⟨s(x, y), H⟩ = k
参数：x y : V。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.EdgeLabeling.labelGraph.eq_1`：∀ {V : Type u_1} {G : SimpleGr
aph V} {K : Type u_3} (C : G.EdgeLabeling K) (k : K),   C.labelGraph k = SimpleG
raph.fromEdgeSet {e | ∃ (h : e…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
-/
theorem labelGraph_adj {C : EdgeLabeling G K} {k : K} (x y : V) :
    (C.labelGraph k).Adj x y ↔ ∃ H : G.Adj x y, C ⟨s(x, y), H⟩ = k := by
  rw [EdgeLabeling.labelGraph]
  simp only [mem_edgeSet, fromEdgeSet_adj, Set.mem_ofPred_eq, Ne.eq_def]
  grind [Adj.ne]
/-
**SimpleGraph.EdgeLabeling.** 是 Mathlib 中的一个实例，位于命名空间 `SimpleGraph.EdgeLabeling`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [DecidableRel G.Adj] [DecidableEq K] (k : K) {C : EdgeLabeling G K} :
    DecidableRel (C.labelGraph k).Adj := fun _ _ =>
  decidable_of_iff' _ (EdgeLabeling.labelGraph_adj _ _)
/-
**SimpleGraph.EdgeLabeling.labelGraph_le** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.
EdgeLabeling`。
形式化陈述：labelGraph_le (C : EdgeLabeling G K) {k : K} : C.labelGraph k <= G
参数：C : EdgeLabeling G K。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem labelGraph_le (C : EdgeLabeling G K) {k : K} : C.labelGraph k ≤ G := by
  intro x y
  grind [labelGraph_adj]
/-
**SimpleGraph.EdgeLabeling.pairwise_disjoint_labelGraph** 是 Mathlib 中的一个定理，位于命名空
间 `SimpleGraph.EdgeLabeling`。
形式化陈述：pairwise_disjoint_labelGraph {C : EdgeLabeling G K} : Pairwise fun k l => 
Disjoint (C.labelGraph k) (C.labelGraph l)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.disjoint_left`：disjoint_left {G H : SimpleGraph V} : Disjoin
t G H ↔ forall x y, G.Adj x y -> ¬H.Adj x y
-/
theorem pairwise_disjoint_labelGraph {C : EdgeLabeling G K} :
    Pairwise fun k l ↦ Disjoint (C.labelGraph k) (C.labelGraph l) := by
  intro _ _ h
  rw [disjoint_left]
  grind [labelGraph_adj]
/-
**SimpleGraph.EdgeLabeling.pairwiseDisjoint_univ_labelGraph** 是 Mathlib 中的一个定理，位
于命名空间 `SimpleGraph.EdgeLabeling`。
形式化陈述：pairwiseDisjoint_univ_labelGraph {C : EdgeLabeling G K} : Set.PairwiseDisj
oint (@Set.univ K) C.labelGraph
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.EdgeLabeling.pairwise_disjoint_labelGraph`：pairwise_disjoint
_labelGraph {C : EdgeLabeling G K} : Pairwise fun k l => Disjoint (C.labelGraph 
k) (C.labelGraph l)
-/
theorem pairwiseDisjoint_univ_labelGraph {C : EdgeLabeling G K} :
    Set.PairwiseDisjoint (@Set.univ K) C.labelGraph := by
  intro _ _ _ _ h
  exact pairwise_disjoint_labelGraph h
/-
**SimpleGraph.EdgeLabeling.iSup_labelGraph** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGrap
h.EdgeLabeling`。
形式化陈述：iSup_labelGraph (C : EdgeLabeling G K) : ⨆ k : K, C.labelGraph k = G
参数：C : EdgeLabeling G K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.ext`：∀ {V : Type u} {x y : SimpleGraph V}, x.Adj = y.Adj → x
 = y
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
-/
theorem iSup_labelGraph (C : EdgeLabeling G K) : ⨆ k : K, C.labelGraph k = G := by
  ext x y
  simp only [iSup_adj, EdgeLabeling.labelGraph_adj]
  grind

end EdgeLabeling

namespace TopEdgeLabeling

/-- Compose an edge-labeling, by an injection into the vertex type. This must be an injection, else
we don't know how to color `x ~ y` in the case `f x = f y`.
-/
/-
**SimpleGraph.TopEdgeLabeling.pullback** 是 Mathlib 中的一个缩写定义，位于命名空间 `SimpleGraph.
TopEdgeLabeling`。
形式化陈述：pullback (C : TopEdgeLabeling V K) (f : V' ↪ V) : TopEdgeLabeling V' K
参数：C : TopEdgeLabeling V K；f : V' ↪ V。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Compose an edge-labeling, by an injection into the vertex type. This must be an 
injection, else
we don't know how to color `x ~ y` in the case `f x = f y`.
-/
abbrev pullback (C : TopEdgeLabeling V K) (f : V' ↪ V) : TopEdgeLabeling V' K :=
  EdgeLabeling.pullback C ⟨f, by simp⟩

@[simp]
/-
**SimpleGraph.TopEdgeLabeling.labelGraph_adj** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGr
aph.TopEdgeLabeling`。
形式化陈述：labelGraph_adj {C : TopEdgeLabeling V K} {k : K} (x y : V) : (C.labelGraph
 k).Adj x y ↔ exists H : x != y, C.get x y H = k
参数：x y : V。
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
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem labelGraph_adj {C : TopEdgeLabeling V K} {k : K} (x y : V) :
    (C.labelGraph k).Adj x y ↔ ∃ H : x ≠ y, C.get x y H = k := by
  simp [EdgeLabeling.labelGraph_adj, EdgeLabeling.get_eq]

end TopEdgeLabeling

/--
From a simple graph on `V`, construct the edge labeling on the complete graph of `V` given where
edges are labeled `1` and non-edges are labeled `0`.
-/
/-
**SimpleGraph.toTopEdgeLabeling** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph`。
形式化陈述：toTopEdgeLabeling (G : SimpleGraph V) [DecidableRel G.Adj] : TopEdgeLabeli
ng V (Fin 2)
参数：G : SimpleGraph V。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
From a simple graph on `V`, construct the edge labeling on the complete graph of
 `V` given where
edges are labeled `1` and non-edges are labeled `0`.
-/
def toTopEdgeLabeling (G : SimpleGraph V) [DecidableRel G.Adj] : TopEdgeLabeling V (Fin 2) :=
  EdgeLabeling.mk (fun x y _ => if G.Adj x y then 1 else 0) (by simp [G.adj_comm])

@[simp]
/-
**SimpleGraph.toTopEdgeLabeling_get** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：toTopEdgeLabeling_get {G : SimpleGraph V} [DecidableRel G.Adj] {x y : V} (
H : x != y) : G.toTopEdgeLabeling.get x y H = if G.Adj x y then 1 else 0
参数：H : x != y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toTopEdgeLabeling_get {G : SimpleGraph V} [DecidableRel G.Adj] {x y : V} (H : x ≠ y) :
    G.toTopEdgeLabeling.get x y H = if G.Adj x y then 1 else 0 :=
  rfl

@[simp]
/-
**SimpleGraph.toTopEdgeLabeling_labelGraph** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGrap
h`。
形式化陈述：toTopEdgeLabeling_labelGraph (G : SimpleGraph V) [DecidableRel G.Adj] : G.
toTopEdgeLabeling.labelGraph 1 = G
参数：G : SimpleGraph V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.ext`：∀ {V : Type u} {x y : SimpleGraph V}, x.Adj = y.Adj → x
 = y
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `SimpleGraph.ne_of_adj`：ne_of_adj (h : G.Adj a b) : a != b
-/
theorem toTopEdgeLabeling_labelGraph (G : SimpleGraph V) [DecidableRel G.Adj] :
    G.toTopEdgeLabeling.labelGraph 1 = G := by ext x y; simpa [imp_false] using G.ne_of_adj

@[simp]
/-
**SimpleGraph.toTopEdgeLabeling_labelGraph_compl** 是 Mathlib 中的一个定理，位于命名空间 `Simp
leGraph`。
形式化陈述：toTopEdgeLabeling_labelGraph_compl (G : SimpleGraph V) [DecidableRel G.Adj
] : G.toTopEdgeLabeling.labelGraph 0 = Gᶜ
参数：G : SimpleGraph V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.ext`：∀ {V : Type u} {x y : SimpleGraph V}, x.Adj = y.Adj → x
 = y
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem toTopEdgeLabeling_labelGraph_compl (G : SimpleGraph V) [DecidableRel G.Adj] :
    G.toTopEdgeLabeling.labelGraph 0 = Gᶜ := by ext x y; simp [imp_false]
/-
**SimpleGraph.TopEdgeLabeling.labelGraph_toTopEdgeLabeling** 是 Mathlib 中的一个定理，位于
命名空间 `SimpleGraph.TopEdgeLabeling`。
形式化陈述：∀ {V : Type u_1} [inst : DecidableEq V] (C : SimpleGraph.TopEdgeLabeling V
 (Fin 2)),   (SimpleGraph.EdgeLabeling.labelGraph C 1).toTopEdgeLabeling = C
参数：C : SimpleGraph.TopEdgeLabeling V (Fin 2)；SimpleGraph.EdgeLabeling.labelGraph
 C 1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.EdgeLabeling.ext_get`：ext_get {C' : EdgeLabeling G K} (h : f
orall x y, (h : G.Adj x y) -> C.get x y h = C'.get x y h) : C = C'
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
theorem TopEdgeLabeling.labelGraph_toTopEdgeLabeling [DecidableEq V]
    (C : TopEdgeLabeling V (Fin 2)) : (C.labelGraph 1).toTopEdgeLabeling = C := by
  refine EdgeLabeling.ext_get ?_
  grind [toTopEdgeLabeling_get, TopEdgeLabeling.labelGraph_adj, Adj.ne]

end SimpleGraph

