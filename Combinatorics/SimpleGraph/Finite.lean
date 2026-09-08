/-
Copyright (c) 2020 Aaron Anderson, Jalex Stark, Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson, Jalex Stark, Kyle Miller, Alena Gusakov
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Sym.Card
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Definitions for finite and locally finite graphs

This file defines finite versions of `edgeSet`, `neighborSet` and `incidenceSet` and proves some
of their basic properties. It also defines the notion of a locally finite graph, which is one
whose vertices have finite degree.

The design for finiteness is that each definition takes the smallest finiteness assumption
necessary. For example, `SimpleGraph.neighborFinset v` only requires that `v` have
finitely many neighbors.

## Main definitions

* `SimpleGraph.edgeFinset` is the `Finset` of edges in a graph, if `edgeSet` is finite
* `SimpleGraph.neighborFinset` is the `Finset` of vertices adjacent to a given vertex,
  if `neighborSet` is finite
* `SimpleGraph.incidenceFinset` is the `Finset` of edges containing a given vertex,
  if `incidenceSet` is finite

## Naming conventions

If the vertex type of a graph is finite, we refer to its cardinality as `CardVerts`
or `card_verts`.

## Implementation notes

* A locally finite graph is one with instances `Π v, Fintype (G.neighborSet v)`.
* Given instances `DecidableRel G.Adj` and `Fintype V`, then the graph
  is locally finite, too.
-/

@[expose] public section


open Finset Function

namespace SimpleGraph

variable {V : Type*} (G H : SimpleGraph V) {e : Sym2 V}

section EdgeFinset

variable {G₁ G₂ : SimpleGraph V} [Fintype G.edgeSet] [Fintype G₁.edgeSet] [Fintype G₂.edgeSet]

/-- The `edgeSet` of the graph as a `Finset`. -/
/-
**SimpleGraph.edgeFinset** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph`。
形式化陈述：edgeFinset : Finset (Sym2 V)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `edgeSet` of the graph as a `Finset`.
-/
def edgeFinset : Finset (Sym2 V) :=
  Set.toFinset G.edgeSet

@[simp, norm_cast]
/-
**SimpleGraph.coe_edgeFinset** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：coe_edgeFinset : (G.edgeFinset : Set (Sym2 V)) = G.edgeSet
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.coe_toFinset`：coe_toFinset (s : Set α) [Fintype s] : (↑s.toFinset : 
Set α) = s
-/
theorem coe_edgeFinset : (G.edgeFinset : Set (Sym2 V)) = G.edgeSet :=
  Set.coe_toFinset _

variable {G}

@[simp]
/-
**SimpleGraph.mem_edgeFinset** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：mem_edgeFinset : e in G.edgeFinset ↔ e in G.edgeSet
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_toFinset`：mem_toFinset {s : Set α} [Fintype s] {a : α} : a in s.
toFinset ↔ a in s
-/
theorem mem_edgeFinset : e ∈ G.edgeFinset ↔ e ∈ G.edgeSet :=
  Set.mem_toFinset
/-
**SimpleGraph.not_isDiag_of_mem_edgeFinset** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGrap
h`。
形式化陈述：not_isDiag_of_mem_edgeFinset : e in G.edgeFinset -> ¬e.IsDiag
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.not_isDiag_of_mem_edgeSet`：not_isDiag_of_mem_edgeSet : e in 
edgeSet G -> ¬e.IsDiag
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `SimpleGraph.mem_edgeFinset`：mem_edgeFinset : e in G.edgeFinset ↔ e in G.
edgeSet
-/
theorem not_isDiag_of_mem_edgeFinset : e ∈ G.edgeFinset → ¬e.IsDiag :=
  not_isDiag_of_mem_edgeSet _ ∘ mem_edgeFinset.1

/-- Mapping an edge to a finite set produces a finset of size `2`. -/
/-
**SimpleGraph.card_toFinset_mem_edgeFinset** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGrap
h`。
形式化陈述：card_toFinset_mem_edgeFinset [DecidableEq V] (e : G.edgeFinset) : (e : Sym
2 V).toFinset.card = 2
参数：e : G.edgeFinset。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Sym2.card_toFinset_of_not_isDiag`：card_toFinset_of_not_isDiag (z : Sym2 
α) (h : ¬z.IsDiag) : #(z : Sym2 α).toFinset = 2
· 使用定理 `SimpleGraph.not_isDiag_of_mem_edgeFinset`：not_isDiag_of_mem_edgeFinset :
 e in G.edgeFinset -> ¬e.IsDiag
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x

--- 原说明 ---
Mapping an edge to a finite set produces a finset of size `2`.
-/
theorem card_toFinset_mem_edgeFinset [DecidableEq V] (e : G.edgeFinset) :
    (e : Sym2 V).toFinset.card = 2 :=
  Sym2.card_toFinset_of_not_isDiag e.val (G.not_isDiag_of_mem_edgeFinset e.prop)

@[simp]
/-
**SimpleGraph.edgeFinset_inj** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：edgeFinset_inj : G₁.edgeFinset = G₂.edgeFinset ↔ G₁ = G₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RelEmbedding.instEmbeddingLike`：∀ {α : Type u_1} {β : Type u_2} {r : α →
 α → Prop} {s : β → β → Prop}, EmbeddingLike (r ↪r s) α β
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem edgeFinset_inj : G₁.edgeFinset = G₂.edgeFinset ↔ G₁ = G₂ := by simp [edgeFinset]

@[simp]
/-
**SimpleGraph.edgeFinset_subset_edgeFinset** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGrap
h`。
形式化陈述：edgeFinset_subset_edgeFinset : G₁.edgeFinset subseteq G₂.edgeFinset ↔ G₁ <
= G₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.coe_toFinset`：coe_toFinset (s : Set α) [Fintype s] : (↑s.toFinset : 
Set α) = s
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem edgeFinset_subset_edgeFinset : G₁.edgeFinset ⊆ G₂.edgeFinset ↔ G₁ ≤ G₂ := by
  simp [edgeFinset]

@[simp]
/-
**SimpleGraph.edgeFinset_ssubset_edgeFinset** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGra
ph`。
形式化陈述：edgeFinset_ssubset_edgeFinset : G₁.edgeFinset ⊂ G₂.edgeFinset ↔ G₁ < G₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.coe_toFinset`：coe_toFinset (s : Set α) [Fintype s] : (↑s.toFinset : 
Set α) = s
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem edgeFinset_ssubset_edgeFinset : G₁.edgeFinset ⊂ G₂.edgeFinset ↔ G₁ < G₂ := by
  simp [edgeFinset]

@[mono, gcongr] alias ⟨_, edgeFinset_mono⟩ := edgeFinset_subset_edgeFinset

@[mono, gcongr]
alias ⟨_, edgeFinset_strict_mono⟩ := edgeFinset_ssubset_edgeFinset

@[simp]
/-
**SimpleGraph.edgeFinset_bot** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：edgeFinset_bot : (⊥ : SimpleGraph V).edgeFinset = ∅
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.toFinset_congr`：toFinset_congr {s t : Set α} [Fintype s] [Fintype t]
 (h : s = t) : toFinset s = toFinset t
· 使用定理 `SimpleGraph.edgeSet_bot`：edgeSet_bot : (⊥ : SimpleGraph V).edgeSet = ∅
· 使用定理 `Set.toFinset_empty`：toFinset_empty [Fintype (∅ : Set α)] : (∅ : Set α).t
oFinset = ∅
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem edgeFinset_bot : (⊥ : SimpleGraph V).edgeFinset = ∅ := by simp [edgeFinset]

@[simp]
/-
**SimpleGraph.edgeFinset_sup** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：edgeFinset_sup [Fintype (edgeSet (G₁ ⊔ G₂))] [DecidableEq V] : (G₁ ⊔ G₂).e
dgeFinset = G₁.edgeFinset union G₂.edgeFinset
参数：edgeSet (G₁ ⊔ G₂)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.toFinset_congr`：toFinset_congr {s t : Set α} [Fintype s] [Fintype t]
 (h : s = t) : toFinset s = toFinset t
· 使用定理 `SimpleGraph.edgeSet_sup`：edgeSet_sup : (G₁ ⊔ G₂).edgeSet = G₁.edgeSet un
ion G₂.edgeSet
· 使用定理 `Set.toFinset_union`：toFinset_union [Fintype (s union t : Set _)] : (s un
ion t).toFinset = s.toFinset union t.toFinset
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem edgeFinset_sup [Fintype (edgeSet (G₁ ⊔ G₂))] [DecidableEq V] :
    (G₁ ⊔ G₂).edgeFinset = G₁.edgeFinset ∪ G₂.edgeFinset := by simp [edgeFinset]

@[simp]
/-
**SimpleGraph.edgeFinset_inf** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：edgeFinset_inf [Fintype (G₁ ⊓ G₂).edgeSet] [DecidableEq V] : (G₁ ⊓ G₂).edg
eFinset = G₁.edgeFinset inter G₂.edgeFinset
参数：G₁ ⊓ G₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.toFinset_congr`：toFinset_congr {s t : Set α} [Fintype s] [Fintype t]
 (h : s = t) : toFinset s = toFinset t
· 使用定理 `SimpleGraph.edgeSet_inf`：edgeSet_inf : (G₁ ⊓ G₂).edgeSet = G₁.edgeSet in
ter G₂.edgeSet
· 使用定理 `Set.toFinset_inter`：toFinset_inter [Fintype (s inter t : Set _)] : (s in
ter t).toFinset = s.toFinset inter t.toFinset
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem edgeFinset_inf [Fintype (G₁ ⊓ G₂).edgeSet] [DecidableEq V] :
    (G₁ ⊓ G₂).edgeFinset = G₁.edgeFinset ∩ G₂.edgeFinset := by
  simp [edgeFinset]

@[simp]
/-
**SimpleGraph.edgeFinset_sdiff** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：edgeFinset_sdiff [DecidableEq V] : (G₁ \ G₂).edgeFinset = G₁.edgeFinset \ 
G₂.edgeFinset
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.toFinset_congr`：toFinset_congr {s t : Set α} [Fintype s] [Fintype t]
 (h : s = t) : toFinset s = toFinset t
· 使用定理 `SimpleGraph.edgeSet_sdiff`：edgeSet_sdiff : (G₁ \ G₂).edgeSet = G₁.edgeSe
t \ G₂.edgeSet
· 使用定理 `Set.toFinset_sdiff`：toFinset_sdiff [Fintype (s \ t : Set _)] : (s \ t).t
oFinset = s.toFinset \ t.toFinset
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem edgeFinset_sdiff [DecidableEq V] :
    (G₁ \ G₂).edgeFinset = G₁.edgeFinset \ G₂.edgeFinset := by simp [edgeFinset]

@[simp]
/-
**SimpleGraph.disjoint_edgeFinset** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
形式化陈述：disjoint_edgeFinset : Disjoint G₁.edgeFinset G₂.edgeFinset ↔ Disjoint G₁ G
₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `SimpleGraph.coe_edgeFinset`：coe_edgeFinset : (G.edgeFinset : Set (Sym2 V
)) = G.edgeSet
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma disjoint_edgeFinset : Disjoint G₁.edgeFinset G₂.edgeFinset ↔ Disjoint G₁ G₂ := by
  simp_rw [← Finset.disjoint_coe, coe_edgeFinset, disjoint_edgeSet]

@[simp]
/-
**SimpleGraph.edgeFinset_eq_empty** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
形式化陈述：edgeFinset_eq_empty : G.edgeFinset = ∅ ↔ G = ⊥
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SimpleGraph.edgeFinset_bot`：edgeFinset_bot : (⊥ : SimpleGraph V).edgeFin
set = ∅
· 使用定理 `SimpleGraph.edgeFinset_inj`：edgeFinset_inj : G₁.edgeFinset = G₂.edgeFins
et ↔ G₁ = G₂
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma edgeFinset_eq_empty : G.edgeFinset = ∅ ↔ G = ⊥ := by
  rw [← edgeFinset_bot, edgeFinset_inj]

@[simp]
/-
**SimpleGraph.edgeFinset_nonempty** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
形式化陈述：edgeFinset_nonempty : G.edgeFinset.Nonempty ↔ G != ⊥
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.nonempty_iff_ne_empty`：nonempty_iff_ne_empty {s : Finset α} : s.N
onempty ↔ s != ∅
· 使用定理 `Iff.ne`：∀ {α : Sort u_1} {β : Sort u_2} {a b : α} {c d : β}, (a = b ↔ c 
= d) → (a ≠ b ↔ c ≠ d)
· 使用引理 `SimpleGraph.edgeFinset_eq_empty`：edgeFinset_eq_empty : G.edgeFinset = ∅ 
↔ G = ⊥
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma edgeFinset_nonempty : G.edgeFinset.Nonempty ↔ G ≠ ⊥ := by
  rw [Finset.nonempty_iff_ne_empty, edgeFinset_eq_empty.ne]
/-
**SimpleGraph.edgeFinset_card** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：edgeFinset_card : #G.edgeFinset = Fintype.card G.edgeSet
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.toFinset_card`：toFinset_card {α : Type*} (s : Set α) [Fintype s] : s
.toFinset.card = Fintype.card s
-/
theorem edgeFinset_card : #G.edgeFinset = Fintype.card G.edgeSet :=
  Set.toFinset_card _
/-
**SimpleGraph.card_edgeSet** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：card_edgeSet : Fintype.card G.edgeSet = #G.edgeFinset
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.toFinset_card`：toFinset_card {α : Type*} (s : Set α) [Fintype s] : s
.toFinset.card = Fintype.card s
-/
theorem card_edgeSet : Fintype.card G.edgeSet = #G.edgeFinset :=
  .symm <| Set.toFinset_card _
/-
**SimpleGraph.edgeSet_univ_card** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：edgeSet_univ_card : #(univ : Finset G.edgeSet) = #G.edgeFinset
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.card_edgeSet`：card_edgeSet : Fintype.card G.edgeSet = #G.edg
eFinset
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem edgeSet_univ_card : #(univ : Finset G.edgeSet) = #G.edgeFinset := by
  simp [card_edgeSet]

variable [Fintype V]

@[simp]
/-
**SimpleGraph.edgeFinset_top** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：edgeFinset_top [DecidableEq V] : (⊤ : SimpleGraph V).edgeFinset = Sym2.dia
gSetᶜ.toFinset
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.toFinset_compl`：toFinset_compl [Fintype α] [Fintype (sᶜ : Set _)] : 
sᶜ.toFinset = s.toFinsetᶜ
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `SimpleGraph.coe_edgeFinset`：coe_edgeFinset : (G.edgeFinset : Set (Sym2 V
)) = G.edgeSet
· 使用定理 `SimpleGraph.edgeSet_top`：edgeSet_top : (⊤ : SimpleGraph V).edgeSet = Sym
2.diagSetᶜ
· 使用定理 `Finset.coe_compl`：coe_compl (s : Finset α) : ↑sᶜ = (↑s : Set α)ᶜ
· 使用定理 `Set.coe_toFinset`：coe_toFinset (s : Set α) [Fintype s] : (↑s.toFinset : 
Set α) = s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem edgeFinset_top [DecidableEq V] :
    (⊤ : SimpleGraph V).edgeFinset = Sym2.diagSetᶜ.toFinset := by simp [← coe_inj]

/-- The complete graph on `n` vertices has `n.choose 2` edges. -/
/-
**SimpleGraph.card_edgeFinset_top_eq_card_choose_two** 是 Mathlib 中的一个定理，位于命名空间 `
SimpleGraph`。
形式化陈述：card_edgeFinset_top_eq_card_choose_two [DecidableEq V] : #(⊤ : SimpleGraph
 V).edgeFinset = (Fintype.card V).choose 2
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.toFinset_card`：toFinset_card {α : Type*} (s : Set α) [Fintype s] : s
.toFinset.card = Fintype.card s
· 使用定理 `Fintype.card_congr'`：card_congr' {α β} [Fintype α] [Fintype β] (h : α = 
β) : card α = card β
· 使用定理 `SimpleGraph.edgeSet_top`：edgeSet_top : (⊤ : SimpleGraph V).edgeSet = Sym
2.diagSetᶜ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The complete graph on `n` vertices has `n.choose 2` edges.
-/
theorem card_edgeFinset_top_eq_card_choose_two [DecidableEq V] :
    #(⊤ : SimpleGraph V).edgeFinset = (Fintype.card V).choose 2 := by
  simp_rw [edgeFinset, Set.toFinset_card, edgeSet_top, ← Sym2.card_diagSet_compl]

/-- Any graph on `n` vertices has at most `n.choose 2` edges. -/
/-
**SimpleGraph.card_edgeFinset_le_card_choose_two** 是 Mathlib 中的一个定理，位于命名空间 `Simp
leGraph`。
形式化陈述：card_edgeFinset_le_card_choose_two : #G.edgeFinset <= (Fintype.card V).cho
ose 2
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SimpleGraph.card_edgeFinset_top_eq_card_choose_two`：card_edgeFinset_top_
eq_card_choose_two [DecidableEq V] : #(⊤ : SimpleGraph V).edgeFinset = (Fintype.
card V).choose 2
· 使用定理 `Finset.card_le_card`：card_le_card : s subseteq t -> #s <= #t
· 使用定理 `SimpleGraph.edgeFinset_mono`：∀ {V : Type u_1} {G₁ G₂ : SimpleGraph V} [i
nst : Fintype ↑G₁.edgeSet] [inst_1 : Fintype ↑G₂.edgeSet],   G₁ ≤ G₂ → G₁.edgeFi
nset ⊆ G₂.edgeFin…
· 使用定理 `le_top`：le_top : a <= ⊤

--- 原说明 ---
Any graph on `n` vertices has at most `n.choose 2` edges.
-/
theorem card_edgeFinset_le_card_choose_two : #G.edgeFinset ≤ (Fintype.card V).choose 2 := by
  classical
  rw [← card_edgeFinset_top_eq_card_choose_two]
  exact card_le_card (edgeFinset_mono le_top)

end EdgeFinset

section FiniteAt

/-!
## Finiteness at a vertex

This section contains definitions and lemmas concerning vertices that
have finitely many adjacent vertices.  We denote this condition by
`Fintype (G.neighborSet v)`.

We define `G.neighborFinset v` to be the `Finset` version of `G.neighborSet v`.
Use `neighborFinset_eq_filter` to rewrite this definition as a `Finset.filter` expression.
-/

variable (v) [Fintype (G.neighborSet v)]

/-- `G.neighborFinset v` is the `Finset` version of `G.neighborSet v` in case `G` is
locally finite at `v`. -/
/-
**SimpleGraph.neighborFinset** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph`。
形式化陈述：neighborFinset : Finset V
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`G.neighborFinset v` is the `Finset` version of `G.neighborSet v` in case `G` is
locally finite at `v`.
-/
def neighborFinset : Finset V :=
  (G.neighborSet v).toFinset
/-
**SimpleGraph.neighborFinset_def** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：neighborFinset_def : G.neighborFinset v = (G.neighborSet v).toFinset
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem neighborFinset_def : G.neighborFinset v = (G.neighborSet v).toFinset :=
  rfl

@[simp, norm_cast]
/-
**SimpleGraph.coe_neighborFinset** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：coe_neighborFinset : (G.neighborFinset v : Set V) = G.neighborSet v
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.coe_toFinset`：coe_toFinset (s : Set α) [Fintype s] : (↑s.toFinset : 
Set α) = s
-/
theorem coe_neighborFinset : (G.neighborFinset v : Set V) = G.neighborSet v :=
  Set.coe_toFinset _

@[simp]
/-
**SimpleGraph.mem_neighborFinset** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：mem_neighborFinset (w : V) : w in G.neighborFinset v ↔ G.Adj v w
参数：w : V。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_toFinset`：mem_toFinset {s : Set α} [Fintype s] {a : α} : a in s.
toFinset ↔ a in s
-/
theorem mem_neighborFinset (w : V) : w ∈ G.neighborFinset v ↔ G.Adj v w :=
  Set.mem_toFinset
/-
**SimpleGraph.notMem_neighborFinset_self** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`
。
形式化陈述：notMem_neighborFinset_self : v ∉ G.neighborFinset v
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem notMem_neighborFinset_self : v ∉ G.neighborFinset v := by simp
/-
**SimpleGraph.neighborFinset_disjoint_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Simpl
eGraph`。
形式化陈述：neighborFinset_disjoint_singleton : Disjoint (G.neighborFinset v) {v}
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.disjoint_singleton_right`：disjoint_singleton_right : Disjoint s (
singleton a) ↔ a ∉ s
· 使用定理 `SimpleGraph.notMem_neighborFinset_self`：notMem_neighborFinset_self : v ∉
 G.neighborFinset v
-/
theorem neighborFinset_disjoint_singleton : Disjoint (G.neighborFinset v) {v} :=
  Finset.disjoint_singleton_right.mpr <| notMem_neighborFinset_self _ _
/-
**SimpleGraph.singleton_disjoint_neighborFinset** 是 Mathlib 中的一个定理，位于命名空间 `Simpl
eGraph`。
形式化陈述：singleton_disjoint_neighborFinset : Disjoint {v} (G.neighborFinset v)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.disjoint_singleton_left`：disjoint_singleton_left : Disjoint (sing
leton a) s ↔ a ∉ s
· 使用定理 `SimpleGraph.notMem_neighborFinset_self`：notMem_neighborFinset_self : v ∉
 G.neighborFinset v
-/
theorem singleton_disjoint_neighborFinset : Disjoint {v} (G.neighborFinset v) :=
  Finset.disjoint_singleton_left.mpr <| notMem_neighborFinset_self _ _
/-
**SimpleGraph.neighborFinset_bot** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：neighborFinset_bot [Fintype ((⊥ : SimpleGraph V).neighborSet v)] : (⊥ : Si
mpleGraph V).neighborFinset v = ∅
参数：(⊥ : SimpleGraph V).neighborSet v。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem neighborFinset_bot [Fintype ((⊥ : SimpleGraph V).neighborSet v)] :
    (⊥ : SimpleGraph V).neighborFinset v = ∅ := by
  ext; simp

@[simp]
/-
**SimpleGraph.neighborFinset_top** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：neighborFinset_top [Fintype V] [DecidableEq V] : (⊤ : SimpleGraph V).neigh
borFinset v = {v}ᶜ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.coe_neighborFinset`：coe_neighborFinset : (G.neighborFinset v
 : Set V) = G.neighborSet v
· 使用定理 `SimpleGraph.neighborSet_top`：neighborSet_top : neighborSet ⊤ v = {v}ᶜ
· 使用定理 `Finset.coe_compl`：coe_compl (s : Finset α) : ↑sᶜ = (↑s : Set α)ᶜ
· 使用定理 `Finset.coe_singleton`：coe_singleton (a : α) : (({a} : Finset α) : Set α)
 = {a}
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem neighborFinset_top [Fintype V] [DecidableEq V] :
    (⊤ : SimpleGraph V).neighborFinset v = {v}ᶜ := by
  simp [← Finset.coe_inj]

@[simp]
/-
**SimpleGraph.neighborFinset_sup** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：neighborFinset_sup [DecidableEq V] {G₁ G₂ : SimpleGraph V} [Fintype ((G₁ ⊔
 G₂).neighborSet v)] [Fintype (G₁.neighborSet v)] [Fintype (G₂.neighborSet v)] :
 (G₁ ⊔ G₂).neighborFinset v = G₁.neighborFinset v union G₂.neighborFinset v
参数：(G₁ ⊔ G₂).neighborSet v；G₁.neighborSet v；G₂.neighborSet v。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.coe_neighborFinset`：coe_neighborFinset : (G.neighborFinset v
 : Set V) = G.neighborSet v
· 使用定理 `Finset.coe_union`：coe_union (s₁ s₂ : Finset α) : ↑(s₁ union s₂) = (s₁ un
ion s₂ : Set α)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem neighborFinset_sup [DecidableEq V] {G₁ G₂ : SimpleGraph V}
    [Fintype ((G₁ ⊔ G₂).neighborSet v)] [Fintype (G₁.neighborSet v)] [Fintype (G₂.neighborSet v)] :
    (G₁ ⊔ G₂).neighborFinset v = G₁.neighborFinset v ∪ G₂.neighborFinset v := by
  simp [← Finset.coe_inj]

@[simp]
/-
**SimpleGraph.neighborFinset_inf** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：neighborFinset_inf [DecidableEq V] {G₁ G₂ : SimpleGraph V} [Fintype ((G₁ ⊓
 G₂).neighborSet v)] [Fintype (G₁.neighborSet v)] [Fintype (G₂.neighborSet v)] :
 (G₁ ⊓ G₂).neighborFinset v = G₁.neighborFinset v inter G₂.neighborFinset v
参数：(G₁ ⊓ G₂).neighborSet v；G₁.neighborSet v；G₂.neighborSet v。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.coe_neighborFinset`：coe_neighborFinset : (G.neighborFinset v
 : Set V) = G.neighborSet v
· 使用定理 `Finset.coe_inter`：coe_inter (s₁ s₂ : Finset α) : ↑(s₁ inter s₂) = (s₁ in
ter s₂ : Set α)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem neighborFinset_inf [DecidableEq V] {G₁ G₂ : SimpleGraph V}
    [Fintype ((G₁ ⊓ G₂).neighborSet v)] [Fintype (G₁.neighborSet v)] [Fintype (G₂.neighborSet v)] :
    (G₁ ⊓ G₂).neighborFinset v = G₁.neighborFinset v ∩ G₂.neighborFinset v := by
  simp [← Finset.coe_inj]

@[simp]
/-
**SimpleGraph.neighborFinset_sdiff** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：neighborFinset_sdiff [DecidableEq V] {G₁ G₂ : SimpleGraph V} [Fintype ((G₁
 \ G₂).neighborSet v)] [Fintype (G₁.neighborSet v)] [Fintype (G₂.neighborSet v)]
 : (G₁ \ G₂).neighborFinset v = G₁.neighborFinset v \ G₂.neighborFinset v
参数：(G₁ \ G₂).neighborSet v；G₁.neighborSet v；G₂.neighborSet v。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.coe_neighborFinset`：coe_neighborFinset : (G.neighborFinset v
 : Set V) = G.neighborSet v
· 使用定理 `Finset.coe_sdiff`：coe_sdiff (s₁ s₂ : Finset α) : ↑(s₁ \ s₂) = (s₁ \ s₂ :
 Set α)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem neighborFinset_sdiff [DecidableEq V] {G₁ G₂ : SimpleGraph V}
    [Fintype ((G₁ \ G₂).neighborSet v)] [Fintype (G₁.neighborSet v)] [Fintype (G₂.neighborSet v)] :
    (G₁ \ G₂).neighborFinset v = G₁.neighborFinset v \ G₂.neighborFinset v := by
  simp [← Finset.coe_inj]
/-
**SimpleGraph.disjoint_neighborFinset_of_disjoint** 是 Mathlib 中的一个定理，位于命名空间 `Sim
pleGraph`。
形式化陈述：disjoint_neighborFinset_of_disjoint [Fintype <| H.neighborSet v] (h : Disj
oint G H) : Disjoint (G.neighborFinset v) (H.neighborFinset v)
参数：h : Disjoint G H。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.coe_neighborFinset`：coe_neighborFinset : (G.neighborFinset v
 : Set V) = G.neighborSet v
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `SimpleGraph.disjoint_neighborSet`：disjoint_neighborSet : (forall v, Disj
oint (G.neighborSet v) (H.neighborSet v)) ↔ Disjoint G H
-/
theorem disjoint_neighborFinset_of_disjoint [Fintype <| H.neighborSet v] (h : Disjoint G H) :
    Disjoint (G.neighborFinset v) (H.neighborFinset v) := by
  simp [← Finset.disjoint_coe, disjoint_neighborSet.mpr h v]
/-
**SimpleGraph.neighborFinset_sup_of_disjoint** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGr
aph`。
形式化陈述：neighborFinset_sup_of_disjoint {G₁ G₂ : SimpleGraph V} [Fintype ((G₁ ⊔ G₂)
.neighborSet v)] [Fintype (G₁.neighborSet v)] [Fintype (G₂.neighborSet v)] (h : 
Disjoint G₁ G₂) : (G₁ ⊔ G₂).neighborFinset v = (G₁.neighborFinset v).disjUnion (
G₂.neighborFinset v) (disjoint_neighborFinset_of_disjoint G₁ G₂ v h)
参数：(G₁ ⊔ G₂).neighborSet v；G₁.neighborSet v；G₂.neighborSet v；h : Disjoint G₁ G₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `SimpleGraph.disjoint_neighborFinset_of_disjoint`：disjoint_neighborFinset
_of_disjoint [Fintype <| H.neighborSet v] (h : Disjoint G H) : Disjoint (G.neigh
borFinset v) (H.neighborFinset v)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.coe_neighborFinset`：coe_neighborFinset : (G.neighborFinset v
 : Set V) = G.neighborSet v
· 使用定理 `Finset.coe_disjUnion`：coe_disjUnion {s t : Finset α} (h : Disjoint s t) 
: (disjUnion s t h : Set α) = (s : Set α) union t
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem neighborFinset_sup_of_disjoint {G₁ G₂ : SimpleGraph V}
    [Fintype ((G₁ ⊔ G₂).neighborSet v)] [Fintype (G₁.neighborSet v)] [Fintype (G₂.neighborSet v)]
    (h : Disjoint G₁ G₂) :
    (G₁ ⊔ G₂).neighborFinset v =
      (G₁.neighborFinset v).disjUnion (G₂.neighborFinset v)
        (disjoint_neighborFinset_of_disjoint G₁ G₂ v h) := by
  simp [← Finset.coe_inj, Finset.coe_disjUnion]
/-
**SimpleGraph.neighborFinset_eq_empty** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：∀ {V : Type u_1} (G : SimpleGraph V) (v : V) [inst : Fintype ↑(G.neighborS
et v)],   G.neighborFinset v = ∅ ↔ G.IsIsolated v
参数：G : SimpleGraph V；v : V；G.neighborSet v。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `iff_false`：∀ (p : Prop), (p ↔ False) = ¬p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma neighborFinset_eq_empty : G.neighborFinset v = ∅ ↔ G.IsIsolated v := by
  simp [neighborFinset, IsIsolated, Set.ext_iff]
/-
**SimpleGraph.neighborFinset_nonempty** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：∀ {V : Type u_1} (G : SimpleGraph V) (v : V) [inst : Fintype ↑(G.neighborS
et v)],   (G.neighborFinset v).Nonempty ↔ ¬G.IsIsolated v
参数：G : SimpleGraph V；v : V；G.neighborSet v；G.neighborFinset v。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma neighborFinset_nonempty : (G.neighborFinset v).Nonempty ↔ ¬ G.IsIsolated v := by
  simp [nonempty_iff_ne_empty]

protected alias ⟨IsIsolated.of_neighborFinset_eq_empty, IsIsolated.neighborFinset_eq_empty⟩
    := neighborFinset_eq_empty

attribute [simp] IsIsolated.neighborFinset_eq_empty

/-- `G.degree v` is the number of vertices adjacent to `v`. -/
/-
**SimpleGraph.degree** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph`。
形式化陈述：degree : Nat
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`G.degree v` is the number of vertices adjacent to `v`.
-/
def degree : ℕ := #(G.neighborFinset v)

@[simp]
/-
**SimpleGraph.card_neighborFinset_eq_degree** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGra
ph`。
形式化陈述：card_neighborFinset_eq_degree : #(G.neighborFinset v) = G.degree v
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem card_neighborFinset_eq_degree : #(G.neighborFinset v) = G.degree v := rfl
/-
**SimpleGraph.card_neighborSet_eq_degree** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`
。
形式化陈述：card_neighborSet_eq_degree : Fintype.card (G.neighborSet v) = G.degree v
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.toFinset_card`：toFinset_card {α : Type*} (s : Set α) [Fintype s] : s
.toFinset.card = Fintype.card s
-/
theorem card_neighborSet_eq_degree : Fintype.card (G.neighborSet v) = G.degree v :=
  (Set.toFinset_card _).symm
/-
**SimpleGraph.degree_eq_zero** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
形式化陈述：degree_eq_zero : G.degree v = 0 ↔ G.IsIsolated v
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
lemma degree_eq_zero : G.degree v = 0 ↔ G.IsIsolated v := by simp [← card_neighborFinset_eq_degree]
/-
**SimpleGraph.degree_pos** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
形式化陈述：degree_pos : 0 < G.degree v ↔ ¬ G.IsIsolated v
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
lemma degree_pos : 0 < G.degree v ↔ ¬ G.IsIsolated v := by simp [← card_neighborFinset_eq_degree]

protected alias ⟨IsIsolated.of_degree_eq_zero, IsIsolated.degree_eq_zero⟩ := degree_eq_zero

attribute [simp] IsIsolated.degree_eq_zero
/-
**SimpleGraph.degree_pos_iff_exists_adj** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：degree_pos_iff_exists_adj : 0 < G.degree v ↔ exists w, G.Adj v w
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
theorem degree_pos_iff_exists_adj : 0 < G.degree v ↔ ∃ w, G.Adj v w := by
  simp only [degree, card_pos, Finset.Nonempty, mem_neighborFinset]

variable {G v} in
/-
**SimpleGraph.degree_pos_iff_nonempty** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：degree_pos_iff_nonempty : 0 < G.degree v ↔ (G.neighborSet v).Nonempty
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.degree_pos_iff_exists_adj`：degree_pos_iff_exists_adj : 0 < G
.degree v ↔ exists w, G.Adj v w
-/
theorem degree_pos_iff_nonempty : 0 < G.degree v ↔ (G.neighborSet v).Nonempty :=
  G.degree_pos_iff_exists_adj v

variable {G v} in
/-
**SimpleGraph.Adj.degree_pos_left** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Adj`。
形式化陈述：∀ {V : Type u_1} {G : SimpleGraph V} {v : V} [inst : Fintype ↑(G.neighborS
et v)] {w : V}, G.Adj v w → 0 < G.degree v
参数：G.neighborSet v。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `SimpleGraph.degree_pos_iff_nonempty`：degree_pos_iff_nonempty : 0 < G.deg
ree v ↔ (G.neighborSet v).Nonempty
-/
theorem Adj.degree_pos_left {w : V} (h : G.Adj v w) : 0 < G.degree v :=
  G.degree_pos_iff_nonempty.mpr ⟨_, h⟩

variable {G v} in
/-
**SimpleGraph.Adj.degree_pos_right** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Adj`。
形式化陈述：∀ {V : Type u_1} {G : SimpleGraph V} {v : V} [inst : Fintype ↑(G.neighborS
et v)] {w : V}, G.Adj w v → 0 < G.degree v
参数：G.neighborSet v。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Adj.degree_pos_left`：∀ {V : Type u_1} {G : SimpleGraph V} {v
 : V} [inst : Fintype ↑(G.neighborSet v)] {w : V}, G.Adj v w → 0 < G.degree v
· 使用定理 `SimpleGraph.Adj.symm`：∀ {V : Type u} {G : SimpleGraph V} {u v : V}, G.Ad
j u v → G.Adj v u
-/
theorem Adj.degree_pos_right {w : V} (h : G.Adj w v) : 0 < G.degree v :=
  h.symm.degree_pos_left
/-
**SimpleGraph.degree_pos_iff_mem_support** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`
。
形式化陈述：degree_pos_iff_mem_support : 0 < G.degree v ↔ v in G.support
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.degree_pos_iff_exists_adj`：degree_pos_iff_exists_adj : 0 < G
.degree v ↔ exists w, G.Adj v w
· 使用定理 `SimpleGraph.mem_support`：mem_support {v : V} : v in G.support ↔ exists w
, G.Adj v w
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem degree_pos_iff_mem_support : 0 < G.degree v ↔ v ∈ G.support := by
  rw [G.degree_pos_iff_exists_adj v, mem_support]
/-
**SimpleGraph.degree_eq_zero_iff_notMem_support** 是 Mathlib 中的一个定理，位于命名空间 `Simpl
eGraph`。
形式化陈述：degree_eq_zero_iff_notMem_support : G.degree v = 0 ↔ v ∉ G.support
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SimpleGraph.degree_pos_iff_mem_support`：degree_pos_iff_mem_support : 0 <
 G.degree v ↔ v in G.support
· 使用定理 `Nat.pos_iff_ne_zero`：∀ {n : ℕ}, 0 < n ↔ n ≠ 0
· 使用定理 `not_ne_iff`：not_ne_iff {α : Sort*} {a b : α} : ¬a != b ↔ a = b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem degree_eq_zero_iff_notMem_support : G.degree v = 0 ↔ v ∉ G.support := by
  rw [← G.degree_pos_iff_mem_support v, Nat.pos_iff_ne_zero, not_ne_iff]
/-
**SimpleGraph.degree_eq_zero_of_subsingleton** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGr
aph`。
形式化陈述：degree_eq_zero_of_subsingleton {G : SimpleGraph V} (v : V) [Fintype (G.nei
ghborSet v)] [Subsingleton V] : G.degree v = 0
参数：v : V；G.neighborSet v。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.IsIsolated.degree_eq_zero`：∀ {V : Type u_1} (G : SimpleGraph
 V) (v : V) [inst : Fintype ↑(G.neighborSet v)], G.IsIsolated v → G.degree v = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem degree_eq_zero_of_subsingleton {G : SimpleGraph V} (v : V) [Fintype (G.neighborSet v)]
    [Subsingleton V] : G.degree v = 0 := by
  simp
/-
**SimpleGraph.nontrivial_of_degree_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGrap
h`。
形式化陈述：nontrivial_of_degree_ne_zero {G : SimpleGraph V} {v : V} [Fintype (G.neigh
borSet v)] (h : G.degree v != 0) : Nontrivial V
参数：G.neighborSet v；h : G.degree v != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.nontrivial_of_not_isIsolated`：nontrivial_of_not_isIsolated (
h : ¬G.IsIsolated v) : Nontrivial V
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用引理 `SimpleGraph.degree_eq_zero`：degree_eq_zero : G.degree v = 0 ↔ G.IsIsolat
ed v
-/
theorem nontrivial_of_degree_ne_zero {G : SimpleGraph V} {v : V} [Fintype (G.neighborSet v)]
    (h : G.degree v ≠ 0) : Nontrivial V :=
  nontrivial_of_not_isIsolated <| G.degree_eq_zero v |>.not.mp h
/-
**SimpleGraph.degree_eq_one_iff_existsUnique_adj** 是 Mathlib 中的一个定理，位于命名空间 `Simp
leGraph`。
形式化陈述：degree_eq_one_iff_existsUnique_adj {G : SimpleGraph V} {v : V} [Fintype (G
.neighborSet v)] : G.degree v = 1 ↔ exists! w : V, G.Adj v w
参数：G.neighborSet v。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.degree.eq_1`：∀ {V : Type u_1} (G : SimpleGraph V) (v : V) [i
nst : Fintype ↑(G.neighborSet v)], G.degree v = (G.neighborFinset v).card
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
theorem degree_eq_one_iff_existsUnique_adj {G : SimpleGraph V} {v : V} [Fintype (G.neighborSet v)] :
    G.degree v = 1 ↔ ∃! w : V, G.Adj v w := by
  rw [degree, Finset.card_eq_one, Finset.singleton_iff_unique_mem]
  simp only [mem_neighborFinset]
/-
**SimpleGraph.degree_compl** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：degree_compl [Fintype (Gᶜ.neighborSet v)] [Fintype V] : Gᶜ.degree v = Fint
ype.card V - 1 - G.degree v
参数：Gᶜ.neighborSet v。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SimpleGraph.card_neighborSet_union_compl_neighborSet`：card_neighborSet_u
nion_compl_neighborSet [Fintype V] (G : SimpleGraph V) (v : V) [Fintype (G.neigh
borSet v union Gᶜ.neighborSet v : Set V)] …
· 使用定理 `Set.toFinset_union`：toFinset_union [Fintype (s union t : Set _)] : (s un
ion t).toFinset = s.toFinset union t.toFinset
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.card_union_of_disjoint`：∀ {α : Type u_1} {s t : Finset α} [inst :
 DecidableEq α], Disjoint s t → (s ∪ t).card = s.card + t.card
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.disjoint_toFinset`：disjoint_toFinset [Fintype s] [Fintype t] : Disjo
int s.toFinset t.toFinset ↔ Disjoint s t
· 使用定理 `SimpleGraph.compl_neighborSet_disjoint`：compl_neighborSet_disjoint (G : 
SimpleGraph V) (v : V) : Disjoint (G.neighborSet v) (Gᶜ.neighborSet v)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Set.toFinset_card`：toFinset_card {α : Type*} (s : Set α) [Fintype s] : s
.toFinset.card = Fintype.card s
· 使用定理 `SimpleGraph.card_neighborSet_eq_degree`：card_neighborSet_eq_degree : Fin
type.card (G.neighborSet v) = G.degree v
· 使用定理 `Nat.add_sub_cancel_left`：∀ (n m : ℕ), n + m - n = m
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem degree_compl [Fintype (Gᶜ.neighborSet v)] [Fintype V] :
    Gᶜ.degree v = Fintype.card V - 1 - G.degree v := by
  classical
    rw [← card_neighborSet_union_compl_neighborSet G v, Set.toFinset_union]
    simp [card_union_of_disjoint (Set.disjoint_toFinset.mpr (compl_neighborSet_disjoint G v)),
      card_neighborSet_eq_degree]
/-
**SimpleGraph.incidenceSetFintype** 是 Mathlib 中的一个实例，位于命名空间 `SimpleGraph`。
形式化陈述：incidenceSetFintype [DecidableEq V] : Fintype (G.incidenceSet v)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
instance incidenceSetFintype [DecidableEq V] : Fintype (G.incidenceSet v) :=
  Fintype.ofEquiv (G.neighborSet v) (G.incidenceSetEquivNeighborSet v).symm

/-- This is the `Finset` version of `incidenceSet`. -/
/-
**SimpleGraph.incidenceFinset** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph`。
形式化陈述：incidenceFinset [DecidableEq V] : Finset (Sym2 V)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This is the `Finset` version of `incidenceSet`.
-/
def incidenceFinset [DecidableEq V] : Finset (Sym2 V) :=
  (G.incidenceSet v).toFinset
/-
**SimpleGraph.card_incidenceSet_eq_degree** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph
`。
形式化陈述：card_incidenceSet_eq_degree [DecidableEq V] : Fintype.card (G.incidenceSet
 v) = G.degree v
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fintype.card_congr`：card_congr {α β} [Fintype α] [Fintype β] (f : α ≃ β)
 : card α = card β
· 使用定理 `SimpleGraph.card_neighborSet_eq_degree`：card_neighborSet_eq_degree : Fin
type.card (G.neighborSet v) = G.degree v
-/
theorem card_incidenceSet_eq_degree [DecidableEq V] :
    Fintype.card (G.incidenceSet v) = G.degree v := by
  rw [Fintype.card_congr (G.incidenceSetEquivNeighborSet v), card_neighborSet_eq_degree]

@[simp, norm_cast]
/-
**SimpleGraph.coe_incidenceFinset** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：coe_incidenceFinset [DecidableEq V] : (G.incidenceFinset v : Set (Sym2 V))
 = G.incidenceSet v
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.coe_toFinset`：coe_toFinset (s : Set α) [Fintype s] : (↑s.toFinset : 
Set α) = s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem coe_incidenceFinset [DecidableEq V] :
    (G.incidenceFinset v : Set (Sym2 V)) = G.incidenceSet v := by
  simp [incidenceFinset]

@[simp]
/-
**SimpleGraph.card_incidenceFinset_eq_degree** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGr
aph`。
形式化陈述：card_incidenceFinset_eq_degree [DecidableEq V] : #(G.incidenceFinset v) = 
G.degree v
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SimpleGraph.card_incidenceSet_eq_degree`：card_incidenceSet_eq_degree [De
cidableEq V] : Fintype.card (G.incidenceSet v) = G.degree v
· 使用定理 `Set.toFinset_card`：toFinset_card {α : Type*} (s : Set α) [Fintype s] : s
.toFinset.card = Fintype.card s
-/
theorem card_incidenceFinset_eq_degree [DecidableEq V] : #(G.incidenceFinset v) = G.degree v := by
  rw [← G.card_incidenceSet_eq_degree]
  apply Set.toFinset_card

@[simp]
/-
**SimpleGraph.mem_incidenceFinset** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：mem_incidenceFinset [DecidableEq V] (e : Sym2 V) : e in G.incidenceFinset 
v ↔ e in G.incidenceSet v
参数：e : Sym2 V。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_toFinset`：mem_toFinset {s : Set α} [Fintype s] {a : α} : a in s.
toFinset ↔ a in s
-/
theorem mem_incidenceFinset [DecidableEq V] (e : Sym2 V) :
    e ∈ G.incidenceFinset v ↔ e ∈ G.incidenceSet v :=
  Set.mem_toFinset
/-
**SimpleGraph.incidenceFinset_eq_filter** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：incidenceFinset_eq_filter [DecidableEq V] [Fintype G.edgeSet] : G.incidenc
eFinset v = {e in G.edgeFinset | v in e}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem incidenceFinset_eq_filter [DecidableEq V] [Fintype G.edgeSet] :
    G.incidenceFinset v = {e ∈ G.edgeFinset | v ∈ e} := by
  ext ⟨⟨⟩⟩
  simp [mk'_mem_incidenceSet_iff]
/-
**SimpleGraph.incidenceFinset_subset** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：incidenceFinset_subset [DecidableEq V] [Fintype G.edgeSet] : G.incidenceFi
nset v subseteq G.edgeFinset
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.toFinset_subset_toFinset`：toFinset_subset_toFinset [Fintype s] [Fint
ype t] : s.toFinset subseteq t.toFinset ↔ s subseteq t
· 使用定理 `SimpleGraph.incidenceSet_subset`：incidenceSet_subset (v : V) : G.inciden
ceSet v subseteq G.edgeSet
-/
theorem incidenceFinset_subset [DecidableEq V] [Fintype G.edgeSet] :
    G.incidenceFinset v ⊆ G.edgeFinset :=
  Set.toFinset_subset_toFinset.mpr (G.incidenceSet_subset v)
/-
**SimpleGraph.disjoint_incidenceFinset_of_disjoint** 是 Mathlib 中的一个定理，位于命名空间 `Si
mpleGraph`。
形式化陈述：disjoint_incidenceFinset_of_disjoint [DecidableEq V] [Fintype <| H.neighbo
rSet v] (h : Disjoint G H) : Disjoint (G.incidenceFinset v) (H.incidenceFinset v
)
参数：h : Disjoint G H。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.coe_incidenceFinset`：coe_incidenceFinset [DecidableEq V] : (
G.incidenceFinset v : Set (Sym2 V)) = G.incidenceSet v
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `SimpleGraph.disjoint_incidenceSet`：disjoint_incidenceSet : (forall v, Di
sjoint (G.incidenceSet v) (H.incidenceSet v)) ↔ Disjoint G H
-/
theorem disjoint_incidenceFinset_of_disjoint [DecidableEq V] [Fintype <| H.neighborSet v]
    (h : Disjoint G H) : Disjoint (G.incidenceFinset v) (H.incidenceFinset v) := by
  simp [← Finset.disjoint_coe, disjoint_incidenceSet.mpr h v]

/-- The degree of a vertex is at most the number of edges. -/
/-
**SimpleGraph.degree_le_card_edgeFinset** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：degree_le_card_edgeFinset [Fintype G.edgeSet] : G.degree v <= #G.edgeFinse
t
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SimpleGraph.card_incidenceFinset_eq_degree`：card_incidenceFinset_eq_degr
ee [DecidableEq V] : #(G.incidenceFinset v) = G.degree v
· 使用定理 `Finset.card_le_card`：card_le_card : s subseteq t -> #s <= #t
· 使用定理 `SimpleGraph.incidenceFinset_subset`：incidenceFinset_subset [DecidableEq 
V] [Fintype G.edgeSet] : G.incidenceFinset v subseteq G.edgeFinset

--- 原说明 ---
The degree of a vertex is at most the number of edges.
-/
theorem degree_le_card_edgeFinset [Fintype G.edgeSet] :
    G.degree v ≤ #G.edgeFinset := by
  classical
  rw [← card_incidenceFinset_eq_degree]
  exact card_le_card (G.incidenceFinset_subset v)

variable {G v}

/-- If `G ≤ H` then `G.degree v ≤ H.degree v` for any vertex `v`. -/
/-
**SimpleGraph.degree_le_of_le** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
形式化陈述：degree_le_of_le {H : SimpleGraph V} [Fintype (H.neighborSet v)] (hle : G <
= H) : G.degree v <= H.degree v
参数：H.neighborSet v；hle : G <= H。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.card_le_card`：card_le_card {s t : Set α} [Fintype s] [Fintype t] (hs
ub : s subseteq t) : Fintype.card s <= Fintype.card t

--- 原说明 ---
If `G ≤ H` then `G.degree v ≤ H.degree v` for any vertex `v`.
-/
lemma degree_le_of_le {H : SimpleGraph V} [Fintype (H.neighborSet v)] (hle : G ≤ H) :
    G.degree v ≤ H.degree v := by
  simp_rw [← card_neighborSet_eq_degree]
  exact Set.card_le_card fun v hv => hle hv
/-
**SimpleGraph.degree_lt_card_verts** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：degree_lt_card_verts [Fintype V] [DecidableRel G.Adj] (v : V) : G.degree v
 < Fintype.card V
参数：v : V。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.card_lt_univ_of_notMem`：Finset.card_lt_univ_of_notMem [Fintype α]
 {s : Finset α} {x : α} (hx : x ∉ s) : #s < Fintype.card α
· 使用定理 `SimpleGraph.notMem_neighborFinset_self`：notMem_neighborFinset_self : v ∉
 G.neighborFinset v
-/
theorem degree_lt_card_verts [Fintype V] [DecidableRel G.Adj] (v : V) :
    G.degree v < Fintype.card V :=
  Finset.card_lt_univ_of_notMem <| G.notMem_neighborFinset_self v

end FiniteAt

section LocallyFinite

/-- A graph is locally finite if every vertex has a finite neighbor set. -/
/-
**SimpleGraph.LocallyFinite** 是 Mathlib 中的一个缩写定义，位于命名空间 `SimpleGraph`。
形式化陈述：LocallyFinite
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A graph is locally finite if every vertex has a finite neighbor set.
-/
abbrev LocallyFinite :=
  ∀ v : V, Fintype (G.neighborSet v)

variable [LocallyFinite G]

/-- A locally finite simple graph is regular of degree `d` if every vertex has degree `d`. -/
@[wikidata Q826467]
/-
**SimpleGraph.IsRegularOfDegree** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph`。
形式化陈述：IsRegularOfDegree (d : Nat) : Prop
参数：d : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A locally finite simple graph is regular of degree `d` if every vertex has degre
e `d`.
-/
def IsRegularOfDegree (d : ℕ) : Prop :=
  ∀ v : V, G.degree v = d

variable {G}
/-
**SimpleGraph.IsRegularOfDegree.degree_eq** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph
.IsRegularOfDegree`。
形式化陈述：∀ {V : Type u_1} {G : SimpleGraph V} [inst : G.LocallyFinite] {d : ℕ}, G.I
sRegularOfDegree d → ∀ (v : V), G.degree v = d
参数：v : V。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem IsRegularOfDegree.degree_eq {d : ℕ} (h : G.IsRegularOfDegree d) (v : V) : G.degree v = d :=
  h v

/-- The empty graph is regular of any degree `d` -/
@[simp]
/-
**SimpleGraph.IsRegularOfDegree.of_isEmpty** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGrap
h.IsRegularOfDegree`。
形式化陈述：∀ {V : Type u_1} {G : SimpleGraph V} [inst : G.LocallyFinite] [IsEmpty V] 
{d : ℕ}, G.IsRegularOfDegree d
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The empty graph is regular of any degree `d`
-/
theorem IsRegularOfDegree.of_isEmpty [IsEmpty V] {d : ℕ} : G.IsRegularOfDegree d :=
  IsEmpty.elim ‹_›
/-
**SimpleGraph.IsRegularOfDegree.compl** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.IsR
egularOfDegree`。
形式化陈述：∀ {V : Type u_1} [inst : Fintype V] [inst_1 : DecidableEq V] {G : SimpleGr
aph V} [inst_2 : DecidableRel G.Adj] {k : ℕ},   G.IsRegularOfDegree k → Gᶜ.IsReg
ularOfDegree (Fintype.card V - 1 - k)
参数：Fintype.card V - 1 - k。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.degree_compl`：degree_compl [Fintype (Gᶜ.neighborSet v)] [Fin
type V] : Gᶜ.degree v = Fintype.card V - 1 - G.degree v
-/
theorem IsRegularOfDegree.compl [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
    {k : ℕ} (h : G.IsRegularOfDegree k) : Gᶜ.IsRegularOfDegree (Fintype.card V - 1 - k) := by
  intro v
  rw [degree_compl, h v]

end LocallyFinite

section Finite

variable [Fintype V]

/-- `Fintype` for `neighborSet` -/
@[deprecated inferInstance (since := "2026-04-29")]
/-
**SimpleGraph.neighborSetFintype** 是 Mathlib 中的一个缩写定义，位于命名空间 `SimpleGraph`。
形式化陈述：neighborSetFintype [DecidableRel G.Adj] (v : V) : Fintype (G.neighborSet v
)
参数：v : V。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Fintype` for `neighborSet`
-/
abbrev neighborSetFintype [DecidableRel G.Adj] (v : V) : Fintype (G.neighborSet v) :=
  inferInstance
/-
**SimpleGraph.neighborFinset_eq_filter** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：neighborFinset_eq_filter {v : V} [DecidableRel G.Adj] : G.neighborFinset v
 = ({w | G.Adj v w} : Finset _)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
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
theorem neighborFinset_eq_filter {v : V} [DecidableRel G.Adj] :
    G.neighborFinset v = ({w | G.Adj v w} : Finset _) := by ext; simp
/-
**SimpleGraph.neighborFinset_compl** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：neighborFinset_compl [DecidableEq V] [DecidableRel G.Adj] (v : V) : Gᶜ.nei
ghborFinset v = (G.neighborFinset v)ᶜ \ {v}
参数：v : V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.toFinset_congr`：toFinset_congr {s t : Set α} [Fintype s] [Fintype t]
 (h : s = t) : toFinset s = toFinset t
· 使用定理 `SimpleGraph.neighborSet_compl`：neighborSet_compl (G : SimpleGraph V) (v 
: V) : Gᶜ.neighborSet v = (G.neighborSet v)ᶜ \ {v}
· 使用定理 `Set.toFinset_sdiff`：toFinset_sdiff [Fintype (s \ t : Set _)] : (s \ t).t
oFinset = s.toFinset \ t.toFinset
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Set.toFinset_compl`：toFinset_compl [Fintype α] [Fintype (sᶜ : Set _)] : 
sᶜ.toFinset = s.toFinsetᶜ
· 使用定理 `Set.toFinset_singleton`：toFinset_singleton (a : α) [Fintype ({a} : Set α
)] : ({a} : Set α).toFinset = {a}
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem neighborFinset_compl [DecidableEq V] [DecidableRel G.Adj] (v : V) :
    Gᶜ.neighborFinset v = (G.neighborFinset v)ᶜ \ {v} := by
  simp only [neighborFinset, neighborSet_compl, Set.toFinset_sdiff, Set.toFinset_compl,
    Set.toFinset_singleton]

@[simp]
/-
**SimpleGraph.complete_graph_degree** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：complete_graph_degree [DecidableEq V] (v : V) : (completeGraph V).degree v
 = Fintype.card V - 1
参数：v : V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.neighborFinset_eq_filter`：neighborFinset_eq_filter {v : V} [
DecidableRel G.Adj] : G.neighborFinset v = ({w | G.Adj v w} : Finset _)
· 使用定理 `Finset.filter_congr`：∀ {α : Type u_1} {p q : α → Prop} [inst : Decidable
Pred p] [inst_1 : DecidablePred q] {s : Finset α},   (∀ x ∈ s, p x ↔ q x) → Fins
et.filter…
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Finset.filter_ne`：filter_ne [DecidableEq β] (s : Finset β) (b : β) : (s.
filter fun a => b != a) = s.erase b
· 使用定理 `Finset.card_erase_of_mem`：card_erase_of_mem : a in s -> #(s.erase a) = #
s - 1
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)
· 使用定理 `Finset.card_univ`：Finset.card_univ [Fintype α] : #(univ : Finset α) = Fi
ntype.card α
-/
theorem complete_graph_degree [DecidableEq V] (v : V) :
    (completeGraph V).degree v = Fintype.card V - 1 := by
  simp_rw [degree, neighborFinset_eq_filter, top_adj, filter_ne]
  rw [card_erase_of_mem (mem_univ v), card_univ]
/-
**SimpleGraph.bot_degree** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：bot_degree (v : V) : (⊥ : SimpleGraph V).degree v = 0
参数：v : V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.IsIsolated.degree_eq_zero`：∀ {V : Type u_1} (G : SimpleGraph
 V) (v : V) [inst : Fintype ↑(G.neighborSet v)], G.IsIsolated v → G.degree v = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem bot_degree (v : V) : (⊥ : SimpleGraph V).degree v = 0 := by
  simp
/-
**SimpleGraph.IsRegularOfDegree.top** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.IsReg
ularOfDegree`。
形式化陈述：∀ {V : Type u_1} [inst : Fintype V] [inst_1 : DecidableEq V], ⊤.IsRegularO
fDegree (Fintype.card V - 1)
参数：Fintype.card V - 1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.complete_graph_degree`：complete_graph_degree [DecidableEq V]
 (v : V) : (completeGraph V).degree v = Fintype.card V - 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem IsRegularOfDegree.top [DecidableEq V] :
    (⊤ : SimpleGraph V).IsRegularOfDegree (Fintype.card V - 1) := by
  simp [IsRegularOfDegree]

@[simp]
/-
**SimpleGraph.IsRegularOfDegree.bot** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.IsReg
ularOfDegree`。
形式化陈述：∀ {V : Type u_1} [inst : Fintype V], ⊥.IsRegularOfDegree 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.bot_degree`：bot_degree (v : V) : (⊥ : SimpleGraph V).degree 
v = 0
-/
theorem IsRegularOfDegree.bot : (⊥ : SimpleGraph V).IsRegularOfDegree 0 :=
  bot_degree

/-- The minimum degree of all vertices (and `0` if there are no vertices).
The key properties of this are given in `exists_minimal_degree_vertex`, `minDegree_le_degree`
and `le_minDegree_of_forall_le_degree`. -/
/-
**SimpleGraph.minDegree** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph`。
形式化陈述：minDegree [DecidableRel G.Adj] : Nat
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The minimum degree of all vertices (and `0` if there are no vertices).
The key properties of this are given in `exists_minimal_degree_vertex`, `minDegr
ee_le_degree`
and `le_minDegree_of_forall_le_degree`.
-/
def minDegree [DecidableRel G.Adj] : ℕ :=
  WithTop.untopD 0 (univ.image fun v => G.degree v).min

/-- There exists a vertex of minimal degree. Note the assumption of being nonempty is necessary, as
the lemma implies there exists a vertex. -/
/-
**SimpleGraph.exists_minimal_degree_vertex** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGrap
h`。
形式化陈述：exists_minimal_degree_vertex [DecidableRel G.Adj] [Nonempty V] : exists v,
 G.minDegree = G.degree v
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
There exists a vertex of minimal degree. Note the assumption of being nonempty i
s necessary, as
the lemma implies there exists a vertex.
-/
theorem exists_minimal_degree_vertex [DecidableRel G.Adj] [Nonempty V] :
    ∃ v, G.minDegree = G.degree v := by
  grind [minDegree, WithTop.untopD_coe, min_mem_image_coe <| univ_nonempty.image (G.degree ·)]

/-- The minimum degree in the graph is at most the degree of any particular vertex. -/
/-
**SimpleGraph.minDegree_le_degree** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：minDegree_le_degree [DecidableRel G.Adj] (v : V) : G.minDegree <= G.degree
 v
参数：v : V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithTop.untopD_le`：∀ {α : Type u_1} [inst : PartialOrder α] {y : WithTop
 α} {a b : α}, y ≤ ↑b → WithTop.untopD a y ≤ b
· 使用定理 `Finset.min_le`：min_le {a : α} {s : Finset α} (as : a in s) : s.min <= a
· 使用定理 `Finset.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {a} (h : a in s) 
: f a in s.image f
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)

--- 原说明 ---
The minimum degree in the graph is at most the degree of any particular vertex.
-/
theorem minDegree_le_degree [DecidableRel G.Adj] (v : V) : G.minDegree ≤ G.degree v :=
  WithTop.untopD_le <| Finset.min_le <| mem_image_of_mem (G.degree ·) <| mem_univ v

/-- In a nonempty graph, if `k` is at most the degree of every vertex, it is at most the minimum
degree. Note the assumption that the graph is nonempty is necessary as long as `G.minDegree` is
defined to be a natural. -/
/-
**SimpleGraph.le_minDegree_of_forall_le_degree** 是 Mathlib 中的一个定理，位于命名空间 `Simple
Graph`。
形式化陈述：le_minDegree_of_forall_le_degree [DecidableRel G.Adj] [Nonempty V] (k : Na
t) (h : forall v, k <= G.degree v) : k <= G.minDegree
参数：k : Nat；h : forall v, k <= G.degree v。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.exists_minimal_degree_vertex`：exists_minimal_degree_vertex [
DecidableRel G.Adj] [Nonempty V] : exists v, G.minDegree = G.degree v
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂

--- 原说明 ---
In a nonempty graph, if `k` is at most the degree of every vertex, it is at most
 the minimum
degree. Note the assumption that the graph is nonempty is necessary as long as `
G.minDegree` is
defined to be a natural.
-/
theorem le_minDegree_of_forall_le_degree [DecidableRel G.Adj] [Nonempty V] (k : ℕ)
    (h : ∀ v, k ≤ G.degree v) : k ≤ G.minDegree := by
  rcases G.exists_minimal_degree_vertex with ⟨v, hv⟩
  rw [hv]
  apply h

@[simp]
/-
**SimpleGraph.minDegree_of_subsingleton** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
形式化陈述：minDegree_of_subsingleton [DecidableRel G.Adj] [Subsingleton V] : G.minDeg
ree = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `SimpleGraph.IsIsolated.degree_eq_zero`：∀ {V : Type u_1} (G : SimpleGraph
 V) (v : V) [inst : Fintype ↑(G.neighborSet v)], G.IsIsolated v → G.degree v = 0
· 使用定理 `Finset.univ_eq_empty`：univ_eq_empty [IsEmpty α] : (univ : Finset α) = ∅
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finset.image_const`：image_const {s : Finset α} (h : s.Nonempty) (b : β) 
: (s.image fun _ => b) = singleton b
· 使用定理 `Finset.min_singleton`：min_singleton {a : α} : Finset.min {a} = (a : With
Top α)
-/
lemma minDegree_of_subsingleton [DecidableRel G.Adj] [Subsingleton V] : G.minDegree = 0 := by
  cases isEmpty_or_nonempty V <;>
    simp [minDegree, Finset.image_const]

@[deprecated (since := "2026-06-15")] alias minDegree_of_isEmpty := minDegree_of_subsingleton

variable {G} in
/-- If `G` is a subgraph of `H` then `G.minDegree ≤ H.minDegree`. -/
@[gcongr]
/-
**SimpleGraph.minDegree_le_minDegree** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
形式化陈述：minDegree_le_minDegree {H : SimpleGraph V} [DecidableRel G.Adj] [Decidable
Rel H.Adj] (hle : G <= H) : G.minDegree <= H.minDegree
参数：hle : G <= H。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `SimpleGraph.minDegree_of_subsingleton`：minDegree_of_subsingleton [Decida
bleRel G.Adj] [Subsingleton V] : G.minDegree = 0
· 使用定理 `IsEmpty.instSubsingleton`：∀ {α : Sort u} [IsEmpty α], Subsingleton α
· 使用定理 `SimpleGraph.le_minDegree_of_forall_le_degree`：le_minDegree_of_forall_le_
degree [DecidableRel G.Adj] [Nonempty V] (k : Nat) (h : forall v, k <= G.degree 
v) : k <= G.minDegree
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `SimpleGraph.minDegree_le_degree`：minDegree_le_degree [DecidableRel G.Adj
] (v : V) : G.minDegree <= G.degree v
· 使用引理 `SimpleGraph.degree_le_of_le`：degree_le_of_le {H : SimpleGraph V} [Fintyp
e (H.neighborSet v)] (hle : G <= H) : G.degree v <= H.degree v

--- 原说明 ---
If `G` is a subgraph of `H` then `G.minDegree ≤ H.minDegree`.
-/
lemma minDegree_le_minDegree {H : SimpleGraph V} [DecidableRel G.Adj] [DecidableRel H.Adj]
    (hle : G ≤ H) : G.minDegree ≤ H.minDegree := by
  cases isEmpty_or_nonempty V
  · simp
  · apply le_minDegree_of_forall_le_degree
    exact fun v ↦ (G.minDegree_le_degree v).trans (G.degree_le_of_le hle)

/-- In a nonempty graph, the minimal degree is less than the number of vertices. -/
/-
**SimpleGraph.minDegree_lt_card** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：minDegree_lt_card [DecidableRel G.Adj] [Nonempty V] : G.minDegree < Fintyp
e.card V
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.exists_minimal_degree_vertex`：exists_minimal_degree_vertex [
DecidableRel G.Adj] [Nonempty V] : exists v, G.minDegree = G.degree v
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.degree_lt_card_verts`：degree_lt_card_verts [Fintype V] [Deci
dableRel G.Adj] (v : V) : G.degree v < Fintype.card V

--- 原说明 ---
In a nonempty graph, the minimal degree is less than the number of vertices.
-/
theorem minDegree_lt_card [DecidableRel G.Adj] [Nonempty V] :
    G.minDegree < Fintype.card V := by
  have ⟨v, hv⟩ := G.exists_minimal_degree_vertex
  rw [hv]
  apply degree_lt_card_verts

/-- The maximum degree of all vertices (and `0` if there are no vertices).
The key properties of this are given in `exists_maximal_degree_vertex`, `degree_le_maxDegree`
and `maxDegree_le_of_forall_degree_le`. -/
/-
**SimpleGraph.maxDegree** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph`。
形式化陈述：maxDegree [DecidableRel G.Adj] : Nat
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The maximum degree of all vertices (and `0` if there are no vertices).
The key properties of this are given in `exists_maximal_degree_vertex`, `degree_
le_maxDegree`
and `maxDegree_le_of_forall_degree_le`.
-/
def maxDegree [DecidableRel G.Adj] : ℕ :=
  WithBot.unbotD 0 (univ.image fun v => G.degree v).max

/-- There exists a vertex of maximal degree. Note the assumption of being nonempty is necessary, as
the lemma implies there exists a vertex. -/
/-
**SimpleGraph.exists_maximal_degree_vertex** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGrap
h`。
形式化陈述：exists_maximal_degree_vertex [DecidableRel G.Adj] [Nonempty V] : exists v,
 G.maxDegree = G.degree v
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
There exists a vertex of maximal degree. Note the assumption of being nonempty i
s necessary, as
the lemma implies there exists a vertex.
-/
theorem exists_maximal_degree_vertex [DecidableRel G.Adj] [Nonempty V] :
    ∃ v, G.maxDegree = G.degree v := by
  grind [maxDegree, WithBot.unbotD_coe, max_mem_image_coe <| univ_nonempty.image (G.degree ·)]

/-- The maximum degree in the graph is at least the degree of any particular vertex. -/
/-
**SimpleGraph.degree_le_maxDegree** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：degree_le_maxDegree [DecidableRel G.Adj] (v : V) : G.degree v <= G.maxDegr
ee
参数：v : V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `WithBot.le_unbotD`：le_unbotD (hy : b <= y) : b <= y.unbotD a
· 使用定理 `Finset.le_max`：le_max {a : α} {s : Finset α} (as : a in s) : ↑a <= s.max
· 使用定理 `Finset.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {a} (h : a in s) 
: f a in s.image f
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)

--- 原说明 ---
The maximum degree in the graph is at least the degree of any particular vertex.
-/
theorem degree_le_maxDegree [DecidableRel G.Adj] (v : V) : G.degree v ≤ G.maxDegree :=
  WithBot.le_unbotD <| Finset.le_max <| mem_image_of_mem (G.degree ·) <| mem_univ v

@[simp]
/-
**SimpleGraph.maxDegree_of_subsingleton** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
形式化陈述：maxDegree_of_subsingleton [DecidableRel G.Adj] [Subsingleton V] : G.maxDeg
ree = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `SimpleGraph.IsIsolated.degree_eq_zero`：∀ {V : Type u_1} (G : SimpleGraph
 V) (v : V) [inst : Fintype ↑(G.neighborSet v)], G.IsIsolated v → G.degree v = 0
· 使用定理 `Finset.univ_eq_empty`：univ_eq_empty [IsEmpty α] : (univ : Finset α) = ∅
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finset.image_const`：image_const {s : Finset α} (h : s.Nonempty) (b : β) 
: (s.image fun _ => b) = singleton b
· 使用定理 `Finset.max_singleton`：max_singleton {a : α} : Finset.max {a} = (a : With
Bot α)
-/
lemma maxDegree_of_subsingleton [DecidableRel G.Adj] [Subsingleton V] : G.maxDegree = 0 := by
  cases isEmpty_or_nonempty V <;>
    simp [maxDegree, Finset.image_const]

@[deprecated (since := "2026-06-15")] alias maxDegree_of_isEmpty := maxDegree_of_subsingleton

/-- In a graph, if `k` is at least the degree of every vertex, then it is at least the maximum
degree. -/
/-
**SimpleGraph.maxDegree_le_of_forall_degree_le** 是 Mathlib 中的一个定理，位于命名空间 `Simple
Graph`。
形式化陈述：maxDegree_le_of_forall_degree_le [DecidableRel G.Adj] (k : Nat) (h : foral
l v, G.degree v <= k) : G.maxDegree <= k
参数：k : Nat；h : forall v, G.degree v <= k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `SimpleGraph.maxDegree_of_subsingleton`：maxDegree_of_subsingleton [Decida
bleRel G.Adj] [Subsingleton V] : G.maxDegree = 0
· 使用定理 `IsEmpty.instSubsingleton`：∀ {α : Sort u} [IsEmpty α], Subsingleton α
· 使用定理 `SimpleGraph.exists_maximal_degree_vertex`：exists_maximal_degree_vertex [
DecidableRel G.Adj] [Nonempty V] : exists v, G.maxDegree = G.degree v
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
In a graph, if `k` is at least the degree of every vertex, then it is at least t
he maximum
degree.
-/
theorem maxDegree_le_of_forall_degree_le [DecidableRel G.Adj] (k : ℕ) (h : ∀ v, G.degree v ≤ k) :
    G.maxDegree ≤ k := by
  cases isEmpty_or_nonempty V
  · simp
  · obtain ⟨_, hv⟩ := G.exists_maximal_degree_vertex
    exact hv ▸ h _
/-
**SimpleGraph.IsRegularOfDegree.maxDegree_eq** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGr
aph.IsRegularOfDegree`。
形式化陈述：∀ {V : Type u_1} (G : SimpleGraph V) [inst : Fintype V] [Nonempty V] [inst
_2 : DecidableRel G.Adj] {d : ℕ},   G.IsRegularOfDegree d → G.maxDegree = d
参数：G : SimpleGraph V。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `SimpleGraph.IsRegularOfDegree.degree_eq`：∀ {V : Type u_1} {G : SimpleGra
ph V} [inst : G.LocallyFinite] {d : ℕ}, G.IsRegularOfDegree d → ∀ (v : V), G.deg
ree v = d
· 使用定理 `Finset.image_const`：image_const {s : Finset α} (h : s.Nonempty) (b : β) 
: (s.image fun _ => b) = singleton b
· 使用定理 `Finset.max_singleton`：max_singleton {a : α} : Finset.max {a} = (a : With
Bot α)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem IsRegularOfDegree.maxDegree_eq [Nonempty V] [DecidableRel G.Adj] {d : ℕ}
    (h : G.IsRegularOfDegree d) : G.maxDegree = d := by
  simp [maxDegree, h.degree_eq, Finset.image_const]

@[simp]
/-
**SimpleGraph.maxDegree_bot_eq_zero** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
形式化陈述：maxDegree_bot_eq_zero : (⊥ : SimpleGraph V).maxDegree = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.le_zero`：∀ {i : ℕ}, i ≤ 0 ↔ i = 0
· 使用定理 `SimpleGraph.maxDegree_le_of_forall_degree_le`：maxDegree_le_of_forall_deg
ree_le [DecidableRel G.Adj] (k : Nat) (h : forall v, G.degree v <= k) : G.maxDeg
ree <= k
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.IsIsolated.degree_eq_zero`：∀ {V : Type u_1} (G : SimpleGraph
 V) (v : V) [inst : Fintype ↑(G.neighborSet v)], G.IsIsolated v → G.degree v = 0
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma maxDegree_bot_eq_zero : (⊥ : SimpleGraph V).maxDegree = 0 :=
  Nat.le_zero.1 <| maxDegree_le_of_forall_degree_le _ _ (by simp)

variable {G} in
@[simp]
/-
**SimpleGraph.maxDegree_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：maxDegree_eq_zero_iff [DecidableRel G.Adj] : G.maxDegree = 0 ↔ G = ⊥
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.eq_bot_iff_isIsolated`：eq_bot_iff_isIsolated : G = ⊥ ↔ foral
l v, G.IsIsolated v
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Lean.Meta.FastSubsingleton.elim`：∀ {α : Sort u} [h : Meta.FastSubsinglet
on α] (a b : α), a = b
· 使用定理 `Fintype.instFastSubsingleton`：∀ (α : Type u_4), Meta.FastSubsingleton (F
intype α)
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `Lean.Meta.instFastSubsingletonForall`：∀ {α : Sort u} {β : α → Sort v} [i
nst : ∀ (x : α), Meta.FastSubsingleton (β x)], Meta.FastSubsingleton ((x : α) → 
β x)
· 使用定理 `Lean.Meta.instFastSubsingletonDecidable`：∀ {p : Prop}, Meta.FastSubsingl
eton (Decidable p)
· 使用引理 `SimpleGraph.maxDegree_bot_eq_zero`：maxDegree_bot_eq_zero : (⊥ : SimpleGr
aph V).maxDegree = 0
-/
theorem maxDegree_eq_zero_iff [DecidableRel G.Adj] : G.maxDegree = 0 ↔ G = ⊥ := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rw [eq_bot_iff_isIsolated]
    intro v
    grind [degree_eq_zero, G.degree_le_maxDegree v]
  · convert maxDegree_bot_eq_zero
    assumption

@[simp]
/-
**SimpleGraph.maxDegree_top** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
形式化陈述：maxDegree_top [DecidableEq V] : (⊤ : SimpleGraph V).maxDegree = Fintype.ca
rd V - 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `SimpleGraph.maxDegree_of_subsingleton`：maxDegree_of_subsingleton [Decida
bleRel G.Adj] [Subsingleton V] : G.maxDegree = 0
· 使用定理 `IsEmpty.instSubsingleton`：∀ {α : Sort u} [IsEmpty α], Subsingleton α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Fintype.card_eq_zero`：∀ {α : Type u_1} [inst : Fintype α] [IsEmpty α], F
intype.card α = 0
· 使用定理 `Nat.sub_eq_zero_of_le`：∀ {n m : ℕ}, n ≤ m → n - m = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `SimpleGraph.IsRegularOfDegree.maxDegree_eq`：∀ {V : Type u_1} (G : Simple
Graph V) [inst : Fintype V] [Nonempty V] [inst_2 : DecidableRel G.Adj] {d : ℕ}, 
  G.IsRegularOfDegree d → G.maxD…
· 使用定理 `SimpleGraph.IsRegularOfDegree.top`：∀ {V : Type u_1} [inst : Fintype V] [
inst_1 : DecidableEq V], ⊤.IsRegularOfDegree (Fintype.card V - 1)
-/
lemma maxDegree_top [DecidableEq V] : (⊤ : SimpleGraph V).maxDegree = Fintype.card V - 1 := by
  cases isEmpty_or_nonempty V
  · simp
  exact IsRegularOfDegree.top.maxDegree_eq

@[simp]
/-
**SimpleGraph.minDegree_le_maxDegree** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
形式化陈述：minDegree_le_maxDegree [DecidableRel G.Adj] : G.minDegree <= G.maxDegree
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `SimpleGraph.minDegree_of_subsingleton`：minDegree_of_subsingleton [Decida
bleRel G.Adj] [Subsingleton V] : G.minDegree = 0
· 使用定理 `IsEmpty.instSubsingleton`：∀ {α : Sort u} [IsEmpty α], Subsingleton α
· 使用引理 `SimpleGraph.maxDegree_of_subsingleton`：maxDegree_of_subsingleton [Decida
bleRel G.Adj] [Subsingleton V] : G.maxDegree = 0
· 使用定理 `Nonempty.elim`：∀ {α : Sort u} {p : Prop}, Nonempty α → (∀ (a : α), p) → 
p
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `SimpleGraph.minDegree_le_degree`：minDegree_le_degree [DecidableRel G.Adj
] (v : V) : G.minDegree <= G.degree v
· 使用定理 `SimpleGraph.degree_le_maxDegree`：degree_le_maxDegree [DecidableRel G.Adj
] (v : V) : G.degree v <= G.maxDegree
-/
lemma minDegree_le_maxDegree [DecidableRel G.Adj] : G.minDegree ≤ G.maxDegree := by
  by_cases! he : IsEmpty V
  · simp
  · exact he.elim fun v ↦ (minDegree_le_degree _ v).trans (degree_le_maxDegree _ v)
/-
**SimpleGraph.IsRegularOfDegree.minDegree_eq** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGr
aph.IsRegularOfDegree`。
形式化陈述：∀ {V : Type u_1} (G : SimpleGraph V) [inst : Fintype V] [Nonempty V] [inst
_2 : DecidableRel G.Adj] {d : ℕ},   G.IsRegularOfDegree d → G.minDegree = d
参数：G : SimpleGraph V。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `SimpleGraph.IsRegularOfDegree.degree_eq`：∀ {V : Type u_1} {G : SimpleGra
ph V} [inst : G.LocallyFinite] {d : ℕ}, G.IsRegularOfDegree d → ∀ (v : V), G.deg
ree v = d
· 使用定理 `Finset.image_const`：image_const {s : Finset α} (h : s.Nonempty) (b : β) 
: (s.image fun _ => b) = singleton b
· 使用定理 `Finset.min_singleton`：min_singleton {a : α} : Finset.min {a} = (a : With
Top α)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem IsRegularOfDegree.minDegree_eq [Nonempty V] [DecidableRel G.Adj] {d : ℕ}
    (h : G.IsRegularOfDegree d) : G.minDegree = d := by
  simp [minDegree, h.degree_eq, Finset.image_const]

@[simp]
/-
**SimpleGraph.minDegree_bot_eq_zero** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
形式化陈述：minDegree_bot_eq_zero : (⊥ : SimpleGraph V).minDegree = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.le_zero`：∀ {i : ℕ}, i ≤ 0 ↔ i = 0
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `SimpleGraph.minDegree_le_maxDegree`：minDegree_le_maxDegree [DecidableRel
 G.Adj] : G.minDegree <= G.maxDegree
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `SimpleGraph.maxDegree_bot_eq_zero`：maxDegree_bot_eq_zero : (⊥ : SimpleGr
aph V).maxDegree = 0
-/
lemma minDegree_bot_eq_zero : (⊥ : SimpleGraph V).minDegree = 0 :=
  Nat.le_zero.1 <| (minDegree_le_maxDegree _).trans (by simp)

variable {G} in
/-
**SimpleGraph.minDegree_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：minDegree_eq_zero_iff [DecidableRel G.Adj] [Nonempty V] : G.minDegree = 0 
↔ exists v, G.IsIsolated v
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem minDegree_eq_zero_iff [DecidableRel G.Adj] [Nonempty V] :
    G.minDegree = 0 ↔ ∃ v, G.IsIsolated v := by
  refine ⟨fun h ↦ ?_, fun ⟨v, hv⟩ ↦ ?_⟩
  · grind [G.exists_minimal_degree_vertex, degree_eq_zero]
  · grind [G.minDegree_le_degree v, degree_eq_zero]

variable {G} in
/-
**SimpleGraph.minDegree_eq_zero_iff_support_ne** 是 Mathlib 中的一个定理，位于命名空间 `Simple
Graph`。
形式化陈述：minDegree_eq_zero_iff_support_ne [DecidableRel G.Adj] [Nonempty V] : G.min
Degree = 0 ↔ G.support != .univ
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
theorem minDegree_eq_zero_iff_support_ne [DecidableRel G.Adj] [Nonempty V] :
    G.minDegree = 0 ↔ G.support ≠ .univ := by
  simp [Set.ne_univ_iff_exists_notMem, minDegree_eq_zero_iff]

@[simp]
/-
**SimpleGraph.minDegree_top** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
形式化陈述：minDegree_top [DecidableEq V] : (⊤ : SimpleGraph V).minDegree = Fintype.ca
rd V - 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `SimpleGraph.minDegree_of_subsingleton`：minDegree_of_subsingleton [Decida
bleRel G.Adj] [Subsingleton V] : G.minDegree = 0
· 使用定理 `IsEmpty.instSubsingleton`：∀ {α : Sort u} [IsEmpty α], Subsingleton α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Fintype.card_eq_zero`：∀ {α : Type u_1} [inst : Fintype α] [IsEmpty α], F
intype.card α = 0
· 使用定理 `Nat.sub_eq_zero_of_le`：∀ {n m : ℕ}, n ≤ m → n - m = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `SimpleGraph.IsRegularOfDegree.minDegree_eq`：∀ {V : Type u_1} (G : Simple
Graph V) [inst : Fintype V] [Nonempty V] [inst_2 : DecidableRel G.Adj] {d : ℕ}, 
  G.IsRegularOfDegree d → G.minD…
· 使用定理 `SimpleGraph.IsRegularOfDegree.top`：∀ {V : Type u_1} [inst : Fintype V] [
inst_1 : DecidableEq V], ⊤.IsRegularOfDegree (Fintype.card V - 1)
-/
lemma minDegree_top [DecidableEq V] : (⊤ : SimpleGraph V).minDegree = Fintype.card V - 1 := by
  cases isEmpty_or_nonempty V
  · simp
  exact IsRegularOfDegree.top.minDegree_eq

/--
The maximum degree of a nonempty graph is less than the number of vertices. Note that the assumption
that `V` is nonempty is necessary, as otherwise this would assert the existence of a
natural number less than zero. -/
/-
**SimpleGraph.maxDegree_lt_card_verts** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：maxDegree_lt_card_verts [DecidableRel G.Adj] [Nonempty V] : G.maxDegree < 
Fintype.card V
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.exists_maximal_degree_vertex`：exists_maximal_degree_vertex [
DecidableRel G.Adj] [Nonempty V] : exists v, G.maxDegree = G.degree v
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.degree_lt_card_verts`：degree_lt_card_verts [Fintype V] [Deci
dableRel G.Adj] (v : V) : G.degree v < Fintype.card V

--- 原说明 ---
The maximum degree of a nonempty graph is less than the number of vertices. Note
 that the assumption
that `V` is nonempty is necessary, as otherwise this would assert the existence 
of a
natural number less than zero.
-/
theorem maxDegree_lt_card_verts [DecidableRel G.Adj] [Nonempty V] :
    G.maxDegree < Fintype.card V := by
  obtain ⟨v, hv⟩ := G.exists_maximal_degree_vertex
  rw [hv]
  apply G.degree_lt_card_verts v
/-
**SimpleGraph.card_commonNeighbors_le_degree_left** 是 Mathlib 中的一个定理，位于命名空间 `Sim
pleGraph`。
形式化陈述：card_commonNeighbors_le_degree_left [DecidableRel G.Adj] (v w : V) : Finty
pe.card (G.commonNeighbors v w) <= G.degree v
参数：v w : V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SimpleGraph.card_neighborSet_eq_degree`：card_neighborSet_eq_degree : Fin
type.card (G.neighborSet v) = G.degree v
· 使用定理 `Set.card_le_card`：card_le_card {s t : Set α} [Fintype s] [Fintype t] (hs
ub : s subseteq t) : Fintype.card s <= Fintype.card t
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
-/
theorem card_commonNeighbors_le_degree_left [DecidableRel G.Adj] (v w : V) :
    Fintype.card (G.commonNeighbors v w) ≤ G.degree v := by
  rw [← card_neighborSet_eq_degree]
  exact Set.card_le_card Set.inter_subset_left
/-
**SimpleGraph.card_commonNeighbors_le_degree_right** 是 Mathlib 中的一个定理，位于命名空间 `Si
mpleGraph`。
形式化陈述：card_commonNeighbors_le_degree_right [DecidableRel G.Adj] (v w : V) : Fint
ype.card (G.commonNeighbors v w) <= G.degree w
参数：v w : V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fintype.card_congr'`：card_congr' {α β} [Fintype α] [Fintype β] (h : α = 
β) : card α = card β
· 使用定理 `SimpleGraph.commonNeighbors_symm`：commonNeighbors_symm (v w : V) : G.com
monNeighbors v w = G.commonNeighbors w v
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
-/
theorem card_commonNeighbors_le_degree_right [DecidableRel G.Adj] (v w : V) :
    Fintype.card (G.commonNeighbors v w) ≤ G.degree w := by
  simp_rw [commonNeighbors_symm _ v w, card_commonNeighbors_le_degree_left]
/-
**SimpleGraph.card_commonNeighbors_lt_card_verts** 是 Mathlib 中的一个定理，位于命名空间 `Simp
leGraph`。
形式化陈述：card_commonNeighbors_lt_card_verts [DecidableRel G.Adj] (v w : V) : Fintyp
e.card (G.commonNeighbors v w) < Fintype.card V
参数：v w : V。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.lt_of_le_of_lt`：∀ {n m k : ℕ}, n ≤ m → m < k → n < k
· 使用定理 `SimpleGraph.card_commonNeighbors_le_degree_left`：card_commonNeighbors_le
_degree_left [DecidableRel G.Adj] (v w : V) : Fintype.card (G.commonNeighbors v 
w) <= G.degree v
· 使用定理 `SimpleGraph.degree_lt_card_verts`：degree_lt_card_verts [Fintype V] [Deci
dableRel G.Adj] (v : V) : G.degree v < Fintype.card V
-/
theorem card_commonNeighbors_lt_card_verts [DecidableRel G.Adj] (v w : V) :
    Fintype.card (G.commonNeighbors v w) < Fintype.card V :=
  Nat.lt_of_le_of_lt (G.card_commonNeighbors_le_degree_left _ _) (G.degree_lt_card_verts v)

/-- If the condition `G.Adj v w` fails, then `card_commonNeighbors_le_degree` is
the best we can do in general. -/
/-
**SimpleGraph.Adj.card_commonNeighbors_lt_degree** 是 Mathlib 中的一个定理，位于命名空间 `Simp
leGraph.Adj`。
形式化陈述：∀ {V : Type u_1} [inst : Fintype V] {G : SimpleGraph V} [inst_1 : Decidabl
eRel G.Adj] {v w : V},   G.Adj v w → Fintype.card ↑(G.commonNeighbors v w) < G.d
egree v
参数：G.commonNeighbors v w。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.toFinset_card`：toFinset_card {α : Type*} (s : Set α) [Fintype s] : s
.toFinset.card = Fintype.card s
· 使用定理 `Finset.card_lt_card`：∀ {α : Type u_1} {s t : Finset α}, s ⊂ t → s.card <
 t.card
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.ssubset_iff`：ssubset_iff : s ⊂ t ↔ exists a ∉ s, insert a s subse
teq t
· 使用定理 `Set.mem_toFinset`：mem_toFinset {s : Set α} [Fintype s] {a : α} : a in s.
toFinset ↔ a in s
· 使用定理 `SimpleGraph.notMem_commonNeighbors_right`：notMem_commonNeighbors_right (
v w : V) : w ∉ G.commonNeighbors v w
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `SimpleGraph.coe_neighborFinset`：coe_neighborFinset : (G.neighborFinset v
 : Set V) = G.neighborSet v
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `SimpleGraph.commonNeighbors_subset_neighborSet_left`：commonNeighbors_sub
set_neighborSet_left (v w : V) : G.commonNeighbors v w subseteq G.neighborSet v
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p

--- 原说明 ---
If the condition `G.Adj v w` fails, then `card_commonNeighbors_le_degree` is
the best we can do in general.
-/
theorem Adj.card_commonNeighbors_lt_degree {G : SimpleGraph V} [DecidableRel G.Adj] {v w : V}
    (h : G.Adj v w) : Fintype.card (G.commonNeighbors v w) < G.degree v := by
  classical
  rw [← Set.toFinset_card]
  refine Finset.card_lt_card <| Finset.ssubset_iff.mpr ⟨w, ?_, ?_⟩
  · rw [Set.mem_toFinset]
    apply notMem_commonNeighbors_right
  · simpa [Finset.insert_subset_iff, G.commonNeighbors_subset_neighborSet_left v w]
/-
**SimpleGraph.card_commonNeighbors_top** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：card_commonNeighbors_top [DecidableEq V] {v w : V} (h : v != w) : Fintype.
card (commonNeighbors ⊤ v w) = Fintype.card V - 2
参数：h : v != w。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fintype.card_congr'`：card_congr' {α β} [Fintype α] [Fintype β] (h : α = 
β) : card α = card β
· 使用定理 `SimpleGraph.commonNeighbors_top_eq`：commonNeighbors_top_eq {v w : V} : (
⊤ : SimpleGraph V).commonNeighbors v w = Set.univ \ {v, w}
· 使用定理 `Set.toFinset_sdiff`：toFinset_sdiff [Fintype (s \ t : Set _)] : (s \ t).t
oFinset = s.toFinset \ t.toFinset
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Set.toFinset_univ`：toFinset_univ [Fintype α] [Fintype (Set.univ : Set α)
] : (Set.univ : Set α).toFinset = Finset.univ
· 使用定理 `Set.toFinset_insert`：toFinset_insert [DecidableEq α] {a : α} {s : Set α}
 [Fintype (insert a s : Set α)] [Fintype s] : (insert a s).toFinset = insert a s
.toFinset
· 使用定理 `Set.toFinset_singleton`：toFinset_singleton (a : α) [Fintype ({a} : Set α
)] : ({a} : Set α).toFinset = {a}
· 使用定理 `Finset.card_sdiff`：card_sdiff : #(t \ s) = #t - #(s inter t)
· 使用定理 `Finset.inter_univ`：∀ {α : Type u_1} [inst : Fintype α] [inst_1 : Decidab
leEq α] (s : Finset α), s ∩ Finset.univ = s
· 使用定理 `Finset.card_insert_of_notMem`：card_insert_of_notMem (h : a ∉ s) : #(inse
rt a s) = #s + 1
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Finset.card_singleton`：card_singleton (a : α) : #{a} = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem card_commonNeighbors_top [DecidableEq V] {v w : V} (h : v ≠ w) :
    Fintype.card (commonNeighbors ⊤ v w) = Fintype.card V - 2 := by
  simp [commonNeighbors_top_eq, ← Set.toFinset_card, Finset.card_sdiff, h]
/-
**SimpleGraph.insert_neighborFinset_eq_univ** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGra
ph`。
形式化陈述：∀ {V : Type u_1} (G : SimpleGraph V) [inst : Fintype V] [inst_1 : Decidabl
eEq V] [inst_2 : DecidableRel G.Adj] (v : V),   insert v (G.neighborFinset v) = 
Finset.univ ↔ G.IsUniversal v
参数：G : SimpleGraph V；v : V；G.neighborFinset v。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
-/
@[simp] lemma insert_neighborFinset_eq_univ [DecidableEq V] [DecidableRel G.Adj] (v : V) :
    insert v (G.neighborFinset v) = univ ↔ G.IsUniversal v := by
  simp only [Finset.ext_iff, mem_insert, mem_neighborFinset, IsUniversal]
  grind
/-
**SimpleGraph.neighborFinset_eq_erase_univ** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGrap
h`。
形式化陈述：∀ {V : Type u_1} (G : SimpleGraph V) [inst : Fintype V] [inst_1 : Decidabl
eEq V] [inst_2 : DecidableRel G.Adj] (v : V),   G.neighborFinset v = Finset.univ
.erase v ↔ G.IsUniversal v
参数：G : SimpleGraph V；v : V。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma neighborFinset_eq_erase_univ [DecidableEq V] [DecidableRel G.Adj] (v : V) :
    G.neighborFinset v = univ.erase v ↔ G.IsUniversal v := by
  grind [insert_neighborFinset_eq_univ, notMem_neighborFinset_self]

@[simp]
/-
**SimpleGraph.degree_eq_card_sub_one** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
形式化陈述：degree_eq_card_sub_one [DecidableRel G.Adj] (v : V) : G.degree v = Fintype
.card V - 1 ↔ G.IsUniversal v
参数：v : V。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SimpleGraph.insert_neighborFinset_eq_univ`：∀ {V : Type u_1} (G : SimpleG
raph V) [inst : Fintype V] [inst_1 : DecidableEq V] [inst_2 : DecidableRel G.Adj
] (v : V),   insert v (G.neighb…
· 使用定理 `Finset.card_eq_iff_eq_univ`：Finset.card_eq_iff_eq_univ [Fintype α] (s : 
Finset α) : #s = Fintype.card α ↔ s = univ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.card_insert_of_notMem`：card_insert_of_notMem (h : a ∉ s) : #(inse
rt a s) = #s + 1
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Nat.sub_add_cancel`：∀ {n m : ℕ}, m ≤ n → n - m + m = n
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Fintype.card_pos_iff`：card_pos_iff : 0 < card α ↔ Nonempty α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `SimpleGraph.neighborFinset_eq_erase_univ`：∀ {V : Type u_1} (G : SimpleGr
aph V) [inst : Fintype V] [inst_1 : DecidableEq V] [inst_2 : DecidableRel G.Adj]
 (v : V),   G.neighborFinset v…
· 使用定理 `Finset.card_erase_of_mem`：card_erase_of_mem : a in s -> #(s.erase a) = #
s - 1
-/
lemma degree_eq_card_sub_one [DecidableRel G.Adj] (v : V) :
    G.degree v = Fintype.card V - 1 ↔ G.IsUniversal v := by
  classical
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rw [← G.insert_neighborFinset_eq_univ v, ← Finset.card_eq_iff_eq_univ]
    simp [h, Nat.sub_add_cancel <| Fintype.card_pos_iff.mpr ⟨v⟩]
  · simp [← card_neighborFinset_eq_degree, (G.neighborFinset_eq_erase_univ v).mpr h]
/-
**SimpleGraph.degree_lt_card_sub_one** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
形式化陈述：degree_lt_card_sub_one [DecidableRel G.Adj] (v : V) : G.degree v < Fintype
.card V - 1 ↔ ¬ G.IsUniversal v
参数：v : V。
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma degree_lt_card_sub_one [DecidableRel G.Adj] (v : V) :
    G.degree v < Fintype.card V - 1 ↔ ¬ G.IsUniversal v := by
  grind [degree_eq_card_sub_one, Nat.le_sub_one_of_lt <| G.degree_lt_card_verts v]

end Finite

namespace Iso

variable {G} {W : Type*} {G' : SimpleGraph W}

/-
**SimpleGraph.Iso.card_edgeFinset_eq** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Iso`
。
形式化陈述：card_edgeFinset_eq (f : G ≃g G') [Fintype G.edgeSet] [Fintype G'.edgeSet] 
: #G.edgeFinset = #G'.edgeFinset
参数：f : G ≃g G'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.card_eq_of_equiv`：Finset.card_eq_of_equiv {s : Finset α} {t : Fin
set β} (i : s ≃ t) : #s = #t
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem card_edgeFinset_eq (f : G ≃g G') [Fintype G.edgeSet] [Fintype G'.edgeSet] :
    #G.edgeFinset = #G'.edgeFinset := by
  apply Finset.card_eq_of_equiv
  simpa using f.mapEdgeSet
/-
**SimpleGraph.Iso.degree_eq** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Iso`。
形式化陈述：∀ {V : Type u_1} {G : SimpleGraph V} {W : Type u_2} {G' : SimpleGraph W} (
f : G ≃g G') (x : V)   [inst : Fintype ↑(G.neighborSet x)] [inst_1 : Fintype ↑(G
'.neighborSet (f x))], G'.degree (f x) = G.degree x
参数：f : G ≃g G'；x : V；G.neighborSet x；G'.neighborSet (f x)；f x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SimpleGraph.card_neighborSet_eq_degree`：card_neighborSet_eq_degree : Fin
type.card (G.neighborSet v) = G.degree v
· 使用定理 `Fintype.card_congr`：card_congr {α β} [Fintype α] [Fintype β] (f : α ≃ β)
 : card α = card β
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
@[simp] theorem degree_eq (f : G ≃g G') (x : V)
    [Fintype ↑(G.neighborSet x)] [Fintype ↑(G'.neighborSet (f x))] :
    G'.degree (f x) = G.degree x := by
  rw [← card_neighborSet_eq_degree, ← card_neighborSet_eq_degree,
    ← Fintype.card_congr (mapNeighborSet f x).symm]

variable [Fintype V] [DecidableRel G.Adj] [Fintype W] [DecidableRel G'.Adj]
/-
**SimpleGraph.Iso.minDegree_eq** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Iso`。
形式化陈述：minDegree_eq (f : G ≃g G') : G.minDegree = G'.minDegree
参数：f : G ≃g G'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `SimpleGraph.Iso.degree_eq`：∀ {V : Type u_1} {G : SimpleGraph V} {W : Typ
e u_2} {G' : SimpleGraph W} (f : G ≃g G') (x : V)   [inst : Fintype ↑(G.neighbor
Set x)] [inst_1…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.minDegree.eq_1`：∀ {V : Type u_1} (G : SimpleGraph V) [inst :
 Fintype V] [inst_1 : DecidableRel G.Adj],   G.minDegree = WithTop.untopD 0 (Fin
set.image (fun v…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.image_image`：image_image [DecidableEq γ] {g : β -> γ} : (s.image 
f).image g = s.image (g ∘ f)
· 使用定理 `Finset.image_univ_of_surjective`：image_univ_of_surjective [Fintype β] {f
 : β -> α} (hf : Surjective f) : univ.image f = univ
· 使用定理 `RelIso.surjective`：∀ {α : Type u_1} {β : Type u_2} {r : α → α → Prop} {s
 : β → β → Prop} (e : r ≃r s), Function.Surjective ⇑e
-/
theorem minDegree_eq (f : G ≃g G') : G.minDegree = G'.minDegree := by
  classical
  have : (G'.degree ·) ∘ f = (G.degree ·) := funext (f.degree_eq ·)
  rw [minDegree, minDegree, ← this, ← image_image, Finset.image_univ_of_surjective f.surjective]
/-
**SimpleGraph.Iso.maxDegree_eq** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Iso`。
形式化陈述：maxDegree_eq (f : G ≃g G') : G.maxDegree = G'.maxDegree
参数：f : G ≃g G'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `SimpleGraph.Iso.degree_eq`：∀ {V : Type u_1} {G : SimpleGraph V} {W : Typ
e u_2} {G' : SimpleGraph W} (f : G ≃g G') (x : V)   [inst : Fintype ↑(G.neighbor
Set x)] [inst_1…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.maxDegree.eq_1`：∀ {V : Type u_1} (G : SimpleGraph V) [inst :
 Fintype V] [inst_1 : DecidableRel G.Adj],   G.maxDegree = WithBot.unbotD 0 (Fin
set.image (fun v…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.image_image`：image_image [DecidableEq γ] {g : β -> γ} : (s.image 
f).image g = s.image (g ∘ f)
· 使用定理 `Finset.image_univ_of_surjective`：image_univ_of_surjective [Fintype β] {f
 : β -> α} (hf : Surjective f) : univ.image f = univ
· 使用定理 `RelIso.surjective`：∀ {α : Type u_1} {β : Type u_2} {r : α → α → Prop} {s
 : β → β → Prop} (e : r ≃r s), Function.Surjective ⇑e
-/
theorem maxDegree_eq (f : G ≃g G') : G.maxDegree = G'.maxDegree := by
  classical
  have : (G'.degree ·) ∘ f = (G.degree ·) := funext (f.degree_eq ·)
  rw [maxDegree, maxDegree, ← this, ← image_image, Finset.image_univ_of_surjective f.surjective]

end Iso

section Support

variable {s : Set V} [DecidablePred (· ∈ s)] [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-
**SimpleGraph.edgeFinset_subset_sym2_of_support_subset** 是 Mathlib 中的一个引理，位于命名空间
 `SimpleGraph`。
形式化陈述：edgeFinset_subset_sym2_of_support_subset (h : G.support subseteq s) : G.ed
geFinset subseteq s.toFinset.sym2
参数：h : G.support subseteq s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.coe_subset`：coe_subset {s₁ s₂ : Finset α} : (s₁ : Set α) subseteq
 s₂ ↔ s₁ subseteq s₂
· 使用定理 `Finset.coe_sym2`：∀ {α : Type u_1} {m : Finset α}, ↑m.sym2 = (↑m).sym2
· 使用定理 `SimpleGraph.edgeFinset.eq_1`：∀ {V : Type u_1} (G : SimpleGraph V) [inst 
: Fintype ↑G.edgeSet], G.edgeFinset = G.edgeSet.toFinset
· 使用定理 `Set.coe_toFinset`：coe_toFinset (s : Set α) [Fintype s] : (↑s.toFinset : 
Set α) = s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `SimpleGraph.edgeSet_subset_sym2_iff`：edgeSet_subset_sym2_iff {s : Set V}
 : G.edgeSet subseteq s.sym2 ↔ G.support subseteq s
-/
lemma edgeFinset_subset_sym2_of_support_subset (h : G.support ⊆ s) :
    G.edgeFinset ⊆ s.toFinset.sym2 := by
  rw [← coe_subset, coe_sym2, edgeFinset, Set.coe_toFinset, Set.coe_toFinset]
  exact edgeSet_subset_sym2_iff.mpr h
/-
**SimpleGraph.** 是 Mathlib 中的一个实例，位于命名空间 `SimpleGraph`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : DecidablePred (· ∈ G.support) :=
  inferInstanceAs <| DecidablePred (· ∈ { v | ∃ w, G.Adj v w })
/-
**SimpleGraph.map_edgeFinset_induce** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：map_edgeFinset_induce [DecidableEq V] : (G.induce s).edgeFinset.map (Embed
ding.subtype (· in s)).sym2Map = G.edgeFinset inter s.toFinset.sym2
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Function.Embedding.sym2Map_apply`：∀ {α : Type u_1} {β : Type u_2} (f : α
 ↪ β) (a : Sym2 α), f.sym2Map a = Sym2.map (⇑f) a
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `Prod.mk.injEq`：∀ {α : Type u} {β : Type v} (fst : α) (snd : β) (fst_1 : 
α) (snd_1 : β),   ((fst, snd) = (fst_1, snd_1)) = (fst = fst_1 ∧ snd = snd_1)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
-/
theorem map_edgeFinset_induce [DecidableEq V] :
    (G.induce s).edgeFinset.map (Embedding.subtype (· ∈ s)).sym2Map
      = G.edgeFinset ∩ s.toFinset.sym2 := by
  aesop (add simp [Finset.ext_iff, Sym2.exists, Sym2.forall, adj_comm])
/-
**SimpleGraph.map_edgeFinset_induce_of_support_subset** 是 Mathlib 中的一个定理，位于命名空间 
`SimpleGraph`。
形式化陈述：map_edgeFinset_induce_of_support_subset (h : G.support subseteq s) : (G.in
duce s).edgeFinset.map (Embedding.subtype (· in s)).sym2Map = G.edgeFinset
参数：h : G.support subseteq s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.map_edgeFinset_induce`：map_edgeFinset_induce [DecidableEq V]
 : (G.induce s).edgeFinset.map (Embedding.subtype (· in s)).sym2Map = G.edgeFins
et inter s.toFinset.sym…
· 使用引理 `SimpleGraph.edgeFinset_subset_sym2_of_support_subset`：edgeFinset_subset_
sym2_of_support_subset (h : G.support subseteq s) : G.edgeFinset subseteq s.toFi
nset.sym2
-/
theorem map_edgeFinset_induce_of_support_subset (h : G.support ⊆ s) :
    (G.induce s).edgeFinset.map (Embedding.subtype (· ∈ s)).sym2Map = G.edgeFinset := by
  classical
  simpa [map_edgeFinset_induce] using edgeFinset_subset_sym2_of_support_subset h

/-- If the support of the simple graph `G` is a subset of the set `s`, then the induced subgraph of
`s` has the same number of edges as `G`. -/
/-
**SimpleGraph.card_edgeFinset_induce_of_support_subset** 是 Mathlib 中的一个定理，位于命名空间
 `SimpleGraph`。
形式化陈述：card_edgeFinset_induce_of_support_subset (h : G.support subseteq s) : #(G.
induce s).edgeFinset = #G.edgeFinset
参数：h : G.support subseteq s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SimpleGraph.map_edgeFinset_induce_of_support_subset`：map_edgeFinset_indu
ce_of_support_subset (h : G.support subseteq s) : (G.induce s).edgeFinset.map (E
mbedding.subtype (· in s)).sym2Map = G.ed…
· 使用定理 `Finset.card_map`：card_map (f : α ↪ β) : #(s.map f) = #s

--- 原说明 ---
If the support of the simple graph `G` is a subset of the set `s`, then the indu
ced subgraph of
`s` has the same number of edges as `G`.
-/
theorem card_edgeFinset_induce_of_support_subset (h : G.support ⊆ s) :
    #(G.induce s).edgeFinset = #G.edgeFinset := by
  rw [← map_edgeFinset_induce_of_support_subset h, card_map]
/-
**SimpleGraph.card_edgeFinset_induce_support** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGr
aph`。
形式化陈述：card_edgeFinset_induce_support : #(G.induce G.support).edgeFinset = #G.edg
eFinset
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.card_edgeFinset_induce_of_support_subset`：card_edgeFinset_in
duce_of_support_subset (h : G.support subseteq s) : #(G.induce s).edgeFinset = #
G.edgeFinset
· 使用定理 `subset_rfl`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preorde
r α] {a : α}, a ⊆ a
-/
theorem card_edgeFinset_induce_support :
    #(G.induce G.support).edgeFinset = #G.edgeFinset :=
  card_edgeFinset_induce_of_support_subset subset_rfl
/-
**SimpleGraph.map_neighborFinset_induce** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：map_neighborFinset_induce [DecidableEq V] (v : s) : ((G.induce s).neighbor
Finset v).map (.subtype (· in s)) = G.neighborFinset v inter s.toFinset
参数：v : s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem map_neighborFinset_induce [DecidableEq V] (v : s) :
    ((G.induce s).neighborFinset v).map (.subtype (· ∈ s)) = G.neighborFinset v ∩ s.toFinset := by
  ext; simp
/-
**SimpleGraph.map_neighborFinset_induce_of_neighborSet_subset** 是 Mathlib 中的一个定理
，位于命名空间 `SimpleGraph`。
形式化陈述：map_neighborFinset_induce_of_neighborSet_subset {v : s} (h : G.neighborSet
 v subseteq s) : ((G.induce s).neighborFinset v).map (.subtype (· in s)) = G.nei
ghborFinset v
参数：h : G.neighborSet v subseteq s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SimpleGraph.map_neighborFinset_induce`：map_neighborFinset_induce [Decida
bleEq V] (v : s) : ((G.induce s).neighborFinset v).map (.subtype (· in s)) = G.n
eighborFinset v inter s.toF…
· 使用定理 `Finset.inter_eq_left`：∀ {α : Type u_1} [inst : DecidableEq α] {s t : Fin
set α}, s ∩ t = s ↔ s ⊆ t
· 使用定理 `SimpleGraph.neighborFinset_def`：neighborFinset_def : G.neighborFinset v 
= (G.neighborSet v).toFinset
· 使用定理 `Set.toFinset_subset_toFinset`：toFinset_subset_toFinset [Fintype s] [Fint
ype t] : s.toFinset subseteq t.toFinset ↔ s subseteq t
-/
theorem map_neighborFinset_induce_of_neighborSet_subset {v : s} (h : G.neighborSet v ⊆ s) :
    ((G.induce s).neighborFinset v).map (.subtype (· ∈ s)) = G.neighborFinset v := by
  classical
  rwa [← Set.toFinset_subset_toFinset, ← neighborFinset_def, ← inter_eq_left,
    ← map_neighborFinset_induce v] at h

/-- If the neighbor set of a vertex `v` is a subset of `s`, then the degree of the vertex in the
induced subgraph of `s` is the same as in `G`. -/
/-
**SimpleGraph.degree_induce_of_neighborSet_subset** 是 Mathlib 中的一个定理，位于命名空间 `Sim
pleGraph`。
形式化陈述：degree_induce_of_neighborSet_subset {v : s} (h : G.neighborSet v subseteq 
s) : (G.induce s).degree v = G.degree v
参数：h : G.neighborSet v subseteq s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SimpleGraph.map_neighborFinset_induce_of_neighborSet_subset`：map_neighbo
rFinset_induce_of_neighborSet_subset {v : s} (h : G.neighborSet v subseteq s) : 
((G.induce s).neighborFinset v).map (.subtype (· …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.card_map`：card_map (f : α ↪ β) : #(s.map f) = #s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
If the neighbor set of a vertex `v` is a subset of `s`, then the degree of the v
ertex in the
induced subgraph of `s` is the same as in `G`.
-/
theorem degree_induce_of_neighborSet_subset {v : s} (h : G.neighborSet v ⊆ s) :
    (G.induce s).degree v = G.degree v := by
  simp_rw [← card_neighborFinset_eq_degree,
    ← map_neighborFinset_induce_of_neighborSet_subset h, card_map]

/-- If the support of the simple graph `G` is a subset of the set `s`, then the degree of vertices
in the induced subgraph of `s` are the same as in `G`. -/
/-
**SimpleGraph.degree_induce_of_support_subset** 是 Mathlib 中的一个定理，位于命名空间 `SimpleG
raph`。
形式化陈述：degree_induce_of_support_subset (h : G.support subseteq s) (v : s) : (G.in
duce s).degree v = G.degree v
参数：h : G.support subseteq s；v : s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.degree_induce_of_neighborSet_subset`：degree_induce_of_neighb
orSet_subset {v : s} (h : G.neighborSet v subseteq s) : (G.induce s).degree v = 
G.degree v
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `SimpleGraph.neighborSet_subset_support`：neighborSet_subset_support (v : 
V) : G.neighborSet v subseteq G.support

--- 原说明 ---
If the support of the simple graph `G` is a subset of the set `s`, then the degr
ee of vertices
in the induced subgraph of `s` are the same as in `G`.
-/
theorem degree_induce_of_support_subset (h : G.support ⊆ s) (v : s) :
    (G.induce s).degree v = G.degree v :=
  degree_induce_of_neighborSet_subset <| (G.neighborSet_subset_support v).trans h

@[simp]
/-
**SimpleGraph.degree_induce_support** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：degree_induce_support (v : G.support) : (G.induce G.support).degree v = G.
degree v
参数：v : G.support。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.degree_induce_of_support_subset`：degree_induce_of_support_su
bset (h : G.support subseteq s) (v : s) : (G.induce s).degree v = G.degree v
· 使用定理 `subset_rfl`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preorde
r α] {a : α}, a ⊆ a
-/
theorem degree_induce_support (v : G.support) :
    (G.induce G.support).degree v = G.degree v :=
  degree_induce_of_support_subset subset_rfl v
/-
**SimpleGraph.le_minDegree_induce_of_support_subset** 是 Mathlib 中的一个定理，位于命名空间 `S
impleGraph`。
形式化陈述：le_minDegree_induce_of_support_subset (h : G.support subseteq s) : G.minDe
gree <= (G.induce s).minDegree
参数：h : G.support subseteq s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `SimpleGraph.minDegree_of_subsingleton`：minDegree_of_subsingleton [Decida
bleRel G.Adj] [Subsingleton V] : G.minDegree = 0
· 使用定理 `IsEmpty.instSubsingleton`：∀ {α : Sort u} [IsEmpty α], Subsingleton α
· 使用定理 `Set.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Set α) : s = ∅ ∨ s.N
onempty
· 使用定理 `Set.instIsEmptyElemEmptyCollection`：∀ (α : Type u), IsEmpty ↑∅
· 使用定理 `Nat.le_zero_eq`：∀ (a : ℕ), (a ≤ 0) = (a = 0)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.subset_empty_iff`：subset_empty_iff {s : Set α} : s subseteq ∅ ↔ s = 
∅
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.Nonempty.to_subtype`：∀ {α : Type u} {s : Set α}, s.Nonempty → Nonemp
ty ↑s
· 使用定理 `SimpleGraph.le_minDegree_of_forall_le_degree`：le_minDegree_of_forall_le_
degree [DecidableRel G.Adj] [Nonempty V] (k : Nat) (h : forall v, k <= G.degree 
v) : k <= G.minDegree
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `SimpleGraph.minDegree_le_degree`：minDegree_le_degree [DecidableRel G.Adj
] (v : V) : G.minDegree <= G.degree v
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `SimpleGraph.degree_induce_of_neighborSet_subset`：degree_induce_of_neighb
orSet_subset {v : s} (h : G.neighborSet v subseteq s) : (G.induce s).degree v = 
G.degree v
· 使用引理 `SimpleGraph.neighborSet_subset_support`：neighborSet_subset_support (v : 
V) : G.neighborSet v subseteq G.support
-/
theorem le_minDegree_induce_of_support_subset (h : G.support ⊆ s) :
    G.minDegree ≤ (G.induce s).minDegree := by
  cases isEmpty_or_nonempty V
  · simp
  rcases s.eq_empty_or_nonempty with (rfl | hs)
  · simp [minDegree_eq_zero_iff_support_ne, Set.subset_empty_iff.mp h, Set.empty_ne_univ]
  have := hs.to_subtype
  refine le_minDegree_of_forall_le_degree _ _ fun v ↦ ?_
  grw [G.minDegree_le_degree v, degree_induce_of_neighborSet_subset]
  grw [neighborSet_subset_support, h]
/-
**SimpleGraph.filter_edgeFinset_toFinset_subset** 是 Mathlib 中的一个定理，位于命名空间 `Simpl
eGraph`。
形式化陈述：filter_edgeFinset_toFinset_subset [DecidableEq V] (s : Finset V) : {e in G
.edgeFinset | e.toFinset subseteq s} = G.edgeFinset inter s.sym2
参数：s : Finset V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.filter_congr`：∀ {α : Type u_1} {p q : α → Prop} [inst : Decidable
Pred p] [inst_1 : DecidablePred q] {s : Finset α},   (∀ x ∈ s, p x ↔ q x) → Fins
et.filter…
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Finset.filter_mem_eq_inter`：filter_mem_eq_inter {s t : Finset α} [forall
 i, Decidable (i in t)] : (s.filter fun i => i in t) = s inter t
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem filter_edgeFinset_toFinset_subset [DecidableEq V] (s : Finset V) :
    {e ∈ G.edgeFinset | e.toFinset ⊆ s} = G.edgeFinset ∩ s.sym2 := by
  simp [subset_iff, ← mem_sym2_iff, filter_mem_eq_inter]

/-- The edges whose vertices lie in `s` are in bijection with the edges of the induced
subgraph `G.induce s`. -/
/-
**SimpleGraph.card_filter_edgeFinset_toFinset_subset** 是 Mathlib 中的一个定理，位于命名空间 `
SimpleGraph`。
形式化陈述：card_filter_edgeFinset_toFinset_subset [DecidableEq V] (s : Finset V) : #{
e in G.edgeFinset | e.toFinset subseteq s} = #(G.induce ↑s).edgeFinset
参数：s : Finset V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.map_edgeFinset_induce`：map_edgeFinset_induce [DecidableEq V]
 : (G.induce s).edgeFinset.map (Embedding.subtype (· in s)).sym2Map = G.edgeFins
et inter s.toFinset.sym…
· 使用定理 `SimpleGraph.filter_edgeFinset_toFinset_subset`：filter_edgeFinset_toFinse
t_subset [DecidableEq V] (s : Finset V) : {e in G.edgeFinset | e.toFinset subset
eq s} = G.edgeFinset inter s.sym2
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Lean.Meta.FastSubsingleton.elim`：∀ {α : Sort u} [h : Meta.FastSubsinglet
on α] (a b : α), a = b
· 使用定理 `Fintype.instFastSubsingleton`：∀ (α : Type u_4), Meta.FastSubsingleton (F
intype α)
· 使用定理 `Finset.toFinset_coe`：Finset.toFinset_coe (s : Finset α) [Fintype (s : Se
t α)] : (s : Set α).toFinset = s
· 使用定理 `Finset.card_map`：card_map (f : α ↪ β) : #(s.map f) = #s

--- 原说明 ---
The edges whose vertices lie in `s` are in bijection with the edges of the induc
ed
subgraph `G.induce s`.
-/
theorem card_filter_edgeFinset_toFinset_subset [DecidableEq V] (s : Finset V) :
    #{e ∈ G.edgeFinset | e.toFinset ⊆ s} = #(G.induce ↑s).edgeFinset := by
  have h := congrArg Finset.card (map_edgeFinset_induce (s := (↑s : Set V)) (G := G))
  rw [card_map, toFinset_coe] at h
  rw [filter_edgeFinset_toFinset_subset]
  convert h.symm using 1
  congr!

end Support

section Map

variable [Fintype V] {W : Type*} [Fintype W] [DecidableEq W]

@[simp]
/-
**SimpleGraph.edgeFinset_map** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：edgeFinset_map (f : V ↪ W) (G : SimpleGraph V) [DecidableRel G.Adj] : (G.m
ap f).edgeFinset = G.edgeFinset.map f.sym2Map
参数：f : V ↪ W；G : SimpleGraph V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.coe_inj`：coe_inj {s₁ s₂ : Finset α} : (s₁ : Set α) = s₂ ↔ s₁ = s₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `SimpleGraph.coe_edgeFinset`：coe_edgeFinset : (G.edgeFinset : Set (Sym2 V
)) = G.edgeSet
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.coe_map`：coe_map (f : α ↪ β) (s : Finset α) : (s.map f : Set β) =
 f '' s
· 使用定理 `SimpleGraph.edgeSet_map`：edgeSet_map (f : V ↪ W) (G : SimpleGraph V) : (
G.map f).edgeSet = f.sym2Map '' G.edgeSet
-/
theorem edgeFinset_map (f : V ↪ W) (G : SimpleGraph V) [DecidableRel G.Adj] :
    (G.map f).edgeFinset = G.edgeFinset.map f.sym2Map := by
  rw [← Finset.coe_inj]
  push_cast
  exact G.edgeSet_map f
/-
**SimpleGraph.card_edgeFinset_map** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：card_edgeFinset_map (f : V ↪ W) (G : SimpleGraph V) [DecidableRel G.Adj] :
 #(G.map f).edgeFinset = #G.edgeFinset
参数：f : V ↪ W；G : SimpleGraph V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.edgeFinset_map`：edgeFinset_map (f : V ↪ W) (G : SimpleGraph 
V) [DecidableRel G.Adj] : (G.map f).edgeFinset = G.edgeFinset.map f.sym2Map
· 使用定理 `Finset.card_map`：card_map (f : α ↪ β) : #(s.map f) = #s
-/
theorem card_edgeFinset_map (f : V ↪ W) (G : SimpleGraph V) [DecidableRel G.Adj] :
    #(G.map f).edgeFinset = #G.edgeFinset := by
  rw [edgeFinset_map]
  exact G.edgeFinset.card_map f.sym2Map

end Map

end SimpleGraph

