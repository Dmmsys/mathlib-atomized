/-
Copyright (c) 2020 Aaron Anderson, Jalex Stark, Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson, Jalex Stark, Kyle Miller, Alena Gusakov, Hunter Monroe
-/
module

public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.Data.Int.Cast.Basic

/-!
# Edge deletion

This file defines operations deleting the edges of a simple graph and proves theorems in the finite
case.

## Main definitions

* `SimpleGraph.deleteEdges G s` is the simple graph `G` with the edges `s : Set (Sym2 V)` removed
  from the edge set.

* `SimpleGraph.deleteIncidenceSet G v` is the simple graph `G` with the incidence set of `v`
  removed from the edge set.

* `SimpleGraph.DeleteFar G p r` is the predicate that a graph is `r`-*delete-far* from a property
  `p`, that is, at least `r` edges must be deleted to satisfy `p`.
-/

@[expose] public section


open Finset Fintype

namespace SimpleGraph

variable {V : Type*} {v w : V} (G : SimpleGraph V)

section DeleteEdges

/-- Given a set of vertex pairs, remove all of the corresponding edges from the
graph's edge set, if present.

See also: `SimpleGraph.Subgraph.deleteEdges`. -/
/-
**SimpleGraph.deleteEdges** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph`。
形式化陈述：deleteEdges (s : Set (Sym2 V)) : SimpleGraph V
参数：s : Set (Sym2 V)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a set of vertex pairs, remove all of the corresponding edges from the
graph's edge set, if present.

See also: `SimpleGraph.Subgraph.deleteEdges`.
-/
def deleteEdges (s : Set (Sym2 V)) : SimpleGraph V := G \ fromEdgeSet s

variable {G} {H : SimpleGraph V} {s s₁ s₂ : Set (Sym2 V)}
/-
**SimpleGraph.** 是 Mathlib 中的一个实例，位于命名空间 `SimpleGraph`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [DecidableRel G.Adj] [DecidablePred (· ∈ s)] [DecidableEq V] :
    DecidableRel (G.deleteEdges s).Adj :=
  inferInstanceAs <| DecidableRel (G \ fromEdgeSet s).Adj
/-
**SimpleGraph.deleteEdges_adj** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：∀ {V : Type u_1} {v w : V} {G : SimpleGraph V} {s : Set (Sym2 V)}, (G.dele
teEdges s).Adj v w ↔ G.Adj v w ∧ s(v, w) ∉ s
参数：Sym2 V；G.deleteEdges s；v, w。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `and_congr_right`：∀ {a b c : Prop}, (a → (b ↔ c)) → (a ∧ b ↔ a ∧ c)
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `and_iff_left`：∀ {b a : Prop}, b → (a ∧ b ↔ a)
· 使用定理 `SimpleGraph.Adj.ne`：∀ {V : Type u} {G : SimpleGraph V} {a b : V}, G.Adj 
a b → a ≠ b
-/
@[simp] lemma deleteEdges_adj : (G.deleteEdges s).Adj v w ↔ G.Adj v w ∧ s(v, w) ∉ s :=
  and_congr_right fun h ↦ (and_iff_left h.ne).not
/-
**SimpleGraph.deleteEdges_edgeSet** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：∀ {V : Type u_1} (G G' : SimpleGraph V), G.deleteEdges G'.edgeSet = G \ G'
参数：G G' : SimpleGraph V。
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
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma deleteEdges_edgeSet (G G' : SimpleGraph V) : G.deleteEdges G'.edgeSet = G \ G' := by
  ext; simp

@[simp]
/-
**SimpleGraph.deleteEdges_deleteEdges** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：deleteEdges_deleteEdges (s s' : Set (Sym2 V)) : (G.deleteEdges s).deleteEd
ges s' = G.deleteEdges (s union s')
参数：s s' : Set (Sym2 V)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sdiff_sdiff`：sdiff_sdiff (a b c : α) : (a \ b) \ c = a \ (b ⊔ c)
· 使用定理 `SimpleGraph.fromEdgeSet_union`：fromEdgeSet_union (s t : Set (Sym2 V)) : 
fromEdgeSet (s union t) = fromEdgeSet s ⊔ fromEdgeSet t
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem deleteEdges_deleteEdges (s s' : Set (Sym2 V)) :
    (G.deleteEdges s).deleteEdges s' = G.deleteEdges (s ∪ s') := by simp [deleteEdges, sdiff_sdiff]

-- This is not marked `simp` since `deleteEdges_of_subset_diagSet` already proves it
/-
**SimpleGraph.deleteEdges_empty** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
形式化陈述：deleteEdges_empty : G.deleteEdges ∅ = G
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.fromEdgeSet_empty`：fromEdgeSet_empty : fromEdgeSet (∅ : Set 
(Sym2 V)) = ⊥
· 使用定理 `sdiff_bot`：∀ {α : Type u_2} [inst : GeneralizedCoheytingAlgebra α] {a : 
α}, a \ ⊥ = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma deleteEdges_empty : G.deleteEdges ∅ = G := by simp [deleteEdges]
/-
**SimpleGraph.deleteEdges_univ** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：∀ {V : Type u_1} {G : SimpleGraph V}, G.deleteEdges Set.univ = ⊥
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.fromEdgeSet_univ`：fromEdgeSet_univ : fromEdgeSet (Set.univ :
 Set (Sym2 V)) = ⊤
· 使用定理 `sdiff_top`：∀ {α : Type u_2} [inst : CoheytingAlgebra α] (a : α), a \ ⊤ =
 ⊥
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma deleteEdges_univ : G.deleteEdges Set.univ = ⊥ := by simp [deleteEdges]

@[simp]
/-
**SimpleGraph.deleteEdges_le_iff** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：deleteEdges_le_iff (s : Set (Sym2 V)) (G' : SimpleGraph V) : G.deleteEdges
 s <= G' ↔ G <= fromEdgeSet s ⊔ G'
参数：s : Set (Sym2 V)；G' : SimpleGraph V。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.deleteEdges.eq_1`：∀ {V : Type u_1} (G : SimpleGraph V) (s : 
Set (Sym2 V)), G.deleteEdges s = G \ SimpleGraph.fromEdgeSet s
· 使用定理 `sdiff_le_iff`：sdiff_le_iff [GeneralizedCoheytingAlgebra α] {a b c : α} :
 a \ b <= c ↔ a <= b ⊔ c
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem deleteEdges_le_iff (s : Set (Sym2 V)) (G' : SimpleGraph V) :
    G.deleteEdges s ≤ G' ↔ G ≤ fromEdgeSet s ⊔ G' := by
    rw [deleteEdges, sdiff_le_iff]
/-
**SimpleGraph.deleteEdges_le** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
形式化陈述：deleteEdges_le (s : Set (Sym2 V)) : G.deleteEdges s <= G
参数：s : Set (Sym2 V)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sdiff_le`：∀ {α : Type u_2} [inst : GeneralizedCoheytingAlgebra α] {a b :
 α}, a \ b ≤ a
-/
lemma deleteEdges_le (s : Set (Sym2 V)) : G.deleteEdges s ≤ G := sdiff_le
/-
**SimpleGraph.deleteEdges_anti** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：∀ {V : Type u_1} {G : SimpleGraph V} {s₁ s₂ : Set (Sym2 V)}, s₁ ⊆ s₂ → G.d
eleteEdges s₂ ≤ G.deleteEdges s₁
参数：Sym2 V。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sdiff_le_sdiff_left`：∀ {α : Type u_2} [inst : GeneralizedCoheytingAlgebr
a α] {a b c : α}, b ≤ a → c \ a ≤ c \ b
· 使用定理 `SimpleGraph.fromEdgeSet_mono`：fromEdgeSet_mono {s t : Set (Sym2 V)} (h :
 s subseteq t) : fromEdgeSet s <= fromEdgeSet t
-/
@[gcongr] lemma deleteEdges_anti (h : s₁ ⊆ s₂) : G.deleteEdges s₂ ≤ G.deleteEdges s₁ :=
  sdiff_le_sdiff_left <| fromEdgeSet_mono h

@[gcongr]
/-
**SimpleGraph.deleteEdges_mono** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
形式化陈述：deleteEdges_mono (h : G <= H) : G.deleteEdges s <= H.deleteEdges s
参数：h : G <= H。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sdiff_le_sdiff_right`：∀ {α : Type u_2} [inst : GeneralizedCoheytingAlgeb
ra α] {a b c : α}, b ≤ a → b \ c ≤ a \ c
-/
lemma deleteEdges_mono (h : G ≤ H) : G.deleteEdges s ≤ H.deleteEdges s := sdiff_le_sdiff_right h
/-
**SimpleGraph.deleteEdges_eq_self** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：∀ {V : Type u_1} {G : SimpleGraph V} {s : Set (Sym2 V)}, G.deleteEdges s =
 G ↔ Disjoint G.edgeSet s
参数：Sym2 V。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.deleteEdges.eq_1`：∀ {V : Type u_1} (G : SimpleGraph V) (s : 
Set (Sym2 V)), G.deleteEdges s = G \ SimpleGraph.fromEdgeSet s
· 使用定理 `sdiff_eq_left`：∀ {α : Type u} {x y : α} [inst : GeneralizedBooleanAlgebr
a α], x \ y = x ↔ Disjoint x y
· 使用定理 `SimpleGraph.disjoint_fromEdgeSet`：∀ {V : Type u} (G : SimpleGraph V) (s 
: Set (Sym2 V)), Disjoint G (SimpleGraph.fromEdgeSet s) ↔ Disjoint G.edgeSet s
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma deleteEdges_eq_self : G.deleteEdges s = G ↔ Disjoint G.edgeSet s := by
  rw [deleteEdges, sdiff_eq_left, disjoint_fromEdgeSet]
/-
**SimpleGraph.deleteEdges_eq_inter_edgeSet** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGrap
h`。
形式化陈述：deleteEdges_eq_inter_edgeSet (s : Set (Sym2 V)) : G.deleteEdges s = G.dele
teEdges (s inter G.edgeSet)
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
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem deleteEdges_eq_inter_edgeSet (s : Set (Sym2 V)) :
    G.deleteEdges s = G.deleteEdges (s ∩ G.edgeSet) := by
  ext
  simp +contextual [imp_false]
/-
**SimpleGraph.deleteEdges_of_subset_diagSet** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGra
ph`。
形式化陈述：∀ {V : Type u_1} {s : Set (Sym2 V)} (G : SimpleGraph V), s ⊆ Sym2.diagSet 
→ G.deleteEdges s = G
参数：Sym2 V；G : SimpleGraph V。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.ext`：∀ {V : Type u} {x y : SimpleGraph V}, x.Adj = y.Adj → x
 = y
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.Adj.ne`：∀ {V : Type u} {G : SimpleGraph V} {a b : V}, G.Adj 
a b → a ≠ b
-/
@[simp] lemma deleteEdges_of_subset_diagSet (G : SimpleGraph V) (hs : s ⊆ Sym2.diagSet) :
    G.deleteEdges s = G := by ext u v; simpa using (·.ne <| hs ·)
/-
**SimpleGraph.deleteEdges_sdiff_eq_of_le** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`
。
形式化陈述：deleteEdges_sdiff_eq_of_le {H : SimpleGraph V} (h : H <= G) : G.deleteEdge
s (G.edgeSet \ H.edgeSet) = H
参数：h : H <= G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SimpleGraph.edgeSet_sdiff`：edgeSet_sdiff : (G₁ \ G₂).edgeSet = G₁.edgeSe
t \ G₂.edgeSet
· 使用定理 `SimpleGraph.deleteEdges_edgeSet`：∀ {V : Type u_1} (G G' : SimpleGraph V)
, G.deleteEdges G'.edgeSet = G \ G'
· 使用定理 `sdiff_sdiff_eq_self`：sdiff_sdiff_eq_self (h : y <= x) : x \ (x \ y) = y
-/
theorem deleteEdges_sdiff_eq_of_le {H : SimpleGraph V} (h : H ≤ G) :
    G.deleteEdges (G.edgeSet \ H.edgeSet) = H := by
  rw [← edgeSet_sdiff, deleteEdges_edgeSet, sdiff_sdiff_eq_self h]

@[simp]
/-
**SimpleGraph.edgeSet_deleteEdges** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：edgeSet_deleteEdges (s : Set (Sym2 V)) : (G.deleteEdges s).edgeSet = G.edg
eSet \ s
参数：s : Set (Sym2 V)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.edgeSet_sdiff`：edgeSet_sdiff : (G₁ \ G₂).edgeSet = G₁.edgeSe
t \ G₂.edgeSet
· 使用定理 `SimpleGraph.edgeSet_fromEdgeSet`：edgeSet_fromEdgeSet : (fromEdgeSet s).e
dgeSet = s \ Sym2.diagSet
· 使用定理 `SimpleGraph.edgeSet_sdiff_sdiff_isDiag`：edgeSet_sdiff_sdiff_isDiag (G : 
SimpleGraph V) (s : Set (Sym2 V)) : G.edgeSet \ (s \ Sym2.diagSet) = G.edgeSet \
 s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem edgeSet_deleteEdges (s : Set (Sym2 V)) : (G.deleteEdges s).edgeSet = G.edgeSet \ s := by
  simp [deleteEdges]
/-
**SimpleGraph.edgeFinset_deleteEdges** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：∀ {V : Type u_1} {G : SimpleGraph V} [inst : DecidableEq V] [inst_1 : Fint
ype ↑G.edgeSet] (s : Finset (Sym2 V))   [inst_2 : Fintype ↑(G.deleteEdges ↑s).ed
geSet], (G.deleteEdges ↑s).edgeFinset = G.edgeFinset \ s
参数：s : Finset (Sym2 V)；G.deleteEdges ↑s；G.deleteEdges ↑s。
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
· 使用定理 `SimpleGraph.edgeSet_deleteEdges`：edgeSet_deleteEdges (s : Set (Sym2 V)) 
: (G.deleteEdges s).edgeSet = G.edgeSet \ s
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] theorem edgeFinset_deleteEdges [DecidableEq V] [Fintype G.edgeSet] (s : Finset (Sym2 V))
    [Fintype (G.deleteEdges s).edgeSet] :
    (G.deleteEdges s).edgeFinset = G.edgeFinset \ s := by
  ext e
  simp [edgeSet_deleteEdges]
/-
**SimpleGraph.deleteEdges_sup** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：∀ {V : Type u_1} (G H : SimpleGraph V) (s : Set (Sym2 V)), (G ⊔ H).deleteE
dges s = G.deleteEdges s ⊔ H.deleteEdges s
参数：G H : SimpleGraph V；s : Set (Sym2 V)；G ⊔ H。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sup_sdiff`：sup_sdiff : (a ⊔ b) \ c = a \ c ⊔ b \ c
-/
@[simp] lemma deleteEdges_sup (G H : SimpleGraph V) (s : Set (Sym2 V)) :
    (G ⊔ H).deleteEdges s = G.deleteEdges s ⊔ H.deleteEdges s := sup_sdiff
/-
**SimpleGraph.deleteEdges_fromEdgeSet** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：∀ {V : Type u_1} (s t : Set (Sym2 V)), (SimpleGraph.fromEdgeSet s).deleteE
dges t = SimpleGraph.fromEdgeSet (s \ t)
参数：s t : Set (Sym2 V)；SimpleGraph.fromEdgeSet s；s \ t。
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
· 使用定理 `SimpleGraph.fromEdgeSet_sdiff`：fromEdgeSet_sdiff (s t : Set (Sym2 V)) : 
fromEdgeSet (s \ t) = fromEdgeSet s \ fromEdgeSet t
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
@[simp] lemma deleteEdges_fromEdgeSet (s t : Set (Sym2 V)) :
    (fromEdgeSet s).deleteEdges t = fromEdgeSet (s \ t) := by ext; simp +contextual
/-
**SimpleGraph.deleteEdges_eq_bot** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：∀ {V : Type u_1} {G : SimpleGraph V} {s : Set (Sym2 V)}, G.deleteEdges s =
 ⊥ ↔ G.edgeSet ⊆ s
参数：Sym2 V。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma deleteEdges_eq_bot : G.deleteEdges s = ⊥ ↔ G.edgeSet ⊆ s := by simp [deleteEdges]

end DeleteEdges

section DeleteIncidenceSet

/-- Given a vertex `x`, remove the edges incident to `x` from the edge set. -/
/-
**SimpleGraph.deleteIncidenceSet** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph`。
形式化陈述：deleteIncidenceSet (G : SimpleGraph V) (x : V) : SimpleGraph V
参数：G : SimpleGraph V；x : V。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a vertex `x`, remove the edges incident to `x` from the edge set.
-/
def deleteIncidenceSet (G : SimpleGraph V) (x : V) : SimpleGraph V :=
  G.deleteEdges (G.incidenceSet x)
/-
**SimpleGraph.deleteIncidenceSet_adj** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
形式化陈述：deleteIncidenceSet_adj {G : SimpleGraph V} {x v₁ v₂ : V} : (G.deleteIncide
nceSet x).Adj v₁ v₂ ↔ G.Adj v₁ v₂ ∧ v₁ != x ∧ v₂ != x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.deleteIncidenceSet.eq_1`：∀ {V : Type u_1} (G : SimpleGraph V
) (x : V), G.deleteIncidenceSet x = G.deleteEdges (G.incidenceSet x)
· 使用定理 `SimpleGraph.deleteEdges_adj`：∀ {V : Type u_1} {v w : V} {G : SimpleGraph
 V} {s : Set (Sym2 V)}, (G.deleteEdges s).Adj v w ↔ G.Adj v w ∧ s(v, w) ∉ s
· 使用定理 `SimpleGraph.mk'_mem_incidenceSet_iff`：∀ {V : Type u} (G : SimpleGraph V)
 {a b c : V}, s(b, c) ∈ G.incidenceSet a ↔ G.Adj b c ∧ (a = b ∨ a = c)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Decidable.not_and_iff_not_or_not'`：∀ {b a : Prop} [Decidable b], ¬(a ∧ b
) ↔ ¬a ∨ ¬b
· 使用定理 `not_or`：∀ {p q : Prop}, ¬(p ∨ q) ↔ ¬p ∧ ¬q
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma deleteIncidenceSet_adj {G : SimpleGraph V} {x v₁ v₂ : V} :
    (G.deleteIncidenceSet x).Adj v₁ v₂ ↔ G.Adj v₁ v₂ ∧ v₁ ≠ x ∧ v₂ ≠ x := by
  rw [deleteIncidenceSet, deleteEdges_adj, mk'_mem_incidenceSet_iff]
  tauto
/-
**SimpleGraph.deleteIncidenceSet_le** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
形式化陈述：deleteIncidenceSet_le (G : SimpleGraph V) (x : V) : G.deleteIncidenceSet x
 <= G
参数：G : SimpleGraph V；x : V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SimpleGraph.deleteEdges_le`：deleteEdges_le (s : Set (Sym2 V)) : G.delete
Edges s <= G
-/
lemma deleteIncidenceSet_le (G : SimpleGraph V) (x : V) : G.deleteIncidenceSet x ≤ G :=
  deleteEdges_le (G.incidenceSet x)
/-
**SimpleGraph.edgeSet_fromEdgeSet_incidenceSet** 是 Mathlib 中的一个引理，位于命名空间 `Simple
Graph`。
形式化陈述：edgeSet_fromEdgeSet_incidenceSet (G : SimpleGraph V) (x : V) : (fromEdgeSe
t (G.incidenceSet x)).edgeSet = G.incidenceSet x
参数：G : SimpleGraph V；x : V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.edgeSet_fromEdgeSet`：edgeSet_fromEdgeSet : (fromEdgeSet s).e
dgeSet = s \ Sym2.diagSet
· 使用定理 `sdiff_eq_left`：∀ {α : Type u} {x y : α} [inst : GeneralizedBooleanAlgebr
a α], x \ y = x ↔ Disjoint x y
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Set.subset_compl_iff_disjoint_right`：subset_compl_iff_disjoint_right : s
 subseteq tᶜ ↔ Disjoint s t
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `SimpleGraph.incidenceSet_subset`：incidenceSet_subset (v : V) : G.inciden
ceSet v subseteq G.edgeSet
· 使用定理 `SimpleGraph.edgeSet_subset_compl_diagSet`：edgeSet_subset_compl_diagSet :
 G.edgeSet subseteq Sym2.diagSetᶜ
-/
lemma edgeSet_fromEdgeSet_incidenceSet (G : SimpleGraph V) (x : V) :
    (fromEdgeSet (G.incidenceSet x)).edgeSet = G.incidenceSet x := by
  rw [edgeSet_fromEdgeSet, sdiff_eq_left, ← Set.subset_compl_iff_disjoint_right]
  exact (incidenceSet_subset G x).trans G.edgeSet_subset_compl_diagSet

/-- The edge set of `G.deleteIncidenceSet x` is the edge set of `G` set difference the incidence
set of the vertex `x`. -/
/-
**SimpleGraph.edgeSet_deleteIncidenceSet** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`
。
形式化陈述：edgeSet_deleteIncidenceSet (G : SimpleGraph V) (x : V) : (G.deleteIncidenc
eSet x).edgeSet = G.edgeSet \ G.incidenceSet x
参数：G : SimpleGraph V；x : V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.edgeSet_sdiff`：edgeSet_sdiff : (G₁ \ G₂).edgeSet = G₁.edgeSe
t \ G₂.edgeSet
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `SimpleGraph.edgeSet_fromEdgeSet_incidenceSet`：edgeSet_fromEdgeSet_incide
nceSet (G : SimpleGraph V) (x : V) : (fromEdgeSet (G.incidenceSet x)).edgeSet = 
G.incidenceSet x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The edge set of `G.deleteIncidenceSet x` is the edge set of `G` set difference t
he incidence
set of the vertex `x`.
-/
theorem edgeSet_deleteIncidenceSet (G : SimpleGraph V) (x : V) :
    (G.deleteIncidenceSet x).edgeSet = G.edgeSet \ G.incidenceSet x := by
  simp_rw [deleteIncidenceSet, deleteEdges, edgeSet_sdiff, edgeSet_fromEdgeSet_incidenceSet]

/-- The support of `G.deleteIncidenceSet x` is a subset of the support of `G` set difference the
singleton set `{x}`. -/
/-
**SimpleGraph.support_deleteIncidenceSet_subset** 是 Mathlib 中的一个定理，位于命名空间 `Simpl
eGraph`。
形式化陈述：support_deleteIncidenceSet_subset (G : SimpleGraph V) (x : V) : (G.deleteI
ncidenceSet x).support subseteq G.support \ {x}
参数：G : SimpleGraph V；x : V。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g

--- 原说明 ---
The support of `G.deleteIncidenceSet x` is a subset of the support of `G` set di
fference the
singleton set `{x}`.
-/
theorem support_deleteIncidenceSet_subset (G : SimpleGraph V) (x : V) :
    (G.deleteIncidenceSet x).support ⊆ G.support \ {x} :=
  fun _ ↦ by simp_rw [mem_support, deleteIncidenceSet_adj]; tauto

/-- If the vertex `x` is not in the set `s`, then the induced subgraph in `G.deleteIncidenceSet x`
by `s` is equal to the induced subgraph in `G` by `s`. -/
/-
**SimpleGraph.induce_deleteIncidenceSet_of_notMem** 是 Mathlib 中的一个定理，位于命名空间 `Sim
pleGraph`。
形式化陈述：induce_deleteIncidenceSet_of_notMem (G : SimpleGraph V) {s : Set V} {x : V
} (h : x ∉ s) : (G.deleteIncidenceSet x).induce s = G.induce s
参数：G : SimpleGraph V；h : x ∉ s。
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
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Membership.mem.ne_of_notMem`：∀ {α : Type u_1} {β : Type u_2} [inst : Mem
bership α β] {s : β} {a b : α}, a ∈ s → b ∉ s → a ≠ b
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x

--- 原说明 ---
If the vertex `x` is not in the set `s`, then the induced subgraph in `G.deleteI
ncidenceSet x`
by `s` is equal to the induced subgraph in `G` by `s`.
-/
theorem induce_deleteIncidenceSet_of_notMem (G : SimpleGraph V) {s : Set V} {x : V} (h : x ∉ s) :
    (G.deleteIncidenceSet x).induce s = G.induce s := by
  ext v₁ v₂
  simp_rw [comap_adj, Function.Embedding.coe_subtype, deleteIncidenceSet_adj, and_iff_left_iff_imp]
  exact fun _ ↦ ⟨v₁.prop.ne_of_notMem h, v₂.prop.ne_of_notMem h⟩

variable [Fintype V] [DecidableEq V]
/-
**SimpleGraph.** 是 Mathlib 中的一个实例，位于命名空间 `SimpleGraph`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {G : SimpleGraph V} [DecidableRel G.Adj] {x : V} :
    DecidableRel (G.deleteIncidenceSet x).Adj :=
  inferInstanceAs <| DecidableRel (G.deleteEdges (G.incidenceSet x)).Adj

/-- Deleting the incidence set of the vertex `x` retains the same number of edges as in the induced
subgraph of the vertices `{x}ᶜ`. -/
/-
**SimpleGraph.card_edgeFinset_induce_compl_singleton** 是 Mathlib 中的一个定理，位于命名空间 `
SimpleGraph`。
形式化陈述：card_edgeFinset_induce_compl_singleton (G : SimpleGraph V) [DecidableRel G
.Adj] (x : V) : #(G.induce {x}ᶜ).edgeFinset = #(G.deleteIncidenceSet x).edgeFins
et
参数：G : SimpleGraph V；x : V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.notMem_compl_iff`：notMem_compl_iff {x : α} : x ∉ sᶜ ↔ x in s
· 使用定理 `Set.mem_singleton`：mem_singleton (a : α) : a in ({a} : Set α)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.toFinset_card`：toFinset_card {α : Type*} (s : Set α) [Fintype s] : s
.toFinset.card = Fintype.card s
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Fintype.card_congr'`：card_congr' {α β} [Fintype α] [Fintype β] (h : α = 
β) : card α = card β
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SimpleGraph.induce_deleteIncidenceSet_of_notMem`：induce_deleteIncidenceS
et_of_notMem (G : SimpleGraph V) {s : Set V} {x : V} (h : x ∉ s) : (G.deleteInci
denceSet x).induce s = G.induce s
· 使用定理 `SimpleGraph.card_edgeFinset_induce_of_support_subset`：card_edgeFinset_in
duce_of_support_subset (h : G.support subseteq s) : #(G.induce s).edgeFinset = #
G.edgeFinset
· 使用定理 `SimpleGraph.support_deleteIncidenceSet_subset`：support_deleteIncidenceSe
t_subset (G : SimpleGraph V) (x : V) : (G.deleteIncidenceSet x).support subseteq
 G.support \ {x}
· 使用定理 `Set.compl_eq_univ_sdiff`：compl_eq_univ_sdiff (s : Set α) : sᶜ = univ \ s
· 使用定理 `Set.sdiff_subset_sdiff_left`：sdiff_subset_sdiff_left {s₁ s₂ t : Set α} (
h : s₁ subseteq s₂) : s₁ \ t subseteq s₂ \ t
· 使用定理 `Set.subset_univ`：subset_univ (s : Set α) : s subseteq univ

--- 原说明 ---
Deleting the incidence set of the vertex `x` retains the same number of edges as
 in the induced
subgraph of the vertices `{x}ᶜ`.
-/
theorem card_edgeFinset_induce_compl_singleton (G : SimpleGraph V) [DecidableRel G.Adj] (x : V) :
    #(G.induce {x}ᶜ).edgeFinset = #(G.deleteIncidenceSet x).edgeFinset := by
  have h_notMem : x ∉ ({x}ᶜ : Set V) := Set.notMem_compl_iff.mpr (Set.mem_singleton x)
  simp_rw [edgeFinset, Set.toFinset_card,
    ← G.induce_deleteIncidenceSet_of_notMem h_notMem, ← Set.toFinset_card]
  apply card_edgeFinset_induce_of_support_subset
  trans G.support \ {x}
  · exact support_deleteIncidenceSet_subset G x
  · rw [Set.compl_eq_univ_sdiff]
    exact Set.sdiff_subset_sdiff_left (Set.subset_univ G.support)

/-- The finite edge set of `G.deleteIncidenceSet x` is the finite edge set of the simple graph `G`
set difference the finite incidence set of the vertex `x`. -/
/-
**SimpleGraph.edgeFinset_deleteIncidenceSet_eq_sdiff** 是 Mathlib 中的一个定理，位于命名空间 `
SimpleGraph`。
形式化陈述：edgeFinset_deleteIncidenceSet_eq_sdiff (G : SimpleGraph V) [DecidableRel G
.Adj] (x : V) : (G.deleteIncidenceSet x).edgeFinset = G.edgeFinset \ G.incidence
Finset x
参数：G : SimpleGraph V；x : V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.coe_injective`：coe_injective {α} : Injective ((↑) : Finset α -> S
et α)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.coe_edgeFinset`：coe_edgeFinset : (G.edgeFinset : Set (Sym2 V
)) = G.edgeSet
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.coe_sdiff`：coe_sdiff (s₁ s₂ : Finset α) : ↑(s₁ \ s₂) = (s₁ \ s₂ :
 Set α)
· 使用定理 `SimpleGraph.coe_incidenceFinset`：coe_incidenceFinset [DecidableEq V] : (
G.incidenceFinset v : Set (Sym2 V)) = G.incidenceSet v
· 使用定理 `SimpleGraph.edgeSet_deleteIncidenceSet`：edgeSet_deleteIncidenceSet (G : 
SimpleGraph V) (x : V) : (G.deleteIncidenceSet x).edgeSet = G.edgeSet \ G.incide
nceSet x

--- 原说明 ---
The finite edge set of `G.deleteIncidenceSet x` is the finite edge set of the si
mple graph `G`
set difference the finite incidence set of the vertex `x`.
-/
theorem edgeFinset_deleteIncidenceSet_eq_sdiff (G : SimpleGraph V) [DecidableRel G.Adj] (x : V) :
    (G.deleteIncidenceSet x).edgeFinset = G.edgeFinset \ G.incidenceFinset x := by
  apply Finset.coe_injective
  push_cast
  exact G.edgeSet_deleteIncidenceSet x

/-- Deleting the incident set of the vertex `x` deletes exactly `G.degree x` edges from the edge
set of the simple graph `G`. -/
/-
**SimpleGraph.card_edgeFinset_deleteIncidenceSet** 是 Mathlib 中的一个定理，位于命名空间 `Simp
leGraph`。
形式化陈述：card_edgeFinset_deleteIncidenceSet (G : SimpleGraph V) [DecidableRel G.Adj
] (x : V) : #(G.deleteIncidenceSet x).edgeFinset = #G.edgeFinset - G.degree x
参数：G : SimpleGraph V；x : V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.card_sdiff_of_subset`：card_sdiff_of_subset (h : s subseteq t) : #
(t \ s) = #t - #s
· 使用定理 `SimpleGraph.incidenceFinset_subset`：incidenceFinset_subset [DecidableEq 
V] [Fintype G.edgeSet] : G.incidenceFinset v subseteq G.edgeFinset
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `SimpleGraph.edgeFinset_deleteIncidenceSet_eq_sdiff`：edgeFinset_deleteInc
idenceSet_eq_sdiff (G : SimpleGraph V) [DecidableRel G.Adj] (x : V) : (G.deleteI
ncidenceSet x).edgeFinset = G.edgeFinset…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Deleting the incident set of the vertex `x` deletes exactly `G.degree x` edges f
rom the edge
set of the simple graph `G`.
-/
theorem card_edgeFinset_deleteIncidenceSet (G : SimpleGraph V) [DecidableRel G.Adj] (x : V) :
    #(G.deleteIncidenceSet x).edgeFinset = #G.edgeFinset - G.degree x := by
  simp_rw [← card_incidenceFinset_eq_degree, ← card_sdiff_of_subset (G.incidenceFinset_subset x),
    edgeFinset_deleteIncidenceSet_eq_sdiff]

/-- Deleting the incident set of the vertex `x` is equivalent to filtering the edges of the simple
graph `G` that do not contain `x`. -/
/-
**SimpleGraph.edgeFinset_deleteIncidenceSet_eq_filter** 是 Mathlib 中的一个定理，位于命名空间 
`SimpleGraph`。
形式化陈述：edgeFinset_deleteIncidenceSet_eq_filter (G : SimpleGraph V) [DecidableRel 
G.Adj] (x : V) : (G.deleteIncidenceSet x).edgeFinset = G.edgeFinset.filter (x ∉ 
·)
参数：G : SimpleGraph V；x : V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.edgeFinset_deleteIncidenceSet_eq_sdiff`：edgeFinset_deleteInc
idenceSet_eq_sdiff (G : SimpleGraph V) [DecidableRel G.Adj] (x : V) : (G.deleteI
ncidenceSet x).edgeFinset = G.edgeFinset…
· 使用定理 `Finset.sdiff_eq_filter`：sdiff_eq_filter (s₁ s₂ : Finset α) : s₁ \ s₂ = s
₁.filter (· ∉ s₂)
· 使用定理 `Finset.filter_congr`：∀ {α : Type u_1} {p q : α → Prop} [inst : Decidable
Pred p] [inst_1 : DecidablePred q] {s : Finset α},   (∀ x ∈ s, p x ↔ q x) → Fins
et.filter…
· 使用定理 `SimpleGraph.incidenceFinset.eq_1`：∀ {V : Type u_1} (G : SimpleGraph V) (
v : V) [inst : Fintype ↑(G.neighborSet v)] [inst_1 : DecidableEq V],   G.inciden
ceFinset v = (G.incide…
· 使用定理 `Set.mem_toFinset`：mem_toFinset {s : Set α} [Fintype s] {a : α} : a in s.
toFinset ↔ a in s
· 使用定理 `SimpleGraph.incidenceSet.eq_1`：∀ {V : Type u} (G : SimpleGraph V) (v : V
), G.incidenceSet v = {e | e ∈ G.edgeSet ∧ v ∈ e}
· 使用定理 `Set.mem_ofPred_eq`：mem_ofPred_eq {x : α} {p : α -> Prop} : (x in {y | p 
y}) = p x
· 使用定理 `not_and`：∀ {a b : Prop}, ¬(a ∧ b) ↔ a → ¬b
· 使用定理 `Classical.imp_iff_right_iff`：∀ {a b : Prop}, (a → b ↔ b) ↔ a ∨ b
· 使用定理 `SimpleGraph.mem_edgeFinset`：mem_edgeFinset : e in G.edgeFinset ↔ e in G.
edgeSet

--- 原说明 ---
Deleting the incident set of the vertex `x` is equivalent to filtering the edges
 of the simple
graph `G` that do not contain `x`.
-/
theorem edgeFinset_deleteIncidenceSet_eq_filter (G : SimpleGraph V) [DecidableRel G.Adj] (x : V) :
    (G.deleteIncidenceSet x).edgeFinset = G.edgeFinset.filter (x ∉ ·) := by
  rw [edgeFinset_deleteIncidenceSet_eq_sdiff, sdiff_eq_filter]
  apply filter_congr
  intro _ h
  rw [incidenceFinset, Set.mem_toFinset, incidenceSet,
    Set.mem_ofPred_eq, not_and, Classical.imp_iff_right_iff]
  left
  rwa [mem_edgeFinset] at h

/-- The support of `G.deleteIncidenceSet x` is at most `1` less than the support of the simple
graph `G`. -/
/-
**SimpleGraph.card_support_deleteIncidenceSet** 是 Mathlib 中的一个定理，位于命名空间 `SimpleG
raph`。
形式化陈述：card_support_deleteIncidenceSet (G : SimpleGraph V) [DecidableRel G.Adj] {
x : V} (hx : x in G.support) : card (G.deleteIncidenceSet x).support <= card G.s
upport - 1
参数：G : SimpleGraph V；hx : x in G.support。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.card_sdiff_of_subset`：card_sdiff_of_subset (h : s subseteq t) : #
(t \ s) = #t - #s
· 使用定理 `Set.toFinset_subset_toFinset`：toFinset_subset_toFinset [Fintype s] [Fint
ype t] : s.toFinset subseteq t.toFinset ↔ s subseteq t
· 使用定理 `Set.singleton_subset_iff`：singleton_subset_iff {a : α} {s : Set α} : {a}
 subseteq s ↔ a in s
· 使用定理 `Finset.card_le_card`：card_le_card : s subseteq t -> #s <= #t
· 使用定理 `SimpleGraph.support_deleteIncidenceSet_subset`：support_deleteIncidenceSe
t_subset (G : SimpleGraph V) (x : V) : (G.deleteIncidenceSet x).support subseteq
 G.support \ {x}

--- 原说明 ---
The support of `G.deleteIncidenceSet x` is at most `1` less than the support of 
the simple
graph `G`.
-/
theorem card_support_deleteIncidenceSet
    (G : SimpleGraph V) [DecidableRel G.Adj] {x : V} (hx : x ∈ G.support) :
    card (G.deleteIncidenceSet x).support ≤ card G.support - 1 := by
  rw [← Set.singleton_subset_iff, ← Set.toFinset_subset_toFinset] at hx
  simp_rw [← Set.card_singleton x, ← Set.toFinset_card, ← card_sdiff_of_subset hx,
    ← Set.toFinset_sdiff]
  apply card_le_card
  rw [Set.toFinset_subset_toFinset]
  exact G.support_deleteIncidenceSet_subset x

end DeleteIncidenceSet

section DeleteFar

variable {𝕜 : Type*} [Ring 𝕜] [PartialOrder 𝕜]
  [Fintype G.edgeSet] {p : SimpleGraph V → Prop} {r r₁ r₂ : 𝕜}

/-- A graph is `r`-*delete-far* from a property `p` if we must delete at least `r` edges from it to
get a graph with the property `p`. -/
/-
**SimpleGraph.DeleteFar** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph`。
形式化陈述：DeleteFar (p : SimpleGraph V -> Prop) (r : 𝕜) : Prop
参数：p : SimpleGraph V -> Prop；r : 𝕜。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A graph is `r`-*delete-far* from a property `p` if we must delete at least `r` e
dges from it to
get a graph with the property `p`.
-/
def DeleteFar (p : SimpleGraph V → Prop) (r : 𝕜) : Prop :=
  ∀ ⦃s⦄, s ⊆ G.edgeFinset → p (G.deleteEdges s) → r ≤ #s

variable {G}
/-
**SimpleGraph.deleteFar_iff** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：deleteFar_iff [Fintype (Sym2 V)] : G.DeleteFar p r ↔ forall ⦃H : SimpleGra
ph _⦄ [DecidableRel H.Adj], H <= G -> p H -> r <= #G.edgeFinset - #H.edgeFinset
参数：Sym2 V。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.sdiff_subset`：sdiff_subset {s t : Finset α} : s \ t subseteq s
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.coe_sdiff`：coe_sdiff (s₁ s₂ : Finset α) : ↑(s₁ \ s₂) = (s₁ \ s₂ :
 Set α)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `SimpleGraph.coe_edgeFinset`：coe_edgeFinset : (G.edgeFinset : Set (Sym2 V
)) = G.edgeSet
· 使用定理 `SimpleGraph.deleteEdges_sdiff_eq_of_le`：deleteEdges_sdiff_eq_of_le {H : 
SimpleGraph V} (h : H <= G) : G.deleteEdges (G.edgeSet \ H.edgeSet) = H
· 使用定理 `Finset.card_sdiff_of_subset`：card_sdiff_of_subset (h : s subseteq t) : #
(t \ s) = #t - #s
· 使用定理 `SimpleGraph.edgeFinset_mono`：∀ {V : Type u_1} {G₁ G₂ : SimpleGraph V} [i
nst : Fintype ↑G₁.edgeSet] [inst_1 : Fintype ↑G₂.edgeSet],   G₁ ≤ G₂ → G₁.edgeFi
nset ⊆ G₂.edgeFin…
· 使用定理 `Nat.cast_sub`：cast_sub {m n} (h : m <= n) : ((n - m : Nat) : R) = n - m
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `SimpleGraph.edgeFinset_deleteEdges`：∀ {V : Type u_1} {G : SimpleGraph V}
 [inst : DecidableEq V] [inst_1 : Fintype ↑G.edgeSet] (s : Finset (Sym2 V))   [i
nst_2 : Fintype ↑(G.dele…
· 使用定理 `Finset.card_le_card`：card_le_card : s subseteq t -> #s <= #t
· 使用定理 `sub_sub_cancel`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G), a - 
(a - b) = b
· 使用引理 `SimpleGraph.deleteEdges_le`：deleteEdges_le (s : Set (Sym2 V)) : G.delete
Edges s <= G
-/
theorem deleteFar_iff [Fintype (Sym2 V)] :
    G.DeleteFar p r ↔ ∀ ⦃H : SimpleGraph _⦄ [DecidableRel H.Adj],
      H ≤ G → p H → r ≤ #G.edgeFinset - #H.edgeFinset := by
  classical
  refine ⟨fun h H _ hHG hH ↦ ?_, fun h s hs hG ↦ ?_⟩
  · have := h (sdiff_subset (t := H.edgeFinset))
    simp only [deleteEdges_sdiff_eq_of_le hHG, edgeFinset_mono hHG, card_sdiff_of_subset,
      card_le_card, coe_sdiff, coe_edgeFinset, Nat.cast_sub] at this
    exact this hH
  · classical
    simpa [card_sdiff_of_subset hs, edgeFinset_deleteEdges, -Set.toFinset_card, Nat.cast_sub,
      card_le_card hs] using h (G.deleteEdges_le s) hG

alias ⟨DeleteFar.le_card_sub_card, _⟩ := deleteFar_iff
/-
**SimpleGraph.DeleteFar.mono** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.DeleteFar`。
形式化陈述：∀ {V : Type u_1} {G : SimpleGraph V} {𝕜 : Type u_2} [inst : Ring 𝕜] [inst_
1 : PartialOrder 𝕜]   [inst_2 : Fintype ↑G.edgeSet] {p : SimpleGraph V → Prop} {
r₁ r₂ : 𝕜}, G.DeleteFar p r₂ → r₁ ≤ r₂ → G.DeleteFar p r₁
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
-/
theorem DeleteFar.mono (h : G.DeleteFar p r₂) (hr : r₁ ≤ r₂) : G.DeleteFar p r₁ := fun _ hs hG =>
  hr.trans <| h hs hG
/-
**SimpleGraph.DeleteFar.le_card_edgeFinset** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGrap
h.DeleteFar`。
形式化陈述：∀ {V : Type u_1} {G : SimpleGraph V} {𝕜 : Type u_2} [inst : Ring 𝕜] [inst_
1 : PartialOrder 𝕜]   [inst_2 : Fintype ↑G.edgeSet] {p : SimpleGraph V → Prop} {
r : 𝕜}, G.DeleteFar p r → p ⊥ → r ≤ ↑G.edgeFinset.card
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `subset_rfl`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preorde
r α] {a : α}, a ⊆ a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `SimpleGraph.coe_edgeFinset`：coe_edgeFinset : (G.edgeFinset : Set (Sym2 V
)) = G.edgeSet
· 使用定理 `SimpleGraph.deleteEdges_edgeSet`：∀ {V : Type u_1} (G G' : SimpleGraph V)
, G.deleteEdges G'.edgeSet = G \ G'
· 使用定理 `sdiff_self`：∀ {α : Type u_2} [inst : GeneralizedCoheytingAlgebra α] {a :
 α}, a \ a = ⊥
-/
lemma DeleteFar.le_card_edgeFinset (h : G.DeleteFar p r) (hp : p ⊥) : r ≤ #G.edgeFinset :=
  h subset_rfl (by simpa)

end DeleteFar

end SimpleGraph

