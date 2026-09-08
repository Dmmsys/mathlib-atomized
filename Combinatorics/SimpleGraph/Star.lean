/-
Copyright (c) 2026 Justin Lai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Justin Lai
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-!

# Star Graphs

## Main definitions

* `SimpleGraph.starGraph r` is the star graph on V centered at r. Every non-center vertex is
  adjacent to r.

## Main statements

* `SimpleGraph.isTree_starGraph` proves the star graph is a tree.


## Tags

star graph
-/

@[expose] public section

namespace SimpleGraph

variable {V V' : Type*} (G : SimpleGraph V) (G' : SimpleGraph V')

/-- The star graph on `V` centered at `r`: every non-center vertex is adjacent to `r`. -/
/-
**SimpleGraph.starGraph** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph`。
形式化陈述：starGraph (r : V) : SimpleGraph V
参数：r : V。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The star graph on `V` centered at `r`: every non-center vertex is adjacent to `r
`.
-/
def starGraph (r : V) : SimpleGraph V :=
  .fromRel fun v _ ↦ v = r
/-
**SimpleGraph.** 是 Mathlib 中的一个实例，位于命名空间 `SimpleGraph`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [DecidableEq V] (r : V) : DecidableRel (starGraph r).Adj :=
  inferInstanceAs (DecidableRel fun x y ↦ x ≠ y ∧ (x = r ∨ y = r))

@[simp]
/-
**SimpleGraph.starGraph_adj** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
形式化陈述：starGraph_adj {r x y : V} : (starGraph r).Adj x y ↔ x != y ∧ (x = r ∨ y = 
r)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma starGraph_adj {r x y : V} : (starGraph r).Adj x y ↔ x ≠ y ∧ (x = r ∨ y = r) := by
  simp [starGraph, fromRel]

@[simp]
/-
**SimpleGraph.isUniversal_starGraph_self** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`
。
形式化陈述：isUniversal_starGraph_self {r : V} : (starGraph r).IsUniversal r
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
-/
lemma isUniversal_starGraph_self {r : V} : (starGraph r).IsUniversal r := by
  intro _ _
  simpa

/-- On (starGraph r), r is adjacent to v iff v ≠ r. -/
/-
**SimpleGraph.starGraph_adj_center_iff** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
形式化陈述：starGraph_adj_center_iff {r v : V} : (starGraph r).Adj r v ↔ r != v
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
On (starGraph r), r is adjacent to v iff v ≠ r.
-/
lemma starGraph_adj_center_iff {r v : V} : (starGraph r).Adj r v ↔ r ≠ v := by simp
/-
**SimpleGraph.starGraph_center_adj** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
形式化陈述：starGraph_center_adj {r v : V} (h : r != v) : (starGraph r).Adj r v
参数：h : r != v。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `SimpleGraph.starGraph_adj_center_iff`：starGraph_adj_center_iff {r v : V}
 : (starGraph r).Adj r v ↔ r != v
-/
lemma starGraph_center_adj {r v : V} (h : r ≠ v) : (starGraph r).Adj r v :=
  starGraph_adj_center_iff.mpr h
/-
**SimpleGraph.starGraph_center_adj'** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
形式化陈述：starGraph_center_adj' {r v : V} (h : r != v) : (starGraph r).Adj v r
参数：h : r != v。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Adj.symm`：∀ {V : Type u} {G : SimpleGraph V} {u v : V}, G.Ad
j u v → G.Adj v u
· 使用引理 `SimpleGraph.starGraph_center_adj`：starGraph_center_adj {r v : V} (h : r 
!= v) : (starGraph r).Adj r v
-/
lemma starGraph_center_adj' {r v : V} (h : r ≠ v) : (starGraph r).Adj v r :=
  (starGraph_center_adj h).symm
/-
**SimpleGraph.connected_starGraph** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
形式化陈述：connected_starGraph (r : V) : (starGraph r).Connected
参数：r : V。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Connected.of_isUniversal`：∀ {V : Type u} {G : SimpleGraph V}
 {v : V}, G.IsUniversal v → G.Connected
· 使用引理 `SimpleGraph.isUniversal_starGraph_self`：isUniversal_starGraph_self {r : 
V} : (starGraph r).IsUniversal r
-/
lemma connected_starGraph (r : V) : (starGraph r).Connected :=
  .of_isUniversal isUniversal_starGraph_self
/-
**SimpleGraph.isAcyclic_starGraph** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
形式化陈述：isAcyclic_starGraph (r : V) : (starGraph r).IsAcyclic
参数：r : V。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `SimpleGraph.isAcyclic_iff_forall_adj_isBridge`：isAcyclic_iff_forall_adj_
isBridge : G.IsAcyclic ↔ forall ⦃v w : V⦄, G.Adj v w -> G.IsBridge s(v, w)
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用引理 `SimpleGraph.not_reachable_of_neighborSet_right_eq_empty`：not_reachable_o
f_neighborSet_right_eq_empty {G : SimpleGraph V} {u v : V} (huv : u != v) (hv : 
G.neighborSet v = ∅) : ¬G.Reachable u v
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Prod.mk.injEq`：∀ {α : Type u} {β : Type v} (fst : α) (snd : β) (fst_1 : 
α) (snd_1 : β),   ((fst, snd) = (fst_1, snd_1)) = (fst = fst_1 ∧ snd = snd_1)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_false`：∀ (p : Prop), (p ↔ False) = ¬p
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用引理 `SimpleGraph.starGraph_adj`：starGraph_adj {r x y : V} : (starGraph r).Adj
 x y ↔ x != y ∧ (x = r ∨ y = r)
· 使用定理 `Sym2.eq_swap`：eq_swap {a b : α} : s(a, b) = s(b, a)
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `Or.symm`：∀ {a b : Prop}, a ∨ b → b ∨ a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
-/
lemma isAcyclic_starGraph (r : V) : (starGraph r).IsAcyclic := by
  refine isAcyclic_iff_forall_adj_isBridge.mpr fun v w hadj ↦ ?_
  rw [starGraph_adj] at hadj
  wlog! h : v = r
  · rw [Sym2.eq_swap]
    exact this r w v ⟨hadj.1.symm, hadj.2.symm⟩ (hadj.2.resolve_left h)
  · subst h
    apply not_reachable_of_neighborSet_right_eq_empty hadj.1
    ext x
    aesop
/-
**SimpleGraph.isTree_starGraph** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
形式化陈述：isTree_starGraph (r : V) : (starGraph r).IsTree
参数：r : V。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SimpleGraph.connected_starGraph`：connected_starGraph (r : V) : (starGrap
h r).Connected
· 使用引理 `SimpleGraph.isAcyclic_starGraph`：isAcyclic_starGraph (r : V) : (starGrap
h r).IsAcyclic
-/
lemma isTree_starGraph (r : V) : (starGraph r).IsTree :=
  ⟨connected_starGraph r, isAcyclic_starGraph r⟩

/-- Every non-center vertex of a starGraph has degree one. -/
/-
**SimpleGraph.degree_starGraph_of_ne_center** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGra
ph`。
形式化陈述：degree_starGraph_of_ne_center [Fintype V] [DecidableEq V] {r v : V} (h : v
 != r) : (starGraph r).degree v = 1
参数：h : v != r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `SimpleGraph.degree_eq_one_iff_existsUnique_adj`：degree_eq_one_iff_exists
Unique_adj {G : SimpleGraph V} {v : V} [Fintype (G.neighborSet v)] : G.degree v 
= 1 ↔ exists! w : V, G.Adj v w
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p

--- 原说明 ---
Every non-center vertex of a starGraph has degree one.
-/
lemma degree_starGraph_of_ne_center [Fintype V] [DecidableEq V] {r v : V} (h : v ≠ r) :
    (starGraph r).degree v = 1 :=
  degree_eq_one_iff_existsUnique_adj.mpr ⟨r, by simp [h], by grind [starGraph_adj]⟩

/-- The center vertex of a starGraph has degree (card V) - 1. -/
/-
**SimpleGraph.degree_starGraph_center** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
形式化陈述：degree_starGraph_center [Fintype V] [DecidableEq V] {r : V} : (starGraph r
).degree r = Fintype.card V - 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c

--- 原说明 ---
The center vertex of a starGraph has degree (card V) - 1.
-/
lemma degree_starGraph_center [Fintype V] [DecidableEq V] {r : V} :
    (starGraph r).degree r = Fintype.card V - 1 := by
  simp

end SimpleGraph

