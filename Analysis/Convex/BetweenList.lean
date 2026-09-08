/-
Copyright (c) 2025 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
module

public import Mathlib.Analysis.Convex.Between
public import Mathlib.Data.List.Triplewise

/-!
# Betweenness for lists of points.

This file defines notions of lists of points in an affine space being in order on a line.

## Main definitions

* `List.Wbtw R l`: The points in list `l` are weakly in order on a line.
* `List.Sbtw R l`: The points in list `l` are strictly in order on a line.

-/

@[expose] public section


variable (R : Type*) {V V' P P' : Type*}

open AffineEquiv AffineMap

namespace List

section OrderedRing

variable [Ring R] [PartialOrder R] [AddCommGroup V] [Module R V] [AddTorsor V P]
variable [AddCommGroup V'] [Module R V'] [AddTorsor V' P']

/-- The points in a list are weakly in that order on a line. -/
/-
**List.Wbtw** 是 Mathlib 中的一个定义，位于命名空间 `List`。
形式化陈述：(R : Type u_1) →   {V : Type u_2} →     {P : Type u_4} →       [inst : Rin
g R] →         [PartialOrder R] → [inst_2 : AddCommGroup V] → [_root_.Module R V
] → [AddTorsor V P] → List P → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The points in a list are weakly in that order on a line.
-/
protected def Wbtw (l : List P) : Prop :=
  l.Triplewise (Wbtw R)

variable {R}
/-
**List.wbtw_cons** 是 Mathlib 中的一个引理，位于命名空间 `List`。
形式化陈述：wbtw_cons {p : P} {l : List P} : (p :: l).Wbtw R ↔ l.Pairwise (Wbtw R p) ∧
 l.Wbtw R
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `List.triplewise_cons`：triplewise_cons : (a :: l).Triplewise p ↔ l.Pairwi
se (p a) ∧ l.Triplewise p
-/
lemma wbtw_cons {p : P} {l : List P} : (p :: l).Wbtw R ↔ l.Pairwise (Wbtw R p) ∧ l.Wbtw R :=
  triplewise_cons

variable (R)

/-- The points in a list are strictly in that order on a line. -/
/-
**List.Sbtw** 是 Mathlib 中的一个定义，位于命名空间 `List`。
形式化陈述：(R : Type u_1) →   {V : Type u_2} →     {P : Type u_4} →       [inst : Rin
g R] →         [PartialOrder R] → [inst_2 : AddCommGroup V] → [_root_.Module R V
] → [AddTorsor V P] → List P → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The points in a list are strictly in that order on a line.
-/
protected def Sbtw (l : List P) : Prop :=
  l.Wbtw R ∧ l.Pairwise (· ≠ ·)

variable (P)
/-
**List.wbtw_nil** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ (R : Type u_1) {V : Type u_2} (P : Type u_4) [inst : Ring R] [inst_1 : P
artialOrder R] [inst_2 : AddCommGroup V]   [inst_3 : _root_.Module R V] [inst_4 
: AddTorsor V P], List.Wbtw R []
参数：R : Type u_1；P : Type u_4。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
-/
@[simp] lemma wbtw_nil : ([] : List P).Wbtw R := by
  simp [List.Wbtw]
/-
**List.sbtw_nil** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ (R : Type u_1) {V : Type u_2} (P : Type u_4) [inst : Ring R] [inst_1 : P
artialOrder R] [inst_2 : AddCommGroup V]   [inst_3 : _root_.Module R V] [inst_4 
: AddTorsor V P], List.Sbtw R []
参数：R : Type u_1；P : Type u_4。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
@[simp] lemma sbtw_nil : ([] : List P).Sbtw R := by
  simp [List.Sbtw]

variable {P}
/-
**List.wbtw_singleton** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ (R : Type u_1) {V : Type u_2} {P : Type u_4} [inst : Ring R] [inst_1 : P
artialOrder R] [inst_2 : AddCommGroup V]   [inst_3 : _root_.Module R V] [inst_4 
: AddTorsor V P] (p₁ : P), List.Wbtw R [p₁]
参数：R : Type u_1；p₁ : P。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
-/
@[simp] lemma wbtw_singleton (p₁ : P) : [p₁].Wbtw R := by
  simp [List.Wbtw]
/-
**List.sbtw_singleton** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ (R : Type u_1) {V : Type u_2} {P : Type u_4} [inst : Ring R] [inst_1 : P
artialOrder R] [inst_2 : AddCommGroup V]   [inst_3 : _root_.Module R V] [inst_4 
: AddTorsor V P] (p₁ : P), List.Sbtw R [p₁]
参数：R : Type u_1；p₁ : P。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
@[simp] lemma sbtw_singleton (p₁ : P) : [p₁].Sbtw R := by
  simp [List.Sbtw]
/-
**List.wbtw_pair** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ (R : Type u_1) {V : Type u_2} {P : Type u_4} [inst : Ring R] [inst_1 : P
artialOrder R] [inst_2 : AddCommGroup V]   [inst_3 : _root_.Module R V] [inst_4 
: AddTorsor V P] (p₁ p₂ : P), List.Wbtw R [p₁, p₂]
参数：R : Type u_1；p₁ p₂ : P。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
-/
@[simp] lemma wbtw_pair (p₁ p₂ : P) : [p₁, p₂].Wbtw R := by
  simp [List.Wbtw]
/-
**List.sbtw_pair** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ (R : Type u_1) {V : Type u_2} {P : Type u_4} [inst : Ring R] [inst_1 : P
artialOrder R] [inst_2 : AddCommGroup V]   [inst_3 : _root_.Module R V] [inst_4 
: AddTorsor V P] {p₁ p₂ : P}, List.Sbtw R [p₁, p₂] ↔ p₁ ≠ p₂
参数：R : Type u_1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma sbtw_pair {p₁ p₂ : P} : [p₁, p₂].Sbtw R ↔ p₁ ≠ p₂ := by
  simp [List.Sbtw]

variable {R}
/-
**List.wbtw_triple** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ {R : Type u_1} {V : Type u_2} {P : Type u_4} [inst : Ring R] [inst_1 : P
artialOrder R] [inst_2 : AddCommGroup V]   [inst_3 : _root_.Module R V] [inst_4 
: AddTorsor V P] {p₁ p₂ p₃ : P}, List.Wbtw R [p₁, p₂, p₃] ↔ Wbtw R p₁ p₂ p₃
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma wbtw_triple {p₁ p₂ p₃ : P} : [p₁, p₂, p₃].Wbtw R ↔ Wbtw R p₁ p₂ p₃ := by
  simp [List.Wbtw]

@[simp]
/-
**List.sbtw_triple** 是 Mathlib 中的一个引理，位于命名空间 `List`。
形式化陈述：sbtw_triple [IsOrderedRing R] {p₁ p₂ p₃ : P} : [p₁, p₂, p₃].Sbtw R ↔ Sbtw 
R p₁ p₂ p₃
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Sbtw.left_ne_right`：Sbtw.left_ne_right {x y z : P} (h : Sbtw R x y z) : 
x != z
-/
lemma sbtw_triple [IsOrderedRing R] {p₁ p₂ p₃ : P} : [p₁, p₂, p₃].Sbtw R ↔ Sbtw R p₁ p₂ p₃ := by
  simp only [List.Sbtw, wbtw_triple, ne_eq, pairwise_cons, mem_cons, not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, IsEmpty.forall_iff, implies_true, Pairwise.nil, and_self, and_true]
  exact ⟨fun ⟨hw, ⟨h₁₂, h₁₃⟩, h₂₃⟩ ↦ ⟨hw, Ne.symm h₁₂, h₂₃⟩,
         fun h ↦ ⟨h.1, ⟨h.2.1.symm, h.left_ne_right⟩, h.2.2⟩⟩
/-
**List.wbtw_four** 是 Mathlib 中的一个引理，位于命名空间 `List`。
形式化陈述：wbtw_four {p₁ p₂ p₃ p₄ : P} : [p₁, p₂, p₃, p₄].Wbtw R ↔ Wbtw R p₁ p₂ p₃ ∧ 
Wbtw R p₁ p₂ p₄ ∧ Wbtw R p₁ p₃ p₄ ∧ Wbtw R p₂ p₃ p₄
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
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma wbtw_four {p₁ p₂ p₃ p₄ : P} : [p₁, p₂, p₃, p₄].Wbtw R ↔
    Wbtw R p₁ p₂ p₃ ∧ Wbtw R p₁ p₂ p₄ ∧ Wbtw R p₁ p₃ p₄ ∧ Wbtw R p₂ p₃ p₄ := by
  simp [List.Wbtw, triplewise_cons, and_assoc]
/-
**List.sbtw_four** 是 Mathlib 中的一个引理，位于命名空间 `List`。
形式化陈述：sbtw_four [IsOrderedRing R] {p₁ p₂ p₃ p₄ : P} : [p₁, p₂, p₃, p₄].Sbtw R ↔ 
Sbtw R p₁ p₂ p₃ ∧ Sbtw R p₁ p₂ p₄ ∧ Sbtw R p₁ p₃ p₄ ∧ Sbtw R p₂ p₃ p₄
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `Aesop.BuiltinRules.not_intro`：∀ {P : Prop}, (P → False) → ¬P
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
-/
lemma sbtw_four [IsOrderedRing R] {p₁ p₂ p₃ p₄ : P} : [p₁, p₂, p₃, p₄].Sbtw R ↔
    Sbtw R p₁ p₂ p₃ ∧ Sbtw R p₁ p₂ p₄ ∧ Sbtw R p₁ p₃ p₄ ∧ Sbtw R p₂ p₃ p₄ := by
  simp [List.Sbtw, List.Wbtw, triplewise_cons, Sbtw]
  aesop
/-
**List.Sbtw.wbtw** 是 Mathlib 中的一个定理，位于命名空间 `List.Sbtw`。
形式化陈述：∀ {R : Type u_1} {V : Type u_2} {P : Type u_4} [inst : Ring R] [inst_1 : P
artialOrder R] [inst_2 : AddCommGroup V]   [inst_3 : _root_.Module R V] [inst_4 
: AddTorsor V P] {l : List P}, List.Sbtw R l → List.Wbtw R l
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
protected lemma Sbtw.wbtw {l : List P} (h : l.Sbtw R) : l.Wbtw R :=
  h.1
/-
**List.Sbtw.pairwise_ne** 是 Mathlib 中的一个定理，位于命名空间 `List.Sbtw`。
形式化陈述：∀ {R : Type u_1} {V : Type u_2} {P : Type u_4} [inst : Ring R] [inst_1 : P
artialOrder R] [inst_2 : AddCommGroup V]   [inst_3 : _root_.Module R V] [inst_4 
: AddTorsor V P] {l : List P},   List.Sbtw R l → List.Pairwise (fun x1 x2 => x1 
≠ x2) l
参数：fun x1 x2 => x1 ≠ x2。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
lemma Sbtw.pairwise_ne {l : List P} (h : l.Sbtw R) : l.Pairwise (· ≠ ·) :=
  h.2
/-
**List.sbtw_iff_triplewise_and_ne_pair** 是 Mathlib 中的一个引理，位于命名空间 `List`。
形式化陈述：sbtw_iff_triplewise_and_ne_pair [IsOrderedRing R] {l : List P} : l.Sbtw R 
↔ l.Triplewise (Sbtw R) ∧ forall a, l != [a, a]
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.Sbtw.eq_1`：∀ (R : Type u_1) {V : Type u_2} {P : Type u_4} [inst : R
ing R] [inst_1 : PartialOrder R] [inst_2 : AddCommGroup V]   [inst_3 : _root_.Mo
dule…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用引理 `List.wbtw_cons`：wbtw_cons {p : P} {l : List P} : (p :: l).Wbtw R ↔ l.Pai
rwise (Wbtw R p) ∧ l.Wbtw R
· 使用引理 `List.triplewise_cons`：triplewise_cons : (a :: l).Triplewise p ↔ l.Pairwi
se (p a) ∧ l.Triplewise p
· 使用定理 `List.pairwise_cons`：∀ {α : Type u} {R : α → α → Prop} {a : α} {l : List 
α},   List.Pairwise R (a :: l) ↔ (∀ a' ∈ l, R a a') ∧ List.Pairwise R l
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `List.Pairwise.imp`：∀ {α : Type u_1} {R S : α → α → Prop},   (∀ {a b : α}
, R a b → S a b) → ∀ {l : List α}, List.Pairwise R l → List.Pairwise S l
· 使用定理 `Sbtw.wbtw`：Sbtw.wbtw {x y z : P} (h : Sbtw R x y z) : Wbtw R x y z
· 使用定理 `List.Triplewise.imp`：∀ {α : Type u_1} {l : List α} {p q : α → α → α → Pr
op},   (∀ {a b c : α}, p a b c → q a b c) → List.Triplewise p l → List.Triplewis
e q l
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.mem_cons`：∀ {α : Type u_1} {b : α} {l : List α} {a : α}, a ∈ b :: l
 ↔ a = b ∨ a ∈ l
· 使用定理 `List.cons.injEq`：∀ {α : Type u} (head : α) (tail : List α) (head_1 : α) 
(tail_1 : List α),   (head :: tail = head_1 :: tail_1) = (head = head_1 ∧ tail =
 tail…
（共 35 条，此处仅展示前 30 条）
-/
lemma sbtw_iff_triplewise_and_ne_pair [IsOrderedRing R] {l : List P} :
    l.Sbtw R ↔ l.Triplewise (Sbtw R) ∧ ∀ a, l ≠ [a, a] := by
  rw [List.Sbtw]
  induction l with
  | nil => simp
  | cons head tail ih =>
    rw [wbtw_cons, triplewise_cons]
    refine ⟨fun h ↦ ?_,
            fun ⟨⟨hp, ht⟩, ha⟩ ↦ ⟨⟨hp.imp _root_.Sbtw.wbtw, ht.imp _root_.Sbtw.wbtw⟩, ?_⟩⟩
    · rcases h with ⟨⟨hp, ht⟩, hpne⟩
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · clear ih
        induction tail with
        | nil => simp
        | cons head2 tail ih' =>
          rw [pairwise_cons] at hp hpne hpne ⊢
          refine ⟨fun a ha ↦ ⟨hp.1 a ha, ?_⟩, ?_⟩
          · refine ⟨(hpne.1 head2 ?_).symm, hpne.2.1 a ha⟩
            simp
          · rw [wbtw_cons] at ht
            grind [List.pairwise_iff_forall_sublist]
      · rw [pairwise_cons] at hpne
        exact (ih.1 ⟨ht, hpne.2⟩).1
      · grind
    · have ht' : tail.Wbtw R := ht.imp _root_.Sbtw.wbtw
      simp only [ht', true_and, ht] at ih
      rw [pairwise_cons, ih]
      refine ⟨fun a ha' ↦ ?_, fun a ↦ ?_⟩
      · rintro rfl
        cases tail with
        | nil => simp at ha'
        | cons head2 tail =>
          rw [pairwise_cons] at hp
          rcases mem_cons.1 ha' with rfl | hat
          · cases tail with
            | nil => simp at ha
            | cons head3 tail => simpa using hp.1 head3
          · simpa using hp.1 head hat
      · rintro rfl
        simp at hp
/-
**List.sbtw_cons** 是 Mathlib 中的一个引理，位于命名空间 `List`。
形式化陈述：sbtw_cons [IsOrderedRing R] {p : P} {l : List P} : (p :: l).Sbtw R ↔ l.Pai
rwise (Sbtw R p) ∧ l.Sbtw R ∧ l != [p]
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `List.sbtw_iff_triplewise_and_ne_pair`：sbtw_iff_triplewise_and_ne_pair [I
sOrderedRing R] {l : List P} : l.Sbtw R ↔ l.Triplewise (Sbtw R) ∧ forall a, l !=
 [a, a]
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `not_exists`：∀ {α : Sort u_1} {p : α → Prop}, (¬∃ x, p x) ↔ ∀ (x : α), ¬p
 x
· 使用引理 `List.triplewise_cons`：triplewise_cons : (a :: l).Triplewise p ↔ l.Pairwi
se (p a) ∧ l.Triplewise p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `List.cons.injEq`：∀ {α : Type u} (head : α) (tail : List α) (head_1 : α) 
(tail_1 : List α),   (head :: tail = head_1 :: tail_1) = (head = head_1 ∧ tail =
 tail…
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self_and`：∀ {p q : Prop}, (p ↔ p ∧ q) ↔ p → q
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
-/
lemma sbtw_cons [IsOrderedRing R] {p : P} {l : List P} :
    (p :: l).Sbtw R ↔ l.Pairwise (Sbtw R p) ∧ l.Sbtw R ∧ l ≠ [p] := by
  rw [sbtw_iff_triplewise_and_ne_pair, ← not_exists, triplewise_cons]
  simp only [cons.injEq, exists_eq_left', and_assoc, and_congr_right_iff, ne_eq, and_congr_left_iff]
  intro hp hne
  rw [sbtw_iff_triplewise_and_ne_pair, iff_self_and, ← not_exists]
  rintro hl ⟨a, rfl⟩
  simp at hp

protected nonrec lemma Wbtw.map {l : List P} (h : l.Wbtw R) (f : P →ᵃ[R] P') : (l.map f).Wbtw R :=
  Triplewise.map (fun h ↦ Wbtw.map h f) h
/-
**List._root_.Function.Injective.list_wbtw_map_iff** 是 Mathlib 中的一个引理，位于命名空间 `Li
st`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.Function.Injective.list_wbtw_map_iff {l : List P} {f : P →ᵃ[R] P'}
    (hf : Function.Injective f) : (l.map f).Wbtw R ↔ l.Wbtw R :=
  ⟨fun h ↦ h.of_map hf.wbtw_map_iff.1, fun h ↦ h.map f⟩
/-
**List._root_.Function.Injective.list_sbtw_map_iff** 是 Mathlib 中的一个引理，位于命名空间 `Li
st`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.Function.Injective.list_sbtw_map_iff {l : List P} {f : P →ᵃ[R] P'}
    (hf : Function.Injective f) : (l.map f).Sbtw R ↔ l.Sbtw R := by
  rw [List.Sbtw, List.Sbtw, hf.list_wbtw_map_iff]
  refine ⟨fun ⟨hl, hp⟩ ↦ ⟨hl, hp.of_map _ ?_⟩, fun ⟨hl, hp⟩ ↦ ⟨hl, hp.map _ ?_⟩⟩ <;>
    simp [hf.ne_iff]
/-
**List._root_.AffineEquiv.list_wbtw_map_iff** 是 Mathlib 中的一个引理，位于命名空间 `List`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.AffineEquiv.list_wbtw_map_iff {l : List P} (f : P ≃ᵃ[R] P') :
    (l.map f).Wbtw R ↔ l.Wbtw R := by
  have hf : Function.Injective f.toAffineMap := f.injective
  apply hf.list_wbtw_map_iff
/-
**List._root_.AffineEquiv.list_sbtw_map_iff** 是 Mathlib 中的一个引理，位于命名空间 `List`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.AffineEquiv.list_sbtw_map_iff {l : List P} (f : P ≃ᵃ[R] P') :
    (l.map f).Sbtw R ↔ l.Sbtw R := by
  have hf : Function.Injective f.toAffineMap := f.injective
  apply hf.list_sbtw_map_iff

end OrderedRing

section LinearOrderedField

variable [Field R] [LinearOrder R] [IsStrictOrderedRing R]
  [AddCommGroup V] [Module R V] [AddTorsor V P] {x y z : P}
variable {R}

/-
**List.SortedLE.wbtw** 是 Mathlib 中的一个定理，位于命名空间 `List.SortedLE`。
形式化陈述：∀ {R : Type u_1} [inst : Field R] [inst_1 : LinearOrder R] [IsStrictOrdere
dRing R] {l : List R},   l.SortedLE → List.Wbtw R l
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.Wbtw.eq_1`：∀ (R : Type u_1) {V : Type u_2} {P : Type u_4} [inst : R
ing R] [inst_1 : PartialOrder R] [inst_2 : AddCommGroup V]   [inst_3 : _root_.Mo
dule…
· 使用引理 `List.triplewise_iff_getElem`：triplewise_iff_getElem : l.Triplewise p ↔ f
orall i j k (hij : i < j) (hjk : j < k) (hk : k < l.length), p l[i] l[j] l[k]
· 使用引理 `Wbtw.of_le_of_le`：Wbtw.of_le_of_le {x y z : R} (hxy : x <= y) (hyz : y <
= z) : Wbtw R x y z
· 使用定理 `List.SortedLE.getElem_le_getElem_of_le`：∀ {α : Type u_1} {l : List α} [i
nst : Preorder α],   l.SortedLE → ∀ ⦃i j : ℕ⦄ ⦃hi : i < l.length⦄ ⦃hj : j < l.le
ngth⦄, i ≤ j → l[i] ≤ l[j]
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
lemma SortedLE.wbtw {l : List R} (h : l.SortedLE) : l.Wbtw R := by
  rw [List.Wbtw, List.triplewise_iff_getElem]
  intro i j k hij hjk hk
  exact Wbtw.of_le_of_le (h.getElem_le_getElem_of_le hij.le) (h.getElem_le_getElem_of_le hjk.le)
/-
**List.SortedLT.sbtw** 是 Mathlib 中的一个定理，位于命名空间 `List.SortedLT`。
形式化陈述：∀ {R : Type u_1} [inst : Field R] [inst_1 : LinearOrder R] [IsStrictOrdere
dRing R] {l : List R},   l.SortedLT → List.Sbtw R l
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.SortedLE.wbtw`：∀ {R : Type u_1} [inst : Field R] [inst_1 : LinearOr
der R] [IsStrictOrderedRing R] {l : List R},   l.SortedLE → List.Wbtw R l
· 使用定理 `List.SortedLT.sortedLE`：∀ {α : Type u_1} [inst : Preorder α] {l : List α
}, l.SortedLT → l.SortedLE
· 使用定理 `List.SortedLT.nodup`：∀ {α : Type u_1} {l : List α} [inst : Preorder α], 
l.SortedLT → l.Nodup
-/
lemma SortedLT.sbtw {l : List R} (h : l.SortedLT) : l.Sbtw R :=
  ⟨h.sortedLE.wbtw, h.nodup⟩

set_option backward.isDefEq.respectTransparency false in
/-
**List.exists_map_eq_of_sorted_nonempty_iff_wbtw** 是 Mathlib 中的一个引理，位于命名空间 `List
`。
形式化陈述：exists_map_eq_of_sorted_nonempty_iff_wbtw {l : List P} (hl : l != []) : (e
xists l' : List R, l'.SortedLE ∧ l'.map (lineMap (l.head hl) (l.getLast hl)) = l
) ↔ l.Wbtw R
参数：hl : l != []。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.head`：head?_flatten_replicate {n : Nat} (h : n != 0) (l : List α) :
 (List.replicate n l).flatten.head? = l.head?
· 使用定理 `List.getLast`：getLast?_flatten_replicate {n : Nat} (h : n != 0) (l : Lis
t α) : (List.replicate n l).flatten.getLast? = l.getLast?
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.Wbtw.map`：∀ {R : Type u_1} {V : Type u_2} {V' : Type u_3} {P : Type
 u_4} {P' : Type u_5} [inst : Ring R] [inst_1 : PartialOrder R]   [inst_2 : AddC
omm…
· 使用定理 `List.SortedLE.wbtw`：∀ {R : Type u_1} [inst : Field R] [inst_1 : LinearOr
der R] [IsStrictOrderedRing R] {l : List R},   l.SortedLE → List.Wbtw R l
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `List.head.congr_simp`：∀ {α : Type u} (as as_1 : List α) (e_as : as = as_
1) (a : as ≠ []), as.head a = as_1.head ⋯
· 使用定理 `List.getLast.congr_simp`：∀ {α : Type u} (as as_1 : List α) (e_as : as = 
as_1) (a : as ≠ []), as.getLast a = as_1.getLast ⋯
· 使用定理 `AffineMap.lineMap_same`：lineMap_same (p : P1) : lineMap p p = const k k 
p
· 使用定理 `List.map_cons`：∀ {α : Type u} {β : Type v} {f : α → β} {a : α} {l : List
 α}, List.map f (a :: l) = f a :: List.map f l
· 使用定理 `List.map_nil`：∀ {α : Type u} {β : Type v} {f : α → β}, List.map f [] = [
]
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用引理 `List.wbtw_cons`：wbtw_cons {p : P} {l : List P} : (p :: l).Wbtw R ↔ l.Pai
rwise (Wbtw R p) ∧ l.Wbtw R
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `List.getLast_cons`：∀ {α : Type u_1} {a : α} {l : List α} (h : l ≠ []), (
a :: l).getLast ⋯ = l.getLast h
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用定理 `AffineMap.lineMap_apply_zero`：lineMap_apply_zero (p₀ p₁ : P1) : lineMap 
p₀ p₁ (0 : k) = p₀
· 使用定理 `AffineMap.lineMap_apply_one`：lineMap_apply_one (p₀ p₁ : P1) : lineMap p₀
 p₁ (1 : k) = p₁
（共 109 条，此处仅展示前 30 条）
-/
lemma exists_map_eq_of_sorted_nonempty_iff_wbtw {l : List P} (hl : l ≠ []) :
    (∃ l' : List R, l'.SortedLE ∧ l'.map (lineMap (l.head hl) (l.getLast hl)) = l) ↔
      l.Wbtw R := by
  refine ⟨fun ⟨l', hl's, hl'l⟩ ↦ ?_, fun h ↦ ?_⟩
  · rw [← hl'l]
    exact Wbtw.map hl's.wbtw _
  · suffices ∃ l' : List R, (∀ a ∈ l', 0 ≤ a) ∧ l'.SortedLE ∧
        l'.map (lineMap (l.head hl) (l.getLast hl)) = l by
      rcases this with ⟨l', -, hl'⟩
      exact ⟨l', hl'⟩
    induction l with
    | nil => simp at hl
    | cons head tail ih =>
      by_cases ht : tail = []
      · refine ⟨[0], ?_⟩
        simp [ht, sortedLE_iff_pairwise]
      · rw [wbtw_cons] at h
        replace ih := ih ht h.2
        rcases ih with ⟨l'', hl''0, hl''s, hl''⟩
        simp only [head_cons, getLast_cons ht]
        cases tail with
        | nil => simp at ht
        | cons head2 tail =>
          by_cases ht2 : tail = []
          · exact ⟨[0, 1], by simp [ht2, sortedLE_iff_pairwise]⟩
          · simp only [head_cons, getLast_cons ht2] at hl'' ⊢
            rw [pairwise_cons] at h
            have hw := h.1.1 _ (getLast_mem ht2)
            rcases hw with ⟨r, ⟨hr0, hr1⟩, rfl⟩
            refine ⟨0 :: l''.map fun x ↦ r + (1 - r) * x, ?_, ?_, ?_⟩
            · simp only [mem_cons, mem_map, forall_eq_or_imp, le_refl, forall_exists_index,
                and_imp, forall_apply_eq_imp_iff₂, true_and]
              intro a ha
              have := hl''0 a ha
              nlinarith
            · simp only [sortedLE_iff_pairwise, pairwise_cons, mem_map,
                forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
              refine ⟨?_, ?_⟩
              · intro a ha
                have := hl''0 a ha
                nlinarith
              · refine hl''s.pairwise.map _ fun a b hab ↦ ?_
                gcongr
            · simp only [map_cons, lineMap_apply_zero, map_map, ← hl'', cons.injEq,
                map_inj_left, Function.comp_apply, lineMap_lineMap_left, lineMap_eq_lineMap_iff,
                true_and]
              ring_nf
              simp

set_option backward.isDefEq.respectTransparency false in
/-
**List.exists_map_eq_of_sorted_iff_wbtw** 是 Mathlib 中的一个引理，位于命名空间 `List`。
形式化陈述：exists_map_eq_of_sorted_iff_wbtw {l : List P} : (exists p₁ p₂ : P, exists 
l' : List R, l'.SortedLE ∧ l'.map (lineMap p₁ p₂) = l) ↔ l.Wbtw R
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.Wbtw.map`：∀ {R : Type u_1} {V : Type u_2} {V' : Type u_3} {P : Type
 u_4} {P' : Type u_5} [inst : Ring R] [inst_1 : PartialOrder R]   [inst_2 : AddC
omm…
· 使用定理 `List.SortedLE.wbtw`：∀ {R : Type u_1} [inst : Field R] [inst_1 : LinearOr
der R] [IsStrictOrderedRing R] {l : List R},   l.SortedLE → List.Wbtw R l
· 使用定理 `AddTorsor.nonempty`：∀ {G : outParam (Type u_1)} {P : Type u_2} {inst : A
ddGroup G} [self : AddTorsor G P], Nonempty P
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `AffineMap.lineMap_same`：lineMap_same (p : P1) : lineMap p p = const k k 
p
· 使用定理 `List.map_nil`：∀ {α : Type u} {β : Type v} {f : α → β}, List.map f [] = [
]
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `List.head`：head?_flatten_replicate {n : Nat} (h : n != 0) (l : List α) :
 (List.replicate n l).flatten.head? = l.head?
· 使用定理 `List.getLast`：getLast?_flatten_replicate {n : Nat} (h : n != 0) (l : Lis
t α) : (List.replicate n l).flatten.getLast? = l.getLast?
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `List.exists_map_eq_of_sorted_nonempty_iff_wbtw`：exists_map_eq_of_sorted_
nonempty_iff_wbtw {l : List P} (hl : l != []) : (exists l' : List R, l'.SortedLE
 ∧ l'.map (lineMap (l.head hl) (l.ge…
-/
lemma exists_map_eq_of_sorted_iff_wbtw {l : List P} :
    (∃ p₁ p₂ : P, ∃ l' : List R, l'.SortedLE ∧ l'.map (lineMap p₁ p₂) = l) ↔ l.Wbtw R := by
  refine ⟨fun ⟨p₁, p₂, l', hl's, hl'l⟩ ↦ ?_, fun h ↦ ?_⟩
  · subst hl'l
    exact Wbtw.map hl's.wbtw _
  · by_cases hl : l = []
    · exact ⟨AddTorsor.nonempty.some, AddTorsor.nonempty.some, [], by
        simp [hl, sortedLE_iff_pairwise]⟩
    · exact ⟨l.head hl, l.getLast hl, (exists_map_eq_of_sorted_nonempty_iff_wbtw hl).2 h⟩

set_option backward.isDefEq.respectTransparency false in
/-
**List.exists_map_eq_of_sorted_nonempty_iff_sbtw** 是 Mathlib 中的一个引理，位于命名空间 `List
`。
形式化陈述：exists_map_eq_of_sorted_nonempty_iff_sbtw {l : List P} (hl : l != []) : (e
xists l' : List R, l'.SortedLT ∧ l'.map (lineMap (l.head hl) (l.getLast hl)) = l
 ∧ (l.length = 1 ∨ l.head hl != l.getLast hl)) ↔ l.Sbtw R
参数：hl : l != []。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.head`：head?_flatten_replicate {n : Nat} (h : n != 0) (l : List α) :
 (List.replicate n l).flatten.head? = l.head?
· 使用定理 `List.getLast`：getLast?_flatten_replicate {n : Nat} (h : n != 0) (l : Lis
t α) : (List.replicate n l).flatten.getLast? = l.getLast?
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `List.exists_map_eq_of_sorted_nonempty_iff_wbtw`：exists_map_eq_of_sorted_
nonempty_iff_wbtw {l : List P} (hl : l != []) : (exists l' : List R, l'.SortedLE
 ∧ l'.map (lineMap (l.head hl) (l.ge…
· 使用定理 `List.Pairwise.sortedLE`：∀ {α : Type u_1} {l : List α} [inst : Preorder α
], List.Pairwise (fun x1 x2 => x1 ≤ x2) l → l.SortedLE
· 使用定理 `List.Pairwise.imp`：∀ {α : Type u_1} {R S : α → α → Prop},   (∀ {a b : α}
, R a b → S a b) → ∀ {l : List α}, List.Pairwise R l → List.Pairwise S l
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `List.SortedLT.pairwise`：∀ {α : Type u_1} {l : List α} [inst : Preorder α
], l.SortedLT → List.Pairwise (fun x1 x2 => x1 < x2) l
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.Pairwise.map`：∀ {β : Type u_1} {α : Type u_2} {R : α → α → Prop} {l
 : List α} {S : β → β → Prop} (f : α → β),   (∀ (a b : α), R a b → S (f a) (f b)
) → Lis…
· 使用定理 `Function.Injective.ne`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, Func
tion.Injective f → ∀ {a₁ a₂ : α}, a₁ ≠ a₂ → f a₁ ≠ f a₂
· 使用定理 `AffineMap.lineMap_injective`：lineMap_injective [IsDomain k] [IsTorsionFr
ee k V1] {p₀ p₁ : P1} (h : p₀ != p₁) : Function.Injective (lineMap p₀ p₁ : k -> 
P1)
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `List.Sbtw.eq_1`：∀ (R : Type u_1) {V : Type u_2} {P : Type u_4} [inst : R
ing R] [inst_1 : PartialOrder R] [inst_2 : AddCommGroup V]   [inst_3 : _root_.Mo
dule…
· 使用定理 `List.Pairwise.of_map`：∀ {β : Type u_1} {α : Type u_2} {R : α → α → Prop}
 {l : List α} {S : β → β → Prop} (f : α → β),   (∀ (a b : α), S (f a) (f b) → R 
a b) → Lis…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `List.Pairwise.sortedLT`：∀ {α : Type u_1} {l : List α} [inst : Preorder α
], List.Pairwise (fun x1 x2 => x1 < x2) l → l.SortedLT
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `lt_iff_le_and_ne`：lt_iff_le_and_ne : a < b ↔ a <= b ∧ a != b
· 使用定理 `List.pairwise_and_iff`：∀ {α : Type u_1} {R : α → α → Prop} {l : List α} 
{S : α → α → Prop},   List.Pairwise (fun a b => R a b ∧ S a b) l ↔ List.Pairwise
 R l ∧ List…
· 使用定理 `List.SortedLE.pairwise`：∀ {α : Type u_1} {l : List α} [inst : Preorder α
], l.SortedLE → List.Pairwise (fun x1 x2 => x1 ≤ x2) l
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
（共 46 条，此处仅展示前 30 条）
-/
lemma exists_map_eq_of_sorted_nonempty_iff_sbtw {l : List P} (hl : l ≠ []) :
    (∃ l' : List R, l'.SortedLT ∧ l'.map (lineMap (l.head hl) (l.getLast hl)) = l ∧
      (l.length = 1 ∨ l.head hl ≠ l.getLast hl)) ↔ l.Sbtw R := by
  refine ⟨fun ⟨l', hl's, hl'l, hla⟩ ↦
            ⟨(exists_map_eq_of_sorted_nonempty_iff_wbtw hl).1
            ⟨l', (hl's.pairwise.imp LT.lt.le).sortedLE, hl'l⟩, ?_⟩,
          fun h ↦ ?_⟩
  · rw [← hl'l]
    rcases hla with hla | hla
    · grind [List.pairwise_iff_forall_sublist]
    · exact (hl's.pairwise.imp LT.lt.ne).map _ fun _ _ ↦ (lineMap_injective _ hla).ne
  · rw [List.Sbtw, ← exists_map_eq_of_sorted_nonempty_iff_wbtw hl] at h
    rcases h with ⟨⟨l', hl's, hl'l⟩, hp⟩
    refine ⟨l', ?_, hl'l, ?_⟩
    · rw [← hl'l] at hp
      have hp' : l'.Pairwise (· ≠ ·) := hp.of_map _ (by simp)
      exact ((pairwise_and_iff.2 ⟨hl's.pairwise, hp'⟩).imp lt_iff_le_and_ne.2).sortedLT
    · cases l with
      | nil => simp at hl
      | cons head tail =>
        simp only [length_cons, add_eq_right, length_eq_zero_iff, head_cons]
        cases tail with
        | nil => simp
        | cons head2 tail =>
          simp only [reduceCtorEq, false_or]
          rw [pairwise_cons] at hp
          refine hp.1 ((head :: head2 :: tail).getLast hl) ?_
          simp

set_option backward.isDefEq.respectTransparency false in
/-
**List.exists_map_eq_of_sorted_iff_sbtw** 是 Mathlib 中的一个引理，位于命名空间 `List`。
形式化陈述：exists_map_eq_of_sorted_iff_sbtw [Nontrivial P] {l : List P} : (exists p₁ 
p₂ : P, p₁ != p₂ ∧ exists l' : List R, l'.SortedLT ∧ l'.map (lineMap p₁ p₂) = l)
 ↔ l.Sbtw R
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.Injective.list_sbtw_map_iff`：∀ {R : Type u_1} {V : Type u_2} {V
' : Type u_3} {P : Type u_4} {P' : Type u_5} [inst : Ring R] [inst_1 : PartialOr
der R]   [inst_2 : AddComm…
· 使用定理 `AffineMap.lineMap_injective`：lineMap_injective [IsDomain k] [IsTorsionFr
ee k V1] {p₀ p₁ : P1} (h : p₀ != p₁) : Function.Injective (lineMap p₀ p₁ : k -> 
P1)
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `List.SortedLT.sbtw`：∀ {R : Type u_1} [inst : Field R] [inst_1 : LinearOr
der R] [IsStrictOrderedRing R] {l : List R},   l.SortedLT → List.Sbtw R l
· 使用定理 `exists_pair_ne`：exists_pair_ne (α : Type*) [Nontrivial α] : exists x y :
 α, x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `List.length_eq_one_iff`：∀ {α : Type u_1} {l : List α}, l.length = 1 ↔ ∃ 
a, l = [a]
· 使用定理 `exists_ne`：exists_ne [Nontrivial α] (x : α) : exists y, y != x
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `List.map_cons`：∀ {α : Type u} {β : Type v} {f : α → β} {a : α} {l : List
 α}, List.map f (a :: l) = f a :: List.map f l
· 使用定理 `AffineMap.lineMap_apply_zero`：lineMap_apply_zero (p₀ p₁ : P1) : lineMap 
p₀ p₁ (0 : k) = p₀
· 使用定理 `List.map_nil`：∀ {α : Type u} {β : Type v} {f : α → β}, List.map f [] = [
]
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.head`：head?_flatten_replicate {n : Nat} (h : n != 0) (l : List α) :
 (List.replicate n l).flatten.head? = l.head?
· 使用定理 `List.getLast`：getLast?_flatten_replicate {n : Nat} (h : n != 0) (l : Lis
t α) : (List.replicate n l).flatten.getLast? = l.getLast?
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
（共 31 条，此处仅展示前 30 条）
-/
lemma exists_map_eq_of_sorted_iff_sbtw [Nontrivial P] {l : List P} :
    (∃ p₁ p₂ : P, p₁ ≠ p₂ ∧ ∃ l' : List R, l'.SortedLT ∧ l'.map (lineMap p₁ p₂) = l) ↔
      l.Sbtw R := by
  refine ⟨fun ⟨p₁, p₂, hp₁p₂, l', hl's, hl'l⟩ ↦ ?_, fun h ↦ ?_⟩
  · subst hl'l
    rw [(lineMap_injective _ hp₁p₂).list_sbtw_map_iff]
    exact hl's.sbtw
  · by_cases hl : l = []
    · rcases exists_pair_ne P with ⟨p₁, p₂, hp₁p₂⟩
      exact ⟨p₁, p₂, hp₁p₂, by simp [hl, sortedLT_iff_pairwise]⟩
    · by_cases hlen : l.length = 1
      · rw [length_eq_one_iff] at hlen
        rcases hlen with ⟨p₁, rfl⟩
        rcases exists_ne p₁ with ⟨p₂, hp₂p₁⟩
        exact ⟨p₁, p₂, hp₂p₁.symm, [0], by simp [sortedLT_iff_pairwise]⟩
      · refine ⟨l.head hl, l.getLast hl, ?_⟩
        rw [← exists_map_eq_of_sorted_nonempty_iff_sbtw hl] at h
        simp only [hlen, false_or] at h
        rcases h with ⟨l', hl's, hl'l, hl⟩
        exact ⟨hl, l', hl's, hl'l⟩

end LinearOrderedField

end List

