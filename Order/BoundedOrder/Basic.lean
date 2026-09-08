/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
module

public import Mathlib.Order.Max
public import Mathlib.Order.ULift
public import Mathlib.Tactic.ByCases
public import Mathlib.Tactic.Finiteness.Attr

/-!
# ⊤ and ⊥, bounded lattices and variants

This file defines top and bottom elements (greatest and least elements) of a type, the bounded
variants of different kinds of lattices, sets up the typeclass hierarchy between them and provides
instances for `Prop` and `fun`.

## Main declarations

* `<Top/Bot> α`: Typeclasses to declare the `⊤`/`⊥` notation.
* `Order<Top/Bot> α`: Order with a top/bottom element.
* `BoundedOrder α`: Order with a top and bottom element.

-/

@[expose] public section

assert_not_exists Monotone

universe u v

variable {α : Type u} {β : Type v}

/-! ### Top, bottom element -/

/-- An order is an `OrderTop` if it has a greatest element.
We state this using a data mixin, holding the value of `⊤` and the greatest element constraint. -/
/-
**OrderTop** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(α : Type u) → [LE α] → Type u
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An order is an `OrderTop` if it has a greatest element.
We state this using a data mixin, holding the value of `⊤` and the greatest elem
ent constraint.
-/
class OrderTop (α : Type u) [LE α] extends Top α where
  /-- `⊤` is the greatest element -/
  le_top : ∀ a : α, a ≤ ⊤

/-- An order is an `OrderBot` if it has a least element.
We state this using a data mixin, holding the value of `⊥` and the least element constraint. -/
/-
**OrderBot** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(α : Type u) → [LE α] → Type u
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An order is an `OrderBot` if it has a least element.
We state this using a data mixin, holding the value of `⊥` and the least element
 constraint.
-/
@[to_dual] class OrderBot (α : Type u) [LE α] extends Bot α where
  /-- `⊥` is the least element -/
  bot_le : ∀ a : α, ⊥ ≤ a

section OrderTop

/-- An order is (noncomputably) either an `OrderTop` or a `NoTopOrder`. Use as
`cases topOrderOrNoTopOrder α`. -/
@[to_dual /-- An order is (noncomputably) either an `OrderBot` or a `NoBotOrder`. Use as
`cases botOrderOrNoBotOrder α`. -/]
/-
**topOrderOrNoTopOrder** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：topOrderOrNoTopOrder (α : Type*) [LE α] : OrderTop α oplus' NoTopOrder α
参数：α : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable def topOrderOrNoTopOrder (α : Type*) [LE α] : OrderTop α ⊕' NoTopOrder α := by
  by_cases! H : ∀ a : α, ∃ b, ¬b ≤ a
  · exact PSum.inr ⟨H⟩
  · letI : Top α := ⟨Classical.choose H⟩
    exact PSum.inl ⟨Classical.choose_spec H⟩

section ite

variable [Top α] {p : Prop} [Decidable p]

@[to_dual (attr := aesop (rule_sets := [finiteness]) unsafe 70% apply)]
/-
**dite_ne_top** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dite_ne_top {a : p -> α} {b : ¬p -> α} (ha : forall h, a h != ⊤) (hb : for
all h, b h != ⊤) : (if h : p then a h else b h) != ⊤
参数：ha : forall h, a h != ⊤；hb : forall h, b h != ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
-/
theorem dite_ne_top {a : p → α} {b : ¬p → α} (ha : ∀ h, a h ≠ ⊤) (hb : ∀ h, b h ≠ ⊤) :
    (if h : p then a h else b h) ≠ ⊤ := by
  split <;> solve_by_elim

@[to_dual (attr := aesop (rule_sets := [finiteness]) unsafe 70% apply)]
/-
**ite_ne_top** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ite_ne_top {a b : α} (ha : p -> a != ⊤) (hb : ¬p -> b != ⊤) : (if p then a
 else b) != ⊤
参数：ha : p -> a != ⊤；hb : ¬p -> b != ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dite_ne_top`：dite_ne_top {a : p -> α} {b : ¬p -> α} (ha : forall h, a h 
!= ⊤) (hb : forall h, b h != ⊤) : (if h : p then a h else b h) != ⊤
-/
theorem ite_ne_top {a b : α} (ha : p → a ≠ ⊤) (hb : ¬p → b ≠ ⊤) :
    (if p then a else b) ≠ ⊤ :=
  dite_ne_top ha hb

end ite

section LE

variable [LE α] [OrderTop α] {a : α}

@[to_dual (attr := simp) bot_le]
/-
**le_top** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_top : a <= ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderTop.le_top`：∀ {α : Type u} {inst : LE α} [self : OrderTop α] (a : α
), a ≤ ⊤
-/
theorem le_top : a ≤ ⊤ :=
  OrderTop.le_top a

@[to_dual (attr := simp)]
/-
**isTop_top** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isTop_top : IsTop (⊤ : α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_top`：le_top : a <= ⊤
-/
theorem isTop_top : IsTop (⊤ : α) := fun _ => le_top

end LE

/-- A top element can be replaced with `⊤`.

Prefer `IsTop.eq_top` if `α` already has a top element. -/
@[to_dual (attr := elab_as_elim) /-- A bottom element can be replaced with `⊥`.

Prefer `IsBot.eq_bot` if `α` already has a bottom element. -/]
/-
**IsTop.rec** 是 Mathlib 中的一个定义，位于命名空间 `IsTop`。
形式化陈述：{α : Type u} →   [inst : LE α] →     {motive : (x : α) → IsTop x → Sort u_
1} →       ([inst_1 : OrderTop α] → motive ⊤ ⋯) → (x : α) → (hx : IsTop x) → mot
ive x hx
参数：x : α；[inst_1 : OrderTop α] → motive ⊤ ⋯；x : α；hx : IsTop x。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `isTop_top`：isTop_top : IsTop (⊤ : α)
-/
protected def IsTop.rec [LE α] {motive : (x : α) → IsTop x → Sort*}
    (top : ∀ [OrderTop α], motive ⊤ isTop_top) (x : α) (hx : IsTop x) : motive x hx :=
  @top { top := x, le_top a := hx a }

section Preorder

variable [Preorder α] [OrderTop α] {a b : α}

@[to_dual (attr := simp)]
/-
**isMax_top** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isMax_top : IsMax (⊤ : α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTop.isMax`：∀ {α : Type u_1} [inst : LE α] {a : α}, IsTop a → IsMax a
· 使用定理 `isTop_top`：isTop_top : IsTop (⊤ : α)
-/
theorem isMax_top : IsMax (⊤ : α) :=
  isTop_top.isMax

@[to_dual (attr := simp) not_lt_bot]
/-
**not_top_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：not_top_lt : ¬⊤ < a
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsMax.not_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, IsMax a → 
¬a < b
· 使用定理 `isMax_top`：isMax_top : IsMax (⊤ : α)
-/
theorem not_top_lt : ¬⊤ < a :=
  isMax_top.not_lt

@[to_dual (attr := simp) not_covBy_bot]
/-
**not_top_covBy** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：not_top_covBy : ¬⊤ ⋖ a
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `not_top_lt`：not_top_lt : ¬⊤ < a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem not_top_covBy : ¬⊤ ⋖ a :=
  fun h ↦ not_top_lt h.1

@[to_dual ne_bot_of_gt]
/-
**ne_top_of_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ne_top_of_lt (h : a < b) : a != ⊤
参数：h : a < b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `le_top`：le_top : a <= ⊤
-/
theorem ne_top_of_lt (h : a < b) : a ≠ ⊤ :=
  (h.trans_le le_top).ne

@[to_dual] alias LT.lt.ne_top := ne_top_of_lt
/-
**lt_top_of_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u} [inst : Preorder α] [inst_1 : OrderTop α] {a b : α}, a < b 
→ a < ⊤
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用定理 `le_top`：le_top : a <= ⊤
-/
@[to_dual bot_lt_of_lt] theorem lt_top_of_lt (h : a < b) : a < ⊤ :=
  lt_of_lt_of_le h le_top

@[to_dual bot_lt] alias LT.lt.lt_top := lt_top_of_lt

@[to_dual bot_lt_iff_not_le_bot]
/-
**lt_top_iff_not_top_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lt_top_iff_not_top_le : a < ⊤ ↔ ¬ ⊤ <= a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem lt_top_iff_not_top_le : a < ⊤ ↔ ¬ ⊤ ≤ a := by
  simp [lt_iff_le_not_ge]

@[to_dual not_isMin_iff_bot_lt]
/-
**not_isMax_iff_lt_top** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：not_isMax_iff_lt_top : ¬ IsMax a ↔ a < ⊤
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `not_isMax_iff`：∀ {α : Type u_1} [inst : Preorder α] {a : α}, ¬IsMax a ↔ 
∃ b, a < b
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `le_top`：le_top : a <= ⊤
-/
theorem not_isMax_iff_lt_top : ¬ IsMax a ↔ a < ⊤ := by
  rw [not_isMax_iff]
  exact ⟨fun ⟨b, hb⟩ ↦ hb.trans_le le_top, fun h ↦ ⟨⊤, h⟩⟩

attribute [aesop (rule_sets := [finiteness]) unsafe 20%] ne_top_of_lt
-- would have been better to implement this as a "safe" "forward" rule, why doesn't this work?
-- attribute [aesop (rule_sets := [finiteness]) safe forward] ne_top_of_lt

end Preorder

variable [PartialOrder α] [OrderTop α] [Preorder β] {a b : α}

@[to_dual (attr := simp)]
/-
**isMax_iff_eq_top** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isMax_iff_eq_top : IsMax a ↔ a = ⊤
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsMax.eq_of_le`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, IsMa
x a → a ≤ b → a = b
· 使用定理 `le_top`：le_top : a <= ⊤
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem isMax_iff_eq_top : IsMax a ↔ a = ⊤ :=
  ⟨fun h => h.eq_of_le le_top, fun h _ _ => h.symm ▸ le_top⟩

@[to_dual (attr := simp)]
/-
**isTop_iff_eq_top** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isTop_iff_eq_top : IsTop a ↔ a = ⊤
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsMax.eq_of_le`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, IsMa
x a → a ≤ b → a = b
· 使用定理 `IsTop.isMax`：∀ {α : Type u_1} [inst : LE α] {a : α}, IsTop a → IsMax a
· 使用定理 `le_top`：le_top : a <= ⊤
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem isTop_iff_eq_top : IsTop a ↔ a = ⊤ :=
  ⟨fun h => h.isMax.eq_of_le le_top, fun h _ => h.symm ▸ le_top⟩

@[to_dual]
/-
**not_isMax_iff_ne_top** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：not_isMax_iff_ne_top : ¬IsMax a ↔ a != ⊤
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `isMax_iff_eq_top`：isMax_iff_eq_top : IsMax a ↔ a = ⊤
-/
theorem not_isMax_iff_ne_top : ¬IsMax a ↔ a ≠ ⊤ :=
  isMax_iff_eq_top.not

@[to_dual]
/-
**not_isTop_iff_ne_top** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：not_isTop_iff_ne_top : ¬IsTop a ↔ a != ⊤
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `isTop_iff_eq_top`：isTop_iff_eq_top : IsTop a ↔ a = ⊤
-/
theorem not_isTop_iff_ne_top : ¬IsTop a ↔ a ≠ ⊤ :=
  isTop_iff_eq_top.not

@[to_dual]
alias ⟨IsMax.eq_top, _⟩ := isMax_iff_eq_top

@[to_dual]
alias ⟨IsTop.eq_top, _⟩ := isTop_iff_eq_top

@[to_dual (attr := simp) le_bot_iff]
/-
**top_le_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：top_le_iff : ⊤ <= a ↔ a = ⊤
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.ge_iff_eq`：ge_iff_eq (h : a <= b) : b <= a ↔ a = b
· 使用定理 `le_top`：le_top : a <= ⊤
-/
theorem top_le_iff : ⊤ ≤ a ↔ a = ⊤ :=
  le_top.ge_iff_eq

-- This tells grind that to prove `a = ⊤` it suffices to prove `⊤ ≤ a`.
@[to_dual (attr := grind ←=, grind →)]
/-
**top_unique** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：top_unique (h : ⊤ <= a) : a = ⊤
参数：h : ⊤ <= a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `le_top`：le_top : a <= ⊤
-/
theorem top_unique (h : ⊤ ≤ a) : a = ⊤ :=
  le_top.antisymm h

@[to_dual]
/-
**eq_top_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：eq_top_iff : a = ⊤ ↔ ⊤ <= a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `top_le_iff`：top_le_iff : ⊤ <= a ↔ a = ⊤
-/
theorem eq_top_iff : a = ⊤ ↔ ⊤ ≤ a :=
  top_le_iff.symm

@[to_dual]
/-
**eq_top_mono** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：eq_top_mono (h : a <= b) (h₂ : a = ⊤) : b = ⊤
参数：h : a <= b；h₂ : a = ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `top_unique`：top_unique (h : ⊤ <= a) : a = ⊤
-/
theorem eq_top_mono (h : a ≤ b) (h₂ : a = ⊤) : b = ⊤ :=
  top_unique <| h₂ ▸ h

@[to_dual bot_lt_iff_ne_bot]
/-
**lt_top_iff_ne_top** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lt_top_iff_ne_top : a < ⊤ ↔ a != ⊤
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.lt_iff_ne`：lt_iff_ne (h : a <= b) : a < b ↔ a != b
· 使用定理 `le_top`：le_top : a <= ⊤
-/
theorem lt_top_iff_ne_top : a < ⊤ ↔ a ≠ ⊤ :=
  le_top.lt_iff_ne

@[to_dual (attr := simp) not_bot_lt_iff]
/-
**not_lt_top_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：not_lt_top_iff : ¬a < ⊤ ↔ a = ⊤
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.not_left`：Iff.not_left (h : a ↔ ¬b) : ¬a ↔ b
· 使用定理 `lt_top_iff_ne_top`：lt_top_iff_ne_top : a < ⊤ ↔ a != ⊤
-/
theorem not_lt_top_iff : ¬a < ⊤ ↔ a = ⊤ :=
  lt_top_iff_ne_top.not_left

@[to_dual eq_bot_or_bot_lt]
/-
**eq_top_or_lt_top** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：eq_top_or_lt_top (a : α) : a = ⊤ ∨ a < ⊤
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.eq_or_lt`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a = b ∨ a < b
· 使用定理 `le_top`：le_top : a <= ⊤
-/
theorem eq_top_or_lt_top (a : α) : a = ⊤ ∨ a < ⊤ :=
  le_top.eq_or_lt

@[aesop (rule_sets := [finiteness]) safe apply, to_dual bot_lt]
/-
**Ne.lt_top** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Ne.lt_top (h : a != ⊤) : a < ⊤
参数：h : a != ⊤。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `lt_top_iff_ne_top`：lt_top_iff_ne_top : a < ⊤ ↔ a != ⊤
-/
theorem Ne.lt_top (h : a ≠ ⊤) : a < ⊤ :=
  lt_top_iff_ne_top.mpr h

@[to_dual bot_lt']
/-
**Ne.lt_top'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Ne.lt_top' (h : ⊤ != a) : a < ⊤
参数：h : ⊤ != a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ne.lt_top`：Ne.lt_top (h : a != ⊤) : a < ⊤
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
-/
theorem Ne.lt_top' (h : ⊤ ≠ a) : a < ⊤ :=
  h.symm.lt_top

@[to_dual]
/-
**ne_top_of_le_ne_top** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ne_top_of_le_ne_top (hb : b != ⊤) (hab : a <= b) : a != ⊤
参数：hb : b != ⊤；hab : a <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `Ne.lt_top`：Ne.lt_top (h : a != ⊤) : a < ⊤
-/
theorem ne_top_of_le_ne_top (hb : b ≠ ⊤) (hab : a ≤ b) : a ≠ ⊤ :=
  (hab.trans_lt hb.lt_top).ne

@[to_dual]
/-
**top_notMem_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：top_notMem_iff {s : Set α} : ⊤ ∉ s ↔ forall x in s, x < ⊤
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ne.lt_top`：Ne.lt_top (h : a != ⊤) : a < ⊤
· 使用定理 `LT.lt.false`：∀ {α : Type u_2} [inst : Preorder α] {a : α}, a < a → False
-/
lemma top_notMem_iff {s : Set α} : ⊤ ∉ s ↔ ∀ x ∈ s, x < ⊤ :=
  ⟨fun h x hx ↦ Ne.lt_top (fun hx' : x = ⊤ ↦ h (hx' ▸ hx)), fun h h₀ ↦ (h ⊤ h₀).false⟩

variable [Nontrivial α]

@[to_dual]
/-
**not_isMin_top** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：not_isMin_top : ¬IsMin (⊤ : α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_ne`：exists_ne [Nontrivial α] (x : α) : exists y, y != x
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `top_le_iff`：top_le_iff : ⊤ <= a ↔ a = ⊤
· 使用定理 `le_top`：le_top : a <= ⊤
-/
theorem not_isMin_top : ¬IsMin (⊤ : α) := fun h =>
  let ⟨_, ha⟩ := exists_ne (⊤ : α)
  ha <| top_le_iff.1 <| h le_top

end OrderTop

@[to_dual (reorder := H (x y))]
/-
**OrderTop.ext_top** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：OrderTop.ext_top {α} {hA : PartialOrder α} (A : OrderTop α) {hB : PartialO
rder α} (B : OrderTop α) (H : forall x y : α, (haveI
参数：A : OrderTop α；B : OrderTop α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `PartialOrder.ext`：PartialOrder.ext {A B : PartialOrder α} (H : forall x 
y : α, (haveI
· 使用定理 `top_unique`：top_unique (h : ⊤ <= a) : a = ⊤
· 使用定理 `OrderTop.le_top`：∀ {α : Type u} {inst : LE α} [self : OrderTop α] (a : α
), a ≤ ⊤
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem OrderTop.ext_top {α} {hA : PartialOrder α} (A : OrderTop α) {hB : PartialOrder α}
    (B : OrderTop α) (H : ∀ x y : α, (haveI := hA; x ≤ y) ↔ x ≤ y) :
    (@Top.top α (@OrderTop.toTop α hA.toLE A)) = (@Top.top α (@OrderTop.toTop α hB.toLE B)) := by
  cases PartialOrder.ext H
  apply top_unique
  exact @le_top _ _ A _

namespace OrderDual

variable (α)

@[to_dual]
/-
**OrderDual.** 是 Mathlib 中的一个实例，位于命名空间 `OrderDual`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [h : Bot α] : Top αᵒᵈ :=
  ⟨h.bot⟩

@[to_dual]
/-
**OrderDual.** 是 Mathlib 中的一个实例，位于命名空间 `OrderDual`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [LE α] [h : OrderBot α] : OrderTop αᵒᵈ where
  le_top := h.bot_le
/-
**OrderDual.ofDual_top** 是 Mathlib 中的一个定理，位于命名空间 `OrderDual`。
形式化陈述：∀ (α : Type u) [inst : Bot α], OrderDual.ofDual ⊤ = ⊥
参数：α : Type u。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_dual (attr := simp)] lemma ofDual_top [Bot α] : ofDual ⊤ = (⊥ : α) := rfl
/-
**OrderDual.toDual_top** 是 Mathlib 中的一个定理，位于命名空间 `OrderDual`。
形式化陈述：∀ (α : Type u) [inst : Top α], OrderDual.toDual ⊤ = ⊥
参数：α : Type u。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_dual (attr := simp)] lemma toDual_top [Top α] : toDual (⊤ : α) = ⊥ := rfl
/-
**OrderDual.ofDual_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `OrderDual`。
形式化陈述：∀ (α : Type u) [inst : Top α] {a : αᵒᵈ}, OrderDual.ofDual a = ⊤ ↔ a = ⊥
参数：α : Type u。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[to_dual (attr := simp)] lemma ofDual_eq_top [Top α] {a : αᵒᵈ} : ofDual a = ⊤ ↔ a = ⊥ := .rfl
/-
**OrderDual.toDual_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `OrderDual`。
形式化陈述：∀ (α : Type u) [inst : Bot α] {a : α}, OrderDual.toDual a = ⊤ ↔ a = ⊥
参数：α : Type u。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[to_dual (attr := simp)] lemma toDual_eq_top [Bot α] {a : α} : toDual a = ⊤ ↔ a = ⊥ := .rfl

end OrderDual


/-! ### Bounded order -/


/-- A bounded order describes an order `(≤)` with a top and bottom element,
  denoted `⊤` and `⊥` respectively. -/
/-
**BoundedOrder** 是 Mathlib 中的一个类，位于命名空间 ``。
形式化陈述：BoundedOrder (α : Type u) [LE α] extends OrderTop α, OrderBot α  attribute
 [to_dual self (reorder
参数：α : Type u。
继承自：OrderTop α, OrderBot α  attribute [to_dual self (reorder。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A bounded order describes an order `(≤)` with a top and bottom element,
  denoted `⊤` and `⊥` respectively.
-/
class BoundedOrder (α : Type u) [LE α] extends OrderTop α, OrderBot α

attribute [to_dual self (reorder := 3 4)] BoundedOrder.mk
attribute [to_dual existing] BoundedOrder.toOrderTop
/-
**OrderDual.instBoundedOrder** 是 Mathlib 中的一个定义，位于命名空间 `OrderDual`。
形式化陈述：(α : Type u) → [inst : LE α] → [BoundedOrder α] → BoundedOrder αᵒᵈ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance OrderDual.instBoundedOrder (α : Type u) [LE α] [BoundedOrder α] : BoundedOrder αᵒᵈ where

section PartialOrder
variable [PartialOrder α]

@[to_dual]
/-
**OrderBot.instSubsingleton** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：OrderBot.instSubsingleton : Subsingleton (OrderBot α) where allEq
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
-/
instance OrderBot.instSubsingleton : Subsingleton (OrderBot α) where
  allEq := by rintro @⟨⟨a⟩, ha⟩ @⟨⟨b⟩, hb⟩; congr; exact le_antisymm (ha _) (hb _)
/-
**BoundedOrder.instSubsingleton** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：BoundedOrder.instSubsingleton : Subsingleton (BoundedOrder α) where allEq
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `OrderTop.instSubsingleton`：∀ {α : Type u} [inst : PartialOrder α], Subsi
ngleton (OrderTop α)
-/
instance BoundedOrder.instSubsingleton : Subsingleton (BoundedOrder α) where
  allEq := by rintro ⟨⟩ ⟨⟩; congr <;> exact Subsingleton.elim _ _

end PartialOrder

/-! ### Function lattices -/

namespace Pi

variable {ι : Type*} {α' : ι → Type*}

@[to_dual]
/-
**Pi.** 是 Mathlib 中的一个实例，位于命名空间 `Pi`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [∀ i, Bot (α' i)] : Bot (∀ i, α' i) :=
  ⟨fun _ => ⊥⟩

@[to_dual (attr := simp)]
/-
**Pi.bot_apply** 是 Mathlib 中的一个定理，位于命名空间 `Pi`。
形式化陈述：bot_apply [forall i, Bot (α' i)] (i : ι) : (⊥ : forall i, α' i) i = ⊥
参数：α' i；i : ι。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem bot_apply [∀ i, Bot (α' i)] (i : ι) : (⊥ : ∀ i, α' i) i = ⊥ :=
  rfl

@[to_dual (attr := push ←)]
/-
**Pi.bot_def** 是 Mathlib 中的一个定理，位于命名空间 `Pi`。
形式化陈述：bot_def [forall i, Bot (α' i)] : (⊥ : forall i, α' i) = fun _ => ⊥
参数：α' i。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem bot_def [∀ i, Bot (α' i)] : (⊥ : ∀ i, α' i) = fun _ => ⊥ :=
  rfl

@[to_dual (attr := simp)]
/-
**Pi.bot_comp** 是 Mathlib 中的一个定理，位于命名空间 `Pi`。
形式化陈述：bot_comp {α β γ : Type*} [Bot γ] (x : α -> β) : (⊥ : β -> γ) ∘ x = ⊥
参数：x : α -> β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem bot_comp {α β γ : Type*} [Bot γ] (x : α → β) : (⊥ : β → γ) ∘ x = ⊥ := by
  rfl

@[to_dual]
/-
**Pi.instOrderBot** 是 Mathlib 中的一个实例，位于命名空间 `Pi`。
形式化陈述：instOrderBot [forall i, LE (α' i)] [forall i, OrderBot (α' i)] : OrderBot 
(forall i, α' i) where bot_le _
参数：α' i；α' i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instOrderBot [∀ i, LE (α' i)] [∀ i, OrderBot (α' i)] : OrderBot (∀ i, α' i) where
  bot_le _ := fun _ => bot_le
/-
**Pi.instBoundedOrder** 是 Mathlib 中的一个实例，位于命名空间 `Pi`。
形式化陈述：instBoundedOrder [forall i, LE (α' i)] [forall i, BoundedOrder (α' i)] : B
oundedOrder (forall i, α' i) where __
参数：α' i；α' i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instBoundedOrder [∀ i, LE (α' i)] [∀ i, BoundedOrder (α' i)] :
    BoundedOrder (∀ i, α' i) where
  __ := (inferInstance : OrderTop (∀ i, α' i))
  __ := (inferInstance : OrderBot (∀ i, α' i))

end Pi

section Subsingleton

/-- A type with a single element is a bounded order. -/
@[implicit_reducible]
/-
**BoundedOrder.ofUnique** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：BoundedOrder.ofUnique (α : Type*) [Preorder α] [Unique α] : BoundedOrder α
 where bot
参数：α : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A type with a single element is a bounded order.
-/
def BoundedOrder.ofUnique (α : Type*) [Preorder α] [Unique α] : BoundedOrder α where
  bot := default
  top := default
  le_top := by simp
  bot_le := by simp

variable [PartialOrder α] [BoundedOrder α]

@[to_dual]
/-
**eq_bot_of_bot_eq_top** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：eq_bot_of_bot_eq_top (hα : (⊥ : α) = ⊤) (x : α) : x = (⊥ : α)
参数：hα : (⊥ : α) = ⊤；x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_bot_mono`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α
] {a b : α}, b ≤ a → a = ⊥ → b = ⊥
· 使用定理 `le_top`：le_top : a <= ⊤
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem eq_bot_of_bot_eq_top (hα : (⊥ : α) = ⊤) (x : α) : x = (⊥ : α) :=
  eq_bot_mono le_top (Eq.symm hα)

@[to_dual]
/-
**eq_top_of_bot_eq_top** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：eq_top_of_bot_eq_top (hα : (⊥ : α) = ⊤) (x : α) : x = (⊤ : α)
参数：hα : (⊥ : α) = ⊤；x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_top_mono`：eq_top_mono (h : a <= b) (h₂ : a = ⊤) : b = ⊤
· 使用定理 `bot_le`：∀ {α : Type u} [inst : LE α] [inst_1 : OrderBot α] {a : α}, ⊥ ≤ 
a
-/
theorem eq_top_of_bot_eq_top (hα : (⊥ : α) = ⊤) (x : α) : x = (⊤ : α) :=
  eq_top_mono bot_le hα
/-
**subsingleton_of_top_le_bot** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：subsingleton_of_top_le_bot (h : (⊤ : α) <= (⊥ : α)) : Subsingleton α
参数：h : (⊤ : α) <= (⊥ : α)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `le_top`：le_top : a <= ⊤
· 使用定理 `bot_le`：∀ {α : Type u} [inst : LE α] [inst_1 : OrderBot α] {a : α}, ⊥ ≤ 
a
-/
theorem subsingleton_of_top_le_bot (h : (⊤ : α) ≤ (⊥ : α)) : Subsingleton α :=
  ⟨fun _ _ => le_antisymm
    (le_trans le_top <| le_trans h bot_le) (le_trans le_top <| le_trans h bot_le)⟩

@[to_dual]
/-
**subsingleton_of_bot_eq_top** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：subsingleton_of_bot_eq_top (hα : (⊥ : α) = (⊤ : α)) : Subsingleton α
参数：hα : (⊥ : α) = (⊤ : α)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `subsingleton_of_top_le_bot`：subsingleton_of_top_le_bot (h : (⊤ : α) <= (
⊥ : α)) : Subsingleton α
· 使用定理 `ge_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
-/
theorem subsingleton_of_bot_eq_top (hα : (⊥ : α) = (⊤ : α)) : Subsingleton α :=
  subsingleton_of_top_le_bot (ge_of_eq hα)

@[to_dual]
/-
**subsingleton_iff_bot_eq_top** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：subsingleton_iff_bot_eq_top : (⊥ : α) = (⊤ : α) ↔ Subsingleton α
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `subsingleton_of_bot_eq_top`：subsingleton_of_bot_eq_top (hα : (⊥ : α) = (
⊤ : α)) : Subsingleton α
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
-/
theorem subsingleton_iff_bot_eq_top : (⊥ : α) = (⊤ : α) ↔ Subsingleton α :=
  ⟨subsingleton_of_bot_eq_top, fun _ => Subsingleton.elim ⊥ ⊤⟩

end Subsingleton

section lift

-- See note [reducible non-instances]
/-- Pullback an `OrderTop`. -/
@[to_dual (reorder := map_le (a b)) /-- Pullback an `OrderBot`. -/]
/-
**OrderTop.lift** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：OrderTop.lift [LE α] [Top α] [LE β] [OrderTop β] (f : α -> β) (map_le : fo
rall a b, f a <= f b -> a <= b) (map_top : f ⊤ = ⊤) : OrderTop α
参数：f : α -> β；map_le : forall a b, f a <= f b -> a <= b；map_top : f ⊤ = ⊤。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Pullback an `OrderTop`.
-/
abbrev OrderTop.lift [LE α] [Top α] [LE β] [OrderTop β] (f : α → β)
    (map_le : ∀ a b, f a ≤ f b → a ≤ b) (map_top : f ⊤ = ⊤) : OrderTop α :=
  ⟨fun a =>
    map_le _ _ <| by
      rw [map_top]
      exact le_top _⟩

-- See note [reducible non-instances]
/-- Pullback a `BoundedOrder`. -/
@[to_dual self (reorder := 4 5, map_le (a b), map_top map_bot)]
/-
**BoundedOrder.lift** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：BoundedOrder.lift [LE α] [Top α] [Bot α] [LE β] [BoundedOrder β] (f : α ->
 β) (map_le : forall a b, f a <= f b -> a <= b) (map_top : f ⊤ = ⊤) (map_bot : f
 ⊥ = ⊥) : BoundedOrder α where __
参数：f : α -> β；map_le : forall a b, f a <= f b -> a <= b；map_top : f ⊤ = ⊤；map_bo
t : f ⊥ = ⊥。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Pullback a `BoundedOrder`.
-/
abbrev BoundedOrder.lift [LE α] [Top α] [Bot α] [LE β] [BoundedOrder β] (f : α → β)
    (map_le : ∀ a b, f a ≤ f b → a ≤ b) (map_top : f ⊤ = ⊤) (map_bot : f ⊥ = ⊥) :
    BoundedOrder α where
  __ := OrderTop.lift f map_le map_top
  __ := OrderBot.lift f map_le map_bot

end lift

/-! ### Subtype, order dual, product lattices -/


namespace Subtype

variable {p : α → Prop}

-- See note [reducible non-instances]
/-- A subtype remains a `⊥`-order if the property holds at `⊥`. -/
@[to_dual /-- A subtype remains a `⊤`-order if the property holds at `⊤`. -/]
/-
**Subtype.orderBot** 是 Mathlib 中的一个实例，位于命名空间 `Nat`。
形式化陈述：Subtype.orderBot (s : Set Nat) [DecidablePred (· in s)] [h : Nonempty s] :
 OrderBot s where bot
参数：s : Set Nat；· in s。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A subtype remains a `⊥`-order if the property holds at `⊥`.
-/
protected abbrev orderBot [LE α] [OrderBot α] (hbot : p ⊥) : OrderBot { x : α // p x } where
  bot := ⟨⊥, hbot⟩
  bot_le _ := bot_le

-- See note [reducible non-instances]
/-- A subtype remains a bounded order if the property holds at `⊥` and `⊤`. -/
@[to_dual self (reorder := hbot htop)]
/-
**Subtype.boundedOrder** 是 Mathlib 中的一个实例，位于命名空间 `IsLprojection`。
形式化陈述：Subtype.boundedOrder [FaithfulSMul M X] : BoundedOrder { P : M // IsLproje
ction X P } where top
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A subtype remains a bounded order if the property holds at `⊥` and `⊤`.
-/
protected abbrev boundedOrder [LE α] [BoundedOrder α] (hbot : p ⊥) (htop : p ⊤) :
    BoundedOrder (Subtype p) where
  __ := Subtype.orderTop htop
  __ := Subtype.orderBot hbot

variable [PartialOrder α]

@[to_dual (attr := simp)]
/-
**Subtype.mk_bot** 是 Mathlib 中的一个定理，位于命名空间 `Subtype`。
形式化陈述：mk_bot [OrderBot α] [OrderBot (Subtype p)] (hbot : p ⊥) : mk ⊥ hbot = ⊥
参数：Subtype p；hbot : p ⊥。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `le_bot_iff`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a ≤ ⊥ ↔ a = ⊥
· 使用定理 `Subtype.coe_le_coe`：coe_le_coe [LE α] {p : α -> Prop} {x y : Subtype p} 
: (x : α) <= y ↔ x <= y
· 使用定理 `bot_le`：∀ {α : Type u} [inst : LE α] [inst_1 : OrderBot α] {a : α}, ⊥ ≤ 
a
-/
theorem mk_bot [OrderBot α] [OrderBot (Subtype p)] (hbot : p ⊥) : mk ⊥ hbot = ⊥ :=
  le_bot_iff.1 <| coe_le_coe.1 bot_le

@[to_dual]
/-
**Subtype.coe_bot** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：Subtype.coe_bot {s : Set Nat} [DecidablePred (· in s)] [h : Nonempty s] : 
((⊥ : s) : Nat) = Nat.find (nonempty_subtype.1 h)
参数：· in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subtype.mk_bot`：mk_bot [OrderBot α] [OrderBot (Subtype p)] (hbot : p ⊥) 
: mk ⊥ hbot = ⊥
-/
theorem coe_bot [OrderBot α] [OrderBot (Subtype p)] (hbot : p ⊥) : ((⊥ : Subtype p) : α) = ⊥ :=
  congr_arg Subtype.val (mk_bot hbot).symm

@[to_dual (attr := simp)]
/-
**Subtype.coe_eq_bot_iff** 是 Mathlib 中的一个定理，位于命名空间 `Subtype`。
形式化陈述：coe_eq_bot_iff [OrderBot α] [OrderBot (Subtype p)] (hbot : p ⊥) {x : { x /
/ p x }} : (x : α) = ⊥ ↔ x = ⊥
参数：Subtype p；hbot : p ⊥。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subtype.coe_bot`：Subtype.coe_bot {s : Set Nat} [DecidablePred (· in s)] 
[h : Nonempty s] : ((⊥ : s) : Nat) = Nat.find (nonempty_subtype.1 h)
· 使用定理 `Subtype.ext_iff`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, a
1 = a2 ↔ ↑a1 = ↑a2
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem coe_eq_bot_iff [OrderBot α] [OrderBot (Subtype p)] (hbot : p ⊥) {x : { x // p x }} :
    (x : α) = ⊥ ↔ x = ⊥ := by
  rw [← coe_bot hbot, Subtype.ext_iff]

@[to_dual (attr := simp)]
/-
**Subtype.mk_eq_bot_iff** 是 Mathlib 中的一个定理，位于命名空间 `Subtype`。
形式化陈述：mk_eq_bot_iff [OrderBot α] [OrderBot (Subtype p)] (hbot : p ⊥) {x : α} (hx
 : p x) : (⟨x, hx⟩ : Subtype p) = ⊥ ↔ x = ⊥
参数：Subtype p；hbot : p ⊥；hx : p x。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Subtype.coe_eq_bot_iff`：coe_eq_bot_iff [OrderBot α] [OrderBot (Subtype p
)] (hbot : p ⊥) {x : { x // p x }} : (x : α) = ⊥ ↔ x = ⊥
-/
theorem mk_eq_bot_iff [OrderBot α] [OrderBot (Subtype p)] (hbot : p ⊥) {x : α} (hx : p x) :
    (⟨x, hx⟩ : Subtype p) = ⊥ ↔ x = ⊥ :=
  (coe_eq_bot_iff hbot).symm

end Subtype

namespace Prod

variable (α β)

@[to_dual]
/-
**Prod.instTop** 是 Mathlib 中的一个实例，位于命名空间 `Prod`。
形式化陈述：instTop [Top α] [Top β] : Top (α × β)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instTop [Top α] [Top β] : Top (α × β) :=
  ⟨⟨⊤, ⊤⟩⟩
/-
**Prod.fst_top** 是 Mathlib 中的一个定理，位于命名空间 `Prod`。
形式化陈述：∀ (α : Type u) (β : Type v) [inst : Top α] [inst_1 : Top β], ⊤.1 = ⊤
参数：α : Type u；β : Type v。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_dual (attr := simp)] lemma fst_top [Top α] [Top β] : (⊤ : α × β).fst = ⊤ := rfl
/-
**Prod.snd_top** 是 Mathlib 中的一个定理，位于命名空间 `Prod`。
形式化陈述：∀ (α : Type u) (β : Type v) [inst : Top α] [inst_1 : Top β], ⊤.2 = ⊤
参数：α : Type u；β : Type v。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_dual (attr := simp)] lemma snd_top [Top α] [Top β] : (⊤ : α × β).snd = ⊤ := rfl

@[to_dual]
/-
**Prod.instOrderTop** 是 Mathlib 中的一个实例，位于命名空间 `Prod`。
形式化陈述：instOrderTop [LE α] [LE β] [OrderTop α] [OrderTop β] : OrderTop (α × β) wh
ere __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instOrderTop [LE α] [LE β] [OrderTop α] [OrderTop β] : OrderTop (α × β) where
  __ := (inferInstance : Top (α × β))
  le_top _ := ⟨le_top, le_top⟩
/-
**Prod.instBoundedOrder** 是 Mathlib 中的一个实例，位于命名空间 `Prod`。
形式化陈述：instBoundedOrder [LE α] [LE β] [BoundedOrder α] [BoundedOrder β] : Bounded
Order (α × β) where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instBoundedOrder [LE α] [LE β] [BoundedOrder α] [BoundedOrder β] :
    BoundedOrder (α × β) where
  __ := (inferInstance : OrderTop (α × β))
  __ := (inferInstance : OrderBot (α × β))

end Prod

namespace ULift

@[to_dual]
/-
**ULift.** 是 Mathlib 中的一个实例，位于命名空间 `ULift`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Top α] : Top (ULift.{v} α) where top := up ⊤
/-
**ULift.up_top** 是 Mathlib 中的一个定理，位于命名空间 `ULift`。
形式化陈述：∀ {α : Type u} [inst : Top α], { down := ⊤ } = ⊤
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_dual (attr := simp)] theorem up_top [Top α] : up (⊤ : α) = ⊤ := rfl
/-
**ULift.down_top** 是 Mathlib 中的一个定理，位于命名空间 `ULift`。
形式化陈述：∀ {α : Type u} [inst : Top α], ⊤.down = ⊤
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_dual (attr := simp)] theorem down_top [Top α] : down (⊤ : ULift α) = ⊤ := rfl

@[to_dual]
/-
**ULift.** 是 Mathlib 中的一个实例，位于命名空间 `ULift`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [LE α] [OrderBot α] : OrderBot (ULift.{v} α) :=
  OrderBot.lift ULift.down (fun _ _ => down_le.mp) down_bot
/-
**ULift.** 是 Mathlib 中的一个实例，位于命名空间 `ULift`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [LE α] [BoundedOrder α] : BoundedOrder (ULift.{v} α) where

end ULift

section Nontrivial

variable [PartialOrder α] [BoundedOrder α] [Nontrivial α]

@[to_dual (attr := simp)]
/-
**bot_ne_top** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：bot_ne_top : (⊥ : α) != ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `not_subsingleton`：not_subsingleton (α) [Nontrivial α] : ¬Subsingleton α
· 使用定理 `subsingleton_of_bot_eq_top`：subsingleton_of_bot_eq_top (hα : (⊥ : α) = (
⊤ : α)) : Subsingleton α
-/
theorem bot_ne_top : (⊥ : α) ≠ ⊤ := fun h => not_subsingleton _ <| subsingleton_of_bot_eq_top h

@[simp]
/-
**bot_lt_top** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：bot_lt_top : (⊥ : α) < ⊤
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `lt_top_iff_ne_top`：lt_top_iff_ne_top : a < ⊤ ↔ a != ⊤
· 使用定理 `bot_ne_top`：bot_ne_top : (⊥ : α) != ⊤
-/
theorem bot_lt_top : (⊥ : α) < ⊤ :=
  lt_top_iff_ne_top.2 bot_ne_top

end Nontrivial

section Bool

open Bool

/-
**Bool.instBoundedOrder** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Bool.instBoundedOrder : BoundedOrder Bool where top
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Bool.le_true`：∀ (x : Bool), x ≤ true
· 使用定理 `Bool.false_le`：∀ (x : Bool), false ≤ x
-/
instance Bool.instBoundedOrder : BoundedOrder Bool where
  top := true
  le_top := Bool.le_true
  bot := false
  bot_le := Bool.false_le

@[simp]
/-
**top_eq_true** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：top_eq_true : ⊤ = true
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem top_eq_true : ⊤ = true :=
  rfl

@[simp]
/-
**bot_eq_false** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：bot_eq_false : ⊥ = false
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem bot_eq_false : ⊥ = false :=
  rfl

end Bool

