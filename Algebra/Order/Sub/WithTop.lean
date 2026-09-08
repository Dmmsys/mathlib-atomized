/-
Copyright (c) 2021 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
module

public import Mathlib.Algebra.Order.Sub.Defs
public import Mathlib.Algebra.Order.Monoid.Unbundled.WithTop

/-!
# Lemma about subtraction in ordered monoids with a top element adjoined.

This file introduces a subtraction on `WithTop α` when `α` has a subtraction and a bottom element,
given by `x - ⊤ = ⊥` and `⊤ - x = ⊤`. This will be instantiated mostly for `ℕ∞` and `ℝ≥0∞`, where
the bottom element is zero.

Note that there is another subtraction on objects of the form `WithTop α` in the file
`Mathlib/Algebra/Order/AddGroupWithTop.lean`, setting `-⊤ = ⊤` as this corresponds to the
additivization of the usual convention `0⁻¹ = 0` and is relevant in valuation theory. Since that
other instance is only registered for `AddCommGroup α` (which doesn't have a bottom
element, unless the group is trivial), this shouldn't create diamonds.
-/

@[expose] public section

variable {α β : Type*}

namespace WithTop

section

variable [Sub α] [Bot α]

/-- If `α` has a subtraction and a bottom element, we can extend the subtraction to `WithTop α`, by
setting `x - ⊤ = ⊥` and `⊤ - x = ⊤`. -/
/-
**WithTop.sub** 是 Mathlib 中的一个定义，位于命名空间 `WithTop`。
形式化陈述：{α : Type u_1} → [Sub α] → [Bot α] → WithTop α → WithTop α → WithTop α
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `α` has a subtraction and a bottom element, we can extend the subtraction to 
`WithTop α`, by
setting `x - ⊤ = ⊥` and `⊤ - x = ⊤`.
-/
protected def sub : ∀ _ _ : WithTop α, WithTop α
  | _, ⊤ => (⊥ : α)
  | ⊤, (x : α) => ⊤
  | (x : α), (y : α) => (x - y : α)
/-
**WithTop.** 是 Mathlib 中的一个实例，位于命名空间 `WithTop`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Sub (WithTop α) :=
  ⟨WithTop.sub⟩

@[simp, norm_cast]
/-
**WithTop.coe_sub** 是 Mathlib 中的一个定理，位于命名空间 `WithTop`。
形式化陈述：coe_sub {a b : α} : (↑(a - b) : WithTop α) = ↑a - ↑b
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_sub {a b : α} : (↑(a - b) : WithTop α) = ↑a - ↑b :=
  rfl

@[simp]
/-
**WithTop.top_sub_coe** 是 Mathlib 中的一个定理，位于命名空间 `WithTop`。
形式化陈述：top_sub_coe {a : α} : (⊤ : WithTop α) - a = ⊤
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem top_sub_coe {a : α} : (⊤ : WithTop α) - a = ⊤ :=
  rfl

@[simp]
/-
**WithTop.sub_top** 是 Mathlib 中的一个定理，位于命名空间 `WithTop`。
形式化陈述：sub_top {a : WithTop α} : a - ⊤ = (⊥ : α)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem sub_top {a : WithTop α} : a - ⊤ = (⊥ : α) := by cases a <;> rfl
/-
**WithTop.sub_eq_top_iff** 是 Mathlib 中的一个定理，位于命名空间 `WithTop`。
形式化陈述：∀ {α : Type u_1} [inst : Sub α] [inst_1 : Bot α] {a b : WithTop α}, a - b 
= ⊤ ↔ a = ⊤ ∧ b ≠ ⊤
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `WithTop.sub_top`：sub_top {a : WithTop α} : a - ⊤ = (⊥ : α)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
-/
@[simp] theorem sub_eq_top_iff {a b : WithTop α} : a - b = ⊤ ↔ a = ⊤ ∧ b ≠ ⊤ := by
  induction a <;> induction b <;>
    simp only [← coe_sub, coe_ne_top, sub_top, top_sub_coe, false_and, Ne, not_true_eq_false,
      not_false_eq_true, and_false, and_self]
/-
**WithTop.sub_ne_top_iff** 是 Mathlib 中的一个引理，位于命名空间 `WithTop`。
形式化陈述：sub_ne_top_iff {a b : WithTop α} : a - b != ⊤ ↔ a != ⊤ ∨ b = ⊤
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
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
lemma sub_ne_top_iff {a b : WithTop α} : a - b ≠ ⊤ ↔ a ≠ ⊤ ∨ b = ⊤ := by simp [or_iff_not_imp_left]

protected
/-
**WithTop.map_sub** 是 Mathlib 中的一个定理，位于命名空间 `WithTop`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : Sub α] [inst_1 : Bot α] [inst_2 : 
Sub β] [inst_3 : Bot β] {f : α → β},   (∀ (x y : α), f (x - y) = f x - f y) →   
  f ⊥ = ⊥ → ∀ (x y : WithTop α), WithTop.map f (x - y) = WithTop.map f x - WithT
op.map f y
参数：∀ (x y : α), f (x - y) = f x - f y；x y : WithTop α；x - y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WithTop.sub_top`：sub_top {a : WithTop α} : a - ⊤ = (⊥ : α)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
-/
theorem map_sub [Sub β] [Bot β] {f : α → β} (h : ∀ x y, f (x - y) = f x - f y) (h₀ : f ⊥ = ⊥) :
    ∀ x y : WithTop α, (x - y).map f = x.map f - y.map f
  | _, ⊤ => by simp only [sub_top, map_coe, h₀, map_top]
  | ⊤, (x : α) => rfl
  | (x : α), (y : α) => by simp only [← coe_sub, map_coe, h]

end

variable [Add α] [LE α] [OrderBot α] [Sub α] [OrderedSub α]

/-
**WithTop.** 是 Mathlib 中的一个实例，位于命名空间 `WithTop`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : OrderedSub (WithTop α) := by
  constructor
  rintro x y z
  cases y
  · cases z <;> simp
  cases x
  · simp
  cases z
  · simp
  norm_cast
  exact tsub_le_iff_right

end WithTop

