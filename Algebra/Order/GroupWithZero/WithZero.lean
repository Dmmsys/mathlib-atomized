/-
Copyright (c) 2024 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/
module

public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Canonical
/-!

# Covariant instances on `WithZero`

Adding a zero to a type with a preorder and multiplication which satisfies some
axiom, gives us a new type which satisfies some variant of the axiom.

## Example

If `α` satisfies `b₁ < b₂ → a * b₁ < a * b₂` for all `a`,
then `WithZero α` satisfies `b₁ < b₂ → a * b₁ < a * b₂` for all `a > 0`,
which is `PosMulStrictMono (WithZero α)`.

## Application

The type `ℤᵐ⁰ := WithZero (Multiplicative ℤ)` is used a lot in mathlib's valuation
theory. These instances enable lemmas such as `mul_pos` to fire on `ℤᵐ⁰`.

-/

@[expose] public section

assert_not_exists Ring

-- this makes `mul_lt_mul_iff_right₀`, `mul_pos` etc. work on `ℤᵐ⁰`
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {α : Type*} [Mul α] [Preorder α] [MulLeftStrictMono α] :
    PosMulStrictMono (WithZero α) where
  mul_lt_mul_of_pos_left
  | (x : α), hx, 0, (b : α), _ => by simpa only [mul_zero] using! WithZero.zero_lt_coe _
  | (x : α), hx, (a : α), (b : α), h => by norm_cast at h ⊢; gcongr

open Function in
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {α : Type*} [Mul α] [Preorder α] [MulRightStrictMono α] :
    MulPosStrictMono (WithZero α) where
  mul_lt_mul_of_pos_right
  | (x : α), hx, 0, (b : α), _ => by simpa only [mul_zero] using! WithZero.zero_lt_coe _
  | (x : α), hx, (a : α), (b : α), h => by norm_cast at h ⊢; gcongr
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {α : Type*} [Mul α] [Preorder α] [MulLeftMono α] :
    PosMulMono (WithZero α) where
  mul_le_mul_of_nonneg_left
  | 0, _, a, b, _ => by simp
  | (x : α), _, 0, _, _ => by simp
  | (x : α), _, (a : α), 0, h => by simp at h
  | (x : α), hx, (a : α), (b : α), h => by norm_cast at h ⊢; gcongr

-- This makes `lt_mul_of_le_of_one_lt'` work on `ℤᵐ⁰`
open Function in
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {α : Type*} [Mul α] [Preorder α] [MulRightMono α] :
    MulPosMono (WithZero α) where
  mul_le_mul_of_nonneg_right
  | 0, _, a, b, _ => by simp
  | (x : α), _, 0, _, _ => by simp
  | (x : α), _, (a : α), 0, h => by simp at h
  | (x : α), hx, (a : α), (b : α), h => by norm_cast at h ⊢; gcongr

section Units

variable {α : Type*} [LinearOrderedCommGroupWithZero α]

open WithZero

/-
**WithZero.withZeroUnitsEquiv_strictMono** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：WithZero.withZeroUnitsEquiv_strictMono : StrictMono (withZeroUnitsEquiv (G
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WithZero.withZeroUnitsEquiv_apply`：∀ {G : Type u_4} [inst : GroupWithZer
o G] [inst_1 : DecidablePred fun a => a = 0] (n : WithZero Gˣ),   WithZero.withZ
eroUnitsEquiv n = WithZ…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `WithZero.instIsBotZeroClass`：∀ {α : Type u_1} [inst : LE α], IsBotZeroCl
ass (WithZero α)
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
-/
lemma WithZero.withZeroUnitsEquiv_strictMono :
    StrictMono (withZeroUnitsEquiv (G := α)) := by
  intro a b
  cases a <;> cases b <;>
  simp

/-- Given any linearly ordered commutative group with zero `α`, this is the order isomorphism
between `WithZero αˣ` with `α`. -/
@[simps!]
/-
**OrderIso.withZeroUnits** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：OrderIso.withZeroUnits : WithZero αˣ ≃o α where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given any linearly ordered commutative group with zero `α`, this is the order is
omorphism
between `WithZero αˣ` with `α`.
-/
def OrderIso.withZeroUnits : WithZero αˣ ≃o α where
  __ := withZeroUnitsEquiv
  map_rel_iff' := WithZero.withZeroUnitsEquiv_strictMono.le_iff_le
/-
**WithZero.withZeroUnitsEquiv_symm_strictMono** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：WithZero.withZeroUnitsEquiv_symm_strictMono : StrictMono (withZeroUnitsEqu
iv (G
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIso.strictMono`：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α]
 [inst_1 : Preorder β] (e : α ≃o β), StrictMono ⇑e
-/
lemma WithZero.withZeroUnitsEquiv_symm_strictMono :
    StrictMono (withZeroUnitsEquiv (G := α)).symm :=
  OrderIso.withZeroUnits.symm.strictMono

end Units

