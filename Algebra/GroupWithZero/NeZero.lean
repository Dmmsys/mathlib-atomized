/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
module

public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.NeZero

/-!
# `NeZero 1` in a nontrivial `MulZeroOneClass`.

This file exists to minimize the dependencies of `Mathlib/Algebra/GroupWithZero/Defs.lean`,
which is a part of the algebraic hierarchy used by basic tactics.
-/

public section

assert_not_exists DenselyOrdered Ring

universe u

variable {M₀ M₀' : Type*} [MulZeroOneClass M₀] [Nontrivial M₀]

/-- In a nontrivial monoid with zero, zero and one are different. -/
/-
**NeZero.one** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：NeZero.one : NeZero (1 : M₀)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_pair_ne`：exists_pair_ne (α : Type*) [Nontrivial α] : exists x y :
 α, x != y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0

--- 原说明 ---
In a nontrivial monoid with zero, zero and one are different.
-/
instance NeZero.one : NeZero (1 : M₀) := ⟨by
  intro h
  rcases exists_pair_ne M₀ with ⟨x, y, hx⟩
  apply hx
  calc
    x = 1 * x := by rw [one_mul]
    _ = 0 := by rw [h, zero_mul]
    _ = 1 * y := by rw [h, zero_mul]
    _ = y := by rw [one_mul]⟩

/-- Pullback a `Nontrivial` instance along a function sending `0` to `0` and `1` to `1`. -/
/-
**domain_nontrivial** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：domain_nontrivial [Zero M₀'] [One M₀'] (f : M₀' -> M₀) (zero : f 0 = 0) (o
ne : f 1 = 1) : Nontrivial M₀'
参数：f : M₀' -> M₀；zero : f 0 = 0；one : f 1 = 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_ne_one`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 0 ≠ 1

--- 原说明 ---
Pullback a `Nontrivial` instance along a function sending `0` to `0` and `1` to 
`1`.
-/
theorem domain_nontrivial [Zero M₀'] [One M₀'] (f : M₀' → M₀) (zero : f 0 = 0) (one : f 1 = 1) :
    Nontrivial M₀' :=
  ⟨⟨0, 1, mt (congr_arg f) <| by
    rw [zero, one]
    exact zero_ne_one⟩⟩

section GroupWithZero

variable {G₀ : Type*} [GroupWithZero G₀] {a : G₀}

/-
**inv_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：inv_ne_zero (h : a != 0) : a⁻¹ != 0
参数：h : a != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `GroupWithZero.toNontrivial`：∀ {G₀ : Type u} [self : GroupWithZero G₀], N
ontrivial G₀
· 使用引理 `mul_inv_cancel₀`：mul_inv_cancel₀ (h : a != 0) : a * a⁻¹ = 1
-/
theorem inv_ne_zero (h : a ≠ 0) : a⁻¹ ≠ 0 := fun a_eq_0 => by
  simpa [a_eq_0] using mul_inv_cancel₀ h

@[simp high] -- should take priority over `IsUnit.inv_mul_cancel`
/-
**inv_mul_cancel** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：inv_mul_cancel (a : G) : a⁻¹ * a = 1
参数：a : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Group.inv_mul_cancel`：∀ {G : Type u} [self : Group G] (a : G), a⁻¹ * a =
 1
-/
theorem inv_mul_cancel₀ (h : a ≠ 0) : a⁻¹ * a = 1 :=
  calc
    a⁻¹ * a = a⁻¹ * a * a⁻¹ * a⁻¹⁻¹ := by simp [inv_ne_zero h]
    _ = a⁻¹ * a⁻¹⁻¹ := by simp [h]
    _ = 1 := by simp [inv_ne_zero h]

end GroupWithZero

