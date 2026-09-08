/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
module

public import Mathlib.Algebra.Group.Units.Basic
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Data.Nat.Basic  -- shake: keep (non-recorded `nontrivial` dependency?)
public import Mathlib.Lean.Meta.CongrTheorems
public import Mathlib.Tactic.Contrapose
public import Mathlib.Tactic.Spread
public import Mathlib.Tactic.Convert
public import Mathlib.Tactic.Nontriviality

/-!
# Lemmas about units in a `MonoidWithZero` or a `GroupWithZero`.

We also define `Ring.inverse`, a globally defined function on any ring
(in fact any `MonoidWithZero`), which inverts units and sends non-units to zero.
-/

@[expose] public section

assert_not_exists DenselyOrdered Equiv Subtype.restrict Multiplicative Ring

variable {α M₀ G₀ : Type*}
variable [MonoidWithZero M₀]

namespace Units

/-- An element of the unit group of a nonzero monoid with zero represented as an element
of the monoid is nonzero. -/
@[simp]
/-
**Units.ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Units`。
形式化陈述：ne_zero [Nontrivial M₀] (u : M₀ˣ) : (u : M₀) != 0
参数：u : M₀ˣ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `left_ne_zero_of_mul_eq_one`：left_ne_zero_of_mul_eq_one (h : a * b = 1) :
 a != 0
· 使用定理 `Units.mul_inv`：mul_inv : (a * ↑a⁻¹ : α) = 1

--- 原说明 ---
An element of the unit group of a nonzero monoid with zero represented as an ele
ment
of the monoid is nonzero.
-/
theorem ne_zero [Nontrivial M₀] (u : M₀ˣ) : (u : M₀) ≠ 0 :=
  left_ne_zero_of_mul_eq_one u.mul_inv

-- We can't use `mul_eq_zero` + `Units.ne_zero` in the next two lemmas because we don't assume
-- `Nontrivial M₀`.
@[simp]
/-
**Units.mul_left_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Units`。
形式化陈述：mul_left_eq_zero (u : M₀ˣ) {a : M₀} : a * u = 0 ↔ a = 0
参数：u : M₀ˣ。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Units.mul_inv_cancel_right`：mul_inv_cancel_right (a : α) (b : αˣ) : a * 
b * ↑b⁻¹ = a
· 使用定理 `mul_eq_zero_of_left`：mul_eq_zero_of_left {a : M₀} (h : a = 0) (b : M₀) :
 a * b = 0
-/
theorem mul_left_eq_zero (u : M₀ˣ) {a : M₀} : a * u = 0 ↔ a = 0 :=
  ⟨fun h => by simpa using mul_eq_zero_of_left h ↑u⁻¹, fun h => mul_eq_zero_of_left h u⟩

@[simp]
/-
**Units.mul_right_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Units`。
形式化陈述：mul_right_eq_zero (u : M₀ˣ) {a : M₀} : ↑u * a = 0 ↔ a = 0
参数：u : M₀ˣ。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Units.inv_mul_cancel_left`：inv_mul_cancel_left (a : αˣ) (b : α) : (↑a⁻¹ 
: α) * (a * b) = b
· 使用定理 `mul_eq_zero_of_right`：mul_eq_zero_of_right (a : M₀) {b : M₀} (h : b = 0)
 : a * b = 0
-/
theorem mul_right_eq_zero (u : M₀ˣ) {a : M₀} : ↑u * a = 0 ↔ a = 0 :=
  ⟨fun h => by simpa using mul_eq_zero_of_right (↑u⁻¹) h, mul_eq_zero_of_right (u : M₀)⟩

end Units

namespace IsUnit

/-
**IsUnit.ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `IsUnit`。
形式化陈述：ne_zero [Nontrivial M₀] {a : M₀} (ha : IsUnit a) : a != 0
参数：ha : IsUnit a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Units.ne_zero`：ne_zero [Nontrivial M₀] (u : M₀ˣ) : (u : M₀) != 0
-/
theorem ne_zero [Nontrivial M₀] {a : M₀} (ha : IsUnit a) : a ≠ 0 :=
  let ⟨u, hu⟩ := ha
  hu ▸ u.ne_zero
/-
**IsUnit.mul_right_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `IsUnit`。
形式化陈述：mul_right_eq_zero {a b : M₀} (ha : IsUnit a) : a * b = 0 ↔ b = 0
参数：ha : IsUnit a。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Units.mul_right_eq_zero`：mul_right_eq_zero (u : M₀ˣ) {a : M₀} : ↑u * a =
 0 ↔ a = 0
-/
theorem mul_right_eq_zero {a b : M₀} (ha : IsUnit a) : a * b = 0 ↔ b = 0 :=
  let ⟨u, hu⟩ := ha
  hu ▸ u.mul_right_eq_zero
/-
**IsUnit.mul_left_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `IsUnit`。
形式化陈述：mul_left_eq_zero {a b : M₀} (hb : IsUnit b) : a * b = 0 ↔ a = 0
参数：hb : IsUnit b。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Units.mul_left_eq_zero`：mul_left_eq_zero (u : M₀ˣ) {a : M₀} : a * u = 0 
↔ a = 0
-/
theorem mul_left_eq_zero {a b : M₀} (hb : IsUnit b) : a * b = 0 ↔ a = 0 :=
  let ⟨u, hu⟩ := hb
  hu ▸ u.mul_left_eq_zero

end IsUnit

@[simp]
/-
**isUnit_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isUnit_zero_iff : IsUnit (0 : M₀) ↔ (0 : M₀) = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `isUnit_of_subsingleton`：isUnit_of_subsingleton [Monoid M] [Subsingleton 
M] (a : M) : IsUnit a
· 使用定理 `subsingleton_of_zero_eq_one`：∀ {M₀ : Type u_1} [inst : MulZeroOneClass M
₀], 0 = 1 → Subsingleton M₀
-/
theorem isUnit_zero_iff : IsUnit (0 : M₀) ↔ (0 : M₀) = 1 :=
  ⟨fun ⟨⟨_, a, (a0 : 0 * a = 1), _⟩, rfl⟩ => by rwa [zero_mul] at a0, fun h =>
    @isUnit_of_subsingleton _ _ (subsingleton_of_zero_eq_one h) 0⟩
/-
**not_isUnit_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：not_isUnit_zero [Nontrivial M₀] : ¬IsUnit (0 : M₀)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isUnit_zero_iff`：isUnit_zero_iff : IsUnit (0 : M₀) ↔ (0 : M₀) = 1
· 使用定理 `zero_ne_one`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 0 ≠ 1
-/
theorem not_isUnit_zero [Nontrivial M₀] : ¬IsUnit (0 : M₀) :=
  mt isUnit_zero_iff.1 zero_ne_one

namespace Ring

open scoped Classical in
/-- Introduce a function `inverse` on a monoid with zero `M₀`, which sends `x` to `x⁻¹` if `x` is
invertible and to `0` otherwise.  This definition is somewhat ad hoc, but one needs a fully (rather
than partially) defined inverse function for some purposes, including for calculus.

Note that while this is in the `Ring` namespace for brevity, it requires the weaker assumption
`MonoidWithZero M₀` instead of `Ring M₀`. -/
/-
**Ring.inverse** 是 Mathlib 中的一个定义，位于命名空间 `Ring`。
形式化陈述：inverse : M₀ -> M₀
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Introduce a function `inverse` on a monoid with zero `M₀`, which sends `x` to `x
⁻¹` if `x` is
invertible and to `0` otherwise.  This definition is somewhat ad hoc, but one ne
eds a fully (rather
than partially) defined inverse function for some purposes, including for calcul
us.

Note that while this is in the `Ring` namespace for brevity, it requires the wea
ker assumption
`MonoidWithZero M₀` instead of `Ring M₀`.
-/
noncomputable def inverse : M₀ → M₀ := fun x => if h : IsUnit x then ((h.unit⁻¹ : M₀ˣ) : M₀) else 0

@[inherit_doc]
scoped postfix:max "⁻¹ʳ" => inverse

/-- By definition, if `x` is invertible then `inverse x = x⁻¹`. -/
/-
**Ring.inverse_unit** 是 Mathlib 中的一个定理，位于命名空间 `Ring`。
形式化陈述：inverse_unit (u : M₀ˣ) : (u : M₀)⁻¹ʳ = (u⁻¹ : M₀ˣ)
参数：u : M₀ˣ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ring.inverse.eq_1`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] (x : M₀)
, Ring.inverse x = if h : IsUnit x then ↑h.unit⁻¹ else 0
· 使用定理 `Units.isUnit`：∀ {M : Type u_1} [inst : Monoid M] (u : Mˣ), IsUnit ↑u
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `IsUnit.unit_of_val_units`：unit_of_val_units {a : Mˣ} (h : IsUnit (a : M)
) : h.unit = a

--- 原说明 ---
By definition, if `x` is invertible then `inverse x = x⁻¹`.
-/
theorem inverse_unit (u : M₀ˣ) : (u : M₀)⁻¹ʳ = (u⁻¹ : M₀ˣ) := by
  rw [inverse, dif_pos u.isUnit, IsUnit.unit_of_val_units]
/-
**Ring.inverse_of_isUnit** 是 Mathlib 中的一个定理，位于命名空间 `Ring`。
形式化陈述：inverse_of_isUnit {x : M₀} (h : IsUnit x) : x⁻¹ʳ = ((h.unit⁻¹ : M₀ˣ) : M₀)
参数：h : IsUnit x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
-/
theorem inverse_of_isUnit {x : M₀} (h : IsUnit x) : x⁻¹ʳ = ((h.unit⁻¹ : M₀ˣ) : M₀) := dif_pos h

/-- By definition, if `x` is not invertible then `inverse x = 0`. -/
@[simp]
/-
**Ring.inverse_non_unit** 是 Mathlib 中的一个定理，位于命名空间 `Ring`。
形式化陈述：inverse_non_unit (x : M₀) (h : ¬IsUnit x) : x⁻¹ʳ = 0
参数：x : M₀；h : ¬IsUnit x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc

--- 原说明 ---
By definition, if `x` is not invertible then `inverse x = 0`.
-/
theorem inverse_non_unit (x : M₀) (h : ¬IsUnit x) : x⁻¹ʳ = 0 :=
  dif_neg h
/-
**Ring.mul_inverse_cancel** 是 Mathlib 中的一个定理，位于命名空间 `Ring`。
形式化陈述：mul_inverse_cancel (x : M₀) (h : IsUnit x) : x * x⁻¹ʳ = 1
参数：x : M₀；h : IsUnit x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ring.inverse_unit`：inverse_unit (u : M₀ˣ) : (u : M₀)⁻¹ʳ = (u⁻¹ : M₀ˣ)
· 使用定理 `Units.mul_inv`：mul_inv : (a * ↑a⁻¹ : α) = 1
-/
theorem mul_inverse_cancel (x : M₀) (h : IsUnit x) : x * x⁻¹ʳ = 1 := by
  rcases h with ⟨u, rfl⟩
  rw [inverse_unit, Units.mul_inv]
/-
**Ring.inverse_mul_cancel** 是 Mathlib 中的一个定理，位于命名空间 `Ring`。
形式化陈述：inverse_mul_cancel (x : M₀) (h : IsUnit x) : x⁻¹ʳ * x = 1
参数：x : M₀；h : IsUnit x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ring.inverse_unit`：inverse_unit (u : M₀ˣ) : (u : M₀)⁻¹ʳ = (u⁻¹ : M₀ˣ)
· 使用定理 `Units.inv_mul`：inv_mul : (↑a⁻¹ * a : α) = 1
-/
theorem inverse_mul_cancel (x : M₀) (h : IsUnit x) : x⁻¹ʳ * x = 1 := by
  rcases h with ⟨u, rfl⟩
  rw [inverse_unit, Units.inv_mul]
/-
**Ring.mul_inverse_cancel_right** 是 Mathlib 中的一个定理，位于命名空间 `Ring`。
形式化陈述：mul_inverse_cancel_right (x y : M₀) (h : IsUnit x) : y * x * x⁻¹ʳ = y
参数：x y : M₀；h : IsUnit x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Ring.mul_inverse_cancel`：mul_inverse_cancel (x : M₀) (h : IsUnit x) : x 
* x⁻¹ʳ = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
theorem mul_inverse_cancel_right (x y : M₀) (h : IsUnit x) : y * x * x⁻¹ʳ = y := by
  rw [mul_assoc, mul_inverse_cancel x h, mul_one]
/-
**Ring.inverse_mul_cancel_right** 是 Mathlib 中的一个定理，位于命名空间 `Ring`。
形式化陈述：inverse_mul_cancel_right (x y : M₀) (h : IsUnit x) : y * x⁻¹ʳ * x = y
参数：x y : M₀；h : IsUnit x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Ring.inverse_mul_cancel`：inverse_mul_cancel (x : M₀) (h : IsUnit x) : x⁻
¹ʳ * x = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
theorem inverse_mul_cancel_right (x y : M₀) (h : IsUnit x) : y * x⁻¹ʳ * x = y := by
  rw [mul_assoc, inverse_mul_cancel x h, mul_one]
/-
**Ring.mul_inverse_cancel_left** 是 Mathlib 中的一个定理，位于命名空间 `Ring`。
形式化陈述：mul_inverse_cancel_left (x y : M₀) (h : IsUnit x) : x * (x⁻¹ʳ * y) = y
参数：x y : M₀；h : IsUnit x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Ring.mul_inverse_cancel`：mul_inverse_cancel (x : M₀) (h : IsUnit x) : x 
* x⁻¹ʳ = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
theorem mul_inverse_cancel_left (x y : M₀) (h : IsUnit x) : x * (x⁻¹ʳ * y) = y := by
  rw [← mul_assoc, mul_inverse_cancel x h, one_mul]
/-
**Ring.inverse_mul_cancel_left** 是 Mathlib 中的一个定理，位于命名空间 `Ring`。
形式化陈述：inverse_mul_cancel_left (x y : M₀) (h : IsUnit x) : x⁻¹ʳ * (x * y) = y
参数：x y : M₀；h : IsUnit x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Ring.inverse_mul_cancel`：inverse_mul_cancel (x : M₀) (h : IsUnit x) : x⁻
¹ʳ * x = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
theorem inverse_mul_cancel_left (x y : M₀) (h : IsUnit x) : x⁻¹ʳ * (x * y) = y := by
  rw [← mul_assoc, inverse_mul_cancel x h, one_mul]
/-
**Ring.inverse_mul_eq_iff_eq_mul** 是 Mathlib 中的一个定理，位于命名空间 `Ring`。
形式化陈述：inverse_mul_eq_iff_eq_mul (x y z : M₀) (h : IsUnit x) : x⁻¹ʳ * y = z ↔ y =
 x * z
参数：x y z : M₀；h : IsUnit x。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ring.mul_inverse_cancel_left`：mul_inverse_cancel_left (x y : M₀) (h : Is
Unit x) : x * (x⁻¹ʳ * y) = y
· 使用定理 `Ring.inverse_mul_cancel_left`：inverse_mul_cancel_left (x y : M₀) (h : Is
Unit x) : x⁻¹ʳ * (x * y) = y
-/
theorem inverse_mul_eq_iff_eq_mul (x y z : M₀) (h : IsUnit x) : x⁻¹ʳ * y = z ↔ y = x * z :=
  ⟨fun h1 => by rw [← h1, mul_inverse_cancel_left _ _ h],
  fun h1 => by rw [h1, inverse_mul_cancel_left _ _ h]⟩
/-
**Ring.eq_mul_inverse_iff_mul_eq** 是 Mathlib 中的一个定理，位于命名空间 `Ring`。
形式化陈述：eq_mul_inverse_iff_mul_eq (x y z : M₀) (h : IsUnit z) : x = y * z⁻¹ʳ ↔ x *
 z = y
参数：x y z : M₀；h : IsUnit z。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ring.inverse_mul_cancel_right`：inverse_mul_cancel_right (x y : M₀) (h : 
IsUnit x) : y * x⁻¹ʳ * x = y
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ring.mul_inverse_cancel_right`：mul_inverse_cancel_right (x y : M₀) (h : 
IsUnit x) : y * x * x⁻¹ʳ = y
-/
theorem eq_mul_inverse_iff_mul_eq (x y z : M₀) (h : IsUnit z) : x = y * z⁻¹ʳ ↔ x * z = y :=
  ⟨fun h1 => by rw [h1, inverse_mul_cancel_right _ _ h],
  fun h1 => by rw [← h1, mul_inverse_cancel_right _ _ h]⟩

variable (M₀) in
@[simp, grind =]
/-
**Ring.inverse_one** 是 Mathlib 中的一个定理，位于命名空间 `Ring`。
形式化陈述：inverse_one : (1 : M₀)⁻¹ʳ = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ring.inverse_unit`：inverse_unit (u : M₀ˣ) : (u : M₀)⁻¹ʳ = (u⁻¹ : M₀ˣ)
-/
theorem inverse_one : (1 : M₀)⁻¹ʳ = 1 :=
  inverse_unit 1

variable (M₀) in
@[simp, grind =]
/-
**Ring.inverse_zero** 是 Mathlib 中的一个定理，位于命名空间 `Ring`。
形式化陈述：inverse_zero : (0 : M₀)⁻¹ʳ = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Ring.inverse_non_unit`：inverse_non_unit (x : M₀) (h : ¬IsUnit x) : x⁻¹ʳ 
= 0
· 使用定理 `not_isUnit_zero`：not_isUnit_zero [Nontrivial M₀] : ¬IsUnit (0 : M₀)
-/
theorem inverse_zero : (0 : M₀)⁻¹ʳ = 0 := by
  nontriviality
  exact inverse_non_unit _ not_isUnit_zero

@[grind =]
/-
**Ring.inverse_inverse** 是 Mathlib 中的一个定理，位于命名空间 `Ring`。
形式化陈述：inverse_inverse {a : M₀} (h : IsUnit a) : a⁻¹ʳ⁻¹ʳ = a
参数：h : IsUnit a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ring.inverse_unit`：inverse_unit (u : M₀ˣ) : (u : M₀)⁻¹ʳ = (u⁻¹ : M₀ˣ)
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
-/
theorem inverse_inverse {a : M₀} (h : IsUnit a) : a⁻¹ʳ⁻¹ʳ = a := by
  obtain ⟨u, rfl⟩ := h
  rw [inverse_unit, inverse_unit, inv_inv]

end Ring

open scoped Ring

/-
**IsUnit.ringInverse** 是 Mathlib 中的一个定理，位于命名空间 `IsUnit`。
形式化陈述：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] {a : M₀}, IsUnit a → IsUnit (
Ring.inverse a)
参数：Ring.inverse a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ring.inverse_unit`：inverse_unit (u : M₀ˣ) : (u : M₀)⁻¹ʳ = (u⁻¹ : M₀ˣ)
-/
theorem IsUnit.ringInverse {a : M₀} : IsUnit a → IsUnit a⁻¹ʳ
  | ⟨u, hu⟩ => hu ▸ ⟨u⁻¹, (Ring.inverse_unit u).symm⟩

@[simp, grind =]
/-
**isUnit_ringInverse** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isUnit_ringInverse {a : M₀} : IsUnit a⁻¹ʳ ↔ IsUnit a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `subsingleton_or_nontrivial`：subsingleton_or_nontrivial (α : Type*) : Sub
singleton α ∨ Nontrivial α
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Lean.Meta.FastSubsingleton.elim`：∀ {α : Sort u} [h : Meta.FastSubsinglet
on α] (a b : α), a = b
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ring.inverse_non_unit`：inverse_non_unit (x : M₀) (h : ¬IsUnit x) : x⁻¹ʳ 
= 0
· 使用定理 `not_isUnit_zero`：not_isUnit_zero [Nontrivial M₀] : ¬IsUnit (0 : M₀)
· 使用定理 `IsUnit.ringInverse`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] {a : M₀
}, IsUnit a → IsUnit (Ring.inverse a)
-/
theorem isUnit_ringInverse {a : M₀} : IsUnit a⁻¹ʳ ↔ IsUnit a :=
  ⟨fun h => by
    cases subsingleton_or_nontrivial M₀
    · convert! h
    · contrapose h
      rw [Ring.inverse_non_unit _ h]
      exact not_isUnit_zero,
    IsUnit.ringInverse⟩

@[grind =]
/-
**Ring.inverse_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Ring.inverse_mul {a b : M₀} (h : IsUnit a ∨ IsUnit b) : (a * b)⁻¹ʳ = b⁻¹ʳ 
* a⁻¹ʳ
参数：h : IsUnit a ∨ IsUnit b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsUnit.mul_left_iff`：mul_left_iff {a b : M} (ha : IsUnit a) : IsUnit (a 
* b) ↔ IsUnit b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Ring.inverse_non_unit`：inverse_non_unit (x : M₀) (h : ¬IsUnit x) : x⁻¹ʳ 
= 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `IsUnit.mul_right_iff`：mul_right_iff {a b : M} (hb : IsUnit b) : IsUnit (
a * b) ↔ IsUnit a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `IsUnit.mul`：∀ {M : Type u_1} [inst : Monoid M] {a b : M}, IsUnit a → IsU
nit b → IsUnit (a * b)
· 使用定理 `Ring.inverse_of_isUnit`：inverse_of_isUnit {x : M₀} (h : IsUnit x) : x⁻¹ʳ
 = ((h.unit⁻¹ : M₀ˣ) : M₀)
-/
theorem Ring.inverse_mul {a b : M₀} (h : IsUnit a ∨ IsUnit b) : (a * b)⁻¹ʳ = b⁻¹ʳ * a⁻¹ʳ := by
  obtain (⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩) :
      (IsUnit a ∧ ¬ IsUnit b) ∨ (¬ IsUnit a ∧ IsUnit b) ∨ (IsUnit a ∧ IsUnit b) := by grind
  · have : ¬ IsUnit (a * b) := by simpa [ha.mul_left_iff]
    simp [Ring.inverse_non_unit, hb, this]
  · have : ¬ IsUnit (a * b) := by simpa [hb.mul_right_iff]
    simp [Ring.inverse_non_unit, ha, this]
  · simp [Ring.inverse_of_isUnit, ha, hb, ha.mul hb, ← Units.val_mul, ← mul_inv_rev]
    simp
/-
**Ring.isUnit_iff_inverse_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Ring.isUnit_iff_inverse_ne_zero [Nontrivial M₀] {x : M₀} : IsUnit x ↔ x⁻¹ʳ
 != 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsUnit.ne_zero`：ne_zero [Nontrivial M₀] {a : M₀} (ha : IsUnit a) : a != 
0
· 使用定理 `IsUnit.ringInverse`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] {a : M₀
}, IsUnit a → IsUnit (Ring.inverse a)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Ring.inverse_non_unit`：inverse_non_unit (x : M₀) (h : ¬IsUnit x) : x⁻¹ʳ 
= 0
-/
theorem Ring.isUnit_iff_inverse_ne_zero [Nontrivial M₀] {x : M₀} : IsUnit x ↔ x⁻¹ʳ ≠ 0 :=
  ⟨(IsUnit.ringInverse · |>.ne_zero), by simpa using mt <| Ring.inverse_non_unit (x := x)⟩

grind_pattern Ring.isUnit_iff_inverse_ne_zero => IsUnit x, x⁻¹ʳ
/-
**Ring.not_isUnit_iff_inverse_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Ring.not_isUnit_iff_inverse_eq_zero [Nontrivial M₀] {x : M₀} : ¬ IsUnit x 
↔ x⁻¹ʳ = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Ring.not_isUnit_iff_inverse_eq_zero [Nontrivial M₀] {x : M₀} : ¬ IsUnit x ↔ x⁻¹ʳ = 0 := by
  grind
/-
**Ring.isUnit_iff_mul_inverse_cancel** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Ring.isUnit_iff_mul_inverse_cancel {x : M₀} : IsUnit x ↔ x * x⁻¹ʳ = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Ring.mul_inverse_cancel`：mul_inverse_cancel (x : M₀) (h : IsUnit x) : x 
* x⁻¹ʳ = 1
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Ring.inverse_non_unit`：inverse_non_unit (x : M₀) (h : ¬IsUnit x) : x⁻¹ʳ 
= 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem Ring.isUnit_iff_mul_inverse_cancel {x : M₀} : IsUnit x ↔ x * x⁻¹ʳ = 1 := by
  nontriviality M₀
  refine ⟨mul_inverse_cancel _, ?_⟩
  contrapose
  simp +contextual [not_isUnit_iff_inverse_eq_zero]

grind_pattern Ring.isUnit_iff_mul_inverse_cancel => IsUnit x, x⁻¹ʳ
/-
**Ring.isUnit_iff_inverse_mul_cancel** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Ring.isUnit_iff_inverse_mul_cancel (x : M₀) : IsUnit x ↔ x⁻¹ʳ * x = 1
参数：x : M₀。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Ring.inverse_mul_cancel`：inverse_mul_cancel (x : M₀) (h : IsUnit x) : x⁻
¹ʳ * x = 1
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Ring.inverse_non_unit`：inverse_non_unit (x : M₀) (h : ¬IsUnit x) : x⁻¹ʳ 
= 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem Ring.isUnit_iff_inverse_mul_cancel (x : M₀) : IsUnit x ↔ x⁻¹ʳ * x = 1 := by
  nontriviality M₀
  refine ⟨Ring.inverse_mul_cancel x, ?_⟩
  contrapose
  simp +contextual [not_isUnit_iff_inverse_eq_zero]

grind_pattern Ring.isUnit_iff_inverse_mul_cancel => IsUnit x, x⁻¹ʳ

@[simp, grind =]
/-
**Ring.inverse_inverse_inverse** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Ring.inverse_inverse_inverse {a : M₀} : a⁻¹ʳ⁻¹ʳ⁻¹ʳ = a⁻¹ʳ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ring.inverse_inverse`：inverse_inverse {a : M₀} (h : IsUnit a) : a⁻¹ʳ⁻¹ʳ 
= a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Ring.not_isUnit_iff_inverse_eq_zero`：Ring.not_isUnit_iff_inverse_eq_zero
 [Nontrivial M₀] {x : M₀} : ¬ IsUnit x ↔ x⁻¹ʳ = 0
· 使用定理 `Ring.inverse_non_unit`：inverse_non_unit (x : M₀) (h : ¬IsUnit x) : x⁻¹ʳ 
= 0
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Ring.inverse_inverse_inverse {a : M₀} : a⁻¹ʳ⁻¹ʳ⁻¹ʳ = a⁻¹ʳ := by
  nontriviality M₀
  by_cases h : IsUnit a
  · rw [Ring.inverse_inverse h]
  · simp [Ring.not_isUnit_iff_inverse_eq_zero.mp h]

namespace Units

variable [GroupWithZero G₀]

/-- Embed a non-zero element of a `GroupWithZero` into the unit group.
  By combining this function with the operations on units,
  or the `/ₚ` operation, it is possible to write a division
  as a partial function with three arguments. -/
/-
**Units.mk0** 是 Mathlib 中的一个定义，位于命名空间 `Units`。
形式化陈述：mk0 (a : G₀) (ha : a != 0) : G₀ˣ
参数：a : G₀；ha : a != 0。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `mul_inv_cancel₀`：mul_inv_cancel₀ (h : a != 0) : a * a⁻¹ = 1
· 使用定理 `inv_mul_cancel₀`：inv_mul_cancel₀ (h : a != 0) : a⁻¹ * a = 1

--- 原说明 ---
Embed a non-zero element of a `GroupWithZero` into the unit group.
  By combining this function with the operations on units,
  or the `/ₚ` operation, it is possible to write a division
  as a partial function with three arguments.
-/
def mk0 (a : G₀) (ha : a ≠ 0) : G₀ˣ :=
  ⟨a, a⁻¹, mul_inv_cancel₀ ha, inv_mul_cancel₀ ha⟩

@[simp]
/-
**Units.mk0_one** 是 Mathlib 中的一个定理，位于命名空间 `Units`。
形式化陈述：mk0_one (h
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Units.ext`：ext {u v : αˣ} (huv : u.val = v.val) : u = v
-/
theorem mk0_one (h := one_ne_zero) : mk0 (1 : G₀) h = 1 := by
  ext
  rfl

@[simp]
/-
**Units.val_mk0** 是 Mathlib 中的一个定理，位于命名空间 `Units`。
形式化陈述：val_mk0 {a : G₀} (h : a != 0) : (mk0 a h : G₀) = a
参数：h : a != 0。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem val_mk0 {a : G₀} (h : a ≠ 0) : (mk0 a h : G₀) = a :=
  rfl

@[simp]
/-
**Units.mk0_val** 是 Mathlib 中的一个定理，位于命名空间 `Units`。
形式化陈述：mk0_val (u : G₀ˣ) (h : (u : G₀) != 0) : mk0 (u : G₀) h = u
参数：u : G₀ˣ；h : (u : G₀) != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Units.ext`：ext {u v : αˣ} (huv : u.val = v.val) : u = v
-/
theorem mk0_val (u : G₀ˣ) (h : (u : G₀) ≠ 0) : mk0 (u : G₀) h = u :=
  Units.ext rfl
/-
**Units.mul_inv'** 是 Mathlib 中的一个定理，位于命名空间 `Units`。
形式化陈述：mul_inv' (u : G₀ˣ) : u * (u : G₀)⁻¹ = 1
参数：u : G₀ˣ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `mul_inv_cancel₀`：mul_inv_cancel₀ (h : a != 0) : a * a⁻¹ = 1
· 使用定理 `Units.ne_zero`：ne_zero [Nontrivial M₀] (u : M₀ˣ) : (u : M₀) != 0
· 使用定理 `GroupWithZero.toNontrivial`：∀ {G₀ : Type u} [self : GroupWithZero G₀], N
ontrivial G₀
-/
theorem mul_inv' (u : G₀ˣ) : u * (u : G₀)⁻¹ = 1 :=
  mul_inv_cancel₀ u.ne_zero
/-
**Units.inv_mul'** 是 Mathlib 中的一个定理，位于命名空间 `Units`。
形式化陈述：inv_mul' (u : G₀ˣ) : (u⁻¹ : G₀) * u = 1
参数：u : G₀ˣ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `inv_mul_cancel₀`：inv_mul_cancel₀ (h : a != 0) : a⁻¹ * a = 1
· 使用定理 `Units.ne_zero`：ne_zero [Nontrivial M₀] (u : M₀ˣ) : (u : M₀) != 0
· 使用定理 `GroupWithZero.toNontrivial`：∀ {G₀ : Type u} [self : GroupWithZero G₀], N
ontrivial G₀
-/
theorem inv_mul' (u : G₀ˣ) : (u⁻¹ : G₀) * u = 1 :=
  inv_mul_cancel₀ u.ne_zero

@[simp]
/-
**Units.mk0_inj** 是 Mathlib 中的一个定理，位于命名空间 `Units`。
形式化陈述：mk0_inj {a b : G₀} (ha : a != 0) (hb : b != 0) : Units.mk0 a ha = Units.mk
0 b hb ↔ a = b
参数：ha : a != 0；hb : b != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `mul_inv_cancel₀`：mul_inv_cancel₀ (h : a != 0) : a * a⁻¹ = 1
· 使用定理 `inv_mul_cancel₀`：inv_mul_cancel₀ (h : a != 0) : a⁻¹ * a = 1
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Units.ext`：ext {u v : αˣ} (huv : u.val = v.val) : u = v
-/
theorem mk0_inj {a b : G₀} (ha : a ≠ 0) (hb : b ≠ 0) : Units.mk0 a ha = Units.mk0 b hb ↔ a = b :=
  ⟨fun h => by injection h, fun h => Units.ext h⟩

/-- In a group with zero, an existential over a unit can be rewritten in terms of `Units.mk0`. -/
/-
**Units.exists0** 是 Mathlib 中的一个定理，位于命名空间 `Units`。
形式化陈述：exists0 {p : G₀ˣ -> Prop} : (exists g : G₀ˣ, p g) ↔ exists (g : G₀) (hg : 
g != 0), p (Units.mk0 g hg)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Units.ne_zero`：ne_zero [Nontrivial M₀] (u : M₀ˣ) : (u : M₀) != 0
· 使用定理 `GroupWithZero.toNontrivial`：∀ {G₀ : Type u} [self : GroupWithZero G₀], N
ontrivial G₀
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Units.mk0_val`：mk0_val (u : G₀ˣ) (h : (u : G₀) != 0) : mk0 (u : G₀) h = 
u

--- 原说明 ---
In a group with zero, an existential over a unit can be rewritten in terms of `U
nits.mk0`.
-/
theorem exists0 {p : G₀ˣ → Prop} : (∃ g : G₀ˣ, p g) ↔ ∃ (g : G₀) (hg : g ≠ 0), p (Units.mk0 g hg) :=
  ⟨fun ⟨g, pg⟩ => ⟨g, g.ne_zero, (g.mk0_val g.ne_zero).symm ▸ pg⟩,
  fun ⟨g, hg, pg⟩ => ⟨Units.mk0 g hg, pg⟩⟩

/-- An alternative version of `Units.exists0`. This one is useful if Lean cannot
figure out `p` when using `Units.exists0` from right to left. -/
/-
**Units.exists0'** 是 Mathlib 中的一个定理，位于命名空间 `Units`。
形式化陈述：exists0' {p : forall g : G₀, g != 0 -> Prop} : (exists (g : G₀) (hg : g !=
 0), p g hg) ↔ exists g : G₀ˣ, p g g.ne_zero
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Units.ne_zero`：ne_zero [Nontrivial M₀] (u : M₀ˣ) : (u : M₀) != 0
· 使用定理 `GroupWithZero.toNontrivial`：∀ {G₀ : Type u} [self : GroupWithZero G₀], N
ontrivial G₀
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Units.exists0`：exists0 {p : G₀ˣ -> Prop} : (exists g : G₀ˣ, p g) ↔ exist
s (g : G₀) (hg : g != 0), p (Units.mk0 g hg)

--- 原说明 ---
An alternative version of `Units.exists0`. This one is useful if Lean cannot
figure out `p` when using `Units.exists0` from right to left.
-/
theorem exists0' {p : ∀ g : G₀, g ≠ 0 → Prop} :
    (∃ (g : G₀) (hg : g ≠ 0), p g hg) ↔ ∃ g : G₀ˣ, p g g.ne_zero :=
  Iff.trans (by simp_rw [val_mk0]) exists0.symm

@[simp]
/-
**Units.exists_iff_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Units`。
形式化陈述：exists_iff_ne_zero {p : G₀ -> Prop} : (exists u : G₀ˣ, p u) ↔ exists x != 
0, p x
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
theorem exists_iff_ne_zero {p : G₀ → Prop} : (∃ u : G₀ˣ, p u) ↔ ∃ x ≠ 0, p x := by
  simp [exists0]
/-
**Units._root_.GroupWithZero.eq_zero_or_unit** 是 Mathlib 中的一个定理，位于命名空间 `Units`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.GroupWithZero.eq_zero_or_unit (a : G₀) : a = 0 ∨ ∃ u : G₀ˣ, a = u := by
  simpa using em _

end Units

section GroupWithZero
variable [GroupWithZero G₀] {a b c : G₀} {m n : ℕ}

/-
**IsUnit.mk0** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsUnit.mk0 (x : G₀) (hx : x != 0) : IsUnit x
参数：x : G₀；hx : x != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Units.isUnit`：∀ {M : Type u_1} [inst : Monoid M] (u : Mˣ), IsUnit ↑u
-/
theorem IsUnit.mk0 (x : G₀) (hx : x ≠ 0) : IsUnit x :=
  (Units.mk0 x hx).isUnit

@[simp]
/-
**isUnit_iff_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isUnit_iff_ne_zero : IsUnit a ↔ a != 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Units.exists_iff_ne_zero`：exists_iff_ne_zero {p : G₀ -> Prop} : (exists 
u : G₀ˣ, p u) ↔ exists x != 0, p x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isUnit_iff_ne_zero : IsUnit a ↔ a ≠ 0 :=
  (Units.exists_iff_ne_zero (p := (· = a))).trans (by simp)

protected alias ⟨_, Ne.isUnit⟩ := isUnit_iff_ne_zero

-- see Note [lower instance priority]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 10) GroupWithZero.noZeroDivisors : NoZeroDivisors G₀ :=
  { (‹_› : GroupWithZero G₀) with
    eq_zero_or_eq_zero_of_mul_eq_zero := @fun a b h => by
      contrapose! h
      exact (Units.mk0 a h.1 * Units.mk0 b h.2).ne_zero }

-- Can't be put next to the other `mk0` lemmas because it depends on the
-- `NoZeroDivisors` instance, which depends on `mk0`.
@[simp]
/-
**Units.mk0_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Units.mk0_mul (x y : G₀) (hxy) : Units.mk0 (x * y) hxy = Units.mk0 x (mul_
ne_zero_iff.mp hxy).1 * Units.mk0 y (mul_ne_zero_iff.mp hxy).2
参数：x y : G₀；hxy。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Units.ext`：ext {u v : αˣ} (huv : u.val = v.val) : u = v
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mul_ne_zero_iff`：mul_ne_zero_iff : a * b != 0 ↔ a != 0 ∧ b != 0
· 使用定理 `GroupWithZero.noZeroDivisors`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀
], NoZeroDivisors G₀
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem Units.mk0_mul (x y : G₀) (hxy) :
    Units.mk0 (x * y) hxy =
      Units.mk0 x (mul_ne_zero_iff.mp hxy).1 * Units.mk0 y (mul_ne_zero_iff.mp hxy).2 := by
  ext; rfl
/-
**div_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：div_ne_zero (ha : a != 0) (hb : b != 0) : a / b != 0
参数：ha : a != 0；hb : b != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `mul_ne_zero`：mul_ne_zero (ha : a != 0) (hb : b != 0) : a * b != 0
· 使用定理 `GroupWithZero.noZeroDivisors`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀
], NoZeroDivisors G₀
· 使用定理 `inv_ne_zero`：inv_ne_zero (h : a != 0) : a⁻¹ != 0
-/
theorem div_ne_zero (ha : a ≠ 0) (hb : b ≠ 0) : a / b ≠ 0 := by
  rw [div_eq_mul_inv]
  exact mul_ne_zero ha (inv_ne_zero hb)

@[simp]
/-
**div_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：div_eq_zero_iff : a / b = 0 ↔ a = 0 ∨ b = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `GroupWithZero.noZeroDivisors`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀
], NoZeroDivisors G₀
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem div_eq_zero_iff : a / b = 0 ↔ a = 0 ∨ b = 0 := by simp [div_eq_mul_inv]
/-
**div_ne_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：div_ne_zero_iff : a / b != 0 ↔ a != 0 ∧ b != 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `div_eq_zero_iff`：div_eq_zero_iff : a / b = 0 ↔ a = 0 ∨ b = 0
· 使用定理 `not_or`：∀ {p q : Prop}, ¬(p ∨ q) ↔ ¬p ∧ ¬q
-/
theorem div_ne_zero_iff : a / b ≠ 0 ↔ a ≠ 0 ∧ b ≠ 0 :=
  div_eq_zero_iff.not.trans not_or
/-
**div_self** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a : G₀}, a ≠ 0 → a / a = 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsUnit.div_self`：∀ {α : Type u} [inst : DivisionMonoid α] {a : α}, IsUni
t a → a / a = 1
· 使用定理 `Ne.isUnit`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a : G₀}, a ≠ 0 →
 IsUnit a
-/
@[simp] lemma div_self (h : a ≠ 0) : a / a = 1 := h.isUnit.div_self

@[simp]
/-
**div_self_eq_one** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma div_self_eq_one₀ : a / a = 1 ↔ a ≠ 0 where
  mp := by contrapose!; simp +contextual
  mpr := div_self
/-
**eq_mul_inv_iff_mul_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：eq_mul_inv_iff_mul_eq : a = b * c⁻¹ ↔ a * c = b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inv_mul_cancel_right`：inv_mul_cancel_right (a b : G) : a * b⁻¹ * b = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_inv_cancel_right`：mul_inv_cancel_right (a b : G) : a * b * b⁻¹ = a
-/
lemma eq_mul_inv_iff_mul_eq₀ (hc : c ≠ 0) : a = b * c⁻¹ ↔ a * c = b :=
  hc.isUnit.eq_mul_inv_iff_mul_eq
/-
**eq_inv_mul_iff_mul_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：eq_inv_mul_iff_mul_eq : a = b⁻¹ * c ↔ b * a = c
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_inv_cancel_left`：mul_inv_cancel_left (a b : G) : a * (a⁻¹ * b) = b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `inv_mul_cancel_left`：inv_mul_cancel_left (a b : G) : a⁻¹ * (a * b) = b
-/
lemma eq_inv_mul_iff_mul_eq₀ (hb : b ≠ 0) : a = b⁻¹ * c ↔ b * a = c :=
  hb.isUnit.eq_inv_mul_iff_mul_eq
/-
**inv_mul_eq_iff_eq_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：inv_mul_eq_iff_eq_mul : a⁻¹ * b = c ↔ b = a * c
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_inv_cancel_left`：mul_inv_cancel_left (a b : G) : a * (a⁻¹ * b) = b
· 使用定理 `inv_mul_cancel_left`：inv_mul_cancel_left (a b : G) : a⁻¹ * (a * b) = b
-/
lemma inv_mul_eq_iff_eq_mul₀ (ha : a ≠ 0) : a⁻¹ * b = c ↔ b = a * c :=
  ha.isUnit.inv_mul_eq_iff_eq_mul
/-
**mul_inv_eq_iff_eq_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_inv_eq_iff_eq_mul : a * b⁻¹ = c ↔ a = c * b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `inv_mul_cancel_right`：inv_mul_cancel_right (a b : G) : a * b⁻¹ * b = a
· 使用定理 `mul_inv_cancel_right`：mul_inv_cancel_right (a b : G) : a * b * b⁻¹ = a
-/
lemma mul_inv_eq_iff_eq_mul₀ (hb : b ≠ 0) : a * b⁻¹ = c ↔ a = c * b :=
  hb.isUnit.mul_inv_eq_iff_eq_mul
/-
**mul_inv_eq_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_inv_eq_one : a * b⁻¹ = 1 ↔ a = b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_eq_one_iff_eq_inv`：mul_eq_one_iff_eq_inv : a * b = 1 ↔ a = b⁻¹
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma mul_inv_eq_one₀ (hb : b ≠ 0) : a * b⁻¹ = 1 ↔ a = b := hb.isUnit.mul_inv_eq_one
/-
**inv_mul_eq_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：inv_mul_eq_one : a⁻¹ * b = 1 ↔ a = b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_eq_one_iff_eq_inv`：mul_eq_one_iff_eq_inv : a * b = 1 ↔ a = b⁻¹
· 使用定理 `inv_inj`：inv_inj : a⁻¹ = b⁻¹ ↔ a = b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma inv_mul_eq_one₀ (ha : a ≠ 0) : a⁻¹ * b = 1 ↔ a = b := ha.isUnit.inv_mul_eq_one
/-
**mul_eq_one_iff_eq_inv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_eq_one_iff_eq_inv : a * b = 1 ↔ a = b⁻¹
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_inv_of_mul_eq_one_left`：eq_inv_of_mul_eq_one_left (h : a * b = 1) : a
 = b⁻¹
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inv_mul_cancel`：inv_mul_cancel (a : G) : a⁻¹ * a = 1
-/
lemma mul_eq_one_iff_eq_inv₀ (hb : b ≠ 0) : a * b = 1 ↔ a = b⁻¹ := hb.isUnit.mul_eq_one_iff_eq_inv
/-
**mul_eq_one_iff_inv_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_eq_one_iff_inv_eq : a * b = 1 ↔ a⁻¹ = b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_eq_one_iff_eq_inv`：mul_eq_one_iff_eq_inv : a * b = 1 ↔ a = b⁻¹
· 使用定理 `inv_eq_iff_eq_inv`：inv_eq_iff_eq_inv : a⁻¹ = b ↔ a = b⁻¹
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma mul_eq_one_iff_inv_eq₀ (ha : a ≠ 0) : a * b = 1 ↔ a⁻¹ = b := ha.isUnit.mul_eq_one_iff_inv_eq

/-- A variant of `eq_mul_inv_iff_mul_eq₀` that moves the nonzero hypothesis to another variable. -/
/-
**mul_eq_of_eq_mul_inv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_eq_of_eq_mul_inv (h : a = c * b⁻¹) : a * b = c
参数：h : a = c * b⁻¹。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `inv_mul_cancel`：inv_mul_cancel (a : G) : a⁻¹ * a = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
A variant of `eq_mul_inv_iff_mul_eq₀` that moves the nonzero hypothesis to anoth
er variable.
-/
lemma mul_eq_of_eq_mul_inv₀ (ha : a ≠ 0) (h : a = c * b⁻¹) : a * b = c := by
  rwa [← eq_mul_inv_iff_mul_eq₀]; rintro rfl; simp [ha] at h

/-- A variant of `eq_inv_mul_iff_mul_eq₀` that moves the nonzero hypothesis to another variable. -/
/-
**mul_eq_of_eq_inv_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_eq_of_eq_inv_mul (h : b = a⁻¹ * c) : a * b = c
参数：h : b = a⁻¹ * c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_inv_cancel_left`：mul_inv_cancel_left (a b : G) : a * (a⁻¹ * b) = b

--- 原说明 ---
A variant of `eq_inv_mul_iff_mul_eq₀` that moves the nonzero hypothesis to anoth
er variable.
-/
lemma mul_eq_of_eq_inv_mul₀ (hb : b ≠ 0) (h : b = a⁻¹ * c) : a * b = c := by
  rwa [← eq_inv_mul_iff_mul_eq₀]; rintro rfl; simp [hb] at h

/-- A variant of `inv_mul_eq_iff_eq_mul₀` that moves the nonzero hypothesis to another variable. -/
/-
**eq_mul_of_inv_mul_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：eq_mul_of_inv_mul_eq (h : b⁻¹ * a = c) : a = b * c
参数：h : b⁻¹ * a = c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_inv_cancel_left`：mul_inv_cancel_left (a b : G) : a * (a⁻¹ * b) = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
A variant of `inv_mul_eq_iff_eq_mul₀` that moves the nonzero hypothesis to anoth
er variable.
-/
lemma eq_mul_of_inv_mul_eq₀ (hc : c ≠ 0) (h : b⁻¹ * a = c) : a = b * c :=
  (mul_eq_of_eq_inv_mul₀ hc h.symm).symm

/-- A variant of `mul_inv_eq_iff_eq_mul₀` that moves the nonzero hypothesis to another variable. -/
/-
**eq_mul_of_mul_inv_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：eq_mul_of_mul_inv_eq (h : a * c⁻¹ = b) : a = b * c
参数：h : a * c⁻¹ = b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `inv_mul_cancel`：inv_mul_cancel (a : G) : a⁻¹ * a = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
A variant of `mul_inv_eq_iff_eq_mul₀` that moves the nonzero hypothesis to anoth
er variable.
-/
lemma eq_mul_of_mul_inv_eq₀ (hb : b ≠ 0) (h : a * c⁻¹ = b) : a = b * c :=
  (mul_eq_of_eq_mul_inv₀ hb h.symm).symm
/-
**div_mul_cancel** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：div_mul_cancel (a b : G) : a / b * b = a
参数：a b : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `inv_mul_cancel_right`：inv_mul_cancel_right (a b : G) : a * b⁻¹ * b = a
-/
lemma div_mul_cancel₀ (a : G₀) (h : b ≠ 0) : a / b * b = a := by simp [h]
/-
**mul_one_div_cancel** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：mul_one_div_cancel (h : a != 0) : a * (1 / a) = 1
参数：h : a != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsUnit.mul_one_div_cancel`：∀ {α : Type u} [inst : DivisionMonoid α] {a :
 α}, IsUnit a → a * (1 / a) = 1
· 使用定理 `Ne.isUnit`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a : G₀}, a ≠ 0 →
 IsUnit a
-/
lemma mul_one_div_cancel (h : a ≠ 0) : a * (1 / a) = 1 := h.isUnit.mul_one_div_cancel
/-
**one_div_mul_cancel** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：one_div_mul_cancel (h : a != 0) : 1 / a * a = 1
参数：h : a != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsUnit.one_div_mul_cancel`：∀ {α : Type u} [inst : DivisionMonoid α] {a :
 α}, IsUnit a → 1 / a * a = 1
· 使用定理 `Ne.isUnit`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a : G₀}, a ≠ 0 →
 IsUnit a
-/
lemma one_div_mul_cancel (h : a ≠ 0) : 1 / a * a = 1 := h.isUnit.one_div_mul_cancel

@[simp]
/-
**div_left_inj'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：div_left_inj' (hc : c != 0) : a / c = b / c ↔ a = b
参数：hc : c != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsUnit.div_left_inj`：∀ {α : Type u} [inst : DivisionMonoid α] {a b c : α
}, IsUnit c → (a / c = b / c ↔ a = b)
· 使用定理 `Ne.isUnit`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a : G₀}, a ≠ 0 →
 IsUnit a
-/
lemma div_left_inj' (hc : c ≠ 0) : a / c = b / c ↔ a = b := hc.isUnit.div_left_inj
/-
**div_eq_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：div_eq_iff (hb : b != 0) : a / b = c ↔ a = c * b
参数：hb : b != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsUnit.div_eq_iff`：∀ {α : Type u} [inst : DivisionMonoid α] {a b c : α},
 IsUnit b → (a / b = c ↔ a = c * b)
· 使用定理 `Ne.isUnit`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a : G₀}, a ≠ 0 →
 IsUnit a
-/
lemma div_eq_iff (hb : b ≠ 0) : a / b = c ↔ a = c * b := hb.isUnit.div_eq_iff
/-
**eq_div_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：eq_div_iff (hb : b != 0) : c = a / b ↔ c * b = a
参数：hb : b != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsUnit.eq_div_iff`：∀ {α : Type u} [inst : DivisionMonoid α] {a b c : α},
 IsUnit c → (a = b / c ↔ a * c = b)
· 使用定理 `Ne.isUnit`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a : G₀}, a ≠ 0 →
 IsUnit a
-/
lemma eq_div_iff (hb : b ≠ 0) : c = a / b ↔ c * b = a := hb.isUnit.eq_div_iff

-- TODO: Swap RHS around
/-
**div_eq_iff_mul_eq** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：div_eq_iff_mul_eq (hb : b != 0) : a / b = c ↔ c * b = a
参数：hb : b != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `IsUnit.div_eq_iff`：∀ {α : Type u} [inst : DivisionMonoid α] {a b c : α},
 IsUnit b → (a / b = c ↔ a = c * b)
· 使用定理 `Ne.isUnit`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a : G₀}, a ≠ 0 →
 IsUnit a
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
-/
lemma div_eq_iff_mul_eq (hb : b ≠ 0) : a / b = c ↔ c * b = a := hb.isUnit.div_eq_iff.trans eq_comm
/-
**eq_div_iff_mul_eq** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：eq_div_iff_mul_eq (hc : c != 0) : a = b / c ↔ a * c = b
参数：hc : c != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsUnit.eq_div_iff`：∀ {α : Type u} [inst : DivisionMonoid α] {a b c : α},
 IsUnit c → (a = b / c ↔ a * c = b)
· 使用定理 `Ne.isUnit`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a : G₀}, a ≠ 0 →
 IsUnit a
-/
lemma eq_div_iff_mul_eq (hc : c ≠ 0) : a = b / c ↔ a * c = b := hc.isUnit.eq_div_iff
/-
**div_eq_of_eq_mul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：div_eq_of_eq_mul (hb : b != 0) : a = c * b -> a / b = c
参数：hb : b != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsUnit.div_eq_of_eq_mul`：∀ {α : Type u} [inst : DivisionMonoid α] {a b c
 : α}, IsUnit b → a = c * b → a / b = c
· 使用定理 `Ne.isUnit`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a : G₀}, a ≠ 0 →
 IsUnit a
-/
lemma div_eq_of_eq_mul (hb : b ≠ 0) : a = c * b → a / b = c := hb.isUnit.div_eq_of_eq_mul
/-
**eq_div_of_mul_eq** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：eq_div_of_mul_eq (hc : c != 0) : a * c = b -> a = b / c
参数：hc : c != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsUnit.eq_div_of_mul_eq`：∀ {α : Type u} [inst : DivisionMonoid α] {a b c
 : α}, IsUnit c → a * c = b → a = b / c
· 使用定理 `Ne.isUnit`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a : G₀}, a ≠ 0 →
 IsUnit a
-/
lemma eq_div_of_mul_eq (hc : c ≠ 0) : a * c = b → a = b / c := hc.isUnit.eq_div_of_mul_eq
/-
**div_eq_one_iff_eq** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：div_eq_one_iff_eq (hb : b != 0) : a / b = 1 ↔ a = b
参数：hb : b != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsUnit.div_eq_one_iff_eq`：∀ {α : Type u} [inst : DivisionMonoid α] {a b 
: α}, IsUnit b → (a / b = 1 ↔ a = b)
· 使用定理 `Ne.isUnit`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a : G₀}, a ≠ 0 →
 IsUnit a
-/
lemma div_eq_one_iff_eq (hb : b ≠ 0) : a / b = 1 ↔ a = b := hb.isUnit.div_eq_one_iff_eq
/-
**div_mul_cancel_right** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：div_mul_cancel_right (a b : G) : a / (b * a) = b⁻¹
参数：a b : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `inv_div`：inv_div : (a / b)⁻¹ = b / a
· 使用定理 `mul_div_cancel_right`：mul_div_cancel_right (a b : G) : a * b / b = a
-/
lemma div_mul_cancel_right₀ (hb : b ≠ 0) (a : G₀) : b / (a * b) = a⁻¹ :=
  hb.isUnit.div_mul_cancel_right _
/-
**mul_div_mul_right** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：mul_div_mul_right (a b : G₀) (hc : c != 0) : a * c / (b * c) = a / b
参数：a b : G₀；hc : c != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsUnit.mul_div_mul_right`：∀ {α : Type u} [inst : DivisionMonoid α] {c : 
α}, IsUnit c → ∀ (a b : α), a * c / (b * c) = a / b
· 使用定理 `Ne.isUnit`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a : G₀}, a ≠ 0 →
 IsUnit a
-/
lemma mul_div_mul_right (a b : G₀) (hc : c ≠ 0) : a * c / (b * c) = a / b :=
  hc.isUnit.mul_div_mul_right _ _

-- TODO: Duplicate of `mul_inv_cancel_right₀`
/-
**mul_mul_div** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：mul_mul_div (a : G₀) (hb : b != 0) : a = a * b * (1 / b)
参数：a : G₀；hb : b != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsUnit.mul_mul_div`：∀ {α : Type u} [inst : DivisionMonoid α] {b : α} (a 
: α), IsUnit b → a * b * (1 / b) = a
· 使用定理 `Ne.isUnit`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a : G₀}, a ≠ 0 →
 IsUnit a
-/
lemma mul_mul_div (a : G₀) (hb : b ≠ 0) : a = a * b * (1 / b) := (hb.isUnit.mul_mul_div _).symm
/-
**div_div_div_cancel_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：div_div_div_cancel_right (a b c : G) : a / c / (b / c) = a / b
参数：a b c : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `inv_div`：inv_div : (a / b)⁻¹ = b / a
· 使用定理 `div_inv_eq_mul`：div_inv_eq_mul : a / b⁻¹ = a * b
· 使用定理 `div_mul_div_cancel`：div_mul_div_cancel (a b c : G) : a / b * (b / c) = a
 / c
-/
lemma div_div_div_cancel_right₀ (hc : c ≠ 0) (a b : G₀) : a / c / (b / c) = a / b := by
  rw [div_div_eq_mul_div, div_mul_cancel₀ _ hc]
/-
**div_mul_div_cancel** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：div_mul_div_cancel (a b c : G) : a / b * (b / c) = a / c
参数：a b c : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_div_assoc`：mul_div_assoc (a b c : G) : a * b / c = a * (b / c)
· 使用定理 `div_mul_cancel`：div_mul_cancel (a b : G) : a / b * b = a
-/
lemma div_mul_div_cancel₀ (hb : b ≠ 0) : a / b * (b / c) = a / c := by
  rw [← mul_div_assoc, div_mul_cancel₀ _ hb]
/-
**div_mul_cancel_of_imp** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：div_mul_cancel_of_imp (h : b = 0 -> a = 0) : a / b * b = a
参数：h : b = 0 -> a = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `div_zero`：div_zero (a : G₀) : a / 0 = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsUnit.div_mul_cancel`：∀ {α : Type u} [inst : DivisionMonoid α] {b : α},
 IsUnit b → ∀ (a : α), a / b * b = a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
lemma div_mul_cancel_of_imp (h : b = 0 → a = 0) : a / b * b = a := by
  obtain rfl | hb := eq_or_ne b 0 <;> simp [*]
/-
**mul_div_cancel_of_imp** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：mul_div_cancel_of_imp (h : b = 0 -> a = 0) : a * b / b = a
参数：h : b = 0 -> a = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `div_zero`：div_zero (a : G₀) : a / 0 = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsUnit.mul_div_cancel_right`：∀ {α : Type u} [inst : DivisionMonoid α] {b
 : α}, IsUnit b → ∀ (a : α), a * b / b = a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
lemma mul_div_cancel_of_imp (h : b = 0 → a = 0) : a * b / b = a := by
  obtain rfl | hb := eq_or_ne b 0 <;> simp [*]
/-
**divp_mk0** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {b : G₀} (a : G₀) (hb : b ≠ 0)
, a /ₚ Units.mk0 b hb = a / b
参数：a : G₀；hb : b ≠ 0。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `divp_eq_div`：divp_eq_div [DivisionMonoid α] (a : α) (u : αˣ) : a /ₚ u = 
a / u
-/
@[simp] lemma divp_mk0 (a : G₀) (hb : b ≠ 0) : a /ₚ Units.mk0 b hb = a / b := divp_eq_div _ _
/-
**pow_sub** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：pow_sub (a : G) {m n : Nat} (h : n <= m) : a ^ (m - n) = a ^ m * (a ^ n)⁻¹
参数：a : G；h : n <= m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_mul_inv_of_mul_eq`：eq_mul_inv_of_mul_eq (h : a * c = b) : a = b * c⁻¹
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `pow_add`：pow_add {b₁ b₂ : Nat} {d : R} (_ : a ^ b₁ = c₁) (_ : a ^ b₂ = c
₂) (_ : c₁ * c₂ = d) : (a : R) ^ (b₁ + b₂) = d
· 使用定理 `Nat.sub_add_cancel`：∀ {n m : ℕ}, m ≤ n → n - m + m = n
-/
lemma pow_sub₀ (a : G₀) (ha : a ≠ 0) (h : n ≤ m) : a ^ (m - n) = a ^ m * (a ^ n)⁻¹ := by
  have h1 : m - n + n = m := Nat.sub_add_cancel h
  have h2 : a ^ (m - n) * a ^ n = a ^ m := by rw [← pow_add, h1]
  simpa only [div_eq_mul_inv] using eq_div_of_mul_eq (pow_ne_zero _ ha) h2
/-
**pow_sub_of_lt** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：pow_sub_of_lt (a : G₀) (h : n < m) : a ^ (m - n) = a ^ m * (a ^ n)⁻¹
参数：a : G₀；h : n < m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用定理 `Nat.ne_of_gt`：∀ {a b : ℕ}, b < a → a ≠ b
· 使用定理 `Nat.sub_pos_of_lt`：∀ {m n : ℕ}, m < n → 0 < n - m
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `pow_sub₀`：pow_sub₀ (a : G₀) (ha : a != 0) (h : n <= m) : a ^ (m - n) = a
 ^ m * (a ^ n)⁻¹
· 使用定理 `Nat.le_of_lt`：∀ {n m : ℕ}, n < m → n ≤ m
-/
lemma pow_sub_of_lt (a : G₀) (h : n < m) : a ^ (m - n) = a ^ m * (a ^ n)⁻¹ := by
  obtain rfl | ha := eq_or_ne a 0
  · rw [zero_pow (Nat.ne_of_gt <| Nat.sub_pos_of_lt h), zero_pow (by lia), zero_mul]
  · exact pow_sub₀ _ ha <| Nat.le_of_lt h
/-
**inv_pow_sub** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：inv_pow_sub (a : G) {m n : Nat} (h : n <= m) : a⁻¹ ^ (m - n) = (a ^ m)⁻¹ *
 a ^ n
参数：a : G；h : n <= m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `pow_sub`：pow_sub (a : G) {m n : Nat} (h : n <= m) : a ^ (m - n) = a ^ m 
* (a ^ n)⁻¹
· 使用定理 `inv_pow`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℕ), a⁻¹
 ^ n = (a ^ n)⁻¹
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
-/
lemma inv_pow_sub₀ (ha : a ≠ 0) (h : n ≤ m) : a⁻¹ ^ (m - n) = (a ^ m)⁻¹ * a ^ n := by
  rw [pow_sub₀ _ (inv_ne_zero ha) h, inv_pow, inv_pow, inv_inv]
/-
**inv_pow_sub_of_lt** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：inv_pow_sub_of_lt (a : G₀) (h : n < m) : a⁻¹ ^ (m - n) = (a ^ m)⁻¹ * a ^ n
参数：a : G₀；h : n < m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `pow_sub_of_lt`：pow_sub_of_lt (a : G₀) (h : n < m) : a ^ (m - n) = a ^ m 
* (a ^ n)⁻¹
· 使用定理 `inv_pow`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℕ), a⁻¹
 ^ n = (a ^ n)⁻¹
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
-/
lemma inv_pow_sub_of_lt (a : G₀) (h : n < m) : a⁻¹ ^ (m - n) = (a ^ m)⁻¹ * a ^ n := by
  rw [pow_sub_of_lt a⁻¹ h, inv_pow, inv_pow, inv_inv]
/-
**zpow_sub** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {G : Type u_3} [inst : Group G] (a : G) (m n : ℤ), a ^ (m - n) = a ^ m *
 (a ^ n)⁻¹
参数：a : G；m n : ℤ；m - n；a ^ n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.sub_eq_add_neg`：∀ {a b : ℤ}, a - b = a + -b
· 使用引理 `zpow_add`：zpow_add (a : G) (m n : Int) : a ^ (m + n) = a ^ m * a ^ n
· 使用定理 `zpow_neg`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℤ), a 
^ (-n) = (a ^ n)⁻¹
-/
lemma zpow_sub₀ (ha : a ≠ 0) (m n : ℤ) : a ^ (m - n) = a ^ m / a ^ n := by
  rw [Int.sub_eq_add_neg, zpow_add₀ ha, zpow_neg, div_eq_mul_inv]
/-
**zpow_natCast_sub_natCast** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：zpow_natCast_sub_natCast (a : G) (m n : Nat) : a ^ (m - n : Int) = a ^ m /
 a ^ n
参数：a : G；m n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `zpow_natCast`：zpow_natCast (a : G) : forall n : Nat, a ^ (n : Int) = a ^
 n | 0 => (zpow_zero _).trans (pow_zero _).symm | n + 1 => calc a ^ (↑(n + 1) : 
In…
· 使用定理 `zpow_sub`：∀ {G : Type u_3} [inst : Group G] (a : G) (m n : ℤ), a ^ (m - 
n) = a ^ m * (a ^ n)⁻¹
-/
lemma zpow_natCast_sub_natCast₀ (ha : a ≠ 0) (m n : ℕ) : a ^ (m - n : ℤ) = a ^ m / a ^ n := by
  simpa using zpow_sub₀ ha m n
/-
**zpow_natCast_sub_one** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：zpow_natCast_sub_one (a : G) (n : Nat) : a ^ (n - 1 : Int) = a ^ n / a
参数：a : G；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `zpow_natCast`：zpow_natCast (a : G) : forall n : Nat, a ^ (n : Int) = a ^
 n | 0 => (zpow_zero _).trans (pow_zero _).symm | n + 1 => calc a ^ (↑(n + 1) : 
In…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `zpow_ofNat`：zpow_ofNat (a : G) (n : Nat) : a ^ (ofNat(n) : Int) = a ^ Of
Nat.ofNat n
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `zpow_sub`：∀ {G : Type u_3} [inst : Group G] (a : G) (m n : ℤ), a ^ (m - 
n) = a ^ m * (a ^ n)⁻¹
-/
lemma zpow_natCast_sub_one₀ (ha : a ≠ 0) (n : ℕ) : a ^ (n - 1 : ℤ) = a ^ n / a := by
  simpa using zpow_sub₀ ha n 1
/-
**zpow_one_sub_natCast** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：zpow_one_sub_natCast (a : G) (n : Nat) : a ^ (1 - n : Int) = a / a ^ n
参数：a : G；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `zpow_ofNat`：zpow_ofNat (a : G) (n : Nat) : a ^ (ofNat(n) : Int) = a ^ Of
Nat.ofNat n
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `zpow_natCast`：zpow_natCast (a : G) : forall n : Nat, a ^ (n : Int) = a ^
 n | 0 => (zpow_zero _).trans (pow_zero _).symm | n + 1 => calc a ^ (↑(n + 1) : 
In…
· 使用定理 `zpow_sub`：∀ {G : Type u_3} [inst : Group G] (a : G) (m n : ℤ), a ^ (m - 
n) = a ^ m * (a ^ n)⁻¹
-/
lemma zpow_one_sub_natCast₀ (ha : a ≠ 0) (n : ℕ) : a ^ (1 - n : ℤ) = a / a ^ n := by
  simpa using zpow_sub₀ ha 1 n
/-
**zpow_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a : G₀} (n : ℤ), a ≠ 0 → a ^ 
n ≠ 0
参数：n : ℤ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zpow_natCast`：zpow_natCast (a : G) : forall n : Nat, a ^ (n : Int) = a ^
 n | 0 => (zpow_zero _).trans (pow_zero _).symm | n + 1 => calc a ^ (↑(n + 1) : 
In…
· 使用引理 `pow_ne_zero`：pow_ne_zero (n : Nat) (h : a != 0) : a ^ n != 0
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `GroupWithZero.noZeroDivisors`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀
], NoZeroDivisors G₀
· 使用定理 `zpow_negSucc`：zpow_negSucc (a : G) (n : Nat) : a ^ (Int.negSucc n) = (a 
^ (n + 1))⁻¹
· 使用定理 `inv_ne_zero`：inv_ne_zero (h : a != 0) : a⁻¹ != 0
-/
lemma zpow_ne_zero {a : G₀} : ∀ n : ℤ, a ≠ 0 → a ^ n ≠ 0
  | (_ : ℕ) => by rw [zpow_natCast]; exact pow_ne_zero _
  | .negSucc n => fun ha ↦ by rw [zpow_negSucc]; exact inv_ne_zero (pow_ne_zero _ ha)
/-
**eq_zero_of_zpow_eq_zero** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：eq_zero_of_zpow_eq_zero {n : Int} : a ^ n = 0 -> a = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_imp_not`：not_imp_not : ¬a -> ¬b ↔ b -> a
· 使用定理 `zpow_ne_zero`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a : G₀} (n : 
ℤ), a ≠ 0 → a ^ n ≠ 0
-/
lemma eq_zero_of_zpow_eq_zero {n : ℤ} : a ^ n = 0 → a = 0 := not_imp_not.1 (zpow_ne_zero _)
/-
**zpow_eq_zero_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：zpow_eq_zero_iff {n : Int} (hn : n != 0) : a ^ n = 0 ↔ a = 0
参数：hn : n != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `eq_zero_of_zpow_eq_zero`：eq_zero_of_zpow_eq_zero {n : Int} : a ^ n = 0 -
> a = 0
· 使用定理 `zero_zpow`：∀ {G₀ : Type u_2} [inst : GroupWithZero G₀] (n : ℤ), n ≠ 0 → 
0 ^ n = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma zpow_eq_zero_iff {n : ℤ} (hn : n ≠ 0) : a ^ n = 0 ↔ a = 0 :=
  ⟨eq_zero_of_zpow_eq_zero, fun ha => ha.symm ▸ zero_zpow _ hn⟩
/-
**zpow_ne_zero_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：zpow_ne_zero_iff {n : Int} (hn : n != 0) : a ^ n != 0 ↔ a != 0
参数：hn : n != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.ne`：∀ {α : Sort u_1} {β : Sort u_2} {a b : α} {c d : β}, (a = b ↔ c 
= d) → (a ≠ b ↔ c ≠ d)
· 使用引理 `zpow_eq_zero_iff`：zpow_eq_zero_iff {n : Int} (hn : n != 0) : a ^ n = 0 ↔
 a = 0
-/
lemma zpow_ne_zero_iff {n : ℤ} (hn : n ≠ 0) : a ^ n ≠ 0 ↔ a ≠ 0 := (zpow_eq_zero_iff hn).ne
/-
**zpow_neg_mul_zpow_self** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：zpow_neg_mul_zpow_self (n : Int) (ha : a != 0) : a ^ (-n) * a ^ n = 1
参数：n : Int；ha : a != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zpow_neg`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℤ), a 
^ (-n) = (a ^ n)⁻¹
· 使用定理 `inv_mul_cancel₀`：inv_mul_cancel₀ (h : a != 0) : a⁻¹ * a = 1
· 使用定理 `zpow_ne_zero`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a : G₀} (n : 
ℤ), a ≠ 0 → a ^ n ≠ 0
-/
lemma zpow_neg_mul_zpow_self (n : ℤ) (ha : a ≠ 0) : a ^ (-n) * a ^ n = 1 := by
  rw [zpow_neg]; exact inv_mul_cancel₀ (zpow_ne_zero n ha)

@[grind =]
/-
**Ring.inverse_eq_inv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Ring.inverse_eq_inv (a : G₀) : a⁻¹ʳ = a⁻¹
参数：a : G₀。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ring.inverse_non_unit`：inverse_non_unit (x : M₀) (h : ¬IsUnit x) : x⁻¹ʳ 
= 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `inv_zero`：∀ {G₀ : Type u} [inst : GroupWithZero G₀], 0⁻¹ = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ring.inverse_unit`：inverse_unit (u : M₀ˣ) : (u : M₀)⁻¹ʳ = (u⁻¹ : M₀ˣ)
-/
theorem Ring.inverse_eq_inv (a : G₀) : a⁻¹ʳ = a⁻¹ := by
  obtain rfl | ha := eq_or_ne a 0
  · simp
  · exact Ring.inverse_unit (Units.mk0 a ha)

@[simp]
/-
**Ring.inverse_eq_inv'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Ring.inverse_eq_inv' : (Ring.inverse : G₀ -> G₀) = Inv.inv
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Ring.inverse_eq_inv`：Ring.inverse_eq_inv (a : G₀) : a⁻¹ʳ = a⁻¹
-/
theorem Ring.inverse_eq_inv' : (Ring.inverse : G₀ → G₀) = Inv.inv :=
  funext Ring.inverse_eq_inv

end GroupWithZero

section CommGroupWithZero

-- comm
variable [CommGroupWithZero G₀] {a b c d : G₀}

-- See note [lower instance priority]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) CommGroupWithZero.toDivisionCommMonoid :
    DivisionCommMonoid G₀ where
  __ := ‹CommGroupWithZero G₀›
  __ := GroupWithZero.toDivisionMonoid
/-
**div_mul_cancel_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：div_mul_cancel_left (a b : G) : a / (a * b) = b⁻¹
参数：a b : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `inv_div`：inv_div : (a / b)⁻¹ = b / a
· 使用定理 `mul_div_cancel_left`：mul_div_cancel_left (a b : G) : a * b / a = b
-/
lemma div_mul_cancel_left₀ (ha : a ≠ 0) (b : G₀) : a / (a * b) = b⁻¹ :=
  ha.isUnit.div_mul_cancel_left _
/-
**mul_div_cancel_left_of_imp** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：mul_div_cancel_left_of_imp (h : a = 0 -> b = 0) : a * b / a = b
参数：h : a = 0 -> b = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用引理 `mul_div_cancel_of_imp`：mul_div_cancel_of_imp (h : b = 0 -> a = 0) : a * 
b / b = a
-/
lemma mul_div_cancel_left_of_imp (h : a = 0 → b = 0) : a * b / a = b := by
  rw [mul_comm, mul_div_cancel_of_imp h]
/-
**mul_div_cancel_of_imp'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：mul_div_cancel_of_imp' (h : b = 0 -> a = 0) : b * (a / b) = a
参数：h : b = 0 -> a = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用引理 `div_mul_cancel_of_imp`：div_mul_cancel_of_imp (h : b = 0 -> a = 0) : a / 
b * b = a
-/
lemma mul_div_cancel_of_imp' (h : b = 0 → a = 0) : b * (a / b) = a := by
  rw [mul_comm, div_mul_cancel_of_imp h]
/-
**mul_div_cancel** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_div_cancel (a b : G) : a * (b / a) = b
参数：a b : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_div_assoc`：mul_div_assoc (a b c : G) : a * b / c = a * (b / c)
· 使用定理 `mul_div_cancel_left`：mul_div_cancel_left (a b : G) : a * b / a = b
-/
lemma mul_div_cancel₀ (a : G₀) (hb : b ≠ 0) : b * (a / b) = a :=
  hb.isUnit.mul_div_cancel _
/-
**mul_div_mul_left** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：mul_div_mul_left (a b : G₀) (hc : c != 0) : c * a / (c * b) = a / b
参数：a b : G₀；hc : c != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsUnit.mul_div_mul_left`：∀ {α : Type u} [inst : DivisionCommMonoid α] {c
 : α}, IsUnit c → ∀ (a b : α), c * a / (c * b) = a / b
· 使用定理 `Ne.isUnit`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a : G₀}, a ≠ 0 →
 IsUnit a
-/
lemma mul_div_mul_left (a b : G₀) (hc : c ≠ 0) : c * a / (c * b) = a / b :=
  hc.isUnit.mul_div_mul_left _ _
/-
**mul_eq_mul_of_div_eq_div** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：mul_eq_mul_of_div_eq_div (a c : G₀) (hb : b != 0) (hd : d != 0) (h : a / b
 = c / d) : a * d = c * b
参数：a c : G₀；hb : b != 0；hd : d != 0；h : a / b = c / d。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `div_self`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a : G₀}, a ≠ 0 → 
a / a = 1
· 使用定理 `mul_comm_div`：mul_comm_div : a / b * c = a * (c / b)
· 使用定理 `div_mul_eq_mul_div`：div_mul_eq_mul_div : a / b * c = a * c / b
· 使用引理 `div_mul_cancel₀`：div_mul_cancel₀ (a : G₀) (h : b != 0) : a / b * b = a
-/
lemma mul_eq_mul_of_div_eq_div (a c : G₀) (hb : b ≠ 0) (hd : d ≠ 0)
    (h : a / b = c / d) : a * d = c * b := by
  rw [← mul_one a, ← div_self hb, ← mul_comm_div, h, div_mul_eq_mul_div, div_mul_cancel₀ _ hd]
/-
**div_eq_div_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：div_eq_div_iff (hb : b != 0) (hd : d != 0) : a / b = c / d ↔ a * d = c * b
参数：hb : b != 0；hd : d != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsUnit.div_eq_div_iff`：∀ {α : Type u} [inst : DivisionCommMonoid α] {a b
 c d : α}, IsUnit b → IsUnit d → (a / b = c / d ↔ a * d = c * b)
· 使用定理 `Ne.isUnit`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a : G₀}, a ≠ 0 →
 IsUnit a
-/
lemma div_eq_div_iff (hb : b ≠ 0) (hd : d ≠ 0) : a / b = c / d ↔ a * d = c * b :=
  hb.isUnit.div_eq_div_iff hd.isUnit
/-
**mul_inv_eq_mul_inv_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：mul_inv_eq_mul_inv_iff (hb : b != 0) (hd : d != 0) : a * b⁻¹ = c * d⁻¹ ↔ a
 * d = c * b
参数：hb : b != 0；hd : d != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsUnit.mul_inv_eq_mul_inv_iff`：∀ {α : Type u} [inst : DivisionCommMonoid
 α] {a b c d : α}, IsUnit b → IsUnit d → (a * b⁻¹ = c * d⁻¹ ↔ a * d = c * b)
· 使用定理 `Ne.isUnit`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a : G₀}, a ≠ 0 →
 IsUnit a
-/
lemma mul_inv_eq_mul_inv_iff (hb : b ≠ 0) (hd : d ≠ 0) :
    a * b⁻¹ = c * d⁻¹ ↔ a * d = c * b :=
  hb.isUnit.mul_inv_eq_mul_inv_iff hd.isUnit
/-
**inv_mul_eq_inv_mul_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：inv_mul_eq_inv_mul_iff (hb : b != 0) (hd : d != 0) : b⁻¹ * a = d⁻¹ * c ↔ a
 * d = c * b
参数：hb : b != 0；hd : d != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsUnit.inv_mul_eq_inv_mul_iff`：∀ {α : Type u} [inst : DivisionCommMonoid
 α] {a b c d : α}, IsUnit b → IsUnit d → (b⁻¹ * a = d⁻¹ * c ↔ a * d = c * b)
· 使用定理 `Ne.isUnit`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a : G₀}, a ≠ 0 →
 IsUnit a
-/
lemma inv_mul_eq_inv_mul_iff (hb : b ≠ 0) (hd : d ≠ 0) :
    b⁻¹ * a = d⁻¹ * c ↔ a * d = c * b :=
  hb.isUnit.inv_mul_eq_inv_mul_iff hd.isUnit

/-- The `CommGroupWithZero` version of `div_eq_div_iff_div_eq_div`. -/
/-
**div_eq_div_iff_div_eq_div'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：div_eq_div_iff_div_eq_div' (hb : b != 0) (hc : c != 0) : a / b = c / d ↔ a
 / c = b / d
参数：hb : b != 0；hc : c != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `mul_left_inj'`：mul_left_inj' (hc : c != 0) : a * c = b * c ↔ a = b
· 使用定理 `IsCancelMulZero.toIsRightCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} 
{inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsRightCancelMulZero M₀
· 使用定理 `instIsCancelMulZero`：∀ {G₀ : Type u_2} [inst : GroupWithZero G₀], IsCanc
elMulZero G₀
· 使用引理 `div_mul_cancel₀`：div_mul_cancel₀ (a : G₀) (h : b != 0) : a / b * b = a
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `div_mul_eq_mul_div`：div_mul_eq_mul_div : a / b * c = a * c / b
· 使用定理 `mul_div_assoc`：mul_div_assoc (a b c : G) : a * b / c = a * (b / c)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
The `CommGroupWithZero` version of `div_eq_div_iff_div_eq_div`.
-/
lemma div_eq_div_iff_div_eq_div' (hb : b ≠ 0) (hc : c ≠ 0) : a / b = c / d ↔ a / c = b / d := by
  conv_lhs => rw [← mul_left_inj' hb, div_mul_cancel₀ _ hb]
  conv_rhs => rw [← mul_left_inj' hc, div_mul_cancel₀ _ hc]
  rw [mul_comm _ c, div_mul_eq_mul_div, mul_div_assoc]
/-
**div_eq_div_of_div_eq_div** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：div_eq_div_of_div_eq_div (hc : c != 0) (hd : d != 0) (h : a / b = c / d) :
 a / c = b / d
参数：hc : c != 0；hd : d != 0；h : a / b = c / d。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `div_ne_zero`：div_ne_zero (ha : a != 0) (hb : b != 0) : a / b != 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_zero`：div_zero (a : G₀) : a / 0 = 0
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `div_eq_div_iff_div_eq_div'`：div_eq_div_iff_div_eq_div' (hb : b != 0) (hc
 : c != 0) : a / b = c / d ↔ a / c = b / d
-/
lemma div_eq_div_of_div_eq_div (hc : c ≠ 0) (hd : d ≠ 0) (h : a / b = c / d) : a / c = b / d :=
  have hb : b ≠ 0 := by
    intro hb
    rw [hb, div_zero] at h
    exact div_ne_zero hc hd h.symm
  (div_eq_div_iff_div_eq_div' hb hc).mp h
/-
**div_div_cancel** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：div_div_cancel (a b : G) : a / (a / b) = b
参数：a b : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `div_div_self'`：div_div_self' (a b : G) : a / (a / b) = b
-/
@[simp] lemma div_div_cancel₀ (ha : a ≠ 0) : a / (a / b) = b := ha.isUnit.div_div_cancel
/-
**div_div_cancel_left'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：div_div_cancel_left' (ha : a != 0) : a / b / a = b⁻¹
参数：ha : a != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsUnit.div_div_cancel_left`：∀ {α : Type u} [inst : DivisionCommMonoid α]
 {a b : α}, IsUnit a → a / b / a = b⁻¹
· 使用定理 `Ne.isUnit`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a : G₀}, a ≠ 0 →
 IsUnit a
-/
lemma div_div_cancel_left' (ha : a ≠ 0) : a / b / a = b⁻¹ := ha.isUnit.div_div_cancel_left
/-
**div_helper** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：div_helper (b : G₀) (h : a != 0) : 1 / (a * b) * a = 1 / b
参数：b : G₀；h : a != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_mul_eq_mul_div`：div_mul_eq_mul_div : a / b * c = a * c / b
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用引理 `div_mul_cancel_left₀`：div_mul_cancel_left₀ (ha : a != 0) (b : G₀) : a / 
(a * b) = b⁻¹
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
-/
lemma div_helper (b : G₀) (h : a ≠ 0) : 1 / (a * b) * a = 1 / b := by
  rw [div_mul_eq_mul_div, one_mul, div_mul_cancel_left₀ h, one_div]
/-
**div_div_div_cancel_left'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：div_div_div_cancel_left' (a b : G₀) (hc : c != 0) : c / a / (c / b) = b / 
a
参数：a b : G₀；hc : c != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_div_div_eq`：div_div_div_eq : a / b / (c / d) = a * d / (b * c)
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用引理 `mul_div_mul_right`：mul_div_mul_right (a b : G₀) (hc : c != 0) : a * c / 
(b * c) = a / b
-/
lemma div_div_div_cancel_left' (a b : G₀) (hc : c ≠ 0) : c / a / (c / b) = b / a := by
  rw [div_div_div_eq, mul_comm, mul_div_mul_right _ _ hc]
/-
**div_mul_div_cancel** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：div_mul_div_cancel (a b c : G) : a / b * (b / c) = a / c
参数：a b c : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_div_assoc`：mul_div_assoc (a b c : G) : a * b / c = a * (b / c)
· 使用定理 `div_mul_cancel`：div_mul_cancel (a b : G) : a / b * b = a
-/
@[simp] lemma div_mul_div_cancel₀' (ha : a ≠ 0) (b c : G₀) : a / b * (c / a) = c / b := by
  rw [mul_comm, div_mul_div_cancel₀ ha]

end CommGroupWithZero

section NoncomputableDefs

variable {M : Type*} [Nontrivial M]

open scoped Classical in
/-- Constructs a `GroupWithZero` structure on a `MonoidWithZero`
  consisting only of units and 0. -/
@[instance_reducible]
/-
**groupWithZeroOfIsUnitOrEqZero** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：groupWithZeroOfIsUnitOrEqZero [hM : MonoidWithZero M] (h : forall a : M, I
sUnit a ∨ a = 0) : GroupWithZero M
参数：h : forall a : M, IsUnit a ∨ a = 0。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructs a `GroupWithZero` structure on a `MonoidWithZero`
  consisting only of units and 0.
-/
noncomputable def groupWithZeroOfIsUnitOrEqZero [hM : MonoidWithZero M]
    (h : ∀ a : M, IsUnit a ∨ a = 0) : GroupWithZero M :=
  { hM with
    inv := fun a => if h0 : a = 0 then 0 else ↑((h a).resolve_right h0).unit⁻¹,
    inv_zero := dif_pos rfl,
    mul_inv_cancel := fun a h0 => by
      change (a * if h0 : a = 0 then 0 else ↑((h a).resolve_right h0).unit⁻¹) = 1
      rw [dif_neg h0, Units.mul_inv_eq_iff_eq_mul, one_mul, IsUnit.unit_spec] }

/-- Constructs a `CommGroupWithZero` structure on a `CommMonoidWithZero`
  consisting only of units and 0. -/
@[instance_reducible]
/-
**commGroupWithZeroOfIsUnitOrEqZero** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：commGroupWithZeroOfIsUnitOrEqZero [hM : CommMonoidWithZero M] (h : forall 
a : M, IsUnit a ∨ a = 0) : CommGroupWithZero M
参数：h : forall a : M, IsUnit a ∨ a = 0。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `GroupWithZero.div_eq_mul_inv`：∀ {G₀ : Type u} [self : GroupWithZero G₀] 
(a b : G₀), a / b = a * b⁻¹
· 使用定理 `GroupWithZero.zpow_zero'`：∀ {G₀ : Type u} [self : GroupWithZero G₀] (a :
 G₀), a ^ 0 = 1
· 使用定理 `GroupWithZero.zpow_succ'`：∀ {G₀ : Type u} [self : GroupWithZero G₀] (n :
 ℕ) (a : G₀), a ^ ↑n.succ = a ^ ↑n * a
· 使用定理 `GroupWithZero.zpow_neg'`：∀ {G₀ : Type u} [self : GroupWithZero G₀] (n : 
ℕ) (a : G₀), a ^ Int.negSucc n = (a ^ ↑n.succ)⁻¹
· 使用定理 `GroupWithZero.toNontrivial`：∀ {G₀ : Type u} [self : GroupWithZero G₀], N
ontrivial G₀
· 使用定理 `GroupWithZero.inv_zero`：∀ {G₀ : Type u} [self : GroupWithZero G₀], 0⁻¹ =
 0
· 使用定理 `GroupWithZero.mul_inv_cancel`：∀ {G₀ : Type u} [self : GroupWithZero G₀] 
(a : G₀), a ≠ 0 → a * a⁻¹ = 1

--- 原说明 ---
Constructs a `CommGroupWithZero` structure on a `CommMonoidWithZero`
  consisting only of units and 0.
-/
noncomputable def commGroupWithZeroOfIsUnitOrEqZero [hM : CommMonoidWithZero M]
    (h : ∀ a : M, IsUnit a ∨ a = 0) : CommGroupWithZero M :=
  { groupWithZeroOfIsUnitOrEqZero h, hM with }

end NoncomputableDefs

