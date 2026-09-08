/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Amelia Livingston, Yury Kudryashov,
Neil Strickland, Aaron Anderson
-/
module

public import Mathlib.Algebra.Divisibility.Basic
public import Mathlib.Algebra.Group.Units.Basic

/-!
# Divisibility and units

## Main definition

* `IsRelPrime x y`: that `x` and `y` are relatively prime, defined to mean that the only common
  divisors of `x` and `y` are the units.

-/

@[expose] public section

variable {α : Type*}

namespace Units

section Monoid

variable [Monoid α] {a b : α} {u : αˣ}

/-- Elements of the unit group of a monoid represented as elements of the monoid
divide any element of the monoid. -/
/-
**Units.coe_dvd** 是 Mathlib 中的一个定理，位于命名空间 `Units`。
形式化陈述：coe_dvd : ↑u ∣ a
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Units.mul_inv_cancel_left`：mul_inv_cancel_left (a : αˣ) (b : α) : (a : α
) * (↑a⁻¹ * b) = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Elements of the unit group of a monoid represented as elements of the monoid
divide any element of the monoid.
-/
theorem coe_dvd : ↑u ∣ a :=
  ⟨↑u⁻¹ * a, by simp⟩

/-- In a monoid, an element `a` divides an element `b` iff `a` divides all associates of `b`. -/
/-
**Units.dvd_mul_right** 是 Mathlib 中的一个定理，位于命名空间 `Units`。
形式化陈述：dvd_mul_right : a ∣ b * u ↔ a ∣ b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Units.mul_inv_cancel_right`：mul_inv_cancel_right (a : α) (b : αˣ) : a * 
b * ↑b⁻¹ = a
· 使用定理 `Dvd.dvd.mul_right`：∀ {α : Type u_1} [inst : Semigroup α] {a b : α}, a ∣ 
b → ∀ (c : α), a ∣ b * c
· 使用定理 `dvd_mul_right`：dvd_mul_right (a b : α) : a ∣ a * b

--- 原说明 ---
In a monoid, an element `a` divides an element `b` iff `a` divides all associate
s of `b`.
-/
theorem dvd_mul_right : a ∣ b * u ↔ a ∣ b :=
  Iff.intro (fun ⟨c, eq⟩ ↦ ⟨c * ↑u⁻¹, by rw [← mul_assoc, ← eq, Units.mul_inv_cancel_right]⟩)
    fun ⟨_, eq⟩ ↦ eq.symm ▸ (_root_.dvd_mul_right _ _).mul_right _

/-- In a monoid, an element `a` divides an element `b` iff all associates of `a` divide `b`. -/
/-
**Units.mul_right_dvd** 是 Mathlib 中的一个定理，位于命名空间 `Units`。
形式化陈述：mul_right_dvd : a * u ∣ b ↔ a ∣ b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `dvd_trans`：dvd_trans : a ∣ b -> b ∣ c -> a ∣ c | ⟨d, h₁⟩, ⟨e, h₂⟩ => ⟨d 
* e, h₁ ▸ h₂.trans mul_assoc a d e⟩  alias Dvd.dvd.trans
· 使用定理 `Dvd.intro`：Dvd.intro (c : α) (h : a * c = b) : a ∣ b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Units.mul_inv`：mul_inv : (a * ↑a⁻¹ : α) = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a

--- 原说明 ---
In a monoid, an element `a` divides an element `b` iff all associates of `a` div
ide `b`.
-/
theorem mul_right_dvd : a * u ∣ b ↔ a ∣ b :=
  Iff.intro (fun ⟨c, eq⟩ => ⟨↑u * c, eq.trans (mul_assoc _ _ _)⟩) fun h =>
    dvd_trans (Dvd.intro (↑u⁻¹) (by rw [mul_assoc, u.mul_inv, mul_one])) h

end Monoid

section CommMonoid

variable [CommMonoid α] {a b : α} {u : αˣ}

/-- In a commutative monoid, an element `a` divides an element `b` iff `a` divides all left
associates of `b`. -/
/-
**Units.dvd_mul_left** 是 Mathlib 中的一个定理，位于命名空间 `Units`。
形式化陈述：dvd_mul_left : a ∣ u * b ↔ a ∣ b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Units.dvd_mul_right`：dvd_mul_right : a ∣ b * u ↔ a ∣ b

--- 原说明 ---
In a commutative monoid, an element `a` divides an element `b` iff `a` divides a
ll left
associates of `b`.
-/
theorem dvd_mul_left : a ∣ u * b ↔ a ∣ b := by
  rw [mul_comm]
  apply dvd_mul_right

/-- In a commutative monoid, an element `a` divides an element `b` iff all
  left associates of `a` divide `b`. -/
/-
**Units.mul_left_dvd** 是 Mathlib 中的一个定理，位于命名空间 `Units`。
形式化陈述：mul_left_dvd : ↑u * a ∣ b ↔ a ∣ b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Units.mul_right_dvd`：mul_right_dvd : a * u ∣ b ↔ a ∣ b

--- 原说明 ---
In a commutative monoid, an element `a` divides an element `b` iff all
  left associates of `a` divide `b`.
-/
theorem mul_left_dvd : ↑u * a ∣ b ↔ a ∣ b := by
  rw [mul_comm]
  apply mul_right_dvd

end CommMonoid

end Units

namespace IsUnit

section Monoid

variable [Monoid α] {a b u : α}

/-- Units of a monoid divide any element of the monoid. -/
@[simp]
/-
**IsUnit.dvd** 是 Mathlib 中的一个定理，位于命名空间 `IsUnit`。
形式化陈述：dvd (hu : IsUnit u) : u ∣ a
参数：hu : IsUnit u。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Units.coe_dvd`：coe_dvd : ↑u ∣ a

--- 原说明 ---
Units of a monoid divide any element of the monoid.
-/
theorem dvd (hu : IsUnit u) : u ∣ a := by
  rcases hu with ⟨u, rfl⟩
  apply Units.coe_dvd

@[simp]
/-
**IsUnit.dvd_mul_right** 是 Mathlib 中的一个定理，位于命名空间 `IsUnit`。
形式化陈述：dvd_mul_right (hu : IsUnit u) : a ∣ b * u ↔ a ∣ b
参数：hu : IsUnit u。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Units.dvd_mul_right`：dvd_mul_right : a ∣ b * u ↔ a ∣ b
-/
theorem dvd_mul_right (hu : IsUnit u) : a ∣ b * u ↔ a ∣ b := by
  rcases hu with ⟨u, rfl⟩
  apply Units.dvd_mul_right

/-- In a monoid, an element a divides an element b iff all associates of `a` divide `b`. -/
@[simp]
/-
**IsUnit.mul_right_dvd** 是 Mathlib 中的一个定理，位于命名空间 `IsUnit`。
形式化陈述：mul_right_dvd (hu : IsUnit u) : a * u ∣ b ↔ a ∣ b
参数：hu : IsUnit u。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Units.mul_right_dvd`：mul_right_dvd : a * u ∣ b ↔ a ∣ b

--- 原说明 ---
In a monoid, an element a divides an element b iff all associates of `a` divide 
`b`.
-/
theorem mul_right_dvd (hu : IsUnit u) : a * u ∣ b ↔ a ∣ b := by
  rcases hu with ⟨u, rfl⟩
  apply Units.mul_right_dvd
/-
**IsUnit.isPrimal** 是 Mathlib 中的一个定理，位于命名空间 `IsUnit`。
形式化陈述：isPrimal (hu : IsUnit u) : IsPrimal u
参数：hu : IsUnit u。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsUnit.dvd`：dvd (hu : IsUnit u) : u ∣ a
· 使用定理 `one_dvd`：one_dvd (a : α) : 1 ∣ a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
theorem isPrimal (hu : IsUnit u) : IsPrimal u :=
  fun _ _ _ ↦ ⟨u, 1, hu.dvd, one_dvd _, (mul_one u).symm⟩

end Monoid

section CommMonoid

variable [CommMonoid α] {a b u : α}

/-- In a commutative monoid, an element `a` divides an element `b` iff `a` divides all left
associates of `b`. -/
@[simp]
/-
**IsUnit.dvd_mul_left** 是 Mathlib 中的一个定理，位于命名空间 `IsUnit`。
形式化陈述：dvd_mul_left (hu : IsUnit u) : a ∣ u * b ↔ a ∣ b
参数：hu : IsUnit u。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Units.dvd_mul_left`：dvd_mul_left : a ∣ u * b ↔ a ∣ b

--- 原说明 ---
In a commutative monoid, an element `a` divides an element `b` iff `a` divides a
ll left
associates of `b`.
-/
theorem dvd_mul_left (hu : IsUnit u) : a ∣ u * b ↔ a ∣ b := by
  rcases hu with ⟨u, rfl⟩
  apply Units.dvd_mul_left

/-- In a commutative monoid, an element `a` divides an element `b` iff all
  left associates of `a` divide `b`. -/
@[simp]
/-
**IsUnit.mul_left_dvd** 是 Mathlib 中的一个定理，位于命名空间 `IsUnit`。
形式化陈述：mul_left_dvd (hu : IsUnit u) : u * a ∣ b ↔ a ∣ b
参数：hu : IsUnit u。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Units.mul_left_dvd`：mul_left_dvd : ↑u * a ∣ b ↔ a ∣ b

--- 原说明 ---
In a commutative monoid, an element `a` divides an element `b` iff all
  left associates of `a` divide `b`.
-/
theorem mul_left_dvd (hu : IsUnit u) : u * a ∣ b ↔ a ∣ b := by
  rcases hu with ⟨u, rfl⟩
  apply Units.mul_left_dvd

end CommMonoid

end IsUnit

section CommMonoid

variable [CommMonoid α]

/-
**isUnit_iff_dvd_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isUnit_iff_dvd_one {x : α} : IsUnit x ↔ x ∣ 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsUnit.dvd`：dvd (hu : IsUnit u) : u ∣ a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
-/
theorem isUnit_iff_dvd_one {x : α} : IsUnit x ↔ x ∣ 1 :=
  ⟨IsUnit.dvd, fun ⟨y, h⟩ => ⟨⟨x, y, h.symm, by rw [h, mul_comm]⟩, rfl⟩⟩
/-
**isUnit_iff_forall_dvd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isUnit_iff_forall_dvd {x : α} : IsUnit x ↔ forall y, x ∣ y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `isUnit_iff_dvd_one`：isUnit_iff_dvd_one {x : α} : IsUnit x ↔ x ∣ 1
· 使用定理 `Dvd.dvd.trans`：∀ {α : Type u_1} [inst : Semigroup α] {a b c : α}, a ∣ b 
→ b ∣ c → a ∣ c
· 使用定理 `one_dvd`：one_dvd (a : α) : 1 ∣ a
-/
theorem isUnit_iff_forall_dvd {x : α} : IsUnit x ↔ ∀ y, x ∣ y :=
  isUnit_iff_dvd_one.trans ⟨fun h _ => h.trans (one_dvd _), fun h => h _⟩
/-
**isUnit_of_dvd_unit** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isUnit_of_dvd_unit {x y : α} (xy : x ∣ y) (hu : IsUnit y) : IsUnit x
参数：xy : x ∣ y；hu : IsUnit y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isUnit_iff_dvd_one`：isUnit_iff_dvd_one {x : α} : IsUnit x ↔ x ∣ 1
· 使用定理 `Dvd.dvd.trans`：∀ {α : Type u_1} [inst : Semigroup α] {a b c : α}, a ∣ b 
→ b ∣ c → a ∣ c
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
-/
theorem isUnit_of_dvd_unit {x y : α} (xy : x ∣ y) (hu : IsUnit y) : IsUnit x :=
  isUnit_iff_dvd_one.2 <| xy.trans <| isUnit_iff_dvd_one.1 hu
/-
**isUnit_of_dvd_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isUnit_of_dvd_one {a : α} (h : a ∣ 1) : IsUnit (a : α)
参数：h : a ∣ 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isUnit_iff_dvd_one`：isUnit_iff_dvd_one {x : α} : IsUnit x ↔ x ∣ 1
-/
theorem isUnit_of_dvd_one {a : α} (h : a ∣ 1) : IsUnit (a : α) :=
  isUnit_iff_dvd_one.mpr h
/-
**not_isUnit_of_not_isUnit_dvd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：not_isUnit_of_not_isUnit_dvd {a b : α} (ha : ¬IsUnit a) (hb : a ∣ b) : ¬Is
Unit b
参数：ha : ¬IsUnit a；hb : a ∣ b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `isUnit_of_dvd_unit`：isUnit_of_dvd_unit {x y : α} (xy : x ∣ y) (hu : IsUn
it y) : IsUnit x
-/
theorem not_isUnit_of_not_isUnit_dvd {a b : α} (ha : ¬IsUnit a) (hb : a ∣ b) : ¬IsUnit b :=
  mt (isUnit_of_dvd_unit hb) ha

@[simp]
/-
**dvd_pow_self_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：dvd_pow_self_iff {x : α} {n : Nat} : x ∣ x ^ n ↔ n != 0 ∨ IsUnit x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
-/
lemma dvd_pow_self_iff {x : α} {n : ℕ} :
    x ∣ x ^ n ↔ n ≠ 0 ∨ IsUnit x := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [isUnit_iff_dvd_one]
  · simp [hn, dvd_pow_self]

end CommMonoid

section RelPrime

/-- `x` and `y` are relatively prime if every common divisor is a unit. -/
/-
**IsRelPrime** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：IsRelPrime [Monoid α] (x y : α) : Prop
参数：x y : α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`x` and `y` are relatively prime if every common divisor is a unit.
-/
def IsRelPrime [Monoid α] (x y : α) : Prop := ∀ ⦃d⦄, d ∣ x → d ∣ y → IsUnit d

variable [CommMonoid α] {x y z : α}
/-
**IsRelPrime.symm** 是 Mathlib 中的一个定理，位于命名空间 `IsRelPrime`。
形式化陈述：∀ {α : Type u_1} [inst : CommMonoid α] {x y : α}, IsRelPrime x y → IsRelPr
ime y x
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[symm] theorem IsRelPrime.symm (H : IsRelPrime x y) : IsRelPrime y x := fun _ hx hy ↦ H hy hx
/-
**symm_isRelPrime** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：symm_isRelPrime : Std.Symm (IsRelPrime : α -> α -> Prop) where symm _ _
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `IsRelPrime.symm`：∀ {α : Type u_1} [inst : CommMonoid α] {x y : α}, IsRel
Prime x y → IsRelPrime y x
-/
instance symm_isRelPrime : Std.Symm (IsRelPrime : α → α → Prop) where
  symm _ _ := .symm

@[deprecated (since := "2026-06-10")] alias symmetric_isRelPrime := symm_isRelPrime
/-
**isRelPrime_comm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isRelPrime_comm : IsRelPrime x y ↔ IsRelPrime y x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsRelPrime.symm`：∀ {α : Type u_1} [inst : CommMonoid α] {x y : α}, IsRel
Prime x y → IsRelPrime y x
-/
theorem isRelPrime_comm : IsRelPrime x y ↔ IsRelPrime y x :=
  ⟨IsRelPrime.symm, IsRelPrime.symm⟩
/-
**isRelPrime_self** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isRelPrime_self : IsRelPrime x x ↔ IsUnit x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dvd_rfl`：dvd_rfl : forall {a : α}, a ∣ a
· 使用定理 `isUnit_of_dvd_unit`：isUnit_of_dvd_unit {x y : α} (xy : x ∣ y) (hu : IsUn
it y) : IsUnit x
-/
theorem isRelPrime_self : IsRelPrime x x ↔ IsUnit x :=
  ⟨(· dvd_rfl dvd_rfl), fun hu _ _ dvd ↦ isUnit_of_dvd_unit dvd hu⟩
/-
**IsUnit.isRelPrime_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsUnit.isRelPrime_left (h : IsUnit x) : IsRelPrime x y
参数：h : IsUnit x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isUnit_of_dvd_unit`：isUnit_of_dvd_unit {x y : α} (xy : x ∣ y) (hu : IsUn
it y) : IsUnit x
-/
theorem IsUnit.isRelPrime_left (h : IsUnit x) : IsRelPrime x y :=
  fun _ hx _ ↦ isUnit_of_dvd_unit hx h
/-
**IsUnit.isRelPrime_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsUnit.isRelPrime_right (h : IsUnit y) : IsRelPrime x y
参数：h : IsUnit y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsRelPrime.symm`：∀ {α : Type u_1} [inst : CommMonoid α] {x y : α}, IsRel
Prime x y → IsRelPrime y x
· 使用定理 `IsUnit.isRelPrime_left`：IsUnit.isRelPrime_left (h : IsUnit x) : IsRelPri
me x y
-/
theorem IsUnit.isRelPrime_right (h : IsUnit y) : IsRelPrime x y := h.isRelPrime_left.symm
/-
**isRelPrime_one_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isRelPrime_one_left : IsRelPrime 1 x
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsUnit.isRelPrime_left`：IsUnit.isRelPrime_left (h : IsUnit x) : IsRelPri
me x y
· 使用定理 `isUnit_one`：isUnit_one [Monoid M] : IsUnit (1 : M)
-/
theorem isRelPrime_one_left : IsRelPrime 1 x := isUnit_one.isRelPrime_left
/-
**isRelPrime_one_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isRelPrime_one_right : IsRelPrime x 1
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsUnit.isRelPrime_right`：IsUnit.isRelPrime_right (h : IsUnit y) : IsRelP
rime x y
· 使用定理 `isUnit_one`：isUnit_one [Monoid M] : IsUnit (1 : M)
-/
theorem isRelPrime_one_right : IsRelPrime x 1 := isUnit_one.isRelPrime_right
/-
**IsRelPrime.of_mul_left_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsRelPrime.of_mul_left_left (H : IsRelPrime (x * y) z) : IsRelPrime x z
参数：H : IsRelPrime (x * y) z。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dvd_mul_of_dvd_left`：dvd_mul_of_dvd_left (h : a ∣ b) (c : α) : a ∣ b * c
-/
theorem IsRelPrime.of_mul_left_left (H : IsRelPrime (x * y) z) : IsRelPrime x z :=
  fun _ hx ↦ H (dvd_mul_of_dvd_left hx _)
/-
**IsRelPrime.of_mul_left_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsRelPrime.of_mul_left_right (H : IsRelPrime (x * y) z) : IsRelPrime y z
参数：H : IsRelPrime (x * y) z。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsRelPrime.of_mul_left_left`：IsRelPrime.of_mul_left_left (H : IsRelPrime
 (x * y) z) : IsRelPrime x z
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
-/
theorem IsRelPrime.of_mul_left_right (H : IsRelPrime (x * y) z) : IsRelPrime y z :=
  (mul_comm x y ▸ H).of_mul_left_left
/-
**IsRelPrime.of_mul_right_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsRelPrime.of_mul_right_left (H : IsRelPrime x (y * z)) : IsRelPrime x y
参数：H : IsRelPrime x (y * z)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isRelPrime_comm`：isRelPrime_comm : IsRelPrime x y ↔ IsRelPrime y x
· 使用定理 `IsRelPrime.of_mul_left_left`：IsRelPrime.of_mul_left_left (H : IsRelPrime
 (x * y) z) : IsRelPrime x z
-/
theorem IsRelPrime.of_mul_right_left (H : IsRelPrime x (y * z)) : IsRelPrime x y := by
  rw [isRelPrime_comm] at H ⊢
  exact H.of_mul_left_left
/-
**IsRelPrime.of_mul_right_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsRelPrime.of_mul_right_right (H : IsRelPrime x (y * z)) : IsRelPrime x z
参数：H : IsRelPrime x (y * z)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsRelPrime.of_mul_right_left`：IsRelPrime.of_mul_right_left (H : IsRelPri
me x (y * z)) : IsRelPrime x y
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
-/
theorem IsRelPrime.of_mul_right_right (H : IsRelPrime x (y * z)) : IsRelPrime x z :=
  (mul_comm y z ▸ H).of_mul_right_left
/-
**IsRelPrime.of_dvd_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsRelPrime.of_dvd_left (h : IsRelPrime y z) (dvd : x ∣ y) : IsRelPrime x z
参数：h : IsRelPrime y z；dvd : x ∣ y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsRelPrime.of_mul_left_left`：IsRelPrime.of_mul_left_left (H : IsRelPrime
 (x * y) z) : IsRelPrime x z
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem IsRelPrime.of_dvd_left (h : IsRelPrime y z) (dvd : x ∣ y) : IsRelPrime x z := by
  obtain ⟨d, rfl⟩ := dvd; exact IsRelPrime.of_mul_left_left h
/-
**IsRelPrime.of_dvd_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsRelPrime.of_dvd_right (h : IsRelPrime z y) (dvd : x ∣ y) : IsRelPrime z 
x
参数：h : IsRelPrime z y；dvd : x ∣ y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsRelPrime.symm`：∀ {α : Type u_1} [inst : CommMonoid α] {x y : α}, IsRel
Prime x y → IsRelPrime y x
· 使用定理 `IsRelPrime.of_dvd_left`：IsRelPrime.of_dvd_left (h : IsRelPrime y z) (dvd
 : x ∣ y) : IsRelPrime x z
-/
theorem IsRelPrime.of_dvd_right (h : IsRelPrime z y) (dvd : x ∣ y) : IsRelPrime z x :=
  (h.symm.of_dvd_left dvd).symm
/-
**IsRelPrime.isUnit_of_dvd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsRelPrime.isUnit_of_dvd (H : IsRelPrime x y) (d : x ∣ y) : IsUnit x
参数：H : IsRelPrime x y；d : x ∣ y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dvd_rfl`：dvd_rfl : forall {a : α}, a ∣ a
-/
theorem IsRelPrime.isUnit_of_dvd (H : IsRelPrime x y) (d : x ∣ y) : IsUnit x := H dvd_rfl d

section IsUnit

variable (hu : IsUnit x)

include hu

/-
**isRelPrime_mul_unit_left_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isRelPrime_mul_unit_left_left : IsRelPrime (x * y) z ↔ IsRelPrime y z
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsRelPrime.of_mul_left_right`：IsRelPrime.of_mul_left_right (H : IsRelPri
me (x * y) z) : IsRelPrime y z
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `IsUnit.dvd_mul_left`：dvd_mul_left (hu : IsUnit u) : a ∣ u * b ↔ a ∣ b
-/
theorem isRelPrime_mul_unit_left_left : IsRelPrime (x * y) z ↔ IsRelPrime y z :=
  ⟨IsRelPrime.of_mul_left_right, fun H _ h ↦ H (hu.dvd_mul_left.mp h)⟩
/-
**isRelPrime_mul_unit_left_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isRelPrime_mul_unit_left_right : IsRelPrime y (x * z) ↔ IsRelPrime y z
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isRelPrime_comm`：isRelPrime_comm : IsRelPrime x y ↔ IsRelPrime y x
· 使用定理 `isRelPrime_mul_unit_left_left`：isRelPrime_mul_unit_left_left : IsRelPrim
e (x * y) z ↔ IsRelPrime y z
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem isRelPrime_mul_unit_left_right : IsRelPrime y (x * z) ↔ IsRelPrime y z := by
  rw [isRelPrime_comm, isRelPrime_mul_unit_left_left hu, isRelPrime_comm]
/-
**isRelPrime_mul_unit_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isRelPrime_mul_unit_left : IsRelPrime (x * y) (x * z) ↔ IsRelPrime y z
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isRelPrime_mul_unit_left_left`：isRelPrime_mul_unit_left_left : IsRelPrim
e (x * y) z ↔ IsRelPrime y z
· 使用定理 `isRelPrime_mul_unit_left_right`：isRelPrime_mul_unit_left_right : IsRelPr
ime y (x * z) ↔ IsRelPrime y z
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem isRelPrime_mul_unit_left : IsRelPrime (x * y) (x * z) ↔ IsRelPrime y z := by
  rw [isRelPrime_mul_unit_left_left hu, isRelPrime_mul_unit_left_right hu]
/-
**isRelPrime_mul_unit_right_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isRelPrime_mul_unit_right_left : IsRelPrime (y * x) z ↔ IsRelPrime y z
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `isRelPrime_mul_unit_left_left`：isRelPrime_mul_unit_left_left : IsRelPrim
e (x * y) z ↔ IsRelPrime y z
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem isRelPrime_mul_unit_right_left : IsRelPrime (y * x) z ↔ IsRelPrime y z := by
  rw [mul_comm, isRelPrime_mul_unit_left_left hu]
/-
**isRelPrime_mul_unit_right_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isRelPrime_mul_unit_right_right : IsRelPrime y (z * x) ↔ IsRelPrime y z
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `isRelPrime_mul_unit_left_right`：isRelPrime_mul_unit_left_right : IsRelPr
ime y (x * z) ↔ IsRelPrime y z
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem isRelPrime_mul_unit_right_right : IsRelPrime y (z * x) ↔ IsRelPrime y z := by
  rw [mul_comm, isRelPrime_mul_unit_left_right hu]
/-
**isRelPrime_mul_unit_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isRelPrime_mul_unit_right : IsRelPrime (y * x) (z * x) ↔ IsRelPrime y z
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isRelPrime_mul_unit_right_left`：isRelPrime_mul_unit_right_left : IsRelPr
ime (y * x) z ↔ IsRelPrime y z
· 使用定理 `isRelPrime_mul_unit_right_right`：isRelPrime_mul_unit_right_right : IsRel
Prime y (z * x) ↔ IsRelPrime y z
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem isRelPrime_mul_unit_right : IsRelPrime (y * x) (z * x) ↔ IsRelPrime y z := by
  rw [isRelPrime_mul_unit_right_left hu, isRelPrime_mul_unit_right_right hu]

end IsUnit

/-
**IsRelPrime.dvd_of_dvd_mul_right_of_isPrimal** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsRelPrime.dvd_of_dvd_mul_right_of_isPrimal (H1 : IsRelPrime x z) (H2 : x 
∣ y * z) (h : IsPrimal x) : x ∣ y
参数：H1 : IsRelPrime x z；H2 : x ∣ y * z；h : IsPrimal x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `IsUnit.mul_right_dvd`：mul_right_dvd (hu : IsUnit u) : a * u ∣ b ↔ a ∣ b
· 使用定理 `IsRelPrime.isUnit_of_dvd`：IsRelPrime.isUnit_of_dvd (H : IsRelPrime x y) 
(d : x ∣ y) : IsUnit x
· 使用定理 `IsRelPrime.of_mul_left_right`：IsRelPrime.of_mul_left_right (H : IsRelPri
me (x * y) z) : IsRelPrime y z
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem IsRelPrime.dvd_of_dvd_mul_right_of_isPrimal (H1 : IsRelPrime x z) (H2 : x ∣ y * z)
    (h : IsPrimal x) : x ∣ y := by
  obtain ⟨a, b, ha, hb, rfl⟩ := h H2
  exact (H1.of_mul_left_right.isUnit_of_dvd hb).mul_right_dvd.mpr ha
/-
**IsRelPrime.dvd_of_dvd_mul_left_of_isPrimal** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsRelPrime.dvd_of_dvd_mul_left_of_isPrimal (H1 : IsRelPrime x y) (H2 : x ∣
 y * z) (h : IsPrimal x) : x ∣ z
参数：H1 : IsRelPrime x y；H2 : x ∣ y * z；h : IsPrimal x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsRelPrime.dvd_of_dvd_mul_right_of_isPrimal`：IsRelPrime.dvd_of_dvd_mul_r
ight_of_isPrimal (H1 : IsRelPrime x z) (H2 : x ∣ y * z) (h : IsPrimal x) : x ∣ y
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
-/
theorem IsRelPrime.dvd_of_dvd_mul_left_of_isPrimal (H1 : IsRelPrime x y) (H2 : x ∣ y * z)
    (h : IsPrimal x) : x ∣ z :=
  H1.dvd_of_dvd_mul_right_of_isPrimal (mul_comm y z ▸ H2) h
/-
**IsRelPrime.mul_dvd_of_right_isPrimal** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsRelPrime.mul_dvd_of_right_isPrimal (H : IsRelPrime x y) (H1 : x ∣ z) (H2
 : y ∣ z) (hy : IsPrimal y) : x * y ∣ z
参数：H : IsRelPrime x y；H1 : x ∣ z；H2 : y ∣ z；hy : IsPrimal y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mul_dvd_mul_left`：mul_dvd_mul_left (a : α) (h : b ∣ c) : a * b ∣ a * c
· 使用定理 `IsRelPrime.dvd_of_dvd_mul_left_of_isPrimal`：IsRelPrime.dvd_of_dvd_mul_le
ft_of_isPrimal (H1 : IsRelPrime x y) (H2 : x ∣ y * z) (h : IsPrimal x) : x ∣ z
· 使用定理 `IsRelPrime.symm`：∀ {α : Type u_1} [inst : CommMonoid α] {x y : α}, IsRel
Prime x y → IsRelPrime y x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem IsRelPrime.mul_dvd_of_right_isPrimal (H : IsRelPrime x y) (H1 : x ∣ z) (H2 : y ∣ z)
    (hy : IsPrimal y) : x * y ∣ z := by
  obtain ⟨w, rfl⟩ := H1
  exact mul_dvd_mul_left x (H.symm.dvd_of_dvd_mul_left_of_isPrimal H2 hy)
/-
**IsRelPrime.mul_dvd_of_left_isPrimal** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsRelPrime.mul_dvd_of_left_isPrimal (H : IsRelPrime x y) (H1 : x ∣ z) (H2 
: y ∣ z) (hx : IsPrimal x) : x * y ∣ z
参数：H : IsRelPrime x y；H1 : x ∣ z；H2 : y ∣ z；hx : IsPrimal x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `IsRelPrime.mul_dvd_of_right_isPrimal`：IsRelPrime.mul_dvd_of_right_isPrim
al (H : IsRelPrime x y) (H1 : x ∣ z) (H2 : y ∣ z) (hy : IsPrimal y) : x * y ∣ z
· 使用定理 `IsRelPrime.symm`：∀ {α : Type u_1} [inst : CommMonoid α] {x y : α}, IsRel
Prime x y → IsRelPrime y x
-/
theorem IsRelPrime.mul_dvd_of_left_isPrimal (H : IsRelPrime x y) (H1 : x ∣ z) (H2 : y ∣ z)
    (hx : IsPrimal x) : x * y ∣ z := by
  rw [mul_comm]; exact H.symm.mul_dvd_of_right_isPrimal H2 H1 hx

/-! `IsRelPrime` enjoys desirable properties in a decomposition monoid.
See Lemma 6.3 in *On properties of square-free elements in commutative cancellative monoids*,
https://doi.org/10.1007/s00233-019-10022-3. -/

variable [DecompositionMonoid α]

/-
**IsRelPrime.dvd_of_dvd_mul_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsRelPrime.dvd_of_dvd_mul_right (H1 : IsRelPrime x z) (H2 : x ∣ y * z) : x
 ∣ y
参数：H1 : IsRelPrime x z；H2 : x ∣ y * z。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsRelPrime.dvd_of_dvd_mul_right_of_isPrimal`：IsRelPrime.dvd_of_dvd_mul_r
ight_of_isPrimal (H1 : IsRelPrime x z) (H2 : x ∣ y * z) (h : IsPrimal x) : x ∣ y
· 使用定理 `DecompositionMonoid.primal`：∀ {α : Type u_1} {inst : Semigroup α} [self 
: DecompositionMonoid α] (a : α), IsPrimal a
-/
theorem IsRelPrime.dvd_of_dvd_mul_right (H1 : IsRelPrime x z) (H2 : x ∣ y * z) : x ∣ y :=
  H1.dvd_of_dvd_mul_right_of_isPrimal H2 (DecompositionMonoid.primal x)
/-
**IsRelPrime.dvd_of_dvd_mul_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsRelPrime.dvd_of_dvd_mul_left (H1 : IsRelPrime x y) (H2 : x ∣ y * z) : x 
∣ z
参数：H1 : IsRelPrime x y；H2 : x ∣ y * z。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsRelPrime.dvd_of_dvd_mul_right`：IsRelPrime.dvd_of_dvd_mul_right (H1 : I
sRelPrime x z) (H2 : x ∣ y * z) : x ∣ y
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
-/
theorem IsRelPrime.dvd_of_dvd_mul_left (H1 : IsRelPrime x y) (H2 : x ∣ y * z) : x ∣ z :=
  H1.dvd_of_dvd_mul_right (mul_comm y z ▸ H2)
/-
**IsRelPrime.mul_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsRelPrime.mul_left (H1 : IsRelPrime x z) (H2 : IsRelPrime y z) : IsRelPri
me (x * y) z
参数：H1 : IsRelPrime x z；H2 : IsRelPrime y z。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_dvd_and_dvd_of_dvd_mul`：exists_dvd_and_dvd_of_dvd_mul [Decomposit
ionMonoid α] {b c a : α} (H : a ∣ b * c) : exists a₁ a₂, a₁ ∣ b ∧ a₂ ∣ c ∧ a = a
₁ * a₂
· 使用定理 `IsUnit.mul`：∀ {M : Type u_1} [inst : Monoid M] {a b : M}, IsUnit a → IsU
nit b → IsUnit (a * b)
· 使用定理 `Dvd.dvd.trans`：∀ {α : Type u_1} [inst : Semigroup α] {a b c : α}, a ∣ b 
→ b ∣ c → a ∣ c
· 使用定理 `dvd_mul_right`：dvd_mul_right (a b : α) : a ∣ a * b
· 使用定理 `dvd_mul_left`：dvd_mul_left (a b : α) : a ∣ b * a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem IsRelPrime.mul_left (H1 : IsRelPrime x z) (H2 : IsRelPrime y z) : IsRelPrime (x * y) z :=
  fun _ h hz ↦ by
    obtain ⟨a, b, ha, hb, rfl⟩ := exists_dvd_and_dvd_of_dvd_mul h
    exact (H1 ha <| (dvd_mul_right a b).trans hz).mul (H2 hb <| (dvd_mul_left b a).trans hz)
/-
**IsRelPrime.mul_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsRelPrime.mul_right (H1 : IsRelPrime x y) (H2 : IsRelPrime x z) : IsRelPr
ime x (y * z)
参数：H1 : IsRelPrime x y；H2 : IsRelPrime x z。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isRelPrime_comm`：isRelPrime_comm : IsRelPrime x y ↔ IsRelPrime y x
· 使用定理 `IsRelPrime.mul_left`：IsRelPrime.mul_left (H1 : IsRelPrime x z) (H2 : IsR
elPrime y z) : IsRelPrime (x * y) z
-/
theorem IsRelPrime.mul_right (H1 : IsRelPrime x y) (H2 : IsRelPrime x z) :
    IsRelPrime x (y * z) := by
  rw [isRelPrime_comm] at H1 H2 ⊢; exact H1.mul_left H2
/-
**IsRelPrime.mul_left_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsRelPrime.mul_left_iff : IsRelPrime (x * y) z ↔ IsRelPrime x z ∧ IsRelPri
me y z
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsRelPrime.of_mul_left_left`：IsRelPrime.of_mul_left_left (H : IsRelPrime
 (x * y) z) : IsRelPrime x z
· 使用定理 `IsRelPrime.of_mul_left_right`：IsRelPrime.of_mul_left_right (H : IsRelPri
me (x * y) z) : IsRelPrime y z
· 使用定理 `IsRelPrime.mul_left`：IsRelPrime.mul_left (H1 : IsRelPrime x z) (H2 : IsR
elPrime y z) : IsRelPrime (x * y) z
-/
theorem IsRelPrime.mul_left_iff : IsRelPrime (x * y) z ↔ IsRelPrime x z ∧ IsRelPrime y z :=
  ⟨fun H ↦ ⟨H.of_mul_left_left, H.of_mul_left_right⟩, fun ⟨H1, H2⟩ ↦ H1.mul_left H2⟩
/-
**IsRelPrime.mul_right_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsRelPrime.mul_right_iff : IsRelPrime x (y * z) ↔ IsRelPrime x y ∧ IsRelPr
ime x z
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsRelPrime.of_mul_right_left`：IsRelPrime.of_mul_right_left (H : IsRelPri
me x (y * z)) : IsRelPrime x y
· 使用定理 `IsRelPrime.of_mul_right_right`：IsRelPrime.of_mul_right_right (H : IsRelP
rime x (y * z)) : IsRelPrime x z
· 使用定理 `IsRelPrime.mul_right`：IsRelPrime.mul_right (H1 : IsRelPrime x y) (H2 : I
sRelPrime x z) : IsRelPrime x (y * z)
-/
theorem IsRelPrime.mul_right_iff : IsRelPrime x (y * z) ↔ IsRelPrime x y ∧ IsRelPrime x z :=
  ⟨fun H ↦ ⟨H.of_mul_right_left, H.of_mul_right_right⟩, fun ⟨H1, H2⟩ ↦ H1.mul_right H2⟩
/-
**IsRelPrime.mul_dvd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsRelPrime.mul_dvd (H : IsRelPrime x y) (H1 : x ∣ z) (H2 : y ∣ z) : x * y 
∣ z
参数：H : IsRelPrime x y；H1 : x ∣ z；H2 : y ∣ z。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsRelPrime.mul_dvd_of_left_isPrimal`：IsRelPrime.mul_dvd_of_left_isPrimal
 (H : IsRelPrime x y) (H1 : x ∣ z) (H2 : y ∣ z) (hx : IsPrimal x) : x * y ∣ z
· 使用定理 `DecompositionMonoid.primal`：∀ {α : Type u_1} {inst : Semigroup α} [self 
: DecompositionMonoid α] (a : α), IsPrimal a
-/
theorem IsRelPrime.mul_dvd (H : IsRelPrime x y) (H1 : x ∣ z) (H2 : y ∣ z) : x * y ∣ z :=
  H.mul_dvd_of_left_isPrimal H1 H2 (DecompositionMonoid.primal x)

end RelPrime

