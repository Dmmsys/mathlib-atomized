/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
module

public import Mathlib.Algebra.GroupWithZero.Semiconj
public import Mathlib.Algebra.Group.Commute.Units
public import Mathlib.Tactic.Nontriviality

/-!
# Lemmas about commuting elements in a `MonoidWithZero` or a `GroupWithZero`.

-/

public section

assert_not_exists DenselyOrdered Ring

open scoped Ring

variable {M₀ G₀ : Type*}
variable [MonoidWithZero M₀]

namespace Ring

/-
**Ring.mul_inverse_rev'** 是 Mathlib 中的一个定理，位于命名空间 `Ring`。
形式化陈述：mul_inverse_rev' {a b : M₀} (h : Commute a b) : inverse (a * b) = inverse 
b * inverse a
参数：h : Commute a b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Commute.isUnit_mul_iff`：Commute.isUnit_mul_iff (h : Commute a b) : IsUni
t (a * b) ↔ IsUnit a ∧ IsUnit b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Units.val_mul`：val_mul : (↑(a * b) : α) = a * b
· 使用定理 `Ring.inverse_unit`：inverse_unit (u : M₀ˣ) : (u : M₀)⁻¹ʳ = (u⁻¹ : M₀ˣ)
· 使用定理 `mul_inv_rev`：mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹
· 使用定理 `not_and_or`：not_and_or : ¬(a ∧ b) ↔ ¬a ∨ ¬b
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Ring.inverse_non_unit`：inverse_non_unit (x : M₀) (h : ¬IsUnit x) : x⁻¹ʳ 
= 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
-/
theorem mul_inverse_rev' {a b : M₀} (h : Commute a b) :
    inverse (a * b) = inverse b * inverse a := by
  by_cases hab : IsUnit (a * b)
  · obtain ⟨⟨a, rfl⟩, b, rfl⟩ := h.isUnit_mul_iff.mp hab
    rw [← Units.val_mul, inverse_unit, inverse_unit, inverse_unit, ← Units.val_mul, mul_inv_rev]
  obtain ha | hb := not_and_or.mp (mt h.isUnit_mul_iff.mpr hab)
  · rw [inverse_non_unit _ hab, inverse_non_unit _ ha, mul_zero]
  · rw [inverse_non_unit _ hab, inverse_non_unit _ hb, zero_mul]
/-
**Ring.mul_inverse_rev** 是 Mathlib 中的一个定理，位于命名空间 `Ring`。
形式化陈述：mul_inverse_rev {M₀} [CommMonoidWithZero M₀] (a b : M₀) : (a * b)⁻¹ʳ = b⁻¹
ʳ * a⁻¹ʳ
参数：a b : M₀。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ring.mul_inverse_rev'`：mul_inverse_rev' {a b : M₀} (h : Commute a b) : i
nverse (a * b) = inverse b * inverse a
· 使用定理 `Commute.all`：∀ {S : Type u_3} [inst : CommMagma S] (a b : S), Commute a 
b
-/
theorem mul_inverse_rev {M₀} [CommMonoidWithZero M₀] (a b : M₀) :
    (a * b)⁻¹ʳ = b⁻¹ʳ * a⁻¹ʳ :=
  mul_inverse_rev' (Commute.all _ _)
/-
**Ring.inverse_pow** 是 Mathlib 中的一个定理，位于命名空间 `Ring`。
形式化陈述：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀] (r : M₀) (n : ℕ), Ring.invers
e r ^ n = Ring.inverse (r ^ n)
参数：r : M₀；n : ℕ；r ^ n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma inverse_pow (r : M₀) : ∀ n : ℕ, r⁻¹ʳ ^ n = (r ^ n)⁻¹ʳ
  | 0 => by rw [pow_zero, pow_zero, Ring.inverse_one]
  | n + 1 => by
    rw [pow_succ', pow_succ, Ring.mul_inverse_rev' ((Commute.refl r).pow_left n),
      Ring.inverse_pow r n]
/-
**Ring.inverse_pow_mul_eq_iff_eq_mul** 是 Mathlib 中的一个引理，位于命名空间 `Ring`。
形式化陈述：inverse_pow_mul_eq_iff_eq_mul {a : M₀} (b c : M₀) (ha : IsUnit a) {k : Nat
} : a⁻¹ʳ ^ k * b = c ↔ b = a ^ k * c
参数：b c : M₀；ha : IsUnit a。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ring.inverse_pow`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀] (r : M₀) 
(n : ℕ), Ring.inverse r ^ n = Ring.inverse (r ^ n)
· 使用定理 `Ring.inverse_mul_eq_iff_eq_mul`：inverse_mul_eq_iff_eq_mul (x y z : M₀) (
h : IsUnit x) : x⁻¹ʳ * y = z ↔ y = x * z
· 使用定理 `IsUnit.pow`：∀ {M : Type u_1} [inst : Monoid M] {a : M} (n : ℕ), IsUnit a
 → IsUnit (a ^ n)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma inverse_pow_mul_eq_iff_eq_mul {a : M₀} (b c : M₀) (ha : IsUnit a) {k : ℕ} :
    a⁻¹ʳ ^ k * b = c ↔ b = a ^ k * c := by
  rw [Ring.inverse_pow, Ring.inverse_mul_eq_iff_eq_mul _ _ _ (IsUnit.pow _ ha)]

end Ring

@[grind ←]
/-
**Commute.ringInverse_ringInverse** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Commute.ringInverse_ringInverse {a b : M₀} (h : Commute a b) : Commute a⁻¹
ʳ b⁻¹ʳ
参数：h : Commute a b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ring.mul_inverse_rev'`：mul_inverse_rev' {a b : M₀} (h : Commute a b) : i
nverse (a * b) = inverse b * inverse a
· 使用定理 `Commute.symm`：∀ {S : Type u_3} [inst : Mul S] {a b : S}, Commute a b → C
ommute b a
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Commute.eq`：∀ {S : Type u_3} [inst : Mul S] {a b : S}, Commute a b → a *
 b = b * a
-/
theorem Commute.ringInverse_ringInverse {a b : M₀} (h : Commute a b) :
    Commute a⁻¹ʳ b⁻¹ʳ :=
  (Ring.mul_inverse_rev' h.symm).symm.trans <| (congr_arg _ h.symm.eq).trans <|
    Ring.mul_inverse_rev' h

namespace Commute

@[simp]
/-
**Commute.zero_right** 是 Mathlib 中的一个定理，位于命名空间 `Commute`。
形式化陈述：zero_right [MulZeroClass G₀] (a : G₀) : Commute a 0
参数：a : G₀。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SemiconjBy.zero_right`：zero_right [MulZeroClass G₀] (a : G₀) : SemiconjB
y a 0 0
-/
theorem zero_right [MulZeroClass G₀] (a : G₀) : Commute a 0 :=
  SemiconjBy.zero_right a

@[simp]
/-
**Commute.zero_left** 是 Mathlib 中的一个定理，位于命名空间 `Commute`。
形式化陈述：zero_left [MulZeroClass G₀] (a : G₀) : Commute 0 a
参数：a : G₀。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SemiconjBy.zero_left`：zero_left [MulZeroClass G₀] (x y : G₀) : SemiconjB
y 0 x y
-/
theorem zero_left [MulZeroClass G₀] (a : G₀) : Commute 0 a :=
  SemiconjBy.zero_left a a

variable [GroupWithZero G₀] {a b c : G₀}

@[simp]
/-
**Commute.inv_left_iff** 是 Mathlib 中的一个引理，位于命名空间 `Commute`。
形式化陈述：inv_left_iff : Commute a⁻¹ b ↔ Commute a b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SemiconjBy.inv_symm_left_iff`：∀ {G : Type u_1} [inst : Group G] {a x y :
 G}, SemiconjBy a⁻¹ y x ↔ SemiconjBy a x y
-/
theorem inv_left_iff₀ : Commute a⁻¹ b ↔ Commute a b :=
  SemiconjBy.inv_symm_left_iff₀
/-
**Commute.inv_left** 是 Mathlib 中的一个定理，位于命名空间 `Commute`。
形式化陈述：∀ {G : Type u_1} [inst : Group G] {a b : G}, Commute a b → Commute a⁻¹ b
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Commute.inv_left_iff`：inv_left_iff : Commute a⁻¹ b ↔ Commute a b
-/
theorem inv_left₀ (h : Commute a b) : Commute a⁻¹ b :=
  inv_left_iff₀.2 h

@[simp]
/-
**Commute.inv_right_iff** 是 Mathlib 中的一个引理，位于命名空间 `Commute`。
形式化陈述：inv_right_iff : Commute a b⁻¹ ↔ Commute a b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SemiconjBy.inv_right_iff`：∀ {G : Type u_1} [inst : Group G] {a x y : G},
 SemiconjBy a x⁻¹ y⁻¹ ↔ SemiconjBy a x y
-/
theorem inv_right_iff₀ : Commute a b⁻¹ ↔ Commute a b :=
  SemiconjBy.inv_right_iff₀
/-
**Commute.inv_right** 是 Mathlib 中的一个定理，位于命名空间 `Commute`。
形式化陈述：∀ {G : Type u_1} [inst : Group G] {a b : G}, Commute a b → Commute a b⁻¹
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Commute.inv_right_iff`：inv_right_iff : Commute a b⁻¹ ↔ Commute a b
-/
theorem inv_right₀ (h : Commute a b) : Commute a b⁻¹ :=
  inv_right_iff₀.2 h

@[simp]
/-
**Commute.div_right** 是 Mathlib 中的一个定理，位于命名空间 `Commute`。
形式化陈述：div_right (hab : Commute a b) (hac : Commute a c) : Commute a (b / c)
参数：hab : Commute a b；hac : Commute a c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SemiconjBy.div_right`：div_right (h : SemiconjBy a x y) (h' : SemiconjBy 
a x' y') : SemiconjBy a (x / x') (y / y')
-/
theorem div_right (hab : Commute a b) (hac : Commute a c) : Commute a (b / c) :=
  SemiconjBy.div_right hab hac

@[simp]
/-
**Commute.div_left** 是 Mathlib 中的一个定理，位于命名空间 `Commute`。
形式化陈述：div_left (hac : Commute a c) (hbc : Commute b c) : Commute (a / b) c
参数：hac : Commute a c；hbc : Commute b c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `Commute.mul_left`：mul_left (hac : Commute a c) (hbc : Commute b c) : Com
mute (a * b) c
· 使用定理 `Commute.inv_left₀`：inv_left₀ (h : Commute a b) : Commute a⁻¹ b
-/
theorem div_left (hac : Commute a c) (hbc : Commute b c) : Commute (a / b) c := by
  rw [div_eq_mul_inv]
  exact hac.mul_left hbc.inv_left₀

end Commute

section GroupWithZero
variable [GroupWithZero G₀]

/-
**pow_inv_comm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {G : Type u_1} [inst : Group G] (a : G) (m n : ℕ), a⁻¹ ^ m * a ^ n = a ^
 n * a⁻¹ ^ m
参数：a : G；m n : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Commute.pow_pow`：pow_pow (h : Commute a b) (m n : Nat) : Commute (a ^ m)
 (b ^ n)
· 使用定理 `Commute.inv_left`：∀ {G : Type u_1} [inst : Group G] {a b : G}, Commute a
 b → Commute a⁻¹ b
· 使用定理 `Commute.refl`：∀ {S : Type u_3} [inst : Mul S] (a : S), Commute a a
-/
theorem pow_inv_comm₀ (a : G₀) (m n : ℕ) : a⁻¹ ^ m * a ^ n = a ^ n * a⁻¹ ^ m :=
  (Commute.refl a).inv_left₀.pow_pow m n

end GroupWithZero

