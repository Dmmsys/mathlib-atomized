/-
Copyright (c) 2018 Louis Carlin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Louis Carlin, Mario Carneiro
-/
module

public import Mathlib.Algebra.EuclideanDomain.Defs
public import Mathlib.Algebra.Ring.Divisibility.Basic
public import Mathlib.Algebra.GroupWithZero.Divisibility
public import Mathlib.Algebra.Ring.Equiv

/-!
# Lemmas about Euclidean domains

## Main statements

* `gcd_eq_gcd_ab`: states Bézout's lemma for Euclidean domains.

-/

@[expose] public section


universe u

namespace EuclideanDomain

variable {R : Type u}
variable [EuclideanDomain R]

/-- The well-founded relation in a Euclidean Domain satisfying `a % b ≺ b` for `b ≠ 0` -/
local infixl:50 " ≺ " => EuclideanDomain.r

-- See note [lower instance priority]
/-
**EuclideanDomain.** 是 Mathlib 中的一个实例，位于命名空间 `EuclideanDomain`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) toMulDivCancelClass : MulDivCancelClass R where
  mul_div_cancel a b hb := by
    refine (eq_of_sub_eq_zero ?_).symm
    by_contra h
    have := mul_right_not_lt b h
    rw [sub_mul, mul_comm (_ / _), sub_eq_iff_eq_add'.2 (div_add_mod (a * b) b).symm] at this
    exact this (mod_lt _ hb)
/-
**EuclideanDomain.mod_eq_sub_mul_div** 是 Mathlib 中的一个定理，位于命名空间 `EuclideanDomain`
。
形式化陈述：mod_eq_sub_mul_div {R : Type*} [EuclideanDomain R] (a b : R) : a % b = a -
 b * (a / b)
参数：a b : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_sub_cancel_left`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G),
 a + b - a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EuclideanDomain.div_add_mod`：div_add_mod (a b : R) : b * (a / b) + a % b
 = a
-/
theorem mod_eq_sub_mul_div {R : Type*} [EuclideanDomain R] (a b : R) : a % b = a - b * (a / b) :=
  calc
    a % b = b * (a / b) + a % b - b * (a / b) := (add_sub_cancel_left _ _).symm
    _ = a - b * (a / b) := by rw [div_add_mod]
/-
**EuclideanDomain.val_dvd_le** 是 Mathlib 中的一个定理，位于命名空间 `EuclideanDomain`。
形式化陈述：∀ {R : Type u} [inst : EuclideanDomain R] (a b : R), b ∣ a → a ≠ 0 → ¬Eucl
ideanDomain.r a b
参数：a b : R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EuclideanDomain.mul_left_not_lt`：∀ {R : Type u} [self : EuclideanDomain 
R] (a : R) {b : R}, b ≠ 0 → ¬EuclideanDomain.r (a * b) a
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem val_dvd_le : ∀ a b : R, b ∣ a → a ≠ 0 → ¬a ≺ b
  | _, b, ⟨d, rfl⟩, ha => mul_left_not_lt b (mt (by rintro rfl; exact mul_zero _) ha)

@[simp]
/-
**EuclideanDomain.mod_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `EuclideanDomain`。
形式化陈述：mod_eq_zero {a b : R} : a % b = 0 ↔ b ∣ a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `EuclideanDomain.div_add_mod`：div_add_mod (a b : R) : b * (a / b) + a % b
 = a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `dvd_mul_right`：dvd_mul_right (a b : α) : a ∣ a * b
· 使用定理 `add_left_cancel_iff`：∀ {G : Type u_1} [inst : Add G] [IsLeftCancelAdd G]
 {a b c : G}, a + b = a + c ↔ b = c
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `mul_div_cancel_left₀`：∀ {M₀ : Type u_1} [inst : CommMonoidWithZero M₀] [
inst_1 : Div M₀] [MulDivCancelClass M₀] (b : M₀) {a : M₀},   a ≠ 0 → a * b / a =
 b
· 使用定理 `EuclideanDomain.toMulDivCancelClass`：∀ {R : Type u} [inst : EuclideanDom
ain R], MulDivCancelClass R
-/
theorem mod_eq_zero {a b : R} : a % b = 0 ↔ b ∣ a :=
  ⟨fun h => by
    rw [← div_add_mod a b, h, add_zero]
    exact dvd_mul_right _ _, fun ⟨c, e⟩ => by
    rw [e, ← add_left_cancel_iff, div_add_mod, add_zero]
    have := Classical.dec
    by_cases b0 : b = 0
    · simp only [b0, zero_mul]
    · rw [mul_div_cancel_left₀ _ b0]⟩

@[simp]
/-
**EuclideanDomain.mod_self** 是 Mathlib 中的一个定理，位于命名空间 `EuclideanDomain`。
形式化陈述：mod_self (a : R) : a % a = 0
参数：a : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `EuclideanDomain.mod_eq_zero`：mod_eq_zero {a b : R} : a % b = 0 ↔ b ∣ a
· 使用定理 `dvd_rfl`：dvd_rfl : forall {a : α}, a ∣ a
-/
theorem mod_self (a : R) : a % a = 0 :=
  mod_eq_zero.2 dvd_rfl
/-
**EuclideanDomain.dvd_mod_iff** 是 Mathlib 中的一个定理，位于命名空间 `EuclideanDomain`。
形式化陈述：dvd_mod_iff {a b c : R} (h : c ∣ b) : c ∣ a % b ↔ c ∣ a
参数：h : c ∣ b。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `dvd_add_right`：dvd_add_right (h : a ∣ b) : a ∣ b + c ↔ a ∣ c
· 使用定理 `Dvd.dvd.mul_right`：∀ {α : Type u_1} [inst : Semigroup α] {a b : α}, a ∣ 
b → ∀ (c : α), a ∣ b * c
· 使用定理 `EuclideanDomain.div_add_mod`：div_add_mod (a b : R) : b * (a / b) + a % b
 = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem dvd_mod_iff {a b c : R} (h : c ∣ b) : c ∣ a % b ↔ c ∣ a := by
  rw [← dvd_add_right (h.mul_right _), div_add_mod]

@[simp]
/-
**EuclideanDomain.mod_one** 是 Mathlib 中的一个定理，位于命名空间 `EuclideanDomain`。
形式化陈述：mod_one (a : R) : a % 1 = 0
参数：a : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `EuclideanDomain.mod_eq_zero`：mod_eq_zero {a b : R} : a % b = 0 ↔ b ∣ a
· 使用定理 `one_dvd`：one_dvd (a : α) : 1 ∣ a
-/
theorem mod_one (a : R) : a % 1 = 0 :=
  mod_eq_zero.2 (one_dvd _)

@[simp]
/-
**EuclideanDomain.zero_mod** 是 Mathlib 中的一个定理，位于命名空间 `EuclideanDomain`。
形式化陈述：zero_mod (b : R) : 0 % b = 0
参数：b : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `EuclideanDomain.mod_eq_zero`：mod_eq_zero {a b : R} : a % b = 0 ↔ b ∣ a
· 使用定理 `dvd_zero`：dvd_zero (a : α) : a ∣ 0
-/
theorem zero_mod (b : R) : 0 % b = 0 :=
  mod_eq_zero.2 (dvd_zero _)

@[simp]
/-
**EuclideanDomain.zero_div** 是 Mathlib 中的一个定理，位于命名空间 `EuclideanDomain`。
形式化陈述：zero_div {a : R} : 0 / a = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `by_cases`：by_cases {p q : Prop} (hpq : p -> q) (hnpq : ¬p -> q) : q
· 使用定理 `EuclideanDomain.div_zero`：div_zero (a : R) : a / 0 = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `mul_div_cancel_right₀`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀] [ins
t_1 : Div M₀] [MulDivCancelClass M₀] (a : M₀) {b : M₀},   b ≠ 0 → a * b / b = a
· 使用定理 `EuclideanDomain.toMulDivCancelClass`：∀ {R : Type u} [inst : EuclideanDom
ain R], MulDivCancelClass R
-/
theorem zero_div {a : R} : 0 / a = 0 :=
  by_cases (fun a0 : a = 0 => a0.symm ▸ div_zero 0) fun a0 => by
    simpa only [zero_mul] using mul_div_cancel_right₀ 0 a0

@[simp]
/-
**EuclideanDomain.div_self** 是 Mathlib 中的一个定理，位于命名空间 `EuclideanDomain`。
形式化陈述：div_self {a : R} (a0 : a != 0) : a / a = 1
参数：a0 : a != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `mul_div_cancel_right₀`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀] [ins
t_1 : Div M₀] [MulDivCancelClass M₀] (a : M₀) {b : M₀},   b ≠ 0 → a * b / b = a
· 使用定理 `EuclideanDomain.toMulDivCancelClass`：∀ {R : Type u} [inst : EuclideanDom
ain R], MulDivCancelClass R
-/
theorem div_self {a : R} (a0 : a ≠ 0) : a / a = 1 := by
  simpa only [one_mul] using mul_div_cancel_right₀ 1 a0
/-
**EuclideanDomain.eq_div_of_mul_eq_left** 是 Mathlib 中的一个定理，位于命名空间 `EuclideanDoma
in`。
形式化陈述：eq_div_of_mul_eq_left {a b c : R} (hb : b != 0) (h : a * b = c) : a = c / 
b
参数：hb : b != 0；h : a * b = c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_div_cancel_right₀`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀] [ins
t_1 : Div M₀] [MulDivCancelClass M₀] (a : M₀) {b : M₀},   b ≠ 0 → a * b / b = a
· 使用定理 `EuclideanDomain.toMulDivCancelClass`：∀ {R : Type u} [inst : EuclideanDom
ain R], MulDivCancelClass R
-/
theorem eq_div_of_mul_eq_left {a b c : R} (hb : b ≠ 0) (h : a * b = c) : a = c / b := by
  rw [← h, mul_div_cancel_right₀ _ hb]
/-
**EuclideanDomain.eq_div_of_mul_eq_right** 是 Mathlib 中的一个定理，位于命名空间 `EuclideanDom
ain`。
形式化陈述：eq_div_of_mul_eq_right {a b c : R} (ha : a != 0) (h : a * b = c) : b = c /
 a
参数：ha : a != 0；h : a * b = c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_div_cancel_left₀`：∀ {M₀ : Type u_1} [inst : CommMonoidWithZero M₀] [
inst_1 : Div M₀] [MulDivCancelClass M₀] (b : M₀) {a : M₀},   a ≠ 0 → a * b / a =
 b
· 使用定理 `EuclideanDomain.toMulDivCancelClass`：∀ {R : Type u} [inst : EuclideanDom
ain R], MulDivCancelClass R
-/
theorem eq_div_of_mul_eq_right {a b c : R} (ha : a ≠ 0) (h : a * b = c) : b = c / a := by
  rw [← h, mul_div_cancel_left₀ _ ha]
/-
**EuclideanDomain.mul_div_assoc** 是 Mathlib 中的一个定理，位于命名空间 `EuclideanDomain`。
形式化陈述：mul_div_assoc (x : R) {y z : R} (h : z ∣ y) : x * y / z = x * (y / z)
参数：x : R；h : z ∣ y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EuclideanDomain.div_zero`：div_zero (a : R) : a / 0 = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_div_cancel_left₀`：∀ {M₀ : Type u_1} [inst : CommMonoidWithZero M₀] [
inst_1 : Div M₀] [MulDivCancelClass M₀] (b : M₀) {a : M₀},   a ≠ 0 → a * b / a =
 b
· 使用定理 `EuclideanDomain.toMulDivCancelClass`：∀ {R : Type u} [inst : EuclideanDom
ain R], MulDivCancelClass R
· 使用定理 `mul_left_comm`：mul_left_comm (a b c : G) : a * (b * c) = b * (a * c)
-/
theorem mul_div_assoc (x : R) {y z : R} (h : z ∣ y) : x * y / z = x * (y / z) := by
  by_cases hz : z = 0
  · subst hz
    rw [div_zero, div_zero, mul_zero]
  rcases h with ⟨p, rfl⟩
  rw [mul_div_cancel_left₀ _ hz, mul_left_comm, mul_div_cancel_left₀ _ hz]
/-
**EuclideanDomain.mul_div_cancel'** 是 Mathlib 中的一个定理，位于命名空间 `EuclideanDomain`。
形式化陈述：∀ {R : Type u} [inst : EuclideanDomain R] {a b : R}, b ≠ 0 → b ∣ a → b * (
a / b) = a
参数：a / b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `EuclideanDomain.mul_div_assoc`：mul_div_assoc (x : R) {y z : R} (h : z ∣ 
y) : x * y / z = x * (y / z)
· 使用定理 `mul_div_cancel_left₀`：∀ {M₀ : Type u_1} [inst : CommMonoidWithZero M₀] [
inst_1 : Div M₀] [MulDivCancelClass M₀] (b : M₀) {a : M₀},   a ≠ 0 → a * b / a =
 b
· 使用定理 `EuclideanDomain.toMulDivCancelClass`：∀ {R : Type u} [inst : EuclideanDom
ain R], MulDivCancelClass R
-/
protected theorem mul_div_cancel' {a b : R} (hb : b ≠ 0) (hab : b ∣ a) : b * (a / b) = a := by
  rw [← mul_div_assoc _ hab, mul_div_cancel_left₀ _ hb]

-- This generalizes `Int.div_one`, see note [simp-normal form]
@[simp]
/-
**EuclideanDomain.div_one** 是 Mathlib 中的一个定理，位于命名空间 `EuclideanDomain`。
形式化陈述：div_one (p : R) : p / 1 = p
参数：p : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `EuclideanDomain.eq_div_of_mul_eq_left`：eq_div_of_mul_eq_left {a b c : R}
 (hb : b != 0) (h : a * b = c) : a = c / b
· 使用引理 `one_ne_zero'`：one_ne_zero' [One α] [NeZero (1 : α)] : (1 : α) != 0
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
theorem div_one (p : R) : p / 1 = p :=
  (EuclideanDomain.eq_div_of_mul_eq_left (one_ne_zero' R) (mul_one p)).symm
/-
**EuclideanDomain.div_dvd_of_dvd** 是 Mathlib 中的一个定理，位于命名空间 `EuclideanDomain`。
形式化陈述：div_dvd_of_dvd {p q : R} (hpq : q ∣ p) : p / q ∣ p
参数：hpq : q ∣ p。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_dvd_iff`：zero_dvd_iff : 0 ∣ a ↔ a = 0
· 使用定理 `dvd_zero`：dvd_zero (a : α) : a ∣ 0
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `EuclideanDomain.mul_div_assoc`：mul_div_assoc (x : R) {y z : R} (h : z ∣ 
y) : x * y / z = x * (y / z)
· 使用定理 `mul_div_cancel_right₀`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀] [ins
t_1 : Div M₀] [MulDivCancelClass M₀] (a : M₀) {b : M₀},   b ≠ 0 → a * b / b = a
· 使用定理 `EuclideanDomain.toMulDivCancelClass`：∀ {R : Type u} [inst : EuclideanDom
ain R], MulDivCancelClass R
-/
theorem div_dvd_of_dvd {p q : R} (hpq : q ∣ p) : p / q ∣ p := by
  by_cases hq : q = 0
  · rw [hq, zero_dvd_iff] at hpq
    rw [hpq]
    exact dvd_zero _
  use q
  rw [mul_comm, ← EuclideanDomain.mul_div_assoc _ hpq, mul_comm, mul_div_cancel_right₀ _ hq]
/-
**EuclideanDomain.dvd_div_of_mul_dvd** 是 Mathlib 中的一个定理，位于命名空间 `EuclideanDomain`
。
形式化陈述：dvd_div_of_mul_dvd {a b c : R} (h : a * b ∣ c) : b ∣ c / a
参数：h : a * b ∣ c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EuclideanDomain.div_zero`：div_zero (a : R) : a / 0 = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `mul_div_cancel_left₀`：∀ {M₀ : Type u_1} [inst : CommMonoidWithZero M₀] [
inst_1 : Div M₀] [MulDivCancelClass M₀] (b : M₀) {a : M₀},   a ≠ 0 → a * b / a =
 b
· 使用定理 `EuclideanDomain.toMulDivCancelClass`：∀ {R : Type u} [inst : EuclideanDom
ain R], MulDivCancelClass R
-/
theorem dvd_div_of_mul_dvd {a b c : R} (h : a * b ∣ c) : b ∣ c / a := by
  rcases eq_or_ne a 0 with (rfl | ha)
  · simp only [div_zero, dvd_zero]
  rcases h with ⟨d, rfl⟩
  refine ⟨d, ?_⟩
  rw [mul_assoc, mul_div_cancel_left₀ _ ha]

section GCD

variable [DecidableEq R]

@[simp]
/-
**EuclideanDomain.gcd_zero_right** 是 Mathlib 中的一个定理，位于命名空间 `EuclideanDomain`。
形式化陈述：gcd_zero_right (a : R) : gcd a 0 = a
参数：a : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EuclideanDomain.mod_lt`：mod_lt : forall (a) {b : R}, b != 0 -> a % b ≺ b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EuclideanDomain.gcd.eq_1`：∀ {R : Type u} [inst : EuclideanDomain R] [ins
t_1 : DecidableEq R] (a b : R),   EuclideanDomain.gcd a b =     if a0 : a = 0 th
en b     else …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `EuclideanDomain.zero_mod`：zero_mod (b : R) : 0 % b = 0
· 使用定理 `EuclideanDomain.gcd_zero_left`：gcd_zero_left (a : R) : gcd 0 a = a
-/
theorem gcd_zero_right (a : R) : gcd a 0 = a := by
  rw [gcd]
  split_ifs with h <;> simp only [h, zero_mod, gcd_zero_left]
/-
**EuclideanDomain.gcd_val** 是 Mathlib 中的一个定理，位于命名空间 `EuclideanDomain`。
形式化陈述：gcd_val (a b : R) : gcd a b = gcd (b % a) a
参数：a b : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EuclideanDomain.mod_lt`：mod_lt : forall (a) {b : R}, b != 0 -> a % b ≺ b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EuclideanDomain.gcd.eq_1`：∀ {R : Type u} [inst : EuclideanDomain R] [ins
t_1 : DecidableEq R] (a b : R),   EuclideanDomain.gcd a b =     if a0 : a = 0 th
en b     else …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `EuclideanDomain.mod_zero`：mod_zero (a : R) : a % 0 = a
· 使用定理 `EuclideanDomain.gcd_zero_right`：gcd_zero_right (a : R) : gcd a 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
-/
theorem gcd_val (a b : R) : gcd a b = gcd (b % a) a := by
  rw [gcd]
  split_ifs with h <;> [simp only [h, mod_zero, gcd_zero_right]; rfl]
/-
**EuclideanDomain.gcd_dvd** 是 Mathlib 中的一个定理，位于命名空间 `EuclideanDomain`。
形式化陈述：gcd_dvd (a b : R) : gcd a b ∣ a ∧ gcd a b ∣ b
参数：a b : R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EuclideanDomain.GCD.induction`：∀ {R : Type u} [inst : EuclideanDomain R]
 {P : R → R → Prop} (a b : R),   (∀ (x : R), P 0 x) → (∀ (a b : R), a ≠ 0 → P (b
 % a) a → P a b) → …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EuclideanDomain.gcd_zero_left`：gcd_zero_left (a : R) : gcd 0 a = a
· 使用定理 `dvd_zero`：dvd_zero (a : α) : a ∣ 0
· 使用定理 `dvd_rfl`：dvd_rfl : forall {a : α}, a ∣ a
· 使用定理 `EuclideanDomain.gcd_val`：gcd_val (a b : R) : gcd a b = gcd (b % a) a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `EuclideanDomain.dvd_mod_iff`：dvd_mod_iff {a b c : R} (h : c ∣ b) : c ∣ a
 % b ↔ c ∣ a
-/
theorem gcd_dvd (a b : R) : gcd a b ∣ a ∧ gcd a b ∣ b :=
  GCD.induction a b
    (fun b => by
      rw [gcd_zero_left]
      exact ⟨dvd_zero _, dvd_rfl⟩)
    fun a b _ ⟨IH₁, IH₂⟩ => by
    rw [gcd_val]
    exact ⟨IH₂, (dvd_mod_iff IH₂).1 IH₁⟩
/-
**EuclideanDomain.gcd_dvd_left** 是 Mathlib 中的一个定理，位于命名空间 `EuclideanDomain`。
形式化陈述：gcd_dvd_left (a b : R) : gcd a b ∣ a
参数：a b : R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `EuclideanDomain.gcd_dvd`：gcd_dvd (a b : R) : gcd a b ∣ a ∧ gcd a b ∣ b
-/
theorem gcd_dvd_left (a b : R) : gcd a b ∣ a :=
  (gcd_dvd a b).left
/-
**EuclideanDomain.gcd_dvd_right** 是 Mathlib 中的一个定理，位于命名空间 `EuclideanDomain`。
形式化陈述：gcd_dvd_right (a b : R) : gcd a b ∣ b
参数：a b : R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `EuclideanDomain.gcd_dvd`：gcd_dvd (a b : R) : gcd a b ∣ a ∧ gcd a b ∣ b
-/
theorem gcd_dvd_right (a b : R) : gcd a b ∣ b :=
  (gcd_dvd a b).right
/-
**EuclideanDomain.gcd_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `EuclideanDomain`。
形式化陈述：∀ {R : Type u} [inst : EuclideanDomain R] [inst_1 : DecidableEq R] {a b : 
R},   EuclideanDomain.gcd a b = 0 ↔ a = 0 ∧ b = 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `EuclideanDomain.gcd_dvd`：gcd_dvd (a b : R) : gcd a b ∣ a ∧ gcd a b ∣ b
· 使用定理 `EuclideanDomain.gcd_zero_right`：gcd_zero_right (a : R) : gcd a 0 = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
protected theorem gcd_eq_zero_iff {a b : R} : gcd a b = 0 ↔ a = 0 ∧ b = 0 :=
  ⟨fun h => by simpa [h] using gcd_dvd a b, by
    rintro ⟨rfl, rfl⟩
    exact gcd_zero_right _⟩
/-
**EuclideanDomain.dvd_gcd** 是 Mathlib 中的一个定理，位于命名空间 `EuclideanDomain`。
形式化陈述：dvd_gcd {a b c : R} : c ∣ a -> c ∣ b -> c ∣ gcd a b
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EuclideanDomain.GCD.induction`：∀ {R : Type u} [inst : EuclideanDomain R]
 {P : R → R → Prop} (a b : R),   (∀ (x : R), P 0 x) → (∀ (a b : R), a ≠ 0 → P (b
 % a) a → P a b) → …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EuclideanDomain.gcd_zero_left`：gcd_zero_left (a : R) : gcd 0 a = a
· 使用定理 `EuclideanDomain.gcd_val`：gcd_val (a b : R) : gcd a b = gcd (b % a) a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `EuclideanDomain.dvd_mod_iff`：dvd_mod_iff {a b c : R} (h : c ∣ b) : c ∣ a
 % b ↔ c ∣ a
-/
theorem dvd_gcd {a b c : R} : c ∣ a → c ∣ b → c ∣ gcd a b :=
  GCD.induction a b (fun _ _ H => by simpa only [gcd_zero_left] using H) fun a b _ IH ca cb => by
    rw [gcd_val]
    exact IH ((dvd_mod_iff ca).2 cb) ca
/-
**EuclideanDomain.gcd_eq_left** 是 Mathlib 中的一个定理，位于命名空间 `EuclideanDomain`。
形式化陈述：gcd_eq_left {a b : R} : gcd a b = a ↔ a ∣ b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `EuclideanDomain.gcd_dvd_right`：gcd_dvd_right (a b : R) : gcd a b ∣ b
· 使用定理 `EuclideanDomain.gcd_val`：gcd_val (a b : R) : gcd a b = gcd (b % a) a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `EuclideanDomain.mod_eq_zero`：mod_eq_zero {a b : R} : a % b = 0 ↔ b ∣ a
· 使用定理 `EuclideanDomain.gcd_zero_left`：gcd_zero_left (a : R) : gcd 0 a = a
-/
theorem gcd_eq_left {a b : R} : gcd a b = a ↔ a ∣ b :=
  ⟨fun h => by
    rw [← h]
    apply gcd_dvd_right, fun h => by rw [gcd_val, mod_eq_zero.2 h, gcd_zero_left]⟩

@[simp]
/-
**EuclideanDomain.gcd_one_left** 是 Mathlib 中的一个定理，位于命名空间 `EuclideanDomain`。
形式化陈述：gcd_one_left (a : R) : gcd 1 a = 1
参数：a : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `EuclideanDomain.gcd_eq_left`：gcd_eq_left {a b : R} : gcd a b = a ↔ a ∣ b
· 使用定理 `one_dvd`：one_dvd (a : α) : 1 ∣ a
-/
theorem gcd_one_left (a : R) : gcd 1 a = 1 :=
  gcd_eq_left.2 (one_dvd _)

@[simp]
/-
**EuclideanDomain.gcd_self** 是 Mathlib 中的一个定理，位于命名空间 `EuclideanDomain`。
形式化陈述：gcd_self (a : R) : gcd a a = a
参数：a : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `EuclideanDomain.gcd_eq_left`：gcd_eq_left {a b : R} : gcd a b = a ↔ a ∣ b
· 使用定理 `dvd_rfl`：dvd_rfl : forall {a : α}, a ∣ a
-/
theorem gcd_self (a : R) : gcd a a = a :=
  gcd_eq_left.2 dvd_rfl

@[simp]
/-
**EuclideanDomain.xgcdAux_fst** 是 Mathlib 中的一个定理，位于命名空间 `EuclideanDomain`。
形式化陈述：xgcdAux_fst (x y : R) : forall s t s' t', (xgcdAux x s t y s' t').1 = gcd 
x y
参数：x y : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EuclideanDomain.GCD.induction`：∀ {R : Type u} [inst : EuclideanDomain R]
 {P : R → R → Prop} (a b : R),   (∀ (x : R), P 0 x) → (∀ (a b : R), a ≠ 0 → P (b
 % a) a → P a b) → …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EuclideanDomain.xgcd_zero_left`：xgcd_zero_left {s t r' s' t' : R} : xgcd
Aux 0 s t r' s' t' = (r', s', t')
· 使用定理 `EuclideanDomain.gcd_zero_left`：gcd_zero_left (a : R) : gcd 0 a = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `EuclideanDomain.xgcdAux_rec`：xgcdAux_rec {r s t r' s' t' : R} (h : r != 
0) : xgcdAux r s t r' s' t' = xgcdAux (r' % r) (s' - r' / r * s) (t' - r' / r * 
t) r s t
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `EuclideanDomain.gcd_val`：gcd_val (a b : R) : gcd a b = gcd (b % a) a
-/
theorem xgcdAux_fst (x y : R) : ∀ s t s' t', (xgcdAux x s t y s' t').1 = gcd x y :=
  GCD.induction x y
    (by
      intros
      rw [xgcd_zero_left, gcd_zero_left])
    fun x y h IH s t s' t' => by
    simp only [xgcdAux_rec h, IH]
    rw [← gcd_val]
/-
**EuclideanDomain.xgcdAux_val** 是 Mathlib 中的一个定理，位于命名空间 `EuclideanDomain`。
形式化陈述：xgcdAux_val (x y : R) : xgcdAux x 1 0 y 0 1 = (gcd x y, xgcd x y)
参数：x y : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EuclideanDomain.xgcd.eq_1`：∀ {R : Type u} [inst : EuclideanDomain R] [in
st_1 : DecidableEq R] (x y : R),   EuclideanDomain.xgcd x y = (EuclideanDomain.x
gcdAux x 1 0 y …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `EuclideanDomain.xgcdAux_fst`：xgcdAux_fst (x y : R) : forall s t s' t', (
xgcdAux x s t y s' t').1 = gcd x y
-/
theorem xgcdAux_val (x y : R) : xgcdAux x 1 0 y 0 1 = (gcd x y, xgcd x y) := by
  rw [xgcd, ← xgcdAux_fst x y 1 0 0 1]

set_option backward.privateInPublic true in
/-
**EuclideanDomain.P** 是 Mathlib 中的一个定义，位于命名空间 `EuclideanDomain`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private def P (a b : R) : R × R × R → Prop
  | (r, s, t) => (r : R) = a * s + b * t

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-
**EuclideanDomain.xgcdAux_P** 是 Mathlib 中的一个定理，位于命名空间 `EuclideanDomain`。
形式化陈述：xgcdAux_P (a b : R) {r r' : R} {s t s' t'} (p : P a b (r, s, t)) (p' : P a
 b (r', s', t')) : P a b (xgcdAux r s t r' s' t')
参数：a b : R；p : P a b (r, s, t)；p' : P a b (r', s', t')。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EuclideanDomain.GCD.induction`：∀ {R : Type u} [inst : EuclideanDomain R]
 {P : R → R → Prop} (a b : R),   (∀ (x : R), P 0 x) → (∀ (a b : R), a ≠ 0 → P (b
 % a) a → P a b) → …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EuclideanDomain.xgcd_zero_left`：xgcd_zero_left {s t r' s' t' : R} : xgcd
Aux 0 s t r' s' t' = (r', s', t')
· 使用定理 `EuclideanDomain.xgcdAux_rec`：xgcdAux_rec {r s t r' s' t' : R} (h : r != 
0) : xgcdAux r s t r' s' t' = xgcdAux (r' % r) (s' - r' / r * s) (t' - r' / r * 
t) r s t
· 使用定理 `mul_sub`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), a 
* (b - c) = a * b - a * c
· 使用定理 `add_sub`：∀ {G : Type u_3} [inst : SubNegMonoid G] (a b c : G), a + (b - 
c) = a + b - c
· 使用定理 `sub_add_eq_add_sub`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a
 b c : α), a - b + c = a + c - b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_sub`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a b c : α), 
a - b - c = a - (b + c)
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `add_mul`：add_mul {d : R} (_ : (a₁ : R) * b = c₁) (_ : a₂ * b = c₂) (_ : 
c₁ + c₂ = d) : (a₁ + a₂) * b = d
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
· 使用定理 `EuclideanDomain.mod_eq_sub_mul_div`：mod_eq_sub_mul_div {R : Type*} [Eucl
ideanDomain R] (a b : R) : a % b = a - b * (a / b)
-/
theorem xgcdAux_P (a b : R) {r r' : R} {s t s' t'} (p : P a b (r, s, t))
    (p' : P a b (r', s', t')) : P a b (xgcdAux r s t r' s' t') := by
  induction r, r' using GCD.induction generalizing s t s' t' with
  | H0 n => simpa only [xgcd_zero_left]
  | H1 _ _ h IH =>
    rw [xgcdAux_rec h]
    refine IH ?_ p
    unfold P at p p' ⊢
    dsimp
    rw [mul_sub, mul_sub, add_sub, sub_add_eq_add_sub, ← p', sub_sub, mul_comm _ s, ← mul_assoc,
      mul_comm _ t, ← mul_assoc, ← add_mul, ← p, mod_eq_sub_mul_div]

/-- An explicit version of **Bézout's lemma** for Euclidean domains. -/
/-
**EuclideanDomain.gcd_eq_gcd_ab** 是 Mathlib 中的一个定理，位于命名空间 `EuclideanDomain`。
形式化陈述：gcd_eq_gcd_ab (a b : R) : (gcd a b : R) = a * gcdA a b + b * gcdB a b
参数：a b : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EuclideanDomain.xgcdAux_P`：xgcdAux_P (a b : R) {r r' : R} {s t s' t'} (p
 : P a b (r, s, t)) (p' : P a b (r', s', t')) : P a b (xgcdAux r s t r' s' t')
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `EuclideanDomain.xgcd_val`：xgcd_val (x y : R) : xgcd x y = (gcdA x y, gcd
B x y)
· 使用定理 `EuclideanDomain.xgcdAux_val`：xgcdAux_val (x y : R) : xgcdAux x 1 0 y 0 1
 = (gcd x y, xgcd x y)

--- 原说明 ---
An explicit version of **Bézout's lemma** for Euclidean domains.
-/
theorem gcd_eq_gcd_ab (a b : R) : (gcd a b : R) = a * gcdA a b + b * gcdB a b := by
  have :=
    @xgcdAux_P _ _ _ a b a b 1 0 0 1 (by dsimp [P]; rw [mul_one, mul_zero, add_zero])
      (by dsimp [P]; rw [mul_one, mul_zero, zero_add])
  rwa [xgcdAux_val, xgcd_val] at this

-- see Note [lower instance priority]
/-
**EuclideanDomain.** 是 Mathlib 中的一个实例，位于命名空间 `EuclideanDomain`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 70) (R : Type*) [e : EuclideanDomain R] : IsDomain R :=
  haveI := Classical.decEq R
  have : NoZeroDivisors R :=
  { eq_zero_or_eq_zero_of_mul_eq_zero {a b} h :=
      or_iff_not_and_not.2 fun h0 ↦ h0.1 <| by rw [← mul_div_cancel_right₀ a h0.2, h, zero_div] }
  { e, NoZeroDivisors.to_isDomain R with }
/-
**EuclideanDomain.div_pow** 是 Mathlib 中的一个定理，位于命名空间 `EuclideanDomain`。
形式化陈述：div_pow {R : Type*} [EuclideanDomain R] {a b : R} {n : Nat} (hab : b ∣ a) 
: (a / b) ^ n = a ^ n / b ^ n
参数：hab : b ∣ a。
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
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `EuclideanDomain.div_zero`：div_zero (a : R) : a / 0 = 0
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `EuclideanDomain.div_self`：div_self {a : R} (a0 : a != 0) : a / a = 1
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `mul_div_cancel_left₀`：∀ {M₀ : Type u_1} [inst : CommMonoidWithZero M₀] [
inst_1 : Div M₀] [MulDivCancelClass M₀] (b : M₀) {a : M₀},   a ≠ 0 → a * b / a =
 b
· 使用定理 `EuclideanDomain.toMulDivCancelClass`：∀ {R : Type u} [inst : EuclideanDom
ain R], MulDivCancelClass R
· 使用定理 `mul_pow`：mul_pow {ea₁ b c₁ : Nat} {xa₁ : R} (_ : ea₁ * b = c₁) (_ : a₂ ^
 b = c₂) : (xa₁ ^ ea₁ * a₂ : R) ^ b = xa₁ ^ c₁ * c₂
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `EuclideanDomain.instIsDomain`：∀ (R : Type u_1) [e : EuclideanDomain R], 
IsDomain R
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
-/
theorem div_pow {R : Type*} [EuclideanDomain R] {a b : R} {n : ℕ} (hab : b ∣ a) :
    (a / b) ^ n = a ^ n / b ^ n := by
  obtain ⟨c, rfl⟩ := hab
  obtain rfl | hb := eq_or_ne b 0
  · obtain rfl | hn := eq_or_ne n 0 <;> simp [*]
  · simp [hb, mul_pow]

end GCD

section LCM

variable [DecidableEq R]

/-
**EuclideanDomain.dvd_lcm_left** 是 Mathlib 中的一个定理，位于命名空间 `EuclideanDomain`。
形式化陈述：dvd_lcm_left (x y : R) : x ∣ lcm x y
参数：x y : R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `by_cases`：by_cases {p q : Prop} (hpq : p -> q) (hnpq : ¬p -> q) : q
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EuclideanDomain.lcm.eq_1`：∀ {R : Type u} [inst : EuclideanDomain R] [ins
t_1 : DecidableEq R] (x y : R),   EuclideanDomain.lcm x y = x * y / EuclideanDom
ain.gcd x y
· 使用定理 `EuclideanDomain.div_zero`：div_zero (a : R) : a / 0 = 0
· 使用定理 `dvd_zero`：dvd_zero (a : α) : a ∣ 0
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `EuclideanDomain.gcd_dvd`：gcd_dvd (a b : R) : gcd a b ∣ a ∧ gcd a b ∣ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `EuclideanDomain.eq_div_of_mul_eq_left`：eq_div_of_mul_eq_left {a b c : R}
 (hb : b != 0) (h : a * b = c) : a = c / b
· 使用定理 `mul_right_comm`：mul_right_comm (a b c : G) : a * b * c = a * c * b
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
-/
theorem dvd_lcm_left (x y : R) : x ∣ lcm x y :=
  by_cases
    (fun hxy : gcd x y = 0 => by
      rw [lcm, hxy, div_zero]
      exact dvd_zero _)
    fun hxy =>
    let ⟨z, hz⟩ := (gcd_dvd x y).2
    ⟨z, Eq.symm <| eq_div_of_mul_eq_left hxy <| by rw [mul_right_comm, mul_assoc, ← hz]⟩
/-
**EuclideanDomain.dvd_lcm_right** 是 Mathlib 中的一个定理，位于命名空间 `EuclideanDomain`。
形式化陈述：dvd_lcm_right (x y : R) : y ∣ lcm x y
参数：x y : R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `by_cases`：by_cases {p q : Prop} (hpq : p -> q) (hnpq : ¬p -> q) : q
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EuclideanDomain.lcm.eq_1`：∀ {R : Type u} [inst : EuclideanDomain R] [ins
t_1 : DecidableEq R] (x y : R),   EuclideanDomain.lcm x y = x * y / EuclideanDom
ain.gcd x y
· 使用定理 `EuclideanDomain.div_zero`：div_zero (a : R) : a / 0 = 0
· 使用定理 `dvd_zero`：dvd_zero (a : α) : a ∣ 0
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `EuclideanDomain.gcd_dvd`：gcd_dvd (a b : R) : gcd a b ∣ a ∧ gcd a b ∣ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `EuclideanDomain.eq_div_of_mul_eq_right`：eq_div_of_mul_eq_right {a b c : 
R} (ha : a != 0) (h : a * b = c) : b = c / a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `mul_right_comm`：mul_right_comm (a b c : G) : a * b * c = a * c * b
-/
theorem dvd_lcm_right (x y : R) : y ∣ lcm x y :=
  by_cases
    (fun hxy : gcd x y = 0 => by
      rw [lcm, hxy, div_zero]
      exact dvd_zero _)
    fun hxy =>
    let ⟨z, hz⟩ := (gcd_dvd x y).1
    ⟨z, Eq.symm <| eq_div_of_mul_eq_right hxy <| by rw [← mul_assoc, mul_right_comm, ← hz]⟩
/-
**EuclideanDomain.lcm_dvd** 是 Mathlib 中的一个定理，位于命名空间 `EuclideanDomain`。
形式化陈述：lcm_dvd {x y z : R} (hxz : x ∣ z) (hyz : y ∣ z) : lcm x y ∣ z
参数：hxz : x ∣ z；hyz : y ∣ z。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EuclideanDomain.lcm.eq_1`：∀ {R : Type u} [inst : EuclideanDomain R] [ins
t_1 : DecidableEq R] (x y : R),   EuclideanDomain.lcm x y = x * y / EuclideanDom
ain.gcd x y
· 使用定理 `EuclideanDomain.div_zero`：div_zero (a : R) : a / 0 = 0
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `EuclideanDomain.gcd_eq_zero_iff`：∀ {R : Type u} [inst : EuclideanDomain 
R] [inst_1 : DecidableEq R] {a b : R},   EuclideanDomain.gcd a b = 0 ↔ a = 0 ∧ b
 = 0
· 使用定理 `EuclideanDomain.gcd_dvd`：gcd_dvd (a b : R) : gcd a b ∣ a ∧ gcd a b ∣ b
· 使用定理 `EuclideanDomain.gcd_eq_gcd_ab`：gcd_eq_gcd_ab (a b : R) : (gcd a b : R) =
 a * gcdA a b + b * gcdB a b
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `dvd_add`：dvd_add [LeftDistribClass α] {a b c : α} (h₁ : a ∣ b) (h₂ : a ∣
 c) : a ∣ b + c
· 使用定理 `mul_left_comm`：mul_left_comm (a b c : G) : a * (b * c) = b * (a * c)
· 使用定理 `mul_dvd_mul_left`：mul_dvd_mul_left (a : α) (h : b ∣ c) : a * b ∣ a * c
· 使用定理 `Dvd.dvd.mul_right`：∀ {α : Type u_1} [inst : Semigroup α] {a b : α}, a ∣ 
b → ∀ (c : α), a ∣ b * c
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `mul_div_cancel_left₀`：∀ {M₀ : Type u_1} [inst : CommMonoidWithZero M₀] [
inst_1 : Div M₀] [MulDivCancelClass M₀] (b : M₀) {a : M₀},   a ≠ 0 → a * b / a =
 b
· 使用定理 `EuclideanDomain.toMulDivCancelClass`：∀ {R : Type u} [inst : EuclideanDom
ain R], MulDivCancelClass R
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `mul_left_inj'`：mul_left_inj' (hc : c != 0) : a * c = b * c ↔ a = b
· 使用定理 `IsCancelMulZero.toIsRightCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} 
{inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsRightCancelMulZero M₀
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `EuclideanDomain.instIsDomain`：∀ (R : Type u_1) [e : EuclideanDomain R], 
IsDomain R
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mul_right_comm`：mul_right_comm (a b c : G) : a * b * c = a * c * b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem lcm_dvd {x y z : R} (hxz : x ∣ z) (hyz : y ∣ z) : lcm x y ∣ z := by
  rw [lcm]
  by_cases hxy : gcd x y = 0
  · rw [hxy, div_zero]
    rw [EuclideanDomain.gcd_eq_zero_iff] at hxy
    rwa [hxy.1] at hxz
  rcases gcd_dvd x y with ⟨⟨r, hr⟩, ⟨s, hs⟩⟩
  suffices x * y ∣ z * gcd x y by
    obtain ⟨p, hp⟩ := this
    use p
    generalize gcd x y = g at hxy hs hp ⊢
    subst hs
    rw [mul_left_comm, mul_div_cancel_left₀ _ hxy, ← mul_left_inj' hxy, hp]
    rw [← mul_assoc]
    simp only [mul_right_comm]
  rw [gcd_eq_gcd_ab, mul_add]
  apply dvd_add
  · rw [mul_left_comm]
    gcongr
    apply hyz.mul_right
  · rw [mul_left_comm, mul_comm]
    gcongr
    apply hxz.mul_right

@[simp]
/-
**EuclideanDomain.lcm_dvd_iff** 是 Mathlib 中的一个定理，位于命名空间 `EuclideanDomain`。
形式化陈述：lcm_dvd_iff {x y z : R} : lcm x y ∣ z ↔ x ∣ z ∧ y ∣ z
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Dvd.dvd.trans`：∀ {α : Type u_1} [inst : Semigroup α] {a b c : α}, a ∣ b 
→ b ∣ c → a ∣ c
· 使用定理 `EuclideanDomain.dvd_lcm_left`：dvd_lcm_left (x y : R) : x ∣ lcm x y
· 使用定理 `EuclideanDomain.dvd_lcm_right`：dvd_lcm_right (x y : R) : y ∣ lcm x y
· 使用定理 `EuclideanDomain.lcm_dvd`：lcm_dvd {x y z : R} (hxz : x ∣ z) (hyz : y ∣ z)
 : lcm x y ∣ z
-/
theorem lcm_dvd_iff {x y z : R} : lcm x y ∣ z ↔ x ∣ z ∧ y ∣ z :=
  ⟨fun hz => ⟨(dvd_lcm_left _ _).trans hz, (dvd_lcm_right _ _).trans hz⟩, fun ⟨hxz, hyz⟩ =>
    lcm_dvd hxz hyz⟩

@[simp]
/-
**EuclideanDomain.lcm_zero_left** 是 Mathlib 中的一个定理，位于命名空间 `EuclideanDomain`。
形式化陈述：lcm_zero_left (x : R) : lcm 0 x = 0
参数：x : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EuclideanDomain.lcm.eq_1`：∀ {R : Type u} [inst : EuclideanDomain R] [ins
t_1 : DecidableEq R] (x y : R),   EuclideanDomain.lcm x y = x * y / EuclideanDom
ain.gcd x y
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `EuclideanDomain.zero_div`：zero_div {a : R} : 0 / a = 0
-/
theorem lcm_zero_left (x : R) : lcm 0 x = 0 := by rw [lcm, zero_mul, zero_div]

@[simp]
/-
**EuclideanDomain.lcm_zero_right** 是 Mathlib 中的一个定理，位于命名空间 `EuclideanDomain`。
形式化陈述：lcm_zero_right (x : R) : lcm x 0 = 0
参数：x : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EuclideanDomain.lcm.eq_1`：∀ {R : Type u} [inst : EuclideanDomain R] [ins
t_1 : DecidableEq R] (x y : R),   EuclideanDomain.lcm x y = x * y / EuclideanDom
ain.gcd x y
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `EuclideanDomain.zero_div`：zero_div {a : R} : 0 / a = 0
-/
theorem lcm_zero_right (x : R) : lcm x 0 = 0 := by rw [lcm, mul_zero, zero_div]

@[simp]
/-
**EuclideanDomain.lcm_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `EuclideanDomain`。
形式化陈述：lcm_eq_zero_iff {x y : R} : lcm x y = 0 ↔ x = 0 ∨ y = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.imp_right`：∀ {b c a : Prop}, (b → c) → a ∨ b → a ∨ c
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EuclideanDomain.gcd_eq_zero_iff`：∀ {R : Type u} [inst : EuclideanDomain 
R] [inst_1 : DecidableEq R] {a b : R},   EuclideanDomain.gcd a b = 0 ↔ a = 0 ∧ b
 = 0
· 使用定理 `EuclideanDomain.gcd_dvd`：gcd_dvd (a b : R) : gcd a b ∣ a ∧ gcd a b ∣ b
· 使用定理 `mul_div_cancel_left₀`：∀ {M₀ : Type u_1} [inst : CommMonoidWithZero M₀] [
inst_1 : Div M₀] [MulDivCancelClass M₀] (b : M₀) {a : M₀},   a ≠ 0 → a * b / a =
 b
· 使用定理 `EuclideanDomain.toMulDivCancelClass`：∀ {R : Type u} [inst : EuclideanDom
ain R], MulDivCancelClass R
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_eq_zero`：mul_eq_zero : a * b = 0 ↔ a = 0 ∨ b = 0
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `EuclideanDomain.instIsDomain`：∀ (R : Type u_1) [e : EuclideanDomain R], 
IsDomain R
· 使用定理 `EuclideanDomain.mul_div_assoc`：mul_div_assoc (x : R) {y z : R} (h : z ∣ 
y) : x * y / z = x * (y / z)
· 使用定理 `EuclideanDomain.gcd_dvd_right`：gcd_dvd_right (a b : R) : gcd a b ∣ b
· 使用定理 `EuclideanDomain.lcm.eq_1`：∀ {R : Type u} [inst : EuclideanDomain R] [ins
t_1 : DecidableEq R] (x y : R),   EuclideanDomain.lcm x y = x * y / EuclideanDom
ain.gcd x y
· 使用定理 `EuclideanDomain.lcm_zero_left`：lcm_zero_left (x : R) : lcm 0 x = 0
· 使用定理 `EuclideanDomain.lcm_zero_right`：lcm_zero_right (x : R) : lcm x 0 = 0
-/
theorem lcm_eq_zero_iff {x y : R} : lcm x y = 0 ↔ x = 0 ∨ y = 0 := by
  constructor
  · intro hxy
    rw [lcm, mul_div_assoc _ (gcd_dvd_right _ _), mul_eq_zero] at hxy
    apply Or.imp_right _ hxy
    intro hy
    by_cases hgxy : gcd x y = 0
    · rw [EuclideanDomain.gcd_eq_zero_iff] at hgxy
      exact hgxy.2
    · rcases gcd_dvd x y with ⟨⟨r, hr⟩, ⟨s, hs⟩⟩
      generalize gcd x y = g at hr hs hy hgxy ⊢
      subst hs
      rw [mul_div_cancel_left₀ _ hgxy] at hy
      rw [hy, mul_zero]
  rintro (hx | hy)
  · rw [hx, lcm_zero_left]
  · rw [hy, lcm_zero_right]

@[simp]
/-
**EuclideanDomain.gcd_mul_lcm** 是 Mathlib 中的一个定理，位于命名空间 `EuclideanDomain`。
形式化陈述：gcd_mul_lcm (x y : R) : gcd x y * lcm x y = x * y
参数：x y : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EuclideanDomain.lcm.eq_1`：∀ {R : Type u} [inst : EuclideanDomain R] [ins
t_1 : DecidableEq R] (x y : R),   EuclideanDomain.lcm x y = x * y / EuclideanDom
ain.gcd x y
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `EuclideanDomain.gcd_eq_zero_iff`：∀ {R : Type u} [inst : EuclideanDomain 
R] [inst_1 : DecidableEq R] {a b : R},   EuclideanDomain.gcd a b = 0 ↔ a = 0 ∧ b
 = 0
· 使用定理 `EuclideanDomain.gcd_dvd`：gcd_dvd (a b : R) : gcd a b ∣ a ∧ gcd a b ∣ b
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `mul_div_cancel_left₀`：∀ {M₀ : Type u_1} [inst : CommMonoidWithZero M₀] [
inst_1 : Div M₀] [MulDivCancelClass M₀] (b : M₀) {a : M₀},   a ≠ 0 → a * b / a =
 b
· 使用定理 `EuclideanDomain.toMulDivCancelClass`：∀ {R : Type u} [inst : EuclideanDom
ain R], MulDivCancelClass R
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem gcd_mul_lcm (x y : R) : gcd x y * lcm x y = x * y := by
  rw [lcm]; by_cases h : gcd x y = 0
  · rw [h, zero_mul]
    rw [EuclideanDomain.gcd_eq_zero_iff] at h
    rw [h.1, zero_mul]
  rcases gcd_dvd x y with ⟨⟨r, hr⟩, ⟨s, hs⟩⟩
  generalize gcd x y = g at h hr ⊢; subst hr
  rw [mul_assoc, mul_div_cancel_left₀ _ h]

end LCM

section Div

/-
**EuclideanDomain.mul_div_mul_cancel** 是 Mathlib 中的一个定理，位于命名空间 `EuclideanDomain`
。
形式化陈述：mul_div_mul_cancel {a b c : R} (ha : a != 0) (hcb : c ∣ b) : a * b / (a * 
c) = b / c
参数：ha : a != 0；hcb : c ∣ b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `EuclideanDomain.div_zero`：div_zero (a : R) : a / 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `EuclideanDomain.eq_div_of_mul_eq_right`：eq_div_of_mul_eq_right {a b c : 
R} (ha : a != 0) (h : a * b = c) : b = c / a
· 使用定理 `mul_left_cancel₀`：mul_left_cancel₀ (ha : a != 0) (h : a * b = a * c) : b
 = c
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `EuclideanDomain.instIsDomain`：∀ (R : Type u_1) [e : EuclideanDomain R], 
IsDomain R
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `EuclideanDomain.mul_div_assoc`：mul_div_assoc (x : R) {y z : R} (h : z ∣ 
y) : x * y / z = x * (y / z)
· 使用定理 `mul_dvd_mul_left`：mul_dvd_mul_left (a : α) (h : b ∣ c) : a * b ∣ a * c
· 使用定理 `mul_div_cancel_left₀`：∀ {M₀ : Type u_1} [inst : CommMonoidWithZero M₀] [
inst_1 : Div M₀] [MulDivCancelClass M₀] (b : M₀) {a : M₀},   a ≠ 0 → a * b / a =
 b
· 使用定理 `EuclideanDomain.toMulDivCancelClass`：∀ {R : Type u} [inst : EuclideanDom
ain R], MulDivCancelClass R
· 使用定理 `mul_ne_zero`：mul_ne_zero (ha : a != 0) (hb : b != 0) : a * b != 0
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
-/
theorem mul_div_mul_cancel {a b c : R} (ha : a ≠ 0) (hcb : c ∣ b) : a * b / (a * c) = b / c := by
  by_cases hc : c = 0; · simp [hc]
  refine eq_div_of_mul_eq_right hc (mul_left_cancel₀ ha ?_)
  rw [← mul_assoc, ← mul_div_assoc _ (by gcongr), mul_div_cancel_left₀ _ (mul_ne_zero ha hc)]
/-
**EuclideanDomain.mul_div_mul_comm_of_dvd_dvd** 是 Mathlib 中的一个定理，位于命名空间 `Euclide
anDomain`。
形式化陈述：mul_div_mul_comm_of_dvd_dvd {a b c d : R} (hac : c ∣ a) (hbd : d ∣ b) : a 
* b / (c * d) = a / c * (b / d)
参数：hac : c ∣ a；hbd : d ∣ b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `EuclideanDomain.div_zero`：div_zero (a : R) : a / 0 = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `mul_div_cancel_left₀`：∀ {M₀ : Type u_1} [inst : CommMonoidWithZero M₀] [
inst_1 : Div M₀] [MulDivCancelClass M₀] (b : M₀) {a : M₀},   a ≠ 0 → a * b / a =
 b
· 使用定理 `EuclideanDomain.toMulDivCancelClass`：∀ {R : Type u} [inst : EuclideanDom
ain R], MulDivCancelClass R
· 使用定理 `mul_mul_mul_comm`：mul_mul_mul_comm (a b c d : G) : a * b * (c * d) = a *
 c * (b * d)
· 使用定理 `mul_ne_zero`：mul_ne_zero (ha : a != 0) (hb : b != 0) : a * b != 0
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `EuclideanDomain.instIsDomain`：∀ (R : Type u_1) [e : EuclideanDomain R], 
IsDomain R
-/
theorem mul_div_mul_comm_of_dvd_dvd {a b c d : R} (hac : c ∣ a) (hbd : d ∣ b) :
    a * b / (c * d) = a / c * (b / d) := by
  rcases eq_or_ne c 0 with (rfl | hc0); · simp
  rcases eq_or_ne d 0 with (rfl | hd0); · simp
  obtain ⟨k1, rfl⟩ := hac
  obtain ⟨k2, rfl⟩ := hbd
  rw [mul_div_cancel_left₀ _ hc0, mul_div_cancel_left₀ _ hd0, mul_mul_mul_comm,
    mul_div_cancel_left₀ _ (mul_ne_zero hc0 hd0)]
/-
**EuclideanDomain.add_mul_div_left** 是 Mathlib 中的一个定理，位于命名空间 `EuclideanDomain`。
形式化陈述：add_mul_div_left (x y z : R) (h1 : y != 0) (h2 : y ∣ x) : (x + y * z) / y 
= x / y + z
参数：x y z : R；h1 : y != 0；h2 : y ∣ x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `EuclideanDomain.eq_div_of_mul_eq_right`：eq_div_of_mul_eq_right {a b c : 
R} (ha : a != 0) (h : a * b = c) : b = c / a
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `EuclideanDomain.mul_div_cancel'`：∀ {R : Type u} [inst : EuclideanDomain 
R] {a b : R}, b ≠ 0 → b ∣ a → b * (a / b) = a
-/
theorem add_mul_div_left (x y z : R) (h1 : y ≠ 0) (h2 : y ∣ x) : (x + y * z) / y = x / y + z := by
  rw [eq_comm]
  apply eq_div_of_mul_eq_right h1
  rw [mul_add, EuclideanDomain.mul_div_cancel' h1 h2]
/-
**EuclideanDomain.add_mul_div_right** 是 Mathlib 中的一个定理，位于命名空间 `EuclideanDomain`。
形式化陈述：add_mul_div_right (x y z : R) (h1 : y != 0) (h2 : y ∣ x) : (x + z * y) / y
 = x / y + z
参数：x y z : R；h1 : y != 0；h2 : y ∣ x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `EuclideanDomain.add_mul_div_left`：add_mul_div_left (x y z : R) (h1 : y !
= 0) (h2 : y ∣ x) : (x + y * z) / y = x / y + z
-/
theorem add_mul_div_right (x y z : R) (h1 : y ≠ 0) (h2 : y ∣ x) : (x + z * y) / y = x / y + z := by
  rw [mul_comm z y]
  exact add_mul_div_left _ _ _ h1 h2
/-
**EuclideanDomain.sub_mul_div_left** 是 Mathlib 中的一个定理，位于命名空间 `EuclideanDomain`。
形式化陈述：sub_mul_div_left (x y z : R) (h1 : y != 0) (h2 : y ∣ x) : (x - y * z) / y 
= x / y - z
参数：x y z : R；h1 : y != 0；h2 : y ∣ x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `EuclideanDomain.eq_div_of_mul_eq_right`：eq_div_of_mul_eq_right {a b c : 
R} (ha : a != 0) (h : a * b = c) : b = c / a
· 使用定理 `mul_sub`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), a 
* (b - c) = a * b - a * c
· 使用定理 `EuclideanDomain.mul_div_cancel'`：∀ {R : Type u} [inst : EuclideanDomain 
R] {a b : R}, b ≠ 0 → b ∣ a → b * (a / b) = a
-/
theorem sub_mul_div_left (x y z : R) (h1 : y ≠ 0) (h2 : y ∣ x) : (x - y * z) / y = x / y - z := by
  rw [eq_comm]
  apply eq_div_of_mul_eq_right h1
  rw [mul_sub, EuclideanDomain.mul_div_cancel' h1 h2]
/-
**EuclideanDomain.sub_mul_div_right** 是 Mathlib 中的一个定理，位于命名空间 `EuclideanDomain`。
形式化陈述：sub_mul_div_right (x y z : R) (h1 : y != 0) (h2 : y ∣ x) : (x - z * y) / y
 = x / y - z
参数：x y z : R；h1 : y != 0；h2 : y ∣ x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `EuclideanDomain.sub_mul_div_left`：sub_mul_div_left (x y z : R) (h1 : y !
= 0) (h2 : y ∣ x) : (x - y * z) / y = x / y - z
-/
theorem sub_mul_div_right (x y z : R) (h1 : y ≠ 0) (h2 : y ∣ x) : (x - z * y) / y = x / y - z := by
  rw [mul_comm z y]
  exact sub_mul_div_left _ _ _ h1 h2
/-
**EuclideanDomain.mul_add_div_left** 是 Mathlib 中的一个定理，位于命名空间 `EuclideanDomain`。
形式化陈述：mul_add_div_left (x y z : R) (h1 : z != 0) (h2 : z ∣ y) : (z * x + y) / z 
= x + y / z
参数：x y z : R；h1 : z != 0；h2 : z ∣ y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `EuclideanDomain.eq_div_of_mul_eq_right`：eq_div_of_mul_eq_right {a b c : 
R} (ha : a != 0) (h : a * b = c) : b = c / a
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `EuclideanDomain.mul_div_cancel'`：∀ {R : Type u} [inst : EuclideanDomain 
R] {a b : R}, b ≠ 0 → b ∣ a → b * (a / b) = a
-/
theorem mul_add_div_left (x y z : R) (h1 : z ≠ 0) (h2 : z ∣ y) : (z * x + y) / z = x + y / z := by
  rw [eq_comm]
  apply eq_div_of_mul_eq_right h1
  rw [mul_add, EuclideanDomain.mul_div_cancel' h1 h2]
/-
**EuclideanDomain.mul_add_div_right** 是 Mathlib 中的一个定理，位于命名空间 `EuclideanDomain`。
形式化陈述：mul_add_div_right (x y z : R) (h1 : z != 0) (h2 : z ∣ y) : (x * z + y) / z
 = x + y / z
参数：x y z : R；h1 : z != 0；h2 : z ∣ y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `EuclideanDomain.mul_add_div_left`：mul_add_div_left (x y z : R) (h1 : z !
= 0) (h2 : z ∣ y) : (z * x + y) / z = x + y / z
-/
theorem mul_add_div_right (x y z : R) (h1 : z ≠ 0) (h2 : z ∣ y) : (x * z + y) / z = x + y / z := by
  rw [mul_comm x z]
  exact mul_add_div_left _ _ _ h1 h2
/-
**EuclideanDomain.mul_sub_div_left** 是 Mathlib 中的一个定理，位于命名空间 `EuclideanDomain`。
形式化陈述：mul_sub_div_left (x y z : R) (h1 : z != 0) (h2 : z ∣ y) : (z * x - y) / z 
= x - y / z
参数：x y z : R；h1 : z != 0；h2 : z ∣ y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `EuclideanDomain.eq_div_of_mul_eq_right`：eq_div_of_mul_eq_right {a b c : 
R} (ha : a != 0) (h : a * b = c) : b = c / a
· 使用定理 `mul_sub`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), a 
* (b - c) = a * b - a * c
· 使用定理 `EuclideanDomain.mul_div_cancel'`：∀ {R : Type u} [inst : EuclideanDomain 
R] {a b : R}, b ≠ 0 → b ∣ a → b * (a / b) = a
-/
theorem mul_sub_div_left (x y z : R) (h1 : z ≠ 0) (h2 : z ∣ y) : (z * x - y) / z = x - y / z := by
  rw [eq_comm]
  apply eq_div_of_mul_eq_right h1
  rw [mul_sub, EuclideanDomain.mul_div_cancel' h1 h2]
/-
**EuclideanDomain.mul_sub_div_right** 是 Mathlib 中的一个定理，位于命名空间 `EuclideanDomain`。
形式化陈述：mul_sub_div_right (x y z : R) (h1 : z != 0) (h2 : z ∣ y) : (x * z - y) / z
 = x - y / z
参数：x y z : R；h1 : z != 0；h2 : z ∣ y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `EuclideanDomain.mul_sub_div_left`：mul_sub_div_left (x y z : R) (h1 : z !
= 0) (h2 : z ∣ y) : (z * x - y) / z = x - y / z
-/
theorem mul_sub_div_right (x y z : R) (h1 : z ≠ 0) (h2 : z ∣ y) : (x * z - y) / z = x - y / z := by
  rw [mul_comm x z]
  exact mul_sub_div_left _ _ _ h1 h2
/-
**EuclideanDomain.div_mul** 是 Mathlib 中的一个定理，位于命名空间 `EuclideanDomain`。
形式化陈述：div_mul {x y z : R} (h1 : y ∣ x) (h2 : y * z ∣ x) : x / (y * z) = x / y / 
z
参数：h1 : y ∣ x；h2 : y * z ∣ x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `EuclideanDomain.div_zero`：div_zero (a : R) : a / 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `EuclideanDomain.eq_div_of_mul_eq_right`：eq_div_of_mul_eq_right {a b c : 
R} (ha : a != 0) (h : a * b = c) : b = c / a
· 使用定理 `EuclideanDomain.mul_div_assoc`：mul_div_assoc (x : R) {y z : R} (h : z ∣ 
y) : x * y / z = x * (y / z)
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `EuclideanDomain.mul_div_mul_cancel`：mul_div_mul_cancel {a b c : R} (ha :
 a != 0) (hcb : c ∣ b) : a * b / (a * c) = b / c
-/
theorem div_mul {x y z : R} (h1 : y ∣ x) (h2 : y * z ∣ x) :
    x / (y * z) = x / y / z := by
  rcases eq_or_ne z 0 with rfl | hz
  · simp only [mul_zero, div_zero]
  apply eq_div_of_mul_eq_right hz
  rw [← EuclideanDomain.mul_div_assoc z h2, mul_comm y z, mul_div_mul_cancel hz h1]
/-
**EuclideanDomain.div_div** 是 Mathlib 中的一个定理，位于命名空间 `EuclideanDomain`。
形式化陈述：div_div {x y z : R} (h1 : y ∣ x) (h2 : z ∣ (x / y)) : x / y / z = x / (y *
 z)
参数：h1 : y ∣ x；h2 : z ∣ (x / y)。
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
· 使用定理 `EuclideanDomain.div_zero`：div_zero (a : R) : a / 0 = 0
· 使用定理 `EuclideanDomain.zero_div`：zero_div {a : R} : 0 / a = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `EuclideanDomain.div_mul`：div_mul {x y z : R} (h1 : y ∣ x) (h2 : y * z ∣ 
x) : x / (y * z) = x / y / z
· 使用定理 `EuclideanDomain.mul_div_cancel'`：∀ {R : Type u} [inst : EuclideanDomain 
R] {a b : R}, b ≠ 0 → b ∣ a → b * (a / b) = a
· 使用定理 `mul_dvd_mul_iff_left`：mul_dvd_mul_iff_left [MonoidWithZero α] [IsLeftCan
celMulZero α] {a b c : α} (ha : a != 0) : a * b ∣ a * c ↔ b ∣ c
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `EuclideanDomain.instIsDomain`：∀ (R : Type u_1) [e : EuclideanDomain R], 
IsDomain R
-/
theorem div_div {x y z : R} (h1 : y ∣ x) (h2 : z ∣ (x / y)) :
    x / y / z = x / (y * z) := by
  rcases eq_or_ne y 0 with rfl | hy
  · simp only [div_zero, zero_div, zero_mul]
  rw [← mul_dvd_mul_iff_left hy, EuclideanDomain.mul_div_cancel' hy h1] at h2
  exact (div_mul h1 h2).symm
/-
**EuclideanDomain.div_add_div_of_dvd** 是 Mathlib 中的一个定理，位于命名空间 `EuclideanDomain`
。
形式化陈述：div_add_div_of_dvd {x y z t : R} (h1 : y != 0) (h2 : t != 0) (h3 : y ∣ x) 
(h4 : t ∣ z) : x / y + z / t = (t * x + y * z) / (t * y)
参数：h1 : y != 0；h2 : t != 0；h3 : y ∣ x；h4 : t ∣ z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EuclideanDomain.eq_div_of_mul_eq_right`：eq_div_of_mul_eq_right {a b c : 
R} (ha : a != 0) (h : a * b = c) : b = c / a
· 使用定理 `mul_ne_zero`：mul_ne_zero (ha : a != 0) (hb : b != 0) : a * b != 0
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `EuclideanDomain.instIsDomain`：∀ (R : Type u_1) [e : EuclideanDomain R], 
IsDomain R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `EuclideanDomain.mul_div_cancel'`：∀ {R : Type u} [inst : EuclideanDomain 
R] {a b : R}, b ≠ 0 → b ∣ a → b * (a / b) = a
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
-/
theorem div_add_div_of_dvd {x y z t : R} (h1 : y ≠ 0) (h2 : t ≠ 0) (h3 : y ∣ x) (h4 : t ∣ z) :
    x / y + z / t = (t * x + y * z) / (t * y) := by
  apply eq_div_of_mul_eq_right (mul_ne_zero h2 h1)
  rw [mul_add, mul_assoc, EuclideanDomain.mul_div_cancel' h1 h3, mul_comm t y,
    mul_assoc, EuclideanDomain.mul_div_cancel' h2 h4]
/-
**EuclideanDomain.div_sub_div_of_dvd** 是 Mathlib 中的一个定理，位于命名空间 `EuclideanDomain`
。
形式化陈述：div_sub_div_of_dvd {x y z t : R} (h1 : y != 0) (h2 : t != 0) (h3 : y ∣ x) 
(h4 : t ∣ z) : x / y - z / t = (t * x - y * z) / (t * y)
参数：h1 : y != 0；h2 : t != 0；h3 : y ∣ x；h4 : t ∣ z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EuclideanDomain.eq_div_of_mul_eq_right`：eq_div_of_mul_eq_right {a b c : 
R} (ha : a != 0) (h : a * b = c) : b = c / a
· 使用定理 `mul_ne_zero`：mul_ne_zero (ha : a != 0) (hb : b != 0) : a * b != 0
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `EuclideanDomain.instIsDomain`：∀ (R : Type u_1) [e : EuclideanDomain R], 
IsDomain R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_sub`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), a 
* (b - c) = a * b - a * c
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `EuclideanDomain.mul_div_cancel'`：∀ {R : Type u} [inst : EuclideanDomain 
R] {a b : R}, b ≠ 0 → b ∣ a → b * (a / b) = a
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
-/
theorem div_sub_div_of_dvd {x y z t : R} (h1 : y ≠ 0) (h2 : t ≠ 0) (h3 : y ∣ x) (h4 : t ∣ z) :
    x / y - z / t = (t * x - y * z) / (t * y) := by
  apply eq_div_of_mul_eq_right (mul_ne_zero h2 h1)
  rw [mul_sub, mul_assoc, EuclideanDomain.mul_div_cancel' h1 h3, mul_comm t y,
    mul_assoc, EuclideanDomain.mul_div_cancel' h2 h4]
/-
**EuclideanDomain.div_eq_iff_eq_mul_of_dvd** 是 Mathlib 中的一个定理，位于命名空间 `EuclideanD
omain`。
形式化陈述：div_eq_iff_eq_mul_of_dvd (x y z : R) (h1 : y != 0) (h2 : y ∣ x) : x / y = 
z ↔ x = y * z
参数：x y z : R；h1 : y != 0；h2 : y ∣ x。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_div_cancel_left₀`：∀ {M₀ : Type u_1} [inst : CommMonoidWithZero M₀] [
inst_1 : Div M₀] [MulDivCancelClass M₀] (b : M₀) {a : M₀},   a ≠ 0 → a * b / a =
 b
· 使用定理 `EuclideanDomain.toMulDivCancelClass`：∀ {R : Type u} [inst : EuclideanDom
ain R], MulDivCancelClass R
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `EuclideanDomain.instIsDomain`：∀ (R : Type u_1) [e : EuclideanDomain R], 
IsDomain R
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem div_eq_iff_eq_mul_of_dvd (x y z : R) (h1 : y ≠ 0) (h2 : y ∣ x) :
    x / y = z ↔ x = y * z := by
  obtain ⟨a, ha⟩ := h2
  rw [ha, mul_div_cancel_left₀ _ h1]
  simp only [mul_eq_mul_left_iff, h1, or_false]
/-
**EuclideanDomain.eq_div_iff_mul_eq_of_dvd** 是 Mathlib 中的一个定理，位于命名空间 `EuclideanD
omain`。
形式化陈述：eq_div_iff_mul_eq_of_dvd (x y z : R) (h1 : z != 0) (h2 : z ∣ y) : x = y / 
z ↔ z * x = y
参数：x y z : R；h1 : z != 0；h2 : z ∣ y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `EuclideanDomain.div_eq_iff_eq_mul_of_dvd`：div_eq_iff_eq_mul_of_dvd (x y 
z : R) (h1 : y != 0) (h2 : y ∣ x) : x / y = z ↔ x = y * z
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem eq_div_iff_mul_eq_of_dvd (x y z : R) (h1 : z ≠ 0) (h2 : z ∣ y) :
    x = y / z ↔ z * x = y := by
  rw [eq_comm, div_eq_iff_eq_mul_of_dvd _ _ _ h1 h2, eq_comm]
/-
**EuclideanDomain.div_eq_div_iff_mul_eq_mul_of_dvd** 是 Mathlib 中的一个定理，位于命名空间 `Eu
clideanDomain`。
形式化陈述：div_eq_div_iff_mul_eq_mul_of_dvd {x y z t : R} (h1 : y != 0) (h2 : t != 0)
 (h3 : y ∣ x) (h4 : t ∣ z) : x / y = z / t ↔ t * x = y * z
参数：h1 : y != 0；h2 : t != 0；h3 : y ∣ x；h4 : t ∣ z。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EuclideanDomain.div_eq_iff_eq_mul_of_dvd`：div_eq_iff_eq_mul_of_dvd (x y 
z : R) (h1 : y != 0) (h2 : y ∣ x) : x / y = z ↔ x = y * z
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `EuclideanDomain.mul_div_assoc`：mul_div_assoc (x : R) {y z : R} (h : z ∣ 
y) : x * y / z = x * (y / z)
· 使用定理 `EuclideanDomain.eq_div_iff_mul_eq_of_dvd`：eq_div_iff_mul_eq_of_dvd (x y 
z : R) (h1 : z != 0) (h2 : z ∣ y) : x = y / z ↔ z * x = y
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem div_eq_div_iff_mul_eq_mul_of_dvd {x y z t : R} (h1 : y ≠ 0) (h2 : t ≠ 0)
    (h3 : y ∣ x) (h4 : t ∣ z) : x / y = z / t ↔ t * x = y * z := by
  rw [div_eq_iff_eq_mul_of_dvd _ _ _ h1 h3, ← mul_div_assoc _ h4,
    eq_div_iff_mul_eq_of_dvd _ _ _ h2]
  obtain ⟨a, ha⟩ := h4
  use y * a
  rw [ha, mul_comm, mul_assoc, mul_comm y a]

end Div

end EuclideanDomain

section RingEquiv

variable {R S : Type*} [EuclideanDomain R] [CommRing S]

/-- If `S` is a nontrivial commutative ring isomorphic to a Euclidean domain
`R` then it is also a Euclidean domain. -/
/-
**RingEquiv.euclideanDomain** 是 Mathlib 中的一个定义，位于命名空间 `RingEquiv`。
形式化陈述：{R : Type u_1} → {S : Type u_2} → [inst : EuclideanDomain R] → [inst_1 : C
ommRing S] → S ≃+* R → EuclideanDomain S
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `S` is a nontrivial commutative ring isomorphic to a Euclidean domain
`R` then it is also a Euclidean domain.
-/
protected abbrev RingEquiv.euclideanDomain (e : S ≃+* R) : EuclideanDomain S where
  toNontrivial := e.nontrivial
  quotient a b := e.symm (e a / e b)
  remainder a b := e.symm (e a % e b)
  r a b := EuclideanDomain.r (e a) (e b)
  r_wellFounded := InvImage.wf e EuclideanDomain.r_wellFounded
  quotient_zero a := by simp
  quotient_mul_add_remainder_eq a b := by
    apply e.injective
    simpa using! EuclideanDomain.quotient_mul_add_remainder_eq (e a) (e b)
  remainder_lt a b hb := by
    have hb' : e b ≠ 0 := by simpa using hb
    simpa using! EuclideanDomain.remainder_lt (e a) hb'
  mul_left_not_lt a b hb := by
    have hb' : e b ≠ 0 := by simpa using hb
    simpa using! EuclideanDomain.mul_left_not_lt (e a) hb'

end RingEquiv

