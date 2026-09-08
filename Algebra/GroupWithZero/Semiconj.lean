/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
module

public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Group.Semiconj.Units

/-!
# Lemmas about semiconjugate elements in a `GroupWithZero`.

-/

public section

assert_not_exists DenselyOrdered Ring

variable {G₀ : Type*}

namespace SemiconjBy

@[simp]
/-
**SemiconjBy.zero_right** 是 Mathlib 中的一个定理，位于命名空间 `SemiconjBy`。
形式化陈述：zero_right [MulZeroClass G₀] (a : G₀) : SemiconjBy a 0 0
参数：a : G₀。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem zero_right [MulZeroClass G₀] (a : G₀) : SemiconjBy a 0 0 := by
  simp only [SemiconjBy, mul_zero, zero_mul]

@[simp]
/-
**SemiconjBy.zero_left** 是 Mathlib 中的一个定理，位于命名空间 `SemiconjBy`。
形式化陈述：zero_left [MulZeroClass G₀] (x y : G₀) : SemiconjBy 0 x y
参数：x y : G₀。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem zero_left [MulZeroClass G₀] (x y : G₀) : SemiconjBy 0 x y := by
  simp only [SemiconjBy, mul_zero, zero_mul]

variable [GroupWithZero G₀] {a x y x' y' : G₀}

@[simp]
/-
**SemiconjBy.inv_symm_left_iff** 是 Mathlib 中的一个定理，位于命名空间 `SemiconjBy`。
形式化陈述：∀ {G : Type u_1} [inst : Group G] {a x y : G}, SemiconjBy a⁻¹ y x ↔ Semico
njBy a x y
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem inv_symm_left_iff₀ : SemiconjBy a⁻¹ x y ↔ SemiconjBy a y x :=
  Classical.by_cases (fun ha : a = 0 => by simp only [ha, inv_zero, SemiconjBy.zero_left]) fun ha =>
    @units_inv_symm_left_iff _ _ (Units.mk0 a ha) _ _
/-
**SemiconjBy.inv_symm_left** 是 Mathlib 中的一个定理，位于命名空间 `SemiconjBy`。
形式化陈述：∀ {G : Type u_1} [inst : Group G] {a x y : G}, SemiconjBy a x y → Semiconj
By a⁻¹ y x
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `SemiconjBy.inv_symm_left_iff`：∀ {G : Type u_1} [inst : Group G] {a x y :
 G}, SemiconjBy a⁻¹ y x ↔ SemiconjBy a x y
-/
theorem inv_symm_left₀ (h : SemiconjBy a x y) : SemiconjBy a⁻¹ y x :=
  SemiconjBy.inv_symm_left_iff₀.2 h
/-
**SemiconjBy.inv_right** 是 Mathlib 中的一个定理，位于命名空间 `SemiconjBy`。
形式化陈述：∀ {G : Type u_1} [inst : Group G] {a x y : G}, SemiconjBy a x y → Semiconj
By a x⁻¹ y⁻¹
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `SemiconjBy.inv_right_iff`：∀ {G : Type u_1} [inst : Group G] {a x y : G},
 SemiconjBy a x⁻¹ y⁻¹ ↔ SemiconjBy a x y
-/
theorem inv_right₀ (h : SemiconjBy a x y) : SemiconjBy a x⁻¹ y⁻¹ := by
  by_cases ha : a = 0
  · simp only [ha, zero_left]
  by_cases hx : x = 0
  · subst x
    simp only [SemiconjBy, mul_zero, @eq_comm _ _ (y * a), mul_eq_zero] at h
    simp [h.resolve_right ha]
  · have := mul_ne_zero ha hx
    rw [h.eq, mul_ne_zero_iff] at this
    exact @units_inv_right _ _ _ (Units.mk0 x hx) (Units.mk0 y this.1) h

@[simp]
/-
**SemiconjBy.inv_right_iff** 是 Mathlib 中的一个定理，位于命名空间 `SemiconjBy`。
形式化陈述：∀ {G : Type u_1} [inst : Group G] {a x y : G}, SemiconjBy a x⁻¹ y⁻¹ ↔ Semi
conjBy a x y
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SemiconjBy.inv_symm_left_iff`：∀ {G : Type u_1} [inst : Group G] {a x y :
 G}, SemiconjBy a⁻¹ y x ↔ SemiconjBy a x y
· 使用定理 `SemiconjBy.inv_inv_symm_iff`：inv_inv_symm_iff : SemiconjBy a⁻¹ x⁻¹ y⁻¹ ↔
 SemiconjBy a y x
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem inv_right_iff₀ : SemiconjBy a x⁻¹ y⁻¹ ↔ SemiconjBy a x y :=
  ⟨fun h => inv_inv x ▸ inv_inv y ▸ h.inv_right₀, inv_right₀⟩
/-
**SemiconjBy.div_right** 是 Mathlib 中的一个定理，位于命名空间 `SemiconjBy`。
形式化陈述：div_right (h : SemiconjBy a x y) (h' : SemiconjBy a x' y') : SemiconjBy a 
(x / x') (y / y')
参数：h : SemiconjBy a x y；h' : SemiconjBy a x' y'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `SemiconjBy.mul_right`：mul_right (h : SemiconjBy a x y) (h' : SemiconjBy 
a x' y') : SemiconjBy a (x * x') (y * y')
· 使用定理 `SemiconjBy.inv_right₀`：inv_right₀ (h : SemiconjBy a x y) : SemiconjBy a 
x⁻¹ y⁻¹
-/
theorem div_right (h : SemiconjBy a x y) (h' : SemiconjBy a x' y') :
    SemiconjBy a (x / x') (y / y') := by
  rw [div_eq_mul_inv, div_eq_mul_inv]
  exact h.mul_right h'.inv_right₀
/-
**SemiconjBy.zpow_right** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：SemiconjBy.zpow_right {A X Y : M} (hx : IsUnit X.det) (hy : IsUnit Y.det) 
(h : SemiconjBy A X Y) : forall m : Int, SemiconjBy A (X ^ m) (Y ^ m) | (n : Nat
) => by simp [h.pow_right n] | -[n+1] => by have hx' : IsUnit (X ^ n.succ).det
参数：hx : IsUnit X.det；hy : IsUnit Y.det；h : SemiconjBy A X Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zpow_natCast`：zpow_natCast (a : G) : forall n : Nat, a ^ (n : Int) = a ^
 n | 0 => (zpow_zero _).trans (pow_zero _).symm | n + 1 => calc a ^ (↑(n + 1) : 
In…
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `SemiconjBy.pow_right`：pow_right {a x y : M} (h : SemiconjBy a x y) (n : 
Nat) : SemiconjBy a (x ^ n) (y ^ n)
· 使用定理 `zpow_negSucc`：zpow_negSucc (a : G) (n : Nat) : a ^ (Int.negSucc n) = (a 
^ (n + 1))⁻¹
-/
lemma zpow_right₀ {a x y : G₀} (h : SemiconjBy a x y) : ∀ m : ℤ, SemiconjBy a (x ^ m) (y ^ m)
  | (n : ℕ) => by simp [h.pow_right n]
  | .negSucc n => by simp only [zpow_negSucc, (h.pow_right (n + 1)).inv_right₀]

end SemiconjBy

namespace Commute
variable [GroupWithZero G₀] {a b : G₀}

/-
**Commute.zpow_right** 是 Mathlib 中的一个引理，位于命名空间 `Commute`。
形式化陈述：zpow_right (h : Commute a b) (m : Int) : Commute a (b ^ m)
参数：h : Commute a b；m : Int。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SemiconjBy.zpow_right`：SemiconjBy.zpow_right {A X Y : M} (hx : IsUnit X.
det) (hy : IsUnit Y.det) (h : SemiconjBy A X Y) : forall m : Int, SemiconjBy A (
X ^ m) (Y ^…
-/
lemma zpow_right₀ (h : Commute a b) : ∀ m : ℤ, Commute a (b ^ m) := SemiconjBy.zpow_right₀ h
/-
**Commute.zpow_left** 是 Mathlib 中的一个引理，位于命名空间 `Commute`。
形式化陈述：zpow_left (h : Commute a b) (m : Int) : Commute (a ^ m) b
参数：h : Commute a b；m : Int。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Commute.symm`：∀ {S : Type u_3} [inst : Mul S] {a b : S}, Commute a b → C
ommute b a
· 使用引理 `Commute.zpow_right`：zpow_right (h : Commute a b) (m : Int) : Commute a (
b ^ m)
-/
lemma zpow_left₀ (h : Commute a b) (m : ℤ) : Commute (a ^ m) b := (h.symm.zpow_right₀ m).symm
/-
**Commute.zpow_zpow** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：Commute.zpow_zpow {A B : M} (h : Commute A B) (m n : Int) : Commute (A ^ m
) (B ^ n)
参数：h : Commute A B；m n : Int。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Commute.zpow_right`：zpow_right (h : Commute a b) (m : Int) : Commute a (
b ^ m)
· 使用引理 `Commute.zpow_left`：zpow_left (h : Commute a b) (m : Int) : Commute (a ^ 
m) b
-/
lemma zpow_zpow₀ (h : Commute a b) (m n : ℤ) : Commute (a ^ m) (b ^ n) :=
  (h.zpow_left₀ m).zpow_right₀ n
/-
**Commute.zpow_self** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：Commute.zpow_self (A : M) (n : Int) : Commute (A ^ n) A
参数：A : M；n : Int。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Commute.zpow_left`：zpow_left (h : Commute a b) (m : Int) : Commute (a ^ 
m) b
· 使用定理 `Commute.refl`：∀ {S : Type u_3} [inst : Mul S] (a : S), Commute a a
-/
lemma zpow_self₀ (a : G₀) (n : ℤ) : Commute (a ^ n) a := (Commute.refl a).zpow_left₀ n
/-
**Commute.self_zpow** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：Commute.self_zpow (A : M) (n : Int) : Commute A (A ^ n)
参数：A : M；n : Int。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Commute.zpow_right`：zpow_right (h : Commute a b) (m : Int) : Commute a (
b ^ m)
· 使用定理 `Commute.refl`：∀ {S : Type u_3} [inst : Mul S] (a : S), Commute a a
-/
lemma self_zpow₀ (a : G₀) (n : ℤ) : Commute a (a ^ n) := (Commute.refl a).zpow_right₀ n
/-
**Commute.zpow_zpow_self** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：Commute.zpow_zpow_self (A : M) (m n : Int) : Commute (A ^ m) (A ^ n)
参数：A : M；m n : Int。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Commute.zpow_zpow`：Commute.zpow_zpow {A B : M} (h : Commute A B) (m n : 
Int) : Commute (A ^ m) (B ^ n)
· 使用定理 `Commute.refl`：∀ {S : Type u_3} [inst : Mul S] (a : S), Commute a a
-/
lemma zpow_zpow_self₀ (a : G₀) (m n : ℤ) : Commute (a ^ m) (a ^ n) :=
  (Commute.refl a).zpow_zpow₀ m n

end Commute

