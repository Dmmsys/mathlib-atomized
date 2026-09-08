/-
Copyright (c) 2019 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Algebra.Group.Semiconj.Defs
public import Mathlib.Algebra.Group.Basic

/-!
# Lemmas about semiconjugate elements of a group

-/

public section

assert_not_exists MonoidWithZero DenselyOrdered

namespace SemiconjBy
variable {G : Type*}

section DivisionMonoid
variable [DivisionMonoid G] {a x y : G}

@[to_additive (attr := simp)]
/-
**SemiconjBy.inv_inv_symm_iff** 是 Mathlib 中的一个定理，位于命名空间 `SemiconjBy`。
形式化陈述：inv_inv_symm_iff : SemiconjBy a⁻¹ x⁻¹ y⁻¹ ↔ SemiconjBy a y x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem inv_inv_symm_iff : SemiconjBy a⁻¹ x⁻¹ y⁻¹ ↔ SemiconjBy a y x := by
  simp_rw [SemiconjBy, ← mul_inv_rev, inv_inj, eq_comm]

@[to_additive] alias ⟨_, inv_inv_symm⟩ := inv_inv_symm_iff

end DivisionMonoid

section Group
variable [Group G] {a x y : G}

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
@[to_additive (attr := simp)] lemma inv_symm_left_iff : SemiconjBy a⁻¹ y x ↔ SemiconjBy a x y := by
  simp_rw [SemiconjBy, eq_mul_inv_iff_mul_eq, mul_assoc, inv_mul_eq_iff_eq_mul, eq_comm]

@[to_additive] alias ⟨_, inv_symm_left⟩ := inv_symm_left_iff
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
@[to_additive (attr := simp)] lemma inv_right_iff : SemiconjBy a x⁻¹ y⁻¹ ↔ SemiconjBy a x y := by
  rw [← inv_symm_left_iff, inv_inv_symm_iff]

@[to_additive] alias ⟨_, inv_right⟩ := inv_right_iff
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
@[to_additive (attr := simp)] lemma zpow_right (h : SemiconjBy a x y) :
    ∀ m : ℤ, SemiconjBy a (x ^ m) (y ^ m)
  | (n : ℕ) => by simp [zpow_natCast, h.pow_right n]
  | .negSucc n => by
    simp only [zpow_negSucc, inv_right_iff]
    apply pow_right h

variable (a) in
/-
**SemiconjBy.eq_one_iff** 是 Mathlib 中的一个定理，位于命名空间 `SemiconjBy`。
形式化陈述：∀ {G : Type u_1} [inst : Group G] (a : G) {x y : G}, SemiconjBy a x y → (x
 = 1 ↔ y = 1)
参数：a : G；x = 1 ↔ y = 1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `conj_eq_one_iff`：conj_eq_one_iff : a * b * a⁻¹ = 1 ↔ b = 1
· 使用定理 `SemiconjBy.eq`：∀ {S : Type u_1} [inst : Mul S] {a x y : S}, SemiconjBy a
 x y → a * x = y * a
· 使用定理 `mul_inv_cancel_right`：mul_inv_cancel_right (a b : G) : a * b * b⁻¹ = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[to_additive] lemma eq_one_iff (h : SemiconjBy a x y) : x = 1 ↔ y = 1 := by
  rw [← conj_eq_one_iff (a := a) (b := x), h.eq, mul_inv_cancel_right]

end Group
end SemiconjBy

