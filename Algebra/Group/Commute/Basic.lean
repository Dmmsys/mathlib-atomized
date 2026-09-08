/-
Copyright (c) 2019 Neil Strickland. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Neil Strickland, Yury Kudryashov
-/
module

public import Mathlib.Algebra.Group.Commute.Defs
public import Mathlib.Algebra.Group.Semiconj.Basic

/-!
# Additional lemmas about commuting pairs of elements in monoids

-/

public section

assert_not_exists MonoidWithZero DenselyOrdered

variable {G : Type*}

section Semigroup
variable [Semigroup G] {a b c : G}

open Function

@[to_additive]
/-
**SemiconjBy.function_semiconj_mul_left** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：SemiconjBy.function_semiconj_mul_left (h : SemiconjBy a b c) : Semiconj (a
 * ·) (b * ·) (c * ·)
参数：h : SemiconjBy a b c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `SemiconjBy.eq`：∀ {S : Type u_1} [inst : Mul S] {a x y : S}, SemiconjBy a
 x y → a * x = y * a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma SemiconjBy.function_semiconj_mul_left (h : SemiconjBy a b c) :
    Semiconj (a * ·) (b * ·) (c * ·) := fun j ↦ by simp only [← mul_assoc, h.eq]

@[to_additive]
/-
**Commute.function_commute_mul_left** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Commute.function_commute_mul_left (h : Commute a b) : Function.Commute (a 
* ·) (b * ·)
参数：h : Commute a b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SemiconjBy.function_semiconj_mul_left`：SemiconjBy.function_semiconj_mul_
left (h : SemiconjBy a b c) : Semiconj (a * ·) (b * ·) (c * ·)
-/
lemma Commute.function_commute_mul_left (h : Commute a b) : Function.Commute (a * ·) (b * ·) :=
  SemiconjBy.function_semiconj_mul_left h

@[to_additive]
/-
**SemiconjBy.function_semiconj_mul_right_swap** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：SemiconjBy.function_semiconj_mul_right_swap (h : SemiconjBy a b c) : Funct
ion.Semiconj (· * a) (· * c) (· * b)
参数：h : SemiconjBy a b c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SemiconjBy.eq`：∀ {S : Type u_1} [inst : Mul S] {a x y : S}, SemiconjBy a
 x y → a * x = y * a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma SemiconjBy.function_semiconj_mul_right_swap (h : SemiconjBy a b c) :
    Function.Semiconj (· * a) (· * c) (· * b) := fun j ↦ by simp only [mul_assoc, ← h.eq]

@[to_additive]
/-
**Commute.function_commute_mul_right** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Commute.function_commute_mul_right (h : Commute a b) : Function.Commute (·
 * a) (· * b)
参数：h : Commute a b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SemiconjBy.function_semiconj_mul_right_swap`：SemiconjBy.function_semicon
j_mul_right_swap (h : SemiconjBy a b c) : Function.Semiconj (· * a) (· * c) (· *
 b)
-/
lemma Commute.function_commute_mul_right (h : Commute a b) : Function.Commute (· * a) (· * b) :=
  SemiconjBy.function_semiconj_mul_right_swap h

end Semigroup

namespace Commute

section DivisionMonoid

variable [DivisionMonoid G] {a b c d : G}

@[to_additive]
/-
**Commute.inv_inv** 是 Mathlib 中的一个定理，位于命名空间 `Commute`。
形式化陈述：∀ {G : Type u_1} [inst : DivisionMonoid G] {a b : G}, Commute a b → Commut
e a⁻¹ b⁻¹
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SemiconjBy.inv_inv_symm`：∀ {G : Type u_1} [inst : DivisionMonoid G] {a x
 y : G}, SemiconjBy a y x → SemiconjBy a⁻¹ x⁻¹ y⁻¹
-/
protected theorem inv_inv : Commute a b → Commute a⁻¹ b⁻¹ :=
  SemiconjBy.inv_inv_symm

@[to_additive (attr := simp)]
/-
**Commute.inv_inv_iff** 是 Mathlib 中的一个定理，位于命名空间 `Commute`。
形式化陈述：inv_inv_iff : Commute a⁻¹ b⁻¹ ↔ Commute a b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SemiconjBy.inv_inv_symm_iff`：inv_inv_symm_iff : SemiconjBy a⁻¹ x⁻¹ y⁻¹ ↔
 SemiconjBy a y x
-/
theorem inv_inv_iff : Commute a⁻¹ b⁻¹ ↔ Commute a b :=
  SemiconjBy.inv_inv_symm_iff

@[to_additive]
/-
**Commute.div_mul_div_comm** 是 Mathlib 中的一个定理，位于命名空间 `Commute`。
形式化陈述：∀ {G : Type u_1} [inst : DivisionMonoid G] {a b c d : G},   Commute b d → 
Commute b⁻¹ c → a / b * (c / d) = a * c / (b * d)
参数：c / d；b * d。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `mul_inv_rev`：mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹
· 使用定理 `Commute.eq`：∀ {S : Type u_3} [inst : Mul S] {a b : S}, Commute a b → a *
 b = b * a
· 使用定理 `Commute.symm`：∀ {S : Type u_3} [inst : Mul S] {a b : S}, Commute a b → C
ommute b a
· 使用定理 `Commute.inv_inv`：∀ {G : Type u_1} [inst : DivisionMonoid G] {a b : G}, C
ommute a b → Commute a⁻¹ b⁻¹
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Commute.mul_mul_mul_comm`：∀ {S : Type u_3} [inst : Semigroup S] {b c : S
}, Commute b c → ∀ (a d : S), a * b * (c * d) = a * c * (b * d)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
protected theorem div_mul_div_comm (hbd : Commute b d) (hbc : Commute b⁻¹ c) :
    a / b * (c / d) = a * c / (b * d) := by
  simp_rw [div_eq_mul_inv, mul_inv_rev, hbd.inv_inv.symm.eq, hbc.mul_mul_mul_comm]

@[to_additive]
/-
**Commute.mul_div_mul_comm** 是 Mathlib 中的一个定理，位于命名空间 `Commute`。
形式化陈述：∀ {G : Type u_1} [inst : DivisionMonoid G] {a b c d : G},   Commute c d → 
Commute b c⁻¹ → a * b / (c * d) = a / c * (b / d)
参数：c * d；b / d。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Commute.div_mul_div_comm`：∀ {G : Type u_1} [inst : DivisionMonoid G] {a 
b c d : G},   Commute b d → Commute b⁻¹ c → a / b * (c / d) = a * c / (b * d)
· 使用定理 `Commute.symm`：∀ {S : Type u_3} [inst : Mul S] {a b : S}, Commute a b → C
ommute b a
-/
protected theorem mul_div_mul_comm (hcd : Commute c d) (hbc : Commute b c⁻¹) :
    a * b / (c * d) = a / c * (b / d) :=
  (hcd.div_mul_div_comm hbc.symm).symm

@[to_additive]
/-
**Commute.div_div_div_comm** 是 Mathlib 中的一个定理，位于命名空间 `Commute`。
形式化陈述：∀ {G : Type u_1} [inst : DivisionMonoid G] {a b c d : G},   Commute b c → 
Commute b⁻¹ d → Commute c⁻¹ d → a / b / (c / d) = a / c / (b / d)
参数：c / d；b / d。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `mul_inv_rev`：mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `Commute.eq`：∀ {S : Type u_3} [inst : Mul S] {a b : S}, Commute a b → a *
 b = b * a
· 使用定理 `Commute.symm`：∀ {S : Type u_3} [inst : Mul S] {a b : S}, Commute a b → C
ommute b a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Commute.mul_mul_mul_comm`：∀ {S : Type u_3} [inst : Semigroup S] {b c : S
}, Commute b c → ∀ (a d : S), a * b * (c * d) = a * c * (b * d)
· 使用定理 `Commute.inv_inv`：∀ {G : Type u_1} [inst : DivisionMonoid G] {a b : G}, C
ommute a b → Commute a⁻¹ b⁻¹
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
protected theorem div_div_div_comm (hbc : Commute b c) (hbd : Commute b⁻¹ d) (hcd : Commute c⁻¹ d) :
    a / b / (c / d) = a / c / (b / d) := by
  simp_rw [div_eq_mul_inv, mul_inv_rev, inv_inv, hbd.symm.eq, hcd.symm.eq,
    hbc.inv_inv.mul_mul_mul_comm]

end DivisionMonoid

section Group
variable [Group G] {a b : G}

@[to_additive (attr := simp)]
/-
**Commute.inv_left_iff** 是 Mathlib 中的一个引理，位于命名空间 `Commute`。
形式化陈述：inv_left_iff : Commute a⁻¹ b ↔ Commute a b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SemiconjBy.inv_symm_left_iff`：∀ {G : Type u_1} [inst : Group G] {a x y :
 G}, SemiconjBy a⁻¹ y x ↔ SemiconjBy a x y
-/
lemma inv_left_iff : Commute a⁻¹ b ↔ Commute a b := SemiconjBy.inv_symm_left_iff

@[to_additive] alias ⟨_, inv_left⟩ := inv_left_iff

@[to_additive (attr := simp)]
/-
**Commute.inv_right_iff** 是 Mathlib 中的一个引理，位于命名空间 `Commute`。
形式化陈述：inv_right_iff : Commute a b⁻¹ ↔ Commute a b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SemiconjBy.inv_right_iff`：∀ {G : Type u_1} [inst : Group G] {a x y : G},
 SemiconjBy a x⁻¹ y⁻¹ ↔ SemiconjBy a x y
-/
lemma inv_right_iff : Commute a b⁻¹ ↔ Commute a b := SemiconjBy.inv_right_iff

@[to_additive] alias ⟨_, inv_right⟩ := inv_right_iff

@[to_additive]
/-
**Commute.inv_mul_cancel** 是 Mathlib 中的一个定理，位于命名空间 `Commute`。
形式化陈述：∀ {G : Type u_1} [inst : Group G] {a b : G}, Commute a b → a⁻¹ * b * a = b
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Commute.eq`：∀ {S : Type u_3} [inst : Mul S] {a b : S}, Commute a b → a *
 b = b * a
· 使用定理 `Commute.inv_left`：∀ {G : Type u_1} [inst : Group G] {a b : G}, Commute a
 b → Commute a⁻¹ b
· 使用定理 `inv_mul_cancel_right`：inv_mul_cancel_right (a b : G) : a * b⁻¹ * b = a
-/
protected lemma inv_mul_cancel (h : Commute a b) : a⁻¹ * b * a = b := by
  rw [h.inv_left.eq, inv_mul_cancel_right]

@[to_additive]
/-
**Commute.inv_mul_cancel_assoc** 是 Mathlib 中的一个引理，位于命名空间 `Commute`。
形式化陈述：inv_mul_cancel_assoc (h : Commute a b) : a⁻¹ * (b * a) = b
参数：h : Commute a b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Commute.inv_mul_cancel`：∀ {G : Type u_1} [inst : Group G] {a b : G}, Com
mute a b → a⁻¹ * b * a = b
-/
lemma inv_mul_cancel_assoc (h : Commute a b) : a⁻¹ * (b * a) = b := by
  rw [← mul_assoc, h.inv_mul_cancel]

@[to_additive (attr := simp)]
/-
**Commute.conj_iff** 是 Mathlib 中的一个定理，位于命名空间 `Commute`。
形式化陈述：∀ {G : Type u_1} [inst : Group G] {a b : G} (h : G), Commute (h * a * h⁻¹)
 (h * b * h⁻¹) ↔ Commute a b
参数：h : G；h * a * h⁻¹；h * b * h⁻¹。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SemiconjBy.conj_iff`：conj_iff {a x y b : G} : SemiconjBy (b * a * b⁻¹) (
b * x * b⁻¹) (b * y * b⁻¹) ↔ SemiconjBy a x y
-/
protected theorem conj_iff (h : G) : Commute (h * a * h⁻¹) (h * b * h⁻¹) ↔ Commute a b :=
  SemiconjBy.conj_iff

@[to_additive]
/-
**Commute.conj** 是 Mathlib 中的一个定理，位于命名空间 `Commute`。
形式化陈述：∀ {G : Type u_1} [inst : Group G] {a b : G}, Commute a b → ∀ (h : G), Comm
ute (h * a * h⁻¹) (h * b * h⁻¹)
参数：h : G；h * a * h⁻¹；h * b * h⁻¹。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Commute.conj_iff`：∀ {G : Type u_1} [inst : Group G] {a b : G} (h : G), C
ommute (h * a * h⁻¹) (h * b * h⁻¹) ↔ Commute a b
-/
protected theorem conj (comm : Commute a b) (h : G) : Commute (h * a * h⁻¹) (h * b * h⁻¹) :=
  (Commute.conj_iff h).mpr comm

@[to_additive (attr := simp)]
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
lemma zpow_right (h : Commute a b) (m : ℤ) : Commute a (b ^ m) := SemiconjBy.zpow_right h m

@[to_additive (attr := simp)]
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
lemma zpow_left (h : Commute a b) (m : ℤ) : Commute (a ^ m) b := (h.symm.zpow_right m).symm
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
@[to_additive] lemma zpow_zpow (h : Commute a b) (m n : ℤ) : Commute (a ^ m) (b ^ n) :=
  (h.zpow_left m).zpow_right n

variable (a) (m n : ℤ)
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
@[to_additive] lemma self_zpow : Commute a (a ^ n) := (Commute.refl a).zpow_right n
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
@[to_additive] lemma zpow_self : Commute (a ^ n) a := (Commute.refl a).zpow_left n
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
@[to_additive] lemma zpow_zpow_self : Commute (a ^ m) (a ^ n) := (Commute.refl a).zpow_zpow m n

end Group
end Commute

section Group
variable [Group G]

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
@[to_additive] lemma pow_inv_comm (a : G) (m n : ℕ) : a⁻¹ ^ m * a ^ n = a ^ n * a⁻¹ ^ m :=
  (Commute.refl a).inv_left.pow_pow _ _

end Group

