/-
Copyright (c) 2019 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
-- Some proofs and docs came from mathlib3 `src/algebra/commute.lean` (c) Neil Strickland
module

public import Mathlib.Algebra.Group.Semiconj.Defs
public import Mathlib.Algebra.Group.Units.Basic

/-!
# Semiconjugate elements of a semigroup

## Main definitions

We say that `x` is semiconjugate to `y` by `a` (`SemiconjBy a x y`), if `a * x = y * a`.
In this file we provide operations on `SemiconjBy _ _ _`.

In the names of these operations, we treat `a` as the “left” argument, and both `x` and `y` as
“right” arguments. This way most names in this file agree with the names of the corresponding lemmas
for `Commute a b = SemiconjBy a b b`. As a side effect, some lemmas have only `_right` version.

Lean does not immediately recognise these terms as equations, so for rewriting we need syntax like
`rw [(h.pow_right 5).eq]` rather than just `rw [h.pow_right 5]`.

This file provides only basic operations (`mul_left`, `mul_right`, `inv_right` etc). Other
operations (`pow_right`, field inverse etc) are in the files that define corresponding notions.
-/

public section

assert_not_exists MonoidWithZero DenselyOrdered

open scoped Int

variable {M : Type*}

namespace SemiconjBy

section Monoid

variable [Monoid M]

/-- If `a` semiconjugates a unit `x` to a unit `y`, then it semiconjugates `x⁻¹` to `y⁻¹`. -/
@[to_additive /-- If `a` semiconjugates an additive unit `x` to an additive unit `y`, then it
semiconjugates `-x` to `-y`. -/]
/-
**SemiconjBy.units_inv_right** 是 Mathlib 中的一个定理，位于命名空间 `SemiconjBy`。
形式化陈述：units_inv_right {a : M} {x y : Mˣ} (h : SemiconjBy a x y) : SemiconjBy a ↑
x⁻¹ ↑y⁻¹
参数：h : SemiconjBy a x y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Units.inv_mul_cancel_left`：inv_mul_cancel_left (a : αˣ) (b : α) : (↑a⁻¹ 
: α) * (a * b) = b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SemiconjBy.eq`：∀ {S : Type u_1} [inst : Mul S] {a x y : S}, SemiconjBy a
 x y → a * x = y * a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Units.mul_inv_cancel_right`：mul_inv_cancel_right (a : α) (b : αˣ) : a * 
b * ↑b⁻¹ = a
-/
theorem units_inv_right {a : M} {x y : Mˣ} (h : SemiconjBy a x y) : SemiconjBy a ↑x⁻¹ ↑y⁻¹ :=
  calc a * ↑x⁻¹
    _ = ↑y⁻¹ * (y * a) * ↑x⁻¹ := by rw [Units.inv_mul_cancel_left]
    _ = ↑y⁻¹ * a := by rw [← h.eq, mul_assoc, Units.mul_inv_cancel_right]

@[to_additive (attr := simp)]
/-
**SemiconjBy.units_inv_right_iff** 是 Mathlib 中的一个定理，位于命名空间 `SemiconjBy`。
形式化陈述：units_inv_right_iff {a : M} {x y : Mˣ} : SemiconjBy a ↑x⁻¹ ↑y⁻¹ ↔ Semiconj
By a x y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SemiconjBy.units_inv_right`：units_inv_right {a : M} {x y : Mˣ} (h : Semi
conjBy a x y) : SemiconjBy a ↑x⁻¹ ↑y⁻¹
-/
theorem units_inv_right_iff {a : M} {x y : Mˣ} : SemiconjBy a ↑x⁻¹ ↑y⁻¹ ↔ SemiconjBy a x y :=
  ⟨units_inv_right, units_inv_right⟩

/-- If a unit `a` semiconjugates `x` to `y`, then `a⁻¹` semiconjugates `y` to `x`. -/
@[to_additive /-- If an additive unit `a` semiconjugates `x` to `y`, then `-a` semiconjugates `y` to
`x`. -/]
/-
**SemiconjBy.units_inv_symm_left** 是 Mathlib 中的一个定理，位于命名空间 `SemiconjBy`。
形式化陈述：units_inv_symm_left {a : Mˣ} {x y : M} (h : SemiconjBy (↑a) x y) : Semicon
jBy (↑a⁻¹) y x
参数：h : SemiconjBy (↑a) x y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Units.mul_inv_cancel_right`：mul_inv_cancel_right (a : α) (b : αˣ) : a * 
b * ↑b⁻¹ = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SemiconjBy.eq`：∀ {S : Type u_1} [inst : Mul S] {a x y : S}, SemiconjBy a
 x y → a * x = y * a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Units.inv_mul_cancel_left`：inv_mul_cancel_left (a : αˣ) (b : α) : (↑a⁻¹ 
: α) * (a * b) = b
-/
theorem units_inv_symm_left {a : Mˣ} {x y : M} (h : SemiconjBy (↑a) x y) : SemiconjBy (↑a⁻¹) y x :=
  calc
    ↑a⁻¹ * y = ↑a⁻¹ * (y * a * ↑a⁻¹) := by rw [Units.mul_inv_cancel_right]
    _ = x * ↑a⁻¹ := by rw [← h.eq, ← mul_assoc, Units.inv_mul_cancel_left]

@[to_additive (attr := simp)]
/-
**SemiconjBy.units_inv_symm_left_iff** 是 Mathlib 中的一个定理，位于命名空间 `SemiconjBy`。
形式化陈述：units_inv_symm_left_iff {a : Mˣ} {x y : M} : SemiconjBy (↑a⁻¹) y x ↔ Semic
onjBy (↑a) x y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SemiconjBy.units_inv_symm_left`：units_inv_symm_left {a : Mˣ} {x y : M} (
h : SemiconjBy (↑a) x y) : SemiconjBy (↑a⁻¹) y x
-/
theorem units_inv_symm_left_iff {a : Mˣ} {x y : M} : SemiconjBy (↑a⁻¹) y x ↔ SemiconjBy (↑a) x y :=
  ⟨units_inv_symm_left, units_inv_symm_left⟩

@[to_additive]
/-
**SemiconjBy.units_val** 是 Mathlib 中的一个定理，位于命名空间 `SemiconjBy`。
形式化陈述：units_val {a x y : Mˣ} (h : SemiconjBy a x y) : SemiconjBy (a : M) x y
参数：h : SemiconjBy a x y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
theorem units_val {a x y : Mˣ} (h : SemiconjBy a x y) : SemiconjBy (a : M) x y :=
  congr_arg Units.val h

@[to_additive]
/-
**SemiconjBy.units_of_val** 是 Mathlib 中的一个定理，位于命名空间 `SemiconjBy`。
形式化陈述：units_of_val {a x y : Mˣ} (h : SemiconjBy (a : M) x y) : SemiconjBy a x y
参数：h : SemiconjBy (a : M) x y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Units.ext`：ext {u v : αˣ} (huv : u.val = v.val) : u = v
-/
theorem units_of_val {a x y : Mˣ} (h : SemiconjBy (a : M) x y) : SemiconjBy a x y :=
  Units.ext h

@[to_additive (attr := simp)]
/-
**SemiconjBy.units_val_iff** 是 Mathlib 中的一个定理，位于命名空间 `SemiconjBy`。
形式化陈述：units_val_iff {a x y : Mˣ} : SemiconjBy (a : M) x y ↔ SemiconjBy a x y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SemiconjBy.units_of_val`：units_of_val {a x y : Mˣ} (h : SemiconjBy (a : 
M) x y) : SemiconjBy a x y
· 使用定理 `SemiconjBy.units_val`：units_val {a x y : Mˣ} (h : SemiconjBy a x y) : Se
miconjBy (a : M) x y
-/
theorem units_val_iff {a x y : Mˣ} : SemiconjBy (a : M) x y ↔ SemiconjBy a x y :=
  ⟨units_of_val, units_val⟩

@[to_additive (attr := simp)]
/-
**SemiconjBy.units_zpow_right** 是 Mathlib 中的一个定理，位于命名空间 `SemiconjBy`。
形式化陈述：∀ {M : Type u_1} [inst : Monoid M] {a : M} {x y : Mˣ}, SemiconjBy a ↑x ↑y 
→ ∀ (m : ℤ), SemiconjBy a ↑(x ^ m) ↑(y ^ m)
参数：m : ℤ；x ^ m；y ^ m。
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
· 使用定理 `zpow_negSucc`：zpow_negSucc (a : G) (n : Nat) : a ^ (Int.negSucc n) = (a 
^ (n + 1))⁻¹
-/
lemma units_zpow_right {a : M} {x y : Mˣ} (h : SemiconjBy a x y) :
    ∀ m : ℤ, SemiconjBy a ↑(x ^ m) ↑(y ^ m)
  | (n : ℕ) => by simp only [zpow_natCast, Units.val_pow_eq_pow_val, h, pow_right]
  | -[n+1] => by simp only [zpow_negSucc, Units.val_pow_eq_pow_val, units_inv_right, h, pow_right]

end Monoid
end SemiconjBy

namespace Units
variable [Monoid M]

/-- `a` semiconjugates `x` to `a * x * a⁻¹`. -/
@[to_additive /-- `a` semiconjugates `x` to `a + x + -a`. -/]
/-
**Units.mk_semiconjBy** 是 Mathlib 中的一个引理，位于命名空间 `Units`。
形式化陈述：mk_semiconjBy (u : Mˣ) (x : M) : SemiconjBy (↑u) x (u * x * ↑u⁻¹)
参数：u : Mˣ；x : M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Units.inv_mul_cancel_right`：inv_mul_cancel_right (a : α) (b : αˣ) : a * 
↑b⁻¹ * b = a

--- 原说明 ---
`a` semiconjugates `x` to `a * x * a⁻¹`.
-/
lemma mk_semiconjBy (u : Mˣ) (x : M) : SemiconjBy (↑u) x (u * x * ↑u⁻¹) := by
  unfold SemiconjBy; rw [Units.inv_mul_cancel_right]
/-
**Units.conj_pow** 是 Mathlib 中的一个引理，位于命名空间 `Units`。
形式化陈述：conj_pow (u : Mˣ) (x : M) (n : Nat) : ((↑u : M) * x * (↑u⁻¹ : M)) ^ n = (u
 : M) * x ^ n * (↑u⁻¹ : M)
参数：u : Mˣ；x : M；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `eq_divp_iff_mul_eq`：eq_divp_iff_mul_eq {x : α} {u : αˣ} {y : α} : x = y 
/ₚ u ↔ x * u = y
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SemiconjBy.eq`：∀ {S : Type u_1} [inst : Mul S] {a x y : S}, SemiconjBy a
 x y → a * x = y * a
· 使用定理 `SemiconjBy.pow_right`：pow_right {a x y : M} (h : SemiconjBy a x y) (n : 
Nat) : SemiconjBy a (x ^ n) (y ^ n)
· 使用引理 `Units.mk_semiconjBy`：mk_semiconjBy (u : Mˣ) (x : M) : SemiconjBy (↑u) x 
(u * x * ↑u⁻¹)
-/
lemma conj_pow (u : Mˣ) (x : M) (n : ℕ) :
    ((↑u : M) * x * (↑u⁻¹ : M)) ^ n = (u : M) * x ^ n * (↑u⁻¹ : M) :=
  eq_divp_iff_mul_eq.2 ((u.mk_semiconjBy x).pow_right n).eq.symm
/-
**Units.conj_pow'** 是 Mathlib 中的一个引理，位于命名空间 `Units`。
形式化陈述：conj_pow' (u : Mˣ) (x : M) (n : Nat) : ((↑u⁻¹ : M) * x * (u : M)) ^ n = (↑
u⁻¹ : M) * x ^ n * (u : M)
参数：u : Mˣ；x : M；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Units.conj_pow`：conj_pow (u : Mˣ) (x : M) (n : Nat) : ((↑u : M) * x * (↑
u⁻¹ : M)) ^ n = (u : M) * x ^ n * (↑u⁻¹ : M)
-/
lemma conj_pow' (u : Mˣ) (x : M) (n : ℕ) :
    ((↑u⁻¹ : M) * x * (u : M)) ^ n = (↑u⁻¹ : M) * x ^ n * (u : M) := u⁻¹.conj_pow x n

end Units

