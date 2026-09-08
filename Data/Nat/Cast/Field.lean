/-
Copyright (c) 2014 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Yaël Dillies, Patrick Stevens
-/
module

public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.Tactic.Common
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.GroupWithZero.Units.Basic

/-!
# Cast of naturals into fields

This file concerns the canonical homomorphism `ℕ → F`, where `F` is a field.

## Main results

* `Nat.cast_div`: if `n` divides `m`, then `↑(m / n) = ↑m / ↑n`
-/

public section


namespace Nat

variable {K : Type*} [DivisionSemiring K] {d m n : ℕ}

@[simp]
/-
**Nat.cast_div** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：cast_div (hnm : n ∣ m) (hn : (n : K) != 0) : (↑(m / n) : K) = m / n
参数：hnm : n ∣ m；hn : (n : K) != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.mul_div_cancel_left`：∀ (m : ℕ) {n : ℕ}, 0 < n → n * m / n = m
· 使用定理 `Nat.zero_lt_of_ne_zero`：∀ {a : ℕ}, a ≠ 0 → 0 < a
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Nat.cast_mul`：∀ {α : Type u_1} [inst : NonAssocSemiring α] (m n : ℕ), ↑(
m * n) = ↑m * ↑n
· 使用定理 `mul_div_cancel_right₀`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀] [ins
t_1 : Div M₀] [MulDivCancelClass M₀] (a : M₀) {b : M₀},   b ≠ 0 → a * b / b = a
· 使用定理 `GroupWithZero.toMulDivCancelClass`：∀ {G₀ : Type u} [inst : GroupWithZero
 G₀], MulDivCancelClass G₀
-/
lemma cast_div (hnm : n ∣ m) (hn : (n : K) ≠ 0) : (↑(m / n) : K) = m / n := by
  obtain ⟨k, rfl⟩ := hnm
  have : n ≠ 0 := by rintro rfl; simp at hn
  rw [Nat.mul_div_cancel_left _ <| zero_lt_of_ne_zero this, mul_comm n,
    cast_mul, mul_div_cancel_right₀ _ hn]

variable [CharZero K]

@[simp, norm_cast]
/-
**Nat.cast_div_charZero** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：cast_div_charZero (hnm : n ∣ m) : (↑(m / n) : K) = m / n
参数：hnm : n ∣ m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.div_zero`：∀ (n : ℕ), n / 0 = 0
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `div_zero`：div_zero (a : G₀) : a / 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `Nat.cast_div`：cast_div (hnm : n ∣ m) (hn : (n : K) != 0) : (↑(m / n) : K
) = m / n
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
lemma cast_div_charZero (hnm : n ∣ m) : (↑(m / n) : K) = m / n := by
  obtain rfl | hn := eq_or_ne n 0 <;> simp [*]
/-
**Nat.cast_div_div_div_cancel_right** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：cast_div_div_div_cancel_right (hn : d ∣ n) (hm : d ∣ m) : (↑(m / d) : K) /
 (↑(n / d) : K) = (m : K) / n
参数：hn : d ∣ n；hm : d ∣ m。
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
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.zero_dvd`：∀ {n : ℕ}, 0 ∣ n ↔ n = 0
· 使用定理 `Nat.div_zero`：∀ (n : ℕ), n / 0 = 0
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `div_zero`：div_zero (a : G₀) : a / 0 = 0
· 使用定理 `zero_div`：zero_div (a : G₀) : 0 / a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Nat.cast_div`：cast_div (hnm : n ∣ m) (hn : (n : K) != 0) : (↑(m / n) : K
) = m / n
· 使用引理 `div_div_div_cancel_right₀`：div_div_div_cancel_right₀ (hc : c != 0) (a b 
: G₀) : a / c / (b / c) = a / b
-/
lemma cast_div_div_div_cancel_right (hn : d ∣ n) (hm : d ∣ m) :
    (↑(m / d) : K) / (↑(n / d) : K) = (m : K) / n := by
  rcases eq_or_ne d 0 with (rfl | hd); · simp [Nat.zero_dvd.1 hm]
  replace hd : (d : K) ≠ 0 := by norm_cast
  rw [cast_div hm, cast_div hn, div_div_div_cancel_right₀ hd] <;> exact hd

end Nat

