/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Patrick Stevens
-/
module

public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Nat.Prime.Factorial

/-!
# Divisibility properties of binomial coefficients
-/

public section


namespace Nat

namespace Prime

variable {p a b k : ℕ}

/-
**Nat.Prime.dvd_choose_add** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Prime`。
形式化陈述：dvd_choose_add (hp : Prime p) (hap : a < p) (hbp : b < p) (h : p <= a + b)
 : p ∣ choose (a + b) a
参数：hp : Prime p；hap : a < p；hbp : b < p；h : p <= a + b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.Prime.dvd_factorial`：∀ {n p : ℕ}, Nat.Prime p → (p ∣ n.factorial ↔ p
 ≤ n)
· 使用定理 `Or.resolve_right`：∀ {a b : Prop}, a ∨ b → ¬b → a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.Prime.dvd_mul`：∀ {p m n : ℕ}, Nat.Prime p → (p ∣ m * n ↔ p ∣ m ∨ p ∣
 n)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.choose_symm_add`：choose_symm_add {a b : Nat} : choose (a + b) a = ch
oose (a + b) b
· 使用定理 `Nat.add_choose_mul_factorial_mul_factorial`：add_choose_mul_factorial_mul
_factorial (i j : Nat) : (i + j).choose j * i ! * j ! = (i + j)!
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
-/
theorem dvd_choose_add (hp : Prime p) (hap : a < p) (hbp : b < p) (h : p ≤ a + b) :
    p ∣ choose (a + b) a := by
  have h₁ : p ∣ (a + b)! := hp.dvd_factorial.2 h
  rw [← add_choose_mul_factorial_mul_factorial, ← choose_symm_add, hp.dvd_mul, hp.dvd_mul,
    hp.dvd_factorial, hp.dvd_factorial] at h₁
  exact (h₁.resolve_right hbp.not_ge).resolve_right hap.not_ge
/-
**Nat.Prime.dvd_choose** 是 Mathlib 中的一个引理，位于命名空间 `Nat.Prime`。
形式化陈述：dvd_choose (hp : Prime p) (ha : a < p) (hab : b - a < p) (h : p <= b) : p 
∣ choose b a
参数：hp : Prime p；ha : a < p；hab : b - a < p；h : p <= b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.add_sub_of_le`：∀ {a b : ℕ}, a ≤ b → a + (b - a) = b
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Nat.Prime.dvd_choose_add`：dvd_choose_add (hp : Prime p) (hap : a < p) (h
bp : b < p) (h : p <= a + b) : p ∣ choose (a + b) a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma dvd_choose (hp : Prime p) (ha : a < p) (hab : b - a < p) (h : p ≤ b) : p ∣ choose b a :=
  have : a + (b - a) = b := Nat.add_sub_of_le (ha.le.trans h)
  this ▸ hp.dvd_choose_add ha hab (this.symm ▸ h)
/-
**Nat.Prime.dvd_choose_self** 是 Mathlib 中的一个引理，位于命名空间 `Nat.Prime`。
形式化陈述：dvd_choose_self (hp : Prime p) (hk : k != 0) (hkp : k < p) : p ∣ choose p 
k
参数：hp : Prime p；hk : k != 0；hkp : k < p。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Nat.Prime.dvd_choose`：dvd_choose (hp : Prime p) (ha : a < p) (hab : b - 
a < p) (h : p <= b) : p ∣ choose b a
· 使用定理 `Nat.sub_lt`：∀ {n m : ℕ}, 0 < n → 0 < m → n - m < n
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `Nat.zero_le`：∀ (n : ℕ), 0 ≤ n
· 使用定理 `Nat.zero_lt_of_ne_zero`：∀ {a : ℕ}, a ≠ 0 → 0 < a
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
lemma dvd_choose_self (hp : Prime p) (hk : k ≠ 0) (hkp : k < p) : p ∣ choose p k :=
  hp.dvd_choose hkp (sub_lt ((zero_le _).trans_lt hkp) <| zero_lt_of_ne_zero hk) le_rfl
/-
**Nat.Prime.coprime_choose_of_lt** 是 Mathlib 中的一个引理，位于命名空间 `Nat.Prime`。
形式化陈述：coprime_choose_of_lt (hp : p.Prime) (hb : b < p) (ha : a <= b) : p.Coprime
 (b.choose a)
参数：hp : p.Prime；hb : b < p；ha : a <= b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.choose_eq_descFactorial_div_factorial`：choose_eq_descFactorial_div_f
actorial (n k : Nat) : n.choose k = n.descFactorial k / k !
· 使用定理 `Nat.Coprime.coprime_div_right`：∀ {m n a : ℕ}, m.Coprime n → a ∣ n → m.Co
prime (n / a)
· 使用定理 `Nat.Prime.coprime_descFactorial_of_lt_of_le`：∀ {p n k : ℕ}, Nat.Prime p 
→ n < p → k ≤ n → p.Coprime (n.descFactorial k)
· 使用定理 `Nat.factorial_dvd_descFactorial`：factorial_dvd_descFactorial (n k : Nat)
 : k ! ∣ n.descFactorial k
-/
lemma coprime_choose_of_lt (hp : p.Prime) (hb : b < p) (ha : a ≤ b) :
    p.Coprime (b.choose a) := by
  rw [Nat.choose_eq_descFactorial_div_factorial]
  exact (hp.coprime_descFactorial_of_lt_of_le hb ha).coprime_div_right
    (Nat.factorial_dvd_descFactorial b a)

end Prime

end Nat

