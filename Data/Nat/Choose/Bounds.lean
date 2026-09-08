/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Eric Rodriguez
-/
module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Data.Nat.Cast.Order.Basic
public import Mathlib.Data.Nat.Choose.Basic

/-!
# Inequalities for binomial coefficients

This file proves exponential bounds on binomial coefficients. We might want to add here the
bounds `n^r/r^r ≤ n.choose r ≤ e^r n^r/r^r` in the future.

## Main declarations

* `Nat.choose_le_pow_div`: `n.choose r ≤ n^r / r!`
* `Nat.pow_le_choose`: `(n + 1 - r)^r / r! ≤ n.choose r`. Beware of the fishy ℕ-subtraction.
-/

public section


open Nat

variable {α : Type*} [Semifield α] [LinearOrder α] [IsStrictOrderedRing α] {n k : ℕ}

namespace Nat

/-
**Nat.choose_le_pow_div** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：choose_le_pow_div (r n : Nat) : (n.choose r : α) <= (n ^ r : α) / r !
参数：r n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `le_div_iff₀'`：le_div_iff₀' (hc : 0 < c) : a <= b / c ↔ c * a <= b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用定理 `Nat.factorial_pos`：∀ (n : ℕ), 0 < n.factorial
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Nat.descFactorial_eq_factorial_mul_choose`：descFactorial_eq_factorial_mu
l_choose (n k : Nat) : n.descFactorial k = k ! * n.choose k
· 使用定理 `Nat.descFactorial_le_pow`：∀ (n k : ℕ), n.descFactorial k ≤ n ^ k
-/
theorem choose_le_pow_div (r n : ℕ) : (n.choose r : α) ≤ (n ^ r : α) / r ! := by
  rw [le_div_iff₀']
  · norm_cast
    rw [← Nat.descFactorial_eq_factorial_mul_choose]
    exact n.descFactorial_le_pow r
  exact mod_cast r.factorial_pos
/-
**Nat.choose_lt_pow_div** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：choose_lt_pow_div (hn : n != 0) (hk : 2 <= k) : (n.choose k : α) < (n ^ k 
: α) / k !
参数：hn : n != 0；hk : 2 <= k。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `lt_div_iff₀'`：lt_div_iff₀' (hc : 0 < c) : a < b / c ↔ c * a < b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用定理 `Nat.factorial_pos`：∀ (n : ℕ), 0 < n.factorial
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Nat.descFactorial_eq_factorial_mul_choose`：descFactorial_eq_factorial_mu
l_choose (n k : Nat) : n.descFactorial k = k ! * n.choose k
· 使用定理 `Nat.descFactorial_lt_pow`：∀ {n : ℕ}, n ≠ 0 → ∀ {k : ℕ}, 2 ≤ k → n.descFa
ctorial k < n ^ k
-/
lemma choose_lt_pow_div (hn : n ≠ 0) (hk : 2 ≤ k) : (n.choose k : α) < (n ^ k : α) / k ! := by
  rw [lt_div_iff₀' (mod_cast k.factorial_pos)]
  norm_cast
  rw [← Nat.descFactorial_eq_factorial_mul_choose]
  exact descFactorial_lt_pow hn hk
/-
**Nat.choose_le_descFactorial** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：choose_le_descFactorial (n k : Nat) : n.choose k <= n.descFactorial k
参数：n k : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.choose_eq_descFactorial_div_factorial`：choose_eq_descFactorial_div_f
actorial (n k : Nat) : n.choose k = n.descFactorial k / k !
· 使用定理 `Nat.div_le_self`：∀ (n k : ℕ), n / k ≤ n
-/
lemma choose_le_descFactorial (n k : ℕ) : n.choose k ≤ n.descFactorial k := by
  rw [choose_eq_descFactorial_div_factorial]
  exact Nat.div_le_self _ _
/-
**Nat.choose_lt_descFactorial** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：choose_lt_descFactorial (hk : 2 <= k) (hkn : k <= n) : n.choose k < n.desc
Factorial k
参数：hk : 2 <= k；hkn : k <= n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.choose_eq_descFactorial_div_factorial`：choose_eq_descFactorial_div_f
actorial (n k : Nat) : n.choose k = n.descFactorial k / k !
· 使用定理 `Nat.div_lt_self`：∀ {n k : ℕ}, 0 < n → 1 < k → n / k < n
-/
lemma choose_lt_descFactorial (hk : 2 ≤ k) (hkn : k ≤ n) : n.choose k < n.descFactorial k := by
  rw [choose_eq_descFactorial_div_factorial]; exact Nat.div_lt_self (by simpa) (by simpa)
/-
**Nat.choose_le_pow** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：choose_le_pow (n k : Nat) : n.choose k <= n ^ k
参数：n k : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `Nat.choose_le_descFactorial`：choose_le_descFactorial (n k : Nat) : n.cho
ose k <= n.descFactorial k
· 使用定理 `Nat.descFactorial_le_pow`：∀ (n k : ℕ), n.descFactorial k ≤ n ^ k
-/
lemma choose_le_pow (n k : ℕ) : n.choose k ≤ n ^ k :=
  (choose_le_descFactorial n k).trans (descFactorial_le_pow n k)
/-
**Nat.choose_lt_pow** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：choose_lt_pow (hn : n != 0) (hk : 2 <= k) : n.choose k < n ^ k
参数：hn : n != 0；hk : 2 <= k。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用引理 `Nat.choose_le_descFactorial`：choose_le_descFactorial (n k : Nat) : n.cho
ose k <= n.descFactorial k
· 使用定理 `Nat.descFactorial_lt_pow`：∀ {n : ℕ}, n ≠ 0 → ∀ {k : ℕ}, 2 ≤ k → n.descFa
ctorial k < n ^ k
-/
lemma choose_lt_pow (hn : n ≠ 0) (hk : 2 ≤ k) : n.choose k < n ^ k :=
  (choose_le_descFactorial n k).trans_lt (descFactorial_lt_pow hn hk)
/-
**Nat.choose_add_le_add_one_pow** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：choose_add_le_add_one_pow (n k : Nat) : (n + k).choose k <= (n + 1) ^ k
参数：n k : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.choose_eq_asc_factorial_div_factorial`：choose_eq_asc_factorial_div_f
actorial (n k : Nat) : (n + k).choose k = (n + 1).ascFactorial k / k !
· 使用定理 `Nat.div_le_of_le_mul`：∀ {m n k : ℕ}, m ≤ k * n → m / k ≤ n
· 使用定理 `Nat.ascFactorial_le_factorial_mul_pow`：ascFactorial_le_factorial_mul_pow
 (n k : Nat) : n.ascFactorial k <= k ! * n ^ k
-/
theorem choose_add_le_add_one_pow (n k : ℕ) : (n + k).choose k ≤ (n + 1) ^ k := by
  rw [choose_eq_asc_factorial_div_factorial]
  exact Nat.div_le_of_le_mul (ascFactorial_le_factorial_mul_pow _ _)
/-
**Nat.choose_le_sub_pow** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：choose_le_sub_pow (n k : Nat) : n.choose k <= (n + 1 - k) ^ k
参数：n k : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_or_gt`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b <
 a
· 使用定理 `Nat.exists_eq_add_of_le`：∀ {m n : ℕ}, m ≤ n → ∃ k, n = m + k
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.add_comm`：∀ (n m : ℕ), n + m = m + n
· 使用定理 `Nat.add_right_comm`：∀ (n m k : ℕ), n + m + k = n + k + m
· 使用定理 `Nat.add_sub_cancel`：∀ (n m : ℕ), n + m - m = n
· 使用定理 `Nat.choose_add_le_add_one_pow`：choose_add_le_add_one_pow (n k : Nat) : (
n + k).choose k <= (n + 1) ^ k
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.choose_eq_zero_of_lt`：choose_eq_zero_of_lt : forall {n k}, n < k -> 
choose n k = 0 | _, 0, hk => absurd hk (Nat.not_lt_zero _) | 0, _ + 1, _ => choo
se_zero_succ _…
· 使用定理 `MulLeftMono.toPosMulMono`：∀ {α : Type u_1} [inst : Mul α] [inst_1 : Zero
 α] [inst_2 : Preorder α] [MulLeftMono α], PosMulMono α
-/
theorem choose_le_sub_pow (n k : ℕ) : n.choose k ≤ (n + 1 - k) ^ k := by
  rcases le_or_gt k n with h | h
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le h
    rw [Nat.add_comm k m, Nat.add_right_comm, Nat.add_sub_cancel]
    exact choose_add_le_add_one_pow m k
  · simp [choose_eq_zero_of_lt h]

-- horrific casting is due to ℕ-subtraction
/-
**Nat.pow_le_choose** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：pow_le_choose (r n : Nat) : ((n + 1 - r : Nat) ^ r : α) / r ! <= n.choose 
r
参数：r n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `div_le_iff₀'`：div_le_iff₀' (hc : 0 < c) : b / c <= a ↔ b <= c * a
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用定理 `Nat.factorial_pos`：∀ (n : ℕ), 0 < n.factorial
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Nat.descFactorial_eq_factorial_mul_choose`：descFactorial_eq_factorial_mu
l_choose (n k : Nat) : n.descFactorial k = k ! * n.choose k
· 使用定理 `Nat.pow_sub_le_descFactorial`：∀ (n k : ℕ), (n + 1 - k) ^ k ≤ n.descFacto
rial k
-/
theorem pow_le_choose (r n : ℕ) : ((n + 1 - r : ℕ) ^ r : α) / r ! ≤ n.choose r := by
  rw [div_le_iff₀']
  · norm_cast
    rw [← Nat.descFactorial_eq_factorial_mul_choose]
    exact n.pow_sub_le_descFactorial r
  exact mod_cast r.factorial_pos
/-
**Nat.choose_succ_le_two_pow** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：choose_succ_le_two_pow (n k : Nat) : (n + 1).choose k <= 2 ^ n
参数：n k : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.choose_succ_le_two_pow._unary`：∀ (_x : (_ : ℕ) ×' ℕ), (_x.1 + 1).cho
ose _x.2 ≤ 2 ^ _x.1
-/
theorem choose_succ_le_two_pow (n k : ℕ) : (n + 1).choose k ≤ 2 ^ n := by
  by_cases lt : n + 1 < k
  · simp [choose_eq_zero_of_lt lt]
  · cases n with
    | zero => cases k <;> simp_all
    | succ n =>
      rcases k with - | k
      · rw [choose_zero_right]
        exact Nat.one_le_two_pow
      · rw [choose_succ_succ', two_pow_succ]
        exact Nat.add_le_add (choose_succ_le_two_pow n k) (choose_succ_le_two_pow n (k + 1))
/-
**Nat.choose_lt_two_pow** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：choose_lt_two_pow (n k : Nat) (p : 0 < n) : n.choose k < 2 ^ n
参数：n k : Nat；p : 0 < n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.sub_add_cancel`：∀ {n m : ℕ}, m ≤ n → n - m + m = n
· 使用定理 `Nat.choose_succ_le_two_pow`：choose_succ_le_two_pow (n k : Nat) : (n + 1)
.choose k <= 2 ^ n
· 使用定理 `Nat.two_pow_pred_lt_two_pow`：∀ {w : ℕ}, 0 < w → 2 ^ (w - 1) < 2 ^ w
-/
theorem choose_lt_two_pow (n k : ℕ) (p : 0 < n) : n.choose k < 2 ^ n := by
  refine lt_of_le_of_lt ?_ (Nat.two_pow_pred_lt_two_pow p)
  rw [← Nat.sub_add_cancel p]
  exact choose_succ_le_two_pow (n - 1) k
/-
**Nat.choose_le_two_pow** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：choose_le_two_pow (n k : Nat) : n.choose k <= 2 ^ n
参数：n k : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.eq_zero_or_pos`：∀ (n : ℕ), n = 0 ∨ n > 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.choose_self`：choose_self (n : Nat) : choose n n = 1
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Nat.choose_lt_two_pow`：choose_lt_two_pow (n k : Nat) (p : 0 < n) : n.cho
ose k < 2 ^ n
-/
theorem choose_le_two_pow (n k : ℕ) : n.choose k ≤ 2 ^ n := by
  obtain (rfl | hn) := eq_zero_or_pos n
  · cases k <;> simp
  · exact (Nat.choose_lt_two_pow _ _ hn).le

end Nat

