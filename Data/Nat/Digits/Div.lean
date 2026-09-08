/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Shing Tak Lam, Mario Carneiro
-/
module

public import Mathlib.Data.List.Palindrome
public import Mathlib.Data.Nat.Digits.Lemmas

/-!
# Divisibility tests for natural numbers in terms of digits.

We prove some divisibility tests based on digits, in particular completing
Theorem #85 from https://www.cs.ru.nl/~freek/100/.

-/

public section

namespace Nat

variable {n : ℕ}

/-
**Nat.modEq_three_digits_sum** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：modEq_three_digits_sum (n : Nat) : n ≡ (digits 10 n).sum [MOD 3]
参数：n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.modEq_digits_sum`：modEq_digits_sum (b b' : Nat) (h : b' % b = 1) (n 
: Nat) : n ≡ (digits b' n).sum [MOD b]
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem modEq_three_digits_sum (n : ℕ) : n ≡ (digits 10 n).sum [MOD 3] :=
  modEq_digits_sum 3 10 (by simp) n
/-
**Nat.modEq_nine_digits_sum** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：modEq_nine_digits_sum (n : Nat) : n ≡ (digits 10 n).sum [MOD 9]
参数：n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.modEq_digits_sum`：modEq_digits_sum (b b' : Nat) (h : b' % b = 1) (n 
: Nat) : n ≡ (digits b' n).sum [MOD b]
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem modEq_nine_digits_sum (n : ℕ) : n ≡ (digits 10 n).sum [MOD 9] :=
  modEq_digits_sum 9 10 (by simp) n
/-
**Nat.modEq_eleven_digits_sum** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：modEq_eleven_digits_sum (n : Nat) : n ≡ ((digits 10 n).map fun n : Nat => 
(n : Int)).alternatingSum [ZMOD 11]
参数：n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.zmodeq_ofDigits_digits`：zmodeq_ofDigits_digits (b b' : Nat) (c : Int
) (h : b' ≡ c [ZMOD b]) (n : Nat) : n ≡ ofDigits c (digits b' n) [ZMOD b]
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.ofDigits_neg_one`：∀ (L : List ℕ), Nat.ofDigits (-1) L = (List.map (f
un n => ↑n) L).alternatingSum
-/
theorem modEq_eleven_digits_sum (n : ℕ) :
    n ≡ ((digits 10 n).map fun n : ℕ => (n : ℤ)).alternatingSum [ZMOD 11] := by
  have t := zmodeq_ofDigits_digits 11 10 (-1 : ℤ) (by unfold Int.ModEq; rfl) n
  rwa [ofDigits_neg_one] at t

/-! ## Divisibility  -/

/-
**Nat.dvd_iff_dvd_digits_sum** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：dvd_iff_dvd_digits_sum (b b' : Nat) (h : b' % b = 1) (n : Nat) : b ∣ n ↔ b
 ∣ (digits b' n).sum
参数：b b' : Nat；h : b' % b = 1；n : Nat。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.ofDigits_one`：ofDigits_one (L : List Nat) : ofDigits 1 L = L.sum
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.ofDigits_digits`：ofDigits_digits (b n : Nat) : ofDigits b (digits b 
n) = n
· 使用定理 `Nat.dvd_iff_mod_eq_zero`：∀ {m n : ℕ}, m ∣ n ↔ n % m = 0
· 使用定理 `Nat.ofDigits_mod`：ofDigits_mod (b k : Nat) (L : List Nat) : ofDigits b L
 % k = ofDigits (b % k) L % k
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
## Divisibility
-/
theorem dvd_iff_dvd_digits_sum (b b' : ℕ) (h : b' % b = 1) (n : ℕ) :
    b ∣ n ↔ b ∣ (digits b' n).sum := by
  rw [← ofDigits_one]
  conv_lhs => rw [← ofDigits_digits b' n]
  rw [Nat.dvd_iff_mod_eq_zero, Nat.dvd_iff_mod_eq_zero, ofDigits_mod, h]

/-- **Divisibility by 3 Rule** -/
/-
**Nat.three_dvd_iff** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：three_dvd_iff (n : Nat) : 3 ∣ n ↔ 3 ∣ (digits 10 n).sum
参数：n : Nat。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.dvd_iff_dvd_digits_sum`：dvd_iff_dvd_digits_sum (b b' : Nat) (h : b' 
% b = 1) (n : Nat) : b ∣ n ↔ b ∣ (digits b' n).sum
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
**Divisibility by 3 Rule**
-/
theorem three_dvd_iff (n : ℕ) : 3 ∣ n ↔ 3 ∣ (digits 10 n).sum :=
  dvd_iff_dvd_digits_sum 3 10 (by simp) n
/-
**Nat.nine_dvd_iff** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：nine_dvd_iff (n : Nat) : 9 ∣ n ↔ 9 ∣ (digits 10 n).sum
参数：n : Nat。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.dvd_iff_dvd_digits_sum`：dvd_iff_dvd_digits_sum (b b' : Nat) (h : b' 
% b = 1) (n : Nat) : b ∣ n ↔ b ∣ (digits b' n).sum
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem nine_dvd_iff (n : ℕ) : 9 ∣ n ↔ 9 ∣ (digits 10 n).sum :=
  dvd_iff_dvd_digits_sum 9 10 (by simp) n
/-
**Nat.dvd_iff_dvd_ofDigits** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：dvd_iff_dvd_ofDigits (b b' : Nat) (c : Int) (h : (b : Int) ∣ (b' : Int) - 
c) (n : Nat) : b ∣ n ↔ (b : Int) ∣ ofDigits c (digits b' n)
参数：b b' : Nat；c : Int；h : (b : Int) ∣ (b' : Int) - c；n : Nat。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Int.natCast_dvd_natCast`：∀ {m n : ℕ}, ↑m ∣ ↑n ↔ m ∣ n
· 使用定理 `dvd_iff_dvd_of_dvd_sub`：dvd_iff_dvd_of_dvd_sub (h : a ∣ b - c) : a ∣ b ↔
 a ∣ c
· 使用定理 `Int.ModEq.dvd`：∀ {n a b : ℤ}, a ≡ b [ZMOD n] → n ∣ b - a
· 使用定理 `Int.ModEq.symm`：∀ {n a b : ℤ}, a ≡ b [ZMOD n] → b ≡ a [ZMOD n]
· 使用定理 `Nat.zmodeq_ofDigits_digits`：zmodeq_ofDigits_digits (b b' : Nat) (c : Int
) (h : b' ≡ c [ZMOD b]) (n : Nat) : n ≡ ofDigits c (digits b' n) [ZMOD b]
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Int.modEq_iff_dvd`：modEq_iff_dvd : a ≡ b [ZMOD n] ↔ n ∣ b - a
-/
theorem dvd_iff_dvd_ofDigits (b b' : ℕ) (c : ℤ) (h : (b : ℤ) ∣ (b' : ℤ) - c) (n : ℕ) :
    b ∣ n ↔ (b : ℤ) ∣ ofDigits c (digits b' n) := by
  rw [← Int.natCast_dvd_natCast]
  exact
    dvd_iff_dvd_of_dvd_sub (zmodeq_ofDigits_digits b b' c (Int.modEq_iff_dvd.2 h).symm _).symm.dvd
/-
**Nat.eleven_dvd_iff** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：eleven_dvd_iff : 11 ∣ n ↔ (11 : Int) ∣ ((digits 10 n).map fun n : Nat => (
n : Int)).alternatingSum
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.dvd_iff_dvd_ofDigits`：dvd_iff_dvd_ofDigits (b b' : Nat) (c : Int) (h
 : (b : Int) ∣ (b' : Int) - c) (n : Nat) : b ∣ n ↔ (b : Int) ∣ ofDigits c (digit
s b' n)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_neg_eq_add`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α),
 a - -b = a + b
· 使用定理 `Nat.ofDigits_neg_one`：∀ (L : List ℕ), Nat.ofDigits (-1) L = (List.map (f
un n => ↑n) L).alternatingSum
-/
theorem eleven_dvd_iff :
    11 ∣ n ↔ (11 : ℤ) ∣ ((digits 10 n).map fun n : ℕ => (n : ℤ)).alternatingSum := by
  have t := dvd_iff_dvd_ofDigits 11 10 (-1 : ℤ) (by simp) n
  rw [ofDigits_neg_one] at t
  exact t
/-
**Nat.eleven_dvd_of_palindrome** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：eleven_dvd_of_palindrome (p : (digits 10 n).Palindrome) (h : Even (digits 
10 n).length) : 11 ∣ n
参数：p : (digits 10 n).Palindrome；h : Even (digits 10 n).length。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.length_map`：∀ {α : Type u_1} {β : Type u_2} {as : List α} (f : α → 
β), (List.map f as).length = as.length
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.eleven_dvd_iff`：eleven_dvd_iff : 11 ∣ n ↔ (11 : Int) ∣ ((digits 10 n
).map fun n : Nat => (n : Int)).alternatingSum
· 使用定理 `List.alternatingSum_reverse`：∀ {G : Type u_7} [inst : AddCommGroup G] (l
 : List G),   l.reverse.alternatingSum = (-1) ^ (l.length + 1) • l.alternatingSu
m
· 使用定理 `eq_zero_of_neg_eq`：∀ {α : Type u} [inst : AddCommGroup α] [inst_1 : Line
arOrder α] [IsOrderedAddMonoid α] {a : α}, -a = a → a = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_one_zsmul`：∀ {G : Type u_1} [inst : SubNegMonoid G] (x : G), -1 • x 
= -x
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用引理 `Even.neg_one_pow`：Even.neg_one_pow (h : Even n) : (-1 : α) ^ n = 1
· 使用定理 `pow_succ'`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (n : ℕ), a ^ (n + 
1) = a * a ^ n
· 使用定理 `List.Palindrome.reverse_eq`：reverse_eq {l : List α} (p : Palindrome l) :
 reverse l = l
· 使用定理 `List.Palindrome.map`：∀ {α : Type u_1} {β : Type u_2} {l : List α} (f : α
 → β), l.Palindrome → (List.map f l).Palindrome
-/
theorem eleven_dvd_of_palindrome (p : (digits 10 n).Palindrome) (h : Even (digits 10 n).length) :
    11 ∣ n := by
  let dig := (digits 10 n).map fun n : ℕ => (n : ℤ)
  replace h : Even dig.length := by rwa [List.length_map]
  refine eleven_dvd_iff.2 ⟨0, (?_ : dig.alternatingSum = 0)⟩
  have := dig.alternatingSum_reverse
  rw [(p.map _).reverse_eq, _root_.pow_succ', h.neg_one_pow, mul_one, neg_one_zsmul] at this
  exact eq_zero_of_neg_eq this.symm

end Nat

