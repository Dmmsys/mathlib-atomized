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

variable {n : Nat}

/--
theorem `modEq_three_digits_sum` / 定理 `modEq_three_digits_sum`

English:
theorem modEq_three_digits_sum
  given: (n : Nat)
  statement: n ≡ (digits 10 n).sum [MOD 3]
  proof: modEq_digits_sum 3 10 (by simp) n

中文:
定理 modEq_three_digits_sum
  条件: (n : 自然数)
  结论: n ≡ (digits 10 n).求和 [MOD 3]
  证明: modEq_digits_sum 3 10 (by simp) n

Depends on / 依赖: modEq_digits_sum
-/
theorem modEq_three_digits_sum (n : Nat) : n ≡ (digits 10 n).sum [MOD 3] :=
  modEq_digits_sum 3 10 (by simp) n

/--
theorem `modEq_nine_digits_sum` / 定理 `modEq_nine_digits_sum`

English:
theorem modEq_nine_digits_sum
  given: (n : Nat)
  statement: n ≡ (digits 10 n).sum [MOD 9]
  proof: modEq_digits_sum 9 10 (by simp) n

中文:
定理 modEq_nine_digits_sum
  条件: (n : 自然数)
  结论: n ≡ (digits 10 n).求和 [MOD 9]
  证明: modEq_digits_sum 9 10 (by simp) n

Depends on / 依赖: modEq_digits_sum
-/
theorem modEq_nine_digits_sum (n : Nat) : n ≡ (digits 10 n).sum [MOD 9] :=
  modEq_digits_sum 9 10 (by simp) n

/--
theorem `modEq_eleven_digits_sum` / 定理 `modEq_eleven_digits_sum`

English:
theorem modEq_eleven_digits_sum
  given: (n : Nat)
  proof: by
  have t := zmodeq_ofDigits_digits 11 10 (-1 : Int) (by unfold Int.ModEq; rfl) n
  rwa [ofDigits_neg_one] at t

中文:
定理 modEq_eleven_digits_sum
  条件: (n : 自然数)
  证明: by
  have t := zmodeq_ofDigits_digits 11 10 (-1 : Int) (by unfold Int.ModEq; rfl) n
  rwa [ofDigits_neg_one] at t

Depends on / 依赖: Int.ModEq, ofDigits_neg_one, zmodeq_ofDigits_digits
-/
theorem modEq_eleven_digits_sum (n : Nat) :
    n ≡ ((digits 10 n).map fun n : Nat => (n : Int)).alternatingSum [ZMOD 11] := by
  have t := zmodeq_ofDigits_digits 11 10 (-1 : Int) (by unfold Int.ModEq; rfl) n
  rwa [ofDigits_neg_one] at t


/--
theorem `dvd_iff_dvd_digits_sum` / 定理 `dvd_iff_dvd_digits_sum`

English:
theorem dvd_iff_dvd_digits_sum
  given: (b b' : Nat) (h : b' % b = 1) (n : Nat)
  proof: by
  rw [← ofDigits_one]
  conv_lhs => rw [← ofDigits_digits b' n]
  rw [Nat.dvd_iff_mod_eq_zero]; rw [Nat.dvd_iff_mod_eq_zero]; rw [ofDigits_mod]; rw [h]

中文:
定理 dvd_iff_dvd_digits_sum
  条件: (b b' : 自然数) (h : b' % b = 1) (n : 自然数)
  证明: by
  rw [← ofDigits_one]
  conv_lhs => rw [← ofDigits_digits b' n]
  rw [Nat.dvd_iff_mod_eq_zero]; rw [Nat.dvd_iff_mod_eq_zero]; rw [ofDigits_mod]; rw [h]

Depends on / 依赖: Nat.dvd_iff_mod_eq_zero, conv_lhs, dvd_iff_mod_eq_zero, ofDigits_digits, ofDigits_mod, ofDigits_one
-/
theorem dvd_iff_dvd_digits_sum (b b' : Nat) (h : b' % b = 1) (n : Nat) :
    b ∣ n ↔ b ∣ (digits b' n).sum := by
  rw [← ofDigits_one]
  conv_lhs => rw [← ofDigits_digits b' n]
  rw [Nat.dvd_iff_mod_eq_zero]; rw [Nat.dvd_iff_mod_eq_zero]; rw [ofDigits_mod]; rw [h]

/--
theorem `three_dvd_iff` / 定理 `three_dvd_iff`

English:
theorem three_dvd_iff
  given: (n : Nat)
  statement: 3 ∣ n ↔ 3 ∣ (digits 10 n).sum
  proof: dvd_iff_dvd_digits_sum 3 10 (by simp) n

中文:
定理 three_dvd_iff
  条件: (n : 自然数)
  结论: 3 ∣ n ↔ 3 ∣ (digits 10 n).求和
  证明: dvd_iff_dvd_digits_sum 3 10 (by simp) n

Depends on / 依赖: dvd_iff_dvd_digits_sum
-/
theorem three_dvd_iff (n : Nat) : 3 ∣ n ↔ 3 ∣ (digits 10 n).sum :=
  dvd_iff_dvd_digits_sum 3 10 (by simp) n

/--
theorem `nine_dvd_iff` / 定理 `nine_dvd_iff`

English:
theorem nine_dvd_iff
  given: (n : Nat)
  statement: 9 ∣ n ↔ 9 ∣ (digits 10 n).sum
  proof: dvd_iff_dvd_digits_sum 9 10 (by simp) n

中文:
定理 nine_dvd_iff
  条件: (n : 自然数)
  结论: 9 ∣ n ↔ 9 ∣ (digits 10 n).求和
  证明: dvd_iff_dvd_digits_sum 9 10 (by simp) n

Depends on / 依赖: dvd_iff_dvd_digits_sum
-/
theorem nine_dvd_iff (n : Nat) : 9 ∣ n ↔ 9 ∣ (digits 10 n).sum :=
  dvd_iff_dvd_digits_sum 9 10 (by simp) n

/--
theorem `dvd_iff_dvd_ofDigits` / 定理 `dvd_iff_dvd_ofDigits`

English:
theorem dvd_iff_dvd_ofDigits
  given: (b b' : Nat) (c : Int) (h : (b : Int) ∣ (b' : Int) - c) (n : Nat)
  proof: by
  rw [← Int.natCast_dvd_natCast]
  exact
    dvd_iff_dvd_of_dvd_sub (zmodeq_ofDigits_digits b b' c (Int.modEq_iff_dvd.2 h).symm _).symm.dvd

中文:
定理 dvd_iff_dvd_ofDigits
  条件: (b b' : 自然数) (c : 整数) (h : (b : 整数) ∣ (b' : 整数) - c) (n : 自然数)
  证明: by
  rw [← Int.natCast_dvd_natCast]
  exact
    dvd_iff_dvd_of_dvd_sub (zmodeq_ofDigits_digits b b' c (Int.modEq_iff_dvd.2 h).symm _).symm.dvd

Depends on / 依赖: Int.modEq_iff_dvd, Int.natCast_dvd_natCast, dvd_iff_dvd_of_dvd_sub, modEq_iff_dvd, natCast_dvd_natCast, symm.dvd, zmodeq_ofDigits_digits
-/
theorem dvd_iff_dvd_ofDigits (b b' : Nat) (c : Int) (h : (b : Int) ∣ (b' : Int) - c) (n : Nat) :
    b ∣ n ↔ (b : Int) ∣ ofDigits c (digits b' n) := by
  rw [← Int.natCast_dvd_natCast]
  exact
    dvd_iff_dvd_of_dvd_sub (zmodeq_ofDigits_digits b b' c (Int.modEq_iff_dvd.2 h).symm _).symm.dvd

/--
theorem `eleven_dvd_iff` / 定理 `eleven_dvd_iff`

English:
theorem eleven_dvd_iff
  proof: by
  have t := dvd_iff_dvd_ofDigits 11 10 (-1 : Int) (by simp) n
  rw [ofDigits_neg_one] at t
  exact t

中文:
定理 eleven_dvd_iff
  证明: by
  have t := dvd_iff_dvd_ofDigits 11 10 (-1 : Int) (by simp) n
  rw [ofDigits_neg_one] at t
  exact t

Depends on / 依赖: dvd_iff_dvd_ofDigits, ofDigits_neg_one
-/
theorem eleven_dvd_iff :
    11 ∣ n ↔ (11 : Int) ∣ ((digits 10 n).map fun n : Nat => (n : Int)).alternatingSum := by
  have t := dvd_iff_dvd_ofDigits 11 10 (-1 : Int) (by simp) n
  rw [ofDigits_neg_one] at t
  exact t

/--
theorem `eleven_dvd_of_palindrome` / 定理 `eleven_dvd_of_palindrome`

English:
theorem eleven_dvd_of_palindrome
  given: (p : (digits 10 n).Palindrome) (h : Even (digits 10 n).length)
  proof: by
  let dig := (digits 10 n).map fun n : Nat => (n : Int)
  replace h : Even dig.length := by rwa [List.length_map]
  refine eleven_dvd_iff.2 ⟨0, (?_ : dig.alternatingSum = 0)⟩
  have := dig.alternatingSum_reverse
  rw [(p.map _).reverse_eq]; rw [_root_.pow_succ']; rw [h.neg_one_pow]; rw [mul_one]; rw [neg_one_zsmul] at this
  exact eq_zero_of_neg_eq this.symm

中文:
定理 eleven_dvd_of_palindrome
  条件: (p : (digits 10 n).Palindrome) (h : Even (digits 10 n).length)
  证明: by
  let dig := (digits 10 n).map fun n : Nat => (n : Int)
  replace h : Even dig.length := by rwa [List.length_map]
  refine eleven_dvd_iff.2 ⟨0, (?_ : dig.alternatingSum = 0)⟩
  have := dig.alternatingSum_reverse
  rw [(p.map _).reverse_eq]; rw [_root_.pow_succ']; rw [h.neg_one_pow]; rw [mul_one]; rw [neg_one_zsmul] at this
  exact eq_zero_of_neg_eq this.symm

Depends on / 依赖: List.length_map, _root_, _root_.pow_succ, alternatingSum, alternatingSum_reverse, dig.alternatingSum, dig.alternatingSum_reverse, dig.length, digits, eleven_dvd_iff, eq_zero_of_neg_eq, h.neg_one_pow, length, length_map, mul_one, neg_one_pow, neg_one_zsmul, p.map, pow_succ, replace
-/
theorem eleven_dvd_of_palindrome (p : (digits 10 n).Palindrome) (h : Even (digits 10 n).length) :
    11 ∣ n := by
  let dig := (digits 10 n).map fun n : Nat => (n : Int)
  replace h : Even dig.length := by rwa [List.length_map]
  refine eleven_dvd_iff.2 ⟨0, (?_ : dig.alternatingSum = 0)⟩
  have := dig.alternatingSum_reverse
  rw [(p.map _).reverse_eq]; rw [_root_.pow_succ']; rw [h.neg_one_pow]; rw [mul_one]; rw [neg_one_zsmul] at this
  exact eq_zero_of_neg_eq this.symm

end Nat
