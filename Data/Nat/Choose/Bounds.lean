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

variable {α : Type*} [Semifield α] [LinearOrder α] [IsStrictOrderedRing α] {n k : Nat}

namespace Nat

/--
theorem `choose_le_pow_div` / 定理 `choose_le_pow_div`

English:
theorem choose_le_pow_div
  given: (r n : Nat)
  statement: (n.choose r : α) <= (n ^ r : α) / r !
  proof: by
  rw [le_div_iff₀']
  · norm_cast
    rw [← Nat.descFactorial_eq_factorial_mul_choose]
    exact n.descFactorial_le_pow r
  exact mod_cast r.factorial_pos

中文:
定理 choose_le_pow_div
  条件: (r n : 自然数)
  结论: (n.choose r : α) <= (n ^ r : α) / r !
  证明: by
  rw [le_div_iff₀']
  · norm_cast
    rw [← Nat.descFactorial_eq_factorial_mul_choose]
    exact n.descFactorial_le_pow r
  exact mod_cast r.factorial_pos

Depends on / 依赖: Nat.descFactorial_eq_factorial_mul_choose, descFactorial_eq_factorial_mul_choose, descFactorial_le_pow, factorial_pos, mod_cast, n.descFactorial_le_pow, r.factorial_pos
-/
theorem choose_le_pow_div (r n : Nat) : (n.choose r : α) <= (n ^ r : α) / r ! := by
  rw [le_div_iff₀']
  · norm_cast
    rw [← Nat.descFactorial_eq_factorial_mul_choose]
    exact n.descFactorial_le_pow r
  exact mod_cast r.factorial_pos

/--
lemma `choose_lt_pow_div` / 引理 `choose_lt_pow_div`

English:
lemma choose_lt_pow_div
  given: (hn : n != 0) (hk : 2 <= k)
  statement: (n.choose k : α) < (n ^ k : α) / k !
  proof: by
  rw [lt_div_iff₀' (mod_cast k.factorial_pos)]
  norm_cast
  rw [← Nat.descFactorial_eq_factorial_mul_choose]
  exact descFactorial_lt_pow hn hk

中文:
引理 choose_lt_pow_div
  条件: (hn : n != 0) (hk : 2 <= k)
  结论: (n.choose k : α) < (n ^ k : α) / k !
  证明: by
  rw [lt_div_iff₀' (mod_cast k.factorial_pos)]
  norm_cast
  rw [← Nat.descFactorial_eq_factorial_mul_choose]
  exact descFactorial_lt_pow hn hk

Depends on / 依赖: Nat.descFactorial_eq_factorial_mul_choose, descFactorial_eq_factorial_mul_choose, descFactorial_lt_pow, factorial_pos, k.factorial_pos, mod_cast
-/
lemma choose_lt_pow_div (hn : n != 0) (hk : 2 <= k) : (n.choose k : α) < (n ^ k : α) / k ! := by
  rw [lt_div_iff₀' (mod_cast k.factorial_pos)]
  norm_cast
  rw [← Nat.descFactorial_eq_factorial_mul_choose]
  exact descFactorial_lt_pow hn hk

/--
lemma `choose_le_descFactorial` / 引理 `choose_le_descFactorial`

English:
lemma choose_le_descFactorial
  given: (n k : Nat)
  statement: n.choose k <= n.descFactorial k
  proof: by
  rw [choose_eq_descFactorial_div_factorial]
  exact Nat.div_le_self _ _

中文:
引理 choose_le_descFactorial
  条件: (n k : 自然数)
  结论: n.choose k <= n.descFactorial k
  证明: by
  rw [choose_eq_descFactorial_div_factorial]
  exact Nat.div_le_self _ _

Depends on / 依赖: Nat.div_le_self, choose_eq_descFactorial_div_factorial, div_le_self
-/
lemma choose_le_descFactorial (n k : Nat) : n.choose k <= n.descFactorial k := by
  rw [choose_eq_descFactorial_div_factorial]
  exact Nat.div_le_self _ _

/--
lemma `choose_lt_descFactorial` / 引理 `choose_lt_descFactorial`

English:
lemma choose_lt_descFactorial
  given: (hk : 2 <= k) (hkn : k <= n)
  statement: n.choose k < n.descFactorial k
  proof: by
  rw [choose_eq_descFactorial_div_factorial]; exact Nat.div_lt_self (by simpa) (by simpa)

中文:
引理 choose_lt_descFactorial
  条件: (hk : 2 <= k) (hkn : k <= n)
  结论: n.choose k < n.descFactorial k
  证明: by
  rw [choose_eq_descFactorial_div_factorial]; exact Nat.div_lt_self (by simpa) (by simpa)

Depends on / 依赖: Nat.div_lt_self, choose_eq_descFactorial_div_factorial, div_lt_self
-/
lemma choose_lt_descFactorial (hk : 2 <= k) (hkn : k <= n) : n.choose k < n.descFactorial k := by
  rw [choose_eq_descFactorial_div_factorial]; exact Nat.div_lt_self (by simpa) (by simpa)

/--
lemma `choose_le_pow` / 引理 `choose_le_pow`

English:
lemma choose_le_pow
  given: (n k : Nat)
  statement: n.choose k <= n ^ k
  proof: (choose_le_descFactorial n k).trans (descFactorial_le_pow n k)

中文:
引理 choose_le_pow
  条件: (n k : 自然数)
  结论: n.choose k <= n ^ k
  证明: (choose_le_descFactorial n k).trans (descFactorial_le_pow n k)

Depends on / 依赖: choose_le_descFactorial, descFactorial_le_pow
-/
lemma choose_le_pow (n k : Nat) : n.choose k <= n ^ k :=
  (choose_le_descFactorial n k).trans (descFactorial_le_pow n k)

/--
lemma `choose_lt_pow` / 引理 `choose_lt_pow`

English:
lemma choose_lt_pow
  given: (hn : n != 0) (hk : 2 <= k)
  statement: n.choose k < n ^ k
  proof: (choose_le_descFactorial n k).trans_lt (descFactorial_lt_pow hn hk)

中文:
引理 choose_lt_pow
  条件: (hn : n != 0) (hk : 2 <= k)
  结论: n.choose k < n ^ k
  证明: (choose_le_descFactorial n k).trans_lt (descFactorial_lt_pow hn hk)

Depends on / 依赖: choose_le_descFactorial, descFactorial_lt_pow, trans_lt
-/
lemma choose_lt_pow (hn : n != 0) (hk : 2 <= k) : n.choose k < n ^ k :=
  (choose_le_descFactorial n k).trans_lt (descFactorial_lt_pow hn hk)

/--
theorem `choose_add_le_add_one_pow` / 定理 `choose_add_le_add_one_pow`

English:
theorem choose_add_le_add_one_pow
  given: (n k : Nat)
  statement: (n + k).choose k <= (n + 1) ^ k
  proof: by
  rw [choose_eq_asc_factorial_div_factorial]
  exact Nat.div_le_of_le_mul (ascFactorial_le_factorial_mul_pow _ _)

中文:
定理 choose_add_le_add_one_pow
  条件: (n k : 自然数)
  结论: (n + k).choose k <= (n + 1) ^ k
  证明: by
  rw [choose_eq_asc_factorial_div_factorial]
  exact Nat.div_le_of_le_mul (ascFactorial_le_factorial_mul_pow _ _)

Depends on / 依赖: Nat.div_le_of_le_mul, ascFactorial_le_factorial_mul_pow, choose_eq_asc_factorial_div_factorial, div_le_of_le_mul
-/
theorem choose_add_le_add_one_pow (n k : Nat) : (n + k).choose k <= (n + 1) ^ k := by
  rw [choose_eq_asc_factorial_div_factorial]
  exact Nat.div_le_of_le_mul (ascFactorial_le_factorial_mul_pow _ _)

/--
theorem `choose_le_sub_pow` / 定理 `choose_le_sub_pow`

English:
theorem choose_le_sub_pow
  given: (n k : Nat)
  statement: n.choose k <= (n + 1 - k) ^ k
  proof: by
  rcases le_or_gt k n with h | h
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le h
    rw [Nat.add_comm k m]; rw [Nat.add_right_comm]; rw [Nat.add_sub_cancel]
    exact choose_add_le_add_one_pow m k
  · simp [choose_eq_zero_of_lt h]

中文:
定理 choose_le_sub_pow
  条件: (n k : 自然数)
  结论: n.choose k <= (n + 1 - k) ^ k
  证明: by
  rcases le_or_gt k n with h | h
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le h
    rw [Nat.add_comm k m]; rw [Nat.add_right_comm]; rw [Nat.add_sub_cancel]
    exact choose_add_le_add_one_pow m k
  · simp [choose_eq_zero_of_lt h]

Depends on / 依赖: Nat.add_comm, Nat.add_right_comm, Nat.add_sub_cancel, Nat.exists_eq_add_of_le, add_comm, add_right_comm, add_sub_cancel, choose_add_le_add_one_pow, choose_eq_zero_of_lt, exists_eq_add_of_le, le_or_gt
-/
theorem choose_le_sub_pow (n k : Nat) : n.choose k <= (n + 1 - k) ^ k := by
  rcases le_or_gt k n with h | h
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le h
    rw [Nat.add_comm k m]; rw [Nat.add_right_comm]; rw [Nat.add_sub_cancel]
    exact choose_add_le_add_one_pow m k
  · simp [choose_eq_zero_of_lt h]

-- horrific casting is due to ℕ-subtraction
/--
theorem `pow_le_choose` / 定理 `pow_le_choose`

English:
theorem pow_le_choose
  given: (r n : Nat)
  statement: ((n + 1 - r : Nat) ^ r : α) / r ! <= n.choose r
  proof: by
  rw [div_le_iff₀']
  · norm_cast
    rw [← Nat.descFactorial_eq_factorial_mul_choose]
    exact n.pow_sub_le_descFactorial r
  exact mod_cast r.factorial_pos

中文:
定理 pow_le_choose
  条件: (r n : 自然数)
  结论: ((n + 1 - r : 自然数) ^ r : α) / r ! <= n.choose r
  证明: by
  rw [div_le_iff₀']
  · norm_cast
    rw [← Nat.descFactorial_eq_factorial_mul_choose]
    exact n.pow_sub_le_descFactorial r
  exact mod_cast r.factorial_pos

Depends on / 依赖: Nat.descFactorial_eq_factorial_mul_choose, descFactorial_eq_factorial_mul_choose, factorial_pos, mod_cast, n.pow_sub_le_descFactorial, pow_sub_le_descFactorial, r.factorial_pos
-/
theorem pow_le_choose (r n : Nat) : ((n + 1 - r : Nat) ^ r : α) / r ! <= n.choose r := by
  rw [div_le_iff₀']
  · norm_cast
    rw [← Nat.descFactorial_eq_factorial_mul_choose]
    exact n.pow_sub_le_descFactorial r
  exact mod_cast r.factorial_pos

/--
theorem `choose_succ_le_two_pow` / 定理 `choose_succ_le_two_pow`

English:
theorem choose_succ_le_two_pow
  given: (n k : Nat)
  statement: (n + 1).choose k <= 2 ^ n
  proof: by
  by_cases lt : n + 1 < k
  · simp [choose_eq_zero_of_lt lt]
  · cases n with
    | zero => cases k <;> simp_all
    | succ n =>
      rcases k with - | k
      · rw [choose_zero_right]
        exact Nat.one_le_two_pow
      · rw [choose_succ_succ', two_pow_succ]
        exact Nat.add_le_add (cho

中文:
定理 choose_succ_le_two_pow
  条件: (n k : 自然数)
  结论: (n + 1).choose k <= 2 ^ n
  证明: by
  by_cases lt : n + 1 < k
  · simp [choose_eq_zero_of_lt lt]
  · cases n with
    | zero => cases k <;> simp_all
    | succ n =>
      rcases k with - | k
      · rw [choose_zero_right]
        exact Nat.one_le_two_pow
      · rw [choose_succ_succ', two_pow_succ]
        exact Nat.add_le_add (cho

Depends on / 依赖: Nat.add_le_add, Nat.one_le_two_pow, add_le_add, choose_eq_zero_of_lt, choose_succ_le_two_pow, choose_succ_succ, choose_zero_right, one_le_two_pow, two_pow_succ
-/
theorem choose_succ_le_two_pow (n k : Nat) : (n + 1).choose k <= 2 ^ n := by
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

/--
theorem `choose_lt_two_pow` / 定理 `choose_lt_two_pow`

English:
theorem choose_lt_two_pow
  given: (n k : Nat) (p : 0 < n)
  statement: n.choose k < 2 ^ n
  proof: by
  refine lt_of_le_of_lt ?_ (Nat.two_pow_pred_lt_two_pow p)
  rw [← Nat.sub_add_cancel p]
  exact choose_succ_le_two_pow (n - 1) k

中文:
定理 choose_lt_two_pow
  条件: (n k : 自然数) (p : 0 < n)
  结论: n.choose k < 2 ^ n
  证明: by
  refine lt_of_le_of_lt ?_ (Nat.two_pow_pred_lt_two_pow p)
  rw [← Nat.sub_add_cancel p]
  exact choose_succ_le_two_pow (n - 1) k

Depends on / 依赖: Nat.sub_add_cancel, Nat.two_pow_pred_lt_two_pow, choose_succ_le_two_pow, lt_of_le_of_lt, sub_add_cancel, two_pow_pred_lt_two_pow
-/
theorem choose_lt_two_pow (n k : Nat) (p : 0 < n) : n.choose k < 2 ^ n := by
  refine lt_of_le_of_lt ?_ (Nat.two_pow_pred_lt_two_pow p)
  rw [← Nat.sub_add_cancel p]
  exact choose_succ_le_two_pow (n - 1) k

/--
theorem `choose_le_two_pow` / 定理 `choose_le_two_pow`

English:
theorem choose_le_two_pow
  given: (n k : Nat)
  statement: n.choose k <= 2 ^ n
  proof: by
  obtain (rfl | hn) := eq_zero_or_pos n
  · cases k <;> simp
  · exact (Nat.choose_lt_two_pow _ _ hn).le

中文:
定理 choose_le_two_pow
  条件: (n k : 自然数)
  结论: n.choose k <= 2 ^ n
  证明: by
  obtain (rfl | hn) := eq_zero_or_pos n
  · cases k <;> simp
  · exact (Nat.choose_lt_two_pow _ _ hn).le

Depends on / 依赖: Nat.choose_lt_two_pow, choose_lt_two_pow, eq_zero_or_pos
-/
theorem choose_le_two_pow (n k : Nat) : n.choose k <= 2 ^ n := by
  obtain (rfl | hn) := eq_zero_or_pos n
  · cases k <;> simp
  · exact (Nat.choose_lt_two_pow _ _ hn).le

end Nat
