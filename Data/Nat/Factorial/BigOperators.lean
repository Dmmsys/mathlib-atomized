/-
Copyright (c) 2022 Pim Otte. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller, Pim Otte
-/
module

public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Tactic.Zify

/-!
# Factorial with big operators

This file contains some lemmas on factorials in combination with big operators.

While in terms of semantics they could be in the `Basic.lean` file, importing
`Algebra.BigOperators.Group.Finset` leads to a cyclic import.

-/

public section


open Finset Nat

namespace Nat

/--
lemma `monotone_factorial` / 引理 `monotone_factorial`

English:
lemma monotone_factorial
  statement: Monotone factorial
  proof: fun _ _ => factorial_le

中文:
引理 monotone_factorial
  结论: Monotone factorial
  证明: fun _ _ => factorial_le

Depends on / 依赖: factorial_le
-/
lemma monotone_factorial : Monotone factorial := fun _ _ => factorial_le

variable {α : Type*} (s : Finset α) (f : α -> Nat)

/--
theorem `prod_factorial_pos` / 定理 `prod_factorial_pos`

English:
theorem prod_factorial_pos
  statement: 0 < ∏ i in s, (f i)!
  proof: prod_pos fun _ _ => factorial_pos _

中文:
定理 prod_factorial_pos
  结论: 0 < ∏ i in s, (f i)!
  证明: prod_pos fun _ _ => factorial_pos _

Depends on / 依赖: factorial_pos, prod_pos
-/
theorem prod_factorial_pos : 0 < ∏ i in s, (f i)! := prod_pos fun _ _ => factorial_pos _

/--
theorem `prod_factorial_dvd_factorial_sum` / 定理 `prod_factorial_dvd_factorial_sum`

English:
theorem prod_factorial_dvd_factorial_sum
  statement: (∏ i in s, (f i)!) ∣ (∑ i in s, f i)!
  proof: by
  induction s using Finset.cons_induction_on with
  | empty => simp
  | cons a s has ih =>
    rw [prod_cons]; rw [Finset.sum_cons]
    exact (mul_dvd_mul_left _ ih).trans (Nat.factorial_mul_factorial_dvd_factorial_add _ _)

中文:
定理 prod_factorial_dvd_factorial_sum
  结论: (∏ i in s, (f i)!) ∣ (∑ i in s, f i)!
  证明: by
  induction s using Finset.cons_induction_on with
  | empty => simp
  | cons a s has ih =>
    rw [prod_cons]; rw [Finset.sum_cons]
    exact (mul_dvd_mul_left _ ih).trans (Nat.factorial_mul_factorial_dvd_factorial_add _ _)

Depends on / 依赖: Finset, Finset.cons_induction_on, Finset.sum_cons, Nat.factorial_mul_factorial_dvd_factorial_add, cons_induction_on, factorial_mul_factorial_dvd_factorial_add, mul_dvd_mul_left, prod_cons, sum_cons
-/
theorem prod_factorial_dvd_factorial_sum : (∏ i in s, (f i)!) ∣ (∑ i in s, f i)! := by
  induction s using Finset.cons_induction_on with
  | empty => simp
  | cons a s has ih =>
    rw [prod_cons]; rw [Finset.sum_cons]
    exact (mul_dvd_mul_left _ ih).trans (Nat.factorial_mul_factorial_dvd_factorial_add _ _)

/--
theorem `factorial_eq_prod_range_add_one` / 定理 `factorial_eq_prod_range_add_one`

English:
theorem factorial_eq_prod_range_add_one
  statement: forall n, (n)! = ∏ i in range n, (i + 1)

中文:
定理 factorial_eq_prod_range_add_one
  结论: 对任意 n, (n)! = ∏ i in range n, (i + 1)
-/
theorem factorial_eq_prod_range_add_one : forall n, (n)! = ∏ i in range n, (i + 1)
  | 0 => rfl
  | n + 1 => by rw [factorial, prod_range_succ_comm, factorial_eq_prod_range_add_one n]

@[simp]
/--
theorem `_root_.Finset.prod_range_add_one_eq_factorial` / 定理 `_root_.Finset.prod_range_add_one_eq_factorial`

English:
theorem _root_.Finset.prod_range_add_one_eq_factorial
  given: (n : Nat)
  statement: ∏ i in range n, (i + 1) = (n)!
  proof: .symm factorial_eq_prod_range_add_one _

中文:
定理 _root_.Finset.prod_range_add_one_eq_factorial
  条件: (n : 自然数)
  结论: ∏ i in range n, (i + 1) = (n)!
  证明: .symm factorial_eq_prod_range_add_one _

Depends on / 依赖: factorial_eq_prod_range_add_one
-/
theorem _root_.Finset.prod_range_add_one_eq_factorial (n : Nat) : ∏ i in range n, (i + 1) = (n)! :=
.symm factorial_eq_prod_range_add_one _

/--
theorem `ascFactorial_eq_prod_range` / 定理 `ascFactorial_eq_prod_range`

English:
theorem ascFactorial_eq_prod_range
  given: (n : Nat)
  statement: forall k, n.ascFactorial k = ∏ i in range k, (n + i)

中文:
定理 ascFactorial_eq_prod_range
  条件: (n : 自然数)
  结论: 对任意 k, n.ascFactorial k = ∏ i in range k, (n + i)
-/
theorem ascFactorial_eq_prod_range (n : Nat) : forall k, n.ascFactorial k = ∏ i in range k, (n + i)
  | 0 => rfl
  | k + 1 => by rw [ascFactorial, prod_range_succ_comm, ascFactorial_eq_prod_range n k]

/--
theorem `descFactorial_eq_prod_range` / 定理 `descFactorial_eq_prod_range`

English:
theorem descFactorial_eq_prod_range
  given: (n : Nat)
  statement: forall k, n.descFactorial k = ∏ i in range k, (n - i)

中文:
定理 descFactorial_eq_prod_range
  条件: (n : 自然数)
  结论: 对任意 k, n.descFactorial k = ∏ i in range k, (n - i)
-/
theorem descFactorial_eq_prod_range (n : Nat) : forall k, n.descFactorial k = ∏ i in range k, (n - i)
  | 0 => rfl
  | k + 1 => by rw [descFactorial, prod_range_succ_comm, descFactorial_eq_prod_range n k]

/--
lemma `factorial_coe_dvd_prod` / 引理 `factorial_coe_dvd_prod`

English:
lemma factorial_coe_dvd_prod
  given: (k : Nat) (n : Int)
  statement: (k ! : Int) ∣ ∏ i in range k, (n + i)
  proof: by
  rw [Int.dvd_iff_emod_eq_zero]; rw [Finset.prod_int_mod]
  simp_rw [← Int.emod_add_emod n]
have hn : 0 <= n % k ! := Int.emod_nonneg n Int.natCast_ne_zero.mpr k.factorial_ne_zero
  obtain ⟨x, hx⟩ := Int.eq_ofNat_of_zero_le hn
  have hdivk := x.factorial_dvd_ascFactorial k
  zify [x.ascFactorial_

中文:
引理 factorial_coe_dvd_prod
  条件: (k : 自然数) (n : 整数)
  结论: (k ! : 整数) ∣ ∏ i in range k, (n + i)
  证明: by
  rw [Int.dvd_iff_emod_eq_zero]; rw [Finset.prod_int_mod]
  simp_rw [← Int.emod_add_emod n]
have hn : 0 <= n % k ! := Int.emod_nonneg n Int.natCast_ne_zero.mpr k.factorial_ne_zero
  obtain ⟨x, hx⟩ := Int.eq_ofNat_of_zero_le hn
  have hdivk := x.factorial_dvd_ascFactorial k
  zify [x.ascFactorial_

Depends on / 依赖: Finset, Finset.prod_int_mod, Int.dvd_iff_emod_eq_zero, Int.emod_add_emod, Int.emod_nonneg, Int.eq_ofNat_of_zero_le, Int.natCast_ne_zero.mpr, ascFactorial_eq_prod_range, dvd_iff_emod_eq_zero, emod_add_emod, emod_nonneg, eq_ofNat_of_zero_le, factorial_dvd_ascFactorial, factorial_ne_zero, k.factorial_ne_zero, natCast_ne_zero, prod_int_mod, simp_rw, x.ascFactorial_eq_prod_range, x.factorial_dvd_ascFactorial
-/
lemma factorial_coe_dvd_prod (k : Nat) (n : Int) : (k ! : Int) ∣ ∏ i in range k, (n + i) := by
  rw [Int.dvd_iff_emod_eq_zero]; rw [Finset.prod_int_mod]
  simp_rw [← Int.emod_add_emod n]
have hn : 0 <= n % k ! := Int.emod_nonneg n Int.natCast_ne_zero.mpr k.factorial_ne_zero
  obtain ⟨x, hx⟩ := Int.eq_ofNat_of_zero_le hn
  have hdivk := x.factorial_dvd_ascFactorial k
  zify [x.ascFactorial_eq_prod_range k] at hdivk
  rwa [← Finset.prod_int_mod, ← Int.dvd_iff_emod_eq_zero, hx]

end Nat
