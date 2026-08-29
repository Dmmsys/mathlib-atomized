/-
Copyright (c) 2022 Julian Kuelshammer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julian Kuelshammer
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Finset.NatAntidiagonal
public import Mathlib.Data.Nat.Choose.Central

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Tactic.Field

/-!
# Catalan numbers

The Catalan numbers (http://oeis.org/A000108) are probably the most ubiquitous sequence of integers
in mathematics. They enumerate several important objects like binary trees, Dyck paths, and
triangulations of convex polygons.

## Main definitions

* `catalan n`: the `n`th Catalan number, defined recursively as
  `catalan (n + 1) = ∑ i : Fin n.succ, catalan i * catalan (n - i)`.

## Main results

* `catalan_eq_centralBinom_div`: The explicit formula for the Catalan number using the central
  binomial coefficient, `catalan n = Nat.centralBinom n / (n + 1)`.

## Implementation details

The proof of `catalan_eq_centralBinom_div` follows https://math.stackexchange.com/questions/3304415

## TODO

* Prove that the Catalan numbers enumerate many interesting objects.
* Provide the many variants of Catalan numbers, e.g. associated to complex reflection groups,
  Fuss-Catalan, etc.

-/

@[expose] public section


open Finset

/--
Definition of `catalan` / `catalan` 的定义

English:
definition catalan
  signature: : Nat -> Nat

中文:
定义 catalan
  签名: : 自然数 -> 自然数
-/
def catalan : Nat -> Nat
  | 0 => 1
  | n + 1 =>
    ∑ i : Fin n.succ,
      catalan i * catalan (n - i)

@[simp]
/--
theorem `catalan_zero` / 定理 `catalan_zero`

English:
theorem catalan_zero
  statement: catalan 0 = 1
  proof: by rw [catalan]

中文:
定理 catalan_zero
  结论: catalan 0 = 1
  证明: by rw [catalan]

Depends on / 依赖: catalan
-/
theorem catalan_zero : catalan 0 = 1 := by rw [catalan]

/--
theorem `catalan_succ` / 定理 `catalan_succ`

English:
theorem catalan_succ
  given: (n : Nat)
  statement: catalan (n + 1) = ∑ i : Fin n.succ, catalan i * catalan (n - i)
  proof: by
  rw [catalan]

中文:
定理 catalan_succ
  条件: (n : 自然数)
  结论: catalan (n + 1) = ∑ i : Fin n.succ, catalan i * catalan (n - i)
  证明: by
  rw [catalan]

Depends on / 依赖: catalan
-/
theorem catalan_succ (n : Nat) : catalan (n + 1) = ∑ i : Fin n.succ, catalan i * catalan (n - i) := by
  rw [catalan]

/--
theorem `catalan_succ'` / 定理 `catalan_succ'`

English:
theorem catalan_succ'
  given: (n : Nat)
  proof: by
  rw [catalan_succ]; rw [Nat.sum_antidiagonal_eq_sum_range_succ (fun x y => catalan x * catalan y) n]; rw [sum_range]

@[simp]

中文:
定理 catalan_succ'
  条件: (n : 自然数)
  证明: by
  rw [catalan_succ]; rw [Nat.sum_antidiagonal_eq_sum_range_succ (fun x y => catalan x * catalan y) n]; rw [sum_range]

@[simp]

Depends on / 依赖: Nat.sum_antidiagonal_eq_sum_range_succ, catalan, catalan_succ, sum_antidiagonal_eq_sum_range_succ, sum_range
-/
theorem catalan_succ' (n : Nat) :
    catalan (n + 1) = ∑ ij in antidiagonal n, catalan ij.1 * catalan ij.2 := by
  rw [catalan_succ]; rw [Nat.sum_antidiagonal_eq_sum_range_succ (fun x y => catalan x * catalan y) n]; rw [sum_range]

@[simp]
/--
theorem `catalan_one` / 定理 `catalan_one`

English:
theorem catalan_one
  statement: catalan 1 = 1
  proof: by simp [catalan_succ]

中文:
定理 catalan_one
  结论: catalan 1 = 1
  证明: by simp [catalan_succ]

Depends on / 依赖: catalan_succ
-/
theorem catalan_one : catalan 1 = 1 := by simp [catalan_succ]

/--
Definition of `gosperCatalan` / `gosperCatalan` 的定义

English:
definition gosperCatalan
  signature: (n j : Nat)
  body: Nat.centralBinom j * Nat.centralBinom (n - j) * (2 * j - n) / (2 * n * (n + 1))

中文:
定义 gosperCatalan
  签名: (n j : 自然数)
  定义体: Nat.centralBinom j * Nat.centralBinom (n - j) * (2 * j - n) / (2 * n * (n + 1))
-/
private def gosperCatalan (n j : Nat) : Rat :=
  Nat.centralBinom j * Nat.centralBinom (n - j) * (2 * j - n) / (2 * n * (n + 1))

/--
theorem `gosper_trick` / 定理 `gosper_trick`

English:
theorem gosper_trick
  given: {n i : Nat} (h : i <= n)
  proof: by
  have l₁ : (i : Rat) + 1 != 0 := by norm_cast
  have l₂ : (n : Rat) - i + 1 != 0 := by norm_cast
  have h₁ := (mul_div_cancel_left₀ (↑(Nat.centralBinom (i + 1))) l₁).symm
  have h₂ := (mul_div_cancel_left₀ (↑(Nat.centralBinom (n - i + 1))) l₂).symm
  have h₃ : ((i : Rat) + 1) * (i + 1).centralBi

中文:
定理 gosper_trick
  条件: {n i : 自然数} (h : i <= n)
  证明: by
  have l₁ : (i : Rat) + 1 != 0 := by norm_cast
  have l₂ : (n : Rat) - i + 1 != 0 := by norm_cast
  have h₁ := (mul_div_cancel_left₀ (↑(Nat.centralBinom (i + 1))) l₁).symm
  have h₂ := (mul_div_cancel_left₀ (↑(Nat.centralBinom (n - i + 1))) l₂).symm
  have h₃ : ((i : Rat) + 1) * (i + 1).centralBi
-/
private theorem gosper_trick {n i : Nat} (h : i <= n) :
    gosperCatalan (n + 1) (i + 1) - gosperCatalan (n + 1) i =
      Nat.centralBinom i / (i + 1) * Nat.centralBinom (n - i) / (n - i + 1) := by
  have l₁ : (i : Rat) + 1 != 0 := by norm_cast
  have l₂ : (n : Rat) - i + 1 != 0 := by norm_cast
  have h₁ := (mul_div_cancel_left₀ (↑(Nat.centralBinom (i + 1))) l₁).symm
  have h₂ := (mul_div_cancel_left₀ (↑(Nat.centralBinom (n - i + 1))) l₂).symm
  have h₃ : ((i : Rat) + 1) * (i + 1).centralBinom = 2 * (2 * i + 1) * i.centralBinom :=
    mod_cast Nat.succ_mul_centralBinom_succ i
  have h₄ :
    ((n : Rat) - i + 1) * (n - i + 1).centralBinom = 2 * (2 * (n - i) + 1) * (n - i).centralBinom :=
      mod_cast Nat.succ_mul_centralBinom_succ (n - i)
  simp only [gosperCatalan]
  push_cast
  rw [show n + 1 - i = n - i + 1 by rw [Nat.add_comm (n - i) 1]; rw [← (Nat.add_sub_assoc h 1)]; rw [add_comm]]
  rw [h₁]; rw [h₂]; rw [h₃]; rw [h₄]
  field

/--
theorem `gosper_catalan_sub_eq_central_binom_div` / 定理 `gosper_catalan_sub_eq_central_binom_div`

English:
theorem gosper_catalan_sub_eq_central_binom_div
  given: (n : Nat)
  statement: gosperCatalan (n + 1) (n + 1) -
  proof: by
  simp only [gosperCatalan, tsub_self, Nat.centralBinom_zero, Nat.cast_one, mul_one, Nat.cast_add,
    Nat.sub_zero, one_mul, Nat.cast_zero, mul_zero, zero_sub, neg_add_rev]
  field

中文:
定理 gosper_catalan_sub_eq_central_binom_div
  条件: (n : 自然数)
  结论: gosperCatalan (n + 1) (n + 1) -
  证明: by
  simp only [gosperCatalan, tsub_self, Nat.centralBinom_zero, Nat.cast_one, mul_one, Nat.cast_add,
    Nat.sub_zero, one_mul, Nat.cast_zero, mul_zero, zero_sub, neg_add_rev]
  field
-/
private theorem gosper_catalan_sub_eq_central_binom_div (n : Nat) : gosperCatalan (n + 1) (n + 1) -
    gosperCatalan (n + 1) 0 = Nat.centralBinom (n + 1) / (n + 2) := by
  simp only [gosperCatalan, tsub_self, Nat.centralBinom_zero, Nat.cast_one, mul_one, Nat.cast_add,
    Nat.sub_zero, one_mul, Nat.cast_zero, mul_zero, zero_sub, neg_add_rev]
  field

/--
theorem `catalan_eq_centralBinom_div` / 定理 `catalan_eq_centralBinom_div`

English:
theorem catalan_eq_centralBinom_div
  given: (n : Nat)
  statement: catalan n = n.centralBinom / (n + 1)
  proof: by
  suffices (catalan n : Rat) = Nat.centralBinom n / (n + 1) by
    have h := Nat.succ_dvd_centralBinom n
    exact mod_cast this
  induction n using Nat.caseStrongRecOn with
  | zero => simp
  | ind d hd =>
    simp_rw [catalan_succ, Nat.cast_sum, Nat.cast_mul]
    trans (∑ i : Fin d.succ, Nat.ce

中文:
定理 catalan_eq_centralBinom_div
  条件: (n : 自然数)
  结论: catalan n = n.centralBinom / (n + 1)
  证明: by
  suffices (catalan n : Rat) = Nat.centralBinom n / (n + 1) by
    have h := Nat.succ_dvd_centralBinom n
    exact mod_cast this
  induction n using Nat.caseStrongRecOn with
  | zero => simp
  | ind d hd =>
    simp_rw [catalan_succ, Nat.cast_sum, Nat.cast_mul]
    trans (∑ i : Fin d.succ, Nat.ce

Depends on / 依赖: Nat.caseStrongRecOn, Nat.cast_mul, Nat.cast_sum, Nat.centralBinom, Nat.succ_dvd_centralBinom, caseStrongRecOn, cast_mul, cast_sum, catalan, catalan_succ, centralBinom, d.succ, d_minus_x_le_d, m_le_d, mod_cast, simp_rw, succ_dvd_centralBinom, tsub_le_self, x.val
-/
theorem catalan_eq_centralBinom_div (n : Nat) : catalan n = n.centralBinom / (n + 1) := by
  suffices (catalan n : Rat) = Nat.centralBinom n / (n + 1) by
    have h := Nat.succ_dvd_centralBinom n
    exact mod_cast this
  induction n using Nat.caseStrongRecOn with
  | zero => simp
  | ind d hd =>
    simp_rw [catalan_succ, Nat.cast_sum, Nat.cast_mul]
    trans (∑ i : Fin d.succ, Nat.centralBinom i / (i + 1) *
                            (Nat.centralBinom (d - i) / (d - i + 1)) : Rat)
    · congr
      ext1 x
      have m_le_d : x.val <= d := by lia
      have d_minus_x_le_d : (d - x.val) <= d := tsub_le_self
      rw [hd _ m_le_d]; rw [hd _ d_minus_x_le_d]
      norm_cast
    · trans (∑ i : Fin d.succ, (gosperCatalan (d + 1) (i + 1) - gosperCatalan (d + 1) i))
      · refine sum_congr rfl fun i _ => ?_
        rw [gosper_trick i.is_le]; rw [mul_div]
      · rw [← sum_range fun i => gosperCatalan (d + 1) (i + 1) - gosperCatalan (d + 1) i,
            sum_range_sub, Nat.succ_eq_add_one]
        rw [gosper_catalan_sub_eq_central_binom_div d]
        norm_cast

/--
theorem `succ_mul_catalan_eq_centralBinom` / 定理 `succ_mul_catalan_eq_centralBinom`

English:
theorem succ_mul_catalan_eq_centralBinom
  given: (n : Nat)
  statement: (n + 1) * catalan n = n.centralBinom
  proof: (Nat.eq_mul_of_div_eq_right n.succ_dvd_centralBinom (catalan_eq_centralBinom_div n).symm).symm

中文:
定理 succ_mul_catalan_eq_centralBinom
  条件: (n : 自然数)
  结论: (n + 1) * catalan n = n.centralBinom
  证明: (Nat.eq_mul_of_div_eq_right n.succ_dvd_centralBinom (catalan_eq_centralBinom_div n).symm).symm

Depends on / 依赖: Nat.eq_mul_of_div_eq_right, catalan_eq_centralBinom_div, eq_mul_of_div_eq_right, n.succ_dvd_centralBinom, succ_dvd_centralBinom
-/
theorem succ_mul_catalan_eq_centralBinom (n : Nat) : (n + 1) * catalan n = n.centralBinom :=
  (Nat.eq_mul_of_div_eq_right n.succ_dvd_centralBinom (catalan_eq_centralBinom_div n).symm).symm

/--
theorem `catalan_two` / 定理 `catalan_two`

English:
theorem catalan_two
  statement: catalan 2 = 2
  proof: by
  norm_num [catalan_eq_centralBinom_div, Nat.centralBinom, Nat.choose]

中文:
定理 catalan_two
  结论: catalan 2 = 2
  证明: by
  norm_num [catalan_eq_centralBinom_div, Nat.centralBinom, Nat.choose]

Depends on / 依赖: Nat.centralBinom, Nat.choose, catalan_eq_centralBinom_div, centralBinom
-/
theorem catalan_two : catalan 2 = 2 := by
  norm_num [catalan_eq_centralBinom_div, Nat.centralBinom, Nat.choose]

/--
theorem `catalan_three` / 定理 `catalan_three`

English:
theorem catalan_three
  statement: catalan 3 = 5
  proof: by
  norm_num [catalan_eq_centralBinom_div, Nat.centralBinom, Nat.choose]

中文:
定理 catalan_three
  结论: catalan 3 = 5
  证明: by
  norm_num [catalan_eq_centralBinom_div, Nat.centralBinom, Nat.choose]

Depends on / 依赖: Nat.centralBinom, Nat.choose, catalan_eq_centralBinom_div, centralBinom
-/
theorem catalan_three : catalan 3 = 5 := by
  norm_num [catalan_eq_centralBinom_div, Nat.centralBinom, Nat.choose]
