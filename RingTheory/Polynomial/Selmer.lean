/-
Copyright (c) 2022 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
module

public import Mathlib.Analysis.Complex.Polynomial.UnitTrinomial
public import Mathlib.RingTheory.Polynomial.GaussLemma
public import Mathlib.Tactic.LinearCombination

/-!
# Irreducibility of Selmer Polynomials

This file proves irreducibility of the Selmer polynomials `X ^ n - X - 1`.

## Main results

- `X_pow_sub_X_sub_one_irreducible`: The Selmer polynomials `X ^ n - X - 1` are irreducible.

TODO: Show that the Selmer polynomials have full Galois group.
-/

public section


namespace Polynomial

open scoped Polynomial

variable {n : Nat}

/--
theorem `X_pow_sub_X_sub_one_irreducible_aux` / 定理 `X_pow_sub_X_sub_one_irreducible_aux`

English:
theorem X_pow_sub_X_sub_one_irreducible_aux
  given: (z : Complex)
  statement: ¬(z ^ n = z + 1 ∧ z ^ n + z ^ 2 = 0)
  proof: by
  rintro ⟨h1, h2⟩
  replace h3 : z ^ 3 = 1 := by
    linear_combination (1 - z - z ^ 2 - z ^ n) * h1 + (z ^ n - 2) * h2
  have key : z ^ n = 1 ∨ z ^ n = z ∨ z ^ n = z ^ 2 := by
    rw [← Nat.mod_add_div n 3]; rw [pow_add]; rw [pow_mul]; rw [h3]; rw [one_pow]; rw [mul_one]
    have : n % 3 < 3 := 

中文:
定理 X_pow_sub_X_sub_one_irreducible_aux
  条件: (z : Complex)
  结论: ¬(z ^ n = z + 1 ∧ z ^ n + z ^ 2 = 0)
  证明: by
  rintro ⟨h1, h2⟩
  replace h3 : z ^ 3 = 1 := by
    linear_combination (1 - z - z ^ 2 - z ^ n) * h1 + (z ^ n - 2) * h2
  have key : z ^ n = 1 ∨ z ^ n = z ∨ z ^ n = z ^ 2 := by
    rw [← Nat.mod_add_div n 3]; rw [pow_add]; rw [pow_mul]; rw [h3]; rw [one_pow]; rw [mul_one]
    have : n % 3 < 3 := 

Depends on / 依赖: Nat.mod_add_div, Nat.mod_lt, interval_cases, linear_combination, mod_add_div, mod_lt, mul_one, one_pow, or_true, pow_add, pow_mul, pow_one, pow_zero, replace, symm.trans, three_ne_zero, true_or, z_ne_zero, zero_lt_three, zero_ne_one
-/
theorem X_pow_sub_X_sub_one_irreducible_aux (z : Complex) : ¬(z ^ n = z + 1 ∧ z ^ n + z ^ 2 = 0) := by
  rintro ⟨h1, h2⟩
  replace h3 : z ^ 3 = 1 := by
    linear_combination (1 - z - z ^ 2 - z ^ n) * h1 + (z ^ n - 2) * h2
  have key : z ^ n = 1 ∨ z ^ n = z ∨ z ^ n = z ^ 2 := by
    rw [← Nat.mod_add_div n 3]; rw [pow_add]; rw [pow_mul]; rw [h3]; rw [one_pow]; rw [mul_one]
    have : n % 3 < 3 := Nat.mod_lt n zero_lt_three
    interval_cases n % 3 <;>
    simp only [pow_zero, pow_one, or_true, true_or]
  have z_ne_zero : z != 0 := fun h =>
    zero_ne_one ((zero_pow three_ne_zero).symm.trans (show (0 : Complex) ^ 3 = 1 from h ▸ h3))
  rcases key with (key | key | key)
  · exact z_ne_zero (by rwa [key, right_eq_add] at h1)
  · exact one_ne_zero (by rwa [key, left_eq_add] at h1)
  · exact z_ne_zero (eq_zero_of_pow_eq_zero (by rwa [key, add_self_eq_zero] at h2))

/--
theorem `X_pow_sub_X_sub_one_irreducible` / 定理 `X_pow_sub_X_sub_one_irreducible`

English:
theorem X_pow_sub_X_sub_one_irreducible
  given: (hn1 : n != 1)
  statement: Irreducible (X ^ n - X - 1 : Int[X])
  proof: by
  by_cases hn0 : n = 0
  · rw [hn0, pow_zero, sub_sub, add_comm, ← sub_sub, sub_self, zero_sub]
    exact Associated.irreducible ⟨-1, mul_neg_one X⟩ irreducible_X
  have hn : 1 < n := Nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨hn0, hn1⟩
  have hp : (X ^ n - X - 1 : Int[X]) = trinomial 0 1 n (-1) (-1)

中文:
定理 X_pow_sub_X_sub_one_irreducible
  条件: (hn1 : n != 1)
  结论: Irreducible (X ^ n - X - 1 : 整数[X])
  证明: by
  by_cases hn0 : n = 0
  · rw [hn0, pow_zero, sub_sub, add_comm, ← sub_sub, sub_self, zero_sub]
    exact Associated.irreducible ⟨-1, mul_neg_one X⟩ irreducible_X
  have hn : 1 < n := Nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨hn0, hn1⟩
  have hp : (X ^ n - X - 1 : Int[X]) = trinomial 0 1 n (-1) (-1)

Depends on / 依赖: Associated, Associated.irreducible, C_neg, IsUnitTrinomial, IsUnitTrinomial.irreducible_of_coprime, Nat.one_lt_iff_ne_zero_and_ne_one.mpr, X_pow_sub_X_sub_one_irreducible_aux, add_comm, irreducible, irreducible_X, irreducible_of_coprime, mul_neg_one, one_lt_iff_ne_zero_and_ne_one, pow_zero, sub_self, sub_sub, trinomial, zero_lt_one, zero_sub
-/
theorem X_pow_sub_X_sub_one_irreducible (hn1 : n != 1) : Irreducible (X ^ n - X - 1 : Int[X]) := by
  by_cases hn0 : n = 0
  · rw [hn0, pow_zero, sub_sub, add_comm, ← sub_sub, sub_self, zero_sub]
    exact Associated.irreducible ⟨-1, mul_neg_one X⟩ irreducible_X
  have hn : 1 < n := Nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨hn0, hn1⟩
  have hp : (X ^ n - X - 1 : Int[X]) = trinomial 0 1 n (-1) (-1) 1 := by
    simp only [trinomial, C_neg, C_1]; ring
  rw [hp]
  apply IsUnitTrinomial.irreducible_of_coprime' ⟨0, 1, n, zero_lt_one, hn, -1, -1, 1, rfl⟩
  rintro z ⟨h1, h2⟩
  apply X_pow_sub_X_sub_one_irreducible_aux (n := n) z
  rw [trinomial_mirror zero_lt_one hn (-1 : Intˣ).ne_zero (1 : Intˣ).ne_zero] at h2
  simp_rw [trinomial, aeval_add, aeval_mul, aeval_X_pow, aeval_C,
    Units.val_neg, Units.val_one, map_neg, map_one] at h1 h2
  replace h1 : z ^ n = z + 1 := by linear_combination h1
  replace h2 := mul_eq_zero_of_left h2 z
  rw [add_mul]; rw [add_mul]; rw [add_zero]; rw [mul_assoc (-1 : Complex)]; rw [← pow_succ]; rw [Nat.sub_add_cancel hn.le] at h2
  rw [h1] at h2 ⊢
  exact ⟨rfl, by linear_combination -h2⟩

/--
theorem `X_pow_sub_X_sub_one_irreducible_rat` / 定理 `X_pow_sub_X_sub_one_irreducible_rat`

English:
theorem X_pow_sub_X_sub_one_irreducible_rat
  given: (hn1 : n != 1)
  statement: Irreducible (X ^ n - X - 1 : Rat[X])
  proof: by
  by_cases hn0 : n = 0
  · rw [hn0, pow_zero, sub_sub, add_comm, ← sub_sub, sub_self, zero_sub]
    exact Associated.irreducible ⟨-1, mul_neg_one X⟩ irreducible_X
  have hp : (X ^ n - X - 1 : Int[X]) = trinomial 0 1 n (-1) (-1) 1 := by
    simp only [trinomial, C_neg, C_1]; ring
  have hn : 1 < n

中文:
定理 X_pow_sub_X_sub_one_irreducible_rat
  条件: (hn1 : n != 1)
  结论: Irreducible (X ^ n - X - 1 : Rat[X])
  证明: by
  by_cases hn0 : n = 0
  · rw [hn0, pow_zero, sub_sub, add_comm, ← sub_sub, sub_self, zero_sub]
    exact Associated.irreducible ⟨-1, mul_neg_one X⟩ irreducible_X
  have hp : (X ^ n - X - 1 : Int[X]) = trinomial 0 1 n (-1) (-1) 1 := by
    simp only [trinomial, C_neg, C_1]; ring
  have hn : 1 < n

Depends on / 依赖: Associated, Associated.irreducible, C_neg, IsPrimitive, IsPrimitive.Int.irreducible_iff_irreducible_map_cast, Nat.one_lt_iff_ne_zero_and_ne_one.mpr, Polynom, Polynomial, Polynomial.map_sub, X_pow_sub_X_sub_one_irreducible, add_comm, irreducible, irreducible_X, irreducible_iff_irreducible_map_cast, map_sub, mul_neg_one, one_lt_iff_ne_zero_and_ne_one, pow_zero, sub_self, sub_sub
-/
theorem X_pow_sub_X_sub_one_irreducible_rat (hn1 : n != 1) : Irreducible (X ^ n - X - 1 : Rat[X]) := by
  by_cases hn0 : n = 0
  · rw [hn0, pow_zero, sub_sub, add_comm, ← sub_sub, sub_self, zero_sub]
    exact Associated.irreducible ⟨-1, mul_neg_one X⟩ irreducible_X
  have hp : (X ^ n - X - 1 : Int[X]) = trinomial 0 1 n (-1) (-1) 1 := by
    simp only [trinomial, C_neg, C_1]; ring
  have hn : 1 < n := Nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨hn0, hn1⟩
  have h := (IsPrimitive.Int.irreducible_iff_irreducible_map_cast ?_).mp
    (X_pow_sub_X_sub_one_irreducible hn1)
  · rwa [Polynomial.map_sub, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_one,
      Polynomial.map_X] at h
  · exact hp.symm ▸ (trinomial_monic zero_lt_one hn).isPrimitive

end Polynomial
