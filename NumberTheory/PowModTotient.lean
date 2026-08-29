/-
Copyright (c) 2025 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module

public import Mathlib.FieldTheory.Finite.Basic

/-!
# Modular exponentiation with the totient function

This file contains lemmas about modular exponentiation.
In particular, it contains lemmas showing that an exponent can be reduced modulo the totient
function when the base is coprime to the modulus.

## Main Results

* `pow_totient_mod`: If `x` is coprime to `n`, then the modular exponentiation
  `x ^ k % n` can be reduced to `x ^ (k % φ n) % n`.

## TODOs

- Extend to results in cases where the base is not coprime to the modulus.
- Write a tactic or simproc that can automatically reduce exponents
  or towers of exponents using these results.

-/

public section

namespace Nat

/--
lemma `pow_totient_mod_eq_one` / 引理 `pow_totient_mod_eq_one`

English:
lemma pow_totient_mod_eq_one
  given: {x n : Nat} (hn : 1 < n) (h : x.Coprime n)
  proof: by
  exact mod_eq_of_modEq (ModEq.pow_totient h) hn

中文:
引理 pow_totient_mod_eq_one
  条件: {x n : 自然数} (hn : 1 < n) (h : x.Coprime n)
  证明: by
  exact mod_eq_of_modEq (ModEq.pow_totient h) hn

Depends on / 依赖: ModEq.pow_totient, mod_eq_of_modEq, pow_totient
-/
lemma pow_totient_mod_eq_one {x n : Nat} (hn : 1 < n) (h : x.Coprime n) :
    (x ^ φ n) % n = 1 := by
  exact mod_eq_of_modEq (ModEq.pow_totient h) hn

/--
lemma `pow_add_totient_mod_eq` / 引理 `pow_add_totient_mod_eq`

English:
lemma pow_add_totient_mod_eq
  given: {x k n : Nat} (hn : 1 < n) (h : x.Coprime n)
  proof: by
  rw [pow_add]; rw [mul_mod]; rw [pow_totient_mod_eq_one hn h]
  simp only [mul_one, dvd_refl, mod_mod_of_dvd]

中文:
引理 pow_add_totient_mod_eq
  条件: {x k n : 自然数} (hn : 1 < n) (h : x.Coprime n)
  证明: by
  rw [pow_add]; rw [mul_mod]; rw [pow_totient_mod_eq_one hn h]
  simp only [mul_one, dvd_refl, mod_mod_of_dvd]

Depends on / 依赖: dvd_refl, mod_mod_of_dvd, mul_mod, mul_one, pow_add, pow_totient_mod_eq_one
-/
lemma pow_add_totient_mod_eq {x k n : Nat} (hn : 1 < n) (h : x.Coprime n) :
    (x ^ (k + φ n)) % n = (x ^ k) % n := by
  rw [pow_add]; rw [mul_mod]; rw [pow_totient_mod_eq_one hn h]
  simp only [mul_one, dvd_refl, mod_mod_of_dvd]

/--
lemma `pow_add_mul_totient_mod_eq` / 引理 `pow_add_mul_totient_mod_eq`

English:
lemma pow_add_mul_totient_mod_eq
  given: {x k l n : Nat} (hn : 1 < n) (h : x.Coprime n)
  proof: by
  induction l with
  | zero => simp
  | succ l ih =>
    rw [add_mul]; rw [one_mul]; rw [← add_assoc]; rw [pow_add_totient_mod_eq hn h]; rw [ih]

中文:
引理 pow_add_mul_totient_mod_eq
  条件: {x k l n : 自然数} (hn : 1 < n) (h : x.Coprime n)
  证明: by
  induction l with
  | zero => simp
  | succ l ih =>
    rw [add_mul]; rw [one_mul]; rw [← add_assoc]; rw [pow_add_totient_mod_eq hn h]; rw [ih]

Depends on / 依赖: add_assoc, add_mul, one_mul, pow_add_totient_mod_eq
-/
lemma pow_add_mul_totient_mod_eq {x k l n : Nat} (hn : 1 < n) (h : x.Coprime n) :
    (x ^ (k + l * φ n)) % n = (x ^ k) % n := by
  induction l with
  | zero => simp
  | succ l ih =>
    rw [add_mul]; rw [one_mul]; rw [← add_assoc]; rw [pow_add_totient_mod_eq hn h]; rw [ih]

/--
lemma `pow_totient_mod` / 引理 `pow_totient_mod`

English:
lemma pow_totient_mod
  given: {x k n : Nat} (hn : 1 < n) (h : x.Coprime n)
  proof: by
  rw [← div_add_mod' k (φ n)]; rw [add_comm]; rw [pow_add_mul_totient_mod_eq hn h]; rw [add_mul_mod_self_right]; rw [mod_mod k (φ n)]

中文:
引理 pow_totient_mod
  条件: {x k n : 自然数} (hn : 1 < n) (h : x.Coprime n)
  证明: by
  rw [← div_add_mod' k (φ n)]; rw [add_comm]; rw [pow_add_mul_totient_mod_eq hn h]; rw [add_mul_mod_self_right]; rw [mod_mod k (φ n)]

Depends on / 依赖: add_comm, add_mul_mod_self_right, div_add_mod, mod_mod, pow_add_mul_totient_mod_eq
-/
lemma pow_totient_mod {x k n : Nat} (hn : 1 < n) (h : x.Coprime n) :
    x ^ k % n = x ^ (k % φ n) % n := by
  rw [← div_add_mod' k (φ n)]; rw [add_comm]; rw [pow_add_mul_totient_mod_eq hn h]; rw [add_mul_mod_self_right]; rw [mod_mod k (φ n)]

end Nat
