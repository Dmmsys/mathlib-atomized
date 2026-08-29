/-
Copyright (c) 2023 Luke Mantle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Mantle
-/
module

public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Data.Nat.Factorial.DoubleFactorial

/-!
# Hermite polynomials

This file defines `Polynomial.hermite n`, the `n`th probabilists' Hermite polynomial.

## Main definitions

* `Polynomial.hermite n`: the `n`th probabilists' Hermite polynomial,
  defined recursively as a `Polynomial ℤ`

## Results

* `Polynomial.hermite_succ`: the recursion `hermite (n+1) = (x - d/dx) (hermite n)`
* `Polynomial.coeff_hermite_explicit`: a closed formula for (nonvanishing) coefficients in terms
  of binomial coefficients and double factorials.
* `Polynomial.coeff_hermite_of_odd_add`: for `n`,`k` where `n+k` is odd, `(hermite n).coeff k` is
  zero.
* `Polynomial.coeff_hermite_of_even_add`: a closed formula for `(hermite n).coeff k` when `n+k` is
  even, equivalent to `Polynomial.coeff_hermite_explicit`.
* `Polynomial.monic_hermite`: for all `n`, `hermite n` is monic.
* `Polynomial.degree_hermite`: for all `n`, `hermite n` has degree `n`.

## References

* [Hermite Polynomials](https://en.wikipedia.org/wiki/Hermite_polynomials)

-/

@[expose] public section

noncomputable section

open Polynomial

namespace Polynomial

/--
Definition of `hermite` / `hermite` 的定义

English:
definition hermite
  signature: : Nat -> Polynomial Int

中文:
定义 hermite
  签名: : 自然数 -> Polynomial 整数
-/
noncomputable def hermite : Nat -> Polynomial Int
  | 0 => 1
  | n + 1 => X * hermite n - derivative (hermite n)

/-- The recursion `hermite (n+1) = (x - d/dx) (hermite n)` -/
@[simp]
/--
theorem `hermite_succ` / 定理 `hermite_succ`

English:
theorem hermite_succ
  given: (n : Nat)
  statement: hermite (n + 1) = X * hermite n - derivative (hermite n)
  proof: by
  rw [hermite]

中文:
定理 hermite_succ
  条件: (n : 自然数)
  结论: hermite (n + 1) = X * hermite n - derivative (hermite n)
  证明: by
  rw [hermite]

Depends on / 依赖: hermite
-/
theorem hermite_succ (n : Nat) : hermite (n + 1) = X * hermite n - derivative (hermite n) := by
  rw [hermite]

/--
theorem `hermite_eq_iterate` / 定理 `hermite_eq_iterate`

English:
theorem hermite_eq_iterate
  given: (n : Nat)
  statement: hermite n = (fun p => X * p - derivative p)^[n] 1
  proof: by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ← ih, hermite_succ]

@[simp]

中文:
定理 hermite_eq_iterate
  条件: (n : 自然数)
  结论: hermite n = (fun p => X * p - derivative p)^[n] 1
  证明: by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ← ih, hermite_succ]

@[simp]

Depends on / 依赖: Function, Function.iterate_succ_apply, hermite_succ, iterate_succ_apply
-/
theorem hermite_eq_iterate (n : Nat) : hermite n = (fun p => X * p - derivative p)^[n] 1 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ← ih, hermite_succ]

@[simp]
/--
theorem `hermite_zero` / 定理 `hermite_zero`

English:
theorem hermite_zero
  statement: hermite 0 = C 1
  proof: rfl

中文:
定理 hermite_zero
  结论: hermite 0 = C 1
  证明: rfl
-/
theorem hermite_zero : hermite 0 = C 1 :=
  rfl

/--
theorem `hermite_one` / 定理 `hermite_one`

English:
theorem hermite_one
  statement: hermite 1 = X
  proof: by
  rw [hermite_succ]; rw [hermite_zero]
  simp only [map_one, mul_one, derivative_one, sub_zero]

中文:
定理 hermite_one
  结论: hermite 1 = X
  证明: by
  rw [hermite_succ]; rw [hermite_zero]
  simp only [map_one, mul_one, derivative_one, sub_zero]

Depends on / 依赖: derivative_one, hermite_succ, hermite_zero, map_one, mul_one, sub_zero
-/
theorem hermite_one : hermite 1 = X := by
  rw [hermite_succ]; rw [hermite_zero]
  simp only [map_one, mul_one, derivative_one, sub_zero]

/-! ### Lemmas about `Polynomial.coeff` -/


section coeff

/--
theorem `coeff_hermite_succ_zero` / 定理 `coeff_hermite_succ_zero`

English:
theorem coeff_hermite_succ_zero
  given: (n : Nat)
  statement: coeff (hermite (n + 1)) 0 = -coeff (hermite n) 1
  proof: by
  simp [coeff_derivative]

中文:
定理 coeff_hermite_succ_zero
  条件: (n : 自然数)
  结论: coeff (hermite (n + 1)) 0 = -coeff (hermite n) 1
  证明: by
  simp [coeff_derivative]

Depends on / 依赖: coeff_derivative
-/
theorem coeff_hermite_succ_zero (n : Nat) : coeff (hermite (n + 1)) 0 = -coeff (hermite n) 1 := by
  simp [coeff_derivative]

/--
theorem `coeff_hermite_succ_succ` / 定理 `coeff_hermite_succ_succ`

English:
theorem coeff_hermite_succ_succ
  given: (n k : Nat)
  statement: coeff (hermite (n + 1)) (k + 1) =
  proof: by
  rw [hermite_succ]; rw [coeff_sub]; rw [coeff_X_mul]; rw [coeff_derivative]; rw [mul_comm]
  norm_cast

中文:
定理 coeff_hermite_succ_succ
  条件: (n k : 自然数)
  结论: coeff (hermite (n + 1)) (k + 1) =
  证明: by
  rw [hermite_succ]; rw [coeff_sub]; rw [coeff_X_mul]; rw [coeff_derivative]; rw [mul_comm]
  norm_cast

Depends on / 依赖: coeff_X_mul, coeff_derivative, coeff_sub, hermite_succ, mul_comm
-/
theorem coeff_hermite_succ_succ (n k : Nat) : coeff (hermite (n + 1)) (k + 1) =
    coeff (hermite n) k - (k + 2) * coeff (hermite n) (k + 2) := by
  rw [hermite_succ]; rw [coeff_sub]; rw [coeff_X_mul]; rw [coeff_derivative]; rw [mul_comm]
  norm_cast

/--
theorem `coeff_hermite_of_lt` / 定理 `coeff_hermite_of_lt`

English:
theorem coeff_hermite_of_lt
  given: {n k : Nat} (hnk : n < k)
  statement: coeff (hermite n) k = 0
  proof: by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hnk
  clear hnk
  induction n generalizing k with
  | zero => exact coeff_C
  | succ n ih =>
    have : n + k + 1 + 2 = n + (k + 2) + 1 := by ring
    rw [coeff_hermite_succ_succ]; rw [add_right_comm]; rw [this]; rw [ih k]; rw [ih (k + 2)]; rw [mul_zer

中文:
定理 coeff_hermite_of_lt
  条件: {n k : 自然数} (hnk : n < k)
  结论: coeff (hermite n) k = 0
  证明: by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hnk
  clear hnk
  induction n generalizing k with
  | zero => exact coeff_C
  | succ n ih =>
    have : n + k + 1 + 2 = n + (k + 2) + 1 := by ring
    rw [coeff_hermite_succ_succ]; rw [add_right_comm]; rw [this]; rw [ih k]; rw [ih (k + 2)]; rw [mul_zer

Depends on / 依赖: Nat.exists_eq_add_of_lt, add_right_comm, coeff_C, coeff_hermite_succ_succ, exists_eq_add_of_lt, generalizing, mul_zero, sub_zero
-/
theorem coeff_hermite_of_lt {n k : Nat} (hnk : n < k) : coeff (hermite n) k = 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hnk
  clear hnk
  induction n generalizing k with
  | zero => exact coeff_C
  | succ n ih =>
    have : n + k + 1 + 2 = n + (k + 2) + 1 := by ring
    rw [coeff_hermite_succ_succ]; rw [add_right_comm]; rw [this]; rw [ih k]; rw [ih (k + 2)]; rw [mul_zero]; rw [sub_zero]

@[simp]
/--
theorem `coeff_hermite_self` / 定理 `coeff_hermite_self`

English:
theorem coeff_hermite_self
  given: (n : Nat)
  statement: coeff (hermite n) n = 1
  proof: by
  induction n with
  | zero => exact coeff_C
  | succ n ih =>
    rw [coeff_hermite_succ_succ]; rw [ih]; rw [coeff_hermite_of_lt]; rw [mul_zero]; rw [sub_zero]
    simp

@[simp]

中文:
定理 coeff_hermite_self
  条件: (n : 自然数)
  结论: coeff (hermite n) n = 1
  证明: by
  induction n with
  | zero => exact coeff_C
  | succ n ih =>
    rw [coeff_hermite_succ_succ]; rw [ih]; rw [coeff_hermite_of_lt]; rw [mul_zero]; rw [sub_zero]
    simp

@[simp]

Depends on / 依赖: coeff_C, coeff_hermite_of_lt, coeff_hermite_succ_succ, mul_zero, sub_zero
-/
theorem coeff_hermite_self (n : Nat) : coeff (hermite n) n = 1 := by
  induction n with
  | zero => exact coeff_C
  | succ n ih =>
    rw [coeff_hermite_succ_succ]; rw [ih]; rw [coeff_hermite_of_lt]; rw [mul_zero]; rw [sub_zero]
    simp

@[simp]
/--
theorem `degree_hermite` / 定理 `degree_hermite`

English:
theorem degree_hermite
  given: (n : Nat)
  statement: (hermite n).degree = n
  proof: by
  rw [degree_eq_of_le_of_coeff_ne_zero]
  · simp_rw [degree_le_iff_coeff_zero, Nat.cast_lt]
    rintro m hnm
    exact coeff_hermite_of_lt hnm
  · simp [coeff_hermite_self n]

@[simp]

中文:
定理 degree_hermite
  条件: (n : 自然数)
  结论: (hermite n).degree = n
  证明: by
  rw [degree_eq_of_le_of_coeff_ne_zero]
  · simp_rw [degree_le_iff_coeff_zero, Nat.cast_lt]
    rintro m hnm
    exact coeff_hermite_of_lt hnm
  · simp [coeff_hermite_self n]

@[simp]

Depends on / 依赖: Nat.cast_lt, cast_lt, coeff_hermite_of_lt, coeff_hermite_self, degree_eq_of_le_of_coeff_ne_zero, degree_le_iff_coeff_zero, simp_rw
-/
theorem degree_hermite (n : Nat) : (hermite n).degree = n := by
  rw [degree_eq_of_le_of_coeff_ne_zero]
  · simp_rw [degree_le_iff_coeff_zero, Nat.cast_lt]
    rintro m hnm
    exact coeff_hermite_of_lt hnm
  · simp [coeff_hermite_self n]

@[simp]
/--
theorem `natDegree_hermite` / 定理 `natDegree_hermite`

English:
theorem natDegree_hermite
  given: {n : Nat}
  statement: (hermite n).natDegree = n
  proof: natDegree_eq_of_degree_eq_some (degree_hermite n)

@[simp]

中文:
定理 natDegree_hermite
  条件: {n : 自然数}
  结论: (hermite n).natDegree = n
  证明: natDegree_eq_of_degree_eq_some (degree_hermite n)

@[simp]

Depends on / 依赖: degree_hermite, natDegree_eq_of_degree_eq_some
-/
theorem natDegree_hermite {n : Nat} : (hermite n).natDegree = n :=
  natDegree_eq_of_degree_eq_some (degree_hermite n)

@[simp]
/--
theorem `leadingCoeff_hermite` / 定理 `leadingCoeff_hermite`

English:
theorem leadingCoeff_hermite
  given: (n : Nat)
  statement: (hermite n).leadingCoeff = 1
  proof: by
  rw [← coeff_natDegree]; rw [natDegree_hermite]; rw [coeff_hermite_self]

中文:
定理 leadingCoeff_hermite
  条件: (n : 自然数)
  结论: (hermite n).leadingCoeff = 1
  证明: by
  rw [← coeff_natDegree]; rw [natDegree_hermite]; rw [coeff_hermite_self]

Depends on / 依赖: coeff_hermite_self, coeff_natDegree, natDegree_hermite
-/
theorem leadingCoeff_hermite (n : Nat) : (hermite n).leadingCoeff = 1 := by
  rw [← coeff_natDegree]; rw [natDegree_hermite]; rw [coeff_hermite_self]

/--
theorem `hermite_monic` / 定理 `hermite_monic`

English:
theorem hermite_monic
  given: (n : Nat)
  statement: (hermite n).Monic
  proof: leadingCoeff_hermite n

中文:
定理 hermite_monic
  条件: (n : 自然数)
  结论: (hermite n).Monic
  证明: leadingCoeff_hermite n

Depends on / 依赖: leadingCoeff_hermite
-/
theorem hermite_monic (n : Nat) : (hermite n).Monic :=
  leadingCoeff_hermite n

/--
theorem `coeff_hermite_of_odd_add` / 定理 `coeff_hermite_of_odd_add`

English:
theorem coeff_hermite_of_odd_add
  given: {n k : Nat} (hnk : Odd (n + k))
  statement: coeff (hermite n) k = 0
  proof: by
  induction n generalizing k with
  | zero =>
    rw [zero_add k] at hnk
    exact coeff_hermite_of_lt hnk.pos
  | succ n ih =>
    cases k with
    | zero =>
      rw [Nat.succ_add_eq_add_succ] at hnk
      rw [coeff_hermite_succ_zero]; rw [ih hnk]; rw [neg_zero]
    | succ k =>
      rw [coeff_

中文:
定理 coeff_hermite_of_odd_add
  条件: {n k : 自然数} (hnk : Odd (n + k))
  结论: coeff (hermite n) k = 0
  证明: by
  induction n generalizing k with
  | zero =>
    rw [zero_add k] at hnk
    exact coeff_hermite_of_lt hnk.pos
  | succ n ih =>
    cases k with
    | zero =>
      rw [Nat.succ_add_eq_add_succ] at hnk
      rw [coeff_hermite_succ_zero]; rw [ih hnk]; rw [neg_zero]
    | succ k =>
      rw [coeff_

Depends on / 依赖: Nat.add_succ, Nat.odd_add.mp, Nat.succ_add, Nat.succ_add_eq_add_succ, add_succ, coeff_hermite_of_lt, coeff_hermite_succ_succ, coeff_hermite_succ_zero, even_two, generalizing, hnk.pos, k.succ, mul_zero, n.succ, neg_zero, odd_add, sub_zero, succ_add, succ_add_eq_add_succ, zero_add
-/
theorem coeff_hermite_of_odd_add {n k : Nat} (hnk : Odd (n + k)) : coeff (hermite n) k = 0 := by
  induction n generalizing k with
  | zero =>
    rw [zero_add k] at hnk
    exact coeff_hermite_of_lt hnk.pos
  | succ n ih =>
    cases k with
    | zero =>
      rw [Nat.succ_add_eq_add_succ] at hnk
      rw [coeff_hermite_succ_zero]; rw [ih hnk]; rw [neg_zero]
    | succ k =>
      rw [coeff_hermite_succ_succ]; rw [ih]; rw [ih]; rw [mul_zero]; rw [sub_zero]
      · rwa [Nat.succ_add_eq_add_succ] at hnk
      · rw [(by rw [Nat.succ_add, Nat.add_succ] : n.succ + k.succ = n + k + 2)] at hnk
        exact (Nat.odd_add.mp hnk).mpr even_two

end coeff

section CoeffExplicit

open scoped Nat

/--
theorem `coeff_hermite_explicit` / 定理 `coeff_hermite_explicit`

English:
theorem coeff_hermite_explicit
  proof: fun n k =>
      (-1) ^ n * (2 * n - 1)‼ * Nat.choose (2 * n + k) k
    have hermite_explicit_recur :
      forall n k : Nat,
        hermite_explicit (n + 1) (k + 1) =
          hermite_explicit (n + 1) k - (k + 2) * hermite_explicit n (k + 2) := by
      intro n k
      simp only [hermite_explicit

中文:
定理 coeff_hermite_explicit
  证明: fun n k =>
      (-1) ^ n * (2 * n - 1)‼ * Nat.choose (2 * n + k) k
    have hermite_explicit_recur :
      forall n k : Nat,
        hermite_explicit (n + 1) (k + 1) =
          hermite_explicit (n + 1) k - (k + 2) * hermite_explicit n (k + 2) := by
      intro n k
      simp only [hermite_explicit
-/
theorem coeff_hermite_explicit :
    forall n k : Nat, coeff (hermite (2 * n + k)) k = (-1) ^ n * (2 * n - 1)‼ * Nat.choose (2 * n + k) k
  | 0, _ => by simp
  | n + 1, 0 => by
    convert! coeff_hermite_succ_zero (2 * n + 1) using 1
    rw [coeff_hermite_explicit n 1]; rw [(by grind : 2 * (n + 1) - 1 = 2 * n + 1)]; rw [Nat.doubleFactorial_add_one]; rw [Nat.choose_zero_right]; rw [Nat.choose_one_right]; rw [pow_succ]
    push_cast
    ring
  | n + 1, k + 1 => by
    let hermite_explicit : Nat -> Nat -> Int := fun n k =>
      (-1) ^ n * (2 * n - 1)‼ * Nat.choose (2 * n + k) k
    have hermite_explicit_recur :
      forall n k : Nat,
        hermite_explicit (n + 1) (k + 1) =
          hermite_explicit (n + 1) k - (k + 2) * hermite_explicit n (k + 2) := by
      intro n k
      simp only [hermite_explicit]
      -- Factor out (-1)'s.
      rw [mul_comm (↑k + _ : Int)]; rw [sub_eq_add_neg]
      nth_rw 3 [neg_eq_neg_one_mul]
      simp only [mul_assoc, ← mul_add, pow_succ']
      congr 2
      -- Factor out double factorials.
      norm_cast
      rw [(by grind : 2 * (n + 1) - 1 = 2 * n + 1)]; rw [Nat.doubleFactorial_add_one]; rw [mul_comm (2 * n + 1)]
      simp only [mul_assoc, ← mul_add]
      congr 1
      -- Match up binomial coefficients using `Nat.choose_succ_right_eq`.
      rw [(by ring : 2 * (n + 1) + (k + 1) = 2 * n + 1 + (k + 1) + 1)]; rw [(by ring : 2 * (n + 1) + k = 2 * n + 1 + (k + 1))]; rw [(by ring : 2 * n + (k + 2) = 2 * n + 1 + (k + 1))]
      rw [Nat.choose]; rw [Nat.choose_succ_right_eq (2 * n + 1 + (k + 1)) (k + 1)]; rw [Nat.add_sub_cancel]
      ring
    change _ = hermite_explicit _ _
    rw [← add_assoc]; rw [coeff_hermite_succ_succ]; rw [hermite_explicit_recur]
    congr
    · rw [coeff_hermite_explicit (n + 1) k]
    · rw [(by ring : 2 * (n + 1) + k = 2 * n + (k + 2)), coeff_hermite_explicit n (k + 2)]

/--
theorem `coeff_hermite_of_even_add` / 定理 `coeff_hermite_of_even_add`

English:
theorem coeff_hermite_of_even_add
  given: {n k : Nat} (hnk : Even (n + k))
  proof: by
  rcases le_or_gt k n with h_le | h_lt
  · rw [Nat.even_add, ← Nat.even_sub h_le] at hnk
    obtain ⟨m, hm⟩ := hnk
    rw [(by lia : n = 2 * m + k)]; rw [Nat.add_sub_cancel]; rw [Nat.mul_div_cancel_left _ (Nat.succ_pos 1)]; rw [coeff_hermite_explicit]
  · simp [Nat.choose_eq_zero_of_lt h_lt, coef

中文:
定理 coeff_hermite_of_even_add
  条件: {n k : 自然数} (hnk : Even (n + k))
  证明: by
  rcases le_or_gt k n with h_le | h_lt
  · rw [Nat.even_add, ← Nat.even_sub h_le] at hnk
    obtain ⟨m, hm⟩ := hnk
    rw [(by lia : n = 2 * m + k)]; rw [Nat.add_sub_cancel]; rw [Nat.mul_div_cancel_left _ (Nat.succ_pos 1)]; rw [coeff_hermite_explicit]
  · simp [Nat.choose_eq_zero_of_lt h_lt, coef

Depends on / 依赖: Nat.add_sub_cancel, Nat.choose_eq_zero_of_lt, Nat.even_add, Nat.even_sub, Nat.mul_div_cancel_left, Nat.succ_pos, add_sub_cancel, choose_eq_zero_of_lt, coeff_hermite_explicit, coeff_hermite_of_lt, even_add, even_sub, h_le, h_lt, le_or_gt, mul_div_cancel_left, succ_pos
-/
theorem coeff_hermite_of_even_add {n k : Nat} (hnk : Even (n + k)) :
    coeff (hermite n) k = (-1) ^ ((n - k) / 2) * (n - k - 1)‼ * Nat.choose n k := by
  rcases le_or_gt k n with h_le | h_lt
  · rw [Nat.even_add, ← Nat.even_sub h_le] at hnk
    obtain ⟨m, hm⟩ := hnk
    rw [(by lia : n = 2 * m + k)]; rw [Nat.add_sub_cancel]; rw [Nat.mul_div_cancel_left _ (Nat.succ_pos 1)]; rw [coeff_hermite_explicit]
  · simp [Nat.choose_eq_zero_of_lt h_lt, coeff_hermite_of_lt h_lt]

/--
theorem `coeff_hermite` / 定理 `coeff_hermite`

English:
theorem coeff_hermite
  given: (n k : Nat)
  proof: by
  split_ifs with h
  · exact coeff_hermite_of_even_add h
  · exact coeff_hermite_of_odd_add (Nat.not_even_iff_odd.1 h)

中文:
定理 coeff_hermite
  条件: (n k : 自然数)
  证明: by
  split_ifs with h
  · exact coeff_hermite_of_even_add h
  · exact coeff_hermite_of_odd_add (Nat.not_even_iff_odd.1 h)

Depends on / 依赖: Nat.not_even_iff_odd, coeff_hermite_of_even_add, coeff_hermite_of_odd_add, not_even_iff_odd, split_ifs
-/
theorem coeff_hermite (n k : Nat) :
    coeff (hermite n) k =
      if Even (n + k) then (-1 : Int) ^ ((n - k) / 2) * (n - k - 1)‼ * Nat.choose n k else 0 := by
  split_ifs with h
  · exact coeff_hermite_of_even_add h
  · exact coeff_hermite_of_odd_add (Nat.not_even_iff_odd.1 h)

end CoeffExplicit

end Polynomial
