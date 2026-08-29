/-
Copyright (c) 2023 Luke Mantle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Mantle, Jake Levinson
-/
module

public import Mathlib.RingTheory.Polynomial.Hermite.Basic
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Hermite polynomials and Gaussians

This file shows that the Hermite polynomial `hermite n` is (up to sign) the
polynomial factor occurring in the `n`th derivative of a Gaussian.

## Results

* `Polynomial.deriv_gaussian_eq_hermite_mul_gaussian`:
  The Hermite polynomial is (up to sign) the polynomial factor occurring in the
  `n`th derivative of a Gaussian.

## References

* [Hermite Polynomials](https://en.wikipedia.org/wiki/Hermite_polynomials)

-/

public section


noncomputable section

open Polynomial

namespace Polynomial

/--
theorem `deriv_gaussian_eq_hermite_mul_gaussian` / 定理 `deriv_gaussian_eq_hermite_mul_gaussian`

English:
theorem deriv_gaussian_eq_hermite_mul_gaussian
  given: (n : Nat) (x : Real)
  proof: by
  rw [mul_assoc]
  induction n generalizing x with
  | zero => rw [Function.iterate_zero_apply, pow_zero, one_mul, hermite_zero, C_1, map_one, one_mul]
  | succ n ih =>
    replace ih : deriv^[n] _ = _ := _root_.funext ih
    have deriv_gaussian :
      deriv (fun y => Real.exp (-(y ^ 2 / 2))) x 

中文:
定理 deriv_gaussian_eq_hermite_mul_gaussian
  条件: (n : 自然数) (x : 实数)
  证明: by
  rw [mul_assoc]
  induction n generalizing x with
  | zero => rw [Function.iterate_zero_apply, pow_zero, one_mul, hermite_zero, C_1, map_one, one_mul]
  | succ n ih =>
    replace ih : deriv^[n] _ = _ := _root_.funext ih
    have deriv_gaussian :
      deriv (fun y => Real.exp (-(y ^ 2 / 2))) x 

Depends on / 依赖: Function, Function.iterate_zero_apply, Real.exp, _root_, _root_.funext, deriv_gaussian, generalizing, hermite_zero, iterate_zero_apply, map_one, mul_assoc, one_mul, pow_zero, replace
-/
theorem deriv_gaussian_eq_hermite_mul_gaussian (n : Nat) (x : Real) :
    deriv^[n] (fun y => Real.exp (-(y ^ 2 / 2))) x =
    (-1 : Real) ^ n * aeval x (hermite n) * Real.exp (-(x ^ 2 / 2)) := by
  rw [mul_assoc]
  induction n generalizing x with
  | zero => rw [Function.iterate_zero_apply, pow_zero, one_mul, hermite_zero, C_1, map_one, one_mul]
  | succ n ih =>
    replace ih : deriv^[n] _ = _ := _root_.funext ih
    have deriv_gaussian :
      deriv (fun y => Real.exp (-(y ^ 2 / 2))) x = -x * Real.exp (-(x ^ 2 / 2)) := by
      -- Porting note (https://github.com/leanprover-community/mathlib4/issues/10745): was `simp [mul_comm, ← neg_mul]`
      rw [deriv_exp (by simp)]
      simp [mul_comm]
    rw [Function.iterate_succ_apply']; rw [ih]; rw [deriv_const_mul_field]; rw [deriv_fun_mul]; rw [pow_succ (-1 : Real)]; rw [deriv_gaussian]; rw [hermite_succ]; rw [map_sub]; rw [map_mul]; rw [aeval_X]; rw [Polynomial.deriv_aeval]
    · ring
    · apply Polynomial.differentiable_aeval
    · apply DifferentiableAt.exp; simp -- Porting note: was just `simp`

/--
theorem `hermite_eq_deriv_gaussian` / 定理 `hermite_eq_deriv_gaussian`

English:
theorem hermite_eq_deriv_gaussian
  given: (n : Nat) (x : Real)
  statement: aeval x (hermite n) =
  proof: by
  rw [deriv_gaussian_eq_hermite_mul_gaussian]
  field_simp
  rw [← pow_mul]
  simp

中文:
定理 hermite_eq_deriv_gaussian
  条件: (n : 自然数) (x : 实数)
  结论: aeval x (hermite n) =
  证明: by
  rw [deriv_gaussian_eq_hermite_mul_gaussian]
  field_simp
  rw [← pow_mul]
  simp

Depends on / 依赖: deriv_gaussian_eq_hermite_mul_gaussian, pow_mul
-/
theorem hermite_eq_deriv_gaussian (n : Nat) (x : Real) : aeval x (hermite n) =
    (-1 : Real) ^ n * deriv^[n] (fun y => Real.exp (-(y ^ 2 / 2))) x / Real.exp (-(x ^ 2 / 2)) := by
  rw [deriv_gaussian_eq_hermite_mul_gaussian]
  field_simp
  rw [← pow_mul]
  simp

/--
theorem `hermite_eq_deriv_gaussian'` / 定理 `hermite_eq_deriv_gaussian'`

English:
theorem hermite_eq_deriv_gaussian'
  given: (n : Nat) (x : Real)
  statement: aeval x (hermite n) =
  proof: by
  rw [hermite_eq_deriv_gaussian]; rw [Real.exp_neg]
  field

中文:
定理 hermite_eq_deriv_gaussian'
  条件: (n : 自然数) (x : 实数)
  结论: aeval x (hermite n) =
  证明: by
  rw [hermite_eq_deriv_gaussian]; rw [Real.exp_neg]
  field

Depends on / 依赖: Real.exp_neg, exp_neg, hermite_eq_deriv_gaussian
-/
theorem hermite_eq_deriv_gaussian' (n : Nat) (x : Real) : aeval x (hermite n) =
    (-1 : Real) ^ n * deriv^[n] (fun y => Real.exp (-(y ^ 2 / 2))) x * Real.exp (x ^ 2 / 2) := by
  rw [hermite_eq_deriv_gaussian]; rw [Real.exp_neg]
  field

end Polynomial
