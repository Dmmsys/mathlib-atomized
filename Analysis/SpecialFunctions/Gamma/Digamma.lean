/-
Copyright (c) 2026 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
module

public import Mathlib.Analysis.Meromorphic.Complex
public import Mathlib.NumberTheory.Harmonic.GammaDeriv

import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

/-!
# The digamma function

This file defines the digamma function as the logarithmic derivative of the Gamma function and
proves some basic properties.

## Main definitions

* `Complex.digamma`: The digamma function of a complex variable.

## Main statements

* `Complex.digamma_apply_add_one`: The digamma function satisfies the functional equation
  `digamma (s + 1) = digamma s + s⁻¹`.
* `Complex.meromorphic_digamma`: The digamma function is meromorphic.

## TODO

* Prove Gauss' integral representation of the digamma function.
-/

@[expose] public section

namespace Complex

/--
Definition of `digamma` / `digamma` 的定义

English:
definition digamma
  signature: : Complex -> Complex
  body: logDeriv Gamma

中文:
定义 digamma
  签名: : 复形 -> 复形
  定义体: logDeriv Gamma

Depends on / 依赖: logDeriv
-/
noncomputable def digamma : Complex -> Complex := logDeriv Gamma

/--
theorem `digamma_def` / 定理 `digamma_def`

English:
theorem digamma_def
  statement: digamma = logDeriv Gamma
  proof: rfl

@[simp]

中文:
定理 digamma_def
  结论: digamma = logDeriv Gamma
  证明: rfl

@[simp]
-/
theorem digamma_def : digamma = logDeriv Gamma := rfl

@[simp]
/--
theorem `digamma_zero` / 定理 `digamma_zero`

English:
theorem digamma_zero
  statement: digamma 0 = 0
  proof: logDeriv_eq_zero_of_not_differentiableAt Gamma 0 not_differentiableAt_Gamma_zero

中文:
定理 digamma_zero
  结论: digamma 0 = 0
  证明: logDeriv_eq_zero_of_not_differentiableAt Gamma 0 not_differentiableAt_Gamma_zero

Depends on / 依赖: logDeriv_eq_zero_of_not_differentiableAt, not_differentiableAt_Gamma_zero
-/
theorem digamma_zero : digamma 0 = 0 :=
  logDeriv_eq_zero_of_not_differentiableAt Gamma 0 not_differentiableAt_Gamma_zero

/--
theorem `digamma_one` / 定理 `digamma_one`

English:
theorem digamma_one
  statement: digamma 1 = - Real.eulerMascheroniConstant
  proof: by
  rw [digamma_def]; rw [logDeriv_apply]; rw [hasDerivAt_Gamma_one.deriv]; rw [Gamma_one]; rw [div_one]

中文:
定理 digamma_one
  结论: digamma 1 = - 实数.eulerMascheroniConstant
  证明: by
  rw [digamma_def]; rw [logDeriv_apply]; rw [hasDerivAt_Gamma_one.deriv]; rw [Gamma_one]; rw [div_one]

Depends on / 依赖: Gamma_one, digamma_def, div_one, hasDerivAt_Gamma_one, hasDerivAt_Gamma_one.deriv, logDeriv_apply
-/
theorem digamma_one : digamma 1 = - Real.eulerMascheroniConstant := by
  rw [digamma_def]; rw [logDeriv_apply]; rw [hasDerivAt_Gamma_one.deriv]; rw [Gamma_one]; rw [div_one]

/--
theorem `digamma_one_half` / 定理 `digamma_one_half`

English:
theorem digamma_one_half
  statement: digamma (1 / 2) = - 2 * log 2 - Real.eulerMascheroniConstant
  proof: by
  rw [digamma_def]; rw [logDeriv_apply]; rw [hasDerivAt_Gamma_one_half.deriv]; rw [add_comm]; rw [Gamma_one_half_eq]; rw [neg_mul]; rw [← mul_neg]; rw [neg_add']; rw [Real.sqrt_eq_rpow]; rw [ofReal_cpow Real.pi_nonneg]
  simp

中文:
定理 digamma_one_half
  结论: digamma (1 / 2) = - 2 * log 2 - 实数.eulerMascheroniConstant
  证明: by
  rw [digamma_def]; rw [logDeriv_apply]; rw [hasDerivAt_Gamma_one_half.deriv]; rw [add_comm]; rw [Gamma_one_half_eq]; rw [neg_mul]; rw [← mul_neg]; rw [neg_add']; rw [Real.sqrt_eq_rpow]; rw [ofReal_cpow Real.pi_nonneg]
  simp

Depends on / 依赖: Gamma_one_half_eq, Real.pi_nonneg, Real.sqrt_eq_rpow, add_comm, digamma_def, hasDerivAt_Gamma_one_half, hasDerivAt_Gamma_one_half.deriv, logDeriv_apply, mul_neg, neg_add, neg_mul, ofReal_cpow, pi_nonneg, sqrt_eq_rpow
-/
theorem digamma_one_half : digamma (1 / 2) = - 2 * log 2 - Real.eulerMascheroniConstant := by
  rw [digamma_def]; rw [logDeriv_apply]; rw [hasDerivAt_Gamma_one_half.deriv]; rw [add_comm]; rw [Gamma_one_half_eq]; rw [neg_mul]; rw [← mul_neg]; rw [neg_add']; rw [Real.sqrt_eq_rpow]; rw [ofReal_cpow Real.pi_nonneg]
  simp

/--
theorem `digamma_apply_add_one` / 定理 `digamma_apply_add_one`

English:
theorem digamma_apply_add_one
  given: (s : Complex) (hs : forall m : Nat, s != - m)
  proof: by
  have hs0 : s != 0 := by simpa using hs 0
  rw [digamma_def]; rw [logDeriv_apply]; rw [logDeriv_apply]; rw [deriv_Gamma_add_one s hs0]; rw [Gamma_add_one s hs0]; rw [add_div]; rw [div_mul_cancel_right₀ (Gamma_ne_zero hs)]; rw [mul_div_mul_left _ _ hs0]; rw [add_comm]

中文:
定理 digamma_apply_add_one
  条件: (s : 复形) (hs : 对任意 m : 自然数, s != - m)
  证明: by
  have hs0 : s != 0 := by simpa using hs 0
  rw [digamma_def]; rw [logDeriv_apply]; rw [logDeriv_apply]; rw [deriv_Gamma_add_one s hs0]; rw [Gamma_add_one s hs0]; rw [add_div]; rw [div_mul_cancel_right₀ (Gamma_ne_zero hs)]; rw [mul_div_mul_left _ _ hs0]; rw [add_comm]

Depends on / 依赖: Gamma_add_one, Gamma_ne_zero, add_comm, add_div, deriv_Gamma_add_one, digamma_def, logDeriv_apply, mul_div_mul_left
-/
theorem digamma_apply_add_one (s : Complex) (hs : forall m : Nat, s != - m) :
    digamma (s + 1) = digamma s + s⁻¹ := by
  have hs0 : s != 0 := by simpa using hs 0
  rw [digamma_def]; rw [logDeriv_apply]; rw [logDeriv_apply]; rw [deriv_Gamma_add_one s hs0]; rw [Gamma_add_one s hs0]; rw [add_div]; rw [div_mul_cancel_right₀ (Gamma_ne_zero hs)]; rw [mul_div_mul_left _ _ hs0]; rw [add_comm]

/--
theorem `meromorphic_digamma` / 定理 `meromorphic_digamma`

English:
theorem meromorphic_digamma
  statement: Meromorphic digamma
  proof: Meromorphic.Gamma.logDeriv

中文:
定理 meromorphic_digamma
  结论: 亚纯 digamma
  证明: Meromorphic.Gamma.logDeriv

Depends on / 依赖: Meromorphic, Meromorphic.Gamma.logDeriv, logDeriv
-/
theorem meromorphic_digamma : Meromorphic digamma :=
  Meromorphic.Gamma.logDeriv

end Complex
