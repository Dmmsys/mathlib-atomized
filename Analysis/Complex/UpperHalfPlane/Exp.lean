/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.Complex.Periodic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic

/-!
# Exp on the upper half plane

This file contains lemmas about the exponential function on the upper half plane. Useful for
q-expansions of modular forms.
-/

public section

open Real Complex UpperHalfPlane Function

local notation "𝕢" => Periodic.qParam

/--
theorem `Function.Periodic.im_invQParam_pos_of_norm_lt_one` / 定理 `Function.Periodic.im_invQParam_pos_of_norm_lt_one`

English:
theorem Function.Periodic.im_invQParam_pos_of_norm_lt_one
  proof: im_invQParam .. ▸ mul_pos_of_neg_of_neg
    (div_neg_of_neg_of_pos (neg_lt_zero.mpr hh) Real.two_pi_pos)
    ((Real.log_neg_iff (norm_pos_iff.mpr hq_ne)).mpr hq)

中文:
定理 函数.周期.im_invQParam_pos_of_norm_lt_one
  证明: im_invQParam .. ▸ mul_pos_of_neg_of_neg
    (div_neg_of_neg_of_pos (neg_lt_zero.mpr hh) Real.two_pi_pos)
    ((Real.log_neg_iff (norm_pos_iff.mpr hq_ne)).mpr hq)

Depends on / 依赖: Real.log_neg_iff, Real.two_pi_pos, div_neg_of_neg_of_pos, hq_ne, im_invQParam, log_neg_iff, mul_pos_of_neg_of_neg, neg_lt_zero, neg_lt_zero.mpr, norm_pos_iff, norm_pos_iff.mpr, two_pi_pos
-/
theorem Function.Periodic.im_invQParam_pos_of_norm_lt_one
    {h : Real} (hh : 0 < h) {q : Complex} (hq : ‖q‖ < 1) (hq_ne : q != 0) :
    0 < im (Periodic.invQParam h q) :=
  im_invQParam .. ▸ mul_pos_of_neg_of_neg
    (div_neg_of_neg_of_pos (neg_lt_zero.mpr hh) Real.two_pi_pos)
    ((Real.log_neg_iff (norm_pos_iff.mpr hq_ne)).mpr hq)

/--
lemma `Function.Periodic.norm_qParam_le_of_one_half_le_im` / 引理 `Function.Periodic.norm_qParam_le_of_one_half_le_im`

English:
lemma Function.Periodic.norm_qParam_le_of_one_half_le_im
  given: {ξ : Complex} (hξ : 1 / 2 <= ξ.im)
  proof: by
  rwa [Periodic.qParam, ofReal_one, div_one, Complex.norm_exp, Real.exp_le_exp,
    mul_right_comm, mul_I_re, neg_le_neg_iff, ← ofReal_ofNat, ← ofReal_mul, im_ofReal_mul,
    mul_comm _ π, mul_assoc, le_mul_iff_one_le_right Real.pi_pos, ← div_le_iff₀' two_pos]

中文:
引理 函数.周期.norm_qParam_le_of_one_half_le_im
  条件: {ξ : 复形} (hξ : 1 / 2 <= ξ.im)
  证明: by
  rwa [Periodic.qParam, ofReal_one, div_one, Complex.norm_exp, Real.exp_le_exp,
    mul_right_comm, mul_I_re, neg_le_neg_iff, ← ofReal_ofNat, ← ofReal_mul, im_ofReal_mul,
    mul_comm _ π, mul_assoc, le_mul_iff_one_le_right Real.pi_pos, ← div_le_iff₀' two_pos]

Depends on / 依赖: Complex.norm_exp, Periodic, Periodic.qParam, Real.exp_le_exp, Real.pi_pos, div_one, exp_le_exp, im_ofReal_mul, le_mul_iff_one_le_right, mul_I_re, mul_assoc, mul_comm, mul_right_comm, neg_le_neg_iff, norm_exp, ofReal_mul, ofReal_ofNat, ofReal_one, pi_pos, qParam
-/
lemma Function.Periodic.norm_qParam_le_of_one_half_le_im {ξ : Complex} (hξ : 1 / 2 <= ξ.im) :
    ‖𝕢 1 ξ‖ <= rexp (-π) := by
  rwa [Periodic.qParam, ofReal_one, div_one, Complex.norm_exp, Real.exp_le_exp,
    mul_right_comm, mul_I_re, neg_le_neg_iff, ← ofReal_ofNat, ← ofReal_mul, im_ofReal_mul,
    mul_comm _ π, mul_assoc, le_mul_iff_one_le_right Real.pi_pos, ← div_le_iff₀' two_pos]

/--
theorem `UpperHalfPlane.norm_qParam_lt_one` / 定理 `UpperHalfPlane.norm_qParam_lt_one`

English:
theorem UpperHalfPlane.norm_qParam_lt_one
  given: (n : Nat) [NeZero n] (τ : ℍ)
  statement: ‖𝕢 n τ‖ < 1
  proof: by
  rw [Periodic.norm_qParam]; rw [Real.exp_lt_one_iff]; rw [neg_mul]; rw [coe_im]; rw [neg_mul]; rw [neg_div]; rw [neg_lt_zero]; rw [div_pos_iff_of_pos_right (mod_cast Nat.pos_of_ne_zero <| NeZero.ne _)]
  positivity

中文:
定理 UpperHalfPlane.norm_qParam_lt_one
  条件: (n : 自然数) [NeZero n] (τ : ℍ)
  结论: ‖𝕢 n τ‖ < 1
  证明: by
  rw [Periodic.norm_qParam]; rw [Real.exp_lt_one_iff]; rw [neg_mul]; rw [coe_im]; rw [neg_mul]; rw [neg_div]; rw [neg_lt_zero]; rw [div_pos_iff_of_pos_right (mod_cast Nat.pos_of_ne_zero <| NeZero.ne _)]
  positivity

Depends on / 依赖: Nat.pos_of_ne_zero, NeZero, NeZero.ne, Periodic, Periodic.norm_qParam, Real.exp_lt_one_iff, coe_im, div_pos_iff_of_pos_right, exp_lt_one_iff, mod_cast, neg_div, neg_lt_zero, neg_mul, norm_qParam, pos_of_ne_zero
-/
theorem UpperHalfPlane.norm_qParam_lt_one (n : Nat) [NeZero n] (τ : ℍ) : ‖𝕢 n τ‖ < 1 := by
  rw [Periodic.norm_qParam]; rw [Real.exp_lt_one_iff]; rw [neg_mul]; rw [coe_im]; rw [neg_mul]; rw [neg_div]; rw [neg_lt_zero]; rw [div_pos_iff_of_pos_right (mod_cast Nat.pos_of_ne_zero <| NeZero.ne _)]
  positivity

/--
theorem `UpperHalfPlane.norm_exp_two_pi_I_lt_one` / 定理 `UpperHalfPlane.norm_exp_two_pi_I_lt_one`

English:
theorem UpperHalfPlane.norm_exp_two_pi_I_lt_one
  given: (τ : ℍ)
  proof: by
  simpa [Function.Periodic.norm_qParam, Complex.norm_exp] using τ.norm_qParam_lt_one 1

中文:
定理 UpperHalfPlane.norm_exp_two_pi_I_lt_one
  条件: (τ : ℍ)
  证明: by
  simpa [Function.Periodic.norm_qParam, Complex.norm_exp] using τ.norm_qParam_lt_one 1

Depends on / 依赖: Complex.norm_exp, Function, Function.Periodic.norm_qParam, Periodic, norm_exp, norm_qParam, norm_qParam_lt_one
-/
theorem UpperHalfPlane.norm_exp_two_pi_I_lt_one (τ : ℍ) :
    ‖(Complex.exp (2 * π * Complex.I * τ))‖ < 1 := by
  simpa [Function.Periodic.norm_qParam, Complex.norm_exp] using τ.norm_qParam_lt_one 1
