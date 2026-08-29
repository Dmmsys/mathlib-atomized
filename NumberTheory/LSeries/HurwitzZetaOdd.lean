/-
Copyright (c) 2024 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
module

public import Mathlib.NumberTheory.LSeries.AbstractFuncEq
public import Mathlib.NumberTheory.ModularForms.JacobiTheta.Bounds
public import Mathlib.NumberTheory.LSeries.MellinEqDirichlet
public import Mathlib.NumberTheory.LSeries.Basic

/-!
# Odd Hurwitz zeta functions

In this file we study the functions on `ℂ` which are the analytic continuation of the following
series (convergent for `1 < re s`), where `a ∈ ℝ` is a parameter:

`hurwitzZetaOdd a s = 1 / 2 * ∑' n : ℤ, sgn (n + a) / |n + a| ^ s`

and

`sinZeta a s = ∑' n : ℕ, sin (2 * π * a * n) / n ^ s`.

The term for `n = -a` in the first sum is understood as 0 if `a` is an integer, as is the term for
`n = 0` in the second sum (for all `a`). Note that these functions are differentiable everywhere,
unlike their even counterparts which have poles.

Of course, we cannot *define* these functions by the above formulae (since existence of the
analytic continuation is not at all obvious); we in fact construct them as Mellin transforms of
various versions of the Jacobi theta function.

## Main definitions and theorems

* `completedHurwitzZetaOdd`: the completed Hurwitz zeta function
* `completedSinZeta`: the completed sine zeta function
* `differentiable_completedHurwitzZetaOdd` and `differentiable_completedSinZeta`:
  differentiability on `ℂ`
* `completedHurwitzZetaOdd_one_sub`: the functional equation
  `completedHurwitzZetaOdd a (1 - s) = completedSinZeta a s`
* `hasSum_int_hurwitzZetaOdd` and `hasSum_nat_sinZeta`: relation between
  the zeta functions and corresponding Dirichlet series for `1 < re s`
-/

@[expose] public section

noncomputable section

open Complex
open CharZero Filter Topology Asymptotics Real Set MeasureTheory
open scoped ComplexConjugate

namespace HurwitzZeta

section kernel_defs
/-!
## Definitions and elementary properties of kernels
-/

/--
Definition of `jacobiTheta₂''` / `jacobiTheta₂''` 的定义

English:
definition jacobiTheta₂''
  signature: (z τ : Complex)
  body: cexp (π * I * z ^ 2 * τ) * (jacobiTheta₂' (z * τ) τ / (2 * π * I) + z * jacobiTheta₂ (z * τ) τ)

中文:
定义 jacobiTheta₂''
  签名: (z τ : 复形)
  定义体: cexp (π * I * z ^ 2 * τ) * (jacobiTheta₂' (z * τ) τ / (2 * π * I) + z * jacobiTheta₂ (z * τ) τ)
-/
def jacobiTheta₂'' (z τ : Complex) : Complex :=
  cexp (π * I * z ^ 2 * τ) * (jacobiTheta₂' (z * τ) τ / (2 * π * I) + z * jacobiTheta₂ (z * τ) τ)

/--
lemma `jacobiTheta₂''_conj` / 引理 `jacobiTheta₂''_conj`

English:
lemma jacobiTheta₂''_conj
  given: (z τ : Complex)
  proof: by
  simp [jacobiTheta₂'', jacobiTheta₂'_conj, jacobiTheta₂_conj, ← exp_conj, map_ofNat, div_neg,
    neg_div, jacobiTheta₂'_neg_left]

中文:
引理 jacobiTheta₂''_conj
  条件: (z τ : 复形)
  证明: by
  simp [jacobiTheta₂'', jacobiTheta₂'_conj, jacobiTheta₂_conj, ← exp_conj, map_ofNat, div_neg,
    neg_div, jacobiTheta₂'_neg_left]
-/
lemma jacobiTheta₂''_conj (z τ : Complex) :
    conj (jacobiTheta₂'' z τ) = jacobiTheta₂'' (conj z) (-conj τ) := by
  simp [jacobiTheta₂'', jacobiTheta₂'_conj, jacobiTheta₂_conj, ← exp_conj, map_ofNat, div_neg,
    neg_div, jacobiTheta₂'_neg_left]

/--
lemma `jacobiTheta₂''_add_left` / 引理 `jacobiTheta₂''_add_left`

English:
lemma jacobiTheta₂''_add_left
  given: (z τ : Complex)
  statement: jacobiTheta₂'' (z + 1) τ = jacobiTheta₂'' z τ
  proof: by
  simp only [jacobiTheta₂'', add_mul z 1, one_mul, jacobiTheta₂'_add_left', jacobiTheta₂_add_left']
  generalize jacobiTheta₂ (z * τ) τ = J
  generalize jacobiTheta₂' (z * τ) τ = J'
  -- clear denominator
  simp_rw [div_add' _ _ _ two_pi_I_ne_zero, ← mul_div_assoc]
  refine congr_arg (· / (2 * π 

中文:
引理 jacobiTheta₂''_add_left
  条件: (z τ : 复形)
  结论: jacobiTheta₂'' (z + 1) τ = jacobiTheta₂'' z τ
  证明: by
  simp only [jacobiTheta₂'', add_mul z 1, one_mul, jacobiTheta₂'_add_left', jacobiTheta₂_add_left']
  generalize jacobiTheta₂ (z * τ) τ = J
  generalize jacobiTheta₂' (z * τ) τ = J'
  -- clear denominator
  simp_rw [div_add' _ _ _ two_pi_I_ne_zero, ← mul_div_assoc]
  refine congr_arg (· / (2 * π 
-/
lemma jacobiTheta₂''_add_left (z τ : Complex) : jacobiTheta₂'' (z + 1) τ = jacobiTheta₂'' z τ := by
  simp only [jacobiTheta₂'', add_mul z 1, one_mul, jacobiTheta₂'_add_left', jacobiTheta₂_add_left']
  generalize jacobiTheta₂ (z * τ) τ = J
  generalize jacobiTheta₂' (z * τ) τ = J'
  -- clear denominator
  simp_rw [div_add' _ _ _ two_pi_I_ne_zero, ← mul_div_assoc]
  refine congr_arg (· / (2 * π * I)) ?_
  -- get all exponential terms to left
  rw [mul_left_comm _ (cexp _)]; rw [← mul_add]; rw [mul_assoc (cexp _)]; rw [← mul_add]; rw [← mul_assoc (cexp _)]; rw [← Complex.exp_add]
  congrm (cexp ?_ * ?_) <;> ring

/--
lemma `jacobiTheta₂''_neg_left` / 引理 `jacobiTheta₂''_neg_left`

English:
lemma jacobiTheta₂''_neg_left
  given: (z τ : Complex)
  statement: jacobiTheta₂'' (-z) τ = -jacobiTheta₂'' z τ
  proof: by
  simp [jacobiTheta₂'', jacobiTheta₂'_neg_left, neg_div, -neg_add_rev, ← neg_add]

中文:
引理 jacobiTheta₂''_neg_left
  条件: (z τ : 复形)
  结论: jacobiTheta₂'' (-z) τ = -jacobiTheta₂'' z τ
  证明: by
  simp [jacobiTheta₂'', jacobiTheta₂'_neg_left, neg_div, -neg_add_rev, ← neg_add]
-/
lemma jacobiTheta₂''_neg_left (z τ : Complex) : jacobiTheta₂'' (-z) τ = -jacobiTheta₂'' z τ := by
  simp [jacobiTheta₂'', jacobiTheta₂'_neg_left, neg_div, -neg_add_rev, ← neg_add]

/--
lemma `jacobiTheta₂'_functional_equation'` / 引理 `jacobiTheta₂'_functional_equation'`

English:
lemma jacobiTheta₂'_functional_equation'
  given: (z τ : Complex)
  proof: by
  rcases eq_or_ne τ 0 with rfl | hτ
  · rw [jacobiTheta₂'_undef _ (by simp), mul_zero, zero_cpow (by simp), div_zero, zero_mul]
  have aux1 : (-2 * π : Complex) / (2 * π * I) = I := by
    rw [div_eq_iff two_pi_I_ne_zero]; rw [mul_comm I]; rw [mul_assoc _ I I]; rw [I_mul_I]; rw [neg_mul]; rw [mul

中文:
引理 jacobiTheta₂'_functional_equation'
  条件: (z τ : 复形)
  证明: by
  rcases eq_or_ne τ 0 with rfl | hτ
  · rw [jacobiTheta₂'_undef _ (by simp), mul_zero, zero_cpow (by simp), div_zero, zero_mul]
  have aux1 : (-2 * π : Complex) / (2 * π * I) = I := by
    rw [div_eq_iff two_pi_I_ne_zero]; rw [mul_comm I]; rw [mul_assoc _ I I]; rw [I_mul_I]; rw [neg_mul]; rw [mul

Depends on / 依赖: I_mul_I, I_ne_zero, _functional_equation, _undef, cpow_one, div_div, div_eq_iff, div_self, div_zero, eq_or_ne, mul_assoc, mul_comm, mul_neg, mul_one, mul_one_div, mul_right_comm, mul_zero, neg_mul, neg_ne_zero, neg_ne_zero.mpr
-/
lemma jacobiTheta₂'_functional_equation' (z τ : Complex) :
    jacobiTheta₂' z τ = (-2 * π) / (-I * τ) ^ (3 / 2 : Complex) * jacobiTheta₂'' z (-1 / τ) := by
  rcases eq_or_ne τ 0 with rfl | hτ
  · rw [jacobiTheta₂'_undef _ (by simp), mul_zero, zero_cpow (by simp), div_zero, zero_mul]
  have aux1 : (-2 * π : Complex) / (2 * π * I) = I := by
    rw [div_eq_iff two_pi_I_ne_zero]; rw [mul_comm I]; rw [mul_assoc _ I I]; rw [I_mul_I]; rw [neg_mul]; rw [mul_neg]; rw [mul_one]
  rw [jacobiTheta₂'_functional_equation]; rw [← mul_one_div _ τ]; rw [mul_right_comm _ (cexp _)]; rw [(by rw [cpow_one]; rw [← div_div]; rw [div_self (neg_ne_zero.mpr I_ne_zero)] :
      1 / τ = -I / (-I * τ) ^ (1 : Complex)), div_mul_div_comm,
    ← cpow_add _ _ (mul_ne_zero (neg_ne_zero.mpr I_ne_zero) hτ), ← div_mul_eq_mul_div,
    (by norm_num : (1 / 2 + 1 : Complex) = 3 / 2), mul_assoc (1 / _), mul_assoc (1 / _),
    ← mul_one_div (-2 * π : Complex), mul_comm _ (1 / _), mul_assoc (1 / _)]
  congr 1
  rw [jacobiTheta₂'']; rw [div_add' _ _ _ two_pi_I_ne_zero]; rw [← mul_div_assoc]; rw [← mul_div_assoc]; rw [← div_mul_eq_mul_div (-2 * π : Complex)]; rw [mul_assoc]; rw [aux1]; rw [mul_div z (-1)]; rw [mul_neg_one]; rw [neg_div τ z]; rw [jacobiTheta₂_neg_left]; rw [jacobiTheta₂'_neg_left]; rw [neg_mul]; rw [← mul_neg]; rw [← mul_neg]; rw [mul_div]; rw [mul_neg_one]; rw [neg_div]; rw [neg_mul]; rw [neg_mul]; rw [neg_div]
  congr 2
  rw [neg_sub]; rw [← sub_eq_neg_add]; rw [mul_comm _ (_ * I)]; rw [← mul_assoc]

/--
Definition of `oddKernel` / `oddKernel` 的定义

English:
definition oddKernel
  signature: (a : UnitAddCircle) (x : Real)
  body: (show Function.Periodic (fun a : Real => re (jacobiTheta₂'' a (I * x))) 1 by
    simp [jacobiTheta₂''_add_left]).lift a

中文:
定义 oddKernel
  签名: (a : UnitAddCircle) (x : 实数)
  定义体: (show Function.Periodic (fun a : Real => re (jacobiTheta₂'' a (I * x))) 1 by
    simp [jacobiTheta₂''_add_left]).lift a
-/
@[irreducible] def oddKernel (a : UnitAddCircle) (x : Real) : Real :=
  (show Function.Periodic (fun a : Real => re (jacobiTheta₂'' a (I * x))) 1 by
    simp [jacobiTheta₂''_add_left]).lift a

/--
lemma `oddKernel_def` / 引理 `oddKernel_def`

English:
lemma oddKernel_def
  given: (a x : Real)
  statement: ↑(oddKernel a x) = jacobiTheta₂'' a (I * x)
  proof: by
  simp [oddKernel, ← conj_eq_iff_re, jacobiTheta₂''_conj]

中文:
引理 oddKernel_def
  条件: (a x : 实数)
  结论: ↑(oddKernel a x) = jacobiTheta₂'' a (I * x)
  证明: by
  simp [oddKernel, ← conj_eq_iff_re, jacobiTheta₂''_conj]

Depends on / 依赖: _conj, conj_eq_iff_re, oddKernel
-/
lemma oddKernel_def (a x : Real) : ↑(oddKernel a x) = jacobiTheta₂'' a (I * x) := by
  simp [oddKernel, ← conj_eq_iff_re, jacobiTheta₂''_conj]

/--
lemma `oddKernel_def'` / 引理 `oddKernel_def'`

English:
lemma oddKernel_def'
  given: (a x : Real)
  statement: ↑(oddKernel ↑a x) = cexp (-π * a ^ 2 * x) *
  proof: by
  rw [oddKernel_def]; rw [jacobiTheta₂'']; rw [← mul_assoc ↑a I x]; rw [(by ring : ↑π * I * ↑a ^ 2 * (I * ↑x) = I ^ 2 * ↑π * ↑a ^ 2 * x)]; rw [I_sq]; rw [neg_one_mul]

中文:
引理 oddKernel_def'
  条件: (a x : 实数)
  结论: ↑(oddKernel ↑a x) = cexp (-π * a ^ 2 * x) *
  证明: by
  rw [oddKernel_def]; rw [jacobiTheta₂'']; rw [← mul_assoc ↑a I x]; rw [(by ring : ↑π * I * ↑a ^ 2 * (I * ↑x) = I ^ 2 * ↑π * ↑a ^ 2 * x)]; rw [I_sq]; rw [neg_one_mul]

Depends on / 依赖: I_sq, mul_assoc, neg_one_mul, oddKernel_def
-/
lemma oddKernel_def' (a x : Real) : ↑(oddKernel ↑a x) = cexp (-π * a ^ 2 * x) *
    (jacobiTheta₂' (a * I * x) (I * x) / (2 * π * I) + a * jacobiTheta₂ (a * I * x) (I * x)) := by
  rw [oddKernel_def]; rw [jacobiTheta₂'']; rw [← mul_assoc ↑a I x]; rw [(by ring : ↑π * I * ↑a ^ 2 * (I * ↑x) = I ^ 2 * ↑π * ↑a ^ 2 * x)]; rw [I_sq]; rw [neg_one_mul]

/--
lemma `oddKernel_undef` / 引理 `oddKernel_undef`

English:
lemma oddKernel_undef
  given: (a : UnitAddCircle) {x : Real} (hx : x <= 0)
  statement: oddKernel a x = 0
  proof: by
  induction a using QuotientAddGroup.induction_on with | H a' =>
  rw [← ofReal_eq_zero]; rw [oddKernel_def']; rw [jacobiTheta₂_undef]; rw [jacobiTheta₂'_undef]; rw [zero_div]; rw [zero_add]; rw [mul_zero]; rw [mul_zero] <;>
  simpa

中文:
引理 oddKernel_undef
  条件: (a : UnitAddCircle) {x : 实数} (hx : x <= 0)
  结论: oddKernel a x = 0
  证明: by
  induction a using QuotientAddGroup.induction_on with | H a' =>
  rw [← ofReal_eq_zero]; rw [oddKernel_def']; rw [jacobiTheta₂_undef]; rw [jacobiTheta₂'_undef]; rw [zero_div]; rw [zero_add]; rw [mul_zero]; rw [mul_zero] <;>
  simpa

Depends on / 依赖: QuotientAddGroup, QuotientAddGroup.induction_on, _undef, induction_on, mul_zero, oddKernel_def, ofReal_eq_zero, zero_add, zero_div
-/
lemma oddKernel_undef (a : UnitAddCircle) {x : Real} (hx : x <= 0) : oddKernel a x = 0 := by
  induction a using QuotientAddGroup.induction_on with | H a' =>
  rw [← ofReal_eq_zero]; rw [oddKernel_def']; rw [jacobiTheta₂_undef]; rw [jacobiTheta₂'_undef]; rw [zero_div]; rw [zero_add]; rw [mul_zero]; rw [mul_zero] <;>
  simpa

/--
Definition of `sinKernel` / `sinKernel` 的定义

English:
definition sinKernel
  signature: (a : UnitAddCircle) (x : Real)
  body: (show Function.Periodic (fun ξ : Real => re (jacobiTheta₂' ξ (I * x) / (-2 * π))) 1 by
    simp [jacobiTheta₂'_add_left]).lift a

中文:
定义 sinKernel
  签名: (a : UnitAddCircle) (x : 实数)
  定义体: (show Function.Periodic (fun ξ : Real => re (jacobiTheta₂' ξ (I * x) / (-2 * π))) 1 by
    simp [jacobiTheta₂'_add_left]).lift a
-/
@[irreducible] def sinKernel (a : UnitAddCircle) (x : Real) : Real :=
  (show Function.Periodic (fun ξ : Real => re (jacobiTheta₂' ξ (I * x) / (-2 * π))) 1 by
    simp [jacobiTheta₂'_add_left]).lift a

/--
lemma `sinKernel_def` / 引理 `sinKernel_def`

English:
lemma sinKernel_def
  given: (a x : Real)
  statement: ↑(sinKernel ↑a x) = jacobiTheta₂' a (I * x) / (-2 * π)
  proof: by
  simp [sinKernel, re_eq_add_conj, jacobiTheta₂'_conj, map_ofNat]

中文:
引理 sinKernel_def
  条件: (a x : 实数)
  结论: ↑(sinKernel ↑a x) = jacobiTheta₂' a (I * x) / (-2 * π)
  证明: by
  simp [sinKernel, re_eq_add_conj, jacobiTheta₂'_conj, map_ofNat]

Depends on / 依赖: _conj, map_ofNat, re_eq_add_conj, sinKernel
-/
lemma sinKernel_def (a x : Real) : ↑(sinKernel ↑a x) = jacobiTheta₂' a (I * x) / (-2 * π) := by
  simp [sinKernel, re_eq_add_conj, jacobiTheta₂'_conj, map_ofNat]

/--
lemma `sinKernel_undef` / 引理 `sinKernel_undef`

English:
lemma sinKernel_undef
  given: (a : UnitAddCircle) {x : Real} (hx : x <= 0)
  statement: sinKernel a x = 0
  proof: by
  induction a using QuotientAddGroup.induction_on with
  | H a => rw [← ofReal_eq_zero, sinKernel_def, jacobiTheta₂'_undef _ (by simpa), zero_div]

中文:
引理 sinKernel_undef
  条件: (a : UnitAddCircle) {x : 实数} (hx : x <= 0)
  结论: sinKernel a x = 0
  证明: by
  induction a using QuotientAddGroup.induction_on with
  | H a => rw [← ofReal_eq_zero, sinKernel_def, jacobiTheta₂'_undef _ (by simpa), zero_div]

Depends on / 依赖: QuotientAddGroup, QuotientAddGroup.induction_on, _undef, induction_on, ofReal_eq_zero, sinKernel_def, zero_div
-/
lemma sinKernel_undef (a : UnitAddCircle) {x : Real} (hx : x <= 0) : sinKernel a x = 0 := by
  induction a using QuotientAddGroup.induction_on with
  | H a => rw [← ofReal_eq_zero, sinKernel_def, jacobiTheta₂'_undef _ (by simpa), zero_div]

/--
lemma `oddKernel_neg` / 引理 `oddKernel_neg`

English:
lemma oddKernel_neg
  given: (a : UnitAddCircle) (x : Real)
  statement: oddKernel (-a) x = -oddKernel a x
  proof: by
  induction a using QuotientAddGroup.induction_on with
  | H a => simp [← ofReal_inj, ← QuotientAddGroup.mk_neg, oddKernel_def, jacobiTheta₂''_neg_left]

中文:
引理 oddKernel_neg
  条件: (a : UnitAddCircle) (x : 实数)
  结论: oddKernel (-a) x = -oddKernel a x
  证明: by
  induction a using QuotientAddGroup.induction_on with
  | H a => simp [← ofReal_inj, ← QuotientAddGroup.mk_neg, oddKernel_def, jacobiTheta₂''_neg_left]

Depends on / 依赖: QuotientAddGroup, QuotientAddGroup.induction_on, QuotientAddGroup.mk_neg, _neg_left, induction_on, mk_neg, oddKernel_def, ofReal_inj
-/
lemma oddKernel_neg (a : UnitAddCircle) (x : Real) : oddKernel (-a) x = -oddKernel a x := by
  induction a using QuotientAddGroup.induction_on with
  | H a => simp [← ofReal_inj, ← QuotientAddGroup.mk_neg, oddKernel_def, jacobiTheta₂''_neg_left]

/--
lemma `oddKernel_zero` / 引理 `oddKernel_zero`

English:
lemma oddKernel_zero
  given: (x : Real)
  statement: oddKernel 0 x = 0
  proof: by
  simpa using oddKernel_neg 0 x

中文:
引理 oddKernel_zero
  条件: (x : 实数)
  结论: oddKernel 0 x = 0
  证明: by
  simpa using oddKernel_neg 0 x
-/
@[simp] lemma oddKernel_zero (x : Real) : oddKernel 0 x = 0 := by
  simpa using oddKernel_neg 0 x

/--
lemma `sinKernel_neg` / 引理 `sinKernel_neg`

English:
lemma sinKernel_neg
  given: (a : UnitAddCircle) (x : Real)
  proof: by
  induction a using QuotientAddGroup.induction_on with
  | H a => simp [← ofReal_inj, ← QuotientAddGroup.mk_neg, sinKernel_def, jacobiTheta₂'_neg_left,
      neg_div]

中文:
引理 sinKernel_neg
  条件: (a : UnitAddCircle) (x : 实数)
  证明: by
  induction a using QuotientAddGroup.induction_on with
  | H a => simp [← ofReal_inj, ← QuotientAddGroup.mk_neg, sinKernel_def, jacobiTheta₂'_neg_left,
      neg_div]

Depends on / 依赖: QuotientAddGroup, QuotientAddGroup.induction_on, QuotientAddGroup.mk_neg, _neg_left, induction_on, mk_neg, neg_div, ofReal_inj, sinKernel_def
-/
lemma sinKernel_neg (a : UnitAddCircle) (x : Real) :
    sinKernel (-a) x = -sinKernel a x := by
  induction a using QuotientAddGroup.induction_on with
  | H a => simp [← ofReal_inj, ← QuotientAddGroup.mk_neg, sinKernel_def, jacobiTheta₂'_neg_left,
      neg_div]

/--
lemma `sinKernel_zero` / 引理 `sinKernel_zero`

English:
lemma sinKernel_zero
  given: (x : Real)
  statement: sinKernel 0 x = 0
  proof: by
  simpa using sinKernel_neg 0 x

中文:
引理 sinKernel_zero
  条件: (x : 实数)
  结论: sinKernel 0 x = 0
  证明: by
  simpa using sinKernel_neg 0 x
-/
@[simp] lemma sinKernel_zero (x : Real) : sinKernel 0 x = 0 := by
  simpa using sinKernel_neg 0 x

/--
lemma `continuousOn_oddKernel` / 引理 `continuousOn_oddKernel`

English:
lemma continuousOn_oddKernel
  given: (a : UnitAddCircle)
  statement: ContinuousOn (oddKernel a) (Ioi 0)
  proof: by
  induction a using QuotientAddGroup.induction_on with | H a =>
  suffices ContinuousOn (fun x => (oddKernel a x : Complex)) (Ioi 0) from
    (continuous_re.comp_continuousOn this).congr fun a _ => (ofReal_re _).symm
  simp_rw [oddKernel_def' a]
  refine fun x hx => ((Continuous.continuousAt ?_).

中文:
引理 continuousOn_oddKernel
  条件: (a : UnitAddCircle)
  结论: ContinuousOn (oddKernel a) (左开右无界区间 0)
  证明: by
  induction a using QuotientAddGroup.induction_on with | H a =>
  suffices ContinuousOn (fun x => (oddKernel a x : Complex)) (Ioi 0) from
    (continuous_re.comp_continuousOn this).congr fun a _ => (ofReal_re _).symm
  simp_rw [oddKernel_def' a]
  refine fun x hx => ((Continuous.continuousAt ?_).

Depends on / 依赖: Continuous, Continuous.continuousAt, ContinuousAt, ContinuousAt.add, ContinuousOn, I_mul_im, QuotientAddGroup, QuotientAddGroup.induction_on, comp_continuousOn, continuousAt, continuousWithinAt, continuous_re, continuous_re.comp_continuousOn, fun_prop, induction_on, oddKernel, oddKernel_def, ofReal_re, simp_rw
-/
lemma continuousOn_oddKernel (a : UnitAddCircle) : ContinuousOn (oddKernel a) (Ioi 0) := by
  induction a using QuotientAddGroup.induction_on with | H a =>
  suffices ContinuousOn (fun x => (oddKernel a x : Complex)) (Ioi 0) from
    (continuous_re.comp_continuousOn this).congr fun a _ => (ofReal_re _).symm
  simp_rw [oddKernel_def' a]
  refine fun x hx => ((Continuous.continuousAt ?_).mul ?_).continuousWithinAt
  · fun_prop
  · have hf : Continuous fun u : Real => (a * I * u, I * u) := by fun_prop
    apply ContinuousAt.add
    · exact ((continuousAt_jacobiTheta₂' (a * I * x) (by rwa [I_mul_im, ofReal_re])).comp
        (f := fun u : Real => (a * I * u, I * u)) hf.continuousAt).div_const _
· exact continuousAt_const.mul (continuousAt_jacobiTheta₂ (a * I * x)
        (by rwa [I_mul_im, ofReal_re])).comp (f := fun u : Real => (a * I * u, I * u)) hf.continuousAt

/--
lemma `continuousOn_sinKernel` / 引理 `continuousOn_sinKernel`

English:
lemma continuousOn_sinKernel
  given: (a : UnitAddCircle)
  statement: ContinuousOn (sinKernel a) (Ioi 0)
  proof: by
  induction a using QuotientAddGroup.induction_on with | H a =>
  suffices ContinuousOn (fun x => (sinKernel a x : Complex)) (Ioi 0) from
    (continuous_re.comp_continuousOn this).congr fun a _ => (ofReal_re _).symm
  simp_rw [sinKernel_def]
  apply (continuousOn_of_forall_continuousAt (fun x hx

中文:
引理 continuousOn_sinKernel
  条件: (a : UnitAddCircle)
  结论: ContinuousOn (sinKernel a) (左开右无界区间 0)
  证明: by
  induction a using QuotientAddGroup.induction_on with | H a =>
  suffices ContinuousOn (fun x => (sinKernel a x : Complex)) (Ioi 0) from
    (continuous_re.comp_continuousOn this).congr fun a _ => (ofReal_re _).symm
  simp_rw [sinKernel_def]
  apply (continuousOn_of_forall_continuousAt (fun x hx

Depends on / 依赖: ContinuousOn, I_mul_im, QuotientAddGroup, QuotientAddGroup.induction_on, comp_continuousOn, continuousOn_of_forall_continuousAt, continuous_re, continuous_re.comp_continuousOn, div_const, fun_prop, induction_on, ofReal_re, simp_rw, sinKernel, sinKernel_def
-/
lemma continuousOn_sinKernel (a : UnitAddCircle) : ContinuousOn (sinKernel a) (Ioi 0) := by
  induction a using QuotientAddGroup.induction_on with | H a =>
  suffices ContinuousOn (fun x => (sinKernel a x : Complex)) (Ioi 0) from
    (continuous_re.comp_continuousOn this).congr fun a _ => (ofReal_re _).symm
  simp_rw [sinKernel_def]
  apply (continuousOn_of_forall_continuousAt (fun x hx => ?_)).div_const
  have h := continuousAt_jacobiTheta₂' a (by rwa [I_mul_im, ofReal_re])
  fun_prop

/--
lemma `oddKernel_functional_equation` / 引理 `oddKernel_functional_equation`

English:
lemma oddKernel_functional_equation
  given: (a : UnitAddCircle) (x : Real)
  proof: by
  -- first reduce to `0 < x`
  rcases le_or_gt x 0 with hx | hx
  · rw [oddKernel_undef _ hx, sinKernel_undef _ (one_div_nonpos.mpr hx), mul_zero]
  induction a using QuotientAddGroup.induction_on with | H a =>
  have h1 : -1 / (I * ↑(1 / x)) = I * x := by rw [one_div, ofReal_inv, mul_comm, ← div

中文:
引理 oddKernel_functional_equation
  条件: (a : UnitAddCircle) (x : 实数)
  证明: by
  -- first reduce to `0 < x`
  rcases le_or_gt x 0 with hx | hx
  · rw [oddKernel_undef _ hx, sinKernel_undef _ (one_div_nonpos.mpr hx), mul_zero]
  induction a using QuotientAddGroup.induction_on with | H a =>
  have h1 : -1 / (I * ↑(1 / x)) = I * x := by rw [one_div, ofReal_inv, mul_comm, ← div
-/
lemma oddKernel_functional_equation (a : UnitAddCircle) (x : Real) :
    oddKernel a x = 1 / x ^ (3 / 2 : Real) * sinKernel a (1 / x) := by
  -- first reduce to `0 < x`
  rcases le_or_gt x 0 with hx | hx
  · rw [oddKernel_undef _ hx, sinKernel_undef _ (one_div_nonpos.mpr hx), mul_zero]
  induction a using QuotientAddGroup.induction_on with | H a =>
  have h1 : -1 / (I * ↑(1 / x)) = I * x := by rw [one_div, ofReal_inv, mul_comm, ← div_div,
    div_inv_eq_mul, div_eq_mul_inv, inv_I, mul_neg, neg_one_mul, neg_mul, neg_neg, mul_comm]
  have h2 : (-I * (I * ↑(1 / x))) = 1 / x := by
    rw [← mul_assoc]; rw [neg_mul]; rw [I_mul_I]; rw [neg_neg]; rw [one_mul]; rw [ofReal_div]; rw [ofReal_one]
  have h3 : (x : Complex) ^ (3 / 2 : Complex) != 0 := by
    simp only [Ne, cpow_eq_zero_iff, ofReal_eq_zero, hx.ne', false_and, not_false_eq_true]
  have h4 : arg x != π := by rw [arg_ofReal_of_nonneg hx.le]; exact pi_ne_zero.symm
  rw [← ofReal_inj]; rw [oddKernel_def]; rw [ofReal_mul]; rw [sinKernel_def]; rw [jacobiTheta₂'_functional_equation']; rw [h1]; rw [h2]
  generalize jacobiTheta₂'' a (I * ↑x) = J
  rw [one_div (x : Complex)]; rw [inv_cpow _ _ h4]; rw [div_inv_eq_mul]; rw [one_div]; rw [ofReal_inv]; rw [ofReal_cpow hx.le]; rw [ofReal_div]; rw [ofReal_ofNat]; rw [ofReal_ofNat]; rw [← mul_div_assoc _ _ (-2 * π : Complex)]; rw [eq_div_iff mul_ne_zero (neg_ne_zero.mpr two_ne_zero) (ofReal_ne_zero.mpr pi_ne_zero)]; rw [← div_eq_inv_mul]; rw [eq_div_iff h3]; rw [mul_comm J _]; rw [mul_right_comm]

end kernel_defs

section sum_formulas


/--
lemma `hasSum_int_oddKernel` / 引理 `hasSum_int_oddKernel`

English:
lemma hasSum_int_oddKernel
  given: (a : Real) {x : Real} (hx : 0 < x)
  proof: by
  rw [← hasSum_ofReal]; rw [oddKernel_def' a x]
  have h1 := hasSum_jacobiTheta₂_term (a * I * x) (by rwa [I_mul_im, ofReal_re])
  have h2 := hasSum_jacobiTheta₂'_term (a * I * x) (by rwa [I_mul_im, ofReal_re])
  refine (((h2.div_const (2 * π * I)).add (h1.mul_left ↑a)).mul_left
    (cexp (-π * a

中文:
引理 hasSum_int_oddKernel
  条件: (a : 实数) {x : 实数} (hx : 0 < x)
  证明: by
  rw [← hasSum_ofReal]; rw [oddKernel_def' a x]
  have h1 := hasSum_jacobiTheta₂_term (a * I * x) (by rwa [I_mul_im, ofReal_re])
  have h2 := hasSum_jacobiTheta₂'_term (a * I * x) (by rwa [I_mul_im, ofReal_re])
  refine (((h2.div_const (2 * π * I)).add (h1.mul_left ↑a)).mul_left
    (cexp (-π * a

Depends on / 依赖: Complex.exp, I_mul_im, _term, add_mul, congr_fun, div_const, h1.mul_left, h2.div_const, hasSum_ofReal, mul_assoc, mul_left, mul_left_comm, oddKernel_def, ofReal_re, two_pi_I_ne_zero
-/
lemma hasSum_int_oddKernel (a : Real) {x : Real} (hx : 0 < x) :
    HasSum (fun n : Int => (n + a) * rexp (-π * (n + a) ^ 2 * x)) (oddKernel ↑a x) := by
  rw [← hasSum_ofReal]; rw [oddKernel_def' a x]
  have h1 := hasSum_jacobiTheta₂_term (a * I * x) (by rwa [I_mul_im, ofReal_re])
  have h2 := hasSum_jacobiTheta₂'_term (a * I * x) (by rwa [I_mul_im, ofReal_re])
  refine (((h2.div_const (2 * π * I)).add (h1.mul_left ↑a)).mul_left
    (cexp (-π * a ^ 2 * x))).congr_fun (fun n => ?_)
  rw [jacobiTheta₂'_term]; rw [mul_assoc (2 * π * I)]; rw [mul_div_cancel_left₀ _ two_pi_I_ne_zero]; rw [← add_mul]; rw [mul_left_comm]; rw [jacobiTheta₂_term]; rw [← Complex.exp_add]
  push_cast
  simp only [← mul_assoc, ← add_mul]
  congrm _ * cexp (?_ * x)
  simp only [mul_right_comm _ I, add_mul, mul_assoc _ I, I_mul_I]
  ring_nf

/--
lemma `hasSum_int_sinKernel` / 引理 `hasSum_int_sinKernel`

English:
lemma hasSum_int_sinKernel
  given: (a : Real) {t : Real} (ht : 0 < t)
  statement: HasSum
  proof: by
  have h : -2 * (π : Complex) != (0 : Complex) := by
    simp only [neg_mul, ne_eq, neg_eq_zero, mul_eq_zero,
      OfNat.ofNat_ne_zero, ofReal_eq_zero, pi_ne_zero, or_self, not_false_eq_true]
  rw [sinKernel_def]
  refine ((hasSum_jacobiTheta₂'_term a
    (by rwa [I_mul_im, ofReal_re])).div_cons

中文:
引理 hasSum_int_sinKernel
  条件: (a : 实数) {t : 实数} (ht : 0 < t)
  结论: HasSum
  证明: by
  have h : -2 * (π : Complex) != (0 : Complex) := by
    simp only [neg_mul, ne_eq, neg_eq_zero, mul_eq_zero,
      OfNat.ofNat_ne_zero, ofReal_eq_zero, pi_ne_zero, or_self, not_false_eq_true]
  rw [sinKernel_def]
  refine ((hasSum_jacobiTheta₂'_term a
    (by rwa [I_mul_im, ofReal_re])).div_cons

Depends on / 依赖: Complex.exp_add, I_mul_im, OfNat.ofNat_ne_zero, _term, congr_fun, div_const, eq_div_iff, exp_add, mul_assoc, mul_eq_zero, ne_eq, neg_eq_zero, neg_mul, not_false_eq_true, ofNat_ne_zero, ofReal_eq_zero, ofReal_exp, ofReal_mul, ofReal_pow, ofReal_re
-/
lemma hasSum_int_sinKernel (a : Real) {t : Real} (ht : 0 < t) : HasSum
    (fun n : Int => -I * n * cexp (2 * π * I * a * n) * rexp (-π * n ^ 2 * t)) ↑(sinKernel a t) := by
  have h : -2 * (π : Complex) != (0 : Complex) := by
    simp only [neg_mul, ne_eq, neg_eq_zero, mul_eq_zero,
      OfNat.ofNat_ne_zero, ofReal_eq_zero, pi_ne_zero, or_self, not_false_eq_true]
  rw [sinKernel_def]
  refine ((hasSum_jacobiTheta₂'_term a
    (by rwa [I_mul_im, ofReal_re])).div_const _).congr_fun fun n => ?_
  rw [jacobiTheta₂'_term]; rw [jacobiTheta₂_term]; rw [ofReal_exp]; rw [mul_assoc (-I * n)]; rw [← Complex.exp_add]; rw [eq_div_iff h]; rw [ofReal_mul]; rw [ofReal_mul]; rw [ofReal_pow]; rw [ofReal_neg]; rw [ofReal_intCast]; rw [mul_comm _ (-2 * π : Complex)]; rw [← mul_assoc]
  congrm ?_ * cexp (?_ + ?_)
  · simp [mul_assoc]
  · exact mul_right_comm (2 * π * I) a n
  · simp [← mul_assoc, mul_comm _ I]

/--
lemma `hasSum_nat_sinKernel` / 引理 `hasSum_nat_sinKernel`

English:
lemma hasSum_nat_sinKernel
  given: (a : Real) {t : Real} (ht : 0 < t)
  proof: by
  rw [← hasSum_ofReal]
  have := (hasSum_int_sinKernel a ht).nat_add_neg
  simp only [Int.cast_zero, zero_mul, mul_zero, add_zero] at this
  refine this.congr_fun fun n => ?_
  simp_rw [Int.cast_neg, neg_sq, mul_neg, ofReal_mul, Int.cast_natCast, ofReal_natCast,
      ofReal_ofNat, ← add_mul, ofR

中文:
引理 hasSum_nat_sinKernel
  条件: (a : 实数) {t : 实数} (ht : 0 < t)
  证明: by
  rw [← hasSum_ofReal]
  have := (hasSum_int_sinKernel a ht).nat_add_neg
  simp only [Int.cast_zero, zero_mul, mul_zero, add_zero] at this
  refine this.congr_fun fun n => ?_
  simp_rw [Int.cast_neg, neg_sq, mul_neg, ofReal_mul, Int.cast_natCast, ofReal_natCast,
      ofReal_ofNat, ← add_mul, ofR

Depends on / 依赖: Complex.sin, Int.cast_natCast, Int.cast_neg, Int.cast_zero, add_mul, add_zero, cast_natCast, cast_neg, cast_zero, congr_fun, div_mul_eq_mul_div, div_self, hasSum_int_sinKernel, hasSum_ofReal, mul_comm, mul_div_assoc, mul_neg, mul_zero, nat_add_neg, neg_mul
-/
lemma hasSum_nat_sinKernel (a : Real) {t : Real} (ht : 0 < t) :
    HasSum (fun n : Nat => 2 * n * Real.sin (2 * π * a * n) * rexp (-π * n ^ 2 * t))
    (sinKernel ↑a t) := by
  rw [← hasSum_ofReal]
  have := (hasSum_int_sinKernel a ht).nat_add_neg
  simp only [Int.cast_zero, zero_mul, mul_zero, add_zero] at this
  refine this.congr_fun fun n => ?_
  simp_rw [Int.cast_neg, neg_sq, mul_neg, ofReal_mul, Int.cast_natCast, ofReal_natCast,
      ofReal_ofNat, ← add_mul, ofReal_sin, Complex.sin]
  push_cast
  congr 1
  rw [← mul_div_assoc]; rw [← div_mul_eq_mul_div]; rw [← div_mul_eq_mul_div]; rw [div_self two_ne_zero]; rw [one_mul]; rw [neg_mul]; rw [neg_mul]; rw [neg_neg]; rw [mul_comm _ I]; rw [← mul_assoc]; rw [mul_comm _ I]; rw [neg_mul]; rw [← sub_eq_neg_add]; rw [mul_sub]
  congr 3 <;> ring

end sum_formulas

section asymp
/-!
## Asymptotics of the kernels as `t → ∞`
-/

/--
lemma `isBigO_atTop_oddKernel` / 引理 `isBigO_atTop_oddKernel`

English:
lemma isBigO_atTop_oddKernel
  given: (a : UnitAddCircle)
  proof: by
  induction a using QuotientAddGroup.induction_on with | H b =>
  obtain ⟨p, hp, hp'⟩ := HurwitzKernelBounds.isBigO_atTop_F_int_one b
  refine ⟨p, hp, (Eventually.isBigO ?_).trans hp'⟩
  filter_upwards [eventually_gt_atTop 0] with t ht
  simpa [← (hasSum_int_oddKernel b ht).tsum_eq, HurwitzKernel

中文:
引理 isBigO_atTop_oddKernel
  条件: (a : UnitAddCircle)
  证明: by
  induction a using QuotientAddGroup.induction_on with | H b =>
  obtain ⟨p, hp, hp'⟩ := HurwitzKernelBounds.isBigO_atTop_F_int_one b
  refine ⟨p, hp, (Eventually.isBigO ?_).trans hp'⟩
  filter_upwards [eventually_gt_atTop 0] with t ht
  simpa [← (hasSum_int_oddKernel b ht).tsum_eq, HurwitzKernel

Depends on / 依赖: Eventually, Eventually.isBigO, F_int, HurwitzKernelBounds, HurwitzKernelBounds.F_int, HurwitzKernelBounds.f_int, HurwitzKernelBounds.isBigO_atTop_F_int_one, QuotientAddGroup, QuotientAddGroup.induction_on, abs_of_nonneg, eventually_gt_atTop, exp_pos, f_int, filter_upwards, hasSum_int_oddKernel, induction_on, isBigO, isBigO_atTop_F_int_one, norm_tsum_le_tsum_norm, summable
-/
lemma isBigO_atTop_oddKernel (a : UnitAddCircle) :
    exists p, 0 < p ∧ IsBigO atTop (oddKernel a) (fun x => Real.exp (-p * x)) := by
  induction a using QuotientAddGroup.induction_on with | H b =>
  obtain ⟨p, hp, hp'⟩ := HurwitzKernelBounds.isBigO_atTop_F_int_one b
  refine ⟨p, hp, (Eventually.isBigO ?_).trans hp'⟩
  filter_upwards [eventually_gt_atTop 0] with t ht
  simpa [← (hasSum_int_oddKernel b ht).tsum_eq, HurwitzKernelBounds.F_int,
    HurwitzKernelBounds.f_int, abs_of_nonneg (exp_pos _).le] using
    norm_tsum_le_tsum_norm (hasSum_int_oddKernel b ht).summable.norm

/--
lemma `isBigO_atTop_sinKernel` / 引理 `isBigO_atTop_sinKernel`

English:
lemma isBigO_atTop_sinKernel
  given: (a : UnitAddCircle)
  proof: by
  induction a using QuotientAddGroup.induction_on with | H a =>
  obtain ⟨p, hp, hp'⟩ := HurwitzKernelBounds.isBigO_atTop_F_nat_one (le_refl 0)
  refine ⟨p, hp, (Eventually.isBigO ?_).trans (hp'.const_mul_left 2)⟩
  filter_upwards [eventually_gt_atTop 0] with t ht
  rw [HurwitzKernelBounds.F_nat]

中文:
引理 isBigO_atTop_sinKernel
  条件: (a : UnitAddCircle)
  证明: by
  induction a using QuotientAddGroup.induction_on with | H a =>
  obtain ⟨p, hp, hp'⟩ := HurwitzKernelBounds.isBigO_atTop_F_nat_one (le_refl 0)
  refine ⟨p, hp, (Eventually.isBigO ?_).trans (hp'.const_mul_left 2)⟩
  filter_upwards [eventually_gt_atTop 0] with t ht
  rw [HurwitzKernelBounds.F_nat]

Depends on / 依赖: Eventually, Eventually.isBigO, F_nat, HurwitzKernelBounds, HurwitzKernelBounds.F_nat, HurwitzKernelBounds.f_nat, HurwitzKernelBounds.isBigO_atTop_F_nat_one, HurwitzKernelBounds.summable_f_nat, QuotientAddGroup, QuotientAddGroup.induction_on, const_mul_left, eventually_gt_atTop, f_nat, filter_upwards, hasSum, hasSum.mul_left, hasSum_nat_sinKernel, induction_on, isBigO, isBigO_atTop_F_nat_one
-/
lemma isBigO_atTop_sinKernel (a : UnitAddCircle) :
    exists p, 0 < p ∧ IsBigO atTop (sinKernel a) (fun x => Real.exp (-p * x)) := by
  induction a using QuotientAddGroup.induction_on with | H a =>
  obtain ⟨p, hp, hp'⟩ := HurwitzKernelBounds.isBigO_atTop_F_nat_one (le_refl 0)
  refine ⟨p, hp, (Eventually.isBigO ?_).trans (hp'.const_mul_left 2)⟩
  filter_upwards [eventually_gt_atTop 0] with t ht
  rw [HurwitzKernelBounds.F_nat]; rw [← (hasSum_nat_sinKernel a ht).tsum_eq]
  apply tsum_of_norm_bounded (g := fun n => 2 * HurwitzKernelBounds.f_nat 1 0 t n)
  · exact (HurwitzKernelBounds.summable_f_nat 1 0 ht).hasSum.mul_left _
  · intro n
    rw [norm_mul]; rw [norm_mul]; rw [norm_mul]; rw [norm_two]; rw [mul_assoc]; rw [mul_assoc]; rw [mul_le_mul_iff_of_pos_left two_pos]; rw [HurwitzKernelBounds.f_nat]; rw [pow_one]; rw [add_zero]; rw [norm_of_nonneg (exp_pos _).le]; rw [Real.norm_eq_abs]; rw [Nat.abs_cast]; rw [← mul_assoc]; rw [mul_le_mul_iff_of_pos_right (exp_pos _)]
    exact mul_le_of_le_one_right (Nat.cast_nonneg _) (abs_sin_le_one _)

end asymp

section FEPair
/-!
## Construction of an FE-pair
-/

/-- A `StrongFEPair` structure with `f = oddKernel a` and `g = sinKernel a`. -/
@[simps]
/--
Definition of `hurwitzOddFEPair` / `hurwitzOddFEPair` 的定义

English:
definition hurwitzOddFEPair
  signature: (a : UnitAddCircle)
  body: ofReal ∘ oddKernel a
  g := ofReal ∘ sinKernel a
  hf_int := (continuous_ofReal.comp_continuousOn (continuousOn_oddKernel a)).locallyIntegrableOn
    measurableSet_Ioi
  hg_int := (continuous_ofReal.comp_continuousOn (continuousOn_sinKernel a)).locallyIntegrableOn
    measurableSet_Ioi
  k := 3 / 2


中文:
定义 hurwitzOddFEPair
  签名: (a : UnitAddCircle)
  定义体: ofReal ∘ oddKernel a
  g := ofReal ∘ sinKernel a
  hf_int := (continuous_ofReal.comp_continuousOn (continuousOn_oddKernel a)).locallyIntegrableOn
    measurableSet_Ioi
  hg_int := (continuous_ofReal.comp_continuousOn (continuousOn_sinKernel a)).locallyIntegrableOn
    measurableSet_Ioi
  k := 3 / 2


Depends on / 依赖: oddKernel, ofReal
-/
def hurwitzOddFEPair (a : UnitAddCircle) : WeakFEPair Complex where
  f := ofReal ∘ oddKernel a
  g := ofReal ∘ sinKernel a
  hf_int := (continuous_ofReal.comp_continuousOn (continuousOn_oddKernel a)).locallyIntegrableOn
    measurableSet_Ioi
  hg_int := (continuous_ofReal.comp_continuousOn (continuousOn_sinKernel a)).locallyIntegrableOn
    measurableSet_Ioi
  k := 3 / 2
  hk := by norm_num
  ε := 1
  hε := one_ne_zero
  f₀ := 0
  g₀ := 0
  hf_top r := by
    let ⟨v, hv, hv'⟩ := isBigO_atTop_oddKernel a
    rw [← isBigO_norm_left] at hv' ⊢
    simpa using hv'.trans (isLittleO_exp_neg_mul_rpow_atTop hv _).isBigO
  hg_top r := by
    let ⟨v, hv, hv'⟩ := isBigO_atTop_sinKernel a
    rw [← isBigO_norm_left] at hv' ⊢
    simpa using hv'.trans (isLittleO_exp_neg_mul_rpow_atTop hv _).isBigO
  h_feq x hx := by simp [← ofReal_mul, oddKernel_functional_equation a, inv_rpow (le_of_lt hx)]

/--
lemma `isStrong_hurwitzOddFEPair` / 引理 `isStrong_hurwitzOddFEPair`

English:
lemma isStrong_hurwitzOddFEPair
  given: (a : UnitAddCircle)
  statement: IsStrongFEPair (hurwitzOddFEPair a) where
  proof: rfl
  hg₀ := rfl

中文:
引理 isStrong_hurwitzOddFEPair
  条件: (a : UnitAddCircle)
  结论: 是StrongFEPair (hurwitzOddFEPair a) where
  证明: rfl
  hg₀ := rfl
-/
lemma isStrong_hurwitzOddFEPair (a : UnitAddCircle) : IsStrongFEPair (hurwitzOddFEPair a) where
  hf₀ := rfl
  hg₀ := rfl

end FEPair

/-!
## Definition of the completed odd Hurwitz zeta function
-/

/--
Definition of `completedHurwitzZetaOdd` / `completedHurwitzZetaOdd` 的定义

English:
definition completedHurwitzZetaOdd
  signature: (a : UnitAddCircle) (s : Complex)
  body: ((hurwitzOddFEPair a).Λ ((s + 1) / 2)) / 2

中文:
定义 completedHurwitzZetaOdd
  签名: (a : UnitAddCircle) (s : 复形)
  定义体: ((hurwitzOddFEPair a).Λ ((s + 1) / 2)) / 2

Depends on / 依赖: hurwitzOddFEPair
-/
def completedHurwitzZetaOdd (a : UnitAddCircle) (s : Complex) : Complex :=
  ((hurwitzOddFEPair a).Λ ((s + 1) / 2)) / 2

/--
lemma `differentiable_completedHurwitzZetaOdd` / 引理 `differentiable_completedHurwitzZetaOdd`

English:
lemma differentiable_completedHurwitzZetaOdd
  given: (a : UnitAddCircle)
  proof: ((isStrong_hurwitzOddFEPair a).differentiable_Λ.comp
    ((differentiable_id.add_const 1).div_const 2)).div_const 2

中文:
引理 differentiable_completedHurwitzZetaOdd
  条件: (a : UnitAddCircle)
  证明: ((isStrong_hurwitzOddFEPair a).differentiable_Λ.comp
    ((differentiable_id.add_const 1).div_const 2)).div_const 2

Depends on / 依赖: add_const, differentiable_id, differentiable_id.add_const, div_const, isStrong_hurwitzOddFEPair
-/
lemma differentiable_completedHurwitzZetaOdd (a : UnitAddCircle) :
    Differentiable Complex (completedHurwitzZetaOdd a) :=
  ((isStrong_hurwitzOddFEPair a).differentiable_Λ.comp
    ((differentiable_id.add_const 1).div_const 2)).div_const 2

/--
Definition of `completedSinZeta` / `completedSinZeta` 的定义

English:
definition completedSinZeta
  signature: (a : UnitAddCircle) (s : Complex)
  body: ((hurwitzOddFEPair a).symm.Λ ((s + 1) / 2)) / 2

中文:
定义 completedSinZeta
  签名: (a : UnitAddCircle) (s : 复形)
  定义体: ((hurwitzOddFEPair a).symm.Λ ((s + 1) / 2)) / 2

Depends on / 依赖: hurwitzOddFEPair
-/
def completedSinZeta (a : UnitAddCircle) (s : Complex) : Complex :=
  ((hurwitzOddFEPair a).symm.Λ ((s + 1) / 2)) / 2

/--
lemma `differentiable_completedSinZeta` / 引理 `differentiable_completedSinZeta`

English:
lemma differentiable_completedSinZeta
  given: (a : UnitAddCircle)
  proof: ((isStrong_hurwitzOddFEPair a).symm.differentiable_Λ.comp
    ((differentiable_id.add_const 1).div_const 2)).div_const 2

中文:
引理 differentiable_completedSinZeta
  条件: (a : UnitAddCircle)
  证明: ((isStrong_hurwitzOddFEPair a).symm.differentiable_Λ.comp
    ((differentiable_id.add_const 1).div_const 2)).div_const 2

Depends on / 依赖: add_const, differentiable_id, differentiable_id.add_const, div_const, isStrong_hurwitzOddFEPair, symm.differentiable_
-/
lemma differentiable_completedSinZeta (a : UnitAddCircle) :
    Differentiable Complex (completedSinZeta a) :=
  ((isStrong_hurwitzOddFEPair a).symm.differentiable_Λ.comp
    ((differentiable_id.add_const 1).div_const 2)).div_const 2


/--
lemma `completedHurwitzZetaOdd_neg` / 引理 `completedHurwitzZetaOdd_neg`

English:
lemma completedHurwitzZetaOdd_neg
  given: (a : UnitAddCircle) (s : Complex)
  proof: by
  simp [completedHurwitzZetaOdd, (isStrong_hurwitzOddFEPair _).Λ_eq, mellin,
    oddKernel_neg, integral_neg, neg_div]

中文:
引理 completedHurwitzZetaOdd_neg
  条件: (a : UnitAddCircle) (s : 复形)
  证明: by
  simp [completedHurwitzZetaOdd, (isStrong_hurwitzOddFEPair _).Λ_eq, mellin,
    oddKernel_neg, integral_neg, neg_div]

Depends on / 依赖: completedHurwitzZetaOdd, integral_neg, isStrong_hurwitzOddFEPair, mellin, neg_div, oddKernel_neg
-/
lemma completedHurwitzZetaOdd_neg (a : UnitAddCircle) (s : Complex) :
    completedHurwitzZetaOdd (-a) s = -completedHurwitzZetaOdd a s := by
  simp [completedHurwitzZetaOdd, (isStrong_hurwitzOddFEPair _).Λ_eq, mellin,
    oddKernel_neg, integral_neg, neg_div]

/--
lemma `completedSinZeta_neg` / 引理 `completedSinZeta_neg`

English:
lemma completedSinZeta_neg
  given: (a : UnitAddCircle) (s : Complex)
  proof: by
  simp [completedSinZeta, (isStrong_hurwitzOddFEPair _).symm_Λ_eq, mellin, sinKernel_neg,
    integral_neg, neg_div]

中文:
引理 completedSinZeta_neg
  条件: (a : UnitAddCircle) (s : 复形)
  证明: by
  simp [completedSinZeta, (isStrong_hurwitzOddFEPair _).symm_Λ_eq, mellin, sinKernel_neg,
    integral_neg, neg_div]

Depends on / 依赖: completedSinZeta, integral_neg, isStrong_hurwitzOddFEPair, mellin, neg_div, sinKernel_neg
-/
lemma completedSinZeta_neg (a : UnitAddCircle) (s : Complex) :
    completedSinZeta (-a) s = -completedSinZeta a s := by
  simp [completedSinZeta, (isStrong_hurwitzOddFEPair _).symm_Λ_eq, mellin, sinKernel_neg,
    integral_neg, neg_div]

/--
theorem `completedHurwitzZetaOdd_one_sub` / 定理 `completedHurwitzZetaOdd_one_sub`

English:
theorem completedHurwitzZetaOdd_one_sub
  given: (a : UnitAddCircle) (s : Complex)
  proof: by
  rw [completedHurwitzZetaOdd]; rw [completedSinZeta]; rw [(by { push_cast; ring } : (1 - s + 1) / 2 = ↑(3 / 2 : Real) - (s + 1) / 2)]; rw [← hurwitzOddFEPair_k]; rw [(hurwitzOddFEPair a).functional_equation ((s + 1) / 2)]; rw [hurwitzOddFEPair_ε]; rw [one_smul]

中文:
定理 completedHurwitzZetaOdd_one_sub
  条件: (a : UnitAddCircle) (s : 复形)
  证明: by
  rw [completedHurwitzZetaOdd]; rw [completedSinZeta]; rw [(by { push_cast; ring } : (1 - s + 1) / 2 = ↑(3 / 2 : Real) - (s + 1) / 2)]; rw [← hurwitzOddFEPair_k]; rw [(hurwitzOddFEPair a).functional_equation ((s + 1) / 2)]; rw [hurwitzOddFEPair_ε]; rw [one_smul]

Depends on / 依赖: completedHurwitzZetaOdd, completedSinZeta, functional_equation, hurwitzOddFEPair, hurwitzOddFEPair_k, one_smul
-/
theorem completedHurwitzZetaOdd_one_sub (a : UnitAddCircle) (s : Complex) :
    completedHurwitzZetaOdd a (1 - s) = completedSinZeta a s := by
  rw [completedHurwitzZetaOdd]; rw [completedSinZeta]; rw [(by { push_cast; ring } : (1 - s + 1) / 2 = ↑(3 / 2 : Real) - (s + 1) / 2)]; rw [← hurwitzOddFEPair_k]; rw [(hurwitzOddFEPair a).functional_equation ((s + 1) / 2)]; rw [hurwitzOddFEPair_ε]; rw [one_smul]

/--
lemma `completedSinZeta_one_sub` / 引理 `completedSinZeta_one_sub`

English:
lemma completedSinZeta_one_sub
  given: (a : UnitAddCircle) (s : Complex)
  proof: by
  simp [← completedHurwitzZetaOdd_one_sub]

中文:
引理 completedSinZeta_one_sub
  条件: (a : UnitAddCircle) (s : 复形)
  证明: by
  simp [← completedHurwitzZetaOdd_one_sub]

Depends on / 依赖: completedHurwitzZetaOdd_one_sub
-/
lemma completedSinZeta_one_sub (a : UnitAddCircle) (s : Complex) :
    completedSinZeta a (1 - s) = completedHurwitzZetaOdd a s := by
  simp [← completedHurwitzZetaOdd_one_sub]

/-!
## Relation to the Dirichlet series for `1 < re s`
-/

/--
lemma `hasSum_int_completedSinZeta` / 引理 `hasSum_int_completedSinZeta`

English:
lemma hasSum_int_completedSinZeta
  given: (a : Real) {s : Complex} (hs : 1 < re s)
  proof: by
  let c (n : Int) : Complex := -I * cexp (2 * π * I * a * n) / 2
  have hc (n : Int) : ‖c n‖ = 1 / 2 := by
    simp_rw [c, (by { push_cast; ring } : 2 * π * I * a * n = ↑(2 * π * a * n) * I), norm_div,
      RCLike.norm_ofNat, norm_mul, norm_neg, norm_I, one_mul, norm_exp_ofReal_mul_I]
  have hF 

中文:
引理 hasSum_int_completedSinZeta
  条件: (a : 实数) {s : 复形} (hs : 1 < re s)
  证明: by
  let c (n : Int) : Complex := -I * cexp (2 * π * I * a * n) / 2
  have hc (n : Int) : ‖c n‖ = 1 / 2 := by
    simp_rw [c, (by { push_cast; ring } : 2 * π * I * a * n = ↑(2 * π * a * n) * I), norm_div,
      RCLike.norm_ofNat, norm_mul, norm_neg, norm_I, one_mul, norm_exp_ofReal_mul_I]
  have hF 

Depends on / 依赖: HasSum, RCLike, RCLike.norm_ofNat, congr_fun, div_const, div_mul_eq_mul_div, hasSum_int_sinKernel, norm_I, norm_div, norm_exp_ofReal_mul_I, norm_mul, norm_neg, norm_ofNat, one_mul, simp_rw, sinKernel
-/
lemma hasSum_int_completedSinZeta (a : Real) {s : Complex} (hs : 1 < re s) :
    HasSum (fun n : Int => GammaReal (s + 1) * (-I) * Int.sign n *
    cexp (2 * π * I * a * n) / (↑|n| : Complex) ^ s / 2) (completedSinZeta a s) := by
  let c (n : Int) : Complex := -I * cexp (2 * π * I * a * n) / 2
  have hc (n : Int) : ‖c n‖ = 1 / 2 := by
    simp_rw [c, (by { push_cast; ring } : 2 * π * I * a * n = ↑(2 * π * a * n) * I), norm_div,
      RCLike.norm_ofNat, norm_mul, norm_neg, norm_I, one_mul, norm_exp_ofReal_mul_I]
  have hF t (ht : 0 < t) :
      HasSum (fun n => c n * n * rexp (-π * n ^ 2 * t)) (sinKernel a t / 2) := by
    refine ((hasSum_int_sinKernel a ht).div_const 2).congr_fun fun n => ?_
    rw [div_mul_eq_mul_div]; rw [div_mul_eq_mul_div]; rw [mul_right_comm (-I)]
  have h_sum : Summable fun i => ‖c i‖ / |↑i| ^ s.re := by
    simp_rw [hc, div_right_comm]
    apply Summable.div_const
    apply Summable.of_nat_of_neg <;>
    simpa
  rw [completedSinZeta]; rw [(isStrong_hurwitzOddFEPair _).symm_Λ_eq]
  refine (mellin_div_const .. ▸ hasSum_mellin_pi_mul_sq' (zero_lt_one.trans hs) hF h_sum).congr_fun
    fun n => ?_
  simp [Int.sign_eq_sign, ← Int.cast_abs] -- non-terminal simp OK when `ring` follows
  ring

/--
lemma `hasSum_nat_completedSinZeta` / 引理 `hasSum_nat_completedSinZeta`

English:
lemma hasSum_nat_completedSinZeta
  given: (a : Real) {s : Complex} (hs : 1 < re s)
  proof: by
  have := (hasSum_int_completedSinZeta a hs).nat_add_neg
  simp_rw [Int.sign_zero, Int.cast_zero, mul_zero, zero_mul, zero_div, add_zero, abs_neg,
    Int.sign_neg, Nat.abs_cast, Int.cast_neg, Int.cast_natCast, ← add_div] at this
  refine this.congr_fun fun n => ?_
  rw [div_right_comm]
  rcases 

中文:
引理 hasSum_nat_completedSinZeta
  条件: (a : 实数) {s : 复形} (hs : 1 < re s)
  证明: by
  have := (hasSum_int_completedSinZeta a hs).nat_add_neg
  simp_rw [Int.sign_zero, Int.cast_zero, mul_zero, zero_mul, zero_div, add_zero, abs_neg,
    Int.sign_neg, Nat.abs_cast, Int.cast_neg, Int.cast_natCast, ← add_div] at this
  refine this.congr_fun fun n => ?_
  rw [div_right_comm]
  rcases 

Depends on / 依赖: Complex.sin, GammaReal, Int.cast_natCast, Int.cast_neg, Int.cast_one, Int.cast_zero, Int.sign_natCast_of_ne_zero, Int.sign_neg, Int.sign_zero, Nat.abs_cast, abs_cast, abs_neg, add_div, add_zero, cast_natCast, cast_neg, cast_one, cast_zero, congr_fun, div_right_comm
-/
lemma hasSum_nat_completedSinZeta (a : Real) {s : Complex} (hs : 1 < re s) :
    HasSum (fun n : Nat => GammaReal (s + 1) * Real.sin (2 * π * a * n) / (n : Complex) ^ s)
    (completedSinZeta a s) := by
  have := (hasSum_int_completedSinZeta a hs).nat_add_neg
  simp_rw [Int.sign_zero, Int.cast_zero, mul_zero, zero_mul, zero_div, add_zero, abs_neg,
    Int.sign_neg, Nat.abs_cast, Int.cast_neg, Int.cast_natCast, ← add_div] at this
  refine this.congr_fun fun n => ?_
  rw [div_right_comm]
  rcases eq_or_ne n 0 with rfl | h
  · simp
  simp_rw [Int.sign_natCast_of_ne_zero h, Int.cast_one, ofReal_sin, Complex.sin]
  simp only [← mul_div_assoc, push_cast, mul_assoc (GammaReal _), ← mul_add]
  congr 3
  rw [mul_one]; rw [mul_neg_one]; rw [neg_neg]; rw [neg_mul I]; rw [← sub_eq_neg_add]; rw [← mul_sub]; rw [mul_comm]; rw [mul_neg]; rw [neg_mul]
  congr 3 <;> ring

/--
lemma `hasSum_int_completedHurwitzZetaOdd` / 引理 `hasSum_int_completedHurwitzZetaOdd`

English:
lemma hasSum_int_completedHurwitzZetaOdd
  given: (a : Real) {s : Complex} (hs : 1 < re s)
  proof: by
  let r (n : Int) : Real := n + a
  let c (n : Int) : Complex := 1 / 2
  have hF t (ht : 0 < t) : HasSum (fun n => c n * r n * rexp (-π * (r n) ^ 2 * t))
      (oddKernel a t / 2) := by
    refine ((hasSum_ofReal.mpr (hasSum_int_oddKernel a ht)).div_const 2).congr_fun fun n => ?_
    simp [r, c, 

中文:
引理 hasSum_int_completedHurwitzZetaOdd
  条件: (a : 实数) {s : 复形} (hs : 1 < re s)
  证明: by
  let r (n : Int) : Real := n + a
  let c (n : Int) : Complex := 1 / 2
  have hF t (ht : 0 < t) : HasSum (fun n => c n * r n * rexp (-π * (r n) ^ 2 * t))
      (oddKernel a t / 2) := by
    refine ((hasSum_ofReal.mpr (hasSum_int_oddKernel a ht)).div_const 2).congr_fun fun n => ?_
    simp [r, c, 

Depends on / 依赖: HasSum, Summable, Summable.mul_left, completedHurwitzZetaOdd, congr_fun, div_const, div_mul_eq_mul_div, h_sum, hasSum_int_oddKernel, hasSum_ofReal, hasSum_ofReal.mpr, mul_left, mul_one_div, oddKernel, one_div, s.re, simp_rw, summable_one_div_int_add_rpow
-/
lemma hasSum_int_completedHurwitzZetaOdd (a : Real) {s : Complex} (hs : 1 < re s) :
    HasSum (fun n : Int => GammaReal (s + 1) * SignType.sign (n + a) / (↑|n + a| : Complex) ^ s / 2)
    (completedHurwitzZetaOdd a s) := by
  let r (n : Int) : Real := n + a
  let c (n : Int) : Complex := 1 / 2
  have hF t (ht : 0 < t) : HasSum (fun n => c n * r n * rexp (-π * (r n) ^ 2 * t))
      (oddKernel a t / 2) := by
    refine ((hasSum_ofReal.mpr (hasSum_int_oddKernel a ht)).div_const 2).congr_fun fun n => ?_
    simp [r, c, push_cast, div_mul_eq_mul_div, -one_div]
  have h_sum : Summable fun i => ‖c i‖ / |r i| ^ s.re := by
    simp_rw [c, ← mul_one_div ‖_‖]
    apply Summable.mul_left
    rwa [summable_one_div_int_add_rpow]
  rw [completedHurwitzZetaOdd]; rw [(isStrong_hurwitzOddFEPair _).Λ_eq]
  have := mellin_div_const .. ▸ hasSum_mellin_pi_mul_sq' (zero_lt_one.trans hs) hF h_sum
  refine this.congr_fun fun n => ?_
  simp only [r, c, mul_one_div, div_mul_eq_mul_div, div_right_comm]

/-!
## Non-completed zeta functions
-/

/--
Definition of `hurwitzZetaOdd` / `hurwitzZetaOdd` 的定义

English:
definition hurwitzZetaOdd
  signature: (a : UnitAddCircle) (s : Complex)
  body: completedHurwitzZetaOdd a s / GammaReal (s + 1)

中文:
定义 hurwitzZetaOdd
  签名: (a : UnitAddCircle) (s : 复形)
  定义体: completedHurwitzZetaOdd a s / GammaReal (s + 1)

Depends on / 依赖: GammaReal, completedHurwitzZetaOdd
-/
noncomputable def hurwitzZetaOdd (a : UnitAddCircle) (s : Complex) :=
  completedHurwitzZetaOdd a s / GammaReal (s + 1)

/--
lemma `hurwitzZetaOdd_neg` / 引理 `hurwitzZetaOdd_neg`

English:
lemma hurwitzZetaOdd_neg
  given: (a : UnitAddCircle) (s : Complex)
  proof: by
  simp_rw [hurwitzZetaOdd, completedHurwitzZetaOdd_neg, neg_div]

中文:
引理 hurwitzZetaOdd_neg
  条件: (a : UnitAddCircle) (s : 复形)
  证明: by
  simp_rw [hurwitzZetaOdd, completedHurwitzZetaOdd_neg, neg_div]

Depends on / 依赖: completedHurwitzZetaOdd_neg, hurwitzZetaOdd, neg_div, simp_rw
-/
lemma hurwitzZetaOdd_neg (a : UnitAddCircle) (s : Complex) :
    hurwitzZetaOdd (-a) s = -hurwitzZetaOdd a s := by
  simp_rw [hurwitzZetaOdd, completedHurwitzZetaOdd_neg, neg_div]

/--
lemma `differentiable_hurwitzZetaOdd` / 引理 `differentiable_hurwitzZetaOdd`

English:
lemma differentiable_hurwitzZetaOdd
  given: (a : UnitAddCircle)
  proof: (differentiable_completedHurwitzZetaOdd a).mul differentiable_GammaReal_inv.comp
differentiable_id.add differentiable_const _

中文:
引理 differentiable_hurwitzZetaOdd
  条件: (a : UnitAddCircle)
  证明: (differentiable_completedHurwitzZetaOdd a).mul differentiable_GammaReal_inv.comp
differentiable_id.add differentiable_const _

Depends on / 依赖: differentiable_GammaReal_inv, differentiable_GammaReal_inv.comp, differentiable_completedHurwitzZetaOdd, differentiable_const, differentiable_id, differentiable_id.add
-/
lemma differentiable_hurwitzZetaOdd (a : UnitAddCircle) :
    Differentiable Complex (hurwitzZetaOdd a) :=
(differentiable_completedHurwitzZetaOdd a).mul differentiable_GammaReal_inv.comp
differentiable_id.add differentiable_const _

/--
Definition of `sinZeta` / `sinZeta` 的定义

English:
definition sinZeta
  signature: (a : UnitAddCircle) (s : Complex)
  body: completedSinZeta a s / GammaReal (s + 1)

中文:
定义 sinZeta
  签名: (a : UnitAddCircle) (s : 复形)
  定义体: completedSinZeta a s / GammaReal (s + 1)

Depends on / 依赖: GammaReal, completedSinZeta
-/
noncomputable def sinZeta (a : UnitAddCircle) (s : Complex) :=
  completedSinZeta a s / GammaReal (s + 1)

/--
lemma `sinZeta_neg` / 引理 `sinZeta_neg`

English:
lemma sinZeta_neg
  given: (a : UnitAddCircle) (s : Complex)
  proof: by
  simp_rw [sinZeta, completedSinZeta_neg, neg_div]

中文:
引理 sinZeta_neg
  条件: (a : UnitAddCircle) (s : 复形)
  证明: by
  simp_rw [sinZeta, completedSinZeta_neg, neg_div]

Depends on / 依赖: completedSinZeta_neg, neg_div, simp_rw, sinZeta
-/
lemma sinZeta_neg (a : UnitAddCircle) (s : Complex) :
    sinZeta (-a) s = -sinZeta a s := by
  simp_rw [sinZeta, completedSinZeta_neg, neg_div]

/--
lemma `differentiableAt_sinZeta` / 引理 `differentiableAt_sinZeta`

English:
lemma differentiableAt_sinZeta
  given: (a : UnitAddCircle)
  proof: (differentiable_completedSinZeta a).mul differentiable_GammaReal_inv.comp
differentiable_id.add differentiable_const _

中文:
引理 differentiableAt_sinZeta
  条件: (a : UnitAddCircle)
  证明: (differentiable_completedSinZeta a).mul differentiable_GammaReal_inv.comp
differentiable_id.add differentiable_const _

Depends on / 依赖: differentiable_GammaReal_inv, differentiable_GammaReal_inv.comp, differentiable_completedSinZeta, differentiable_const, differentiable_id, differentiable_id.add
-/
lemma differentiableAt_sinZeta (a : UnitAddCircle) :
    Differentiable Complex (sinZeta a) :=
(differentiable_completedSinZeta a).mul differentiable_GammaReal_inv.comp
differentiable_id.add differentiable_const _

/--
theorem `hasSum_int_hurwitzZetaOdd` / 定理 `hasSum_int_hurwitzZetaOdd`

English:
theorem hasSum_int_hurwitzZetaOdd
  given: (a : Real) {s : Complex} (hs : 1 < re s)
  proof: by
  refine ((hasSum_int_completedHurwitzZetaOdd a hs).div_const (GammaReal _)).congr_fun fun n => ?_
  have : 0 < re (s + 1) := by rw [add_re, one_re]; positivity
  simp [div_right_comm _ _ (GammaReal _), mul_div_cancel_left₀ _ (GammaReal_ne_zero_of_re_pos this)]

中文:
定理 hasSum_int_hurwitzZetaOdd
  条件: (a : 实数) {s : 复形} (hs : 1 < re s)
  证明: by
  refine ((hasSum_int_completedHurwitzZetaOdd a hs).div_const (GammaReal _)).congr_fun fun n => ?_
  have : 0 < re (s + 1) := by rw [add_re, one_re]; positivity
  simp [div_right_comm _ _ (GammaReal _), mul_div_cancel_left₀ _ (GammaReal_ne_zero_of_re_pos this)]

Depends on / 依赖: GammaReal, GammaReal_ne_zero_of_re_pos, add_re, congr_fun, div_const, div_right_comm, hasSum_int_completedHurwitzZetaOdd, one_re
-/
theorem hasSum_int_hurwitzZetaOdd (a : Real) {s : Complex} (hs : 1 < re s) :
    HasSum (fun n : Int => SignType.sign (n + a) / (↑|n + a| : Complex) ^ s / 2) (hurwitzZetaOdd a s) := by
  refine ((hasSum_int_completedHurwitzZetaOdd a hs).div_const (GammaReal _)).congr_fun fun n => ?_
  have : 0 < re (s + 1) := by rw [add_re, one_re]; positivity
  simp [div_right_comm _ _ (GammaReal _), mul_div_cancel_left₀ _ (GammaReal_ne_zero_of_re_pos this)]

/--
lemma `hasSum_nat_hurwitzZetaOdd` / 引理 `hasSum_nat_hurwitzZetaOdd`

English:
lemma hasSum_nat_hurwitzZetaOdd
  given: (a : Real) {s : Complex} (hs : 1 < re s)
  proof: by
  refine (hasSum_int_hurwitzZetaOdd a hs).nat_add_neg_add_one.congr_fun fun n => ?_
  rw [Int.cast_neg]; rw [Int.cast_add]; rw [Int.cast_one]; rw [sub_div]; rw [sub_eq_add_neg]; rw [Int.cast_natCast]
  have : -(n + 1) + a = -(n + 1 - a) := by ring_nf
  rw [this]; rw [Left.sign_neg]; rw [abs_neg];

中文:
引理 hasSum_nat_hurwitzZetaOdd
  条件: (a : 实数) {s : 复形} (hs : 1 < re s)
  证明: by
  refine (hasSum_int_hurwitzZetaOdd a hs).nat_add_neg_add_one.congr_fun fun n => ?_
  rw [Int.cast_neg]; rw [Int.cast_add]; rw [Int.cast_one]; rw [sub_div]; rw [sub_eq_add_neg]; rw [Int.cast_natCast]
  have : -(n + 1) + a = -(n + 1 - a) := by ring_nf
  rw [this]; rw [Left.sign_neg]; rw [abs_neg];

Depends on / 依赖: Int.cast_add, Int.cast_natCast, Int.cast_neg, Int.cast_one, Left.sign_neg, SignType, SignType.coe_neg, abs_neg, cast_add, cast_natCast, cast_neg, cast_one, coe_neg, congr_fun, hasSum_int_hurwitzZetaOdd, nat_add_neg_add_one, nat_add_neg_add_one.congr_fun, neg_div, ring_nf, sign_neg
-/
lemma hasSum_nat_hurwitzZetaOdd (a : Real) {s : Complex} (hs : 1 < re s) :
    HasSum (fun n : Nat => (SignType.sign (n + a) / (↑|n + a| : Complex) ^ s
      - SignType.sign (n + 1 - a) / (↑|n + 1 - a| : Complex) ^ s) / 2) (hurwitzZetaOdd a s) := by
  refine (hasSum_int_hurwitzZetaOdd a hs).nat_add_neg_add_one.congr_fun fun n => ?_
  rw [Int.cast_neg]; rw [Int.cast_add]; rw [Int.cast_one]; rw [sub_div]; rw [sub_eq_add_neg]; rw [Int.cast_natCast]
  have : -(n + 1) + a = -(n + 1 - a) := by ring_nf
  rw [this]; rw [Left.sign_neg]; rw [abs_neg]; rw [SignType.coe_neg]; rw [neg_div]; rw [neg_div]

/--
lemma `hasSum_nat_hurwitzZetaOdd_of_mem_Icc` / 引理 `hasSum_nat_hurwitzZetaOdd_of_mem_Icc`

English:
lemma hasSum_nat_hurwitzZetaOdd_of_mem_Icc
  given: {a : Real} (ha : a in Icc 0 1) {s : Complex} (hs : 1 < re s)
  proof: by
  refine (hasSum_nat_hurwitzZetaOdd a hs).congr_fun fun n => ?_
  suffices forall b : Real, 0 <= b -> SignType.sign (n + b) / (↑|n + b| : Complex) ^ s = 1 / (n + b) ^ s by
    simp only [add_sub_assoc, this a ha.1, this (1 - a) (sub_nonneg.mpr ha.2), push_cast]
  intro b hb
  rw [abs_of_nonneg (b

中文:
引理 hasSum_nat_hurwitzZetaOdd_of_mem_Icc
  条件: {a : 实数} (ha : a in 闭区间 0 1) {s : 复形} (hs : 1 < re s)
  证明: by
  refine (hasSum_nat_hurwitzZetaOdd a hs).congr_fun fun n => ?_
  suffices forall b : Real, 0 <= b -> SignType.sign (n + b) / (↑|n + b| : Complex) ^ s = 1 / (n + b) ^ s by
    simp only [add_sub_assoc, this a ha.1, this (1 - a) (sub_nonneg.mpr ha.2), push_cast]
  intro b hb
  rw [abs_of_nonneg (b

Depends on / 依赖: SignType, SignType.sign, abs_of_nonneg, add_sub_assoc, congr_fun, hasSum_nat_hurwitzZetaOdd, lt_or_eq_of_le, not_lt, not_lt.mpr, ofReal_zero, sign_pos, sub_nonneg, sub_nonneg.mpr, zero_cpow, zero_le_one
-/
lemma hasSum_nat_hurwitzZetaOdd_of_mem_Icc {a : Real} (ha : a in Icc 0 1) {s : Complex} (hs : 1 < re s) :
    HasSum (fun n : Nat => (1 / (n + a : Complex) ^ s - 1 / (n + 1 - a : Complex) ^ s) / 2)
    (hurwitzZetaOdd a s) := by
  refine (hasSum_nat_hurwitzZetaOdd a hs).congr_fun fun n => ?_
  suffices forall b : Real, 0 <= b -> SignType.sign (n + b) / (↑|n + b| : Complex) ^ s = 1 / (n + b) ^ s by
    simp only [add_sub_assoc, this a ha.1, this (1 - a) (sub_nonneg.mpr ha.2), push_cast]
  intro b hb
  rw [abs_of_nonneg (by positivity)]; rw [(by simp : (n : Complex) + b = ↑(n + b))]
  rcases lt_or_eq_of_le (by positivity : 0 <= n + b) with hb | hb
  · simp [sign_pos hb]
  · rw [← hb, ofReal_zero, zero_cpow ((not_lt.mpr zero_le_one) ∘ (zero_re ▸ · ▸ hs)),
      div_zero, div_zero]

/--
theorem `hasSum_int_sinZeta` / 定理 `hasSum_int_sinZeta`

English:
theorem hasSum_int_sinZeta
  given: (a : Real) {s : Complex} (hs : 1 < re s)
  proof: by
  rw [sinZeta]
  refine ((hasSum_int_completedSinZeta a hs).div_const (GammaReal (s + 1))).congr_fun fun n => ?_
  have : 0 < re (s + 1) := by rw [add_re, one_re]; positivity
  simp only [mul_assoc, div_right_comm _ _ (GammaReal _),
    mul_div_cancel_left₀ _ (GammaReal_ne_zero_of_re_pos this)]

中文:
定理 hasSum_int_sinZeta
  条件: (a : 实数) {s : 复形} (hs : 1 < re s)
  证明: by
  rw [sinZeta]
  refine ((hasSum_int_completedSinZeta a hs).div_const (GammaReal (s + 1))).congr_fun fun n => ?_
  have : 0 < re (s + 1) := by rw [add_re, one_re]; positivity
  simp only [mul_assoc, div_right_comm _ _ (GammaReal _),
    mul_div_cancel_left₀ _ (GammaReal_ne_zero_of_re_pos this)]

Depends on / 依赖: GammaReal, GammaReal_ne_zero_of_re_pos, add_re, congr_fun, div_const, div_right_comm, hasSum_int_completedSinZeta, mul_assoc, one_re, sinZeta
-/
theorem hasSum_int_sinZeta (a : Real) {s : Complex} (hs : 1 < re s) :
    HasSum (fun n : Int => -I * n.sign * cexp (2 * π * I * a * n) / ↑|n| ^ s / 2) (sinZeta a s) := by
  rw [sinZeta]
  refine ((hasSum_int_completedSinZeta a hs).div_const (GammaReal (s + 1))).congr_fun fun n => ?_
  have : 0 < re (s + 1) := by rw [add_re, one_re]; positivity
  simp only [mul_assoc, div_right_comm _ _ (GammaReal _),
    mul_div_cancel_left₀ _ (GammaReal_ne_zero_of_re_pos this)]

/--
lemma `hasSum_nat_sinZeta` / 引理 `hasSum_nat_sinZeta`

English:
lemma hasSum_nat_sinZeta
  given: (a : Real) {s : Complex} (hs : 1 < re s)
  proof: by
  have := (hasSum_int_sinZeta a hs).nat_add_neg
  simp_rw [abs_neg, Int.sign_neg, Int.cast_neg, Nat.abs_cast, Int.cast_natCast, mul_neg, abs_zero,
    Int.cast_zero, zero_cpow (ne_zero_of_one_lt_re hs), div_zero, zero_div, add_zero] at this
  simp_rw [push_cast, Complex.sin]
  refine this.congr_f

中文:
引理 hasSum_nat_sinZeta
  条件: (a : 实数) {s : 复形} (hs : 1 < re s)
  证明: by
  have := (hasSum_int_sinZeta a hs).nat_add_neg
  simp_rw [abs_neg, Int.sign_neg, Int.cast_neg, Nat.abs_cast, Int.cast_natCast, mul_neg, abs_zero,
    Int.cast_zero, zero_cpow (ne_zero_of_one_lt_re hs), div_zero, zero_div, add_zero] at this
  simp_rw [push_cast, Complex.sin]
  refine this.congr_f

Depends on / 依赖: Complex.sin, Int.cast_natCast, Int.cast_neg, Int.cast_one, Int.cast_zero, Int.sign_natCast_of_ne_zero, Int.sign_neg, Nat.abs_cast, abs_cast, abs_neg, abs_zero, add_div, add_zero, cast_natCast, cast_neg, cast_one, cast_zero, congr_fun, div_right_comm, div_zero
-/
lemma hasSum_nat_sinZeta (a : Real) {s : Complex} (hs : 1 < re s) :
    HasSum (fun n : Nat => Real.sin (2 * π * a * n) / (n : Complex) ^ s) (sinZeta a s) := by
  have := (hasSum_int_sinZeta a hs).nat_add_neg
  simp_rw [abs_neg, Int.sign_neg, Int.cast_neg, Nat.abs_cast, Int.cast_natCast, mul_neg, abs_zero,
    Int.cast_zero, zero_cpow (ne_zero_of_one_lt_re hs), div_zero, zero_div, add_zero] at this
  simp_rw [push_cast, Complex.sin]
  refine this.congr_fun fun n => ?_
  rcases ne_or_eq n 0 with h | rfl
  · simp only [neg_mul, sub_mul, div_right_comm _ (2 : Complex), Int.sign_natCast_of_ne_zero h,
      Int.cast_one, mul_one, mul_comm I, neg_neg, ← add_div, ← sub_eq_neg_add]
    congr 5 <;> ring
  · simp

/--
lemma `LSeriesHasSum_sin` / 引理 `LSeriesHasSum_sin`

English:
lemma LSeriesHasSum_sin
  given: (a : Real) {s : Complex} (hs : 1 < re s)
  proof: (hasSum_nat_sinZeta a hs).congr_fun (LSeries.term_of_ne_zero' (ne_zero_of_one_lt_re hs) _)

中文:
引理 LSeriesHasSum_sin
  条件: (a : 实数) {s : 复形} (hs : 1 < re s)
  证明: (hasSum_nat_sinZeta a hs).congr_fun (LSeries.term_of_ne_zero' (ne_zero_of_one_lt_re hs) _)

Depends on / 依赖: LSeries, LSeries.term_of_ne_zero, congr_fun, hasSum_nat_sinZeta, ne_zero_of_one_lt_re, term_of_ne_zero
-/
lemma LSeriesHasSum_sin (a : Real) {s : Complex} (hs : 1 < re s) :
    LSeriesHasSum (Real.sin <| 2 * π * a * ·) s (sinZeta a s) :=
  (hasSum_nat_sinZeta a hs).congr_fun (LSeries.term_of_ne_zero' (ne_zero_of_one_lt_re hs) _)

/--
theorem `hurwitzZetaOdd_neg_two_mul_nat_sub_one` / 定理 `hurwitzZetaOdd_neg_two_mul_nat_sub_one`

English:
theorem hurwitzZetaOdd_neg_two_mul_nat_sub_one
  given: (a : UnitAddCircle) (n : Nat)
  proof: by
  rw [hurwitzZetaOdd]; rw [GammaReal_eq_zero_iff.mpr ⟨n]; rw [by rw [neg_mul]; rw [sub_add_cancel]⟩, div_zero]

中文:
定理 hurwitzZetaOdd_neg_two_mul_nat_sub_one
  条件: (a : UnitAddCircle) (n : 自然数)
  证明: by
  rw [hurwitzZetaOdd]; rw [GammaReal_eq_zero_iff.mpr ⟨n]; rw [by rw [neg_mul]; rw [sub_add_cancel]⟩, div_zero]

Depends on / 依赖: GammaReal_eq_zero_iff, GammaReal_eq_zero_iff.mpr, div_zero, hurwitzZetaOdd, neg_mul, sub_add_cancel
-/
theorem hurwitzZetaOdd_neg_two_mul_nat_sub_one (a : UnitAddCircle) (n : Nat) :
    hurwitzZetaOdd a (-2 * n - 1) = 0 := by
  rw [hurwitzZetaOdd]; rw [GammaReal_eq_zero_iff.mpr ⟨n]; rw [by rw [neg_mul]; rw [sub_add_cancel]⟩, div_zero]

/--
theorem `sinZeta_neg_two_mul_nat_sub_one` / 定理 `sinZeta_neg_two_mul_nat_sub_one`

English:
theorem sinZeta_neg_two_mul_nat_sub_one
  given: (a : UnitAddCircle) (n : Nat)
  proof: by
  rw [sinZeta]; rw [GammaReal_eq_zero_iff.mpr ⟨n]; rw [by rw [neg_mul]; rw [sub_add_cancel]⟩, div_zero]

中文:
定理 sinZeta_neg_two_mul_nat_sub_one
  条件: (a : UnitAddCircle) (n : 自然数)
  证明: by
  rw [sinZeta]; rw [GammaReal_eq_zero_iff.mpr ⟨n]; rw [by rw [neg_mul]; rw [sub_add_cancel]⟩, div_zero]

Depends on / 依赖: GammaReal_eq_zero_iff, GammaReal_eq_zero_iff.mpr, div_zero, neg_mul, sinZeta, sub_add_cancel
-/
theorem sinZeta_neg_two_mul_nat_sub_one (a : UnitAddCircle) (n : Nat) :
    sinZeta a (-2 * n - 1) = 0 := by
  rw [sinZeta]; rw [GammaReal_eq_zero_iff.mpr ⟨n]; rw [by rw [neg_mul]; rw [sub_add_cancel]⟩, div_zero]

/--
lemma `hurwitzZetaOdd_one_sub` / 引理 `hurwitzZetaOdd_one_sub`

English:
lemma hurwitzZetaOdd_one_sub
  given: (a : UnitAddCircle) {s : Complex} (hs : forall (n : Nat), s != -n)
  proof: by
  rw [← GammaComplex]; rw [hurwitzZetaOdd]; rw [(by ring : 1 - s + 1 = 2 - s)]; rw [div_eq_mul_inv]; rw [inv_GammaReal_two_sub hs]; rw [completedHurwitzZetaOdd_one_sub]; rw [sinZeta]; rw [← div_eq_mul_inv]; rw [← mul_div_assoc]; rw [← mul_div_assoc]; rw [mul_comm]

中文:
引理 hurwitzZetaOdd_one_sub
  条件: (a : UnitAddCircle) {s : 复形} (hs : 对任意 (n : 自然数), s != -n)
  证明: by
  rw [← GammaComplex]; rw [hurwitzZetaOdd]; rw [(by ring : 1 - s + 1 = 2 - s)]; rw [div_eq_mul_inv]; rw [inv_GammaReal_two_sub hs]; rw [completedHurwitzZetaOdd_one_sub]; rw [sinZeta]; rw [← div_eq_mul_inv]; rw [← mul_div_assoc]; rw [← mul_div_assoc]; rw [mul_comm]

Depends on / 依赖: GammaComplex, completedHurwitzZetaOdd_one_sub, div_eq_mul_inv, hurwitzZetaOdd, inv_GammaReal_two_sub, mul_comm, mul_div_assoc, sinZeta
-/
lemma hurwitzZetaOdd_one_sub (a : UnitAddCircle) {s : Complex} (hs : forall (n : Nat), s != -n) :
    hurwitzZetaOdd a (1 - s) = 2 * (2 * π) ^ (-s) * Gamma s * sin (π * s / 2) * sinZeta a s := by
  rw [← GammaComplex]; rw [hurwitzZetaOdd]; rw [(by ring : 1 - s + 1 = 2 - s)]; rw [div_eq_mul_inv]; rw [inv_GammaReal_two_sub hs]; rw [completedHurwitzZetaOdd_one_sub]; rw [sinZeta]; rw [← div_eq_mul_inv]; rw [← mul_div_assoc]; rw [← mul_div_assoc]; rw [mul_comm]

/--
lemma `sinZeta_one_sub` / 引理 `sinZeta_one_sub`

English:
lemma sinZeta_one_sub
  given: (a : UnitAddCircle) {s : Complex} (hs : forall (n : Nat), s != -n)
  proof: by
  rw [← GammaComplex]; rw [sinZeta]; rw [(by ring : 1 - s + 1 = 2 - s)]; rw [div_eq_mul_inv]; rw [inv_GammaReal_two_sub hs]; rw [completedSinZeta_one_sub]; rw [hurwitzZetaOdd]; rw [← div_eq_mul_inv]; rw [← mul_div_assoc]; rw [← mul_div_assoc]; rw [mul_comm]

中文:
引理 sinZeta_one_sub
  条件: (a : UnitAddCircle) {s : 复形} (hs : 对任意 (n : 自然数), s != -n)
  证明: by
  rw [← GammaComplex]; rw [sinZeta]; rw [(by ring : 1 - s + 1 = 2 - s)]; rw [div_eq_mul_inv]; rw [inv_GammaReal_two_sub hs]; rw [completedSinZeta_one_sub]; rw [hurwitzZetaOdd]; rw [← div_eq_mul_inv]; rw [← mul_div_assoc]; rw [← mul_div_assoc]; rw [mul_comm]

Depends on / 依赖: GammaComplex, completedSinZeta_one_sub, div_eq_mul_inv, hurwitzZetaOdd, inv_GammaReal_two_sub, mul_comm, mul_div_assoc, sinZeta
-/
lemma sinZeta_one_sub (a : UnitAddCircle) {s : Complex} (hs : forall (n : Nat), s != -n) :
    sinZeta a (1 - s) = 2 * (2 * π) ^ (-s) * Gamma s * sin (π * s / 2) * hurwitzZetaOdd a s := by
  rw [← GammaComplex]; rw [sinZeta]; rw [(by ring : 1 - s + 1 = 2 - s)]; rw [div_eq_mul_inv]; rw [inv_GammaReal_two_sub hs]; rw [completedSinZeta_one_sub]; rw [hurwitzZetaOdd]; rw [← div_eq_mul_inv]; rw [← mul_div_assoc]; rw [← mul_div_assoc]; rw [mul_comm]

end HurwitzZeta
