/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Yury Kudryashov
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.SpecialFunctions.PolynomialExp
public import Mathlib.Analysis.Analytic.IsolatedZeros

/-!
# Infinitely smooth transition function

In this file we construct two infinitely smooth functions with properties that an analytic function
cannot have:

* `expNegInvGlue` is equal to zero for `x ≤ 0` and is strictly positive otherwise; it is given by
  `x ↦ exp (-1/x)` for `x > 0`;

* `Real.smoothTransition` is equal to zero for `x ≤ 0` and is equal to one for `x ≥ 1`; it is given
  by `expNegInvGlue x / (expNegInvGlue x + expNegInvGlue (1 - x))`;
-/

@[expose] public section

noncomputable section

open scoped Topology
open Polynomial Real Filter Set Function

/--
Definition of `expNegInvGlue` / `expNegInvGlue` 的定义

English:
definition expNegInvGlue
  signature: (x : Real)
  body: if x <= 0 then 0 else exp (-x⁻¹)

中文:
定义 expNegInvGlue
  签名: (x : 实数)
  定义体: if x <= 0 then 0 else exp (-x⁻¹)
-/
def expNegInvGlue (x : Real) : Real :=
  if x <= 0 then 0 else exp (-x⁻¹)

namespace expNegInvGlue

/--
theorem `zero_of_nonpos` / 定理 `zero_of_nonpos`

English:
theorem zero_of_nonpos
  given: {x : Real} (hx : x <= 0)
  statement: expNegInvGlue x = 0
  proof: by simp [expNegInvGlue, hx]

@[simp]

中文:
定理 zero_of_nonpos
  条件: {x : 实数} (hx : x <= 0)
  结论: expNegInvGlue x = 0
  证明: by simp [expNegInvGlue, hx]

@[simp]

Depends on / 依赖: expNegInvGlue
-/
theorem zero_of_nonpos {x : Real} (hx : x <= 0) : expNegInvGlue x = 0 := by simp [expNegInvGlue, hx]

@[simp]
/--
theorem `zero` / 定理 `zero`

English:
theorem zero
  statement: expNegInvGlue 0 = 0
  proof: zero_of_nonpos le_rfl

中文:
定理 zero
  结论: expNegInvGlue 0 = 0
  证明: zero_of_nonpos le_rfl
-/
protected theorem zero : expNegInvGlue 0 = 0 := zero_of_nonpos le_rfl

/--
theorem `pos_of_pos` / 定理 `pos_of_pos`

English:
theorem pos_of_pos
  given: {x : Real} (hx : 0 < x)
  statement: 0 < expNegInvGlue x
  proof: by
  simp [expNegInvGlue, not_le.2 hx, exp_pos]

中文:
定理 pos_of_pos
  条件: {x : 实数} (hx : 0 < x)
  结论: 0 < expNegInvGlue x
  证明: by
  simp [expNegInvGlue, not_le.2 hx, exp_pos]

Depends on / 依赖: expNegInvGlue, exp_pos, not_le
-/
theorem pos_of_pos {x : Real} (hx : 0 < x) : 0 < expNegInvGlue x := by
  simp [expNegInvGlue, not_le.2 hx, exp_pos]

/--
theorem `nonneg` / 定理 `nonneg`

English:
theorem nonneg
  given: (x : Real)
  statement: 0 <= expNegInvGlue x
  proof: by
  cases le_or_gt x 0 with
  | inl h => exact ge_of_eq (zero_of_nonpos h)
  | inr h => exact le_of_lt (pos_of_pos h)

中文:
定理 nonneg
  条件: (x : 实数)
  结论: 0 <= expNegInvGlue x
  证明: by
  cases le_or_gt x 0 with
  | inl h => exact ge_of_eq (zero_of_nonpos h)
  | inr h => exact le_of_lt (pos_of_pos h)

Depends on / 依赖: ge_of_eq, le_of_lt, le_or_gt, pos_of_pos, zero_of_nonpos
-/
theorem nonneg (x : Real) : 0 <= expNegInvGlue x := by
  cases le_or_gt x 0 with
  | inl h => exact ge_of_eq (zero_of_nonpos h)
  | inr h => exact le_of_lt (pos_of_pos h)

/--
theorem `zero_iff_nonpos` / 定理 `zero_iff_nonpos`

English:
theorem zero_iff_nonpos
  given: {x : Real}
  statement: expNegInvGlue x = 0 ↔ x <= 0
  proof: ⟨fun h => not_lt.mp fun h' => (pos_of_pos h').ne' h, zero_of_nonpos⟩

中文:
定理 zero_iff_nonpos
  条件: {x : 实数}
  结论: expNegInvGlue x = 0 ↔ x <= 0
  证明: ⟨fun h => not_lt.mp fun h' => (pos_of_pos h').ne' h, zero_of_nonpos⟩
-/
@[simp] theorem zero_iff_nonpos {x : Real} : expNegInvGlue x = 0 ↔ x <= 0 :=
  ⟨fun h => not_lt.mp fun h' => (pos_of_pos h').ne' h, zero_of_nonpos⟩

/--
theorem `monotone` / 定理 `monotone`

English:
theorem monotone
  statement: Monotone expNegInvGlue
  proof: by
  intro x y hxy
  rcases le_or_gt x 0 with hx | hx
  · simp [zero_of_nonpos hx, nonneg]
  simp [expNegInvGlue, not_le.2 hx, not_le.2 (hx.trans_le hxy),
    inv_le_inv₀ (hx.trans_le hxy) hx, hxy]

中文:
定理 monotone
  结论: 递增 expNegInvGlue
  证明: by
  intro x y hxy
  rcases le_or_gt x 0 with hx | hx
  · simp [zero_of_nonpos hx, nonneg]
  simp [expNegInvGlue, not_le.2 hx, not_le.2 (hx.trans_le hxy),
    inv_le_inv₀ (hx.trans_le hxy) hx, hxy]
-/
protected theorem monotone : Monotone expNegInvGlue := by
  intro x y hxy
  rcases le_or_gt x 0 with hx | hx
  · simp [zero_of_nonpos hx, nonneg]
  simp [expNegInvGlue, not_le.2 hx, not_le.2 (hx.trans_le hxy),
    inv_le_inv₀ (hx.trans_le hxy) hx, hxy]

/--
theorem `not_analyticAt_zero` / 定理 `not_analyticAt_zero`

English:
theorem not_analyticAt_zero
  statement: ¬ AnalyticAt Real expNegInvGlue 0
  proof: by
  intro h
  obtain ⟨r, hr, h⟩ := h.exists_ball_analyticOnNhd
  suffices expNegInvGlue (r / 2) = 0 by simpa [hr, not_le_of_gt]
  exact h.eqOn_zero_of_preconnected_of_mem_closure (z₀ := 0)
    (Real.ball_eq_Ioo 0 r ▸ isPreconnected_Ioo)
    (by simp [hr]) (by simp [Set.Iic_def]) (by simp [abs_of_po

中文:
定理 not_analyticAt_zero
  结论: ¬ AnalyticAt 实数 expNegInvGlue 0
  证明: by
  intro h
  obtain ⟨r, hr, h⟩ := h.exists_ball_analyticOnNhd
  suffices expNegInvGlue (r / 2) = 0 by simpa [hr, not_le_of_gt]
  exact h.eqOn_zero_of_preconnected_of_mem_closure (z₀ := 0)
    (Real.ball_eq_Ioo 0 r ▸ isPreconnected_Ioo)
    (by simp [hr]) (by simp [Set.Iic_def]) (by simp [abs_of_po

Depends on / 依赖: Iic_def, Real.ball_eq_Ioo, Set.Iic_def, abs_of_pos, ball_eq_Ioo, eqOn_zero_of_preconnected_of_mem_closure, exists_ball_analyticOnNhd, expNegInvGlue, h.eqOn_zero_of_preconnected_of_mem_closure, h.exists_ball_analyticOnNhd, isPreconnected_Ioo, not_le_of_gt
-/
theorem not_analyticAt_zero : ¬ AnalyticAt Real expNegInvGlue 0 := by
  intro h
  obtain ⟨r, hr, h⟩ := h.exists_ball_analyticOnNhd
  suffices expNegInvGlue (r / 2) = 0 by simpa [hr, not_le_of_gt]
  exact h.eqOn_zero_of_preconnected_of_mem_closure (z₀ := 0)
    (Real.ball_eq_Ioo 0 r ▸ isPreconnected_Ioo)
    (by simp [hr]) (by simp [Set.Iic_def]) (by simp [abs_of_pos, hr])

/-!
### Smoothness of `expNegInvGlue`

In this section we prove that the function `f = expNegInvGlue` is infinitely smooth. To do
this, we show that $g_p(x)=p(x^{-1})f(x)$ is infinitely smooth for any polynomial `p` with real
coefficients. First we show that $g_p(x)$ tends to zero at zero, then we show that it is
differentiable with derivative $g_p'=g_{x^2(p-p')}$. Finally, we prove smoothness of $g_p$ by
induction, then deduce smoothness of $f$ by setting $p=1$.
-/

/--
theorem `tendsto_polynomial_inv_mul_zero` / 定理 `tendsto_polynomial_inv_mul_zero`

English:
theorem tendsto_polynomial_inv_mul_zero
  given: (p : Real[X])
  proof: by
  simp only [expNegInvGlue, mul_ite, mul_zero]
  refine tendsto_const_nhds.if ?_
  simp only [not_le]
  have : Tendsto (fun x => p.eval x⁻¹ / exp x⁻¹) (𝓝[>] 0) (𝓝 0) :=
    p.tendsto_div_exp_atTop.comp tendsto_inv_nhdsGT_zero
refine this.congr' mem_of_superset self_mem_nhdsWithin fun x hx => ?_
 

中文:
定理 tendsto_polynomial_inv_mul_zero
  条件: (p : 实数[X])
  证明: by
  simp only [expNegInvGlue, mul_ite, mul_zero]
  refine tendsto_const_nhds.if ?_
  simp only [not_le]
  have : Tendsto (fun x => p.eval x⁻¹ / exp x⁻¹) (𝓝[>] 0) (𝓝 0) :=
    p.tendsto_div_exp_atTop.comp tendsto_inv_nhdsGT_zero
refine this.congr' mem_of_superset self_mem_nhdsWithin fun x hx => ?_
 

Depends on / 依赖: Tendsto, div_eq_mul_inv, expNegInvGlue, exp_neg, mem_of_superset, mul_ite, mul_zero, not_le, p.eval, p.tendsto_div_exp_atTop.comp, self_mem_nhdsWithin, tendsto_const_nhds, tendsto_const_nhds.if, tendsto_div_exp_atTop, tendsto_inv_nhdsGT_zero, this.congr
-/
theorem tendsto_polynomial_inv_mul_zero (p : Real[X]) :
    Tendsto (fun x => p.eval x⁻¹ * expNegInvGlue x) (𝓝 0) (𝓝 0) := by
  simp only [expNegInvGlue, mul_ite, mul_zero]
  refine tendsto_const_nhds.if ?_
  simp only [not_le]
  have : Tendsto (fun x => p.eval x⁻¹ / exp x⁻¹) (𝓝[>] 0) (𝓝 0) :=
    p.tendsto_div_exp_atTop.comp tendsto_inv_nhdsGT_zero
refine this.congr' mem_of_superset self_mem_nhdsWithin fun x hx => ?_
  simp [exp_neg, div_eq_mul_inv]

/--
theorem `hasDerivAt_polynomial_eval_inv_mul` / 定理 `hasDerivAt_polynomial_eval_inv_mul`

English:
theorem hasDerivAt_polynomial_eval_inv_mul
  given: (p : Real[X]) (x : Real)
  proof: by
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · rw [zero_of_nonpos hx.le, mul_zero]
    refine (hasDerivAt_const _ 0).congr_of_eventuallyEq ?_
    filter_upwards [gt_mem_nhds hx] with y hy
    rw [zero_of_nonpos hy.le]; rw [mul_zero]
  · rw [expNegInvGlue.zero, mul_zero, hasDerivAt_iff_tendsto_

中文:
定理 hasDerivAt_polynomial_eval_inv_mul
  条件: (p : 实数[X]) (x : 实数)
  证明: by
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · rw [zero_of_nonpos hx.le, mul_zero]
    refine (hasDerivAt_const _ 0).congr_of_eventuallyEq ?_
    filter_upwards [gt_mem_nhds hx] with y hy
    rw [zero_of_nonpos hy.le]; rw [mul_zero]
  · rw [expNegInvGlue.zero, mul_zero, hasDerivAt_iff_tendsto_

Depends on / 依赖: congr_of_eventuallyEq, div_eq_mul_inv, expNegInvGlue, expNegInvGlue.zero, filter_upwards, gt_mem_nhds, hasDeriv, hasDerivAt_const, hasDerivAt_iff_tendsto_slope, hx.le, hy.le, inf_le_left, lt_trichotomy, mono_left, mul_right_comm, mul_zero, p.hasDeriv, slope_def_field, tendsto_polynomial_inv_mul_zero, zero_of_nonpos
-/
theorem hasDerivAt_polynomial_eval_inv_mul (p : Real[X]) (x : Real) :
    HasDerivAt (fun x => p.eval x⁻¹ * expNegInvGlue x)
      ((X ^ 2 * (p - derivative (R := Real) p)).eval x⁻¹ * expNegInvGlue x) x := by
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · rw [zero_of_nonpos hx.le, mul_zero]
    refine (hasDerivAt_const _ 0).congr_of_eventuallyEq ?_
    filter_upwards [gt_mem_nhds hx] with y hy
    rw [zero_of_nonpos hy.le]; rw [mul_zero]
  · rw [expNegInvGlue.zero, mul_zero, hasDerivAt_iff_tendsto_slope]
    refine ((tendsto_polynomial_inv_mul_zero (p * X)).mono_left inf_le_left).congr fun x => ?_
    simp [slope_def_field, div_eq_mul_inv, mul_right_comm]
  · have := ((p.hasDerivAt x⁻¹).mul (hasDerivAt_neg _).exp).comp x (hasDerivAt_inv hx.ne')
    convert! this.congr_of_eventuallyEq _ using 1
    · simp [expNegInvGlue, hx.not_ge]
      ring
    · filter_upwards [lt_mem_nhds hx] with y hy
      simp [expNegInvGlue, hy.not_ge]

/--
theorem `differentiable_polynomial_eval_inv_mul` / 定理 `differentiable_polynomial_eval_inv_mul`

English:
theorem differentiable_polynomial_eval_inv_mul
  given: (p : Real[X])
  proof: fun x =>
  (hasDerivAt_polynomial_eval_inv_mul p x).differentiableAt

中文:
定理 differentiable_polynomial_eval_inv_mul
  条件: (p : 实数[X])
  证明: fun x =>
  (hasDerivAt_polynomial_eval_inv_mul p x).differentiableAt
-/
theorem differentiable_polynomial_eval_inv_mul (p : Real[X]) :
    Differentiable Real (fun x => p.eval x⁻¹ * expNegInvGlue x) := fun x =>
  (hasDerivAt_polynomial_eval_inv_mul p x).differentiableAt

/--
theorem `continuous_polynomial_eval_inv_mul` / 定理 `continuous_polynomial_eval_inv_mul`

English:
theorem continuous_polynomial_eval_inv_mul
  given: (p : Real[X])
  proof: (differentiable_polynomial_eval_inv_mul p).continuous

中文:
定理 continuous_polynomial_eval_inv_mul
  条件: (p : 实数[X])
  证明: (differentiable_polynomial_eval_inv_mul p).continuous

Depends on / 依赖: continuous, differentiable_polynomial_eval_inv_mul
-/
theorem continuous_polynomial_eval_inv_mul (p : Real[X]) :
    Continuous (fun x => p.eval x⁻¹ * expNegInvGlue x) :=
  (differentiable_polynomial_eval_inv_mul p).continuous

/--
theorem `contDiff_polynomial_eval_inv_mul` / 定理 `contDiff_polynomial_eval_inv_mul`

English:
theorem contDiff_polynomial_eval_inv_mul
  given: {n : Nat∞} (p : Real[X])
  proof: by
  apply contDiff_all_iff_nat.2 (fun m => ?_) n
  induction m generalizing p with
| zero => exact contDiff_zero.2 continuous_polynomial_eval_inv_mul _
  | succ m ihm =>
    rw [show ((m + 1 : Nat) : WithTop Nat∞) = m + 1 from rfl]
    refine contDiff_succ_iff_deriv.2 ⟨differentiable_polynomial_eva

中文:
定理 contDiff_polynomial_eval_inv_mul
  条件: {n : 自然数∞} (p : 实数[X])
  证明: by
  apply contDiff_all_iff_nat.2 (fun m => ?_) n
  induction m generalizing p with
| zero => exact contDiff_zero.2 continuous_polynomial_eval_inv_mul _
  | succ m ihm =>
    rw [show ((m + 1 : Nat) : WithTop Nat∞) = m + 1 from rfl]
    refine contDiff_succ_iff_deriv.2 ⟨differentiable_polynomial_eva

Depends on / 依赖: WithTop, contDiff_all_iff_nat, contDiff_succ_iff_deriv, contDiff_zero, continuous_polynomial_eval_inv_mul, convert, derivative, differentiable_polynomial_eval_inv_mul, generalizing, hasDerivAt_polynomial_eval_inv_mul
-/
theorem contDiff_polynomial_eval_inv_mul {n : Nat∞} (p : Real[X]) :
    ContDiff Real n (fun x => p.eval x⁻¹ * expNegInvGlue x) := by
  apply contDiff_all_iff_nat.2 (fun m => ?_) n
  induction m generalizing p with
| zero => exact contDiff_zero.2 continuous_polynomial_eval_inv_mul _
  | succ m ihm =>
    rw [show ((m + 1 : Nat) : WithTop Nat∞) = m + 1 from rfl]
    refine contDiff_succ_iff_deriv.2 ⟨differentiable_polynomial_eval_inv_mul _, by simp, ?_⟩
    convert! ihm (X ^ 2 * (p - derivative (R := Real) p)) using 2
    exact (hasDerivAt_polynomial_eval_inv_mul p _).deriv

/-- The function `expNegInvGlue` is smooth. -/
@[fun_prop]
/--
theorem `contDiff` / 定理 `contDiff`

English:
theorem contDiff
  given: {n : Nat∞}
  statement: ContDiff Real n expNegInvGlue
  proof: by
  simpa using contDiff_polynomial_eval_inv_mul 1

中文:
定理 contDiff
  条件: {n : 自然数∞}
  结论: 连续可微 实数 n expNegInvGlue
  证明: by
  simpa using contDiff_polynomial_eval_inv_mul 1
-/
protected theorem contDiff {n : Nat∞} : ContDiff Real n expNegInvGlue := by
  simpa using contDiff_polynomial_eval_inv_mul 1

end expNegInvGlue

/--
Definition of `Real.smoothTransition` / `Real.smoothTransition` 的定义

English:
definition Real.smoothTransition
  signature: (x : Real)
  body: expNegInvGlue x / (expNegInvGlue x + expNegInvGlue (1 - x))

中文:
定义 实数.smoothTransition
  签名: (x : 实数)
  定义体: expNegInvGlue x / (expNegInvGlue x + expNegInvGlue (1 - x))

Depends on / 依赖: expNegInvGlue
-/
def Real.smoothTransition (x : Real) : Real :=
  expNegInvGlue x / (expNegInvGlue x + expNegInvGlue (1 - x))

namespace Real

namespace smoothTransition

variable {x : Real}

open expNegInvGlue

/--
theorem `pos_denom` / 定理 `pos_denom`

English:
theorem pos_denom
  given: (x)
  statement: 0 < expNegInvGlue x + expNegInvGlue (1 - x)
  proof: (zero_lt_one.gt_or_lt x).elim (fun hx => add_pos_of_pos_of_nonneg (pos_of_pos hx) (nonneg _))
    fun hx => add_pos_of_nonneg_of_pos (nonneg _) (pos_of_pos <| sub_pos.2 hx)

中文:
定理 pos_denom
  条件: (x)
  结论: 0 < expNegInvGlue x + expNegInvGlue (1 - x)
  证明: (zero_lt_one.gt_or_lt x).elim (fun hx => add_pos_of_pos_of_nonneg (pos_of_pos hx) (nonneg _))
    fun hx => add_pos_of_nonneg_of_pos (nonneg _) (pos_of_pos <| sub_pos.2 hx)

Depends on / 依赖: add_pos_of_nonneg_of_pos, add_pos_of_pos_of_nonneg, gt_or_lt, nonneg, pos_of_pos, sub_pos, zero_lt_one, zero_lt_one.gt_or_lt
-/
theorem pos_denom (x) : 0 < expNegInvGlue x + expNegInvGlue (1 - x) :=
  (zero_lt_one.gt_or_lt x).elim (fun hx => add_pos_of_pos_of_nonneg (pos_of_pos hx) (nonneg _))
    fun hx => add_pos_of_nonneg_of_pos (nonneg _) (pos_of_pos <| sub_pos.2 hx)

/--
theorem `one_of_one_le` / 定理 `one_of_one_le`

English:
theorem one_of_one_le
  given: (h : 1 <= x)
  statement: smoothTransition x = 1
  proof: (div_eq_one_iff_eq <| (pos_denom x).ne').2 by rw [zero_of_nonpos (sub_nonpos.2 h), add_zero]

@[simp]
nonrec theorem zero_iff_nonpos : smoothTransition x = 0 ↔ x <= 0 := by
  simp only [smoothTransition, _root_.div_eq_zero_iff, (pos_denom x).ne', zero_iff_nonpos, or_false]

中文:
定理 one_of_one_le
  条件: (h : 1 <= x)
  结论: smoothTransition x = 1
  证明: (div_eq_one_iff_eq <| (pos_denom x).ne').2 by rw [zero_of_nonpos (sub_nonpos.2 h), add_zero]

@[simp]
nonrec theorem zero_iff_nonpos : smoothTransition x = 0 ↔ x <= 0 := by
  simp only [smoothTransition, _root_.div_eq_zero_iff, (pos_denom x).ne', zero_iff_nonpos, or_false]

Depends on / 依赖: add_zero, div_eq_one_iff_eq, pos_denom, sub_nonpos, zero_of_nonpos
-/
theorem one_of_one_le (h : 1 <= x) : smoothTransition x = 1 :=
(div_eq_one_iff_eq <| (pos_denom x).ne').2 by rw [zero_of_nonpos (sub_nonpos.2 h), add_zero]

@[simp]
nonrec theorem zero_iff_nonpos : smoothTransition x = 0 ↔ x <= 0 := by
  simp only [smoothTransition, _root_.div_eq_zero_iff, (pos_denom x).ne', zero_iff_nonpos, or_false]

/--
theorem `zero_of_nonpos` / 定理 `zero_of_nonpos`

English:
theorem zero_of_nonpos
  given: (h : x <= 0)
  statement: smoothTransition x = 0
  proof: zero_iff_nonpos.2 h

@[simp]

中文:
定理 zero_of_nonpos
  条件: (h : x <= 0)
  结论: smoothTransition x = 0
  证明: zero_iff_nonpos.2 h

@[simp]

Depends on / 依赖: zero_iff_nonpos
-/
theorem zero_of_nonpos (h : x <= 0) : smoothTransition x = 0 := zero_iff_nonpos.2 h

@[simp]
/--
theorem `zero` / 定理 `zero`

English:
theorem zero
  statement: smoothTransition 0 = 0
  proof: zero_of_nonpos le_rfl

@[simp]

中文:
定理 zero
  结论: smoothTransition 0 = 0
  证明: zero_of_nonpos le_rfl

@[simp]
-/
protected theorem zero : smoothTransition 0 = 0 :=
  zero_of_nonpos le_rfl

@[simp]
/--
theorem `one` / 定理 `one`

English:
theorem one
  statement: smoothTransition 1 = 1
  proof: one_of_one_le le_rfl

中文:
定理 one
  结论: smoothTransition 1 = 1
  证明: one_of_one_le le_rfl
-/
protected theorem one : smoothTransition 1 = 1 :=
  one_of_one_le le_rfl

/-- Since `Real.smoothTransition` is constant on $(-∞, 0]$ and $[1, ∞)$, applying it to the
projection of `x : ℝ` to $[0, 1]$ gives the same result as applying it to `x`. -/
@[simp]
/--
theorem `projIcc` / 定理 `projIcc`

English:
theorem projIcc
  proof: by
  refine congr_fun
    (IccExtend_eq_self zero_le_one smoothTransition (fun x hx => ?_) fun x hx => ?_) x
  · rw [smoothTransition.zero, zero_of_nonpos hx.le]
  · rw [smoothTransition.one, one_of_one_le hx.le]

中文:
定理 projIcc
  证明: by
  refine congr_fun
    (IccExtend_eq_self zero_le_one smoothTransition (fun x hx => ?_) fun x hx => ?_) x
  · rw [smoothTransition.zero, zero_of_nonpos hx.le]
  · rw [smoothTransition.one, one_of_one_le hx.le]
-/
protected theorem projIcc :
    smoothTransition (projIcc (0 : Real) 1 zero_le_one x) = smoothTransition x := by
  refine congr_fun
    (IccExtend_eq_self zero_le_one smoothTransition (fun x hx => ?_) fun x hx => ?_) x
  · rw [smoothTransition.zero, zero_of_nonpos hx.le]
  · rw [smoothTransition.one, one_of_one_le hx.le]

/--
theorem `le_one` / 定理 `le_one`

English:
theorem le_one
  given: (x : Real)
  statement: smoothTransition x <= 1
  proof: (div_le_one (pos_denom x)).2 le_add_of_nonneg_right (nonneg _)

中文:
定理 le_one
  条件: (x : 实数)
  结论: smoothTransition x <= 1
  证明: (div_le_one (pos_denom x)).2 le_add_of_nonneg_right (nonneg _)

Depends on / 依赖: div_le_one, le_add_of_nonneg_right, nonneg, pos_denom
-/
theorem le_one (x : Real) : smoothTransition x <= 1 :=
(div_le_one (pos_denom x)).2 le_add_of_nonneg_right (nonneg _)

/--
theorem `nonneg` / 定理 `nonneg`

English:
theorem nonneg
  given: (x : Real)
  statement: 0 <= smoothTransition x
  proof: div_nonneg (expNegInvGlue.nonneg _) (pos_denom x).le

中文:
定理 nonneg
  条件: (x : 实数)
  结论: 0 <= smoothTransition x
  证明: div_nonneg (expNegInvGlue.nonneg _) (pos_denom x).le

Depends on / 依赖: div_nonneg, expNegInvGlue, expNegInvGlue.nonneg, nonneg, pos_denom
-/
theorem nonneg (x : Real) : 0 <= smoothTransition x :=
  div_nonneg (expNegInvGlue.nonneg _) (pos_denom x).le

/--
theorem `lt_one_of_lt_one` / 定理 `lt_one_of_lt_one`

English:
theorem lt_one_of_lt_one
  given: (h : x < 1)
  statement: smoothTransition x < 1
  proof: (div_lt_one <| pos_denom x).2 lt_add_of_pos_right _ pos_of_pos sub_pos.2 h

中文:
定理 lt_one_of_lt_one
  条件: (h : x < 1)
  结论: smoothTransition x < 1
  证明: (div_lt_one <| pos_denom x).2 lt_add_of_pos_right _ pos_of_pos sub_pos.2 h

Depends on / 依赖: div_lt_one, lt_add_of_pos_right, pos_denom, pos_of_pos, sub_pos
-/
theorem lt_one_of_lt_one (h : x < 1) : smoothTransition x < 1 :=
(div_lt_one <| pos_denom x).2 lt_add_of_pos_right _ pos_of_pos sub_pos.2 h

/--
theorem `pos_of_pos` / 定理 `pos_of_pos`

English:
theorem pos_of_pos
  given: (h : 0 < x)
  statement: 0 < smoothTransition x
  proof: div_pos (expNegInvGlue.pos_of_pos h) (pos_denom x)

中文:
定理 pos_of_pos
  条件: (h : 0 < x)
  结论: 0 < smoothTransition x
  证明: div_pos (expNegInvGlue.pos_of_pos h) (pos_denom x)

Depends on / 依赖: div_pos, expNegInvGlue, expNegInvGlue.pos_of_pos, pos_denom, pos_of_pos
-/
theorem pos_of_pos (h : 0 < x) : 0 < smoothTransition x :=
  div_pos (expNegInvGlue.pos_of_pos h) (pos_denom x)

/--
theorem `eq_one_iff_one_le` / 定理 `eq_one_iff_one_le`

English:
theorem eq_one_iff_one_le
  statement: smoothTransition x = 1 ↔ 1 <= x
  proof: by
  rcases le_or_gt 1 x with hx | hx
  · simp [hx, one_of_one_le]
  · simpa [(lt_one_of_lt_one hx).ne] using hx

@[fun_prop]

中文:
定理 eq_one_iff_one_le
  结论: smoothTransition x = 1 ↔ 1 <= x
  证明: by
  rcases le_or_gt 1 x with hx | hx
  · simp [hx, one_of_one_le]
  · simpa [(lt_one_of_lt_one hx).ne] using hx

@[fun_prop]
-/
@[simp] theorem eq_one_iff_one_le : smoothTransition x = 1 ↔ 1 <= x := by
  rcases le_or_gt 1 x with hx | hx
  · simp [hx, one_of_one_le]
  · simpa [(lt_one_of_lt_one hx).ne] using hx

@[fun_prop]
/--
theorem `contDiff` / 定理 `contDiff`

English:
theorem contDiff
  given: {n : Nat∞}
  statement: ContDiff Real n smoothTransition
  proof: expNegInvGlue.contDiff.div
    (expNegInvGlue.contDiff.add <| expNegInvGlue.contDiff.comp <| contDiff_const.sub contDiff_id)
    fun x => (pos_denom x).ne'

@[fun_prop]

中文:
定理 contDiff
  条件: {n : 自然数∞}
  结论: 连续可微 实数 n smoothTransition
  证明: expNegInvGlue.contDiff.div
    (expNegInvGlue.contDiff.add <| expNegInvGlue.contDiff.comp <| contDiff_const.sub contDiff_id)
    fun x => (pos_denom x).ne'

@[fun_prop]
-/
protected theorem contDiff {n : Nat∞} : ContDiff Real n smoothTransition :=
  expNegInvGlue.contDiff.div
    (expNegInvGlue.contDiff.add <| expNegInvGlue.contDiff.comp <| contDiff_const.sub contDiff_id)
    fun x => (pos_denom x).ne'

@[fun_prop]
/--
theorem `contDiffAt` / 定理 `contDiffAt`

English:
theorem contDiffAt
  given: {x : Real} {n : Nat∞}
  statement: ContDiffAt Real n smoothTransition x
  proof: smoothTransition.contDiff.contDiffAt

@[fun_prop]

中文:
定理 contDiffAt
  条件: {x : 实数} {n : 自然数∞}
  结论: ContDiffAt 实数 n smoothTransition x
  证明: smoothTransition.contDiff.contDiffAt

@[fun_prop]
-/
protected theorem contDiffAt {x : Real} {n : Nat∞} : ContDiffAt Real n smoothTransition x :=
  smoothTransition.contDiff.contDiffAt

@[fun_prop]
/--
theorem `continuous` / 定理 `continuous`

English:
theorem continuous
  statement: Continuous smoothTransition
  proof: (@smoothTransition.contDiff 0).continuous

@[fun_prop]

中文:
定理 continuous
  结论: 连续 smoothTransition
  证明: (@smoothTransition.contDiff 0).continuous

@[fun_prop]
-/
protected theorem continuous : Continuous smoothTransition :=
  (@smoothTransition.contDiff 0).continuous

@[fun_prop]
/--
theorem `continuousAt` / 定理 `continuousAt`

English:
theorem continuousAt
  statement: ContinuousAt smoothTransition x
  proof: smoothTransition.continuous.continuousAt

中文:
定理 continuousAt
  结论: ContinuousAt smoothTransition x
  证明: smoothTransition.continuous.continuousAt
-/
protected theorem continuousAt : ContinuousAt smoothTransition x :=
  smoothTransition.continuous.continuousAt

/--
theorem `monotone` / 定理 `monotone`

English:
theorem monotone
  statement: Monotone smoothTransition
  proof: by
  intro x y hxy
  simp only [smoothTransition]
  rw [div_le_div_iff₀ (pos_denom x) (pos_denom y)]
  simp only [mul_add, mul_comm (expNegInvGlue x) (expNegInvGlue y), add_le_add_iff_left]
  gcongr
  · exact expNegInvGlue.nonneg _
  · exact expNegInvGlue.nonneg _
  · apply expNegInvGlue.monotone hx

中文:
定理 monotone
  结论: 递增 smoothTransition
  证明: by
  intro x y hxy
  simp only [smoothTransition]
  rw [div_le_div_iff₀ (pos_denom x) (pos_denom y)]
  simp only [mul_add, mul_comm (expNegInvGlue x) (expNegInvGlue y), add_le_add_iff_left]
  gcongr
  · exact expNegInvGlue.nonneg _
  · exact expNegInvGlue.nonneg _
  · apply expNegInvGlue.monotone hx
-/
protected theorem monotone : Monotone smoothTransition := by
  intro x y hxy
  simp only [smoothTransition]
  rw [div_le_div_iff₀ (pos_denom x) (pos_denom y)]
  simp only [mul_add, mul_comm (expNegInvGlue x) (expNegInvGlue y), add_le_add_iff_left]
  gcongr
  · exact expNegInvGlue.nonneg _
  · exact expNegInvGlue.nonneg _
  · apply expNegInvGlue.monotone hxy
  · apply expNegInvGlue.monotone (by linarith)

end smoothTransition

end Real
