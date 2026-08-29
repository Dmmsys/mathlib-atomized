/-
Copyright (c) 2023 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
module

public import Mathlib.Analysis.Convolution
public import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.EulerSineProd
public import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
public import Mathlib.Analysis.Analytic.IsolatedZeros
public import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# The Beta function, and further properties of the Gamma function

In this file we define the Beta integral, relate Beta and Gamma functions, and prove some
refined properties of the Gamma function using these relations.

## Results on the Beta function

* `Complex.betaIntegral`: the Beta function `Β(u, v)`, where `u`, `v` are complex with positive
  real part.
* `Complex.Gamma_mul_Gamma_eq_betaIntegral`: the formula
  `Gamma u * Gamma v = Gamma (u + v) * betaIntegral u v`.

## Results on the Gamma function

* `Complex.Gamma_ne_zero`: for all `s : ℂ` with `s ∉ {-n : n ∈ ℕ}` we have `Γ s ≠ 0`.
* `Complex.GammaSeq_tendsto_Gamma`: for all `s`, the limit as `n → ∞` of the sequence
  `n ↦ n ^ s * n! / (s * (s + 1) * ... * (s + n))` is `Γ(s)`.
* `Complex.Gamma_mul_Gamma_one_sub`: Euler's reflection formula
  `Gamma s * Gamma (1 - s) = π / sin π s`.
* `Complex.differentiable_one_div_Gamma`: the function `1 / Γ(s)` is differentiable everywhere.
* `Complex.Gamma_mul_Gamma_add_half`: Legendre's duplication formula
  `Gamma s * Gamma (s + 1 / 2) = Gamma (2 * s) * 2 ^ (1 - 2 * s) * √π`.
* `Real.Gamma_ne_zero`, `Real.GammaSeq_tendsto_Gamma`,
  `Real.Gamma_mul_Gamma_one_sub`, `Real.Gamma_mul_Gamma_add_half`: real versions of the above.
-/

@[expose] public section


noncomputable section


open Filter intervalIntegral Set Real MeasureTheory

open scoped Nat Topology Real

section BetaIntegral

/-! ## The Beta function -/


namespace Complex

/--
Definition of `betaIntegral` / `betaIntegral` 的定义

English:
definition betaIntegral
  signature: (u v : Complex)
  body: ∫ x : Real in 0..1, (x : Complex) ^ (u - 1) * (1 - (x : Complex)) ^ (v - 1)

中文:
定义 beta整数egral
  签名: (u v : 复形)
  定义体: ∫ x : Real in 0..1, (x : Complex) ^ (u - 1) * (1 - (x : Complex)) ^ (v - 1)

Depends on / 依赖: _unit, adj.homEquiv_unit, homEquiv_unit
-/
noncomputable def betaIntegral (u v : Complex) : Complex :=
  ∫ x : Real in 0..1, (x : Complex) ^ (u - 1) * (1 - (x : Complex)) ^ (v - 1)

/--
theorem `betaIntegral_convergent_left` / 定理 `betaIntegral_convergent_left`

English:
theorem betaIntegral_convergent_left
  given: {u : Complex} (hu : 0 < re u) (v : Complex)
  proof: by
  apply IntervalIntegrable.mul_continuousOn
  · refine intervalIntegral.intervalIntegrable_cpow' ?_
    rwa [sub_re, one_re, ← zero_sub, sub_lt_sub_iff_right]
  · apply continuousOn_of_forall_continuousAt
    intro x hx
    rw [uIcc_of_le (by positivity : (0 : Real) <= 1 / 2)] at hx
    apply Con

中文:
定理 beta整数egral_convergent_left
  条件: {u : 复形} (hu : 0 < re u) (v : 复形)
  证明: by
  apply IntervalIntegrable.mul_continuousOn
  · refine intervalIntegral.intervalIntegrable_cpow' ?_
    rwa [sub_re, one_re, ← zero_sub, sub_lt_sub_iff_right]
  · apply continuousOn_of_forall_continuousAt
    intro x hx
    rw [uIcc_of_le (by positivity : (0 : Real) <= 1 / 2)] at hx
    apply Con

Depends on / 依赖: ContinuousAt, ContinuousAt.cpow, IntervalIntegrable, IntervalIntegrable.mul_continuousOn, continuousOn_of_forall_continuousAt, fun_prop, intervalIntegrable_cpow, intervalIntegral, intervalIntegral.intervalIntegrable_cpow, mul_continuousOn, ofReal_mem_slitPlane, one_re, sub_lt_sub_iff_right, sub_re, uIcc_of_le, zero_sub
-/
theorem betaIntegral_convergent_left {u : Complex} (hu : 0 < re u) (v : Complex) :
    IntervalIntegrable (fun x =>
      (x : Complex) ^ (u - 1) * (1 - (x : Complex)) ^ (v - 1) : Real -> Complex) volume 0 (1 / 2) := by
  apply IntervalIntegrable.mul_continuousOn
  · refine intervalIntegral.intervalIntegrable_cpow' ?_
    rwa [sub_re, one_re, ← zero_sub, sub_lt_sub_iff_right]
  · apply continuousOn_of_forall_continuousAt
    intro x hx
    rw [uIcc_of_le (by positivity : (0 : Real) <= 1 / 2)] at hx
    apply ContinuousAt.cpow (by fun_prop) (by fun_prop)
    norm_cast
exact ofReal_mem_slitPlane.2 by linarith only [hx.2]

/--
theorem `betaIntegral_convergent` / 定理 `betaIntegral_convergent`

English:
theorem betaIntegral_convergent
  given: {u v : Complex} (hu : 0 < re u) (hv : 0 < re v)
  proof: by
  refine (betaIntegral_convergent_left hu v).trans ?_
  rw [IntervalIntegrable.iff_comp_neg]
  convert! ((betaIntegral_convergent_left hv u).comp_add_right 1).symm using 1
  · ext1 x
    conv_lhs => rw [mul_comm]
    congr 2 <;> · push_cast; ring
  · norm_num
  · simp

中文:
定理 beta整数egral_convergent
  条件: {u v : 复形} (hu : 0 < re u) (hv : 0 < re v)
  证明: by
  refine (betaIntegral_convergent_left hu v).trans ?_
  rw [IntervalIntegrable.iff_comp_neg]
  convert! ((betaIntegral_convergent_left hv u).comp_add_right 1).symm using 1
  · ext1 x
    conv_lhs => rw [mul_comm]
    congr 2 <;> · push_cast; ring
  · norm_num
  · simp

Depends on / 依赖: IntervalIntegrable, IntervalIntegrable.iff_comp_neg, betaIntegral_convergent_left, comp_add_right, conv_lhs, convert, iff_comp_neg, mul_comm
-/
theorem betaIntegral_convergent {u v : Complex} (hu : 0 < re u) (hv : 0 < re v) :
    IntervalIntegrable (fun x =>
      (x : Complex) ^ (u - 1) * (1 - (x : Complex)) ^ (v - 1) : Real -> Complex) volume 0 1 := by
  refine (betaIntegral_convergent_left hu v).trans ?_
  rw [IntervalIntegrable.iff_comp_neg]
  convert! ((betaIntegral_convergent_left hv u).comp_add_right 1).symm using 1
  · ext1 x
    conv_lhs => rw [mul_comm]
    congr 2 <;> · push_cast; ring
  · norm_num
  · simp

/--
theorem `betaIntegral_symm` / 定理 `betaIntegral_symm`

English:
theorem betaIntegral_symm
  given: (u v : Complex)
  statement: betaIntegral v u = betaIntegral u v
  proof: by
  simpa [betaIntegral, ← intervalIntegral.integral_symm, add_comm, mul_comm, sub_eq_add_neg]
    using intervalIntegral.integral_comp_mul_add (a := 0) (b := 1) (c := -1)
      (fun x : Real => (x : Complex) ^ (u - 1) * (1 - (x : Complex)) ^ (v - 1)) neg_one_lt_zero.ne 1

中文:
定理 beta整数egral_symm
  条件: (u v : 复形)
  结论: beta整数egral v u = beta整数egral u v
  证明: by
  simpa [betaIntegral, ← intervalIntegral.integral_symm, add_comm, mul_comm, sub_eq_add_neg]
    using intervalIntegral.integral_comp_mul_add (a := 0) (b := 1) (c := -1)
      (fun x : Real => (x : Complex) ^ (u - 1) * (1 - (x : Complex)) ^ (v - 1)) neg_one_lt_zero.ne 1

Depends on / 依赖: add_comm, betaIntegral, integral_comp_mul_add, integral_symm, intervalIntegral, intervalIntegral.integral_comp_mul_add, intervalIntegral.integral_symm, mul_comm, neg_one_lt_zero, neg_one_lt_zero.ne, sub_eq_add_neg
-/
theorem betaIntegral_symm (u v : Complex) : betaIntegral v u = betaIntegral u v := by
  simpa [betaIntegral, ← intervalIntegral.integral_symm, add_comm, mul_comm, sub_eq_add_neg]
    using intervalIntegral.integral_comp_mul_add (a := 0) (b := 1) (c := -1)
      (fun x : Real => (x : Complex) ^ (u - 1) * (1 - (x : Complex)) ^ (v - 1)) neg_one_lt_zero.ne 1

/--
theorem `betaIntegral_eval_one_right` / 定理 `betaIntegral_eval_one_right`

English:
theorem betaIntegral_eval_one_right
  given: {u : Complex} (hu : 0 < re u)
  statement: betaIntegral u 1 = 1 / u
  proof: by
  simp_rw [betaIntegral, sub_self, cpow_zero, mul_one]
  rw [integral_cpow (Or.inl _)]
  · rw [ofReal_zero, ofReal_one, one_cpow, zero_cpow, sub_zero, sub_add_cancel]
    rw [sub_add_cancel]
    contrapose! hu; rw [hu, zero_re]
  · rwa [sub_re, one_re, ← sub_pos, sub_neg_eq_add, sub_add_cancel]

中文:
定理 beta整数egral_eval_one_right
  条件: {u : 复形} (hu : 0 < re u)
  结论: beta整数egral u 1 = 1 / u
  证明: by
  simp_rw [betaIntegral, sub_self, cpow_zero, mul_one]
  rw [integral_cpow (Or.inl _)]
  · rw [ofReal_zero, ofReal_one, one_cpow, zero_cpow, sub_zero, sub_add_cancel]
    rw [sub_add_cancel]
    contrapose! hu; rw [hu, zero_re]
  · rwa [sub_re, one_re, ← sub_pos, sub_neg_eq_add, sub_add_cancel]

Depends on / 依赖: Or.inl, betaIntegral, contrapose, cpow_zero, integral_cpow, mul_one, ofReal_one, ofReal_zero, one_cpow, one_re, simp_rw, sub_add_cancel, sub_neg_eq_add, sub_pos, sub_re, sub_self, sub_zero, zero_cpow, zero_re
-/
theorem betaIntegral_eval_one_right {u : Complex} (hu : 0 < re u) : betaIntegral u 1 = 1 / u := by
  simp_rw [betaIntegral, sub_self, cpow_zero, mul_one]
  rw [integral_cpow (Or.inl _)]
  · rw [ofReal_zero, ofReal_one, one_cpow, zero_cpow, sub_zero, sub_add_cancel]
    rw [sub_add_cancel]
    contrapose! hu; rw [hu, zero_re]
  · rwa [sub_re, one_re, ← sub_pos, sub_neg_eq_add, sub_add_cancel]

/--
theorem `betaIntegral_scaled` / 定理 `betaIntegral_scaled`

English:
theorem betaIntegral_scaled
  given: (s t : Complex) {a : Real} (ha : 0 < a)
  proof: by
  have ha' : (a : Complex) != 0 := ofReal_ne_zero.mpr ha.ne'
  rw [betaIntegral]
  have A : (a : Complex) ^ (s + t - 1) = a * ((a : Complex) ^ (s - 1) * (a : Complex) ^ (t - 1)) := by
    rw [(by abel : s + t - 1 = 1 + (s - 1) + (t - 1))]; rw [cpow_add _ _ ha']; rw [cpow_add 1 _ ha']; rw [cpow_on

中文:
定理 beta整数egral_scaled
  条件: (s t : 复形) {a : 实数} (ha : 0 < a)
  证明: by
  have ha' : (a : Complex) != 0 := ofReal_ne_zero.mpr ha.ne'
  rw [betaIntegral]
  have A : (a : Complex) ^ (s + t - 1) = a * ((a : Complex) ^ (s - 1) * (a : Complex) ^ (t - 1)) := by
    rw [(by abel : s + t - 1 = 1 + (s - 1) + (t - 1))]; rw [cpow_add _ _ ha']; rw [cpow_add 1 _ ha']; rw [cpow_on

Depends on / 依赖: betaIntegral, cpow_add, cpow_one, div_self, ha.ne, integral_comp_div, integral_const_mul, intervalIntegral, intervalIntegral.integral_comp_div, intervalIntegral.integral_const_mul, mul_assoc, ofReal_ne_zero, ofReal_ne_zero.mpr, real_smul, zero_d, zero_div
-/
theorem betaIntegral_scaled (s t : Complex) {a : Real} (ha : 0 < a) :
    ∫ x in 0..a, (x : Complex) ^ (s - 1) * ((a : Complex) - x) ^ (t - 1) =
    (a : Complex) ^ (s + t - 1) * betaIntegral s t := by
  have ha' : (a : Complex) != 0 := ofReal_ne_zero.mpr ha.ne'
  rw [betaIntegral]
  have A : (a : Complex) ^ (s + t - 1) = a * ((a : Complex) ^ (s - 1) * (a : Complex) ^ (t - 1)) := by
    rw [(by abel : s + t - 1 = 1 + (s - 1) + (t - 1))]; rw [cpow_add _ _ ha']; rw [cpow_add 1 _ ha']; rw [cpow_one]; rw [mul_assoc]
  rw [A]; rw [mul_assoc]; rw [← intervalIntegral.integral_const_mul]; rw [← real_smul]; rw [← zero_div a]; rw [←
    div_self ha.ne']; rw [← intervalIntegral.integral_comp_div _ ha.ne']; rw [zero_div]
  simp_rw [intervalIntegral.integral_of_le ha.le]
  refine setIntegral_congr_fun measurableSet_Ioc fun x hx => ?_
  rw [mul_mul_mul_comm]
  congr 1
  · rw [← mul_cpow_ofReal_nonneg ha.le (div_pos hx.1 ha).le, ofReal_div, mul_div_cancel₀ _ ha']
  · rw [(by norm_cast : (1 : Complex) - ↑(x / a) = ↑(1 - x / a)), ←
      mul_cpow_ofReal_nonneg ha.le (sub_nonneg.mpr <| (div_le_one ha).mpr hx.2)]
    push_cast
    rw [mul_sub]; rw [mul_one]; rw [mul_div_cancel₀ _ ha']

/--
theorem `Gamma_mul_Gamma_eq_betaIntegral` / 定理 `Gamma_mul_Gamma_eq_betaIntegral`

English:
theorem Gamma_mul_Gamma_eq_betaIntegral
  given: {s t : Complex} (hs : 0 < re s) (ht : 0 < re t)
  proof: by
  -- Note that we haven't proved (yet) that the Gamma function has no zeroes, so we can't formulate
  -- this as a formula for the Beta function.
  have conv_int := integral_posConvolution
    (GammaIntegral_convergent hs) (GammaIntegral_convergent ht) (ContinuousLinearMap.mul Real Complex)
  sim

中文:
定理 Gamma_mul_Gamma_eq_beta整数egral
  条件: {s t : 复形} (hs : 0 < re s) (ht : 0 < re t)
  证明: by
  -- Note that we haven't proved (yet) that the Gamma function has no zeroes, so we can't formulate
  -- this as a formula for the Beta function.
  have conv_int := integral_posConvolution
    (GammaIntegral_convergent hs) (GammaIntegral_convergent ht) (ContinuousLinearMap.mul Real Complex)
  sim
-/
theorem Gamma_mul_Gamma_eq_betaIntegral {s t : Complex} (hs : 0 < re s) (ht : 0 < re t) :
    Gamma s * Gamma t = Gamma (s + t) * betaIntegral s t := by
  -- Note that we haven't proved (yet) that the Gamma function has no zeroes, so we can't formulate
  -- this as a formula for the Beta function.
  have conv_int := integral_posConvolution
    (GammaIntegral_convergent hs) (GammaIntegral_convergent ht) (ContinuousLinearMap.mul Real Complex)
  simp_rw [ContinuousLinearMap.mul_apply'] at conv_int
  have hst : 0 < re (s + t) := by rw [add_re]; exact add_pos hs ht
  rw [Gamma_eq_integral hs]; rw [Gamma_eq_integral ht]; rw [Gamma_eq_integral hst]; rw [GammaIntegral]; rw [GammaIntegral]; rw [GammaIntegral]; rw [← conv_int]; rw [← MeasureTheory.integral_mul_const (betaIntegral _ _)]
  refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
  rw [mul_assoc]; rw [← betaIntegral_scaled s t hx]; rw [← intervalIntegral.integral_const_mul]
  congr 1 with y : 1
  push_cast
  suffices Complex.exp (-x) = Complex.exp (-y) * Complex.exp (-(x - y)) by rw [this]; ring
  rw [← Complex.exp_add]; congr 1; abel

/--
theorem `betaIntegral_recurrence` / 定理 `betaIntegral_recurrence`

English:
theorem betaIntegral_recurrence
  given: {u v : Complex} (hu : 0 < re u) (hv : 0 < re v)
  proof: by
  -- NB: If we knew `Gamma (u + v + 1) ≠ 0` this would be an easy consequence of
  -- `Gamma_mul_Gamma_eq_betaIntegral`; but we don't know that yet. We will prove it later, but
  -- this lemma is needed in the proof. So we give a (somewhat laborious) direct argument.
  let F : Real -> Complex := 

中文:
定理 beta整数egral_recurrence
  条件: {u v : 复形} (hu : 0 < re u) (hv : 0 < re v)
  证明: by
  -- NB: If we knew `Gamma (u + v + 1) ≠ 0` this would be an easy consequence of
  -- `Gamma_mul_Gamma_eq_betaIntegral`; but we don't know that yet. We will prove it later, but
  -- this lemma is needed in the proof. So we give a (somewhat laborious) direct argument.
  let F : Real -> Complex := 
-/
theorem betaIntegral_recurrence {u v : Complex} (hu : 0 < re u) (hv : 0 < re v) :
    u * betaIntegral u (v + 1) = v * betaIntegral (u + 1) v := by
  -- NB: If we knew `Gamma (u + v + 1) ≠ 0` this would be an easy consequence of
  -- `Gamma_mul_Gamma_eq_betaIntegral`; but we don't know that yet. We will prove it later, but
  -- this lemma is needed in the proof. So we give a (somewhat laborious) direct argument.
  let F : Real -> Complex := fun x => (x : Complex) ^ u * (1 - (x : Complex)) ^ v
  have hu' : 0 < re (u + 1) := by rw [add_re, one_re]; positivity
  have hv' : 0 < re (v + 1) := by rw [add_re, one_re]; positivity
  have hc : ContinuousOn F (Icc 0 1) := by
    refine (continuousOn_of_forall_continuousAt fun x hx => ?_).mul
        (continuousOn_of_forall_continuousAt fun x hx => ?_)
    · refine (continuousAt_cpow_const_of_re_pos (Or.inl ?_) hu).comp continuous_ofReal.continuousAt
      rw [ofReal_re]; exact hx.1
    · refine (continuousAt_cpow_const_of_re_pos (Or.inl ?_) hv).comp (by fun_prop)
      rw [sub_re]; rw [one_re]; rw [ofReal_re]; rw [sub_nonneg]
      exact hx.2
  have hder : forall x : Real, x in Ioo (0 : Real) 1 ->
      HasDerivAt F (u * ((x : Complex) ^ (u - 1) * (1 - (x : Complex)) ^ v) -
        v * ((x : Complex) ^ u * (1 - (x : Complex)) ^ (v - 1))) x := by
    intro x hx
    have U : HasDerivAt (fun y : Complex => y ^ u) (u * (x : Complex) ^ (u - 1)) ↑x := by
      have := @HasDerivAt.cpow_const _ _ _ u (hasDerivAt_id (x : Complex)) (Or.inl ?_)
      · simp only [id_eq, mul_one] at this
        exact this
      · rw [id_eq, ofReal_re]; exact hx.1
    have V : HasDerivAt (fun y : Complex => (1 - y) ^ v) (-v * (1 - (x : Complex)) ^ (v - 1)) ↑x := by
      have A := @HasDerivAt.cpow_const _ _ _ v (hasDerivAt_id (1 - (x : Complex))) (Or.inl ?_)
      swap; · rw [id, sub_re, one_re, ofReal_re, sub_pos]; exact hx.2
      simp_rw [id] at A
      have B : HasDerivAt (fun y : Complex => 1 - y) (-1) ↑x := by
        apply HasDerivAt.const_sub; apply hasDerivAt_id
      convert! HasDerivAt.comp (↑x) A B using 1
      ring
    convert! (U.mul V).comp_ofReal using 1
    ring
  have h_int := ((betaIntegral_convergent hu hv').const_mul u).sub
    ((betaIntegral_convergent hu' hv).const_mul v)
  rw [add_sub_cancel_right]; rw [add_sub_cancel_right] at h_int
  have int_ev := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one hc hder h_int
  have hF0 : F 0 = 0 := by
    simp only [F, mul_eq_zero, ofReal_zero, cpow_eq_zero_iff, Ne,
      true_and, sub_zero, one_cpow, one_ne_zero, or_false]
    contrapose! hu; rw [hu, zero_re]
  have hF1 : F 1 = 0 := by
    simp only [F, mul_eq_zero, ofReal_one, one_cpow, one_ne_zero, sub_self, cpow_eq_zero_iff,
      Ne, true_and, false_or]
    contrapose! hv; rw [hv, zero_re]
  rw [hF0]; rw [hF1]; rw [sub_zero]; rw [intervalIntegral.integral_sub]; rw [intervalIntegral.integral_const_mul]; rw [intervalIntegral.integral_const_mul] at int_ev
  · rw [betaIntegral, betaIntegral, ← sub_eq_zero]
    convert! int_ev <;> ring
  · apply IntervalIntegrable.const_mul
    convert! betaIntegral_convergent hu hv'; ring
  · apply IntervalIntegrable.const_mul
    convert! betaIntegral_convergent hu' hv; ring

/--
theorem `betaIntegral_eval_nat_add_one_right` / 定理 `betaIntegral_eval_nat_add_one_right`

English:
theorem betaIntegral_eval_nat_add_one_right
  given: {u : Complex} (hu : 0 < re u) (n : Nat)
  proof: by
  induction n generalizing u with
  | zero =>
    rw [Nat.cast_zero]; rw [zero_add]; rw [betaIntegral_eval_one_right hu]; rw [Nat.factorial_zero]; rw [Nat.cast_one]
    simp
  | succ n IH =>
    have := betaIntegral_recurrence hu (?_ : 0 < re n.succ)
    swap; · rw [← ofReal_natCast, ofReal_re]; 

中文:
定理 beta整数egral_eval_nat_add_one_right
  条件: {u : 复形} (hu : 0 < re u) (n : 自然数)
  证明: by
  induction n generalizing u with
  | zero =>
    rw [Nat.cast_zero]; rw [zero_add]; rw [betaIntegral_eval_one_right hu]; rw [Nat.factorial_zero]; rw [Nat.cast_one]
    simp
  | succ n IH =>
    have := betaIntegral_recurrence hu (?_ : 0 < re n.succ)
    swap; · rw [← ofReal_natCast, ofReal_re]; 

Depends on / 依赖: Finset, Finset.prod_range_succ, Nat.cast_one, Nat.cast_succ, Nat.cast_zero, Nat.factoria, Nat.factorial_zero, add_re, betaIntegral_eval_one_right, betaIntegral_recurrence, cast_one, cast_succ, cast_zero, contrapose, eq_div_iff, factoria, factorial_zero, generalizing, mul_comm, n.succ
-/
theorem betaIntegral_eval_nat_add_one_right {u : Complex} (hu : 0 < re u) (n : Nat) :
    betaIntegral u (n + 1) = n ! / ∏ j in Finset.range (n + 1), (u + j) := by
  induction n generalizing u with
  | zero =>
    rw [Nat.cast_zero]; rw [zero_add]; rw [betaIntegral_eval_one_right hu]; rw [Nat.factorial_zero]; rw [Nat.cast_one]
    simp
  | succ n IH =>
    have := betaIntegral_recurrence hu (?_ : 0 < re n.succ)
    swap; · rw [← ofReal_natCast, ofReal_re]; positivity
    rw [mul_comm u _]; rw [← eq_div_iff] at this
    swap; · contrapose! hu; rw [hu, zero_re]
    rw [this]; rw [Finset.prod_range_succ']; rw [Nat.cast_succ]; rw [IH]
    swap; · rw [add_re, one_re]; positivity
    rw [Nat.factorial_succ]; rw [Nat.cast_mul]; rw [Nat.cast_add]; rw [Nat.cast_one]; rw [Nat.cast_zero]; rw [add_zero]; rw [←
      mul_div_assoc]; rw [← div_div]
    congr 3 with j : 1
    push_cast; abel

end Complex

end BetaIntegral

section LimitFormula

/-! ## The Euler limit formula -/


namespace Complex

/--
Definition of `GammaSeq` / `GammaSeq` 的定义

English:
definition GammaSeq
  signature: (s : Complex) (n : Nat)
  body: (n : Complex) ^ s * n ! / ∏ j in Finset.range (n + 1), (s + j)

中文:
定义 GammaSeq
  签名: (s : 复形) (n : 自然数)
  定义体: (n : Complex) ^ s * n ! / ∏ j in Finset.range (n + 1), (s + j)

Depends on / 依赖: Finset, Finset.range
-/
noncomputable def GammaSeq (s : Complex) (n : Nat) :=
  (n : Complex) ^ s * n ! / ∏ j in Finset.range (n + 1), (s + j)

/--
theorem `GammaSeq_eq_betaIntegral_of_re_pos` / 定理 `GammaSeq_eq_betaIntegral_of_re_pos`

English:
theorem GammaSeq_eq_betaIntegral_of_re_pos
  given: {s : Complex} (hs : 0 < re s) (n : Nat)
  proof: by
  rw [GammaSeq]; rw [betaIntegral_eval_nat_add_one_right hs n]; rw [← mul_div_assoc]

中文:
定理 GammaSeq_eq_beta整数egral_of_re_pos
  条件: {s : 复形} (hs : 0 < re s) (n : 自然数)
  证明: by
  rw [GammaSeq]; rw [betaIntegral_eval_nat_add_one_right hs n]; rw [← mul_div_assoc]

Depends on / 依赖: GammaSeq, betaIntegral_eval_nat_add_one_right, mul_div_assoc
-/
theorem GammaSeq_eq_betaIntegral_of_re_pos {s : Complex} (hs : 0 < re s) (n : Nat) :
    GammaSeq s n = (n : Complex) ^ s * betaIntegral s (n + 1) := by
  rw [GammaSeq]; rw [betaIntegral_eval_nat_add_one_right hs n]; rw [← mul_div_assoc]

/--
theorem `GammaSeq_add_one_left` / 定理 `GammaSeq_add_one_left`

English:
theorem GammaSeq_add_one_left
  given: (s : Complex) {n : Nat} (hn : n != 0)
  proof: by
  conv_lhs => rw [GammaSeq, Finset.prod_range_succ, div_div]
  conv_rhs =>
    rw [GammaSeq]; rw [Finset.prod_range_succ']; rw [Nat.cast_zero]; rw [add_zero]; rw [div_mul_div_comm]; rw [← mul_assoc]; rw [← mul_assoc]; rw [mul_comm _ (Finset.prod _ _)]
  congr 3
  · rw [cpow_add _ _ (Nat.cast_ne_z

中文:
定理 GammaSeq_add_one_left
  条件: (s : 复形) {n : 自然数} (hn : n != 0)
  证明: by
  conv_lhs => rw [GammaSeq, Finset.prod_range_succ, div_div]
  conv_rhs =>
    rw [GammaSeq]; rw [Finset.prod_range_succ']; rw [Nat.cast_zero]; rw [add_zero]; rw [div_mul_div_comm]; rw [← mul_assoc]; rw [← mul_assoc]; rw [mul_comm _ (Finset.prod _ _)]
  congr 3
  · rw [cpow_add _ _ (Nat.cast_ne_z

Depends on / 依赖: Finset, Finset.prod, Finset.prod_congr, Finset.prod_range_succ, GammaSeq, Nat.cast_ne_zero.mpr, Nat.cast_zero, add_zero, cast_ne_zero, cast_zero, conv_lhs, conv_rhs, cpow_add, cpow_one, div_div, div_mul_div_comm, mul_assoc, mul_comm, prod_congr, prod_range_succ
-/
theorem GammaSeq_add_one_left (s : Complex) {n : Nat} (hn : n != 0) :
    GammaSeq (s + 1) n / s = n / (n + 1 + s) * GammaSeq s n := by
  conv_lhs => rw [GammaSeq, Finset.prod_range_succ, div_div]
  conv_rhs =>
    rw [GammaSeq]; rw [Finset.prod_range_succ']; rw [Nat.cast_zero]; rw [add_zero]; rw [div_mul_div_comm]; rw [← mul_assoc]; rw [← mul_assoc]; rw [mul_comm _ (Finset.prod _ _)]
  congr 3
  · rw [cpow_add _ _ (Nat.cast_ne_zero.mpr hn), cpow_one, mul_comm]
  · refine Finset.prod_congr rfl fun x _ => ?_
    push_cast; ring
  · abel

/--
theorem `GammaSeq_eq_approx_Gamma_integral` / 定理 `GammaSeq_eq_approx_Gamma_integral`

English:
theorem GammaSeq_eq_approx_Gamma_integral
  given: {s : Complex} (hs : 0 < re s) {n : Nat} (hn : n != 0)
  proof: by
  have : forall x : Real, x = x / n * n := by intro x; rw [div_mul_cancel₀]; exact Nat.cast_ne_zero.mpr hn
  conv_rhs => enter [1, x, 2, 1]; rw [this x]
  rw [GammaSeq_eq_betaIntegral_of_re_pos hs]
  have := intervalIntegral.integral_comp_div (a := 0) (b := n)
    (fun x => ↑((1 - x) ^ n) * ↑(x *

中文:
定理 GammaSeq_eq_approx_Gamma_integral
  条件: {s : 复形} (hs : 0 < re s) {n : 自然数} (hn : n != 0)
  证明: by
  have : forall x : Real, x = x / n * n := by intro x; rw [div_mul_cancel₀]; exact Nat.cast_ne_zero.mpr hn
  conv_rhs => enter [1, x, 2, 1]; rw [this x]
  rw [GammaSeq_eq_betaIntegral_of_re_pos hs]
  have := intervalIntegral.integral_comp_div (a := 0) (b := n)
    (fun x => ↑((1 - x) ^ n) * ↑(x *

Depends on / 依赖: GammaSeq_eq_betaIntegral_of_re_pos, Nat.cast_ne_zero.mpr, add_sub_cancel_right, betaIntegral, cast_ne_zero, conv_rhs, div_self, integral_comp_div, integral_const_mul, intervalIntegral, intervalIntegral.integral_comp_div, intervalIntegral.integral_const_mul, real_smul, zero_div
-/
theorem GammaSeq_eq_approx_Gamma_integral {s : Complex} (hs : 0 < re s) {n : Nat} (hn : n != 0) :
    GammaSeq s n = ∫ x : Real in 0..n, ↑((1 - x / n) ^ n) * (x : Complex) ^ (s - 1) := by
  have : forall x : Real, x = x / n * n := by intro x; rw [div_mul_cancel₀]; exact Nat.cast_ne_zero.mpr hn
  conv_rhs => enter [1, x, 2, 1]; rw [this x]
  rw [GammaSeq_eq_betaIntegral_of_re_pos hs]
  have := intervalIntegral.integral_comp_div (a := 0) (b := n)
    (fun x => ↑((1 - x) ^ n) * ↑(x * ↑n) ^ (s - 1) : Real -> Complex) (Nat.cast_ne_zero.mpr hn)
  rw [betaIntegral]; rw [this]; rw [real_smul]; rw [zero_div]; rw [div_self]; rw [add_sub_cancel_right]; rw [← intervalIntegral.integral_const_mul]; rw [← intervalIntegral.integral_const_mul]
  swap; · exact Nat.cast_ne_zero.mpr hn
  simp_rw [intervalIntegral.integral_of_le zero_le_one]
  refine setIntegral_congr_fun measurableSet_Ioc fun x hx => ?_
  push_cast
  have hn' : (n : Complex) != 0 := Nat.cast_ne_zero.mpr hn
  have A : (n : Complex) ^ s = (n : Complex) ^ (s - 1) * n := by
    conv_lhs => rw [(by ring : s = s - 1 + 1), cpow_add _ _ hn']
    simp
  have B : ((x : Complex) * ↑n) ^ (s - 1) = (x : Complex) ^ (s - 1) * (n : Complex) ^ (s - 1) := by
    rw [← ofReal_natCast]; rw [mul_cpow_ofReal_nonneg hx.1.le (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)).le]
  rw [A]; rw [B]; rw [cpow_natCast]; ring

/--
theorem `approx_Gamma_integral_tendsto_Gamma_integral` / 定理 `approx_Gamma_integral_tendsto_Gamma_integral`

English:
theorem approx_Gamma_integral_tendsto_Gamma_integral
  given: {s : Complex} (hs : 0 < re s)
  proof: by
  rw [Gamma_eq_integral hs]
  -- We apply dominated convergence to the following function, which we will show is uniformly
  -- bounded above by the Gamma integrand `exp (-x) * x ^ (re s - 1)`.
  let f : Nat -> Real -> Complex := fun n =>
    indicator (Ioc 0 (n : Real)) fun x : Real => ((1 - x /

中文:
定理 approx_Gamma_integral_tendsto_Gamma_integral
  条件: {s : 复形} (hs : 0 < re s)
  证明: by
  rw [Gamma_eq_integral hs]
  -- We apply dominated convergence to the following function, which we will show is uniformly
  -- bounded above by the Gamma integrand `exp (-x) * x ^ (re s - 1)`.
  let f : Nat -> Real -> Complex := fun n =>
    indicator (Ioc 0 (n : Real)) fun x : Real => ((1 - x /

Depends on / 依赖: Gamma_eq_integral
-/
theorem approx_Gamma_integral_tendsto_Gamma_integral {s : Complex} (hs : 0 < re s) :
    Tendsto (fun n : Nat => ∫ x : Real in 0..n, ((1 - x / n) ^ n : Real) * (x : Complex) ^ (s - 1)) atTop
      (𝓝 <| Gamma s) := by
  rw [Gamma_eq_integral hs]
  -- We apply dominated convergence to the following function, which we will show is uniformly
  -- bounded above by the Gamma integrand `exp (-x) * x ^ (re s - 1)`.
  let f : Nat -> Real -> Complex := fun n =>
    indicator (Ioc 0 (n : Real)) fun x : Real => ((1 - x / n) ^ n : Real) * (x : Complex) ^ (s - 1)
  -- integrability of f
  have f_ible : forall n : Nat, Integrable (f n) (volume.restrict (Ioi 0)) := by
    intro n
    rw [integrable_indicator_iff (measurableSet_Ioc : MeasurableSet (Ioc (_ : Real) _))]; rw [IntegrableOn]; rw [Measure.restrict_restrict_of_subset Ioc_subset_Ioi_self]; rw [← IntegrableOn]; rw [←
      intervalIntegrable_iff_integrableOn_Ioc_of_le (by positivity : (0 : Real) <= n)]
    apply IntervalIntegrable.continuousOn_mul
    · refine intervalIntegral.intervalIntegrable_cpow' ?_
      rwa [sub_re, one_re, ← zero_sub, sub_lt_sub_iff_right]
    · fun_prop
  -- pointwise limit of f
  have f_tends : forall x : Real, x in Ioi (0 : Real) ->
      Tendsto (fun n : Nat => f n x) atTop (𝓝 <| ↑(Real.exp (-x)) * (x : Complex) ^ (s - 1)) := by
    intro x hx
    apply Tendsto.congr'
    · change forallᶠ n : Nat in atTop, ↑((1 - x / n) ^ n) * (x : Complex) ^ (s - 1) = f n x
      filter_upwards [eventually_ge_atTop ⌈x⌉₊] with n hn
      rw [Nat.ceil_le] at hn
      dsimp only [f]
      rw [indicator_of_mem]
      exact ⟨hx, hn⟩
    · simp_rw [mul_comm]
      refine (Tendsto.comp (continuous_ofReal.tendsto _) ?_).const_mul _
      convert! Real.tendsto_one_add_div_pow_exp (-x) using 1
      ext1 n
      rw [neg_div]; rw [← sub_eq_add_neg]
  -- let `convert` identify the remaining goals
  convert!
    tendsto_integral_of_dominated_convergence _ (fun n => (f_ible n).1)
      (Real.GammaIntegral_convergent hs) _
      ((ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ f_tends)) using 1
    -- limit of f is the integrand we want

  -- limit of f is the integrand we want
  · ext1 n
    rw [MeasureTheory.integral_indicator (measurableSet_Ioc : MeasurableSet (Ioc (_ : Real) _))]; rw [intervalIntegral.integral_of_le (by positivity : 0 <= (n : Real))]; rw [Measure.restrict_restrict_of_subset Ioc_subset_Ioi_self]
  -- f is uniformly bounded by the Gamma integrand
  · intro n
    rw [ae_restrict_iff' measurableSet_Ioi]
    filter_upwards with x hx
    simp only [mem_Ioi, f] at hx ⊢
    rcases lt_or_ge (n : Real) x with (hxn | hxn)
    · rw [indicator_of_notMem (notMem_Ioc_of_gt hxn), norm_zero,
        mul_nonneg_iff_right_nonneg_of_pos (exp_pos _)]
      positivity
    · rw [indicator_of_mem (mem_Ioc.mpr ⟨mem_Ioi.mp hx, hxn⟩), norm_mul, Complex.norm_of_nonneg
          (pow_nonneg (sub_nonneg.mpr <| div_le_one_of_le₀ hxn <| by positivity) _),
          norm_cpow_eq_rpow_re_of_pos hx, sub_re, one_re]
      gcongr
      exact one_sub_div_pow_le_exp_neg hxn

/--
theorem `GammaSeq_tendsto_Gamma` / 定理 `GammaSeq_tendsto_Gamma`

English:
theorem GammaSeq_tendsto_Gamma
  given: (s : Complex)
  statement: Tendsto (GammaSeq s) atTop (𝓝 <| Gamma s)
  proof: by
  suffices forall m : Nat, ⌊1 - s.re⌋₊ = m -> Tendsto (GammaSeq s) atTop (𝓝 <| Gamma s) by tauto
  intro m
  induction m generalizing s with intro hs
  | zero => -- Base case: `0 < re s`, so Gamma is given by the integral formula
    rw [Nat.floor_eq_zero]; rw [sub_lt_self_iff] at hs
    apply (a

中文:
定理 GammaSeq_tendsto_Gamma
  条件: (s : 复形)
  结论: 收敛 (GammaSeq s) atTop (𝓝 <| Gamma s)
  证明: by
  suffices forall m : Nat, ⌊1 - s.re⌋₊ = m -> Tendsto (GammaSeq s) atTop (𝓝 <| Gamma s) by tauto
  intro m
  induction m generalizing s with intro hs
  | zero => -- Base case: `0 < re s`, so Gamma is given by the integral formula
    rw [Nat.floor_eq_zero]; rw [sub_lt_self_iff] at hs
    apply (a

Depends on / 依赖: GammaSeq, GammaSeq_eq_approx_Gamma_integral, Induction, Nat.floor_eq_zero, Tendsto, approx_Gamma_integral_tendsto_Gamma_integral, eventually_ne_atTop, filter_upwards, floor_eq_zero, formula, formulae, generalizing, integral, recurrence, s.re, sub_lt_self_iff
-/
theorem GammaSeq_tendsto_Gamma (s : Complex) : Tendsto (GammaSeq s) atTop (𝓝 <| Gamma s) := by
  suffices forall m : Nat, ⌊1 - s.re⌋₊ = m -> Tendsto (GammaSeq s) atTop (𝓝 <| Gamma s) by tauto
  intro m
  induction m generalizing s with intro hs
  | zero => -- Base case: `0 < re s`, so Gamma is given by the integral formula
    rw [Nat.floor_eq_zero]; rw [sub_lt_self_iff] at hs
    apply (approx_Gamma_integral_tendsto_Gamma_integral hs).congr'
    filter_upwards [eventually_ne_atTop 0] with n hn using
      (GammaSeq_eq_approx_Gamma_integral hs hn).symm
  | succ m IH => -- Induction step: use recurrence formulae in `s` for Gamma and GammaSeq
    -- Silly case `s = 0`: both sides are zero
    rcases eq_or_ne s 0 with rfl | hsne
    · unfold GammaSeq
      simp [Finset.prod_range_succ']
    specialize IH (s + 1) ?_
    · rw [Nat.floor_eq_iff' (by lia)] at hs
      have : s.re <= -m := by grind
      rw [Nat.floor_eq_iff <| by simpa using (show s.re <= 0 by grind)]
      grind [add_re, one_re]
    rw [Gamma_add_one _ hsne] at IH
have := (IH.div_const s).congr' by
      filter_upwards [eventually_ne_atTop 0] with n using GammaSeq_add_one_left s
    simp only [mul_comm _ (s.GammaSeq _)] at this
    rwa [mul_div_cancel_left₀ _ hsne, ← mul_one (Gamma s),
      tendsto_mul_iff_of_ne_zero _ (one_ne_zero' Complex)] at this
    simp_rw [add_assoc]
    exact tendsto_natCast_div_add_atTop (1 + s)

end Complex

end LimitFormula

section GammaReflection

/-! ## The reflection formula -/


namespace Complex

/--
theorem `GammaSeq_mul` / 定理 `GammaSeq_mul`

English:
theorem GammaSeq_mul
  given: (z : Complex) {n : Nat} (hn : n != 0)
  proof: by
  -- also true for n = 0 but we don't need it
  have aux : forall a b c d : Complex, a * b * (c * d) = a * c * (b * d) := by intros; ring
  rw [GammaSeq]; rw [GammaSeq]; rw [div_mul_div_comm]; rw [aux]; rw [← pow_two]
  have : (n : Complex) ^ z * (n : Complex) ^ (1 - z) = n := by
    rw [← cpow_a

中文:
定理 GammaSeq_mul
  条件: (z : 复形) {n : 自然数} (hn : n != 0)
  证明: by
  -- also true for n = 0 but we don't need it
  have aux : forall a b c d : Complex, a * b * (c * d) = a * c * (b * d) := by intros; ring
  rw [GammaSeq]; rw [GammaSeq]; rw [div_mul_div_comm]; rw [aux]; rw [← pow_two]
  have : (n : Complex) ^ z * (n : Complex) ^ (1 - z) = n := by
    rw [← cpow_a
-/
theorem GammaSeq_mul (z : Complex) {n : Nat} (hn : n != 0) :
    GammaSeq z n * GammaSeq (1 - z) n =
      n / (n + ↑1 - z) * (↑1 / (z * ∏ j in Finset.range n, (↑1 - z ^ 2 / ((j : Complex) + 1) ^ 2))) := by
  -- also true for n = 0 but we don't need it
  have aux : forall a b c d : Complex, a * b * (c * d) = a * c * (b * d) := by intros; ring
  rw [GammaSeq]; rw [GammaSeq]; rw [div_mul_div_comm]; rw [aux]; rw [← pow_two]
  have : (n : Complex) ^ z * (n : Complex) ^ (1 - z) = n := by
    rw [← cpow_add _ _ (Nat.cast_ne_zero.mpr hn)]; rw [add_sub_cancel]; rw [cpow_one]
  rw [this]; rw [Finset.prod_range_succ']; rw [Finset.prod_range_succ]; rw [aux]; rw [← Finset.prod_mul_distrib]; rw [Nat.cast_zero]; rw [add_zero]; rw [add_comm (1 - z) n]; rw [← add_sub_assoc]
  have : forall j : Nat, (z + ↑(j + 1)) * (↑1 - z + ↑j) =
      ((j + 1) ^ 2 :) * (↑1 - z ^ 2 / ((j : Complex) + 1) ^ 2) := by
    intro j
    push_cast
    have : (j : Complex) + 1 != 0 := by rw [← Nat.cast_succ, Nat.cast_ne_zero]; exact Nat.succ_ne_zero j
    field
  simp_rw [this]
  rw [Finset.prod_mul_distrib]; rw [← Nat.cast_prod]; rw [Finset.prod_pow]; rw [Finset.prod_range_add_one_eq_factorial]; rw [Nat.cast_pow]; rw [(by intros; ring : forall a b c d : Complex]; rw [a * b * (c * d) = a * (d * (b * c)))]; rw [← div_div]; rw [mul_div_cancel_right₀]; rw [← div_div]; rw [mul_comm z _]; rw [mul_one_div]
  exact pow_ne_zero 2 (Nat.cast_ne_zero.mpr <| by positivity)

/--
theorem `Gamma_mul_Gamma_one_sub` / 定理 `Gamma_mul_Gamma_one_sub`

English:
theorem Gamma_mul_Gamma_one_sub
  given: (z : Complex)
  statement: Gamma z * Gamma (1 - z) = π / sin (π * z)
  proof: by
  have pi_ne : (π : Complex) != 0 := Complex.ofReal_ne_zero.mpr pi_ne_zero
  by_cases hs : sin (↑π * z) = 0
  · -- first deal with silly case z = integer
    rw [hs]; rw [div_zero]
    rw [← neg_eq_zero]; rw [← Complex.sin_neg]; rw [← mul_neg]; rw [Complex.sin_eq_zero_iff]; rw [mul_comm] at hs
  

中文:
定理 Gamma_mul_Gamma_one_sub
  条件: (z : 复形)
  结论: Gamma z * Gamma (1 - z) = π / sin (π * z)
  证明: by
  have pi_ne : (π : Complex) != 0 := Complex.ofReal_ne_zero.mpr pi_ne_zero
  by_cases hs : sin (↑π * z) = 0
  · -- first deal with silly case z = integer
    rw [hs]; rw [div_zero]
    rw [← neg_eq_zero]; rw [← Complex.sin_neg]; rw [← mul_neg]; rw [Complex.sin_eq_zero_iff]; rw [mul_comm] at hs
  

Depends on / 依赖: Complex.Gamma_n, Complex.ofReal_ne_zero.mpr, Complex.sin_eq_zero_iff, Complex.sin_neg, Gamma_n, Int.cast_natCast, Int.ofNat_eq_natCast, cast_natCast, div_zero, eq_false, integer, mul_comm, mul_eq_mul_right_iff, mul_neg, neg_eq_iff_eq_neg, neg_eq_zero, ofNat_eq_natCast, ofReal_ne_zero, ofReal_ne_zero.mpr, or_false
-/
theorem Gamma_mul_Gamma_one_sub (z : Complex) : Gamma z * Gamma (1 - z) = π / sin (π * z) := by
  have pi_ne : (π : Complex) != 0 := Complex.ofReal_ne_zero.mpr pi_ne_zero
  by_cases hs : sin (↑π * z) = 0
  · -- first deal with silly case z = integer
    rw [hs]; rw [div_zero]
    rw [← neg_eq_zero]; rw [← Complex.sin_neg]; rw [← mul_neg]; rw [Complex.sin_eq_zero_iff]; rw [mul_comm] at hs
    obtain ⟨k, hk⟩ := hs
    rw [mul_eq_mul_right_iff]; rw [eq_false (ofReal_ne_zero.mpr pi_pos.ne')]; rw [or_false]; rw [neg_eq_iff_eq_neg] at hk
    rw [hk]
    cases k
    · rw [Int.ofNat_eq_natCast, Int.cast_natCast, Complex.Gamma_neg_nat_eq_zero, zero_mul]
    · rw [Int.cast_negSucc, neg_neg, Nat.cast_add, Nat.cast_one, add_comm, sub_add_cancel_left,
        Complex.Gamma_neg_nat_eq_zero, mul_zero]
  refine tendsto_nhds_unique ((GammaSeq_tendsto_Gamma z).mul (GammaSeq_tendsto_Gamma <| 1 - z)) ?_
  have : ↑π / sin (↑π * z) = 1 * (π / sin (π * z)) := by rw [one_mul]
  convert!
    Tendsto.congr'
      ((eventually_ne_atTop 0).mp (Eventually.of_forall fun n hn => (GammaSeq_mul z hn).symm))
      (Tendsto.mul _ _)
  · convert! tendsto_natCast_div_add_atTop (1 - z) using 1; ext1 n; rw [add_sub_assoc]
  · have : ↑π / sin (↑π * z) = 1 / (sin (π * z) / π) := by simp
    convert! tendsto_const_nhds.div _ (div_ne_zero hs pi_ne)
    rw [← tendsto_mul_iff_of_ne_zero tendsto_const_nhds pi_ne]; rw [div_mul_cancel₀ _ pi_ne]
    convert! tendsto_euler_sin_prod z using 1
    ext1 n; rw [mul_comm, ← mul_assoc]

/--
theorem `Gamma_ne_zero` / 定理 `Gamma_ne_zero`

English:
theorem Gamma_ne_zero
  given: {s : Complex} (hs : forall m : Nat, s != -m)
  statement: Gamma s != 0
  proof: by
  by_cases h_im : s.im = 0
  · have : s = ↑s.re := by
      conv_lhs => rw [← Complex.re_add_im s]
      rw [h_im]; rw [ofReal_zero]; rw [zero_mul]; rw [add_zero]
    rw [this]; rw [Gamma_ofReal]; rw [ofReal_ne_zero]
    refine Real.Gamma_ne_zero fun n => ?_
    specialize hs n
    contrapose hs


中文:
定理 Gamma_ne_zero
  条件: {s : 复形} (hs : 对任意 m : 自然数, s != -m)
  结论: Gamma s != 0
  证明: by
  by_cases h_im : s.im = 0
  · have : s = ↑s.re := by
      conv_lhs => rw [← Complex.re_add_im s]
      rw [h_im]; rw [ofReal_zero]; rw [zero_mul]; rw [add_zero]
    rw [this]; rw [Gamma_ofReal]; rw [ofReal_ne_zero]
    refine Real.Gamma_ne_zero fun n => ?_
    specialize hs n
    contrapose hs


Depends on / 依赖: Complex.re_add_im, Complex.sin_ne_zero_iff, Gamma_ne_zero, Gamma_ofReal, Real.Gamma_ne_zero, add_zero, apply_fun, contrapose, conv_lhs, h_im, im_ofReal_mul, mul_ne_zero, ofReal_im, ofReal_inj, ofReal_intCast, ofReal_mul, ofReal_natCast, ofReal_ne_zero, ofReal_neg, ofReal_zero
-/
theorem Gamma_ne_zero {s : Complex} (hs : forall m : Nat, s != -m) : Gamma s != 0 := by
  by_cases h_im : s.im = 0
  · have : s = ↑s.re := by
      conv_lhs => rw [← Complex.re_add_im s]
      rw [h_im]; rw [ofReal_zero]; rw [zero_mul]; rw [add_zero]
    rw [this]; rw [Gamma_ofReal]; rw [ofReal_ne_zero]
    refine Real.Gamma_ne_zero fun n => ?_
    specialize hs n
    contrapose hs
    rwa [this, ← ofReal_natCast, ← ofReal_neg, ofReal_inj]
  · have : sin (↑π * s) != 0 := by
      rw [Complex.sin_ne_zero_iff]
      intro k
      apply_fun im
      rw [im_ofReal_mul]; rw [← ofReal_intCast]; rw [← ofReal_mul]; rw [ofReal_im]
      exact mul_ne_zero Real.pi_pos.ne' h_im
    have A := div_ne_zero (ofReal_ne_zero.mpr Real.pi_pos.ne') this
    rw [← Complex.Gamma_mul_Gamma_one_sub s]; rw [mul_ne_zero_iff] at A
    exact A.1

@[grind =]
/--
theorem `Gamma_eq_zero_iff` / 定理 `Gamma_eq_zero_iff`

English:
theorem Gamma_eq_zero_iff
  given: (s : Complex)
  statement: Gamma s = 0 ↔ exists m : Nat, s = -m
  proof: by
  constructor
  · contrapose!; exact Gamma_ne_zero
  · rintro ⟨m, rfl⟩; exact Gamma_neg_nat_eq_zero m

中文:
定理 Gamma_eq_zero_iff
  条件: (s : 复形)
  结论: Gamma s = 0 ↔ 存在 m : 自然数, s = -m
  证明: by
  constructor
  · contrapose!; exact Gamma_ne_zero
  · rintro ⟨m, rfl⟩; exact Gamma_neg_nat_eq_zero m

Depends on / 依赖: Gamma_ne_zero, Gamma_neg_nat_eq_zero, contrapose
-/
theorem Gamma_eq_zero_iff (s : Complex) : Gamma s = 0 ↔ exists m : Nat, s = -m := by
  constructor
  · contrapose!; exact Gamma_ne_zero
  · rintro ⟨m, rfl⟩; exact Gamma_neg_nat_eq_zero m

/--
theorem `Gamma_ne_zero_of_re_pos` / 定理 `Gamma_ne_zero_of_re_pos`

English:
theorem Gamma_ne_zero_of_re_pos
  given: {s : Complex} (hs : 0 < re s)
  statement: Gamma s != 0
  proof: by
  refine Gamma_ne_zero fun m => ?_
  contrapose! hs
  simpa only [hs, neg_re, ← ofReal_natCast, ofReal_re, neg_nonpos] using Nat.cast_nonneg _

中文:
定理 Gamma_ne_zero_of_re_pos
  条件: {s : 复形} (hs : 0 < re s)
  结论: Gamma s != 0
  证明: by
  refine Gamma_ne_zero fun m => ?_
  contrapose! hs
  simpa only [hs, neg_re, ← ofReal_natCast, ofReal_re, neg_nonpos] using Nat.cast_nonneg _

Depends on / 依赖: Gamma_ne_zero, Nat.cast_nonneg, cast_nonneg, contrapose, neg_nonpos, neg_re, ofReal_natCast, ofReal_re
-/
theorem Gamma_ne_zero_of_re_pos {s : Complex} (hs : 0 < re s) : Gamma s != 0 := by
  refine Gamma_ne_zero fun m => ?_
  contrapose! hs
  simpa only [hs, neg_re, ← ofReal_natCast, ofReal_re, neg_nonpos] using Nat.cast_nonneg _

/--
theorem `Gamma_add_nat_div_Gamma_eq` / 定理 `Gamma_add_nat_div_Gamma_eq`

English:
theorem Gamma_add_nat_div_Gamma_eq
  given: {n : Nat} (z : Complex) (hz : forall k : Nat, z != -k)
  proof: by
  induction n generalizing z with
  | zero =>
    simp
    grind
  | succ n ih =>
    suffices h : Gamma (z + n + 1) = Gamma (z + n) * (z + n) by
      simp [ascPochhammer_succ_right, ← ih z hz, div_mul_eq_mul_div, h, ← add_assoc]
    grind

中文:
定理 Gamma_add_nat_div_Gamma_eq
  条件: {n : 自然数} (z : 复形) (hz : 对任意 k : 自然数, z != -k)
  证明: by
  induction n generalizing z with
  | zero =>
    simp
    grind
  | succ n ih =>
    suffices h : Gamma (z + n + 1) = Gamma (z + n) * (z + n) by
      simp [ascPochhammer_succ_right, ← ih z hz, div_mul_eq_mul_div, h, ← add_assoc]
    grind

Depends on / 依赖: add_assoc, ascPochhammer_succ_right, div_mul_eq_mul_div, generalizing
-/
theorem Gamma_add_nat_div_Gamma_eq {n : Nat} (z : Complex) (hz : forall k : Nat, z != -k) :
    Gamma (z + n) / Gamma z = (ascPochhammer Complex n).eval z := by
  induction n generalizing z with
  | zero =>
    simp
    grind
  | succ n ih =>
    suffices h : Gamma (z + n + 1) = Gamma (z + n) * (z + n) by
      simp [ascPochhammer_succ_right, ← ih z hz, div_mul_eq_mul_div, h, ← add_assoc]
    grind

end Complex

namespace Real

/--
Definition of `GammaSeq` / `GammaSeq` 的定义

English:
definition GammaSeq
  signature: (s : Real) (n : Nat)
  body: (n : Real) ^ s * n ! / ∏ j in Finset.range (n + 1), (s + j)

中文:
定义 GammaSeq
  签名: (s : 实数) (n : 自然数)
  定义体: (n : Real) ^ s * n ! / ∏ j in Finset.range (n + 1), (s + j)

Depends on / 依赖: Finset, Finset.range
-/
noncomputable def GammaSeq (s : Real) (n : Nat) :=
  (n : Real) ^ s * n ! / ∏ j in Finset.range (n + 1), (s + j)

/--
theorem `GammaSeq_tendsto_Gamma` / 定理 `GammaSeq_tendsto_Gamma`

English:
theorem GammaSeq_tendsto_Gamma
  given: (s : Real)
  statement: Tendsto (GammaSeq s) atTop (𝓝 <| Gamma s)
  proof: by
  suffices Tendsto ((↑) ∘ GammaSeq s : Nat -> Complex) atTop (𝓝 <| Complex.Gamma s) by
    exact (Complex.continuous_re.tendsto (Complex.Gamma ↑s)).comp this
  convert! Complex.GammaSeq_tendsto_Gamma s
  ext1 n
  dsimp only [GammaSeq, Function.comp_apply, Complex.GammaSeq]
  push_cast
  rw [Compl

中文:
定理 GammaSeq_tendsto_Gamma
  条件: (s : 实数)
  结论: 收敛 (GammaSeq s) atTop (𝓝 <| Gamma s)
  证明: by
  suffices Tendsto ((↑) ∘ GammaSeq s : Nat -> Complex) atTop (𝓝 <| Complex.Gamma s) by
    exact (Complex.continuous_re.tendsto (Complex.Gamma ↑s)).comp this
  convert! Complex.GammaSeq_tendsto_Gamma s
  ext1 n
  dsimp only [GammaSeq, Function.comp_apply, Complex.GammaSeq]
  push_cast
  rw [Compl

Depends on / 依赖: Complex.Gamma, Complex.GammaSeq, Complex.GammaSeq_tendsto_Gamma, Complex.continuous_re.tendsto, Complex.ofReal_cpow, Complex.ofReal_natCast, Function, Function.comp_apply, GammaSeq, GammaSeq_tendsto_Gamma, Tendsto, cast_nonneg, comp_apply, continuous_re, convert, n.cast_nonneg, ofReal_cpow, ofReal_natCast, tendsto
-/
theorem GammaSeq_tendsto_Gamma (s : Real) : Tendsto (GammaSeq s) atTop (𝓝 <| Gamma s) := by
  suffices Tendsto ((↑) ∘ GammaSeq s : Nat -> Complex) atTop (𝓝 <| Complex.Gamma s) by
    exact (Complex.continuous_re.tendsto (Complex.Gamma ↑s)).comp this
  convert! Complex.GammaSeq_tendsto_Gamma s
  ext1 n
  dsimp only [GammaSeq, Function.comp_apply, Complex.GammaSeq]
  push_cast
  rw [Complex.ofReal_cpow n.cast_nonneg]; rw [Complex.ofReal_natCast]

/--
theorem `Gamma_mul_Gamma_one_sub` / 定理 `Gamma_mul_Gamma_one_sub`

English:
theorem Gamma_mul_Gamma_one_sub
  given: (s : Real)
  statement: Gamma s * Gamma (1 - s) = π / sin (π * s)
  proof: by
  simp_rw [← Complex.ofReal_inj, Complex.ofReal_div, Complex.ofReal_sin, Complex.ofReal_mul, ←
    Complex.Gamma_ofReal, Complex.ofReal_sub, Complex.ofReal_one]
  exact Complex.Gamma_mul_Gamma_one_sub s

中文:
定理 Gamma_mul_Gamma_one_sub
  条件: (s : 实数)
  结论: Gamma s * Gamma (1 - s) = π / sin (π * s)
  证明: by
  simp_rw [← Complex.ofReal_inj, Complex.ofReal_div, Complex.ofReal_sin, Complex.ofReal_mul, ←
    Complex.Gamma_ofReal, Complex.ofReal_sub, Complex.ofReal_one]
  exact Complex.Gamma_mul_Gamma_one_sub s

Depends on / 依赖: Complex.Gamma_mul_Gamma_one_sub, Complex.Gamma_ofReal, Complex.ofReal_div, Complex.ofReal_inj, Complex.ofReal_mul, Complex.ofReal_one, Complex.ofReal_sin, Complex.ofReal_sub, Gamma_mul_Gamma_one_sub, Gamma_ofReal, ofReal_div, ofReal_inj, ofReal_mul, ofReal_one, ofReal_sin, ofReal_sub, simp_rw
-/
theorem Gamma_mul_Gamma_one_sub (s : Real) : Gamma s * Gamma (1 - s) = π / sin (π * s) := by
  simp_rw [← Complex.ofReal_inj, Complex.ofReal_div, Complex.ofReal_sin, Complex.ofReal_mul, ←
    Complex.Gamma_ofReal, Complex.ofReal_sub, Complex.ofReal_one]
  exact Complex.Gamma_mul_Gamma_one_sub s

end Real

end GammaReflection

section InvGamma

open scoped Real

namespace Complex

/-! ## The reciprocal Gamma function

We show that the reciprocal Gamma function `1 / Γ(s)` is entire. These lemmas show that (in this
case at least) mathlib's conventions for division by zero do actually give a mathematically useful
answer! (These results are useful in the theory of zeta and L-functions.) -/


/--
theorem `one_div_Gamma_eq_self_mul_one_div_Gamma_add_one` / 定理 `one_div_Gamma_eq_self_mul_one_div_Gamma_add_one`

English:
theorem one_div_Gamma_eq_self_mul_one_div_Gamma_add_one
  given: (s : Complex)
  proof: by
  rcases ne_or_eq s 0 with (h | rfl)
  · rw [Gamma_add_one s h, mul_inv, mul_inv_cancel_left₀ h]
  · rw [zero_add, Gamma_zero, inv_zero, zero_mul]

中文:
定理 one_div_Gamma_eq_self_mul_one_div_Gamma_add_one
  条件: (s : 复形)
  证明: by
  rcases ne_or_eq s 0 with (h | rfl)
  · rw [Gamma_add_one s h, mul_inv, mul_inv_cancel_left₀ h]
  · rw [zero_add, Gamma_zero, inv_zero, zero_mul]

Depends on / 依赖: Gamma_add_one, Gamma_zero, inv_zero, mul_inv, ne_or_eq, zero_add, zero_mul
-/
theorem one_div_Gamma_eq_self_mul_one_div_Gamma_add_one (s : Complex) :
    (Gamma s)⁻¹ = s * (Gamma (s + 1))⁻¹ := by
  rcases ne_or_eq s 0 with (h | rfl)
  · rw [Gamma_add_one s h, mul_inv, mul_inv_cancel_left₀ h]
  · rw [zero_add, Gamma_zero, inv_zero, zero_mul]

/--
theorem `differentiable_one_div_Gamma` / 定理 `differentiable_one_div_Gamma`

English:
theorem differentiable_one_div_Gamma
  statement: Differentiable Complex fun s : Complex => (Gamma s)⁻¹
  proof: fun s => by
  rcases exists_nat_gt (-s.re) with ⟨n, hs⟩
  induction n generalizing s with
  | zero =>
    rw [Nat.cast_zero]; rw [neg_lt_zero] at hs
    suffices forall m : Nat, s != -↑m from (differentiableAt_Gamma _ this).inv (Gamma_ne_zero this)
    rintro m rfl
    apply hs.not_ge
    simp
  | s

中文:
定理 differentiable_one_div_Gamma
  结论: 可微 复形 fun s : 复形 => (Gamma s)⁻¹
  证明: fun s => by
  rcases exists_nat_gt (-s.re) with ⟨n, hs⟩
  induction n generalizing s with
  | zero =>
    rw [Nat.cast_zero]; rw [neg_lt_zero] at hs
    suffices forall m : Nat, s != -↑m from (differentiableAt_Gamma _ this).inv (Gamma_ne_zero this)
    rintro m rfl
    apply hs.not_ge
    simp
  | s

Depends on / 依赖: Gamma_ne_zero, Nat.cast_succ, Nat.cast_zero, add_re, cast_succ, cast_zero, differentiableAt_Gamma, differentiableAt_id, differentiableAt_id.mul, exists_nat_gt, generalizing, hs.not_ge, ihn.comp, neg_add, neg_lt_zero, not_ge, one_div_Gamma_eq_self_mul_one_div_Gamma_add_one, one_re, s.re, specialize
-/
theorem differentiable_one_div_Gamma : Differentiable Complex fun s : Complex => (Gamma s)⁻¹ := fun s => by
  rcases exists_nat_gt (-s.re) with ⟨n, hs⟩
  induction n generalizing s with
  | zero =>
    rw [Nat.cast_zero]; rw [neg_lt_zero] at hs
    suffices forall m : Nat, s != -↑m from (differentiableAt_Gamma _ this).inv (Gamma_ne_zero this)
    rintro m rfl
    apply hs.not_ge
    simp
  | succ n ihn =>
    rw [funext one_div_Gamma_eq_self_mul_one_div_Gamma_add_one]
    specialize ihn (s + 1) (by rwa [add_re, one_re, neg_add', sub_lt_iff_lt_add, ← Nat.cast_succ])
    exact differentiableAt_id.mul (ihn.comp s (f := fun s => s + 1) <|
      differentiableAt_id.add_const (1 : Complex))

/--
lemma `betaIntegral_eq_Gamma_mul_div` / 引理 `betaIntegral_eq_Gamma_mul_div`

English:
lemma betaIntegral_eq_Gamma_mul_div
  given: (u v : Complex) (hu : 0 < u.re) (hv : 0 < v.re)
  proof: by
  rw [Gamma_mul_Gamma_eq_betaIntegral hu hv]; rw [mul_div_cancel_left₀ _ (Gamma_ne_zero_of_re_pos (add_pos hu hv))]

中文:
引理 beta整数egral_eq_Gamma_mul_div
  条件: (u v : 复形) (hu : 0 < u.re) (hv : 0 < v.re)
  证明: by
  rw [Gamma_mul_Gamma_eq_betaIntegral hu hv]; rw [mul_div_cancel_left₀ _ (Gamma_ne_zero_of_re_pos (add_pos hu hv))]

Depends on / 依赖: Gamma_mul_Gamma_eq_betaIntegral, Gamma_ne_zero_of_re_pos, add_pos
-/
lemma betaIntegral_eq_Gamma_mul_div (u v : Complex) (hu : 0 < u.re) (hv : 0 < v.re) :
    betaIntegral u v = Gamma u * Gamma v / Gamma (u + v) := by
  rw [Gamma_mul_Gamma_eq_betaIntegral hu hv]; rw [mul_div_cancel_left₀ _ (Gamma_ne_zero_of_re_pos (add_pos hu hv))]

end Complex

end InvGamma

section Doubling

/-!
## The doubling formula for Gamma

We prove the doubling formula for arbitrary real or complex arguments, by analytic continuation from
the positive real case. (Knowing that `Γ⁻¹` is analytic everywhere makes this much simpler, since we
do not have to do any special-case handling for the poles of `Γ`.)
-/


namespace Complex

/--
theorem `Gamma_mul_Gamma_add_half` / 定理 `Gamma_mul_Gamma_add_half`

English:
theorem Gamma_mul_Gamma_add_half
  given: (s : Complex)
  proof: by
  suffices (fun z => (Gamma z)⁻¹ * (Gamma (z + 1 / 2))⁻¹) = fun z =>
      (Gamma (2 * z))⁻¹ * (2 : Complex) ^ (2 * z - 1) / ↑(√π) by
    convert! congr_arg Inv.inv (congr_fun this s) using 1
    · rw [mul_inv, inv_inv, inv_inv]
    · rw [div_eq_mul_inv, mul_inv, mul_inv, inv_inv, inv_inv, ← cpow

中文:
定理 Gamma_mul_Gamma_add_half
  条件: (s : 复形)
  证明: by
  suffices (fun z => (Gamma z)⁻¹ * (Gamma (z + 1 / 2))⁻¹) = fun z =>
      (Gamma (2 * z))⁻¹ * (2 : Complex) ^ (2 * z - 1) / ↑(√π) by
    convert! congr_arg Inv.inv (congr_fun this s) using 1
    · rw [mul_inv, inv_inv, inv_inv]
    · rw [div_eq_mul_inv, mul_inv, mul_inv, inv_inv, inv_inv, ← cpow

Depends on / 依赖: AnalyticOnNhd, DifferentiableOn, DifferentiableOn.analyticOnNhd, Inv.inv, analyticOnNhd, congr_arg, congr_fun, convert, cpow_neg, differe, differentiable_one_div_Gamma, differentiable_one_div_Gamma.mul, div_eq_mul_inv, inv_inv, isOpen_univ, mul_inv, neg_sub
-/
theorem Gamma_mul_Gamma_add_half (s : Complex) :
    Gamma s * Gamma (s + 1 / 2) = Gamma (2 * s) * (2 : Complex) ^ (1 - 2 * s) * ↑(√π) := by
  suffices (fun z => (Gamma z)⁻¹ * (Gamma (z + 1 / 2))⁻¹) = fun z =>
      (Gamma (2 * z))⁻¹ * (2 : Complex) ^ (2 * z - 1) / ↑(√π) by
    convert! congr_arg Inv.inv (congr_fun this s) using 1
    · rw [mul_inv, inv_inv, inv_inv]
    · rw [div_eq_mul_inv, mul_inv, mul_inv, inv_inv, inv_inv, ← cpow_neg, neg_sub]
  have h1 : AnalyticOnNhd Complex (fun z : Complex => (Gamma z)⁻¹ * (Gamma (z + 1 / 2))⁻¹) univ := by
    refine DifferentiableOn.analyticOnNhd ?_ isOpen_univ
    refine (differentiable_one_div_Gamma.mul ?_).differentiableOn
    exact differentiable_one_div_Gamma.comp (differentiable_id.add (differentiable_const _))
  have h2 : AnalyticOnNhd Complex
      (fun z => (Gamma (2 * z))⁻¹ * (2 : Complex) ^ (2 * z - 1) / ↑(√π)) univ := by
    refine DifferentiableOn.analyticOnNhd ?_ isOpen_univ
    refine (Differentiable.mul ?_ (differentiable_const _)).differentiableOn
    apply Differentiable.mul
    · exact differentiable_one_div_Gamma.comp (differentiable_id.const_mul _)
    · refine fun t => DifferentiableAt.const_cpow ?_ (Or.inl two_ne_zero)
      exact DifferentiableAt.sub_const (differentiableAt_id.const_mul _) _
  have h3 : Tendsto ((↑) : Real -> Complex) (𝓝[!=] 1) (𝓝[!=] 1) := by
    rw [tendsto_nhdsWithin_iff]; constructor
    · exact tendsto_nhdsWithin_of_tendsto_nhds continuous_ofReal.continuousAt
    · exact eventually_nhdsWithin_iff.mpr (Eventually.of_forall fun t ht => ofReal_ne_one.mpr ht)
  refine AnalyticOnNhd.eq_of_frequently_eq h1 h2 (h3.frequently ?_)
  refine ((Eventually.filter_mono nhdsWithin_le_nhds) ?_).frequently
  refine (eventually_gt_nhds zero_lt_one).mp (Eventually.of_forall fun t ht => ?_)
  rw [← mul_inv]; rw [Gamma_ofReal]; rw [(by simp : (t : Complex) + 1 / 2 = ↑(t + 1 / 2))]; rw [Gamma_ofReal]; rw [←
    ofReal_mul]; rw [Gamma_mul_Gamma_add_half_of_pos ht]; rw [ofReal_mul]; rw [ofReal_mul]; rw [← Gamma_ofReal]; rw [mul_inv]; rw [mul_inv]; rw [(by simp : 2 * (t : Complex) = ↑(2 * t))]; rw [Gamma_ofReal]; rw [ofReal_cpow zero_le_two]; rw [show (2 : Real) = (2 : Complex) by norm_cast]; rw [← cpow_neg]; rw [ofReal_sub]; rw [ofReal_one]; rw [neg_sub]; rw [← div_eq_mul_inv]

end Complex

namespace Real

open Complex

/--
theorem `Gamma_mul_Gamma_add_half` / 定理 `Gamma_mul_Gamma_add_half`

English:
theorem Gamma_mul_Gamma_add_half
  given: (s : Real)
  proof: by
  rw [← ofReal_inj]
  simpa only [← Gamma_ofReal, ofReal_cpow zero_le_two, ofReal_mul, ofReal_add, ofReal_div,
    ofReal_sub] using! Complex.Gamma_mul_Gamma_add_half ↑s

中文:
定理 Gamma_mul_Gamma_add_half
  条件: (s : 实数)
  证明: by
  rw [← ofReal_inj]
  simpa only [← Gamma_ofReal, ofReal_cpow zero_le_two, ofReal_mul, ofReal_add, ofReal_div,
    ofReal_sub] using! Complex.Gamma_mul_Gamma_add_half ↑s

Depends on / 依赖: Complex.Gamma_mul_Gamma_add_half, Gamma_mul_Gamma_add_half, Gamma_ofReal, ofReal_add, ofReal_cpow, ofReal_div, ofReal_inj, ofReal_mul, ofReal_sub, zero_le_two
-/
theorem Gamma_mul_Gamma_add_half (s : Real) :
    Gamma s * Gamma (s + 1 / 2) = Gamma (2 * s) * (2 : Real) ^ (1 - 2 * s) * √π := by
  rw [← ofReal_inj]
  simpa only [← Gamma_ofReal, ofReal_cpow zero_le_two, ofReal_mul, ofReal_add, ofReal_div,
    ofReal_sub] using! Complex.Gamma_mul_Gamma_add_half ↑s

end Real

end Doubling
