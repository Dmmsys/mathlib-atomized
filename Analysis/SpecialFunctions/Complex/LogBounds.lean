/-
Copyright (c) 2023 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Analysis.Complex.Convex
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.Calculus.Deriv.Shift
public import Mathlib.Analysis.SpecificLimits.RCLike

import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

/-!
# Estimates for the complex logarithm

We show that `log (1+z)` differs from its Taylor polynomial up to degree `n` by at most
`‖z‖^(n+1)/((n+1)*(1-‖z‖))` when `‖z‖ < 1`; see `Complex.norm_log_sub_logTaylor_le`.

To this end, we derive the representation of `log (1+z)` as the integral of `1/(1+tz)`
over the unit interval (`Complex.log_eq_integral`) and introduce notation
`Complex.logTaylor n` for the Taylor polynomial up to degree `n-1`.

## TODO

Refactor using general Taylor series theory, once this exists in Mathlib.
-/

@[expose] public section

namespace Complex


/--
lemma `continuousOn_one_add_mul_inv` / 引理 `continuousOn_one_add_mul_inv`

English:
lemma continuousOn_one_add_mul_inv
  given: {z : Complex} (hz : 1 + z in slitPlane)
  proof: ContinuousOn.inv₀ (by fun_prop)
    (fun _ ht => slitPlane_ne_zero <| StarConvex.add_smul_mem starConvex_one_slitPlane hz ht.1 ht.2)

中文:
引理 continuousOn_one_add_mul_inv
  条件: {z : 复形} (hz : 1 + z in slitPlane)
  证明: ContinuousOn.inv₀ (by fun_prop)
    (fun _ ht => slitPlane_ne_zero <| StarConvex.add_smul_mem starConvex_one_slitPlane hz ht.1 ht.2)

Depends on / 依赖: ContinuousOn, ContinuousOn.inv, StarConvex, StarConvex.add_smul_mem, add_smul_mem, fun_prop, slitPlane_ne_zero, starConvex_one_slitPlane
-/
lemma continuousOn_one_add_mul_inv {z : Complex} (hz : 1 + z in slitPlane) :
    ContinuousOn (fun t : Real => (1 + t • z)⁻¹) (Set.Icc 0 1) :=
  ContinuousOn.inv₀ (by fun_prop)
    (fun _ ht => slitPlane_ne_zero <| StarConvex.add_smul_mem starConvex_one_slitPlane hz ht.1 ht.2)

open intervalIntegral in
/--
lemma `log_eq_integral` / 引理 `log_eq_integral`

English:
lemma log_eq_integral
  given: {z : Complex} (hz : 1 + z in slitPlane)
  proof: by
  convert!
    (integral_unitInterval_deriv_eq_sub (continuousOn_one_add_mul_inv hz)
        (fun _ ht =>
hasDerivAt_log
            StarConvex.add_smul_mem starConvex_one_slitPlane hz ht.1 ht.2)).symm using 1
  simp only [log_one, sub_zero]

中文:
引理 log_eq_integral
  条件: {z : 复形} (hz : 1 + z in slitPlane)
  证明: by
  convert!
    (integral_unitInterval_deriv_eq_sub (continuousOn_one_add_mul_inv hz)
        (fun _ ht =>
hasDerivAt_log
            StarConvex.add_smul_mem starConvex_one_slitPlane hz ht.1 ht.2)).symm using 1
  simp only [log_one, sub_zero]

Depends on / 依赖: StarConvex, StarConvex.add_smul_mem, add_smul_mem, continuousOn_one_add_mul_inv, convert, hasDerivAt_log, integral_unitInterval_deriv_eq_sub, log_one, starConvex_one_slitPlane, sub_zero
-/
lemma log_eq_integral {z : Complex} (hz : 1 + z in slitPlane) :
    log (1 + z) = z * ∫ (t : Real) in (0 : Real)..1, (1 + t • z)⁻¹ := by
  convert!
    (integral_unitInterval_deriv_eq_sub (continuousOn_one_add_mul_inv hz)
        (fun _ ht =>
hasDerivAt_log
            StarConvex.add_smul_mem starConvex_one_slitPlane hz ht.1 ht.2)).symm using 1
  simp only [log_one, sub_zero]

/--
lemma `log_inv_eq_integral` / 引理 `log_inv_eq_integral`

English:
lemma log_inv_eq_integral
  given: {z : Complex} (hz : 1 - z in slitPlane)
  proof: by
  rw [sub_eq_add_neg 1 z] at hz ⊢
  rw [log_inv _ <| slitPlane_arg_ne_pi hz]; rw [neg_eq_iff_eq_neg]; rw [← neg_mul]
  convert! log_eq_integral hz using 5
  rw [sub_eq_add_neg]; rw [smul_neg]

中文:
引理 log_inv_eq_integral
  条件: {z : 复形} (hz : 1 - z in slitPlane)
  证明: by
  rw [sub_eq_add_neg 1 z] at hz ⊢
  rw [log_inv _ <| slitPlane_arg_ne_pi hz]; rw [neg_eq_iff_eq_neg]; rw [← neg_mul]
  convert! log_eq_integral hz using 5
  rw [sub_eq_add_neg]; rw [smul_neg]

Depends on / 依赖: convert, log_eq_integral, log_inv, neg_eq_iff_eq_neg, neg_mul, slitPlane_arg_ne_pi, smul_neg, sub_eq_add_neg
-/
lemma log_inv_eq_integral {z : Complex} (hz : 1 - z in slitPlane) :
    log (1 - z)⁻¹ = z * ∫ (t : Real) in (0 : Real)..1, (1 - t • z)⁻¹ := by
  rw [sub_eq_add_neg 1 z] at hz ⊢
  rw [log_inv _ <| slitPlane_arg_ne_pi hz]; rw [neg_eq_iff_eq_neg]; rw [← neg_mul]
  convert! log_eq_integral hz using 5
  rw [sub_eq_add_neg]; rw [smul_neg]

/-!
### The Taylor polynomials of the logarithm
-/

/-- The `n`th Taylor polynomial of `log` at `1`, as a function `ℂ → ℂ` -/
noncomputable
/--
Definition of `logTaylor` / `logTaylor` 的定义

English:
definition logTaylor
  signature: (n : Nat)
  body: fun z => ∑ j in Finset.range n, (-1) ^ (j + 1) * z ^ j / j

中文:
定义 logTaylor
  签名: (n : 自然数)
  定义体: fun z => ∑ j in Finset.range n, (-1) ^ (j + 1) * z ^ j / j

Depends on / 依赖: Finset, Finset.range
-/
def logTaylor (n : Nat) : Complex -> Complex := fun z => ∑ j in Finset.range n, (-1) ^ (j + 1) * z ^ j / j

/--
lemma `logTaylor_zero` / 引理 `logTaylor_zero`

English:
lemma logTaylor_zero
  statement: logTaylor 0 = fun _ => 0
  proof: by
  funext
  simp only [logTaylor, Finset.range_zero,
    Finset.sum_empty]

中文:
引理 logTaylor_zero
  结论: logTaylor 0 = fun _ => 0
  证明: by
  funext
  simp only [logTaylor, Finset.range_zero,
    Finset.sum_empty]

Depends on / 依赖: Finset, Finset.range_zero, Finset.sum_empty, logTaylor, range_zero, sum_empty
-/
lemma logTaylor_zero : logTaylor 0 = fun _ => 0 := by
  funext
  simp only [logTaylor, Finset.range_zero,
    Finset.sum_empty]

/--
lemma `logTaylor_succ` / 引理 `logTaylor_succ`

English:
lemma logTaylor_succ
  given: (n : Nat)
  proof: by
  funext
  simpa only [logTaylor] using! Finset.sum_range_succ ..

中文:
引理 logTaylor_succ
  条件: (n : 自然数)
  证明: by
  funext
  simpa only [logTaylor] using! Finset.sum_range_succ ..

Depends on / 依赖: Finset, Finset.sum_range_succ, logTaylor, sum_range_succ
-/
lemma logTaylor_succ (n : Nat) :
    logTaylor (n + 1) = logTaylor n + (fun z : Complex => (-1) ^ (n + 1) * z ^ n / n) := by
  funext
  simpa only [logTaylor] using! Finset.sum_range_succ ..

/--
lemma `logTaylor_at_zero` / 引理 `logTaylor_at_zero`

English:
lemma logTaylor_at_zero
  given: (n : Nat)
  statement: logTaylor n 0 = 0
  proof: by
  induction n with
  | zero => simp [logTaylor_zero]
  | succ n ih => simpa [logTaylor_succ, ih] using ne_or_eq n 0

中文:
引理 logTaylor_at_zero
  条件: (n : 自然数)
  结论: logTaylor n 0 = 0
  证明: by
  induction n with
  | zero => simp [logTaylor_zero]
  | succ n ih => simpa [logTaylor_succ, ih] using ne_or_eq n 0

Depends on / 依赖: logTaylor_succ, logTaylor_zero, ne_or_eq
-/
lemma logTaylor_at_zero (n : Nat) : logTaylor n 0 = 0 := by
  induction n with
  | zero => simp [logTaylor_zero]
  | succ n ih => simpa [logTaylor_succ, ih] using ne_or_eq n 0

/--
lemma `hasDerivAt_logTaylor` / 引理 `hasDerivAt_logTaylor`

English:
lemma hasDerivAt_logTaylor
  given: (n : Nat) (z : Complex)
  proof: by
  induction n with
  | zero => simp [logTaylor_succ, logTaylor_zero, Pi.add_def, hasDerivAt_const]
  | succ n ih =>
    rw [logTaylor_succ]
    simp only [Nat.cast_add, Nat.cast_one,
      Finset.sum_range_succ]
    refine HasDerivAt.add ih ?_
    simp only [mul_div_assoc]
    have : HasDerivAt (

中文:
引理 hasDerivAt_logTaylor
  条件: (n : 自然数) (z : 复形)
  证明: by
  induction n with
  | zero => simp [logTaylor_succ, logTaylor_zero, Pi.add_def, hasDerivAt_const]
  | succ n ih =>
    rw [logTaylor_succ]
    simp only [Nat.cast_add, Nat.cast_one,
      Finset.sum_range_succ]
    refine HasDerivAt.add ih ?_
    simp only [mul_div_assoc]
    have : HasDerivAt (

Depends on / 依赖: Finset, Finset.sum_range_succ, HasDerivAt, HasDerivAt.add, HasDerivAt.const_mul, HasDerivAt.mul_const, Nat.cast_add, Nat.cast_one, Pi.add_def, add_def, cast_add, cast_one, const_mul, convert, div_eq_mul_inv, hasDerivAt_const, hasDerivAt_pow, logTaylor_succ, logTaylor_zero, mul_const
-/
lemma hasDerivAt_logTaylor (n : Nat) (z : Complex) :
    HasDerivAt (logTaylor (n + 1)) (∑ j in Finset.range n, (-1) ^ j * z ^ j) z := by
  induction n with
  | zero => simp [logTaylor_succ, logTaylor_zero, Pi.add_def, hasDerivAt_const]
  | succ n ih =>
    rw [logTaylor_succ]
    simp only [Nat.cast_add, Nat.cast_one,
      Finset.sum_range_succ]
    refine HasDerivAt.add ih ?_
    simp only [mul_div_assoc]
    have : HasDerivAt (fun x : Complex => (x ^ (n + 1) / (n + 1))) (z ^ n) z := by
      simp_rw [div_eq_mul_inv]
      convert! HasDerivAt.mul_const (hasDerivAt_pow (n + 1) z) (((n : Complex) + 1)⁻¹) using 1
      simp [field]
    convert! HasDerivAt.const_mul _ this using 2
    ring


/--
lemma `hasDerivAt_log_sub_logTaylor` / 引理 `hasDerivAt_log_sub_logTaylor`

English:
lemma hasDerivAt_log_sub_logTaylor
  given: (n : Nat) {z : Complex} (hz : 1 + z in slitPlane)
  proof: by
  convert! ((hasDerivAt_log hz).comp_const_add 1 z).sub (hasDerivAt_logTaylor n z) using 1
  have hz' : -z != 1 := by
    intro H
    rw [neg_eq_iff_eq_neg] at H
    simp only [H, add_neg_cancel] at hz
    exact slitPlane_ne_zero hz rfl
  simp_rw [← mul_pow, neg_one_mul, geom_sum_eq hz', ← neg_ad

中文:
引理 hasDerivAt_log_sub_logTaylor
  条件: (n : 自然数) {z : 复形} (hz : 1 + z in slitPlane)
  证明: by
  convert! ((hasDerivAt_log hz).comp_const_add 1 z).sub (hasDerivAt_logTaylor n z) using 1
  have hz' : -z != 1 := by
    intro H
    rw [neg_eq_iff_eq_neg] at H
    simp only [H, add_neg_cancel] at hz
    exact slitPlane_ne_zero hz rfl
  simp_rw [← mul_pow, neg_one_mul, geom_sum_eq hz', ← neg_ad

Depends on / 依赖: add_comm, add_neg_cancel, comp_const_add, convert, div_neg, geom_sum_eq, hasDerivAt_log, hasDerivAt_logTaylor, mul_pow, neg_add, neg_eq_iff_eq_neg, neg_one_mul, simp_rw, slitPlane_ne_zero
-/
lemma hasDerivAt_log_sub_logTaylor (n : Nat) {z : Complex} (hz : 1 + z in slitPlane) :
    HasDerivAt (fun z : Complex => log (1 + z) - logTaylor (n + 1) z) ((-z) ^ n * (1 + z)⁻¹) z := by
  convert! ((hasDerivAt_log hz).comp_const_add 1 z).sub (hasDerivAt_logTaylor n z) using 1
  have hz' : -z != 1 := by
    intro H
    rw [neg_eq_iff_eq_neg] at H
    simp only [H, add_neg_cancel] at hz
    exact slitPlane_ne_zero hz rfl
  simp_rw [← mul_pow, neg_one_mul, geom_sum_eq hz', ← neg_add', div_neg, add_comm z]
  simp [field]

/--
lemma `norm_one_add_mul_inv_le` / 引理 `norm_one_add_mul_inv_le`

English:
lemma norm_one_add_mul_inv_le
  given: {t : Real} (ht : t in Set.Icc 0 1) {z : Complex} (hz : ‖z‖ < 1)
  proof: by
  rw [Set.mem_Icc] at ht
  rw [norm_inv]
  refine inv_anti₀ (by linarith) ?_
  calc 1 - ‖z‖
    _ <= 1 - t * ‖z‖ := by
      nlinarith [norm_nonneg z]
    _ = 1 - ‖t * z‖ := by
      rw [norm_mul]; rw [Complex.norm_of_nonneg ht.1]
    _ <= ‖1 + t * z‖ := by
      rw [← norm_neg (t * z)]; rw [← su

中文:
引理 norm_one_add_mul_inv_le
  条件: {t : 实数} (ht : t in 集合.闭区间 0 1) {z : 复形} (hz : ‖z‖ < 1)
  证明: by
  rw [Set.mem_Icc] at ht
  rw [norm_inv]
  refine inv_anti₀ (by linarith) ?_
  calc 1 - ‖z‖
    _ <= 1 - t * ‖z‖ := by
      nlinarith [norm_nonneg z]
    _ = 1 - ‖t * z‖ := by
      rw [norm_mul]; rw [Complex.norm_of_nonneg ht.1]
    _ <= ‖1 + t * z‖ := by
      rw [← norm_neg (t * z)]; rw [← su

Depends on / 依赖: Complex.norm_of_nonneg, Set.mem_Icc, convert, mem_Icc, norm_inv, norm_mul, norm_neg, norm_nonneg, norm_of_nonneg, norm_one, norm_one.symm, norm_sub_norm_le, sub_neg_eq_add
-/
lemma norm_one_add_mul_inv_le {t : Real} (ht : t in Set.Icc 0 1) {z : Complex} (hz : ‖z‖ < 1) :
    ‖(1 + t * z)⁻¹‖ <= (1 - ‖z‖)⁻¹ := by
  rw [Set.mem_Icc] at ht
  rw [norm_inv]
  refine inv_anti₀ (by linarith) ?_
  calc 1 - ‖z‖
    _ <= 1 - t * ‖z‖ := by
      nlinarith [norm_nonneg z]
    _ = 1 - ‖t * z‖ := by
      rw [norm_mul]; rw [Complex.norm_of_nonneg ht.1]
    _ <= ‖1 + t * z‖ := by
      rw [← norm_neg (t * z)]; rw [← sub_neg_eq_add]
      convert! norm_sub_norm_le 1 (-(t * z))
      exact norm_one.symm

/--
lemma `integrable_pow_mul_norm_one_add_mul_inv` / 引理 `integrable_pow_mul_norm_one_add_mul_inv`

English:
lemma integrable_pow_mul_norm_one_add_mul_inv
  given: (n : Nat) {z : Complex} (hz : ‖z‖ < 1)
  proof: by
have := continuousOn_one_add_mul_inv mem_slitPlane_of_norm_lt_one hz
  rw [← Set.uIcc_of_le zero_le_one] at this
  exact ContinuousOn.intervalIntegrable (by fun_prop)

中文:
引理 integrable_pow_mul_norm_one_add_mul_inv
  条件: (n : 自然数) {z : 复形} (hz : ‖z‖ < 1)
  证明: by
have := continuousOn_one_add_mul_inv mem_slitPlane_of_norm_lt_one hz
  rw [← Set.uIcc_of_le zero_le_one] at this
  exact ContinuousOn.intervalIntegrable (by fun_prop)

Depends on / 依赖: ContinuousOn, ContinuousOn.intervalIntegrable, Set.uIcc_of_le, continuousOn_one_add_mul_inv, fun_prop, intervalIntegrable, mem_slitPlane_of_norm_lt_one, uIcc_of_le, zero_le_one
-/
lemma integrable_pow_mul_norm_one_add_mul_inv (n : Nat) {z : Complex} (hz : ‖z‖ < 1) :
    IntervalIntegrable (fun t : Real => t ^ n * ‖(1 + t * z)⁻¹‖) MeasureTheory.volume 0 1 := by
have := continuousOn_one_add_mul_inv mem_slitPlane_of_norm_lt_one hz
  rw [← Set.uIcc_of_le zero_le_one] at this
  exact ContinuousOn.intervalIntegrable (by fun_prop)

open intervalIntegral in
/--
lemma `norm_log_sub_logTaylor_le` / 引理 `norm_log_sub_logTaylor_le`

English:
lemma norm_log_sub_logTaylor_le
  given: (n : Nat) {z : Complex} (hz : ‖z‖ < 1)
  proof: by
  have help : IntervalIntegrable (fun t : Real => t ^ n * (1 - ‖z‖)⁻¹) MeasureTheory.volume 0 1 :=
    IntervalIntegrable.mul_const (Continuous.intervalIntegrable (by fun_prop) 0 1) (1 - ‖z‖)⁻¹
  let f (z : Complex) : Complex := log (1 + z) - logTaylor (n + 1) z
  let f' (z : Complex) : Complex :

中文:
引理 norm_log_sub_logTaylor_le
  条件: (n : 自然数) {z : 复形} (hz : ‖z‖ < 1)
  证明: by
  have help : IntervalIntegrable (fun t : Real => t ^ n * (1 - ‖z‖)⁻¹) MeasureTheory.volume 0 1 :=
    IntervalIntegrable.mul_const (Continuous.intervalIntegrable (by fun_prop) 0 1) (1 - ‖z‖)⁻¹
  let f (z : Complex) : Complex := log (1 + z) - logTaylor (n + 1) z
  let f' (z : Complex) : Complex :

Depends on / 依赖: Continuous, Continuous.intervalIntegrable, HasDerivAt, IntervalIntegrable, IntervalIntegrable.mul_const, MeasureTheory, MeasureTheory.volume, Set.Icc, StarConvex, StarConvex.add_smul_mem, add_smul_mem, fun_prop, hasDerivAt_log_sub_logTaylor, hderiv, intervalIntegrable, logTaylor, mul_const, volume, zero_add
-/
lemma norm_log_sub_logTaylor_le (n : Nat) {z : Complex} (hz : ‖z‖ < 1) :
    ‖log (1 + z) - logTaylor (n + 1) z‖ <= ‖z‖ ^ (n + 1) * (1 - ‖z‖)⁻¹ / (n + 1) := by
  have help : IntervalIntegrable (fun t : Real => t ^ n * (1 - ‖z‖)⁻¹) MeasureTheory.volume 0 1 :=
    IntervalIntegrable.mul_const (Continuous.intervalIntegrable (by fun_prop) 0 1) (1 - ‖z‖)⁻¹
  let f (z : Complex) : Complex := log (1 + z) - logTaylor (n + 1) z
  let f' (z : Complex) : Complex := (-z) ^ n * (1 + z)⁻¹
  have hderiv : forall t in Set.Icc (0 : Real) 1, HasDerivAt f (f' (0 + t * z)) (0 + t * z) := by
    intro t ht
    rw [zero_add]
exact hasDerivAt_log_sub_logTaylor n
      StarConvex.add_smul_mem starConvex_one_slitPlane (mem_slitPlane_of_norm_lt_one hz) ht.1 ht.2
  have hcont : ContinuousOn (fun t : Real => f' (0 + t * z)) (Set.Icc 0 1) := by
    simp only [zero_add]
exact (Continuous.continuousOn (by fun_prop)).mul
continuousOn_one_add_mul_inv mem_slitPlane_of_norm_lt_one hz
  have H : f z = z * ∫ t in (0 : Real)..1, (-(t * z)) ^ n * (1 + t * z)⁻¹ := by
    convert! (integral_unitInterval_deriv_eq_sub hcont hderiv).symm using 1
    · simp only [f, zero_add, add_zero, log_one, logTaylor_at_zero, sub_self, sub_zero]
    · simp only [f', real_smul, zero_add,
        smul_eq_mul]
  unfold f at H
  simp only [H, norm_mul]
  simp_rw [neg_pow (_ * z) n, mul_assoc, intervalIntegral.integral_const_mul, mul_pow,
    mul_comm _ (z ^ n), mul_assoc, intervalIntegral.integral_const_mul, norm_mul, norm_pow,
    norm_neg, norm_one, one_pow, one_mul, ← mul_assoc, ← pow_succ', mul_div_assoc]
  gcongr _ * ?_
  calc ‖∫ t in (0 : Real)..1, (t : Complex) ^ n * (1 + t * z)⁻¹‖
    _ <= ∫ t in (0 : Real)..1, t ^ n * (1 - ‖z‖)⁻¹ := by
      refine intervalIntegral.norm_integral_le_of_norm_le zero_le_one ?_ help
      filter_upwards with t ⟨ht₀, ht₁⟩
      rw [norm_mul]; rw [norm_pow]; rw [Complex.norm_of_nonneg ht₀.le]
      gcongr
      exact norm_one_add_mul_inv_le ⟨ht₀.le, ht₁⟩ hz
    _ = (1 - ‖z‖)⁻¹ / (n + 1) := by
      rw [intervalIntegral.integral_mul_const]; rw [mul_comm]; rw [integral_pow]
      simp [field]

/--
lemma `norm_log_one_add_sub_self_le` / 引理 `norm_log_one_add_sub_self_le`

English:
lemma norm_log_one_add_sub_self_le
  given: {z : Complex} (hz : ‖z‖ < 1)
  proof: by
  convert! norm_log_sub_logTaylor_le 1 hz using 2
  · simp [logTaylor_succ, logTaylor_zero, sub_eq_add_neg]
  · norm_num

中文:
引理 norm_log_one_add_sub_self_le
  条件: {z : 复形} (hz : ‖z‖ < 1)
  证明: by
  convert! norm_log_sub_logTaylor_le 1 hz using 2
  · simp [logTaylor_succ, logTaylor_zero, sub_eq_add_neg]
  · norm_num

Depends on / 依赖: convert, logTaylor_succ, logTaylor_zero, norm_log_sub_logTaylor_le, sub_eq_add_neg
-/
lemma norm_log_one_add_sub_self_le {z : Complex} (hz : ‖z‖ < 1) :
    ‖log (1 + z) - z‖ <= ‖z‖ ^ 2 * (1 - ‖z‖)⁻¹ / 2 := by
  convert! norm_log_sub_logTaylor_le 1 hz using 2
  · simp [logTaylor_succ, logTaylor_zero, sub_eq_add_neg]
  · norm_num

set_option linter.style.whitespace false in -- manual alignment is not recognised
open scoped Topology in
/--
lemma `log_sub_logTaylor_isBigO` / 引理 `log_sub_logTaylor_isBigO`

English:
lemma log_sub_logTaylor_isBigO
  given: (n : Nat)
  proof: by
  rw [Asymptotics.isBigO_iff]
  use 2 / (n + 1)
  filter_upwards [
    eventually_norm_sub_lt 0 one_pos,
    eventually_norm_sub_lt 0 (show 0 < 1 / 2 by simp)] with z hz1 hz12
  rw [sub_zero] at hz1 hz12
  have : (1 - ‖z‖)⁻¹ <= 2 := by rw [inv_le_comm₀ (sub_pos_of_lt hz1) two_pos]; linarith
  app

中文:
引理 log_sub_logTaylor_isBigO
  条件: (n : 自然数)
  证明: by
  rw [Asymptotics.isBigO_iff]
  use 2 / (n + 1)
  filter_upwards [
    eventually_norm_sub_lt 0 one_pos,
    eventually_norm_sub_lt 0 (show 0 < 1 / 2 by simp)] with z hz1 hz12
  rw [sub_zero] at hz1 hz12
  have : (1 - ‖z‖)⁻¹ <= 2 := by rw [inv_le_comm₀ (sub_pos_of_lt hz1) two_pos]; linarith
  app

Depends on / 依赖: Asymptotics, Asymptotics.isBigO_iff, eventually_norm_sub_lt, filter_upwards, isBigO_iff, mul_comm, mul_div_assoc, norm_log_sub_logTaylor_le, norm_pow, one_pos, sub_pos_of_lt, sub_zero, two_pos
-/
lemma log_sub_logTaylor_isBigO (n : Nat) :
    (fun z => log (1 + z) - logTaylor (n + 1) z) =O[𝓝 0] fun z => z ^ (n + 1) := by
  rw [Asymptotics.isBigO_iff]
  use 2 / (n + 1)
  filter_upwards [
    eventually_norm_sub_lt 0 one_pos,
    eventually_norm_sub_lt 0 (show 0 < 1 / 2 by simp)] with z hz1 hz12
  rw [sub_zero] at hz1 hz12
  have : (1 - ‖z‖)⁻¹ <= 2 := by rw [inv_le_comm₀ (sub_pos_of_lt hz1) two_pos]; linarith
  apply (norm_log_sub_logTaylor_le n hz1).trans
  rw [mul_div_assoc]; rw [mul_comm]; rw [norm_pow]
  gcongr

open scoped Topology in
/--
lemma `log_sub_self_isBigO` / 引理 `log_sub_self_isBigO`

English:
lemma log_sub_self_isBigO
  proof: by
  convert! log_sub_logTaylor_isBigO 1
  simp [logTaylor_succ, logTaylor_zero]

中文:
引理 log_sub_self_isBigO
  证明: by
  convert! log_sub_logTaylor_isBigO 1
  simp [logTaylor_succ, logTaylor_zero]

Depends on / 依赖: convert, logTaylor_succ, logTaylor_zero, log_sub_logTaylor_isBigO
-/
lemma log_sub_self_isBigO :
    (fun z => log (1 + z) - z) =O[𝓝 0] fun z => z ^ 2 := by
  convert! log_sub_logTaylor_isBigO 1
  simp [logTaylor_succ, logTaylor_zero]

/--
lemma `norm_log_one_add_le` / 引理 `norm_log_one_add_le`

English:
lemma norm_log_one_add_le
  given: {z : Complex} (hz : ‖z‖ < 1)
  proof: by
  rw [← sub_add_cancel (log (1 + z)) z]
  exact norm_add_le_of_le (Complex.norm_log_one_add_sub_self_le hz) le_rfl

中文:
引理 norm_log_one_add_le
  条件: {z : 复形} (hz : ‖z‖ < 1)
  证明: by
  rw [← sub_add_cancel (log (1 + z)) z]
  exact norm_add_le_of_le (Complex.norm_log_one_add_sub_self_le hz) le_rfl

Depends on / 依赖: Complex.norm_log_one_add_sub_self_le, le_rfl, norm_add_le_of_le, norm_log_one_add_sub_self_le, sub_add_cancel
-/
lemma norm_log_one_add_le {z : Complex} (hz : ‖z‖ < 1) :
    ‖log (1 + z)‖ <= ‖z‖ ^ 2 * (1 - ‖z‖)⁻¹ / 2 + ‖z‖ := by
  rw [← sub_add_cancel (log (1 + z)) z]
  exact norm_add_le_of_le (Complex.norm_log_one_add_sub_self_le hz) le_rfl

/--
lemma `norm_log_one_add_half_le_self` / 引理 `norm_log_one_add_half_le_self`

English:
lemma norm_log_one_add_half_le_self
  given: {z : Complex} (hz : ‖z‖ <= 1 / 2)
  statement: ‖log (1 + z)‖ <= (3 / 2) * ‖z‖
  proof: by
  apply le_trans (norm_log_one_add_le (lt_of_le_of_lt hz one_half_lt_one))
  have hz3 : (1 - ‖z‖)⁻¹ <= 2 := by
    rw [inv_eq_one_div]; rw [div_le_iff₀]
    · linarith
    · linarith
  have hz4 : ‖z‖ ^ 2 * (1 - ‖z‖)⁻¹ / 2 <= ‖z‖ / 2 * 2 / 2 := by
    gcongr
    · rw [inv_nonneg]
      linarith
  

中文:
引理 norm_log_one_add_half_le_self
  条件: {z : 复形} (hz : ‖z‖ <= 1 / 2)
  结论: ‖log (1 + z)‖ <= (3 / 2) * ‖z‖
  证明: by
  apply le_trans (norm_log_one_add_le (lt_of_le_of_lt hz one_half_lt_one))
  have hz3 : (1 - ‖z‖)⁻¹ <= 2 := by
    rw [inv_eq_one_div]; rw [div_le_iff₀]
    · linarith
    · linarith
  have hz4 : ‖z‖ ^ 2 * (1 - ‖z‖)⁻¹ / 2 <= ‖z‖ / 2 * 2 / 2 := by
    gcongr
    · rw [inv_nonneg]
      linarith
  

Depends on / 依赖: IsUnit, IsUnit.div_mul_cancel, OfNat.ofNat_ne_zero, div_eq_mul_one_div, div_mul_cancel, inv_eq_one_div, inv_nonneg, isUnit_iff_ne_zero, le_trans, lt_of_le_of_lt, ne_eq, norm_log_one_add_le, not_false_eq_true, ofNat_ne_zero, one_half_lt_one
-/
lemma norm_log_one_add_half_le_self {z : Complex} (hz : ‖z‖ <= 1 / 2) : ‖log (1 + z)‖ <= (3 / 2) * ‖z‖ := by
  apply le_trans (norm_log_one_add_le (lt_of_le_of_lt hz one_half_lt_one))
  have hz3 : (1 - ‖z‖)⁻¹ <= 2 := by
    rw [inv_eq_one_div]; rw [div_le_iff₀]
    · linarith
    · linarith
  have hz4 : ‖z‖ ^ 2 * (1 - ‖z‖)⁻¹ / 2 <= ‖z‖ / 2 * 2 / 2 := by
    gcongr
    · rw [inv_nonneg]
      linarith
    · rw [sq, div_eq_mul_one_div]
      gcongr
  simp only [isUnit_iff_ne_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    IsUnit.div_mul_cancel] at hz4
  linarith

/--
lemma `norm_log_one_sub_inv_add_logTaylor_neg_le` / 引理 `norm_log_one_sub_inv_add_logTaylor_neg_le`

English:
lemma norm_log_one_sub_inv_add_logTaylor_neg_le
  given: (n : Nat) {z : Complex} (hz : ‖z‖ < 1)
  proof: by
  rw [sub_eq_add_neg]; rw [log_inv _ slitPlane_arg_ne_pi mem_slitPlane_of_norm_lt_one (norm_neg z).symm ▸ hz]; rw [← sub_neg_eq_add]; rw [← neg_sub']; rw [norm_neg]
convert! norm_log_sub_logTaylor_le n (norm_neg z).symm ▸ hz using 4 <;> rw [norm_neg]

中文:
引理 norm_log_one_sub_inv_add_logTaylor_neg_le
  条件: (n : 自然数) {z : 复形} (hz : ‖z‖ < 1)
  证明: by
  rw [sub_eq_add_neg]; rw [log_inv _ slitPlane_arg_ne_pi mem_slitPlane_of_norm_lt_one (norm_neg z).symm ▸ hz]; rw [← sub_neg_eq_add]; rw [← neg_sub']; rw [norm_neg]
convert! norm_log_sub_logTaylor_le n (norm_neg z).symm ▸ hz using 4 <;> rw [norm_neg]

Depends on / 依赖: convert, log_inv, mem_slitPlane_of_norm_lt_one, neg_sub, norm_log_sub_logTaylor_le, norm_neg, slitPlane_arg_ne_pi, sub_eq_add_neg, sub_neg_eq_add
-/
lemma norm_log_one_sub_inv_add_logTaylor_neg_le (n : Nat) {z : Complex} (hz : ‖z‖ < 1) :
    ‖log (1 - z)⁻¹ + logTaylor (n + 1) (-z)‖ <= ‖z‖ ^ (n + 1) * (1 - ‖z‖)⁻¹ / (n + 1) := by
  rw [sub_eq_add_neg]; rw [log_inv _ slitPlane_arg_ne_pi mem_slitPlane_of_norm_lt_one (norm_neg z).symm ▸ hz]; rw [← sub_neg_eq_add]; rw [← neg_sub']; rw [norm_neg]
convert! norm_log_sub_logTaylor_le n (norm_neg z).symm ▸ hz using 4 <;> rw [norm_neg]

/--
lemma `norm_log_one_sub_inv_sub_self_le` / 引理 `norm_log_one_sub_inv_sub_self_le`

English:
lemma norm_log_one_sub_inv_sub_self_le
  given: {z : Complex} (hz : ‖z‖ < 1)
  proof: by
  convert! norm_log_one_sub_inv_add_logTaylor_neg_le 1 hz using 2
  · simp [logTaylor_succ, logTaylor_zero, sub_eq_add_neg]
  · norm_num

中文:
引理 norm_log_one_sub_inv_sub_self_le
  条件: {z : 复形} (hz : ‖z‖ < 1)
  证明: by
  convert! norm_log_one_sub_inv_add_logTaylor_neg_le 1 hz using 2
  · simp [logTaylor_succ, logTaylor_zero, sub_eq_add_neg]
  · norm_num

Depends on / 依赖: convert, logTaylor_succ, logTaylor_zero, norm_log_one_sub_inv_add_logTaylor_neg_le, sub_eq_add_neg
-/
lemma norm_log_one_sub_inv_sub_self_le {z : Complex} (hz : ‖z‖ < 1) :
    ‖log (1 - z)⁻¹ - z‖ <= ‖z‖ ^ 2 * (1 - ‖z‖)⁻¹ / 2 := by
  convert! norm_log_one_sub_inv_add_logTaylor_neg_le 1 hz using 2
  · simp [logTaylor_succ, logTaylor_zero, sub_eq_add_neg]
  · norm_num

open Filter Asymptotics in
/--
lemma `hasSum_taylorSeries_log` / 引理 `hasSum_taylorSeries_log`

English:
lemma hasSum_taylorSeries_log
  given: {z : Complex} (hz : ‖z‖ < 1)
  proof: by
  refine (hasSum_iff_tendsto_nat_of_summable_norm ?_).mpr ?_
  · refine (summable_geometric_of_norm_lt_one hz).norm.of_nonneg_of_le (fun _ => norm_nonneg _) ?_
    intro n
    simp only [norm_div, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, norm_natCast]
    rcases n.eq_zero_or_pos 

中文:
引理 hasSum_taylorSeries_log
  条件: {z : 复形} (hz : ‖z‖ < 1)
  证明: by
  refine (hasSum_iff_tendsto_nat_of_summable_norm ?_).mpr ?_
  · refine (summable_geometric_of_norm_lt_one hz).norm.of_nonneg_of_le (fun _ => norm_nonneg _) ?_
    intro n
    simp only [norm_div, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, norm_natCast]
    rcases n.eq_zero_or_pos 

Depends on / 依赖: div_one, eq_zero_or_pos, hasSum_iff_tendsto_nat_of_summable_norm, isLittleO_iff_tendsto, logTaylor, n.eq_zero_or_pos, norm.of_nonneg_of_le, norm_div, norm_mul, norm_natCast, norm_neg, norm_nonneg, norm_one, norm_pow, of_nonneg_of_le, one_mul, one_pow, summable_geometric_of_norm_lt_one, tendsto_sub_nhds_zero_iff
-/
lemma hasSum_taylorSeries_log {z : Complex} (hz : ‖z‖ < 1) :
    HasSum (fun n : Nat => (-1) ^ (n + 1) * z ^ n / n) (log (1 + z)) := by
  refine (hasSum_iff_tendsto_nat_of_summable_norm ?_).mpr ?_
  · refine (summable_geometric_of_norm_lt_one hz).norm.of_nonneg_of_le (fun _ => norm_nonneg _) ?_
    intro n
    simp only [norm_div, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, norm_natCast]
    rcases n.eq_zero_or_pos with rfl | hn
    · simp
    conv => enter [2]; rw [← div_one (‖z‖ ^ n)]
    gcongr
    norm_cast
  · rw [← tendsto_sub_nhds_zero_iff]
    conv => enter [1, x]; rw [← div_one (_ - _), ← logTaylor]
    rw [← isLittleO_iff_tendsto fun _ h => (one_ne_zero h).elim]
refine IsLittleO.trans_isBigO ?_ isBigO_const_one Complex (1 : Real) atTop
    have H : (fun n => logTaylor n z - log (1 + z)) =O[atTop] (fun n : Nat => ‖z‖ ^ n) := by
      have (n : Nat) : ‖logTaylor n z - log (1 + z)‖
          <= (max ‖log (1 + z)‖ (1 - ‖z‖)⁻¹) * ‖(‖z‖ ^ n)‖ := by
        rw [norm_sub_rev]; rw [norm_pow]; rw [norm_norm]
        cases n with
        | zero => simp [logTaylor_zero]
        | succ n =>
            refine (norm_log_sub_logTaylor_le n hz).trans ?_
            rw [mul_comm]; rw [← div_one ((max _ _) * _)]
            gcongr
            · exact le_max_right ..
            · linarith
      exact (isBigOWith_of_le' atTop this).isBigO
    refine IsBigO.trans_isLittleO H ?_
    convert! isLittleO_pow_pow_of_lt_left (norm_nonneg z) hz
    exact (one_pow _).symm

/--
lemma `hasSum_taylorSeries_neg_log` / 引理 `hasSum_taylorSeries_neg_log`

English:
lemma hasSum_taylorSeries_neg_log
  given: {z : Complex} (hz : ‖z‖ < 1)
  proof: by
  conv => enter [1, n]; rw [← neg_neg (z ^ n / n)]
  refine HasSum.neg ?_
  convert! hasSum_taylorSeries_log (z := -z) (norm_neg z ▸ hz) using 2 with n
  rcases n.eq_zero_or_pos with rfl | hn
  · simp
  simp [field, pow_add, ← mul_pow]

中文:
引理 hasSum_taylorSeries_neg_log
  条件: {z : 复形} (hz : ‖z‖ < 1)
  证明: by
  conv => enter [1, n]; rw [← neg_neg (z ^ n / n)]
  refine HasSum.neg ?_
  convert! hasSum_taylorSeries_log (z := -z) (norm_neg z ▸ hz) using 2 with n
  rcases n.eq_zero_or_pos with rfl | hn
  · simp
  simp [field, pow_add, ← mul_pow]

Depends on / 依赖: HasSum, HasSum.neg, convert, eq_zero_or_pos, hasSum_taylorSeries_log, mul_pow, n.eq_zero_or_pos, neg_neg, norm_neg, pow_add
-/
lemma hasSum_taylorSeries_neg_log {z : Complex} (hz : ‖z‖ < 1) :
    HasSum (fun n : Nat => z ^ n / n) (-log (1 - z)) := by
  conv => enter [1, n]; rw [← neg_neg (z ^ n / n)]
  refine HasSum.neg ?_
  convert! hasSum_taylorSeries_log (z := -z) (norm_neg z ▸ hz) using 2 with n
  rcases n.eq_zero_or_pos with rfl | hn
  · simp
  simp [field, pow_add, ← mul_pow]

/--
lemma `hasSum_taylorSeries_neg_log'` / 引理 `hasSum_taylorSeries_neg_log'`

English:
lemma hasSum_taylorSeries_neg_log'
  given: {z : Complex} (hz : ‖z‖ < 1)
  proof: by
  rw_mod_cast [hasSum_nat_add_iff 1 (f := fun n => z ^ n / n) (g := -log (1 - z))]
  simpa using hasSum_taylorSeries_neg_log hz

中文:
引理 hasSum_taylorSeries_neg_log'
  条件: {z : 复形} (hz : ‖z‖ < 1)
  证明: by
  rw_mod_cast [hasSum_nat_add_iff 1 (f := fun n => z ^ n / n) (g := -log (1 - z))]
  simpa using hasSum_taylorSeries_neg_log hz

Depends on / 依赖: hasSum_nat_add_iff, hasSum_taylorSeries_neg_log, rw_mod_cast
-/
lemma hasSum_taylorSeries_neg_log' {z : Complex} (hz : ‖z‖ < 1) :
    HasSum (fun n : Nat => z ^ (n + 1) / (n + 1)) (-log (1 - z)) := by
  rw_mod_cast [hasSum_nat_add_iff 1 (f := fun n => z ^ n / n) (g := -log (1 - z))]
  simpa using hasSum_taylorSeries_neg_log hz

end Complex

section Limits

/-! Limits of functions of the form `(1 + t/x + o(1/x)) ^ x` as `x → ∞`. -/

open Filter Asymptotics
open scoped Topology

namespace Complex

/--
lemma `tendsto_mul_log_one_add_of_tendsto` / 引理 `tendsto_mul_log_one_add_of_tendsto`

English:
lemma tendsto_mul_log_one_add_of_tendsto
  statement: {g : Real -> Complex} {t : Complex}
  proof: by
  apply hg.congr_dist
  refine IsBigO.trans_tendsto ?_ tendsto_inv_atTop_zero.ofReal
  simp_rw [dist_comm (_ * g _), dist_eq, ← mul_sub, isBigO_norm_left]
  calc
    _ =O[atTop] fun x => x * g x ^ 2 := by
      have hg0 := tendsto_zero_of_isBoundedUnder_smul_of_tendsto_cobounded hg.norm.isBounded

中文:
引理 tendsto_mul_log_one_add_of_tendsto
  结论: {g : 实数 -> 复形} {t : 复形}
  证明: by
  apply hg.congr_dist
  refine IsBigO.trans_tendsto ?_ tendsto_inv_atTop_zero.ofReal
  simp_rw [dist_comm (_ * g _), dist_eq, ← mul_sub, isBigO_norm_left]
  calc
    _ =O[atTop] fun x => x * g x ^ 2 := by
      have hg0 := tendsto_zero_of_isBoundedUnder_smul_of_tendsto_cobounded hg.norm.isBounded

Depends on / 依赖: IsBigO, IsBigO.trans_tendsto, RCLike, RCLike.tendsto_ofReal_atTop_cobounded, comp_tendsto, congr_dist, dist_comm, dist_eq, eventually_ne_atTop, filter_upwards, hg.congr_dist, hg.norm.isBoundedUnder_le, isBigO_norm_left, isBigO_refl, isBoundedUnder_le, log_sub_self_isBigO, log_sub_self_isBigO.comp_tendsto, mul_sub, ofReal, simp_rw
-/
lemma tendsto_mul_log_one_add_of_tendsto {g : Real -> Complex} {t : Complex}
    (hg : Tendsto (fun x => x * g x) atTop (𝓝 t)) :
    Tendsto (fun x => x * log (1 + g x)) atTop (𝓝 t) := by
  apply hg.congr_dist
  refine IsBigO.trans_tendsto ?_ tendsto_inv_atTop_zero.ofReal
  simp_rw [dist_comm (_ * g _), dist_eq, ← mul_sub, isBigO_norm_left]
  calc
    _ =O[atTop] fun x => x * g x ^ 2 := by
      have hg0 := tendsto_zero_of_isBoundedUnder_smul_of_tendsto_cobounded hg.norm.isBoundedUnder_le
        (RCLike.tendsto_ofReal_atTop_cobounded Complex)
      exact (isBigO_refl _ _).mul (log_sub_self_isBigO.comp_tendsto hg0)
    _ =ᶠ[atTop] fun x => (x * g x) ^ 2 * x⁻¹ := by
      filter_upwards [eventually_ne_atTop 0] with x hx0
      rw [ofReal_inv]; rw [eq_mul_inv_iff_mul_eq₀ (mod_cast hx0)]
      ring
    _ =O[atTop] _ := by
      simpa using isBigO_const_of_tendsto hg (one_ne_zero (α := Complex))
.mul (isBigO_refl _ _) .pow 2

/--
lemma `tendsto_one_add_cpow_exp_of_tendsto` / 引理 `tendsto_one_add_cpow_exp_of_tendsto`

English:
lemma tendsto_one_add_cpow_exp_of_tendsto
  statement: {g : Real -> Complex} {t : Complex}
  proof: by
  apply ((continuous_exp.tendsto _).comp (tendsto_mul_log_one_add_of_tendsto hg)).congr'
  have hg0 := tendsto_zero_of_isBoundedUnder_smul_of_tendsto_cobounded
    hg.norm.isBoundedUnder_le (RCLike.tendsto_ofReal_atTop_cobounded Complex)
  filter_upwards [hg0.eventually_ne (show 0 != -1 by simp)]

中文:
引理 tendsto_one_add_cpow_exp_of_tendsto
  结论: {g : 实数 -> 复形} {t : 复形}
  证明: by
  apply ((continuous_exp.tendsto _).comp (tendsto_mul_log_one_add_of_tendsto hg)).congr'
  have hg0 := tendsto_zero_of_isBoundedUnder_smul_of_tendsto_cobounded
    hg.norm.isBoundedUnder_le (RCLike.tendsto_ofReal_atTop_cobounded Complex)
  filter_upwards [hg0.eventually_ne (show 0 != -1 by simp)]

Depends on / 依赖: RCLike, RCLike.tendsto_ofReal_atTop_cobounded, add_eq_zero_iff_neg_eq, add_eq_zero_iff_neg_eq.mp, continuous_exp, continuous_exp.tendsto, cpow_def_of_ne_zero, eventually_ne, filter_upwards, hg.norm.isBoundedUnder_le, hg0.eventually_ne, isBoundedUnder_le, mul_comm, tendsto, tendsto_mul_log_one_add_of_tendsto, tendsto_ofReal_atTop_cobounded, tendsto_zero_of_isBoundedUnder_smul_of_tendsto_cobounded
-/
lemma tendsto_one_add_cpow_exp_of_tendsto {g : Real -> Complex} {t : Complex}
    (hg : Tendsto (fun x => x * g x) atTop (𝓝 t)) :
    Tendsto (fun x => (1 + g x) ^ (x : Complex)) atTop (𝓝 (exp t)) := by
  apply ((continuous_exp.tendsto _).comp (tendsto_mul_log_one_add_of_tendsto hg)).congr'
  have hg0 := tendsto_zero_of_isBoundedUnder_smul_of_tendsto_cobounded
    hg.norm.isBoundedUnder_le (RCLike.tendsto_ofReal_atTop_cobounded Complex)
  filter_upwards [hg0.eventually_ne (show 0 != -1 by simp)] with x hg1
  dsimp
  rw [cpow_def_of_ne_zero]; rw [mul_comm]
  intro hg0
  rw [← add_eq_zero_iff_neg_eq.mp hg0] at hg1
  norm_num at hg1

/--
lemma `tendsto_one_add_div_cpow_exp` / 引理 `tendsto_one_add_div_cpow_exp`

English:
lemma tendsto_one_add_div_cpow_exp
  given: (t : Complex)
  proof: by
  apply tendsto_one_add_cpow_exp_of_tendsto
  apply tendsto_nhds_of_eventually_eq
  filter_upwards [eventually_ne_atTop 0] with x hx0
  exact mul_div_cancel₀ t (mod_cast hx0)

中文:
引理 tendsto_one_add_div_cpow_exp
  条件: (t : 复形)
  证明: by
  apply tendsto_one_add_cpow_exp_of_tendsto
  apply tendsto_nhds_of_eventually_eq
  filter_upwards [eventually_ne_atTop 0] with x hx0
  exact mul_div_cancel₀ t (mod_cast hx0)

Depends on / 依赖: eventually_ne_atTop, filter_upwards, mod_cast, tendsto_nhds_of_eventually_eq, tendsto_one_add_cpow_exp_of_tendsto
-/
lemma tendsto_one_add_div_cpow_exp (t : Complex) :
    Tendsto (fun x : Real => (1 + t / x) ^ (x : Complex)) atTop (𝓝 (exp t)) := by
  apply tendsto_one_add_cpow_exp_of_tendsto
  apply tendsto_nhds_of_eventually_eq
  filter_upwards [eventually_ne_atTop 0] with x hx0
  exact mul_div_cancel₀ t (mod_cast hx0)

/--
lemma `tendsto_nat_mul_log_one_add_of_tendsto` / 引理 `tendsto_nat_mul_log_one_add_of_tendsto`

English:
lemma tendsto_nat_mul_log_one_add_of_tendsto
  statement: {g : Nat -> Complex} {t : Complex}
  proof: tendsto_mul_log_one_add_of_tendsto (tendsto_smul_comp_nat_floor_of_tendsto_mul hg)
.congr (by simp) .comp tendsto_natCast_atTop_atTop

中文:
引理 tendsto_nat_mul_log_one_add_of_tendsto
  结论: {g : 自然数 -> 复形} {t : 复形}
  证明: tendsto_mul_log_one_add_of_tendsto (tendsto_smul_comp_nat_floor_of_tendsto_mul hg)
.congr (by simp) .comp tendsto_natCast_atTop_atTop

Depends on / 依赖: tendsto_mul_log_one_add_of_tendsto, tendsto_natCast_atTop_atTop, tendsto_smul_comp_nat_floor_of_tendsto_mul
-/
lemma tendsto_nat_mul_log_one_add_of_tendsto {g : Nat -> Complex} {t : Complex}
    (hg : Tendsto (fun n => n * g n) atTop (𝓝 t)) :
    Tendsto (fun n => n * log (1 + g n)) atTop (𝓝 t) :=
  tendsto_mul_log_one_add_of_tendsto (tendsto_smul_comp_nat_floor_of_tendsto_mul hg)
.congr (by simp) .comp tendsto_natCast_atTop_atTop

/--
lemma `tendsto_one_add_pow_exp_of_tendsto` / 引理 `tendsto_one_add_pow_exp_of_tendsto`

English:
lemma tendsto_one_add_pow_exp_of_tendsto
  statement: {g : Nat -> Complex} {t : Complex}
  proof: tendsto_one_add_cpow_exp_of_tendsto (tendsto_smul_comp_nat_floor_of_tendsto_mul hg)
.congr (by simp) .comp tendsto_natCast_atTop_atTop

中文:
引理 tendsto_one_add_pow_exp_of_tendsto
  结论: {g : 自然数 -> 复形} {t : 复形}
  证明: tendsto_one_add_cpow_exp_of_tendsto (tendsto_smul_comp_nat_floor_of_tendsto_mul hg)
.congr (by simp) .comp tendsto_natCast_atTop_atTop

Depends on / 依赖: tendsto_natCast_atTop_atTop, tendsto_one_add_cpow_exp_of_tendsto, tendsto_smul_comp_nat_floor_of_tendsto_mul
-/
lemma tendsto_one_add_pow_exp_of_tendsto {g : Nat -> Complex} {t : Complex}
    (hg : Tendsto (fun n => n * g n) atTop (𝓝 t)) :
    Tendsto (fun n => (1 + g n) ^ n) atTop (𝓝 (exp t)) :=
  tendsto_one_add_cpow_exp_of_tendsto (tendsto_smul_comp_nat_floor_of_tendsto_mul hg)
.congr (by simp) .comp tendsto_natCast_atTop_atTop

/--
lemma `tendsto_one_add_div_pow_exp` / 引理 `tendsto_one_add_div_pow_exp`

English:
lemma tendsto_one_add_div_pow_exp
  given: (t : Complex)
  proof: .congr (by simp) .comp tendsto_natCast_atTop_atTop tendsto_one_add_div_cpow_exp t

中文:
引理 tendsto_one_add_div_pow_exp
  条件: (t : 复形)
  证明: .congr (by simp) .comp tendsto_natCast_atTop_atTop tendsto_one_add_div_cpow_exp t

Depends on / 依赖: tendsto_natCast_atTop_atTop, tendsto_one_add_div_cpow_exp
-/
lemma tendsto_one_add_div_pow_exp (t : Complex) :
    Tendsto (fun n : Nat => (1 + t / n) ^ n) atTop (𝓝 (exp t)) :=
.congr (by simp) .comp tendsto_natCast_atTop_atTop tendsto_one_add_div_cpow_exp t

/--
lemma `tendsto_pow_exp_of_isLittleO_sub_add_div` / 引理 `tendsto_pow_exp_of_isLittleO_sub_add_div`

English:
lemma tendsto_pow_exp_of_isLittleO_sub_add_div
  statement: {f : Nat -> Complex} (t : Complex)
  proof: by
  rw [show (fun n => f n ^ n) = (fun n => (1 + (f n - 1)) ^ n) by ext; simp]
  refine tendsto_one_add_pow_exp_of_tendsto (tendsto_sub_nhds_zero_iff.1 ?_)
  convert! hf.tendsto_inv_smul_nhds_zero.congr' ?_
  filter_upwards [eventually_ne_atTop 0] with n h0
  simp
  field_simp [n.cast_ne_zero.2 h0]

中文:
引理 tendsto_pow_exp_of_isLittleO_sub_add_div
  结论: {f : 自然数 -> 复形} (t : 复形)
  证明: by
  rw [show (fun n => f n ^ n) = (fun n => (1 + (f n - 1)) ^ n) by ext; simp]
  refine tendsto_one_add_pow_exp_of_tendsto (tendsto_sub_nhds_zero_iff.1 ?_)
  convert! hf.tendsto_inv_smul_nhds_zero.congr' ?_
  filter_upwards [eventually_ne_atTop 0] with n h0
  simp
  field_simp [n.cast_ne_zero.2 h0]

Depends on / 依赖: cast_ne_zero, convert, eventually_ne_atTop, filter_upwards, hf.tendsto_inv_smul_nhds_zero.congr, n.cast_ne_zero, tendsto_inv_smul_nhds_zero, tendsto_one_add_pow_exp_of_tendsto, tendsto_sub_nhds_zero_iff
-/
lemma tendsto_pow_exp_of_isLittleO_sub_add_div {f : Nat -> Complex} (t : Complex)
    (hf : (fun n => f n - (1 + t / n)) =o[atTop] fun n => 1 / (n : Complex)) :
    Tendsto (fun n => f n ^ n) atTop (𝓝 (exp t)) := by
  rw [show (fun n => f n ^ n) = (fun n => (1 + (f n - 1)) ^ n) by ext; simp]
  refine tendsto_one_add_pow_exp_of_tendsto (tendsto_sub_nhds_zero_iff.1 ?_)
  convert! hf.tendsto_inv_smul_nhds_zero.congr' ?_
  filter_upwards [eventually_ne_atTop 0] with n h0
  simp
  field_simp [n.cast_ne_zero.2 h0]
  ring

end Complex

namespace Real

/--
lemma `tendsto_mul_log_one_add_of_tendsto` / 引理 `tendsto_mul_log_one_add_of_tendsto`

English:
lemma tendsto_mul_log_one_add_of_tendsto
  statement: {g : Real -> Real} {t : Real}
  proof: by
  have hg0 := tendsto_zero_of_isBoundedUnder_smul_of_tendsto_cobounded
    hg.norm.isBoundedUnder_le (tendsto_id'.mpr (by simp))
  rw [← tendsto_ofReal_iff] at hg ⊢
  push_cast at hg ⊢
  apply (Complex.tendsto_mul_log_one_add_of_tendsto hg).congr'
  filter_upwards [hg0.eventually_const_le (show (

中文:
引理 tendsto_mul_log_one_add_of_tendsto
  结论: {g : 实数 -> 实数} {t : 实数}
  证明: by
  have hg0 := tendsto_zero_of_isBoundedUnder_smul_of_tendsto_cobounded
    hg.norm.isBoundedUnder_le (tendsto_id'.mpr (by simp))
  rw [← tendsto_ofReal_iff] at hg ⊢
  push_cast at hg ⊢
  apply (Complex.tendsto_mul_log_one_add_of_tendsto hg).congr'
  filter_upwards [hg0.eventually_const_le (show (

Depends on / 依赖: Complex.ofReal_add, Complex.ofReal_log, Complex.ofReal_one, Complex.tendsto_mul_log_one_add_of_tendsto, eventually_const_le, filter_upwards, hg.norm.isBoundedUnder_le, hg0.eventually_const_le, isBoundedUnder_le, ofReal_add, ofReal_log, ofReal_one, tendsto_id, tendsto_mul_log_one_add_of_tendsto, tendsto_ofReal_iff, tendsto_zero_of_isBoundedUnder_smul_of_tendsto_cobounded
-/
lemma tendsto_mul_log_one_add_of_tendsto {g : Real -> Real} {t : Real}
    (hg : Tendsto (fun x => x * g x) atTop (𝓝 t)) :
    Tendsto (fun x => x * log (1 + g x)) atTop (𝓝 t) := by
  have hg0 := tendsto_zero_of_isBoundedUnder_smul_of_tendsto_cobounded
    hg.norm.isBoundedUnder_le (tendsto_id'.mpr (by simp))
  rw [← tendsto_ofReal_iff] at hg ⊢
  push_cast at hg ⊢
  apply (Complex.tendsto_mul_log_one_add_of_tendsto hg).congr'
  filter_upwards [hg0.eventually_const_le (show (-1 : Real) < 0 by simp)] with x hg1
  rw [Complex.ofReal_log (by linarith)]; rw [Complex.ofReal_add]; rw [Complex.ofReal_one]

/--
theorem `tendsto_mul_log_one_add_div_atTop` / 定理 `tendsto_mul_log_one_add_div_atTop`

English:
theorem tendsto_mul_log_one_add_div_atTop
  given: (t : Real)
  proof: tendsto_mul_log_one_add_of_tendsto
tendsto_const_nhds.congr'
(EventuallyEq.div_mul_cancel_atTop tendsto_id).symm.trans
.of_eq funext fun _ => mul_comm _ _

中文:
定理 tendsto_mul_log_one_add_div_atTop
  条件: (t : 实数)
  证明: tendsto_mul_log_one_add_of_tendsto
tendsto_const_nhds.congr'
(EventuallyEq.div_mul_cancel_atTop tendsto_id).symm.trans
.of_eq funext fun _ => mul_comm _ _

Depends on / 依赖: EventuallyEq, EventuallyEq.div_mul_cancel_atTop, div_mul_cancel_atTop, mul_comm, of_eq, symm.trans, tendsto_const_nhds, tendsto_const_nhds.congr, tendsto_id, tendsto_mul_log_one_add_of_tendsto
-/
theorem tendsto_mul_log_one_add_div_atTop (t : Real) :
    Tendsto (fun x => x * log (1 + t / x)) atTop (𝓝 t) :=
tendsto_mul_log_one_add_of_tendsto
tendsto_const_nhds.congr'
(EventuallyEq.div_mul_cancel_atTop tendsto_id).symm.trans
.of_eq funext fun _ => mul_comm _ _

/--
lemma `tendsto_one_add_rpow_exp_of_tendsto` / 引理 `tendsto_one_add_rpow_exp_of_tendsto`

English:
lemma tendsto_one_add_rpow_exp_of_tendsto
  statement: {g : Real -> Real} {t : Real}
  proof: by
  have hg0 := tendsto_zero_of_isBoundedUnder_smul_of_tendsto_cobounded
    hg.norm.isBoundedUnder_le (tendsto_id'.mpr (by simp))
  rw [← tendsto_ofReal_iff] at hg ⊢
  push_cast at hg ⊢
  apply (Complex.tendsto_one_add_cpow_exp_of_tendsto hg).congr'
  filter_upwards [hg0.eventually_const_le (show 

中文:
引理 tendsto_one_add_rpow_exp_of_tendsto
  结论: {g : 实数 -> 实数} {t : 实数}
  证明: by
  have hg0 := tendsto_zero_of_isBoundedUnder_smul_of_tendsto_cobounded
    hg.norm.isBoundedUnder_le (tendsto_id'.mpr (by simp))
  rw [← tendsto_ofReal_iff] at hg ⊢
  push_cast at hg ⊢
  apply (Complex.tendsto_one_add_cpow_exp_of_tendsto hg).congr'
  filter_upwards [hg0.eventually_const_le (show 

Depends on / 依赖: Complex.ofReal_add, Complex.ofReal_cpow, Complex.ofReal_one, Complex.tendsto_one_add_cpow_exp_of_tendsto, eventually_const_le, filter_upwards, hg.norm.isBoundedUnder_le, hg0.eventually_const_le, isBoundedUnder_le, ofReal_add, ofReal_cpow, ofReal_one, tendsto_id, tendsto_ofReal_iff, tendsto_one_add_cpow_exp_of_tendsto, tendsto_zero_of_isBoundedUnder_smul_of_tendsto_cobounded
-/
lemma tendsto_one_add_rpow_exp_of_tendsto {g : Real -> Real} {t : Real}
    (hg : Tendsto (fun x => x * g x) atTop (𝓝 t)) :
    Tendsto (fun x => (1 + g x) ^ x) atTop (𝓝 (exp t)) := by
  have hg0 := tendsto_zero_of_isBoundedUnder_smul_of_tendsto_cobounded
    hg.norm.isBoundedUnder_le (tendsto_id'.mpr (by simp))
  rw [← tendsto_ofReal_iff] at hg ⊢
  push_cast at hg ⊢
  apply (Complex.tendsto_one_add_cpow_exp_of_tendsto hg).congr'
  filter_upwards [hg0.eventually_const_le (show (-1 : Real) < 0 by simp)] with x hg1
  rw [Complex.ofReal_cpow (by linarith)]; rw [Complex.ofReal_add]; rw [Complex.ofReal_one]

/--
lemma `tendsto_one_add_div_rpow_exp` / 引理 `tendsto_one_add_div_rpow_exp`

English:
lemma tendsto_one_add_div_rpow_exp
  given: (t : Real)
  proof: by
  apply tendsto_one_add_rpow_exp_of_tendsto
  apply tendsto_nhds_of_eventually_eq
  filter_upwards [eventually_ne_atTop 0] with x hx0
  exact mul_div_cancel₀ t (mod_cast hx0)

中文:
引理 tendsto_one_add_div_rpow_exp
  条件: (t : 实数)
  证明: by
  apply tendsto_one_add_rpow_exp_of_tendsto
  apply tendsto_nhds_of_eventually_eq
  filter_upwards [eventually_ne_atTop 0] with x hx0
  exact mul_div_cancel₀ t (mod_cast hx0)

Depends on / 依赖: eventually_ne_atTop, filter_upwards, mod_cast, tendsto_nhds_of_eventually_eq, tendsto_one_add_rpow_exp_of_tendsto
-/
lemma tendsto_one_add_div_rpow_exp (t : Real) :
    Tendsto (fun x : Real => (1 + t / x) ^ x) atTop (𝓝 (exp t)) := by
  apply tendsto_one_add_rpow_exp_of_tendsto
  apply tendsto_nhds_of_eventually_eq
  filter_upwards [eventually_ne_atTop 0] with x hx0
  exact mul_div_cancel₀ t (mod_cast hx0)

/--
lemma `tendsto_nat_mul_log_one_add_of_tendsto` / 引理 `tendsto_nat_mul_log_one_add_of_tendsto`

English:
lemma tendsto_nat_mul_log_one_add_of_tendsto
  statement: {g : Nat -> Real} {t : Real}
  proof: .comp tendsto_mul_log_one_add_of_tendsto (tendsto_smul_comp_nat_floor_of_tendsto_mul hg)
.congr (by simp) tendsto_natCast_atTop_atTop

中文:
引理 tendsto_nat_mul_log_one_add_of_tendsto
  结论: {g : 自然数 -> 实数} {t : 实数}
  证明: .comp tendsto_mul_log_one_add_of_tendsto (tendsto_smul_comp_nat_floor_of_tendsto_mul hg)
.congr (by simp) tendsto_natCast_atTop_atTop

Depends on / 依赖: tendsto_mul_log_one_add_of_tendsto, tendsto_natCast_atTop_atTop, tendsto_smul_comp_nat_floor_of_tendsto_mul
-/
lemma tendsto_nat_mul_log_one_add_of_tendsto {g : Nat -> Real} {t : Real}
    (hg : Tendsto (fun n => n * g n) atTop (𝓝 t)) :
    Tendsto (fun n => n * log (1 + g n)) atTop (𝓝 t) :=
.comp tendsto_mul_log_one_add_of_tendsto (tendsto_smul_comp_nat_floor_of_tendsto_mul hg)
.congr (by simp) tendsto_natCast_atTop_atTop

/--
lemma `tendsto_one_add_pow_exp_of_tendsto` / 引理 `tendsto_one_add_pow_exp_of_tendsto`

English:
lemma tendsto_one_add_pow_exp_of_tendsto
  statement: {g : Nat -> Real} {t : Real}
  proof: .comp tendsto_one_add_rpow_exp_of_tendsto (tendsto_smul_comp_nat_floor_of_tendsto_mul hg)
.congr (by simp) tendsto_natCast_atTop_atTop

中文:
引理 tendsto_one_add_pow_exp_of_tendsto
  结论: {g : 自然数 -> 实数} {t : 实数}
  证明: .comp tendsto_one_add_rpow_exp_of_tendsto (tendsto_smul_comp_nat_floor_of_tendsto_mul hg)
.congr (by simp) tendsto_natCast_atTop_atTop

Depends on / 依赖: tendsto_natCast_atTop_atTop, tendsto_one_add_rpow_exp_of_tendsto, tendsto_smul_comp_nat_floor_of_tendsto_mul
-/
lemma tendsto_one_add_pow_exp_of_tendsto {g : Nat -> Real} {t : Real}
    (hg : Tendsto (fun n => n * g n) atTop (𝓝 t)) :
    Tendsto (fun n => (1 + g n) ^ n) atTop (𝓝 (exp t)) :=
.comp tendsto_one_add_rpow_exp_of_tendsto (tendsto_smul_comp_nat_floor_of_tendsto_mul hg)
.congr (by simp) tendsto_natCast_atTop_atTop

/--
lemma `tendsto_one_add_div_pow_exp` / 引理 `tendsto_one_add_div_pow_exp`

English:
lemma tendsto_one_add_div_pow_exp
  given: (t : Real)
  proof: .congr (by simp) .comp tendsto_natCast_atTop_atTop tendsto_one_add_div_rpow_exp t

中文:
引理 tendsto_one_add_div_pow_exp
  条件: (t : 实数)
  证明: .congr (by simp) .comp tendsto_natCast_atTop_atTop tendsto_one_add_div_rpow_exp t

Depends on / 依赖: tendsto_natCast_atTop_atTop, tendsto_one_add_div_rpow_exp
-/
lemma tendsto_one_add_div_pow_exp (t : Real) :
    Tendsto (fun n : Nat => (1 + t / n) ^ n) atTop (𝓝 (exp t)) :=
.congr (by simp) .comp tendsto_natCast_atTop_atTop tendsto_one_add_div_rpow_exp t

end Real

end Limits
