/-
Copyright (c) 2024 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Analysis.Complex.LocallyUniformLimit
public import Mathlib.NumberTheory.LSeries.Convergence
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.Complex.HalfPlane

/-!
# Differentiability and derivatives of L-series

## Main results

* We show that the `LSeries` of `f` is differentiable at `s` when `re s` is greater than
  the abscissa of absolute convergence of `f` (`LSeries.hasDerivAt`) and that its derivative
  there is the negative of the `LSeries` of the point-wise product `log * f` (`LSeries.deriv`).

* We prove similar results for iterated derivatives (`LSeries.iteratedDeriv`).

* We use this to show that `LSeries f` is holomorphic on the right half-plane of
  absolute convergence (`LSeries.analyticOnNhd`).

## Implementation notes

We introduce `LSeries.logMul` as an abbreviation for the point-wise product `log * f`, to avoid
the problem that this expression does not type-check.
-/

public section

open Complex LSeries

/-!
### The derivative of an L-series
-/

/--
Definition of `LSeries.logMul` / `LSeries.logMul` 的定义

English:
abbreviation LSeries.logMul
  signature: (f : Nat -> Complex) (n : Nat)
  body: log n * f n

中文:
缩写 LSeries.logMul
  签名: (f : 自然数 -> Complex) (n : 自然数)
  定义体: log n * f n
-/
noncomputable abbrev LSeries.logMul (f : Nat -> Complex) (n : Nat) : Complex := log n * f n

/--
lemma `LSeries.hasDerivAt_term` / 引理 `LSeries.hasDerivAt_term`

English:
lemma LSeries.hasDerivAt_term
  given: (f : Nat -> Complex) (n : Nat) (s : Complex)
  proof: by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [hasDerivAt_const]
  simp_rw [term_of_ne_zero hn, ← neg_div, ← neg_mul, mul_comm, mul_div_assoc, div_eq_mul_inv,
    ← cpow_neg]
  exact HasDerivAt.const_mul (f n) (by simpa only [mul_comm, ← mul_neg_one (log n), ← mul_assoc]
    using (hasDerivAt_neg'

中文:
引理 LSeries.hasDerivAt_term
  条件: (f : 自然数 -> Complex) (n : 自然数) (s : Complex)
  证明: by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [hasDerivAt_const]
  simp_rw [term_of_ne_zero hn, ← neg_div, ← neg_mul, mul_comm, mul_div_assoc, div_eq_mul_inv,
    ← cpow_neg]
  exact HasDerivAt.const_mul (f n) (by simpa only [mul_comm, ← mul_neg_one (log n), ← mul_assoc]
    using (hasDerivAt_neg'

Depends on / 依赖: HasDerivAt, HasDerivAt.const_mul, Nat.cast_ne_zero.mpr, Or.inl, cast_ne_zero, const_cpow, const_mul, cpow_neg, div_eq_mul_inv, eq_or_ne, hasDerivAt_const, hasDerivAt_neg, mul_assoc, mul_comm, mul_div_assoc, mul_neg_one, neg_div, neg_mul, simp_rw, term_of_ne_zero
-/
lemma LSeries.hasDerivAt_term (f : Nat -> Complex) (n : Nat) (s : Complex) :
    HasDerivAt (fun z => term f z n) (-(term (logMul f) s n)) s := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [hasDerivAt_const]
  simp_rw [term_of_ne_zero hn, ← neg_div, ← neg_mul, mul_comm, mul_div_assoc, div_eq_mul_inv,
    ← cpow_neg]
  exact HasDerivAt.const_mul (f n) (by simpa only [mul_comm, ← mul_neg_one (log n), ← mul_assoc]
    using (hasDerivAt_neg' s).const_cpow (Or.inl <| Nat.cast_ne_zero.mpr hn))

/--
lemma `LSeries.LSeriesSummable_logMul_and_hasDerivAt` / 引理 `LSeries.LSeriesSummable_logMul_and_hasDerivAt`

English:
lemma LSeries.LSeriesSummable_logMul_and_hasDerivAt
  statement: {f : Nat -> Complex} {s : Complex}
  proof: by
  -- The L-series of `f` is summable at some real `x < re s`.
  obtain ⟨x, hxs, hf⟩ := LSeriesSummable_lt_re_of_abscissaOfAbsConv_lt_re h
  obtain ⟨y, hxy, hys⟩ := exists_between hxs
  -- We work in the right half-plane `y < re z`, for some `y` such that `x < y < re s`, on which
  -- we have a un

中文:
引理 LSeries.LSeriesSummable_logMul_and_hasDerivAt
  结论: {f : 自然数 -> Complex} {s : Complex}
  证明: by
  -- The L-series of `f` is summable at some real `x < re s`.
  obtain ⟨x, hxs, hf⟩ := LSeriesSummable_lt_re_of_abscissaOfAbsConv_lt_re h
  obtain ⟨y, hxy, hys⟩ := exists_between hxs
  -- We work in the right half-plane `y < re z`, for some `y` such that `x < y < re s`, on which
  -- we have a un
-/
private lemma LSeries.LSeriesSummable_logMul_and_hasDerivAt {f : Nat -> Complex} {s : Complex}
    (h : abscissaOfAbsConv f < s.re) :
    LSeriesSummable (logMul f) s ∧ HasDerivAt (LSeries f) (-LSeries (logMul f) s) s := by
  -- The L-series of `f` is summable at some real `x < re s`.
  obtain ⟨x, hxs, hf⟩ := LSeriesSummable_lt_re_of_abscissaOfAbsConv_lt_re h
  obtain ⟨y, hxy, hys⟩ := exists_between hxs
  -- We work in the right half-plane `y < re z`, for some `y` such that `x < y < re s`, on which
  -- we have a uniform summable bound on `‖term f z ·‖`.
  let S : Set Complex := {z | y < z.re}
  have h₀ : Summable (fun n => ‖term f x n‖) := summable_norm_iff.mpr hf
  have h₁ (n) : DifferentiableOn Complex (term f · n) S :=
    fun z _ => (hasDerivAt_term f n _).differentiableAt.differentiableWithinAt
  have h₂ : IsOpen S := isOpen_lt continuous_const continuous_re
  have h₃ (n z) (hz : z in S) : ‖term f z n‖ <= ‖term f x n‖ :=
    norm_term_le_of_re_le_re f (by simpa using! (hxy.trans hz).le) n
  have H := hasSum_deriv_of_summable_norm h₀ h₁ h₂ h₃ hys
  simp_rw [(hasDerivAt_term f _ _).deriv] at H
  refine ⟨summable_neg_iff.mp H.summable, ?_⟩
  simpa [← H.tsum_eq, tsum_neg] using! ((differentiableOn_tsum_of_summable_norm
    h₀ h₁ h₂ h₃).differentiableAt <| h₂.mem_nhds hys).hasDerivAt

/--
lemma `LSeries_hasDerivAt` / 引理 `LSeries_hasDerivAt`

English:
lemma LSeries_hasDerivAt
  given: {f : Nat -> Complex} {s : Complex} (h : abscissaOfAbsConv f < s.re)
  proof: (LSeriesSummable_logMul_and_hasDerivAt h).2

中文:
引理 LSeries_hasDerivAt
  条件: {f : 自然数 -> Complex} {s : Complex} (h : abscissaOfAbsConv f < s.re)
  证明: (LSeriesSummable_logMul_and_hasDerivAt h).2

Depends on / 依赖: LSeriesSummable_logMul_and_hasDerivAt
-/
lemma LSeries_hasDerivAt {f : Nat -> Complex} {s : Complex} (h : abscissaOfAbsConv f < s.re) :
    HasDerivAt (LSeries f) (-LSeries (logMul f) s) s :=
  (LSeriesSummable_logMul_and_hasDerivAt h).2

/--
lemma `LSeries_deriv` / 引理 `LSeries_deriv`

English:
lemma LSeries_deriv
  given: {f : Nat -> Complex} {s : Complex} (h : abscissaOfAbsConv f < s.re)
  proof: (LSeries_hasDerivAt h).deriv

中文:
引理 LSeries_deriv
  条件: {f : 自然数 -> Complex} {s : Complex} (h : abscissaOfAbsConv f < s.re)
  证明: (LSeries_hasDerivAt h).deriv

Depends on / 依赖: LSeries_hasDerivAt
-/
lemma LSeries_deriv {f : Nat -> Complex} {s : Complex} (h : abscissaOfAbsConv f < s.re) :
    deriv (LSeries f) s = -LSeries (logMul f) s :=
  (LSeries_hasDerivAt h).deriv

/--
lemma `LSeries_deriv_eqOn` / 引理 `LSeries_deriv_eqOn`

English:
lemma LSeries_deriv_eqOn
  given: {f : Nat -> Complex}
  proof: deriv_eqOn (isOpen_re_gt_EReal _) fun _ hs => (LSeries_hasDerivAt hs).hasDerivWithinAt

中文:
引理 LSeries_deriv_eqOn
  条件: {f : 自然数 -> Complex}
  证明: deriv_eqOn (isOpen_re_gt_EReal _) fun _ hs => (LSeries_hasDerivAt hs).hasDerivWithinAt

Depends on / 依赖: LSeries_hasDerivAt, deriv_eqOn, hasDerivWithinAt, isOpen_re_gt_EReal
-/
lemma LSeries_deriv_eqOn {f : Nat -> Complex} :
    {s | abscissaOfAbsConv f < s.re}.EqOn (deriv (LSeries f)) (-LSeries (logMul f)) :=
  deriv_eqOn (isOpen_re_gt_EReal _) fun _ hs => (LSeries_hasDerivAt hs).hasDerivWithinAt

/--
lemma `LSeriesSummable_logMul_of_lt_re` / 引理 `LSeriesSummable_logMul_of_lt_re`

English:
lemma LSeriesSummable_logMul_of_lt_re
  given: {f : Nat -> Complex} {s : Complex} (h : abscissaOfAbsConv f < s.re)
  proof: (LSeriesSummable_logMul_and_hasDerivAt h).1

中文:
引理 LSeriesSummable_logMul_of_lt_re
  条件: {f : 自然数 -> Complex} {s : Complex} (h : abscissaOfAbsConv f < s.re)
  证明: (LSeriesSummable_logMul_and_hasDerivAt h).1

Depends on / 依赖: LSeriesSummable_logMul_and_hasDerivAt
-/
lemma LSeriesSummable_logMul_of_lt_re {f : Nat -> Complex} {s : Complex} (h : abscissaOfAbsConv f < s.re) :
    LSeriesSummable (logMul f) s :=
  (LSeriesSummable_logMul_and_hasDerivAt h).1

/-- The abscissa of absolute convergence of the point-wise product of `log` and `f`
is the same as that of `f`. -/
@[simp]
/--
lemma `LSeries.abscissaOfAbsConv_logMul` / 引理 `LSeries.abscissaOfAbsConv_logMul`

English:
lemma LSeries.abscissaOfAbsConv_logMul
  given: {f : Nat -> Complex}
  proof: by
  apply le_antisymm <;> refine abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable' fun s hs => ?_
· exact LSeriesSummable_logMul_of_lt_re by simp [hs]
  · refine (LSeriesSummable_of_abscissaOfAbsConv_lt_re <| by simp [hs])
.norm.of_norm_bounded_eventually_nat (g := fun n => ‖term (logMul f) s n‖) 

中文:
引理 LSeries.abscissaOfAbsConv_logMul
  条件: {f : 自然数 -> Complex}
  证明: by
  apply le_antisymm <;> refine abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable' fun s hs => ?_
· exact LSeriesSummable_logMul_of_lt_re by simp [hs]
  · refine (LSeriesSummable_of_abscissaOfAbsConv_lt_re <| by simp [hs])
.norm.of_norm_bounded_eventually_nat (g := fun n => ‖term (logMul f) s n‖) 

Depends on / 依赖: Filter, Filter.eventually_ge_atTop, LSeriesSummable_logMul_of_lt_re, LSeriesSummable_of_abscissaOfAbsConv_lt_re, Nat.ceil, Real.exp, abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable, eventually_ge_atTop, filter_upwards, le_antisymm, logMul, mul_div_assoc, natCast_log, norm.of_norm_bounded_eventually_nat, norm_mul, norm_real, of_norm_bounded_eventually_nat, term_of_ne_zero
-/
lemma LSeries.abscissaOfAbsConv_logMul {f : Nat -> Complex} :
    abscissaOfAbsConv (logMul f) = abscissaOfAbsConv f := by
  apply le_antisymm <;> refine abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable' fun s hs => ?_
· exact LSeriesSummable_logMul_of_lt_re by simp [hs]
  · refine (LSeriesSummable_of_abscissaOfAbsConv_lt_re <| by simp [hs])
.norm.of_norm_bounded_eventually_nat (g := fun n => ‖term (logMul f) s n‖) ?_
    filter_upwards [Filter.eventually_ge_atTop <| max 1 (Nat.ceil (Real.exp 1))] with n hn
    simp only [term_of_ne_zero (show n != 0 by omega), logMul, norm_mul, mul_div_assoc,
      ← natCast_log, norm_real]
    refine le_mul_of_one_le_left (norm_nonneg _) (.trans ?_ <| Real.le_norm_self _)
simpa using Real.log_le_log (Real.exp_pos 1) Nat.ceil_le.mp (le_max_right _ _).trans hn

/-!
### Higher derivatives of L-series
-/

/-- The abscissa of absolute convergence of the point-wise product of a power of `log` and `f`
is the same as that of `f`. -/
@[simp]
/--
lemma `LSeries.absicssaOfAbsConv_logPowMul` / 引理 `LSeries.absicssaOfAbsConv_logPowMul`

English:
lemma LSeries.absicssaOfAbsConv_logPowMul
  given: {f : Nat -> Complex} {m : Nat}
  proof: by
  induction m with
  | zero => simp
  | succ n ih => simp [ih, Function.iterate_succ', Function.comp_def,
      -Function.comp_apply, -Function.iterate_succ]

中文:
引理 LSeries.absicssaOfAbsConv_logPowMul
  条件: {f : 自然数 -> Complex} {m : 自然数}
  证明: by
  induction m with
  | zero => simp
  | succ n ih => simp [ih, Function.iterate_succ', Function.comp_def,
      -Function.comp_apply, -Function.iterate_succ]

Depends on / 依赖: Function, Function.comp_apply, Function.comp_def, Function.iterate_succ, comp_apply, comp_def, iterate_succ
-/
lemma LSeries.absicssaOfAbsConv_logPowMul {f : Nat -> Complex} {m : Nat} :
    abscissaOfAbsConv (logMul^[m] f) = abscissaOfAbsConv f := by
  induction m with
  | zero => simp
  | succ n ih => simp [ih, Function.iterate_succ', Function.comp_def,
      -Function.comp_apply, -Function.iterate_succ]

/--
lemma `LSeries_iteratedDeriv` / 引理 `LSeries_iteratedDeriv`

English:
lemma LSeries_iteratedDeriv
  given: {f : Nat -> Complex} (m : Nat) {s : Complex} (h : abscissaOfAbsConv f < s.re)
  proof: by
  induction m generalizing s with
  | zero => simp
  | succ m ih =>
    have ih' : {s | abscissaOfAbsConv f < re s}.EqOn (iteratedDeriv m (LSeries f))
        ((-1) ^ m * LSeries (logMul^[m] f)) := fun _ hs => ih hs
    have := derivWithin_congr ih' (ih h)
    simp_rw [derivWithin_of_isOpen (isOp

中文:
引理 LSeries_iteratedDeriv
  条件: {f : 自然数 -> Complex} (m : 自然数) {s : Complex} (h : abscissaOfAbsConv f < s.re)
  证明: by
  induction m generalizing s with
  | zero => simp
  | succ m ih =>
    have ih' : {s | abscissaOfAbsConv f < re s}.EqOn (iteratedDeriv m (LSeries f))
        ((-1) ^ m * LSeries (logMul^[m] f)) := fun _ hs => ih hs
    have := derivWithin_congr ih' (ih h)
    simp_rw [derivWithin_of_isOpen (isOp

Depends on / 依赖: Function, Function.iterate_succ, LSeries, LSeries_deriv, Pi.mul_def, abscissaOfAbsConv, absicssaOfAbsConv_logPowMul, absicssaOfAbsConv_logPowMul.symm, derivWithin_congr, derivWithin_of_isOpen, generalizing, isOpen_re_gt_EReal, iterate_succ, iteratedDeriv, iteratedDeriv_succ, logMul, mul_def, pow_succ, simp_rw
-/
lemma LSeries_iteratedDeriv {f : Nat -> Complex} (m : Nat) {s : Complex} (h : abscissaOfAbsConv f < s.re) :
    iteratedDeriv m (LSeries f) s = (-1) ^ m * LSeries (logMul^[m] f) s := by
  induction m generalizing s with
  | zero => simp
  | succ m ih =>
    have ih' : {s | abscissaOfAbsConv f < re s}.EqOn (iteratedDeriv m (LSeries f))
        ((-1) ^ m * LSeries (logMul^[m] f)) := fun _ hs => ih hs
    have := derivWithin_congr ih' (ih h)
    simp_rw [derivWithin_of_isOpen (isOpen_re_gt_EReal _) h] at this
    rw [iteratedDeriv_succ]; rw [this]
    simp [Pi.mul_def, pow_succ, Function.iterate_succ',
LSeries_deriv absicssaOfAbsConv_logPowMul.symm ▸ h, -Function.iterate_succ]

/-!
### The L-series is holomorphic
-/

/--
lemma `LSeries_differentiableOn` / 引理 `LSeries_differentiableOn`

English:
lemma LSeries_differentiableOn
  given: (f : Nat -> Complex)
  proof: fun _ hz => (LSeries_hasDerivAt hz).differentiableAt.differentiableWithinAt

中文:
引理 LSeries_differentiableOn
  条件: (f : 自然数 -> Complex)
  证明: fun _ hz => (LSeries_hasDerivAt hz).differentiableAt.differentiableWithinAt

Depends on / 依赖: LSeries_hasDerivAt, differentiableAt, differentiableAt.differentiableWithinAt, differentiableWithinAt
-/
lemma LSeries_differentiableOn (f : Nat -> Complex) :
    DifferentiableOn Complex (LSeries f) {s | abscissaOfAbsConv f < s.re} :=
  fun _ hz => (LSeries_hasDerivAt hz).differentiableAt.differentiableWithinAt

/--
lemma `LSeries_analyticOnNhd` / 引理 `LSeries_analyticOnNhd`

English:
lemma LSeries_analyticOnNhd
  given: (f : Nat -> Complex)
  proof: (LSeries_differentiableOn f).analyticOnNhd isOpen_re_gt_EReal _

中文:
引理 LSeries_analyticOnNhd
  条件: (f : 自然数 -> Complex)
  证明: (LSeries_differentiableOn f).analyticOnNhd isOpen_re_gt_EReal _

Depends on / 依赖: LSeries_differentiableOn, analyticOnNhd, isOpen_re_gt_EReal
-/
lemma LSeries_analyticOnNhd (f : Nat -> Complex) :
    AnalyticOnNhd Complex (LSeries f) {s | abscissaOfAbsConv f < s.re} :=
(LSeries_differentiableOn f).analyticOnNhd isOpen_re_gt_EReal _

/--
lemma `LSeries_analyticOn` / 引理 `LSeries_analyticOn`

English:
lemma LSeries_analyticOn
  given: (f : Nat -> Complex)
  proof: (LSeries_analyticOnNhd f).analyticOn

中文:
引理 LSeries_analyticOn
  条件: (f : 自然数 -> Complex)
  证明: (LSeries_analyticOnNhd f).analyticOn

Depends on / 依赖: LSeries_analyticOnNhd, analyticOn
-/
lemma LSeries_analyticOn (f : Nat -> Complex) :
    AnalyticOn Complex (LSeries f) {s | abscissaOfAbsConv f < s.re} :=
  (LSeries_analyticOnNhd f).analyticOn
