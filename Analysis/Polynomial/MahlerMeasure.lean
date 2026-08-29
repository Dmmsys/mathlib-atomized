/-
Copyright (c) 2025 Fabrizio Barroero. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Barroero, Kevin H. Wilson
-/
module

public import Mathlib.Analysis.Analytic.Polynomial
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Multiset
public import Mathlib.Analysis.Polynomial.Norm
public import Mathlib.Analysis.SpecialFunctions.Integrals.PosLogEqCircleAverage
public import Mathlib.Analysis.Convex.Integral
public import Mathlib.Analysis.Polynomial.Fourier

/-!
# Mahler measure of complex polynomials

In this file we define the Mahler measure of a polynomial over `ℂ[X]` and prove some basic
properties.

## Main definitions

- `Polynomial.logMahlerMeasure p`: the logarithmic Mahler measure of a polynomial `p` defined as
  `(2 * π)⁻¹ * ∫ x ∈ (0, 2 * π), log ‖p (e ^ (i * x))‖`.
- `Polynomial.mahlerMeasure p`: the (exponential) Mahler measure of a polynomial `p`, which is equal
  to `e ^ p.logMahlerMeasure` if `p` is nonzero, and `0` otherwise.
- `Polynomial.mapMahlerMeasure p v`: the (exponential) Mahler measure of a polynomial `p` over a
  ring `A` whose coefficients are mapped to `ℂ` via `v : A →+* ℂ`

## Main results

- `Polynomial.mahlerMeasure_mul`: the Mahler measure of the product of two polynomials is the
  product of their Mahler measures.
- `mahlerMeasure_eq_leadingCoeff_mul_prod_roots`: the Mahler measure of a polynomial is the absolute
  value of its leading coefficient times the product of the absolute values of its roots lying
  outside the unit disk.
- `mahlerMeasure_le_sqrt_sum_sq_norm_coeff`: **Landau's inequality** — the Mahler measure is
  at most the ℓ² norm of the coefficient vector.
- `norm_coeff_le_choose_mul_mahlerMeasure_of_one_le_mahlerMeasure`: **Mignotte's coefficient
  bound** — if `f = g * h` with `M(h) ≥ 1`, then `‖g.coeff n‖ ≤ C(deg g, n) · M(f)`.
-/

@[expose] public section

namespace Polynomial

open Real

variable (p : Complex[X])

/--
Definition of `logMahlerMeasure` / `logMahlerMeasure` 的定义

English:
definition logMahlerMeasure
  signature: : Real
  body: circleAverage (fun x => log ‖eval x p‖) 0 1

中文:
定义 logMahlerMeasure
  签名: : 实数
  定义体: circleAverage (fun x => log ‖eval x p‖) 0 1

Depends on / 依赖: circleAverage
-/
noncomputable def logMahlerMeasure : Real := circleAverage (fun x => log ‖eval x p‖) 0 1

/--
theorem `logMahlerMeasure_def` / 定理 `logMahlerMeasure_def`

English:
theorem logMahlerMeasure_def
  statement: p.logMahlerMeasure = circleAverage (fun x => log ‖eval x p‖) 0 1
  proof: rfl

@[simp]

中文:
定理 logMahlerMeasure_def
  结论: p.logMahlerMeasure = circleAverage (fun x => log ‖eval x p‖) 0 1
  证明: rfl

@[simp]
-/
theorem logMahlerMeasure_def : p.logMahlerMeasure = circleAverage (fun x => log ‖eval x p‖) 0 1 :=
  rfl

@[simp]
/--
theorem `logMahlerMeasure_zero` / 定理 `logMahlerMeasure_zero`

English:
theorem logMahlerMeasure_zero
  statement: (0 : Complex[X]).logMahlerMeasure = 0
  proof: by
  simp [logMahlerMeasure_def, circleAverage_def]

@[simp]

中文:
定理 logMahlerMeasure_zero
  结论: (0 : 复形[X]).logMahlerMeasure = 0
  证明: by
  simp [logMahlerMeasure_def, circleAverage_def]

@[simp]

Depends on / 依赖: circleAverage_def, logMahlerMeasure_def
-/
theorem logMahlerMeasure_zero : (0 : Complex[X]).logMahlerMeasure = 0 := by
  simp [logMahlerMeasure_def, circleAverage_def]

@[simp]
/--
theorem `logMahlerMeasure_one` / 定理 `logMahlerMeasure_one`

English:
theorem logMahlerMeasure_one
  statement: (1 : Complex[X]).logMahlerMeasure = 0
  proof: by
  simp [logMahlerMeasure_def, circleAverage_def]

@[simp]

中文:
定理 logMahlerMeasure_one
  结论: (1 : 复形[X]).logMahlerMeasure = 0
  证明: by
  simp [logMahlerMeasure_def, circleAverage_def]

@[simp]

Depends on / 依赖: circleAverage_def, logMahlerMeasure_def
-/
theorem logMahlerMeasure_one : (1 : Complex[X]).logMahlerMeasure = 0 := by
  simp [logMahlerMeasure_def, circleAverage_def]

@[simp]
/--
theorem `logMahlerMeasure_const` / 定理 `logMahlerMeasure_const`

English:
theorem logMahlerMeasure_const
  given: (z : Complex)
  statement: (C z).logMahlerMeasure = log ‖z‖
  proof: by
  simp [logMahlerMeasure_def, circleAverage_def, mul_assoc]

@[simp]

中文:
定理 logMahlerMeasure_const
  条件: (z : 复形)
  结论: (C z).logMahlerMeasure = log ‖z‖
  证明: by
  simp [logMahlerMeasure_def, circleAverage_def, mul_assoc]

@[simp]

Depends on / 依赖: Equivalence, Equivalence.congrLeft, F.asEquivalence, IsEquivalence, asEquivalence, circleAverage_def, congrLeft, inverse, logMahlerMeasure_def, mul_assoc
-/
theorem logMahlerMeasure_const (z : Complex) : (C z).logMahlerMeasure = log ‖z‖ := by
  simp [logMahlerMeasure_def, circleAverage_def, mul_assoc]

@[simp]
/--
theorem `logMahlerMeasure_X` / 定理 `logMahlerMeasure_X`

English:
theorem logMahlerMeasure_X
  statement: (X : Complex[X]).logMahlerMeasure = 0
  proof: by
  simp [logMahlerMeasure_def, circleAverage_def]

@[simp]

中文:
定理 logMahlerMeasure_X
  结论: (X : 复形[X]).logMahlerMeasure = 0
  证明: by
  simp [logMahlerMeasure_def, circleAverage_def]

@[simp]

Depends on / 依赖: Equivalence, Equivalence.congrRight, F.asEquivalence, IsEquivalence, asEquivalence, circleAverage_def, congrRight, functor, logMahlerMeasure_def
-/
theorem logMahlerMeasure_X : (X : Complex[X]).logMahlerMeasure = 0 := by
  simp [logMahlerMeasure_def, circleAverage_def]

@[simp]
/--
theorem `logMahlerMeasure_monomial` / 定理 `logMahlerMeasure_monomial`

English:
theorem logMahlerMeasure_monomial
  given: (n : Nat) (z : Complex)
  statement: (monomial n z).logMahlerMeasure = log ‖z‖
  proof: by
  simp [logMahlerMeasure_def, circleAverage_def, mul_assoc]

中文:
定理 logMahlerMeasure_monomial
  条件: (n : 自然数) (z : 复形)
  结论: (monomial n z).logMahlerMeasure = log ‖z‖
  证明: by
  simp [logMahlerMeasure_def, circleAverage_def, mul_assoc]

Depends on / 依赖: circleAverage_def, logMahlerMeasure_def, mul_assoc
-/
theorem logMahlerMeasure_monomial (n : Nat) (z : Complex) : (monomial n z).logMahlerMeasure = log ‖z‖ := by
  simp [logMahlerMeasure_def, circleAverage_def, mul_assoc]

/--
Definition of `mahlerMeasure` / `mahlerMeasure` 的定义

English:
definition mahlerMeasure
  signature: : Real
  body: if p != 0 then exp (p.logMahlerMeasure) else 0

中文:
定义 mahlerMeasure
  签名: : 实数
  定义体: if p != 0 then exp (p.logMahlerMeasure) else 0

Depends on / 依赖: logMahlerMeasure, p.logMahlerMeasure
-/
noncomputable def mahlerMeasure : Real := if p != 0 then exp (p.logMahlerMeasure) else 0

variable {p} in
/--
theorem `mahlerMeasure_def_of_ne_zero` / 定理 `mahlerMeasure_def_of_ne_zero`

English:
theorem mahlerMeasure_def_of_ne_zero
  given: (hp : p != 0)
  statement: p.mahlerMeasure =
  proof: by
  simp [mahlerMeasure, hp, logMahlerMeasure_def, circleAverage_def]

中文:
定理 mahlerMeasure_def_of_ne_zero
  条件: (hp : p != 0)
  结论: p.mahlerMeasure =
  证明: by
  simp [mahlerMeasure, hp, logMahlerMeasure_def, circleAverage_def]

Depends on / 依赖: circleAverage_def, logMahlerMeasure_def, mahlerMeasure
-/
theorem mahlerMeasure_def_of_ne_zero (hp : p != 0) : p.mahlerMeasure =
    exp ((2 * π)⁻¹ * ∫ (x : Real) in (0)..(2 * π), log ‖eval (circleMap 0 1 x) p‖) := by
  simp [mahlerMeasure, hp, logMahlerMeasure_def, circleAverage_def]

variable {p} in
/--
theorem `logMahlerMeasure_eq_log_MahlerMeasure` / 定理 `logMahlerMeasure_eq_log_MahlerMeasure`

English:
theorem logMahlerMeasure_eq_log_MahlerMeasure
  statement: p.logMahlerMeasure = log p.mahlerMeasure
  proof: by
  rw [mahlerMeasure]
  split_ifs <;> simp_all [logMahlerMeasure_def, circleAverage_def]

@[simp]

中文:
定理 logMahlerMeasure_eq_log_MahlerMeasure
  结论: p.logMahlerMeasure = log p.mahlerMeasure
  证明: by
  rw [mahlerMeasure]
  split_ifs <;> simp_all [logMahlerMeasure_def, circleAverage_def]

@[simp]

Depends on / 依赖: circleAverage_def, logMahlerMeasure_def, mahlerMeasure, split_ifs
-/
theorem logMahlerMeasure_eq_log_MahlerMeasure : p.logMahlerMeasure = log p.mahlerMeasure := by
  rw [mahlerMeasure]
  split_ifs <;> simp_all [logMahlerMeasure_def, circleAverage_def]

@[simp]
/--
theorem `mahlerMeasure_zero` / 定理 `mahlerMeasure_zero`

English:
theorem mahlerMeasure_zero
  statement: (0 : Complex[X]).mahlerMeasure = 0
  proof: by simp [mahlerMeasure]

@[simp]

中文:
定理 mahlerMeasure_zero
  结论: (0 : 复形[X]).mahlerMeasure = 0
  证明: by simp [mahlerMeasure]

@[simp]

Depends on / 依赖: mahlerMeasure
-/
theorem mahlerMeasure_zero : (0 : Complex[X]).mahlerMeasure = 0 := by simp [mahlerMeasure]

@[simp]
/--
theorem `mahlerMeasure_one` / 定理 `mahlerMeasure_one`

English:
theorem mahlerMeasure_one
  statement: (1 : Complex[X]).mahlerMeasure = 1
  proof: by simp [mahlerMeasure]

@[simp]

中文:
定理 mahlerMeasure_one
  结论: (1 : 复形[X]).mahlerMeasure = 1
  证明: by simp [mahlerMeasure]

@[simp]

Depends on / 依赖: mahlerMeasure
-/
theorem mahlerMeasure_one : (1 : Complex[X]).mahlerMeasure = 1 := by simp [mahlerMeasure]

@[simp]
/--
theorem `mahlerMeasure_const` / 定理 `mahlerMeasure_const`

English:
theorem mahlerMeasure_const
  given: (z : Complex)
  statement: (C z).mahlerMeasure = ‖z‖
  proof: by
  simp only [mahlerMeasure, ne_eq, map_eq_zero, logMahlerMeasure_const, ite_not]
  split_ifs with h
  · simp [h]
  · simp [h, exp_log]

中文:
定理 mahlerMeasure_const
  条件: (z : 复形)
  结论: (C z).mahlerMeasure = ‖z‖
  证明: by
  simp only [mahlerMeasure, ne_eq, map_eq_zero, logMahlerMeasure_const, ite_not]
  split_ifs with h
  · simp [h]
  · simp [h, exp_log]

Depends on / 依赖: exp_log, ite_not, logMahlerMeasure_const, mahlerMeasure, map_eq_zero, ne_eq, split_ifs
-/
theorem mahlerMeasure_const (z : Complex) : (C z).mahlerMeasure = ‖z‖ := by
  simp only [mahlerMeasure, ne_eq, map_eq_zero, logMahlerMeasure_const, ite_not]
  split_ifs with h
  · simp [h]
  · simp [h, exp_log]

/--
theorem `mahlerMeasure_nonneg` / 定理 `mahlerMeasure_nonneg`

English:
theorem mahlerMeasure_nonneg
  statement: 0 <= p.mahlerMeasure
  proof: by
  by_cases hp : p = 0 <;> simp [hp, mahlerMeasure_def_of_ne_zero, exp_nonneg]

中文:
定理 mahlerMeasure_nonneg
  结论: 0 <= p.mahlerMeasure
  证明: by
  by_cases hp : p = 0 <;> simp [hp, mahlerMeasure_def_of_ne_zero, exp_nonneg]

Depends on / 依赖: exp_nonneg, mahlerMeasure_def_of_ne_zero
-/
theorem mahlerMeasure_nonneg : 0 <= p.mahlerMeasure := by
  by_cases hp : p = 0 <;> simp [hp, mahlerMeasure_def_of_ne_zero, exp_nonneg]

variable {p} in
/--
theorem `mahlerMeasure_pos_of_ne_zero` / 定理 `mahlerMeasure_pos_of_ne_zero`

English:
theorem mahlerMeasure_pos_of_ne_zero
  given: (hp : p != 0)
  statement: 0 < p.mahlerMeasure
  proof: by
  grind [exp_pos, mahlerMeasure_def_of_ne_zero]

@[simp]

中文:
定理 mahlerMeasure_pos_of_ne_zero
  条件: (hp : p != 0)
  结论: 0 < p.mahlerMeasure
  证明: by
  grind [exp_pos, mahlerMeasure_def_of_ne_zero]

@[simp]

Depends on / 依赖: exp_pos, mahlerMeasure_def_of_ne_zero
-/
theorem mahlerMeasure_pos_of_ne_zero (hp : p != 0) : 0 < p.mahlerMeasure := by
  grind [exp_pos, mahlerMeasure_def_of_ne_zero]

@[simp]
/--
theorem `mahlerMeasure_eq_zero_iff` / 定理 `mahlerMeasure_eq_zero_iff`

English:
theorem mahlerMeasure_eq_zero_iff
  statement: p.mahlerMeasure = 0 ↔ p = 0
  proof: by
  refine ⟨?_, by simp_all [mahlerMeasure_zero]⟩
  contrapose
  exact fun h => by simp [mahlerMeasure_def_of_ne_zero h]

中文:
定理 mahlerMeasure_eq_zero_iff
  结论: p.mahlerMeasure = 0 ↔ p = 0
  证明: by
  refine ⟨?_, by simp_all [mahlerMeasure_zero]⟩
  contrapose
  exact fun h => by simp [mahlerMeasure_def_of_ne_zero h]

Depends on / 依赖: contrapose, mahlerMeasure_def_of_ne_zero, mahlerMeasure_zero
-/
theorem mahlerMeasure_eq_zero_iff : p.mahlerMeasure = 0 ↔ p = 0 := by
  refine ⟨?_, by simp_all [mahlerMeasure_zero]⟩
  contrapose
  exact fun h => by simp [mahlerMeasure_def_of_ne_zero h]

/--
lemma `intervalIntegrable_mahlerMeasure` / 引理 `intervalIntegrable_mahlerMeasure`

English:
lemma intervalIntegrable_mahlerMeasure
  proof: by
  rw [← circleIntegrable_def fun z => log ‖p.eval z‖]
  exact (analyticOnNhd_id.aeval_polynomial p).meromorphicOn.circleIntegrable_log_norm

中文:
引理 interval整数egrable_mahlerMeasure
  证明: by
  rw [← circleIntegrable_def fun z => log ‖p.eval z‖]
  exact (analyticOnNhd_id.aeval_polynomial p).meromorphicOn.circleIntegrable_log_norm

Depends on / 依赖: aeval_polynomial, analyticOnNhd_id, analyticOnNhd_id.aeval_polynomial, circleIntegrable_def, circleIntegrable_log_norm, meromorphicOn, meromorphicOn.circleIntegrable_log_norm, p.eval
-/
lemma intervalIntegrable_mahlerMeasure :
    IntervalIntegrable (fun x => log ‖p.eval (circleMap 0 1 x)‖) MeasureTheory.volume 0 (2 * π) := by
  rw [← circleIntegrable_def fun z => log ‖p.eval z‖]
  exact (analyticOnNhd_id.aeval_polynomial p).meromorphicOn.circleIntegrable_log_norm

/-! The Mahler measure of the product of two polynomials is the product of their Mahler measures -/
open intervalIntegral in
/--
theorem `mahlerMeasure_mul` / 定理 `mahlerMeasure_mul`

English:
theorem mahlerMeasure_mul
  given: (p q : Complex[X])
  proof: by
  by_cases hpq : p * q = 0
  · simpa [hpq, mahlerMeasure_zero] using mul_eq_zero.mp hpq
  rw [mul_eq_zero]; rw [not_or] at hpq
  simp only [mahlerMeasure, ne_eq, mul_eq_zero, hpq, or_self, not_false_eq_true, ↓reduceIte,
    logMahlerMeasure, eval_mul, Complex.norm_mul, circleAverage_def, mul_inv_

中文:
定理 mahlerMeasure_mul
  条件: (p q : 复形[X])
  证明: by
  by_cases hpq : p * q = 0
  · simpa [hpq, mahlerMeasure_zero] using mul_eq_zero.mp hpq
  rw [mul_eq_zero]; rw [not_or] at hpq
  simp only [mahlerMeasure, ne_eq, mul_eq_zero, hpq, or_self, not_false_eq_true, ↓reduceIte,
    logMahlerMeasure, eval_mul, Complex.norm_mul, circleAverage_def, mul_inv_

Depends on / 依赖: Complex.norm_mul, MeasureTheory, MeasureTheory.ae_iff, Set.Fi, ae_iff, circleAverage_def, eval_mul, exp_add, integral_add, integral_congr_ae, intervalIntegrable_mahlerMeasure, left_distrib, logMahlerMeasure, mahlerMeasure, mahlerMeasure_zero, mul_eq_zero, mul_eq_zero.mp, mul_inv_rev, ne_eq, norm_mul
-/
theorem mahlerMeasure_mul (p q : Complex[X]) :
    (p * q).mahlerMeasure = p.mahlerMeasure * q.mahlerMeasure := by
  by_cases hpq : p * q = 0
  · simpa [hpq, mahlerMeasure_zero] using mul_eq_zero.mp hpq
  rw [mul_eq_zero]; rw [not_or] at hpq
  simp only [mahlerMeasure, ne_eq, mul_eq_zero, hpq, or_self, not_false_eq_true, ↓reduceIte,
    logMahlerMeasure, eval_mul, Complex.norm_mul, circleAverage_def, mul_inv_rev, smul_eq_mul]
  rw [← exp_add]; rw [← left_distrib]
  congr
  rw [← integral_add p.intervalIntegrable_mahlerMeasure q.intervalIntegrable_mahlerMeasure]
  apply integral_congr_ae
  rw [MeasureTheory.ae_iff]
  apply Set.Finite.measure_zero _ MeasureTheory.volume
  simp only [Classical.not_imp]
apply Set.Finite.of_finite_image (f := circleMap 0 1) _
    (injOn_circleMap_of_abs_sub_le one_ne_zero (by simp [le_of_eq, pi_nonneg])).mono (fun _ h => h.1)
  apply (p * q).roots.finite_toSet.subset
  rintro _ ⟨_, ⟨_, h⟩, _⟩
  contrapose h
  simp_all [log_mul]

@[simp]
/--
theorem `prod_mahlerMeasure_eq_mahlerMeasure_prod` / 定理 `prod_mahlerMeasure_eq_mahlerMeasure_prod`

English:
theorem prod_mahlerMeasure_eq_mahlerMeasure_prod
  given: (s : Multiset Complex[X])
  proof: by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons _ _ ih => simp [mahlerMeasure_mul, ih]

中文:
定理 prod_mahlerMeasure_eq_mahlerMeasure_prod
  条件: (s : Multiset 复形[X])
  证明: by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons _ _ ih => simp [mahlerMeasure_mul, ih]

Depends on / 依赖: Multiset, Multiset.induction_on, induction_on, mahlerMeasure_mul
-/
theorem prod_mahlerMeasure_eq_mahlerMeasure_prod (s : Multiset Complex[X]) :
    (s.prod).mahlerMeasure = (s.map (fun p => p.mahlerMeasure)).prod := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons _ _ ih => simp [mahlerMeasure_mul, ih]

/--
theorem `logMahlerMeasure_mul_eq_add_logMahlerMeasure` / 定理 `logMahlerMeasure_mul_eq_add_logMahlerMeasure`

English:
theorem logMahlerMeasure_mul_eq_add_logMahlerMeasure
  given: {p q : Complex[X]} (hpq : p * q != 0)
  proof: by
  simp_all [logMahlerMeasure_eq_log_MahlerMeasure, mahlerMeasure_mul, log_mul]

中文:
定理 logMahlerMeasure_mul_eq_add_logMahlerMeasure
  条件: {p q : 复形[X]} (hpq : p * q != 0)
  证明: by
  simp_all [logMahlerMeasure_eq_log_MahlerMeasure, mahlerMeasure_mul, log_mul]

Depends on / 依赖: logMahlerMeasure_eq_log_MahlerMeasure, log_mul, mahlerMeasure_mul
-/
theorem logMahlerMeasure_mul_eq_add_logMahlerMeasure {p q : Complex[X]} (hpq : p * q != 0) :
    (p * q).logMahlerMeasure = p.logMahlerMeasure + q.logMahlerMeasure := by
  simp_all [logMahlerMeasure_eq_log_MahlerMeasure, mahlerMeasure_mul, log_mul]

/--
theorem `logMahlerMeasure_C_mul` / 定理 `logMahlerMeasure_C_mul`

English:
theorem logMahlerMeasure_C_mul
  given: {a : Complex} (ha : a != 0) {p : Complex[X]} (hp : p != 0)
  proof: by
  rw [logMahlerMeasure_mul_eq_add_logMahlerMeasure (by simp [ha]; rw [hp]), logMahlerMeasure_const]

中文:
定理 logMahlerMeasure_C_mul
  条件: {a : 复形} (ha : a != 0) {p : 复形[X]} (hp : p != 0)
  证明: by
  rw [logMahlerMeasure_mul_eq_add_logMahlerMeasure (by simp [ha]; rw [hp]), logMahlerMeasure_const]

Depends on / 依赖: logMahlerMeasure_const, logMahlerMeasure_mul_eq_add_logMahlerMeasure
-/
theorem logMahlerMeasure_C_mul {a : Complex} (ha : a != 0) {p : Complex[X]} (hp : p != 0) :
    (C a * p).logMahlerMeasure = log ‖a‖ + p.logMahlerMeasure := by
  rw [logMahlerMeasure_mul_eq_add_logMahlerMeasure (by simp [ha]; rw [hp]), logMahlerMeasure_const]

open MeromorphicOn Metric in
/-- The logarithmic Mahler measure of `X - C z` is the `log⁺` of the absolute value of `z`. -/
@[simp]
/--
theorem `logMahlerMeasure_X_sub_C` / 定理 `logMahlerMeasure_X_sub_C`

English:
theorem logMahlerMeasure_X_sub_C
  given: (z : Complex)
  statement: (X - C z).logMahlerMeasure = log⁺ ‖z‖
  proof: by
  simp [logMahlerMeasure_def]

@[simp]

中文:
定理 logMahlerMeasure_X_sub_C
  条件: (z : 复形)
  结论: (X - C z).logMahlerMeasure = log⁺ ‖z‖
  证明: by
  simp [logMahlerMeasure_def]

@[simp]

Depends on / 依赖: logMahlerMeasure_def
-/
theorem logMahlerMeasure_X_sub_C (z : Complex) : (X - C z).logMahlerMeasure = log⁺ ‖z‖ := by
  simp [logMahlerMeasure_def]

@[simp]
/--
theorem `logMahlerMeasure_X_add_C` / 定理 `logMahlerMeasure_X_add_C`

English:
theorem logMahlerMeasure_X_add_C
  given: (z : Complex)
  statement: (X + C z).logMahlerMeasure = log⁺ ‖z‖
  proof: by
  simp [← sub_neg_eq_add, ← map_neg]

中文:
定理 logMahlerMeasure_X_add_C
  条件: (z : 复形)
  结论: (X + C z).logMahlerMeasure = log⁺ ‖z‖
  证明: by
  simp [← sub_neg_eq_add, ← map_neg]

Depends on / 依赖: map_neg, sub_neg_eq_add
-/
theorem logMahlerMeasure_X_add_C (z : Complex) : (X + C z).logMahlerMeasure = log⁺ ‖z‖ := by
  simp [← sub_neg_eq_add, ← map_neg]

/--
theorem `logMahlerMeasure_C_mul_X_add_C` / 定理 `logMahlerMeasure_C_mul_X_add_C`

English:
theorem logMahlerMeasure_C_mul_X_add_C
  given: {a : Complex} (ha : a != 0) (b : Complex)
  proof: by
  rw [show C a * X + C b = C a * (X + C (a⁻¹ * b)) by simp [mul_add]; rw [← map_mul]; rw [ha],
    logMahlerMeasure_C_mul ha (X_add_C_ne_zero (a⁻¹ * b)), logMahlerMeasure_X_add_C]

中文:
定理 logMahlerMeasure_C_mul_X_add_C
  条件: {a : 复形} (ha : a != 0) (b : 复形)
  证明: by
  rw [show C a * X + C b = C a * (X + C (a⁻¹ * b)) by simp [mul_add]; rw [← map_mul]; rw [ha],
    logMahlerMeasure_C_mul ha (X_add_C_ne_zero (a⁻¹ * b)), logMahlerMeasure_X_add_C]

Depends on / 依赖: X_add_C_ne_zero, logMahlerMeasure_C_mul, logMahlerMeasure_X_add_C, map_mul, mul_add
-/
theorem logMahlerMeasure_C_mul_X_add_C {a : Complex} (ha : a != 0) (b : Complex) :
    (C a * X + C b).logMahlerMeasure = log ‖a‖ + log⁺ ‖a⁻¹ * b‖ := by
  rw [show C a * X + C b = C a * (X + C (a⁻¹ * b)) by simp [mul_add]; rw [← map_mul]; rw [ha],
    logMahlerMeasure_C_mul ha (X_add_C_ne_zero (a⁻¹ * b)), logMahlerMeasure_X_add_C]

/--
theorem `logMahlerMeasure_of_degree_eq_one` / 定理 `logMahlerMeasure_of_degree_eq_one`

English:
theorem logMahlerMeasure_of_degree_eq_one
  given: {p : Complex[X]} (h : p.degree = 1)
  statement: p.logMahlerMeasure =
  proof: by
  rw [eq_X_add_C_of_degree_le_one (le_of_eq h)]
  simp [logMahlerMeasure_C_mul_X_add_C (show p.coeff 1 != 0 by exact coeff_ne_zero_of_eq_degree h)]

中文:
定理 logMahlerMeasure_of_degree_eq_one
  条件: {p : 复形[X]} (h : p.degree = 1)
  结论: p.logMahlerMeasure =
  证明: by
  rw [eq_X_add_C_of_degree_le_one (le_of_eq h)]
  simp [logMahlerMeasure_C_mul_X_add_C (show p.coeff 1 != 0 by exact coeff_ne_zero_of_eq_degree h)]

Depends on / 依赖: coeff_ne_zero_of_eq_degree, eq_X_add_C_of_degree_le_one, le_of_eq, logMahlerMeasure_C_mul_X_add_C, p.coeff
-/
theorem logMahlerMeasure_of_degree_eq_one {p : Complex[X]} (h : p.degree = 1) : p.logMahlerMeasure =
    log ‖p.coeff 1‖ + log⁺ ‖(p.coeff 1)⁻¹ * p.coeff 0‖ := by
  rw [eq_X_add_C_of_degree_le_one (le_of_eq h)]
  simp [logMahlerMeasure_C_mul_X_add_C (show p.coeff 1 != 0 by exact coeff_ne_zero_of_eq_degree h)]

/-- The Mahler measure of `X - C z` equals `max 1 ‖z‖`. -/
@[simp]
/--
theorem `mahlerMeasure_X_sub_C` / 定理 `mahlerMeasure_X_sub_C`

English:
theorem mahlerMeasure_X_sub_C
  given: (z : Complex)
  statement: (X - C z).mahlerMeasure = max 1 ‖z‖
  proof: by
  have := logMahlerMeasure_X_sub_C z
  rw [logMahlerMeasure_eq_log_MahlerMeasure] at this
  apply_fun exp at this
  rwa [posLog_eq_log_max_one (norm_nonneg z),
    exp_log (mahlerMeasure_pos_of_ne_zero <| X_sub_C_ne_zero z),
    exp_log (lt_of_lt_of_le zero_lt_one <| le_max_left 1 ‖z‖)] at this



中文:
定理 mahlerMeasure_X_sub_C
  条件: (z : 复形)
  结论: (X - C z).mahlerMeasure = 最大值 1 ‖z‖
  证明: by
  have := logMahlerMeasure_X_sub_C z
  rw [logMahlerMeasure_eq_log_MahlerMeasure] at this
  apply_fun exp at this
  rwa [posLog_eq_log_max_one (norm_nonneg z),
    exp_log (mahlerMeasure_pos_of_ne_zero <| X_sub_C_ne_zero z),
    exp_log (lt_of_lt_of_le zero_lt_one <| le_max_left 1 ‖z‖)] at this



Depends on / 依赖: X_sub_C_ne_zero, apply_fun, exp_log, le_max_left, logMahlerMeasure_X_sub_C, logMahlerMeasure_eq_log_MahlerMeasure, lt_of_lt_of_le, mahlerMeasure_pos_of_ne_zero, norm_nonneg, posLog_eq_log_max_one, zero_lt_one
-/
theorem mahlerMeasure_X_sub_C (z : Complex) : (X - C z).mahlerMeasure = max 1 ‖z‖ := by
  have := logMahlerMeasure_X_sub_C z
  rw [logMahlerMeasure_eq_log_MahlerMeasure] at this
  apply_fun exp at this
  rwa [posLog_eq_log_max_one (norm_nonneg z),
    exp_log (mahlerMeasure_pos_of_ne_zero <| X_sub_C_ne_zero z),
    exp_log (lt_of_lt_of_le zero_lt_one <| le_max_left 1 ‖z‖)] at this

@[simp]
/--
theorem `mahlerMeasure_X_add_C` / 定理 `mahlerMeasure_X_add_C`

English:
theorem mahlerMeasure_X_add_C
  given: (z : Complex)
  statement: (X + C z).mahlerMeasure = max 1 ‖z‖
  proof: by
  simp [← sub_neg_eq_add, ← map_neg]

@[simp]

中文:
定理 mahlerMeasure_X_add_C
  条件: (z : 复形)
  结论: (X + C z).mahlerMeasure = 最大值 1 ‖z‖
  证明: by
  simp [← sub_neg_eq_add, ← map_neg]

@[simp]

Depends on / 依赖: map_neg, sub_neg_eq_add
-/
theorem mahlerMeasure_X_add_C (z : Complex) : (X + C z).mahlerMeasure = max 1 ‖z‖ := by
  simp [← sub_neg_eq_add, ← map_neg]

@[simp]
/--
theorem `mahlerMeasure_C_mul_X_add_C` / 定理 `mahlerMeasure_C_mul_X_add_C`

English:
theorem mahlerMeasure_C_mul_X_add_C
  given: {a : Complex} (ha : a != 0) (b : Complex)
  proof: by
  simp only [show C a * X + C b = C a * (X + C (a⁻¹ * b)) by simp [mul_add, ← map_mul, ha],
    mahlerMeasure_mul, mahlerMeasure_const, ← coe_nnnorm, mahlerMeasure_X_add_C]
  norm_cast
  simp [mul_max, ha]

中文:
定理 mahlerMeasure_C_mul_X_add_C
  条件: {a : 复形} (ha : a != 0) (b : 复形)
  证明: by
  simp only [show C a * X + C b = C a * (X + C (a⁻¹ * b)) by simp [mul_add, ← map_mul, ha],
    mahlerMeasure_mul, mahlerMeasure_const, ← coe_nnnorm, mahlerMeasure_X_add_C]
  norm_cast
  simp [mul_max, ha]

Depends on / 依赖: coe_nnnorm, mahlerMeasure_X_add_C, mahlerMeasure_const, mahlerMeasure_mul, map_mul, mul_add, mul_max
-/
theorem mahlerMeasure_C_mul_X_add_C {a : Complex} (ha : a != 0) (b : Complex) :
    (C a * X + C b).mahlerMeasure = max ‖a‖ ‖b‖ := by
  simp only [show C a * X + C b = C a * (X + C (a⁻¹ * b)) by simp [mul_add, ← map_mul, ha],
    mahlerMeasure_mul, mahlerMeasure_const, ← coe_nnnorm, mahlerMeasure_X_add_C]
  norm_cast
  simp [mul_max, ha]

/--
theorem `mahlerMeasure_of_degree_eq_one` / 定理 `mahlerMeasure_of_degree_eq_one`

English:
theorem mahlerMeasure_of_degree_eq_one
  given: {p : Complex[X]} (h : p.degree = 1)
  proof: by
  rw [eq_X_add_C_of_degree_le_one (le_of_eq h)]
  simp [mahlerMeasure_C_mul_X_add_C (show p.coeff 1 != 0 by exact coeff_ne_zero_of_eq_degree h)]

中文:
定理 mahlerMeasure_of_degree_eq_one
  条件: {p : 复形[X]} (h : p.degree = 1)
  证明: by
  rw [eq_X_add_C_of_degree_le_one (le_of_eq h)]
  simp [mahlerMeasure_C_mul_X_add_C (show p.coeff 1 != 0 by exact coeff_ne_zero_of_eq_degree h)]

Depends on / 依赖: coeff_ne_zero_of_eq_degree, eq_X_add_C_of_degree_le_one, le_of_eq, mahlerMeasure_C_mul_X_add_C, p.coeff
-/
theorem mahlerMeasure_of_degree_eq_one {p : Complex[X]} (h : p.degree = 1) :
    p.mahlerMeasure = max ‖p.coeff 1‖ ‖p.coeff 0‖ := by
  rw [eq_X_add_C_of_degree_le_one (le_of_eq h)]
  simp [mahlerMeasure_C_mul_X_add_C (show p.coeff 1 != 0 by exact coeff_ne_zero_of_eq_degree h)]

/--
theorem `logMahlerMeasure_eq_log_leadingCoeff_add_sum_log_roots` / 定理 `logMahlerMeasure_eq_log_leadingCoeff_add_sum_log_roots`

English:
theorem logMahlerMeasure_eq_log_leadingCoeff_add_sum_log_roots
  given: (p : Complex[X])
  statement: p.logMahlerMeasure =
  proof: by
  by_cases hp : p = 0
  · simp [hp]
  have : forall x in Multiset.map (fun x => max 1 ‖x‖) p.roots, x != 0 := by grind [Multiset.mem_map]
  nth_rw 1 [(IsAlgClosed.splits p).eq_prod_roots]
  rw [logMahlerMeasure_mul_eq_add_logMahlerMeasure (by simp [hp]; rw [X_sub_C_ne_zero])]
  simp [posLog_eq_lo

中文:
定理 logMahlerMeasure_eq_log_leadingCoeff_add_sum_log_roots
  条件: (p : 复形[X])
  结论: p.logMahlerMeasure =
  证明: by
  by_cases hp : p = 0
  · simp [hp]
  have : forall x in Multiset.map (fun x => max 1 ‖x‖) p.roots, x != 0 := by grind [Multiset.mem_map]
  nth_rw 1 [(IsAlgClosed.splits p).eq_prod_roots]
  rw [logMahlerMeasure_mul_eq_add_logMahlerMeasure (by simp [hp]; rw [X_sub_C_ne_zero])]
  simp [posLog_eq_lo

Depends on / 依赖: IsAlgClosed, IsAlgClosed.splits, Multiset, Multiset.map, Multiset.mem_map, X_sub_C_ne_zero, eq_prod_roots, logMahlerMeasure_eq_log_MahlerMeasure, logMahlerMeasure_mul_eq_add_logMahlerMeasure, log_multiset_prod, mem_map, nth_rw, p.roots, posLog_eq_log_max_one, prod_mahlerMeasure_eq_mahlerMeasure_prod, splits
-/
theorem logMahlerMeasure_eq_log_leadingCoeff_add_sum_log_roots (p : Complex[X]) : p.logMahlerMeasure =
    log ‖p.leadingCoeff‖ + (p.roots.map (fun a => log⁺ ‖a‖)).sum := by
  by_cases hp : p = 0
  · simp [hp]
  have : forall x in Multiset.map (fun x => max 1 ‖x‖) p.roots, x != 0 := by grind [Multiset.mem_map]
  nth_rw 1 [(IsAlgClosed.splits p).eq_prod_roots]
  rw [logMahlerMeasure_mul_eq_add_logMahlerMeasure (by simp [hp]; rw [X_sub_C_ne_zero])]
  simp [posLog_eq_log_max_one, logMahlerMeasure_eq_log_MahlerMeasure,
    prod_mahlerMeasure_eq_mahlerMeasure_prod, log_multiset_prod this]

/--
theorem `mahlerMeasure_eq_leadingCoeff_mul_prod_roots` / 定理 `mahlerMeasure_eq_leadingCoeff_mul_prod_roots`

English:
theorem mahlerMeasure_eq_leadingCoeff_mul_prod_roots
  given: (p : Complex[X])
  statement: p.mahlerMeasure =
  proof: by
  by_cases hp : p = 0
  · simp [hp]
  have := logMahlerMeasure_eq_log_leadingCoeff_add_sum_log_roots p
  rw [logMahlerMeasure_eq_log_MahlerMeasure] at this
  apply_fun exp at this
  rw [exp_add]; rw [exp_log <| mahlerMeasure_pos_of_ne_zero hp]; rw [exp_log norm_pos_iff.mpr leadingCoeff_ne_zero.mp

中文:
定理 mahlerMeasure_eq_leadingCoeff_mul_prod_roots
  条件: (p : 复形[X])
  结论: p.mahlerMeasure =
  证明: by
  by_cases hp : p = 0
  · simp [hp]
  have := logMahlerMeasure_eq_log_leadingCoeff_add_sum_log_roots p
  rw [logMahlerMeasure_eq_log_MahlerMeasure] at this
  apply_fun exp at this
  rw [exp_add]; rw [exp_log <| mahlerMeasure_pos_of_ne_zero hp]; rw [exp_log norm_pos_iff.mpr leadingCoeff_ne_zero.mp

Depends on / 依赖: apply_fun, exp_add, exp_log, exp_multiset_sum, leadingCoeff_ne_zero, leadingCoeff_ne_zero.mpr, logMahlerMeasure_eq_log_MahlerMeasure, logMahlerMeasure_eq_log_leadingCoeff_add_sum_log_roots, mahlerMeasure_pos_of_ne_zero, norm_pos_iff, norm_pos_iff.mpr, posLog_eq_log_max_one
-/
theorem mahlerMeasure_eq_leadingCoeff_mul_prod_roots (p : Complex[X]) : p.mahlerMeasure =
    ‖p.leadingCoeff‖ * (p.roots.map (fun a => max 1 ‖a‖)).prod := by
  by_cases hp : p = 0
  · simp [hp]
  have := logMahlerMeasure_eq_log_leadingCoeff_add_sum_log_roots p
  rw [logMahlerMeasure_eq_log_MahlerMeasure] at this
  apply_fun exp at this
  rw [exp_add]; rw [exp_log <| mahlerMeasure_pos_of_ne_zero hp]; rw [exp_log norm_pos_iff.mpr leadingCoeff_ne_zero.mpr hp] at this
  simp [this, exp_multiset_sum, posLog_eq_log_max_one, exp_log]


/--
lemma `one_le_prod_max_one_norm_roots` / 引理 `one_le_prod_max_one_norm_roots`

English:
lemma one_le_prod_max_one_norm_roots
  given: (p : Complex[X])
  statement: 1 <= (p.roots.map (fun a => max 1 ‖a‖)).prod
  proof: by
  grind [Multiset.one_le_prod, Multiset.mem_map]

中文:
引理 one_le_prod_max_one_norm_roots
  条件: (p : 复形[X])
  结论: 1 <= (p.roots.map (fun a => 最大值 1 ‖a‖)).乘积
  证明: by
  grind [Multiset.one_le_prod, Multiset.mem_map]

Depends on / 依赖: Multiset, Multiset.mem_map, Multiset.one_le_prod, mem_map, one_le_prod
-/
lemma one_le_prod_max_one_norm_roots (p : Complex[X]) : 1 <= (p.roots.map (fun a => max 1 ‖a‖)).prod := by
  grind [Multiset.one_le_prod, Multiset.mem_map]

/--
lemma `leadingCoeff_le_mahlerMeasure` / 引理 `leadingCoeff_le_mahlerMeasure`

English:
lemma leadingCoeff_le_mahlerMeasure
  given: (p : Complex[X])
  statement: ‖p.leadingCoeff‖ <= p.mahlerMeasure
  proof: by
  rw [← mul_one ‖_‖]; rw [mahlerMeasure_eq_leadingCoeff_mul_prod_roots]
  gcongr
  exact one_le_prod_max_one_norm_roots p

@[deprecated (since := "2026-01-02")] alias leading_coeff_le_mahlerMeasure :=
  leadingCoeff_le_mahlerMeasure

中文:
引理 leadingCoeff_le_mahlerMeasure
  条件: (p : 复形[X])
  结论: ‖p.leadingCoeff‖ <= p.mahlerMeasure
  证明: by
  rw [← mul_one ‖_‖]; rw [mahlerMeasure_eq_leadingCoeff_mul_prod_roots]
  gcongr
  exact one_le_prod_max_one_norm_roots p

@[deprecated (since := "2026-01-02")] alias leading_coeff_le_mahlerMeasure :=
  leadingCoeff_le_mahlerMeasure

Depends on / 依赖: mahlerMeasure_eq_leadingCoeff_mul_prod_roots, mul_one, one_le_prod_max_one_norm_roots
-/
lemma leadingCoeff_le_mahlerMeasure (p : Complex[X]) : ‖p.leadingCoeff‖ <= p.mahlerMeasure := by
  rw [← mul_one ‖_‖]; rw [mahlerMeasure_eq_leadingCoeff_mul_prod_roots]
  gcongr
  exact one_le_prod_max_one_norm_roots p

@[deprecated (since := "2026-01-02")] alias leading_coeff_le_mahlerMeasure :=
  leadingCoeff_le_mahlerMeasure

/--
lemma `prod_max_one_norm_roots_le_mahlerMeasure_of_one_le_leadingCoeff` / 引理 `prod_max_one_norm_roots_le_mahlerMeasure_of_one_le_leadingCoeff`

English:
lemma prod_max_one_norm_roots_le_mahlerMeasure_of_one_le_leadingCoeff
  statement: {p : Complex[X]}
  proof: by
  rw [← one_mul (Multiset.prod _)]; rw [mahlerMeasure_eq_leadingCoeff_mul_prod_roots]
  gcongr
exact zero_le_one.trans one_le_prod_max_one_norm_roots p

中文:
引理 prod_max_one_norm_roots_le_mahlerMeasure_of_one_le_leadingCoeff
  结论: {p : 复形[X]}
  证明: by
  rw [← one_mul (Multiset.prod _)]; rw [mahlerMeasure_eq_leadingCoeff_mul_prod_roots]
  gcongr
exact zero_le_one.trans one_le_prod_max_one_norm_roots p

Depends on / 依赖: Multiset, Multiset.prod, mahlerMeasure_eq_leadingCoeff_mul_prod_roots, one_le_prod_max_one_norm_roots, one_mul, zero_le_one, zero_le_one.trans
-/
lemma prod_max_one_norm_roots_le_mahlerMeasure_of_one_le_leadingCoeff {p : Complex[X]}
    (hlc : 1 <= ‖p.leadingCoeff‖) : (p.roots.map (fun a => max 1 ‖a‖)).prod <= p.mahlerMeasure := by
  rw [← one_mul (Multiset.prod _)]; rw [mahlerMeasure_eq_leadingCoeff_mul_prod_roots]
  gcongr
exact zero_le_one.trans one_le_prod_max_one_norm_roots p

/--
lemma `one_le_mahlerMeasure_of_one_le_norm_leadingCoeff` / 引理 `one_le_mahlerMeasure_of_one_le_norm_leadingCoeff`

English:
lemma one_le_mahlerMeasure_of_one_le_norm_leadingCoeff
  statement: {p : Complex[X]}
  proof: hlc.trans (leadingCoeff_le_mahlerMeasure p)

中文:
引理 one_le_mahlerMeasure_of_one_le_norm_leadingCoeff
  结论: {p : 复形[X]}
  证明: hlc.trans (leadingCoeff_le_mahlerMeasure p)

Depends on / 依赖: hlc.trans, leadingCoeff_le_mahlerMeasure
-/
lemma one_le_mahlerMeasure_of_one_le_norm_leadingCoeff {p : Complex[X]}
    (hlc : 1 <= ‖p.leadingCoeff‖) : 1 <= p.mahlerMeasure :=
  hlc.trans (leadingCoeff_le_mahlerMeasure p)

open Filter MeasureTheory Set in
/--
theorem `mahlerMeasure_le_sum_norm_coeff` / 定理 `mahlerMeasure_le_sum_norm_coeff`

English:
theorem mahlerMeasure_le_sum_norm_coeff
  given: (p : Complex[X])
  statement: p.mahlerMeasure <= p.sum fun _ a => ‖a‖
  proof: by
  by_cases hp : p = 0
  · simp [hp]
  have : 0 < p.sum fun _ a => ‖a‖ :=
    Finset.sum_pos' (fun i _ => norm_nonneg (p.coeff i)) ⟨p.natDegree, by simp [hp]⟩
  rw [show (p.sum fun _ a => ‖a‖) = rexp (circleAverage (fun _ => log (p.sum fun _ a => ‖a‖)) 0 1)
    by simp [circleAverage_def]; rw [mul

中文:
定理 mahlerMeasure_le_sum_norm_coeff
  条件: (p : 复形[X])
  结论: p.mahlerMeasure <= p.求和 fun _ a => ‖a‖
  证明: by
  by_cases hp : p = 0
  · simp [hp]
  have : 0 < p.sum fun _ a => ‖a‖ :=
    Finset.sum_pos' (fun i _ => norm_nonneg (p.coeff i)) ⟨p.natDegree, by simp [hp]⟩
  rw [show (p.sum fun _ a => ‖a‖) = rexp (circleAverage (fun _ => log (p.sum fun _ a => ‖a‖)) 0 1)
    by simp [circleAverage_def]; rw [mul

Depends on / 依赖: Finset, Finset.sum_pos, circleAverage, circleAverage_def, exp_log, integral_mono_ae_restrict, intervalIntegrable_mahlerMeasure, intervalIntegral, intervalIntegral.integral_mono_ae_restrict, mahlerMeasure_def_of_ne_zero, mul_assoc, natDegree, norm_nonneg, p.coeff, p.intervalIntegrable_mahlerMeasure, p.natDegree, p.sum, smul_eq_mul, sum_pos
-/
theorem mahlerMeasure_le_sum_norm_coeff (p : Complex[X]) : p.mahlerMeasure <= p.sum fun _ a => ‖a‖ := by
  by_cases hp : p = 0
  · simp [hp]
  have : 0 < p.sum fun _ a => ‖a‖ :=
    Finset.sum_pos' (fun i _ => norm_nonneg (p.coeff i)) ⟨p.natDegree, by simp [hp]⟩
  rw [show (p.sum fun _ a => ‖a‖) = rexp (circleAverage (fun _ => log (p.sum fun _ a => ‖a‖)) 0 1)
    by simp [circleAverage_def]; rw [mul_assoc]; rw [exp_log this], mahlerMeasure_def_of_ne_zero hp,
    circleAverage_def, smul_eq_mul]
  gcongr
  apply intervalIntegral.integral_mono_ae_restrict (by positivity)
    p.intervalIntegrable_mahlerMeasure (by simp)
  rw [EventuallyLE]; rw [eventually_iff_exists_mem]
  use {x : Real | eval (circleMap 0 1 x) p != 0}
  constructor
  · rw [mem_ae_iff, compl_def, Measure.restrict_apply' (by simp)]
    apply (Finite.of_sdiff _ <| finite_singleton (2 * π)).measure_zero
    simp only [ne_eq, mem_ofPred_eq, Decidable.not_not, inter_sdiff_assoc, Icc_sdiff_right]
    rw [ofPred_inter_eq_sep]
    apply Finite.of_finite_image (f := circleMap 0 1) ((Multiset.finite_toSet p.roots).subset _)
 fun _ h _ k l => injOn_circleMap_of_abs_sub_le' one_ne_zero (by linarith) h.1 k.1 l
    simp [hp]
  · intro _ _
    gcongr
    rw [eval_eq_sum]
    apply norm_sum_le_of_le p.support
    simp

open MeasureTheory Set in
/--
theorem `mahlerMeasure_le_sqrt_sum_sq_norm_coeff` / 定理 `mahlerMeasure_le_sqrt_sum_sq_norm_coeff`

English:
theorem mahlerMeasure_le_sqrt_sum_sq_norm_coeff
  given: (p : Polynomial Complex)
  proof: by
  -- Proof: Jensen's inequality (twice) + Parseval's identity
  have : IsFiniteMeasure (volume.restrict (uIoc 0 (2 * π))) := by
    rw [uIoc_of_le (by positivity)]; infer_instance
  have : NeZero (volume (uIoc 0 (2 * π))) := ⟨by simp⟩
  by_cases! hp : p = 0
  · simp [hp]
  have : forallᵐ (θ : Rea

中文:
定理 mahlerMeasure_le_sqrt_sum_sq_norm_coeff
  条件: (p : 多项式 复形)
  证明: by
  -- Proof: Jensen's inequality (twice) + Parseval's identity
  have : IsFiniteMeasure (volume.restrict (uIoc 0 (2 * π))) := by
    rw [uIoc_of_le (by positivity)]; infer_instance
  have : NeZero (volume (uIoc 0 (2 * π))) := ⟨by simp⟩
  by_cases! hp : p = 0
  · simp [hp]
  have : forallᵐ (θ : Rea
-/
theorem mahlerMeasure_le_sqrt_sum_sq_norm_coeff (p : Polynomial Complex) :
    p.mahlerMeasure <= √(∑ i in p.support, ‖p.coeff i‖ ^ 2) := by
  -- Proof: Jensen's inequality (twice) + Parseval's identity
  have : IsFiniteMeasure (volume.restrict (uIoc 0 (2 * π))) := by
    rw [uIoc_of_le (by positivity)]; infer_instance
  have : NeZero (volume (uIoc 0 (2 * π))) := ⟨by simp⟩
  by_cases! hp : p = 0
  · simp [hp]
  have : forallᵐ (θ : Real) ∂volume.restrict (uIoc 0 (2 * π)), 0 < ‖p.eval (circleMap 0 1 θ)‖ := by
    rw [ae_restrict_iff' measurableSet_uIoc]
    refine Set.Finite.measure_zero ?_ _
    simp only [norm_pos_iff, ne_eq, compl_ofPred, Classical.not_imp, Decidable.not_not]
    refine Finite.of_finite_image (f := circleMap 0 1) (p.roots.finite_toSet.subset ?_) ?_
    · rintro z ⟨θ, ⟨_, heval⟩, rfl⟩
      exact (mem_roots hp).mpr heval
    · grw [ofPred_and, inter_subset_left]
      exact injOn_circleMap_of_abs_sub_le one_ne_zero (by simp [abs_of_pos pi_pos])
  have hlogAe : forallᵐ (θ : Real) ∂volume.restrict (uIoc 0 (2 * π)),
      exp (log ‖p.eval (circleMap 0 1 θ)‖) = ‖p.eval (circleMap 0 1 θ)‖ := by
    filter_upwards [this] with θ hθ
    exact exp_log hθ
  have hcont : Continuous (fun x : Real => ‖eval (circleMap 0 1 x) p‖) := by fun_prop
  simp only [mahlerMeasure, logMahlerMeasure, ne_eq, hp, not_false_eq_true, ↓reduceIte]
  rw [circleAverage_eq_intervalAverage]
  calc exp (⨍ (θ : Real) in 0..(2 * π), log ‖p.eval (circleMap 0 1 θ)‖)
    <= ⨍ (θ : Real) in 0..(2 * π), exp (log ‖p.eval (circleMap 0 1 θ)‖) := by
        -- First Jensen's inequality invocation
        refine convexOn_exp.map_average_le continuousOn_exp isClosed_univ (by simp) ?_ ?_
        · rw [Set.uIoc_of_le (by positivity : 0 <= 2 * Real.pi)]
          exact ((analyticOnNhd_id.aeval_polynomial p).meromorphicOn.circleIntegrable_log_norm).1
        · exact (integrable_congr hlogAe).mpr hcont.integrableOn_uIoc
    _ = ⨍ (θ : Real) in 0..(2 * π), ‖p.eval (circleMap 0 1 θ)‖ := average_congr hlogAe
    _ = √((⨍ (θ : Real) in 0..(2 * π), ‖p.eval (circleMap 0 1 θ)‖) ^ 2) := by
        rw [sqrt_sq]; exact integral_nonneg (fun _ => norm_nonneg _)
    _ <= √(⨍ (θ : Real) in 0..(2 * π), ‖p.eval (circleMap 0 1 θ)‖ ^ 2) := by
        -- Second Jensen's inequality invocation
        gcongr
        refine (convexOn_pow 2).map_average_le (continuousOn_pow 2)
            isClosed_Ici (by filter_upwards; simp) ?_ ?_
        · exact hcont.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
        · exact ((continuous_pow 2).comp hcont).integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
    _ = √(circleAverage (fun θ => ‖p.eval θ‖ ^ 2) 0 1) := by simp [circleAverage_eq_intervalAverage]
    _ = √(∑ i in p.support, ‖p.coeff i‖ ^ 2) := by simp [p.sum_sq_norm_coeff_eq_circleAverage]

/--
theorem `mahlerMeasure_le_sqrt_natDegree_add_one_mul_supNorm` / 定理 `mahlerMeasure_le_sqrt_natDegree_add_one_mul_supNorm`

English:
theorem mahlerMeasure_le_sqrt_natDegree_add_one_mul_supNorm
  given: (p : Polynomial Complex)
  proof: (p.mahlerMeasure_le_sqrt_sum_sq_norm_coeff).trans by
    rw [show √(↑(p.natDegree) + 1) * p.supNorm = √((p.natDegree + 1) * p.supNorm ^ 2) by
      rw [Real.sqrt_mul (by positivity)]; rw [Real.sqrt_sq p.supNorm_nonneg]]
    gcongr
    refine (p.support.sum_le_card_nsmul _ (p.supNorm ^ 2) fun i _ => 

中文:
定理 mahlerMeasure_le_sqrt_natDegree_add_one_mul_supNorm
  条件: (p : 多项式 复形)
  证明: (p.mahlerMeasure_le_sqrt_sum_sq_norm_coeff).trans by
    rw [show √(↑(p.natDegree) + 1) * p.supNorm = √((p.natDegree + 1) * p.supNorm ^ 2) by
      rw [Real.sqrt_mul (by positivity)]; rw [Real.sqrt_sq p.supNorm_nonneg]]
    gcongr
    refine (p.support.sum_le_card_nsmul _ (p.supNorm ^ 2) fun i _ => 

Depends on / 依赖: Real.sqrt_mul, Real.sqrt_sq, card_supp_le_succ_natDegree, le_supNorm, mahlerMeasure_le_sqrt_sum_sq_norm_coeff, mod_cast, natDegree, nsmul_eq_mul, p.card_supp_le_succ_natDegree, p.le_supNorm, p.mahlerMeasure_le_sqrt_sum_sq_norm_coeff, p.natDegree, p.supNorm, p.supNorm_nonneg, p.support.sum_le_card_nsmul, sqrt_mul, sqrt_sq, sum_le_card_nsmul, supNorm, supNorm_nonneg
-/
theorem mahlerMeasure_le_sqrt_natDegree_add_one_mul_supNorm (p : Polynomial Complex) :
    p.mahlerMeasure <= √(p.natDegree + 1) * p.supNorm :=
(p.mahlerMeasure_le_sqrt_sum_sq_norm_coeff).trans by
    rw [show √(↑(p.natDegree) + 1) * p.supNorm = √((p.natDegree + 1) * p.supNorm ^ 2) by
      rw [Real.sqrt_mul (by positivity)]; rw [Real.sqrt_sq p.supNorm_nonneg]]
    gcongr
    refine (p.support.sum_le_card_nsmul _ (p.supNorm ^ 2) fun i _ => ?_).trans ?_
    · gcongr; exact p.le_supNorm _
    · simp only [nsmul_eq_mul]
      gcongr
      exact mod_cast p.card_supp_le_succ_natDegree

open Multiset in
/--
theorem `norm_coeff_le_choose_mul_mahlerMeasure` / 定理 `norm_coeff_le_choose_mul_mahlerMeasure`

English:
theorem norm_coeff_le_choose_mul_mahlerMeasure
  given: (n : Nat) (p : Complex[X])
  proof: by
  by_cases hp : p = 0
  · simp [hp]
  rcases lt_or_ge p.natDegree n with hlt | hn
  · simp [coeff_eq_zero_of_natDegree_lt hlt, Nat.choose_eq_zero_of_lt hlt]
  rw [mahlerMeasure_eq_leadingCoeff_mul_prod_roots]; rw [mul_left_comm]; rw [coeff_eq_esymm_roots_of_card (splits_iff_card_roots.mp (IsAlgCl

中文:
定理 norm_coeff_le_choose_mul_mahlerMeasure
  条件: (n : 自然数) (p : 复形[X])
  证明: by
  by_cases hp : p = 0
  · simp [hp]
  rcases lt_or_ge p.natDegree n with hlt | hn
  · simp [coeff_eq_zero_of_natDegree_lt hlt, Nat.choose_eq_zero_of_lt hlt]
  rw [mahlerMeasure_eq_leadingCoeff_mul_prod_roots]; rw [mul_left_comm]; rw [coeff_eq_esymm_roots_of_card (splits_iff_card_roots.mp (IsAlgCl

Depends on / 依赖: IsAlgClosed, IsAlgClosed.splits, Nat.choose_eq_zero_of_lt, choose_eq_zero_of_lt, coeff_eq_esymm_roots_of_card, coeff_eq_zero_of_natDegree_lt, leadingCoeff_ne_zero, leadingCoeff_ne_zero.mpr, lt_or_ge, mahlerMeasure_eq_leadingCoeff_mul_prod_roots, mul_assoc, mul_left_comm, natDegree, norm_mul, norm_neg, norm_one, norm_pow, one_mul, one_pow, p.natDegree
-/
theorem norm_coeff_le_choose_mul_mahlerMeasure (n : Nat) (p : Complex[X]) :
    ‖p.coeff n‖ <= (p.natDegree).choose n * p.mahlerMeasure := by
  by_cases hp : p = 0
  · simp [hp]
  rcases lt_or_ge p.natDegree n with hlt | hn
  · simp [coeff_eq_zero_of_natDegree_lt hlt, Nat.choose_eq_zero_of_lt hlt]
  rw [mahlerMeasure_eq_leadingCoeff_mul_prod_roots]; rw [mul_left_comm]; rw [coeff_eq_esymm_roots_of_card (splits_iff_card_roots.mp (IsAlgClosed.splits p)) hn]; rw [mul_assoc]; rw [norm_mul]; rw [norm_mul]; rw [norm_pow]; rw [norm_neg]; rw [norm_one]; rw [one_pow]; rw [one_mul]; rw [mul_le_mul_iff_right₀ (by simp [leadingCoeff_ne_zero.mpr hp]), esymm,
    Finset.sum_multiset_map_count]
apply le_trans norm_sum_le _ _
  simp_rw [nsmul_eq_mul, norm_mul, _root_.norm_natCast]
  let S := powersetCard (p.natDegree - n) p.roots
  --to be used later in the calc block:
  have (x : Multiset Complex) (hx : x in S.toFinset) : ∏ x_1 in x.toFinset, ‖x_1‖ ^ count x_1 x
      <= ∏ m in p.roots.toFinset, max 1 ‖m‖ ^ count m p.roots := by
    rw [mem_toFinset]; rw [mem_powersetCard] at hx
    calc
    ∏ z in x.toFinset, ‖z‖ ^ count z x
      <= ∏ z in x.toFinset, (1 ⊔ ‖z‖) ^ count z x := by
      gcongr with a
      exact le_max_right 1 ‖a‖
    _ <= ∏ z in p.roots.toFinset, (1 ⊔ ‖z‖) ^ count z x := by
      simp_rw [← coe_nnnorm]
      norm_cast
      exact Finset.prod_le_prod_of_subset_of_one_le' (toFinset_subset.mpr (subset_of_le hx.1))
        (fun a _ _ => one_le_pow₀ (le_max_left 1 ‖a‖))
    _ <= ∏ z in p.roots.toFinset, (1 ⊔ ‖z‖) ^ count z p.roots := by
      gcongr with a
      · exact le_max_left 1 ‖a‖
      · exact hx.1
  --final calc block:
  calc ∑ x in S.toFinset, count x S * ‖x.prod‖
    _ <= ∑ x in S.toFinset, count x S * ((p.roots).map (fun a => max 1 ‖a‖)).prod := by
      gcongr with x hx
      rw [Finset.prod_multiset_map_count]; rw [Finset.prod_multiset_count]; rw [norm_prod]
      simp_rw [norm_pow]
      exact this x hx
    _ = p.natDegree.choose n * (p.roots.map (fun a => 1 ⊔ ‖a‖)).prod := by
      rw [← Finset.sum_mul]
      congr
      norm_cast
      simp only [mem_powersetCard, mem_toFinset, imp_self, implies_true, sum_count_eq_card,
        card_powersetCard, S, ← Nat.choose_symm hn]
      congr
exact splits_iff_card_roots.mp IsAlgClosed.splits p

/--
theorem `supNorm_le_choose_natDegree_div_two_mul_mahlerMeasure` / 定理 `supNorm_le_choose_natDegree_div_two_mul_mahlerMeasure`

English:
theorem supNorm_le_choose_natDegree_div_two_mul_mahlerMeasure
  given: (p : Polynomial Complex)
  proof: by
  obtain ⟨i, hi⟩ := p.exists_eq_supNorm
  calc p.supNorm = ‖p.coeff i‖ := hi
    _ <= (p.natDegree.choose i) * p.mahlerMeasure := p.norm_coeff_le_choose_mul_mahlerMeasure i
    _ <= (p.natDegree.choose (p.natDegree / 2)) * p.mahlerMeasure :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast Nat

中文:
定理 supNorm_le_choose_natDegree_div_two_mul_mahlerMeasure
  条件: (p : 多项式 复形)
  证明: by
  obtain ⟨i, hi⟩ := p.exists_eq_supNorm
  calc p.supNorm = ‖p.coeff i‖ := hi
    _ <= (p.natDegree.choose i) * p.mahlerMeasure := p.norm_coeff_le_choose_mul_mahlerMeasure i
    _ <= (p.natDegree.choose (p.natDegree / 2)) * p.mahlerMeasure :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast Nat

Depends on / 依赖: Nat.choose_le_middle, choose_le_middle, exists_eq_supNorm, mahlerMeasure, mahlerMeasure_nonneg, mul_le_mul_of_nonneg_right, natDegree, norm_coeff_le_choose_mul_mahlerMeasure, p.coeff, p.exists_eq_supNorm, p.mahlerMeasure, p.mahlerMeasure_nonneg, p.natDegree, p.natDegree.choose, p.norm_coeff_le_choose_mul_mahlerMeasure, p.supNorm, supNorm
-/
theorem supNorm_le_choose_natDegree_div_two_mul_mahlerMeasure (p : Polynomial Complex) :
    p.supNorm <= p.natDegree.choose (p.natDegree / 2) * p.mahlerMeasure := by
  obtain ⟨i, hi⟩ := p.exists_eq_supNorm
  calc p.supNorm = ‖p.coeff i‖ := hi
    _ <= (p.natDegree.choose i) * p.mahlerMeasure := p.norm_coeff_le_choose_mul_mahlerMeasure i
    _ <= (p.natDegree.choose (p.natDegree / 2)) * p.mahlerMeasure :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.choose_le_middle i p.natDegree)
        p.mahlerMeasure_nonneg

/-!
### The Mignotte bound
-/

/--
theorem `norm_coeff_le_choose_mul_mahlerMeasure_of_one_le_mahlerMeasure` / 定理 `norm_coeff_le_choose_mul_mahlerMeasure_of_one_le_mahlerMeasure`

English:
theorem norm_coeff_le_choose_mul_mahlerMeasure_of_one_le_mahlerMeasure
  statement: (n : Nat) (g h : Complex[X])
  proof: (g.norm_coeff_le_choose_mul_mahlerMeasure n).trans by
    gcongr
    rw [mahlerMeasure_mul]
    exact le_mul_of_one_le_right g.mahlerMeasure_nonneg hh

中文:
定理 norm_coeff_le_choose_mul_mahlerMeasure_of_one_le_mahlerMeasure
  结论: (n : 自然数) (g h : 复形[X])
  证明: (g.norm_coeff_le_choose_mul_mahlerMeasure n).trans by
    gcongr
    rw [mahlerMeasure_mul]
    exact le_mul_of_one_le_right g.mahlerMeasure_nonneg hh

Depends on / 依赖: g.mahlerMeasure_nonneg, g.norm_coeff_le_choose_mul_mahlerMeasure, le_mul_of_one_le_right, mahlerMeasure_mul, mahlerMeasure_nonneg, norm_coeff_le_choose_mul_mahlerMeasure
-/
theorem norm_coeff_le_choose_mul_mahlerMeasure_of_one_le_mahlerMeasure (n : Nat) (g h : Complex[X])
    (hh : 1 <= h.mahlerMeasure) :
    ‖g.coeff n‖ <= g.natDegree.choose n * (g * h).mahlerMeasure :=
(g.norm_coeff_le_choose_mul_mahlerMeasure n).trans by
    gcongr
    rw [mahlerMeasure_mul]
    exact le_mul_of_one_le_right g.mahlerMeasure_nonneg hh

end Polynomial

section generic

/-!
### Mahler Measure on Other Rings

While the Mahler measure is an inherently Complex concept, we often want to work with it for
polynomials with coefficients in subrings of `ℂ`. To do so, we introduce `mapMahlerMeasure`. This
takes a `RingHom A ℂ` which takes the polynomial from `A[X]` to `ℂ[X]`.

Some lemmas require the `RingHom` to also preserve the norm on the base ring, e.g.,
`leadingCoeff_le_mapMahlerMeasure`. Those will come below.
-/

namespace Polynomial

variable {A : Type*} [Semiring A] (p : A[X]) (v : A ->+* Complex)

/--
Definition of `mapMahlerMeasure` / `mapMahlerMeasure` 的定义

English:
definition mapMahlerMeasure
  body: (p.map v).mahlerMeasure

中文:
定义 mapMahlerMeasure
  定义体: (p.map v).mahlerMeasure

Depends on / 依赖: mahlerMeasure, p.map
-/
noncomputable def mapMahlerMeasure := (p.map v).mahlerMeasure

/--
lemma `mapMahlerMeasure_eq` / 引理 `mapMahlerMeasure_eq`

English:
lemma mapMahlerMeasure_eq
  statement: p.mapMahlerMeasure v = (p.map v).mahlerMeasure
  proof: rfl

中文:
引理 mapMahlerMeasure_eq
  结论: p.mapMahlerMeasure v = (p.map v).mahlerMeasure
  证明: rfl
-/
lemma mapMahlerMeasure_eq : p.mapMahlerMeasure v = (p.map v).mahlerMeasure := rfl

/--
lemma `mapMahlerMeasure_mul` / 引理 `mapMahlerMeasure_mul`

English:
lemma mapMahlerMeasure_mul
  given: (f g : A[X])
  proof: by
  simp [mapMahlerMeasure, mahlerMeasure_mul]

中文:
引理 mapMahlerMeasure_mul
  条件: (f g : A[X])
  证明: by
  simp [mapMahlerMeasure, mahlerMeasure_mul]

Depends on / 依赖: mahlerMeasure_mul, mapMahlerMeasure
-/
lemma mapMahlerMeasure_mul (f g : A[X]) :
    (f * g).mapMahlerMeasure v = (f.mapMahlerMeasure v) * (g.mapMahlerMeasure v) := by
  simp [mapMahlerMeasure, mahlerMeasure_mul]

/--
lemma `mapMahlerMeasure_nonneg` / 引理 `mapMahlerMeasure_nonneg`

English:
lemma mapMahlerMeasure_nonneg
  statement: 0 <= p.mapMahlerMeasure v
  proof: Polynomial.mahlerMeasure_nonneg _

@[simp]

中文:
引理 mapMahlerMeasure_nonneg
  结论: 0 <= p.mapMahlerMeasure v
  证明: Polynomial.mahlerMeasure_nonneg _

@[simp]

Depends on / 依赖: Cofork, Cofork.IsColimit.regularEpi, IsColimit, Polynomial, Polynomial.mahlerMeasure_nonneg, e.isCoequalizer, isCoequalizer, mahlerMeasure_nonneg, regularEpi
-/
lemma mapMahlerMeasure_nonneg : 0 <= p.mapMahlerMeasure v :=
  Polynomial.mahlerMeasure_nonneg _

@[simp]
/--
lemma `mapMahlerMeasure_zero` / 引理 `mapMahlerMeasure_zero`

English:
lemma mapMahlerMeasure_zero
  statement: (0 : A[X]).mapMahlerMeasure v = 0
  proof: by
  simp [mapMahlerMeasure]

@[simp]

中文:
引理 mapMahlerMeasure_zero
  结论: (0 : A[X]).mapMahlerMeasure v = 0
  证明: by
  simp [mapMahlerMeasure]

@[simp]

Depends on / 依赖: mapMahlerMeasure
-/
lemma mapMahlerMeasure_zero : (0 : A[X]).mapMahlerMeasure v = 0 := by
  simp [mapMahlerMeasure]

@[simp]
/--
lemma `mapMahlerMeasure_one` / 引理 `mapMahlerMeasure_one`

English:
lemma mapMahlerMeasure_one
  statement: (1 : A[X]).mapMahlerMeasure v = 1
  proof: by
  simp [mapMahlerMeasure]

中文:
引理 mapMahlerMeasure_one
  结论: (1 : A[X]).mapMahlerMeasure v = 1
  证明: by
  simp [mapMahlerMeasure]

Depends on / 依赖: mapMahlerMeasure
-/
lemma mapMahlerMeasure_one : (1 : A[X]).mapMahlerMeasure v = 1 := by
  simp [mapMahlerMeasure]

variable {A : Type*} [NormedRing A] (p : A[X]) (v : A ->+* Complex)

/--
lemma `mapMahlerMeasure_const` / 引理 `mapMahlerMeasure_const`

English:
lemma mapMahlerMeasure_const
  given: (hv : Isometry v) (z : A)
  statement: (C z).mapMahlerMeasure v = ‖z‖
  proof: by
  simp [mapMahlerMeasure, hv.norm_map_of_map_zero (map_zero _)]

中文:
引理 mapMahlerMeasure_const
  条件: (hv : 等距 v) (z : A)
  结论: (C z).mapMahlerMeasure v = ‖z‖
  证明: by
  simp [mapMahlerMeasure, hv.norm_map_of_map_zero (map_zero _)]

Depends on / 依赖: hv.norm_map_of_map_zero, mapMahlerMeasure, map_zero, norm_map_of_map_zero
-/
lemma mapMahlerMeasure_const (hv : Isometry v) (z : A) : (C z).mapMahlerMeasure v = ‖z‖ := by
  simp [mapMahlerMeasure, hv.norm_map_of_map_zero (map_zero _)]

/--
lemma `leadingCoeff_le_mapMahlerMeasure` / 引理 `leadingCoeff_le_mapMahlerMeasure`

English:
lemma leadingCoeff_le_mapMahlerMeasure
  given: (hv : Isometry v)
  proof: by
  by_cases hp : p.leadingCoeff = 0
  · simp [hp, mapMahlerMeasure_nonneg]
  · have hv_ne : v p.leadingCoeff != 0 :=
fun h => hp hv.injective h.trans (map_zero _).symm
    have hv_norm : ‖v p.leadingCoeff‖ = ‖p.leadingCoeff‖ := hv.norm_map_of_map_zero (map_zero _) _
    grw [← hv_norm, ← leadingCo

中文:
引理 leadingCoeff_le_mapMahlerMeasure
  条件: (hv : 等距 v)
  证明: by
  by_cases hp : p.leadingCoeff = 0
  · simp [hp, mapMahlerMeasure_nonneg]
  · have hv_ne : v p.leadingCoeff != 0 :=
fun h => hp hv.injective h.trans (map_zero _).symm
    have hv_norm : ‖v p.leadingCoeff‖ = ‖p.leadingCoeff‖ := hv.norm_map_of_map_zero (map_zero _) _
    grw [← hv_norm, ← leadingCo

Depends on / 依赖: h.trans, hv.injective, hv.norm_map_of_map_zero, hv_ne, hv_norm, injective, leadingCoeff, leadingCoeff_le_mahlerMeasure, leadingCoeff_map_of_leadingCoeff_ne_zero, mapMahlerMeasure, mapMahlerMeasure_nonneg, map_zero, norm_map_of_map_zero, p.leadingCoeff
-/
lemma leadingCoeff_le_mapMahlerMeasure (hv : Isometry v) :
    ‖p.leadingCoeff‖ <= p.mapMahlerMeasure v := by
  by_cases hp : p.leadingCoeff = 0
  · simp [hp, mapMahlerMeasure_nonneg]
  · have hv_ne : v p.leadingCoeff != 0 :=
fun h => hp hv.injective h.trans (map_zero _).symm
    have hv_norm : ‖v p.leadingCoeff‖ = ‖p.leadingCoeff‖ := hv.norm_map_of_map_zero (map_zero _) _
    grw [← hv_norm, ← leadingCoeff_map_of_leadingCoeff_ne_zero v hv_ne,
      leadingCoeff_le_mahlerMeasure, mapMahlerMeasure]

variable {p} in
/--
lemma `Monic.one_le_mapMahlerMeasure` / 引理 `Monic.one_le_mapMahlerMeasure`

English:
lemma Monic.one_le_mapMahlerMeasure
  given: [NormOneClass A] (hv : Isometry v) (hp : p.Monic)
  proof: by
  grw [← p.leadingCoeff_le_mapMahlerMeasure v hv, hp.leadingCoeff, norm_one]

中文:
引理 Monic.one_le_mapMahlerMeasure
  条件: [NormOne类 A] (hv : 等距 v) (hp : p.Monic)
  证明: by
  grw [← p.leadingCoeff_le_mapMahlerMeasure v hv, hp.leadingCoeff, norm_one]

Depends on / 依赖: hp.leadingCoeff, leadingCoeff, leadingCoeff_le_mapMahlerMeasure, norm_one, p.leadingCoeff_le_mapMahlerMeasure
-/
lemma Monic.one_le_mapMahlerMeasure [NormOneClass A] (hv : Isometry v) (hp : p.Monic) :
    1 <= p.mapMahlerMeasure v := by
  grw [← p.leadingCoeff_le_mapMahlerMeasure v hv, hp.leadingCoeff, norm_one]

variable {p} in
/--
theorem `mapMahlerMeasure_pos_of_ne_zero` / 定理 `mapMahlerMeasure_pos_of_ne_zero`

English:
theorem mapMahlerMeasure_pos_of_ne_zero
  given: (hv : Isometry v) (hp : p != 0)
  proof: mahlerMeasure_pos_of_ne_zero (Polynomial.map_eq_zero_iff hv.injective).not.mpr hp

中文:
定理 mapMahlerMeasure_pos_of_ne_zero
  条件: (hv : 等距 v) (hp : p != 0)
  证明: mahlerMeasure_pos_of_ne_zero (Polynomial.map_eq_zero_iff hv.injective).not.mpr hp

Depends on / 依赖: Polynomial, Polynomial.map_eq_zero_iff, hv.injective, injective, mahlerMeasure_pos_of_ne_zero, map_eq_zero_iff, not.mpr
-/
theorem mapMahlerMeasure_pos_of_ne_zero (hv : Isometry v) (hp : p != 0) :
    0 < p.mapMahlerMeasure v :=
mahlerMeasure_pos_of_ne_zero (Polynomial.map_eq_zero_iff hv.injective).not.mpr hp

/--
theorem `mapMahlerMeasure_le_sum_norm_coeff` / 定理 `mapMahlerMeasure_le_sum_norm_coeff`

English:
theorem mapMahlerMeasure_le_sum_norm_coeff
  given: (hv : Isometry v)
  proof: by
.trans_eq apply mahlerMeasure_le_sum_norm_coeff _
  rw [sum_def]; rw [sum_def]; rw [support_map_of_injective _ hv.injective]
  exact Finset.sum_congr rfl fun x _ => by
    simp [hv.norm_map_of_map_zero (map_zero _)]

中文:
定理 mapMahlerMeasure_le_sum_norm_coeff
  条件: (hv : 等距 v)
  证明: by
.trans_eq apply mahlerMeasure_le_sum_norm_coeff _
  rw [sum_def]; rw [sum_def]; rw [support_map_of_injective _ hv.injective]
  exact Finset.sum_congr rfl fun x _ => by
    simp [hv.norm_map_of_map_zero (map_zero _)]

Depends on / 依赖: Finset, Finset.sum_congr, hv.injective, hv.norm_map_of_map_zero, injective, mahlerMeasure_le_sum_norm_coeff, map_zero, norm_map_of_map_zero, sum_congr, sum_def, support_map_of_injective, trans_eq
-/
theorem mapMahlerMeasure_le_sum_norm_coeff (hv : Isometry v) :
    p.mapMahlerMeasure v <= p.sum fun _ a => ‖a‖ := by
.trans_eq apply mahlerMeasure_le_sum_norm_coeff _
  rw [sum_def]; rw [sum_def]; rw [support_map_of_injective _ hv.injective]
  exact Finset.sum_congr rfl fun x _ => by
    simp [hv.norm_map_of_map_zero (map_zero _)]

/--
theorem `norm_coeff_le_choose_mul_mapMahlerMeasure` / 定理 `norm_coeff_le_choose_mul_mapMahlerMeasure`

English:
theorem norm_coeff_le_choose_mul_mapMahlerMeasure
  given: (hv : Isometry v) (n : Nat) (p : A[X])
  proof: by
  have hv_norm : ‖p.coeff n‖ = ‖v (p.coeff n)‖ :=
    (hv.norm_map_of_map_zero (map_zero _) _).symm
  have hcoeff : ‖v (p.coeff n)‖ = ‖(p.map v).coeff n‖ := by simp
  grw [hv_norm, hcoeff, norm_coeff_le_choose_mul_mahlerMeasure,
    natDegree_map_eq_of_injective hv.injective, mapMahlerMeasure]

中文:
定理 norm_coeff_le_choose_mul_mapMahlerMeasure
  条件: (hv : 等距 v) (n : 自然数) (p : A[X])
  证明: by
  have hv_norm : ‖p.coeff n‖ = ‖v (p.coeff n)‖ :=
    (hv.norm_map_of_map_zero (map_zero _) _).symm
  have hcoeff : ‖v (p.coeff n)‖ = ‖(p.map v).coeff n‖ := by simp
  grw [hv_norm, hcoeff, norm_coeff_le_choose_mul_mahlerMeasure,
    natDegree_map_eq_of_injective hv.injective, mapMahlerMeasure]

Depends on / 依赖: hcoeff, hv.injective, hv.norm_map_of_map_zero, hv_norm, injective, mapMahlerMeasure, map_zero, natDegree_map_eq_of_injective, norm_coeff_le_choose_mul_mahlerMeasure, norm_map_of_map_zero, p.coeff, p.map
-/
theorem norm_coeff_le_choose_mul_mapMahlerMeasure (hv : Isometry v) (n : Nat) (p : A[X]) :
    ‖p.coeff n‖ <= (p.natDegree).choose n * p.mapMahlerMeasure v := by
  have hv_norm : ‖p.coeff n‖ = ‖v (p.coeff n)‖ :=
    (hv.norm_map_of_map_zero (map_zero _) _).symm
  have hcoeff : ‖v (p.coeff n)‖ = ‖(p.map v).coeff n‖ := by simp
  grw [hv_norm, hcoeff, norm_coeff_le_choose_mul_mahlerMeasure,
    natDegree_map_eq_of_injective hv.injective, mapMahlerMeasure]

end Polynomial

end generic
