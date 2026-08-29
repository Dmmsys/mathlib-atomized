/-
Copyright (c) 2025 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov, Andrew Yang
-/
module

public import Mathlib.Analysis.Calculus.IteratedDeriv.ConvergenceOnBall
public import Mathlib.Analysis.Complex.OperatorNorm
public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
public import Mathlib.Analysis.SpecialFunctions.OrdinaryHypergeometric
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.RingTheory.Binomial

/-!
# Binomial Series

This file introduces the binomial series:
$$
\sum_{k=0}^{\infty} \; \binom{a}{k} \; x^k = 1 + a x + \frac{a(a-1)}{2!} x^2 +
  \frac{a(a-1)(a-2)}{3!} x^3 + \cdots
$$
where $a$ is an element of a normed field $\mathbb{K}$,
and $x$ is an element of a normed algebra over $\mathbb{K}$.

## Main Statements

* `binomialSeries_radius_eq_one`: The radius of convergence of the binomial series is `1` when `a`
  is not a natural number.
* `binomialSeries_radius_eq_top_of_nat`: In case `a` is natural, the series converges everywhere,
  since it is finite.
-/

@[expose] public section

open scoped Nat

universe u v

@[norm_cast]
/--
lemma `Complex.ofReal_choose` / 引理 `Complex.ofReal_choose`

English:
lemma Complex.ofReal_choose
  given: (a : Real) (n : Nat)
  proof: Ring.map_choose (algebraMap Real Complex) _ _

中文:
引理 复形.of实数_choose
  条件: (a : 实数) (n : 自然数)
  证明: Ring.map_choose (algebraMap Real Complex) _ _

Depends on / 依赖: Ring.map_choose, algebraMap, map_choose
-/
lemma Complex.ofReal_choose (a : Real) (n : Nat) :
    ↑(Ring.choose a n) = Ring.choose (a : Complex) n :=
  Ring.map_choose (algebraMap Real Complex) _ _

/--
Definition of `binomialSeries` / `binomialSeries` 的定义

English:
definition binomialSeries
  signature: {𝕂 : Type u} [Field 𝕂] [CharZero 𝕂] (𝔸 : Type v)
  body: .ofScalars 𝔸 (Ring.choose a ·)

@[simp]

中文:
定义 binomialSeries
  签名: {𝕂 : 类型u} [域 𝕂] [特征零 𝕂] (𝔸 : 类型v)
  定义体: .ofScalars 𝔸 (Ring.choose a ·)

@[simp]

Depends on / 依赖: Ring.choose, ofScalars
-/
noncomputable def binomialSeries {𝕂 : Type u} [Field 𝕂] [CharZero 𝕂] (𝔸 : Type v)
    [Ring 𝔸] [Algebra 𝕂 𝔸] [TopologicalSpace 𝔸] [IsTopologicalRing 𝔸] (a : 𝕂) :
    FormalMultilinearSeries 𝕂 𝔸 𝔸 :=
  .ofScalars 𝔸 (Ring.choose a ·)

@[simp]
/--
theorem `binomialSeries_apply` / 定理 `binomialSeries_apply`

English:
theorem binomialSeries_apply
  statement: {𝕂 : Type u} [Field 𝕂] [CharZero 𝕂] (𝔸 : Type v)
  proof: by
  simp [binomialSeries, FormalMultilinearSeries.ofScalars]

中文:
定理 binomialSeries_apply
  结论: {𝕂 : 类型u} [域 𝕂] [特征零 𝕂] (𝔸 : 类型v)
  证明: by
  simp [binomialSeries, FormalMultilinearSeries.ofScalars]

Depends on / 依赖: FormalMultilinearSeries, FormalMultilinearSeries.ofScalars, binomialSeries, ofScalars
-/
theorem binomialSeries_apply {𝕂 : Type u} [Field 𝕂] [CharZero 𝕂] (𝔸 : Type v)
    [Ring 𝔸] [Algebra 𝕂 𝔸] [TopologicalSpace 𝔸] [IsTopologicalRing 𝔸] (a : 𝕂) {n} (v : Fin n -> 𝔸) :
    binomialSeries 𝔸 a n v = Ring.choose a n • (List.ofFn v).prod := by
  simp [binomialSeries, FormalMultilinearSeries.ofScalars]

/--
theorem `binomialSeries_eq_ordinaryHypergeometricSeries` / 定理 `binomialSeries_eq_ordinaryHypergeometricSeries`

English:
theorem binomialSeries_eq_ordinaryHypergeometricSeries
  statement: {𝕂 : Type u} [Field 𝕂] [CharZero 𝕂]
  proof: by
  simp only [binomialSeries, ordinaryHypergeometricSeries,
    FormalMultilinearSeries.ofScalars_comp_neg_id]
  congr! with n
  rw [ordinaryHypergeometricCoefficient]; rw [mul_inv_cancel_right₀ (by simp [ascPochhammer_eval_eq_zero_iff]; grind)]
  simp only [Ring.choose_eq_smul, Polynomial.descPochhammer_smeval_eq_ascPochhammer,
    Polynomial.ascPochhammer_smeval_cast, Polynomial.ascPochhammer_smeval_eq_eval,
    ascPochhammer_eval_neg_eq_descPochhammer, descPochhammer_eval_eq_ascPochhammer]
  ring_nf
  simp

中文:
定理 binomialSeries_eq_ordinaryHypergeometricSeries
  结论: {𝕂 : 类型u} [域 𝕂] [特征零 𝕂]
  证明: by
  simp only [binomialSeries, ordinaryHypergeometricSeries,
    FormalMultilinearSeries.ofScalars_comp_neg_id]
  congr! with n
  rw [ordinaryHypergeometricCoefficient]; rw [mul_inv_cancel_right₀ (by simp [ascPochhammer_eval_eq_zero_iff]; grind)]
  simp only [Ring.choose_eq_smul, Polynomial.descPochhammer_smeval_eq_ascPochhammer,
    Polynomial.ascPochhammer_smeval_cast, Polynomial.ascPochhammer_smeval_eq_eval,
    ascPochhammer_eval_neg_eq_descPochhammer, descPochhammer_eval_eq_ascPochhammer]
  ring_nf
  simp

Depends on / 依赖: FormalMultilinearSeries, FormalMultilinearSeries.ofScalars_comp_neg_id, Polynomial, Polynomial.ascPochhammer_smeval_cast, Polynomial.ascPochhammer_smeval_eq_eval, Polynomial.descPochhammer_smeval_eq_ascPochhammer, Ring.choose_eq_smul, ascPochhammer_eval_eq_zero_iff, ascPochhammer_eval_neg_eq_descPochhammer, ascPochhammer_smeval_cast, ascPochhammer_smeval_eq_eval, binomialSeries, choose_eq_smul, descPochhammer_eval_eq_ascPochhammer, descPochhammer_smeval_eq_ascPochhammer, ofScalars_comp_neg_id, ordinaryHypergeometricCoefficient, ordinaryHypergeometricSeries, ring_nf
-/
theorem binomialSeries_eq_ordinaryHypergeometricSeries {𝕂 : Type u} [Field 𝕂] [CharZero 𝕂]
    {𝔸 : Type v} [Ring 𝔸] [Algebra 𝕂 𝔸] [TopologicalSpace 𝔸] [IsTopologicalRing 𝔸] {a b : 𝕂}
    (h : forall (k : Nat), (k : 𝕂) != -b) :
    binomialSeries 𝔸 a =
    (ordinaryHypergeometricSeries 𝔸 (-a) b b).compContinuousLinearMap (-(.id _ _)) := by
  simp only [binomialSeries, ordinaryHypergeometricSeries,
    FormalMultilinearSeries.ofScalars_comp_neg_id]
  congr! with n
  rw [ordinaryHypergeometricCoefficient]; rw [mul_inv_cancel_right₀ (by simp [ascPochhammer_eval_eq_zero_iff]; grind)]
  simp only [Ring.choose_eq_smul, Polynomial.descPochhammer_smeval_eq_ascPochhammer,
    Polynomial.ascPochhammer_smeval_cast, Polynomial.ascPochhammer_smeval_eq_eval,
    ascPochhammer_eval_neg_eq_descPochhammer, descPochhammer_eval_eq_ascPochhammer]
  ring_nf
  simp

/--
theorem `binomialSeries_radius_eq_top_of_nat` / 定理 `binomialSeries_radius_eq_top_of_nat`

English:
theorem binomialSeries_radius_eq_top_of_nat
  statement: {𝕂 : Type v} [RCLike 𝕂] {𝔸 : Type u}
  proof: by
  simp [binomialSeries_eq_ordinaryHypergeometricSeries (b := (1 : 𝕂)) (by norm_cast; simp),
    ordinaryHypergeometric_radius_top_of_neg_nat₁]

中文:
定理 binomialSeries_radius_eq_top_of_nat
  结论: {𝕂 : 类型v} [RCLike 𝕂] {𝔸 : 类型u}
  证明: by
  simp [binomialSeries_eq_ordinaryHypergeometricSeries (b := (1 : 𝕂)) (by norm_cast; simp),
    ordinaryHypergeometric_radius_top_of_neg_nat₁]

Depends on / 依赖: binomialSeries_eq_ordinaryHypergeometricSeries
-/
theorem binomialSeries_radius_eq_top_of_nat {𝕂 : Type v} [RCLike 𝕂] {𝔸 : Type u}
    [NormedDivisionRing 𝔸] [NormedAlgebra 𝕂 𝔸] {a : Nat} :
    (binomialSeries 𝔸 (a : 𝕂)).radius = ⊤ := by
  simp [binomialSeries_eq_ordinaryHypergeometricSeries (b := (1 : 𝕂)) (by norm_cast; simp),
    ordinaryHypergeometric_radius_top_of_neg_nat₁]

/--
theorem `binomialSeries_radius_eq_one` / 定理 `binomialSeries_radius_eq_one`

English:
theorem binomialSeries_radius_eq_one
  statement: {𝕂 : Type v} [RCLike 𝕂] {𝔸 : Type u} [NormedDivisionRing 𝔸]
  proof: by
  simp only [binomialSeries_eq_ordinaryHypergeometricSeries (b := (1 : 𝕂)) (by norm_cast; simp),
    FormalMultilinearSeries.radius_compNeg]
  conv at ha => ext; rw [ne_comm]
  exact ordinaryHypergeometricSeries_radius_eq_one _ _ _ _ (by norm_cast; grind)

中文:
定理 binomialSeries_radius_eq_one
  结论: {𝕂 : 类型v} [RCLike 𝕂] {𝔸 : 类型u} [NormedDivision环 𝔸]
  证明: by
  simp only [binomialSeries_eq_ordinaryHypergeometricSeries (b := (1 : 𝕂)) (by norm_cast; simp),
    FormalMultilinearSeries.radius_compNeg]
  conv at ha => ext; rw [ne_comm]
  exact ordinaryHypergeometricSeries_radius_eq_one _ _ _ _ (by norm_cast; grind)

Depends on / 依赖: FormalMultilinearSeries, FormalMultilinearSeries.radius_compNeg, binomialSeries_eq_ordinaryHypergeometricSeries, ne_comm, ordinaryHypergeometricSeries_radius_eq_one, radius_compNeg
-/
theorem binomialSeries_radius_eq_one {𝕂 : Type v} [RCLike 𝕂] {𝔸 : Type u} [NormedDivisionRing 𝔸]
    [NormedAlgebra 𝕂 𝔸] {a : 𝕂} (ha : forall (k : Nat), a != k) : (binomialSeries 𝔸 a).radius = 1 := by
  simp only [binomialSeries_eq_ordinaryHypergeometricSeries (b := (1 : 𝕂)) (by norm_cast; simp),
    FormalMultilinearSeries.radius_compNeg]
  conv at ha => ext; rw [ne_comm]
  exact ordinaryHypergeometricSeries_radius_eq_one _ _ _ _ (by norm_cast; grind)

/--
theorem `binomialSeries_radius_ge_one` / 定理 `binomialSeries_radius_ge_one`

English:
theorem binomialSeries_radius_ge_one
  statement: {𝕂 : Type*} [RCLike 𝕂] {𝔸 : Type*} [NormedDivisionRing 𝔸]
  proof: by
  by_cases ha : forall (k : Nat), a != k
  · rw [binomialSeries_radius_eq_one ha]
  · push Not at ha
    rcases ha with ⟨k, rfl⟩
    simp [binomialSeries_radius_eq_top_of_nat]

中文:
定理 binomialSeries_radius_ge_one
  结论: {𝕂 : 类型} [RCLike 𝕂] {𝔸 : 类型} [NormedDivision环 𝔸]
  证明: by
  by_cases ha : forall (k : Nat), a != k
  · rw [binomialSeries_radius_eq_one ha]
  · push Not at ha
    rcases ha with ⟨k, rfl⟩
    simp [binomialSeries_radius_eq_top_of_nat]

Depends on / 依赖: binomialSeries_radius_eq_one, binomialSeries_radius_eq_top_of_nat
-/
theorem binomialSeries_radius_ge_one {𝕂 : Type*} [RCLike 𝕂] {𝔸 : Type*} [NormedDivisionRing 𝔸]
    [NormedAlgebra 𝕂 𝔸] {a : 𝕂} :
    1 <= (binomialSeries 𝔸 a).radius := by
  by_cases ha : forall (k : Nat), a != k
  · rw [binomialSeries_radius_eq_one ha]
  · push Not at ha
    rcases ha with ⟨k, rfl⟩
    simp [binomialSeries_radius_eq_top_of_nat]

namespace Complex

/--
theorem `one_add_cpow_hasFPowerSeriesOnBall_zero` / 定理 `one_add_cpow_hasFPowerSeriesOnBall_zero`

English:
theorem one_add_cpow_hasFPowerSeriesOnBall_zero
  given: {a : Complex}
  proof: by
  suffices (binomialSeries Complex a = FormalMultilinearSeries.ofScalars Complex
      fun n => iteratedDeriv n (fun (x : Complex) => (1 + x) ^ a) 0 / n !) by
    convert! AnalyticOn.hasFPowerSeriesOnSubball _ _ _
    · norm_num
    · -- TODO: use `fun_prop` for this subgoal
      apply AnalyticOn.cpow (analyticOn_const.add analyticOn_id) analyticOn_const
      intro z hz
      apply Complex.mem_slitPlane_of_norm_lt_one
      rw [← ENNReal.ofReal_one]; rw [Metric.eball_ofReal] at hz
      simpa using hz
    · rw [← this]
      exact binomialSeries_radius_ge_one
  simp only [binomialSeries, FormalMultilinearSeries.ofScalars_series_eq_iff]
  ext n
  rw [eq_div_iff_mul_eq (by simp [Nat.factorial_ne_zero]), ← nsmul_eq_mul',
    ← Ring.descPochhammer_eq_factorial_smul_choose]
  let B := Metric.ball (0 : Complex) 1
  suffices Set.EqOn (iteratedDerivWithin n (fun x => (1 + x) ^ a) B)
      (fun x => (descPochhammer Int n).smeval a * (1 + x) ^ (a - n)) B by
    specialize this (show 0 in _ by simp [B])
    rw [iteratedDerivWithin_of_isOpen Metric.isOpen_ball (by simp)] at this
    symm
    simpa using this
  induction n with
  | zero => simp [Set.EqOn]
  | succ n ih =>
    have : iteratedDerivWithin (n + 1) (fun (x : Complex) => (1 + x) ^ a) B =
        derivWithin (iteratedDerivWithin n (fun x => (1 + x) ^ a) B) B := by
      ext z
      rw [iteratedDerivWithin_succ]
    rw [this]
    have : Set.EqOn (derivWithin (iteratedDerivWithin n (fun (x : Complex) => (1 + x) ^ a) B) B)
        (derivWithin (fun x => (descPochhammer Int n).smeval a * (1 + x) ^ (a - ↑n)) B) B := by
      intro z hz
      rw [derivWithin_congr (fun _ hz => ih hz) (ih hz)]
    apply Set.EqOn.trans this
    intro z hz
    simp only [Nat.cast_add, Nat.cast_one, B, derivWithin_of_isOpen Metric.isOpen_ball hz,
      deriv_const_mul_field']
    rw [_root_.deriv_cpow_const (by fun_prop)]; rw [deriv_const_add_id]; rw [mul_one]; rw [show a - (n + 1) = a - n - 1 by ring]; rw [← mul_assoc]
    · congr
      simp [descPochhammer_succ_right, Polynomial.smeval_mul, Polynomial.smeval_natCast]
    · apply Complex.mem_slitPlane_of_norm_lt_one
      simpa [B] using hz

中文:
定理 one_add_cpow_hasFPowerSeriesOnBall_zero
  条件: {a : 复形}
  证明: by
  suffices (binomialSeries Complex a = FormalMultilinearSeries.ofScalars Complex
      fun n => iteratedDeriv n (fun (x : Complex) => (1 + x) ^ a) 0 / n !) by
    convert! AnalyticOn.hasFPowerSeriesOnSubball _ _ _
    · norm_num
    · -- TODO: use `fun_prop` for this subgoal
      apply AnalyticOn.cpow (analyticOn_const.add analyticOn_id) analyticOn_const
      intro z hz
      apply Complex.mem_slitPlane_of_norm_lt_one
      rw [← ENNReal.ofReal_one]; rw [Metric.eball_ofReal] at hz
      simpa using hz
    · rw [← this]
      exact binomialSeries_radius_ge_one
  simp only [binomialSeries, FormalMultilinearSeries.ofScalars_series_eq_iff]
  ext n
  rw [eq_div_iff_mul_eq (by simp [Nat.factorial_ne_zero]), ← nsmul_eq_mul',
    ← Ring.descPochhammer_eq_factorial_smul_choose]
  let B := Metric.ball (0 : Complex) 1
  suffices Set.EqOn (iteratedDerivWithin n (fun x => (1 + x) ^ a) B)
      (fun x => (descPochhammer Int n).smeval a * (1 + x) ^ (a - n)) B by
    specialize this (show 0 in _ by simp [B])
    rw [iteratedDerivWithin_of_isOpen Metric.isOpen_ball (by simp)] at this
    symm
    simpa using this
  induction n with
  | zero => simp [Set.EqOn]
  | succ n ih =>
    have : iteratedDerivWithin (n + 1) (fun (x : Complex) => (1 + x) ^ a) B =
        derivWithin (iteratedDerivWithin n (fun x => (1 + x) ^ a) B) B := by
      ext z
      rw [iteratedDerivWithin_succ]
    rw [this]
    have : Set.EqOn (derivWithin (iteratedDerivWithin n (fun (x : Complex) => (1 + x) ^ a) B) B)
        (derivWithin (fun x => (descPochhammer Int n).smeval a * (1 + x) ^ (a - ↑n)) B) B := by
      intro z hz
      rw [derivWithin_congr (fun _ hz => ih hz) (ih hz)]
    apply Set.EqOn.trans this
    intro z hz
    simp only [Nat.cast_add, Nat.cast_one, B, derivWithin_of_isOpen Metric.isOpen_ball hz,
      deriv_const_mul_field']
    rw [_root_.deriv_cpow_const (by fun_prop)]; rw [deriv_const_add_id]; rw [mul_one]; rw [show a - (n + 1) = a - n - 1 by ring]; rw [← mul_assoc]
    · congr
      simp [descPochhammer_succ_right, Polynomial.smeval_mul, Polynomial.smeval_natCast]
    · apply Complex.mem_slitPlane_of_norm_lt_one
      simpa [B] using hz

Depends on / 依赖: AnalyticOn, AnalyticOn.cpow, AnalyticOn.hasFPowerSeriesOnSubball, Complex.mem_slitPlane_of_norm_lt_one, ENNReal, ENNReal.ofReal_one, FormalMultilinearSeries, FormalMultilinearSeries.ofScalars, Metric, Metric.eball_ofReal, analyticOn_const, analyticOn_const.add, analyticOn_id, binomialSeries, binomialSeries_rad, convert, eball_ofReal, fun_prop, hasFPowerSeriesOnSubball, iteratedDeriv
-/
theorem one_add_cpow_hasFPowerSeriesOnBall_zero {a : Complex} :
    HasFPowerSeriesOnBall (fun x => (1 + x) ^ a) (binomialSeries Complex a) 0 1 := by
  suffices (binomialSeries Complex a = FormalMultilinearSeries.ofScalars Complex
      fun n => iteratedDeriv n (fun (x : Complex) => (1 + x) ^ a) 0 / n !) by
    convert! AnalyticOn.hasFPowerSeriesOnSubball _ _ _
    · norm_num
    · -- TODO: use `fun_prop` for this subgoal
      apply AnalyticOn.cpow (analyticOn_const.add analyticOn_id) analyticOn_const
      intro z hz
      apply Complex.mem_slitPlane_of_norm_lt_one
      rw [← ENNReal.ofReal_one]; rw [Metric.eball_ofReal] at hz
      simpa using hz
    · rw [← this]
      exact binomialSeries_radius_ge_one
  simp only [binomialSeries, FormalMultilinearSeries.ofScalars_series_eq_iff]
  ext n
  rw [eq_div_iff_mul_eq (by simp [Nat.factorial_ne_zero]), ← nsmul_eq_mul',
    ← Ring.descPochhammer_eq_factorial_smul_choose]
  let B := Metric.ball (0 : Complex) 1
  suffices Set.EqOn (iteratedDerivWithin n (fun x => (1 + x) ^ a) B)
      (fun x => (descPochhammer Int n).smeval a * (1 + x) ^ (a - n)) B by
    specialize this (show 0 in _ by simp [B])
    rw [iteratedDerivWithin_of_isOpen Metric.isOpen_ball (by simp)] at this
    symm
    simpa using this
  induction n with
  | zero => simp [Set.EqOn]
  | succ n ih =>
    have : iteratedDerivWithin (n + 1) (fun (x : Complex) => (1 + x) ^ a) B =
        derivWithin (iteratedDerivWithin n (fun x => (1 + x) ^ a) B) B := by
      ext z
      rw [iteratedDerivWithin_succ]
    rw [this]
    have : Set.EqOn (derivWithin (iteratedDerivWithin n (fun (x : Complex) => (1 + x) ^ a) B) B)
        (derivWithin (fun x => (descPochhammer Int n).smeval a * (1 + x) ^ (a - ↑n)) B) B := by
      intro z hz
      rw [derivWithin_congr (fun _ hz => ih hz) (ih hz)]
    apply Set.EqOn.trans this
    intro z hz
    simp only [Nat.cast_add, Nat.cast_one, B, derivWithin_of_isOpen Metric.isOpen_ball hz,
      deriv_const_mul_field']
    rw [_root_.deriv_cpow_const (by fun_prop)]; rw [deriv_const_add_id]; rw [mul_one]; rw [show a - (n + 1) = a - n - 1 by ring]; rw [← mul_assoc]
    · congr
      simp [descPochhammer_succ_right, Polynomial.smeval_mul, Polynomial.smeval_natCast]
    · apply Complex.mem_slitPlane_of_norm_lt_one
      simpa [B] using hz

/--
theorem `one_add_cpow_hasFPowerSeriesAt_zero` / 定理 `one_add_cpow_hasFPowerSeriesAt_zero`

English:
theorem one_add_cpow_hasFPowerSeriesAt_zero
  given: {a : Complex}
  proof: one_add_cpow_hasFPowerSeriesOnBall_zero.hasFPowerSeriesAt

中文:
定理 one_add_cpow_hasFPowerSeriesAt_zero
  条件: {a : 复形}
  证明: one_add_cpow_hasFPowerSeriesOnBall_zero.hasFPowerSeriesAt

Depends on / 依赖: hasFPowerSeriesAt, one_add_cpow_hasFPowerSeriesOnBall_zero, one_add_cpow_hasFPowerSeriesOnBall_zero.hasFPowerSeriesAt
-/
theorem one_add_cpow_hasFPowerSeriesAt_zero {a : Complex} :
    HasFPowerSeriesAt (fun x => (1 + x) ^ a) (binomialSeries Complex a) 0 :=
  one_add_cpow_hasFPowerSeriesOnBall_zero.hasFPowerSeriesAt

/--
theorem `one_div_one_sub_cpow_hasFPowerSeriesOnBall_zero` / 定理 `one_div_one_sub_cpow_hasFPowerSeriesOnBall_zero`

English:
theorem one_div_one_sub_cpow_hasFPowerSeriesOnBall_zero
  given: (a : Complex)
  proof: by
  have H : ((binomialSeries Complex (-a)).compContinuousLinearMap (-1)) =
      .ofScalars Complex fun n => Ring.choose (a + n - 1) n := by
    ext n; simp [FormalMultilinearSeries.compContinuousLinearMap, binomialSeries, Ring.choose_neg,
      Units.smul_def, ← pow_add, ← mul_assoc]
  have : HasFPowerSeriesOnBall (fun x => (1 + x) ^ (-a)) (binomialSeries Complex (-a : Complex)) (-0) 1 := by
    simpa using one_add_cpow_hasFPowerSeriesOnBall_zero
  simpa [cpow_neg, Function.comp_def, ← sub_eq_add_neg, H] using
    this.compContinuousLinearMap (u := -1) (x := (0 : Complex))

中文:
定理 one_div_one_sub_cpow_hasFPowerSeriesOnBall_zero
  条件: (a : 复形)
  证明: by
  have H : ((binomialSeries Complex (-a)).compContinuousLinearMap (-1)) =
      .ofScalars Complex fun n => Ring.choose (a + n - 1) n := by
    ext n; simp [FormalMultilinearSeries.compContinuousLinearMap, binomialSeries, Ring.choose_neg,
      Units.smul_def, ← pow_add, ← mul_assoc]
  have : HasFPowerSeriesOnBall (fun x => (1 + x) ^ (-a)) (binomialSeries Complex (-a : Complex)) (-0) 1 := by
    simpa using one_add_cpow_hasFPowerSeriesOnBall_zero
  simpa [cpow_neg, Function.comp_def, ← sub_eq_add_neg, H] using
    this.compContinuousLinearMap (u := -1) (x := (0 : Complex))

Depends on / 依赖: FormalMultilinearSeries, FormalMultilinearSeries.compContinuousLinearMap, Function, Function.comp_def, HasFPowerSeriesOnBall, Ring.choose, Ring.choose_neg, Units.smul_def, binomialSeries, choose_neg, compContinuousLinearMap, comp_def, cpow_neg, mul_assoc, ofScalars, one_add_cpow_hasFPowerSeriesOnBall_zero, pow_add, smul_def, sub_eq_add_neg, this.co
-/
theorem one_div_one_sub_cpow_hasFPowerSeriesOnBall_zero (a : Complex) :
    HasFPowerSeriesOnBall (fun x => 1 / (1 - x) ^ a)
      (.ofScalars Complex fun n => Ring.choose (a + n - 1) n) 0 1 := by
  have H : ((binomialSeries Complex (-a)).compContinuousLinearMap (-1)) =
      .ofScalars Complex fun n => Ring.choose (a + n - 1) n := by
    ext n; simp [FormalMultilinearSeries.compContinuousLinearMap, binomialSeries, Ring.choose_neg,
      Units.smul_def, ← pow_add, ← mul_assoc]
  have : HasFPowerSeriesOnBall (fun x => (1 + x) ^ (-a)) (binomialSeries Complex (-a : Complex)) (-0) 1 := by
    simpa using one_add_cpow_hasFPowerSeriesOnBall_zero
  simpa [cpow_neg, Function.comp_def, ← sub_eq_add_neg, H] using
    this.compContinuousLinearMap (u := -1) (x := (0 : Complex))

/--
theorem `one_div_one_sub_pow_hasFPowerSeriesOnBall_zero` / 定理 `one_div_one_sub_pow_hasFPowerSeriesOnBall_zero`

English:
theorem one_div_one_sub_pow_hasFPowerSeriesOnBall_zero
  given: (a : Nat)
  proof: by
  convert one_div_one_sub_cpow_hasFPowerSeriesOnBall_zero (a + 1) with z n
  · norm_cast
  · rw [eq_comm, add_right_comm, add_sub_cancel_right, ← Nat.cast_add,
      Ring.choose_natCast, Nat.choose_symm_add]

中文:
定理 one_div_one_sub_pow_hasFPowerSeriesOnBall_zero
  条件: (a : 自然数)
  证明: by
  convert one_div_one_sub_cpow_hasFPowerSeriesOnBall_zero (a + 1) with z n
  · norm_cast
  · rw [eq_comm, add_right_comm, add_sub_cancel_right, ← Nat.cast_add,
      Ring.choose_natCast, Nat.choose_symm_add]

Depends on / 依赖: Nat.cast_add, Nat.choose, Nat.choose_symm_add, Ring.choose_natCast, add_right_comm, add_sub_cancel_right, cast_add, choose_natCast, choose_symm_add, convert, eq_comm, one_div_one_sub_cpow_hasFPowerSeriesOnBall_zero
-/
theorem one_div_one_sub_pow_hasFPowerSeriesOnBall_zero (a : Nat) :
    HasFPowerSeriesOnBall (fun x => 1 / (1 - x) ^ (a + 1))
      (.ofScalars Complex (𝕜 := Complex) fun n => ↑(Nat.choose (a + n) a)) 0 1 := by
  convert one_div_one_sub_cpow_hasFPowerSeriesOnBall_zero (a + 1) with z n
  · norm_cast
  · rw [eq_comm, add_right_comm, add_sub_cancel_right, ← Nat.cast_add,
      Ring.choose_natCast, Nat.choose_symm_add]

/--
theorem `one_div_sub_pow_hasFPowerSeriesOnBall_zero` / 定理 `one_div_sub_pow_hasFPowerSeriesOnBall_zero`

English:
theorem one_div_sub_pow_hasFPowerSeriesOnBall_zero
  given: (a : Nat) {z : Complex} (hz : z != 0)
  proof: by
  have := one_div_one_sub_pow_hasFPowerSeriesOnBall_zero a
  rw [← map_zero (z⁻¹ • 1 : Complex ->L[Complex] Complex)] at this
  have := this.compContinuousLinearMap
  have H : 1 / ‖(z⁻¹ • 1 : Complex ->L[Complex] Complex)‖ₑ = ‖z‖ₑ := by simp [enorm_smul, enorm_inv, hz]
  simp only [one_div, FunLike.coe_smul, H, Function.comp_def] at this
  convert (this.const_smul (c := (z ^ (a + 1))⁻¹)).congr ?_
  · ext n
    simp only [FormalMultilinearSeries.smul_apply, smul_apply,
      FormalMultilinearSeries.compContinuousLinearMap_apply]
    simp [add_assoc, pow_add _ _ (a + 1), mul_assoc]
  · intro w hw
    simp [← mul_inv_rev, ← mul_pow, sub_mul, mul_right_comm _ w, hz]

中文:
定理 one_div_sub_pow_hasFPowerSeriesOnBall_zero
  条件: (a : 自然数) {z : 复形} (hz : z != 0)
  证明: by
  have := one_div_one_sub_pow_hasFPowerSeriesOnBall_zero a
  rw [← map_zero (z⁻¹ • 1 : Complex ->L[Complex] Complex)] at this
  have := this.compContinuousLinearMap
  have H : 1 / ‖(z⁻¹ • 1 : Complex ->L[Complex] Complex)‖ₑ = ‖z‖ₑ := by simp [enorm_smul, enorm_inv, hz]
  simp only [one_div, FunLike.coe_smul, H, Function.comp_def] at this
  convert (this.const_smul (c := (z ^ (a + 1))⁻¹)).congr ?_
  · ext n
    simp only [FormalMultilinearSeries.smul_apply, smul_apply,
      FormalMultilinearSeries.compContinuousLinearMap_apply]
    simp [add_assoc, pow_add _ _ (a + 1), mul_assoc]
  · intro w hw
    simp [← mul_inv_rev, ← mul_pow, sub_mul, mul_right_comm _ w, hz]

Depends on / 依赖: FormalMultiline, FunLike, FunLike.coe_smul, Function, Function.comp_def, Nat.choose, coe_smul, compContinuousLinearMap, comp_def, const_smul, convert, enorm_inv, enorm_smul, map_zero, one_div, one_div_one_sub_pow_hasFPowerSeriesOnBall_zero, this.compContinuousLinearMap, this.const_smul
-/
theorem one_div_sub_pow_hasFPowerSeriesOnBall_zero (a : Nat) {z : Complex} (hz : z != 0) :
    HasFPowerSeriesOnBall (fun x => 1 / (z - x) ^ (a + 1))
      (.ofScalars Complex (𝕜 := Complex) fun n => (z ^ (n + a + 1))⁻¹ * ↑(Nat.choose (a + n) a)) 0 ‖z‖ₑ := by
  have := one_div_one_sub_pow_hasFPowerSeriesOnBall_zero a
  rw [← map_zero (z⁻¹ • 1 : Complex ->L[Complex] Complex)] at this
  have := this.compContinuousLinearMap
  have H : 1 / ‖(z⁻¹ • 1 : Complex ->L[Complex] Complex)‖ₑ = ‖z‖ₑ := by simp [enorm_smul, enorm_inv, hz]
  simp only [one_div, FunLike.coe_smul, H, Function.comp_def] at this
  convert (this.const_smul (c := (z ^ (a + 1))⁻¹)).congr ?_
  · ext n
    simp only [FormalMultilinearSeries.smul_apply, smul_apply,
      FormalMultilinearSeries.compContinuousLinearMap_apply]
    simp [add_assoc, pow_add _ _ (a + 1), mul_assoc]
  · intro w hw
    simp [← mul_inv_rev, ← mul_pow, sub_mul, mul_right_comm _ w, hz]

/--
theorem `one_div_sub_hasFPowerSeriesOnBall_zero` / 定理 `one_div_sub_hasFPowerSeriesOnBall_zero`

English:
theorem one_div_sub_hasFPowerSeriesOnBall_zero
  given: {z : Complex} (hz : z != 0)
  proof: by
  simpa using one_div_sub_pow_hasFPowerSeriesOnBall_zero (a := 0) hz

中文:
定理 one_div_sub_hasFPowerSeriesOnBall_zero
  条件: {z : 复形} (hz : z != 0)
  证明: by
  simpa using one_div_sub_pow_hasFPowerSeriesOnBall_zero (a := 0) hz

Depends on / 依赖: one_div_sub_pow_hasFPowerSeriesOnBall_zero
-/
theorem one_div_sub_hasFPowerSeriesOnBall_zero {z : Complex} (hz : z != 0) :
    HasFPowerSeriesOnBall (fun x => 1 / (z - x)) (.ofScalars Complex fun n => (z ^ (n + 1))⁻¹) 0 ‖z‖ₑ := by
  simpa using one_div_sub_pow_hasFPowerSeriesOnBall_zero (a := 0) hz

/--
theorem `one_div_sub_sq_hasFPowerSeriesOnBall_zero` / 定理 `one_div_sub_sq_hasFPowerSeriesOnBall_zero`

English:
theorem one_div_sub_sq_hasFPowerSeriesOnBall_zero
  given: {z : Complex} (hz : z != 0)
  proof: by
  simpa [add_comm 1] using one_div_sub_pow_hasFPowerSeriesOnBall_zero 1 hz

中文:
定理 one_div_sub_sq_hasFPowerSeriesOnBall_zero
  条件: {z : 复形} (hz : z != 0)
  证明: by
  simpa [add_comm 1] using one_div_sub_pow_hasFPowerSeriesOnBall_zero 1 hz

Depends on / 依赖: add_comm, one_div_sub_pow_hasFPowerSeriesOnBall_zero
-/
theorem one_div_sub_sq_hasFPowerSeriesOnBall_zero {z : Complex} (hz : z != 0) :
    HasFPowerSeriesOnBall (fun x => 1 / (z - x) ^ 2)
      (.ofScalars Complex fun n => (z ^ (n + 2))⁻¹ * (n + 1)) 0 ‖z‖ₑ := by
  simpa [add_comm 1] using one_div_sub_pow_hasFPowerSeriesOnBall_zero 1 hz

/--
theorem `one_div_one_sub_hasFPowerSeriesOnBall_zero` / 定理 `one_div_one_sub_hasFPowerSeriesOnBall_zero`

English:
theorem one_div_one_sub_hasFPowerSeriesOnBall_zero
  proof: by
  simpa using! one_div_sub_hasFPowerSeriesOnBall_zero (z := 1)

中文:
定理 one_div_one_sub_hasFPowerSeriesOnBall_zero
  证明: by
  simpa using! one_div_sub_hasFPowerSeriesOnBall_zero (z := 1)

Depends on / 依赖: one_div_sub_hasFPowerSeriesOnBall_zero
-/
theorem one_div_one_sub_hasFPowerSeriesOnBall_zero :
    HasFPowerSeriesOnBall (fun x => 1 / (1 - x : Complex)) (.ofScalars (𝕜 := Complex) Complex 1) 0 1 := by
  simpa using! one_div_sub_hasFPowerSeriesOnBall_zero (z := 1)

/--
theorem `one_div_one_sub_sq_hasFPowerSeriesOnBall_zero` / 定理 `one_div_one_sub_sq_hasFPowerSeriesOnBall_zero`

English:
theorem one_div_one_sub_sq_hasFPowerSeriesOnBall_zero
  proof: by
  simpa using one_div_sub_sq_hasFPowerSeriesOnBall_zero (z := 1)

中文:
定理 one_div_one_sub_sq_hasFPowerSeriesOnBall_zero
  证明: by
  simpa using one_div_sub_sq_hasFPowerSeriesOnBall_zero (z := 1)

Depends on / 依赖: one_div_sub_sq_hasFPowerSeriesOnBall_zero
-/
theorem one_div_one_sub_sq_hasFPowerSeriesOnBall_zero :
    HasFPowerSeriesOnBall (fun x => 1 / (1 - x : Complex) ^ 2) (.ofScalars Complex fun n => (n + 1 : Complex)) 0 1 := by
  simpa using one_div_sub_sq_hasFPowerSeriesOnBall_zero (z := 1)

/--
theorem `hasFPowerSeriesOnBall_ofScalars_mul_add_zero` / 定理 `hasFPowerSeriesOnBall_ofScalars_mul_add_zero`

English:
theorem hasFPowerSeriesOnBall_ofScalars_mul_add_zero
  given: (a b : Complex)
  proof: by
  convert
    (one_div_one_sub_hasFPowerSeriesOnBall_zero.const_smul (c := b - a)).add
      (one_div_one_sub_sq_hasFPowerSeriesOnBall_zero.const_smul (c := a))
  · simp [div_eq_mul_inv]
  · ext; simp; ring

中文:
定理 hasFPowerSeriesOnBall_ofScalars_mul_add_zero
  条件: (a b : 复形)
  证明: by
  convert
    (one_div_one_sub_hasFPowerSeriesOnBall_zero.const_smul (c := b - a)).add
      (one_div_one_sub_sq_hasFPowerSeriesOnBall_zero.const_smul (c := a))
  · simp [div_eq_mul_inv]
  · ext; simp; ring

Depends on / 依赖: const_smul, convert, div_eq_mul_inv, one_div_one_sub_hasFPowerSeriesOnBall_zero, one_div_one_sub_hasFPowerSeriesOnBall_zero.const_smul, one_div_one_sub_sq_hasFPowerSeriesOnBall_zero, one_div_one_sub_sq_hasFPowerSeriesOnBall_zero.const_smul
-/
theorem hasFPowerSeriesOnBall_ofScalars_mul_add_zero (a b : Complex) :
    HasFPowerSeriesOnBall (fun x => (b - a) / (1 - x) + a / (1 - x) ^ 2)
      (.ofScalars Complex fun n => a * n + b) 0 1 := by
  convert
    (one_div_one_sub_hasFPowerSeriesOnBall_zero.const_smul (c := b - a)).add
      (one_div_one_sub_sq_hasFPowerSeriesOnBall_zero.const_smul (c := a))
  · simp [div_eq_mul_inv]
  · ext; simp; ring

/--
lemma `one_div_sub_sq_sub_one_div_sq_hasFPowerSeriesOnBall_zero` / 引理 `one_div_sub_sq_sub_one_div_sq_hasFPowerSeriesOnBall_zero`

English:
lemma one_div_sub_sq_sub_one_div_sq_hasFPowerSeriesOnBall_zero
  given: (w x : Complex) (hw : w != x)
  proof: by
  rw [← Pi.sub_def]; rw [← Pi.sub_def]; rw [FormalMultilinearSeries.ofScalars_sub]
  refine .sub ?_ ?_
  · simpa only [sub_sub_sub_cancel_right, zero_add, sub_sq_comm w, zpow_neg, zpow_natCast, mul_comm]
      using (one_div_sub_sq_hasFPowerSeriesOnBall_zero
        (z := w - x) (by simp [sub_eq_zero, hw])).comp_sub x
  · convert! hasFPowerSeriesOnBall_const.mono _ le_top
    · ext (_ | _) <;> simp [zpow_ofNat]
    · simpa [sub_eq_zero]

中文:
引理 one_div_sub_sq_sub_one_div_sq_hasFPowerSeriesOnBall_zero
  条件: (w x : 复形) (hw : w != x)
  证明: by
  rw [← Pi.sub_def]; rw [← Pi.sub_def]; rw [FormalMultilinearSeries.ofScalars_sub]
  refine .sub ?_ ?_
  · simpa only [sub_sub_sub_cancel_right, zero_add, sub_sq_comm w, zpow_neg, zpow_natCast, mul_comm]
      using (one_div_sub_sq_hasFPowerSeriesOnBall_zero
        (z := w - x) (by simp [sub_eq_zero, hw])).comp_sub x
  · convert! hasFPowerSeriesOnBall_const.mono _ le_top
    · ext (_ | _) <;> simp [zpow_ofNat]
    · simpa [sub_eq_zero]

Depends on / 依赖: FormalMultilinearSeries, FormalMultilinearSeries.ofScalars_sub, Pi.sub_def, comp_sub, convert, hasFPowerSeriesOnBall_const, hasFPowerSeriesOnBall_const.mono, le_top, mul_comm, ofScalars_sub, one_div_sub_sq_hasFPowerSeriesOnBall_zero, sub_def, sub_eq_zero, sub_sq_comm, sub_sub_sub_cancel_right, zero_add, zpow_natCast, zpow_neg, zpow_ofNat
-/
lemma one_div_sub_sq_sub_one_div_sq_hasFPowerSeriesOnBall_zero (w x : Complex) (hw : w != x) :
    HasFPowerSeriesOnBall (fun z => 1 / (z - w) ^ 2 - 1 / w ^ 2) (.ofScalars Complex
      fun i => (i + 1) * (w - x) ^ (-↑(i + 2) : Int) - i.casesOn (w ^ (-2 : Int)) 0) x ‖w - x‖ₑ := by
  rw [← Pi.sub_def]; rw [← Pi.sub_def]; rw [FormalMultilinearSeries.ofScalars_sub]
  refine .sub ?_ ?_
  · simpa only [sub_sub_sub_cancel_right, zero_add, sub_sq_comm w, zpow_neg, zpow_natCast, mul_comm]
      using (one_div_sub_sq_hasFPowerSeriesOnBall_zero
        (z := w - x) (by simp [sub_eq_zero, hw])).comp_sub x
  · convert! hasFPowerSeriesOnBall_const.mono _ le_top
    · ext (_ | _) <;> simp [zpow_ofNat]
    · simpa [sub_eq_zero]

end Complex

namespace Real

attribute [local simp← ] Complex.ofReal_choose in
attribute [-simp] FormalMultilinearSeries.apply_eq_prod_smul_coeff in
/--
theorem `one_add_rpow_hasFPowerSeriesOnBall_zero` / 定理 `one_add_rpow_hasFPowerSeriesOnBall_zero`

English:
theorem one_add_rpow_hasFPowerSeriesOnBall_zero
  given: {a : Real}
  proof: by
  have H : binomialSeries Complex a = (binomialSeries Complex (a : Complex)).restrictScalars (𝕜 := Real) := by aesop
  have : HasFPowerSeriesOnBall (fun x => (1 + x) ^ (a : Complex)) (binomialSeries Complex a) (.ofRealCLM 0) 1 :=
    Complex.ofRealCLM.map_zero ▸ H ▸ Complex.one_add_cpow_hasFPowerSeriesOnBall_zero.restrictScalars
  convert! (Complex.reCLM.comp_hasFPowerSeriesOnBall this.compContinuousLinearMap).congr ?_
  · ext; simp [Function.comp_def]
  · simp
  · intro x hx; simp_all; norm_cast

中文:
定理 one_add_rpow_hasFPowerSeriesOnBall_zero
  条件: {a : 实数}
  证明: by
  have H : binomialSeries Complex a = (binomialSeries Complex (a : Complex)).restrictScalars (𝕜 := Real) := by aesop
  have : HasFPowerSeriesOnBall (fun x => (1 + x) ^ (a : Complex)) (binomialSeries Complex a) (.ofRealCLM 0) 1 :=
    Complex.ofRealCLM.map_zero ▸ H ▸ Complex.one_add_cpow_hasFPowerSeriesOnBall_zero.restrictScalars
  convert! (Complex.reCLM.comp_hasFPowerSeriesOnBall this.compContinuousLinearMap).congr ?_
  · ext; simp [Function.comp_def]
  · simp
  · intro x hx; simp_all; norm_cast

Depends on / 依赖: Complex.ofRealCLM.map_zero, Complex.one_add_cpow_hasFPowerSeriesOnBall_zero.restrictScalars, Complex.reCLM.comp_hasFPowerSeriesOnBall, Function, Function.comp_def, HasFPowerSeriesOnBall, binomialSeries, compContinuousLinearMap, comp_def, comp_hasFPowerSeriesOnBall, convert, map_zero, ofRealCLM, one_add_cpow_hasFPowerSeriesOnBall_zero, restrictScalars, this.compContinuousLinearMap
-/
theorem one_add_rpow_hasFPowerSeriesOnBall_zero {a : Real} :
    HasFPowerSeriesOnBall (fun x => (1 + x) ^ a) (binomialSeries Real a) 0 1 := by
  have H : binomialSeries Complex a = (binomialSeries Complex (a : Complex)).restrictScalars (𝕜 := Real) := by aesop
  have : HasFPowerSeriesOnBall (fun x => (1 + x) ^ (a : Complex)) (binomialSeries Complex a) (.ofRealCLM 0) 1 :=
    Complex.ofRealCLM.map_zero ▸ H ▸ Complex.one_add_cpow_hasFPowerSeriesOnBall_zero.restrictScalars
  convert! (Complex.reCLM.comp_hasFPowerSeriesOnBall this.compContinuousLinearMap).congr ?_
  · ext; simp [Function.comp_def]
  · simp
  · intro x hx; simp_all; norm_cast

/--
theorem `one_add_rpow_hasFPowerSeriesAt_zero` / 定理 `one_add_rpow_hasFPowerSeriesAt_zero`

English:
theorem one_add_rpow_hasFPowerSeriesAt_zero
  given: {a : Real}
  proof: one_add_rpow_hasFPowerSeriesOnBall_zero.hasFPowerSeriesAt

中文:
定理 one_add_rpow_hasFPowerSeriesAt_zero
  条件: {a : 实数}
  证明: one_add_rpow_hasFPowerSeriesOnBall_zero.hasFPowerSeriesAt

Depends on / 依赖: hasFPowerSeriesAt, one_add_rpow_hasFPowerSeriesOnBall_zero, one_add_rpow_hasFPowerSeriesOnBall_zero.hasFPowerSeriesAt
-/
theorem one_add_rpow_hasFPowerSeriesAt_zero {a : Real} :
    HasFPowerSeriesAt (fun x => (1 + x) ^ a) (binomialSeries Real a) 0 :=
  one_add_rpow_hasFPowerSeriesOnBall_zero.hasFPowerSeriesAt

/--
theorem `one_div_one_sub_rpow_hasFPowerSeriesOnBall_zero` / 定理 `one_div_one_sub_rpow_hasFPowerSeriesOnBall_zero`

English:
theorem one_div_one_sub_rpow_hasFPowerSeriesOnBall_zero
  given: (a : Real)
  proof: by
  have := (Complex.one_div_one_sub_cpow_hasFPowerSeriesOnBall_zero a).restrictScalars (𝕜 := Real)
  rw [← Complex.ofRealCLM.map_zero] at this
  convert (Complex.reCLM.comp_hasFPowerSeriesOnBall this.compContinuousLinearMap).congr ?_
  · ext n
    simp only [ContinuousLinearMap.compFormalMultilinearSeries_apply,
      ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp_apply,
      FormalMultilinearSeries.compContinuousLinearMap_apply]
    simp
    norm_cast
  · simp
  · intro x hx
    have : |x| < 1 := by simpa [enorm_eq_nnnorm] using! hx
    have : 0 <= 1 - x := by grind
    simp [-Complex.inv_re, ← Complex.ofReal_one, ← Complex.ofReal_sub, ← Complex.ofReal_cpow this]

中文:
定理 one_div_one_sub_rpow_hasFPowerSeriesOnBall_zero
  条件: (a : 实数)
  证明: by
  have := (Complex.one_div_one_sub_cpow_hasFPowerSeriesOnBall_zero a).restrictScalars (𝕜 := Real)
  rw [← Complex.ofRealCLM.map_zero] at this
  convert (Complex.reCLM.comp_hasFPowerSeriesOnBall this.compContinuousLinearMap).congr ?_
  · ext n
    simp only [ContinuousLinearMap.compFormalMultilinearSeries_apply,
      ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp_apply,
      FormalMultilinearSeries.compContinuousLinearMap_apply]
    simp
    norm_cast
  · simp
  · intro x hx
    have : |x| < 1 := by simpa [enorm_eq_nnnorm] using! hx
    have : 0 <= 1 - x := by grind
    simp [-Complex.inv_re, ← Complex.ofReal_one, ← Complex.ofReal_sub, ← Complex.ofReal_cpow this]

Depends on / 依赖: Complex.ofRealCLM.map_zero, Complex.one_div_one_sub_cpow_hasFPowerSeriesOnBall_zero, Complex.reCLM.comp_hasFPowerSeriesOnBall, ContinuousLinearMap, ContinuousLinearMap.compContinuousMultilinearMap_coe, ContinuousLinearMap.compFormalMultilinearSeries_apply, FormalMultilinearSeries, FormalMultilinearSeries.compContinuousLinearMap_apply, Function, Function.comp_apply, compContinuousLinearMap, compContinuousLinearMap_apply, compContinuousMultilinearMap_coe, compFormalMultilinearSeries_apply, comp_apply, comp_hasFPowerSeriesOnBall, convert, map_zero, ofRealCLM, one_div_one_sub_cpow_hasFPowerSeriesOnBall_zero
-/
theorem one_div_one_sub_rpow_hasFPowerSeriesOnBall_zero (a : Real) :
    HasFPowerSeriesOnBall (fun x => 1 / (1 - x) ^ a)
      (.ofScalars Real fun n => Ring.choose (a + n - 1) n) 0 1 := by
  have := (Complex.one_div_one_sub_cpow_hasFPowerSeriesOnBall_zero a).restrictScalars (𝕜 := Real)
  rw [← Complex.ofRealCLM.map_zero] at this
  convert (Complex.reCLM.comp_hasFPowerSeriesOnBall this.compContinuousLinearMap).congr ?_
  · ext n
    simp only [ContinuousLinearMap.compFormalMultilinearSeries_apply,
      ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp_apply,
      FormalMultilinearSeries.compContinuousLinearMap_apply]
    simp
    norm_cast
  · simp
  · intro x hx
    have : |x| < 1 := by simpa [enorm_eq_nnnorm] using! hx
    have : 0 <= 1 - x := by grind
    simp [-Complex.inv_re, ← Complex.ofReal_one, ← Complex.ofReal_sub, ← Complex.ofReal_cpow this]

/--
theorem `one_div_sub_pow_hasFPowerSeriesOnBall_zero` / 定理 `one_div_sub_pow_hasFPowerSeriesOnBall_zero`

English:
theorem one_div_sub_pow_hasFPowerSeriesOnBall_zero
  given: (a : Nat) {r : Real} (hr : r != 0)
  proof: by
  have := (Complex.one_div_sub_pow_hasFPowerSeriesOnBall_zero a (z := r)
    (by simpa)).restrictScalars (𝕜 := Real)
  rw [← Complex.ofRealCLM.map_zero] at this
  convert (Complex.reCLM.comp_hasFPowerSeriesOnBall this.compContinuousLinearMap)
  · simp [-Complex.inv_re, ← Complex.ofReal_pow, ← Complex.ofReal_inv, ← Complex.ofReal_sub]
  · ext n
    simp only [ContinuousLinearMap.compFormalMultilinearSeries_apply,
      ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp_apply,
      FormalMultilinearSeries.compContinuousLinearMap_apply]
    simp [-Complex.inv_re, ← Complex.ofReal_pow, ← Complex.ofReal_inv]
  · simp [enorm_eq_nnnorm]

中文:
定理 one_div_sub_pow_hasFPowerSeriesOnBall_zero
  条件: (a : 自然数) {r : 实数} (hr : r != 0)
  证明: by
  have := (Complex.one_div_sub_pow_hasFPowerSeriesOnBall_zero a (z := r)
    (by simpa)).restrictScalars (𝕜 := Real)
  rw [← Complex.ofRealCLM.map_zero] at this
  convert (Complex.reCLM.comp_hasFPowerSeriesOnBall this.compContinuousLinearMap)
  · simp [-Complex.inv_re, ← Complex.ofReal_pow, ← Complex.ofReal_inv, ← Complex.ofReal_sub]
  · ext n
    simp only [ContinuousLinearMap.compFormalMultilinearSeries_apply,
      ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp_apply,
      FormalMultilinearSeries.compContinuousLinearMap_apply]
    simp [-Complex.inv_re, ← Complex.ofReal_pow, ← Complex.ofReal_inv]
  · simp [enorm_eq_nnnorm]

Depends on / 依赖: Complex.inv_re, Complex.ofRealCLM.map_zero, Complex.ofReal_inv, Complex.ofReal_pow, Complex.ofReal_sub, Complex.one_div_sub_pow_hasFPowerSeriesOnBall_zero, Complex.reCLM.comp_hasFPowerSeriesOnBall, ContinuousLinearMap, ContinuousLinearMap.compCon, ContinuousLinearMap.compFormalMultilinearSeries_apply, Nat.choose, compCon, compContinuousLinearMap, compFormalMultilinearSeries_apply, comp_hasFPowerSeriesOnBall, convert, inv_re, map_zero, ofRealCLM, ofReal_inv
-/
theorem one_div_sub_pow_hasFPowerSeriesOnBall_zero (a : Nat) {r : Real} (hr : r != 0) :
    HasFPowerSeriesOnBall (fun x => 1 / (r - x) ^ (a + 1))
      (.ofScalars Real (𝕜 := Real) fun n => (r ^ (n + a + 1))⁻¹ * ↑(Nat.choose (a + n) a)) 0 ‖r‖ₑ := by
  have := (Complex.one_div_sub_pow_hasFPowerSeriesOnBall_zero a (z := r)
    (by simpa)).restrictScalars (𝕜 := Real)
  rw [← Complex.ofRealCLM.map_zero] at this
  convert (Complex.reCLM.comp_hasFPowerSeriesOnBall this.compContinuousLinearMap)
  · simp [-Complex.inv_re, ← Complex.ofReal_pow, ← Complex.ofReal_inv, ← Complex.ofReal_sub]
  · ext n
    simp only [ContinuousLinearMap.compFormalMultilinearSeries_apply,
      ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp_apply,
      FormalMultilinearSeries.compContinuousLinearMap_apply]
    simp [-Complex.inv_re, ← Complex.ofReal_pow, ← Complex.ofReal_inv]
  · simp [enorm_eq_nnnorm]

/--
theorem `one_div_sub_hasFPowerSeriesOnBall_zero` / 定理 `one_div_sub_hasFPowerSeriesOnBall_zero`

English:
theorem one_div_sub_hasFPowerSeriesOnBall_zero
  given: {r : Real} (hr : r != 0)
  proof: by
  simpa using one_div_sub_pow_hasFPowerSeriesOnBall_zero (a := 0) hr

中文:
定理 one_div_sub_hasFPowerSeriesOnBall_zero
  条件: {r : 实数} (hr : r != 0)
  证明: by
  simpa using one_div_sub_pow_hasFPowerSeriesOnBall_zero (a := 0) hr

Depends on / 依赖: one_div_sub_pow_hasFPowerSeriesOnBall_zero
-/
theorem one_div_sub_hasFPowerSeriesOnBall_zero {r : Real} (hr : r != 0) :
    HasFPowerSeriesOnBall (fun x => 1 / (r - x)) (.ofScalars Real fun n => (r ^ (n + 1))⁻¹) 0 ‖r‖ₑ := by
  simpa using one_div_sub_pow_hasFPowerSeriesOnBall_zero (a := 0) hr

/--
theorem `one_div_sub_sq_hasFPowerSeriesOnBall_zero` / 定理 `one_div_sub_sq_hasFPowerSeriesOnBall_zero`

English:
theorem one_div_sub_sq_hasFPowerSeriesOnBall_zero
  given: {r : Real} (hr : r != 0)
  proof: by
  simpa [add_comm 1] using one_div_sub_pow_hasFPowerSeriesOnBall_zero 1 hr

中文:
定理 one_div_sub_sq_hasFPowerSeriesOnBall_zero
  条件: {r : 实数} (hr : r != 0)
  证明: by
  simpa [add_comm 1] using one_div_sub_pow_hasFPowerSeriesOnBall_zero 1 hr

Depends on / 依赖: add_comm, one_div_sub_pow_hasFPowerSeriesOnBall_zero
-/
theorem one_div_sub_sq_hasFPowerSeriesOnBall_zero {r : Real} (hr : r != 0) :
    HasFPowerSeriesOnBall (fun x => 1 / (r - x) ^ 2)
      (.ofScalars Real fun n => (r ^ (n + 2))⁻¹ * (n + 1)) 0 ‖r‖ₑ := by
  simpa [add_comm 1] using one_div_sub_pow_hasFPowerSeriesOnBall_zero 1 hr

/--
theorem `one_div_one_sub_hasFPowerSeriesOnBall_zero` / 定理 `one_div_one_sub_hasFPowerSeriesOnBall_zero`

English:
theorem one_div_one_sub_hasFPowerSeriesOnBall_zero
  proof: by
  simpa using! one_div_sub_hasFPowerSeriesOnBall_zero (r := 1)

中文:
定理 one_div_one_sub_hasFPowerSeriesOnBall_zero
  证明: by
  simpa using! one_div_sub_hasFPowerSeriesOnBall_zero (r := 1)

Depends on / 依赖: one_div_sub_hasFPowerSeriesOnBall_zero
-/
theorem one_div_one_sub_hasFPowerSeriesOnBall_zero :
    HasFPowerSeriesOnBall (fun x => 1 / (1 - x)) (.ofScalars (𝕜 := Real) Real 1) 0 1 := by
  simpa using! one_div_sub_hasFPowerSeriesOnBall_zero (r := 1)

/--
theorem `one_div_one_sub_sq_hasFPowerSeriesOnBall_zero` / 定理 `one_div_one_sub_sq_hasFPowerSeriesOnBall_zero`

English:
theorem one_div_one_sub_sq_hasFPowerSeriesOnBall_zero
  proof: by
  simpa using one_div_sub_sq_hasFPowerSeriesOnBall_zero (r := 1)

中文:
定理 one_div_one_sub_sq_hasFPowerSeriesOnBall_zero
  证明: by
  simpa using one_div_sub_sq_hasFPowerSeriesOnBall_zero (r := 1)

Depends on / 依赖: one_div_sub_sq_hasFPowerSeriesOnBall_zero
-/
theorem one_div_one_sub_sq_hasFPowerSeriesOnBall_zero :
    HasFPowerSeriesOnBall (fun x => 1 / (1 - x) ^ 2) (.ofScalars Real fun n => (n + 1 : Real)) 0 1 := by
  simpa using one_div_sub_sq_hasFPowerSeriesOnBall_zero (r := 1)

/--
theorem `hasFPowerSeriesOnBall_ofScalars_mul_add_zero` / 定理 `hasFPowerSeriesOnBall_ofScalars_mul_add_zero`

English:
theorem hasFPowerSeriesOnBall_ofScalars_mul_add_zero
  given: (a b : Real)
  proof: by
  convert!
    (one_div_one_sub_hasFPowerSeriesOnBall_zero.const_smul (c := b - a)).add
      (one_div_one_sub_sq_hasFPowerSeriesOnBall_zero.const_smul (c := a)) using 2
  · simp [div_eq_mul_inv]
  · ext; simp; ring

中文:
定理 hasFPowerSeriesOnBall_ofScalars_mul_add_zero
  条件: (a b : 实数)
  证明: by
  convert!
    (one_div_one_sub_hasFPowerSeriesOnBall_zero.const_smul (c := b - a)).add
      (one_div_one_sub_sq_hasFPowerSeriesOnBall_zero.const_smul (c := a)) using 2
  · simp [div_eq_mul_inv]
  · ext; simp; ring

Depends on / 依赖: const_smul, convert, div_eq_mul_inv, one_div_one_sub_hasFPowerSeriesOnBall_zero, one_div_one_sub_hasFPowerSeriesOnBall_zero.const_smul, one_div_one_sub_sq_hasFPowerSeriesOnBall_zero, one_div_one_sub_sq_hasFPowerSeriesOnBall_zero.const_smul
-/
theorem hasFPowerSeriesOnBall_ofScalars_mul_add_zero (a b : Real) :
    HasFPowerSeriesOnBall (fun x => (b - a) / (1 - x) + a / (1 - x) ^ 2)
      (.ofScalars Real (a * · + b)) 0 1 := by
  convert!
    (one_div_one_sub_hasFPowerSeriesOnBall_zero.const_smul (c := b - a)).add
      (one_div_one_sub_sq_hasFPowerSeriesOnBall_zero.const_smul (c := a)) using 2
  · simp [div_eq_mul_inv]
  · ext; simp; ring

end Real
