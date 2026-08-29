/-
Copyright (c) 2025 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
module

public import Mathlib.Analysis.Complex.Harmonic.Poisson
public import Mathlib.Analysis.SpecialFunctions.Integrals.PosLogEqCircleAverage

import Mathlib.Algebra.FiniteSupport.Basic

/-!
# Jensen's Formula of Complex Analysis

If a function `g : ℂ → ℂ` is analytic without zero on the closed ball with center `c` and radius
`R`, then `log ‖g ·‖` is harmonic, and the mean value theorem of harmonic functions asserts that the
circle average `circleAverage (log ‖g ·‖) c R` equals `log ‖g c‖`. Note that `g c` equals
`meromorphicTrailingCoeffAt g c` and see `AnalyticOnNhd.circleAverage_log_norm_of_ne_zero` for the
precise statement.

Jensen's Formula, formulated in `MeromorphicOn.circleAverage_log_norm` below, generalizes this to
the setting where `g` is merely meromorphic. In that case, the `circleAverage (log ‖g ·‖) c R`
equals `log ‖meromorphicTrailingCoeffAt g c‖` plus a correction term that accounts for the zeros and
poles of `g` within the ball.
-/

public section

open Filter MeromorphicAt MeasureTheory MeromorphicOn Metric Real Set Topology
open scoped ComplexConjugate



-- Auxiliary definitition for `circleAverage_re_herglotzRieszKernel_mul_log`. Shorthand for the
-- integrand in our computations
/--
Definition of `noncomputable` / `noncomputable` 的定义

English:
definition noncomputable
  signature: def herglotzLogIntegrand (w ρ : Complex)
  body: (Complex.re ∘ herglotzRieszKernel 0 w) • (Real.log ‖· - ρ‖)

中文:
定义 noncomputable
  签名: def herglotzLog整数egrand (w ρ : 复形)
  定义体: (Complex.re ∘ herglotzRieszKernel 0 w) • (Real.log ‖· - ρ‖)
-/
private noncomputable def herglotzLogIntegrand (w ρ : Complex) : Complex -> Real :=
  (Complex.re ∘ herglotzRieszKernel 0 w) • (Real.log ‖· - ρ‖)

-- Auxiliary lemma for `circleAverage_re_herglotzRieszKernel_mul_log`. Continuity of the
-- herglotzLogIntegrand.
/--
lemma `continuousAt_herglotzLogIntegrand` / 引理 `continuousAt_herglotzLogIntegrand`

English:
lemma continuousAt_herglotzLogIntegrand
  given: {w ρ z : Complex} (hz_w : z != w) (hz_ρ : z != ρ)
  proof: by
  have : ‖z - ρ‖ != 0 := by simp_all [sub_eq_zero]
  simp only [herglotzLogIntegrand, herglotzRieszKernel_fun_def, sub_zero, smul_eq_mul]
  fun_prop (disch := grind)

中文:
引理 continuousAt_herglotzLog整数egrand
  条件: {w ρ z : 复形} (hz_w : z != w) (hz_ρ : z != ρ)
  证明: by
  have : ‖z - ρ‖ != 0 := by simp_all [sub_eq_zero]
  simp only [herglotzLogIntegrand, herglotzRieszKernel_fun_def, sub_zero, smul_eq_mul]
  fun_prop (disch := grind)
-/
private lemma continuousAt_herglotzLogIntegrand {w ρ z : Complex} (hz_w : z != w) (hz_ρ : z != ρ) :
    ContinuousAt (herglotzLogIntegrand w ρ) z := by
  have : ‖z - ρ‖ != 0 := by simp_all [sub_eq_zero]
  simp only [herglotzLogIntegrand, herglotzRieszKernel_fun_def, sub_zero, smul_eq_mul]
  fun_prop (disch := grind)

-- Auxiliary lemma for `circleAverage_re_herglotzRieszKernel_mul_log`. Continuity of the
-- herglotzLogIntegrand.
/--
lemma `continuous_herglotzLogIntegrand_circle` / 引理 `continuous_herglotzLogIntegrand_circle`

English:
lemma continuous_herglotzLogIntegrand_circle
  statement: {w ρ : Complex} {R r : Real} (hρ : ‖ρ‖ = R)
  proof: by
  rw [continuous_iff_continuousAt]
  intro θ
  apply ContinuousAt.comp (continuousAt_herglotzLogIntegrand _ _) (by fun_prop)
  all_goals
    by_contra h
    grind [norm_circleMap_zero, lt_of_le_of_lt (Complex.norm_nonneg w) hwr]

中文:
引理 continuous_herglotzLog整数egrand_circle
  结论: {w ρ : 复形} {R r : 实数} (hρ : ‖ρ‖ = R)
  证明: by
  rw [continuous_iff_continuousAt]
  intro θ
  apply ContinuousAt.comp (continuousAt_herglotzLogIntegrand _ _) (by fun_prop)
  all_goals
    by_contra h
    grind [norm_circleMap_zero, lt_of_le_of_lt (Complex.norm_nonneg w) hwr]
-/
private lemma continuous_herglotzLogIntegrand_circle {w ρ : Complex} {R r : Real} (hρ : ‖ρ‖ = R)
    (hr_lt : r < R) (hwr : ‖w‖ < r) :
    Continuous (fun θ => herglotzLogIntegrand w ρ (circleMap 0 r θ)) := by
  rw [continuous_iff_continuousAt]
  intro θ
  apply ContinuousAt.comp (continuousAt_herglotzLogIntegrand _ _) (by fun_prop)
  all_goals
    by_contra h
    grind [norm_circleMap_zero, lt_of_le_of_lt (Complex.norm_nonneg w) hwr]

open Complex in
-- Auxiliary lemma for `circleAverage_re_herglotzRieszKernel_mul_log`. Computation for the
-- boundedness required by the dominated convergence theorem, Part I.
/--
lemma `const_mul_norm_sub_circleMap_le_norm_sub_circleMap` / 引理 `const_mul_norm_sub_circleMap_le_norm_sub_circleMap`

English:
lemma const_mul_norm_sub_circleMap_le_norm_sub_circleMap
  statement: {r₀ r R : Real} {ρ : Complex} (hρ : ‖ρ‖ = R)
  proof: by
  have h_cos_law (r₁ : Real) :
      ‖circleMap 0 r₁ θ - ρ‖ ^ 2 = r₁ ^ 2 + R ^ 2 - 2 * r₁ * R * Real.cos (θ - Complex.arg ρ) := by
    rw [← ofReal_inj]; rw [← normSq_eq_norm_sq]; rw [normSq_sub]
    suffices (circleMap 0 r₁ θ * (conj) ρ).re = r₁ * ‖ρ‖ * Real.cos (θ - ρ.arg) by
      simp [normSq

中文:
引理 const_mul_norm_sub_circleMap_le_norm_sub_circleMap
  结论: {r₀ r R : 实数} {ρ : 复形} (hρ : ‖ρ‖ = R)
  证明: by
  have h_cos_law (r₁ : Real) :
      ‖circleMap 0 r₁ θ - ρ‖ ^ 2 = r₁ ^ 2 + R ^ 2 - 2 * r₁ * R * Real.cos (θ - Complex.arg ρ) := by
    rw [← ofReal_inj]; rw [← normSq_eq_norm_sq]; rw [normSq_sub]
    suffices (circleMap 0 r₁ θ * (conj) ρ).re = r₁ * ‖ρ‖ * Real.cos (θ - ρ.arg) by
      simp [normSq
-/
private lemma const_mul_norm_sub_circleMap_le_norm_sub_circleMap {r₀ r R : Real} {ρ : Complex} (hρ : ‖ρ‖ = R)
    (hr₀ : 0 < r₀) (hR : 0 < R) (hr₀r : r₀ <= r) (hrR : r <= R) (θ : Real) :
    sqrt (r₀ / R) * ‖circleMap 0 R θ - ρ‖ <= ‖circleMap 0 r θ - ρ‖ := by
  have h_cos_law (r₁ : Real) :
      ‖circleMap 0 r₁ θ - ρ‖ ^ 2 = r₁ ^ 2 + R ^ 2 - 2 * r₁ * R * Real.cos (θ - Complex.arg ρ) := by
    rw [← ofReal_inj]; rw [← normSq_eq_norm_sq]; rw [normSq_sub]
    suffices (circleMap 0 r₁ θ * (conj) ρ).re = r₁ * ‖ρ‖ * Real.cos (θ - ρ.arg) by
      simp [normSq_eq_norm_sq, hρ, -mul_re, this, mul_assoc]
    conv_lhs => rw [← norm_mul_exp_arg_mul_I ρ, ← circleMap_zero, conj_circleMap_zero,
      circleMap_zero_mul, circleMap_zero_re, ← sub_eq_add_neg]
  have : (r₀ / R) * ‖circleMap 0 R θ - ρ‖ ^ 2 <= ‖circleMap 0 r θ - ρ‖ ^ 2 := by
    rw [div_mul_eq_mul_div]; rw [div_le_iff₀ hR]
    nlinarith [h_cos_law r, h_cos_law R, mul_le_mul_of_nonneg_left hr₀r hR.le,
      mul_le_mul_of_nonneg_left hrR hR.le, neg_one_le_cos, cos_le_one]
  grw [← sqrt_sq (norm_nonneg _), ← sqrt_mul (by positivity), this, sqrt_sq (norm_nonneg _)]

-- Auxiliary lemma for `circleAverage_re_herglotzRieszKernel_mul_log`. Computation for the
-- boundedness required by the dominated convergence theorem, Part II.
/--
lemma `norm_herglotzLogIntegrand_circleMap_le` / 引理 `norm_herglotzLogIntegrand_circleMap_le`

English:
lemma norm_herglotzLogIntegrand_circleMap_le
  statement: {w ρ : Complex} {R r₀ r : Real} (hR : 0 < R)
  proof: by
  simp only [herglotzLogIntegrand, Pi.smul_apply', Function.comp_apply, smul_eq_mul, norm_mul,
    norm_eq_abs]
  have ⟨hrw, hr⟩ : 0 < r₀ - ‖w‖ ∧ 0 < r := by grind
  have h_norm_sub₁ := const_mul_norm_sub_circleMap_le_norm_sub_circleMap hρ hr₀ hR hr₀r hrR θ
  have h_norm_sub₂ : 0 < ‖circleMap 0 r

中文:
引理 norm_herglotzLog整数egrand_circleMap_le
  结论: {w ρ : 复形} {R r₀ r : 实数} (hR : 0 < R)
  证明: by
  simp only [herglotzLogIntegrand, Pi.smul_apply', Function.comp_apply, smul_eq_mul, norm_mul,
    norm_eq_abs]
  have ⟨hrw, hr⟩ : 0 < r₀ - ‖w‖ ∧ 0 < r := by grind
  have h_norm_sub₁ := const_mul_norm_sub_circleMap_le_norm_sub_circleMap hρ hr₀ hR hr₀r hrR θ
  have h_norm_sub₂ : 0 < ‖circleMap 0 r
-/
private lemma norm_herglotzLogIntegrand_circleMap_le {w ρ : Complex} {R r₀ r : Real} (hR : 0 < R)
  (hρ : ‖ρ‖ = R) (hr₀ : 0 < r₀) (hw : ‖w‖ < r₀) (hr₀r : r₀ <= r) (hrR : r <= R) (θ : Real)
  (hdR : 0 < ‖circleMap 0 R θ - ρ‖) :
  ‖herglotzLogIntegrand w ρ (circleMap 0 r θ)‖ <= ((R + ‖w‖) / (r₀ - ‖w‖))
    * (|log (2 * R)| + |log (sqrt (r₀ / R))| + |log ‖circleMap 0 R θ - ρ‖|) := by
  simp only [herglotzLogIntegrand, Pi.smul_apply', Function.comp_apply, smul_eq_mul, norm_mul,
    norm_eq_abs]
  have ⟨hrw, hr⟩ : 0 < r₀ - ‖w‖ ∧ 0 < r := by grind
  have h_norm_sub₁ := const_mul_norm_sub_circleMap_le_norm_sub_circleMap hρ hr₀ hR hr₀r hrR θ
  have h_norm_sub₂ : 0 < ‖circleMap 0 r θ - ρ‖ := lt_of_lt_of_le (by positivity) h_norm_sub₁
  gcongr
  · simp only [herglotzRieszKernel_def, sub_zero]
    calc
     |((circleMap 0 r θ + w) / (circleMap 0 r θ - w)).re|
     _ <= ‖circleMap 0 r θ + w‖ / ‖circleMap 0 r θ - w‖ := by grw [Complex.abs_re_le_norm, norm_div]
     _ <= (r + ‖w‖) / (r - ‖w‖) := by
        grw [norm_add_le, ← norm_sub_norm_le]
        all_goals simp only [norm_circleMap_zero, abs_of_pos hr]; grind
      _ <= (R + ‖w‖) / (r₀ - ‖w‖) := by gcongr
  · apply abs_le.mpr ⟨_, _⟩
    · have h_log_lower_bound :
          log ‖circleMap 0 r θ - ρ‖ >= log (sqrt (r₀ / R)) + log ‖circleMap 0 R θ - ρ‖ := by
        rw [← log_mul (by positivity) (by positivity)]
        gcongr
      grind
    · calc log ‖circleMap 0 r θ - ρ‖
      _ <= |log (2 * R)| + 0 + 0 := by
        grw [← le_abs_self, norm_sub_le, hρ, two_mul, norm_circleMap_zero, abs_of_pos hr, hrR]
        simp
      _ <= |log (2 * R)| + |log √(r₀ / R)| + |log ‖circleMap 0 R θ - ρ‖| := by
        gcongr <;> positivity

-- Auxiliary lemma for `circleAverage_re_herglotzRieszKernel_mul_log`. Dominated convergence
-- theorem: circle average can be computed by a sequence of circle averages integrating over circles
-- in the interior
/--
theorem `herglotzLogIntegrand_circleAverage_tendsto` / 定理 `herglotzLogIntegrand_circleAverage_tendsto`

English:
theorem herglotzLogIntegrand_circleAverage_tendsto
  statement: {ρ w : Complex} {R : Real} (hR : 0 < R)
  proof: by
  -- Apply the dominated convergence theorem.
  let bound := fun θ => ((R + ‖w‖) / ((R + ‖w‖) / 2 - ‖w‖)) * (|log (2 * R)|
    + |log (sqrt ((R + ‖w‖) / 2 / R))| + |log ‖circleMap 0 R θ - ρ‖|)
  apply Filter.Tendsto.smul tendsto_const_nhds _
  apply intervalIntegral.tendsto_integral_filter_of_dom

中文:
定理 herglotzLog整数egrand_circleAverage_tendsto
  结论: {ρ w : 复形} {R : 实数} (hR : 0 < R)
  证明: by
  -- Apply the dominated convergence theorem.
  let bound := fun θ => ((R + ‖w‖) / ((R + ‖w‖) / 2 - ‖w‖)) * (|log (2 * R)|
    + |log (sqrt ((R + ‖w‖) / 2 / R))| + |log ‖circleMap 0 R θ - ρ‖|)
  apply Filter.Tendsto.smul tendsto_const_nhds _
  apply intervalIntegral.tendsto_integral_filter_of_dom
-/
private theorem herglotzLogIntegrand_circleAverage_tendsto {ρ w : Complex} {R : Real} (hR : 0 < R)
    (hρ : ‖ρ‖ = R) (hw : ‖w‖ < R) {r : Nat -> Real} (hr_lt : forall n, r n < R)
    (hr_tendsto : Tendsto r atTop (nhds R)) :
    Tendsto (fun n => circleAverage (herglotzLogIntegrand w ρ) 0 (r n)) atTop
      (nhds (circleAverage (herglotzLogIntegrand w ρ) 0 R)) := by
  -- Apply the dominated convergence theorem.
  let bound := fun θ => ((R + ‖w‖) / ((R + ‖w‖) / 2 - ‖w‖)) * (|log (2 * R)|
    + |log (sqrt ((R + ‖w‖) / 2 / R))| + |log ‖circleMap 0 R θ - ρ‖|)
  apply Filter.Tendsto.smul tendsto_const_nhds _
  apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence bound
  · -- The herglotzLogIntegrand is AEStronglyMeasurable
    filter_upwards [hr_tendsto.eventually (lt_mem_nhds hw)] with n hn
.aestronglyMeasurable exact continuous_herglotzLogIntegrand_circle hρ (hr_lt n) hn
  · -- Pointwise boundedness outside a null set
    filter_upwards [hr_tendsto.eventually (le_mem_nhds (by linarith : (R + ‖w‖) / 2 < R))] with n hn
    have h_bound {θ : Real} :
        ‖herglotzLogIntegrand w ρ (circleMap 0 (r n) θ)‖ <= bound θ ∨ ‖circleMap 0 R θ - ρ‖ = 0 := by
      refine Classical.or_iff_not_imp_right.mpr fun h => ?_
      apply norm_herglotzLogIntegrand_circleMap_le hR hρ (by positivity) (by linarith) hn
        (hr_lt n).le
      simpa using! h
    apply measure_mono_null (t := {θ | ‖circleMap 0 R θ - ρ‖ = 0}) (by grind)
    simpa [sub_eq_zero] using!
.measure_zero _ (countable_singleton ρ).preimage_circleMap 0 (hR.ne')
  · -- IntervalIntegrable bound volume 0 (2 * π)
.const_mul apply (IntervalIntegrable.add (by simp) (by simp)).add ?_
exact .abs MeromorphicOn.circleIntegrable_log_norm (f := fun z => z - ρ) (by intro; fun_prop)
  · -- Pointwise convergence outside a null set
    have h_measure_zero : volume {θ : Real | circleMap 0 R θ = w ∨ circleMap 0 R θ = ρ} = 0 :=
.union .preimage_circleMap 0 (hR.ne') countable_singleton w
.measure_zero _ ((countable_singleton ρ).preimage_circleMap 0 (hR.ne'))
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp h_measure_zero] with θ hθ _
    apply (continuousAt_herglotzLogIntegrand (by tauto) (by tauto)).tendsto.comp
exact tendsto_const_nhds.add
      (Complex.continuous_ofReal.continuousAt.tendsto.comp hr_tendsto).mul tendsto_const_nhds

-- Auxiliary lemma for `circleAverage_re_herglotzRieszKernel_mul_log`. Statement in case where the
-- center equals zero.
/--
theorem `circleAverage_re_herglotzRieszKernel_mul_log₀` / 定理 `circleAverage_re_herglotzRieszKernel_mul_log₀`

English:
theorem circleAverage_re_herglotzRieszKernel_mul_log₀
  statement: {w ρ : Complex} {R : Real} (hρ : ρ in sphere 0 R)
  proof: by
  have hR : 0 < R := pos_of_mem_ball hw
  rw [mem_sphere_iff_norm]; rw [sub_zero] at hρ
  rw [mem_ball_iff_norm]; rw [sub_zero] at hw
  let r : Nat -> Real := fun n => R - (R - ‖w‖) / (n + 2)
  have hr_lt (n : Nat) : r n < R := by
    simp_all only [sub_lt_self_iff, sub_pos, div_pos_iff_of_pos_le

中文:
定理 circleAverage_re_herglotzRieszKernel_mul_log₀
  结论: {w ρ : 复形} {R : 实数} (hρ : ρ in sphere 0 R)
  证明: by
  have hR : 0 < R := pos_of_mem_ball hw
  rw [mem_sphere_iff_norm]; rw [sub_zero] at hρ
  rw [mem_ball_iff_norm]; rw [sub_zero] at hw
  let r : Nat -> Real := fun n => R - (R - ‖w‖) / (n + 2)
  have hr_lt (n : Nat) : r n < R := by
    simp_all only [sub_lt_self_iff, sub_pos, div_pos_iff_of_pos_le

Depends on / 依赖: div_pos_iff_of_pos_left, hr_lt, hr_pos, mem_ball_iff_norm, mem_sphere_iff_norm, pos_of_mem_ball, sub_lt_self_iff, sub_pos, sub_zero
-/
theorem circleAverage_re_herglotzRieszKernel_mul_log₀ {w ρ : Complex} {R : Real} (hρ : ρ in sphere 0 R)
    (hw : w in ball 0 R) :
    circleAverage ((Complex.re ∘ herglotzRieszKernel 0 w) • (log ‖· - ρ‖)) (0 : Complex) R
      = log ‖w - ρ‖ := by
  have hR : 0 < R := pos_of_mem_ball hw
  rw [mem_sphere_iff_norm]; rw [sub_zero] at hρ
  rw [mem_ball_iff_norm]; rw [sub_zero] at hw
  let r : Nat -> Real := fun n => R - (R - ‖w‖) / (n + 2)
  have hr_lt (n : Nat) : r n < R := by
    simp_all only [sub_lt_self_iff, sub_pos, div_pos_iff_of_pos_left, r]
    positivity
  have hr_pos (n : Nat) : 0 < r n := by
    simp_all only [sub_lt_self_iff, sub_pos, div_pos_iff_of_pos_left, r]
    apply (div_lt_iff₀ (by linarith)).2
    calc R - ‖w‖
      _ <= R * 1 := by aesop
      _ < R * (n + 2) := by gcongr; grind
  have hr_tendsto : Tendsto r atTop (nhds R) :=
    sub_zero R ▸ (tendsto_const_nhds.sub <| tendsto_const_nhds.div_atTop <|
      tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop)
  have DCT := herglotzLogIntegrand_circleAverage_tendsto hR hρ hw hr_lt hr_tendsto
  have {n : Nat} : circleAverage (herglotzLogIntegrand w ρ) 0 (r n) = log ‖w - ρ‖ := by
    unfold herglotzLogIntegrand
    apply InnerProductSpace.HarmonicContOnCl.circleAverage_re_herglotzRieszKernel_smul
    · refine ⟨fun z hz => ?_, fun x hx => ?_⟩
      · exact AnalyticAt.harmonicAt_log_norm (by fun_prop) (by grind [mem_ball, dist_zero_right])
      · suffices ‖x - ρ‖ != 0 by fun_prop
        suffices x != ρ by simpa [sub_eq_zero]
        have key := by simpa using closure_ball_subset_closedBall hx
        grind
    · simp only [mem_ball, dist_zero_right, lt_sub_iff_add_lt, r]
      field_simp
      calc ‖w‖ * (n + 2) + (R - ‖w‖) = ‖w‖ * (n + 1) + R := by ring
        _ < R * (n + 1) + R := by gcongr
        _ = R * (n + 2) := by ring
  aesop

/--
theorem `circleAverage_re_herglotzRieszKernel_mul_log` / 定理 `circleAverage_re_herglotzRieszKernel_mul_log`

English:
theorem circleAverage_re_herglotzRieszKernel_mul_log
  statement: {w ρ c : Complex} {R : Real} (hρ : ρ in sphere c R)
  proof: by
  simp only [← circleAverage_map_add_const, Pi.mul_apply, Function.comp_apply, add_zero]
  conv =>
    left; arg 1
    intro z
    rw [(by ring : (z + 0 + c) - ρ = z - (ρ - c))]
    arg 1; arg 1
    rw [add_zero]; rw [herglotzRieszKernel_add_const c w z]
  have : (fun z => (herglotzRieszKernel 0 

中文:
定理 circleAverage_re_herglotzRieszKernel_mul_log
  结论: {w ρ c : 复形} {R : 实数} (hρ : ρ in sphere c R)
  证明: by
  simp only [← circleAverage_map_add_const, Pi.mul_apply, Function.comp_apply, add_zero]
  conv =>
    left; arg 1
    intro z
    rw [(by ring : (z + 0 + c) - ρ = z - (ρ - c))]
    arg 1; arg 1
    rw [add_zero]; rw [herglotzRieszKernel_add_const c w z]
  have : (fun z => (herglotzRieszKernel 0 

Depends on / 依赖: Complex.re, Function, Function.comp_apply, Pi.mul_apply, add_zero, circleAverage_map_add_const, comp_apply, herglotzRieszKernel, herglotzRieszKernel_add_const, mem_ball_iff_norm, mul_apply
-/
theorem circleAverage_re_herglotzRieszKernel_mul_log {w ρ c : Complex} {R : Real} (hρ : ρ in sphere c R)
    (hw : w in ball c R) :
    circleAverage ((Complex.re ∘ herglotzRieszKernel c w) * (log ‖· - ρ‖)) c R = log ‖w - ρ‖ := by
  simp only [← circleAverage_map_add_const, Pi.mul_apply, Function.comp_apply, add_zero]
  conv =>
    left; arg 1
    intro z
    rw [(by ring : (z + 0 + c) - ρ = z - (ρ - c))]
    arg 1; arg 1
    rw [add_zero]; rw [herglotzRieszKernel_add_const c w z]
  have : (fun z => (herglotzRieszKernel 0 (w - c) z).re * log ‖z - (ρ - c)‖) =
    (Complex.re ∘ herglotzRieszKernel 0 (w - c)) • (log ‖· - (ρ - c)‖) := by rfl
  rw [this]; rw [circleAverage_re_herglotzRieszKernel_mul_log₀ (by simp_all)
    (by simp_all [mem_ball_iff_norm.1 hw])]
  simp

/--
Let `D : ℂ → ℤ` be a function with locally finite support within the closed ball with center `c` and
radius `R`, such as the zero- and pole divisor of a meromorphic function. Then, the circle average
of the function `∑ᶠ u, (D u * log ‖· - u‖)` over the boundary of the ball equals
`∑ᶠ u, D u * log R`.
-/
@[simp]
/--
lemma `circleAverage_log_norm_factorizedRational` / 引理 `circleAverage_log_norm_factorizedRational`

English:
lemma circleAverage_log_norm_factorizedRational
  statement: {R : Real} {c : Complex}
  proof: by
  have h := D.finiteSupport (isCompact_closedBall c |R|)
  calc circleAverage (∑ᶠ u, (D u * log ‖· - u‖)) c R
  _ = circleAverage (∑ u in h.toFinset, (D u * log ‖· - u‖)) c R := by
    rw [finsum_eq_sum_of_support_subset]
    intro u
    contrapose
    aesop
  _ = ∑ i in h.toFinset, circleAverage

中文:
引理 circleAverage_log_norm_factorizedRational
  结论: {R : 实数} {c : 复形}
  证明: by
  have h := D.finiteSupport (isCompact_closedBall c |R|)
  calc circleAverage (∑ᶠ u, (D u * log ‖· - u‖)) c R
  _ = circleAverage (∑ u in h.toFinset, (D u * log ‖· - u‖)) c R := by
    rw [finsum_eq_sum_of_support_subset]
    intro u
    contrapose
    aesop
  _ = ∑ i in h.toFinset, circleAverage

Depends on / 依赖: D.finiteSupport, IntervalIntegrable, IntervalIntegrable.const_mul, analyticOnNhd_const, analyticOnNhd_id, analyticOnNhd_id.sub, circleAverage, circleAverage_sum, circleIntegrable_log_norm, const_mul, contrapose, finiteSupport, finsum_eq_sum_of_support_subset, h.toFinset, isCompact_closedBall, meromorphicOn, meromorphicOn.circleIntegrable_log_norm, toFinset
-/
lemma circleAverage_log_norm_factorizedRational {R : Real} {c : Complex}
    (D : Function.locallyFinsuppWithin (closedBall c |R|) Int) :
    circleAverage (∑ᶠ u, (D u * log ‖· - u‖)) c R = ∑ᶠ u, D u * log R := by
  have h := D.finiteSupport (isCompact_closedBall c |R|)
  calc circleAverage (∑ᶠ u, (D u * log ‖· - u‖)) c R
  _ = circleAverage (∑ u in h.toFinset, (D u * log ‖· - u‖)) c R := by
    rw [finsum_eq_sum_of_support_subset]
    intro u
    contrapose
    aesop
  _ = ∑ i in h.toFinset, circleAverage (fun x => D i * log ‖x - i‖) c R := by
    rw [circleAverage_sum]
    intro u hu
    apply IntervalIntegrable.const_mul
    apply (analyticOnNhd_id.sub analyticOnNhd_const).meromorphicOn.circleIntegrable_log_norm
  _ = ∑ u in h.toFinset, D u * log R := by
    apply Finset.sum_congr rfl
    intro u hu
    simp_rw [← smul_eq_mul, circleAverage_fun_smul]
    congr
    rw [circleAverage_log_norm_sub_const_of_mem_closedBall]
    apply D.supportWithinDomain
    simp_all
  _ = ∑ᶠ u, D u * log R := by
    rw [finsum_eq_sum_of_support_subset]
    intro u
    aesop

/--
If `g : ℂ → ℂ` is analytic without zero on the closed ball with center `c` and radius `R`, then the
circle average `circleAverage (log ‖g ·‖) c R` equals `log ‖g c‖`.
-/
@[simp]
/--
lemma `AnalyticOnNhd.circleAverage_log_norm_of_ne_zero` / 引理 `AnalyticOnNhd.circleAverage_log_norm_of_ne_zero`

English:
lemma AnalyticOnNhd.circleAverage_log_norm_of_ne_zero
  statement: {R : Real} {c : Complex} {g : Complex -> Complex}
  proof: InnerProductSpace.HarmonicOnNhd.circleAverage_eq
    (fun x hx => (h₁g x hx).harmonicAt_log_norm (h₂g x hx))

中文:
引理 AnalyticOnNhd.circleAverage_log_norm_of_ne_zero
  结论: {R : 实数} {c : 复形} {g : 复形 -> 复形}
  证明: InnerProductSpace.HarmonicOnNhd.circleAverage_eq
    (fun x hx => (h₁g x hx).harmonicAt_log_norm (h₂g x hx))

Depends on / 依赖: HarmonicOnNhd, InnerProductSpace, InnerProductSpace.HarmonicOnNhd.circleAverage_eq, circleAverage_eq, harmonicAt_log_norm
-/
lemma AnalyticOnNhd.circleAverage_log_norm_of_ne_zero {R : Real} {c : Complex} {g : Complex -> Complex}
    (h₁g : AnalyticOnNhd Complex g (closedBall c |R|)) (h₂g : forall u in closedBall c |R|, g u != 0) :
    circleAverage (Real.log ‖g ·‖) c R = Real.log ‖g c‖ :=
  InnerProductSpace.HarmonicOnNhd.circleAverage_eq
    (fun x hx => (h₁g x hx).harmonicAt_log_norm (h₂g x hx))

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `countingFunction_finsum_eq_finsum_add` / 引理 `countingFunction_finsum_eq_finsum_add`

English:
lemma countingFunction_finsum_eq_finsum_add
  statement: {c : Complex} {R : Real} {D : Complex -> Int} (hR : R != 0)
  proof: by
  by_cases h : c in D.support
  · have {g : Complex -> Real} : (fun u => D u * g u).support subseteq hD.toFinset :=
      fun x => by simp +contextual
    simp only [finsum_eq_sum_of_support_subset _ this,
      Finset.sum_eq_sum_sdiff_singleton_add ((Set.Finite.mem_toFinset hD).mpr h), sub_self,

中文:
引理 countingFunction_finsum_eq_finsum_add
  结论: {c : 复形} {R : 实数} {D : 复形 -> 整数} (hR : R != 0)
  证明: by
  by_cases h : c in D.support
  · have {g : Complex -> Real} : (fun u => D u * g u).support subseteq hD.toFinset :=
      fun x => by simp +contextual
    simp only [finsum_eq_sum_of_support_subset _ this,
      Finset.sum_eq_sum_sdiff_singleton_add ((Set.Finite.mem_toFinset hD).mpr h), sub_self,

Depends on / 依赖: D.support, Finite, Finset, Finset.mem_sdiff, Finset.notMem_singleton, Finset.sum_congr, Finset.sum_eq_sum_sdiff_singleton_add, Set.Finite.mem_toFinset, add_left_inj, add_zero, contextual, finsum_eq_sum_of_support_subset, hD.toFinset, inv_ne_zero, inv_zero, log_mul, log_zero, mem_sdiff, mem_toFinset, mul_zero
-/
lemma countingFunction_finsum_eq_finsum_add {c : Complex} {R : Real} {D : Complex -> Int} (hR : R != 0)
    (hD : D.HasFiniteSupport) :
    ∑ᶠ u, D u * (log R - log ‖c - u‖) = ∑ᶠ u, D u * log (R * ‖c - u‖⁻¹) + D c * log R := by
  by_cases h : c in D.support
  · have {g : Complex -> Real} : (fun u => D u * g u).support subseteq hD.toFinset :=
      fun x => by simp +contextual
    simp only [finsum_eq_sum_of_support_subset _ this,
      Finset.sum_eq_sum_sdiff_singleton_add ((Set.Finite.mem_toFinset hD).mpr h), sub_self,
      norm_zero, log_zero, sub_zero, inv_zero, mul_zero, add_zero, add_left_inj]
    refine Finset.sum_congr rfl fun x hx => ?_
    simp only [Finset.mem_sdiff, Finset.notMem_singleton] at hx
    rw [log_mul hR (inv_ne_zero (norm_ne_zero_iff.mpr (sub_eq_zero.not.2 hx.2.symm)))]; rw [log_inv]
    ring
  · simp_all only [Function.mem_support, Decidable.not_not, Int.cast_zero, zero_mul, add_zero]
    refine finsum_congr fun x => ?_
    by_cases h₁ : c = x
    · simp_all
    · rw [log_mul hR (inv_ne_zero (norm_ne_zero_iff.mpr (sub_eq_zero.not.2 h₁))), log_inv]
      ring

/-!
## Jensen's Formula
-/

/--
theorem `MeromorphicOn.circleAverage_log_norm` / 定理 `MeromorphicOn.circleAverage_log_norm`

English:
theorem MeromorphicOn.circleAverage_log_norm
  statement: {c : Complex} {R : Real} {f : Complex -> Complex} (hR : R != 0)
  proof: by
  -- Shorthand notation to keep line size in check
  let CB := closedBall c |R|
  by_cases h₂f : forall u in CB, meromorphicOrderAt f u != ⊤
  · have h₃f := (divisor f CB).finiteSupport (isCompact_closedBall c |R|)
    -- Extract zeros & poles and compute
    obtain ⟨g, h₁g, h₂g, h₃g⟩ := h₁f.extr

中文:
定理 MeromorphicOn.circleAverage_log_norm
  结论: {c : 复形} {R : 实数} {f : 复形 -> 复形} (hR : R != 0)
  证明: by
  -- Shorthand notation to keep line size in check
  let CB := closedBall c |R|
  by_cases h₂f : forall u in CB, meromorphicOrderAt f u != ⊤
  · have h₃f := (divisor f CB).finiteSupport (isCompact_closedBall c |R|)
    -- Extract zeros & poles and compute
    obtain ⟨g, h₁g, h₂g, h₃g⟩ := h₁f.extr
-/
theorem MeromorphicOn.circleAverage_log_norm {c : Complex} {R : Real} {f : Complex -> Complex} (hR : R != 0)
    (h₁f : MeromorphicOn f (closedBall c |R|)) :
    circleAverage (log ‖f ·‖) c R
      = ∑ᶠ u, divisor f (closedBall c |R|) u * log (R * ‖c - u‖⁻¹)
        + divisor f (closedBall c |R|) c * log R + log ‖meromorphicTrailingCoeffAt f c‖ := by
  -- Shorthand notation to keep line size in check
  let CB := closedBall c |R|
  by_cases h₂f : forall u in CB, meromorphicOrderAt f u != ⊤
  · have h₃f := (divisor f CB).finiteSupport (isCompact_closedBall c |R|)
    -- Extract zeros & poles and compute
    obtain ⟨g, h₁g, h₂g, h₃g⟩ := h₁f.extract_zeros_poles (by simp_all) h₃f
    calc circleAverage (log ‖f ·‖) c R
    _ = circleAverage ((∑ᶠ u, (divisor f CB u * log ‖· - u‖)) + (log ‖g ·‖)) c R := by
      have h₄g := extract_zeros_poles_log h₂g h₃g
      rw [circleAverage_congr_codiscreteWithin (codiscreteWithin_mono sphere_subset_closedBall h₄g)
        hR]
    _ = circleAverage (∑ᶠ u, (divisor f CB u * log ‖· - u‖)) c R + circleAverage (log ‖g ·‖) c R :=
      circleAverage_add (circleIntegrable_log_norm_factorizedRational (divisor f CB))
        ((h₁g.mono sphere_subset_closedBall).meromorphicOn.circleIntegrable_log_norm)
    _ = ∑ᶠ u, divisor f CB u * log R + log ‖g c‖ := by
      simp only [circleAverage_log_norm_factorizedRational, add_right_inj]
      rw [h₁g.circleAverage_log_norm_of_ne_zero]
      exact fun u hu => h₂g ⟨u, hu⟩
    _ = ∑ᶠ u, divisor f CB u * log R
      + (log ‖meromorphicTrailingCoeffAt f c‖ - ∑ᶠ u, divisor f CB u * log ‖c - u‖) := by
      have t₀ : c in CB := by simp [CB]
      have t₁ : AccPt c (𝓟 CB) := by
        apply accPt_iff_frequently_nhdsNE.mpr
        apply compl_notMem
        apply mem_nhdsWithin.mpr
        use ball c |R|
        simpa [hR] using! fun _ ⟨h, _⟩ => ball_subset_closedBall h
      simp [MeromorphicOn.log_norm_meromorphicTrailingCoeffAt_extract_zeros_poles h₃f t₀ t₁
        (h₁f c t₀) (h₁g c t₀) (h₂g ⟨c, t₀⟩) h₃g]
    _ = ∑ᶠ u, divisor f CB u * log R - ∑ᶠ u, divisor f CB u * log ‖c - u‖
      + log ‖meromorphicTrailingCoeffAt f c‖ := by
      ring
    _ = (∑ᶠ u, divisor f CB u * (log R - log ‖c - u‖)) + log ‖meromorphicTrailingCoeffAt f c‖ := by
      rw [← finsum_sub_distrib]
      · simp_rw [← mul_sub]
      repeat apply h₃f.subset (fun _ => (by simp_all))
    _ = ∑ᶠ u, divisor f CB u * log (R * ‖c - u‖⁻¹) + divisor f CB c * log R
      + log ‖meromorphicTrailingCoeffAt f c‖ := by
      rw [countingFunction_finsum_eq_finsum_add hR h₃f]
  · -- Trivial case: `f` vanishes on a codiscrete set
    have h₂f : ¬forall (u : ↑(closedBall c |R|)), meromorphicOrderAt f ↑u != ⊤ := by aesop
    rw [← h₁f.exists_meromorphicOrderAt_ne_top_iff_forall
      ⟨nonempty_closedBall.mpr (abs_nonneg R)]; rw [(convex_closedBall c |R|).isPreconnected⟩] at h₂f
    push Not at h₂f
    have : divisor f CB = 0 := by
      ext x
      by_cases h : x in CB
      <;> simp_all [CB]
    simp only [CB, this, Function.locallyFinsuppWithin.coe_zero, Pi.zero_apply, Int.cast_zero,
      zero_mul, finsum_zero, add_zero, zero_add]
    rw [MeromorphicAt.meromorphicTrailingCoeffAt_of_order_eq_top (by aesop)]; rw [norm_zero]; rw [log_zero]
    have : f =ᶠ[codiscreteWithin CB] 0 := by
      filter_upwards [h₁f.meromorphicNFAt_mem_codiscreteWithin, self_mem_codiscreteWithin CB]
        with z h₁z h₂z
      simpa [h₂f ⟨z, h₂z⟩] using (not_iff_not.2 h₁z.meromorphicOrderAt_eq_zero_iff)
    rw [circleAverage_congr_codiscreteWithin (f₂ := 0) _ hR]
    · simp only [circleAverage, mul_inv_rev, Pi.zero_apply, intervalIntegral.integral_zero,
        smul_eq_mul, mul_zero]
    apply Filter.codiscreteWithin_mono (U := CB) sphere_subset_closedBall
    filter_upwards [this] with z hz
    simp_all

/--
theorem `AnalyticOnNhd.circleAverage_log_norm` / 定理 `AnalyticOnNhd.circleAverage_log_norm`

English:
theorem AnalyticOnNhd.circleAverage_log_norm
  statement: {c : Complex} {R : Real} {f : Complex -> Complex} (hR : R != 0)
  proof: by
  rw [h₁f.meromorphicOn.circleAverage_log_norm hR]; rw [h₁f.divisor_apply (by simp)]; rw [(h₁f c (by simp)).analyticOrderAt_eq_zero.mpr h₂f]; rw [(h₁f c (by simp)).meromorphicTrailingCoeffAt_of_ne_zero h₂f]
  simp

中文:
定理 AnalyticOnNhd.circleAverage_log_norm
  结论: {c : 复形} {R : 实数} {f : 复形 -> 复形} (hR : R != 0)
  证明: by
  rw [h₁f.meromorphicOn.circleAverage_log_norm hR]; rw [h₁f.divisor_apply (by simp)]; rw [(h₁f c (by simp)).analyticOrderAt_eq_zero.mpr h₂f]; rw [(h₁f c (by simp)).meromorphicTrailingCoeffAt_of_ne_zero h₂f]
  simp

Depends on / 依赖: analyticOrderAt_eq_zero, analyticOrderAt_eq_zero.mpr, circleAverage_log_norm, divisor_apply, f.divisor_apply, f.meromorphicOn.circleAverage_log_norm, meromorphicOn, meromorphicTrailingCoeffAt_of_ne_zero
-/
theorem AnalyticOnNhd.circleAverage_log_norm {c : Complex} {R : Real} {f : Complex -> Complex} (hR : R != 0)
    (h₁f : AnalyticOnNhd Complex f (closedBall c |R|))
    (h₂f : f c != 0) :
    circleAverage (Real.log ‖f ·‖) c R
      = ∑ᶠ u, divisor f (closedBall c |R|) u * Real.log (R * ‖c - u‖⁻¹) + Real.log ‖f c‖ := by
  rw [h₁f.meromorphicOn.circleAverage_log_norm hR]; rw [h₁f.divisor_apply (by simp)]; rw [(h₁f c (by simp)).analyticOrderAt_eq_zero.mpr h₂f]; rw [(h₁f c (by simp)).meromorphicTrailingCoeffAt_of_ne_zero h₂f]
  simp

/--
theorem `AnalyticOnNhd.sum_divisor_le` / 定理 `AnalyticOnNhd.sum_divisor_le`

English:
theorem AnalyticOnNhd.sum_divisor_le
  statement: {c : Complex} {r R M : Real} {f : Complex -> Complex} (r_pos : 0 < |r|)
  proof: by
  -- Push the coerssion inside the sum
  trans ∑ᶠ u, (divisor f (closedBall c |r|) u : Real)
  · exact map_finsum (Int.castRingHom Real)
.le ((divisor _ _).finiteSupport <| isCompact_closedBall ..)
  -- Rearrange: move `log R/r` to the LHS and inside the sum.
  have hrR : 1 < |R / r| := by simpa 

中文:
定理 AnalyticOnNhd.sum_divisor_le
  结论: {c : 复形} {r R M : 实数} {f : 复形 -> 复形} (r_pos : 0 < |r|)
  证明: by
  -- Push the coerssion inside the sum
  trans ∑ᶠ u, (divisor f (closedBall c |r|) u : Real)
  · exact map_finsum (Int.castRingHom Real)
.le ((divisor _ _).finiteSupport <| isCompact_closedBall ..)
  -- Rearrange: move `log R/r` to the LHS and inside the sum.
  have hrR : 1 < |R / r| := by simpa 
-/
theorem AnalyticOnNhd.sum_divisor_le {c : Complex} {r R M : Real} {f : Complex -> Complex} (r_pos : 0 < |r|)
    (r_lt_R : |r| < |R|) (hM : 1 <= M) (h₁f : AnalyticOnNhd Complex f (closedBall c |R|))
    (h₂f : f c != 0)
    (f_bound : forall z in sphere c |R|, ‖f z‖ <= M) :
    ∑ᶠ u, divisor f (closedBall c |r|) u <= Real.log (M / ‖f c‖) / Real.log (R / r) := by
  -- Push the coerssion inside the sum
  trans ∑ᶠ u, (divisor f (closedBall c |r|) u : Real)
  · exact map_finsum (Int.castRingHom Real)
.le ((divisor _ _).finiteSupport <| isCompact_closedBall ..)
  -- Rearrange: move `log R/r` to the LHS and inside the sum.
  have hrR : 1 < |R / r| := by simpa [abs_div, one_lt_div r_pos]
  suffices ∑ᶠ u, divisor f (closedBall c |r|) u * Real.log (R / r) <= Real.log (M / ‖f c‖) by
    rwa [← finsum_mul, ← le_div_iff₀] at this
    simpa using log_pos hrR
  have jensen := h₁f.circleAverage_log_norm (abs_ne_zero.mp (by linarith)) h₂f
  -- Estimate the circleAverage using the bound on f
  have integral_bound : circleAverage (fun x => Real.log ‖f x‖) c R <= Real.log M := by
    apply circleAverage_mono_on_of_le_circle
    · exact (h₁f.mono sphere_subset_closedBall).meromorphicOn.circleIntegrable_log_norm
    · peel f_bound with z hz _
      obtain (h | h) := eq_zero_or_norm_pos (f z)
      · simpa [h] using log_nonneg hM
      · gcongr
  calc
  -- Bound by the sum from Jensen's formula
  _ <= ∑ᶠ u, ((divisor f (closedBall c |R|)) u) * Real.log (R * ‖c - u‖⁻¹) := by
    refine finsum_le_finsum' ?_ ?_ fun u => ?_
.subset · exact (divisor f (closedBall c |r|)).finiteSupport (isCompact_closedBall ..)
        fun _ _ => (by simp_all)
.subset · exact (divisor f (closedBall c |R|)).finiteSupport (isCompact_closedBall ..)
        fun _ _ => (by simp_all)
    · -- Core bound: estimate the summand by splitting on which ball u is in
      by_cases h1 : u in closedBall c |R|
      · by_cases h2 : u in closedBall c |r|
        · --In the smaller ball: the divisors agree and we bound the log factor
          simp only [(h₁f.mono (closedBall_subset_closedBall r_lt_R.le)), h2,
            AnalyticOnNhd.divisor_apply, h₁f, h1]
          by_cases! h3 : u = c --Need to use the divisor is 0 at c rather than comparing the logs
          · rw [h3, (h₁f c (by simp)).analyticOrderAt_eq_zero.mpr h₂f]
            simp
          simp +singlePass only [← log_abs]
          gcongr 2
          · simp
          · have : ‖c - u‖ != 0 := by simpa [sub_eq_zero] using h3.symm
            simpa [field, abs_div, r_pos.trans r_lt_R, dist_eq_norm'] using h2
        · --In the larger ball but not the smaller so LHS is 0 and RHS nonnegative
          simp only [h2, not_false_eq_true, Function.locallyFinsuppWithin.apply_eq_zero_of_notMem,
            Int.cast_zero, zero_mul]
          refine mul_nonneg (mod_cast h₁f.divisor_nonneg ..) ?_
          apply log_abs _ ▸ log_nonneg
          simp only [mem_closedBall, dist_eq_norm', not_le] at h1 h2
          have : ‖c - u‖ != 0 := (r_pos.trans h2).ne'
          simpa [field]
      · --Outside the larger ball so both sides are 0
        have : u ∉ closedBall c |r| := by
          simp_all
          linarith
        simp [h1, this]
  _ <= Real.log M - Real.log ‖f c‖ := by linarith --Uses jensen and integral_bound
  _ = _ := by rw [← log_div (by linarith) (norm_ne_zero_iff.mpr h₂f)]
