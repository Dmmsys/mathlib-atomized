/-
Copyright (c) 2025 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
module

public import Mathlib.Analysis.Complex.Harmonic.MeanValue
public import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.Integrals.LogTrigonometric
public import Mathlib.MeasureTheory.Integral.CircleAverage

/-!
# Representation of `log⁺` as a Circle Average

If `a` is any complex number, `circleAverage_log_norm_sub_const_eq_posLog` represents `log⁺ a` as
the circle average of `log ‖· - a‖` over the unit circle.
-/

public section

open Filter Interval intervalIntegral MeasureTheory Metric Real

variable {a c : Complex} {R : Real}

/-!
## Circle Integrability
-/

/--
If `a` is any complex number, the function `(log ‖· - a‖)` is circle integrable over every circle.
-/
@[fun_prop]
/--
lemma `circleIntegrable_log_norm_sub_const` / 引理 `circleIntegrable_log_norm_sub_const`

English:
lemma circleIntegrable_log_norm_sub_const
  given: (r : Real)
  statement: CircleIntegrable (log ‖· - a‖) c r
  proof: MeromorphicOn.circleIntegrable_log_norm (fun z hz => by fun_prop)

中文:
引理 circleIntegrable_log_norm_sub_const
  条件: (r : 实数)
  结论: Circle整数egrable (log ‖· - a‖) c r
  证明: MeromorphicOn.circleIntegrable_log_norm (fun z hz => by fun_prop)

Depends on / 依赖: MeromorphicOn, MeromorphicOn.circleIntegrable_log_norm, circleIntegrable_log_norm, fun_prop
-/
lemma circleIntegrable_log_norm_sub_const (r : Real) : CircleIntegrable (log ‖· - a‖) c r :=
  MeromorphicOn.circleIntegrable_log_norm (fun z hz => by fun_prop)

/-!
## Computing `circleAverage (log ‖· - a‖) 0 1` in case where `‖a‖ < 1`.
-/

/--
If `a : ℂ` has norm smaller than one, then `circleAverage (log ‖· - a‖) 0 1` vanishes.
-/
@[simp]
/--
theorem `circleAverage_log_norm_sub_const₀` / 定理 `circleAverage_log_norm_sub_const₀`

English:
theorem circleAverage_log_norm_sub_const₀
  given: (h : ‖a‖ < 1)
  statement: circleAverage (log ‖· - a‖) 0 1 = 0
  proof: by
  calc circleAverage (log ‖· - a‖) 0 1
  _ = circleAverage (log ‖1 - ·⁻¹ * a‖) 0 1 := by
    apply circleAverage_congr_sphere
    intro z hz
    simp_all only [abs_one, mem_sphere_iff_norm, sub_zero]
    congr 1
    have : z != 0 := fun h => by simp [h] at hz
    calc ‖z - a‖
    _ = ‖z⁻¹ * (z - 

中文:
定理 circleAverage_log_norm_sub_const₀
  条件: (h : ‖a‖ < 1)
  结论: circleAverage (log ‖· - a‖) 0 1 = 0
  证明: by
  calc circleAverage (log ‖· - a‖) 0 1
  _ = circleAverage (log ‖1 - ·⁻¹ * a‖) 0 1 := by
    apply circleAverage_congr_sphere
    intro z hz
    simp_all only [abs_one, mem_sphere_iff_norm, sub_zero]
    congr 1
    have : z != 0 := fun h => by simp [h] at hz
    calc ‖z - a‖
    _ = ‖z⁻¹ * (z - 

Depends on / 依赖: HarmonicOnNhd, InnerProductSpace, InnerProductSpace.HarmonicOnNhd.circleAverage_eq, abs_one, circleAverage, circleAverage_congr_sphere, circleAverage_eq, circleAverage_zero_one_congr_inv, mem_sphere_iff_norm, sub_zero, zero_mul
-/
theorem circleAverage_log_norm_sub_const₀ (h : ‖a‖ < 1) : circleAverage (log ‖· - a‖) 0 1 = 0 := by
  calc circleAverage (log ‖· - a‖) 0 1
  _ = circleAverage (log ‖1 - ·⁻¹ * a‖) 0 1 := by
    apply circleAverage_congr_sphere
    intro z hz
    simp_all only [abs_one, mem_sphere_iff_norm, sub_zero]
    congr 1
    have : z != 0 := fun h => by simp [h] at hz
    calc ‖z - a‖
    _ = ‖z⁻¹ * (z - a)‖ := by simp [hz]
    _ = ‖1 - z⁻¹ * a‖ := by field_simp
  _ = 0 := by
    rw [circleAverage_zero_one_congr_inv (f := fun x => log ‖1 - x * a‖)]; rw [InnerProductSpace.HarmonicOnNhd.circleAverage_eq]; rw [zero_mul]; rw [sub_zero]; rw [CStarRing.norm_of_mem_unitary (unitary Complex).one_mem]; rw [log_one]
    intro x hx
    have : ‖x * a‖ < 1 := by
      calc ‖x * a‖
      _ = ‖x‖ * ‖a‖ := by simp
      _ <= ‖a‖ := mul_le_of_le_one_left (norm_nonneg _) (by aesop)
      _ < 1 := h
    apply AnalyticAt.harmonicAt_log_norm (by fun_prop)
    rw [sub_ne_zero]
    by_contra! hCon
    rwa [← hCon, CStarRing.norm_of_mem_unitary (unitary Complex).one_mem, lt_self_iff_false] at this


-- Integral computation used in `circleAverage_log_norm_id_sub_const₁`
/--
lemma `circleAverage_log_norm_sub_const₁_integral` / 引理 `circleAverage_log_norm_sub_const₁_integral`

English:
lemma circleAverage_log_norm_sub_const₁_integral
  proof: by
  calc ∫ x in 0..(2 * π), log (4 * sin (x / 2) ^ 2) / 2
  _ = ∫ (x : Real) in 0..π, log (4 * sin x ^ 2) := by
    have {x : Real} : x / 2 = 2⁻¹ * x := by ring
    rw [intervalIntegral.integral_div]; rw [this]; rw [inv_mul_integral_comp_div
      (f := fun x => log (4 * sin x ^ 2))]
    simp
  _ =

中文:
引理 circleAverage_log_norm_sub_const₁_integral
  证明: by
  calc ∫ x in 0..(2 * π), log (4 * sin (x / 2) ^ 2) / 2
  _ = ∫ (x : Real) in 0..π, log (4 * sin x ^ 2) := by
    have {x : Real} : x / 2 = 2⁻¹ * x := by ring
    rw [intervalIntegral.integral_div]; rw [this]; rw [inv_mul_integral_comp_div
      (f := fun x => log (4 * sin x ^ 2))]
    simp
  _ =
-/
private lemma circleAverage_log_norm_sub_const₁_integral :
    ∫ x in 0..(2 * π), log (4 * sin (x / 2) ^ 2) / 2 = 0 := by
  calc ∫ x in 0..(2 * π), log (4 * sin (x / 2) ^ 2) / 2
  _ = ∫ (x : Real) in 0..π, log (4 * sin x ^ 2) := by
    have {x : Real} : x / 2 = 2⁻¹ * x := by ring
    rw [intervalIntegral.integral_div]; rw [this]; rw [inv_mul_integral_comp_div
      (f := fun x => log (4 * sin x ^ 2))]
    simp
  _ = ∫ (x : Real) in 0..π, log 4 + 2 * log (sin x) := by
    apply integral_congr_codiscreteWithin
    apply codiscreteWithin_mono (by tauto : Ι 0 π subseteq Set.univ)
    have : AnalyticOnNhd Real (4 * sin · ^ 2) Set.univ := fun _ _ => by fun_prop
    have := this.preimage_zero_mem_codiscrete (x := π / 2)
    simp only [sin_pi_div_two, one_pow, mul_one, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      Set.preimage_compl, forall_const] at this
    filter_upwards [this] with a ha
    simp only [Set.mem_compl_iff, Set.mem_preimage, Set.mem_singleton_iff, mul_eq_zero,
      OfNat.ofNat_ne_zero, ne_eq, not_false_eq_true, pow_eq_zero_iff, false_or] at ha
    rw [log_mul (by simp) (by simp_all)]; rw [log_pow]; rw [Nat.cast_ofNat]
  _ = (∫ (x : Real) in 0..π, log 4) + 2 * ∫ (x : Real) in 0..π, log (sin x) := by
    rw [integral_add _root_.intervalIntegrable_const
      (by apply intervalIntegrable_log_sin.const_mul 2)]; rw [intervalIntegral.integral_const_mul]
  _ = 0 := by
    simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, integral_log_sin_zero_pi,
      (by norm_num : (4 : Real) = 2 * 2), log_mul two_ne_zero two_ne_zero]
    ring

/--
theorem `circleAverage_log_norm_sub_const₁` / 定理 `circleAverage_log_norm_sub_const₁`

English:
theorem circleAverage_log_norm_sub_const₁
  given: (h : ‖a‖ = 1)
  proof: by
  -- Observing that the problem is rotation invariant, we rotate by an angle of `ζ = - arg a` and
  -- reduce the problem to the case where `a = 1`. The integral can then be evaluated by a direct
  -- computation.
  simp only [circleAverage, mul_inv_rev, smul_eq_mul, mul_eq_zero, inv_eq_zero, OfN

中文:
定理 circleAverage_log_norm_sub_const₁
  条件: (h : ‖a‖ = 1)
  证明: by
  -- Observing that the problem is rotation invariant, we rotate by an angle of `ζ = - arg a` and
  -- reduce the problem to the case where `a = 1`. The integral can then be evaluated by a direct
  -- computation.
  simp only [circleAverage, mul_inv_rev, smul_eq_mul, mul_eq_zero, inv_eq_zero, OfN
-/
theorem circleAverage_log_norm_sub_const₁ (h : ‖a‖ = 1) :
    circleAverage (log ‖· - a‖) 0 1 = 0 := by
  -- Observing that the problem is rotation invariant, we rotate by an angle of `ζ = - arg a` and
  -- reduce the problem to the case where `a = 1`. The integral can then be evaluated by a direct
  -- computation.
  simp only [circleAverage, mul_inv_rev, smul_eq_mul, mul_eq_zero, inv_eq_zero, OfNat.ofNat_ne_zero,
    or_false]
  right
  obtain ⟨ζ, hζ⟩ : exists ζ, a⁻¹ = circleMap 0 1 ζ := by simp [Set.exists_range_iff.1, h]
  calc ∫ x in 0..(2 * π), log ‖circleMap 0 1 x - a‖
  _ = ∫ x in 0..(2 * π), log ‖(circleMap 0 1 ζ) * (circleMap 0 1 x - a)‖ := by
    simp
  _ = ∫ x in 0..(2 * π), log ‖circleMap 0 1 (ζ + x) - (circleMap 0 1 ζ) * a‖ := by
    simp [mul_sub, circleMap, add_mul, Complex.exp_add]
  _ = ∫ x in 0..(2 * π), log ‖circleMap 0 1 (ζ + x) - 1‖ := by
    simp [← hζ, inv_mul_cancel₀ (by aesop : a != 0)]
  _ = ∫ x in 0..(2 * π), log ‖circleMap 0 1 x - 1‖ := by
    have : Function.Periodic (log ‖circleMap 0 1 · - 1‖) (2 * π) :=
      fun x => by simp [periodic_circleMap 0 1 x]
    have := this.intervalIntegral_add_eq (t := 0) (s := ζ)
    simp_all [integral_comp_add_left (log ‖circleMap 0 1 · - 1‖)]
  _ = ∫ x in 0..(2 * π), log (4 * sin (x / 2) ^ 2) / 2 := by
    apply integral_congr
    intro x hx
    simp only
    rw [Complex.norm_def]; rw [log_sqrt (circleMap 0 1 x - 1).normSq_nonneg]
    congr
    calc Complex.normSq (circleMap 0 1 x - 1)
    _ = (cos x - 1) * (cos x - 1) + sin x * sin x := by
      simp [circleMap, Complex.normSq_apply]
    _ = sin x ^ 2 + cos x ^ 2 + 1 - 2 * cos x := by
      ring
    _ = 2 - 2 * cos x := by
      rw [sin_sq_add_cos_sq]
      norm_num
    _ = 2 - 2 * cos (2 * (x / 2)) := by
      rw [← mul_div_assoc]
      simp
    _ = 4 - 4 * cos (x / 2) ^ 2 := by
      rw [cos_two_mul]
      ring
    _ = 4 * sin (x / 2) ^ 2 := by
      nth_rw 1 [← mul_one 4, ← sin_sq_add_cos_sq (x / 2)]
      ring
  _ = 0 := circleAverage_log_norm_sub_const₁_integral

/-!
## Computing `circleAverage (log ‖· - a‖) 0 1` in case where `1 < ‖a‖`.
-/

/--
If `a : ℂ` has norm greater than one, then `circleAverage (log ‖· - a‖) 0 1` equals `log ‖a‖`.
-/
@[simp]
/--
theorem `circleAverage_log_norm_sub_const₂` / 定理 `circleAverage_log_norm_sub_const₂`

English:
theorem circleAverage_log_norm_sub_const₂
  given: (h : 1 < ‖a‖)
  proof: by
  rw [InnerProductSpace.HarmonicOnNhd.circleAverage_eq]; rw [zero_sub]; rw [norm_neg]
  intro x hx
  apply AnalyticAt.harmonicAt_log_norm (by fun_prop)
  rw [sub_ne_zero]
  by_contra!
  simp_all only [abs_one, Metric.mem_closedBall, dist_zero_right]
  linarith

中文:
定理 circleAverage_log_norm_sub_const₂
  条件: (h : 1 < ‖a‖)
  证明: by
  rw [InnerProductSpace.HarmonicOnNhd.circleAverage_eq]; rw [zero_sub]; rw [norm_neg]
  intro x hx
  apply AnalyticAt.harmonicAt_log_norm (by fun_prop)
  rw [sub_ne_zero]
  by_contra!
  simp_all only [abs_one, Metric.mem_closedBall, dist_zero_right]
  linarith

Depends on / 依赖: AnalyticAt, AnalyticAt.harmonicAt_log_norm, HarmonicOnNhd, InnerProductSpace, InnerProductSpace.HarmonicOnNhd.circleAverage_eq, Metric, Metric.mem_closedBall, abs_one, circleAverage_eq, dist_zero_right, fun_prop, harmonicAt_log_norm, mem_closedBall, norm_neg, sub_ne_zero, zero_sub
-/
theorem circleAverage_log_norm_sub_const₂ (h : 1 < ‖a‖) :
    circleAverage (log ‖· - a‖) 0 1 = log ‖a‖ := by
  rw [InnerProductSpace.HarmonicOnNhd.circleAverage_eq]; rw [zero_sub]; rw [norm_neg]
  intro x hx
  apply AnalyticAt.harmonicAt_log_norm (by fun_prop)
  rw [sub_ne_zero]
  by_contra!
  simp_all only [abs_one, Metric.mem_closedBall, dist_zero_right]
  linarith

/-!
## Presentation of `log⁺` in Terms of Circle Averages
-/

/--
The `circleAverage (log ‖· - a‖) 0 1` equals `log⁺ ‖a‖`.
-/
@[simp]
/--
theorem `circleAverage_log_norm_sub_const_eq_posLog` / 定理 `circleAverage_log_norm_sub_const_eq_posLog`

English:
theorem circleAverage_log_norm_sub_const_eq_posLog
  proof: by
  rcases lt_trichotomy 1 ‖a‖ with h | h | h
  · rw [circleAverage_log_norm_sub_const₂ h]
    apply (posLog_eq_log _).symm
    simp_all [le_of_lt h]
  · rw [eq_comm, circleAverage_log_norm_sub_const₁ h.symm, posLog_eq_zero_iff]
    simp_all
  · rw [eq_comm, circleAverage_log_norm_sub_const₀ h, pos

中文:
定理 circleAverage_log_norm_sub_const_eq_posLog
  证明: by
  rcases lt_trichotomy 1 ‖a‖ with h | h | h
  · rw [circleAverage_log_norm_sub_const₂ h]
    apply (posLog_eq_log _).symm
    simp_all [le_of_lt h]
  · rw [eq_comm, circleAverage_log_norm_sub_const₁ h.symm, posLog_eq_zero_iff]
    simp_all
  · rw [eq_comm, circleAverage_log_norm_sub_const₀ h, pos

Depends on / 依赖: eq_comm, h.symm, le_of_lt, lt_trichotomy, posLog_eq_log, posLog_eq_zero_iff
-/
theorem circleAverage_log_norm_sub_const_eq_posLog :
    circleAverage (log ‖· - a‖) 0 1 = log⁺ ‖a‖ := by
  rcases lt_trichotomy 1 ‖a‖ with h | h | h
  · rw [circleAverage_log_norm_sub_const₂ h]
    apply (posLog_eq_log _).symm
    simp_all [le_of_lt h]
  · rw [eq_comm, circleAverage_log_norm_sub_const₁ h.symm, posLog_eq_zero_iff]
    simp_all
  · rw [eq_comm, circleAverage_log_norm_sub_const₀ h, posLog_eq_zero_iff]
    simp_all [le_of_lt h]

/--
The `circleAverage (log ‖· + a‖) 0 1` equals `log⁺ ‖a‖`.
-/
@[simp]
/--
theorem `circleAverage_log_norm_add_const_eq_posLog` / 定理 `circleAverage_log_norm_add_const_eq_posLog`

English:
theorem circleAverage_log_norm_add_const_eq_posLog
  proof: by
  have : (log ‖· + a‖) = (log ‖· - -a‖) := by simp
  simp [this]

中文:
定理 circleAverage_log_norm_add_const_eq_posLog
  证明: by
  have : (log ‖· + a‖) = (log ‖· - -a‖) := by simp
  simp [this]
-/
theorem circleAverage_log_norm_add_const_eq_posLog :
    circleAverage (log ‖· + a‖) 0 1 = log⁺ ‖a‖ := by
  have : (log ‖· + a‖) = (log ‖· - -a‖) := by simp
  simp [this]

/--
theorem `circleAverage_log_norm_sub_const_eq_log_radius_add_posLog` / 定理 `circleAverage_log_norm_sub_const_eq_log_radius_add_posLog`

English:
theorem circleAverage_log_norm_sub_const_eq_log_radius_add_posLog
  given: (hR : R != 0)
  proof: by
  calc circleAverage (log ‖· - a‖) c R
  _ = circleAverage (fun z => log ‖R * (z + R⁻¹ * (c - a))‖) 0 1 := by
    rw [circleAverage_eq_circleAverage_zero_one]
    congr
    ext z
    congr
    rw [Complex.ofReal_inv R]
    field [Complex.ofReal_ne_zero.mpr hR]
  _ = circleAverage (fun z => log ‖R

中文:
定理 circleAverage_log_norm_sub_const_eq_log_radius_add_posLog
  条件: (hR : R != 0)
  证明: by
  calc circleAverage (log ‖· - a‖) c R
  _ = circleAverage (fun z => log ‖R * (z + R⁻¹ * (c - a))‖) 0 1 := by
    rw [circleAverage_eq_circleAverage_zero_one]
    congr
    ext z
    congr
    rw [Complex.ofReal_inv R]
    field [Complex.ofReal_ne_zero.mpr hR]
  _ = circleAverage (fun z => log ‖R

Depends on / 依赖: Complex.ofReal_inv, Complex.ofReal_ne_zero.mpr, Metric, Metric.sphere, circleAverage, circleAverage_congr_codiscreteWithin, circleAverage_eq_circleAverage_zero_one, codiscreteWithin, ofReal_inv, ofReal_ne_zero, sphere, zero_ne_one
-/
theorem circleAverage_log_norm_sub_const_eq_log_radius_add_posLog (hR : R != 0) :
    circleAverage (log ‖· - a‖) c R = log R + log⁺ (R⁻¹ * ‖c - a‖) := by
  calc circleAverage (log ‖· - a‖) c R
  _ = circleAverage (fun z => log ‖R * (z + R⁻¹ * (c - a))‖) 0 1 := by
    rw [circleAverage_eq_circleAverage_zero_one]
    congr
    ext z
    congr
    rw [Complex.ofReal_inv R]
    field [Complex.ofReal_ne_zero.mpr hR]
  _ = circleAverage (fun z => log ‖R‖ + log ‖z + R⁻¹ * (c - a)‖) 0 1 := by
    apply circleAverage_congr_codiscreteWithin _ (zero_ne_one' Real).symm
    have : {z | ‖z + ↑R⁻¹ * (c - a)‖ != 0} in codiscreteWithin (Metric.sphere (0 : Complex) |1|) := by
      apply codiscreteWithin_iff_locallyFiniteComplementWithin.2
      intro z hz
      use Set.univ
      simp only [univ_mem, abs_one, Complex.ofReal_inv, ne_eq, norm_eq_zero, Set.univ_inter,
        true_and]
      apply Set.Subsingleton.finite
      intro z₁ hz₁ z₂ hz₂
      simp_all only [ne_eq, abs_one, mem_sphere_iff_norm, sub_zero, Set.mem_sdiff,
        Set.mem_ofPred_eq, Decidable.not_not]
      rw [add_eq_zero_iff_eq_neg.1 hz₁.2]; rw [add_eq_zero_iff_eq_neg.1 hz₂.2]
    filter_upwards [this] with z hz
    rw [norm_mul]; rw [log_mul (norm_ne_zero_iff.2 (Complex.ofReal_ne_zero.mpr hR)) hz]
    simp
  _ = log R + log⁺ (|R|⁻¹ * ‖c - a‖) := by
    rw [← Pi.add_def]; rw [circleAverage_add (circleIntegrable_const (log ‖R‖) 0 1)
      (MeromorphicOn.circleIntegrable_log_norm (fun _ _ => by fun_prop))]; rw [circleAverage_const]
    simp
  _ = log R + log⁺ (R⁻¹ * ‖c - a‖) := by
    congr 1
    rcases hR.lt_or_gt with h | h
    · simp [abs_of_neg h]
    · rw [abs_of_pos h]

/--
lemma `circleAverage_log_norm_sub_const_of_mem_closedBall` / 引理 `circleAverage_log_norm_sub_const_of_mem_closedBall`

English:
lemma circleAverage_log_norm_sub_const_of_mem_closedBall
  given: (hu : a in closedBall c |R|)
  proof: by
  by_cases hR : R = 0
  · simp_all
  rw [circleAverage_log_norm_sub_const_eq_log_radius_add_posLog hR]; rw [add_eq_left]; rw [posLog_eq_zero_iff]; rw [abs_mul]; rw [abs_inv]; rw [abs_of_nonneg (norm_nonneg (c - a))]
  rw [mem_closedBall]; rw [dist_eq_norm'] at hu
  apply inv_mul_le_one_of_le₀ hu 

中文:
引理 circleAverage_log_norm_sub_const_of_mem_closedBall
  条件: (hu : a in closedBall c |R|)
  证明: by
  by_cases hR : R = 0
  · simp_all
  rw [circleAverage_log_norm_sub_const_eq_log_radius_add_posLog hR]; rw [add_eq_left]; rw [posLog_eq_zero_iff]; rw [abs_mul]; rw [abs_inv]; rw [abs_of_nonneg (norm_nonneg (c - a))]
  rw [mem_closedBall]; rw [dist_eq_norm'] at hu
  apply inv_mul_le_one_of_le₀ hu 

Depends on / 依赖: abs_inv, abs_mul, abs_nonneg, abs_of_nonneg, add_eq_left, circleAverage_log_norm_sub_const_eq_log_radius_add_posLog, dist_eq_norm, mem_closedBall, norm_nonneg, posLog_eq_zero_iff
-/
lemma circleAverage_log_norm_sub_const_of_mem_closedBall (hu : a in closedBall c |R|) :
    circleAverage (log ‖· - a‖) c R = log R := by
  by_cases hR : R = 0
  · simp_all
  rw [circleAverage_log_norm_sub_const_eq_log_radius_add_posLog hR]; rw [add_eq_left]; rw [posLog_eq_zero_iff]; rw [abs_mul]; rw [abs_inv]; rw [abs_of_nonneg (norm_nonneg (c - a))]
  rw [mem_closedBall]; rw [dist_eq_norm'] at hu
  apply inv_mul_le_one_of_le₀ hu (abs_nonneg R)
