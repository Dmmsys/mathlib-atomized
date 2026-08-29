/-
Copyright (c) 2025 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
module

public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.MeasureTheory.Integral.CircleAverage

/-!
# The Mean Value Property of Complex Differentiable Functions

This file established the classic mean value properties of complex differentiable functions,
computing the value of a function at the center of a circle as a circle average. It also provides
generalized versions that computing the value of a function at arbitrary points of a disk as circle
averages over suitable weighted functions.
-/

public section

open Complex Filter Function Metric Real Set Topology

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace Complex E] [CompleteSpace E]
  {f : Complex -> E} {R : Real} {c w : Complex} {s : Set Complex}

/-!
## Generalized Mean Value Properties

For a complex differentiable function `f`, the theorems in this section compute values of `f` in the
interior of a disk as circle averages of a weighted function.
-/

/--
theorem `circleAverage_sub_sub_inv_smul_of_differentiable_on_off_countable` / 定理 `circleAverage_sub_sub_inv_smul_of_differentiable_on_off_countable`

English:
theorem circleAverage_sub_sub_inv_smul_of_differentiable_on_off_countable
  statement: (hs : s.Countable)
  proof: by
  rw [← circleAverage_abs_radius]
  rcases le_or_gt |R| 0 with hR | hR
  · simp_all [ball_eq_empty.2 hR]
  calc circleAverage (fun z => ((z - c) * (z - w)⁻¹) • f z) c |R|
  _ = (2 * π * I)⁻¹ • (∮ z in C(c, |R|), (z - w)⁻¹ • f z) := by
    simp only [circleAverage_eq_circleIntegral hR.ne', mul_inv

中文:
定理 circleAverage_sub_sub_inv_smul_of_differentiable_on_off_countable
  结论: (hs : s.可数)
  证明: by
  rw [← circleAverage_abs_radius]
  rcases le_or_gt |R| 0 with hR | hR
  · simp_all [ball_eq_empty.2 hR]
  calc circleAverage (fun z => ((z - c) * (z - w)⁻¹) • f z) c |R|
  _ = (2 * π * I)⁻¹ • (∮ z in C(c, |R|), (z - w)⁻¹ • f z) := by
    simp only [circleAverage_eq_circleIntegral hR.ne', mul_inv

Depends on / 依赖: I_ne_zero, OfNat.ofNat_ne_zero, ball_eq_empty, circleAverage, circleAverage_abs_radius, circleAverage_eq_circleIntegral, circleIntegral, circleIntegral.integral_congr, hR.ne, integral_congr, inv_I, inv_eq_zero, le_or_gt, mul_eq_zero, mul_inv_rev, ne_eq, neg_inj, neg_mul, neg_smul, not_false_eq_true
-/
theorem circleAverage_sub_sub_inv_smul_of_differentiable_on_off_countable (hs : s.Countable)
    (h₁f : ContinuousOn f (closedBall c |R|)) (h₂f : forall z in ball c |R| \ s, DifferentiableAt Complex f z)
    (hw : w in ball c |R|) :
    circleAverage (fun z => ((z - c) / (z - w)) • f z) c R = f w := by
  rw [← circleAverage_abs_radius]
  rcases le_or_gt |R| 0 with hR | hR
  · simp_all [ball_eq_empty.2 hR]
  calc circleAverage (fun z => ((z - c) * (z - w)⁻¹) • f z) c |R|
  _ = (2 * π * I)⁻¹ • (∮ z in C(c, |R|), (z - w)⁻¹ • f z) := by
    simp only [circleAverage_eq_circleIntegral hR.ne', mul_inv_rev, inv_I, neg_mul, neg_smul,
      neg_inj, ne_eq, mul_eq_zero, I_ne_zero, inv_eq_zero, ofReal_eq_zero, pi_ne_zero,
      OfNat.ofNat_ne_zero, or_self, not_false_eq_true, smul_right_inj]
    apply circleIntegral.integral_congr hR.le
    intro z hz
    match_scalars
    have : z - c != 0 := by grind [ne_of_mem_sphere]
    grind
  _ = f w := by
    rw [circleIntegral_sub_inv_smul_of_differentiable_on_off_countable hs hw h₁f h₂f]
    match_scalars
    simp [field]

/--
theorem `DiffContOnCl.circleAverage_smul_div` / 定理 `DiffContOnCl.circleAverage_smul_div`

English:
theorem DiffContOnCl.circleAverage_smul_div
  statement: (hf : DiffContOnCl Complex f (ball c |R|))
  proof: by
  by_cases hR : |R| <= 0
  · simp_all [ball_eq_empty.2 hR]
  apply circleAverage_sub_sub_inv_smul_of_differentiable_on_off_countable countable_empty _ _ hw
  · simpa [← closure_ball _ (ne_of_not_ge hR).symm] using hf.2
  · intro z hz
    rw [sdiff_empty] at hz
    apply (hf.1 z hz).differentiable

中文:
定理 DiffContOnCl.circleAverage_smul_div
  结论: (hf : DiffContOnCl 复形 f (ball c |R|))
  证明: by
  by_cases hR : |R| <= 0
  · simp_all [ball_eq_empty.2 hR]
  apply circleAverage_sub_sub_inv_smul_of_differentiable_on_off_countable countable_empty _ _ hw
  · simpa [← closure_ball _ (ne_of_not_ge hR).symm] using hf.2
  · intro z hz
    rw [sdiff_empty] at hz
    apply (hf.1 z hz).differentiable

Depends on / 依赖: ball_eq_empty, circleAverage_sub_sub_inv_smul_of_differentiable_on_off_countable, closure_ball, countable_empty, differentiableAt, isOpen_ball, isOpen_ball.mem_nhds, mem_nhds, ne_of_not_ge, sdiff_empty
-/
theorem DiffContOnCl.circleAverage_smul_div (hf : DiffContOnCl Complex f (ball c |R|))
    (hw : w in ball c |R|) :
    circleAverage (fun z => ((z - c) / (z - w)) • f z) c R = f w := by
  by_cases hR : |R| <= 0
  · simp_all [ball_eq_empty.2 hR]
  apply circleAverage_sub_sub_inv_smul_of_differentiable_on_off_countable countable_empty _ _ hw
  · simpa [← closure_ball _ (ne_of_not_ge hR).symm] using hf.2
  · intro z hz
    rw [sdiff_empty] at hz
    apply (hf.1 z hz).differentiableAt (isOpen_ball.mem_nhds hz)

@[deprecated (since := "2026-02-11")]
alias circleAverage_sub_sub_inv_smul_of_differentiable_on := DiffContOnCl.circleAverage_smul_div

/-!
## Classic Mean Value Properties

For a complex differentiable function `f`, the theorems in this section compute value of `f` at the
center of a circle as a circle average of the function. This specializes the generalized mean value
properties discussed in the previous section.
-/

/--
theorem `circleAverage_of_differentiable_on_off_countable` / 定理 `circleAverage_of_differentiable_on_off_countable`

English:
theorem circleAverage_of_differentiable_on_off_countable
  statement: (hs : s.Countable)
  proof: by
  by_cases hR : R = 0
  · simp [hR]
  · rw [← circleAverage_sub_sub_inv_smul_of_differentiable_on_off_countable hs h₁f h₂f (by aesop)]
    apply circleAverage_congr_sphere fun z hz => ?_
    have : z - c != 0 := by grind [ne_of_mem_sphere]
    simp_all

中文:
定理 circleAverage_of_differentiable_on_off_countable
  结论: (hs : s.可数)
  证明: by
  by_cases hR : R = 0
  · simp [hR]
  · rw [← circleAverage_sub_sub_inv_smul_of_differentiable_on_off_countable hs h₁f h₂f (by aesop)]
    apply circleAverage_congr_sphere fun z hz => ?_
    have : z - c != 0 := by grind [ne_of_mem_sphere]
    simp_all

Depends on / 依赖: circleAverage_congr_sphere, circleAverage_sub_sub_inv_smul_of_differentiable_on_off_countable, ne_of_mem_sphere
-/
theorem circleAverage_of_differentiable_on_off_countable (hs : s.Countable)
    (h₁f : ContinuousOn f (closedBall c |R|)) (h₂f : forall z in ball c |R| \ s, DifferentiableAt Complex f z) :
    circleAverage f c R = f c := by
  by_cases hR : R = 0
  · simp [hR]
  · rw [← circleAverage_sub_sub_inv_smul_of_differentiable_on_off_countable hs h₁f h₂f (by aesop)]
    apply circleAverage_congr_sphere fun z hz => ?_
    have : z - c != 0 := by grind [ne_of_mem_sphere]
    simp_all

/--
theorem `DiffContOnCl.circleAverage` / 定理 `DiffContOnCl.circleAverage`

English:
theorem DiffContOnCl.circleAverage
  given: (hf : DiffContOnCl Complex f (ball c |R|))
  proof: by
  by_cases hR : R = 0
  · simp [hR]
  · rw [← circleAverage_smul_div hf (by aesop)]
    apply circleAverage_congr_sphere fun z hz => ?_
    have : z - c != 0 := by grind [ne_of_mem_sphere]
    simp_all

@[deprecated (since := "2026-02-11")]
alias circleAverage_of_differentiable_on := DiffContOnCl

中文:
定理 DiffContOnCl.circleAverage
  条件: (hf : DiffContOnCl 复形 f (ball c |R|))
  证明: by
  by_cases hR : R = 0
  · simp [hR]
  · rw [← circleAverage_smul_div hf (by aesop)]
    apply circleAverage_congr_sphere fun z hz => ?_
    have : z - c != 0 := by grind [ne_of_mem_sphere]
    simp_all

@[deprecated (since := "2026-02-11")]
alias circleAverage_of_differentiable_on := DiffContOnCl

Depends on / 依赖: circleAverage_congr_sphere, circleAverage_smul_div, ne_of_mem_sphere
-/
theorem DiffContOnCl.circleAverage (hf : DiffContOnCl Complex f (ball c |R|)) :
    circleAverage f c R = f c := by
  by_cases hR : R = 0
  · simp [hR]
  · rw [← circleAverage_smul_div hf (by aesop)]
    apply circleAverage_congr_sphere fun z hz => ?_
    have : z - c != 0 := by grind [ne_of_mem_sphere]
    simp_all

@[deprecated (since := "2026-02-11")]
alias circleAverage_of_differentiable_on := DiffContOnCl.circleAverage
