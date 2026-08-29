/-
Copyright (c) 2026 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mihai Iancu, Stefan Kebekus, Sebastian Schleissinger, Aristotle AI
-/
module

public import Mathlib.Analysis.Complex.Harmonic.MeanValue
public import Mathlib.Analysis.Complex.Poisson

/-!
# Poisson Integral Formula

This file establishes several versions of the **Poisson Integral Formula** for harmonic functions on
arbitrary disks in the complex plane, formulated with the real part of the Herglotz–Riesz kernel of
integration and with the Poisson kernel, respectively.

TODO: Extend this formula to vector-valued harmonic functions
-/

public section

open Complex InnerProductSpace Metric Real Topology

variable
  {f : Complex -> Real} {c w : Complex} {R : Real}

namespace InnerProductSpace

/--
lemma `continuousOn_herglotz_riesz` / 引理 `continuousOn_herglotz_riesz`

English:
lemma continuousOn_herglotz_riesz
  given: (_ : w in ball c R)
  proof: by
  have : forall x in {z | ‖z - c‖ in Set.Ioc ‖w - c‖ R}, x - c - (w - c) != 0 := by
    grind [mem_ball, mem_sphere]
  fun_prop

中文:
引理 continuousOn_herglotz_riesz
  条件: (_ : w in ball c R)
  证明: by
  have : forall x in {z | ‖z - c‖ in Set.Ioc ‖w - c‖ R}, x - c - (w - c) != 0 := by
    grind [mem_ball, mem_sphere]
  fun_prop
-/
private lemma continuousOn_herglotz_riesz (_ : w in ball c R) :
    ContinuousOn (fun x => ((x - c + (w - c)) / (x - c - (w - c))).re)
      {z | ‖z - c‖ in Set.Ioc ‖w - c‖ R} := by
  have : forall x in {z | ‖z - c‖ in Set.Ioc ‖w - c‖ R}, x - c - (w - c) != 0 := by
    grind [mem_ball, mem_sphere]
  fun_prop

/--
theorem `HarmonicOnNhd.circleAverage_re_herglotzRieszKernel_smul` / 定理 `HarmonicOnNhd.circleAverage_re_herglotzRieszKernel_smul`

English:
theorem HarmonicOnNhd.circleAverage_re_herglotzRieszKernel_smul
  proof: by
  obtain ⟨e, h₁e, h₂e⟩ := (isCompact_closedBall c R).exists_thickening_subset_open
    (isOpen_setOfPred_harmonicAt f) (by aesop)
  rw [thickening_closedBall h₁e (pos_of_mem_ball hw).le] at h₂e
  obtain ⟨F, h₁F, h₂F⟩ := HarmonicOnNhd.exists_analyticOnNhd_ball_re_eq h₂e
  have h₃F : Differentiable

中文:
定理 HarmonicOnNhd.circleAverage_re_herglotzRieszKernel_smul
  证明: by
  obtain ⟨e, h₁e, h₂e⟩ := (isCompact_closedBall c R).exists_thickening_subset_open
    (isOpen_setOfPred_harmonicAt f) (by aesop)
  rw [thickening_closedBall h₁e (pos_of_mem_ball hw).le] at h₂e
  obtain ⟨F, h₁F, h₂F⟩ := HarmonicOnNhd.exists_analyticOnNhd_ball_re_eq h₂e
  have h₃F : Differentiable

Depends on / 依赖: DifferentiableOn, HarmonicOnNhd, HarmonicOnNhd.exists_analyticOnNhd_ball_re_eq, Set.EqOn, closure, closure_ball_subset_closedBall, differentiableWithinAt, exists_analyticOnNhd_ball_re_eq, exists_thickening_subset_open, herglotzRieszKernel, isCompact_closedBall, isOpen_setOfPred_harmonicAt, mem_ball, mem_closedBall, pos_of_mem_ball, thickening_closedBall
-/
theorem HarmonicOnNhd.circleAverage_re_herglotzRieszKernel_smul
    (hf : HarmonicOnNhd f (closedBall c R)) (hw : w in ball c R) :
    Real.circleAverage ((re ∘ herglotzRieszKernel c w) • f) c R = f w := by
  obtain ⟨e, h₁e, h₂e⟩ := (isCompact_closedBall c R).exists_thickening_subset_open
    (isOpen_setOfPred_harmonicAt f) (by aesop)
  rw [thickening_closedBall h₁e (pos_of_mem_ball hw).le] at h₂e
  obtain ⟨F, h₁F, h₂F⟩ := HarmonicOnNhd.exists_analyticOnNhd_ball_re_eq h₂e
  have h₃F : DifferentiableOn Complex F (closure (ball c R)) := by
    intro x hx
    apply (h₁F x _).differentiableWithinAt
    grind [mem_ball, mem_closedBall.1 (closure_ball_subset_closedBall hx)]
  have h₄F : Set.EqOn (re ∘ herglotzRieszKernel c w • f)
      (reCLM ∘ (fun z => ((z - c + (w - c)) / (z - c - (w - c))).re • F z))
      (sphere c R) := by
    intro x hx
    simp [h₂F (sphere_subset_ball (lt_add_of_pos_left R h₁e) hx), herglotzRieszKernel_def]
  rw [← abs_of_pos (pos_of_mem_ball hw)] at h₄F
  rw [circleAverage_congr_sphere h₄F]; rw [reCLM.circleAverage_comp_comm]; rw [h₃F.diffContOnCl.circleAverage_re_herglotzRieszKernel_smul' hw]
  · apply h₂F
    grind [mem_ball]
  -- CircleIntegrable (fun z ↦ ((z - c + (w - c)) / (z - c - (w - c))).re • F z) c R
  apply (ContinuousOn.fun_smul _ _).circleIntegrable'
  · apply (continuousOn_herglotz_riesz hw).mono
    grind [mem_ball, dist_eq_norm, mem_sphere_iff_norm, (pos_of_mem_ball hw)]
  · apply (h₁F.mono _).continuousOn (𝕜 := Complex)
    grind [mem_sphere, mem_ball, (pos_of_mem_ball hw)]

/--
theorem `HarmonicContOnCl.circleAverage_re_herglotzRieszKernel_smul` / 定理 `HarmonicContOnCl.circleAverage_re_herglotzRieszKernel_smul`

English:
theorem HarmonicContOnCl.circleAverage_re_herglotzRieszKernel_smul
  proof: by
  apply ContinuousOn.eq_of_eqOn_Ioo (r := ‖w - c‖)
  · apply ContinuousOn.circleAverage
    · rw [herglotzRieszKernel_fun_def]
      apply (continuousOn_herglotz_riesz hw).smul (hf.2.mono _)
      grind [closure_ball c (pos_of_mem_ball hw).ne', mem_closedBall_iff_norm]
    · grind [norm_nonneg (w

中文:
定理 HarmonicContOnCl.circleAverage_re_herglotzRieszKernel_smul
  证明: by
  apply ContinuousOn.eq_of_eqOn_Ioo (r := ‖w - c‖)
  · apply ContinuousOn.circleAverage
    · rw [herglotzRieszKernel_fun_def]
      apply (continuousOn_herglotz_riesz hw).smul (hf.2.mono _)
      grind [closure_ball c (pos_of_mem_ball hw).ne', mem_closedBall_iff_norm]
    · grind [norm_nonneg (w

Depends on / 依赖: ContinuousOn, ContinuousOn.circleAverage, ContinuousOn.eq_of_eqOn_Ioo, HarmonicOnNhd, HarmonicOnNhd.circleAverage_re_herglotzRieszKernel_smul, circleAverage, circleAverage_re_herglotzRieszKernel_smul, closedBall_subset_ball, closure_ball, continuousOn_herglotz_riesz, eq_of_eqOn_Ioo, herglotzRieszKernel_fun_def, mem_ball_iff_norm, mem_closedBall_iff_norm, norm_nonneg, pos_of_mem_ball
-/
theorem HarmonicContOnCl.circleAverage_re_herglotzRieszKernel_smul
    (hf : HarmonicContOnCl f (ball c R)) (hw : w in ball c R) :
    Real.circleAverage ((re ∘ herglotzRieszKernel c w) • f) c R = f w := by
  apply ContinuousOn.eq_of_eqOn_Ioo (r := ‖w - c‖)
  · apply ContinuousOn.circleAverage
    · rw [herglotzRieszKernel_fun_def]
      apply (continuousOn_herglotz_riesz hw).smul (hf.2.mono _)
      grind [closure_ball c (pos_of_mem_ball hw).ne', mem_closedBall_iff_norm]
    · grind [norm_nonneg (w - c)]
  · grind [mem_ball_iff_norm]
  · intro r hr
    rw [HarmonicOnNhd.circleAverage_re_herglotzRieszKernel_smul
      (hf.1.mono (closedBall_subset_ball hr.2)) (by grind [mem_ball_iff_norm])]

/--
theorem `HarmonicOnNhd.circleAverage_poissonKernel_smul` / 定理 `HarmonicOnNhd.circleAverage_poissonKernel_smul`

English:
theorem HarmonicOnNhd.circleAverage_poissonKernel_smul
  proof: by
  rw [← hf.circleAverage_re_herglotzRieszKernel_smul hw]
  apply circleAverage_congr_sphere
    (fun _ _ => by simp_rw [← poissonKernel_eq_re_herglotzRieszKernel])

中文:
定理 HarmonicOnNhd.circleAverage_poissonKernel_smul
  证明: by
  rw [← hf.circleAverage_re_herglotzRieszKernel_smul hw]
  apply circleAverage_congr_sphere
    (fun _ _ => by simp_rw [← poissonKernel_eq_re_herglotzRieszKernel])

Depends on / 依赖: circleAverage_congr_sphere, circleAverage_re_herglotzRieszKernel_smul, hf.circleAverage_re_herglotzRieszKernel_smul, poissonKernel_eq_re_herglotzRieszKernel, simp_rw
-/
theorem HarmonicOnNhd.circleAverage_poissonKernel_smul
    (hf : HarmonicOnNhd f (closedBall c R)) (hw : w in ball c R) :
    Real.circleAverage (poissonKernel c w • f) c R = f w := by
  rw [← hf.circleAverage_re_herglotzRieszKernel_smul hw]
  apply circleAverage_congr_sphere
    (fun _ _ => by simp_rw [← poissonKernel_eq_re_herglotzRieszKernel])

/--
theorem `HarmonicContOnCl.circleAverage_poissonKernel_smul` / 定理 `HarmonicContOnCl.circleAverage_poissonKernel_smul`

English:
theorem HarmonicContOnCl.circleAverage_poissonKernel_smul
  proof: by
  rw [← hf.circleAverage_re_herglotzRieszKernel_smul hw]
  apply circleAverage_congr_sphere
    (fun _ _ => by simp_rw [← poissonKernel_eq_re_herglotzRieszKernel])

中文:
定理 HarmonicContOnCl.circleAverage_poissonKernel_smul
  证明: by
  rw [← hf.circleAverage_re_herglotzRieszKernel_smul hw]
  apply circleAverage_congr_sphere
    (fun _ _ => by simp_rw [← poissonKernel_eq_re_herglotzRieszKernel])

Depends on / 依赖: circleAverage_congr_sphere, circleAverage_re_herglotzRieszKernel_smul, hf.circleAverage_re_herglotzRieszKernel_smul, poissonKernel_eq_re_herglotzRieszKernel, simp_rw
-/
theorem HarmonicContOnCl.circleAverage_poissonKernel_smul
    (hf : HarmonicContOnCl f (ball c R)) (hw : w in ball c R) :
    Real.circleAverage (poissonKernel c w • f) c R = f w := by
  rw [← hf.circleAverage_re_herglotzRieszKernel_smul hw]
  apply circleAverage_congr_sphere
    (fun _ _ => by simp_rw [← poissonKernel_eq_re_herglotzRieszKernel])

end InnerProductSpace
