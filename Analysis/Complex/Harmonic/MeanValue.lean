/-
Copyright (c) 2025 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus, Yi Yuan
-/
module

public import Mathlib.Analysis.Complex.Harmonic.Analytic
public import Mathlib.Analysis.Complex.MeanValue
public import Mathlib.Analysis.InnerProductSpace.Harmonic.HarmonicContOnCl

/-!
# The Mean Value Property of Vector-Valued Harmonic Functions

This file establishes the mean value property for harmonic functions `f : ℂ → F`, where `F` is an
arbitrary complete real normed vector space. This generalizes the mean value property for
real-valued harmonic functions.

Completeness of `F` cannot be dropped: `circleAverage` is defined in terms of the Bochner integral,
which is junk (zero) whenever the target space is incomplete.

The proof reduces to the real-valued case. Circle averages commute with continuous linear maps, and
composition with continuous linear maps preserves harmonicity. Thus, `g (circleAverage f c R)`
equals `circleAverage (g ∘ f) c R = g (f c)` for every continuous linear functional `g : F →L[ℝ] ℝ`.
Since continuous linear functionals separate the points of a normed space (Hahn-Banach, in the form
of `SeparatingDual.eq_iff_forall_dual_eq`), this suffices.
-/

public section

open InnerProductSpace Metric Real

namespace InnerProductSpace

/-!
## Compatibility of `HarmonicContOnCl` with Linear Maps
-/

section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E] [FiniteDimensional Real E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace Real F]
variable {G : Type*} [NormedAddCommGroup G] [NormedSpace Real G]

/--
theorem `HarmonicContOnCl.comp_CLM` / 定理 `HarmonicContOnCl.comp_CLM`

English:
theorem HarmonicContOnCl.comp_CLM
  statement: {f : E -> F} {s : Set E} (h : HarmonicContOnCl f s)
  proof: ⟨h.1.comp_CLM l, l.continuous.comp_continuousOn h.2⟩

中文:
定理 HarmonicContOnCl.comp_CLM
  结论: {f : E -> F} {s : 集合 E} (h : HarmonicContOnCl f s)
  证明: ⟨h.1.comp_CLM l, l.continuous.comp_continuousOn h.2⟩

Depends on / 依赖: comp_CLM, comp_continuousOn, continuous, l.continuous.comp_continuousOn
-/
theorem HarmonicContOnCl.comp_CLM {f : E -> F} {s : Set E} (h : HarmonicContOnCl f s)
    (l : F ->L[Real] G) : HarmonicContOnCl (l ∘ f) s :=
  ⟨h.1.comp_CLM l, l.continuous.comp_continuousOn h.2⟩

end

/-!
## The Mean Value Property
-/

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace Real F] [CompleteSpace F]
variable {f : Complex -> F} {c : Complex} {R : Real}

/--
theorem `HarmonicOnNhd.circleAverage_eq` / 定理 `HarmonicOnNhd.circleAverage_eq`

English:
theorem HarmonicOnNhd.circleAverage_eq
  given: (hf : HarmonicOnNhd f (closedBall c |R|))
  proof: by
  have h : CircleIntegrable f c R :=
    (hf.continuousOn.mono sphere_subset_closedBall).circleIntegrable'
  rw [SeparatingDual.eq_iff_forall_dual_eq (R := Real)]
  intro g
  rw [← g.circleAverage_comp_comm h]
  obtain ⟨e, h₁e, h₂e⟩ := (isCompact_closedBall c |R|).exists_thickening_subset_open
  

中文:
定理 HarmonicOnNhd.circleAverage_eq
  条件: (hf : HarmonicOnNhd f (closedBall c |R|))
  证明: by
  have h : CircleIntegrable f c R :=
    (hf.continuousOn.mono sphere_subset_closedBall).circleIntegrable'
  rw [SeparatingDual.eq_iff_forall_dual_eq (R := Real)]
  intro g
  rw [← g.circleAverage_comp_comm h]
  obtain ⟨e, h₁e, h₂e⟩ := (isCompact_closedBall c |R|).exists_thickening_subset_open
  

Depends on / 依赖: CircleIntegrable, Differ, HarmonicOnNhd, InnerProductSpace, InnerProductSpace.HarmonicOnNhd.exists_analyticOnNhd_ball_re_eq, SeparatingDual, SeparatingDual.eq_iff_forall_dual_eq, abs_nonneg, circleAverage_comp_comm, circleIntegrable, comp_CLM, continuousOn, eq_iff_forall_dual_eq, exists_analyticOnNhd_ball_re_eq, exists_thickening_subset_open, g.circleAverage_comp_comm, hf.comp_CLM, hf.continuousOn.mono, isCompact_closedBall, isOpen_setOfPred_harmonicAt
-/
theorem HarmonicOnNhd.circleAverage_eq (hf : HarmonicOnNhd f (closedBall c |R|)) :
    circleAverage f c R = f c := by
  have h : CircleIntegrable f c R :=
    (hf.continuousOn.mono sphere_subset_closedBall).circleIntegrable'
  rw [SeparatingDual.eq_iff_forall_dual_eq (R := Real)]
  intro g
  rw [← g.circleAverage_comp_comm h]
  obtain ⟨e, h₁e, h₂e⟩ := (isCompact_closedBall c |R|).exists_thickening_subset_open
    (isOpen_setOfPred_harmonicAt (g ∘ f)) (hf.comp_CLM g)
  rw [thickening_closedBall h₁e (abs_nonneg R)] at h₂e
  obtain ⟨F, h₁F, h₂F⟩ := InnerProductSpace.HarmonicOnNhd.exists_analyticOnNhd_ball_re_eq h₂e
  have h₃F : DifferentiableOn Complex F (closure (ball c |R|)) := by
    intro x hx
    apply (h₁F x _).differentiableWithinAt
    grind [mem_ball, mem_closedBall.1 (closure_ball_subset_closedBall hx)]
  have h₄F : Set.EqOn (Complex.reCLM ∘ F) (⇑g ∘ f) (sphere c |R|) :=
    fun x hx => h₂F (sphere_subset_ball (lt_add_of_pos_left |R| h₁e) hx)
  rw [← circleAverage_congr_sphere h₄F]; rw [Complex.reCLM.circleAverage_comp_comm]; rw [h₃F.diffContOnCl.circleAverage]
  · apply h₂F
    simp [mem_ball, dist_self, add_pos_of_pos_of_nonneg h₁e (abs_nonneg R)]
  · apply (h₁F.continuousOn.mono (fun _ _ => by simp_all [dist_eq_norm])).circleIntegrable'

/--
theorem `HarmonicContOnCl.circleAverage_eq` / 定理 `HarmonicContOnCl.circleAverage_eq`

English:
theorem HarmonicContOnCl.circleAverage_eq
  given: (hf : HarmonicContOnCl f (ball c |R|))
  proof: by
  have h : CircleIntegrable f c R :=
    (hf.continuousOn_ball.mono sphere_subset_closedBall).circleIntegrable'
  rw [SeparatingDual.eq_iff_forall_dual_eq (R := Real)]
  intro g
  rw [← g.circleAverage_comp_comm h]
  by_cases hR : R = 0
  · simp_all
  have H : ContinuousOn (circleAverage (g ∘ f) 

中文:
定理 HarmonicContOnCl.circleAverage_eq
  条件: (hf : HarmonicContOnCl f (ball c |R|))
  证明: by
  have h : CircleIntegrable f c R :=
    (hf.continuousOn_ball.mono sphere_subset_closedBall).circleIntegrable'
  rw [SeparatingDual.eq_iff_forall_dual_eq (R := Real)]
  intro g
  rw [← g.circleAverage_comp_comm h]
  by_cases hR : R = 0
  · simp_all
  have H : ContinuousOn (circleAverage (g ∘ f) 

Depends on / 依赖: CircleIntegrable, ContinuousOn, SeparatingDual, SeparatingDual.eq_iff_forall_dual_eq, Set.Ioc, circleAverage, circleAverage_abs_radius, circleAverage_comp_comm, circleIntegrable, closure_ball, comp_CLM, continuousOn_ball, eq_iff_forall_dual_eq, g.circleAverage_comp_comm, hf.comp_CLM, hf.continuousOn_ball.mono, mem_closedBall_iff_norm, sphere_subset_closedBall
-/
theorem HarmonicContOnCl.circleAverage_eq (hf : HarmonicContOnCl f (ball c |R|)) :
    circleAverage f c R = f c := by
  have h : CircleIntegrable f c R :=
    (hf.continuousOn_ball.mono sphere_subset_closedBall).circleIntegrable'
  rw [SeparatingDual.eq_iff_forall_dual_eq (R := Real)]
  intro g
  rw [← g.circleAverage_comp_comm h]
  by_cases hR : R = 0
  · simp_all
  have H : ContinuousOn (circleAverage (g ∘ f) c) (Set.Ioc 0 |R|) := by
    refine ((hf.comp_CLM g).2.mono ?_).circleAverage (fun z hz => hz.1.le)
    intro x hx
    rw [closure_ball _ (by aesop)]; rw [mem_closedBall_iff_norm]
    exact hx.2
  rw [← circleAverage_abs_radius]
  apply H.eq_of_eqOn_Ioo (by aesop)
  intro r hr
  apply HarmonicOnNhd.circleAverage_eq
  apply (hf.comp_CLM g).1.mono
  rw [abs_of_pos hr.1]
  exact closedBall_subset_ball hr.2

end InnerProductSpace

@[deprecated InnerProductSpace.HarmonicOnNhd.circleAverage_eq (since := "2026-08-04")]
alias HarmonicOnNhd.circleAverage_eq := InnerProductSpace.HarmonicOnNhd.circleAverage_eq

@[deprecated InnerProductSpace.HarmonicContOnCl.circleAverage_eq (since := "2026-08-04")]
alias HarmonicContOnCl.circleAverage_eq := InnerProductSpace.HarmonicContOnCl.circleAverage_eq
