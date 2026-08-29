/-
Copyright (c) 2025 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.Complex.Conformal
public import Mathlib.Analysis.Complex.HasPrimitives
public import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic

/-!
# Analyticity of Harmonic Functions

If `f : ℂ → ℝ` is harmonic at `x`, we show that `∂f/∂1 - I • ∂f/∂I` is complex-analytic at `x`. If
`f` is harmonic on an open ball, then it is the real part of a function `F : ℂ → ℂ` that is
holomorphic on the ball. This implies in particular that harmonic functions are real-analytic.
-/

public section

open Complex InnerProductSpace Metric Set Topology

variable
  {f : Complex -> Real} {x : Complex}

/--
theorem `HarmonicAt.differentiableAt_complex_partial` / 定理 `HarmonicAt.differentiableAt_complex_partial`

English:
theorem HarmonicAt.differentiableAt_complex_partial
  given: (hf : HarmonicAt f x)
  proof: by
  have : (fun z => fderiv Real f z 1 - I * fderiv Real f z I) =
      (ofRealCLM ∘ (fderiv Real f · 1) - I • ofRealCLM ∘ (fderiv Real f · I)) := by
    ext; simp
  rw [this]
  have h₁f := hf.1
  refine differentiableAt_complex_iff_differentiableAt_real.2 ⟨by fun_prop, ?_⟩
  rw [fderiv_sub (by fun

中文:
定理 HarmonicAt.differentiableAt_complex_partial
  条件: (hf : HarmonicAt f x)
  证明: by
  have : (fun z => fderiv Real f z 1 - I * fderiv Real f z I) =
      (ofRealCLM ∘ (fderiv Real f · 1) - I • ofRealCLM ∘ (fderiv Real f · I)) := by
    ext; simp
  rw [this]
  have h₁f := hf.1
  refine differentiableAt_complex_iff_differentiableAt_real.2 ⟨by fun_prop, ?_⟩
  rw [fderiv_sub (by fun

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.comp_apply, ContinuousLinearMap.fderiv, all_goals, comp_apply, differentiableAt_complex_iff_differentiableAt_real, fderiv, fderiv_comp, fderiv_const_smul, fderiv_sub, fun_prop, ofRealCLM, ofRealCLM_apply, repeat, smul_apply, sub_apply
-/
theorem HarmonicAt.differentiableAt_complex_partial (hf : HarmonicAt f x) :
    DifferentiableAt Complex (fun z => fderiv Real f z 1 - I * fderiv Real f z I) x := by
  have : (fun z => fderiv Real f z 1 - I * fderiv Real f z I) =
      (ofRealCLM ∘ (fderiv Real f · 1) - I • ofRealCLM ∘ (fderiv Real f · I)) := by
    ext; simp
  rw [this]
  have h₁f := hf.1
  refine differentiableAt_complex_iff_differentiableAt_real.2 ⟨by fun_prop, ?_⟩
  rw [fderiv_sub (by fun_prop) (by fun_prop)]; rw [fderiv_const_smul (by fun_prop)]
  repeat rw [fderiv_comp]; all_goals try fun_prop
  simp only [ContinuousLinearMap.fderiv, sub_apply, ContinuousLinearMap.comp_apply, ofRealCLM_apply,
    smul_apply, smul_eq_mul]
  ring_nf
  rw [fderiv_clm_apply (by fun_prop) (by fun_prop)]; rw [fderiv_clm_apply (by fun_prop) (by fun_prop)]
  simp only [fderiv_fun_const, Pi.zero_apply, ContinuousLinearMap.comp_zero, zero_add,
    ContinuousLinearMap.flip_apply, I_sq, neg_mul, one_mul, sub_neg_eq_add]
  rw [add_comm]; rw [sub_eq_add_neg]
  congr 1
  · norm_cast
    apply h₁f.isSymmSndFDerivAt (by simp)
  · have h₂f := hf.2.eq_of_nhds
    simp only [laplacian_eq_iteratedFDeriv_complexPlane, iteratedFDeriv_two_apply, Fin.isValue,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Pi.zero_apply,
      add_eq_zero_iff_eq_neg] at h₂f
    simp [h₂f]

/--
theorem `HarmonicAt.analyticAt_complex_partial` / 定理 `HarmonicAt.analyticAt_complex_partial`

English:
theorem HarmonicAt.analyticAt_complex_partial
  given: (hf : HarmonicAt f x)
  proof: DifferentiableOn.analyticAt (s := { x | HarmonicAt f x })
    (fun _ hy => (HarmonicAt.differentiableAt_complex_partial hy).differentiableWithinAt)
    ((isOpen_setOfPred_harmonicAt f).mem_nhds hf)

中文:
定理 HarmonicAt.analyticAt_complex_partial
  条件: (hf : HarmonicAt f x)
  证明: DifferentiableOn.analyticAt (s := { x | HarmonicAt f x })
    (fun _ hy => (HarmonicAt.differentiableAt_complex_partial hy).differentiableWithinAt)
    ((isOpen_setOfPred_harmonicAt f).mem_nhds hf)

Depends on / 依赖: DifferentiableOn, DifferentiableOn.analyticAt, HarmonicAt, HarmonicAt.differentiableAt_complex_partial, analyticAt, differentiableAt_complex_partial, differentiableWithinAt, isOpen_setOfPred_harmonicAt, mem_nhds
-/
theorem HarmonicAt.analyticAt_complex_partial (hf : HarmonicAt f x) :
    AnalyticAt Complex (fun z => fderiv Real f z 1 - I * fderiv Real f z I) x :=
  DifferentiableOn.analyticAt (s := { x | HarmonicAt f x })
    (fun _ hy => (HarmonicAt.differentiableAt_complex_partial hy).differentiableWithinAt)
    ((isOpen_setOfPred_harmonicAt f).mem_nhds hf)

/--
theorem `InnerProductSpace.HarmonicOnNhd.exists_analyticOnNhd_ball_re_eq` / 定理 `InnerProductSpace.HarmonicOnNhd.exists_analyticOnNhd_ball_re_eq`

English:
theorem InnerProductSpace.HarmonicOnNhd.exists_analyticOnNhd_ball_re_eq
  statement: {z : Complex} {R : Real}
  proof: by
  by_cases hR : R <= 0
  · simp [ball_eq_empty.2 hR]
  let g := ofRealCLM ∘ (fderiv Real f · 1) - I • ofRealCLM ∘ (fderiv Real f · I)
  have hg : DifferentiableOn Complex g (ball z R) :=
    fun x hx => (HarmonicAt.differentiableAt_complex_partial (hf x hx)).differentiableWithinAt
  obtain ⟨F, hF

中文:
定理 内积空间.HarmonicOnNhd.存在_analyticOnNhd_ball_re_eq
  结论: {z : 复形} {R : 实数}
  证明: by
  by_cases hR : R <= 0
  · simp [ball_eq_empty.2 hR]
  let g := ofRealCLM ∘ (fderiv Real f · 1) - I • ofRealCLM ∘ (fderiv Real f · I)
  have hg : DifferentiableOn Complex g (ball z R) :=
    fun x hx => (HarmonicAt.differentiableAt_complex_partial (hf x hx)).differentiableWithinAt
  obtain ⟨F, hF

Depends on / 依赖: DifferentiableOn, F.re, HarmonicAt, HarmonicAt.differentiableAt_complex_partial, ball_eq_empty, differentiableAt, differentiableAt.differentiableWithinAt, differentiableAt_complex_partial, differentiableWithinAt, fderiv, hg.isExactOn_ball.with_val_at, isExactOn_ball, ofRealCLM, with_val_at
-/
theorem InnerProductSpace.HarmonicOnNhd.exists_analyticOnNhd_ball_re_eq {z : Complex} {R : Real}
    (hf : HarmonicOnNhd f (ball z R)) :
    exists F : Complex -> Complex, (AnalyticOnNhd Complex F (ball z R)) ∧ ((ball z R).EqOn (fun z => (F z).re) f) := by
  by_cases hR : R <= 0
  · simp [ball_eq_empty.2 hR]
  let g := ofRealCLM ∘ (fderiv Real f · 1) - I • ofRealCLM ∘ (fderiv Real f · I)
  have hg : DifferentiableOn Complex g (ball z R) :=
    fun x hx => (HarmonicAt.differentiableAt_complex_partial (hf x hx)).differentiableWithinAt
  obtain ⟨F, hF⟩ := hg.isExactOn_ball.with_val_at z (f z)
  have h₁F : DifferentiableOn Complex F (ball z R) :=
    fun x hx => (hF.2 x hx).differentiableAt.differentiableWithinAt
  have h₂F : DifferentiableOn Real F (ball z R) := h₁F.restrictScalars (𝕜 := Real) (𝕜' := Complex)
  use F, h₁F.analyticOnNhd isOpen_ball
  rw [(by aesop : (fun z => (F z).re) = Complex.reCLM ∘ F)]
  intro x hx
  apply (convex_ball z R).eqOn_of_fderivWithin_eq (𝕜 := Real) (x := z)
  · exact reCLM.differentiable.comp_differentiableOn h₂F
  · exact fun y hy => (ContDiffAt.differentiableAt (hf y hy).1 two_ne_zero).differentiableWithinAt
  · exact isOpen_ball.uniqueDiffOn
  · intro y hy
    have h₄F := (hF.2 y hy).differentiableAt
    have h₅F := h₄F.restrictScalars (𝕜 := Real) (𝕜' := Complex)
    rw [fderivWithin_eq_fderiv (isOpen_ball.uniqueDiffWithinAt hy)
      (reCLM.differentiableAt.comp y h₅F)]; rw [fderivWithin_eq_fderiv
      (isOpen_ball.uniqueDiffWithinAt hy) ((hf y hy).1.differentiableAt two_ne_zero)]; rw [fderiv_comp y
      (by fun_prop) h₅F]; rw [ContinuousLinearMap.fderiv]; rw [h₄F.fderiv_restrictScalars (𝕜 := Real)]
    ext a
    nth_rw 2 [(by simp : a = a.re • (1 : Complex) + a.im • (I : Complex))]
    rw [map_add]; rw [map_smul]; rw [map_smul]
    simp [HasDerivAt.deriv (hF.2 y hy), g]
  all_goals simp_all

@[deprecated (since := "2026-03-03")]
alias harmonic_is_realOfHolomorphic :=
  InnerProductSpace.HarmonicOnNhd.exists_analyticOnNhd_ball_re_eq

/--
theorem `InnerProductSpace.HarmonicOnNhd.exists_analyticOnNhd_univ_re_eq` / 定理 `InnerProductSpace.HarmonicOnNhd.exists_analyticOnNhd_univ_re_eq`

English:
theorem InnerProductSpace.HarmonicOnNhd.exists_analyticOnNhd_univ_re_eq
  statement: {f : Complex -> Real}
  proof: by
  let g := ofRealCLM ∘ (fderiv Real f · 1) - I • ofRealCLM ∘ (fderiv Real f · I)
  have hg : Differentiable Complex g :=
    fun x => (HarmonicAt.differentiableAt_complex_partial (hf x (mem_univ x)))
  obtain ⟨F, hF⟩ := hg.isExactOn_univ.with_val_at 0 (f 0)
  have h₁F : forall z₁, HasDerivAt F (g

中文:
定理 内积空间.HarmonicOnNhd.存在_analyticOnNhd_univ_re_eq
  结论: {f : 复形 -> 实数}
  证明: by
  let g := ofRealCLM ∘ (fderiv Real f · 1) - I • ofRealCLM ∘ (fderiv Real f · I)
  have hg : Differentiable Complex g :=
    fun x => (HarmonicAt.differentiableAt_complex_partial (hf x (mem_univ x)))
  obtain ⟨F, hF⟩ := hg.isExactOn_univ.with_val_at 0 (f 0)
  have h₁F : forall z₁, HasDerivAt F (g

Depends on / 依赖: Differentiable, F.differentiableOn, F.restrictScalars, HarmonicAt, HarmonicAt.differentiableAt_complex_partial, HasDerivAt, analyticOnNhd, differentiableAt, differentiableAt_complex_partial, differentiableOn, fderiv, hg.isExactOn_univ.with_val_at, isExactOn_univ, mem_univ, ofRealCLM, restrictScalars, with_val_at
-/
theorem InnerProductSpace.HarmonicOnNhd.exists_analyticOnNhd_univ_re_eq {f : Complex -> Real}
    (hf : HarmonicOnNhd f univ) :
    exists F : Complex -> Complex, (AnalyticOnNhd Complex F univ) ∧ ((fun z => (F z).re) = f) := by
  let g := ofRealCLM ∘ (fderiv Real f · 1) - I • ofRealCLM ∘ (fderiv Real f · I)
  have hg : Differentiable Complex g :=
    fun x => (HarmonicAt.differentiableAt_complex_partial (hf x (mem_univ x)))
  obtain ⟨F, hF⟩ := hg.isExactOn_univ.with_val_at 0 (f 0)
  have h₁F : forall z₁, HasDerivAt F (g z₁) z₁ := by simp_all
  have h₂F : Differentiable Complex F := fun x => (h₁F x).differentiableAt
  have h₃F : Differentiable Real F := h₂F.restrictScalars (𝕜 := Real)
  use F, (h₂F.differentiableOn).analyticOnNhd isOpen_univ
  ext x
  rw [← Complex.reCLM_apply]; rw [← Function.comp_apply (f := reCLM)]
  refine (convex_univ).eqOn_of_fderivWithin_eq (𝕜 := Real) (x := 0) (by fun_prop) ?hd ?_ ?heq ?_ ?_ ?_
  case hd => exact hf.contDiffOn.differentiableOn two_ne_zero
  case heq =>
    intro y hy
    simp only [fderivWithin_univ]
    rw [fderiv_comp y (by fun_prop) (by fun_prop)]
    ext x
    trans fderiv Real f y (x.re • (1 : Complex) + x.im • (I : Complex))
    · simp only [map_smul, map_add]
      simp [(h₁F y).hasFDerivAt.restrictScalars Real |>.fderiv, g]
    · simp
  all_goals simp_all

@[deprecated (since := "2026-03-03")]
alias InnerProductSpace.harmonic_is_realOfHolomorphic_univ :=
  InnerProductSpace.HarmonicOnNhd.exists_analyticOnNhd_univ_re_eq

/--
theorem `HarmonicAt.analyticAt` / 定理 `HarmonicAt.analyticAt`

English:
theorem HarmonicAt.analyticAt
  given: (hf : HarmonicAt f x)
  statement: AnalyticAt Real f x
  proof: by
  obtain ⟨ε, h₁ε, h₂ε⟩ := isOpen_iff.1 (isOpen_setOfPred_harmonicAt (f := f)) x hf
  obtain ⟨F, h₁F, h₂F⟩ := InnerProductSpace.HarmonicOnNhd.exists_analyticOnNhd_ball_re_eq
    (fun _ hy => h₂ε hy)
  rw [analyticAt_congr (Filter.eventually_of_mem (ball_mem_nhds x h₁ε) (fun y hy => h₂F.symm hy))]


中文:
定理 HarmonicAt.analyticAt
  条件: (hf : HarmonicAt f x)
  结论: AnalyticAt 实数 f x
  证明: by
  obtain ⟨ε, h₁ε, h₂ε⟩ := isOpen_iff.1 (isOpen_setOfPred_harmonicAt (f := f)) x hf
  obtain ⟨F, h₁F, h₂F⟩ := InnerProductSpace.HarmonicOnNhd.exists_analyticOnNhd_ball_re_eq
    (fun _ hy => h₂ε hy)
  rw [analyticAt_congr (Filter.eventually_of_mem (ball_mem_nhds x h₁ε) (fun y hy => h₂F.symm hy))]


Depends on / 依赖: F.symm, Filter, Filter.eventually_of_mem, HarmonicOnNhd, InnerProductSpace, InnerProductSpace.HarmonicOnNhd.exists_analyticOnNhd_ball_re_eq, analyticAt, analyticAt_congr, ball_mem_nhds, eventually_of_mem, exists_analyticOnNhd_ball_re_eq, isOpen_iff, isOpen_setOfPred_harmonicAt, mem_ball_self, reCLM.analyticAt, restrictScalars
-/
theorem HarmonicAt.analyticAt (hf : HarmonicAt f x) : AnalyticAt Real f x := by
  obtain ⟨ε, h₁ε, h₂ε⟩ := isOpen_iff.1 (isOpen_setOfPred_harmonicAt (f := f)) x hf
  obtain ⟨F, h₁F, h₂F⟩ := InnerProductSpace.HarmonicOnNhd.exists_analyticOnNhd_ball_re_eq
    (fun _ hy => h₂ε hy)
  rw [analyticAt_congr (Filter.eventually_of_mem (ball_mem_nhds x h₁ε) (fun y hy => h₂F.symm hy))]
  exact (reCLM.analyticAt (F x)).comp (h₁F x (mem_ball_self h₁ε)).restrictScalars
