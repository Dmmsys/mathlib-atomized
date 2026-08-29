/-
Copyright (c) 2025 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
module

public import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
public import Mathlib.Analysis.Calculus.ContDiff.RestrictScalars
public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

/-!
# Construction of Harmonic Functions

This file constructs examples of harmonic functions.

If `f : ℂ → F` is complex-differentiable, then `f` is harmonic. If `F = ℂ`, then so is its real
part, imaginary part, and complex conjugate. If `f` has no zero, then `log ‖f‖` is harmonic.
-/

public section

open Complex ComplexConjugate InnerProductSpace Topology

variable
  {F : Type*} [NormedAddCommGroup F] [NormedSpace Complex F]
  {f : Complex -> F} {x : Complex}

/-!
## Harmonicity of Analytic Functions on the Complex Plane
-/

/--
theorem `ContDiffAt.harmonicAt` / 定理 `ContDiffAt.harmonicAt`

English:
theorem ContDiffAt.harmonicAt
  given: (h : ContDiffAt Complex 2 f x)
  statement: HarmonicAt f x
  proof: by
  refine ⟨h.restrict_scalars Real, ?_⟩
  filter_upwards [h.restrictScalars_iteratedFDeriv_eventuallyEq (𝕜 := Real)] with a ha
  have : (iteratedFDeriv Complex 2 f a) (I • ![1, 1])
      = (∏ i, I) • ((iteratedFDeriv Complex 2 f a) ![1, 1]) :=
    (iteratedFDeriv Complex 2 f a).map_smul_univ (fun 

中文:
定理 ContDiffAt.harmonicAt
  条件: (h : ContDiffAt Complex 2 f x)
  结论: HarmonicAt f x
  证明: by
  refine ⟨h.restrict_scalars Real, ?_⟩
  filter_upwards [h.restrictScalars_iteratedFDeriv_eventuallyEq (𝕜 := Real)] with a ha
  have : (iteratedFDeriv Complex 2 f a) (I • ![1, 1])
      = (∏ i, I) • ((iteratedFDeriv Complex 2 f a) ![1, 1]) :=
    (iteratedFDeriv Complex 2 f a).map_smul_univ (fun 

Depends on / 依赖: ContinuousMultilinearMap, ContinuousMultilinearMap.coe_restrictScalars, coe_restrictScalars, filter_upwards, h.restrictScalars_iteratedFDeriv_eventuallyEq, h.restrict_scalars, iteratedFDeriv, laplacian_eq_iteratedFDeriv_complexPlane, map_smul_univ, restrictScalars_iteratedFDeriv_eventuallyEq, restrict_scalars
-/
theorem ContDiffAt.harmonicAt (h : ContDiffAt Complex 2 f x) : HarmonicAt f x := by
  refine ⟨h.restrict_scalars Real, ?_⟩
  filter_upwards [h.restrictScalars_iteratedFDeriv_eventuallyEq (𝕜 := Real)] with a ha
  have : (iteratedFDeriv Complex 2 f a) (I • ![1, 1])
      = (∏ i, I) • ((iteratedFDeriv Complex 2 f a) ![1, 1]) :=
    (iteratedFDeriv Complex 2 f a).map_smul_univ (fun _ => I) ![1, 1]
  simp_all [laplacian_eq_iteratedFDeriv_complexPlane f, ← ha,
    ContinuousMultilinearMap.coe_restrictScalars]

/--
theorem `AnalyticAt.harmonicAt` / 定理 `AnalyticAt.harmonicAt`

English:
theorem AnalyticAt.harmonicAt
  given: [CompleteSpace F] (h : AnalyticAt Complex f x)
  statement: HarmonicAt f x
  proof: h.contDiffAt.harmonicAt

中文:
定理 AnalyticAt.harmonicAt
  条件: [CompleteSpace F] (h : AnalyticAt Complex f x)
  结论: HarmonicAt f x
  证明: h.contDiffAt.harmonicAt

Depends on / 依赖: contDiffAt, h.contDiffAt.harmonicAt, harmonicAt
-/
theorem AnalyticAt.harmonicAt [CompleteSpace F] (h : AnalyticAt Complex f x) : HarmonicAt f x :=
  h.contDiffAt.harmonicAt

/--
theorem `AnalyticAt.harmonicAt_re` / 定理 `AnalyticAt.harmonicAt_re`

English:
theorem AnalyticAt.harmonicAt_re
  given: {f : Complex -> Complex} (h : AnalyticAt Complex f x)
  proof: h.harmonicAt.comp_CLM reCLM

中文:
定理 AnalyticAt.harmonicAt_re
  条件: {f : Complex -> Complex} (h : AnalyticAt Complex f x)
  证明: h.harmonicAt.comp_CLM reCLM

Depends on / 依赖: comp_CLM, h.harmonicAt.comp_CLM, harmonicAt
-/
theorem AnalyticAt.harmonicAt_re {f : Complex -> Complex} (h : AnalyticAt Complex f x) :
    HarmonicAt (fun z => (f z).re) x := h.harmonicAt.comp_CLM reCLM

/--
theorem `AnalyticAt.harmonicAt_im` / 定理 `AnalyticAt.harmonicAt_im`

English:
theorem AnalyticAt.harmonicAt_im
  given: {f : Complex -> Complex} (h : AnalyticAt Complex f x)
  proof: h.harmonicAt.comp_CLM imCLM

中文:
定理 AnalyticAt.harmonicAt_im
  条件: {f : Complex -> Complex} (h : AnalyticAt Complex f x)
  证明: h.harmonicAt.comp_CLM imCLM

Depends on / 依赖: comp_CLM, h.harmonicAt.comp_CLM, harmonicAt
-/
theorem AnalyticAt.harmonicAt_im {f : Complex -> Complex} (h : AnalyticAt Complex f x) :
    HarmonicAt (fun z => (f z).im) x :=
  h.harmonicAt.comp_CLM imCLM

/--
theorem `AnalyticAt.harmonicAt_conj` / 定理 `AnalyticAt.harmonicAt_conj`

English:
theorem AnalyticAt.harmonicAt_conj
  given: {f : Complex -> Complex} (h : AnalyticAt Complex f x)
  statement: HarmonicAt (conj f) x
  proof: (harmonicAt_comp_CLE_iff conjCLE).2 h.harmonicAt

中文:
定理 AnalyticAt.harmonicAt_conj
  条件: {f : Complex -> Complex} (h : AnalyticAt Complex f x)
  结论: HarmonicAt (conj f) x
  证明: (harmonicAt_comp_CLE_iff conjCLE).2 h.harmonicAt

Depends on / 依赖: conjCLE, h.harmonicAt, harmonicAt, harmonicAt_comp_CLE_iff
-/
theorem AnalyticAt.harmonicAt_conj {f : Complex -> Complex} (h : AnalyticAt Complex f x) : HarmonicAt (conj f) x :=
  (harmonicAt_comp_CLE_iff conjCLE).2 h.harmonicAt

/-!
## Harmonicity of `log ‖analytic‖`
-/

/--
lemma `analyticAt_harmonicAt_log_normSq` / 引理 `analyticAt_harmonicAt_log_normSq`

English:
lemma analyticAt_harmonicAt_log_normSq
  statement: {z : Complex} {g : Complex -> Complex} (h₁g : AnalyticAt Complex g z)
  proof: by
  rw [harmonicAt_congr_nhds (f₂ := reCLM ∘ (conjCLE ∘ log ∘ g + log ∘ g))]
  · exact (((harmonicAt_comp_CLE_iff conjCLE).2 ((analyticAt_clog h₃g).comp h₁g).harmonicAt).add
      ((analyticAt_clog h₃g).comp h₁g).harmonicAt).comp_CLM reCLM
  · have t₀ := h₁g.differentiableAt.continuousAt.preimage_m

中文:
引理 analyticAt_harmonicAt_log_normSq
  结论: {z : Complex} {g : Complex -> Complex} (h₁g : AnalyticAt Complex g z)
  证明: by
  rw [harmonicAt_congr_nhds (f₂ := reCLM ∘ (conjCLE ∘ log ∘ g + log ∘ g))]
  · exact (((harmonicAt_comp_CLE_iff conjCLE).2 ((analyticAt_clog h₃g).comp h₁g).harmonicAt).add
      ((analyticAt_clog h₃g).comp h₁g).harmonicAt).comp_CLM reCLM
  · have t₀ := h₁g.differentiableAt.continuousAt.preimage_m
-/
private lemma analyticAt_harmonicAt_log_normSq {z : Complex} {g : Complex -> Complex} (h₁g : AnalyticAt Complex g z)
    (h₂g : g z != 0) (h₃g : g z in slitPlane) :
    HarmonicAt (Real.log ∘ normSq ∘ g) z := by
  rw [harmonicAt_congr_nhds (f₂ := reCLM ∘ (conjCLE ∘ log ∘ g + log ∘ g))]
  · exact (((harmonicAt_comp_CLE_iff conjCLE).2 ((analyticAt_clog h₃g).comp h₁g).harmonicAt).add
      ((analyticAt_clog h₃g).comp h₁g).harmonicAt).comp_CLM reCLM
  · have t₀ := h₁g.differentiableAt.continuousAt.preimage_mem_nhds
      ((isOpen_slitPlane.inter isOpen_ne).mem_nhds ⟨h₃g, h₂g⟩)
    calc Real.log ∘ normSq ∘ g
    _ =ᶠ[𝓝 z] reCLM ∘ ofRealCLM ∘ Real.log ∘ normSq ∘ g := by aesop
    _ =ᶠ[𝓝 z] reCLM ∘ log ∘ ((conjCLE ∘ g) * g) := by
      filter_upwards with x
      simp only [Function.comp_apply, ofRealCLM_apply, Pi.mul_apply, conjCLE_apply]
      rw [ofReal_log]; rw [normSq_eq_conj_mul_self]
      exact normSq_nonneg (g x)
    _ =ᶠ[𝓝 z] reCLM ∘ (log ∘ conjCLE ∘ g + log ∘ g) := by
      filter_upwards [t₀] with x hx
      simp only [Function.comp_apply, Pi.mul_apply, conjCLE_apply, Pi.add_apply]
      congr
      rw [Complex.log_mul_eq_add_log_iff _ hx.2]; rw [Complex.arg_conj]
      · simp [Complex.slitPlane_arg_ne_pi hx.1, Real.pi_pos, Real.pi_nonneg]
      · simpa [ne_eq, map_eq_zero] using hx.2
    _ =ᶠ[𝓝 z] ⇑reCLM ∘ (⇑conjCLE ∘ log ∘ g + log ∘ g) := by
      apply Filter.eventuallyEq_iff_exists_mem.2
      use g ⁻¹' (Complex.slitPlane inter {0}ᶜ), t₀
      intro x hx
      simp only [Function.comp_apply, Pi.add_apply, conjCLE_apply]
      congr 1
      rw [← Complex.log_conj]
      simp [Complex.slitPlane_arg_ne_pi hx.1]

/--
theorem `AnalyticAt.harmonicAt_log_norm` / 定理 `AnalyticAt.harmonicAt_log_norm`

English:
theorem AnalyticAt.harmonicAt_log_norm
  statement: {f : Complex -> Complex} {z : Complex} (h₁f : AnalyticAt Complex f z)
  proof: by
  have : (Real.log ‖f ·‖) = (2 : Real)⁻¹ • (Real.log ∘ Complex.normSq ∘ f) := by
    funext z
    simp only [Pi.smul_apply, Function.comp_apply, smul_eq_mul]
    rw [Complex.norm_def]; rw [Real.log_sqrt]
    · linarith
    exact (f z).normSq_nonneg
  rw [this]
  apply HarmonicAt.const_smul
  by_c

中文:
定理 AnalyticAt.harmonicAt_log_norm
  结论: {f : Complex -> Complex} {z : Complex} (h₁f : AnalyticAt Complex f z)
  证明: by
  have : (Real.log ‖f ·‖) = (2 : Real)⁻¹ • (Real.log ∘ Complex.normSq ∘ f) := by
    funext z
    simp only [Pi.smul_apply, Function.comp_apply, smul_eq_mul]
    rw [Complex.norm_def]; rw [Real.log_sqrt]
    · linarith
    exact (f z).normSq_nonneg
  rw [this]
  apply HarmonicAt.const_smul
  by_c

Depends on / 依赖: Complex.normSq, Complex.norm_def, Complex.slitPlane, Function, Function.comp_apply, HarmonicAt, HarmonicAt.const_smul, Pi.smul_apply, Real.log, Real.log_sqrt, analyticAt_harmonicAt_log_normSq, comp_apply, const_smul, f.neg, log_sqrt, mem_slitPlane_or, normSq, normSq_nonneg, norm_def, slitPlane
-/
theorem AnalyticAt.harmonicAt_log_norm {f : Complex -> Complex} {z : Complex} (h₁f : AnalyticAt Complex f z)
    (h₂f : f z != 0) :
    HarmonicAt (Real.log ‖f ·‖) z := by
  have : (Real.log ‖f ·‖) = (2 : Real)⁻¹ • (Real.log ∘ Complex.normSq ∘ f) := by
    funext z
    simp only [Pi.smul_apply, Function.comp_apply, smul_eq_mul]
    rw [Complex.norm_def]; rw [Real.log_sqrt]
    · linarith
    exact (f z).normSq_nonneg
  rw [this]
  apply HarmonicAt.const_smul
  by_cases h₃f : f z in Complex.slitPlane
  · exact analyticAt_harmonicAt_log_normSq h₁f h₂f h₃f
  · rw [(by aesop : Complex.normSq ∘ f = Complex.normSq ∘ (-f))]
    exact analyticAt_harmonicAt_log_normSq h₁f.neg (by simpa)
      ((mem_slitPlane_or_neg_mem_slitPlane h₂f).resolve_left h₃f)
