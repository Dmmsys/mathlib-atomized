/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Floris van Doorn
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Higher differentiability in finite dimensions.

-/

public section


noncomputable section

universe uD uE uF

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {D : Type uD} [NormedAddCommGroup D] [NormedSpace 𝕜 D]
  {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type uF} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {n : WithTop Nat∞} {f : D -> E} {s : Set D}

/-! ### Finite-dimensional results -/

section FiniteDimensional

open Function Module

open scoped ContDiff

variable [CompleteSpace 𝕜]


/--
theorem `contDiffOn_clm_apply` / 定理 `contDiffOn_clm_apply`

English:
theorem contDiffOn_clm_apply
  given: {f : D -> E ->L[𝕜] F} {s : Set D} [FiniteDimensional 𝕜 E]
  proof: by
  refine ⟨fun h y => h.clm_apply contDiffOn_const, fun h => ?_⟩
  let d := finrank 𝕜 E
  have hd : d = finrank 𝕜 (Fin d -> 𝕜) := (finrank_fin_fun 𝕜).symm
  let e₁ := ContinuousLinearEquiv.ofFinrankEq hd
  let e₂ := (e₁.arrowCongr (1 : F ≃L[𝕜] F)).trans (ContinuousLinearEquiv.piRing (Fin d))
  rw [← id_comp f]; rw [← e₂.symm_comp_self]
  exact e₂.symm.contDiff.comp_contDiffOn (contDiffOn_pi.mpr fun i => h _)

中文:
定理 contDiffOn_clm_apply
  条件: {f : D -> E ->L[𝕜] F} {s : 集合 D} [有限维 𝕜 E]
  证明: by
  refine ⟨fun h y => h.clm_apply contDiffOn_const, fun h => ?_⟩
  let d := finrank 𝕜 E
  have hd : d = finrank 𝕜 (Fin d -> 𝕜) := (finrank_fin_fun 𝕜).symm
  let e₁ := ContinuousLinearEquiv.ofFinrankEq hd
  let e₂ := (e₁.arrowCongr (1 : F ≃L[𝕜] F)).trans (ContinuousLinearEquiv.piRing (Fin d))
  rw [← id_comp f]; rw [← e₂.symm_comp_self]
  exact e₂.symm.contDiff.comp_contDiffOn (contDiffOn_pi.mpr fun i => h _)

Depends on / 依赖: ContinuousLinearEquiv, ContinuousLinearEquiv.ofFinrankEq, ContinuousLinearEquiv.piRing, arrowCongr, clm_apply, comp_contDiffOn, contDiff, contDiffOn_const, contDiffOn_pi, contDiffOn_pi.mpr, finrank, finrank_fin_fun, h.clm_apply, id_comp, ofFinrankEq, piRing, symm.contDiff.comp_contDiffOn, symm_comp_self
-/
theorem contDiffOn_clm_apply {f : D -> E ->L[𝕜] F} {s : Set D} [FiniteDimensional 𝕜 E] :
    ContDiffOn 𝕜 n f s ↔ forall y, ContDiffOn 𝕜 n (fun x => f x y) s := by
  refine ⟨fun h y => h.clm_apply contDiffOn_const, fun h => ?_⟩
  let d := finrank 𝕜 E
  have hd : d = finrank 𝕜 (Fin d -> 𝕜) := (finrank_fin_fun 𝕜).symm
  let e₁ := ContinuousLinearEquiv.ofFinrankEq hd
  let e₂ := (e₁.arrowCongr (1 : F ≃L[𝕜] F)).trans (ContinuousLinearEquiv.piRing (Fin d))
  rw [← id_comp f]; rw [← e₂.symm_comp_self]
  exact e₂.symm.contDiff.comp_contDiffOn (contDiffOn_pi.mpr fun i => h _)

/--
theorem `contDiff_clm_apply_iff` / 定理 `contDiff_clm_apply_iff`

English:
theorem contDiff_clm_apply_iff
  given: {f : D -> E ->L[𝕜] F} [FiniteDimensional 𝕜 E]
  proof: by
  simp_rw [← contDiffOn_univ, contDiffOn_clm_apply]

中文:
定理 contDiff_clm_apply_iff
  条件: {f : D -> E ->L[𝕜] F} [有限维 𝕜 E]
  证明: by
  simp_rw [← contDiffOn_univ, contDiffOn_clm_apply]

Depends on / 依赖: contDiffOn_clm_apply, contDiffOn_univ, simp_rw
-/
theorem contDiff_clm_apply_iff {f : D -> E ->L[𝕜] F} [FiniteDimensional 𝕜 E] :
    ContDiff 𝕜 n f ↔ forall y, ContDiff 𝕜 n fun x => f x y := by
  simp_rw [← contDiffOn_univ, contDiffOn_clm_apply]

/--
theorem `contDiff_succ_iff_fderiv_apply` / 定理 `contDiff_succ_iff_fderiv_apply`

English:
theorem contDiff_succ_iff_fderiv_apply
  given: [FiniteDimensional 𝕜 D]
  proof: by
  rw [contDiff_succ_iff_fderiv]; rw [contDiff_clm_apply_iff]

中文:
定理 contDiff_succ_iff_fderiv_apply
  条件: [有限维 𝕜 D]
  证明: by
  rw [contDiff_succ_iff_fderiv]; rw [contDiff_clm_apply_iff]

Depends on / 依赖: contDiff_clm_apply_iff, contDiff_succ_iff_fderiv
-/
theorem contDiff_succ_iff_fderiv_apply [FiniteDimensional 𝕜 D] :
    ContDiff 𝕜 (n + 1) f ↔ Differentiable 𝕜 f ∧
      (n = ω -> AnalyticOnNhd 𝕜 f Set.univ) ∧ forall y, ContDiff 𝕜 n fun x => fderiv 𝕜 f x y := by
  rw [contDiff_succ_iff_fderiv]; rw [contDiff_clm_apply_iff]

/--
theorem `contDiffOn_succ_of_fderiv_apply` / 定理 `contDiffOn_succ_of_fderiv_apply`

English:
theorem contDiffOn_succ_of_fderiv_apply
  statement: [FiniteDimensional 𝕜 D]
  proof: contDiffOn_succ_of_fderivWithin hf h'f contDiffOn_clm_apply.mpr h

中文:
定理 contDiffOn_succ_of_fderiv_apply
  结论: [有限维 𝕜 D]
  证明: contDiffOn_succ_of_fderivWithin hf h'f contDiffOn_clm_apply.mpr h

Depends on / 依赖: contDiffOn_clm_apply, contDiffOn_clm_apply.mpr, contDiffOn_succ_of_fderivWithin
-/
theorem contDiffOn_succ_of_fderiv_apply [FiniteDimensional 𝕜 D]
    (hf : DifferentiableOn 𝕜 f s) (h'f : n = ω -> AnalyticOn 𝕜 f s)
    (h : forall y, ContDiffOn 𝕜 n (fun x => fderivWithin 𝕜 f s x y) s) :
    ContDiffOn 𝕜 (n + 1) f s :=
contDiffOn_succ_of_fderivWithin hf h'f contDiffOn_clm_apply.mpr h

/--
theorem `contDiffOn_succ_iff_fderiv_apply` / 定理 `contDiffOn_succ_iff_fderiv_apply`

English:
theorem contDiffOn_succ_iff_fderiv_apply
  given: [FiniteDimensional 𝕜 D] (hs : UniqueDiffOn 𝕜 s)
  proof: by
  rw [contDiffOn_succ_iff_fderivWithin hs]; rw [contDiffOn_clm_apply]

中文:
定理 contDiffOn_succ_iff_fderiv_apply
  条件: [有限维 𝕜 D] (hs : UniqueDiffOn 𝕜 s)
  证明: by
  rw [contDiffOn_succ_iff_fderivWithin hs]; rw [contDiffOn_clm_apply]

Depends on / 依赖: contDiffOn_clm_apply, contDiffOn_succ_iff_fderivWithin
-/
theorem contDiffOn_succ_iff_fderiv_apply [FiniteDimensional 𝕜 D] (hs : UniqueDiffOn 𝕜 s) :
    ContDiffOn 𝕜 (n + 1) f s ↔
      DifferentiableOn 𝕜 f s ∧ (n = ω -> AnalyticOn 𝕜 f s) ∧
      forall y, ContDiffOn 𝕜 n (fun x => fderivWithin 𝕜 f s x y) s := by
  rw [contDiffOn_succ_iff_fderivWithin hs]; rw [contDiffOn_clm_apply]

end FiniteDimensional
