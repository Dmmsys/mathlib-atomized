/-
Copyright (c) 2024 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Floris van Doorn
-/
module

public import Mathlib.Geometry.Manifold.MFDeriv.Atlas
public import Mathlib.Geometry.Manifold.MFDeriv.UniqueDifferential
public import Mathlib.Geometry.Manifold.VectorBundle.Tangent
public import Mathlib.Geometry.Manifold.Diffeomorph

/-!
# Derivatives of maps in the tangent bundle

This file contains properties of derivatives which need the manifold structure of the tangent
bundle. Notably, it includes formulas for the tangent maps to charts, and unique differentiability
statements for subsets of the tangent bundle.
-/

@[expose] public section

open Bundle Set
open scoped Manifold

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 1 M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {H' : Type*} [TopologicalSpace H']
  {I' : ModelWithCorners 𝕜 E' H'} {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
  [IsManifold I' 1 M']


/--
theorem `tangentMap_chart` / 定理 `tangentMap_chart`

English:
theorem tangentMap_chart
  given: {p q : TangentBundle I M} (h : q.1 in (chartAt H p.1).source)
  proof: by
  dsimp [tangentMap]
  rw [MDifferentiableAt.mfderiv]
  · rfl
  · exact mdifferentiableAt_atlas (chart_mem_atlas _ _) h

中文:
定理 tangentMap_chart
  条件: {p q : 切丛 I M} (h : q.1 in (chartAt H p.1).source)
  证明: by
  dsimp [tangentMap]
  rw [MDifferentiableAt.mfderiv]
  · rfl
  · exact mdifferentiableAt_atlas (chart_mem_atlas _ _) h

Depends on / 依赖: MDifferentiableAt, MDifferentiableAt.mfderiv, chart_mem_atlas, mdifferentiableAt_atlas, mfderiv, tangentMap
-/
theorem tangentMap_chart {p q : TangentBundle I M} (h : q.1 in (chartAt H p.1).source) :
    tangentMap% (chartAt H p.1) q =
      (TotalSpace.toProd _ _).symm
        ((chartAt (ModelProd H E) p : TangentBundle I M -> ModelProd H E) q) := by
  dsimp [tangentMap]
  rw [MDifferentiableAt.mfderiv]
  · rfl
  · exact mdifferentiableAt_atlas (chart_mem_atlas _ _) h

/--
theorem `tangentMap_chart_symm` / 定理 `tangentMap_chart_symm`

English:
theorem tangentMap_chart_symm
  statement: {p : TangentBundle I M} {q : TangentBundle I H}
  proof: by
  dsimp only [tangentMap]
  rw [MDifferentiableAt.mfderiv (mdifferentiableAt_atlas_symm (chart_mem_atlas _ _) h)]
  simp only [TangentBundle.chartAt, tangentBundleCore,
    mfld_simps]
  -- `simp` fails to apply `PartialEquiv.prod_symm` with `ModelProd`
  congr
  exact ((chartAt H (TotalSpace.pro

中文:
定理 tangentMap_chart_symm
  结论: {p : 切丛 I M} {q : 切丛 I H}
  证明: by
  dsimp only [tangentMap]
  rw [MDifferentiableAt.mfderiv (mdifferentiableAt_atlas_symm (chart_mem_atlas _ _) h)]
  simp only [TangentBundle.chartAt, tangentBundleCore,
    mfld_simps]
  -- `simp` fails to apply `PartialEquiv.prod_symm` with `ModelProd`
  congr
  exact ((chartAt H (TotalSpace.pro

Depends on / 依赖: MDifferentiableAt, MDifferentiableAt.mfderiv, TangentBundle, TangentBundle.chartAt, chartAt, chart_mem_atlas, mdifferentiableAt_atlas_symm, mfderiv, mfld_simps, tangentBundleCore, tangentMap
-/
theorem tangentMap_chart_symm {p : TangentBundle I M} {q : TangentBundle I H}
    (h : q.1 in (chartAt H p.1).target) :
    tangentMap% (chartAt H p.1).symm q =
      (chartAt (ModelProd H E) p).symm (TotalSpace.toProd H E q) := by
  dsimp only [tangentMap]
  rw [MDifferentiableAt.mfderiv (mdifferentiableAt_atlas_symm (chart_mem_atlas _ _) h)]
  simp only [TangentBundle.chartAt, tangentBundleCore,
    mfld_simps]
  -- `simp` fails to apply `PartialEquiv.prod_symm` with `ModelProd`
  congr
  exact ((chartAt H (TotalSpace.proj p)).right_inv h).symm

set_option backward.isDefEq.respectTransparency false in
/--
lemma `mfderiv_chartAt_eq_tangentCoordChange` / 引理 `mfderiv_chartAt_eq_tangentCoordChange`

English:
lemma mfderiv_chartAt_eq_tangentCoordChange
  given: {x y : M} (hsrc : x in (chartAt H y).source)
  proof: by
  have := mdifferentiableAt_atlas (I := I) (ChartedSpace.chart_mem_atlas _) hsrc
  simp [mfderiv, if_pos this, Function.comp_assoc]

中文:
引理 mfderiv_chartAt_eq_tangentCoordChange
  条件: {x y : M} (hsrc : x in (chartAt H y).source)
  证明: by
  have := mdifferentiableAt_atlas (I := I) (ChartedSpace.chart_mem_atlas _) hsrc
  simp [mfderiv, if_pos this, Function.comp_assoc]

Depends on / 依赖: ChartedSpace, ChartedSpace.chart_mem_atlas, Function, Function.comp_assoc, chart_mem_atlas, comp_assoc, if_pos, mdifferentiableAt_atlas, mfderiv
-/
lemma mfderiv_chartAt_eq_tangentCoordChange {x y : M} (hsrc : x in (chartAt H y).source) :
    mfderiv% (chartAt H y) x = tangentCoordChange I x y x := by
  have := mdifferentiableAt_atlas (I := I) (ChartedSpace.chart_mem_atlas _) hsrc
  simp [mfderiv, if_pos this, Function.comp_assoc]

/--
theorem `UniqueMDiffOn.tangentBundle_proj_preimage` / 定理 `UniqueMDiffOn.tangentBundle_proj_preimage`

English:
theorem UniqueMDiffOn.tangentBundle_proj_preimage
  given: {s : Set M} (hs : UniqueMDiffOn I s)
  proof: hs.bundle_preimage _

中文:
定理 UniqueMDiffOn.tangentBundle_proj_preimage
  条件: {s : 集合 M} (hs : UniqueMDiffOn I s)
  证明: hs.bundle_preimage _

Depends on / 依赖: bundle_preimage, hs.bundle_preimage
-/
theorem UniqueMDiffOn.tangentBundle_proj_preimage {s : Set M} (hs : UniqueMDiffOn I s) :
    UniqueMDiffOn I.tangent (π E (TangentSpace I) ⁻¹' s) :=
  hs.bundle_preimage _

set_option backward.isDefEq.respectTransparency false in
/--
lemma `inTangentCoordinates_eq_mfderiv_comp` / 引理 `inTangentCoordinates_eq_mfderiv_comp`

English:
lemma inTangentCoordinates_eq_mfderiv_comp
  proof: by
  rw [inTangentCoordinates_eq _ _ _ hx hy]; rw [tangentBundleCore_coordChange]
  congr
  · have : MDiffAt (extChartAt I' (g x₀)) (g x) := mdifferentiableAt_extChartAt hy
    simp_all [mfderiv]
  · simp only [mfderivWithin, writtenInExtChartAt, modelWithCornersSelf_coe, range_id, inter_univ]
    r

中文:
引理 inTangentCoordinates_eq_mfderiv_comp
  证明: by
  rw [inTangentCoordinates_eq _ _ _ hx hy]; rw [tangentBundleCore_coordChange]
  congr
  · have : MDiffAt (extChartAt I' (g x₀)) (g x) := mdifferentiableAt_extChartAt hy
    simp_all [mfderiv]
  · simp only [mfderivWithin, writtenInExtChartAt, modelWithCornersSelf_coe, range_id, inter_univ]
    r

Depends on / 依赖: Function, Function.comp_def, MDiffAt, OpenPartialHomeomorph, OpenPartialHomeomorph.left_inv, chartAt, comp_def, extChartAt, if_pos, inTangentCoordinates_eq, inter_univ, left_inv, map_source, mdifferentiableAt_extChartAt, mdifferentiableWithinAt_extChartAt_symm, mfderiv, mfderivWithin, modelWithCornersSelf_coe, range_id, tangentBundleCore_coordChange
-/
lemma inTangentCoordinates_eq_mfderiv_comp
    {N : Type*} {f : N -> M} {g : N -> M'}
    {ϕ : Π x : N, TangentSpace% (f x) ->L[𝕜] TangentSpace% (g x)} {x₀ : N} {x : N}
    (hx : f x in (chartAt H (f x₀)).source) (hy : g x in (chartAt H' (g x₀)).source) :
    inTangentCoordinates I I' f g ϕ x₀ x =
    (mfderiv% (extChartAt I' (g x₀)) (g x)) ∘L (ϕ x) ∘L
      (mfderiv[range I] (extChartAt I (f x₀)).symm (extChartAt I (f x₀) (f x))) := by
  rw [inTangentCoordinates_eq _ _ _ hx hy]; rw [tangentBundleCore_coordChange]
  congr
  · have : MDiffAt (extChartAt I' (g x₀)) (g x) := mdifferentiableAt_extChartAt hy
    simp_all [mfderiv]
  · simp only [mfderivWithin, writtenInExtChartAt, modelWithCornersSelf_coe, range_id, inter_univ]
    rw [if_pos]
    · simp [Function.comp_def, OpenPartialHomeomorph.left_inv (chartAt H (f x₀)) hx]
    · apply mdifferentiableWithinAt_extChartAt_symm
      apply (extChartAt I (f x₀)).map_source
      simpa using hx

open Bundle
variable (I) in
/--
Definition of `tangentBundleModelSpaceDiffeomorph` / `tangentBundleModelSpaceDiffeomorph` 的定义

English:
definition tangentBundleModelSpaceDiffeomorph
  signature: (n : Nat∞)
  body: TotalSpace.toProd H E
  contMDiff_toFun := contMDiff_tangentBundleModelSpaceHomeomorph
  contMDiff_invFun := contMDiff_tangentBundleModelSpaceHomeomorph_symm

中文:
定义 tangentBundleModelSpaceDiffeomorph
  签名: (n : 自然数∞)
  定义体: TotalSpace.toProd H E
  contMDiff_toFun := contMDiff_tangentBundleModelSpaceHomeomorph
  contMDiff_invFun := contMDiff_tangentBundleModelSpaceHomeomorph_symm

Depends on / 依赖: TotalSpace, TotalSpace.toProd, toProd
-/
def tangentBundleModelSpaceDiffeomorph (n : Nat∞) :
    TangentBundle I H ≃ₘ^n⟮I.tangent, I.prod 𝓘(𝕜, E)⟯ ModelProd H E where
  __ := TotalSpace.toProd H E
  contMDiff_toFun := contMDiff_tangentBundleModelSpaceHomeomorph
  contMDiff_invFun := contMDiff_tangentBundleModelSpaceHomeomorph_symm
