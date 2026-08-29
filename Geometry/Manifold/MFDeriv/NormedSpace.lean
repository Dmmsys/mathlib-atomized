/-
Copyright (c) 2024 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Floris van Doorn
-/
module

public import Mathlib.Geometry.Manifold.Algebra.SMul
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
public import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions

/-! # Equivalence of manifold differentiability with the basic definition for functions between
vector spaces

The API in this file is mostly copied from `Mathlib/Geometry/Manifold/ContMDiff/NormedSpace.lean`,
providing the same statements for higher smoothness. In this file, we do the same for
differentiability.

## Main definitions

In addition to the above, this file provides two important definitions.
* `mvfderiv I f x` is the manifold Fréchet derivative at `x : M` of a vector-valued function
  `f : M → V`, but taking values in the target normed space `V` instead of `TangentSpace% (f x) V`.
  Mathematically, this uses the global trivialization `T V ≅ V × V`, yielding an identification
  `T_v V ≅ V` for each `v : V`. In Lean, we post-compose the differential `mfderiv% f x` with
  `NormedSpace.fromTangentSpace`. If `V` is a field, this coincides with the exterior derivative
  of `f` as a section of the cotangent bundle.
  There is notation `d% f` for `mvfderiv I f` via a custom elaborator scoped to the
  `Manifold` namespace, with a corresponding delaborator,
* `mvfderivWithin` with notation `d[s] f` for `mvfderivWithin I f s` in the `Manifold` namespace:
  the analogous concept within a set, with analogous API lemmas

## Main results

This file contains
* results about the differentiability of scalar multiplication (`mfderiv_smul` and friends),
* basic lemmas about `mvfderiv` (such as addition, subtraction, multiplication and constants),
* analogous lemmas about `mvfderivWithin`,
* composition lemmas about `mvfderivWithin` and `mvfderiv`.

-/

public section

open Set ChartedSpace IsManifold
open scoped Topology Manifold

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {n : WithTop Nat∞}
  -- declare a charted space `M` over the pair `(E, H)`.
  {E : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  -- declare a `C^n` manifold `M'` over the pair `(E', H')`.
  {E' : Type*}
  [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {H' : Type*} [TopologicalSpace H']
  {I' : ModelWithCorners 𝕜 E' H'} {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
  [IsManifold I' n M']
  -- declare a `C^n` manifold `N` over the pair `(F, G)`.
  {F : Type*}
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] {G : Type*} [TopologicalSpace G]
  {J : ModelWithCorners 𝕜 F G} {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  [IsManifold J n N]
  -- declare a `C^n` manifold `N'` over the pair `(F', G')`.
  {F' : Type*}
  [NormedAddCommGroup F'] [NormedSpace 𝕜 F'] {G' : Type*} [TopologicalSpace G']
  {J' : ModelWithCorners 𝕜 F' G'} {N' : Type*} [TopologicalSpace N'] [ChartedSpace G' N']
  [IsManifold J' n N']
  -- F₁, F₂, F₃, F₄ are normed spaces
  {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] {F₂ : Type*} [NormedAddCommGroup F₂]
  [NormedSpace 𝕜 F₂] {F₃ : Type*} [NormedAddCommGroup F₃] [NormedSpace 𝕜 F₃] {F₄ : Type*}
  [NormedAddCommGroup F₄] [NormedSpace 𝕜 F₄]
  -- declare functions, sets, points and smoothness indices
  {f f₁ : M -> M'} {s t : Set M} {x : M} {m n : Nat∞}

section Module

/--
theorem `DifferentiableWithinAt.comp_mdifferentiableWithinAt` / 定理 `DifferentiableWithinAt.comp_mdifferentiableWithinAt`

English:
theorem DifferentiableWithinAt.comp_mdifferentiableWithinAt
  proof: hg.mdifferentiableWithinAt.comp x hf h

中文:
定理 DifferentiableWithinAt.comp_mdifferentiableWithinAt
  证明: hg.mdifferentiableWithinAt.comp x hf h

Depends on / 依赖: hg.mdifferentiableWithinAt.comp, mdifferentiableWithinAt
-/
theorem DifferentiableWithinAt.comp_mdifferentiableWithinAt
    {g : F -> F'} {f : M -> F} {s : Set M} {t : Set F} {x : M}
    (hg : DifferentiableWithinAt 𝕜 g t (f x)) (hf : MDiffAt[s] f x) (h : MapsTo f s t) :
    MDiffAt[s] (g ∘ f) x :=
  hg.mdifferentiableWithinAt.comp x hf h

/--
theorem `DifferentiableAt.comp_mdifferentiableWithinAt` / 定理 `DifferentiableAt.comp_mdifferentiableWithinAt`

English:
theorem DifferentiableAt.comp_mdifferentiableWithinAt
  statement: {g : F -> F'} {f : M -> F} {s : Set M} {x : M}
  proof: hg.mdifferentiableAt.comp_mdifferentiableWithinAt x hf

中文:
定理 DifferentiableAt.comp_mdifferentiableWithinAt
  结论: {g : F -> F'} {f : M -> F} {s : 集合 M} {x : M}
  证明: hg.mdifferentiableAt.comp_mdifferentiableWithinAt x hf

Depends on / 依赖: comp_mdifferentiableWithinAt, hg.mdifferentiableAt.comp_mdifferentiableWithinAt, mdifferentiableAt
-/
theorem DifferentiableAt.comp_mdifferentiableWithinAt {g : F -> F'} {f : M -> F} {s : Set M} {x : M}
    (hg : DifferentiableAt 𝕜 g (f x)) (hf : MDiffAt[s] f x) : MDiffAt[s] (g ∘ f) x :=
  hg.mdifferentiableAt.comp_mdifferentiableWithinAt x hf

/--
theorem `DifferentiableAt.comp_mdifferentiableAt` / 定理 `DifferentiableAt.comp_mdifferentiableAt`

English:
theorem DifferentiableAt.comp_mdifferentiableAt
  statement: {g : F -> F'} {f : M -> F} {x : M}
  proof: hg.comp_mdifferentiableWithinAt hf

中文:
定理 DifferentiableAt.comp_mdifferentiableAt
  结论: {g : F -> F'} {f : M -> F} {x : M}
  证明: hg.comp_mdifferentiableWithinAt hf

Depends on / 依赖: comp_mdifferentiableWithinAt, hg.comp_mdifferentiableWithinAt
-/
theorem DifferentiableAt.comp_mdifferentiableAt {g : F -> F'} {f : M -> F} {x : M}
    (hg : DifferentiableAt 𝕜 g (f x)) (hf : MDiffAt f x) : MDiffAt (g ∘ f) x :=
  hg.comp_mdifferentiableWithinAt hf

/--
theorem `Differentiable.comp_mdifferentiableWithinAt` / 定理 `Differentiable.comp_mdifferentiableWithinAt`

English:
theorem Differentiable.comp_mdifferentiableWithinAt
  statement: {g : F -> F'} {f : M -> F} {s : Set M} {x : M}
  proof: hg.differentiableAt.comp_mdifferentiableWithinAt hf

中文:
定理 可微.comp_mdifferentiableWithinAt
  结论: {g : F -> F'} {f : M -> F} {s : 集合 M} {x : M}
  证明: hg.differentiableAt.comp_mdifferentiableWithinAt hf

Depends on / 依赖: comp_mdifferentiableWithinAt, differentiableAt, hg.differentiableAt.comp_mdifferentiableWithinAt
-/
theorem Differentiable.comp_mdifferentiableWithinAt {g : F -> F'} {f : M -> F} {s : Set M} {x : M}
    (hg : Differentiable 𝕜 g) (hf : MDiffAt[s] f x) : MDiffAt[s] (g ∘ f) x :=
  hg.differentiableAt.comp_mdifferentiableWithinAt hf

/--
theorem `Differentiable.comp_mdifferentiableAt` / 定理 `Differentiable.comp_mdifferentiableAt`

English:
theorem Differentiable.comp_mdifferentiableAt
  statement: {g : F -> F'} {f : M -> F} {x : M}
  proof: hg.comp_mdifferentiableWithinAt hf

中文:
定理 可微.comp_mdifferentiableAt
  结论: {g : F -> F'} {f : M -> F} {x : M}
  证明: hg.comp_mdifferentiableWithinAt hf

Depends on / 依赖: comp_mdifferentiableWithinAt, hg.comp_mdifferentiableWithinAt
-/
theorem Differentiable.comp_mdifferentiableAt {g : F -> F'} {f : M -> F} {x : M}
    (hg : Differentiable 𝕜 g) (hf : MDiffAt f x) : MDiffAt (g ∘ f) x :=
  hg.comp_mdifferentiableWithinAt hf

/--
theorem `Differentiable.comp_mdifferentiable` / 定理 `Differentiable.comp_mdifferentiable`

English:
theorem Differentiable.comp_mdifferentiable
  statement: {g : F -> F'} {f : M -> F}
  proof: fun x => hg.differentiableAt.comp_mdifferentiableAt (hf x)

中文:
定理 可微.comp_mdifferentiable
  结论: {g : F -> F'} {f : M -> F}
  证明: fun x => hg.differentiableAt.comp_mdifferentiableAt (hf x)

Depends on / 依赖: comp_mdifferentiableAt, differentiableAt, hg.differentiableAt.comp_mdifferentiableAt
-/
theorem Differentiable.comp_mdifferentiable {g : F -> F'} {f : M -> F}
    (hg : Differentiable 𝕜 g) (hf : MDiff f) : MDiff (g ∘ f) :=
  fun x => hg.differentiableAt.comp_mdifferentiableAt (hf x)

end Module

section extChartAt

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] {f : M -> F}

set_option backward.isDefEq.respectTransparency.types false in
-- TODO: add pre-composition version also
/--
theorem `MDifferentiableWithinAt.differentiableWithinAt_comp_extChartAt_symm` / 定理 `MDifferentiableWithinAt.differentiableWithinAt_comp_extChartAt_symm`

English:
theorem MDifferentiableWithinAt.differentiableWithinAt_comp_extChartAt_symm
  given: (hf : MDiffAt[s] f x)
  proof: extChartAt I x
    DifferentiableWithinAt 𝕜 (f ∘ φ.symm) (φ.symm ⁻¹' s inter range I) (φ x) := by
  simpa [extChartAt_self_eq] using (mdifferentiableWithinAt_iff.1 hf).2

中文:
定理 MDifferentiableWithinAt.differentiableWithinAt_comp_extChartAt_symm
  条件: (hf : MDiffAt[s] f x)
  证明: extChartAt I x
    DifferentiableWithinAt 𝕜 (f ∘ φ.symm) (φ.symm ⁻¹' s inter range I) (φ x) := by
  simpa [extChartAt_self_eq] using (mdifferentiableWithinAt_iff.1 hf).2

Depends on / 依赖: extChartAt
-/
theorem MDifferentiableWithinAt.differentiableWithinAt_comp_extChartAt_symm (hf : MDiffAt[s] f x) :
    letI φ := extChartAt I x
    DifferentiableWithinAt 𝕜 (f ∘ φ.symm) (φ.symm ⁻¹' s inter range I) (φ x) := by
  simpa [extChartAt_self_eq] using (mdifferentiableWithinAt_iff.1 hf).2

-- TODO: the `IsManifold I 1 M` assumption can probably be removed
/--
theorem `DifferentiableWithinAt.mdifferentiableWithinAt_of_comp_extChartAt_symm` / 定理 `DifferentiableWithinAt.mdifferentiableWithinAt_of_comp_extChartAt_symm`

English:
theorem DifferentiableWithinAt.mdifferentiableWithinAt_of_comp_extChartAt_symm
  statement: [IsManifold I 1 M]
  proof: by
  refine (mdifferentiableWithinAt_iff_source_of_mem_source (mem_chart_source H x)).2 ?_
  simpa [extChartAt_self_eq] using hf.mdifferentiableWithinAt

中文:
定理 DifferentiableWithinAt.mdifferentiableWithinAt_of_comp_extChartAt_symm
  结论: [是流形 I 1 M]
  证明: by
  refine (mdifferentiableWithinAt_iff_source_of_mem_source (mem_chart_source H x)).2 ?_
  simpa [extChartAt_self_eq] using hf.mdifferentiableWithinAt

Depends on / 依赖: extChartAt
-/
theorem DifferentiableWithinAt.mdifferentiableWithinAt_of_comp_extChartAt_symm [IsManifold I 1 M]
    (hf : letI φ := extChartAt I x
      DifferentiableWithinAt 𝕜 (f ∘ φ.symm) (φ.symm ⁻¹' s inter range I) (φ x)) :
    MDiffAt[s] f x := by
  refine (mdifferentiableWithinAt_iff_source_of_mem_source (mem_chart_source H x)).2 ?_
  simpa [extChartAt_self_eq] using hf.mdifferentiableWithinAt

end extChartAt


/--
theorem `MDifferentiableWithinAt.clm_precomp` / 定理 `MDifferentiableWithinAt.clm_precomp`

English:
theorem MDifferentiableWithinAt.clm_precomp
  statement: {f : M -> F₁ ->L[𝕜] F₂} {s : Set M} {x : M}
  proof: Differentiable.comp_mdifferentiableWithinAt
    (ContinuousLinearMap.differentiable (ContinuousLinearMap.compL 𝕜 F₁ F₂ F₃).flip) hf

nonrec theorem MDifferentiableAt.clm_precomp {f : M -> F₁ ->L[𝕜] F₂} {x : M} (hf : MDiffAt f x) :
    MDiffAt (fun y => (f y).precomp F₃ : M -> (F₂ ->L[𝕜] F₃) ->L[𝕜] (F₁ ->L[𝕜] F₃)) x :=
  Differentiable.comp_mdifferentiableAt
    (ContinuousLinearMap.differentiable (ContinuousLinearMap.compL 𝕜 F₁ F₂ F₃).flip) hf

中文:
定理 MDifferentiableWithinAt.clm_precomp
  结论: {f : M -> F₁ ->L[𝕜] F₂} {s : 集合 M} {x : M}
  证明: Differentiable.comp_mdifferentiableWithinAt
    (ContinuousLinearMap.differentiable (ContinuousLinearMap.compL 𝕜 F₁ F₂ F₃).flip) hf

nonrec theorem MDifferentiableAt.clm_precomp {f : M -> F₁ ->L[𝕜] F₂} {x : M} (hf : MDiffAt f x) :
    MDiffAt (fun y => (f y).precomp F₃ : M -> (F₂ ->L[𝕜] F₃) ->L[𝕜] (F₁ ->L[𝕜] F₃)) x :=
  Differentiable.comp_mdifferentiableAt
    (ContinuousLinearMap.differentiable (ContinuousLinearMap.compL 𝕜 F₁ F₂ F₃).flip) hf

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.compL, ContinuousLinearMap.differentiable, Differentiable, Differentiable.comp_mdifferentiableWithinAt, comp_mdifferentiableWithinAt, differentiable
-/
theorem MDifferentiableWithinAt.clm_precomp {f : M -> F₁ ->L[𝕜] F₂} {s : Set M} {x : M}
    (hf : MDiffAt[s] f x) :
    MDiffAt[s] (fun y => (f y).precomp F₃ : M -> (F₂ ->L[𝕜] F₃) ->L[𝕜] (F₁ ->L[𝕜] F₃)) x :=
  Differentiable.comp_mdifferentiableWithinAt
    (ContinuousLinearMap.differentiable (ContinuousLinearMap.compL 𝕜 F₁ F₂ F₃).flip) hf

nonrec theorem MDifferentiableAt.clm_precomp {f : M -> F₁ ->L[𝕜] F₂} {x : M} (hf : MDiffAt f x) :
    MDiffAt (fun y => (f y).precomp F₃ : M -> (F₂ ->L[𝕜] F₃) ->L[𝕜] (F₁ ->L[𝕜] F₃)) x :=
  Differentiable.comp_mdifferentiableAt
    (ContinuousLinearMap.differentiable (ContinuousLinearMap.compL 𝕜 F₁ F₂ F₃).flip) hf

/--
theorem `MDifferentiableOn.clm_precomp` / 定理 `MDifferentiableOn.clm_precomp`

English:
theorem MDifferentiableOn.clm_precomp
  given: {f : M -> F₁ ->L[𝕜] F₂} {s : Set M} (hf : MDiff[s] f)
  proof: fun x hx => (hf x hx).clm_precomp

中文:
定理 MDifferentiableOn.clm_precomp
  条件: {f : M -> F₁ ->L[𝕜] F₂} {s : 集合 M} (hf : MDiff[s] f)
  证明: fun x hx => (hf x hx).clm_precomp

Depends on / 依赖: clm_precomp
-/
theorem MDifferentiableOn.clm_precomp {f : M -> F₁ ->L[𝕜] F₂} {s : Set M} (hf : MDiff[s] f) :
    MDiff[s] (fun y => (f y).precomp F₃ : M -> (F₂ ->L[𝕜] F₃) ->L[𝕜] (F₁ ->L[𝕜] F₃)) :=
  fun x hx => (hf x hx).clm_precomp

/--
theorem `MDifferentiable.clm_precomp` / 定理 `MDifferentiable.clm_precomp`

English:
theorem MDifferentiable.clm_precomp
  given: {f : M -> F₁ ->L[𝕜] F₂} (hf : MDiff f)
  proof: fun x => (hf x).clm_precomp

中文:
定理 MDifferentiable.clm_precomp
  条件: {f : M -> F₁ ->L[𝕜] F₂} (hf : MDiff f)
  证明: fun x => (hf x).clm_precomp

Depends on / 依赖: clm_precomp
-/
theorem MDifferentiable.clm_precomp {f : M -> F₁ ->L[𝕜] F₂} (hf : MDiff f) :
    MDiff (fun y => (f y).precomp F₃ : M -> (F₂ ->L[𝕜] F₃) ->L[𝕜] (F₁ ->L[𝕜] F₃)) :=
  fun x => (hf x).clm_precomp

/--
theorem `MDifferentiableWithinAt.clm_postcomp` / 定理 `MDifferentiableWithinAt.clm_postcomp`

English:
theorem MDifferentiableWithinAt.clm_postcomp
  statement: {f : M -> F₂ ->L[𝕜] F₃} {s : Set M} {x : M}
  proof: Differentiable.comp_mdifferentiableWithinAt
    (ContinuousLinearMap.differentiable (ContinuousLinearMap.compL 𝕜 F₁ F₂ F₃)) hf

中文:
定理 MDifferentiableWithinAt.clm_postcomp
  结论: {f : M -> F₂ ->L[𝕜] F₃} {s : 集合 M} {x : M}
  证明: Differentiable.comp_mdifferentiableWithinAt
    (ContinuousLinearMap.differentiable (ContinuousLinearMap.compL 𝕜 F₁ F₂ F₃)) hf

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.compL, ContinuousLinearMap.differentiable, Differentiable, Differentiable.comp_mdifferentiableWithinAt, comp_mdifferentiableWithinAt, differentiable
-/
theorem MDifferentiableWithinAt.clm_postcomp {f : M -> F₂ ->L[𝕜] F₃} {s : Set M} {x : M}
    (hf : MDiffAt[s] f x) :
    MDiffAt[s] (fun y => (f y).postcomp F₁ : M -> (F₁ ->L[𝕜] F₂) ->L[𝕜] (F₁ ->L[𝕜] F₃)) x :=
  Differentiable.comp_mdifferentiableWithinAt
    (ContinuousLinearMap.differentiable (ContinuousLinearMap.compL 𝕜 F₁ F₂ F₃)) hf

/--
theorem `MDifferentiableAt.clm_postcomp` / 定理 `MDifferentiableAt.clm_postcomp`

English:
theorem MDifferentiableAt.clm_postcomp
  given: {f : M -> F₂ ->L[𝕜] F₃} {x : M} (hf : MDiffAt f x)
  proof: Differentiable.comp_mdifferentiableAt
    (ContinuousLinearMap.differentiable (ContinuousLinearMap.compL 𝕜 F₁ F₂ F₃)) hf

nonrec theorem MDifferentiableOn.clm_postcomp {f : M -> F₂ ->L[𝕜] F₃} {s : Set M} (hf : MDiff[s] f) :
    MDiff[s] (fun y => (f y).postcomp F₁ : M -> (F₁ ->L[𝕜] F₂) ->L[𝕜] (F₁ ->L[𝕜] F₃)) := fun x hx =>
  (hf x hx).clm_postcomp

中文:
定理 MDifferentiableAt.clm_postcomp
  条件: {f : M -> F₂ ->L[𝕜] F₃} {x : M} (hf : MDiffAt f x)
  证明: Differentiable.comp_mdifferentiableAt
    (ContinuousLinearMap.differentiable (ContinuousLinearMap.compL 𝕜 F₁ F₂ F₃)) hf

nonrec theorem MDifferentiableOn.clm_postcomp {f : M -> F₂ ->L[𝕜] F₃} {s : Set M} (hf : MDiff[s] f) :
    MDiff[s] (fun y => (f y).postcomp F₁ : M -> (F₁ ->L[𝕜] F₂) ->L[𝕜] (F₁ ->L[𝕜] F₃)) := fun x hx =>
  (hf x hx).clm_postcomp

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.compL, ContinuousLinearMap.differentiable, Differentiable, Differentiable.comp_mdifferentiableAt, comp_mdifferentiableAt, differentiable
-/
theorem MDifferentiableAt.clm_postcomp {f : M -> F₂ ->L[𝕜] F₃} {x : M} (hf : MDiffAt f x) :
    MDiffAt (fun y => (f y).postcomp F₁ : M -> (F₁ ->L[𝕜] F₂) ->L[𝕜] (F₁ ->L[𝕜] F₃)) x :=
  Differentiable.comp_mdifferentiableAt
    (ContinuousLinearMap.differentiable (ContinuousLinearMap.compL 𝕜 F₁ F₂ F₃)) hf

nonrec theorem MDifferentiableOn.clm_postcomp {f : M -> F₂ ->L[𝕜] F₃} {s : Set M} (hf : MDiff[s] f) :
    MDiff[s] (fun y => (f y).postcomp F₁ : M -> (F₁ ->L[𝕜] F₂) ->L[𝕜] (F₁ ->L[𝕜] F₃)) := fun x hx =>
  (hf x hx).clm_postcomp

/--
theorem `MDifferentiable.clm_postcomp` / 定理 `MDifferentiable.clm_postcomp`

English:
theorem MDifferentiable.clm_postcomp
  given: {f : M -> F₂ ->L[𝕜] F₃} (hf : MDiff f)
  proof: fun x => (hf x).clm_postcomp

中文:
定理 MDifferentiable.clm_postcomp
  条件: {f : M -> F₂ ->L[𝕜] F₃} (hf : MDiff f)
  证明: fun x => (hf x).clm_postcomp

Depends on / 依赖: clm_postcomp
-/
theorem MDifferentiable.clm_postcomp {f : M -> F₂ ->L[𝕜] F₃} (hf : MDiff f) :
    MDiff (fun y => (f y).postcomp F₁ : M -> (F₁ ->L[𝕜] F₂) ->L[𝕜] (F₁ ->L[𝕜] F₃)) :=
  fun x => (hf x).clm_postcomp

/--
theorem `MDifferentiableWithinAt.clm_comp` / 定理 `MDifferentiableWithinAt.clm_comp`

English:
theorem MDifferentiableWithinAt.clm_comp
  proof: Differentiable.comp_mdifferentiableWithinAt
    (g := fun x : (F₁ ->L[𝕜] F₃) × (F₂ ->L[𝕜] F₁) => x.1.comp x.2)
    (f := fun x => (g x, f x)) (differentiable_fst.clm_comp differentiable_snd)
    (hg.prodMk_space hf)

中文:
定理 MDifferentiableWithinAt.clm_comp
  证明: Differentiable.comp_mdifferentiableWithinAt
    (g := fun x : (F₁ ->L[𝕜] F₃) × (F₂ ->L[𝕜] F₁) => x.1.comp x.2)
    (f := fun x => (g x, f x)) (differentiable_fst.clm_comp differentiable_snd)
    (hg.prodMk_space hf)

Depends on / 依赖: Differentiable, Differentiable.comp_mdifferentiableWithinAt, clm_comp, comp_mdifferentiableWithinAt, differentiable_fst, differentiable_fst.clm_comp, differentiable_snd, hg.prodMk_space, prodMk_space
-/
theorem MDifferentiableWithinAt.clm_comp
    {g : M -> F₁ ->L[𝕜] F₃} {f : M -> F₂ ->L[𝕜] F₁} {s : Set M} {x : M}
    (hg : MDiffAt[s] g x) (hf : MDiffAt[s] f x) :
    MDiffAt[s] (fun x => (g x).comp (f x)) x :=
  Differentiable.comp_mdifferentiableWithinAt
    (g := fun x : (F₁ ->L[𝕜] F₃) × (F₂ ->L[𝕜] F₁) => x.1.comp x.2)
    (f := fun x => (g x, f x)) (differentiable_fst.clm_comp differentiable_snd)
    (hg.prodMk_space hf)

/--
theorem `MDifferentiableAt.clm_comp` / 定理 `MDifferentiableAt.clm_comp`

English:
theorem MDifferentiableAt.clm_comp
  statement: {g : M -> F₁ ->L[𝕜] F₃} {f : M -> F₂ ->L[𝕜] F₁} {x : M}
  proof: (hg.mdifferentiableWithinAt.clm_comp hf.mdifferentiableWithinAt).mdifferentiableAt Filter.univ_mem

中文:
定理 MDifferentiableAt.clm_comp
  结论: {g : M -> F₁ ->L[𝕜] F₃} {f : M -> F₂ ->L[𝕜] F₁} {x : M}
  证明: (hg.mdifferentiableWithinAt.clm_comp hf.mdifferentiableWithinAt).mdifferentiableAt Filter.univ_mem

Depends on / 依赖: Filter, Filter.univ_mem, clm_comp, hf.mdifferentiableWithinAt, hg.mdifferentiableWithinAt.clm_comp, mdifferentiableAt, mdifferentiableWithinAt, univ_mem
-/
theorem MDifferentiableAt.clm_comp {g : M -> F₁ ->L[𝕜] F₃} {f : M -> F₂ ->L[𝕜] F₁} {x : M}
    (hg : MDiffAt g x) (hf : MDiffAt f x) :
    MDiffAt (fun x => (g x).comp (f x)) x :=
  (hg.mdifferentiableWithinAt.clm_comp hf.mdifferentiableWithinAt).mdifferentiableAt Filter.univ_mem

/--
theorem `MDifferentiableOn.clm_comp` / 定理 `MDifferentiableOn.clm_comp`

English:
theorem MDifferentiableOn.clm_comp
  statement: {g : M -> F₁ ->L[𝕜] F₃} {f : M -> F₂ ->L[𝕜] F₁} {s : Set M}
  proof: fun x hx => (hg x hx).clm_comp (hf x hx)

中文:
定理 MDifferentiableOn.clm_comp
  结论: {g : M -> F₁ ->L[𝕜] F₃} {f : M -> F₂ ->L[𝕜] F₁} {s : 集合 M}
  证明: fun x hx => (hg x hx).clm_comp (hf x hx)

Depends on / 依赖: clm_comp
-/
theorem MDifferentiableOn.clm_comp {g : M -> F₁ ->L[𝕜] F₃} {f : M -> F₂ ->L[𝕜] F₁} {s : Set M}
    (hg : MDiff[s] g) (hf : MDiff[s] f) : MDiff[s] (fun x => (g x).comp (f x)) :=
  fun x hx => (hg x hx).clm_comp (hf x hx)

/--
theorem `MDifferentiable.clm_comp` / 定理 `MDifferentiable.clm_comp`

English:
theorem MDifferentiable.clm_comp
  statement: {g : M -> F₁ ->L[𝕜] F₃} {f : M -> F₂ ->L[𝕜] F₁}
  proof: fun x => (hg x).clm_comp (hf x)

中文:
定理 MDifferentiable.clm_comp
  结论: {g : M -> F₁ ->L[𝕜] F₃} {f : M -> F₂ ->L[𝕜] F₁}
  证明: fun x => (hg x).clm_comp (hf x)

Depends on / 依赖: clm_comp
-/
theorem MDifferentiable.clm_comp {g : M -> F₁ ->L[𝕜] F₃} {f : M -> F₂ ->L[𝕜] F₁}
    (hg : MDiff g) (hf : MDiff f) : MDiff fun x => (g x).comp (f x) :=
  fun x => (hg x).clm_comp (hf x)

/--
theorem `MDifferentiableWithinAt.clm_apply` / 定理 `MDifferentiableWithinAt.clm_apply`

English:
theorem MDifferentiableWithinAt.clm_apply
  statement: {g : M -> F₁ ->L[𝕜] F₂} {f : M -> F₁} {s : Set M} {x : M}
  proof: DifferentiableWithinAt.comp_mdifferentiableWithinAt (t := univ)
    (g := fun x : (F₁ ->L[𝕜] F₂) × F₁ => x.1 x.2)
    (by apply (Differentiable.differentiableAt _).differentiableWithinAt
        exact differentiable_fst.clm_apply differentiable_snd) (hg.prodMk_space hf)
    (by simp_rw [mapsTo_univ])

中文:
定理 MDifferentiableWithinAt.clm_apply
  结论: {g : M -> F₁ ->L[𝕜] F₂} {f : M -> F₁} {s : 集合 M} {x : M}
  证明: DifferentiableWithinAt.comp_mdifferentiableWithinAt (t := univ)
    (g := fun x : (F₁ ->L[𝕜] F₂) × F₁ => x.1 x.2)
    (by apply (Differentiable.differentiableAt _).differentiableWithinAt
        exact differentiable_fst.clm_apply differentiable_snd) (hg.prodMk_space hf)
    (by simp_rw [mapsTo_univ])

Depends on / 依赖: Differentiable, Differentiable.differentiableAt, DifferentiableWithinAt, DifferentiableWithinAt.comp_mdifferentiableWithinAt, clm_apply, comp_mdifferentiableWithinAt, differentiableAt, differentiableWithinAt, differentiable_fst, differentiable_fst.clm_apply, differentiable_snd, hg.prodMk_space, mapsTo_univ, prodMk_space, simp_rw
-/
theorem MDifferentiableWithinAt.clm_apply {g : M -> F₁ ->L[𝕜] F₂} {f : M -> F₁} {s : Set M} {x : M}
    (hg : MDiffAt[s] g x) (hf : MDiffAt[s] f x) :
    MDiffAt[s] (fun x => g x (f x)) x :=
  DifferentiableWithinAt.comp_mdifferentiableWithinAt (t := univ)
    (g := fun x : (F₁ ->L[𝕜] F₂) × F₁ => x.1 x.2)
    (by apply (Differentiable.differentiableAt _).differentiableWithinAt
        exact differentiable_fst.clm_apply differentiable_snd) (hg.prodMk_space hf)
    (by simp_rw [mapsTo_univ])

/--
theorem `MDifferentiableAt.clm_apply` / 定理 `MDifferentiableAt.clm_apply`

English:
theorem MDifferentiableAt.clm_apply
  statement: {g : M -> F₁ ->L[𝕜] F₂} {f : M -> F₁} {x : M}
  proof: DifferentiableWithinAt.comp_mdifferentiableWithinAt (t := univ)
    (g := fun x : (F₁ ->L[𝕜] F₂) × F₁ => x.1 x.2)
    (by apply (Differentiable.differentiableAt _).differentiableWithinAt
        exact differentiable_fst.clm_apply differentiable_snd) (hg.prodMk_space hf)
    (by simp_rw [mapsTo_univ])

中文:
定理 MDifferentiableAt.clm_apply
  结论: {g : M -> F₁ ->L[𝕜] F₂} {f : M -> F₁} {x : M}
  证明: DifferentiableWithinAt.comp_mdifferentiableWithinAt (t := univ)
    (g := fun x : (F₁ ->L[𝕜] F₂) × F₁ => x.1 x.2)
    (by apply (Differentiable.differentiableAt _).differentiableWithinAt
        exact differentiable_fst.clm_apply differentiable_snd) (hg.prodMk_space hf)
    (by simp_rw [mapsTo_univ])

Depends on / 依赖: Differentiable, Differentiable.differentiableAt, DifferentiableWithinAt, DifferentiableWithinAt.comp_mdifferentiableWithinAt, clm_apply, comp_mdifferentiableWithinAt, differentiableAt, differentiableWithinAt, differentiable_fst, differentiable_fst.clm_apply, differentiable_snd, hg.prodMk_space, mapsTo_univ, prodMk_space, simp_rw
-/
theorem MDifferentiableAt.clm_apply {g : M -> F₁ ->L[𝕜] F₂} {f : M -> F₁} {x : M}
    (hg : MDiffAt g x) (hf : MDiffAt f x) : MDiffAt (fun x => g x (f x)) x :=
  DifferentiableWithinAt.comp_mdifferentiableWithinAt (t := univ)
    (g := fun x : (F₁ ->L[𝕜] F₂) × F₁ => x.1 x.2)
    (by apply (Differentiable.differentiableAt _).differentiableWithinAt
        exact differentiable_fst.clm_apply differentiable_snd) (hg.prodMk_space hf)
    (by simp_rw [mapsTo_univ])

/--
theorem `MDifferentiableOn.clm_apply` / 定理 `MDifferentiableOn.clm_apply`

English:
theorem MDifferentiableOn.clm_apply
  statement: {g : M -> F₁ ->L[𝕜] F₂} {f : M -> F₁} {s : Set M}
  proof: fun x hx => (hg x hx).clm_apply (hf x hx)

中文:
定理 MDifferentiableOn.clm_apply
  结论: {g : M -> F₁ ->L[𝕜] F₂} {f : M -> F₁} {s : 集合 M}
  证明: fun x hx => (hg x hx).clm_apply (hf x hx)

Depends on / 依赖: clm_apply
-/
theorem MDifferentiableOn.clm_apply {g : M -> F₁ ->L[𝕜] F₂} {f : M -> F₁} {s : Set M}
    (hg : MDiff[s] g) (hf : MDiff[s] f) : MDiff[s] (fun x => g x (f x)) :=
  fun x hx => (hg x hx).clm_apply (hf x hx)

/--
theorem `MDifferentiable.clm_apply` / 定理 `MDifferentiable.clm_apply`

English:
theorem MDifferentiable.clm_apply
  statement: {g : M -> F₁ ->L[𝕜] F₂} {f : M -> F₁}
  proof: fun x => (hg x).clm_apply (hf x)

中文:
定理 MDifferentiable.clm_apply
  结论: {g : M -> F₁ ->L[𝕜] F₂} {f : M -> F₁}
  证明: fun x => (hg x).clm_apply (hf x)

Depends on / 依赖: clm_apply
-/
theorem MDifferentiable.clm_apply {g : M -> F₁ ->L[𝕜] F₂} {f : M -> F₁}
    (hg : MDiff g) (hf : MDiff f) : MDiff fun x => g x (f x) :=
  fun x => (hg x).clm_apply (hf x)

/--
theorem `MDifferentiableWithinAt.cle_arrowCongr` / 定理 `MDifferentiableWithinAt.cle_arrowCongr`

English:
theorem MDifferentiableWithinAt.cle_arrowCongr
  proof: show MDifferentiableWithinAt I 𝓘(𝕜, (F₁ ->L[𝕜] F₃) ->L[𝕜] (F₂ ->L[𝕜] F₄))
    (fun y => (((f y).symm : F₂ ->L[𝕜] F₁).precomp F₄).comp ((g y : F₃ ->L[𝕜] F₄).postcomp F₁)) s x
.clm_comp hg.clm_postcomp (F₁ := F₁) from hf.clm_precomp (F₃ := F₄)

中文:
定理 MDifferentiableWithinAt.cle_arrowCongr
  证明: show MDifferentiableWithinAt I 𝓘(𝕜, (F₁ ->L[𝕜] F₃) ->L[𝕜] (F₂ ->L[𝕜] F₄))
    (fun y => (((f y).symm : F₂ ->L[𝕜] F₁).precomp F₄).comp ((g y : F₃ ->L[𝕜] F₄).postcomp F₁)) s x
.clm_comp hg.clm_postcomp (F₁ := F₁) from hf.clm_precomp (F₃ := F₄)

Depends on / 依赖: MDifferentiableWithinAt, clm_comp, clm_postcomp, clm_precomp, hf.clm_precomp, hg.clm_postcomp, postcomp, precomp
-/
theorem MDifferentiableWithinAt.cle_arrowCongr
    {f : M -> F₁ ≃L[𝕜] F₂} {g : M -> F₃ ≃L[𝕜] F₄} {s : Set M} {x : M}
    (hf : MDiffAt[s] (fun x => ((f x).symm : F₂ ->L[𝕜] F₁)) x)
    (hg : MDiffAt[s] (fun x => (g x : F₃ ->L[𝕜] F₄)) x) :
    MDiffAt[s] (fun y => (f y).arrowCongr (g y) : M -> (F₁ ->L[𝕜] F₃) ->L[𝕜] (F₂ ->L[𝕜] F₄)) x :=
  show MDifferentiableWithinAt I 𝓘(𝕜, (F₁ ->L[𝕜] F₃) ->L[𝕜] (F₂ ->L[𝕜] F₄))
    (fun y => (((f y).symm : F₂ ->L[𝕜] F₁).precomp F₄).comp ((g y : F₃ ->L[𝕜] F₄).postcomp F₁)) s x
.clm_comp hg.clm_postcomp (F₁ := F₁) from hf.clm_precomp (F₃ := F₄)

/--
theorem `MDifferentiableAt.cle_arrowCongr` / 定理 `MDifferentiableAt.cle_arrowCongr`

English:
theorem MDifferentiableAt.cle_arrowCongr
  statement: {f : M -> F₁ ≃L[𝕜] F₂} {g : M -> F₃ ≃L[𝕜] F₄} {x : M}
  proof: show MDifferentiableAt I 𝓘(𝕜, (F₁ ->L[𝕜] F₃) ->L[𝕜] (F₂ ->L[𝕜] F₄))
    (fun y => (((f y).symm : F₂ ->L[𝕜] F₁).precomp F₄).comp ((g y : F₃ ->L[𝕜] F₄).postcomp F₁)) x
.clm_comp hg.clm_postcomp (F₁ := F₁) from hf.clm_precomp (F₃ := F₄)

中文:
定理 MDifferentiableAt.cle_arrowCongr
  结论: {f : M -> F₁ ≃L[𝕜] F₂} {g : M -> F₃ ≃L[𝕜] F₄} {x : M}
  证明: show MDifferentiableAt I 𝓘(𝕜, (F₁ ->L[𝕜] F₃) ->L[𝕜] (F₂ ->L[𝕜] F₄))
    (fun y => (((f y).symm : F₂ ->L[𝕜] F₁).precomp F₄).comp ((g y : F₃ ->L[𝕜] F₄).postcomp F₁)) x
.clm_comp hg.clm_postcomp (F₁ := F₁) from hf.clm_precomp (F₃ := F₄)

Depends on / 依赖: MDifferentiableAt, clm_comp, clm_postcomp, clm_precomp, hf.clm_precomp, hg.clm_postcomp, postcomp, precomp
-/
theorem MDifferentiableAt.cle_arrowCongr {f : M -> F₁ ≃L[𝕜] F₂} {g : M -> F₃ ≃L[𝕜] F₄} {x : M}
    (hf : MDiffAt (fun x => ((f x).symm : F₂ ->L[𝕜] F₁)) x)
    (hg : MDiffAt (fun x => (g x : F₃ ->L[𝕜] F₄)) x) :
    MDiffAt (fun y => (f y).arrowCongr (g y) : M -> (F₁ ->L[𝕜] F₃) ->L[𝕜] (F₂ ->L[𝕜] F₄)) x :=
  show MDifferentiableAt I 𝓘(𝕜, (F₁ ->L[𝕜] F₃) ->L[𝕜] (F₂ ->L[𝕜] F₄))
    (fun y => (((f y).symm : F₂ ->L[𝕜] F₁).precomp F₄).comp ((g y : F₃ ->L[𝕜] F₄).postcomp F₁)) x
.clm_comp hg.clm_postcomp (F₁ := F₁) from hf.clm_precomp (F₃ := F₄)

/--
theorem `MDifferentiableOn.cle_arrowCongr` / 定理 `MDifferentiableOn.cle_arrowCongr`

English:
theorem MDifferentiableOn.cle_arrowCongr
  statement: {f : M -> F₁ ≃L[𝕜] F₂} {g : M -> F₃ ≃L[𝕜] F₄} {s : Set M}
  proof: fun x hx =>
  (hf x hx).cle_arrowCongr (hg x hx)

中文:
定理 MDifferentiableOn.cle_arrowCongr
  结论: {f : M -> F₁ ≃L[𝕜] F₂} {g : M -> F₃ ≃L[𝕜] F₄} {s : 集合 M}
  证明: fun x hx =>
  (hf x hx).cle_arrowCongr (hg x hx)
-/
theorem MDifferentiableOn.cle_arrowCongr {f : M -> F₁ ≃L[𝕜] F₂} {g : M -> F₃ ≃L[𝕜] F₄} {s : Set M}
    (hf : MDiff[s] (fun x => ((f x).symm : F₂ ->L[𝕜] F₁)))
    (hg : MDiff[s] (fun x => (g x : F₃ ->L[𝕜] F₄))) :
    MDiff[s] (fun y => (f y).arrowCongr (g y) : M -> (F₁ ->L[𝕜] F₃) ->L[𝕜] (F₂ ->L[𝕜] F₄)) := fun x hx =>
  (hf x hx).cle_arrowCongr (hg x hx)

/--
theorem `MDifferentiable.cle_arrowCongr` / 定理 `MDifferentiable.cle_arrowCongr`

English:
theorem MDifferentiable.cle_arrowCongr
  statement: {f : M -> F₁ ≃L[𝕜] F₂} {g : M -> F₃ ≃L[𝕜] F₄}
  proof: fun x =>
  (hf x).cle_arrowCongr (hg x)

中文:
定理 MDifferentiable.cle_arrowCongr
  结论: {f : M -> F₁ ≃L[𝕜] F₂} {g : M -> F₃ ≃L[𝕜] F₄}
  证明: fun x =>
  (hf x).cle_arrowCongr (hg x)
-/
theorem MDifferentiable.cle_arrowCongr {f : M -> F₁ ≃L[𝕜] F₂} {g : M -> F₃ ≃L[𝕜] F₄}
    (hf : MDiff (fun x => ((f x).symm : F₂ ->L[𝕜] F₁)))
    (hg : MDiff (fun x => (g x : F₃ ->L[𝕜] F₄))) :
    MDiff (fun y => (f y).arrowCongr (g y) : M -> (F₁ ->L[𝕜] F₃) ->L[𝕜] (F₂ ->L[𝕜] F₄)) := fun x =>
  (hf x).cle_arrowCongr (hg x)

/--
theorem `MDifferentiableWithinAt.clm_prodMap` / 定理 `MDifferentiableWithinAt.clm_prodMap`

English:
theorem MDifferentiableWithinAt.clm_prodMap
  statement: {g : M -> F₁ ->L[𝕜] F₃} {f : M -> F₂ ->L[𝕜] F₄} {s : Set M}
  proof: Differentiable.comp_mdifferentiableWithinAt
    (g := fun x : (F₁ ->L[𝕜] F₃) × (F₂ ->L[𝕜] F₄) => x.1.prodMap x.2)
    (f := fun x => (g x, f x)) (ContinuousLinearMap.prodMapL 𝕜 F₁ F₃ F₂ F₄).differentiable
    (hg.prodMk_space hf)

nonrec theorem MDifferentiableAt.clm_prodMap {g : M -> F₁ ->L[𝕜] F₃} {f : M -> F₂ ->L[𝕜] F₄} {x : M}
    (hg : MDiffAt g x) (hf : MDiffAt f x) : MDiffAt (fun x => (g x).prodMap (f x)) x :=
  Differentiable.comp_mdifferentiableWithinAt
    (g := fun x : (F₁ ->L[𝕜] F₃) × (F₂ ->L[𝕜] F₄) => x.1.prodMap x.2)
    (f := fun x => (g x, f x)) (ContinuousLinearMap.prodMapL 𝕜 F₁ F₃ F₂ F₄).differentiable
    (hg.prodMk_space hf)

中文:
定理 MDifferentiableWithinAt.clm_prodMap
  结论: {g : M -> F₁ ->L[𝕜] F₃} {f : M -> F₂ ->L[𝕜] F₄} {s : 集合 M}
  证明: Differentiable.comp_mdifferentiableWithinAt
    (g := fun x : (F₁ ->L[𝕜] F₃) × (F₂ ->L[𝕜] F₄) => x.1.prodMap x.2)
    (f := fun x => (g x, f x)) (ContinuousLinearMap.prodMapL 𝕜 F₁ F₃ F₂ F₄).differentiable
    (hg.prodMk_space hf)

nonrec theorem MDifferentiableAt.clm_prodMap {g : M -> F₁ ->L[𝕜] F₃} {f : M -> F₂ ->L[𝕜] F₄} {x : M}
    (hg : MDiffAt g x) (hf : MDiffAt f x) : MDiffAt (fun x => (g x).prodMap (f x)) x :=
  Differentiable.comp_mdifferentiableWithinAt
    (g := fun x : (F₁ ->L[𝕜] F₃) × (F₂ ->L[𝕜] F₄) => x.1.prodMap x.2)
    (f := fun x => (g x, f x)) (ContinuousLinearMap.prodMapL 𝕜 F₁ F₃ F₂ F₄).differentiable
    (hg.prodMk_space hf)

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.prodMapL, Differentiable, Differentiable.comp_mdifferentiableWithinAt, comp_mdifferentiableWithinAt, differentiable, hg.prodMk_space, prodMap, prodMapL, prodMk_space
-/
theorem MDifferentiableWithinAt.clm_prodMap {g : M -> F₁ ->L[𝕜] F₃} {f : M -> F₂ ->L[𝕜] F₄} {s : Set M}
    {x : M} (hg : MDiffAt[s] g x) (hf : MDiffAt[s] f x) :
    MDiffAt[s] (fun x => (g x).prodMap (f x)) x :=
  Differentiable.comp_mdifferentiableWithinAt
    (g := fun x : (F₁ ->L[𝕜] F₃) × (F₂ ->L[𝕜] F₄) => x.1.prodMap x.2)
    (f := fun x => (g x, f x)) (ContinuousLinearMap.prodMapL 𝕜 F₁ F₃ F₂ F₄).differentiable
    (hg.prodMk_space hf)

nonrec theorem MDifferentiableAt.clm_prodMap {g : M -> F₁ ->L[𝕜] F₃} {f : M -> F₂ ->L[𝕜] F₄} {x : M}
    (hg : MDiffAt g x) (hf : MDiffAt f x) : MDiffAt (fun x => (g x).prodMap (f x)) x :=
  Differentiable.comp_mdifferentiableWithinAt
    (g := fun x : (F₁ ->L[𝕜] F₃) × (F₂ ->L[𝕜] F₄) => x.1.prodMap x.2)
    (f := fun x => (g x, f x)) (ContinuousLinearMap.prodMapL 𝕜 F₁ F₃ F₂ F₄).differentiable
    (hg.prodMk_space hf)

/--
theorem `MDifferentiableOn.clm_prodMap` / 定理 `MDifferentiableOn.clm_prodMap`

English:
theorem MDifferentiableOn.clm_prodMap
  statement: {g : M -> F₁ ->L[𝕜] F₃} {f : M -> F₂ ->L[𝕜] F₄} {s : Set M}
  proof: fun x hx => (hg x hx).clm_prodMap (hf x hx)

中文:
定理 MDifferentiableOn.clm_prodMap
  结论: {g : M -> F₁ ->L[𝕜] F₃} {f : M -> F₂ ->L[𝕜] F₄} {s : 集合 M}
  证明: fun x hx => (hg x hx).clm_prodMap (hf x hx)

Depends on / 依赖: clm_prodMap
-/
theorem MDifferentiableOn.clm_prodMap {g : M -> F₁ ->L[𝕜] F₃} {f : M -> F₂ ->L[𝕜] F₄} {s : Set M}
    (hg : MDiff[s] g) (hf : MDiff[s] f) :
    MDiff[s] (fun x => (g x).prodMap (f x)) :=
  fun x hx => (hg x hx).clm_prodMap (hf x hx)

/--
theorem `MDifferentiable.clm_prodMap` / 定理 `MDifferentiable.clm_prodMap`

English:
theorem MDifferentiable.clm_prodMap
  statement: {g : M -> F₁ ->L[𝕜] F₃} {f : M -> F₂ ->L[𝕜] F₄}
  proof: fun x => (hg x).clm_prodMap (hf x)

中文:
定理 MDifferentiable.clm_prodMap
  结论: {g : M -> F₁ ->L[𝕜] F₃} {f : M -> F₂ ->L[𝕜] F₄}
  证明: fun x => (hg x).clm_prodMap (hf x)

Depends on / 依赖: clm_prodMap
-/
theorem MDifferentiable.clm_prodMap {g : M -> F₁ ->L[𝕜] F₃} {f : M -> F₂ ->L[𝕜] F₄}
    (hg : MDiff g) (hf : MDiff f) : MDiff fun x => (g x).prodMap (f x) :=
  fun x => (hg x).clm_prodMap (hf x)

/-! ### Differentiability of scalar multiplication -/

section smul

open NormedSpace ContinuousLinearMap

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V]
variable {f : M -> 𝕜} {g : M -> V}

-- TODO: investigate inlining this proof entirely!
/--
lemma `HasMFDerivAt.smul` / 引理 `HasMFDerivAt.smul`

English:
lemma HasMFDerivAt.smul
  proof: (fromTangentSpace _).symm.toContinuousLinearMap ∘L g'
    -- canonically identify `g x` with a linear map into a tangent space at `(f • g) x`
    letI gx : 𝕜 ->L[𝕜] TangentSpace% ((f • g) x) :=
      toSpanSingleton 𝕜 ((fromTangentSpace _).symm (g x))
    -- now the main statement typechecks
    HasMFDerivAt% (f • g) x (f x • g'_ + gx ∘L f') := by
  constructor
  · exact hs.1.smul hg.1
  · simpa using! hs.2.smul hg.2

中文:
引理 HasMFDerivAt.smul
  证明: (fromTangentSpace _).symm.toContinuousLinearMap ∘L g'
    -- canonically identify `g x` with a linear map into a tangent space at `(f • g) x`
    letI gx : 𝕜 ->L[𝕜] TangentSpace% ((f • g) x) :=
      toSpanSingleton 𝕜 ((fromTangentSpace _).symm (g x))
    -- now the main statement typechecks
    HasMFDerivAt% (f • g) x (f x • g'_ + gx ∘L f') := by
  constructor
  · exact hs.1.smul hg.1
  · simpa using! hs.2.smul hg.2
-/
private lemma HasMFDerivAt.smul
    {f' : TangentSpace% x ->L[𝕜] 𝕜}
    (hs : HasMFDerivAt% f x ((fromTangentSpace (f x)).symm.toContinuousLinearMap ∘L f'))
    {g' : TangentSpace% x ->L[𝕜] V}
    (hg : HasMFDerivAt% g x ((fromTangentSpace (g x)).symm.toContinuousLinearMap ∘L g')) :
    -- canonically identify `g'` with a linear map into the tangent space at `(f • g) x`
    letI g'_ : TangentSpace% x ->L[𝕜] TangentSpace 𝓘(𝕜, V) ((f • g) x) :=
      (fromTangentSpace _).symm.toContinuousLinearMap ∘L g'
    -- canonically identify `g x` with a linear map into a tangent space at `(f • g) x`
    letI gx : 𝕜 ->L[𝕜] TangentSpace% ((f • g) x) :=
      toSpanSingleton 𝕜 ((fromTangentSpace _).symm (g x))
    -- now the main statement typechecks
    HasMFDerivAt% (f • g) x (f x • g'_ + gx ∘L f') := by
  constructor
  · exact hs.1.smul hg.1
  · simpa using! hs.2.smul hg.2

/--
theorem `MDifferentiableWithinAt.smul` / 定理 `MDifferentiableWithinAt.smul`

English:
theorem MDifferentiableWithinAt.smul
  proof: ((contMDiff_smul.of_le le_top).mdifferentiable one_ne_zero _).comp_mdifferentiableWithinAt x
    (hf.prodMk hg)

@[to_fun]

中文:
定理 MDifferentiableWithinAt.smul
  证明: ((contMDiff_smul.of_le le_top).mdifferentiable one_ne_zero _).comp_mdifferentiableWithinAt x
    (hf.prodMk hg)

@[to_fun]

Depends on / 依赖: comp_mdifferentiableWithinAt, contMDiff_smul, contMDiff_smul.of_le, hf.prodMk, le_top, mdifferentiable, of_le, one_ne_zero, prodMk
-/
theorem MDifferentiableWithinAt.smul
    (hf : MDiffAt[s] f x) (hg : MDiffAt[s] g x) :
    MDiffAt[s] (fun p => f p • g p) x :=
  ((contMDiff_smul.of_le le_top).mdifferentiable one_ne_zero _).comp_mdifferentiableWithinAt x
    (hf.prodMk hg)

@[to_fun]
/--
theorem `MDifferentiableAt.smul` / 定理 `MDifferentiableAt.smul`

English:
theorem MDifferentiableAt.smul
  statement: (hf : MDiffAt f x)
  proof: ((contMDiff_smul.of_le le_top).mdifferentiable one_ne_zero _).comp x (hf.prodMk hg)

@[to_fun]

中文:
定理 MDifferentiableAt.smul
  结论: (hf : MDiffAt f x)
  证明: ((contMDiff_smul.of_le le_top).mdifferentiable one_ne_zero _).comp x (hf.prodMk hg)

@[to_fun]

Depends on / 依赖: contMDiff_smul, contMDiff_smul.of_le, hf.prodMk, le_top, mdifferentiable, of_le, one_ne_zero, prodMk
-/
theorem MDifferentiableAt.smul (hf : MDiffAt f x)
    (hg : MDiffAt g x) : MDiffAt (f • g) x :=
  ((contMDiff_smul.of_le le_top).mdifferentiable one_ne_zero _).comp x (hf.prodMk hg)

@[to_fun]
/--
theorem `MDifferentiableOn.smul` / 定理 `MDifferentiableOn.smul`

English:
theorem MDifferentiableOn.smul
  statement: (hf : MDiff[s] f)
  proof: fun x hx => (hf x hx).smul (hg x hx)

@[to_fun]

中文:
定理 MDifferentiableOn.smul
  结论: (hf : MDiff[s] f)
  证明: fun x hx => (hf x hx).smul (hg x hx)

@[to_fun]
-/
theorem MDifferentiableOn.smul (hf : MDiff[s] f)
    (hg : MDiff[s] g) : MDiff[s] (f • g) :=
  fun x hx => (hf x hx).smul (hg x hx)

@[to_fun]
/--
theorem `MDifferentiable.smul` / 定理 `MDifferentiable.smul`

English:
theorem MDifferentiable.smul
  given: (hf : MDiff f) (hg : MDiff g)
  statement: MDiff (f • g)
  proof: fun x => (hf x).smul (hg x)

中文:
定理 MDifferentiable.smul
  条件: (hf : MDiff f) (hg : MDiff g)
  结论: MDiff (f • g)
  证明: fun x => (hf x).smul (hg x)
-/
theorem MDifferentiable.smul (hf : MDiff f) (hg : MDiff g) : MDiff (f • g) :=
  fun x => (hf x).smul (hg x)

-- TODO: deprecate in favour of `mvfderiv_smul`, then delete this lemma
/--
lemma `mfderiv_smul` / 引理 `mfderiv_smul`

English:
lemma mfderiv_smul
  given: (hf : MDiffAt f x) (hg : MDiffAt g x)
  proof: (hf.hasMFDerivAt.smul hg.hasMFDerivAt).mfderiv

中文:
引理 mfderiv_smul
  条件: (hf : MDiffAt f x) (hg : MDiffAt g x)
  证明: (hf.hasMFDerivAt.smul hg.hasMFDerivAt).mfderiv
-/
private lemma mfderiv_smul (hf : MDiffAt f x) (hg : MDiffAt g x) :
    mfderiv% (f • g) x
    = f x • (fromTangentSpace _).symm.toContinuousLinearMap ∘L
      ((fromTangentSpace (g x)).toContinuousLinearMap ∘L mfderiv% g x)
    + toSpanSingleton 𝕜 ((fromTangentSpace _).symm (g x)) ∘L
      ((fromTangentSpace (f x)).toContinuousLinearMap ∘L mfderiv% f x) :=
  (hf.hasMFDerivAt.smul hg.hasMFDerivAt).mfderiv

-- TODO: investigate inlining the proof: this lemma statement abuses defeq
/--
lemma `fromTangentSpace_mfderiv_smul` / 引理 `fromTangentSpace_mfderiv_smul`

English:
lemma fromTangentSpace_mfderiv_smul
  given: (hf : MDiffAt f x) (hg : MDiffAt g x)
  proof: by
  rw [mfderiv_smul hf hg]
  rfl

中文:
引理 fromTangentSpace_mfderiv_smul
  条件: (hf : MDiffAt f x) (hg : MDiffAt g x)
  证明: by
  rw [mfderiv_smul hf hg]
  rfl
-/
private lemma fromTangentSpace_mfderiv_smul (hf : MDiffAt f x) (hg : MDiffAt g x) :
    (fromTangentSpace ((f • g) x)).toContinuousLinearMap ∘L mfderiv% (f • g) x
    = f x • (fromTangentSpace _).toContinuousLinearMap ∘L mfderiv% g x
    + toSpanSingleton 𝕜 (g x) ∘L (fromTangentSpace _).toContinuousLinearMap ∘L mfderiv% f x := by
  rw [mfderiv_smul hf hg]
  rfl

-- TODO: investigate inlining the proof: this lemma statement abuses defeq
/--
lemma `fromTangentSpace_mfderiv_smul'` / 引理 `fromTangentSpace_mfderiv_smul'`

English:
lemma fromTangentSpace_mfderiv_smul'
  given: (hf : MDiffAt f x) (hg : MDiffAt g x)
  proof: fromTangentSpace_mfderiv_smul hf hg

中文:
引理 fromTangentSpace_mfderiv_smul'
  条件: (hf : MDiffAt f x) (hg : MDiffAt g x)
  证明: fromTangentSpace_mfderiv_smul hf hg
-/
private lemma fromTangentSpace_mfderiv_smul' (hf : MDiffAt f x) (hg : MDiffAt g x) :
    (fromTangentSpace (f x • g x)).toContinuousLinearMap ∘L mfderiv% (f • g) x
    = f x • (fromTangentSpace _).toContinuousLinearMap ∘L mfderiv% g x
    + toSpanSingleton 𝕜 (g x) ∘L (fromTangentSpace _).toContinuousLinearMap ∘L mfderiv% f x :=
  fromTangentSpace_mfderiv_smul hf hg

-- TODO: investigate inlining the proof: this lemma statement abuses defeq
/--
lemma `fromTangentSpace_mfderiv_smul_apply` / 引理 `fromTangentSpace_mfderiv_smul_apply`

English:
lemma fromTangentSpace_mfderiv_smul_apply
  statement: (hf : MDiffAt f x) (hg : MDiffAt g x)
  proof: by
  simpa using congr($(fromTangentSpace_mfderiv_smul hf hg) v)

中文:
引理 fromTangentSpace_mfderiv_smul_apply
  结论: (hf : MDiffAt f x) (hg : MDiffAt g x)
  证明: by
  simpa using congr($(fromTangentSpace_mfderiv_smul hf hg) v)
-/
private lemma fromTangentSpace_mfderiv_smul_apply (hf : MDiffAt f x) (hg : MDiffAt g x)
    (v : TangentSpace% x) :
    fromTangentSpace _ (mfderiv% (f • g) x v)
    = f x • fromTangentSpace _ (mfderiv% g x v) + fromTangentSpace _ (mfderiv% f x v) • g x := by
  simpa using congr($(fromTangentSpace_mfderiv_smul hf hg) v)

-- TODO: investigate inlining the proof: this lemma statement abuses defeq
/--
lemma `fromTangentSpace_mfderiv_smul_apply'` / 引理 `fromTangentSpace_mfderiv_smul_apply'`

English:
lemma fromTangentSpace_mfderiv_smul_apply'
  statement: (hf : MDiffAt f x) (hg : MDiffAt g x)
  proof: fromTangentSpace_mfderiv_smul_apply hf hg v

中文:
引理 fromTangentSpace_mfderiv_smul_apply'
  结论: (hf : MDiffAt f x) (hg : MDiffAt g x)
  证明: fromTangentSpace_mfderiv_smul_apply hf hg v
-/
private lemma fromTangentSpace_mfderiv_smul_apply' (hf : MDiffAt f x) (hg : MDiffAt g x)
    (v : TangentSpace% x) :
    fromTangentSpace (f x • g x) (mfderiv% (f • g) x v)
    = f x • fromTangentSpace _ (mfderiv% g x v) + fromTangentSpace _ (mfderiv% f x v) • g x :=
  fromTangentSpace_mfderiv_smul_apply hf hg v

end smul

/-! ### Exterior derivative of a vector-valued function -/

variable (I) in
/-- `mvfderivWithin I J f s x` is the `mfderiv` of a vector-valued function `f` on `M` at `x`
within the set `s`, but taking values in the target normed space directly.
The difference to `mfderivWithin` is explained in the module-docstring for
`Mathlib/Geometry/Manifold/MFDeriv/NormedSpace.lean`.

Future: this could be generalised to functions into additive torsors over abelian Lie groups.
-/
@[expose]
/--
Definition of `mvfderivWithin` / `mvfderivWithin` 的定义

English:
definition mvfderivWithin
  signature: (g : M -> F) (s : Set M)
  body: fun x => (NormedSpace.fromTangentSpace <| g x).toContinuousLinearMap ∘L (mfderiv[s] g x)

中文:
定义 mvfderivWithin
  签名: (g : M -> F) (s : 集合 M)
  定义体: fun x => (NormedSpace.fromTangentSpace <| g x).toContinuousLinearMap ∘L (mfderiv[s] g x)

Depends on / 依赖: NormedSpace, NormedSpace.fromTangentSpace, fromTangentSpace, mfderiv, toContinuousLinearMap
-/
noncomputable def mvfderivWithin (g : M -> F) (s : Set M) :
    Π x : M, TangentSpace I x ->L[𝕜] F :=
  fun x => (NormedSpace.fromTangentSpace <| g x).toContinuousLinearMap ∘L (mfderiv[s] g x)

variable (I) in
/-- `mvfderiv I J f x` is the `mfderiv` of a vector-valued function `f` on `M` at `x`,
but taking values in the target normed space directly.
The difference to `mfderiv` is explained in the module-docstring for
`Mathlib/Geometry/Manifold/MFDeriv/NormedSpace.lean`.

Future: this could be generalised to functions into additive torsors over abelian Lie groups.
-/
@[expose]
/--
Definition of `mvfderiv` / `mvfderiv` 的定义

English:
definition mvfderiv
  signature: (g : M -> F)
  body: fun x => (NormedSpace.fromTangentSpace <| g x).toContinuousLinearMap ∘L (mfderiv% g x)
@[deprecated (since := "2026-05-17")] alias extDerivFun := mvfderiv

中文:
定义 mvfderiv
  签名: (g : M -> F)
  定义体: fun x => (NormedSpace.fromTangentSpace <| g x).toContinuousLinearMap ∘L (mfderiv% g x)
@[deprecated (since := "2026-05-17")] alias extDerivFun := mvfderiv

Depends on / 依赖: NormedSpace, NormedSpace.fromTangentSpace, deprecated, extDerivFun, fromTangentSpace, mfderiv, mvfderiv, toContinuousLinearMap
-/
noncomputable def mvfderiv (g : M -> F) :
    Π x : M, TangentSpace% x ->L[𝕜] F :=
  fun x => (NormedSpace.fromTangentSpace <| g x).toContinuousLinearMap ∘L (mfderiv% g x)
@[deprecated (since := "2026-05-17")] alias extDerivFun := mvfderiv

namespace Manifold
open scoped Bundle Manifold ContDiff

open Lean Meta Elab Tactic

/-- `d[s] f x` (scoped to the `Manifold` namespace) elaborates to `mvfderivWithin I J f s x`,
trying to determine `I` and `J` from the local context. -/
scoped elab:max "d[" s:term "]" ppSpace t:term:arg : term => do
  let es ← Term.elabTerm s none
let e ← ensureIsFunction ← Term.elabTerm t none
  let (srcI, _tgtI) ← findModels e none
  mkAppM ``mvfderivWithin #[srcI, e, es]

/-- `d% f x` (scoped to the `Manifold` namespace) elaborates to `mvfderiv I J f x`,
trying to determine `I` and `J` from the local context. -/
scoped elab:max "d%" ppSpace t:term:arg : term => do
let e ← ensureIsFunction ← Term.elabTerm t none
  let (srcI, _tgtI) ← findModels e none
  mkAppM ``mvfderiv #[srcI, e]

open Bundle PrettyPrinter Delaborator SubExpr

/-- Delaborator for `mvfderivWithin`. -/
-- There is no need to special-case any arguments which could use the `T%` elaborator:
-- the argument to `mvfderivWithin` is a vector-valued function, which a map to a total space
-- can never be.
@[app_delab mvfderivWithin] meta def delabMVFDerivWithin : Delab := do
  whenPPOption getPPNotation do
  withOverApp 16 do
  let ss ← withAppArg delab
let fs ← withNaryArg 14 delab
  `(d[$ss] $fs) >>= annotateGoToSyntaxDef

/-- Delaborator for `mvfderiv`. -/
-- There is no need to special-case any arguments which could use the `T%` elaborator:
-- the argument to `mvfderiv` is a vector-valued function, which a map to a total space
-- can never be.
@[app_delab mvfderiv] meta def delabMVFDeriv : Delab := do
  whenPPOption getPPNotation do
  withOverApp 15 do
  let fs ← withAppArg delab
  `(d% $fs) >>= annotateGoToSyntaxDef

end Manifold

/--
lemma `mvfderivWithin_univ` / 引理 `mvfderivWithin_univ`

English:
lemma mvfderivWithin_univ
  given: {f : M -> F}
  statement: d[(univ : Set M)] f = d% f
  proof: by
  ext X
  simp [mvfderiv, mvfderivWithin]

中文:
引理 mvfderivWithin_univ
  条件: {f : M -> F}
  结论: d[(univ : 集合 M)] f = d% f
  证明: by
  ext X
  simp [mvfderiv, mvfderivWithin]
-/
@[simp, mfld_simps] lemma mvfderivWithin_univ {f : M -> F} : d[(univ : Set M)] f = d% f := by
  ext X
  simp [mvfderiv, mvfderivWithin]

/--
lemma `mvfderivWithin_const` / 引理 `mvfderivWithin_const`

English:
lemma mvfderivWithin_const
  given: (c : F) {x : M}
  statement: d[s] (fun _ : M => c) x = 0
  proof: by
  simp [mvfderivWithin, mfderivWithin_const]

@[simp, to_fun mvfderivWithin_fun_add]

中文:
引理 mvfderivWithin_const
  条件: (c : F) {x : M}
  结论: d[s] (fun _ : M => c) x = 0
  证明: by
  simp [mvfderivWithin, mfderivWithin_const]

@[simp, to_fun mvfderivWithin_fun_add]

Depends on / 依赖: mfderivWithin_const, mvfderivWithin
-/
lemma mvfderivWithin_const (c : F) {x : M} : d[s] (fun _ : M => c) x = 0 := by
  simp [mvfderivWithin, mfderivWithin_const]

@[simp, to_fun mvfderivWithin_fun_add]
/--
lemma `mvfderivWithin_add` / 引理 `mvfderivWithin_add`

English:
lemma mvfderivWithin_add
  statement: {g g' : M -> F} {x : M}
  proof: by
  simp [mvfderivWithin, mfderivWithin_add hg hg' hs]
  rfl

@[simp, to_fun mvfderivWithin_fun_sub]

中文:
引理 mvfderivWithin_add
  结论: {g g' : M -> F} {x : M}
  证明: by
  simp [mvfderivWithin, mfderivWithin_add hg hg' hs]
  rfl

@[simp, to_fun mvfderivWithin_fun_sub]

Depends on / 依赖: mfderivWithin_add, mvfderivWithin
-/
lemma mvfderivWithin_add {g g' : M -> F} {x : M}
    (hg : MDiffAt[s] g x) (hg' : MDiffAt[s] g' x) (hs : UniqueMDiffAt[s] x) :
    d[s](g + g') x = d[s]g x + d[s]g' x := by
  simp [mvfderivWithin, mfderivWithin_add hg hg' hs]
  rfl

@[simp, to_fun mvfderivWithin_fun_sub]
/--
lemma `mvfderivWithin_sub` / 引理 `mvfderivWithin_sub`

English:
lemma mvfderivWithin_sub
  statement: {g g' : M -> F} {x : M}
  proof: by
  simp [mvfderivWithin, mfderivWithin_sub hg hg' hs]
  rfl

@[simp, to_fun mvfderivWithin_fun_neg]

中文:
引理 mvfderivWithin_sub
  结论: {g g' : M -> F} {x : M}
  证明: by
  simp [mvfderivWithin, mfderivWithin_sub hg hg' hs]
  rfl

@[simp, to_fun mvfderivWithin_fun_neg]

Depends on / 依赖: mfderivWithin_sub, mvfderivWithin
-/
lemma mvfderivWithin_sub {g g' : M -> F} {x : M}
    (hg : MDiffAt[s] g x) (hg' : MDiffAt[s] g' x) (hs : UniqueMDiffAt[s] x) :
    d[s](g - g') x = d[s]g x - d[s]g' x := by
  simp [mvfderivWithin, mfderivWithin_sub hg hg' hs]
  rfl

@[simp, to_fun mvfderivWithin_fun_neg]
/--
lemma `mvfderivWithin_neg` / 引理 `mvfderivWithin_neg`

English:
lemma mvfderivWithin_neg
  given: {g : M -> F} {x : M} (hs : UniqueMDiffAt[s] x)
  proof: by
  simp [mvfderivWithin, mfderivWithin_neg hs]
  rfl

@[simp, to_fun mvfderivWithin_fun_smul]

中文:
引理 mvfderivWithin_neg
  条件: {g : M -> F} {x : M} (hs : UniqueMDiffAt[s] x)
  证明: by
  simp [mvfderivWithin, mfderivWithin_neg hs]
  rfl

@[simp, to_fun mvfderivWithin_fun_smul]

Depends on / 依赖: mfderivWithin_neg, mvfderivWithin
-/
lemma mvfderivWithin_neg {g : M -> F} {x : M} (hs : UniqueMDiffAt[s] x) :
    d[s](-g) x = -d[s]g x := by
  simp [mvfderivWithin, mfderivWithin_neg hs]
  rfl

@[simp, to_fun mvfderivWithin_fun_smul]
/--
lemma `mvfderivWithin_smul` / 引理 `mvfderivWithin_smul`

English:
lemma mvfderivWithin_smul
  statement: {a : M -> 𝕜} (ha : MDiffAt[s] a x) {g : M -> F} (hg : MDiffAt[s] g x)
  proof: by
  refine HasMFDerivWithinAt.mfderivWithin ⟨ha.1.smul hg.1, ?_⟩ hs
  convert! ha.hasMFDerivWithinAt.2.smul hg.hasMFDerivWithinAt.2
  simp
  rfl

@[simp, to_fun mvfderivWithin_fun_mul]

中文:
引理 mvfderivWithin_smul
  结论: {a : M -> 𝕜} (ha : MDiffAt[s] a x) {g : M -> F} (hg : MDiffAt[s] g x)
  证明: by
  refine HasMFDerivWithinAt.mfderivWithin ⟨ha.1.smul hg.1, ?_⟩ hs
  convert! ha.hasMFDerivWithinAt.2.smul hg.hasMFDerivWithinAt.2
  simp
  rfl

@[simp, to_fun mvfderivWithin_fun_mul]

Depends on / 依赖: HasMFDerivWithinAt, HasMFDerivWithinAt.mfderivWithin, convert, ha.hasMFDerivWithinAt, hasMFDerivWithinAt, hg.hasMFDerivWithinAt, mfderivWithin
-/
lemma mvfderivWithin_smul {a : M -> 𝕜} (ha : MDiffAt[s] a x) {g : M -> F} (hg : MDiffAt[s] g x)
    (hs : UniqueMDiffAt[s] x) :
    d[s](a • g) x =
      a x • d[s] g x + (d[s] a x).smulRight (g x) := by
  refine HasMFDerivWithinAt.mfderivWithin ⟨ha.1.smul hg.1, ?_⟩ hs
  convert! ha.hasMFDerivWithinAt.2.smul hg.hasMFDerivWithinAt.2
  simp
  rfl

@[simp, to_fun mvfderivWithin_fun_mul]
/--
lemma `mvfderivWithin_mul` / 引理 `mvfderivWithin_mul`

English:
lemma mvfderivWithin_mul
  statement: {f g : M -> 𝕜} {x : M} (hf : MDiffAt[s] f x) (hg : MDiffAt[s] g x)
  proof: by
  convert! mvfderivWithin_smul hf hg hs
  ext v
  simp [mul_comm]

@[simp]

中文:
引理 mvfderivWithin_mul
  结论: {f g : M -> 𝕜} {x : M} (hf : MDiffAt[s] f x) (hg : MDiffAt[s] g x)
  证明: by
  convert! mvfderivWithin_smul hf hg hs
  ext v
  simp [mul_comm]

@[simp]

Depends on / 依赖: convert, mul_comm, mvfderivWithin_smul
-/
lemma mvfderivWithin_mul {f g : M -> 𝕜} {x : M} (hf : MDiffAt[s] f x) (hg : MDiffAt[s] g x)
    (hs : UniqueMDiffAt[s] x) :
    d[s](f * g) x = f x • d[s]g x + (g x) • (d[s]f x) := by
  convert! mvfderivWithin_smul hf hg hs
  ext v
  simp [mul_comm]

@[simp]
/--
lemma `mvfderivWithin_zero` / 引理 `mvfderivWithin_zero`

English:
lemma mvfderivWithin_zero
  given: {s : Set M} (hs : UniqueMDiffAt[s] x)
  proof: by
  have : d[s] (0 : M -> F) x + d[s] (0 : M -> F) x = d[s] (0 : M -> F) x := by
    rw [← mvfderivWithin_add (by exact mdifferentiableWithinAt_const)
      (by exact mdifferentiableWithinAt_const) hs]
    simp
  simpa using this

中文:
引理 mvfderivWithin_zero
  条件: {s : 集合 M} (hs : UniqueMDiffAt[s] x)
  证明: by
  have : d[s] (0 : M -> F) x + d[s] (0 : M -> F) x = d[s] (0 : M -> F) x := by
    rw [← mvfderivWithin_add (by exact mdifferentiableWithinAt_const)
      (by exact mdifferentiableWithinAt_const) hs]
    simp
  simpa using this

Depends on / 依赖: mdifferentiableWithinAt_const, mvfderivWithin_add
-/
lemma mvfderivWithin_zero {s : Set M} (hs : UniqueMDiffAt[s] x) :
    d[s] (0 : M -> F) x = 0 := by
  have : d[s] (0 : M -> F) x + d[s] (0 : M -> F) x = d[s] (0 : M -> F) x := by
    rw [← mvfderivWithin_add (by exact mdifferentiableWithinAt_const)
      (by exact mdifferentiableWithinAt_const) hs]
    simp
  simpa using this

/--
lemma `mvfderiv_const` / 引理 `mvfderiv_const`

English:
lemma mvfderiv_const
  given: (c : F) {x : M}
  statement: d% (fun _ : M => c) x = 0
  proof: by
  simp [mvfderiv, mfderiv_const]

@[simp, to_fun mvfderiv_fun_add]

中文:
引理 mvfderiv_const
  条件: (c : F) {x : M}
  结论: d% (fun _ : M => c) x = 0
  证明: by
  simp [mvfderiv, mfderiv_const]

@[simp, to_fun mvfderiv_fun_add]

Depends on / 依赖: mfderiv_const, mvfderiv
-/
lemma mvfderiv_const (c : F) {x : M} : d% (fun _ : M => c) x = 0 := by
  simp [mvfderiv, mfderiv_const]

@[simp, to_fun mvfderiv_fun_add]
/--
lemma `mvfderiv_add` / 引理 `mvfderiv_add`

English:
lemma mvfderiv_add
  given: {g g' : M -> F} {x : M} (hg : MDiffAt g x) (hg' : MDiffAt g' x)
  proof: by
  simp [mvfderiv, mfderiv_add hg hg']
  rfl
@[deprecated (since := "2026-05-17")] alias extDerivFun_add := mvfderiv_add

@[simp, to_fun mvfderiv_fun_sub]

中文:
引理 mvfderiv_add
  条件: {g g' : M -> F} {x : M} (hg : MDiffAt g x) (hg' : MDiffAt g' x)
  证明: by
  simp [mvfderiv, mfderiv_add hg hg']
  rfl
@[deprecated (since := "2026-05-17")] alias extDerivFun_add := mvfderiv_add

@[simp, to_fun mvfderiv_fun_sub]

Depends on / 依赖: deprecated, extDerivFun_add, mfderiv_add, mvfderiv, mvfderiv_add
-/
lemma mvfderiv_add {g g' : M -> F} {x : M} (hg : MDiffAt g x) (hg' : MDiffAt g' x) :
    d% (g + g') x = d% g x + d% g' x := by
  simp [mvfderiv, mfderiv_add hg hg']
  rfl
@[deprecated (since := "2026-05-17")] alias extDerivFun_add := mvfderiv_add

@[simp, to_fun mvfderiv_fun_sub]
/--
lemma `mvfderiv_sub` / 引理 `mvfderiv_sub`

English:
lemma mvfderiv_sub
  given: {g g' : M -> F} {x : M} (hg : MDiffAt g x) (hg' : MDiffAt g' x)
  proof: by
  simp [mvfderiv, mfderiv_sub hg hg']
  rfl

@[simp, to_fun mvfderiv_fun_neg]

中文:
引理 mvfderiv_sub
  条件: {g g' : M -> F} {x : M} (hg : MDiffAt g x) (hg' : MDiffAt g' x)
  证明: by
  simp [mvfderiv, mfderiv_sub hg hg']
  rfl

@[simp, to_fun mvfderiv_fun_neg]

Depends on / 依赖: mfderiv_sub, mvfderiv
-/
lemma mvfderiv_sub {g g' : M -> F} {x : M} (hg : MDiffAt g x) (hg' : MDiffAt g' x) :
    d% (g - g') x = d% g x - d% g' x := by
  simp [mvfderiv, mfderiv_sub hg hg']
  rfl

@[simp, to_fun mvfderiv_fun_neg]
/--
lemma `mvfderiv_neg` / 引理 `mvfderiv_neg`

English:
lemma mvfderiv_neg
  given: {g : M -> F} {x : M}
  proof: by
  simp [mvfderiv, mfderiv_neg]
  rfl

@[simp, to_fun mvfderiv_fun_smul]

中文:
引理 mvfderiv_neg
  条件: {g : M -> F} {x : M}
  证明: by
  simp [mvfderiv, mfderiv_neg]
  rfl

@[simp, to_fun mvfderiv_fun_smul]

Depends on / 依赖: mfderiv_neg, mvfderiv
-/
lemma mvfderiv_neg {g : M -> F} {x : M} :
    d% (-g) x = -d% g x := by
  simp [mvfderiv, mfderiv_neg]
  rfl

@[simp, to_fun mvfderiv_fun_smul]
/--
lemma `mvfderiv_smul` / 引理 `mvfderiv_smul`

English:
lemma mvfderiv_smul
  given: {x : M} {a : M -> 𝕜} (ha : MDiffAt a x) {g : M -> F} (hg : MDiffAt g x)
  proof: by
  ext v
  simp [mvfderiv, -Pi.smul_apply', fromTangentSpace_mfderiv_smul_apply ha hg]

@[simp, to_fun mvfderiv_fun_mul]

中文:
引理 mvfderiv_smul
  条件: {x : M} {a : M -> 𝕜} (ha : MDiffAt a x) {g : M -> F} (hg : MDiffAt g x)
  证明: by
  ext v
  simp [mvfderiv, -Pi.smul_apply', fromTangentSpace_mfderiv_smul_apply ha hg]

@[simp, to_fun mvfderiv_fun_mul]

Depends on / 依赖: Pi.smul_apply, fromTangentSpace_mfderiv_smul_apply, mvfderiv, smul_apply
-/
lemma mvfderiv_smul {x : M} {a : M -> 𝕜} (ha : MDiffAt a x) {g : M -> F} (hg : MDiffAt g x) :
    d% (a • g) x = a x • d% g x + (d% a x).smulRight (g x) := by
  ext v
  simp [mvfderiv, -Pi.smul_apply', fromTangentSpace_mfderiv_smul_apply ha hg]

@[simp, to_fun mvfderiv_fun_mul]
/--
lemma `mvfderiv_mul` / 引理 `mvfderiv_mul`

English:
lemma mvfderiv_mul
  given: {f g : M -> 𝕜} {x : M} (hf : MDiffAt f x) (hg : MDiffAt g x)
  proof: by
  ext v
  simp only [mvfderiv, ← smul_eq_mul, mfderiv_smul hf hg]
  simp [mul_comm _ (g x)]

@[simp]

中文:
引理 mvfderiv_mul
  条件: {f g : M -> 𝕜} {x : M} (hf : MDiffAt f x) (hg : MDiffAt g x)
  证明: by
  ext v
  simp only [mvfderiv, ← smul_eq_mul, mfderiv_smul hf hg]
  simp [mul_comm _ (g x)]

@[simp]

Depends on / 依赖: mfderiv_smul, mul_comm, mvfderiv, smul_eq_mul
-/
lemma mvfderiv_mul {f g : M -> 𝕜} {x : M} (hf : MDiffAt f x) (hg : MDiffAt g x) :
    d% (f * g) x = f x • d% g x + (g x) • (d% f x) := by
  ext v
  simp only [mvfderiv, ← smul_eq_mul, mfderiv_smul hf hg]
  simp [mul_comm _ (g x)]

@[simp]
/--
lemma `mvfderiv_zero` / 引理 `mvfderiv_zero`

English:
lemma mvfderiv_zero
  given: {x : M}
  statement: d% (0 : M -> F) x = 0
  proof: by
  have : d% (0 : M -> F) x + d% (0 : M -> F) x = d% (0 : M -> F) x := by
    rw [← mvfderiv_add (by exact mdifferentiable_const ..) (by exact mdifferentiable_const ..)]
    simp
  simpa using this
@[deprecated (since := "2026-05-17")] alias extDerivFun_zero := mvfderiv_zero

中文:
引理 mvfderiv_zero
  条件: {x : M}
  结论: d% (0 : M -> F) x = 0
  证明: by
  have : d% (0 : M -> F) x + d% (0 : M -> F) x = d% (0 : M -> F) x := by
    rw [← mvfderiv_add (by exact mdifferentiable_const ..) (by exact mdifferentiable_const ..)]
    simp
  simpa using this
@[deprecated (since := "2026-05-17")] alias extDerivFun_zero := mvfderiv_zero

Depends on / 依赖: deprecated, extDerivFun_zero, mdifferentiable_const, mvfderiv_add, mvfderiv_zero
-/
lemma mvfderiv_zero {x : M} : d% (0 : M -> F) x = 0 := by
  have : d% (0 : M -> F) x + d% (0 : M -> F) x = d% (0 : M -> F) x := by
    rw [← mvfderiv_add (by exact mdifferentiable_const ..) (by exact mdifferentiable_const ..)]
    simp
  simpa using this
@[deprecated (since := "2026-05-17")] alias extDerivFun_zero := mvfderiv_zero

-- TODO: the next two lemmas are more type correct than their `mvfderiv` cousins, but not entirely:
-- the right hand side should be of the form `fderiv ∘SL TangentSpaceCastModel`.
/--
theorem `MDifferentiableWithinAt.mvfderivWithin` / 定理 `MDifferentiableWithinAt.mvfderivWithin`

English:
theorem MDifferentiableWithinAt.mvfderivWithin
  given: {f : M -> E'} (h : MDiffAt[s] f x)
  proof: by
  convert! h.mfderivWithin

中文:
定理 MDifferentiableWithinAt.mvfderivWithin
  条件: {f : M -> E'} (h : MDiffAt[s] f x)
  证明: by
  convert! h.mfderivWithin
-/
protected theorem MDifferentiableWithinAt.mvfderivWithin {f : M -> E'} (h : MDiffAt[s] f x) :
    d[s] f x = fderivWithin 𝕜 (writtenInExtChartAt I 𝓘(𝕜, E') x f)
      ((extChartAt I x).symm ⁻¹' s inter range I) (extChartAt I x x) := by
  convert! h.mfderivWithin

/--
theorem `MDifferentiableAt.mvfderiv` / 定理 `MDifferentiableAt.mvfderiv`

English:
theorem MDifferentiableAt.mvfderiv
  given: {f : M -> E'} (h : MDiffAt f x)
  proof: by
  convert! h.mfderiv

中文:
定理 MDifferentiableAt.mvfderiv
  条件: {f : M -> E'} (h : MDiffAt f x)
  证明: by
  convert! h.mfderiv
-/
protected theorem MDifferentiableAt.mvfderiv {f : M -> E'} (h : MDiffAt f x) :
    d% f x = fderivWithin 𝕜 (writtenInExtChartAt I 𝓘(𝕜, E') x f) (range I) (extChartAt I x x) := by
  convert! h.mfderiv

/-! ## Composition lemmas for `mvfderiv(Within)` -/
section

variable {f : M' -> M} {g : M -> 𝕜} {x : M'} {y : M} {u : Set M} {s : Set M'}

/--
theorem `mvfderivWithin_comp` / 定理 `mvfderivWithin_comp`

English:
theorem mvfderivWithin_comp
  statement: (x : M') (hg : MDiffAt[u] g (f x)) (hf : MDiffAt[s] f x)
  proof: mfderivWithin_comp x hg hf h hxs

中文:
定理 mvfderivWithin_comp
  结论: (x : M') (hg : MDiffAt[u] g (f x)) (hf : MDiffAt[s] f x)
  证明: mfderivWithin_comp x hg hf h hxs

Depends on / 依赖: mfderivWithin_comp
-/
theorem mvfderivWithin_comp (x : M') (hg : MDiffAt[u] g (f x)) (hf : MDiffAt[s] f x)
    (h : s subseteq f ⁻¹' u) (hxs : UniqueMDiffAt[s] x) :
    d[s] (g ∘ f) x = (d[u] g (f x)).comp (mfderiv[s] f x) :=
  mfderivWithin_comp x hg hf h hxs

/--
theorem `mvfderivWithin_comp_of_eq` / 定理 `mvfderivWithin_comp_of_eq`

English:
theorem mvfderivWithin_comp_of_eq
  statement: (hg : MDiffAt[u] g y) (hf : MDiffAt[s] f x)
  proof: mfderivWithin_comp_of_eq hg hf h hxs hy

中文:
定理 mvfderivWithin_comp_of_eq
  结论: (hg : MDiffAt[u] g y) (hf : MDiffAt[s] f x)
  证明: mfderivWithin_comp_of_eq hg hf h hxs hy

Depends on / 依赖: mfderivWithin_comp_of_eq
-/
theorem mvfderivWithin_comp_of_eq (hg : MDiffAt[u] g y) (hf : MDiffAt[s] f x)
    (h : s subseteq f ⁻¹' u) (hxs : UniqueMDiffAt[s] x) (hy : f x = y) :
    d[s] (g ∘ f) x = (d[u] g y).comp (mfderiv[s] f x) :=
  mfderivWithin_comp_of_eq hg hf h hxs hy

/--
theorem `mvfderivWithin_comp_of_preimage_mem_nhdsWithin` / 定理 `mvfderivWithin_comp_of_preimage_mem_nhdsWithin`

English:
theorem mvfderivWithin_comp_of_preimage_mem_nhdsWithin
  statement: (x : M') (hg : MDiffAt[u] g (f x))
  proof: mfderivWithin_comp_of_preimage_mem_nhdsWithin x hg hf h hxs

中文:
定理 mvfderivWithin_comp_of_preimage_mem_nhdsWithin
  结论: (x : M') (hg : MDiffAt[u] g (f x))
  证明: mfderivWithin_comp_of_preimage_mem_nhdsWithin x hg hf h hxs

Depends on / 依赖: mfderivWithin_comp_of_preimage_mem_nhdsWithin
-/
theorem mvfderivWithin_comp_of_preimage_mem_nhdsWithin (x : M') (hg : MDiffAt[u] g (f x))
    (hf : MDiffAt[s] f x) (h : f ⁻¹' u in 𝓝[s] x) (hxs : UniqueMDiffAt[s] x) :
    d[s] (g ∘ f) x = (d[u] g (f x)).comp (mfderiv[s] f x) :=
  mfderivWithin_comp_of_preimage_mem_nhdsWithin x hg hf h hxs

/--
theorem `mvfderivWithin_comp_of_preimage_mem_nhdsWithin_of_eq` / 定理 `mvfderivWithin_comp_of_preimage_mem_nhdsWithin_of_eq`

English:
theorem mvfderivWithin_comp_of_preimage_mem_nhdsWithin_of_eq
  statement: (x : M') (hg : MDiffAt[u] g y)
  proof: mfderivWithin_comp_of_preimage_mem_nhdsWithin_of_eq x hg hf h hxs hy

中文:
定理 mvfderivWithin_comp_of_preimage_mem_nhdsWithin_of_eq
  结论: (x : M') (hg : MDiffAt[u] g y)
  证明: mfderivWithin_comp_of_preimage_mem_nhdsWithin_of_eq x hg hf h hxs hy

Depends on / 依赖: mfderivWithin_comp_of_preimage_mem_nhdsWithin_of_eq
-/
theorem mvfderivWithin_comp_of_preimage_mem_nhdsWithin_of_eq (x : M') (hg : MDiffAt[u] g y)
    (hf : MDiffAt[s] f x) (h : f ⁻¹' u in 𝓝[s] x) (hxs : UniqueMDiffAt[s] x) (hy : f x = y) :
    d[s] (g ∘ f) x = (d[u] g y).comp (mfderiv[s] f x) :=
  mfderivWithin_comp_of_preimage_mem_nhdsWithin_of_eq x hg hf h hxs hy

/--
theorem `mvfderiv_comp_mfderivWithin` / 定理 `mvfderiv_comp_mfderivWithin`

English:
theorem mvfderiv_comp_mfderivWithin
  proof: mfderiv_comp_mfderivWithin x hg hf hxs

中文:
定理 mvfderiv_comp_mfderivWithin
  证明: mfderiv_comp_mfderivWithin x hg hf hxs

Depends on / 依赖: mfderiv_comp_mfderivWithin
-/
theorem mvfderiv_comp_mfderivWithin
    (x : M') (hg : MDiffAt g (f x)) (hf : MDiffAt[s] f x) (hxs : UniqueMDiffAt[s] x) :
    d[s] (g ∘ f) x = (d% g (f x)).comp (mfderiv[s] f x) :=
  mfderiv_comp_mfderivWithin x hg hf hxs

/--
theorem `mvfderiv_comp_mfderivWithin_of_eq` / 定理 `mvfderiv_comp_mfderivWithin_of_eq`

English:
theorem mvfderiv_comp_mfderivWithin_of_eq
  proof: mfderiv_comp_mfderivWithin_of_eq hg hf hxs hy

中文:
定理 mvfderiv_comp_mfderivWithin_of_eq
  证明: mfderiv_comp_mfderivWithin_of_eq hg hf hxs hy

Depends on / 依赖: mfderiv_comp_mfderivWithin_of_eq
-/
theorem mvfderiv_comp_mfderivWithin_of_eq
    (hg : MDiffAt g y) (hf : MDiffAt[s] f x) (hxs : UniqueMDiffAt[s] x) (hy : f x = y) :
    d[s] (g ∘ f) x = (d% g y).comp (mfderiv[s] f x) :=
  mfderiv_comp_mfderivWithin_of_eq hg hf hxs hy

/--
theorem `mvfderiv_comp` / 定理 `mvfderiv_comp`

English:
theorem mvfderiv_comp
  given: (x : M') (hg : MDiffAt g (f x)) (hf : MDiffAt f x)
  proof: mfderiv_comp x hg hf

中文:
定理 mvfderiv_comp
  条件: (x : M') (hg : MDiffAt g (f x)) (hf : MDiffAt f x)
  证明: mfderiv_comp x hg hf

Depends on / 依赖: mfderiv_comp
-/
theorem mvfderiv_comp (x : M') (hg : MDiffAt g (f x)) (hf : MDiffAt f x) :
    d% (g ∘ f) x = (d% g (f x)).comp (mfderiv% f x) :=
  mfderiv_comp x hg hf

/--
theorem `mvfderiv_comp_of_eq` / 定理 `mvfderiv_comp_of_eq`

English:
theorem mvfderiv_comp_of_eq
  given: {y : M} (hg : MDiffAt g y) (hf : MDiffAt f x) (hy : f x = y)
  proof: mfderiv_comp_of_eq hg hf hy

中文:
定理 mvfderiv_comp_of_eq
  条件: {y : M} (hg : MDiffAt g y) (hf : MDiffAt f x) (hy : f x = y)
  证明: mfderiv_comp_of_eq hg hf hy

Depends on / 依赖: mfderiv_comp_of_eq
-/
theorem mvfderiv_comp_of_eq {y : M} (hg : MDiffAt g y) (hf : MDiffAt f x) (hy : f x = y) :
    d% (g ∘ f) x = (d% g (f x)).comp (mfderiv% f x) :=
  mfderiv_comp_of_eq hg hf hy

/--
theorem `mvfderiv_comp_apply` / 定理 `mvfderiv_comp_apply`

English:
theorem mvfderiv_comp_apply
  proof: mfderiv_comp_apply x hg hf v

中文:
定理 mvfderiv_comp_apply
  证明: mfderiv_comp_apply x hg hf v

Depends on / 依赖: mfderiv_comp_apply
-/
theorem mvfderiv_comp_apply
    (x : M') (hg : MDiffAt g (f x)) (hf : MDiffAt f x) (v : TangentSpace% x) :
    d% (g ∘ f) x v = (d% g (f x)) ((mfderiv% f x) v) :=
  mfderiv_comp_apply x hg hf v

/--
theorem `mvfderiv_comp_apply_of_eq` / 定理 `mvfderiv_comp_apply_of_eq`

English:
theorem mvfderiv_comp_apply_of_eq
  proof: mfderiv_comp_apply_of_eq x hg hf hy v

中文:
定理 mvfderiv_comp_apply_of_eq
  证明: mfderiv_comp_apply_of_eq x hg hf hy v

Depends on / 依赖: mfderiv_comp_apply_of_eq
-/
theorem mvfderiv_comp_apply_of_eq
    (x : M') (hg : MDiffAt g y) (hf : MDiffAt f x) (hy : f x = y) (v : TangentSpace% x) :
    d% (g ∘ f) x v = (d% g y) ((mfderiv% f x) v) :=
  mfderiv_comp_apply_of_eq x hg hf hy v

end
