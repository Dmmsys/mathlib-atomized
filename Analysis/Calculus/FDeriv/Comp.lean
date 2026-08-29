/-
Copyright (c) 2019 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Sébastien Gouëzel, Yury Kudryashov
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Basic

/-!
# The derivative of a composition (chain rule)

For detailed documentation of the Fréchet derivative,
see the module docstring of `Mathlib/Analysis/Calculus/FDeriv/Basic.lean`.

This file contains the usual formulas (and existence assertions) for the derivative of
composition of functions (the chain rule).
-/

public section


open Filter Asymptotics ContinuousLinearMap Set Metric Topology NNReal ENNReal

noncomputable section

section

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
variable {G' : Type*} [NormedAddCommGroup G'] [NormedSpace 𝕜 G']
variable {f g : E -> F} {f' g' : E ->L[𝕜] F} {x : E} {s : Set E} {L : Filter (E × E)}

section Composition

/-!
### Derivative of the composition of two functions

For composition lemmas, we put `x` explicit to help the elaborator, as otherwise Lean tends to
get confused since there are too many possibilities for composition. -/


variable (x)

/--
theorem `HasFDerivAtFilter.comp` / 定理 `HasFDerivAtFilter.comp`

English:
theorem HasFDerivAtFilter.comp
  statement: {g : F -> G} {g' : F ->L[𝕜] G} {L' : Filter (F × F)}
  proof: by
  -- This proof can be golfed a lot. However, it should be left this way for readability.
refine .of_isLittleOTVS calc
    (fun p => (g ∘ f) p.1 - (g ∘ f) p.2 - (g' ∘L f') (p.1 - p.2))
      = fun p => (g (f p.1) - g (f p.2) - g' (f p.1 - f p.2)) +
          g' (f p.1 - f p.2 - f' (p.1 - p.2)) := by
      ext; simp
    _ =o[𝕜; L] (fun p => p.1 - p.2) := .add ?Hg ?Hf
  case Hg => calc (fun p => g (f p.1) - g (f p.2) - g' (f p.1 - f p.2))
    _ =o[𝕜; L] (fun p => f p.1 - f p.2) :=
      hg.isLittleOTVS.comp_tendsto hL
    _ =O[𝕜; L] (fun p => p.1 - p.2) := hf.isBigOTVS_sub
  case Hf => calc (fun p => g' (f p.1 - f p.2 - f' (p.1 - p.2)))
    _ =O[𝕜; L] (fun p => f p.1 - f p.2 - f' (p.1 - p.2)) := g'.isBigOTVS_comp
    _ =o[𝕜; L] (fun p => p.1 - p.2) := hf.isLittleOTVS

中文:
定理 有FDerivAtFilter.comp
  结论: {g : F -> G} {g' : F ->L[𝕜] G} {L' : 滤子 (F × F)}
  证明: by
  -- This proof can be golfed a lot. However, it should be left this way for readability.
refine .of_isLittleOTVS calc
    (fun p => (g ∘ f) p.1 - (g ∘ f) p.2 - (g' ∘L f') (p.1 - p.2))
      = fun p => (g (f p.1) - g (f p.2) - g' (f p.1 - f p.2)) +
          g' (f p.1 - f p.2 - f' (p.1 - p.2)) := by
      ext; simp
    _ =o[𝕜; L] (fun p => p.1 - p.2) := .add ?Hg ?Hf
  case Hg => calc (fun p => g (f p.1) - g (f p.2) - g' (f p.1 - f p.2))
    _ =o[𝕜; L] (fun p => f p.1 - f p.2) :=
      hg.isLittleOTVS.comp_tendsto hL
    _ =O[𝕜; L] (fun p => p.1 - p.2) := hf.isBigOTVS_sub
  case Hf => calc (fun p => g' (f p.1 - f p.2 - f' (p.1 - p.2)))
    _ =O[𝕜; L] (fun p => f p.1 - f p.2 - f' (p.1 - p.2)) := g'.isBigOTVS_comp
    _ =o[𝕜; L] (fun p => p.1 - p.2) := hf.isLittleOTVS
-/
theorem HasFDerivAtFilter.comp {g : F -> G} {g' : F ->L[𝕜] G} {L' : Filter (F × F)}
    (hg : HasFDerivAtFilter g g' L') (hf : HasFDerivAtFilter f f' L)
    (hL : Tendsto (Prod.map f f) L L') :
    HasFDerivAtFilter (g ∘ f) (g' ∘L f') L := by
  -- This proof can be golfed a lot. However, it should be left this way for readability.
refine .of_isLittleOTVS calc
    (fun p => (g ∘ f) p.1 - (g ∘ f) p.2 - (g' ∘L f') (p.1 - p.2))
      = fun p => (g (f p.1) - g (f p.2) - g' (f p.1 - f p.2)) +
          g' (f p.1 - f p.2 - f' (p.1 - p.2)) := by
      ext; simp
    _ =o[𝕜; L] (fun p => p.1 - p.2) := .add ?Hg ?Hf
  case Hg => calc (fun p => g (f p.1) - g (f p.2) - g' (f p.1 - f p.2))
    _ =o[𝕜; L] (fun p => f p.1 - f p.2) :=
      hg.isLittleOTVS.comp_tendsto hL
    _ =O[𝕜; L] (fun p => p.1 - p.2) := hf.isBigOTVS_sub
  case Hf => calc (fun p => g' (f p.1 - f p.2 - f' (p.1 - p.2)))
    _ =O[𝕜; L] (fun p => f p.1 - f p.2 - f' (p.1 - p.2)) := g'.isBigOTVS_comp
    _ =o[𝕜; L] (fun p => p.1 - p.2) := hf.isLittleOTVS

/-- The chain rule for derivatives in the sense of strict differentiability. -/
@[fun_prop]
/--
theorem `HasStrictFDerivAt.comp` / 定理 `HasStrictFDerivAt.comp`

English:
theorem HasStrictFDerivAt.comp
  statement: {g : F -> G} {g' : F ->L[𝕜] G}
  proof: HasFDerivAtFilter.comp hg hf hf.continuousAt.tendsto.prodMap_nhds hf.continuousAt.tendsto

@[fun_prop]

中文:
定理 HasStrictFDerivAt.comp
  结论: {g : F -> G} {g' : F ->L[𝕜] G}
  证明: HasFDerivAtFilter.comp hg hf hf.continuousAt.tendsto.prodMap_nhds hf.continuousAt.tendsto

@[fun_prop]
-/
protected theorem HasStrictFDerivAt.comp {g : F -> G} {g' : F ->L[𝕜] G}
    (hg : HasStrictFDerivAt g g' (f x)) (hf : HasStrictFDerivAt f f' x) :
    HasStrictFDerivAt (fun x => g (f x)) (g'.comp f') x :=
HasFDerivAtFilter.comp hg hf hf.continuousAt.tendsto.prodMap_nhds hf.continuousAt.tendsto

@[fun_prop]
/--
theorem `HasFDerivWithinAt.comp` / 定理 `HasFDerivWithinAt.comp`

English:
theorem HasFDerivWithinAt.comp
  statement: {g : F -> G} {g' : F ->L[𝕜] G} {t : Set F}
  proof: HasFDerivAtFilter.comp hg hf .prodMap (hf.continuousWithinAt.tendsto_nhdsWithin hst)
    tendsto_pure_pure ..

@[fun_prop]

中文:
定理 HasFDerivWithinAt.comp
  结论: {g : F -> G} {g' : F ->L[𝕜] G} {t : 集合 F}
  证明: HasFDerivAtFilter.comp hg hf .prodMap (hf.continuousWithinAt.tendsto_nhdsWithin hst)
    tendsto_pure_pure ..

@[fun_prop]

Depends on / 依赖: HasFDerivAtFilter, HasFDerivAtFilter.comp, continuousWithinAt, hf.continuousWithinAt.tendsto_nhdsWithin, prodMap, tendsto_nhdsWithin, tendsto_pure_pure
-/
theorem HasFDerivWithinAt.comp {g : F -> G} {g' : F ->L[𝕜] G} {t : Set F}
    (hg : HasFDerivWithinAt g g' t (f x)) (hf : HasFDerivWithinAt f f' s x) (hst : MapsTo f s t) :
    HasFDerivWithinAt (g ∘ f) (g'.comp f') s x :=
HasFDerivAtFilter.comp hg hf .prodMap (hf.continuousWithinAt.tendsto_nhdsWithin hst)
    tendsto_pure_pure ..

@[fun_prop]
/--
theorem `HasFDerivAt.comp_hasFDerivWithinAt` / 定理 `HasFDerivAt.comp_hasFDerivWithinAt`

English:
theorem HasFDerivAt.comp_hasFDerivWithinAt
  statement: {g : F -> G} {g' : F ->L[𝕜] G}
  proof: hg.hasFDerivWithinAt.comp x hf (mapsTo_univ _ _)

@[fun_prop]

中文:
定理 在点处Fréchet可导.comp_hasFDerivWithinAt
  结论: {g : F -> G} {g' : F ->L[𝕜] G}
  证明: hg.hasFDerivWithinAt.comp x hf (mapsTo_univ _ _)

@[fun_prop]

Depends on / 依赖: hasFDerivWithinAt, hg.hasFDerivWithinAt.comp, mapsTo_univ
-/
theorem HasFDerivAt.comp_hasFDerivWithinAt {g : F -> G} {g' : F ->L[𝕜] G}
    (hg : HasFDerivAt g g' (f x)) (hf : HasFDerivWithinAt f f' s x) :
    HasFDerivWithinAt (g ∘ f) (g'.comp f') s x :=
  hg.hasFDerivWithinAt.comp x hf (mapsTo_univ _ _)

@[fun_prop]
/--
theorem `HasFDerivWithinAt.comp_of_tendsto` / 定理 `HasFDerivWithinAt.comp_of_tendsto`

English:
theorem HasFDerivWithinAt.comp_of_tendsto
  statement: {g : F -> G} {g' : F ->L[𝕜] G} {t : Set F}
  proof: HasFDerivAtFilter.comp hg hf hst.prodMap tendsto_pure_pure ..

中文:
定理 HasFDerivWithinAt.comp_of_tendsto
  结论: {g : F -> G} {g' : F ->L[𝕜] G} {t : 集合 F}
  证明: HasFDerivAtFilter.comp hg hf hst.prodMap tendsto_pure_pure ..

Depends on / 依赖: HasFDerivAtFilter, HasFDerivAtFilter.comp, hst.prodMap, prodMap, tendsto_pure_pure
-/
theorem HasFDerivWithinAt.comp_of_tendsto {g : F -> G} {g' : F ->L[𝕜] G} {t : Set F}
    (hg : HasFDerivWithinAt g g' t (f x)) (hf : HasFDerivWithinAt f f' s x)
    (hst : Tendsto f (𝓝[s] x) (𝓝[t] f x)) : HasFDerivWithinAt (g ∘ f) (g'.comp f') s x :=
HasFDerivAtFilter.comp hg hf hst.prodMap tendsto_pure_pure ..

/--
theorem `HasFDerivWithinAt.comp_hasFDerivAt` / 定理 `HasFDerivWithinAt.comp_hasFDerivAt`

English:
theorem HasFDerivWithinAt.comp_hasFDerivAt
  statement: {g : F -> G} {g' : F ->L[𝕜] G} {t : Set F}
  proof: HasFDerivAtFilter.comp hg hf .prodMap (tendsto_nhdsWithin_iff.mpr ⟨hf.continuousAt, ht⟩)
    tendsto_pure_pure ..

中文:
定理 HasFDerivWithinAt.comp_hasFDerivAt
  结论: {g : F -> G} {g' : F ->L[𝕜] G} {t : 集合 F}
  证明: HasFDerivAtFilter.comp hg hf .prodMap (tendsto_nhdsWithin_iff.mpr ⟨hf.continuousAt, ht⟩)
    tendsto_pure_pure ..

Depends on / 依赖: HasFDerivAtFilter, HasFDerivAtFilter.comp, continuousAt, hf.continuousAt, prodMap, tendsto_nhdsWithin_iff, tendsto_nhdsWithin_iff.mpr, tendsto_pure_pure
-/
theorem HasFDerivWithinAt.comp_hasFDerivAt {g : F -> G} {g' : F ->L[𝕜] G} {t : Set F}
    (hg : HasFDerivWithinAt g g' t (f x)) (hf : HasFDerivAt f f' x)
    (ht : forallᶠ x' in 𝓝 x, f x' in t) : HasFDerivAt (g ∘ f) (g' ∘L f') x :=
HasFDerivAtFilter.comp hg hf .prodMap (tendsto_nhdsWithin_iff.mpr ⟨hf.continuousAt, ht⟩)
    tendsto_pure_pure ..

/--
theorem `HasFDerivWithinAt.comp_hasFDerivAt_of_eq` / 定理 `HasFDerivWithinAt.comp_hasFDerivAt_of_eq`

English:
theorem HasFDerivWithinAt.comp_hasFDerivAt_of_eq
  statement: {g : F -> G} {g' : F ->L[𝕜] G} {t : Set F} {y : F}
  proof: by
  subst y; exact hg.comp_hasFDerivAt x hf ht

中文:
定理 HasFDerivWithinAt.comp_hasFDerivAt_of_eq
  结论: {g : F -> G} {g' : F ->L[𝕜] G} {t : 集合 F} {y : F}
  证明: by
  subst y; exact hg.comp_hasFDerivAt x hf ht

Depends on / 依赖: comp_hasFDerivAt, hg.comp_hasFDerivAt
-/
theorem HasFDerivWithinAt.comp_hasFDerivAt_of_eq {g : F -> G} {g' : F ->L[𝕜] G} {t : Set F} {y : F}
    (hg : HasFDerivWithinAt g g' t y) (hf : HasFDerivAt f f' x)
    (ht : forallᶠ x' in 𝓝 x, f x' in t) (hy : y = f x) : HasFDerivAt (g ∘ f) (g' ∘L f') x := by
  subst y; exact hg.comp_hasFDerivAt x hf ht

/-- The chain rule. -/
@[fun_prop]
/--
theorem `HasFDerivAt.comp` / 定理 `HasFDerivAt.comp`

English:
theorem HasFDerivAt.comp
  statement: {g : F -> G} {g' : F ->L[𝕜] G} (hg : HasFDerivAt g g' (f x))
  proof: HasFDerivAtFilter.comp hg hf hf.continuousAt.tendsto.prodMap tendsto_pure_pure ..

@[fun_prop]

中文:
定理 在点处Fréchet可导.comp
  结论: {g : F -> G} {g' : F ->L[𝕜] G} (hg : 在点处Fréchet可导 g g' (f x))
  证明: HasFDerivAtFilter.comp hg hf hf.continuousAt.tendsto.prodMap tendsto_pure_pure ..

@[fun_prop]

Depends on / 依赖: HasFDerivAtFilter, HasFDerivAtFilter.comp, continuousAt, hf.continuousAt.tendsto.prodMap, prodMap, tendsto, tendsto_pure_pure
-/
theorem HasFDerivAt.comp {g : F -> G} {g' : F ->L[𝕜] G} (hg : HasFDerivAt g g' (f x))
    (hf : HasFDerivAt f f' x) : HasFDerivAt (g ∘ f) (g'.comp f') x :=
HasFDerivAtFilter.comp hg hf hf.continuousAt.tendsto.prodMap tendsto_pure_pure ..

@[fun_prop]
/--
theorem `DifferentiableWithinAt.comp` / 定理 `DifferentiableWithinAt.comp`

English:
theorem DifferentiableWithinAt.comp
  statement: {g : F -> G} {t : Set F}
  proof: (hg.hasFDerivWithinAt.comp x hf.hasFDerivWithinAt h).differentiableWithinAt

@[fun_prop]

中文:
定理 DifferentiableWithinAt.comp
  结论: {g : F -> G} {t : 集合 F}
  证明: (hg.hasFDerivWithinAt.comp x hf.hasFDerivWithinAt h).differentiableWithinAt

@[fun_prop]

Depends on / 依赖: differentiableWithinAt, hasFDerivWithinAt, hf.hasFDerivWithinAt, hg.hasFDerivWithinAt.comp
-/
theorem DifferentiableWithinAt.comp {g : F -> G} {t : Set F}
    (hg : DifferentiableWithinAt 𝕜 g t (f x)) (hf : DifferentiableWithinAt 𝕜 f s x)
    (h : MapsTo f s t) : DifferentiableWithinAt 𝕜 (g ∘ f) s x :=
  (hg.hasFDerivWithinAt.comp x hf.hasFDerivWithinAt h).differentiableWithinAt

@[fun_prop]
/--
theorem `DifferentiableWithinAt.comp'` / 定理 `DifferentiableWithinAt.comp'`

English:
theorem DifferentiableWithinAt.comp'
  statement: {g : F -> G} {t : Set F}
  proof: hg.comp x (hf.mono inter_subset_left) inter_subset_right

@[fun_prop]

中文:
定理 DifferentiableWithinAt.comp'
  结论: {g : F -> G} {t : 集合 F}
  证明: hg.comp x (hf.mono inter_subset_left) inter_subset_right

@[fun_prop]

Depends on / 依赖: hf.mono, hg.comp, inter_subset_left, inter_subset_right
-/
theorem DifferentiableWithinAt.comp' {g : F -> G} {t : Set F}
    (hg : DifferentiableWithinAt 𝕜 g t (f x)) (hf : DifferentiableWithinAt 𝕜 f s x) :
    DifferentiableWithinAt 𝕜 (g ∘ f) (s inter f ⁻¹' t) x :=
  hg.comp x (hf.mono inter_subset_left) inter_subset_right

@[fun_prop]
/--
theorem `DifferentiableAt.fun_comp'` / 定理 `DifferentiableAt.fun_comp'`

English:
theorem DifferentiableAt.fun_comp'
  statement: {f : E -> F} {g : F -> G} (hg : DifferentiableAt 𝕜 g (f x))
  proof: (hg.hasFDerivAt.comp x hf.hasFDerivAt).differentiableAt

@[fun_prop]

中文:
定理 DifferentiableAt.fun_comp'
  结论: {f : E -> F} {g : F -> G} (hg : DifferentiableAt 𝕜 g (f x))
  证明: (hg.hasFDerivAt.comp x hf.hasFDerivAt).differentiableAt

@[fun_prop]

Depends on / 依赖: differentiableAt, hasFDerivAt, hf.hasFDerivAt, hg.hasFDerivAt.comp
-/
theorem DifferentiableAt.fun_comp' {f : E -> F} {g : F -> G} (hg : DifferentiableAt 𝕜 g (f x))
    (hf : DifferentiableAt 𝕜 f x) : DifferentiableAt 𝕜 (fun x => g (f x)) x :=
  (hg.hasFDerivAt.comp x hf.hasFDerivAt).differentiableAt

@[fun_prop]
/--
theorem `DifferentiableAt.comp` / 定理 `DifferentiableAt.comp`

English:
theorem DifferentiableAt.comp
  statement: {g : F -> G} (hg : DifferentiableAt 𝕜 g (f x))
  proof: (hg.hasFDerivAt.comp x hf.hasFDerivAt).differentiableAt

@[fun_prop]

中文:
定理 DifferentiableAt.comp
  结论: {g : F -> G} (hg : DifferentiableAt 𝕜 g (f x))
  证明: (hg.hasFDerivAt.comp x hf.hasFDerivAt).differentiableAt

@[fun_prop]

Depends on / 依赖: differentiableAt, hasFDerivAt, hf.hasFDerivAt, hg.hasFDerivAt.comp
-/
theorem DifferentiableAt.comp {g : F -> G} (hg : DifferentiableAt 𝕜 g (f x))
    (hf : DifferentiableAt 𝕜 f x) : DifferentiableAt 𝕜 (g ∘ f) x :=
  (hg.hasFDerivAt.comp x hf.hasFDerivAt).differentiableAt

@[fun_prop]
/--
theorem `DifferentiableAt.comp_differentiableWithinAt` / 定理 `DifferentiableAt.comp_differentiableWithinAt`

English:
theorem DifferentiableAt.comp_differentiableWithinAt
  statement: {g : F -> G} (hg : DifferentiableAt 𝕜 g (f x))
  proof: hg.differentiableWithinAt.comp x hf (mapsTo_univ _ _)

中文:
定理 DifferentiableAt.comp_differentiableWithinAt
  结论: {g : F -> G} (hg : DifferentiableAt 𝕜 g (f x))
  证明: hg.differentiableWithinAt.comp x hf (mapsTo_univ _ _)

Depends on / 依赖: differentiableWithinAt, hg.differentiableWithinAt.comp, mapsTo_univ
-/
theorem DifferentiableAt.comp_differentiableWithinAt {g : F -> G} (hg : DifferentiableAt 𝕜 g (f x))
    (hf : DifferentiableWithinAt 𝕜 f s x) : DifferentiableWithinAt 𝕜 (g ∘ f) s x :=
  hg.differentiableWithinAt.comp x hf (mapsTo_univ _ _)

-- Allow `to_fun` to eta-expand `g ∘ f`. Ideally, `Function.comp_def` would be a global pull lemma
-- instead, which is not supported yet: see https://github.com/leanprover-community/mathlib4/issues/40183.
attribute [local push ←] Function.comp_def
@[to_fun fderivWithin_fun_comp]
/--
theorem `fderivWithin_comp` / 定理 `fderivWithin_comp`

English:
theorem fderivWithin_comp
  statement: {g : F -> G} {t : Set F} (hg : DifferentiableWithinAt 𝕜 g t (f x))
  proof: (hg.hasFDerivWithinAt.comp x hf.hasFDerivWithinAt h).fderivWithin hxs

@[to_fun fderivWithin_fun_comp_of_eq]

中文:
定理 fderivWithin_comp
  结论: {g : F -> G} {t : 集合 F} (hg : DifferentiableWithinAt 𝕜 g t (f x))
  证明: (hg.hasFDerivWithinAt.comp x hf.hasFDerivWithinAt h).fderivWithin hxs

@[to_fun fderivWithin_fun_comp_of_eq]

Depends on / 依赖: fderivWithin, hasFDerivWithinAt, hf.hasFDerivWithinAt, hg.hasFDerivWithinAt.comp
-/
theorem fderivWithin_comp {g : F -> G} {t : Set F} (hg : DifferentiableWithinAt 𝕜 g t (f x))
    (hf : DifferentiableWithinAt 𝕜 f s x) (h : MapsTo f s t) (hxs : UniqueDiffWithinAt 𝕜 s x) :
    fderivWithin 𝕜 (g ∘ f) s x = (fderivWithin 𝕜 g t (f x)).comp (fderivWithin 𝕜 f s x) :=
  (hg.hasFDerivWithinAt.comp x hf.hasFDerivWithinAt h).fderivWithin hxs

@[to_fun fderivWithin_fun_comp_of_eq]
/--
theorem `fderivWithin_comp_of_eq` / 定理 `fderivWithin_comp_of_eq`

English:
theorem fderivWithin_comp_of_eq
  statement: {g : F -> G} {t : Set F} {y : F}
  proof: by
  subst hy; exact fderivWithin_comp _ hg hf h hxs

@[deprecated (since := "2026-05-18")] alias fderivWithin_comp' := fderivWithin_fun_comp
@[deprecated (since := "2026-05-18")] alias fderivWithin_comp_of_eq' := fderivWithin_fun_comp_of_eq

中文:
定理 fderivWithin_comp_of_eq
  结论: {g : F -> G} {t : 集合 F} {y : F}
  证明: by
  subst hy; exact fderivWithin_comp _ hg hf h hxs

@[deprecated (since := "2026-05-18")] alias fderivWithin_comp' := fderivWithin_fun_comp
@[deprecated (since := "2026-05-18")] alias fderivWithin_comp_of_eq' := fderivWithin_fun_comp_of_eq

Depends on / 依赖: fderivWithin_comp
-/
theorem fderivWithin_comp_of_eq {g : F -> G} {t : Set F} {y : F}
    (hg : DifferentiableWithinAt 𝕜 g t y) (hf : DifferentiableWithinAt 𝕜 f s x) (h : MapsTo f s t)
    (hxs : UniqueDiffWithinAt 𝕜 s x) (hy : f x = y) :
    fderivWithin 𝕜 (g ∘ f) s x = (fderivWithin 𝕜 g t (f x)).comp (fderivWithin 𝕜 f s x) := by
  subst hy; exact fderivWithin_comp _ hg hf h hxs

@[deprecated (since := "2026-05-18")] alias fderivWithin_comp' := fderivWithin_fun_comp
@[deprecated (since := "2026-05-18")] alias fderivWithin_comp_of_eq' := fderivWithin_fun_comp_of_eq

/--
theorem `fderivWithin_fderivWithin` / 定理 `fderivWithin_fderivWithin`

English:
theorem fderivWithin_fderivWithin
  statement: {g : F -> G} {f : E -> F} {x : E} {y : F} {s : Set E} {t : Set F}
  proof: by
  subst y
  rw [fderivWithin_comp x hg hf h hxs]; rw [comp_apply]

中文:
定理 fderivWithin_fderivWithin
  结论: {g : F -> G} {f : E -> F} {x : E} {y : F} {s : 集合 E} {t : 集合 F}
  证明: by
  subst y
  rw [fderivWithin_comp x hg hf h hxs]; rw [comp_apply]

Depends on / 依赖: comp_apply, fderivWithin_comp
-/
theorem fderivWithin_fderivWithin {g : F -> G} {f : E -> F} {x : E} {y : F} {s : Set E} {t : Set F}
    (hg : DifferentiableWithinAt 𝕜 g t y) (hf : DifferentiableWithinAt 𝕜 f s x) (h : MapsTo f s t)
    (hxs : UniqueDiffWithinAt 𝕜 s x) (hy : f x = y) (v : E) :
    fderivWithin 𝕜 g t y (fderivWithin 𝕜 f s x v) = fderivWithin 𝕜 (g ∘ f) s x v := by
  subst y
  rw [fderivWithin_comp x hg hf h hxs]; rw [comp_apply]

/--
theorem `fderivWithin_comp₃` / 定理 `fderivWithin_comp₃`

English:
theorem fderivWithin_comp₃
  statement: {g' : G -> G'} {g : F -> G} {t : Set F} {u : Set G} {y : F} {y' : G}
  proof: by
  subst h3g h3f
  exact (hg'.hasFDerivWithinAt.comp x (hg.hasFDerivWithinAt.comp x hf.hasFDerivWithinAt h2f) <|
    h2g.comp h2f).fderivWithin hxs

@[to_fun fderiv_fun_comp]

中文:
定理 fderivWithin_comp₃
  结论: {g' : G -> G'} {g : F -> G} {t : 集合 F} {u : 集合 G} {y : F} {y' : G}
  证明: by
  subst h3g h3f
  exact (hg'.hasFDerivWithinAt.comp x (hg.hasFDerivWithinAt.comp x hf.hasFDerivWithinAt h2f) <|
    h2g.comp h2f).fderivWithin hxs

@[to_fun fderiv_fun_comp]

Depends on / 依赖: fderivWithin, h2g.comp, hasFDerivWithinAt, hasFDerivWithinAt.comp, hf.hasFDerivWithinAt, hg.hasFDerivWithinAt.comp
-/
theorem fderivWithin_comp₃ {g' : G -> G'} {g : F -> G} {t : Set F} {u : Set G} {y : F} {y' : G}
    (hg' : DifferentiableWithinAt 𝕜 g' u y') (hg : DifferentiableWithinAt 𝕜 g t y)
    (hf : DifferentiableWithinAt 𝕜 f s x) (h2g : MapsTo g t u) (h2f : MapsTo f s t) (h3g : g y = y')
    (h3f : f x = y) (hxs : UniqueDiffWithinAt 𝕜 s x) :
    fderivWithin 𝕜 (g' ∘ g ∘ f) s x =
      (fderivWithin 𝕜 g' u y').comp ((fderivWithin 𝕜 g t y).comp (fderivWithin 𝕜 f s x)) := by
  subst h3g h3f
  exact (hg'.hasFDerivWithinAt.comp x (hg.hasFDerivWithinAt.comp x hf.hasFDerivWithinAt h2f) <|
    h2g.comp h2f).fderivWithin hxs

@[to_fun fderiv_fun_comp]
/--
theorem `fderiv_comp` / 定理 `fderiv_comp`

English:
theorem fderiv_comp
  given: {g : F -> G} (hg : DifferentiableAt 𝕜 g (f x)) (hf : DifferentiableAt 𝕜 f x)
  proof: (hg.hasFDerivAt.comp x hf.hasFDerivAt).fderiv
@[deprecated (since := "2026-05-18")] alias fderiv_comp' := fderiv_fun_comp

中文:
定理 fderiv_comp
  条件: {g : F -> G} (hg : DifferentiableAt 𝕜 g (f x)) (hf : DifferentiableAt 𝕜 f x)
  证明: (hg.hasFDerivAt.comp x hf.hasFDerivAt).fderiv
@[deprecated (since := "2026-05-18")] alias fderiv_comp' := fderiv_fun_comp

Depends on / 依赖: deprecated, fderiv, fderiv_comp, fderiv_fun_comp, hasFDerivAt, hf.hasFDerivAt, hg.hasFDerivAt.comp
-/
theorem fderiv_comp {g : F -> G} (hg : DifferentiableAt 𝕜 g (f x)) (hf : DifferentiableAt 𝕜 f x) :
    fderiv 𝕜 (g ∘ f) x = (fderiv 𝕜 g (f x)).comp (fderiv 𝕜 f x) :=
  (hg.hasFDerivAt.comp x hf.hasFDerivAt).fderiv
@[deprecated (since := "2026-05-18")] alias fderiv_comp' := fderiv_fun_comp

/--
theorem `fderiv_comp_fderivWithin` / 定理 `fderiv_comp_fderivWithin`

English:
theorem fderiv_comp_fderivWithin
  statement: {g : F -> G} (hg : DifferentiableAt 𝕜 g (f x))
  proof: (hg.hasFDerivAt.comp_hasFDerivWithinAt x hf.hasFDerivWithinAt).fderivWithin hxs

@[fun_prop]

中文:
定理 fderiv_comp_fderivWithin
  结论: {g : F -> G} (hg : DifferentiableAt 𝕜 g (f x))
  证明: (hg.hasFDerivAt.comp_hasFDerivWithinAt x hf.hasFDerivWithinAt).fderivWithin hxs

@[fun_prop]

Depends on / 依赖: comp_hasFDerivWithinAt, fderivWithin, hasFDerivAt, hasFDerivWithinAt, hf.hasFDerivWithinAt, hg.hasFDerivAt.comp_hasFDerivWithinAt
-/
theorem fderiv_comp_fderivWithin {g : F -> G} (hg : DifferentiableAt 𝕜 g (f x))
    (hf : DifferentiableWithinAt 𝕜 f s x) (hxs : UniqueDiffWithinAt 𝕜 s x) :
    fderivWithin 𝕜 (g ∘ f) s x = (fderiv 𝕜 g (f x)).comp (fderivWithin 𝕜 f s x) :=
  (hg.hasFDerivAt.comp_hasFDerivWithinAt x hf.hasFDerivWithinAt).fderivWithin hxs

@[fun_prop]
/--
theorem `DifferentiableOn.fun_comp` / 定理 `DifferentiableOn.fun_comp`

English:
theorem DifferentiableOn.fun_comp
  statement: {g : F -> G} {t : Set F} (hg : DifferentiableOn 𝕜 g t)
  proof: fun x hx => DifferentiableWithinAt.comp x (hg (f x) (st hx)) (hf x hx) st

@[fun_prop]

中文:
定理 DifferentiableOn.fun_comp
  结论: {g : F -> G} {t : 集合 F} (hg : DifferentiableOn 𝕜 g t)
  证明: fun x hx => DifferentiableWithinAt.comp x (hg (f x) (st hx)) (hf x hx) st

@[fun_prop]

Depends on / 依赖: DifferentiableWithinAt, DifferentiableWithinAt.comp
-/
theorem DifferentiableOn.fun_comp {g : F -> G} {t : Set F} (hg : DifferentiableOn 𝕜 g t)
    (hf : DifferentiableOn 𝕜 f s) (st : MapsTo f s t) :
    DifferentiableOn 𝕜 (fun x => g (f x)) s :=
  fun x hx => DifferentiableWithinAt.comp x (hg (f x) (st hx)) (hf x hx) st

@[fun_prop]
/--
theorem `DifferentiableOn.comp` / 定理 `DifferentiableOn.comp`

English:
theorem DifferentiableOn.comp
  statement: {g : F -> G} {t : Set F} (hg : DifferentiableOn 𝕜 g t)
  proof: fun x hx => DifferentiableWithinAt.comp x (hg (f x) (st hx)) (hf x hx) st

@[fun_prop]

中文:
定理 DifferentiableOn.comp
  结论: {g : F -> G} {t : 集合 F} (hg : DifferentiableOn 𝕜 g t)
  证明: fun x hx => DifferentiableWithinAt.comp x (hg (f x) (st hx)) (hf x hx) st

@[fun_prop]

Depends on / 依赖: DifferentiableWithinAt, DifferentiableWithinAt.comp
-/
theorem DifferentiableOn.comp {g : F -> G} {t : Set F} (hg : DifferentiableOn 𝕜 g t)
    (hf : DifferentiableOn 𝕜 f s) (st : MapsTo f s t) : DifferentiableOn 𝕜 (g ∘ f) s :=
  fun x hx => DifferentiableWithinAt.comp x (hg (f x) (st hx)) (hf x hx) st

@[fun_prop]
/--
theorem `Differentiable.fun_comp` / 定理 `Differentiable.fun_comp`

English:
theorem Differentiable.fun_comp
  given: {g : F -> G} (hg : Differentiable 𝕜 g) (hf : Differentiable 𝕜 f)
  proof: fun x => DifferentiableAt.comp x (hg (f x)) (hf x)

@[fun_prop]

中文:
定理 可微.fun_comp
  条件: {g : F -> G} (hg : 可微 𝕜 g) (hf : 可微 𝕜 f)
  证明: fun x => DifferentiableAt.comp x (hg (f x)) (hf x)

@[fun_prop]

Depends on / 依赖: DifferentiableAt, DifferentiableAt.comp
-/
theorem Differentiable.fun_comp {g : F -> G} (hg : Differentiable 𝕜 g) (hf : Differentiable 𝕜 f) :
    Differentiable 𝕜 (fun x => g (f x)) :=
  fun x => DifferentiableAt.comp x (hg (f x)) (hf x)

@[fun_prop]
/--
theorem `Differentiable.comp` / 定理 `Differentiable.comp`

English:
theorem Differentiable.comp
  given: {g : F -> G} (hg : Differentiable 𝕜 g) (hf : Differentiable 𝕜 f)
  proof: fun x => DifferentiableAt.comp x (hg (f x)) (hf x)

@[fun_prop]

中文:
定理 可微.comp
  条件: {g : F -> G} (hg : 可微 𝕜 g) (hf : 可微 𝕜 f)
  证明: fun x => DifferentiableAt.comp x (hg (f x)) (hf x)

@[fun_prop]

Depends on / 依赖: DifferentiableAt, DifferentiableAt.comp
-/
theorem Differentiable.comp {g : F -> G} (hg : Differentiable 𝕜 g) (hf : Differentiable 𝕜 f) :
    Differentiable 𝕜 (g ∘ f) :=
  fun x => DifferentiableAt.comp x (hg (f x)) (hf x)

@[fun_prop]
/--
theorem `Differentiable.comp_differentiableOn` / 定理 `Differentiable.comp_differentiableOn`

English:
theorem Differentiable.comp_differentiableOn
  statement: {g : F -> G} (hg : Differentiable 𝕜 g)
  proof: hg.differentiableOn.comp hf (mapsTo_univ _ _)


@[fun_prop]

中文:
定理 可微.comp_differentiableOn
  结论: {g : F -> G} (hg : 可微 𝕜 g)
  证明: hg.differentiableOn.comp hf (mapsTo_univ _ _)


@[fun_prop]

Depends on / 依赖: differentiableOn, hg.differentiableOn.comp, mapsTo_univ
-/
theorem Differentiable.comp_differentiableOn {g : F -> G} (hg : Differentiable 𝕜 g)
    (hf : DifferentiableOn 𝕜 f s) : DifferentiableOn 𝕜 (g ∘ f) s :=
  hg.differentiableOn.comp hf (mapsTo_univ _ _)


@[fun_prop]
/--
theorem `Differentiable.iterate` / 定理 `Differentiable.iterate`

English:
theorem Differentiable.iterate
  given: {f : E -> E} (hf : Differentiable 𝕜 f) (n : Nat)
  proof: Nat.recOn n differentiable_id fun _ ihn => ihn.comp hf

@[fun_prop]

中文:
定理 可微.iterate
  条件: {f : E -> E} (hf : 可微 𝕜 f) (n : 自然数)
  证明: Nat.recOn n differentiable_id fun _ ihn => ihn.comp hf

@[fun_prop]
-/
protected theorem Differentiable.iterate {f : E -> E} (hf : Differentiable 𝕜 f) (n : Nat) :
    Differentiable 𝕜 f^[n] :=
  Nat.recOn n differentiable_id fun _ ihn => ihn.comp hf

@[fun_prop]
/--
theorem `DifferentiableOn.iterate` / 定理 `DifferentiableOn.iterate`

English:
theorem DifferentiableOn.iterate
  statement: {f : E -> E} (hf : DifferentiableOn 𝕜 f s)
  proof: Nat.recOn n differentiableOn_id fun _ ihn => ihn.comp hf hs

中文:
定理 DifferentiableOn.iterate
  结论: {f : E -> E} (hf : DifferentiableOn 𝕜 f s)
  证明: Nat.recOn n differentiableOn_id fun _ ihn => ihn.comp hf hs
-/
protected theorem DifferentiableOn.iterate {f : E -> E} (hf : DifferentiableOn 𝕜 f s)
    (hs : MapsTo f s s) (n : Nat) : DifferentiableOn 𝕜 f^[n] s :=
  Nat.recOn n differentiableOn_id fun _ ihn => ihn.comp hf hs

variable {x}

/--
theorem `HasFDerivAtFilter.iterate` / 定理 `HasFDerivAtFilter.iterate`

English:
theorem HasFDerivAtFilter.iterate
  statement: {f : E -> E} {f' : E ->L[𝕜] E}
  proof: by
  induction n with
  | zero => exact hasFDerivAtFilter_id L
  | succ n ihn =>
    rw [Function.iterate_succ]; rw [pow_succ]
    exact ihn.comp hf hL

@[fun_prop]

中文:
定理 有FDerivAtFilter.iterate
  结论: {f : E -> E} {f' : E ->L[𝕜] E}
  证明: by
  induction n with
  | zero => exact hasFDerivAtFilter_id L
  | succ n ihn =>
    rw [Function.iterate_succ]; rw [pow_succ]
    exact ihn.comp hf hL

@[fun_prop]
-/
protected theorem HasFDerivAtFilter.iterate {f : E -> E} {f' : E ->L[𝕜] E}
    (hf : HasFDerivAtFilter f f' L) (hL : Tendsto (Prod.map f f) L L) (n : Nat) :
    HasFDerivAtFilter f^[n] (f' ^ n) L := by
  induction n with
  | zero => exact hasFDerivAtFilter_id L
  | succ n ihn =>
    rw [Function.iterate_succ]; rw [pow_succ]
    exact ihn.comp hf hL

@[fun_prop]
/--
theorem `HasFDerivAt.iterate` / 定理 `HasFDerivAt.iterate`

English:
theorem HasFDerivAt.iterate
  statement: {f : E -> E} {f' : E ->L[𝕜] E} (hf : HasFDerivAt f f' x)
  proof: by
  refine HasFDerivAtFilter.iterate hf ?_ n
  simpa [hx] using hf.continuousAt.tendsto.prodMap (tendsto_pure_pure f x)

@[fun_prop]

中文:
定理 在点处Fréchet可导.iterate
  结论: {f : E -> E} {f' : E ->L[𝕜] E} (hf : 在点处Fréchet可导 f f' x)
  证明: by
  refine HasFDerivAtFilter.iterate hf ?_ n
  simpa [hx] using hf.continuousAt.tendsto.prodMap (tendsto_pure_pure f x)

@[fun_prop]
-/
protected theorem HasFDerivAt.iterate {f : E -> E} {f' : E ->L[𝕜] E} (hf : HasFDerivAt f f' x)
    (hx : f x = x) (n : Nat) : HasFDerivAt f^[n] (f' ^ n) x := by
  refine HasFDerivAtFilter.iterate hf ?_ n
  simpa [hx] using hf.continuousAt.tendsto.prodMap (tendsto_pure_pure f x)

@[fun_prop]
/--
theorem `HasFDerivWithinAt.iterate` / 定理 `HasFDerivWithinAt.iterate`

English:
theorem HasFDerivWithinAt.iterate
  statement: {f : E -> E} {f' : E ->L[𝕜] E}
  proof: by
  refine HasFDerivAtFilter.iterate hf ?_ n
.prodMap (tendsto_pure_pure f x) simpa [hx] using hf.continuousWithinAt.tendsto_nhdsWithin hs

@[fun_prop]

中文:
定理 HasFDerivWithinAt.iterate
  结论: {f : E -> E} {f' : E ->L[𝕜] E}
  证明: by
  refine HasFDerivAtFilter.iterate hf ?_ n
.prodMap (tendsto_pure_pure f x) simpa [hx] using hf.continuousWithinAt.tendsto_nhdsWithin hs

@[fun_prop]
-/
protected theorem HasFDerivWithinAt.iterate {f : E -> E} {f' : E ->L[𝕜] E}
    (hf : HasFDerivWithinAt f f' s x) (hx : f x = x) (hs : MapsTo f s s) (n : Nat) :
    HasFDerivWithinAt f^[n] (f' ^ n) s x := by
  refine HasFDerivAtFilter.iterate hf ?_ n
.prodMap (tendsto_pure_pure f x) simpa [hx] using hf.continuousWithinAt.tendsto_nhdsWithin hs

@[fun_prop]
/--
theorem `HasStrictFDerivAt.iterate` / 定理 `HasStrictFDerivAt.iterate`

English:
theorem HasStrictFDerivAt.iterate
  statement: {f : E -> E} {f' : E ->L[𝕜] E}
  proof: by
  refine HasFDerivAtFilter.iterate hf ?_ n
  simpa [hx, ContinuousAt] using hf.continuousAt.prodMap' hf.continuousAt

@[fun_prop]

中文:
定理 HasStrictFDerivAt.iterate
  结论: {f : E -> E} {f' : E ->L[𝕜] E}
  证明: by
  refine HasFDerivAtFilter.iterate hf ?_ n
  simpa [hx, ContinuousAt] using hf.continuousAt.prodMap' hf.continuousAt

@[fun_prop]
-/
protected theorem HasStrictFDerivAt.iterate {f : E -> E} {f' : E ->L[𝕜] E}
    (hf : HasStrictFDerivAt f f' x) (hx : f x = x) (n : Nat) :
    HasStrictFDerivAt f^[n] (f' ^ n) x := by
  refine HasFDerivAtFilter.iterate hf ?_ n
  simpa [hx, ContinuousAt] using hf.continuousAt.prodMap' hf.continuousAt

@[fun_prop]
/--
theorem `DifferentiableAt.iterate` / 定理 `DifferentiableAt.iterate`

English:
theorem DifferentiableAt.iterate
  statement: {f : E -> E} (hf : DifferentiableAt 𝕜 f x) (hx : f x = x)
  proof: (hf.hasFDerivAt.iterate hx n).differentiableAt

@[fun_prop]

中文:
定理 DifferentiableAt.iterate
  结论: {f : E -> E} (hf : DifferentiableAt 𝕜 f x) (hx : f x = x)
  证明: (hf.hasFDerivAt.iterate hx n).differentiableAt

@[fun_prop]
-/
protected theorem DifferentiableAt.iterate {f : E -> E} (hf : DifferentiableAt 𝕜 f x) (hx : f x = x)
    (n : Nat) : DifferentiableAt 𝕜 f^[n] x :=
  (hf.hasFDerivAt.iterate hx n).differentiableAt

@[fun_prop]
/--
theorem `DifferentiableWithinAt.iterate` / 定理 `DifferentiableWithinAt.iterate`

English:
theorem DifferentiableWithinAt.iterate
  statement: {f : E -> E} (hf : DifferentiableWithinAt 𝕜 f s x)
  proof: (hf.hasFDerivWithinAt.iterate hx hs n).differentiableWithinAt

中文:
定理 DifferentiableWithinAt.iterate
  结论: {f : E -> E} (hf : DifferentiableWithinAt 𝕜 f s x)
  证明: (hf.hasFDerivWithinAt.iterate hx hs n).differentiableWithinAt
-/
protected theorem DifferentiableWithinAt.iterate {f : E -> E} (hf : DifferentiableWithinAt 𝕜 f s x)
    (hx : f x = x) (hs : MapsTo f s s) (n : Nat) : DifferentiableWithinAt 𝕜 f^[n] s x :=
  (hf.hasFDerivWithinAt.iterate hx hs n).differentiableWithinAt

end Composition

end
