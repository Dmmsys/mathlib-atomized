/-
Copyright (c) 2025 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.ContinuousMultilinearMap
public import Mathlib.Analysis.Normed.Module.Alternating.Basic

/-!
# Derivatives of operations on continuous alternating maps

In this file we prove formulas for the derivatives of

- `ContinuousAlternatingMap.compContinuousLinearMap`, the pullback of a continuous alternating map
  along a continuous linear map;
- application of a `ContinuousAlternatingMap` as a function of both the map and the vectors.
-/

public section

variable {𝕜 ι E F G H : Type*}
  [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G] [NormedAddCommGroup H] [NormedSpace 𝕜 H]

open ContinuousAlternatingMap
open scoped Topology

section CompContinuousLinearMap

variable
  {f : E -> G [⋀^ι]->L[𝕜] H} {f' : E ->L[𝕜] G [⋀^ι]->L[𝕜] H}
  {g : E -> F ->L[𝕜] G} {g' : E ->L[𝕜] F ->L[𝕜] G}
  {s : Set E} {x : E}


/--
theorem `ContinuousAlternatingMap.hasStrictFDerivAt_toContinuousMultilinearMap_comp_iff` / 定理 `ContinuousAlternatingMap.hasStrictFDerivAt_toContinuousMultilinearMap_comp_iff`

English:
theorem ContinuousAlternatingMap.hasStrictFDerivAt_toContinuousMultilinearMap_comp_iff
  given: [Finite ι]
  proof: by
  cases nonempty_fintype ι
  constructor <;> intro h
  · rw [hasStrictFDerivAt_iff_isLittleOTVS] at h ⊢
    refine Asymptotics.IsBigOTVS.trans_isLittleOTVS ?_ h
    simp only [Function.comp_apply, ← toContinuousMultilinearMapCLM_apply 𝕜,
      ContinuousLinearMap.comp_apply, ← map_sub]
    apply LinearMap.isBigOTVS_rev_comp
    simp [isEmbedding_toContinuousMultilinearMap.nhds_eq_comap]
  · exact (toContinuousMultilinearMapCLM 𝕜).hasStrictFDerivAt.comp x h

中文:
定理 余ntinuousAlternating映射.hasStrictFDerivAt_toContinuousMultilinearMap_comp_iff
  条件: [有限 ι]
  证明: by
  cases nonempty_fintype ι
  constructor <;> intro h
  · rw [hasStrictFDerivAt_iff_isLittleOTVS] at h ⊢
    refine Asymptotics.IsBigOTVS.trans_isLittleOTVS ?_ h
    simp only [Function.comp_apply, ← toContinuousMultilinearMapCLM_apply 𝕜,
      ContinuousLinearMap.comp_apply, ← map_sub]
    apply LinearMap.isBigOTVS_rev_comp
    simp [isEmbedding_toContinuousMultilinearMap.nhds_eq_comap]
  · exact (toContinuousMultilinearMapCLM 𝕜).hasStrictFDerivAt.comp x h

Depends on / 依赖: Asymptotics, Asymptotics.IsBigOTVS.trans_isLittleOTVS, ContinuousLinearMap, ContinuousLinearMap.comp_apply, Function, Function.comp_apply, IsBigOTVS, LinearMap, LinearMap.isBigOTVS_rev_comp, comp_apply, hasStrictFDerivAt, hasStrictFDerivAt.comp, hasStrictFDerivAt_iff_isLittleOTVS, isBigOTVS_rev_comp, isEmbedding_toContinuousMultilinearMap, isEmbedding_toContinuousMultilinearMap.nhds_eq_comap, map_sub, nhds_eq_comap, nonempty_fintype, toContinuousMultilinearMapCLM
-/
theorem ContinuousAlternatingMap.hasStrictFDerivAt_toContinuousMultilinearMap_comp_iff [Finite ι] :
    HasStrictFDerivAt (toContinuousMultilinearMap ∘ f) (toContinuousMultilinearMapCLM 𝕜 ∘L f') x ↔
      HasStrictFDerivAt f f' x := by
  cases nonempty_fintype ι
  constructor <;> intro h
  · rw [hasStrictFDerivAt_iff_isLittleOTVS] at h ⊢
    refine Asymptotics.IsBigOTVS.trans_isLittleOTVS ?_ h
    simp only [Function.comp_apply, ← toContinuousMultilinearMapCLM_apply 𝕜,
      ContinuousLinearMap.comp_apply, ← map_sub]
    apply LinearMap.isBigOTVS_rev_comp
    simp [isEmbedding_toContinuousMultilinearMap.nhds_eq_comap]
  · exact (toContinuousMultilinearMapCLM 𝕜).hasStrictFDerivAt.comp x h

section HasFDerivAt

variable [Fintype ι] [DecidableEq ι]

/--
theorem `ContinuousAlternatingMap.hasStrictFDerivAt_compContinuousLinearMap` / 定理 `ContinuousAlternatingMap.hasStrictFDerivAt_compContinuousLinearMap`

English:
theorem ContinuousAlternatingMap.hasStrictFDerivAt_compContinuousLinearMap
  proof: by
  rw [← hasStrictFDerivAt_toContinuousMultilinearMap_comp_iff]
  have H₁ := ContinuousMultilinearMap.hasStrictFDerivAt_compContinuousLinearMap
    (fg.1.1, fun _ : ι => fg.2)
  have H₂ := ((toContinuousMultilinearMapCLM 𝕜).hasStrictFDerivAt (x := fg.1))
  have H₃ := hasStrictFDerivAt_pi.mpr fun i : ι => hasStrictFDerivAt_id (𝕜 := 𝕜) fg.2
  exact H₁.comp fg (H₂.prodMap fg H₃)

中文:
定理 余ntinuousAlternating映射.hasStrictFDerivAt_compContinuousLinearMap
  证明: by
  rw [← hasStrictFDerivAt_toContinuousMultilinearMap_comp_iff]
  have H₁ := ContinuousMultilinearMap.hasStrictFDerivAt_compContinuousLinearMap
    (fg.1.1, fun _ : ι => fg.2)
  have H₂ := ((toContinuousMultilinearMapCLM 𝕜).hasStrictFDerivAt (x := fg.1))
  have H₃ := hasStrictFDerivAt_pi.mpr fun i : ι => hasStrictFDerivAt_id (𝕜 := 𝕜) fg.2
  exact H₁.comp fg (H₂.prodMap fg H₃)

Depends on / 依赖: ContinuousMultilinearMap, ContinuousMultilinearMap.hasStrictFDerivAt_compContinuousLinearMap, hasStrictFDerivAt, hasStrictFDerivAt_compContinuousLinearMap, hasStrictFDerivAt_id, hasStrictFDerivAt_pi, hasStrictFDerivAt_pi.mpr, hasStrictFDerivAt_toContinuousMultilinearMap_comp_iff, prodMap, toContinuousMultilinearMapCLM
-/
theorem ContinuousAlternatingMap.hasStrictFDerivAt_compContinuousLinearMap
    (fg : (G [⋀^ι]->L[𝕜] H) × (F ->L[𝕜] G)) :
    HasStrictFDerivAt
      (fun fg : (G [⋀^ι]->L[𝕜] H) × (F ->L[𝕜] G) => fg.1.compContinuousLinearMap fg.2)
      (compContinuousLinearMapCLM fg.2 ∘L .fst _ _ _ +
        fg.1.fderivCompContinuousLinearMap fg.2 ∘L .snd _ _ _)
      fg := by
  rw [← hasStrictFDerivAt_toContinuousMultilinearMap_comp_iff]
  have H₁ := ContinuousMultilinearMap.hasStrictFDerivAt_compContinuousLinearMap
    (fg.1.1, fun _ : ι => fg.2)
  have H₂ := ((toContinuousMultilinearMapCLM 𝕜).hasStrictFDerivAt (x := fg.1))
  have H₃ := hasStrictFDerivAt_pi.mpr fun i : ι => hasStrictFDerivAt_id (𝕜 := 𝕜) fg.2
  exact H₁.comp fg (H₂.prodMap fg H₃)

/--
theorem `HasStrictFDerivAt.continuousAlternatingMapCompContinuousLinearMap` / 定理 `HasStrictFDerivAt.continuousAlternatingMapCompContinuousLinearMap`

English:
theorem HasStrictFDerivAt.continuousAlternatingMapCompContinuousLinearMap
  proof: .comp x (hf.prodMk hg) hasStrictFDerivAt_compContinuousLinearMap (f x, g x)

中文:
定理 HasStrictFDerivAt.continuousAlternatingMapCompContinuousLinearMap
  证明: .comp x (hf.prodMk hg) hasStrictFDerivAt_compContinuousLinearMap (f x, g x)

Depends on / 依赖: hasStrictFDerivAt_compContinuousLinearMap, hf.prodMk, prodMk
-/
theorem HasStrictFDerivAt.continuousAlternatingMapCompContinuousLinearMap
    (hf : HasStrictFDerivAt f f' x) (hg : HasStrictFDerivAt g g' x) :
    HasStrictFDerivAt (fun x => (f x).compContinuousLinearMap (g x))
      (compContinuousLinearMapCLM (g x) ∘L f' +
        (f x).fderivCompContinuousLinearMap (g x) ∘L g') x :=
.comp x (hf.prodMk hg) hasStrictFDerivAt_compContinuousLinearMap (f x, g x)

/--
theorem `HasFDerivAt.continuousAlternatingMapCompContinuousLinearMap` / 定理 `HasFDerivAt.continuousAlternatingMapCompContinuousLinearMap`

English:
theorem HasFDerivAt.continuousAlternatingMapCompContinuousLinearMap
  proof: by
  convert!
.comp x (hf.prodMk hg) .hasFDerivAt hasStrictFDerivAt_compContinuousLinearMap (f x, (g x))

中文:
定理 在点处Fréchet可导.continuousAlternatingMapCompContinuousLinearMap
  证明: by
  convert!
.comp x (hf.prodMk hg) .hasFDerivAt hasStrictFDerivAt_compContinuousLinearMap (f x, (g x))

Depends on / 依赖: convert, hasFDerivAt, hasStrictFDerivAt_compContinuousLinearMap, hf.prodMk, prodMk
-/
theorem HasFDerivAt.continuousAlternatingMapCompContinuousLinearMap
    (hf : HasFDerivAt f f' x) (hg : HasFDerivAt g g' x) :
    HasFDerivAt (fun x => (f x).compContinuousLinearMap (g x))
      (compContinuousLinearMapCLM (g x) ∘L f' +
        (f x).fderivCompContinuousLinearMap (g x) ∘L g') x := by
  convert!
.comp x (hf.prodMk hg) .hasFDerivAt hasStrictFDerivAt_compContinuousLinearMap (f x, (g x))

/--
theorem `HasFDerivWithinAt.continuousAlternatingMapCompContinuousLinearMap` / 定理 `HasFDerivWithinAt.continuousAlternatingMapCompContinuousLinearMap`

English:
theorem HasFDerivWithinAt.continuousAlternatingMapCompContinuousLinearMap
  proof: by
  convert!
.comp_hasFDerivWithinAt .hasFDerivAt hasStrictFDerivAt_compContinuousLinearMap (f x, (g x))
      x (hf.prodMk hg)

中文:
定理 HasFDerivWithinAt.continuousAlternatingMapCompContinuousLinearMap
  证明: by
  convert!
.comp_hasFDerivWithinAt .hasFDerivAt hasStrictFDerivAt_compContinuousLinearMap (f x, (g x))
      x (hf.prodMk hg)

Depends on / 依赖: comp_hasFDerivWithinAt, convert, hasFDerivAt, hasStrictFDerivAt_compContinuousLinearMap, hf.prodMk, prodMk
-/
theorem HasFDerivWithinAt.continuousAlternatingMapCompContinuousLinearMap
    (hf : HasFDerivWithinAt f f' s x) (hg : HasFDerivWithinAt g g' s x) :
    HasFDerivWithinAt (fun x => (f x).compContinuousLinearMap (g x))
      (compContinuousLinearMapCLM (g x) ∘L f' +
        (f x).fderivCompContinuousLinearMap (g x) ∘L g') s x := by
  convert!
.comp_hasFDerivWithinAt .hasFDerivAt hasStrictFDerivAt_compContinuousLinearMap (f x, (g x))
      x (hf.prodMk hg)

/--
theorem `fderivWithin_continuousAlternatingMapCompContinuousLinearMap` / 定理 `fderivWithin_continuousAlternatingMapCompContinuousLinearMap`

English:
theorem fderivWithin_continuousAlternatingMapCompContinuousLinearMap
  proof: hf.hasFDerivWithinAt.continuousAlternatingMapCompContinuousLinearMap (hg.hasFDerivWithinAt)
.fderivWithin hs

中文:
定理 fderivWithin_continuousAlternatingMapCompContinuousLinearMap
  证明: hf.hasFDerivWithinAt.continuousAlternatingMapCompContinuousLinearMap (hg.hasFDerivWithinAt)
.fderivWithin hs

Depends on / 依赖: continuousAlternatingMapCompContinuousLinearMap, fderivWithin, hasFDerivWithinAt, hf.hasFDerivWithinAt.continuousAlternatingMapCompContinuousLinearMap, hg.hasFDerivWithinAt
-/
theorem fderivWithin_continuousAlternatingMapCompContinuousLinearMap
    (hf : DifferentiableWithinAt 𝕜 f s x) (hg : DifferentiableWithinAt 𝕜 g s x)
    (hs : UniqueDiffWithinAt 𝕜 s x) :
    fderivWithin 𝕜 (fun x => (f x).compContinuousLinearMap (g x)) s x =
      compContinuousLinearMapCLM (g x) ∘L fderivWithin 𝕜 f s x +
        (f x).fderivCompContinuousLinearMap (g x) ∘L fderivWithin 𝕜 g s x :=
  hf.hasFDerivWithinAt.continuousAlternatingMapCompContinuousLinearMap (hg.hasFDerivWithinAt)
.fderivWithin hs

/--
theorem `fderiv_continuousAlternatingMapCompContinuousLinearMap` / 定理 `fderiv_continuousAlternatingMapCompContinuousLinearMap`

English:
theorem fderiv_continuousAlternatingMapCompContinuousLinearMap
  proof: .fderiv hf.hasFDerivAt.continuousAlternatingMapCompContinuousLinearMap (hg.hasFDerivAt)

中文:
定理 fderiv_continuousAlternatingMapCompContinuousLinearMap
  证明: .fderiv hf.hasFDerivAt.continuousAlternatingMapCompContinuousLinearMap (hg.hasFDerivAt)

Depends on / 依赖: continuousAlternatingMapCompContinuousLinearMap, fderiv, hasFDerivAt, hf.hasFDerivAt.continuousAlternatingMapCompContinuousLinearMap, hg.hasFDerivAt
-/
theorem fderiv_continuousAlternatingMapCompContinuousLinearMap
    (hf : DifferentiableAt 𝕜 f x) (hg : DifferentiableAt 𝕜 g x) :
    fderiv 𝕜 (fun x => (f x).compContinuousLinearMap (g x)) x =
      compContinuousLinearMapCLM (g x) ∘L fderiv 𝕜 f x +
        (f x).fderivCompContinuousLinearMap (g x) ∘L fderiv 𝕜 g x :=
.fderiv hf.hasFDerivAt.continuousAlternatingMapCompContinuousLinearMap (hg.hasFDerivAt)

end HasFDerivAt

/-!
### Differentiability of the pullback

In this section we prove that the pullback of a continuous alternating map
along a continuous linear map is differentiable with respect to a parameter,
provided that both maps are differentiable.
-/

variable [Finite ι]

/--
theorem `DifferentiableWithinAt.continuousAlternatingMapCompContinuousLinearMap` / 定理 `DifferentiableWithinAt.continuousAlternatingMapCompContinuousLinearMap`

English:
theorem DifferentiableWithinAt.continuousAlternatingMapCompContinuousLinearMap
  proof: by
  cases nonempty_fintype ι
  classical
  exact hf.hasFDerivWithinAt.continuousAlternatingMapCompContinuousLinearMap hg.hasFDerivWithinAt
.differentiableWithinAt

中文:
定理 DifferentiableWithinAt.continuousAlternatingMapCompContinuousLinearMap
  证明: by
  cases nonempty_fintype ι
  classical
  exact hf.hasFDerivWithinAt.continuousAlternatingMapCompContinuousLinearMap hg.hasFDerivWithinAt
.differentiableWithinAt

Depends on / 依赖: classical, continuousAlternatingMapCompContinuousLinearMap, differentiableWithinAt, hasFDerivWithinAt, hf.hasFDerivWithinAt.continuousAlternatingMapCompContinuousLinearMap, hg.hasFDerivWithinAt, nonempty_fintype
-/
theorem DifferentiableWithinAt.continuousAlternatingMapCompContinuousLinearMap
    (hf : DifferentiableWithinAt 𝕜 f s x) (hg : DifferentiableWithinAt 𝕜 g s x) :
    DifferentiableWithinAt 𝕜 (fun x => (f x).compContinuousLinearMap (g x)) s x := by
  cases nonempty_fintype ι
  classical
  exact hf.hasFDerivWithinAt.continuousAlternatingMapCompContinuousLinearMap hg.hasFDerivWithinAt
.differentiableWithinAt

/--
theorem `DifferentiableAt.continuousAlternatingMapCompContinuousLinearMap` / 定理 `DifferentiableAt.continuousAlternatingMapCompContinuousLinearMap`

English:
theorem DifferentiableAt.continuousAlternatingMapCompContinuousLinearMap
  proof: by
  cases nonempty_fintype ι
  classical
  exact hf.hasFDerivAt.continuousAlternatingMapCompContinuousLinearMap hg.hasFDerivAt
.differentiableAt

中文:
定理 DifferentiableAt.continuousAlternatingMapCompContinuousLinearMap
  证明: by
  cases nonempty_fintype ι
  classical
  exact hf.hasFDerivAt.continuousAlternatingMapCompContinuousLinearMap hg.hasFDerivAt
.differentiableAt

Depends on / 依赖: classical, continuousAlternatingMapCompContinuousLinearMap, differentiableAt, hasFDerivAt, hf.hasFDerivAt.continuousAlternatingMapCompContinuousLinearMap, hg.hasFDerivAt, nonempty_fintype
-/
theorem DifferentiableAt.continuousAlternatingMapCompContinuousLinearMap
    (hf : DifferentiableAt 𝕜 f x) (hg : DifferentiableAt 𝕜 g x) :
    DifferentiableAt 𝕜 (fun x => (f x).compContinuousLinearMap (g x)) x := by
  cases nonempty_fintype ι
  classical
  exact hf.hasFDerivAt.continuousAlternatingMapCompContinuousLinearMap hg.hasFDerivAt
.differentiableAt

end CompContinuousLinearMap

/-!
### Derivative of a continuous alternating map applied to a tuple of vectors

In this section we prove the formula for the derivative `D_xf(x; g_0(x), ..., g_n(x))`.
-/

section Apply

variable {f : E -> F [⋀^ι]->L[𝕜] G} {f' : E ->L[𝕜] F [⋀^ι]->L[𝕜] G}
  {g : ι -> E -> F} {g' : ι -> E ->L[𝕜] F}
  {s : Set E} {x : E}

section HasFDerivAt

variable [Fintype ι] [DecidableEq ι]

namespace ContinuousAlternatingMap

/--
theorem `hasStrictFDerivAt` / 定理 `hasStrictFDerivAt`

English:
theorem hasStrictFDerivAt
  given: (f : E [⋀^ι]->L[𝕜] F) (x : ι -> E)
  proof: f.1.hasStrictFDerivAt x

中文:
定理 hasStrictFDerivAt
  条件: (f : E [⋀^ι]->L[𝕜] F) (x : ι -> E)
  证明: f.1.hasStrictFDerivAt x

Depends on / 依赖: hasStrictFDerivAt
-/
theorem hasStrictFDerivAt (f : E [⋀^ι]->L[𝕜] F) (x : ι -> E) :
    HasStrictFDerivAt f (f.1.linearDeriv x) x :=
  f.1.hasStrictFDerivAt x

/--
theorem `hasFDerivAt` / 定理 `hasFDerivAt`

English:
theorem hasFDerivAt
  given: (f : E [⋀^ι]->L[𝕜] F) (x : ι -> E)
  statement: HasFDerivAt f (f.1.linearDeriv x) x
  proof: f.1.hasFDerivAt x

中文:
定理 hasFDerivAt
  条件: (f : E [⋀^ι]->L[𝕜] F) (x : ι -> E)
  结论: 在点处Fréchet可导 f (f.1.linearDeriv x) x
  证明: f.1.hasFDerivAt x

Depends on / 依赖: hasFDerivAt
-/
theorem hasFDerivAt (f : E [⋀^ι]->L[𝕜] F) (x : ι -> E) : HasFDerivAt f (f.1.linearDeriv x) x :=
  f.1.hasFDerivAt x

/--
theorem `hasFDerivWithinAt` / 定理 `hasFDerivWithinAt`

English:
theorem hasFDerivWithinAt
  given: (f : E [⋀^ι]->L[𝕜] F) (s : Set (ι -> E)) (x : ι -> E)
  proof: (f.hasFDerivAt x).hasFDerivWithinAt

中文:
定理 hasFDerivWithinAt
  条件: (f : E [⋀^ι]->L[𝕜] F) (s : 集合 (ι -> E)) (x : ι -> E)
  证明: (f.hasFDerivAt x).hasFDerivWithinAt

Depends on / 依赖: f.hasFDerivAt, hasFDerivAt, hasFDerivWithinAt
-/
theorem hasFDerivWithinAt (f : E [⋀^ι]->L[𝕜] F) (s : Set (ι -> E)) (x : ι -> E) :
    HasFDerivWithinAt f (f.1.linearDeriv x) s x :=
  (f.hasFDerivAt x).hasFDerivWithinAt

end ContinuousAlternatingMap

/--
theorem `HasStrictFDerivAt.continuousAlternatingMap_apply` / 定理 `HasStrictFDerivAt.continuousAlternatingMap_apply`

English:
theorem HasStrictFDerivAt.continuousAlternatingMap_apply
  statement: (hf : HasStrictFDerivAt f f' x)
  proof: (toContinuousMultilinearMapCLM 𝕜).hasStrictFDerivAt.comp x hf
.continuousMultilinearMap_apply hg

中文:
定理 HasStrictFDerivAt.continuousAlternatingMap_apply
  结论: (hf : HasStrictFDerivAt f f' x)
  证明: (toContinuousMultilinearMapCLM 𝕜).hasStrictFDerivAt.comp x hf
.continuousMultilinearMap_apply hg

Depends on / 依赖: continuousMultilinearMap_apply, hasStrictFDerivAt, hasStrictFDerivAt.comp, toContinuousMultilinearMapCLM
-/
theorem HasStrictFDerivAt.continuousAlternatingMap_apply (hf : HasStrictFDerivAt f f' x)
    (hg : forall i, HasStrictFDerivAt (g i) (g' i) x) :
    HasStrictFDerivAt
      (fun x => f x (g · x))
      (apply 𝕜 F G (g · x) ∘L f' + ∑ i, (f x).toContinuousLinearMap (g · x) i ∘L g' i)
      x :=
  (toContinuousMultilinearMapCLM 𝕜).hasStrictFDerivAt.comp x hf
.continuousMultilinearMap_apply hg

/--
theorem `HasFDerivAt.continuousAlternatingMap_apply` / 定理 `HasFDerivAt.continuousAlternatingMap_apply`

English:
theorem HasFDerivAt.continuousAlternatingMap_apply
  statement: (hf : HasFDerivAt f f' x)
  proof: (toContinuousMultilinearMapCLM 𝕜).hasFDerivAt.comp x hf
.continuousMultilinearMap_apply hg

中文:
定理 在点处Fréchet可导.continuousAlternatingMap_apply
  结论: (hf : 在点处Fréchet可导 f f' x)
  证明: (toContinuousMultilinearMapCLM 𝕜).hasFDerivAt.comp x hf
.continuousMultilinearMap_apply hg

Depends on / 依赖: continuousMultilinearMap_apply, hasFDerivAt, hasFDerivAt.comp, toContinuousMultilinearMapCLM
-/
theorem HasFDerivAt.continuousAlternatingMap_apply (hf : HasFDerivAt f f' x)
    (hg : forall i, HasFDerivAt (g i) (g' i) x) :
    HasFDerivAt
      (fun x => f x (g · x))
      (apply 𝕜 F G (g · x) ∘L f' + ∑ i, (f x).toContinuousLinearMap (g · x) i ∘L g' i)
      x :=
  (toContinuousMultilinearMapCLM 𝕜).hasFDerivAt.comp x hf
.continuousMultilinearMap_apply hg

/--
theorem `HasFDerivWithinAt.continuousAlternatingMap_apply` / 定理 `HasFDerivWithinAt.continuousAlternatingMap_apply`

English:
theorem HasFDerivWithinAt.continuousAlternatingMap_apply
  statement: (hf : HasFDerivWithinAt f f' s x)
  proof: (toContinuousMultilinearMapCLM 𝕜).hasFDerivAt.comp_hasFDerivWithinAt x hf
.continuousMultilinearMap_apply hg

中文:
定理 HasFDerivWithinAt.continuousAlternatingMap_apply
  结论: (hf : HasFDerivWithinAt f f' s x)
  证明: (toContinuousMultilinearMapCLM 𝕜).hasFDerivAt.comp_hasFDerivWithinAt x hf
.continuousMultilinearMap_apply hg

Depends on / 依赖: comp_hasFDerivWithinAt, continuousMultilinearMap_apply, hasFDerivAt, hasFDerivAt.comp_hasFDerivWithinAt, toContinuousMultilinearMapCLM
-/
theorem HasFDerivWithinAt.continuousAlternatingMap_apply (hf : HasFDerivWithinAt f f' s x)
    (hg : forall i, HasFDerivWithinAt (g i) (g' i) s x) :
    HasFDerivWithinAt
      (fun x => f x (g · x))
      (apply 𝕜 F G (g · x) ∘L f' + ∑ i, (f x).toContinuousLinearMap (g · x) i ∘L g' i)
      s x :=
  (toContinuousMultilinearMapCLM 𝕜).hasFDerivAt.comp_hasFDerivWithinAt x hf
.continuousMultilinearMap_apply hg

/--
theorem `fderivWithin_continuousAlternatingMap_apply` / 定理 `fderivWithin_continuousAlternatingMap_apply`

English:
theorem fderivWithin_continuousAlternatingMap_apply
  statement: (hf : DifferentiableWithinAt 𝕜 f s x)
  proof: hf.hasFDerivWithinAt.continuousAlternatingMap_apply (fun i => (hg i).hasFDerivWithinAt)
.fderivWithin hs

中文:
定理 fderivWithin_continuousAlternatingMap_apply
  结论: (hf : DifferentiableWithinAt 𝕜 f s x)
  证明: hf.hasFDerivWithinAt.continuousAlternatingMap_apply (fun i => (hg i).hasFDerivWithinAt)
.fderivWithin hs

Depends on / 依赖: continuousAlternatingMap_apply, fderivWithin, hasFDerivWithinAt, hf.hasFDerivWithinAt.continuousAlternatingMap_apply
-/
theorem fderivWithin_continuousAlternatingMap_apply (hf : DifferentiableWithinAt 𝕜 f s x)
    (hg : forall i, DifferentiableWithinAt 𝕜 (g i) s x) (hs : UniqueDiffWithinAt 𝕜 s x) :
    fderivWithin 𝕜 (fun x => f x (g · x)) s x =
      apply 𝕜 F G (g · x) ∘L fderivWithin 𝕜 f s x +
        ∑ i, (f x).toContinuousLinearMap (g · x) i ∘L fderivWithin 𝕜 (g i) s x :=
  hf.hasFDerivWithinAt.continuousAlternatingMap_apply (fun i => (hg i).hasFDerivWithinAt)
.fderivWithin hs

/--
theorem `fderivWithin_continuousAlternatingMap_apply_apply` / 定理 `fderivWithin_continuousAlternatingMap_apply_apply`

English:
theorem fderivWithin_continuousAlternatingMap_apply_apply
  statement: (hf : DifferentiableWithinAt 𝕜 f s x)
  proof: by
  simp [fderivWithin_continuousAlternatingMap_apply, *]

中文:
定理 fderivWithin_continuousAlternatingMap_apply_apply
  结论: (hf : DifferentiableWithinAt 𝕜 f s x)
  证明: by
  simp [fderivWithin_continuousAlternatingMap_apply, *]

Depends on / 依赖: fderivWithin_continuousAlternatingMap_apply
-/
theorem fderivWithin_continuousAlternatingMap_apply_apply (hf : DifferentiableWithinAt 𝕜 f s x)
    (hg : forall i, DifferentiableWithinAt 𝕜 (g i) s x) (hs : UniqueDiffWithinAt 𝕜 s x) (dx : E) :
    fderivWithin 𝕜 (fun x => f x (g · x)) s x dx =
      fderivWithin 𝕜 f s x dx (g · x) +
        ∑ i, f x (Function.update (g · x) i (fderivWithin 𝕜 (g i) s x dx)) := by
  simp [fderivWithin_continuousAlternatingMap_apply, *]

/--
theorem `fderiv_continuousAlternatingMap_apply` / 定理 `fderiv_continuousAlternatingMap_apply`

English:
theorem fderiv_continuousAlternatingMap_apply
  statement: (hf : DifferentiableAt 𝕜 f x)
  proof: .fderiv hf.hasFDerivAt.continuousAlternatingMap_apply (fun i => (hg i).hasFDerivAt)

中文:
定理 fderiv_continuousAlternatingMap_apply
  结论: (hf : DifferentiableAt 𝕜 f x)
  证明: .fderiv hf.hasFDerivAt.continuousAlternatingMap_apply (fun i => (hg i).hasFDerivAt)

Depends on / 依赖: continuousAlternatingMap_apply, fderiv, hasFDerivAt, hf.hasFDerivAt.continuousAlternatingMap_apply
-/
theorem fderiv_continuousAlternatingMap_apply (hf : DifferentiableAt 𝕜 f x)
    (hg : forall i, DifferentiableAt 𝕜 (g i) x) :
    fderiv 𝕜 (fun x => f x (g · x)) x =
      apply 𝕜 F G (g · x) ∘L fderiv 𝕜 f x +
        ∑ i, (f x).toContinuousLinearMap (g · x) i ∘L fderiv 𝕜 (g i) x :=
.fderiv hf.hasFDerivAt.continuousAlternatingMap_apply (fun i => (hg i).hasFDerivAt)

/--
theorem `fderiv_continuousAlternatingMap_apply_apply` / 定理 `fderiv_continuousAlternatingMap_apply_apply`

English:
theorem fderiv_continuousAlternatingMap_apply_apply
  statement: (hf : DifferentiableAt 𝕜 f x)
  proof: by
  simp [fderiv_continuousAlternatingMap_apply, *]

中文:
定理 fderiv_continuousAlternatingMap_apply_apply
  结论: (hf : DifferentiableAt 𝕜 f x)
  证明: by
  simp [fderiv_continuousAlternatingMap_apply, *]

Depends on / 依赖: fderiv_continuousAlternatingMap_apply
-/
theorem fderiv_continuousAlternatingMap_apply_apply (hf : DifferentiableAt 𝕜 f x)
    (hg : forall i, DifferentiableAt 𝕜 (g i) x) (dx : E) :
    fderiv 𝕜 (fun x => f x (g · x)) x dx =
      fderiv 𝕜 f x dx (g · x) +
        ∑ i, f x (Function.update (g · x) i (fderiv 𝕜 (g i) x dx)) := by
  simp [fderiv_continuousAlternatingMap_apply, *]

end HasFDerivAt

variable [Finite ι]

/--
theorem `DifferentiableWithinAt.continuousAlternatingMap_apply` / 定理 `DifferentiableWithinAt.continuousAlternatingMap_apply`

English:
theorem DifferentiableWithinAt.continuousAlternatingMap_apply
  statement: (hf : DifferentiableWithinAt 𝕜 f s x)
  proof: by
  cases nonempty_fintype ι
  classical
  exact hf.hasFDerivWithinAt.continuousAlternatingMap_apply (fun i => (hg i).hasFDerivWithinAt)
.differentiableWithinAt

中文:
定理 DifferentiableWithinAt.continuousAlternatingMap_apply
  结论: (hf : DifferentiableWithinAt 𝕜 f s x)
  证明: by
  cases nonempty_fintype ι
  classical
  exact hf.hasFDerivWithinAt.continuousAlternatingMap_apply (fun i => (hg i).hasFDerivWithinAt)
.differentiableWithinAt

Depends on / 依赖: classical, continuousAlternatingMap_apply, differentiableWithinAt, hasFDerivWithinAt, hf.hasFDerivWithinAt.continuousAlternatingMap_apply, nonempty_fintype
-/
theorem DifferentiableWithinAt.continuousAlternatingMap_apply (hf : DifferentiableWithinAt 𝕜 f s x)
    (hg : forall i, DifferentiableWithinAt 𝕜 (g i) s x) :
    DifferentiableWithinAt 𝕜 (fun x => f x (g · x)) s x := by
  cases nonempty_fintype ι
  classical
  exact hf.hasFDerivWithinAt.continuousAlternatingMap_apply (fun i => (hg i).hasFDerivWithinAt)
.differentiableWithinAt

/--
theorem `DifferentiableAt.continuousAlternatingMap_apply` / 定理 `DifferentiableAt.continuousAlternatingMap_apply`

English:
theorem DifferentiableAt.continuousAlternatingMap_apply
  statement: (hf : DifferentiableAt 𝕜 f x)
  proof: by
  cases nonempty_fintype ι
  classical
  exact hf.hasFDerivAt.continuousAlternatingMap_apply (fun i => (hg i).hasFDerivAt)
.differentiableAt

中文:
定理 DifferentiableAt.continuousAlternatingMap_apply
  结论: (hf : DifferentiableAt 𝕜 f x)
  证明: by
  cases nonempty_fintype ι
  classical
  exact hf.hasFDerivAt.continuousAlternatingMap_apply (fun i => (hg i).hasFDerivAt)
.differentiableAt

Depends on / 依赖: classical, continuousAlternatingMap_apply, differentiableAt, hasFDerivAt, hf.hasFDerivAt.continuousAlternatingMap_apply, nonempty_fintype
-/
theorem DifferentiableAt.continuousAlternatingMap_apply (hf : DifferentiableAt 𝕜 f x)
    (hg : forall i, DifferentiableAt 𝕜 (g i) x) : DifferentiableAt 𝕜 (fun x => f x (g · x)) x := by
  cases nonempty_fintype ι
  classical
  exact hf.hasFDerivAt.continuousAlternatingMap_apply (fun i => (hg i).hasFDerivAt)
.differentiableAt

/--
theorem `DifferentiableOn.continuousAlternatingMap_apply` / 定理 `DifferentiableOn.continuousAlternatingMap_apply`

English:
theorem DifferentiableOn.continuousAlternatingMap_apply
  statement: (hf : DifferentiableOn 𝕜 f s)
  proof: fun x hx => (hf x hx).continuousAlternatingMap_apply (hg · x hx)

中文:
定理 DifferentiableOn.continuousAlternatingMap_apply
  结论: (hf : DifferentiableOn 𝕜 f s)
  证明: fun x hx => (hf x hx).continuousAlternatingMap_apply (hg · x hx)

Depends on / 依赖: continuousAlternatingMap_apply
-/
theorem DifferentiableOn.continuousAlternatingMap_apply (hf : DifferentiableOn 𝕜 f s)
    (hg : forall i, DifferentiableOn 𝕜 (g i) s) : DifferentiableOn 𝕜 (fun x => f x (g · x)) s :=
  fun x hx => (hf x hx).continuousAlternatingMap_apply (hg · x hx)

/--
theorem `Differentiable.continuousAlternatingMap_apply` / 定理 `Differentiable.continuousAlternatingMap_apply`

English:
theorem Differentiable.continuousAlternatingMap_apply
  statement: (hf : Differentiable 𝕜 f)
  proof: fun x => (hf x).continuousAlternatingMap_apply (hg · x)

中文:
定理 可微.continuousAlternatingMap_apply
  结论: (hf : 可微 𝕜 f)
  证明: fun x => (hf x).continuousAlternatingMap_apply (hg · x)

Depends on / 依赖: continuousAlternatingMap_apply
-/
theorem Differentiable.continuousAlternatingMap_apply (hf : Differentiable 𝕜 f)
    (hg : forall i, Differentiable 𝕜 (g i)) : Differentiable 𝕜 (fun x => f x (g · x)) :=
  fun x => (hf x).continuousAlternatingMap_apply (hg · x)

/--
theorem `ContinuousAlternatingMap.differentiable` / 定理 `ContinuousAlternatingMap.differentiable`

English:
theorem ContinuousAlternatingMap.differentiable
  given: (f : E [⋀^ι]->L[𝕜] F)
  statement: Differentiable 𝕜 f
  proof: by
  cases nonempty_fintype ι
  apply Differentiable.continuousAlternatingMap_apply <;> fun_prop

中文:
定理 余ntinuousAlternating映射.differentiable
  条件: (f : E [⋀^ι]->L[𝕜] F)
  结论: 可微 𝕜 f
  证明: by
  cases nonempty_fintype ι
  apply Differentiable.continuousAlternatingMap_apply <;> fun_prop

Depends on / 依赖: Differentiable, Differentiable.continuousAlternatingMap_apply, continuousAlternatingMap_apply, fun_prop, nonempty_fintype
-/
theorem ContinuousAlternatingMap.differentiable (f : E [⋀^ι]->L[𝕜] F) : Differentiable 𝕜 f := by
  cases nonempty_fintype ι
  apply Differentiable.continuousAlternatingMap_apply <;> fun_prop

end Apply
