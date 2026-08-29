/-
Copyright (c) 2025 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Analytic
public import Mathlib.Analysis.Calculus.FDeriv.CompCLM

/-!
# Derivatives of operations on continuous multilinear maps

In this file,

- `ι` is an index type (`Fin n` in many applications);
- `E`, `F i`, `G i`, `H`, are normed spaces for each `i : ι`;
- `f x` is a continuous multilinear map from `Π i, G i` to `H`, depending on a parameter `x : E`;
- for each `i : ι`, `g i x` is a continuous linear map `F i → G i`,
  depending on a parameter `x : E`.

Given this data, for each `x` we can define a continuous multilinear map from `Π i, F i` to `H`
given by `(f x).compContinuousLinearMap (fun i ↦ g i x) v = f x (fun i ↦ g i x (v i))`.

As a map between functional spaces,
`ContinuousMultilinearMap.compContinuousLinearMap` is multilinear in `(f; g i)`.
Thus its derivative with respect to each map (`f` or `g i`)
is given by substituting `f'` or `g' i` instead of `f` or `g i`
in `(f x).compContinuousLinearMap (fun i ↦ g i x)`,
and the full differential is given by the sum of these terms.

In terms of bundled maps, the derivative with respect to `f`
is given by `ContinuousMultilinearMap.compContinuousLinearMapL`
and the sum of terms that represent the derivatives with respect to `g i`
is given by `ContinuousMultilinearMap.fderivCompContinuousLinearMap`.

All statements in the first section are claiming this, for various notions of differentiation.
The second section deduces the corresponding differentiability results when `ι` is finite.
-/

public section

variable {𝕜 ι E : Type*} {F G : ι -> Type*} {H : Type*}
  [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [forall i, NormedAddCommGroup (F i)] [forall i, NormedSpace 𝕜 (F i)]
  [forall i, NormedAddCommGroup (G i)] [forall i, NormedSpace 𝕜 (G i)]
  [NormedAddCommGroup H] [NormedSpace 𝕜 H]
  {f : E -> ContinuousMultilinearMap 𝕜 G H} {f' : E ->L[𝕜] ContinuousMultilinearMap 𝕜 G H}
  {g : forall i, E -> F i ->L[𝕜] G i} {g' : forall i, E ->L[𝕜] F i ->L[𝕜] G i}
  {s : Set E} {x : E}

open ContinuousMultilinearMap

section HasFDerivAt

variable [Fintype ι] [DecidableEq ι]

/--
theorem `ContinuousMultilinearMap.hasStrictFDerivAt_compContinuousLinearMap` / 定理 `ContinuousMultilinearMap.hasStrictFDerivAt_compContinuousLinearMap`

English:
theorem ContinuousMultilinearMap.hasStrictFDerivAt_compContinuousLinearMap
  proof: by
  have := (compContinuousLinearMapContinuousMultilinear 𝕜 F G H).hasStrictFDerivAt fg.2
.clm_apply hasStrictFDerivAt_fst convert! this.comp fg hasStrictFDerivAt_snd
  ext <;> simp [fderivCompContinuousLinearMap]

中文:
定理 ContinuousMultilinearMap.hasStrictFDerivAt_compContinuousLinearMap
  证明: by
  have := (compContinuousLinearMapContinuousMultilinear 𝕜 F G H).hasStrictFDerivAt fg.2
.clm_apply hasStrictFDerivAt_fst convert! this.comp fg hasStrictFDerivAt_snd
  ext <;> simp [fderivCompContinuousLinearMap]

Depends on / 依赖: clm_apply, compContinuousLinearMapContinuousMultilinear, convert, fderivCompContinuousLinearMap, hasStrictFDerivAt, hasStrictFDerivAt_fst, hasStrictFDerivAt_snd, this.comp
-/
theorem ContinuousMultilinearMap.hasStrictFDerivAt_compContinuousLinearMap
    (fg : ContinuousMultilinearMap 𝕜 G H × forall i, F i ->L[𝕜] G i) :
    HasStrictFDerivAt
      (fun fg : ContinuousMultilinearMap 𝕜 G H × forall i, F i ->L[𝕜] G i =>
        fg.1.compContinuousLinearMap fg.2)
      (compContinuousLinearMapL fg.2 ∘L .fst _ _ _ +
        fg.1.fderivCompContinuousLinearMap fg.2 ∘L .snd _ _ _)
      fg := by
  have := (compContinuousLinearMapContinuousMultilinear 𝕜 F G H).hasStrictFDerivAt fg.2
.clm_apply hasStrictFDerivAt_fst convert! this.comp fg hasStrictFDerivAt_snd
  ext <;> simp [fderivCompContinuousLinearMap]

/--
theorem `HasStrictFDerivAt.continuousMultilinearMapCompContinuousLinearMap` / 定理 `HasStrictFDerivAt.continuousMultilinearMapCompContinuousLinearMap`

English:
theorem HasStrictFDerivAt.continuousMultilinearMapCompContinuousLinearMap
  proof: hasStrictFDerivAt_compContinuousLinearMap (f x, (g · x))
.comp x (hf.prodMk (hasStrictFDerivAt_pi.2 hg))

中文:
定理 HasStrictFDerivAt.continuousMultilinearMapCompContinuousLinearMap
  证明: hasStrictFDerivAt_compContinuousLinearMap (f x, (g · x))
.comp x (hf.prodMk (hasStrictFDerivAt_pi.2 hg))

Depends on / 依赖: hasStrictFDerivAt_compContinuousLinearMap, hasStrictFDerivAt_pi, hf.prodMk, prodMk
-/
theorem HasStrictFDerivAt.continuousMultilinearMapCompContinuousLinearMap
    (hf : HasStrictFDerivAt f f' x) (hg : forall i, HasStrictFDerivAt (g i) (g' i) x) :
    HasStrictFDerivAt (fun x => (f x).compContinuousLinearMap (g · x))
      (compContinuousLinearMapL (g · x) ∘L f' +
        (f x).fderivCompContinuousLinearMap (g · x) ∘L .pi g') x :=
  hasStrictFDerivAt_compContinuousLinearMap (f x, (g · x))
.comp x (hf.prodMk (hasStrictFDerivAt_pi.2 hg))

/--
theorem `HasFDerivAt.continuousMultilinearMapCompContinuousLinearMap` / 定理 `HasFDerivAt.continuousMultilinearMapCompContinuousLinearMap`

English:
theorem HasFDerivAt.continuousMultilinearMapCompContinuousLinearMap
  proof: by
  convert!
.comp x .hasFDerivAt hasStrictFDerivAt_compContinuousLinearMap (f x, (g · x))
      (hf.prodMk (hasFDerivAt_pi.2 hg))

中文:
定理 HasFDerivAt.continuousMultilinearMapCompContinuousLinearMap
  证明: by
  convert!
.comp x .hasFDerivAt hasStrictFDerivAt_compContinuousLinearMap (f x, (g · x))
      (hf.prodMk (hasFDerivAt_pi.2 hg))

Depends on / 依赖: convert, hasFDerivAt, hasFDerivAt_pi, hasStrictFDerivAt_compContinuousLinearMap, hf.prodMk, prodMk
-/
theorem HasFDerivAt.continuousMultilinearMapCompContinuousLinearMap
    (hf : HasFDerivAt f f' x) (hg : forall i, HasFDerivAt (g i) (g' i) x) :
    HasFDerivAt (fun x => (f x).compContinuousLinearMap (g · x))
      (compContinuousLinearMapL (g · x) ∘L f' +
        (f x).fderivCompContinuousLinearMap (g · x) ∘L .pi g') x := by
  convert!
.comp x .hasFDerivAt hasStrictFDerivAt_compContinuousLinearMap (f x, (g · x))
      (hf.prodMk (hasFDerivAt_pi.2 hg))

/--
theorem `HasFDerivWithinAt.continuousMultilinearMapCompContinuousLinearMap` / 定理 `HasFDerivWithinAt.continuousMultilinearMapCompContinuousLinearMap`

English:
theorem HasFDerivWithinAt.continuousMultilinearMapCompContinuousLinearMap
  proof: by
  convert!
    hasStrictFDerivAt_compContinuousLinearMap
.comp_hasFDerivWithinAt .hasFDerivAt (f x, (g · x))
      x (hf.prodMk (hasFDerivWithinAt_pi.2 hg))

中文:
定理 HasFDerivWithinAt.continuousMultilinearMapCompContinuousLinearMap
  证明: by
  convert!
    hasStrictFDerivAt_compContinuousLinearMap
.comp_hasFDerivWithinAt .hasFDerivAt (f x, (g · x))
      x (hf.prodMk (hasFDerivWithinAt_pi.2 hg))

Depends on / 依赖: comp_hasFDerivWithinAt, convert, hasFDerivAt, hasFDerivWithinAt_pi, hasStrictFDerivAt_compContinuousLinearMap, hf.prodMk, prodMk
-/
theorem HasFDerivWithinAt.continuousMultilinearMapCompContinuousLinearMap
    (hf : HasFDerivWithinAt f f' s x) (hg : forall i, HasFDerivWithinAt (g i) (g' i) s x) :
    HasFDerivWithinAt (fun x => (f x).compContinuousLinearMap (g · x))
      (compContinuousLinearMapL (g · x) ∘L f' +
        (f x).fderivCompContinuousLinearMap (g · x) ∘L .pi g') s x := by
  convert!
    hasStrictFDerivAt_compContinuousLinearMap
.comp_hasFDerivWithinAt .hasFDerivAt (f x, (g · x))
      x (hf.prodMk (hasFDerivWithinAt_pi.2 hg))

/--
theorem `fderivWithin_continuousMultilinearMapCompContinuousLinearMap` / 定理 `fderivWithin_continuousMultilinearMapCompContinuousLinearMap`

English:
theorem fderivWithin_continuousMultilinearMapCompContinuousLinearMap
  proof: hf.hasFDerivWithinAt.continuousMultilinearMapCompContinuousLinearMap
.fderivWithin hs (fun i => (hg i).hasFDerivWithinAt)

中文:
定理 fderivWithin_continuousMultilinearMapCompContinuousLinearMap
  证明: hf.hasFDerivWithinAt.continuousMultilinearMapCompContinuousLinearMap
.fderivWithin hs (fun i => (hg i).hasFDerivWithinAt)

Depends on / 依赖: continuousMultilinearMapCompContinuousLinearMap, fderivWithin, hasFDerivWithinAt, hf.hasFDerivWithinAt.continuousMultilinearMapCompContinuousLinearMap
-/
theorem fderivWithin_continuousMultilinearMapCompContinuousLinearMap
    (hf : DifferentiableWithinAt 𝕜 f s x) (hg : forall i, DifferentiableWithinAt 𝕜 (g i) s x)
    (hs : UniqueDiffWithinAt 𝕜 s x) :
    fderivWithin 𝕜 (fun x => (f x).compContinuousLinearMap (g · x)) s x =
      compContinuousLinearMapL (g · x) ∘L fderivWithin 𝕜 f s x +
        (f x).fderivCompContinuousLinearMap (g · x) ∘L .pi fun i => fderivWithin 𝕜 (g i) s x :=
  hf.hasFDerivWithinAt.continuousMultilinearMapCompContinuousLinearMap
.fderivWithin hs (fun i => (hg i).hasFDerivWithinAt)

/--
theorem `fderiv_continuousMultilinearMapCompContinuousLinearMap` / 定理 `fderiv_continuousMultilinearMapCompContinuousLinearMap`

English:
theorem fderiv_continuousMultilinearMapCompContinuousLinearMap
  proof: hf.hasFDerivAt.continuousMultilinearMapCompContinuousLinearMap
.fderiv (fun i => (hg i).hasFDerivAt)

中文:
定理 fderiv_continuousMultilinearMapCompContinuousLinearMap
  证明: hf.hasFDerivAt.continuousMultilinearMapCompContinuousLinearMap
.fderiv (fun i => (hg i).hasFDerivAt)

Depends on / 依赖: continuousMultilinearMapCompContinuousLinearMap, fderiv, hasFDerivAt, hf.hasFDerivAt.continuousMultilinearMapCompContinuousLinearMap
-/
theorem fderiv_continuousMultilinearMapCompContinuousLinearMap
    (hf : DifferentiableAt 𝕜 f x) (hg : forall i, DifferentiableAt 𝕜 (g i) x) :
    fderiv 𝕜 (fun x => (f x).compContinuousLinearMap (g · x)) x =
      compContinuousLinearMapL (g · x) ∘L fderiv 𝕜 f x +
        (f x).fderivCompContinuousLinearMap (g · x) ∘L .pi fun i => fderiv 𝕜 (g i) x :=
  hf.hasFDerivAt.continuousMultilinearMapCompContinuousLinearMap
.fderiv (fun i => (hg i).hasFDerivAt)

end HasFDerivAt

variable [Finite ι]

/--
theorem `DifferentiableWithinAt.continuousMultilinearMapCompContinuousLinearMap` / 定理 `DifferentiableWithinAt.continuousMultilinearMapCompContinuousLinearMap`

English:
theorem DifferentiableWithinAt.continuousMultilinearMapCompContinuousLinearMap
  proof: by
  cases nonempty_fintype ι
  classical
  exact hf.hasFDerivWithinAt.continuousMultilinearMapCompContinuousLinearMap
.differentiableWithinAt (fun i => (hg i).hasFDerivWithinAt)

中文:
定理 DifferentiableWithinAt.continuousMultilinearMapCompContinuousLinearMap
  证明: by
  cases nonempty_fintype ι
  classical
  exact hf.hasFDerivWithinAt.continuousMultilinearMapCompContinuousLinearMap
.differentiableWithinAt (fun i => (hg i).hasFDerivWithinAt)

Depends on / 依赖: classical, continuousMultilinearMapCompContinuousLinearMap, differentiableWithinAt, hasFDerivWithinAt, hf.hasFDerivWithinAt.continuousMultilinearMapCompContinuousLinearMap, nonempty_fintype
-/
theorem DifferentiableWithinAt.continuousMultilinearMapCompContinuousLinearMap
    (hf : DifferentiableWithinAt 𝕜 f s x) (hg : forall i, DifferentiableWithinAt 𝕜 (g i) s x) :
    DifferentiableWithinAt 𝕜 (fun x => (f x).compContinuousLinearMap (g · x)) s x := by
  cases nonempty_fintype ι
  classical
  exact hf.hasFDerivWithinAt.continuousMultilinearMapCompContinuousLinearMap
.differentiableWithinAt (fun i => (hg i).hasFDerivWithinAt)

/--
theorem `DifferentiableAt.continuousMultilinearMapCompContinuousLinearMap` / 定理 `DifferentiableAt.continuousMultilinearMapCompContinuousLinearMap`

English:
theorem DifferentiableAt.continuousMultilinearMapCompContinuousLinearMap
  proof: by
  cases nonempty_fintype ι
  classical
  exact hf.hasFDerivAt.continuousMultilinearMapCompContinuousLinearMap
.differentiableAt (fun i => (hg i).hasFDerivAt)

中文:
定理 DifferentiableAt.continuousMultilinearMapCompContinuousLinearMap
  证明: by
  cases nonempty_fintype ι
  classical
  exact hf.hasFDerivAt.continuousMultilinearMapCompContinuousLinearMap
.differentiableAt (fun i => (hg i).hasFDerivAt)

Depends on / 依赖: classical, continuousMultilinearMapCompContinuousLinearMap, differentiableAt, hasFDerivAt, hf.hasFDerivAt.continuousMultilinearMapCompContinuousLinearMap, nonempty_fintype
-/
theorem DifferentiableAt.continuousMultilinearMapCompContinuousLinearMap
    (hf : DifferentiableAt 𝕜 f x) (hg : forall i, DifferentiableAt 𝕜 (g i) x) :
    DifferentiableAt 𝕜 (fun x => (f x).compContinuousLinearMap (g · x)) x := by
  cases nonempty_fintype ι
  classical
  exact hf.hasFDerivAt.continuousMultilinearMapCompContinuousLinearMap
.differentiableAt (fun i => (hg i).hasFDerivAt)

/--
theorem `DifferentiableOn.continuousMultilinearMapCompContinuousLinearMap` / 定理 `DifferentiableOn.continuousMultilinearMapCompContinuousLinearMap`

English:
theorem DifferentiableOn.continuousMultilinearMapCompContinuousLinearMap
  proof: fun x hx =>
  (hf x hx).continuousMultilinearMapCompContinuousLinearMap (hg · x hx)

中文:
定理 DifferentiableOn.continuousMultilinearMapCompContinuousLinearMap
  证明: fun x hx =>
  (hf x hx).continuousMultilinearMapCompContinuousLinearMap (hg · x hx)
-/
theorem DifferentiableOn.continuousMultilinearMapCompContinuousLinearMap
    (hf : DifferentiableOn 𝕜 f s) (hg : forall i, DifferentiableOn 𝕜 (g i) s) :
    DifferentiableOn 𝕜 (fun x => (f x).compContinuousLinearMap (g · x)) s := fun x hx =>
  (hf x hx).continuousMultilinearMapCompContinuousLinearMap (hg · x hx)

/--
theorem `Differentiable.continuousMultilinearMapCompContinuousLinearMap` / 定理 `Differentiable.continuousMultilinearMapCompContinuousLinearMap`

English:
theorem Differentiable.continuousMultilinearMapCompContinuousLinearMap
  proof: fun x =>
  (hf x).continuousMultilinearMapCompContinuousLinearMap (hg · x)

中文:
定理 Differentiable.continuousMultilinearMapCompContinuousLinearMap
  证明: fun x =>
  (hf x).continuousMultilinearMapCompContinuousLinearMap (hg · x)
-/
theorem Differentiable.continuousMultilinearMapCompContinuousLinearMap
    (hf : Differentiable 𝕜 f) (hg : forall i, Differentiable 𝕜 (g i)) :
    Differentiable 𝕜 (fun x => (f x).compContinuousLinearMap (g · x)) := fun x =>
  (hf x).continuousMultilinearMapCompContinuousLinearMap (hg · x)
