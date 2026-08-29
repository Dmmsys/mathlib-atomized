/-
Copyright (c) 2019 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Sébastien Gouëzel, Yury Kudryashov
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Bilinear
public import Mathlib.Analysis.Normed.Module.Alternating.Basic

/-!
# Multiplicative operations on derivatives

For detailed documentation of the Fréchet derivative,
see the module docstring of `Mathlib/Analysis/Calculus/FDeriv/Basic.lean`.

This file contains the usual formulas (and existence assertions) for the derivative of

* composition of continuous linear maps
* application of continuous (multi)linear maps to a constant
-/

public section


open Asymptotics ContinuousLinearMap Topology

section

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
variable {f : E -> F}
variable {f' : E ->L[𝕜] F}
variable {x : E}
variable {s : Set E}

section CLMCompApply

/-! ### Derivative of the pointwise composition/application of continuous linear maps -/

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace 𝕜 H] {c : E -> G ->L[𝕜] H}
  {c' : E ->L[𝕜] G ->L[𝕜] H} {d : E -> F ->L[𝕜] G} {d' : E ->L[𝕜] F ->L[𝕜] G} {u : E -> G} {u' : E ->L[𝕜] G}

@[fun_prop]
/--
theorem `HasStrictFDerivAt.clm_comp` / 定理 `HasStrictFDerivAt.clm_comp`

English:
theorem HasStrictFDerivAt.clm_comp
  given: (hc : HasStrictFDerivAt c c' x) (hd : HasStrictFDerivAt d d' x)
  proof: (isBoundedBilinearMap_comp.hasStrictFDerivAt (c x, d x)).comp x (hc.prodMk hd)

@[fun_prop]

中文:
定理 HasStrictFDerivAt.clm_comp
  条件: (hc : HasStrictFDerivAt c c' x) (hd : HasStrictFDerivAt d d' x)
  证明: (isBoundedBilinearMap_comp.hasStrictFDerivAt (c x, d x)).comp x (hc.prodMk hd)

@[fun_prop]

Depends on / 依赖: hasStrictFDerivAt, hc.prodMk, isBoundedBilinearMap_comp, isBoundedBilinearMap_comp.hasStrictFDerivAt, prodMk
-/
theorem HasStrictFDerivAt.clm_comp (hc : HasStrictFDerivAt c c' x) (hd : HasStrictFDerivAt d d' x) :
    HasStrictFDerivAt (fun y => (c y).comp (d y))
      ((compL 𝕜 F G H (c x)).comp d' + ((compL 𝕜 F G H).flip (d x)).comp c') x :=
  (isBoundedBilinearMap_comp.hasStrictFDerivAt (c x, d x)).comp x (hc.prodMk hd)

@[fun_prop]
/--
theorem `HasFDerivWithinAt.clm_comp` / 定理 `HasFDerivWithinAt.clm_comp`

English:
theorem HasFDerivWithinAt.clm_comp
  statement: (hc : HasFDerivWithinAt c c' s x)
  proof: by
  -- `by exact` to solve unification issues.
  exact (isBoundedBilinearMap_comp.hasFDerivAt (c x, d x)).comp_hasFDerivWithinAt x (hc.prodMk hd)

@[fun_prop]

中文:
定理 HasFDerivWithinAt.clm_comp
  结论: (hc : HasFDerivWithinAt c c' s x)
  证明: by
  -- `by exact` to solve unification issues.
  exact (isBoundedBilinearMap_comp.hasFDerivAt (c x, d x)).comp_hasFDerivWithinAt x (hc.prodMk hd)

@[fun_prop]
-/
theorem HasFDerivWithinAt.clm_comp (hc : HasFDerivWithinAt c c' s x)
    (hd : HasFDerivWithinAt d d' s x) :
    HasFDerivWithinAt (fun y => (c y).comp (d y))
      ((compL 𝕜 F G H (c x)).comp d' + ((compL 𝕜 F G H).flip (d x)).comp c') s x := by
  -- `by exact` to solve unification issues.
  exact (isBoundedBilinearMap_comp.hasFDerivAt (c x, d x)).comp_hasFDerivWithinAt x (hc.prodMk hd)

@[fun_prop]
/--
theorem `HasFDerivAt.clm_comp` / 定理 `HasFDerivAt.clm_comp`

English:
theorem HasFDerivAt.clm_comp
  given: (hc : HasFDerivAt c c' x) (hd : HasFDerivAt d d' x)
  proof: by
  -- `by exact` to solve unification issues.
exact (isBoundedBilinearMap_comp.hasFDerivAt (c x, d x)).comp x hc.prodMk hd

@[fun_prop]

中文:
定理 在点处Fréchet可导.clm_comp
  条件: (hc : 在点处Fréchet可导 c c' x) (hd : 在点处Fréchet可导 d d' x)
  证明: by
  -- `by exact` to solve unification issues.
exact (isBoundedBilinearMap_comp.hasFDerivAt (c x, d x)).comp x hc.prodMk hd

@[fun_prop]
-/
theorem HasFDerivAt.clm_comp (hc : HasFDerivAt c c' x) (hd : HasFDerivAt d d' x) :
    HasFDerivAt (fun y => (c y).comp (d y))
      ((compL 𝕜 F G H (c x)).comp d' + ((compL 𝕜 F G H).flip (d x)).comp c') x := by
  -- `by exact` to solve unification issues.
exact (isBoundedBilinearMap_comp.hasFDerivAt (c x, d x)).comp x hc.prodMk hd

@[fun_prop]
/--
theorem `DifferentiableWithinAt.clm_comp` / 定理 `DifferentiableWithinAt.clm_comp`

English:
theorem DifferentiableWithinAt.clm_comp
  statement: (hc : DifferentiableWithinAt 𝕜 c s x)
  proof: (hc.hasFDerivWithinAt.clm_comp hd.hasFDerivWithinAt).differentiableWithinAt

@[fun_prop]

中文:
定理 DifferentiableWithinAt.clm_comp
  结论: (hc : DifferentiableWithinAt 𝕜 c s x)
  证明: (hc.hasFDerivWithinAt.clm_comp hd.hasFDerivWithinAt).differentiableWithinAt

@[fun_prop]

Depends on / 依赖: clm_comp, differentiableWithinAt, hasFDerivWithinAt, hc.hasFDerivWithinAt.clm_comp, hd.hasFDerivWithinAt
-/
theorem DifferentiableWithinAt.clm_comp (hc : DifferentiableWithinAt 𝕜 c s x)
    (hd : DifferentiableWithinAt 𝕜 d s x) :
    DifferentiableWithinAt 𝕜 (fun y => (c y).comp (d y)) s x :=
  (hc.hasFDerivWithinAt.clm_comp hd.hasFDerivWithinAt).differentiableWithinAt

@[fun_prop]
/--
theorem `DifferentiableAt.clm_comp` / 定理 `DifferentiableAt.clm_comp`

English:
theorem DifferentiableAt.clm_comp
  given: (hc : DifferentiableAt 𝕜 c x) (hd : DifferentiableAt 𝕜 d x)
  proof: (hc.hasFDerivAt.clm_comp hd.hasFDerivAt).differentiableAt

@[fun_prop]

中文:
定理 DifferentiableAt.clm_comp
  条件: (hc : DifferentiableAt 𝕜 c x) (hd : DifferentiableAt 𝕜 d x)
  证明: (hc.hasFDerivAt.clm_comp hd.hasFDerivAt).differentiableAt

@[fun_prop]

Depends on / 依赖: clm_comp, differentiableAt, hasFDerivAt, hc.hasFDerivAt.clm_comp, hd.hasFDerivAt
-/
theorem DifferentiableAt.clm_comp (hc : DifferentiableAt 𝕜 c x) (hd : DifferentiableAt 𝕜 d x) :
    DifferentiableAt 𝕜 (fun y => (c y).comp (d y)) x :=
  (hc.hasFDerivAt.clm_comp hd.hasFDerivAt).differentiableAt

@[fun_prop]
/--
theorem `DifferentiableOn.clm_comp` / 定理 `DifferentiableOn.clm_comp`

English:
theorem DifferentiableOn.clm_comp
  given: (hc : DifferentiableOn 𝕜 c s) (hd : DifferentiableOn 𝕜 d s)
  proof: fun x hx => (hc x hx).clm_comp (hd x hx)

@[fun_prop]

中文:
定理 DifferentiableOn.clm_comp
  条件: (hc : DifferentiableOn 𝕜 c s) (hd : DifferentiableOn 𝕜 d s)
  证明: fun x hx => (hc x hx).clm_comp (hd x hx)

@[fun_prop]

Depends on / 依赖: clm_comp
-/
theorem DifferentiableOn.clm_comp (hc : DifferentiableOn 𝕜 c s) (hd : DifferentiableOn 𝕜 d s) :
    DifferentiableOn 𝕜 (fun y => (c y).comp (d y)) s := fun x hx => (hc x hx).clm_comp (hd x hx)

@[fun_prop]
/--
theorem `Differentiable.clm_comp` / 定理 `Differentiable.clm_comp`

English:
theorem Differentiable.clm_comp
  given: (hc : Differentiable 𝕜 c) (hd : Differentiable 𝕜 d)
  proof: fun x => (hc x).clm_comp (hd x)

中文:
定理 可微.clm_comp
  条件: (hc : 可微 𝕜 c) (hd : 可微 𝕜 d)
  证明: fun x => (hc x).clm_comp (hd x)

Depends on / 依赖: clm_comp
-/
theorem Differentiable.clm_comp (hc : Differentiable 𝕜 c) (hd : Differentiable 𝕜 d) :
    Differentiable 𝕜 fun y => (c y).comp (d y) := fun x => (hc x).clm_comp (hd x)

/--
theorem `fderivWithin_clm_comp` / 定理 `fderivWithin_clm_comp`

English:
theorem fderivWithin_clm_comp
  statement: (hxs : UniqueDiffWithinAt 𝕜 s x) (hc : DifferentiableWithinAt 𝕜 c s x)
  proof: (hc.hasFDerivWithinAt.clm_comp hd.hasFDerivWithinAt).fderivWithin hxs

中文:
定理 fderivWithin_clm_comp
  结论: (hxs : UniqueDiffWithinAt 𝕜 s x) (hc : DifferentiableWithinAt 𝕜 c s x)
  证明: (hc.hasFDerivWithinAt.clm_comp hd.hasFDerivWithinAt).fderivWithin hxs

Depends on / 依赖: clm_comp, fderivWithin, hasFDerivWithinAt, hc.hasFDerivWithinAt.clm_comp, hd.hasFDerivWithinAt
-/
theorem fderivWithin_clm_comp (hxs : UniqueDiffWithinAt 𝕜 s x) (hc : DifferentiableWithinAt 𝕜 c s x)
    (hd : DifferentiableWithinAt 𝕜 d s x) :
    fderivWithin 𝕜 (fun y => (c y).comp (d y)) s x =
      (compL 𝕜 F G H (c x)).comp (fderivWithin 𝕜 d s x) +
        ((compL 𝕜 F G H).flip (d x)).comp (fderivWithin 𝕜 c s x) :=
  (hc.hasFDerivWithinAt.clm_comp hd.hasFDerivWithinAt).fderivWithin hxs

/--
theorem `fderiv_clm_comp` / 定理 `fderiv_clm_comp`

English:
theorem fderiv_clm_comp
  given: (hc : DifferentiableAt 𝕜 c x) (hd : DifferentiableAt 𝕜 d x)
  proof: (hc.hasFDerivAt.clm_comp hd.hasFDerivAt).fderiv

@[fun_prop]

中文:
定理 fderiv_clm_comp
  条件: (hc : DifferentiableAt 𝕜 c x) (hd : DifferentiableAt 𝕜 d x)
  证明: (hc.hasFDerivAt.clm_comp hd.hasFDerivAt).fderiv

@[fun_prop]

Depends on / 依赖: clm_comp, fderiv, hasFDerivAt, hc.hasFDerivAt.clm_comp, hd.hasFDerivAt
-/
theorem fderiv_clm_comp (hc : DifferentiableAt 𝕜 c x) (hd : DifferentiableAt 𝕜 d x) :
    fderiv 𝕜 (fun y => (c y).comp (d y)) x =
      (compL 𝕜 F G H (c x)).comp (fderiv 𝕜 d x) +
        ((compL 𝕜 F G H).flip (d x)).comp (fderiv 𝕜 c x) :=
  (hc.hasFDerivAt.clm_comp hd.hasFDerivAt).fderiv

@[fun_prop]
/--
theorem `HasStrictFDerivAt.clm_apply` / 定理 `HasStrictFDerivAt.clm_apply`

English:
theorem HasStrictFDerivAt.clm_apply
  statement: (hc : HasStrictFDerivAt c c' x)
  proof: (isBoundedBilinearMap_apply.hasStrictFDerivAt (c x, u x)).comp x (hc.prodMk hu)

@[fun_prop]

中文:
定理 HasStrictFDerivAt.clm_apply
  结论: (hc : HasStrictFDerivAt c c' x)
  证明: (isBoundedBilinearMap_apply.hasStrictFDerivAt (c x, u x)).comp x (hc.prodMk hu)

@[fun_prop]

Depends on / 依赖: hasStrictFDerivAt, hc.prodMk, isBoundedBilinearMap_apply, isBoundedBilinearMap_apply.hasStrictFDerivAt, prodMk
-/
theorem HasStrictFDerivAt.clm_apply (hc : HasStrictFDerivAt c c' x)
    (hu : HasStrictFDerivAt u u' x) :
    HasStrictFDerivAt (fun y => (c y) (u y)) ((c x).comp u' + c'.flip (u x)) x :=
  (isBoundedBilinearMap_apply.hasStrictFDerivAt (c x, u x)).comp x (hc.prodMk hu)

@[fun_prop]
/--
theorem `HasFDerivWithinAt.clm_apply` / 定理 `HasFDerivWithinAt.clm_apply`

English:
theorem HasFDerivWithinAt.clm_apply
  statement: (hc : HasFDerivWithinAt c c' s x)
  proof: by
  -- `by exact` to solve unification issues.
  exact (isBoundedBilinearMap_apply.hasFDerivAt (c x, u x)).comp_hasFDerivWithinAt x
    (hc.prodMk hu)

@[fun_prop]

中文:
定理 HasFDerivWithinAt.clm_apply
  结论: (hc : HasFDerivWithinAt c c' s x)
  证明: by
  -- `by exact` to solve unification issues.
  exact (isBoundedBilinearMap_apply.hasFDerivAt (c x, u x)).comp_hasFDerivWithinAt x
    (hc.prodMk hu)

@[fun_prop]
-/
theorem HasFDerivWithinAt.clm_apply (hc : HasFDerivWithinAt c c' s x)
    (hu : HasFDerivWithinAt u u' s x) :
    HasFDerivWithinAt (fun y => (c y) (u y)) ((c x).comp u' + c'.flip (u x)) s x := by
  -- `by exact` to solve unification issues.
  exact (isBoundedBilinearMap_apply.hasFDerivAt (c x, u x)).comp_hasFDerivWithinAt x
    (hc.prodMk hu)

@[fun_prop]
/--
theorem `HasFDerivAt.clm_apply` / 定理 `HasFDerivAt.clm_apply`

English:
theorem HasFDerivAt.clm_apply
  given: (hc : HasFDerivAt c c' x) (hu : HasFDerivAt u u' x)
  proof: by
  -- `by exact` to solve unification issues.
  exact (isBoundedBilinearMap_apply.hasFDerivAt (c x, u x)).comp x (hc.prodMk hu)

@[fun_prop]

中文:
定理 在点处Fréchet可导.clm_apply
  条件: (hc : 在点处Fréchet可导 c c' x) (hu : 在点处Fréchet可导 u u' x)
  证明: by
  -- `by exact` to solve unification issues.
  exact (isBoundedBilinearMap_apply.hasFDerivAt (c x, u x)).comp x (hc.prodMk hu)

@[fun_prop]
-/
theorem HasFDerivAt.clm_apply (hc : HasFDerivAt c c' x) (hu : HasFDerivAt u u' x) :
    HasFDerivAt (fun y => (c y) (u y)) ((c x).comp u' + c'.flip (u x)) x := by
  -- `by exact` to solve unification issues.
  exact (isBoundedBilinearMap_apply.hasFDerivAt (c x, u x)).comp x (hc.prodMk hu)

@[fun_prop]
/--
theorem `DifferentiableWithinAt.clm_apply` / 定理 `DifferentiableWithinAt.clm_apply`

English:
theorem DifferentiableWithinAt.clm_apply
  statement: (hc : DifferentiableWithinAt 𝕜 c s x)
  proof: (hc.hasFDerivWithinAt.clm_apply hu.hasFDerivWithinAt).differentiableWithinAt

@[fun_prop]

中文:
定理 DifferentiableWithinAt.clm_apply
  结论: (hc : DifferentiableWithinAt 𝕜 c s x)
  证明: (hc.hasFDerivWithinAt.clm_apply hu.hasFDerivWithinAt).differentiableWithinAt

@[fun_prop]

Depends on / 依赖: clm_apply, differentiableWithinAt, hasFDerivWithinAt, hc.hasFDerivWithinAt.clm_apply, hu.hasFDerivWithinAt
-/
theorem DifferentiableWithinAt.clm_apply (hc : DifferentiableWithinAt 𝕜 c s x)
    (hu : DifferentiableWithinAt 𝕜 u s x) : DifferentiableWithinAt 𝕜 (fun y => (c y) (u y)) s x :=
  (hc.hasFDerivWithinAt.clm_apply hu.hasFDerivWithinAt).differentiableWithinAt

@[fun_prop]
/--
theorem `DifferentiableAt.clm_apply` / 定理 `DifferentiableAt.clm_apply`

English:
theorem DifferentiableAt.clm_apply
  given: (hc : DifferentiableAt 𝕜 c x) (hu : DifferentiableAt 𝕜 u x)
  proof: (hc.hasFDerivAt.clm_apply hu.hasFDerivAt).differentiableAt

@[fun_prop]

中文:
定理 DifferentiableAt.clm_apply
  条件: (hc : DifferentiableAt 𝕜 c x) (hu : DifferentiableAt 𝕜 u x)
  证明: (hc.hasFDerivAt.clm_apply hu.hasFDerivAt).differentiableAt

@[fun_prop]

Depends on / 依赖: clm_apply, differentiableAt, hasFDerivAt, hc.hasFDerivAt.clm_apply, hu.hasFDerivAt
-/
theorem DifferentiableAt.clm_apply (hc : DifferentiableAt 𝕜 c x) (hu : DifferentiableAt 𝕜 u x) :
    DifferentiableAt 𝕜 (fun y => (c y) (u y)) x :=
  (hc.hasFDerivAt.clm_apply hu.hasFDerivAt).differentiableAt

@[fun_prop]
/--
theorem `DifferentiableOn.clm_apply` / 定理 `DifferentiableOn.clm_apply`

English:
theorem DifferentiableOn.clm_apply
  given: (hc : DifferentiableOn 𝕜 c s) (hu : DifferentiableOn 𝕜 u s)
  proof: fun x hx => (hc x hx).clm_apply (hu x hx)

@[fun_prop]

中文:
定理 DifferentiableOn.clm_apply
  条件: (hc : DifferentiableOn 𝕜 c s) (hu : DifferentiableOn 𝕜 u s)
  证明: fun x hx => (hc x hx).clm_apply (hu x hx)

@[fun_prop]

Depends on / 依赖: clm_apply
-/
theorem DifferentiableOn.clm_apply (hc : DifferentiableOn 𝕜 c s) (hu : DifferentiableOn 𝕜 u s) :
    DifferentiableOn 𝕜 (fun y => (c y) (u y)) s := fun x hx => (hc x hx).clm_apply (hu x hx)

@[fun_prop]
/--
theorem `Differentiable.clm_apply` / 定理 `Differentiable.clm_apply`

English:
theorem Differentiable.clm_apply
  given: (hc : Differentiable 𝕜 c) (hu : Differentiable 𝕜 u)
  proof: fun x => (hc x).clm_apply (hu x)

中文:
定理 可微.clm_apply
  条件: (hc : 可微 𝕜 c) (hu : 可微 𝕜 u)
  证明: fun x => (hc x).clm_apply (hu x)

Depends on / 依赖: clm_apply
-/
theorem Differentiable.clm_apply (hc : Differentiable 𝕜 c) (hu : Differentiable 𝕜 u) :
    Differentiable 𝕜 fun y => (c y) (u y) := fun x => (hc x).clm_apply (hu x)

/--
theorem `fderivWithin_clm_apply` / 定理 `fderivWithin_clm_apply`

English:
theorem fderivWithin_clm_apply
  statement: (hxs : UniqueDiffWithinAt 𝕜 s x)
  proof: (hc.hasFDerivWithinAt.clm_apply hu.hasFDerivWithinAt).fderivWithin hxs

中文:
定理 fderivWithin_clm_apply
  结论: (hxs : UniqueDiffWithinAt 𝕜 s x)
  证明: (hc.hasFDerivWithinAt.clm_apply hu.hasFDerivWithinAt).fderivWithin hxs

Depends on / 依赖: clm_apply, fderivWithin, hasFDerivWithinAt, hc.hasFDerivWithinAt.clm_apply, hu.hasFDerivWithinAt
-/
theorem fderivWithin_clm_apply (hxs : UniqueDiffWithinAt 𝕜 s x)
    (hc : DifferentiableWithinAt 𝕜 c s x) (hu : DifferentiableWithinAt 𝕜 u s x) :
    fderivWithin 𝕜 (fun y => (c y) (u y)) s x =
      (c x).comp (fderivWithin 𝕜 u s x) + (fderivWithin 𝕜 c s x).flip (u x) :=
  (hc.hasFDerivWithinAt.clm_apply hu.hasFDerivWithinAt).fderivWithin hxs

/--
theorem `fderiv_clm_apply` / 定理 `fderiv_clm_apply`

English:
theorem fderiv_clm_apply
  given: (hc : DifferentiableAt 𝕜 c x) (hu : DifferentiableAt 𝕜 u x)
  proof: (hc.hasFDerivAt.clm_apply hu.hasFDerivAt).fderiv

中文:
定理 fderiv_clm_apply
  条件: (hc : DifferentiableAt 𝕜 c x) (hu : DifferentiableAt 𝕜 u x)
  证明: (hc.hasFDerivAt.clm_apply hu.hasFDerivAt).fderiv

Depends on / 依赖: clm_apply, fderiv, hasFDerivAt, hc.hasFDerivAt.clm_apply, hu.hasFDerivAt
-/
theorem fderiv_clm_apply (hc : DifferentiableAt 𝕜 c x) (hu : DifferentiableAt 𝕜 u x) :
    fderiv 𝕜 (fun y => (c y) (u y)) x = (c x).comp (fderiv 𝕜 u x) + (fderiv 𝕜 c x).flip (u x) :=
  (hc.hasFDerivAt.clm_apply hu.hasFDerivAt).fderiv

end CLMCompApply

section ContinuousMultilinearApplyConst

/-! ### Derivative of the application of continuous multilinear maps to a constant -/

variable {ι : Type*}
  {M : ι -> Type*} [forall i, NormedAddCommGroup (M i)] [forall i, NormedSpace 𝕜 (M i)]
  {H : Type*} [NormedAddCommGroup H] [NormedSpace 𝕜 H]
  {c : E -> ContinuousMultilinearMap 𝕜 M H}
  {c' : E ->L[𝕜] ContinuousMultilinearMap 𝕜 M H}

section fintype

variable [Fintype ι]

@[fun_prop]
/--
theorem `HasStrictFDerivAt.continuousMultilinear_apply_const` / 定理 `HasStrictFDerivAt.continuousMultilinear_apply_const`

English:
theorem HasStrictFDerivAt.continuousMultilinear_apply_const
  statement: (hc : HasStrictFDerivAt c c' x)
  proof: (ContinuousMultilinearMap.apply 𝕜 M H u).hasStrictFDerivAt.comp x hc

@[fun_prop]

中文:
定理 HasStrictFDerivAt.continuousMultilinear_apply_const
  结论: (hc : HasStrictFDerivAt c c' x)
  证明: (ContinuousMultilinearMap.apply 𝕜 M H u).hasStrictFDerivAt.comp x hc

@[fun_prop]

Depends on / 依赖: ContinuousMultilinearMap, ContinuousMultilinearMap.apply, hasStrictFDerivAt, hasStrictFDerivAt.comp
-/
theorem HasStrictFDerivAt.continuousMultilinear_apply_const (hc : HasStrictFDerivAt c c' x)
    (u : forall i, M i) : HasStrictFDerivAt (fun y => (c y) u) (c'.flipMultilinear u) x :=
  (ContinuousMultilinearMap.apply 𝕜 M H u).hasStrictFDerivAt.comp x hc

@[fun_prop]
/--
theorem `HasFDerivWithinAt.continuousMultilinear_apply_const` / 定理 `HasFDerivWithinAt.continuousMultilinear_apply_const`

English:
theorem HasFDerivWithinAt.continuousMultilinear_apply_const
  statement: (hc : HasFDerivWithinAt c c' s x)
  proof: (ContinuousMultilinearMap.apply 𝕜 M H u).hasFDerivAt.comp_hasFDerivWithinAt x hc

@[fun_prop]

中文:
定理 HasFDerivWithinAt.continuousMultilinear_apply_const
  结论: (hc : HasFDerivWithinAt c c' s x)
  证明: (ContinuousMultilinearMap.apply 𝕜 M H u).hasFDerivAt.comp_hasFDerivWithinAt x hc

@[fun_prop]

Depends on / 依赖: ContinuousMultilinearMap, ContinuousMultilinearMap.apply, comp_hasFDerivWithinAt, hasFDerivAt, hasFDerivAt.comp_hasFDerivWithinAt
-/
theorem HasFDerivWithinAt.continuousMultilinear_apply_const (hc : HasFDerivWithinAt c c' s x)
    (u : forall i, M i) :
    HasFDerivWithinAt (fun y => (c y) u) (c'.flipMultilinear u) s x :=
  (ContinuousMultilinearMap.apply 𝕜 M H u).hasFDerivAt.comp_hasFDerivWithinAt x hc

@[fun_prop]
/--
theorem `HasFDerivAt.continuousMultilinear_apply_const` / 定理 `HasFDerivAt.continuousMultilinear_apply_const`

English:
theorem HasFDerivAt.continuousMultilinear_apply_const
  given: (hc : HasFDerivAt c c' x) (u : forall i, M i)
  proof: (ContinuousMultilinearMap.apply 𝕜 M H u).hasFDerivAt.comp x hc

中文:
定理 在点处Fréchet可导.continuousMultilinear_apply_const
  条件: (hc : 在点处Fréchet可导 c c' x) (u : 对任意 i, M i)
  证明: (ContinuousMultilinearMap.apply 𝕜 M H u).hasFDerivAt.comp x hc

Depends on / 依赖: ContinuousMultilinearMap, ContinuousMultilinearMap.apply, hasFDerivAt, hasFDerivAt.comp
-/
theorem HasFDerivAt.continuousMultilinear_apply_const (hc : HasFDerivAt c c' x) (u : forall i, M i) :
    HasFDerivAt (fun y => (c y) u) (c'.flipMultilinear u) x :=
  (ContinuousMultilinearMap.apply 𝕜 M H u).hasFDerivAt.comp x hc

/--
theorem `fderivWithin_continuousMultilinear_apply_const` / 定理 `fderivWithin_continuousMultilinear_apply_const`

English:
theorem fderivWithin_continuousMultilinear_apply_const
  statement: (hxs : UniqueDiffWithinAt 𝕜 s x)
  proof: (hc.hasFDerivWithinAt.continuousMultilinear_apply_const u).fderivWithin hxs

中文:
定理 fderivWithin_continuousMultilinear_apply_const
  结论: (hxs : UniqueDiffWithinAt 𝕜 s x)
  证明: (hc.hasFDerivWithinAt.continuousMultilinear_apply_const u).fderivWithin hxs

Depends on / 依赖: continuousMultilinear_apply_const, fderivWithin, hasFDerivWithinAt, hc.hasFDerivWithinAt.continuousMultilinear_apply_const
-/
theorem fderivWithin_continuousMultilinear_apply_const (hxs : UniqueDiffWithinAt 𝕜 s x)
    (hc : DifferentiableWithinAt 𝕜 c s x) (u : forall i, M i) :
    fderivWithin 𝕜 (fun y => (c y) u) s x = ((fderivWithin 𝕜 c s x).flipMultilinear u) :=
  (hc.hasFDerivWithinAt.continuousMultilinear_apply_const u).fderivWithin hxs

/--
theorem `fderiv_continuousMultilinear_apply_const` / 定理 `fderiv_continuousMultilinear_apply_const`

English:
theorem fderiv_continuousMultilinear_apply_const
  given: (hc : DifferentiableAt 𝕜 c x) (u : forall i, M i)
  proof: (hc.hasFDerivAt.continuousMultilinear_apply_const u).fderiv

中文:
定理 fderiv_continuousMultilinear_apply_const
  条件: (hc : DifferentiableAt 𝕜 c x) (u : 对任意 i, M i)
  证明: (hc.hasFDerivAt.continuousMultilinear_apply_const u).fderiv

Depends on / 依赖: continuousMultilinear_apply_const, fderiv, hasFDerivAt, hc.hasFDerivAt.continuousMultilinear_apply_const
-/
theorem fderiv_continuousMultilinear_apply_const (hc : DifferentiableAt 𝕜 c x) (u : forall i, M i) :
    (fderiv 𝕜 (fun y => (c y) u) x) = (fderiv 𝕜 c x).flipMultilinear u :=
  (hc.hasFDerivAt.continuousMultilinear_apply_const u).fderiv

end fintype

section finite

variable [Finite ι]

@[fun_prop]
/--
theorem `DifferentiableWithinAt.continuousMultilinear_apply_const` / 定理 `DifferentiableWithinAt.continuousMultilinear_apply_const`

English:
theorem DifferentiableWithinAt.continuousMultilinear_apply_const
  proof: have := Fintype.ofFinite ι
  (hc.hasFDerivWithinAt.continuousMultilinear_apply_const u).differentiableWithinAt

@[fun_prop]

中文:
定理 DifferentiableWithinAt.continuousMultilinear_apply_const
  证明: have := Fintype.ofFinite ι
  (hc.hasFDerivWithinAt.continuousMultilinear_apply_const u).differentiableWithinAt

@[fun_prop]

Depends on / 依赖: Fintype, Fintype.ofFinite, continuousMultilinear_apply_const, differentiableWithinAt, hasFDerivWithinAt, hc.hasFDerivWithinAt.continuousMultilinear_apply_const, ofFinite
-/
theorem DifferentiableWithinAt.continuousMultilinear_apply_const
    (hc : DifferentiableWithinAt 𝕜 c s x) (u : forall i, M i) :
    DifferentiableWithinAt 𝕜 (fun y => (c y) u) s x :=
  have := Fintype.ofFinite ι
  (hc.hasFDerivWithinAt.continuousMultilinear_apply_const u).differentiableWithinAt

@[fun_prop]
/--
theorem `DifferentiableAt.continuousMultilinear_apply_const` / 定理 `DifferentiableAt.continuousMultilinear_apply_const`

English:
theorem DifferentiableAt.continuousMultilinear_apply_const
  statement: (hc : DifferentiableAt 𝕜 c x)
  proof: have := Fintype.ofFinite ι
  (hc.hasFDerivAt.continuousMultilinear_apply_const u).differentiableAt

@[fun_prop]

中文:
定理 DifferentiableAt.continuousMultilinear_apply_const
  结论: (hc : DifferentiableAt 𝕜 c x)
  证明: have := Fintype.ofFinite ι
  (hc.hasFDerivAt.continuousMultilinear_apply_const u).differentiableAt

@[fun_prop]

Depends on / 依赖: Fintype, Fintype.ofFinite, continuousMultilinear_apply_const, differentiableAt, hasFDerivAt, hc.hasFDerivAt.continuousMultilinear_apply_const, ofFinite
-/
theorem DifferentiableAt.continuousMultilinear_apply_const (hc : DifferentiableAt 𝕜 c x)
    (u : forall i, M i) :
    DifferentiableAt 𝕜 (fun y => (c y) u) x :=
  have := Fintype.ofFinite ι
  (hc.hasFDerivAt.continuousMultilinear_apply_const u).differentiableAt

@[fun_prop]
/--
theorem `DifferentiableOn.continuousMultilinear_apply_const` / 定理 `DifferentiableOn.continuousMultilinear_apply_const`

English:
theorem DifferentiableOn.continuousMultilinear_apply_const
  statement: (hc : DifferentiableOn 𝕜 c s)
  proof: fun x hx => (hc x hx).continuousMultilinear_apply_const u

@[fun_prop]

中文:
定理 DifferentiableOn.continuousMultilinear_apply_const
  结论: (hc : DifferentiableOn 𝕜 c s)
  证明: fun x hx => (hc x hx).continuousMultilinear_apply_const u

@[fun_prop]

Depends on / 依赖: continuousMultilinear_apply_const
-/
theorem DifferentiableOn.continuousMultilinear_apply_const (hc : DifferentiableOn 𝕜 c s)
    (u : forall i, M i) : DifferentiableOn 𝕜 (fun y => (c y) u) s :=
  fun x hx => (hc x hx).continuousMultilinear_apply_const u

@[fun_prop]
/--
theorem `Differentiable.continuousMultilinear_apply_const` / 定理 `Differentiable.continuousMultilinear_apply_const`

English:
theorem Differentiable.continuousMultilinear_apply_const
  given: (hc : Differentiable 𝕜 c) (u : forall i, M i)
  proof: fun x => (hc x).continuousMultilinear_apply_const u

中文:
定理 可微.continuousMultilinear_apply_const
  条件: (hc : 可微 𝕜 c) (u : 对任意 i, M i)
  证明: fun x => (hc x).continuousMultilinear_apply_const u

Depends on / 依赖: continuousMultilinear_apply_const
-/
theorem Differentiable.continuousMultilinear_apply_const (hc : Differentiable 𝕜 c) (u : forall i, M i) :
    Differentiable 𝕜 fun y => (c y) u := fun x => (hc x).continuousMultilinear_apply_const u

/--
theorem `fderivWithin_continuousMultilinear_apply_const_apply` / 定理 `fderivWithin_continuousMultilinear_apply_const_apply`

English:
theorem fderivWithin_continuousMultilinear_apply_const_apply
  statement: (hxs : UniqueDiffWithinAt 𝕜 s x)
  proof: by
  have := Fintype.ofFinite ι
  simp [fderivWithin_continuousMultilinear_apply_const hxs hc]

中文:
定理 fderivWithin_continuousMultilinear_apply_const_apply
  结论: (hxs : UniqueDiffWithinAt 𝕜 s x)
  证明: by
  have := Fintype.ofFinite ι
  simp [fderivWithin_continuousMultilinear_apply_const hxs hc]

Depends on / 依赖: Fintype, Fintype.ofFinite, fderivWithin_continuousMultilinear_apply_const, ofFinite
-/
theorem fderivWithin_continuousMultilinear_apply_const_apply (hxs : UniqueDiffWithinAt 𝕜 s x)
    (hc : DifferentiableWithinAt 𝕜 c s x) (u : forall i, M i) (m : E) :
    (fderivWithin 𝕜 (fun y => (c y) u) s x) m = (fderivWithin 𝕜 c s x) m u := by
  have := Fintype.ofFinite ι
  simp [fderivWithin_continuousMultilinear_apply_const hxs hc]

/--
theorem `fderiv_continuousMultilinear_apply_const_apply` / 定理 `fderiv_continuousMultilinear_apply_const_apply`

English:
theorem fderiv_continuousMultilinear_apply_const_apply
  statement: (hc : DifferentiableAt 𝕜 c x)
  proof: by
  have := Fintype.ofFinite ι
  simp [fderiv_continuousMultilinear_apply_const hc]

中文:
定理 fderiv_continuousMultilinear_apply_const_apply
  结论: (hc : DifferentiableAt 𝕜 c x)
  证明: by
  have := Fintype.ofFinite ι
  simp [fderiv_continuousMultilinear_apply_const hc]

Depends on / 依赖: Fintype, Fintype.ofFinite, fderiv_continuousMultilinear_apply_const, ofFinite
-/
theorem fderiv_continuousMultilinear_apply_const_apply (hc : DifferentiableAt 𝕜 c x)
    (u : forall i, M i) (m : E) :
    (fderiv 𝕜 (fun y => (c y) u) x) m = (fderiv 𝕜 c x) m u := by
  have := Fintype.ofFinite ι
  simp [fderiv_continuousMultilinear_apply_const hc]

end finite

end ContinuousMultilinearApplyConst

section ContinuousAlternatingMapApplyConst

/-!
### Derivative of the application of continuous alternating maps to a constant

Given a differentiable family of continuous alternating maps `c : E → F [⋀^ι]→L[𝕜] G`
and a tuple of vectors `u : ι → F`,
the derivative of `c x u` as a function of `x` is given by `fun m ↦ c' m u`,
where `c'` is the derivative of `c` at `x`.
-/

variable {ι : Type*} {c : E -> F [⋀^ι]->L[𝕜] G} {c' : E ->L[𝕜] (F [⋀^ι]->L[𝕜] G)}

section fintype

variable [Fintype ι]

@[fun_prop]
/--
theorem `HasStrictFDerivAt.continuousAlternatingMap_apply_const` / 定理 `HasStrictFDerivAt.continuousAlternatingMap_apply_const`

English:
theorem HasStrictFDerivAt.continuousAlternatingMap_apply_const
  statement: (hc : HasStrictFDerivAt c c' x)
  proof: (ContinuousAlternatingMap.apply 𝕜 F G u).hasStrictFDerivAt.comp x hc

@[fun_prop]

中文:
定理 HasStrictFDerivAt.continuousAlternatingMap_apply_const
  结论: (hc : HasStrictFDerivAt c c' x)
  证明: (ContinuousAlternatingMap.apply 𝕜 F G u).hasStrictFDerivAt.comp x hc

@[fun_prop]

Depends on / 依赖: ContinuousAlternatingMap, ContinuousAlternatingMap.apply, hasStrictFDerivAt, hasStrictFDerivAt.comp
-/
theorem HasStrictFDerivAt.continuousAlternatingMap_apply_const (hc : HasStrictFDerivAt c c' x)
    (u : ι -> F) : HasStrictFDerivAt (c · u) (c'.flipAlternating u) x :=
  (ContinuousAlternatingMap.apply 𝕜 F G u).hasStrictFDerivAt.comp x hc

@[fun_prop]
/--
theorem `HasFDerivWithinAt.continuousAlternatingMap_apply_const` / 定理 `HasFDerivWithinAt.continuousAlternatingMap_apply_const`

English:
theorem HasFDerivWithinAt.continuousAlternatingMap_apply_const
  statement: (hc : HasFDerivWithinAt c c' s x)
  proof: (ContinuousAlternatingMap.apply 𝕜 F G u).hasFDerivAt.comp_hasFDerivWithinAt x hc

@[fun_prop]

中文:
定理 HasFDerivWithinAt.continuousAlternatingMap_apply_const
  结论: (hc : HasFDerivWithinAt c c' s x)
  证明: (ContinuousAlternatingMap.apply 𝕜 F G u).hasFDerivAt.comp_hasFDerivWithinAt x hc

@[fun_prop]

Depends on / 依赖: ContinuousAlternatingMap, ContinuousAlternatingMap.apply, comp_hasFDerivWithinAt, hasFDerivAt, hasFDerivAt.comp_hasFDerivWithinAt
-/
theorem HasFDerivWithinAt.continuousAlternatingMap_apply_const (hc : HasFDerivWithinAt c c' s x)
    (u : ι -> F) :
    HasFDerivWithinAt (c · u) (c'.flipAlternating u) s x :=
  (ContinuousAlternatingMap.apply 𝕜 F G u).hasFDerivAt.comp_hasFDerivWithinAt x hc

@[fun_prop]
/--
theorem `HasFDerivAt.continuousAlternatingMap_apply_const` / 定理 `HasFDerivAt.continuousAlternatingMap_apply_const`

English:
theorem HasFDerivAt.continuousAlternatingMap_apply_const
  given: (hc : HasFDerivAt c c' x) (u : ι -> F)
  proof: (ContinuousAlternatingMap.apply 𝕜 F G u).hasFDerivAt.comp x hc

中文:
定理 在点处Fréchet可导.continuousAlternatingMap_apply_const
  条件: (hc : 在点处Fréchet可导 c c' x) (u : ι -> F)
  证明: (ContinuousAlternatingMap.apply 𝕜 F G u).hasFDerivAt.comp x hc

Depends on / 依赖: ContinuousAlternatingMap, ContinuousAlternatingMap.apply, hasFDerivAt, hasFDerivAt.comp
-/
theorem HasFDerivAt.continuousAlternatingMap_apply_const (hc : HasFDerivAt c c' x) (u : ι -> F) :
    HasFDerivAt (fun y => (c y) u) (c'.flipAlternating u) x :=
  (ContinuousAlternatingMap.apply 𝕜 F G u).hasFDerivAt.comp x hc

/--
theorem `fderivWithin_continuousAlternatingMap_apply_const` / 定理 `fderivWithin_continuousAlternatingMap_apply_const`

English:
theorem fderivWithin_continuousAlternatingMap_apply_const
  statement: (hxs : UniqueDiffWithinAt 𝕜 s x)
  proof: (hc.hasFDerivWithinAt.continuousAlternatingMap_apply_const u).fderivWithin hxs

中文:
定理 fderivWithin_continuousAlternatingMap_apply_const
  结论: (hxs : UniqueDiffWithinAt 𝕜 s x)
  证明: (hc.hasFDerivWithinAt.continuousAlternatingMap_apply_const u).fderivWithin hxs

Depends on / 依赖: continuousAlternatingMap_apply_const, fderivWithin, hasFDerivWithinAt, hc.hasFDerivWithinAt.continuousAlternatingMap_apply_const
-/
theorem fderivWithin_continuousAlternatingMap_apply_const (hxs : UniqueDiffWithinAt 𝕜 s x)
    (hc : DifferentiableWithinAt 𝕜 c s x) (u : ι -> F) :
    fderivWithin 𝕜 (fun y => (c y) u) s x = ((fderivWithin 𝕜 c s x).flipAlternating u) :=
  (hc.hasFDerivWithinAt.continuousAlternatingMap_apply_const u).fderivWithin hxs

/--
theorem `fderiv_continuousAlternatingMap_apply_const` / 定理 `fderiv_continuousAlternatingMap_apply_const`

English:
theorem fderiv_continuousAlternatingMap_apply_const
  given: (hc : DifferentiableAt 𝕜 c x) (u : ι -> F)
  proof: (hc.hasFDerivAt.continuousAlternatingMap_apply_const u).fderiv

中文:
定理 fderiv_continuousAlternatingMap_apply_const
  条件: (hc : DifferentiableAt 𝕜 c x) (u : ι -> F)
  证明: (hc.hasFDerivAt.continuousAlternatingMap_apply_const u).fderiv

Depends on / 依赖: continuousAlternatingMap_apply_const, fderiv, hasFDerivAt, hc.hasFDerivAt.continuousAlternatingMap_apply_const
-/
theorem fderiv_continuousAlternatingMap_apply_const (hc : DifferentiableAt 𝕜 c x) (u : ι -> F) :
    (fderiv 𝕜 (fun y => (c y) u) x) = (fderiv 𝕜 c x).flipAlternating u :=
  (hc.hasFDerivAt.continuousAlternatingMap_apply_const u).fderiv

end fintype

section finite

variable [Finite ι]

@[fun_prop]
/--
theorem `DifferentiableWithinAt.continuousAlternatingMap_apply_const` / 定理 `DifferentiableWithinAt.continuousAlternatingMap_apply_const`

English:
theorem DifferentiableWithinAt.continuousAlternatingMap_apply_const
  proof: have := Fintype.ofFinite ι
  (hc.hasFDerivWithinAt.continuousAlternatingMap_apply_const u).differentiableWithinAt

@[fun_prop]

中文:
定理 DifferentiableWithinAt.continuousAlternatingMap_apply_const
  证明: have := Fintype.ofFinite ι
  (hc.hasFDerivWithinAt.continuousAlternatingMap_apply_const u).differentiableWithinAt

@[fun_prop]

Depends on / 依赖: Fintype, Fintype.ofFinite, continuousAlternatingMap_apply_const, differentiableWithinAt, hasFDerivWithinAt, hc.hasFDerivWithinAt.continuousAlternatingMap_apply_const, ofFinite
-/
theorem DifferentiableWithinAt.continuousAlternatingMap_apply_const
    (hc : DifferentiableWithinAt 𝕜 c s x) (u : ι -> F) :
    DifferentiableWithinAt 𝕜 (fun y => (c y) u) s x :=
  have := Fintype.ofFinite ι
  (hc.hasFDerivWithinAt.continuousAlternatingMap_apply_const u).differentiableWithinAt

@[fun_prop]
/--
theorem `DifferentiableAt.continuousAlternatingMap_apply_const` / 定理 `DifferentiableAt.continuousAlternatingMap_apply_const`

English:
theorem DifferentiableAt.continuousAlternatingMap_apply_const
  statement: (hc : DifferentiableAt 𝕜 c x)
  proof: have := Fintype.ofFinite ι
  (hc.hasFDerivAt.continuousAlternatingMap_apply_const u).differentiableAt

中文:
定理 DifferentiableAt.continuousAlternatingMap_apply_const
  结论: (hc : DifferentiableAt 𝕜 c x)
  证明: have := Fintype.ofFinite ι
  (hc.hasFDerivAt.continuousAlternatingMap_apply_const u).differentiableAt

Depends on / 依赖: Fintype, Fintype.ofFinite, continuousAlternatingMap_apply_const, differentiableAt, hasFDerivAt, hc.hasFDerivAt.continuousAlternatingMap_apply_const, ofFinite
-/
theorem DifferentiableAt.continuousAlternatingMap_apply_const (hc : DifferentiableAt 𝕜 c x)
    (u : ι -> F) :
    DifferentiableAt 𝕜 (fun y => (c y) u) x :=
  have := Fintype.ofFinite ι
  (hc.hasFDerivAt.continuousAlternatingMap_apply_const u).differentiableAt

/--
theorem `fderivWithin_continuousAlternatingMap_apply_const_apply` / 定理 `fderivWithin_continuousAlternatingMap_apply_const_apply`

English:
theorem fderivWithin_continuousAlternatingMap_apply_const_apply
  statement: (hxs : UniqueDiffWithinAt 𝕜 s x)
  proof: by
  have := Fintype.ofFinite ι
  simp [fderivWithin_continuousAlternatingMap_apply_const hxs hc]

中文:
定理 fderivWithin_continuousAlternatingMap_apply_const_apply
  结论: (hxs : UniqueDiffWithinAt 𝕜 s x)
  证明: by
  have := Fintype.ofFinite ι
  simp [fderivWithin_continuousAlternatingMap_apply_const hxs hc]

Depends on / 依赖: Fintype, Fintype.ofFinite, fderivWithin_continuousAlternatingMap_apply_const, ofFinite
-/
theorem fderivWithin_continuousAlternatingMap_apply_const_apply (hxs : UniqueDiffWithinAt 𝕜 s x)
    (hc : DifferentiableWithinAt 𝕜 c s x) (u : ι -> F) (m : E) :
    (fderivWithin 𝕜 (fun y => (c y) u) s x) m = (fderivWithin 𝕜 c s x) m u := by
  have := Fintype.ofFinite ι
  simp [fderivWithin_continuousAlternatingMap_apply_const hxs hc]

/--
theorem `fderiv_continuousAlternatingMap_apply_const_apply` / 定理 `fderiv_continuousAlternatingMap_apply_const_apply`

English:
theorem fderiv_continuousAlternatingMap_apply_const_apply
  statement: (hc : DifferentiableAt 𝕜 c x)
  proof: by
  have := Fintype.ofFinite ι
  simp [fderiv_continuousAlternatingMap_apply_const hc]

@[fun_prop]

中文:
定理 fderiv_continuousAlternatingMap_apply_const_apply
  结论: (hc : DifferentiableAt 𝕜 c x)
  证明: by
  have := Fintype.ofFinite ι
  simp [fderiv_continuousAlternatingMap_apply_const hc]

@[fun_prop]

Depends on / 依赖: Fintype, Fintype.ofFinite, fderiv_continuousAlternatingMap_apply_const, ofFinite
-/
theorem fderiv_continuousAlternatingMap_apply_const_apply (hc : DifferentiableAt 𝕜 c x)
    (u : ι -> F) (m : E) :
    (fderiv 𝕜 (fun y => (c y) u) x) m = (fderiv 𝕜 c x) m u := by
  have := Fintype.ofFinite ι
  simp [fderiv_continuousAlternatingMap_apply_const hc]

@[fun_prop]
/--
theorem `DifferentiableOn.continuousAlternatingMap_apply_const` / 定理 `DifferentiableOn.continuousAlternatingMap_apply_const`

English:
theorem DifferentiableOn.continuousAlternatingMap_apply_const
  statement: (hc : DifferentiableOn 𝕜 c s)
  proof: fun x hx => (hc x hx).continuousAlternatingMap_apply_const u

@[fun_prop]

中文:
定理 DifferentiableOn.continuousAlternatingMap_apply_const
  结论: (hc : DifferentiableOn 𝕜 c s)
  证明: fun x hx => (hc x hx).continuousAlternatingMap_apply_const u

@[fun_prop]

Depends on / 依赖: continuousAlternatingMap_apply_const
-/
theorem DifferentiableOn.continuousAlternatingMap_apply_const (hc : DifferentiableOn 𝕜 c s)
    (u : ι -> F) : DifferentiableOn 𝕜 (fun y => (c y) u) s :=
  fun x hx => (hc x hx).continuousAlternatingMap_apply_const u

@[fun_prop]
/--
theorem `Differentiable.continuousAlternatingMap_apply_const` / 定理 `Differentiable.continuousAlternatingMap_apply_const`

English:
theorem Differentiable.continuousAlternatingMap_apply_const
  given: (hc : Differentiable 𝕜 c) (u : ι -> F)
  proof: fun x => (hc x).continuousAlternatingMap_apply_const u

中文:
定理 可微.continuousAlternatingMap_apply_const
  条件: (hc : 可微 𝕜 c) (u : ι -> F)
  证明: fun x => (hc x).continuousAlternatingMap_apply_const u

Depends on / 依赖: continuousAlternatingMap_apply_const
-/
theorem Differentiable.continuousAlternatingMap_apply_const (hc : Differentiable 𝕜 c) (u : ι -> F) :
    Differentiable 𝕜 fun y => (c y) u := fun x => (hc x).continuousAlternatingMap_apply_const u

end finite

end ContinuousAlternatingMapApplyConst

end
