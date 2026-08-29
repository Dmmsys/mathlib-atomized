/-
Copyright (c) 2019 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Sébastien Gouëzel, Yury Kudryashov
-/
module

public import Mathlib.Analysis.Analytic.Constructions
public import Mathlib.Analysis.Calculus.FDeriv.Analytic
public import Mathlib.Analysis.Calculus.FDeriv.Bilinear

/-!
# Multiplicative operations on derivatives

For detailed documentation of the Fréchet derivative,
see the module docstring of `Mathlib/Analysis/Calculus/FDeriv/Basic.lean`.

This file contains the usual formulas (and existence assertions) for the derivative of

* multiplication of a function by a scalar function
* product of finitely many scalar functions
* taking the pointwise multiplicative inverse (i.e. `Inv.inv` or `Ring.inverse`) of a function
-/

public section

open scoped Ring
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

section SMul

/-! ### Derivative of the product of a scalar-valued function and a vector-valued function

If `c` is a differentiable scalar-valued function and `f` is a differentiable vector-valued
function, then `fun x ↦ c x • f x` is differentiable as well. Lemmas in this section work for
functions `c` taking values in the base field, as well as in a normed algebra over the base
field: e.g., they work for `c : E → ℂ` and `f : E → F` provided that `F` is a complex
normed vector space.
-/


variable {𝕜' : Type*} [NormedRing 𝕜'] [NormedAlgebra 𝕜 𝕜'] [Module 𝕜' F] [IsBoundedSMul 𝕜' F]
  [IsScalarTower 𝕜 𝕜' F]

variable {c : E -> 𝕜'} {c' : E ->L[𝕜] 𝕜'}

@[to_fun (attr := fun_prop)]
/--
theorem `HasStrictFDerivAt.smul` / 定理 `HasStrictFDerivAt.smul`

English:
theorem HasStrictFDerivAt.smul
  given: (hc : HasStrictFDerivAt c c' x) (hf : HasStrictFDerivAt f f' x)
  proof: (isBoundedBilinearMap_smul.hasStrictFDerivAt (c x, f x)).comp x hc.prodMk hf

@[to_fun (attr := fun_prop)]

中文:
定理 HasStrictFDerivAt.smul
  条件: (hc : HasStrictFDerivAt c c' x) (hf : HasStrictFDerivAt f f' x)
  证明: (isBoundedBilinearMap_smul.hasStrictFDerivAt (c x, f x)).comp x hc.prodMk hf

@[to_fun (attr := fun_prop)]

Depends on / 依赖: hasStrictFDerivAt, hc.prodMk, isBoundedBilinearMap_smul, isBoundedBilinearMap_smul.hasStrictFDerivAt, prodMk
-/
theorem HasStrictFDerivAt.smul (hc : HasStrictFDerivAt c c' x) (hf : HasStrictFDerivAt f f' x) :
    HasStrictFDerivAt (c • f) (c x • f' + c'.smulRight (f x)) x :=
(isBoundedBilinearMap_smul.hasStrictFDerivAt (c x, f x)).comp x hc.prodMk hf

@[to_fun (attr := fun_prop)]
/--
theorem `HasFDerivWithinAt.smul` / 定理 `HasFDerivWithinAt.smul`

English:
theorem HasFDerivWithinAt.smul
  proof: by
  -- `by exact` to solve unification issues.
exact (isBoundedBilinearMap_smul.hasFDerivAt (𝕜 := 𝕜) (c x, f x)).comp_hasFDerivWithinAt x
    hc.prodMk hf

@[to_fun (attr := fun_prop)]

中文:
定理 HasFDerivWithinAt.smul
  证明: by
  -- `by exact` to solve unification issues.
exact (isBoundedBilinearMap_smul.hasFDerivAt (𝕜 := 𝕜) (c x, f x)).comp_hasFDerivWithinAt x
    hc.prodMk hf

@[to_fun (attr := fun_prop)]
-/
theorem HasFDerivWithinAt.smul
    (hc : HasFDerivWithinAt c c' s x) (hf : HasFDerivWithinAt f f' s x) :
    HasFDerivWithinAt (c • f) (c x • f' + c'.smulRight (f x)) s x := by
  -- `by exact` to solve unification issues.
exact (isBoundedBilinearMap_smul.hasFDerivAt (𝕜 := 𝕜) (c x, f x)).comp_hasFDerivWithinAt x
    hc.prodMk hf

@[to_fun (attr := fun_prop)]
/--
theorem `HasFDerivAt.smul` / 定理 `HasFDerivAt.smul`

English:
theorem HasFDerivAt.smul
  given: (hc : HasFDerivAt c c' x) (hf : HasFDerivAt f f' x)
  proof: by
  -- `by exact` to solve unification issues.
exact (isBoundedBilinearMap_smul.hasFDerivAt (𝕜 := 𝕜) (c x, f x)).comp x hc.prodMk hf

@[to_fun (attr := fun_prop)]

中文:
定理 HasFDerivAt.smul
  条件: (hc : HasFDerivAt c c' x) (hf : HasFDerivAt f f' x)
  证明: by
  -- `by exact` to solve unification issues.
exact (isBoundedBilinearMap_smul.hasFDerivAt (𝕜 := 𝕜) (c x, f x)).comp x hc.prodMk hf

@[to_fun (attr := fun_prop)]
-/
theorem HasFDerivAt.smul (hc : HasFDerivAt c c' x) (hf : HasFDerivAt f f' x) :
    HasFDerivAt (c • f) (c x • f' + c'.smulRight (f x)) x := by
  -- `by exact` to solve unification issues.
exact (isBoundedBilinearMap_smul.hasFDerivAt (𝕜 := 𝕜) (c x, f x)).comp x hc.prodMk hf

@[to_fun (attr := fun_prop)]
/--
theorem `DifferentiableWithinAt.smul` / 定理 `DifferentiableWithinAt.smul`

English:
theorem DifferentiableWithinAt.smul
  statement: (hc : DifferentiableWithinAt 𝕜 c s x)
  proof: (hc.hasFDerivWithinAt.smul hf.hasFDerivWithinAt).differentiableWithinAt

@[to_fun (attr := simp, fun_prop)]

中文:
定理 DifferentiableWithinAt.smul
  结论: (hc : DifferentiableWithinAt 𝕜 c s x)
  证明: (hc.hasFDerivWithinAt.smul hf.hasFDerivWithinAt).differentiableWithinAt

@[to_fun (attr := simp, fun_prop)]

Depends on / 依赖: differentiableWithinAt, hasFDerivWithinAt, hc.hasFDerivWithinAt.smul, hf.hasFDerivWithinAt
-/
theorem DifferentiableWithinAt.smul (hc : DifferentiableWithinAt 𝕜 c s x)
    (hf : DifferentiableWithinAt 𝕜 f s x) : DifferentiableWithinAt 𝕜 (c • f) s x :=
  (hc.hasFDerivWithinAt.smul hf.hasFDerivWithinAt).differentiableWithinAt

@[to_fun (attr := simp, fun_prop)]
/--
theorem `DifferentiableAt.smul` / 定理 `DifferentiableAt.smul`

English:
theorem DifferentiableAt.smul
  given: (hc : DifferentiableAt 𝕜 c x) (hf : DifferentiableAt 𝕜 f x)
  proof: (hc.hasFDerivAt.smul hf.hasFDerivAt).differentiableAt

@[to_fun (attr := fun_prop)]

中文:
定理 DifferentiableAt.smul
  条件: (hc : DifferentiableAt 𝕜 c x) (hf : DifferentiableAt 𝕜 f x)
  证明: (hc.hasFDerivAt.smul hf.hasFDerivAt).differentiableAt

@[to_fun (attr := fun_prop)]

Depends on / 依赖: differentiableAt, hasFDerivAt, hc.hasFDerivAt.smul, hf.hasFDerivAt
-/
theorem DifferentiableAt.smul (hc : DifferentiableAt 𝕜 c x) (hf : DifferentiableAt 𝕜 f x) :
    DifferentiableAt 𝕜 (c • f) x :=
  (hc.hasFDerivAt.smul hf.hasFDerivAt).differentiableAt

@[to_fun (attr := fun_prop)]
/--
theorem `DifferentiableOn.smul` / 定理 `DifferentiableOn.smul`

English:
theorem DifferentiableOn.smul
  given: (hc : DifferentiableOn 𝕜 c s) (hf : DifferentiableOn 𝕜 f s)
  proof: fun x hx => (hc x hx).smul (hf x hx)

@[to_fun (attr := simp, fun_prop)]

中文:
定理 DifferentiableOn.smul
  条件: (hc : DifferentiableOn 𝕜 c s) (hf : DifferentiableOn 𝕜 f s)
  证明: fun x hx => (hc x hx).smul (hf x hx)

@[to_fun (attr := simp, fun_prop)]
-/
theorem DifferentiableOn.smul (hc : DifferentiableOn 𝕜 c s) (hf : DifferentiableOn 𝕜 f s) :
    DifferentiableOn 𝕜 (c • f) s := fun x hx => (hc x hx).smul (hf x hx)

@[to_fun (attr := simp, fun_prop)]
/--
theorem `Differentiable.smul` / 定理 `Differentiable.smul`

English:
theorem Differentiable.smul
  given: (hc : Differentiable 𝕜 c) (hf : Differentiable 𝕜 f)
  proof: fun x => (hc x).smul (hf x)

中文:
定理 Differentiable.smul
  条件: (hc : Differentiable 𝕜 c) (hf : Differentiable 𝕜 f)
  证明: fun x => (hc x).smul (hf x)
-/
theorem Differentiable.smul (hc : Differentiable 𝕜 c) (hf : Differentiable 𝕜 f) :
    Differentiable 𝕜 (c • f) := fun x => (hc x).smul (hf x)

/--
theorem `fderivWithin_fun_smul` / 定理 `fderivWithin_fun_smul`

English:
theorem fderivWithin_fun_smul
  statement: (hxs : UniqueDiffWithinAt 𝕜 s x) (hc : DifferentiableWithinAt 𝕜 c s x)
  proof: (hc.hasFDerivWithinAt.smul hf.hasFDerivWithinAt).fderivWithin hxs

中文:
定理 fderivWithin_fun_smul
  结论: (hxs : UniqueDiffWithinAt 𝕜 s x) (hc : DifferentiableWithinAt 𝕜 c s x)
  证明: (hc.hasFDerivWithinAt.smul hf.hasFDerivWithinAt).fderivWithin hxs

Depends on / 依赖: fderivWithin, hasFDerivWithinAt, hc.hasFDerivWithinAt.smul, hf.hasFDerivWithinAt
-/
theorem fderivWithin_fun_smul (hxs : UniqueDiffWithinAt 𝕜 s x) (hc : DifferentiableWithinAt 𝕜 c s x)
    (hf : DifferentiableWithinAt 𝕜 f s x) :
    fderivWithin 𝕜 (fun y => c y • f y) s x =
      c x • fderivWithin 𝕜 f s x + (fderivWithin 𝕜 c s x).smulRight (f x) :=
  (hc.hasFDerivWithinAt.smul hf.hasFDerivWithinAt).fderivWithin hxs

/--
theorem `fderivWithin_smul` / 定理 `fderivWithin_smul`

English:
theorem fderivWithin_smul
  statement: (hxs : UniqueDiffWithinAt 𝕜 s x) (hc : DifferentiableWithinAt 𝕜 c s x)
  proof: (hc.hasFDerivWithinAt.smul hf.hasFDerivWithinAt).fderivWithin hxs

中文:
定理 fderivWithin_smul
  结论: (hxs : UniqueDiffWithinAt 𝕜 s x) (hc : DifferentiableWithinAt 𝕜 c s x)
  证明: (hc.hasFDerivWithinAt.smul hf.hasFDerivWithinAt).fderivWithin hxs

Depends on / 依赖: fderivWithin, hasFDerivWithinAt, hc.hasFDerivWithinAt.smul, hf.hasFDerivWithinAt
-/
theorem fderivWithin_smul (hxs : UniqueDiffWithinAt 𝕜 s x) (hc : DifferentiableWithinAt 𝕜 c s x)
    (hf : DifferentiableWithinAt 𝕜 f s x) :
    fderivWithin 𝕜 (c • f) s x =
      c x • fderivWithin 𝕜 f s x + (fderivWithin 𝕜 c s x).smulRight (f x) :=
  (hc.hasFDerivWithinAt.smul hf.hasFDerivWithinAt).fderivWithin hxs

/--
theorem `fderiv_fun_smul` / 定理 `fderiv_fun_smul`

English:
theorem fderiv_fun_smul
  given: (hc : DifferentiableAt 𝕜 c x) (hf : DifferentiableAt 𝕜 f x)
  proof: (hc.hasFDerivAt.smul hf.hasFDerivAt).fderiv

中文:
定理 fderiv_fun_smul
  条件: (hc : DifferentiableAt 𝕜 c x) (hf : DifferentiableAt 𝕜 f x)
  证明: (hc.hasFDerivAt.smul hf.hasFDerivAt).fderiv

Depends on / 依赖: fderiv, hasFDerivAt, hc.hasFDerivAt.smul, hf.hasFDerivAt
-/
theorem fderiv_fun_smul (hc : DifferentiableAt 𝕜 c x) (hf : DifferentiableAt 𝕜 f x) :
    fderiv 𝕜 (fun y => c y • f y) x = c x • fderiv 𝕜 f x + (fderiv 𝕜 c x).smulRight (f x) :=
  (hc.hasFDerivAt.smul hf.hasFDerivAt).fderiv

/--
theorem `fderiv_smul` / 定理 `fderiv_smul`

English:
theorem fderiv_smul
  given: (hc : DifferentiableAt 𝕜 c x) (hf : DifferentiableAt 𝕜 f x)
  proof: (hc.hasFDerivAt.smul hf.hasFDerivAt).fderiv

@[fun_prop]

中文:
定理 fderiv_smul
  条件: (hc : DifferentiableAt 𝕜 c x) (hf : DifferentiableAt 𝕜 f x)
  证明: (hc.hasFDerivAt.smul hf.hasFDerivAt).fderiv

@[fun_prop]

Depends on / 依赖: fderiv, hasFDerivAt, hc.hasFDerivAt.smul, hf.hasFDerivAt
-/
theorem fderiv_smul (hc : DifferentiableAt 𝕜 c x) (hf : DifferentiableAt 𝕜 f x) :
    fderiv 𝕜 (c • f) x = c x • fderiv 𝕜 f x + (fderiv 𝕜 c x).smulRight (f x) :=
  (hc.hasFDerivAt.smul hf.hasFDerivAt).fderiv

@[fun_prop]
/--
theorem `HasStrictFDerivAt.smul_const` / 定理 `HasStrictFDerivAt.smul_const`

English:
theorem HasStrictFDerivAt.smul_const
  given: (hc : HasStrictFDerivAt c c' x) (f : F)
  proof: by
  simpa only [smul_zero, zero_add] using! hc.smul (hasStrictFDerivAt_const f x)

@[fun_prop]

中文:
定理 HasStrictFDerivAt.smul_const
  条件: (hc : HasStrictFDerivAt c c' x) (f : F)
  证明: by
  simpa only [smul_zero, zero_add] using! hc.smul (hasStrictFDerivAt_const f x)

@[fun_prop]

Depends on / 依赖: hasStrictFDerivAt_const, hc.smul, smul_zero, zero_add
-/
theorem HasStrictFDerivAt.smul_const (hc : HasStrictFDerivAt c c' x) (f : F) :
    HasStrictFDerivAt (fun y => c y • f) (c'.smulRight f) x := by
  simpa only [smul_zero, zero_add] using! hc.smul (hasStrictFDerivAt_const f x)

@[fun_prop]
/--
theorem `HasFDerivWithinAt.smul_const` / 定理 `HasFDerivWithinAt.smul_const`

English:
theorem HasFDerivWithinAt.smul_const
  given: (hc : HasFDerivWithinAt c c' s x) (f : F)
  proof: by
  simpa only [smul_zero, zero_add] using! hc.smul (hasFDerivWithinAt_const f x s)

@[fun_prop]

中文:
定理 HasFDerivWithinAt.smul_const
  条件: (hc : HasFDerivWithinAt c c' s x) (f : F)
  证明: by
  simpa only [smul_zero, zero_add] using! hc.smul (hasFDerivWithinAt_const f x s)

@[fun_prop]

Depends on / 依赖: hasFDerivWithinAt_const, hc.smul, smul_zero, zero_add
-/
theorem HasFDerivWithinAt.smul_const (hc : HasFDerivWithinAt c c' s x) (f : F) :
    HasFDerivWithinAt (fun y => c y • f) (c'.smulRight f) s x := by
  simpa only [smul_zero, zero_add] using! hc.smul (hasFDerivWithinAt_const f x s)

@[fun_prop]
/--
theorem `HasFDerivAt.smul_const` / 定理 `HasFDerivAt.smul_const`

English:
theorem HasFDerivAt.smul_const
  given: (hc : HasFDerivAt c c' x) (f : F)
  proof: by
  simpa only [smul_zero, zero_add] using! hc.smul (hasFDerivAt_const f x)

@[fun_prop]

中文:
定理 HasFDerivAt.smul_const
  条件: (hc : HasFDerivAt c c' x) (f : F)
  证明: by
  simpa only [smul_zero, zero_add] using! hc.smul (hasFDerivAt_const f x)

@[fun_prop]

Depends on / 依赖: hasFDerivAt_const, hc.smul, smul_zero, zero_add
-/
theorem HasFDerivAt.smul_const (hc : HasFDerivAt c c' x) (f : F) :
    HasFDerivAt (fun y => c y • f) (c'.smulRight f) x := by
  simpa only [smul_zero, zero_add] using! hc.smul (hasFDerivAt_const f x)

@[fun_prop]
/--
theorem `DifferentiableWithinAt.smul_const` / 定理 `DifferentiableWithinAt.smul_const`

English:
theorem DifferentiableWithinAt.smul_const
  given: (hc : DifferentiableWithinAt 𝕜 c s x) (f : F)
  proof: (hc.hasFDerivWithinAt.smul_const f).differentiableWithinAt

@[fun_prop]

中文:
定理 DifferentiableWithinAt.smul_const
  条件: (hc : DifferentiableWithinAt 𝕜 c s x) (f : F)
  证明: (hc.hasFDerivWithinAt.smul_const f).differentiableWithinAt

@[fun_prop]

Depends on / 依赖: differentiableWithinAt, hasFDerivWithinAt, hc.hasFDerivWithinAt.smul_const, smul_const
-/
theorem DifferentiableWithinAt.smul_const (hc : DifferentiableWithinAt 𝕜 c s x) (f : F) :
    DifferentiableWithinAt 𝕜 (fun y => c y • f) s x :=
  (hc.hasFDerivWithinAt.smul_const f).differentiableWithinAt

@[fun_prop]
/--
theorem `DifferentiableAt.smul_const` / 定理 `DifferentiableAt.smul_const`

English:
theorem DifferentiableAt.smul_const
  given: (hc : DifferentiableAt 𝕜 c x) (f : F)
  proof: (hc.hasFDerivAt.smul_const f).differentiableAt

@[fun_prop]

中文:
定理 DifferentiableAt.smul_const
  条件: (hc : DifferentiableAt 𝕜 c x) (f : F)
  证明: (hc.hasFDerivAt.smul_const f).differentiableAt

@[fun_prop]

Depends on / 依赖: differentiableAt, hasFDerivAt, hc.hasFDerivAt.smul_const, smul_const
-/
theorem DifferentiableAt.smul_const (hc : DifferentiableAt 𝕜 c x) (f : F) :
    DifferentiableAt 𝕜 (fun y => c y • f) x :=
  (hc.hasFDerivAt.smul_const f).differentiableAt

@[fun_prop]
/--
theorem `DifferentiableOn.smul_const` / 定理 `DifferentiableOn.smul_const`

English:
theorem DifferentiableOn.smul_const
  given: (hc : DifferentiableOn 𝕜 c s) (f : F)
  proof: fun x hx => (hc x hx).smul_const f

@[fun_prop]

中文:
定理 DifferentiableOn.smul_const
  条件: (hc : DifferentiableOn 𝕜 c s) (f : F)
  证明: fun x hx => (hc x hx).smul_const f

@[fun_prop]

Depends on / 依赖: smul_const
-/
theorem DifferentiableOn.smul_const (hc : DifferentiableOn 𝕜 c s) (f : F) :
    DifferentiableOn 𝕜 (fun y => c y • f) s := fun x hx => (hc x hx).smul_const f

@[fun_prop]
/--
theorem `Differentiable.smul_const` / 定理 `Differentiable.smul_const`

English:
theorem Differentiable.smul_const
  given: (hc : Differentiable 𝕜 c) (f : F)
  proof: fun x => (hc x).smul_const f

中文:
定理 Differentiable.smul_const
  条件: (hc : Differentiable 𝕜 c) (f : F)
  证明: fun x => (hc x).smul_const f

Depends on / 依赖: smul_const
-/
theorem Differentiable.smul_const (hc : Differentiable 𝕜 c) (f : F) :
    Differentiable 𝕜 fun y => c y • f := fun x => (hc x).smul_const f

/--
theorem `fderivWithin_smul_const` / 定理 `fderivWithin_smul_const`

English:
theorem fderivWithin_smul_const
  statement: (hxs : UniqueDiffWithinAt 𝕜 s x)
  proof: (hc.hasFDerivWithinAt.smul_const f).fderivWithin hxs

中文:
定理 fderivWithin_smul_const
  结论: (hxs : UniqueDiffWithinAt 𝕜 s x)
  证明: (hc.hasFDerivWithinAt.smul_const f).fderivWithin hxs

Depends on / 依赖: fderivWithin, hasFDerivWithinAt, hc.hasFDerivWithinAt.smul_const, smul_const
-/
theorem fderivWithin_smul_const (hxs : UniqueDiffWithinAt 𝕜 s x)
    (hc : DifferentiableWithinAt 𝕜 c s x) (f : F) :
    fderivWithin 𝕜 (fun y => c y • f) s x = (fderivWithin 𝕜 c s x).smulRight f :=
  (hc.hasFDerivWithinAt.smul_const f).fderivWithin hxs

/--
theorem `fderiv_smul_const` / 定理 `fderiv_smul_const`

English:
theorem fderiv_smul_const
  given: (hc : DifferentiableAt 𝕜 c x) (f : F)
  proof: (hc.hasFDerivAt.smul_const f).fderiv

中文:
定理 fderiv_smul_const
  条件: (hc : DifferentiableAt 𝕜 c x) (f : F)
  证明: (hc.hasFDerivAt.smul_const f).fderiv

Depends on / 依赖: fderiv, hasFDerivAt, hc.hasFDerivAt.smul_const, smul_const
-/
theorem fderiv_smul_const (hc : DifferentiableAt 𝕜 c x) (f : F) :
    fderiv 𝕜 (fun y => c y • f) x = (fderiv 𝕜 c x).smulRight f :=
  (hc.hasFDerivAt.smul_const f).fderiv

end SMul

section Mul

/-! ### Derivative of the product of two functions -/

open scoped RightActions


variable {𝔸 𝔸' : Type*} [NormedRing 𝔸] [NormedCommRing 𝔸'] [NormedAlgebra 𝕜 𝔸] [NormedAlgebra 𝕜 𝔸']
  {a b : E -> 𝔸} {a' b' : E ->L[𝕜] 𝔸} {c d : E -> 𝔸'} {c' d' : E ->L[𝕜] 𝔸'}

@[to_fun (attr := fun_prop)]
/--
theorem `HasStrictFDerivAt.mul'` / 定理 `HasStrictFDerivAt.mul'`

English:
theorem HasStrictFDerivAt.mul'
  statement: {x : E} (ha : HasStrictFDerivAt a a' x)
  proof: ((ContinuousLinearMap.mul 𝕜 𝔸).isBoundedBilinearMap.hasStrictFDerivAt (a x, b x)).comp x
    (ha.prodMk hb)

@[to_fun (attr := fun_prop)]

中文:
定理 HasStrictFDerivAt.mul'
  结论: {x : E} (ha : HasStrictFDerivAt a a' x)
  证明: ((ContinuousLinearMap.mul 𝕜 𝔸).isBoundedBilinearMap.hasStrictFDerivAt (a x, b x)).comp x
    (ha.prodMk hb)

@[to_fun (attr := fun_prop)]

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.mul, ha.prodMk, hasStrictFDerivAt, isBoundedBilinearMap, isBoundedBilinearMap.hasStrictFDerivAt, prodMk
-/
theorem HasStrictFDerivAt.mul' {x : E} (ha : HasStrictFDerivAt a a' x)
    (hb : HasStrictFDerivAt b b' x) :
    HasStrictFDerivAt (a * b) (a x • b' + a' <• b x) x :=
  ((ContinuousLinearMap.mul 𝕜 𝔸).isBoundedBilinearMap.hasStrictFDerivAt (a x, b x)).comp x
    (ha.prodMk hb)

@[to_fun (attr := fun_prop)]
/--
theorem `HasStrictFDerivAt.mul` / 定理 `HasStrictFDerivAt.mul`

English:
theorem HasStrictFDerivAt.mul
  given: (hc : HasStrictFDerivAt c c' x) (hd : HasStrictFDerivAt d d' x)
  proof: by
  convert! hc.mul' hd
  ext z
  apply mul_comm

@[to_fun (attr := fun_prop)]

中文:
定理 HasStrictFDerivAt.mul
  条件: (hc : HasStrictFDerivAt c c' x) (hd : HasStrictFDerivAt d d' x)
  证明: by
  convert! hc.mul' hd
  ext z
  apply mul_comm

@[to_fun (attr := fun_prop)]

Depends on / 依赖: convert, hc.mul, mul_comm
-/
theorem HasStrictFDerivAt.mul (hc : HasStrictFDerivAt c c' x) (hd : HasStrictFDerivAt d d' x) :
    HasStrictFDerivAt (c * d) (c x • d' + d x • c') x := by
  convert! hc.mul' hd
  ext z
  apply mul_comm

@[to_fun (attr := fun_prop)]
/--
theorem `HasFDerivWithinAt.mul'` / 定理 `HasFDerivWithinAt.mul'`

English:
theorem HasFDerivWithinAt.mul'
  given: (ha : HasFDerivWithinAt a a' s x) (hb : HasFDerivWithinAt b b' s x)
  proof: by
  -- `by exact` to solve unification issues.
  exact ((ContinuousLinearMap.mul 𝕜 𝔸).isBoundedBilinearMap.hasFDerivAt
    (a x, b x)).comp_hasFDerivWithinAt x (ha.prodMk hb)

@[to_fun (attr := fun_prop)]

中文:
定理 HasFDerivWithinAt.mul'
  条件: (ha : HasFDerivWithinAt a a' s x) (hb : HasFDerivWithinAt b b' s x)
  证明: by
  -- `by exact` to solve unification issues.
  exact ((ContinuousLinearMap.mul 𝕜 𝔸).isBoundedBilinearMap.hasFDerivAt
    (a x, b x)).comp_hasFDerivWithinAt x (ha.prodMk hb)

@[to_fun (attr := fun_prop)]
-/
theorem HasFDerivWithinAt.mul' (ha : HasFDerivWithinAt a a' s x) (hb : HasFDerivWithinAt b b' s x) :
    HasFDerivWithinAt (a * b) (a x • b' + a' <• b x) s x := by
  -- `by exact` to solve unification issues.
  exact ((ContinuousLinearMap.mul 𝕜 𝔸).isBoundedBilinearMap.hasFDerivAt
    (a x, b x)).comp_hasFDerivWithinAt x (ha.prodMk hb)

@[to_fun (attr := fun_prop)]
/--
theorem `HasFDerivWithinAt.mul` / 定理 `HasFDerivWithinAt.mul`

English:
theorem HasFDerivWithinAt.mul
  given: (hc : HasFDerivWithinAt c c' s x) (hd : HasFDerivWithinAt d d' s x)
  proof: by
  convert! hc.mul' hd
  ext z
  apply mul_comm

@[to_fun (attr := fun_prop)]

中文:
定理 HasFDerivWithinAt.mul
  条件: (hc : HasFDerivWithinAt c c' s x) (hd : HasFDerivWithinAt d d' s x)
  证明: by
  convert! hc.mul' hd
  ext z
  apply mul_comm

@[to_fun (attr := fun_prop)]

Depends on / 依赖: convert, hc.mul, mul_comm
-/
theorem HasFDerivWithinAt.mul (hc : HasFDerivWithinAt c c' s x) (hd : HasFDerivWithinAt d d' s x) :
    HasFDerivWithinAt (c * d) (c x • d' + d x • c') s x := by
  convert! hc.mul' hd
  ext z
  apply mul_comm

@[to_fun (attr := fun_prop)]
/--
theorem `HasFDerivAt.mul'` / 定理 `HasFDerivAt.mul'`

English:
theorem HasFDerivAt.mul'
  given: (ha : HasFDerivAt a a' x) (hb : HasFDerivAt b b' x)
  proof: by
  -- `by exact` to solve unification issues.
  exact ((ContinuousLinearMap.mul 𝕜 𝔸).isBoundedBilinearMap.hasFDerivAt
    (a x, b x)).comp x (ha.prodMk hb)

@[to_fun (attr := fun_prop)]

中文:
定理 HasFDerivAt.mul'
  条件: (ha : HasFDerivAt a a' x) (hb : HasFDerivAt b b' x)
  证明: by
  -- `by exact` to solve unification issues.
  exact ((ContinuousLinearMap.mul 𝕜 𝔸).isBoundedBilinearMap.hasFDerivAt
    (a x, b x)).comp x (ha.prodMk hb)

@[to_fun (attr := fun_prop)]
-/
theorem HasFDerivAt.mul' (ha : HasFDerivAt a a' x) (hb : HasFDerivAt b b' x) :
    HasFDerivAt (a * b) (a x • b' + a' <• b x) x := by
  -- `by exact` to solve unification issues.
  exact ((ContinuousLinearMap.mul 𝕜 𝔸).isBoundedBilinearMap.hasFDerivAt
    (a x, b x)).comp x (ha.prodMk hb)

@[to_fun (attr := fun_prop)]
/--
theorem `HasFDerivAt.mul` / 定理 `HasFDerivAt.mul`

English:
theorem HasFDerivAt.mul
  given: (hc : HasFDerivAt c c' x) (hd : HasFDerivAt d d' x)
  proof: by
  convert! hc.mul' hd
  ext z
  apply mul_comm

@[to_fun (attr := fun_prop)]

中文:
定理 HasFDerivAt.mul
  条件: (hc : HasFDerivAt c c' x) (hd : HasFDerivAt d d' x)
  证明: by
  convert! hc.mul' hd
  ext z
  apply mul_comm

@[to_fun (attr := fun_prop)]

Depends on / 依赖: convert, hc.mul, mul_comm
-/
theorem HasFDerivAt.mul (hc : HasFDerivAt c c' x) (hd : HasFDerivAt d d' x) :
    HasFDerivAt (c * d) (c x • d' + d x • c') x := by
  convert! hc.mul' hd
  ext z
  apply mul_comm

@[to_fun (attr := fun_prop)]
/--
theorem `DifferentiableWithinAt.mul` / 定理 `DifferentiableWithinAt.mul`

English:
theorem DifferentiableWithinAt.mul
  statement: (ha : DifferentiableWithinAt 𝕜 a s x)
  proof: (ha.hasFDerivWithinAt.mul' hb.hasFDerivWithinAt).differentiableWithinAt

@[to_fun (attr := simp, fun_prop)]

中文:
定理 DifferentiableWithinAt.mul
  结论: (ha : DifferentiableWithinAt 𝕜 a s x)
  证明: (ha.hasFDerivWithinAt.mul' hb.hasFDerivWithinAt).differentiableWithinAt

@[to_fun (attr := simp, fun_prop)]

Depends on / 依赖: differentiableWithinAt, ha.hasFDerivWithinAt.mul, hasFDerivWithinAt, hb.hasFDerivWithinAt
-/
theorem DifferentiableWithinAt.mul (ha : DifferentiableWithinAt 𝕜 a s x)
    (hb : DifferentiableWithinAt 𝕜 b s x) : DifferentiableWithinAt 𝕜 (a * b) s x :=
  (ha.hasFDerivWithinAt.mul' hb.hasFDerivWithinAt).differentiableWithinAt

@[to_fun (attr := simp, fun_prop)]
/--
theorem `DifferentiableAt.mul` / 定理 `DifferentiableAt.mul`

English:
theorem DifferentiableAt.mul
  given: (ha : DifferentiableAt 𝕜 a x) (hb : DifferentiableAt 𝕜 b x)
  proof: (ha.hasFDerivAt.mul' hb.hasFDerivAt).differentiableAt

@[to_fun (attr := fun_prop)]

中文:
定理 DifferentiableAt.mul
  条件: (ha : DifferentiableAt 𝕜 a x) (hb : DifferentiableAt 𝕜 b x)
  证明: (ha.hasFDerivAt.mul' hb.hasFDerivAt).differentiableAt

@[to_fun (attr := fun_prop)]

Depends on / 依赖: differentiableAt, ha.hasFDerivAt.mul, hasFDerivAt, hb.hasFDerivAt
-/
theorem DifferentiableAt.mul (ha : DifferentiableAt 𝕜 a x) (hb : DifferentiableAt 𝕜 b x) :
    DifferentiableAt 𝕜 (a * b) x :=
  (ha.hasFDerivAt.mul' hb.hasFDerivAt).differentiableAt

@[to_fun (attr := fun_prop)]
/--
theorem `DifferentiableOn.mul` / 定理 `DifferentiableOn.mul`

English:
theorem DifferentiableOn.mul
  given: (ha : DifferentiableOn 𝕜 a s) (hb : DifferentiableOn 𝕜 b s)
  proof: fun x hx => (ha x hx).mul (hb x hx)

@[to_fun (attr := simp, fun_prop)]

中文:
定理 DifferentiableOn.mul
  条件: (ha : DifferentiableOn 𝕜 a s) (hb : DifferentiableOn 𝕜 b s)
  证明: fun x hx => (ha x hx).mul (hb x hx)

@[to_fun (attr := simp, fun_prop)]
-/
theorem DifferentiableOn.mul (ha : DifferentiableOn 𝕜 a s) (hb : DifferentiableOn 𝕜 b s) :
    DifferentiableOn 𝕜 (a * b) s := fun x hx => (ha x hx).mul (hb x hx)

@[to_fun (attr := simp, fun_prop)]
/--
theorem `Differentiable.mul` / 定理 `Differentiable.mul`

English:
theorem Differentiable.mul
  given: (ha : Differentiable 𝕜 a) (hb : Differentiable 𝕜 b)
  proof: fun x => (ha x).mul (hb x)

中文:
定理 Differentiable.mul
  条件: (ha : Differentiable 𝕜 a) (hb : Differentiable 𝕜 b)
  证明: fun x => (ha x).mul (hb x)
-/
theorem Differentiable.mul (ha : Differentiable 𝕜 a) (hb : Differentiable 𝕜 b) :
    Differentiable 𝕜 (a * b) := fun x => (ha x).mul (hb x)

/--
theorem `fderivWithin_fun_mul'` / 定理 `fderivWithin_fun_mul'`

English:
theorem fderivWithin_fun_mul'
  statement: (hxs : UniqueDiffWithinAt 𝕜 s x) (ha : DifferentiableWithinAt 𝕜 a s x)
  proof: (ha.hasFDerivWithinAt.mul' hb.hasFDerivWithinAt).fderivWithin hxs

中文:
定理 fderivWithin_fun_mul'
  结论: (hxs : UniqueDiffWithinAt 𝕜 s x) (ha : DifferentiableWithinAt 𝕜 a s x)
  证明: (ha.hasFDerivWithinAt.mul' hb.hasFDerivWithinAt).fderivWithin hxs

Depends on / 依赖: fderivWithin, ha.hasFDerivWithinAt.mul, hasFDerivWithinAt, hb.hasFDerivWithinAt
-/
theorem fderivWithin_fun_mul' (hxs : UniqueDiffWithinAt 𝕜 s x) (ha : DifferentiableWithinAt 𝕜 a s x)
    (hb : DifferentiableWithinAt 𝕜 b s x) :
    fderivWithin 𝕜 (fun y => a y * b y) s x =
      a x • fderivWithin 𝕜 b s x + fderivWithin 𝕜 a s x <• b x :=
  (ha.hasFDerivWithinAt.mul' hb.hasFDerivWithinAt).fderivWithin hxs

/--
theorem `fderivWithin_mul'` / 定理 `fderivWithin_mul'`

English:
theorem fderivWithin_mul'
  statement: (hxs : UniqueDiffWithinAt 𝕜 s x) (ha : DifferentiableWithinAt 𝕜 a s x)
  proof: (ha.hasFDerivWithinAt.mul' hb.hasFDerivWithinAt).fderivWithin hxs

中文:
定理 fderivWithin_mul'
  结论: (hxs : UniqueDiffWithinAt 𝕜 s x) (ha : DifferentiableWithinAt 𝕜 a s x)
  证明: (ha.hasFDerivWithinAt.mul' hb.hasFDerivWithinAt).fderivWithin hxs

Depends on / 依赖: fderivWithin, ha.hasFDerivWithinAt.mul, hasFDerivWithinAt, hb.hasFDerivWithinAt
-/
theorem fderivWithin_mul' (hxs : UniqueDiffWithinAt 𝕜 s x) (ha : DifferentiableWithinAt 𝕜 a s x)
    (hb : DifferentiableWithinAt 𝕜 b s x) :
    fderivWithin 𝕜 (a * b) s x =
      a x • fderivWithin 𝕜 b s x + fderivWithin 𝕜 a s x <• b x :=
  (ha.hasFDerivWithinAt.mul' hb.hasFDerivWithinAt).fderivWithin hxs

/--
theorem `fderivWithin_fun_mul` / 定理 `fderivWithin_fun_mul`

English:
theorem fderivWithin_fun_mul
  statement: (hxs : UniqueDiffWithinAt 𝕜 s x) (hc : DifferentiableWithinAt 𝕜 c s x)
  proof: (hc.hasFDerivWithinAt.mul hd.hasFDerivWithinAt).fderivWithin hxs

中文:
定理 fderivWithin_fun_mul
  结论: (hxs : UniqueDiffWithinAt 𝕜 s x) (hc : DifferentiableWithinAt 𝕜 c s x)
  证明: (hc.hasFDerivWithinAt.mul hd.hasFDerivWithinAt).fderivWithin hxs

Depends on / 依赖: fderivWithin, hasFDerivWithinAt, hc.hasFDerivWithinAt.mul, hd.hasFDerivWithinAt
-/
theorem fderivWithin_fun_mul (hxs : UniqueDiffWithinAt 𝕜 s x) (hc : DifferentiableWithinAt 𝕜 c s x)
    (hd : DifferentiableWithinAt 𝕜 d s x) :
    fderivWithin 𝕜 (fun y => c y * d y) s x =
      c x • fderivWithin 𝕜 d s x + d x • fderivWithin 𝕜 c s x :=
  (hc.hasFDerivWithinAt.mul hd.hasFDerivWithinAt).fderivWithin hxs

/--
theorem `fderivWithin_mul` / 定理 `fderivWithin_mul`

English:
theorem fderivWithin_mul
  statement: (hxs : UniqueDiffWithinAt 𝕜 s x) (hc : DifferentiableWithinAt 𝕜 c s x)
  proof: (hc.hasFDerivWithinAt.mul hd.hasFDerivWithinAt).fderivWithin hxs

中文:
定理 fderivWithin_mul
  结论: (hxs : UniqueDiffWithinAt 𝕜 s x) (hc : DifferentiableWithinAt 𝕜 c s x)
  证明: (hc.hasFDerivWithinAt.mul hd.hasFDerivWithinAt).fderivWithin hxs

Depends on / 依赖: fderivWithin, hasFDerivWithinAt, hc.hasFDerivWithinAt.mul, hd.hasFDerivWithinAt
-/
theorem fderivWithin_mul (hxs : UniqueDiffWithinAt 𝕜 s x) (hc : DifferentiableWithinAt 𝕜 c s x)
    (hd : DifferentiableWithinAt 𝕜 d s x) :
    fderivWithin 𝕜 (c * d) s x =
      c x • fderivWithin 𝕜 d s x + d x • fderivWithin 𝕜 c s x :=
  (hc.hasFDerivWithinAt.mul hd.hasFDerivWithinAt).fderivWithin hxs

/--
theorem `fderiv_fun_mul'` / 定理 `fderiv_fun_mul'`

English:
theorem fderiv_fun_mul'
  given: (ha : DifferentiableAt 𝕜 a x) (hb : DifferentiableAt 𝕜 b x)
  proof: (ha.hasFDerivAt.mul' hb.hasFDerivAt).fderiv

中文:
定理 fderiv_fun_mul'
  条件: (ha : DifferentiableAt 𝕜 a x) (hb : DifferentiableAt 𝕜 b x)
  证明: (ha.hasFDerivAt.mul' hb.hasFDerivAt).fderiv

Depends on / 依赖: fderiv, ha.hasFDerivAt.mul, hasFDerivAt, hb.hasFDerivAt
-/
theorem fderiv_fun_mul' (ha : DifferentiableAt 𝕜 a x) (hb : DifferentiableAt 𝕜 b x) :
    fderiv 𝕜 (fun y => a y * b y) x = a x • fderiv 𝕜 b x + fderiv 𝕜 a x <• b x :=
  (ha.hasFDerivAt.mul' hb.hasFDerivAt).fderiv

/--
theorem `fderiv_mul'` / 定理 `fderiv_mul'`

English:
theorem fderiv_mul'
  given: (ha : DifferentiableAt 𝕜 a x) (hb : DifferentiableAt 𝕜 b x)
  proof: (ha.hasFDerivAt.mul' hb.hasFDerivAt).fderiv

中文:
定理 fderiv_mul'
  条件: (ha : DifferentiableAt 𝕜 a x) (hb : DifferentiableAt 𝕜 b x)
  证明: (ha.hasFDerivAt.mul' hb.hasFDerivAt).fderiv

Depends on / 依赖: fderiv, ha.hasFDerivAt.mul, hasFDerivAt, hb.hasFDerivAt
-/
theorem fderiv_mul' (ha : DifferentiableAt 𝕜 a x) (hb : DifferentiableAt 𝕜 b x) :
    fderiv 𝕜 (a * b) x = a x • fderiv 𝕜 b x + fderiv 𝕜 a x <• b x :=
  (ha.hasFDerivAt.mul' hb.hasFDerivAt).fderiv

/--
theorem `fderiv_fun_mul` / 定理 `fderiv_fun_mul`

English:
theorem fderiv_fun_mul
  given: (hc : DifferentiableAt 𝕜 c x) (hd : DifferentiableAt 𝕜 d x)
  proof: (hc.hasFDerivAt.mul hd.hasFDerivAt).fderiv

中文:
定理 fderiv_fun_mul
  条件: (hc : DifferentiableAt 𝕜 c x) (hd : DifferentiableAt 𝕜 d x)
  证明: (hc.hasFDerivAt.mul hd.hasFDerivAt).fderiv

Depends on / 依赖: fderiv, hasFDerivAt, hc.hasFDerivAt.mul, hd.hasFDerivAt
-/
theorem fderiv_fun_mul (hc : DifferentiableAt 𝕜 c x) (hd : DifferentiableAt 𝕜 d x) :
    fderiv 𝕜 (fun y => c y * d y) x = c x • fderiv 𝕜 d x + d x • fderiv 𝕜 c x :=
  (hc.hasFDerivAt.mul hd.hasFDerivAt).fderiv

/--
theorem `fderiv_mul` / 定理 `fderiv_mul`

English:
theorem fderiv_mul
  given: (hc : DifferentiableAt 𝕜 c x) (hd : DifferentiableAt 𝕜 d x)
  proof: (hc.hasFDerivAt.mul hd.hasFDerivAt).fderiv

@[fun_prop]

中文:
定理 fderiv_mul
  条件: (hc : DifferentiableAt 𝕜 c x) (hd : DifferentiableAt 𝕜 d x)
  证明: (hc.hasFDerivAt.mul hd.hasFDerivAt).fderiv

@[fun_prop]

Depends on / 依赖: fderiv, hasFDerivAt, hc.hasFDerivAt.mul, hd.hasFDerivAt
-/
theorem fderiv_mul (hc : DifferentiableAt 𝕜 c x) (hd : DifferentiableAt 𝕜 d x) :
    fderiv 𝕜 (c * d) x = c x • fderiv 𝕜 d x + d x • fderiv 𝕜 c x :=
  (hc.hasFDerivAt.mul hd.hasFDerivAt).fderiv

@[fun_prop]
/--
theorem `HasStrictFDerivAt.mul_const'` / 定理 `HasStrictFDerivAt.mul_const'`

English:
theorem HasStrictFDerivAt.mul_const'
  given: (ha : HasStrictFDerivAt a a' x) (b : 𝔸)
  proof: ((ContinuousLinearMap.mul 𝕜 𝔸).flip b).hasStrictFDerivAt.comp x ha

@[fun_prop]

中文:
定理 HasStrictFDerivAt.mul_const'
  条件: (ha : HasStrictFDerivAt a a' x) (b : 𝔸)
  证明: ((ContinuousLinearMap.mul 𝕜 𝔸).flip b).hasStrictFDerivAt.comp x ha

@[fun_prop]

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.mul, hasStrictFDerivAt, hasStrictFDerivAt.comp
-/
theorem HasStrictFDerivAt.mul_const' (ha : HasStrictFDerivAt a a' x) (b : 𝔸) :
    HasStrictFDerivAt (fun y => a y * b) (a' <• b) x :=
  ((ContinuousLinearMap.mul 𝕜 𝔸).flip b).hasStrictFDerivAt.comp x ha

@[fun_prop]
/--
theorem `HasStrictFDerivAt.mul_const` / 定理 `HasStrictFDerivAt.mul_const`

English:
theorem HasStrictFDerivAt.mul_const
  given: (hc : HasStrictFDerivAt c c' x) (d : 𝔸')
  proof: by
  convert! hc.mul_const' d
  ext z
  apply mul_comm

@[fun_prop]

中文:
定理 HasStrictFDerivAt.mul_const
  条件: (hc : HasStrictFDerivAt c c' x) (d : 𝔸')
  证明: by
  convert! hc.mul_const' d
  ext z
  apply mul_comm

@[fun_prop]

Depends on / 依赖: convert, hc.mul_const, mul_comm, mul_const
-/
theorem HasStrictFDerivAt.mul_const (hc : HasStrictFDerivAt c c' x) (d : 𝔸') :
    HasStrictFDerivAt (fun y => c y * d) (d • c') x := by
  convert! hc.mul_const' d
  ext z
  apply mul_comm

@[fun_prop]
/--
theorem `HasFDerivWithinAt.mul_const'` / 定理 `HasFDerivWithinAt.mul_const'`

English:
theorem HasFDerivWithinAt.mul_const'
  given: (ha : HasFDerivWithinAt a a' s x) (b : 𝔸)
  proof: ((ContinuousLinearMap.mul 𝕜 𝔸).flip b).hasFDerivAt.comp_hasFDerivWithinAt x ha

@[fun_prop]

中文:
定理 HasFDerivWithinAt.mul_const'
  条件: (ha : HasFDerivWithinAt a a' s x) (b : 𝔸)
  证明: ((ContinuousLinearMap.mul 𝕜 𝔸).flip b).hasFDerivAt.comp_hasFDerivWithinAt x ha

@[fun_prop]

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.mul, comp_hasFDerivWithinAt, hasFDerivAt, hasFDerivAt.comp_hasFDerivWithinAt
-/
theorem HasFDerivWithinAt.mul_const' (ha : HasFDerivWithinAt a a' s x) (b : 𝔸) :
    HasFDerivWithinAt (fun y => a y * b) (a' <• b) s x :=
  ((ContinuousLinearMap.mul 𝕜 𝔸).flip b).hasFDerivAt.comp_hasFDerivWithinAt x ha

@[fun_prop]
/--
theorem `HasFDerivWithinAt.mul_const` / 定理 `HasFDerivWithinAt.mul_const`

English:
theorem HasFDerivWithinAt.mul_const
  given: (hc : HasFDerivWithinAt c c' s x) (d : 𝔸')
  proof: by
  convert! hc.mul_const' d
  ext z
  apply mul_comm

@[fun_prop]

中文:
定理 HasFDerivWithinAt.mul_const
  条件: (hc : HasFDerivWithinAt c c' s x) (d : 𝔸')
  证明: by
  convert! hc.mul_const' d
  ext z
  apply mul_comm

@[fun_prop]

Depends on / 依赖: convert, hc.mul_const, mul_comm, mul_const
-/
theorem HasFDerivWithinAt.mul_const (hc : HasFDerivWithinAt c c' s x) (d : 𝔸') :
    HasFDerivWithinAt (fun y => c y * d) (d • c') s x := by
  convert! hc.mul_const' d
  ext z
  apply mul_comm

@[fun_prop]
/--
theorem `HasFDerivAt.mul_const'` / 定理 `HasFDerivAt.mul_const'`

English:
theorem HasFDerivAt.mul_const'
  given: (ha : HasFDerivAt a a' x) (b : 𝔸)
  proof: ((ContinuousLinearMap.mul 𝕜 𝔸).flip b).hasFDerivAt.comp x ha

@[fun_prop]

中文:
定理 HasFDerivAt.mul_const'
  条件: (ha : HasFDerivAt a a' x) (b : 𝔸)
  证明: ((ContinuousLinearMap.mul 𝕜 𝔸).flip b).hasFDerivAt.comp x ha

@[fun_prop]

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.mul, hasFDerivAt, hasFDerivAt.comp
-/
theorem HasFDerivAt.mul_const' (ha : HasFDerivAt a a' x) (b : 𝔸) :
    HasFDerivAt (fun y => a y * b) (a' <• b) x :=
  ((ContinuousLinearMap.mul 𝕜 𝔸).flip b).hasFDerivAt.comp x ha

@[fun_prop]
/--
theorem `HasFDerivAt.mul_const` / 定理 `HasFDerivAt.mul_const`

English:
theorem HasFDerivAt.mul_const
  given: (hc : HasFDerivAt c c' x) (d : 𝔸')
  proof: by
  convert! hc.mul_const' d
  ext z
  apply mul_comm

@[fun_prop]

中文:
定理 HasFDerivAt.mul_const
  条件: (hc : HasFDerivAt c c' x) (d : 𝔸')
  证明: by
  convert! hc.mul_const' d
  ext z
  apply mul_comm

@[fun_prop]

Depends on / 依赖: convert, hc.mul_const, mul_comm, mul_const
-/
theorem HasFDerivAt.mul_const (hc : HasFDerivAt c c' x) (d : 𝔸') :
    HasFDerivAt (fun y => c y * d) (d • c') x := by
  convert! hc.mul_const' d
  ext z
  apply mul_comm

@[fun_prop]
/--
theorem `DifferentiableWithinAt.mul_const` / 定理 `DifferentiableWithinAt.mul_const`

English:
theorem DifferentiableWithinAt.mul_const
  given: (ha : DifferentiableWithinAt 𝕜 a s x) (b : 𝔸)
  proof: (ha.hasFDerivWithinAt.mul_const' b).differentiableWithinAt

@[fun_prop]

中文:
定理 DifferentiableWithinAt.mul_const
  条件: (ha : DifferentiableWithinAt 𝕜 a s x) (b : 𝔸)
  证明: (ha.hasFDerivWithinAt.mul_const' b).differentiableWithinAt

@[fun_prop]

Depends on / 依赖: differentiableWithinAt, ha.hasFDerivWithinAt.mul_const, hasFDerivWithinAt, mul_const
-/
theorem DifferentiableWithinAt.mul_const (ha : DifferentiableWithinAt 𝕜 a s x) (b : 𝔸) :
    DifferentiableWithinAt 𝕜 (fun y => a y * b) s x :=
  (ha.hasFDerivWithinAt.mul_const' b).differentiableWithinAt

@[fun_prop]
/--
theorem `DifferentiableAt.mul_const` / 定理 `DifferentiableAt.mul_const`

English:
theorem DifferentiableAt.mul_const
  given: (ha : DifferentiableAt 𝕜 a x) (b : 𝔸)
  proof: (ha.hasFDerivAt.mul_const' b).differentiableAt

@[fun_prop]

中文:
定理 DifferentiableAt.mul_const
  条件: (ha : DifferentiableAt 𝕜 a x) (b : 𝔸)
  证明: (ha.hasFDerivAt.mul_const' b).differentiableAt

@[fun_prop]

Depends on / 依赖: differentiableAt, ha.hasFDerivAt.mul_const, hasFDerivAt, mul_const
-/
theorem DifferentiableAt.mul_const (ha : DifferentiableAt 𝕜 a x) (b : 𝔸) :
    DifferentiableAt 𝕜 (fun y => a y * b) x :=
  (ha.hasFDerivAt.mul_const' b).differentiableAt

@[fun_prop]
/--
theorem `DifferentiableOn.mul_const` / 定理 `DifferentiableOn.mul_const`

English:
theorem DifferentiableOn.mul_const
  given: (ha : DifferentiableOn 𝕜 a s) (b : 𝔸)
  proof: fun x hx => (ha x hx).mul_const b

@[fun_prop]

中文:
定理 DifferentiableOn.mul_const
  条件: (ha : DifferentiableOn 𝕜 a s) (b : 𝔸)
  证明: fun x hx => (ha x hx).mul_const b

@[fun_prop]

Depends on / 依赖: mul_const
-/
theorem DifferentiableOn.mul_const (ha : DifferentiableOn 𝕜 a s) (b : 𝔸) :
    DifferentiableOn 𝕜 (fun y => a y * b) s := fun x hx => (ha x hx).mul_const b

@[fun_prop]
/--
theorem `Differentiable.mul_const` / 定理 `Differentiable.mul_const`

English:
theorem Differentiable.mul_const
  given: (ha : Differentiable 𝕜 a) (b : 𝔸)
  proof: fun x => (ha x).mul_const b

中文:
定理 Differentiable.mul_const
  条件: (ha : Differentiable 𝕜 a) (b : 𝔸)
  证明: fun x => (ha x).mul_const b

Depends on / 依赖: mul_const
-/
theorem Differentiable.mul_const (ha : Differentiable 𝕜 a) (b : 𝔸) :
    Differentiable 𝕜 fun y => a y * b := fun x => (ha x).mul_const b

/--
theorem `fderivWithin_mul_const'` / 定理 `fderivWithin_mul_const'`

English:
theorem fderivWithin_mul_const'
  statement: (hxs : UniqueDiffWithinAt 𝕜 s x)
  proof: (ha.hasFDerivWithinAt.mul_const' b).fderivWithin hxs

中文:
定理 fderivWithin_mul_const'
  结论: (hxs : UniqueDiffWithinAt 𝕜 s x)
  证明: (ha.hasFDerivWithinAt.mul_const' b).fderivWithin hxs

Depends on / 依赖: fderivWithin, ha.hasFDerivWithinAt.mul_const, hasFDerivWithinAt, mul_const
-/
theorem fderivWithin_mul_const' (hxs : UniqueDiffWithinAt 𝕜 s x)
    (ha : DifferentiableWithinAt 𝕜 a s x) (b : 𝔸) :
    fderivWithin 𝕜 (fun y => a y * b) s x = fderivWithin 𝕜 a s x <• b :=
  (ha.hasFDerivWithinAt.mul_const' b).fderivWithin hxs

/--
theorem `fderivWithin_mul_const` / 定理 `fderivWithin_mul_const`

English:
theorem fderivWithin_mul_const
  statement: (hxs : UniqueDiffWithinAt 𝕜 s x)
  proof: (hc.hasFDerivWithinAt.mul_const d).fderivWithin hxs

中文:
定理 fderivWithin_mul_const
  结论: (hxs : UniqueDiffWithinAt 𝕜 s x)
  证明: (hc.hasFDerivWithinAt.mul_const d).fderivWithin hxs

Depends on / 依赖: fderivWithin, hasFDerivWithinAt, hc.hasFDerivWithinAt.mul_const, mul_const
-/
theorem fderivWithin_mul_const (hxs : UniqueDiffWithinAt 𝕜 s x)
    (hc : DifferentiableWithinAt 𝕜 c s x) (d : 𝔸') :
    fderivWithin 𝕜 (fun y => c y * d) s x = d • fderivWithin 𝕜 c s x :=
  (hc.hasFDerivWithinAt.mul_const d).fderivWithin hxs

/--
theorem `fderiv_mul_const'` / 定理 `fderiv_mul_const'`

English:
theorem fderiv_mul_const'
  given: (ha : DifferentiableAt 𝕜 a x) (b : 𝔸)
  proof: (ha.hasFDerivAt.mul_const' b).fderiv

中文:
定理 fderiv_mul_const'
  条件: (ha : DifferentiableAt 𝕜 a x) (b : 𝔸)
  证明: (ha.hasFDerivAt.mul_const' b).fderiv

Depends on / 依赖: fderiv, ha.hasFDerivAt.mul_const, hasFDerivAt, mul_const
-/
theorem fderiv_mul_const' (ha : DifferentiableAt 𝕜 a x) (b : 𝔸) :
    fderiv 𝕜 (fun y => a y * b) x = fderiv 𝕜 a x <• b :=
  (ha.hasFDerivAt.mul_const' b).fderiv

/--
theorem `fderiv_mul_const` / 定理 `fderiv_mul_const`

English:
theorem fderiv_mul_const
  given: (hc : DifferentiableAt 𝕜 c x) (d : 𝔸')
  proof: (hc.hasFDerivAt.mul_const d).fderiv

@[fun_prop]

中文:
定理 fderiv_mul_const
  条件: (hc : DifferentiableAt 𝕜 c x) (d : 𝔸')
  证明: (hc.hasFDerivAt.mul_const d).fderiv

@[fun_prop]

Depends on / 依赖: fderiv, hasFDerivAt, hc.hasFDerivAt.mul_const, mul_const
-/
theorem fderiv_mul_const (hc : DifferentiableAt 𝕜 c x) (d : 𝔸') :
    fderiv 𝕜 (fun y => c y * d) x = d • fderiv 𝕜 c x :=
  (hc.hasFDerivAt.mul_const d).fderiv

@[fun_prop]
/--
theorem `HasStrictFDerivAt.const_mul` / 定理 `HasStrictFDerivAt.const_mul`

English:
theorem HasStrictFDerivAt.const_mul
  given: (ha : HasStrictFDerivAt a a' x) (b : 𝔸)
  proof: ((ContinuousLinearMap.mul 𝕜 𝔸) b).hasStrictFDerivAt.comp x ha

@[fun_prop]

中文:
定理 HasStrictFDerivAt.const_mul
  条件: (ha : HasStrictFDerivAt a a' x) (b : 𝔸)
  证明: ((ContinuousLinearMap.mul 𝕜 𝔸) b).hasStrictFDerivAt.comp x ha

@[fun_prop]

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.mul, hasStrictFDerivAt, hasStrictFDerivAt.comp
-/
theorem HasStrictFDerivAt.const_mul (ha : HasStrictFDerivAt a a' x) (b : 𝔸) :
    HasStrictFDerivAt (fun y => b * a y) (b • a') x :=
  ((ContinuousLinearMap.mul 𝕜 𝔸) b).hasStrictFDerivAt.comp x ha

@[fun_prop]
/--
theorem `HasFDerivWithinAt.const_mul` / 定理 `HasFDerivWithinAt.const_mul`

English:
theorem HasFDerivWithinAt.const_mul
  given: (ha : HasFDerivWithinAt a a' s x) (b : 𝔸)
  proof: ((ContinuousLinearMap.mul 𝕜 𝔸) b).hasFDerivAt.comp_hasFDerivWithinAt x ha

@[fun_prop]

中文:
定理 HasFDerivWithinAt.const_mul
  条件: (ha : HasFDerivWithinAt a a' s x) (b : 𝔸)
  证明: ((ContinuousLinearMap.mul 𝕜 𝔸) b).hasFDerivAt.comp_hasFDerivWithinAt x ha

@[fun_prop]

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.mul, comp_hasFDerivWithinAt, hasFDerivAt, hasFDerivAt.comp_hasFDerivWithinAt
-/
theorem HasFDerivWithinAt.const_mul (ha : HasFDerivWithinAt a a' s x) (b : 𝔸) :
    HasFDerivWithinAt (fun y => b * a y) (b • a') s x :=
  ((ContinuousLinearMap.mul 𝕜 𝔸) b).hasFDerivAt.comp_hasFDerivWithinAt x ha

@[fun_prop]
/--
theorem `HasFDerivAt.const_mul` / 定理 `HasFDerivAt.const_mul`

English:
theorem HasFDerivAt.const_mul
  given: (ha : HasFDerivAt a a' x) (b : 𝔸)
  proof: ((ContinuousLinearMap.mul 𝕜 𝔸) b).hasFDerivAt.comp x ha

@[fun_prop]

中文:
定理 HasFDerivAt.const_mul
  条件: (ha : HasFDerivAt a a' x) (b : 𝔸)
  证明: ((ContinuousLinearMap.mul 𝕜 𝔸) b).hasFDerivAt.comp x ha

@[fun_prop]

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.mul, hasFDerivAt, hasFDerivAt.comp
-/
theorem HasFDerivAt.const_mul (ha : HasFDerivAt a a' x) (b : 𝔸) :
    HasFDerivAt (fun y => b * a y) (b • a') x :=
  ((ContinuousLinearMap.mul 𝕜 𝔸) b).hasFDerivAt.comp x ha

@[fun_prop]
/--
theorem `DifferentiableWithinAt.const_mul` / 定理 `DifferentiableWithinAt.const_mul`

English:
theorem DifferentiableWithinAt.const_mul
  given: (ha : DifferentiableWithinAt 𝕜 a s x) (b : 𝔸)
  proof: (ha.hasFDerivWithinAt.const_mul b).differentiableWithinAt

@[fun_prop]

中文:
定理 DifferentiableWithinAt.const_mul
  条件: (ha : DifferentiableWithinAt 𝕜 a s x) (b : 𝔸)
  证明: (ha.hasFDerivWithinAt.const_mul b).differentiableWithinAt

@[fun_prop]

Depends on / 依赖: const_mul, differentiableWithinAt, ha.hasFDerivWithinAt.const_mul, hasFDerivWithinAt
-/
theorem DifferentiableWithinAt.const_mul (ha : DifferentiableWithinAt 𝕜 a s x) (b : 𝔸) :
    DifferentiableWithinAt 𝕜 (fun y => b * a y) s x :=
  (ha.hasFDerivWithinAt.const_mul b).differentiableWithinAt

@[fun_prop]
/--
theorem `DifferentiableAt.const_mul` / 定理 `DifferentiableAt.const_mul`

English:
theorem DifferentiableAt.const_mul
  given: (ha : DifferentiableAt 𝕜 a x) (b : 𝔸)
  proof: (ha.hasFDerivAt.const_mul b).differentiableAt

@[fun_prop]

中文:
定理 DifferentiableAt.const_mul
  条件: (ha : DifferentiableAt 𝕜 a x) (b : 𝔸)
  证明: (ha.hasFDerivAt.const_mul b).differentiableAt

@[fun_prop]

Depends on / 依赖: const_mul, differentiableAt, ha.hasFDerivAt.const_mul, hasFDerivAt
-/
theorem DifferentiableAt.const_mul (ha : DifferentiableAt 𝕜 a x) (b : 𝔸) :
    DifferentiableAt 𝕜 (fun y => b * a y) x :=
  (ha.hasFDerivAt.const_mul b).differentiableAt

@[fun_prop]
/--
theorem `DifferentiableOn.const_mul` / 定理 `DifferentiableOn.const_mul`

English:
theorem DifferentiableOn.const_mul
  given: (ha : DifferentiableOn 𝕜 a s) (b : 𝔸)
  proof: fun x hx => (ha x hx).const_mul b

@[fun_prop]

中文:
定理 DifferentiableOn.const_mul
  条件: (ha : DifferentiableOn 𝕜 a s) (b : 𝔸)
  证明: fun x hx => (ha x hx).const_mul b

@[fun_prop]

Depends on / 依赖: const_mul
-/
theorem DifferentiableOn.const_mul (ha : DifferentiableOn 𝕜 a s) (b : 𝔸) :
    DifferentiableOn 𝕜 (fun y => b * a y) s := fun x hx => (ha x hx).const_mul b

@[fun_prop]
/--
theorem `Differentiable.const_mul` / 定理 `Differentiable.const_mul`

English:
theorem Differentiable.const_mul
  given: (ha : Differentiable 𝕜 a) (b : 𝔸)
  proof: fun x => (ha x).const_mul b

中文:
定理 Differentiable.const_mul
  条件: (ha : Differentiable 𝕜 a) (b : 𝔸)
  证明: fun x => (ha x).const_mul b

Depends on / 依赖: const_mul
-/
theorem Differentiable.const_mul (ha : Differentiable 𝕜 a) (b : 𝔸) :
    Differentiable 𝕜 fun y => b * a y := fun x => (ha x).const_mul b

/--
theorem `fderivWithin_const_mul` / 定理 `fderivWithin_const_mul`

English:
theorem fderivWithin_const_mul
  statement: (hxs : UniqueDiffWithinAt 𝕜 s x)
  proof: (ha.hasFDerivWithinAt.const_mul b).fderivWithin hxs

中文:
定理 fderivWithin_const_mul
  结论: (hxs : UniqueDiffWithinAt 𝕜 s x)
  证明: (ha.hasFDerivWithinAt.const_mul b).fderivWithin hxs

Depends on / 依赖: const_mul, fderivWithin, ha.hasFDerivWithinAt.const_mul, hasFDerivWithinAt
-/
theorem fderivWithin_const_mul (hxs : UniqueDiffWithinAt 𝕜 s x)
    (ha : DifferentiableWithinAt 𝕜 a s x) (b : 𝔸) :
    fderivWithin 𝕜 (fun y => b * a y) s x = b • fderivWithin 𝕜 a s x :=
  (ha.hasFDerivWithinAt.const_mul b).fderivWithin hxs

/--
theorem `fderiv_const_mul` / 定理 `fderiv_const_mul`

English:
theorem fderiv_const_mul
  given: (ha : DifferentiableAt 𝕜 a x) (b : 𝔸)
  proof: (ha.hasFDerivAt.const_mul b).fderiv

中文:
定理 fderiv_const_mul
  条件: (ha : DifferentiableAt 𝕜 a x) (b : 𝔸)
  证明: (ha.hasFDerivAt.const_mul b).fderiv

Depends on / 依赖: const_mul, fderiv, ha.hasFDerivAt.const_mul, hasFDerivAt
-/
theorem fderiv_const_mul (ha : DifferentiableAt 𝕜 a x) (b : 𝔸) :
    fderiv 𝕜 (fun y => b * a y) x = b • fderiv 𝕜 a x :=
  (ha.hasFDerivAt.const_mul b).fderiv

end Mul

section Prod
open scoped RightActions

/-! ### Derivative of a finite product of functions -/

variable {ι : Type*} {𝔸 𝔸' : Type*} [NormedRing 𝔸] [NormedCommRing 𝔸'] [NormedAlgebra 𝕜 𝔸]
  [NormedAlgebra 𝕜 𝔸'] {u : Finset ι} {f : ι -> E -> 𝔸} {f' : ι -> E ->L[𝕜] 𝔸} {g : ι -> E -> 𝔸'}
  {g' : ι -> E ->L[𝕜] 𝔸'}

@[fun_prop]
/--
theorem `hasStrictFDerivAt_list_prod'` / 定理 `hasStrictFDerivAt_list_prod'`

English:
theorem hasStrictFDerivAt_list_prod'
  given: [Finite ι] {l : List ι} {x : ι -> 𝔸}
  proof: by
  have := Fintype.ofFinite ι
  induction l with
  | nil => simp [hasStrictFDerivAt_const]
  | cons a l IH =>
    simp only [List.map_cons, List.prod_cons, ← proj_apply (R := 𝕜) (φ := fun _ : ι => 𝔸) a]
    exact .congr_fderiv (.mul' (ContinuousLinearMap.hasStrictFDerivAt _) IH)
      (by ext; sim

中文:
定理 hasStrictFDerivAt_list_prod'
  条件: [Finite ι] {l : List ι} {x : ι -> 𝔸}
  证明: by
  have := Fintype.ofFinite ι
  induction l with
  | nil => simp [hasStrictFDerivAt_const]
  | cons a l IH =>
    simp only [List.map_cons, List.prod_cons, ← proj_apply (R := 𝕜) (φ := fun _ : ι => 𝔸) a]
    exact .congr_fderiv (.mul' (ContinuousLinearMap.hasStrictFDerivAt _) IH)
      (by ext; sim

Depends on / 依赖: l.map
-/
theorem hasStrictFDerivAt_list_prod' [Finite ι] {l : List ι} {x : ι -> 𝔸} :
    HasStrictFDerivAt (𝕜 := 𝕜) (fun x => (l.map x).prod)
      (∑ i : Fin l.length, ((l.take i).map x).prod •
        proj l[i] <• ((l.drop (.succ i)).map x).prod) x := by
  have := Fintype.ofFinite ι
  induction l with
  | nil => simp [hasStrictFDerivAt_const]
  | cons a l IH =>
    simp only [List.map_cons, List.prod_cons, ← proj_apply (R := 𝕜) (φ := fun _ : ι => 𝔸) a]
    exact .congr_fderiv (.mul' (ContinuousLinearMap.hasStrictFDerivAt _) IH)
      (by ext; simp [Fin.sum_univ_succ, Finset.mul_sum, mul_assoc, add_comm])

@[fun_prop]
/--
theorem `hasStrictFDerivAt_list_prod_finRange'` / 定理 `hasStrictFDerivAt_list_prod_finRange'`

English:
theorem hasStrictFDerivAt_list_prod_finRange'
  given: {n : Nat} {x : Fin n -> 𝔸}
  proof: hasStrictFDerivAt_list_prod'.congr_fderiv
    Finset.sum_equiv (finCongr List.length_finRange) (by simp) (by simp)

@[fun_prop]

中文:
定理 hasStrictFDerivAt_list_prod_finRange'
  条件: {n : 自然数} {x : Fin n -> 𝔸}
  证明: hasStrictFDerivAt_list_prod'.congr_fderiv
    Finset.sum_equiv (finCongr List.length_finRange) (by simp) (by simp)

@[fun_prop]

Depends on / 依赖: List.finRange, finRange
-/
theorem hasStrictFDerivAt_list_prod_finRange' {n : Nat} {x : Fin n -> 𝔸} :
    HasStrictFDerivAt (𝕜 := 𝕜) (fun x => ((List.finRange n).map x).prod)
      (∑ i : Fin n, (((List.finRange n).take i).map x).prod •
        proj i <• (((List.finRange n).drop (.succ i)).map x).prod) x :=
hasStrictFDerivAt_list_prod'.congr_fderiv
    Finset.sum_equiv (finCongr List.length_finRange) (by simp) (by simp)

@[fun_prop]
/--
theorem `hasStrictFDerivAt_list_prod_attach'` / 定理 `hasStrictFDerivAt_list_prod_attach'`

English:
theorem hasStrictFDerivAt_list_prod_attach'
  given: {l : List ι} {x : {i // i in l} -> 𝔸}
  proof: by
classical exact hasStrictFDerivAt_list_prod'.congr_fderiv Eq.symm
    Finset.sum_equiv (finCongr List.length_attach.symm) (by simp) (by simp)

@[fun_prop]

中文:
定理 hasStrictFDerivAt_list_prod_attach'
  条件: {l : List ι} {x : {i // i in l} -> 𝔸}
  证明: by
classical exact hasStrictFDerivAt_list_prod'.congr_fderiv Eq.symm
    Finset.sum_equiv (finCongr List.length_attach.symm) (by simp) (by simp)

@[fun_prop]

Depends on / 依赖: attach, l.attach.map
-/
theorem hasStrictFDerivAt_list_prod_attach' {l : List ι} {x : {i // i in l} -> 𝔸} :
    HasStrictFDerivAt (𝕜 := 𝕜) (fun x => (l.attach.map x).prod)
      (∑ i : Fin l.length, ((l.attach.take i).map x).prod •
        proj l.attach[i.cast List.length_attach.symm] <•
          ((l.attach.drop (.succ i)).map x).prod) x := by
classical exact hasStrictFDerivAt_list_prod'.congr_fderiv Eq.symm
    Finset.sum_equiv (finCongr List.length_attach.symm) (by simp) (by simp)

@[fun_prop]
/--
theorem `hasFDerivAt_list_prod'` / 定理 `hasFDerivAt_list_prod'`

English:
theorem hasFDerivAt_list_prod'
  given: [Finite ι] {l : List ι} {x : ι -> 𝔸'}
  proof: have := Fintype.ofFinite ι
  hasStrictFDerivAt_list_prod'.hasFDerivAt

@[fun_prop]

中文:
定理 hasFDerivAt_list_prod'
  条件: [Finite ι] {l : List ι} {x : ι -> 𝔸'}
  证明: have := Fintype.ofFinite ι
  hasStrictFDerivAt_list_prod'.hasFDerivAt

@[fun_prop]

Depends on / 依赖: l.map
-/
theorem hasFDerivAt_list_prod' [Finite ι] {l : List ι} {x : ι -> 𝔸'} :
    HasFDerivAt (𝕜 := 𝕜) (fun x => (l.map x).prod)
      (∑ i : Fin l.length, ((l.take i).map x).prod •
        proj l[i] <• ((l.drop (.succ i)).map x).prod) x :=
  have := Fintype.ofFinite ι
  hasStrictFDerivAt_list_prod'.hasFDerivAt

@[fun_prop]
/--
theorem `hasFDerivAt_list_prod_finRange'` / 定理 `hasFDerivAt_list_prod_finRange'`

English:
theorem hasFDerivAt_list_prod_finRange'
  given: {n : Nat} {x : Fin n -> 𝔸}
  proof: hasStrictFDerivAt_list_prod_finRange'.hasFDerivAt

@[fun_prop]

中文:
定理 hasFDerivAt_list_prod_finRange'
  条件: {n : 自然数} {x : Fin n -> 𝔸}
  证明: hasStrictFDerivAt_list_prod_finRange'.hasFDerivAt

@[fun_prop]

Depends on / 依赖: List.finRange, finRange
-/
theorem hasFDerivAt_list_prod_finRange' {n : Nat} {x : Fin n -> 𝔸} :
    HasFDerivAt (𝕜 := 𝕜) (fun x => ((List.finRange n).map x).prod)
      (∑ i : Fin n, (((List.finRange n).take i).map x).prod •
        proj i <• (((List.finRange n).drop (.succ i)).map x).prod) x :=
  hasStrictFDerivAt_list_prod_finRange'.hasFDerivAt

@[fun_prop]
/--
theorem `hasFDerivAt_list_prod_attach'` / 定理 `hasFDerivAt_list_prod_attach'`

English:
theorem hasFDerivAt_list_prod_attach'
  given: {l : List ι} {x : {i // i in l} -> 𝔸}
  proof: by
  exact hasStrictFDerivAt_list_prod_attach'.hasFDerivAt

中文:
定理 hasFDerivAt_list_prod_attach'
  条件: {l : List ι} {x : {i // i in l} -> 𝔸}
  证明: by
  exact hasStrictFDerivAt_list_prod_attach'.hasFDerivAt

Depends on / 依赖: attach, l.attach.map
-/
theorem hasFDerivAt_list_prod_attach' {l : List ι} {x : {i // i in l} -> 𝔸} :
    HasFDerivAt (𝕜 := 𝕜) (fun x => (l.attach.map x).prod)
      (∑ i : Fin l.length, ((l.attach.take i).map x).prod •
        (proj l.attach[i.cast List.length_attach.symm]) <•
          ((l.attach.drop (.succ i)).map x).prod) x := by
  exact hasStrictFDerivAt_list_prod_attach'.hasFDerivAt

/--
Auxiliary lemma for `hasStrictFDerivAt_multiset_prod`.

For `NormedCommRing 𝔸'`, can rewrite as `Multiset` using `Multiset.prod_coe`.
-/
@[fun_prop]
/--
theorem `hasStrictFDerivAt_list_prod` / 定理 `hasStrictFDerivAt_list_prod`

English:
theorem hasStrictFDerivAt_list_prod
  given: [DecidableEq ι] [Finite ι] {l : List ι} {x : ι -> 𝔸'}
  proof: by
  have := Fintype.ofFinite ι
  refine hasStrictFDerivAt_list_prod'.congr_fderiv ?_
  conv_rhs => arg 1; arg 2; rw [← List.map_get_finRange l]
  simp only [List.map_map, ← List.sum_toFinset _ (List.nodup_finRange _), List.toFinset_finRange,
    Function.comp_def, ((List.erase_getElem _).map _).pro

中文:
定理 hasStrictFDerivAt_list_prod
  条件: [DecidableEq ι] [Finite ι] {l : List ι} {x : ι -> 𝔸'}
  证明: by
  have := Fintype.ofFinite ι
  refine hasStrictFDerivAt_list_prod'.congr_fderiv ?_
  conv_rhs => arg 1; arg 2; rw [← List.map_get_finRange l]
  simp only [List.map_map, ← List.sum_toFinset _ (List.nodup_finRange _), List.toFinset_finRange,
    Function.comp_def, ((List.erase_getElem _).map _).pro

Depends on / 依赖: l.map
-/
theorem hasStrictFDerivAt_list_prod [DecidableEq ι] [Finite ι] {l : List ι} {x : ι -> 𝔸'} :
    HasStrictFDerivAt (𝕜 := 𝕜) (fun x => (l.map x).prod)
      (l.map fun i => ((l.erase i).map x).prod • proj i).sum x := by
  have := Fintype.ofFinite ι
  refine hasStrictFDerivAt_list_prod'.congr_fderiv ?_
  conv_rhs => arg 1; arg 2; rw [← List.map_get_finRange l]
  simp only [List.map_map, ← List.sum_toFinset _ (List.nodup_finRange _), List.toFinset_finRange,
    Function.comp_def, ((List.erase_getElem _).map _).prod_eq, List.eraseIdx_eq_take_drop_succ,
    List.map_append, List.prod_append, List.get_eq_getElem, Fin.getElem_fin, Nat.succ_eq_add_one]
  exact Finset.sum_congr rfl fun i _ => by
    ext; simp only [smul_apply, op_smul_eq_smul, smul_eq_mul]; ring

@[fun_prop]
/--
theorem `hasStrictFDerivAt_multiset_prod` / 定理 `hasStrictFDerivAt_multiset_prod`

English:
theorem hasStrictFDerivAt_multiset_prod
  given: [DecidableEq ι] [Finite ι] {u : Multiset ι} {x : ι -> 𝔸'}
  proof: have := Fintype.ofFinite ι
  u.inductionOn fun l => by simpa using hasStrictFDerivAt_list_prod

@[fun_prop]

中文:
定理 hasStrictFDerivAt_multiset_prod
  条件: [DecidableEq ι] [Finite ι] {u : Multiset ι} {x : ι -> 𝔸'}
  证明: have := Fintype.ofFinite ι
  u.inductionOn fun l => by simpa using hasStrictFDerivAt_list_prod

@[fun_prop]

Depends on / 依赖: u.map
-/
theorem hasStrictFDerivAt_multiset_prod [DecidableEq ι] [Finite ι] {u : Multiset ι} {x : ι -> 𝔸'} :
    HasStrictFDerivAt (𝕜 := 𝕜) (fun x => (u.map x).prod)
      (u.map (fun i => ((u.erase i).map x).prod • proj i)).sum x :=
  have := Fintype.ofFinite ι
  u.inductionOn fun l => by simpa using hasStrictFDerivAt_list_prod

@[fun_prop]
/--
theorem `hasFDerivAt_multiset_prod` / 定理 `hasFDerivAt_multiset_prod`

English:
theorem hasFDerivAt_multiset_prod
  given: [DecidableEq ι] [Finite ι] {u : Multiset ι} {x : ι -> 𝔸'}
  proof: have := Fintype.ofFinite ι
  hasStrictFDerivAt_multiset_prod.hasFDerivAt

中文:
定理 hasFDerivAt_multiset_prod
  条件: [DecidableEq ι] [Finite ι] {u : Multiset ι} {x : ι -> 𝔸'}
  证明: have := Fintype.ofFinite ι
  hasStrictFDerivAt_multiset_prod.hasFDerivAt

Depends on / 依赖: u.map
-/
theorem hasFDerivAt_multiset_prod [DecidableEq ι] [Finite ι] {u : Multiset ι} {x : ι -> 𝔸'} :
    HasFDerivAt (𝕜 := 𝕜) (fun x => (u.map x).prod)
      (Multiset.sum (u.map (fun i => ((u.erase i).map x).prod • proj i))) x :=
  have := Fintype.ofFinite ι
  hasStrictFDerivAt_multiset_prod.hasFDerivAt

/--
theorem `hasStrictFDerivAt_finsetProd` / 定理 `hasStrictFDerivAt_finsetProd`

English:
theorem hasStrictFDerivAt_finsetProd
  given: [DecidableEq ι] [Finite ι] {x : ι -> 𝔸'}
  proof: by
  simp only [Finset.sum_eq_multiset_sum, Finset.prod_eq_multiset_prod]
  exact hasStrictFDerivAt_multiset_prod

@[deprecated (since := "2026-04-08")]
alias hasStrictFDerivAt_finset_prod := hasStrictFDerivAt_finsetProd

中文:
定理 hasStrictFDerivAt_finsetProd
  条件: [DecidableEq ι] [Finite ι] {x : ι -> 𝔸'}
  证明: by
  simp only [Finset.sum_eq_multiset_sum, Finset.prod_eq_multiset_prod]
  exact hasStrictFDerivAt_multiset_prod

@[deprecated (since := "2026-04-08")]
alias hasStrictFDerivAt_finset_prod := hasStrictFDerivAt_finsetProd

Depends on / 依赖: Finset, Finset.prod_eq_multiset_prod, Finset.sum_eq_multiset_sum, hasStrictFDerivAt_multiset_prod, prod_eq_multiset_prod, sum_eq_multiset_sum, u.erase
-/
theorem hasStrictFDerivAt_finsetProd [DecidableEq ι] [Finite ι] {x : ι -> 𝔸'} :
    HasStrictFDerivAt (𝕜 := 𝕜) (∏ i in u, · i) (∑ i in u, (∏ j in u.erase i, x j) • proj i) x := by
  simp only [Finset.sum_eq_multiset_sum, Finset.prod_eq_multiset_prod]
  exact hasStrictFDerivAt_multiset_prod

@[deprecated (since := "2026-04-08")]
alias hasStrictFDerivAt_finset_prod := hasStrictFDerivAt_finsetProd

/--
theorem `hasFDerivAt_finsetProd` / 定理 `hasFDerivAt_finsetProd`

English:
theorem hasFDerivAt_finsetProd
  given: [DecidableEq ι] [Finite ι] {x : ι -> 𝔸'}
  proof: have := Fintype.ofFinite ι
  hasStrictFDerivAt_finsetProd.hasFDerivAt

@[deprecated (since := "2026-04-08")] alias hasFDerivAt_finset_prod := hasFDerivAt_finsetProd

中文:
定理 hasFDerivAt_finsetProd
  条件: [DecidableEq ι] [Finite ι] {x : ι -> 𝔸'}
  证明: have := Fintype.ofFinite ι
  hasStrictFDerivAt_finsetProd.hasFDerivAt

@[deprecated (since := "2026-04-08")] alias hasFDerivAt_finset_prod := hasFDerivAt_finsetProd

Depends on / 依赖: u.erase
-/
theorem hasFDerivAt_finsetProd [DecidableEq ι] [Finite ι] {x : ι -> 𝔸'} :
    HasFDerivAt (𝕜 := 𝕜) (∏ i in u, · i) (∑ i in u, (∏ j in u.erase i, x j) • proj i) x :=
  have := Fintype.ofFinite ι
  hasStrictFDerivAt_finsetProd.hasFDerivAt

@[deprecated (since := "2026-04-08")] alias hasFDerivAt_finset_prod := hasFDerivAt_finsetProd

section Comp

@[fun_prop]
/--
theorem `HasStrictFDerivAt.list_prod'` / 定理 `HasStrictFDerivAt.list_prod'`

English:
theorem HasStrictFDerivAt.list_prod'
  statement: {l : List ι} {x : E}
  proof: by
  simp_rw [Fin.getElem_fin, ← l.get_eq_getElem, ← List.map_get_finRange l, List.map_map]
  -- After https://github.com/leanprover-community/mathlib4/issues/19108, we have to be optimistic with `:)`s; otherwise Lean decides it need to find
  -- `NormedAddCommGroup (List 𝔸)` which is nonsense.
  re

中文:
定理 HasStrictFDerivAt.list_prod'
  结论: {l : List ι} {x : E}
  证明: by
  simp_rw [Fin.getElem_fin, ← l.get_eq_getElem, ← List.map_get_finRange l, List.map_map]
  -- After https://github.com/leanprover-community/mathlib4/issues/19108, we have to be optimistic with `:)`s; otherwise Lean decides it need to find
  -- `NormedAddCommGroup (List 𝔸)` which is nonsense.
  re

Depends on / 依赖: Fin.getElem_fin, List.map_get_finRange, List.map_map, getElem_fin, get_eq_getElem, l.get_eq_getElem, map_get_finRange, map_map, simp_rw
-/
theorem HasStrictFDerivAt.list_prod' {l : List ι} {x : E}
    (h : forall i in l, HasStrictFDerivAt (f i ·) (f' i) x) :
    HasStrictFDerivAt (fun x => (l.map (f · x)).prod)
      (∑ i : Fin l.length, ((l.take i).map (f · x)).prod •
        f' l[i] <• ((l.drop (.succ i)).map (f · x)).prod) x := by
  simp_rw [Fin.getElem_fin, ← l.get_eq_getElem, ← List.map_get_finRange l, List.map_map]
  -- After https://github.com/leanprover-community/mathlib4/issues/19108, we have to be optimistic with `:)`s; otherwise Lean decides it need to find
  -- `NormedAddCommGroup (List 𝔸)` which is nonsense.
  refine .congr_fderiv (hasStrictFDerivAt_list_prod_finRange'.comp x
    (hasStrictFDerivAt_pi.mpr fun i => h (l.get i) (List.getElem_mem ..)) :) ?_
  ext m
  simp_rw [List.map_take, List.map_drop, List.map_map, comp_apply, sum_apply, smul_apply,
    proj_apply, pi_apply, Function.comp_def]

/--
Unlike `HasFDerivAt.finsetProd`, supports non-commutative multiply and duplicate elements.
-/
@[fun_prop]
/--
theorem `HasFDerivAt.list_prod'` / 定理 `HasFDerivAt.list_prod'`

English:
theorem HasFDerivAt.list_prod'
  statement: {l : List ι} {x : E}
  proof: by
  simp_rw [Fin.getElem_fin, ← l.get_eq_getElem, ← List.map_get_finRange l, List.map_map]
  refine .congr_fderiv (hasFDerivAt_list_prod_finRange'.comp x
    (hasFDerivAt_pi.mpr fun i => h (l.get i) (l.get_mem i)) :) ?_
  ext m
  simp_rw [List.map_take, List.map_drop, List.map_map, comp_apply, sum_

中文:
定理 HasFDerivAt.list_prod'
  结论: {l : List ι} {x : E}
  证明: by
  simp_rw [Fin.getElem_fin, ← l.get_eq_getElem, ← List.map_get_finRange l, List.map_map]
  refine .congr_fderiv (hasFDerivAt_list_prod_finRange'.comp x
    (hasFDerivAt_pi.mpr fun i => h (l.get i) (l.get_mem i)) :) ?_
  ext m
  simp_rw [List.map_take, List.map_drop, List.map_map, comp_apply, sum_

Depends on / 依赖: Fin.getElem_fin, Function, Function.comp_def, List.map_drop, List.map_get_finRange, List.map_map, List.map_take, comp_apply, comp_def, congr_fderiv, getElem_fin, get_eq_getElem, get_mem, hasFDerivAt_list_prod_finRange, hasFDerivAt_pi, hasFDerivAt_pi.mpr, l.get, l.get_eq_getElem, l.get_mem, map_drop
-/
theorem HasFDerivAt.list_prod' {l : List ι} {x : E}
    (h : forall i in l, HasFDerivAt (f i ·) (f' i) x) :
    HasFDerivAt (fun x => (l.map (f · x)).prod)
      (∑ i : Fin l.length, ((l.take i).map (f · x)).prod •
        f' l[i] <• ((l.drop (.succ i)).map (f · x)).prod) x := by
  simp_rw [Fin.getElem_fin, ← l.get_eq_getElem, ← List.map_get_finRange l, List.map_map]
  refine .congr_fderiv (hasFDerivAt_list_prod_finRange'.comp x
    (hasFDerivAt_pi.mpr fun i => h (l.get i) (l.get_mem i)) :) ?_
  ext m
  simp_rw [List.map_take, List.map_drop, List.map_map, comp_apply, sum_apply, smul_apply,
    proj_apply, pi_apply, Function.comp_def]

@[fun_prop]
/--
theorem `HasFDerivWithinAt.list_prod'` / 定理 `HasFDerivWithinAt.list_prod'`

English:
theorem HasFDerivWithinAt.list_prod'
  statement: {l : List ι} {x : E}
  proof: by
  simp_rw [Fin.getElem_fin, ← l.get_eq_getElem, ← List.map_get_finRange l, List.map_map]
  refine .congr_fderiv (hasFDerivAt_list_prod_finRange'.comp_hasFDerivWithinAt x
    (hasFDerivWithinAt_pi.mpr fun i => h (l.get i) (l.get_mem i)) :) ?_
  ext m
  simp_rw [List.map_take, List.map_drop, List.m

中文:
定理 HasFDerivWithinAt.list_prod'
  结论: {l : List ι} {x : E}
  证明: by
  simp_rw [Fin.getElem_fin, ← l.get_eq_getElem, ← List.map_get_finRange l, List.map_map]
  refine .congr_fderiv (hasFDerivAt_list_prod_finRange'.comp_hasFDerivWithinAt x
    (hasFDerivWithinAt_pi.mpr fun i => h (l.get i) (l.get_mem i)) :) ?_
  ext m
  simp_rw [List.map_take, List.map_drop, List.m

Depends on / 依赖: Fin.getElem_fin, Function, Function.comp_def, List.map_drop, List.map_get_finRange, List.map_map, List.map_take, comp_apply, comp_def, comp_hasFDerivWithinAt, congr_fderiv, getElem_fin, get_eq_getElem, get_mem, hasFDerivAt_list_prod_finRange, hasFDerivWithinAt_pi, hasFDerivWithinAt_pi.mpr, l.get, l.get_eq_getElem, l.get_mem
-/
theorem HasFDerivWithinAt.list_prod' {l : List ι} {x : E}
    (h : forall i in l, HasFDerivWithinAt (f i ·) (f' i) s x) :
    HasFDerivWithinAt (fun x => (l.map (f · x)).prod)
      (∑ i : Fin l.length, ((l.take i).map (f · x)).prod •
        f' l[i] <• ((l.drop (.succ i)).map (f · x)).prod) s x := by
  simp_rw [Fin.getElem_fin, ← l.get_eq_getElem, ← List.map_get_finRange l, List.map_map]
  refine .congr_fderiv (hasFDerivAt_list_prod_finRange'.comp_hasFDerivWithinAt x
    (hasFDerivWithinAt_pi.mpr fun i => h (l.get i) (l.get_mem i)) :) ?_
  ext m
  simp_rw [List.map_take, List.map_drop, List.map_map, comp_apply, sum_apply, smul_apply,
    proj_apply, pi_apply, Function.comp_def]

/--
theorem `fderiv_list_prod'` / 定理 `fderiv_list_prod'`

English:
theorem fderiv_list_prod'
  statement: {l : List ι} {x : E}
  proof: (HasFDerivAt.list_prod' fun i hi => (h i hi).hasFDerivAt).fderiv

中文:
定理 fderiv_list_prod'
  结论: {l : List ι} {x : E}
  证明: (HasFDerivAt.list_prod' fun i hi => (h i hi).hasFDerivAt).fderiv

Depends on / 依赖: HasFDerivAt, HasFDerivAt.list_prod, fderiv, hasFDerivAt, list_prod
-/
theorem fderiv_list_prod' {l : List ι} {x : E}
    (h : forall i in l, DifferentiableAt 𝕜 (f i ·) x) :
    fderiv 𝕜 (fun x => (l.map (f · x)).prod) x =
      ∑ i : Fin l.length, ((l.take i).map (f · x)).prod •
        (fderiv 𝕜 (fun x => f l[i] x) x) <• ((l.drop (.succ i)).map (f · x)).prod :=
  (HasFDerivAt.list_prod' fun i hi => (h i hi).hasFDerivAt).fderiv

/--
theorem `fderivWithin_list_prod'` / 定理 `fderivWithin_list_prod'`

English:
theorem fderivWithin_list_prod'
  statement: {l : List ι} {x : E}
  proof: (HasFDerivWithinAt.list_prod' fun i hi => (h i hi).hasFDerivWithinAt).fderivWithin hxs

@[fun_prop]

中文:
定理 fderivWithin_list_prod'
  结论: {l : List ι} {x : E}
  证明: (HasFDerivWithinAt.list_prod' fun i hi => (h i hi).hasFDerivWithinAt).fderivWithin hxs

@[fun_prop]

Depends on / 依赖: HasFDerivWithinAt, HasFDerivWithinAt.list_prod, fderivWithin, hasFDerivWithinAt, list_prod
-/
theorem fderivWithin_list_prod' {l : List ι} {x : E}
    (hxs : UniqueDiffWithinAt 𝕜 s x) (h : forall i in l, DifferentiableWithinAt 𝕜 (f i ·) s x) :
    fderivWithin 𝕜 (fun x => (l.map (f · x)).prod) s x =
      ∑ i : Fin l.length, ((l.take i).map (f · x)).prod •
        (fderivWithin 𝕜 (fun x => f l[i] x) s x) <• ((l.drop (.succ i)).map (f · x)).prod :=
  (HasFDerivWithinAt.list_prod' fun i hi => (h i hi).hasFDerivWithinAt).fderivWithin hxs

@[fun_prop]
/--
theorem `HasStrictFDerivAt.multiset_prod` / 定理 `HasStrictFDerivAt.multiset_prod`

English:
theorem HasStrictFDerivAt.multiset_prod
  statement: [DecidableEq ι] {u : Multiset ι} {x : E}
  proof: by
  simp only [← Multiset.attach_map_val u, Multiset.map_map]
  exact .congr_fderiv
    (hasStrictFDerivAt_multiset_prod.comp x <|
      hasStrictFDerivAt_pi.mpr fun i => h (Subtype.val i) i.prop :)
    (by ext; simp [Finset.sum_multiset_map_count, u.erase_attach_map (g · x)])

中文:
定理 HasStrictFDerivAt.multiset_prod
  结论: [DecidableEq ι] {u : Multiset ι} {x : E}
  证明: by
  simp only [← Multiset.attach_map_val u, Multiset.map_map]
  exact .congr_fderiv
    (hasStrictFDerivAt_multiset_prod.comp x <|
      hasStrictFDerivAt_pi.mpr fun i => h (Subtype.val i) i.prop :)
    (by ext; simp [Finset.sum_multiset_map_count, u.erase_attach_map (g · x)])

Depends on / 依赖: Finset, Finset.sum_multiset_map_count, Multiset, Multiset.attach_map_val, Multiset.map_map, Subtype, Subtype.val, attach_map_val, congr_fderiv, erase_attach_map, hasStrictFDerivAt_multiset_prod, hasStrictFDerivAt_multiset_prod.comp, hasStrictFDerivAt_pi, hasStrictFDerivAt_pi.mpr, i.prop, map_map, sum_multiset_map_count, u.erase_attach_map
-/
theorem HasStrictFDerivAt.multiset_prod [DecidableEq ι] {u : Multiset ι} {x : E}
    (h : forall i in u, HasStrictFDerivAt (g i ·) (g' i) x) :
    HasStrictFDerivAt (fun x => (u.map (g · x)).prod)
      (u.map fun i => ((u.erase i).map (g · x)).prod • g' i).sum x := by
  simp only [← Multiset.attach_map_val u, Multiset.map_map]
  exact .congr_fderiv
    (hasStrictFDerivAt_multiset_prod.comp x <|
      hasStrictFDerivAt_pi.mpr fun i => h (Subtype.val i) i.prop :)
    (by ext; simp [Finset.sum_multiset_map_count, u.erase_attach_map (g · x)])

/--
Unlike `HasFDerivAt.finsetProd`, supports duplicate elements.
-/
@[fun_prop]
/--
theorem `HasFDerivAt.multiset_prod` / 定理 `HasFDerivAt.multiset_prod`

English:
theorem HasFDerivAt.multiset_prod
  statement: [DecidableEq ι] {u : Multiset ι} {x : E}
  proof: by
  simp only [← Multiset.attach_map_val u, Multiset.map_map]
  exact .congr_fderiv
    (hasFDerivAt_multiset_prod.comp x <| hasFDerivAt_pi.mpr fun i => h (Subtype.val i) i.prop :)
    (by ext; simp [Finset.sum_multiset_map_count, u.erase_attach_map (g · x)])

@[fun_prop]

中文:
定理 HasFDerivAt.multiset_prod
  结论: [DecidableEq ι] {u : Multiset ι} {x : E}
  证明: by
  simp only [← Multiset.attach_map_val u, Multiset.map_map]
  exact .congr_fderiv
    (hasFDerivAt_multiset_prod.comp x <| hasFDerivAt_pi.mpr fun i => h (Subtype.val i) i.prop :)
    (by ext; simp [Finset.sum_multiset_map_count, u.erase_attach_map (g · x)])

@[fun_prop]

Depends on / 依赖: Finset, Finset.sum_multiset_map_count, Multiset, Multiset.attach_map_val, Multiset.map_map, Subtype, Subtype.val, attach_map_val, congr_fderiv, erase_attach_map, hasFDerivAt_multiset_prod, hasFDerivAt_multiset_prod.comp, hasFDerivAt_pi, hasFDerivAt_pi.mpr, i.prop, map_map, sum_multiset_map_count, u.erase_attach_map
-/
theorem HasFDerivAt.multiset_prod [DecidableEq ι] {u : Multiset ι} {x : E}
    (h : forall i in u, HasFDerivAt (g i ·) (g' i) x) :
    HasFDerivAt (fun x => (u.map (g · x)).prod)
      (u.map fun i => ((u.erase i).map (g · x)).prod • g' i).sum x := by
  simp only [← Multiset.attach_map_val u, Multiset.map_map]
  exact .congr_fderiv
    (hasFDerivAt_multiset_prod.comp x <| hasFDerivAt_pi.mpr fun i => h (Subtype.val i) i.prop :)
    (by ext; simp [Finset.sum_multiset_map_count, u.erase_attach_map (g · x)])

@[fun_prop]
/--
theorem `HasFDerivWithinAt.multiset_prod` / 定理 `HasFDerivWithinAt.multiset_prod`

English:
theorem HasFDerivWithinAt.multiset_prod
  statement: [DecidableEq ι] {u : Multiset ι} {x : E}
  proof: by
  simp only [← Multiset.attach_map_val u, Multiset.map_map]
  exact .congr_fderiv
    (hasFDerivAt_multiset_prod.comp_hasFDerivWithinAt x <|
      hasFDerivWithinAt_pi.mpr fun i => h (Subtype.val i) i.prop :)
    (by ext; simp [Finset.sum_multiset_map_count, u.erase_attach_map (g · x)])

中文:
定理 HasFDerivWithinAt.multiset_prod
  结论: [DecidableEq ι] {u : Multiset ι} {x : E}
  证明: by
  simp only [← Multiset.attach_map_val u, Multiset.map_map]
  exact .congr_fderiv
    (hasFDerivAt_multiset_prod.comp_hasFDerivWithinAt x <|
      hasFDerivWithinAt_pi.mpr fun i => h (Subtype.val i) i.prop :)
    (by ext; simp [Finset.sum_multiset_map_count, u.erase_attach_map (g · x)])

Depends on / 依赖: Finset, Finset.sum_multiset_map_count, Multiset, Multiset.attach_map_val, Multiset.map_map, Subtype, Subtype.val, attach_map_val, comp_hasFDerivWithinAt, congr_fderiv, erase_attach_map, hasFDerivAt_multiset_prod, hasFDerivAt_multiset_prod.comp_hasFDerivWithinAt, hasFDerivWithinAt_pi, hasFDerivWithinAt_pi.mpr, i.prop, map_map, sum_multiset_map_count, u.erase_attach_map
-/
theorem HasFDerivWithinAt.multiset_prod [DecidableEq ι] {u : Multiset ι} {x : E}
    (h : forall i in u, HasFDerivWithinAt (g i ·) (g' i) s x) :
    HasFDerivWithinAt (fun x => (u.map (g · x)).prod)
      (u.map fun i => ((u.erase i).map (g · x)).prod • g' i).sum s x := by
  simp only [← Multiset.attach_map_val u, Multiset.map_map]
  exact .congr_fderiv
    (hasFDerivAt_multiset_prod.comp_hasFDerivWithinAt x <|
      hasFDerivWithinAt_pi.mpr fun i => h (Subtype.val i) i.prop :)
    (by ext; simp [Finset.sum_multiset_map_count, u.erase_attach_map (g · x)])

/--
theorem `fderiv_multiset_prod` / 定理 `fderiv_multiset_prod`

English:
theorem fderiv_multiset_prod
  statement: [DecidableEq ι] {u : Multiset ι} {x : E}
  proof: (HasFDerivAt.multiset_prod fun i hi => (h i hi).hasFDerivAt).fderiv

中文:
定理 fderiv_multiset_prod
  结论: [DecidableEq ι] {u : Multiset ι} {x : E}
  证明: (HasFDerivAt.multiset_prod fun i hi => (h i hi).hasFDerivAt).fderiv

Depends on / 依赖: HasFDerivAt, HasFDerivAt.multiset_prod, fderiv, hasFDerivAt, multiset_prod
-/
theorem fderiv_multiset_prod [DecidableEq ι] {u : Multiset ι} {x : E}
    (h : forall i in u, DifferentiableAt 𝕜 (g i ·) x) :
    fderiv 𝕜 (fun x => (u.map (g · x)).prod) x =
      (u.map fun i => ((u.erase i).map (g · x)).prod • fderiv 𝕜 (g i) x).sum :=
  (HasFDerivAt.multiset_prod fun i hi => (h i hi).hasFDerivAt).fderiv

/--
theorem `fderivWithin_multiset_prod` / 定理 `fderivWithin_multiset_prod`

English:
theorem fderivWithin_multiset_prod
  statement: [DecidableEq ι] {u : Multiset ι} {x : E}
  proof: (HasFDerivWithinAt.multiset_prod fun i hi => (h i hi).hasFDerivWithinAt).fderivWithin hxs

中文:
定理 fderivWithin_multiset_prod
  结论: [DecidableEq ι] {u : Multiset ι} {x : E}
  证明: (HasFDerivWithinAt.multiset_prod fun i hi => (h i hi).hasFDerivWithinAt).fderivWithin hxs

Depends on / 依赖: HasFDerivWithinAt, HasFDerivWithinAt.multiset_prod, fderivWithin, hasFDerivWithinAt, multiset_prod
-/
theorem fderivWithin_multiset_prod [DecidableEq ι] {u : Multiset ι} {x : E}
    (hxs : UniqueDiffWithinAt 𝕜 s x) (h : forall i in u, DifferentiableWithinAt 𝕜 (g i ·) s x) :
    fderivWithin 𝕜 (fun x => (u.map (g · x)).prod) s x =
      (u.map fun i => ((u.erase i).map (g · x)).prod • fderivWithin 𝕜 (g i) s x).sum :=
  (HasFDerivWithinAt.multiset_prod fun i hi => (h i hi).hasFDerivWithinAt).fderivWithin hxs

/--
theorem `HasStrictFDerivAt.finsetProd` / 定理 `HasStrictFDerivAt.finsetProd`

English:
theorem HasStrictFDerivAt.finsetProd
  statement: [DecidableEq ι] {x : E}
  proof: by
  simpa [← Finset.prod_attach u] using .congr_fderiv
    (hasStrictFDerivAt_finsetProd.comp x <| hasStrictFDerivAt_pi.mpr fun i => hg i i.prop)
    (by ext; simp [Finset.prod_erase_attach (g · x), ← u.sum_attach])

@[deprecated (since := "2026-04-08")]
alias HasStrictFDerivAt.finset_prod := HasSt

中文:
定理 HasStrictFDerivAt.finsetProd
  结论: [DecidableEq ι] {x : E}
  证明: by
  simpa [← Finset.prod_attach u] using .congr_fderiv
    (hasStrictFDerivAt_finsetProd.comp x <| hasStrictFDerivAt_pi.mpr fun i => hg i i.prop)
    (by ext; simp [Finset.prod_erase_attach (g · x), ← u.sum_attach])

@[deprecated (since := "2026-04-08")]
alias HasStrictFDerivAt.finset_prod := HasSt

Depends on / 依赖: Finset, Finset.prod_attach, Finset.prod_erase_attach, congr_fderiv, hasStrictFDerivAt_finsetProd, hasStrictFDerivAt_finsetProd.comp, hasStrictFDerivAt_pi, hasStrictFDerivAt_pi.mpr, i.prop, prod_attach, prod_erase_attach, sum_attach, u.sum_attach
-/
theorem HasStrictFDerivAt.finsetProd [DecidableEq ι] {x : E}
    (hg : forall i in u, HasStrictFDerivAt (g i) (g' i) x) :
    HasStrictFDerivAt (∏ i in u, g i ·) (∑ i in u, (∏ j in u.erase i, g j x) • g' i) x := by
  simpa [← Finset.prod_attach u] using .congr_fderiv
    (hasStrictFDerivAt_finsetProd.comp x <| hasStrictFDerivAt_pi.mpr fun i => hg i i.prop)
    (by ext; simp [Finset.prod_erase_attach (g · x), ← u.sum_attach])

@[deprecated (since := "2026-04-08")]
alias HasStrictFDerivAt.finset_prod := HasStrictFDerivAt.finsetProd

/--
theorem `HasFDerivAt.finsetProd` / 定理 `HasFDerivAt.finsetProd`

English:
theorem HasFDerivAt.finsetProd
  statement: [DecidableEq ι] {x : E}
  proof: by
  simpa [← Finset.prod_attach u] using .congr_fderiv
    (hasFDerivAt_finsetProd.comp x <| hasFDerivAt_pi.mpr fun i => hg (Subtype.val i) i.prop :)
    (by ext; simp [Finset.prod_erase_attach (g · x), ← u.sum_attach])

@[deprecated (since := "2026-04-08")] alias HasFDerivAt.finset_prod := HasFDer

中文:
定理 HasFDerivAt.finsetProd
  结论: [DecidableEq ι] {x : E}
  证明: by
  simpa [← Finset.prod_attach u] using .congr_fderiv
    (hasFDerivAt_finsetProd.comp x <| hasFDerivAt_pi.mpr fun i => hg (Subtype.val i) i.prop :)
    (by ext; simp [Finset.prod_erase_attach (g · x), ← u.sum_attach])

@[deprecated (since := "2026-04-08")] alias HasFDerivAt.finset_prod := HasFDer

Depends on / 依赖: Finset, Finset.prod_attach, Finset.prod_erase_attach, Subtype, Subtype.val, congr_fderiv, hasFDerivAt_finsetProd, hasFDerivAt_finsetProd.comp, hasFDerivAt_pi, hasFDerivAt_pi.mpr, i.prop, prod_attach, prod_erase_attach, sum_attach, u.sum_attach
-/
theorem HasFDerivAt.finsetProd [DecidableEq ι] {x : E}
    (hg : forall i in u, HasFDerivAt (g i) (g' i) x) :
    HasFDerivAt (∏ i in u, g i ·) (∑ i in u, (∏ j in u.erase i, g j x) • g' i) x := by
  simpa [← Finset.prod_attach u] using .congr_fderiv
    (hasFDerivAt_finsetProd.comp x <| hasFDerivAt_pi.mpr fun i => hg (Subtype.val i) i.prop :)
    (by ext; simp [Finset.prod_erase_attach (g · x), ← u.sum_attach])

@[deprecated (since := "2026-04-08")] alias HasFDerivAt.finset_prod := HasFDerivAt.finsetProd

/--
theorem `HasFDerivWithinAt.finsetProd` / 定理 `HasFDerivWithinAt.finsetProd`

English:
theorem HasFDerivWithinAt.finsetProd
  statement: [DecidableEq ι] {x : E}
  proof: by
  simpa [← Finset.prod_attach u] using .congr_fderiv
    (hasFDerivAt_finsetProd.comp_hasFDerivWithinAt x <|
      hasFDerivWithinAt_pi.mpr fun i => hg (Subtype.val i) i.prop :)
    (by ext; simp [Finset.prod_erase_attach (g · x), ← u.sum_attach])

@[deprecated (since := "2026-04-08")]
alias HasF

中文:
定理 HasFDerivWithinAt.finsetProd
  结论: [DecidableEq ι] {x : E}
  证明: by
  simpa [← Finset.prod_attach u] using .congr_fderiv
    (hasFDerivAt_finsetProd.comp_hasFDerivWithinAt x <|
      hasFDerivWithinAt_pi.mpr fun i => hg (Subtype.val i) i.prop :)
    (by ext; simp [Finset.prod_erase_attach (g · x), ← u.sum_attach])

@[deprecated (since := "2026-04-08")]
alias HasF

Depends on / 依赖: Finset, Finset.prod_attach, Finset.prod_erase_attach, Subtype, Subtype.val, comp_hasFDerivWithinAt, congr_fderiv, hasFDerivAt_finsetProd, hasFDerivAt_finsetProd.comp_hasFDerivWithinAt, hasFDerivWithinAt_pi, hasFDerivWithinAt_pi.mpr, i.prop, prod_attach, prod_erase_attach, sum_attach, u.sum_attach
-/
theorem HasFDerivWithinAt.finsetProd [DecidableEq ι] {x : E}
    (hg : forall i in u, HasFDerivWithinAt (g i) (g' i) s x) :
    HasFDerivWithinAt (∏ i in u, g i ·) (∑ i in u, (∏ j in u.erase i, g j x) • g' i) s x := by
  simpa [← Finset.prod_attach u] using .congr_fderiv
    (hasFDerivAt_finsetProd.comp_hasFDerivWithinAt x <|
      hasFDerivWithinAt_pi.mpr fun i => hg (Subtype.val i) i.prop :)
    (by ext; simp [Finset.prod_erase_attach (g · x), ← u.sum_attach])

@[deprecated (since := "2026-04-08")]
alias HasFDerivWithinAt.finset_prod := HasFDerivWithinAt.finsetProd

/--
theorem `fderiv_finsetProd` / 定理 `fderiv_finsetProd`

English:
theorem fderiv_finsetProd
  given: [DecidableEq ι] {x : E} (hg : forall i in u, DifferentiableAt 𝕜 (g i) x)
  proof: (HasFDerivAt.finsetProd fun i hi => (hg i hi).hasFDerivAt).fderiv

@[deprecated (since := "2026-04-08")] alias fderiv_finset_prod := fderiv_finsetProd

中文:
定理 fderiv_finsetProd
  条件: [DecidableEq ι] {x : E} (hg : 对任意 i in u, DifferentiableAt 𝕜 (g i) x)
  证明: (HasFDerivAt.finsetProd fun i hi => (hg i hi).hasFDerivAt).fderiv

@[deprecated (since := "2026-04-08")] alias fderiv_finset_prod := fderiv_finsetProd

Depends on / 依赖: HasFDerivAt, HasFDerivAt.finsetProd, fderiv, finsetProd, hasFDerivAt
-/
theorem fderiv_finsetProd [DecidableEq ι] {x : E} (hg : forall i in u, DifferentiableAt 𝕜 (g i) x) :
    fderiv 𝕜 (∏ i in u, g i ·) x = ∑ i in u, (∏ j in u.erase i, (g j x)) • fderiv 𝕜 (g i) x :=
  (HasFDerivAt.finsetProd fun i hi => (hg i hi).hasFDerivAt).fderiv

@[deprecated (since := "2026-04-08")] alias fderiv_finset_prod := fderiv_finsetProd

/--
theorem `fderivWithin_finsetProd` / 定理 `fderivWithin_finsetProd`

English:
theorem fderivWithin_finsetProd
  statement: [DecidableEq ι] {x : E} (hxs : UniqueDiffWithinAt 𝕜 s x)
  proof: (HasFDerivWithinAt.finsetProd fun i hi => (hg i hi).hasFDerivWithinAt).fderivWithin hxs

@[deprecated (since := "2026-04-08")] alias fderivWithin_finset_prod := fderivWithin_finsetProd

中文:
定理 fderivWithin_finsetProd
  结论: [DecidableEq ι] {x : E} (hxs : UniqueDiffWithinAt 𝕜 s x)
  证明: (HasFDerivWithinAt.finsetProd fun i hi => (hg i hi).hasFDerivWithinAt).fderivWithin hxs

@[deprecated (since := "2026-04-08")] alias fderivWithin_finset_prod := fderivWithin_finsetProd

Depends on / 依赖: HasFDerivWithinAt, HasFDerivWithinAt.finsetProd, fderivWithin, finsetProd, hasFDerivWithinAt
-/
theorem fderivWithin_finsetProd [DecidableEq ι] {x : E} (hxs : UniqueDiffWithinAt 𝕜 s x)
    (hg : forall i in u, DifferentiableWithinAt 𝕜 (g i) s x) :
    fderivWithin 𝕜 (∏ i in u, g i ·) s x =
      ∑ i in u, (∏ j in u.erase i, (g j x)) • fderivWithin 𝕜 (g i) s x :=
  (HasFDerivWithinAt.finsetProd fun i hi => (hg i hi).hasFDerivWithinAt).fderivWithin hxs

@[deprecated (since := "2026-04-08")] alias fderivWithin_finset_prod := fderivWithin_finsetProd

end Comp

end Prod

section AlgebraInverse

variable {R : Type*} [NormedRing R] [HasSummableGeomSeries R] [NormedAlgebra 𝕜 R]

open NormedRing ContinuousLinearMap Ring

/-- At an invertible element `x` of a normed algebra `R`, the Fréchet derivative of the inversion
operation is the linear map `fun t ↦ - x⁻¹ * t * x⁻¹`.

TODO (low prio): prove a version without assumption `[HasSummableGeomSeries R]` but within the set
of units. -/
@[fun_prop]
/--
theorem `hasFDerivAt_ringInverse` / 定理 `hasFDerivAt_ringInverse`

English:
theorem hasFDerivAt_ringInverse
  given: (x : Rˣ)
  proof: by
  have : (fun t : R => Ring.inverse (↑x + t) - ↑x⁻¹ + ↑x⁻¹ * t * ↑x⁻¹) =o[𝓝 0] id :=
    (inverse_add_norm_diff_second_order x).trans_isLittleO (isLittleO_norm_pow_id one_lt_two)
  simpa [hasFDerivAt_iff_isLittleO_nhds_zero] using! this

@[fun_prop]

中文:
定理 hasFDerivAt_ringInverse
  条件: (x : Rˣ)
  证明: by
  have : (fun t : R => Ring.inverse (↑x + t) - ↑x⁻¹ + ↑x⁻¹ * t * ↑x⁻¹) =o[𝓝 0] id :=
    (inverse_add_norm_diff_second_order x).trans_isLittleO (isLittleO_norm_pow_id one_lt_two)
  simpa [hasFDerivAt_iff_isLittleO_nhds_zero] using! this

@[fun_prop]

Depends on / 依赖: Ring.inverse, hasFDerivAt_iff_isLittleO_nhds_zero, inverse, inverse_add_norm_diff_second_order, isLittleO_norm_pow_id, one_lt_two, trans_isLittleO
-/
theorem hasFDerivAt_ringInverse (x : Rˣ) :
    HasFDerivAt Ring.inverse (-mulLeftRight 𝕜 R ↑x⁻¹ ↑x⁻¹) x := by
  have : (fun t : R => Ring.inverse (↑x + t) - ↑x⁻¹ + ↑x⁻¹ * t * ↑x⁻¹) =o[𝓝 0] id :=
    (inverse_add_norm_diff_second_order x).trans_isLittleO (isLittleO_norm_pow_id one_lt_two)
  simpa [hasFDerivAt_iff_isLittleO_nhds_zero] using! this

@[fun_prop]
/--
theorem `differentiableAt_inverse` / 定理 `differentiableAt_inverse`

English:
theorem differentiableAt_inverse
  given: {x : R} (hx : IsUnit x)
  proof: let ⟨u, hu⟩ := hx; hu ▸ (hasFDerivAt_ringInverse u).differentiableAt

@[fun_prop]

中文:
定理 differentiableAt_inverse
  条件: {x : R} (hx : IsUnit x)
  证明: let ⟨u, hu⟩ := hx; hu ▸ (hasFDerivAt_ringInverse u).differentiableAt

@[fun_prop]

Depends on / 依赖: differentiableAt, hasFDerivAt_ringInverse
-/
theorem differentiableAt_inverse {x : R} (hx : IsUnit x) :
    DifferentiableAt 𝕜 (@Ring.inverse R _) x :=
  let ⟨u, hu⟩ := hx; hu ▸ (hasFDerivAt_ringInverse u).differentiableAt

@[fun_prop]
/--
theorem `differentiableWithinAt_inverse` / 定理 `differentiableWithinAt_inverse`

English:
theorem differentiableWithinAt_inverse
  given: {x : R} (hx : IsUnit x) (s : Set R)
  proof: (differentiableAt_inverse hx).differentiableWithinAt

@[fun_prop]

中文:
定理 differentiableWithinAt_inverse
  条件: {x : R} (hx : IsUnit x) (s : Set R)
  证明: (differentiableAt_inverse hx).differentiableWithinAt

@[fun_prop]

Depends on / 依赖: differentiableAt_inverse, differentiableWithinAt
-/
theorem differentiableWithinAt_inverse {x : R} (hx : IsUnit x) (s : Set R) :
    DifferentiableWithinAt 𝕜 (@Ring.inverse R _) s x :=
  (differentiableAt_inverse hx).differentiableWithinAt

@[fun_prop]
/--
theorem `differentiableOn_inverse` / 定理 `differentiableOn_inverse`

English:
theorem differentiableOn_inverse
  statement: DifferentiableOn 𝕜 (@Ring.inverse R _) {x | IsUnit x}
  proof: fun _x hx => differentiableWithinAt_inverse hx _

中文:
定理 differentiableOn_inverse
  结论: DifferentiableOn 𝕜 (@Ring.inverse R _) {x | IsUnit x}
  证明: fun _x hx => differentiableWithinAt_inverse hx _

Depends on / 依赖: differentiableWithinAt_inverse
-/
theorem differentiableOn_inverse : DifferentiableOn 𝕜 (@Ring.inverse R _) {x | IsUnit x} :=
  fun _x hx => differentiableWithinAt_inverse hx _

/--
theorem `fderiv_inverse` / 定理 `fderiv_inverse`

English:
theorem fderiv_inverse
  given: (x : Rˣ)
  statement: fderiv 𝕜 (@Ring.inverse R _) x = -mulLeftRight 𝕜 R ↑x⁻¹ ↑x⁻¹
  proof: (hasFDerivAt_ringInverse x).fderiv

中文:
定理 fderiv_inverse
  条件: (x : Rˣ)
  结论: fderiv 𝕜 (@Ring.inverse R _) x = -mulLeftRight 𝕜 R ↑x⁻¹ ↑x⁻¹
  证明: (hasFDerivAt_ringInverse x).fderiv

Depends on / 依赖: fderiv, hasFDerivAt_ringInverse
-/
theorem fderiv_inverse (x : Rˣ) : fderiv 𝕜 (@Ring.inverse R _) x = -mulLeftRight 𝕜 R ↑x⁻¹ ↑x⁻¹ :=
  (hasFDerivAt_ringInverse x).fderiv

/--
theorem `hasStrictFDerivAt_ringInverse` / 定理 `hasStrictFDerivAt_ringInverse`

English:
theorem hasStrictFDerivAt_ringInverse
  given: (x : Rˣ)
  proof: by
  convert! (analyticAt_inverse (𝕜 := 𝕜) x).hasStrictFDerivAt
  exact (fderiv_inverse x).symm

中文:
定理 hasStrictFDerivAt_ringInverse
  条件: (x : Rˣ)
  证明: by
  convert! (analyticAt_inverse (𝕜 := 𝕜) x).hasStrictFDerivAt
  exact (fderiv_inverse x).symm

Depends on / 依赖: analyticAt_inverse, convert, fderiv_inverse, hasStrictFDerivAt
-/
theorem hasStrictFDerivAt_ringInverse (x : Rˣ) :
    HasStrictFDerivAt Ring.inverse (-mulLeftRight 𝕜 R ↑x⁻¹ ↑x⁻¹) x := by
  convert! (analyticAt_inverse (𝕜 := 𝕜) x).hasStrictFDerivAt
  exact (fderiv_inverse x).symm

variable {h : E -> R} {z : E} {S : Set E}

@[fun_prop]
/--
theorem `DifferentiableWithinAt.inverse` / 定理 `DifferentiableWithinAt.inverse`

English:
theorem DifferentiableWithinAt.inverse
  given: (hf : DifferentiableWithinAt 𝕜 h S z) (hz : IsUnit (h z))
  proof: (differentiableAt_inverse hz).comp_differentiableWithinAt z hf

@[simp, fun_prop]

中文:
定理 DifferentiableWithinAt.inverse
  条件: (hf : DifferentiableWithinAt 𝕜 h S z) (hz : IsUnit (h z))
  证明: (differentiableAt_inverse hz).comp_differentiableWithinAt z hf

@[simp, fun_prop]

Depends on / 依赖: comp_differentiableWithinAt, differentiableAt_inverse
-/
theorem DifferentiableWithinAt.inverse (hf : DifferentiableWithinAt 𝕜 h S z) (hz : IsUnit (h z)) :
    DifferentiableWithinAt 𝕜 (fun x => (h x)⁻¹ʳ) S z :=
  (differentiableAt_inverse hz).comp_differentiableWithinAt z hf

@[simp, fun_prop]
/--
theorem `DifferentiableAt.inverse` / 定理 `DifferentiableAt.inverse`

English:
theorem DifferentiableAt.inverse
  given: (hf : DifferentiableAt 𝕜 h z) (hz : IsUnit (h z))
  proof: (differentiableAt_inverse hz).comp z hf

@[fun_prop]

中文:
定理 DifferentiableAt.inverse
  条件: (hf : DifferentiableAt 𝕜 h z) (hz : IsUnit (h z))
  证明: (differentiableAt_inverse hz).comp z hf

@[fun_prop]

Depends on / 依赖: differentiableAt_inverse
-/
theorem DifferentiableAt.inverse (hf : DifferentiableAt 𝕜 h z) (hz : IsUnit (h z)) :
    DifferentiableAt 𝕜 (fun x => (h x)⁻¹ʳ) z :=
  (differentiableAt_inverse hz).comp z hf

@[fun_prop]
/--
theorem `DifferentiableOn.inverse` / 定理 `DifferentiableOn.inverse`

English:
theorem DifferentiableOn.inverse
  given: (hf : DifferentiableOn 𝕜 h S) (hz : forall x in S, IsUnit (h x))
  proof: fun x h => (hf x h).inverse (hz x h)

@[simp, fun_prop]

中文:
定理 DifferentiableOn.inverse
  条件: (hf : DifferentiableOn 𝕜 h S) (hz : 对任意 x in S, IsUnit (h x))
  证明: fun x h => (hf x h).inverse (hz x h)

@[simp, fun_prop]

Depends on / 依赖: inverse
-/
theorem DifferentiableOn.inverse (hf : DifferentiableOn 𝕜 h S) (hz : forall x in S, IsUnit (h x)) :
    DifferentiableOn 𝕜 (fun x => (h x)⁻¹ʳ) S := fun x h => (hf x h).inverse (hz x h)

@[simp, fun_prop]
/--
theorem `Differentiable.inverse` / 定理 `Differentiable.inverse`

English:
theorem Differentiable.inverse
  given: (hf : Differentiable 𝕜 h) (hz : forall x, IsUnit (h x))
  proof: fun x => (hf x).inverse (hz x)

中文:
定理 Differentiable.inverse
  条件: (hf : Differentiable 𝕜 h) (hz : 对任意 x, IsUnit (h x))
  证明: fun x => (hf x).inverse (hz x)

Depends on / 依赖: inverse
-/
theorem Differentiable.inverse (hf : Differentiable 𝕜 h) (hz : forall x, IsUnit (h x)) :
    Differentiable 𝕜 fun x => (h x)⁻¹ʳ := fun x => (hf x).inverse (hz x)

end AlgebraInverse

/-! ### Derivative of the inverse in a division ring

Note that some lemmas are primed as they are expressed without commutativity, whereas their
counterparts in commutative fields involve simpler expressions, and are given in
`Mathlib/Analysis/Calculus/Deriv/Inv.lean`.
-/

section DivisionRingInverse

variable {R : Type*} [NormedDivisionRing R] [NormedAlgebra 𝕜 R]

open NormedRing ContinuousLinearMap Ring

/--
theorem `hasStrictFDerivAt_inv'` / 定理 `hasStrictFDerivAt_inv'`

English:
theorem hasStrictFDerivAt_inv'
  given: {x : R} (hx : x != 0)
  proof: by
  simpa using hasStrictFDerivAt_ringInverse (Units.mk0 _ hx)

中文:
定理 hasStrictFDerivAt_inv'
  条件: {x : R} (hx : x != 0)
  证明: by
  simpa using hasStrictFDerivAt_ringInverse (Units.mk0 _ hx)

Depends on / 依赖: Units.mk0, hasStrictFDerivAt_ringInverse
-/
theorem hasStrictFDerivAt_inv' {x : R} (hx : x != 0) :
    HasStrictFDerivAt Inv.inv (-mulLeftRight 𝕜 R x⁻¹ x⁻¹) x := by
  simpa using hasStrictFDerivAt_ringInverse (Units.mk0 _ hx)

/-- At an invertible element `x` of a normed division algebra `R`, the Fréchet derivative of the
inversion operation is the linear map `fun t ↦ - x⁻¹ * t * x⁻¹`. For a nicer formula in the
commutative case, see `hasFDerivAt_inv`. -/
@[fun_prop]
/--
theorem `hasFDerivAt_inv'` / 定理 `hasFDerivAt_inv'`

English:
theorem hasFDerivAt_inv'
  given: {x : R} (hx : x != 0)
  proof: by
  simpa using hasFDerivAt_ringInverse (Units.mk0 _ hx)

@[fun_prop]

中文:
定理 hasFDerivAt_inv'
  条件: {x : R} (hx : x != 0)
  证明: by
  simpa using hasFDerivAt_ringInverse (Units.mk0 _ hx)

@[fun_prop]

Depends on / 依赖: Units.mk0, hasFDerivAt_ringInverse
-/
theorem hasFDerivAt_inv' {x : R} (hx : x != 0) :
    HasFDerivAt Inv.inv (-mulLeftRight 𝕜 R x⁻¹ x⁻¹) x := by
  simpa using hasFDerivAt_ringInverse (Units.mk0 _ hx)

@[fun_prop]
/--
theorem `differentiableAt_inv` / 定理 `differentiableAt_inv`

English:
theorem differentiableAt_inv
  given: {x : R} (hx : x != 0)
  statement: DifferentiableAt 𝕜 Inv.inv x
  proof: (hasFDerivAt_inv' hx).differentiableAt

@[fun_prop]

中文:
定理 differentiableAt_inv
  条件: {x : R} (hx : x != 0)
  结论: DifferentiableAt 𝕜 Inv.inv x
  证明: (hasFDerivAt_inv' hx).differentiableAt

@[fun_prop]

Depends on / 依赖: differentiableAt, hasFDerivAt_inv
-/
theorem differentiableAt_inv {x : R} (hx : x != 0) : DifferentiableAt 𝕜 Inv.inv x :=
  (hasFDerivAt_inv' hx).differentiableAt

@[fun_prop]
/--
theorem `differentiableWithinAt_inv` / 定理 `differentiableWithinAt_inv`

English:
theorem differentiableWithinAt_inv
  given: {x : R} (hx : x != 0) (s : Set R)
  proof: (differentiableAt_inv hx).differentiableWithinAt

@[fun_prop]

中文:
定理 differentiableWithinAt_inv
  条件: {x : R} (hx : x != 0) (s : Set R)
  证明: (differentiableAt_inv hx).differentiableWithinAt

@[fun_prop]

Depends on / 依赖: differentiableAt_inv, differentiableWithinAt
-/
theorem differentiableWithinAt_inv {x : R} (hx : x != 0) (s : Set R) :
    DifferentiableWithinAt 𝕜 (fun x => x⁻¹) s x :=
  (differentiableAt_inv hx).differentiableWithinAt

@[fun_prop]
/--
theorem `differentiableOn_inv` / 定理 `differentiableOn_inv`

English:
theorem differentiableOn_inv
  statement: DifferentiableOn 𝕜 (fun x : R => x⁻¹) {x | x != 0}
  proof: fun _x hx =>
  differentiableWithinAt_inv hx _

中文:
定理 differentiableOn_inv
  结论: DifferentiableOn 𝕜 (fun x : R => x⁻¹) {x | x != 0}
  证明: fun _x hx =>
  differentiableWithinAt_inv hx _
-/
theorem differentiableOn_inv : DifferentiableOn 𝕜 (fun x : R => x⁻¹) {x | x != 0} := fun _x hx =>
  differentiableWithinAt_inv hx _

/--
theorem `fderiv_inv'` / 定理 `fderiv_inv'`

English:
theorem fderiv_inv'
  given: {x : R} (hx : x != 0)
  statement: fderiv 𝕜 Inv.inv x = -mulLeftRight 𝕜 R x⁻¹ x⁻¹
  proof: (hasFDerivAt_inv' hx).fderiv

中文:
定理 fderiv_inv'
  条件: {x : R} (hx : x != 0)
  结论: fderiv 𝕜 Inv.inv x = -mulLeftRight 𝕜 R x⁻¹ x⁻¹
  证明: (hasFDerivAt_inv' hx).fderiv

Depends on / 依赖: fderiv, hasFDerivAt_inv
-/
theorem fderiv_inv' {x : R} (hx : x != 0) : fderiv 𝕜 Inv.inv x = -mulLeftRight 𝕜 R x⁻¹ x⁻¹ :=
  (hasFDerivAt_inv' hx).fderiv

/--
theorem `fderivWithin_inv'` / 定理 `fderivWithin_inv'`

English:
theorem fderivWithin_inv'
  given: {s : Set R} {x : R} (hx : x != 0) (hxs : UniqueDiffWithinAt 𝕜 s x)
  proof: by
  rw [DifferentiableAt.fderivWithin (differentiableAt_inv hx) hxs]
  exact fderiv_inv' hx

中文:
定理 fderivWithin_inv'
  条件: {s : Set R} {x : R} (hx : x != 0) (hxs : UniqueDiffWithinAt 𝕜 s x)
  证明: by
  rw [DifferentiableAt.fderivWithin (differentiableAt_inv hx) hxs]
  exact fderiv_inv' hx

Depends on / 依赖: DifferentiableAt, DifferentiableAt.fderivWithin, differentiableAt_inv, fderivWithin, fderiv_inv
-/
theorem fderivWithin_inv' {s : Set R} {x : R} (hx : x != 0) (hxs : UniqueDiffWithinAt 𝕜 s x) :
    fderivWithin 𝕜 (fun x => x⁻¹) s x = -mulLeftRight 𝕜 R x⁻¹ x⁻¹ := by
  rw [DifferentiableAt.fderivWithin (differentiableAt_inv hx) hxs]
  exact fderiv_inv' hx

variable {h : E -> R} {z : E} {S : Set E}

@[to_fun (attr := fun_prop)]
/--
theorem `DifferentiableWithinAt.inv` / 定理 `DifferentiableWithinAt.inv`

English:
theorem DifferentiableWithinAt.inv
  given: (hf : DifferentiableWithinAt 𝕜 h S z) (hz : h z != 0)
  proof: (differentiableAt_inv hz).comp_differentiableWithinAt z hf

@[to_fun (attr := simp, fun_prop)]

中文:
定理 DifferentiableWithinAt.inv
  条件: (hf : DifferentiableWithinAt 𝕜 h S z) (hz : h z != 0)
  证明: (differentiableAt_inv hz).comp_differentiableWithinAt z hf

@[to_fun (attr := simp, fun_prop)]

Depends on / 依赖: comp_differentiableWithinAt, differentiableAt_inv
-/
theorem DifferentiableWithinAt.inv (hf : DifferentiableWithinAt 𝕜 h S z) (hz : h z != 0) :
    DifferentiableWithinAt 𝕜 (h⁻¹) S z :=
  (differentiableAt_inv hz).comp_differentiableWithinAt z hf

@[to_fun (attr := simp, fun_prop)]
/--
theorem `DifferentiableAt.inv` / 定理 `DifferentiableAt.inv`

English:
theorem DifferentiableAt.inv
  given: (hf : DifferentiableAt 𝕜 h z) (hz : h z != 0)
  proof: (differentiableAt_inv hz).comp z hf

@[to_fun (attr := fun_prop)]

中文:
定理 DifferentiableAt.inv
  条件: (hf : DifferentiableAt 𝕜 h z) (hz : h z != 0)
  证明: (differentiableAt_inv hz).comp z hf

@[to_fun (attr := fun_prop)]

Depends on / 依赖: differentiableAt_inv
-/
theorem DifferentiableAt.inv (hf : DifferentiableAt 𝕜 h z) (hz : h z != 0) :
    DifferentiableAt 𝕜 (h⁻¹) z :=
  (differentiableAt_inv hz).comp z hf

@[to_fun (attr := fun_prop)]
/--
theorem `DifferentiableOn.inv` / 定理 `DifferentiableOn.inv`

English:
theorem DifferentiableOn.inv
  given: (hf : DifferentiableOn 𝕜 h S) (hz : forall x in S, h x != 0)
  proof: fun x h => (hf x h).inv (hz x h)

@[to_fun (attr := simp, fun_prop)]

中文:
定理 DifferentiableOn.inv
  条件: (hf : DifferentiableOn 𝕜 h S) (hz : 对任意 x in S, h x != 0)
  证明: fun x h => (hf x h).inv (hz x h)

@[to_fun (attr := simp, fun_prop)]
-/
theorem DifferentiableOn.inv (hf : DifferentiableOn 𝕜 h S) (hz : forall x in S, h x != 0) :
    DifferentiableOn 𝕜 (h⁻¹) S := fun x h => (hf x h).inv (hz x h)

@[to_fun (attr := simp, fun_prop)]
/--
theorem `Differentiable.inv` / 定理 `Differentiable.inv`

English:
theorem Differentiable.inv
  given: (hf : Differentiable 𝕜 h) (hz : forall x, h x != 0)
  proof: fun x => (hf x).inv (hz x)

中文:
定理 Differentiable.inv
  条件: (hf : Differentiable 𝕜 h) (hz : 对任意 x, h x != 0)
  证明: fun x => (hf x).inv (hz x)
-/
theorem Differentiable.inv (hf : Differentiable 𝕜 h) (hz : forall x, h x != 0) :
    Differentiable 𝕜 (h⁻¹) := fun x => (hf x).inv (hz x)

end DivisionRingInverse

end
