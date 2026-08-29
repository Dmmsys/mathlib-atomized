/-
Copyright (c) 2025 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Normed.Group.AddTorsor
public import Mathlib.Topology.Algebra.ContinuousAffineMap


/-!
# The derivative of continuous affine maps

For detailed documentation of the Fréchet derivative,
see the module docstring of `Mathlib/Analysis/Calculus/FDeriv/Basic.lean`.

This file contains the usual formulas (and existence assertions) for the derivative of
continuous affine maps.
-/

public section

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  (f : E ->ᴬ[𝕜] F) {x : E} {s : Set E} {L : Filter (E × E)}

namespace ContinuousAffineMap


/--
theorem `hasFDerivAtFilter` / 定理 `hasFDerivAtFilter`

English:
theorem hasFDerivAtFilter
  statement: HasFDerivAtFilter f f.contLinear L
  proof: by
refine .of_isLittleOTVS .congr_left (.zero _ _) ?_
  simp [(vsub_eq_sub _ _).symm.trans (f.contLinear_map_vsub _ _).symm]

@[fun_prop]

中文:
定理 hasFDerivAtFilter
  结论: HasFDerivAtFilter f f.contLinear L
  证明: by
refine .of_isLittleOTVS .congr_left (.zero _ _) ?_
  simp [(vsub_eq_sub _ _).symm.trans (f.contLinear_map_vsub _ _).symm]

@[fun_prop]
-/
protected theorem hasFDerivAtFilter : HasFDerivAtFilter f f.contLinear L := by
refine .of_isLittleOTVS .congr_left (.zero _ _) ?_
  simp [(vsub_eq_sub _ _).symm.trans (f.contLinear_map_vsub _ _).symm]

@[fun_prop]
/--
theorem `hasStrictFDerivAt` / 定理 `hasStrictFDerivAt`

English:
theorem hasStrictFDerivAt
  given: {x : E}
  statement: HasStrictFDerivAt f f.contLinear x
  proof: f.hasFDerivAtFilter

@[fun_prop]

中文:
定理 hasStrictFDerivAt
  条件: {x : E}
  结论: HasStrictFDerivAt f f.contLinear x
  证明: f.hasFDerivAtFilter

@[fun_prop]
-/
protected theorem hasStrictFDerivAt {x : E} : HasStrictFDerivAt f f.contLinear x :=
  f.hasFDerivAtFilter

@[fun_prop]
/--
theorem `hasFDerivWithinAt` / 定理 `hasFDerivWithinAt`

English:
theorem hasFDerivWithinAt
  statement: HasFDerivWithinAt f f.contLinear s x
  proof: f.hasFDerivAtFilter

@[fun_prop]

中文:
定理 hasFDerivWithinAt
  结论: HasFDerivWithinAt f f.contLinear s x
  证明: f.hasFDerivAtFilter

@[fun_prop]
-/
protected theorem hasFDerivWithinAt : HasFDerivWithinAt f f.contLinear s x :=
  f.hasFDerivAtFilter

@[fun_prop]
/--
theorem `hasFDerivAt` / 定理 `hasFDerivAt`

English:
theorem hasFDerivAt
  statement: HasFDerivAt f f.contLinear x
  proof: f.hasFDerivAtFilter

@[simp, fun_prop]

中文:
定理 hasFDerivAt
  结论: HasFDerivAt f f.contLinear x
  证明: f.hasFDerivAtFilter

@[simp, fun_prop]
-/
protected theorem hasFDerivAt : HasFDerivAt f f.contLinear x :=
  f.hasFDerivAtFilter

@[simp, fun_prop]
/--
theorem `differentiableAt` / 定理 `differentiableAt`

English:
theorem differentiableAt
  statement: DifferentiableAt 𝕜 f x
  proof: f.hasFDerivAt.differentiableAt

@[fun_prop]

中文:
定理 differentiableAt
  结论: DifferentiableAt 𝕜 f x
  证明: f.hasFDerivAt.differentiableAt

@[fun_prop]
-/
protected theorem differentiableAt : DifferentiableAt 𝕜 f x :=
  f.hasFDerivAt.differentiableAt

@[fun_prop]
/--
theorem `differentiableWithinAt` / 定理 `differentiableWithinAt`

English:
theorem differentiableWithinAt
  statement: DifferentiableWithinAt 𝕜 f s x
  proof: f.differentiableAt.differentiableWithinAt

@[simp]

中文:
定理 differentiableWithinAt
  结论: DifferentiableWithinAt 𝕜 f s x
  证明: f.differentiableAt.differentiableWithinAt

@[simp]
-/
protected theorem differentiableWithinAt : DifferentiableWithinAt 𝕜 f s x :=
  f.differentiableAt.differentiableWithinAt

@[simp]
/--
theorem `fderiv` / 定理 `fderiv`

English:
theorem fderiv
  statement: fderiv 𝕜 f x = f.contLinear
  proof: f.hasFDerivAt.fderiv

中文:
定理 fderiv
  结论: fderiv 𝕜 f x = f.contLinear
  证明: f.hasFDerivAt.fderiv
-/
protected theorem fderiv : fderiv 𝕜 f x = f.contLinear :=
  f.hasFDerivAt.fderiv

/--
theorem `fderivWithin` / 定理 `fderivWithin`

English:
theorem fderivWithin
  given: (hxs : UniqueDiffWithinAt 𝕜 s x)
  proof: by
  rw [DifferentiableAt.fderivWithin f.differentiableAt hxs]
  exact f.fderiv

@[simp, fun_prop]

中文:
定理 fderivWithin
  条件: (hxs : UniqueDiffWithinAt 𝕜 s x)
  证明: by
  rw [DifferentiableAt.fderivWithin f.differentiableAt hxs]
  exact f.fderiv

@[simp, fun_prop]
-/
protected theorem fderivWithin (hxs : UniqueDiffWithinAt 𝕜 s x) :
    fderivWithin 𝕜 f s x = f.contLinear := by
  rw [DifferentiableAt.fderivWithin f.differentiableAt hxs]
  exact f.fderiv

@[simp, fun_prop]
/--
theorem `differentiable` / 定理 `differentiable`

English:
theorem differentiable
  statement: Differentiable 𝕜 f
  proof: fun _ =>
  f.differentiableAt

@[fun_prop]

中文:
定理 differentiable
  结论: Differentiable 𝕜 f
  证明: fun _ =>
  f.differentiableAt

@[fun_prop]
-/
protected theorem differentiable : Differentiable 𝕜 f := fun _ =>
  f.differentiableAt

@[fun_prop]
/--
theorem `differentiableOn` / 定理 `differentiableOn`

English:
theorem differentiableOn
  statement: DifferentiableOn 𝕜 f s
  proof: f.differentiable.differentiableOn

中文:
定理 differentiableOn
  结论: DifferentiableOn 𝕜 f s
  证明: f.differentiable.differentiableOn
-/
protected theorem differentiableOn : DifferentiableOn 𝕜 f s :=
  f.differentiable.differentiableOn

end ContinuousAffineMap
