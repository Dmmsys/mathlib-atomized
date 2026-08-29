/-
Copyright (c) 2019 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Sébastien Gouëzel, Yury Kudryashov
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps

/-!
# The derivative of bounded linear maps

For detailed documentation of the Fréchet derivative,
see the module docstring of `Mathlib/Analysis/Calculus/FDeriv/Basic.lean`.

This file contains the usual formulas (and existence assertions) for the derivative of
bounded linear maps.
-/

public section

open Asymptotics

namespace ContinuousLinearMap

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
variable {F : Type*} [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F]
variable (f : E ->L[𝕜] F)
variable {x : E}
variable {s : Set E}
variable {L : Filter (E × E)}


/--
theorem `hasFDerivAtFilter` / 定理 `hasFDerivAtFilter`

English:
theorem hasFDerivAtFilter
  statement: HasFDerivAtFilter f f L
  proof: .of_isLittleOTVS (IsLittleOTVS.zero _ _).congr_left fun x => by
    simp only [f.map_sub, sub_self, Pi.zero_apply]

@[fun_prop]

中文:
定理 hasFDerivAtFilter
  结论: 有FDerivAtFilter f f L
  证明: .of_isLittleOTVS (IsLittleOTVS.zero _ _).congr_left fun x => by
    simp only [f.map_sub, sub_self, Pi.zero_apply]

@[fun_prop]
-/
protected theorem hasFDerivAtFilter : HasFDerivAtFilter f f L :=
.of_isLittleOTVS (IsLittleOTVS.zero _ _).congr_left fun x => by
    simp only [f.map_sub, sub_self, Pi.zero_apply]

@[fun_prop]
/--
theorem `hasStrictFDerivAt` / 定理 `hasStrictFDerivAt`

English:
theorem hasStrictFDerivAt
  statement: HasStrictFDerivAt f f x
  proof: f.hasFDerivAtFilter

@[fun_prop]

中文:
定理 hasStrictFDerivAt
  结论: HasStrictFDerivAt f f x
  证明: f.hasFDerivAtFilter

@[fun_prop]
-/
protected theorem hasStrictFDerivAt : HasStrictFDerivAt f f x :=
  f.hasFDerivAtFilter

@[fun_prop]
/--
theorem `hasFDerivWithinAt` / 定理 `hasFDerivWithinAt`

English:
theorem hasFDerivWithinAt
  statement: HasFDerivWithinAt f f s x
  proof: f.hasFDerivAtFilter

@[fun_prop]

中文:
定理 hasFDerivWithinAt
  结论: HasFDerivWithinAt f f s x
  证明: f.hasFDerivAtFilter

@[fun_prop]
-/
protected theorem hasFDerivWithinAt : HasFDerivWithinAt f f s x :=
  f.hasFDerivAtFilter

@[fun_prop]
/--
theorem `hasFDerivAt` / 定理 `hasFDerivAt`

English:
theorem hasFDerivAt
  statement: HasFDerivAt f f x
  proof: f.hasFDerivAtFilter

@[simp, fun_prop]

中文:
定理 hasFDerivAt
  结论: 在点处Fréchet可导 f f x
  证明: f.hasFDerivAtFilter

@[simp, fun_prop]
-/
protected theorem hasFDerivAt : HasFDerivAt f f x :=
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

@[simp, fun_prop]

中文:
定理 differentiableWithinAt
  结论: DifferentiableWithinAt 𝕜 f s x
  证明: f.differentiableAt.differentiableWithinAt

@[simp, fun_prop]
-/
protected theorem differentiableWithinAt : DifferentiableWithinAt 𝕜 f s x :=
  f.differentiableAt.differentiableWithinAt

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
  结论: 可微 𝕜 f
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

variable [ContinuousAdd E] [ContinuousSMul 𝕜 E] [ContinuousAdd F] [ContinuousSMul 𝕜 F] [T2Space F]

@[simp]
/--
theorem `fderiv` / 定理 `fderiv`

English:
theorem fderiv
  statement: fderiv 𝕜 f x = f
  proof: f.hasFDerivAt.fderiv

中文:
定理 fderiv
  结论: fderiv 𝕜 f x = f
  证明: f.hasFDerivAt.fderiv
-/
protected theorem fderiv : fderiv 𝕜 f x = f :=
  f.hasFDerivAt.fderiv

/--
theorem `fderivWithin` / 定理 `fderivWithin`

English:
theorem fderivWithin
  given: (hxs : UniqueDiffWithinAt 𝕜 s x)
  proof: by
  rw [DifferentiableAt.fderivWithin f.differentiableAt hxs]
  exact f.fderiv

中文:
定理 fderivWithin
  条件: (hxs : UniqueDiffWithinAt 𝕜 s x)
  证明: by
  rw [DifferentiableAt.fderivWithin f.differentiableAt hxs]
  exact f.fderiv
-/
protected theorem fderivWithin (hxs : UniqueDiffWithinAt 𝕜 s x) :
    fderivWithin 𝕜 f s x = f := by
  rw [DifferentiableAt.fderivWithin f.differentiableAt hxs]
  exact f.fderiv

end ContinuousLinearMap

/-! ### Unbundled continuous linear maps -/

namespace IsBoundedLinearMap
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {f : E -> F}
variable {x : E}
variable {s : Set E}
variable {L : Filter (E × E)}

/--
theorem `hasFDerivAtFilter` / 定理 `hasFDerivAtFilter`

English:
theorem hasFDerivAtFilter
  given: (h : IsBoundedLinearMap 𝕜 f)
  proof: h.toContinuousLinearMap.hasFDerivAtFilter

@[fun_prop]

中文:
定理 hasFDerivAtFilter
  条件: (h : 是BoundedLinear映射 𝕜 f)
  证明: h.toContinuousLinearMap.hasFDerivAtFilter

@[fun_prop]

Depends on / 依赖: h.toContinuousLinearMap.hasFDerivAtFilter, hasFDerivAtFilter, toContinuousLinearMap
-/
theorem hasFDerivAtFilter (h : IsBoundedLinearMap 𝕜 f) :
    HasFDerivAtFilter f h.toContinuousLinearMap L :=
  h.toContinuousLinearMap.hasFDerivAtFilter

@[fun_prop]
/--
theorem `hasFDerivWithinAt` / 定理 `hasFDerivWithinAt`

English:
theorem hasFDerivWithinAt
  given: (h : IsBoundedLinearMap 𝕜 f)
  proof: h.hasFDerivAtFilter

@[fun_prop]

中文:
定理 hasFDerivWithinAt
  条件: (h : 是BoundedLinear映射 𝕜 f)
  证明: h.hasFDerivAtFilter

@[fun_prop]

Depends on / 依赖: h.hasFDerivAtFilter, hasFDerivAtFilter
-/
theorem hasFDerivWithinAt (h : IsBoundedLinearMap 𝕜 f) :
    HasFDerivWithinAt f h.toContinuousLinearMap s x :=
  h.hasFDerivAtFilter

@[fun_prop]
/--
theorem `hasFDerivAt` / 定理 `hasFDerivAt`

English:
theorem hasFDerivAt
  given: (h : IsBoundedLinearMap 𝕜 f)
  proof: h.hasFDerivAtFilter

@[fun_prop]

中文:
定理 hasFDerivAt
  条件: (h : 是BoundedLinear映射 𝕜 f)
  证明: h.hasFDerivAtFilter

@[fun_prop]

Depends on / 依赖: h.hasFDerivAtFilter, hasFDerivAtFilter
-/
theorem hasFDerivAt (h : IsBoundedLinearMap 𝕜 f) :
    HasFDerivAt f h.toContinuousLinearMap x :=
  h.hasFDerivAtFilter

@[fun_prop]
/--
theorem `differentiableAt` / 定理 `differentiableAt`

English:
theorem differentiableAt
  given: (h : IsBoundedLinearMap 𝕜 f)
  statement: DifferentiableAt 𝕜 f x
  proof: h.hasFDerivAt.differentiableAt

@[fun_prop]

中文:
定理 differentiableAt
  条件: (h : 是BoundedLinear映射 𝕜 f)
  结论: DifferentiableAt 𝕜 f x
  证明: h.hasFDerivAt.differentiableAt

@[fun_prop]

Depends on / 依赖: differentiableAt, h.hasFDerivAt.differentiableAt, hasFDerivAt
-/
theorem differentiableAt (h : IsBoundedLinearMap 𝕜 f) : DifferentiableAt 𝕜 f x :=
  h.hasFDerivAt.differentiableAt

@[fun_prop]
/--
theorem `differentiableWithinAt` / 定理 `differentiableWithinAt`

English:
theorem differentiableWithinAt
  given: (h : IsBoundedLinearMap 𝕜 f)
  proof: h.differentiableAt.differentiableWithinAt

中文:
定理 differentiableWithinAt
  条件: (h : 是BoundedLinear映射 𝕜 f)
  证明: h.differentiableAt.differentiableWithinAt

Depends on / 依赖: differentiableAt, differentiableWithinAt, h.differentiableAt.differentiableWithinAt
-/
theorem differentiableWithinAt (h : IsBoundedLinearMap 𝕜 f) :
    DifferentiableWithinAt 𝕜 f s x :=
  h.differentiableAt.differentiableWithinAt

/--
theorem `fderiv` / 定理 `fderiv`

English:
theorem fderiv
  given: (h : IsBoundedLinearMap 𝕜 f)
  proof: HasFDerivAt.fderiv h.hasFDerivAt

中文:
定理 fderiv
  条件: (h : 是BoundedLinear映射 𝕜 f)
  证明: HasFDerivAt.fderiv h.hasFDerivAt
-/
protected theorem fderiv (h : IsBoundedLinearMap 𝕜 f) :
    fderiv 𝕜 f x = h.toContinuousLinearMap :=
  HasFDerivAt.fderiv h.hasFDerivAt

/--
theorem `fderivWithin` / 定理 `fderivWithin`

English:
theorem fderivWithin
  statement: (h : IsBoundedLinearMap 𝕜 f)
  proof: by
  rw [DifferentiableAt.fderivWithin h.differentiableAt hxs]
  exact h.fderiv

@[fun_prop]

中文:
定理 fderivWithin
  结论: (h : 是BoundedLinear映射 𝕜 f)
  证明: by
  rw [DifferentiableAt.fderivWithin h.differentiableAt hxs]
  exact h.fderiv

@[fun_prop]
-/
protected theorem fderivWithin (h : IsBoundedLinearMap 𝕜 f)
    (hxs : UniqueDiffWithinAt 𝕜 s x) : fderivWithin 𝕜 f s x = h.toContinuousLinearMap := by
  rw [DifferentiableAt.fderivWithin h.differentiableAt hxs]
  exact h.fderiv

@[fun_prop]
/--
theorem `differentiable` / 定理 `differentiable`

English:
theorem differentiable
  given: (h : IsBoundedLinearMap 𝕜 f)
  statement: Differentiable 𝕜 f
  proof: fun _ => h.differentiableAt

@[fun_prop]

中文:
定理 differentiable
  条件: (h : 是BoundedLinear映射 𝕜 f)
  结论: 可微 𝕜 f
  证明: fun _ => h.differentiableAt

@[fun_prop]

Depends on / 依赖: differentiableAt, h.differentiableAt
-/
theorem differentiable (h : IsBoundedLinearMap 𝕜 f) : Differentiable 𝕜 f :=
  fun _ => h.differentiableAt

@[fun_prop]
/--
theorem `differentiableOn` / 定理 `differentiableOn`

English:
theorem differentiableOn
  given: (h : IsBoundedLinearMap 𝕜 f)
  statement: DifferentiableOn 𝕜 f s
  proof: h.differentiable.differentiableOn

中文:
定理 differentiableOn
  条件: (h : 是BoundedLinear映射 𝕜 f)
  结论: DifferentiableOn 𝕜 f s
  证明: h.differentiable.differentiableOn

Depends on / 依赖: differentiable, differentiableOn, h.differentiable.differentiableOn
-/
theorem differentiableOn (h : IsBoundedLinearMap 𝕜 f) : DifferentiableOn 𝕜 f s :=
  h.differentiable.differentiableOn

end IsBoundedLinearMap
