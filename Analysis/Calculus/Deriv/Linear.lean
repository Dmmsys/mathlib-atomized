/-
Copyright (c) 2019 Gabriel Ebner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, Yury Kudryashov
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Linear

/-!
# Derivatives of continuous linear maps from the base field

In this file we prove that `f : 𝕜 →L[𝕜] E` (or `f : 𝕜 →ₗ[𝕜] E`) has derivative `f 1`.

For a more detailed overview of one-dimensional derivatives in mathlib, see the module docstring of
`Analysis/Calculus/Deriv/Basic`.

## Keywords

derivative, linear map
-/

public section


universe u v w

open Topology Filter

open Filter Asymptotics Set

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]
variable {F : Type v} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {E : Type w} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {x : 𝕜}
variable {s : Set 𝕜}
variable {L : Filter (𝕜 × 𝕜)}

section ContinuousLinearMap

/-! ### Derivative of continuous linear maps -/

variable (e : 𝕜 ->L[𝕜] F)

/--
theorem `ContinuousLinearMap.hasDerivAtFilter` / 定理 `ContinuousLinearMap.hasDerivAtFilter`

English:
theorem ContinuousLinearMap.hasDerivAtFilter
  statement: HasDerivAtFilter e (e 1) L
  proof: e.hasFDerivAtFilter.hasDerivAtFilter

中文:
定理 连续线性映射.hasDerivAtFilter
  结论: HasDerivAtFilter e (e 1) L
  证明: e.hasFDerivAtFilter.hasDerivAtFilter
-/
protected theorem ContinuousLinearMap.hasDerivAtFilter : HasDerivAtFilter e (e 1) L :=
  e.hasFDerivAtFilter.hasDerivAtFilter

/--
theorem `ContinuousLinearMap.hasStrictDerivAt` / 定理 `ContinuousLinearMap.hasStrictDerivAt`

English:
theorem ContinuousLinearMap.hasStrictDerivAt
  statement: HasStrictDerivAt e (e 1) x
  proof: e.hasDerivAtFilter

中文:
定理 连续线性映射.hasStrictDerivAt
  结论: HasStrictDerivAt e (e 1) x
  证明: e.hasDerivAtFilter
-/
protected theorem ContinuousLinearMap.hasStrictDerivAt : HasStrictDerivAt e (e 1) x :=
  e.hasDerivAtFilter

/--
theorem `ContinuousLinearMap.hasDerivAt` / 定理 `ContinuousLinearMap.hasDerivAt`

English:
theorem ContinuousLinearMap.hasDerivAt
  statement: HasDerivAt e (e 1) x
  proof: e.hasDerivAtFilter

中文:
定理 连续线性映射.hasDerivAt
  结论: 在点处可导 e (e 1) x
  证明: e.hasDerivAtFilter
-/
protected theorem ContinuousLinearMap.hasDerivAt : HasDerivAt e (e 1) x :=
  e.hasDerivAtFilter

/--
theorem `ContinuousLinearMap.hasDerivWithinAt` / 定理 `ContinuousLinearMap.hasDerivWithinAt`

English:
theorem ContinuousLinearMap.hasDerivWithinAt
  statement: HasDerivWithinAt e (e 1) s x
  proof: e.hasDerivAtFilter

@[simp]

中文:
定理 连续线性映射.hasDerivWithinAt
  结论: HasDerivWithinAt e (e 1) s x
  证明: e.hasDerivAtFilter

@[simp]
-/
protected theorem ContinuousLinearMap.hasDerivWithinAt : HasDerivWithinAt e (e 1) s x :=
  e.hasDerivAtFilter

@[simp]
/--
theorem `ContinuousLinearMap.deriv` / 定理 `ContinuousLinearMap.deriv`

English:
theorem ContinuousLinearMap.deriv
  statement: deriv e x = e 1
  proof: e.hasDerivAt.deriv

中文:
定理 连续线性映射.deriv
  结论: deriv e x = e 1
  证明: e.hasDerivAt.deriv
-/
protected theorem ContinuousLinearMap.deriv : deriv e x = e 1 :=
  e.hasDerivAt.deriv

/--
theorem `ContinuousLinearMap.derivWithin` / 定理 `ContinuousLinearMap.derivWithin`

English:
theorem ContinuousLinearMap.derivWithin
  given: (hxs : UniqueDiffWithinAt 𝕜 s x)
  proof: e.hasDerivWithinAt.derivWithin hxs

中文:
定理 连续线性映射.derivWithin
  条件: (hxs : UniqueDiffWithinAt 𝕜 s x)
  证明: e.hasDerivWithinAt.derivWithin hxs
-/
protected theorem ContinuousLinearMap.derivWithin (hxs : UniqueDiffWithinAt 𝕜 s x) :
    derivWithin e s x = e 1 :=
  e.hasDerivWithinAt.derivWithin hxs

end ContinuousLinearMap

section LinearMap

/-! ### Derivative of bundled linear maps -/

variable (e : 𝕜 ->ₗ[𝕜] F)

/--
theorem `LinearMap.hasDerivAtFilter` / 定理 `LinearMap.hasDerivAtFilter`

English:
theorem LinearMap.hasDerivAtFilter
  statement: HasDerivAtFilter e (e 1) L
  proof: e.toContinuousLinearMap₁.hasDerivAtFilter

中文:
定理 线性映射.hasDerivAtFilter
  结论: HasDerivAtFilter e (e 1) L
  证明: e.toContinuousLinearMap₁.hasDerivAtFilter

Depends on / 依赖: Complex.conjCAE_apply, Complex.conj_im, Complex.star_def, abs_of_nonpos, abs_of_pos, conjCAE_apply, conj_im, moebius_im, neg_div, neg_inj, neg_mul, not_lt, not_lt.mp, smulAux, split_ifs, star_def
-/
protected theorem LinearMap.hasDerivAtFilter : HasDerivAtFilter e (e 1) L :=
  e.toContinuousLinearMap₁.hasDerivAtFilter

/--
theorem `LinearMap.hasStrictDerivAt` / 定理 `LinearMap.hasStrictDerivAt`

English:
theorem LinearMap.hasStrictDerivAt
  statement: HasStrictDerivAt e (e 1) x
  proof: e.hasDerivAtFilter

中文:
定理 线性映射.hasStrictDerivAt
  结论: HasStrictDerivAt e (e 1) x
  证明: e.hasDerivAtFilter
-/
protected theorem LinearMap.hasStrictDerivAt : HasStrictDerivAt e (e 1) x :=
  e.hasDerivAtFilter

/--
theorem `LinearMap.hasDerivAt` / 定理 `LinearMap.hasDerivAt`

English:
theorem LinearMap.hasDerivAt
  statement: HasDerivAt e (e 1) x
  proof: e.hasDerivAtFilter

中文:
定理 线性映射.hasDerivAt
  结论: 在点处可导 e (e 1) x
  证明: e.hasDerivAtFilter
-/
protected theorem LinearMap.hasDerivAt : HasDerivAt e (e 1) x :=
  e.hasDerivAtFilter

/--
theorem `LinearMap.hasDerivWithinAt` / 定理 `LinearMap.hasDerivWithinAt`

English:
theorem LinearMap.hasDerivWithinAt
  statement: HasDerivWithinAt e (e 1) s x
  proof: e.hasDerivAtFilter

@[simp]

中文:
定理 线性映射.hasDerivWithinAt
  结论: HasDerivWithinAt e (e 1) s x
  证明: e.hasDerivAtFilter

@[simp]
-/
protected theorem LinearMap.hasDerivWithinAt : HasDerivWithinAt e (e 1) s x :=
  e.hasDerivAtFilter

@[simp]
/--
theorem `LinearMap.deriv` / 定理 `LinearMap.deriv`

English:
theorem LinearMap.deriv
  statement: deriv e x = e 1
  proof: e.hasDerivAt.deriv

中文:
定理 线性映射.deriv
  结论: deriv e x = e 1
  证明: e.hasDerivAt.deriv
-/
protected theorem LinearMap.deriv : deriv e x = e 1 :=
  e.hasDerivAt.deriv

/--
theorem `LinearMap.derivWithin` / 定理 `LinearMap.derivWithin`

English:
theorem LinearMap.derivWithin
  given: (hxs : UniqueDiffWithinAt 𝕜 s x)
  proof: e.hasDerivWithinAt.derivWithin hxs

中文:
定理 线性映射.derivWithin
  条件: (hxs : UniqueDiffWithinAt 𝕜 s x)
  证明: e.hasDerivWithinAt.derivWithin hxs
-/
protected theorem LinearMap.derivWithin (hxs : UniqueDiffWithinAt 𝕜 s x) :
    derivWithin e s x = e 1 :=
  e.hasDerivWithinAt.derivWithin hxs

end LinearMap
