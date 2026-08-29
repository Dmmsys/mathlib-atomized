/-
Copyright (c) 2023 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Linear
public import Mathlib.LinearAlgebra.AffineSpace.AffineMap
/-!
# Derivatives of affine maps

In this file we prove formulas for one-dimensional derivatives of affine maps `f : 𝕜 →ᵃ[𝕜] E`. We
also specialise some of these results to `AffineMap.lineMap` because it is useful to transfer MVT
from dimension 1 to a domain in higher dimension.

## TODO

Add theorems about `deriv`s and `fderiv`s of `ContinuousAffineMap`s once they will be ported to
Mathlib 4.

## Keywords

affine map, derivative, differentiability
-/

public section

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  (f : 𝕜 ->ᵃ[𝕜] E) {a b : E} {L : Filter (𝕜 × 𝕜)} {s : Set 𝕜} {x : 𝕜}

namespace AffineMap

/--
theorem `hasDerivAtFilter` / 定理 `hasDerivAtFilter`

English:
theorem hasDerivAtFilter
  statement: HasDerivAtFilter f (f.linear 1) L
  proof: by
  rw [f.decomp]
  exact f.linear.hasDerivAtFilter.add_const (f 0)

中文:
定理 hasDerivAtFilter
  结论: HasDerivAtFilter f (f.linear 1) L
  证明: by
  rw [f.decomp]
  exact f.linear.hasDerivAtFilter.add_const (f 0)

Depends on / 依赖: add_const, decomp, f.decomp, f.linear.hasDerivAtFilter.add_const, hasDerivAtFilter, linear
-/
theorem hasDerivAtFilter : HasDerivAtFilter f (f.linear 1) L := by
  rw [f.decomp]
  exact f.linear.hasDerivAtFilter.add_const (f 0)

/--
theorem `hasStrictDerivAt` / 定理 `hasStrictDerivAt`

English:
theorem hasStrictDerivAt
  statement: HasStrictDerivAt f (f.linear 1) x
  proof: f.hasDerivAtFilter

中文:
定理 hasStrictDerivAt
  结论: HasStrictDerivAt f (f.linear 1) x
  证明: f.hasDerivAtFilter

Depends on / 依赖: f.hasDerivAtFilter, hasDerivAtFilter
-/
theorem hasStrictDerivAt : HasStrictDerivAt f (f.linear 1) x := f.hasDerivAtFilter
/--
theorem `hasDerivWithinAt` / 定理 `hasDerivWithinAt`

English:
theorem hasDerivWithinAt
  statement: HasDerivWithinAt f (f.linear 1) s x
  proof: f.hasDerivAtFilter

中文:
定理 hasDerivWithinAt
  结论: HasDerivWithinAt f (f.linear 1) s x
  证明: f.hasDerivAtFilter

Depends on / 依赖: f.hasDerivAtFilter, hasDerivAtFilter
-/
theorem hasDerivWithinAt : HasDerivWithinAt f (f.linear 1) s x := f.hasDerivAtFilter
/--
theorem `hasDerivAt` / 定理 `hasDerivAt`

English:
theorem hasDerivAt
  statement: HasDerivAt f (f.linear 1) x
  proof: f.hasDerivAtFilter

中文:
定理 hasDerivAt
  结论: HasDerivAt f (f.linear 1) x
  证明: f.hasDerivAtFilter

Depends on / 依赖: f.hasDerivAtFilter, hasDerivAtFilter
-/
theorem hasDerivAt : HasDerivAt f (f.linear 1) x := f.hasDerivAtFilter

/--
theorem `derivWithin` / 定理 `derivWithin`

English:
theorem derivWithin
  given: (hs : UniqueDiffWithinAt 𝕜 s x)
  proof: f.hasDerivWithinAt.derivWithin hs

中文:
定理 derivWithin
  条件: (hs : UniqueDiffWithinAt 𝕜 s x)
  证明: f.hasDerivWithinAt.derivWithin hs
-/
protected theorem derivWithin (hs : UniqueDiffWithinAt 𝕜 s x) :
    derivWithin f s x = f.linear 1 :=
  f.hasDerivWithinAt.derivWithin hs

/--
theorem `deriv` / 定理 `deriv`

English:
theorem deriv
  statement: deriv f x = f.linear 1
  proof: f.hasDerivAt.deriv

中文:
定理 deriv
  结论: deriv f x = f.linear 1
  证明: f.hasDerivAt.deriv
-/
@[simp] protected theorem deriv : deriv f x = f.linear 1 := f.hasDerivAt.deriv

/--
theorem `differentiableAt` / 定理 `differentiableAt`

English:
theorem differentiableAt
  statement: DifferentiableAt 𝕜 f x
  proof: f.hasDerivAt.differentiableAt

中文:
定理 differentiableAt
  结论: DifferentiableAt 𝕜 f x
  证明: f.hasDerivAt.differentiableAt
-/
protected theorem differentiableAt : DifferentiableAt 𝕜 f x := f.hasDerivAt.differentiableAt
/--
theorem `differentiable` / 定理 `differentiable`

English:
theorem differentiable
  statement: Differentiable 𝕜 f
  proof: fun _ => f.differentiableAt

中文:
定理 differentiable
  结论: Differentiable 𝕜 f
  证明: fun _ => f.differentiableAt
-/
protected theorem differentiable : Differentiable 𝕜 f := fun _ => f.differentiableAt

/--
theorem `differentiableWithinAt` / 定理 `differentiableWithinAt`

English:
theorem differentiableWithinAt
  statement: DifferentiableWithinAt 𝕜 f s x
  proof: f.differentiableAt.differentiableWithinAt

中文:
定理 differentiableWithinAt
  结论: DifferentiableWithinAt 𝕜 f s x
  证明: f.differentiableAt.differentiableWithinAt
-/
protected theorem differentiableWithinAt : DifferentiableWithinAt 𝕜 f s x :=
  f.differentiableAt.differentiableWithinAt

/--
theorem `differentiableOn` / 定理 `differentiableOn`

English:
theorem differentiableOn
  statement: DifferentiableOn 𝕜 f s
  proof: fun _ _ => f.differentiableWithinAt

中文:
定理 differentiableOn
  结论: DifferentiableOn 𝕜 f s
  证明: fun _ _ => f.differentiableWithinAt
-/
protected theorem differentiableOn : DifferentiableOn 𝕜 f s := fun _ _ => f.differentiableWithinAt

/-!
### Line map

In this section we specialize some lemmas to `AffineMap.lineMap` because this map is very useful to
deduce higher-dimensional lemmas from one-dimensional versions.
-/

set_option backward.isDefEq.respectTransparency false in
/--
theorem `hasStrictDerivAt_lineMap` / 定理 `hasStrictDerivAt_lineMap`

English:
theorem hasStrictDerivAt_lineMap
  statement: HasStrictDerivAt (lineMap a b) (b - a) x
  proof: by
  simpa using (lineMap a b : 𝕜 ->ᵃ[𝕜] E).hasStrictDerivAt

中文:
定理 hasStrictDerivAt_lineMap
  结论: HasStrictDerivAt (lineMap a b) (b - a) x
  证明: by
  simpa using (lineMap a b : 𝕜 ->ᵃ[𝕜] E).hasStrictDerivAt

Depends on / 依赖: hasStrictDerivAt, lineMap
-/
theorem hasStrictDerivAt_lineMap : HasStrictDerivAt (lineMap a b) (b - a) x := by
  simpa using (lineMap a b : 𝕜 ->ᵃ[𝕜] E).hasStrictDerivAt

set_option backward.isDefEq.respectTransparency false in
/--
theorem `hasDerivAt_lineMap` / 定理 `hasDerivAt_lineMap`

English:
theorem hasDerivAt_lineMap
  statement: HasDerivAt (lineMap a b) (b - a) x
  proof: hasStrictDerivAt_lineMap.hasDerivAt

中文:
定理 hasDerivAt_lineMap
  结论: HasDerivAt (lineMap a b) (b - a) x
  证明: hasStrictDerivAt_lineMap.hasDerivAt

Depends on / 依赖: hasDerivAt, hasStrictDerivAt_lineMap, hasStrictDerivAt_lineMap.hasDerivAt
-/
theorem hasDerivAt_lineMap : HasDerivAt (lineMap a b) (b - a) x :=
  hasStrictDerivAt_lineMap.hasDerivAt

set_option backward.isDefEq.respectTransparency false in
/--
theorem `hasDerivWithinAt_lineMap` / 定理 `hasDerivWithinAt_lineMap`

English:
theorem hasDerivWithinAt_lineMap
  statement: HasDerivWithinAt (lineMap a b) (b - a) s x
  proof: hasDerivAt_lineMap.hasDerivWithinAt

中文:
定理 hasDerivWithinAt_lineMap
  结论: HasDerivWithinAt (lineMap a b) (b - a) s x
  证明: hasDerivAt_lineMap.hasDerivWithinAt

Depends on / 依赖: hasDerivAt_lineMap, hasDerivAt_lineMap.hasDerivWithinAt, hasDerivWithinAt
-/
theorem hasDerivWithinAt_lineMap : HasDerivWithinAt (lineMap a b) (b - a) s x :=
  hasDerivAt_lineMap.hasDerivWithinAt

end AffineMap
