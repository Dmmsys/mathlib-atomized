/-
Copyright (c) 2024 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Analysis.Calculus.LineDeriv.Basic
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.LinearAlgebra.QuadraticForm.Basic

/-!
# Quadratic forms are line (Gateaux) differentiable

In this file we prove that a quadratic form is line differentiable,
with the line derivative given by the polar bilinear form.
Note that this statement does not need topology on the domain.
In particular, it applies to discontinuous quadratic forms on infinite-dimensional spaces.
-/

public section

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [AddCommGroup E] [Module 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

namespace QuadraticMap

/--
theorem `hasLineDerivAt` / 定理 `hasLineDerivAt`

English:
theorem hasLineDerivAt
  given: (f : QuadraticMap 𝕜 E F) (a b : E)
  proof: by
  simpa [HasLineDerivAt, QuadraticMap.map_add, f.map_smul] using!
    ((hasDerivAt_const (0 : 𝕜) (f a)).add <|
      ((hasDerivAt_id 0).mul (hasDerivAt_id 0)).smul (hasDerivAt_const 0 (f b))).add
      ((hasDerivAt_id 0).smul (hasDerivAt_const 0 (polar f a b)))

中文:
定理 hasLineDerivAt
  条件: (f : QuadraticMap 𝕜 E F) (a b : E)
  证明: by
  simpa [HasLineDerivAt, QuadraticMap.map_add, f.map_smul] using!
    ((hasDerivAt_const (0 : 𝕜) (f a)).add <|
      ((hasDerivAt_id 0).mul (hasDerivAt_id 0)).smul (hasDerivAt_const 0 (f b))).add
      ((hasDerivAt_id 0).smul (hasDerivAt_const 0 (polar f a b)))

Depends on / 依赖: HasLineDerivAt, QuadraticMap, QuadraticMap.map_add, f.map_smul, hasDerivAt_const, hasDerivAt_id, map_add, map_smul
-/
theorem hasLineDerivAt (f : QuadraticMap 𝕜 E F) (a b : E) :
    HasLineDerivAt 𝕜 f (polar f a b) a b := by
  simpa [HasLineDerivAt, QuadraticMap.map_add, f.map_smul] using!
    ((hasDerivAt_const (0 : 𝕜) (f a)).add <|
      ((hasDerivAt_id 0).mul (hasDerivAt_id 0)).smul (hasDerivAt_const 0 (f b))).add
      ((hasDerivAt_id 0).smul (hasDerivAt_const 0 (polar f a b)))

/--
theorem `lineDifferentiableAt` / 定理 `lineDifferentiableAt`

English:
theorem lineDifferentiableAt
  given: (f : QuadraticMap 𝕜 E F) (a b : E)
  statement: LineDifferentiableAt 𝕜 f a b
  proof: (f.hasLineDerivAt a b).lineDifferentiableAt

@[simp]

中文:
定理 lineDifferentiableAt
  条件: (f : QuadraticMap 𝕜 E F) (a b : E)
  结论: LineDifferentiableAt 𝕜 f a b
  证明: (f.hasLineDerivAt a b).lineDifferentiableAt

@[simp]

Depends on / 依赖: f.hasLineDerivAt, hasLineDerivAt, lineDifferentiableAt
-/
theorem lineDifferentiableAt (f : QuadraticMap 𝕜 E F) (a b : E) : LineDifferentiableAt 𝕜 f a b :=
  (f.hasLineDerivAt a b).lineDifferentiableAt

@[simp]
/--
theorem `lineDeriv` / 定理 `lineDeriv`

English:
theorem lineDeriv
  given: (f : QuadraticMap 𝕜 E F)
  statement: lineDeriv 𝕜 f = polar f
  proof: by
  ext a b
  exact (f.hasLineDerivAt a b).lineDeriv

中文:
定理 lineDeriv
  条件: (f : QuadraticMap 𝕜 E F)
  结论: lineDeriv 𝕜 f = polar f
  证明: by
  ext a b
  exact (f.hasLineDerivAt a b).lineDeriv
-/
protected theorem lineDeriv (f : QuadraticMap 𝕜 E F) : lineDeriv 𝕜 f = polar f := by
  ext a b
  exact (f.hasLineDerivAt a b).lineDeriv

end QuadraticMap
