/-
Copyright (c) 2025 A Tucker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: A Tucker
-/
module

public import Mathlib.Analysis.Calculus.ImplicitFunction.ProdDomain
public import Mathlib.Analysis.Calculus.FDeriv.Partial

/-!
# Implicit function theorem — curried bivariate

This specialization of the implicit function theorem applies to a curried bivariate function
`f : E₁ → E₂ → F` and assumes continuity of both its partial derivatives at `u : E₁ × E₂` as well as
invertibility of `f₂ u.1 u.2 : E₂ →L[𝕜] F` its partial derivative with respect to the second
argument.

It proves the existence of `ψ : E₁ → E₂` such that for `v` in a neighbourhood of `u` we have
`f v.1 v.2 = f u.1 u.2 ↔ ψ v.1 = v.2`. This is `implicitFunctionOfBivariate`. A formula for its
first derivative follows.

A similar specialization is made to an uncurried bivariate function by
`HasStrictFDerivAt.implicitFunctionOfProdDomain` in a sister file.

## Tags

implicit function
-/

public section

open Filter
open scoped Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [IsRCLikeNormedField 𝕜]
  {E₁ : Type*} [NormedAddCommGroup E₁] [NormedSpace 𝕜 E₁] [CompleteSpace E₁]
  {E₂ : Type*} [NormedAddCommGroup E₂] [NormedSpace 𝕜 E₂] [CompleteSpace E₂]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]

variable {u : E₁ × E₂}
  {f : E₁ -> E₂ -> F} {f₁ : E₁ -> E₂ -> E₁ ->L[𝕜] F} {f₂ : E₁ -> E₂ -> E₂ ->L[𝕜] F}
  (df₁ : forallᶠ v in 𝓝 u, HasFDerivAt (f · v.2) (f₁ v.1 v.2) v.1)
  (df₂ : forallᶠ v in 𝓝 u, HasFDerivAt (f v.1 ·) (f₂ v.1 v.2) v.2)
  (cf₁ : ContinuousAt ↿f₁ u) (cf₂ : ContinuousAt ↿f₂ u) (if₂u : (f₂ u.1 u.2).IsInvertible)

/--
Definition of `implicitFunctionOfBivariate` / `implicitFunctionOfBivariate` 的定义

English:
definition implicitFunctionOfBivariate
  signature: : E₁ -> E₂
  body: HasStrictFDerivAt.implicitFunctionOfProdDomain
    (hasStrictFDerivAt_uncurry_coprod df₁ df₂ cf₁ cf₂) (by simpa using! if₂u)

中文:
定义 implicitFunctionOfBivariate
  签名: : E₁ -> E₂
  定义体: HasStrictFDerivAt.implicitFunctionOfProdDomain
    (hasStrictFDerivAt_uncurry_coprod df₁ df₂ cf₁ cf₂) (by simpa using! if₂u)

Depends on / 依赖: HasStrictFDerivAt, HasStrictFDerivAt.implicitFunctionOfProdDomain, hasStrictFDerivAt_uncurry_coprod, implicitFunctionOfProdDomain
-/
noncomputable def implicitFunctionOfBivariate : E₁ -> E₂ :=
  HasStrictFDerivAt.implicitFunctionOfProdDomain
    (hasStrictFDerivAt_uncurry_coprod df₁ df₂ cf₁ cf₂) (by simpa using! if₂u)

/--
theorem `implicitFunctionOfBivariate_def` / 定理 `implicitFunctionOfBivariate_def`

English:
theorem implicitFunctionOfBivariate_def
  proof: by
  rfl

中文:
定理 implicitFunctionOfBivariate_def
  证明: by
  rfl
-/
theorem implicitFunctionOfBivariate_def :
    implicitFunctionOfBivariate df₁ df₂ cf₁ cf₂ if₂u =
      HasStrictFDerivAt.implicitFunctionOfProdDomain
        (hasStrictFDerivAt_uncurry_coprod df₁ df₂ cf₁ cf₂) (by simpa using! if₂u) := by
  rfl

/--
theorem `tendsto_implicitFunctionOfBivariate` / 定理 `tendsto_implicitFunctionOfBivariate`

English:
theorem tendsto_implicitFunctionOfBivariate
  proof: by
  simpa using! HasStrictFDerivAt.tendsto_implicitFunctionOfProdDomain
    (hasStrictFDerivAt_uncurry_coprod df₁ df₂ cf₁ cf₂) (by simpa using! if₂u)

中文:
定理 tendsto_implicitFunctionOfBivariate
  证明: by
  simpa using! HasStrictFDerivAt.tendsto_implicitFunctionOfProdDomain
    (hasStrictFDerivAt_uncurry_coprod df₁ df₂ cf₁ cf₂) (by simpa using! if₂u)

Depends on / 依赖: HasStrictFDerivAt, HasStrictFDerivAt.tendsto_implicitFunctionOfProdDomain, hasStrictFDerivAt_uncurry_coprod, tendsto_implicitFunctionOfProdDomain
-/
theorem tendsto_implicitFunctionOfBivariate :
    Tendsto (implicitFunctionOfBivariate df₁ df₂ cf₁ cf₂ if₂u) (𝓝 u.1) (𝓝 u.2) := by
  simpa using! HasStrictFDerivAt.tendsto_implicitFunctionOfProdDomain
    (hasStrictFDerivAt_uncurry_coprod df₁ df₂ cf₁ cf₂) (by simpa using! if₂u)

/--
theorem `eventually_apply_implicitFunctionOfBivariate` / 定理 `eventually_apply_implicitFunctionOfBivariate`

English:
theorem eventually_apply_implicitFunctionOfBivariate
  proof: by
  simpa using! HasStrictFDerivAt.eventually_apply_implicitFunctionOfProdDomain
    (hasStrictFDerivAt_uncurry_coprod df₁ df₂ cf₁ cf₂) (by simpa using! if₂u)

中文:
定理 eventually_apply_implicitFunctionOfBivariate
  证明: by
  simpa using! HasStrictFDerivAt.eventually_apply_implicitFunctionOfProdDomain
    (hasStrictFDerivAt_uncurry_coprod df₁ df₂ cf₁ cf₂) (by simpa using! if₂u)

Depends on / 依赖: HasStrictFDerivAt, HasStrictFDerivAt.eventually_apply_implicitFunctionOfProdDomain, eventually_apply_implicitFunctionOfProdDomain, hasStrictFDerivAt_uncurry_coprod
-/
theorem eventually_apply_implicitFunctionOfBivariate :
    forallᶠ x in 𝓝 u.1, f x (implicitFunctionOfBivariate df₁ df₂ cf₁ cf₂ if₂u x) = f u.1 u.2 := by
  simpa using! HasStrictFDerivAt.eventually_apply_implicitFunctionOfProdDomain
    (hasStrictFDerivAt_uncurry_coprod df₁ df₂ cf₁ cf₂) (by simpa using! if₂u)

/--
theorem `eventually_apply_eq_iff_implicitFunctionOfBivariate` / 定理 `eventually_apply_eq_iff_implicitFunctionOfBivariate`

English:
theorem eventually_apply_eq_iff_implicitFunctionOfBivariate
  proof: by
  simpa using! HasStrictFDerivAt.eventually_apply_eq_iff_implicitFunctionOfProdDomain
    (hasStrictFDerivAt_uncurry_coprod df₁ df₂ cf₁ cf₂) (by simpa using! if₂u)

中文:
定理 eventually_apply_eq_iff_implicitFunctionOfBivariate
  证明: by
  simpa using! HasStrictFDerivAt.eventually_apply_eq_iff_implicitFunctionOfProdDomain
    (hasStrictFDerivAt_uncurry_coprod df₁ df₂ cf₁ cf₂) (by simpa using! if₂u)

Depends on / 依赖: HasStrictFDerivAt, HasStrictFDerivAt.eventually_apply_eq_iff_implicitFunctionOfProdDomain, eventually_apply_eq_iff_implicitFunctionOfProdDomain, hasStrictFDerivAt_uncurry_coprod
-/
theorem eventually_apply_eq_iff_implicitFunctionOfBivariate :
    forallᶠ v in 𝓝 u,
      f v.1 v.2 = f u.1 u.2 ↔ implicitFunctionOfBivariate df₁ df₂ cf₁ cf₂ if₂u v.1 = v.2 := by
  simpa using! HasStrictFDerivAt.eventually_apply_eq_iff_implicitFunctionOfProdDomain
    (hasStrictFDerivAt_uncurry_coprod df₁ df₂ cf₁ cf₂) (by simpa using! if₂u)

/--
theorem `hasStrictFDerivAt_implicitFunctionOfBivariate` / 定理 `hasStrictFDerivAt_implicitFunctionOfBivariate`

English:
theorem hasStrictFDerivAt_implicitFunctionOfBivariate
  proof: by
  simpa using! HasStrictFDerivAt.hasStrictFDerivAt_implicitFunctionOfProdDomain
    (hasStrictFDerivAt_uncurry_coprod df₁ df₂ cf₁ cf₂) (by simpa using! if₂u)

中文:
定理 hasStrictFDerivAt_implicitFunctionOfBivariate
  证明: by
  simpa using! HasStrictFDerivAt.hasStrictFDerivAt_implicitFunctionOfProdDomain
    (hasStrictFDerivAt_uncurry_coprod df₁ df₂ cf₁ cf₂) (by simpa using! if₂u)

Depends on / 依赖: HasStrictFDerivAt, HasStrictFDerivAt.hasStrictFDerivAt_implicitFunctionOfProdDomain, hasStrictFDerivAt_implicitFunctionOfProdDomain, hasStrictFDerivAt_uncurry_coprod
-/
theorem hasStrictFDerivAt_implicitFunctionOfBivariate :
    HasStrictFDerivAt (implicitFunctionOfBivariate df₁ df₂ cf₁ cf₂ if₂u)
      (-(f₂ u.1 u.2).inverse ∘L f₁ u.1 u.2) u.1 := by
  simpa using! HasStrictFDerivAt.hasStrictFDerivAt_implicitFunctionOfProdDomain
    (hasStrictFDerivAt_uncurry_coprod df₁ df₂ cf₁ cf₂) (by simpa using! if₂u)

end
