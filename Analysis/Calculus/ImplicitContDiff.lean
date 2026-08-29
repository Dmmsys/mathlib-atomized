/-
Copyright (c) 2025 Winston Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin
-/
module

public import Mathlib.Analysis.Calculus.ImplicitFunction.ProdDomain
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

/-!
# Implicit function theorem

In this file, we apply the generalised implicit function theorem to the more familiar case and show
that the implicit function preserves the smoothness class of the implicit equation.

Let `E₁`, `E₂`, and `F` be real or complex Banach spaces. Let `f : E₁ × E₂ → F` be a function that
is $C^n$ at a point `(u₁, u₂) : E₁ × E₂`, where `n ≥ 1`. Let `f'` be the derivative of `f` at
`(u₁, u₂)`. If the map `y ↦ f' (0, y)` is a Banach space isomorphism, then there exists a function
`ψ : E₁ → E₂` such that `ψ u₁ = u₂`, and `f (x, ψ x) = f (u₁, u₂)` holds for all `x` in a
neighbourhood of `u₁`. Furthermore, `ψ` is $C^n$ at `u₁`.

## Tags

implicit function, inverse function
-/

public section

variable {𝕜 : Type*} [RCLike 𝕜]
  {E₁ : Type*} [NormedAddCommGroup E₁] [NormedSpace 𝕜 E₁] [CompleteSpace E₁]
  {E₂ : Type*} [NormedAddCommGroup E₂] [NormedSpace 𝕜 E₂] [CompleteSpace E₂]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]

open scoped Topology ContDiff

namespace ImplicitFunctionData

/--
theorem `contDiffAt_implicitFunction` / 定理 `contDiffAt_implicitFunction`

English:
theorem contDiffAt_implicitFunction
  statement: {φ : ImplicitFunctionData 𝕜 E₁ E₂ F} {n : Nat∞ω}
  proof: by
  rw [implicitFunction_def]; rw [Function.uncurry_curry]; rw [← HasStrictFDerivAt.localInverse_def]
  refine ContDiffAt.to_localInverse ?_ (φ.hasStrictFDerivAt.hasFDerivAt) pn
  convert! hl.prodMk hr <;> simp

中文:
定理 contDiffAt_implicitFunction
  结论: {φ : ImplicitFunctionData 𝕜 E₁ E₂ F} {n : 自然数∞ω}
  证明: by
  rw [implicitFunction_def]; rw [Function.uncurry_curry]; rw [← HasStrictFDerivAt.localInverse_def]
  refine ContDiffAt.to_localInverse ?_ (φ.hasStrictFDerivAt.hasFDerivAt) pn
  convert! hl.prodMk hr <;> simp

Depends on / 依赖: ContDiffAt, ContDiffAt.to_localInverse, Function, Function.uncurry_curry, HasStrictFDerivAt, HasStrictFDerivAt.localInverse_def, convert, hasFDerivAt, hasStrictFDerivAt, hasStrictFDerivAt.hasFDerivAt, hl.prodMk, implicitFunction_def, localInverse_def, prodMk, to_localInverse, uncurry_curry
-/
theorem contDiffAt_implicitFunction {φ : ImplicitFunctionData 𝕜 E₁ E₂ F} {n : Nat∞ω}
    (hl : ContDiffAt 𝕜 n φ.leftFun φ.pt) (hr : ContDiffAt 𝕜 n φ.rightFun φ.pt) (pn : n != 0) :
    ContDiffAt 𝕜 n φ.implicitFunction.uncurry (φ.prodFun φ.pt) := by
  rw [implicitFunction_def]; rw [Function.uncurry_curry]; rw [← HasStrictFDerivAt.localInverse_def]
  refine ContDiffAt.to_localInverse ?_ (φ.hasStrictFDerivAt.hasFDerivAt) pn
  convert! hl.prodMk hr <;> simp

end ImplicitFunctionData

namespace ContDiffAt

variable {u : E₁ × E₂} {f : E₁ × E₂ -> F} {n : Nat∞ω}

/--
Definition of `implicitFunction` / `implicitFunction` 的定义

English:
definition implicitFunction
  body: (cdf.hasStrictFDerivAt pn).implicitFunctionOfProdDomain if₂

中文:
定义 implicitFunction
  定义体: (cdf.hasStrictFDerivAt pn).implicitFunctionOfProdDomain if₂

Depends on / 依赖: cdf.hasStrictFDerivAt, hasStrictFDerivAt, implicitFunctionOfProdDomain
-/
noncomputable def implicitFunction
    (cdf : ContDiffAt 𝕜 n f u) (pn : n != 0) (if₂ : (fderiv 𝕜 f u ∘L .inr 𝕜 E₁ E₂).IsInvertible) :
    E₁ -> E₂ :=
  (cdf.hasStrictFDerivAt pn).implicitFunctionOfProdDomain if₂

/--
theorem `implicitFunction_def` / 定理 `implicitFunction_def`

English:
theorem implicitFunction_def
  proof: by
  rfl

中文:
定理 implicitFunction_def
  证明: by
  rfl
-/
theorem implicitFunction_def
    (cdf : ContDiffAt 𝕜 n f u) (pn : n != 0) (if₂ : (fderiv 𝕜 f u ∘L .inr 𝕜 E₁ E₂).IsInvertible) :
    cdf.implicitFunction pn if₂ = (cdf.hasStrictFDerivAt pn).implicitFunctionOfProdDomain if₂ := by
  rfl

/--
theorem `implicitFunction_apply_self` / 定理 `implicitFunction_apply_self`

English:
theorem implicitFunction_apply_self
  proof: eq_of_tendsto_nhds ((cdf.hasStrictFDerivAt pn).tendsto_implicitFunctionOfProdDomain if₂)

中文:
定理 implicitFunction_apply_self
  证明: eq_of_tendsto_nhds ((cdf.hasStrictFDerivAt pn).tendsto_implicitFunctionOfProdDomain if₂)

Depends on / 依赖: cdf.hasStrictFDerivAt, eq_of_tendsto_nhds, hasStrictFDerivAt, tendsto_implicitFunctionOfProdDomain
-/
theorem implicitFunction_apply_self
    (cdf : ContDiffAt 𝕜 n f u) (pn : n != 0) (if₂ : (fderiv 𝕜 f u ∘L .inr 𝕜 E₁ E₂).IsInvertible) :
    cdf.implicitFunction pn if₂ u.1 = u.2 :=
  eq_of_tendsto_nhds ((cdf.hasStrictFDerivAt pn).tendsto_implicitFunctionOfProdDomain if₂)

/--
theorem `eventually_apply_implicitFunction` / 定理 `eventually_apply_implicitFunction`

English:
theorem eventually_apply_implicitFunction
  proof: (cdf.hasStrictFDerivAt pn).eventually_apply_implicitFunctionOfProdDomain if₂

中文:
定理 eventually_apply_implicitFunction
  证明: (cdf.hasStrictFDerivAt pn).eventually_apply_implicitFunctionOfProdDomain if₂

Depends on / 依赖: cdf.hasStrictFDerivAt, eventually_apply_implicitFunctionOfProdDomain, hasStrictFDerivAt
-/
theorem eventually_apply_implicitFunction
    (cdf : ContDiffAt 𝕜 n f u) (pn : n != 0) (if₂ : (fderiv 𝕜 f u ∘L .inr 𝕜 E₁ E₂).IsInvertible) :
    forallᶠ x in 𝓝 u.1, f (x, cdf.implicitFunction pn if₂ x) = f u :=
  (cdf.hasStrictFDerivAt pn).eventually_apply_implicitFunctionOfProdDomain if₂

/--
theorem `eventually_apply_eq_iff_implicitFunction` / 定理 `eventually_apply_eq_iff_implicitFunction`

English:
theorem eventually_apply_eq_iff_implicitFunction
  proof: (cdf.hasStrictFDerivAt pn).eventually_apply_eq_iff_implicitFunctionOfProdDomain if₂

中文:
定理 eventually_apply_eq_iff_implicitFunction
  证明: (cdf.hasStrictFDerivAt pn).eventually_apply_eq_iff_implicitFunctionOfProdDomain if₂

Depends on / 依赖: cdf.hasStrictFDerivAt, eventually_apply_eq_iff_implicitFunctionOfProdDomain, hasStrictFDerivAt
-/
theorem eventually_apply_eq_iff_implicitFunction
    (cdf : ContDiffAt 𝕜 n f u) (pn : n != 0) (if₂ : (fderiv 𝕜 f u ∘L .inr 𝕜 E₁ E₂).IsInvertible) :
    forallᶠ v in 𝓝 u, f v = f u ↔ cdf.implicitFunction pn if₂ v.1 = v.2 :=
  (cdf.hasStrictFDerivAt pn).eventually_apply_eq_iff_implicitFunctionOfProdDomain if₂

/--
theorem `hasStrictFDerivAt_implicitFunction` / 定理 `hasStrictFDerivAt_implicitFunction`

English:
theorem hasStrictFDerivAt_implicitFunction
  proof: (cdf.hasStrictFDerivAt pn).hasStrictFDerivAt_implicitFunctionOfProdDomain if₂

中文:
定理 hasStrictFDerivAt_implicitFunction
  证明: (cdf.hasStrictFDerivAt pn).hasStrictFDerivAt_implicitFunctionOfProdDomain if₂

Depends on / 依赖: cdf.hasStrictFDerivAt, hasStrictFDerivAt, hasStrictFDerivAt_implicitFunctionOfProdDomain
-/
theorem hasStrictFDerivAt_implicitFunction
    (cdf : ContDiffAt 𝕜 n f u) (pn : n != 0) (if₂ : (fderiv 𝕜 f u ∘L .inr 𝕜 E₁ E₂).IsInvertible) :
    HasStrictFDerivAt (cdf.implicitFunction pn if₂)
      (-(fderiv 𝕜 f u ∘L .inr 𝕜 E₁ E₂).inverse ∘L (fderiv 𝕜 f u ∘L .inl 𝕜 E₁ E₂)) u.1 :=
  (cdf.hasStrictFDerivAt pn).hasStrictFDerivAt_implicitFunctionOfProdDomain if₂

/--
theorem `contDiffAt_implicitFunction` / 定理 `contDiffAt_implicitFunction`

English:
theorem contDiffAt_implicitFunction
  proof: by
  rw [ContDiffAt.implicitFunction_def]; rw [HasStrictFDerivAt.implicitFunctionOfProdDomain_def]
  set φ := (cdf.hasStrictFDerivAt pn).implicitFunctionDataOfProdDomain if₂
  have : ContDiffAt 𝕜 n φ.implicitFunction.uncurry (f u, u.1) := by
    simpa [φ] using φ.contDiffAt_implicitFunction
      (b

中文:
定理 contDiffAt_implicitFunction
  证明: by
  rw [ContDiffAt.implicitFunction_def]; rw [HasStrictFDerivAt.implicitFunctionOfProdDomain_def]
  set φ := (cdf.hasStrictFDerivAt pn).implicitFunctionDataOfProdDomain if₂
  have : ContDiffAt 𝕜 n φ.implicitFunction.uncurry (f u, u.1) := by
    simpa [φ] using φ.contDiffAt_implicitFunction
      (b

Depends on / 依赖: ContDiffAt, ContDiffAt.implicitFunction_def, HasStrictFDerivAt, HasStrictFDerivAt.implicitFunctionOfProdDomain_def, cdf.hasStrictFDerivAt, contDiffAt_fst, contDiffAt_implicitFunction, fun_prop, hasStrictFDerivAt, implicitFunction, implicitFunction.uncurry, implicitFunctionDataOfProdDomain, implicitFunctionOfProdDomain_def, implicitFunction_def, uncurry
-/
theorem contDiffAt_implicitFunction
    (cdf : ContDiffAt 𝕜 n f u) (pn : n != 0) (if₂ : (fderiv 𝕜 f u ∘L .inr 𝕜 E₁ E₂).IsInvertible) :
    ContDiffAt 𝕜 n (cdf.implicitFunction pn if₂) u.1 := by
  rw [ContDiffAt.implicitFunction_def]; rw [HasStrictFDerivAt.implicitFunctionOfProdDomain_def]
  set φ := (cdf.hasStrictFDerivAt pn).implicitFunctionDataOfProdDomain if₂
  have : ContDiffAt 𝕜 n φ.implicitFunction.uncurry (f u, u.1) := by
    simpa [φ] using φ.contDiffAt_implicitFunction
      (by simpa [φ] using cdf) (by simpa [φ] using contDiffAt_fst) pn
  fun_prop

end ContDiffAt

/-- A predicate stating the sufficient conditions on an implicit equation `f : E₁ × E₂ → F` that
will lead to a $C^n$ implicit function `ψ : E₁ → E₂`. -/
@[deprecated "ContDiffAt.implicitFunction does not require this" (since := "2026-01-27")]
/--
Definition of `IsContDiffImplicitAt` / `IsContDiffImplicitAt` 的定义

English:
structure IsContDiffImplicitAt
  parameters: (n : Nat∞ω) (f : E₁ × E₂ -> F) (f' : E₁ × E₂ ->L[𝕜] F)
  axioms and operations (4):
    - hasFDerivAt : HasFDerivAt f f' u
    - contDiffAt : ContDiffAt 𝕜 n f u
    - bijective : Function.Bijective (f'.comp (ContinuousLinearMap.inr 𝕜 E₁ E₂))
    - ne_zero : n != 0

中文:
结构 是余ntDiffImplicitAt
  参数: (n : 自然数∞ω) (f : E₁ × E₂ -> F) (f' : E₁ × E₂ ->L[𝕜] F)
  公理与运算 (4 个):
    - hasFDerivAt : 在点处Fréchet可导 f f' u
    - contDiffAt : ContDiffAt 𝕜 n f u
    - bijective : 函数.双射 (f'.comp (连续线性映射.inr 𝕜 E₁ E₂))
    - ne_zero : n != 0
-/
structure IsContDiffImplicitAt (n : Nat∞ω) (f : E₁ × E₂ -> F) (f' : E₁ × E₂ ->L[𝕜] F)
    (u : E₁ × E₂) : Prop where
  hasFDerivAt : HasFDerivAt f f' u
  contDiffAt : ContDiffAt 𝕜 n f u
  bijective : Function.Bijective (f'.comp (ContinuousLinearMap.inr 𝕜 E₁ E₂))
  ne_zero : n != 0

namespace IsContDiffImplicitAt

@[deprecated (since := "2026-01-27")]
alias implicitFunction := ContDiffAt.implicitFunction

@[deprecated (since := "2026-01-27")]
alias implicitFunction_def := ContDiffAt.implicitFunction_def

@[deprecated (since := "2026-01-27")]
alias apply_implicitFunction := ContDiffAt.eventually_apply_implicitFunction

@[deprecated (since := "2026-01-27")]
alias eventually_implicitFunction_apply_eq := ContDiffAt.eventually_apply_eq_iff_implicitFunction

@[deprecated (since := "2026-01-27")]
alias contDiffAt_implicitFunction := ContDiffAt.contDiffAt_implicitFunction

end IsContDiffImplicitAt

end
