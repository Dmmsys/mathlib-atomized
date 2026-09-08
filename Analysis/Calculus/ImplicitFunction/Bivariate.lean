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
  {f : E₁ → E₂ → F} {f₁ : E₁ → E₂ → E₁ →L[𝕜] F} {f₂ : E₁ → E₂ → E₂ →L[𝕜] F}
  (df₁ : ∀ᶠ v in 𝓝 u, HasFDerivAt (f · v.2) (f₁ v.1 v.2) v.1)
  (df₂ : ∀ᶠ v in 𝓝 u, HasFDerivAt (f v.1 ·) (f₂ v.1 v.2) v.2)
  (cf₁ : ContinuousAt ↿f₁ u) (cf₂ : ContinuousAt ↿f₂ u) (if₂u : (f₂ u.1 u.2).IsInvertible)

/-- Implicit function `ψ : E₁ → E₂` associated with the (curried) bivariate function
`f : E₁ → E₂ → F` at `u : E₁ × E₂`. -/
/-
**implicitFunctionOfBivariate** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：implicitFunctionOfBivariate : E₁ -> E₂
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `hasStrictFDerivAt_uncurry_coprod`：∀ {𝕜 : Type u_1} {E₁ : Type u_2} {E₂ :
 Type u_3} {F : Type u_4} [inst : NontriviallyNormedField 𝕜]   [inst_1 : NormedA
ddCommGroup E₁] [inst_…

--- 原说明 ---
Implicit function `ψ : E₁ → E₂` associated with the (curried) bivariate function
`f : E₁ → E₂ → F` at `u : E₁ × E₂`.
-/
noncomputable def implicitFunctionOfBivariate : E₁ → E₂ :=
  HasStrictFDerivAt.implicitFunctionOfProdDomain
    (hasStrictFDerivAt_uncurry_coprod df₁ df₂ cf₁ cf₂) (by simpa using! if₂u)
/-
**implicitFunctionOfBivariate_def** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：implicitFunctionOfBivariate_def : implicitFunctionOfBivariate df₁ df₂ cf₁ 
cf₂ if₂u = HasStrictFDerivAt.implicitFunctionOfProdDomain (hasStrictFDerivAt_unc
urry_coprod df₁ df₂ cf₁ cf₂) (by simpa using! if₂u)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
-/
theorem implicitFunctionOfBivariate_def :
    implicitFunctionOfBivariate df₁ df₂ cf₁ cf₂ if₂u =
      HasStrictFDerivAt.implicitFunctionOfProdDomain
        (hasStrictFDerivAt_uncurry_coprod df₁ df₂ cf₁ cf₂) (by simpa using! if₂u) := by
  rfl
/-
**tendsto_implicitFunctionOfBivariate** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_implicitFunctionOfBivariate : Tendsto (implicitFunctionOfBivariate
 df₁ df₂ cf₁ cf₂ if₂u) (𝓝 u.1) (𝓝 u.2)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `HasStrictFDerivAt.tendsto_implicitFunctionOfProdDomain`：tendsto_implicit
FunctionOfProdDomain (dfu : HasStrictFDerivAt f f'u u) (if₂u : (f'u ∘L .inr 𝕜 E₁
 E₂).IsInvertible) : Tendsto (dfu.implicitFu…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `hasStrictFDerivAt_uncurry_coprod`：∀ {𝕜 : Type u_1} {E₁ : Type u_2} {E₂ :
 Type u_3} {F : Type u_4} [inst : NontriviallyNormedField 𝕜]   [inst_1 : NormedA
ddCommGroup E₁] [inst_…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousLinearMap.coprod_comp_inr`：∀ {R : Type u_1} {M : Type u_3} {M₁
 : Type u_5} {M₂ : Type u_6} [inst : Semiring R] [inst_1 : TopologicalSpace M]  
 [inst_2 : TopologicalSpa…
-/
theorem tendsto_implicitFunctionOfBivariate :
    Tendsto (implicitFunctionOfBivariate df₁ df₂ cf₁ cf₂ if₂u) (𝓝 u.1) (𝓝 u.2) := by
  simpa using! HasStrictFDerivAt.tendsto_implicitFunctionOfProdDomain
    (hasStrictFDerivAt_uncurry_coprod df₁ df₂ cf₁ cf₂) (by simpa using! if₂u)
/-
**eventually_apply_implicitFunctionOfBivariate** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：eventually_apply_implicitFunctionOfBivariate : forallᶠ x in 𝓝 u.1, f x (im
plicitFunctionOfBivariate df₁ df₂ cf₁ cf₂ if₂u x) = f u.1 u.2
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `HasStrictFDerivAt.eventually_apply_implicitFunctionOfProdDomain`：eventua
lly_apply_implicitFunctionOfProdDomain (dfu : HasStrictFDerivAt f f'u u) (if₂u :
 (f'u ∘L .inr 𝕜 E₁ E₂).IsInvertible) : forallᶠ x in 𝓝…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `hasStrictFDerivAt_uncurry_coprod`：∀ {𝕜 : Type u_1} {E₁ : Type u_2} {E₂ :
 Type u_3} {F : Type u_4} [inst : NontriviallyNormedField 𝕜]   [inst_1 : NormedA
ddCommGroup E₁] [inst_…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousLinearMap.coprod_comp_inr`：∀ {R : Type u_1} {M : Type u_3} {M₁
 : Type u_5} {M₂ : Type u_6} [inst : Semiring R] [inst_1 : TopologicalSpace M]  
 [inst_2 : TopologicalSpa…
-/
theorem eventually_apply_implicitFunctionOfBivariate :
    ∀ᶠ x in 𝓝 u.1, f x (implicitFunctionOfBivariate df₁ df₂ cf₁ cf₂ if₂u x) = f u.1 u.2 := by
  simpa using! HasStrictFDerivAt.eventually_apply_implicitFunctionOfProdDomain
    (hasStrictFDerivAt_uncurry_coprod df₁ df₂ cf₁ cf₂) (by simpa using! if₂u)
/-
**eventually_apply_eq_iff_implicitFunctionOfBivariate** 是 Mathlib 中的一个定理，位于命名空间 
``。
形式化陈述：eventually_apply_eq_iff_implicitFunctionOfBivariate : forallᶠ v in 𝓝 u, f 
v.1 v.2 = f u.1 u.2 ↔ implicitFunctionOfBivariate df₁ df₂ cf₁ cf₂ if₂u v.1 = v.2
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `HasStrictFDerivAt.eventually_apply_eq_iff_implicitFunctionOfProdDomain`：
eventually_apply_eq_iff_implicitFunctionOfProdDomain (dfu : HasStrictFDerivAt f 
f'u u) (if₂u : (f'u ∘L .inr 𝕜 E₁ E₂).IsInvertible) : forallᶠ…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `hasStrictFDerivAt_uncurry_coprod`：∀ {𝕜 : Type u_1} {E₁ : Type u_2} {E₂ :
 Type u_3} {F : Type u_4} [inst : NontriviallyNormedField 𝕜]   [inst_1 : NormedA
ddCommGroup E₁] [inst_…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousLinearMap.coprod_comp_inr`：∀ {R : Type u_1} {M : Type u_3} {M₁
 : Type u_5} {M₂ : Type u_6} [inst : Semiring R] [inst_1 : TopologicalSpace M]  
 [inst_2 : TopologicalSpa…
-/
theorem eventually_apply_eq_iff_implicitFunctionOfBivariate :
    ∀ᶠ v in 𝓝 u,
      f v.1 v.2 = f u.1 u.2 ↔ implicitFunctionOfBivariate df₁ df₂ cf₁ cf₂ if₂u v.1 = v.2 := by
  simpa using! HasStrictFDerivAt.eventually_apply_eq_iff_implicitFunctionOfProdDomain
    (hasStrictFDerivAt_uncurry_coprod df₁ df₂ cf₁ cf₂) (by simpa using! if₂u)
/-
**hasStrictFDerivAt_implicitFunctionOfBivariate** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasStrictFDerivAt_implicitFunctionOfBivariate : HasStrictFDerivAt (implici
tFunctionOfBivariate df₁ df₂ cf₁ cf₂ if₂u) (-(f₂ u.1 u.2).inverse ∘L f₁ u.1 u.2)
 u.1
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `hasStrictFDerivAt_uncurry_coprod`：∀ {𝕜 : Type u_1} {E₁ : Type u_2} {E₂ :
 Type u_3} {F : Type u_4} [inst : NontriviallyNormedField 𝕜]   [inst_1 : NormedA
ddCommGroup E₁] [inst_…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousLinearMap.coprod_comp_inr`：∀ {R : Type u_1} {M : Type u_3} {M₁
 : Type u_5} {M₂ : Type u_6} [inst : Semiring R] [inst_1 : TopologicalSpace M]  
 [inst_2 : TopologicalSpa…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ContinuousLinearMap.comp.congr_simp`：∀ {R₁ : Type u_1} {R₂ : Type u_2} {
R₃ : Type u_3} [inst : Semiring R₁] [inst_1 : Semiring R₂] [inst_2 : Semiring R₃
]   {σ₁₂ : R₁ →+* R₂} {σ₂…
· 使用定理 `ContinuousLinearMap.coprod_comp_inl`：∀ {R : Type u_1} {M : Type u_3} {M₁
 : Type u_5} {M₂ : Type u_6} [inst : Semiring R] [inst_1 : TopologicalSpace M]  
 [inst_2 : TopologicalSpa…
· 使用定理 `HasStrictFDerivAt.hasStrictFDerivAt_implicitFunctionOfProdDomain`：hasStr
ictFDerivAt_implicitFunctionOfProdDomain (dfu : HasStrictFDerivAt f f'u u) (if₂u
 : (f'u ∘L .inr 𝕜 E₁ E₂).IsInvertible) : HasStrictFDer…
-/
theorem hasStrictFDerivAt_implicitFunctionOfBivariate :
    HasStrictFDerivAt (implicitFunctionOfBivariate df₁ df₂ cf₁ cf₂ if₂u)
      (-(f₂ u.1 u.2).inverse ∘L f₁ u.1 u.2) u.1 := by
  simpa using! HasStrictFDerivAt.hasStrictFDerivAt_implicitFunctionOfProdDomain
    (hasStrictFDerivAt_uncurry_coprod df₁ df₂ cf₁ cf₂) (by simpa using! if₂u)

end

