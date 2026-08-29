/-
Copyright (c) 2025 A Tucker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: A Tucker
-/
module

public import Mathlib.Analysis.Calculus.Implicit

/-!
# Implicit function theorem — domain a product space

This specialization of the implicit function theorem applies to an uncurried bivariate function
`f : E₁ × E₂ → F` and assumes strict differentiability of `f` at `u : E₁ × E₂` as well as
invertibility of `f₂u : E₂ →L[𝕜] F` its partial derivative with respect to the second argument.

It proves the existence of `ψ : E₁ → E₂` such that for `v` in a neighbourhood of `u` we have
`f v = f u ↔ ψ v.1 = v.2`. This is `HasStrictFDerivAt.implicitFunctionOfProdDomain`. A formula for
its first derivative follows.

A similar specialization is made to a curried bivariate function by `implicitFunctionOfBivariate` in
a sister file .

## Tags

implicit function
-/

public section

open Filter
open scoped Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E₁ : Type*} [NormedAddCommGroup E₁] [NormedSpace 𝕜 E₁] [CompleteSpace E₁]
  {E₂ : Type*} [NormedAddCommGroup E₂] [NormedSpace 𝕜 E₂] [CompleteSpace E₂]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]

namespace HasStrictFDerivAt

variable {u : E₁ × E₂} {f : E₁ × E₂ -> F} {f'u : E₁ × E₂ ->L[𝕜] F}

/--
Definition of `implicitFunctionDataOfProdDomain` / `implicitFunctionDataOfProdDomain` 的定义

English:
definition implicitFunctionDataOfProdDomain
  body: f
  rightFun := Prod.fst
  pt := u
  leftDeriv := f'u
  hasStrictFDerivAt_leftFun := dfu
  rightDeriv := .fst 𝕜 E₁ E₂
  hasStrictFDerivAt_rightFun := hasStrictFDerivAt_fst
  range_leftDeriv := by
    have : (f'u ∘L .inr 𝕜 E₁ E₂).range <= f'u.range := LinearMap.range_comp_le_range ..
    rwa [LinearMap.range_eq_top.mpr if₂u.surjective, top_le_iff] at this
  range_rightDeriv := Submodule.range_fst
  isCompl_ker := by
    constructor
    · rw [LinearMap.disjoint_ker]
      intro (_, y) h rfl
      simpa using (injective_iff_map_eq_zero _).mp if₂u.injective y h
    · rw [Submodule.codisjoint_iff_exists_add_eq]
      intro v
      have ⟨y, hy⟩ := if₂u.surjective (f'u v)
      use v - (0, y), (0, y)
      aesop

中文:
定义 implicitFunctionDataOfProdDomain
  定义体: f
  rightFun := Prod.fst
  pt := u
  leftDeriv := f'u
  hasStrictFDerivAt_leftFun := dfu
  rightDeriv := .fst 𝕜 E₁ E₂
  hasStrictFDerivAt_rightFun := hasStrictFDerivAt_fst
  range_leftDeriv := by
    have : (f'u ∘L .inr 𝕜 E₁ E₂).range <= f'u.range := LinearMap.range_comp_le_range ..
    rwa [LinearMap.range_eq_top.mpr if₂u.surjective, top_le_iff] at this
  range_rightDeriv := Submodule.range_fst
  isCompl_ker := by
    constructor
    · rw [LinearMap.disjoint_ker]
      intro (_, y) h rfl
      simpa using (injective_iff_map_eq_zero _).mp if₂u.injective y h
    · rw [Submodule.codisjoint_iff_exists_add_eq]
      intro v
      have ⟨y, hy⟩ := if₂u.surjective (f'u v)
      use v - (0, y), (0, y)
      aesop
-/
def implicitFunctionDataOfProdDomain
    (dfu : HasStrictFDerivAt f f'u u) (if₂u : (f'u ∘L .inr 𝕜 E₁ E₂).IsInvertible) :
    ImplicitFunctionData 𝕜 (E₁ × E₂) F E₁ where
  leftFun := f
  rightFun := Prod.fst
  pt := u
  leftDeriv := f'u
  hasStrictFDerivAt_leftFun := dfu
  rightDeriv := .fst 𝕜 E₁ E₂
  hasStrictFDerivAt_rightFun := hasStrictFDerivAt_fst
  range_leftDeriv := by
    have : (f'u ∘L .inr 𝕜 E₁ E₂).range <= f'u.range := LinearMap.range_comp_le_range ..
    rwa [LinearMap.range_eq_top.mpr if₂u.surjective, top_le_iff] at this
  range_rightDeriv := Submodule.range_fst
  isCompl_ker := by
    constructor
    · rw [LinearMap.disjoint_ker]
      intro (_, y) h rfl
      simpa using (injective_iff_map_eq_zero _).mp if₂u.injective y h
    · rw [Submodule.codisjoint_iff_exists_add_eq]
      intro v
      have ⟨y, hy⟩ := if₂u.surjective (f'u v)
      use v - (0, y), (0, y)
      aesop

/--
theorem `pt_implicitFunctionDataOfProdDomain` / 定理 `pt_implicitFunctionDataOfProdDomain`

English:
theorem pt_implicitFunctionDataOfProdDomain
  proof: by
  rfl

中文:
定理 pt_implicitFunctionDataOfProdDomain
  证明: by
  rfl
-/
@[simp] theorem pt_implicitFunctionDataOfProdDomain
    (dfu : HasStrictFDerivAt f f'u u) (if₂u : (f'u ∘L .inr 𝕜 E₁ E₂).IsInvertible) :
    (dfu.implicitFunctionDataOfProdDomain if₂u).pt = u := by
  rfl

/--
theorem `leftFun_implicitFunctionDataOfProdDomain` / 定理 `leftFun_implicitFunctionDataOfProdDomain`

English:
theorem leftFun_implicitFunctionDataOfProdDomain
  proof: by
  rfl

中文:
定理 leftFun_implicitFunctionDataOfProdDomain
  证明: by
  rfl
-/
@[simp] theorem leftFun_implicitFunctionDataOfProdDomain
    (dfu : HasStrictFDerivAt f f'u u) (if₂u : (f'u ∘L .inr 𝕜 E₁ E₂).IsInvertible) :
    (dfu.implicitFunctionDataOfProdDomain if₂u).leftFun = f := by
  rfl

/--
theorem `rightFun_implicitFunctionDataOfProdDomain` / 定理 `rightFun_implicitFunctionDataOfProdDomain`

English:
theorem rightFun_implicitFunctionDataOfProdDomain
  proof: by
  rfl

中文:
定理 rightFun_implicitFunctionDataOfProdDomain
  证明: by
  rfl
-/
@[simp] theorem rightFun_implicitFunctionDataOfProdDomain
    (dfu : HasStrictFDerivAt f f'u u) (if₂u : (f'u ∘L .inr 𝕜 E₁ E₂).IsInvertible) :
    (dfu.implicitFunctionDataOfProdDomain if₂u).rightFun = Prod.fst := by
  rfl

/--
Definition of `implicitFunctionOfProdDomain` / `implicitFunctionOfProdDomain` 的定义

English:
definition implicitFunctionOfProdDomain
  body: fun x => ((dfu.implicitFunctionDataOfProdDomain if₂u).implicitFunction (f u) x).2

中文:
定义 implicitFunctionOfProdDomain
  定义体: fun x => ((dfu.implicitFunctionDataOfProdDomain if₂u).implicitFunction (f u) x).2

Depends on / 依赖: dfu.implicitFunctionDataOfProdDomain, implicitFunction, implicitFunctionDataOfProdDomain
-/
noncomputable def implicitFunctionOfProdDomain
    (dfu : HasStrictFDerivAt f f'u u) (if₂u : (f'u ∘L .inr 𝕜 E₁ E₂).IsInvertible) :
    E₁ -> E₂ :=
  fun x => ((dfu.implicitFunctionDataOfProdDomain if₂u).implicitFunction (f u) x).2

/--
theorem `implicitFunctionOfProdDomain_def` / 定理 `implicitFunctionOfProdDomain_def`

English:
theorem implicitFunctionOfProdDomain_def
  proof: by
  rfl

中文:
定理 implicitFunctionOfProdDomain_def
  证明: by
  rfl
-/
theorem implicitFunctionOfProdDomain_def
    {dfu : HasStrictFDerivAt f f'u u} {if₂u : (f'u ∘L .inr 𝕜 E₁ E₂).IsInvertible} :
    dfu.implicitFunctionOfProdDomain if₂u =
      fun x => ((dfu.implicitFunctionDataOfProdDomain if₂u).implicitFunction (f u) x).2 := by
  rfl

/--
theorem `eventually_apply_eq_iff_implicitFunctionOfProdDomain` / 定理 `eventually_apply_eq_iff_implicitFunctionOfProdDomain`

English:
theorem eventually_apply_eq_iff_implicitFunctionOfProdDomain
  proof: by
  let φ := dfu.implicitFunctionDataOfProdDomain if₂u
  filter_upwards [φ.leftFun_eq_iff_implicitFunction, φ.rightFun_implicitFunction_eq_rightFun]
  exact fun v h _ => Iff.trans h ⟨congrArg _, by aesop⟩

中文:
定理 eventually_apply_eq_iff_implicitFunctionOfProdDomain
  证明: by
  let φ := dfu.implicitFunctionDataOfProdDomain if₂u
  filter_upwards [φ.leftFun_eq_iff_implicitFunction, φ.rightFun_implicitFunction_eq_rightFun]
  exact fun v h _ => Iff.trans h ⟨congrArg _, by aesop⟩

Depends on / 依赖: Iff.trans, dfu.implicitFunctionDataOfProdDomain, filter_upwards, implicitFunctionDataOfProdDomain, leftFun_eq_iff_implicitFunction, rightFun_implicitFunction_eq_rightFun
-/
theorem eventually_apply_eq_iff_implicitFunctionOfProdDomain
    (dfu : HasStrictFDerivAt f f'u u) (if₂u : (f'u ∘L .inr 𝕜 E₁ E₂).IsInvertible) :
    forallᶠ v in 𝓝 u, f v = f u ↔ dfu.implicitFunctionOfProdDomain if₂u v.1 = v.2 := by
  let φ := dfu.implicitFunctionDataOfProdDomain if₂u
  filter_upwards [φ.leftFun_eq_iff_implicitFunction, φ.rightFun_implicitFunction_eq_rightFun]
  exact fun v h _ => Iff.trans h ⟨congrArg _, by aesop⟩

/--
theorem `hasStrictFDerivAt_implicitFunctionOfProdDomain` / 定理 `hasStrictFDerivAt_implicitFunctionOfProdDomain`

English:
theorem hasStrictFDerivAt_implicitFunctionOfProdDomain
  proof: by
  suffices f'u ∘L (.prod (.id ..) (-(f'u ∘L .inr ..).inverse ∘L (f'u ∘L .inl ..))) = 0 from
    ((dfu.implicitFunctionDataOfProdDomain if₂u).hasStrictFDerivAt_implicitFunction _
      (ContinuousLinearMap.fst_comp_prod _ _) this).snd
  ext
  rw [f'u.comp_apply]; rw [← f'u.comp_inl_add_comp_inr]
  simp [-ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_comp, map_neg, if₂u]

中文:
定理 hasStrictFDerivAt_implicitFunctionOfProdDomain
  证明: by
  suffices f'u ∘L (.prod (.id ..) (-(f'u ∘L .inr ..).inverse ∘L (f'u ∘L .inl ..))) = 0 from
    ((dfu.implicitFunctionDataOfProdDomain if₂u).hasStrictFDerivAt_implicitFunction _
      (ContinuousLinearMap.fst_comp_prod _ _) this).snd
  ext
  rw [f'u.comp_apply]; rw [← f'u.comp_inl_add_comp_inr]
  simp [-ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_comp, map_neg, if₂u]

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.coe_comp, ContinuousLinearMap.comp_apply, ContinuousLinearMap.fst_comp_prod, coe_comp, comp_apply, comp_inl_add_comp_inr, dfu.implicitFunctionDataOfProdDomain, fst_comp_prod, hasStrictFDerivAt_implicitFunction, implicitFunctionDataOfProdDomain, inverse, map_neg, u.comp_apply, u.comp_inl_add_comp_inr
-/
theorem hasStrictFDerivAt_implicitFunctionOfProdDomain
    (dfu : HasStrictFDerivAt f f'u u) (if₂u : (f'u ∘L .inr 𝕜 E₁ E₂).IsInvertible) :
    HasStrictFDerivAt (dfu.implicitFunctionOfProdDomain if₂u)
      (-(f'u ∘L .inr 𝕜 E₁ E₂).inverse ∘L (f'u ∘L .inl 𝕜 E₁ E₂)) u.1 := by
  suffices f'u ∘L (.prod (.id ..) (-(f'u ∘L .inr ..).inverse ∘L (f'u ∘L .inl ..))) = 0 from
    ((dfu.implicitFunctionDataOfProdDomain if₂u).hasStrictFDerivAt_implicitFunction _
      (ContinuousLinearMap.fst_comp_prod _ _) this).snd
  ext
  rw [f'u.comp_apply]; rw [← f'u.comp_inl_add_comp_inr]
  simp [-ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_comp, map_neg, if₂u]

/--
theorem `tendsto_implicitFunctionOfProdDomain` / 定理 `tendsto_implicitFunctionOfProdDomain`

English:
theorem tendsto_implicitFunctionOfProdDomain
  proof: by
  have := (dfu.hasStrictFDerivAt_implicitFunctionOfProdDomain if₂u).continuousAt.tendsto
  rwa [(dfu.eventually_apply_eq_iff_implicitFunctionOfProdDomain if₂u).self_of_nhds.mp rfl] at this

中文:
定理 tendsto_implicitFunctionOfProdDomain
  证明: by
  have := (dfu.hasStrictFDerivAt_implicitFunctionOfProdDomain if₂u).continuousAt.tendsto
  rwa [(dfu.eventually_apply_eq_iff_implicitFunctionOfProdDomain if₂u).self_of_nhds.mp rfl] at this

Depends on / 依赖: continuousAt, continuousAt.tendsto, dfu.eventually_apply_eq_iff_implicitFunctionOfProdDomain, dfu.hasStrictFDerivAt_implicitFunctionOfProdDomain, eventually_apply_eq_iff_implicitFunctionOfProdDomain, hasStrictFDerivAt_implicitFunctionOfProdDomain, self_of_nhds, self_of_nhds.mp, tendsto
-/
theorem tendsto_implicitFunctionOfProdDomain
    (dfu : HasStrictFDerivAt f f'u u) (if₂u : (f'u ∘L .inr 𝕜 E₁ E₂).IsInvertible) :
    Tendsto (dfu.implicitFunctionOfProdDomain if₂u) (𝓝 u.1) (𝓝 u.2) := by
  have := (dfu.hasStrictFDerivAt_implicitFunctionOfProdDomain if₂u).continuousAt.tendsto
  rwa [(dfu.eventually_apply_eq_iff_implicitFunctionOfProdDomain if₂u).self_of_nhds.mp rfl] at this

/--
theorem `eventually_apply_implicitFunctionOfProdDomain` / 定理 `eventually_apply_implicitFunctionOfProdDomain`

English:
theorem eventually_apply_implicitFunctionOfProdDomain
  proof: by
  have hψ := dfu.tendsto_implicitFunctionOfProdDomain if₂u
  set ψ := dfu.implicitFunctionOfProdDomain if₂u
  suffices forallᶠ x in 𝓝 u.1, f (x, ψ x) = f u ↔ ψ x = ψ x by simpa using this
  apply Eventually.image_of_prod (r := fun x y => f (x, y) = f u ↔ ψ x = y) hψ
  rw [← nhds_prod_eq]
  exact dfu.eventually_apply_eq_iff_implicitFunctionOfProdDomain if₂u

中文:
定理 eventually_apply_implicitFunctionOfProdDomain
  证明: by
  have hψ := dfu.tendsto_implicitFunctionOfProdDomain if₂u
  set ψ := dfu.implicitFunctionOfProdDomain if₂u
  suffices forallᶠ x in 𝓝 u.1, f (x, ψ x) = f u ↔ ψ x = ψ x by simpa using this
  apply Eventually.image_of_prod (r := fun x y => f (x, y) = f u ↔ ψ x = y) hψ
  rw [← nhds_prod_eq]
  exact dfu.eventually_apply_eq_iff_implicitFunctionOfProdDomain if₂u

Depends on / 依赖: Eventually, Eventually.image_of_prod, dfu.eventually_apply_eq_iff_implicitFunctionOfProdDomain, dfu.implicitFunctionOfProdDomain, dfu.tendsto_implicitFunctionOfProdDomain, eventually_apply_eq_iff_implicitFunctionOfProdDomain, image_of_prod, implicitFunctionOfProdDomain, nhds_prod_eq, tendsto_implicitFunctionOfProdDomain
-/
theorem eventually_apply_implicitFunctionOfProdDomain
    (dfu : HasStrictFDerivAt f f'u u) (if₂u : (f'u ∘L .inr 𝕜 E₁ E₂).IsInvertible) :
    forallᶠ x in 𝓝 u.1, f (x, dfu.implicitFunctionOfProdDomain if₂u x) = f u := by
  have hψ := dfu.tendsto_implicitFunctionOfProdDomain if₂u
  set ψ := dfu.implicitFunctionOfProdDomain if₂u
  suffices forallᶠ x in 𝓝 u.1, f (x, ψ x) = f u ↔ ψ x = ψ x by simpa using this
  apply Eventually.image_of_prod (r := fun x y => f (x, y) = f u ↔ ψ x = y) hψ
  rw [← nhds_prod_eq]
  exact dfu.eventually_apply_eq_iff_implicitFunctionOfProdDomain if₂u

end HasStrictFDerivAt

end
