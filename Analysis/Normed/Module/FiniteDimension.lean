/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
public import Mathlib.Analysis.Normed.Group.Lemmas
public import Mathlib.Analysis.Normed.Affine.Isometry
public import Mathlib.Analysis.Normed.Operator.NormedSpace
public import Mathlib.Analysis.Normed.Module.RieszLemma
public import Mathlib.Analysis.Normed.Module.Ball.Pointwise
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Logic.Encodable.Pi
public import Mathlib.Topology.Algebra.AffineSubspace
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Topology.Algebra.InfiniteSum.Module
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.LinearAlgebra.Dimension.LinearMap
public import Mathlib.LinearAlgebra.Dual.Lemmas


/-!
# Finite-dimensional normed spaces over complete fields

Over a complete nontrivially normed field, in finite dimension, all norms are equivalent and all
linear maps are continuous. Moreover, a finite-dimensional subspace is always complete and closed.

## Main results:

* `FiniteDimensional.complete` : a finite-dimensional space over a complete field is complete. This
  is not registered as an instance, as the field would be an unknown metavariable in typeclass
  resolution.
* `Submodule.closed_of_finiteDimensional` : a finite-dimensional subspace over a complete field is
  closed
* `FiniteDimensional.proper` : a finite-dimensional space over a proper field is proper. This
  is not registered as an instance, as the field would be an unknown metavariable in typeclass
  resolution. It is however registered as an instance for `𝕜 = ℝ` and `𝕜 = ℂ`. As properness
  implies completeness, there is no need to also register `FiniteDimensional.complete` on `ℝ` or
  `ℂ`.
* `FiniteDimensional.of_isCompact_closedBall`: Riesz' theorem: if the closed unit ball is
  compact, then the space is finite-dimensional.

## Implementation notes

The fact that all norms are equivalent is not written explicitly, as it would mean having two norms
on a single space, which is not the way type classes work. However, if one has a
finite-dimensional vector space `E` with a norm, and a copy `E'` of this type with another norm,
then the identities from `E` to `E'` and from `E'` to `E` are continuous thanks to
`LinearMap.continuous_of_finiteDimensional`. This gives the desired norm equivalence.
-/

@[expose] public section

universe u v w x

noncomputable section

open Asymptotics Filter Module Metric Module NNReal Set TopologicalSpace Topology

namespace LinearIsometry

open LinearMap

variable {F E₁ : Type*} [SeminormedAddCommGroup F] [NormedAddCommGroup E₁]
variable {R₁ : Type*} [Field R₁] [Module R₁ E₁] [Module R₁ F] [FiniteDimensional R₁ E₁]
  [FiniteDimensional R₁ F]

/--
Definition of `toLinearIsometryEquiv` / `toLinearIsometryEquiv` 的定义

English:
definition toLinearIsometryEquiv
  signature: (li : E₁ ->ₗᵢ[R₁] F) (h : finrank R₁ E₁ = finrank R₁ F)
  body: li.toLinearMap.linearEquivOfInjective li.injective h
  norm_map' := li.norm_map'

@[simp]

中文:
定义 toLinearIsometryEquiv
  签名: (li : E₁ ->ₗᵢ[R₁] F) (h : finrank R₁ E₁ = finrank R₁ F)
  定义体: li.toLinearMap.linearEquivOfInjective li.injective h
  norm_map' := li.norm_map'

@[simp]

Depends on / 依赖: injective, li.injective, li.toLinearMap.linearEquivOfInjective, linearEquivOfInjective, toLinearMap
-/
def toLinearIsometryEquiv (li : E₁ ->ₗᵢ[R₁] F) (h : finrank R₁ E₁ = finrank R₁ F) :
    E₁ ≃ₗᵢ[R₁] F where
  toLinearEquiv := li.toLinearMap.linearEquivOfInjective li.injective h
  norm_map' := li.norm_map'

@[simp]
/--
theorem `coe_toLinearIsometryEquiv` / 定理 `coe_toLinearIsometryEquiv`

English:
theorem coe_toLinearIsometryEquiv
  given: (li : E₁ ->ₗᵢ[R₁] F) (h : finrank R₁ E₁ = finrank R₁ F)
  proof: rfl

@[simp]

中文:
定理 coe_toLinearIsometryEquiv
  条件: (li : E₁ ->ₗᵢ[R₁] F) (h : finrank R₁ E₁ = finrank R₁ F)
  证明: rfl

@[simp]
-/
theorem coe_toLinearIsometryEquiv (li : E₁ ->ₗᵢ[R₁] F) (h : finrank R₁ E₁ = finrank R₁ F) :
    (li.toLinearIsometryEquiv h : E₁ -> F) = li :=
  rfl

@[simp]
/--
theorem `toLinearIsometryEquiv_apply` / 定理 `toLinearIsometryEquiv_apply`

English:
theorem toLinearIsometryEquiv_apply
  statement: (li : E₁ ->ₗᵢ[R₁] F) (h : finrank R₁ E₁ = finrank R₁ F)
  proof: rfl

中文:
定理 toLinearIsometryEquiv_apply
  结论: (li : E₁ ->ₗᵢ[R₁] F) (h : finrank R₁ E₁ = finrank R₁ F)
  证明: rfl
-/
theorem toLinearIsometryEquiv_apply (li : E₁ ->ₗᵢ[R₁] F) (h : finrank R₁ E₁ = finrank R₁ F)
    (x : E₁) : (li.toLinearIsometryEquiv h) x = li x :=
  rfl

end LinearIsometry

namespace AffineIsometry

open AffineMap

variable {𝕜 : Type*} {V₁ V₂ : Type*} {P₁ P₂ : Type*} [NormedField 𝕜] [NormedAddCommGroup V₁]
  [SeminormedAddCommGroup V₂] [NormedSpace 𝕜 V₁] [NormedSpace 𝕜 V₂] [MetricSpace P₁]
  [PseudoMetricSpace P₂] [NormedAddTorsor V₁ P₁] [NormedAddTorsor V₂ P₂]

variable [FiniteDimensional 𝕜 V₁] [FiniteDimensional 𝕜 V₂]

/--
Definition of `toAffineIsometryEquiv` / `toAffineIsometryEquiv` 的定义

English:
definition toAffineIsometryEquiv
  signature: [Inhabited P₁] (li : P₁ ->ᵃⁱ[𝕜] P₂) (h : finrank 𝕜 V₁ = finrank 𝕜 V₂)
  body: AffineIsometryEquiv.mk' li (li.linearIsometry.toLinearIsometryEquiv h)
    (Inhabited.default (α := P₁)) fun p => by simp

@[simp]

中文:
定义 toAffineIsometryEquiv
  签名: [可居 P₁] (li : P₁ ->ᵃⁱ[𝕜] P₂) (h : finrank 𝕜 V₁ = finrank 𝕜 V₂)
  定义体: AffineIsometryEquiv.mk' li (li.linearIsometry.toLinearIsometryEquiv h)
    (Inhabited.default (α := P₁)) fun p => by simp

@[simp]

Depends on / 依赖: AffineIsometryEquiv, AffineIsometryEquiv.mk, Inhabited, Inhabited.default, li.linearIsometry.toLinearIsometryEquiv, linearIsometry, toLinearIsometryEquiv
-/
def toAffineIsometryEquiv [Inhabited P₁] (li : P₁ ->ᵃⁱ[𝕜] P₂) (h : finrank 𝕜 V₁ = finrank 𝕜 V₂) :
    P₁ ≃ᵃⁱ[𝕜] P₂ :=
  AffineIsometryEquiv.mk' li (li.linearIsometry.toLinearIsometryEquiv h)
    (Inhabited.default (α := P₁)) fun p => by simp

@[simp]
/--
theorem `coe_toAffineIsometryEquiv` / 定理 `coe_toAffineIsometryEquiv`

English:
theorem coe_toAffineIsometryEquiv
  statement: [Inhabited P₁] (li : P₁ ->ᵃⁱ[𝕜] P₂)
  proof: rfl

@[simp]

中文:
定理 coe_toAffineIsometryEquiv
  结论: [可居 P₁] (li : P₁ ->ᵃⁱ[𝕜] P₂)
  证明: rfl

@[simp]
-/
theorem coe_toAffineIsometryEquiv [Inhabited P₁] (li : P₁ ->ᵃⁱ[𝕜] P₂)
    (h : finrank 𝕜 V₁ = finrank 𝕜 V₂) : (li.toAffineIsometryEquiv h : P₁ -> P₂) = li :=
  rfl

@[simp]
/--
theorem `toAffineIsometryEquiv_apply` / 定理 `toAffineIsometryEquiv_apply`

English:
theorem toAffineIsometryEquiv_apply
  statement: [Inhabited P₁] (li : P₁ ->ᵃⁱ[𝕜] P₂)
  proof: rfl

中文:
定理 toAffineIsometryEquiv_apply
  结论: [可居 P₁] (li : P₁ ->ᵃⁱ[𝕜] P₂)
  证明: rfl
-/
theorem toAffineIsometryEquiv_apply [Inhabited P₁] (li : P₁ ->ᵃⁱ[𝕜] P₂)
    (h : finrank 𝕜 V₁ = finrank 𝕜 V₂) (x : P₁) : (li.toAffineIsometryEquiv h) x = li x :=
  rfl

end AffineIsometry

section CompleteField

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜] {E : Type v} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {F : Type w} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace 𝕜]

section Affine

variable {PE PF : Type*} [MetricSpace PE] [NormedAddTorsor E PE] [MetricSpace PF]
  [NormedAddTorsor F PF] [FiniteDimensional 𝕜 E]

/--
theorem `AffineMap.continuous_of_finiteDimensional` / 定理 `AffineMap.continuous_of_finiteDimensional`

English:
theorem AffineMap.continuous_of_finiteDimensional
  given: (f : PE ->ᵃ[𝕜] PF)
  statement: Continuous f
  proof: AffineMap.continuous_linear_iff.1 f.linear.continuous_of_finiteDimensional

中文:
定理 仿射映射.continuous_of_finiteDimensional
  条件: (f : PE ->ᵃ[𝕜] PF)
  结论: 连续 f
  证明: AffineMap.continuous_linear_iff.1 f.linear.continuous_of_finiteDimensional

Depends on / 依赖: AffineMap, AffineMap.continuous_linear_iff, continuous_linear_iff, continuous_of_finiteDimensional, f.linear.continuous_of_finiteDimensional, linear
-/
theorem AffineMap.continuous_of_finiteDimensional (f : PE ->ᵃ[𝕜] PF) : Continuous f :=
  AffineMap.continuous_linear_iff.1 f.linear.continuous_of_finiteDimensional

/--
theorem `AffineEquiv.continuous_of_finiteDimensional` / 定理 `AffineEquiv.continuous_of_finiteDimensional`

English:
theorem AffineEquiv.continuous_of_finiteDimensional
  given: (f : PE ≃ᵃ[𝕜] PF)
  statement: Continuous f
  proof: f.toAffineMap.continuous_of_finiteDimensional

中文:
定理 仿射等价.continuous_of_finiteDimensional
  条件: (f : PE ≃ᵃ[𝕜] PF)
  结论: 连续 f
  证明: f.toAffineMap.continuous_of_finiteDimensional

Depends on / 依赖: continuous_of_finiteDimensional, f.toAffineMap.continuous_of_finiteDimensional, toAffineMap
-/
theorem AffineEquiv.continuous_of_finiteDimensional (f : PE ≃ᵃ[𝕜] PF) : Continuous f :=
  f.toAffineMap.continuous_of_finiteDimensional

/--
Definition of `AffineEquiv.toContinuousAffineEquiv` / `AffineEquiv.toContinuousAffineEquiv` 的定义

English:
definition AffineEquiv.toContinuousAffineEquiv
  signature: : (PE ≃ᵃ[𝕜] PF) ≃ (PE ≃ᴬ[𝕜] PF) where
  body: haveI := f.linear.finiteDimensional
    ⟨f, f.continuous_of_finiteDimensional, f.symm.continuous_of_finiteDimensional⟩
  invFun f := f.toAffineEquiv
  left_inv _ := rfl
  right_inv _ := ContinuousAffineEquiv.toAffineEquiv_injective rfl

@[simp]

中文:
定义 仿射等价.toContinuousAffineEquiv
  签名: : (PE ≃ᵃ[𝕜] PF) ≃ (PE ≃ᴬ[𝕜] PF) where
  定义体: haveI := f.linear.finiteDimensional
    ⟨f, f.continuous_of_finiteDimensional, f.symm.continuous_of_finiteDimensional⟩
  invFun f := f.toAffineEquiv
  left_inv _ := rfl
  right_inv _ := ContinuousAffineEquiv.toAffineEquiv_injective rfl

@[simp]

Depends on / 依赖: ContinuousAffineEquiv, ContinuousAffineEquiv.toAffineEquiv_injective, continuous_of_finiteDimensional, f.continuous_of_finiteDimensional, f.linear.finiteDimensional, f.symm.continuous_of_finiteDimensional, f.toAffineEquiv, finiteDimensional, invFun, left_inv, linear, right_inv, toAffineEquiv, toAffineEquiv_injective
-/
def AffineEquiv.toContinuousAffineEquiv : (PE ≃ᵃ[𝕜] PF) ≃ (PE ≃ᴬ[𝕜] PF) where
  toFun f :=
    haveI := f.linear.finiteDimensional
    ⟨f, f.continuous_of_finiteDimensional, f.symm.continuous_of_finiteDimensional⟩
  invFun f := f.toAffineEquiv
  left_inv _ := rfl
  right_inv _ := ContinuousAffineEquiv.toAffineEquiv_injective rfl

@[simp]
/--
theorem `AffineEquiv.coe_toContinuousAffineEquiv` / 定理 `AffineEquiv.coe_toContinuousAffineEquiv`

English:
theorem AffineEquiv.coe_toContinuousAffineEquiv
  given: (f : PE ≃ᵃ[𝕜] PF)
  proof: rfl

@[simp]

中文:
定理 仿射等价.coe_toContinuousAffineEquiv
  条件: (f : PE ≃ᵃ[𝕜] PF)
  证明: rfl

@[simp]
-/
theorem AffineEquiv.coe_toContinuousAffineEquiv (f : PE ≃ᵃ[𝕜] PF) :
    ⇑(toContinuousAffineEquiv f) = f := rfl

@[simp]
/--
theorem `AffineEquiv.toAffineEquiv_toContinuousAffineEquiv` / 定理 `AffineEquiv.toAffineEquiv_toContinuousAffineEquiv`

English:
theorem AffineEquiv.toAffineEquiv_toContinuousAffineEquiv
  given: (f : PE ≃ᵃ[𝕜] PF)
  proof: rfl

@[simp]

中文:
定理 仿射等价.toAffineEquiv_toContinuousAffineEquiv
  条件: (f : PE ≃ᵃ[𝕜] PF)
  证明: rfl

@[simp]
-/
theorem AffineEquiv.toAffineEquiv_toContinuousAffineEquiv (f : PE ≃ᵃ[𝕜] PF) :
    (toContinuousAffineEquiv f).toAffineEquiv = f := rfl

@[simp]
/--
theorem `AffineEquiv.toContinuousAffineEquiv_symm_apply` / 定理 `AffineEquiv.toContinuousAffineEquiv_symm_apply`

English:
theorem AffineEquiv.toContinuousAffineEquiv_symm_apply
  given: (f : PE ≃ᴬ[𝕜] PF)
  proof: rfl

中文:
定理 仿射等价.toContinuousAffineEquiv_symm_apply
  条件: (f : PE ≃ᴬ[𝕜] PF)
  证明: rfl
-/
theorem AffineEquiv.toContinuousAffineEquiv_symm_apply (f : PE ≃ᴬ[𝕜] PF) :
    toContinuousAffineEquiv.symm f = f.toAffineEquiv := rfl

/--
Definition of `AffineEquiv.toHomeomorphOfFiniteDimensional` / `AffineEquiv.toHomeomorphOfFiniteDimensional` 的定义

English:
definition AffineEquiv.toHomeomorphOfFiniteDimensional
  signature: (f : PE ≃ᵃ[𝕜] PF)
  body: (toContinuousAffineEquiv f).toHomeomorph

@[simp]

中文:
定义 仿射等价.toHomeomorphOfFiniteDimensional
  签名: (f : PE ≃ᵃ[𝕜] PF)
  定义体: (toContinuousAffineEquiv f).toHomeomorph

@[simp]

Depends on / 依赖: toContinuousAffineEquiv, toHomeomorph
-/
def AffineEquiv.toHomeomorphOfFiniteDimensional (f : PE ≃ᵃ[𝕜] PF) : PE ≃ₜ PF :=
  (toContinuousAffineEquiv f).toHomeomorph

@[simp]
/--
theorem `AffineEquiv.coe_toHomeomorphOfFiniteDimensional` / 定理 `AffineEquiv.coe_toHomeomorphOfFiniteDimensional`

English:
theorem AffineEquiv.coe_toHomeomorphOfFiniteDimensional
  given: (f : PE ≃ᵃ[𝕜] PF)
  proof: rfl

@[simp]

中文:
定理 仿射等价.coe_toHomeomorphOfFiniteDimensional
  条件: (f : PE ≃ᵃ[𝕜] PF)
  证明: rfl

@[simp]
-/
theorem AffineEquiv.coe_toHomeomorphOfFiniteDimensional (f : PE ≃ᵃ[𝕜] PF) :
    ⇑f.toHomeomorphOfFiniteDimensional = f :=
  rfl

@[simp]
/--
theorem `AffineEquiv.coe_toHomeomorphOfFiniteDimensional_symm` / 定理 `AffineEquiv.coe_toHomeomorphOfFiniteDimensional_symm`

English:
theorem AffineEquiv.coe_toHomeomorphOfFiniteDimensional_symm
  given: (f : PE ≃ᵃ[𝕜] PF)
  proof: rfl

中文:
定理 仿射等价.coe_toHomeomorphOfFiniteDimensional_symm
  条件: (f : PE ≃ᵃ[𝕜] PF)
  证明: rfl
-/
theorem AffineEquiv.coe_toHomeomorphOfFiniteDimensional_symm (f : PE ≃ᵃ[𝕜] PF) :
    ⇑f.toHomeomorphOfFiniteDimensional.symm = f.symm :=
  rfl

attribute [deprecated AffineEquiv.toContinuousAffineEquiv (since := "2026-05-11")]
  AffineEquiv.toHomeomorphOfFiniteDimensional

/--
theorem `AffineMap.lipschitzWith_of_finiteDimensional` / 定理 `AffineMap.lipschitzWith_of_finiteDimensional`

English:
theorem AffineMap.lipschitzWith_of_finiteDimensional
  given: (f : PE ->ᵃ[𝕜] PF)
  proof: by
  let fL : E ->L[𝕜] F := f.linear.toContinuousLinearMap
  refine ⟨‖fL‖₊, LipschitzWith.of_dist_le_mul fun x y => ?_⟩
  rw [NormedAddTorsor.dist_eq_norm']; rw [NormedAddTorsor.dist_eq_norm']; rw [← f.linearMap_vsub]
  exact fL.le_opNorm _

中文:
定理 仿射映射.lipschitzWith_of_finiteDimensional
  条件: (f : PE ->ᵃ[𝕜] PF)
  证明: by
  let fL : E ->L[𝕜] F := f.linear.toContinuousLinearMap
  refine ⟨‖fL‖₊, LipschitzWith.of_dist_le_mul fun x y => ?_⟩
  rw [NormedAddTorsor.dist_eq_norm']; rw [NormedAddTorsor.dist_eq_norm']; rw [← f.linearMap_vsub]
  exact fL.le_opNorm _

Depends on / 依赖: LipschitzWith, LipschitzWith.of_dist_le_mul, NormedAddTorsor, NormedAddTorsor.dist_eq_norm, dist_eq_norm, f.linear.toContinuousLinearMap, f.linearMap_vsub, fL.le_opNorm, le_opNorm, linear, linearMap_vsub, of_dist_le_mul, toContinuousLinearMap
-/
theorem AffineMap.lipschitzWith_of_finiteDimensional (f : PE ->ᵃ[𝕜] PF) :
    exists K : Real>=0, LipschitzWith K f := by
  let fL : E ->L[𝕜] F := f.linear.toContinuousLinearMap
  refine ⟨‖fL‖₊, LipschitzWith.of_dist_le_mul fun x y => ?_⟩
  rw [NormedAddTorsor.dist_eq_norm']; rw [NormedAddTorsor.dist_eq_norm']; rw [← f.linearMap_vsub]
  exact fL.le_opNorm _

end Affine

/--
theorem `ContinuousLinearMap.continuous_det` / 定理 `ContinuousLinearMap.continuous_det`

English:
theorem ContinuousLinearMap.continuous_det
  statement: Continuous fun f : E ->L[𝕜] E => f.det
  proof: by
  change Continuous fun f : E ->L[𝕜] E => LinearMap.det (f : E ->ₗ[𝕜] E)
  -- TODO: this could be easier with `det_cases`
  by_cases h : exists s : Finset E, Nonempty (Basis (↥s) 𝕜 E)
  · rcases h with ⟨s, ⟨b⟩⟩
    have : FiniteDimensional 𝕜 E := b.finiteDimensional_of_finite
    classical
    simp_rw [LinearMap.det_eq_det_toMatrix_of_finset b]
    refine Continuous.matrix_det ?_
    exact
      ((LinearMap.toMatrix b b).toLinearMap.comp
          (ContinuousLinearMap.coeLM 𝕜)).continuous_of_finiteDimensional
  · rw [LinearMap.det]
    simpa only [h, MonoidHom.one_apply, dif_neg, not_false_iff] using continuous_const

中文:
定理 连续线性映射.continuous_det
  结论: 连续 fun f : E ->L[𝕜] E => f.det
  证明: by
  change Continuous fun f : E ->L[𝕜] E => LinearMap.det (f : E ->ₗ[𝕜] E)
  -- TODO: this could be easier with `det_cases`
  by_cases h : exists s : Finset E, Nonempty (Basis (↥s) 𝕜 E)
  · rcases h with ⟨s, ⟨b⟩⟩
    have : FiniteDimensional 𝕜 E := b.finiteDimensional_of_finite
    classical
    simp_rw [LinearMap.det_eq_det_toMatrix_of_finset b]
    refine Continuous.matrix_det ?_
    exact
      ((LinearMap.toMatrix b b).toLinearMap.comp
          (ContinuousLinearMap.coeLM 𝕜)).continuous_of_finiteDimensional
  · rw [LinearMap.det]
    simpa only [h, MonoidHom.one_apply, dif_neg, not_false_iff] using continuous_const

Depends on / 依赖: Continuous, LinearMap, LinearMap.det
-/
theorem ContinuousLinearMap.continuous_det : Continuous fun f : E ->L[𝕜] E => f.det := by
  change Continuous fun f : E ->L[𝕜] E => LinearMap.det (f : E ->ₗ[𝕜] E)
  -- TODO: this could be easier with `det_cases`
  by_cases h : exists s : Finset E, Nonempty (Basis (↥s) 𝕜 E)
  · rcases h with ⟨s, ⟨b⟩⟩
    have : FiniteDimensional 𝕜 E := b.finiteDimensional_of_finite
    classical
    simp_rw [LinearMap.det_eq_det_toMatrix_of_finset b]
    refine Continuous.matrix_det ?_
    exact
      ((LinearMap.toMatrix b b).toLinearMap.comp
          (ContinuousLinearMap.coeLM 𝕜)).continuous_of_finiteDimensional
  · rw [LinearMap.det]
    simpa only [h, MonoidHom.one_apply, dif_neg, not_false_iff] using continuous_const

/-- Any `K`-Lipschitz map from a subset `s` of a metric space `α` to a finite-dimensional real
vector space `E'` can be extended to a Lipschitz map on the whole space `α`, with a slightly worse
constant `C * K` where `C` only depends on `E'`. We record a working value for this constant `C`
as `lipschitzExtensionConstant E'`. -/
irreducible_def lipschitzExtensionConstant (E' : Type*) [NormedAddCommGroup E'] [NormedSpace Real E']
  [FiniteDimensional Real E'] : Real>=0 :=
  let A := (Basis.ofVectorSpace Real E').equivFun.toContinuousLinearEquiv
  max (‖A.symm.toContinuousLinearMap‖₊ * ‖A.toContinuousLinearMap‖₊) 1

/--
theorem `lipschitzExtensionConstant_pos` / 定理 `lipschitzExtensionConstant_pos`

English:
theorem lipschitzExtensionConstant_pos
  statement: (E' : Type*) [NormedAddCommGroup E'] [NormedSpace Real E']
  proof: by
  rw [lipschitzExtensionConstant]
  exact zero_lt_one.trans_le (le_max_right _ _)

中文:
定理 lipschitzExtensionConstant_pos
  结论: (E' : 类型) [赋范交换加群 E'] [赋范空间 实数 E']
  证明: by
  rw [lipschitzExtensionConstant]
  exact zero_lt_one.trans_le (le_max_right _ _)

Depends on / 依赖: le_max_right, lipschitzExtensionConstant, trans_le, zero_lt_one, zero_lt_one.trans_le
-/
theorem lipschitzExtensionConstant_pos (E' : Type*) [NormedAddCommGroup E'] [NormedSpace Real E']
    [FiniteDimensional Real E'] : 0 < lipschitzExtensionConstant E' := by
  rw [lipschitzExtensionConstant]
  exact zero_lt_one.trans_le (le_max_right _ _)

/--
theorem `LipschitzOnWith.extend_finite_dimension` / 定理 `LipschitzOnWith.extend_finite_dimension`

English:
theorem LipschitzOnWith.extend_finite_dimension
  statement: {α : Type*} [PseudoMetricSpace α] {E' : Type*}
  proof: by
  /- This result is already known for spaces `ι → ℝ`. We use a continuous linear equiv between
    `E'` and such a space to transfer the result to `E'`. -/
  let ι : Type _ := Basis.ofVectorSpaceIndex Real E'
  let A := (Basis.ofVectorSpace Real E').equivFun.toContinuousLinearEquiv
  have LA : LipschitzWith ‖A.toContinuousLinearMap‖₊ A := by apply A.lipschitz
  have L : LipschitzOnWith (‖A.toContinuousLinearMap‖₊ * K) (A ∘ f) s :=
    LA.comp_lipschitzOnWith hf
  obtain ⟨g, hg, gs⟩ :
    exists g : α -> ι -> Real, LipschitzWith (‖A.toContinuousLinearMap‖₊ * K) g ∧ EqOn (A ∘ f) g s :=
    L.extend_pi
  refine ⟨A.symm ∘ g, ?_, ?_⟩
  · have LAsymm : LipschitzWith ‖A.symm.toContinuousLinearMap‖₊ A.symm := by
      apply A.symm.lipschitz
    apply (LAsymm.comp hg).weaken
    rw [lipschitzExtensionConstant]; rw [← mul_assoc]
    exact mul_le_mul' (le_max_left _ _) le_rfl
  · intro x hx
    have : A (f x) = g x := gs hx
    simp only [(· ∘ ·), ← this, A.symm_apply_apply]

中文:
定理 LipschitzOnWith.extend_finite_dimension
  结论: {α : 类型} [伪度量空间 α] {E' : 类型}
  证明: by
  /- This result is already known for spaces `ι → ℝ`. We use a continuous linear equiv between
    `E'` and such a space to transfer the result to `E'`. -/
  let ι : Type _ := Basis.ofVectorSpaceIndex Real E'
  let A := (Basis.ofVectorSpace Real E').equivFun.toContinuousLinearEquiv
  have LA : LipschitzWith ‖A.toContinuousLinearMap‖₊ A := by apply A.lipschitz
  have L : LipschitzOnWith (‖A.toContinuousLinearMap‖₊ * K) (A ∘ f) s :=
    LA.comp_lipschitzOnWith hf
  obtain ⟨g, hg, gs⟩ :
    exists g : α -> ι -> Real, LipschitzWith (‖A.toContinuousLinearMap‖₊ * K) g ∧ EqOn (A ∘ f) g s :=
    L.extend_pi
  refine ⟨A.symm ∘ g, ?_, ?_⟩
  · have LAsymm : LipschitzWith ‖A.symm.toContinuousLinearMap‖₊ A.symm := by
      apply A.symm.lipschitz
    apply (LAsymm.comp hg).weaken
    rw [lipschitzExtensionConstant]; rw [← mul_assoc]
    exact mul_le_mul' (le_max_left _ _) le_rfl
  · intro x hx
    have : A (f x) = g x := gs hx
    simp only [(· ∘ ·), ← this, A.symm_apply_apply]
-/
theorem LipschitzOnWith.extend_finite_dimension {α : Type*} [PseudoMetricSpace α] {E' : Type*}
    [NormedAddCommGroup E'] [NormedSpace Real E'] [FiniteDimensional Real E'] {s : Set α} {f : α -> E'}
    {K : Real>=0} (hf : LipschitzOnWith K f s) :
    exists g : α -> E', LipschitzWith (lipschitzExtensionConstant E' * K) g ∧ EqOn f g s := by
  /- This result is already known for spaces `ι → ℝ`. We use a continuous linear equiv between
    `E'` and such a space to transfer the result to `E'`. -/
  let ι : Type _ := Basis.ofVectorSpaceIndex Real E'
  let A := (Basis.ofVectorSpace Real E').equivFun.toContinuousLinearEquiv
  have LA : LipschitzWith ‖A.toContinuousLinearMap‖₊ A := by apply A.lipschitz
  have L : LipschitzOnWith (‖A.toContinuousLinearMap‖₊ * K) (A ∘ f) s :=
    LA.comp_lipschitzOnWith hf
  obtain ⟨g, hg, gs⟩ :
    exists g : α -> ι -> Real, LipschitzWith (‖A.toContinuousLinearMap‖₊ * K) g ∧ EqOn (A ∘ f) g s :=
    L.extend_pi
  refine ⟨A.symm ∘ g, ?_, ?_⟩
  · have LAsymm : LipschitzWith ‖A.symm.toContinuousLinearMap‖₊ A.symm := by
      apply A.symm.lipschitz
    apply (LAsymm.comp hg).weaken
    rw [lipschitzExtensionConstant]; rw [← mul_assoc]
    exact mul_le_mul' (le_max_left _ _) le_rfl
  · intro x hx
    have : A (f x) = g x := gs hx
    simp only [(· ∘ ·), ← this, A.symm_apply_apply]

/--
theorem `LinearMap.exists_antilipschitzWith` / 定理 `LinearMap.exists_antilipschitzWith`

English:
theorem LinearMap.exists_antilipschitzWith
  statement: [FiniteDimensional 𝕜 E] (f : E ->ₗ[𝕜] F)
  proof: by
  cases subsingleton_or_nontrivial E
  · exact ⟨1, zero_lt_one, AntilipschitzWith.of_subsingleton⟩
  · rw [LinearMap.ker_eq_bot] at hf
    let e : E ≃L[𝕜] LinearMap.range f := (LinearEquiv.ofInjective f hf).toContinuousLinearEquiv
    exact ⟨_, e.nnnorm_symm_pos, e.antilipschitz⟩

中文:
定理 线性映射.存在_antilipschitzWith
  结论: [有限维 𝕜 E] (f : E ->ₗ[𝕜] F)
  证明: by
  cases subsingleton_or_nontrivial E
  · exact ⟨1, zero_lt_one, AntilipschitzWith.of_subsingleton⟩
  · rw [LinearMap.ker_eq_bot] at hf
    let e : E ≃L[𝕜] LinearMap.range f := (LinearEquiv.ofInjective f hf).toContinuousLinearEquiv
    exact ⟨_, e.nnnorm_symm_pos, e.antilipschitz⟩

Depends on / 依赖: AntilipschitzWith, AntilipschitzWith.of_subsingleton, LinearEquiv, LinearEquiv.ofInjective, LinearMap, LinearMap.ker_eq_bot, LinearMap.range, antilipschitz, e.antilipschitz, e.nnnorm_symm_pos, ker_eq_bot, nnnorm_symm_pos, ofInjective, of_subsingleton, subsingleton_or_nontrivial, toContinuousLinearEquiv, zero_lt_one
-/
theorem LinearMap.exists_antilipschitzWith [FiniteDimensional 𝕜 E] (f : E ->ₗ[𝕜] F)
    (hf : LinearMap.ker f = ⊥) : exists K > 0, AntilipschitzWith K f := by
  cases subsingleton_or_nontrivial E
  · exact ⟨1, zero_lt_one, AntilipschitzWith.of_subsingleton⟩
  · rw [LinearMap.ker_eq_bot] at hf
    let e : E ≃L[𝕜] LinearMap.range f := (LinearEquiv.ofInjective f hf).toContinuousLinearEquiv
    exact ⟨_, e.nnnorm_symm_pos, e.antilipschitz⟩

open Function in
/--
theorem `LinearMap.injective_iff_antilipschitz` / 定理 `LinearMap.injective_iff_antilipschitz`

English:
theorem LinearMap.injective_iff_antilipschitz
  given: [FiniteDimensional 𝕜 E] (f : E ->ₗ[𝕜] F)
  proof: by
  constructor
  · rw [← LinearMap.ker_eq_bot]
    exact f.exists_antilipschitzWith
  · rintro ⟨K, -, H⟩
    exact H.injective

中文:
定理 线性映射.injective_iff_antilipschitz
  条件: [有限维 𝕜 E] (f : E ->ₗ[𝕜] F)
  证明: by
  constructor
  · rw [← LinearMap.ker_eq_bot]
    exact f.exists_antilipschitzWith
  · rintro ⟨K, -, H⟩
    exact H.injective

Depends on / 依赖: H.injective, LinearMap, LinearMap.ker_eq_bot, exists_antilipschitzWith, f.exists_antilipschitzWith, injective, ker_eq_bot
-/
theorem LinearMap.injective_iff_antilipschitz [FiniteDimensional 𝕜 E] (f : E ->ₗ[𝕜] F) :
    Injective f ↔ exists K > 0, AntilipschitzWith K f := by
  constructor
  · rw [← LinearMap.ker_eq_bot]
    exact f.exists_antilipschitzWith
  · rintro ⟨K, -, H⟩
    exact H.injective

/--
theorem `AffineMap.antilipschitzWith_of_finiteDimensional` / 定理 `AffineMap.antilipschitzWith_of_finiteDimensional`

English:
theorem AffineMap.antilipschitzWith_of_finiteDimensional
  statement: {PE PF : Type*} [MetricSpace PE]
  proof: by
  obtain ⟨K, -, hK⟩ := f.linear.injective_iff_antilipschitz.mp (f.linear_injective_iff.mpr hf)
  refine ⟨K, AntilipschitzWith.of_le_mul_dist fun x y => ?_⟩
  rw [dist_eq_norm_vsub E]; rw [dist_eq_norm_vsub F]; rw [← f.linearMap_vsub]
  exact ZeroHomClass.bound_of_antilipschitz f.linear hK (x -ᵥ y)

中文:
定理 仿射映射.antilipschitzWith_of_finiteDimensional
  结论: {PE PF : 类型} [度量空间 PE]
  证明: by
  obtain ⟨K, -, hK⟩ := f.linear.injective_iff_antilipschitz.mp (f.linear_injective_iff.mpr hf)
  refine ⟨K, AntilipschitzWith.of_le_mul_dist fun x y => ?_⟩
  rw [dist_eq_norm_vsub E]; rw [dist_eq_norm_vsub F]; rw [← f.linearMap_vsub]
  exact ZeroHomClass.bound_of_antilipschitz f.linear hK (x -ᵥ y)

Depends on / 依赖: AntilipschitzWith, AntilipschitzWith.of_le_mul_dist, ZeroHomClass, ZeroHomClass.bound_of_antilipschitz, bound_of_antilipschitz, dist_eq_norm_vsub, f.linear, f.linear.injective_iff_antilipschitz.mp, f.linearMap_vsub, f.linear_injective_iff.mpr, injective_iff_antilipschitz, linear, linearMap_vsub, linear_injective_iff, of_le_mul_dist
-/
theorem AffineMap.antilipschitzWith_of_finiteDimensional {PE PF : Type*} [MetricSpace PE]
    [NormedAddTorsor E PE] [MetricSpace PF] [NormedAddTorsor F PF] [FiniteDimensional 𝕜 E]
    {f : PE ->ᵃ[𝕜] PF} (hf : Function.Injective f) :
    exists K : Real>=0, AntilipschitzWith K f := by
  obtain ⟨K, -, hK⟩ := f.linear.injective_iff_antilipschitz.mp (f.linear_injective_iff.mpr hf)
  refine ⟨K, AntilipschitzWith.of_le_mul_dist fun x y => ?_⟩
  rw [dist_eq_norm_vsub E]; rw [dist_eq_norm_vsub F]; rw [← f.linearMap_vsub]
  exact ZeroHomClass.bound_of_antilipschitz f.linear hK (x -ᵥ y)

open Function in
/--
theorem `ContinuousLinearMap.isOpen_injective` / 定理 `ContinuousLinearMap.isOpen_injective`

English:
theorem ContinuousLinearMap.isOpen_injective
  given: [FiniteDimensional 𝕜 E]
  proof: by
  rw [isOpen_iff_eventually]
  rintro φ₀ hφ₀
  rcases φ₀.injective_iff_antilipschitz.mp hφ₀ with ⟨K, K_pos, H⟩
have : forallᶠ φ in 𝓝 φ₀, ‖φ - φ₀‖₊ < K⁻¹ := eventually_nnnorm_sub_lt _ inv_pos_of_pos K_pos
  filter_upwards [this] with φ hφ
  apply φ.injective_iff_antilipschitz.mpr
  exact ⟨(K⁻¹ - ‖φ - φ₀‖₊)⁻¹, inv_pos_of_pos (tsub_pos_of_lt hφ),
    H.add_sub_lipschitzWith (φ - φ₀).lipschitz hφ⟩

中文:
定理 连续线性映射.isOpen_injective
  条件: [有限维 𝕜 E]
  证明: by
  rw [isOpen_iff_eventually]
  rintro φ₀ hφ₀
  rcases φ₀.injective_iff_antilipschitz.mp hφ₀ with ⟨K, K_pos, H⟩
have : forallᶠ φ in 𝓝 φ₀, ‖φ - φ₀‖₊ < K⁻¹ := eventually_nnnorm_sub_lt _ inv_pos_of_pos K_pos
  filter_upwards [this] with φ hφ
  apply φ.injective_iff_antilipschitz.mpr
  exact ⟨(K⁻¹ - ‖φ - φ₀‖₊)⁻¹, inv_pos_of_pos (tsub_pos_of_lt hφ),
    H.add_sub_lipschitzWith (φ - φ₀).lipschitz hφ⟩

Depends on / 依赖: H.add_sub_lipschitzWith, K_pos, add_sub_lipschitzWith, eventually_nnnorm_sub_lt, filter_upwards, injective_iff_antilipschitz, injective_iff_antilipschitz.mp, injective_iff_antilipschitz.mpr, inv_pos_of_pos, isOpen_iff_eventually, lipschitz, tsub_pos_of_lt
-/
theorem ContinuousLinearMap.isOpen_injective [FiniteDimensional 𝕜 E] :
    IsOpen { L : E ->L[𝕜] F | Injective L } := by
  rw [isOpen_iff_eventually]
  rintro φ₀ hφ₀
  rcases φ₀.injective_iff_antilipschitz.mp hφ₀ with ⟨K, K_pos, H⟩
have : forallᶠ φ in 𝓝 φ₀, ‖φ - φ₀‖₊ < K⁻¹ := eventually_nnnorm_sub_lt _ inv_pos_of_pos K_pos
  filter_upwards [this] with φ hφ
  apply φ.injective_iff_antilipschitz.mpr
  exact ⟨(K⁻¹ - ‖φ - φ₀‖₊)⁻¹, inv_pos_of_pos (tsub_pos_of_lt hφ),
    H.add_sub_lipschitzWith (φ - φ₀).lipschitz hφ⟩

open ContinuousLinearMap

/--
Definition of `ContinuousLinearEquiv.piRing` / `ContinuousLinearEquiv.piRing` 的定义

English:
definition ContinuousLinearEquiv.piRing
  signature: (ι : Type*) [Fintype ι] [DecidableEq ι]
  body: { LinearMap.toContinuousLinearMap.symm.trans (LinearEquiv.piRing 𝕜 E ι 𝕜) with
    continuous_invFun := by
      simp_rw [LinearEquiv.invFun_eq_symm, LinearEquiv.trans_symm, LinearEquiv.symm_symm]
      refine AddMonoidHomClass.continuous_of_bound
        (LinearMap.toContinuousLinearMap.toLinearMap.comp
            (LinearEquiv.piRing 𝕜 E ι 𝕜).symm.toLinearMap)
        (Fintype.card ι : Real) fun g => ?_
      rw [← nsmul_eq_mul]
      refine opNorm_le_bound _ (nsmul_nonneg (norm_nonneg g) (Fintype.card ι)) fun t => ?_
      simp_rw [LinearMap.coe_comp, LinearEquiv.coe_toLinearMap, Function.comp_apply,
        LinearMap.coe_toContinuousLinearMap', LinearEquiv.piRing_symm_apply]
      apply le_trans (norm_sum_le _ _)
      rw [smul_mul_assoc]
      refine Finset.sum_le_card_nsmul _ _ _ fun i _ => ?_
      rw [norm_smul]; rw [mul_comm]
      gcongr <;> apply norm_le_pi_norm }

中文:
定义 连续线性等价.piRing
  签名: (ι : 类型) [有限类型 ι] [DecidableEq ι]
  定义体: { LinearMap.toContinuousLinearMap.symm.trans (LinearEquiv.piRing 𝕜 E ι 𝕜) with
    continuous_invFun := by
      simp_rw [LinearEquiv.invFun_eq_symm, LinearEquiv.trans_symm, LinearEquiv.symm_symm]
      refine AddMonoidHomClass.continuous_of_bound
        (LinearMap.toContinuousLinearMap.toLinearMap.comp
            (LinearEquiv.piRing 𝕜 E ι 𝕜).symm.toLinearMap)
        (Fintype.card ι : Real) fun g => ?_
      rw [← nsmul_eq_mul]
      refine opNorm_le_bound _ (nsmul_nonneg (norm_nonneg g) (Fintype.card ι)) fun t => ?_
      simp_rw [LinearMap.coe_comp, LinearEquiv.coe_toLinearMap, Function.comp_apply,
        LinearMap.coe_toContinuousLinearMap', LinearEquiv.piRing_symm_apply]
      apply le_trans (norm_sum_le _ _)
      rw [smul_mul_assoc]
      refine Finset.sum_le_card_nsmul _ _ _ fun i _ => ?_
      rw [norm_smul]; rw [mul_comm]
      gcongr <;> apply norm_le_pi_norm }

Depends on / 依赖: AddMonoidHomClass, AddMonoidHomClass.continuous_of_bound, Fintype, Fintype.card, LinearEquiv, LinearEquiv.invFun_eq_symm, LinearEquiv.piRing, LinearEquiv.symm_symm, LinearEquiv.trans_symm, LinearMap, LinearMap.coe_comp, LinearMap.toContinuousLinearMap.symm.trans, LinearMap.toContinuousLinearMap.toLinearMap.comp, coe_comp, continuous_invFun, continuous_of_bound, invFun_eq_symm, norm_nonneg, nsmul_eq_mul, nsmul_nonneg
-/
def ContinuousLinearEquiv.piRing (ι : Type*) [Fintype ι] [DecidableEq ι] :
    ((ι -> 𝕜) ->L[𝕜] E) ≃L[𝕜] ι -> E :=
  { LinearMap.toContinuousLinearMap.symm.trans (LinearEquiv.piRing 𝕜 E ι 𝕜) with
    continuous_invFun := by
      simp_rw [LinearEquiv.invFun_eq_symm, LinearEquiv.trans_symm, LinearEquiv.symm_symm]
      refine AddMonoidHomClass.continuous_of_bound
        (LinearMap.toContinuousLinearMap.toLinearMap.comp
            (LinearEquiv.piRing 𝕜 E ι 𝕜).symm.toLinearMap)
        (Fintype.card ι : Real) fun g => ?_
      rw [← nsmul_eq_mul]
      refine opNorm_le_bound _ (nsmul_nonneg (norm_nonneg g) (Fintype.card ι)) fun t => ?_
      simp_rw [LinearMap.coe_comp, LinearEquiv.coe_toLinearMap, Function.comp_apply,
        LinearMap.coe_toContinuousLinearMap', LinearEquiv.piRing_symm_apply]
      apply le_trans (norm_sum_le _ _)
      rw [smul_mul_assoc]
      refine Finset.sum_le_card_nsmul _ _ _ fun i _ => ?_
      rw [norm_smul]; rw [mul_comm]
      gcongr <;> apply norm_le_pi_norm }

/--
theorem `LinearIndependent.eventually` / 定理 `LinearIndependent.eventually`

English:
theorem LinearIndependent.eventually
  statement: {ι} [Finite ι] {f : ι -> E}
  proof: by
  cases nonempty_fintype ι
  classical
  simp only [Fintype.linearIndependent_iff'] at hf ⊢
  rcases LinearMap.exists_antilipschitzWith _ hf with ⟨K, K0, hK⟩
  have : Tendsto (fun g : ι -> E => ∑ i, ‖g i - f i‖) (𝓝 f) (𝓝 <| ∑ i, ‖f i - f i‖) :=
    tendsto_finsetSum _ fun i _ =>
Tendsto.norm ((continuous_apply i).tendsto _).sub tendsto_const_nhds
  simp only [sub_self, norm_zero, Finset.sum_const_zero] at this
  refine (this.eventually (gt_mem_nhds <| inv_pos.2 K0)).mono fun g hg => ?_
  replace hg : ∑ i, ‖g i - f i‖₊ < K⁻¹ := by
    rw [← NNReal.coe_lt_coe]
    push_cast
    exact hg
  rw [LinearMap.ker_eq_bot]
  refine (hK.add_sub_lipschitzWith (LipschitzWith.of_dist_le_mul fun v u => ?_) hg).injective
  simp only [dist_eq_norm, LinearMap.lsum_apply, Pi.sub_apply, LinearMap.sum_apply,
    LinearMap.comp_apply, LinearMap.proj_apply, LinearMap.smulRight_apply, LinearMap.id_apply, ←
    Finset.sum_sub_distrib, ← smul_sub, ← sub_smul, NNReal.coe_sum, coe_nnnorm, Finset.sum_mul]
  refine norm_sum_le_of_le _ fun i _ => ?_
  rw [norm_smul]; rw [mul_comm]
  gcongr
  exact norm_le_pi_norm (v - u) i

中文:
定理 LinearIndependent.eventually
  结论: {ι} [有限 ι] {f : ι -> E}
  证明: by
  cases nonempty_fintype ι
  classical
  simp only [Fintype.linearIndependent_iff'] at hf ⊢
  rcases LinearMap.exists_antilipschitzWith _ hf with ⟨K, K0, hK⟩
  have : Tendsto (fun g : ι -> E => ∑ i, ‖g i - f i‖) (𝓝 f) (𝓝 <| ∑ i, ‖f i - f i‖) :=
    tendsto_finsetSum _ fun i _ =>
Tendsto.norm ((continuous_apply i).tendsto _).sub tendsto_const_nhds
  simp only [sub_self, norm_zero, Finset.sum_const_zero] at this
  refine (this.eventually (gt_mem_nhds <| inv_pos.2 K0)).mono fun g hg => ?_
  replace hg : ∑ i, ‖g i - f i‖₊ < K⁻¹ := by
    rw [← NNReal.coe_lt_coe]
    push_cast
    exact hg
  rw [LinearMap.ker_eq_bot]
  refine (hK.add_sub_lipschitzWith (LipschitzWith.of_dist_le_mul fun v u => ?_) hg).injective
  simp only [dist_eq_norm, LinearMap.lsum_apply, Pi.sub_apply, LinearMap.sum_apply,
    LinearMap.comp_apply, LinearMap.proj_apply, LinearMap.smulRight_apply, LinearMap.id_apply, ←
    Finset.sum_sub_distrib, ← smul_sub, ← sub_smul, NNReal.coe_sum, coe_nnnorm, Finset.sum_mul]
  refine norm_sum_le_of_le _ fun i _ => ?_
  rw [norm_smul]; rw [mul_comm]
  gcongr
  exact norm_le_pi_norm (v - u) i
-/
protected theorem LinearIndependent.eventually {ι} [Finite ι] {f : ι -> E}
    (hf : LinearIndependent 𝕜 f) : forallᶠ g in 𝓝 f, LinearIndependent 𝕜 g := by
  cases nonempty_fintype ι
  classical
  simp only [Fintype.linearIndependent_iff'] at hf ⊢
  rcases LinearMap.exists_antilipschitzWith _ hf with ⟨K, K0, hK⟩
  have : Tendsto (fun g : ι -> E => ∑ i, ‖g i - f i‖) (𝓝 f) (𝓝 <| ∑ i, ‖f i - f i‖) :=
    tendsto_finsetSum _ fun i _ =>
Tendsto.norm ((continuous_apply i).tendsto _).sub tendsto_const_nhds
  simp only [sub_self, norm_zero, Finset.sum_const_zero] at this
  refine (this.eventually (gt_mem_nhds <| inv_pos.2 K0)).mono fun g hg => ?_
  replace hg : ∑ i, ‖g i - f i‖₊ < K⁻¹ := by
    rw [← NNReal.coe_lt_coe]
    push_cast
    exact hg
  rw [LinearMap.ker_eq_bot]
  refine (hK.add_sub_lipschitzWith (LipschitzWith.of_dist_le_mul fun v u => ?_) hg).injective
  simp only [dist_eq_norm, LinearMap.lsum_apply, Pi.sub_apply, LinearMap.sum_apply,
    LinearMap.comp_apply, LinearMap.proj_apply, LinearMap.smulRight_apply, LinearMap.id_apply, ←
    Finset.sum_sub_distrib, ← smul_sub, ← sub_smul, NNReal.coe_sum, coe_nnnorm, Finset.sum_mul]
  refine norm_sum_le_of_le _ fun i _ => ?_
  rw [norm_smul]; rw [mul_comm]
  gcongr
  exact norm_le_pi_norm (v - u) i

/--
theorem `isOpen_setOfPred_linearIndependent` / 定理 `isOpen_setOfPred_linearIndependent`

English:
theorem isOpen_setOfPred_linearIndependent
  given: {ι : Type*} [Finite ι]
  proof: isOpen_iff_mem_nhds.2 fun _ => LinearIndependent.eventually

@[deprecated (since := "2026-07-09")]
alias isOpen_setOf_linearIndependent := isOpen_setOfPred_linearIndependent

中文:
定理 isOpen_setOfPred_linearIndependent
  条件: {ι : 类型} [有限 ι]
  证明: isOpen_iff_mem_nhds.2 fun _ => LinearIndependent.eventually

@[deprecated (since := "2026-07-09")]
alias isOpen_setOf_linearIndependent := isOpen_setOfPred_linearIndependent

Depends on / 依赖: LinearIndependent, LinearIndependent.eventually, eventually, isOpen_iff_mem_nhds
-/
theorem isOpen_setOfPred_linearIndependent {ι : Type*} [Finite ι] :
    IsOpen { f : ι -> E | LinearIndependent 𝕜 f } :=
  isOpen_iff_mem_nhds.2 fun _ => LinearIndependent.eventually

@[deprecated (since := "2026-07-09")]
alias isOpen_setOf_linearIndependent := isOpen_setOfPred_linearIndependent

/--
theorem `isOpen_setOfPred_nat_le_rank` / 定理 `isOpen_setOfPred_nat_le_rank`

English:
theorem isOpen_setOfPred_nat_le_rank
  given: (n : Nat)
  proof: by
  simp only [LinearMap.le_rank_iff_exists_linearIndependent_finset, ofPred_exists, ← exists_prop]
  refine isOpen_biUnion fun t _ => ?_
  have : Continuous fun f : E ->L[𝕜] F => fun x : (t : Set E) => f x :=
    continuous_pi fun x => (ContinuousLinearMap.apply 𝕜 F (x : E)).continuous
  exact isOpen_setOfPred_linearIndependent.preimage this

@[deprecated (since := "2026-07-09")]
alias isOpen_setOf_nat_le_rank := isOpen_setOfPred_nat_le_rank

中文:
定理 isOpen_setOfPred_nat_le_rank
  条件: (n : 自然数)
  证明: by
  simp only [LinearMap.le_rank_iff_exists_linearIndependent_finset, ofPred_exists, ← exists_prop]
  refine isOpen_biUnion fun t _ => ?_
  have : Continuous fun f : E ->L[𝕜] F => fun x : (t : Set E) => f x :=
    continuous_pi fun x => (ContinuousLinearMap.apply 𝕜 F (x : E)).continuous
  exact isOpen_setOfPred_linearIndependent.preimage this

@[deprecated (since := "2026-07-09")]
alias isOpen_setOf_nat_le_rank := isOpen_setOfPred_nat_le_rank

Depends on / 依赖: Continuous, ContinuousLinearMap, ContinuousLinearMap.apply, LinearMap, LinearMap.le_rank_iff_exists_linearIndependent_finset, continuous, continuous_pi, exists_prop, isOpen_biUnion, isOpen_setOfPred_linearIndependent, isOpen_setOfPred_linearIndependent.preimage, le_rank_iff_exists_linearIndependent_finset, ofPred_exists, preimage
-/
theorem isOpen_setOfPred_nat_le_rank (n : Nat) :
    IsOpen { f : E ->L[𝕜] F | ↑n <= (f : E ->ₗ[𝕜] F).rank } := by
  simp only [LinearMap.le_rank_iff_exists_linearIndependent_finset, ofPred_exists, ← exists_prop]
  refine isOpen_biUnion fun t _ => ?_
  have : Continuous fun f : E ->L[𝕜] F => fun x : (t : Set E) => f x :=
    continuous_pi fun x => (ContinuousLinearMap.apply 𝕜 F (x : E)).continuous
  exact isOpen_setOfPred_linearIndependent.preimage this

@[deprecated (since := "2026-07-09")]
alias isOpen_setOf_nat_le_rank := isOpen_setOfPred_nat_le_rank

/--
theorem `isOpen_setOfPred_affineIndependent` / 定理 `isOpen_setOfPred_affineIndependent`

English:
theorem isOpen_setOfPred_affineIndependent
  given: {ι : Type*} [Finite ι]
  proof: by
  classical
  rcases isEmpty_or_nonempty ι with h | ⟨⟨i₀⟩⟩
  · exact isOpen_discrete _
  · simp_rw [affineIndependent_iff_linearIndependent_vsub 𝕜 _ i₀]
    let ι' := { x // x != i₀ }
    cases nonempty_fintype ι
    have : Fintype ι' := Subtype.fintype _
    convert_to!
      IsOpen ((fun (p : ι -> E) (i : ι') => p i -ᵥ p i₀) ⁻¹' {p : ι' -> E | LinearIndependent 𝕜 p})
    exact isOpen_setOfPred_linearIndependent.preimage (by fun_prop)

@[deprecated (since := "2026-07-09")]
alias isOpen_setOf_affineIndependent := isOpen_setOfPred_affineIndependent

中文:
定理 isOpen_setOfPred_affineIndependent
  条件: {ι : 类型} [有限 ι]
  证明: by
  classical
  rcases isEmpty_or_nonempty ι with h | ⟨⟨i₀⟩⟩
  · exact isOpen_discrete _
  · simp_rw [affineIndependent_iff_linearIndependent_vsub 𝕜 _ i₀]
    let ι' := { x // x != i₀ }
    cases nonempty_fintype ι
    have : Fintype ι' := Subtype.fintype _
    convert_to!
      IsOpen ((fun (p : ι -> E) (i : ι') => p i -ᵥ p i₀) ⁻¹' {p : ι' -> E | LinearIndependent 𝕜 p})
    exact isOpen_setOfPred_linearIndependent.preimage (by fun_prop)

@[deprecated (since := "2026-07-09")]
alias isOpen_setOf_affineIndependent := isOpen_setOfPred_affineIndependent

Depends on / 依赖: Fintype, IsOpen, LinearIndependent, Subtype, Subtype.fintype, affineIndependent_iff_linearIndependent_vsub, classical, convert_to, fintype, fun_prop, isEmpty_or_nonempty, isOpen_discrete, isOpen_setOfPred_linearIndependent, isOpen_setOfPred_linearIndependent.preimage, nonempty_fintype, preimage, simp_rw
-/
theorem isOpen_setOfPred_affineIndependent {ι : Type*} [Finite ι] :
    IsOpen {p : ι -> E | AffineIndependent 𝕜 p} := by
  classical
  rcases isEmpty_or_nonempty ι with h | ⟨⟨i₀⟩⟩
  · exact isOpen_discrete _
  · simp_rw [affineIndependent_iff_linearIndependent_vsub 𝕜 _ i₀]
    let ι' := { x // x != i₀ }
    cases nonempty_fintype ι
    have : Fintype ι' := Subtype.fintype _
    convert_to!
      IsOpen ((fun (p : ι -> E) (i : ι') => p i -ᵥ p i₀) ⁻¹' {p : ι' -> E | LinearIndependent 𝕜 p})
    exact isOpen_setOfPred_linearIndependent.preimage (by fun_prop)

@[deprecated (since := "2026-07-09")]
alias isOpen_setOf_affineIndependent := isOpen_setOfPred_affineIndependent

namespace Module.Basis

set_option backward.isDefEq.respectTransparency false in
/--
theorem `opNNNorm_le` / 定理 `opNNNorm_le`

English:
theorem opNNNorm_le
  statement: {ι : Type*} [Fintype ι] (v : Basis ι 𝕜 E) {u : E ->L[𝕜] F} (M : Real>=0)
  proof: u.opNNNorm_le_bound _ fun e => by
    set φ := v.equivFunL.toContinuousLinearMap
    calc
      ‖u e‖₊ = ‖u (∑ i, v.equivFun e i • v i)‖₊ := by rw [v.sum_equivFun]
      _ = ‖∑ i, v.equivFun e i • (u <| v i)‖₊ := by simp only [equivFun_apply, map_sum, map_smul]
      _ <= ∑ i, ‖v.equivFun e i • (u <| v i)‖₊ := nnnorm_sum_le _ _
      _ = ∑ i, ‖v.equivFun e i‖₊ * ‖u (v i)‖₊ := by simp only [nnnorm_smul]
      _ <= ∑ i, ‖v.equivFun e i‖₊ * M := by gcongr; apply hu
      _ = (∑ i, ‖v.equivFun e i‖₊) * M := by rw [Finset.sum_mul]
      _ <= Fintype.card ι • (‖φ‖₊ * ‖e‖₊) * M := by
        gcongr
        calc
          ∑ i, ‖v.equivFun e i‖₊ <= Fintype.card ι • ‖φ e‖₊ := Pi.sum_nnnorm_apply_le_nnnorm _
          _ <= Fintype.card ι • (‖φ‖₊ * ‖e‖₊) := nsmul_le_nsmul_right (φ.le_opNNNorm e) _
      _ = Fintype.card ι • ‖φ‖₊ * M * ‖e‖₊ := by simp only [smul_mul_assoc, mul_right_comm]

中文:
定理 opNNNorm_le
  结论: {ι : 类型} [有限类型 ι] (v : 基 ι 𝕜 E) {u : E ->L[𝕜] F} (M : 实数>=0)
  证明: u.opNNNorm_le_bound _ fun e => by
    set φ := v.equivFunL.toContinuousLinearMap
    calc
      ‖u e‖₊ = ‖u (∑ i, v.equivFun e i • v i)‖₊ := by rw [v.sum_equivFun]
      _ = ‖∑ i, v.equivFun e i • (u <| v i)‖₊ := by simp only [equivFun_apply, map_sum, map_smul]
      _ <= ∑ i, ‖v.equivFun e i • (u <| v i)‖₊ := nnnorm_sum_le _ _
      _ = ∑ i, ‖v.equivFun e i‖₊ * ‖u (v i)‖₊ := by simp only [nnnorm_smul]
      _ <= ∑ i, ‖v.equivFun e i‖₊ * M := by gcongr; apply hu
      _ = (∑ i, ‖v.equivFun e i‖₊) * M := by rw [Finset.sum_mul]
      _ <= Fintype.card ι • (‖φ‖₊ * ‖e‖₊) * M := by
        gcongr
        calc
          ∑ i, ‖v.equivFun e i‖₊ <= Fintype.card ι • ‖φ e‖₊ := Pi.sum_nnnorm_apply_le_nnnorm _
          _ <= Fintype.card ι • (‖φ‖₊ * ‖e‖₊) := nsmul_le_nsmul_right (φ.le_opNNNorm e) _
      _ = Fintype.card ι • ‖φ‖₊ * M * ‖e‖₊ := by simp only [smul_mul_assoc, mul_right_comm]

Depends on / 依赖: Finset, Finset.sum_mul, Fintype, equivFun, equivFunL, equivFun_apply, map_smul, map_sum, nnnorm_smul, nnnorm_sum_le, opNNNorm_le_bound, sum_equivFun, sum_mul, toContinuousLinearMap, u.opNNNorm_le_bound, v.equivFun, v.equivFunL.toContinuousLinearMap, v.sum_equivFun
-/
theorem opNNNorm_le {ι : Type*} [Fintype ι] (v : Basis ι 𝕜 E) {u : E ->L[𝕜] F} (M : Real>=0)
    (hu : forall i, ‖u (v i)‖₊ <= M) : ‖u‖₊ <= Fintype.card ι • ‖v.equivFunL.toContinuousLinearMap‖₊ * M :=
  u.opNNNorm_le_bound _ fun e => by
    set φ := v.equivFunL.toContinuousLinearMap
    calc
      ‖u e‖₊ = ‖u (∑ i, v.equivFun e i • v i)‖₊ := by rw [v.sum_equivFun]
      _ = ‖∑ i, v.equivFun e i • (u <| v i)‖₊ := by simp only [equivFun_apply, map_sum, map_smul]
      _ <= ∑ i, ‖v.equivFun e i • (u <| v i)‖₊ := nnnorm_sum_le _ _
      _ = ∑ i, ‖v.equivFun e i‖₊ * ‖u (v i)‖₊ := by simp only [nnnorm_smul]
      _ <= ∑ i, ‖v.equivFun e i‖₊ * M := by gcongr; apply hu
      _ = (∑ i, ‖v.equivFun e i‖₊) * M := by rw [Finset.sum_mul]
      _ <= Fintype.card ι • (‖φ‖₊ * ‖e‖₊) * M := by
        gcongr
        calc
          ∑ i, ‖v.equivFun e i‖₊ <= Fintype.card ι • ‖φ e‖₊ := Pi.sum_nnnorm_apply_le_nnnorm _
          _ <= Fintype.card ι • (‖φ‖₊ * ‖e‖₊) := nsmul_le_nsmul_right (φ.le_opNNNorm e) _
      _ = Fintype.card ι • ‖φ‖₊ * M * ‖e‖₊ := by simp only [smul_mul_assoc, mul_right_comm]

/--
theorem `opNorm_le` / 定理 `opNorm_le`

English:
theorem opNorm_le
  statement: {ι : Type*} [Fintype ι] (v : Basis ι 𝕜 E) {u : E ->L[𝕜] F} {M : Real}
  proof: by
  simpa using! NNReal.coe_le_coe.mpr (v.opNNNorm_le ⟨M, hM⟩ hu)

中文:
定理 opNorm_le
  结论: {ι : 类型} [有限类型 ι] (v : 基 ι 𝕜 E) {u : E ->L[𝕜] F} {M : 实数}
  证明: by
  simpa using! NNReal.coe_le_coe.mpr (v.opNNNorm_le ⟨M, hM⟩ hu)

Depends on / 依赖: NNReal, NNReal.coe_le_coe.mpr, coe_le_coe, opNNNorm_le, v.opNNNorm_le
-/
theorem opNorm_le {ι : Type*} [Fintype ι] (v : Basis ι 𝕜 E) {u : E ->L[𝕜] F} {M : Real}
    (hM : 0 <= M) (hu : forall i, ‖u (v i)‖ <= M) :
    ‖u‖ <= Fintype.card ι • ‖v.equivFunL.toContinuousLinearMap‖ * M := by
  simpa using! NNReal.coe_le_coe.mpr (v.opNNNorm_le ⟨M, hM⟩ hu)

/--
theorem `exists_opNNNorm_le` / 定理 `exists_opNNNorm_le`

English:
theorem exists_opNNNorm_le
  given: {ι : Type*} [Finite ι] (v : Basis ι 𝕜 E)
  proof: by
  cases nonempty_fintype ι
  exact
    ⟨max (Fintype.card ι • ‖v.equivFunL.toContinuousLinearMap‖₊) 1,
      zero_lt_one.trans_le (le_max_right _ _), fun {u} M hu =>
(v.opNNNorm_le M hu).trans mul_le_mul_of_nonneg_right (le_max_left _ _) zero_le⟩

中文:
定理 存在_opNNNorm_le
  条件: {ι : 类型} [有限 ι] (v : 基 ι 𝕜 E)
  证明: by
  cases nonempty_fintype ι
  exact
    ⟨max (Fintype.card ι • ‖v.equivFunL.toContinuousLinearMap‖₊) 1,
      zero_lt_one.trans_le (le_max_right _ _), fun {u} M hu =>
(v.opNNNorm_le M hu).trans mul_le_mul_of_nonneg_right (le_max_left _ _) zero_le⟩

Depends on / 依赖: Fintype, Fintype.card, equivFunL, le_max_left, le_max_right, mul_le_mul_of_nonneg_right, nonempty_fintype, opNNNorm_le, toContinuousLinearMap, trans_le, v.equivFunL.toContinuousLinearMap, v.opNNNorm_le, zero_le, zero_lt_one, zero_lt_one.trans_le
-/
theorem exists_opNNNorm_le {ι : Type*} [Finite ι] (v : Basis ι 𝕜 E) :
    exists C > (0 : Real>=0), forall {u : E ->L[𝕜] F} (M : Real>=0), (forall i, ‖u (v i)‖₊ <= M) -> ‖u‖₊ <= C * M := by
  cases nonempty_fintype ι
  exact
    ⟨max (Fintype.card ι • ‖v.equivFunL.toContinuousLinearMap‖₊) 1,
      zero_lt_one.trans_le (le_max_right _ _), fun {u} M hu =>
(v.opNNNorm_le M hu).trans mul_le_mul_of_nonneg_right (le_max_left _ _) zero_le⟩

/--
theorem `exists_opNorm_le` / 定理 `exists_opNorm_le`

English:
theorem exists_opNorm_le
  given: {ι : Type*} [Finite ι] (v : Basis ι 𝕜 E)
  proof: by
  obtain ⟨C, hC, h⟩ := v.exists_opNNNorm_le (F := F)
  refine ⟨C, hC, ?_⟩
  intro u M hM H
  simpa using! h ⟨M, hM⟩ H

中文:
定理 存在_opNorm_le
  条件: {ι : 类型} [有限 ι] (v : 基 ι 𝕜 E)
  证明: by
  obtain ⟨C, hC, h⟩ := v.exists_opNNNorm_le (F := F)
  refine ⟨C, hC, ?_⟩
  intro u M hM H
  simpa using! h ⟨M, hM⟩ H

Depends on / 依赖: exists_opNNNorm_le, v.exists_opNNNorm_le
-/
theorem exists_opNorm_le {ι : Type*} [Finite ι] (v : Basis ι 𝕜 E) :
    exists C > (0 : Real), forall {u : E ->L[𝕜] F} {M : Real}, 0 <= M -> (forall i, ‖u (v i)‖ <= M) -> ‖u‖ <= C * M := by
  obtain ⟨C, hC, h⟩ := v.exists_opNNNorm_le (F := F)
  refine ⟨C, hC, ?_⟩
  intro u M hM H
  simpa using! h ⟨M, hM⟩ H

end Module.Basis

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [FiniteDimensional
  signature: 𝕜 E] [SecondCountableTopology F] :
  body: by
  let d := Module.finrank 𝕜 E
  let e₁ : E ≃L[𝕜] Fin d -> 𝕜 :=
    ContinuousLinearEquiv.ofFinrankEq (finrank_fin_fun 𝕜).symm
  let e₂ : (E ->L[𝕜] F) ≃L[𝕜] Fin d -> F :=
    (e₁.arrowCongr (1 : F ≃L[𝕜] F)).trans (ContinuousLinearEquiv.piRing (Fin d))
  exact e₂.toHomeomorph.secondCountableTopology

中文:
实例 [有限维
  签名: 𝕜 E] [第二可数拓扑 F] :
  定义体: by
  let d := Module.finrank 𝕜 E
  let e₁ : E ≃L[𝕜] Fin d -> 𝕜 :=
    ContinuousLinearEquiv.ofFinrankEq (finrank_fin_fun 𝕜).symm
  let e₂ : (E ->L[𝕜] F) ≃L[𝕜] Fin d -> F :=
    (e₁.arrowCongr (1 : F ≃L[𝕜] F)).trans (ContinuousLinearEquiv.piRing (Fin d))
  exact e₂.toHomeomorph.secondCountableTopology

Depends on / 依赖: ContinuousLinearEquiv, ContinuousLinearEquiv.ofFinrankEq, ContinuousLinearEquiv.piRing, Module, Module.finrank, arrowCongr, finrank, finrank_fin_fun, ofFinrankEq, piRing, secondCountableTopology, toHomeomorph, toHomeomorph.secondCountableTopology
-/
instance [FiniteDimensional 𝕜 E] [SecondCountableTopology F] :
    SecondCountableTopology (E ->L[𝕜] F) := by
  let d := Module.finrank 𝕜 E
  let e₁ : E ≃L[𝕜] Fin d -> 𝕜 :=
    ContinuousLinearEquiv.ofFinrankEq (finrank_fin_fun 𝕜).symm
  let e₂ : (E ->L[𝕜] F) ≃L[𝕜] Fin d -> F :=
    (e₁.arrowCongr (1 : F ≃L[𝕜] F)).trans (ContinuousLinearEquiv.piRing (Fin d))
  exact e₂.toHomeomorph.secondCountableTopology

/--
theorem `AffineSubspace.closed_of_finiteDimensional` / 定理 `AffineSubspace.closed_of_finiteDimensional`

English:
theorem AffineSubspace.closed_of_finiteDimensional
  statement: {P : Type*} [MetricSpace P]
  proof: s.isClosed_direction_iff.mp s.direction.closed_of_finiteDimensional

中文:
定理 仿射子空间.closed_of_finiteDimensional
  结论: {P : 类型} [度量空间 P]
  证明: s.isClosed_direction_iff.mp s.direction.closed_of_finiteDimensional

Depends on / 依赖: closed_of_finiteDimensional, direction, isClosed_direction_iff, s.direction.closed_of_finiteDimensional, s.isClosed_direction_iff.mp
-/
theorem AffineSubspace.closed_of_finiteDimensional {P : Type*} [MetricSpace P]
    [NormedAddTorsor E P] (s : AffineSubspace 𝕜 P) [FiniteDimensional 𝕜 s.direction] :
    IsClosed (s : Set P) :=
  s.isClosed_direction_iff.mp s.direction.closed_of_finiteDimensional

section Riesz

/--
theorem `exists_norm_le_le_norm_sub_of_finset` / 定理 `exists_norm_le_le_norm_sub_of_finset`

English:
theorem exists_norm_le_le_norm_sub_of_finset
  statement: {c : 𝕜} (hc : 1 < ‖c‖) {R : Real} (hR : ‖c‖ < R)
  proof: by
  let F := Submodule.span 𝕜 (s : Set E)
  have hF : F.FG := ⟨s, rfl⟩
  have : FiniteDimensional 𝕜 F := .of_fg hF
  have Fclosed : IsClosed (F : Set E) := Submodule.closed_of_finiteDimensional _
  have : exists x, x ∉ F := by
    contrapose! h
    have : (⊤ : Submodule 𝕜 E) = F := by
      ext x
      simp [h]
    rw [← this] at hF
    exact .of_fg_top hF
  obtain ⟨x, xR, hx⟩ : exists x : E, ‖x‖ <= R ∧ forall y : E, y in F -> 1 <= ‖x - y‖ :=
    riesz_lemma_of_norm_lt hc hR Fclosed this
  have hx' : forall y : E, y in F -> 1 <= ‖y - x‖ := by
    intro y hy
    rw [← norm_neg]
    simpa using hx y hy
  exact ⟨x, xR, fun y hy => hx' _ (Submodule.subset_span hy)⟩

中文:
定理 存在_norm_le_le_norm_sub_of_finset
  结论: {c : 𝕜} (hc : 1 < ‖c‖) {R : 实数} (hR : ‖c‖ < R)
  证明: by
  let F := Submodule.span 𝕜 (s : Set E)
  have hF : F.FG := ⟨s, rfl⟩
  have : FiniteDimensional 𝕜 F := .of_fg hF
  have Fclosed : IsClosed (F : Set E) := Submodule.closed_of_finiteDimensional _
  have : exists x, x ∉ F := by
    contrapose! h
    have : (⊤ : Submodule 𝕜 E) = F := by
      ext x
      simp [h]
    rw [← this] at hF
    exact .of_fg_top hF
  obtain ⟨x, xR, hx⟩ : exists x : E, ‖x‖ <= R ∧ forall y : E, y in F -> 1 <= ‖x - y‖ :=
    riesz_lemma_of_norm_lt hc hR Fclosed this
  have hx' : forall y : E, y in F -> 1 <= ‖y - x‖ := by
    intro y hy
    rw [← norm_neg]
    simpa using hx y hy
  exact ⟨x, xR, fun y hy => hx' _ (Submodule.subset_span hy)⟩

Depends on / 依赖: F.FG, Fclosed, FiniteDimensional, IsClosed, Submodule, Submodule.closed_of_finiteDimensional, Submodule.span, closed_of_finiteDimensional, contrapose, of_fg, of_fg_top, riesz_lemma_of_norm_lt
-/
theorem exists_norm_le_le_norm_sub_of_finset {c : 𝕜} (hc : 1 < ‖c‖) {R : Real} (hR : ‖c‖ < R)
    (h : ¬FiniteDimensional 𝕜 E) (s : Finset E) : exists x : E, ‖x‖ <= R ∧ forall y in s, 1 <= ‖y - x‖ := by
  let F := Submodule.span 𝕜 (s : Set E)
  have hF : F.FG := ⟨s, rfl⟩
  have : FiniteDimensional 𝕜 F := .of_fg hF
  have Fclosed : IsClosed (F : Set E) := Submodule.closed_of_finiteDimensional _
  have : exists x, x ∉ F := by
    contrapose! h
    have : (⊤ : Submodule 𝕜 E) = F := by
      ext x
      simp [h]
    rw [← this] at hF
    exact .of_fg_top hF
  obtain ⟨x, xR, hx⟩ : exists x : E, ‖x‖ <= R ∧ forall y : E, y in F -> 1 <= ‖x - y‖ :=
    riesz_lemma_of_norm_lt hc hR Fclosed this
  have hx' : forall y : E, y in F -> 1 <= ‖y - x‖ := by
    intro y hy
    rw [← norm_neg]
    simpa using hx y hy
  exact ⟨x, xR, fun y hy => hx' _ (Submodule.subset_span hy)⟩

/--
theorem `exists_seq_norm_le_one_le_norm_sub'` / 定理 `exists_seq_norm_le_one_le_norm_sub'`

English:
theorem exists_seq_norm_le_one_le_norm_sub'
  statement: {c : 𝕜} (hc : 1 < ‖c‖) {R : Real} (hR : ‖c‖ < R)
  proof: by
  have : Std.Symm fun x y : E => 1 <= ‖x - y‖ := by
    constructor
    intro x y hxy
    rw [← norm_neg]
    simpa
  apply
    exists_seq_of_forall_finset_exists' (fun x : E => ‖x‖ <= R) fun (x : E) (y : E) => 1 <= ‖x - y‖
  rintro s -
  exact exists_norm_le_le_norm_sub_of_finset hc hR h s

中文:
定理 存在_seq_norm_le_one_le_norm_sub'
  结论: {c : 𝕜} (hc : 1 < ‖c‖) {R : 实数} (hR : ‖c‖ < R)
  证明: by
  have : Std.Symm fun x y : E => 1 <= ‖x - y‖ := by
    constructor
    intro x y hxy
    rw [← norm_neg]
    simpa
  apply
    exists_seq_of_forall_finset_exists' (fun x : E => ‖x‖ <= R) fun (x : E) (y : E) => 1 <= ‖x - y‖
  rintro s -
  exact exists_norm_le_le_norm_sub_of_finset hc hR h s

Depends on / 依赖: Std.Symm, exists_norm_le_le_norm_sub_of_finset, exists_seq_of_forall_finset_exists, norm_neg
-/
theorem exists_seq_norm_le_one_le_norm_sub' {c : 𝕜} (hc : 1 < ‖c‖) {R : Real} (hR : ‖c‖ < R)
    (h : ¬FiniteDimensional 𝕜 E) :
    exists f : Nat -> E, (forall n, ‖f n‖ <= R) ∧ Pairwise fun m n => 1 <= ‖f m - f n‖ := by
  have : Std.Symm fun x y : E => 1 <= ‖x - y‖ := by
    constructor
    intro x y hxy
    rw [← norm_neg]
    simpa
  apply
    exists_seq_of_forall_finset_exists' (fun x : E => ‖x‖ <= R) fun (x : E) (y : E) => 1 <= ‖x - y‖
  rintro s -
  exact exists_norm_le_le_norm_sub_of_finset hc hR h s

/--
theorem `exists_seq_norm_le_one_le_norm_sub` / 定理 `exists_seq_norm_le_one_le_norm_sub`

English:
theorem exists_seq_norm_le_one_le_norm_sub
  given: (h : ¬FiniteDimensional 𝕜 E)
  proof: by
  obtain ⟨c, hc⟩ : exists c : 𝕜, 1 < ‖c‖ := NormedField.exists_one_lt_norm 𝕜
  have A : ‖c‖ < ‖c‖ + 1 := by linarith
  rcases exists_seq_norm_le_one_le_norm_sub' hc A h with ⟨f, hf⟩
  exact ⟨‖c‖ + 1, f, hc.trans A, hf.1, hf.2⟩

中文:
定理 存在_seq_norm_le_one_le_norm_sub
  条件: (h : ¬有限维 𝕜 E)
  证明: by
  obtain ⟨c, hc⟩ : exists c : 𝕜, 1 < ‖c‖ := NormedField.exists_one_lt_norm 𝕜
  have A : ‖c‖ < ‖c‖ + 1 := by linarith
  rcases exists_seq_norm_le_one_le_norm_sub' hc A h with ⟨f, hf⟩
  exact ⟨‖c‖ + 1, f, hc.trans A, hf.1, hf.2⟩

Depends on / 依赖: NormedField, NormedField.exists_one_lt_norm, exists_one_lt_norm, exists_seq_norm_le_one_le_norm_sub, hc.trans
-/
theorem exists_seq_norm_le_one_le_norm_sub (h : ¬FiniteDimensional 𝕜 E) :
    exists (R : Real) (f : Nat -> E), 1 < R ∧ (forall n, ‖f n‖ <= R) ∧ Pairwise fun m n => 1 <= ‖f m - f n‖ := by
  obtain ⟨c, hc⟩ : exists c : 𝕜, 1 < ‖c‖ := NormedField.exists_one_lt_norm 𝕜
  have A : ‖c‖ < ‖c‖ + 1 := by linarith
  rcases exists_seq_norm_le_one_le_norm_sub' hc A h with ⟨f, hf⟩
  exact ⟨‖c‖ + 1, f, hc.trans A, hf.1, hf.2⟩

variable (𝕜)

/--
theorem `FiniteDimensional.of_isCompact_closedBall₀` / 定理 `FiniteDimensional.of_isCompact_closedBall₀`

English:
theorem FiniteDimensional.of_isCompact_closedBall₀
  statement: {V : Type*} [NormedAddCommGroup V] [Module 𝕜 V]
  proof: .of_totallyBounded_nhds_zero 𝕜 (Metric.closedBall_mem_nhds 0 rpos) h.totallyBounded

中文:
定理 有限维.of_isCompact_closedBall₀
  结论: {V : 类型} [赋范交换加群 V] [模 𝕜 V]
  证明: .of_totallyBounded_nhds_zero 𝕜 (Metric.closedBall_mem_nhds 0 rpos) h.totallyBounded

Depends on / 依赖: Metric, Metric.closedBall_mem_nhds, closedBall_mem_nhds, h.totallyBounded, of_totallyBounded_nhds_zero, totallyBounded
-/
theorem FiniteDimensional.of_isCompact_closedBall₀ {V : Type*} [NormedAddCommGroup V] [Module 𝕜 V]
    [ContinuousSMul 𝕜 V] {r : Real} (rpos : 0 < r) (h : IsCompact (Metric.closedBall (0 : V) r)) :
    FiniteDimensional 𝕜 V :=
  .of_totallyBounded_nhds_zero 𝕜 (Metric.closedBall_mem_nhds 0 rpos) h.totallyBounded

/--
theorem `FiniteDimensional.of_isCompact_closedBall` / 定理 `FiniteDimensional.of_isCompact_closedBall`

English:
theorem FiniteDimensional.of_isCompact_closedBall
  statement: {V : Type*} [NormedAddCommGroup V] [Module 𝕜 V]
  proof: .of_isCompact_closedBall₀ 𝕜 rpos by simpa using h.vadd (-c)

中文:
定理 有限维.of_isCompact_closedBall
  结论: {V : 类型} [赋范交换加群 V] [模 𝕜 V]
  证明: .of_isCompact_closedBall₀ 𝕜 rpos by simpa using h.vadd (-c)

Depends on / 依赖: h.vadd
-/
theorem FiniteDimensional.of_isCompact_closedBall {V : Type*} [NormedAddCommGroup V] [Module 𝕜 V]
    [ContinuousSMul 𝕜 V] {r : Real} (rpos : 0 < r) {c : V} (h : IsCompact (Metric.closedBall c r)) :
    FiniteDimensional 𝕜 V :=
.of_isCompact_closedBall₀ 𝕜 rpos by simpa using h.vadd (-c)

/--
lemma `ProperSpace.of_locallyCompactSpace` / 引理 `ProperSpace.of_locallyCompactSpace`

English:
lemma ProperSpace.of_locallyCompactSpace
  statement: (𝕜 : Type*) [NontriviallyNormedField 𝕜] {E : Type*}
  proof: by
  rcases exists_isCompact_closedBall (0 : E) with ⟨r, rpos, hr⟩
  rcases NormedField.exists_one_lt_norm 𝕜 with ⟨c, hc⟩
  have hC : forall n, IsCompact (closedBall (0 : E) (‖c‖ ^ n * r)) := fun n => by
have : c ^ n != 0 := pow_ne_zero _ fun h => by simp [h, zero_le_one.not_gt] at hc
    simpa [_root_.smul_closedBall' this] using hr.smul (c ^ n)
  have hTop : Tendsto (fun n => ‖c‖ ^ n * r) atTop atTop :=
    Tendsto.atTop_mul_const rpos (tendsto_pow_atTop_atTop_of_one_lt hc)
  exact .of_seq_closedBall hTop (Eventually.of_forall hC)

中文:
引理 真空间.of_locallyCompactSpace
  结论: (𝕜 : 类型) [NontriviallyNormedField 𝕜] {E : 类型}
  证明: by
  rcases exists_isCompact_closedBall (0 : E) with ⟨r, rpos, hr⟩
  rcases NormedField.exists_one_lt_norm 𝕜 with ⟨c, hc⟩
  have hC : forall n, IsCompact (closedBall (0 : E) (‖c‖ ^ n * r)) := fun n => by
have : c ^ n != 0 := pow_ne_zero _ fun h => by simp [h, zero_le_one.not_gt] at hc
    simpa [_root_.smul_closedBall' this] using hr.smul (c ^ n)
  have hTop : Tendsto (fun n => ‖c‖ ^ n * r) atTop atTop :=
    Tendsto.atTop_mul_const rpos (tendsto_pow_atTop_atTop_of_one_lt hc)
  exact .of_seq_closedBall hTop (Eventually.of_forall hC)

Depends on / 依赖: IsCompact, NormedField, NormedField.exists_one_lt_norm, Tendsto, Tendsto.atTop_mul_const, _root_, _root_.smul_closedBall, atTop_mul_const, closedBall, exists_isCompact_closedBall, exists_one_lt_norm, hr.smul, not_gt, of_seq_closedBall, pow_ne_zero, smul_closedBall, tendsto_pow_atTop_atTop_of_one_lt, zero_le_one, zero_le_one.not_gt
-/
lemma ProperSpace.of_locallyCompactSpace (𝕜 : Type*) [NontriviallyNormedField 𝕜] {E : Type*}
    [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] [LocallyCompactSpace E] : ProperSpace E := by
  rcases exists_isCompact_closedBall (0 : E) with ⟨r, rpos, hr⟩
  rcases NormedField.exists_one_lt_norm 𝕜 with ⟨c, hc⟩
  have hC : forall n, IsCompact (closedBall (0 : E) (‖c‖ ^ n * r)) := fun n => by
have : c ^ n != 0 := pow_ne_zero _ fun h => by simp [h, zero_le_one.not_gt] at hc
    simpa [_root_.smul_closedBall' this] using hr.smul (c ^ n)
  have hTop : Tendsto (fun n => ‖c‖ ^ n * r) atTop atTop :=
    Tendsto.atTop_mul_const rpos (tendsto_pow_atTop_atTop_of_one_lt hc)
  exact .of_seq_closedBall hTop (Eventually.of_forall hC)

/--
lemma `ProperSpace.of_locallyCompact_module` / 引理 `ProperSpace.of_locallyCompact_module`

English:
lemma ProperSpace.of_locallyCompact_module
  statement: (V : Type*) [AddCommGroup V] [TopologicalSpace V]
  proof: have : LocallyCompactSpace 𝕜 := by
    obtain ⟨v, hv⟩ : exists v : V, v != 0 := exists_ne 0
    let L : 𝕜 -> V := fun t => t • v
    have : IsClosedEmbedding L := isClosedEmbedding_smul_left hv
    apply IsClosedEmbedding.locallyCompactSpace this
  .of_locallyCompactSpace 𝕜

中文:
引理 真空间.of_locallyCompact_module
  结论: (V : 类型) [加法交换群 V] [拓扑空间 V]
  证明: have : LocallyCompactSpace 𝕜 := by
    obtain ⟨v, hv⟩ : exists v : V, v != 0 := exists_ne 0
    let L : 𝕜 -> V := fun t => t • v
    have : IsClosedEmbedding L := isClosedEmbedding_smul_left hv
    apply IsClosedEmbedding.locallyCompactSpace this
  .of_locallyCompactSpace 𝕜

Depends on / 依赖: IsClosedEmbedding, IsClosedEmbedding.locallyCompactSpace, LocallyCompactSpace, exists_ne, isClosedEmbedding_smul_left, locallyCompactSpace, of_locallyCompactSpace
-/
lemma ProperSpace.of_locallyCompact_module (V : Type*) [AddCommGroup V] [TopologicalSpace V]
    [IsTopologicalAddGroup V] [T2Space V] [Nontrivial V] [LocallyCompactSpace V] [Module 𝕜 V]
    [ContinuousSMul 𝕜 V] : ProperSpace 𝕜 :=
  have : LocallyCompactSpace 𝕜 := by
    obtain ⟨v, hv⟩ : exists v : V, v != 0 := exists_ne 0
    let L : 𝕜 -> V := fun t => t • v
    have : IsClosedEmbedding L := isClosedEmbedding_smul_left hv
    apply IsClosedEmbedding.locallyCompactSpace this
  .of_locallyCompactSpace 𝕜

end Riesz

open ContinuousLinearMap

/--
theorem `continuousWithinAt_clm_apply` / 定理 `continuousWithinAt_clm_apply`

English:
theorem continuousWithinAt_clm_apply
  statement: {X : Type*} [TopologicalSpace X] [FiniteDimensional 𝕜 E]
  proof: by
  refine ⟨fun h y => (apply 𝕜 F y).continuous.continuousAt.comp_continuousWithinAt h, fun h => ?_⟩
  let e : (E ->L[𝕜] F) ≃L[𝕜] Fin (finrank 𝕜 E) -> F :=
    ((ContinuousLinearEquiv.ofFinrankEq (finrank_fin_fun 𝕜).symm).arrowCongr
      (1 : F ≃L[𝕜] F)).trans (ContinuousLinearEquiv.piRing _)
  rw [e.toHomeomorph.isInducing.continuousWithinAt_iff]
  exact continuousWithinAt_pi.mpr fun i => h _

中文:
定理 continuousWithinAt_clm_apply
  结论: {X : 类型} [拓扑空间 X] [有限维 𝕜 E]
  证明: by
  refine ⟨fun h y => (apply 𝕜 F y).continuous.continuousAt.comp_continuousWithinAt h, fun h => ?_⟩
  let e : (E ->L[𝕜] F) ≃L[𝕜] Fin (finrank 𝕜 E) -> F :=
    ((ContinuousLinearEquiv.ofFinrankEq (finrank_fin_fun 𝕜).symm).arrowCongr
      (1 : F ≃L[𝕜] F)).trans (ContinuousLinearEquiv.piRing _)
  rw [e.toHomeomorph.isInducing.continuousWithinAt_iff]
  exact continuousWithinAt_pi.mpr fun i => h _

Depends on / 依赖: ContinuousLinearEquiv, ContinuousLinearEquiv.ofFinrankEq, ContinuousLinearEquiv.piRing, arrowCongr, comp_continuousWithinAt, continuous, continuous.continuousAt.comp_continuousWithinAt, continuousAt, continuousWithinAt_iff, continuousWithinAt_pi, continuousWithinAt_pi.mpr, e.toHomeomorph.isInducing.continuousWithinAt_iff, finrank, finrank_fin_fun, isInducing, ofFinrankEq, piRing, toHomeomorph
-/
theorem continuousWithinAt_clm_apply {X : Type*} [TopologicalSpace X] [FiniteDimensional 𝕜 E]
    {f : X -> E ->L[𝕜] F} {s : Set X} {x : X} :
    ContinuousWithinAt f s x ↔ forall y, ContinuousWithinAt (fun q => f q y) s x := by
  refine ⟨fun h y => (apply 𝕜 F y).continuous.continuousAt.comp_continuousWithinAt h, fun h => ?_⟩
  let e : (E ->L[𝕜] F) ≃L[𝕜] Fin (finrank 𝕜 E) -> F :=
    ((ContinuousLinearEquiv.ofFinrankEq (finrank_fin_fun 𝕜).symm).arrowCongr
      (1 : F ≃L[𝕜] F)).trans (ContinuousLinearEquiv.piRing _)
  rw [e.toHomeomorph.isInducing.continuousWithinAt_iff]
  exact continuousWithinAt_pi.mpr fun i => h _

/--
theorem `continuousOn_clm_apply` / 定理 `continuousOn_clm_apply`

English:
theorem continuousOn_clm_apply
  statement: {X : Type*} [TopologicalSpace X] [FiniteDimensional 𝕜 E]
  proof: by
  simp_rw [ContinuousOn, continuousWithinAt_clm_apply, imp_forall_iff]
  exact forall_comm

中文:
定理 continuousOn_clm_apply
  结论: {X : 类型} [拓扑空间 X] [有限维 𝕜 E]
  证明: by
  simp_rw [ContinuousOn, continuousWithinAt_clm_apply, imp_forall_iff]
  exact forall_comm

Depends on / 依赖: ContinuousOn, continuousWithinAt_clm_apply, forall_comm, imp_forall_iff, simp_rw
-/
theorem continuousOn_clm_apply {X : Type*} [TopologicalSpace X] [FiniteDimensional 𝕜 E]
    {f : X -> E ->L[𝕜] F} {s : Set X} :
    ContinuousOn f s ↔ forall y, ContinuousOn (fun x => f x y) s := by
  simp_rw [ContinuousOn, continuousWithinAt_clm_apply, imp_forall_iff]
  exact forall_comm

/--
theorem `continuousAt_clm_apply` / 定理 `continuousAt_clm_apply`

English:
theorem continuousAt_clm_apply
  statement: {X : Type*} [TopologicalSpace X] [FiniteDimensional 𝕜 E]
  proof: by
  simp_rw [← continuousWithinAt_univ, continuousWithinAt_clm_apply]

中文:
定理 continuousAt_clm_apply
  结论: {X : 类型} [拓扑空间 X] [有限维 𝕜 E]
  证明: by
  simp_rw [← continuousWithinAt_univ, continuousWithinAt_clm_apply]

Depends on / 依赖: continuousWithinAt_clm_apply, continuousWithinAt_univ, simp_rw
-/
theorem continuousAt_clm_apply {X : Type*} [TopologicalSpace X] [FiniteDimensional 𝕜 E]
    {f : X -> E ->L[𝕜] F} {x : X} :
    ContinuousAt f x ↔ forall y, ContinuousAt (fun q => f q y) x := by
  simp_rw [← continuousWithinAt_univ, continuousWithinAt_clm_apply]

/--
theorem `continuous_clm_apply` / 定理 `continuous_clm_apply`

English:
theorem continuous_clm_apply
  statement: {X : Type*} [TopologicalSpace X] [FiniteDimensional 𝕜 E]
  proof: by
  simp_rw [← continuousOn_univ, continuousOn_clm_apply]

中文:
定理 continuous_clm_apply
  结论: {X : 类型} [拓扑空间 X] [有限维 𝕜 E]
  证明: by
  simp_rw [← continuousOn_univ, continuousOn_clm_apply]

Depends on / 依赖: continuousOn_clm_apply, continuousOn_univ, simp_rw
-/
theorem continuous_clm_apply {X : Type*} [TopologicalSpace X] [FiniteDimensional 𝕜 E]
    {f : X -> E ->L[𝕜] F} : Continuous f ↔ forall y, Continuous (f · y) := by
  simp_rw [← continuousOn_univ, continuousOn_clm_apply]

end CompleteField

section LocallyCompactField

variable (𝕜 : Type u) [NontriviallyNormedField 𝕜] (E : Type v) [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] [LocallyCompactSpace 𝕜]

/--
theorem `FiniteDimensional.proper` / 定理 `FiniteDimensional.proper`

English:
theorem FiniteDimensional.proper
  given: [FiniteDimensional 𝕜 E]
  statement: ProperSpace E
  proof: by
  have : ProperSpace 𝕜 := .of_locallyCompactSpace 𝕜
  set e := ContinuousLinearEquiv.ofFinrankEq (@finrank_fin_fun 𝕜 _ _ (finrank 𝕜 E)).symm
  exact e.symm.antilipschitz.properSpace e.symm.continuous e.symm.surjective

中文:
定理 有限维.proper
  条件: [有限维 𝕜 E]
  结论: 真空间 E
  证明: by
  have : ProperSpace 𝕜 := .of_locallyCompactSpace 𝕜
  set e := ContinuousLinearEquiv.ofFinrankEq (@finrank_fin_fun 𝕜 _ _ (finrank 𝕜 E)).symm
  exact e.symm.antilipschitz.properSpace e.symm.continuous e.symm.surjective

Depends on / 依赖: ContinuousLinearEquiv, ContinuousLinearEquiv.ofFinrankEq, ProperSpace, antilipschitz, continuous, e.symm.antilipschitz.properSpace, e.symm.continuous, e.symm.surjective, finrank, finrank_fin_fun, ofFinrankEq, of_locallyCompactSpace, properSpace, surjective
-/
theorem FiniteDimensional.proper [FiniteDimensional 𝕜 E] : ProperSpace E := by
  have : ProperSpace 𝕜 := .of_locallyCompactSpace 𝕜
  set e := ContinuousLinearEquiv.ofFinrankEq (@finrank_fin_fun 𝕜 _ _ (finrank 𝕜 E)).symm
  exact e.symm.antilipschitz.properSpace e.symm.continuous e.symm.surjective

end LocallyCompactField

/-- Over the real numbers, we can register the previous statement as an instance as it will not
cause problems in instance resolution since the properness of `ℝ` is already known. -/
instance (priority := 900) FiniteDimensional.proper_real (E : Type u) [NormedAddCommGroup E]
    [NormedSpace Real E] [FiniteDimensional Real E] : ProperSpace E :=
  FiniteDimensional.proper Real E

/-- A submodule of a locally compact space over a complete field is also locally compact (and even
proper). -/
instance {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [LocallyCompactSpace E] (S : Submodule 𝕜 E) :
    ProperSpace S := by
  nontriviality E
  have : ProperSpace 𝕜 := .of_locallyCompact_module 𝕜 E
  have : FiniteDimensional 𝕜 E := .of_locallyCompactSpace 𝕜
  exact FiniteDimensional.proper 𝕜 S

/--
theorem `exists_mem_frontier_infDist_compl_eq_dist` / 定理 `exists_mem_frontier_infDist_compl_eq_dist`

English:
theorem exists_mem_frontier_infDist_compl_eq_dist
  statement: {E : Type*} [NormedAddCommGroup E]
  proof: by
  rcases Metric.exists_mem_closure_infDist_eq_dist (nonempty_compl.2 hs) x with ⟨y, hys, hyd⟩
  rw [closure_compl] at hys
refine ⟨y, ⟨Metric.closedBall_infDist_compl_subset_closure hx
Metric.mem_closedBall.2 ge_of_eq ?_, hys⟩, hyd⟩
  rwa [dist_comm]

中文:
定理 存在_mem_frontier_infDist_compl_eq_dist
  结论: {E : 类型} [赋范交换加群 E]
  证明: by
  rcases Metric.exists_mem_closure_infDist_eq_dist (nonempty_compl.2 hs) x with ⟨y, hys, hyd⟩
  rw [closure_compl] at hys
refine ⟨y, ⟨Metric.closedBall_infDist_compl_subset_closure hx
Metric.mem_closedBall.2 ge_of_eq ?_, hys⟩, hyd⟩
  rwa [dist_comm]

Depends on / 依赖: Metric, Metric.closedBall_infDist_compl_subset_closure, Metric.exists_mem_closure_infDist_eq_dist, Metric.mem_closedBall, closedBall_infDist_compl_subset_closure, closure_compl, dist_comm, exists_mem_closure_infDist_eq_dist, ge_of_eq, mem_closedBall, nonempty_compl
-/
theorem exists_mem_frontier_infDist_compl_eq_dist {E : Type*} [NormedAddCommGroup E]
    [NormedSpace Real E] [FiniteDimensional Real E] {x : E} {s : Set E} (hx : x in s) (hs : s != univ) :
    exists y in frontier s, Metric.infDist x sᶜ = dist x y := by
  rcases Metric.exists_mem_closure_infDist_eq_dist (nonempty_compl.2 hs) x with ⟨y, hys, hyd⟩
  rw [closure_compl] at hys
refine ⟨y, ⟨Metric.closedBall_infDist_compl_subset_closure hx
Metric.mem_closedBall.2 ge_of_eq ?_, hys⟩, hyd⟩
  rwa [dist_comm]

/-- If `K` is a compact set in a nontrivial real normed space and `x ∈ K`, then there exists a point
`y` of the boundary of `K` at distance `Metric.infDist x Kᶜ` from `x`. See also
`exists_mem_frontier_infDist_compl_eq_dist`. -/
nonrec theorem IsCompact.exists_mem_frontier_infDist_compl_eq_dist {E : Type*}
    [NormedAddCommGroup E] [NormedSpace Real E] [Nontrivial E] {x : E} {K : Set E} (hK : IsCompact K)
    (hx : x in K) :
    exists y in frontier K, Metric.infDist x Kᶜ = dist x y := by
  obtain hx' | hx' : x in interior K union frontier K := by
    rw [← closure_eq_interior_union_frontier]
    exact subset_closure hx
  · rw [mem_interior_iff_mem_nhds, Metric.nhds_basis_closedBall.mem_iff] at hx'
    rcases hx' with ⟨r, hr₀, hrK⟩
    have : FiniteDimensional Real E :=
      .of_isCompact_closedBall Real hr₀
        (hK.of_isClosed_subset Metric.isClosed_closedBall hrK)
    exact exists_mem_frontier_infDist_compl_eq_dist hx hK.ne_univ
  · refine ⟨x, hx', ?_⟩
    rw [frontier_eq_closure_inter_closure] at hx'
    rw [Metric.infDist_zero_of_mem_closure hx'.2]; rw [dist_self]

/--
theorem `summable_norm_iff` / 定理 `summable_norm_iff`

English:
theorem summable_norm_iff
  statement: {α E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  proof: by
  refine ⟨Summable.of_norm, fun hf => ?_⟩
  -- First we use a finite basis to reduce the problem to the case `E = Fin N → ℝ`
  suffices forall {N : Nat} {g : α -> Fin N -> Real}, Summable g -> Summable fun x => ‖g x‖ by
    obtain v := Module.finBasis Real E
    set e := v.equivFunL
    have H : Summable fun x => ‖e (f x)‖ := this (e.summable.2 hf)
    refine .of_norm_bounded (H.mul_left ↑‖(e.symm : (Fin (finrank Real E) -> Real) ->L[Real] E)‖₊) fun i => ?_
    simpa using (e.symm : (Fin (finrank Real E) -> Real) ->L[Real] E).le_opNorm (e <| f i)
  clear! E
  -- Now we deal with `g : α → Fin N → ℝ`
  intro N g hg
  have : forall i, Summable fun x => ‖g x i‖ := fun i => (Pi.summable.1 hg i).abs
  refine .of_norm_bounded (summable_sum fun i (_ : i in Finset.univ) => this i) fun x => ?_
  rw [norm_norm]; rw [pi_norm_le_iff_of_nonneg]
  · refine fun i => Finset.single_le_sum (f := fun i => ‖g x i‖) (fun i _ => ?_) (Finset.mem_univ i)
    exact norm_nonneg (g x i)
  · exact Finset.sum_nonneg fun _ _ => norm_nonneg _

alias ⟨_, Summable.norm⟩ := summable_norm_iff

中文:
定理 summable_norm_iff
  结论: {α E : 类型} [赋范交换加群 E] [赋范空间 实数 E]
  证明: by
  refine ⟨Summable.of_norm, fun hf => ?_⟩
  -- First we use a finite basis to reduce the problem to the case `E = Fin N → ℝ`
  suffices forall {N : Nat} {g : α -> Fin N -> Real}, Summable g -> Summable fun x => ‖g x‖ by
    obtain v := Module.finBasis Real E
    set e := v.equivFunL
    have H : Summable fun x => ‖e (f x)‖ := this (e.summable.2 hf)
    refine .of_norm_bounded (H.mul_left ↑‖(e.symm : (Fin (finrank Real E) -> Real) ->L[Real] E)‖₊) fun i => ?_
    simpa using (e.symm : (Fin (finrank Real E) -> Real) ->L[Real] E).le_opNorm (e <| f i)
  clear! E
  -- Now we deal with `g : α → Fin N → ℝ`
  intro N g hg
  have : forall i, Summable fun x => ‖g x i‖ := fun i => (Pi.summable.1 hg i).abs
  refine .of_norm_bounded (summable_sum fun i (_ : i in Finset.univ) => this i) fun x => ?_
  rw [norm_norm]; rw [pi_norm_le_iff_of_nonneg]
  · refine fun i => Finset.single_le_sum (f := fun i => ‖g x i‖) (fun i _ => ?_) (Finset.mem_univ i)
    exact norm_nonneg (g x i)
  · exact Finset.sum_nonneg fun _ _ => norm_nonneg _

alias ⟨_, Summable.norm⟩ := summable_norm_iff

Depends on / 依赖: Summable, Summable.of_norm, of_norm
-/
theorem summable_norm_iff {α E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    [FiniteDimensional Real E] {f : α -> E} : (Summable fun x => ‖f x‖) ↔ Summable f := by
  refine ⟨Summable.of_norm, fun hf => ?_⟩
  -- First we use a finite basis to reduce the problem to the case `E = Fin N → ℝ`
  suffices forall {N : Nat} {g : α -> Fin N -> Real}, Summable g -> Summable fun x => ‖g x‖ by
    obtain v := Module.finBasis Real E
    set e := v.equivFunL
    have H : Summable fun x => ‖e (f x)‖ := this (e.summable.2 hf)
    refine .of_norm_bounded (H.mul_left ↑‖(e.symm : (Fin (finrank Real E) -> Real) ->L[Real] E)‖₊) fun i => ?_
    simpa using (e.symm : (Fin (finrank Real E) -> Real) ->L[Real] E).le_opNorm (e <| f i)
  clear! E
  -- Now we deal with `g : α → Fin N → ℝ`
  intro N g hg
  have : forall i, Summable fun x => ‖g x i‖ := fun i => (Pi.summable.1 hg i).abs
  refine .of_norm_bounded (summable_sum fun i (_ : i in Finset.univ) => this i) fun x => ?_
  rw [norm_norm]; rw [pi_norm_le_iff_of_nonneg]
  · refine fun i => Finset.single_le_sum (f := fun i => ‖g x i‖) (fun i _ => ?_) (Finset.mem_univ i)
    exact norm_nonneg (g x i)
  · exact Finset.sum_nonneg fun _ _ => norm_nonneg _

alias ⟨_, Summable.norm⟩ := summable_norm_iff

/--
theorem `summable_of_sum_range_norm_le` / 定理 `summable_of_sum_range_norm_le`

English:
theorem summable_of_sum_range_norm_le
  statement: {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  proof: summable_norm_iff.mp summable_of_sum_range_le (fun _ => norm_nonneg _) h

中文:
定理 summable_of_sum_range_norm_le
  结论: {E : 类型} [赋范交换加群 E] [赋范空间 实数 E]
  证明: summable_norm_iff.mp summable_of_sum_range_le (fun _ => norm_nonneg _) h

Depends on / 依赖: norm_nonneg, summable_norm_iff, summable_norm_iff.mp, summable_of_sum_range_le
-/
theorem summable_of_sum_range_norm_le {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    [FiniteDimensional Real E] {c : Real} {f : Nat -> E} (h : forall n, ∑ i in Finset.range n, ‖f i‖ <= c) :
    Summable f :=
summable_norm_iff.mp summable_of_sum_range_le (fun _ => norm_nonneg _) h

/--
theorem `summable_of_isBigO'` / 定理 `summable_of_isBigO'`

English:
theorem summable_of_isBigO'
  statement: {ι E F : Type*} [NormedAddCommGroup E] [CompleteSpace E]
  proof: summable_of_isBigO hg.norm h.norm_right

中文:
定理 summable_of_isBigO'
  结论: {ι E F : 类型} [赋范交换加群 E] [完备空间 E]
  证明: summable_of_isBigO hg.norm h.norm_right

Depends on / 依赖: h.norm_right, hg.norm, norm_right, summable_of_isBigO
-/
theorem summable_of_isBigO' {ι E F : Type*} [NormedAddCommGroup E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace Real F] [FiniteDimensional Real F] {f : ι -> E} {g : ι -> F}
    (hg : Summable g) (h : f =O[cofinite] g) : Summable f :=
  summable_of_isBigO hg.norm h.norm_right

/--
lemma `Asymptotics.IsBigO.comp_summable` / 引理 `Asymptotics.IsBigO.comp_summable`

English:
lemma Asymptotics.IsBigO.comp_summable
  statement: {ι E F : Type*}
  proof: .of_norm hf.comp_summable_norm hg.norm

中文:
引理 Asymptotics.IsBigO.comp_summable
  结论: {ι E F : 类型}
  证明: .of_norm hf.comp_summable_norm hg.norm

Depends on / 依赖: comp_summable_norm, hf.comp_summable_norm, hg.norm, of_norm
-/
lemma Asymptotics.IsBigO.comp_summable {ι E F : Type*}
    [NormedAddCommGroup E] [NormedSpace Real E] [FiniteDimensional Real E]
    [NormedAddCommGroup F] [CompleteSpace F]
    {f : E -> F} (hf : f =O[𝓝 0] id) {g : ι -> E} (hg : Summable g) : Summable (f ∘ g) :=
.of_norm hf.comp_summable_norm hg.norm

/--
theorem `summable_of_isBigO_nat'` / 定理 `summable_of_isBigO_nat'`

English:
theorem summable_of_isBigO_nat'
  statement: {E F : Type*} [NormedAddCommGroup E] [CompleteSpace E]
  proof: summable_of_isBigO_nat hg.norm h.norm_right

中文:
定理 summable_of_isBigO_nat'
  结论: {E F : 类型} [赋范交换加群 E] [完备空间 E]
  证明: summable_of_isBigO_nat hg.norm h.norm_right

Depends on / 依赖: h.norm_right, hg.norm, norm_right, summable_of_isBigO_nat
-/
theorem summable_of_isBigO_nat' {E F : Type*} [NormedAddCommGroup E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace Real F] [FiniteDimensional Real F] {f : Nat -> E} {g : Nat -> F}
    (hg : Summable g) (h : f =O[atTop] g) : Summable f :=
  summable_of_isBigO_nat hg.norm h.norm_right


open Nat Asymptotics in
/--
theorem `summable_norm_mul_geometric_of_norm_lt_one'` / 定理 `summable_norm_mul_geometric_of_norm_lt_one'`

English:
theorem summable_norm_mul_geometric_of_norm_lt_one'
  statement: {F : Type*} [NormedRing F]
  proof: by
  rcases exists_between hr with ⟨r', hrr', h⟩
  apply summable_of_isBigO_nat (summable_geometric_of_lt_one ((norm_nonneg _).trans hrr'.le) h).norm
  calc
  fun n => ‖(u n) * r ^ n‖
  _ =O[atTop] fun n => ‖u n‖ * ‖r‖ ^ n := by
      apply (IsBigOWith.of_bound (c := ‖(1 : Real)‖) ?_).isBigO
      filter_upwards [eventually_norm_pow_le r] with n hn
      simp
  _ =O[atTop] fun n => ‖((n : F) ^ k)‖ * ‖r‖ ^ n := by
      simpa [Nat.cast_pow] using
      (isBigO_norm_left.mpr (isBigO_norm_right.mpr hu)).mul (isBigO_refl (fun n => (‖r‖ ^ n)) atTop)
  _ =O[atTop] fun n => ‖r' ^ n‖ := by
      convert!
        isBigO_norm_right.mpr
          (isBigO_norm_left.mpr
            (isLittleO_pow_const_mul_const_pow_const_pow_of_norm_lt k hrr').isBigO)
      simp only [norm_pow, norm_mul]

中文:
定理 summable_norm_mul_geometric_of_norm_lt_one'
  结论: {F : 类型} [赋范环 F]
  证明: by
  rcases exists_between hr with ⟨r', hrr', h⟩
  apply summable_of_isBigO_nat (summable_geometric_of_lt_one ((norm_nonneg _).trans hrr'.le) h).norm
  calc
  fun n => ‖(u n) * r ^ n‖
  _ =O[atTop] fun n => ‖u n‖ * ‖r‖ ^ n := by
      apply (IsBigOWith.of_bound (c := ‖(1 : Real)‖) ?_).isBigO
      filter_upwards [eventually_norm_pow_le r] with n hn
      simp
  _ =O[atTop] fun n => ‖((n : F) ^ k)‖ * ‖r‖ ^ n := by
      simpa [Nat.cast_pow] using
      (isBigO_norm_left.mpr (isBigO_norm_right.mpr hu)).mul (isBigO_refl (fun n => (‖r‖ ^ n)) atTop)
  _ =O[atTop] fun n => ‖r' ^ n‖ := by
      convert!
        isBigO_norm_right.mpr
          (isBigO_norm_left.mpr
            (isLittleO_pow_const_mul_const_pow_const_pow_of_norm_lt k hrr').isBigO)
      simp only [norm_pow, norm_mul]

Depends on / 依赖: IsBigOWith, IsBigOWith.of_bound, Nat.cast_pow, cast_pow, eventually_norm_pow_le, exists_between, filter_upwards, isBigO, isBigO_norm_left, isBigO_norm_left.mpr, isBigO_norm_right, isBigO_norm_right.mpr, isBigO_refl, norm_nonneg, of_bound, summable_geometric_of_lt_one, summable_of_isBigO_nat
-/
theorem summable_norm_mul_geometric_of_norm_lt_one' {F : Type*} [NormedRing F]
    [NormOneClass F] [NormMulClass F] {k : Nat} {r : F} (hr : ‖r‖ < 1) {u : Nat -> F}
    (hu : u =O[atTop] fun n => ((n ^ k : Nat) : F)) : Summable fun n : Nat => ‖u n * r ^ n‖ := by
  rcases exists_between hr with ⟨r', hrr', h⟩
  apply summable_of_isBigO_nat (summable_geometric_of_lt_one ((norm_nonneg _).trans hrr'.le) h).norm
  calc
  fun n => ‖(u n) * r ^ n‖
  _ =O[atTop] fun n => ‖u n‖ * ‖r‖ ^ n := by
      apply (IsBigOWith.of_bound (c := ‖(1 : Real)‖) ?_).isBigO
      filter_upwards [eventually_norm_pow_le r] with n hn
      simp
  _ =O[atTop] fun n => ‖((n : F) ^ k)‖ * ‖r‖ ^ n := by
      simpa [Nat.cast_pow] using
      (isBigO_norm_left.mpr (isBigO_norm_right.mpr hu)).mul (isBigO_refl (fun n => (‖r‖ ^ n)) atTop)
  _ =O[atTop] fun n => ‖r' ^ n‖ := by
      convert!
        isBigO_norm_right.mpr
          (isBigO_norm_left.mpr
            (isLittleO_pow_const_mul_const_pow_const_pow_of_norm_lt k hrr').isBigO)
      simp only [norm_pow, norm_mul]

/--
theorem `summable_of_isEquivalent` / 定理 `summable_of_isEquivalent`

English:
theorem summable_of_isEquivalent
  statement: {ι E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  proof: summable_of_isBigO' hg h.isBigO

中文:
定理 summable_of_isEquivalent
  结论: {ι E : 类型} [赋范交换加群 E] [赋范空间 实数 E]
  证明: summable_of_isBigO' hg h.isBigO

Depends on / 依赖: h.isBigO, isBigO, summable_of_isBigO
-/
theorem summable_of_isEquivalent {ι E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    [FiniteDimensional Real E] {f : ι -> E} {g : ι -> E} (hg : Summable g) (h : f ~[cofinite] g) :
    Summable f :=
  summable_of_isBigO' hg h.isBigO

/--
theorem `summable_of_isEquivalent_nat` / 定理 `summable_of_isEquivalent_nat`

English:
theorem summable_of_isEquivalent_nat
  statement: {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  proof: summable_of_isBigO_nat' hg h.isBigO

中文:
定理 summable_of_isEquivalent_nat
  结论: {E : 类型} [赋范交换加群 E] [赋范空间 实数 E]
  证明: summable_of_isBigO_nat' hg h.isBigO

Depends on / 依赖: h.isBigO, isBigO, summable_of_isBigO_nat
-/
theorem summable_of_isEquivalent_nat {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    [FiniteDimensional Real E] {f : Nat -> E} {g : Nat -> E} (hg : Summable g) (h : f ~[atTop] g) :
    Summable f :=
  summable_of_isBigO_nat' hg h.isBigO

/--
theorem `Asymptotics.IsTheta.summable_iff` / 定理 `Asymptotics.IsTheta.summable_iff`

English:
theorem Asymptotics.IsTheta.summable_iff
  statement: {ι E F : Type*} [NormedAddCommGroup E]
  proof: ⟨fun hf => summable_of_isBigO' hf h.isBigO_symm, fun hg => summable_of_isBigO' hg h.isBigO⟩

中文:
定理 Asymptotics.IsTheta.summable_iff
  结论: {ι E F : 类型} [赋范交换加群 E]
  证明: ⟨fun hf => summable_of_isBigO' hf h.isBigO_symm, fun hg => summable_of_isBigO' hg h.isBigO⟩

Depends on / 依赖: h.isBigO, h.isBigO_symm, isBigO, isBigO_symm, summable_of_isBigO
-/
theorem Asymptotics.IsTheta.summable_iff {ι E F : Type*} [NormedAddCommGroup E]
  [NormedAddCommGroup F] [NormedSpace Real E] [NormedSpace Real F] [FiniteDimensional Real E]
  [FiniteDimensional Real F] {f : ι -> E} {g : ι -> F} (h : f =Θ[cofinite] g) :
    Summable f ↔ Summable g :=
  ⟨fun hf => summable_of_isBigO' hf h.isBigO_symm, fun hg => summable_of_isBigO' hg h.isBigO⟩

/--
theorem `Asymptotics.IsTheta.summable_iff_nat` / 定理 `Asymptotics.IsTheta.summable_iff_nat`

English:
theorem Asymptotics.IsTheta.summable_iff_nat
  statement: {E F : Type*} [NormedAddCommGroup E]
  proof: IsTheta.summable_iff by simpa [← Nat.cofinite_eq_atTop] using h

中文:
定理 Asymptotics.IsTheta.summable_iff_nat
  结论: {E F : 类型} [赋范交换加群 E]
  证明: IsTheta.summable_iff by simpa [← Nat.cofinite_eq_atTop] using h

Depends on / 依赖: IsTheta, IsTheta.summable_iff, Nat.cofinite_eq_atTop, cofinite_eq_atTop, summable_iff
-/
theorem Asymptotics.IsTheta.summable_iff_nat {E F : Type*} [NormedAddCommGroup E]
  [NormedAddCommGroup F] [NormedSpace Real E] [NormedSpace Real F] [FiniteDimensional Real E]
  [FiniteDimensional Real F] {f : Nat -> E} {g : Nat -> F} (h : f =Θ[atTop] g) :
    Summable f ↔ Summable g :=
IsTheta.summable_iff by simpa [← Nat.cofinite_eq_atTop] using h

/--
theorem `Asymptotics.IsEquivalent.summable_iff` / 定理 `Asymptotics.IsEquivalent.summable_iff`

English:
theorem Asymptotics.IsEquivalent.summable_iff
  statement: {ι E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  proof: h.isTheta.summable_iff

@[deprecated (since := "2026-02-07")]
alias IsEquivalent.summable_iff := Asymptotics.IsEquivalent.summable_iff

中文:
定理 Asymptotics.IsEquivalent.summable_iff
  结论: {ι E : 类型} [赋范交换加群 E] [赋范空间 实数 E]
  证明: h.isTheta.summable_iff

@[deprecated (since := "2026-02-07")]
alias IsEquivalent.summable_iff := Asymptotics.IsEquivalent.summable_iff

Depends on / 依赖: h.isTheta.summable_iff, isTheta, summable_iff
-/
theorem Asymptotics.IsEquivalent.summable_iff {ι E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    [FiniteDimensional Real E] {f : ι -> E} {g : ι -> E} (h : f ~[cofinite] g) :
    Summable f ↔ Summable g :=
  h.isTheta.summable_iff

@[deprecated (since := "2026-02-07")]
alias IsEquivalent.summable_iff := Asymptotics.IsEquivalent.summable_iff

/--
theorem `Asymptotics.IsEquivalent.summable_iff_nat` / 定理 `Asymptotics.IsEquivalent.summable_iff_nat`

English:
theorem Asymptotics.IsEquivalent.summable_iff_nat
  statement: {E : Type*} [NormedAddCommGroup E]
  proof: h.isTheta.summable_iff_nat

@[deprecated (since := "2026-02-07")]
alias IsEquivalent.summable_iff_nat := Asymptotics.IsEquivalent.summable_iff_nat

中文:
定理 Asymptotics.IsEquivalent.summable_iff_nat
  结论: {E : 类型} [赋范交换加群 E]
  证明: h.isTheta.summable_iff_nat

@[deprecated (since := "2026-02-07")]
alias IsEquivalent.summable_iff_nat := Asymptotics.IsEquivalent.summable_iff_nat

Depends on / 依赖: h.isTheta.summable_iff_nat, isTheta, summable_iff_nat
-/
theorem Asymptotics.IsEquivalent.summable_iff_nat {E : Type*} [NormedAddCommGroup E]
    [NormedSpace Real E] [FiniteDimensional Real E] {f : Nat -> E} {g : Nat -> E} (h : f ~[atTop] g) :
    Summable f ↔ Summable g :=
  h.isTheta.summable_iff_nat

@[deprecated (since := "2026-02-07")]
alias IsEquivalent.summable_iff_nat := Asymptotics.IsEquivalent.summable_iff_nat

namespace Module.Basis

variable {ι R M : Type*} [Finite ι]
  [NontriviallyNormedField R] [CompleteSpace R]
  [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M] [T2Space M]
  [Module R M] [ContinuousSMul R M] (B : Module.Basis ι R M)

-- Note that Finsupp has no topology so we need the coercion, see
-- https://leanprover.zulipchat.com/#narrow/channel/217875-Is-there-code-for-X.3F/topic/TVS.20and.20NormedSpace.20on.20Finsupp.2C.20DFinsupp.2C.20DirectSum.2C.20.2E.2E/near/512890984
/--
theorem `continuous_coe_repr` / 定理 `continuous_coe_repr`

English:
theorem continuous_coe_repr
  statement: Continuous (fun m : M => ⇑(B.repr m))
  proof: have := Finite.of_basis B
  LinearMap.continuous_of_finiteDimensional B.equivFun.toLinearMap

中文:
定理 continuous_coe_repr
  结论: 连续 (fun m : M => ⇑(B.repr m))
  证明: have := Finite.of_basis B
  LinearMap.continuous_of_finiteDimensional B.equivFun.toLinearMap

Depends on / 依赖: B.equivFun.toLinearMap, Finite, Finite.of_basis, LinearMap, LinearMap.continuous_of_finiteDimensional, continuous_of_finiteDimensional, equivFun, of_basis, toLinearMap
-/
theorem continuous_coe_repr : Continuous (fun m : M => ⇑(B.repr m)) :=
  have := Finite.of_basis B
  LinearMap.continuous_of_finiteDimensional B.equivFun.toLinearMap

-- Note: this could be generalized if we had some typeclass to indicate "each of the projections
-- into the basis is continuous".
/--
theorem `continuous_toMatrix` / 定理 `continuous_toMatrix`

English:
theorem continuous_toMatrix
  statement: Continuous fun (v : ι -> M) => B.toMatrix v
  proof: let _ := Fintype.ofFinite ι
  have := Finite.of_basis B
  LinearMap.continuous_of_finiteDimensional B.toMatrixEquiv.toLinearMap

中文:
定理 continuous_toMatrix
  结论: 连续 fun (v : ι -> M) => B.toMatrix v
  证明: let _ := Fintype.ofFinite ι
  have := Finite.of_basis B
  LinearMap.continuous_of_finiteDimensional B.toMatrixEquiv.toLinearMap

Depends on / 依赖: B.toMatrixEquiv.toLinearMap, Finite, Finite.of_basis, Fintype, Fintype.ofFinite, LinearMap, LinearMap.continuous_of_finiteDimensional, continuous_of_finiteDimensional, ofFinite, of_basis, toLinearMap, toMatrixEquiv
-/
theorem continuous_toMatrix : Continuous fun (v : ι -> M) => B.toMatrix v :=
  let _ := Fintype.ofFinite ι
  have := Finite.of_basis B
  LinearMap.continuous_of_finiteDimensional B.toMatrixEquiv.toLinearMap

end Module.Basis
