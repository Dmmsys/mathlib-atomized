/-
Copyright (c) 2018 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Mario Carneiro, Yury Kudryashov, Heather Macbeth
-/
module

public import Mathlib.Analysis.CStarAlgebra.Basic
public import Mathlib.Topology.ContinuousMap.Bounded.Normed
public import Mathlib.Topology.ContinuousMap.Star

/-!
# Star structures on bounded continuous functions

-/

@[expose] public section

noncomputable section

open Topology Bornology NNReal uniformity UniformConvergence RCLike BoundedContinuousFunction

open Set Filter Metric Function

universe u v w

variable {F : Type*} {α : Type u} {β : Type v} {γ : Type w}

namespace BoundedContinuousFunction

/-!
### Star structures

In this section, if `β` is a normed ⋆-group, then so is the space of bounded
continuous functions from `α` to `β`, by using the star operation pointwise.

If `𝕜` is normed field and a ⋆-ring over which `β` is a normed algebra and a
star module, then the space of bounded continuous functions from `α` to `β`
is a star module.

If `β` is a ⋆-ring in addition to being a normed ⋆-group, then `α →ᵇ β`
inherits a ⋆-ring structure.

In summary, if `β` is a C⋆-algebra over `𝕜`, then so is `α →ᵇ β`; note that
completeness is guaranteed when `β` is complete (see
`BoundedContinuousFunction.complete`). -/


section NormedAddCommGroup

variable {𝕜 : Type*} [NormedField 𝕜] [StarRing 𝕜] [TopologicalSpace α] [SeminormedAddCommGroup β]
  [StarAddMonoid β] [NormedStarGroup β]

variable [NormedSpace 𝕜 β] [StarModule 𝕜 β]

/--
Instance `instStarAddMonoid` / 实例 `instStarAddMonoid`

English:
instance instStarAddMonoid
  signature: : StarAddMonoid (α ->ᵇ β) where
  body: f.comp star starNormedAddGroupHom.lipschitz
  star_involutive f := ext fun x => star_star (f x)
  star_add f g := ext fun x => star_add (f x) (g x)

中文:
实例 instStarAddMonoid
  签名: : StarAddMonoid (α ->ᵇ β) where
  定义体: f.comp star starNormedAddGroupHom.lipschitz
  star_involutive f := ext fun x => star_star (f x)
  star_add f g := ext fun x => star_add (f x) (g x)

Depends on / 依赖: f.comp, lipschitz, starNormedAddGroupHom, starNormedAddGroupHom.lipschitz
-/
instance instStarAddMonoid : StarAddMonoid (α ->ᵇ β) where
  star f := f.comp star starNormedAddGroupHom.lipschitz
  star_involutive f := ext fun x => star_star (f x)
  star_add f g := ext fun x => star_add (f x) (g x)

/-- The right-hand side of this equality can be parsed `star ∘ ⇑f` because of the
instance `Pi.instStarForAll`. Upon inspecting the goal, one sees `⊢ ↑(star f) = star ↑f`. -/
@[simp]
/--
theorem `coe_star` / 定理 `coe_star`

English:
theorem coe_star
  given: (f : α ->ᵇ β)
  statement: ⇑(star f) = star (⇑f)
  proof: rfl

@[simp]

中文:
定理 coe_star
  条件: (f : α ->ᵇ β)
  结论: ⇑(star f) = star (⇑f)
  证明: rfl

@[simp]
-/
theorem coe_star (f : α ->ᵇ β) : ⇑(star f) = star (⇑f) := rfl

@[simp]
/--
theorem `star_apply` / 定理 `star_apply`

English:
theorem star_apply
  given: (f : α ->ᵇ β) (x : α)
  statement: star f x = star (f x)
  proof: rfl

中文:
定理 star_apply
  条件: (f : α ->ᵇ β) (x : α)
  结论: star f x = star (f x)
  证明: rfl
-/
theorem star_apply (f : α ->ᵇ β) (x : α) : star f x = star (f x) := rfl

/--
Instance `instNormedStarGroup` / 实例 `instNormedStarGroup`

English:
instance instNormedStarGroup
  signature: : NormedStarGroup (α ->ᵇ β) where
  body: by simp only [norm_eq, star_apply, norm_star, le_of_eq]

中文:
实例 instNormedStarGroup
  签名: : NormedStarGroup (α ->ᵇ β) where
  定义体: by simp only [norm_eq, star_apply, norm_star, le_of_eq]

Depends on / 依赖: le_of_eq, norm_eq, norm_star, star_apply
-/
instance instNormedStarGroup : NormedStarGroup (α ->ᵇ β) where
  norm_star_le f := by simp only [norm_eq, star_apply, norm_star, le_of_eq]

/--
Instance `instStarModule` / 实例 `instStarModule`

English:
instance instStarModule
  signature: : StarModule 𝕜 (α ->ᵇ β) where
  body: ext fun x => star_smul k (f x)

中文:
实例 instStarModule
  签名: : StarModule 𝕜 (α ->ᵇ β) where
  定义体: ext fun x => star_smul k (f x)

Depends on / 依赖: star_smul
-/
instance instStarModule : StarModule 𝕜 (α ->ᵇ β) where
  star_smul k f := ext fun x => star_smul k (f x)

end NormedAddCommGroup

section CStarRing

variable [TopologicalSpace α]
variable [NonUnitalNormedRing β] [StarRing β]

/--
Instance `instStarRing` / 实例 `instStarRing`

English:
instance instStarRing
  signature: [NormedStarGroup β]
  body: instStarAddMonoid
  star_mul f g := ext fun x => star_mul (f x) (g x)

中文:
实例 instStarRing
  签名: [NormedStarGroup β]
  定义体: instStarAddMonoid
  star_mul f g := ext fun x => star_mul (f x) (g x)

Depends on / 依赖: instStarAddMonoid
-/
instance instStarRing [NormedStarGroup β] : StarRing (α ->ᵇ β) where
  __ := instStarAddMonoid
  star_mul f g := ext fun x => star_mul (f x) (g x)

variable [CStarRing β]

/--
Instance `instCStarRing` / 实例 `instCStarRing`

English:
instance instCStarRing
  signature: : CStarRing (α ->ᵇ β) where
  body: by
    rw [← sq]; rw [← Real.le_sqrt (norm_nonneg _) (norm_nonneg _)]; rw [norm_le (Real.sqrt_nonneg _)]
    intro x
    rw [Real.le_sqrt (norm_nonneg _) (norm_nonneg _)]; rw [sq]; rw [← CStarRing.norm_star_mul_self]
    exact norm_coe_le_norm (star f * f) x

中文:
实例 instCStarRing
  签名: : CStarRing (α ->ᵇ β) where
  定义体: by
    rw [← sq]; rw [← Real.le_sqrt (norm_nonneg _) (norm_nonneg _)]; rw [norm_le (Real.sqrt_nonneg _)]
    intro x
    rw [Real.le_sqrt (norm_nonneg _) (norm_nonneg _)]; rw [sq]; rw [← CStarRing.norm_star_mul_self]
    exact norm_coe_le_norm (star f * f) x

Depends on / 依赖: CStarRing, CStarRing.norm_star_mul_self, Real.le_sqrt, Real.sqrt_nonneg, le_sqrt, norm_coe_le_norm, norm_le, norm_nonneg, norm_star_mul_self, sqrt_nonneg
-/
instance instCStarRing : CStarRing (α ->ᵇ β) where
  norm_mul_self_le f := by
    rw [← sq]; rw [← Real.le_sqrt (norm_nonneg _) (norm_nonneg _)]; rw [norm_le (Real.sqrt_nonneg _)]
    intro x
    rw [Real.le_sqrt (norm_nonneg _) (norm_nonneg _)]; rw [sq]; rw [← CStarRing.norm_star_mul_self]
    exact norm_coe_le_norm (star f * f) x

end CStarRing

section NormedAlgebra

variable (𝕜 : Type*) [NormedField 𝕜] [TopologicalSpace α]
  [NormedRing β] [NormedAlgebra 𝕜 β] [StarAddMonoid β] [NormedStarGroup β]

/-- The ⋆-algebra-homomorphism forgetting that a bounded continuous function is bounded. -/
@[simps!]
/--
Definition of `toContinuousMapStarₐ` / `toContinuousMapStarₐ` 的定义

English:
definition toContinuousMapStarₐ
  signature: : (α ->ᵇ β) ->⋆ₐ[𝕜] C(α, β)
  body: { toContinuousMapₐ 𝕜 with
  map_star' _ := rfl }

@[simp]

中文:
定义 toContinuousMapStarₐ
  签名: : (α ->ᵇ β) ->⋆ₐ[𝕜] C(α, β)
  定义体: { toContinuousMapₐ 𝕜 with
  map_star' _ := rfl }

@[simp]
-/
def toContinuousMapStarₐ : (α ->ᵇ β) ->⋆ₐ[𝕜] C(α, β) := { toContinuousMapₐ 𝕜 with
  map_star' _ := rfl }

@[simp]
/--
theorem `coe_toContinuousMapStarₐ` / 定理 `coe_toContinuousMapStarₐ`

English:
theorem coe_toContinuousMapStarₐ
  given: (f : α ->ᵇ β)
  statement: (f.toContinuousMapStarₐ 𝕜 : α -> β) = f
  proof: rfl

中文:
定理 coe_toContinuousMapStarₐ
  条件: (f : α ->ᵇ β)
  结论: (f.toContinuousMapStarₐ 𝕜 : α -> β) = f
  证明: rfl
-/
theorem coe_toContinuousMapStarₐ (f : α ->ᵇ β) : (f.toContinuousMapStarₐ 𝕜 : α -> β) = f := rfl

end NormedAlgebra

end BoundedContinuousFunction
