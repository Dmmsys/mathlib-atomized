/-
Copyright (c) 2023 Fangming Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fangming Li
-/
module

public import Mathlib.RingTheory.GradedAlgebra.Basic
public import Mathlib.RingTheory.Noetherian.Basic

/-!
# The properties of a graded Noetherian ring.

This file proves that the 0-th grade of a Noetherian ring is
also a Noetherian ring.
-/

public section

variable {ι A σ : Type*}
variable [Ring A] [IsNoetherianRing A]
variable [DecidableEq ι] [AddCommMonoid ι] [PartialOrder ι] [CanonicallyOrderedAdd ι]
variable [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ι -> σ) [GradedRing 𝒜]

namespace GradedRing

/--
Instance `GradeZero.isNoetherianRing` / 实例 `GradeZero.isNoetherianRing`

English:
instance GradeZero.isNoetherianRing
  signature: : IsNoetherianRing (𝒜 0)
  body: isNoetherianRing_of_surjective
    A (𝒜 0) (GradedRing.projZeroRingHom' 𝒜) (GradedRing.projZeroRingHom'_surjective 𝒜)

中文:
实例 GradeZero.isNoetherianRing
  签名: : IsNoetherianRing (𝒜 0)
  定义体: isNoetherianRing_of_surjective
    A (𝒜 0) (GradedRing.projZeroRingHom' 𝒜) (GradedRing.projZeroRingHom'_surjective 𝒜)

Depends on / 依赖: GradedRing, GradedRing.projZeroRingHom, _surjective, isNoetherianRing_of_surjective, projZeroRingHom
-/
instance GradeZero.isNoetherianRing : IsNoetherianRing (𝒜 0) :=
  isNoetherianRing_of_surjective
    A (𝒜 0) (GradedRing.projZeroRingHom' 𝒜) (GradedRing.projZeroRingHom'_surjective 𝒜)

end GradedRing
