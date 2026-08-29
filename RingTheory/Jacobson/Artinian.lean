/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu, Andrew Yang
-/
module

public import Mathlib.RingTheory.HopkinsLevitzki
public import Mathlib.RingTheory.Jacobson.Ring

/-!
# Artinian rings over Jacobson rings

## Main results
- `Module.finite_iff_isArtinianRing`: If `A` is a finite type algebra over an Artinian ring `R`,
  then `A` is finite over `R` if and only if `A` is an Artinian ring.

-/

public section

variable (R A : Type*) [CommRing R] [CommRing A] [Algebra R A] [Algebra.FiniteType R A]

attribute [local instance] IsArtinianRing.fieldOfSubtypeIsMaximal in
/--
lemma `Module.finite_of_isSemisimpleRing` / 引理 `Module.finite_of_isSemisimpleRing`

English:
lemma Module.finite_of_isSemisimpleRing
  given: [IsJacobsonRing R] [IsSemisimpleRing A]
  proof: have (I : MaximalSpectrum A) := finite_of_finite_type_of_isJacobsonRing R (A ⧸ I.asIdeal)
  .equiv ((IsArtinianRing.equivPi A).restrictScalars R).toLinearEquiv.symm

中文:
引理 Module.finite_of_isSemisimpleRing
  条件: [IsJacobsonRing R] [IsSemisimpleRing A]
  证明: have (I : MaximalSpectrum A) := finite_of_finite_type_of_isJacobsonRing R (A ⧸ I.asIdeal)
  .equiv ((IsArtinianRing.equivPi A).restrictScalars R).toLinearEquiv.symm

Depends on / 依赖: I.asIdeal, IsArtinianRing, IsArtinianRing.equivPi, MaximalSpectrum, asIdeal, equivPi, finite_of_finite_type_of_isJacobsonRing, restrictScalars, toLinearEquiv, toLinearEquiv.symm
-/
lemma Module.finite_of_isSemisimpleRing [IsJacobsonRing R] [IsSemisimpleRing A] :
    Module.Finite R A :=
  have (I : MaximalSpectrum A) := finite_of_finite_type_of_isJacobsonRing R (A ⧸ I.asIdeal)
  .equiv ((IsArtinianRing.equivPi A).restrictScalars R).toLinearEquiv.symm

/-- If `A` is a finite type algebra over `R`, then `A` is an Artinian ring and `R` is Jacobson
implies `A` is finite over `R`. -/
/--
lemma `Module.finite_of_isArtinianRing` / 引理 `Module.finite_of_isArtinianRing`

English:
lemma Module.finite_of_isArtinianRing
  given: [IsJacobsonRing R] [IsArtinianRing A]
  proof: have := finite_of_isSemisimpleRing R (A ⧸ Ring.jacobson A)
  IsSemiprimaryRing.finite_of_isArtinian R A A

中文:
引理 Module.finite_of_isArtinianRing
  条件: [IsJacobsonRing R] [IsArtinianRing A]
  证明: have := finite_of_isSemisimpleRing R (A ⧸ Ring.jacobson A)
  IsSemiprimaryRing.finite_of_isArtinian R A A

Depends on / 依赖: IsSemiprimaryRing, IsSemiprimaryRing.finite_of_isArtinian, Ring.jacobson, finite_of_isArtinian, finite_of_isSemisimpleRing, jacobson
-/
lemma Module.finite_of_isArtinianRing [IsJacobsonRing R] [IsArtinianRing A] :
    Module.Finite R A :=
  have := finite_of_isSemisimpleRing R (A ⧸ Ring.jacobson A)
  IsSemiprimaryRing.finite_of_isArtinian R A A

/--
lemma `Module.finite_iff_isArtinianRing` / 引理 `Module.finite_iff_isArtinianRing`

English:
lemma Module.finite_iff_isArtinianRing
  given: [IsArtinianRing R]
  proof: ⟨isArtinian_of_tower _ ∘ ((IsArtinianRing.tfae R A).out 0 2).mp,
    fun _ => finite_of_isArtinianRing R A⟩

中文:
引理 Module.finite_iff_isArtinianRing
  条件: [IsArtinianRing R]
  证明: ⟨isArtinian_of_tower _ ∘ ((IsArtinianRing.tfae R A).out 0 2).mp,
    fun _ => finite_of_isArtinianRing R A⟩

Depends on / 依赖: IsArtinianRing, IsArtinianRing.tfae, finite_of_isArtinianRing, isArtinian_of_tower
-/
lemma Module.finite_iff_isArtinianRing [IsArtinianRing R] :
    Module.Finite R A ↔ IsArtinianRing A :=
  ⟨isArtinian_of_tower _ ∘ ((IsArtinianRing.tfae R A).out 0 2).mp,
    fun _ => finite_of_isArtinianRing R A⟩

/--
lemma `Module.finite_iff_krullDimLE_zero` / 引理 `Module.finite_iff_krullDimLE_zero`

English:
lemma Module.finite_iff_krullDimLE_zero
  given: [IsArtinianRing R]
  proof: by
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing R A
  rw [finite_iff_isArtinianRing]; rw [isArtinianRing_iff_isNoetherianRing_krullDimLE_zero]; rw [and_iff_right this]

中文:
引理 Module.finite_iff_krullDimLE_zero
  条件: [IsArtinianRing R]
  证明: by
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing R A
  rw [finite_iff_isArtinianRing]; rw [isArtinianRing_iff_isNoetherianRing_krullDimLE_zero]; rw [and_iff_right this]

Depends on / 依赖: Algebra, Algebra.FiniteType.isNoetherianRing, FiniteType, IsNoetherianRing, and_iff_right, finite_iff_isArtinianRing, isArtinianRing_iff_isNoetherianRing_krullDimLE_zero, isNoetherianRing
-/
lemma Module.finite_iff_krullDimLE_zero [IsArtinianRing R] :
    Module.Finite R A ↔ Ring.KrullDimLE 0 A := by
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing R A
  rw [finite_iff_isArtinianRing]; rw [isArtinianRing_iff_isNoetherianRing_krullDimLE_zero]; rw [and_iff_right this]
