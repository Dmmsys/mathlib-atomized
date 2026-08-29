/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.LocalRing.Module
public import Mathlib.RingTheory.Smooth.Basic
public import Mathlib.RingTheory.TensorProduct.Free

/-!
# Formally smooth local algebras
-/

public section

open TensorProduct IsLocalRing KaehlerDifferential

variable {R S : Type*} [CommRing R] [CommRing S] [IsLocalRing S] [Algebra R S]

namespace Algebra

/--
theorem `FormallySmooth.iff_injective_lTensor_residueField.` / 定理 `FormallySmooth.iff_injective_lTensor_residueField.`

English:
theorem FormallySmooth.iff_injective_lTensor_residueField.{u}
  proof: by
  have : Module.Finite P.Ring P.Cotangent :=
    have : Module.Finite P.Ring P.ker := .of_fg h'
    .of_surjective _ Extension.Cotangent.mk_surjective
  have : Module.Finite S P.Cotangent := Module.Finite.of_restrictScalars_finite P.Ring _ _
  rw [← IsLocalRing.split_injective_iff_lTensor_residue

中文:
定理 FormallySmooth.iff_injective_lTensor_residueField.{u}
  证明: by
  have : Module.Finite P.Ring P.Cotangent :=
    have : Module.Finite P.Ring P.ker := .of_fg h'
    .of_surjective _ Extension.Cotangent.mk_surjective
  have : Module.Finite S P.Cotangent := Module.Finite.of_restrictScalars_finite P.Ring _ _
  rw [← IsLocalRing.split_injective_iff_lTensor_residue

Depends on / 依赖: Cotangent, Extension, Extension.Cotangent.mk_surjective, Finite, IsLocalRing, IsLocalRing.split_injective_iff_lTensor_residueField_injective, Module, Module.Finite, Module.Finite.of_restrictScalars_finite, P.Cotangent, P.Ring, P.formallySmooth_iff_split_injection, P.ker, formallySmooth_iff_split_injection, mk_surjective, of_fg, of_restrictScalars_finite, of_surjective, split_injective_iff_lTensor_residueField_injective
-/
theorem FormallySmooth.iff_injective_lTensor_residueField.{u}
    (P : Algebra.Extension.{u} R S)
    [FormallySmooth R P.Ring]
    [Module.Free P.Ring Ω[P.Ring⁄R]] [Module.Finite P.Ring Ω[P.Ring⁄R]]
    (h' : P.ker.FG) :
    Algebra.FormallySmooth R S ↔
      Function.Injective (P.cotangentComplex.lTensor (ResidueField S)) := by
  have : Module.Finite P.Ring P.Cotangent :=
    have : Module.Finite P.Ring P.ker := .of_fg h'
    .of_surjective _ Extension.Cotangent.mk_surjective
  have : Module.Finite S P.Cotangent := Module.Finite.of_restrictScalars_finite P.Ring _ _
  rw [← IsLocalRing.split_injective_iff_lTensor_residueField_injective]; rw [P.formallySmooth_iff_split_injection]

/--
theorem `FormallySmooth.iff_injective_cotangentComplexBaseChange_residueField` / 定理 `FormallySmooth.iff_injective_cotangentComplexBaseChange_residueField`

English:
theorem FormallySmooth.iff_injective_cotangentComplexBaseChange_residueField
  proof: by
  let P' : Extension R S := { Ring := P, σ := _, algebraMap_σ := Function.surjInv_eq h₁ }
  rw [Algebra.FormallySmooth.iff_injective_lTensor_residueField P' h₂]
  rw [P'.cotangentComplexBaseChange_eq_lTensor_cotangentComplex (ResidueField S)]
  refine .trans ?_ ((AlgebraTensorModule.cancelBaseCha

中文:
定理 FormallySmooth.iff_injective_cotangentComplexBaseChange_residueField
  证明: by
  let P' : Extension R S := { Ring := P, σ := _, algebraMap_σ := Function.surjInv_eq h₁ }
  rw [Algebra.FormallySmooth.iff_injective_lTensor_residueField P' h₂]
  rw [P'.cotangentComplexBaseChange_eq_lTensor_cotangentComplex (ResidueField S)]
  refine .trans ?_ ((AlgebraTensorModule.cancelBaseCha

Depends on / 依赖: Algebra, Algebra.FormallySmooth.iff_injective_lTensor_residueField, AlgebraTensorModule, AlgebraTensorModule.cancelBaseChange, Extension, FormallySmooth, Function, Function.surjInv_eq, ResidueField, baseChange, cancelBaseChange, comp_injective, cotangentComplexBaseChange_eq_lTensor_cotangentComplex, cotangentEquiv, cotangentEquiv.baseChange, iff_injective_lTensor_residueField, injective_comp, surjInv_eq
-/
theorem FormallySmooth.iff_injective_cotangentComplexBaseChange_residueField
    (P : Type*) [CommRing P] [Algebra R P] [Algebra P S]
    [IsScalarTower R P S] [FormallySmooth R P] [Module.Free P Ω[P⁄R]] [Module.Finite P Ω[P⁄R]]
    (h₁ : Function.Surjective (algebraMap P S)) (h₂ : (RingHom.ker (algebraMap P S)).FG) :
    Algebra.FormallySmooth R S ↔
      Function.Injective (cotangentComplexBaseChange R S P (ResidueField S)) := by
  let P' : Extension R S := { Ring := P, σ := _, algebraMap_σ := Function.surjInv_eq h₁ }
  rw [Algebra.FormallySmooth.iff_injective_lTensor_residueField P' h₂]
  rw [P'.cotangentComplexBaseChange_eq_lTensor_cotangentComplex (ResidueField S)]
  refine .trans ?_ ((AlgebraTensorModule.cancelBaseChange P'.Ring S _ _
    Ω[P'.Ring⁄R]).comp_injective _).symm
  exact (((AlgebraTensorModule.cancelBaseChange P'.Ring S _ _ P'.ker).symm ≪≫ₗ
    P'.cotangentEquiv.baseChange (A := _)).injective_comp _).symm

/--
theorem `FormallySmooth.iff_injective_cotangentComplexBaseChange` / 定理 `FormallySmooth.iff_injective_cotangentComplexBaseChange`

English:
theorem FormallySmooth.iff_injective_cotangentComplexBaseChange
  proof: by
  let f : ResidueField S ->ₐ[S] K := Ideal.Quotient.liftₐ _ (Algebra.ofId _ _) h₃
  let := f.toAlgebra
  have := IsScalarTower.of_algebraMap_eq' f.comp_algebraMap.symm
  have : IsScalarTower P (ResidueField S) K := .to₁₃₄ _ S _ _
  rw [FormallySmooth.iff_injective_cotangentComplexBaseChange_resid

中文:
定理 FormallySmooth.iff_injective_cotangentComplexBaseChange
  证明: by
  let f : ResidueField S ->ₐ[S] K := Ideal.Quotient.liftₐ _ (Algebra.ofId _ _) h₃
  let := f.toAlgebra
  have := IsScalarTower.of_algebraMap_eq' f.comp_algebraMap.symm
  have : IsScalarTower P (ResidueField S) K := .to₁₃₄ _ S _ _
  rw [FormallySmooth.iff_injective_cotangentComplexBaseChange_resid

Depends on / 依赖: Algebra, Algebra.ofId, AlgebraTensorModule, AlgebraTensorModule.cancelBaseChange, FaithfullyFlat, FormallySmooth, FormallySmooth.iff_injective_cotangentComplexBaseChange_residueField, Ideal.Quotient.lift, IsScalarTower, IsScalarTower.of_algebraMap_eq, Module, Module.FaithfullyFlat.lTensor_injective_iff_injective, Quotient, ResidueField, cancelBaseChange, comp_algebraMap, cotangentComplexBaseChange, f.comp_algebraMap.symm, f.toAlgebra, iff_injective_cotangentComplexBaseChange_residueField
-/
theorem FormallySmooth.iff_injective_cotangentComplexBaseChange
    (P K : Type*) [Field K] [CommRing P] [Algebra R P] [Algebra P S]
    [IsScalarTower R P S] [Algebra S K] [Algebra P K] [IsScalarTower P S K]
    [FormallySmooth R P] [Module.Free P Ω[P⁄R]] [Module.Finite P Ω[P⁄R]]
    (h₁ : Function.Surjective (algebraMap P S)) (h₂ : (RingHom.ker (algebraMap P S)).FG)
    (h₃ : maximalIdeal S <= RingHom.ker (algebraMap S K)) :
    Algebra.FormallySmooth R S ↔ Function.Injective (cotangentComplexBaseChange R S P K) := by
  let f : ResidueField S ->ₐ[S] K := Ideal.Quotient.liftₐ _ (Algebra.ofId _ _) h₃
  let := f.toAlgebra
  have := IsScalarTower.of_algebraMap_eq' f.comp_algebraMap.symm
  have : IsScalarTower P (ResidueField S) K := .to₁₃₄ _ S _ _
  rw [FormallySmooth.iff_injective_cotangentComplexBaseChange_residueField P h₁ h₂]; rw [← Module.FaithfullyFlat.lTensor_injective_iff_injective _ K]
  have : (AlgebraTensorModule.cancelBaseChange _ _ _ _ _).toLinearMap ∘ₗ
      (cotangentComplexBaseChange R S P (ResidueField S)).baseChange K ∘ₗ
      (AlgebraTensorModule.cancelBaseChange _ _ _ _ _).symm.toLinearMap =
      (cotangentComplexBaseChange R S P K) := by
    ext
    #adaptation_note /-- Prior to nightly-2026-04-06, this was just `simp`. -/
    simp_rw [AlgebraTensorModule.curry_apply, LinearMap.restrictScalars_comp, curry_apply,
      LinearMap.coe_comp, LinearMap.coe_restrictScalars, LinearEquiv.coe_coe, Function.comp_apply,
      AlgebraTensorModule.cancelBaseChange_symm_tmul, LinearMap.baseChange_tmul,
      cotangentComplexBaseChange_tmul, kerToTensor_apply, one_smul,
      AlgebraTensorModule.cancelBaseChange_tmul]
    simp
  rw [← this]
  refine .trans ?_ ((AlgebraTensorModule.cancelBaseChange _ _ _ _ _).comp_injective _).symm
  exact ((AlgebraTensorModule.cancelBaseChange _ _ _ _ _).symm.injective_comp _).symm

end Algebra
