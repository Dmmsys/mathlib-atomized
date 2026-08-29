/-
Copyright (c) 2023 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
module

public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.Localization.NormTrace

/-!
# Number field discriminant

This file defines the discriminant of a number field.

## Main definitions

* `NumberField.discr`: the absolute discriminant of a number field.

## Tags
number field, discriminant
-/

public section

open Module

-- TODO: Rewrite some of the FLT results on the discriminant using the definitions and results of
-- this file

namespace NumberField

variable (K : Type*) [Field K] [NumberField K]

/--
Definition of `discr` / `discr` 的定义

English:
abbreviation discr
  signature: : Int
  body: Algebra.discr Int (RingOfIntegers.basis K)

中文:
缩写 discr
  签名: : 整数
  定义体: Algebra.discr Int (RingOfIntegers.basis K)

Depends on / 依赖: Algebra, Algebra.discr, RingOfIntegers, RingOfIntegers.basis
-/
noncomputable abbrev discr : Int := Algebra.discr Int (RingOfIntegers.basis K)

/--
theorem `coe_discr` / 定理 `coe_discr`

English:
theorem coe_discr
  statement: (discr K : Rat) = Algebra.discr Rat (integralBasis K)
  proof: (Algebra.discr_localizationLocalization Int _ K (RingOfIntegers.basis K)).symm

中文:
定理 coe_discr
  结论: (discr K : Rat) = Algebra.discr Rat (integralBasis K)
  证明: (Algebra.discr_localizationLocalization Int _ K (RingOfIntegers.basis K)).symm

Depends on / 依赖: Algebra, Algebra.discr_localizationLocalization, RingOfIntegers, RingOfIntegers.basis, discr_localizationLocalization
-/
theorem coe_discr : (discr K : Rat) = Algebra.discr Rat (integralBasis K) :=
  (Algebra.discr_localizationLocalization Int _ K (RingOfIntegers.basis K)).symm

/--
theorem `discr_ne_zero` / 定理 `discr_ne_zero`

English:
theorem discr_ne_zero
  statement: discr K != 0
  proof: by
  rw [← (Int.cast_injective (α := Rat)).ne_iff]; rw [coe_discr]
  exact Algebra.discr_not_zero_of_basis Rat (integralBasis K)

中文:
定理 discr_ne_zero
  结论: discr K != 0
  证明: by
  rw [← (Int.cast_injective (α := Rat)).ne_iff]; rw [coe_discr]
  exact Algebra.discr_not_zero_of_basis Rat (integralBasis K)

Depends on / 依赖: Algebra, Algebra.discr_not_zero_of_basis, Int.cast_injective, cast_injective, coe_discr, discr_not_zero_of_basis, integralBasis, ne_iff
-/
theorem discr_ne_zero : discr K != 0 := by
  rw [← (Int.cast_injective (α := Rat)).ne_iff]; rw [coe_discr]
  exact Algebra.discr_not_zero_of_basis Rat (integralBasis K)

/--
theorem `discr_eq_discr` / 定理 `discr_eq_discr`

English:
theorem discr_eq_discr
  given: {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι Int (𝓞 K))
  proof: by
  let b₀ := Basis.reindex (RingOfIntegers.basis K) (Basis.indexEquiv (RingOfIntegers.basis K) b)
  rw [Algebra.discr_eq_discr (𝓞 K) b b₀]; rw [Basis.coe_reindex]; rw [Algebra.discr_reindex]

中文:
定理 discr_eq_discr
  条件: {ι : 类型} [Fintype ι] [DecidableEq ι] (b : Basis ι 整数 (𝓞 K))
  证明: by
  let b₀ := Basis.reindex (RingOfIntegers.basis K) (Basis.indexEquiv (RingOfIntegers.basis K) b)
  rw [Algebra.discr_eq_discr (𝓞 K) b b₀]; rw [Basis.coe_reindex]; rw [Algebra.discr_reindex]

Depends on / 依赖: Algebra, Algebra.discr_eq_discr, Algebra.discr_reindex, Basis.coe_reindex, Basis.indexEquiv, Basis.reindex, RingOfIntegers, RingOfIntegers.basis, coe_reindex, discr_eq_discr, discr_reindex, indexEquiv, reindex
-/
theorem discr_eq_discr {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι Int (𝓞 K)) :
    Algebra.discr Int b = discr K := by
  let b₀ := Basis.reindex (RingOfIntegers.basis K) (Basis.indexEquiv (RingOfIntegers.basis K) b)
  rw [Algebra.discr_eq_discr (𝓞 K) b b₀]; rw [Basis.coe_reindex]; rw [Algebra.discr_reindex]

/--
theorem `discr_eq_discr_of_algEquiv` / 定理 `discr_eq_discr_of_algEquiv`

English:
theorem discr_eq_discr_of_algEquiv
  given: {L : Type*} [Field L] [NumberField L] (f : K ≃ₐ[Rat] L)
  proof: by
  let f₀ : 𝓞 K ≃ₗ[Int] 𝓞 L := (f.restrictScalars Int).mapIntegralClosure.toLinearEquiv
  rw [← Rat.intCast_inj]; rw [coe_discr]; rw [Algebra.discr_eq_discr_of_algEquiv (integralBasis K) f]; rw [← discr_eq_discr L ((RingOfIntegers.basis K).map f₀)]
  change _ = algebraMap Int Rat _
  rw [← Algebra

中文:
定理 discr_eq_discr_of_algEquiv
  条件: {L : 类型} [Field L] [NumberField L] (f : K ≃ₐ[Rat] L)
  证明: by
  let f₀ : 𝓞 K ≃ₗ[Int] 𝓞 L := (f.restrictScalars Int).mapIntegralClosure.toLinearEquiv
  rw [← Rat.intCast_inj]; rw [coe_discr]; rw [Algebra.discr_eq_discr_of_algEquiv (integralBasis K) f]; rw [← discr_eq_discr L ((RingOfIntegers.basis K).map f₀)]
  change _ = algebraMap Int Rat _
  rw [← Algebra

Depends on / 依赖: Algebra, Algebra.discr_eq_discr_of_algEquiv, Algebra.discr_localizationLocalization, Basis.localizationLocalization_apply, Basis.map_apply, Function, Function.comp_apply, Rat.intCast_inj, RingOfIntegers, RingOfIntegers.basis, algebraMap, coe_discr, comp_apply, discr_eq_discr, discr_eq_discr_of_algEquiv, discr_localizationLocalization, f.restrictScalars, intCast_inj, integralBasis, integralBasis_apply
-/
theorem discr_eq_discr_of_algEquiv {L : Type*} [Field L] [NumberField L] (f : K ≃ₐ[Rat] L) :
    discr K = discr L := by
  let f₀ : 𝓞 K ≃ₗ[Int] 𝓞 L := (f.restrictScalars Int).mapIntegralClosure.toLinearEquiv
  rw [← Rat.intCast_inj]; rw [coe_discr]; rw [Algebra.discr_eq_discr_of_algEquiv (integralBasis K) f]; rw [← discr_eq_discr L ((RingOfIntegers.basis K).map f₀)]
  change _ = algebraMap Int Rat _
  rw [← Algebra.discr_localizationLocalization Int (nonZeroDivisors Int) L]
  congr 1
  ext
  simp only [Function.comp_apply, integralBasis_apply, Basis.localizationLocalization_apply,
    Basis.map_apply]
  rfl

/--
theorem `discr_eq_discr_of_ringEquiv` / 定理 `discr_eq_discr_of_ringEquiv`

English:
theorem discr_eq_discr_of_ringEquiv
  given: {L : Type*} [Field L] [NumberField L] (f : K ≃+* L)
  proof: discr_eq_discr_of_algEquiv _ AlgEquiv.ofRingEquiv (f := f) fun _ => by simp

中文:
定理 discr_eq_discr_of_ringEquiv
  条件: {L : 类型} [Field L] [NumberField L] (f : K ≃+* L)
  证明: discr_eq_discr_of_algEquiv _ AlgEquiv.ofRingEquiv (f := f) fun _ => by simp

Depends on / 依赖: AlgEquiv, AlgEquiv.ofRingEquiv, discr_eq_discr_of_algEquiv, ofRingEquiv
-/
theorem discr_eq_discr_of_ringEquiv {L : Type*} [Field L] [NumberField L] (f : K ≃+* L) :
    discr K = discr L :=
discr_eq_discr_of_algEquiv _ AlgEquiv.ofRingEquiv (f := f) fun _ => by simp

end NumberField

namespace Rat

open NumberField

/-- The absolute discriminant of the number field `ℚ` is 1. -/
@[simp]
/--
theorem `numberField_discr` / 定理 `numberField_discr`

English:
theorem numberField_discr
  statement: discr Rat = 1
  proof: by
  let b : Basis (Fin 1) Int (𝓞 Rat) :=
    Basis.map (Basis.singleton (Fin 1) Int) ringOfIntegersEquiv.toAddEquiv.toIntLinearEquiv.symm
  calc NumberField.discr Rat
    _ = Algebra.discr Int b := by convert! (discr_eq_discr Rat b).symm
    _ = Algebra.trace Int (𝓞 Rat) (b default * b default) := 

中文:
定理 numberField_discr
  结论: discr Rat = 1
  证明: by
  let b : Basis (Fin 1) Int (𝓞 Rat) :=
    Basis.map (Basis.singleton (Fin 1) Int) ringOfIntegersEquiv.toAddEquiv.toIntLinearEquiv.symm
  calc NumberField.discr Rat
    _ = Algebra.discr Int b := by convert! (discr_eq_discr Rat b).symm
    _ = Algebra.trace Int (𝓞 Rat) (b default * b default) := 

Depends on / 依赖: Algebra, Algebra.discr, Algebra.discr_def, Algebra.trace, Algebra.traceForm_apply, Algebra.traceMatrix_apply, Basis.map, Basis.map_apply, Basis.singleton, Matrix, Matrix.det_unique, NumberField, NumberField.discr, RingEquiv, RingEquiv.toAddEquiv_eq_coe, convert, det_unique, discr_def, discr_eq_discr, map_apply
-/
theorem numberField_discr : discr Rat = 1 := by
  let b : Basis (Fin 1) Int (𝓞 Rat) :=
    Basis.map (Basis.singleton (Fin 1) Int) ringOfIntegersEquiv.toAddEquiv.toIntLinearEquiv.symm
  calc NumberField.discr Rat
    _ = Algebra.discr Int b := by convert! (discr_eq_discr Rat b).symm
    _ = Algebra.trace Int (𝓞 Rat) (b default * b default) := by
      rw [Algebra.discr_def]; rw [Matrix.det_unique]; rw [Algebra.traceMatrix_apply]; rw [Algebra.traceForm_apply]
    _ = Algebra.trace Int (𝓞 Rat) 1 := by
      rw [Basis.map_apply]; rw [RingEquiv.toAddEquiv_eq_coe]; rw [← AddEquiv.toIntLinearEquiv_symm]; rw [AddEquiv.coe_toIntLinearEquiv]; rw [Basis.singleton_apply]; rw [show (AddEquiv.symm ↑ringOfIntegersEquiv) (1 : Int) = ringOfIntegersEquiv.symm 1 by rfl]; rw [map_one]; rw [mul_one]
    _ = 1 := by rw [Algebra.trace_eq_matrix_trace b]; simp

alias _root_.NumberField.discr_rat := numberField_discr

end Rat

variable {ι ι'} (K) [Field K] [DecidableEq ι] [DecidableEq ι'] [Fintype ι] [Fintype ι']

/--
theorem `Algebra.discr_eq_discr_of_toMatrix_coeff_isIntegral` / 定理 `Algebra.discr_eq_discr_of_toMatrix_coeff_isIntegral`

English:
theorem Algebra.discr_eq_discr_of_toMatrix_coeff_isIntegral
  statement: [NumberField K]
  proof: by
  replace h' : forall i j, IsIntegral Int (b'.toMatrix (b.reindex (b.indexEquiv b')) i j) := by
    intro i j
    convert! h' i ((b.indexEquiv b').symm j)
    simp [Basis.toMatrix_apply]
  rw [← (b.reindex (b.indexEquiv b')).toMatrix_map_vecMul b']; rw [discr_of_matrix_vecMul]; rw [← one_mul (dis

中文:
定理 Algebra.discr_eq_discr_of_toMatrix_coeff_isIntegral
  结论: [NumberField K]
  证明: by
  replace h' : forall i j, IsIntegral Int (b'.toMatrix (b.reindex (b.indexEquiv b')) i j) := by
    intro i j
    convert! h' i ((b.indexEquiv b').symm j)
    simp [Basis.toMatrix_apply]
  rw [← (b.reindex (b.indexEquiv b')).toMatrix_map_vecMul b']; rw [discr_of_matrix_vecMul]; rw [← one_mul (dis

Depends on / 依赖: Basis.coe_reindex, Basis.toMatrix_apply, IsIntegral, IsIntegral.det, IsIntegrallyClosed, IsIntegrallyClosed.isIntegr, b.indexEquiv, b.reindex, coe_reindex, convert, discr_of_matrix_vecMul, discr_reindex, indexEquiv, isIntegr, one_mul, reindex, replace, toMatrix, toMatrix_apply, toMatrix_map_vecMul
-/
theorem Algebra.discr_eq_discr_of_toMatrix_coeff_isIntegral [NumberField K]
    {b : Basis ι Rat K} {b' : Basis ι' Rat K} (h : forall i j, IsIntegral Int (b.toMatrix b' i j))
    (h' : forall i j, IsIntegral Int (b'.toMatrix b i j)) : discr Rat b = discr Rat b' := by
  replace h' : forall i j, IsIntegral Int (b'.toMatrix (b.reindex (b.indexEquiv b')) i j) := by
    intro i j
    convert! h' i ((b.indexEquiv b').symm j)
    simp [Basis.toMatrix_apply]
  rw [← (b.reindex (b.indexEquiv b')).toMatrix_map_vecMul b']; rw [discr_of_matrix_vecMul]; rw [← one_mul (discr Rat b)]; rw [Basis.coe_reindex]; rw [discr_reindex]
  congr
  have hint : IsIntegral Int ((b.reindex (b.indexEquiv b')).toMatrix b').det :=
    IsIntegral.det fun i j => h _ _
  obtain ⟨r, hr⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint
  have hunit : IsUnit r := by
    have : IsIntegral Int (b'.toMatrix (b.reindex (b.indexEquiv b'))).det :=
      IsIntegral.det fun i j => h' _ _
    obtain ⟨r', hr'⟩ := IsIntegrallyClosed.isIntegral_iff.1 this
    refine isUnit_iff_exists_inv.2 ⟨r', ?_⟩
    suffices algebraMap Int Rat (r * r') = 1 by
      rw [← map_one (algebraMap Int Rat)] at this
      exact (IsFractionRing.injective Int Rat) this
    rw [map_mul]; rw [hr]; rw [hr']; rw [← Matrix.det_mul]; rw [Basis.toMatrix_mul_toMatrix_flip]; rw [Matrix.det_one]
  rw [← map_one (algebraMap Int Rat)]; rw [← hr]
  rcases Int.isUnit_iff.1 hunit with hp | hm
  · simp [hp]
  · simp [hm]
