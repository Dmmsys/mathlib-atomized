/-
Copyright (c) 2023 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
module

public import Mathlib.Algebra.Module.ZLattice.Covolume
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.ConvexBody
public import Mathlib.NumberTheory.NumberField.Discriminant.Defs
public import Mathlib.NumberTheory.NumberField.EquivReindex
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Number field discriminant

This file defines the discriminant of a number field.

## Main result

* `NumberField.abs_discr_gt_two`: **Hermite-Minkowski Theorem**. A nontrivial number field has
  discriminant greater than `2`.

* `NumberField.finite_of_discr_bdd`: **Hermite Theorem**. Let `N` be an integer. There are only
  finitely many number fields (in some fixed extension of `ℚ`) of discriminant bounded by `N`.

## Tags
number field, discriminant
-/

public section

-- TODO. Rewrite some of the FLT results on the discriminant using the definitions and results of
-- this file

namespace NumberField

open Module NumberField NumberField.InfinitePlace Matrix

open scoped Real nonZeroDivisors

variable (K : Type*) [Field K] [NumberField K]

open MeasureTheory MeasureTheory.Measure ZSpan NumberField.mixedEmbedding
  NumberField.InfinitePlace ENNReal NNReal Complex

/--
theorem `discr_eq_basisMatrix_det_sq` / 定理 `discr_eq_basisMatrix_det_sq`

English:
theorem discr_eq_basisMatrix_det_sq
  given: [DecidableEq (K ->+* Complex)]
  proof: by
  rw [← Rat.cast_intCast]; rw [coe_discr]; rw [basisMatrix_eq_embeddingsMatrixReindex]; rw [← Algebra.discr_eq_det_embeddingsMatrixReindex_pow_two]; rw [← (equivReindex K).symm_symm]; rw [Algebra.discr_reindex]; rw [eq_ratCast]

中文:
定理 discr_eq_basisMatrix_det_sq
  条件: [DecidableEq (K ->+* Complex)]
  证明: by
  rw [← Rat.cast_intCast]; rw [coe_discr]; rw [basisMatrix_eq_embeddingsMatrixReindex]; rw [← Algebra.discr_eq_det_embeddingsMatrixReindex_pow_two]; rw [← (equivReindex K).symm_symm]; rw [Algebra.discr_reindex]; rw [eq_ratCast]

Depends on / 依赖: Algebra, Algebra.discr_eq_det_embeddingsMatrixReindex_pow_two, Algebra.discr_reindex, Rat.cast_intCast, basisMatrix_eq_embeddingsMatrixReindex, cast_intCast, coe_discr, discr_eq_det_embeddingsMatrixReindex_pow_two, discr_reindex, eq_ratCast, equivReindex, symm_symm
-/
theorem discr_eq_basisMatrix_det_sq [DecidableEq (K ->+* Complex)] :
    discr K = (basisMatrix K).det ^ 2 := by
  rw [← Rat.cast_intCast]; rw [coe_discr]; rw [basisMatrix_eq_embeddingsMatrixReindex]; rw [← Algebra.discr_eq_det_embeddingsMatrixReindex_pow_two]; rw [← (equivReindex K).symm_symm]; rw [Algebra.discr_reindex]; rw [eq_ratCast]

set_option backward.isDefEq.respectTransparency false in
open scoped ComplexConjugate ComplexOrder in
/--
theorem `sign_discr` / 定理 `sign_discr`

English:
theorem sign_discr
  proof: by
  classical
  have : 0 <= (discr K : Complex) ↔ Even (nrComplexPlaces K) := by
    rw [discr_eq_basisMatrix_det_sq]; rw [Complex.sq_nonneg_iff]; rw [← conj_eq_iff_im]; rw [RingHom.map_det]; rw [RingHom.mapMatrix_apply]; rw [conj_basisMatrix]; rw [reindex_apply]; rw [Equiv.refl_symm]; rw [Equiv.co

中文:
定理 sign_discr
  证明: by
  classical
  have : 0 <= (discr K : Complex) ↔ Even (nrComplexPlaces K) := by
    rw [discr_eq_basisMatrix_det_sq]; rw [Complex.sq_nonneg_iff]; rw [← conj_eq_iff_im]; rw [RingHom.map_det]; rw [RingHom.mapMatrix_apply]; rw [conj_basisMatrix]; rw [reindex_apply]; rw [Equiv.refl_symm]; rw [Equiv.co

Depends on / 依赖: Complex.sq_nonneg_iff, ComplexEmbedding, ComplexEmbedding.conjugate_sign, Equiv.coe_refl, Equiv.refl_symm, Function, Function.Involutive.toPerm_symm, Int.reduceNeg, Involutive, RingHom, RingHom.mapMatrix_apply, RingHom.map_det, Units.val_neg, Units.val_one, Units.val_pow_eq_pow_val, classical, coe_refl, conj_basisMatrix, conj_eq_iff_im, conjugate_sign
-/
theorem sign_discr :
    (discr K).sign = (-1) ^ nrComplexPlaces K := by
  classical
  have : 0 <= (discr K : Complex) ↔ Even (nrComplexPlaces K) := by
    rw [discr_eq_basisMatrix_det_sq]; rw [Complex.sq_nonneg_iff]; rw [← conj_eq_iff_im]; rw [RingHom.map_det]; rw [RingHom.mapMatrix_apply]; rw [conj_basisMatrix]; rw [reindex_apply]; rw [Equiv.refl_symm]; rw [Equiv.coe_refl]; rw [Function.Involutive.toPerm_symm]; rw [det_permute']; rw [mul_eq_right₀]; rw [ComplexEmbedding.conjugate_sign]
    · simp only [Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one, Int.reduceNeg,
        Int.cast_pow, Int.cast_neg, Int.cast_one]
      rw [neg_one_pow_eq_one_iff_even (by norm_num)]
    · exact det_of_basisMatrix_non_zero K
  obtain h | h | h := Int.lt_trichotomy 0 (discr K)
  · rw [Int.sign_eq_one_of_pos h, Even.neg_one_pow (this.mp <| Int.cast_nonneg h.le)]
  · grind [discr_ne_zero]
  · rw [Int.sign_eq_neg_one_of_neg h, Odd.neg_one_pow]
    rwa [← Nat.not_even_iff_odd, ← this, Int.cast_nonneg_iff, not_le]

section rootDiscr

/--
Definition of `rootDiscr` / `rootDiscr` 的定义

English:
definition rootDiscr
  signature: : Real
  body: |discr K| ^ (finrank Rat K : Real)⁻¹

中文:
定义 rootDiscr
  签名: : 实数
  定义体: |discr K| ^ (finrank Rat K : Real)⁻¹

Depends on / 依赖: finrank
-/
noncomputable def rootDiscr : Real :=
  |discr K| ^ (finrank Rat K : Real)⁻¹

/--
theorem `rootDiscr_def` / 定理 `rootDiscr_def`

English:
theorem rootDiscr_def
  statement: rootDiscr K = |discr K| ^ (finrank Rat K : Real)⁻¹
  proof: by
  rw [rootDiscr]

中文:
定理 rootDiscr_def
  结论: rootDiscr K = |discr K| ^ (finrank Rat K : 实数)⁻¹
  证明: by
  rw [rootDiscr]

Depends on / 依赖: rootDiscr
-/
theorem rootDiscr_def : rootDiscr K = |discr K| ^ (finrank Rat K : Real)⁻¹ := by
  rw [rootDiscr]

/--
theorem `rootDiscr_rat` / 定理 `rootDiscr_rat`

English:
theorem rootDiscr_rat
  statement: rootDiscr Rat = 1
  proof: by
  simp [rootDiscr_def]

中文:
定理 rootDiscr_rat
  结论: rootDiscr Rat = 1
  证明: by
  simp [rootDiscr_def]

Depends on / 依赖: rootDiscr_def
-/
theorem rootDiscr_rat : rootDiscr Rat = 1 := by
  simp [rootDiscr_def]

end rootDiscr

open scoped Classical in
/--
theorem `_root_.NumberField.mixedEmbedding.volume_fundamentalDomain_latticeBasis` / 定理 `_root_.NumberField.mixedEmbedding.volume_fundamentalDomain_latticeBasis`

English:
theorem _root_.NumberField.mixedEmbedding.volume_fundamentalDomain_latticeBasis
  proof: by
  let f : Module.Free.ChooseBasisIndex Int (𝓞 K) ≃ (K ->+* Complex) :=
    (canonicalEmbedding.latticeBasis K).indexEquiv (Pi.basisFun Complex _)
  let e : (index K) ≃ Module.Free.ChooseBasisIndex Int (𝓞 K) := (indexEquiv K).trans f.symm
  let M := (mixedEmbedding.stdBasis K).toMatrix ((latticeBa

中文:
定理 _root_.NumberField.mixedEmbedding.volume_fundamentalDomain_latticeBasis
  证明: by
  let f : Module.Free.ChooseBasisIndex Int (𝓞 K) ≃ (K ->+* Complex) :=
    (canonicalEmbedding.latticeBasis K).indexEquiv (Pi.basisFun Complex _)
  let e : (index K) ≃ Module.Free.ChooseBasisIndex Int (𝓞 K) := (indexEquiv K).trans f.symm
  let M := (mixedEmbedding.stdBasis K).toMatrix ((latticeBa

Depends on / 依赖: Algebra, Algebra.embeddingsMatrixReindex, ChooseBasisIndex, M.map, Matrix, Matrix.reindex, Module, Module.Free.ChooseBasisIndex, Pi.basisFun, RingHom, RingHom.equivRatAlgHom, basisFun, canonicalEmbedding, canonicalEmbedding.latticeBasis, e.symm, embeddingsMatrixReindex, equivRatAlgHom, f.symm, indexEq, indexEquiv
-/
theorem _root_.NumberField.mixedEmbedding.volume_fundamentalDomain_latticeBasis :
    volume (fundamentalDomain (latticeBasis K)) =
      (2 : Real>=0∞)⁻¹ ^ nrComplexPlaces K * sqrt ‖discr K‖₊ := by
  let f : Module.Free.ChooseBasisIndex Int (𝓞 K) ≃ (K ->+* Complex) :=
    (canonicalEmbedding.latticeBasis K).indexEquiv (Pi.basisFun Complex _)
  let e : (index K) ≃ Module.Free.ChooseBasisIndex Int (𝓞 K) := (indexEquiv K).trans f.symm
  let M := (mixedEmbedding.stdBasis K).toMatrix ((latticeBasis K).reindex e.symm)
  let N := Algebra.embeddingsMatrixReindex Rat Complex (integralBasis K ∘ f.symm)
    (RingHom.equivRatAlgHom K Complex)
  suffices M.map ofRealHom = matrixToStdBasis K *
      (Matrix.reindex (indexEquiv K).symm (indexEquiv K).symm N).transpose by
    calc volume (fundamentalDomain (latticeBasis K))
      _ = ‖((mixedEmbedding.stdBasis K).toMatrix ((latticeBasis K).reindex e.symm)).det‖₊ := by
        rw [← fundamentalDomain_reindex _ e.symm]; rw [← norm_toNNReal]; rw [measure_fundamentalDomain
          ((latticeBasis K).reindex e.symm)]; rw [volume_fundamentalDomain_stdBasis]; rw [mul_one]
        rfl
      _ = ‖(matrixToStdBasis K).det * N.det‖₊ := by
        rw [← nnnorm_real]; rw [← ofRealHom_eq_coe]; rw [RingHom.map_det]; rw [RingHom.mapMatrix_apply]; rw [this]; rw [det_mul]; rw [det_transpose]; rw [det_reindex_self]
      _ = (2 : Real>=0∞)⁻¹ ^ Fintype.card {w : InfinitePlace K // IsComplex w} * sqrt ‖N.det ^ 2‖₊ := by
        have : ‖Complex.I‖₊ = 1 := by rw [← norm_toNNReal, norm_I, Real.toNNReal_one]
        rw [det_matrixToStdBasis]; rw [nnnorm_mul]; rw [nnnorm_pow]; rw [nnnorm_mul]; rw [this]; rw [mul_one]; rw [nnnorm_inv]; rw [coe_mul]; rw [ENNReal.coe_pow]; rw [← norm_toNNReal]; rw [RCLike.norm_two]; rw [Real.toNNReal_ofNat]; rw [coe_inv two_ne_zero]; rw [coe_ofNat]; rw [nnnorm_pow]; rw [NNReal.sqrt_sq]
      _ = (2 : Real>=0∞)⁻¹ ^ Fintype.card { w // IsComplex w } * NNReal.sqrt ‖discr K‖₊ := by
        rw [← Algebra.discr_eq_det_embeddingsMatrixReindex_pow_two]; rw [Algebra.discr_reindex]; rw [← coe_discr]; rw [map_intCast]; rw [← Complex.nnnorm_intCast]
  ext : 2
  dsimp only [M]
  rw [Matrix.map_apply]; rw [Basis.toMatrix_apply]; rw [Basis.coe_reindex]; rw [Function.comp_apply]; rw [Equiv.symm_symm]; rw [latticeBasis_apply]; rw [← commMap_canonical_eq_mixed]; rw [Complex.ofRealHom_eq_coe]; rw [stdBasis_repr_eq_matrixToStdBasis_mul K _ (fun _ => rfl)]
  rfl

open scoped Classical in
/--
theorem `_root_.NumberField.mixedEmbedding.covolume_integerLattice` / 定理 `_root_.NumberField.mixedEmbedding.covolume_integerLattice`

English:
theorem _root_.NumberField.mixedEmbedding.covolume_integerLattice
  proof: by
  rw [ZLattice.covolume_eq_measure_fundamentalDomain _ _ (fundamentalDomain_integerLattice K)]; rw [measureReal_def]; rw [volume_fundamentalDomain_latticeBasis]; rw [ENNReal.toReal_mul]; rw [ENNReal.toReal_pow]; rw [ENNReal.toReal_inv]; rw [toReal_ofNat]; rw [ENNReal.coe_toReal]; rw [Real.coe_sqr

中文:
定理 _root_.NumberField.mixedEmbedding.covolume_integerLattice
  证明: by
  rw [ZLattice.covolume_eq_measure_fundamentalDomain _ _ (fundamentalDomain_integerLattice K)]; rw [measureReal_def]; rw [volume_fundamentalDomain_latticeBasis]; rw [ENNReal.toReal_mul]; rw [ENNReal.toReal_pow]; rw [ENNReal.toReal_inv]; rw [toReal_ofNat]; rw [ENNReal.coe_toReal]; rw [Real.coe_sqr

Depends on / 依赖: ENNReal, ENNReal.coe_toReal, ENNReal.toReal_inv, ENNReal.toReal_mul, ENNReal.toReal_pow, Int.norm_eq_abs, Real.coe_sqrt, ZLattice, ZLattice.covolume_eq_measure_fundamentalDomain, coe_nnnorm, coe_sqrt, coe_toReal, covolume_eq_measure_fundamentalDomain, fundamentalDomain_integerLattice, measureReal_def, norm_eq_abs, toReal_inv, toReal_mul, toReal_ofNat, toReal_pow
-/
theorem _root_.NumberField.mixedEmbedding.covolume_integerLattice :
    ZLattice.covolume (mixedEmbedding.integerLattice K) =
      (2⁻¹) ^ nrComplexPlaces K * √|discr K| := by
  rw [ZLattice.covolume_eq_measure_fundamentalDomain _ _ (fundamentalDomain_integerLattice K)]; rw [measureReal_def]; rw [volume_fundamentalDomain_latticeBasis]; rw [ENNReal.toReal_mul]; rw [ENNReal.toReal_pow]; rw [ENNReal.toReal_inv]; rw [toReal_ofNat]; rw [ENNReal.coe_toReal]; rw [Real.coe_sqrt]; rw [coe_nnnorm]; rw [Int.norm_eq_abs]

open scoped Classical in
/--
theorem `_root_.NumberField.mixedEmbedding.covolume_idealLattice` / 定理 `_root_.NumberField.mixedEmbedding.covolume_idealLattice`

English:
theorem _root_.NumberField.mixedEmbedding.covolume_idealLattice
  given: (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
  proof: by
  rw [ZLattice.covolume_eq_measure_fundamentalDomain _ _ (fundamentalDomain_idealLattice K I)]; rw [measureReal_def]; rw [volume_fundamentalDomain_fractionalIdealLatticeBasis]; rw [volume_fundamentalDomain_latticeBasis]; rw [ENNReal.toReal_mul]; rw [ENNReal.toReal_mul]; rw [ENNReal.toReal_pow]; r

中文:
定理 _root_.NumberField.mixedEmbedding.covolume_idealLattice
  条件: (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
  证明: by
  rw [ZLattice.covolume_eq_measure_fundamentalDomain _ _ (fundamentalDomain_idealLattice K I)]; rw [measureReal_def]; rw [volume_fundamentalDomain_fractionalIdealLatticeBasis]; rw [volume_fundamentalDomain_latticeBasis]; rw [ENNReal.toReal_mul]; rw [ENNReal.toReal_mul]; rw [ENNReal.toReal_pow]; r

Depends on / 依赖: ENNReal, ENNReal.coe_toReal, ENNReal.toReal_inv, ENNReal.toReal_mul, ENNReal.toReal_ofReal, ENNReal.toReal_pow, FractionalIdeal, FractionalIdeal.absNorm_non, Int.norm_eq_abs, Rat.cast_nonneg.mpr, Real.coe_sqrt, ZLattice, ZLattice.covolume_eq_measure_fundamentalDomain, absNorm_non, cast_nonneg, coe_nnnorm, coe_sqrt, coe_toReal, covolume_eq_measure_fundamentalDomain, fundamentalDomain_idealLattice
-/
theorem _root_.NumberField.mixedEmbedding.covolume_idealLattice (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    ZLattice.covolume (mixedEmbedding.idealLattice K I) =
      (FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K)) *
        (2⁻¹) ^ nrComplexPlaces K * √|discr K| := by
  rw [ZLattice.covolume_eq_measure_fundamentalDomain _ _ (fundamentalDomain_idealLattice K I)]; rw [measureReal_def]; rw [volume_fundamentalDomain_fractionalIdealLatticeBasis]; rw [volume_fundamentalDomain_latticeBasis]; rw [ENNReal.toReal_mul]; rw [ENNReal.toReal_mul]; rw [ENNReal.toReal_pow]; rw [ENNReal.toReal_inv]; rw [toReal_ofNat]; rw [ENNReal.coe_toReal]; rw [Real.coe_sqrt]; rw [coe_nnnorm]; rw [Int.norm_eq_abs]; rw [ENNReal.toReal_ofReal (Rat.cast_nonneg.mpr (FractionalIdeal.absNorm_nonneg I.val))]; rw [mul_assoc]

/--
theorem `exists_ne_zero_mem_ideal_of_norm_le_mul_sqrt_discr` / 定理 `exists_ne_zero_mem_ideal_of_norm_le_mul_sqrt_discr`

English:
theorem exists_ne_zero_mem_ideal_of_norm_le_mul_sqrt_discr
  given: (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
  proof: by
  classical
  -- The smallest possible value for `exists_ne_zero_mem_ideal_of_norm_le`
  let B := (minkowskiBound K I * (convexBodySumFactor K)⁻¹).toReal ^ (1 / (finrank Rat K : Real))
  have h_le : (minkowskiBound K I) <= volume (convexBodySum K B) := by
    refine le_of_eq ?_
    rw [convexBody

中文:
定理 exists_ne_zero_mem_ideal_of_norm_le_mul_sqrt_discr
  条件: (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
  证明: by
  classical
  -- The smallest possible value for `exists_ne_zero_mem_ideal_of_norm_le`
  let B := (minkowskiBound K I * (convexBodySumFactor K)⁻¹).toReal ^ (1 / (finrank Rat K : Real))
  have h_le : (minkowskiBound K I) <= volume (convexBodySum K B) := by
    refine le_of_eq ?_
    rw [convexBody

Depends on / 依赖: classical
-/
theorem exists_ne_zero_mem_ideal_of_norm_le_mul_sqrt_discr (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    exists a in (I : FractionalIdeal (𝓞 K)⁰ K), a != 0 ∧
      |Algebra.norm Rat (a : K)| <= FractionalIdeal.absNorm I.1 * (4 / π) ^ nrComplexPlaces K *
        (finrank Rat K).factorial / (finrank Rat K) ^ (finrank Rat K) * Real.sqrt |discr K| := by
  classical
  -- The smallest possible value for `exists_ne_zero_mem_ideal_of_norm_le`
  let B := (minkowskiBound K I * (convexBodySumFactor K)⁻¹).toReal ^ (1 / (finrank Rat K : Real))
  have h_le : (minkowskiBound K I) <= volume (convexBodySum K B) := by
    refine le_of_eq ?_
    rw [convexBodySum_volume]; rw [← ENNReal.ofReal_pow (by positivity)]; rw [← Real.rpow_natCast]; rw [← Real.rpow_mul toReal_nonneg]; rw [div_mul_cancel₀]; rw [Real.rpow_one]; rw [ofReal_toReal]; rw [mul_comm]; rw [mul_assoc]; rw [← coe_mul]; rw [inv_mul_cancel₀ (convexBodySumFactor_ne_zero K)]; rw [ENNReal.coe_one]; rw [mul_one]
    · exact mul_ne_top (ne_of_lt (minkowskiBound_lt_top K I)) coe_ne_top
    · exact (Nat.cast_ne_zero.mpr (ne_of_gt finrank_pos))
  convert! exists_ne_zero_mem_ideal_of_norm_le K I h_le
  rw [div_pow B]; rw [← Real.rpow_natCast B]; rw [← Real.rpow_mul (by positivity)]; rw [div_mul_cancel₀ _
    (Nat.cast_ne_zero.mpr <| ne_of_gt finrank_pos)]; rw [Real.rpow_one]; rw [mul_comm_div]; rw [mul_div_assoc']
  congr 1
  rw [eq_comm]
  calc
    _ = FractionalIdeal.absNorm I.1 * (2 : Real)⁻¹ ^ nrComplexPlaces K * sqrt ‖discr K‖₊ *
          (2 : Real) ^ finrank Rat K * ((2 : Real) ^ nrRealPlaces K * (π / 2) ^ nrComplexPlaces K /
            (Nat.factorial (finrank Rat K)))⁻¹ := by
      simp_rw [minkowskiBound, convexBodySumFactor,
        volume_fundamentalDomain_fractionalIdealLatticeBasis,
        volume_fundamentalDomain_latticeBasis, toReal_mul, toReal_pow, toReal_inv, coe_toReal,
        toReal_ofNat, mixedEmbedding.finrank, mul_assoc]
      rw [ENNReal.toReal_ofReal (Rat.cast_nonneg.mpr (FractionalIdeal.absNorm_nonneg I.1))]
      simp_rw [NNReal.coe_inv, NNReal.coe_div, NNReal.coe_mul, NNReal.coe_pow, NNReal.coe_div,
        coe_real_pi, NNReal.coe_ofNat, NNReal.coe_natCast]
    _ = FractionalIdeal.absNorm I.1 * (2 : Real) ^ (finrank Rat K - nrComplexPlaces K - nrRealPlaces K +
          nrComplexPlaces K : Int) * Real.sqrt ‖discr K‖ * Nat.factorial (finrank Rat K) *
            π⁻¹ ^ (nrComplexPlaces K) := by
      simp_rw [inv_div, div_eq_mul_inv, mul_inv, ← zpow_neg_one, ← zpow_natCast, mul_zpow,
        ← zpow_mul, neg_one_mul, mul_neg_one, neg_neg, Real.coe_sqrt, coe_nnnorm, sub_eq_add_neg,
        zpow_add₀ (two_ne_zero : (2 : Real) != 0)]
      ring
    _ = FractionalIdeal.absNorm I.1 * (2 : Real) ^ (2 * nrComplexPlaces K : Int) * Real.sqrt ‖discr K‖ *
          Nat.factorial (finrank Rat K) * π⁻¹ ^ (nrComplexPlaces K) := by
      congr
      rw [← card_add_two_mul_card_eq_rank]; rw [Nat.cast_add]; rw [Nat.cast_mul]; rw [Nat.cast_ofNat]
      ring
    _ = FractionalIdeal.absNorm I.1 * (4 / π) ^ nrComplexPlaces K * (finrank Rat K).factorial *
          Real.sqrt |discr K| := by
      rw [Int.norm_eq_abs]; rw [zpow_mul]; rw [show (2 : Real) ^ (2 : Int) = 4 by norm_cast]; rw [div_pow]; rw [inv_eq_one_div]; rw [div_pow]; rw [one_pow]; rw [zpow_natCast]
      ring

/--
theorem `exists_ne_zero_mem_ringOfIntegers_of_norm_le_mul_sqrt_discr` / 定理 `exists_ne_zero_mem_ringOfIntegers_of_norm_le_mul_sqrt_discr`

English:
theorem exists_ne_zero_mem_ringOfIntegers_of_norm_le_mul_sqrt_discr
  proof: by
  obtain ⟨_, h_mem, h_nz, h_nm⟩ := exists_ne_zero_mem_ideal_of_norm_le_mul_sqrt_discr K ↑1
  obtain ⟨a, rfl⟩ := (FractionalIdeal.mem_one_iff _).mp h_mem
  refine ⟨a, ne_zero_of_map h_nz, ?_⟩
  simp_rw [Units.val_one, FractionalIdeal.absNorm_one, Rat.cast_one, one_mul] at h_nm
  exact h_nm

中文:
定理 exists_ne_zero_mem_ringOfIntegers_of_norm_le_mul_sqrt_discr
  证明: by
  obtain ⟨_, h_mem, h_nz, h_nm⟩ := exists_ne_zero_mem_ideal_of_norm_le_mul_sqrt_discr K ↑1
  obtain ⟨a, rfl⟩ := (FractionalIdeal.mem_one_iff _).mp h_mem
  refine ⟨a, ne_zero_of_map h_nz, ?_⟩
  simp_rw [Units.val_one, FractionalIdeal.absNorm_one, Rat.cast_one, one_mul] at h_nm
  exact h_nm

Depends on / 依赖: FractionalIdeal, FractionalIdeal.absNorm_one, FractionalIdeal.mem_one_iff, Rat.cast_one, Units.val_one, absNorm_one, cast_one, exists_ne_zero_mem_ideal_of_norm_le_mul_sqrt_discr, h_mem, h_nm, h_nz, mem_one_iff, ne_zero_of_map, one_mul, simp_rw, val_one
-/
theorem exists_ne_zero_mem_ringOfIntegers_of_norm_le_mul_sqrt_discr :
    exists (a : 𝓞 K), a != 0 ∧
      |Algebra.norm Rat (a : K)| <= (4 / π) ^ nrComplexPlaces K *
        (finrank Rat K).factorial / (finrank Rat K) ^ (finrank Rat K) * Real.sqrt |discr K| := by
  obtain ⟨_, h_mem, h_nz, h_nm⟩ := exists_ne_zero_mem_ideal_of_norm_le_mul_sqrt_discr K ↑1
  obtain ⟨a, rfl⟩ := (FractionalIdeal.mem_one_iff _).mp h_mem
  refine ⟨a, ne_zero_of_map h_nz, ?_⟩
  simp_rw [Units.val_one, FractionalIdeal.absNorm_one, Rat.cast_one, one_mul] at h_nm
  exact h_nm

/--
theorem `abs_discr_ge'` / 定理 `abs_discr_ge'`

English:
theorem abs_discr_ge'
  proof: by
  -- We use `exists_ne_zero_mem_ringOfIntegers_of_norm_le_mul_sqrt_discr` to get a nonzero
  -- algebraic integer `x` of small norm and the fact that `1 ≤ |Norm x|` to get a lower bound
  -- on `sqrt |discr K|`.
  obtain ⟨x, h_nz, h_bd⟩ := exists_ne_zero_mem_ringOfIntegers_of_norm_le_mul_sqrt_dis

中文:
定理 abs_discr_ge'
  证明: by
  -- We use `exists_ne_zero_mem_ringOfIntegers_of_norm_le_mul_sqrt_discr` to get a nonzero
  -- algebraic integer `x` of small norm and the fact that `1 ≤ |Norm x|` to get a lower bound
  -- on `sqrt |discr K|`.
  obtain ⟨x, h_nz, h_bd⟩ := exists_ne_zero_mem_ringOfIntegers_of_norm_le_mul_sqrt_dis
-/
theorem abs_discr_ge' :
    (finrank Rat K) ^ (2 * finrank Rat K) / ((4 / π) ^ (2 * nrComplexPlaces K) *
      (finrank Rat K).factorial ^ 2) <= |discr K| := by
  -- We use `exists_ne_zero_mem_ringOfIntegers_of_norm_le_mul_sqrt_discr` to get a nonzero
  -- algebraic integer `x` of small norm and the fact that `1 ≤ |Norm x|` to get a lower bound
  -- on `sqrt |discr K|`.
  obtain ⟨x, h_nz, h_bd⟩ := exists_ne_zero_mem_ringOfIntegers_of_norm_le_mul_sqrt_discr K
  have h_nm : (1 : Real) <= |Algebra.norm Rat (x : K)| := by
    rw [← Algebra.coe_norm_int]; rw [← Int.cast_one]; rw [← Int.cast_abs]; rw [Rat.cast_intCast]; rw [Int.cast_le]
    exact Int.one_le_abs (Algebra.norm_ne_zero_iff.mpr h_nz)
  replace h_bd := le_trans h_nm h_bd
  rwa [← inv_mul_le_iff₀, inv_div, mul_one, Real.le_sqrt (by positivity) (by positivity),
    ← Int.cast_abs, div_pow, mul_pow, ← pow_mul, mul_comm _ 2, ← pow_mul, mul_comm _ 2] at h_bd
exact div_pos (by positivity) pow_pos (Nat.cast_pos.mpr finrank_pos) (finrank Rat K)

/--
theorem `abs_discr_ge_of_isTotallyComplex` / 定理 `abs_discr_ge_of_isTotallyComplex`

English:
theorem abs_discr_ge_of_isTotallyComplex
  given: [IsTotallyComplex K]
  proof: by
  have := abs_discr_ge' K
  rwa [← IsTotallyComplex.finrank] at this

中文:
定理 abs_discr_ge_of_isTotallyComplex
  条件: [IsTotallyComplex K]
  证明: by
  have := abs_discr_ge' K
  rwa [← IsTotallyComplex.finrank] at this

Depends on / 依赖: IsTotallyComplex, IsTotallyComplex.finrank, abs_discr_ge, finrank
-/
theorem abs_discr_ge_of_isTotallyComplex [IsTotallyComplex K] :
    (finrank Rat K) ^ (2 * finrank Rat K) / ((4 / π) ^ (finrank Rat K) *
      (finrank Rat K).factorial ^ 2) <= |discr K| := by
  have := abs_discr_ge' K
  rwa [← IsTotallyComplex.finrank] at this

/--
theorem `abs_discr_rpow_ge_of_isTotallyComplex` / 定理 `abs_discr_rpow_ge_of_isTotallyComplex`

English:
theorem abs_discr_rpow_ge_of_isTotallyComplex
  given: [IsTotallyComplex K]
  proof: by
  have h : 0 < (finrank Rat K : Real) := Nat.cast_pos.mpr finrank_pos
  rw [← Real.rpow_le_rpow_iff (z := finrank Rat K) (by positivity) (by positivity) h]; rw [Real.div_rpow
    (by positivity) (by positivity)]; rw [← Real.rpow_mul (by positivity)]; rw [inv_mul_cancel₀ h.ne']; rw [Real.rpow_one]

中文:
定理 abs_discr_rpow_ge_of_isTotallyComplex
  条件: [IsTotallyComplex K]
  证明: by
  have h : 0 < (finrank Rat K : Real) := Nat.cast_pos.mpr finrank_pos
  rw [← Real.rpow_le_rpow_iff (z := finrank Rat K) (by positivity) (by positivity) h]; rw [Real.div_rpow
    (by positivity) (by positivity)]; rw [← Real.rpow_mul (by positivity)]; rw [inv_mul_cancel₀ h.ne']; rw [Real.rpow_one]

Depends on / 依赖: Nat.cast_pos.mpr, Real.div_rpow, Real.mul_rpow, Real.rpow_le_rpow_iff, Real.rpow_mul, Real.rpow_natCast, Real.rpow_one, Real.rpow_two, cast_pos, div_rpow, finrank, finrank_pos, h.ne, mul_rpow, pow_mul, rpow_le_rpow_iff, rpow_mul, rpow_natCast, rpow_one, rpow_two
-/
theorem abs_discr_rpow_ge_of_isTotallyComplex [IsTotallyComplex K] :
    (finrank Rat K) ^ 2 / ((4 / π) * (finrank Rat K).factorial ^ (2 * (finrank Rat K : Real)⁻¹)) <=
        |discr K| ^ (finrank Rat K : Real)⁻¹ := by
  have h : 0 < (finrank Rat K : Real) := Nat.cast_pos.mpr finrank_pos
  rw [← Real.rpow_le_rpow_iff (z := finrank Rat K) (by positivity) (by positivity) h]; rw [Real.div_rpow
    (by positivity) (by positivity)]; rw [← Real.rpow_mul (by positivity)]; rw [inv_mul_cancel₀ h.ne']; rw [Real.rpow_one]; rw [Real.mul_rpow (by positivity) (by positivity)]; rw [Real.rpow_natCast]; rw [Real.rpow_natCast]; rw [← pow_mul]; rw [← Real.rpow_mul (by positivity)]; rw [inv_mul_cancel_right₀ h.ne']; rw [Real.rpow_two]
  exact abs_discr_ge_of_isTotallyComplex K

variable {K}

/--
theorem `abs_discr_ge` / 定理 `abs_discr_ge`

English:
theorem abs_discr_ge
  given: (h : 1 < finrank Rat K)
  proof: by
  refine le_trans ?_ (abs_discr_ge' K)
  -- The sequence `a n` is a lower bound for `|discr K|`. We prove below by induction a uniform
  -- lower bound for this sequence from which we deduce the result.
  rw [mul_comm 2 _]
  let a : Nat -> Real := fun n => (n : Real) ^ (n * 2) / ((4 / π) ^ n * (n

中文:
定理 abs_discr_ge
  条件: (h : 1 < finrank Rat K)
  证明: by
  refine le_trans ?_ (abs_discr_ge' K)
  -- The sequence `a n` is a lower bound for `|discr K|`. We prove below by induction a uniform
  -- lower bound for this sequence from which we deduce the result.
  rw [mul_comm 2 _]
  let a : Nat -> Real := fun n => (n : Real) ^ (n * 2) / ((4 / π) ^ n * (n

Depends on / 依赖: abs_discr_ge, le_trans
-/
theorem abs_discr_ge (h : 1 < finrank Rat K) :
    (4 / 9 : Real) * (3 * π / 4) ^ finrank Rat K <= |discr K| := by
  refine le_trans ?_ (abs_discr_ge' K)
  -- The sequence `a n` is a lower bound for `|discr K|`. We prove below by induction a uniform
  -- lower bound for this sequence from which we deduce the result.
  rw [mul_comm 2 _]
  let a : Nat -> Real := fun n => (n : Real) ^ (n * 2) / ((4 / π) ^ n * (n.factorial : Real) ^ 2)
  suffices forall n, 2 <= n -> (4 / 9 : Real) * (3 * π / 4) ^ n <= a n by
    refine le_trans (this (finrank Rat K) h) ?_
    simp only [a]
    gcongr
    · exact (one_le_div Real.pi_pos).2 Real.pi_le_four
    · rw [← card_add_two_mul_card_eq_rank, mul_comm]
      exact Nat.le_add_left _ _
  intro n hn
  induction n, hn using Nat.le_induction with
| base => exact le_of_eq by simp [a, Nat.factorial_two]; field
  | succ m _ h_m =>
      suffices (3 : Real) <= (1 + 1 / m : Real) ^ (2 * m) by
        convert_to _ <= (a m) * (1 + 1 / m : Real) ^ (2 * m) / (4 / π)
        · simp_rw [a, add_mul, one_mul, pow_succ, Nat.factorial_succ]
          field_simp
          simp [field, div_pow]
          ring
        · rw [_root_.le_div_iff₀ (by positivity), pow_succ]
          convert! (mul_le_mul h_m this (by positivity) (by positivity)) using 1
          field
      refine le_trans (le_of_eq (by simp [field]; norm_num)) (one_add_mul_le_pow ?_ (2 * m))
      exact le_trans (by norm_num : (-2 : Real) <= 0) (by positivity)

/--
theorem `abs_discr_gt_two` / 定理 `abs_discr_gt_two`

English:
theorem abs_discr_gt_two
  given: (h : 1 < finrank Rat K)
  statement: 2 < |discr K|
  proof: by
  rw [← Nat.succ_le_iff] at h
  rify
  calc
    (2 : Real) < (4 / 9) * (3 * π / 4) ^ 2 := by
      nlinarith [Real.pi_gt_three]
    _ <= (4 / 9 : Real) * (3 * π / 4) ^ finrank Rat K := by
      gcongr
      linarith [Real.pi_gt_three]
    _ <= |(discr K : Real)| := mod_cast abs_discr_ge h

中文:
定理 abs_discr_gt_two
  条件: (h : 1 < finrank Rat K)
  结论: 2 < |discr K|
  证明: by
  rw [← Nat.succ_le_iff] at h
  rify
  calc
    (2 : Real) < (4 / 9) * (3 * π / 4) ^ 2 := by
      nlinarith [Real.pi_gt_three]
    _ <= (4 / 9 : Real) * (3 * π / 4) ^ finrank Rat K := by
      gcongr
      linarith [Real.pi_gt_three]
    _ <= |(discr K : Real)| := mod_cast abs_discr_ge h

Depends on / 依赖: Nat.succ_le_iff, Real.pi_gt_three, abs_discr_ge, finrank, mod_cast, pi_gt_three, succ_le_iff
-/
theorem abs_discr_gt_two (h : 1 < finrank Rat K) : 2 < |discr K| := by
  rw [← Nat.succ_le_iff] at h
  rify
  calc
    (2 : Real) < (4 / 9) * (3 * π / 4) ^ 2 := by
      nlinarith [Real.pi_gt_three]
    _ <= (4 / 9 : Real) * (3 * π / 4) ^ finrank Rat K := by
      gcongr
      linarith [Real.pi_gt_three]
    _ <= |(discr K : Real)| := mod_cast abs_discr_ge h

/-!
### Hermite Theorem
This section is devoted to the proof of Hermite theorem.

Let `N` be an integer . We prove that the set `S` of finite extensions `K` of `ℚ`
(in some fixed extension `A` of `ℚ`) such that `|discr K| ≤ N` is finite by proving, using
`finite_of_finite_generating_set`, that there exists a finite set `T ⊆ A` such that
`∀ K ∈ S, ∃ x ∈ T, K = ℚ⟮x⟯` .

To find the set `T`, we construct a finite set `T₀` of polynomials in `ℤ[X]` containing, for each
`K ∈ S`, the minimal polynomial of a primitive element of `K`. The set `T` is then the union of
roots in `A` of the polynomials in `T₀`. More precisely, the set `T₀` is the set of all polynomials
in `ℤ[X]` of degrees and coefficients bounded by some explicit constants depending only on `N`.

Indeed, we prove that, for any field `K` in `S`, its degree is bounded, see
`rank_le_rankOfDiscrBdd`, and also its Minkowski bound, see `minkowskiBound_lt_boundOfDiscBdd`.
Thus it follows from `mixedEmbedding.exists_primitive_element_lt_of_isComplex` and
`mixedEmbedding.exists_primitive_element_lt_of_isReal` that there exists an algebraic integer
`x` of `K` such that `K = ℚ(x)` and the conjugates of `x` are all bounded by some quantity
depending only on `N`.

Since the primitive element `x` is constructed differently depending on whether `K` has an infinite
real place or not, the theorem is proved in two parts.
-/

namespace hermiteTheorem

open Polynomial

open scoped IntermediateField

variable (A : Type*) [Field A] [CharZero A]

/--
theorem `finite_of_finite_generating_set` / 定理 `finite_of_finite_generating_set`

English:
theorem finite_of_finite_generating_set
  statement: {p : IntermediateField Rat A -> Prop}
  proof: by
  rw [← Set.finite_coe_iff] at hT
refine Set.finite_coe_iff.mp Finite.of_injective
    (fun ⟨F, hF⟩ => (⟨(h F hF).choose, (h F hF).choose_spec.1⟩ : T)) (fun _ _ h_eq => ?_)
  rw [Subtype.ext_iff]; rw [Subtype.ext_iff]
  convert! congr_arg (Rat⟮·⟯) (Subtype.mk_eq_mk.mp h_eq)
  all_goals exact (h _

中文:
定理 finite_of_finite_generating_set
  结论: {p : 整数ermediateField Rat A -> 命题}
  证明: by
  rw [← Set.finite_coe_iff] at hT
refine Set.finite_coe_iff.mp Finite.of_injective
    (fun ⟨F, hF⟩ => (⟨(h F hF).choose, (h F hF).choose_spec.1⟩ : T)) (fun _ _ h_eq => ?_)
  rw [Subtype.ext_iff]; rw [Subtype.ext_iff]
  convert! congr_arg (Rat⟮·⟯) (Subtype.mk_eq_mk.mp h_eq)
  all_goals exact (h _

Depends on / 依赖: Finite, Finite.of_injective, Set.finite_coe_iff, Set.finite_coe_iff.mp, Subtype, Subtype.ext_iff, Subtype.mem, Subtype.mk_eq_mk.mp, all_goals, choose_spec, congr_arg, convert, ext_iff, finite_coe_iff, h_eq, mk_eq_mk, of_injective
-/
theorem finite_of_finite_generating_set {p : IntermediateField Rat A -> Prop}
    (S : Set {F : IntermediateField Rat A // p F}) {T : Set A}
    (hT : T.Finite) (h : forall F in S, exists x in T, F = Rat⟮x⟯) :
    S.Finite := by
  rw [← Set.finite_coe_iff] at hT
refine Set.finite_coe_iff.mp Finite.of_injective
    (fun ⟨F, hF⟩ => (⟨(h F hF).choose, (h F hF).choose_spec.1⟩ : T)) (fun _ _ h_eq => ?_)
  rw [Subtype.ext_iff]; rw [Subtype.ext_iff]
  convert! congr_arg (Rat⟮·⟯) (Subtype.mk_eq_mk.mp h_eq)
  all_goals exact (h _ (Subtype.mem _)).choose_spec.2

variable (N : Nat)

/--
Definition of `rankOfDiscrBdd` / `rankOfDiscrBdd` 的定义

English:
abbreviation rankOfDiscrBdd
  signature: : Nat
  body: max 1 (Nat.floor ((Real.log ((9 / 4 : Real) * N) / Real.log (3 * π / 4))))

中文:
缩写 rankOfDiscrBdd
  签名: : 自然数
  定义体: max 1 (Nat.floor ((Real.log ((9 / 4 : Real) * N) / Real.log (3 * π / 4))))

Depends on / 依赖: Nat.floor, Real.log
-/
noncomputable abbrev rankOfDiscrBdd : Nat :=
  max 1 (Nat.floor ((Real.log ((9 / 4 : Real) * N) / Real.log (3 * π / 4))))

/--
Definition of `boundOfDiscBdd` / `boundOfDiscBdd` 的定义

English:
abbreviation boundOfDiscBdd
  signature: : Real>=0
  body: sqrt N * (2 : Real>=0) ^ rankOfDiscrBdd N + 1

中文:
缩写 boundOfDiscBdd
  签名: : 实数>=0
  定义体: sqrt N * (2 : Real>=0) ^ rankOfDiscrBdd N + 1

Depends on / 依赖: rankOfDiscrBdd
-/
noncomputable abbrev boundOfDiscBdd : Real>=0 := sqrt N * (2 : Real>=0) ^ rankOfDiscrBdd N + 1

variable {N} (hK : |discr K| <= N)

include hK in
/--
theorem `rank_le_rankOfDiscrBdd` / 定理 `rank_le_rankOfDiscrBdd`

English:
theorem rank_le_rankOfDiscrBdd
  proof: by
  have h_nz : N != 0 := by
    refine fun h => discr_ne_zero K ?_
    rwa [h, Nat.cast_zero, abs_nonpos_iff] at hK
  have h₂ : 1 < 3 * π / 4 := by
    rw [_root_.lt_div_iff₀ (by positivity)]; rw [← _root_.div_lt_iff₀' (by positivity)]; rw [one_mul]
    linarith [Real.pi_gt_three]
  obtain h | h :

中文:
定理 rank_le_rankOfDiscrBdd
  证明: by
  have h_nz : N != 0 := by
    refine fun h => discr_ne_zero K ?_
    rwa [h, Nat.cast_zero, abs_nonpos_iff] at hK
  have h₂ : 1 < 3 * π / 4 := by
    rw [_root_.lt_div_iff₀ (by positivity)]; rw [← _root_.div_lt_iff₀' (by positivity)]; rw [one_mul]
    linarith [Real.pi_gt_three]
  obtain h | h :

Depends on / 依赖: Int.cast_le.mpr, Nat.cast_zero, Nat.le_floor_iff, Real.log_div_log, Real.pi_gt_three, Real.rpow_natCast, _root_, _root_.div_lt_iff, _root_.lt_div_iff, abs_discr_ge, abs_nonpos_iff, cast_le, cast_zero, contrapose, discr_ne_zero, finrank, h_nz, le_floor_iff, le_max_of_le_right, le_trans
-/
theorem rank_le_rankOfDiscrBdd :
    finrank Rat K <= rankOfDiscrBdd N := by
  have h_nz : N != 0 := by
    refine fun h => discr_ne_zero K ?_
    rwa [h, Nat.cast_zero, abs_nonpos_iff] at hK
  have h₂ : 1 < 3 * π / 4 := by
    rw [_root_.lt_div_iff₀ (by positivity)]; rw [← _root_.div_lt_iff₀' (by positivity)]; rw [one_mul]
    linarith [Real.pi_gt_three]
  obtain h | h := lt_or_ge 1 (finrank Rat K)
  · apply le_max_of_le_right
    rw [Nat.le_floor_iff]
    · have h := le_trans (abs_discr_ge h) (Int.cast_le.mpr hK)
      contrapose! h
      rw [← Real.rpow_natCast]
      rw [Real.log_div_log] at h
      refine lt_of_le_of_lt ?_ (mul_lt_mul_of_pos_left
        (Real.rpow_lt_rpow_of_exponent_lt h₂ h) (by positivity : (0 : Real) < 4 / 9))
      rw [Real.rpow_logb (lt_trans zero_lt_one h₂) (ne_of_gt h₂) (by positivity)]; rw [← mul_assoc]; rw [← inv_div]; rw [inv_mul_cancel₀ (by simp)]; rw [one_mul]; rw [Int.cast_natCast]
    · refine div_nonneg (Real.log_nonneg ?_) (Real.log_nonneg (le_of_lt h₂))
      rw [mul_comm]; rw [← mul_div_assoc]; rw [_root_.le_div_iff₀ (by positivity)]; rw [one_mul]; rw [← _root_.div_le_iff₀ (by positivity)]
      exact le_trans (by norm_num) (Nat.one_le_cast.mpr (Nat.one_le_iff_ne_zero.mpr h_nz))
  · exact le_max_of_le_left h

include hK in
/--
theorem `minkowskiBound_lt_boundOfDiscBdd` / 定理 `minkowskiBound_lt_boundOfDiscBdd`

English:
theorem minkowskiBound_lt_boundOfDiscBdd
  statement: minkowskiBound K ↑1 < boundOfDiscBdd N
  proof: by
  have : boundOfDiscBdd N - 1 < boundOfDiscBdd N := by
    simp_rw [boundOfDiscBdd, add_tsub_cancel_right, lt_add_iff_pos_right, zero_lt_one]
  refine lt_of_le_of_lt ?_ (coe_lt_coe.mpr this)
  rw [minkowskiBound]; rw [volume_fundamentalDomain_fractionalIdealLatticeBasis]; rw [boundOfDiscBdd]; rw 

中文:
定理 minkowskiBound_lt_boundOfDiscBdd
  结论: minkowskiBound K ↑1 < boundOfDiscBdd N
  证明: by
  have : boundOfDiscBdd N - 1 < boundOfDiscBdd N := by
    simp_rw [boundOfDiscBdd, add_tsub_cancel_right, lt_add_iff_pos_right, zero_lt_one]
  refine lt_of_le_of_lt ?_ (coe_lt_coe.mpr this)
  rw [minkowskiBound]; rw [volume_fundamentalDomain_fractionalIdealLatticeBasis]; rw [boundOfDiscBdd]; rw 

Depends on / 依赖: ENNReal, ENNReal.ofReal_one, FractionalIdeal, FractionalIdeal.absNorm_one, Rat.cast_one, Units.val_one, absNorm_one, add_tsub_cancel_right, boundOfDiscBdd, cast_one, coe_lt_coe, coe_lt_coe.mpr, finrank, lt_add_iff_pos_right, lt_of_le_of_lt, minkowskiBound, mixedEmbedding, mixedEmbedding.finrank, ofReal_one, one_mul
-/
theorem minkowskiBound_lt_boundOfDiscBdd : minkowskiBound K ↑1 < boundOfDiscBdd N := by
  have : boundOfDiscBdd N - 1 < boundOfDiscBdd N := by
    simp_rw [boundOfDiscBdd, add_tsub_cancel_right, lt_add_iff_pos_right, zero_lt_one]
  refine lt_of_le_of_lt ?_ (coe_lt_coe.mpr this)
  rw [minkowskiBound]; rw [volume_fundamentalDomain_fractionalIdealLatticeBasis]; rw [boundOfDiscBdd]; rw [add_tsub_cancel_right]; rw [Units.val_one]; rw [FractionalIdeal.absNorm_one]; rw [Rat.cast_one]; rw [ENNReal.ofReal_one]; rw [one_mul]; rw [mixedEmbedding.finrank]; rw [volume_fundamentalDomain_latticeBasis]; rw [coe_mul]; rw [ENNReal.coe_pow]; rw [coe_ofNat]; rw [show sqrt N = (1 : Real>=0∞) * sqrt N by rw [one_mul]]
  gcongr
  · exact pow_le_one₀ (by positivity) (by simp)
  · rwa [← NNReal.coe_le_coe, coe_nnnorm, Int.norm_eq_abs, ← Int.cast_abs,
      NNReal.coe_natCast, ← Int.cast_natCast, Int.cast_le]
  · exact one_le_two
  · exact rank_le_rankOfDiscrBdd hK

include hK in
/--
theorem `natDegree_le_rankOfDiscrBdd` / 定理 `natDegree_le_rankOfDiscrBdd`

English:
theorem natDegree_le_rankOfDiscrBdd
  given: (a : 𝓞 K) (h : Rat⟮(a : K)⟯ = ⊤)
  proof: by
  rw [Field.primitive_element_iff_minpoly_natDegree_eq]; rw [minpoly.isIntegrallyClosed_eq_field_fractions' Rat a.isIntegral_coe]; rw [(minpoly.monic a.isIntegral_coe).natDegree_map] at h
  exact h.symm ▸ rank_le_rankOfDiscrBdd hK

中文:
定理 natDegree_le_rankOfDiscrBdd
  条件: (a : 𝓞 K) (h : Rat⟮(a : K)⟯ = ⊤)
  证明: by
  rw [Field.primitive_element_iff_minpoly_natDegree_eq]; rw [minpoly.isIntegrallyClosed_eq_field_fractions' Rat a.isIntegral_coe]; rw [(minpoly.monic a.isIntegral_coe).natDegree_map] at h
  exact h.symm ▸ rank_le_rankOfDiscrBdd hK

Depends on / 依赖: Field.primitive_element_iff_minpoly_natDegree_eq, a.isIntegral_coe, h.symm, isIntegral_coe, isIntegrallyClosed_eq_field_fractions, minpoly, minpoly.isIntegrallyClosed_eq_field_fractions, minpoly.monic, natDegree_map, primitive_element_iff_minpoly_natDegree_eq, rank_le_rankOfDiscrBdd
-/
theorem natDegree_le_rankOfDiscrBdd (a : 𝓞 K) (h : Rat⟮(a : K)⟯ = ⊤) :
    natDegree (minpoly Int (a : K)) <= rankOfDiscrBdd N := by
  rw [Field.primitive_element_iff_minpoly_natDegree_eq]; rw [minpoly.isIntegrallyClosed_eq_field_fractions' Rat a.isIntegral_coe]; rw [(minpoly.monic a.isIntegral_coe).natDegree_map] at h
  exact h.symm ▸ rank_le_rankOfDiscrBdd hK

variable (N)

set_option backward.isDefEq.respectTransparency false in
/--
theorem `finite_of_discr_bdd_of_isReal` / 定理 `finite_of_discr_bdd_of_isReal`

English:
theorem finite_of_discr_bdd_of_isReal
  proof: by
  classical
  -- The bound on the degree of the generating polynomials
  let D := rankOfDiscrBdd N
  -- The bound on the Minkowski bound
  let B := boundOfDiscBdd N
  -- The bound on the coefficients of the generating polynomials
  let C := Nat.ceil ((max B 1) ^ D * Nat.choose D (D / 2))
  refine

中文:
定理 finite_of_discr_bdd_of_isReal
  证明: by
  classical
  -- The bound on the degree of the generating polynomials
  let D := rankOfDiscrBdd N
  -- The bound on the Minkowski bound
  let B := boundOfDiscBdd N
  -- The bound on the coefficients of the generating polynomials
  let C := Nat.ceil ((max B 1) ^ D * Nat.choose D (D / 2))
  refine

Depends on / 依赖: K.prop, NumberField, NumberField.mk
-/
theorem finite_of_discr_bdd_of_isReal :
    {K : { F : IntermediateField Rat A // FiniteDimensional Rat F} |
      haveI : NumberField K := @NumberField.mk _ _ inferInstance K.prop
      {w : InfinitePlace K | IsReal w}.Nonempty ∧ |discr K| <= N }.Finite := by
  classical
  -- The bound on the degree of the generating polynomials
  let D := rankOfDiscrBdd N
  -- The bound on the Minkowski bound
  let B := boundOfDiscBdd N
  -- The bound on the coefficients of the generating polynomials
  let C := Nat.ceil ((max B 1) ^ D * Nat.choose D (D / 2))
  refine finite_of_finite_generating_set A _ (bUnion_roots_finite (algebraMap Int A) D
      (Set.finite_Icc (-C : Int) C)) (fun ⟨K, hK₀⟩ ⟨hK₁, hK₂⟩ => ?_)
  -- We now need to prove that each field is generated by an element of the union of the root set
  simp_rw [Set.mem_iUnion]
  -- this is purely an optimization
  have : CharZero K := SubsemiringClass.instCharZero K
  have : NumberField K := @NumberField.mk _ _ inferInstance hK₀
  obtain ⟨w₀, hw₀⟩ := hK₁
  suffices minkowskiBound K ↑1 < (convexBodyLTFactor K) * B by
    obtain ⟨x, hx₁, hx₂⟩ := exists_primitive_element_lt_of_isReal K hw₀ this
    have hx := x.isIntegral_coe
    refine ⟨x, ⟨⟨minpoly Int (x : K), ⟨?_, fun i => ?_⟩, ?_⟩, ?_⟩⟩
    · exact natDegree_le_rankOfDiscrBdd hK₂ x hx₁
    · rw [Set.mem_Icc, ← abs_le, ← @Int.cast_le Real]
      refine (Eq.trans_le ?_ <| Embeddings.coeff_bdd_of_norm_le
          ((le_iff_le (x : K) _).mp (fun w => le_of_lt (hx₂ w))) i).trans ?_
      · rw [minpoly.isIntegrallyClosed_eq_field_fractions' Rat hx, coeff_map, eq_intCast,
          Int.norm_cast_rat, Int.norm_eq_abs, Int.cast_abs]
      · refine le_trans ?_ (Nat.le_ceil _)
        rw [show max ↑(max (B : Real>=0) 1) (1 : Real) = max (B : Real) 1 by simp]; rw [val_eq_coe]; rw [NNReal.coe_mul]; rw [NNReal.coe_pow]; rw [NNReal.coe_max]; rw [NNReal.coe_one]; rw [NNReal.coe_natCast]
        gcongr
        · exact le_max_right _ 1
        · exact rank_le_rankOfDiscrBdd hK₂
        · exact (Nat.choose_le_choose _ (rank_le_rankOfDiscrBdd hK₂)).trans
            (Nat.choose_le_middle _ _)
    · refine mem_rootSet.mpr ⟨minpoly.ne_zero hx, ?_⟩
      exact (aeval_algebraMap_eq_zero_iff A (x : K) _).mpr (minpoly.aeval Int (x : K))
    · rw [← (IntermediateField.lift_injective _).eq_iff, eq_comm] at hx₁
      convert! hx₁
      · simp only [IntermediateField.lift_top]
      · simp only [IntermediateField.lift_adjoin, Set.image_singleton]
  calc
    minkowskiBound K 1 < B := minkowskiBound_lt_boundOfDiscBdd hK₂
    _ = 1 * B := by rw [one_mul]
    _ <= convexBodyLTFactor K * B := by gcongr; exact mod_cast one_le_convexBodyLTFactor K

set_option backward.isDefEq.respectTransparency false in
/--
theorem `finite_of_discr_bdd_of_isComplex` / 定理 `finite_of_discr_bdd_of_isComplex`

English:
theorem finite_of_discr_bdd_of_isComplex
  proof: by
  classical
  -- The bound on the degree of the generating polynomials
  let D := rankOfDiscrBdd N
  -- The bound on the Minkowski bound
  let B := boundOfDiscBdd N
  -- The bound on the coefficients of the generating polynomials
  let C := Nat.ceil ((max (sqrt (1 + B ^ 2)) 1) ^ D * Nat.choose D 

中文:
定理 finite_of_discr_bdd_of_isComplex
  证明: by
  classical
  -- The bound on the degree of the generating polynomials
  let D := rankOfDiscrBdd N
  -- The bound on the Minkowski bound
  let B := boundOfDiscBdd N
  -- The bound on the coefficients of the generating polynomials
  let C := Nat.ceil ((max (sqrt (1 + B ^ 2)) 1) ^ D * Nat.choose D 

Depends on / 依赖: K.prop, NumberField, NumberField.mk
-/
theorem finite_of_discr_bdd_of_isComplex :
    {K : { F : IntermediateField Rat A // FiniteDimensional Rat F} |
      haveI : NumberField K := @NumberField.mk _ _ inferInstance K.prop
      {w : InfinitePlace K | IsComplex w}.Nonempty ∧ |discr K| <= N }.Finite := by
  classical
  -- The bound on the degree of the generating polynomials
  let D := rankOfDiscrBdd N
  -- The bound on the Minkowski bound
  let B := boundOfDiscBdd N
  -- The bound on the coefficients of the generating polynomials
  let C := Nat.ceil ((max (sqrt (1 + B ^ 2)) 1) ^ D * Nat.choose D (D / 2))
  refine finite_of_finite_generating_set A _ (bUnion_roots_finite (algebraMap Int A) D
      (Set.finite_Icc (-C : Int) C)) (fun ⟨K, hK₀⟩ ⟨hK₁, hK₂⟩ => ?_)
  -- We now need to prove that each field is generated by an element of the union of the root set
  simp_rw [Set.mem_iUnion]
  -- this is purely an optimization
  have : CharZero K := SubsemiringClass.instCharZero K
  have : NumberField K := @NumberField.mk _ _ inferInstance hK₀
  obtain ⟨w₀, hw₀⟩ := hK₁
  suffices minkowskiBound K ↑1 < (convexBodyLT'Factor K) * boundOfDiscBdd N by
    obtain ⟨x, hx₁, hx₂⟩ := exists_primitive_element_lt_of_isComplex K hw₀ this
    have hx := x.isIntegral_coe
    refine ⟨x, ⟨⟨minpoly Int (x : K), ⟨?_, fun i => ?_⟩, ?_⟩, ?_⟩⟩
    · exact natDegree_le_rankOfDiscrBdd hK₂ x hx₁
    · rw [Set.mem_Icc, ← abs_le, ← @Int.cast_le Real]
      refine (Eq.trans_le ?_ <| Embeddings.coeff_bdd_of_norm_le
          ((le_iff_le (x : K) _).mp (fun w => le_of_lt (hx₂ w))) i).trans ?_
      · rw [minpoly.isIntegrallyClosed_eq_field_fractions' Rat hx, coeff_map, eq_intCast,
          Int.norm_cast_rat, Int.norm_eq_abs, Int.cast_abs]
      · refine le_trans ?_ (Nat.le_ceil _)
        rw [val_eq_coe]; rw [NNReal.coe_mul]; rw [NNReal.coe_pow]; rw [NNReal.coe_max]; rw [NNReal.coe_one]; rw [Real.coe_sqrt]; rw [NNReal.coe_add 1]; rw [NNReal.coe_one]; rw [NNReal.coe_pow]
        gcongr
        · exact le_max_right _ 1
        · exact rank_le_rankOfDiscrBdd hK₂
        · rw [NNReal.coe_natCast, Nat.cast_le]
          exact (Nat.choose_le_choose _ (rank_le_rankOfDiscrBdd hK₂)).trans
            (Nat.choose_le_middle _ _)
    · refine mem_rootSet.mpr ⟨minpoly.ne_zero hx, ?_⟩
      exact (aeval_algebraMap_eq_zero_iff A (x : K) _).mpr (minpoly.aeval Int (x : K))
    · rw [← (IntermediateField.lift_injective _).eq_iff, eq_comm] at hx₁
      convert! hx₁
      · simp only [IntermediateField.lift_top]
      · simp only [IntermediateField.lift_adjoin, Set.image_singleton]
  calc
    minkowskiBound K 1 < B := minkowskiBound_lt_boundOfDiscBdd hK₂
    _ = 1 * B := by rw [one_mul]
    _ <= convexBodyLT'Factor K * B := by gcongr; exact mod_cast one_le_convexBodyLT'Factor K

/--
theorem `_root_.NumberField.finite_of_discr_bdd` / 定理 `_root_.NumberField.finite_of_discr_bdd`

English:
theorem _root_.NumberField.finite_of_discr_bdd
  proof: by
  refine Set.Finite.subset (Set.Finite.union (finite_of_discr_bdd_of_isReal A N)
    (finite_of_discr_bdd_of_isComplex A N)) ?_
  rintro ⟨K, hK₀⟩ hK₁
  -- this is purely an optimization
  have : CharZero K := SubsemiringClass.instCharZero K
  have : NumberField K := @NumberField.mk _ _ inferInsta

中文:
定理 _root_.NumberField.finite_of_discr_bdd
  证明: by
  refine Set.Finite.subset (Set.Finite.union (finite_of_discr_bdd_of_isReal A N)
    (finite_of_discr_bdd_of_isComplex A N)) ?_
  rintro ⟨K, hK₀⟩ hK₁
  -- this is purely an optimization
  have : CharZero K := SubsemiringClass.instCharZero K
  have : NumberField K := @NumberField.mk _ _ inferInsta

Depends on / 依赖: K.prop, NumberField, NumberField.mk
-/
theorem _root_.NumberField.finite_of_discr_bdd :
    {K : { F : IntermediateField Rat A // FiniteDimensional Rat F} |
      haveI : NumberField K := @NumberField.mk _ _ inferInstance K.prop
      |discr K| <= N }.Finite := by
  refine Set.Finite.subset (Set.Finite.union (finite_of_discr_bdd_of_isReal A N)
    (finite_of_discr_bdd_of_isComplex A N)) ?_
  rintro ⟨K, hK₀⟩ hK₁
  -- this is purely an optimization
  have : CharZero K := SubsemiringClass.instCharZero K
  have : NumberField K := @NumberField.mk _ _ inferInstance hK₀
  obtain ⟨w₀⟩ := (inferInstance : Nonempty (InfinitePlace K))
  by_cases hw₀ : IsReal w₀
  · apply Set.mem_union_left
    exact ⟨⟨w₀, hw₀⟩, hK₁⟩
  · apply Set.mem_union_right
    exact ⟨⟨w₀, not_isReal_iff_isComplex.mp hw₀⟩, hK₁⟩

end hermiteTheorem

end NumberField
