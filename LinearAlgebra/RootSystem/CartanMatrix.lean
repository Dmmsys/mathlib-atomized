/-
Copyright (c) 2025 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
module

public import Mathlib.Algebra.CharZero.Infinite
public import Mathlib.Algebra.Module.Submodule.Union
public import Mathlib.Data.Int.Star
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.ZMatrix
public import Mathlib.LinearAlgebra.RootSystem.Base
public import Mathlib.LinearAlgebra.RootSystem.Finite.Lemmas
public import Mathlib.LinearAlgebra.RootSystem.Finite.Nondegenerate

/-!
# Cartan matrices for root systems

This file contains definitions and basic results about Cartan matrices of root pairings / systems.

## Main definitions:
* `RootPairing.Base.cartanMatrix`: the Cartan matrix of a crystallographic root pairing, with
  respect to a base `b`.
* `RootPairing.Base.cartanMatrix_nondegenerate`: the Cartan matrix is non-degenerate.
* `RootPairing.Base.induction_on_cartanMatrix`: an induction principle expressing the connectedness
  of the Dynkin diagram of an irreducible root pairing.
* `RootPairing.Base.equivOfCartanMatrixEq`: a root system is determined by its Cartan matrix.

-/

@[expose] public section

noncomputable section

open FaithfulSMul (algebraMap_injective)
open Function Set
open Matrix
open Module.End (invtSubmodule mem_invtSubmodule)
open Submodule (span subset_span)

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

namespace RootPairing.Base

variable (S : Type*) [CommRing S] [Algebra S R]
  {P : RootPairing ι R M N} [P.IsValuedIn S] (b : P.Base)

/--
Definition of `cartanMatrixIn` / `cartanMatrixIn` 的定义

English:
definition cartanMatrixIn
  signature: :
  body: .of fun i j => P.pairingIn S i j

中文:
定义 cartanMatrixIn
  签名: :
  定义体: .of fun i j => P.pairingIn S i j

Depends on / 依赖: P.pairingIn, pairingIn
-/
def cartanMatrixIn :
    Matrix b.support b.support S :=
  .of fun i j => P.pairingIn S i j

/--
lemma `cartanMatrixIn_def` / 引理 `cartanMatrixIn_def`

English:
lemma cartanMatrixIn_def
  given: (i j : b.support)
  proof: rfl

@[simp]

中文:
引理 cartanMatrixIn_def
  条件: (i j : b.support)
  证明: rfl

@[simp]
-/
lemma cartanMatrixIn_def (i j : b.support) :
    b.cartanMatrixIn S i j = P.pairingIn S i j :=
  rfl

@[simp]
/--
lemma `algebraMap_cartanMatrixIn_apply` / 引理 `algebraMap_cartanMatrixIn_apply`

English:
lemma algebraMap_cartanMatrixIn_apply
  given: (i j : b.support)
  proof: by
  simp [cartanMatrixIn_def]

@[simp]

中文:
引理 algebraMap_cartanMatrixIn_apply
  条件: (i j : b.support)
  证明: by
  simp [cartanMatrixIn_def]

@[simp]

Depends on / 依赖: cartanMatrixIn_def
-/
lemma algebraMap_cartanMatrixIn_apply (i j : b.support) :
    algebraMap S R (b.cartanMatrixIn S i j) = P.pairing i j := by
  simp [cartanMatrixIn_def]

@[simp]
/--
lemma `cartanMatrixIn_apply_same` / 引理 `cartanMatrixIn_apply_same`

English:
lemma cartanMatrixIn_apply_same
  given: [FaithfulSMul S R] (i : b.support)
  proof: FaithfulSMul.algebraMap_injective S R by simp [cartanMatrixIn_def, map_ofNat]

中文:
引理 cartanMatrixIn_apply_same
  条件: [忠实标量乘法 S R] (i : b.support)
  证明: FaithfulSMul.algebraMap_injective S R by simp [cartanMatrixIn_def, map_ofNat]

Depends on / 依赖: FaithfulSMul, FaithfulSMul.algebraMap_injective, algebraMap_injective, cartanMatrixIn_def, map_ofNat
-/
lemma cartanMatrixIn_apply_same [FaithfulSMul S R] (i : b.support) :
    b.cartanMatrixIn S i i = 2 :=
FaithfulSMul.algebraMap_injective S R by simp [cartanMatrixIn_def, map_ofNat]

/--
lemma `cartanMatrixIn_mul_diagonal_eq` / 引理 `cartanMatrixIn_mul_diagonal_eq`

English:
lemma cartanMatrixIn_mul_diagonal_eq
  statement: {P : RootPairing ι R M N} [P.IsRootSystem] [P.IsValuedIn S]
  proof: by
  ext
  simp [B.two_mul_apply_root_root]

中文:
引理 cartanMatrixIn_mul_diagonal_eq
  结论: {P : RootPairing ι R M N} [P.是RootSystem] [P.是ValuedIn S]
  证明: by
  ext
  simp [B.two_mul_apply_root_root]

Depends on / 依赖: B.two_mul_apply_root_root, two_mul_apply_root_root
-/
lemma cartanMatrixIn_mul_diagonal_eq {P : RootPairing ι R M N} [P.IsRootSystem] [P.IsValuedIn S]
    (B : P.InvariantForm) (b : P.Base) [DecidableEq ι] :
    (b.cartanMatrixIn S).map (algebraMap S R) *
      (Matrix.diagonal fun i : b.support => B.form (P.root i) (P.root i)) =
      (2 : R) • B.form.toMatrix b.toWeightBasis := by
  ext
  simp [B.two_mul_apply_root_root]

/--
lemma `cartanMatrixIn_nondegenerate` / 引理 `cartanMatrixIn_nondegenerate`

English:
lemma cartanMatrixIn_nondegenerate
  statement: [IsDomain R] [NeZero (2 : R)] [FaithfulSMul S R] [IsDomain S]
  proof: by
  classical
  obtain ⟨B, hB⟩ : exists B : P.InvariantForm, B.form.Nondegenerate :=
    ⟨P.toInvariantForm, P.rootForm_nondegenerate⟩
  replace hB : ((2 : R) • B.form.toMatrix b.toWeightBasis).Nondegenerate := by
    rwa [Matrix.Nondegenerate.smul_iff two_ne_zero, LinearMap.BilinForm.nondegenerate

中文:
引理 cartanMatrixIn_nondegenerate
  结论: [是整环 R] [NeZero (2 : R)] [忠实标量乘法 S R] [是整环 S]
  证明: by
  classical
  obtain ⟨B, hB⟩ : exists B : P.InvariantForm, B.form.Nondegenerate :=
    ⟨P.toInvariantForm, P.rootForm_nondegenerate⟩
  replace hB : ((2 : R) • B.form.toMatrix b.toWeightBasis).Nondegenerate := by
    rwa [Matrix.Nondegenerate.smul_iff two_ne_zero, LinearMap.BilinForm.nondegenerate

Depends on / 依赖: B.form, B.form.Nondegenerate, B.form.toMatrix, BilinForm, Finset, Finset.prod_ne_zero_iff, InvariantForm, LinearMap, LinearMap.BilinForm.nondegenerate_toMatrix_iff, Matrix, Matrix.Nondegenerate.smul_iff, Matrix.det_diagonal, Matrix.diagonal, Matrix.nondegenerate_iff_det_ne_zero, Nondegenerate, P.InvariantForm, P.root, P.rootForm_nondegenerate, P.toInvariantForm, b.support
-/
lemma cartanMatrixIn_nondegenerate [IsDomain R] [NeZero (2 : R)] [FaithfulSMul S R] [IsDomain S]
    {P : RootPairing ι R M N} [P.IsRootSystem] [P.IsValuedIn S] [Fintype ι] [P.IsAnisotropic]
    (b : P.Base) :
    (b.cartanMatrixIn S).Nondegenerate := by
  classical
  obtain ⟨B, hB⟩ : exists B : P.InvariantForm, B.form.Nondegenerate :=
    ⟨P.toInvariantForm, P.rootForm_nondegenerate⟩
  replace hB : ((2 : R) • B.form.toMatrix b.toWeightBasis).Nondegenerate := by
    rwa [Matrix.Nondegenerate.smul_iff two_ne_zero, LinearMap.BilinForm.nondegenerate_toMatrix_iff]
  have aux : (Matrix.diagonal fun i : b.support => B.form (P.root i) (P.root i)).Nondegenerate := by
    rw [Matrix.nondegenerate_iff_det_ne_zero]; rw [Matrix.det_diagonal]; rw [Finset.prod_ne_zero_iff]
    aesop
  rw [← cartanMatrixIn_mul_diagonal_eq (S := S)]; rw [Matrix.Nondegenerate.mul_iff_right aux]; rw [Matrix.nondegenerate_iff_det_ne_zero]; rw [← (algebraMap S R).mapMatrix_apply]; rw [← RingHom.map_det]; rw [ne_eq]; rw [FaithfulSMul.algebraMap_eq_zero_iff] at hB
  rwa [Matrix.nondegenerate_iff_det_ne_zero]

section IsCrystallographic

variable [P.IsCrystallographic]

/--
Definition of `cartanMatrix` / `cartanMatrix` 的定义

English:
abbreviation cartanMatrix
  signature: :
  body: b.cartanMatrixIn Int

中文:
缩写 cartanMatrix
  签名: :
  定义体: b.cartanMatrixIn Int

Depends on / 依赖: b.cartanMatrixIn, cartanMatrixIn
-/
abbrev cartanMatrix :
    Matrix b.support b.support Int :=
  b.cartanMatrixIn Int

variable [CharZero R]

/--
lemma `cartanMatrix_apply_same` / 引理 `cartanMatrix_apply_same`

English:
lemma cartanMatrix_apply_same
  given: (i : b.support)
  proof: b.cartanMatrixIn_apply_same Int i

中文:
引理 cartanMatrix_apply_same
  条件: (i : b.support)
  证明: b.cartanMatrixIn_apply_same Int i

Depends on / 依赖: b.cartanMatrixIn_apply_same, cartanMatrixIn_apply_same
-/
lemma cartanMatrix_apply_same (i : b.support) :
    b.cartanMatrix i i = 2 :=
  b.cartanMatrixIn_apply_same Int i

/--
lemma `cartanMatrix_apply_eq_zero_iff_pairing` / 引理 `cartanMatrix_apply_eq_zero_iff_pairing`

English:
lemma cartanMatrix_apply_eq_zero_iff_pairing
  given: {i j : b.support}
  proof: by
  rw [cartanMatrix]; rw [cartanMatrixIn_def]; rw [← (algebraMap_injective Int R).eq_iff]; rw [algebraMap_pairingIn]; rw [map_zero]

中文:
引理 cartanMatrix_apply_eq_zero_iff_pairing
  条件: {i j : b.support}
  证明: by
  rw [cartanMatrix]; rw [cartanMatrixIn_def]; rw [← (algebraMap_injective Int R).eq_iff]; rw [algebraMap_pairingIn]; rw [map_zero]

Depends on / 依赖: algebraMap_injective, algebraMap_pairingIn, cartanMatrix, cartanMatrixIn_def, eq_iff, map_zero
-/
lemma cartanMatrix_apply_eq_zero_iff_pairing {i j : b.support} :
    b.cartanMatrix i j = 0 ↔ P.pairing i j = 0 := by
  rw [cartanMatrix]; rw [cartanMatrixIn_def]; rw [← (algebraMap_injective Int R).eq_iff]; rw [algebraMap_pairingIn]; rw [map_zero]

variable [IsDomain R]

/--
lemma `cartanMatrix_apply_eq_zero_iff_symm` / 引理 `cartanMatrix_apply_eq_zero_iff_symm`

English:
lemma cartanMatrix_apply_eq_zero_iff_symm
  given: {i j : b.support}
  proof: by
  have : Module.IsReflexive R M := .of_isPerfPair P.toLinearMap
  simp only [cartanMatrix_apply_eq_zero_iff_pairing, P.pairing_eq_zero_iff]

中文:
引理 cartanMatrix_apply_eq_zero_iff_symm
  条件: {i j : b.support}
  证明: by
  have : Module.IsReflexive R M := .of_isPerfPair P.toLinearMap
  simp only [cartanMatrix_apply_eq_zero_iff_pairing, P.pairing_eq_zero_iff]

Depends on / 依赖: IsReflexive, Module, Module.IsReflexive, P.pairing_eq_zero_iff, P.toLinearMap, cartanMatrix_apply_eq_zero_iff_pairing, of_isPerfPair, pairing_eq_zero_iff, toLinearMap
-/
lemma cartanMatrix_apply_eq_zero_iff_symm {i j : b.support} :
    b.cartanMatrix i j = 0 ↔ b.cartanMatrix j i = 0 := by
  have : Module.IsReflexive R M := .of_isPerfPair P.toLinearMap
  simp only [cartanMatrix_apply_eq_zero_iff_pairing, P.pairing_eq_zero_iff]

variable [Finite ι]

/--
lemma `cartanMatrix_le_zero_of_ne` / 引理 `cartanMatrix_le_zero_of_ne`

English:
lemma cartanMatrix_le_zero_of_ne
  proof: b.pairingIn_le_zero_of_ne (by rwa [ne_eq, ← Subtype.ext_iff]) i.property j.property

中文:
引理 cartanMatrix_le_zero_of_ne
  证明: b.pairingIn_le_zero_of_ne (by rwa [ne_eq, ← Subtype.ext_iff]) i.property j.property

Depends on / 依赖: Subtype, Subtype.ext_iff, b.pairingIn_le_zero_of_ne, ext_iff, i.property, j.property, ne_eq, pairingIn_le_zero_of_ne, property
-/
lemma cartanMatrix_le_zero_of_ne
    (i j : b.support) (h : i != j) :
    b.cartanMatrix i j <= 0 :=
  b.pairingIn_le_zero_of_ne (by rwa [ne_eq, ← Subtype.ext_iff]) i.property j.property

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `cartanMatrix_mem_of_ne` / 引理 `cartanMatrix_mem_of_ne`

English:
lemma cartanMatrix_mem_of_ne
  given: {i j : b.support} (hij : i != j)
  proof: by
  have : Module.IsReflexive R M := .of_isPerfPair P.toLinearMap
  have : Module.IsReflexive R N := .of_isPerfPair P.flip.toLinearMap
  simp only [cartanMatrix, cartanMatrixIn_def]
  have h₁ := P.pairingIn_pairingIn_mem_set_of_isCrystallographic i j
  have h₂ : P.pairingIn Int i j <= 0 := b.cartan

中文:
引理 cartanMatrix_mem_of_ne
  条件: {i j : b.support} (hij : i != j)
  证明: by
  have : Module.IsReflexive R M := .of_isPerfPair P.toLinearMap
  have : Module.IsReflexive R N := .of_isPerfPair P.flip.toLinearMap
  simp only [cartanMatrix, cartanMatrixIn_def]
  have h₁ := P.pairingIn_pairingIn_mem_set_of_isCrystallographic i j
  have h₂ : P.pairingIn Int i j <= 0 := b.cartan

Depends on / 依赖: IsReflexive, Module, Module.IsReflexive, P.flip.toLinearMap, P.pairingIn, P.pairingIn_pairingIn_mem_set_of_isCrystallographic, P.toLinearMap, b.cartanMatrix_le_zero_of_ne, cartanMatrix, cartanMatrixIn_def, cartanMatrix_le_zero_of_ne, contra, of_isPerfPair, pairingIn, pairingIn_neg_one_neg_, pairingIn_pairingIn_mem_set_of_isCrystallographic, replace, toLinearMap
-/
lemma cartanMatrix_mem_of_ne {i j : b.support} (hij : i != j) :
    b.cartanMatrix i j in ({-3, -2, -1, 0} : Set Int) := by
  have : Module.IsReflexive R M := .of_isPerfPair P.toLinearMap
  have : Module.IsReflexive R N := .of_isPerfPair P.flip.toLinearMap
  simp only [cartanMatrix, cartanMatrixIn_def]
  have h₁ := P.pairingIn_pairingIn_mem_set_of_isCrystallographic i j
  have h₂ : P.pairingIn Int i j <= 0 := b.cartanMatrix_le_zero_of_ne i j hij
  suffices P.pairingIn Int i j != -4 by aesop
  by_contra contra
  replace contra : P.pairingIn Int j i = -1 ∧ P.pairingIn Int i j = -4 := ⟨by simp_all, contra⟩
  rw [pairingIn_neg_one_neg_four_iff] at contra
  refine (not_linearIndependent_iff.mpr ?_) b.linearIndepOn_root
  refine ⟨⟨{i, j}, by simpa⟩, Finsupp.single i (1 : R) + Finsupp.single j (2 : R), ?_⟩
  simp [contra, hij, hij.symm]

/--
lemma `cartanMatrix_eq_neg_chainTopCoeff` / 引理 `cartanMatrix_eq_neg_chainTopCoeff`

English:
lemma cartanMatrix_eq_neg_chainTopCoeff
  given: {i j : b.support} (hij : i != j)
  proof: by
  rw [cartanMatrix]; rw [cartanMatrixIn_def]; rw [← neg_eq_iff_eq_neg]; rw [← b.chainTopCoeff_eq_of_ne hij.symm]

中文:
引理 cartanMatrix_eq_neg_chainTopCoeff
  条件: {i j : b.support} (hij : i != j)
  证明: by
  rw [cartanMatrix]; rw [cartanMatrixIn_def]; rw [← neg_eq_iff_eq_neg]; rw [← b.chainTopCoeff_eq_of_ne hij.symm]

Depends on / 依赖: b.chainTopCoeff_eq_of_ne, cartanMatrix, cartanMatrixIn_def, chainTopCoeff_eq_of_ne, hij.symm, neg_eq_iff_eq_neg
-/
lemma cartanMatrix_eq_neg_chainTopCoeff {i j : b.support} (hij : i != j) :
    b.cartanMatrix i j = - P.chainTopCoeff j i := by
  rw [cartanMatrix]; rw [cartanMatrixIn_def]; rw [← neg_eq_iff_eq_neg]; rw [← b.chainTopCoeff_eq_of_ne hij.symm]

/--
lemma `cartanMatrix_apply_eq_zero_iff` / 引理 `cartanMatrix_apply_eq_zero_iff`

English:
lemma cartanMatrix_apply_eq_zero_iff
  given: {i j : b.support} (hij : i != j)
  proof: by
  rw [b.cartanMatrix_eq_neg_chainTopCoeff hij]; rw [neg_eq_zero]; rw [Int.natCast_eq_zero]; rw [P.chainTopCoeff_eq_zero_iff]
  replace hij := b.linearIndependent_pair_of_ne hij.symm
  tauto

中文:
引理 cartanMatrix_apply_eq_zero_iff
  条件: {i j : b.support} (hij : i != j)
  证明: by
  rw [b.cartanMatrix_eq_neg_chainTopCoeff hij]; rw [neg_eq_zero]; rw [Int.natCast_eq_zero]; rw [P.chainTopCoeff_eq_zero_iff]
  replace hij := b.linearIndependent_pair_of_ne hij.symm
  tauto

Depends on / 依赖: Int.natCast_eq_zero, P.chainTopCoeff_eq_zero_iff, b.cartanMatrix_eq_neg_chainTopCoeff, b.linearIndependent_pair_of_ne, cartanMatrix_eq_neg_chainTopCoeff, chainTopCoeff_eq_zero_iff, hij.symm, linearIndependent_pair_of_ne, natCast_eq_zero, neg_eq_zero, replace
-/
lemma cartanMatrix_apply_eq_zero_iff {i j : b.support} (hij : i != j) :
    b.cartanMatrix i j = 0 ↔ P.root i + P.root j ∉ range P.root := by
  rw [b.cartanMatrix_eq_neg_chainTopCoeff hij]; rw [neg_eq_zero]; rw [Int.natCast_eq_zero]; rw [P.chainTopCoeff_eq_zero_iff]
  replace hij := b.linearIndependent_pair_of_ne hij.symm
  tauto

/--
lemma `abs_cartanMatrix_apply` / 引理 `abs_cartanMatrix_apply`

English:
lemma abs_cartanMatrix_apply
  given: [DecidableEq ι] {i j : b.support}
  proof: by
  rcases eq_or_ne i j with rfl | h
  · simp
  · simpa [h] using b.cartanMatrix_le_zero_of_ne i j h

@[simp]

中文:
引理 abs_cartanMatrix_apply
  条件: [DecidableEq ι] {i j : b.support}
  证明: by
  rcases eq_or_ne i j with rfl | h
  · simp
  · simpa [h] using b.cartanMatrix_le_zero_of_ne i j h

@[simp]

Depends on / 依赖: b.cartanMatrix_le_zero_of_ne, cartanMatrix_le_zero_of_ne, eq_or_ne
-/
lemma abs_cartanMatrix_apply [DecidableEq ι] {i j : b.support} :
    |b.cartanMatrix i j| = (if i = j then 4 else 0) - b.cartanMatrix i j := by
  rcases eq_or_ne i j with rfl | h
  · simp
  · simpa [h] using b.cartanMatrix_le_zero_of_ne i j h

@[simp]
/--
lemma `cartanMatrix_map_abs` / 引理 `cartanMatrix_map_abs`

English:
lemma cartanMatrix_map_abs
  given: [DecidableEq ι]
  proof: by
  ext; simp [abs_cartanMatrix_apply, Matrix.ofNat_apply]

中文:
引理 cartanMatrix_map_abs
  条件: [DecidableEq ι]
  证明: by
  ext; simp [abs_cartanMatrix_apply, Matrix.ofNat_apply]

Depends on / 依赖: Matrix, Matrix.ofNat_apply, abs_cartanMatrix_apply, ofNat_apply
-/
lemma cartanMatrix_map_abs [DecidableEq ι] :
    b.cartanMatrix.map abs = 4 - b.cartanMatrix := by
  ext; simp [abs_cartanMatrix_apply, Matrix.ofNat_apply]

/--
lemma `cartanMatrix_nondegenerate` / 引理 `cartanMatrix_nondegenerate`

English:
lemma cartanMatrix_nondegenerate
  proof: let _i : Fintype ι := Fintype.ofFinite ι
  cartanMatrixIn_nondegenerate Int b

omit [Finite ι] [IsDomain R] in

中文:
引理 cartanMatrix_nondegenerate
  证明: let _i : Fintype ι := Fintype.ofFinite ι
  cartanMatrixIn_nondegenerate Int b

omit [Finite ι] [IsDomain R] in

Depends on / 依赖: Fintype, Fintype.ofFinite, cartanMatrixIn_nondegenerate, ofFinite
-/
lemma cartanMatrix_nondegenerate
    {P : RootPairing ι R M N} [P.IsRootSystem] [P.IsCrystallographic] (b : P.Base) :
    b.cartanMatrix.Nondegenerate :=
  let _i : Fintype ι := Fintype.ofFinite ι
  cartanMatrixIn_nondegenerate Int b

omit [Finite ι] [IsDomain R] in
/--
lemma `cartanMatrix_mul_diagonal_eq` / 引理 `cartanMatrix_mul_diagonal_eq`

English:
lemma cartanMatrix_mul_diagonal_eq
  given: [Fintype ι] [DecidableEq ι] [P.IsRootSystem]
  proof: fun i => P.RootFormIn Int (P.rootSpanMem Int i) (P.rootSpanMem Int i)
    b.cartanMatrix * diagonal d =
      (2 : Int) • (P.posRootForm Int).posForm.toMatrix b.toWeightBasisInt := by
  ext i j
  apply algebraMap_injective Int R
  simp only [mul_diagonal, map_mul, algebraMap_rootFormIn, posRootForm_

中文:
引理 cartanMatrix_mul_diagonal_eq
  条件: [有限类型 ι] [DecidableEq ι] [P.是RootSystem]
  证明: fun i => P.RootFormIn Int (P.rootSpanMem Int i) (P.rootSpanMem Int i)
    b.cartanMatrix * diagonal d =
      (2 : Int) • (P.posRootForm Int).posForm.toMatrix b.toWeightBasisInt := by
  ext i j
  apply algebraMap_injective Int R
  simp only [mul_diagonal, map_mul, algebraMap_rootFormIn, posRootForm_

Depends on / 依赖: P.RootFormIn, P.rootSpanMem, RootFormIn, rootSpanMem
-/
lemma cartanMatrix_mul_diagonal_eq [Fintype ι] [DecidableEq ι] [P.IsRootSystem] :
    letI d : b.support -> Int := fun i => P.RootFormIn Int (P.rootSpanMem Int i) (P.rootSpanMem Int i)
    b.cartanMatrix * diagonal d =
      (2 : Int) • (P.posRootForm Int).posForm.toMatrix b.toWeightBasisInt := by
  ext i j
  apply algebraMap_injective Int R
  simp only [mul_diagonal, map_mul, algebraMap_rootFormIn, posRootForm_eq, Matrix.smul_apply,
    LinearMap.BilinForm.toMatrix_apply, Int.zsmul_eq_mul]
  simpa [← algebraMap_pairingIn P Int i j] using
    congr_fun₂ (cartanMatrixIn_mul_diagonal_eq Int P.toInvariantForm b) i j

/--
lemma `exists_cartanMatrix_mul_diagaonal_posDef` / 引理 `exists_cartanMatrix_mul_diagaonal_posDef`

English:
lemma exists_cartanMatrix_mul_diagaonal_posDef
  given: [DecidableEq ι] [P.IsRootSystem]
  proof: by
  have _i : Fintype ι := Fintype.ofFinite ι
  set d : b.support -> Int := fun i => P.RootFormIn Int (P.rootSpanMem Int i) (P.rootSpanMem Int i) with hd
  refine ⟨d, fun i => ?_, ?_⟩
  · rw [hd, ← posRootForm_eq]
    exact RootPositiveForm.zero_lt_posForm_apply_root _ _
  · rw [cartanMatrix_mul_di

中文:
引理 存在_cartanMatrix_mul_diagaonal_posDef
  条件: [DecidableEq ι] [P.是RootSystem]
  证明: by
  have _i : Fintype ι := Fintype.ofFinite ι
  set d : b.support -> Int := fun i => P.RootFormIn Int (P.rootSpanMem Int i) (P.rootSpanMem Int i) with hd
  refine ⟨d, fun i => ?_, ?_⟩
  · rw [hd, ← posRootForm_eq]
    exact RootPositiveForm.zero_lt_posForm_apply_root _ _
  · rw [cartanMatrix_mul_di

Depends on / 依赖: BilinFor, BilinForm, Fintype, Fintype.ofFinite, IsSymm, LinearMap, LinearMap.BilinFor, LinearMap.BilinForm.isSymm_iff, Matrix, Matrix.PosDef.smul, P.RootFormIn, P.posRootForm, P.rootFormIn_isSymm, P.rootSpanMem, PosDef, RootFormIn, RootPositiveForm, RootPositiveForm.zero_lt_posForm_apply_root, b.support, cartanMatrix_mul_diagonal_eq
-/
lemma exists_cartanMatrix_mul_diagaonal_posDef [DecidableEq ι] [P.IsRootSystem] :
    exists d : b.support -> Int, (forall i, 0 < d i) ∧ (b.cartanMatrix * diagonal d).PosDef := by
  have _i : Fintype ι := Fintype.ofFinite ι
  set d : b.support -> Int := fun i => P.RootFormIn Int (P.rootSpanMem Int i) (P.rootSpanMem Int i) with hd
  refine ⟨d, fun i => ?_, ?_⟩
  · rw [hd, ← posRootForm_eq]
    exact RootPositiveForm.zero_lt_posForm_apply_root _ _
  · rw [cartanMatrix_mul_diagonal_eq]
    refine Matrix.PosDef.smul ?_ two_pos
    have aux : (P.posRootForm Int).posForm.IsSymm := by
      simpa only [posRootForm_eq, LinearMap.BilinForm.isSymm_iff] using P.rootFormIn_isSymm Int
    rw [← LinearMap.BilinForm.posDef_toQuadraticMap_iff_matrix _ _ aux]
    simpa using P.posRootForm_rootFormIn_posDef Int

/--
lemma `exists_cartanMatrix_diagaonal_mul_posDef` / 引理 `exists_cartanMatrix_diagaonal_mul_posDef`

English:
lemma exists_cartanMatrix_diagaonal_mul_posDef
  given: [DecidableEq ι] [P.IsRootSystem]
  proof: by
  obtain ⟨d, hd, hd'⟩ := b.flip.exists_cartanMatrix_mul_diagaonal_posDef
  refine ⟨d, hd, ?_⟩
  rw [← PosDef.transpose_iff] at hd'
  aesop

中文:
引理 存在_cartanMatrix_diagaonal_mul_posDef
  条件: [DecidableEq ι] [P.是RootSystem]
  证明: by
  obtain ⟨d, hd, hd'⟩ := b.flip.exists_cartanMatrix_mul_diagaonal_posDef
  refine ⟨d, hd, ?_⟩
  rw [← PosDef.transpose_iff] at hd'
  aesop

Depends on / 依赖: PosDef, PosDef.transpose_iff, b.flip.exists_cartanMatrix_mul_diagaonal_posDef, exists_cartanMatrix_mul_diagaonal_posDef, transpose_iff
-/
lemma exists_cartanMatrix_diagaonal_mul_posDef [DecidableEq ι] [P.IsRootSystem] :
    exists d : b.support -> Int, (forall i, 0 < d i) ∧ (diagonal d * b.cartanMatrix).PosDef := by
  obtain ⟨d, hd, hd'⟩ := b.flip.exists_cartanMatrix_mul_diagaonal_posDef
  refine ⟨d, hd, ?_⟩
  rw [← PosDef.transpose_iff] at hd'
  aesop

open LinearMap Module.End in
/--
lemma `det_four_sub_cartanMatrix_ne_zero` / 引理 `det_four_sub_cartanMatrix_ne_zero`

English:
lemma det_four_sub_cartanMatrix_ne_zero
  given: [DecidableEq ι] [P.IsRootSystem]
  proof: by
  suffices ¬ HasEigenvalue b.cartanMatrix.toLin' 4 by
    have aux : (4 - b.cartanMatrix).toLin' = - (b.cartanMatrix.toLin' - (4 : Int) • 1) := by ext; simp
    rwa [ne_eq, ← det_toLin', det_eq_zero_iff_ker_ne_bot, aux, ker_neg, ← eigenspace_def,
      ← hasEigenvalue_iff]
  obtain ⟨d, hd, hdS⟩ :

中文:
引理 det_four_sub_cartanMatrix_ne_zero
  条件: [DecidableEq ι] [P.是RootSystem]
  证明: by
  suffices ¬ HasEigenvalue b.cartanMatrix.toLin' 4 by
    have aux : (4 - b.cartanMatrix).toLin' = - (b.cartanMatrix.toLin' - (4 : Int) • 1) := by ext; simp
    rwa [ne_eq, ← det_toLin', det_eq_zero_iff_ker_ne_bot, aux, ker_neg, ← eigenspace_def,
      ← hasEigenvalue_iff]
  obtain ⟨d, hd, hdS⟩ :

Depends on / 依赖: HasEigenvalue, b.cartanMatrix, b.cartanMatrix.toLin, b.exists_cartanMatrix_diagaonal_mul_posDef, b.support, cartanMatrix, cartanMatrix_le_zero_of_ne, det_eq_zero_iff_ker_ne_bot, det_toLin, eigenspace_def, eq_or_ne, exists_cartanMatrix_diagaonal_mul_posDef, hasEigenvalue_iff, ker_neg, ne_eq, support
-/
lemma det_four_sub_cartanMatrix_ne_zero [DecidableEq ι] [P.IsRootSystem] :
    (4 - b.cartanMatrix).det != 0 := by
  suffices ¬ HasEigenvalue b.cartanMatrix.toLin' 4 by
    have aux : (4 - b.cartanMatrix).toLin' = - (b.cartanMatrix.toLin' - (4 : Int) • 1) := by ext; simp
    rwa [ne_eq, ← det_toLin', det_eq_zero_iff_ker_ne_bot, aux, ker_neg, ← eigenspace_def,
      ← hasEigenvalue_iff]
  obtain ⟨d, hd, hdS⟩ := b.exists_cartanMatrix_diagaonal_mul_posDef
  have aux (i j : b.support) : b.cartanMatrix i j <= if i = j then 2 else 0 := by
    rcases eq_or_ne i j with rfl | hij
    · simp
    · simpa [hij] using cartanMatrix_le_zero_of_ne b i j hij
  have := b.cartanMatrix.lt_two_mul_of_mul_diagonal_posDef_of_for_le_of_hasEigen d hdS hd 2 4 aux
  aesop

/--
lemma `induction_on_cartanMatrix` / 引理 `induction_on_cartanMatrix`

English:
lemma induction_on_cartanMatrix
  statement: [P.IsReduced] [P.IsIrreducible]
  proof: by
  let q : Submodule R M := span R (P.root ∘ (↑) '' {i | p i})
have hq₀ : q != ⊥ := q.ne_bot_iff.mpr ⟨P.root i, subset_span by simpa, P.ne_zero i⟩
  have hq_mem (k : b.support) : P.root k in q ↔ p k := by
refine ⟨fun hk => ?_, fun hk => subset_span by simpa⟩
    contrapose hk
    exact b.linearInd

中文:
引理 induction_on_cartanMatrix
  结论: [P.是既约] [P.是不可约]
  证明: by
  let q : Submodule R M := span R (P.root ∘ (↑) '' {i | p i})
have hq₀ : q != ⊥ := q.ne_bot_iff.mpr ⟨P.root i, subset_span by simpa, P.ne_zero i⟩
  have hq_mem (k : b.support) : P.root k in q ↔ p k := by
refine ⟨fun hk => ?_, fun hk => subset_span by simpa⟩
    contrapose hk
    exact b.linearInd

Depends on / 依赖: LinearMap, LinearMap.ker, LinearMap.mem_ker.mpr, P.coroot, P.ne_zero, P.root, Submodule, b.linearIndepOn_root.linearIndependent.notMem_span_image, b.support, contrapose, coroot, hq_mem, hq_notMem, linearIndepOn_root, linearIndependent, mem_ker, ne_bot_iff, ne_zero, notMem_span_image, q.ne_bot_iff.mpr
-/
lemma induction_on_cartanMatrix [P.IsReduced] [P.IsIrreducible]
    (p : b.support -> Prop) {i j : b.support} (hi : p i)
    (hp : forall i j, p i -> b.cartanMatrix j i != 0 -> p j) :
    p j := by
  let q : Submodule R M := span R (P.root ∘ (↑) '' {i | p i})
have hq₀ : q != ⊥ := q.ne_bot_iff.mpr ⟨P.root i, subset_span by simpa, P.ne_zero i⟩
  have hq_mem (k : b.support) : P.root k in q ↔ p k := by
refine ⟨fun hk => ?_, fun hk => subset_span by simpa⟩
    contrapose hk
    exact b.linearIndepOn_root.linearIndependent.notMem_span_image hk
  have hq_notMem (k : b.support) (hk : P.root k ∉ q) : q <= LinearMap.ker (P.coroot' k) := by
    refine fun x hx => LinearMap.mem_ker.mpr ?_
    contrapose! hk
    rw [hq_mem]
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨l, hl, rfl⟩ : exists l : b.support, p l ∧ P.root l = x := by simp_all
      replace hk : b.cartanMatrix k l != 0 := by
        rwa [ne_eq, cartanMatrix_apply_eq_zero_iff_symm, cartanMatrix_apply_eq_zero_iff_pairing]
      tauto
    | zero => simp_all
    | add x y hx hy hx' hy' =>
      replace hk : P.coroot' k x != 0 ∨ P.coroot' k y != 0 := by by_contra! contra; simp_all
      tauto
    | smul a x hx hx' => simp_all
  have hq : forall k, q in invtSubmodule (P.reflection k) := by
    rw [← b.forall_mem_support_invtSubmodule_iff]
    refine fun k hkb => (mem_invtSubmodule _).mpr fun x hx => ?_
    rw [Submodule.mem_comap]; rw [LinearEquiv.coe_coe]; rw [reflection_apply]
    apply q.sub_mem hx
    by_cases hk : P.root k in q
    · exact q.smul_mem _ hk
    · replace hk : P.coroot' k x = 0 := hq_notMem ⟨k, hkb⟩ hk hx
      simp [hk]
  simp [← hq_mem, IsIrreducible.eq_top_of_invtSubmodule_reflection q hq hq₀]

-- TODO Derive from `LinearIndependent.injective`
set_option backward.isDefEq.respectTransparency.types false in
open scoped Matrix in
/--
lemma `injective_pairingIn` / 引理 `injective_pairingIn`

English:
lemma injective_pairingIn
  statement: {P : RootPairing ι R M N} [P.IsRootSystem] [P.IsCrystallographic]
  proof: by
  classical
  intro i j hij
  obtain ⟨f, -, -, hf⟩ := b.exists_root_eq_sum_int i
  obtain ⟨g, -, -, hg⟩ := b.exists_root_eq_sum_int j
  let f' : b.support -> Int := f ∘ (↑)
  let g' : b.support -> Int := g ∘ (↑)
  suffices f' = g' by
    rw [← P.root.apply_eq_iff_eq]; rw [hf]; rw [hg]
    refine 

中文:
引理 injective_pairingIn
  结论: {P : RootPairing ι R M N} [P.是RootSystem] [P.IsCrystallographic]
  证明: by
  classical
  intro i j hij
  obtain ⟨f, -, -, hf⟩ := b.exists_root_eq_sum_int i
  obtain ⟨g, -, -, hg⟩ := b.exists_root_eq_sum_int j
  let f' : b.support -> Int := f ∘ (↑)
  let g' : b.support -> Int := g ∘ (↑)
  suffices f' = g' by
    rw [← P.root.apply_eq_iff_eq]; rw [hf]; rw [hg]
    refine 

Depends on / 依赖: Finset, Finset.sum_congr, P.pairingIn, P.root.apply_eq_iff_eq, apply_eq_iff_eq, b.cartanMatrix, b.exists_root_eq_sum_int, b.support, cartanMatrix, classical, congr_fun, exists_root_eq_sum_int, pairingIn, replace, sum_congr, support
-/
lemma injective_pairingIn {P : RootPairing ι R M N} [P.IsRootSystem] [P.IsCrystallographic]
    (b : P.Base) :
    Injective (fun i (k : b.support) => P.pairingIn Int i k) := by
  classical
  intro i j hij
  obtain ⟨f, -, -, hf⟩ := b.exists_root_eq_sum_int i
  obtain ⟨g, -, -, hg⟩ := b.exists_root_eq_sum_int j
  let f' : b.support -> Int := f ∘ (↑)
  let g' : b.support -> Int := g ∘ (↑)
  suffices f' = g' by
    rw [← P.root.apply_eq_iff_eq]; rw [hf]; rw [hg]
    refine Finset.sum_congr rfl fun k hk => ?_
    replace this : f k = g k := congr_fun this ⟨k, hk⟩
    rw [this]
  replace hf : (fun k : b.support => P.pairingIn Int i k) = f' ᵥ* b.cartanMatrix := by
    suffices forall k, P.pairingIn Int i k = ∑ l in b.support, f l * P.pairingIn Int l k by
      ext; simp [f', this, cartanMatrixIn, Matrix.vecMul_eq_sum, b.support.sum_subtype (by tauto)]
    refine fun k => algebraMap_injective Int R ?_
    simp_rw [algebraMap_pairingIn, map_sum, map_mul, algebraMap_pairingIn,
      ← P.root_coroot'_eq_pairing]
    simp [hf]
  replace hg : (fun k : b.support => P.pairingIn Int j k) = g' ᵥ* b.cartanMatrix := by
    suffices forall k, P.pairingIn Int j k = ∑ l in b.support, g l * P.pairingIn Int l k by
      ext; simp [g', this, cartanMatrixIn, Matrix.vecMul_eq_sum, b.support.sum_subtype (by tauto)]
    refine fun k => algebraMap_injective Int R ?_
    simp_rw [algebraMap_pairingIn, map_sum, map_mul, algebraMap_pairingIn,
      ← P.root_coroot'_eq_pairing]
    simp [hg]
suffices Injective fun v => v ᵥ* b.cartanMatrix from this by simpa [← hf, ← hg]
  rw [Matrix.vecMul_injective_iff]
  apply Matrix.linearIndependent_rows_of_det_ne_zero
  rw [← Matrix.nondegenerate_iff_det_ne_zero]
  exact b.cartanMatrix_nondegenerate

/--
lemma `exists_mem_span_pairingIn_ne_zero_and_pairwise_ne` / 引理 `exists_mem_span_pairingIn_ne_zero_and_pairwise_ne`

English:
lemma exists_mem_span_pairingIn_ne_zero_and_pairwise_ne
  proof: by
  set p := span K (range fun (i : b.support) j => (P.pairingIn Int j i : K))
  let f : ι oplus {(i, j) : ι × ι | i != j} -> Module.Dual K (ι -> K) := Sum.elim
    LinearMap.proj (fun x => LinearMap.proj (R := K) (φ := fun _ => K) x.1.1 - LinearMap.proj x.1.2)
  suffices exists d in p, forall i, f

中文:
引理 存在_mem_span_pairingIn_ne_zero_and_pairwise_ne
  证明: by
  set p := span K (range fun (i : b.support) j => (P.pairingIn Int j i : K))
  let f : ι oplus {(i, j) : ι × ι | i != j} -> Module.Dual K (ι -> K) := Sum.elim
    LinearMap.proj (fun x => LinearMap.proj (R := K) (φ := fun _ => K) x.1.1 - LinearMap.proj x.1.2)
  suffices exists d in p, forall i, f

Depends on / 依赖: LinearMap, LinearMap.proj, Module, Module.Dual, Module.Dual.exists_forall_mem_ne_zero_of_forall_exist, P.pairingIn, Sum.elim, Sum.inl, Sum.inr, b.support, exists_forall_mem_ne_zero_of_forall_exist, pairingIn, sub_eq_zero, support
-/
lemma exists_mem_span_pairingIn_ne_zero_and_pairwise_ne
    {K : Type*} [Field K] [CharZero K] [Module K M] [Module K N]
    {P : RootPairing ι K M N} [P.IsRootSystem] [P.IsCrystallographic] (b : P.Base) :
    exists d in span K (range fun (i : b.support) j => (P.pairingIn Int j i : K)),
      (forall i, d i != 0) ∧ Pairwise ((· != ·) on d) := by
  set p := span K (range fun (i : b.support) j => (P.pairingIn Int j i : K))
  let f : ι oplus {(i, j) : ι × ι | i != j} -> Module.Dual K (ι -> K) := Sum.elim
    LinearMap.proj (fun x => LinearMap.proj (R := K) (φ := fun _ => K) x.1.1 - LinearMap.proj x.1.2)
  suffices exists d in p, forall i, f i d != 0 by
    obtain ⟨d, hp, hf⟩ := this
    refine ⟨d, hp, fun i => hf (Sum.inl i), fun i j h => ?_⟩
    simpa [f, sub_eq_zero] using hf (Sum.inr ⟨⟨i, j⟩, h⟩)
  apply Module.Dual.exists_forall_mem_ne_zero_of_forall_exists p f
  rintro (i | ⟨⟨i, j⟩, h : i != j⟩)
  · obtain ⟨j, hj, hj₀⟩ := b.exists_mem_support_pos_pairingIn_ne_zero i
    refine ⟨fun i => P.pairingIn Int i j, subset_span ⟨⟨j, hj⟩, rfl⟩, ?_⟩
    rw [ne_eq]; rw [P.pairingIn_eq_zero_iff] at hj₀
    simpa [f, ne_eq, Int.cast_eq_zero]
  · obtain ⟨k, hk, hk'⟩ : exists k in b.support, P.pairingIn Int i k != P.pairingIn Int j k := by
      contrapose! h
      apply b.injective_pairingIn
      aesop
    simpa [f, sub_eq_zero] using ⟨fun i => P.pairingIn Int i k, subset_span ⟨⟨k, hk⟩, rfl⟩, by simpa⟩

section Uniqueness

variable {ι₂ M₂ N₂ : Type*} [AddCommGroup M₂] [Module R M₂] [AddCommGroup N₂] [Module R N₂]
  {P : RootPairing ι R M N} [P.IsRootSystem] [P.IsCrystallographic] [P.IsReduced] (b : P.Base)
  {P₂ : RootPairing ι₂ R M₂ N₂} [P₂.IsCrystallographic] (b₂ : P₂.Base)
  (e : b.support ≃ b₂.support)

/--
lemma `apply_mem_range_root_of_cartanMatrixEq` / 引理 `apply_mem_range_root_of_cartanMatrixEq`

English:
lemma apply_mem_range_root_of_cartanMatrixEq
  proof: by
  have (k : b.support) : (P.reflection k).trans f = f.trans (P₂.reflection (e k)) := by
    suffices forall j : b.support,
        (P.reflection k).trans f (P.root j) = f.trans (P₂.reflection (e k)) (P.root j) by
      rw [← LinearEquiv.toLinearMap_inj]
      exact b.toWeightBasis.ext fun j => by

中文:
引理 apply_mem_range_root_of_cartanMatrixEq
  证明: by
  have (k : b.support) : (P.reflection k).trans f = f.trans (P₂.reflection (e k)) := by
    suffices forall j : b.support,
        (P.reflection k).trans f (P.root j) = f.trans (P₂.reflection (e k)) (P.root j) by
      rw [← LinearEquiv.toLinearMap_inj]
      exact b.toWeightBasis.ext fun j => by

Depends on / 依赖: LinearEquiv, LinearEquiv.toLinearMap_inj, P.pairing, P.reflection, P.root, algebraMap, algebraMap_pairingIn, b.support, b.toWeightBasis.ext, cartanMatrixIn_def, congr_arg, f.trans, pairing, reflection, reflection_apply, support, toLinearMap_inj, toWeightBasis
-/
lemma apply_mem_range_root_of_cartanMatrixEq
    (f : M ≃ₗ[R] M₂) (hf : forall i : b.support, f (P.root i) = P₂.root (e i))
    (m : M) (hm : m in range P.root)
    (he : forall i j, b₂.cartanMatrix (e i) (e j) = b.cartanMatrix i j) :
    f m in range P₂.root := by
  have (k : b.support) : (P.reflection k).trans f = f.trans (P₂.reflection (e k)) := by
    suffices forall j : b.support,
        (P.reflection k).trans f (P.root j) = f.trans (P₂.reflection (e k)) (P.root j) by
      rw [← LinearEquiv.toLinearMap_inj]
      exact b.toWeightBasis.ext fun j => by simpa using this j
    intro j
    suffices P₂.pairing (e j) (e k) = P.pairing j k by simp [reflection_apply, hf, this]
    simpa only [cartanMatrixIn_def, algebraMap_pairingIn] using congr_arg (algebraMap Int R) (he j k)
  obtain ⟨i, rfl⟩ := hm
  apply b.induction_reflect i
  · exact fun j ⟨k, hk⟩ => ⟨P₂.reflectionPerm k k, by simpa⟩
  · exact fun j hj => ⟨e ⟨j, hj⟩, (hf _).symm⟩
  · intro j k ⟨l, hl⟩ hk
    replace this : f (P.reflection k (P.root j)) = (P₂.reflection (e ⟨k, hk⟩)) (f (P.root j)) := by
      simpa using LinearEquiv.congr_fun (this ⟨k, hk⟩) (P.root j)
    rw [root_reflectionPerm]; rw [this]; rw [← hl]; rw [← root_reflectionPerm]
    exact mem_range_self _

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `equivOfCartanMatrixEq` / `equivOfCartanMatrixEq` 的定义

English:
definition equivOfCartanMatrixEq
  signature: [Finite ι₂] [P₂.IsRootSystem] [P₂.IsReduced]
  body: let f : M ≃ₗ[R] M₂ := b.toWeightBasis.equiv b₂.toWeightBasis e
  have hf : forall m, f m in range P₂.root ↔ m in range P.root := by
    refine fun m => ⟨fun h => ?_, fun h => ?_⟩
    · simpa using apply_mem_range_root_of_cartanMatrixEq _ b e.symm f.symm
        (by simp [f, Module.Basis.equiv]) (f m

中文:
定义 equivOfCartanMatrixEq
  签名: [有限 ι₂] [P₂.是RootSystem] [P₂.是既约]
  定义体: let f : M ≃ₗ[R] M₂ := b.toWeightBasis.equiv b₂.toWeightBasis e
  have hf : forall m, f m in range P₂.root ↔ m in range P.root := by
    refine fun m => ⟨fun h => ?_, fun h => ?_⟩
    · simpa using apply_mem_range_root_of_cartanMatrixEq _ b e.symm f.symm
        (by simp [f, Module.Basis.equiv]) (f m

Depends on / 依赖: Decidab, Fintype, Fintype.ofFinite, Module, Module.Basis.equiv, P.root, apply_mem_range_root_of_cartanMatrixEq, b.toWeightBasis.equiv, e.symm, f.symm, ofFinite, toWeightBasis
-/
def equivOfCartanMatrixEq [Finite ι₂] [P₂.IsRootSystem] [P₂.IsReduced]
    (he : forall i j, b₂.cartanMatrix (e i) (e j) = b.cartanMatrix i j) :
    P.Equiv P₂ :=
  let f : M ≃ₗ[R] M₂ := b.toWeightBasis.equiv b₂.toWeightBasis e
  have hf : forall m, f m in range P₂.root ↔ m in range P.root := by
    refine fun m => ⟨fun h => ?_, fun h => ?_⟩
    · simpa using apply_mem_range_root_of_cartanMatrixEq _ b e.symm f.symm
        (by simp [f, Module.Basis.equiv]) (f m) h (by simp [(he _ _).symm])
    · exact apply_mem_range_root_of_cartanMatrixEq b b₂ e f (by simp [f, Module.Basis.equiv]) m h he
  let : Fintype ι := Fintype.ofFinite _
  let : Fintype ι₂ := Fintype.ofFinite _
  have : DecidableEq M := Classical.typeDecidableEq M
  have : DecidableEq M₂ := Classical.typeDecidableEq M₂
let e' : ι ≃ ι₂ := P.root.toEquivRange.trans (f.bijOn hf).equiv.trans P₂.root.toEquivRange.symm
  have he' (i : ι) : f (P.root i) = P₂.root (e' i) := by
    simp [f, e', BijOn.equiv, Embedding.toEquivRange]
  have : Module.IsReflexive R M₂ := .of_isPerfPair P₂.toLinearMap
  Equiv.mk' P P₂ (b.toWeightBasis.equiv b₂.toWeightBasis e) e' he'

end Uniqueness

end IsCrystallographic

end RootPairing.Base
