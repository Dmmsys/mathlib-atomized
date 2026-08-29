/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.LinearAlgebra.Charpoly.ToMatrix
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.RingTheory.TensorProduct.Finite
public import Mathlib.LinearAlgebra.TensorProduct.Tower


/-! # The characteristic polynomial of base change -/

public section

variable {R M} [CommRing R] [AddCommGroup M] [Module R M]
    [Module.Free R M] [Module.Finite R M] (f : M ->ₗ[R] M)
    (A) [CommRing A] [Algebra R A]

@[simp]
/--
lemma `LinearMap.charpoly_baseChange` / 引理 `LinearMap.charpoly_baseChange`

English:
lemma LinearMap.charpoly_baseChange
  proof: by
  nontriviality A
  have := (algebraMap R A).domain_nontrivial
  let I := Module.Free.ChooseBasisIndex R M
  let b : Module.Basis I R M := Module.Free.chooseBasis R M
  rw [← f.charpoly_toMatrix b]; rw [← (f.baseChange A).charpoly_toMatrix (b.baseChange A)]; rw [← Matrix.charpoly_map]
  congr 1
  ext i j
  simp [LinearMap.toMatrix_apply, ← Algebra.algebraMap_eq_smul_one]

中文:
引理 线性映射.charpoly_baseChange
  证明: by
  nontriviality A
  have := (algebraMap R A).domain_nontrivial
  let I := Module.Free.ChooseBasisIndex R M
  let b : Module.Basis I R M := Module.Free.chooseBasis R M
  rw [← f.charpoly_toMatrix b]; rw [← (f.baseChange A).charpoly_toMatrix (b.baseChange A)]; rw [← Matrix.charpoly_map]
  congr 1
  ext i j
  simp [LinearMap.toMatrix_apply, ← Algebra.algebraMap_eq_smul_one]

Depends on / 依赖: Algebra, Algebra.algebraMap_eq_smul_one, ChooseBasisIndex, LinearMap, LinearMap.toMatrix_apply, Matrix, Matrix.charpoly_map, Module, Module.Basis, Module.Free.ChooseBasisIndex, Module.Free.chooseBasis, algebraMap, algebraMap_eq_smul_one, b.baseChange, baseChange, charpoly_map, charpoly_toMatrix, chooseBasis, domain_nontrivial, f.baseChange
-/
lemma LinearMap.charpoly_baseChange :
    (f.baseChange A).charpoly = f.charpoly.map (algebraMap R A) := by
  nontriviality A
  have := (algebraMap R A).domain_nontrivial
  let I := Module.Free.ChooseBasisIndex R M
  let b : Module.Basis I R M := Module.Free.chooseBasis R M
  rw [← f.charpoly_toMatrix b]; rw [← (f.baseChange A).charpoly_toMatrix (b.baseChange A)]; rw [← Matrix.charpoly_map]
  congr 1
  ext i j
  simp [LinearMap.toMatrix_apply, ← Algebra.algebraMap_eq_smul_one]

/--
lemma `LinearMap.det_eq_sign_charpoly_coeff` / 引理 `LinearMap.det_eq_sign_charpoly_coeff`

English:
lemma LinearMap.det_eq_sign_charpoly_coeff
  proof: by
  nontriviality R
  rw [← LinearMap.det_toMatrix (Module.Free.chooseBasis R M)]; rw [Matrix.det_eq_sign_charpoly_coeff]; rw [← Module.finrank_eq_card_chooseBasisIndex]; rw [charpoly_def]

中文:
引理 线性映射.det_eq_sign_charpoly_coeff
  证明: by
  nontriviality R
  rw [← LinearMap.det_toMatrix (Module.Free.chooseBasis R M)]; rw [Matrix.det_eq_sign_charpoly_coeff]; rw [← Module.finrank_eq_card_chooseBasisIndex]; rw [charpoly_def]

Depends on / 依赖: LinearMap, LinearMap.det_toMatrix, Matrix, Matrix.det_eq_sign_charpoly_coeff, Module, Module.Free.chooseBasis, Module.finrank_eq_card_chooseBasisIndex, charpoly_def, chooseBasis, det_eq_sign_charpoly_coeff, det_toMatrix, finrank_eq_card_chooseBasisIndex, nontriviality
-/
lemma LinearMap.det_eq_sign_charpoly_coeff :
    LinearMap.det f = (-1) ^ Module.finrank R M * f.charpoly.coeff 0 := by
  nontriviality R
  rw [← LinearMap.det_toMatrix (Module.Free.chooseBasis R M)]; rw [Matrix.det_eq_sign_charpoly_coeff]; rw [← Module.finrank_eq_card_chooseBasisIndex]; rw [charpoly_def]

variable {A} in
/--
lemma `LinearMap.det_baseChange` / 引理 `LinearMap.det_baseChange`

English:
lemma LinearMap.det_baseChange
  proof: by
  nontriviality A
  have := (algebraMap R A).domain_nontrivial
  rw [LinearMap.det_eq_sign_charpoly_coeff]; rw [LinearMap.det_eq_sign_charpoly_coeff]
  simp

中文:
引理 线性映射.det_baseChange
  证明: by
  nontriviality A
  have := (algebraMap R A).domain_nontrivial
  rw [LinearMap.det_eq_sign_charpoly_coeff]; rw [LinearMap.det_eq_sign_charpoly_coeff]
  simp

Depends on / 依赖: LinearMap, LinearMap.det_eq_sign_charpoly_coeff, algebraMap, det_eq_sign_charpoly_coeff, domain_nontrivial, nontriviality
-/
lemma LinearMap.det_baseChange :
    LinearMap.det (f.baseChange A) = algebraMap R A (LinearMap.det f) := by
  nontriviality A
  have := (algebraMap R A).domain_nontrivial
  rw [LinearMap.det_eq_sign_charpoly_coeff]; rw [LinearMap.det_eq_sign_charpoly_coeff]
  simp

/--
lemma `LinearEquiv.det_baseChange` / 引理 `LinearEquiv.det_baseChange`

English:
lemma LinearEquiv.det_baseChange
  given: (f : M ≃ₗ[R] M)
  proof: by
  ext
  simp [LinearMap.det_baseChange]

中文:
引理 线性等价.det_baseChange
  条件: (f : M ≃ₗ[R] M)
  证明: by
  ext
  simp [LinearMap.det_baseChange]

Depends on / 依赖: LinearMap, LinearMap.det_baseChange, det_baseChange
-/
lemma LinearEquiv.det_baseChange (f : M ≃ₗ[R] M) :
    LinearEquiv.det (f.baseChange R A _ _) = (LinearEquiv.det f).map (algebraMap R A) := by
  ext
  simp [LinearMap.det_baseChange]

/-! Also see `LinearMap.trace_baseChange` in `Mathlib/LinearAlgebra/Trace` -/
