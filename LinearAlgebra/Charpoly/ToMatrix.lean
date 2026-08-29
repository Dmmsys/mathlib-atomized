/-
Copyright (c) 2021 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/
module

public import Mathlib.LinearAlgebra.Charpoly.Basic
public import Mathlib.LinearAlgebra.Matrix.Basis
public import Mathlib.RingTheory.Finiteness.Prod

/-!

# Characteristic polynomial

## Main result

* `LinearMap.charpoly_toMatrix f` : `charpoly f` is the characteristic polynomial of the matrix
  of `f` in any basis.

-/

public section

noncomputable section

open Module Free Polynomial Matrix

universe u v w

variable {R M M₁ M₂ : Type*} [CommRing R]
variable [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M]
variable [AddCommGroup M₁] [Module R M₁] [Module.Finite R M₁] [Module.Free R M₁]
variable [AddCommGroup M₂] [Module R M₂] [Module.Finite R M₂] [Module.Free R M₂]
variable (f : M ->ₗ[R] M)

namespace LinearMap

section Basic

/-- `charpoly f` is the characteristic polynomial of the matrix of `f` in any basis. -/
@[simp]
/--
theorem `charpoly_toMatrix` / 定理 `charpoly_toMatrix`

English:
theorem charpoly_toMatrix
  given: {ι : Type w} [DecidableEq ι] [Fintype ι] (b : Basis ι R M)
  proof: by
  nontriviality R
  unfold LinearMap.charpoly
  set b' := chooseBasis R M
  rw [← basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix b b' b b']
  set P := b.toMatrix b'
  set A := toMatrix b' b' f
  set Q := b'.toMatrix b
  let e := Basis.indexEquiv b b'
  let ι' := ChooseBasisIndex R M
  l

中文:
定理 charpoly_toMatrix
  条件: {ι : 类型 w} [DecidableEq ι] [有限类型 ι] (b : 基 ι R M)
  证明: by
  nontriviality R
  unfold LinearMap.charpoly
  set b' := chooseBasis R M
  rw [← basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix b b' b b']
  set P := b.toMatrix b'
  set A := toMatrix b' b' f
  set Q := b'.toMatrix b
  let e := Basis.indexEquiv b b'
  let ι' := ChooseBasisIndex R M
  l

Depends on / 依赖: Basis.indexEquiv, ChooseBasisIndex, Equiv.refl, LinearMap, LinearMap.charpoly, b.toMatrix, basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix, charpoly, chooseBasis, indexEquiv, nontriviality, reindexLinearEquiv, toMatrix
-/
theorem charpoly_toMatrix {ι : Type w} [DecidableEq ι] [Fintype ι] (b : Basis ι R M) :
    (toMatrix b b f).charpoly = f.charpoly := by
  nontriviality R
  unfold LinearMap.charpoly
  set b' := chooseBasis R M
  rw [← basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix b b' b b']
  set P := b.toMatrix b'
  set A := toMatrix b' b' f
  set Q := b'.toMatrix b
  let e := Basis.indexEquiv b b'
  let ι' := ChooseBasisIndex R M
  let φ := reindexLinearEquiv R R e e
  let φ₁ := reindexLinearEquiv R R e (Equiv.refl ι')
  let φ₂ := reindexLinearEquiv R R (Equiv.refl ι') (Equiv.refl ι')
  let φ₃ := reindexLinearEquiv R R (Equiv.refl ι') e
  calc
    (P * A * Q).charpoly = (φ (P * A * Q)).charpoly := (charpoly_reindex ..).symm
    _ = (φ₁ P * φ₂ A * φ₃ Q).charpoly := by rw [reindexLinearEquiv_mul, reindexLinearEquiv_mul]
    _ = A.charpoly := by rw [charpoly_mul_comm, ← mul_assoc]; simp [P, Q, φ₁, φ₂, φ₃]

/--
lemma `charpoly_prodMap` / 引理 `charpoly_prodMap`

English:
lemma charpoly_prodMap
  given: (f₁ : M₁ ->ₗ[R] M₁) (f₂ : M₂ ->ₗ[R] M₂)
  proof: by
  let b₁ := chooseBasis R M₁
  let b₂ := chooseBasis R M₂
  let b := b₁.prod b₂
  rw [← charpoly_toMatrix f₁ b₁]; rw [← charpoly_toMatrix f₂ b₂]; rw [← charpoly_toMatrix (f₁.prodMap f₂) b]; rw [toMatrix_prodMap b₁ b₂ f₁ f₂]; rw [Matrix.charpoly_fromBlocks_zero₁₂]

中文:
引理 charpoly_prodMap
  条件: (f₁ : M₁ ->ₗ[R] M₁) (f₂ : M₂ ->ₗ[R] M₂)
  证明: by
  let b₁ := chooseBasis R M₁
  let b₂ := chooseBasis R M₂
  let b := b₁.prod b₂
  rw [← charpoly_toMatrix f₁ b₁]; rw [← charpoly_toMatrix f₂ b₂]; rw [← charpoly_toMatrix (f₁.prodMap f₂) b]; rw [toMatrix_prodMap b₁ b₂ f₁ f₂]; rw [Matrix.charpoly_fromBlocks_zero₁₂]

Depends on / 依赖: Matrix, Matrix.charpoly_fromBlocks_zero, charpoly_toMatrix, chooseBasis, prodMap, toMatrix_prodMap
-/
lemma charpoly_prodMap (f₁ : M₁ ->ₗ[R] M₁) (f₂ : M₂ ->ₗ[R] M₂) :
    (f₁.prodMap f₂).charpoly = f₁.charpoly * f₂.charpoly := by
  let b₁ := chooseBasis R M₁
  let b₂ := chooseBasis R M₂
  let b := b₁.prod b₂
  rw [← charpoly_toMatrix f₁ b₁]; rw [← charpoly_toMatrix f₂ b₂]; rw [← charpoly_toMatrix (f₁.prodMap f₂) b]; rw [toMatrix_prodMap b₁ b₂ f₁ f₂]; rw [Matrix.charpoly_fromBlocks_zero₁₂]

end Basic

end LinearMap

@[simp]
/--
lemma `LinearEquiv.charpoly_conj` / 引理 `LinearEquiv.charpoly_conj`

English:
lemma LinearEquiv.charpoly_conj
  given: (e : M₁ ≃ₗ[R] M₂) (φ : Module.End R M₁)
  proof: by
  let b := chooseBasis R M₁
  rw [← LinearMap.charpoly_toMatrix φ b]; rw [← LinearMap.charpoly_toMatrix (e.conj φ) (b.map e)]
  congr 1
  ext i j : 1
  simp [LinearMap.toMatrix]

中文:
引理 线性等价.charpoly_conj
  条件: (e : M₁ ≃ₗ[R] M₂) (φ : 模.End R M₁)
  证明: by
  let b := chooseBasis R M₁
  rw [← LinearMap.charpoly_toMatrix φ b]; rw [← LinearMap.charpoly_toMatrix (e.conj φ) (b.map e)]
  congr 1
  ext i j : 1
  simp [LinearMap.toMatrix]

Depends on / 依赖: LinearMap, LinearMap.charpoly_toMatrix, LinearMap.toMatrix, b.map, charpoly_toMatrix, chooseBasis, e.conj, toMatrix
-/
lemma LinearEquiv.charpoly_conj (e : M₁ ≃ₗ[R] M₂) (φ : Module.End R M₁) :
    (e.conj φ).charpoly = φ.charpoly := by
  let b := chooseBasis R M₁
  rw [← LinearMap.charpoly_toMatrix φ b]; rw [← LinearMap.charpoly_toMatrix (e.conj φ) (b.map e)]
  congr 1
  ext i j : 1
  simp [LinearMap.toMatrix]

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

@[simp]
/--
theorem `charpoly_toLin` / 定理 `charpoly_toLin`

English:
theorem charpoly_toLin
  given: (A : Matrix n n R) (b : Basis n R M)
  proof: by
  simp [← LinearMap.charpoly_toMatrix (A.toLin b b) b]

@[simp]

中文:
定理 charpoly_toLin
  条件: (A : 矩阵 n n R) (b : 基 n R M)
  证明: by
  simp [← LinearMap.charpoly_toMatrix (A.toLin b b) b]

@[simp]

Depends on / 依赖: A.toLin, LinearMap, LinearMap.charpoly_toMatrix, charpoly_toMatrix
-/
theorem charpoly_toLin (A : Matrix n n R) (b : Basis n R M) :
    (A.toLin b b).charpoly = A.charpoly := by
  simp [← LinearMap.charpoly_toMatrix (A.toLin b b) b]

@[simp]
/--
theorem `charpoly_toLin'` / 定理 `charpoly_toLin'`

English:
theorem charpoly_toLin'
  given: (A : Matrix n n R)
  statement: A.toLin'.charpoly = A.charpoly
  proof: by
  rw [← Matrix.toLin_eq_toLin']; rw [charpoly_toLin]

@[simp]

中文:
定理 charpoly_toLin'
  条件: (A : 矩阵 n n R)
  结论: A.toLin'.charpoly = A.charpoly
  证明: by
  rw [← Matrix.toLin_eq_toLin']; rw [charpoly_toLin]

@[simp]

Depends on / 依赖: Matrix, Matrix.toLin_eq_toLin, charpoly_toLin, toLin_eq_toLin
-/
theorem charpoly_toLin' (A : Matrix n n R) : A.toLin'.charpoly = A.charpoly := by
  rw [← Matrix.toLin_eq_toLin']; rw [charpoly_toLin]

@[simp]
/--
theorem `charpoly_mulVecLin` / 定理 `charpoly_mulVecLin`

English:
theorem charpoly_mulVecLin
  given: (A : Matrix n n R)
  statement: A.mulVecLin.charpoly = A.charpoly
  proof: charpoly_toLin' A

中文:
定理 charpoly_mulVecLin
  条件: (A : 矩阵 n n R)
  结论: A.mulVecLin.charpoly = A.charpoly
  证明: charpoly_toLin' A

Depends on / 依赖: charpoly_toLin
-/
theorem charpoly_mulVecLin (A : Matrix n n R) : A.mulVecLin.charpoly = A.charpoly :=
  charpoly_toLin' A

end Matrix
