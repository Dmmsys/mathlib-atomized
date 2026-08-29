/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Algebra.Polynomial.Eval.SMul
public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.RingTheory.MatrixPolynomialAlgebra
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Characteristic polynomials and the Cayley-Hamilton theorem

We define characteristic polynomials of matrices and
prove the Cayley–Hamilton theorem over arbitrary commutative rings.

See the file `Mathlib/LinearAlgebra/Matrix/Charpoly/Coeff.lean` for corollaries of this theorem.

## Main definitions

* `Matrix.charpoly` is the characteristic polynomial of a matrix.

## Implementation details

We follow a nice proof from http://drorbn.net/AcademicPensieve/2015-12/CayleyHamilton.pdf
-/

@[expose] public section

noncomputable section

universe u v w

namespace Matrix

open Finset Matrix Polynomial

variable {R S : Type*} [CommRing R] [CommRing S]
variable {m n : Type*} [DecidableEq m] [DecidableEq n] [Fintype m] [Fintype n]
variable (M₁₁ : Matrix m m R) (M₁₂ : Matrix m n R) (M₂₁ : Matrix n m R) (M₂₂ M : Matrix n n R)
variable (i j : n)


/--
Definition of `charmatrix` / `charmatrix` 的定义

English:
definition charmatrix
  signature: (M : Matrix n n R)
  body: Matrix.scalar n (X : R[X]) - (C : R ->+* R[X]).mapMatrix M

中文:
定义 charmatrix
  签名: (M : Matrix n n R)
  定义体: Matrix.scalar n (X : R[X]) - (C : R ->+* R[X]).mapMatrix M

Depends on / 依赖: Matrix, Matrix.scalar, mapMatrix, scalar
-/
def charmatrix (M : Matrix n n R) : Matrix n n R[X] :=
  Matrix.scalar n (X : R[X]) - (C : R ->+* R[X]).mapMatrix M

/--
theorem `charmatrix_apply` / 定理 `charmatrix_apply`

English:
theorem charmatrix_apply
  proof: rfl

@[simp]

中文:
定理 charmatrix_apply
  证明: rfl

@[simp]
-/
theorem charmatrix_apply :
    charmatrix M i j = (Matrix.diagonal fun _ : n => X) i j - C (M i j) :=
  rfl

@[simp]
/--
theorem `charmatrix_apply_eq` / 定理 `charmatrix_apply_eq`

English:
theorem charmatrix_apply_eq
  statement: charmatrix M i i = (X : R[X]) - C (M i i)
  proof: by
  simp only [charmatrix, RingHom.mapMatrix_apply, sub_apply, scalar_apply, map_apply,
    diagonal_apply_eq]

@[simp]

中文:
定理 charmatrix_apply_eq
  结论: charmatrix M i i = (X : R[X]) - C (M i i)
  证明: by
  simp only [charmatrix, RingHom.mapMatrix_apply, sub_apply, scalar_apply, map_apply,
    diagonal_apply_eq]

@[simp]

Depends on / 依赖: RingHom, RingHom.mapMatrix_apply, charmatrix, diagonal_apply_eq, mapMatrix_apply, map_apply, scalar_apply, sub_apply
-/
theorem charmatrix_apply_eq : charmatrix M i i = (X : R[X]) - C (M i i) := by
  simp only [charmatrix, RingHom.mapMatrix_apply, sub_apply, scalar_apply, map_apply,
    diagonal_apply_eq]

@[simp]
/--
theorem `charmatrix_apply_ne` / 定理 `charmatrix_apply_ne`

English:
theorem charmatrix_apply_ne
  given: (h : i != j)
  statement: charmatrix M i j = -C (M i j)
  proof: by
  simp only [charmatrix, RingHom.mapMatrix_apply, sub_apply, scalar_apply, diagonal_apply_ne _ h,
    map_apply, sub_eq_neg_self]

@[simp]

中文:
定理 charmatrix_apply_ne
  条件: (h : i != j)
  结论: charmatrix M i j = -C (M i j)
  证明: by
  simp only [charmatrix, RingHom.mapMatrix_apply, sub_apply, scalar_apply, diagonal_apply_ne _ h,
    map_apply, sub_eq_neg_self]

@[simp]

Depends on / 依赖: RingHom, RingHom.mapMatrix_apply, charmatrix, diagonal_apply_ne, mapMatrix_apply, map_apply, scalar_apply, sub_apply, sub_eq_neg_self
-/
theorem charmatrix_apply_ne (h : i != j) : charmatrix M i j = -C (M i j) := by
  simp only [charmatrix, RingHom.mapMatrix_apply, sub_apply, scalar_apply, diagonal_apply_ne _ h,
    map_apply, sub_eq_neg_self]

@[simp]
/--
theorem `charmatrix_zero` / 定理 `charmatrix_zero`

English:
theorem charmatrix_zero
  statement: charmatrix (0 : Matrix n n R) = Matrix.scalar n (X : R[X])
  proof: by
  simp [charmatrix]

@[simp]

中文:
定理 charmatrix_zero
  结论: charmatrix (0 : Matrix n n R) = Matrix.scalar n (X : R[X])
  证明: by
  simp [charmatrix]

@[simp]

Depends on / 依赖: charmatrix
-/
theorem charmatrix_zero : charmatrix (0 : Matrix n n R) = Matrix.scalar n (X : R[X]) := by
  simp [charmatrix]

@[simp]
/--
theorem `charmatrix_diagonal` / 定理 `charmatrix_diagonal`

English:
theorem charmatrix_diagonal
  given: (d : n -> R)
  proof: by
  rw [charmatrix]; rw [scalar_apply]; rw [RingHom.mapMatrix_apply]; rw [diagonal_map (map_zero _)]; rw [diagonal_sub]

@[simp]

中文:
定理 charmatrix_diagonal
  条件: (d : n -> R)
  证明: by
  rw [charmatrix]; rw [scalar_apply]; rw [RingHom.mapMatrix_apply]; rw [diagonal_map (map_zero _)]; rw [diagonal_sub]

@[simp]

Depends on / 依赖: RingHom, RingHom.mapMatrix_apply, charmatrix, diagonal_map, diagonal_sub, mapMatrix_apply, map_zero, scalar_apply
-/
theorem charmatrix_diagonal (d : n -> R) :
    charmatrix (diagonal d) = diagonal fun i => X - C (d i) := by
  rw [charmatrix]; rw [scalar_apply]; rw [RingHom.mapMatrix_apply]; rw [diagonal_map (map_zero _)]; rw [diagonal_sub]

@[simp]
/--
theorem `charmatrix_one` / 定理 `charmatrix_one`

English:
theorem charmatrix_one
  statement: charmatrix (1 : Matrix n n R) = diagonal fun _ => X - 1
  proof: charmatrix_diagonal _

@[simp]

中文:
定理 charmatrix_one
  结论: charmatrix (1 : Matrix n n R) = diagonal fun _ => X - 1
  证明: charmatrix_diagonal _

@[simp]

Depends on / 依赖: charmatrix_diagonal
-/
theorem charmatrix_one : charmatrix (1 : Matrix n n R) = diagonal fun _ => X - 1 :=
  charmatrix_diagonal _

@[simp]
/--
theorem `charmatrix_natCast` / 定理 `charmatrix_natCast`

English:
theorem charmatrix_natCast
  given: (k : Nat)
  proof: charmatrix_diagonal _

@[simp]

中文:
定理 charmatrix_natCast
  条件: (k : 自然数)
  证明: charmatrix_diagonal _

@[simp]

Depends on / 依赖: charmatrix_diagonal
-/
theorem charmatrix_natCast (k : Nat) :
    charmatrix (k : Matrix n n R) = diagonal fun _ => X - (k : R[X]) :=
  charmatrix_diagonal _

@[simp]
/--
theorem `charmatrix_ofNat` / 定理 `charmatrix_ofNat`

English:
theorem charmatrix_ofNat
  given: (k : Nat) [k.AtLeastTwo]
  proof: charmatrix_natCast _

@[simp]

中文:
定理 charmatrix_ofNat
  条件: (k : 自然数) [k.AtLeastTwo]
  证明: charmatrix_natCast _

@[simp]

Depends on / 依赖: charmatrix_natCast
-/
theorem charmatrix_ofNat (k : Nat) [k.AtLeastTwo] :
    charmatrix (ofNat(k) : Matrix n n R) = diagonal fun _ => X - ofNat(k) :=
  charmatrix_natCast _

@[simp]
/--
theorem `charmatrix_transpose` / 定理 `charmatrix_transpose`

English:
theorem charmatrix_transpose
  given: (M : Matrix n n R)
  statement: (Mᵀ).charmatrix = M.charmatrixᵀ
  proof: by
  simp [charmatrix, transpose_map]

中文:
定理 charmatrix_transpose
  条件: (M : Matrix n n R)
  结论: (Mᵀ).charmatrix = M.charmatrixᵀ
  证明: by
  simp [charmatrix, transpose_map]

Depends on / 依赖: charmatrix, transpose_map
-/
theorem charmatrix_transpose (M : Matrix n n R) : (Mᵀ).charmatrix = M.charmatrixᵀ := by
  simp [charmatrix, transpose_map]

/--
theorem `matPolyEquiv_charmatrix` / 定理 `matPolyEquiv_charmatrix`

English:
theorem matPolyEquiv_charmatrix
  statement: matPolyEquiv (charmatrix M) = X - C M
  proof: by
  ext k i j
  simp only [matPolyEquiv_coeff_apply, coeff_sub]
  by_cases h : i = j
  · subst h
    rw [charmatrix_apply_eq]; rw [coeff_sub]
    simp only [coeff_X, coeff_C]
    split_ifs <;> simp
  · rw [charmatrix_apply_ne _ _ _ h, coeff_X, coeff_neg, coeff_C, coeff_C]
    split_ifs <;> simp [h]

中文:
定理 matPolyEquiv_charmatrix
  结论: matPolyEquiv (charmatrix M) = X - C M
  证明: by
  ext k i j
  simp only [matPolyEquiv_coeff_apply, coeff_sub]
  by_cases h : i = j
  · subst h
    rw [charmatrix_apply_eq]; rw [coeff_sub]
    simp only [coeff_X, coeff_C]
    split_ifs <;> simp
  · rw [charmatrix_apply_ne _ _ _ h, coeff_X, coeff_neg, coeff_C, coeff_C]
    split_ifs <;> simp [h]

Depends on / 依赖: charmatrix_apply_eq, charmatrix_apply_ne, coeff_C, coeff_X, coeff_neg, coeff_sub, matPolyEquiv_coeff_apply, split_ifs
-/
theorem matPolyEquiv_charmatrix : matPolyEquiv (charmatrix M) = X - C M := by
  ext k i j
  simp only [matPolyEquiv_coeff_apply, coeff_sub]
  by_cases h : i = j
  · subst h
    rw [charmatrix_apply_eq]; rw [coeff_sub]
    simp only [coeff_X, coeff_C]
    split_ifs <;> simp
  · rw [charmatrix_apply_ne _ _ _ h, coeff_X, coeff_neg, coeff_C, coeff_C]
    split_ifs <;> simp [h]

/--
theorem `charmatrix_reindex` / 定理 `charmatrix_reindex`

English:
theorem charmatrix_reindex
  given: (e : n ≃ m)
  proof: by
  ext i j x
  by_cases h : i = j
  all_goals simp [h]

中文:
定理 charmatrix_reindex
  条件: (e : n ≃ m)
  证明: by
  ext i j x
  by_cases h : i = j
  all_goals simp [h]

Depends on / 依赖: all_goals
-/
theorem charmatrix_reindex (e : n ≃ m) :
    charmatrix (reindex e e M) = reindex e e (charmatrix M) := by
  ext i j x
  by_cases h : i = j
  all_goals simp [h]

/--
lemma `charmatrix_map` / 引理 `charmatrix_map`

English:
lemma charmatrix_map
  given: (M : Matrix n n R) (f : R ->+* S)
  proof: by
  ext i j
  by_cases h : i = j <;> simp [h, charmatrix, diagonal]

中文:
引理 charmatrix_map
  条件: (M : Matrix n n R) (f : R ->+* S)
  证明: by
  ext i j
  by_cases h : i = j <;> simp [h, charmatrix, diagonal]

Depends on / 依赖: charmatrix, diagonal
-/
lemma charmatrix_map (M : Matrix n n R) (f : R ->+* S) :
    charmatrix (M.map f) = (charmatrix M).map (Polynomial.map f) := by
  ext i j
  by_cases h : i = j <;> simp [h, charmatrix, diagonal]

/--
lemma `charmatrix_fromBlocks` / 引理 `charmatrix_fromBlocks`

English:
lemma charmatrix_fromBlocks
  proof: by
  simp only [charmatrix]
  ext (i | i) (j | j) : 2 <;> simp [diagonal]

中文:
引理 charmatrix_fromBlocks
  证明: by
  simp only [charmatrix]
  ext (i | i) (j | j) : 2 <;> simp [diagonal]

Depends on / 依赖: charmatrix, diagonal
-/
lemma charmatrix_fromBlocks :
    charmatrix (fromBlocks M₁₁ M₁₂ M₂₁ M₂₂) =
      fromBlocks (charmatrix M₁₁) (- M₁₂.map C) (- M₂₁.map C) (charmatrix M₂₂) := by
  simp only [charmatrix]
  ext (i | i) (j | j) : 2 <;> simp [diagonal]

-- TODO: importing block triangular here is somewhat expensive, if more lemmas about it are added
-- to this file, it may be worth extracting things out to Charpoly/Block.lean
@[simp]
/--
lemma `charmatrix_blockTriangular_iff` / 引理 `charmatrix_blockTriangular_iff`

English:
lemma charmatrix_blockTriangular_iff
  given: {α : Type*} [Preorder α] {M : Matrix n n R} {b : n -> α}
  proof: by
  rw [charmatrix]; rw [scalar_apply]; rw [RingHom.mapMatrix_apply]; rw [(blockTriangular_diagonal _).sub_iff_right]
  simp [BlockTriangular]

alias ⟨BlockTriangular.of_charmatrix, BlockTriangular.charmatrix⟩ := charmatrix_blockTriangular_iff

中文:
引理 charmatrix_blockTriangular_iff
  条件: {α : 类型} [Preorder α] {M : Matrix n n R} {b : n -> α}
  证明: by
  rw [charmatrix]; rw [scalar_apply]; rw [RingHom.mapMatrix_apply]; rw [(blockTriangular_diagonal _).sub_iff_right]
  simp [BlockTriangular]

alias ⟨BlockTriangular.of_charmatrix, BlockTriangular.charmatrix⟩ := charmatrix_blockTriangular_iff

Depends on / 依赖: BlockTriangular, RingHom, RingHom.mapMatrix_apply, blockTriangular_diagonal, charmatrix, mapMatrix_apply, scalar_apply, sub_iff_right
-/
lemma charmatrix_blockTriangular_iff {α : Type*} [Preorder α] {M : Matrix n n R} {b : n -> α} :
    M.charmatrix.BlockTriangular b ↔ M.BlockTriangular b := by
  rw [charmatrix]; rw [scalar_apply]; rw [RingHom.mapMatrix_apply]; rw [(blockTriangular_diagonal _).sub_iff_right]
  simp [BlockTriangular]

alias ⟨BlockTriangular.of_charmatrix, BlockTriangular.charmatrix⟩ := charmatrix_blockTriangular_iff

/-- The characteristic polynomial of a matrix `M` is given by $\det (t I - M)$. -/
@[wikidata Q849705]
/--
Definition of `charpoly` / `charpoly` 的定义

English:
definition charpoly
  signature: (M : Matrix n n R)
  body: (charmatrix M).det

中文:
定义 charpoly
  签名: (M : Matrix n n R)
  定义体: (charmatrix M).det

Depends on / 依赖: charmatrix
-/
def charpoly (M : Matrix n n R) : R[X] :=
  (charmatrix M).det

/--
theorem `eval_charpoly` / 定理 `eval_charpoly`

English:
theorem eval_charpoly
  given: (M : Matrix m m R) (t : R)
  proof: by
  rw [Matrix.charpoly]; rw [← Polynomial.coe_evalRingHom]; rw [RingHom.map_det]; rw [Matrix.charmatrix]
  congr
  ext i j
  obtain rfl | hij := eq_or_ne i j <;> simp [*]

@[simp]

中文:
定理 eval_charpoly
  条件: (M : Matrix m m R) (t : R)
  证明: by
  rw [Matrix.charpoly]; rw [← Polynomial.coe_evalRingHom]; rw [RingHom.map_det]; rw [Matrix.charmatrix]
  congr
  ext i j
  obtain rfl | hij := eq_or_ne i j <;> simp [*]

@[simp]

Depends on / 依赖: Matrix, Matrix.charmatrix, Matrix.charpoly, Polynomial, Polynomial.coe_evalRingHom, RingHom, RingHom.map_det, charmatrix, charpoly, coe_evalRingHom, eq_or_ne, map_det
-/
theorem eval_charpoly (M : Matrix m m R) (t : R) :
    M.charpoly.eval t = (Matrix.scalar _ t - M).det := by
  rw [Matrix.charpoly]; rw [← Polynomial.coe_evalRingHom]; rw [RingHom.map_det]; rw [Matrix.charmatrix]
  congr
  ext i j
  obtain rfl | hij := eq_or_ne i j <;> simp [*]

@[simp]
/--
theorem `charpoly_isEmpty` / 定理 `charpoly_isEmpty`

English:
theorem charpoly_isEmpty
  given: [IsEmpty n] {A : Matrix n n R}
  statement: charpoly A = 1
  proof: by
  simp [charpoly]

@[simp]

中文:
定理 charpoly_isEmpty
  条件: [IsEmpty n] {A : Matrix n n R}
  结论: charpoly A = 1
  证明: by
  simp [charpoly]

@[simp]

Depends on / 依赖: charpoly
-/
theorem charpoly_isEmpty [IsEmpty n] {A : Matrix n n R} : charpoly A = 1 := by
  simp [charpoly]

@[simp]
/--
theorem `charpoly_zero` / 定理 `charpoly_zero`

English:
theorem charpoly_zero
  statement: charpoly (0 : Matrix n n R) = X ^ Fintype.card n
  proof: by
  simp [charpoly]

中文:
定理 charpoly_zero
  结论: charpoly (0 : Matrix n n R) = X ^ Fintype.card n
  证明: by
  simp [charpoly]

Depends on / 依赖: charpoly
-/
theorem charpoly_zero : charpoly (0 : Matrix n n R) = X ^ Fintype.card n := by
  simp [charpoly]

/--
theorem `charpoly_diagonal` / 定理 `charpoly_diagonal`

English:
theorem charpoly_diagonal
  given: (d : n -> R)
  statement: charpoly (diagonal d) = ∏ i, (X - C (d i))
  proof: by
  simp [charpoly]

中文:
定理 charpoly_diagonal
  条件: (d : n -> R)
  结论: charpoly (diagonal d) = ∏ i, (X - C (d i))
  证明: by
  simp [charpoly]

Depends on / 依赖: charpoly
-/
theorem charpoly_diagonal (d : n -> R) : charpoly (diagonal d) = ∏ i, (X - C (d i)) := by
  simp [charpoly]

/--
theorem `charpoly_one` / 定理 `charpoly_one`

English:
theorem charpoly_one
  statement: charpoly (1 : Matrix n n R) = (X - 1) ^ Fintype.card n
  proof: by
  simp [charpoly]

中文:
定理 charpoly_one
  结论: charpoly (1 : Matrix n n R) = (X - 1) ^ Fintype.card n
  证明: by
  simp [charpoly]

Depends on / 依赖: charpoly
-/
theorem charpoly_one : charpoly (1 : Matrix n n R) = (X - 1) ^ Fintype.card n := by
  simp [charpoly]

/--
theorem `charpoly_natCast` / 定理 `charpoly_natCast`

English:
theorem charpoly_natCast
  given: (k : Nat)
  proof: by
  simp [charpoly]

中文:
定理 charpoly_natCast
  条件: (k : 自然数)
  证明: by
  simp [charpoly]

Depends on / 依赖: charpoly
-/
theorem charpoly_natCast (k : Nat) :
    charpoly (k : Matrix n n R) = (X - (k : R[X])) ^ Fintype.card n := by
  simp [charpoly]

/--
theorem `charpoly_ofNat` / 定理 `charpoly_ofNat`

English:
theorem charpoly_ofNat
  given: (k : Nat) [k.AtLeastTwo]
  proof: charpoly_natCast _

@[simp]

中文:
定理 charpoly_ofNat
  条件: (k : 自然数) [k.AtLeastTwo]
  证明: charpoly_natCast _

@[simp]

Depends on / 依赖: charpoly_natCast
-/
theorem charpoly_ofNat (k : Nat) [k.AtLeastTwo] :
    charpoly (ofNat(k) : Matrix n n R) = (X - ofNat(k)) ^ Fintype.card n :=
  charpoly_natCast _

@[simp]
/--
theorem `charpoly_transpose` / 定理 `charpoly_transpose`

English:
theorem charpoly_transpose
  given: (M : Matrix n n R)
  statement: (Mᵀ).charpoly = M.charpoly
  proof: by
  simp [charpoly]

中文:
定理 charpoly_transpose
  条件: (M : Matrix n n R)
  结论: (Mᵀ).charpoly = M.charpoly
  证明: by
  simp [charpoly]

Depends on / 依赖: charpoly
-/
theorem charpoly_transpose (M : Matrix n n R) : (Mᵀ).charpoly = M.charpoly := by
  simp [charpoly]

/--
theorem `charpoly_reindex` / 定理 `charpoly_reindex`

English:
theorem charpoly_reindex
  statement: (e : n ≃ m)
  proof: by
  unfold Matrix.charpoly
  rw [charmatrix_reindex]; rw [Matrix.det_reindex_self]

中文:
定理 charpoly_reindex
  结论: (e : n ≃ m)
  证明: by
  unfold Matrix.charpoly
  rw [charmatrix_reindex]; rw [Matrix.det_reindex_self]

Depends on / 依赖: Matrix, Matrix.charpoly, Matrix.det_reindex_self, charmatrix_reindex, charpoly, det_reindex_self
-/
theorem charpoly_reindex (e : n ≃ m)
    (M : Matrix n n R) : (reindex e e M).charpoly = M.charpoly := by
  unfold Matrix.charpoly
  rw [charmatrix_reindex]; rw [Matrix.det_reindex_self]

/--
lemma `charpoly_map` / 引理 `charpoly_map`

English:
lemma charpoly_map
  given: (M : Matrix n n R) (f : R ->+* S)
  proof: by
  rw [charpoly]; rw [charmatrix_map]; rw [← Polynomial.coe_mapRingHom]; rw [charpoly]; rw [RingHom.map_det]; rw [RingHom.mapMatrix_apply]

@[simp]

中文:
引理 charpoly_map
  条件: (M : Matrix n n R) (f : R ->+* S)
  证明: by
  rw [charpoly]; rw [charmatrix_map]; rw [← Polynomial.coe_mapRingHom]; rw [charpoly]; rw [RingHom.map_det]; rw [RingHom.mapMatrix_apply]

@[simp]

Depends on / 依赖: Polynomial, Polynomial.coe_mapRingHom, RingHom, RingHom.mapMatrix_apply, RingHom.map_det, charmatrix_map, charpoly, coe_mapRingHom, mapMatrix_apply, map_det
-/
lemma charpoly_map (M : Matrix n n R) (f : R ->+* S) :
    (M.map f).charpoly = M.charpoly.map f := by
  rw [charpoly]; rw [charmatrix_map]; rw [← Polynomial.coe_mapRingHom]; rw [charpoly]; rw [RingHom.map_det]; rw [RingHom.mapMatrix_apply]

@[simp]
/--
lemma `charpoly_fromBlocks_zero₁₂` / 引理 `charpoly_fromBlocks_zero₁₂`

English:
lemma charpoly_fromBlocks_zero₁₂
  proof: by
  simp only [charpoly, charmatrix_fromBlocks, Matrix.map_zero _ (Polynomial.C_0), neg_zero,
    det_fromBlocks_zero₁₂]

@[simp]

中文:
引理 charpoly_fromBlocks_zero₁₂
  证明: by
  simp only [charpoly, charmatrix_fromBlocks, Matrix.map_zero _ (Polynomial.C_0), neg_zero,
    det_fromBlocks_zero₁₂]

@[simp]

Depends on / 依赖: Matrix, Matrix.map_zero, Polynomial, Polynomial.C_0, charmatrix_fromBlocks, charpoly, map_zero, neg_zero
-/
lemma charpoly_fromBlocks_zero₁₂ :
    (fromBlocks M₁₁ 0 M₂₁ M₂₂).charpoly = (M₁₁.charpoly * M₂₂.charpoly) := by
  simp only [charpoly, charmatrix_fromBlocks, Matrix.map_zero _ (Polynomial.C_0), neg_zero,
    det_fromBlocks_zero₁₂]

@[simp]
/--
lemma `charpoly_fromBlocks_zero₂₁` / 引理 `charpoly_fromBlocks_zero₂₁`

English:
lemma charpoly_fromBlocks_zero₂₁
  proof: by
  simp only [charpoly, charmatrix_fromBlocks, Matrix.map_zero _ (Polynomial.C_0), neg_zero,
    det_fromBlocks_zero₂₁]

中文:
引理 charpoly_fromBlocks_zero₂₁
  证明: by
  simp only [charpoly, charmatrix_fromBlocks, Matrix.map_zero _ (Polynomial.C_0), neg_zero,
    det_fromBlocks_zero₂₁]

Depends on / 依赖: Matrix, Matrix.map_zero, Polynomial, Polynomial.C_0, charmatrix_fromBlocks, charpoly, map_zero, neg_zero
-/
lemma charpoly_fromBlocks_zero₂₁ :
    (fromBlocks M₁₁ M₁₂ 0 M₂₂).charpoly = (M₁₁.charpoly * M₂₂.charpoly) := by
  simp only [charpoly, charmatrix_fromBlocks, Matrix.map_zero _ (Polynomial.C_0), neg_zero,
    det_fromBlocks_zero₂₁]

/--
lemma `charmatrix_toSquareBlock` / 引理 `charmatrix_toSquareBlock`

English:
lemma charmatrix_toSquareBlock
  given: {α : Type*} [DecidableEq α] {b : n -> α} {a : α}
  proof: by
  ext i j : 1
  simp [charmatrix_apply, toSquareBlock_def, diagonal_apply, Subtype.ext_iff]

中文:
引理 charmatrix_toSquareBlock
  条件: {α : 类型} [DecidableEq α] {b : n -> α} {a : α}
  证明: by
  ext i j : 1
  simp [charmatrix_apply, toSquareBlock_def, diagonal_apply, Subtype.ext_iff]

Depends on / 依赖: Subtype, Subtype.ext_iff, charmatrix_apply, diagonal_apply, ext_iff, toSquareBlock_def
-/
lemma charmatrix_toSquareBlock {α : Type*} [DecidableEq α] {b : n -> α} {a : α} :
    (M.toSquareBlock b a).charmatrix = M.charmatrix.toSquareBlock b a := by
  ext i j : 1
  simp [charmatrix_apply, toSquareBlock_def, diagonal_apply, Subtype.ext_iff]

/--
lemma `BlockTriangular.charpoly` / 引理 `BlockTriangular.charpoly`

English:
lemma BlockTriangular.charpoly
  given: {α : Type*} {b : n -> α} [LinearOrder α] (h : M.BlockTriangular b)
  proof: by
  simp only [Matrix.charpoly, h.charmatrix.det, charmatrix_toSquareBlock]

中文:
引理 BlockTriangular.charpoly
  条件: {α : 类型} {b : n -> α} [LinearOrder α] (h : M.BlockTriangular b)
  证明: by
  simp only [Matrix.charpoly, h.charmatrix.det, charmatrix_toSquareBlock]

Depends on / 依赖: Matrix, Matrix.charpoly, charmatrix, charmatrix_toSquareBlock, charpoly, h.charmatrix.det
-/
lemma BlockTriangular.charpoly {α : Type*} {b : n -> α} [LinearOrder α] (h : M.BlockTriangular b) :
    M.charpoly = ∏ a in image b univ, (M.toSquareBlock b a).charpoly := by
  simp only [Matrix.charpoly, h.charmatrix.det, charmatrix_toSquareBlock]

/--
lemma `charpoly_of_isUpperTriangular` / 引理 `charpoly_of_isUpperTriangular`

English:
lemma charpoly_of_isUpperTriangular
  given: [LinearOrder n] (M : Matrix n n R) (h : M.IsUpperTriangular)
  proof: by
  simp [charpoly, det_of_isUpperTriangular h.charmatrix]

@[deprecated (since := "2026-07-30")]
alias charpoly_of_upperTriangular := charpoly_of_isUpperTriangular

中文:
引理 charpoly_of_isUpperTriangular
  条件: [LinearOrder n] (M : Matrix n n R) (h : M.IsUpperTriangular)
  证明: by
  simp [charpoly, det_of_isUpperTriangular h.charmatrix]

@[deprecated (since := "2026-07-30")]
alias charpoly_of_upperTriangular := charpoly_of_isUpperTriangular

Depends on / 依赖: charmatrix, charpoly, det_of_isUpperTriangular, h.charmatrix
-/
lemma charpoly_of_isUpperTriangular [LinearOrder n] (M : Matrix n n R) (h : M.IsUpperTriangular) :
    M.charpoly = ∏ i : n, (X - C (M i i)) := by
  simp [charpoly, det_of_isUpperTriangular h.charmatrix]

@[deprecated (since := "2026-07-30")]
alias charpoly_of_upperTriangular := charpoly_of_isUpperTriangular

-- This proof follows http://drorbn.net/AcademicPensieve/2015-12/CayleyHamilton.pdf
/--
theorem `aeval_self_charpoly` / 定理 `aeval_self_charpoly`

English:
theorem aeval_self_charpoly
  given: (M : Matrix n n R)
  statement: aeval M M.charpoly = 0
  proof: by
  -- We begin with the fact $χ_M(t) I = adjugate (t I - M) * (t I - M)$,
  -- as an identity in `Matrix n n R[X]`.
  have h : M.charpoly • (1 : Matrix n n R[X]) = adjugate (charmatrix M) * charmatrix M :=
    (adjugate_mul _).symm
  -- Using the algebra isomorphism `Matrix n n R[X] ≃ₐ[R] Polynomi

中文:
定理 aeval_self_charpoly
  条件: (M : Matrix n n R)
  结论: aeval M M.charpoly = 0
  证明: by
  -- We begin with the fact $χ_M(t) I = adjugate (t I - M) * (t I - M)$,
  -- as an identity in `Matrix n n R[X]`.
  have h : M.charpoly • (1 : Matrix n n R[X]) = adjugate (charmatrix M) * charmatrix M :=
    (adjugate_mul _).symm
  -- Using the algebra isomorphism `Matrix n n R[X] ≃ₐ[R] Polynomi
-/
theorem aeval_self_charpoly (M : Matrix n n R) : aeval M M.charpoly = 0 := by
  -- We begin with the fact $χ_M(t) I = adjugate (t I - M) * (t I - M)$,
  -- as an identity in `Matrix n n R[X]`.
  have h : M.charpoly • (1 : Matrix n n R[X]) = adjugate (charmatrix M) * charmatrix M :=
    (adjugate_mul _).symm
  -- Using the algebra isomorphism `Matrix n n R[X] ≃ₐ[R] Polynomial (Matrix n n R)`,
  -- we have the same identity in `Polynomial (Matrix n n R)`.
  apply_fun matPolyEquiv at h
  simp only [map_mul, matPolyEquiv_charmatrix] at h
  -- Because the coefficient ring `Matrix n n R` is non-commutative,
  -- evaluation at `M` is not multiplicative.
  -- However, any polynomial which is a product of the form $N * (t I - M)$
  -- is sent to zero, because the evaluation function puts the polynomial variable
  -- to the right of any coefficients, so everything telescopes.
  apply_fun fun p => p.eval M at h
  rw [eval_mul_X_sub_C] at h
  -- Now $χ_M (t) I$, when thought of as a polynomial of matrices
  -- and evaluated at some `N` is exactly $χ_M (N)$.
  rw [matPolyEquiv_smul_one]; rw [eval_map] at h
  -- Thus we have $χ_M(M) = 0$, which is the desired result.
  exact h

set_option backward.defeqAttrib.useBackward true in
/--
theorem `charpoly_mul_comm'` / 定理 `charpoly_mul_comm'`

English:
theorem charpoly_mul_comm'
  given: (A : Matrix m n R) (B : Matrix n m R)
  proof: by
  -- This proof follows https://math.stackexchange.com/a/311362/315369
  let M := fromBlocks (scalar m X) (A.map C) (B.map C) (1 : Matrix n n R[X])
  let N := fromBlocks (-1 : Matrix m m R[X]) 0 (B.map C) (-scalar n X)
  have hMN :
      M * N = fromBlocks (-scalar m X + (A * B).map C) (-(X : R[X

中文:
定理 charpoly_mul_comm'
  条件: (A : Matrix m n R) (B : Matrix n m R)
  证明: by
  -- This proof follows https://math.stackexchange.com/a/311362/315369
  let M := fromBlocks (scalar m X) (A.map C) (B.map C) (1 : Matrix n n R[X])
  let N := fromBlocks (-1 : Matrix m m R[X]) 0 (B.map C) (-scalar n X)
  have hMN :
      M * N = fromBlocks (-scalar m X + (A * B).map C) (-(X : R[X
-/
theorem charpoly_mul_comm' (A : Matrix m n R) (B : Matrix n m R) :
    X ^ Fintype.card n * (A * B).charpoly = X ^ Fintype.card m * (B * A).charpoly := by
  -- This proof follows https://math.stackexchange.com/a/311362/315369
  let M := fromBlocks (scalar m X) (A.map C) (B.map C) (1 : Matrix n n R[X])
  let N := fromBlocks (-1 : Matrix m m R[X]) 0 (B.map C) (-scalar n X)
  have hMN :
      M * N = fromBlocks (-scalar m X + (A * B).map C) (-(X : R[X]) • A.map C) 0 (-scalar n X) := by
    simp [M, N, fromBlocks_multiply, smul_eq_mul_diagonal, -diagonal_neg]
  have hNM : N * M = fromBlocks (-scalar m X) (-A.map C) 0 ((B * A).map C - scalar n X) := by
    simp [M, N, fromBlocks_multiply, sub_eq_add_neg, -scalar_apply, scalar_comm, Commute.all]
  have hdet_MN : (M * N).det = (-1 : R[X]) ^ (Fintype.card m + Fintype.card n) *
      (X ^ Fintype.card n * (scalar m X - (A * B).map C).det) := by
    rw [hMN]; rw [det_fromBlocks_zero₂₁]; rw [neg_add_eq_sub]; rw [← neg_sub]; rw [det_neg]
    simp
    ring
  have hdet_NM : (N * M).det = (-1 : R[X]) ^ (Fintype.card m + Fintype.card n) *
      (X ^ Fintype.card m * (scalar n X - (B * A).map C).det) := by
    rw [hNM]; rw [det_fromBlocks_zero₂₁]; rw [← neg_sub]; rw [det_neg (_ - _)]
    simp
    ring
  dsimp only [charpoly, charmatrix, RingHom.mapMatrix_apply]
  rw [← (isUnit_neg_one.pow _).isRegular.left.eq_iff]; rw [← hdet_NM]; rw [← hdet_MN]; rw [det_mul_comm]

/--
theorem `charpoly_mul_comm_of_le` / 定理 `charpoly_mul_comm_of_le`

English:
theorem charpoly_mul_comm_of_le
  proof: by
  rw [← (isRegular_X_pow _).left.eq_iff]; rw [← mul_assoc]; rw [← pow_add]; rw [Nat.add_sub_cancel' hle]; rw [charpoly_mul_comm']

中文:
定理 charpoly_mul_comm_of_le
  证明: by
  rw [← (isRegular_X_pow _).left.eq_iff]; rw [← mul_assoc]; rw [← pow_add]; rw [Nat.add_sub_cancel' hle]; rw [charpoly_mul_comm']

Depends on / 依赖: Nat.add_sub_cancel, add_sub_cancel, charpoly_mul_comm, eq_iff, isRegular_X_pow, left.eq_iff, mul_assoc, pow_add
-/
theorem charpoly_mul_comm_of_le
    (A : Matrix m n R) (B : Matrix n m R) (hle : Fintype.card n <= Fintype.card m) :
    (A * B).charpoly = X ^ (Fintype.card m - Fintype.card n) * (B * A).charpoly := by
  rw [← (isRegular_X_pow _).left.eq_iff]; rw [← mul_assoc]; rw [← pow_add]; rw [Nat.add_sub_cancel' hle]; rw [charpoly_mul_comm']

/--
theorem `charpoly_mul_comm` / 定理 `charpoly_mul_comm`

English:
theorem charpoly_mul_comm
  given: (A B : Matrix n n R)
  statement: (A * B).charpoly = (B * A).charpoly
  proof: (isRegular_X_pow _).left.eq_iff.mp charpoly_mul_comm' A B

中文:
定理 charpoly_mul_comm
  条件: (A B : Matrix n n R)
  结论: (A * B).charpoly = (B * A).charpoly
  证明: (isRegular_X_pow _).left.eq_iff.mp charpoly_mul_comm' A B

Depends on / 依赖: charpoly_mul_comm, eq_iff, isRegular_X_pow, left.eq_iff.mp
-/
theorem charpoly_mul_comm (A B : Matrix n n R) : (A * B).charpoly = (B * A).charpoly :=
(isRegular_X_pow _).left.eq_iff.mp charpoly_mul_comm' A B

/--
theorem `charpoly_vecMulVec` / 定理 `charpoly_vecMulVec`

English:
theorem charpoly_vecMulVec
  given: (u v : n -> R)
  proof: by
  cases isEmpty_or_nonempty n
  · simp
  · have h : 1 <= Fintype.card n := NeZero.one_le
    rw [vecMulVec_eq (ι := Unit)]; rw [charpoly_mul_comm_of_le (n := Unit) _ _ h]; rw [charpoly]; rw [charmatrix]
    simp [-Matrix.map_mul, mul_sub, ← pow_succ, h, dotProduct_comm, smul_eq_C_mul]

@[simp]

中文:
定理 charpoly_vecMulVec
  条件: (u v : n -> R)
  证明: by
  cases isEmpty_or_nonempty n
  · simp
  · have h : 1 <= Fintype.card n := NeZero.one_le
    rw [vecMulVec_eq (ι := Unit)]; rw [charpoly_mul_comm_of_le (n := Unit) _ _ h]; rw [charpoly]; rw [charmatrix]
    simp [-Matrix.map_mul, mul_sub, ← pow_succ, h, dotProduct_comm, smul_eq_C_mul]

@[simp]

Depends on / 依赖: Fintype, Fintype.card, Matrix, Matrix.map_mul, NeZero, NeZero.one_le, charmatrix, charpoly, charpoly_mul_comm_of_le, dotProduct_comm, isEmpty_or_nonempty, map_mul, mul_sub, one_le, pow_succ, smul_eq_C_mul, vecMulVec_eq
-/
theorem charpoly_vecMulVec (u v : n -> R) :
    (vecMulVec u v).charpoly = X ^ Fintype.card n - (u ⬝ᵥ v) • X ^ (Fintype.card n - 1) := by
  cases isEmpty_or_nonempty n
  · simp
  · have h : 1 <= Fintype.card n := NeZero.one_le
    rw [vecMulVec_eq (ι := Unit)]; rw [charpoly_mul_comm_of_le (n := Unit) _ _ h]; rw [charpoly]; rw [charmatrix]
    simp [-Matrix.map_mul, mul_sub, ← pow_succ, h, dotProduct_comm, smul_eq_C_mul]

@[simp]
/--
theorem `charpoly_units_conj` / 定理 `charpoly_units_conj`

English:
theorem charpoly_units_conj
  given: (M : (Matrix n n R)ˣ) (N : Matrix n n R)
  proof: by
  rw [Matrix.charpoly_mul_comm]; rw [← mul_assoc]
  simp

@[simp]

中文:
定理 charpoly_units_conj
  条件: (M : (Matrix n n R)ˣ) (N : Matrix n n R)
  证明: by
  rw [Matrix.charpoly_mul_comm]; rw [← mul_assoc]
  simp

@[simp]

Depends on / 依赖: Matrix, Matrix.charpoly_mul_comm, charpoly_mul_comm, mul_assoc
-/
theorem charpoly_units_conj (M : (Matrix n n R)ˣ) (N : Matrix n n R) :
    (M.val * N * M.val⁻¹).charpoly = N.charpoly := by
  rw [Matrix.charpoly_mul_comm]; rw [← mul_assoc]
  simp

@[simp]
/--
theorem `charpoly_units_conj'` / 定理 `charpoly_units_conj'`

English:
theorem charpoly_units_conj'
  given: (M : (Matrix n n R)ˣ) (N : Matrix n n R)
  proof: by
  simpa using charpoly_units_conj M⁻¹ N

中文:
定理 charpoly_units_conj'
  条件: (M : (Matrix n n R)ˣ) (N : Matrix n n R)
  证明: by
  simpa using charpoly_units_conj M⁻¹ N

Depends on / 依赖: charpoly_units_conj
-/
theorem charpoly_units_conj' (M : (Matrix n n R)ˣ) (N : Matrix n n R) :
    (M.val⁻¹ * N * M.val).charpoly = N.charpoly := by
  simpa using charpoly_units_conj M⁻¹ N

set_option backward.isDefEq.respectTransparency false in
/--
theorem `charpoly_sub_scalar` / 定理 `charpoly_sub_scalar`

English:
theorem charpoly_sub_scalar
  given: (M : Matrix n n R) (μ : R)
  proof: by
  simp_rw [charpoly, det_apply, Polynomial.sum_comp, Polynomial.smul_comp, Polynomial.prod_comp]
  congr! with σ _ i _
  by_cases hi : σ i = i <;> simp [hi]
  ring

中文:
定理 charpoly_sub_scalar
  条件: (M : Matrix n n R) (μ : R)
  证明: by
  simp_rw [charpoly, det_apply, Polynomial.sum_comp, Polynomial.smul_comp, Polynomial.prod_comp]
  congr! with σ _ i _
  by_cases hi : σ i = i <;> simp [hi]
  ring

Depends on / 依赖: Polynomial, Polynomial.prod_comp, Polynomial.smul_comp, Polynomial.sum_comp, charpoly, det_apply, prod_comp, simp_rw, smul_comp, sum_comp
-/
theorem charpoly_sub_scalar (M : Matrix n n R) (μ : R) :
    (M - scalar n μ).charpoly = M.charpoly.comp (X + C μ) := by
  simp_rw [charpoly, det_apply, Polynomial.sum_comp, Polynomial.smul_comp, Polynomial.prod_comp]
  congr! with σ _ i _
  by_cases hi : σ i = i <;> simp [hi]
  ring

end Matrix
