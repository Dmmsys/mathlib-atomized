/-
Copyright (c) 2021 Lu-Ming Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lu-Ming Zhang
-/
module

public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Matrix.Block
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Symmetric matrices

This file contains the definition and basic results about symmetric matrices.

## Main definition

* `Matrix.isSymm`: a matrix `A : Matrix n n α` is "symmetric" if `Aᵀ = A`.

## Tags

symm, symmetric, matrix
-/

@[expose] public section


variable {α β n m R : Type*}

namespace Matrix

/-- A matrix `A : Matrix n n α` is "symmetric" if `Aᵀ = A`. -/
@[wikidata Q339011]
/--
Definition of `IsSymm` / `IsSymm` 的定义

English:
definition IsSymm
  signature: (A : Matrix n n α)
  body: Aᵀ = A

中文:
定义 是Symm
  签名: (A : 矩阵 n n α)
  定义体: Aᵀ = A
-/
def IsSymm (A : Matrix n n α) : Prop :=
  Aᵀ = A

instance (A : Matrix n n α) [Decidable (Aᵀ = A)] : Decidable (IsSymm A) :=
inferInstanceAs Decidable (_ = _)

/--
theorem `IsSymm.eq` / 定理 `IsSymm.eq`

English:
theorem IsSymm.eq
  given: {A : Matrix n n α} (h : A.IsSymm)
  statement: Aᵀ = A
  proof: h

中文:
定理 是Symm.eq
  条件: {A : 矩阵 n n α} (h : A.是Symm)
  结论: Aᵀ = A
  证明: h
-/
theorem IsSymm.eq {A : Matrix n n α} (h : A.IsSymm) : Aᵀ = A :=
  h

/--
theorem `IsSymm.ext_iff` / 定理 `IsSymm.ext_iff`

English:
theorem IsSymm.ext_iff
  given: {A : Matrix n n α}
  statement: A.IsSymm ↔ forall i j, A j i = A i j
  proof: Matrix.ext_iff.symm

中文:
定理 是Symm.ext_iff
  条件: {A : 矩阵 n n α}
  结论: A.是Symm ↔ 对任意 i j, A j i = A i j
  证明: Matrix.ext_iff.symm

Depends on / 依赖: Matrix, Matrix.ext_iff.symm, ext_iff
-/
theorem IsSymm.ext_iff {A : Matrix n n α} : A.IsSymm ↔ forall i j, A j i = A i j :=
  Matrix.ext_iff.symm

/--
theorem `IsSymm.ext` / 定理 `IsSymm.ext`

English:
theorem IsSymm.ext
  given: {A : Matrix n n α}
  statement: (forall i j, A j i = A i j) -> A.IsSymm
  proof: Matrix.ext

中文:
定理 是Symm.ext
  条件: {A : 矩阵 n n α}
  结论: (对任意 i j, A j i = A i j) -> A.是Symm
  证明: Matrix.ext

Depends on / 依赖: Matrix, Matrix.ext
-/
theorem IsSymm.ext {A : Matrix n n α} : (forall i j, A j i = A i j) -> A.IsSymm :=
  Matrix.ext

/--
theorem `IsSymm.apply` / 定理 `IsSymm.apply`

English:
theorem IsSymm.apply
  given: {A : Matrix n n α} (h : A.IsSymm) (i j : n)
  statement: A j i = A i j
  proof: IsSymm.ext_iff.1 h i j

中文:
定理 是Symm.apply
  条件: {A : 矩阵 n n α} (h : A.是Symm) (i j : n)
  结论: A j i = A i j
  证明: IsSymm.ext_iff.1 h i j

Depends on / 依赖: IsSymm, IsSymm.ext_iff, ext_iff
-/
theorem IsSymm.apply {A : Matrix n n α} (h : A.IsSymm) (i j : n) : A j i = A i j :=
  IsSymm.ext_iff.1 h i j

/--
theorem `isSymm_mul_transpose_self` / 定理 `isSymm_mul_transpose_self`

English:
theorem isSymm_mul_transpose_self
  given: [Fintype n] [NonUnitalCommSemiring α] (A : Matrix n n α)
  proof: transpose_mul _ _

中文:
定理 isSymm_mul_transpose_self
  条件: [有限类型 n] [非幺交换半环 α] (A : 矩阵 n n α)
  证明: transpose_mul _ _

Depends on / 依赖: transpose_mul
-/
theorem isSymm_mul_transpose_self [Fintype n] [NonUnitalCommSemiring α] (A : Matrix n n α) :
    (A * Aᵀ).IsSymm :=
  transpose_mul _ _

/--
theorem `isSymm_transpose_mul_self` / 定理 `isSymm_transpose_mul_self`

English:
theorem isSymm_transpose_mul_self
  given: [Fintype n] [NonUnitalCommSemiring α] (A : Matrix n n α)
  proof: transpose_mul _ _

中文:
定理 isSymm_transpose_mul_self
  条件: [有限类型 n] [非幺交换半环 α] (A : 矩阵 n n α)
  证明: transpose_mul _ _

Depends on / 依赖: transpose_mul
-/
theorem isSymm_transpose_mul_self [Fintype n] [NonUnitalCommSemiring α] (A : Matrix n n α) :
    (Aᵀ * A).IsSymm :=
  transpose_mul _ _

/--
theorem `isSymm_add_transpose_self` / 定理 `isSymm_add_transpose_self`

English:
theorem isSymm_add_transpose_self
  given: [AddCommSemigroup α] (A : Matrix n n α)
  statement: (A + Aᵀ).IsSymm
  proof: add_comm _ _

中文:
定理 isSymm_add_transpose_self
  条件: [加法交换半群 α] (A : 矩阵 n n α)
  结论: (A + Aᵀ).是Symm
  证明: add_comm _ _

Depends on / 依赖: add_comm
-/
theorem isSymm_add_transpose_self [AddCommSemigroup α] (A : Matrix n n α) : (A + Aᵀ).IsSymm :=
  add_comm _ _

/--
theorem `isSymm_transpose_add_self` / 定理 `isSymm_transpose_add_self`

English:
theorem isSymm_transpose_add_self
  given: [AddCommSemigroup α] (A : Matrix n n α)
  statement: (Aᵀ + A).IsSymm
  proof: add_comm _ _

@[simp]

中文:
定理 isSymm_transpose_add_self
  条件: [加法交换半群 α] (A : 矩阵 n n α)
  结论: (Aᵀ + A).是Symm
  证明: add_comm _ _

@[simp]

Depends on / 依赖: add_comm
-/
theorem isSymm_transpose_add_self [AddCommSemigroup α] (A : Matrix n n α) : (Aᵀ + A).IsSymm :=
  add_comm _ _

@[simp]
/--
theorem `isSymm_zero` / 定理 `isSymm_zero`

English:
theorem isSymm_zero
  given: [Zero α]
  statement: (0 : Matrix n n α).IsSymm
  proof: transpose_zero

@[simp]

中文:
定理 isSymm_zero
  条件: [零 α]
  结论: (0 : 矩阵 n n α).是Symm
  证明: transpose_zero

@[simp]

Depends on / 依赖: transpose_zero
-/
theorem isSymm_zero [Zero α] : (0 : Matrix n n α).IsSymm :=
  transpose_zero

@[simp]
/--
theorem `isSymm_one` / 定理 `isSymm_one`

English:
theorem isSymm_one
  given: [DecidableEq n] [Zero α] [One α]
  statement: (1 : Matrix n n α).IsSymm
  proof: transpose_one

中文:
定理 isSymm_one
  条件: [DecidableEq n] [零 α] [幺 α]
  结论: (1 : 矩阵 n n α).是Symm
  证明: transpose_one

Depends on / 依赖: transpose_one
-/
theorem isSymm_one [DecidableEq n] [Zero α] [One α] : (1 : Matrix n n α).IsSymm :=
  transpose_one

/--
theorem `IsSymm.pow` / 定理 `IsSymm.pow`

English:
theorem IsSymm.pow
  statement: [CommSemiring α] [Fintype n] [DecidableEq n] {A : Matrix n n α} (h : A.IsSymm)
  proof: by
  rw [IsSymm]; rw [transpose_pow]; rw [h]

@[simp]

中文:
定理 是Symm.pow
  结论: [交换半环 α] [有限类型 n] [DecidableEq n] {A : 矩阵 n n α} (h : A.是Symm)
  证明: by
  rw [IsSymm]; rw [transpose_pow]; rw [h]

@[simp]

Depends on / 依赖: IsSymm, transpose_pow
-/
theorem IsSymm.pow [CommSemiring α] [Fintype n] [DecidableEq n] {A : Matrix n n α} (h : A.IsSymm)
    (k : Nat) :
    (A ^ k).IsSymm := by
  rw [IsSymm]; rw [transpose_pow]; rw [h]

@[simp]
/--
theorem `IsSymm.map` / 定理 `IsSymm.map`

English:
theorem IsSymm.map
  given: {A : Matrix n n α} (h : A.IsSymm) (f : α -> β)
  statement: (A.map f).IsSymm
  proof: by
  rw [IsSymm]; rw [← transpose_map]; rw [h.eq]

@[simp]

中文:
定理 是Symm.map
  条件: {A : 矩阵 n n α} (h : A.是Symm) (f : α -> β)
  结论: (A.map f).是Symm
  证明: by
  rw [IsSymm]; rw [← transpose_map]; rw [h.eq]

@[simp]

Depends on / 依赖: IsSymm, h.eq, transpose_map
-/
theorem IsSymm.map {A : Matrix n n α} (h : A.IsSymm) (f : α -> β) : (A.map f).IsSymm := by
  rw [IsSymm]; rw [← transpose_map]; rw [h.eq]

@[simp]
/--
theorem `isSymm_map_iff` / 定理 `isSymm_map_iff`

English:
theorem isSymm_map_iff
  given: {A : Matrix n n α} {f : α -> β} (hf : f.Injective)
  proof: by
  rw [IsSymm]; rw [IsSymm]; rw [← transpose_map]; rw [map_injective hf |>.eq_iff]

中文:
定理 isSymm_map_iff
  条件: {A : 矩阵 n n α} {f : α -> β} (hf : f.单射)
  证明: by
  rw [IsSymm]; rw [IsSymm]; rw [← transpose_map]; rw [map_injective hf |>.eq_iff]

Depends on / 依赖: IsSymm, eq_iff, map_injective, transpose_map
-/
theorem isSymm_map_iff {A : Matrix n n α} {f : α -> β} (hf : f.Injective) :
    (A.map f).IsSymm ↔ A.IsSymm := by
  rw [IsSymm]; rw [IsSymm]; rw [← transpose_map]; rw [map_injective hf |>.eq_iff]

/--
theorem `IsSymm.transpose` / 定理 `IsSymm.transpose`

English:
theorem IsSymm.transpose
  given: {A : Matrix n n α} (h : A.IsSymm)
  statement: Aᵀ.IsSymm
  proof: congr_arg _ h

@[simp]

中文:
定理 是Symm.transpose
  条件: {A : 矩阵 n n α} (h : A.是Symm)
  结论: Aᵀ.是Symm
  证明: congr_arg _ h

@[simp]

Depends on / 依赖: congr_arg
-/
theorem IsSymm.transpose {A : Matrix n n α} (h : A.IsSymm) : Aᵀ.IsSymm :=
  congr_arg _ h

@[simp]
/--
theorem `isSymm_transpose_iff` / 定理 `isSymm_transpose_iff`

English:
theorem isSymm_transpose_iff
  given: {A : Matrix n n α}
  statement: Aᵀ.IsSymm ↔ A.IsSymm
  proof: by
  refine ⟨fun h => ?_, (·.transpose)⟩
  rw [← A.transpose_transpose]
  exact h.transpose

@[simp]

中文:
定理 isSymm_transpose_iff
  条件: {A : 矩阵 n n α}
  结论: Aᵀ.是Symm ↔ A.是Symm
  证明: by
  refine ⟨fun h => ?_, (·.transpose)⟩
  rw [← A.transpose_transpose]
  exact h.transpose

@[simp]

Depends on / 依赖: A.transpose_transpose, h.transpose, transpose, transpose_transpose
-/
theorem isSymm_transpose_iff {A : Matrix n n α} : Aᵀ.IsSymm ↔ A.IsSymm := by
  refine ⟨fun h => ?_, (·.transpose)⟩
  rw [← A.transpose_transpose]
  exact h.transpose

@[simp]
/--
theorem `IsSymm.conjTranspose` / 定理 `IsSymm.conjTranspose`

English:
theorem IsSymm.conjTranspose
  given: [Star α] {A : Matrix n n α} (h : A.IsSymm)
  statement: Aᴴ.IsSymm
  proof: h.transpose.map _

@[simp]

中文:
定理 是Symm.conjTranspose
  条件: [对合 α] {A : 矩阵 n n α} (h : A.是Symm)
  结论: Aᴴ.是Symm
  证明: h.transpose.map _

@[simp]

Depends on / 依赖: h.transpose.map, transpose
-/
theorem IsSymm.conjTranspose [Star α] {A : Matrix n n α} (h : A.IsSymm) : Aᴴ.IsSymm :=
  h.transpose.map _

@[simp]
/--
theorem `isSymm_conjTranspose_iff` / 定理 `isSymm_conjTranspose_iff`

English:
theorem isSymm_conjTranspose_iff
  given: [InvolutiveStar α] {A : Matrix n n α}
  statement: Aᴴ.IsSymm ↔ A.IsSymm
  proof: by
  refine ⟨fun h => ?_, (·.conjTranspose)⟩
  rw [← A.conjTranspose_conjTranspose]
  exact h.conjTranspose

@[simp]

中文:
定理 isSymm_conjTranspose_iff
  条件: [InvolutiveStar α] {A : 矩阵 n n α}
  结论: Aᴴ.是Symm ↔ A.是Symm
  证明: by
  refine ⟨fun h => ?_, (·.conjTranspose)⟩
  rw [← A.conjTranspose_conjTranspose]
  exact h.conjTranspose

@[simp]

Depends on / 依赖: A.conjTranspose_conjTranspose, conjTranspose, conjTranspose_conjTranspose, h.conjTranspose
-/
theorem isSymm_conjTranspose_iff [InvolutiveStar α] {A : Matrix n n α} : Aᴴ.IsSymm ↔ A.IsSymm := by
  refine ⟨fun h => ?_, (·.conjTranspose)⟩
  rw [← A.conjTranspose_conjTranspose]
  exact h.conjTranspose

@[simp]
/--
theorem `IsSymm.neg` / 定理 `IsSymm.neg`

English:
theorem IsSymm.neg
  given: [Neg α] {A : Matrix n n α} (h : A.IsSymm)
  statement: (-A).IsSymm
  proof: (transpose_neg _).trans (congr_arg _ h)

@[simp]

中文:
定理 是Symm.neg
  条件: [取负 α] {A : 矩阵 n n α} (h : A.是Symm)
  结论: (-A).是Symm
  证明: (transpose_neg _).trans (congr_arg _ h)

@[simp]

Depends on / 依赖: congr_arg, transpose_neg
-/
theorem IsSymm.neg [Neg α] {A : Matrix n n α} (h : A.IsSymm) : (-A).IsSymm :=
  (transpose_neg _).trans (congr_arg _ h)

@[simp]
/--
theorem `isSymm_neg_iff` / 定理 `isSymm_neg_iff`

English:
theorem isSymm_neg_iff
  given: [InvolutiveNeg α] {A : Matrix n n α}
  statement: (-A).IsSymm ↔ A.IsSymm
  proof: by
  refine ⟨fun h => ?_, (·.neg)⟩
  rw [← neg_neg A]
  exact h.neg

@[simp]

中文:
定理 isSymm_neg_iff
  条件: [InvolutiveNeg α] {A : 矩阵 n n α}
  结论: (-A).是Symm ↔ A.是Symm
  证明: by
  refine ⟨fun h => ?_, (·.neg)⟩
  rw [← neg_neg A]
  exact h.neg

@[simp]

Depends on / 依赖: h.neg, neg_neg
-/
theorem isSymm_neg_iff [InvolutiveNeg α] {A : Matrix n n α} : (-A).IsSymm ↔ A.IsSymm := by
  refine ⟨fun h => ?_, (·.neg)⟩
  rw [← neg_neg A]
  exact h.neg

@[simp]
/--
theorem `IsSymm.add` / 定理 `IsSymm.add`

English:
theorem IsSymm.add
  given: {A B : Matrix n n α} [Add α] (hA : A.IsSymm) (hB : B.IsSymm)
  statement: (A + B).IsSymm
  proof: (transpose_add _ _).trans (hA.symm ▸ hB.symm ▸ rfl)

@[simp]

中文:
定理 是Symm.add
  条件: {A B : 矩阵 n n α} [加法 α] (hA : A.是Symm) (hB : B.是Symm)
  结论: (A + B).是Symm
  证明: (transpose_add _ _).trans (hA.symm ▸ hB.symm ▸ rfl)

@[simp]

Depends on / 依赖: hA.symm, hB.symm, transpose_add
-/
theorem IsSymm.add {A B : Matrix n n α} [Add α] (hA : A.IsSymm) (hB : B.IsSymm) : (A + B).IsSymm :=
  (transpose_add _ _).trans (hA.symm ▸ hB.symm ▸ rfl)

@[simp]
/--
theorem `IsSymm.sub` / 定理 `IsSymm.sub`

English:
theorem IsSymm.sub
  given: {A B : Matrix n n α} [Sub α] (hA : A.IsSymm) (hB : B.IsSymm)
  statement: (A - B).IsSymm
  proof: (transpose_sub _ _).trans (hA.symm ▸ hB.symm ▸ rfl)

@[simp]

中文:
定理 是Symm.sub
  条件: {A B : 矩阵 n n α} [减法 α] (hA : A.是Symm) (hB : B.是Symm)
  结论: (A - B).是Symm
  证明: (transpose_sub _ _).trans (hA.symm ▸ hB.symm ▸ rfl)

@[simp]

Depends on / 依赖: hA.symm, hB.symm, transpose_sub
-/
theorem IsSymm.sub {A B : Matrix n n α} [Sub α] (hA : A.IsSymm) (hB : B.IsSymm) : (A - B).IsSymm :=
  (transpose_sub _ _).trans (hA.symm ▸ hB.symm ▸ rfl)

@[simp]
/--
theorem `IsSymm.smul` / 定理 `IsSymm.smul`

English:
theorem IsSymm.smul
  given: [SMul R α] {A : Matrix n n α} (h : A.IsSymm) (k : R)
  statement: (k • A).IsSymm
  proof: (transpose_smul _ _).trans (congr_arg _ h)

@[simp]

中文:
定理 是Symm.smul
  条件: [标量乘法 R α] {A : 矩阵 n n α} (h : A.是Symm) (k : R)
  结论: (k • A).是Symm
  证明: (transpose_smul _ _).trans (congr_arg _ h)

@[simp]

Depends on / 依赖: congr_arg, transpose_smul
-/
theorem IsSymm.smul [SMul R α] {A : Matrix n n α} (h : A.IsSymm) (k : R) : (k • A).IsSymm :=
  (transpose_smul _ _).trans (congr_arg _ h)

@[simp]
/--
theorem `isSymm_smul_iff` / 定理 `isSymm_smul_iff`

English:
theorem isSymm_smul_iff
  given: [Monoid R] [MulAction R α] {A : Matrix n n α} (k : R) [Invertible k]
  proof: by
  refine ⟨fun h => ?_, (·.smul k)⟩
  rw [← invOf_smul_smul k A]
  exact h.smul ⅟k

@[simp]

中文:
定理 isSymm_smul_iff
  条件: [幺半群 R] [乘法作用 R α] {A : 矩阵 n n α} (k : R) [可逆 k]
  证明: by
  refine ⟨fun h => ?_, (·.smul k)⟩
  rw [← invOf_smul_smul k A]
  exact h.smul ⅟k

@[simp]

Depends on / 依赖: h.smul, invOf_smul_smul
-/
theorem isSymm_smul_iff [Monoid R] [MulAction R α] {A : Matrix n n α} (k : R) [Invertible k] :
    (k • A).IsSymm ↔ A.IsSymm := by
  refine ⟨fun h => ?_, (·.smul k)⟩
  rw [← invOf_smul_smul k A]
  exact h.smul ⅟k

@[simp]
/--
theorem `IsSymm.submatrix` / 定理 `IsSymm.submatrix`

English:
theorem IsSymm.submatrix
  given: {A : Matrix n n α} (h : A.IsSymm) (f : m -> n)
  statement: (A.submatrix f f).IsSymm
  proof: (transpose_submatrix _ _ _).trans (h.symm ▸ rfl)

中文:
定理 是Symm.submatrix
  条件: {A : 矩阵 n n α} (h : A.是Symm) (f : m -> n)
  结论: (A.submatrix f f).是Symm
  证明: (transpose_submatrix _ _ _).trans (h.symm ▸ rfl)

Depends on / 依赖: h.symm, transpose_submatrix
-/
theorem IsSymm.submatrix {A : Matrix n n α} (h : A.IsSymm) (f : m -> n) : (A.submatrix f f).IsSymm :=
  (transpose_submatrix _ _ _).trans (h.symm ▸ rfl)

/--
theorem `IsSymm.reindex` / 定理 `IsSymm.reindex`

English:
theorem IsSymm.reindex
  given: {A : Matrix n n α} (h : A.IsSymm) (f : n ≃ m)
  statement: (A.reindex f f).IsSymm
  proof: by
  rw [reindex_apply]
  apply submatrix h

中文:
定理 是Symm.reindex
  条件: {A : 矩阵 n n α} (h : A.是Symm) (f : n ≃ m)
  结论: (A.reindex f f).是Symm
  证明: by
  rw [reindex_apply]
  apply submatrix h

Depends on / 依赖: reindex_apply, submatrix
-/
theorem IsSymm.reindex {A : Matrix n n α} (h : A.IsSymm) (f : n ≃ m) : (A.reindex f f).IsSymm := by
  rw [reindex_apply]
  apply submatrix h

/--
theorem `isSymm_reindex_iff` / 定理 `isSymm_reindex_iff`

English:
theorem isSymm_reindex_iff
  given: {A : Matrix n n α} (f : n ≃ m)
  statement: (A.reindex f f).IsSymm ↔ A.IsSymm
  proof: by
  refine ⟨fun h => ?_, (·.reindex f)⟩
  simpa using h.reindex f.symm

中文:
定理 isSymm_reindex_iff
  条件: {A : 矩阵 n n α} (f : n ≃ m)
  结论: (A.reindex f f).是Symm ↔ A.是Symm
  证明: by
  refine ⟨fun h => ?_, (·.reindex f)⟩
  simpa using h.reindex f.symm

Depends on / 依赖: f.symm, h.reindex, reindex
-/
theorem isSymm_reindex_iff {A : Matrix n n α} (f : n ≃ m) : (A.reindex f f).IsSymm ↔ A.IsSymm := by
  refine ⟨fun h => ?_, (·.reindex f)⟩
  simpa using h.reindex f.symm

/-- The diagonal matrix `diagonal v` is symmetric. -/
@[simp]
/--
theorem `isSymm_diagonal` / 定理 `isSymm_diagonal`

English:
theorem isSymm_diagonal
  given: [DecidableEq n] [Zero α] (v : n -> α)
  statement: (diagonal v).IsSymm
  proof: diagonal_transpose _

中文:
定理 isSymm_diagonal
  条件: [DecidableEq n] [零 α] (v : n -> α)
  结论: (diagonal v).是Symm
  证明: diagonal_transpose _

Depends on / 依赖: diagonal_transpose
-/
theorem isSymm_diagonal [DecidableEq n] [Zero α] (v : n -> α) : (diagonal v).IsSymm :=
  diagonal_transpose _

/--
theorem `IsSymm.fromBlocks` / 定理 `IsSymm.fromBlocks`

English:
theorem IsSymm.fromBlocks
  statement: {A : Matrix m m α} {B : Matrix m n α} {C : Matrix n m α}
  proof: by
  have hCB : Cᵀ = B := by
    rw [← hBC]
    simp
  unfold Matrix.IsSymm
  rw [fromBlocks_transpose]; rw [hA]; rw [hCB]; rw [hBC]; rw [hD]

中文:
定理 是Symm.fromBlocks
  结论: {A : 矩阵 m m α} {B : 矩阵 m n α} {C : 矩阵 n m α}
  证明: by
  have hCB : Cᵀ = B := by
    rw [← hBC]
    simp
  unfold Matrix.IsSymm
  rw [fromBlocks_transpose]; rw [hA]; rw [hCB]; rw [hBC]; rw [hD]

Depends on / 依赖: IsSymm, Matrix, Matrix.IsSymm, fromBlocks_transpose
-/
theorem IsSymm.fromBlocks {A : Matrix m m α} {B : Matrix m n α} {C : Matrix n m α}
    {D : Matrix n n α} (hA : A.IsSymm) (hBC : Bᵀ = C) (hD : D.IsSymm) :
    (A.fromBlocks B C D).IsSymm := by
  have hCB : Cᵀ = B := by
    rw [← hBC]
    simp
  unfold Matrix.IsSymm
  rw [fromBlocks_transpose]; rw [hA]; rw [hCB]; rw [hBC]; rw [hD]

/--
theorem `isSymm_fromBlocks_iff` / 定理 `isSymm_fromBlocks_iff`

English:
theorem isSymm_fromBlocks_iff
  statement: {A : Matrix m m α} {B : Matrix m n α} {C : Matrix n m α}
  proof: ⟨fun h =>
    ⟨(congr_arg toBlocks₁₁ h :), (congr_arg toBlocks₂₁ h :), (congr_arg toBlocks₁₂ h :),
      (congr_arg toBlocks₂₂ h :)⟩,
    fun ⟨hA, hBC, _, hD⟩ => IsSymm.fromBlocks hA hBC hD⟩

中文:
定理 isSymm_fromBlocks_iff
  结论: {A : 矩阵 m m α} {B : 矩阵 m n α} {C : 矩阵 n m α}
  证明: ⟨fun h =>
    ⟨(congr_arg toBlocks₁₁ h :), (congr_arg toBlocks₂₁ h :), (congr_arg toBlocks₁₂ h :),
      (congr_arg toBlocks₂₂ h :)⟩,
    fun ⟨hA, hBC, _, hD⟩ => IsSymm.fromBlocks hA hBC hD⟩

Depends on / 依赖: IsSymm, IsSymm.fromBlocks, congr_arg, fromBlocks
-/
theorem isSymm_fromBlocks_iff {A : Matrix m m α} {B : Matrix m n α} {C : Matrix n m α}
    {D : Matrix n n α} : (A.fromBlocks B C D).IsSymm ↔ A.IsSymm ∧ Bᵀ = C ∧ Cᵀ = B ∧ D.IsSymm :=
  ⟨fun h =>
    ⟨(congr_arg toBlocks₁₁ h :), (congr_arg toBlocks₂₁ h :), (congr_arg toBlocks₁₂ h :),
      (congr_arg toBlocks₂₂ h :)⟩,
    fun ⟨hA, hBC, _, hD⟩ => IsSymm.fromBlocks hA hBC hD⟩

/--
theorem `isSymm_comp_iff` / 定理 `isSymm_comp_iff`

English:
theorem isSymm_comp_iff
  given: {A : Matrix m m (Matrix n n α)}
  proof: by
  rw [IsSymm]; rw [transpose_comp]; rw [transpose_map]; rw [comp .. |>.injective.eq_iff]; rw [eq_comm]; rw [.eq_iff] transpose_involutive _ _

中文:
定理 isSymm_comp_iff
  条件: {A : 矩阵 m m (矩阵 n n α)}
  证明: by
  rw [IsSymm]; rw [transpose_comp]; rw [transpose_map]; rw [comp .. |>.injective.eq_iff]; rw [eq_comm]; rw [.eq_iff] transpose_involutive _ _

Depends on / 依赖: IsSymm, eq_comm, eq_iff, injective, injective.eq_iff, transpose_comp, transpose_involutive, transpose_map
-/
theorem isSymm_comp_iff {A : Matrix m m (Matrix n n α)} :
    (A.comp m m n n α).IsSymm ↔ Aᵀ = A.map (·ᵀ) := by
  rw [IsSymm]; rw [transpose_comp]; rw [transpose_map]; rw [comp .. |>.injective.eq_iff]; rw [eq_comm]; rw [.eq_iff] transpose_involutive _ _

/--
theorem `isSymm_comp_iff_forall` / 定理 `isSymm_comp_iff_forall`

English:
theorem isSymm_comp_iff_forall
  given: {A : Matrix m m (Matrix n n α)}
  proof: by
  simp [IsSymm.ext_iff]
  grind

中文:
定理 isSymm_comp_iff_对任意
  条件: {A : 矩阵 m m (矩阵 n n α)}
  证明: by
  simp [IsSymm.ext_iff]
  grind

Depends on / 依赖: IsSymm, IsSymm.ext_iff, ext_iff
-/
theorem isSymm_comp_iff_forall {A : Matrix m m (Matrix n n α)} :
    (A.comp m m n n α).IsSymm ↔ forall i j i' j', A j i j' i' = A i j i' j' := by
  simp [IsSymm.ext_iff]
  grind

end Matrix
