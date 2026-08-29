/-
Copyright (c) 2021 Lu-Ming Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lu-Ming Zhang
-/
module

public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Data.Matrix.Basic

/-!
# Hadamard product of matrices

This file defines the Hadamard product `Matrix.hadamard`
and contains basic properties about them.

## Main definition

- `Matrix.hadamard`: defines the Hadamard product,
  which is the pointwise product of two matrices of the same size.

## Notation

* `⊙`: the Hadamard product `Matrix.hadamard`;

## References

* <https://en.wikipedia.org/wiki/hadamard_product_(matrices)>

## Tags

hadamard product, hadamard
-/

@[expose] public section


variable {α m n R : Type*}

namespace Matrix

/--
Definition of `hadamard` / `hadamard` 的定义

English:
definition hadamard
  signature: [Mul α] (A : Matrix m n α) (B : Matrix m n α)
  body: of fun i j => A i j * B i j

中文:
定义 hadamard
  签名: [乘法 α] (A : 矩阵 m n α) (B : 矩阵 m n α)
  定义体: of fun i j => A i j * B i j
-/
def hadamard [Mul α] (A : Matrix m n α) (B : Matrix m n α) : Matrix m n α :=
  of fun i j => A i j * B i j

-- TODO: set as an equation lemma for `hadamard`, see https://github.com/leanprover-community/mathlib4/pull/3024
@[simp]
/--
theorem `hadamard_apply` / 定理 `hadamard_apply`

English:
theorem hadamard_apply
  given: [Mul α] (A : Matrix m n α) (B : Matrix m n α) (i j)
  proof: rfl

@[inherit_doc] scoped infixl:100 " ⊙ " => Matrix.hadamard

中文:
定理 hadamard_apply
  条件: [乘法 α] (A : 矩阵 m n α) (B : 矩阵 m n α) (i j)
  证明: rfl

@[inherit_doc] scoped infixl:100 " ⊙ " => Matrix.hadamard
-/
theorem hadamard_apply [Mul α] (A : Matrix m n α) (B : Matrix m n α) (i j) :
    hadamard A B i j = A i j * B i j :=
  rfl

@[inherit_doc] scoped infixl:100 " ⊙ " => Matrix.hadamard

section BasicProperties

variable (A : Matrix m n α) (B : Matrix m n α) (C : Matrix m n α)

-- commutativity
/--
theorem `hadamard_comm` / 定理 `hadamard_comm`

English:
theorem hadamard_comm
  given: [CommMagma α]
  statement: A ⊙ B = B ⊙ A
  proof: ext fun _ _ => mul_comm _ _

中文:
定理 hadamard_comm
  条件: [交换原群 α]
  结论: A ⊙ B = B ⊙ A
  证明: ext fun _ _ => mul_comm _ _

Depends on / 依赖: mul_comm
-/
theorem hadamard_comm [CommMagma α] : A ⊙ B = B ⊙ A :=
  ext fun _ _ => mul_comm _ _

-- associativity
/--
theorem `hadamard_assoc` / 定理 `hadamard_assoc`

English:
theorem hadamard_assoc
  given: [Semigroup α]
  statement: A ⊙ B ⊙ C = A ⊙ (B ⊙ C)
  proof: ext fun _ _ => mul_assoc _ _ _

中文:
定理 hadamard_assoc
  条件: [半群 α]
  结论: A ⊙ B ⊙ C = A ⊙ (B ⊙ C)
  证明: ext fun _ _ => mul_assoc _ _ _

Depends on / 依赖: mul_assoc
-/
theorem hadamard_assoc [Semigroup α] : A ⊙ B ⊙ C = A ⊙ (B ⊙ C) :=
  ext fun _ _ => mul_assoc _ _ _

-- distributivity
/--
theorem `hadamard_add` / 定理 `hadamard_add`

English:
theorem hadamard_add
  given: [Distrib α]
  statement: A ⊙ (B + C) = A ⊙ B + A ⊙ C
  proof: ext fun _ _ => left_distrib _ _ _

中文:
定理 hadamard_add
  条件: [Distrib α]
  结论: A ⊙ (B + C) = A ⊙ B + A ⊙ C
  证明: ext fun _ _ => left_distrib _ _ _

Depends on / 依赖: left_distrib
-/
theorem hadamard_add [Distrib α] : A ⊙ (B + C) = A ⊙ B + A ⊙ C :=
  ext fun _ _ => left_distrib _ _ _

/--
theorem `add_hadamard` / 定理 `add_hadamard`

English:
theorem add_hadamard
  given: [Distrib α]
  statement: (B + C) ⊙ A = B ⊙ A + C ⊙ A
  proof: ext fun _ _ => right_distrib _ _ _

中文:
定理 add_hadamard
  条件: [Distrib α]
  结论: (B + C) ⊙ A = B ⊙ A + C ⊙ A
  证明: ext fun _ _ => right_distrib _ _ _

Depends on / 依赖: right_distrib
-/
theorem add_hadamard [Distrib α] : (B + C) ⊙ A = B ⊙ A + C ⊙ A :=
  ext fun _ _ => right_distrib _ _ _

-- scalar multiplication
section Scalar

@[simp]
/--
theorem `smul_hadamard` / 定理 `smul_hadamard`

English:
theorem smul_hadamard
  given: [Mul α] [SMul R α] [IsScalarTower R α α] (k : R)
  statement: (k • A) ⊙ B = k • A ⊙ B
  proof: ext fun _ _ => smul_mul_assoc _ _ _

@[simp]

中文:
定理 smul_hadamard
  条件: [乘法 α] [标量乘法 R α] [标量塔 R α α] (k : R)
  结论: (k • A) ⊙ B = k • A ⊙ B
  证明: ext fun _ _ => smul_mul_assoc _ _ _

@[simp]

Depends on / 依赖: smul_mul_assoc
-/
theorem smul_hadamard [Mul α] [SMul R α] [IsScalarTower R α α] (k : R) : (k • A) ⊙ B = k • A ⊙ B :=
  ext fun _ _ => smul_mul_assoc _ _ _

@[simp]
/--
theorem `hadamard_smul` / 定理 `hadamard_smul`

English:
theorem hadamard_smul
  given: [Mul α] [SMul R α] [SMulCommClass R α α] (k : R)
  statement: A ⊙ (k • B) = k • A ⊙ B
  proof: ext fun _ _ => mul_smul_comm _ _ _

中文:
定理 hadamard_smul
  条件: [乘法 α] [标量乘法 R α] [标量交换类 R α α] (k : R)
  结论: A ⊙ (k • B) = k • A ⊙ B
  证明: ext fun _ _ => mul_smul_comm _ _ _

Depends on / 依赖: mul_smul_comm
-/
theorem hadamard_smul [Mul α] [SMul R α] [SMulCommClass R α α] (k : R) : A ⊙ (k • B) = k • A ⊙ B :=
  ext fun _ _ => mul_smul_comm _ _ _

end Scalar

section Zero

variable [MulZeroClass α]

@[simp]
/--
theorem `hadamard_zero` / 定理 `hadamard_zero`

English:
theorem hadamard_zero
  statement: A ⊙ (0 : Matrix m n α) = 0
  proof: ext fun _ _ => mul_zero _

@[simp]

中文:
定理 hadamard_zero
  结论: A ⊙ (0 : 矩阵 m n α) = 0
  证明: ext fun _ _ => mul_zero _

@[simp]

Depends on / 依赖: mul_zero
-/
theorem hadamard_zero : A ⊙ (0 : Matrix m n α) = 0 :=
  ext fun _ _ => mul_zero _

@[simp]
/--
theorem `zero_hadamard` / 定理 `zero_hadamard`

English:
theorem zero_hadamard
  statement: (0 : Matrix m n α) ⊙ A = 0
  proof: ext fun _ _ => zero_mul _

中文:
定理 zero_hadamard
  结论: (0 : 矩阵 m n α) ⊙ A = 0
  证明: ext fun _ _ => zero_mul _

Depends on / 依赖: zero_mul
-/
theorem zero_hadamard : (0 : Matrix m n α) ⊙ A = 0 :=
  ext fun _ _ => zero_mul _

end Zero

section Diagonal

variable [DecidableEq n] [MulZeroClass α]

/--
theorem `hadamard_diagonal` / 定理 `hadamard_diagonal`

English:
theorem hadamard_diagonal
  given: (M) (w : n -> α)
  proof: by aesop (add simp diagonal)

中文:
定理 hadamard_diagonal
  条件: (M) (w : n -> α)
  证明: by aesop (add simp diagonal)

Depends on / 依赖: diagonal
-/
theorem hadamard_diagonal (M) (w : n -> α) :
    M ⊙ diagonal w = diagonal (M.diag * w) := by aesop (add simp diagonal)

/--
theorem `diagonal_hadamard` / 定理 `diagonal_hadamard`

English:
theorem diagonal_hadamard
  given: (M) (w : n -> α)
  proof: by aesop (add simp diagonal)

中文:
定理 diagonal_hadamard
  条件: (M) (w : n -> α)
  证明: by aesop (add simp diagonal)

Depends on / 依赖: diagonal
-/
theorem diagonal_hadamard (M) (w : n -> α) :
    diagonal w ⊙ M = diagonal (w * M.diag) := by aesop (add simp diagonal)

/--
theorem `diagonal_hadamard_diagonal` / 定理 `diagonal_hadamard_diagonal`

English:
theorem diagonal_hadamard_diagonal
  given: (v : n -> α) (w : n -> α)
  proof: by simp [diagonal_hadamard]

中文:
定理 diagonal_hadamard_diagonal
  条件: (v : n -> α) (w : n -> α)
  证明: by simp [diagonal_hadamard]

Depends on / 依赖: diagonal_hadamard
-/
theorem diagonal_hadamard_diagonal (v : n -> α) (w : n -> α) :
    diagonal v ⊙ diagonal w = diagonal (v * w) := by simp [diagonal_hadamard]

/--
theorem `diagonal_hadamard_eq_diagonal_iff` / 定理 `diagonal_hadamard_eq_diagonal_iff`

English:
theorem diagonal_hadamard_eq_diagonal_iff
  given: {A : Matrix n n α} {d e}
  proof: by
  simp [diagonal_hadamard, diagonal_eq_diagonal_iff, funext_iff]

中文:
定理 diagonal_hadamard_eq_diagonal_iff
  条件: {A : 矩阵 n n α} {d e}
  证明: by
  simp [diagonal_hadamard, diagonal_eq_diagonal_iff, funext_iff]

Depends on / 依赖: diagonal_eq_diagonal_iff, diagonal_hadamard, funext_iff
-/
theorem diagonal_hadamard_eq_diagonal_iff {A : Matrix n n α} {d e} :
    diagonal d ⊙ A = diagonal e ↔ d * A.diag = e := by
  simp [diagonal_hadamard, diagonal_eq_diagonal_iff, funext_iff]

/--
theorem `hadamard_diagonal_eq_diagonal_iff` / 定理 `hadamard_diagonal_eq_diagonal_iff`

English:
theorem hadamard_diagonal_eq_diagonal_iff
  given: {A : Matrix n n α} {d e}
  proof: by
  simp [hadamard_diagonal, diagonal_eq_diagonal_iff, funext_iff]

中文:
定理 hadamard_diagonal_eq_diagonal_iff
  条件: {A : 矩阵 n n α} {d e}
  证明: by
  simp [hadamard_diagonal, diagonal_eq_diagonal_iff, funext_iff]

Depends on / 依赖: diagonal_eq_diagonal_iff, funext_iff, hadamard_diagonal
-/
theorem hadamard_diagonal_eq_diagonal_iff {A : Matrix n n α} {d e} :
    A ⊙ diagonal d = diagonal e ↔ A.diag * d = e := by
  simp [hadamard_diagonal, diagonal_eq_diagonal_iff, funext_iff]

end Diagonal

section One

variable [DecidableEq n] [MulZeroOneClass α]
variable (M : Matrix n n α)

/--
theorem `hadamard_one` / 定理 `hadamard_one`

English:
theorem hadamard_one
  statement: M ⊙ 1 = diagonal M.diag
  proof: mul_one M.diag ▸ hadamard_diagonal M 1

中文:
定理 hadamard_one
  结论: M ⊙ 1 = diagonal M.diag
  证明: mul_one M.diag ▸ hadamard_diagonal M 1

Depends on / 依赖: M.diag, hadamard_diagonal, mul_one
-/
theorem hadamard_one : M ⊙ 1 = diagonal M.diag := mul_one M.diag ▸ hadamard_diagonal M 1

/--
theorem `one_hadamard` / 定理 `one_hadamard`

English:
theorem one_hadamard
  statement: 1 ⊙ M = diagonal M.diag
  proof: one_mul M.diag ▸ diagonal_hadamard M 1

中文:
定理 one_hadamard
  结论: 1 ⊙ M = diagonal M.diag
  证明: one_mul M.diag ▸ diagonal_hadamard M 1

Depends on / 依赖: M.diag, diagonal_hadamard, one_mul
-/
theorem one_hadamard : 1 ⊙ M = diagonal M.diag := one_mul M.diag ▸ diagonal_hadamard M 1

/--
theorem `one_hadamard_eq_diagonal_iff` / 定理 `one_hadamard_eq_diagonal_iff`

English:
theorem one_hadamard_eq_diagonal_iff
  given: {A : Matrix n n α} {d}
  statement: 1 ⊙ A = diagonal d ↔ A.diag = d
  proof: by
  simpa using diagonal_hadamard_eq_diagonal_iff (A := A) (d := 1)

中文:
定理 one_hadamard_eq_diagonal_iff
  条件: {A : 矩阵 n n α} {d}
  结论: 1 ⊙ A = diagonal d ↔ A.diag = d
  证明: by
  simpa using diagonal_hadamard_eq_diagonal_iff (A := A) (d := 1)

Depends on / 依赖: diagonal_hadamard_eq_diagonal_iff
-/
theorem one_hadamard_eq_diagonal_iff {A : Matrix n n α} {d} : 1 ⊙ A = diagonal d ↔ A.diag = d := by
  simpa using diagonal_hadamard_eq_diagonal_iff (A := A) (d := 1)

/--
theorem `hadamard_one_eq_diagonal_iff` / 定理 `hadamard_one_eq_diagonal_iff`

English:
theorem hadamard_one_eq_diagonal_iff
  given: {A : Matrix n n α} {d}
  statement: A ⊙ 1 = diagonal d ↔ A.diag = d
  proof: by
  simpa using hadamard_diagonal_eq_diagonal_iff (A := A) (d := 1)

中文:
定理 hadamard_one_eq_diagonal_iff
  条件: {A : 矩阵 n n α} {d}
  结论: A ⊙ 1 = diagonal d ↔ A.diag = d
  证明: by
  simpa using hadamard_diagonal_eq_diagonal_iff (A := A) (d := 1)

Depends on / 依赖: hadamard_diagonal_eq_diagonal_iff
-/
theorem hadamard_one_eq_diagonal_iff {A : Matrix n n α} {d} : A ⊙ 1 = diagonal d ↔ A.diag = d := by
  simpa using hadamard_diagonal_eq_diagonal_iff (A := A) (d := 1)

/--
theorem `one_hadamard_eq_zero_iff` / 定理 `one_hadamard_eq_zero_iff`

English:
theorem one_hadamard_eq_zero_iff
  given: {A : Matrix n n α}
  statement: 1 ⊙ A = 0 ↔ A.diag = 0
  proof: by
  simpa using one_hadamard_eq_diagonal_iff (A := A) (d := 0)

中文:
定理 one_hadamard_eq_zero_iff
  条件: {A : 矩阵 n n α}
  结论: 1 ⊙ A = 0 ↔ A.diag = 0
  证明: by
  simpa using one_hadamard_eq_diagonal_iff (A := A) (d := 0)

Depends on / 依赖: one_hadamard_eq_diagonal_iff
-/
theorem one_hadamard_eq_zero_iff {A : Matrix n n α} : 1 ⊙ A = 0 ↔ A.diag = 0 := by
  simpa using one_hadamard_eq_diagonal_iff (A := A) (d := 0)

/--
theorem `hadamard_one_eq_zero_iff` / 定理 `hadamard_one_eq_zero_iff`

English:
theorem hadamard_one_eq_zero_iff
  given: {A : Matrix n n α}
  statement: A ⊙ 1 = 0 ↔ A.diag = 0
  proof: by
  simpa using hadamard_one_eq_diagonal_iff (A := A) (d := 0)

中文:
定理 hadamard_one_eq_zero_iff
  条件: {A : 矩阵 n n α}
  结论: A ⊙ 1 = 0 ↔ A.diag = 0
  证明: by
  simpa using hadamard_one_eq_diagonal_iff (A := A) (d := 0)

Depends on / 依赖: hadamard_one_eq_diagonal_iff
-/
theorem hadamard_one_eq_zero_iff {A : Matrix n n α} : A ⊙ 1 = 0 ↔ A.diag = 0 := by
  simpa using hadamard_one_eq_diagonal_iff (A := A) (d := 0)

/--
theorem `one_hadamard_eq_one_iff` / 定理 `one_hadamard_eq_one_iff`

English:
theorem one_hadamard_eq_one_iff
  given: {A : Matrix n n α}
  statement: 1 ⊙ A = 1 ↔ A.diag = 1
  proof: one_hadamard_eq_diagonal_iff

中文:
定理 one_hadamard_eq_one_iff
  条件: {A : 矩阵 n n α}
  结论: 1 ⊙ A = 1 ↔ A.diag = 1
  证明: one_hadamard_eq_diagonal_iff

Depends on / 依赖: one_hadamard_eq_diagonal_iff
-/
theorem one_hadamard_eq_one_iff {A : Matrix n n α} : 1 ⊙ A = 1 ↔ A.diag = 1 :=
  one_hadamard_eq_diagonal_iff

/--
theorem `hadamard_one_eq_one_iff` / 定理 `hadamard_one_eq_one_iff`

English:
theorem hadamard_one_eq_one_iff
  given: {A : Matrix n n α}
  statement: A ⊙ 1 = 1 ↔ A.diag = 1
  proof: hadamard_one_eq_diagonal_iff

中文:
定理 hadamard_one_eq_one_iff
  条件: {A : 矩阵 n n α}
  结论: A ⊙ 1 = 1 ↔ A.diag = 1
  证明: hadamard_one_eq_diagonal_iff

Depends on / 依赖: hadamard_one_eq_diagonal_iff
-/
theorem hadamard_one_eq_one_iff {A : Matrix n n α} : A ⊙ 1 = 1 ↔ A.diag = 1 :=
  hadamard_one_eq_diagonal_iff

end One

/--
theorem `hadamard_of_one` / 定理 `hadamard_of_one`

English:
theorem hadamard_of_one
  given: [MulOneClass α] (A : Matrix m n α)
  proof: by ext; simp

中文:
定理 hadamard_of_one
  条件: [MulOne类 α] (A : 矩阵 m n α)
  证明: by ext; simp
-/
@[simp] theorem hadamard_of_one [MulOneClass α] (A : Matrix m n α) :
    A ⊙ of 1 = A := by ext; simp

/--
theorem `of_one_hadamard` / 定理 `of_one_hadamard`

English:
theorem of_one_hadamard
  given: [MulOneClass α] (A : Matrix m n α)
  proof: by ext; simp

中文:
定理 of_one_hadamard
  条件: [MulOne类 α] (A : 矩阵 m n α)
  证明: by ext; simp
-/
@[simp] theorem of_one_hadamard [MulOneClass α] (A : Matrix m n α) :
    of 1 ⊙ A = A := by ext; simp

/--
theorem `hadamard_self_eq_self_iff` / 定理 `hadamard_self_eq_self_iff`

English:
theorem hadamard_self_eq_self_iff
  given: [Mul α] {A : Matrix m n α}
  proof: ext_iff.symm

中文:
定理 hadamard_self_eq_self_iff
  条件: [乘法 α] {A : 矩阵 m n α}
  证明: ext_iff.symm

Depends on / 依赖: ext_iff, ext_iff.symm
-/
theorem hadamard_self_eq_self_iff [Mul α] {A : Matrix m n α} :
    A ⊙ A = A ↔ forall i j, IsIdempotentElem (A i j) := ext_iff.symm

/--
theorem `submatrix_hadamard` / 定理 `submatrix_hadamard`

English:
theorem submatrix_hadamard
  statement: {l o : Type*} [Mul α]
  proof: rfl

中文:
定理 submatrix_hadamard
  结论: {l o : 类型} [乘法 α]
  证明: rfl
-/
theorem submatrix_hadamard {l o : Type*} [Mul α]
    (A B : Matrix m n α) (e : l -> m) (f : o -> n) :
    (A ⊙ B).submatrix e f = A.submatrix e f ⊙ B.submatrix e f := rfl

/--
theorem `transpose_hadamard` / 定理 `transpose_hadamard`

English:
theorem transpose_hadamard
  given: [Mul α] (A B : Matrix m n α)
  statement: (A ⊙ B)ᵀ = Aᵀ ⊙ Bᵀ
  proof: ext fun _ _ => rfl

中文:
定理 transpose_hadamard
  条件: [乘法 α] (A B : 矩阵 m n α)
  结论: (A ⊙ B)ᵀ = Aᵀ ⊙ Bᵀ
  证明: ext fun _ _ => rfl
-/
theorem transpose_hadamard [Mul α] (A B : Matrix m n α) : (A ⊙ B)ᵀ = Aᵀ ⊙ Bᵀ :=
  ext fun _ _ => rfl

/--
theorem `conjTranspose_hadamard` / 定理 `conjTranspose_hadamard`

English:
theorem conjTranspose_hadamard
  given: [Mul α] [StarMul α] (A B : Matrix m n α)
  statement: (A ⊙ B)ᴴ = Bᴴ ⊙ Aᴴ
  proof: ext fun _ _ => StarMul.star_mul _ _

中文:
定理 conjTranspose_hadamard
  条件: [乘法 α] [StarMul α] (A B : 矩阵 m n α)
  结论: (A ⊙ B)ᴴ = Bᴴ ⊙ Aᴴ
  证明: ext fun _ _ => StarMul.star_mul _ _

Depends on / 依赖: StarMul, StarMul.star_mul, star_mul
-/
theorem conjTranspose_hadamard [Mul α] [StarMul α] (A B : Matrix m n α) : (A ⊙ B)ᴴ = Bᴴ ⊙ Aᴴ :=
  ext fun _ _ => StarMul.star_mul _ _

section single

variable [DecidableEq m] [DecidableEq n] [MulZeroClass α]

/--
theorem `single_hadamard_single_eq` / 定理 `single_hadamard_single_eq`

English:
theorem single_hadamard_single_eq
  given: (i : m) (j : n) (a b : α)
  proof: ext fun _ _ => (apply_ite₂ _ _ _ _ _ _).trans (congr_arg _ <| zero_mul 0)

中文:
定理 single_hadamard_single_eq
  条件: (i : m) (j : n) (a b : α)
  证明: ext fun _ _ => (apply_ite₂ _ _ _ _ _ _).trans (congr_arg _ <| zero_mul 0)

Depends on / 依赖: congr_arg, zero_mul
-/
theorem single_hadamard_single_eq (i : m) (j : n) (a b : α) :
    single i j a ⊙ single i j b = single i j (a * b) :=
  ext fun _ _ => (apply_ite₂ _ _ _ _ _ _).trans (congr_arg _ <| zero_mul 0)

/--
theorem `single_hadamard_single_of_ne` / 定理 `single_hadamard_single_of_ne`

English:
theorem single_hadamard_single_of_ne
  proof: by
  rw [not_and_or] at h
  cases h <;> (simp only [single]; aesop)

中文:
定理 single_hadamard_single_of_ne
  证明: by
  rw [not_and_or] at h
  cases h <;> (simp only [single]; aesop)

Depends on / 依赖: not_and_or, single
-/
theorem single_hadamard_single_of_ne
    {ia : m} {ja : n} {ib : m} {jb : n} (h : ¬(ia = ib ∧ ja = jb)) (a b : α) :
    single ia ja a ⊙ single ib jb b = 0 := by
  rw [not_and_or] at h
  cases h <;> (simp only [single]; aesop)

end single

section trace

variable [Fintype m] [Fintype n]
variable (R) [NonUnitalSemiring α]

/--
theorem `sum_hadamard_eq` / 定理 `sum_hadamard_eq`

English:
theorem sum_hadamard_eq
  statement: (∑ i : m, ∑ j : n, (A ⊙ B) i j) = trace (A * Bᵀ)
  proof: rfl

中文:
定理 sum_hadamard_eq
  结论: (∑ i : m, ∑ j : n, (A ⊙ B) i j) = trace (A * Bᵀ)
  证明: rfl
-/
theorem sum_hadamard_eq : (∑ i : m, ∑ j : n, (A ⊙ B) i j) = trace (A * Bᵀ) :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/--
theorem `dotProduct_vecMul_hadamard` / 定理 `dotProduct_vecMul_hadamard`

English:
theorem dotProduct_vecMul_hadamard
  given: [DecidableEq m] [DecidableEq n] (v : m -> α) (w : n -> α)
  proof: by
  rw [← sum_hadamard_eq]; rw [Finset.sum_comm]
  simp [dotProduct, vecMul, Finset.sum_mul, mul_assoc]

中文:
定理 dotProduct_vecMul_hadamard
  条件: [DecidableEq m] [DecidableEq n] (v : m -> α) (w : n -> α)
  证明: by
  rw [← sum_hadamard_eq]; rw [Finset.sum_comm]
  simp [dotProduct, vecMul, Finset.sum_mul, mul_assoc]

Depends on / 依赖: Finset, Finset.sum_comm, Finset.sum_mul, dotProduct, mul_assoc, sum_comm, sum_hadamard_eq, sum_mul, vecMul
-/
theorem dotProduct_vecMul_hadamard [DecidableEq m] [DecidableEq n] (v : m -> α) (w : n -> α) :
    v ᵥ* (A ⊙ B) ⬝ᵥ w = trace (diagonal v * A * (B * diagonal w)ᵀ) := by
  rw [← sum_hadamard_eq]; rw [Finset.sum_comm]
  simp [dotProduct, vecMul, Finset.sum_mul, mul_assoc]

end trace

end BasicProperties

end Matrix
