/-
Copyright (c) 2024 Judith Ludwig, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Judith Ludwig, Christian Merten
-/
module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.Permutation
public import Mathlib.Data.Matrix.PEquiv

/-!
# Swap matrices

A swap matrix indexed by `i` and `j` is the matrix that, when multiplying another matrix
on the left (resp. on the right), swaps the `i`-th row with the `j`-th row
(resp. the `i`-th column with the `j`-th column).

Swap matrices are a special case of *elementary matrices*. For transvections see
`Mathlib/LinearAlgebra/Matrix/Transvection.lean`.

## Implementation detail

This is a thin wrapper around `(Equiv.swap i j).permMatrix`.
-/

@[expose] public section

namespace Matrix

section Def
variable {R n : Type*} [Zero R] [One R] [DecidableEq n]

variable (R) in
/--
Definition of `swap` / `swap` 的定义

English:
definition swap
  signature: (i j : n)
  body: (Equiv.swap i j).permMatrix R

中文:
定义 swap
  签名: (i j : n)
  定义体: (Equiv.swap i j).permMatrix R

Depends on / 依赖: Equiv.swap, permMatrix
-/
def swap (i j : n) : Matrix n n R :=
  (Equiv.swap i j).permMatrix R

/--
lemma `swap_comm` / 引理 `swap_comm`

English:
lemma swap_comm
  given: (i j : n)
  proof: by
  simp only [swap, Equiv.swap_comm]

@[simp]

中文:
引理 swap_comm
  条件: (i j : n)
  证明: by
  simp only [swap, Equiv.swap_comm]

@[simp]

Depends on / 依赖: Equiv.swap_comm, swap_comm
-/
lemma swap_comm (i j : n) :
    swap R i j = swap R j i := by
  simp only [swap, Equiv.swap_comm]

@[simp]
/--
lemma `transpose_swap` / 引理 `transpose_swap`

English:
lemma transpose_swap
  given: (i j : n)
  statement: (swap R i j).transpose = swap R i j
  proof: by
  simp [swap]

中文:
引理 transpose_swap
  条件: (i j : n)
  结论: (swap R i j).transpose = swap R i j
  证明: by
  simp [swap]
-/
lemma transpose_swap (i j : n) : (swap R i j).transpose = swap R i j := by
  simp [swap]

/--
theorem `isSymm_swap` / 定理 `isSymm_swap`

English:
theorem isSymm_swap
  given: (i j : n)
  statement: (swap R i j).IsSymm
  proof: transpose_swap i j

@[simp]

中文:
定理 isSymm_swap
  条件: (i j : n)
  结论: (swap R i j).是Symm
  证明: transpose_swap i j

@[simp]

Depends on / 依赖: transpose_swap
-/
theorem isSymm_swap (i j : n) : (swap R i j).IsSymm :=
  transpose_swap i j

@[simp]
/--
lemma `conjTranspose_swap` / 引理 `conjTranspose_swap`

English:
lemma conjTranspose_swap
  given: {R : Type*} [NonAssocSemiring R] [StarRing R] (i j : n)
  proof: by
  simp [swap]

中文:
引理 conjTranspose_swap
  条件: {R : 类型} [非结合半环 R] [对合环 R] (i j : n)
  证明: by
  simp [swap]
-/
lemma conjTranspose_swap {R : Type*} [NonAssocSemiring R] [StarRing R] (i j : n) :
    (swap R i j).conjTranspose = swap R i j := by
  simp [swap]

end Def

section
variable {R n m : Type*} [Semiring R] [DecidableEq n]

@[simp]
/--
lemma `map_swap` / 引理 `map_swap`

English:
lemma map_swap
  given: {S : Type*} [NonAssocSemiring S] (f : R ->+* S) (i j : n)
  proof: by
  simp [swap]

中文:
引理 map_swap
  条件: {S : 类型} [非结合半环 S] (f : R ->+* S) (i j : n)
  证明: by
  simp [swap]
-/
lemma map_swap {S : Type*} [NonAssocSemiring S] (f : R ->+* S) (i j : n) :
    (swap R i j).map f = swap S i j := by
  simp [swap]

variable [Fintype n]

/--
lemma `swap_mulVec` / 引理 `swap_mulVec`

English:
lemma swap_mulVec
  given: (i j : n) (a : n -> R)
  proof: by
  simp [swap, PEquiv.toMatrix_toPEquiv_mulVec]

中文:
引理 swap_mulVec
  条件: (i j : n) (a : n -> R)
  证明: by
  simp [swap, PEquiv.toMatrix_toPEquiv_mulVec]

Depends on / 依赖: PEquiv, PEquiv.toMatrix_toPEquiv_mulVec, toMatrix_toPEquiv_mulVec
-/
lemma swap_mulVec (i j : n) (a : n -> R) :
    swap R i j *ᵥ a = a ∘ Equiv.swap i j := by
  simp [swap, PEquiv.toMatrix_toPEquiv_mulVec]

/--
lemma `vecMul_swap` / 引理 `vecMul_swap`

English:
lemma vecMul_swap
  given: (i j : n) (a : n -> R)
  proof: by
  simp [swap, PEquiv.vecMul_toMatrix_toPEquiv]

@[simp]

中文:
引理 vecMul_swap
  条件: (i j : n) (a : n -> R)
  证明: by
  simp [swap, PEquiv.vecMul_toMatrix_toPEquiv]

@[simp]

Depends on / 依赖: PEquiv, PEquiv.vecMul_toMatrix_toPEquiv, vecMul_toMatrix_toPEquiv
-/
lemma vecMul_swap (i j : n) (a : n -> R) :
    a ᵥ* swap R i j = a ∘ Equiv.swap i j := by
  simp [swap, PEquiv.vecMul_toMatrix_toPEquiv]

@[simp]
/--
lemma `swap_mulVec_apply` / 引理 `swap_mulVec_apply`

English:
lemma swap_mulVec_apply
  given: (i j : n) (a : n -> R)
  proof: by
  simp [swap, PEquiv.toMatrix_toPEquiv_mulVec]

@[simp]

中文:
引理 swap_mulVec_apply
  条件: (i j : n) (a : n -> R)
  证明: by
  simp [swap, PEquiv.toMatrix_toPEquiv_mulVec]

@[simp]

Depends on / 依赖: PEquiv, PEquiv.toMatrix_toPEquiv_mulVec, toMatrix_toPEquiv_mulVec
-/
lemma swap_mulVec_apply (i j : n) (a : n -> R) :
    (swap R i j *ᵥ a) i = a j := by
  simp [swap, PEquiv.toMatrix_toPEquiv_mulVec]

@[simp]
/--
lemma `vecMul_swap_apply` / 引理 `vecMul_swap_apply`

English:
lemma vecMul_swap_apply
  given: (i j : n) (a : n -> R)
  proof: by
  simp [swap, PEquiv.vecMul_toMatrix_toPEquiv]

中文:
引理 vecMul_swap_apply
  条件: (i j : n) (a : n -> R)
  证明: by
  simp [swap, PEquiv.vecMul_toMatrix_toPEquiv]

Depends on / 依赖: PEquiv, PEquiv.vecMul_toMatrix_toPEquiv, vecMul_toMatrix_toPEquiv
-/
lemma vecMul_swap_apply (i j : n) (a : n -> R) :
    (a ᵥ* swap R i j) i = a j := by
  simp [swap, PEquiv.vecMul_toMatrix_toPEquiv]

/-- Multiplying with `swap R i j` on the left swaps the `i`-th row with the `j`-th row. -/
@[simp]
/--
lemma `swap_mul_apply_left` / 引理 `swap_mul_apply_left`

English:
lemma swap_mul_apply_left
  given: (i j : n) (a : m) (g : Matrix n m R)
  proof: by
  simp [swap, PEquiv.toMatrix_toPEquiv_mul]

中文:
引理 swap_mul_apply_left
  条件: (i j : n) (a : m) (g : 矩阵 n m R)
  证明: by
  simp [swap, PEquiv.toMatrix_toPEquiv_mul]

Depends on / 依赖: PEquiv, PEquiv.toMatrix_toPEquiv_mul, toMatrix_toPEquiv_mul
-/
lemma swap_mul_apply_left (i j : n) (a : m) (g : Matrix n m R) :
    (swap R i j * g) i a = g j a := by
  simp [swap, PEquiv.toMatrix_toPEquiv_mul]

/-- Multiplying with `swap R i j` on the left swaps the `j`-th row with the `i`-th row. -/
@[simp]
/--
lemma `swap_mul_apply_right` / 引理 `swap_mul_apply_right`

English:
lemma swap_mul_apply_right
  given: (i j : n) (a : m) (g : Matrix n m R)
  proof: by
  rw [swap_comm]; rw [swap_mul_apply_left]

中文:
引理 swap_mul_apply_right
  条件: (i j : n) (a : m) (g : 矩阵 n m R)
  证明: by
  rw [swap_comm]; rw [swap_mul_apply_left]

Depends on / 依赖: swap_comm, swap_mul_apply_left
-/
lemma swap_mul_apply_right (i j : n) (a : m) (g : Matrix n m R) :
    (swap R i j * g) j a = g i a := by
  rw [swap_comm]; rw [swap_mul_apply_left]

/--
lemma `swap_mul_of_ne` / 引理 `swap_mul_of_ne`

English:
lemma swap_mul_of_ne
  given: {i j a : n} {b : m} (hai : a != i) (haj : a != j) (g : Matrix n m R)
  proof: by
  simp [swap, PEquiv.toMatrix_toPEquiv_mul, Equiv.swap_apply_of_ne_of_ne hai haj]

中文:
引理 swap_mul_of_ne
  条件: {i j a : n} {b : m} (hai : a != i) (haj : a != j) (g : 矩阵 n m R)
  证明: by
  simp [swap, PEquiv.toMatrix_toPEquiv_mul, Equiv.swap_apply_of_ne_of_ne hai haj]

Depends on / 依赖: Equiv.swap_apply_of_ne_of_ne, PEquiv, PEquiv.toMatrix_toPEquiv_mul, swap_apply_of_ne_of_ne, toMatrix_toPEquiv_mul
-/
lemma swap_mul_of_ne {i j a : n} {b : m} (hai : a != i) (haj : a != j) (g : Matrix n m R) :
    (swap R i j * g) a b = g a b := by
  simp [swap, PEquiv.toMatrix_toPEquiv_mul, Equiv.swap_apply_of_ne_of_ne hai haj]

/-- Multiplying with `swap R i j` on the right swaps the `i`-th column with the `j`-th column. -/
@[simp]
/--
lemma `mul_swap_apply_left` / 引理 `mul_swap_apply_left`

English:
lemma mul_swap_apply_left
  given: (i j : n) (a : m) (g : Matrix m n R)
  proof: by
  simp [swap, PEquiv.mul_toMatrix_toPEquiv]

中文:
引理 mul_swap_apply_left
  条件: (i j : n) (a : m) (g : 矩阵 m n R)
  证明: by
  simp [swap, PEquiv.mul_toMatrix_toPEquiv]

Depends on / 依赖: PEquiv, PEquiv.mul_toMatrix_toPEquiv, mul_toMatrix_toPEquiv
-/
lemma mul_swap_apply_left (i j : n) (a : m) (g : Matrix m n R) :
    (g * swap R i j) a i = g a j := by
  simp [swap, PEquiv.mul_toMatrix_toPEquiv]

/-- Multiplying with `swap R i j` on the right swaps the `j`-th column with the `i`-th column. -/
@[simp]
/--
lemma `mul_swap_apply_right` / 引理 `mul_swap_apply_right`

English:
lemma mul_swap_apply_right
  given: (i j : n) (a : m) (g : Matrix m n R)
  proof: by
  rw [swap_comm]; rw [mul_swap_apply_left]

中文:
引理 mul_swap_apply_right
  条件: (i j : n) (a : m) (g : 矩阵 m n R)
  证明: by
  rw [swap_comm]; rw [mul_swap_apply_left]

Depends on / 依赖: mul_swap_apply_left, swap_comm
-/
lemma mul_swap_apply_right (i j : n) (a : m) (g : Matrix m n R) :
    (g * swap R i j) a j = g a i := by
  rw [swap_comm]; rw [mul_swap_apply_left]

/--
lemma `mul_swap_of_ne` / 引理 `mul_swap_of_ne`

English:
lemma mul_swap_of_ne
  given: {i j b : n} {a : m} (hbi : b != i) (hbj : b != j) (g : Matrix m n R)
  proof: by
  simp [swap, PEquiv.mul_toMatrix_toPEquiv, Equiv.swap_apply_of_ne_of_ne hbi hbj]

中文:
引理 mul_swap_of_ne
  条件: {i j b : n} {a : m} (hbi : b != i) (hbj : b != j) (g : 矩阵 m n R)
  证明: by
  simp [swap, PEquiv.mul_toMatrix_toPEquiv, Equiv.swap_apply_of_ne_of_ne hbi hbj]

Depends on / 依赖: Equiv.swap_apply_of_ne_of_ne, PEquiv, PEquiv.mul_toMatrix_toPEquiv, mul_toMatrix_toPEquiv, swap_apply_of_ne_of_ne
-/
lemma mul_swap_of_ne {i j b : n} {a : m} (hbi : b != i) (hbj : b != j) (g : Matrix m n R) :
    (g * swap R i j) a b = g a b := by
  simp [swap, PEquiv.mul_toMatrix_toPEquiv, Equiv.swap_apply_of_ne_of_ne hbi hbj]

/--
lemma `swap_mul_self` / 引理 `swap_mul_self`

English:
lemma swap_mul_self
  given: (i j : n)
  statement: swap R i j * swap R i j = 1
  proof: by
  simp only [swap]
  rw [← Equiv.swap_inv]; rw [Equiv.Perm.inv_def]
  simp [← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_trans]

中文:
引理 swap_mul_self
  条件: (i j : n)
  结论: swap R i j * swap R i j = 1
  证明: by
  simp only [swap]
  rw [← Equiv.swap_inv]; rw [Equiv.Perm.inv_def]
  simp [← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_trans]

Depends on / 依赖: Equiv.Perm.inv_def, Equiv.swap_inv, Equiv.toPEquiv_trans, PEquiv, PEquiv.toMatrix_trans, inv_def, swap_inv, toMatrix_trans, toPEquiv_trans
-/
lemma swap_mul_self (i j : n) : swap R i j * swap R i j = 1 := by
  simp only [swap]
  rw [← Equiv.swap_inv]; rw [Equiv.Perm.inv_def]
  simp [← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_trans]

end

namespace GeneralLinearGroup
variable (R : Type*) {n : Type*} [CommRing R] [DecidableEq n] [Fintype n]

/-- `Matrix.swap` as an element of `GL n R`. -/
@[simps val]
/--
Definition of `swap` / `swap` 的定义

English:
definition swap
  signature: (i j : n)
  body: Matrix.swap R i j
  inv := Matrix.swap R i j
  val_inv := swap_mul_self i j
  inv_val := swap_mul_self i j

中文:
定义 swap
  签名: (i j : n)
  定义体: Matrix.swap R i j
  inv := Matrix.swap R i j
  val_inv := swap_mul_self i j
  inv_val := swap_mul_self i j

Depends on / 依赖: Matrix, Matrix.swap
-/
def swap (i j : n) : GL n R where
  val := Matrix.swap R i j
  inv := Matrix.swap R i j
  val_inv := swap_mul_self i j
  inv_val := swap_mul_self i j

variable {R} {S : Type*} [CommRing S] (f : R ->+* S)

@[simp]
/--
lemma `map_swap` / 引理 `map_swap`

English:
lemma map_swap
  given: (i j : n)
  statement: (swap R i j).map f = swap S i j
  proof: by
  ext : 1
  simp [swap]

中文:
引理 map_swap
  条件: (i j : n)
  结论: (swap R i j).map f = swap S i j
  证明: by
  ext : 1
  simp [swap]
-/
lemma map_swap (i j : n) : (swap R i j).map f = swap S i j := by
  ext : 1
  simp [swap]

end GeneralLinearGroup

end Matrix
