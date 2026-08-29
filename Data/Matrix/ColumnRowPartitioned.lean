/-
Copyright (c) 2023 Mohanad ahmed. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mohanad Ahmed
-/
module

public import Mathlib.Data.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.SemiringInverse

/-! # Block Matrices from Rows and Columns

This file provides the basic definitions of matrices composed from columns and rows.
The concatenation of two matrices with the same row indices can be expressed as
`A = fromCols A₁ A₂` the concatenation of two matrices with the same column indices
can be expressed as `B = fromRows B₁ B₂`.

We then provide a few lemmas that deal with the products of these with each other and
with block matrices

## Tags
column matrices, row matrices, column row block matrices
-/

@[expose] public section

namespace Matrix

variable {R : Type*}
variable {m m₁ m₂ n n₁ n₂ : Type*}

/--
Definition of `fromRows` / `fromRows` 的定义

English:
definition fromRows
  signature: (A₁ : Matrix m₁ n R) (A₂ : Matrix m₂ n R)
  body: of (Sum.elim A₁ A₂)

中文:
定义 fromRows
  签名: (A₁ : 矩阵 m₁ n R) (A₂ : 矩阵 m₂ n R)
  定义体: of (Sum.elim A₁ A₂)

Depends on / 依赖: Sum.elim
-/
def fromRows (A₁ : Matrix m₁ n R) (A₂ : Matrix m₂ n R) : Matrix (m₁ oplus m₂) n R :=
  of (Sum.elim A₁ A₂)

/--
Definition of `fromCols` / `fromCols` 的定义

English:
definition fromCols
  signature: (B₁ : Matrix m n₁ R) (B₂ : Matrix m n₂ R)
  body: of fun i => Sum.elim (B₁ i) (B₂ i)

中文:
定义 fromCols
  签名: (B₁ : 矩阵 m n₁ R) (B₂ : 矩阵 m n₂ R)
  定义体: of fun i => Sum.elim (B₁ i) (B₂ i)

Depends on / 依赖: Sum.elim
-/
def fromCols (B₁ : Matrix m n₁ R) (B₂ : Matrix m n₂ R) : Matrix m (n₁ oplus n₂) R :=
  of fun i => Sum.elim (B₁ i) (B₂ i)

/--
Definition of `toCols₁` / `toCols₁` 的定义

English:
definition toCols₁
  signature: (A : Matrix m (n₁ oplus n₂) R)
  body: of fun i j => (A i (Sum.inl j))

中文:
定义 toCols₁
  签名: (A : 矩阵 m (n₁ oplus n₂) R)
  定义体: of fun i j => (A i (Sum.inl j))

Depends on / 依赖: Sum.inl
-/
def toCols₁ (A : Matrix m (n₁ oplus n₂) R) : Matrix m n₁ R := of fun i j => (A i (Sum.inl j))

/--
Definition of `toCols₂` / `toCols₂` 的定义

English:
definition toCols₂
  signature: (A : Matrix m (n₁ oplus n₂) R)
  body: of fun i j => (A i (Sum.inr j))

中文:
定义 toCols₂
  签名: (A : 矩阵 m (n₁ oplus n₂) R)
  定义体: of fun i j => (A i (Sum.inr j))

Depends on / 依赖: Sum.inr
-/
def toCols₂ (A : Matrix m (n₁ oplus n₂) R) : Matrix m n₂ R := of fun i j => (A i (Sum.inr j))

/--
Definition of `toRows₁` / `toRows₁` 的定义

English:
definition toRows₁
  signature: (A : Matrix (m₁ oplus m₂) n R)
  body: of fun i j => (A (Sum.inl i) j)

中文:
定义 toRows₁
  签名: (A : 矩阵 (m₁ oplus m₂) n R)
  定义体: of fun i j => (A (Sum.inl i) j)

Depends on / 依赖: Sum.inl
-/
def toRows₁ (A : Matrix (m₁ oplus m₂) n R) : Matrix m₁ n R := of fun i j => (A (Sum.inl i) j)

/--
Definition of `toRows₂` / `toRows₂` 的定义

English:
definition toRows₂
  signature: (A : Matrix (m₁ oplus m₂) n R)
  body: of fun i j => (A (Sum.inr i) j)

@[simp]

中文:
定义 toRows₂
  签名: (A : 矩阵 (m₁ oplus m₂) n R)
  定义体: of fun i j => (A (Sum.inr i) j)

@[simp]

Depends on / 依赖: Sum.inr
-/
def toRows₂ (A : Matrix (m₁ oplus m₂) n R) : Matrix m₂ n R := of fun i j => (A (Sum.inr i) j)

@[simp]
/--
lemma `fromRows_apply_inl` / 引理 `fromRows_apply_inl`

English:
lemma fromRows_apply_inl
  given: (A₁ : Matrix m₁ n R) (A₂ : Matrix m₂ n R) (i : m₁) (j : n)
  proof: rfl

@[simp]

中文:
引理 fromRows_apply_inl
  条件: (A₁ : 矩阵 m₁ n R) (A₂ : 矩阵 m₂ n R) (i : m₁) (j : n)
  证明: rfl

@[simp]
-/
lemma fromRows_apply_inl (A₁ : Matrix m₁ n R) (A₂ : Matrix m₂ n R) (i : m₁) (j : n) :
    (fromRows A₁ A₂) (Sum.inl i) j = A₁ i j := rfl

@[simp]
/--
lemma `fromRows_apply_inr` / 引理 `fromRows_apply_inr`

English:
lemma fromRows_apply_inr
  given: (A₁ : Matrix m₁ n R) (A₂ : Matrix m₂ n R) (i : m₂) (j : n)
  proof: rfl

@[simp]

中文:
引理 fromRows_apply_inr
  条件: (A₁ : 矩阵 m₁ n R) (A₂ : 矩阵 m₂ n R) (i : m₂) (j : n)
  证明: rfl

@[simp]
-/
lemma fromRows_apply_inr (A₁ : Matrix m₁ n R) (A₂ : Matrix m₂ n R) (i : m₂) (j : n) :
    (fromRows A₁ A₂) (Sum.inr i) j = A₂ i j := rfl

@[simp]
/--
lemma `fromCols_apply_inl` / 引理 `fromCols_apply_inl`

English:
lemma fromCols_apply_inl
  given: (A₁ : Matrix m n₁ R) (A₂ : Matrix m n₂ R) (i : m) (j : n₁)
  proof: rfl

@[simp]

中文:
引理 fromCols_apply_inl
  条件: (A₁ : 矩阵 m n₁ R) (A₂ : 矩阵 m n₂ R) (i : m) (j : n₁)
  证明: rfl

@[simp]
-/
lemma fromCols_apply_inl (A₁ : Matrix m n₁ R) (A₂ : Matrix m n₂ R) (i : m) (j : n₁) :
    (fromCols A₁ A₂) i (Sum.inl j) = A₁ i j := rfl

@[simp]
/--
lemma `fromCols_apply_inr` / 引理 `fromCols_apply_inr`

English:
lemma fromCols_apply_inr
  given: (A₁ : Matrix m n₁ R) (A₂ : Matrix m n₂ R) (i : m) (j : n₂)
  proof: rfl

@[simp]

中文:
引理 fromCols_apply_inr
  条件: (A₁ : 矩阵 m n₁ R) (A₂ : 矩阵 m n₂ R) (i : m) (j : n₂)
  证明: rfl

@[simp]
-/
lemma fromCols_apply_inr (A₁ : Matrix m n₁ R) (A₂ : Matrix m n₂ R) (i : m) (j : n₂) :
    (fromCols A₁ A₂) i (Sum.inr j) = A₂ i j := rfl

@[simp]
/--
lemma `toRows₁_apply` / 引理 `toRows₁_apply`

English:
lemma toRows₁_apply
  given: (A : Matrix (m₁ oplus m₂) n R) (i : m₁) (j : n)
  proof: rfl

@[simp]

中文:
引理 toRows₁_apply
  条件: (A : 矩阵 (m₁ oplus m₂) n R) (i : m₁) (j : n)
  证明: rfl

@[simp]
-/
lemma toRows₁_apply (A : Matrix (m₁ oplus m₂) n R) (i : m₁) (j : n) :
    (toRows₁ A) i j = A (Sum.inl i) j := rfl

@[simp]
/--
lemma `toRows₂_apply` / 引理 `toRows₂_apply`

English:
lemma toRows₂_apply
  given: (A : Matrix (m₁ oplus m₂) n R) (i : m₂) (j : n)
  proof: rfl

@[simp]

中文:
引理 toRows₂_apply
  条件: (A : 矩阵 (m₁ oplus m₂) n R) (i : m₂) (j : n)
  证明: rfl

@[simp]
-/
lemma toRows₂_apply (A : Matrix (m₁ oplus m₂) n R) (i : m₂) (j : n) :
    (toRows₂ A) i j = A (Sum.inr i) j := rfl

@[simp]
/--
lemma `toRows₁_fromRows` / 引理 `toRows₁_fromRows`

English:
lemma toRows₁_fromRows
  given: (A₁ : Matrix m₁ n R) (A₂ : Matrix m₂ n R)
  proof: rfl

@[simp]

中文:
引理 toRows₁_fromRows
  条件: (A₁ : 矩阵 m₁ n R) (A₂ : 矩阵 m₂ n R)
  证明: rfl

@[simp]
-/
lemma toRows₁_fromRows (A₁ : Matrix m₁ n R) (A₂ : Matrix m₂ n R) :
    toRows₁ (fromRows A₁ A₂) = A₁ := rfl

@[simp]
/--
lemma `toRows₂_fromRows` / 引理 `toRows₂_fromRows`

English:
lemma toRows₂_fromRows
  given: (A₁ : Matrix m₁ n R) (A₂ : Matrix m₂ n R)
  proof: rfl

@[simp]

中文:
引理 toRows₂_fromRows
  条件: (A₁ : 矩阵 m₁ n R) (A₂ : 矩阵 m₂ n R)
  证明: rfl

@[simp]
-/
lemma toRows₂_fromRows (A₁ : Matrix m₁ n R) (A₂ : Matrix m₂ n R) :
    toRows₂ (fromRows A₁ A₂) = A₂ := rfl

@[simp]
/--
lemma `toCols₁_apply` / 引理 `toCols₁_apply`

English:
lemma toCols₁_apply
  given: (A : Matrix m (n₁ oplus n₂) R) (i : m) (j : n₁)
  proof: rfl

@[simp]

中文:
引理 toCols₁_apply
  条件: (A : 矩阵 m (n₁ oplus n₂) R) (i : m) (j : n₁)
  证明: rfl

@[simp]
-/
lemma toCols₁_apply (A : Matrix m (n₁ oplus n₂) R) (i : m) (j : n₁) :
    (toCols₁ A) i j = A i (Sum.inl j) := rfl

@[simp]
/--
lemma `toCols₂_apply` / 引理 `toCols₂_apply`

English:
lemma toCols₂_apply
  given: (A : Matrix m (n₁ oplus n₂) R) (i : m) (j : n₂)
  proof: rfl

@[simp]

中文:
引理 toCols₂_apply
  条件: (A : 矩阵 m (n₁ oplus n₂) R) (i : m) (j : n₂)
  证明: rfl

@[simp]
-/
lemma toCols₂_apply (A : Matrix m (n₁ oplus n₂) R) (i : m) (j : n₂) :
    (toCols₂ A) i j = A i (Sum.inr j) := rfl

@[simp]
/--
lemma `toCols₁_fromCols` / 引理 `toCols₁_fromCols`

English:
lemma toCols₁_fromCols
  given: (A₁ : Matrix m n₁ R) (A₂ : Matrix m n₂ R)
  proof: rfl

@[simp]

中文:
引理 toCols₁_fromCols
  条件: (A₁ : 矩阵 m n₁ R) (A₂ : 矩阵 m n₂ R)
  证明: rfl

@[simp]
-/
lemma toCols₁_fromCols (A₁ : Matrix m n₁ R) (A₂ : Matrix m n₂ R) :
    toCols₁ (fromCols A₁ A₂) = A₁ := rfl

@[simp]
/--
lemma `toCols₂_fromCols` / 引理 `toCols₂_fromCols`

English:
lemma toCols₂_fromCols
  given: (A₁ : Matrix m n₁ R) (A₂ : Matrix m n₂ R)
  proof: rfl

@[simp]

中文:
引理 toCols₂_fromCols
  条件: (A₁ : 矩阵 m n₁ R) (A₂ : 矩阵 m n₂ R)
  证明: rfl

@[simp]
-/
lemma toCols₂_fromCols (A₁ : Matrix m n₁ R) (A₂ : Matrix m n₂ R) :
    toCols₂ (fromCols A₁ A₂) = A₂ := rfl

@[simp]
/--
lemma `fromCols_toCols` / 引理 `fromCols_toCols`

English:
lemma fromCols_toCols
  given: (A : Matrix m (n₁ oplus n₂) R)
  proof: by
  ext i (j | j) <;> simp

@[simp]

中文:
引理 fromCols_toCols
  条件: (A : 矩阵 m (n₁ oplus n₂) R)
  证明: by
  ext i (j | j) <;> simp

@[simp]
-/
lemma fromCols_toCols (A : Matrix m (n₁ oplus n₂) R) :
    fromCols A.toCols₁ A.toCols₂ = A := by
  ext i (j | j) <;> simp

@[simp]
/--
lemma `fromRows_toRows` / 引理 `fromRows_toRows`

English:
lemma fromRows_toRows
  given: (A : Matrix (m₁ oplus m₂) n R)
  statement: fromRows A.toRows₁ A.toRows₂ = A
  proof: by
  ext (i | i) j <;> simp

中文:
引理 fromRows_toRows
  条件: (A : 矩阵 (m₁ oplus m₂) n R)
  结论: fromRows A.toRows₁ A.toRows₂ = A
  证明: by
  ext (i | i) j <;> simp
-/
lemma fromRows_toRows (A : Matrix (m₁ oplus m₂) n R) : fromRows A.toRows₁ A.toRows₂ = A := by
  ext (i | i) j <;> simp

/--
lemma `fromRows_inj` / 引理 `fromRows_inj`

English:
lemma fromRows_inj
  statement: Function.Injective2 (@fromRows R m₁ m₂ n)
  proof: by
  intro x1 x2 y1 y2
  simp [← Matrix.ext_iff]

中文:
引理 fromRows_inj
  结论: 函数.Injective2 (@fromRows R m₁ m₂ n)
  证明: by
  intro x1 x2 y1 y2
  simp [← Matrix.ext_iff]

Depends on / 依赖: Matrix, Matrix.ext_iff, ext_iff
-/
lemma fromRows_inj : Function.Injective2 (@fromRows R m₁ m₂ n) := by
  intro x1 x2 y1 y2
  simp [← Matrix.ext_iff]

/--
lemma `fromCols_inj` / 引理 `fromCols_inj`

English:
lemma fromCols_inj
  statement: Function.Injective2 (@fromCols R m n₁ n₂)
  proof: by
  intro x1 x2 y1 y2
  simp only [← Matrix.ext_iff]
  simp_all

中文:
引理 fromCols_inj
  结论: 函数.Injective2 (@fromCols R m n₁ n₂)
  证明: by
  intro x1 x2 y1 y2
  simp only [← Matrix.ext_iff]
  simp_all

Depends on / 依赖: Matrix, Matrix.ext_iff, ext_iff
-/
lemma fromCols_inj : Function.Injective2 (@fromCols R m n₁ n₂) := by
  intro x1 x2 y1 y2
  simp only [← Matrix.ext_iff]
  simp_all

/--
lemma `fromCols_ext_iff` / 引理 `fromCols_ext_iff`

English:
lemma fromCols_ext_iff
  statement: (A₁ : Matrix m n₁ R) (A₂ : Matrix m n₂ R) (B₁ : Matrix m n₁ R)
  proof: fromCols_inj.eq_iff

中文:
引理 fromCols_ext_iff
  结论: (A₁ : 矩阵 m n₁ R) (A₂ : 矩阵 m n₂ R) (B₁ : 矩阵 m n₁ R)
  证明: fromCols_inj.eq_iff

Depends on / 依赖: eq_iff, fromCols_inj, fromCols_inj.eq_iff
-/
lemma fromCols_ext_iff (A₁ : Matrix m n₁ R) (A₂ : Matrix m n₂ R) (B₁ : Matrix m n₁ R)
    (B₂ : Matrix m n₂ R) :
    fromCols A₁ A₂ = fromCols B₁ B₂ ↔ A₁ = B₁ ∧ A₂ = B₂ := fromCols_inj.eq_iff

/--
lemma `fromRows_ext_iff` / 引理 `fromRows_ext_iff`

English:
lemma fromRows_ext_iff
  statement: (A₁ : Matrix m₁ n R) (A₂ : Matrix m₂ n R) (B₁ : Matrix m₁ n R)
  proof: fromRows_inj.eq_iff

中文:
引理 fromRows_ext_iff
  结论: (A₁ : 矩阵 m₁ n R) (A₂ : 矩阵 m₂ n R) (B₁ : 矩阵 m₁ n R)
  证明: fromRows_inj.eq_iff

Depends on / 依赖: eq_iff, fromRows_inj, fromRows_inj.eq_iff
-/
lemma fromRows_ext_iff (A₁ : Matrix m₁ n R) (A₂ : Matrix m₂ n R) (B₁ : Matrix m₁ n R)
    (B₂ : Matrix m₂ n R) :
    fromRows A₁ A₂ = fromRows B₁ B₂ ↔ A₁ = B₁ ∧ A₂ = B₂ := fromRows_inj.eq_iff

/--
lemma `transpose_fromCols` / 引理 `transpose_fromCols`

English:
lemma transpose_fromCols
  given: (A₁ : Matrix m n₁ R) (A₂ : Matrix m n₂ R)
  proof: by
  ext (i | i) j <;> simp

中文:
引理 transpose_fromCols
  条件: (A₁ : 矩阵 m n₁ R) (A₂ : 矩阵 m n₂ R)
  证明: by
  ext (i | i) j <;> simp
-/
lemma transpose_fromCols (A₁ : Matrix m n₁ R) (A₂ : Matrix m n₂ R) :
    transpose (fromCols A₁ A₂) = fromRows (transpose A₁) (transpose A₂) := by
  ext (i | i) j <;> simp

/--
lemma `transpose_fromRows` / 引理 `transpose_fromRows`

English:
lemma transpose_fromRows
  given: (A₁ : Matrix m₁ n R) (A₂ : Matrix m₂ n R)
  proof: by
  ext i (j | j) <;> simp

中文:
引理 transpose_fromRows
  条件: (A₁ : 矩阵 m₁ n R) (A₂ : 矩阵 m₂ n R)
  证明: by
  ext i (j | j) <;> simp
-/
lemma transpose_fromRows (A₁ : Matrix m₁ n R) (A₂ : Matrix m₂ n R) :
    transpose (fromRows A₁ A₂) = fromCols (transpose A₁) (transpose A₂) := by
  ext i (j | j) <;> simp

/--
lemma `fromRows_map` / 引理 `fromRows_map`

English:
lemma fromRows_map
  given: (A₁ : Matrix m₁ n R) (A₂ : Matrix m₂ n R) {R' : Type*} (f : R -> R')
  proof: by
  ext (_ | _) <;> rfl

中文:
引理 fromRows_map
  条件: (A₁ : 矩阵 m₁ n R) (A₂ : 矩阵 m₂ n R) {R' : 类型} (f : R -> R')
  证明: by
  ext (_ | _) <;> rfl
-/
lemma fromRows_map (A₁ : Matrix m₁ n R) (A₂ : Matrix m₂ n R) {R' : Type*} (f : R -> R') :
    (fromRows A₁ A₂).map f = fromRows (A₁.map f) (A₂.map f) := by
  ext (_ | _) <;> rfl

/--
lemma `fromCols_map` / 引理 `fromCols_map`

English:
lemma fromCols_map
  given: (A₁ : Matrix m n₁ R) (A₂ : Matrix m n₂ R) {R' : Type*} (f : R -> R')
  proof: by
  ext _ (_ | _) <;> rfl

中文:
引理 fromCols_map
  条件: (A₁ : 矩阵 m n₁ R) (A₂ : 矩阵 m n₂ R) {R' : 类型} (f : R -> R')
  证明: by
  ext _ (_ | _) <;> rfl
-/
lemma fromCols_map (A₁ : Matrix m n₁ R) (A₂ : Matrix m n₂ R) {R' : Type*} (f : R -> R') :
    (fromCols A₁ A₂).map f = fromCols (A₁.map f) (A₂.map f) := by
  ext _ (_ | _) <;> rfl

section Neg

variable [Neg R]

/-- Negating a matrix partitioned by rows is equivalent to negating each of the rows. -/
@[simp]
/--
lemma `fromRows_neg` / 引理 `fromRows_neg`

English:
lemma fromRows_neg
  given: (A₁ : Matrix m₁ n R) (A₂ : Matrix m₂ n R)
  proof: by
  ext (i | i) j <;> simp

中文:
引理 fromRows_neg
  条件: (A₁ : 矩阵 m₁ n R) (A₂ : 矩阵 m₂ n R)
  证明: by
  ext (i | i) j <;> simp
-/
lemma fromRows_neg (A₁ : Matrix m₁ n R) (A₂ : Matrix m₂ n R) :
    -fromRows A₁ A₂ = fromRows (-A₁) (-A₂) := by
  ext (i | i) j <;> simp

/-- Negating a matrix partitioned by columns is equivalent to negating each of the columns. -/
@[simp]
/--
lemma `fromCols_neg` / 引理 `fromCols_neg`

English:
lemma fromCols_neg
  given: (A₁ : Matrix n m₁ R) (A₂ : Matrix n m₂ R)
  proof: by
  ext i (j | j) <;> simp

中文:
引理 fromCols_neg
  条件: (A₁ : 矩阵 n m₁ R) (A₂ : 矩阵 n m₂ R)
  证明: by
  ext i (j | j) <;> simp
-/
lemma fromCols_neg (A₁ : Matrix n m₁ R) (A₂ : Matrix n m₂ R) :
    -fromCols A₁ A₂ = fromCols (-A₁) (-A₂) := by
  ext i (j | j) <;> simp

end Neg

@[simp]
/--
lemma `fromCols_fromRows_eq_fromBlocks` / 引理 `fromCols_fromRows_eq_fromBlocks`

English:
lemma fromCols_fromRows_eq_fromBlocks
  statement: (B₁₁ : Matrix m₁ n₁ R) (B₁₂ : Matrix m₁ n₂ R)
  proof: by
  ext (_ | _) (_ | _) <;> simp

@[simp]

中文:
引理 fromCols_fromRows_eq_fromBlocks
  结论: (B₁₁ : 矩阵 m₁ n₁ R) (B₁₂ : 矩阵 m₁ n₂ R)
  证明: by
  ext (_ | _) (_ | _) <;> simp

@[simp]
-/
lemma fromCols_fromRows_eq_fromBlocks (B₁₁ : Matrix m₁ n₁ R) (B₁₂ : Matrix m₁ n₂ R)
    (B₂₁ : Matrix m₂ n₁ R) (B₂₂ : Matrix m₂ n₂ R) :
    fromCols (fromRows B₁₁ B₂₁) (fromRows B₁₂ B₂₂) = fromBlocks B₁₁ B₁₂ B₂₁ B₂₂ := by
  ext (_ | _) (_ | _) <;> simp

@[simp]
/--
lemma `fromRows_fromCols_eq_fromBlocks` / 引理 `fromRows_fromCols_eq_fromBlocks`

English:
lemma fromRows_fromCols_eq_fromBlocks
  statement: (B₁₁ : Matrix m₁ n₁ R) (B₁₂ : Matrix m₁ n₂ R)
  proof: by
  ext (_ | _) (_ | _) <;> simp

中文:
引理 fromRows_fromCols_eq_fromBlocks
  结论: (B₁₁ : 矩阵 m₁ n₁ R) (B₁₂ : 矩阵 m₁ n₂ R)
  证明: by
  ext (_ | _) (_ | _) <;> simp
-/
lemma fromRows_fromCols_eq_fromBlocks (B₁₁ : Matrix m₁ n₁ R) (B₁₂ : Matrix m₁ n₂ R)
    (B₂₁ : Matrix m₂ n₁ R) (B₂₂ : Matrix m₂ n₂ R) :
    fromRows (fromCols B₁₁ B₁₂) (fromCols B₂₁ B₂₂) = fromBlocks B₁₁ B₁₂ B₂₁ B₂₂ := by
  ext (_ | _) (_ | _) <;> simp

section Semiring

variable [Semiring R]

@[simp]
/--
lemma `fromRows_mulVec` / 引理 `fromRows_mulVec`

English:
lemma fromRows_mulVec
  given: [Fintype n] (A₁ : Matrix m₁ n R) (A₂ : Matrix m₂ n R) (v : n -> R)
  proof: by
  ext (_ | _) <;> rfl

@[simp]

中文:
引理 fromRows_mulVec
  条件: [有限类型 n] (A₁ : 矩阵 m₁ n R) (A₂ : 矩阵 m₂ n R) (v : n -> R)
  证明: by
  ext (_ | _) <;> rfl

@[simp]
-/
lemma fromRows_mulVec [Fintype n] (A₁ : Matrix m₁ n R) (A₂ : Matrix m₂ n R) (v : n -> R) :
    fromRows A₁ A₂ *ᵥ v = Sum.elim (A₁ *ᵥ v) (A₂ *ᵥ v) := by
  ext (_ | _) <;> rfl

@[simp]
/--
lemma `vecMul_fromCols` / 引理 `vecMul_fromCols`

English:
lemma vecMul_fromCols
  given: [Fintype m] (B₁ : Matrix m n₁ R) (B₂ : Matrix m n₂ R) (v : m -> R)
  proof: by
  ext (_ | _) <;> rfl

中文:
引理 vecMul_fromCols
  条件: [有限类型 m] (B₁ : 矩阵 m n₁ R) (B₂ : 矩阵 m n₂ R) (v : m -> R)
  证明: by
  ext (_ | _) <;> rfl
-/
lemma vecMul_fromCols [Fintype m] (B₁ : Matrix m n₁ R) (B₂ : Matrix m n₂ R) (v : m -> R) :
    v ᵥ* fromCols B₁ B₂ = Sum.elim (v ᵥ* B₁) (v ᵥ* B₂) := by
  ext (_ | _) <;> rfl

set_option backward.isDefEq.respectTransparency false in
/--
lemma `sumElim_vecMul_fromRows` / 引理 `sumElim_vecMul_fromRows`

English:
lemma sumElim_vecMul_fromRows
  statement: [Fintype m₁] [Fintype m₂] (B₁ : Matrix m₁ n R) (B₂ : Matrix m₂ n R)
  proof: by
  ext
  simp [Matrix.vecMul, fromRows, dotProduct]

@[simp]

中文:
引理 sumElim_vecMul_fromRows
  结论: [有限类型 m₁] [有限类型 m₂] (B₁ : 矩阵 m₁ n R) (B₂ : 矩阵 m₂ n R)
  证明: by
  ext
  simp [Matrix.vecMul, fromRows, dotProduct]

@[simp]

Depends on / 依赖: Matrix, Matrix.vecMul, dotProduct, fromRows, vecMul
-/
lemma sumElim_vecMul_fromRows [Fintype m₁] [Fintype m₂] (B₁ : Matrix m₁ n R) (B₂ : Matrix m₂ n R)
    (v₁ : m₁ -> R) (v₂ : m₂ -> R) :
    Sum.elim v₁ v₂ ᵥ* fromRows B₁ B₂ = v₁ ᵥ* B₁ + v₂ ᵥ* B₂ := by
  ext
  simp [Matrix.vecMul, fromRows, dotProduct]

@[simp]
/--
lemma `vecMul_fromRows` / 引理 `vecMul_fromRows`

English:
lemma vecMul_fromRows
  statement: [Fintype m₁] [Fintype m₂]
  proof: by
  simp [← sumElim_vecMul_fromRows]

中文:
引理 vecMul_fromRows
  结论: [有限类型 m₁] [有限类型 m₂]
  证明: by
  simp [← sumElim_vecMul_fromRows]

Depends on / 依赖: sumElim_vecMul_fromRows
-/
lemma vecMul_fromRows [Fintype m₁] [Fintype m₂]
    (B₁ : Matrix m₁ n R) (B₂ : Matrix m₂ n R) (v : m₁ oplus m₂ -> R) :
    v ᵥ* fromRows B₁ B₂ = v ∘ Sum.inl ᵥ* B₁ + v ∘ Sum.inr ᵥ* B₂ := by
  simp [← sumElim_vecMul_fromRows]

/--
lemma `fromCols_mulVec_sumElim` / 引理 `fromCols_mulVec_sumElim`

English:
lemma fromCols_mulVec_sumElim
  statement: [Fintype n₁] [Fintype n₂]
  proof: by
  ext
  simp [Matrix.mulVec, fromCols]

@[simp]

中文:
引理 fromCols_mulVec_sumElim
  结论: [有限类型 n₁] [有限类型 n₂]
  证明: by
  ext
  simp [Matrix.mulVec, fromCols]

@[simp]

Depends on / 依赖: Matrix, Matrix.mulVec, fromCols, mulVec
-/
lemma fromCols_mulVec_sumElim [Fintype n₁] [Fintype n₂]
    (A₁ : Matrix m n₁ R) (A₂ : Matrix m n₂ R) (v₁ : n₁ -> R) (v₂ : n₂ -> R) :
    fromCols A₁ A₂ *ᵥ Sum.elim v₁ v₂ = A₁ *ᵥ v₁ + A₂ *ᵥ v₂ := by
  ext
  simp [Matrix.mulVec, fromCols]

@[simp]
/--
lemma `fromCols_mulVec` / 引理 `fromCols_mulVec`

English:
lemma fromCols_mulVec
  statement: [Fintype n₁] [Fintype n₂]
  proof: by
  simp [← fromCols_mulVec_sumElim]

@[simp]

中文:
引理 fromCols_mulVec
  结论: [有限类型 n₁] [有限类型 n₂]
  证明: by
  simp [← fromCols_mulVec_sumElim]

@[simp]

Depends on / 依赖: fromCols_mulVec_sumElim
-/
lemma fromCols_mulVec [Fintype n₁] [Fintype n₂]
    (A₁ : Matrix m n₁ R) (A₂ : Matrix m n₂ R) (v : n₁ oplus n₂ -> R) :
    fromCols A₁ A₂ *ᵥ v = A₁ *ᵥ v ∘ Sum.inl + A₂ *ᵥ v ∘ Sum.inr := by
  simp [← fromCols_mulVec_sumElim]

@[simp]
/--
lemma `fromRows_mul` / 引理 `fromRows_mul`

English:
lemma fromRows_mul
  given: [Fintype n] (A₁ : Matrix m₁ n R) (A₂ : Matrix m₂ n R) (B : Matrix n m R)
  proof: by
  ext (_ | _) _ <;> simp [mul_apply]

@[simp]

中文:
引理 fromRows_mul
  条件: [有限类型 n] (A₁ : 矩阵 m₁ n R) (A₂ : 矩阵 m₂ n R) (B : 矩阵 n m R)
  证明: by
  ext (_ | _) _ <;> simp [mul_apply]

@[simp]

Depends on / 依赖: mul_apply
-/
lemma fromRows_mul [Fintype n] (A₁ : Matrix m₁ n R) (A₂ : Matrix m₂ n R) (B : Matrix n m R) :
    fromRows A₁ A₂ * B = fromRows (A₁ * B) (A₂ * B) := by
  ext (_ | _) _ <;> simp [mul_apply]

@[simp]
/--
lemma `mul_fromCols` / 引理 `mul_fromCols`

English:
lemma mul_fromCols
  given: [Fintype n] (A : Matrix m n R) (B₁ : Matrix n n₁ R) (B₂ : Matrix n n₂ R)
  proof: by
  ext _ (_ | _) <;> simp [mul_apply]

@[simp]

中文:
引理 mul_fromCols
  条件: [有限类型 n] (A : 矩阵 m n R) (B₁ : 矩阵 n n₁ R) (B₂ : 矩阵 n n₂ R)
  证明: by
  ext _ (_ | _) <;> simp [mul_apply]

@[simp]

Depends on / 依赖: mul_apply
-/
lemma mul_fromCols [Fintype n] (A : Matrix m n R) (B₁ : Matrix n n₁ R) (B₂ : Matrix n n₂ R) :
    A * fromCols B₁ B₂ = fromCols (A * B₁) (A * B₂) := by
  ext _ (_ | _) <;> simp [mul_apply]

@[simp]
/--
lemma `fromRows_zero` / 引理 `fromRows_zero`

English:
lemma fromRows_zero
  statement: fromRows (0 : Matrix m₁ n R) (0 : Matrix m₂ n R) = 0
  proof: by
  ext (_ | _) _ <;> simp

@[simp]

中文:
引理 fromRows_zero
  结论: fromRows (0 : 矩阵 m₁ n R) (0 : 矩阵 m₂ n R) = 0
  证明: by
  ext (_ | _) _ <;> simp

@[simp]
-/
lemma fromRows_zero : fromRows (0 : Matrix m₁ n R) (0 : Matrix m₂ n R) = 0 := by
  ext (_ | _) _ <;> simp

@[simp]
/--
lemma `fromCols_zero` / 引理 `fromCols_zero`

English:
lemma fromCols_zero
  statement: fromCols (0 : Matrix m n₁ R) (0 : Matrix m n₂ R) = 0
  proof: by
  ext _ (_ | _) <;> simp

中文:
引理 fromCols_zero
  结论: fromCols (0 : 矩阵 m n₁ R) (0 : 矩阵 m n₂ R) = 0
  证明: by
  ext _ (_ | _) <;> simp
-/
lemma fromCols_zero : fromCols (0 : Matrix m n₁ R) (0 : Matrix m n₂ R) = 0 := by
  ext _ (_ | _) <;> simp

/--
lemma `fromRows_mul_fromCols` / 引理 `fromRows_mul_fromCols`

English:
lemma fromRows_mul_fromCols
  statement: [Fintype n] (A₁ : Matrix m₁ n R) (A₂ : Matrix m₂ n R)
  proof: by
  ext (_ | _) (_ | _) <;> simp

中文:
引理 fromRows_mul_fromCols
  结论: [有限类型 n] (A₁ : 矩阵 m₁ n R) (A₂ : 矩阵 m₂ n R)
  证明: by
  ext (_ | _) (_ | _) <;> simp
-/
lemma fromRows_mul_fromCols [Fintype n] (A₁ : Matrix m₁ n R) (A₂ : Matrix m₂ n R)
    (B₁ : Matrix n n₁ R) (B₂ : Matrix n n₂ R) :
    (fromRows A₁ A₂) * (fromCols B₁ B₂) =
      fromBlocks (A₁ * B₁) (A₁ * B₂) (A₂ * B₁) (A₂ * B₂) := by
  ext (_ | _) (_ | _) <;> simp

/--
lemma `fromCols_mul_fromRows` / 引理 `fromCols_mul_fromRows`

English:
lemma fromCols_mul_fromRows
  statement: [Fintype n₁] [Fintype n₂] (A₁ : Matrix m n₁ R) (A₂ : Matrix m n₂ R)
  proof: by
  ext
  simp [mul_apply]

中文:
引理 fromCols_mul_fromRows
  结论: [有限类型 n₁] [有限类型 n₂] (A₁ : 矩阵 m n₁ R) (A₂ : 矩阵 m n₂ R)
  证明: by
  ext
  simp [mul_apply]

Depends on / 依赖: mul_apply
-/
lemma fromCols_mul_fromRows [Fintype n₁] [Fintype n₂] (A₁ : Matrix m n₁ R) (A₂ : Matrix m n₂ R)
    (B₁ : Matrix n₁ n R) (B₂ : Matrix n₂ n R) :
    fromCols A₁ A₂ * fromRows B₁ B₂ = (A₁ * B₁ + A₂ * B₂) := by
  ext
  simp [mul_apply]

/--
lemma `fromCols_mul_fromBlocks` / 引理 `fromCols_mul_fromBlocks`

English:
lemma fromCols_mul_fromBlocks
  statement: [Fintype m₁] [Fintype m₂] (A₁ : Matrix m m₁ R) (A₂ : Matrix m m₂ R)
  proof: by
  ext _ (_ | _) <;> simp [mul_apply]

中文:
引理 fromCols_mul_fromBlocks
  结论: [有限类型 m₁] [有限类型 m₂] (A₁ : 矩阵 m m₁ R) (A₂ : 矩阵 m m₂ R)
  证明: by
  ext _ (_ | _) <;> simp [mul_apply]

Depends on / 依赖: mul_apply
-/
lemma fromCols_mul_fromBlocks [Fintype m₁] [Fintype m₂] (A₁ : Matrix m m₁ R) (A₂ : Matrix m m₂ R)
    (B₁₁ : Matrix m₁ n₁ R) (B₁₂ : Matrix m₁ n₂ R) (B₂₁ : Matrix m₂ n₁ R) (B₂₂ : Matrix m₂ n₂ R) :
    (fromCols A₁ A₂) * fromBlocks B₁₁ B₁₂ B₂₁ B₂₂ =
      fromCols (A₁ * B₁₁ + A₂ * B₂₁) (A₁ * B₁₂ + A₂ * B₂₂) := by
  ext _ (_ | _) <;> simp [mul_apply]

/--
lemma `fromBlocks_mul_fromRows` / 引理 `fromBlocks_mul_fromRows`

English:
lemma fromBlocks_mul_fromRows
  statement: [Fintype n₁] [Fintype n₂] (A₁ : Matrix n₁ n R) (A₂ : Matrix n₂ n R)
  proof: by
  ext (_ | _) _ <;> simp [mul_apply]

中文:
引理 fromBlocks_mul_fromRows
  结论: [有限类型 n₁] [有限类型 n₂] (A₁ : 矩阵 n₁ n R) (A₂ : 矩阵 n₂ n R)
  证明: by
  ext (_ | _) _ <;> simp [mul_apply]

Depends on / 依赖: mul_apply
-/
lemma fromBlocks_mul_fromRows [Fintype n₁] [Fintype n₂] (A₁ : Matrix n₁ n R) (A₂ : Matrix n₂ n R)
    (B₁₁ : Matrix m₁ n₁ R) (B₁₂ : Matrix m₁ n₂ R) (B₂₁ : Matrix m₂ n₁ R) (B₂₂ : Matrix m₂ n₂ R) :
    fromBlocks B₁₁ B₁₂ B₂₁ B₂₂ * (fromRows A₁ A₂) =
      fromRows (B₁₁ * A₁ + B₁₂ * A₂) (B₂₁ * A₁ + B₂₂ * A₂) := by
  ext (_ | _) _ <;> simp [mul_apply]

end Semiring

section CommRing

variable [CommRing R]

/--
lemma `fromCols_mul_fromRows_eq_one_comm` / 引理 `fromCols_mul_fromRows_eq_one_comm`

English:
lemma fromCols_mul_fromRows_eq_one_comm
  proof: mul_eq_one_comm_of_equiv e

中文:
引理 fromCols_mul_fromRows_eq_one_comm
  证明: mul_eq_one_comm_of_equiv e

Depends on / 依赖: mul_eq_one_comm_of_equiv
-/
lemma fromCols_mul_fromRows_eq_one_comm
    [Fintype n₁] [Fintype n₂] [Fintype n] [DecidableEq n] [DecidableEq n₁] [DecidableEq n₂]
    (e : n ≃ n₁ oplus n₂)
    (A₁ : Matrix n n₁ R) (A₂ : Matrix n n₂ R) (B₁ : Matrix n₁ n R) (B₂ : Matrix n₂ n R) :
    fromCols A₁ A₂ * fromRows B₁ B₂ = 1 ↔ fromRows B₁ B₂ * fromCols A₁ A₂ = 1 :=
  mul_eq_one_comm_of_equiv e

/--
lemma `equiv_compl_fromCols_mul_fromRows_eq_one_comm` / 引理 `equiv_compl_fromCols_mul_fromRows_eq_one_comm`

English:
lemma equiv_compl_fromCols_mul_fromRows_eq_one_comm
  proof: fromCols_mul_fromRows_eq_one_comm (Equiv.sumCompl p).symm A₁ A₂ B₁ B₂

中文:
引理 equiv_compl_fromCols_mul_fromRows_eq_one_comm
  证明: fromCols_mul_fromRows_eq_one_comm (Equiv.sumCompl p).symm A₁ A₂ B₁ B₂

Depends on / 依赖: Equiv.sumCompl, fromCols_mul_fromRows_eq_one_comm, sumCompl
-/
lemma equiv_compl_fromCols_mul_fromRows_eq_one_comm
    [Fintype n] [DecidableEq n] (p : n -> Prop) [DecidablePred p]
    (A₁ : Matrix n {i // p i} R) (A₂ : Matrix n {i // ¬p i} R)
    (B₁ : Matrix {i // p i} n R) (B₂ : Matrix {i // ¬p i} n R) :
    fromCols A₁ A₂ * fromRows B₁ B₂ = 1 ↔ fromRows B₁ B₂ * fromCols A₁ A₂ = 1 :=
  fromCols_mul_fromRows_eq_one_comm (Equiv.sumCompl p).symm A₁ A₂ B₁ B₂

end CommRing

section Star
variable [Star R]

/--
lemma `conjTranspose_fromCols_eq_fromRows_conjTranspose` / 引理 `conjTranspose_fromCols_eq_fromRows_conjTranspose`

English:
lemma conjTranspose_fromCols_eq_fromRows_conjTranspose
  statement: (A₁ : Matrix m n₁ R)
  proof: by
  ext (_ | _) _ <;> simp

中文:
引理 conjTranspose_fromCols_eq_fromRows_conjTranspose
  结论: (A₁ : 矩阵 m n₁ R)
  证明: by
  ext (_ | _) _ <;> simp
-/
lemma conjTranspose_fromCols_eq_fromRows_conjTranspose (A₁ : Matrix m n₁ R)
    (A₂ : Matrix m n₂ R) :
    conjTranspose (fromCols A₁ A₂) = fromRows (conjTranspose A₁) (conjTranspose A₂) := by
  ext (_ | _) _ <;> simp

/--
lemma `conjTranspose_fromRows_eq_fromCols_conjTranspose` / 引理 `conjTranspose_fromRows_eq_fromCols_conjTranspose`

English:
lemma conjTranspose_fromRows_eq_fromCols_conjTranspose
  statement: (A₁ : Matrix m₁ n R)
  proof: by
  ext _ (_ | _) <;> simp

中文:
引理 conjTranspose_fromRows_eq_fromCols_conjTranspose
  结论: (A₁ : 矩阵 m₁ n R)
  证明: by
  ext _ (_ | _) <;> simp
-/
lemma conjTranspose_fromRows_eq_fromCols_conjTranspose (A₁ : Matrix m₁ n R)
    (A₂ : Matrix m₂ n R) : conjTranspose (fromRows A₁ A₂) =
      fromCols (conjTranspose A₁) (conjTranspose A₂) := by
  ext _ (_ | _) <;> simp

end Star

end Matrix
