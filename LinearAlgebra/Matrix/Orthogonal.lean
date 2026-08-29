/-
Copyright (c) 2021 Lu-Ming Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lu-Ming Zhang
-/
module

public import Mathlib.Data.Matrix.Mul

/-!
# Orthogonal

This file contains definitions and properties concerning orthogonality of rows and columns.

## Main results

- `matrix.HasOrthogonalRows`:
  `A.HasOrthogonalRows` means `A` has orthogonal (with respect to `dotProduct`) rows.
- `matrix.HasOrthogonalCols`:
  `A.HasOrthogonalCols` means `A` has orthogonal (with respect to `dotProduct`) columns.

## Tags

orthogonal
-/

@[expose] public section

assert_not_exists Field

namespace Matrix

variable {α n m : Type*}
variable [Mul α] [AddCommMonoid α]
variable (A : Matrix m n α)

open Matrix

/--
Definition of `HasOrthogonalRows` / `HasOrthogonalRows` 的定义

English:
definition HasOrthogonalRows
  signature: [Fintype n]
  body: forall ⦃i₁ i₂⦄, i₁ != i₂ -> A i₁ ⬝ᵥ A i₂ = 0

中文:
定义 HasOrthogonalRows
  签名: [有限类型 n]
  定义体: forall ⦃i₁ i₂⦄, i₁ != i₂ -> A i₁ ⬝ᵥ A i₂ = 0
-/
def HasOrthogonalRows [Fintype n] : Prop :=
  forall ⦃i₁ i₂⦄, i₁ != i₂ -> A i₁ ⬝ᵥ A i₂ = 0

/--
Definition of `HasOrthogonalCols` / `HasOrthogonalCols` 的定义

English:
definition HasOrthogonalCols
  signature: [Fintype m]
  body: HasOrthogonalRows Aᵀ

中文:
定义 HasOrthogonalCols
  签名: [有限类型 m]
  定义体: HasOrthogonalRows Aᵀ

Depends on / 依赖: HasOrthogonalRows
-/
def HasOrthogonalCols [Fintype m] : Prop :=
  HasOrthogonalRows Aᵀ

/-- `Aᵀ` has orthogonal rows iff `A` has orthogonal columns. -/
@[simp]
/--
theorem `transpose_hasOrthogonalRows_iff_hasOrthogonalCols` / 定理 `transpose_hasOrthogonalRows_iff_hasOrthogonalCols`

English:
theorem transpose_hasOrthogonalRows_iff_hasOrthogonalCols
  given: [Fintype m]
  proof: Iff.rfl

中文:
定理 transpose_hasOrthogonalRows_iff_hasOrthogonalCols
  条件: [有限类型 m]
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem transpose_hasOrthogonalRows_iff_hasOrthogonalCols [Fintype m] :
    Aᵀ.HasOrthogonalRows ↔ A.HasOrthogonalCols :=
  Iff.rfl

/-- `Aᵀ` has orthogonal columns iff `A` has orthogonal rows. -/
@[simp]
/--
theorem `transpose_hasOrthogonalCols_iff_hasOrthogonalRows` / 定理 `transpose_hasOrthogonalCols_iff_hasOrthogonalRows`

English:
theorem transpose_hasOrthogonalCols_iff_hasOrthogonalRows
  given: [Fintype n]
  proof: Iff.rfl

中文:
定理 transpose_hasOrthogonalCols_iff_hasOrthogonalRows
  条件: [有限类型 n]
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem transpose_hasOrthogonalCols_iff_hasOrthogonalRows [Fintype n] :
    Aᵀ.HasOrthogonalCols ↔ A.HasOrthogonalRows :=
  Iff.rfl

variable {A}

/--
theorem `HasOrthogonalRows.hasOrthogonalCols` / 定理 `HasOrthogonalRows.hasOrthogonalCols`

English:
theorem HasOrthogonalRows.hasOrthogonalCols
  given: [Fintype m] (h : Aᵀ.HasOrthogonalRows)
  proof: h

中文:
定理 HasOrthogonalRows.hasOrthogonalCols
  条件: [有限类型 m] (h : Aᵀ.HasOrthogonalRows)
  证明: h
-/
theorem HasOrthogonalRows.hasOrthogonalCols [Fintype m] (h : Aᵀ.HasOrthogonalRows) :
    A.HasOrthogonalCols :=
  h

/--
theorem `HasOrthogonalCols.transpose_hasOrthogonalRows` / 定理 `HasOrthogonalCols.transpose_hasOrthogonalRows`

English:
theorem HasOrthogonalCols.transpose_hasOrthogonalRows
  given: [Fintype m] (h : A.HasOrthogonalCols)
  proof: h

中文:
定理 HasOrthogonalCols.transpose_hasOrthogonalRows
  条件: [有限类型 m] (h : A.HasOrthogonalCols)
  证明: h
-/
theorem HasOrthogonalCols.transpose_hasOrthogonalRows [Fintype m] (h : A.HasOrthogonalCols) :
    Aᵀ.HasOrthogonalRows :=
  h

/--
theorem `HasOrthogonalCols.hasOrthogonalRows` / 定理 `HasOrthogonalCols.hasOrthogonalRows`

English:
theorem HasOrthogonalCols.hasOrthogonalRows
  given: [Fintype n] (h : Aᵀ.HasOrthogonalCols)
  proof: h

中文:
定理 HasOrthogonalCols.hasOrthogonalRows
  条件: [有限类型 n] (h : Aᵀ.HasOrthogonalCols)
  证明: h
-/
theorem HasOrthogonalCols.hasOrthogonalRows [Fintype n] (h : Aᵀ.HasOrthogonalCols) :
    A.HasOrthogonalRows :=
  h

/--
theorem `HasOrthogonalRows.transpose_hasOrthogonalCols` / 定理 `HasOrthogonalRows.transpose_hasOrthogonalCols`

English:
theorem HasOrthogonalRows.transpose_hasOrthogonalCols
  given: [Fintype n] (h : A.HasOrthogonalRows)
  proof: h

中文:
定理 HasOrthogonalRows.transpose_hasOrthogonalCols
  条件: [有限类型 n] (h : A.HasOrthogonalRows)
  证明: h
-/
theorem HasOrthogonalRows.transpose_hasOrthogonalCols [Fintype n] (h : A.HasOrthogonalRows) :
    Aᵀ.HasOrthogonalCols :=
  h

end Matrix
