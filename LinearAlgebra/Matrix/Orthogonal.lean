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

/-- `A.HasOrthogonalRows` means matrix `A` has orthogonal rows (with respect to
`dotProduct`). -/
/-
**Matrix.HasOrthogonalRows** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：HasOrthogonalRows [Fintype n] : Prop
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`A.HasOrthogonalRows` means matrix `A` has orthogonal rows (with respect to
`dotProduct`).
-/
def HasOrthogonalRows [Fintype n] : Prop :=
  ∀ ⦃i₁ i₂⦄, i₁ ≠ i₂ → A i₁ ⬝ᵥ A i₂ = 0

/-- `A.HasOrthogonalCols` means matrix `A` has orthogonal columns (with respect to
`dotProduct`). -/
/-
**Matrix.HasOrthogonalCols** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：HasOrthogonalCols [Fintype m] : Prop
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`A.HasOrthogonalCols` means matrix `A` has orthogonal columns (with respect to
`dotProduct`).
-/
def HasOrthogonalCols [Fintype m] : Prop :=
  HasOrthogonalRows Aᵀ

/-- `Aᵀ` has orthogonal rows iff `A` has orthogonal columns. -/
@[simp]
/-
**Matrix.transpose_hasOrthogonalRows_iff_hasOrthogonalCols** 是 Mathlib 中的一个定理，位于
命名空间 `Matrix`。
形式化陈述：transpose_hasOrthogonalRows_iff_hasOrthogonalCols [Fintype m] : Aᵀ.HasOrth
ogonalRows ↔ A.HasOrthogonalCols
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
`Aᵀ` has orthogonal rows iff `A` has orthogonal columns.
-/
theorem transpose_hasOrthogonalRows_iff_hasOrthogonalCols [Fintype m] :
    Aᵀ.HasOrthogonalRows ↔ A.HasOrthogonalCols :=
  Iff.rfl

/-- `Aᵀ` has orthogonal columns iff `A` has orthogonal rows. -/
@[simp]
/-
**Matrix.transpose_hasOrthogonalCols_iff_hasOrthogonalRows** 是 Mathlib 中的一个定理，位于
命名空间 `Matrix`。
形式化陈述：transpose_hasOrthogonalCols_iff_hasOrthogonalRows [Fintype n] : Aᵀ.HasOrth
ogonalCols ↔ A.HasOrthogonalRows
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
`Aᵀ` has orthogonal columns iff `A` has orthogonal rows.
-/
theorem transpose_hasOrthogonalCols_iff_hasOrthogonalRows [Fintype n] :
    Aᵀ.HasOrthogonalCols ↔ A.HasOrthogonalRows :=
  Iff.rfl

variable {A}
/-
**Matrix.HasOrthogonalRows.hasOrthogonalCols** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.H
asOrthogonalRows`。
形式化陈述：∀ {α : Type u_1} {n : Type u_2} {m : Type u_3} [inst : Mul α] [inst_1 : Ad
dCommMonoid α] {A : Matrix m n α}   [inst_2 : Fintype m], A.transpose.HasOrthogo
nalRows → A.HasOrthogonalCols
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem HasOrthogonalRows.hasOrthogonalCols [Fintype m] (h : Aᵀ.HasOrthogonalRows) :
    A.HasOrthogonalCols :=
  h
/-
**Matrix.HasOrthogonalCols.transpose_hasOrthogonalRows** 是 Mathlib 中的一个定理，位于命名空间
 `Matrix.HasOrthogonalCols`。
形式化陈述：∀ {α : Type u_1} {n : Type u_2} {m : Type u_3} [inst : Mul α] [inst_1 : Ad
dCommMonoid α] {A : Matrix m n α}   [inst_2 : Fintype m], A.HasOrthogonalCols → 
A.transpose.HasOrthogonalRows
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem HasOrthogonalCols.transpose_hasOrthogonalRows [Fintype m] (h : A.HasOrthogonalCols) :
    Aᵀ.HasOrthogonalRows :=
  h
/-
**Matrix.HasOrthogonalCols.hasOrthogonalRows** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.H
asOrthogonalCols`。
形式化陈述：∀ {α : Type u_1} {n : Type u_2} {m : Type u_3} [inst : Mul α] [inst_1 : Ad
dCommMonoid α] {A : Matrix m n α}   [inst_2 : Fintype n], A.transpose.HasOrthogo
nalCols → A.HasOrthogonalRows
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem HasOrthogonalCols.hasOrthogonalRows [Fintype n] (h : Aᵀ.HasOrthogonalCols) :
    A.HasOrthogonalRows :=
  h
/-
**Matrix.HasOrthogonalRows.transpose_hasOrthogonalCols** 是 Mathlib 中的一个定理，位于命名空间
 `Matrix.HasOrthogonalRows`。
形式化陈述：∀ {α : Type u_1} {n : Type u_2} {m : Type u_3} [inst : Mul α] [inst_1 : Ad
dCommMonoid α] {A : Matrix m n α}   [inst_2 : Fintype n], A.HasOrthogonalRows → 
A.transpose.HasOrthogonalCols
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem HasOrthogonalRows.transpose_hasOrthogonalCols [Fintype n] (h : A.HasOrthogonalRows) :
    Aᵀ.HasOrthogonalCols :=
  h

end Matrix

