/-
Copyright (c) 2025 Yunzhou Xie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yunzhou Xie
-/
module

public import Mathlib.Data.Matrix.Basic

/-!
# One by one matrices

This file proves that one by one matrices over a base are equivalent to the base itself under the
canonical map that sends a one by one matrix `!![a]` to `a`.

## Main results
- `Matrix.uniqueRingEquiv`
- `Matrix.uniqueAlgEquiv`

## Tags
Matrix, Unique, AlgEquiv
-/

@[expose] public section

namespace Matrix

variable {m n A R : Type*} [Unique m] [Unique n]

/-- The isomorphism between the type of all one by one matrices and the base type. -/
@[simps]
/-
**Matrix.uniqueEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：uniqueEquiv : Matrix m n A ≃ A where toFun M
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The isomorphism between the type of all one by one matrices and the base type.
-/
def uniqueEquiv : Matrix m n A ≃ A where
  toFun M := M default default
  invFun a := .of fun _ _ => a
  left_inv M := by ext i j; simp [Subsingleton.elim i default, Subsingleton.elim j default]
  right_inv a := by simp

/-- The obvious additive isomorphism between M₁(A) and A, if A has an addition. -/
@[simps!]
/-
**Matrix.uniqueAddEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：uniqueAddEquiv [Add A] : Matrix m n A ≃+ A where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The obvious additive isomorphism between M₁(A) and A, if A has an addition.
-/
def uniqueAddEquiv [Add A] : Matrix m n A ≃+ A where
  __ := uniqueEquiv
  map_add' := by simp

/-- `M₁(A)` is linearly equivalent to `A` as an `R`-module where `R` is a semiring. -/
@[simps]
/-
**Matrix.uniqueLinearEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：uniqueLinearEquiv [Semiring R] [AddCommMonoid A] [Module R A] : Matrix m n
 A ≃ₗ[R] A where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`M₁(A)` is linearly equivalent to `A` as an `R`-module where `R` is a semiring.
-/
def uniqueLinearEquiv [Semiring R] [AddCommMonoid A] [Module R A] : Matrix m n A ≃ₗ[R] A where
  __ := uniqueAddEquiv
  map_smul' := by simp

/-- `M₁(A)` and `A` are equivalent as rings. -/
@[simps!]
/-
**Matrix.uniqueRingEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：uniqueRingEquiv [NonUnitalNonAssocSemiring A] : Matrix m m A ≃+* A where _
_
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`M₁(A)` and `A` are equivalent as rings.
-/
def uniqueRingEquiv [NonUnitalNonAssocSemiring A] : Matrix m m A ≃+* A where
  __ := uniqueAddEquiv
  map_mul' := by simp [mul_apply]

/-- `M₁(A)` is equivalent to `A` as an `R`-algebra. -/
@[simps!]
/-
**Matrix.uniqueAlgEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：uniqueAlgEquiv [Semiring A] [CommSemiring R] [Algebra R A] : Matrix m m A 
≃ₐ[R] A where __
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α

--- 原说明 ---
`M₁(A)` is equivalent to `A` as an `R`-algebra.
-/
def uniqueAlgEquiv [Semiring A] [CommSemiring R] [Algebra R A] : Matrix m m A ≃ₐ[R] A where
  __ := uniqueRingEquiv
  commutes' r := by aesop

end Matrix

