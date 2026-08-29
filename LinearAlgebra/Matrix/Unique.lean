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
/--
Definition of `uniqueEquiv` / `uniqueEquiv` 的定义

English:
definition uniqueEquiv
  signature: : Matrix m n A ≃ A where
  body: M default default
  invFun a := .of fun _ _ => a
  left_inv M := by ext i j; simp [Subsingleton.elim i default, Subsingleton.elim j default]
  right_inv a := by simp

中文:
定义 uniqueEquiv
  签名: : 矩阵 m n A ≃ A where
  定义体: M default default
  invFun a := .of fun _ _ => a
  left_inv M := by ext i j; simp [Subsingleton.elim i default, Subsingleton.elim j default]
  right_inv a := by simp
-/
def uniqueEquiv : Matrix m n A ≃ A where
  toFun M := M default default
  invFun a := .of fun _ _ => a
  left_inv M := by ext i j; simp [Subsingleton.elim i default, Subsingleton.elim j default]
  right_inv a := by simp

/-- The obvious additive isomorphism between M₁(A) and A, if A has an addition. -/
@[simps!]
/--
Definition of `uniqueAddEquiv` / `uniqueAddEquiv` 的定义

English:
definition uniqueAddEquiv
  signature: [Add A]
  body: uniqueEquiv
  map_add' := by simp

中文:
定义 uniqueAddEquiv
  签名: [加法 A]
  定义体: uniqueEquiv
  map_add' := by simp

Depends on / 依赖: uniqueEquiv
-/
def uniqueAddEquiv [Add A] : Matrix m n A ≃+ A where
  __ := uniqueEquiv
  map_add' := by simp

/-- `M₁(A)` is linearly equivalent to `A` as an `R`-module where `R` is a semiring. -/
@[simps]
/--
Definition of `uniqueLinearEquiv` / `uniqueLinearEquiv` 的定义

English:
definition uniqueLinearEquiv
  signature: [Semiring R] [AddCommMonoid A] [Module R A]
  body: uniqueAddEquiv
  map_smul' := by simp

中文:
定义 uniqueLinearEquiv
  签名: [半环 R] [加法交换幺半群 A] [模 R A]
  定义体: uniqueAddEquiv
  map_smul' := by simp

Depends on / 依赖: uniqueAddEquiv
-/
def uniqueLinearEquiv [Semiring R] [AddCommMonoid A] [Module R A] : Matrix m n A ≃ₗ[R] A where
  __ := uniqueAddEquiv
  map_smul' := by simp

/-- `M₁(A)` and `A` are equivalent as rings. -/
@[simps!]
/--
Definition of `uniqueRingEquiv` / `uniqueRingEquiv` 的定义

English:
definition uniqueRingEquiv
  signature: [NonUnitalNonAssocSemiring A]
  body: uniqueAddEquiv
  map_mul' := by simp [mul_apply]

中文:
定义 uniqueRingEquiv
  签名: [非幺非结合半环 A]
  定义体: uniqueAddEquiv
  map_mul' := by simp [mul_apply]

Depends on / 依赖: uniqueAddEquiv
-/
def uniqueRingEquiv [NonUnitalNonAssocSemiring A] : Matrix m m A ≃+* A where
  __ := uniqueAddEquiv
  map_mul' := by simp [mul_apply]

/-- `M₁(A)` is equivalent to `A` as an `R`-algebra. -/
@[simps!]
/--
Definition of `uniqueAlgEquiv` / `uniqueAlgEquiv` 的定义

English:
definition uniqueAlgEquiv
  signature: [Semiring A] [CommSemiring R] [Algebra R A]
  body: uniqueRingEquiv
  commutes' r := by aesop

中文:
定义 uniqueAlgEquiv
  签名: [半环 A] [交换半环 R] [代数 R A]
  定义体: uniqueRingEquiv
  commutes' r := by aesop

Depends on / 依赖: uniqueRingEquiv
-/
def uniqueAlgEquiv [Semiring A] [CommSemiring R] [Algebra R A] : Matrix m m A ≃ₐ[R] A where
  __ := uniqueRingEquiv
  commutes' r := by aesop

end Matrix
