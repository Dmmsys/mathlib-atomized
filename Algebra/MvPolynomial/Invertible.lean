/-
Copyright (c) 2020 Johan Commelin, Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Robert Y. Lewis
-/
module

public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.RingTheory.AlgebraTower

/-!
# Invertible polynomials

This file is a stub containing some basic facts about
invertible elements in the ring of polynomials.
-/

public section


open MvPolynomial

/-
**MvPolynomial.invertibleC** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：MvPolynomial.invertibleC (σ : Type*) {R : Type*} [CommSemiring R] (r : R) 
[Invertible r] : Invertible (C r : MvPolynomial σ R)
参数：σ : Type*；r : R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance MvPolynomial.invertibleC (σ : Type*) {R : Type*} [CommSemiring R] (r : R)
    [Invertible r] : Invertible (C r : MvPolynomial σ R) :=
  Invertible.map (C : R →+* MvPolynomial σ R) _

/-- A natural number that is invertible when coerced to a commutative semiring `R`
is also invertible when coerced to any polynomial ring with rational coefficients.

Short-cut for typeclass resolution. -/
/-
**MvPolynomial.invertibleCoeNat** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：MvPolynomial.invertibleCoeNat (σ R : Type*) (p : Nat) [CommSemiring R] [In
vertible (p : R)] : Invertible (p : MvPolynomial σ R)
参数：σ R : Type*；p : Nat；p : R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A natural number that is invertible when coerced to a commutative semiring `R`
is also invertible when coerced to any polynomial ring with rational coefficient
s.

Short-cut for typeclass resolution.
-/
noncomputable instance MvPolynomial.invertibleCoeNat (σ R : Type*) (p : ℕ) [CommSemiring R]
    [Invertible (p : R)] : Invertible (p : MvPolynomial σ R) :=
  IsScalarTower.invertibleAlgebraCoeNat R _ _
