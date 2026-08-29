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

/--
Instance `MvPolynomial.invertibleC` / 实例 `MvPolynomial.invertibleC`

English:
instance MvPolynomial.invertibleC
  signature: (σ : Type*) {R : Type*} [CommSemiring R] (r : R)
  body: Invertible.map (C : R ->+* MvPolynomial σ R) _

中文:
实例 多元多项式.invertibleC
  签名: (σ : 类型) {R : 类型} [交换半环 R] (r : R)
  定义体: Invertible.map (C : R ->+* MvPolynomial σ R) _

Depends on / 依赖: Invertible, Invertible.map, MvPolynomial
-/
noncomputable instance MvPolynomial.invertibleC (σ : Type*) {R : Type*} [CommSemiring R] (r : R)
    [Invertible r] : Invertible (C r : MvPolynomial σ R) :=
  Invertible.map (C : R ->+* MvPolynomial σ R) _

/--
Instance `MvPolynomial.invertibleCoeNat` / 实例 `MvPolynomial.invertibleCoeNat`

English:
instance MvPolynomial.invertibleCoeNat
  signature: (σ R : Type*) (p : Nat) [CommSemiring R]
  body: IsScalarTower.invertibleAlgebraCoeNat R _ _

中文:
实例 多元多项式.invertibleCoe自然数
  签名: (σ R : 类型) (p : 自然数) [交换半环 R]
  定义体: IsScalarTower.invertibleAlgebraCoeNat R _ _

Depends on / 依赖: IsScalarTower, IsScalarTower.invertibleAlgebraCoeNat, invertibleAlgebraCoeNat
-/
noncomputable instance MvPolynomial.invertibleCoeNat (σ R : Type*) (p : Nat) [CommSemiring R]
    [Invertible (p : R)] : Invertible (p : MvPolynomial σ R) :=
  IsScalarTower.invertibleAlgebraCoeNat R _ _
