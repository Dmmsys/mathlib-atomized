/-
Copyright (c) 2019 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Tactic.Algebraize

/-!
# Integral closure of a subring.

If A is an R-algebra then `a : A` is integral over R if it is a root of a monic polynomial
with coefficients in R.

## Main definitions

Let `R` be a `CommRing` and let `A` be an R-algebra.

* `RingHom.IsIntegralElem (f : R →+* A) (x : A)` : `x` is integral with respect to the map `f`,

* `IsIntegral (x : A)`  : `x` is integral over `R`, i.e., is a root of a monic polynomial with
                          coefficients in `R`.
-/

@[expose] public section

open Polynomial

section Ring

variable {R S A : Type*}
variable [CommRing R] [Ring A] [Ring S] (f : R →+* S)

/-- An element `x` of `A` is said to be integral over `R` with respect to `f`
if it is a root of a monic polynomial `p : R[X]` evaluated under `f` -/
/-
**RingHom.IsIntegralElem** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：RingHom.IsIntegralElem (f : R ->+* A) (x : A)
参数：f : R ->+* A；x : A。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An element `x` of `A` is said to be integral over `R` with respect to `f`
if it is a root of a monic polynomial `p : R[X]` evaluated under `f`
-/
def RingHom.IsIntegralElem (f : R →+* A) (x : A) :=
  ∃ p : R[X], Monic p ∧ eval₂ f x p = 0

/-- A ring homomorphism `f : R →+* A` is said to be integral
if every element `A` is integral with respect to the map `f` -/
@[algebraize Algebra.IsIntegral.mk, stacks 00GI "(2)"]
/-
**RingHom.IsIntegral** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：RingHom.IsIntegral (f : R ->+* A)
参数：f : R ->+* A。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A ring homomorphism `f : R →+* A` is said to be integral
if every element `A` is integral with respect to the map `f`
-/
def RingHom.IsIntegral (f : R →+* A) :=
  ∀ x : A, f.IsIntegralElem x

variable [Algebra R A] (R)

/-- An element `x` of an algebra `A` over a commutative ring `R` is said to be *integral*,
if it is a root of some monic polynomial `p : R[X]`.
Equivalently, the element is integral over `R` with respect to the induced `algebraMap` -/
/-
**IsIntegral** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：IsIntegral (x : A) : Prop
参数：x : A。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An element `x` of an algebra `A` over a commutative ring `R` is said to be *inte
gral*,
if it is a root of some monic polynomial `p : R[X]`.
Equivalently, the element is integral over `R` with respect to the induced `alge
braMap`
-/
def IsIntegral (x : A) : Prop :=
  (algebraMap R A).IsIntegralElem x

end Ring

