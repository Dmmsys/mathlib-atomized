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

* `IsIntegral (x : A)` : `x` is integral over `R`, i.e., is a root of a monic polynomial with
                          coefficients in `R`.
-/

@[expose] public section

open Polynomial

section Ring

variable {R S A : Type*}
variable [CommRing R] [Ring A] [Ring S] (f : R ->+* S)

/--
Definition of `RingHom.IsIntegralElem` / `RingHom.IsIntegralElem` 的定义

English:
definition RingHom.IsIntegralElem
  signature: (f : R ->+* A) (x : A)
  body: exists p : R[X], Monic p ∧ eval₂ f x p = 0

中文:
定义 RingHom.IsIntegralElem
  签名: (f : R ->+* A) (x : A)
  定义体: exists p : R[X], Monic p ∧ eval₂ f x p = 0
-/
def RingHom.IsIntegralElem (f : R ->+* A) (x : A) :=
  exists p : R[X], Monic p ∧ eval₂ f x p = 0

/-- A ring homomorphism `f : R →+* A` is said to be integral
if every element `A` is integral with respect to the map `f` -/
@[algebraize Algebra.IsIntegral.mk, stacks 00GI "(2)"]
/--
Definition of `RingHom.IsIntegral` / `RingHom.IsIntegral` 的定义

English:
definition RingHom.IsIntegral
  signature: (f : R ->+* A)
  body: forall x : A, f.IsIntegralElem x

中文:
定义 RingHom.IsIntegral
  签名: (f : R ->+* A)
  定义体: forall x : A, f.IsIntegralElem x

Depends on / 依赖: IsIntegralElem, f.IsIntegralElem
-/
def RingHom.IsIntegral (f : R ->+* A) :=
  forall x : A, f.IsIntegralElem x

variable [Algebra R A] (R)

/--
Definition of `IsIntegral` / `IsIntegral` 的定义

English:
definition IsIntegral
  signature: (x : A)
  body: (algebraMap R A).IsIntegralElem x

中文:
定义 IsIntegral
  签名: (x : A)
  定义体: (algebraMap R A).IsIntegralElem x

Depends on / 依赖: IsIntegralElem, algebraMap
-/
def IsIntegral (x : A) : Prop :=
  (algebraMap R A).IsIntegralElem x

end Ring
