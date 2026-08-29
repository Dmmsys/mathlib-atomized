/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
module

public import Mathlib.Algebra.Polynomial.AlgebraMap

/-!
# Algebraic functions

This file defines algebraic functions as the image of the `algebraMap R[X] (R → S)`.
-/

@[expose] public section

assert_not_exists IsIntegralClosure LinearIndependent IsLocalRing MvPolynomial

open Polynomial

section Pi

variable (R S T : Type*)

/-- This is not an instance as it forms a diamond with `Pi.instSMul`.

See the `instance_diamonds` test for details. -/
@[instance_reducible]
/--
Definition of `Polynomial.hasSMulPi` / `Polynomial.hasSMulPi` 的定义

English:
definition Polynomial.hasSMulPi
  signature: [Semiring R] [SMul R S]
  body: ⟨fun p f x => eval x p • f x⟩

中文:
定义 Polynomial.hasSMulPi
  签名: [Semiring R] [SMul R S]
  定义体: ⟨fun p f x => eval x p • f x⟩
-/
def Polynomial.hasSMulPi [Semiring R] [SMul R S] : SMul R[X] (R -> S) :=
  ⟨fun p f x => eval x p • f x⟩

/-- This is not an instance as it forms a diamond with `Pi.instSMul`.

See the `instance_diamonds` test for details. -/
@[instance_reducible]
/--
Definition of `Polynomial.hasSMulPi'` / `Polynomial.hasSMulPi'` 的定义

English:
definition Polynomial.hasSMulPi'
  signature: [CommSemiring R] [Semiring S] [Algebra R S]
  body: ⟨fun p f x => aeval x p • f x⟩

中文:
定义 Polynomial.hasSMulPi'
  签名: [CommSemiring R] [Semiring S] [Algebra R S]
  定义体: ⟨fun p f x => aeval x p • f x⟩
-/
noncomputable def Polynomial.hasSMulPi' [CommSemiring R] [Semiring S] [Algebra R S]
    [SMul S T] : SMul R[X] (S -> T) :=
  ⟨fun p f x => aeval x p • f x⟩

attribute [local instance] Polynomial.hasSMulPi Polynomial.hasSMulPi'

@[simp]
/--
theorem `polynomial_smul_apply` / 定理 `polynomial_smul_apply`

English:
theorem polynomial_smul_apply
  given: [Semiring R] [SMul R S] (p : R[X]) (f : R -> S) (x : R)
  proof: rfl

@[simp]

中文:
定理 polynomial_smul_apply
  条件: [Semiring R] [SMul R S] (p : R[X]) (f : R -> S) (x : R)
  证明: rfl

@[simp]
-/
theorem polynomial_smul_apply [Semiring R] [SMul R S] (p : R[X]) (f : R -> S) (x : R) :
    (p • f) x = eval x p • f x :=
  rfl

@[simp]
/--
theorem `polynomial_smul_apply'` / 定理 `polynomial_smul_apply'`

English:
theorem polynomial_smul_apply'
  statement: [CommSemiring R] [Semiring S] [Algebra R S] [SMul S T]
  proof: rfl

中文:
定理 polynomial_smul_apply'
  结论: [CommSemiring R] [Semiring S] [Algebra R S] [SMul S T]
  证明: rfl
-/
theorem polynomial_smul_apply' [CommSemiring R] [Semiring S] [Algebra R S] [SMul S T]
    (p : R[X]) (f : S -> T) (x : S) : (p • f) x = aeval x p • f x :=
  rfl

variable [CommSemiring R] [CommSemiring S] [CommSemiring T] [Algebra R S] [Algebra S T]

/-- This is not an instance for the same reasons as `Polynomial.hasSMulPi'`. -/
@[instance_reducible]
/--
Definition of `Polynomial.algebraPi` / `Polynomial.algebraPi` 的定义

English:
definition Polynomial.algebraPi
  signature: : Algebra R[X] (S -> T) where
  body: Polynomial.hasSMulPi' R S T
  algebraMap :=
  { toFun p z := algebraMap S T (aeval z p)
    map_one' := funext fun z => by simp only [Pi.one_apply, map_one]
    map_mul' _ _ := funext fun z => by simp only [Pi.mul_apply, map_mul]
    map_zero' := funext fun z => by simp only [Pi.zero_apply, map_zero

中文:
定义 Polynomial.algebraPi
  签名: : Algebra R[X] (S -> T) where
  定义体: Polynomial.hasSMulPi' R S T
  algebraMap :=
  { toFun p z := algebraMap S T (aeval z p)
    map_one' := funext fun z => by simp only [Pi.one_apply, map_one]
    map_mul' _ _ := funext fun z => by simp only [Pi.mul_apply, map_mul]
    map_zero' := funext fun z => by simp only [Pi.zero_apply, map_zero

Depends on / 依赖: Polynomial, Polynomial.hasSMulPi, hasSMulPi
-/
noncomputable def Polynomial.algebraPi : Algebra R[X] (S -> T) where
  __ := Polynomial.hasSMulPi' R S T
  algebraMap :=
  { toFun p z := algebraMap S T (aeval z p)
    map_one' := funext fun z => by simp only [Pi.one_apply, map_one]
    map_mul' _ _ := funext fun z => by simp only [Pi.mul_apply, map_mul]
    map_zero' := funext fun z => by simp only [Pi.zero_apply, map_zero]
    map_add' _ _ := funext fun z => by simp only [Pi.add_apply, map_add] }
  commutes' _ _ := funext fun z => by exact mul_comm _ _
  smul_def' _ _ := funext fun z => by
    simp only [polynomial_smul_apply', Algebra.algebraMap_eq_smul_one, RingHom.coe_mk,
      MonoidHom.coe_mk, OneHom.coe_mk, Pi.mul_apply, Algebra.smul_mul_assoc, one_mul]

attribute [local instance] Polynomial.algebraPi

@[simp]
/--
theorem `Polynomial.algebraMap_pi_eq_aeval` / 定理 `Polynomial.algebraMap_pi_eq_aeval`

English:
theorem Polynomial.algebraMap_pi_eq_aeval
  proof: rfl

@[simp]

中文:
定理 Polynomial.algebraMap_pi_eq_aeval
  证明: rfl

@[simp]
-/
theorem Polynomial.algebraMap_pi_eq_aeval :
    (algebraMap R[X] (S -> T) : R[X] -> S -> T) = fun p z => algebraMap _ _ (aeval z p) :=
  rfl

@[simp]
/--
theorem `Polynomial.algebraMap_pi_self_eq_eval` / 定理 `Polynomial.algebraMap_pi_self_eq_eval`

English:
theorem Polynomial.algebraMap_pi_self_eq_eval
  proof: rfl

中文:
定理 Polynomial.algebraMap_pi_self_eq_eval
  证明: rfl
-/
theorem Polynomial.algebraMap_pi_self_eq_eval :
    (algebraMap R[X] (R -> R) : R[X] -> R -> R) = fun p z => eval z p :=
  rfl

end Pi
