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
/-
**Polynomial.hasSMulPi** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Polynomial.hasSMulPi [Semiring R] [SMul R S] : SMul R[X] (R -> S)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This is not an instance as it forms a diamond with `Pi.instSMul`.

See the `instance_diamonds` test for details.
-/
def Polynomial.hasSMulPi [Semiring R] [SMul R S] : SMul R[X] (R → S) :=
  ⟨fun p f x => eval x p • f x⟩

/-- This is not an instance as it forms a diamond with `Pi.instSMul`.

See the `instance_diamonds` test for details. -/
@[instance_reducible]
/-
**Polynomial.hasSMulPi'** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Polynomial.hasSMulPi' [CommSemiring R] [Semiring S] [Algebra R S] [SMul S 
T] : SMul R[X] (S -> T)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This is not an instance as it forms a diamond with `Pi.instSMul`.

See the `instance_diamonds` test for details.
-/
noncomputable def Polynomial.hasSMulPi' [CommSemiring R] [Semiring S] [Algebra R S]
    [SMul S T] : SMul R[X] (S → T) :=
  ⟨fun p f x => aeval x p • f x⟩

attribute [local instance] Polynomial.hasSMulPi Polynomial.hasSMulPi'

@[simp]
/-
**polynomial_smul_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：polynomial_smul_apply [Semiring R] [SMul R S] (p : R[X]) (f : R -> S) (x :
 R) : (p • f) x = eval x p • f x
参数：p : R[X]；f : R -> S；x : R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem polynomial_smul_apply [Semiring R] [SMul R S] (p : R[X]) (f : R → S) (x : R) :
    (p • f) x = eval x p • f x :=
  rfl

@[simp]
/-
**polynomial_smul_apply'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：polynomial_smul_apply' [CommSemiring R] [Semiring S] [Algebra R S] [SMul S
 T] (p : R[X]) (f : S -> T) (x : S) : (p • f) x = aeval x p • f x
参数：p : R[X]；f : S -> T；x : S。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem polynomial_smul_apply' [CommSemiring R] [Semiring S] [Algebra R S] [SMul S T]
    (p : R[X]) (f : S → T) (x : S) : (p • f) x = aeval x p • f x :=
  rfl

variable [CommSemiring R] [CommSemiring S] [CommSemiring T] [Algebra R S] [Algebra S T]

/-- This is not an instance for the same reasons as `Polynomial.hasSMulPi'`. -/
@[instance_reducible]
/-
**Polynomial.algebraPi** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Polynomial.algebraPi : Algebra R[X] (S -> T) where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This is not an instance for the same reasons as `Polynomial.hasSMulPi'`.
-/
noncomputable def Polynomial.algebraPi : Algebra R[X] (S → T) where
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
/-
**Polynomial.algebraMap_pi_eq_aeval** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Polynomial.algebraMap_pi_eq_aeval : (algebraMap R[X] (S -> T) : R[X] -> S 
-> T) = fun p z => algebraMap _ _ (aeval z p)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Polynomial.algebraMap_pi_eq_aeval :
    (algebraMap R[X] (S → T) : R[X] → S → T) = fun p z => algebraMap _ _ (aeval z p) :=
  rfl

@[simp]
/-
**Polynomial.algebraMap_pi_self_eq_eval** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Polynomial.algebraMap_pi_self_eq_eval : (algebraMap R[X] (R -> R) : R[X] -
> R -> R) = fun p z => eval z p
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Polynomial.algebraMap_pi_self_eq_eval :
    (algebraMap R[X] (R → R) : R[X] → R → R) = fun p z => eval z p :=
  rfl

end Pi

