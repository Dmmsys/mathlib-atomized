/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
module

public import Mathlib.NumberTheory.ClassNumber.AdmissibleCardPowDegree
public import Mathlib.NumberTheory.ClassNumber.Finite
public import Mathlib.NumberTheory.FunctionField

/-!
# Class numbers of function fields

This file defines the class number of a function field as the (finite) cardinality of
the class group of its ring of integers. It also proves some elementary results
on the class number.

## Main definitions
- `FunctionField.classNumber`: the class number of a function field is the (finite)
  cardinality of the class group of its ring of integers
-/

@[expose] public section


namespace FunctionField

open scoped Polynomial

variable (Fq F : Type*) [Field Fq] [Fintype Fq] [Field F]
variable [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
variable [IsScalarTower Fq[X] (RatFunc Fq) F]
variable [FunctionField Fq F] [Algebra.IsSeparable (RatFunc Fq) F]

namespace RingOfIntegers

open FunctionField

open scoped Classical in
/-
**FunctionField.RingOfIntegers.** 是 Mathlib 中的一个实例，位于命名空间 `FunctionField.RingOfI
ntegers`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : Fintype (ClassGroup (ringOfIntegers Fq F)) :=
  ClassGroup.fintypeOfAdmissibleOfFinite (RatFunc Fq) F
    (Polynomial.cardPowDegreeIsAdmissible :
      AbsoluteValue.IsAdmissible (Polynomial.cardPowDegree : AbsoluteValue Fq[X] ℤ))

end RingOfIntegers

/-- The class number in a function field is the (finite) cardinality of the class group. -/
/-
**FunctionField.classNumber** 是 Mathlib 中的一个定义，位于命名空间 `FunctionField`。
形式化陈述：classNumber : Nat
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `FunctionField.ringOfIntegers.instIsDomainSubtypeMemSubalgebraPolynomial`
：∀ (F : Type u_1) (K : Type u_2) [inst : Field F] [inst_1 : Field K] [inst_2 : A
lgebra (Polynomial F) K],   IsDomain ↥(FunctionField.ringOfIn…

--- 原说明 ---
The class number in a function field is the (finite) cardinality of the class gr
oup.
-/
noncomputable def classNumber : ℕ :=
  Fintype.card (ClassGroup (ringOfIntegers Fq F))

/-- The class number of a function field is `1` iff the ring of integers is a PID. -/
/-
**FunctionField.classNumber_eq_one_iff** 是 Mathlib 中的一个定理，位于命名空间 `FunctionField`
。
形式化陈述：classNumber_eq_one_iff : classNumber Fq F = 1 ↔ IsPrincipalIdealRing (ring
OfIntegers Fq F)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `card_classGroup_eq_one_iff`：card_classGroup_eq_one_iff [IsDedekindDomain
 R] [Fintype (ClassGroup R)] : Fintype.card (ClassGroup R) = 1 ↔ IsPrincipalIdea
lRing R
· 使用定理 `FunctionField.ringOfIntegers.instIsDomainSubtypeMemSubalgebraPolynomial`
：∀ (F : Type u_1) (K : Type u_2) [inst : Field F] [inst_1 : Field K] [inst_2 : A
lgebra (Polynomial F) K],   IsDomain ↥(FunctionField.ringOfIn…
· 使用定理 `FunctionField.ringOfIntegers.instIsDedekindDomainSubtypeMemSubalgebraPol
ynomialOfIsSeparableRatFunc`：∀ (F : Type u_1) (K : Type u_2) [inst : Field F] [i
nst_1 : Field K] [inst_2 : Algebra (Polynomial F) K]   [inst_3 : Algebra (RatFun
c F) K] […

--- 原说明 ---
The class number of a function field is `1` iff the ring of integers is a PID.
-/
theorem classNumber_eq_one_iff :
    classNumber Fq F = 1 ↔ IsPrincipalIdealRing (ringOfIntegers Fq F) :=
  card_classGroup_eq_one_iff

end FunctionField

