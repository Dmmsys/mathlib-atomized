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
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Fintype (ClassGroup (ringOfIntegers Fq F))
  body: ClassGroup.fintypeOfAdmissibleOfFinite (RatFunc Fq) F
    (Polynomial.cardPowDegreeIsAdmissible :
      AbsoluteValue.IsAdmissible (Polynomial.cardPowDegree : AbsoluteValue Fq[X] Int))

中文:
实例 :
  签名: 有限类型 (ClassGroup (ringOf整数egers Fq F))
  定义体: ClassGroup.fintypeOfAdmissibleOfFinite (RatFunc Fq) F
    (Polynomial.cardPowDegreeIsAdmissible :
      AbsoluteValue.IsAdmissible (Polynomial.cardPowDegree : AbsoluteValue Fq[X] Int))

Depends on / 依赖: AbsoluteValue, AbsoluteValue.IsAdmissible, ClassGroup, ClassGroup.fintypeOfAdmissibleOfFinite, IsAdmissible, Polynomial, Polynomial.cardPowDegree, Polynomial.cardPowDegreeIsAdmissible, RatFunc, cardPowDegree, cardPowDegreeIsAdmissible, fintypeOfAdmissibleOfFinite
-/
noncomputable instance : Fintype (ClassGroup (ringOfIntegers Fq F)) :=
  ClassGroup.fintypeOfAdmissibleOfFinite (RatFunc Fq) F
    (Polynomial.cardPowDegreeIsAdmissible :
      AbsoluteValue.IsAdmissible (Polynomial.cardPowDegree : AbsoluteValue Fq[X] Int))

end RingOfIntegers

/--
Definition of `classNumber` / `classNumber` 的定义

English:
definition classNumber
  signature: : Nat
  body: Fintype.card (ClassGroup (ringOfIntegers Fq F))

中文:
定义 classNumber
  签名: : 自然数
  定义体: Fintype.card (ClassGroup (ringOfIntegers Fq F))

Depends on / 依赖: ClassGroup, Fintype, Fintype.card, ringOfIntegers
-/
noncomputable def classNumber : Nat :=
  Fintype.card (ClassGroup (ringOfIntegers Fq F))

/--
theorem `classNumber_eq_one_iff` / 定理 `classNumber_eq_one_iff`

English:
theorem classNumber_eq_one_iff
  proof: card_classGroup_eq_one_iff

中文:
定理 classNumber_eq_one_iff
  证明: card_classGroup_eq_one_iff

Depends on / 依赖: card_classGroup_eq_one_iff
-/
theorem classNumber_eq_one_iff :
    classNumber Fq F = 1 ↔ IsPrincipalIdealRing (ringOfIntegers Fq F) :=
  card_classGroup_eq_one_iff

end FunctionField
