/-
Copyright (c) 2025 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
module

public import Mathlib.RingTheory.PrincipalIdealDomain
public import Mathlib.RingTheory.SimpleRing.Field
public import Mathlib.RingTheory.TwoSidedIdeal.Operations

/-!
# A commutative simple ring is a principal ideal domain

Indeed, it is a field.

-/

public section

variable {R : Type*} [CommRing R] [IsSimpleRing R]

/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsSimpleOrder (Ideal R) := TwoSidedIdeal.orderIsoIdeal.symm.isSimpleOrder
/-
**IsPrincipalIdealRing.of_isSimpleRing** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：IsPrincipalIdealRing.of_isSimpleRing : IsPrincipalIdealRing R
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `IsField.isPrincipalIdealRing`：IsField.isPrincipalIdealRing {R : Type*} [
Ring R] (h : IsField R) : IsPrincipalIdealRing R
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `isSimpleRing_iff_isField`：isSimpleRing_iff_isField (A : Type*) [CommRing
 A] : IsSimpleRing A ↔ IsField A
-/
instance IsPrincipalIdealRing.of_isSimpleRing :
    IsPrincipalIdealRing R :=
  ((isSimpleRing_iff_isField _).mp ‹_›).isPrincipalIdealRing
/-
**IsDomain.of_isSimpleRing** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：IsDomain.of_isSimpleRing : IsDomain R
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `IsField.isDomain`：IsField.isDomain {R : Type u} [Semiring R] (h : IsFiel
d R) : IsDomain R where mul_left_cancel_of_ne_zero ha _ _ hb
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `isSimpleRing_iff_isField`：isSimpleRing_iff_isField (A : Type*) [CommRing
 A] : IsSimpleRing A ↔ IsField A
-/
instance IsDomain.of_isSimpleRing :
    IsDomain R :=
  ((isSimpleRing_iff_isField _).mp ‹_›).isDomain
