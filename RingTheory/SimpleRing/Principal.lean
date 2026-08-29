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

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsSimpleOrder (Ideal R)
  body: TwoSidedIdeal.orderIsoIdeal.symm.isSimpleOrder

中文:
实例 :
  签名: 是单序 (理想 R)
  定义体: TwoSidedIdeal.orderIsoIdeal.symm.isSimpleOrder

Depends on / 依赖: TwoSidedIdeal, TwoSidedIdeal.orderIsoIdeal.symm.isSimpleOrder, isSimpleOrder, orderIsoIdeal
-/
instance : IsSimpleOrder (Ideal R) := TwoSidedIdeal.orderIsoIdeal.symm.isSimpleOrder

/--
Instance `IsPrincipalIdealRing.of_isSimpleRing` / 实例 `IsPrincipalIdealRing.of_isSimpleRing`

English:
instance IsPrincipalIdealRing.of_isSimpleRing
  signature: :
  body: ((isSimpleRing_iff_isField _).mp ‹_›).isPrincipalIdealRing

中文:
实例 是主理想环.of_isSimpleRing
  签名: :
  定义体: ((isSimpleRing_iff_isField _).mp ‹_›).isPrincipalIdealRing

Depends on / 依赖: isPrincipalIdealRing, isSimpleRing_iff_isField
-/
instance IsPrincipalIdealRing.of_isSimpleRing :
    IsPrincipalIdealRing R :=
  ((isSimpleRing_iff_isField _).mp ‹_›).isPrincipalIdealRing

/--
Instance `IsDomain.of_isSimpleRing` / 实例 `IsDomain.of_isSimpleRing`

English:
instance IsDomain.of_isSimpleRing
  signature: :
  body: ((isSimpleRing_iff_isField _).mp ‹_›).isDomain

中文:
实例 是整环.of_isSimpleRing
  签名: :
  定义体: ((isSimpleRing_iff_isField _).mp ‹_›).isDomain

Depends on / 依赖: Countable, Countable.LindelofSpace, LindelofSpace, isDomain, isSimpleRing_iff_isField
-/
instance IsDomain.of_isSimpleRing :
    IsDomain R :=
  ((isSimpleRing_iff_isField _).mp ‹_›).isDomain
