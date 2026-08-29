/-
Copyright (c) 2021 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
module

public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.Algebra.Ring.Subsemiring.Order

/-!
# Order instances on subalgebras
-/

public section

namespace Subalgebra

variable {R A : Type*}

/--
Instance `toIsOrderedRing` / 实例 `toIsOrderedRing`

English:
instance toIsOrderedRing
  signature: [CommSemiring R] [Semiring A] [PartialOrder A] [IsOrderedRing A]
  body: S.toSubsemiring.toIsOrderedRing

中文:
实例 toIsOrderedRing
  签名: [交换半环 R] [半环 A] [偏序 A] [是Ordered环 A]
  定义体: S.toSubsemiring.toIsOrderedRing

Depends on / 依赖: S.toSubsemiring.toIsOrderedRing, toIsOrderedRing, toSubsemiring
-/
instance toIsOrderedRing [CommSemiring R] [Semiring A] [PartialOrder A] [IsOrderedRing A]
    [Algebra R A] (S : Subalgebra R A) : IsOrderedRing S :=
  S.toSubsemiring.toIsOrderedRing

/--
Instance `toIsStrictOrderedRing` / 实例 `toIsStrictOrderedRing`

English:
instance toIsStrictOrderedRing
  signature: [CommSemiring R] [Semiring A] [PartialOrder A]
  body: S.toSubsemiring.toIsStrictOrderedRing

中文:
实例 toIsStrictOrderedRing
  签名: [交换半环 R] [半环 A] [偏序 A]
  定义体: S.toSubsemiring.toIsStrictOrderedRing

Depends on / 依赖: S.toSubsemiring.toIsStrictOrderedRing, toIsStrictOrderedRing, toSubsemiring
-/
instance toIsStrictOrderedRing [CommSemiring R] [Semiring A] [PartialOrder A]
    [IsStrictOrderedRing A] [Algebra R A] (S : Subalgebra R A) : IsStrictOrderedRing S :=
  S.toSubsemiring.toIsStrictOrderedRing

end Subalgebra
