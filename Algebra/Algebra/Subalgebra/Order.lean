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

/-
**Subalgebra.toIsOrderedRing** 是 Mathlib 中的一个实例，位于命名空间 `Subalgebra`。
形式化陈述：toIsOrderedRing [CommSemiring R] [Semiring A] [PartialOrder A] [IsOrderedR
ing A] [Algebra R A] (S : Subalgebra R A) : IsOrderedRing S
参数：S : Subalgebra R A。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance toIsOrderedRing [CommSemiring R] [Semiring A] [PartialOrder A] [IsOrderedRing A]
    [Algebra R A] (S : Subalgebra R A) : IsOrderedRing S :=
  S.toSubsemiring.toIsOrderedRing
/-
**Subalgebra.toIsStrictOrderedRing** 是 Mathlib 中的一个实例，位于命名空间 `Subalgebra`。
形式化陈述：toIsStrictOrderedRing [CommSemiring R] [Semiring A] [PartialOrder A] [IsSt
rictOrderedRing A] [Algebra R A] (S : Subalgebra R A) : IsStrictOrderedRing S
参数：S : Subalgebra R A。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance toIsStrictOrderedRing [CommSemiring R] [Semiring A] [PartialOrder A]
    [IsStrictOrderedRing A] [Algebra R A] (S : Subalgebra R A) : IsStrictOrderedRing S :=
  S.toSubsemiring.toIsStrictOrderedRing

end Subalgebra

