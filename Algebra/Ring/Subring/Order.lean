/-
Copyright (c) 2021 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
module

public import Mathlib.Algebra.Order.Hom.Ring
public import Mathlib.Algebra.Order.Ring.InjSurj
public import Mathlib.Algebra.Ring.Subring.Defs

/-!
# Subrings of ordered rings

We study subrings of ordered rings and prove their basic properties.

## Main definitions and results

* `Subring.orderedSubtype`: the inclusion `S → R` of a subring as an ordered ring homomorphism
* various ordered instances: a subring of an `IsOrderedRing` or an `IsStrictOrderRing` is again
  the respective kind of ordered ring.
-/

@[expose] public section

namespace Subring

variable {R S : Type*} [Ring R] [PartialOrder R] [SetLike S R] [SubringClass S R]

/-- A subring of an ordered ring is an ordered ring. -/
/-
**Subring.toIsOrderedRing** 是 Mathlib 中的一个实例，位于命名空间 `Subring`。
形式化陈述：toIsOrderedRing [IsOrderedRing R] (s : S) : IsOrderedRing s
参数：s : S。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.isOrderedRing`：∀ {R : Type u_1} {S : Type u_2} [inst 
: Semiring R] [inst_1 : PartialOrder R] [IsOrderedRing R] [inst_3 : Semiring S] 
  [inst_4 : PartialOrd…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
A subring of an ordered ring is an ordered ring.
-/
instance toIsOrderedRing [IsOrderedRing R] (s : S) : IsOrderedRing s :=
  Function.Injective.isOrderedRing Subtype.val rfl rfl (fun _ _ => rfl) (fun _ _ => rfl) .rfl

/-- A subring of a strict ordered ring is a strict ordered ring. -/
/-
**Subring.toIsStrictOrderedRing** 是 Mathlib 中的一个实例，位于命名空间 `Subring`。
形式化陈述：toIsStrictOrderedRing [IsStrictOrderedRing R] (s : S) : IsStrictOrderedRin
g s
参数：s : S。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.isStrictOrderedRing`：∀ {R : Type u_1} {S : Type u_2} 
[inst : Semiring R] [inst_1 : PartialOrder R] [IsStrictOrderedRing R]   [inst_3 
: Semiring S] [inst_4 : Part…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
A subring of a strict ordered ring is a strict ordered ring.
-/
instance toIsStrictOrderedRing [IsStrictOrderedRing R] (s : S) : IsStrictOrderedRing s :=
  Function.Injective.isStrictOrderedRing Subtype.val
    rfl rfl (fun _ _ => rfl) (fun _ _ => rfl) .rfl .rfl

/-- The inclusion `S → R` of a subring, as an ordered ring homomorphism. -/
/-
**Subring.orderedSubtype** 是 Mathlib 中的一个定义，位于命名空间 `Subring`。
形式化陈述：orderedSubtype (s : Subring R) : s ->+*o R where __
参数：s : Subring R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inclusion `S → R` of a subring, as an ordered ring homomorphism.
-/
def orderedSubtype (s : Subring R) : s →+*o R where
  __ := s.subtype
  monotone' := fun _ _ h ↦ h
/-
**Subring.orderedSubtype_coe** 是 Mathlib 中的一个引理，位于命名空间 `Subring`。
形式化陈述：orderedSubtype_coe (s : Subring R) : Subring.orderedSubtype s = Subring.su
btype s
参数：s : Subring R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subring.instSubringClass`：∀ {R : Type u} [inst : NonAssocRing R], Subrin
gClass (Subring R) R
· 使用定理 `OrderRingHom.instRingHomClass`：∀ {α : Type u_2} {β : Type u_3} [inst : N
onAssocSemiring α] [inst_1 : Preorder α] [inst_2 : NonAssocSemiring β]   [inst_3
 : Preorder β], Rin…
-/
lemma orderedSubtype_coe (s : Subring R) : Subring.orderedSubtype s = Subring.subtype s := rfl

end Subring

