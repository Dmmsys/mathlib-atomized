/-
Copyright (c) 2021 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
module

public import Mathlib.Algebra.Order.Monoid.Submonoid
public import Mathlib.Algebra.Order.Ring.InjSurj
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Tactic.FastInstance

/-!
# `Order`ed instances for `SubsemiringClass` and `Subsemiring`.
-/

@[expose] public section

namespace SubsemiringClass
variable {R S : Type*} [SetLike S R] (s : S)

/-- A subsemiring of an ordered semiring is an ordered semiring. -/
/-
**SubsemiringClass.toIsOrderedRing** 是 Mathlib 中的一个实例，位于命名空间 `SubsemiringClass`。
形式化陈述：toIsOrderedRing [Semiring R] [PartialOrder R] [IsOrderedRing R] [Subsemiri
ngClass S R] : IsOrderedRing s
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.isOrderedRing`：∀ {R : Type u_1} {S : Type u_2} [inst 
: Semiring R] [inst_1 : PartialOrder R] [IsOrderedRing R] [inst_3 : Semiring S] 
  [inst_4 : PartialOrd…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
A subsemiring of an ordered semiring is an ordered semiring.
-/
instance toIsOrderedRing [Semiring R] [PartialOrder R] [IsOrderedRing R] [SubsemiringClass S R] :
    IsOrderedRing s :=
  Function.Injective.isOrderedRing Subtype.val rfl rfl (fun _ _ => rfl) (fun _ _ => rfl) .rfl

/-- A subsemiring of a strict ordered semiring is a strict ordered semiring. -/
/-
**SubsemiringClass.toIsStrictOrderedRing** 是 Mathlib 中的一个实例，位于命名空间 `SubsemiringC
lass`。
形式化陈述：toIsStrictOrderedRing [Semiring R] [PartialOrder R] [IsStrictOrderedRing R
] [SubsemiringClass S R] : IsStrictOrderedRing s
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.isStrictOrderedRing`：∀ {R : Type u_1} {S : Type u_2} 
[inst : Semiring R] [inst_1 : PartialOrder R] [IsStrictOrderedRing R]   [inst_3 
: Semiring S] [inst_4 : Part…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
A subsemiring of a strict ordered semiring is a strict ordered semiring.
-/
instance toIsStrictOrderedRing [Semiring R] [PartialOrder R] [IsStrictOrderedRing R]
    [SubsemiringClass S R] : IsStrictOrderedRing s :=
  Function.Injective.isStrictOrderedRing Subtype.val
    rfl rfl (fun _ _ => rfl) (fun _ _ => rfl) .rfl .rfl

end SubsemiringClass

namespace Subsemiring

variable {R : Type*}

/-- A subsemiring of an ordered semiring is an ordered semiring. -/
/-
**Subsemiring.toIsOrderedRing** 是 Mathlib 中的一个实例，位于命名空间 `Subsemiring`。
形式化陈述：toIsOrderedRing [Semiring R] [PartialOrder R] [IsOrderedRing R] (s : Subse
miring R) : IsOrderedRing s
参数：s : Subsemiring R。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Subsemiring.instSubsemiringClass`：∀ {R : Type u} [inst : NonAssocSemirin
g R], SubsemiringClass (Subsemiring R) R

--- 原说明 ---
A subsemiring of an ordered semiring is an ordered semiring.
-/
instance toIsOrderedRing [Semiring R] [PartialOrder R] [IsOrderedRing R] (s : Subsemiring R) :
    IsOrderedRing s :=
  SubsemiringClass.toIsOrderedRing _

/-- A subsemiring of a strict ordered semiring is a strict ordered semiring. -/
/-
**Subsemiring.toIsStrictOrderedRing** 是 Mathlib 中的一个实例，位于命名空间 `Subsemiring`。
形式化陈述：toIsStrictOrderedRing [Semiring R] [PartialOrder R] [IsStrictOrderedRing R
] (s : Subsemiring R) : IsStrictOrderedRing s
参数：s : Subsemiring R。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Subsemiring.instSubsemiringClass`：∀ {R : Type u} [inst : NonAssocSemirin
g R], SubsemiringClass (Subsemiring R) R

--- 原说明 ---
A subsemiring of a strict ordered semiring is a strict ordered semiring.
-/
instance toIsStrictOrderedRing [Semiring R] [PartialOrder R] [IsStrictOrderedRing R]
    (s : Subsemiring R) : IsStrictOrderedRing s :=
  SubsemiringClass.toIsStrictOrderedRing _

section nonneg

variable [Semiring R] [PartialOrder R] [IsOrderedRing R]

variable (R) in
/-- The set of nonnegative elements in an ordered semiring, as a subsemiring. -/
@[simps]
/-
**Subsemiring.nonneg** 是 Mathlib 中的一个定义，位于命名空间 `Subsemiring`。
形式化陈述：nonneg : Subsemiring R where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The set of nonnegative elements in an ordered semiring, as a subsemiring.
-/
def nonneg : Subsemiring R where
  __ := AddSubmonoid.nonneg R
  mul_mem' := mul_nonneg
  one_mem' := zero_le_one
/-
**Subsemiring.mem_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `Subsemiring`。
形式化陈述：∀ {R : Type u_1} [inst : Semiring R] [inst_1 : PartialOrder R] [inst_2 : I
sOrderedRing R] {x : R},   x ∈ Subsemiring.nonneg R ↔ 0 ≤ x
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma mem_nonneg {x : R} : x ∈ nonneg R ↔ 0 ≤ x := .rfl

variable (R) in
@[simp]
/-
**Subsemiring.nonneg_toAddSubmonoid** 是 Mathlib 中的一个定理，位于命名空间 `Subsemiring`。
形式化陈述：nonneg_toAddSubmonoid : (nonneg R).toAddSubmonoid = AddSubmonoid.nonneg R
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem nonneg_toAddSubmonoid : (nonneg R).toAddSubmonoid = AddSubmonoid.nonneg R := rfl

end nonneg

end Subsemiring

