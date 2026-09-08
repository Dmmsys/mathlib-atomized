/-
Copyright (c) 2021 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
module

public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Order.Monoid.Basic
public import Mathlib.Order.Interval.Set.Defs

/-!
# Ordered instances on submonoids
-/

@[expose] public section

assert_not_exists MonoidWithZero

namespace SubmonoidClass
variable {M S : Type*} [SetLike S M]

-- Prefer subclasses of `Monoid` over subclasses of `SubmonoidClass`.
/-- A submonoid of an ordered monoid is an ordered monoid. -/
@[to_additive /-- An `AddSubmonoid` of an ordered additive monoid is an ordered additive monoid. -/]
/-
**SubmonoidClass.** 是 Mathlib 中的一个实例，位于命名空间 `SubmonoidClass`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A submonoid of an ordered monoid is an ordered monoid.
-/
instance (priority := 75) toIsOrderedMonoid [CommMonoid M] [Preorder M] [IsOrderedMonoid M]
    [SubmonoidClass S M] (s : S) : IsOrderedMonoid s :=
  Function.Injective.isOrderedMonoid Subtype.val (fun _ _ => rfl) .rfl

-- Prefer subclasses of `Monoid` over subclasses of `SubmonoidClass`.
/-- A submonoid of an ordered cancellative monoid is an ordered cancellative monoid. -/
@[to_additive AddSubmonoidClass.toIsOrderedCancelAddMonoid
      /-- An `AddSubmonoid` of an ordered cancellative additive monoid is an ordered cancellative
      additive monoid. -/]
/-
**SubmonoidClass.** 是 Mathlib 中的一个实例，位于命名空间 `SubmonoidClass`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 75) toIsOrderedCancelMonoid
    [CommMonoid M] [Preorder M] [IsOrderedCancelMonoid M]
    [SubmonoidClass S M] (s : S) : IsOrderedCancelMonoid s :=
  Function.Injective.isOrderedCancelMonoid Subtype.val (fun _ _ => rfl) .rfl


end SubmonoidClass

namespace Submonoid
variable {M : Type*}

/-- A submonoid of an ordered monoid is an ordered monoid. -/
@[to_additive /-- An `AddSubmonoid` of an ordered additive monoid is an ordered additive monoid. -/]
/-
**Submonoid.toIsOrderedMonoid** 是 Mathlib 中的一个实例，位于命名空间 `Submonoid`。
形式化陈述：toIsOrderedMonoid [CommMonoid M] [Preorder M] [IsOrderedMonoid M] (S : Sub
monoid M) : IsOrderedMonoid S
参数：S : Submonoid M。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `Function.Injective.isOrderedMonoid`：Function.Injective.isOrderedMonoid [
IsOrderedMonoid α] [CommMonoid β] [Preorder β] (f : β -> α) (mul : forall x y, f
 (x * y) = f x * f y) (l…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
A submonoid of an ordered monoid is an ordered monoid.
-/
instance toIsOrderedMonoid [CommMonoid M] [Preorder M] [IsOrderedMonoid M]
    (S : Submonoid M) : IsOrderedMonoid S :=
  Function.Injective.isOrderedMonoid Subtype.val (fun _ _ => rfl) .rfl

/-- A submonoid of an ordered cancellative monoid is an ordered cancellative monoid. -/
@[to_additive AddSubmonoid.toIsOrderedCancelAddMonoid
      /-- An `AddSubmonoid` of an ordered cancellative additive monoid is an ordered cancellative
      additive monoid. -/]
/-
**Submonoid.toIsOrderedCancelMonoid** 是 Mathlib 中的一个实例，位于命名空间 `Submonoid`。
形式化陈述：toIsOrderedCancelMonoid [CommMonoid M] [Preorder M] [IsOrderedCancelMonoid
 M] (S : Submonoid M) : IsOrderedCancelMonoid S
参数：S : Submonoid M。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `Function.Injective.isOrderedCancelMonoid`：Function.Injective.isOrderedCa
ncelMonoid [IsOrderedCancelMonoid α] [CommMonoid β] [Preorder β] (f : β -> α) (m
ul : forall x y, f (x * y) = f…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
instance toIsOrderedCancelMonoid [CommMonoid M] [Preorder M] [IsOrderedCancelMonoid M]
    (S : Submonoid M) : IsOrderedCancelMonoid S :=
  Function.Injective.isOrderedCancelMonoid Subtype.val (fun _ _ => rfl) .rfl

section Preorder
variable (M)
variable [Monoid M] [Preorder M] [MulLeftMono M] {a : M}

/-- The submonoid of elements that are at least `1`. -/
@[to_additive (attr := simps) /-- The submonoid of nonnegative elements. -/]
/-
**Submonoid.oneLE** 是 Mathlib 中的一个定义，位于命名空间 `Submonoid`。
形式化陈述：oneLE : Submonoid M where carrier
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The submonoid of elements that are at least `1`.
-/
def oneLE : Submonoid M where
  carrier := Set.Ici 1
  mul_mem' := one_le_mul
  one_mem' := le_rfl

variable {M}
/-
**Submonoid.mem_oneLE** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：∀ {M : Type u_1} [inst : Monoid M] [inst_1 : Preorder M] [inst_2 : MulLeft
Mono M] {a : M}, a ∈ Submonoid.oneLE M ↔ 1 ≤ a
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[to_additive (attr := simp)] lemma mem_oneLE : a ∈ oneLE M ↔ 1 ≤ a := Iff.rfl

end Preorder
end Submonoid

