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
instance (priority := 75) toIsOrderedMonoid [CommMonoid M] [Preorder M] [IsOrderedMonoid M]
    [SubmonoidClass S M] (s : S) : IsOrderedMonoid s :=
  Function.Injective.isOrderedMonoid Subtype.val (fun _ _ => rfl) .rfl

-- Prefer subclasses of `Monoid` over subclasses of `SubmonoidClass`.
/-- A submonoid of an ordered cancellative monoid is an ordered cancellative monoid. -/
@[to_additive AddSubmonoidClass.toIsOrderedCancelAddMonoid
      /-- An `AddSubmonoid` of an ordered cancellative additive monoid is an ordered cancellative
      additive monoid. -/]
instance (priority := 75) toIsOrderedCancelMonoid
    [CommMonoid M] [Preorder M] [IsOrderedCancelMonoid M]
    [SubmonoidClass S M] (s : S) : IsOrderedCancelMonoid s :=
  Function.Injective.isOrderedCancelMonoid Subtype.val (fun _ _ => rfl) .rfl


end SubmonoidClass

namespace Submonoid
variable {M : Type*}

/-- A submonoid of an ordered monoid is an ordered monoid. -/
@[to_additive /-- An `AddSubmonoid` of an ordered additive monoid is an ordered additive monoid. -/]
/--
Instance `toIsOrderedMonoid` / 实例 `toIsOrderedMonoid`

English:
instance toIsOrderedMonoid
  signature: [CommMonoid M] [Preorder M] [IsOrderedMonoid M]
  body: Function.Injective.isOrderedMonoid Subtype.val (fun _ _ => rfl) .rfl

中文:
实例 toIsOrderedMonoid
  签名: [交换幺半群 M] [预序 M] [是Ordered幺半群 M]
  定义体: Function.Injective.isOrderedMonoid Subtype.val (fun _ _ => rfl) .rfl

Depends on / 依赖: Function, Function.Injective.isOrderedMonoid, Injective, Subtype, Subtype.val, isOrderedMonoid
-/
instance toIsOrderedMonoid [CommMonoid M] [Preorder M] [IsOrderedMonoid M]
    (S : Submonoid M) : IsOrderedMonoid S :=
  Function.Injective.isOrderedMonoid Subtype.val (fun _ _ => rfl) .rfl

/-- A submonoid of an ordered cancellative monoid is an ordered cancellative monoid. -/
@[to_additive AddSubmonoid.toIsOrderedCancelAddMonoid
      /-- An `AddSubmonoid` of an ordered cancellative additive monoid is an ordered cancellative
      additive monoid. -/]
/--
Instance `toIsOrderedCancelMonoid` / 实例 `toIsOrderedCancelMonoid`

English:
instance toIsOrderedCancelMonoid
  signature: [CommMonoid M] [Preorder M] [IsOrderedCancelMonoid M]
  body: Function.Injective.isOrderedCancelMonoid Subtype.val (fun _ _ => rfl) .rfl

中文:
实例 toIsOrderedCancelMonoid
  签名: [交换幺半群 M] [预序 M] [是OrderedCancel幺半群 M]
  定义体: Function.Injective.isOrderedCancelMonoid Subtype.val (fun _ _ => rfl) .rfl

Depends on / 依赖: Function, Function.Injective.isOrderedCancelMonoid, Injective, Subtype, Subtype.val, isOrderedCancelMonoid
-/
instance toIsOrderedCancelMonoid [CommMonoid M] [Preorder M] [IsOrderedCancelMonoid M]
    (S : Submonoid M) : IsOrderedCancelMonoid S :=
  Function.Injective.isOrderedCancelMonoid Subtype.val (fun _ _ => rfl) .rfl

section Preorder
variable (M)
variable [Monoid M] [Preorder M] [MulLeftMono M] {a : M}

/-- The submonoid of elements that are at least `1`. -/
@[to_additive (attr := simps) /-- The submonoid of nonnegative elements. -/]
/--
Definition of `oneLE` / `oneLE` 的定义

English:
definition oneLE
  signature: : Submonoid M where
  body: Set.Ici 1
  mul_mem' := one_le_mul
  one_mem' := le_rfl

中文:
定义 oneLE
  签名: : 子幺半群 M where
  定义体: Set.Ici 1
  mul_mem' := one_le_mul
  one_mem' := le_rfl

Depends on / 依赖: Set.Ici
-/
def oneLE : Submonoid M where
  carrier := Set.Ici 1
  mul_mem' := one_le_mul
  one_mem' := le_rfl

variable {M}

/--
lemma `mem_oneLE` / 引理 `mem_oneLE`

English:
lemma mem_oneLE
  statement: a in oneLE M ↔ 1 <= a
  proof: Iff.rfl

中文:
引理 mem_oneLE
  结论: a in oneLE M ↔ 1 <= a
  证明: Iff.rfl
-/
@[to_additive (attr := simp)] lemma mem_oneLE : a in oneLE M ↔ 1 <= a := Iff.rfl

end Preorder
end Submonoid
