/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Algebra.Group.ULift
public import Mathlib.Algebra.GroupWithZero.InjSurj

/-!
# `ULift` instances for groups and monoids with zero

This file defines instances for group and monoid with zero and related structures on `ULift` types.

(Recall `ULift α` is just a "copy" of a type `α` in a higher universe.)
-/

public section

assert_not_exists Ring

universe u

variable {α : Type u}

namespace ULift

/--
Instance `mulZeroOneClass` / 实例 `mulZeroOneClass`

English:
instance mulZeroOneClass
  signature: [MulZeroOneClass α]
  body: Equiv.ulift.injective.mulZeroOneClass _ rfl rfl (by intros; rfl)

中文:
实例 mulZeroOneClass
  签名: [MulZeroOneClass α]
  定义体: Equiv.ulift.injective.mulZeroOneClass _ rfl rfl (by intros; rfl)

Depends on / 依赖: Equiv.ulift.injective.mulZeroOneClass, injective, intros, mulZeroOneClass
-/
instance mulZeroOneClass [MulZeroOneClass α] : MulZeroOneClass (ULift α) :=
  Equiv.ulift.injective.mulZeroOneClass _ rfl rfl (by intros; rfl)

/--
Instance `monoidWithZero` / 实例 `monoidWithZero`

English:
instance monoidWithZero
  signature: [MonoidWithZero α]
  body: Equiv.ulift.injective.monoidWithZero _ rfl rfl (fun _ _ => rfl) fun _ _ => rfl

中文:
实例 monoidWithZero
  签名: [MonoidWithZero α]
  定义体: Equiv.ulift.injective.monoidWithZero _ rfl rfl (fun _ _ => rfl) fun _ _ => rfl

Depends on / 依赖: Equiv.ulift.injective.monoidWithZero, injective, monoidWithZero
-/
instance monoidWithZero [MonoidWithZero α] : MonoidWithZero (ULift α) :=
  Equiv.ulift.injective.monoidWithZero _ rfl rfl (fun _ _ => rfl) fun _ _ => rfl

/--
Instance `commMonoidWithZero` / 实例 `commMonoidWithZero`

English:
instance commMonoidWithZero
  signature: [CommMonoidWithZero α]
  body: Equiv.ulift.injective.commMonoidWithZero _ rfl rfl (fun _ _ => rfl) fun _ _ => rfl

中文:
实例 commMonoidWithZero
  签名: [CommMonoidWithZero α]
  定义体: Equiv.ulift.injective.commMonoidWithZero _ rfl rfl (fun _ _ => rfl) fun _ _ => rfl

Depends on / 依赖: Equiv.ulift.injective.commMonoidWithZero, commMonoidWithZero, injective
-/
instance commMonoidWithZero [CommMonoidWithZero α] : CommMonoidWithZero (ULift α) :=
  Equiv.ulift.injective.commMonoidWithZero _ rfl rfl (fun _ _ => rfl) fun _ _ => rfl

/--
Instance `groupWithZero` / 实例 `groupWithZero`

English:
instance groupWithZero
  signature: [GroupWithZero α]
  body: Equiv.ulift.injective.groupWithZero _ rfl rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) fun _ _ => rfl

中文:
实例 groupWithZero
  签名: [GroupWithZero α]
  定义体: Equiv.ulift.injective.groupWithZero _ rfl rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) fun _ _ => rfl

Depends on / 依赖: Equiv.ulift.injective.groupWithZero, groupWithZero, injective
-/
instance groupWithZero [GroupWithZero α] : GroupWithZero (ULift α) :=
  Equiv.ulift.injective.groupWithZero _ rfl rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) fun _ _ => rfl

/--
Instance `commGroupWithZero` / 实例 `commGroupWithZero`

English:
instance commGroupWithZero
  signature: [CommGroupWithZero α]
  body: Equiv.ulift.injective.commGroupWithZero _ rfl rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) fun _ _ => rfl

中文:
实例 commGroupWithZero
  签名: [CommGroupWithZero α]
  定义体: Equiv.ulift.injective.commGroupWithZero _ rfl rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) fun _ _ => rfl

Depends on / 依赖: Equiv.ulift.injective.commGroupWithZero, commGroupWithZero, injective
-/
instance commGroupWithZero [CommGroupWithZero α] : CommGroupWithZero (ULift α) :=
  Equiv.ulift.injective.commGroupWithZero _ rfl rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) fun _ _ => rfl

end ULift
