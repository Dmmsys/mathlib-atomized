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

/-
**ULift.mulZeroOneClass** 是 Mathlib 中的一个实例，位于命名空间 `ULift`。
形式化陈述：mulZeroOneClass [MulZeroOneClass α] : MulZeroOneClass (ULift α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance mulZeroOneClass [MulZeroOneClass α] : MulZeroOneClass (ULift α) :=
  Equiv.ulift.injective.mulZeroOneClass _ rfl rfl (by intros; rfl)
/-
**ULift.monoidWithZero** 是 Mathlib 中的一个实例，位于命名空间 `ULift`。
形式化陈述：monoidWithZero [MonoidWithZero α] : MonoidWithZero (ULift α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance monoidWithZero [MonoidWithZero α] : MonoidWithZero (ULift α) :=
  Equiv.ulift.injective.monoidWithZero _ rfl rfl (fun _ _ => rfl) fun _ _ => rfl
/-
**ULift.commMonoidWithZero** 是 Mathlib 中的一个实例，位于命名空间 `ULift`。
形式化陈述：commMonoidWithZero [CommMonoidWithZero α] : CommMonoidWithZero (ULift α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance commMonoidWithZero [CommMonoidWithZero α] : CommMonoidWithZero (ULift α) :=
  Equiv.ulift.injective.commMonoidWithZero _ rfl rfl (fun _ _ => rfl) fun _ _ => rfl
/-
**ULift.groupWithZero** 是 Mathlib 中的一个实例，位于命名空间 `ULift`。
形式化陈述：groupWithZero [GroupWithZero α] : GroupWithZero (ULift α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance groupWithZero [GroupWithZero α] : GroupWithZero (ULift α) :=
  Equiv.ulift.injective.groupWithZero _ rfl rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) fun _ _ => rfl
/-
**ULift.commGroupWithZero** 是 Mathlib 中的一个实例，位于命名空间 `ULift`。
形式化陈述：commGroupWithZero [CommGroupWithZero α] : CommGroupWithZero (ULift α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance commGroupWithZero [CommGroupWithZero α] : CommGroupWithZero (ULift α) :=
  Equiv.ulift.injective.commGroupWithZero _ rfl rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) fun _ _ => rfl

end ULift

