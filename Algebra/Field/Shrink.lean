/-
Copyright (c) 2021 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Algebra.Field.TransferInstance
public import Mathlib.Logic.Small.Defs

/-!
# Transfer field structures from `α` to `Shrink α`
-/

public section

noncomputable section

universe v
variable {α : Type*} [Small.{v} α]

namespace Shrink

/-
**Shrink.** 是 Mathlib 中的一个实例，位于命名空间 `Shrink`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [NNRatCast α] : NNRatCast (Shrink.{v} α) := (equivShrink α).symm.nnratCast
/-
**Shrink.** 是 Mathlib 中的一个实例，位于命名空间 `Shrink`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [RatCast α] : RatCast (Shrink.{v} α) := (equivShrink α).symm.ratCast
/-
**Shrink.** 是 Mathlib 中的一个实例，位于命名空间 `Shrink`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [DivisionRing α] : DivisionRing (Shrink.{v} α) := (equivShrink _).symm.divisionRing
/-
**Shrink.** 是 Mathlib 中的一个实例，位于命名空间 `Shrink`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Field α] : Field (Shrink.{v} α) := (equivShrink _).symm.field

end Shrink

