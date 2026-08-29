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

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [NNRatCast
  signature: α] : NNRatCast (Shrink.{v} α)
  body: (equivShrink α).symm.nnratCast

中文:
实例 [非负有理数嵌入
  签名: α] : 非负有理数嵌入 (Shrink.{v} α)
  定义体: (equivShrink α).symm.nnratCast
-/
instance [NNRatCast α] : NNRatCast (Shrink.{v} α) := (equivShrink α).symm.nnratCast
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [RatCast
  signature: α] : RatCast (Shrink.{v} α)
  body: (equivShrink α).symm.ratCast

中文:
实例 [有理数嵌入
  签名: α] : 有理数嵌入 (Shrink.{v} α)
  定义体: (equivShrink α).symm.ratCast

Depends on / 依赖: equivShrink, ratCast, symm.ratCast
-/
instance [RatCast α] : RatCast (Shrink.{v} α) := (equivShrink α).symm.ratCast
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [DivisionRing
  signature: α] : DivisionRing (Shrink.{v} α)
  body: (equivShrink _).symm.divisionRing

中文:
实例 [除环
  签名: α] : 除环 (Shrink.{v} α)
  定义体: (equivShrink _).symm.divisionRing

Depends on / 依赖: divisionRing, equivShrink, symm.divisionRing
-/
instance [DivisionRing α] : DivisionRing (Shrink.{v} α) := (equivShrink _).symm.divisionRing
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Field
  signature: α] : Field (Shrink.{v} α)
  body: (equivShrink _).symm.field

中文:
实例 [域
  签名: α] : 域 (Shrink.{v} α)
  定义体: (equivShrink _).symm.field

Depends on / 依赖: equivShrink, symm.field
-/
instance [Field α] : Field (Shrink.{v} α) := (equivShrink _).symm.field

end Shrink
