/-
Copyright (c) 2025 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
module

public import Mathlib.Data.Prod.Lex
public import Mathlib.Order.Hom.Basic

/-!
# Order homomorphism for `Prod.Lex`
-/

@[expose] public section

/-- `toLex` as an `OrderHom`. -/
@[simps]
/--
Definition of `Prod.Lex.toLexOrderHom` / `Prod.Lex.toLexOrderHom` 的定义

English:
definition Prod.Lex.toLexOrderHom
  signature: {α β : Type*} [PartialOrder α] [Preorder β]
  body: toLex
  monotone' := Prod.Lex.toLex_mono

中文:
定义 Prod.Lex.toLexOrderHom
  签名: {α β : 类型} [PartialOrder α] [Preorder β]
  定义体: toLex
  monotone' := Prod.Lex.toLex_mono

Depends on / 依赖: _eq_iff_mk, toLocalizationMap
-/
def Prod.Lex.toLexOrderHom {α β : Type*} [PartialOrder α] [Preorder β] :
    α × β ->o α ×ₗ β where
  toFun := toLex
  monotone' := Prod.Lex.toLex_mono
