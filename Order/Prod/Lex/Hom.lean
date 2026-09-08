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
/-
**Prod.Lex.toLexOrderHom** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Prod.Lex.toLexOrderHom {α β : Type*} [PartialOrder α] [Preorder β] : α × β
 ->o α ×ₗ β where toFun
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Prod.Lex.toLex_mono`：toLex_mono : Monotone (toLex : α × β -> α ×ₗ β)

--- 原说明 ---
`toLex` as an `OrderHom`.
-/
def Prod.Lex.toLexOrderHom {α β : Type*} [PartialOrder α] [Preorder β] :
    α × β →o α ×ₗ β where
  toFun := toLex
  monotone' := Prod.Lex.toLex_mono
