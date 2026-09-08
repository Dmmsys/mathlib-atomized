/-
Copyright (c) 2023 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Algebra.Order.Sub.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Notation.Prod

/-!
# Products of `OrderedSub` types.
-/

public section

assert_not_exists MonoidWithZero

variable {α β : Type*}

/-
**Prod.orderedSub** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Prod.orderedSub [Preorder α] [Add α] [Sub α] [OrderedSub α] [Sub β] [Preor
der β] [Add β] [OrderedSub β] : OrderedSub (α × β) where tsub_le_iff_right _ _ _
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `tsub_le_iff_right`：tsub_le_iff_right [LE α] [Add α] [Sub α] [OrderedSub 
α] {a b c : α} : a - b <= c ↔ a <= c + b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
-/
instance Prod.orderedSub
    [Preorder α] [Add α] [Sub α] [OrderedSub α] [Sub β] [Preorder β] [Add β] [OrderedSub β] :
    OrderedSub (α × β) where
  tsub_le_iff_right _ _ _ :=
  ⟨fun w ↦ ⟨tsub_le_iff_right.mp w.1, tsub_le_iff_right.mp w.2⟩,
   fun w ↦ ⟨tsub_le_iff_right.mpr w.1, tsub_le_iff_right.mpr w.2⟩⟩
/-
**Pi.orderedSub** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Pi.orderedSub {ι : Type*} {α : ι -> Type*} [forall i, Preorder (α i)] [for
all i, Add (α i)] [forall i, Sub (α i)] [forall i, OrderedSub (α i)] : OrderedSu
b ((i : ι) -> α i) where tsub_le_iff_right _ _ _
参数：α i；α i；α i；α i。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `tsub_le_iff_right`：tsub_le_iff_right [LE α] [Add α] [Sub α] [OrderedSub 
α] {a b c : α} : a - b <= c ↔ a <= c + b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
-/
instance Pi.orderedSub {ι : Type*} {α : ι → Type*}
    [∀ i, Preorder (α i)] [∀ i, Add (α i)] [∀ i, Sub (α i)] [∀ i, OrderedSub (α i)] :
    OrderedSub ((i : ι) → α i) where
  tsub_le_iff_right _ _ _ :=
  ⟨fun w i ↦ tsub_le_iff_right.mp (w i), fun w i ↦ tsub_le_iff_right.mpr (w i)⟩
