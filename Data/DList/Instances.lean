/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon
-/
module

public import Batteries.Data.DList.Lemmas
public import Mathlib.Control.Traversable.Equiv
public import Mathlib.Control.Traversable.Instances

/-!
# Traversable instance for DLists

This file provides the equivalence between `List α` and `DList α` and the traversable instance
for `DList`.
-/

@[expose] public section


open Function Equiv

namespace Batteries

variable (α : Type*)

/-- The natural equivalence between lists and difference lists, using
`DList.ofList` and `DList.toList`. -/
/-
**Batteries.DList.listEquivDList** 是 Mathlib 中的一个定义，位于命名空间 `Batteries.DList`。
形式化陈述：(α : Type u_1) → List α ≃ Batteries.DList α
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Batteries.DList.toList_ofList`：∀ {α : Type u_1} (l : List α), (Batteries
.DList.ofList l).toList = l
· 使用定理 `Batteries.DList.ofList_toList`：∀ {α : Type u_1} (l : Batteries.DList α),
 Batteries.DList.ofList l.toList = l

--- 原说明 ---
The natural equivalence between lists and difference lists, using
`DList.ofList` and `DList.toList`.
-/
def DList.listEquivDList : List α ≃ DList α where
  toFun := DList.ofList
  invFun := DList.toList
  left_inv _ := DList.toList_ofList _
  right_inv _ := DList.ofList_toList _
/-
**Batteries.** 是 Mathlib 中的一个实例，位于命名空间 `Batteries`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Traversable DList :=
  Equiv.traversable DList.listEquivDList
/-
**Batteries.** 是 Mathlib 中的一个实例，位于命名空间 `Batteries`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : LawfulTraversable DList :=
  Equiv.isLawfulTraversable DList.listEquivDList

end Batteries

