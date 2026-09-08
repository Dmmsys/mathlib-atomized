/-
Copyright (c) 2019 mathlib community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Wojciech Nawrocki
-/
module

public import Mathlib.Data.Num.Basic
public import Mathlib.Data.Ordering.Basic
public import Mathlib.Data.Tree.Basic

/-!
# Binary tree get operation

In this file we define `Tree.indexOf`, `Tree.get`, and `Tree.getOrElse`.
These definitions were moved from the main file to avoid a dependency on `Num`.

## References

<https://leanprover-community.github.io/archive/stream/113488-general/topic/tactic.20question.html#170999997>
-/

@[expose] public section

namespace BinaryTree

variable {α : Type*}

/-- Finds the index of an element in the tree assuming the tree has been
constructed according to the provided decidable order on its elements.
If it hasn't, the result will be incorrect. If it has, but the element
is not in the tree, returns none. -/
/-
**BinaryTree.indexOf** 是 Mathlib 中的一个定义，位于命名空间 `BinaryTree`。
形式化陈述：{α : Type u_1} → (lt : α → α → Prop) → [DecidableRel lt] → α → BinaryTree 
α → Option PosNum
参数：lt : α → α → Prop。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Finds the index of an element in the tree assuming the tree has been
constructed according to the provided decidable order on its elements.
If it hasn't, the result will be incorrect. If it has, but the element
is not in the tree, returns none.
-/
def indexOf (lt : α → α → Prop) [DecidableRel lt] (x : α) : BinaryTree α → Option PosNum
  | nil => none
  | node a t₁ t₂ =>
    match cmpUsing lt x a with
    | Ordering.lt => PosNum.bit0 <$> indexOf lt x t₁
    | Ordering.eq => some PosNum.one
    | Ordering.gt => PosNum.bit1 <$> indexOf lt x t₂

/-- **Alias** of `BinaryTree.indexOf`. -/
@[deprecated BinaryTree.indexOf (since := "2026-06-07")]
/-
**BinaryTree._root_.Tree.indexOf** 是 Mathlib 中的一个缩写定义，位于命名空间 `BinaryTree`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
**Alias** of `BinaryTree.indexOf`.
-/
abbrev _root_.Tree.indexOf (lt : α → α → Prop) [DecidableRel lt] (x : α) : Tree α → Option PosNum :=
  BinaryTree.indexOf lt x

/-- Retrieves an element uniquely determined by a `PosNum` from the tree,
taking the following path to get to the element:
- `bit0` - go to left child
- `bit1` - go to right child
- `PosNum.one` - retrieve from here -/
/-
**BinaryTree.get** 是 Mathlib 中的一个定义，位于命名空间 `BinaryTree`。
形式化陈述：{α : Type u_1} → PosNum → BinaryTree α → Option α
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Retrieves an element uniquely determined by a `PosNum` from the tree,
taking the following path to get to the element:
- `bit0` - go to left child
- `bit1` - go to right child
- `PosNum.one` - retrieve from here
-/
def get : PosNum → BinaryTree α → Option α
  | _, nil => none
  | PosNum.one, node a _t₁ _t₂ => some a
  | PosNum.bit0 n, node _a t₁ _t₂ => t₁.get n
  | PosNum.bit1 n, node _a _t₁ t₂ => t₂.get n

/-- **Alias** of `BinaryTree.get`. -/
@[deprecated BinaryTree.get (since := "2026-06-07")]
/-
**BinaryTree._root_.Tree.get** 是 Mathlib 中的一个缩写定义，位于命名空间 `BinaryTree`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
**Alias** of `BinaryTree.get`.
-/
abbrev _root_.Tree.get (n : PosNum) (t : Tree α) : Option α :=
  BinaryTree.get n t

/-- Retrieves an element from the tree, or the provided default value
if the index is invalid. See `BinaryTree.get`. -/
/-
**BinaryTree.getOrElse** 是 Mathlib 中的一个定义，位于命名空间 `BinaryTree`。
形式化陈述：getOrElse (n : PosNum) (t : BinaryTree α) (v : α) : α
参数：n : PosNum；t : BinaryTree α；v : α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Retrieves an element from the tree, or the provided default value
if the index is invalid. See `BinaryTree.get`.
-/
def getOrElse (n : PosNum) (t : BinaryTree α) (v : α) : α :=
  (t.get n).getD v

/-- **Alias** of `BinaryTree.getOrElse`. -/
@[deprecated BinaryTree.getOrElse (since := "2026-06-07")]
/-
**BinaryTree._root_.Tree.getOrElse** 是 Mathlib 中的一个缩写定义，位于命名空间 `BinaryTree`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
**Alias** of `BinaryTree.getOrElse`.
-/
abbrev _root_.Tree.getOrElse (n : PosNum) (t : Tree α) (v : α) : α :=
  BinaryTree.getOrElse n t v

end BinaryTree

