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

/--
Definition of `indexOf` / `indexOf` 的定义

English:
definition indexOf
  signature: (lt : α -> α -> Prop) [DecidableRel lt] (x : α)

中文:
定义 indexOf
  签名: (lt : α -> α -> 命题) [DecidableRel lt] (x : α)
-/
def indexOf (lt : α -> α -> Prop) [DecidableRel lt] (x : α) : BinaryTree α -> Option PosNum
  | nil => none
  | node a t₁ t₂ =>
    match cmpUsing lt x a with
| Ordering.lt => PosNum.bit0 < > indexOf lt x t₁
    | Ordering.eq => some PosNum.one
| Ordering.gt => PosNum.bit1 < > indexOf lt x t₂

/-- **Alias** of `BinaryTree.indexOf`. -/
@[deprecated BinaryTree.indexOf (since := "2026-06-07")]
/--
Definition of `_root_.Tree.indexOf` / `_root_.Tree.indexOf` 的定义

English:
abbreviation _root_.Tree.indexOf
  signature: (lt : α -> α -> Prop) [DecidableRel lt] (x : α)
  body: BinaryTree.indexOf lt x

中文:
缩写 _root_.树.indexOf
  签名: (lt : α -> α -> 命题) [DecidableRel lt] (x : α)
  定义体: BinaryTree.indexOf lt x

Depends on / 依赖: BinaryTree, BinaryTree.indexOf, indexOf
-/
abbrev _root_.Tree.indexOf (lt : α -> α -> Prop) [DecidableRel lt] (x : α) : Tree α -> Option PosNum :=
  BinaryTree.indexOf lt x

/--
Definition of `get` / `get` 的定义

English:
definition get
  signature: : PosNum -> BinaryTree α -> Option α

中文:
定义 get
  签名: : PosNum -> BinaryTree α -> 选项类型 α
-/
def get : PosNum -> BinaryTree α -> Option α
  | _, nil => none
  | PosNum.one, node a _t₁ _t₂ => some a
  | PosNum.bit0 n, node _a t₁ _t₂ => t₁.get n
  | PosNum.bit1 n, node _a _t₁ t₂ => t₂.get n

/-- **Alias** of `BinaryTree.get`. -/
@[deprecated BinaryTree.get (since := "2026-06-07")]
/--
Definition of `_root_.Tree.get` / `_root_.Tree.get` 的定义

English:
abbreviation _root_.Tree.get
  signature: (n : PosNum) (t : Tree α)
  body: BinaryTree.get n t

中文:
缩写 _root_.树.get
  签名: (n : PosNum) (t : 树 α)
  定义体: BinaryTree.get n t

Depends on / 依赖: BinaryTree, BinaryTree.get
-/
abbrev _root_.Tree.get (n : PosNum) (t : Tree α) : Option α :=
  BinaryTree.get n t

/--
Definition of `getOrElse` / `getOrElse` 的定义

English:
definition getOrElse
  signature: (n : PosNum) (t : BinaryTree α) (v : α)
  body: (t.get n).getD v

中文:
定义 getOrElse
  签名: (n : PosNum) (t : BinaryTree α) (v : α)
  定义体: (t.get n).getD v

Depends on / 依赖: t.get
-/
def getOrElse (n : PosNum) (t : BinaryTree α) (v : α) : α :=
  (t.get n).getD v

/-- **Alias** of `BinaryTree.getOrElse`. -/
@[deprecated BinaryTree.getOrElse (since := "2026-06-07")]
/--
Definition of `_root_.Tree.getOrElse` / `_root_.Tree.getOrElse` 的定义

English:
abbreviation _root_.Tree.getOrElse
  signature: (n : PosNum) (t : Tree α) (v : α)
  body: BinaryTree.getOrElse n t v

中文:
缩写 _root_.树.getOrElse
  签名: (n : PosNum) (t : 树 α) (v : α)
  定义体: BinaryTree.getOrElse n t v

Depends on / 依赖: BinaryTree, BinaryTree.getOrElse, getOrElse
-/
abbrev _root_.Tree.getOrElse (n : PosNum) (t : Tree α) (v : α) : α :=
  BinaryTree.getOrElse n t v

end BinaryTree
