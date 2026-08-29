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

/--
Definition of `DList.listEquivDList` / `DList.listEquivDList` 的定义

English:
definition DList.listEquivDList
  signature: : List α ≃ DList α where
  body: DList.ofList
  invFun := DList.toList
  left_inv _ := DList.toList_ofList _
  right_inv _ := DList.ofList_toList _

中文:
定义 DList.listEquivDList
  签名: : List α ≃ DList α where
  定义体: DList.ofList
  invFun := DList.toList
  left_inv _ := DList.toList_ofList _
  right_inv _ := DList.ofList_toList _

Depends on / 依赖: DList.ofList, ofList
-/
def DList.listEquivDList : List α ≃ DList α where
  toFun := DList.ofList
  invFun := DList.toList
  left_inv _ := DList.toList_ofList _
  right_inv _ := DList.ofList_toList _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Traversable DList
  body: Equiv.traversable DList.listEquivDList

中文:
实例 :
  签名: Traversable DList
  定义体: Equiv.traversable DList.listEquivDList

Depends on / 依赖: DList.listEquivDList, Equiv.traversable, listEquivDList, traversable
-/
instance : Traversable DList :=
  Equiv.traversable DList.listEquivDList

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LawfulTraversable DList
  body: Equiv.isLawfulTraversable DList.listEquivDList

中文:
实例 :
  签名: LawfulTraversable DList
  定义体: Equiv.isLawfulTraversable DList.listEquivDList

Depends on / 依赖: DList.listEquivDList, Equiv.isLawfulTraversable, isLawfulTraversable, listEquivDList
-/
instance : LawfulTraversable DList :=
  Equiv.isLawfulTraversable DList.listEquivDList

end Batteries
