/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Logic.Equiv.List

/-!
# Equivalences involving `Array`
-/

@[expose] public section


namespace Equiv

/--
Definition of `arrayEquivList` / `arrayEquivList` 的定义

English:
definition arrayEquivList
  signature: (α : Type*)
  body: Array.toList
  invFun := Array.mk

中文:
定义 arrayEquivList
  签名: (α : 类型)
  定义体: Array.toList
  invFun := Array.mk

Depends on / 依赖: Array.toList, toList
-/
def arrayEquivList (α : Type*) : Array α ≃ List α where
  toFun := Array.toList
  invFun := Array.mk

end Equiv

/- Porting note: removed instances for what would be ported as `Traversable (Array α)` and
`LawfulTraversable (Array α)`. These would

1. be implemented directly in terms of `Array` functionality for efficiency, rather than being the
traversal of some other type transported along an equivalence to `Array α` (as the traversable
instance for `array` was)

2. belong in `Mathlib/Control/Traversable/Instances.lean` instead of this file. -/

-- namespace Array'

-- open Function

-- variable {n : ℕ}

-- instance : Traversable (Array' n) :=
-- @Equiv.traversable (flip Vector n) _ (fun α => Equiv.vectorEquivArray α n) _

-- instance : LawfulTraversable (Array' n) :=
-- @Equiv.isLawfulTraversable (flip Vector n) _ (fun α => Equiv.vectorEquivArray α n) _ _

-- end Array'

/--
Instance `Array.encodable` / 实例 `Array.encodable`

English:
instance Array.encodable
  signature: {α} [Encodable α]
  body: Encodable.ofEquiv _ (Equiv.arrayEquivList _)

中文:
实例 Array.encodable
  签名: {α} [Encodable α]
  定义体: Encodable.ofEquiv _ (Equiv.arrayEquivList _)

Depends on / 依赖: Encodable, Encodable.ofEquiv, Equiv.arrayEquivList, arrayEquivList, ofEquiv
-/
instance Array.encodable {α} [Encodable α] : Encodable (Array α) :=
  Encodable.ofEquiv _ (Equiv.arrayEquivList _)

/--
Instance `Array.countable` / 实例 `Array.countable`

English:
instance Array.countable
  signature: {α} [Countable α]
  body: Countable.of_equiv _ (Equiv.arrayEquivList α).symm

中文:
实例 Array.countable
  签名: {α} [Countable α]
  定义体: Countable.of_equiv _ (Equiv.arrayEquivList α).symm

Depends on / 依赖: Countable, Countable.of_equiv, Equiv.arrayEquivList, arrayEquivList, of_equiv
-/
instance Array.countable {α} [Countable α] : Countable (Array α) :=
  Countable.of_equiv _ (Equiv.arrayEquivList α).symm
