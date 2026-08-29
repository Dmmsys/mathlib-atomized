/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Algebra.Order.Group.Multiset
public import Mathlib.Algebra.Order.Monoid.Canonical.Defs

/-!
# Multisets as ordered monoids

The `IsOrderedCancelAddMonoid` and `CanonicallyOrderedAdd` instances on `Multiset α`

-/

public section

variable {α : Type*}

namespace Multiset

open List

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsOrderedCancelAddMonoid (Multiset α)
  body: fun _ _ => add_le_add_left
  le_of_add_le_add_left := fun _ _ _ => le_of_add_le_add_left

中文:
实例 :
  签名: IsOrderedCancelAddMonoid (Multiset α)
  定义体: fun _ _ => add_le_add_left
  le_of_add_le_add_left := fun _ _ _ => le_of_add_le_add_left

Depends on / 依赖: add_le_add_left
-/
instance : IsOrderedCancelAddMonoid (Multiset α) where
  add_le_add_left := fun _ _ => add_le_add_left
  le_of_add_le_add_left := fun _ _ _ => le_of_add_le_add_left

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CanonicallyOrderedAdd (Multiset α)
  body: le_add_left
  le_self_add := le_add_right
  exists_add_of_le h := exists_add_of_le h

中文:
实例 :
  签名: CanonicallyOrderedAdd (Multiset α)
  定义体: le_add_left
  le_self_add := le_add_right
  exists_add_of_le h := exists_add_of_le h

Depends on / 依赖: le_add_left
-/
instance : CanonicallyOrderedAdd (Multiset α) where
  le_add_self := le_add_left
  le_self_add := le_add_right
  exists_add_of_le h := exists_add_of_le h

end Multiset
