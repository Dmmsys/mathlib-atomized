/-
Copyright (c) 2019 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.Algebra.Group.PUnit
public import Mathlib.Algebra.Order.AddGroupWithTop
/-!
# Instances on PUnit

This file collects facts about ordered algebraic structures on the one-element type.
-/

public section

namespace PUnit

/--
Instance `canonicallyOrderedAdd` / 实例 `canonicallyOrderedAdd`

English:
instance canonicallyOrderedAdd
  signature: : CanonicallyOrderedAdd PUnit where
  body: ⟨unit, by subsingleton⟩
  le_add_self _ _ := trivial
  le_self_add _ _ := trivial

中文:
实例 canonicallyOrderedAdd
  签名: : CanonicallyOrderedAdd PUnit where
  定义体: ⟨unit, by subsingleton⟩
  le_add_self _ _ := trivial
  le_self_add _ _ := trivial

Depends on / 依赖: subsingleton
-/
instance canonicallyOrderedAdd : CanonicallyOrderedAdd PUnit where
  exists_add_of_le {_ _} _ := ⟨unit, by subsingleton⟩
  le_add_self _ _ := trivial
  le_self_add _ _ := trivial

/--
Instance `isOrderedCancelAddMonoid` / 实例 `isOrderedCancelAddMonoid`

English:
instance isOrderedCancelAddMonoid
  signature: : IsOrderedCancelAddMonoid PUnit where
  body: trivial
  add_le_add_left := by intros; rfl

中文:
实例 isOrderedCancelAddMonoid
  签名: : IsOrderedCancelAddMonoid PUnit where
  定义体: trivial
  add_le_add_left := by intros; rfl
-/
instance isOrderedCancelAddMonoid : IsOrderedCancelAddMonoid PUnit where
  le_of_add_le_add_left _ _ _ _ := trivial
  add_le_add_left := by intros; rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LinearOrderedAddCommMonoidWithTop PUnit
  body: ()
  le_top _ := le_rfl
  top_add' _ := rfl
  isAddLeftRegular_of_ne_top := by simp

中文:
实例 :
  签名: LinearOrderedAddCommMonoidWithTop PUnit
  定义体: ()
  le_top _ := le_rfl
  top_add' _ := rfl
  isAddLeftRegular_of_ne_top := by simp
-/
instance : LinearOrderedAddCommMonoidWithTop PUnit where
  top := ()
  le_top _ := le_rfl
  top_add' _ := rfl
  isAddLeftRegular_of_ne_top := by simp

end PUnit
