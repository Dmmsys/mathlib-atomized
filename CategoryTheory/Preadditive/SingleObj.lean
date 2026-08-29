/-
Copyright (c) 2021 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.CategoryTheory.Preadditive.Basic
public import Mathlib.CategoryTheory.SingleObj

/-!
# `SingleObj α` is preadditive when `α` is a ring.

-/

public section


namespace CategoryTheory

variable {α : Type*} [Ring α]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Preadditive (SingleObj α)
  body: mul_add g f f'
  comp_add _ _ _ f g g' := add_mul g g' f

中文:
实例 :
  签名: Preadditive (SingleObj α)
  定义体: mul_add g f f'
  comp_add _ _ _ f g g' := add_mul g g' f

Depends on / 依赖: mul_add
-/
instance : Preadditive (SingleObj α) where
  add_comp _ _ _ f f' g := mul_add g f f'
  comp_add _ _ _ f g g' := add_mul g g' f

-- TODO define `PreAddCat` (with additive functors as morphisms), and `Ring ⥤ PreAddCat`.
end CategoryTheory
