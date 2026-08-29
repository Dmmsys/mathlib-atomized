/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Data.Nat.Basic
public import Mathlib.Order.Defs.LinearOrder

/-!
# More `Char` instances

This file provides a `LinearOrder` instance on `Char`. `Char` is the type of Unicode scalar values.
Provides an additional definition to truncate a `Char` to `UInt8` and a theorem on conversion to
`Nat`.
-/

public section

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LinearOrder Char
  body: fun _ => @le_refl Nat _ _
  le_trans := fun _ _ _ => @le_trans Nat _ _ _ _
le_antisymm := fun _ _ h₁ h₂ => Char.ext UInt32.eq_of_toBitVec_eq
    BitVec.le_antisymm h₁ h₂
  lt_iff_le_not_ge := fun _ _ => @lt_iff_le_not_ge Nat _ _ _
  le_total := fun _ _ => @le_total Nat _ _ _
  min := fun a b => if a

中文:
实例 :
  签名: LinearOrder Char
  定义体: fun _ => @le_refl Nat _ _
  le_trans := fun _ _ _ => @le_trans Nat _ _ _ _
le_antisymm := fun _ _ h₁ h₂ => Char.ext UInt32.eq_of_toBitVec_eq
    BitVec.le_antisymm h₁ h₂
  lt_iff_le_not_ge := fun _ _ => @lt_iff_le_not_ge Nat _ _ _
  le_total := fun _ _ => @le_total Nat _ _ _
  min := fun a b => if a

Depends on / 依赖: le_refl
-/
instance : LinearOrder Char where
  le_refl := fun _ => @le_refl Nat _ _
  le_trans := fun _ _ _ => @le_trans Nat _ _ _ _
le_antisymm := fun _ _ h₁ h₂ => Char.ext UInt32.eq_of_toBitVec_eq
    BitVec.le_antisymm h₁ h₂
  lt_iff_le_not_ge := fun _ _ => @lt_iff_le_not_ge Nat _ _ _
  le_total := fun _ _ => @le_total Nat _ _ _
  min := fun a b => if a <= b then a else b
  max := fun a b => if a <= b then b else a
  toDecidableLE := inferInstance
  toDecidableEq := inferInstance
  toDecidableLT := inferInstance
