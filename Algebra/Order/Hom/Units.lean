/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.Algebra.Group.Units.Equiv
public import Mathlib.Algebra.Order.Hom.Monoid
public import Mathlib.Algebra.Order.Monoid.Units

/-! # Isomorphism of ordered monoids descends to units
-/

@[expose] public section

variable {α β : Type*} [Preorder α] [Monoid α] [Preorder β] [Monoid β] (e : α ≃*o β)

/-- An isomorphism of ordered monoids descends to their units. -/
@[simps!]
/--
Definition of `OrderMonoidIso.unitsCongr` / `OrderMonoidIso.unitsCongr` 的定义

English:
definition OrderMonoidIso.unitsCongr
  signature: : αˣ ≃*o βˣ where
  body: Units.mapEquiv e.toMulEquiv
  map_le_map_iff' {x y} := by simp [← Units.val_le_val]

中文:
定义 OrderMonoidIso.unitsCongr
  签名: : αˣ ≃*o βˣ where
  定义体: Units.mapEquiv e.toMulEquiv
  map_le_map_iff' {x y} := by simp [← Units.val_le_val]

Depends on / 依赖: Units.mapEquiv, e.toMulEquiv, mapEquiv, toMulEquiv
-/
def OrderMonoidIso.unitsCongr : αˣ ≃*o βˣ where
  __ := Units.mapEquiv e.toMulEquiv
  map_le_map_iff' {x y} := by simp [← Units.val_le_val]

/--
lemma `OrderMonoidIso.unitsCongr_symm_apply` / 引理 `OrderMonoidIso.unitsCongr_symm_apply`

English:
lemma OrderMonoidIso.unitsCongr_symm_apply
  given: (x : βˣ)
  statement: e.unitsCongr.symm x = e.symm x
  proof: rfl

中文:
引理 OrderMonoidIso.unitsCongr_symm_apply
  条件: (x : βˣ)
  结论: e.unitsCongr.symm x = e.symm x
  证明: rfl
-/
lemma OrderMonoidIso.unitsCongr_symm_apply (x : βˣ) : e.unitsCongr.symm x = e.symm x := rfl
