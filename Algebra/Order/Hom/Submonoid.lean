/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.Algebra.Group.Submonoid.Operations
public import Mathlib.Algebra.Order.Hom.Monoid

/-!
# Isomorphism of submonoids of ordered monoids
-/

@[expose] public section

/-- The top submonoid is order isomorphic to the whole monoid. -/
@[simps!]
/--
Definition of `Submonoid.topOrderMonoidIso` / `Submonoid.topOrderMonoidIso` 的定义

English:
definition Submonoid.topOrderMonoidIso
  signature: {α : Type*} [Preorder α] [Monoid α]
  body: Submonoid.topEquiv
  map_le_map_iff' := Iff.rfl

中文:
定义 子幺半群.topOrderMonoidIso
  签名: {α : 类型} [预序 α] [幺半群 α]
  定义体: Submonoid.topEquiv
  map_le_map_iff' := Iff.rfl

Depends on / 依赖: Submonoid, Submonoid.topEquiv, topEquiv
-/
def Submonoid.topOrderMonoidIso {α : Type*} [Preorder α] [Monoid α] : (⊤ : Submonoid α) ≃*o α where
  __ := Submonoid.topEquiv
  map_le_map_iff' := Iff.rfl
