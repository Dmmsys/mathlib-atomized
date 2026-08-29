/-
Copyright (c) 2016 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Yury Kudryashov
-/
module

import Mathlib.Tactic.ToDual

/-!
# Order definitions for propositions

This file defines orders on `Pi` and `Prop`.
-/

public section

/--
Instance `Pi.hasLe` / 实例 `Pi.hasLe`

English:
instance Pi.hasLe
  signature: {ι : Type*} {π : ι -> Type*} [forall i, LE (π i)]
  body: forall i, x i <= y i

@[to_dual self]

中文:
实例 Pi.hasLe
  签名: {ι : 类型} {π : ι -> 类型} [对任意 i, LE (π i)]
  定义体: forall i, x i <= y i

@[to_dual self]
-/
instance Pi.hasLe {ι : Type*} {π : ι -> Type*} [forall i, LE (π i)] : LE (forall i, π i) where
  le x y := forall i, x i <= y i

@[to_dual self]
/--
theorem `Pi.le_def` / 定理 `Pi.le_def`

English:
theorem Pi.le_def
  given: {ι : Type*} {π : ι -> Type*} [forall i, LE (π i)] {x y : forall i, π i}
  proof: .rfl

中文:
定理 Pi.le_def
  条件: {ι : 类型} {π : ι -> 类型} [对任意 i, LE (π i)] {x y : 对任意 i, π i}
  证明: .rfl
-/
theorem Pi.le_def {ι : Type*} {π : ι -> Type*} [forall i, LE (π i)] {x y : forall i, π i} :
    x <= y ↔ forall i, x i <= y i :=
  .rfl

/--
Instance `Prop.le` / 实例 `Prop.le`

English:
instance Prop.le
  signature: : LE Prop
  body: ⟨(· -> ·)⟩

@[simp]

中文:
实例 Prop.le
  签名: : LE 命题
  定义体: ⟨(· -> ·)⟩

@[simp]
-/
instance Prop.le : LE Prop :=
  ⟨(· -> ·)⟩

@[simp]
/--
theorem `le_Prop_eq` / 定理 `le_Prop_eq`

English:
theorem le_Prop_eq
  statement: ((· <= ·) : Prop -> Prop -> Prop) = (· -> ·)
  proof: rfl

中文:
定理 le_Prop_eq
  结论: ((· <= ·) : 命题 -> 命题 -> 命题) = (· -> ·)
  证明: rfl
-/
theorem le_Prop_eq : ((· <= ·) : Prop -> Prop -> Prop) = (· -> ·) :=
  rfl
