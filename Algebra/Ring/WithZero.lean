/-
Copyright (c) 2020 Mario Carneiro, Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Johan Commelin
-/
module

public import Mathlib.Algebra.GroupWithZero.WithZero
public import Mathlib.Algebra.Ring.Defs

/-!
# Adjoining a zero to a semiring
-/

public section

namespace WithZero
variable {α : Type*}

/--
Instance `instLeftDistribClass` / 实例 `instLeftDistribClass`

English:
instance instLeftDistribClass
  signature: [Mul α] [Add α] [LeftDistribClass α]
  body: by
    cases a; · rfl
    cases b <;> cases c <;> try rfl
    exact congr_arg some (left_distrib _ _ _)

中文:
实例 instLeftDistribClass
  签名: [乘法 α] [加法 α] [LeftDistrib类 α]
  定义体: by
    cases a; · rfl
    cases b <;> cases c <;> try rfl
    exact congr_arg some (left_distrib _ _ _)

Depends on / 依赖: congr_arg, left_distrib
-/
instance instLeftDistribClass [Mul α] [Add α] [LeftDistribClass α] :
    LeftDistribClass (WithZero α) where
  left_distrib a b c := by
    cases a; · rfl
    cases b <;> cases c <;> try rfl
    exact congr_arg some (left_distrib _ _ _)

/--
Instance `instRightDistribClass` / 实例 `instRightDistribClass`

English:
instance instRightDistribClass
  signature: [Mul α] [Add α] [RightDistribClass α]
  body: by
    cases c; · simp
    cases a <;> cases b <;> try rfl
    exact congr_arg some (right_distrib _ _ _)

中文:
实例 instRightDistribClass
  签名: [乘法 α] [加法 α] [RightDistrib类 α]
  定义体: by
    cases c; · simp
    cases a <;> cases b <;> try rfl
    exact congr_arg some (right_distrib _ _ _)

Depends on / 依赖: congr_arg, right_distrib
-/
instance instRightDistribClass [Mul α] [Add α] [RightDistribClass α] :
    RightDistribClass (WithZero α) where
  right_distrib a b c := by
    cases c; · simp
    cases a <;> cases b <;> try rfl
    exact congr_arg some (right_distrib _ _ _)

/--
Instance `instDistrib` / 实例 `instDistrib`

English:
instance instDistrib
  signature: [Distrib α]
  body: left_distrib
  right_distrib := right_distrib

中文:
实例 instDistrib
  签名: [Distrib α]
  定义体: left_distrib
  right_distrib := right_distrib

Depends on / 依赖: left_distrib
-/
instance instDistrib [Distrib α] : Distrib (WithZero α) where
  left_distrib := left_distrib
  right_distrib := right_distrib

/--
Instance `instSemiring` / 实例 `instSemiring`

English:
instance instSemiring
  signature: [Semiring α]

中文:
实例 instSemiring
  签名: [半环 α]
-/
instance instSemiring [Semiring α] : Semiring (WithZero α) where

end WithZero
