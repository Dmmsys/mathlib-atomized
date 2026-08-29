/-
Copyright (c) 2024 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Data.Countable.Defs

/-!
# Monoid action by iterates of a map

In this file we define `IterateMulAct f`, `f : α → α`, as a one field structure wrapper over `ℕ`
that acts on `α` by iterates of `f`, `⟨n⟩ • x = f^[n] x`.

It is useful to convert between definitions and theorems about maps and monoid actions.
-/

public section

/--
Definition of `IterateAddAct` / `IterateAddAct` 的定义

English:
structure IterateAddAct
  parameters: {α : Type*} (f : α -> α)
  axioms and operations (1):
    - val : Nat

中文:
结构 IterateAddAct
  参数: {α : 类型} (f : α -> α)
  公理与运算 (1 个):
    - val : 自然数
-/
structure IterateAddAct {α : Type*} (f : α -> α) where
  /-- The value of `n : IterateAddAct f`. -/
  val : Nat

/-- A structure with a single field `val : ℕ` that acts on `α` by `⟨n⟩ • x = f^[n] x`. -/
@[to_additive (attr := ext)]
/--
Definition of `IterateMulAct` / `IterateMulAct` 的定义

English:
structure IterateMulAct
  parameters: {α : Type*} (f : α -> α)
  axioms and operations (1):
    - val : Nat

中文:
结构 IterateMulAct
  参数: {α : 类型} (f : α -> α)
  公理与运算 (1 个):
    - val : 自然数
-/
structure IterateMulAct {α : Type*} (f : α -> α) where
  /-- The value of `n : IterateMulAct f`. -/
  val : Nat

namespace IterateMulAct

variable {α : Type*} {f : α -> α}

@[to_additive]
/--
Instance `instCountable` / 实例 `instCountable`

English:
instance instCountable
  signature: : Countable (IterateMulAct f)
  body: Function.Injective.countable fun _ _ => IterateMulAct.ext

@[to_additive]

中文:
实例 instCountable
  签名: : Countable (IterateMulAct f)
  定义体: Function.Injective.countable fun _ _ => IterateMulAct.ext

@[to_additive]

Depends on / 依赖: Function, Function.Injective.countable, Injective, IterateMulAct, IterateMulAct.ext, countable
-/
instance instCountable : Countable (IterateMulAct f) :=
  Function.Injective.countable fun _ _ => IterateMulAct.ext

@[to_additive]
/--
Instance `instCommMonoid` / 实例 `instCommMonoid`

English:
instance instCommMonoid
  signature: : CommMonoid (IterateMulAct f) where
  body: ⟨0⟩
  mul m n := ⟨m.1 + n.1⟩
  mul_assoc a b c := by ext; apply Nat.add_assoc
  one_mul _ := by ext; apply Nat.zero_add
  mul_one _ := rfl
  mul_comm _ _ := by ext; apply Nat.add_comm
  npow n a := ⟨n * a.val⟩
  npow_zero _ := by ext; apply Nat.zero_mul
  npow_succ n a := by ext; apply Nat.succ_mul


中文:
实例 instCommMonoid
  签名: : CommMonoid (IterateMulAct f) where
  定义体: ⟨0⟩
  mul m n := ⟨m.1 + n.1⟩
  mul_assoc a b c := by ext; apply Nat.add_assoc
  one_mul _ := by ext; apply Nat.zero_add
  mul_one _ := rfl
  mul_comm _ _ := by ext; apply Nat.add_comm
  npow n a := ⟨n * a.val⟩
  npow_zero _ := by ext; apply Nat.zero_mul
  npow_succ n a := by ext; apply Nat.succ_mul

-/
instance instCommMonoid : CommMonoid (IterateMulAct f) where
  one := ⟨0⟩
  mul m n := ⟨m.1 + n.1⟩
  mul_assoc a b c := by ext; apply Nat.add_assoc
  one_mul _ := by ext; apply Nat.zero_add
  mul_one _ := rfl
  mul_comm _ _ := by ext; apply Nat.add_comm
  npow n a := ⟨n * a.val⟩
  npow_zero _ := by ext; apply Nat.zero_mul
  npow_succ n a := by ext; apply Nat.succ_mul

@[to_additive]
/--
Instance `instMulAction` / 实例 `instMulAction`

English:
instance instMulAction
  signature: : MulAction (IterateMulAct f) α where
  body: f^[n.val] x
  one_smul _ := rfl
  mul_smul _ _ := Function.iterate_add_apply f _ _

@[to_additive (attr := simp)]

中文:
实例 instMulAction
  签名: : MulAction (IterateMulAct f) α where
  定义体: f^[n.val] x
  one_smul _ := rfl
  mul_smul _ _ := Function.iterate_add_apply f _ _

@[to_additive (attr := simp)]

Depends on / 依赖: n.val
-/
instance instMulAction : MulAction (IterateMulAct f) α where
  smul n x := f^[n.val] x
  one_smul _ := rfl
  mul_smul _ _ := Function.iterate_add_apply f _ _

@[to_additive (attr := simp)]
/--
theorem `mk_smul` / 定理 `mk_smul`

English:
theorem mk_smul
  given: (n : Nat) (x : α)
  statement: mk (f := f) n • x = f^[n] x
  proof: rfl

中文:
定理 mk_smul
  条件: (n : 自然数) (x : α)
  结论: mk (f := f) n • x = f^[n] x
  证明: rfl
-/
theorem mk_smul (n : Nat) (x : α) : mk (f := f) n • x = f^[n] x := rfl

end IterateMulAct
