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

/-- A structure with a single field `val : ℕ`
that additively acts on `α` by `⟨n⟩ +ᵥ x = f^[n] x`. -/
/-
**IterateAddAct** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：{α : Type u_1} → (α → α) → Type
参数：α → α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A structure with a single field `val : ℕ`
that additively acts on `α` by `⟨n⟩ +ᵥ x = f^[n] x`.
-/
structure IterateAddAct {α : Type*} (f : α → α) where
  /-- The value of `n : IterateAddAct f`. -/
  val : ℕ

/-- A structure with a single field `val : ℕ` that acts on `α` by `⟨n⟩ • x = f^[n] x`. -/
@[to_additive (attr := ext)]
/-
**IterateMulAct** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：{α : Type u_1} → (α → α) → Type
参数：α → α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A structure with a single field `val : ℕ` that acts on `α` by `⟨n⟩ • x = f^[n] x
`.
-/
structure IterateMulAct {α : Type*} (f : α → α) where
  /-- The value of `n : IterateMulAct f`. -/
  val : ℕ

namespace IterateMulAct

variable {α : Type*} {f : α → α}

@[to_additive]
/-
**IterateMulAct.instCountable** 是 Mathlib 中的一个实例，位于命名空间 `IterateMulAct`。
形式化陈述：instCountable : Countable (IterateMulAct f)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.countable`：∀ {α : Sort u} {β : Sort v} [Countable β] 
{f : α → β}, Function.Injective f → Countable α
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `IterateMulAct.ext`：∀ {α : Type u_1} {f : α → α} {x y : IterateMulAct f},
 x.val = y.val → x = y
-/
instance instCountable : Countable (IterateMulAct f) :=
  Function.Injective.countable fun _ _ ↦ IterateMulAct.ext

@[to_additive]
/-
**IterateMulAct.instCommMonoid** 是 Mathlib 中的一个实例，位于命名空间 `IterateMulAct`。
形式化陈述：instCommMonoid : CommMonoid (IterateMulAct f) where one
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
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
/-
**IterateMulAct.instMulAction** 是 Mathlib 中的一个实例，位于命名空间 `IterateMulAct`。
形式化陈述：instMulAction : MulAction (IterateMulAct f) α where smul n x
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instMulAction : MulAction (IterateMulAct f) α where
  smul n x := f^[n.val] x
  one_smul _ := rfl
  mul_smul _ _ := Function.iterate_add_apply f _ _

@[to_additive (attr := simp)]
/-
**IterateMulAct.mk_smul** 是 Mathlib 中的一个定理，位于命名空间 `IterateMulAct`。
形式化陈述：mk_smul (n : Nat) (x : α) : mk (f
参数：n : Nat；x : α。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mk_smul (n : ℕ) (x : α) : mk (f := f) n • x = f^[n] x := rfl

end IterateMulAct

