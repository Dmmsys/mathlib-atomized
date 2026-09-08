/-
Copyright (c) 2022 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
module

public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.FunLike.Basic
public import Mathlib.Data.Finite.Prod

/-!
# Finiteness of `DFunLike` types

We show a type `F` with a `DFunLike F α β` is finite if both `α` and `β` are finite.
This corresponds to the following two pairs of declarations:

* `DFunLike.fintype` is a definition stating all `DFunLike`s are finite if their domain and
  codomain are.
* `DFunLike.finite` is a lemma stating all `DFunLike`s are finite if their domain and
  codomain are.
* `FunLike.fintype` is a non-dependent version of `DFunLike.fintype` and
* `FunLike.finite` is a non-dependent version of `DFunLike.finite`, because dependent instances
  are harder to infer.

You can use these to produce instances for specific `DFunLike` types.
(Although there might be options for `Fintype` instances with better definitional behaviour.)
They can't be instances themselves since they can cause loops.
-/

@[expose] public section

-- `Type` is a reserved word, switched to `Type'`
section Type'

variable (F G : Type*) {α γ : Type*} {β : α → Type*} [DFunLike F α β] [FunLike G α γ]

/-- All `DFunLike`s are finite if their domain and codomain are.

This is not an instance because specific `DFunLike` types might have a better-suited definition.

See also `DFunLike.finite`.
-/
@[instance_reducible]
/-
**DFunLike.fintype** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：DFunLike.fintype [DecidableEq α] [Fintype α] [forall i, Fintype (β i)] : F
intype F
参数：β i。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.coe_injective`：∀ {F : Sort u_1} {α : outParam (Sort u_2)} {β : 
outParam (α → Sort u_3)} [self : DFunLike F α β],   Function.Injective DFunLike.
coe

--- 原说明 ---
All `DFunLike`s are finite if their domain and codomain are.

This is not an instance because specific `DFunLike` types might have a better-su
ited definition.

See also `DFunLike.finite`.
-/
noncomputable def DFunLike.fintype [DecidableEq α] [Fintype α] [∀ i, Fintype (β i)] : Fintype F :=
  Fintype.ofInjective _ DFunLike.coe_injective

/-- All `FunLike`s are finite if their domain and codomain are.

Non-dependent version of `DFunLike.fintype` that might be easier to infer.
This is not an instance because specific `FunLike` types might have a better-suited definition.
-/
@[instance_reducible]
/-
**FunLike.fintype** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：FunLike.fintype [DecidableEq α] [Fintype α] [Fintype γ] : Fintype G
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
All `FunLike`s are finite if their domain and codomain are.

Non-dependent version of `DFunLike.fintype` that might be easier to infer.
This is not an instance because specific `FunLike` types might have a better-sui
ted definition.
-/
noncomputable def FunLike.fintype [DecidableEq α] [Fintype α] [Fintype γ] : Fintype G :=
  DFunLike.fintype G

end Type'

-- `Sort` is a reserved word, switched to `Sort'`
section Sort'

variable (F G : Sort*) {α γ : Sort*} {β : α → Sort*} [DFunLike F α β] [FunLike G α γ]

/-- All `DFunLike`s are finite if their domain and codomain are.

Can't be an instance because it can cause infinite loops.
-/
/-
**DFunLike.finite** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DFunLike.finite [Finite α] [forall i, Finite (β i)] : Finite F
参数：β i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_injective`：Finite.of_injective {α β : Sort*} [Finite β] (f : α
 -> β) (H : Injective f) : Finite α
· 使用定理 `DFunLike.coe_injective`：∀ {F : Sort u_1} {α : outParam (Sort u_2)} {β : 
outParam (α → Sort u_3)} [self : DFunLike F α β],   Function.Injective DFunLike.
coe

--- 原说明 ---
All `DFunLike`s are finite if their domain and codomain are.

Can't be an instance because it can cause infinite loops.
-/
theorem DFunLike.finite [Finite α] [∀ i, Finite (β i)] : Finite F :=
  Finite.of_injective _ DFunLike.coe_injective

/-- All `FunLike`s are finite if their domain and codomain are.

Non-dependent version of `DFunLike.finite` that might be easier to infer.
Can't be an instance because it can cause infinite loops.
-/
/-
**FunLike.finite** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：FunLike.finite [Finite α] [Finite γ] : Finite G
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.finite`：DFunLike.finite [Finite α] [forall i, Finite (β i)] : F
inite F

--- 原说明 ---
All `FunLike`s are finite if their domain and codomain are.

Non-dependent version of `DFunLike.finite` that might be easier to infer.
Can't be an instance because it can cause infinite loops.
-/
theorem FunLike.finite [Finite α] [Finite γ] : Finite G :=
  DFunLike.finite G

end Sort'

-- See note [lower instance priority]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) FunLike.toDecidableEq {F α β : Type*}
    [DecidableEq β] [Fintype α] [FunLike F α β] : DecidableEq F :=
  fun a b ↦ decidable_of_iff ((a : α → β) = b) DFunLike.coe_injective.eq_iff
