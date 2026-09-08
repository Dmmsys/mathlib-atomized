/-
Copyright (c) 2021 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
module

public import Mathlib.Data.SetLike.Basic
public import Mathlib.Data.Fintype.Powerset

/-!
# Set-like fintype

This file contains a fintype instance for set-like objects such as subgroups. If `SetLike A B`
and `Fintype B` then `Fintype A`.
-/

public section


namespace SetLike

/-- TODO: It should be possible to obtain a computable version of this for most
SetLike objects. If we add those instances, we should remove this one. -/
/-
**SetLike.** 是 Mathlib 中的一个实例，位于命名空间 `SetLike`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
TODO: It should be possible to obtain a computable version of this for most
SetLike objects. If we add those instances, we should remove this one.
-/
noncomputable instance (priority := 100) {A B : Type*} [SetLike A B] [Fintype B] : Fintype A :=
  Fintype.ofInjective SetLike.coe SetLike.coe_injective

-- See note [lower instance priority]
/-
**SetLike.** 是 Mathlib 中的一个实例，位于命名空间 `SetLike`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) {A B : Type*} [SetLike A B] [Finite B] : Finite A :=
  Finite.of_injective SetLike.coe SetLike.coe_injective

end SetLike

