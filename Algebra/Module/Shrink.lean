/-
Copyright (c) 2021 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Algebra.Group.Shrink
public import Mathlib.Algebra.Module.TransferInstance

/-!
# Transfer module and algebra structures from `α` to `Shrink α`
-/

@[expose] public noncomputable section

universe v
variable {R α : Type*} [Small.{v} α] [Semiring R] [AddCommMonoid α] [Module R α]

namespace Shrink

/-
**Shrink.** 是 Mathlib 中的一个实例，位于命名空间 `Shrink`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Module R (Shrink.{v} α) := (equivShrink α).symm.module R

variable (R α) in
/-- Shrinking `α` to a smaller universe preserves module structure. -/
@[simps!]
/-
**Shrink.linearEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Shrink`。
形式化陈述：linearEquiv : Shrink.{v} α ≃ₗ[R] α
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
Shrinking `α` to a smaller universe preserves module structure.
-/
def linearEquiv : Shrink.{v} α ≃ₗ[R] α := (equivShrink α).symm.linearEquiv _

end Shrink

