/-
Copyright (c) 2022 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
module

public import Mathlib.Data.Fintype.Sum

/-!
# Finiteness of sum types
-/

public section

variable {α β : Type*}

namespace Finite

/-
**Finite.** 是 Mathlib 中的一个实例，位于命名空间 `Finite`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Finite α] [Finite β] : Finite (α ⊕ β) := by
  have := Fintype.ofFinite α
  have := Fintype.ofFinite β
  infer_instance
/-
**Finite.sum_left** 是 Mathlib 中的一个定理，位于命名空间 `Finite`。
形式化陈述：sum_left (β) [Finite (α oplus β)] : Finite α
参数：β；α oplus β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_injective`：Finite.of_injective {α β : Sort*} [Finite β] (f : α
 -> β) (H : Injective f) : Finite α
· 使用定理 `Sum.inl_injective`：inl_injective : Function.Injective (inl : α -> α oplu
s β)
-/
theorem sum_left (β) [Finite (α ⊕ β)] : Finite α :=
  of_injective (Sum.inl : α → α ⊕ β) Sum.inl_injective
/-
**Finite.sum_right** 是 Mathlib 中的一个定理，位于命名空间 `Finite`。
形式化陈述：sum_right (α) [Finite (α oplus β)] : Finite β
参数：α；α oplus β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_injective`：Finite.of_injective {α β : Sort*} [Finite β] (f : α
 -> β) (H : Injective f) : Finite α
· 使用定理 `Sum.inr_injective`：inr_injective : Function.Injective (inr : β -> α oplu
s β)
-/
theorem sum_right (α) [Finite (α ⊕ β)] : Finite β :=
  of_injective (Sum.inr : β → α ⊕ β) Sum.inr_injective
/-
**Finite.** 是 Mathlib 中的一个实例，位于命名空间 `Finite`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {α β : Sort*} [Finite α] [Finite β] : Finite (α ⊕' β) :=
  of_equiv _ ((Equiv.psumEquivSum _ _).symm.trans (Equiv.plift.psumCongr Equiv.plift))
/-
**Finite.psum_left** 是 Mathlib 中的一个定理，位于命名空间 `Finite`。
形式化陈述：psum_left {α β : Sort*} [Finite (α oplus' β)] : Finite α
参数：α oplus' β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_injective`：Finite.of_injective {α β : Sort*} [Finite β] (f : α
 -> β) (H : Injective f) : Finite α
· 使用定理 `PSum.inl_injective`：inl_injective : Function.Injective (PSum.inl : α -> 
α oplus' β)
-/
theorem psum_left {α β : Sort*} [Finite (α ⊕' β)] : Finite α :=
  of_injective (PSum.inl : α → α ⊕' β) PSum.inl_injective
/-
**Finite.psum_right** 是 Mathlib 中的一个定理，位于命名空间 `Finite`。
形式化陈述：psum_right {α β : Sort*} [Finite (α oplus' β)] : Finite β
参数：α oplus' β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_injective`：Finite.of_injective {α β : Sort*} [Finite β] (f : α
 -> β) (H : Injective f) : Finite α
· 使用定理 `PSum.inr_injective`：inr_injective : Function.Injective (PSum.inr : β -> 
α oplus' β)
-/
theorem psum_right {α β : Sort*} [Finite (α ⊕' β)] : Finite β :=
  of_injective (PSum.inr : β → α ⊕' β) PSum.inr_injective

end Finite

