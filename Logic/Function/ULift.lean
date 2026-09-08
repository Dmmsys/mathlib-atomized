/-
Copyright (c) 2016 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
module

public import Mathlib.Init

/-!
# `ULift` and `PLift`
-/

public section

/-
**ULift.down_injective** 是 Mathlib 中的一个定理，位于命名空间 `ULift`。
形式化陈述：∀ {α : Type u_1}, Function.Injective ULift.down
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ULift.down_injective {α : Type*} : Function.Injective (@ULift.down α)
  | ⟨a⟩, ⟨b⟩, _ => by congr
/-
**ULift.down_inj** 是 Mathlib 中的一个定理，位于命名空间 `ULift`。
形式化陈述：∀ {α : Type u_1} {a b : ULift.{u_2, u_1} α}, a.down = b.down ↔ a = b
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ULift.down_injective`：∀ {α : Type u_1}, Function.Injective ULift.down
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
@[simp] theorem ULift.down_inj {α : Type*} {a b : ULift α} : a.down = b.down ↔ a = b :=
  ⟨fun h ↦ ULift.down_injective h, fun h ↦ by rw [h]⟩

variable {α : Sort*}
/-
**PLift.down_injective** 是 Mathlib 中的一个定理，位于命名空间 `PLift`。
形式化陈述：∀ {α : Sort u_1}, Function.Injective PLift.down
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem PLift.down_injective : Function.Injective (@PLift.down α)
  | ⟨a⟩, ⟨b⟩, _ => by congr
/-
**PLift.down_inj** 是 Mathlib 中的一个定理，位于命名空间 `PLift`。
形式化陈述：∀ {α : Sort u_1} {a b : PLift α}, a.down = b.down ↔ a = b
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PLift.down_injective`：∀ {α : Sort u_1}, Function.Injective PLift.down
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
@[simp] theorem PLift.down_inj {a b : PLift α} : a.down = b.down ↔ a = b :=
  ⟨fun h ↦ PLift.down_injective h, fun h ↦ by rw [h]⟩
