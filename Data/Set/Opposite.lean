/-
Copyright (c) 2022 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

public import Mathlib.Data.Opposite
public import Mathlib.Data.Set.Operations

/-!
# The opposite of a set

The opposite of a set `s` is simply the set obtained by taking the opposite of each member of `s`.
-/

@[expose] public section

variable {α : Type*}

open Opposite

namespace Set

/-- The opposite of a set `s` is the set obtained by taking the opposite of each member of `s`. -/
/-
**Set.op** 是 Mathlib 中的一个定义，位于命名空间 `Set`。
形式化陈述：{α : Type u_1} → Set α → Set αᵒᵖ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The opposite of a set `s` is the set obtained by taking the opposite of each mem
ber of `s`.
-/
protected def op (s : Set α) : Set αᵒᵖ :=
  unop ⁻¹' s

/-- The unop of a set `s` is the set obtained by taking the unop of each member of `s`. -/
/-
**Set.unop** 是 Mathlib 中的一个定义，位于命名空间 `Set`。
形式化陈述：{α : Type u_1} → Set αᵒᵖ → Set α
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The unop of a set `s` is the set obtained by taking the unop of each member of `
s`.
-/
protected def unop (s : Set αᵒᵖ) : Set α :=
  op ⁻¹' s

@[simp]
/-
**Set.mem_op** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：mem_op {s : Set α} {a : αᵒᵖ} : a in s.op ↔ unop a in s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_op {s : Set α} {a : αᵒᵖ} : a ∈ s.op ↔ unop a ∈ s :=
  Iff.rfl

@[simp 1100]
/-
**Set.op_mem_op** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：op_mem_op {s : Set α} {a : α} : op a in s.op ↔ a in s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem op_mem_op {s : Set α} {a : α} : op a ∈ s.op ↔ a ∈ s := by rfl

@[simp]
/-
**Set.mem_unop** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：mem_unop {s : Set αᵒᵖ} {a : α} : a in s.unop ↔ op a in s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_unop {s : Set αᵒᵖ} {a : α} : a ∈ s.unop ↔ op a ∈ s :=
  Iff.rfl

@[simp 1100]
/-
**Set.unop_mem_unop** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：unop_mem_unop {s : Set αᵒᵖ} {a : αᵒᵖ} : unop a in s.unop ↔ a in s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem unop_mem_unop {s : Set αᵒᵖ} {a : αᵒᵖ} : unop a ∈ s.unop ↔ a ∈ s := by rfl

@[simp]
/-
**Set.op_unop** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：op_unop (s : Set α) : s.op.unop = s
参数：s : Set α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem op_unop (s : Set α) : s.op.unop = s := rfl

@[simp]
/-
**Set.unop_op** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：unop_op (s : Set αᵒᵖ) : s.unop.op = s
参数：s : Set αᵒᵖ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem unop_op (s : Set αᵒᵖ) : s.unop.op = s := rfl

/-- The members of the opposite of a set are in bijection with the members of the set itself. -/
@[simps]
/-
**Set.opEquiv_self** 是 Mathlib 中的一个定义，位于命名空间 `Set`。
形式化陈述：opEquiv_self (s : Set α) : s.op ≃ s
参数：s : Set α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The members of the opposite of a set are in bijection with the members of the se
t itself.
-/
def opEquiv_self (s : Set α) : s.op ≃ s :=
  ⟨fun x ↦ ⟨unop x, x.2⟩, fun x ↦ ⟨op x, x.2⟩, fun _ ↦ rfl, fun _ ↦ rfl⟩

/-- Taking opposites as an equivalence of powersets. -/
@[simps]
/-
**Set.opEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Set`。
形式化陈述：opEquiv : Set α ≃ Set αᵒᵖ
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Set.op_unop`：op_unop (s : Set α) : s.op.unop = s
· 使用定理 `Set.unop_op`：unop_op (s : Set αᵒᵖ) : s.unop.op = s

--- 原说明 ---
Taking opposites as an equivalence of powersets.
-/
def opEquiv : Set α ≃ Set αᵒᵖ :=
  ⟨Set.op, Set.unop, op_unop, unop_op⟩

@[simp]
/-
**Set.singleton_op** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：singleton_op (x : α) : ({x} : Set α).op = {op x}
参数：x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Opposite.unop_injective`：unop_injective : Function.Injective (unop : αᵒᵖ
 -> α)
· 使用定理 `Opposite.op_injective`：op_injective : Function.Injective (op : α -> αᵒᵖ)
-/
theorem singleton_op (x : α) : ({x} : Set α).op = {op x} := by
  ext
  constructor
  · apply unop_injective
  · apply op_injective

@[simp]
/-
**Set.singleton_unop** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：singleton_unop (x : αᵒᵖ) : ({x} : Set αᵒᵖ).unop = {unop x}
参数：x : αᵒᵖ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Opposite.op_injective`：op_injective : Function.Injective (op : α -> αᵒᵖ)
· 使用定理 `Opposite.unop_injective`：unop_injective : Function.Injective (unop : αᵒᵖ
 -> α)
-/
theorem singleton_unop (x : αᵒᵖ) : ({x} : Set αᵒᵖ).unop = {unop x} := by
  ext
  constructor
  · apply op_injective
  · apply unop_injective

@[simp 1100]
/-
**Set.singleton_op_unop** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：singleton_op_unop (x : α) : ({op x} : Set αᵒᵖ).unop = {x}
参数：x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Opposite.op_injective`：op_injective : Function.Injective (op : α -> αᵒᵖ)
· 使用定理 `Opposite.unop_injective`：unop_injective : Function.Injective (unop : αᵒᵖ
 -> α)
-/
theorem singleton_op_unop (x : α) : ({op x} : Set αᵒᵖ).unop = {x} := by
  ext
  constructor
  · apply op_injective
  · apply unop_injective

@[simp 1100]
/-
**Set.singleton_unop_op** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：singleton_unop_op (x : αᵒᵖ) : ({unop x} : Set α).op = {x}
参数：x : αᵒᵖ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Opposite.unop_injective`：unop_injective : Function.Injective (unop : αᵒᵖ
 -> α)
· 使用定理 `Opposite.op_injective`：op_injective : Function.Injective (op : α -> αᵒᵖ)
-/
theorem singleton_unop_op (x : αᵒᵖ) : ({unop x} : Set α).op = {x} := by
  ext
  constructor
  · apply unop_injective
  · apply op_injective

end Set

