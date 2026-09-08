/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

public import Mathlib.Init

/-!
# Typeclasses for commuting heterogeneous operations

The three classes in this file are for two-argument functions where one input is of type `α`,
the output is of type `β` and the other input is of type `α` or `β`.
They express the property that permuting arguments of type `α` does not change the result.

## Main definitions

* `IsSymmOp`: for `op : α → α → β`, `op a b = op b a`.
* `LeftCommutative`: for `op : α → β → β`, `op a₁ (op a₂ b) = op a₂ (op a₁ b)`.
* `RightCommutative`: for `op : β → α → β`, `op (op b a₁) a₂ = op (op b a₂) a₁`.
-/

public section

universe u v

variable {α : Sort u} {β : Sort v}

/-- `IsSymmOp op` where `op : α → α → β` says that `op` is a symmetric operation,
i.e. `op a b = op b a`.
It is the natural generalisation of `Std.Commutative` (`β = α`) and `IsSymm` (`β = Prop`). -/
/-
**IsSymmOp** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：{α : Sort u} → {β : Sort v} → (α → α → β) → Prop
参数：α → α → β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`IsSymmOp op` where `op : α → α → β` says that `op` is a symmetric operation,
i.e. `op a b = op b a`.
It is the natural generalisation of `Std.Commutative` (`β = α`) and `IsSymm` (`β
 = Prop`).
-/
class IsSymmOp (op : α → α → β) : Prop where
  /-- A symmetric operation satisfies `op a b = op b a`. -/
  symm_op : ∀ a b, op a b = op b a

/-- `LeftCommutative op` where `op : α → β → β` says that `op` is a left-commutative operation,
i.e. `op a₁ (op a₂ b) = op a₂ (op a₁ b)`. -/
/-
**LeftCommutative** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：{α : Sort u} → {β : Sort v} → (α → β → β) → Prop
参数：α → β → β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`LeftCommutative op` where `op : α → β → β` says that `op` is a left-commutative
 operation,
i.e. `op a₁ (op a₂ b) = op a₂ (op a₁ b)`.
-/
class LeftCommutative (op : α → β → β) : Prop where
  /-- A left-commutative operation satisfies `op a₁ (op a₂ b) = op a₂ (op a₁ b)`. -/
  left_comm : (a₁ a₂ : α) → (b : β) → op a₁ (op a₂ b) = op a₂ (op a₁ b)

/-- `RightCommutative op` where `op : β → α → β` says that `op` is a right-commutative operation,
i.e. `op (op b a₁) a₂ = op (op b a₂) a₁`. -/
/-
**RightCommutative** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：{α : Sort u} → {β : Sort v} → (β → α → β) → Prop
参数：β → α → β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`RightCommutative op` where `op : β → α → β` says that `op` is a right-commutati
ve operation,
i.e. `op (op b a₁) a₂ = op (op b a₂) a₁`.
-/
class RightCommutative (op : β → α → β) : Prop where
  /-- A right-commutative operation satisfies `op (op b a₁) a₂ = op (op b a₂) a₁`. -/
  right_comm : (b : β) → (a₁ a₂ : α) → op (op b a₁) a₂ = op (op b a₂) a₁
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) isSymmOp_of_isCommutative (α : Sort u) (op : α → α → α)
    [Std.Commutative op] : IsSymmOp op where symm_op := Std.Commutative.comm
/-
**IsSymmOp.flip_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsSymmOp.flip_eq (op : α -> α -> β) [IsSymmOp op] : flip op = op
参数：op : α -> α -> β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsSymmOp.symm_op`：∀ {α : Sort u} {β : Sort v} {op : α → α → β} [self : I
sSymmOp op] (a b : α), op a b = op b a
-/
theorem IsSymmOp.flip_eq (op : α → α → β) [IsSymmOp op] : flip op = op :=
  funext fun a ↦ funext fun b ↦ (IsSymmOp.symm_op a b).symm
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {f : α → β → β} [h : LeftCommutative f] : RightCommutative (fun x y ↦ f y x) :=
  ⟨fun _ _ _ ↦ (h.left_comm _ _ _).symm⟩
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {f : β → α → β} [h : RightCommutative f] : LeftCommutative (fun x y ↦ f y x) :=
  ⟨fun _ _ _ ↦ (h.right_comm _ _ _).symm⟩
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {f : α → α → α} [hc : Std.Commutative f] [ha : Std.Associative f] : LeftCommutative f :=
  ⟨fun a b c ↦ by rw [← ha.assoc, hc.comm a, ha.assoc]⟩
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {f : α → α → α} [hc : Std.Commutative f] [ha : Std.Associative f] : RightCommutative f :=
  ⟨fun a b c ↦ by rw [ha.assoc, hc.comm b, ha.assoc]⟩
