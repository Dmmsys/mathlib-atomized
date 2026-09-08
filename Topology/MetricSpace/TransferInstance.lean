/-
Copyright (c) 2025 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang
-/
module

public import Mathlib.Topology.MetricSpace.Basic

/-!
# Transfer metric space structures across `Equiv`s

In this file, we transfer a distance and (pseudo-)metric space structure across an equivalence.

-/

public section

variable {α β : Type*}

namespace Equiv

variable (e : α ≃ β)

-- See note [instance transfer via equivalence]
/-- Transfer a `Dist` across an `Equiv` -/
/-
**Equiv.dist** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：{α : Type u_1} → {β : Type u_2} → α ≃ β → [Dist β] → Dist α
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Transfer a `Dist` across an `Equiv`
-/
protected abbrev dist (e : α ≃ β) [Dist β] : Dist α := ⟨fun x y ↦ dist (e.toFun x) (e.toFun y)⟩

/-- Transfer a `PseudoMetricSpace` across an `Equiv` -/
/-
**Equiv.pseudometricSpace** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：{α : Type u_1} → {β : Type u_2} → [PseudoMetricSpace β] → α ≃ β → PseudoMe
tricSpace α
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Transfer a `PseudoMetricSpace` across an `Equiv`
-/
protected abbrev pseudometricSpace [PseudoMetricSpace β] (e : α ≃ β) : PseudoMetricSpace α :=
  .induced e.toFun ‹_›

/-- Transfer a `MetricSpace` across an `Equiv` -/
/-
**Equiv.metricSpace** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：{α : Type u_1} → {β : Type u_2} → [MetricSpace β] → α ≃ β → MetricSpace α
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e

--- 原说明 ---
Transfer a `MetricSpace` across an `Equiv`
-/
protected abbrev metricSpace [MetricSpace β] (e : α ≃ β) : MetricSpace α :=
  .induced e.toFun e.injective ‹_›

end Equiv

