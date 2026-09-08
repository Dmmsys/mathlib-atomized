/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
module

public import Mathlib.Topology.MetricSpace.Bounded
public import Mathlib.Topology.Order.Bornology

/-!
# The reals are equipped with their order bornology

This file contains results related to the order bornology on (non-negative) real numbers.
We prove that `ℝ` and `ℝ≥0` are equipped with the order topology and bornology.
-/

public section

assert_not_exists IsTopologicalRing UniformContinuousConstSMul UniformOnFun

open Metric Set

/-
**Real.instIsOrderBornology** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Real.instIsOrderBornology : IsOrderBornology Real
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOrderBornology.of_isCompactIcc`：∀ {α : Type u} [inst : PseudoMetricSpa
ce α] [inst_1 : Preorder α] [CompactIccSpace α] (x : α),   (∀ (r : ℝ), BddBelow 
(Metric.closedBall x r…
· 使用定理 `ConditionallyCompleteLinearOrder.toCompactIccSpace`：∀ (α : Type u_2) [in
st : ConditionallyCompleteLinearOrder α] [inst_1 : TopologicalSpace α] [OrderTop
ology α],   CompactIccSpace α
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.closedBall_eq_Icc`：Real.closedBall_eq_Icc {x r : Real} : closedBall
 x r = Icc (x - r) (x + r)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `zero_sub`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 0 - a = -a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
instance Real.instIsOrderBornology : IsOrderBornology ℝ :=
  .of_isCompactIcc 0 (by simp [closedBall_eq_Icc]) (by simp [closedBall_eq_Icc])

namespace NNReal

/-
**NNReal.** 是 Mathlib 中的一个实例，位于命名空间 `NNReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : OrderTopology ℝ≥0 :=
  orderTopology_of_ordConnected (t := Ici 0)
/-
**NNReal.** 是 Mathlib 中的一个实例，位于命名空间 `NNReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsOrderBornology ℝ≥0 := .of_isCompactIcc 0 (by simp) fun r ↦ by
  obtain hr | hr := le_or_gt 0 r <;> simp [closedBall_zero_eq_Icc, *]

end NNReal

