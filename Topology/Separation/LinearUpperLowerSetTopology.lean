/-
Copyright (c) 2025 Miyahara Kō. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miyahara Kō
-/
module

public import Mathlib.Topology.Order.UpperLowerSetTopology
public import Mathlib.Topology.Separation.Regular

/-!
# Linear upper or lower sets topologies are completely normal
-/

public section

open Set Topology.IsUpperSet

/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := low) {α : Type*}
    [TopologicalSpace α] [LinearOrder α] [Topology.IsUpperSet α] : CompletelyNormalSpace α where
  completely_normal s t hcst hsct := by
    obtain (rfl | ⟨a, ha⟩) := s.eq_empty_or_nonempty
    case inl => simp
    obtain (rfl | ⟨b, hb⟩) := t.eq_empty_or_nonempty
    case inl => simp
    exfalso
    grewrite [← singleton_subset_iff.mpr ha, ← singleton_subset_iff.mpr hb] at hcst hsct
    conv at hcst => equals a < b => simp
    conv at hsct => equals b < a => simp
    exact lt_asymm hcst hsct
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := low) {α : Type*}
    [TopologicalSpace α] [LinearOrder α] [Topology.IsLowerSet α] :
    CompletelyNormalSpace α :=
  inferInstanceAs (CompletelyNormalSpace αᵒᵈ)
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CompletelyNormalSpace Prop :=
  inferInstance
