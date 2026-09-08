/-
Copyright (c) 2024 Miyahara Kō. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miyahara Kō
-/
module

public import Mathlib.Topology.Instances.Nat

/-!
# Topology on the positive natural numbers

The structure of a metric space on `ℕ+` is introduced in this file, induced from `ℝ`.
-/

public section

noncomputable section

open Metric

namespace PNat

/-
**PNat.** 是 Mathlib 中的一个实例，位于命名空间 `PNat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : MetricSpace ℕ+ := inferInstanceAs (MetricSpace { n : ℕ // 0 < n })
/-
**PNat.dist_eq** 是 Mathlib 中的一个定理，位于命名空间 `PNat`。
形式化陈述：dist_eq (x y : Nat+) : dist x y = |(↑x : Real) - ↑y|
参数：x y : Nat+。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem dist_eq (x y : ℕ+) : dist x y = |(↑x : ℝ) - ↑y| := rfl

@[simp, norm_cast]
/-
**PNat.dist_coe** 是 Mathlib 中的一个定理，位于命名空间 `PNat`。
形式化陈述：dist_coe (x y : Nat+) : dist (↑x : Nat) (↑y : Nat) = dist x y
参数：x y : Nat+。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem dist_coe (x y : ℕ+) : dist (↑x : ℕ) (↑y : ℕ) = dist x y := rfl
/-
**PNat.isUniformEmbedding_coe** 是 Mathlib 中的一个定理，位于命名空间 `PNat`。
形式化陈述：isUniformEmbedding_coe : IsUniformEmbedding ((↑) : Nat+ -> Nat)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isUniformEmbedding_subtype_val`：isUniformEmbedding_subtype_val {p : α ->
 Prop} : IsUniformEmbedding (Subtype.val : Subtype p -> α)
-/
theorem isUniformEmbedding_coe : IsUniformEmbedding ((↑) : ℕ+ → ℕ) := isUniformEmbedding_subtype_val
/-
**PNat.** 是 Mathlib 中的一个实例，位于命名空间 `PNat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : DiscreteTopology ℕ+ := inferInstanceAs (DiscreteTopology { n : ℕ // 0 < n })
/-
**PNat.** 是 Mathlib 中的一个实例，位于命名空间 `PNat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : ProperSpace ℕ+ where
  isCompact_closedBall n r := by
    change IsCompact (((↑) : ℕ+ → ℕ) ⁻¹' closedBall (↑n : ℕ) r)
    rw [Nat.closedBall_eq_Icc]
    exact ((Set.finite_Icc _ _).preimage PNat.coe_injective.injOn).isCompact
/-
**PNat.** 是 Mathlib 中的一个实例，位于命名空间 `PNat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : NoncompactSpace ℕ+ :=
  noncompactSpace_of_neBot <| by simp only [Filter.cocompact_eq_cofinite, Filter.cofinite_neBot]

end PNat

