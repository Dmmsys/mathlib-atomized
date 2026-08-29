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

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MetricSpace Nat+
  body: inferInstanceAs (MetricSpace { n : Nat // 0 < n })

中文:
实例 :
  签名: MetricSpace 自然数+
  定义体: inferInstanceAs (MetricSpace { n : Nat // 0 < n })

Depends on / 依赖: MetricSpace
-/
instance : MetricSpace Nat+ := inferInstanceAs (MetricSpace { n : Nat // 0 < n })

/--
theorem `dist_eq` / 定理 `dist_eq`

English:
theorem dist_eq
  given: (x y : Nat+)
  statement: dist x y = |(↑x : Real) - ↑y|
  proof: rfl

@[simp, norm_cast]

中文:
定理 dist_eq
  条件: (x y : 自然数+)
  结论: dist x y = |(↑x : 实数) - ↑y|
  证明: rfl

@[simp, norm_cast]
-/
theorem dist_eq (x y : Nat+) : dist x y = |(↑x : Real) - ↑y| := rfl

@[simp, norm_cast]
/--
theorem `dist_coe` / 定理 `dist_coe`

English:
theorem dist_coe
  given: (x y : Nat+)
  statement: dist (↑x : Nat) (↑y : Nat) = dist x y
  proof: rfl

中文:
定理 dist_coe
  条件: (x y : 自然数+)
  结论: dist (↑x : 自然数) (↑y : 自然数) = dist x y
  证明: rfl
-/
theorem dist_coe (x y : Nat+) : dist (↑x : Nat) (↑y : Nat) = dist x y := rfl

/--
theorem `isUniformEmbedding_coe` / 定理 `isUniformEmbedding_coe`

English:
theorem isUniformEmbedding_coe
  statement: IsUniformEmbedding ((↑) : Nat+ -> Nat)
  proof: isUniformEmbedding_subtype_val

中文:
定理 isUniformEmbedding_coe
  结论: IsUniformEmbedding ((↑) : 自然数+ -> 自然数)
  证明: isUniformEmbedding_subtype_val

Depends on / 依赖: isUniformEmbedding_subtype_val
-/
theorem isUniformEmbedding_coe : IsUniformEmbedding ((↑) : Nat+ -> Nat) := isUniformEmbedding_subtype_val

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: DiscreteTopology Nat+
  body: inferInstanceAs (DiscreteTopology { n : Nat // 0 < n })

中文:
实例 :
  签名: DiscreteTopology 自然数+
  定义体: inferInstanceAs (DiscreteTopology { n : Nat // 0 < n })

Depends on / 依赖: DiscreteTopology
-/
instance : DiscreteTopology Nat+ := inferInstanceAs (DiscreteTopology { n : Nat // 0 < n })

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ProperSpace Nat+
  body: by
    change IsCompact (((↑) : Nat+ -> Nat) ⁻¹' closedBall (↑n : Nat) r)
    rw [Nat.closedBall_eq_Icc]
    exact ((Set.finite_Icc _ _).preimage PNat.coe_injective.injOn).isCompact

中文:
实例 :
  签名: 命题erSpace 自然数+
  定义体: by
    change IsCompact (((↑) : Nat+ -> Nat) ⁻¹' closedBall (↑n : Nat) r)
    rw [Nat.closedBall_eq_Icc]
    exact ((Set.finite_Icc _ _).preimage PNat.coe_injective.injOn).isCompact

Depends on / 依赖: IsCompact, Nat.closedBall_eq_Icc, PNat.coe_injective.injOn, Set.finite_Icc, closedBall, closedBall_eq_Icc, coe_injective, finite_Icc, isCompact, preimage
-/
instance : ProperSpace Nat+ where
  isCompact_closedBall n r := by
    change IsCompact (((↑) : Nat+ -> Nat) ⁻¹' closedBall (↑n : Nat) r)
    rw [Nat.closedBall_eq_Icc]
    exact ((Set.finite_Icc _ _).preimage PNat.coe_injective.injOn).isCompact

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: NoncompactSpace Nat+
  body: noncompactSpace_of_neBot by simp only [Filter.cocompact_eq_cofinite, Filter.cofinite_neBot]

中文:
实例 :
  签名: NoncompactSpace 自然数+
  定义体: noncompactSpace_of_neBot by simp only [Filter.cocompact_eq_cofinite, Filter.cofinite_neBot]

Depends on / 依赖: Filter, Filter.cocompact_eq_cofinite, Filter.cofinite_neBot, cocompact_eq_cofinite, cofinite_neBot, noncompactSpace_of_neBot
-/
instance : NoncompactSpace Nat+ :=
noncompactSpace_of_neBot by simp only [Filter.cocompact_eq_cofinite, Filter.cofinite_neBot]

end PNat
