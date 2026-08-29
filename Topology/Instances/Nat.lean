/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
module

public import Mathlib.Order.Lattice.Nat
public import Mathlib.Topology.Instances.Int

/-!
# Topology on the natural numbers

The structure of a metric space on `ℕ` is introduced in this file, induced from `ℝ`.
-/

public section

noncomputable section

open Filter Metric Set Topology

namespace Nat

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Dist Nat
  body: ⟨fun x y => dist (x : Real) y⟩

中文:
实例 :
  签名: Dist 自然数
  定义体: ⟨fun x y => dist (x : Real) y⟩
-/
noncomputable instance : Dist Nat :=
  ⟨fun x y => dist (x : Real) y⟩

/--
theorem `dist_eq` / 定理 `dist_eq`

English:
theorem dist_eq
  given: (x y : Nat)
  statement: dist x y = |(x : Real) - y|
  proof: rfl

中文:
定理 dist_eq
  条件: (x y : 自然数)
  结论: dist x y = |(x : 实数) - y|
  证明: rfl
-/
theorem dist_eq (x y : Nat) : dist x y = |(x : Real) - y| := rfl

/--
theorem `dist_coe_int` / 定理 `dist_coe_int`

English:
theorem dist_coe_int
  given: (x y : Nat)
  statement: dist (x : Int) (y : Int) = dist x y
  proof: rfl

@[norm_cast, simp]

中文:
定理 dist_coe_int
  条件: (x y : 自然数)
  结论: dist (x : 整数) (y : 整数) = dist x y
  证明: rfl

@[norm_cast, simp]
-/
theorem dist_coe_int (x y : Nat) : dist (x : Int) (y : Int) = dist x y := rfl

@[norm_cast, simp]
/--
theorem `dist_cast_real` / 定理 `dist_cast_real`

English:
theorem dist_cast_real
  given: (x y : Nat)
  statement: dist (x : Real) y = dist x y
  proof: rfl

中文:
定理 dist_cast_real
  条件: (x y : 自然数)
  结论: dist (x : 实数) y = dist x y
  证明: rfl
-/
theorem dist_cast_real (x y : Nat) : dist (x : Real) y = dist x y := rfl

/--
theorem `pairwise_one_le_dist` / 定理 `pairwise_one_le_dist`

English:
theorem pairwise_one_le_dist
  statement: Pairwise fun m n : Nat => 1 <= dist m n
  proof: fun _ _ hne =>
Int.pairwise_one_le_dist mod_cast hne

中文:
定理 pairwise_one_le_dist
  结论: Pairwise fun m n : 自然数 => 1 <= dist m n
  证明: fun _ _ hne =>
Int.pairwise_one_le_dist mod_cast hne
-/
theorem pairwise_one_le_dist : Pairwise fun m n : Nat => 1 <= dist m n := fun _ _ hne =>
Int.pairwise_one_le_dist mod_cast hne

/--
theorem `isUniformEmbedding_coe_real` / 定理 `isUniformEmbedding_coe_real`

English:
theorem isUniformEmbedding_coe_real
  statement: IsUniformEmbedding ((↑) : Nat -> Real)
  proof: isUniformEmbedding_bot_of_pairwise_le_dist zero_lt_one pairwise_one_le_dist

中文:
定理 isUniformEmbedding_coe_real
  结论: IsUniformEmbedding ((↑) : 自然数 -> 实数)
  证明: isUniformEmbedding_bot_of_pairwise_le_dist zero_lt_one pairwise_one_le_dist

Depends on / 依赖: isUniformEmbedding_bot_of_pairwise_le_dist, pairwise_one_le_dist, zero_lt_one
-/
theorem isUniformEmbedding_coe_real : IsUniformEmbedding ((↑) : Nat -> Real) :=
  isUniformEmbedding_bot_of_pairwise_le_dist zero_lt_one pairwise_one_le_dist

/--
theorem `isClosedEmbedding_coe_real` / 定理 `isClosedEmbedding_coe_real`

English:
theorem isClosedEmbedding_coe_real
  statement: IsClosedEmbedding ((↑) : Nat -> Real)
  proof: isClosedEmbedding_of_pairwise_le_dist zero_lt_one pairwise_one_le_dist

中文:
定理 isClosedEmbedding_coe_real
  结论: IsClosedEmbedding ((↑) : 自然数 -> 实数)
  证明: isClosedEmbedding_of_pairwise_le_dist zero_lt_one pairwise_one_le_dist

Depends on / 依赖: isClosedEmbedding_of_pairwise_le_dist, pairwise_one_le_dist, zero_lt_one
-/
theorem isClosedEmbedding_coe_real : IsClosedEmbedding ((↑) : Nat -> Real) :=
  isClosedEmbedding_of_pairwise_le_dist zero_lt_one pairwise_one_le_dist

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MetricSpace Nat
  body: Nat.isUniformEmbedding_coe_real.comapMetricSpace _

中文:
实例 :
  签名: MetricSpace 自然数
  定义体: Nat.isUniformEmbedding_coe_real.comapMetricSpace _
-/
instance : MetricSpace Nat := Nat.isUniformEmbedding_coe_real.comapMetricSpace _

/--
theorem `preimage_ball` / 定理 `preimage_ball`

English:
theorem preimage_ball
  given: (x : Nat) (r : Real)
  statement: (↑) ⁻¹' ball (x : Real) r = ball x r
  proof: rfl

中文:
定理 preimage_ball
  条件: (x : 自然数) (r : 实数)
  结论: (↑) ⁻¹' ball (x : 实数) r = ball x r
  证明: rfl
-/
theorem preimage_ball (x : Nat) (r : Real) : (↑) ⁻¹' ball (x : Real) r = ball x r := rfl

/--
theorem `preimage_closedBall` / 定理 `preimage_closedBall`

English:
theorem preimage_closedBall
  given: (x : Nat) (r : Real)
  statement: (↑) ⁻¹' closedBall (x : Real) r = closedBall x r
  proof: rfl

中文:
定理 preimage_closedBall
  条件: (x : 自然数) (r : 实数)
  结论: (↑) ⁻¹' closedBall (x : 实数) r = closedBall x r
  证明: rfl
-/
theorem preimage_closedBall (x : Nat) (r : Real) : (↑) ⁻¹' closedBall (x : Real) r = closedBall x r := rfl

/--
theorem `closedBall_eq_Icc` / 定理 `closedBall_eq_Icc`

English:
theorem closedBall_eq_Icc
  given: (x : Nat) (r : Real)
  statement: closedBall x r = Icc ⌈↑x - r⌉₊ ⌊↑x + r⌋₊
  proof: by
  rcases le_or_gt 0 r with (hr | hr)
  · rw [← preimage_closedBall, Real.closedBall_eq_Icc, preimage_Icc]
    positivity
  · rw [closedBall_eq_empty.2 hr, Icc_eq_empty_of_lt]
calc ⌊(x : Real) + r⌋₊ <= ⌊(x : Real)⌋₊ := floor_mono by linarith
    _ < ⌈↑x - r⌉₊ := by
      rw [floor_natCast]; rw [Na

中文:
定理 closedBall_eq_Icc
  条件: (x : 自然数) (r : 实数)
  结论: closedBall x r = Icc ⌈↑x - r⌉₊ ⌊↑x + r⌋₊
  证明: by
  rcases le_or_gt 0 r with (hr | hr)
  · rw [← preimage_closedBall, Real.closedBall_eq_Icc, preimage_Icc]
    positivity
  · rw [closedBall_eq_empty.2 hr, Icc_eq_empty_of_lt]
calc ⌊(x : Real) + r⌋₊ <= ⌊(x : Real)⌋₊ := floor_mono by linarith
    _ < ⌈↑x - r⌉₊ := by
      rw [floor_natCast]; rw [Na

Depends on / 依赖: Icc_eq_empty_of_lt, Nat.lt_ceil, Real.closedBall_eq_Icc, closedBall_eq_Icc, closedBall_eq_empty, floor_mono, floor_natCast, le_or_gt, lt_ceil, preimage_Icc, preimage_closedBall
-/
theorem closedBall_eq_Icc (x : Nat) (r : Real) : closedBall x r = Icc ⌈↑x - r⌉₊ ⌊↑x + r⌋₊ := by
  rcases le_or_gt 0 r with (hr | hr)
  · rw [← preimage_closedBall, Real.closedBall_eq_Icc, preimage_Icc]
    positivity
  · rw [closedBall_eq_empty.2 hr, Icc_eq_empty_of_lt]
calc ⌊(x : Real) + r⌋₊ <= ⌊(x : Real)⌋₊ := floor_mono by linarith
    _ < ⌈↑x - r⌉₊ := by
      rw [floor_natCast]; rw [Nat.lt_ceil]
      linarith

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ProperSpace Nat
  body: ⟨fun x r => by
    rw [closedBall_eq_Icc]
    exact (Set.finite_Icc _ _).isCompact⟩

中文:
实例 :
  签名: 命题erSpace 自然数
  定义体: ⟨fun x r => by
    rw [closedBall_eq_Icc]
    exact (Set.finite_Icc _ _).isCompact⟩

Depends on / 依赖: Set.finite_Icc, closedBall_eq_Icc, finite_Icc, isCompact
-/
instance : ProperSpace Nat :=
  ⟨fun x r => by
    rw [closedBall_eq_Icc]
    exact (Set.finite_Icc _ _).isCompact⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsOrderBornology Nat
  body: .of_isCompactIcc 0 (by simp) (by simp [Nat.closedBall_eq_Icc])

中文:
实例 :
  签名: IsOrderBornology 自然数
  定义体: .of_isCompactIcc 0 (by simp) (by simp [Nat.closedBall_eq_Icc])

Depends on / 依赖: Nat.closedBall_eq_Icc, closedBall_eq_Icc, of_isCompactIcc
-/
instance : IsOrderBornology Nat := .of_isCompactIcc 0 (by simp) (by simp [Nat.closedBall_eq_Icc])

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: NoncompactSpace Nat
  body: noncompactSpace_of_neBot by simp only [Filter.cocompact_eq_cofinite, Filter.cofinite_neBot]

中文:
实例 :
  签名: NoncompactSpace 自然数
  定义体: noncompactSpace_of_neBot by simp only [Filter.cocompact_eq_cofinite, Filter.cofinite_neBot]

Depends on / 依赖: Filter, Filter.cocompact_eq_cofinite, Filter.cofinite_neBot, cocompact_eq_cofinite, cofinite_neBot, noncompactSpace_of_neBot
-/
instance : NoncompactSpace Nat :=
noncompactSpace_of_neBot by simp only [Filter.cocompact_eq_cofinite, Filter.cofinite_neBot]

end Nat
