/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
module

public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Int.ConditionallyCompleteOrder
public import Mathlib.Topology.Instances.Discrete
public import Mathlib.Topology.MetricSpace.Bounded
public import Mathlib.Order.Filter.AtTopBot.Archimedean
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Topology.Order.Bornology

/-!
# Topology on the integers

The structure of a metric space on `ℤ` is introduced in this file, induced from `ℝ`.
-/

public section


noncomputable section

open Filter Metric Set Topology

namespace Int

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Dist Int
  body: ⟨fun x y => dist (x : Real) y⟩

中文:
实例 :
  签名: Dist 整数
  定义体: ⟨fun x y => dist (x : Real) y⟩
-/
instance : Dist Int :=
  ⟨fun x y => dist (x : Real) y⟩

/--
theorem `dist_eq` / 定理 `dist_eq`

English:
theorem dist_eq
  given: (x y : Int)
  statement: dist x y = |(x : Real) - y|
  proof: rfl

中文:
定理 dist_eq
  条件: (x y : 整数)
  结论: dist x y = |(x : 实数) - y|
  证明: rfl
-/
theorem dist_eq (x y : Int) : dist x y = |(x : Real) - y| := rfl

/--
theorem `dist_eq'` / 定理 `dist_eq'`

English:
theorem dist_eq'
  given: (m n : Int)
  statement: dist m n = |m - n|
  proof: by rw [dist_eq]; norm_cast

@[norm_cast, simp]

中文:
定理 dist_eq'
  条件: (m n : 整数)
  结论: dist m n = |m - n|
  证明: by rw [dist_eq]; norm_cast

@[norm_cast, simp]

Depends on / 依赖: dist_eq
-/
theorem dist_eq' (m n : Int) : dist m n = |m - n| := by rw [dist_eq]; norm_cast

@[norm_cast, simp]
/--
theorem `dist_cast_real` / 定理 `dist_cast_real`

English:
theorem dist_cast_real
  given: (x y : Int)
  statement: dist (x : Real) y = dist x y
  proof: rfl

中文:
定理 dist_cast_real
  条件: (x y : 整数)
  结论: dist (x : 实数) y = dist x y
  证明: rfl
-/
theorem dist_cast_real (x y : Int) : dist (x : Real) y = dist x y :=
  rfl

/--
theorem `pairwise_one_le_dist` / 定理 `pairwise_one_le_dist`

English:
theorem pairwise_one_le_dist
  statement: Pairwise fun m n : Int => 1 <= dist m n
  proof: by
  intro m n hne
  rw [dist_eq]; norm_cast; rwa [← zero_add (1 : Int), Int.add_one_le_iff, abs_pos, sub_ne_zero]

中文:
定理 pairwise_one_le_dist
  结论: 两两 fun m n : 整数 => 1 <= dist m n
  证明: by
  intro m n hne
  rw [dist_eq]; norm_cast; rwa [← zero_add (1 : Int), Int.add_one_le_iff, abs_pos, sub_ne_zero]

Depends on / 依赖: Int.add_one_le_iff, abs_pos, add_one_le_iff, dist_eq, sub_ne_zero, zero_add
-/
theorem pairwise_one_le_dist : Pairwise fun m n : Int => 1 <= dist m n := by
  intro m n hne
  rw [dist_eq]; norm_cast; rwa [← zero_add (1 : Int), Int.add_one_le_iff, abs_pos, sub_ne_zero]

/--
theorem `isUniformEmbedding_coe_real` / 定理 `isUniformEmbedding_coe_real`

English:
theorem isUniformEmbedding_coe_real
  statement: IsUniformEmbedding ((↑) : Int -> Real)
  proof: isUniformEmbedding_bot_of_pairwise_le_dist zero_lt_one pairwise_one_le_dist

中文:
定理 isUniformEmbedding_coe_real
  结论: 是一致嵌入 ((↑) : 整数 -> 实数)
  证明: isUniformEmbedding_bot_of_pairwise_le_dist zero_lt_one pairwise_one_le_dist

Depends on / 依赖: isUniformEmbedding_bot_of_pairwise_le_dist, pairwise_one_le_dist, zero_lt_one
-/
theorem isUniformEmbedding_coe_real : IsUniformEmbedding ((↑) : Int -> Real) :=
  isUniformEmbedding_bot_of_pairwise_le_dist zero_lt_one pairwise_one_le_dist

/--
theorem `isClosedEmbedding_coe_real` / 定理 `isClosedEmbedding_coe_real`

English:
theorem isClosedEmbedding_coe_real
  statement: IsClosedEmbedding ((↑) : Int -> Real)
  proof: isClosedEmbedding_of_pairwise_le_dist zero_lt_one pairwise_one_le_dist

中文:
定理 isClosedEmbedding_coe_real
  结论: 是闭嵌入 ((↑) : 整数 -> 实数)
  证明: isClosedEmbedding_of_pairwise_le_dist zero_lt_one pairwise_one_le_dist

Depends on / 依赖: isClosedEmbedding_of_pairwise_le_dist, pairwise_one_le_dist, zero_lt_one
-/
theorem isClosedEmbedding_coe_real : IsClosedEmbedding ((↑) : Int -> Real) :=
  isClosedEmbedding_of_pairwise_le_dist zero_lt_one pairwise_one_le_dist

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MetricSpace Int
  body: Int.isUniformEmbedding_coe_real.comapMetricSpace _

中文:
实例 :
  签名: 度量空间 整数
  定义体: Int.isUniformEmbedding_coe_real.comapMetricSpace _

Depends on / 依赖: Int.isUniformEmbedding_coe_real.comapMetricSpace, comapMetricSpace, isUniformEmbedding_coe_real
-/
instance : MetricSpace Int := Int.isUniformEmbedding_coe_real.comapMetricSpace _

/--
theorem `preimage_ball` / 定理 `preimage_ball`

English:
theorem preimage_ball
  given: (x : Int) (r : Real)
  statement: (↑) ⁻¹' ball (x : Real) r = ball x r
  proof: rfl

中文:
定理 preimage_ball
  条件: (x : 整数) (r : 实数)
  结论: (↑) ⁻¹' ball (x : 实数) r = ball x r
  证明: rfl
-/
theorem preimage_ball (x : Int) (r : Real) : (↑) ⁻¹' ball (x : Real) r = ball x r := rfl

/--
theorem `preimage_closedBall` / 定理 `preimage_closedBall`

English:
theorem preimage_closedBall
  given: (x : Int) (r : Real)
  statement: (↑) ⁻¹' closedBall (x : Real) r = closedBall x r
  proof: rfl

中文:
定理 preimage_closedBall
  条件: (x : 整数) (r : 实数)
  结论: (↑) ⁻¹' closedBall (x : 实数) r = closedBall x r
  证明: rfl
-/
theorem preimage_closedBall (x : Int) (r : Real) : (↑) ⁻¹' closedBall (x : Real) r = closedBall x r := rfl

/--
theorem `ball_eq_Ioo` / 定理 `ball_eq_Ioo`

English:
theorem ball_eq_Ioo
  given: (x : Int) (r : Real)
  statement: ball x r = Ioo ⌊↑x - r⌋ ⌈↑x + r⌉
  proof: by
  rw [← preimage_ball]; rw [Real.ball_eq_Ioo]; rw [preimage_Ioo]

中文:
定理 ball_eq_Ioo
  条件: (x : 整数) (r : 实数)
  结论: ball x r = 开区间 ⌊↑x - r⌋ ⌈↑x + r⌉
  证明: by
  rw [← preimage_ball]; rw [Real.ball_eq_Ioo]; rw [preimage_Ioo]

Depends on / 依赖: Real.ball_eq_Ioo, ball_eq_Ioo, preimage_Ioo, preimage_ball
-/
theorem ball_eq_Ioo (x : Int) (r : Real) : ball x r = Ioo ⌊↑x - r⌋ ⌈↑x + r⌉ := by
  rw [← preimage_ball]; rw [Real.ball_eq_Ioo]; rw [preimage_Ioo]

/--
theorem `closedBall_eq_Icc` / 定理 `closedBall_eq_Icc`

English:
theorem closedBall_eq_Icc
  given: (x : Int) (r : Real)
  statement: closedBall x r = Icc ⌈↑x - r⌉ ⌊↑x + r⌋
  proof: by
  rw [← preimage_closedBall]; rw [Real.closedBall_eq_Icc]; rw [preimage_Icc]

中文:
定理 closedBall_eq_Icc
  条件: (x : 整数) (r : 实数)
  结论: closedBall x r = 闭区间 ⌈↑x - r⌉ ⌊↑x + r⌋
  证明: by
  rw [← preimage_closedBall]; rw [Real.closedBall_eq_Icc]; rw [preimage_Icc]

Depends on / 依赖: Real.closedBall_eq_Icc, closedBall_eq_Icc, preimage_Icc, preimage_closedBall
-/
theorem closedBall_eq_Icc (x : Int) (r : Real) : closedBall x r = Icc ⌈↑x - r⌉ ⌊↑x + r⌋ := by
  rw [← preimage_closedBall]; rw [Real.closedBall_eq_Icc]; rw [preimage_Icc]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ProperSpace Int
  body: ⟨fun x r => by
    rw [closedBall_eq_Icc]
    exact (Set.finite_Icc _ _).isCompact⟩

中文:
实例 :
  签名: 真空间 整数
  定义体: ⟨fun x r => by
    rw [closedBall_eq_Icc]
    exact (Set.finite_Icc _ _).isCompact⟩

Depends on / 依赖: Set.finite_Icc, closedBall_eq_Icc, finite_Icc, isCompact
-/
instance : ProperSpace Int :=
  ⟨fun x r => by
    rw [closedBall_eq_Icc]
    exact (Set.finite_Icc _ _).isCompact⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsOrderBornology Int
  body: .of_isCompactIcc 0 (by simp [Int.closedBall_eq_Icc]) (by simp [Int.closedBall_eq_Icc])

@[deprecated (since := "2026-04-07")]
alias cobounded_eq := IsOrderBornology.cobounded_eq

@[simp]

中文:
实例 :
  签名: 是OrderBornology 整数
  定义体: .of_isCompactIcc 0 (by simp [Int.closedBall_eq_Icc]) (by simp [Int.closedBall_eq_Icc])

@[deprecated (since := "2026-04-07")]
alias cobounded_eq := IsOrderBornology.cobounded_eq

@[simp]

Depends on / 依赖: Int.closedBall_eq_Icc, closedBall_eq_Icc, of_isCompactIcc
-/
instance : IsOrderBornology Int :=
  .of_isCompactIcc 0 (by simp [Int.closedBall_eq_Icc]) (by simp [Int.closedBall_eq_Icc])

@[deprecated (since := "2026-04-07")]
alias cobounded_eq := IsOrderBornology.cobounded_eq

@[simp]
/--
theorem `cofinite_eq` / 定理 `cofinite_eq`

English:
theorem cofinite_eq
  statement: (cofinite : Filter Int) = atBot ⊔ atTop
  proof: by
  rw [← cocompact_eq_cofinite]; rw [cocompact_eq_atBot_atTop]

中文:
定理 cofinite_eq
  结论: (cofinite : 滤子 整数) = atBot ⊔ atTop
  证明: by
  rw [← cocompact_eq_cofinite]; rw [cocompact_eq_atBot_atTop]

Depends on / 依赖: cocompact_eq_atBot_atTop, cocompact_eq_cofinite
-/
theorem cofinite_eq : (cofinite : Filter Int) = atBot ⊔ atTop := by
  rw [← cocompact_eq_cofinite]; rw [cocompact_eq_atBot_atTop]

end Int
