/-
Copyright (c) 2022 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
module

public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef

/-!
# Uniformly locally doubling measures

A uniformly locally doubling measure `μ` on a metric space is a measure for which there exists a
constant `C` such that for all sufficiently small radii `ε`, and for any centre, the measure of a
ball of radius `2 * ε` is bounded by `C` times the measure of the concentric ball of radius `ε`.

This file records basic facts about uniformly locally doubling measures.

## Main definitions

  * `IsUnifLocDoublingMeasure`: the definition of a uniformly locally doubling measure (as a
    typeclass).
  * `IsUnifLocDoublingMeasure.doublingConstant`: a function yielding the doubling constant `C`
    appearing in the definition of a uniformly locally doubling measure.
-/

@[expose] public section

assert_not_exists Real.instPow

noncomputable section

open Set Filter Metric MeasureTheory TopologicalSpace ENNReal NNReal Topology

/--
Definition of `IsUnifLocDoublingMeasure` / `IsUnifLocDoublingMeasure` 的定义

English:
class IsUnifLocDoublingMeasure
  parameters: {α : Type*} [PseudoMetricSpace α] [MeasurableSpace α]
  axioms and operations (1):
    - exists_measure_closedBall_le_mul'' : exists C : Real>=0, forallᶠ ε in 𝓝[>] 0, forall x, μ (closedBall x (2 * ε)) <= C * μ (closedBall x ε)

中文:
类 是UnifLocDoublingMeasure
  参数: {α : 类型} [伪度量空间 α] [可测空间 α]
  公理与运算 (1 个):
    - exists_measure_closedBall_le_mul'' : 存在 C : 实数>=0, 对任意ᶠ ε in 𝓝[>] 0, 对任意 x, μ (closedBall x (2 * ε)) <= C * μ (closedBall x ε)
-/
class IsUnifLocDoublingMeasure {α : Type*} [PseudoMetricSpace α] [MeasurableSpace α]
  (μ : Measure α) : Prop where
  exists_measure_closedBall_le_mul'' :
    exists C : Real>=0, forallᶠ ε in 𝓝[>] 0, forall x, μ (closedBall x (2 * ε)) <= C * μ (closedBall x ε)

namespace IsUnifLocDoublingMeasure

variable {α : Type*} [PseudoMetricSpace α] [MeasurableSpace α] (μ : Measure α)
  [IsUnifLocDoublingMeasure μ]

/--
theorem `exists_measure_closedBall_le_mul` / 定理 `exists_measure_closedBall_le_mul`

English:
theorem exists_measure_closedBall_le_mul
  proof: exists_measure_closedBall_le_mul''

中文:
定理 存在_measure_closedBall_le_mul
  证明: exists_measure_closedBall_le_mul''

Depends on / 依赖: exists_measure_closedBall_le_mul
-/
theorem exists_measure_closedBall_le_mul :
    exists C : Real>=0, forallᶠ ε in 𝓝[>] 0, forall x, μ (closedBall x (2 * ε)) <= C * μ (closedBall x ε) :=
  exists_measure_closedBall_le_mul''

/--
Definition of `doublingConstant` / `doublingConstant` 的定义

English:
definition doublingConstant
  signature: : Real>=0
  body: Classical.choose exists_measure_closedBall_le_mul μ

中文:
定义 doublingConstant
  签名: : 实数>=0
  定义体: Classical.choose exists_measure_closedBall_le_mul μ

Depends on / 依赖: Classical, Classical.choose, exists_measure_closedBall_le_mul
-/
def doublingConstant : Real>=0 :=
Classical.choose exists_measure_closedBall_le_mul μ

/--
theorem `eventually_measure_le_doublingConstant_mul` / 定理 `eventually_measure_le_doublingConstant_mul`

English:
theorem eventually_measure_le_doublingConstant_mul
  proof: Classical.choose_spec exists_measure_closedBall_le_mul μ

中文:
定理 eventually_measure_le_doublingConstant_mul
  证明: Classical.choose_spec exists_measure_closedBall_le_mul μ

Depends on / 依赖: Classical, Classical.choose_spec, choose_spec, exists_measure_closedBall_le_mul
-/
theorem eventually_measure_le_doublingConstant_mul :
    forallᶠ ε in 𝓝[>] 0, forall x, μ (closedBall x (2 * ε)) <= doublingConstant μ * μ (closedBall x ε) :=
Classical.choose_spec exists_measure_closedBall_le_mul μ

/--
theorem `exists_eventually_forall_measure_closedBall_le_mul` / 定理 `exists_eventually_forall_measure_closedBall_le_mul`

English:
theorem exists_eventually_forall_measure_closedBall_le_mul
  given: (K : Real)
  proof: by
  let C := doublingConstant μ
  suffices forall n,
      forallᶠ ε in 𝓝[>] 0, forall x, μ (closedBall x ((2 : Real) ^ n * ε)) <= C ^ n * μ (closedBall x ε) by
    rcases pow_unbounded_of_one_lt K one_lt_two with ⟨n, hn⟩
    use C ^ n
    filter_upwards [eventually_mem_nhdsWithin, this n] with ε h

中文:
定理 存在_eventually_对任意_measure_closedBall_le_mul
  条件: (K : 实数)
  证明: by
  let C := doublingConstant μ
  suffices forall n,
      forallᶠ ε in 𝓝[>] 0, forall x, μ (closedBall x ((2 : Real) ^ n * ε)) <= C ^ n * μ (closedBall x ε) by
    rcases pow_unbounded_of_one_lt K one_lt_two with ⟨n, hn⟩
    use C ^ n
    filter_upwards [eventually_mem_nhdsWithin, this n] with ε h

Depends on / 依赖: ENNReal, ENNReal.coe_pow, closedBall, coe_pow, doublingConstant, eventually_mem_nhdsWithin, eventually_nhdsGT_zero_mul_left, filter_upwards, mem_Ioi, one_lt_two, pow_unbounded_of_one_lt, replace, two_pos
-/
theorem exists_eventually_forall_measure_closedBall_le_mul (K : Real) :
    exists C : Real>=0, forallᶠ ε in 𝓝[>] 0, forall x, forall t <= K, μ (closedBall x (t * ε)) <= C * μ (closedBall x ε) := by
  let C := doublingConstant μ
  suffices forall n,
      forallᶠ ε in 𝓝[>] 0, forall x, μ (closedBall x ((2 : Real) ^ n * ε)) <= C ^ n * μ (closedBall x ε) by
    rcases pow_unbounded_of_one_lt K one_lt_two with ⟨n, hn⟩
    use C ^ n
    filter_upwards [eventually_mem_nhdsWithin, this n] with ε hε₀ hε x t ht
    rw [mem_Ioi] at hε₀
    grw [ht, hn, ENNReal.coe_pow]
    exact hε x
  intro n
  induction n with
  | zero => simp
  | succ n ihn =>
    replace ihn := eventually_nhdsGT_zero_mul_left (two_pos : 0 < (2 : Real)) ihn
    filter_upwards [ihn, eventually_measure_le_doublingConstant_mul μ] with ε hεn hε x
    grw [pow_succ, mul_assoc, hεn, hε, ← mul_assoc, pow_succ]

/--
Definition of `scalingConstantOf` / `scalingConstantOf` 的定义

English:
definition scalingConstantOf
  signature: (K : Real)
  body: max (Classical.choose <| exists_eventually_forall_measure_closedBall_le_mul μ K) 1

@[simp]

中文:
定义 scalingConstantOf
  签名: (K : 实数)
  定义体: max (Classical.choose <| exists_eventually_forall_measure_closedBall_le_mul μ K) 1

@[simp]

Depends on / 依赖: Classical, Classical.choose, exists_eventually_forall_measure_closedBall_le_mul
-/
def scalingConstantOf (K : Real) : Real>=0 :=
  max (Classical.choose <| exists_eventually_forall_measure_closedBall_le_mul μ K) 1

@[simp]
/--
theorem `one_le_scalingConstantOf` / 定理 `one_le_scalingConstantOf`

English:
theorem one_le_scalingConstantOf
  given: (K : Real)
  statement: 1 <= scalingConstantOf μ K
  proof: le_max_of_le_right le_refl 1

中文:
定理 one_le_scalingConstantOf
  条件: (K : 实数)
  结论: 1 <= scalingConstantOf μ K
  证明: le_max_of_le_right le_refl 1

Depends on / 依赖: le_max_of_le_right, le_refl
-/
theorem one_le_scalingConstantOf (K : Real) : 1 <= scalingConstantOf μ K :=
le_max_of_le_right le_refl 1

/--
theorem `eventually_measure_mul_le_scalingConstantOf_mul` / 定理 `eventually_measure_mul_le_scalingConstantOf_mul`

English:
theorem eventually_measure_mul_le_scalingConstantOf_mul
  given: (K : Real)
  proof: by
  have h := Classical.choose_spec (exists_eventually_forall_measure_closedBall_le_mul μ K)
  rcases mem_nhdsGT_iff_exists_Ioc_subset.1 h with ⟨R, Rpos, hR⟩
  refine ⟨R, Rpos, fun x t r ht hr => ?_⟩
  rcases lt_trichotomy r 0 with (rneg | rfl | rpos)
  · have : t * r < 0 := mul_neg_of_pos_of_neg h

中文:
定理 eventually_measure_mul_le_scalingConstantOf_mul
  条件: (K : 实数)
  证明: by
  have h := Classical.choose_spec (exists_eventually_forall_measure_closedBall_le_mul μ K)
  rcases mem_nhdsGT_iff_exists_Ioc_subset.1 h with ⟨R, Rpos, hR⟩
  refine ⟨R, Rpos, fun x t r ht hr => ?_⟩
  rcases lt_trichotomy r 0 with (rneg | rfl | rpos)
  · have : t * r < 0 := mul_neg_of_pos_of_neg h

Depends on / 依赖: Classical, Classical.choose_spec, ENNReal, ENNReal.one_le_coe_iff, choose_spec, closedBall_eq_empty, exists_eventually_forall_measure_closedBall_le_mul, le_max_right, le_mul_of_one_le_of_le, le_rfl, lt_trichotomy, measure_empty, mem_nhdsGT_iff_exists_Ioc_subset, mul_neg_of_pos_of_neg, mul_zero, one_le_coe_iff, zero_le
-/
theorem eventually_measure_mul_le_scalingConstantOf_mul (K : Real) :
    exists R : Real,
      0 < R ∧
        forall x t r, t in Ioc 0 K -> r <= R ->
          μ (closedBall x (t * r)) <= scalingConstantOf μ K * μ (closedBall x r) := by
  have h := Classical.choose_spec (exists_eventually_forall_measure_closedBall_le_mul μ K)
  rcases mem_nhdsGT_iff_exists_Ioc_subset.1 h with ⟨R, Rpos, hR⟩
  refine ⟨R, Rpos, fun x t r ht hr => ?_⟩
  rcases lt_trichotomy r 0 with (rneg | rfl | rpos)
  · have : t * r < 0 := mul_neg_of_pos_of_neg ht.1 rneg
    simp only [closedBall_eq_empty.2 this, measure_empty, zero_le]
  · simp only [mul_zero]
    refine le_mul_of_one_le_of_le ?_ le_rfl
    apply ENNReal.one_le_coe_iff.2 (le_max_right _ _)
  · apply (hR ⟨rpos, hr⟩ x t ht.2).trans
    gcongr
    apply le_max_left

/--
theorem `eventually_measure_le_scaling_constant_mul` / 定理 `eventually_measure_le_scaling_constant_mul`

English:
theorem eventually_measure_le_scaling_constant_mul
  given: (K : Real)
  proof: by
  filter_upwards [Classical.choose_spec
      (exists_eventually_forall_measure_closedBall_le_mul μ K)] with r hr x
  grw [hr x K le_rfl, scalingConstantOf, ← le_max_left]

中文:
定理 eventually_measure_le_scaling_constant_mul
  条件: (K : 实数)
  证明: by
  filter_upwards [Classical.choose_spec
      (exists_eventually_forall_measure_closedBall_le_mul μ K)] with r hr x
  grw [hr x K le_rfl, scalingConstantOf, ← le_max_left]

Depends on / 依赖: Classical, Classical.choose_spec, choose_spec, exists_eventually_forall_measure_closedBall_le_mul, filter_upwards, le_max_left, le_rfl, scalingConstantOf
-/
theorem eventually_measure_le_scaling_constant_mul (K : Real) :
    forallᶠ r in 𝓝[>] 0, forall x, μ (closedBall x (K * r)) <= scalingConstantOf μ K * μ (closedBall x r) := by
  filter_upwards [Classical.choose_spec
      (exists_eventually_forall_measure_closedBall_le_mul μ K)] with r hr x
  grw [hr x K le_rfl, scalingConstantOf, ← le_max_left]

/--
theorem `eventually_measure_le_scaling_constant_mul'` / 定理 `eventually_measure_le_scaling_constant_mul'`

English:
theorem eventually_measure_le_scaling_constant_mul'
  given: (K : Real) (hK : 0 < K)
  proof: by
  convert! eventually_nhdsGT_zero_mul_left hK (eventually_measure_le_scaling_constant_mul μ K⁻¹)
  simp [inv_mul_cancel_left₀ hK.ne']

中文:
定理 eventually_measure_le_scaling_constant_mul'
  条件: (K : 实数) (hK : 0 < K)
  证明: by
  convert! eventually_nhdsGT_zero_mul_left hK (eventually_measure_le_scaling_constant_mul μ K⁻¹)
  simp [inv_mul_cancel_left₀ hK.ne']

Depends on / 依赖: convert, eventually_measure_le_scaling_constant_mul, eventually_nhdsGT_zero_mul_left, hK.ne
-/
theorem eventually_measure_le_scaling_constant_mul' (K : Real) (hK : 0 < K) :
    forallᶠ r in 𝓝[>] 0, forall x,
      μ (closedBall x r) <= scalingConstantOf μ K⁻¹ * μ (closedBall x (K * r)) := by
  convert! eventually_nhdsGT_zero_mul_left hK (eventually_measure_le_scaling_constant_mul μ K⁻¹)
  simp [inv_mul_cancel_left₀ hK.ne']

/--
Definition of `scalingScaleOf` / `scalingScaleOf` 的定义

English:
definition scalingScaleOf
  signature: (K : Real)
  body: (eventually_measure_mul_le_scalingConstantOf_mul μ K).choose

中文:
定义 scalingScaleOf
  签名: (K : 实数)
  定义体: (eventually_measure_mul_le_scalingConstantOf_mul μ K).choose

Depends on / 依赖: eventually_measure_mul_le_scalingConstantOf_mul
-/
def scalingScaleOf (K : Real) : Real :=
  (eventually_measure_mul_le_scalingConstantOf_mul μ K).choose

/--
theorem `scalingScaleOf_pos` / 定理 `scalingScaleOf_pos`

English:
theorem scalingScaleOf_pos
  given: (K : Real)
  statement: 0 < scalingScaleOf μ K
  proof: (eventually_measure_mul_le_scalingConstantOf_mul μ K).choose_spec.1

中文:
定理 scalingScaleOf_pos
  条件: (K : 实数)
  结论: 0 < scalingScaleOf μ K
  证明: (eventually_measure_mul_le_scalingConstantOf_mul μ K).choose_spec.1

Depends on / 依赖: choose_spec, eventually_measure_mul_le_scalingConstantOf_mul
-/
theorem scalingScaleOf_pos (K : Real) : 0 < scalingScaleOf μ K :=
  (eventually_measure_mul_le_scalingConstantOf_mul μ K).choose_spec.1

/--
theorem `measure_mul_le_scalingConstantOf_mul` / 定理 `measure_mul_le_scalingConstantOf_mul`

English:
theorem measure_mul_le_scalingConstantOf_mul
  statement: {K : Real} {x : α} {t r : Real} (ht : t in Ioc 0 K)
  proof: (eventually_measure_mul_le_scalingConstantOf_mul μ K).choose_spec.2 x t r ht hr

中文:
定理 measure_mul_le_scalingConstantOf_mul
  结论: {K : 实数} {x : α} {t r : 实数} (ht : t in 左开右闭区间 0 K)
  证明: (eventually_measure_mul_le_scalingConstantOf_mul μ K).choose_spec.2 x t r ht hr

Depends on / 依赖: choose_spec, eventually_measure_mul_le_scalingConstantOf_mul
-/
theorem measure_mul_le_scalingConstantOf_mul {K : Real} {x : α} {t r : Real} (ht : t in Ioc 0 K)
    (hr : r <= scalingScaleOf μ K) :
    μ (closedBall x (t * r)) <= scalingConstantOf μ K * μ (closedBall x r) :=
  (eventually_measure_mul_le_scalingConstantOf_mul μ K).choose_spec.2 x t r ht hr

end IsUnifLocDoublingMeasure
