/-
Copyright (c) 2022 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.MeasureTheory.Covering.DensityTheorem
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Covering theorems for Lebesgue measure in one dimension

We have a general theory of covering theorems for doubling measures, developed notably
in `DensityTheorem.lean`. In this file, we expand the API for this theory in one dimension,
by showing that intervals belong to the relevant Vitali family.
-/

public section


open Set MeasureTheory IsUnifLocDoublingMeasure Filter

open scoped Topology

namespace Real

/--
theorem `Icc_mem_vitaliFamily_at_right` / 定理 `Icc_mem_vitaliFamily_at_right`

English:
theorem Icc_mem_vitaliFamily_at_right
  given: {x y : Real} (hxy : x < y)
  proof: by
  rw [Icc_eq_closedBall]
  refine closedBall_mem_vitaliFamily_of_dist_le_mul _ ?_ (by linarith)
  rw [dist_comm]; rw [Real.dist_eq]; rw [abs_of_nonneg] <;> linarith

中文:
定理 Icc_mem_vitaliFamily_at_right
  条件: {x y : 实数} (hxy : x < y)
  证明: by
  rw [Icc_eq_closedBall]
  refine closedBall_mem_vitaliFamily_of_dist_le_mul _ ?_ (by linarith)
  rw [dist_comm]; rw [Real.dist_eq]; rw [abs_of_nonneg] <;> linarith

Depends on / 依赖: Icc_eq_closedBall, Real.dist_eq, abs_of_nonneg, closedBall_mem_vitaliFamily_of_dist_le_mul, dist_comm, dist_eq
-/
theorem Icc_mem_vitaliFamily_at_right {x y : Real} (hxy : x < y) :
    Icc x y in (vitaliFamily (volume : Measure Real) 1).setsAt x := by
  rw [Icc_eq_closedBall]
  refine closedBall_mem_vitaliFamily_of_dist_le_mul _ ?_ (by linarith)
  rw [dist_comm]; rw [Real.dist_eq]; rw [abs_of_nonneg] <;> linarith

/--
theorem `tendsto_Icc_vitaliFamily_right` / 定理 `tendsto_Icc_vitaliFamily_right`

English:
theorem tendsto_Icc_vitaliFamily_right
  given: (x : Real)
  proof: by
  refine (VitaliFamily.tendsto_filterAt_iff _).2 ⟨?_, ?_⟩
  · filter_upwards [self_mem_nhdsWithin] with y hy using Icc_mem_vitaliFamily_at_right hy
  · intro ε εpos
    filter_upwards [Icc_mem_nhdsGT <| show x < x + ε by linarith] with y hy
    rw [closedBall_eq_Icc]
    exact Icc_subset_Icc (by linarith) hy.2

中文:
定理 tendsto_Icc_vitaliFamily_right
  条件: (x : 实数)
  证明: by
  refine (VitaliFamily.tendsto_filterAt_iff _).2 ⟨?_, ?_⟩
  · filter_upwards [self_mem_nhdsWithin] with y hy using Icc_mem_vitaliFamily_at_right hy
  · intro ε εpos
    filter_upwards [Icc_mem_nhdsGT <| show x < x + ε by linarith] with y hy
    rw [closedBall_eq_Icc]
    exact Icc_subset_Icc (by linarith) hy.2

Depends on / 依赖: Icc_mem_nhdsGT, Icc_mem_vitaliFamily_at_right, Icc_subset_Icc, VitaliFamily, VitaliFamily.tendsto_filterAt_iff, closedBall_eq_Icc, filter_upwards, self_mem_nhdsWithin, tendsto_filterAt_iff
-/
theorem tendsto_Icc_vitaliFamily_right (x : Real) :
    Tendsto (fun y => Icc x y) (𝓝[>] x) ((vitaliFamily (volume : Measure Real) 1).filterAt x) := by
  refine (VitaliFamily.tendsto_filterAt_iff _).2 ⟨?_, ?_⟩
  · filter_upwards [self_mem_nhdsWithin] with y hy using Icc_mem_vitaliFamily_at_right hy
  · intro ε εpos
    filter_upwards [Icc_mem_nhdsGT <| show x < x + ε by linarith] with y hy
    rw [closedBall_eq_Icc]
    exact Icc_subset_Icc (by linarith) hy.2

/--
theorem `Icc_mem_vitaliFamily_at_left` / 定理 `Icc_mem_vitaliFamily_at_left`

English:
theorem Icc_mem_vitaliFamily_at_left
  given: {x y : Real} (hxy : x < y)
  proof: by
  rw [Icc_eq_closedBall]
  refine closedBall_mem_vitaliFamily_of_dist_le_mul _ ?_ (by linarith)
  rw [Real.dist_eq]; rw [abs_of_nonneg] <;> linarith

中文:
定理 Icc_mem_vitaliFamily_at_left
  条件: {x y : 实数} (hxy : x < y)
  证明: by
  rw [Icc_eq_closedBall]
  refine closedBall_mem_vitaliFamily_of_dist_le_mul _ ?_ (by linarith)
  rw [Real.dist_eq]; rw [abs_of_nonneg] <;> linarith

Depends on / 依赖: Icc_eq_closedBall, Real.dist_eq, abs_of_nonneg, closedBall_mem_vitaliFamily_of_dist_le_mul, dist_eq
-/
theorem Icc_mem_vitaliFamily_at_left {x y : Real} (hxy : x < y) :
    Icc x y in (vitaliFamily (volume : Measure Real) 1).setsAt y := by
  rw [Icc_eq_closedBall]
  refine closedBall_mem_vitaliFamily_of_dist_le_mul _ ?_ (by linarith)
  rw [Real.dist_eq]; rw [abs_of_nonneg] <;> linarith

/--
theorem `tendsto_Icc_vitaliFamily_left` / 定理 `tendsto_Icc_vitaliFamily_left`

English:
theorem tendsto_Icc_vitaliFamily_left
  given: (x : Real)
  proof: by
  refine (VitaliFamily.tendsto_filterAt_iff _).2 ⟨?_, ?_⟩
  · filter_upwards [self_mem_nhdsWithin] with y hy using Icc_mem_vitaliFamily_at_left hy
  · intro ε εpos
    filter_upwards [Icc_mem_nhdsLT <| show x - ε < x by linarith] with y hy
    rw [closedBall_eq_Icc]
    exact Icc_subset_Icc hy.1 (by linarith)

中文:
定理 tendsto_Icc_vitaliFamily_left
  条件: (x : 实数)
  证明: by
  refine (VitaliFamily.tendsto_filterAt_iff _).2 ⟨?_, ?_⟩
  · filter_upwards [self_mem_nhdsWithin] with y hy using Icc_mem_vitaliFamily_at_left hy
  · intro ε εpos
    filter_upwards [Icc_mem_nhdsLT <| show x - ε < x by linarith] with y hy
    rw [closedBall_eq_Icc]
    exact Icc_subset_Icc hy.1 (by linarith)

Depends on / 依赖: Icc_mem_nhdsLT, Icc_mem_vitaliFamily_at_left, Icc_subset_Icc, VitaliFamily, VitaliFamily.tendsto_filterAt_iff, closedBall_eq_Icc, filter_upwards, self_mem_nhdsWithin, tendsto_filterAt_iff
-/
theorem tendsto_Icc_vitaliFamily_left (x : Real) :
    Tendsto (fun y => Icc y x) (𝓝[<] x) ((vitaliFamily (volume : Measure Real) 1).filterAt x) := by
  refine (VitaliFamily.tendsto_filterAt_iff _).2 ⟨?_, ?_⟩
  · filter_upwards [self_mem_nhdsWithin] with y hy using Icc_mem_vitaliFamily_at_left hy
  · intro ε εpos
    filter_upwards [Icc_mem_nhdsLT <| show x - ε < x by linarith] with y hy
    rw [closedBall_eq_Icc]
    exact Icc_subset_Icc hy.1 (by linarith)

end Real
