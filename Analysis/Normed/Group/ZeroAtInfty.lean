/-
Copyright (c) 2024 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
module

public import Mathlib.Topology.ContinuousMap.ZeroAtInfty

/-!
# ZeroAtInftyContinuousMapClass in normed additive groups

In this file we give a characterization of the predicate `zero_at_infty` from
`ZeroAtInftyContinuousMapClass`. A continuous map `f` is zero at infinity if and only if
for every `ε > 0` there exists a `r : ℝ` such that for all `x : E` with `r < ‖x‖` it holds that
`‖f x‖ < ε`.
-/

public section

open Topology Filter

variable {E F 𝓕 : Type*}
variable [SeminormedAddGroup E] [SeminormedAddCommGroup F]
variable [FunLike 𝓕 E F] [ZeroAtInftyContinuousMapClass 𝓕 E F]

/--
theorem `ZeroAtInftyContinuousMapClass.norm_le` / 定理 `ZeroAtInftyContinuousMapClass.norm_le`

English:
theorem ZeroAtInftyContinuousMapClass.norm_le
  given: (f : 𝓕) (ε : Real) (hε : 0 < ε)
  proof: by
  have h := zero_at_infty f
  rw [tendsto_zero_iff_norm_tendsto_zero]; rw [tendsto_def] at h
  specialize h (Metric.ball 0 ε) (Metric.ball_mem_nhds 0 hε)
  rcases Metric.closedBall_compl_subset_of_mem_cocompact h 0 with ⟨r, hr⟩
  use r
  intro x hr'
  suffices x in (fun x => ‖f x‖) ⁻¹' Metric.ball 0 ε by simp_all
  apply hr
  simp_all

中文:
定理 ZeroAtInftyContinuous映射类.norm_le
  条件: (f : 𝓕) (ε : 实数) (hε : 0 < ε)
  证明: by
  have h := zero_at_infty f
  rw [tendsto_zero_iff_norm_tendsto_zero]; rw [tendsto_def] at h
  specialize h (Metric.ball 0 ε) (Metric.ball_mem_nhds 0 hε)
  rcases Metric.closedBall_compl_subset_of_mem_cocompact h 0 with ⟨r, hr⟩
  use r
  intro x hr'
  suffices x in (fun x => ‖f x‖) ⁻¹' Metric.ball 0 ε by simp_all
  apply hr
  simp_all

Depends on / 依赖: Metric, Metric.ball, Metric.ball_mem_nhds, Metric.closedBall_compl_subset_of_mem_cocompact, ball_mem_nhds, closedBall_compl_subset_of_mem_cocompact, specialize, tendsto_def, tendsto_zero_iff_norm_tendsto_zero, zero_at_infty
-/
theorem ZeroAtInftyContinuousMapClass.norm_le (f : 𝓕) (ε : Real) (hε : 0 < ε) :
    exists (r : Real), forall (x : E) (_hx : r < ‖x‖), ‖f x‖ < ε := by
  have h := zero_at_infty f
  rw [tendsto_zero_iff_norm_tendsto_zero]; rw [tendsto_def] at h
  specialize h (Metric.ball 0 ε) (Metric.ball_mem_nhds 0 hε)
  rcases Metric.closedBall_compl_subset_of_mem_cocompact h 0 with ⟨r, hr⟩
  use r
  intro x hr'
  suffices x in (fun x => ‖f x‖) ⁻¹' Metric.ball 0 ε by simp_all
  apply hr
  simp_all

variable [ProperSpace E]

/--
theorem `zero_at_infty_of_norm_le` / 定理 `zero_at_infty_of_norm_le`

English:
theorem zero_at_infty_of_norm_le
  statement: (f : E -> F)
  proof: by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  intro s hs
  rw [mem_map]; rw [Metric.mem_cocompact_iff_closedBall_compl_subset 0]
  rw [Metric.mem_nhds_iff] at hs
  rcases hs with ⟨ε, hε, hs⟩
  rcases h ε hε with ⟨r, hr⟩
  use r
  intro
  aesop

中文:
定理 zero_at_infty_of_norm_le
  结论: (f : E -> F)
  证明: by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  intro s hs
  rw [mem_map]; rw [Metric.mem_cocompact_iff_closedBall_compl_subset 0]
  rw [Metric.mem_nhds_iff] at hs
  rcases hs with ⟨ε, hε, hs⟩
  rcases h ε hε with ⟨r, hr⟩
  use r
  intro
  aesop

Depends on / 依赖: Metric, Metric.mem_cocompact_iff_closedBall_compl_subset, Metric.mem_nhds_iff, mem_cocompact_iff_closedBall_compl_subset, mem_map, mem_nhds_iff, tendsto_zero_iff_norm_tendsto_zero
-/
theorem zero_at_infty_of_norm_le (f : E -> F)
    (h : forall (ε : Real) (_hε : 0 < ε), exists (r : Real), forall (x : E) (_hx : r < ‖x‖), ‖f x‖ < ε) :
    Tendsto f (cocompact E) (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  intro s hs
  rw [mem_map]; rw [Metric.mem_cocompact_iff_closedBall_compl_subset 0]
  rw [Metric.mem_nhds_iff] at hs
  rcases hs with ⟨ε, hε, hs⟩
  rcases h ε hε with ⟨r, hr⟩
  use r
  intro
  aesop
