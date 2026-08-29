/-
Copyright (c) 2024 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
module

public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Topology.ContinuousMap.CocompactMap
public import Mathlib.Topology.MetricSpace.Bounded

/-!
# Cocompact maps in normed groups

This file gives a characterization of cocompact maps in terms of norm estimates.

## Main statements

* `CocompactMapClass.norm_le`: Every cocompact map satisfies a norm estimate
* `ContinuousMapClass.toCocompactMapClass_of_norm`: Conversely, this norm estimate implies that a
  map is cocompact.

-/

public section

open Filter Metric

variable {𝕜 E F 𝓕 : Type*}
variable [NormedAddCommGroup E] [NormedAddCommGroup F]
variable {f : 𝓕}

/--
theorem `CocompactMapClass.norm_le` / 定理 `CocompactMapClass.norm_le`

English:
theorem CocompactMapClass.norm_le
  statement: [ProperSpace F] [FunLike 𝓕 E F] [CocompactMapClass 𝓕 E F]
  proof: by
  have h := cocompact_tendsto f
  rw [tendsto_def] at h
  specialize h (Metric.closedBall 0 ε)ᶜ (mem_cocompact_of_closedBall_compl_subset 0 ⟨ε, rfl.subset⟩)
  rcases closedBall_compl_subset_of_mem_cocompact h 0 with ⟨r, hr⟩
  use r
  intro x hx
  suffices x in f ⁻¹' (Metric.closedBall 0 ε)ᶜ by si

中文:
定理 CocompactMapClass.norm_le
  结论: [命题erSpace F] [FunLike 𝓕 E F] [CocompactMapClass 𝓕 E F]
  证明: by
  have h := cocompact_tendsto f
  rw [tendsto_def] at h
  specialize h (Metric.closedBall 0 ε)ᶜ (mem_cocompact_of_closedBall_compl_subset 0 ⟨ε, rfl.subset⟩)
  rcases closedBall_compl_subset_of_mem_cocompact h 0 with ⟨r, hr⟩
  use r
  intro x hx
  suffices x in f ⁻¹' (Metric.closedBall 0 ε)ᶜ by si

Depends on / 依赖: Metric, Metric.closedBall, closedBall, closedBall_compl_subset_of_mem_cocompact, cocompact_tendsto, mem_cocompact_of_closedBall_compl_subset, rfl.subset, specialize, subset, tendsto_def
-/
theorem CocompactMapClass.norm_le [ProperSpace F] [FunLike 𝓕 E F] [CocompactMapClass 𝓕 E F]
    (ε : Real) : exists r : Real, forall x : E, r < ‖x‖ -> ε < ‖f x‖ := by
  have h := cocompact_tendsto f
  rw [tendsto_def] at h
  specialize h (Metric.closedBall 0 ε)ᶜ (mem_cocompact_of_closedBall_compl_subset 0 ⟨ε, rfl.subset⟩)
  rcases closedBall_compl_subset_of_mem_cocompact h 0 with ⟨r, hr⟩
  use r
  intro x hx
  suffices x in f ⁻¹' (Metric.closedBall 0 ε)ᶜ by simp_all
  apply hr
  simp [hx]

/--
theorem `Filter.tendsto_cocompact_cocompact_of_norm` / 定理 `Filter.tendsto_cocompact_cocompact_of_norm`

English:
theorem Filter.tendsto_cocompact_cocompact_of_norm
  statement: [ProperSpace E] {f : E -> F}
  proof: by
  rw [tendsto_def]
  intro s hs
  rcases closedBall_compl_subset_of_mem_cocompact hs 0 with ⟨ε, hε⟩
  rcases h ε with ⟨r, hr⟩
  apply mem_cocompact_of_closedBall_compl_subset 0
  use r
  intro x hx
  simp only [Set.mem_compl_iff, Metric.mem_closedBall, dist_zero_right, not_le] at hx
  apply hε
  

中文:
定理 Filter.tendsto_cocompact_cocompact_of_norm
  结论: [命题erSpace E] {f : E -> F}
  证明: by
  rw [tendsto_def]
  intro s hs
  rcases closedBall_compl_subset_of_mem_cocompact hs 0 with ⟨ε, hε⟩
  rcases h ε with ⟨r, hr⟩
  apply mem_cocompact_of_closedBall_compl_subset 0
  use r
  intro x hx
  simp only [Set.mem_compl_iff, Metric.mem_closedBall, dist_zero_right, not_le] at hx
  apply hε
  

Depends on / 依赖: Metric, Metric.mem_closedBall, Set.mem_compl_iff, closedBall_compl_subset_of_mem_cocompact, dist_zero_right, mem_closedBall, mem_cocompact_of_closedBall_compl_subset, mem_compl_iff, not_le, tendsto_def
-/
theorem Filter.tendsto_cocompact_cocompact_of_norm [ProperSpace E] {f : E -> F}
    (h : forall ε : Real, exists r : Real, forall x : E, r < ‖x‖ -> ε < ‖f x‖) :
    Tendsto f (cocompact E) (cocompact F) := by
  rw [tendsto_def]
  intro s hs
  rcases closedBall_compl_subset_of_mem_cocompact hs 0 with ⟨ε, hε⟩
  rcases h ε with ⟨r, hr⟩
  apply mem_cocompact_of_closedBall_compl_subset 0
  use r
  intro x hx
  simp only [Set.mem_compl_iff, Metric.mem_closedBall, dist_zero_right, not_le] at hx
  apply hε
  simp [hr x hx]

/--
theorem `ContinuousMapClass.toCocompactMapClass_of_norm` / 定理 `ContinuousMapClass.toCocompactMapClass_of_norm`

English:
theorem ContinuousMapClass.toCocompactMapClass_of_norm
  statement: [ProperSpace E] [FunLike 𝓕 E F]
  proof: (tendsto_cocompact_cocompact_of_norm <| h ·)

中文:
定理 ContinuousMapClass.toCocompactMapClass_of_norm
  结论: [命题erSpace E] [FunLike 𝓕 E F]
  证明: (tendsto_cocompact_cocompact_of_norm <| h ·)

Depends on / 依赖: tendsto_cocompact_cocompact_of_norm
-/
theorem ContinuousMapClass.toCocompactMapClass_of_norm [ProperSpace E] [FunLike 𝓕 E F]
    [ContinuousMapClass 𝓕 E F] (h : forall (f : 𝓕) (ε : Real), exists r : Real, forall x : E, r < ‖x‖ -> ε < ‖f x‖) :
    CocompactMapClass 𝓕 E F where
  cocompact_tendsto := (tendsto_cocompact_cocompact_of_norm <| h ·)
