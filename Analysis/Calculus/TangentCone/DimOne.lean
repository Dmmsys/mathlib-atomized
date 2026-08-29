/-
Copyright (c) 2025 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Yury Kudryashov
-/
module

public import Mathlib.Analysis.Calculus.TangentCone.Defs
import Mathlib.Analysis.Calculus.TangentCone.Basic
import Mathlib.Analysis.Normed.Group.Uniform
public import Mathlib.Analysis.Normed.Field.Basic

/-!
# Unique differentiability property of a set in the base field

In this file we prove that a set in the base field has the unique differentiability property at `x`
iff `x` is an accumulation point of the set, see `uniqueDiffWithinAt_iff_accPt`.
-/

public section

open Filter Metric Set
open scoped Topology

variable {𝕜 : Type*} [NormedDivisionRing 𝕜]

/--
theorem `tangentConeAt_eq_univ` / 定理 `tangentConeAt_eq_univ`

English:
theorem tangentConeAt_eq_univ
  given: {s : Set 𝕜} {x : 𝕜} (hx : AccPt x (𝓟 s))
  proof: by
  refine eq_univ_of_forall fun y => ?_
  apply mem_tangentConeAt_of_frequently (𝓝[!=] x) (fun z => y / (z - x)) (· - x)
.mono_left inf_le_left · exact Continuous.tendsto' (by fun_prop) _ _ (by simp)
  · simpa [accPt_iff_frequently_nhdsNE] using hx
  · apply tendsto_nhds_of_eventually_eq
    refin

中文:
定理 tangentConeAt_eq_univ
  条件: {s : Set 𝕜} {x : 𝕜} (hx : AccPt x (𝓟 s))
  证明: by
  refine eq_univ_of_forall fun y => ?_
  apply mem_tangentConeAt_of_frequently (𝓝[!=] x) (fun z => y / (z - x)) (· - x)
.mono_left inf_le_left · exact Continuous.tendsto' (by fun_prop) _ _ (by simp)
  · simpa [accPt_iff_frequently_nhdsNE] using hx
  · apply tendsto_nhds_of_eventually_eq
    refin

Depends on / 依赖: Continuous, Continuous.tendsto, accPt_iff_frequently_nhdsNE, eq_univ_of_forall, eventually_mem_nhdsWithin, eventually_mem_nhdsWithin.mono, fun_prop, inf_le_left, mem_tangentConeAt_of_frequently, mono_left, sub_eq_zero, tendsto, tendsto_nhds_of_eventually_eq
-/
theorem tangentConeAt_eq_univ {s : Set 𝕜} {x : 𝕜} (hx : AccPt x (𝓟 s)) :
    tangentConeAt 𝕜 s x = univ := by
  refine eq_univ_of_forall fun y => ?_
  apply mem_tangentConeAt_of_frequently (𝓝[!=] x) (fun z => y / (z - x)) (· - x)
.mono_left inf_le_left · exact Continuous.tendsto' (by fun_prop) _ _ (by simp)
  · simpa [accPt_iff_frequently_nhdsNE] using hx
  · apply tendsto_nhds_of_eventually_eq
    refine eventually_mem_nhdsWithin.mono fun z hz => ?_
    have : z - x != 0 := by simpa [sub_eq_zero] using hz
    simp [div_mul_cancel₀ _ this]

/--
theorem `uniqueDiffWithinAt_iff_accPt` / 定理 `uniqueDiffWithinAt_iff_accPt`

English:
theorem uniqueDiffWithinAt_iff_accPt
  given: {s : Set 𝕜} {x : 𝕜}
  proof: ⟨UniqueDiffWithinAt.accPt, fun h =>
    ⟨by simp [tangentConeAt_eq_univ h], mem_closure_iff_clusterPt.mpr h.clusterPt⟩⟩

alias ⟨_, AccPt.uniqueDiffWithinAt⟩ := uniqueDiffWithinAt_iff_accPt

中文:
定理 uniqueDiffWithinAt_iff_accPt
  条件: {s : Set 𝕜} {x : 𝕜}
  证明: ⟨UniqueDiffWithinAt.accPt, fun h =>
    ⟨by simp [tangentConeAt_eq_univ h], mem_closure_iff_clusterPt.mpr h.clusterPt⟩⟩

alias ⟨_, AccPt.uniqueDiffWithinAt⟩ := uniqueDiffWithinAt_iff_accPt

Depends on / 依赖: UniqueDiffWithinAt, UniqueDiffWithinAt.accPt, clusterPt, h.clusterPt, mem_closure_iff_clusterPt, mem_closure_iff_clusterPt.mpr, tangentConeAt_eq_univ
-/
theorem uniqueDiffWithinAt_iff_accPt {s : Set 𝕜} {x : 𝕜} :
    UniqueDiffWithinAt 𝕜 s x ↔ AccPt x (𝓟 s) :=
  ⟨UniqueDiffWithinAt.accPt, fun h =>
    ⟨by simp [tangentConeAt_eq_univ h], mem_closure_iff_clusterPt.mpr h.clusterPt⟩⟩

alias ⟨_, AccPt.uniqueDiffWithinAt⟩ := uniqueDiffWithinAt_iff_accPt
