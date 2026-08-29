/-
Copyright (c) 2025 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Analysis.Calculus.BumpFunction.Convolution
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-!
# Density of smooth functions in the space of continuous functions

In this file we prove that smooth functions are dense in the set of continuous functions
from a real finite-dimensional vector space to a Banach space,
see `ContinuousMap.dense_setOfPred_contDiff`.
We also prove several unbundled versions of this statement.

The heavy part of the proof is done upstream in `ContDiffBump.dist_normed_convolution_le`
and `HasCompactSupport.contDiff_convolution_left`.
Here we wrap these results removing measure-related arguments from the assumptions.
-/

public section

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace Real E] [FiniteDimensional Real E]
  [NormedAddCommGroup F] [NormedSpace Real F] [CompleteSpace F] {f : E -> F} {ε : Real}

open scoped ContDiff unitInterval Topology
open Function Set Metric MeasureTheory

/--
theorem `MeasureTheory.LocallyIntegrable.exists_contDiff_dist_le_of_forall_mem_ball_dist_le` / 定理 `MeasureTheory.LocallyIntegrable.exists_contDiff_dist_le_of_forall_mem_ball_dist_le`

English:
theorem MeasureTheory.LocallyIntegrable.exists_contDiff_dist_le_of_forall_mem_ball_dist_le
  proof: by
  set φ : ContDiffBump (0 : E) := ⟨ε / 2, ε, half_pos hε, half_lt_self hε⟩
  refine ⟨_, ?_, fun a δ => φ.dist_normed_convolution_le hf.aestronglyMeasurable⟩
  exact φ.hasCompactSupport_normed.contDiff_convolution_left _ φ.contDiff_normed hf

中文:
定理 MeasureTheory.LocallyIntegrable.exists_contDiff_dist_le_of_forall_mem_ball_dist_le
  证明: by
  set φ : ContDiffBump (0 : E) := ⟨ε / 2, ε, half_pos hε, half_lt_self hε⟩
  refine ⟨_, ?_, fun a δ => φ.dist_normed_convolution_le hf.aestronglyMeasurable⟩
  exact φ.hasCompactSupport_normed.contDiff_convolution_left _ φ.contDiff_normed hf

Depends on / 依赖: ContDiffBump, aestronglyMeasurable, contDiff_convolution_left, contDiff_normed, dist_normed_convolution_le, half_lt_self, half_pos, hasCompactSupport_normed, hasCompactSupport_normed.contDiff_convolution_left, hf.aestronglyMeasurable
-/
theorem MeasureTheory.LocallyIntegrable.exists_contDiff_dist_le_of_forall_mem_ball_dist_le
    [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]
    (hf : LocallyIntegrable f μ) (hε : 0 < ε) :
    exists g : E -> F, ContDiff Real ∞ g ∧ forall a, forall δ, (forall x in ball a ε, dist (f x) (f a) <= δ) ->
      dist (g a) (f a) <= δ := by
  set φ : ContDiffBump (0 : E) := ⟨ε / 2, ε, half_pos hε, half_lt_self hε⟩
  refine ⟨_, ?_, fun a δ => φ.dist_normed_convolution_le hf.aestronglyMeasurable⟩
  exact φ.hasCompactSupport_normed.contDiff_convolution_left _ φ.contDiff_normed hf

/--
theorem `Continuous.exists_contDiff_dist_le_of_forall_mem_ball_dist_le` / 定理 `Continuous.exists_contDiff_dist_le_of_forall_mem_ball_dist_le`

English:
theorem Continuous.exists_contDiff_dist_le_of_forall_mem_ball_dist_le
  statement: (hf : Continuous f)
  proof: by
  borelize E
  exact (hf.locallyIntegrable (μ := .addHaar)).exists_contDiff_dist_le_of_forall_mem_ball_dist_le hε

中文:
定理 Continuous.exists_contDiff_dist_le_of_forall_mem_ball_dist_le
  结论: (hf : Continuous f)
  证明: by
  borelize E
  exact (hf.locallyIntegrable (μ := .addHaar)).exists_contDiff_dist_le_of_forall_mem_ball_dist_le hε

Depends on / 依赖: addHaar, borelize, exists_contDiff_dist_le_of_forall_mem_ball_dist_le, hf.locallyIntegrable, locallyIntegrable
-/
theorem Continuous.exists_contDiff_dist_le_of_forall_mem_ball_dist_le (hf : Continuous f)
    (hε : 0 < ε) :
    exists g : E -> F, ContDiff Real ∞ g ∧ forall a, forall δ, (forall x in ball a ε, dist (f x) (f a) <= δ) ->
      dist (g a) (f a) <= δ := by
  borelize E
  exact (hf.locallyIntegrable (μ := .addHaar)).exists_contDiff_dist_le_of_forall_mem_ball_dist_le hε

/--
theorem `UniformContinuous.exists_contDiff_dist_le` / 定理 `UniformContinuous.exists_contDiff_dist_le`

English:
theorem UniformContinuous.exists_contDiff_dist_le
  given: (hf : UniformContinuous f) (hε : 0 < ε)
  proof: by
  rcases Metric.uniformContinuous_iff.mp hf (ε / 2) (half_pos hε) with ⟨δ, hδ, hfδ⟩
  rcases hf.continuous.exists_contDiff_dist_le_of_forall_mem_ball_dist_le hδ with ⟨g, hgc, hg⟩
  exact ⟨g, hgc, fun a => (hg a _ fun _ h => (hfδ h).le).trans_lt (half_lt_self hε)⟩

中文:
定理 UniformContinuous.exists_contDiff_dist_le
  条件: (hf : UniformContinuous f) (hε : 0 < ε)
  证明: by
  rcases Metric.uniformContinuous_iff.mp hf (ε / 2) (half_pos hε) with ⟨δ, hδ, hfδ⟩
  rcases hf.continuous.exists_contDiff_dist_le_of_forall_mem_ball_dist_le hδ with ⟨g, hgc, hg⟩
  exact ⟨g, hgc, fun a => (hg a _ fun _ h => (hfδ h).le).trans_lt (half_lt_self hε)⟩

Depends on / 依赖: Metric, Metric.uniformContinuous_iff.mp, continuous, exists_contDiff_dist_le_of_forall_mem_ball_dist_le, half_lt_self, half_pos, hf.continuous.exists_contDiff_dist_le_of_forall_mem_ball_dist_le, trans_lt, uniformContinuous_iff
-/
theorem UniformContinuous.exists_contDiff_dist_le (hf : UniformContinuous f) (hε : 0 < ε) :
    exists g : E -> F, ContDiff Real ∞ g ∧ forall a, dist (g a) (f a) < ε := by
  rcases Metric.uniformContinuous_iff.mp hf (ε / 2) (half_pos hε) with ⟨δ, hδ, hfδ⟩
  rcases hf.continuous.exists_contDiff_dist_le_of_forall_mem_ball_dist_le hδ with ⟨g, hgc, hg⟩
  exact ⟨g, hgc, fun a => (hg a _ fun _ h => (hfδ h).le).trans_lt (half_lt_self hε)⟩

/--
theorem `ContinuousMap.dense_setOfPred_contDiff` / 定理 `ContinuousMap.dense_setOfPred_contDiff`

English:
theorem ContinuousMap.dense_setOfPred_contDiff
  statement: Dense {f : C(E, F) | ContDiff Real ∞ f}
  proof: by
  intro f
  rw [mem_closure_iff_nhds_basis
    (nhds_basis_uniformity uniformity_basis_dist.compactConvergenceUniformity)]
  simp only [Prod.forall, mem_ofPred_eq, and_imp]
  intro K ε hK hε
  have : UniformContinuousOn f (cthickening 1 K) :=
hK.cthickening.uniformContinuousOn_of_continuous by fu

中文:
定理 ContinuousMap.dense_setOfPred_contDiff
  结论: Dense {f : C(E, F) | ContDiff 实数 ∞ f}
  证明: by
  intro f
  rw [mem_closure_iff_nhds_basis
    (nhds_basis_uniformity uniformity_basis_dist.compactConvergenceUniformity)]
  simp only [Prod.forall, mem_ofPred_eq, and_imp]
  intro K ε hK hε
  have : UniformContinuousOn f (cthickening 1 K) :=
hK.cthickening.uniformContinuousOn_of_continuous by fu

Depends on / 依赖: Metric, Metric.uniformContinuousOn_iff.mp, Prod.forall, UniformContinuousOn, and_imp, compactConvergenceUniformity, cthickening, exists_contDiff_dist_le_of_forall_mem_ball_dist_le, fun_prop, hK.cthickening.uniformContinuousOn_of_continuous, half_pos, lt_min, map_continuous, mem_closure_iff_nhds_basis, mem_ofPred_eq, nhds_basis_uniformity, one_pos, uniformContinuousOn_iff, uniformContinuousOn_of_continuous, uniformity_basis_dist
-/
theorem ContinuousMap.dense_setOfPred_contDiff : Dense {f : C(E, F) | ContDiff Real ∞ f} := by
  intro f
  rw [mem_closure_iff_nhds_basis
    (nhds_basis_uniformity uniformity_basis_dist.compactConvergenceUniformity)]
  simp only [Prod.forall, mem_ofPred_eq, and_imp]
  intro K ε hK hε
  have : UniformContinuousOn f (cthickening 1 K) :=
hK.cthickening.uniformContinuousOn_of_continuous by fun_prop
  rcases Metric.uniformContinuousOn_iff.mp this (ε / 2) (half_pos hε) with ⟨δ, hδ, hfδ⟩
  rcases (map_continuous f).exists_contDiff_dist_le_of_forall_mem_ball_dist_le
    (lt_min one_pos hδ) with ⟨g, hgc, hg⟩
  refine ⟨⟨g, hgc.continuous⟩, hgc, fun x hx => (hg _ _ fun y hy => ?_).trans_lt (half_lt_self hε)⟩
  rw [mem_ball]; rw [lt_min_iff] at hy
  exact hfδ _ (mem_cthickening_of_dist_le _ x _ _ hx hy.1.le) _
.le (self_subset_cthickening _ hx) hy.2

@[deprecated (since := "2026-07-09")]
alias ContinuousMap.dense_setOf_contDiff := ContinuousMap.dense_setOfPred_contDiff
