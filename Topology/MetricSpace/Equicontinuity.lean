/-
Copyright (c) 2022 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/
module

public import Mathlib.Topology.UniformSpace.Equicontinuity
public import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

/-!
# Equicontinuity in metric spaces

This file contains various facts about (uniform) equicontinuity in metric spaces. Most
importantly, we prove the usual characterization of equicontinuity of `F` at `x₀` in the case of
(pseudo) metric spaces: `∀ ε > 0, ∃ δ > 0, ∀ x, dist x x₀ < δ → ∀ i, dist (F i x₀) (F i x) < ε`,
and we prove that functions sharing a common (local or global) continuity modulus are
(locally or uniformly) equicontinuous.

## Main statements

* `Metric.equicontinuousAt_iff`: characterization of equicontinuity for families of functions
  between (pseudo) metric spaces.
* `Metric.equicontinuousAt_of_continuity_modulus`: convenient way to prove equicontinuity at a
  point of a family of functions to a (pseudo) metric space by showing that they share a common
  *local* continuity modulus.
* `Metric.uniformEquicontinuous_of_continuity_modulus`: convenient way to prove uniform
  equicontinuity of a family of functions to a (pseudo) metric space by showing that they share a
  common *global* continuity modulus.

## Tags

equicontinuity, continuity modulus
-/

public section


open Filter Topology Uniformity

variable {α β ι : Type*} [PseudoMetricSpace α]

namespace Metric

/--
theorem `equicontinuousAt_iff_right` / 定理 `equicontinuousAt_iff_right`

English:
theorem equicontinuousAt_iff_right
  given: {ι : Type*} [TopologicalSpace β] {F : ι -> β -> α} {x₀ : β}
  proof: uniformity_basis_dist.equicontinuousAt_iff_right

中文:
定理 equicontinuousAt_iff_right
  条件: {ι : 类型} [TopologicalSpace β] {F : ι -> β -> α} {x₀ : β}
  证明: uniformity_basis_dist.equicontinuousAt_iff_right

Depends on / 依赖: equicontinuousAt_iff_right, uniformity_basis_dist, uniformity_basis_dist.equicontinuousAt_iff_right
-/
theorem equicontinuousAt_iff_right {ι : Type*} [TopologicalSpace β] {F : ι -> β -> α} {x₀ : β} :
    EquicontinuousAt F x₀ ↔ forall ε > 0, forallᶠ x in 𝓝 x₀, forall i, dist (F i x₀) (F i x) < ε :=
  uniformity_basis_dist.equicontinuousAt_iff_right

/--
theorem `equicontinuousAt_iff` / 定理 `equicontinuousAt_iff`

English:
theorem equicontinuousAt_iff
  given: {ι : Type*} [PseudoMetricSpace β] {F : ι -> β -> α} {x₀ : β}
  proof: nhds_basis_ball.equicontinuousAt_iff uniformity_basis_dist

中文:
定理 equicontinuousAt_iff
  条件: {ι : 类型} [PseudoMetricSpace β] {F : ι -> β -> α} {x₀ : β}
  证明: nhds_basis_ball.equicontinuousAt_iff uniformity_basis_dist

Depends on / 依赖: equicontinuousAt_iff, nhds_basis_ball, nhds_basis_ball.equicontinuousAt_iff, uniformity_basis_dist
-/
theorem equicontinuousAt_iff {ι : Type*} [PseudoMetricSpace β] {F : ι -> β -> α} {x₀ : β} :
    EquicontinuousAt F x₀ ↔ forall ε > 0, exists δ > 0, forall x, dist x x₀ < δ -> forall i, dist (F i x₀) (F i x) < ε :=
  nhds_basis_ball.equicontinuousAt_iff uniformity_basis_dist

/--
theorem `equicontinuousAt_iff_pair` / 定理 `equicontinuousAt_iff_pair`

English:
theorem equicontinuousAt_iff_pair
  statement: {ι : Type*} [TopologicalSpace β] {F : ι -> β -> α}
  proof: by
  rw [equicontinuousAt_iff_pair]
  constructor <;> intro H
  · intro ε hε
    exact H _ (dist_mem_uniformity hε)
  · intro U hU
    rcases mem_uniformity_dist.mp hU with ⟨ε, hε, hεU⟩
    refine Exists.imp (fun V => And.imp_right fun h => ?_) (H _ hε)
    exact fun x hx x' hx' i => hεU (h _ hx _ h

中文:
定理 equicontinuousAt_iff_pair
  结论: {ι : 类型} [TopologicalSpace β] {F : ι -> β -> α}
  证明: by
  rw [equicontinuousAt_iff_pair]
  constructor <;> intro H
  · intro ε hε
    exact H _ (dist_mem_uniformity hε)
  · intro U hU
    rcases mem_uniformity_dist.mp hU with ⟨ε, hε, hεU⟩
    refine Exists.imp (fun V => And.imp_right fun h => ?_) (H _ hε)
    exact fun x hx x' hx' i => hεU (h _ hx _ h
-/
protected theorem equicontinuousAt_iff_pair {ι : Type*} [TopologicalSpace β] {F : ι -> β -> α}
    {x₀ : β} :
    EquicontinuousAt F x₀ ↔
      forall ε > 0, exists U in 𝓝 x₀, forall x in U, forall x' in U, forall i, dist (F i x) (F i x') < ε := by
  rw [equicontinuousAt_iff_pair]
  constructor <;> intro H
  · intro ε hε
    exact H _ (dist_mem_uniformity hε)
  · intro U hU
    rcases mem_uniformity_dist.mp hU with ⟨ε, hε, hεU⟩
    refine Exists.imp (fun V => And.imp_right fun h => ?_) (H _ hε)
    exact fun x hx x' hx' i => hεU (h _ hx _ hx' i)

/--
theorem `uniformEquicontinuous_iff_right` / 定理 `uniformEquicontinuous_iff_right`

English:
theorem uniformEquicontinuous_iff_right
  given: {ι : Type*} [UniformSpace β] {F : ι -> β -> α}
  proof: uniformity_basis_dist.uniformEquicontinuous_iff_right

中文:
定理 uniformEquicontinuous_iff_right
  条件: {ι : 类型} [UniformSpace β] {F : ι -> β -> α}
  证明: uniformity_basis_dist.uniformEquicontinuous_iff_right

Depends on / 依赖: uniformEquicontinuous_iff_right, uniformity_basis_dist, uniformity_basis_dist.uniformEquicontinuous_iff_right
-/
theorem uniformEquicontinuous_iff_right {ι : Type*} [UniformSpace β] {F : ι -> β -> α} :
    UniformEquicontinuous F ↔ forall ε > 0, forallᶠ xy : β × β in 𝓤 β, forall i, dist (F i xy.1) (F i xy.2) < ε :=
  uniformity_basis_dist.uniformEquicontinuous_iff_right

/--
theorem `uniformEquicontinuous_iff` / 定理 `uniformEquicontinuous_iff`

English:
theorem uniformEquicontinuous_iff
  given: {ι : Type*} [PseudoMetricSpace β] {F : ι -> β -> α}
  proof: uniformity_basis_dist.uniformEquicontinuous_iff uniformity_basis_dist

中文:
定理 uniformEquicontinuous_iff
  条件: {ι : 类型} [PseudoMetricSpace β] {F : ι -> β -> α}
  证明: uniformity_basis_dist.uniformEquicontinuous_iff uniformity_basis_dist

Depends on / 依赖: uniformEquicontinuous_iff, uniformity_basis_dist, uniformity_basis_dist.uniformEquicontinuous_iff
-/
theorem uniformEquicontinuous_iff {ι : Type*} [PseudoMetricSpace β] {F : ι -> β -> α} :
    UniformEquicontinuous F ↔
      forall ε > 0, exists δ > 0, forall x y, dist x y < δ -> forall i, dist (F i x) (F i y) < ε :=
  uniformity_basis_dist.uniformEquicontinuous_iff uniformity_basis_dist

/--
theorem `equicontinuousAt_of_continuity_modulus` / 定理 `equicontinuousAt_of_continuity_modulus`

English:
theorem equicontinuousAt_of_continuity_modulus
  statement: {ι : Type*} [TopologicalSpace β] {x₀ : β}
  proof: by
  rw [Metric.equicontinuousAt_iff_right]
  intro ε ε0
  filter_upwards [b_lim (Iio_mem_nhds ε0), H] using fun x hx₁ hx₂ i => (hx₂ i).trans_lt hx₁

中文:
定理 equicontinuousAt_of_continuity_modulus
  结论: {ι : 类型} [TopologicalSpace β] {x₀ : β}
  证明: by
  rw [Metric.equicontinuousAt_iff_right]
  intro ε ε0
  filter_upwards [b_lim (Iio_mem_nhds ε0), H] using fun x hx₁ hx₂ i => (hx₂ i).trans_lt hx₁

Depends on / 依赖: Iio_mem_nhds, Metric, Metric.equicontinuousAt_iff_right, b_lim, equicontinuousAt_iff_right, filter_upwards, trans_lt
-/
theorem equicontinuousAt_of_continuity_modulus {ι : Type*} [TopologicalSpace β] {x₀ : β}
    (b : β -> Real) (b_lim : Tendsto b (𝓝 x₀) (𝓝 0)) (F : ι -> β -> α)
    (H : forallᶠ x in 𝓝 x₀, forall i, dist (F i x₀) (F i x) <= b x) : EquicontinuousAt F x₀ := by
  rw [Metric.equicontinuousAt_iff_right]
  intro ε ε0
  filter_upwards [b_lim (Iio_mem_nhds ε0), H] using fun x hx₁ hx₂ i => (hx₂ i).trans_lt hx₁

/--
theorem `uniformEquicontinuous_of_continuity_modulus` / 定理 `uniformEquicontinuous_of_continuity_modulus`

English:
theorem uniformEquicontinuous_of_continuity_modulus
  statement: {ι : Type*} [PseudoMetricSpace β] (b : Real -> Real)
  proof: by
  rw [Metric.uniformEquicontinuous_iff]
  intro ε ε0
  rcases tendsto_nhds_nhds.1 b_lim ε ε0 with ⟨δ, δ0, hδ⟩
  refine ⟨δ, δ0, fun x y hxy i => ?_⟩
  calc
    dist (F i x) (F i y) <= b (dist x y) := H x y i
    _ <= |b (dist x y)| := le_abs_self _
    _ = dist (b (dist x y)) 0 := by simp [Real.di

中文:
定理 uniformEquicontinuous_of_continuity_modulus
  结论: {ι : 类型} [PseudoMetricSpace β] (b : 实数 -> 实数)
  证明: by
  rw [Metric.uniformEquicontinuous_iff]
  intro ε ε0
  rcases tendsto_nhds_nhds.1 b_lim ε ε0 with ⟨δ, δ0, hδ⟩
  refine ⟨δ, δ0, fun x y hxy i => ?_⟩
  calc
    dist (F i x) (F i y) <= b (dist x y) := H x y i
    _ <= |b (dist x y)| := le_abs_self _
    _ = dist (b (dist x y)) 0 := by simp [Real.di

Depends on / 依赖: Metric, Metric.uniformEquicontinuous_iff, Real.dist_eq, abs_dist, b_lim, dist_eq, le_abs_self, tendsto_nhds_nhds, tsub_zero, uniformEquicontinuous_iff
-/
theorem uniformEquicontinuous_of_continuity_modulus {ι : Type*} [PseudoMetricSpace β] (b : Real -> Real)
    (b_lim : Tendsto b (𝓝 0) (𝓝 0)) (F : ι -> β -> α)
    (H : forall (x y : β) (i), dist (F i x) (F i y) <= b (dist x y)) : UniformEquicontinuous F := by
  rw [Metric.uniformEquicontinuous_iff]
  intro ε ε0
  rcases tendsto_nhds_nhds.1 b_lim ε ε0 with ⟨δ, δ0, hδ⟩
  refine ⟨δ, δ0, fun x y hxy i => ?_⟩
  calc
    dist (F i x) (F i y) <= b (dist x y) := H x y i
    _ <= |b (dist x y)| := le_abs_self _
    _ = dist (b (dist x y)) 0 := by simp [Real.dist_eq]
    _ < ε := hδ (by simpa only [Real.dist_eq, tsub_zero, abs_dist] using hxy)

/--
theorem `equicontinuous_of_continuity_modulus` / 定理 `equicontinuous_of_continuity_modulus`

English:
theorem equicontinuous_of_continuity_modulus
  statement: {ι : Type*} [PseudoMetricSpace β] (b : Real -> Real)
  proof: (uniformEquicontinuous_of_continuity_modulus b b_lim F H).equicontinuous

中文:
定理 equicontinuous_of_continuity_modulus
  结论: {ι : 类型} [PseudoMetricSpace β] (b : 实数 -> 实数)
  证明: (uniformEquicontinuous_of_continuity_modulus b b_lim F H).equicontinuous

Depends on / 依赖: b_lim, equicontinuous, uniformEquicontinuous_of_continuity_modulus
-/
theorem equicontinuous_of_continuity_modulus {ι : Type*} [PseudoMetricSpace β] (b : Real -> Real)
    (b_lim : Tendsto b (𝓝 0) (𝓝 0)) (F : ι -> β -> α)
    (H : forall (x y : β) (i), dist (F i x) (F i y) <= b (dist x y)) : Equicontinuous F :=
  (uniformEquicontinuous_of_continuity_modulus b b_lim F H).equicontinuous

end Metric
