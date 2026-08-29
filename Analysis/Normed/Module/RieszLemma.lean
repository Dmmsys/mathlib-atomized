/-
Copyright (c) 2019 Jean Lo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean Lo, Yury Kudryashov
-/
module

public import Mathlib.Analysis.Normed.Module.RCLike.Real
public import Mathlib.Analysis.Normed.Module.RCLike.Basic
public import Mathlib.Analysis.Seminorm
public import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
# Applications of the Hausdorff distance in normed spaces

Riesz's lemma, stated for a normed space over a normed field: for any
closed proper subspace `F` of `E`, there is a nonzero `x` such that `‖x - F‖`
is at least `r * ‖x‖` for any `r < 1`. This is `riesz_lemma`.

In a nontrivially normed field (with an element `c` of norm `> 1`) and any `R > ‖c‖`, one can
guarantee `‖x‖ ≤ R` and `‖x - y‖ ≥ 1` for any `y` in `F`. This is `riesz_lemma_of_norm_lt`.

For a normed space over an `RCLike` field, one can find an element of norm exactly `1` with the same
property. This is `riesz_lemma_one`.

A further lemma, `Metric.closedBall_infDist_compl_subset_closure`, finds a *closed* ball within
the closure of a set `s` of optimal distance from a point in `x` to the frontier of `s`.
-/

public section


open Set Metric

open Topology

variable {𝕜 : Type*} [NormedField 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {F : Type*} [SeminormedAddCommGroup F] [NormedSpace Real F]

/--
theorem `riesz_lemma` / 定理 `riesz_lemma`

English:
theorem riesz_lemma
  statement: {F : Subspace 𝕜 E} (hFc : IsClosed (F : Set E)) (hF : exists x : E, x ∉ F) {r : Real}
  proof: by
  obtain ⟨x, hx⟩ : exists x : E, x ∉ F := hF
  let d := Metric.infDist x F
  have hFn : (F : Set E).Nonempty := ⟨_, F.zero_mem⟩
  have hdp : 0 < d :=
    lt_of_le_of_ne Metric.infDist_nonneg fun heq =>
      hx ((hFc.mem_iff_infDist_zero hFn).2 heq.symm)
  let r' := max r 2⁻¹
  have hr' : r' < 1 

中文:
定理 riesz_lemma
  结论: {F : 子空间 𝕜 E} (hFc : 是闭集 (F : 集合 E)) (hF : 存在 x : E, x ∉ F) {r : 实数}
  证明: by
  obtain ⟨x, hx⟩ : exists x : E, x ∉ F := hF
  let d := Metric.infDist x F
  have hFn : (F : Set E).Nonempty := ⟨_, F.zero_mem⟩
  have hdp : 0 < d :=
    lt_of_le_of_ne Metric.infDist_nonneg fun heq =>
      hx ((hFc.mem_iff_infDist_zero hFn).2 heq.symm)
  let r' := max r 2⁻¹
  have hr' : r' < 1 

Depends on / 依赖: F.zero_mem, Metric, Metric.infDist, Metric.infDist_nonneg, Nonempty, hFc.mem_iff_infDist_zero, heq.symm, infDist, infDist_nonneg, le_max_right, lt_of_le_of_ne, lt_of_lt_of_le, max_lt_iff, mem_iff_infDist_zero, mul_lt_iff_lt_one_right, true_and, zero_mem
-/
theorem riesz_lemma {F : Subspace 𝕜 E} (hFc : IsClosed (F : Set E)) (hF : exists x : E, x ∉ F) {r : Real}
    (hr : r < 1) : exists x₀ : E, x₀ ∉ F ∧ forall y in F, r * ‖x₀‖ <= ‖x₀ - y‖ := by
  obtain ⟨x, hx⟩ : exists x : E, x ∉ F := hF
  let d := Metric.infDist x F
  have hFn : (F : Set E).Nonempty := ⟨_, F.zero_mem⟩
  have hdp : 0 < d :=
    lt_of_le_of_ne Metric.infDist_nonneg fun heq =>
      hx ((hFc.mem_iff_infDist_zero hFn).2 heq.symm)
  let r' := max r 2⁻¹
  have hr' : r' < 1 := by
    simp only [r', max_lt_iff, hr, true_and]
    norm_num
  have hlt : 0 < r' := lt_of_lt_of_le (by simp) (le_max_right r 2⁻¹)
  have hdlt : d < d / r' := (lt_div_iff₀ hlt).mpr ((mul_lt_iff_lt_one_right hdp).2 hr')
  obtain ⟨y₀, hy₀F, hxy₀⟩ : exists y in F, dist x y < d / r' := (Metric.infDist_lt_iff hFn).mp hdlt
  have x_ne_y₀ : x - y₀ ∉ F := by
    by_contra h
    have : x - y₀ + y₀ in F := F.add_mem h hy₀F
    simp only [neg_add_cancel_right, sub_eq_add_neg] at this
    exact hx this
  refine ⟨x - y₀, x_ne_y₀, fun y hy => le_of_lt ?_⟩
  have hy₀y : y₀ + y in F := F.add_mem hy₀F hy
  calc
    r * ‖x - y₀‖ <= r' * ‖x - y₀‖ := by gcongr; apply le_max_left
    _ < d := by
      rw [← dist_eq_norm]
      exact (lt_div_iff₀' hlt).1 hxy₀
    _ <= dist x (y₀ + y) := Metric.infDist_le_dist_of_mem hy₀y
    _ = ‖x - y₀ - y‖ := by rw [sub_sub, dist_eq_norm]

/--
theorem `riesz_lemma_of_norm_lt` / 定理 `riesz_lemma_of_norm_lt`

English:
theorem riesz_lemma_of_norm_lt
  statement: {c : 𝕜} (hc : 1 < ‖c‖) {R : Real} (hR : ‖c‖ < R) {F : Subspace 𝕜 E}
  proof: by
  have Rpos : 0 < R := (norm_nonneg _).trans_lt hR
  have : ‖c‖ / R < 1 := by
    rw [div_lt_iff₀ Rpos]
    simpa using hR
  rcases riesz_lemma hFc hF this with ⟨x, xF, hx⟩
  have x0 : x != 0 := fun H => by simp [H] at xF
  obtain ⟨d, d0, dxlt, ledx, -⟩ :
    exists d : 𝕜, d != 0 ∧ ‖d • x‖ < R ∧ 

中文:
定理 riesz_lemma_of_norm_lt
  结论: {c : 𝕜} (hc : 1 < ‖c‖) {R : 实数} (hR : ‖c‖ < R) {F : 子空间 𝕜 E}
  证明: by
  have Rpos : 0 < R := (norm_nonneg _).trans_lt hR
  have : ‖c‖ / R < 1 := by
    rw [div_lt_iff₀ Rpos]
    simpa using hR
  rcases riesz_lemma hFc hF this with ⟨x, xF, hx⟩
  have x0 : x != 0 := fun H => by simp [H] at xF
  obtain ⟨d, d0, dxlt, ledx, -⟩ :
    exists d : 𝕜, d != 0 ∧ ‖d • x‖ < R ∧ 

Depends on / 依赖: dxlt.le, norm_nonneg, rescale_to_shell, riesz_lemma, smul_smul, trans_lt
-/
theorem riesz_lemma_of_norm_lt {c : 𝕜} (hc : 1 < ‖c‖) {R : Real} (hR : ‖c‖ < R) {F : Subspace 𝕜 E}
    (hFc : IsClosed (F : Set E)) (hF : exists x : E, x ∉ F) :
    exists x₀ : E, ‖x₀‖ <= R ∧ forall y in F, 1 <= ‖x₀ - y‖ := by
  have Rpos : 0 < R := (norm_nonneg _).trans_lt hR
  have : ‖c‖ / R < 1 := by
    rw [div_lt_iff₀ Rpos]
    simpa using hR
  rcases riesz_lemma hFc hF this with ⟨x, xF, hx⟩
  have x0 : x != 0 := fun H => by simp [H] at xF
  obtain ⟨d, d0, dxlt, ledx, -⟩ :
    exists d : 𝕜, d != 0 ∧ ‖d • x‖ < R ∧ R / ‖c‖ <= ‖d • x‖ ∧ ‖d‖⁻¹ <= R⁻¹ * ‖c‖ * ‖x‖ :=
    rescale_to_shell hc Rpos x0
  refine ⟨d • x, dxlt.le, fun y hy => ?_⟩
  set y' := d⁻¹ • y
  have yy' : y = d • y' := by simp [y', smul_smul, mul_inv_cancel₀ d0]
  calc
    1 = ‖c‖ / R * (R / ‖c‖) := by field
    _ <= ‖c‖ / R * ‖d • x‖ := by gcongr
    _ = ‖d‖ * (‖c‖ / R * ‖x‖) := by
      simp only [norm_smul]
      ring
    _ <= ‖d‖ * ‖x - y'‖ := by gcongr; exact hx y' (by simp [y', Submodule.smul_mem _ _ hy])
    _ = ‖d • x - y‖ := by rw [yy', ← smul_sub, norm_smul]

/--
theorem `Metric.closedBall_infDist_compl_subset_closure` / 定理 `Metric.closedBall_infDist_compl_subset_closure`

English:
theorem Metric.closedBall_infDist_compl_subset_closure
  given: {x : F} {s : Set F} (hx : x in s)
  proof: by
  rcases eq_or_ne (infDist x sᶜ) 0 with h₀ | h₀
  · rw [h₀, closedBall_zero']
    exact closure_mono (singleton_subset_iff.2 hx)
  · rw [← closure_ball x h₀]
    exact closure_mono ball_infDist_compl_subset

中文:
定理 Metric.closedBall_infDist_compl_subset_closure
  条件: {x : F} {s : 集合 F} (hx : x in s)
  证明: by
  rcases eq_or_ne (infDist x sᶜ) 0 with h₀ | h₀
  · rw [h₀, closedBall_zero']
    exact closure_mono (singleton_subset_iff.2 hx)
  · rw [← closure_ball x h₀]
    exact closure_mono ball_infDist_compl_subset

Depends on / 依赖: ball_infDist_compl_subset, closedBall_zero, closure_ball, closure_mono, eq_or_ne, infDist, singleton_subset_iff
-/
theorem Metric.closedBall_infDist_compl_subset_closure {x : F} {s : Set F} (hx : x in s) :
    closedBall x (infDist x sᶜ) subseteq closure s := by
  rcases eq_or_ne (infDist x sᶜ) 0 with h₀ | h₀
  · rw [h₀, closedBall_zero']
    exact closure_mono (singleton_subset_iff.2 hx)
  · rw [← closure_ball x h₀]
    exact closure_mono ball_infDist_compl_subset

/--
theorem `riesz_lemma_of_lt_one` / 定理 `riesz_lemma_of_lt_one`

English:
theorem riesz_lemma_of_lt_one
  statement: {𝕜 : Type*} [RCLike 𝕜]
  proof: by
  obtain ⟨x₀, hx₀, h⟩ := riesz_lemma hFc hF hr
  have hx₀' : x₀ != 0 := by rintro rfl; simp at hx₀
  refine ⟨(‖x₀‖⁻¹ : 𝕜) • x₀, ?_, norm_smul_inv_norm hx₀', ?_⟩
  · rwa [Submodule.smul_mem_iff]
    simpa
  intro y hy
  have h₂ : ‖(‖x₀‖ : 𝕜)⁻¹ • (x₀ - (‖x₀‖ : 𝕜) • y)‖ = ‖x₀‖⁻¹ * ‖x₀ - (‖x₀‖ : 𝕜) •

中文:
定理 riesz_lemma_of_lt_one
  结论: {𝕜 : 类型} [RCLike 𝕜]
  证明: by
  obtain ⟨x₀, hx₀, h⟩ := riesz_lemma hFc hF hr
  have hx₀' : x₀ != 0 := by rintro rfl; simp at hx₀
  refine ⟨(‖x₀‖⁻¹ : 𝕜) • x₀, ?_, norm_smul_inv_norm hx₀', ?_⟩
  · rwa [Submodule.smul_mem_iff]
    simpa
  intro y hy
  have h₂ : ‖(‖x₀‖ : 𝕜)⁻¹ • (x₀ - (‖x₀‖ : 𝕜) • y)‖ = ‖x₀‖⁻¹ * ‖x₀ - (‖x₀‖ : 𝕜) •

Depends on / 依赖: F.smul_mem, Submodule, Submodule.smul_mem_iff, norm_algebraMap, norm_inv, norm_norm, norm_smul, norm_smul_inv_norm, riesz_lemma, smul_mem, smul_mem_iff, smul_sub
-/
theorem riesz_lemma_of_lt_one {𝕜 : Type*} [RCLike 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {F : Subspace 𝕜 E} (hFc : IsClosed (F : Set E)) (hF : exists (x : E), x ∉ F) {r : Real} (hr : r < 1) :
    exists x₀ ∉ F, ‖x₀‖ = 1 ∧ forall y in F, r <= ‖x₀ - y‖ := by
  obtain ⟨x₀, hx₀, h⟩ := riesz_lemma hFc hF hr
  have hx₀' : x₀ != 0 := by rintro rfl; simp at hx₀
  refine ⟨(‖x₀‖⁻¹ : 𝕜) • x₀, ?_, norm_smul_inv_norm hx₀', ?_⟩
  · rwa [Submodule.smul_mem_iff]
    simpa
  intro y hy
  have h₂ : ‖(‖x₀‖ : 𝕜)⁻¹ • (x₀ - (‖x₀‖ : 𝕜) • y)‖ = ‖x₀‖⁻¹ * ‖x₀ - (‖x₀‖ : 𝕜) • y‖ := by
    rw [norm_smul]; rw [norm_inv]; rw [norm_algebraMap']; rw [norm_norm]
  have h₁ := h ((‖x₀‖ : 𝕜) • y) (F.smul_mem _ hy)
  rwa [← le_inv_mul_iff₀' (by simpa), ← h₂, smul_sub, inv_smul_smul₀] at h₁
  simpa using hx₀'
