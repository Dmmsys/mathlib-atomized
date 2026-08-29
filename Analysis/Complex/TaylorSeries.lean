/-
Copyright (c) 2024 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Convergence of Taylor series of holomorphic functions

We show that the Taylor series around some point `c : ℂ` of a function `f` that is complex
differentiable on the open ball of radius `r` around `c` converges to `f` on that open ball;
see `Complex.hasSum_taylorSeries_on_ball` and `Complex.taylorSeries_eq_on_ball` for versions
(in terms of `HasSum` and `tsum`, respectively) for functions to a complete normed
space over `ℂ`, and `Complex.taylorSeries_eq_on_ball'` for a variant when `f : ℂ → ℂ`.

There are corresponding statements for `Metric.eball`s; see
`Complex.hasSum_taylorSeries_on_eball`, `Complex.taylorSeries_eq_on_eball`
and `Complex.taylorSeries_eq_on_ball'`.

We also show that the Taylor series around some point `c : ℂ` of a function `f` that is complex
differentiable on all of `ℂ` converges to `f` on `ℂ`;
see `Complex.hasSum_taylorSeries_of_entire`, `Complex.taylorSeries_eq_of_entire` and
`Complex.taylorSeries_eq_of_entire'`.
-/

public section

namespace Complex

open Nat

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Complex E] [CompleteSpace E] ⦃f : Complex -> E⦄

section ball

variable ⦃c : Complex⦄ ⦃r : Real⦄ (hf : DifferentiableOn Complex f (Metric.ball c r))
variable ⦃z : Complex⦄ (hz : z in Metric.ball c r)

include hf hz in
/--
lemma `hasSum_taylorSeries_on_ball` / 引理 `hasSum_taylorSeries_on_ball`

English:
lemma hasSum_taylorSeries_on_ball
  proof: by
  obtain ⟨r', hr', hr'₀, hzr'⟩ : exists r' < r, 0 < r' ∧ z in Metric.ball c r' := by
    obtain ⟨r', h₁, h₂⟩ := exists_between (Metric.mem_ball'.mp hz)
    exact ⟨r', h₂, Metric.pos_of_mem_ball h₁, Metric.mem_ball'.mpr h₁⟩
  lift r' to NNReal using hr'₀.le
  have hz' : z - c in Metric.eball 0 r' 

中文:
引理 hasSum_taylorSeries_on_ball
  证明: by
  obtain ⟨r', hr', hr'₀, hzr'⟩ : exists r' < r, 0 < r' ∧ z in Metric.ball c r' := by
    obtain ⟨r', h₁, h₂⟩ := exists_between (Metric.mem_ball'.mp hz)
    exact ⟨r', h₂, Metric.pos_of_mem_ball h₁, Metric.mem_ball'.mpr h₁⟩
  lift r' to NNReal using hr'₀.le
  have hz' : z - c in Metric.eball 0 r' 

Depends on / 依赖: Metric, Metric.ball, Metric.closedBall_subset_ball, Metric.eball, Metric.eball_coe, Metric.mem_ball, Metric.pos_of_mem_ball, NNReal, add_sub_canc, closedBall_subset_ball, eball_coe, exists_between, hasFPowerSeriesOnBall, hasSum_iteratedFDeriv, hf.mono, mem_ball, mem_ball_iff_norm, pos_of_mem_ball, sub_zero
-/
lemma hasSum_taylorSeries_on_ball :
    HasSum (fun n : Nat => (n ! : Complex)⁻¹ • (z - c) ^ n • iteratedDeriv n f c) (f z) := by
  obtain ⟨r', hr', hr'₀, hzr'⟩ : exists r' < r, 0 < r' ∧ z in Metric.ball c r' := by
    obtain ⟨r', h₁, h₂⟩ := exists_between (Metric.mem_ball'.mp hz)
    exact ⟨r', h₂, Metric.pos_of_mem_ball h₁, Metric.mem_ball'.mpr h₁⟩
  lift r' to NNReal using hr'₀.le
  have hz' : z - c in Metric.eball 0 r' := by
    rw [Metric.eball_coe]
    simpa only [mem_ball_iff_norm, sub_zero] using hzr'
  have H := (hf.mono <| Metric.closedBall_subset_ball hr').hasFPowerSeriesOnBall hr'₀
.hasSum_iteratedFDeriv hz'
  simp only [add_sub_cancel] at H
  convert H with n
  simpa only [iteratedDeriv_eq_iteratedFDeriv, smul_eq_mul, mul_one, Finset.prod_const,
    Finset.card_fin]
    using ((iteratedFDeriv Complex n f c).map_smul_univ (fun _ => z - c) (fun _ => 1)).symm

include hf hz in
/--
lemma `taylorSeries_eq_on_ball` / 引理 `taylorSeries_eq_on_ball`

English:
lemma taylorSeries_eq_on_ball
  proof: (hasSum_taylorSeries_on_ball hf hz).tsum_eq

include hz in

中文:
引理 taylorSeries_eq_on_ball
  证明: (hasSum_taylorSeries_on_ball hf hz).tsum_eq

include hz in

Depends on / 依赖: hasSum_taylorSeries_on_ball, tsum_eq
-/
lemma taylorSeries_eq_on_ball :
    ∑' n : Nat, (n ! : Complex)⁻¹ • (z - c) ^ n • iteratedDeriv n f c = f z :=
  (hasSum_taylorSeries_on_ball hf hz).tsum_eq

include hz in
/--
lemma `taylorSeries_eq_on_ball'` / 引理 `taylorSeries_eq_on_ball'`

English:
lemma taylorSeries_eq_on_ball'
  given: {f : Complex -> Complex} (hf : DifferentiableOn Complex f (Metric.ball c r))
  proof: by
  convert! taylorSeries_eq_on_ball hf hz using 3 with n
  rw [mul_right_comm]; rw [smul_eq_mul]; rw [smul_eq_mul]; rw [mul_assoc]

中文:
引理 taylorSeries_eq_on_ball'
  条件: {f : 复形 -> 复形} (hf : DifferentiableOn 复形 f (Metric.ball c r))
  证明: by
  convert! taylorSeries_eq_on_ball hf hz using 3 with n
  rw [mul_right_comm]; rw [smul_eq_mul]; rw [smul_eq_mul]; rw [mul_assoc]

Depends on / 依赖: convert, mul_assoc, mul_right_comm, smul_eq_mul, taylorSeries_eq_on_ball
-/
lemma taylorSeries_eq_on_ball' {f : Complex -> Complex} (hf : DifferentiableOn Complex f (Metric.ball c r)) :
    ∑' n : Nat, (n ! : Complex)⁻¹ * iteratedDeriv n f c * (z - c) ^ n = f z := by
  convert! taylorSeries_eq_on_ball hf hz using 3 with n
  rw [mul_right_comm]; rw [smul_eq_mul]; rw [smul_eq_mul]; rw [mul_assoc]

end ball

section emetric

variable ⦃c : Complex⦄ ⦃r : ENNReal⦄ (hf : DifferentiableOn Complex f (Metric.eball c r))
variable ⦃z : Complex⦄ (hz : z in Metric.eball c r)

include hf hz in
/--
lemma `hasSum_taylorSeries_on_eball` / 引理 `hasSum_taylorSeries_on_eball`

English:
lemma hasSum_taylorSeries_on_eball
  proof: by
  obtain ⟨r', hzr', hr'⟩ := exists_between (Metric.mem_eball'.mp hz)
  lift r' to NNReal using ne_top_of_lt hr'
  rw [← Metric.mem_eball']; rw [Metric.eball_coe] at hzr'
  refine hasSum_taylorSeries_on_ball ?_ hzr'
  rw [← Metric.eball_coe]
exact hf.mono Metric.eball_subset_eball hr'.le

@[deprec

中文:
引理 hasSum_taylorSeries_on_eball
  证明: by
  obtain ⟨r', hzr', hr'⟩ := exists_between (Metric.mem_eball'.mp hz)
  lift r' to NNReal using ne_top_of_lt hr'
  rw [← Metric.mem_eball']; rw [Metric.eball_coe] at hzr'
  refine hasSum_taylorSeries_on_ball ?_ hzr'
  rw [← Metric.eball_coe]
exact hf.mono Metric.eball_subset_eball hr'.le

@[deprec

Depends on / 依赖: Metric, Metric.eball_coe, Metric.eball_subset_eball, Metric.mem_eball, NNReal, eball_coe, eball_subset_eball, exists_between, hasSum_taylorSeries_on_ball, hf.mono, mem_eball, ne_top_of_lt
-/
lemma hasSum_taylorSeries_on_eball :
    HasSum (fun n : Nat => (n ! : Complex)⁻¹ • (z - c) ^ n • iteratedDeriv n f c) (f z) := by
  obtain ⟨r', hzr', hr'⟩ := exists_between (Metric.mem_eball'.mp hz)
  lift r' to NNReal using ne_top_of_lt hr'
  rw [← Metric.mem_eball']; rw [Metric.eball_coe] at hzr'
  refine hasSum_taylorSeries_on_ball ?_ hzr'
  rw [← Metric.eball_coe]
exact hf.mono Metric.eball_subset_eball hr'.le

@[deprecated (since := "2026-01-24")]
alias hasSum_taylorSeries_on_emetric_ball := hasSum_taylorSeries_on_eball

include hf hz in
/--
lemma `taylorSeries_eq_on_eball` / 引理 `taylorSeries_eq_on_eball`

English:
lemma taylorSeries_eq_on_eball
  proof: (hasSum_taylorSeries_on_eball hf hz).tsum_eq

@[deprecated (since := "2026-01-24")]
alias taylorSeries_eq_on_emetric_ball := taylorSeries_eq_on_eball

include hz in

中文:
引理 taylorSeries_eq_on_eball
  证明: (hasSum_taylorSeries_on_eball hf hz).tsum_eq

@[deprecated (since := "2026-01-24")]
alias taylorSeries_eq_on_emetric_ball := taylorSeries_eq_on_eball

include hz in

Depends on / 依赖: hasSum_taylorSeries_on_eball, tsum_eq
-/
lemma taylorSeries_eq_on_eball :
    ∑' n : Nat, (n ! : Complex)⁻¹ • (z - c) ^ n • iteratedDeriv n f c = f z :=
  (hasSum_taylorSeries_on_eball hf hz).tsum_eq

@[deprecated (since := "2026-01-24")]
alias taylorSeries_eq_on_emetric_ball := taylorSeries_eq_on_eball

include hz in
/--
lemma `taylorSeries_eq_on_eball'` / 引理 `taylorSeries_eq_on_eball'`

English:
lemma taylorSeries_eq_on_eball'
  given: {f : Complex -> Complex} (hf : DifferentiableOn Complex f (Metric.eball c r))
  proof: by
  convert! taylorSeries_eq_on_eball hf hz using 3 with n
  rw [mul_right_comm]; rw [smul_eq_mul]; rw [smul_eq_mul]; rw [mul_assoc]

@[deprecated (since := "2026-01-24")]
alias taylorSeries_eq_on_emetric_ball' := taylorSeries_eq_on_eball'

中文:
引理 taylorSeries_eq_on_eball'
  条件: {f : 复形 -> 复形} (hf : DifferentiableOn 复形 f (Metric.eball c r))
  证明: by
  convert! taylorSeries_eq_on_eball hf hz using 3 with n
  rw [mul_right_comm]; rw [smul_eq_mul]; rw [smul_eq_mul]; rw [mul_assoc]

@[deprecated (since := "2026-01-24")]
alias taylorSeries_eq_on_emetric_ball' := taylorSeries_eq_on_eball'

Depends on / 依赖: convert, mul_assoc, mul_right_comm, smul_eq_mul, taylorSeries_eq_on_eball
-/
lemma taylorSeries_eq_on_eball' {f : Complex -> Complex} (hf : DifferentiableOn Complex f (Metric.eball c r)) :
    ∑' n : Nat, (n ! : Complex)⁻¹ * iteratedDeriv n f c * (z - c) ^ n = f z := by
  convert! taylorSeries_eq_on_eball hf hz using 3 with n
  rw [mul_right_comm]; rw [smul_eq_mul]; rw [smul_eq_mul]; rw [mul_assoc]

@[deprecated (since := "2026-01-24")]
alias taylorSeries_eq_on_emetric_ball' := taylorSeries_eq_on_eball'

end emetric

section entire

variable ⦃f : Complex -> E⦄ (hf : Differentiable Complex f) (c z : Complex)

include hf in
/--
lemma `hasSum_taylorSeries_of_entire` / 引理 `hasSum_taylorSeries_of_entire`

English:
lemma hasSum_taylorSeries_of_entire
  proof: hasSum_taylorSeries_on_eball hf.differentiableOn Metric.mem_eball.mpr
    edist_lt_top ..

include hf in

中文:
引理 hasSum_taylorSeries_of_entire
  证明: hasSum_taylorSeries_on_eball hf.differentiableOn Metric.mem_eball.mpr
    edist_lt_top ..

include hf in

Depends on / 依赖: Metric, Metric.mem_eball.mpr, differentiableOn, edist_lt_top, hasSum_taylorSeries_on_eball, hf.differentiableOn, mem_eball
-/
lemma hasSum_taylorSeries_of_entire :
    HasSum (fun n : Nat => (n ! : Complex)⁻¹ • (z - c) ^ n • iteratedDeriv n f c) (f z) :=
hasSum_taylorSeries_on_eball hf.differentiableOn Metric.mem_eball.mpr
    edist_lt_top ..

include hf in
/--
lemma `taylorSeries_eq_of_entire` / 引理 `taylorSeries_eq_of_entire`

English:
lemma taylorSeries_eq_of_entire
  proof: (hasSum_taylorSeries_of_entire hf c z).tsum_eq

中文:
引理 taylorSeries_eq_of_entire
  证明: (hasSum_taylorSeries_of_entire hf c z).tsum_eq

Depends on / 依赖: hasSum_taylorSeries_of_entire, tsum_eq
-/
lemma taylorSeries_eq_of_entire :
    ∑' n : Nat, (n ! : Complex)⁻¹ • (z - c) ^ n • iteratedDeriv n f c = f z :=
  (hasSum_taylorSeries_of_entire hf c z).tsum_eq

/--
lemma `taylorSeries_eq_of_entire'` / 引理 `taylorSeries_eq_of_entire'`

English:
lemma taylorSeries_eq_of_entire'
  given: {f : Complex -> Complex} (hf : Differentiable Complex f)
  proof: by
  convert! taylorSeries_eq_of_entire hf c z using 3 with n
  rw [mul_right_comm]; rw [smul_eq_mul]; rw [smul_eq_mul]; rw [mul_assoc]

中文:
引理 taylorSeries_eq_of_entire'
  条件: {f : 复形 -> 复形} (hf : 可微 复形 f)
  证明: by
  convert! taylorSeries_eq_of_entire hf c z using 3 with n
  rw [mul_right_comm]; rw [smul_eq_mul]; rw [smul_eq_mul]; rw [mul_assoc]

Depends on / 依赖: convert, mul_assoc, mul_right_comm, smul_eq_mul, taylorSeries_eq_of_entire
-/
lemma taylorSeries_eq_of_entire' {f : Complex -> Complex} (hf : Differentiable Complex f) :
    ∑' n : Nat, (n ! : Complex)⁻¹ * iteratedDeriv n f c * (z - c) ^ n = f z := by
  convert! taylorSeries_eq_of_entire hf c z using 3 with n
  rw [mul_right_comm]; rw [smul_eq_mul]; rw [smul_eq_mul]; rw [mul_assoc]

end entire

end Complex
