/-
Copyright (c) 2022 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Analysis.Analytic.Linear
public import Mathlib.Analysis.Analytic.Composition
public import Mathlib.Analysis.Analytic.Constructions
public import Mathlib.Analysis.Normed.Module.Completion
public import Mathlib.Analysis.Analytic.ChangeOrigin

/-!
# Uniqueness principle for analytic functions

We show that two analytic functions which coincide around a point coincide on whole connected sets,
in `AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq`.
-/

public section


variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

open Set

open scoped Topology ENNReal NNReal

/-!
### Uniqueness of power series
If a function `f : E → F` has two representations as power series at a point `x : E`, corresponding
to formal multilinear series `p₁` and `p₂`, then these representations agree term-by-term. That is,
for any `n : ℕ` and `y : E`, `p₁ n (fun i ↦ y) = p₂ n (fun i ↦ y)`. In the one-dimensional case,
when `f : 𝕜 → E`, the continuous multilinear maps `p₁ n` and `p₂ n` are given by
`ContinuousMultilinearMap.mkPiRing`, and hence are determined completely by the value of
`p₁ n (fun i ↦ 1)`, so `p₁ = p₂`. Consequently, the radius of convergence for one series can be
transferred to the other.
-/

section Uniqueness

open ContinuousMultilinearMap

/--
theorem `Asymptotics.IsBigO.continuousMultilinearMap_apply_eq_zero` / 定理 `Asymptotics.IsBigO.continuousMultilinearMap_apply_eq_zero`

English:
theorem Asymptotics.IsBigO.continuousMultilinearMap_apply_eq_zero
  statement: {n : Nat} {p : E [×n]->L[𝕜] F}
  proof: by
  obtain ⟨c, c_pos, hc⟩ := h.exists_pos
  obtain ⟨t, ht, t_open, z_mem⟩ := eventually_nhds_iff.mp (isBigOWith_iff.mp hc)
  obtain ⟨δ, δ_pos, δε⟩ := (Metric.isOpen_iff.mp t_open) 0 z_mem
  clear h hc z_mem
  rcases n with - | n
  · exact norm_eq_zero.mp (by
      simpa only [fin0_apply_norm, norm_

中文:
定理 Asymptotics.IsBigO.continuousMultilinearMap_apply_eq_zero
  结论: {n : 自然数} {p : E [×n]->L[𝕜] F}
  证明: by
  obtain ⟨c, c_pos, hc⟩ := h.exists_pos
  obtain ⟨t, ht, t_open, z_mem⟩ := eventually_nhds_iff.mp (isBigOWith_iff.mp hc)
  obtain ⟨δ, δ_pos, δε⟩ := (Metric.isOpen_iff.mp t_open) 0 z_mem
  clear h hc z_mem
  rcases n with - | n
  · exact norm_eq_zero.mp (by
      simpa only [fin0_apply_norm, norm_

Depends on / 依赖: Classical, Classical.em, Metric, Metric.isOpen_iff.mp, Metric.mem_ball_self, Or.elim, c_pos, eventually_nhds_iff, eventually_nhds_iff.mp, exists_pos, fin0_apply_norm, h.exists_pos, isBigOWith_iff, isBigOWith_iff.mp, isOpen_iff, map_zero, mem_ball_self, mul_zero, norm_eq_zero, norm_eq_zero.mp
-/
theorem Asymptotics.IsBigO.continuousMultilinearMap_apply_eq_zero {n : Nat} {p : E [×n]->L[𝕜] F}
    (h : (fun y => p fun _ => y) =O[𝓝 0] fun y => ‖y‖ ^ (n + 1)) (y : E) : (p fun _ => y) = 0 := by
  obtain ⟨c, c_pos, hc⟩ := h.exists_pos
  obtain ⟨t, ht, t_open, z_mem⟩ := eventually_nhds_iff.mp (isBigOWith_iff.mp hc)
  obtain ⟨δ, δ_pos, δε⟩ := (Metric.isOpen_iff.mp t_open) 0 z_mem
  clear h hc z_mem
  rcases n with - | n
  · exact norm_eq_zero.mp (by
      simpa only [fin0_apply_norm, norm_eq_zero, norm_zero, zero_add, pow_one,
        mul_zero, norm_le_zero_iff] using! ht 0 (δε (Metric.mem_ball_self δ_pos)))
  · refine Or.elim (Classical.em (y = 0))
      (fun hy => by simpa only [hy] using! p.map_zero) fun hy => ?_
    replace hy := norm_pos_iff.mpr hy
    refine norm_eq_zero.mp (le_antisymm (le_of_forall_pos_le_add fun ε ε_pos => ?_) (norm_nonneg _))
    have h₀ := _root_.mul_pos c_pos (pow_pos hy (n.succ + 1))
    obtain ⟨k, k_pos, k_norm⟩ := NormedField.exists_norm_lt 𝕜
      (lt_min (mul_pos δ_pos (inv_pos.mpr hy)) (mul_pos ε_pos (inv_pos.mpr h₀)))
    have h₁ : ‖k • y‖ < δ := by
      rw [norm_smul]
      exact inv_mul_cancel_right₀ hy.ne.symm δ ▸
        mul_lt_mul_of_pos_right (lt_of_lt_of_le k_norm (min_le_left _ _)) hy
    have h₂ :=
      calc
        ‖p fun _ => k • y‖ <= c * ‖k • y‖ ^ (n.succ + 1) := by
          simpa only [norm_pow, _root_.norm_norm] using! ht (k • y) (δε (mem_ball_zero_iff.mpr h₁))
        _ = ‖k‖ ^ n.succ * (‖k‖ * (c * ‖y‖ ^ (n.succ + 1))) := by
          simp only [norm_smul, mul_pow]
          ring
    have h₃ : ‖k‖ * (c * ‖y‖ ^ (n.succ + 1)) < ε :=
      inv_mul_cancel_right₀ h₀.ne.symm ε ▸
        mul_lt_mul_of_pos_right (lt_of_lt_of_le k_norm (min_le_right _ _)) h₀
    calc
      ‖p fun _ => y‖ = ‖k⁻¹ ^ n.succ‖ * ‖p fun _ => k • y‖ := by
        simpa only [inv_smul_smul₀ (norm_pos_iff.mp k_pos), norm_smul, Finset.prod_const,
          Finset.card_fin] using!
          congr_arg norm (p.map_smul_univ (fun _ : Fin n.succ => k⁻¹) fun _ : Fin n.succ => k • y)
      _ <= ‖k⁻¹ ^ n.succ‖ * (‖k‖ ^ n.succ * (‖k‖ * (c * ‖y‖ ^ (n.succ + 1)))) := by gcongr
      _ = ‖(k⁻¹ * k) ^ n.succ‖ * (‖k‖ * (c * ‖y‖ ^ (n.succ + 1))) := by
        rw [← mul_assoc]
        simp [norm_mul, mul_pow]
      _ <= 0 + ε := by
        rw [inv_mul_cancel₀ (norm_pos_iff.mp k_pos)]
        simpa using! h₃.le

/--
theorem `HasFPowerSeriesAt.apply_eq_zero` / 定理 `HasFPowerSeriesAt.apply_eq_zero`

English:
theorem HasFPowerSeriesAt.apply_eq_zero
  statement: {p : FormalMultilinearSeries 𝕜 E F} {x : E}
  proof: by
  refine Nat.strong_induction_on n fun k hk => ?_
  have psum_eq : p.partialSum (k + 1) = fun y => p k fun _ => y := by
    funext z
    refine Finset.sum_eq_single _ (fun b hb hnb => ?_) fun hn => ?_
    · have := Finset.mem_range_succ_iff.mp hb
      simp only [hk b (this.lt_of_ne hnb)]
    · e

中文:
定理 HasFPowerSeriesAt.apply_eq_zero
  结论: {p : FormalMultilinearSeries 𝕜 E F} {x : E}
  证明: by
  refine Nat.strong_induction_on n fun k hk => ?_
  have psum_eq : p.partialSum (k + 1) = fun y => p k fun _ => y := by
    funext z
    refine Finset.sum_eq_single _ (fun b hb hnb => ?_) fun hn => ?_
    · have := Finset.mem_range_succ_iff.mp hb
      simp only [hk b (this.lt_of_ne hnb)]
    · e

Depends on / 依赖: Asymptotics, Asymptotics.isBigO_neg_left, False.elim, Finset, Finset.mem_range.mpr, Finset.mem_range_succ_iff.mp, Finset.sum_eq_single, Nat.strong_induction_on, Pi.zero_apply, continuousMultilinearMap_apply_e, h.continuousMultilinearMap_apply_e, h.isBigO_sub_partialSum_pow, isBigO_neg_left, isBigO_sub_partialSum_pow, k.succ, lt_add_one, lt_of_ne, mem_range, mem_range_succ_iff, p.partialSum
-/
theorem HasFPowerSeriesAt.apply_eq_zero {p : FormalMultilinearSeries 𝕜 E F} {x : E}
    (h : HasFPowerSeriesAt 0 p x) (n : Nat) : forall y : E, (p n fun _ => y) = 0 := by
  refine Nat.strong_induction_on n fun k hk => ?_
  have psum_eq : p.partialSum (k + 1) = fun y => p k fun _ => y := by
    funext z
    refine Finset.sum_eq_single _ (fun b hb hnb => ?_) fun hn => ?_
    · have := Finset.mem_range_succ_iff.mp hb
      simp only [hk b (this.lt_of_ne hnb)]
    · exact False.elim (hn (Finset.mem_range.mpr (lt_add_one k)))
  replace h := h.isBigO_sub_partialSum_pow k.succ
  simp only [psum_eq, zero_sub, Pi.zero_apply, Asymptotics.isBigO_neg_left] at h
  exact h.continuousMultilinearMap_apply_eq_zero

/--
theorem `HasFPowerSeriesAt.eq_zero` / 定理 `HasFPowerSeriesAt.eq_zero`

English:
theorem HasFPowerSeriesAt.eq_zero
  statement: {p : FormalMultilinearSeries 𝕜 𝕜 E} {x : 𝕜}
  proof: by
  ext n
  rw [← mkPiRing_apply_one_eq_self (p n)]
  simp [h.apply_eq_zero n 1]

中文:
定理 HasFPowerSeriesAt.eq_zero
  结论: {p : FormalMultilinearSeries 𝕜 𝕜 E} {x : 𝕜}
  证明: by
  ext n
  rw [← mkPiRing_apply_one_eq_self (p n)]
  simp [h.apply_eq_zero n 1]

Depends on / 依赖: apply_eq_zero, h.apply_eq_zero, mkPiRing_apply_one_eq_self
-/
theorem HasFPowerSeriesAt.eq_zero {p : FormalMultilinearSeries 𝕜 𝕜 E} {x : 𝕜}
    (h : HasFPowerSeriesAt 0 p x) : p = 0 := by
  ext n
  rw [← mkPiRing_apply_one_eq_self (p n)]
  simp [h.apply_eq_zero n 1]

/--
theorem `HasFPowerSeriesAt.eq_formalMultilinearSeries` / 定理 `HasFPowerSeriesAt.eq_formalMultilinearSeries`

English:
theorem HasFPowerSeriesAt.eq_formalMultilinearSeries
  statement: {p₁ p₂ : FormalMultilinearSeries 𝕜 𝕜 E}
  proof: sub_eq_zero.mp (HasFPowerSeriesAt.eq_zero (x := x) (by simpa only [sub_self] using h₁.sub h₂))

中文:
定理 HasFPowerSeriesAt.eq_formalMultilinearSeries
  结论: {p₁ p₂ : FormalMultilinearSeries 𝕜 𝕜 E}
  证明: sub_eq_zero.mp (HasFPowerSeriesAt.eq_zero (x := x) (by simpa only [sub_self] using h₁.sub h₂))

Depends on / 依赖: HasFPowerSeriesAt, HasFPowerSeriesAt.eq_zero, eq_zero, sub_eq_zero, sub_eq_zero.mp, sub_self
-/
theorem HasFPowerSeriesAt.eq_formalMultilinearSeries {p₁ p₂ : FormalMultilinearSeries 𝕜 𝕜 E}
    {f : 𝕜 -> E} {x : 𝕜} (h₁ : HasFPowerSeriesAt f p₁ x) (h₂ : HasFPowerSeriesAt f p₂ x) : p₁ = p₂ :=
  sub_eq_zero.mp (HasFPowerSeriesAt.eq_zero (x := x) (by simpa only [sub_self] using h₁.sub h₂))

/--
theorem `HasFPowerSeriesAt.eq_formalMultilinearSeries_of_eventually` / 定理 `HasFPowerSeriesAt.eq_formalMultilinearSeries_of_eventually`

English:
theorem HasFPowerSeriesAt.eq_formalMultilinearSeries_of_eventually
  proof: (hp.congr heq).eq_formalMultilinearSeries hq

中文:
定理 HasFPowerSeriesAt.eq_formalMultilinearSeries_of_eventually
  证明: (hp.congr heq).eq_formalMultilinearSeries hq

Depends on / 依赖: eq_formalMultilinearSeries, hp.congr
-/
theorem HasFPowerSeriesAt.eq_formalMultilinearSeries_of_eventually
    {p q : FormalMultilinearSeries 𝕜 𝕜 E} {f g : 𝕜 -> E} {x : 𝕜} (hp : HasFPowerSeriesAt f p x)
    (hq : HasFPowerSeriesAt g q x) (heq : forallᶠ z in 𝓝 x, f z = g z) : p = q :=
  (hp.congr heq).eq_formalMultilinearSeries hq

/--
theorem `HasFPowerSeriesAt.eq_zero_of_eventually` / 定理 `HasFPowerSeriesAt.eq_zero_of_eventually`

English:
theorem HasFPowerSeriesAt.eq_zero_of_eventually
  statement: {p : FormalMultilinearSeries 𝕜 𝕜 E} {f : 𝕜 -> E}
  proof: (hp.congr hf).eq_zero

中文:
定理 HasFPowerSeriesAt.eq_zero_of_eventually
  结论: {p : FormalMultilinearSeries 𝕜 𝕜 E} {f : 𝕜 -> E}
  证明: (hp.congr hf).eq_zero

Depends on / 依赖: eq_zero, hp.congr
-/
theorem HasFPowerSeriesAt.eq_zero_of_eventually {p : FormalMultilinearSeries 𝕜 𝕜 E} {f : 𝕜 -> E}
    {x : 𝕜} (hp : HasFPowerSeriesAt f p x) (hf : f =ᶠ[𝓝 x] 0) : p = 0 :=
  (hp.congr hf).eq_zero

/--
theorem `HasFPowerSeriesOnBall.exchange_radius` / 定理 `HasFPowerSeriesOnBall.exchange_radius`

English:
theorem HasFPowerSeriesOnBall.exchange_radius
  statement: {p₁ p₂ : FormalMultilinearSeries 𝕜 𝕜 E} {f : 𝕜 -> E}
  proof: h₂.hasFPowerSeriesAt.eq_formalMultilinearSeries h₁.hasFPowerSeriesAt ▸ h₂

中文:
定理 HasFPowerSeriesOnBall.exchange_radius
  结论: {p₁ p₂ : FormalMultilinearSeries 𝕜 𝕜 E} {f : 𝕜 -> E}
  证明: h₂.hasFPowerSeriesAt.eq_formalMultilinearSeries h₁.hasFPowerSeriesAt ▸ h₂

Depends on / 依赖: eq_formalMultilinearSeries, hasFPowerSeriesAt, hasFPowerSeriesAt.eq_formalMultilinearSeries
-/
theorem HasFPowerSeriesOnBall.exchange_radius {p₁ p₂ : FormalMultilinearSeries 𝕜 𝕜 E} {f : 𝕜 -> E}
    {r₁ r₂ : Real>=0∞} {x : 𝕜} (h₁ : HasFPowerSeriesOnBall f p₁ x r₁)
    (h₂ : HasFPowerSeriesOnBall f p₂ x r₂) : HasFPowerSeriesOnBall f p₁ x r₂ :=
  h₂.hasFPowerSeriesAt.eq_formalMultilinearSeries h₁.hasFPowerSeriesAt ▸ h₂

/--
theorem `HasFPowerSeriesOnBall.r_eq_top_of_exists` / 定理 `HasFPowerSeriesOnBall.r_eq_top_of_exists`

English:
theorem HasFPowerSeriesOnBall.r_eq_top_of_exists
  statement: {f : 𝕜 -> E} {r : Real>=0∞} {x : 𝕜}
  proof: { r_le := ENNReal.le_of_forall_pos_nnreal_lt fun r hr _ =>
      let ⟨_, hp'⟩ := h' r hr
      (h.exchange_radius hp').r_le
    r_pos := ENNReal.coe_lt_top
    hasSum := fun {y} _ =>
      let ⟨r', hr'⟩ := exists_gt ‖y‖₊
      let ⟨_, hp'⟩ := h' r' hr'.ne_bot.bot_lt
(h.exchange_radius hp').hasSum me

中文:
定理 HasFPowerSeriesOnBall.r_eq_top_of_exists
  结论: {f : 𝕜 -> E} {r : 实数>=0∞} {x : 𝕜}
  证明: { r_le := ENNReal.le_of_forall_pos_nnreal_lt fun r hr _ =>
      let ⟨_, hp'⟩ := h' r hr
      (h.exchange_radius hp').r_le
    r_pos := ENNReal.coe_lt_top
    hasSum := fun {y} _ =>
      let ⟨r', hr'⟩ := exists_gt ‖y‖₊
      let ⟨_, hp'⟩ := h' r' hr'.ne_bot.bot_lt
(h.exchange_radius hp').hasSum me

Depends on / 依赖: ENNReal, ENNReal.coe_lt_coe, ENNReal.coe_lt_top, ENNReal.le_of_forall_pos_nnreal_lt, bot_lt, coe_lt_coe, coe_lt_top, exchange_radius, exists_gt, h.exchange_radius, hasSum, le_of_forall_pos_nnreal_lt, mem_eball_zero_iff, mem_eball_zero_iff.mpr, ne_bot, ne_bot.bot_lt, r_le, r_pos
-/
theorem HasFPowerSeriesOnBall.r_eq_top_of_exists {f : 𝕜 -> E} {r : Real>=0∞} {x : 𝕜}
    {p : FormalMultilinearSeries 𝕜 𝕜 E} (h : HasFPowerSeriesOnBall f p x r)
    (h' : forall (r' : Real>=0) (_ : 0 < r'), exists p' : FormalMultilinearSeries 𝕜 𝕜 E,
      HasFPowerSeriesOnBall f p' x r') :
    HasFPowerSeriesOnBall f p x ∞ :=
  { r_le := ENNReal.le_of_forall_pos_nnreal_lt fun r hr _ =>
      let ⟨_, hp'⟩ := h' r hr
      (h.exchange_radius hp').r_le
    r_pos := ENNReal.coe_lt_top
    hasSum := fun {y} _ =>
      let ⟨r', hr'⟩ := exists_gt ‖y‖₊
      let ⟨_, hp'⟩ := h' r' hr'.ne_bot.bot_lt
(h.exchange_radius hp').hasSum mem_eball_zero_iff.mpr (ENNReal.coe_lt_coe.2 hr') }

end Uniqueness

namespace AnalyticOnNhd

/--
theorem `eqOn_zero_of_preconnected_of_eventuallyEq_zero_aux` / 定理 `eqOn_zero_of_preconnected_of_eventuallyEq_zero_aux`

English:
theorem eqOn_zero_of_preconnected_of_eventuallyEq_zero_aux
  statement: [CompleteSpace F] {f : E -> F} {U : Set E}
  proof: by
  /- Let `u` be the set of points around which `f` vanishes. It is clearly open. We have to show
    that its limit points in `U` still belong to it, from which the inclusion `U ⊆ u` will follow
    by connectedness. -/
  let u := {x | f =ᶠ[𝓝 x] 0}
  suffices main : closure u inter U subseteq u b

中文:
定理 eqOn_zero_of_preconnected_of_eventuallyEq_zero_aux
  结论: [CompleteSpace F] {f : E -> F} {U : Set E}
  证明: by
  /- Let `u` be the set of points around which `f` vanishes. It is clearly open. We have to show
    that its limit points in `U` still belong to it, from which the inclusion `U ⊆ u` will follow
    by connectedness. -/
  let u := {x | f =ᶠ[𝓝 x] 0}
  suffices main : closure u inter U subseteq u b
-/
theorem eqOn_zero_of_preconnected_of_eventuallyEq_zero_aux [CompleteSpace F] {f : E -> F} {U : Set E}
    (hf : AnalyticOnNhd 𝕜 f U) (hU : IsPreconnected U)
    {z₀ : E} (h₀ : z₀ in U) (hfz₀ : f =ᶠ[𝓝 z₀] 0) :
    EqOn f 0 U := by
  /- Let `u` be the set of points around which `f` vanishes. It is clearly open. We have to show
    that its limit points in `U` still belong to it, from which the inclusion `U ⊆ u` will follow
    by connectedness. -/
  let u := {x | f =ᶠ[𝓝 x] 0}
  suffices main : closure u inter U subseteq u by
    have Uu : U subseteq u :=
      hU.subset_of_closure_inter_subset isOpen_setOfPred_eventually_nhds ⟨z₀, h₀, hfz₀⟩ main
    intro z hz
    simpa using mem_of_mem_nhds (Uu hz)
  /- Take a limit point `x`, then a ball `B (x, r)` on which it has a power series expansion, and
    then `y ∈ B (x, r/2) ∩ u`. Then `f` has a power series expansion on `B (y, r/2)` as it is
    contained in `B (x, r)`. All the coefficients in this series expansion vanish, as `f` is zero
    on a neighborhood of `y`. Therefore, `f` is zero on `B (y, r/2)`. As this ball contains `x`,
    it follows that `f` vanishes on a neighborhood of `x`, proving the claim. -/
  rintro x ⟨xu, xU⟩
  rcases hf x xU with ⟨p, r, hp⟩
  obtain ⟨y, yu, hxy⟩ : exists y in u, edist x y < r / 2 :=
    EMetric.mem_closure_iff.1 xu (r / 2) (ENNReal.half_pos hp.r_pos.ne')
  let q := p.changeOrigin (y - x)
  have has_series : HasFPowerSeriesOnBall f q y (r / 2) := by
    have A : (‖y - x‖₊ : Real>=0∞) < r / 2 := by rwa [edist_comm, edist_eq_enorm_sub] at hxy
    have := hp.changeOrigin (A.trans_le ENNReal.half_le_self)
    simp only [add_sub_cancel] at this
    apply this.mono (ENNReal.half_pos hp.r_pos.ne')
    apply ENNReal.le_sub_of_add_le_left ENNReal.coe_ne_top
    apply (add_le_add A.le (le_refl (r / 2))).trans (le_of_eq _)
    exact ENNReal.add_halves _
  have M : Metric.eball y (r / 2) in 𝓝 x := Metric.isOpen_eball.mem_nhds hxy
  filter_upwards [M] with z hz
  have A : HasSum (fun n : Nat => q n fun _ : Fin n => z - y) (f z) := has_series.hasSum_sub hz
  have B : HasSum (fun n : Nat => q n fun _ : Fin n => z - y) 0 := by
    have : HasFPowerSeriesAt 0 q y := has_series.hasFPowerSeriesAt.congr yu
    convert! hasSum_zero (α := F) using 1
    ext n
    exact this.apply_eq_zero n _
  exact HasSum.unique A B

/--
theorem `eqOn_zero_of_preconnected_of_eventuallyEq_zero` / 定理 `eqOn_zero_of_preconnected_of_eventuallyEq_zero`

English:
theorem eqOn_zero_of_preconnected_of_eventuallyEq_zero
  statement: {f : E -> F} {U : Set E}
  proof: by
  let F' := UniformSpace.Completion F
  set e : F ->L[𝕜] F' := UniformSpace.Completion.toComplL
  have : AnalyticOnNhd 𝕜 (e ∘ f) U := fun x hx => (e.analyticAt _).comp (hf x hx)
  have A : EqOn (e ∘ f) 0 U := by
    apply eqOn_zero_of_preconnected_of_eventuallyEq_zero_aux this hU h₀
    filter_up

中文:
定理 eqOn_zero_of_preconnected_of_eventuallyEq_zero
  结论: {f : E -> F} {U : Set E}
  证明: by
  let F' := UniformSpace.Completion F
  set e : F ->L[𝕜] F' := UniformSpace.Completion.toComplL
  have : AnalyticOnNhd 𝕜 (e ∘ f) U := fun x hx => (e.analyticAt _).comp (hf x hx)
  have A : EqOn (e ∘ f) 0 U := by
    apply eqOn_zero_of_preconnected_of_eventuallyEq_zero_aux this hU h₀
    filter_up

Depends on / 依赖: AnalyticOnNhd, Completion, Function, Function.comp_apply, Pi.zero_apply, UniformSpace, UniformSpace.Completion, UniformSpace.Completion.coe_injective, UniformSpace.Completion.toComplL, analyticAt, coe_injective, comp_apply, e.analyticAt, eqOn_zero_of_preconnected_of_eventuallyEq_zero_aux, filter_upwards, map_zero, toComplL, zero_apply
-/
theorem eqOn_zero_of_preconnected_of_eventuallyEq_zero {f : E -> F} {U : Set E}
    (hf : AnalyticOnNhd 𝕜 f U) (hU : IsPreconnected U)
    {z₀ : E} (h₀ : z₀ in U) (hfz₀ : f =ᶠ[𝓝 z₀] 0) :
    EqOn f 0 U := by
  let F' := UniformSpace.Completion F
  set e : F ->L[𝕜] F' := UniformSpace.Completion.toComplL
  have : AnalyticOnNhd 𝕜 (e ∘ f) U := fun x hx => (e.analyticAt _).comp (hf x hx)
  have A : EqOn (e ∘ f) 0 U := by
    apply eqOn_zero_of_preconnected_of_eventuallyEq_zero_aux this hU h₀
    filter_upwards [hfz₀] with x hx
    simp only [hx, Function.comp_apply, Pi.zero_apply, map_zero]
  intro z hz
  have : e (f z) = e 0 := by simpa only using! A hz
  exact UniformSpace.Completion.coe_injective F this

/--
theorem `eqOn_of_preconnected_of_eventuallyEq` / 定理 `eqOn_of_preconnected_of_eventuallyEq`

English:
theorem eqOn_of_preconnected_of_eventuallyEq
  statement: {f g : E -> F} {U : Set E} (hf : AnalyticOnNhd 𝕜 f U)
  proof: by
  have hfg' : f - g =ᶠ[𝓝 z₀] 0 := hfg.mono fun z h => by simp [h]
  simpa [sub_eq_zero] using! fun z hz =>
    (hf.sub hg).eqOn_zero_of_preconnected_of_eventuallyEq_zero hU h₀ hfg' hz

中文:
定理 eqOn_of_preconnected_of_eventuallyEq
  结论: {f g : E -> F} {U : Set E} (hf : AnalyticOnNhd 𝕜 f U)
  证明: by
  have hfg' : f - g =ᶠ[𝓝 z₀] 0 := hfg.mono fun z h => by simp [h]
  simpa [sub_eq_zero] using! fun z hz =>
    (hf.sub hg).eqOn_zero_of_preconnected_of_eventuallyEq_zero hU h₀ hfg' hz

Depends on / 依赖: eqOn_zero_of_preconnected_of_eventuallyEq_zero, hf.sub, hfg.mono, sub_eq_zero
-/
theorem eqOn_of_preconnected_of_eventuallyEq {f g : E -> F} {U : Set E} (hf : AnalyticOnNhd 𝕜 f U)
    (hg : AnalyticOnNhd 𝕜 g U) (hU : IsPreconnected U) {z₀ : E} (h₀ : z₀ in U) (hfg : f =ᶠ[𝓝 z₀] g) :
    EqOn f g U := by
  have hfg' : f - g =ᶠ[𝓝 z₀] 0 := hfg.mono fun z h => by simp [h]
  simpa [sub_eq_zero] using! fun z hz =>
    (hf.sub hg).eqOn_zero_of_preconnected_of_eventuallyEq_zero hU h₀ hfg' hz

/--
theorem `eq_of_eventuallyEq` / 定理 `eq_of_eventuallyEq`

English:
theorem eq_of_eventuallyEq
  statement: {f g : E -> F} [PreconnectedSpace E] (hf : AnalyticOnNhd 𝕜 f univ)
  proof: funext fun x =>
    eqOn_of_preconnected_of_eventuallyEq hf hg isPreconnected_univ (mem_univ z₀) hfg (mem_univ x)

中文:
定理 eq_of_eventuallyEq
  结论: {f g : E -> F} [PreconnectedSpace E] (hf : AnalyticOnNhd 𝕜 f univ)
  证明: funext fun x =>
    eqOn_of_preconnected_of_eventuallyEq hf hg isPreconnected_univ (mem_univ z₀) hfg (mem_univ x)

Depends on / 依赖: eqOn_of_preconnected_of_eventuallyEq, isPreconnected_univ, mem_univ
-/
theorem eq_of_eventuallyEq {f g : E -> F} [PreconnectedSpace E] (hf : AnalyticOnNhd 𝕜 f univ)
    (hg : AnalyticOnNhd 𝕜 g univ) {z₀ : E} (hfg : f =ᶠ[𝓝 z₀] g) : f = g :=
  funext fun x =>
    eqOn_of_preconnected_of_eventuallyEq hf hg isPreconnected_univ (mem_univ z₀) hfg (mem_univ x)

end AnalyticOnNhd
