/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Analytic
public import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
public import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Removable singularity theorem

In this file we prove Riemann's removable singularity theorem: if `f : ℂ → E` is complex
differentiable in a punctured neighborhood of a point `c` and is bounded in a punctured neighborhood
of `c` (or, more generally, $f(z) - f(c)=o((z-c)^{-1})$), then it has a limit at `c` and the
function `update f c (limUnder (𝓝[≠] c) f)` is complex differentiable in a neighborhood of `c`.
-/

public section


open TopologicalSpace Metric Set Filter Asymptotics Function

open scoped Topology Filter NNReal Real

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace Complex E] [CompleteSpace E]

namespace Complex

/--
theorem `analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt` / 定理 `analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt`

English:
theorem analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt
  statement: {f : Complex -> E} {c : Complex}
  proof: by
  rcases (nhdsWithin_hasBasis nhds_basis_closedBall _).mem_iff.1 hd with ⟨R, hR0, hRs⟩
  lift R to Real>=0 using hR0.le
  replace hc : ContinuousOn f (closedBall c R) := by
    refine fun z hz => ContinuousAt.continuousWithinAt ?_
    rcases eq_or_ne z c with (rfl | hne)
    exacts [hc, (hRs ⟨hz,

中文:
定理 analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt
  结论: {f : 复形 -> E} {c : 复形}
  证明: by
  rcases (nhdsWithin_hasBasis nhds_basis_closedBall _).mem_iff.1 hd with ⟨R, hR0, hRs⟩
  lift R to Real>=0 using hR0.le
  replace hc : ContinuousOn f (closedBall c R) := by
    refine fun z hz => ContinuousAt.continuousWithinAt ?_
    rcases eq_or_ne z c with (rfl | hne)
    exacts [hc, (hRs ⟨hz,

Depends on / 依赖: ContinuousAt, ContinuousAt.continuousWithinAt, ContinuousOn, analyticAt, ball_subset_closedBall, closedBall, continuousAt, continuousWithinAt, countable_singleton, eq_or_ne, exacts, hR0.le, hasFPowerSeriesOnBall_of_differentiable_off_countable, mem_iff, nhdsWithin_hasBasis, nhds_basis_closedBall, replace, sdiff_subset_sdiff_left
-/
theorem analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt {f : Complex -> E} {c : Complex}
    (hd : forallᶠ z in 𝓝[!=] c, DifferentiableAt Complex f z) (hc : ContinuousAt f c) : AnalyticAt Complex f c := by
  rcases (nhdsWithin_hasBasis nhds_basis_closedBall _).mem_iff.1 hd with ⟨R, hR0, hRs⟩
  lift R to Real>=0 using hR0.le
  replace hc : ContinuousOn f (closedBall c R) := by
    refine fun z hz => ContinuousAt.continuousWithinAt ?_
    rcases eq_or_ne z c with (rfl | hne)
    exacts [hc, (hRs ⟨hz, hne⟩).continuousAt]
  exact (hasFPowerSeriesOnBall_of_differentiable_off_countable (countable_singleton c) hc
    (fun z hz => hRs (sdiff_subset_sdiff_left ball_subset_closedBall hz)) hR0).analyticAt

/--
theorem `differentiableOn_compl_singleton_and_continuousAt_iff` / 定理 `differentiableOn_compl_singleton_and_continuousAt_iff`

English:
theorem differentiableOn_compl_singleton_and_continuousAt_iff
  statement: {f : Complex -> E} {s : Set Complex} {c : Complex}
  proof: by
  refine ⟨?_, fun hd => ⟨hd.mono sdiff_subset, (hd.differentiableAt hs).continuousAt⟩⟩
  rintro ⟨hd, hc⟩ x hx
  rcases eq_or_ne x c with (rfl | hne)
  · refine (analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt
      ?_ hc).differentiableAt.differentiableWithinAt
    refine eventuall

中文:
定理 differentiableOn_compl_singleton_and_continuousAt_iff
  结论: {f : 复形 -> E} {s : 集合 复形} {c : 复形}
  证明: by
  refine ⟨?_, fun hd => ⟨hd.mono sdiff_subset, (hd.differentiableAt hs).continuousAt⟩⟩
  rintro ⟨hd, hc⟩ x hx
  rcases eq_or_ne x c with (rfl | hne)
  · refine (analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt
      ?_ hc).differentiableAt.differentiableWithinAt
    refine eventuall

Depends on / 依赖: DifferentiableWithinAt, FunLike, FunLike.module, HasFDerivWithinAt, analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt, continuousAt, differentiableAt, differentiableAt.differentiableWithinAt, differentiableWithinAt, eq_or_ne, eventually_mem_nhds_iff, eventually_nhdsWithin_iff, fast_instance, hd.differentiableAt, hd.mono, hne.nhdsWithin_sdif, inter_mem, isOpen_ne, isOpen_ne.mem_nhds, mem_nhds
-/
theorem differentiableOn_compl_singleton_and_continuousAt_iff {f : Complex -> E} {s : Set Complex} {c : Complex}
    (hs : s in 𝓝 c) :
    DifferentiableOn Complex f (s \ {c}) ∧ ContinuousAt f c ↔ DifferentiableOn Complex f s := by
  refine ⟨?_, fun hd => ⟨hd.mono sdiff_subset, (hd.differentiableAt hs).continuousAt⟩⟩
  rintro ⟨hd, hc⟩ x hx
  rcases eq_or_ne x c with (rfl | hne)
  · refine (analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt
      ?_ hc).differentiableAt.differentiableWithinAt
    refine eventually_nhdsWithin_iff.2 ((eventually_mem_nhds_iff.2 hs).mono fun z hz hzx => ?_)
    exact hd.differentiableAt (inter_mem hz (isOpen_ne.mem_nhds hzx))
  · simpa only [DifferentiableWithinAt, HasFDerivWithinAt, hne.nhdsWithin_sdiff_singleton] using
      hd x ⟨hx, hne⟩

/--
theorem `differentiableOn_dslope` / 定理 `differentiableOn_dslope`

English:
theorem differentiableOn_dslope
  given: {f : Complex -> E} {s : Set Complex} {c : Complex} (hc : s in 𝓝 c)
  proof: ⟨fun h => h.of_dslope, fun h =>
(differentiableOn_compl_singleton_and_continuousAt_iff hc).mp
      ⟨Iff.mpr (differentiableOn_dslope_of_notMem fun h => h.2 rfl) (h.mono sdiff_subset),
continuousAt_dslope_same.2 h.differentiableAt hc⟩⟩

中文:
定理 differentiableOn_dslope
  条件: {f : 复形 -> E} {s : 集合 复形} {c : 复形} (hc : s in 𝓝 c)
  证明: ⟨fun h => h.of_dslope, fun h =>
(differentiableOn_compl_singleton_and_continuousAt_iff hc).mp
      ⟨Iff.mpr (differentiableOn_dslope_of_notMem fun h => h.2 rfl) (h.mono sdiff_subset),
continuousAt_dslope_same.2 h.differentiableAt hc⟩⟩

Depends on / 依赖: FunLike, FunLike.isScalarTower, Iff.mpr, continuousAt_dslope_same, differentiableAt, differentiableOn_compl_singleton_and_continuousAt_iff, differentiableOn_dslope_of_notMem, h.differentiableAt, h.mono, h.of_dslope, isScalarTower, of_dslope, sdiff_subset
-/
theorem differentiableOn_dslope {f : Complex -> E} {s : Set Complex} {c : Complex} (hc : s in 𝓝 c) :
    DifferentiableOn Complex (dslope f c) s ↔ DifferentiableOn Complex f s :=
  ⟨fun h => h.of_dslope, fun h =>
(differentiableOn_compl_singleton_and_continuousAt_iff hc).mp
      ⟨Iff.mpr (differentiableOn_dslope_of_notMem fun h => h.2 rfl) (h.mono sdiff_subset),
continuousAt_dslope_same.2 h.differentiableAt hc⟩⟩

/--
theorem `differentiableOn_update_limUnder_of_isLittleO` / 定理 `differentiableOn_update_limUnder_of_isLittleO`

English:
theorem differentiableOn_update_limUnder_of_isLittleO
  statement: {f : Complex -> E} {s : Set Complex} {c : Complex} (hc : s in 𝓝 c)
  proof: by
  set F : Complex -> E := fun z => (z - c) • f z
  suffices DifferentiableOn Complex F (s \ {c}) ∧ ContinuousAt F c by
    rw [differentiableOn_compl_singleton_and_continuousAt_iff hc]; rw [← differentiableOn_dslope hc]; rw [dslope_sub_smul] at this
    have hc : Tendsto f (𝓝[!=] c) (𝓝 (deriv F c

中文:
定理 differentiableOn_update_limUnder_of_isLittleO
  结论: {f : 复形 -> E} {s : 集合 复形} {c : 复形} (hc : s in 𝓝 c)
  证明: by
  set F : Complex -> E := fun z => (z - c) • f z
  suffices DifferentiableOn Complex F (s \ {c}) ∧ ContinuousAt F c by
    rw [differentiableOn_compl_singleton_and_continuousAt_iff hc]; rw [← differentiableOn_dslope hc]; rw [dslope_sub_smul] at this
    have hc : Tendsto f (𝓝[!=] c) (𝓝 (deriv F c

Depends on / 依赖: ContinuousAt, DifferentiableOn, Tendsto, continuousAt, continuousAt_update_same, continuousAt_update_same.mp, continuousOn, continuousWithinAt_compl_self, differentiableOn_compl_singleton_and_continuousAt_iff, differentiableOn_dslope, differentiableOn_id, differentiableOn_id.sub_const, dslope_sub_smul, hc.limUnder_eq, ho.tendsto_inv_smul, limUnder_eq, sub_const, tendsto_inv_smul, this.continuousOn.continuousAt
-/
theorem differentiableOn_update_limUnder_of_isLittleO {f : Complex -> E} {s : Set Complex} {c : Complex} (hc : s in 𝓝 c)
    (hd : DifferentiableOn Complex f (s \ {c}))
    (ho : (fun z => f z - f c) =o[𝓝[!=] c] fun z => (z - c)⁻¹) :
    DifferentiableOn Complex (update f c (limUnder (𝓝[!=] c) f)) s := by
  set F : Complex -> E := fun z => (z - c) • f z
  suffices DifferentiableOn Complex F (s \ {c}) ∧ ContinuousAt F c by
    rw [differentiableOn_compl_singleton_and_continuousAt_iff hc]; rw [← differentiableOn_dslope hc]; rw [dslope_sub_smul] at this
    have hc : Tendsto f (𝓝[!=] c) (𝓝 (deriv F c)) :=
      continuousAt_update_same.mp (this.continuousOn.continuousAt hc)
    rwa [hc.limUnder_eq]
  refine ⟨(differentiableOn_id.sub_const _).smul hd, ?_⟩
  rw [← continuousWithinAt_compl_self]
  have H := ho.tendsto_inv_smul_nhds_zero
  have H' : Tendsto (fun z => (z - c) • f c) (𝓝[!=] c) (𝓝 (F c)) :=
    (continuousWithinAt_id.tendsto.sub tendsto_const_nhds).smul tendsto_const_nhds
  simpa [← smul_add, ContinuousWithinAt] using H.add H'

/--
theorem `differentiableOn_update_limUnder_insert_of_isLittleO` / 定理 `differentiableOn_update_limUnder_insert_of_isLittleO`

English:
theorem differentiableOn_update_limUnder_insert_of_isLittleO
  statement: {f : Complex -> E} {s : Set Complex} {c : Complex}
  proof: differentiableOn_update_limUnder_of_isLittleO (insert_mem_nhds_iff.2 hc)
    (hd.mono fun _ hz => hz.1.resolve_left hz.2) ho

中文:
定理 differentiableOn_update_limUnder_insert_of_isLittleO
  结论: {f : 复形 -> E} {s : 集合 复形} {c : 复形}
  证明: differentiableOn_update_limUnder_of_isLittleO (insert_mem_nhds_iff.2 hc)
    (hd.mono fun _ hz => hz.1.resolve_left hz.2) ho

Depends on / 依赖: differentiableOn_update_limUnder_of_isLittleO, hd.mono, insert_mem_nhds_iff, resolve_left
-/
theorem differentiableOn_update_limUnder_insert_of_isLittleO {f : Complex -> E} {s : Set Complex} {c : Complex}
    (hc : s in 𝓝[!=] c) (hd : DifferentiableOn Complex f s)
    (ho : (fun z => f z - f c) =o[𝓝[!=] c] fun z => (z - c)⁻¹) :
    DifferentiableOn Complex (update f c (limUnder (𝓝[!=] c) f)) (insert c s) :=
  differentiableOn_update_limUnder_of_isLittleO (insert_mem_nhds_iff.2 hc)
    (hd.mono fun _ hz => hz.1.resolve_left hz.2) ho

/--
theorem `differentiableOn_update_limUnder_of_bddAbove` / 定理 `differentiableOn_update_limUnder_of_bddAbove`

English:
theorem differentiableOn_update_limUnder_of_bddAbove
  statement: {f : Complex -> E} {s : Set Complex} {c : Complex} (hc : s in 𝓝 c)
  proof: differentiableOn_update_limUnder_of_isLittleO hc hd IsBoundedUnder.isLittleO_sub_self_inv
    let ⟨C, hC⟩ := hb
⟨C + ‖f c‖, eventually_map.2 mem_nhdsWithin_iff_exists_mem_nhds_inter.2
      ⟨s, hc, fun _ hz => norm_sub_le_of_le (hC <| mem_image_of_mem _ hz) le_rfl⟩⟩

中文:
定理 differentiableOn_update_limUnder_of_bddAbove
  结论: {f : 复形 -> E} {s : 集合 复形} {c : 复形} (hc : s in 𝓝 c)
  证明: differentiableOn_update_limUnder_of_isLittleO hc hd IsBoundedUnder.isLittleO_sub_self_inv
    let ⟨C, hC⟩ := hb
⟨C + ‖f c‖, eventually_map.2 mem_nhdsWithin_iff_exists_mem_nhds_inter.2
      ⟨s, hc, fun _ hz => norm_sub_le_of_le (hC <| mem_image_of_mem _ hz) le_rfl⟩⟩

Depends on / 依赖: IsBoundedUnder, IsBoundedUnder.isLittleO_sub_self_inv, differentiableOn_update_limUnder_of_isLittleO, eventually_map, isLittleO_sub_self_inv, le_rfl, mem_image_of_mem, mem_nhdsWithin_iff_exists_mem_nhds_inter, norm_sub_le_of_le
-/
theorem differentiableOn_update_limUnder_of_bddAbove {f : Complex -> E} {s : Set Complex} {c : Complex} (hc : s in 𝓝 c)
    (hd : DifferentiableOn Complex f (s \ {c})) (hb : BddAbove (norm ∘ f '' (s \ {c}))) :
    DifferentiableOn Complex (update f c (limUnder (𝓝[!=] c) f)) s :=
differentiableOn_update_limUnder_of_isLittleO hc hd IsBoundedUnder.isLittleO_sub_self_inv
    let ⟨C, hC⟩ := hb
⟨C + ‖f c‖, eventually_map.2 mem_nhdsWithin_iff_exists_mem_nhds_inter.2
      ⟨s, hc, fun _ hz => norm_sub_le_of_le (hC <| mem_image_of_mem _ hz) le_rfl⟩⟩

/--
theorem `tendsto_limUnder_of_differentiable_on_punctured_nhds_of_isLittleO` / 定理 `tendsto_limUnder_of_differentiable_on_punctured_nhds_of_isLittleO`

English:
theorem tendsto_limUnder_of_differentiable_on_punctured_nhds_of_isLittleO
  statement: {f : Complex -> E} {c : Complex}
  proof: by
  rw [eventually_nhdsWithin_iff] at hd
  have : DifferentiableOn Complex f ({z | z != c -> DifferentiableAt Complex f z} \ {c}) := fun z hz =>
    (hz.1 hz.2).differentiableWithinAt
  have H := differentiableOn_update_limUnder_of_isLittleO hd this ho
  exact continuousAt_update_same.1 (H.differen

中文:
定理 tendsto_limUnder_of_differentiable_on_punctured_nhds_of_isLittleO
  结论: {f : 复形 -> E} {c : 复形}
  证明: by
  rw [eventually_nhdsWithin_iff] at hd
  have : DifferentiableOn Complex f ({z | z != c -> DifferentiableAt Complex f z} \ {c}) := fun z hz =>
    (hz.1 hz.2).differentiableWithinAt
  have H := differentiableOn_update_limUnder_of_isLittleO hd this ho
  exact continuousAt_update_same.1 (H.differen

Depends on / 依赖: DifferentiableAt, DifferentiableOn, H.differentiableAt, continuousAt, continuousAt_update_same, differentiableAt, differentiableOn_update_limUnder_of_isLittleO, differentiableWithinAt, eventually_nhdsWithin_iff
-/
theorem tendsto_limUnder_of_differentiable_on_punctured_nhds_of_isLittleO {f : Complex -> E} {c : Complex}
    (hd : forallᶠ z in 𝓝[!=] c, DifferentiableAt Complex f z)
    (ho : (fun z => f z - f c) =o[𝓝[!=] c] fun z => (z - c)⁻¹) :
    Tendsto f (𝓝[!=] c) (𝓝 <| limUnder (𝓝[!=] c) f) := by
  rw [eventually_nhdsWithin_iff] at hd
  have : DifferentiableOn Complex f ({z | z != c -> DifferentiableAt Complex f z} \ {c}) := fun z hz =>
    (hz.1 hz.2).differentiableWithinAt
  have H := differentiableOn_update_limUnder_of_isLittleO hd this ho
  exact continuousAt_update_same.1 (H.differentiableAt hd).continuousAt

/--
theorem `tendsto_limUnder_of_differentiable_on_punctured_nhds_of_bounded_under` / 定理 `tendsto_limUnder_of_differentiable_on_punctured_nhds_of_bounded_under`

English:
theorem tendsto_limUnder_of_differentiable_on_punctured_nhds_of_bounded_under
  statement: {f : Complex -> E} {c : Complex}
  proof: tendsto_limUnder_of_differentiable_on_punctured_nhds_of_isLittleO hd hb.isLittleO_sub_self_inv

中文:
定理 tendsto_limUnder_of_differentiable_on_punctured_nhds_of_bounded_under
  结论: {f : 复形 -> E} {c : 复形}
  证明: tendsto_limUnder_of_differentiable_on_punctured_nhds_of_isLittleO hd hb.isLittleO_sub_self_inv

Depends on / 依赖: hb.isLittleO_sub_self_inv, isLittleO_sub_self_inv, tendsto_limUnder_of_differentiable_on_punctured_nhds_of_isLittleO
-/
theorem tendsto_limUnder_of_differentiable_on_punctured_nhds_of_bounded_under {f : Complex -> E} {c : Complex}
    (hd : forallᶠ z in 𝓝[!=] c, DifferentiableAt Complex f z)
    (hb : IsBoundedUnder (· <= ·) (𝓝[!=] c) fun z => ‖f z - f c‖) :
    Tendsto f (𝓝[!=] c) (𝓝 <| limUnder (𝓝[!=] c) f) :=
  tendsto_limUnder_of_differentiable_on_punctured_nhds_of_isLittleO hd hb.isLittleO_sub_self_inv

/--
theorem `two_pi_I_inv_smul_circleIntegral_sub_sq_inv_smul_of_differentiable` / 定理 `two_pi_I_inv_smul_circleIntegral_sub_sq_inv_smul_of_differentiable`

English:
theorem two_pi_I_inv_smul_circleIntegral_sub_sq_inv_smul_of_differentiable
  statement: {U : Set Complex}
  proof: by
  -- We apply the removable singularity theorem and the Cauchy formula to `dslope f w₀`
  have hf' : DifferentiableOn Complex (dslope f w₀) U :=
    (differentiableOn_dslope (hU.mem_nhds ((ball_subset_closedBall.trans hc) hw₀))).mpr hf
  have h0 := (hf'.diffContOnCl_ball hc).two_pi_i_inv_smul_cir

中文:
定理 two_pi_I_inv_smul_circle整数egral_sub_sq_inv_smul_of_differentiable
  结论: {U : 集合 复形}
  证明: by
  -- We apply the removable singularity theorem and the Cauchy formula to `dslope f w₀`
  have hf' : DifferentiableOn Complex (dslope f w₀) U :=
    (differentiableOn_dslope (hU.mem_nhds ((ball_subset_closedBall.trans hc) hw₀))).mpr hf
  have h0 := (hf'.diffContOnCl_ball hc).two_pi_i_inv_smul_cir
-/
theorem two_pi_I_inv_smul_circleIntegral_sub_sq_inv_smul_of_differentiable {U : Set Complex}
    (hU : IsOpen U) {c w₀ : Complex} {R : Real} {f : Complex -> E} (hc : closedBall c R subseteq U)
    (hf : DifferentiableOn Complex f U) (hw₀ : w₀ in ball c R) :
    ((2 * π * I : Complex)⁻¹ • ∮ z in C(c, R), ((z - w₀) ^ 2)⁻¹ • f z) = deriv f w₀ := by
  -- We apply the removable singularity theorem and the Cauchy formula to `dslope f w₀`
  have hf' : DifferentiableOn Complex (dslope f w₀) U :=
    (differentiableOn_dslope (hU.mem_nhds ((ball_subset_closedBall.trans hc) hw₀))).mpr hf
  have h0 := (hf'.diffContOnCl_ball hc).two_pi_i_inv_smul_circleIntegral_sub_inv_smul hw₀
  rw [← dslope_same]; rw [← h0]
  congr 1
  trans ∮ z in C(c, R), ((z - w₀) ^ 2)⁻¹ • (f z - f w₀)
  · have h1 : ContinuousOn (fun z : Complex => ((z - w₀) ^ 2)⁻¹) (sphere c R) := by
      refine ((continuous_id'.sub continuous_const).pow 2).continuousOn.inv₀ fun w hw h => ?_
      exact sphere_disjoint_ball.ne_of_mem hw hw₀ (sub_eq_zero.mp (sq_eq_zero_iff.mp h))
    have h2 : CircleIntegrable (fun z : Complex => ((z - w₀) ^ 2)⁻¹ • f z) c R := by
      refine ContinuousOn.circleIntegrable (pos_of_mem_ball hw₀).le ?_
      exact h1.smul (hf.continuousOn.mono (sphere_subset_closedBall.trans hc))
    have h3 : CircleIntegrable (fun z : Complex => ((z - w₀) ^ 2)⁻¹ • f w₀) c R :=
      ContinuousOn.circleIntegrable (pos_of_mem_ball hw₀).le (h1.smul continuousOn_const)
    have h4 : (∮ z : Complex in C(c, R), ((z - w₀) ^ 2)⁻¹) = 0 := by
      simpa using! circleIntegral.integral_sub_zpow_of_ne (by decide : (-2 : Int) != -1) c w₀ R
    simp only [smul_sub, circleIntegral.integral_sub h2 h3, h4, circleIntegral.integral_smul_const,
      zero_smul, sub_zero]
  · refine circleIntegral.integral_congr (pos_of_mem_ball hw₀).le fun z hz => ?_
    simp only [dslope_of_ne, Metric.sphere_disjoint_ball.ne_of_mem hz hw₀, slope, ← smul_assoc, sq,
      mul_inv, Ne, not_false_iff, vsub_eq_sub, smul_eq_mul]

end Complex
