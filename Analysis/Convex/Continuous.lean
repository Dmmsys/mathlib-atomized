/-
Copyright (c) 2023 Yaël Dillies, Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Zichen Wang
-/
module

public import Mathlib.Analysis.Normed.Affine.Convex

/-!
# Convex functions are continuous

This file proves that a convex function from a finite-dimensional real normed space to `ℝ` is
continuous.
-/

public section

open FiniteDimensional Metric Set List Bornology
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  {C : Set E} {f : E -> Real} {x₀ : E} {ε r r' M : Real}

/--
lemma `ConvexOn.lipschitzOnWith_of_abs_le` / 引理 `ConvexOn.lipschitzOnWith_of_abs_le`

English:
lemma ConvexOn.lipschitzOnWith_of_abs_le
  statement: (hf : ConvexOn Real (ball x₀ r) f) (hε : 0 < ε)
  proof: by
  set K := 2 * M / ε with hK
  have oneside {x y : E} (hx : x in ball x₀ (r - ε)) (hy : y in ball x₀ (r - ε)) :
      f x - f y <= K * ‖x - y‖ := by
    obtain rfl | hxy := eq_or_ne x y
    · simp
have hx₀r : ball x₀ (r - ε) subseteq ball x₀ r := ball_subset_ball by linarith
    have hx' : x in b

中文:
引理 ConvexOn.lipschitzOnWith_of_abs_le
  结论: (hf : ConvexOn 实数 (ball x₀ r) f) (hε : 0 < ε)
  证明: by
  set K := 2 * M / ε with hK
  have oneside {x y : E} (hx : x in ball x₀ (r - ε)) (hy : y in ball x₀ (r - ε)) :
      f x - f y <= K * ‖x - y‖ := by
    obtain rfl | hxy := eq_or_ne x y
    · simp
have hx₀r : ball x₀ (r - ε) subseteq ball x₀ r := ball_subset_ball by linarith
    have hx' : x in b

Depends on / 依赖: ball_subset_ball, eq_or_ne, mem_ball_iff_norm, norm_sub_pos_iff, oneside, replace, subseteq
-/
lemma ConvexOn.lipschitzOnWith_of_abs_le (hf : ConvexOn Real (ball x₀ r) f) (hε : 0 < ε)
    (hM : forall a, dist a x₀ < r -> |f a| <= M) :
    LipschitzOnWith (2 * M / ε).toNNReal f (ball x₀ (r - ε)) := by
  set K := 2 * M / ε with hK
  have oneside {x y : E} (hx : x in ball x₀ (r - ε)) (hy : y in ball x₀ (r - ε)) :
      f x - f y <= K * ‖x - y‖ := by
    obtain rfl | hxy := eq_or_ne x y
    · simp
have hx₀r : ball x₀ (r - ε) subseteq ball x₀ r := ball_subset_ball by linarith
    have hx' : x in ball x₀ r := hx₀r hx
    have hy' : y in ball x₀ r := hx₀r hy
    let z := x + (ε / ‖x - y‖) • (x - y)
    replace hxy : 0 < ‖x - y‖ := by rwa [norm_sub_pos_iff]
have hz : z in ball x₀ r := mem_ball_iff_norm.2 by
      calc
        _ = ‖(x - x₀) + (ε / ‖x - y‖) • (x - y)‖ := by simp only [z, add_sub_right_comm]
        _ <= ‖x - x₀‖ + ‖(ε / ‖x - y‖) • (x - y)‖ := norm_add_le ..
        _ < r - ε + ε :=
add_lt_add_of_lt_of_le (mem_ball_iff_norm.1 hx) by
            simp [norm_smul, abs_of_nonneg, hε.le, hxy.ne']
        _ = r := by simp
    let a := ε / (ε + ‖x - y‖)
    let b := ‖x - y‖ / (ε + ‖x - y‖)
    have hab : a + b = 1 := by simp [field, a, b]
    have hxyz : x = a • y + b • z := by
      calc
        x = a • x + b • x := by rw [Convex.combo_self hab]
        _ = a • y + b • z := by simp [z, a, b, smul_smul, hxy.ne', smul_sub]; abel
    rw [hK]; rw [mul_comm]; rw [← mul_div_assoc]; rw [le_div_iff₀' hε]
    calc
      ε * (f x - f y) <= ‖x - y‖ * (f z - f x) := by
        have h := hf.2 hy' hz (by positivity) (by positivity) hab
        simp only [← hxyz, smul_eq_mul, a, b] at h
        field_simp at h
        linear_combination h
      _ <= _ := by
        rw [sub_eq_add_neg (f _)]; rw [two_mul]
        gcongr
· exact (le_abs_self _).trans hM _ hz
· exact (neg_le_abs _).trans hM _ hx'
  refine .of_dist_le' fun x hx y hy => ?_
  simp_rw [dist_eq_norm_sub, Real.norm_eq_abs, abs_sub_le_iff]
  exact ⟨oneside hx hy, norm_sub_rev x _ ▸ oneside hy hx⟩

/--
lemma `ConcaveOn.lipschitzOnWith_of_abs_le` / 引理 `ConcaveOn.lipschitzOnWith_of_abs_le`

English:
lemma ConcaveOn.lipschitzOnWith_of_abs_le
  statement: (hf : ConcaveOn Real (ball x₀ r) f) (hε : 0 < ε)
  proof: by
simpa using hf.neg.lipschitzOnWith_of_abs_le hε by simpa using hM

中文:
引理 ConcaveOn.lipschitzOnWith_of_abs_le
  结论: (hf : ConcaveOn 实数 (ball x₀ r) f) (hε : 0 < ε)
  证明: by
simpa using hf.neg.lipschitzOnWith_of_abs_le hε by simpa using hM

Depends on / 依赖: hf.neg.lipschitzOnWith_of_abs_le, lipschitzOnWith_of_abs_le
-/
lemma ConcaveOn.lipschitzOnWith_of_abs_le (hf : ConcaveOn Real (ball x₀ r) f) (hε : 0 < ε)
    (hM : forall a, dist a x₀ < r -> |f a| <= M) :
    LipschitzOnWith (2 * M / ε).toNNReal f (ball x₀ (r - ε)) := by
simpa using hf.neg.lipschitzOnWith_of_abs_le hε by simpa using hM

/--
lemma `ConvexOn.exists_lipschitzOnWith_of_isBounded` / 引理 `ConvexOn.exists_lipschitzOnWith_of_isBounded`

English:
lemma ConvexOn.exists_lipschitzOnWith_of_isBounded
  statement: (hf : ConvexOn Real (ball x₀ r) f) (hr : r' < r)
  proof: by
  rw [isBounded_iff_subset_ball 0] at hf'
  simp only [Set.subset_def, mem_image, mem_ball, dist_zero_right, Real.norm_eq_abs,
    forall_exists_index, and_imp, forall_apply_eq_imp_iff₂] at hf'
  obtain ⟨M, hM⟩ := hf'
  rw [← sub_sub_cancel r r']
  exact ⟨_, hf.lipschitzOnWith_of_abs_le (sub_pos.

中文:
引理 ConvexOn.存在_lipschitzOnWith_of_isBounded
  结论: (hf : ConvexOn 实数 (ball x₀ r) f) (hr : r' < r)
  证明: by
  rw [isBounded_iff_subset_ball 0] at hf'
  simp only [Set.subset_def, mem_image, mem_ball, dist_zero_right, Real.norm_eq_abs,
    forall_exists_index, and_imp, forall_apply_eq_imp_iff₂] at hf'
  obtain ⟨M, hM⟩ := hf'
  rw [← sub_sub_cancel r r']
  exact ⟨_, hf.lipschitzOnWith_of_abs_le (sub_pos.

Depends on / 依赖: Real.norm_eq_abs, Set.subset_def, and_imp, dist_zero_right, forall_exists_index, hf.lipschitzOnWith_of_abs_le, isBounded_iff_subset_ball, lipschitzOnWith_of_abs_le, mem_ball, mem_image, norm_eq_abs, sub_pos, sub_sub_cancel, subset_def
-/
lemma ConvexOn.exists_lipschitzOnWith_of_isBounded (hf : ConvexOn Real (ball x₀ r) f) (hr : r' < r)
    (hf' : IsBounded (f '' ball x₀ r)) : exists K, LipschitzOnWith K f (ball x₀ r') := by
  rw [isBounded_iff_subset_ball 0] at hf'
  simp only [Set.subset_def, mem_image, mem_ball, dist_zero_right, Real.norm_eq_abs,
    forall_exists_index, and_imp, forall_apply_eq_imp_iff₂] at hf'
  obtain ⟨M, hM⟩ := hf'
  rw [← sub_sub_cancel r r']
  exact ⟨_, hf.lipschitzOnWith_of_abs_le (sub_pos.2 hr) fun a ha => (hM a ha).le⟩

/--
lemma `ConcaveOn.exists_lipschitzOnWith_of_isBounded` / 引理 `ConcaveOn.exists_lipschitzOnWith_of_isBounded`

English:
lemma ConcaveOn.exists_lipschitzOnWith_of_isBounded
  statement: (hf : ConcaveOn Real (ball x₀ r) f) (hr : r' < r)
  proof: by
  replace hf' : IsBounded ((-f) '' ball x₀ r) := by convert! hf'.neg; ext; simp [neg_eq_iff_eq_neg]
  simpa using hf.neg.exists_lipschitzOnWith_of_isBounded hr hf'

中文:
引理 ConcaveOn.存在_lipschitzOnWith_of_isBounded
  结论: (hf : ConcaveOn 实数 (ball x₀ r) f) (hr : r' < r)
  证明: by
  replace hf' : IsBounded ((-f) '' ball x₀ r) := by convert! hf'.neg; ext; simp [neg_eq_iff_eq_neg]
  simpa using hf.neg.exists_lipschitzOnWith_of_isBounded hr hf'

Depends on / 依赖: IsBounded, convert, exists_lipschitzOnWith_of_isBounded, hf.neg.exists_lipschitzOnWith_of_isBounded, neg_eq_iff_eq_neg, replace
-/
lemma ConcaveOn.exists_lipschitzOnWith_of_isBounded (hf : ConcaveOn Real (ball x₀ r) f) (hr : r' < r)
    (hf' : IsBounded (f '' ball x₀ r)) : exists K, LipschitzOnWith K f (ball x₀ r') := by
  replace hf' : IsBounded ((-f) '' ball x₀ r) := by convert! hf'.neg; ext; simp [neg_eq_iff_eq_neg]
  simpa using hf.neg.exists_lipschitzOnWith_of_isBounded hr hf'

/--
lemma `ConvexOn.isBoundedUnder_abs` / 引理 `ConvexOn.isBoundedUnder_abs`

English:
lemma ConvexOn.isBoundedUnder_abs
  given: (hf : ConvexOn Real C f) {x₀ : E} (hC : C in 𝓝 x₀)
  proof: by
refine ⟨fun h => h.mono_le .of_forall fun x => le_abs_self _, ?_⟩
  rintro ⟨r, hr⟩
  refine ⟨|r| + 2 * |f x₀|, ?_⟩
  have : (𝓝 x₀).Tendsto (fun y => 2 • x₀ - y) (𝓝 x₀) :=
    tendsto_nhds_nhds.2 (⟨·, ·, by simp [two_nsmul, dist_comm]⟩)
  simp only [Filter.eventually_map, Pi.abs_apply, abs_le'] at

中文:
引理 ConvexOn.isBoundedUnder_abs
  条件: (hf : ConvexOn 实数 C f) {x₀ : E} (hC : C in 𝓝 x₀)
  证明: by
refine ⟨fun h => h.mono_le .of_forall fun x => le_abs_self _, ?_⟩
  rintro ⟨r, hr⟩
  refine ⟨|r| + 2 * |f x₀|, ?_⟩
  have : (𝓝 x₀).Tendsto (fun y => 2 • x₀ - y) (𝓝 x₀) :=
    tendsto_nhds_nhds.2 (⟨·, ·, by simp [two_nsmul, dist_comm]⟩)
  simp only [Filter.eventually_map, Pi.abs_apply, abs_le'] at

Depends on / 依赖: Filter, Filter.eventually_map, Pi.abs_apply, Tendsto, abs_apply, abs_le, dist_comm, eventually, eventually_map, eventually_mem, filter_upwards, h.mono_le, hfr.trans, le_abs_self, mono_le, neg_sub_comm, of_forall, sub_le_iff_le, sub_le_iff_le_add, tendsto_nhds_nhds
-/
lemma ConvexOn.isBoundedUnder_abs (hf : ConvexOn Real C f) {x₀ : E} (hC : C in 𝓝 x₀) :
    (𝓝 x₀).IsBoundedUnder (· <= ·) |f| ↔ (𝓝 x₀).IsBoundedUnder (· <= ·) f := by
refine ⟨fun h => h.mono_le .of_forall fun x => le_abs_self _, ?_⟩
  rintro ⟨r, hr⟩
  refine ⟨|r| + 2 * |f x₀|, ?_⟩
  have : (𝓝 x₀).Tendsto (fun y => 2 • x₀ - y) (𝓝 x₀) :=
    tendsto_nhds_nhds.2 (⟨·, ·, by simp [two_nsmul, dist_comm]⟩)
  simp only [Filter.eventually_map, Pi.abs_apply, abs_le'] at hr ⊢
  filter_upwards [this.eventually_mem hC, hC, hr, this.eventually hr] with y hx hx' hfr hfr'
refine ⟨hfr.trans (le_abs_self _).trans by simp, ?_⟩
  rw [← sub_le_iff_le_add]; rw [neg_sub_comm]; rw [sub_le_iff_le_add']; rw [← abs_two]; rw [← abs_mul]
  calc
    -|2 * f x₀| <= 2 * f x₀ := neg_abs_le _
    _ <= f y + f (2 • x₀ - y) := by
      have := hf.2 hx' hx (by positivity) (by positivity) (add_halves _)
      simp only [one_div, ← Nat.cast_smul_eq_nsmul Real, Nat.cast_ofNat, smul_sub, ne_eq,
        OfNat.ofNat_ne_zero, not_false_eq_true, inv_smul_smul₀, add_sub_cancel, smul_eq_mul] at this
      cancel_denoms at this
      rwa [← Nat.cast_two, Nat.cast_smul_eq_nsmul] at this
    _ <= f y + |r| := by gcongr; exact hfr'.trans (le_abs_self _)

/--
lemma `ConcaveOn.isBoundedUnder_abs` / 引理 `ConcaveOn.isBoundedUnder_abs`

English:
lemma ConcaveOn.isBoundedUnder_abs
  given: (hf : ConcaveOn Real C f) {x₀ : E} (hC : C in 𝓝 x₀)
  proof: by
  simpa [Pi.neg_def, Pi.abs_def] using hf.neg.isBoundedUnder_abs hC

中文:
引理 ConcaveOn.isBoundedUnder_abs
  条件: (hf : ConcaveOn 实数 C f) {x₀ : E} (hC : C in 𝓝 x₀)
  证明: by
  simpa [Pi.neg_def, Pi.abs_def] using hf.neg.isBoundedUnder_abs hC

Depends on / 依赖: Pi.abs_def, Pi.neg_def, abs_def, hf.neg.isBoundedUnder_abs, isBoundedUnder_abs, neg_def
-/
lemma ConcaveOn.isBoundedUnder_abs (hf : ConcaveOn Real C f) {x₀ : E} (hC : C in 𝓝 x₀) :
    (𝓝 x₀).IsBoundedUnder (· <= ·) |f| ↔ (𝓝 x₀).IsBoundedUnder (· >= ·) f := by
  simpa [Pi.neg_def, Pi.abs_def] using hf.neg.isBoundedUnder_abs hC

/--
lemma `ConvexOn.continuousOn_tfae` / 引理 `ConvexOn.continuousOn_tfae`

English:
lemma ConvexOn.continuousOn_tfae
  given: (hC : IsOpen C) (hC' : C.Nonempty) (hf : ConvexOn Real C f)
  statement: TFAE [
  proof: by
  tfae_have 1 -> 2 := LocallyLipschitzOn.continuousOn
  tfae_have 2 -> 3 := by
    obtain ⟨x₀, hx₀⟩ := hC'
exact fun h => ⟨x₀, hx₀, h.continuousAt hC.mem_nhds hx₀⟩
  tfae_have 3 -> 4
  | ⟨x₀, hx₀, h⟩ =>
    ⟨x₀, hx₀, f x₀ + 1, by simpa using! h.eventually (eventually_le_nhds (by simp))⟩
  tfae_ha

中文:
引理 ConvexOn.continuousOn_tfae
  条件: (hC : 是开集 C) (hC' : C.非空) (hf : ConvexOn 实数 C f)
  结论: TFAE [
  证明: by
  tfae_have 1 -> 2 := LocallyLipschitzOn.continuousOn
  tfae_have 2 -> 3 := by
    obtain ⟨x₀, hx₀⟩ := hC'
exact fun h => ⟨x₀, hx₀, h.continuousAt hC.mem_nhds hx₀⟩
  tfae_have 3 -> 4
  | ⟨x₀, hx₀, h⟩ =>
    ⟨x₀, hx₀, f x₀ + 1, by simpa using! h.eventually (eventually_le_nhds (by simp))⟩
  tfae_ha

Depends on / 依赖: ContinuousAt, LocallyLipschitzOn, LocallyLipschitzOn.continuousOn, continuousAt, continuousOn, eventually, eventually_le_nhds, fun_prop, h.continuousAt, h.eventually, hC.mem_nhds, mem_nhds, tfae_have
-/
lemma ConvexOn.continuousOn_tfae (hC : IsOpen C) (hC' : C.Nonempty) (hf : ConvexOn Real C f) : TFAE [
    LocallyLipschitzOn C f,
    ContinuousOn f C,
    exists x₀ in C, ContinuousAt f x₀,
    exists x₀ in C, (𝓝 x₀).IsBoundedUnder (· <= ·) f,
    forall ⦃x₀⦄, x₀ in C -> (𝓝 x₀).IsBoundedUnder (· <= ·) f,
    forall ⦃x₀⦄, x₀ in C -> (𝓝 x₀).IsBoundedUnder (· <= ·) |f|] := by
  tfae_have 1 -> 2 := LocallyLipschitzOn.continuousOn
  tfae_have 2 -> 3 := by
    obtain ⟨x₀, hx₀⟩ := hC'
exact fun h => ⟨x₀, hx₀, h.continuousAt hC.mem_nhds hx₀⟩
  tfae_have 3 -> 4
  | ⟨x₀, hx₀, h⟩ =>
    ⟨x₀, hx₀, f x₀ + 1, by simpa using! h.eventually (eventually_le_nhds (by simp))⟩
  tfae_have 4 -> 5
  | ⟨x₀, hx₀, r, hr⟩, x, hx => by
    have : forallᶠ δ in 𝓝 (0 : Real), (1 - δ)⁻¹ • x - (δ / (1 - δ)) • x₀ in C := by
      have h : ContinuousAt (fun δ : Real => (1 - δ)⁻¹ • x - (δ / (1 - δ)) • x₀) 0 := by
        fun_prop (disch := norm_num)
      exact h (by simpa using! hC.mem_nhds hx)
    obtain ⟨δ, hδ₀, hy, hδ₁⟩ := (this.and <| eventually_lt_nhds zero_lt_one).exists_gt
    set y := (1 - δ)⁻¹ • x - (δ / (1 - δ)) • x₀
    refine ⟨max r (f y), ?_⟩
    simp only [Filter.eventually_map] at hr ⊢
obtain ⟨ε, hε, hr⟩ := Metric.eventually_nhds_iff.1 hr.and (hC.eventually_mem hx₀)
    refine Metric.eventually_nhds_iff.2 ⟨ε * δ, by positivity, fun z hz => ?_⟩
have hx₀' : δ⁻¹ • (x - y) + y = x₀ := MulAction.injective₀ (sub_ne_zero.2 hδ₁.ne') by
      simp [y, smul_sub, smul_smul, hδ₀.ne', div_eq_mul_inv, sub_ne_zero.2 hδ₁.ne', mul_left_comm,
        sub_mul, sub_smul]
    let w := δ⁻¹ • (z - y) + y
    have hwyz : δ • w + (1 - δ) • y = z := by simp [w, hδ₀.ne', sub_smul]
    have hw : dist w x₀ < ε := by
      simpa [w, ← hx₀', dist_smul₀, abs_of_nonneg, hδ₀.le, inv_mul_lt_iff₀', hδ₀]
    calc
      f z <= max (f w) (f y) :=
        hf.le_max_of_mem_segment (hr hw).2 hy ⟨_, _, hδ₀.le, sub_nonneg.2 hδ₁.le, by simp, hwyz⟩
      _ <= max r (f y) := by gcongr; exact (hr hw).1
  tfae_have 6 ↔ 5 := forall₂_congr fun x₀ hx₀ => hf.isBoundedUnder_abs (hC.mem_nhds hx₀)
  tfae_have 6 -> 1
  | h, x, hx => by
    obtain ⟨r, hr⟩ := h hx
obtain ⟨ε, hε, hεD⟩ := Metric.mem_nhds_iff.1 Filter.inter_mem (hC.mem_nhds hx) hr
    simp only [preimage_ofPred_eq, Pi.abs_apply, subset_inter_iff, hC.nhdsWithin_eq hx] at hεD ⊢
    obtain ⟨K, hK⟩ := exists_lipschitzOnWith_of_isBounded (hf.subset hεD.1 (convex_ball ..))
(half_lt_self hε) isBounded_iff_forall_norm_le.2 ⟨r, by simpa using! hεD.2⟩
    exact ⟨K, _, ball_mem_nhds _ (by simpa), hK⟩
  tfae_finish

/--
lemma `ConcaveOn.continuousOn_tfae` / 引理 `ConcaveOn.continuousOn_tfae`

English:
lemma ConcaveOn.continuousOn_tfae
  given: (hC : IsOpen C) (hC' : C.Nonempty) (hf : ConcaveOn Real C f)
  statement: TFAE [
  proof: by
  have := hf.neg.continuousOn_tfae hC hC'
  simp only [locallyLipschitzOn_neg_iff, continuousOn_neg_iff, continuousAt_neg_iff, abs_neg]
    at this
  convert! this using 8 <;> exact (Equiv.neg Real).exists_congr (by simp)

中文:
引理 ConcaveOn.continuousOn_tfae
  条件: (hC : 是开集 C) (hC' : C.非空) (hf : ConcaveOn 实数 C f)
  结论: TFAE [
  证明: by
  have := hf.neg.continuousOn_tfae hC hC'
  simp only [locallyLipschitzOn_neg_iff, continuousOn_neg_iff, continuousAt_neg_iff, abs_neg]
    at this
  convert! this using 8 <;> exact (Equiv.neg Real).exists_congr (by simp)

Depends on / 依赖: Equiv.neg, abs_neg, continuousAt_neg_iff, continuousOn_neg_iff, continuousOn_tfae, convert, exists_congr, hf.neg.continuousOn_tfae, locallyLipschitzOn_neg_iff
-/
lemma ConcaveOn.continuousOn_tfae (hC : IsOpen C) (hC' : C.Nonempty) (hf : ConcaveOn Real C f) : TFAE [
    LocallyLipschitzOn C f,
    ContinuousOn f C,
    exists x₀ in C, ContinuousAt f x₀,
    exists x₀ in C, (𝓝 x₀).IsBoundedUnder (· >= ·) f,
    forall ⦃x₀⦄, x₀ in C -> (𝓝 x₀).IsBoundedUnder (· >= ·) f,
    forall ⦃x₀⦄, x₀ in C -> (𝓝 x₀).IsBoundedUnder (· <= ·) |f|] := by
  have := hf.neg.continuousOn_tfae hC hC'
  simp only [locallyLipschitzOn_neg_iff, continuousOn_neg_iff, continuousAt_neg_iff, abs_neg]
    at this
  convert! this using 8 <;> exact (Equiv.neg Real).exists_congr (by simp)

/--
lemma `ConvexOn.locallyLipschitzOn_iff_continuousOn` / 引理 `ConvexOn.locallyLipschitzOn_iff_continuousOn`

English:
lemma ConvexOn.locallyLipschitzOn_iff_continuousOn
  given: (hC : IsOpen C) (hf : ConvexOn Real C f)
  proof: by
  obtain rfl | hC' := C.eq_empty_or_nonempty
  · simp
  · exact (hf.continuousOn_tfae hC hC').out 0 1

中文:
引理 ConvexOn.locallyLipschitzOn_iff_continuousOn
  条件: (hC : 是开集 C) (hf : ConvexOn 实数 C f)
  证明: by
  obtain rfl | hC' := C.eq_empty_or_nonempty
  · simp
  · exact (hf.continuousOn_tfae hC hC').out 0 1

Depends on / 依赖: C.eq_empty_or_nonempty, continuousOn_tfae, eq_empty_or_nonempty, hf.continuousOn_tfae
-/
lemma ConvexOn.locallyLipschitzOn_iff_continuousOn (hC : IsOpen C) (hf : ConvexOn Real C f) :
    LocallyLipschitzOn C f ↔ ContinuousOn f C := by
  obtain rfl | hC' := C.eq_empty_or_nonempty
  · simp
  · exact (hf.continuousOn_tfae hC hC').out 0 1

/--
lemma `ConcaveOn.locallyLipschitzOn_iff_continuousOn` / 引理 `ConcaveOn.locallyLipschitzOn_iff_continuousOn`

English:
lemma ConcaveOn.locallyLipschitzOn_iff_continuousOn
  given: (hC : IsOpen C) (hf : ConcaveOn Real C f)
  proof: by
  simpa using hf.neg.locallyLipschitzOn_iff_continuousOn hC

中文:
引理 ConcaveOn.locallyLipschitzOn_iff_continuousOn
  条件: (hC : 是开集 C) (hf : ConcaveOn 实数 C f)
  证明: by
  simpa using hf.neg.locallyLipschitzOn_iff_continuousOn hC

Depends on / 依赖: hf.neg.locallyLipschitzOn_iff_continuousOn, locallyLipschitzOn_iff_continuousOn
-/
lemma ConcaveOn.locallyLipschitzOn_iff_continuousOn (hC : IsOpen C) (hf : ConcaveOn Real C f) :
    LocallyLipschitzOn C f ↔ ContinuousOn f C := by
  simpa using hf.neg.locallyLipschitzOn_iff_continuousOn hC

variable [FiniteDimensional Real E]

/--
lemma `ConvexOn.locallyLipschitzOn` / 引理 `ConvexOn.locallyLipschitzOn`

English:
lemma ConvexOn.locallyLipschitzOn
  given: (hC : IsOpen C) (hf : ConvexOn Real C f)
  proof: by
  obtain rfl | ⟨x₀, hx₀⟩ := C.eq_empty_or_nonempty
  · simp
  · obtain ⟨b, hx₀b, hbC⟩ := exists_mem_interior_convexHull_affineBasis (hC.mem_nhds hx₀)
    refine ((hf.continuousOn_tfae hC ⟨x₀, hx₀⟩).out 3 0).mp ?_
    refine ⟨x₀, hx₀, BddAbove.isBoundedUnder (IsOpen.mem_nhds isOpen_interior hx₀b) 

中文:
引理 ConvexOn.locallyLipschitzOn
  条件: (hC : 是开集 C) (hf : ConvexOn 实数 C f)
  证明: by
  obtain rfl | ⟨x₀, hx₀⟩ := C.eq_empty_or_nonempty
  · simp
  · obtain ⟨b, hx₀b, hbC⟩ := exists_mem_interior_convexHull_affineBasis (hC.mem_nhds hx₀)
    refine ((hf.continuousOn_tfae hC ⟨x₀, hx₀⟩).out 3 0).mp ?_
    refine ⟨x₀, hx₀, BddAbove.isBoundedUnder (IsOpen.mem_nhds isOpen_interior hx₀b) 
-/
protected lemma ConvexOn.locallyLipschitzOn (hC : IsOpen C) (hf : ConvexOn Real C f) :
    LocallyLipschitzOn C f := by
  obtain rfl | ⟨x₀, hx₀⟩ := C.eq_empty_or_nonempty
  · simp
  · obtain ⟨b, hx₀b, hbC⟩ := exists_mem_interior_convexHull_affineBasis (hC.mem_nhds hx₀)
    refine ((hf.continuousOn_tfae hC ⟨x₀, hx₀⟩).out 3 0).mp ?_
    refine ⟨x₀, hx₀, BddAbove.isBoundedUnder (IsOpen.mem_nhds isOpen_interior hx₀b) ?_⟩
    exact (hf.bddAbove_convexHull ((subset_convexHull ..).trans hbC)
      ((finite_range _).image _).bddAbove).mono (by gcongr; exact interior_subset)

/--
lemma `ConcaveOn.locallyLipschitzOn` / 引理 `ConcaveOn.locallyLipschitzOn`

English:
lemma ConcaveOn.locallyLipschitzOn
  given: (hC : IsOpen C) (hf : ConcaveOn Real C f)
  proof: by simpa using hf.neg.locallyLipschitzOn hC

中文:
引理 ConcaveOn.locallyLipschitzOn
  条件: (hC : 是开集 C) (hf : ConcaveOn 实数 C f)
  证明: by simpa using hf.neg.locallyLipschitzOn hC
-/
protected lemma ConcaveOn.locallyLipschitzOn (hC : IsOpen C) (hf : ConcaveOn Real C f) :
    LocallyLipschitzOn C f := by simpa using hf.neg.locallyLipschitzOn hC

/--
lemma `ConvexOn.continuousOn` / 引理 `ConvexOn.continuousOn`

English:
lemma ConvexOn.continuousOn
  given: (hC : IsOpen C) (hf : ConvexOn Real C f)
  proof: (hf.locallyLipschitzOn hC).continuousOn

中文:
引理 ConvexOn.continuousOn
  条件: (hC : 是开集 C) (hf : ConvexOn 实数 C f)
  证明: (hf.locallyLipschitzOn hC).continuousOn
-/
protected lemma ConvexOn.continuousOn (hC : IsOpen C) (hf : ConvexOn Real C f) :
    ContinuousOn f C := (hf.locallyLipschitzOn hC).continuousOn

/--
lemma `ConcaveOn.continuousOn` / 引理 `ConcaveOn.continuousOn`

English:
lemma ConcaveOn.continuousOn
  given: (hC : IsOpen C) (hf : ConcaveOn Real C f)
  proof: (hf.locallyLipschitzOn hC).continuousOn

中文:
引理 ConcaveOn.continuousOn
  条件: (hC : 是开集 C) (hf : ConcaveOn 实数 C f)
  证明: (hf.locallyLipschitzOn hC).continuousOn
-/
protected lemma ConcaveOn.continuousOn (hC : IsOpen C) (hf : ConcaveOn Real C f) :
    ContinuousOn f C := (hf.locallyLipschitzOn hC).continuousOn

/--
lemma `ConvexOn.locallyLipschitzOn_interior` / 引理 `ConvexOn.locallyLipschitzOn_interior`

English:
lemma ConvexOn.locallyLipschitzOn_interior
  given: (hf : ConvexOn Real C f)
  proof: (hf.subset interior_subset hf.1.interior).locallyLipschitzOn isOpen_interior

中文:
引理 ConvexOn.locallyLipschitzOn_interior
  条件: (hf : ConvexOn 实数 C f)
  证明: (hf.subset interior_subset hf.1.interior).locallyLipschitzOn isOpen_interior

Depends on / 依赖: hf.subset, interior, interior_subset, isOpen_interior, locallyLipschitzOn, subset
-/
lemma ConvexOn.locallyLipschitzOn_interior (hf : ConvexOn Real C f) :
    LocallyLipschitzOn (interior C) f :=
  (hf.subset interior_subset hf.1.interior).locallyLipschitzOn isOpen_interior

/--
lemma `ConcaveOn.locallyLipschitzOn_interior` / 引理 `ConcaveOn.locallyLipschitzOn_interior`

English:
lemma ConcaveOn.locallyLipschitzOn_interior
  given: (hf : ConcaveOn Real C f)
  proof: (hf.subset interior_subset hf.1.interior).locallyLipschitzOn isOpen_interior

中文:
引理 ConcaveOn.locallyLipschitzOn_interior
  条件: (hf : ConcaveOn 实数 C f)
  证明: (hf.subset interior_subset hf.1.interior).locallyLipschitzOn isOpen_interior

Depends on / 依赖: hf.subset, interior, interior_subset, isOpen_interior, locallyLipschitzOn, subset
-/
lemma ConcaveOn.locallyLipschitzOn_interior (hf : ConcaveOn Real C f) :
    LocallyLipschitzOn (interior C) f :=
  (hf.subset interior_subset hf.1.interior).locallyLipschitzOn isOpen_interior

/--
lemma `ConvexOn.continuousOn_interior` / 引理 `ConvexOn.continuousOn_interior`

English:
lemma ConvexOn.continuousOn_interior
  given: (hf : ConvexOn Real C f)
  statement: ContinuousOn f (interior C)
  proof: hf.locallyLipschitzOn_interior.continuousOn

中文:
引理 ConvexOn.continuousOn_interior
  条件: (hf : ConvexOn 实数 C f)
  结论: ContinuousOn f (interior C)
  证明: hf.locallyLipschitzOn_interior.continuousOn

Depends on / 依赖: continuousOn, hf.locallyLipschitzOn_interior.continuousOn, locallyLipschitzOn_interior
-/
lemma ConvexOn.continuousOn_interior (hf : ConvexOn Real C f) : ContinuousOn f (interior C) :=
  hf.locallyLipschitzOn_interior.continuousOn

/--
lemma `ConcaveOn.continuousOn_interior` / 引理 `ConcaveOn.continuousOn_interior`

English:
lemma ConcaveOn.continuousOn_interior
  given: (hf : ConcaveOn Real C f)
  statement: ContinuousOn f (interior C)
  proof: hf.locallyLipschitzOn_interior.continuousOn

中文:
引理 ConcaveOn.continuousOn_interior
  条件: (hf : ConcaveOn 实数 C f)
  结论: ContinuousOn f (interior C)
  证明: hf.locallyLipschitzOn_interior.continuousOn

Depends on / 依赖: continuousOn, hf.locallyLipschitzOn_interior.continuousOn, locallyLipschitzOn_interior
-/
lemma ConcaveOn.continuousOn_interior (hf : ConcaveOn Real C f) : ContinuousOn f (interior C) :=
  hf.locallyLipschitzOn_interior.continuousOn

/--
lemma `ConvexOn.locallyLipschitz` / 引理 `ConvexOn.locallyLipschitz`

English:
lemma ConvexOn.locallyLipschitz
  given: (hf : ConvexOn Real univ f)
  statement: LocallyLipschitz f
  proof: by
  simpa using hf.locallyLipschitzOn_interior

中文:
引理 ConvexOn.locallyLipschitz
  条件: (hf : ConvexOn 实数 univ f)
  结论: LocallyLipschitz f
  证明: by
  simpa using hf.locallyLipschitzOn_interior
-/
protected lemma ConvexOn.locallyLipschitz (hf : ConvexOn Real univ f) : LocallyLipschitz f := by
  simpa using hf.locallyLipschitzOn_interior

/--
lemma `ConcaveOn.locallyLipschitz` / 引理 `ConcaveOn.locallyLipschitz`

English:
lemma ConcaveOn.locallyLipschitz
  given: (hf : ConcaveOn Real univ f)
  statement: LocallyLipschitz f
  proof: by
  simpa using hf.locallyLipschitzOn_interior

中文:
引理 ConcaveOn.locallyLipschitz
  条件: (hf : ConcaveOn 实数 univ f)
  结论: LocallyLipschitz f
  证明: by
  simpa using hf.locallyLipschitzOn_interior
-/
protected lemma ConcaveOn.locallyLipschitz (hf : ConcaveOn Real univ f) : LocallyLipschitz f := by
  simpa using hf.locallyLipschitzOn_interior

-- Commented out since `intrinsicInterior` is not imported (but should be once these are proved)
-- proof_wanted ConvexOn.locallyLipschitzOn_intrinsicInterior (hf : ConvexOn ℝ C f) :
-- LocallyLipschitzOn (intrinsicInterior ℝ C) f

-- proof_wanted ConcaveOn.locallyLipschitzOn_intrinsicInterior (hf : ConcaveOn ℝ C f) :
-- LocallyLipschitzOn (intrinsicInterior ℝ C) f

-- proof_wanted ConvexOn.continuousOn_intrinsicInterior (hf : ConvexOn ℝ C f) :
-- ContinuousOn f (intrinsicInterior ℝ C)

-- proof_wanted ConcaveOn.continuousOn_intrinsicInterior (hf : ConcaveOn ℝ C f) :
-- ContinuousOn f (intrinsicInterior ℝ C)

section Intervals

/--
lemma `ConvexOn.continuousOn_Ici` / 引理 `ConvexOn.continuousOn_Ici`

English:
lemma ConvexOn.continuousOn_Ici
  statement: {f : Real -> Real} {y : Real} (hf_cvx : ConvexOn Real (Ici y) f)
  proof: by
  intro x hx
  rcases eq_or_lt_of_le (α := Real) hx with rfl | hxy
  · exact hf_cont
  · have h := hf_cvx.continuousOn_interior x
    simp only [nonempty_Iio, interior_Ici', mem_Ioi] at h
    rw [continuousWithinAt_iff_continuousAt (Ioi_mem_nhds hxy)] at h
    exact (h hxy).continuousWithinAt

中文:
引理 ConvexOn.continuousOn_Ici
  结论: {f : 实数 -> 实数} {y : 实数} (hf_cvx : ConvexOn 实数 (左闭右无界区间 y) f)
  证明: by
  intro x hx
  rcases eq_or_lt_of_le (α := Real) hx with rfl | hxy
  · exact hf_cont
  · have h := hf_cvx.continuousOn_interior x
    simp only [nonempty_Iio, interior_Ici', mem_Ioi] at h
    rw [continuousWithinAt_iff_continuousAt (Ioi_mem_nhds hxy)] at h
    exact (h hxy).continuousWithinAt

Depends on / 依赖: Ioi_mem_nhds, continuousOn_interior, continuousWithinAt, continuousWithinAt_iff_continuousAt, eq_or_lt_of_le, hf_cont, hf_cvx, hf_cvx.continuousOn_interior, interior_Ici, mem_Ioi, nonempty_Iio
-/
lemma ConvexOn.continuousOn_Ici {f : Real -> Real} {y : Real} (hf_cvx : ConvexOn Real (Ici y) f)
    (hf_cont : ContinuousWithinAt f (Ici y) y) :
    ContinuousOn f (Ici y) := by
  intro x hx
  rcases eq_or_lt_of_le (α := Real) hx with rfl | hxy
  · exact hf_cont
  · have h := hf_cvx.continuousOn_interior x
    simp only [nonempty_Iio, interior_Ici', mem_Ioi] at h
    rw [continuousWithinAt_iff_continuousAt (Ioi_mem_nhds hxy)] at h
    exact (h hxy).continuousWithinAt

/--
lemma `ConcaveOn.continuousOn_Ici` / 引理 `ConcaveOn.continuousOn_Ici`

English:
lemma ConcaveOn.continuousOn_Ici
  statement: {f : Real -> Real} {y : Real} (hf_cnv : ConcaveOn Real (Ici y) f)
  proof: by
  simpa using hf_cnv.neg.continuousOn_Ici hf_cont.neg

中文:
引理 ConcaveOn.continuousOn_Ici
  结论: {f : 实数 -> 实数} {y : 实数} (hf_cnv : ConcaveOn 实数 (左闭右无界区间 y) f)
  证明: by
  simpa using hf_cnv.neg.continuousOn_Ici hf_cont.neg

Depends on / 依赖: continuousOn_Ici, hf_cnv, hf_cnv.neg.continuousOn_Ici, hf_cont, hf_cont.neg
-/
lemma ConcaveOn.continuousOn_Ici {f : Real -> Real} {y : Real} (hf_cnv : ConcaveOn Real (Ici y) f)
    (hf_cont : ContinuousWithinAt f (Ici y) y) :
    ContinuousOn f (Ici y) := by
  simpa using hf_cnv.neg.continuousOn_Ici hf_cont.neg

/--
lemma `ConvexOn.continuousOn_Iic` / 引理 `ConvexOn.continuousOn_Iic`

English:
lemma ConvexOn.continuousOn_Iic
  statement: {f : Real -> Real} {y : Real} (hf_cvx : ConvexOn Real (Iic y) f)
  proof: by
  intro x hx
  rcases eq_or_lt_of_le (α := Real) hx with rfl | hxy
  · exact hf_cont
  · have h := hf_cvx.continuousOn_interior x
    simp only [nonempty_Ioi, interior_Iic', mem_Iio] at h
    rw [continuousWithinAt_iff_continuousAt (Iio_mem_nhds hxy)] at h
    exact (h hxy).continuousWithinAt

中文:
引理 ConvexOn.continuousOn_Iic
  结论: {f : 实数 -> 实数} {y : 实数} (hf_cvx : ConvexOn 实数 (左无界右闭区间 y) f)
  证明: by
  intro x hx
  rcases eq_or_lt_of_le (α := Real) hx with rfl | hxy
  · exact hf_cont
  · have h := hf_cvx.continuousOn_interior x
    simp only [nonempty_Ioi, interior_Iic', mem_Iio] at h
    rw [continuousWithinAt_iff_continuousAt (Iio_mem_nhds hxy)] at h
    exact (h hxy).continuousWithinAt

Depends on / 依赖: Iio_mem_nhds, continuousOn_interior, continuousWithinAt, continuousWithinAt_iff_continuousAt, eq_or_lt_of_le, hf_cont, hf_cvx, hf_cvx.continuousOn_interior, interior_Iic, mem_Iio, nonempty_Ioi
-/
lemma ConvexOn.continuousOn_Iic {f : Real -> Real} {y : Real} (hf_cvx : ConvexOn Real (Iic y) f)
    (hf_cont : ContinuousWithinAt f (Iic y) y) :
    ContinuousOn f (Iic y) := by
  intro x hx
  rcases eq_or_lt_of_le (α := Real) hx with rfl | hxy
  · exact hf_cont
  · have h := hf_cvx.continuousOn_interior x
    simp only [nonempty_Ioi, interior_Iic', mem_Iio] at h
    rw [continuousWithinAt_iff_continuousAt (Iio_mem_nhds hxy)] at h
    exact (h hxy).continuousWithinAt

/--
lemma `ConcaveOn.continuousOn_Iic` / 引理 `ConcaveOn.continuousOn_Iic`

English:
lemma ConcaveOn.continuousOn_Iic
  statement: {f : Real -> Real} {y : Real} (hf_cnv : ConcaveOn Real (Iic y) f)
  proof: by
  simpa using hf_cnv.neg.continuousOn_Iic hf_cont.neg

中文:
引理 ConcaveOn.continuousOn_Iic
  结论: {f : 实数 -> 实数} {y : 实数} (hf_cnv : ConcaveOn 实数 (左无界右闭区间 y) f)
  证明: by
  simpa using hf_cnv.neg.continuousOn_Iic hf_cont.neg

Depends on / 依赖: continuousOn_Iic, hf_cnv, hf_cnv.neg.continuousOn_Iic, hf_cont, hf_cont.neg
-/
lemma ConcaveOn.continuousOn_Iic {f : Real -> Real} {y : Real} (hf_cnv : ConcaveOn Real (Iic y) f)
    (hf_cont : ContinuousWithinAt f (Iic y) y) :
    ContinuousOn f (Iic y) := by
  simpa using hf_cnv.neg.continuousOn_Iic hf_cont.neg

/--
lemma `ConvexOn.continuousOn_Ioc` / 引理 `ConvexOn.continuousOn_Ioc`

English:
lemma ConvexOn.continuousOn_Ioc
  statement: {f : Real -> Real} {y z : Real} (hf_cvx : ConvexOn Real (Ioc y z) f)
  proof: by
  intro x hx
  rcases eq_or_lt_of_le (α := Real) hx.2 with rfl | hxz
  · rw [continuousWithinAt_Ioc_iff_Iic hx.1]
    exact hf_cont
  · have h := hf_cvx.continuousOn_interior x
    simp only [interior_Ioc, mem_Ioo, hx.1, hxz, and_self, forall_const] at h
    rw [continuousWithinAt_iff_continuousA

中文:
引理 ConvexOn.continuousOn_Ioc
  结论: {f : 实数 -> 实数} {y z : 实数} (hf_cvx : ConvexOn 实数 (左开右闭区间 y z) f)
  证明: by
  intro x hx
  rcases eq_or_lt_of_le (α := Real) hx.2 with rfl | hxz
  · rw [continuousWithinAt_Ioc_iff_Iic hx.1]
    exact hf_cont
  · have h := hf_cvx.continuousOn_interior x
    simp only [interior_Ioc, mem_Ioo, hx.1, hxz, and_self, forall_const] at h
    rw [continuousWithinAt_iff_continuousA

Depends on / 依赖: Ioo_mem_nhds, and_self, continuousOn_interior, continuousWithinAt, continuousWithinAt_Ioc_iff_Iic, continuousWithinAt_iff_continuousAt, eq_or_lt_of_le, forall_const, h.continuousWithinAt, hf_cont, hf_cvx, hf_cvx.continuousOn_interior, interior_Ioc, mem_Ioo
-/
lemma ConvexOn.continuousOn_Ioc {f : Real -> Real} {y z : Real} (hf_cvx : ConvexOn Real (Ioc y z) f)
    (hf_cont : ContinuousWithinAt f (Iic z) z) :
    ContinuousOn f (Ioc y z) := by
  intro x hx
  rcases eq_or_lt_of_le (α := Real) hx.2 with rfl | hxz
  · rw [continuousWithinAt_Ioc_iff_Iic hx.1]
    exact hf_cont
  · have h := hf_cvx.continuousOn_interior x
    simp only [interior_Ioc, mem_Ioo, hx.1, hxz, and_self, forall_const] at h
    rw [continuousWithinAt_iff_continuousAt (Ioo_mem_nhds hx.1 hxz)] at h
    exact h.continuousWithinAt

/--
lemma `ConcaveOn.continuousOn_Ioc` / 引理 `ConcaveOn.continuousOn_Ioc`

English:
lemma ConcaveOn.continuousOn_Ioc
  statement: {f : Real -> Real} {y z : Real} (hf_cnv : ConcaveOn Real (Ioc y z) f)
  proof: by
  simpa using hf_cnv.neg.continuousOn_Ioc hf_cont.neg

中文:
引理 ConcaveOn.continuousOn_Ioc
  结论: {f : 实数 -> 实数} {y z : 实数} (hf_cnv : ConcaveOn 实数 (左开右闭区间 y z) f)
  证明: by
  simpa using hf_cnv.neg.continuousOn_Ioc hf_cont.neg

Depends on / 依赖: continuousOn_Ioc, hf_cnv, hf_cnv.neg.continuousOn_Ioc, hf_cont, hf_cont.neg
-/
lemma ConcaveOn.continuousOn_Ioc {f : Real -> Real} {y z : Real} (hf_cnv : ConcaveOn Real (Ioc y z) f)
    (hf_cont : ContinuousWithinAt f (Iic z) z) :
    ContinuousOn f (Ioc y z) := by
  simpa using hf_cnv.neg.continuousOn_Ioc hf_cont.neg

/--
lemma `ConvexOn.continuousOn_Ico` / 引理 `ConvexOn.continuousOn_Ico`

English:
lemma ConvexOn.continuousOn_Ico
  statement: {f : Real -> Real} {y z : Real} (hf_cvx : ConvexOn Real (Ico y z) f)
  proof: by
  intro x hx
  rcases eq_or_lt_of_le (α := Real) hx.1 with rfl | hyx
  · rw [continuousWithinAt_Ico_iff_Ici hx.2]
    exact hf_cont
  · have h := hf_cvx.continuousOn_interior x
    simp only [interior_Ico, mem_Ioo, hyx, hx.2, and_self, forall_const] at h
    rw [continuousWithinAt_iff_continuousA

中文:
引理 ConvexOn.continuousOn_Ico
  结论: {f : 实数 -> 实数} {y z : 实数} (hf_cvx : ConvexOn 实数 (左闭右开区间 y z) f)
  证明: by
  intro x hx
  rcases eq_or_lt_of_le (α := Real) hx.1 with rfl | hyx
  · rw [continuousWithinAt_Ico_iff_Ici hx.2]
    exact hf_cont
  · have h := hf_cvx.continuousOn_interior x
    simp only [interior_Ico, mem_Ioo, hyx, hx.2, and_self, forall_const] at h
    rw [continuousWithinAt_iff_continuousA

Depends on / 依赖: Ioo_mem_nhds, and_self, continuousOn_interior, continuousWithinAt, continuousWithinAt_Ico_iff_Ici, continuousWithinAt_iff_continuousAt, eq_or_lt_of_le, forall_const, h.continuousWithinAt, hf_cont, hf_cvx, hf_cvx.continuousOn_interior, interior_Ico, mem_Ioo
-/
lemma ConvexOn.continuousOn_Ico {f : Real -> Real} {y z : Real} (hf_cvx : ConvexOn Real (Ico y z) f)
    (hf_cont : ContinuousWithinAt f (Ici y) y) :
    ContinuousOn f (Ico y z) := by
  intro x hx
  rcases eq_or_lt_of_le (α := Real) hx.1 with rfl | hyx
  · rw [continuousWithinAt_Ico_iff_Ici hx.2]
    exact hf_cont
  · have h := hf_cvx.continuousOn_interior x
    simp only [interior_Ico, mem_Ioo, hyx, hx.2, and_self, forall_const] at h
    rw [continuousWithinAt_iff_continuousAt (Ioo_mem_nhds hyx hx.2)] at h
    exact h.continuousWithinAt

/--
lemma `ConcaveOn.continuousOn_Ico` / 引理 `ConcaveOn.continuousOn_Ico`

English:
lemma ConcaveOn.continuousOn_Ico
  statement: {f : Real -> Real} {y z : Real} (hf_cnv : ConcaveOn Real (Ico y z) f)
  proof: by
  simpa using hf_cnv.neg.continuousOn_Ico hf_cont.neg

中文:
引理 ConcaveOn.continuousOn_Ico
  结论: {f : 实数 -> 实数} {y z : 实数} (hf_cnv : ConcaveOn 实数 (左闭右开区间 y z) f)
  证明: by
  simpa using hf_cnv.neg.continuousOn_Ico hf_cont.neg

Depends on / 依赖: continuousOn_Ico, hf_cnv, hf_cnv.neg.continuousOn_Ico, hf_cont, hf_cont.neg
-/
lemma ConcaveOn.continuousOn_Ico {f : Real -> Real} {y z : Real} (hf_cnv : ConcaveOn Real (Ico y z) f)
    (hf_cont : ContinuousWithinAt f (Ici y) y) :
    ContinuousOn f (Ico y z) := by
  simpa using hf_cnv.neg.continuousOn_Ico hf_cont.neg

/--
lemma `ConvexOn.continuousOn_Icc` / 引理 `ConvexOn.continuousOn_Icc`

English:
lemma ConvexOn.continuousOn_Icc
  statement: {f : Real -> Real} {y z : Real} (hf_cvx : ConvexOn Real (Icc y z) f)
  proof: by
  suffices ContinuousOn f (Ico y z) ∧ ContinuousOn f (Ioc y z) by
    intro x hx
    rcases eq_or_lt_of_le (α := Real) hx.1 with rfl | hyx
    · exact hfy.mono (by grind)
    rcases eq_or_lt_of_le (α := Real) hx.2 with rfl | hxz
    · exact hfz.mono (by grind)
    have hx := this.1 x (by grind)
 

中文:
引理 ConvexOn.continuousOn_Icc
  结论: {f : 实数 -> 实数} {y z : 实数} (hf_cvx : ConvexOn 实数 (闭区间 y z) f)
  证明: by
  suffices ContinuousOn f (Ico y z) ∧ ContinuousOn f (Ioc y z) by
    intro x hx
    rcases eq_or_lt_of_le (α := Real) hx.1 with rfl | hyx
    · exact hfy.mono (by grind)
    rcases eq_or_lt_of_le (α := Real) hx.2 with rfl | hxz
    · exact hfz.mono (by grind)
    have hx := this.1 x (by grind)
 

Depends on / 依赖: ContinuousOn, ConvexOn, ConvexOn.continuousOn_Ico, ConvexOn.continuousOn_Ioc, Ico_mem_nhds, Ico_subset_Icc_self, continuousOn_Ico, continuousOn_Ioc, continuousWithinAt, continuousWithinAt_iff_continuousAt, convex_Ico, eq_or_lt_of_le, hf_cvx, hf_cvx.subset, hfy.mono, hfz.mono, hx.continuousWithinAt, subset
-/
lemma ConvexOn.continuousOn_Icc {f : Real -> Real} {y z : Real} (hf_cvx : ConvexOn Real (Icc y z) f)
    (hyz : y < z)
    (hfy : ContinuousWithinAt f (Ici y) y) (hfz : ContinuousWithinAt f (Iic z) z) :
    ContinuousOn f (Icc y z) := by
  suffices ContinuousOn f (Ico y z) ∧ ContinuousOn f (Ioc y z) by
    intro x hx
    rcases eq_or_lt_of_le (α := Real) hx.1 with rfl | hyx
    · exact hfy.mono (by grind)
    rcases eq_or_lt_of_le (α := Real) hx.2 with rfl | hxz
    · exact hfz.mono (by grind)
    have hx := this.1 x (by grind)
    rw [continuousWithinAt_iff_continuousAt (Ico_mem_nhds hyx hxz)] at hx
    exact hx.continuousWithinAt
  refine ⟨ConvexOn.continuousOn_Ico ?_ hfy, ConvexOn.continuousOn_Ioc ?_ hfz⟩
  · exact hf_cvx.subset Ico_subset_Icc_self (convex_Ico y z)
  · exact hf_cvx.subset Ioc_subset_Icc_self (convex_Ioc y z)

/--
lemma `ConcaveOn.continuousOn_Icc` / 引理 `ConcaveOn.continuousOn_Icc`

English:
lemma ConcaveOn.continuousOn_Icc
  statement: {f : Real -> Real} {y z : Real} (hf_cnv : ConcaveOn Real (Icc y z) f)
  proof: by
  simpa using hf_cnv.neg.continuousOn_Icc hyz hfy.neg hfz.neg

中文:
引理 ConcaveOn.continuousOn_Icc
  结论: {f : 实数 -> 实数} {y z : 实数} (hf_cnv : ConcaveOn 实数 (闭区间 y z) f)
  证明: by
  simpa using hf_cnv.neg.continuousOn_Icc hyz hfy.neg hfz.neg

Depends on / 依赖: continuousOn_Icc, hf_cnv, hf_cnv.neg.continuousOn_Icc, hfy.neg, hfz.neg
-/
lemma ConcaveOn.continuousOn_Icc {f : Real -> Real} {y z : Real} (hf_cnv : ConcaveOn Real (Icc y z) f)
    (hyz : y < z)
    (hfy : ContinuousWithinAt f (Ici y) y) (hfz : ContinuousWithinAt f (Iic z) z) :
    ContinuousOn f (Icc y z) := by
  simpa using hf_cnv.neg.continuousOn_Icc hyz hfy.neg hfz.neg

end Intervals
