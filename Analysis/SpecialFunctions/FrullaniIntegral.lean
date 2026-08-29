/-
Copyright (c) 2026 Louis (Yiyang) Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Louis (Yiyang) Liu
-/
module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Frullani's integral

This file proves **Frullani's integral**: if `f : ℝ → E` is locally integrable on `(0, ∞)` with
`f x → L` as `x → 0⁺` and `f x → R` as `x → +∞`, and `0 < a` and `0 < b`, then
`∫ x in Ioi 0, x⁻¹ • (f (a * x) - f (b * x)) = log (b / a) • (L - R)`
(`Frullani.integral_Ioi_eq`), provided the integrand is integrable on `(0, ∞)`.

We also prove a limit form `Frullani.tendsto_intervalIntegral`, which does not require global
integrability of the integrand.
-/

public section

open Real Set Filter MeasureTheory intervalIntegral Topology Metric

namespace Frullani

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E] {f : Real -> E}
         {a b c : Real} {L R : E}

/--
lemma `intervalIntegrable_inv_smul` / 引理 `intervalIntegrable_inv_smul`

English:
lemma intervalIntegrable_inv_smul
  statement: (hf : LocallyIntegrableOn f (Ioi 0)) (ha : 0 < a)
  proof: by
  have hsub : uIcc a b subseteq Ioi 0 := by simp [uIcc, Icc_subset_Ioi_iff, ha, hb]
  have hf_int : IntervalIntegrable f volume a b :=
    intervalIntegrable_iff.mpr
      ((hf.integrableOn_compact_subset hsub isCompact_uIcc).mono_set uIoc_subset_uIcc)
  exact hf_int.continuousOn_smul (continuous

中文:
引理 intervalIntegrable_inv_smul
  结论: (hf : Locally整数egrableOn f (Ioi 0)) (ha : 0 < a)
  证明: by
  have hsub : uIcc a b subseteq Ioi 0 := by simp [uIcc, Icc_subset_Ioi_iff, ha, hb]
  have hf_int : IntervalIntegrable f volume a b :=
    intervalIntegrable_iff.mpr
      ((hf.integrableOn_compact_subset hsub isCompact_uIcc).mono_set uIoc_subset_uIcc)
  exact hf_int.continuousOn_smul (continuous

Depends on / 依赖: Icc_subset_Ioi_iff, IntervalIntegrable, continuousOn_smul, hf.integrableOn_compact_subset, hf_int, hf_int.continuousOn_smul, integrableOn_compact_subset, intervalIntegrable_iff, intervalIntegrable_iff.mpr, isCompact_uIcc, mono_set, ne_of_gt, subseteq, uIoc_subset_uIcc, volume
-/
lemma intervalIntegrable_inv_smul (hf : LocallyIntegrableOn f (Ioi 0)) (ha : 0 < a)
    (hb : 0 < b) : IntervalIntegrable (fun x => x⁻¹ • f x) volume a b := by
  have hsub : uIcc a b subseteq Ioi 0 := by simp [uIcc, Icc_subset_Ioi_iff, ha, hb]
  have hf_int : IntervalIntegrable f volume a b :=
    intervalIntegrable_iff.mpr
      ((hf.integrableOn_compact_subset hsub isCompact_uIcc).mono_set uIoc_subset_uIcc)
  exact hf_int.continuousOn_smul (continuousOn_inv₀.mono fun x hx => ne_of_gt (hsub hx))

/--
lemma `intervalIntegrable_inv_smul_comp_mul` / 引理 `intervalIntegrable_inv_smul_comp_mul`

English:
lemma intervalIntegrable_inv_smul_comp_mul
  statement: (hf : LocallyIntegrableOn f (Ioi 0)) (ha : 0 < a)
  proof: by
  have hsub : uIcc a b subseteq Ioi 0 := by simp [uIcc, Icc_subset_Ioi_iff, ha, hb]
  have hf_cint : IntervalIntegrable f volume (c * a) (c * b) :=
    intervalIntegrable_iff.mpr
      ((hf.integrableOn_compact_subset (by simp [uIcc, Icc_subset_Ioi_iff, mul_pos hc ha,
        mul_pos hc hb]) isCo

中文:
引理 intervalIntegrable_inv_smul_comp_mul
  结论: (hf : Locally整数egrableOn f (Ioi 0)) (ha : 0 < a)
  证明: by
  have hsub : uIcc a b subseteq Ioi 0 := by simp [uIcc, Icc_subset_Ioi_iff, ha, hb]
  have hf_cint : IntervalIntegrable f volume (c * a) (c * b) :=
    intervalIntegrable_iff.mpr
      ((hf.integrableOn_compact_subset (by simp [uIcc, Icc_subset_Ioi_iff, mul_pos hc ha,
        mul_pos hc hb]) isCo

Depends on / 依赖: Icc_subset_Ioi_iff, IntervalIntegrable, comp_mul_left, hc.ne, hf.integrableOn_compact_subset, hf_cint, hf_cint.comp_mul_left, hf_comp, integrableOn_compact_subset, intervalIntegrable_iff, intervalIntegrable_iff.mpr, isCompact_uIcc, mono_set, mul_pos, subseteq, uIoc_subset_uIcc, volume
-/
lemma intervalIntegrable_inv_smul_comp_mul (hf : LocallyIntegrableOn f (Ioi 0)) (ha : 0 < a)
    (hb : 0 < b) (hc : 0 < c) :
    IntervalIntegrable (fun x => x⁻¹ • f (c * x)) volume a b := by
  have hsub : uIcc a b subseteq Ioi 0 := by simp [uIcc, Icc_subset_Ioi_iff, ha, hb]
  have hf_cint : IntervalIntegrable f volume (c * a) (c * b) :=
    intervalIntegrable_iff.mpr
      ((hf.integrableOn_compact_subset (by simp [uIcc, Icc_subset_Ioi_iff, mul_pos hc ha,
        mul_pos hc hb]) isCompact_uIcc).mono_set uIoc_subset_uIcc)
  have hf_comp : IntervalIntegrable (fun x => f (c * x)) volume a b := by
    have h := hf_cint.comp_mul_left (c := c)
    rwa [mul_div_cancel_left₀ a hc.ne', mul_div_cancel_left₀ b hc.ne'] at h
  exact hf_comp.continuousOn_smul (continuousOn_inv₀.mono fun x hx => ne_of_gt (hsub hx))

/--
lemma `integral_comp_mul_inv_smul` / 引理 `integral_comp_mul_inv_smul`

English:
lemma integral_comp_mul_inv_smul
  given: {ε r : Real} (hc : c != 0)
  proof: by
  let u : Real -> E := fun x => x⁻¹ • f x
  have key : (fun x => x⁻¹ • f (c * x)) = fun x => c • u (c * x) := by
    funext x
    simp only [u, smul_smul]
    congr 1
    field_simp
  rw [key]; rw [intervalIntegral.integral_smul]; rw [smul_integral_comp_mul_left]

中文:
引理 integral_comp_mul_inv_smul
  条件: {ε r : 实数} (hc : c != 0)
  证明: by
  let u : Real -> E := fun x => x⁻¹ • f x
  have key : (fun x => x⁻¹ • f (c * x)) = fun x => c • u (c * x) := by
    funext x
    simp only [u, smul_smul]
    congr 1
    field_simp
  rw [key]; rw [intervalIntegral.integral_smul]; rw [smul_integral_comp_mul_left]

Depends on / 依赖: integral_smul, intervalIntegral, intervalIntegral.integral_smul, smul_integral_comp_mul_left, smul_smul
-/
lemma integral_comp_mul_inv_smul {ε r : Real} (hc : c != 0) :
    ∫ x in ε..r, x⁻¹ • f (c * x) = ∫ x in c * ε..c * r, x⁻¹ • f x := by
  let u : Real -> E := fun x => x⁻¹ • f x
  have key : (fun x => x⁻¹ • f (c * x)) = fun x => c • u (c * x) := by
    funext x
    simp only [u, smul_smul]
    congr 1
    field_simp
  rw [key]; rw [intervalIntegral.integral_smul]; rw [smul_integral_comp_mul_left]

variable [CompleteSpace E]

/--
lemma `norm_integral_inv_smul_sub_le` / 引理 `norm_integral_inv_smul_sub_le`

English:
lemma norm_integral_inv_smul_sub_le
  statement: (hf : LocallyIntegrableOn f (Ioi 0)) (ha : 0 < a)
  proof: by
  have hsub : uIcc a b subseteq Ioi 0 := by simp [uIcc, Icc_subset_Ioi_iff, ha, hb]
  have hint_f : IntervalIntegrable (fun x => x⁻¹ • f x) volume a b :=
    intervalIntegrable_inv_smul hf ha hb
  have hint_V : IntervalIntegrable (fun x => x⁻¹ • V) volume a b := by
    apply ContinuousOn.interval

中文:
引理 norm_integral_inv_smul_sub_le
  结论: (hf : Locally整数egrableOn f (Ioi 0)) (ha : 0 < a)
  证明: by
  have hsub : uIcc a b subseteq Ioi 0 := by simp [uIcc, Icc_subset_Ioi_iff, ha, hb]
  have hint_f : IntervalIntegrable (fun x => x⁻¹ • f x) volume a b :=
    intervalIntegrable_inv_smul hf ha hb
  have hint_V : IntervalIntegrable (fun x => x⁻¹ • V) volume a b := by
    apply ContinuousOn.interval

Depends on / 依赖: ContinuousOn, ContinuousOn.intervalIntegrable, Icc_subset_Ioi_iff, IntervalIntegrable, continuousOn_const, hint_V, hint_f, hint_inv, intervalIntegrable, intervalIntegrable_inv_smul, ne_of_gt, subseteq, volume
-/
lemma norm_integral_inv_smul_sub_le (hf : LocallyIntegrableOn f (Ioi 0)) (ha : 0 < a)
    (hb : 0 < b) {V : E} {δ : Real} (hδ : 0 <= δ) (h : forall x in uIoc a b, ‖f x - V‖ <= δ) :
    ‖(∫ x in a..b, x⁻¹ • f x) - log (b / a) • V‖ <= δ * |log (b / a)| := by
  have hsub : uIcc a b subseteq Ioi 0 := by simp [uIcc, Icc_subset_Ioi_iff, ha, hb]
  have hint_f : IntervalIntegrable (fun x => x⁻¹ • f x) volume a b :=
    intervalIntegrable_inv_smul hf ha hb
  have hint_V : IntervalIntegrable (fun x => x⁻¹ • V) volume a b := by
    apply ContinuousOn.intervalIntegrable
    exact (continuousOn_inv₀.mono (fun x hx => ne_of_gt (hsub hx))).smul continuousOn_const
  have hint_inv : IntervalIntegrable (fun x : Real => x⁻¹ * δ) volume a b := by
    apply ContinuousOn.intervalIntegrable
    exact (continuousOn_inv₀.mono (fun x hx => ne_of_gt (hsub hx))).mul continuousOn_const
  calc ‖(∫ x in a..b, x⁻¹ • f x) - log (b / a) • V‖
    _ = ‖∫ x in a..b, x⁻¹ • (f x - V)‖ := by
        congr 1
        have : log (b / a) • V = ∫ x in a..b, x⁻¹ • V := by
          rw [intervalIntegral.integral_smul_const (f := fun x => (x⁻¹ : Real)) (c := V)]; rw [integral_inv_of_pos ha hb]
        rw [this]; rw [← integral_sub hint_f hint_V]
        congr 1
        funext x
        exact (smul_sub _ _ _).symm
    _ <= |∫ x in a..b, x⁻¹ * δ| := by
        apply norm_integral_le_abs_of_norm_le
        · exact (ae_restrict_mem measurableSet_uIoc).mono fun x hx => by
            have hx_pos : 0 < x :=
              lt_of_lt_of_le (lt_min ha hb) (uIoc_subset_uIcc hx).1
            rw [norm_smul]; rw [Real.norm_eq_abs]; rw [abs_of_pos (inv_pos.2 hx_pos)]
            exact mul_le_mul_of_nonneg_left (h x hx) (inv_nonneg.2 hx_pos.le)
        · exact hint_inv
    _ = δ * |log (b / a)| := by
        simp_rw [mul_comm, intervalIntegral.integral_const_mul, integral_inv_of_pos ha hb]
        exact (abs_mul δ (log (b / a))).trans (by rw [abs_of_nonneg hδ])

/--
lemma `tendsto_integral_inv_smul_of_tendsto_uniform` / 引理 `tendsto_integral_inv_smul_of_tendsto_uniform`

English:
lemma tendsto_integral_inv_smul_of_tendsto_uniform
  statement: (hf : LocallyIntegrableOn f (Ioi 0)) (ha : 0 < a)
  proof: by
  rw [Metric.tendsto_nhds]
  intro δ hδ
  set C := |log (b / a)| with hC_def
  set δ' := δ / (C + 1)
  filter_upwards [hpos, huni δ' (by positivity)] with t ht_pos hbound
  have hlog_eq : log (b * t / (a * t)) = log (b / a) := by
    rw [mul_div_mul_right b a (ne_of_gt ht_pos)]
  calc dist (∫ x i

中文:
引理 tendsto_integral_inv_smul_of_tendsto_uniform
  结论: (hf : Locally整数egrableOn f (Ioi 0)) (ha : 0 < a)
  证明: by
  rw [Metric.tendsto_nhds]
  intro δ hδ
  set C := |log (b / a)| with hC_def
  set δ' := δ / (C + 1)
  filter_upwards [hpos, huni δ' (by positivity)] with t ht_pos hbound
  have hlog_eq : log (b * t / (a * t)) = log (b / a) := by
    rw [mul_div_mul_right b a (ne_of_gt ht_pos)]
  calc dist (∫ x i

Depends on / 依赖: Metric, Metric.tendsto_nhds, dist_eq_norm, filter_upwards, hC_def, hbound, hlog_eq, ht_pos, mul_div_mul_right, ne_of_gt, tendsto_nhds
-/
lemma tendsto_integral_inv_smul_of_tendsto_uniform (hf : LocallyIntegrableOn f (Ioi 0)) (ha : 0 < a)
    (hb : 0 < b) {F : Filter Real} (hpos : forallᶠ t in F, 0 < t) {V : E}
    (huni : forall δ > 0, forallᶠ t in F, forall x in uIoc (a * t) (b * t), ‖f x - V‖ <= δ) :
    Tendsto (fun t => ∫ x in (a * t)..(b * t), x⁻¹ • f x) F (𝓝 (log (b / a) • V)) := by
  rw [Metric.tendsto_nhds]
  intro δ hδ
  set C := |log (b / a)| with hC_def
  set δ' := δ / (C + 1)
  filter_upwards [hpos, huni δ' (by positivity)] with t ht_pos hbound
  have hlog_eq : log (b * t / (a * t)) = log (b / a) := by
    rw [mul_div_mul_right b a (ne_of_gt ht_pos)]
  calc dist (∫ x in a * t..b * t, x⁻¹ • f x) (log (b / a) • V)
    _ = ‖(∫ x in a * t..b * t, x⁻¹ • f x) - log (b / a) • V‖ := dist_eq_norm _ _
    _ = ‖(∫ x in a * t..b * t, x⁻¹ • f x) - log (b * t / (a * t)) • V‖ := by rw [hlog_eq]
    _ <= δ' * |log (b * t / (a * t))| :=
        norm_integral_inv_smul_sub_le hf (by positivity) (by positivity) (by positivity) hbound
    _ = δ' * C := by rw [hlog_eq]
    _ = δ * (C / (C + 1)) := by ring
    _ < δ * 1 := mul_lt_mul_of_pos_left ((div_lt_one (by positivity)).2 (lt_add_one C)) hδ
    _ = δ := mul_one δ

/--
lemma `tendsto_integral_inv_smul_nhdsWithin` / 引理 `tendsto_integral_inv_smul_nhdsWithin`

English:
lemma tendsto_integral_inv_smul_nhdsWithin
  statement: (hf : LocallyIntegrableOn f (Ioi 0)) (ha : 0 < a)
  proof: by
  apply tendsto_integral_inv_smul_of_tendsto_uniform hf ha hb self_mem_nhdsWithin
  intro δ hδ
  have hev : forallᶠ x in 𝓝[>] (0 : Real), dist (f x) L < δ :=
    hL.eventually (ball_mem_nhds L hδ)
  rw [Filter.Eventually]; rw [mem_nhdsWithin_iff] at hev
  obtain ⟨η, hη, hη_sub⟩ := hev
  set M := 

中文:
引理 tendsto_integral_inv_smul_nhdsWithin
  结论: (hf : Locally整数egrableOn f (Ioi 0)) (ha : 0 < a)
  证明: by
  apply tendsto_integral_inv_smul_of_tendsto_uniform hf ha hb self_mem_nhdsWithin
  intro δ hδ
  have hev : forallᶠ x in 𝓝[>] (0 : Real), dist (f x) L < δ :=
    hL.eventually (ball_mem_nhds L hδ)
  rw [Filter.Eventually]; rw [mem_nhdsWithin_iff] at hev
  obtain ⟨η, hη, hη_sub⟩ := hev
  set M := 

Depends on / 依赖: Eventually, Filter, Filter.Eventually, Iio_mem_nhds, ball_mem_nhds, div_pos, eventually, filter_upwards, hL.eventually, hM_def, ht_bound, ht_pos, hx_pos, lt_max_of_lt_left, lt_min, mem_nhdsWithin_iff, nhdsWithin_le_nhds, self_mem_nhdsWithin, tendsto_integral_inv_smul_of_tendsto_uniform
-/
lemma tendsto_integral_inv_smul_nhdsWithin (hf : LocallyIntegrableOn f (Ioi 0)) (ha : 0 < a)
    (hb : 0 < b) (hL : Tendsto f (𝓝[>] 0) (𝓝 L)) :
    Tendsto (fun ε => ∫ x in (a * ε)..(b * ε), x⁻¹ • f x) (𝓝[>] 0) (𝓝 (log (b / a) • L)) := by
  apply tendsto_integral_inv_smul_of_tendsto_uniform hf ha hb self_mem_nhdsWithin
  intro δ hδ
  have hev : forallᶠ x in 𝓝[>] (0 : Real), dist (f x) L < δ :=
    hL.eventually (ball_mem_nhds L hδ)
  rw [Filter.Eventually]; rw [mem_nhdsWithin_iff] at hev
  obtain ⟨η, hη, hη_sub⟩ := hev
  set M := max a b with hM_def
  have hM : 0 < M := lt_max_of_lt_left ha
  filter_upwards [self_mem_nhdsWithin,
    nhdsWithin_le_nhds (Iio_mem_nhds (div_pos hη hM))] with t ht_pos ht_bound
  intro x hx
  have hx_pos : 0 < x := (lt_min (by positivity) (by positivity)).trans_le (uIoc_subset_uIcc hx).1
  have hx_lt_η : dist x 0 < η := by
    rw [Real.dist_eq]; rw [sub_zero]; rw [abs_of_pos hx_pos]
    calc x
      _ <= max (a * t) (b * t) := (uIoc_subset_uIcc hx).2
      _ = M * t := by rw [hM_def, max_mul_of_nonneg _ _ ht_pos.le]
      _ < M * (η / M) := mul_lt_mul_of_pos_left ht_bound hM
      _ = η := mul_div_cancel₀ η (ne_of_gt hM)
  have := hη_sub ⟨mem_ball.2 hx_lt_η, hx_pos⟩
  rw [mem_ofPred_eq]; rw [dist_eq_norm] at this
  exact le_of_lt this

/--
lemma `tendsto_integral_inv_smul_atTop` / 引理 `tendsto_integral_inv_smul_atTop`

English:
lemma tendsto_integral_inv_smul_atTop
  statement: (hf : LocallyIntegrableOn f (Ioi 0)) (ha : 0 < a) (hb : 0 < b)
  proof: by
  apply tendsto_integral_inv_smul_of_tendsto_uniform hf ha hb
    (eventually_atTop.2 ⟨1, fun r hr => zero_lt_one.trans_le hr⟩)
  intro δ hδ
  have hev : forallᶠ x in atTop, dist (f x) R < δ :=
    hR.eventually (ball_mem_nhds R hδ)
  rw [Filter.eventually_atTop] at hev
  obtain ⟨N, hN⟩ := hev
  

中文:
引理 tendsto_integral_inv_smul_atTop
  结论: (hf : Locally整数egrableOn f (Ioi 0)) (ha : 0 < a) (hb : 0 < b)
  证明: by
  apply tendsto_integral_inv_smul_of_tendsto_uniform hf ha hb
    (eventually_atTop.2 ⟨1, fun r hr => zero_lt_one.trans_le hr⟩)
  intro δ hδ
  have hev : forallᶠ x in atTop, dist (f x) R < δ :=
    hR.eventually (ball_mem_nhds R hδ)
  rw [Filter.eventually_atTop] at hev
  obtain ⟨N, hN⟩ := hev
  

Depends on / 依赖: Filter, Filter.eventually_atTop, ball_mem_nhds, eventually, eventually_atTop, filter_upwards, hR.eventually, ht_pos, le_max_left, lt_min, lt_of_lt_of_le, one_pos, tendsto_integral_inv_smul_of_tendsto_uniform, trans_le, zero_lt_one, zero_lt_one.trans_le
-/
lemma tendsto_integral_inv_smul_atTop (hf : LocallyIntegrableOn f (Ioi 0)) (ha : 0 < a) (hb : 0 < b)
    (hR : Tendsto f atTop (𝓝 R)) :
    Tendsto (fun r => ∫ x in (a * r)..(b * r), x⁻¹ • f x) atTop (𝓝 (log (b / a) • R)) := by
  apply tendsto_integral_inv_smul_of_tendsto_uniform hf ha hb
    (eventually_atTop.2 ⟨1, fun r hr => zero_lt_one.trans_le hr⟩)
  intro δ hδ
  have hev : forallᶠ x in atTop, dist (f x) R < δ :=
    hR.eventually (ball_mem_nhds R hδ)
  rw [Filter.eventually_atTop] at hev
  obtain ⟨N, hN⟩ := hev
  have hm : 0 < min a b := lt_min ha hb
  filter_upwards [eventually_atTop.2 ⟨max 1 (N / min a b), fun r hr => hr⟩] with t ht
  intro x hx
  have ht_pos : 0 < t := lt_of_lt_of_le one_pos ((le_max_left 1 _).trans ht)
  have hNx : N <= x :=
    calc N
      _ = min a b * (N / min a b) := by field_simp
      _ <= min a b * t :=
        mul_le_mul_of_nonneg_left ((le_max_right _ _).trans ht) hm.le
      _ = min (a * t) (b * t) := by rw [min_mul_of_nonneg _ _ ht_pos.le]
      _ <= x := (uIoc_subset_uIcc hx).1
  have hdist := hN x hNx
  rw [dist_eq_norm] at hdist
  exact le_of_lt hdist

/--
theorem `tendsto_intervalIntegral` / 定理 `tendsto_intervalIntegral`

English:
theorem tendsto_intervalIntegral
  statement: (hf : LocallyIntegrableOn f (Ioi 0)) (ha : 0 < a) (hb : 0 < b)
  proof: by
  let u := fun x => x⁻¹ • f x
  have hint {p q : Real} (hp : 0 < p) (hq : 0 < q) : IntervalIntegrable u volume p q :=
    intervalIntegrable_inv_smul hf hp hq
  have hsplit {ε r : Real} (hε : 0 < ε) (hr : 0 < r) :
      ∫ x in ε..r, x⁻¹ • (f (a * x) - f (b * x)) =
      (∫ x in (a * ε)..(b * ε), 

中文:
定理 tendsto_intervalIntegral
  结论: (hf : Locally整数egrableOn f (Ioi 0)) (ha : 0 < a) (hb : 0 < b)
  证明: by
  let u := fun x => x⁻¹ • f x
  have hint {p q : Real} (hp : 0 < p) (hq : 0 < q) : IntervalIntegrable u volume p q :=
    intervalIntegrable_inv_smul hf hp hq
  have hsplit {ε r : Real} (hε : 0 < ε) (hr : 0 < r) :
      ∫ x in ε..r, x⁻¹ • (f (a * x) - f (b * x)) =
      (∫ x in (a * ε)..(b * ε), 

Depends on / 依赖: IntervalIntegrable, hsplit, integral_sub, intervalIntegrable_in, intervalIntegrable_inv_smul, simp_rw, smul_sub, volume
-/
theorem tendsto_intervalIntegral (hf : LocallyIntegrableOn f (Ioi 0)) (ha : 0 < a) (hb : 0 < b)
    (hL : Tendsto f (𝓝[>] 0) (𝓝 L)) (hR : Tendsto f atTop (𝓝 R)) :
    Tendsto (fun p : Real × Real => ∫ x in p.1..p.2, x⁻¹ • (f (a * x) - f (b * x)))
      ((𝓝[>] 0) ×ˢ atTop) (𝓝 (log (b / a) • (L - R))) := by
  let u := fun x => x⁻¹ • f x
  have hint {p q : Real} (hp : 0 < p) (hq : 0 < q) : IntervalIntegrable u volume p q :=
    intervalIntegrable_inv_smul hf hp hq
  have hsplit {ε r : Real} (hε : 0 < ε) (hr : 0 < r) :
      ∫ x in ε..r, x⁻¹ • (f (a * x) - f (b * x)) =
      (∫ x in (a * ε)..(b * ε), u x) - ∫ x in (a * r)..(b * r), u x := by
    calc ∫ x in ε..r, x⁻¹ • (f (a * x) - f (b * x))
      _ = (∫ x in ε..r, x⁻¹ • f (a * x)) - ∫ x in ε..r, x⁻¹ • f (b * x) := by
        simp_rw [smul_sub]
        exact integral_sub (intervalIntegrable_inv_smul_comp_mul hf hε hr ha)
          (intervalIntegrable_inv_smul_comp_mul hf hε hr hb)
      _ = (∫ y in a * ε..a * r, u y) - ∫ y in b * ε..b * r, u y := by
        rw [integral_comp_mul_inv_smul ha.ne']; rw [integral_comp_mul_inv_smul hb.ne']
      _ = _ := integral_interval_sub_interval_comm
                 (hint (mul_pos ha hε) (mul_pos ha hr))
                 (hint (mul_pos hb hε) (mul_pos hb hr))
                 (hint (mul_pos ha hε) (mul_pos hb hε))
  have h_ev : (fun p : Real × Real => ∫ x in p.1..p.2, x⁻¹ • (f (a * x) - f (b * x))) =ᶠ[(𝓝[>] 0) ×ˢ atTop]
      fun p => (∫ x in (a * p.1)..(b * p.1), u x) - ∫ x in (a * p.2)..(b * p.2), u x := by
    filter_upwards [prod_mem_prod (eventually_nhdsWithin_of_forall fun _ h => h)
      (eventually_atTop.2 ⟨1, fun _ h => lt_of_lt_of_le one_pos h⟩)] with ⟨ε, r⟩ ⟨hε, hr⟩
    exact hsplit hε hr
  rw [tendsto_congr' h_ev]; rw [show log (b / a) • (L - R) =
    log (b / a) • L - log (b / a) • R from smul_sub _ _ _]
  exact ((tendsto_integral_inv_smul_nhdsWithin hf ha hb hL).comp tendsto_fst).sub
    ((tendsto_integral_inv_smul_atTop hf ha hb hR).comp tendsto_snd)

/--
theorem `integral_Ioi_eq` / 定理 `integral_Ioi_eq`

English:
theorem integral_Ioi_eq
  statement: (hf : LocallyIntegrableOn f (Ioi 0)) (ha : 0 < a) (hb : 0 < b)
  proof: by
  have h_lim := (tendsto_intervalIntegral hf ha hb hL hR).mono_left curry_le_prod
  set g := fun x => x⁻¹ • (f (a * x) - f (b * x)) with hg
  apply tendsto_nhds_unique
    (hint.continuousWithinAt_Ici_primitive_Ioi.mono_left (nhdsWithin_mono 0 Ioi_subset_Ici_self))
  rw [tendsto_nhdsWithin_nhds]


中文:
定理 integral_Ioi_eq
  结论: (hf : Locally整数egrableOn f (Ioi 0)) (ha : 0 < a) (hb : 0 < b)
  证明: by
  have h_lim := (tendsto_intervalIntegral hf ha hb hL hR).mono_left curry_le_prod
  set g := fun x => x⁻¹ • (f (a * x) - f (b * x)) with hg
  apply tendsto_nhds_unique
    (hint.continuousWithinAt_Ici_primitive_Ioi.mono_left (nhdsWithin_mono 0 Ioi_subset_Ici_self))
  rw [tendsto_nhdsWithin_nhds]


Depends on / 依赖: Eventually, Filter, Filter.Eventually, Ioi_subset_Ici_self, Metric, Metric.tendsto_nhds, continuousWithinAt_Ici_primitive_Ioi, curry_le_prod, eventually_curry_iff, h_lim, hint.continuousWithinAt_Ici_primitive_Ioi.mono_left, mem_nhdsWithin_iff, mono_left, nhdsWithin_mono, simp_rw, specialize, tendsto_intervalIntegral, tendsto_nhds, tendsto_nhdsWithin_nhds, tendsto_nhds_unique
-/
theorem integral_Ioi_eq (hf : LocallyIntegrableOn f (Ioi 0)) (ha : 0 < a) (hb : 0 < b)
    (hL : Tendsto f (𝓝[>] 0) (𝓝 L)) (hR : Tendsto f atTop (𝓝 R))
    (hint : IntegrableOn (fun x => x⁻¹ • (f (a * x) - f (b * x))) (Ioi 0)) :
    ∫ x in Ioi 0, x⁻¹ • (f (a * x) - f (b * x)) = log (b / a) • (L - R) := by
  have h_lim := (tendsto_intervalIntegral hf ha hb hL hR).mono_left curry_le_prod
  set g := fun x => x⁻¹ • (f (a * x) - f (b * x)) with hg
  apply tendsto_nhds_unique
    (hint.continuousWithinAt_Ici_primitive_Ioi.mono_left (nhdsWithin_mono 0 Ioi_subset_Ici_self))
  rw [tendsto_nhdsWithin_nhds]
  intro ε hε
  rw [Metric.tendsto_nhds] at h_lim
  specialize h_lim (ε / 2) (by positivity)
  rw [eventually_curry_iff]; rw [Filter.Eventually]; rw [mem_nhdsWithin_iff] at h_lim
  obtain ⟨δ, hδ_pos, hδ⟩ := h_lim
  simp_rw [subset_def, mem_inter_iff, mem_ball] at hδ
  refine ⟨δ, hδ_pos, ?_⟩
  intro x hx hdist
  specialize hδ x ⟨hdist, hx⟩
  rw [mem_ofPred] at hδ
  have hint' : IntegrableOn g (Ioi x) := hint.mono (by grind) (by simp)
  have htends := intervalIntegral_tendsto_integral_Ioi x hint' tendsto_id
  have hle := le_of_tendsto (htends.dist tendsto_const_nhds) (hδ.mono (fun _ hy => hy.le))
  linarith

end Frullani
