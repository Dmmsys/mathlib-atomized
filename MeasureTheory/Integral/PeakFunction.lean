/-
Copyright (c) 2023 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Integrals against peak functions

A sequence of peak functions is a sequence of functions with average one concentrating around
a point `x₀`. Given such a sequence `φₙ`, then `∫ φₙ g` tends to `g x₀` in many situations, with
a whole zoo of possible assumptions on `φₙ` and `g`. This file is devoted to such results. Such
functions are also called approximations of unity, or approximations of identity.

## Main results

* `tendsto_setIntegral_peak_smul_of_integrableOn_of_tendsto`: If a sequence of peak
  functions `φᵢ` converges uniformly to zero away from a point `x₀`, and
  `g` is integrable and continuous at `x₀`, then `∫ φᵢ • g` converges to `g x₀`.
* `tendsto_setIntegral_pow_smul_of_unique_maximum_of_isCompact_of_continuousOn`:
  If a continuous function `c` realizes its maximum at a unique point `x₀` in a compact set `s`,
  then the sequence of functions `(c x) ^ n / ∫ (c x) ^ n` is a sequence of peak functions
  concentrating around `x₀`. Therefore, `∫ (c x) ^ n * g / ∫ (c x) ^ n` converges to `g x₀`
  if `g` is continuous on `s`.
* `tendsto_integral_comp_smul_smul_of_integrable`:
  If a nonnegative function `φ` has integral one and decays quickly enough at infinity,
  then its renormalizations `x ↦ c ^ d * φ (c • x)` form a sequence of peak functions as `c → ∞`.
  Therefore, `∫ (c ^ d * φ (c • x)) • g x` converges to `g 0` as `c → ∞` if `g` is continuous
  at `0` and integrable.

Note that there are related results about convolution with respect to peak functions in the file
`Mathlib/Analysis/Convolution.lean`, such as `MeasureTheory.convolution_tendsto_right` there.
-/

public section

open Set Filter MeasureTheory MeasureTheory.Measure TopologicalSpace Metric

open scoped Topology ENNReal

/-!
### General convergent result for integrals against a sequence of peak functions
-/

open Set

variable {α E ι : Type*} {hm : MeasurableSpace α} {μ : Measure α} [TopologicalSpace α]
  [BorelSpace α] [NormedAddCommGroup E] [NormedSpace Real E] {g : α -> E} {l : Filter ι} {x₀ : α}
  {s t : Set α} {φ : ι -> α -> Real} {a : E}

/--
theorem `integrableOn_peak_smul_of_integrableOn_of_tendsto` / 定理 `integrableOn_peak_smul_of_integrableOn_of_tendsto`

English:
theorem integrableOn_peak_smul_of_integrableOn_of_tendsto
  proof: by
  obtain ⟨u, u_open, x₀u, ut, hu⟩ :
      exists u, IsOpen u ∧ x₀ in u ∧ s inter u subseteq t ∧ forall x in u inter s, g x in ball a 1 := by
    rcases mem_nhdsWithin.1 (Filter.inter_mem h'st (hcg (ball_mem_nhds _ zero_lt_one)))
      with ⟨u, u_open, x₀u, hu⟩
    refine ⟨u, u_open, x₀u, ?_, hu.t

中文:
定理 integrableOn_peak_smul_of_integrableOn_of_tendsto
  证明: by
  obtain ⟨u, u_open, x₀u, ut, hu⟩ :
      exists u, IsOpen u ∧ x₀ in u ∧ s inter u subseteq t ∧ forall x in u inter s, g x in ball a 1 := by
    rcases mem_nhdsWithin.1 (Filter.inter_mem h'st (hcg (ball_mem_nhds _ zero_lt_one)))
      with ⟨u, u_open, x₀u, hu⟩
    refine ⟨u, u_open, x₀u, ?_, hu.t

Depends on / 依赖: Filter, Filter.inter_mem, IsOpen, ball_mem_nhds, filter_upwards, hu.trans, inter_comm, inter_mem, inter_subset_left, inter_subset_right, mem_nhdsWithin, subseteq, tendstoUniformlyOn_iff, tendsto_iff_norm_sub_tendsto_zero, tendsto_order, u_open, zero_lt_one
-/
theorem integrableOn_peak_smul_of_integrableOn_of_tendsto
    (hs : MeasurableSet s) (h'st : t in 𝓝[s] x₀)
    (hlφ : forall u : Set α, IsOpen u -> x₀ in u -> TendstoUniformlyOn φ 0 l (s \ u))
    (hiφ : Tendsto (fun i => ∫ x in t, φ i x ∂μ) l (𝓝 1))
    (h'iφ : forallᶠ i in l, AEStronglyMeasurable (φ i) (μ.restrict s))
    (hmg : IntegrableOn g s μ) (hcg : Tendsto g (𝓝[s] x₀) (𝓝 a)) :
    forallᶠ i in l, IntegrableOn (fun x => φ i x • g x) s μ := by
  obtain ⟨u, u_open, x₀u, ut, hu⟩ :
      exists u, IsOpen u ∧ x₀ in u ∧ s inter u subseteq t ∧ forall x in u inter s, g x in ball a 1 := by
    rcases mem_nhdsWithin.1 (Filter.inter_mem h'st (hcg (ball_mem_nhds _ zero_lt_one)))
      with ⟨u, u_open, x₀u, hu⟩
    refine ⟨u, u_open, x₀u, ?_, hu.trans inter_subset_right⟩
    rw [inter_comm]
    exact hu.trans inter_subset_left
  rw [tendsto_iff_norm_sub_tendsto_zero] at hiφ
  filter_upwards [tendstoUniformlyOn_iff.1 (hlφ u u_open x₀u) 1 zero_lt_one,
    (tendsto_order.1 hiφ).2 1 zero_lt_one, h'iφ] with i hi h'i h''i
  have I : IntegrableOn (φ i) t μ := .of_integral_ne_zero (fun h => by simp [h] at h'i)
  have A : IntegrableOn (fun x => φ i x • g x) (s \ u) μ := by
    refine Integrable.smul_of_top_right (hmg.mono sdiff_subset le_rfl) ?_
    apply memLp_top_of_bound (h''i.mono_set sdiff_subset) 1
    filter_upwards [self_mem_ae_restrict (hs.diff u_open.measurableSet)] with x hx
    simpa only [Pi.zero_apply, dist_zero_left] using (hi x hx).le
  have B : IntegrableOn (fun x => φ i x • g x) (s inter u) μ := by
    apply Integrable.smul_of_top_left
    · exact IntegrableOn.mono_set I ut
    · apply
        memLp_top_of_bound (hmg.mono_set inter_subset_left).aestronglyMeasurable (‖a‖ + 1)
      filter_upwards [self_mem_ae_restrict (hs.inter u_open.measurableSet)] with x hx
      rw [inter_comm] at hx
      exact (norm_lt_of_mem_ball (hu x hx)).le
  convert! A.union B
  simp only [sdiff_union_inter]

/--
theorem `tendsto_setIntegral_peak_smul_of_integrableOn_of_tendsto_aux` / 定理 `tendsto_setIntegral_peak_smul_of_integrableOn_of_tendsto_aux`

English:
theorem tendsto_setIntegral_peak_smul_of_integrableOn_of_tendsto_aux
  proof: by
  refine Metric.tendsto_nhds.2 fun ε εpos => ?_
  obtain ⟨δ, hδ, δpos, δone⟩ : exists δ, (δ * ∫ x in s, ‖g x‖ ∂μ) + 2 * δ < ε ∧ 0 < δ ∧ δ < 1 := by
    have A :
      Tendsto (fun δ => (δ * ∫ x in s, ‖g x‖ ∂μ) + 2 * δ) (𝓝[>] 0)
        (𝓝 ((0 * ∫ x in s, ‖g x‖ ∂μ) + 2 * 0)) := by
      apply Tend

中文:
定理 tendsto_setIntegral_peak_smul_of_integrableOn_of_tendsto_aux
  证明: by
  refine Metric.tendsto_nhds.2 fun ε εpos => ?_
  obtain ⟨δ, hδ, δpos, δone⟩ : exists δ, (δ * ∫ x in s, ‖g x‖ ∂μ) + 2 * δ < ε ∧ 0 < δ ∧ δ < 1 := by
    have A :
      Tendsto (fun δ => (δ * ∫ x in s, ‖g x‖ ∂μ) + 2 * δ) (𝓝[>] 0)
        (𝓝 ((0 * ∫ x in s, ‖g x‖ ∂μ) + 2 * 0)) := by
      apply Tend

Depends on / 依赖: Ioo_mem_nhdsGT, Metric, Metric.tendsto_nhds, Tendsto, Tendsto.mono_left, const_mul, mono_left, mul_zero, nhdsWithin_le_nhds, tendsto_const_nhds, tendsto_id, tendsto_id.const_mul, tendsto_id.mul, tendsto_nhds, zero_add, zero_lt_one, zero_mul
-/
theorem tendsto_setIntegral_peak_smul_of_integrableOn_of_tendsto_aux
    (hs : MeasurableSet s) (ht : MeasurableSet t) (hts : t subseteq s) (h'ts : t in 𝓝[s] x₀)
    (hnφ : forallᶠ i in l, forall x in s, 0 <= φ i x)
    (hlφ : forall u : Set α, IsOpen u -> x₀ in u -> TendstoUniformlyOn φ 0 l (s \ u))
    (hiφ : Tendsto (fun i => ∫ x in t, φ i x ∂μ) l (𝓝 1))
    (h'iφ : forallᶠ i in l, AEStronglyMeasurable (φ i) (μ.restrict s))
    (hmg : IntegrableOn g s μ) (hcg : Tendsto g (𝓝[s] x₀) (𝓝 0)) :
    Tendsto (fun i : ι => ∫ x in s, φ i x • g x ∂μ) l (𝓝 0) := by
  refine Metric.tendsto_nhds.2 fun ε εpos => ?_
  obtain ⟨δ, hδ, δpos, δone⟩ : exists δ, (δ * ∫ x in s, ‖g x‖ ∂μ) + 2 * δ < ε ∧ 0 < δ ∧ δ < 1 := by
    have A :
      Tendsto (fun δ => (δ * ∫ x in s, ‖g x‖ ∂μ) + 2 * δ) (𝓝[>] 0)
        (𝓝 ((0 * ∫ x in s, ‖g x‖ ∂μ) + 2 * 0)) := by
      apply Tendsto.mono_left _ nhdsWithin_le_nhds
      exact (tendsto_id.mul tendsto_const_nhds).add (tendsto_id.const_mul _)
    rw [zero_mul]; rw [zero_add]; rw [mul_zero] at A
    have : Ioo (0 : Real) 1 in 𝓝[>] 0 := Ioo_mem_nhdsGT zero_lt_one
    rcases (((tendsto_order.1 A).2 ε εpos).and this).exists with ⟨δ, hδ, h'δ⟩
    exact ⟨δ, hδ, h'δ.1, h'δ.2⟩
  suffices forallᶠ i in l, ‖∫ x in s, φ i x • g x ∂μ‖ <= (δ * ∫ x in s, ‖g x‖ ∂μ) + 2 * δ by
    filter_upwards [this] with i hi
    simp only [dist_zero_right]
    exact hi.trans_lt hδ
  obtain ⟨u, u_open, x₀u, ut, hu⟩ :
      exists u, IsOpen u ∧ x₀ in u ∧ s inter u subseteq t ∧ forall x in u inter s, g x in ball 0 δ := by
    rcases mem_nhdsWithin.1 (Filter.inter_mem h'ts (hcg (ball_mem_nhds _ δpos)))
      with ⟨u, u_open, x₀u, hu⟩
    refine ⟨u, u_open, x₀u, ?_, hu.trans inter_subset_right⟩
    rw [inter_comm]
    exact hu.trans inter_subset_left
  filter_upwards [tendstoUniformlyOn_iff.1 (hlφ u u_open x₀u) δ δpos,
    (tendsto_order.1 (tendsto_iff_norm_sub_tendsto_zero.1 hiφ)).2 δ δpos, hnφ,
    integrableOn_peak_smul_of_integrableOn_of_tendsto hs h'ts hlφ hiφ h'iφ hmg hcg]
    with i hi h'i hφpos h''i
  have I : IntegrableOn (φ i) t μ := by
    apply Integrable.of_integral_ne_zero (fun h => ?_)
    simp [h] at h'i
    linarith
  have B : ‖∫ x in s inter u, φ i x • g x ∂μ‖ <= 2 * δ :=
    calc
      ‖∫ x in s inter u, φ i x • g x ∂μ‖ <= ∫ x in s inter u, ‖φ i x • g x‖ ∂μ :=
        norm_integral_le_integral_norm _
      _ <= ∫ x in s inter u, ‖φ i x‖ * δ ∂μ := by
        refine setIntegral_mono_on ?_ ?_ (hs.inter u_open.measurableSet) fun x hx => ?_
        · exact IntegrableOn.mono_set h''i.norm inter_subset_left
        · exact IntegrableOn.mono_set (I.norm.mul_const _) ut
        rw [norm_smul]
        gcongr
        rw [inter_comm] at hu
        exact (mem_ball_zero_iff.1 (hu x hx)).le
      _ <= ∫ x in t, ‖φ i x‖ * δ ∂μ := by
        apply setIntegral_mono_set
        · exact I.norm.mul_const _
        · exact Eventually.of_forall fun x => mul_nonneg (norm_nonneg _) δpos.le
        · exact Eventually.of_forall ut
      _ = ∫ x in t, φ i x * δ ∂μ := by
        apply setIntegral_congr_fun ht fun x hx => ?_
        rw [Real.norm_of_nonneg (hφpos _ (hts hx))]
      _ = (∫ x in t, φ i x ∂μ) * δ := by rw [integral_mul_const]
      _ <= 2 * δ := by gcongr; linarith [(le_abs_self _).trans h'i.le]
  have C : ‖∫ x in s \ u, φ i x • g x ∂μ‖ <= δ * ∫ x in s, ‖g x‖ ∂μ :=
    calc
      ‖∫ x in s \ u, φ i x • g x ∂μ‖ <= ∫ x in s \ u, ‖φ i x • g x‖ ∂μ :=
        norm_integral_le_integral_norm _
      _ <= ∫ x in s \ u, δ * ‖g x‖ ∂μ := by
        refine setIntegral_mono_on ?_ ?_ (hs.diff u_open.measurableSet) fun x hx => ?_
        · exact IntegrableOn.mono_set h''i.norm sdiff_subset
        · exact IntegrableOn.mono_set (hmg.norm.const_mul _) sdiff_subset
        rw [norm_smul]
        gcongr
        simpa only [Pi.zero_apply, dist_zero_left] using (hi x hx).le
      _ <= δ * ∫ x in s, ‖g x‖ ∂μ := by
        rw [integral_const_mul]
        apply mul_le_mul_of_nonneg_left (setIntegral_mono_set hmg.norm _ _) δpos.le
        · filter_upwards with x using norm_nonneg _
        · filter_upwards using sdiff_subset (s := s) (t := u)
  calc
    ‖∫ x in s, φ i x • g x ∂μ‖ =
      ‖(∫ x in s \ u, φ i x • g x ∂μ) + ∫ x in s inter u, φ i x • g x ∂μ‖ := by
      conv_lhs => rw [← sdiff_union_inter s u]
      rw [setIntegral_union disjoint_sdiff_inter (hs.inter u_open.measurableSet)
          (h''i.mono_set sdiff_subset) (h''i.mono_set inter_subset_left)]
    _ <= ‖∫ x in s \ u, φ i x • g x ∂μ‖ + ‖∫ x in s inter u, φ i x • g x ∂μ‖ := norm_add_le _ _
    _ <= (δ * ∫ x in s, ‖g x‖ ∂μ) + 2 * δ := add_le_add C B

variable [CompleteSpace E]

/--
theorem `tendsto_setIntegral_peak_smul_of_integrableOn_of_tendsto` / 定理 `tendsto_setIntegral_peak_smul_of_integrableOn_of_tendsto`

English:
theorem tendsto_setIntegral_peak_smul_of_integrableOn_of_tendsto
  proof: by
  let h := g - t.indicator (fun _ => a)
  have A : Tendsto (fun i : ι => (∫ x in s, φ i x • h x ∂μ) + (∫ x in t, φ i x ∂μ) • a) l
      (𝓝 (0 + (1 : Real) • a)) := by
    refine Tendsto.add ?_ (Tendsto.smul hiφ tendsto_const_nhds)
    apply tendsto_setIntegral_peak_smul_of_integrableOn_of_tendsto

中文:
定理 tendsto_setIntegral_peak_smul_of_integrableOn_of_tendsto
  证明: by
  let h := g - t.indicator (fun _ => a)
  have A : Tendsto (fun i : ι => (∫ x in s, φ i x • h x ∂μ) + (∫ x in t, φ i x ∂μ) • a) l
      (𝓝 (0 + (1 : Real) • a)) := by
    refine Tendsto.add ?_ (Tendsto.smul hiφ tendsto_const_nhds)
    apply tendsto_setIntegral_peak_smul_of_integrableOn_of_tendsto

Depends on / 依赖: Tendsto, Tendsto.add, Tendsto.smul, hmg.sub, indicator, integrableOn_const_iff, integrableOn_indicator_iff, inter_subset_left, lt_of_le_of_lt, lt_top, measure_mono, sub_self, t.indicator, t.lt_top, tendsto_const_nhds, tendsto_setIntegral_peak_smul_of_integrableOn_of_tendsto_aux
-/
theorem tendsto_setIntegral_peak_smul_of_integrableOn_of_tendsto
    (hs : MeasurableSet s) {t : Set α} (ht : MeasurableSet t) (hts : t subseteq s) (h'ts : t in 𝓝[s] x₀)
    (h't : μ t != ∞) (hnφ : forallᶠ i in l, forall x in s, 0 <= φ i x)
    (hlφ : forall u : Set α, IsOpen u -> x₀ in u -> TendstoUniformlyOn φ 0 l (s \ u))
    (hiφ : Tendsto (fun i => ∫ x in t, φ i x ∂μ) l (𝓝 1))
    (h'iφ : forallᶠ i in l, AEStronglyMeasurable (φ i) (μ.restrict s))
    (hmg : IntegrableOn g s μ) (hcg : Tendsto g (𝓝[s] x₀) (𝓝 a)) :
    Tendsto (fun i : ι => ∫ x in s, φ i x • g x ∂μ) l (𝓝 a) := by
  let h := g - t.indicator (fun _ => a)
  have A : Tendsto (fun i : ι => (∫ x in s, φ i x • h x ∂μ) + (∫ x in t, φ i x ∂μ) • a) l
      (𝓝 (0 + (1 : Real) • a)) := by
    refine Tendsto.add ?_ (Tendsto.smul hiφ tendsto_const_nhds)
    apply tendsto_setIntegral_peak_smul_of_integrableOn_of_tendsto_aux hs ht hts h'ts
        hnφ hlφ hiφ h'iφ
    · apply hmg.sub
      simp only [integrableOn_indicator_iff ht, integrableOn_const_iff (C := a)]
      right
      exact lt_of_le_of_lt (measure_mono inter_subset_left) (h't.lt_top)
    · rw [← sub_self a]
      apply Tendsto.sub hcg
      apply tendsto_const_nhds.congr'
      filter_upwards [h'ts] with x hx using by simp [hx]
  simp only [one_smul, zero_add] at A
  refine Tendsto.congr' ?_ A
  filter_upwards [integrableOn_peak_smul_of_integrableOn_of_tendsto hs h'ts
    hlφ hiφ h'iφ hmg hcg,
    (tendsto_order.1 (tendsto_iff_norm_sub_tendsto_zero.1 hiφ)).2 1 zero_lt_one] with i hi h'i
  simp only [h, Pi.sub_apply, smul_sub, ← indicator_smul_apply]
  rw [integral_sub hi]; rw [setIntegral_indicator ht]; rw [inter_eq_right.mpr hts]; rw [integral_smul_const]; rw [sub_add_cancel]
  rw [integrable_indicator_iff ht]
  apply Integrable.smul_const
  rw [restrict_restrict ht]; rw [inter_eq_left.mpr hts]
  exact .of_integral_ne_zero (fun h => by simp [h] at h'i)

/--
theorem `tendsto_integral_peak_smul_of_integrable_of_tendsto` / 定理 `tendsto_integral_peak_smul_of_integrable_of_tendsto`

English:
theorem tendsto_integral_peak_smul_of_integrable_of_tendsto
  proof: by
  suffices Tendsto (fun i : ι => ∫ x in univ, φ i x • g x ∂μ) l (𝓝 a) by simpa
  exact tendsto_setIntegral_peak_smul_of_integrableOn_of_tendsto MeasurableSet.univ ht (x₀ := x₀)
    (subset_univ _) (by simpa [nhdsWithin_univ]) h't (by simpa)
    (by simpa [← compl_eq_univ_sdiff] using hlφ) hiφ
   

中文:
定理 tendsto_integral_peak_smul_of_integrable_of_tendsto
  证明: by
  suffices Tendsto (fun i : ι => ∫ x in univ, φ i x • g x ∂μ) l (𝓝 a) by simpa
  exact tendsto_setIntegral_peak_smul_of_integrableOn_of_tendsto MeasurableSet.univ ht (x₀ := x₀)
    (subset_univ _) (by simpa [nhdsWithin_univ]) h't (by simpa)
    (by simpa [← compl_eq_univ_sdiff] using hlφ) hiφ
   

Depends on / 依赖: MeasurableSet, MeasurableSet.univ, Tendsto, compl_eq_univ_sdiff, nhdsWithin_univ, subset_univ, tendsto_setIntegral_peak_smul_of_integrableOn_of_tendsto
-/
theorem tendsto_integral_peak_smul_of_integrable_of_tendsto
    {t : Set α} (ht : MeasurableSet t) (h'ts : t in 𝓝 x₀)
    (h't : μ t != ∞) (hnφ : forallᶠ i in l, forall x, 0 <= φ i x)
    (hlφ : forall u : Set α, IsOpen u -> x₀ in u -> TendstoUniformlyOn φ 0 l uᶜ)
    (hiφ : Tendsto (fun i => ∫ x in t, φ i x ∂μ) l (𝓝 1))
    (h'iφ : forallᶠ i in l, AEStronglyMeasurable (φ i) μ)
    (hmg : Integrable g μ) (hcg : Tendsto g (𝓝 x₀) (𝓝 a)) :
    Tendsto (fun i : ι => ∫ x, φ i x • g x ∂μ) l (𝓝 a) := by
  suffices Tendsto (fun i : ι => ∫ x in univ, φ i x • g x ∂μ) l (𝓝 a) by simpa
  exact tendsto_setIntegral_peak_smul_of_integrableOn_of_tendsto MeasurableSet.univ ht (x₀ := x₀)
    (subset_univ _) (by simpa [nhdsWithin_univ]) h't (by simpa)
    (by simpa [← compl_eq_univ_sdiff] using hlφ) hiφ
    (by simpa) (by simpa) (by simpa [nhdsWithin_univ])

/-!
### Peak functions of the form `x ↦ (c x) ^ n / ∫ (c y) ^ n`
-/

/--
theorem `tendsto_setIntegral_pow_smul_of_unique_maximum_of_isCompact_of_measure_nhdsWithin_pos` / 定理 `tendsto_setIntegral_pow_smul_of_unique_maximum_of_isCompact_of_measure_nhdsWithin_pos`

English:
theorem tendsto_setIntegral_pow_smul_of_unique_maximum_of_isCompact_of_measure_nhdsWithin_pos
  proof: by
  /- We apply the general result
    `tendsto_setIntegral_peak_smul_of_integrableOn_of_continuousWithinAt` to the sequence of
    peak functions `φₙ = (c x) ^ n / ∫ (c x) ^ n`. The only nontrivial bit is to check that this
    sequence converges uniformly to zero on any set `s \ u` away from `x₀`

中文:
定理 tendsto_setIntegral_pow_smul_of_unique_maximum_of_isCompact_of_measure_nhdsWithin_pos
  证明: by
  /- We apply the general result
    `tendsto_setIntegral_peak_smul_of_integrableOn_of_continuousWithinAt` to the sequence of
    peak functions `φₙ = (c x) ^ n / ∫ (c x) ^ n`. The only nontrivial bit is to check that this
    sequence converges uniformly to zero on any set `s \ u` away from `x₀`
-/
theorem tendsto_setIntegral_pow_smul_of_unique_maximum_of_isCompact_of_measure_nhdsWithin_pos
    [MetrizableSpace α] [IsLocallyFiniteMeasure μ] (hs : IsCompact s)
    (hμ : forall u, IsOpen u -> x₀ in u -> 0 < μ (u inter s)) {c : α -> Real} (hc : ContinuousOn c s)
    (h'c : forall y in s, y != x₀ -> c y < c x₀) (hnc : forall x in s, 0 <= c x) (hnc₀ : 0 < c x₀) (h₀ : x₀ in s)
    (hmg : IntegrableOn g s μ) (hcg : ContinuousWithinAt g s x₀) :
    Tendsto (fun n : Nat => (∫ x in s, c x ^ n ∂μ)⁻¹ • ∫ x in s, c x ^ n • g x ∂μ)
      atTop (𝓝 (g x₀)) := by
  /- We apply the general result
    `tendsto_setIntegral_peak_smul_of_integrableOn_of_continuousWithinAt` to the sequence of
    peak functions `φₙ = (c x) ^ n / ∫ (c x) ^ n`. The only nontrivial bit is to check that this
    sequence converges uniformly to zero on any set `s \ u` away from `x₀`. By compactness, the
    function `c` is bounded by `t < c x₀` there. Consider `t' ∈ (t, c x₀)`, and a neighborhood `v`
    of `x₀` where `c x ≥ t'`, by continuity. Then `∫ (c x) ^ n` is bounded below by `t' ^ n μ v`.
    It follows that, on `s \ u`, then `φₙ x ≤ t ^ n / (t' ^ n μ v)`,
    which tends (exponentially fast) to zero with `n`. -/
  let φ : Nat -> α -> Real := fun n x => (∫ x in s, c x ^ n ∂μ)⁻¹ * c x ^ n
  have hnφ : forall n, forall x in s, 0 <= φ n x := by
    intro n x hx
    apply mul_nonneg (inv_nonneg.2 _) (pow_nonneg (hnc x hx) _)
    exact setIntegral_nonneg hs.measurableSet fun x hx => pow_nonneg (hnc x hx) _
  have I : forall n, IntegrableOn (fun x => c x ^ n) s μ := fun n =>
    ContinuousOn.integrableOn_compact hs (hc.pow n)
  have J : forall n, 0 <=ᵐ[μ.restrict s] fun x : α => c x ^ n := by
    intro n
    filter_upwards [ae_restrict_mem hs.measurableSet] with x hx
    exact pow_nonneg (hnc x hx) n
  have P : forall n, (0 : Real) < ∫ x in s, c x ^ n ∂μ := by
    intro n
    refine (setIntegral_pos_iff_support_of_nonneg_ae (J n) (I n)).2 ?_
    obtain ⟨u, u_open, x₀_u, hu⟩ : exists u : Set α, IsOpen u ∧ x₀ in u ∧ u inter s subseteq c ⁻¹' Ioi 0 :=
      _root_.continuousOn_iff.1 hc x₀ h₀ (Ioi (0 : Real)) isOpen_Ioi hnc₀
    apply (hμ u u_open x₀_u).trans_le
    exact measure_mono fun x hx => ⟨ne_of_gt (pow_pos (a := c x) (hu hx) _), hx.2⟩
  have hiφ : forall n, ∫ x in s, φ n x ∂μ = 1 := fun n => by
    rw [integral_const_mul]; rw [inv_mul_cancel₀ (P n).ne']
  have A : forall u : Set α, IsOpen u -> x₀ in u -> TendstoUniformlyOn φ 0 atTop (s \ u) := by
    intro u u_open x₀u
    obtain ⟨t, t_pos, tx₀, ht⟩ : exists t, 0 <= t ∧ t < c x₀ ∧ forall x in s \ u, c x <= t := by
      rcases eq_empty_or_nonempty (s \ u) with (h | h)
      · exact
          ⟨0, le_rfl, hnc₀, by simp only [h, mem_empty_iff_false, IsEmpty.forall_iff, imp_true_iff]⟩
      obtain ⟨x, hx, h'x⟩ : exists x in s \ u, forall y in s \ u, c y <= c x :=
        IsCompact.exists_isMaxOn (hs.diff u_open) h (hc.mono sdiff_subset)
      refine ⟨c x, hnc x hx.1, h'c x hx.1 ?_, h'x⟩
      rintro rfl
      exact hx.2 x₀u
    obtain ⟨t', tt', t'x₀⟩ : exists t', t < t' ∧ t' < c x₀ := exists_between tx₀
    have t'_pos : 0 < t' := t_pos.trans_lt tt'
    obtain ⟨v, v_open, x₀_v, hv⟩ : exists v : Set α, IsOpen v ∧ x₀ in v ∧ v inter s subseteq c ⁻¹' Ioi t' :=
      _root_.continuousOn_iff.1 hc x₀ h₀ (Ioi t') isOpen_Ioi t'x₀
    have M : forall n, forall x in s \ u, φ n x <= (μ.real (v inter s))⁻¹ * (t / t') ^ n := by
      intro n x hx
      have B : t' ^ n * μ.real (v inter s) <= ∫ y in s, c y ^ n ∂μ :=
        calc
          t' ^ n * μ.real (v inter s) = ∫ _ in v inter s, t' ^ n ∂μ := by simp [mul_comm]
          _ <= ∫ y in v inter s, c y ^ n ∂μ := by
            apply setIntegral_mono_on _ _ (v_open.measurableSet.inter hs.measurableSet) _
            · refine integrableOn_const (C := t' ^ n) ?_
              exact (lt_of_le_of_lt (measure_mono inter_subset_right) hs.measure_lt_top).ne
            · exact (I n).mono inter_subset_right le_rfl
            · intro x hx
              exact pow_le_pow_left₀ t'_pos.le (hv hx).le _
          _ <= ∫ y in s, c y ^ n ∂μ :=
            setIntegral_mono_set (I n) (J n) (Eventually.of_forall inter_subset_right)
      simp_rw [φ, ← div_eq_inv_mul, div_pow, div_div]
      have := ENNReal.toReal_pos (hμ v v_open x₀_v).ne'
        ((measure_mono inter_subset_right).trans_lt hs.measure_lt_top).ne
      gcongr
      · exact hnc _ hx.1
      · exact ht x hx
    have N :
      Tendsto (fun n => (μ.real (v inter s))⁻¹ * (t / t') ^ n) atTop
        (𝓝 ((μ.real (v inter s))⁻¹ * 0)) := by
      apply Tendsto.mul tendsto_const_nhds _
      apply tendsto_pow_atTop_nhds_zero_of_lt_one (div_nonneg t_pos t'_pos.le)
      exact (div_lt_one t'_pos).2 tt'
    rw [mul_zero] at N
    refine tendstoUniformlyOn_iff.2 fun ε εpos => ?_
    filter_upwards [(tendsto_order.1 N).2 ε εpos] with n hn x hx
    simp only [Pi.zero_apply, dist_zero_left, Real.norm_of_nonneg (hnφ n x hx.1)]
    exact (M n x hx).trans_lt hn
  have : Tendsto (fun i : Nat => ∫ x : α in s, φ i x • g x ∂μ) atTop (𝓝 (g x₀)) := by
    have B : Tendsto (fun i => ∫ (x : α) in s, φ i x ∂μ) atTop (𝓝 1) :=
      tendsto_const_nhds.congr (fun n => (hiφ n).symm)
    have C : forallᶠ (i : Nat) in atTop, AEStronglyMeasurable (fun x => φ i x) (μ.restrict s) := by
      apply Eventually.of_forall (fun n => ((I n).const_mul _).aestronglyMeasurable)
    exact tendsto_setIntegral_peak_smul_of_integrableOn_of_tendsto hs.measurableSet
      hs.measurableSet (Subset.rfl) (self_mem_nhdsWithin)
      hs.measure_lt_top.ne (Eventually.of_forall hnφ) A B C hmg hcg
  convert! this
  simp_rw [φ, ← smul_smul, integral_smul]

/--
theorem `tendsto_setIntegral_pow_smul_of_unique_maximum_of_isCompact_of_integrableOn` / 定理 `tendsto_setIntegral_pow_smul_of_unique_maximum_of_isCompact_of_integrableOn`

English:
theorem tendsto_setIntegral_pow_smul_of_unique_maximum_of_isCompact_of_integrableOn
  proof: by
  have : x₀ in s := by rw [← hs.isClosed.closure_eq]; exact closure_mono interior_subset h₀
  apply
    tendsto_setIntegral_pow_smul_of_unique_maximum_of_isCompact_of_measure_nhdsWithin_pos hs _ hc
      h'c hnc hnc₀ this hmg hcg
  intro u u_open x₀_u
  calc
    0 < μ (u inter interior s) :=
    

中文:
定理 tendsto_setIntegral_pow_smul_of_unique_maximum_of_isCompact_of_integrableOn
  证明: by
  have : x₀ in s := by rw [← hs.isClosed.closure_eq]; exact closure_mono interior_subset h₀
  apply
    tendsto_setIntegral_pow_smul_of_unique_maximum_of_isCompact_of_measure_nhdsWithin_pos hs _ hc
      h'c hnc hnc₀ this hmg hcg
  intro u u_open x₀_u
  calc
    0 < μ (u inter interior s) :=
    

Depends on / 依赖: _root_, _root_.mem_closure_iff, closure_eq, closure_mono, hs.isClosed.closure_eq, interior, interior_subset, isClosed, isOpen_interior, measure_pos, mem_closure_iff, tendsto_setIntegral_pow_smul_of_unique_maximum_of_isCompact_of_measure_nhdsWithin_pos, u_open, u_open.inter
-/
theorem tendsto_setIntegral_pow_smul_of_unique_maximum_of_isCompact_of_integrableOn
    [MetrizableSpace α] [IsLocallyFiniteMeasure μ] [IsOpenPosMeasure μ] (hs : IsCompact s)
    {c : α -> Real} (hc : ContinuousOn c s) (h'c : forall y in s, y != x₀ -> c y < c x₀)
    (hnc : forall x in s, 0 <= c x) (hnc₀ : 0 < c x₀) (h₀ : x₀ in closure (interior s))
    (hmg : IntegrableOn g s μ) (hcg : ContinuousWithinAt g s x₀) :
    Tendsto (fun n : Nat => (∫ x in s, c x ^ n ∂μ)⁻¹ • ∫ x in s, c x ^ n • g x ∂μ) atTop
      (𝓝 (g x₀)) := by
  have : x₀ in s := by rw [← hs.isClosed.closure_eq]; exact closure_mono interior_subset h₀
  apply
    tendsto_setIntegral_pow_smul_of_unique_maximum_of_isCompact_of_measure_nhdsWithin_pos hs _ hc
      h'c hnc hnc₀ this hmg hcg
  intro u u_open x₀_u
  calc
    0 < μ (u inter interior s) :=
      (u_open.inter isOpen_interior).measure_pos μ (_root_.mem_closure_iff.1 h₀ u u_open x₀_u)
    _ <= μ (u inter s) := by gcongr; apply interior_subset

/--
theorem `tendsto_setIntegral_pow_smul_of_unique_maximum_of_isCompact_of_continuousOn` / 定理 `tendsto_setIntegral_pow_smul_of_unique_maximum_of_isCompact_of_continuousOn`

English:
theorem tendsto_setIntegral_pow_smul_of_unique_maximum_of_isCompact_of_continuousOn
  proof: haveI : x₀ in s := by rw [← hs.isClosed.closure_eq]; exact closure_mono interior_subset h₀
  tendsto_setIntegral_pow_smul_of_unique_maximum_of_isCompact_of_integrableOn hs hc h'c hnc hnc₀ h₀
    (hmg.integrableOn_compact hs) (hmg x₀ this)

中文:
定理 tendsto_setIntegral_pow_smul_of_unique_maximum_of_isCompact_of_continuousOn
  证明: haveI : x₀ in s := by rw [← hs.isClosed.closure_eq]; exact closure_mono interior_subset h₀
  tendsto_setIntegral_pow_smul_of_unique_maximum_of_isCompact_of_integrableOn hs hc h'c hnc hnc₀ h₀
    (hmg.integrableOn_compact hs) (hmg x₀ this)

Depends on / 依赖: closure_eq, closure_mono, hmg.integrableOn_compact, hs.isClosed.closure_eq, integrableOn_compact, interior_subset, isClosed, tendsto_setIntegral_pow_smul_of_unique_maximum_of_isCompact_of_integrableOn
-/
theorem tendsto_setIntegral_pow_smul_of_unique_maximum_of_isCompact_of_continuousOn
    [MetrizableSpace α] [IsLocallyFiniteMeasure μ] [IsOpenPosMeasure μ] (hs : IsCompact s)
    {c : α -> Real} (hc : ContinuousOn c s) (h'c : forall y in s, y != x₀ -> c y < c x₀)
    (hnc : forall x in s, 0 <= c x) (hnc₀ : 0 < c x₀) (h₀ : x₀ in closure (interior s))
    (hmg : ContinuousOn g s) :
    Tendsto (fun n : Nat => (∫ x in s, c x ^ n ∂μ)⁻¹ • ∫ x in s, c x ^ n • g x ∂μ) atTop (𝓝 (g x₀)) :=
  haveI : x₀ in s := by rw [← hs.isClosed.closure_eq]; exact closure_mono interior_subset h₀
  tendsto_setIntegral_pow_smul_of_unique_maximum_of_isCompact_of_integrableOn hs hc h'c hnc hnc₀ h₀
    (hmg.integrableOn_compact hs) (hmg x₀ this)

/-!
### Peak functions of the form `x ↦ c ^ dim * φ (c x)`
-/

open Module Bornology

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace Real F] [FiniteDimensional Real F]
  [MeasurableSpace F] [BorelSpace F] {μ : Measure F} [IsAddHaarMeasure μ]

/--
theorem `tendsto_integral_comp_smul_smul_of_integrable` / 定理 `tendsto_integral_comp_smul_smul_of_integrable`

English:
theorem tendsto_integral_comp_smul_smul_of_integrable
  proof: by
  have I : Integrable φ μ := integrable_of_integral_eq_one h'φ
  apply tendsto_integral_peak_smul_of_integrable_of_tendsto (t := closedBall 0 1) (x₀ := 0)
  · exact isClosed_closedBall.measurableSet
  · exact closedBall_mem_nhds _ zero_lt_one
  · exact (isCompact_closedBall 0 1).measure_ne_top
  

中文:
定理 tendsto_integral_comp_smul_smul_of_integrable
  证明: by
  have I : Integrable φ μ := integrable_of_integral_eq_one h'φ
  apply tendsto_integral_peak_smul_of_integrable_of_tendsto (t := closedBall 0 1) (x₀ := 0)
  · exact isClosed_closedBall.measurableSet
  · exact closedBall_mem_nhds _ zero_lt_one
  · exact (isCompact_closedBall 0 1).measure_ne_top
  

Depends on / 依赖: Ici_mem_atTop, Integrable, closedBall, closedBall_mem_nhds, filter_upwards, integrable_of_integral_eq_one, isClosed_closedBall, isClosed_closedBall.measurableSet, isCompact_closedBall, measurableSet, measure_ne_top, mul_nonneg, tendstoUniformlyOn_iff, tendsto_integral_peak_smul_of_integrable_of_tendsto, u_open, zero_lt_one
-/
theorem tendsto_integral_comp_smul_smul_of_integrable
    {φ : F -> Real} (hφ : forall x, 0 <= φ x) (h'φ : ∫ x, φ x ∂μ = 1)
    (h : Tendsto (fun x => ‖x‖ ^ finrank Real F * φ x) (cobounded F) (𝓝 0))
    {g : F -> E} (hg : Integrable g μ) (h'g : ContinuousAt g 0) :
    Tendsto (fun (c : Real) => ∫ x, (c ^ (finrank Real F) * φ (c • x)) • g x ∂μ) atTop (𝓝 (g 0)) := by
  have I : Integrable φ μ := integrable_of_integral_eq_one h'φ
  apply tendsto_integral_peak_smul_of_integrable_of_tendsto (t := closedBall 0 1) (x₀ := 0)
  · exact isClosed_closedBall.measurableSet
  · exact closedBall_mem_nhds _ zero_lt_one
  · exact (isCompact_closedBall 0 1).measure_ne_top
  · filter_upwards [Ici_mem_atTop 0] with c (hc : 0 <= c) x using mul_nonneg (by positivity) (hφ _)
  · intro u u_open hu
    apply tendstoUniformlyOn_iff.2 (fun ε εpos => ?_)
    obtain ⟨δ, δpos, h'u⟩ : exists δ > 0, ball 0 δ subseteq u := Metric.isOpen_iff.1 u_open _ hu
    obtain ⟨M, Mpos, hM⟩ : exists M > 0, forall ⦃x : F⦄, x in (closedBall 0 M)ᶜ ->
        ‖x‖ ^ finrank Real F * φ x < δ ^ finrank Real F * ε := by
      rcases (hasBasis_cobounded_compl_closedBall (0 : F)).eventually_iff.1
        ((tendsto_order.1 h).2 (δ ^ finrank Real F * ε) (by positivity)) with ⟨M, -, hM⟩
      refine ⟨max M 1, zero_lt_one.trans_le (le_max_right _ _), fun x hx => hM ?_⟩
      simp only [mem_compl_iff, mem_closedBall, dist_zero_right, le_max_iff, not_or, not_le] at hx
      simpa using hx.1
    filter_upwards [Ioi_mem_atTop (M / δ)] with c (hc : M / δ < c) x hx
    have cpos : 0 < c := lt_trans (by positivity) hc
    suffices c ^ finrank Real F * φ (c • x) < ε by simpa [abs_of_nonneg (hφ _), abs_of_nonneg cpos.le]
    have hδx : δ <= ‖x‖ := by
      have : x in (ball 0 δ)ᶜ := fun h => hx (h'u h)
      simpa only [mem_compl_iff, mem_ball, dist_zero_right, not_lt]
    suffices δ ^ finrank Real F * (c ^ finrank Real F * φ (c • x)) < δ ^ finrank Real F * ε by
      rwa [mul_lt_mul_iff_of_pos_left (by positivity)] at this
    calc
      δ ^ finrank Real F * (c ^ finrank Real F * φ (c • x))
      _ <= ‖x‖ ^ finrank Real F * (c ^ finrank Real F * φ (c • x)) := by
        gcongr; exact mul_nonneg (by positivity) (hφ _)
      _ = ‖c • x‖ ^ finrank Real F * φ (c • x) := by
        simp [norm_smul, abs_of_pos cpos, mul_pow]; ring
      _ < δ ^ finrank Real F * ε := by
        apply hM
        rw [div_lt_iff₀ δpos] at hc
        simp only [mem_compl_iff, mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
          abs_of_nonneg cpos.le, not_le]
        exact hc.trans_le (by gcongr)
  · have : Tendsto (fun c => ∫ (x : F) in closedBall 0 c, φ x ∂μ) atTop (𝓝 1) := by
      rw [← h'φ]
      exact (aecover_closedBall tendsto_id).integral_tendsto_of_countably_generated I
    apply this.congr'
    filter_upwards [Ioi_mem_atTop 0] with c (hc : 0 < c)
    rw [integral_const_mul]; rw [setIntegral_comp_smul_of_pos _ _ _ hc]; rw [smul_eq_mul]; rw [← mul_assoc]; rw [mul_inv_cancel₀ (by positivity)]; rw [_root_.smul_closedBall _ _ zero_le_one]
    simp [abs_of_nonneg hc.le]
  · filter_upwards [Ioi_mem_atTop 0] with c (hc : 0 < c)
    exact (I.comp_smul hc.ne').aestronglyMeasurable.const_mul _
  · exact hg
  · exact h'g

/--
theorem `tendsto_integral_comp_smul_smul_of_integrable'` / 定理 `tendsto_integral_comp_smul_smul_of_integrable'`

English:
theorem tendsto_integral_comp_smul_smul_of_integrable'
  proof: by
  let f := fun x => g (x₀ - x)
  have If : Integrable f μ := by simpa [f, sub_eq_add_neg] using (hg.comp_add_left x₀).comp_neg
  have : Tendsto (fun (c : Real) => ∫ x, (c ^ (finrank Real F) * φ (c • x)) • f x ∂μ)
      atTop (𝓝 (f 0)) := by
    apply tendsto_integral_comp_smul_smul_of_integrable 

中文:
定理 tendsto_integral_comp_smul_smul_of_integrable'
  证明: by
  let f := fun x => g (x₀ - x)
  have If : Integrable f μ := by simpa [f, sub_eq_add_neg] using (hg.comp_add_left x₀).comp_neg
  have : Tendsto (fun (c : Real) => ∫ x, (c ^ (finrank Real F) * φ (c • x)) • f x ∂μ)
      atTop (𝓝 (f 0)) := by
    apply tendsto_integral_comp_smul_smul_of_integrable 

Depends on / 依赖: A.comp, ContinuousAt, Integrable, Tendsto, comp_add_left, comp_neg, conv_rhs, convert, finrank, fun_prop, hg.comp_add_left, integral_add_left_eq_self, sub_eq_add_neg, sub_zero, tendsto_integral_comp_smul_smul_of_integrable
-/
theorem tendsto_integral_comp_smul_smul_of_integrable'
    {φ : F -> Real} (hφ : forall x, 0 <= φ x) (h'φ : ∫ x, φ x ∂μ = 1)
    (h : Tendsto (fun x => ‖x‖ ^ finrank Real F * φ x) (cobounded F) (𝓝 0))
    {g : F -> E} {x₀ : F} (hg : Integrable g μ) (h'g : ContinuousAt g x₀) :
    Tendsto (fun (c : Real) => ∫ x, (c ^ (finrank Real F) * φ (c • (x₀ - x))) • g x ∂μ)
      atTop (𝓝 (g x₀)) := by
  let f := fun x => g (x₀ - x)
  have If : Integrable f μ := by simpa [f, sub_eq_add_neg] using (hg.comp_add_left x₀).comp_neg
  have : Tendsto (fun (c : Real) => ∫ x, (c ^ (finrank Real F) * φ (c • x)) • f x ∂μ)
      atTop (𝓝 (f 0)) := by
    apply tendsto_integral_comp_smul_smul_of_integrable hφ h'φ h If
    have A : ContinuousAt g (x₀ - 0) := by simpa using h'g
exact A.comp by fun_prop
  simp only [f, sub_zero] at this
  convert! this using 2 with c
  conv_rhs => rw [← integral_add_left_eq_self x₀ (μ := μ)
    (f := fun x => (c ^ finrank Real F * φ (c • x)) • g (x₀ - x)), ← integral_neg_eq_self]
  simp [sub_eq_add_neg]
