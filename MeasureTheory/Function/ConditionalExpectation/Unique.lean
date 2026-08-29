/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.Function.AEEqOfIntegral
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.AEMeasurable

/-!
# Uniqueness of the conditional expectation

Two Lp functions `f, g` which are almost everywhere strongly measurable with respect to a σ-algebra
`m` and verify `∫ x in s, f x ∂μ = ∫ x in s, g x ∂μ` for all `m`-measurable sets `s` are equal
almost everywhere. This proves the uniqueness of the conditional expectation, which is not yet
defined in this file but is introduced in
`Mathlib/MeasureTheory/Function/ConditionalExpectation/Basic.lean`.

## Main statements

* `Lp.ae_eq_of_forall_setIntegral_eq'`: two `Lp` functions verifying the equality of integrals
  defining the conditional expectation are equal.
* `ae_eq_of_forall_setIntegral_eq_of_sigma_finite'`: two functions verifying the equality of
  integrals defining the conditional expectation are equal almost everywhere.
  Requires `[SigmaFinite (μ.trim hm)]`.

-/

public section


open scoped ENNReal MeasureTheory

namespace MeasureTheory

variable {α E' F' 𝕜 : Type*} {p : Real>=0∞} {m m0 : MeasurableSpace α} {μ : Measure α} [RCLike 𝕜]
  -- 𝕜 for ℝ or ℂ
  -- E' for an inner product space on which we compute integrals
  [NormedAddCommGroup E']
  [InnerProductSpace 𝕜 E'] [CompleteSpace E'] [NormedSpace Real E']
  -- F' for integrals on a Lp submodule
  [NormedAddCommGroup F']
  [NormedSpace Real F'] [CompleteSpace F']

section UniquenessOfConditionalExpectation


/--
theorem `lpMeas.ae_eq_zero_of_forall_setIntegral_eq_zero` / 定理 `lpMeas.ae_eq_zero_of_forall_setIntegral_eq_zero`

English:
theorem lpMeas.ae_eq_zero_of_forall_setIntegral_eq_zero
  statement: (hm : m <= m0) (f : lpMeas E' 𝕜 m p μ)
  proof: by
  obtain ⟨g, hg_sm, hfg⟩ := lpMeas.ae_fin_strongly_measurable' hm f hp_ne_zero hp_ne_top
  refine hfg.trans ?_
  refine ae_eq_zero_of_forall_setIntegral_eq_of_finStronglyMeasurable_trim hm ?_ ?_ hg_sm
  · intro s hs hμs
    have hfg_restrict : f =ᵐ[μ.restrict s] g := ae_restrict_of_ae hfg
    rw [IntegrableOn]; rw [integrable_congr hfg_restrict.symm]
    exact hf_int_finite s hs hμs
  · intro s hs hμs
    have hfg_restrict : f =ᵐ[μ.restrict s] g := ae_restrict_of_ae hfg
    rw [integral_congr_ae hfg_restrict.symm]
    exact hf_zero s hs hμs

中文:
定理 lpMeas.ae_eq_zero_of_对任意_set整数egral_eq_zero
  结论: (hm : m <= m0) (f : lpMeas E' 𝕜 m p μ)
  证明: by
  obtain ⟨g, hg_sm, hfg⟩ := lpMeas.ae_fin_strongly_measurable' hm f hp_ne_zero hp_ne_top
  refine hfg.trans ?_
  refine ae_eq_zero_of_forall_setIntegral_eq_of_finStronglyMeasurable_trim hm ?_ ?_ hg_sm
  · intro s hs hμs
    have hfg_restrict : f =ᵐ[μ.restrict s] g := ae_restrict_of_ae hfg
    rw [IntegrableOn]; rw [integrable_congr hfg_restrict.symm]
    exact hf_int_finite s hs hμs
  · intro s hs hμs
    have hfg_restrict : f =ᵐ[μ.restrict s] g := ae_restrict_of_ae hfg
    rw [integral_congr_ae hfg_restrict.symm]
    exact hf_zero s hs hμs

Depends on / 依赖: IntegrableOn, ae_eq_zero_of_forall_setIntegral_eq_of_finStronglyMeasurable_trim, ae_fin_strongly_measurable, ae_restrict_of_ae, hf_int_finite, hfg.trans, hfg_restrict, hfg_restrict.symm, hg_sm, hp_ne_top, hp_ne_zero, integrable_congr, integral_congr_ae, lpMeas, lpMeas.ae_fin_strongly_measurable, restrict
-/
theorem lpMeas.ae_eq_zero_of_forall_setIntegral_eq_zero (hm : m <= m0) (f : lpMeas E' 𝕜 m p μ)
    (hp_ne_zero : p != 0) (hp_ne_top : p != ∞)
    (hf_int_finite : forall s, MeasurableSet[m] s -> μ s < ∞ -> IntegrableOn (f : Lp E' p μ) s μ)
    (hf_zero : forall s : Set α, MeasurableSet[m] s -> μ s < ∞ -> ∫ x in s, (f : Lp E' p μ) x ∂μ = 0) :
    f =ᵐ[μ] (0 : α -> E') := by
  obtain ⟨g, hg_sm, hfg⟩ := lpMeas.ae_fin_strongly_measurable' hm f hp_ne_zero hp_ne_top
  refine hfg.trans ?_
  refine ae_eq_zero_of_forall_setIntegral_eq_of_finStronglyMeasurable_trim hm ?_ ?_ hg_sm
  · intro s hs hμs
    have hfg_restrict : f =ᵐ[μ.restrict s] g := ae_restrict_of_ae hfg
    rw [IntegrableOn]; rw [integrable_congr hfg_restrict.symm]
    exact hf_int_finite s hs hμs
  · intro s hs hμs
    have hfg_restrict : f =ᵐ[μ.restrict s] g := ae_restrict_of_ae hfg
    rw [integral_congr_ae hfg_restrict.symm]
    exact hf_zero s hs hμs

variable (𝕜)

include 𝕜 in
/--
theorem `Lp.ae_eq_zero_of_forall_setIntegral_eq_zero'` / 定理 `Lp.ae_eq_zero_of_forall_setIntegral_eq_zero'`

English:
theorem Lp.ae_eq_zero_of_forall_setIntegral_eq_zero'
  statement: (hm : m <= m0) (f : Lp E' p μ)
  proof: by
  let f_meas : lpMeas E' 𝕜 m p μ := ⟨f, hf_meas⟩
  have hf_f_meas : f =ᵐ[μ] f_meas := by simp [f_meas]
  refine hf_f_meas.trans ?_
  exact lpMeas.ae_eq_zero_of_forall_setIntegral_eq_zero
    hm f_meas hp_ne_zero hp_ne_top hf_int_finite hf_zero

include 𝕜 in

中文:
定理 Lp.ae_eq_zero_of_对任意_set整数egral_eq_zero'
  结论: (hm : m <= m0) (f : Lp E' p μ)
  证明: by
  let f_meas : lpMeas E' 𝕜 m p μ := ⟨f, hf_meas⟩
  have hf_f_meas : f =ᵐ[μ] f_meas := by simp [f_meas]
  refine hf_f_meas.trans ?_
  exact lpMeas.ae_eq_zero_of_forall_setIntegral_eq_zero
    hm f_meas hp_ne_zero hp_ne_top hf_int_finite hf_zero

include 𝕜 in

Depends on / 依赖: ae_eq_zero_of_forall_setIntegral_eq_zero, f_meas, hf_f_meas, hf_f_meas.trans, hf_int_finite, hf_meas, hf_zero, hp_ne_top, hp_ne_zero, lpMeas, lpMeas.ae_eq_zero_of_forall_setIntegral_eq_zero
-/
theorem Lp.ae_eq_zero_of_forall_setIntegral_eq_zero' (hm : m <= m0) (f : Lp E' p μ)
    (hp_ne_zero : p != 0) (hp_ne_top : p != ∞)
    (hf_int_finite : forall s, MeasurableSet[m] s -> μ s < ∞ -> IntegrableOn f s μ)
    (hf_zero : forall s : Set α, MeasurableSet[m] s -> μ s < ∞ -> ∫ x in s, f x ∂μ = 0)
    (hf_meas : AEStronglyMeasurable[m] f μ) : f =ᵐ[μ] 0 := by
  let f_meas : lpMeas E' 𝕜 m p μ := ⟨f, hf_meas⟩
  have hf_f_meas : f =ᵐ[μ] f_meas := by simp [f_meas]
  refine hf_f_meas.trans ?_
  exact lpMeas.ae_eq_zero_of_forall_setIntegral_eq_zero
    hm f_meas hp_ne_zero hp_ne_top hf_int_finite hf_zero

include 𝕜 in
/--
theorem `Lp.ae_eq_of_forall_setIntegral_eq'` / 定理 `Lp.ae_eq_of_forall_setIntegral_eq'`

English:
theorem Lp.ae_eq_of_forall_setIntegral_eq'
  statement: (hm : m <= m0) (f g : Lp E' p μ) (hp_ne_zero : p != 0)
  proof: by
  suffices h_sub : ⇑(f - g) =ᵐ[μ] 0 by
    rw [← sub_ae_eq_zero]; exact (Lp.coeFn_sub f g).symm.trans h_sub
  have hfg' : forall s : Set α, MeasurableSet[m] s -> μ s < ∞ -> (∫ x in s, (f - g) x ∂μ) = 0 := by
    intro s hs hμs
    rw [integral_congr_ae (ae_restrict_of_ae (Lp.coeFn_sub f g))]
    rw [integral_sub' (hf_int_finite s hs hμs) (hg_int_finite s hs hμs)]
    exact sub_eq_zero.mpr (hfg s hs hμs)
  have hfg_int : forall s, MeasurableSet[m] s -> μ s < ∞ -> IntegrableOn (⇑(f - g)) s μ := by
    intro s hs hμs
    rw [IntegrableOn]; rw [integrable_congr (ae_restrict_of_ae (Lp.coeFn_sub f g))]
    exact (hf_int_finite s hs hμs).sub (hg_int_finite s hs hμs)
  exact Lp.ae_eq_zero_of_forall_setIntegral_eq_zero' 𝕜 hm (f - g) hp_ne_zero hp_ne_top hfg_int hfg'
 (hf_meas.sub hg_meas).congr (Lp.coeFn_sub f g).symm

中文:
定理 Lp.ae_eq_of_对任意_set整数egral_eq'
  结论: (hm : m <= m0) (f g : Lp E' p μ) (hp_ne_zero : p != 0)
  证明: by
  suffices h_sub : ⇑(f - g) =ᵐ[μ] 0 by
    rw [← sub_ae_eq_zero]; exact (Lp.coeFn_sub f g).symm.trans h_sub
  have hfg' : forall s : Set α, MeasurableSet[m] s -> μ s < ∞ -> (∫ x in s, (f - g) x ∂μ) = 0 := by
    intro s hs hμs
    rw [integral_congr_ae (ae_restrict_of_ae (Lp.coeFn_sub f g))]
    rw [integral_sub' (hf_int_finite s hs hμs) (hg_int_finite s hs hμs)]
    exact sub_eq_zero.mpr (hfg s hs hμs)
  have hfg_int : forall s, MeasurableSet[m] s -> μ s < ∞ -> IntegrableOn (⇑(f - g)) s μ := by
    intro s hs hμs
    rw [IntegrableOn]; rw [integrable_congr (ae_restrict_of_ae (Lp.coeFn_sub f g))]
    exact (hf_int_finite s hs hμs).sub (hg_int_finite s hs hμs)
  exact Lp.ae_eq_zero_of_forall_setIntegral_eq_zero' 𝕜 hm (f - g) hp_ne_zero hp_ne_top hfg_int hfg'
 (hf_meas.sub hg_meas).congr (Lp.coeFn_sub f g).symm

Depends on / 依赖: IntegrableOn, Lp.coeFn_sub, MeasurableSet, ae_restrict_of_ae, coeFn_sub, h_sub, hf_int_finite, hfg_int, hg_int_finite, integral_congr_ae, integral_sub, sub_ae_eq_zero, sub_eq_zero, sub_eq_zero.mpr, symm.trans
-/
theorem Lp.ae_eq_of_forall_setIntegral_eq' (hm : m <= m0) (f g : Lp E' p μ) (hp_ne_zero : p != 0)
    (hp_ne_top : p != ∞) (hf_int_finite : forall s, MeasurableSet[m] s -> μ s < ∞ -> IntegrableOn f s μ)
    (hg_int_finite : forall s, MeasurableSet[m] s -> μ s < ∞ -> IntegrableOn g s μ)
    (hfg : forall s : Set α, MeasurableSet[m] s -> μ s < ∞ -> ∫ x in s, f x ∂μ = ∫ x in s, g x ∂μ)
    (hf_meas : AEStronglyMeasurable[m] f μ) (hg_meas : AEStronglyMeasurable[m] g μ) :
    f =ᵐ[μ] g := by
  suffices h_sub : ⇑(f - g) =ᵐ[μ] 0 by
    rw [← sub_ae_eq_zero]; exact (Lp.coeFn_sub f g).symm.trans h_sub
  have hfg' : forall s : Set α, MeasurableSet[m] s -> μ s < ∞ -> (∫ x in s, (f - g) x ∂μ) = 0 := by
    intro s hs hμs
    rw [integral_congr_ae (ae_restrict_of_ae (Lp.coeFn_sub f g))]
    rw [integral_sub' (hf_int_finite s hs hμs) (hg_int_finite s hs hμs)]
    exact sub_eq_zero.mpr (hfg s hs hμs)
  have hfg_int : forall s, MeasurableSet[m] s -> μ s < ∞ -> IntegrableOn (⇑(f - g)) s μ := by
    intro s hs hμs
    rw [IntegrableOn]; rw [integrable_congr (ae_restrict_of_ae (Lp.coeFn_sub f g))]
    exact (hf_int_finite s hs hμs).sub (hg_int_finite s hs hμs)
  exact Lp.ae_eq_zero_of_forall_setIntegral_eq_zero' 𝕜 hm (f - g) hp_ne_zero hp_ne_top hfg_int hfg'
 (hf_meas.sub hg_meas).congr (Lp.coeFn_sub f g).symm

variable {𝕜}

/--
theorem `ae_eq_of_forall_setIntegral_eq_of_sigmaFinite'` / 定理 `ae_eq_of_forall_setIntegral_eq_of_sigmaFinite'`

English:
theorem ae_eq_of_forall_setIntegral_eq_of_sigmaFinite'
  statement: (hm : m <= m0) [SigmaFinite (μ.trim hm)]
  proof: by
  rw [← ae_eq_trim_iff_of_aestronglyMeasurable hm hfm hgm]
  have hf_mk_int_finite (s) :
      MeasurableSet[m] s -> μ.trim hm s < ∞ -> @IntegrableOn _ _ m _ _ (hfm.mk f) s (μ.trim hm) := by
    intro hs hμs
    rw [trim_measurableSet_eq hm hs] at hμs
    rw [IntegrableOn]; rw [restrict_trim hm _ hs]
    refine Integrable.trim hm ?_ hfm.stronglyMeasurable_mk
    exact Integrable.congr (hf_int_finite s hs hμs) (ae_restrict_of_ae hfm.ae_eq_mk)
  have hg_mk_int_finite (s) :
      MeasurableSet[m] s -> μ.trim hm s < ∞ -> @IntegrableOn _ _ m _ _ (hgm.mk g) s (μ.trim hm) := by
    intro hs hμs
    rw [trim_measurableSet_eq hm hs] at hμs
    rw [IntegrableOn]; rw [restrict_trim hm _ hs]
    refine Integrable.trim hm ?_ hgm.stronglyMeasurable_mk
    exact Integrable.congr (hg_int_finite s hs hμs) (ae_restrict_of_ae hgm.ae_eq_mk)
  have hfg_mk_eq :
    forall s : Set α,
      MeasurableSet[m] s ->
        μ.trim hm s < ∞ -> ∫ x in s, hfm.mk f x ∂μ.trim hm = ∫ x in s, hgm.mk g x ∂μ.trim hm := by
    intro s hs hμs
    rw [trim_measurableSet_eq hm hs] at hμs
    rw [restrict_trim hm _ hs]; rw [← integral_trim hm hfm.stronglyMeasurable_mk]; rw [←
      integral_trim hm hgm.stronglyMeasurable_mk]; rw [integral_congr_ae (ae_restrict_of_ae hfm.ae_eq_mk.symm)]; rw [integral_congr_ae (ae_restrict_of_ae hgm.ae_eq_mk.symm)]
    exact hfg_eq s hs hμs
  exact ae_eq_of_forall_setIntegral_eq_of_sigmaFinite hf_mk_int_finite hg_mk_int_finite hfg_mk_eq

中文:
定理 ae_eq_of_对任意_set整数egral_eq_of_sigmaFinite'
  结论: (hm : m <= m0) [σ有限 (μ.trim hm)]
  证明: by
  rw [← ae_eq_trim_iff_of_aestronglyMeasurable hm hfm hgm]
  have hf_mk_int_finite (s) :
      MeasurableSet[m] s -> μ.trim hm s < ∞ -> @IntegrableOn _ _ m _ _ (hfm.mk f) s (μ.trim hm) := by
    intro hs hμs
    rw [trim_measurableSet_eq hm hs] at hμs
    rw [IntegrableOn]; rw [restrict_trim hm _ hs]
    refine Integrable.trim hm ?_ hfm.stronglyMeasurable_mk
    exact Integrable.congr (hf_int_finite s hs hμs) (ae_restrict_of_ae hfm.ae_eq_mk)
  have hg_mk_int_finite (s) :
      MeasurableSet[m] s -> μ.trim hm s < ∞ -> @IntegrableOn _ _ m _ _ (hgm.mk g) s (μ.trim hm) := by
    intro hs hμs
    rw [trim_measurableSet_eq hm hs] at hμs
    rw [IntegrableOn]; rw [restrict_trim hm _ hs]
    refine Integrable.trim hm ?_ hgm.stronglyMeasurable_mk
    exact Integrable.congr (hg_int_finite s hs hμs) (ae_restrict_of_ae hgm.ae_eq_mk)
  have hfg_mk_eq :
    forall s : Set α,
      MeasurableSet[m] s ->
        μ.trim hm s < ∞ -> ∫ x in s, hfm.mk f x ∂μ.trim hm = ∫ x in s, hgm.mk g x ∂μ.trim hm := by
    intro s hs hμs
    rw [trim_measurableSet_eq hm hs] at hμs
    rw [restrict_trim hm _ hs]; rw [← integral_trim hm hfm.stronglyMeasurable_mk]; rw [←
      integral_trim hm hgm.stronglyMeasurable_mk]; rw [integral_congr_ae (ae_restrict_of_ae hfm.ae_eq_mk.symm)]; rw [integral_congr_ae (ae_restrict_of_ae hgm.ae_eq_mk.symm)]
    exact hfg_eq s hs hμs
  exact ae_eq_of_forall_setIntegral_eq_of_sigmaFinite hf_mk_int_finite hg_mk_int_finite hfg_mk_eq

Depends on / 依赖: Integrable, Integrable.congr, Integrable.trim, IntegrableO, IntegrableOn, MeasurableSet, ae_eq_mk, ae_eq_trim_iff_of_aestronglyMeasurable, ae_restrict_of_ae, hf_int_finite, hf_mk_int_finite, hfm.ae_eq_mk, hfm.mk, hfm.stronglyMeasurable_mk, hg_mk_int_finite, restrict_trim, stronglyMeasurable_mk, trim_measurableSet_eq
-/
theorem ae_eq_of_forall_setIntegral_eq_of_sigmaFinite' (hm : m <= m0) [SigmaFinite (μ.trim hm)]
    {f g : α -> F'} (hf_int_finite : forall s, MeasurableSet[m] s -> μ s < ∞ -> IntegrableOn f s μ)
    (hg_int_finite : forall s, MeasurableSet[m] s -> μ s < ∞ -> IntegrableOn g s μ)
    (hfg_eq : forall s : Set α, MeasurableSet[m] s -> μ s < ∞ -> ∫ x in s, f x ∂μ = ∫ x in s, g x ∂μ)
    (hfm : AEStronglyMeasurable[m] f μ) (hgm : AEStronglyMeasurable[m] g μ) : f =ᵐ[μ] g := by
  rw [← ae_eq_trim_iff_of_aestronglyMeasurable hm hfm hgm]
  have hf_mk_int_finite (s) :
      MeasurableSet[m] s -> μ.trim hm s < ∞ -> @IntegrableOn _ _ m _ _ (hfm.mk f) s (μ.trim hm) := by
    intro hs hμs
    rw [trim_measurableSet_eq hm hs] at hμs
    rw [IntegrableOn]; rw [restrict_trim hm _ hs]
    refine Integrable.trim hm ?_ hfm.stronglyMeasurable_mk
    exact Integrable.congr (hf_int_finite s hs hμs) (ae_restrict_of_ae hfm.ae_eq_mk)
  have hg_mk_int_finite (s) :
      MeasurableSet[m] s -> μ.trim hm s < ∞ -> @IntegrableOn _ _ m _ _ (hgm.mk g) s (μ.trim hm) := by
    intro hs hμs
    rw [trim_measurableSet_eq hm hs] at hμs
    rw [IntegrableOn]; rw [restrict_trim hm _ hs]
    refine Integrable.trim hm ?_ hgm.stronglyMeasurable_mk
    exact Integrable.congr (hg_int_finite s hs hμs) (ae_restrict_of_ae hgm.ae_eq_mk)
  have hfg_mk_eq :
    forall s : Set α,
      MeasurableSet[m] s ->
        μ.trim hm s < ∞ -> ∫ x in s, hfm.mk f x ∂μ.trim hm = ∫ x in s, hgm.mk g x ∂μ.trim hm := by
    intro s hs hμs
    rw [trim_measurableSet_eq hm hs] at hμs
    rw [restrict_trim hm _ hs]; rw [← integral_trim hm hfm.stronglyMeasurable_mk]; rw [←
      integral_trim hm hgm.stronglyMeasurable_mk]; rw [integral_congr_ae (ae_restrict_of_ae hfm.ae_eq_mk.symm)]; rw [integral_congr_ae (ae_restrict_of_ae hgm.ae_eq_mk.symm)]
    exact hfg_eq s hs hμs
  exact ae_eq_of_forall_setIntegral_eq_of_sigmaFinite hf_mk_int_finite hg_mk_int_finite hfg_mk_eq

end UniquenessOfConditionalExpectation

section IntegralNormLE

variable {s : Set α}

/--
theorem `integral_norm_le_of_forall_fin_meas_integral_eq` / 定理 `integral_norm_le_of_forall_fin_meas_integral_eq`

English:
theorem integral_norm_le_of_forall_fin_meas_integral_eq
  statement: (hm : m <= m0) {f g : α -> Real}
  proof: by
  rw [integral_norm_eq_pos_sub_neg hgi]; rw [integral_norm_eq_pos_sub_neg hfi]
  have h_meas_nonneg_g : MeasurableSet[m] {x | 0 <= g x} :=
    (@stronglyMeasurable_const _ _ m _ _).measurableSet_le hg
  have h_meas_nonneg_f : MeasurableSet {x | 0 <= f x} :=
    stronglyMeasurable_const.measurableSet_le hf
  have h_meas_nonpos_g : MeasurableSet[m] {x | g x <= 0} :=
    hg.measurableSet_le (@stronglyMeasurable_const _ _ m _ _)
  have h_meas_nonpos_f : MeasurableSet {x | f x <= 0} :=
    hf.measurableSet_le stronglyMeasurable_const
  refine sub_le_sub ?_ ?_
  · rw [Measure.restrict_restrict (hm _ h_meas_nonneg_g), Measure.restrict_restrict h_meas_nonneg_f,
      hgf _ (@MeasurableSet.inter α m _ _ h_meas_nonneg_g hs)
        ((measure_mono Set.inter_subset_right).trans_lt (lt_top_iff_ne_top.mpr hμs)),
      ← Measure.restrict_restrict (hm _ h_meas_nonneg_g), ←
      Measure.restrict_restrict h_meas_nonneg_f]
    exact setIntegral_le_nonneg (hm _ h_meas_nonneg_g) hf hfi
  · rw [Measure.restrict_restrict (hm _ h_meas_nonpos_g), Measure.restrict_restrict h_meas_nonpos_f,
      hgf _ (@MeasurableSet.inter α m _ _ h_meas_nonpos_g hs)
        ((measure_mono Set.inter_subset_right).trans_lt (lt_top_iff_ne_top.mpr hμs)),
      ← Measure.restrict_restrict (hm _ h_meas_nonpos_g), ←
      Measure.restrict_restrict h_meas_nonpos_f]
    exact setIntegral_nonpos_le (hm _ h_meas_nonpos_g) hf hfi

中文:
定理 integral_norm_le_of_对任意_fin_meas_integral_eq
  结论: (hm : m <= m0) {f g : α -> 实数}
  证明: by
  rw [integral_norm_eq_pos_sub_neg hgi]; rw [integral_norm_eq_pos_sub_neg hfi]
  have h_meas_nonneg_g : MeasurableSet[m] {x | 0 <= g x} :=
    (@stronglyMeasurable_const _ _ m _ _).measurableSet_le hg
  have h_meas_nonneg_f : MeasurableSet {x | 0 <= f x} :=
    stronglyMeasurable_const.measurableSet_le hf
  have h_meas_nonpos_g : MeasurableSet[m] {x | g x <= 0} :=
    hg.measurableSet_le (@stronglyMeasurable_const _ _ m _ _)
  have h_meas_nonpos_f : MeasurableSet {x | f x <= 0} :=
    hf.measurableSet_le stronglyMeasurable_const
  refine sub_le_sub ?_ ?_
  · rw [Measure.restrict_restrict (hm _ h_meas_nonneg_g), Measure.restrict_restrict h_meas_nonneg_f,
      hgf _ (@MeasurableSet.inter α m _ _ h_meas_nonneg_g hs)
        ((measure_mono Set.inter_subset_right).trans_lt (lt_top_iff_ne_top.mpr hμs)),
      ← Measure.restrict_restrict (hm _ h_meas_nonneg_g), ←
      Measure.restrict_restrict h_meas_nonneg_f]
    exact setIntegral_le_nonneg (hm _ h_meas_nonneg_g) hf hfi
  · rw [Measure.restrict_restrict (hm _ h_meas_nonpos_g), Measure.restrict_restrict h_meas_nonpos_f,
      hgf _ (@MeasurableSet.inter α m _ _ h_meas_nonpos_g hs)
        ((measure_mono Set.inter_subset_right).trans_lt (lt_top_iff_ne_top.mpr hμs)),
      ← Measure.restrict_restrict (hm _ h_meas_nonpos_g), ←
      Measure.restrict_restrict h_meas_nonpos_f]
    exact setIntegral_nonpos_le (hm _ h_meas_nonpos_g) hf hfi

Depends on / 依赖: MeasurableSet, h_meas_nonneg_f, h_meas_nonneg_g, h_meas_nonpos_f, h_meas_nonpos_g, hf.measurableSet_le, hg.measurableSet_le, integral_norm_eq_pos_sub_neg, measurableSet_le, stronglyMeasu, stronglyMeasurable_const, stronglyMeasurable_const.measurableSet_le
-/
theorem integral_norm_le_of_forall_fin_meas_integral_eq (hm : m <= m0) {f g : α -> Real}
    (hf : StronglyMeasurable f) (hfi : IntegrableOn f s μ) (hg : StronglyMeasurable[m] g)
    (hgi : IntegrableOn g s μ)
    (hgf : forall t, MeasurableSet[m] t -> μ t < ∞ -> ∫ x in t, g x ∂μ = ∫ x in t, f x ∂μ)
    (hs : MeasurableSet[m] s) (hμs : μ s != ∞) : (∫ x in s, ‖g x‖ ∂μ) <= ∫ x in s, ‖f x‖ ∂μ := by
  rw [integral_norm_eq_pos_sub_neg hgi]; rw [integral_norm_eq_pos_sub_neg hfi]
  have h_meas_nonneg_g : MeasurableSet[m] {x | 0 <= g x} :=
    (@stronglyMeasurable_const _ _ m _ _).measurableSet_le hg
  have h_meas_nonneg_f : MeasurableSet {x | 0 <= f x} :=
    stronglyMeasurable_const.measurableSet_le hf
  have h_meas_nonpos_g : MeasurableSet[m] {x | g x <= 0} :=
    hg.measurableSet_le (@stronglyMeasurable_const _ _ m _ _)
  have h_meas_nonpos_f : MeasurableSet {x | f x <= 0} :=
    hf.measurableSet_le stronglyMeasurable_const
  refine sub_le_sub ?_ ?_
  · rw [Measure.restrict_restrict (hm _ h_meas_nonneg_g), Measure.restrict_restrict h_meas_nonneg_f,
      hgf _ (@MeasurableSet.inter α m _ _ h_meas_nonneg_g hs)
        ((measure_mono Set.inter_subset_right).trans_lt (lt_top_iff_ne_top.mpr hμs)),
      ← Measure.restrict_restrict (hm _ h_meas_nonneg_g), ←
      Measure.restrict_restrict h_meas_nonneg_f]
    exact setIntegral_le_nonneg (hm _ h_meas_nonneg_g) hf hfi
  · rw [Measure.restrict_restrict (hm _ h_meas_nonpos_g), Measure.restrict_restrict h_meas_nonpos_f,
      hgf _ (@MeasurableSet.inter α m _ _ h_meas_nonpos_g hs)
        ((measure_mono Set.inter_subset_right).trans_lt (lt_top_iff_ne_top.mpr hμs)),
      ← Measure.restrict_restrict (hm _ h_meas_nonpos_g), ←
      Measure.restrict_restrict h_meas_nonpos_f]
    exact setIntegral_nonpos_le (hm _ h_meas_nonpos_g) hf hfi

/--
theorem `lintegral_enorm_le_of_forall_fin_meas_integral_eq` / 定理 `lintegral_enorm_le_of_forall_fin_meas_integral_eq`

English:
theorem lintegral_enorm_le_of_forall_fin_meas_integral_eq
  statement: (hm : m <= m0) {f g : α -> Real}
  proof: by
  rw [← ofReal_integral_norm_eq_lintegral_enorm hfi]; rw [←
    ofReal_integral_norm_eq_lintegral_enorm hgi]; rw [ENNReal.ofReal_le_ofReal_iff]
  · exact integral_norm_le_of_forall_fin_meas_integral_eq hm hf hfi hg hgi hgf hs hμs
  · positivity

中文:
定理 lintegral_enorm_le_of_对任意_fin_meas_integral_eq
  结论: (hm : m <= m0) {f g : α -> 实数}
  证明: by
  rw [← ofReal_integral_norm_eq_lintegral_enorm hfi]; rw [←
    ofReal_integral_norm_eq_lintegral_enorm hgi]; rw [ENNReal.ofReal_le_ofReal_iff]
  · exact integral_norm_le_of_forall_fin_meas_integral_eq hm hf hfi hg hgi hgf hs hμs
  · positivity

Depends on / 依赖: ENNReal, ENNReal.ofReal_le_ofReal_iff, integral_norm_le_of_forall_fin_meas_integral_eq, ofReal_integral_norm_eq_lintegral_enorm, ofReal_le_ofReal_iff
-/
theorem lintegral_enorm_le_of_forall_fin_meas_integral_eq (hm : m <= m0) {f g : α -> Real}
    (hf : StronglyMeasurable f) (hfi : IntegrableOn f s μ) (hg : StronglyMeasurable[m] g)
    (hgi : IntegrableOn g s μ)
    (hgf : forall t, MeasurableSet[m] t -> μ t < ∞ -> ∫ x in t, g x ∂μ = ∫ x in t, f x ∂μ)
    (hs : MeasurableSet[m] s) (hμs : μ s != ∞) : (∫⁻ x in s, ‖g x‖ₑ ∂μ) <= ∫⁻ x in s, ‖f x‖ₑ ∂μ := by
  rw [← ofReal_integral_norm_eq_lintegral_enorm hfi]; rw [←
    ofReal_integral_norm_eq_lintegral_enorm hgi]; rw [ENNReal.ofReal_le_ofReal_iff]
  · exact integral_norm_le_of_forall_fin_meas_integral_eq hm hf hfi hg hgi hgf hs hμs
  · positivity

end IntegralNormLE

end MeasureTheory
