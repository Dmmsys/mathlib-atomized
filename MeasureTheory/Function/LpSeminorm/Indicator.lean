/-
Copyright (c) 2020 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Sébastien Gouëzel
-/
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.Analysis.Normed.Group.Indicator
public import Mathlib.MeasureTheory.Integral.Lebesgue.Sub

/-!
# ℒp seminorms and indicator functions
-/

public section
noncomputable section

open TopologicalSpace MeasureTheory Filter

open scoped NNReal ENNReal Topology ComplexConjugate

variable {α ε ε' E F G : Type*} {m m0 : MeasurableSpace α} {p : Real>=0∞} {q : Real} {μ ν : Measure α}
  [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedAddCommGroup G] [ENorm ε] [ENorm ε']

namespace MeasureTheory

section Lp

variable {f : α -> F}

section Indicator

variable {ε : Type*} [TopologicalSpace ε] [ESeminormedAddMonoid ε]
  {c : ε} {hf : AEStronglyMeasurable f μ} {s : Set α}
  {ε' : Type*} [TopologicalSpace ε'] [ContinuousENorm ε']

/--
lemma `eLpNorm_indicator_eq_eLpNorm_restrict` / 引理 `eLpNorm_indicator_eq_eLpNorm_restrict`

English:
lemma eLpNorm_indicator_eq_eLpNorm_restrict
  given: {f : α -> ε} {s : Set α} (hs : MeasurableSet s)
  proof: by
  by_cases hp_zero : p = 0
  · simp only [hp_zero, eLpNorm_exponent_zero]
  by_cases hp_top : p = ∞
  · simp_rw [hp_top, eLpNorm_exponent_top, eLpNormEssSup_eq_essSup_enorm,
       enorm_indicator_eq_indicator_enorm, ENNReal.essSup_indicator_eq_essSup_restrict hs]
  simp_rw [eLpNorm_eq_lintegral_

中文:
引理 eLpNorm_indicator_eq_eLpNorm_restrict
  条件: {f : α -> ε} {s : 集合 α} (hs : 可测集 s)
  证明: by
  by_cases hp_zero : p = 0
  · simp only [hp_zero, eLpNorm_exponent_zero]
  by_cases hp_top : p = ∞
  · simp_rw [hp_top, eLpNorm_exponent_top, eLpNormEssSup_eq_essSup_enorm,
       enorm_indicator_eq_indicator_enorm, ENNReal.essSup_indicator_eq_essSup_restrict hs]
  simp_rw [eLpNorm_eq_lintegral_

Depends on / 依赖: ENNReal, ENNReal.essSup_indicator_eq_essSup_restrict, Function, Function.comp_def, Set.indicator_comp_of_z, comp_def, eLpNormEssSup_eq_essSup_enorm, eLpNorm_eq_lintegral_rpow_enorm_toReal, eLpNorm_exponent_top, eLpNorm_exponent_zero, enorm_indicator_eq_indicator_enorm, eq_comm, essSup_indicator_eq_essSup_restrict, hp_top, hp_zero, indicator_comp_of_z, lintegral_indicator, p.toReal, simp_rw, toReal
-/
lemma eLpNorm_indicator_eq_eLpNorm_restrict {f : α -> ε} {s : Set α} (hs : MeasurableSet s) :
    eLpNorm (s.indicator f) p μ = eLpNorm f p (μ.restrict s) := by
  by_cases hp_zero : p = 0
  · simp only [hp_zero, eLpNorm_exponent_zero]
  by_cases hp_top : p = ∞
  · simp_rw [hp_top, eLpNorm_exponent_top, eLpNormEssSup_eq_essSup_enorm,
       enorm_indicator_eq_indicator_enorm, ENNReal.essSup_indicator_eq_essSup_restrict hs]
  simp_rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp_zero hp_top]
  rw [← lintegral_indicator hs]
  congr
  simp_rw [enorm_indicator_eq_indicator_enorm]
  rw [eq_comm]; rw [← Function.comp_def (fun x : Real>=0∞ => x ^ p.toReal)]; rw [Set.indicator_comp_of_zero]; rw [Function.comp_def]
  simp [ENNReal.toReal_pos hp_zero hp_top]

/--
lemma `eLpNormEssSup_indicator_eq_eLpNormEssSup_restrict` / 引理 `eLpNormEssSup_indicator_eq_eLpNormEssSup_restrict`

English:
lemma eLpNormEssSup_indicator_eq_eLpNormEssSup_restrict
  given: (hs : MeasurableSet s)
  proof: by
  simp_rw [← eLpNorm_exponent_top, eLpNorm_indicator_eq_eLpNorm_restrict hs]

中文:
引理 eLpNormEssSup_indicator_eq_eLpNormEssSup_restrict
  条件: (hs : 可测集 s)
  证明: by
  simp_rw [← eLpNorm_exponent_top, eLpNorm_indicator_eq_eLpNorm_restrict hs]

Depends on / 依赖: eLpNorm_exponent_top, eLpNorm_indicator_eq_eLpNorm_restrict, simp_rw
-/
lemma eLpNormEssSup_indicator_eq_eLpNormEssSup_restrict (hs : MeasurableSet s) :
    eLpNormEssSup (s.indicator f) μ = eLpNormEssSup f (μ.restrict s) := by
  simp_rw [← eLpNorm_exponent_top, eLpNorm_indicator_eq_eLpNorm_restrict hs]

/--
lemma `eLpNorm_restrict_le` / 引理 `eLpNorm_restrict_le`

English:
lemma eLpNorm_restrict_le
  given: (f : α -> ε') (p : Real>=0∞) (μ : Measure α) (s : Set α)
  proof: eLpNorm_mono_measure f Measure.restrict_le_self

中文:
引理 eLpNorm_restrict_le
  条件: (f : α -> ε') (p : 实数>=0∞) (μ : 测度 α) (s : 集合 α)
  证明: eLpNorm_mono_measure f Measure.restrict_le_self

Depends on / 依赖: Measure, Measure.restrict_le_self, eLpNorm_mono_measure, restrict_le_self
-/
lemma eLpNorm_restrict_le (f : α -> ε') (p : Real>=0∞) (μ : Measure α) (s : Set α) :
    eLpNorm f p (μ.restrict s) <= eLpNorm f p μ :=
  eLpNorm_mono_measure f Measure.restrict_le_self

/--
lemma `eLpNorm_indicator_le` / 引理 `eLpNorm_indicator_le`

English:
lemma eLpNorm_indicator_le
  given: (f : α -> ε)
  proof: by
  apply eLpNorm_mono_enorm
  simp_rw [enorm_indicator_eq_indicator_enorm]
  exact s.indicator_le_self _

中文:
引理 eLpNorm_indicator_le
  条件: (f : α -> ε)
  证明: by
  apply eLpNorm_mono_enorm
  simp_rw [enorm_indicator_eq_indicator_enorm]
  exact s.indicator_le_self _

Depends on / 依赖: eLpNorm_mono_enorm, enorm_indicator_eq_indicator_enorm, indicator_le_self, s.indicator_le_self, simp_rw
-/
lemma eLpNorm_indicator_le (f : α -> ε) :
    eLpNorm (s.indicator f) p μ <= eLpNorm f p μ := by
  apply eLpNorm_mono_enorm
  simp_rw [enorm_indicator_eq_indicator_enorm]
  exact s.indicator_le_self _

/--
lemma `eLpNormEssSup_indicator_le` / 引理 `eLpNormEssSup_indicator_le`

English:
lemma eLpNormEssSup_indicator_le
  given: (s : Set α) (f : α -> ε)
  proof: by
  refine essSup_mono_ae (.of_forall fun x => ?_)
  simp_rw [enorm_indicator_eq_indicator_enorm]
  exact Set.indicator_le_self s _ x

中文:
引理 eLpNormEssSup_indicator_le
  条件: (s : 集合 α) (f : α -> ε)
  证明: by
  refine essSup_mono_ae (.of_forall fun x => ?_)
  simp_rw [enorm_indicator_eq_indicator_enorm]
  exact Set.indicator_le_self s _ x

Depends on / 依赖: Complex.norm_real, IsReal, RingHom, RingHom.pi_apply, RingHom.prod_apply, Set.indicator_le_self, Set.mem_ofPred_eq, Set.mem_pi, Set.mem_prod, Set.mem_univ, Subtype, Subtype.forall, apply_ite, embedding, embedding_of_isReal_apply, enorm_indicator_eq_indicator_enorm, essSup_mono_ae, forall_true_left, h_ne, indicator_le_self
-/
lemma eLpNormEssSup_indicator_le (s : Set α) (f : α -> ε) :
    eLpNormEssSup (s.indicator f) μ <= eLpNormEssSup f μ := by
  refine essSup_mono_ae (.of_forall fun x => ?_)
  simp_rw [enorm_indicator_eq_indicator_enorm]
  exact Set.indicator_le_self s _ x

/--
lemma `eLpNormEssSup_indicator_const_le` / 引理 `eLpNormEssSup_indicator_const_le`

English:
lemma eLpNormEssSup_indicator_const_le
  given: (s : Set α) (c : ε)
  proof: by
  obtain rfl | hμ0 := eq_or_ne μ 0
  · simp
  · exact (eLpNormEssSup_indicator_le s fun _ => c).trans (eLpNormEssSup_const c hμ0).le

中文:
引理 eLpNormEssSup_indicator_const_le
  条件: (s : 集合 α) (c : ε)
  证明: by
  obtain rfl | hμ0 := eq_or_ne μ 0
  · simp
  · exact (eLpNormEssSup_indicator_le s fun _ => c).trans (eLpNormEssSup_const c hμ0).le

Depends on / 依赖: Pi.neg_apply, Prod.fst_neg, Prod.snd_neg, Real.norm_eq_abs, Set.mem_pi, Set.mem_prod, Set.mem_univ, Subtype, Subtype.forall, convert, dist_zero_right, eLpNormEssSup_const, eLpNormEssSup_indicator_le, eq_or_ne, fst_neg, mem_ball, mem_pi, mem_prod, mem_univ, neg_apply
-/
lemma eLpNormEssSup_indicator_const_le (s : Set α) (c : ε) :
    eLpNormEssSup (s.indicator fun _ : α => c) μ <= ‖c‖ₑ := by
  obtain rfl | hμ0 := eq_or_ne μ 0
  · simp
  · exact (eLpNormEssSup_indicator_le s fun _ => c).trans (eLpNormEssSup_const c hμ0).le

/--
lemma `eLpNormEssSup_indicator_const_eq` / 引理 `eLpNormEssSup_indicator_const_eq`

English:
lemma eLpNormEssSup_indicator_const_eq
  given: (s : Set α) (c : ε) (hμs : μ s != 0)
  proof: by
  refine le_antisymm (eLpNormEssSup_indicator_const_le s c) ?_
  by_contra! h
  have h' := ae_iff.mp (ae_lt_of_essSup_lt h)
  push Not at h'
  refine hμs (measure_mono_null (fun x hx_mem => ?_) h')
  rw [Set.mem_ofPred_eq]; rw [Set.indicator_of_mem hx_mem]

中文:
引理 eLpNormEssSup_indicator_const_eq
  条件: (s : 集合 α) (c : ε) (hμs : μ s != 0)
  证明: by
  refine le_antisymm (eLpNormEssSup_indicator_const_le s c) ?_
  by_contra! h
  have h' := ae_iff.mp (ae_lt_of_essSup_lt h)
  push Not at h'
  refine hμs (measure_mono_null (fun x hx_mem => ?_) h')
  rw [Set.mem_ofPred_eq]; rw [Set.indicator_of_mem hx_mem]

Depends on / 依赖: Convex, Convex.inter, Convex.prod, Set.indicator_of_mem, Set.mem_ofPred_eq, abs_lt, ae_iff, ae_iff.mp, ae_lt_of_essSup_lt, convex_ball, convex_halfSpace_im_gt, convex_halfSpace_im_lt, convex_halfSpace_re_gt, convex_halfSpace_re_lt, convex_pi, eLpNormEssSup_indicator_const_le, hx_mem, indicator_of_mem, le_antisymm, measure_mono_null
-/
lemma eLpNormEssSup_indicator_const_eq (s : Set α) (c : ε) (hμs : μ s != 0) :
    eLpNormEssSup (s.indicator fun _ : α => c) μ = ‖c‖ₑ := by
  refine le_antisymm (eLpNormEssSup_indicator_const_le s c) ?_
  by_contra! h
  have h' := ae_iff.mp (ae_lt_of_essSup_lt h)
  push Not at h'
  refine hμs (measure_mono_null (fun x hx_mem => ?_) h')
  rw [Set.mem_ofPred_eq]; rw [Set.indicator_of_mem hx_mem]

/--
lemma `eLpNorm_indicator_const₀` / 引理 `eLpNorm_indicator_const₀`

English:
lemma eLpNorm_indicator_const₀
  given: (hs : NullMeasurableSet s μ) (hp : p != 0) (hp_top : p != ∞)
  proof: have hp_pos : 0 < p.toReal := ENNReal.toReal_pos hp hp_top
  calc
    eLpNorm (s.indicator fun _ => c) p μ
      = (∫⁻ x, (‖(s.indicator fun _ => c) x‖ₑ ^ p.toReal) ∂μ) ^ (1 / p.toReal) :=
          eLpNorm_eq_lintegral_rpow_enorm_toReal hp hp_top
    _ = (∫⁻ x, (s.indicator fun _ => ‖c‖ₑ ^ p.toReal

中文:
引理 eLpNorm_indicator_const₀
  条件: (hs : NullMeasurableSet s μ) (hp : p != 0) (hp_top : p != ∞)
  证明: have hp_pos : 0 < p.toReal := ENNReal.toReal_pos hp hp_top
  calc
    eLpNorm (s.indicator fun _ => c) p μ
      = (∫⁻ x, (‖(s.indicator fun _ => c) x‖ₑ ^ p.toReal) ∂μ) ^ (1 / p.toReal) :=
          eLpNorm_eq_lintegral_rpow_enorm_toReal hp hp_top
    _ = (∫⁻ x, (s.indicator fun _ => ‖c‖ₑ ^ p.toReal

Depends on / 依赖: ENNReal, ENNReal.mul_rpow_of_nonneg, ENNReal.toReal_pos, NNReal, NNReal.pi, Set.comp_indicator_const, comp_indicator_const, eLpNorm, eLpNorm_eq_lintegral_rpow_enorm_toReal, hp_pos, hp_top, indicator, mul_rpow_of_nonneg, nrComplexPlaces, nrRealPlaces, p.toReal, s.indicator, toReal, toReal_pos
-/
lemma eLpNorm_indicator_const₀ (hs : NullMeasurableSet s μ) (hp : p != 0) (hp_top : p != ∞) :
    eLpNorm (s.indicator fun _ => c) p μ = ‖c‖ₑ * μ s ^ (1 / p.toReal) :=
  have hp_pos : 0 < p.toReal := ENNReal.toReal_pos hp hp_top
  calc
    eLpNorm (s.indicator fun _ => c) p μ
      = (∫⁻ x, (‖(s.indicator fun _ => c) x‖ₑ ^ p.toReal) ∂μ) ^ (1 / p.toReal) :=
          eLpNorm_eq_lintegral_rpow_enorm_toReal hp hp_top
    _ = (∫⁻ x, (s.indicator fun _ => ‖c‖ₑ ^ p.toReal) x ∂μ) ^ (1 / p.toReal) := by
      congr 2
      refine (Set.comp_indicator_const c (fun x => (‖x‖ₑ) ^ p.toReal) ?_)
      simp [hp_pos]
    _ = ‖c‖ₑ * μ s ^ (1 / p.toReal) := by
      rw [lintegral_indicator_const₀ hs]; rw [ENNReal.mul_rpow_of_nonneg]; rw [← ENNReal.rpow_mul]; rw [mul_one_div_cancel hp_pos.ne']; rw [ENNReal.rpow_one]
      positivity

/--
lemma `eLpNorm_indicator_const` / 引理 `eLpNorm_indicator_const`

English:
lemma eLpNorm_indicator_const
  given: (hs : MeasurableSet s) (hp : p != 0) (hp_top : p != ∞)
  proof: eLpNorm_indicator_const₀ hs.nullMeasurableSet hp hp_top

中文:
引理 eLpNorm_indicator_const
  条件: (hs : 可测集 s) (hp : p != 0) (hp_top : p != ∞)
  证明: eLpNorm_indicator_const₀ hs.nullMeasurableSet hp hp_top

Depends on / 依赖: hp_top, hs.nullMeasurableSet, mul_ne_zero, nullMeasurableSet, pi_ne_zero, pow_ne_zero, two_ne_zero
-/
lemma eLpNorm_indicator_const (hs : MeasurableSet s) (hp : p != 0) (hp_top : p != ∞) :
    eLpNorm (s.indicator fun _ => c) p μ = ‖c‖ₑ * μ s ^ (1 / p.toReal) :=
  eLpNorm_indicator_const₀ hs.nullMeasurableSet hp hp_top

/--
lemma `eLpNorm_indicator_const'` / 引理 `eLpNorm_indicator_const'`

English:
lemma eLpNorm_indicator_const'
  given: (hs : MeasurableSet s) (hμs : μ s != 0) (hp : p != 0)
  proof: by
  by_cases hp_top : p = ∞
  · simp [hp_top, eLpNormEssSup_indicator_const_eq s c hμs]
  · exact eLpNorm_indicator_const hs hp hp_top

中文:
引理 eLpNorm_indicator_const'
  条件: (hs : 可测集 s) (hμs : μ s != 0) (hp : p != 0)
  证明: by
  by_cases hp_top : p = ∞
  · simp [hp_top, eLpNormEssSup_indicator_const_eq s c hμs]
  · exact eLpNorm_indicator_const hs hp hp_top

Depends on / 依赖: eLpNormEssSup_indicator_const_eq, eLpNorm_indicator_const, hp_top
-/
lemma eLpNorm_indicator_const' (hs : MeasurableSet s) (hμs : μ s != 0) (hp : p != 0) :
    eLpNorm (s.indicator fun _ => c) p μ = ‖c‖ₑ * μ s ^ (1 / p.toReal) := by
  by_cases hp_top : p = ∞
  · simp [hp_top, eLpNormEssSup_indicator_const_eq s c hμs]
  · exact eLpNorm_indicator_const hs hp hp_top

variable (c) in
/--
lemma `eLpNorm_indicator_const_le` / 引理 `eLpNorm_indicator_const_le`

English:
lemma eLpNorm_indicator_const_le
  given: (p : Real>=0∞)
  proof: by
  obtain rfl | hp := eq_or_ne p 0
  · simp
  obtain rfl | h'p := eq_or_ne p ∞
  · simp only [eLpNorm_exponent_top, ENNReal.toReal_top, _root_.div_zero, ENNReal.rpow_zero,
      mul_one]
    exact eLpNormEssSup_indicator_const_le _ _
  let t := toMeasurable μ s
  calc
    eLpNorm (s.indicator fun 

中文:
引理 eLpNorm_indicator_const_le
  条件: (p : 实数>=0∞)
  证明: by
  obtain rfl | hp := eq_or_ne p 0
  · simp
  obtain rfl | h'p := eq_or_ne p ∞
  · simp only [eLpNorm_exponent_top, ENNReal.toReal_top, _root_.div_zero, ENNReal.rpow_zero,
      mul_one]
    exact eLpNormEssSup_indicator_const_le _ _
  let t := toMeasurable μ s
  calc
    eLpNorm (s.indicator fun 

Depends on / 依赖: Complex.measurableEquivRealProd_symm_apply, Complex.volume_preserving_equiv_real_prod.symm, ENNReal, ENNReal.rpow_zero, ENNReal.toReal_top, Set.Ioo, Set.mem_Ioo, Set.mem_ofPred_eq, Set.mem_prod, Set.preimage_ofPred_eq, _root_, _root_.div_zero, abs_lt, div_zero, eLpNorm, eLpNormEssSup_indicator_const_le, eLpNorm_exponent_top, eLpNorm_indicator_const, eLpNorm_mono_enorm, enorm_indicator_le_of_subset
-/
lemma eLpNorm_indicator_const_le (p : Real>=0∞) :
    eLpNorm (s.indicator fun _ => c) p μ <= ‖c‖ₑ * μ s ^ (1 / p.toReal) := by
  obtain rfl | hp := eq_or_ne p 0
  · simp
  obtain rfl | h'p := eq_or_ne p ∞
  · simp only [eLpNorm_exponent_top, ENNReal.toReal_top, _root_.div_zero, ENNReal.rpow_zero,
      mul_one]
    exact eLpNormEssSup_indicator_const_le _ _
  let t := toMeasurable μ s
  calc
    eLpNorm (s.indicator fun _ => c) p μ <= eLpNorm (t.indicator fun _ => c) p μ :=
      eLpNorm_mono_enorm (enorm_indicator_le_of_subset (subset_toMeasurable _ _) _)
    _ = ‖c‖ₑ * μ t ^ (1 / p.toReal) :=
      eLpNorm_indicator_const (measurableSet_toMeasurable ..) hp h'p
    _ = ‖c‖ₑ * μ s ^ (1 / p.toReal) := by rw [measure_toMeasurable]

/--
lemma `MemLp.indicator` / 引理 `MemLp.indicator`

English:
lemma MemLp.indicator
  given: {f : α -> ε} (hs : MeasurableSet s) (hf : MemLp f p μ)
  proof: ⟨hf.aestronglyMeasurable.indicator hs, lt_of_le_of_lt (eLpNorm_indicator_le f) (by finiteness)⟩

中文:
引理 MemLp.indicator
  条件: {f : α -> ε} (hs : 可测集 s) (hf : MemLp f p μ)
  证明: ⟨hf.aestronglyMeasurable.indicator hs, lt_of_le_of_lt (eLpNorm_indicator_le f) (by finiteness)⟩

Depends on / 依赖: aestronglyMeasurable, eLpNorm_indicator_le, finiteness, hf.aestronglyMeasurable.indicator, indicator, lt_of_le_of_lt
-/
lemma MemLp.indicator {f : α -> ε} (hs : MeasurableSet s) (hf : MemLp f p μ) :
    MemLp (s.indicator f) p μ :=
  ⟨hf.aestronglyMeasurable.indicator hs, lt_of_le_of_lt (eLpNorm_indicator_le f) (by finiteness)⟩

/--
lemma `memLp_indicator_iff_restrict` / 引理 `memLp_indicator_iff_restrict`

English:
lemma memLp_indicator_iff_restrict
  given: {f : α -> ε} (hs : MeasurableSet s)
  proof: by
  simp [MemLp, aestronglyMeasurable_indicator_iff hs, eLpNorm_indicator_eq_eLpNorm_restrict hs]

中文:
引理 memLp_indicator_iff_restrict
  条件: {f : α -> ε} (hs : 可测集 s)
  证明: by
  simp [MemLp, aestronglyMeasurable_indicator_iff hs, eLpNorm_indicator_eq_eLpNorm_restrict hs]

Depends on / 依赖: aestronglyMeasurable_indicator_iff, eLpNorm_indicator_eq_eLpNorm_restrict
-/
lemma memLp_indicator_iff_restrict {f : α -> ε} (hs : MeasurableSet s) :
    MemLp (s.indicator f) p μ ↔ MemLp f p (μ.restrict s) := by
  simp [MemLp, aestronglyMeasurable_indicator_iff hs, eLpNorm_indicator_eq_eLpNorm_restrict hs]

/--
lemma `memLp_indicator_const` / 引理 `memLp_indicator_const`

English:
lemma memLp_indicator_const
  given: (p : Real>=0∞) (hs : MeasurableSet s) (c : E) (hμsc : c = 0 ∨ μ s != ∞)
  proof: by
  rw [memLp_indicator_iff_restrict hs]
  obtain rfl | hμ := hμsc
  · exact MemLp.zero
  · have := Fact.mk hμ.lt_top
    apply memLp_const

中文:
引理 memLp_indicator_const
  条件: (p : 实数>=0∞) (hs : 可测集 s) (c : E) (hμsc : c = 0 ∨ μ s != ∞)
  证明: by
  rw [memLp_indicator_iff_restrict hs]
  obtain rfl | hμ := hμsc
  · exact MemLp.zero
  · have := Fact.mk hμ.lt_top
    apply memLp_const

Depends on / 依赖: Fact.mk, MemLp.zero, lt_top, memLp_const, memLp_indicator_iff_restrict
-/
lemma memLp_indicator_const (p : Real>=0∞) (hs : MeasurableSet s) (c : E) (hμsc : c = 0 ∨ μ s != ∞) :
    MemLp (s.indicator fun _ => c) p μ := by
  rw [memLp_indicator_iff_restrict hs]
  obtain rfl | hμ := hμsc
  · exact MemLp.zero
  · have := Fact.mk hμ.lt_top
    apply memLp_const

/--
lemma `eLpNormEssSup_piecewise` / 引理 `eLpNormEssSup_piecewise`

English:
lemma eLpNormEssSup_piecewise
  given: (f g : α -> ε) [DecidablePred (· in s)] (hs : MeasurableSet s)
  proof: by
  simp only [eLpNormEssSup, ← ENNReal.essSup_piecewise hs]
  congr with x
  by_cases hx : x in s <;> simp [hx]

中文:
引理 eLpNormEssSup_piecewise
  条件: (f g : α -> ε) [DecidablePred (· in s)] (hs : 可测集 s)
  证明: by
  simp only [eLpNormEssSup, ← ENNReal.essSup_piecewise hs]
  congr with x
  by_cases hx : x in s <;> simp [hx]

Depends on / 依赖: ENNReal, ENNReal.essSup_piecewise, eLpNormEssSup, essSup_piecewise
-/
lemma eLpNormEssSup_piecewise (f g : α -> ε) [DecidablePred (· in s)] (hs : MeasurableSet s) :
    eLpNormEssSup (Set.piecewise s f g) μ
      = max (eLpNormEssSup f (μ.restrict s)) (eLpNormEssSup g (μ.restrict sᶜ)) := by
  simp only [eLpNormEssSup, ← ENNReal.essSup_piecewise hs]
  congr with x
  by_cases hx : x in s <;> simp [hx]

/--
lemma `eLpNorm_top_piecewise` / 引理 `eLpNorm_top_piecewise`

English:
lemma eLpNorm_top_piecewise
  given: (f g : α -> ε) [DecidablePred (· in s)] (hs : MeasurableSet s)
  proof: eLpNormEssSup_piecewise f g hs

中文:
引理 eLpNorm_top_piecewise
  条件: (f g : α -> ε) [DecidablePred (· in s)] (hs : 可测集 s)
  证明: eLpNormEssSup_piecewise f g hs

Depends on / 依赖: eLpNormEssSup_piecewise
-/
lemma eLpNorm_top_piecewise (f g : α -> ε) [DecidablePred (· in s)] (hs : MeasurableSet s) :
    eLpNorm (Set.piecewise s f g) ∞ μ
      = max (eLpNorm f ∞ (μ.restrict s)) (eLpNorm g ∞ (μ.restrict sᶜ)) :=
  eLpNormEssSup_piecewise f g hs

/--
lemma `MemLp.piecewise` / 引理 `MemLp.piecewise`

English:
lemma MemLp.piecewise
  statement: {f : α -> ε} [DecidablePred (· in s)] {g} (hs : MeasurableSet s)
  proof: by
  by_cases hp_zero : p = 0
  · simp only [hp_zero, memLp_zero_iff_aestronglyMeasurable]
    exact AEStronglyMeasurable.piecewise hs hf.1 hg.1
  refine ⟨AEStronglyMeasurable.piecewise hs hf.1 hg.1, ?_⟩
  obtain rfl | hp_top := eq_or_ne p ∞
  · rw [eLpNorm_top_piecewise f g hs]
    exact max_lt hf.

中文:
引理 MemLp.piecewise
  结论: {f : α -> ε} [DecidablePred (· in s)] {g} (hs : 可测集 s)
  证明: by
  by_cases hp_zero : p = 0
  · simp only [hp_zero, memLp_zero_iff_aestronglyMeasurable]
    exact AEStronglyMeasurable.piecewise hs hf.1 hg.1
  refine ⟨AEStronglyMeasurable.piecewise hs hf.1 hg.1, ?_⟩
  obtain rfl | hp_top := eq_or_ne p ∞
  · rw [eLpNorm_top_piecewise f g hs]
    exact max_lt hf.
-/
protected lemma MemLp.piecewise {f : α -> ε} [DecidablePred (· in s)] {g} (hs : MeasurableSet s)
    (hf : MemLp f p (μ.restrict s)) (hg : MemLp g p (μ.restrict sᶜ)) :
    MemLp (s.piecewise f g) p μ := by
  by_cases hp_zero : p = 0
  · simp only [hp_zero, memLp_zero_iff_aestronglyMeasurable]
    exact AEStronglyMeasurable.piecewise hs hf.1 hg.1
  refine ⟨AEStronglyMeasurable.piecewise hs hf.1 hg.1, ?_⟩
  obtain rfl | hp_top := eq_or_ne p ∞
  · rw [eLpNorm_top_piecewise f g hs]
    exact max_lt hf.2 hg.2
  rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top hp_zero hp_top]; rw [← lintegral_add_compl _ hs]; rw [ENNReal.add_lt_top]
  constructor
  · have h (x) (hx : x in s) : ‖Set.piecewise s f g x‖ₑ ^ p.toReal = ‖f x‖ₑ ^ p.toReal := by
      simp [hx]
    rw [setLIntegral_congr_fun hs h]
    exact lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top hp_zero hp_top hf.2
  · have h (x) (hx : x in sᶜ) : ‖Set.piecewise s f g x‖ₑ ^ p.toReal = ‖g x‖ₑ ^ p.toReal := by
      have hx' : x ∉ s := hx
      simp [hx']
    rw [setLIntegral_congr_fun hs.compl h]
    exact lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top hp_zero hp_top hg.2

/--
theorem `eLpNorm_indicator_sub_le_of_dist_bdd` / 定理 `eLpNorm_indicator_sub_le_of_dist_bdd`

English:
theorem eLpNorm_indicator_sub_le_of_dist_bdd
  statement: {β : Type*} [NormedAddCommGroup β]
  proof: by
  by_cases hp : p = 0
  · simp [hp]
  have : forall x, ‖s.indicator (f - g) x‖ <= ‖s.indicator (fun _ => c) x‖ := by
    intro x
    by_cases hx : x in s
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, Pi.sub_apply, ← dist_eq_norm,
        Real.norm_eq_abs, abs_of_nonneg hc]
      exa

中文:
定理 eLpNorm_indicator_sub_le_of_dist_bdd
  结论: {β : 类型} [赋范交换加群 β]
  证明: by
  by_cases hp : p = 0
  · simp [hp]
  have : forall x, ‖s.indicator (f - g) x‖ <= ‖s.indicator (fun _ => c) x‖ := by
    intro x
    by_cases hx : x in s
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, Pi.sub_apply, ← dist_eq_norm,
        Real.norm_eq_abs, abs_of_nonneg hc]
      exa

Depends on / 依赖: ENNReal, ENNReal.ofReal, MeasurableSet, Pi.sub_apply, Real.norm_eq_abs, Set.indicator_of_mem, abs_of_nonneg, dist_eq_norm, eLpNorm, indicator, indicator_of_mem, norm_eq_abs, ofReal, p.toReal, s.indicator, sub_apply, toReal, volume_tac
-/
theorem eLpNorm_indicator_sub_le_of_dist_bdd {β : Type*} [NormedAddCommGroup β]
    (μ : Measure α := by volume_tac) (hp' : p != ∞) (hs : MeasurableSet s)
    {f g : α -> β} {c : Real} (hc : 0 <= c) (hf : forall x in s, dist (f x) (g x) <= c) :
    eLpNorm (s.indicator (f - g)) p μ <= ENNReal.ofReal c * μ s ^ (1 / p.toReal) := by
  by_cases hp : p = 0
  · simp [hp]
  have : forall x, ‖s.indicator (f - g) x‖ <= ‖s.indicator (fun _ => c) x‖ := by
    intro x
    by_cases hx : x in s
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, Pi.sub_apply, ← dist_eq_norm,
        Real.norm_eq_abs, abs_of_nonneg hc]
      exact hf x hx
    · simp [Set.indicator_of_notMem hx]
  grw [eLpNorm_mono this, eLpNorm_indicator_const hs hp hp', ← ofReal_norm,
    Real.norm_eq_abs, abs_of_nonneg hc]

/--
theorem `eLpNorm_sub_le_of_dist_bdd` / 定理 `eLpNorm_sub_le_of_dist_bdd`

English:
theorem eLpNorm_sub_le_of_dist_bdd
  statement: {β : Type*} [NormedAddCommGroup β]
  proof: by
  have hs₃ : s.indicator (f - g) = f - g := by
    rw [Set.indicator_eq_self]
    exact (Function.support_sub _ _).trans (Set.union_subset hs₁ hs₂)
  rw [← hs₃]
  exact eLpNorm_indicator_sub_le_of_dist_bdd μ hp hs hc (fun x _ => h x)

中文:
定理 eLpNorm_sub_le_of_dist_bdd
  结论: {β : 类型} [赋范交换加群 β]
  证明: by
  have hs₃ : s.indicator (f - g) = f - g := by
    rw [Set.indicator_eq_self]
    exact (Function.support_sub _ _).trans (Set.union_subset hs₁ hs₂)
  rw [← hs₃]
  exact eLpNorm_indicator_sub_le_of_dist_bdd μ hp hs hc (fun x _ => h x)

Depends on / 依赖: ENNReal, ENNReal.ofReal, Function, Function.support_sub, MeasurableSet, Set.indicator_eq_self, Set.union_subset, eLpNorm, eLpNorm_indicator_sub_le_of_dist_bdd, f.support, g.support, indicator, indicator_eq_self, ofReal, p.toReal, s.indicator, subseteq, support, support_sub, toReal
-/
theorem eLpNorm_sub_le_of_dist_bdd {β : Type*} [NormedAddCommGroup β]
    (μ : Measure α := by volume_tac) (hp : p != ⊤) (hs : MeasurableSet s) {c : Real} (hc : 0 <= c)
    {f g : α -> β} (h : forall x, dist (f x) (g x) <= c) (hs₁ : f.support subseteq s) (hs₂ : g.support subseteq s) :
    eLpNorm (f - g) p μ <= ENNReal.ofReal c * μ s ^ (1 / p.toReal) := by
  have hs₃ : s.indicator (f - g) = f - g := by
    rw [Set.indicator_eq_self]
    exact (Function.support_sub _ _).trans (Set.union_subset hs₁ hs₂)
  rw [← hs₃]
  exact eLpNorm_indicator_sub_le_of_dist_bdd μ hp hs hc (fun x _ => h x)

end Indicator

section UnifTight

/--
theorem `MemLp.exists_eLpNorm_indicator_compl_lt` / 定理 `MemLp.exists_eLpNorm_indicator_compl_lt`

English:
theorem MemLp.exists_eLpNorm_indicator_compl_lt
  statement: {β : Type*} [NormedAddCommGroup β] (hp_top : p != ∞)
  proof: by
  rcases eq_or_ne p 0 with rfl | hp₀
  · use ∅; simp [pos_iff_ne_zero.2 hε] -- first take care of `p = 0`
  · obtain ⟨s, hsm, hs, hε⟩ :
        exists s, MeasurableSet s ∧ μ s < ∞ ∧ ∫⁻ a in sᶜ, (‖f a‖ₑ) ^ p.toReal ∂μ < ε ^ p.toReal := by
      apply exists_setLIntegral_compl_lt
      · exact ((eL

中文:
定理 MemLp.存在_eLpNorm_indicator_compl_lt
  结论: {β : 类型} [赋范交换加群 β] (hp_top : p != ∞)
  证明: by
  rcases eq_or_ne p 0 with rfl | hp₀
  · use ∅; simp [pos_iff_ne_zero.2 hε] -- first take care of `p = 0`
  · obtain ⟨s, hsm, hs, hε⟩ :
        exists s, MeasurableSet s ∧ μ s < ∞ ∧ ∫⁻ a in sᶜ, (‖f a‖ₑ) ^ p.toReal ∂μ < ε ^ p.toReal := by
      apply exists_setLIntegral_compl_lt
      · exact ((eL

Depends on / 依赖: ENNReal, ENNReal.r, MeasurableSet, eLpNorm_eq_lintegral_rpow_enorm_toReal, eLpNorm_indicator_eq_eLpNorm_restrict, eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top, eq_or_ne, exists_setLIntegral_compl_lt, hp_top, hsm.compl, one_div, p.toReal, pos_iff_ne_zero, toReal
-/
theorem MemLp.exists_eLpNorm_indicator_compl_lt {β : Type*} [NormedAddCommGroup β] (hp_top : p != ∞)
    {f : α -> β} (hf : MemLp f p μ) {ε : Real>=0∞} (hε : ε != 0) :
    exists s : Set α, MeasurableSet s ∧ μ s < ∞ ∧ eLpNorm (sᶜ.indicator f) p μ < ε := by
  rcases eq_or_ne p 0 with rfl | hp₀
  · use ∅; simp [pos_iff_ne_zero.2 hε] -- first take care of `p = 0`
  · obtain ⟨s, hsm, hs, hε⟩ :
        exists s, MeasurableSet s ∧ μ s < ∞ ∧ ∫⁻ a in sᶜ, (‖f a‖ₑ) ^ p.toReal ∂μ < ε ^ p.toReal := by
      apply exists_setLIntegral_compl_lt
      · exact ((eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top hp₀ hp_top).1 hf.2).ne
      · simp [*]
    refine ⟨s, hsm, hs, ?_⟩
    rwa [eLpNorm_indicator_eq_eLpNorm_restrict hsm.compl,
      eLpNorm_eq_lintegral_rpow_enorm_toReal hp₀ hp_top, one_div, ENNReal.rpow_inv_lt_iff]
    simp [ENNReal.toReal_pos, *]

end UnifTight
end Lp
end MeasureTheory
