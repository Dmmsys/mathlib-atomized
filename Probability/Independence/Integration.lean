/-
Copyright (c) 2021 Martin Zinkevich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Zinkevich, Vincent Beffara, Etienne Marion
-/
module

public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.Probability.Independence.Integrable
public import Mathlib.Probability.Notation

/-!
# Integration in Probability Theory

Integration results for independent random variables. Specifically, for two
independent random variables X and Y over the extended non-negative
reals, `E[X * Y] = E[X] * E[Y]`, and similar results.

## Implementation notes

Many lemmas in this file take two arguments of the same typeclass. It is worth remembering that lean
will always pick the later typeclass in this situation, and does not care whether the arguments are
`[]`, `{}`, or `()`. All of these use the `MeasurableSpace` `M2` to define `μ`:

```lean
example {M1 : MeasurableSpace Ω} [M2 : MeasurableSpace Ω] {μ : Measure Ω} : sorry := sorry
example [M1 : MeasurableSpace Ω] {M2 : MeasurableSpace Ω} {μ : Measure Ω} : sorry := sorry
```

-/

public section


open Set MeasureTheory ENNReal

open scoped NNReal MeasureTheory

variable {Ω 𝕜 : Type*} [RCLike 𝕜] {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {f g : Ω -> Real>=0∞}
    {X Y : Ω -> 𝕜}

namespace ProbabilityTheory

/--
theorem `lintegral_mul_indicator_eq_lintegral_mul_lintegral_indicator` / 定理 `lintegral_mul_indicator_eq_lintegral_mul_lintegral_indicator`

English:
theorem lintegral_mul_indicator_eq_lintegral_mul_lintegral_indicator
  statement: {Mf mΩ : MeasurableSpace Ω}
  proof: by
  revert f
  have h_mul_indicator : forall g, Measurable g -> Measurable fun a => g a * T.indicator (fun _ => c) a :=
    fun g h_mg => h_mg.mul (measurable_const.indicator h_meas_T)
  apply @Measurable.ennreal_induction _ Mf
  · intro c' s' h_meas_s'
    simp_rw [← inter_indicator_mul]
    rw [l

中文:
定理 lintegral_mul_indicator_eq_lintegral_mul_lintegral_indicator
  结论: {Mf mΩ : MeasurableSpace Ω}
  证明: by
  revert f
  have h_mul_indicator : forall g, Measurable g -> Measurable fun a => g a * T.indicator (fun _ => c) a :=
    fun g h_mg => h_mg.mul (measurable_const.indicator h_meas_T)
  apply @Measurable.ennreal_induction _ Mf
  · intro c' s' h_meas_s'
    simp_rw [← inter_indicator_mul]
    rw [l

Depends on / 依赖: Measurable, Measurable.ennreal_induction, MeasurableSet, MeasurableSet.inter, MeasurableSet.univ, Measure, Measure.rest, T.indicator, ennreal_induction, h_meas_T, h_meas_s, h_mg, h_mg.mul, h_mul_indicator, indicator, inter_indicator_mul, lintegral_const, lintegral_indicator, measurable_const, measurable_const.indicator
-/
theorem lintegral_mul_indicator_eq_lintegral_mul_lintegral_indicator {Mf mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} (hMf : Mf <= mΩ) (c : Real>=0∞) {T : Set Ω} (h_meas_T : MeasurableSet T)
    (h_ind : IndepSets {s | MeasurableSet[Mf] s} {T} μ) (h_meas_f : Measurable[Mf] f) :
    (∫⁻ ω, f ω * T.indicator (fun _ => c) ω ∂μ) =
      (∫⁻ ω, f ω ∂μ) * ∫⁻ ω, T.indicator (fun _ => c) ω ∂μ := by
  revert f
  have h_mul_indicator : forall g, Measurable g -> Measurable fun a => g a * T.indicator (fun _ => c) a :=
    fun g h_mg => h_mg.mul (measurable_const.indicator h_meas_T)
  apply @Measurable.ennreal_induction _ Mf
  · intro c' s' h_meas_s'
    simp_rw [← inter_indicator_mul]
    rw [lintegral_indicator (MeasurableSet.inter (hMf _ h_meas_s') h_meas_T)]; rw [lintegral_indicator (hMf _ h_meas_s')]; rw [lintegral_indicator h_meas_T]
    simp only [lintegral_const, univ_inter,
      MeasurableSet.univ, Measure.restrict_apply]
    rw [IndepSets_iff] at h_ind
    rw [mul_mul_mul_comm]; rw [h_ind s' T h_meas_s' (Set.mem_singleton _)]
  · intro f' g _ h_meas_f' _ h_ind_f' h_ind_g
    have h_measM_f' : Measurable f' := h_meas_f'.mono hMf le_rfl
    simp_rw [Pi.add_apply, right_distrib]
    rw [lintegral_add_left (h_mul_indicator _ h_measM_f')]; rw [lintegral_add_left h_measM_f']; rw [right_distrib]; rw [h_ind_f']; rw [h_ind_g]
  · intro f h_meas_f h_mono_f h_ind_f
    have h_measM_f : forall n, Measurable (f n) := fun n => (h_meas_f n).mono hMf le_rfl
    simp_rw [iSup_mul]
    rw [lintegral_iSup h_measM_f h_mono_f]; rw [lintegral_iSup]; rw [iSup_mul]
    · simp_rw [← h_ind_f]
    · exact fun n => h_mul_indicator _ (h_measM_f n)
    · exact fun m n h_le a => mul_le_mul_left (h_mono_f h_le a) _

/--
theorem `lintegral_mul_eq_lintegral_mul_lintegral_of_independent_measurableSpace` / 定理 `lintegral_mul_eq_lintegral_mul_lintegral_of_independent_measurableSpace`

English:
theorem lintegral_mul_eq_lintegral_mul_lintegral_of_independent_measurableSpace
  proof: by
  revert g
  have h_measM_f : Measurable f := h_meas_f.mono hMf le_rfl
  apply @Measurable.ennreal_induction _ Mg
  · intro c s h_s
    apply lintegral_mul_indicator_eq_lintegral_mul_lintegral_indicator hMf _ (hMg _ h_s) _ h_meas_f
    apply indepSets_of_indepSets_of_le_right h_ind
    rwa [singl

中文:
定理 lintegral_mul_eq_lintegral_mul_lintegral_of_independent_measurableSpace
  证明: by
  revert g
  have h_measM_f : Measurable f := h_meas_f.mono hMf le_rfl
  apply @Measurable.ennreal_induction _ Mg
  · intro c s h_s
    apply lintegral_mul_indicator_eq_lintegral_mul_lintegral_indicator hMf _ (hMg _ h_s) _ h_meas_f
    apply indepSets_of_indepSets_of_le_right h_ind
    rwa [singl

Depends on / 依赖: Measurable, Measurable.ennreal_induction, Pi.add_apply, add_apply, ennreal_induction, h_ind, h_ind_f, h_ind_g, h_measM_f, h_measMg_f, h_meas_f, h_meas_f.mono, indepSets_of_indepSets_of_le_right, le_rfl, left_distrib, lintegral_add_le, lintegral_add_left, lintegral_mul_indicator_eq_lintegral_mul_lintegral_indicator, revert, simp_rw
-/
theorem lintegral_mul_eq_lintegral_mul_lintegral_of_independent_measurableSpace
    {Mf Mg mΩ : MeasurableSpace Ω} {μ : Measure Ω} (hMf : Mf <= mΩ) (hMg : Mg <= mΩ)
    (h_ind : Indep Mf Mg μ) (h_meas_f : Measurable[Mf] f) (h_meas_g : Measurable[Mg] g) :
    ∫⁻ ω, f ω * g ω ∂μ = (∫⁻ ω, f ω ∂μ) * ∫⁻ ω, g ω ∂μ := by
  revert g
  have h_measM_f : Measurable f := h_meas_f.mono hMf le_rfl
  apply @Measurable.ennreal_induction _ Mg
  · intro c s h_s
    apply lintegral_mul_indicator_eq_lintegral_mul_lintegral_indicator hMf _ (hMg _ h_s) _ h_meas_f
    apply indepSets_of_indepSets_of_le_right h_ind
    rwa [singleton_subset_iff]
  · intro f' g _ h_measMg_f' _ h_ind_f' h_ind_g'
    have h_measM_f' : Measurable f' := h_measMg_f'.mono hMg le_rfl
    simp_rw [Pi.add_apply, left_distrib]
    rw [lintegral_add_left h_measM_f']; rw [lintegral_add_left (h_measM_f.fun_mul h_measM_f')]; rw [left_distrib]; rw [h_ind_f']; rw [h_ind_g']
  · intro f' h_meas_f' h_mono_f' h_ind_f'
    have h_measM_f' : forall n, Measurable (f' n) := fun n => (h_meas_f' n).mono hMg le_rfl
    simp_rw [mul_iSup]
    rw [lintegral_iSup]; rw [lintegral_iSup h_measM_f' h_mono_f']; rw [mul_iSup]
    · simp_rw [← h_ind_f']
    · exact fun n => h_measM_f.mul (h_measM_f' n)
    · exact fun n m (h_le : n <= m) a => mul_le_mul_right (h_mono_f' h_le a) _

/--
theorem `lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun` / 定理 `lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun`

English:
theorem lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun
  statement: (h_meas_f : Measurable f)
  proof: lintegral_mul_eq_lintegral_mul_lintegral_of_independent_measurableSpace
    (measurable_iff_comap_le.1 h_meas_f) (measurable_iff_comap_le.1 h_meas_g) h_indep_fun
    (Measurable.of_comap_le le_rfl) (Measurable.of_comap_le le_rfl)

中文:
定理 lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun
  结论: (h_meas_f : Measurable f)
  证明: lintegral_mul_eq_lintegral_mul_lintegral_of_independent_measurableSpace
    (measurable_iff_comap_le.1 h_meas_f) (measurable_iff_comap_le.1 h_meas_g) h_indep_fun
    (Measurable.of_comap_le le_rfl) (Measurable.of_comap_le le_rfl)

Depends on / 依赖: Measurable, Measurable.of_comap_le, h_indep_fun, h_meas_f, h_meas_g, le_rfl, lintegral_mul_eq_lintegral_mul_lintegral_of_independent_measurableSpace, measurable_iff_comap_le, of_comap_le
-/
theorem lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun (h_meas_f : Measurable f)
    (h_meas_g : Measurable g) (h_indep_fun : f ⟂ᵢ[μ] g) :
    (∫⁻ ω, (f * g) ω ∂μ) = (∫⁻ ω, f ω ∂μ) * ∫⁻ ω, g ω ∂μ :=
  lintegral_mul_eq_lintegral_mul_lintegral_of_independent_measurableSpace
    (measurable_iff_comap_le.1 h_meas_f) (measurable_iff_comap_le.1 h_meas_g) h_indep_fun
    (Measurable.of_comap_le le_rfl) (Measurable.of_comap_le le_rfl)

/--
theorem `lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun'` / 定理 `lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun'`

English:
theorem lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun'
  statement: (h_meas_f : AEMeasurable f μ)
  proof: by
  have fg_ae : f * g =ᵐ[μ] h_meas_f.mk _ * h_meas_g.mk _ := h_meas_f.ae_eq_mk.mul h_meas_g.ae_eq_mk
  rw [lintegral_congr_ae h_meas_f.ae_eq_mk]; rw [lintegral_congr_ae h_meas_g.ae_eq_mk]; rw [lintegral_congr_ae fg_ae]
  apply lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun h_meas_f.measurabl

中文:
定理 lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun'
  结论: (h_meas_f : AEMeasurable f μ)
  证明: by
  have fg_ae : f * g =ᵐ[μ] h_meas_f.mk _ * h_meas_g.mk _ := h_meas_f.ae_eq_mk.mul h_meas_g.ae_eq_mk
  rw [lintegral_congr_ae h_meas_f.ae_eq_mk]; rw [lintegral_congr_ae h_meas_g.ae_eq_mk]; rw [lintegral_congr_ae fg_ae]
  apply lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun h_meas_f.measurabl

Depends on / 依赖: ae_eq_mk, fg_ae, h_indep_fun, h_indep_fun.congr, h_meas_f, h_meas_f.ae_eq_mk, h_meas_f.ae_eq_mk.mul, h_meas_f.measurable_mk, h_meas_f.mk, h_meas_g, h_meas_g.ae_eq_mk, h_meas_g.measurable_mk, h_meas_g.mk, lintegral_congr_ae, lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun, measurable_mk
-/
theorem lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun' (h_meas_f : AEMeasurable f μ)
    (h_meas_g : AEMeasurable g μ) (h_indep_fun : f ⟂ᵢ[μ] g) :
    (∫⁻ ω, (f * g) ω ∂μ) = (∫⁻ ω, f ω ∂μ) * ∫⁻ ω, g ω ∂μ := by
  have fg_ae : f * g =ᵐ[μ] h_meas_f.mk _ * h_meas_g.mk _ := h_meas_f.ae_eq_mk.mul h_meas_g.ae_eq_mk
  rw [lintegral_congr_ae h_meas_f.ae_eq_mk]; rw [lintegral_congr_ae h_meas_g.ae_eq_mk]; rw [lintegral_congr_ae fg_ae]
  apply lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun h_meas_f.measurable_mk
      h_meas_g.measurable_mk
  exact h_indep_fun.congr h_meas_f.ae_eq_mk h_meas_g.ae_eq_mk

/--
theorem `lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun''` / 定理 `lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun''`

English:
theorem lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun''
  statement: (h_meas_f : AEMeasurable f μ)
  proof: lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun' h_meas_f h_meas_g h_indep_fun

中文:
定理 lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun''
  结论: (h_meas_f : AEMeasurable f μ)
  证明: lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun' h_meas_f h_meas_g h_indep_fun

Depends on / 依赖: h_indep_fun, h_meas_f, h_meas_g, lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun
-/
theorem lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun'' (h_meas_f : AEMeasurable f μ)
    (h_meas_g : AEMeasurable g μ) (h_indep_fun : f ⟂ᵢ[μ] g) :
    ∫⁻ ω, f ω * g ω ∂μ = (∫⁻ ω, f ω ∂μ) * ∫⁻ ω, g ω ∂μ :=
  lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun' h_meas_f h_meas_g h_indep_fun

/--
theorem `lintegral_prod_eq_prod_lintegral_of_indepFun` / 定理 `lintegral_prod_eq_prod_lintegral_of_indepFun`

English:
theorem lintegral_prod_eq_prod_lintegral_of_indepFun
  statement: {ι : Type*}
  proof: by
  have : IsProbabilityMeasure μ := hX.isProbabilityMeasure
  induction s using Finset.cons_induction with
  | empty => simp only [Finset.prod_empty, lintegral_const, measure_univ, mul_one]
  | cons j s hj ihs =>
    simp only [← Finset.prod_apply, Finset.prod_cons, ← ihs]
    apply lintegral_mul_

中文:
定理 lintegral_prod_eq_prod_lintegral_of_indepFun
  结论: {ι : 类型}
  证明: by
  have : IsProbabilityMeasure μ := hX.isProbabilityMeasure
  induction s using Finset.cons_induction with
  | empty => simp only [Finset.prod_empty, lintegral_const, measure_univ, mul_one]
  | cons j s hj ihs =>
    simp only [← Finset.prod_apply, Finset.prod_cons, ← ihs]
    apply lintegral_mul_

Depends on / 依赖: Finset, Finset.cons_induction, Finset.prod_apply, Finset.prod_cons, Finset.prod_empty, IsProbabilityMeasure, aemeasurable, aemeasurable_prod, cons_induction, cyclotomic, hX.isProbabilityMeasure, iIndepFun, iIndepFun.indepFun_finsetProd_of_notMem, indepFun_finsetProd_of_notMem, isProbabilityMeasure, lintegral_const, lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun, measure_univ, mul_one, primitiveRoots_zero
-/
theorem lintegral_prod_eq_prod_lintegral_of_indepFun {ι : Type*}
    (s : Finset ι) (X : ι -> Ω -> Real>=0∞) (hX : iIndepFun X μ)
    (x_mea : forall i, Measurable (X i)) :
    ∫⁻ ω, ∏ i in s, (X i ω) ∂μ = ∏ i in s, ∫⁻ ω, X i ω ∂μ := by
  have : IsProbabilityMeasure μ := hX.isProbabilityMeasure
  induction s using Finset.cons_induction with
  | empty => simp only [Finset.prod_empty, lintegral_const, measure_univ, mul_one]
  | cons j s hj ihs =>
    simp only [← Finset.prod_apply, Finset.prod_cons, ← ihs]
    apply lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun'
    · exact (x_mea j).aemeasurable
    · exact s.aemeasurable_prod (fun i _ => (x_mea i).aemeasurable)
    · exact (iIndepFun.indepFun_finsetProd_of_notMem hX x_mea hj).symm

section Integral

variable {𝓧 𝓨 E F G : Type*} [MeasurableSpace 𝓧] [MeasurableSpace 𝓨]

/--
theorem `IndepFun.integrable_op` / 定理 `IndepFun.integrable_op`

English:
theorem IndepFun.integrable_op
  proof: by
  refine ⟨cB.comp_aestronglyMeasurable₂ hX.1 hY.1, ?_⟩
  unfold HasFiniteIntegral
  calc
  _ <= C * ∫⁻ ω, ‖X ω‖ₑ * ‖Y ω‖ₑ ∂μ := by
    rw [← lintegral_const_mul'' _ (by fun_prop)]
    gcongr with ω
    simp [← mul_assoc, hB]
  _ = C * ((∫⁻ ω, ‖X ω‖ₑ ∂μ) * (∫⁻ ω, ‖Y ω‖ₑ ∂μ)) := by
    rw [lintegra

中文:
定理 IndepFun.integrable_op
  证明: by
  refine ⟨cB.comp_aestronglyMeasurable₂ hX.1 hY.1, ?_⟩
  unfold HasFiniteIntegral
  calc
  _ <= C * ∫⁻ ω, ‖X ω‖ₑ * ‖Y ω‖ₑ ∂μ := by
    rw [← lintegral_const_mul'' _ (by fun_prop)]
    gcongr with ω
    simp [← mul_assoc, hB]
  _ = C * ((∫⁻ ω, ‖X ω‖ₑ ∂μ) * (∫⁻ ω, ‖Y ω‖ₑ ∂μ)) := by
    rw [lintegra

Depends on / 依赖: Finset, Finset.prod_singleton, HasFiniteIntegral, IsPrimitiveRoot, IsPrimitiveRoot.primitiveRoots_one, cB.comp_aestronglyMeasurable, cyclotomic, finiteness, fun_prop, hXY.comp, lintegral_const_mul, lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun, map_one, measurable_enorm, mul_assoc, mul_lt_top, primitiveRoots_one, prod_singleton
-/
theorem IndepFun.integrable_op
    [TopologicalSpace E] [ContinuousENorm E] [MeasurableSpace E] [OpensMeasurableSpace E]
    [TopologicalSpace F] [ContinuousENorm F] [MeasurableSpace F] [OpensMeasurableSpace F]
    [TopologicalSpace G] [ContinuousENorm G]
    {X : Ω -> E} {Y : Ω -> F} (hXY : X ⟂ᵢ[μ] Y) (hX : Integrable X μ) (hY : Integrable Y μ)
    (B : E -> F -> G) (cB : Continuous B.uncurry) (C : Real>=0) (hB : forall x y, ‖B x y‖ₑ <= C * ‖x‖ₑ * ‖y‖ₑ) :
    Integrable (fun ω => B (X ω) (Y ω)) μ := by
  refine ⟨cB.comp_aestronglyMeasurable₂ hX.1 hY.1, ?_⟩
  unfold HasFiniteIntegral
  calc
  _ <= C * ∫⁻ ω, ‖X ω‖ₑ * ‖Y ω‖ₑ ∂μ := by
    rw [← lintegral_const_mul'' _ (by fun_prop)]
    gcongr with ω
    simp [← mul_assoc, hB]
  _ = C * ((∫⁻ ω, ‖X ω‖ₑ ∂μ) * (∫⁻ ω, ‖Y ω‖ₑ ∂μ)) := by
    rw [lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun'' hX.1.enorm hY.1.enorm
        (hXY.comp measurable_enorm measurable_enorm)]
  _ < ∞ := mul_lt_top (by finiteness) (mul_lt_top hX.2 hY.2)

/--
theorem `IndepFun.integrable_bilin` / 定理 `IndepFun.integrable_bilin`

English:
theorem IndepFun.integrable_bilin
  statement: {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  proof: by
  refine hXY.integrable_op hX hY (B · ·) (by fun_prop) ‖B‖₊ (fun x y => ?_)
  rw [← toReal_le_toReal (by finiteness) (by finiteness)]
  simp [B.le_opNorm₂]

中文:
定理 IndepFun.integrable_bilin
  结论: {𝕜 : 类型} [NontriviallyNormedField 𝕜]
  证明: by
  refine hXY.integrable_op hX hY (B · ·) (by fun_prop) ‖B‖₊ (fun x y => ?_)
  rw [← toReal_le_toReal (by finiteness) (by finiteness)]
  simp [B.le_opNorm₂]

Depends on / 依赖: B.le_opNorm, Finset, Finset.eq_singleton_iff_unique_mem, Finset.prod_singleton, IsPrimitiveRoot, IsPrimitiveRoot.eq_neg_one_of_two_right, IsPrimitiveRoot.neg_one, cyclotomic, eq_neg_one_of_two_right, eq_singleton_iff_unique_mem, finiteness, fun_prop, hXY.integrable_op, integrable_op, map_neg, map_one, mem_primitiveRoots, neg_one, prim_root_two, primitiveRoots
-/
theorem IndepFun.integrable_bilin {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] [MeasurableSpace E] [OpensMeasurableSpace E]
    [SeminormedAddCommGroup F] [NormedSpace 𝕜 F] [MeasurableSpace F] [OpensMeasurableSpace F]
    [SeminormedAddCommGroup G] [NormedSpace 𝕜 G]
    {X : Ω -> E} {Y : Ω -> F} (hXY : X ⟂ᵢ[μ] Y) (hX : Integrable X μ) (hY : Integrable Y μ)
    (B : E ->L[𝕜] F ->L[𝕜] G) :
    Integrable (fun ω => B (X ω) (Y ω)) μ := by
  refine hXY.integrable_op hX hY (B · ·) (by fun_prop) ‖B‖₊ (fun x y => ?_)
  rw [← toReal_le_toReal (by finiteness) (by finiteness)]
  simp [B.le_opNorm₂]

/--
theorem `IndepFun.integrable_left_of_integrable_op` / 定理 `IndepFun.integrable_left_of_integrable_op`

English:
theorem IndepFun.integrable_left_of_integrable_op
  proof: by
  refine ⟨hX, ?_⟩
  have I : (∫⁻ ω, ‖Y ω‖ₑ ∂μ) != 0 := fun H => by
    have I : (fun ω => ‖Y ω‖ₑ : Ω -> Real>=0∞) =ᵐ[μ] 0 := (lintegral_eq_zero_iff' hY.enorm).1 H
    apply h'Y
    filter_upwards [I] with ω hω
    simpa using hω
refine hasFiniteIntegral_iff_enorm.mpr lt_top_iff_ne_top.2 fun H => 

中文:
定理 IndepFun.integrable_left_of_integrable_op
  证明: by
  refine ⟨hX, ?_⟩
  have I : (∫⁻ ω, ‖Y ω‖ₑ ∂μ) != 0 := fun H => by
    have I : (fun ω => ‖Y ω‖ₑ : Ω -> Real>=0∞) =ᵐ[μ] 0 := (lintegral_eq_zero_iff' hY.enorm).1 H
    apply h'Y
    filter_upwards [I] with ω hω
    simpa using hω
refine hasFiniteIntegral_iff_enorm.mpr lt_top_iff_ne_top.2 fun H => 

Depends on / 依赖: filter_upwards, hXY.comp, hY.enorm, hasFiniteIntegral_iff_enorm, hasFiniteIntegral_iff_enorm.mpr, lintegral_eq_zero_iff, lt_top_iff_ne_top, measurable_enorm, monic_X_sub_C, monic_prod_of_monic, mul_top, top_mul
-/
theorem IndepFun.integrable_left_of_integrable_op
    [TopologicalSpace E] [ContinuousENorm E] [MeasurableSpace E] [OpensMeasurableSpace E]
    [NormedAddGroup F] [MeasurableSpace F] [OpensMeasurableSpace F]
    [TopologicalSpace G] [ContinuousENorm G]
    {X : Ω -> E} {Y : Ω -> F} (hXY : X ⟂ᵢ[μ] Y)
    (B : E -> F -> G) (c : Real>=0) (hc : c != 0) (hB : forall x y, c * ‖x‖ₑ * ‖y‖ₑ <= ‖B x y‖ₑ)
    (h'XY : Integrable (fun ω => B (X ω) (Y ω)) μ)
    (hX : AEStronglyMeasurable X μ) (hY : AEStronglyMeasurable Y μ) (h'Y : ¬Y =ᵐ[μ] 0) :
    Integrable X μ := by
  refine ⟨hX, ?_⟩
  have I : (∫⁻ ω, ‖Y ω‖ₑ ∂μ) != 0 := fun H => by
    have I : (fun ω => ‖Y ω‖ₑ : Ω -> Real>=0∞) =ᵐ[μ] 0 := (lintegral_eq_zero_iff' hY.enorm).1 H
    apply h'Y
    filter_upwards [I] with ω hω
    simpa using hω
refine hasFiniteIntegral_iff_enorm.mpr lt_top_iff_ne_top.2 fun H => ?_
  have J : (‖X ·‖ₑ) ⟂ᵢ[μ] (‖Y ·‖ₑ) := hXY.comp measurable_enorm measurable_enorm
  have : ∞ < ∞ := calc
    ∞ = c * ((∫⁻ ω, ‖X ω‖ₑ ∂μ) * (∫⁻ ω, ‖Y ω‖ₑ ∂μ)) := by
      rw [H]; rw [top_mul I]; rw [mul_top (by simpa)]
    _ <= ∫⁻ ω, ‖B (X ω) (Y ω)‖ₑ ∂μ := by
      rw [← lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun'' hX.enorm hY.enorm J]; rw [← lintegral_const_mul'' _ (by fun_prop)]
      gcongr with ω
      simp [hB, ← mul_assoc]
    _ < ∞ := h'XY.2
  contradiction

/--
theorem `IndepFun.integrable_right_of_integrable_op` / 定理 `IndepFun.integrable_right_of_integrable_op`

English:
theorem IndepFun.integrable_right_of_integrable_op
  proof: by
  refine hXY.symm.integrable_left_of_integrable_op (Function.swap B) c hc (fun y x => ?_)
    h'XY hY hX h'X
  grw [mul_right_comm, hB]

中文:
定理 IndepFun.integrable_right_of_integrable_op
  证明: by
  refine hXY.symm.integrable_left_of_integrable_op (Function.swap B) c hc (fun y x => ?_)
    h'XY hY hX h'X
  grw [mul_right_comm, hB]

Depends on / 依赖: Function, Function.swap, cyclotomic, hXY.symm.integrable_left_of_integrable_op, integrable_left_of_integrable_op, mul_right_comm, ne_zero
-/
theorem IndepFun.integrable_right_of_integrable_op
    [NormedAddGroup E] [MeasurableSpace E] [OpensMeasurableSpace E]
    [TopologicalSpace F] [ContinuousENorm F] [MeasurableSpace F] [OpensMeasurableSpace F]
    [TopologicalSpace G] [ContinuousENorm G]
    {X : Ω -> E} {Y : Ω -> F} (hXY : X ⟂ᵢ[μ] Y)
    (B : E -> F -> G) (c : Real>=0) (hc : c != 0) (hB : forall x y, c * ‖x‖ₑ * ‖y‖ₑ <= ‖B x y‖ₑ)
    (h'XY : Integrable (fun ω => B (X ω) (Y ω)) μ)
    (hX : AEStronglyMeasurable X μ) (hY : AEStronglyMeasurable Y μ) (h'X : ¬X =ᵐ[μ] 0) :
    Integrable Y μ := by
  refine hXY.symm.integrable_left_of_integrable_op (Function.swap B) c hc (fun y x => ?_)
    h'XY hY hX h'X
  grw [mul_right_comm, hB]

/--
theorem `IndepFun.integral_bilin_comp_comp` / 定理 `IndepFun.integral_bilin_comp_comp`

English:
theorem IndepFun.integral_bilin_comp_comp
  proof: by
  by_cases h : forallᵐ ω ∂μ, f (X ω) = 0
  · have h1 : forallᵐ ω ∂μ, B (f (X ω)) (g (Y ω)) = 0 := by
      filter_upwards [h] with ω hω
      simp [hω]
    simp [integral_congr_ae h1, integral_congr_ae h]
  borelize E F
  have : IsProbabilityMeasure μ :=
    (hf.comp_aemeasurable hX).isProbabilit

中文:
定理 IndepFun.integral_bilin_comp_comp
  证明: by
  by_cases h : forallᵐ ω ∂μ, f (X ω) = 0
  · have h1 : forallᵐ ω ∂μ, B (f (X ω)) (g (Y ω)) = 0 := by
      filter_upwards [h] with ω hω
      simp [hω]
    simp [integral_congr_ae h1, integral_congr_ae h]
  borelize E F
  have : IsProbabilityMeasure μ :=
    (hf.comp_aemeasurable hX).isProbabilit

Depends on / 依赖: IsProbabilityMeasure, aemeasurable, borelize, comp_aemeasurable, filter_upwards, fun_prop, hXY.comp, hXY.map_prod_eq_prod_map_map, hf.comp_aemeasurable, integral_congr_ae, integral_map, isProbabilityMeasure_of_indepFun, map_prod_eq_prod_map_map
-/
theorem IndepFun.integral_bilin_comp_comp
    [NormedAddCommGroup E] [NormedSpace Real E] [NormedSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace Real F] [NormedSpace 𝕜 F] [CompleteSpace F]
    [NormedAddCommGroup G] [NormedSpace Real G] [NormedSpace 𝕜 G] [CompleteSpace G]
    {X : Ω -> 𝓧} {Y : Ω -> 𝓨} {f : 𝓧 -> E} {g : 𝓨 -> F} (hXY : X ⟂ᵢ[μ] Y)
    (hX : AEMeasurable X μ) (hY : AEMeasurable Y μ)
    (hf : Integrable f (μ.map X)) (hg : Integrable g (μ.map Y)) (B : E ->L[𝕜] F ->L[𝕜] G) :
    ∫ ω, B (f (X ω)) (g (Y ω)) ∂μ = B (∫ ω, f (X ω) ∂μ) (∫ ω, g (Y ω) ∂μ) := by
  by_cases h : forallᵐ ω ∂μ, f (X ω) = 0
  · have h1 : forallᵐ ω ∂μ, B (f (X ω)) (g (Y ω)) = 0 := by
      filter_upwards [h] with ω hω
      simp [hω]
    simp [integral_congr_ae h1, integral_congr_ae h]
  borelize E F
  have : IsProbabilityMeasure μ :=
    (hf.comp_aemeasurable hX).isProbabilityMeasure_of_indepFun (f ∘ X) (g ∘ Y) h
      (hXY.comp₀ hX hY hf.1.aemeasurable hg.1.aemeasurable)
  rw [← integral_map (f := fun z => B (f z.1) (g z.2)) (φ := fun ω => (X ω]; rw [Y ω)) (by fun_prop)]; rw [hXY.map_prod_eq_prod_map_map hX hY]; rw [integral_prod_bilin _ hf hg]; rw [integral_map hX hf.1]; rw [integral_map hY hg.1]
  rw [hXY.map_prod_eq_prod_map_map hX hY]
  exact Continuous.comp_aestronglyMeasurable₂ (g := (B · ·)) (by fun_prop)
    hf.1.comp_fst hg.1.comp_snd

/--
theorem `IndepFun.integral_bilin_comp_comp'` / 定理 `IndepFun.integral_bilin_comp_comp'`

English:
theorem IndepFun.integral_bilin_comp_comp'
  proof: by
  borelize E F
  have hfXgY := (hXY.comp₀ hX hY hf.aemeasurable hg.aemeasurable)
  have hfX := (hf.comp_aemeasurable hX)
  have hgY := (hg.comp_aemeasurable hY)
  by_cases h'X : forallᵐ ω ∂μ, f (X ω) = 0
  · have h' : forallᵐ ω ∂μ, B (f (X ω)) (g (Y ω)) = 0 := by
      filter_upwards [h'X] with ω

中文:
定理 IndepFun.integral_bilin_comp_comp'
  证明: by
  borelize E F
  have hfXgY := (hXY.comp₀ hX hY hf.aemeasurable hg.aemeasurable)
  have hfX := (hf.comp_aemeasurable hX)
  have hgY := (hg.comp_aemeasurable hY)
  by_cases h'X : forallᵐ ω ∂μ, f (X ω) = 0
  · have h' : forallᵐ ω ∂μ, B (f (X ω)) (g (Y ω)) = 0 := by
      filter_upwards [h'X] with ω

Depends on / 依赖: aemeasurable, borelize, comp_aemeasurable, filter_upwards, hXY.comp, hf.aemeasurable, hf.comp_aemeasurable, hg.aemeasurable, hg.comp_aemeasurable, integra, integral_congr_ae
-/
theorem IndepFun.integral_bilin_comp_comp'
    [NormedAddCommGroup E] [NormedSpace Real E] [NormedSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace Real F] [NormedSpace 𝕜 F] [CompleteSpace F]
    [NormedAddCommGroup G] [NormedSpace Real G] [NormedSpace 𝕜 G] [CompleteSpace G]
    {X : Ω -> 𝓧} {Y : Ω -> 𝓨} {f : 𝓧 -> E} {g : 𝓨 -> F} (hXY : X ⟂ᵢ[μ] Y)
    (hX : AEMeasurable X μ) (hY : AEMeasurable Y μ)
    (hf : AEStronglyMeasurable f (μ.map X)) (hg : AEStronglyMeasurable g (μ.map Y))
    (B : E ->L[𝕜] F ->L[𝕜] G) (c : Real>=0) (hc : c != 0) (hB : forall x y, c * ‖x‖ * ‖y‖ <= ‖B x y‖) :
    ∫ ω, B (f (X ω)) (g (Y ω)) ∂μ = B (∫ ω, f (X ω) ∂μ) (∫ ω, g (Y ω) ∂μ) := by
  borelize E F
  have hfXgY := (hXY.comp₀ hX hY hf.aemeasurable hg.aemeasurable)
  have hfX := (hf.comp_aemeasurable hX)
  have hgY := (hg.comp_aemeasurable hY)
  by_cases h'X : forallᵐ ω ∂μ, f (X ω) = 0
  · have h' : forallᵐ ω ∂μ, B (f (X ω)) (g (Y ω)) = 0 := by
      filter_upwards [h'X] with ω hω
      simp [hω]
    simp [integral_congr_ae h'X, integral_congr_ae h']
  by_cases h'Y : forallᵐ ω ∂μ, g (Y ω) = 0
  · have h' : forallᵐ ω ∂μ, B (f (X ω)) (g (Y ω)) = 0 := by
      filter_upwards [h'Y] with ω hω
      simp [hω]
    simp [integral_congr_ae h'Y, integral_congr_ae h']
  have hB x y : c * ‖x‖ₑ * ‖y‖ₑ <= ‖B x y‖ₑ := by
    rw [← toReal_le_toReal]
    · simpa using hB x y
    all_goals finiteness
  by_cases h : Integrable (fun ω => B (f (X ω)) (g (Y ω))) μ
· have h1 : Integrable f (μ.map X) := (integrable_map_measure hf hX).2
      hfXgY.integrable_left_of_integrable_op (B · ·) c hc hB h hfX hgY h'Y
have h2 : Integrable g (μ.map Y) := (integrable_map_measure hg hY).2
      hfXgY.integrable_right_of_integrable_op (B · ·) c hc hB h hfX hgY h'X
    exact hXY.integral_bilin_comp_comp hX hY h1 h2 B
  · rw [integral_undef h]
    obtain h | h : ¬(Integrable (fun ω => f (X ω)) μ) ∨ ¬(Integrable (fun ω => g (Y ω)) μ) :=
      not_and_or.1 fun ⟨HX, HY⟩ => h (hfXgY.integrable_bilin HX HY B)
    all_goals simp [integral_undef h]

/--
theorem `IndepFun.integral_bilin` / 定理 `IndepFun.integral_bilin`

English:
theorem IndepFun.integral_bilin
  proof: hXY.integral_bilin_comp_comp hX.aemeasurable hY.aemeasurable
    ((integrable_map_measure hX.aestronglyMeasurable.aestronglyMeasurable_id_map hX.aemeasurable).2
      hX)
    ((integrable_map_measure hY.aestronglyMeasurable.aestronglyMeasurable_id_map hY.aemeasurable).2
      hY) B

中文:
定理 IndepFun.integral_bilin
  证明: hXY.integral_bilin_comp_comp hX.aemeasurable hY.aemeasurable
    ((integrable_map_measure hX.aestronglyMeasurable.aestronglyMeasurable_id_map hX.aemeasurable).2
      hX)
    ((integrable_map_measure hY.aestronglyMeasurable.aestronglyMeasurable_id_map hY.aemeasurable).2
      hY) B

Depends on / 依赖: aemeasurable, aestronglyMeasurable, aestronglyMeasurable_id_map, hX.aemeasurable, hX.aestronglyMeasurable.aestronglyMeasurable_id_map, hXY.integral_bilin_comp_comp, hY.aemeasurable, hY.aestronglyMeasurable.aestronglyMeasurable_id_map, integrable_map_measure, integral_bilin_comp_comp
-/
theorem IndepFun.integral_bilin
    [NormedAddCommGroup E] [NormedSpace Real E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup F] [NormedSpace Real F] [CompleteSpace F]
    [MeasurableSpace F] [BorelSpace F]
    [NormedAddCommGroup G] [NormedSpace Real G] [CompleteSpace G]
    {X : Ω -> E} {Y : Ω -> F} (hXY : X ⟂ᵢ[μ] Y) (hX : Integrable X μ) (hY : Integrable Y μ)
    (B : E ->L[Real] F ->L[Real] G) :
    ∫ ω, B (X ω) (Y ω) ∂μ = B μ[X] μ[Y] :=
  hXY.integral_bilin_comp_comp hX.aemeasurable hY.aemeasurable
    ((integrable_map_measure hX.aestronglyMeasurable.aestronglyMeasurable_id_map hX.aemeasurable).2
      hX)
    ((integrable_map_measure hY.aestronglyMeasurable.aestronglyMeasurable_id_map hY.aemeasurable).2
      hY) B

/--
theorem `IndepFun.integral_bilin'` / 定理 `IndepFun.integral_bilin'`

English:
theorem IndepFun.integral_bilin'
  proof: hXY.integral_bilin_comp_comp' hX.aemeasurable hY.aemeasurable
    hX.aestronglyMeasurable_id_map hY.aestronglyMeasurable_id_map B c hc hB

中文:
定理 IndepFun.integral_bilin'
  证明: hXY.integral_bilin_comp_comp' hX.aemeasurable hY.aemeasurable
    hX.aestronglyMeasurable_id_map hY.aestronglyMeasurable_id_map B c hc hB

Depends on / 依赖: aemeasurable, aestronglyMeasurable_id_map, hX.aemeasurable, hX.aestronglyMeasurable_id_map, hXY.integral_bilin_comp_comp, hY.aemeasurable, hY.aestronglyMeasurable_id_map, integral_bilin_comp_comp
-/
theorem IndepFun.integral_bilin'
    [NormedAddCommGroup E] [NormedSpace Real E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup F] [NormedSpace Real F] [CompleteSpace F]
    [MeasurableSpace F] [BorelSpace F]
    [NormedAddCommGroup G] [NormedSpace Real G] [CompleteSpace G]
    {X : Ω -> E} {Y : Ω -> F} (hXY : X ⟂ᵢ[μ] Y) (hX : AEStronglyMeasurable X μ)
    (hY : AEStronglyMeasurable Y μ)
    (B : E ->L[Real] F ->L[Real] G) (c : Real>=0) (hc : c != 0) (hB : forall x y, c * ‖x‖ * ‖y‖ <= ‖B x y‖) :
    ∫ ω, B (X ω) (Y ω) ∂μ = B μ[X] μ[Y] :=
  hXY.integral_bilin_comp_comp' hX.aemeasurable hY.aemeasurable
    hX.aestronglyMeasurable_id_map hY.aestronglyMeasurable_id_map B c hc hB

/--
theorem `IndepFun.integrable_smul` / 定理 `IndepFun.integrable_smul`

English:
theorem IndepFun.integrable_smul
  proof: hXY.integrable_op hX hY (· • ·) (by fun_prop) 1 (by simp [enorm_smul])

中文:
定理 IndepFun.integrable_smul
  证明: hXY.integrable_op hX hY (· • ·) (by fun_prop) 1 (by simp [enorm_smul])

Depends on / 依赖: Splits, Splits.X_sub_C, Splits.prod, X_sub_C, enorm_smul, fun_prop, hXY.integrable_op, integrable_op
-/
theorem IndepFun.integrable_smul
    [TopologicalSpace E] [ContinuousENorm E] [MeasurableSpace E] [OpensMeasurableSpace E]
    [TopologicalSpace F] [ContinuousENorm F] [MeasurableSpace F] [OpensMeasurableSpace F]
    [SMul E F] [ContinuousSMul E F] [ENormSMulClass E F]
    {X : Ω -> E} {Y : Ω -> F} (hXY : X ⟂ᵢ[μ] Y) (hX : Integrable X μ) (hY : Integrable Y μ) :
    Integrable (fun ω => (X ω) • (Y ω)) μ :=
  hXY.integrable_op hX hY (· • ·) (by fun_prop) 1 (by simp [enorm_smul])

/--
theorem `IndepFun.integrable_mul` / 定理 `IndepFun.integrable_mul`

English:
theorem IndepFun.integrable_mul
  proof: hXY.integrable_smul hX hY

@[deprecated (since := "2026-04-30")] alias IndepFun.integrable_left_of_integrable_mul :=
  IndepFun.integrable_left_of_integrable_op

@[deprecated (since := "2026-04-30")] alias IndepFun.integrable_right_of_integrable_mul :=
  IndepFun.integrable_right_of_integrable_op

中文:
定理 IndepFun.integrable_mul
  证明: hXY.integrable_smul hX hY

@[deprecated (since := "2026-04-30")] alias IndepFun.integrable_left_of_integrable_mul :=
  IndepFun.integrable_left_of_integrable_op

@[deprecated (since := "2026-04-30")] alias IndepFun.integrable_right_of_integrable_mul :=
  IndepFun.integrable_right_of_integrable_op

Depends on / 依赖: hXY.integrable_smul, integrable_smul
-/
theorem IndepFun.integrable_mul
    [TopologicalSpace E] [ContinuousENorm E] [Mul E] [ContinuousMul E] [ENormSMulClass E E]
    [MeasurableSpace E] [OpensMeasurableSpace E]
    {X Y : Ω -> E} (hXY : X ⟂ᵢ[μ] Y) (hX : Integrable X μ) (hY : Integrable Y μ) :
    Integrable (X * Y) μ := hXY.integrable_smul hX hY

@[deprecated (since := "2026-04-30")] alias IndepFun.integrable_left_of_integrable_mul :=
  IndepFun.integrable_left_of_integrable_op

@[deprecated (since := "2026-04-30")] alias IndepFun.integrable_right_of_integrable_mul :=
  IndepFun.integrable_right_of_integrable_op

/--
lemma `IndepFun.integral_fun_comp_smul_comp` / 引理 `IndepFun.integral_fun_comp_smul_comp`

English:
lemma IndepFun.integral_fun_comp_smul_comp
  proof: by
  by_cases hE : CompleteSpace E
  · exact hXY.integral_bilin_comp_comp' hX hY hf hg (.lsmul Real 𝕜) 1 (by simp) (by simp [norm_smul])
  · simp [integral, hE]

中文:
引理 IndepFun.integral_fun_comp_smul_comp
  证明: by
  by_cases hE : CompleteSpace E
  · exact hXY.integral_bilin_comp_comp' hX hY hf hg (.lsmul Real 𝕜) 1 (by simp) (by simp [norm_smul])
  · simp [integral, hE]

Depends on / 依赖: CompleteSpace, hXY.integral_bilin_comp_comp, integral, integral_bilin_comp_comp, norm_smul
-/
lemma IndepFun.integral_fun_comp_smul_comp
    [NormedAddCommGroup E] [NormedSpace Real E] [NormedSpace 𝕜 E]
    {X : Ω -> 𝓧} {Y : Ω -> 𝓨} {f : 𝓧 -> 𝕜} {g : 𝓨 -> E}
    (hXY : X ⟂ᵢ[μ] Y) (hX : AEMeasurable X μ) (hY : AEMeasurable Y μ)
    (hf : AEStronglyMeasurable f (μ.map X)) (hg : AEStronglyMeasurable g (μ.map Y)) :
    ∫ ω, f (X ω) • g (Y ω) ∂μ = (∫ ω, f (X ω) ∂μ) • (∫ ω, g (Y ω) ∂μ) := by
  by_cases hE : CompleteSpace E
  · exact hXY.integral_bilin_comp_comp' hX hY hf hg (.lsmul Real 𝕜) 1 (by simp) (by simp [norm_smul])
  · simp [integral, hE]

/--
lemma `IndepFun.integral_fun_comp_mul_comp` / 引理 `IndepFun.integral_fun_comp_mul_comp`

English:
lemma IndepFun.integral_fun_comp_mul_comp
  proof: hXY.integral_fun_comp_smul_comp hX hY hf hg

中文:
引理 IndepFun.integral_fun_comp_mul_comp
  证明: hXY.integral_fun_comp_smul_comp hX hY hf hg

Depends on / 依赖: Finset, Finset.prod_cons, Monic.ne_zero, Nat.cons_self_properDivisors, Nat.properDivisors, _eq_X_pow_sub_one, bot_lt_iff_ne_bot, cons_self_properDivisors, cyclotomic, degree_eq_bot, degree_zero, div_modByMonic_unique, hXY.integral_fun_comp_smul_comp, hpos.ne, integral_fun_comp_smul_comp, monic_prod_of_monic, mul_comm, ne_zero, prod_cons, prod_cyclotomic
-/
lemma IndepFun.integral_fun_comp_mul_comp
    {X : Ω -> 𝓧} {Y : Ω -> 𝓨} {f : 𝓧 -> 𝕜} {g : 𝓨 -> 𝕜}
    (hXY : X ⟂ᵢ[μ] Y) (hX : AEMeasurable X μ) (hY : AEMeasurable Y μ)
    (hf : AEStronglyMeasurable f (μ.map X)) (hg : AEStronglyMeasurable g (μ.map Y)) :
    ∫ ω, f (X ω) * g (Y ω) ∂μ = (∫ ω, f (X ω) ∂μ) * (∫ ω, g (Y ω) ∂μ) :=
  hXY.integral_fun_comp_smul_comp hX hY hf hg

/--
lemma `IndepFun.integral_comp_smul_comp` / 引理 `IndepFun.integral_comp_smul_comp`

English:
lemma IndepFun.integral_comp_smul_comp
  proof: hXY.integral_fun_comp_smul_comp hX hY hf hg

中文:
引理 IndepFun.integral_comp_smul_comp
  证明: hXY.integral_fun_comp_smul_comp hX hY hf hg

Depends on / 依赖: hXY.integral_fun_comp_smul_comp, integral_fun_comp_smul_comp
-/
lemma IndepFun.integral_comp_smul_comp
    [NormedAddCommGroup E] [NormedSpace Real E] [NormedSpace 𝕜 E]
    {X : Ω -> 𝓧} {Y : Ω -> 𝓨} {f : 𝓧 -> 𝕜} {g : 𝓨 -> E}
    (hXY : X ⟂ᵢ[μ] Y) (hX : AEMeasurable X μ) (hY : AEMeasurable Y μ)
    (hf : AEStronglyMeasurable f (μ.map X)) (hg : AEStronglyMeasurable g (μ.map Y)) :
    μ[(f ∘ X) • (g ∘ Y)] = μ[f ∘ X] • μ[g ∘ Y] :=
  hXY.integral_fun_comp_smul_comp hX hY hf hg

/--
lemma `IndepFun.integral_comp_mul_comp` / 引理 `IndepFun.integral_comp_mul_comp`

English:
lemma IndepFun.integral_comp_mul_comp
  proof: hXY.integral_fun_comp_mul_comp hX hY hf hg

中文:
引理 IndepFun.integral_comp_mul_comp
  证明: hXY.integral_fun_comp_mul_comp hX hY hf hg

Depends on / 依赖: hXY.integral_fun_comp_mul_comp, integral_fun_comp_mul_comp
-/
lemma IndepFun.integral_comp_mul_comp
    {X : Ω -> 𝓧} {Y : Ω -> 𝓨} {f : 𝓧 -> 𝕜} {g : 𝓨 -> 𝕜}
    (hXY : X ⟂ᵢ[μ] Y) (hX : AEMeasurable X μ) (hY : AEMeasurable Y μ)
    (hf : AEStronglyMeasurable f (μ.map X)) (hg : AEStronglyMeasurable g (μ.map Y)) :
    μ[(f ∘ X) * (g ∘ Y)] = μ[f ∘ X] * μ[g ∘ Y] :=
  hXY.integral_fun_comp_mul_comp hX hY hf hg

/--
lemma `IndepFun.integral_smul_eq_smul_integral` / 引理 `IndepFun.integral_smul_eq_smul_integral`

English:
lemma IndepFun.integral_smul_eq_smul_integral
  proof: by
  by_cases hE : CompleteSpace E
  · exact hXY.integral_bilin' hX hY (.lsmul Real 𝕜) 1 (by simp) (by simp [norm_smul])
  · simp [integral, hE]

中文:
引理 IndepFun.integral_smul_eq_smul_integral
  证明: by
  by_cases hE : CompleteSpace E
  · exact hXY.integral_bilin' hX hY (.lsmul Real 𝕜) 1 (by simp) (by simp [norm_smul])
  · simp [integral, hE]

Depends on / 依赖: CompleteSpace, hXY.integral_bilin, integral, integral_bilin, norm_smul
-/
lemma IndepFun.integral_smul_eq_smul_integral
    [NormedAddCommGroup E] [NormedSpace Real E] [NormedSpace 𝕜 E] [MeasurableSpace E] [BorelSpace E]
    {X : Ω -> 𝕜} {Y : Ω -> E} (hXY : X ⟂ᵢ[μ] Y)
    (hX : AEStronglyMeasurable X μ) (hY : AEStronglyMeasurable Y μ) :
    μ[X • Y] = μ[X] • μ[Y] := by
  by_cases hE : CompleteSpace E
  · exact hXY.integral_bilin' hX hY (.lsmul Real 𝕜) 1 (by simp) (by simp [norm_smul])
  · simp [integral, hE]

/--
lemma `IndepFun.integral_mul_eq_mul_integral` / 引理 `IndepFun.integral_mul_eq_mul_integral`

English:
lemma IndepFun.integral_mul_eq_mul_integral
  proof: hXY.integral_smul_eq_smul_integral hX hY

中文:
引理 IndepFun.integral_mul_eq_mul_integral
  证明: hXY.integral_smul_eq_smul_integral hX hY

Depends on / 依赖: hXY.integral_smul_eq_smul_integral, integral_smul_eq_smul_integral
-/
lemma IndepFun.integral_mul_eq_mul_integral
    (hXY : X ⟂ᵢ[μ] Y) (hX : AEStronglyMeasurable X μ) (hY : AEStronglyMeasurable Y μ) :
    μ[X * Y] = μ[X] * μ[Y] :=
  hXY.integral_smul_eq_smul_integral hX hY

/--
lemma `IndepFun.integral_fun_smul_eq_smul_integral` / 引理 `IndepFun.integral_fun_smul_eq_smul_integral`

English:
lemma IndepFun.integral_fun_smul_eq_smul_integral
  proof: hXY.integral_smul_eq_smul_integral hX hY

中文:
引理 IndepFun.integral_fun_smul_eq_smul_integral
  证明: hXY.integral_smul_eq_smul_integral hX hY

Depends on / 依赖: hXY.integral_smul_eq_smul_integral, integral_smul_eq_smul_integral
-/
lemma IndepFun.integral_fun_smul_eq_smul_integral
    [NormedAddCommGroup E] [NormedSpace Real E] [NormedSpace 𝕜 E] [MeasurableSpace E] [BorelSpace E]
    {X : Ω -> 𝕜} {Y : Ω -> E} (hXY : X ⟂ᵢ[μ] Y)
    (hX : AEStronglyMeasurable X μ) (hY : AEStronglyMeasurable Y μ) :
    ∫ ω, X ω • Y ω ∂μ = (∫ ω, X ω ∂μ) • ∫ ω, Y ω ∂μ :=
  hXY.integral_smul_eq_smul_integral hX hY

/--
lemma `IndepFun.integral_fun_mul_eq_mul_integral` / 引理 `IndepFun.integral_fun_mul_eq_mul_integral`

English:
lemma IndepFun.integral_fun_mul_eq_mul_integral
  proof: hXY.integral_fun_smul_eq_smul_integral hX hY

中文:
引理 IndepFun.integral_fun_mul_eq_mul_integral
  证明: hXY.integral_fun_smul_eq_smul_integral hX hY

Depends on / 依赖: hXY.integral_fun_smul_eq_smul_integral, integral_fun_smul_eq_smul_integral
-/
lemma IndepFun.integral_fun_mul_eq_mul_integral
    (hXY : X ⟂ᵢ[μ] Y) (hX : AEStronglyMeasurable X μ) (hY : AEStronglyMeasurable Y μ) :
    ∫ ω, X ω * Y ω ∂μ = μ[X] * μ[Y] :=
  hXY.integral_fun_smul_eq_smul_integral hX hY

end Integral

/--
theorem `indepFun_iff_integral_comp_mul` / 定理 `indepFun_iff_integral_comp_mul`

English:
theorem indepFun_iff_integral_comp_mul
  statement: [IsFiniteMeasure μ] {β β' : Type*} {mβ : MeasurableSpace β}
  proof: by
  refine ⟨fun hfg _ _ hφ hψ _ _ => hfg.integral_comp_mul_comp
      hfm.aemeasurable hgm.aemeasurable hφ.aestronglyMeasurable hψ.aestronglyMeasurable, ?_⟩
  rw [IndepFun_iff]
  rintro h _ _ ⟨A, hA, rfl⟩ ⟨B, hB, rfl⟩
  specialize
    h (measurable_one.indicator hA) (measurable_one.indicator hB)
  

中文:
定理 indepFun_iff_integral_comp_mul
  结论: [IsFiniteMeasure μ] {β β' : 类型} {mβ : MeasurableSpace β}
  证明: by
  refine ⟨fun hfg _ _ hφ hψ _ _ => hfg.integral_comp_mul_comp
      hfm.aemeasurable hgm.aemeasurable hφ.aestronglyMeasurable hψ.aestronglyMeasurable, ?_⟩
  rw [IndepFun_iff]
  rintro h _ _ ⟨A, hA, rfl⟩ ⟨B, hB, rfl⟩
  specialize
    h (measurable_one.indicator hA) (measurable_one.indicator hB)
  

Depends on / 依赖: IndepFun_iff, aemeasurable, aestronglyMeasurable, hfg.integral_comp_mul_comp, hfm.aemeasurable, hfm.comp, hgm.aemeasurable, hgm.comp, indicator, integrable_const, integral_comp_mul_comp, measurable_id, measurable_one, measurable_one.indicator, measureReal_de, measureReal_def, measure_ne_top, specialize, toReal_eq_toReal_iff, toReal_mul
-/
theorem indepFun_iff_integral_comp_mul [IsFiniteMeasure μ] {β β' : Type*} {mβ : MeasurableSpace β}
    {mβ' : MeasurableSpace β'} {f : Ω -> β} {g : Ω -> β'} {hfm : Measurable f} {hgm : Measurable g} :
    f ⟂ᵢ[μ] g ↔ forall {φ : β -> Real} {ψ : β' -> Real}, Measurable φ -> Measurable ψ ->
      Integrable (φ ∘ f) μ -> Integrable (ψ ∘ g) μ ->
        integral μ (φ ∘ f * ψ ∘ g) = integral μ (φ ∘ f) * integral μ (ψ ∘ g) := by
  refine ⟨fun hfg _ _ hφ hψ _ _ => hfg.integral_comp_mul_comp
      hfm.aemeasurable hgm.aemeasurable hφ.aestronglyMeasurable hψ.aestronglyMeasurable, ?_⟩
  rw [IndepFun_iff]
  rintro h _ _ ⟨A, hA, rfl⟩ ⟨B, hB, rfl⟩
  specialize
    h (measurable_one.indicator hA) (measurable_one.indicator hB)
      ((integrable_const 1).indicator (hfm.comp measurable_id hA))
      ((integrable_const 1).indicator (hgm.comp measurable_id hB))
  rwa [← toReal_eq_toReal_iff' (measure_ne_top μ _), toReal_mul, ← measureReal_def,
    ← measureReal_def, ← measureReal_def, ← integral_indicator_one ((hfm hA).inter (hgm hB)),
    ← integral_indicator_one (hfm hA), ← integral_indicator_one (hgm hB), Set.inter_indicator_one]
  exact mul_ne_top (measure_ne_top μ _) (measure_ne_top μ _)

variable {ι : Type*} [Fintype ι] {𝓧 : ι -> Type*} {m𝓧 : forall i, MeasurableSpace (𝓧 i)}
    {X : (i : ι) -> Ω -> 𝓧 i} {f : (i : ι) -> 𝓧 i -> 𝕜}

/--
lemma `iIndepFun.integral_fun_prod_comp` / 引理 `iIndepFun.integral_fun_prod_comp`

English:
lemma iIndepFun.integral_fun_prod_comp
  statement: (hX : iIndepFun X μ)
  proof: by
  have := hX.isProbabilityMeasure
  change ∫ ω, (fun x => ∏ i, f i (x i)) (X · ω) ∂μ = _
  rw [← integral_map (f := fun x => ∏ i]; rw [f i (x i)) (φ := fun ω => (X · ω))]; rw [hX.map_fun_eq_pi_map mX]; rw [integral_fintype_prod_eq_prod]
  · congr with i
    rw [integral_map (mX i) (hf i)]
  · fun

中文:
引理 iIndepFun.integral_fun_prod_comp
  结论: (hX : iIndepFun X μ)
  证明: by
  have := hX.isProbabilityMeasure
  change ∫ ω, (fun x => ∏ i, f i (x i)) (X · ω) ∂μ = _
  rw [← integral_map (f := fun x => ∏ i]; rw [f i (x i)) (φ := fun ω => (X · ω))]; rw [hX.map_fun_eq_pi_map mX]; rw [integral_fintype_prod_eq_prod]
  · congr with i
    rw [integral_map (mX i) (hf i)]
  · fun

Depends on / 依赖: Finset, Finset.aestronglyMeasurable_fun_prod, Finset.univ, Measure, Measure.quasiMeasurePreserving_eval, aestronglyMeasurable_fun_prod, comp_quasiMeasurePreserving, fun_prop, hX.isProbabilityMeasure, hX.map_fun_eq_pi_map, integral_fintype_prod_eq_prod, integral_map, isProbabilityMeasure, map_fun_eq_pi_map, quasiMeasurePreserving_eval
-/
lemma iIndepFun.integral_fun_prod_comp (hX : iIndepFun X μ)
    (mX : forall i, AEMeasurable (X i) μ) (hf : forall i, AEStronglyMeasurable (f i) (μ.map (X i))) :
    ∫ ω, ∏ i, f i (X i ω) ∂μ = ∏ i, ∫ ω, f i (X i ω) ∂μ := by
  have := hX.isProbabilityMeasure
  change ∫ ω, (fun x => ∏ i, f i (x i)) (X · ω) ∂μ = _
  rw [← integral_map (f := fun x => ∏ i]; rw [f i (x i)) (φ := fun ω => (X · ω))]; rw [hX.map_fun_eq_pi_map mX]; rw [integral_fintype_prod_eq_prod]
  · congr with i
    rw [integral_map (mX i) (hf i)]
  · fun_prop
  rw [hX.map_fun_eq_pi_map mX]
  exact Finset.aestronglyMeasurable_fun_prod Finset.univ fun i _ =>
    (hf i).comp_quasiMeasurePreserving (Measure.quasiMeasurePreserving_eval _ i)

/--
lemma `iIndepFun.integral_prod_comp` / 引理 `iIndepFun.integral_prod_comp`

English:
lemma iIndepFun.integral_prod_comp
  statement: (hX : iIndepFun X μ)
  proof: by
  convert! hX.integral_fun_prod_comp mX hf
  simp

中文:
引理 iIndepFun.integral_prod_comp
  结论: (hX : iIndepFun X μ)
  证明: by
  convert! hX.integral_fun_prod_comp mX hf
  simp

Depends on / 依赖: convert, hX.integral_fun_prod_comp, integral_fun_prod_comp
-/
lemma iIndepFun.integral_prod_comp (hX : iIndepFun X μ)
    (mX : forall i, AEMeasurable (X i) μ) (hf : forall i, AEStronglyMeasurable (f i) (μ.map (X i))) :
    μ[∏ i, (f i) ∘ (X i)] = ∏ i, μ[(f i) ∘ (X i)] := by
  convert! hX.integral_fun_prod_comp mX hf
  simp

variable {X : (i : ι) -> Ω -> 𝕜}

/--
lemma `iIndepFun.integral_prod_eq_prod_integral` / 引理 `iIndepFun.integral_prod_eq_prod_integral`

English:
lemma iIndepFun.integral_prod_eq_prod_integral
  proof: hX.integral_prod_comp (fun i => (mX i).aemeasurable) (fun _ => aestronglyMeasurable_id)

中文:
引理 iIndepFun.integral_prod_eq_prod_integral
  证明: hX.integral_prod_comp (fun i => (mX i).aemeasurable) (fun _ => aestronglyMeasurable_id)

Depends on / 依赖: aemeasurable, aestronglyMeasurable_id, hX.integral_prod_comp, integral_prod_comp
-/
lemma iIndepFun.integral_prod_eq_prod_integral
    (hX : iIndepFun X μ) (mX : forall i, AEStronglyMeasurable (X i) μ) :
    μ[∏ i, X i] = ∏ i, μ[X i] :=
  hX.integral_prod_comp (fun i => (mX i).aemeasurable) (fun _ => aestronglyMeasurable_id)

/--
lemma `iIndepFun.integral_fun_prod_eq_prod_integral` / 引理 `iIndepFun.integral_fun_prod_eq_prod_integral`

English:
lemma iIndepFun.integral_fun_prod_eq_prod_integral
  proof: hX.integral_fun_prod_comp (fun i => (mX i).aemeasurable) (fun _ => aestronglyMeasurable_id)

中文:
引理 iIndepFun.integral_fun_prod_eq_prod_integral
  证明: hX.integral_fun_prod_comp (fun i => (mX i).aemeasurable) (fun _ => aestronglyMeasurable_id)

Depends on / 依赖: aemeasurable, aestronglyMeasurable_id, hX.integral_fun_prod_comp, integral_fun_prod_comp
-/
lemma iIndepFun.integral_fun_prod_eq_prod_integral
    (hX : iIndepFun X μ) (mX : forall i, AEStronglyMeasurable (X i) μ) :
    ∫ ω, ∏ i, X i ω ∂μ = ∏ i, μ[X i] :=
  hX.integral_fun_prod_comp (fun i => (mX i).aemeasurable) (fun _ => aestronglyMeasurable_id)

section SetIntegral

variable {Ω 𝓧 : Type*} {m mΩ : MeasurableSpace Ω} {P : Measure Ω} [m𝓧 : MeasurableSpace 𝓧]
  {X : Ω -> 𝓧} {A : Set Ω}

/--
lemma `Indep.setIntegral_eq_smul` / 引理 `Indep.setIntegral_eq_smul`

English:
lemma Indep.setIntegral_eq_smul
  statement: {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  proof: calc ∫ ω in A, f (X ω) ∂P
    = ∫ ω, id (A.indicator (1 : Ω -> Real) ω) • f (X ω) ∂P := by
        rw [← integral_indicator (hm A hA2)]
        congr with ω
        by_cases hω : ω in A <;> simp [hω]
  _ = P.real A • ∫ ω, f (X ω) ∂P := by
    rw [IndepFun.integral_fun_comp_smul_comp _ _ hX (by fun_p

中文:
引理 Indep.setIntegral_eq_smul
  结论: {E : 类型} [NormedAddCommGroup E] [NormedSpace 实数 E]
  证明: calc ∫ ω in A, f (X ω) ∂P
    = ∫ ω, id (A.indicator (1 : Ω -> Real) ω) • f (X ω) ∂P := by
        rw [← integral_indicator (hm A hA2)]
        congr with ω
        by_cases hω : ω in A <;> simp [hω]
  _ = P.real A • ∫ ω, f (X ω) ∂P := by
    rw [IndepFun.integral_fun_comp_smul_comp _ _ hX (by fun_p

Depends on / 依赖: A.indicator, IndepFun, IndepFun.integral_fun_comp_smul_comp, P.real, aemeasurable_indicator_const_iff, fun_prop, hA1.indicator_indepFun, indicator, indicator_indepFun, integral_fun_comp_smul_comp, integral_indicator, nullMeasurableSet
-/
lemma Indep.setIntegral_eq_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    (hm : m <= mΩ) {f : 𝓧 -> E} (hA1 : Indep m (m𝓧.comap X) P)
    (hX : AEMeasurable X P) (hA2 : MeasurableSet[m] A)
    (hf : AEStronglyMeasurable f (P.map X)) :
    ∫ ω in A, f (X ω) ∂P = P.real A • ∫ ω, f (X ω) ∂P :=
  calc ∫ ω in A, f (X ω) ∂P
    = ∫ ω, id (A.indicator (1 : Ω -> Real) ω) • f (X ω) ∂P := by
        rw [← integral_indicator (hm A hA2)]
        congr with ω
        by_cases hω : ω in A <;> simp [hω]
  _ = P.real A • ∫ ω, f (X ω) ∂P := by
    rw [IndepFun.integral_fun_comp_smul_comp _ _ hX (by fun_prop) hf]
    · simp [hm A hA2]
    · exact hA1.indicator_indepFun 1 hA2
    · exact (aemeasurable_indicator_const_iff 1).2 (hm A hA2).nullMeasurableSet

/--
lemma `Indep.setIntegral_eq_mul` / 引理 `Indep.setIntegral_eq_mul`

English:
lemma Indep.setIntegral_eq_mul
  statement: (hm : m <= mΩ) {f : 𝓧 -> Real} (hA1 : Indep m (m𝓧.comap X) P)
  proof: hA1.setIntegral_eq_smul hm hX hA hf

中文:
引理 Indep.setIntegral_eq_mul
  结论: (hm : m <= mΩ) {f : 𝓧 -> 实数} (hA1 : Indep m (m𝓧.comap X) P)
  证明: hA1.setIntegral_eq_smul hm hX hA hf

Depends on / 依赖: hA1.setIntegral_eq_smul, setIntegral_eq_smul
-/
lemma Indep.setIntegral_eq_mul (hm : m <= mΩ) {f : 𝓧 -> Real} (hA1 : Indep m (m𝓧.comap X) P)
    (hX : AEMeasurable X P) (hA : MeasurableSet[m] A)
    (hf : AEStronglyMeasurable f (P.map X)) :
    ∫ ω in A, f (X ω) ∂P = P.real A * ∫ ω, f (X ω) ∂P :=
  hA1.setIntegral_eq_smul hm hX hA hf

end SetIntegral

end ProbabilityTheory
