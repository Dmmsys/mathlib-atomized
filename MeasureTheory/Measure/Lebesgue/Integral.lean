/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Sébastien Gouëzel, Yury Kudryashov
-/
module

public import Mathlib.MeasureTheory.Measure.Haar.Unique

/-! # Properties of integration with respect to the Lebesgue measure -/

public section


open Set Filter MeasureTheory MeasureTheory.Measure TopologicalSpace

section regionBetween

variable {α : Type*}
variable [MeasurableSpace α] {μ : Measure α} {f g : α -> Real} {s : Set α}

/--
theorem `volume_regionBetween_eq_integral'` / 定理 `volume_regionBetween_eq_integral'`

English:
theorem volume_regionBetween_eq_integral'
  statement: [SigmaFinite μ] (f_int : IntegrableOn f s μ)
  proof: by
  have h : g - f =ᵐ[μ.restrict s] fun x => Real.toNNReal (g x - f x) :=
    hfg.mono fun x hx => (Real.coe_toNNReal _ <| sub_nonneg.2 hx).symm
  rw [volume_regionBetween_eq_lintegral f_int.aemeasurable g_int.aemeasurable hs]; rw [integral_congr_ae h]; rw [lintegral_congr_ae]; rw [lintegral_coe_eq

中文:
定理 volume_regionBetween_eq_integral'
  结论: [σ有限 μ] (f_int : 整数egrableOn f s μ)
  证明: by
  have h : g - f =ᵐ[μ.restrict s] fun x => Real.toNNReal (g x - f x) :=
    hfg.mono fun x hx => (Real.coe_toNNReal _ <| sub_nonneg.2 hx).symm
  rw [volume_regionBetween_eq_lintegral f_int.aemeasurable g_int.aemeasurable hs]; rw [integral_congr_ae h]; rw [lintegral_congr_ae]; rw [lintegral_coe_eq

Depends on / 依赖: Real.coe_toNNReal, Real.toNNReal, aemeasurable, coe_toNNReal, f_int, f_int.aemeasurable, g_int, g_int.aemeasurable, g_int.sub, hfg.mono, integrable_congr, integral_congr_ae, lintegral_coe_eq_integral, lintegral_congr_ae, restrict, sub_nonneg, toNNReal, volume_regionBetween_eq_lintegral
-/
theorem volume_regionBetween_eq_integral' [SigmaFinite μ] (f_int : IntegrableOn f s μ)
    (g_int : IntegrableOn g s μ) (hs : MeasurableSet s) (hfg : f <=ᵐ[μ.restrict s] g) :
    μ.prod volume (regionBetween f g s) = ENNReal.ofReal (∫ y in s, (g - f) y ∂μ) := by
  have h : g - f =ᵐ[μ.restrict s] fun x => Real.toNNReal (g x - f x) :=
    hfg.mono fun x hx => (Real.coe_toNNReal _ <| sub_nonneg.2 hx).symm
  rw [volume_regionBetween_eq_lintegral f_int.aemeasurable g_int.aemeasurable hs]; rw [integral_congr_ae h]; rw [lintegral_congr_ae]; rw [lintegral_coe_eq_integral _ ((integrable_congr h).mp (g_int.sub f_int))]
  rfl

/--
theorem `volume_regionBetween_eq_integral` / 定理 `volume_regionBetween_eq_integral`

English:
theorem volume_regionBetween_eq_integral
  statement: [SigmaFinite μ] (f_int : IntegrableOn f s μ)
  proof: volume_regionBetween_eq_integral' f_int g_int hs
    ((ae_restrict_iff' hs).mpr (Eventually.of_forall hfg))

中文:
定理 volume_regionBetween_eq_integral
  结论: [σ有限 μ] (f_int : 整数egrableOn f s μ)
  证明: volume_regionBetween_eq_integral' f_int g_int hs
    ((ae_restrict_iff' hs).mpr (Eventually.of_forall hfg))

Depends on / 依赖: Eventually, Eventually.of_forall, ae_restrict_iff, f_int, g_int, of_forall, volume_regionBetween_eq_integral
-/
theorem volume_regionBetween_eq_integral [SigmaFinite μ] (f_int : IntegrableOn f s μ)
    (g_int : IntegrableOn g s μ) (hs : MeasurableSet s) (hfg : forall x in s, f x <= g x) :
    μ.prod volume (regionBetween f g s) = ENNReal.ofReal (∫ y in s, (g - f) y ∂μ) :=
  volume_regionBetween_eq_integral' f_int g_int hs
    ((ae_restrict_iff' hs).mpr (Eventually.of_forall hfg))

end regionBetween

section SummableNormIcc

open ContinuousMap

/- The following lemma is a minor variation on `integrable_of_summable_norm_restrict` in
`Mathlib/MeasureTheory/Integral/Bochner/Set.lean`, but it is placed here because it needs to know
that `Icc a b` has volume `b - a`. -/
/--
theorem `Real.integrable_of_summable_norm_Icc` / 定理 `Real.integrable_of_summable_norm_Icc`

English:
theorem Real.integrable_of_summable_norm_Icc
  statement: {E : Type*} [NormedAddCommGroup E] {f : C(Real, E)}
  proof: by
  refine integrable_of_summable_norm_restrict (.of_nonneg_of_le
    (fun n : Int => mul_nonneg (norm_nonneg
      (f.restrict (⟨Icc (n : Real) ((n : Real) + 1), isCompact_Icc⟩ : Compacts Real)))
        ENNReal.toReal_nonneg) (fun n => ?_) hf) ?_
  · simp only [Compacts.coe_mk, le_add_iff_nonneg_

中文:
定理 实数.integrable_of_summable_norm_Icc
  结论: {E : 类型} [赋范交换加群 E] {f : C(实数, E)}
  证明: by
  refine integrable_of_summable_norm_restrict (.of_nonneg_of_le
    (fun n : Int => mul_nonneg (norm_nonneg
      (f.restrict (⟨Icc (n : Real) ((n : Real) + 1), isCompact_Icc⟩ : Compacts Real)))
        ENNReal.toReal_nonneg) (fun n => ?_) hf) ?_
  · simp only [Compacts.coe_mk, le_add_iff_nonneg_

Depends on / 依赖: Compacts, Compacts.coe_mk, ContinuousMap, ContinuousMap.addRight, ContinuousMap.restrict_apply, ENNReal, ENNReal.toReal_nonneg, addRight, add_sub_cancel_left, coe_mk, f.comp, f.restrict, integrable_of_summable_norm_restrict, isCompact_Icc, le_add_iff_nonneg_right, mul_nonneg, mul_one, norm_coe_le_norm, norm_le, norm_nonneg
-/
theorem Real.integrable_of_summable_norm_Icc {E : Type*} [NormedAddCommGroup E] {f : C(Real, E)}
    (hf : Summable fun n : Int => ‖(f.comp <| ContinuousMap.addRight n).restrict (Icc 0 1)‖) :
    Integrable f := by
  refine integrable_of_summable_norm_restrict (.of_nonneg_of_le
    (fun n : Int => mul_nonneg (norm_nonneg
      (f.restrict (⟨Icc (n : Real) ((n : Real) + 1), isCompact_Icc⟩ : Compacts Real)))
        ENNReal.toReal_nonneg) (fun n => ?_) hf) ?_
  · simp only [Compacts.coe_mk, le_add_iff_nonneg_right, zero_le_one, volume_real_Icc_of_le,
      add_sub_cancel_left, mul_one, norm_le _ (norm_nonneg _), ContinuousMap.restrict_apply]
    intro x
    have := ((f.comp <| ContinuousMap.addRight n).restrict (Icc 0 1)).norm_coe_le_norm
        ⟨x - n, ⟨sub_nonneg.mpr x.2.1, sub_le_iff_le_add'.mpr x.2.2⟩⟩
    simpa only [ContinuousMap.restrict_apply, comp_apply, coe_addRight, Subtype.coe_mk,
      sub_add_cancel] using this
  · exact iUnion_Icc_intCast Real

end SummableNormIcc

/-!
### Substituting `-x` for `x`

These lemmas are stated in terms of either `Iic` or `Ioi` (neglecting `Iio` and `Ici`) to match
mathlib's conventions for integrals over finite intervals (see `intervalIntegral`). For the case
of finite integrals, see `intervalIntegral.integral_comp_neg`.
-/


@[simp]
/--
theorem `integral_comp_neg_Iic` / 定理 `integral_comp_neg_Iic`

English:
theorem integral_comp_neg_Iic
  statement: {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  proof: by
  have A : MeasurableEmbedding fun x : Real => -x :=
    (Homeomorph.neg Real).isClosedEmbedding.measurableEmbedding
  have := MeasurableEmbedding.setIntegral_map (μ := volume) A f (Ici (-c))
  rw [Measure.map_neg_eq_self (volume : Measure Real)] at this
  simp_rw [← integral_Ici_eq_integral_Ioi,

中文:
定理 integral_comp_neg_Iic
  结论: {E : 类型} [赋范交换加群 E] [赋范空间 实数 E]
  证明: by
  have A : MeasurableEmbedding fun x : Real => -x :=
    (Homeomorph.neg Real).isClosedEmbedding.measurableEmbedding
  have := MeasurableEmbedding.setIntegral_map (μ := volume) A f (Ici (-c))
  rw [Measure.map_neg_eq_self (volume : Measure Real)] at this
  simp_rw [← integral_Ici_eq_integral_Ioi,

Depends on / 依赖: Homeomorph, Homeomorph.neg, MeasurableEmbedding, MeasurableEmbedding.setIntegral_map, Measure, Measure.map_neg_eq_self, integral_Ici_eq_integral_Ioi, isClosedEmbedding, isClosedEmbedding.measurableEmbedding, map_neg_eq_self, measurableEmbedding, neg_Ici, neg_neg, neg_preimage, setIntegral_map, simp_rw, volume
-/
theorem integral_comp_neg_Iic {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    (c : Real) (f : Real -> E) : (∫ x in Iic c, f (-x)) = ∫ x in Ioi (-c), f x := by
  have A : MeasurableEmbedding fun x : Real => -x :=
    (Homeomorph.neg Real).isClosedEmbedding.measurableEmbedding
  have := MeasurableEmbedding.setIntegral_map (μ := volume) A f (Ici (-c))
  rw [Measure.map_neg_eq_self (volume : Measure Real)] at this
  simp_rw [← integral_Ici_eq_integral_Ioi, this, neg_preimage, neg_Ici, neg_neg]

@[simp]
/--
theorem `integral_comp_neg_Ioi` / 定理 `integral_comp_neg_Ioi`

English:
theorem integral_comp_neg_Ioi
  statement: {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  proof: by
  rw [← neg_neg c]; rw [← integral_comp_neg_Iic]
  simp only [neg_neg]

中文:
定理 integral_comp_neg_Ioi
  结论: {E : 类型} [赋范交换加群 E] [赋范空间 实数 E]
  证明: by
  rw [← neg_neg c]; rw [← integral_comp_neg_Iic]
  simp only [neg_neg]

Depends on / 依赖: integral_comp_neg_Iic, neg_neg
-/
theorem integral_comp_neg_Ioi {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    (c : Real) (f : Real -> E) : (∫ x in Ioi c, f (-x)) = ∫ x in Iic (-c), f x := by
  rw [← neg_neg c]; rw [← integral_comp_neg_Iic]
  simp only [neg_neg]

/--
theorem `integral_comp_abs` / 定理 `integral_comp_abs`

English:
theorem integral_comp_abs
  given: {f : Real -> Real}
  proof: by
  have eq : ∫ (x : Real) in Ioi 0, f |x| = ∫ (x : Real) in Ioi 0, f x := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun _ hx => ?_)
    rw [abs_eq_self.mpr (le_of_lt (by exact hx))]
  by_cases hf : IntegrableOn (fun x => f |x|) (Ioi 0)
  · have int_Iic : IntegrableOn (fun x => f |x|) 

中文:
定理 integral_comp_abs
  条件: {f : 实数 -> 实数}
  证明: by
  have eq : ∫ (x : Real) in Ioi 0, f |x| = ∫ (x : Real) in Ioi 0, f x := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun _ hx => ?_)
    rw [abs_eq_self.mpr (le_of_lt (by exact hx))]
  by_cases hf : IntegrableOn (fun x => f |x|) (Ioi 0)
  · have int_Iic : IntegrableOn (fun x => f |x|) 

Depends on / 依赖: Function, Function.comp_de, Homeomorph, Homeomorph.neg, IntegrableOn, MeasurableEmbedding, Measure, Measure.map_neg_eq_self, abs_eq_self, abs_eq_self.mpr, comp_de, int_Iic, integrableOn_map_iff, le_of_lt, m.integrableOn_map_iff, map_neg_eq_self, measurableEmbedding, measurableSet_Ioi, setIntegral_congr_fun, simp_rw
-/
theorem integral_comp_abs {f : Real -> Real} :
    ∫ x, f |x| = 2 * ∫ x in Ioi (0 : Real), f x := by
  have eq : ∫ (x : Real) in Ioi 0, f |x| = ∫ (x : Real) in Ioi 0, f x := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun _ hx => ?_)
    rw [abs_eq_self.mpr (le_of_lt (by exact hx))]
  by_cases hf : IntegrableOn (fun x => f |x|) (Ioi 0)
  · have int_Iic : IntegrableOn (fun x => f |x|) (Iic 0) := by
      rw [← Measure.map_neg_eq_self (volume : Measure Real)]
      let m : MeasurableEmbedding fun x : Real => -x := (Homeomorph.neg Real).measurableEmbedding
      rw [m.integrableOn_map_iff]
      simp_rw [Function.comp_def, abs_neg, neg_preimage, neg_Iic, neg_zero]
      exact Iff.mpr integrableOn_Ici_iff_integrableOn_Ioi hf
    calc
      _ = (∫ x in Iic 0, f |x|) + ∫ x in Ioi 0, f |x| := by
        rw [← setIntegral_union (Iic_disjoint_Ioi le_rfl) measurableSet_Ioi int_Iic hf]; rw [Iic_union_Ioi]; rw [restrict_univ]
      _ = 2 * ∫ x in Ioi 0, f x := by
        rw [two_mul]; rw [eq]
        congr! 1
        rw [← neg_zero]; rw [← integral_comp_neg_Iic]; rw [neg_zero]
        refine setIntegral_congr_fun measurableSet_Iic (fun _ hx => ?_)
        rw [abs_eq_neg_self.mpr (by exact hx)]
  · have : ¬ Integrable (fun x => f |x|) := by
      contrapose hf
      exact hf.integrableOn
    rw [← eq]; rw [integral_undef hf]; rw [integral_undef this]; rw [mul_zero]
