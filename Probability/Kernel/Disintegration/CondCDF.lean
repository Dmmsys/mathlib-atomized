/-
Copyright (c) 2023 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.Probability.Kernel.Disintegration.CDFToKernel

/-!
# Conditional cumulative distribution function

Given `ρ : Measure (α × ℝ)`, we define the conditional cumulative distribution function
(conditional cdf) of `ρ`. It is a function `condCDF ρ : α → ℝ → ℝ` such that if `ρ` is a finite
measure, then for all `a : α` `condCDF ρ a` is monotone and right-continuous with limit 0 at -∞
and limit 1 at +∞, and such that for all `x : ℝ`, `a ↦ condCDF ρ a x` is measurable. For all
`x : ℝ` and measurable set `s`, that function satisfies
`∫⁻ a in s, ENNReal.ofReal (condCDF ρ a x) ∂ρ.fst = ρ (s ×ˢ Iic x)`.

`condCDF` is build from the more general tools about kernel CDFs developed in the file
`Mathlib/Probability/Kernel/Disintegration/CDFToKernel.lean`. In that file, we build a function
`α × β → StieltjesFunction ℝ` (which is `α × β → ℝ → ℝ` with additional properties) from a function
`α × β → ℚ → ℝ`. The restriction to `ℚ` allows to prove some properties like measurability more
easily. Here we apply that construction to the case `β = Unit` and then drop `β` to build
`condCDF : α → StieltjesFunction ℝ`.

## Main definitions

* `ProbabilityTheory.condCDF ρ : α → StieltjesFunction ℝ`: the conditional cdf of
  `ρ : Measure (α × ℝ)`. A `StieltjesFunction ℝ` is a function `ℝ → ℝ` which is monotone and
  right-continuous.

## Main statements

* `ProbabilityTheory.setLIntegral_condCDF`: for all `a : α` and `x : ℝ`, all measurable set `s`,
  `∫⁻ a in s, ENNReal.ofReal (condCDF ρ a x) ∂ρ.fst = ρ (s ×ˢ Iic x)`.

-/

@[expose] public section

open MeasureTheory Set Filter TopologicalSpace

open scoped NNReal ENNReal MeasureTheory Topology

namespace MeasureTheory.Measure

variable {α : Type*} {mα : MeasurableSpace α} (ρ : Measure (α × Real))

/--
Definition of `IicSnd` / `IicSnd` 的定义

English:
definition IicSnd
  signature: (r : Real)
  body: (ρ.restrict (univ ×ˢ Iic r)).fst

中文:
定义 IicSnd
  签名: (r : 实数)
  定义体: (ρ.restrict (univ ×ˢ Iic r)).fst

Depends on / 依赖: restrict
-/
noncomputable def IicSnd (r : Real) : Measure α :=
  (ρ.restrict (univ ×ˢ Iic r)).fst

/--
theorem `IicSnd_apply` / 定理 `IicSnd_apply`

English:
theorem IicSnd_apply
  given: (r : Real) {s : Set α} (hs : MeasurableSet s)
  proof: by
  rw [IicSnd]; rw [fst_apply hs]; rw [restrict_apply' (MeasurableSet.univ.prod measurableSet_Iic)]; rw [univ_prod]; rw [Set.prod_eq]

中文:
定理 IicSnd_apply
  条件: (r : 实数) {s : 集合 α} (hs : 可测集 s)
  证明: by
  rw [IicSnd]; rw [fst_apply hs]; rw [restrict_apply' (MeasurableSet.univ.prod measurableSet_Iic)]; rw [univ_prod]; rw [Set.prod_eq]

Depends on / 依赖: IicSnd, MeasurableSet, MeasurableSet.univ.prod, Set.prod_eq, fst_apply, measurableSet_Iic, prod_eq, restrict_apply, univ_prod
-/
theorem IicSnd_apply (r : Real) {s : Set α} (hs : MeasurableSet s) :
    ρ.IicSnd r s = ρ (s ×ˢ Iic r) := by
  rw [IicSnd]; rw [fst_apply hs]; rw [restrict_apply' (MeasurableSet.univ.prod measurableSet_Iic)]; rw [univ_prod]; rw [Set.prod_eq]

/--
theorem `IicSnd_univ` / 定理 `IicSnd_univ`

English:
theorem IicSnd_univ
  given: (r : Real)
  statement: ρ.IicSnd r univ = ρ (univ ×ˢ Iic r)
  proof: IicSnd_apply ρ r MeasurableSet.univ

@[gcongr]

中文:
定理 IicSnd_univ
  条件: (r : 实数)
  结论: ρ.IicSnd r univ = ρ (univ ×ˢ 左无界右闭区间 r)
  证明: IicSnd_apply ρ r MeasurableSet.univ

@[gcongr]

Depends on / 依赖: IicSnd_apply, MeasurableSet, MeasurableSet.univ
-/
theorem IicSnd_univ (r : Real) : ρ.IicSnd r univ = ρ (univ ×ˢ Iic r) :=
  IicSnd_apply ρ r MeasurableSet.univ

@[gcongr]
/--
theorem `IicSnd_mono` / 定理 `IicSnd_mono`

English:
theorem IicSnd_mono
  given: {r r' : Real} (h_le : r <= r')
  statement: ρ.IicSnd r <= ρ.IicSnd r'
  proof: by
  unfold IicSnd; gcongr

中文:
定理 IicSnd_mono
  条件: {r r' : 实数} (h_le : r <= r')
  结论: ρ.IicSnd r <= ρ.IicSnd r'
  证明: by
  unfold IicSnd; gcongr

Depends on / 依赖: IicSnd
-/
theorem IicSnd_mono {r r' : Real} (h_le : r <= r') : ρ.IicSnd r <= ρ.IicSnd r' := by
  unfold IicSnd; gcongr

/--
theorem `IicSnd_le_fst` / 定理 `IicSnd_le_fst`

English:
theorem IicSnd_le_fst
  given: (r : Real)
  statement: ρ.IicSnd r <= ρ.fst
  proof: fst_mono restrict_le_self

中文:
定理 IicSnd_le_fst
  条件: (r : 实数)
  结论: ρ.IicSnd r <= ρ.fst
  证明: fst_mono restrict_le_self

Depends on / 依赖: fst_mono, restrict_le_self
-/
theorem IicSnd_le_fst (r : Real) : ρ.IicSnd r <= ρ.fst :=
  fst_mono restrict_le_self

/--
theorem `IicSnd_ac_fst` / 定理 `IicSnd_ac_fst`

English:
theorem IicSnd_ac_fst
  given: (r : Real)
  statement: ρ.IicSnd r ≪ ρ.fst
  proof: Measure.absolutelyContinuous_of_le (IicSnd_le_fst ρ r)

中文:
定理 IicSnd_ac_fst
  条件: (r : 实数)
  结论: ρ.IicSnd r ≪ ρ.fst
  证明: Measure.absolutelyContinuous_of_le (IicSnd_le_fst ρ r)

Depends on / 依赖: IicSnd_le_fst, Measure, Measure.absolutelyContinuous_of_le, absolutelyContinuous_of_le
-/
theorem IicSnd_ac_fst (r : Real) : ρ.IicSnd r ≪ ρ.fst :=
  Measure.absolutelyContinuous_of_le (IicSnd_le_fst ρ r)

/--
theorem `IsFiniteMeasure.IicSnd` / 定理 `IsFiniteMeasure.IicSnd`

English:
theorem IsFiniteMeasure.IicSnd
  given: {ρ : Measure (α × Real)} [IsFiniteMeasure ρ] (r : Real)
  proof: isFiniteMeasure_of_le _ (IicSnd_le_fst ρ _)

中文:
定理 是有限测度.IicSnd
  条件: {ρ : 测度 (α × 实数)} [是有限测度 ρ] (r : 实数)
  证明: isFiniteMeasure_of_le _ (IicSnd_le_fst ρ _)

Depends on / 依赖: IicSnd_le_fst, isFiniteMeasure_of_le
-/
theorem IsFiniteMeasure.IicSnd {ρ : Measure (α × Real)} [IsFiniteMeasure ρ] (r : Real) :
    IsFiniteMeasure (ρ.IicSnd r) :=
  isFiniteMeasure_of_le _ (IicSnd_le_fst ρ _)

/--
theorem `iInf_IicSnd_gt` / 定理 `iInf_IicSnd_gt`

English:
theorem iInf_IicSnd_gt
  given: (t : Rat) {s : Set α} (hs : MeasurableSet s) [IsFiniteMeasure ρ]
  proof: by
  simp_rw [ρ.IicSnd_apply _ hs, Measure.iInf_rat_gt_prod_Iic hs]

中文:
定理 iInf_IicSnd_gt
  条件: (t : 有理数) {s : 集合 α} (hs : 可测集 s) [是有限测度 ρ]
  证明: by
  simp_rw [ρ.IicSnd_apply _ hs, Measure.iInf_rat_gt_prod_Iic hs]

Depends on / 依赖: IicSnd_apply, Measure, Measure.iInf_rat_gt_prod_Iic, iInf_rat_gt_prod_Iic, simp_rw
-/
theorem iInf_IicSnd_gt (t : Rat) {s : Set α} (hs : MeasurableSet s) [IsFiniteMeasure ρ] :
    ⨅ r : { r' : Rat // t < r' }, ρ.IicSnd r s = ρ.IicSnd t s := by
  simp_rw [ρ.IicSnd_apply _ hs, Measure.iInf_rat_gt_prod_Iic hs]

/--
theorem `tendsto_IicSnd_atTop` / 定理 `tendsto_IicSnd_atTop`

English:
theorem tendsto_IicSnd_atTop
  given: {s : Set α} (hs : MeasurableSet s)
  proof: by
  simp_rw [ρ.IicSnd_apply _ hs, fst_apply hs, ← prod_univ]
  rw [← Real.iUnion_Iic_rat]; rw [prod_iUnion]
  apply tendsto_measure_iUnion_atTop
  exact monotone_const.set_prod Rat.cast_mono.Iic

中文:
定理 tendsto_IicSnd_atTop
  条件: {s : 集合 α} (hs : 可测集 s)
  证明: by
  simp_rw [ρ.IicSnd_apply _ hs, fst_apply hs, ← prod_univ]
  rw [← Real.iUnion_Iic_rat]; rw [prod_iUnion]
  apply tendsto_measure_iUnion_atTop
  exact monotone_const.set_prod Rat.cast_mono.Iic

Depends on / 依赖: IicSnd_apply, Rat.cast_mono.Iic, Real.iUnion_Iic_rat, cast_mono, fst_apply, iUnion_Iic_rat, monotone_const, monotone_const.set_prod, prod_iUnion, prod_univ, set_prod, simp_rw, tendsto_measure_iUnion_atTop
-/
theorem tendsto_IicSnd_atTop {s : Set α} (hs : MeasurableSet s) :
    Tendsto (fun r : Rat => ρ.IicSnd r s) atTop (𝓝 (ρ.fst s)) := by
  simp_rw [ρ.IicSnd_apply _ hs, fst_apply hs, ← prod_univ]
  rw [← Real.iUnion_Iic_rat]; rw [prod_iUnion]
  apply tendsto_measure_iUnion_atTop
  exact monotone_const.set_prod Rat.cast_mono.Iic

/--
theorem `tendsto_IicSnd_atBot` / 定理 `tendsto_IicSnd_atBot`

English:
theorem tendsto_IicSnd_atBot
  given: [IsFiniteMeasure ρ] {s : Set α} (hs : MeasurableSet s)
  proof: by
  simp_rw [ρ.IicSnd_apply _ hs]
  have h_empty : ρ (s ×ˢ ∅) = 0 := by simp only [prod_empty, measure_empty]
  rw [← h_empty]; rw [← Real.iInter_Iic_rat]; rw [prod_iInter]
  suffices h_neg :
      Tendsto (fun r : Rat => ρ (s ×ˢ Iic ↑(-r))) atTop (𝓝 (ρ (⋂ r : Rat, s ×ˢ Iic ↑(-r)))) by
    have h_i

中文:
定理 tendsto_IicSnd_atBot
  条件: [是有限测度 ρ] {s : 集合 α} (hs : 可测集 s)
  证明: by
  simp_rw [ρ.IicSnd_apply _ hs]
  have h_empty : ρ (s ×ˢ ∅) = 0 := by simp only [prod_empty, measure_empty]
  rw [← h_empty]; rw [← Real.iInter_Iic_rat]; rw [prod_iInter]
  suffices h_neg :
      Tendsto (fun r : Rat => ρ (s ×ˢ Iic ↑(-r))) atTop (𝓝 (ρ (⋂ r : Rat, s ×ˢ Iic ↑(-r)))) by
    have h_i

Depends on / 依赖: IicSnd_apply, Real.iInter_Iic_rat, Tendsto, h_empty, h_inter_eq, h_neg, iInter_Iic_rat, measure_empty, neg_neg, prod_empty, prod_iInter, simp_rw
-/
theorem tendsto_IicSnd_atBot [IsFiniteMeasure ρ] {s : Set α} (hs : MeasurableSet s) :
    Tendsto (fun r : Rat => ρ.IicSnd r s) atBot (𝓝 0) := by
  simp_rw [ρ.IicSnd_apply _ hs]
  have h_empty : ρ (s ×ˢ ∅) = 0 := by simp only [prod_empty, measure_empty]
  rw [← h_empty]; rw [← Real.iInter_Iic_rat]; rw [prod_iInter]
  suffices h_neg :
      Tendsto (fun r : Rat => ρ (s ×ˢ Iic ↑(-r))) atTop (𝓝 (ρ (⋂ r : Rat, s ×ˢ Iic ↑(-r)))) by
    have h_inter_eq : ⋂ r : Rat, s ×ˢ Iic ↑(-r) = ⋂ r : Rat, s ×ˢ Iic (r : Real) := by
      ext1 x
      push _ in _
      refine ⟨fun h i => ⟨(h i).1, ?_⟩, fun h i => ⟨(h i).1, ?_⟩⟩ <;> have h' := h (-i)
      · rw [neg_neg] at h'; exact h'.2
      · exact h'.2
    rw [h_inter_eq] at h_neg
    exact tendsto_comp_neg_atTop_iff.mp h_neg
  refine tendsto_measure_iInter_atTop (fun q => (hs.prod measurableSet_Iic).nullMeasurableSet)
    ?_ ⟨0, measure_ne_top ρ _⟩
  refine fun q r hqr => Set.prod_mono subset_rfl fun x hx => ?_
  simp only [Rat.cast_neg, mem_Iic] at hx ⊢
  refine hx.trans (neg_le_neg ?_)
  exact mod_cast hqr

end MeasureTheory.Measure

open MeasureTheory

namespace ProbabilityTheory

variable {α : Type*} {mα : MeasurableSpace α}

attribute [local instance] MeasureTheory.Measure.IsFiniteMeasure.IicSnd

/-! ### Auxiliary definitions

We build towards the definition of `ProbabilityTheory.condCDF`. We first define
`ProbabilityTheory.preCDF`, a function defined on `α × ℚ` with the properties of a cdf almost
everywhere. -/

/--
Definition of `preCDF` / `preCDF` 的定义

English:
definition preCDF
  signature: (ρ : Measure (α × Real)) (r : Rat)
  body: Measure.rnDeriv (ρ.IicSnd r) ρ.fst

中文:
定义 preCDF
  签名: (ρ : 测度 (α × 实数)) (r : 有理数)
  定义体: Measure.rnDeriv (ρ.IicSnd r) ρ.fst

Depends on / 依赖: IicSnd, Measure, Measure.rnDeriv, rnDeriv
-/
noncomputable def preCDF (ρ : Measure (α × Real)) (r : Rat) : α -> Real>=0∞ :=
  Measure.rnDeriv (ρ.IicSnd r) ρ.fst

/--
theorem `measurable_preCDF` / 定理 `measurable_preCDF`

English:
theorem measurable_preCDF
  given: {ρ : Measure (α × Real)} {r : Rat}
  statement: Measurable (preCDF ρ r)
  proof: Measure.measurable_rnDeriv _ _

中文:
定理 measurable_preCDF
  条件: {ρ : 测度 (α × 实数)} {r : 有理数}
  结论: 可测 (preCDF ρ r)
  证明: Measure.measurable_rnDeriv _ _

Depends on / 依赖: Measure, Measure.measurable_rnDeriv, measurable_rnDeriv
-/
theorem measurable_preCDF {ρ : Measure (α × Real)} {r : Rat} : Measurable (preCDF ρ r) :=
  Measure.measurable_rnDeriv _ _

/--
lemma `measurable_preCDF'` / 引理 `measurable_preCDF'`

English:
lemma measurable_preCDF'
  given: {ρ : Measure (α × Real)}
  proof: by
  rw [measurable_pi_iff]
  exact fun _ => measurable_preCDF.ennreal_toReal

中文:
引理 measurable_preCDF'
  条件: {ρ : 测度 (α × 实数)}
  证明: by
  rw [measurable_pi_iff]
  exact fun _ => measurable_preCDF.ennreal_toReal

Depends on / 依赖: ennreal_toReal, measurable_pi_iff, measurable_preCDF, measurable_preCDF.ennreal_toReal
-/
lemma measurable_preCDF' {ρ : Measure (α × Real)} :
    Measurable fun a r => (preCDF ρ r a).toReal := by
  rw [measurable_pi_iff]
  exact fun _ => measurable_preCDF.ennreal_toReal

/--
theorem `withDensity_preCDF` / 定理 `withDensity_preCDF`

English:
theorem withDensity_preCDF
  given: (ρ : Measure (α × Real)) (r : Rat) [IsFiniteMeasure ρ]
  proof: Measure.absolutelyContinuous_iff_withDensity_rnDeriv_eq.mp (Measure.IicSnd_ac_fst ρ r)

中文:
定理 withDensity_preCDF
  条件: (ρ : 测度 (α × 实数)) (r : 有理数) [是有限测度 ρ]
  证明: Measure.absolutelyContinuous_iff_withDensity_rnDeriv_eq.mp (Measure.IicSnd_ac_fst ρ r)

Depends on / 依赖: IicSnd_ac_fst, Measure, Measure.IicSnd_ac_fst, Measure.absolutelyContinuous_iff_withDensity_rnDeriv_eq.mp, absolutelyContinuous_iff_withDensity_rnDeriv_eq
-/
theorem withDensity_preCDF (ρ : Measure (α × Real)) (r : Rat) [IsFiniteMeasure ρ] :
    ρ.fst.withDensity (preCDF ρ r) = ρ.IicSnd r :=
  Measure.absolutelyContinuous_iff_withDensity_rnDeriv_eq.mp (Measure.IicSnd_ac_fst ρ r)

/--
theorem `setLIntegral_preCDF_fst` / 定理 `setLIntegral_preCDF_fst`

English:
theorem setLIntegral_preCDF_fst
  statement: (ρ : Measure (α × Real)) (r : Rat) {s : Set α} (hs : MeasurableSet s)
  proof: by
  have : forall r, ∫⁻ x in s, preCDF ρ r x ∂ρ.fst = ∫⁻ x in s, (preCDF ρ r * 1) x ∂ρ.fst := by
    simp only [mul_one, forall_const]
  rw [this]; rw [← setLIntegral_withDensity_eq_setLIntegral_mul _ measurable_preCDF _ hs]
  · simp only [withDensity_preCDF ρ r, Pi.one_apply, lintegral_one, Measur

中文:
定理 setL整数egral_preCDF_fst
  结论: (ρ : 测度 (α × 实数)) (r : 有理数) {s : 集合 α} (hs : 可测集 s)
  证明: by
  have : forall r, ∫⁻ x in s, preCDF ρ r x ∂ρ.fst = ∫⁻ x in s, (preCDF ρ r * 1) x ∂ρ.fst := by
    simp only [mul_one, forall_const]
  rw [this]; rw [← setLIntegral_withDensity_eq_setLIntegral_mul _ measurable_preCDF _ hs]
  · simp only [withDensity_preCDF ρ r, Pi.one_apply, lintegral_one, Measur

Depends on / 依赖: MeasurableSet, MeasurableSet.univ, Measure, Measure.restrict_apply, Pi.one_apply, Pi.one_def, forall_const, lintegral_one, measurable_const, measurable_preCDF, mul_one, one_apply, one_def, preCDF, restrict_apply, setLIntegral_withDensity_eq_setLIntegral_mul, univ_inter, withDensity_preCDF
-/
theorem setLIntegral_preCDF_fst (ρ : Measure (α × Real)) (r : Rat) {s : Set α} (hs : MeasurableSet s)
    [IsFiniteMeasure ρ] : ∫⁻ x in s, preCDF ρ r x ∂ρ.fst = ρ.IicSnd r s := by
  have : forall r, ∫⁻ x in s, preCDF ρ r x ∂ρ.fst = ∫⁻ x in s, (preCDF ρ r * 1) x ∂ρ.fst := by
    simp only [mul_one, forall_const]
  rw [this]; rw [← setLIntegral_withDensity_eq_setLIntegral_mul _ measurable_preCDF _ hs]
  · simp only [withDensity_preCDF ρ r, Pi.one_apply, lintegral_one, Measure.restrict_apply,
      MeasurableSet.univ, univ_inter]
  · rw [Pi.one_def]
    exact measurable_const

/--
lemma `lintegral_preCDF_fst` / 引理 `lintegral_preCDF_fst`

English:
lemma lintegral_preCDF_fst
  given: (ρ : Measure (α × Real)) (r : Rat) [IsFiniteMeasure ρ]
  proof: by
  rw [← setLIntegral_univ]; rw [setLIntegral_preCDF_fst ρ r MeasurableSet.univ]

中文:
引理 lintegral_preCDF_fst
  条件: (ρ : 测度 (α × 实数)) (r : 有理数) [是有限测度 ρ]
  证明: by
  rw [← setLIntegral_univ]; rw [setLIntegral_preCDF_fst ρ r MeasurableSet.univ]

Depends on / 依赖: MeasurableSet, MeasurableSet.univ, setLIntegral_preCDF_fst, setLIntegral_univ
-/
lemma lintegral_preCDF_fst (ρ : Measure (α × Real)) (r : Rat) [IsFiniteMeasure ρ] :
    ∫⁻ x, preCDF ρ r x ∂ρ.fst = ρ.IicSnd r univ := by
  rw [← setLIntegral_univ]; rw [setLIntegral_preCDF_fst ρ r MeasurableSet.univ]

/--
theorem `monotone_preCDF` / 定理 `monotone_preCDF`

English:
theorem monotone_preCDF
  given: (ρ : Measure (α × Real)) [IsFiniteMeasure ρ]
  proof: by
  simp_rw [Monotone, ae_all_iff]
  refine fun r r' hrr' => ae_le_of_forall_setLIntegral_le_of_sigmaFinite measurable_preCDF
    fun s hs _ => ?_
  rw [setLIntegral_preCDF_fst ρ r hs]; rw [setLIntegral_preCDF_fst ρ r' hs]
  exact Measure.IicSnd_mono ρ (mod_cast hrr') s

中文:
定理 monotone_preCDF
  条件: (ρ : 测度 (α × 实数)) [是有限测度 ρ]
  证明: by
  simp_rw [Monotone, ae_all_iff]
  refine fun r r' hrr' => ae_le_of_forall_setLIntegral_le_of_sigmaFinite measurable_preCDF
    fun s hs _ => ?_
  rw [setLIntegral_preCDF_fst ρ r hs]; rw [setLIntegral_preCDF_fst ρ r' hs]
  exact Measure.IicSnd_mono ρ (mod_cast hrr') s

Depends on / 依赖: IicSnd_mono, Measure, Measure.IicSnd_mono, Monotone, ae_all_iff, ae_le_of_forall_setLIntegral_le_of_sigmaFinite, measurable_preCDF, mod_cast, setLIntegral_preCDF_fst, simp_rw
-/
theorem monotone_preCDF (ρ : Measure (α × Real)) [IsFiniteMeasure ρ] :
    forallᵐ a ∂ρ.fst, Monotone fun r => preCDF ρ r a := by
  simp_rw [Monotone, ae_all_iff]
  refine fun r r' hrr' => ae_le_of_forall_setLIntegral_le_of_sigmaFinite measurable_preCDF
    fun s hs _ => ?_
  rw [setLIntegral_preCDF_fst ρ r hs]; rw [setLIntegral_preCDF_fst ρ r' hs]
  exact Measure.IicSnd_mono ρ (mod_cast hrr') s

/--
theorem `preCDF_le_one` / 定理 `preCDF_le_one`

English:
theorem preCDF_le_one
  given: (ρ : Measure (α × Real)) [IsFiniteMeasure ρ]
  proof: by
  rw [ae_all_iff]
  refine fun r => ae_le_of_forall_setLIntegral_le_of_sigmaFinite measurable_preCDF fun s hs _ => ?_
  rw [setLIntegral_preCDF_fst ρ r hs]
  simp only [lintegral_one, Measure.restrict_apply, MeasurableSet.univ, univ_inter]
  exact Measure.IicSnd_le_fst ρ r s

中文:
定理 preCDF_le_one
  条件: (ρ : 测度 (α × 实数)) [是有限测度 ρ]
  证明: by
  rw [ae_all_iff]
  refine fun r => ae_le_of_forall_setLIntegral_le_of_sigmaFinite measurable_preCDF fun s hs _ => ?_
  rw [setLIntegral_preCDF_fst ρ r hs]
  simp only [lintegral_one, Measure.restrict_apply, MeasurableSet.univ, univ_inter]
  exact Measure.IicSnd_le_fst ρ r s

Depends on / 依赖: IicSnd_le_fst, MeasurableSet, MeasurableSet.univ, Measure, Measure.IicSnd_le_fst, Measure.restrict_apply, ae_all_iff, ae_le_of_forall_setLIntegral_le_of_sigmaFinite, lintegral_one, measurable_preCDF, restrict_apply, setLIntegral_preCDF_fst, univ_inter
-/
theorem preCDF_le_one (ρ : Measure (α × Real)) [IsFiniteMeasure ρ] :
    forallᵐ a ∂ρ.fst, forall r, preCDF ρ r a <= 1 := by
  rw [ae_all_iff]
  refine fun r => ae_le_of_forall_setLIntegral_le_of_sigmaFinite measurable_preCDF fun s hs _ => ?_
  rw [setLIntegral_preCDF_fst ρ r hs]
  simp only [lintegral_one, Measure.restrict_apply, MeasurableSet.univ, univ_inter]
  exact Measure.IicSnd_le_fst ρ r s

/--
lemma `setIntegral_preCDF_fst` / 引理 `setIntegral_preCDF_fst`

English:
lemma setIntegral_preCDF_fst
  statement: (ρ : Measure (α × Real)) (r : Rat) {s : Set α} (hs : MeasurableSet s)
  proof: by
  rw [integral_toReal]
  · rw [setLIntegral_preCDF_fst _ _ hs, measureReal_def]
  · exact measurable_preCDF.aemeasurable
  · refine ae_restrict_of_ae ?_
    filter_upwards [preCDF_le_one ρ] with a ha
    exact (ha r).trans_lt ENNReal.one_lt_top

中文:
引理 set整数egral_preCDF_fst
  结论: (ρ : 测度 (α × 实数)) (r : 有理数) {s : 集合 α} (hs : 可测集 s)
  证明: by
  rw [integral_toReal]
  · rw [setLIntegral_preCDF_fst _ _ hs, measureReal_def]
  · exact measurable_preCDF.aemeasurable
  · refine ae_restrict_of_ae ?_
    filter_upwards [preCDF_le_one ρ] with a ha
    exact (ha r).trans_lt ENNReal.one_lt_top

Depends on / 依赖: ENNReal, ENNReal.one_lt_top, ae_restrict_of_ae, aemeasurable, filter_upwards, integral_toReal, measurable_preCDF, measurable_preCDF.aemeasurable, measureReal_def, one_lt_top, preCDF_le_one, setLIntegral_preCDF_fst, trans_lt
-/
lemma setIntegral_preCDF_fst (ρ : Measure (α × Real)) (r : Rat) {s : Set α} (hs : MeasurableSet s)
    [IsFiniteMeasure ρ] :
    ∫ x in s, (preCDF ρ r x).toReal ∂ρ.fst = (ρ.IicSnd r).real s := by
  rw [integral_toReal]
  · rw [setLIntegral_preCDF_fst _ _ hs, measureReal_def]
  · exact measurable_preCDF.aemeasurable
  · refine ae_restrict_of_ae ?_
    filter_upwards [preCDF_le_one ρ] with a ha
    exact (ha r).trans_lt ENNReal.one_lt_top

/--
lemma `integral_preCDF_fst` / 引理 `integral_preCDF_fst`

English:
lemma integral_preCDF_fst
  given: (ρ : Measure (α × Real)) (r : Rat) [IsFiniteMeasure ρ]
  proof: by
  rw [← setIntegral_univ]; rw [setIntegral_preCDF_fst ρ _ MeasurableSet.univ]

中文:
引理 integral_preCDF_fst
  条件: (ρ : 测度 (α × 实数)) (r : 有理数) [是有限测度 ρ]
  证明: by
  rw [← setIntegral_univ]; rw [setIntegral_preCDF_fst ρ _ MeasurableSet.univ]

Depends on / 依赖: MeasurableSet, MeasurableSet.univ, setIntegral_preCDF_fst, setIntegral_univ
-/
lemma integral_preCDF_fst (ρ : Measure (α × Real)) (r : Rat) [IsFiniteMeasure ρ] :
    ∫ x, (preCDF ρ r x).toReal ∂ρ.fst = (ρ.IicSnd r).real univ := by
  rw [← setIntegral_univ]; rw [setIntegral_preCDF_fst ρ _ MeasurableSet.univ]

/--
lemma `integrable_preCDF` / 引理 `integrable_preCDF`

English:
lemma integrable_preCDF
  given: (ρ : Measure (α × Real)) [IsFiniteMeasure ρ] (x : Rat)
  proof: by
  refine integrable_of_forall_fin_meas_le _ (measure_lt_top ρ.fst univ) ?_ fun t _ _ => ?_
  · exact measurable_preCDF.ennreal_toReal.aestronglyMeasurable
  · simp_rw [← ofReal_norm, Real.norm_of_nonneg ENNReal.toReal_nonneg]
    rw [← lintegral_one]
    refine (setLIntegral_le_lintegral _ _).tra

中文:
引理 integrable_preCDF
  条件: (ρ : 测度 (α × 实数)) [是有限测度 ρ] (x : 有理数)
  证明: by
  refine integrable_of_forall_fin_meas_le _ (measure_lt_top ρ.fst univ) ?_ fun t _ _ => ?_
  · exact measurable_preCDF.ennreal_toReal.aestronglyMeasurable
  · simp_rw [← ofReal_norm, Real.norm_of_nonneg ENNReal.toReal_nonneg]
    rw [← lintegral_one]
    refine (setLIntegral_le_lintegral _ _).tra

Depends on / 依赖: ENNReal, ENNReal.ofReal_toReal_le.trans, ENNReal.toReal_nonneg, Real.norm_of_nonneg, aestronglyMeasurable, ennreal_toReal, filter_upwards, integrable_of_forall_fin_meas_le, lintegral_mono_ae, lintegral_one, measurable_preCDF, measurable_preCDF.ennreal_toReal.aestronglyMeasurable, measure_lt_top, norm_of_nonneg, ofReal_norm, ofReal_toReal_le, preCDF_le_one, setLIntegral_le_lintegral, simp_rw, toReal_nonneg
-/
lemma integrable_preCDF (ρ : Measure (α × Real)) [IsFiniteMeasure ρ] (x : Rat) :
    Integrable (fun a => (preCDF ρ x a).toReal) ρ.fst := by
  refine integrable_of_forall_fin_meas_le _ (measure_lt_top ρ.fst univ) ?_ fun t _ _ => ?_
  · exact measurable_preCDF.ennreal_toReal.aestronglyMeasurable
  · simp_rw [← ofReal_norm, Real.norm_of_nonneg ENNReal.toReal_nonneg]
    rw [← lintegral_one]
    refine (setLIntegral_le_lintegral _ _).trans (lintegral_mono_ae ?_)
    filter_upwards [preCDF_le_one ρ] with a ha using ENNReal.ofReal_toReal_le.trans (ha _)

/--
lemma `isRatCondKernelCDFAux_preCDF` / 引理 `isRatCondKernelCDFAux_preCDF`

English:
lemma isRatCondKernelCDFAux_preCDF
  given: (ρ : Measure (α × Real)) [IsFiniteMeasure ρ]
  proof: measurable_preCDF'.comp measurable_snd
  mono' a r r' hrr' := by
    filter_upwards [monotone_preCDF ρ, preCDF_le_one ρ] with a h₁ h₂
    exact ENNReal.toReal_mono ((h₂ _).trans_lt ENNReal.one_lt_top).ne (h₁ hrr')
  nonneg' _ q := by simp
  le_one' a q := by
    simp only [Kernel.const_apply]
    fi

中文:
引理 isRatCondKernelCDFAux_preCDF
  条件: (ρ : 测度 (α × 实数)) [是有限测度 ρ]
  证明: measurable_preCDF'.comp measurable_snd
  mono' a r r' hrr' := by
    filter_upwards [monotone_preCDF ρ, preCDF_le_one ρ] with a h₁ h₂
    exact ENNReal.toReal_mono ((h₂ _).trans_lt ENNReal.one_lt_top).ne (h₁ hrr')
  nonneg' _ q := by simp
  le_one' a q := by
    simp only [Kernel.const_apply]
    fi

Depends on / 依赖: measurable_preCDF, measurable_snd
-/
lemma isRatCondKernelCDFAux_preCDF (ρ : Measure (α × Real)) [IsFiniteMeasure ρ] :
    IsRatCondKernelCDFAux (fun p r => (preCDF ρ r p.2).toReal)
      (Kernel.const Unit ρ) (Kernel.const Unit ρ.fst) where
  measurable := measurable_preCDF'.comp measurable_snd
  mono' a r r' hrr' := by
    filter_upwards [monotone_preCDF ρ, preCDF_le_one ρ] with a h₁ h₂
    exact ENNReal.toReal_mono ((h₂ _).trans_lt ENNReal.one_lt_top).ne (h₁ hrr')
  nonneg' _ q := by simp
  le_one' a q := by
    simp only [Kernel.const_apply]
    filter_upwards [preCDF_le_one ρ] with a ha
    refine ENNReal.toReal_le_of_le_ofReal zero_le_one ?_
    simp [ha]
  tendsto_integral_of_antitone a s _ hs_tendsto := by
    simp_rw [Kernel.const_apply, integral_preCDF_fst ρ]
    have h := ρ.tendsto_IicSnd_atBot MeasurableSet.univ
    rw [← ENNReal.toReal_zero]
    have h0 : Tendsto ENNReal.toReal (𝓝 0) (𝓝 0) :=
      ENNReal.continuousAt_toReal ENNReal.zero_ne_top
    exact h0.comp (h.comp hs_tendsto)
  tendsto_integral_of_monotone a s _ hs_tendsto := by
    simp_rw [Kernel.const_apply, integral_preCDF_fst ρ]
    have h := ρ.tendsto_IicSnd_atTop MeasurableSet.univ
    have h0 : Tendsto ENNReal.toReal (𝓝 (ρ.fst univ)) (𝓝 (ρ.fst.real univ)) :=
      ENNReal.continuousAt_toReal (measure_ne_top _ _)
    exact h0.comp (h.comp hs_tendsto)
  integrable _ q := integrable_preCDF ρ q
  setIntegral a s hs q := by rw [Kernel.const_apply, Kernel.const_apply,
    setIntegral_preCDF_fst _ _ hs, measureReal_def, measureReal_def, Measure.IicSnd_apply _ _ hs]

/--
lemma `isRatCondKernelCDF_preCDF` / 引理 `isRatCondKernelCDF_preCDF`

English:
lemma isRatCondKernelCDF_preCDF
  given: (ρ : Measure (α × Real)) [IsFiniteMeasure ρ]
  proof: (isRatCondKernelCDFAux_preCDF ρ).isRatCondKernelCDF

中文:
引理 isRatCondKernelCDF_preCDF
  条件: (ρ : 测度 (α × 实数)) [是有限测度 ρ]
  证明: (isRatCondKernelCDFAux_preCDF ρ).isRatCondKernelCDF

Depends on / 依赖: isRatCondKernelCDF, isRatCondKernelCDFAux_preCDF
-/
lemma isRatCondKernelCDF_preCDF (ρ : Measure (α × Real)) [IsFiniteMeasure ρ] :
    IsRatCondKernelCDF (fun p r => (preCDF ρ r p.2).toReal)
      (Kernel.const Unit ρ) (Kernel.const Unit ρ.fst) :=
  (isRatCondKernelCDFAux_preCDF ρ).isRatCondKernelCDF

/-! ### Conditional cdf -/

/--
Definition of `condCDF` / `condCDF` 的定义

English:
definition condCDF
  signature: (ρ : Measure (α × Real)) (a : α)
  body: stieltjesOfMeasurableRat (fun a r => (preCDF ρ r a).toReal) measurable_preCDF' a

中文:
定义 condCDF
  签名: (ρ : 测度 (α × 实数)) (a : α)
  定义体: stieltjesOfMeasurableRat (fun a r => (preCDF ρ r a).toReal) measurable_preCDF' a

Depends on / 依赖: measurable_preCDF, preCDF, stieltjesOfMeasurableRat, toReal
-/
noncomputable def condCDF (ρ : Measure (α × Real)) (a : α) : StieltjesFunction Real :=
  stieltjesOfMeasurableRat (fun a r => (preCDF ρ r a).toReal) measurable_preCDF' a

/--
lemma `condCDF_eq_stieltjesOfMeasurableRat_unit_prod` / 引理 `condCDF_eq_stieltjesOfMeasurableRat_unit_prod`

English:
lemma condCDF_eq_stieltjesOfMeasurableRat_unit_prod
  given: (ρ : Measure (α × Real)) (a : α)
  proof: by
  ext x
  rw [condCDF]; rw [← stieltjesOfMeasurableRat_unit_prod]

中文:
引理 condCDF_eq_stieltjesOfMeasurableRat_unit_prod
  条件: (ρ : 测度 (α × 实数)) (a : α)
  证明: by
  ext x
  rw [condCDF]; rw [← stieltjesOfMeasurableRat_unit_prod]

Depends on / 依赖: condCDF, stieltjesOfMeasurableRat_unit_prod
-/
lemma condCDF_eq_stieltjesOfMeasurableRat_unit_prod (ρ : Measure (α × Real)) (a : α) :
    condCDF ρ a = stieltjesOfMeasurableRat (fun (p : Unit × α) r => (preCDF ρ r p.2).toReal)
      (measurable_preCDF'.comp measurable_snd) ((), a) := by
  ext x
  rw [condCDF]; rw [← stieltjesOfMeasurableRat_unit_prod]

/--
lemma `isCondKernelCDF_condCDF` / 引理 `isCondKernelCDF_condCDF`

English:
lemma isCondKernelCDF_condCDF
  given: (ρ : Measure (α × Real)) [IsFiniteMeasure ρ]
  proof: by
  simp_rw [condCDF_eq_stieltjesOfMeasurableRat_unit_prod ρ]
  exact isCondKernelCDF_stieltjesOfMeasurableRat (isRatCondKernelCDF_preCDF ρ)

中文:
引理 isCondKernelCDF_condCDF
  条件: (ρ : 测度 (α × 实数)) [是有限测度 ρ]
  证明: by
  simp_rw [condCDF_eq_stieltjesOfMeasurableRat_unit_prod ρ]
  exact isCondKernelCDF_stieltjesOfMeasurableRat (isRatCondKernelCDF_preCDF ρ)

Depends on / 依赖: condCDF_eq_stieltjesOfMeasurableRat_unit_prod, isCondKernelCDF_stieltjesOfMeasurableRat, isRatCondKernelCDF_preCDF, simp_rw
-/
lemma isCondKernelCDF_condCDF (ρ : Measure (α × Real)) [IsFiniteMeasure ρ] :
    IsCondKernelCDF (fun p : Unit × α => condCDF ρ p.2) (Kernel.const Unit ρ)
      (Kernel.const Unit ρ.fst) := by
  simp_rw [condCDF_eq_stieltjesOfMeasurableRat_unit_prod ρ]
  exact isCondKernelCDF_stieltjesOfMeasurableRat (isRatCondKernelCDF_preCDF ρ)

/--
theorem `condCDF_nonneg` / 定理 `condCDF_nonneg`

English:
theorem condCDF_nonneg
  given: (ρ : Measure (α × Real)) (a : α) (r : Real)
  statement: 0 <= condCDF ρ a r
  proof: stieltjesOfMeasurableRat_nonneg _ a r

中文:
定理 condCDF_nonneg
  条件: (ρ : 测度 (α × 实数)) (a : α) (r : 实数)
  结论: 0 <= condCDF ρ a r
  证明: stieltjesOfMeasurableRat_nonneg _ a r

Depends on / 依赖: stieltjesOfMeasurableRat_nonneg
-/
theorem condCDF_nonneg (ρ : Measure (α × Real)) (a : α) (r : Real) : 0 <= condCDF ρ a r :=
  stieltjesOfMeasurableRat_nonneg _ a r

/--
theorem `condCDF_le_one` / 定理 `condCDF_le_one`

English:
theorem condCDF_le_one
  given: (ρ : Measure (α × Real)) (a : α) (x : Real)
  statement: condCDF ρ a x <= 1
  proof: stieltjesOfMeasurableRat_le_one _ _ _

中文:
定理 condCDF_le_one
  条件: (ρ : 测度 (α × 实数)) (a : α) (x : 实数)
  结论: condCDF ρ a x <= 1
  证明: stieltjesOfMeasurableRat_le_one _ _ _

Depends on / 依赖: stieltjesOfMeasurableRat_le_one
-/
theorem condCDF_le_one (ρ : Measure (α × Real)) (a : α) (x : Real) : condCDF ρ a x <= 1 :=
  stieltjesOfMeasurableRat_le_one _ _ _

/--
theorem `tendsto_condCDF_atBot` / 定理 `tendsto_condCDF_atBot`

English:
theorem tendsto_condCDF_atBot
  given: (ρ : Measure (α × Real)) (a : α)
  proof: tendsto_stieltjesOfMeasurableRat_atBot _ _

中文:
定理 tendsto_condCDF_atBot
  条件: (ρ : 测度 (α × 实数)) (a : α)
  证明: tendsto_stieltjesOfMeasurableRat_atBot _ _

Depends on / 依赖: tendsto_stieltjesOfMeasurableRat_atBot
-/
theorem tendsto_condCDF_atBot (ρ : Measure (α × Real)) (a : α) :
    Tendsto (condCDF ρ a) atBot (𝓝 0) := tendsto_stieltjesOfMeasurableRat_atBot _ _

/--
theorem `tendsto_condCDF_atTop` / 定理 `tendsto_condCDF_atTop`

English:
theorem tendsto_condCDF_atTop
  given: (ρ : Measure (α × Real)) (a : α)
  proof: tendsto_stieltjesOfMeasurableRat_atTop _ _

中文:
定理 tendsto_condCDF_atTop
  条件: (ρ : 测度 (α × 实数)) (a : α)
  证明: tendsto_stieltjesOfMeasurableRat_atTop _ _

Depends on / 依赖: tendsto_stieltjesOfMeasurableRat_atTop
-/
theorem tendsto_condCDF_atTop (ρ : Measure (α × Real)) (a : α) :
    Tendsto (condCDF ρ a) atTop (𝓝 1) := tendsto_stieltjesOfMeasurableRat_atTop _ _

/--
theorem `condCDF_ae_eq` / 定理 `condCDF_ae_eq`

English:
theorem condCDF_ae_eq
  given: (ρ : Measure (α × Real)) [IsFiniteMeasure ρ] (r : Rat)
  proof: by
  simp_rw [condCDF_eq_stieltjesOfMeasurableRat_unit_prod ρ]
  exact stieltjesOfMeasurableRat_ae_eq (isRatCondKernelCDF_preCDF ρ) () r

中文:
定理 condCDF_ae_eq
  条件: (ρ : 测度 (α × 实数)) [是有限测度 ρ] (r : 有理数)
  证明: by
  simp_rw [condCDF_eq_stieltjesOfMeasurableRat_unit_prod ρ]
  exact stieltjesOfMeasurableRat_ae_eq (isRatCondKernelCDF_preCDF ρ) () r

Depends on / 依赖: condCDF_eq_stieltjesOfMeasurableRat_unit_prod, isRatCondKernelCDF_preCDF, simp_rw, stieltjesOfMeasurableRat_ae_eq
-/
theorem condCDF_ae_eq (ρ : Measure (α × Real)) [IsFiniteMeasure ρ] (r : Rat) :
    (fun a => condCDF ρ a r) =ᵐ[ρ.fst] fun a => (preCDF ρ r a).toReal := by
  simp_rw [condCDF_eq_stieltjesOfMeasurableRat_unit_prod ρ]
  exact stieltjesOfMeasurableRat_ae_eq (isRatCondKernelCDF_preCDF ρ) () r

/--
theorem `ofReal_condCDF_ae_eq` / 定理 `ofReal_condCDF_ae_eq`

English:
theorem ofReal_condCDF_ae_eq
  given: (ρ : Measure (α × Real)) [IsFiniteMeasure ρ] (r : Rat)
  proof: by
  filter_upwards [condCDF_ae_eq ρ r, preCDF_le_one ρ] with a ha ha_le_one
  rw [ha]; rw [ENNReal.ofReal_toReal]
  exact ((ha_le_one r).trans_lt ENNReal.one_lt_top).ne

中文:
定理 of实数_condCDF_ae_eq
  条件: (ρ : 测度 (α × 实数)) [是有限测度 ρ] (r : 有理数)
  证明: by
  filter_upwards [condCDF_ae_eq ρ r, preCDF_le_one ρ] with a ha ha_le_one
  rw [ha]; rw [ENNReal.ofReal_toReal]
  exact ((ha_le_one r).trans_lt ENNReal.one_lt_top).ne

Depends on / 依赖: ENNReal, ENNReal.ofReal_toReal, ENNReal.one_lt_top, condCDF_ae_eq, filter_upwards, ha_le_one, ofReal_toReal, one_lt_top, preCDF_le_one, trans_lt
-/
theorem ofReal_condCDF_ae_eq (ρ : Measure (α × Real)) [IsFiniteMeasure ρ] (r : Rat) :
    (fun a => ENNReal.ofReal (condCDF ρ a r)) =ᵐ[ρ.fst] preCDF ρ r := by
  filter_upwards [condCDF_ae_eq ρ r, preCDF_le_one ρ] with a ha ha_le_one
  rw [ha]; rw [ENNReal.ofReal_toReal]
  exact ((ha_le_one r).trans_lt ENNReal.one_lt_top).ne

/--
theorem `measurable_condCDF` / 定理 `measurable_condCDF`

English:
theorem measurable_condCDF
  given: (ρ : Measure (α × Real)) (x : Real)
  statement: Measurable fun a => condCDF ρ a x
  proof: measurable_stieltjesOfMeasurableRat _ _

中文:
定理 measurable_condCDF
  条件: (ρ : 测度 (α × 实数)) (x : 实数)
  结论: 可测 fun a => condCDF ρ a x
  证明: measurable_stieltjesOfMeasurableRat _ _

Depends on / 依赖: measurable_stieltjesOfMeasurableRat
-/
theorem measurable_condCDF (ρ : Measure (α × Real)) (x : Real) : Measurable fun a => condCDF ρ a x :=
  measurable_stieltjesOfMeasurableRat _ _

/--
theorem `stronglyMeasurable_condCDF` / 定理 `stronglyMeasurable_condCDF`

English:
theorem stronglyMeasurable_condCDF
  given: (ρ : Measure (α × Real)) (x : Real)
  proof: stronglyMeasurable_stieltjesOfMeasurableRat _ _

中文:
定理 stronglyMeasurable_condCDF
  条件: (ρ : 测度 (α × 实数)) (x : 实数)
  证明: stronglyMeasurable_stieltjesOfMeasurableRat _ _

Depends on / 依赖: stronglyMeasurable_stieltjesOfMeasurableRat
-/
theorem stronglyMeasurable_condCDF (ρ : Measure (α × Real)) (x : Real) :
    StronglyMeasurable fun a => condCDF ρ a x := stronglyMeasurable_stieltjesOfMeasurableRat _ _

/--
theorem `setLIntegral_condCDF` / 定理 `setLIntegral_condCDF`

English:
theorem setLIntegral_condCDF
  statement: (ρ : Measure (α × Real)) [IsFiniteMeasure ρ] (x : Real) {s : Set α}
  proof: (isCondKernelCDF_condCDF ρ).setLIntegral () hs x

中文:
定理 setL整数egral_condCDF
  结论: (ρ : 测度 (α × 实数)) [是有限测度 ρ] (x : 实数) {s : 集合 α}
  证明: (isCondKernelCDF_condCDF ρ).setLIntegral () hs x

Depends on / 依赖: isCondKernelCDF_condCDF, setLIntegral
-/
theorem setLIntegral_condCDF (ρ : Measure (α × Real)) [IsFiniteMeasure ρ] (x : Real) {s : Set α}
    (hs : MeasurableSet s) :
    ∫⁻ a in s, ENNReal.ofReal (condCDF ρ a x) ∂ρ.fst = ρ (s ×ˢ Iic x) :=
  (isCondKernelCDF_condCDF ρ).setLIntegral () hs x

/--
theorem `lintegral_condCDF` / 定理 `lintegral_condCDF`

English:
theorem lintegral_condCDF
  given: (ρ : Measure (α × Real)) [IsFiniteMeasure ρ] (x : Real)
  proof: (isCondKernelCDF_condCDF ρ).lintegral () x

中文:
定理 lintegral_condCDF
  条件: (ρ : 测度 (α × 实数)) [是有限测度 ρ] (x : 实数)
  证明: (isCondKernelCDF_condCDF ρ).lintegral () x

Depends on / 依赖: isCondKernelCDF_condCDF, lintegral
-/
theorem lintegral_condCDF (ρ : Measure (α × Real)) [IsFiniteMeasure ρ] (x : Real) :
    ∫⁻ a, ENNReal.ofReal (condCDF ρ a x) ∂ρ.fst = ρ (univ ×ˢ Iic x) :=
  (isCondKernelCDF_condCDF ρ).lintegral () x

/--
theorem `integrable_condCDF` / 定理 `integrable_condCDF`

English:
theorem integrable_condCDF
  given: (ρ : Measure (α × Real)) [IsFiniteMeasure ρ] (x : Real)
  proof: (isCondKernelCDF_condCDF ρ).integrable () x

中文:
定理 integrable_condCDF
  条件: (ρ : 测度 (α × 实数)) [是有限测度 ρ] (x : 实数)
  证明: (isCondKernelCDF_condCDF ρ).integrable () x

Depends on / 依赖: integrable, isCondKernelCDF_condCDF
-/
theorem integrable_condCDF (ρ : Measure (α × Real)) [IsFiniteMeasure ρ] (x : Real) :
    Integrable (fun a => condCDF ρ a x) ρ.fst :=
  (isCondKernelCDF_condCDF ρ).integrable () x

/--
theorem `setIntegral_condCDF` / 定理 `setIntegral_condCDF`

English:
theorem setIntegral_condCDF
  statement: (ρ : Measure (α × Real)) [IsFiniteMeasure ρ] (x : Real) {s : Set α}
  proof: (isCondKernelCDF_condCDF ρ).setIntegral () hs x

中文:
定理 set整数egral_condCDF
  结论: (ρ : 测度 (α × 实数)) [是有限测度 ρ] (x : 实数) {s : 集合 α}
  证明: (isCondKernelCDF_condCDF ρ).setIntegral () hs x

Depends on / 依赖: isCondKernelCDF_condCDF, setIntegral
-/
theorem setIntegral_condCDF (ρ : Measure (α × Real)) [IsFiniteMeasure ρ] (x : Real) {s : Set α}
    (hs : MeasurableSet s) : ∫ a in s, condCDF ρ a x ∂ρ.fst = ρ.real (s ×ˢ Iic x) :=
  (isCondKernelCDF_condCDF ρ).setIntegral () hs x

/--
theorem `integral_condCDF` / 定理 `integral_condCDF`

English:
theorem integral_condCDF
  given: (ρ : Measure (α × Real)) [IsFiniteMeasure ρ] (x : Real)
  proof: (isCondKernelCDF_condCDF ρ).integral () x

中文:
定理 integral_condCDF
  条件: (ρ : 测度 (α × 实数)) [是有限测度 ρ] (x : 实数)
  证明: (isCondKernelCDF_condCDF ρ).integral () x

Depends on / 依赖: integral, isCondKernelCDF_condCDF
-/
theorem integral_condCDF (ρ : Measure (α × Real)) [IsFiniteMeasure ρ] (x : Real) :
    ∫ a, condCDF ρ a x ∂ρ.fst = ρ.real (univ ×ˢ Iic x) :=
  (isCondKernelCDF_condCDF ρ).integral () x

section Measure

/--
theorem `measure_condCDF_Iic` / 定理 `measure_condCDF_Iic`

English:
theorem measure_condCDF_Iic
  given: (ρ : Measure (α × Real)) (a : α) (x : Real)
  proof: by
  rw [← sub_zero (condCDF ρ a x)]
  exact (condCDF ρ a).measure_Iic (tendsto_condCDF_atBot ρ a) _

中文:
定理 measure_condCDF_Iic
  条件: (ρ : 测度 (α × 实数)) (a : α) (x : 实数)
  证明: by
  rw [← sub_zero (condCDF ρ a x)]
  exact (condCDF ρ a).measure_Iic (tendsto_condCDF_atBot ρ a) _

Depends on / 依赖: condCDF, measure_Iic, sub_zero, tendsto_condCDF_atBot
-/
theorem measure_condCDF_Iic (ρ : Measure (α × Real)) (a : α) (x : Real) :
    (condCDF ρ a).measure (Iic x) = ENNReal.ofReal (condCDF ρ a x) := by
  rw [← sub_zero (condCDF ρ a x)]
  exact (condCDF ρ a).measure_Iic (tendsto_condCDF_atBot ρ a) _

/--
theorem `measure_condCDF_univ` / 定理 `measure_condCDF_univ`

English:
theorem measure_condCDF_univ
  given: (ρ : Measure (α × Real)) (a : α)
  statement: (condCDF ρ a).measure univ = 1
  proof: by
  rw [← ENNReal.ofReal_one]; rw [← sub_zero (1 : Real)]
  exact StieltjesFunction.measure_univ _ (tendsto_condCDF_atBot ρ a) (tendsto_condCDF_atTop ρ a)

中文:
定理 measure_condCDF_univ
  条件: (ρ : 测度 (α × 实数)) (a : α)
  结论: (condCDF ρ a).measure univ = 1
  证明: by
  rw [← ENNReal.ofReal_one]; rw [← sub_zero (1 : Real)]
  exact StieltjesFunction.measure_univ _ (tendsto_condCDF_atBot ρ a) (tendsto_condCDF_atTop ρ a)

Depends on / 依赖: ENNReal, ENNReal.ofReal_one, StieltjesFunction, StieltjesFunction.measure_univ, measure_univ, ofReal_one, sub_zero, tendsto_condCDF_atBot, tendsto_condCDF_atTop
-/
theorem measure_condCDF_univ (ρ : Measure (α × Real)) (a : α) : (condCDF ρ a).measure univ = 1 := by
  rw [← ENNReal.ofReal_one]; rw [← sub_zero (1 : Real)]
  exact StieltjesFunction.measure_univ _ (tendsto_condCDF_atBot ρ a) (tendsto_condCDF_atTop ρ a)

/--
Instance `instIsProbabilityMeasureCondCDF` / 实例 `instIsProbabilityMeasureCondCDF`

English:
instance instIsProbabilityMeasureCondCDF
  signature: (ρ : Measure (α × Real)) (a : α)
  body: ⟨measure_condCDF_univ ρ a⟩

中文:
实例 instIsProbabilityMeasureCondCDF
  签名: (ρ : 测度 (α × 实数)) (a : α)
  定义体: ⟨measure_condCDF_univ ρ a⟩

Depends on / 依赖: measure_condCDF_univ
-/
instance instIsProbabilityMeasureCondCDF (ρ : Measure (α × Real)) (a : α) :
    IsProbabilityMeasure (condCDF ρ a).measure :=
  ⟨measure_condCDF_univ ρ a⟩

/--
theorem `measurable_measure_condCDF` / 定理 `measurable_measure_condCDF`

English:
theorem measurable_measure_condCDF
  given: (ρ : Measure (α × Real))
  proof: .measure_of_isPiSystem_of_isProbabilityMeasure (borel_eq_generateFrom_Iic Real) isPiSystem_Iic by
    simp_rw [forall_mem_range, measure_condCDF_Iic]
    exact fun u => (measurable_condCDF ρ u).ennreal_ofReal

中文:
定理 measurable_measure_condCDF
  条件: (ρ : 测度 (α × 实数))
  证明: .measure_of_isPiSystem_of_isProbabilityMeasure (borel_eq_generateFrom_Iic Real) isPiSystem_Iic by
    simp_rw [forall_mem_range, measure_condCDF_Iic]
    exact fun u => (measurable_condCDF ρ u).ennreal_ofReal

Depends on / 依赖: borel_eq_generateFrom_Iic, ennreal_ofReal, forall_mem_range, isPiSystem_Iic, measurable_condCDF, measure_condCDF_Iic, measure_of_isPiSystem_of_isProbabilityMeasure, simp_rw
-/
theorem measurable_measure_condCDF (ρ : Measure (α × Real)) :
    Measurable fun a => (condCDF ρ a).measure :=
.measure_of_isPiSystem_of_isProbabilityMeasure (borel_eq_generateFrom_Iic Real) isPiSystem_Iic by
    simp_rw [forall_mem_range, measure_condCDF_Iic]
    exact fun u => (measurable_condCDF ρ u).ennreal_ofReal

end Measure

end ProbabilityTheory
