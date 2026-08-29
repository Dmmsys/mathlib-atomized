/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.Function.AEEqOfIntegral
public import Mathlib.Probability.Kernel.Composition.CompProd
public import Mathlib.Probability.Kernel.Disintegration.MeasurableStieltjes

/-!
# Building a Markov kernel from a conditional cumulative distribution function

Let `κ : Kernel α (β × ℝ)` and `ν : Kernel α β` be two finite kernels.
A function `f : α × β → StieltjesFunction ℝ` is called a conditional kernel CDF of `κ` with respect
to `ν` if it is measurable, tends to 0 at -∞ and to 1 at +∞ for all `p : α × β`,
`fun b ↦ f (a, b) x` is `(ν a)`-integrable for all `a : α` and `x : ℝ` and for all measurable
sets `s : Set β`, `∫ b in s, f (a, b) x ∂(ν a) = (κ a).real (s ×ˢ Iic x)`.

From such a function with property `hf : IsCondKernelCDF f κ ν`, we can build a `Kernel (α × β) ℝ`
denoted by `hf.toKernel f` such that `κ = ν ⊗ₖ hf.toKernel f`.

## Main definitions

Let `κ : Kernel α (β × ℝ)` and `ν : Kernel α β`.

* `ProbabilityTheory.IsCondKernelCDF`: a function `f : α × β → StieltjesFunction ℝ` is called
  a conditional kernel CDF of `κ` with respect to `ν` if it is measurable, tends to 0 at -∞ and
  to 1 at +∞ for all `p : α × β`, if `fun b ↦ f (a, b) x` is `(ν a)`-integrable for all `a : α` and
  `x : ℝ` and for all measurable sets `s : Set β`,
  `∫ b in s, f (a, b) x ∂(ν a) = (κ a).real (s ×ˢ Iic x)`.
* `ProbabilityTheory.IsCondKernelCDF.toKernel`: from a function `f : α × β → StieltjesFunction ℝ`
  with the property `hf : IsCondKernelCDF f κ ν`, build a `Kernel (α × β) ℝ` such that
  `κ = ν ⊗ₖ hf.toKernel f`.
* `ProbabilityTheory.IsRatCondKernelCDF`: a function `f : α × β → ℚ → ℝ` is called a rational
  conditional kernel CDF of `κ` with respect to `ν` if is measurable and satisfies the same
  integral conditions as in the definition of `IsCondKernelCDF`, and the `ℚ → ℝ` function `f (a, b)`
  satisfies the properties of a Stieltjes function for `(ν a)`-almost all `b : β`.

## Main statements

* `ProbabilityTheory.isCondKernelCDF_stieltjesOfMeasurableRat`: if `f : α × β → ℚ → ℝ` has the
  property `IsRatCondKernelCDF`, then `stieltjesOfMeasurableRat f` is a function
  `α × β → StieltjesFunction ℝ` with the property `IsCondKernelCDF`.
* `ProbabilityTheory.compProd_toKernel`: for `hf : IsCondKernelCDF f κ ν`, `ν ⊗ₖ hf.toKernel f = κ`.

-/

@[expose] public section

open MeasureTheory Set Filter TopologicalSpace

open scoped NNReal ENNReal MeasureTheory Topology ProbabilityTheory

namespace ProbabilityTheory

variable {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  {κ : Kernel α (β × Real)} {ν : Kernel α β}

section stieltjesOfMeasurableRat

variable {f : α × β -> Rat -> Real}

/--
Definition of `IsRatCondKernelCDF` / `IsRatCondKernelCDF` 的定义

English:
structure IsRatCondKernelCDF
  parameters: (f : α × β -> Rat -> Real) (κ : Kernel α (β × Real)) (ν : Kernel α β)
  axioms and operations (4):
    - measurable : Measurable f
    - isRatStieltjesPoint_ae((a : α)) : forallᵐ b ∂(ν a), IsRatStieltjesPoint f (a, b)
    - integrable((a : α) (q : Rat)) : Integrable (fun b => f (a, b) q) (ν a)
    - setIntegral((a : α) {s : Set β} (_hs : MeasurableSet s) (q : Rat)) : ∫ b in s, f (a, b) q ∂(ν a) = (κ a).real (s ×ˢ Iic (q : Real))

中文:
结构 是RatCondKernelCDF
  参数: (f : α × β -> 有理数 -> 实数) (κ : 核 α (β × 实数)) (ν : 核 α β)
  公理与运算 (4 个):
    - measurable : 可测 f
    - isRatStieltjesPoint_ae((a : α)) : 对任意ᵐ b ∂(ν a), 是RatStieltjesPoint f (a, b)
    - integrable((a : α) (q : 有理数)) : 可积 (fun b => f (a, b) q) (ν a)
    - setIntegral((a : α) {s : 集合 β} (_hs : 可测集 s) (q : 有理数)) : ∫ b in s, f (a, b) q ∂(ν a) = (κ a).real (s ×ˢ 左无界右闭区间 (q : 实数))
-/
structure IsRatCondKernelCDF (f : α × β -> Rat -> Real) (κ : Kernel α (β × Real)) (ν : Kernel α β) :
    Prop where
  measurable : Measurable f
  isRatStieltjesPoint_ae (a : α) : forallᵐ b ∂(ν a), IsRatStieltjesPoint f (a, b)
  integrable (a : α) (q : Rat) : Integrable (fun b => f (a, b) q) (ν a)
  setIntegral (a : α) {s : Set β} (_hs : MeasurableSet s) (q : Rat) :
    ∫ b in s, f (a, b) q ∂(ν a) = (κ a).real (s ×ˢ Iic (q : Real))

/--
lemma `IsRatCondKernelCDF.mono` / 引理 `IsRatCondKernelCDF.mono`

English:
lemma IsRatCondKernelCDF.mono
  given: (hf : IsRatCondKernelCDF f κ ν) (a : α)
  proof: by
  filter_upwards [hf.isRatStieltjesPoint_ae a] with b hb using hb.mono

中文:
引理 是RatCondKernelCDF.mono
  条件: (hf : 是RatCondKernelCDF f κ ν) (a : α)
  证明: by
  filter_upwards [hf.isRatStieltjesPoint_ae a] with b hb using hb.mono

Depends on / 依赖: filter_upwards, hb.mono, hf.isRatStieltjesPoint_ae, isRatStieltjesPoint_ae
-/
lemma IsRatCondKernelCDF.mono (hf : IsRatCondKernelCDF f κ ν) (a : α) :
    forallᵐ b ∂(ν a), Monotone (f (a, b)) := by
  filter_upwards [hf.isRatStieltjesPoint_ae a] with b hb using hb.mono

/--
lemma `IsRatCondKernelCDF.tendsto_atTop_one` / 引理 `IsRatCondKernelCDF.tendsto_atTop_one`

English:
lemma IsRatCondKernelCDF.tendsto_atTop_one
  given: (hf : IsRatCondKernelCDF f κ ν) (a : α)
  proof: by
  filter_upwards [hf.isRatStieltjesPoint_ae a] with b hb using hb.tendsto_atTop_one

中文:
引理 是RatCondKernelCDF.tendsto_atTop_one
  条件: (hf : 是RatCondKernelCDF f κ ν) (a : α)
  证明: by
  filter_upwards [hf.isRatStieltjesPoint_ae a] with b hb using hb.tendsto_atTop_one

Depends on / 依赖: filter_upwards, hb.tendsto_atTop_one, hf.isRatStieltjesPoint_ae, isRatStieltjesPoint_ae, tendsto_atTop_one
-/
lemma IsRatCondKernelCDF.tendsto_atTop_one (hf : IsRatCondKernelCDF f κ ν) (a : α) :
    forallᵐ b ∂(ν a), Tendsto (f (a, b)) atTop (𝓝 1) := by
  filter_upwards [hf.isRatStieltjesPoint_ae a] with b hb using hb.tendsto_atTop_one

/--
lemma `IsRatCondKernelCDF.tendsto_atBot_zero` / 引理 `IsRatCondKernelCDF.tendsto_atBot_zero`

English:
lemma IsRatCondKernelCDF.tendsto_atBot_zero
  given: (hf : IsRatCondKernelCDF f κ ν) (a : α)
  proof: by
  filter_upwards [hf.isRatStieltjesPoint_ae a] with b hb using hb.tendsto_atBot_zero

中文:
引理 是RatCondKernelCDF.tendsto_atBot_zero
  条件: (hf : 是RatCondKernelCDF f κ ν) (a : α)
  证明: by
  filter_upwards [hf.isRatStieltjesPoint_ae a] with b hb using hb.tendsto_atBot_zero

Depends on / 依赖: filter_upwards, hb.tendsto_atBot_zero, hf.isRatStieltjesPoint_ae, isRatStieltjesPoint_ae, tendsto_atBot_zero
-/
lemma IsRatCondKernelCDF.tendsto_atBot_zero (hf : IsRatCondKernelCDF f κ ν) (a : α) :
    forallᵐ b ∂(ν a), Tendsto (f (a, b)) atBot (𝓝 0) := by
  filter_upwards [hf.isRatStieltjesPoint_ae a] with b hb using hb.tendsto_atBot_zero

/--
lemma `IsRatCondKernelCDF.iInf_rat_gt_eq` / 引理 `IsRatCondKernelCDF.iInf_rat_gt_eq`

English:
lemma IsRatCondKernelCDF.iInf_rat_gt_eq
  given: (hf : IsRatCondKernelCDF f κ ν) (a : α)
  proof: by
  filter_upwards [hf.isRatStieltjesPoint_ae a] with b hb using hb.iInf_rat_gt_eq

中文:
引理 是RatCondKernelCDF.iInf_rat_gt_eq
  条件: (hf : 是RatCondKernelCDF f κ ν) (a : α)
  证明: by
  filter_upwards [hf.isRatStieltjesPoint_ae a] with b hb using hb.iInf_rat_gt_eq

Depends on / 依赖: filter_upwards, hb.iInf_rat_gt_eq, hf.isRatStieltjesPoint_ae, iInf_rat_gt_eq, isRatStieltjesPoint_ae
-/
lemma IsRatCondKernelCDF.iInf_rat_gt_eq (hf : IsRatCondKernelCDF f κ ν) (a : α) :
    forallᵐ b ∂(ν a), forall q, ⨅ r : Ioi q, f (a, b) r = f (a, b) q := by
  filter_upwards [hf.isRatStieltjesPoint_ae a] with b hb using hb.iInf_rat_gt_eq

/--
lemma `stieltjesOfMeasurableRat_ae_eq` / 引理 `stieltjesOfMeasurableRat_ae_eq`

English:
lemma stieltjesOfMeasurableRat_ae_eq
  given: (hf : IsRatCondKernelCDF f κ ν) (a : α) (q : Rat)
  proof: by
  filter_upwards [hf.isRatStieltjesPoint_ae a] with a ha
  rw [stieltjesOfMeasurableRat_eq]; rw [toRatCDF_of_isRatStieltjesPoint ha]

中文:
引理 stieltjesOfMeasurableRat_ae_eq
  条件: (hf : 是RatCondKernelCDF f κ ν) (a : α) (q : 有理数)
  证明: by
  filter_upwards [hf.isRatStieltjesPoint_ae a] with a ha
  rw [stieltjesOfMeasurableRat_eq]; rw [toRatCDF_of_isRatStieltjesPoint ha]

Depends on / 依赖: filter_upwards, hf.isRatStieltjesPoint_ae, isRatStieltjesPoint_ae, stieltjesOfMeasurableRat_eq, toRatCDF_of_isRatStieltjesPoint
-/
lemma stieltjesOfMeasurableRat_ae_eq (hf : IsRatCondKernelCDF f κ ν) (a : α) (q : Rat) :
    (fun b => stieltjesOfMeasurableRat f hf.measurable (a, b) q) =ᵐ[ν a] fun b => f (a, b) q := by
  filter_upwards [hf.isRatStieltjesPoint_ae a] with a ha
  rw [stieltjesOfMeasurableRat_eq]; rw [toRatCDF_of_isRatStieltjesPoint ha]

/--
lemma `setIntegral_stieltjesOfMeasurableRat_rat` / 引理 `setIntegral_stieltjesOfMeasurableRat_rat`

English:
lemma setIntegral_stieltjesOfMeasurableRat_rat
  statement: (hf : IsRatCondKernelCDF f κ ν) (a : α) (q : Rat)
  proof: by
  rw [setIntegral_congr_ae hs (g := fun b => f (a]; rw [b) q) ?_]; rw [hf.setIntegral a hs]
  filter_upwards [stieltjesOfMeasurableRat_ae_eq hf a q] with b hb using fun _ => hb

中文:
引理 set整数egral_stieltjesOfMeasurableRat_rat
  结论: (hf : 是RatCondKernelCDF f κ ν) (a : α) (q : 有理数)
  证明: by
  rw [setIntegral_congr_ae hs (g := fun b => f (a]; rw [b) q) ?_]; rw [hf.setIntegral a hs]
  filter_upwards [stieltjesOfMeasurableRat_ae_eq hf a q] with b hb using fun _ => hb

Depends on / 依赖: filter_upwards, hf.setIntegral, setIntegral, setIntegral_congr_ae, stieltjesOfMeasurableRat_ae_eq
-/
lemma setIntegral_stieltjesOfMeasurableRat_rat (hf : IsRatCondKernelCDF f κ ν) (a : α) (q : Rat)
    {s : Set β} (hs : MeasurableSet s) :
    ∫ b in s, stieltjesOfMeasurableRat f hf.measurable (a, b) q ∂(ν a)
      = (κ a).real (s ×ˢ Iic (q : Real)) := by
  rw [setIntegral_congr_ae hs (g := fun b => f (a]; rw [b) q) ?_]; rw [hf.setIntegral a hs]
  filter_upwards [stieltjesOfMeasurableRat_ae_eq hf a q] with b hb using fun _ => hb

/--
lemma `setLIntegral_stieltjesOfMeasurableRat_rat` / 引理 `setLIntegral_stieltjesOfMeasurableRat_rat`

English:
lemma setLIntegral_stieltjesOfMeasurableRat_rat
  statement: [IsFiniteKernel κ] (hf : IsRatCondKernelCDF f κ ν)
  proof: by
  rw [← ofReal_integral_eq_lintegral_ofReal]
  · rw [setIntegral_stieltjesOfMeasurableRat_rat hf a q hs, ofReal_measureReal]
  · refine Integrable.restrict ?_
    rw [integrable_congr (stieltjesOfMeasurableRat_ae_eq hf a q)]
    exact hf.integrable a q
  · exact ae_of_all _ (fun x => stieltjesOfM

中文:
引理 setL整数egral_stieltjesOfMeasurableRat_rat
  结论: [是FiniteKernel κ] (hf : 是RatCondKernelCDF f κ ν)
  证明: by
  rw [← ofReal_integral_eq_lintegral_ofReal]
  · rw [setIntegral_stieltjesOfMeasurableRat_rat hf a q hs, ofReal_measureReal]
  · refine Integrable.restrict ?_
    rw [integrable_congr (stieltjesOfMeasurableRat_ae_eq hf a q)]
    exact hf.integrable a q
  · exact ae_of_all _ (fun x => stieltjesOfM

Depends on / 依赖: Integrable, Integrable.restrict, ae_of_all, hf.integrable, integrable, integrable_congr, ofReal_integral_eq_lintegral_ofReal, ofReal_measureReal, restrict, setIntegral_stieltjesOfMeasurableRat_rat, stieltjesOfMeasurableRat_ae_eq, stieltjesOfMeasurableRat_nonneg
-/
lemma setLIntegral_stieltjesOfMeasurableRat_rat [IsFiniteKernel κ] (hf : IsRatCondKernelCDF f κ ν)
    (a : α) (q : Rat) {s : Set β} (hs : MeasurableSet s) :
    ∫⁻ b in s, ENNReal.ofReal (stieltjesOfMeasurableRat f hf.measurable (a, b) q) ∂(ν a)
      = κ a (s ×ˢ Iic (q : Real)) := by
  rw [← ofReal_integral_eq_lintegral_ofReal]
  · rw [setIntegral_stieltjesOfMeasurableRat_rat hf a q hs, ofReal_measureReal]
  · refine Integrable.restrict ?_
    rw [integrable_congr (stieltjesOfMeasurableRat_ae_eq hf a q)]
    exact hf.integrable a q
  · exact ae_of_all _ (fun x => stieltjesOfMeasurableRat_nonneg _ _ _)

/--
lemma `setLIntegral_stieltjesOfMeasurableRat` / 引理 `setLIntegral_stieltjesOfMeasurableRat`

English:
lemma setLIntegral_stieltjesOfMeasurableRat
  statement: [IsFiniteKernel κ] (hf : IsRatCondKernelCDF f κ ν)
  proof: by
  -- We have the result for `x : ℚ` thanks to `setLIntegral_stieltjesOfMeasurableRat_rat`.
  -- We use a monotone convergence argument to extend it to the reals.
  by_cases hρ_zero : (ν a).restrict s = 0
  · rw [hρ_zero, lintegral_zero_measure]
    have ⟨q, hq⟩ := exists_rat_gt x
    suffices κ a

中文:
引理 setL整数egral_stieltjesOfMeasurableRat
  结论: [是FiniteKernel κ] (hf : 是RatCondKernelCDF f κ ν)
  证明: by
  -- We have the result for `x : ℚ` thanks to `setLIntegral_stieltjesOfMeasurableRat_rat`.
  -- We use a monotone convergence argument to extend it to the reals.
  by_cases hρ_zero : (ν a).restrict s = 0
  · rw [hρ_zero, lintegral_zero_measure]
    have ⟨q, hq⟩ := exists_rat_gt x
    suffices κ a
-/
lemma setLIntegral_stieltjesOfMeasurableRat [IsFiniteKernel κ] (hf : IsRatCondKernelCDF f κ ν)
    (a : α) (x : Real) {s : Set β} (hs : MeasurableSet s) :
    ∫⁻ b in s, ENNReal.ofReal (stieltjesOfMeasurableRat f hf.measurable (a, b) x) ∂(ν a)
      = κ a (s ×ˢ Iic x) := by
  -- We have the result for `x : ℚ` thanks to `setLIntegral_stieltjesOfMeasurableRat_rat`.
  -- We use a monotone convergence argument to extend it to the reals.
  by_cases hρ_zero : (ν a).restrict s = 0
  · rw [hρ_zero, lintegral_zero_measure]
    have ⟨q, hq⟩ := exists_rat_gt x
    suffices κ a (s ×ˢ Iic (q : Real)) = 0 by
      symm
      refine measure_mono_null (fun p => ?_) this
      simp only [mem_prod, mem_Iic, and_imp]
      exact fun h1 h2 => ⟨h1, h2.trans hq.le⟩
    suffices (κ a).real (s ×ˢ Iic (q : Real)) = 0 by
      rw [measureReal_eq_zero_iff] at this
      simpa [measure_ne_top] using this
    rw [← hf.setIntegral a hs q]
    simp [hρ_zero]
  have h : ∫⁻ b in s, ENNReal.ofReal (stieltjesOfMeasurableRat f hf.measurable (a, b) x) ∂(ν a)
      = ∫⁻ b in s, ⨅ r : { r' : Rat // x < r' },
        ENNReal.ofReal (stieltjesOfMeasurableRat f hf.measurable (a, b) r) ∂(ν a) := by
    congr with b : 1
    simp_rw [← measure_stieltjesOfMeasurableRat_Iic]
    rw [← Monotone.measure_iInter]
    · congr with y : 1
      simp only [mem_Iic, mem_iInter, Subtype.forall]
      exact le_iff_forall_lt_rat_imp_le
· exact fun r r' hrr' => Iic_subset_Iic.mpr mod_cast hrr'
    · exact fun _ => nullMeasurableSet_Iic
    · obtain ⟨q, hq⟩ := exists_rat_gt x
      exact ⟨⟨q, hq⟩, measure_ne_top _ _⟩
  have h_nonempty : Nonempty { r' : Rat // x < ↑r' } := by
    obtain ⟨r, hrx⟩ := exists_rat_gt x
    exact ⟨⟨r, hrx⟩⟩
  rw [h]; rw [lintegral_iInf_directed_of_measurable hρ_zero fun q : { r' : Rat // x < ↑r' } => ?_]
  rotate_left
  · intro b
    rw [setLIntegral_stieltjesOfMeasurableRat_rat hf a _ hs]
    exact measure_ne_top _ _
  · refine Monotone.directed_ge fun i j hij b => ?_
    simp_rw [← measure_stieltjesOfMeasurableRat_Iic]
    refine measure_mono (Iic_subset_Iic.mpr ?_)
    exact mod_cast hij
  · refine Measurable.ennreal_ofReal ?_
    exact (measurable_stieltjesOfMeasurableRat hf.measurable _).comp measurable_prodMk_left
  simp_rw [setLIntegral_stieltjesOfMeasurableRat_rat hf _ _ hs]
  rw [← Monotone.measure_iInter]
  · rw [← prod_iInter]
    congr with y
    simp only [mem_iInter, mem_Iic, Subtype.forall]
    exact ⟨le_of_forall_lt_rat_imp_le, fun hyx q hq => hyx.trans hq.le⟩
  · exact fun i j hij => prod_mono_right (by gcongr)
  · exact fun i => (hs.prod measurableSet_Iic).nullMeasurableSet
  · exact ⟨h_nonempty.some, measure_ne_top _ _⟩

/--
lemma `lintegral_stieltjesOfMeasurableRat` / 引理 `lintegral_stieltjesOfMeasurableRat`

English:
lemma lintegral_stieltjesOfMeasurableRat
  statement: [IsFiniteKernel κ] (hf : IsRatCondKernelCDF f κ ν)
  proof: by
  rw [← setLIntegral_univ]; rw [setLIntegral_stieltjesOfMeasurableRat hf _ _ MeasurableSet.univ]

中文:
引理 lintegral_stieltjesOfMeasurableRat
  结论: [是FiniteKernel κ] (hf : 是RatCondKernelCDF f κ ν)
  证明: by
  rw [← setLIntegral_univ]; rw [setLIntegral_stieltjesOfMeasurableRat hf _ _ MeasurableSet.univ]

Depends on / 依赖: MeasurableSet, MeasurableSet.univ, setLIntegral_stieltjesOfMeasurableRat, setLIntegral_univ
-/
lemma lintegral_stieltjesOfMeasurableRat [IsFiniteKernel κ] (hf : IsRatCondKernelCDF f κ ν)
    (a : α) (x : Real) :
    ∫⁻ b, ENNReal.ofReal (stieltjesOfMeasurableRat f hf.measurable (a, b) x) ∂(ν a)
      = κ a (univ ×ˢ Iic x) := by
  rw [← setLIntegral_univ]; rw [setLIntegral_stieltjesOfMeasurableRat hf _ _ MeasurableSet.univ]

/--
lemma `integrable_stieltjesOfMeasurableRat` / 引理 `integrable_stieltjesOfMeasurableRat`

English:
lemma integrable_stieltjesOfMeasurableRat
  statement: [IsFiniteKernel κ] (hf : IsRatCondKernelCDF f κ ν)
  proof: by
  have : (fun b => stieltjesOfMeasurableRat f hf.measurable (a, b) x)
      = fun b => (ENNReal.ofReal (stieltjesOfMeasurableRat f hf.measurable (a, b) x)).toReal := by
    ext t
    rw [ENNReal.toReal_ofReal]
    exact stieltjesOfMeasurableRat_nonneg _ _ _
  rw [this]
  refine integrable_toReal_

中文:
引理 integrable_stieltjesOfMeasurableRat
  结论: [是FiniteKernel κ] (hf : 是RatCondKernelCDF f κ ν)
  证明: by
  have : (fun b => stieltjesOfMeasurableRat f hf.measurable (a, b) x)
      = fun b => (ENNReal.ofReal (stieltjesOfMeasurableRat f hf.measurable (a, b) x)).toReal := by
    ext t
    rw [ENNReal.toReal_ofReal]
    exact stieltjesOfMeasurableRat_nonneg _ _ _
  rw [this]
  refine integrable_toReal_

Depends on / 依赖: ENNReal, ENNReal.ofReal, ENNReal.toReal_ofReal, Measurable, Measurable.ennreal_ofReal, aemeasurable, ennreal_ofReal, hf.measurable, integrable_toReal_of_lintegral_ne_top, lintegral_stieltjesOfMeasurableRat, measur, measurable, measurable_prodMk_left, measurable_stieltjesOfMeasurableRat, ofReal, stieltjesOfMeasurableRat, stieltjesOfMeasurableRat_nonneg, toReal, toReal_ofReal
-/
lemma integrable_stieltjesOfMeasurableRat [IsFiniteKernel κ] (hf : IsRatCondKernelCDF f κ ν)
    (a : α) (x : Real) :
    Integrable (fun b => stieltjesOfMeasurableRat f hf.measurable (a, b) x) (ν a) := by
  have : (fun b => stieltjesOfMeasurableRat f hf.measurable (a, b) x)
      = fun b => (ENNReal.ofReal (stieltjesOfMeasurableRat f hf.measurable (a, b) x)).toReal := by
    ext t
    rw [ENNReal.toReal_ofReal]
    exact stieltjesOfMeasurableRat_nonneg _ _ _
  rw [this]
  refine integrable_toReal_of_lintegral_ne_top ?_ ?_
  · refine (Measurable.ennreal_ofReal ?_).aemeasurable
    exact (measurable_stieltjesOfMeasurableRat hf.measurable x).comp measurable_prodMk_left
  · rw [lintegral_stieltjesOfMeasurableRat hf]
    exact measure_ne_top _ _

/--
lemma `setIntegral_stieltjesOfMeasurableRat` / 引理 `setIntegral_stieltjesOfMeasurableRat`

English:
lemma setIntegral_stieltjesOfMeasurableRat
  statement: [IsFiniteKernel κ] (hf : IsRatCondKernelCDF f κ ν)
  proof: by
  rw [← ENNReal.ofReal_eq_ofReal_iff]; rw [ofReal_measureReal]
  rotate_left
  · exact setIntegral_nonneg hs (fun _ _ => stieltjesOfMeasurableRat_nonneg _ _ _)
  · exact ENNReal.toReal_nonneg
  rw [ofReal_integral_eq_lintegral_ofReal]; rw [setLIntegral_stieltjesOfMeasurableRat hf _ _ hs]
  · exac

中文:
引理 set整数egral_stieltjesOfMeasurableRat
  结论: [是FiniteKernel κ] (hf : 是RatCondKernelCDF f κ ν)
  证明: by
  rw [← ENNReal.ofReal_eq_ofReal_iff]; rw [ofReal_measureReal]
  rotate_left
  · exact setIntegral_nonneg hs (fun _ _ => stieltjesOfMeasurableRat_nonneg _ _ _)
  · exact ENNReal.toReal_nonneg
  rw [ofReal_integral_eq_lintegral_ofReal]; rw [setLIntegral_stieltjesOfMeasurableRat hf _ _ hs]
  · exac

Depends on / 依赖: ENNReal, ENNReal.ofReal_eq_ofReal_iff, ENNReal.toReal_nonneg, ae_of_all, integrable_stieltjesOfMeasurableRat, ofReal_eq_ofReal_iff, ofReal_integral_eq_lintegral_ofReal, ofReal_measureReal, restrict, rotate_left, setIntegral_nonneg, setLIntegral_stieltjesOfMeasurableRat, stieltjesOfMeasurableRat_nonneg, toReal_nonneg
-/
lemma setIntegral_stieltjesOfMeasurableRat [IsFiniteKernel κ] (hf : IsRatCondKernelCDF f κ ν)
    (a : α) (x : Real) {s : Set β} (hs : MeasurableSet s) :
    ∫ b in s, stieltjesOfMeasurableRat f hf.measurable (a, b) x ∂(ν a)
      = (κ a).real (s ×ˢ Iic x) := by
  rw [← ENNReal.ofReal_eq_ofReal_iff]; rw [ofReal_measureReal]
  rotate_left
  · exact setIntegral_nonneg hs (fun _ _ => stieltjesOfMeasurableRat_nonneg _ _ _)
  · exact ENNReal.toReal_nonneg
  rw [ofReal_integral_eq_lintegral_ofReal]; rw [setLIntegral_stieltjesOfMeasurableRat hf _ _ hs]
  · exact (integrable_stieltjesOfMeasurableRat hf _ _).restrict
  · exact ae_of_all _ (fun _ => stieltjesOfMeasurableRat_nonneg _ _ _)

/--
lemma `integral_stieltjesOfMeasurableRat` / 引理 `integral_stieltjesOfMeasurableRat`

English:
lemma integral_stieltjesOfMeasurableRat
  statement: [IsFiniteKernel κ] (hf : IsRatCondKernelCDF f κ ν)
  proof: by
  rw [← setIntegral_univ]; rw [setIntegral_stieltjesOfMeasurableRat hf _ _ MeasurableSet.univ]

中文:
引理 integral_stieltjesOfMeasurableRat
  结论: [是FiniteKernel κ] (hf : 是RatCondKernelCDF f κ ν)
  证明: by
  rw [← setIntegral_univ]; rw [setIntegral_stieltjesOfMeasurableRat hf _ _ MeasurableSet.univ]

Depends on / 依赖: Ideal.Quotient.mk, Ideal.Quotient.mk_surjective, MeasurableSet, MeasurableSet.univ, QuasiFiniteAt, Quotient, WeaklyQuasiFiniteAt, mk_surjective, of_surjective_algHom, setIntegral_stieltjesOfMeasurableRat, setIntegral_univ, weaklyQuasiFiniteAt_iff
-/
lemma integral_stieltjesOfMeasurableRat [IsFiniteKernel κ] (hf : IsRatCondKernelCDF f κ ν)
    (a : α) (x : Real) :
    ∫ b, stieltjesOfMeasurableRat f hf.measurable (a, b) x ∂(ν a)
      = (κ a).real (univ ×ˢ Iic x) := by
  rw [← setIntegral_univ]; rw [setIntegral_stieltjesOfMeasurableRat hf _ _ MeasurableSet.univ]

end stieltjesOfMeasurableRat

section isRatCondKernelCDFAux

variable {f : α × β -> Rat -> Real}

/--
Definition of `IsRatCondKernelCDFAux` / `IsRatCondKernelCDFAux` 的定义

English:
structure IsRatCondKernelCDFAux
  parameters: (f : α × β -> Rat -> Real) (κ : Kernel α (β × Real)) (ν : Kernel α β)
  axioms and operations (8):
    - measurable : Measurable f
    - mono'((a : α) {q r : Rat} (_hqr : q <= r)) : forallᵐ c ∂(ν a), f (a, c) q <= f (a, c) r
    - nonneg'((a : α) (q : Rat)) : forallᵐ c ∂(ν a), 0 <= f (a, c) q
    - le_one'((a : α) (q : Rat)) : forallᵐ c ∂(ν a), f (a, c) q <= 1
    - tendsto_integral_of_antitone((a : α) (seq : Nat -> Rat) (_hs : Antitone seq) (_hs_tendsto : Tendsto seq atTop atBot)) : Tendsto (fun m => ∫ c, f (a, c) (seq m) ∂(ν a)) atTop (𝓝 0)
    - tendsto_integral_of_monotone((a : α) (seq : Nat -> Rat) (_hs : Monotone seq) (_hs_tendsto : Tendsto seq atTop atTop)) : Tendsto (fun m => ∫ c, f (a, c) (seq m) ∂(ν a)) atTop (𝓝 ((ν a).real univ))
    - integrable((a : α) (q : Rat)) : Integrable (fun c => f (a, c) q) (ν a)
    - setIntegral((a : α) {A : Set β} (_hA : MeasurableSet A) (q : Rat)) : ∫ c in A, f (a, c) q ∂(ν a) = (κ a).real (A ×ˢ Iic ↑q)

中文:
结构 是RatCondKernelCDFAux
  参数: (f : α × β -> 有理数 -> 实数) (κ : 核 α (β × 实数)) (ν : 核 α β)
  公理与运算 (8 个):
    - measurable : 可测 f
    - mono'((a : α) {q r : 有理数} (_hqr : q <= r)) : 对任意ᵐ c ∂(ν a), f (a, c) q <= f (a, c) r
    - nonneg'((a : α) (q : 有理数)) : 对任意ᵐ c ∂(ν a), 0 <= f (a, c) q
    - le_one'((a : α) (q : 有理数)) : 对任意ᵐ c ∂(ν a), f (a, c) q <= 1
    - tendsto_integral_of_antitone((a : α) (seq : 自然数 -> 有理数) (_hs : 递减 seq) (_hs_tendsto : 收敛 seq atTop atBot)) : 收敛 (fun m => ∫ c, f (a, c) (seq m) ∂(ν a)) atTop (𝓝 0)
    - tendsto_integral_of_monotone((a : α) (seq : 自然数 -> 有理数) (_hs : 递增 seq) (_hs_tendsto : 收敛 seq atTop atTop)) : 收敛 (fun m => ∫ c, f (a, c) (seq m) ∂(ν a)) atTop (𝓝 ((ν a).real univ))
    - integrable((a : α) (q : 有理数)) : 可积 (fun c => f (a, c) q) (ν a)
    - setIntegral((a : α) {A : 集合 β} (_hA : 可测集 A) (q : 有理数)) : ∫ c in A, f (a, c) q ∂(ν a) = (κ a).real (A ×ˢ 左无界右闭区间 ↑q)
-/
structure IsRatCondKernelCDFAux (f : α × β -> Rat -> Real) (κ : Kernel α (β × Real)) (ν : Kernel α β) :
    Prop where
  measurable : Measurable f
  mono' (a : α) {q r : Rat} (_hqr : q <= r) : forallᵐ c ∂(ν a), f (a, c) q <= f (a, c) r
  nonneg' (a : α) (q : Rat) : forallᵐ c ∂(ν a), 0 <= f (a, c) q
  le_one' (a : α) (q : Rat) : forallᵐ c ∂(ν a), f (a, c) q <= 1
  /- Same as `Tendsto (fun q : ℚ ↦ ∫ c, f (a, c) q ∂(ν a)) atBot (𝓝 0)` but slightly easier
  to prove in the current applications of this definition (some integral convergence lemmas
  currently apply only to `ℕ`, not `ℚ`) -/
  tendsto_integral_of_antitone (a : α) (seq : Nat -> Rat) (_hs : Antitone seq)
    (_hs_tendsto : Tendsto seq atTop atBot) :
    Tendsto (fun m => ∫ c, f (a, c) (seq m) ∂(ν a)) atTop (𝓝 0)
  /- Same as `Tendsto (fun q : ℚ ↦ ∫ c, f (a, c) q ∂(ν a)) atTop (𝓝 ((ν a).real univ))` but
  slightly easier to prove in the current applications of this definition (some integral convergence
  lemmas currently apply only to `ℕ`, not `ℚ`) -/
  tendsto_integral_of_monotone (a : α) (seq : Nat -> Rat) (_hs : Monotone seq)
    (_hs_tendsto : Tendsto seq atTop atTop) :
    Tendsto (fun m => ∫ c, f (a, c) (seq m) ∂(ν a)) atTop (𝓝 ((ν a).real univ))
  integrable (a : α) (q : Rat) : Integrable (fun c => f (a, c) q) (ν a)
  setIntegral (a : α) {A : Set β} (_hA : MeasurableSet A) (q : Rat) :
    ∫ c in A, f (a, c) q ∂(ν a) = (κ a).real (A ×ˢ Iic ↑q)

/--
lemma `IsRatCondKernelCDFAux.measurable_right` / 引理 `IsRatCondKernelCDFAux.measurable_right`

English:
lemma IsRatCondKernelCDFAux.measurable_right
  given: (hf : IsRatCondKernelCDFAux f κ ν) (a : α) (q : Rat)
  proof: by
  let h := hf.measurable
  rw [measurable_pi_iff] at h
  exact (h q).comp measurable_prodMk_left

中文:
引理 是RatCondKernelCDFAux.measurable_right
  条件: (hf : 是RatCondKernelCDFAux f κ ν) (a : α) (q : 有理数)
  证明: by
  let h := hf.measurable
  rw [measurable_pi_iff] at h
  exact (h q).comp measurable_prodMk_left

Depends on / 依赖: hf.measurable, measurable, measurable_pi_iff, measurable_prodMk_left
-/
lemma IsRatCondKernelCDFAux.measurable_right (hf : IsRatCondKernelCDFAux f κ ν) (a : α) (q : Rat) :
    Measurable (fun t => f (a, t) q) := by
  let h := hf.measurable
  rw [measurable_pi_iff] at h
  exact (h q).comp measurable_prodMk_left

/--
lemma `IsRatCondKernelCDFAux.mono` / 引理 `IsRatCondKernelCDFAux.mono`

English:
lemma IsRatCondKernelCDFAux.mono
  given: (hf : IsRatCondKernelCDFAux f κ ν) (a : α)
  proof: by
  unfold Monotone
  simp_rw [ae_all_iff]
  exact fun _ _ hqr => hf.mono' a hqr

中文:
引理 是RatCondKernelCDFAux.mono
  条件: (hf : 是RatCondKernelCDFAux f κ ν) (a : α)
  证明: by
  unfold Monotone
  simp_rw [ae_all_iff]
  exact fun _ _ hqr => hf.mono' a hqr

Depends on / 依赖: Monotone, ae_all_iff, hf.mono, simp_rw
-/
lemma IsRatCondKernelCDFAux.mono (hf : IsRatCondKernelCDFAux f κ ν) (a : α) :
    forallᵐ c ∂(ν a), Monotone (f (a, c)) := by
  unfold Monotone
  simp_rw [ae_all_iff]
  exact fun _ _ hqr => hf.mono' a hqr

/--
lemma `IsRatCondKernelCDFAux.nonneg` / 引理 `IsRatCondKernelCDFAux.nonneg`

English:
lemma IsRatCondKernelCDFAux.nonneg
  given: (hf : IsRatCondKernelCDFAux f κ ν) (a : α)
  proof: ae_all_iff.mpr hf.nonneg' a

中文:
引理 是RatCondKernelCDFAux.nonneg
  条件: (hf : 是RatCondKernelCDFAux f κ ν) (a : α)
  证明: ae_all_iff.mpr hf.nonneg' a

Depends on / 依赖: ae_all_iff, ae_all_iff.mpr, hf.nonneg, nonneg
-/
lemma IsRatCondKernelCDFAux.nonneg (hf : IsRatCondKernelCDFAux f κ ν) (a : α) :
forallᵐ c ∂(ν a), forall q, 0 <= f (a, c) q := ae_all_iff.mpr hf.nonneg' a

/--
lemma `IsRatCondKernelCDFAux.le_one` / 引理 `IsRatCondKernelCDFAux.le_one`

English:
lemma IsRatCondKernelCDFAux.le_one
  given: (hf : IsRatCondKernelCDFAux f κ ν) (a : α)
  proof: ae_all_iff.mpr hf.le_one' a

中文:
引理 是RatCondKernelCDFAux.le_one
  条件: (hf : 是RatCondKernelCDFAux f κ ν) (a : α)
  证明: ae_all_iff.mpr hf.le_one' a

Depends on / 依赖: ae_all_iff, ae_all_iff.mpr, hf.le_one, le_one
-/
lemma IsRatCondKernelCDFAux.le_one (hf : IsRatCondKernelCDFAux f κ ν) (a : α) :
forallᵐ c ∂(ν a), forall q, f (a, c) q <= 1 := ae_all_iff.mpr hf.le_one' a

/--
lemma `IsRatCondKernelCDFAux.tendsto_zero_of_antitone` / 引理 `IsRatCondKernelCDFAux.tendsto_zero_of_antitone`

English:
lemma IsRatCondKernelCDFAux.tendsto_zero_of_antitone
  statement: (hf : IsRatCondKernelCDFAux f κ ν)
  proof: by
  refine tendsto_of_integral_tendsto_of_antitone ?_ (integrable_const _) ?_ ?_ ?_
  · exact fun n => hf.integrable a (seq n)
  · rw [integral_zero]
    exact hf.tendsto_integral_of_antitone a seq hseq hseq_tendsto
  · filter_upwards [hf.mono a] with t ht using fun n m hnm => ht (hseq hnm)
  · fil

中文:
引理 是RatCondKernelCDFAux.tendsto_zero_of_antitone
  结论: (hf : 是RatCondKernelCDFAux f κ ν)
  证明: by
  refine tendsto_of_integral_tendsto_of_antitone ?_ (integrable_const _) ?_ ?_ ?_
  · exact fun n => hf.integrable a (seq n)
  · rw [integral_zero]
    exact hf.tendsto_integral_of_antitone a seq hseq hseq_tendsto
  · filter_upwards [hf.mono a] with t ht using fun n m hnm => ht (hseq hnm)
  · fil

Depends on / 依赖: filter_upwards, hf.integrable, hf.mono, hf.nonneg, hf.tendsto_integral_of_antitone, hseq_tendsto, integrable, integrable_const, integral_zero, nonneg, tendsto_integral_of_antitone, tendsto_of_integral_tendsto_of_antitone
-/
lemma IsRatCondKernelCDFAux.tendsto_zero_of_antitone (hf : IsRatCondKernelCDFAux f κ ν)
    [IsFiniteKernel ν] (a : α) (seq : Nat -> Rat) (hseq : Antitone seq)
    (hseq_tendsto : Tendsto seq atTop atBot) :
    forallᵐ c ∂(ν a), Tendsto (fun m => f (a, c) (seq m)) atTop (𝓝 0) := by
  refine tendsto_of_integral_tendsto_of_antitone ?_ (integrable_const _) ?_ ?_ ?_
  · exact fun n => hf.integrable a (seq n)
  · rw [integral_zero]
    exact hf.tendsto_integral_of_antitone a seq hseq hseq_tendsto
  · filter_upwards [hf.mono a] with t ht using fun n m hnm => ht (hseq hnm)
  · filter_upwards [hf.nonneg a] with c hc using fun i => hc (seq i)

/--
lemma `IsRatCondKernelCDFAux.tendsto_one_of_monotone` / 引理 `IsRatCondKernelCDFAux.tendsto_one_of_monotone`

English:
lemma IsRatCondKernelCDFAux.tendsto_one_of_monotone
  statement: (hf : IsRatCondKernelCDFAux f κ ν)
  proof: by
  refine tendsto_of_integral_tendsto_of_monotone ?_ (integrable_const _) ?_ ?_ ?_
  · exact fun n => hf.integrable a (seq n)
  · rw [MeasureTheory.integral_const, smul_eq_mul, mul_one]
    exact hf.tendsto_integral_of_monotone a seq hseq hseq_tendsto
  · filter_upwards [hf.mono a] with t ht using

中文:
引理 是RatCondKernelCDFAux.tendsto_one_of_monotone
  结论: (hf : 是RatCondKernelCDFAux f κ ν)
  证明: by
  refine tendsto_of_integral_tendsto_of_monotone ?_ (integrable_const _) ?_ ?_ ?_
  · exact fun n => hf.integrable a (seq n)
  · rw [MeasureTheory.integral_const, smul_eq_mul, mul_one]
    exact hf.tendsto_integral_of_monotone a seq hseq hseq_tendsto
  · filter_upwards [hf.mono a] with t ht using

Depends on / 依赖: MeasureTheory, MeasureTheory.integral_const, filter_upwards, hf.integrable, hf.le_one, hf.mono, hf.tendsto_integral_of_monotone, hseq_tendsto, integrable, integrable_const, integral_const, le_one, mul_one, smul_eq_mul, tendsto_integral_of_monotone, tendsto_of_integral_tendsto_of_monotone
-/
lemma IsRatCondKernelCDFAux.tendsto_one_of_monotone (hf : IsRatCondKernelCDFAux f κ ν)
    [IsFiniteKernel ν] (a : α) (seq : Nat -> Rat) (hseq : Monotone seq)
    (hseq_tendsto : Tendsto seq atTop atTop) :
    forallᵐ c ∂(ν a), Tendsto (fun m => f (a, c) (seq m)) atTop (𝓝 1) := by
  refine tendsto_of_integral_tendsto_of_monotone ?_ (integrable_const _) ?_ ?_ ?_
  · exact fun n => hf.integrable a (seq n)
  · rw [MeasureTheory.integral_const, smul_eq_mul, mul_one]
    exact hf.tendsto_integral_of_monotone a seq hseq hseq_tendsto
  · filter_upwards [hf.mono a] with t ht using fun n m hnm => ht (hseq hnm)
  · filter_upwards [hf.le_one a] with c hc using fun i => hc (seq i)

/--
lemma `IsRatCondKernelCDFAux.tendsto_atTop_one` / 引理 `IsRatCondKernelCDFAux.tendsto_atTop_one`

English:
lemma IsRatCondKernelCDFAux.tendsto_atTop_one
  statement: (hf : IsRatCondKernelCDFAux f κ ν) [IsFiniteKernel ν]
  proof: by
  suffices forallᵐ t ∂(ν a), Tendsto (fun (n : Nat) => f (a, t) n) atTop (𝓝 1) by
    filter_upwards [this, hf.mono a] with t ht h_mono
    rw [tendsto_iff_tendsto_subseq_of_monotone h_mono tendsto_natCast_atTop_atTop]
    exact ht
  filter_upwards [hf.tendsto_one_of_monotone a Nat.cast Nat.mono_

中文:
引理 是RatCondKernelCDFAux.tendsto_atTop_one
  结论: (hf : 是RatCondKernelCDFAux f κ ν) [是FiniteKernel ν]
  证明: by
  suffices forallᵐ t ∂(ν a), Tendsto (fun (n : Nat) => f (a, t) n) atTop (𝓝 1) by
    filter_upwards [this, hf.mono a] with t ht h_mono
    rw [tendsto_iff_tendsto_subseq_of_monotone h_mono tendsto_natCast_atTop_atTop]
    exact ht
  filter_upwards [hf.tendsto_one_of_monotone a Nat.cast Nat.mono_

Depends on / 依赖: Nat.cast, Nat.mono_cast, Tendsto, filter_upwards, h_mono, hf.mono, hf.tendsto_one_of_monotone, mono_cast, tendsto_iff_tendsto_subseq_of_monotone, tendsto_natCast_atTop_atTop, tendsto_one_of_monotone
-/
lemma IsRatCondKernelCDFAux.tendsto_atTop_one (hf : IsRatCondKernelCDFAux f κ ν) [IsFiniteKernel ν]
    (a : α) :
    forallᵐ t ∂(ν a), Tendsto (f (a, t)) atTop (𝓝 1) := by
  suffices forallᵐ t ∂(ν a), Tendsto (fun (n : Nat) => f (a, t) n) atTop (𝓝 1) by
    filter_upwards [this, hf.mono a] with t ht h_mono
    rw [tendsto_iff_tendsto_subseq_of_monotone h_mono tendsto_natCast_atTop_atTop]
    exact ht
  filter_upwards [hf.tendsto_one_of_monotone a Nat.cast Nat.mono_cast tendsto_natCast_atTop_atTop]
    with x hx using hx

/--
lemma `IsRatCondKernelCDFAux.tendsto_atBot_zero` / 引理 `IsRatCondKernelCDFAux.tendsto_atBot_zero`

English:
lemma IsRatCondKernelCDFAux.tendsto_atBot_zero
  statement: (hf : IsRatCondKernelCDFAux f κ ν) [IsFiniteKernel ν]
  proof: by
  suffices forallᵐ t ∂(ν a), Tendsto (fun q : Rat => f (a, t) (-q)) atTop (𝓝 0) by
    filter_upwards [this] with t ht
    exact tendsto_comp_neg_atTop_iff.mp ht
  suffices forallᵐ t ∂(ν a), Tendsto (fun (n : Nat) => f (a, t) (-n)) atTop (𝓝 0) by
    filter_upwards [this, hf.mono a] with t ht h_m

中文:
引理 是RatCondKernelCDFAux.tendsto_atBot_zero
  结论: (hf : 是RatCondKernelCDFAux f κ ν) [是FiniteKernel ν]
  证明: by
  suffices forallᵐ t ∂(ν a), Tendsto (fun q : Rat => f (a, t) (-q)) atTop (𝓝 0) by
    filter_upwards [this] with t ht
    exact tendsto_comp_neg_atTop_iff.mp ht
  suffices forallᵐ t ∂(ν a), Tendsto (fun (n : Nat) => f (a, t) (-n)) atTop (𝓝 0) by
    filter_upwards [this, hf.mono a] with t ht h_m

Depends on / 依赖: Antitone, Tendsto, comp_antitone, filter_upwards, h_anti, h_mono, h_mono.comp_antitone, hf.mono, hf.tendsto_zero_of_antitone, monotone_id, monotone_id.neg, tendsto_comp_neg_atTop_iff, tendsto_comp_neg_atTop_iff.mp, tendsto_iff_tendsto_subseq_of_antitone, tendsto_natCast_atTop_atTop, tendsto_zero_of_antitone
-/
lemma IsRatCondKernelCDFAux.tendsto_atBot_zero (hf : IsRatCondKernelCDFAux f κ ν) [IsFiniteKernel ν]
    (a : α) :
    forallᵐ t ∂(ν a), Tendsto (f (a, t)) atBot (𝓝 0) := by
  suffices forallᵐ t ∂(ν a), Tendsto (fun q : Rat => f (a, t) (-q)) atTop (𝓝 0) by
    filter_upwards [this] with t ht
    exact tendsto_comp_neg_atTop_iff.mp ht
  suffices forallᵐ t ∂(ν a), Tendsto (fun (n : Nat) => f (a, t) (-n)) atTop (𝓝 0) by
    filter_upwards [this, hf.mono a] with t ht h_mono
    have h_anti : Antitone (fun q => f (a, t) (-q)) := h_mono.comp_antitone monotone_id.neg
    exact (tendsto_iff_tendsto_subseq_of_antitone h_anti tendsto_natCast_atTop_atTop).mpr ht
  exact hf.tendsto_zero_of_antitone _ _ Nat.mono_cast.neg
    (tendsto_neg_atBot_iff.mpr tendsto_natCast_atTop_atTop)

/--
lemma `IsRatCondKernelCDFAux.bddBelow_range` / 引理 `IsRatCondKernelCDFAux.bddBelow_range`

English:
lemma IsRatCondKernelCDFAux.bddBelow_range
  given: (hf : IsRatCondKernelCDFAux f κ ν) (a : α)
  proof: by
  filter_upwards [hf.nonneg a] with c hc
  refine fun q => ⟨0, ?_⟩
  simp [mem_lowerBounds, hc]

中文:
引理 是RatCondKernelCDFAux.bddBelow_range
  条件: (hf : 是RatCondKernelCDFAux f κ ν) (a : α)
  证明: by
  filter_upwards [hf.nonneg a] with c hc
  refine fun q => ⟨0, ?_⟩
  simp [mem_lowerBounds, hc]

Depends on / 依赖: filter_upwards, hf.nonneg, mem_lowerBounds, nonneg
-/
lemma IsRatCondKernelCDFAux.bddBelow_range (hf : IsRatCondKernelCDFAux f κ ν) (a : α) :
    forallᵐ t ∂(ν a), forall q : Rat, BddBelow (range fun (r : Ioi q) => f (a, t) r) := by
  filter_upwards [hf.nonneg a] with c hc
  refine fun q => ⟨0, ?_⟩
  simp [mem_lowerBounds, hc]

/--
lemma `IsRatCondKernelCDFAux.integrable_iInf_rat_gt` / 引理 `IsRatCondKernelCDFAux.integrable_iInf_rat_gt`

English:
lemma IsRatCondKernelCDFAux.integrable_iInf_rat_gt
  statement: (hf : IsRatCondKernelCDFAux f κ ν)
  proof: by
  rw [← memLp_one_iff_integrable]
  refine ⟨(Measurable.iInf fun i => hf.measurable_right a _).aestronglyMeasurable, ?_⟩
  refine (?_ : _ <= (ν a univ : Real>=0∞)).trans_lt (measure_lt_top _ _)
  refine (eLpNorm_le_of_ae_bound (C := 1) ?_).trans (by simp)
  filter_upwards [hf.bddBelow_range a, hf

中文:
引理 是RatCondKernelCDFAux.integrable_iInf_rat_gt
  结论: (hf : 是RatCondKernelCDFAux f κ ν)
  证明: by
  rw [← memLp_one_iff_integrable]
  refine ⟨(Measurable.iInf fun i => hf.measurable_right a _).aestronglyMeasurable, ?_⟩
  refine (?_ : _ <= (ν a univ : Real>=0∞)).trans_lt (measure_lt_top _ _)
  refine (eLpNorm_le_of_ae_bound (C := 1) ?_).trans (by simp)
  filter_upwards [hf.bddBelow_range a, hf

Depends on / 依赖: Measurable, Measurable.iInf, Real.norm_eq_abs, abs_of_nonneg, aestronglyMeasurable, bddBelow_range, ciInf_le_of_le, eLpNorm_le_of_ae_bound, filter_upwards, h_le_one, h_nonneg, hbdd_below, hf.bddBelow_range, hf.le_one, hf.measurable_right, hf.nonneg, le_one, measurable_right, measure_lt_top, memLp_one_iff_integrable
-/
lemma IsRatCondKernelCDFAux.integrable_iInf_rat_gt (hf : IsRatCondKernelCDFAux f κ ν)
    [IsFiniteKernel ν] (a : α) (q : Rat) :
    Integrable (fun t => ⨅ r : Ioi q, f (a, t) r) (ν a) := by
  rw [← memLp_one_iff_integrable]
  refine ⟨(Measurable.iInf fun i => hf.measurable_right a _).aestronglyMeasurable, ?_⟩
  refine (?_ : _ <= (ν a univ : Real>=0∞)).trans_lt (measure_lt_top _ _)
  refine (eLpNorm_le_of_ae_bound (C := 1) ?_).trans (by simp)
  filter_upwards [hf.bddBelow_range a, hf.nonneg a, hf.le_one a]
    with t hbdd_below h_nonneg h_le_one
  rw [Real.norm_eq_abs]; rw [abs_of_nonneg]
  · refine ciInf_le_of_le ?_ ?_ ?_
    · exact hbdd_below _
    · exact ⟨q + 1, by simp⟩
    · exact h_le_one _
  · exact le_ciInf fun r => h_nonneg _

/--
lemma `_root_.MeasureTheory.Measure.iInf_rat_gt_prod_Iic` / 引理 `_root_.MeasureTheory.Measure.iInf_rat_gt_prod_Iic`

English:
lemma _root_.MeasureTheory.Measure.iInf_rat_gt_prod_Iic
  statement: {ρ : Measure (α × Real)} [IsFiniteMeasure ρ]
  proof: by
  rw [← Monotone.measure_iInter]
  · rw [← prod_iInter]
    congr with x : 1
    simp only [mem_iInter, mem_Iic, Subtype.forall]
    refine ⟨fun h => ?_, fun h a hta => h.trans ?_⟩
    · refine le_of_forall_lt_rat_imp_le fun q htq => h q ?_
      exact mod_cast htq
    · exact mod_cast hta.le
· e

中文:
引理 _root_.测度论.测度.iInf_rat_gt_prod_Iic
  结论: {ρ : 测度 (α × 实数)} [是有限测度 ρ]
  证明: by
  rw [← Monotone.measure_iInter]
  · rw [← prod_iInter]
    congr with x : 1
    simp only [mem_iInter, mem_Iic, Subtype.forall]
    refine ⟨fun h => ?_, fun h a hta => h.trans ?_⟩
    · refine le_of_forall_lt_rat_imp_le fun q htq => h q ?_
      exact mod_cast htq
    · exact mod_cast hta.le
· e

Depends on / 依赖: Monotone, Monotone.measure_iInter, Subtype, Subtype.forall, h.trans, hs.prod, hta.le, le_of_forall_lt_rat_imp_le, lt_add_one, measurableSet_Iic, measure_iInter, measure_ne_top, mem_Iic, mem_iInter, mod_cast, nullMeasurableSet, prod_iInter, prod_mono_right
-/
lemma _root_.MeasureTheory.Measure.iInf_rat_gt_prod_Iic {ρ : Measure (α × Real)} [IsFiniteMeasure ρ]
    {s : Set α} (hs : MeasurableSet s) (t : Rat) :
    ⨅ r : { r' : Rat // t < r' }, ρ (s ×ˢ Iic (r : Real)) = ρ (s ×ˢ Iic (t : Real)) := by
  rw [← Monotone.measure_iInter]
  · rw [← prod_iInter]
    congr with x : 1
    simp only [mem_iInter, mem_Iic, Subtype.forall]
    refine ⟨fun h => ?_, fun h a hta => h.trans ?_⟩
    · refine le_of_forall_lt_rat_imp_le fun q htq => h q ?_
      exact mod_cast htq
    · exact mod_cast hta.le
· exact fun r r' hrr' => prod_mono_right by gcongr
  · exact fun _ => (hs.prod measurableSet_Iic).nullMeasurableSet
  · exact ⟨⟨t + 1, lt_add_one _⟩, measure_ne_top ρ _⟩

/--
lemma `IsRatCondKernelCDFAux.setIntegral_iInf_rat_gt` / 引理 `IsRatCondKernelCDFAux.setIntegral_iInf_rat_gt`

English:
lemma IsRatCondKernelCDFAux.setIntegral_iInf_rat_gt
  statement: (hf : IsRatCondKernelCDFAux f κ ν)
  proof: by
  refine le_antisymm ?_ ?_
  · have h : forall r : Ioi q, ∫ t in A, ⨅ r' : Ioi q, f (a, t) r' ∂(ν a)
        <= (κ a).real (A ×ˢ Iic (r : Real)) := by
      intro r
      rw [← hf.setIntegral a hA]
      refine setIntegral_mono_ae ?_ ?_ ?_
      · exact (hf.integrable_iInf_rat_gt _ _).integrableO

中文:
引理 是RatCondKernelCDFAux.set整数egral_iInf_rat_gt
  结论: (hf : 是RatCondKernelCDFAux f κ ν)
  证明: by
  refine le_antisymm ?_ ?_
  · have h : forall r : Ioi q, ∫ t in A, ⨅ r' : Ioi q, f (a, t) r' ∂(ν a)
        <= (κ a).real (A ×ˢ Iic (r : Real)) := by
      intro r
      rw [← hf.setIntegral a hA]
      refine setIntegral_mono_ae ?_ ?_ ?_
      · exact (hf.integrable_iInf_rat_gt _ _).integrableO

Depends on / 依赖: bddBelow_range, ciInf_le, filter_upwards, hf.bddBelow_range, hf.integrable, hf.integrable_iInf_rat_gt, hf.setIntegral, integrable, integrableOn, integrable_iInf_rat_gt, le_antisymm, le_ciInf, setIntegral, setIntegral_mono_ae
-/
lemma IsRatCondKernelCDFAux.setIntegral_iInf_rat_gt (hf : IsRatCondKernelCDFAux f κ ν)
    [IsFiniteKernel κ] [IsFiniteKernel ν] (a : α) (q : Rat) {A : Set β} (hA : MeasurableSet A) :
    ∫ t in A, ⨅ r : Ioi q, f (a, t) r ∂(ν a) = (κ a).real (A ×ˢ Iic (q : Real)) := by
  refine le_antisymm ?_ ?_
  · have h : forall r : Ioi q, ∫ t in A, ⨅ r' : Ioi q, f (a, t) r' ∂(ν a)
        <= (κ a).real (A ×ˢ Iic (r : Real)) := by
      intro r
      rw [← hf.setIntegral a hA]
      refine setIntegral_mono_ae ?_ ?_ ?_
      · exact (hf.integrable_iInf_rat_gt _ _).integrableOn
      · exact (hf.integrable _ _).integrableOn
      · filter_upwards [hf.bddBelow_range a] with t ht using ciInf_le (ht _) r
    calc ∫ t in A, ⨅ r : Ioi q, f (a, t) r ∂(ν a)
      <= ⨅ r : Ioi q, (κ a).real (A ×ˢ Iic (r : Real)) := le_ciInf h
    _ = (κ a).real (A ×ˢ Iic (q : Real)) := by
        rw [measureReal_def]; rw [← Measure.iInf_rat_gt_prod_Iic hA q]
        exact (ENNReal.toReal_iInf (fun r => measure_ne_top _ _)).symm
  · rw [← hf.setIntegral a hA]
    refine setIntegral_mono_ae ?_ ?_ ?_
    · exact (hf.integrable _ _).integrableOn
    · exact (hf.integrable_iInf_rat_gt _ _).integrableOn
    · filter_upwards [hf.mono a] with c h_mono using le_ciInf (fun r => h_mono (le_of_lt r.prop))

/--
lemma `IsRatCondKernelCDFAux.iInf_rat_gt_eq` / 引理 `IsRatCondKernelCDFAux.iInf_rat_gt_eq`

English:
lemma IsRatCondKernelCDFAux.iInf_rat_gt_eq
  statement: (hf : IsRatCondKernelCDFAux f κ ν) [IsFiniteKernel κ]
  proof: by
  rw [ae_all_iff]
  refine fun q => ae_eq_of_forall_setIntegral_eq_of_sigmaFinite (μ := ν a) ?_ ?_ ?_
  · exact fun _ _ _ => (hf.integrable_iInf_rat_gt _ _).integrableOn
  · exact fun _ _ _ => (hf.integrable a _).integrableOn
  · intro s hs _
    rw [hf.setIntegral _ hs]; rw [hf.setIntegral_iInf_

中文:
引理 是RatCondKernelCDFAux.iInf_rat_gt_eq
  结论: (hf : 是RatCondKernelCDFAux f κ ν) [是FiniteKernel κ]
  证明: by
  rw [ae_all_iff]
  refine fun q => ae_eq_of_forall_setIntegral_eq_of_sigmaFinite (μ := ν a) ?_ ?_ ?_
  · exact fun _ _ _ => (hf.integrable_iInf_rat_gt _ _).integrableOn
  · exact fun _ _ _ => (hf.integrable a _).integrableOn
  · intro s hs _
    rw [hf.setIntegral _ hs]; rw [hf.setIntegral_iInf_

Depends on / 依赖: ae_all_iff, ae_eq_of_forall_setIntegral_eq_of_sigmaFinite, hf.integrable, hf.integrable_iInf_rat_gt, hf.setIntegral, hf.setIntegral_iInf_rat_gt, integrable, integrableOn, integrable_iInf_rat_gt, setIntegral, setIntegral_iInf_rat_gt
-/
lemma IsRatCondKernelCDFAux.iInf_rat_gt_eq (hf : IsRatCondKernelCDFAux f κ ν) [IsFiniteKernel κ]
    [IsFiniteKernel ν] (a : α) :
    forallᵐ t ∂(ν a), forall q : Rat, ⨅ r : Ioi q, f (a, t) r = f (a, t) q := by
  rw [ae_all_iff]
  refine fun q => ae_eq_of_forall_setIntegral_eq_of_sigmaFinite (μ := ν a) ?_ ?_ ?_
  · exact fun _ _ _ => (hf.integrable_iInf_rat_gt _ _).integrableOn
  · exact fun _ _ _ => (hf.integrable a _).integrableOn
  · intro s hs _
    rw [hf.setIntegral _ hs]; rw [hf.setIntegral_iInf_rat_gt _ _ hs]

/--
lemma `IsRatCondKernelCDFAux.isRatStieltjesPoint_ae` / 引理 `IsRatCondKernelCDFAux.isRatStieltjesPoint_ae`

English:
lemma IsRatCondKernelCDFAux.isRatStieltjesPoint_ae
  statement: (hf : IsRatCondKernelCDFAux f κ ν)
  proof: by
  filter_upwards [hf.tendsto_atTop_one a, hf.tendsto_atBot_zero a,
    hf.iInf_rat_gt_eq a, hf.mono a] with t ht_top ht_bot ht_iInf h_mono
  exact ⟨h_mono, ht_top, ht_bot, ht_iInf⟩

中文:
引理 是RatCondKernelCDFAux.isRatStieltjesPoint_ae
  结论: (hf : 是RatCondKernelCDFAux f κ ν)
  证明: by
  filter_upwards [hf.tendsto_atTop_one a, hf.tendsto_atBot_zero a,
    hf.iInf_rat_gt_eq a, hf.mono a] with t ht_top ht_bot ht_iInf h_mono
  exact ⟨h_mono, ht_top, ht_bot, ht_iInf⟩

Depends on / 依赖: filter_upwards, h_mono, hf.iInf_rat_gt_eq, hf.mono, hf.tendsto_atBot_zero, hf.tendsto_atTop_one, ht_bot, ht_iInf, ht_top, iInf_rat_gt_eq, tendsto_atBot_zero, tendsto_atTop_one
-/
lemma IsRatCondKernelCDFAux.isRatStieltjesPoint_ae (hf : IsRatCondKernelCDFAux f κ ν)
    [IsFiniteKernel κ] [IsFiniteKernel ν] (a : α) :
    forallᵐ t ∂(ν a), IsRatStieltjesPoint f (a, t) := by
  filter_upwards [hf.tendsto_atTop_one a, hf.tendsto_atBot_zero a,
    hf.iInf_rat_gt_eq a, hf.mono a] with t ht_top ht_bot ht_iInf h_mono
  exact ⟨h_mono, ht_top, ht_bot, ht_iInf⟩

/--
lemma `IsRatCondKernelCDFAux.isRatCondKernelCDF` / 引理 `IsRatCondKernelCDFAux.isRatCondKernelCDF`

English:
lemma IsRatCondKernelCDFAux.isRatCondKernelCDF
  statement: (hf : IsRatCondKernelCDFAux f κ ν) [IsFiniteKernel κ]
  proof: hf.measurable
  isRatStieltjesPoint_ae := hf.isRatStieltjesPoint_ae
  integrable := hf.integrable
  setIntegral := hf.setIntegral

中文:
引理 是RatCondKernelCDFAux.isRatCondKernelCDF
  结论: (hf : 是RatCondKernelCDFAux f κ ν) [是FiniteKernel κ]
  证明: hf.measurable
  isRatStieltjesPoint_ae := hf.isRatStieltjesPoint_ae
  integrable := hf.integrable
  setIntegral := hf.setIntegral

Depends on / 依赖: hf.measurable, measurable
-/
lemma IsRatCondKernelCDFAux.isRatCondKernelCDF (hf : IsRatCondKernelCDFAux f κ ν) [IsFiniteKernel κ]
    [IsFiniteKernel ν] :
    IsRatCondKernelCDF f κ ν where
  measurable := hf.measurable
  isRatStieltjesPoint_ae := hf.isRatStieltjesPoint_ae
  integrable := hf.integrable
  setIntegral := hf.setIntegral

end isRatCondKernelCDFAux

section IsCondKernelCDF

variable {f : α × β -> StieltjesFunction Real}

/--
Definition of `IsCondKernelCDF` / `IsCondKernelCDF` 的定义

English:
structure IsCondKernelCDF
  parameters: (f : α × β -> StieltjesFunction Real) (κ : Kernel α (β × Real))
  axioms and operations (5):
    - measurable((x : Real)) : Measurable fun p => f p x
    - integrable((a : α) (x : Real)) : Integrable (fun b => f (a, b) x) (ν a)
    - tendsto_atTop_one((p : α × β)) : Tendsto (f p) atTop (𝓝 1)
    - tendsto_atBot_zero((p : α × β)) : Tendsto (f p) atBot (𝓝 0)
    - setIntegral((a : α) {s : Set β} (_hs : MeasurableSet s) (x : Real)) : ∫ b in s, f (a, b) x ∂(ν a) = (κ a).real (s ×ˢ Iic x)

中文:
结构 是余ndKernelCDF
  参数: (f : α × β -> Stieltjes函数 实数) (κ : 核 α (β × 实数))
  公理与运算 (5 个):
    - measurable((x : 实数)) : 可测 fun p => f p x
    - integrable((a : α) (x : 实数)) : 可积 (fun b => f (a, b) x) (ν a)
    - tendsto_atTop_one((p : α × β)) : 收敛 (f p) atTop (𝓝 1)
    - tendsto_atBot_zero((p : α × β)) : 收敛 (f p) atBot (𝓝 0)
    - setIntegral((a : α) {s : 集合 β} (_hs : 可测集 s) (x : 实数)) : ∫ b in s, f (a, b) x ∂(ν a) = (κ a).real (s ×ˢ 左无界右闭区间 x)
-/
structure IsCondKernelCDF (f : α × β -> StieltjesFunction Real) (κ : Kernel α (β × Real))
    (ν : Kernel α β) : Prop where
  measurable (x : Real) : Measurable fun p => f p x
  integrable (a : α) (x : Real) : Integrable (fun b => f (a, b) x) (ν a)
  tendsto_atTop_one (p : α × β) : Tendsto (f p) atTop (𝓝 1)
  tendsto_atBot_zero (p : α × β) : Tendsto (f p) atBot (𝓝 0)
  setIntegral (a : α) {s : Set β} (_hs : MeasurableSet s) (x : Real) :
    ∫ b in s, f (a, b) x ∂(ν a) = (κ a).real (s ×ˢ Iic x)

/--
lemma `IsCondKernelCDF.nonneg` / 引理 `IsCondKernelCDF.nonneg`

English:
lemma IsCondKernelCDF.nonneg
  given: (hf : IsCondKernelCDF f κ ν) (p : α × β) (x : Real)
  statement: 0 <= f p x
  proof: Monotone.le_of_tendsto (f p).mono (hf.tendsto_atBot_zero p) x

中文:
引理 是余ndKernelCDF.nonneg
  条件: (hf : 是余ndKernelCDF f κ ν) (p : α × β) (x : 实数)
  结论: 0 <= f p x
  证明: Monotone.le_of_tendsto (f p).mono (hf.tendsto_atBot_zero p) x

Depends on / 依赖: Monotone, Monotone.le_of_tendsto, hf.tendsto_atBot_zero, le_of_tendsto, tendsto_atBot_zero
-/
lemma IsCondKernelCDF.nonneg (hf : IsCondKernelCDF f κ ν) (p : α × β) (x : Real) : 0 <= f p x :=
  Monotone.le_of_tendsto (f p).mono (hf.tendsto_atBot_zero p) x

/--
lemma `IsCondKernelCDF.le_one` / 引理 `IsCondKernelCDF.le_one`

English:
lemma IsCondKernelCDF.le_one
  given: (hf : IsCondKernelCDF f κ ν) (p : α × β) (x : Real)
  statement: f p x <= 1
  proof: Monotone.ge_of_tendsto (f p).mono (hf.tendsto_atTop_one p) x

中文:
引理 是余ndKernelCDF.le_one
  条件: (hf : 是余ndKernelCDF f κ ν) (p : α × β) (x : 实数)
  结论: f p x <= 1
  证明: Monotone.ge_of_tendsto (f p).mono (hf.tendsto_atTop_one p) x

Depends on / 依赖: Monotone, Monotone.ge_of_tendsto, ge_of_tendsto, hf.tendsto_atTop_one, tendsto_atTop_one
-/
lemma IsCondKernelCDF.le_one (hf : IsCondKernelCDF f κ ν) (p : α × β) (x : Real) : f p x <= 1 :=
  Monotone.ge_of_tendsto (f p).mono (hf.tendsto_atTop_one p) x

/--
lemma `IsCondKernelCDF.integral` / 引理 `IsCondKernelCDF.integral`

English:
lemma IsCondKernelCDF.integral
  proof: by
  rw [← hf.setIntegral _ MeasurableSet.univ]; rw [Measure.restrict_univ]

中文:
引理 是余ndKernelCDF.integral
  证明: by
  rw [← hf.setIntegral _ MeasurableSet.univ]; rw [Measure.restrict_univ]

Depends on / 依赖: MeasurableSet, MeasurableSet.univ, Measure, Measure.restrict_univ, hf.setIntegral, restrict_univ, setIntegral
-/
lemma IsCondKernelCDF.integral
    {f : α × β -> StieltjesFunction Real} (hf : IsCondKernelCDF f κ ν) (a : α) (x : Real) :
    ∫ b, f (a, b) x ∂(ν a) = (κ a).real (univ ×ˢ Iic x) := by
  rw [← hf.setIntegral _ MeasurableSet.univ]; rw [Measure.restrict_univ]

/--
lemma `IsCondKernelCDF.setLIntegral` / 引理 `IsCondKernelCDF.setLIntegral`

English:
lemma IsCondKernelCDF.setLIntegral
  statement: [IsFiniteKernel κ]
  proof: by
  rw [← ofReal_integral_eq_lintegral_ofReal (hf.integrable a x).restrict
    (ae_of_all _ (fun _ => hf.nonneg _ _))]; rw [hf.setIntegral a hs x]; rw [ofReal_measureReal]

中文:
引理 是余ndKernelCDF.setL整数egral
  结论: [是FiniteKernel κ]
  证明: by
  rw [← ofReal_integral_eq_lintegral_ofReal (hf.integrable a x).restrict
    (ae_of_all _ (fun _ => hf.nonneg _ _))]; rw [hf.setIntegral a hs x]; rw [ofReal_measureReal]

Depends on / 依赖: ae_of_all, hf.integrable, hf.nonneg, hf.setIntegral, integrable, nonneg, ofReal_integral_eq_lintegral_ofReal, ofReal_measureReal, restrict, setIntegral
-/
lemma IsCondKernelCDF.setLIntegral [IsFiniteKernel κ]
    {f : α × β -> StieltjesFunction Real} (hf : IsCondKernelCDF f κ ν)
    (a : α) {s : Set β} (hs : MeasurableSet s) (x : Real) :
    ∫⁻ b in s, ENNReal.ofReal (f (a, b) x) ∂(ν a) = κ a (s ×ˢ Iic x) := by
  rw [← ofReal_integral_eq_lintegral_ofReal (hf.integrable a x).restrict
    (ae_of_all _ (fun _ => hf.nonneg _ _))]; rw [hf.setIntegral a hs x]; rw [ofReal_measureReal]

/--
lemma `IsCondKernelCDF.lintegral` / 引理 `IsCondKernelCDF.lintegral`

English:
lemma IsCondKernelCDF.lintegral
  statement: [IsFiniteKernel κ]
  proof: by
  rw [← hf.setLIntegral _ MeasurableSet.univ]; rw [Measure.restrict_univ]

中文:
引理 是余ndKernelCDF.lintegral
  结论: [是FiniteKernel κ]
  证明: by
  rw [← hf.setLIntegral _ MeasurableSet.univ]; rw [Measure.restrict_univ]

Depends on / 依赖: MeasurableSet, MeasurableSet.univ, Measure, Measure.restrict_univ, hf.setLIntegral, restrict_univ, setLIntegral
-/
lemma IsCondKernelCDF.lintegral [IsFiniteKernel κ]
    {f : α × β -> StieltjesFunction Real} (hf : IsCondKernelCDF f κ ν) (a : α) (x : Real) :
    ∫⁻ b, ENNReal.ofReal (f (a, b) x) ∂(ν a) = κ a (univ ×ˢ Iic x) := by
  rw [← hf.setLIntegral _ MeasurableSet.univ]; rw [Measure.restrict_univ]

/--
lemma `isCondKernelCDF_stieltjesOfMeasurableRat` / 引理 `isCondKernelCDF_stieltjesOfMeasurableRat`

English:
lemma isCondKernelCDF_stieltjesOfMeasurableRat
  statement: {f : α × β -> Rat -> Real} (hf : IsRatCondKernelCDF f κ ν)
  proof: measurable_stieltjesOfMeasurableRat hf.measurable
  integrable := integrable_stieltjesOfMeasurableRat hf
  tendsto_atTop_one := tendsto_stieltjesOfMeasurableRat_atTop hf.measurable
  tendsto_atBot_zero := tendsto_stieltjesOfMeasurableRat_atBot hf.measurable
  setIntegral a _ hs x := setIntegral_stie

中文:
引理 isCondKernelCDF_stieltjesOfMeasurableRat
  结论: {f : α × β -> 有理数 -> 实数} (hf : 是RatCondKernelCDF f κ ν)
  证明: measurable_stieltjesOfMeasurableRat hf.measurable
  integrable := integrable_stieltjesOfMeasurableRat hf
  tendsto_atTop_one := tendsto_stieltjesOfMeasurableRat_atTop hf.measurable
  tendsto_atBot_zero := tendsto_stieltjesOfMeasurableRat_atBot hf.measurable
  setIntegral a _ hs x := setIntegral_stie

Depends on / 依赖: hf.measurable, measurable, measurable_stieltjesOfMeasurableRat
-/
lemma isCondKernelCDF_stieltjesOfMeasurableRat {f : α × β -> Rat -> Real} (hf : IsRatCondKernelCDF f κ ν)
    [IsFiniteKernel κ] :
    IsCondKernelCDF (stieltjesOfMeasurableRat f hf.measurable) κ ν where
  measurable := measurable_stieltjesOfMeasurableRat hf.measurable
  integrable := integrable_stieltjesOfMeasurableRat hf
  tendsto_atTop_one := tendsto_stieltjesOfMeasurableRat_atTop hf.measurable
  tendsto_atBot_zero := tendsto_stieltjesOfMeasurableRat_atBot hf.measurable
  setIntegral a _ hs x := setIntegral_stieltjesOfMeasurableRat hf a x hs

end IsCondKernelCDF

section ToKernel

variable {_ : MeasurableSpace β} {f : α × β -> StieltjesFunction Real}
  {κ : Kernel α (β × Real)} {ν : Kernel α β}

/-- A function `f : α × β → StieltjesFunction ℝ` with the property `IsCondKernelCDF f κ ν` gives a
Markov kernel from `α × β` to `ℝ`, by taking for each `p : α × β` the measure defined by `f p`. -/
noncomputable
/--
Definition of `IsCondKernelCDF.toKernel` / `IsCondKernelCDF.toKernel` 的定义

English:
definition IsCondKernelCDF.toKernel
  signature: (f : α × β -> StieltjesFunction Real) (hf : IsCondKernelCDF f κ ν)
  body: (f p).measure
  measurable' := StieltjesFunction.measurable_measure hf.measurable
    hf.tendsto_atBot_zero hf.tendsto_atTop_one

中文:
定义 是余ndKernelCDF.toKernel
  签名: (f : α × β -> Stieltjes函数 实数) (hf : 是余ndKernelCDF f κ ν)
  定义体: (f p).measure
  measurable' := StieltjesFunction.measurable_measure hf.measurable
    hf.tendsto_atBot_zero hf.tendsto_atTop_one

Depends on / 依赖: measure
-/
def IsCondKernelCDF.toKernel (f : α × β -> StieltjesFunction Real) (hf : IsCondKernelCDF f κ ν) :
    Kernel (α × β) Real where
  toFun p := (f p).measure
  measurable' := StieltjesFunction.measurable_measure hf.measurable
    hf.tendsto_atBot_zero hf.tendsto_atTop_one

/--
lemma `IsCondKernelCDF.toKernel_apply` / 引理 `IsCondKernelCDF.toKernel_apply`

English:
lemma IsCondKernelCDF.toKernel_apply
  given: {hf : IsCondKernelCDF f κ ν} (p : α × β)
  proof: rfl

中文:
引理 是余ndKernelCDF.toKernel_apply
  条件: {hf : 是余ndKernelCDF f κ ν} (p : α × β)
  证明: rfl
-/
lemma IsCondKernelCDF.toKernel_apply {hf : IsCondKernelCDF f κ ν} (p : α × β) :
    hf.toKernel f p = (f p).measure := rfl

/--
Instance `instIsMarkovKernel_toKernel` / 实例 `instIsMarkovKernel_toKernel`

English:
instance instIsMarkovKernel_toKernel
  signature: {hf : IsCondKernelCDF f κ ν}
  body: ⟨fun _ => (f _).isProbabilityMeasure (hf.tendsto_atBot_zero _) (hf.tendsto_atTop_one _)⟩

中文:
实例 instIsMarkovKernel_toKernel
  签名: {hf : 是余ndKernelCDF f κ ν}
  定义体: ⟨fun _ => (f _).isProbabilityMeasure (hf.tendsto_atBot_zero _) (hf.tendsto_atTop_one _)⟩

Depends on / 依赖: hf.tendsto_atBot_zero, hf.tendsto_atTop_one, isProbabilityMeasure, tendsto_atBot_zero, tendsto_atTop_one
-/
instance instIsMarkovKernel_toKernel {hf : IsCondKernelCDF f κ ν} :
    IsMarkovKernel (hf.toKernel f) :=
  ⟨fun _ => (f _).isProbabilityMeasure (hf.tendsto_atBot_zero _) (hf.tendsto_atTop_one _)⟩

/--
lemma `IsCondKernelCDF.toKernel_Iic` / 引理 `IsCondKernelCDF.toKernel_Iic`

English:
lemma IsCondKernelCDF.toKernel_Iic
  given: {hf : IsCondKernelCDF f κ ν} (p : α × β) (x : Real)
  proof: by
  rw [IsCondKernelCDF.toKernel_apply p]; rw [(f p).measure_Iic (hf.tendsto_atBot_zero p)]
  simp

中文:
引理 是余ndKernelCDF.toKernel_Iic
  条件: {hf : 是余ndKernelCDF f κ ν} (p : α × β) (x : 实数)
  证明: by
  rw [IsCondKernelCDF.toKernel_apply p]; rw [(f p).measure_Iic (hf.tendsto_atBot_zero p)]
  simp

Depends on / 依赖: IsCondKernelCDF, IsCondKernelCDF.toKernel_apply, hf.tendsto_atBot_zero, measure_Iic, tendsto_atBot_zero, toKernel_apply
-/
lemma IsCondKernelCDF.toKernel_Iic {hf : IsCondKernelCDF f κ ν} (p : α × β) (x : Real) :
    hf.toKernel f p (Iic x) = ENNReal.ofReal (f p x) := by
  rw [IsCondKernelCDF.toKernel_apply p]; rw [(f p).measure_Iic (hf.tendsto_atBot_zero p)]
  simp

end ToKernel

section

variable {f : α × β -> StieltjesFunction Real}

/--
lemma `setLIntegral_toKernel_Iic` / 引理 `setLIntegral_toKernel_Iic`

English:
lemma setLIntegral_toKernel_Iic
  statement: [IsFiniteKernel κ] (hf : IsCondKernelCDF f κ ν)
  proof: by
  simp_rw [IsCondKernelCDF.toKernel_Iic]
  exact hf.setLIntegral _ hs _

中文:
引理 setL整数egral_toKernel_Iic
  结论: [是FiniteKernel κ] (hf : 是余ndKernelCDF f κ ν)
  证明: by
  simp_rw [IsCondKernelCDF.toKernel_Iic]
  exact hf.setLIntegral _ hs _

Depends on / 依赖: IsCondKernelCDF, IsCondKernelCDF.toKernel_Iic, hf.setLIntegral, setLIntegral, simp_rw, toKernel_Iic
-/
lemma setLIntegral_toKernel_Iic [IsFiniteKernel κ] (hf : IsCondKernelCDF f κ ν)
    (a : α) (x : Real) {s : Set β} (hs : MeasurableSet s) :
    ∫⁻ b in s, hf.toKernel f (a, b) (Iic x) ∂(ν a) = κ a (s ×ˢ Iic x) := by
  simp_rw [IsCondKernelCDF.toKernel_Iic]
  exact hf.setLIntegral _ hs _

/--
lemma `setLIntegral_toKernel_univ` / 引理 `setLIntegral_toKernel_univ`

English:
lemma setLIntegral_toKernel_univ
  statement: [IsFiniteKernel κ] (hf : IsCondKernelCDF f κ ν)
  proof: by
  rw [← Real.iUnion_Iic_rat]; rw [prod_iUnion]
  have h_dir : Directed (fun x y => x subseteq y) fun q : Rat => Iic (q : Real) := by
    refine Monotone.directed_le fun r r' hrr' => Iic_subset_Iic.mpr ?_
    exact mod_cast hrr'
  have h_dir_prod : Directed (fun x y => x subseteq y) fun q : Rat =>

中文:
引理 setL整数egral_toKernel_univ
  结论: [是FiniteKernel κ] (hf : 是余ndKernelCDF f κ ν)
  证明: by
  rw [← Real.iUnion_Iic_rat]; rw [prod_iUnion]
  have h_dir : Directed (fun x y => x subseteq y) fun q : Rat => Iic (q : Real) := by
    refine Monotone.directed_le fun r r' hrr' => Iic_subset_Iic.mpr ?_
    exact mod_cast hrr'
  have h_dir_prod : Directed (fun x y => x subseteq y) fun q : Rat =>

Depends on / 依赖: Directed, Iic_subset_Iic, Iic_subset_Iic.mpr, Monotone, Monotone.directed_le, Or.inl, Real.iUnion_Iic_rat, directed_le, h_dir, h_dir.measure_iUnion, h_dir_prod, h_dir_prod.mea, iUnion_Iic_rat, measure_iUnion, mod_cast, prod_iUnion, prod_subset_prod_iff, prod_subset_prod_iff.mpr, simp_rw, subset_rfl
-/
lemma setLIntegral_toKernel_univ [IsFiniteKernel κ] (hf : IsCondKernelCDF f κ ν)
    (a : α) {s : Set β} (hs : MeasurableSet s) :
    ∫⁻ b in s, hf.toKernel f (a, b) univ ∂(ν a) = κ a (s ×ˢ univ) := by
  rw [← Real.iUnion_Iic_rat]; rw [prod_iUnion]
  have h_dir : Directed (fun x y => x subseteq y) fun q : Rat => Iic (q : Real) := by
    refine Monotone.directed_le fun r r' hrr' => Iic_subset_Iic.mpr ?_
    exact mod_cast hrr'
  have h_dir_prod : Directed (fun x y => x subseteq y) fun q : Rat => s ×ˢ Iic (q : Real) := by
    refine Monotone.directed_le fun i j hij => ?_
    refine prod_subset_prod_iff.mpr (Or.inl ⟨subset_rfl, Iic_subset_Iic.mpr ?_⟩)
    exact mod_cast hij
  simp_rw [h_dir.measure_iUnion, h_dir_prod.measure_iUnion]
  rw [lintegral_iSup_directed]
  · simp_rw [setLIntegral_toKernel_Iic hf _ _ hs]
  · refine fun q => Measurable.aemeasurable ?_
    exact (Kernel.measurable_coe _ measurableSet_Iic).comp measurable_prodMk_left
  · refine Monotone.directed_le fun i j hij t => measure_mono (Iic_subset_Iic.mpr ?_)
    exact mod_cast hij

/--
lemma `lintegral_toKernel_univ` / 引理 `lintegral_toKernel_univ`

English:
lemma lintegral_toKernel_univ
  given: [IsFiniteKernel κ] (hf : IsCondKernelCDF f κ ν) (a : α)
  proof: by
  rw [← setLIntegral_univ]; rw [setLIntegral_toKernel_univ hf a MeasurableSet.univ]; rw [univ_prod_univ]

中文:
引理 lintegral_toKernel_univ
  条件: [是FiniteKernel κ] (hf : 是余ndKernelCDF f κ ν) (a : α)
  证明: by
  rw [← setLIntegral_univ]; rw [setLIntegral_toKernel_univ hf a MeasurableSet.univ]; rw [univ_prod_univ]

Depends on / 依赖: MeasurableSet, MeasurableSet.univ, setLIntegral_toKernel_univ, setLIntegral_univ, univ_prod_univ
-/
lemma lintegral_toKernel_univ [IsFiniteKernel κ] (hf : IsCondKernelCDF f κ ν) (a : α) :
    ∫⁻ b, hf.toKernel f (a, b) univ ∂(ν a) = κ a univ := by
  rw [← setLIntegral_univ]; rw [setLIntegral_toKernel_univ hf a MeasurableSet.univ]; rw [univ_prod_univ]

/--
lemma `setLIntegral_toKernel_prod` / 引理 `setLIntegral_toKernel_prod`

English:
lemma setLIntegral_toKernel_prod
  statement: [IsFiniteKernel κ] (hf : IsCondKernelCDF f κ ν)
  proof: by
  -- `setLIntegral_toKernel_Iic` gives the result for `t = Iic x`. These sets form a
  -- π-system that generates the Borel σ-algebra, hence we can get the same equality for any
  -- measurable set `t`.
  induction t, ht
    using MeasurableSpace.induction_on_inter (borel_eq_generateFrom_Iic Real

中文:
引理 setL整数egral_toKernel_prod
  结论: [是FiniteKernel κ] (hf : 是余ndKernelCDF f κ ν)
  证明: by
  -- `setLIntegral_toKernel_Iic` gives the result for `t = Iic x`. These sets form a
  -- π-system that generates the Borel σ-algebra, hence we can get the same equality for any
  -- measurable set `t`.
  induction t, ht
    using MeasurableSpace.induction_on_inter (borel_eq_generateFrom_Iic Real
-/
lemma setLIntegral_toKernel_prod [IsFiniteKernel κ] (hf : IsCondKernelCDF f κ ν)
    (a : α) {s : Set β} (hs : MeasurableSet s) {t : Set Real} (ht : MeasurableSet t) :
    ∫⁻ b in s, hf.toKernel f (a, b) t ∂(ν a) = κ a (s ×ˢ t) := by
  -- `setLIntegral_toKernel_Iic` gives the result for `t = Iic x`. These sets form a
  -- π-system that generates the Borel σ-algebra, hence we can get the same equality for any
  -- measurable set `t`.
  induction t, ht
    using MeasurableSpace.induction_on_inter (borel_eq_generateFrom_Iic Real) isPiSystem_Iic with
  | empty => simp only [measure_empty, lintegral_const, zero_mul, prod_empty]
  | basic t ht =>
    obtain ⟨q, rfl⟩ := ht
    exact setLIntegral_toKernel_Iic hf a _ hs
  | compl t ht iht =>
    calc ∫⁻ b in s, hf.toKernel f (a, b) tᶜ ∂(ν a)
      = ∫⁻ b in s, hf.toKernel f (a, b) univ - hf.toKernel f (a, b) t ∂(ν a) := by
          congr with x; rw [measure_compl ht (measure_ne_top (hf.toKernel f (a, x)) _)]
    _ = ∫⁻ b in s, hf.toKernel f (a, b) univ ∂(ν a)
          - ∫⁻ b in s, hf.toKernel f (a, b) t ∂(ν a) := by
        rw [lintegral_sub]
        · exact (Kernel.measurable_coe (hf.toKernel f) ht).comp measurable_prodMk_left
        · rw [iht]
          exact measure_ne_top _ _
        · exact Eventually.of_forall fun a => measure_mono (subset_univ _)
    _ = κ a (s ×ˢ univ) - κ a (s ×ˢ t) := by
        rw [setLIntegral_toKernel_univ hf a hs]; rw [iht]
    _ = κ a (s ×ˢ tᶜ) := by
        rw [← measure_sdiff _ (hs.prod ht).nullMeasurableSet (measure_ne_top _ _)]
        · rw [prod_sdiff_prod, compl_eq_univ_sdiff]
          simp only [sdiff_self, empty_prod, union_empty]
        · rw [prod_subset_prod_iff]
          exact Or.inl ⟨subset_rfl, subset_univ t⟩
  | iUnion f hf_disj hf_meas ihf =>
    simp_rw [measure_iUnion hf_disj hf_meas]
    rw [lintegral_tsum]; rw [prod_iUnion]; rw [measure_iUnion]
    · simp_rw [ihf]
    · exact hf_disj.mono fun i j h => h.set_prod_right _ _
    · exact fun i => MeasurableSet.prod hs (hf_meas i)
    · exact fun i =>
        ((Kernel.measurable_coe _ (hf_meas i)).comp measurable_prodMk_left).aemeasurable.restrict

open scoped Function in -- required for scoped `on` notation
/--
lemma `lintegral_toKernel_mem` / 引理 `lintegral_toKernel_mem`

English:
lemma lintegral_toKernel_mem
  statement: [IsFiniteKernel κ] (hf : IsCondKernelCDF f κ ν)
  proof: by
  -- `setLIntegral_toKernel_prod` gives the result for sets of the form `t₁ × t₂`. These
  -- sets form a π-system that generates the product σ-algebra, hence we can get the same equality
  -- for any measurable set `s`.
  induction s, hs
    using MeasurableSpace.induction_on_inter generateFrom_

中文:
引理 lintegral_toKernel_mem
  结论: [是FiniteKernel κ] (hf : 是余ndKernelCDF f κ ν)
  证明: by
  -- `setLIntegral_toKernel_prod` gives the result for sets of the form `t₁ × t₂`. These
  -- sets form a π-system that generates the product σ-algebra, hence we can get the same equality
  -- for any measurable set `s`.
  induction s, hs
    using MeasurableSpace.induction_on_inter generateFrom_
-/
lemma lintegral_toKernel_mem [IsFiniteKernel κ] (hf : IsCondKernelCDF f κ ν)
    (a : α) {s : Set (β × Real)} (hs : MeasurableSet s) :
    ∫⁻ b, hf.toKernel f (a, b) (Prod.mk b ⁻¹' s) ∂(ν a) = κ a s := by
  -- `setLIntegral_toKernel_prod` gives the result for sets of the form `t₁ × t₂`. These
  -- sets form a π-system that generates the product σ-algebra, hence we can get the same equality
  -- for any measurable set `s`.
  induction s, hs
    using MeasurableSpace.induction_on_inter generateFrom_prod.symm isPiSystem_prod with
  | empty =>
    simp only [preimage_empty, measure_empty, lintegral_const, zero_mul]
  | basic s hs =>
    rcases hs with ⟨t₁, ht₁, t₂, ht₂, rfl⟩
    simp only [mem_ofPred_eq] at ht₁ ht₂
    rw [← lintegral_add_compl _ ht₁]
    have h_eq1 : ∫⁻ x in t₁, hf.toKernel f (a, x) (Prod.mk x ⁻¹' t₁ ×ˢ t₂) ∂(ν a)
        = ∫⁻ x in t₁, hf.toKernel f (a, x) t₂ ∂(ν a) := by
      refine setLIntegral_congr_fun ht₁ (fun a ha => ?_)
      rw [mk_preimage_prod_right ha]
    have h_eq2 :
        ∫⁻ x in t₁ᶜ, hf.toKernel f (a, x) (Prod.mk x ⁻¹' t₁ ×ˢ t₂) ∂(ν a) = 0 := by
      suffices h_eq_zero :
          forall x in t₁ᶜ, hf.toKernel f (a, x) (Prod.mk x ⁻¹' t₁ ×ˢ t₂) = 0 by
        rw [setLIntegral_congr_fun ht₁.compl h_eq_zero]
        simp only [lintegral_const, zero_mul]
      intro a hat₁
      rw [mem_compl_iff] at hat₁
      simp only [hat₁, not_false_eq_true, mk_preimage_prod_right_eq_empty, measure_empty]
    rw [h_eq1]; rw [h_eq2]; rw [add_zero]
    exact setLIntegral_toKernel_prod hf a ht₁ ht₂
  | compl t ht ht_eq =>
    calc ∫⁻ b, hf.toKernel f (a, b) (Prod.mk b ⁻¹' tᶜ) ∂(ν a)
      = ∫⁻ b, hf.toKernel f (a, b) (Prod.mk b ⁻¹' t)ᶜ ∂(ν a) := rfl
    _ = ∫⁻ b, hf.toKernel f (a, b) univ
          - hf.toKernel f (a, b) (Prod.mk b ⁻¹' t) ∂(ν a) := by
        congr with x : 1
        exact measure_compl (measurable_prodMk_left ht)
          (measure_ne_top (hf.toKernel f (a, x)) _)
    _ = ∫⁻ x, hf.toKernel f (a, x) univ ∂(ν a) -
          ∫⁻ x, hf.toKernel f (a, x) (Prod.mk x ⁻¹' t) ∂(ν a) := by
        have h_le : (fun x => hf.toKernel f (a, x) (Prod.mk x ⁻¹' t))
              <=ᵐ[ν a] fun x => hf.toKernel f (a, x) univ :=
          Eventually.of_forall fun _ => measure_mono (subset_univ _)
        rw [lintegral_sub _ _ h_le]
        · exact Kernel.measurable_kernel_prodMk_left' ht a
        refine ((lintegral_mono_ae h_le).trans_lt ?_).ne
        rw [lintegral_toKernel_univ hf]
        exact measure_lt_top _ univ
    _ = κ a univ - κ a t := by rw [ht_eq, lintegral_toKernel_univ hf]
    _ = κ a tᶜ := (measure_compl ht (measure_ne_top _ _)).symm
  | iUnion f' hf_disj hf_meas hf_eq =>
    have h_eq : forall a, Prod.mk a ⁻¹' ⋃ i, f' i = ⋃ i, Prod.mk a ⁻¹' f' i := by
      simp only [preimage_iUnion, implies_true]
    simp_rw [h_eq]
    have h_disj : forall a, Pairwise (Disjoint on fun i => Prod.mk a ⁻¹' f' i) := by
      intro _ _ _ hij
      exact Disjoint.preimage _ (hf_disj hij)
    calc ∫⁻ b, hf.toKernel f (a, b) (⋃ i, Prod.mk b ⁻¹' f' i) ∂(ν a)
      = ∫⁻ b, ∑' i, hf.toKernel f (a, b) (Prod.mk b ⁻¹' f' i) ∂(ν a) := by
          congr with x : 1
          rw [measure_iUnion (h_disj x) fun i => measurable_prodMk_left (hf_meas i)]
    _ = ∑' i, ∫⁻ b, hf.toKernel f (a, b) (Prod.mk b ⁻¹' f' i) ∂(ν a) :=
          lintegral_tsum fun i => (Kernel.measurable_kernel_prodMk_left' (hf_meas i) a).aemeasurable
    _ = ∑' i, κ a (f' i) := by simp_rw [hf_eq]
    _ = κ a (iUnion f') := (measure_iUnion hf_disj hf_meas).symm

/--
lemma `compProd_toKernel` / 引理 `compProd_toKernel`

English:
lemma compProd_toKernel
  given: [IsFiniteKernel κ] [IsSFiniteKernel ν] (hf : IsCondKernelCDF f κ ν)
  proof: by
  ext a s hs
  rw [Kernel.compProd_apply hs]; rw [lintegral_toKernel_mem hf a hs]

中文:
引理 compProd_toKernel
  条件: [是FiniteKernel κ] [是SFiniteKernel ν] (hf : 是余ndKernelCDF f κ ν)
  证明: by
  ext a s hs
  rw [Kernel.compProd_apply hs]; rw [lintegral_toKernel_mem hf a hs]

Depends on / 依赖: Kernel, Kernel.compProd_apply, compProd_apply, lintegral_toKernel_mem
-/
lemma compProd_toKernel [IsFiniteKernel κ] [IsSFiniteKernel ν] (hf : IsCondKernelCDF f κ ν) :
    ν otimesₖ hf.toKernel f = κ := by
  ext a s hs
  rw [Kernel.compProd_apply hs]; rw [lintegral_toKernel_mem hf a hs]

end

end ProbabilityTheory
