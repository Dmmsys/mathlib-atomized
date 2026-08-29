/-
Copyright (c) 2023 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Topology.ContinuousMap.Bounded.Normed
public import Mathlib.Topology.Algebra.Order.LiminfLimsup

/-!
# Integration of bounded continuous functions

In this file, some results are collected about integrals of bounded continuous functions. They are
mostly specializations of results in general integration theory, but they are used directly in this
specialized form in some other files, in particular in those related to the topology of weak
convergence of probability measures and finite measures.
-/

public section

open MeasureTheory Filter
open scoped ENNReal NNReal BoundedContinuousFunction Topology

namespace BoundedContinuousFunction

section NNRealValued

variable {X : Type*} [TopologicalSpace X]

/--
lemma `apply_le_nndist_zero` / 引理 `apply_le_nndist_zero`

English:
lemma apply_le_nndist_zero
  given: (f : X ->ᵇ Real>=0) (x : X)
  proof: by
  convert! nndist_coe_le_nndist x
  simp only [coe_zero, Pi.zero_apply, NNReal.nndist_zero_eq_val]

中文:
引理 apply_le_nndist_zero
  条件: (f : X ->ᵇ 实数>=0) (x : X)
  证明: by
  convert! nndist_coe_le_nndist x
  simp only [coe_zero, Pi.zero_apply, NNReal.nndist_zero_eq_val]

Depends on / 依赖: NNReal, NNReal.nndist_zero_eq_val, Pi.zero_apply, coe_zero, convert, nndist_coe_le_nndist, nndist_zero_eq_val, zero_apply
-/
lemma apply_le_nndist_zero (f : X ->ᵇ Real>=0) (x : X) :
    f x <= nndist 0 f := by
  convert! nndist_coe_le_nndist x
  simp only [coe_zero, Pi.zero_apply, NNReal.nndist_zero_eq_val]

/--
lemma `apply_le_edist_zero` / 引理 `apply_le_edist_zero`

English:
lemma apply_le_edist_zero
  given: (f : X ->ᵇ Real>=0) (x : X)
  proof: by
  simpa [← ENNReal.coe_le_coe] using f.apply_le_nndist_zero x

中文:
引理 apply_le_edist_zero
  条件: (f : X ->ᵇ 实数>=0) (x : X)
  证明: by
  simpa [← ENNReal.coe_le_coe] using f.apply_le_nndist_zero x

Depends on / 依赖: ENNReal, ENNReal.coe_le_coe, apply_le_nndist_zero, coe_le_coe, f.apply_le_nndist_zero
-/
lemma apply_le_edist_zero (f : X ->ᵇ Real>=0) (x : X) :
    f x <= edist 0 f := by
  simpa [← ENNReal.coe_le_coe] using f.apply_le_nndist_zero x

variable [MeasurableSpace X]

/--
lemma `lintegral_le_edist_mul` / 引理 `lintegral_le_edist_mul`

English:
lemma lintegral_le_edist_mul
  given: (f : X ->ᵇ Real>=0) (μ : Measure X)
  proof: le_trans (lintegral_mono (fun x => ENNReal.coe_le_coe.mpr (f.apply_le_nndist_zero x))) (by simp)

中文:
引理 lintegral_le_edist_mul
  条件: (f : X ->ᵇ 实数>=0) (μ : 测度 X)
  证明: le_trans (lintegral_mono (fun x => ENNReal.coe_le_coe.mpr (f.apply_le_nndist_zero x))) (by simp)

Depends on / 依赖: ENNReal, ENNReal.coe_le_coe.mpr, apply_le_nndist_zero, coe_le_coe, f.apply_le_nndist_zero, le_trans, lintegral_mono
-/
lemma lintegral_le_edist_mul (f : X ->ᵇ Real>=0) (μ : Measure X) :
    (∫⁻ x, f x ∂μ) <= edist 0 f * (μ Set.univ) :=
  le_trans (lintegral_mono (fun x => ENNReal.coe_le_coe.mpr (f.apply_le_nndist_zero x))) (by simp)

/--
theorem `measurable_coe_ennreal_comp` / 定理 `measurable_coe_ennreal_comp`

English:
theorem measurable_coe_ennreal_comp
  given: [OpensMeasurableSpace X] (f : X ->ᵇ Real>=0)
  proof: measurable_coe_nnreal_ennreal.comp f.continuous.measurable

中文:
定理 measurable_coe_ennreal_comp
  条件: [OpensMeasurable空间 X] (f : X ->ᵇ 实数>=0)
  证明: measurable_coe_nnreal_ennreal.comp f.continuous.measurable

Depends on / 依赖: continuous, f.continuous.measurable, measurable, measurable_coe_nnreal_ennreal, measurable_coe_nnreal_ennreal.comp
-/
theorem measurable_coe_ennreal_comp [OpensMeasurableSpace X] (f : X ->ᵇ Real>=0) :
    Measurable fun x => (f x : Real>=0∞) :=
  measurable_coe_nnreal_ennreal.comp f.continuous.measurable

variable (μ : Measure X) [IsFiniteMeasure μ]

/--
theorem `lintegral_lt_top_of_nnreal` / 定理 `lintegral_lt_top_of_nnreal`

English:
theorem lintegral_lt_top_of_nnreal
  given: (f : X ->ᵇ Real>=0)
  statement: ∫⁻ x, f x ∂μ < ∞
  proof: by
  apply IsFiniteMeasure.lintegral_lt_top_of_bounded_to_ennreal
  refine ⟨nndist f 0, fun x => ?_⟩
  have key := BoundedContinuousFunction.NNReal.upper_bound f x
  rwa [ENNReal.coe_le_coe]

中文:
定理 lintegral_lt_top_of_nnreal
  条件: (f : X ->ᵇ 实数>=0)
  结论: ∫⁻ x, f x ∂μ < ∞
  证明: by
  apply IsFiniteMeasure.lintegral_lt_top_of_bounded_to_ennreal
  refine ⟨nndist f 0, fun x => ?_⟩
  have key := BoundedContinuousFunction.NNReal.upper_bound f x
  rwa [ENNReal.coe_le_coe]

Depends on / 依赖: BoundedContinuousFunction, BoundedContinuousFunction.NNReal.upper_bound, ENNReal, ENNReal.coe_le_coe, IsFiniteMeasure, IsFiniteMeasure.lintegral_lt_top_of_bounded_to_ennreal, NNReal, coe_le_coe, lintegral_lt_top_of_bounded_to_ennreal, nndist, upper_bound
-/
theorem lintegral_lt_top_of_nnreal (f : X ->ᵇ Real>=0) : ∫⁻ x, f x ∂μ < ∞ := by
  apply IsFiniteMeasure.lintegral_lt_top_of_bounded_to_ennreal
  refine ⟨nndist f 0, fun x => ?_⟩
  have key := BoundedContinuousFunction.NNReal.upper_bound f x
  rwa [ENNReal.coe_le_coe]

/--
theorem `integrable_of_nnreal` / 定理 `integrable_of_nnreal`

English:
theorem integrable_of_nnreal
  given: [OpensMeasurableSpace X] (f : X ->ᵇ Real>=0)
  proof: by
  refine ⟨(NNReal.continuous_coe.comp f.continuous).measurable.aestronglyMeasurable, ?_⟩
  simp only [hasFiniteIntegral_iff_enorm, Function.comp_apply, NNReal.enorm_eq]
  exact lintegral_lt_top_of_nnreal _ f

中文:
定理 integrable_of_nnreal
  条件: [OpensMeasurable空间 X] (f : X ->ᵇ 实数>=0)
  证明: by
  refine ⟨(NNReal.continuous_coe.comp f.continuous).measurable.aestronglyMeasurable, ?_⟩
  simp only [hasFiniteIntegral_iff_enorm, Function.comp_apply, NNReal.enorm_eq]
  exact lintegral_lt_top_of_nnreal _ f

Depends on / 依赖: Function, Function.comp_apply, NNReal, NNReal.continuous_coe.comp, NNReal.enorm_eq, aestronglyMeasurable, comp_apply, continuous, continuous_coe, enorm_eq, f.continuous, hasFiniteIntegral_iff_enorm, lintegral_lt_top_of_nnreal, measurable, measurable.aestronglyMeasurable
-/
theorem integrable_of_nnreal [OpensMeasurableSpace X] (f : X ->ᵇ Real>=0) :
    Integrable (((↑) : Real>=0 -> Real) ∘ ⇑f) μ := by
  refine ⟨(NNReal.continuous_coe.comp f.continuous).measurable.aestronglyMeasurable, ?_⟩
  simp only [hasFiniteIntegral_iff_enorm, Function.comp_apply, NNReal.enorm_eq]
  exact lintegral_lt_top_of_nnreal _ f

/--
theorem `integral_eq_integral_nnrealPart_sub` / 定理 `integral_eq_integral_nnrealPart_sub`

English:
theorem integral_eq_integral_nnrealPart_sub
  given: [OpensMeasurableSpace X] (f : X ->ᵇ Real)
  proof: by
  simp only [f.self_eq_nnrealPart_sub_nnrealPart_neg, Pi.sub_apply, integral_sub,
             integrable_of_nnreal]
  simp only [Function.comp_apply]

中文:
定理 integral_eq_integral_nnrealPart_sub
  条件: [OpensMeasurable空间 X] (f : X ->ᵇ 实数)
  证明: by
  simp only [f.self_eq_nnrealPart_sub_nnrealPart_neg, Pi.sub_apply, integral_sub,
             integrable_of_nnreal]
  simp only [Function.comp_apply]

Depends on / 依赖: Function, Function.comp_apply, Pi.sub_apply, comp_apply, f.self_eq_nnrealPart_sub_nnrealPart_neg, integrable_of_nnreal, integral_sub, self_eq_nnrealPart_sub_nnrealPart_neg, sub_apply
-/
theorem integral_eq_integral_nnrealPart_sub [OpensMeasurableSpace X] (f : X ->ᵇ Real) :
    ∫ x, f x ∂μ = (∫ x, (f.nnrealPart x : Real) ∂μ) - ∫ x, ((-f).nnrealPart x : Real) ∂μ := by
  simp only [f.self_eq_nnrealPart_sub_nnrealPart_neg, Pi.sub_apply, integral_sub,
             integrable_of_nnreal]
  simp only [Function.comp_apply]

/--
theorem `lintegral_of_real_lt_top` / 定理 `lintegral_of_real_lt_top`

English:
theorem lintegral_of_real_lt_top
  given: (f : X ->ᵇ Real)
  proof: lintegral_lt_top_of_nnreal _ f.nnrealPart

中文:
定理 lintegral_of_real_lt_top
  条件: (f : X ->ᵇ 实数)
  证明: lintegral_lt_top_of_nnreal _ f.nnrealPart

Depends on / 依赖: f.nnrealPart, lintegral_lt_top_of_nnreal, nnrealPart
-/
theorem lintegral_of_real_lt_top (f : X ->ᵇ Real) :
    ∫⁻ x, ENNReal.ofReal (f x) ∂μ < ∞ := lintegral_lt_top_of_nnreal _ f.nnrealPart

/--
theorem `toReal_lintegral_coe_eq_integral` / 定理 `toReal_lintegral_coe_eq_integral`

English:
theorem toReal_lintegral_coe_eq_integral
  given: [OpensMeasurableSpace X] (f : X ->ᵇ Real>=0) (μ : Measure X)
  proof: by
  rw [integral_eq_lintegral_of_nonneg_ae _ (by simpa [Function.comp_apply] using!
        (NNReal.continuous_coe.comp f.continuous).measurable.aestronglyMeasurable)]
  · simp only [ENNReal.ofReal_coe_nnreal]
  · exact Eventually.of_forall (by simp)

中文:
定理 to实数_lintegral_coe_eq_integral
  条件: [OpensMeasurable空间 X] (f : X ->ᵇ 实数>=0) (μ : 测度 X)
  证明: by
  rw [integral_eq_lintegral_of_nonneg_ae _ (by simpa [Function.comp_apply] using!
        (NNReal.continuous_coe.comp f.continuous).measurable.aestronglyMeasurable)]
  · simp only [ENNReal.ofReal_coe_nnreal]
  · exact Eventually.of_forall (by simp)

Depends on / 依赖: ENNReal, ENNReal.ofReal_coe_nnreal, Eventually, Eventually.of_forall, Function, Function.comp_apply, NNReal, NNReal.continuous_coe.comp, aestronglyMeasurable, comp_apply, continuous, continuous_coe, f.continuous, integral_eq_lintegral_of_nonneg_ae, measurable, measurable.aestronglyMeasurable, ofReal_coe_nnreal, of_forall
-/
theorem toReal_lintegral_coe_eq_integral [OpensMeasurableSpace X] (f : X ->ᵇ Real>=0) (μ : Measure X) :
    (∫⁻ x, (f x : Real>=0∞) ∂μ).toReal = ∫ x, (f x : Real) ∂μ := by
  rw [integral_eq_lintegral_of_nonneg_ae _ (by simpa [Function.comp_apply] using!
        (NNReal.continuous_coe.comp f.continuous).measurable.aestronglyMeasurable)]
  · simp only [ENNReal.ofReal_coe_nnreal]
  · exact Eventually.of_forall (by simp)

end NNRealValued

section BochnerIntegral

variable {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
variable (μ : Measure X)
variable {E : Type*} [NormedAddCommGroup E]

set_option linter.style.whitespace false in -- manual alignment is not recognised
/--
lemma `lintegral_nnnorm_le` / 引理 `lintegral_nnnorm_le`

English:
lemma lintegral_nnnorm_le
  given: (f : X ->ᵇ E)
  proof: by
  calc ∫⁻ x, ‖f x‖₊ ∂μ
    _ <= ∫⁻ _, ‖f‖₊ ∂μ := by gcongr; apply nnnorm_coe_le_nnnorm
    _ = ‖f‖₊ * (μ Set.univ) := by rw [lintegral_const]

中文:
引理 lintegral_nnnorm_le
  条件: (f : X ->ᵇ E)
  证明: by
  calc ∫⁻ x, ‖f x‖₊ ∂μ
    _ <= ∫⁻ _, ‖f‖₊ ∂μ := by gcongr; apply nnnorm_coe_le_nnnorm
    _ = ‖f‖₊ * (μ Set.univ) := by rw [lintegral_const]

Depends on / 依赖: Set.univ, lintegral_const, nnnorm_coe_le_nnnorm
-/
lemma lintegral_nnnorm_le (f : X ->ᵇ E) :
    ∫⁻ x, ‖f x‖₊ ∂μ <= ‖f‖₊ * (μ Set.univ) := by
  calc ∫⁻ x, ‖f x‖₊ ∂μ
    _ <= ∫⁻ _, ‖f‖₊ ∂μ := by gcongr; apply nnnorm_coe_le_nnnorm
    _ = ‖f‖₊ * (μ Set.univ) := by rw [lintegral_const]

variable [OpensMeasurableSpace X] [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]

set_option linter.style.whitespace false in -- manual alignment is not recognised
/--
lemma `integrable` / 引理 `integrable`

English:
lemma integrable
  given: [IsFiniteMeasure μ] (f : X ->ᵇ E)
  proof: by
  refine ⟨f.continuous.measurable.aestronglyMeasurable, (hasFiniteIntegral_def _ _).mp ?_⟩
  calc ∫⁻ x, ‖f x‖₊ ∂μ
    _ <= ‖f‖₊ * (μ Set.univ) := f.lintegral_nnnorm_le μ
    _ < ∞ := ENNReal.mul_lt_top ENNReal.coe_lt_top (measure_lt_top μ Set.univ)

中文:
引理 integrable
  条件: [是有限测度 μ] (f : X ->ᵇ E)
  证明: by
  refine ⟨f.continuous.measurable.aestronglyMeasurable, (hasFiniteIntegral_def _ _).mp ?_⟩
  calc ∫⁻ x, ‖f x‖₊ ∂μ
    _ <= ‖f‖₊ * (μ Set.univ) := f.lintegral_nnnorm_le μ
    _ < ∞ := ENNReal.mul_lt_top ENNReal.coe_lt_top (measure_lt_top μ Set.univ)

Depends on / 依赖: ENNReal, ENNReal.coe_lt_top, ENNReal.mul_lt_top, Set.univ, aestronglyMeasurable, coe_lt_top, continuous, f.continuous.measurable.aestronglyMeasurable, f.lintegral_nnnorm_le, hasFiniteIntegral_def, lintegral_nnnorm_le, measurable, measure_lt_top, mul_lt_top
-/
lemma integrable [IsFiniteMeasure μ] (f : X ->ᵇ E) :
    Integrable f μ := by
  refine ⟨f.continuous.measurable.aestronglyMeasurable, (hasFiniteIntegral_def _ _).mp ?_⟩
  calc ∫⁻ x, ‖f x‖₊ ∂μ
    _ <= ‖f‖₊ * (μ Set.univ) := f.lintegral_nnnorm_le μ
    _ < ∞ := ENNReal.mul_lt_top ENNReal.coe_lt_top (measure_lt_top μ Set.univ)

variable [NormedSpace Real E]

set_option linter.style.whitespace false in -- manual alignment is not recognised
/--
lemma `norm_integral_le_mul_norm` / 引理 `norm_integral_le_mul_norm`

English:
lemma norm_integral_le_mul_norm
  given: [IsFiniteMeasure μ] (f : X ->ᵇ E)
  proof: by
  calc ‖∫ x, f x ∂μ‖
    _ <= ∫ x, ‖f x‖ ∂μ := norm_integral_le_integral_norm _
    _ <= ∫ _, ‖f‖ ∂μ := ?_
    _ = μ.real Set.univ • ‖f‖ := by rw [integral_const]
  apply integral_mono _ (integrable_const ‖f‖) (fun x => f.norm_coe_le_norm x) -- NOTE: `gcongr`?
  exact (integrable_norm_iff f.continuous.measurable.aestronglyMeasurable).mpr (f.integrable μ)

中文:
引理 norm_integral_le_mul_norm
  条件: [是有限测度 μ] (f : X ->ᵇ E)
  证明: by
  calc ‖∫ x, f x ∂μ‖
    _ <= ∫ x, ‖f x‖ ∂μ := norm_integral_le_integral_norm _
    _ <= ∫ _, ‖f‖ ∂μ := ?_
    _ = μ.real Set.univ • ‖f‖ := by rw [integral_const]
  apply integral_mono _ (integrable_const ‖f‖) (fun x => f.norm_coe_le_norm x) -- NOTE: `gcongr`?
  exact (integrable_norm_iff f.continuous.measurable.aestronglyMeasurable).mpr (f.integrable μ)

Depends on / 依赖: Set.univ, aestronglyMeasurable, continuous, f.continuous.measurable.aestronglyMeasurable, f.integrable, f.norm_coe_le_norm, integrable, integrable_const, integrable_norm_iff, integral_const, integral_mono, measurable, norm_coe_le_norm, norm_integral_le_integral_norm
-/
lemma norm_integral_le_mul_norm [IsFiniteMeasure μ] (f : X ->ᵇ E) :
    ‖∫ x, f x ∂μ‖ <= μ.real Set.univ * ‖f‖ := by
  calc ‖∫ x, f x ∂μ‖
    _ <= ∫ x, ‖f x‖ ∂μ := norm_integral_le_integral_norm _
    _ <= ∫ _, ‖f‖ ∂μ := ?_
    _ = μ.real Set.univ • ‖f‖ := by rw [integral_const]
  apply integral_mono _ (integrable_const ‖f‖) (fun x => f.norm_coe_le_norm x) -- NOTE: `gcongr`?
  exact (integrable_norm_iff f.continuous.measurable.aestronglyMeasurable).mpr (f.integrable μ)

/--
lemma `norm_integral_le_norm` / 引理 `norm_integral_le_norm`

English:
lemma norm_integral_le_norm
  given: [IsProbabilityMeasure μ] (f : X ->ᵇ E)
  proof: by
  convert! f.norm_integral_le_mul_norm μ
  simp

中文:
引理 norm_integral_le_norm
  条件: [是概率测度 μ] (f : X ->ᵇ E)
  证明: by
  convert! f.norm_integral_le_mul_norm μ
  simp

Depends on / 依赖: convert, f.norm_integral_le_mul_norm, norm_integral_le_mul_norm
-/
lemma norm_integral_le_norm [IsProbabilityMeasure μ] (f : X ->ᵇ E) :
    ‖∫ x, f x ∂μ‖ <= ‖f‖ := by
  convert! f.norm_integral_le_mul_norm μ
  simp

/--
lemma `isBounded_range_integral` / 引理 `isBounded_range_integral`

English:
lemma isBounded_range_integral
  proof: by
  apply isBounded_iff_forall_norm_le.mpr ⟨‖f‖, fun v hv => ?_⟩
  obtain ⟨i, hi⟩ := hv
  rw [← hi]
  apply f.norm_integral_le_norm (μs i)

中文:
引理 isBounded_range_integral
  证明: by
  apply isBounded_iff_forall_norm_le.mpr ⟨‖f‖, fun v hv => ?_⟩
  obtain ⟨i, hi⟩ := hv
  rw [← hi]
  apply f.norm_integral_le_norm (μs i)

Depends on / 依赖: f.norm_integral_le_norm, isBounded_iff_forall_norm_le, isBounded_iff_forall_norm_le.mpr, norm_integral_le_norm
-/
lemma isBounded_range_integral
    {ι : Type*} (μs : ι -> Measure X) [forall i, IsProbabilityMeasure (μs i)] (f : X ->ᵇ E) :
    Bornology.IsBounded (Set.range (fun i => ∫ x, f x ∂(μs i))) := by
  apply isBounded_iff_forall_norm_le.mpr ⟨‖f‖, fun v hv => ?_⟩
  obtain ⟨i, hi⟩ := hv
  rw [← hi]
  apply f.norm_integral_le_norm (μs i)

end BochnerIntegral

section RealValued

variable {X : Type*} [TopologicalSpace X]
variable [MeasurableSpace X] [OpensMeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]

/--
lemma `integral_add_const` / 引理 `integral_add_const`

English:
lemma integral_add_const
  given: (f : X ->ᵇ Real) (c : Real)
  proof: by
  simp [integral_add (f.integrable _) (integrable_const c)]

中文:
引理 integral_add_const
  条件: (f : X ->ᵇ 实数) (c : 实数)
  证明: by
  simp [integral_add (f.integrable _) (integrable_const c)]

Depends on / 依赖: f.integrable, integrable, integrable_const, integral_add
-/
lemma integral_add_const (f : X ->ᵇ Real) (c : Real) :
    ∫ x, (f + const X c) x ∂μ = ∫ x, f x ∂μ + μ.real Set.univ • c := by
  simp [integral_add (f.integrable _) (integrable_const c)]

/--
lemma `integral_const_sub` / 引理 `integral_const_sub`

English:
lemma integral_const_sub
  given: (f : X ->ᵇ Real) (c : Real)
  proof: by
  simp [integral_sub (integrable_const c) (f.integrable _)]

中文:
引理 integral_const_sub
  条件: (f : X ->ᵇ 实数) (c : 实数)
  证明: by
  simp [integral_sub (integrable_const c) (f.integrable _)]

Depends on / 依赖: f.integrable, integrable, integrable_const, integral_sub
-/
lemma integral_const_sub (f : X ->ᵇ Real) (c : Real) :
    ∫ x, (const X c - f) x ∂μ = μ.real Set.univ • c - ∫ x, f x ∂μ := by
  simp [integral_sub (integrable_const c) (f.integrable _)]

end RealValued

section tendsto_integral

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]

/--
lemma `tendsto_integral_of_forall_limsup_integral_le_integral` / 引理 `tendsto_integral_of_forall_limsup_integral_le_integral`

English:
lemma tendsto_integral_of_forall_limsup_integral_le_integral
  statement: {ι : Type*} {L : Filter ι}
  proof: by
  rcases eq_or_neBot L with rfl | hL
  · simp only [tendsto_bot]
  have obs := BoundedContinuousFunction.isBounded_range_integral μs f
  have bdd_above := BddAbove.isBoundedUnder L.univ_mem (by simpa using obs.bddAbove)
  have bdd_below := BddBelow.isBoundedUnder L.univ_mem (by simpa using obs.bddBelow)
  apply tendsto_of_le_liminf_of_limsup_le _ _ bdd_above bdd_below
  · have key := h _ (f.norm_sub_nonneg)
    simp_rw [f.integral_const_sub ‖f‖] at key
    simp only [probReal_univ, smul_eq_mul, one_mul] at key
    have := limsup_const_sub L (fun i => ∫ x, f x ∂(μs i)) ‖f‖ bdd_above.isCobounded_ge bdd_below
    rwa [this, _root_.sub_le_sub_iff_left ‖f‖] at key
  · have key := h _ (f.add_norm_nonneg)
    simp_rw [f.integral_add_const ‖f‖] at key
    simp only [probReal_univ, smul_eq_mul, one_mul] at key
    have := limsup_add_const L (fun i => ∫ x, f x ∂(μs i)) ‖f‖ bdd_above bdd_below.isCobounded_le
    rwa [this, add_le_add_iff_right] at key

中文:
引理 tendsto_integral_of_对任意_limsup_integral_le_integral
  结论: {ι : 类型} {L : 滤子 ι}
  证明: by
  rcases eq_or_neBot L with rfl | hL
  · simp only [tendsto_bot]
  have obs := BoundedContinuousFunction.isBounded_range_integral μs f
  have bdd_above := BddAbove.isBoundedUnder L.univ_mem (by simpa using obs.bddAbove)
  have bdd_below := BddBelow.isBoundedUnder L.univ_mem (by simpa using obs.bddBelow)
  apply tendsto_of_le_liminf_of_limsup_le _ _ bdd_above bdd_below
  · have key := h _ (f.norm_sub_nonneg)
    simp_rw [f.integral_const_sub ‖f‖] at key
    simp only [probReal_univ, smul_eq_mul, one_mul] at key
    have := limsup_const_sub L (fun i => ∫ x, f x ∂(μs i)) ‖f‖ bdd_above.isCobounded_ge bdd_below
    rwa [this, _root_.sub_le_sub_iff_left ‖f‖] at key
  · have key := h _ (f.add_norm_nonneg)
    simp_rw [f.integral_add_const ‖f‖] at key
    simp only [probReal_univ, smul_eq_mul, one_mul] at key
    have := limsup_add_const L (fun i => ∫ x, f x ∂(μs i)) ‖f‖ bdd_above bdd_below.isCobounded_le
    rwa [this, add_le_add_iff_right] at key

Depends on / 依赖: BddAbove, BddAbove.isBoundedUnder, BddBelow, BddBelow.isBoundedUnder, BoundedContinuousFunction, BoundedContinuousFunction.isBounded_range_integral, L.univ_mem, bddAbove, bddBelow, bdd_above, bdd_below, eq_or_neBot, f.integral_const_sub, f.norm_sub_nonneg, integral_const_sub, isBoundedUnder, isBounded_range_integral, norm_sub_nonneg, obs.bddAbove, obs.bddBelow
-/
lemma tendsto_integral_of_forall_limsup_integral_le_integral {ι : Type*} {L : Filter ι}
    {μ : Measure X} [IsProbabilityMeasure μ] {μs : ι -> Measure X} [forall i, IsProbabilityMeasure (μs i)]
    (h : forall f : X ->ᵇ Real, 0 <= f -> L.limsup (fun i => ∫ x, f x ∂(μs i)) <= ∫ x, f x ∂μ)
    (f : X ->ᵇ Real) :
    Tendsto (fun i => ∫ x, f x ∂(μs i)) L (𝓝 (∫ x, f x ∂μ)) := by
  rcases eq_or_neBot L with rfl | hL
  · simp only [tendsto_bot]
  have obs := BoundedContinuousFunction.isBounded_range_integral μs f
  have bdd_above := BddAbove.isBoundedUnder L.univ_mem (by simpa using obs.bddAbove)
  have bdd_below := BddBelow.isBoundedUnder L.univ_mem (by simpa using obs.bddBelow)
  apply tendsto_of_le_liminf_of_limsup_le _ _ bdd_above bdd_below
  · have key := h _ (f.norm_sub_nonneg)
    simp_rw [f.integral_const_sub ‖f‖] at key
    simp only [probReal_univ, smul_eq_mul, one_mul] at key
    have := limsup_const_sub L (fun i => ∫ x, f x ∂(μs i)) ‖f‖ bdd_above.isCobounded_ge bdd_below
    rwa [this, _root_.sub_le_sub_iff_left ‖f‖] at key
  · have key := h _ (f.add_norm_nonneg)
    simp_rw [f.integral_add_const ‖f‖] at key
    simp only [probReal_univ, smul_eq_mul, one_mul] at key
    have := limsup_add_const L (fun i => ∫ x, f x ∂(μs i)) ‖f‖ bdd_above bdd_below.isCobounded_le
    rwa [this, add_le_add_iff_right] at key

/--
lemma `tendsto_integral_of_forall_integral_le_liminf_integral` / 引理 `tendsto_integral_of_forall_integral_le_liminf_integral`

English:
lemma tendsto_integral_of_forall_integral_le_liminf_integral
  statement: {ι : Type*} {L : Filter ι}
  proof: by
  rcases eq_or_neBot L with rfl | hL
  · simp only [tendsto_bot]
  have obs := BoundedContinuousFunction.isBounded_range_integral μs f
  have bdd_above := BddAbove.isBoundedUnder L.univ_mem (by simpa using obs.bddAbove)
  have bdd_below := BddBelow.isBoundedUnder L.univ_mem (by simpa using obs.bddBelow)
  apply @tendsto_of_le_liminf_of_limsup_le Real ι _ _ _ L (fun i => ∫ x, f x ∂(μs i)) (∫ x, f x ∂μ)
  · have key := h _ (f.add_norm_nonneg)
    simp_rw [f.integral_add_const ‖f‖] at key
    simp only [probReal_univ, smul_eq_mul, one_mul] at key
    have := liminf_add_const L (fun i => ∫ x, f x ∂(μs i)) ‖f‖ bdd_above.isCobounded_ge bdd_below
    rwa [this, add_le_add_iff_right] at key
  · have key := h _ (f.norm_sub_nonneg)
    simp_rw [f.integral_const_sub ‖f‖] at key
    simp only [probReal_univ, smul_eq_mul, one_mul] at key
    have := liminf_const_sub L (fun i => ∫ x, f x ∂(μs i)) ‖f‖ bdd_above bdd_below.isCobounded_le
    rwa [this, sub_le_sub_iff_left] at key
  · exact bdd_above
  · exact bdd_below

中文:
引理 tendsto_integral_of_对任意_integral_le_liminf_integral
  结论: {ι : 类型} {L : 滤子 ι}
  证明: by
  rcases eq_or_neBot L with rfl | hL
  · simp only [tendsto_bot]
  have obs := BoundedContinuousFunction.isBounded_range_integral μs f
  have bdd_above := BddAbove.isBoundedUnder L.univ_mem (by simpa using obs.bddAbove)
  have bdd_below := BddBelow.isBoundedUnder L.univ_mem (by simpa using obs.bddBelow)
  apply @tendsto_of_le_liminf_of_limsup_le Real ι _ _ _ L (fun i => ∫ x, f x ∂(μs i)) (∫ x, f x ∂μ)
  · have key := h _ (f.add_norm_nonneg)
    simp_rw [f.integral_add_const ‖f‖] at key
    simp only [probReal_univ, smul_eq_mul, one_mul] at key
    have := liminf_add_const L (fun i => ∫ x, f x ∂(μs i)) ‖f‖ bdd_above.isCobounded_ge bdd_below
    rwa [this, add_le_add_iff_right] at key
  · have key := h _ (f.norm_sub_nonneg)
    simp_rw [f.integral_const_sub ‖f‖] at key
    simp only [probReal_univ, smul_eq_mul, one_mul] at key
    have := liminf_const_sub L (fun i => ∫ x, f x ∂(μs i)) ‖f‖ bdd_above bdd_below.isCobounded_le
    rwa [this, sub_le_sub_iff_left] at key
  · exact bdd_above
  · exact bdd_below

Depends on / 依赖: BddAbove, BddAbove.isBoundedUnder, BddBelow, BddBelow.isBoundedUnder, BoundedContinuousFunction, BoundedContinuousFunction.isBounded_range_integral, L.univ_mem, add_norm_nonneg, bddAbove, bddBelow, bdd_above, bdd_below, eq_or_neBot, f.add_norm_nonneg, f.integral_add_const, integral_add_const, isBoundedUnder, isBounded_range_integral, obs.bddAbove, obs.bddBelow
-/
lemma tendsto_integral_of_forall_integral_le_liminf_integral {ι : Type*} {L : Filter ι}
    {μ : Measure X} [IsProbabilityMeasure μ] {μs : ι -> Measure X} [forall i, IsProbabilityMeasure (μs i)]
    (h : forall f : X ->ᵇ Real, 0 <= f -> ∫ x, f x ∂μ <= L.liminf (fun i => ∫ x, f x ∂(μs i)))
    (f : X ->ᵇ Real) :
    Tendsto (fun i => ∫ x, f x ∂(μs i)) L (𝓝 (∫ x, f x ∂μ)) := by
  rcases eq_or_neBot L with rfl | hL
  · simp only [tendsto_bot]
  have obs := BoundedContinuousFunction.isBounded_range_integral μs f
  have bdd_above := BddAbove.isBoundedUnder L.univ_mem (by simpa using obs.bddAbove)
  have bdd_below := BddBelow.isBoundedUnder L.univ_mem (by simpa using obs.bddBelow)
  apply @tendsto_of_le_liminf_of_limsup_le Real ι _ _ _ L (fun i => ∫ x, f x ∂(μs i)) (∫ x, f x ∂μ)
  · have key := h _ (f.add_norm_nonneg)
    simp_rw [f.integral_add_const ‖f‖] at key
    simp only [probReal_univ, smul_eq_mul, one_mul] at key
    have := liminf_add_const L (fun i => ∫ x, f x ∂(μs i)) ‖f‖ bdd_above.isCobounded_ge bdd_below
    rwa [this, add_le_add_iff_right] at key
  · have key := h _ (f.norm_sub_nonneg)
    simp_rw [f.integral_const_sub ‖f‖] at key
    simp only [probReal_univ, smul_eq_mul, one_mul] at key
    have := liminf_const_sub L (fun i => ∫ x, f x ∂(μs i)) ‖f‖ bdd_above bdd_below.isCobounded_le
    rwa [this, sub_le_sub_iff_left] at key
  · exact bdd_above
  · exact bdd_below

end tendsto_integral --section

end BoundedContinuousFunction
