/-
Copyright (c) 2021 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying
-/
module

public import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.Probability.Independence.Basic

/-!
# Probability density function

This file defines the probability density function of random variables, by which we mean
measurable functions taking values in a Borel space. The probability density function is defined
as the Radon–Nikodym derivative of the law of `X`. In particular, a measurable function `f`
is said to the probability density function of a random variable `X` if for all measurable
sets `S`, `ℙ(X ∈ S) = ∫ x in S, f x dx`. Probability density functions are one way of describing
the distribution of a random variable, and are useful for calculating probabilities and
finding moments (although the latter is better achieved with moment-generating functions).

This file also defines the continuous uniform distribution and proves some properties about
random variables with this distribution.

## Main definitions

* `MeasureTheory.HasPDF` : A random variable `X : Ω → E` is said to `HasPDF` with
  respect to the measure `ℙ` on `Ω` and `μ` on `E` if the push-forward measure of `ℙ` along `X`
  is absolutely continuous with respect to `μ` and they `HaveLebesgueDecomposition`.
* `MeasureTheory.pdf` : If `X` is a random variable that `HasPDF X ℙ μ`, then `pdf X`
  is the Radon–Nikodym derivative of the push-forward measure of `ℙ` along `X` with respect to `μ`.
* `MeasureTheory.pdf.IsUniform` : A random variable `X` is said to follow the uniform
  distribution if it has a constant probability density function with a compact, non-null support.

## Main results

* `MeasureTheory.pdf.integral_pdf_smul` : Law of the unconscious statistician,
  i.e. if a random variable `X : Ω → E` has pdf `f`, then `𝔼(g(X)) = ∫ x, f x • g x dx` for
  all measurable `g : E → F`.
* `MeasureTheory.pdf.integral_mul_eq_integral` : A real-valued random variable `X` with
  pdf `f` has expectation `∫ x, x * f x dx`.
* `MeasureTheory.pdf.IsUniform.integral_eq` : If `X` follows the uniform distribution with
  its pdf having support `s`, then `X` has expectation `(λ s)⁻¹ * ∫ x in s, x dx` where `λ`
  is the Lebesgue measure.
-/

@[expose] public section


open scoped MeasureTheory NNReal ENNReal

open TopologicalSpace MeasureTheory Measure ProbabilityTheory

noncomputable section

namespace MeasureTheory

variable {Ω E : Type*} [MeasurableSpace E]

/--
Definition of `HasPDF` / `HasPDF` 的定义

English:
class HasPDF
  parameters: {m : MeasurableSpace Ω} (X : Ω -> E) (ℙ : Measure Ω) (μ : Measure E := by volume_tac)
  axioms and operations (3):
    - aemeasurable' : AEMeasurable X ℙ
    - haveLebesgueDecomposition' : (map X ℙ).HaveLebesgueDecomposition μ
    - absolutelyContinuous' : map X ℙ ≪ μ

中文:
类 HasPDF
  参数: {m : MeasurableSpace Ω} (X : Ω -> E) (ℙ : Measure Ω) (μ : Measure E := by volume_tac)
  公理与运算 (3 个):
    - aemeasurable' : AEMeasurable X ℙ
    - haveLebesgueDecomposition' : (map X ℙ).HaveLebesgueDecomposition μ
    - absolutelyContinuous' : map X ℙ ≪ μ

Depends on / 依赖: AEMeasurable, HaveLebesgueDecomposition, NonUnitalNonAssocCommSemiring, absolutelyContinuous, aemeasurable, haveLebesgueDecomposition, protected, toNonUnitalNonAssocCommSemiring, volume_tac
-/
class HasPDF {m : MeasurableSpace Ω} (X : Ω -> E) (ℙ : Measure Ω) (μ : Measure E := by volume_tac) :
    Prop where
  protected aemeasurable' : AEMeasurable X ℙ
  protected haveLebesgueDecomposition' : (map X ℙ).HaveLebesgueDecomposition μ
  protected absolutelyContinuous' : map X ℙ ≪ μ

section HasPDF

variable {_ : MeasurableSpace Ω} {X Y : Ω -> E} {ℙ : Measure Ω} {μ : Measure E}

/--
theorem `hasPDF_iff` / 定理 `hasPDF_iff`

English:
theorem hasPDF_iff
  proof: ⟨fun ⟨h₁, h₂, h₃⟩ => ⟨h₁, h₂, h₃⟩, fun ⟨h₁, h₂, h₃⟩ => ⟨h₁, h₂, h₃⟩⟩

中文:
定理 hasPDF_iff
  证明: ⟨fun ⟨h₁, h₂, h₃⟩ => ⟨h₁, h₂, h₃⟩, fun ⟨h₁, h₂, h₃⟩ => ⟨h₁, h₂, h₃⟩⟩
-/
theorem hasPDF_iff :
    HasPDF X ℙ μ ↔ AEMeasurable X ℙ ∧ (map X ℙ).HaveLebesgueDecomposition μ ∧ map X ℙ ≪ μ :=
  ⟨fun ⟨h₁, h₂, h₃⟩ => ⟨h₁, h₂, h₃⟩, fun ⟨h₁, h₂, h₃⟩ => ⟨h₁, h₂, h₃⟩⟩

/--
theorem `hasPDF_iff_of_aemeasurable` / 定理 `hasPDF_iff_of_aemeasurable`

English:
theorem hasPDF_iff_of_aemeasurable
  given: (hX : AEMeasurable X ℙ)
  proof: by
  rw [hasPDF_iff]
  simp only [hX, true_and]

中文:
定理 hasPDF_iff_of_aemeasurable
  条件: (hX : AEMeasurable X ℙ)
  证明: by
  rw [hasPDF_iff]
  simp only [hX, true_and]

Depends on / 依赖: hasPDF_iff, true_and
-/
theorem hasPDF_iff_of_aemeasurable (hX : AEMeasurable X ℙ) :
    HasPDF X ℙ μ ↔ (map X ℙ).HaveLebesgueDecomposition μ ∧ map X ℙ ≪ μ := by
  rw [hasPDF_iff]
  simp only [hX, true_and]

variable (X ℙ μ) in
/--
theorem `HasPDF.aemeasurable` / 定理 `HasPDF.aemeasurable`

English:
theorem HasPDF.aemeasurable
  given: [HasPDF X ℙ μ]
  statement: AEMeasurable X ℙ
  proof: HasPDF.aemeasurable' μ

中文:
定理 HasPDF.aemeasurable
  条件: [HasPDF X ℙ μ]
  结论: AEMeasurable X ℙ
  证明: HasPDF.aemeasurable' μ

Depends on / 依赖: HasPDF, HasPDF.aemeasurable, aemeasurable
-/
theorem HasPDF.aemeasurable [HasPDF X ℙ μ] : AEMeasurable X ℙ := HasPDF.aemeasurable' μ

/--
Instance `HasPDF.haveLebesgueDecomposition` / 实例 `HasPDF.haveLebesgueDecomposition`

English:
instance HasPDF.haveLebesgueDecomposition
  signature: [HasPDF X ℙ μ]
  body: HasPDF.haveLebesgueDecomposition'

中文:
实例 HasPDF.haveLebesgueDecomposition
  签名: [HasPDF X ℙ μ]
  定义体: HasPDF.haveLebesgueDecomposition'

Depends on / 依赖: HasPDF, HasPDF.haveLebesgueDecomposition, haveLebesgueDecomposition
-/
instance HasPDF.haveLebesgueDecomposition [HasPDF X ℙ μ] : (map X ℙ).HaveLebesgueDecomposition μ :=
  HasPDF.haveLebesgueDecomposition'

/--
theorem `HasPDF.absolutelyContinuous` / 定理 `HasPDF.absolutelyContinuous`

English:
theorem HasPDF.absolutelyContinuous
  given: [HasPDF X ℙ μ]
  statement: map X ℙ ≪ μ
  proof: HasPDF.absolutelyContinuous'

中文:
定理 HasPDF.absolutelyContinuous
  条件: [HasPDF X ℙ μ]
  结论: map X ℙ ≪ μ
  证明: HasPDF.absolutelyContinuous'

Depends on / 依赖: HasPDF, HasPDF.absolutelyContinuous, absolutelyContinuous
-/
theorem HasPDF.absolutelyContinuous [HasPDF X ℙ μ] : map X ℙ ≪ μ := HasPDF.absolutelyContinuous'

/--
theorem `HasPDF.quasiMeasurePreserving_of_measurable` / 定理 `HasPDF.quasiMeasurePreserving_of_measurable`

English:
theorem HasPDF.quasiMeasurePreserving_of_measurable
  statement: (X : Ω -> E) (ℙ : Measure Ω) (μ : Measure E)
  proof: { measurable := h
    absolutelyContinuous := HasPDF.absolutelyContinuous .. }

中文:
定理 HasPDF.quasiMeasurePreserving_of_measurable
  结论: (X : Ω -> E) (ℙ : Measure Ω) (μ : Measure E)
  证明: { measurable := h
    absolutelyContinuous := HasPDF.absolutelyContinuous .. }

Depends on / 依赖: HasPDF, HasPDF.absolutelyContinuous, absolutelyContinuous, measurable
-/
theorem HasPDF.quasiMeasurePreserving_of_measurable (X : Ω -> E) (ℙ : Measure Ω) (μ : Measure E)
    [HasPDF X ℙ μ] (h : Measurable X) : QuasiMeasurePreserving X ℙ μ :=
  { measurable := h
    absolutelyContinuous := HasPDF.absolutelyContinuous .. }

/--
theorem `HasPDF.congr` / 定理 `HasPDF.congr`

English:
theorem HasPDF.congr
  given: (hXY : X =ᵐ[ℙ] Y) [hX : HasPDF X ℙ μ]
  statement: HasPDF Y ℙ μ
  proof: ⟨(HasPDF.aemeasurable X ℙ μ).congr hXY, ℙ.map_congr hXY ▸ hX.haveLebesgueDecomposition,
    ℙ.map_congr hXY ▸ hX.absolutelyContinuous⟩

中文:
定理 HasPDF.congr
  条件: (hXY : X =ᵐ[ℙ] Y) [hX : HasPDF X ℙ μ]
  结论: HasPDF Y ℙ μ
  证明: ⟨(HasPDF.aemeasurable X ℙ μ).congr hXY, ℙ.map_congr hXY ▸ hX.haveLebesgueDecomposition,
    ℙ.map_congr hXY ▸ hX.absolutelyContinuous⟩

Depends on / 依赖: HasPDF, HasPDF.aemeasurable, absolutelyContinuous, aemeasurable, hX.absolutelyContinuous, hX.haveLebesgueDecomposition, haveLebesgueDecomposition, map_congr
-/
theorem HasPDF.congr (hXY : X =ᵐ[ℙ] Y) [hX : HasPDF X ℙ μ] : HasPDF Y ℙ μ :=
  ⟨(HasPDF.aemeasurable X ℙ μ).congr hXY, ℙ.map_congr hXY ▸ hX.haveLebesgueDecomposition,
    ℙ.map_congr hXY ▸ hX.absolutelyContinuous⟩

/--
theorem `HasPDF.congr_iff` / 定理 `HasPDF.congr_iff`

English:
theorem HasPDF.congr_iff
  given: (hXY : X =ᵐ[ℙ] Y)
  statement: HasPDF X ℙ μ ↔ HasPDF Y ℙ μ
  proof: ⟨fun _ => HasPDF.congr hXY, fun _ => HasPDF.congr hXY.symm⟩

中文:
定理 HasPDF.congr_iff
  条件: (hXY : X =ᵐ[ℙ] Y)
  结论: HasPDF X ℙ μ ↔ HasPDF Y ℙ μ
  证明: ⟨fun _ => HasPDF.congr hXY, fun _ => HasPDF.congr hXY.symm⟩

Depends on / 依赖: HasPDF, HasPDF.congr, hXY.symm
-/
theorem HasPDF.congr_iff (hXY : X =ᵐ[ℙ] Y) : HasPDF X ℙ μ ↔ HasPDF Y ℙ μ :=
  ⟨fun _ => HasPDF.congr hXY, fun _ => HasPDF.congr hXY.symm⟩

/--
theorem `hasPDF_of_map_eq_withDensity` / 定理 `hasPDF_of_map_eq_withDensity`

English:
theorem hasPDF_of_map_eq_withDensity
  statement: (hX : AEMeasurable X ℙ) (f : E -> Real>=0∞) (hf : AEMeasurable f μ)
  proof: by
  refine ⟨hX, ?_, ?_⟩ <;> rw [h]
  · rw [withDensity_congr_ae hf.ae_eq_mk]
    exact haveLebesgueDecomposition_withDensity μ hf.measurable_mk
  · exact withDensity_absolutelyContinuous μ f

中文:
定理 hasPDF_of_map_eq_withDensity
  结论: (hX : AEMeasurable X ℙ) (f : E -> 实数>=0∞) (hf : AEMeasurable f μ)
  证明: by
  refine ⟨hX, ?_, ?_⟩ <;> rw [h]
  · rw [withDensity_congr_ae hf.ae_eq_mk]
    exact haveLebesgueDecomposition_withDensity μ hf.measurable_mk
  · exact withDensity_absolutelyContinuous μ f

Depends on / 依赖: ae_eq_mk, haveLebesgueDecomposition_withDensity, hf.ae_eq_mk, hf.measurable_mk, measurable_mk, withDensity_absolutelyContinuous, withDensity_congr_ae
-/
theorem hasPDF_of_map_eq_withDensity (hX : AEMeasurable X ℙ) (f : E -> Real>=0∞) (hf : AEMeasurable f μ)
    (h : map X ℙ = μ.withDensity f) : HasPDF X ℙ μ := by
  refine ⟨hX, ?_, ?_⟩ <;> rw [h]
  · rw [withDensity_congr_ae hf.ae_eq_mk]
    exact haveLebesgueDecomposition_withDensity μ hf.measurable_mk
  · exact withDensity_absolutelyContinuous μ f

end HasPDF

/--
Definition of `pdf` / `pdf` 的定义

English:
definition pdf
  signature: {_ : MeasurableSpace Ω} (X : Ω -> E) (ℙ : Measure Ω) (μ : Measure E := by volume_tac)
  body: (map X ℙ).rnDeriv μ

中文:
定义 pdf
  签名: {_ : MeasurableSpace Ω} (X : Ω -> E) (ℙ : Measure Ω) (μ : Measure E := by volume_tac)
  定义体: (map X ℙ).rnDeriv μ

Depends on / 依赖: rnDeriv, volume_tac
-/
def pdf {_ : MeasurableSpace Ω} (X : Ω -> E) (ℙ : Measure Ω) (μ : Measure E := by volume_tac) :
    E -> Real>=0∞ :=
  (map X ℙ).rnDeriv μ

/--
theorem `pdf_def` / 定理 `pdf_def`

English:
theorem pdf_def
  given: {_ : MeasurableSpace Ω} {ℙ : Measure Ω} {μ : Measure E} {X : Ω -> E}
  proof: rfl

中文:
定理 pdf_def
  条件: {_ : MeasurableSpace Ω} {ℙ : Measure Ω} {μ : Measure E} {X : Ω -> E}
  证明: rfl
-/
theorem pdf_def {_ : MeasurableSpace Ω} {ℙ : Measure Ω} {μ : Measure E} {X : Ω -> E} :
    pdf X ℙ μ = (map X ℙ).rnDeriv μ := rfl

/--
theorem `pdf_of_not_aemeasurable` / 定理 `pdf_of_not_aemeasurable`

English:
theorem pdf_of_not_aemeasurable
  statement: {_ : MeasurableSpace Ω} {ℙ : Measure Ω} {μ : Measure E}
  proof: by
  rw [pdf_def]; rw [map_of_not_aemeasurable hX]
  exact rnDeriv_zero μ

中文:
定理 pdf_of_not_aemeasurable
  结论: {_ : MeasurableSpace Ω} {ℙ : Measure Ω} {μ : Measure E}
  证明: by
  rw [pdf_def]; rw [map_of_not_aemeasurable hX]
  exact rnDeriv_zero μ

Depends on / 依赖: CanLift, NonUnitalSubsemiring, map_of_not_aemeasurable, pdf_def, rnDeriv_zero
-/
theorem pdf_of_not_aemeasurable {_ : MeasurableSpace Ω} {ℙ : Measure Ω} {μ : Measure E}
    {X : Ω -> E} (hX : ¬AEMeasurable X ℙ) : pdf X ℙ μ =ᵐ[μ] 0 := by
  rw [pdf_def]; rw [map_of_not_aemeasurable hX]
  exact rnDeriv_zero μ

/--
theorem `pdf_of_not_haveLebesgueDecomposition` / 定理 `pdf_of_not_haveLebesgueDecomposition`

English:
theorem pdf_of_not_haveLebesgueDecomposition
  statement: {_ : MeasurableSpace Ω} {ℙ : Measure Ω}
  proof: rnDeriv_of_not_haveLebesgueDecomposition h

中文:
定理 pdf_of_not_haveLebesgueDecomposition
  结论: {_ : MeasurableSpace Ω} {ℙ : Measure Ω}
  证明: rnDeriv_of_not_haveLebesgueDecomposition h

Depends on / 依赖: rnDeriv_of_not_haveLebesgueDecomposition
-/
theorem pdf_of_not_haveLebesgueDecomposition {_ : MeasurableSpace Ω} {ℙ : Measure Ω}
    {μ : Measure E} {X : Ω -> E} (h : ¬(map X ℙ).HaveLebesgueDecomposition μ) : pdf X ℙ μ = 0 :=
  rnDeriv_of_not_haveLebesgueDecomposition h

/--
theorem `aemeasurable_of_pdf_ne_zero` / 定理 `aemeasurable_of_pdf_ne_zero`

English:
theorem aemeasurable_of_pdf_ne_zero
  statement: {m : MeasurableSpace Ω} {ℙ : Measure Ω} {μ : Measure E}
  proof: by
  contrapose h
  exact pdf_of_not_aemeasurable h

中文:
定理 aemeasurable_of_pdf_ne_zero
  结论: {m : MeasurableSpace Ω} {ℙ : Measure Ω} {μ : Measure E}
  证明: by
  contrapose h
  exact pdf_of_not_aemeasurable h

Depends on / 依赖: contrapose, pdf_of_not_aemeasurable
-/
theorem aemeasurable_of_pdf_ne_zero {m : MeasurableSpace Ω} {ℙ : Measure Ω} {μ : Measure E}
    (X : Ω -> E) (h : ¬pdf X ℙ μ =ᵐ[μ] 0) : AEMeasurable X ℙ := by
  contrapose h
  exact pdf_of_not_aemeasurable h

/--
theorem `hasPDF_of_pdf_ne_zero` / 定理 `hasPDF_of_pdf_ne_zero`

English:
theorem hasPDF_of_pdf_ne_zero
  statement: {m : MeasurableSpace Ω} {ℙ : Measure Ω} {μ : Measure E} {X : Ω -> E}
  proof: by
  refine ⟨?_, ?_, hac⟩
  · exact aemeasurable_of_pdf_ne_zero X hpdf
  · contrapose hpdf
    have := pdf_of_not_haveLebesgueDecomposition hpdf
    filter_upwards using congrFun this

@[fun_prop]

中文:
定理 hasPDF_of_pdf_ne_zero
  结论: {m : MeasurableSpace Ω} {ℙ : Measure Ω} {μ : Measure E} {X : Ω -> E}
  证明: by
  refine ⟨?_, ?_, hac⟩
  · exact aemeasurable_of_pdf_ne_zero X hpdf
  · contrapose hpdf
    have := pdf_of_not_haveLebesgueDecomposition hpdf
    filter_upwards using congrFun this

@[fun_prop]

Depends on / 依赖: aemeasurable_of_pdf_ne_zero, contrapose, filter_upwards, pdf_of_not_haveLebesgueDecomposition
-/
theorem hasPDF_of_pdf_ne_zero {m : MeasurableSpace Ω} {ℙ : Measure Ω} {μ : Measure E} {X : Ω -> E}
    (hac : map X ℙ ≪ μ) (hpdf : ¬pdf X ℙ μ =ᵐ[μ] 0) : HasPDF X ℙ μ := by
  refine ⟨?_, ?_, hac⟩
  · exact aemeasurable_of_pdf_ne_zero X hpdf
  · contrapose hpdf
    have := pdf_of_not_haveLebesgueDecomposition hpdf
    filter_upwards using congrFun this

@[fun_prop]
/--
theorem `measurable_pdf` / 定理 `measurable_pdf`

English:
theorem measurable_pdf
  statement: {m : MeasurableSpace Ω} (X : Ω -> E) (ℙ : Measure Ω)
  proof: by
  exact measurable_rnDeriv _ _

中文:
定理 measurable_pdf
  结论: {m : MeasurableSpace Ω} (X : Ω -> E) (ℙ : Measure Ω)
  证明: by
  exact measurable_rnDeriv _ _

Depends on / 依赖: Measurable, measurable_rnDeriv, volume_tac
-/
theorem measurable_pdf {m : MeasurableSpace Ω} (X : Ω -> E) (ℙ : Measure Ω)
    (μ : Measure E := by volume_tac) : Measurable (pdf X ℙ μ) := by
  exact measurable_rnDeriv _ _

/--
theorem `withDensity_pdf_le_map` / 定理 `withDensity_pdf_le_map`

English:
theorem withDensity_pdf_le_map
  statement: {_ : MeasurableSpace Ω} (X : Ω -> E) (ℙ : Measure Ω)
  proof: withDensity_rnDeriv_le _ _

中文:
定理 withDensity_pdf_le_map
  结论: {_ : MeasurableSpace Ω} (X : Ω -> E) (ℙ : Measure Ω)
  证明: withDensity_rnDeriv_le _ _

Depends on / 依赖: volume_tac, withDensity, withDensity_rnDeriv_le
-/
theorem withDensity_pdf_le_map {_ : MeasurableSpace Ω} (X : Ω -> E) (ℙ : Measure Ω)
    (μ : Measure E := by volume_tac) : μ.withDensity (pdf X ℙ μ) <= map X ℙ :=
  withDensity_rnDeriv_le _ _

/--
theorem `setLIntegral_pdf_le_map` / 定理 `setLIntegral_pdf_le_map`

English:
theorem setLIntegral_pdf_le_map
  statement: {m : MeasurableSpace Ω} (X : Ω -> E) (ℙ : Measure Ω)
  proof: by
  apply (withDensity_apply_le _ s).trans
  exact withDensity_pdf_le_map _ _ _ s

中文:
定理 setLIntegral_pdf_le_map
  结论: {m : MeasurableSpace Ω} (X : Ω -> E) (ℙ : Measure Ω)
  证明: by
  apply (withDensity_apply_le _ s).trans
  exact withDensity_pdf_le_map _ _ _ s

Depends on / 依赖: volume_tac, withDensity_apply_le, withDensity_pdf_le_map
-/
theorem setLIntegral_pdf_le_map {m : MeasurableSpace Ω} (X : Ω -> E) (ℙ : Measure Ω)
    (μ : Measure E := by volume_tac) (s : Set E) :
    ∫⁻ x in s, pdf X ℙ μ x ∂μ <= map X ℙ s := by
  apply (withDensity_apply_le _ s).trans
  exact withDensity_pdf_le_map _ _ _ s

/--
theorem `map_eq_withDensity_pdf` / 定理 `map_eq_withDensity_pdf`

English:
theorem map_eq_withDensity_pdf
  statement: {m : MeasurableSpace Ω} (X : Ω -> E) (ℙ : Measure Ω)
  proof: by
  rw [pdf_def]; rw [withDensity_rnDeriv_eq _ _ hX.absolutelyContinuous]

中文:
定理 map_eq_withDensity_pdf
  结论: {m : MeasurableSpace Ω} (X : Ω -> E) (ℙ : Measure Ω)
  证明: by
  rw [pdf_def]; rw [withDensity_rnDeriv_eq _ _ hX.absolutelyContinuous]

Depends on / 依赖: HasPDF, absolutelyContinuous, hX.absolutelyContinuous, pdf_def, volume_tac, withDensity, withDensity_rnDeriv_eq
-/
theorem map_eq_withDensity_pdf {m : MeasurableSpace Ω} (X : Ω -> E) (ℙ : Measure Ω)
    (μ : Measure E := by volume_tac) [hX : HasPDF X ℙ μ] :
    map X ℙ = μ.withDensity (pdf X ℙ μ) := by
  rw [pdf_def]; rw [withDensity_rnDeriv_eq _ _ hX.absolutelyContinuous]

/--
theorem `map_eq_setLIntegral_pdf` / 定理 `map_eq_setLIntegral_pdf`

English:
theorem map_eq_setLIntegral_pdf
  statement: {m : MeasurableSpace Ω} (X : Ω -> E) (ℙ : Measure Ω)
  proof: by
  rw [← withDensity_apply _ hs]; rw [map_eq_withDensity_pdf X ℙ μ]

中文:
定理 map_eq_setLIntegral_pdf
  结论: {m : MeasurableSpace Ω} (X : Ω -> E) (ℙ : Measure Ω)
  证明: by
  rw [← withDensity_apply _ hs]; rw [map_eq_withDensity_pdf X ℙ μ]

Depends on / 依赖: HasPDF, MeasurableSet, map_eq_withDensity_pdf, volume_tac, withDensity_apply
-/
theorem map_eq_setLIntegral_pdf {m : MeasurableSpace Ω} (X : Ω -> E) (ℙ : Measure Ω)
    (μ : Measure E := by volume_tac) [hX : HasPDF X ℙ μ] {s : Set E}
    (hs : MeasurableSet s) : map X ℙ s = ∫⁻ x in s, pdf X ℙ μ x ∂μ := by
  rw [← withDensity_apply _ hs]; rw [map_eq_withDensity_pdf X ℙ μ]

namespace pdf

variable {m : MeasurableSpace Ω} {ℙ : Measure Ω} {μ : Measure E}

/--
theorem `congr` / 定理 `congr`

English:
theorem congr
  given: {X Y : Ω -> E} (hXY : X =ᵐ[ℙ] Y)
  statement: pdf X ℙ μ = pdf Y ℙ μ
  proof: by
  rw [pdf_def]; rw [pdf_def]; rw [map_congr hXY]

中文:
定理 congr
  条件: {X Y : Ω -> E} (hXY : X =ᵐ[ℙ] Y)
  结论: pdf X ℙ μ = pdf Y ℙ μ
  证明: by
  rw [pdf_def]; rw [pdf_def]; rw [map_congr hXY]

Depends on / 依赖: SetLike, SetLike.coe_injective, coe_injective, ha.symm
-/
protected theorem congr {X Y : Ω -> E} (hXY : X =ᵐ[ℙ] Y) : pdf X ℙ μ = pdf Y ℙ μ := by
  rw [pdf_def]; rw [pdf_def]; rw [map_congr hXY]

/--
theorem `lintegral_eq_measure_univ` / 定理 `lintegral_eq_measure_univ`

English:
theorem lintegral_eq_measure_univ
  given: {X : Ω -> E} [HasPDF X ℙ μ]
  proof: by
  rw [← setLIntegral_univ]; rw [← map_eq_setLIntegral_pdf X ℙ μ MeasurableSet.univ]; rw [map_apply_of_aemeasurable (HasPDF.aemeasurable X ℙ μ) MeasurableSet.univ]; rw [Set.preimage_univ]

中文:
定理 lintegral_eq_measure_univ
  条件: {X : Ω -> E} [HasPDF X ℙ μ]
  证明: by
  rw [← setLIntegral_univ]; rw [← map_eq_setLIntegral_pdf X ℙ μ MeasurableSet.univ]; rw [map_apply_of_aemeasurable (HasPDF.aemeasurable X ℙ μ) MeasurableSet.univ]; rw [Set.preimage_univ]

Depends on / 依赖: HasPDF, HasPDF.aemeasurable, MeasurableSet, MeasurableSet.univ, Set.preimage_univ, aemeasurable, map_apply_of_aemeasurable, map_eq_setLIntegral_pdf, preimage_univ, setLIntegral_univ
-/
theorem lintegral_eq_measure_univ {X : Ω -> E} [HasPDF X ℙ μ] :
    ∫⁻ x, pdf X ℙ μ x ∂μ = ℙ Set.univ := by
  rw [← setLIntegral_univ]; rw [← map_eq_setLIntegral_pdf X ℙ μ MeasurableSet.univ]; rw [map_apply_of_aemeasurable (HasPDF.aemeasurable X ℙ μ) MeasurableSet.univ]; rw [Set.preimage_univ]

/--
theorem `eq_of_map_eq_withDensity` / 定理 `eq_of_map_eq_withDensity`

English:
theorem eq_of_map_eq_withDensity
  statement: [IsFiniteMeasure ℙ] {X : Ω -> E} [HasPDF X ℙ μ] (f : E -> Real>=0∞)
  proof: by
  rw [map_eq_withDensity_pdf X ℙ μ]
  apply withDensity_eq_iff (measurable_pdf X ℙ μ).aemeasurable hmf
  rw [lintegral_eq_measure_univ]
  exact measure_ne_top _ _

中文:
定理 eq_of_map_eq_withDensity
  结论: [IsFiniteMeasure ℙ] {X : Ω -> E} [HasPDF X ℙ μ] (f : E -> 实数>=0∞)
  证明: by
  rw [map_eq_withDensity_pdf X ℙ μ]
  apply withDensity_eq_iff (measurable_pdf X ℙ μ).aemeasurable hmf
  rw [lintegral_eq_measure_univ]
  exact measure_ne_top _ _

Depends on / 依赖: aemeasurable, lintegral_eq_measure_univ, map_eq_withDensity_pdf, measurable_pdf, measure_ne_top, withDensity_eq_iff
-/
theorem eq_of_map_eq_withDensity [IsFiniteMeasure ℙ] {X : Ω -> E} [HasPDF X ℙ μ] (f : E -> Real>=0∞)
    (hmf : AEMeasurable f μ) : map X ℙ = μ.withDensity f ↔ pdf X ℙ μ =ᵐ[μ] f := by
  rw [map_eq_withDensity_pdf X ℙ μ]
  apply withDensity_eq_iff (measurable_pdf X ℙ μ).aemeasurable hmf
  rw [lintegral_eq_measure_univ]
  exact measure_ne_top _ _

/--
theorem `eq_of_map_eq_withDensity'` / 定理 `eq_of_map_eq_withDensity'`

English:
theorem eq_of_map_eq_withDensity'
  statement: [SigmaFinite μ] {X : Ω -> E} [HasPDF X ℙ μ] (f : E -> Real>=0∞)
  proof: map_eq_withDensity_pdf X ℙ μ ▸
    withDensity_eq_iff_of_sigmaFinite (measurable_pdf X ℙ μ).aemeasurable hmf

nonrec theorem ae_lt_top [IsFiniteMeasure ℙ] {μ : Measure E} {X : Ω -> E} :
    forallᵐ x ∂μ, pdf X ℙ μ x < ∞ :=
  rnDeriv_lt_top (map X ℙ) μ

nonrec theorem ofReal_toReal_ae_eq [IsFiniteMea

中文:
定理 eq_of_map_eq_withDensity'
  结论: [SigmaFinite μ] {X : Ω -> E} [HasPDF X ℙ μ] (f : E -> 实数>=0∞)
  证明: map_eq_withDensity_pdf X ℙ μ ▸
    withDensity_eq_iff_of_sigmaFinite (measurable_pdf X ℙ μ).aemeasurable hmf

nonrec theorem ae_lt_top [IsFiniteMeasure ℙ] {μ : Measure E} {X : Ω -> E} :
    forallᵐ x ∂μ, pdf X ℙ μ x < ∞ :=
  rnDeriv_lt_top (map X ℙ) μ

nonrec theorem ofReal_toReal_ae_eq [IsFiniteMea

Depends on / 依赖: aemeasurable, map_eq_withDensity_pdf, measurable_pdf, withDensity_eq_iff_of_sigmaFinite
-/
theorem eq_of_map_eq_withDensity' [SigmaFinite μ] {X : Ω -> E} [HasPDF X ℙ μ] (f : E -> Real>=0∞)
    (hmf : AEMeasurable f μ) : map X ℙ = μ.withDensity f ↔ pdf X ℙ μ =ᵐ[μ] f :=
  map_eq_withDensity_pdf X ℙ μ ▸
    withDensity_eq_iff_of_sigmaFinite (measurable_pdf X ℙ μ).aemeasurable hmf

nonrec theorem ae_lt_top [IsFiniteMeasure ℙ] {μ : Measure E} {X : Ω -> E} :
    forallᵐ x ∂μ, pdf X ℙ μ x < ∞ :=
  rnDeriv_lt_top (map X ℙ) μ

nonrec theorem ofReal_toReal_ae_eq [IsFiniteMeasure ℙ] {X : Ω -> E} :
    (fun x => ENNReal.ofReal (pdf X ℙ μ x).toReal) =ᵐ[μ] pdf X ℙ μ :=
  ofReal_toReal_ae_eq ae_lt_top

section IntegralPDFMul

/--
theorem `lintegral_pdf_mul` / 定理 `lintegral_pdf_mul`

English:
theorem lintegral_pdf_mul
  statement: {X : Ω -> E} [HasPDF X ℙ μ] {f : E -> Real>=0∞}
  proof: by
  rw [pdf_def]; rw [← lintegral_map' (hf.mono_ac HasPDF.absolutelyContinuous) (HasPDF.aemeasurable X ℙ μ)]; rw [lintegral_rnDeriv_mul HasPDF.absolutelyContinuous hf]

中文:
定理 lintegral_pdf_mul
  结论: {X : Ω -> E} [HasPDF X ℙ μ] {f : E -> 实数>=0∞}
  证明: by
  rw [pdf_def]; rw [← lintegral_map' (hf.mono_ac HasPDF.absolutelyContinuous) (HasPDF.aemeasurable X ℙ μ)]; rw [lintegral_rnDeriv_mul HasPDF.absolutelyContinuous hf]

Depends on / 依赖: HasPDF, HasPDF.absolutelyContinuous, HasPDF.aemeasurable, absolutelyContinuous, aemeasurable, hf.mono_ac, lintegral_map, lintegral_rnDeriv_mul, mono_ac, pdf_def
-/
theorem lintegral_pdf_mul {X : Ω -> E} [HasPDF X ℙ μ] {f : E -> Real>=0∞}
    (hf : AEMeasurable f μ) : ∫⁻ x, pdf X ℙ μ x * f x ∂μ = ∫⁻ x, f (X x) ∂ℙ := by
  rw [pdf_def]; rw [← lintegral_map' (hf.mono_ac HasPDF.absolutelyContinuous) (HasPDF.aemeasurable X ℙ μ)]; rw [lintegral_rnDeriv_mul HasPDF.absolutelyContinuous hf]

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace Real F]

/--
theorem `integrable_pdf_smul_iff` / 定理 `integrable_pdf_smul_iff`

English:
theorem integrable_pdf_smul_iff
  statement: [IsFiniteMeasure ℙ] {X : Ω -> E} [HasPDF X ℙ μ] {f : E -> F}
  proof: by
  rw [← Function.comp_def]; rw [← integrable_map_measure (hf.mono_ac HasPDF.absolutelyContinuous) (HasPDF.aemeasurable X ℙ μ)]; rw [map_eq_withDensity_pdf X ℙ μ]; rw [pdf_def]; rw [integrable_rnDeriv_smul_iff HasPDF.absolutelyContinuous]
  rw [withDensity_rnDeriv_eq _ _ HasPDF.absolutelyContinuou

中文:
定理 integrable_pdf_smul_iff
  结论: [IsFiniteMeasure ℙ] {X : Ω -> E} [HasPDF X ℙ μ] {f : E -> F}
  证明: by
  rw [← Function.comp_def]; rw [← integrable_map_measure (hf.mono_ac HasPDF.absolutelyContinuous) (HasPDF.aemeasurable X ℙ μ)]; rw [map_eq_withDensity_pdf X ℙ μ]; rw [pdf_def]; rw [integrable_rnDeriv_smul_iff HasPDF.absolutelyContinuous]
  rw [withDensity_rnDeriv_eq _ _ HasPDF.absolutelyContinuou

Depends on / 依赖: Function, Function.comp_def, HasPDF, HasPDF.absolutelyContinuous, HasPDF.aemeasurable, absolutelyContinuous, aemeasurable, comp_def, hf.mono_ac, integrable_map_measure, integrable_rnDeriv_smul_iff, map_eq_withDensity_pdf, mono_ac, pdf_def, withDensity_rnDeriv_eq
-/
theorem integrable_pdf_smul_iff [IsFiniteMeasure ℙ] {X : Ω -> E} [HasPDF X ℙ μ] {f : E -> F}
    (hf : AEStronglyMeasurable f μ) :
    Integrable (fun x => (pdf X ℙ μ x).toReal • f x) μ ↔ Integrable (fun x => f (X x)) ℙ := by
  rw [← Function.comp_def]; rw [← integrable_map_measure (hf.mono_ac HasPDF.absolutelyContinuous) (HasPDF.aemeasurable X ℙ μ)]; rw [map_eq_withDensity_pdf X ℙ μ]; rw [pdf_def]; rw [integrable_rnDeriv_smul_iff HasPDF.absolutelyContinuous]
  rw [withDensity_rnDeriv_eq _ _ HasPDF.absolutelyContinuous]

/--
theorem `integral_pdf_smul` / 定理 `integral_pdf_smul`

English:
theorem integral_pdf_smul
  statement: [IsFiniteMeasure ℙ] {X : Ω -> E} [HasPDF X ℙ μ] {f : E -> F}
  proof: by
  rw [← integral_map (HasPDF.aemeasurable X ℙ μ) (hf.mono_ac HasPDF.absolutelyContinuous)]; rw [map_eq_withDensity_pdf X ℙ μ]; rw [pdf_def]; rw [integral_rnDeriv_smul HasPDF.absolutelyContinuous]; rw [withDensity_rnDeriv_eq _ _ HasPDF.absolutelyContinuous]

中文:
定理 integral_pdf_smul
  结论: [IsFiniteMeasure ℙ] {X : Ω -> E} [HasPDF X ℙ μ] {f : E -> F}
  证明: by
  rw [← integral_map (HasPDF.aemeasurable X ℙ μ) (hf.mono_ac HasPDF.absolutelyContinuous)]; rw [map_eq_withDensity_pdf X ℙ μ]; rw [pdf_def]; rw [integral_rnDeriv_smul HasPDF.absolutelyContinuous]; rw [withDensity_rnDeriv_eq _ _ HasPDF.absolutelyContinuous]

Depends on / 依赖: HasPDF, HasPDF.absolutelyContinuous, HasPDF.aemeasurable, absolutelyContinuous, aemeasurable, hf.mono_ac, integral_map, integral_rnDeriv_smul, map_eq_withDensity_pdf, mono_ac, pdf_def, withDensity_rnDeriv_eq
-/
theorem integral_pdf_smul [IsFiniteMeasure ℙ] {X : Ω -> E} [HasPDF X ℙ μ] {f : E -> F}
    (hf : AEStronglyMeasurable f μ) : ∫ x, (pdf X ℙ μ x).toReal • f x ∂μ = ∫ x, f (X x) ∂ℙ := by
  rw [← integral_map (HasPDF.aemeasurable X ℙ μ) (hf.mono_ac HasPDF.absolutelyContinuous)]; rw [map_eq_withDensity_pdf X ℙ μ]; rw [pdf_def]; rw [integral_rnDeriv_smul HasPDF.absolutelyContinuous]; rw [withDensity_rnDeriv_eq _ _ HasPDF.absolutelyContinuous]

end IntegralPDFMul

section

variable {F : Type*} [MeasurableSpace F] {ν : Measure F} (X : Ω -> E) [HasPDF X ℙ μ] {g : E -> F}

/--
theorem `quasiMeasurePreserving_hasPDF` / 定理 `quasiMeasurePreserving_hasPDF`

English:
theorem quasiMeasurePreserving_hasPDF
  statement: (hg : QuasiMeasurePreserving g μ ν)
  proof: by
  have hgm : AEMeasurable g (map X ℙ) := hg.aemeasurable.mono_ac HasPDF.absolutelyContinuous
  rw [hasPDF_iff]; rw [← AEMeasurable.map_map_of_aemeasurable hgm (HasPDF.aemeasurable X ℙ μ)]
  refine ⟨hg.measurable.comp_aemeasurable (HasPDF.aemeasurable _ _ μ), hmap, ?_⟩
  exact (HasPDF.absolutelyCo

中文:
定理 quasiMeasurePreserving_hasPDF
  结论: (hg : QuasiMeasurePreserving g μ ν)
  证明: by
  have hgm : AEMeasurable g (map X ℙ) := hg.aemeasurable.mono_ac HasPDF.absolutelyContinuous
  rw [hasPDF_iff]; rw [← AEMeasurable.map_map_of_aemeasurable hgm (HasPDF.aemeasurable X ℙ μ)]
  refine ⟨hg.measurable.comp_aemeasurable (HasPDF.aemeasurable _ _ μ), hmap, ?_⟩
  exact (HasPDF.absolutelyCo

Depends on / 依赖: AEMeasurable, AEMeasurable.map_map_of_aemeasurable, HasPDF, HasPDF.absolutelyContinuous, HasPDF.absolutelyContinuous.map, HasPDF.aemeasurable, absolutelyContinuous, aemeasurable, comp_aemeasurable, hasPDF_iff, hg.aemeasurable.mono_ac, hg.measurable.comp_aemeasurable, map_map_of_aemeasurable, measurable, mono_ac
-/
theorem quasiMeasurePreserving_hasPDF (hg : QuasiMeasurePreserving g μ ν)
    (hmap : (map g (map X ℙ)).HaveLebesgueDecomposition ν) : HasPDF (g ∘ X) ℙ ν := by
  have hgm : AEMeasurable g (map X ℙ) := hg.aemeasurable.mono_ac HasPDF.absolutelyContinuous
  rw [hasPDF_iff]; rw [← AEMeasurable.map_map_of_aemeasurable hgm (HasPDF.aemeasurable X ℙ μ)]
  refine ⟨hg.measurable.comp_aemeasurable (HasPDF.aemeasurable _ _ μ), hmap, ?_⟩
  exact (HasPDF.absolutelyContinuous.map hg.1).trans hg.2

/--
theorem `quasiMeasurePreserving_hasPDF'` / 定理 `quasiMeasurePreserving_hasPDF'`

English:
theorem quasiMeasurePreserving_hasPDF'
  statement: [SFinite ℙ] [SigmaFinite ν]
  proof: quasiMeasurePreserving_hasPDF X hg inferInstance

中文:
定理 quasiMeasurePreserving_hasPDF'
  结论: [SFinite ℙ] [SigmaFinite ν]
  证明: quasiMeasurePreserving_hasPDF X hg inferInstance

Depends on / 依赖: quasiMeasurePreserving_hasPDF
-/
theorem quasiMeasurePreserving_hasPDF' [SFinite ℙ] [SigmaFinite ν]
    (hg : QuasiMeasurePreserving g μ ν) : HasPDF (g ∘ X) ℙ ν :=
  quasiMeasurePreserving_hasPDF X hg inferInstance

end

section Real

variable {X : Ω -> Real}

nonrec theorem _root_.Real.hasPDF_iff [SFinite ℙ] :
    HasPDF X ℙ ↔ AEMeasurable X ℙ ∧ map X ℙ ≪ volume := by
  rw [hasPDF_iff]; rw [and_iff_right (inferInstance : HaveLebesgueDecomposition _ _)]

/-- A real-valued random variable `X` `HasPDF X ℙ λ` (where `λ` is the Lebesgue measure) if and
only if the push-forward measure of `ℙ` along `X` is absolutely continuous with respect to `λ`. -/
nonrec theorem _root_.Real.hasPDF_iff_of_aemeasurable [SFinite ℙ] (hX : AEMeasurable X ℙ) :
    HasPDF X ℙ ↔ map X ℙ ≪ volume := by
  rw [Real.hasPDF_iff]; rw [and_iff_right hX]

variable [IsFiniteMeasure ℙ]

/--
theorem `integral_mul_eq_integral` / 定理 `integral_mul_eq_integral`

English:
theorem integral_mul_eq_integral
  given: [HasPDF X ℙ]
  statement: ∫ x, x * (pdf X ℙ volume x).toReal = ∫ x, X x ∂ℙ
  proof: calc
    _ = ∫ x, (pdf X ℙ volume x).toReal * x := by congr with x; exact mul_comm _ _
    _ = _ := integral_pdf_smul measurable_id.aestronglyMeasurable

中文:
定理 integral_mul_eq_integral
  条件: [HasPDF X ℙ]
  结论: ∫ x, x * (pdf X ℙ volume x).to实数 = ∫ x, X x ∂ℙ
  证明: calc
    _ = ∫ x, (pdf X ℙ volume x).toReal * x := by congr with x; exact mul_comm _ _
    _ = _ := integral_pdf_smul measurable_id.aestronglyMeasurable

Depends on / 依赖: aestronglyMeasurable, integral_pdf_smul, measurable_id, measurable_id.aestronglyMeasurable, mul_comm, toReal, volume
-/
theorem integral_mul_eq_integral [HasPDF X ℙ] : ∫ x, x * (pdf X ℙ volume x).toReal = ∫ x, X x ∂ℙ :=
  calc
    _ = ∫ x, (pdf X ℙ volume x).toReal * x := by congr with x; exact mul_comm _ _
    _ = _ := integral_pdf_smul measurable_id.aestronglyMeasurable

/--
theorem `hasFiniteIntegral_mul` / 定理 `hasFiniteIntegral_mul`

English:
theorem hasFiniteIntegral_mul
  statement: {f : Real -> Real} {g : Real -> Real>=0∞} (hg : pdf X ℙ =ᵐ[volume] g)
  proof: by
  rw [hasFiniteIntegral_iff_enorm]
  have : (fun x => ‖f x‖ₑ * g x) =ᵐ[volume] fun x => ‖f x * (pdf X ℙ volume x).toReal‖ₑ := by
    refine ae_eq_trans ((ae_eq_refl _).fun_mul (ae_eq_trans hg.symm ofReal_toReal_ae_eq.symm)) ?_
    simp_rw [← smul_eq_mul, enorm_smul, smul_eq_mul]
    refine .fun_m

中文:
定理 hasFiniteIntegral_mul
  结论: {f : 实数 -> 实数} {g : 实数 -> 实数>=0∞} (hg : pdf X ℙ =ᵐ[volume] g)
  证明: by
  rw [hasFiniteIntegral_iff_enorm]
  have : (fun x => ‖f x‖ₑ * g x) =ᵐ[volume] fun x => ‖f x * (pdf X ℙ volume x).toReal‖ₑ := by
    refine ae_eq_trans ((ae_eq_refl _).fun_mul (ae_eq_trans hg.symm ofReal_toReal_ae_eq.symm)) ?_
    simp_rw [← smul_eq_mul, enorm_smul, smul_eq_mul]
    refine .fun_m

Depends on / 依赖: ENNReal, ENNReal.toReal_nonneg, Real.enorm_eq_ofReal, ae_eq_refl, ae_eq_trans, enorm_eq_ofReal, enorm_smul, fun_mul, hasFiniteIntegral_iff_enorm, hg.symm, lintegral_congr_ae, lt_top_iff_ne_top, ofReal_toReal_ae_eq, ofReal_toReal_ae_eq.symm, simp_rw, smul_eq_mul, toReal, toReal_nonneg, volume
-/
theorem hasFiniteIntegral_mul {f : Real -> Real} {g : Real -> Real>=0∞} (hg : pdf X ℙ =ᵐ[volume] g)
    (hgi : ∫⁻ x, ‖f x‖ₑ * g x != ∞) :
    HasFiniteIntegral fun x => f x * (pdf X ℙ volume x).toReal := by
  rw [hasFiniteIntegral_iff_enorm]
  have : (fun x => ‖f x‖ₑ * g x) =ᵐ[volume] fun x => ‖f x * (pdf X ℙ volume x).toReal‖ₑ := by
    refine ae_eq_trans ((ae_eq_refl _).fun_mul (ae_eq_trans hg.symm ofReal_toReal_ae_eq.symm)) ?_
    simp_rw [← smul_eq_mul, enorm_smul, smul_eq_mul]
    refine .fun_mul (ae_eq_refl _) ?_
    simp only [Real.enorm_eq_ofReal ENNReal.toReal_nonneg, ae_eq_refl]
  rwa [lt_top_iff_ne_top, ← lintegral_congr_ae this]

end Real

section TwoVariables

variable {F : Type*} [MeasurableSpace F] {ν : Measure F} {X : Ω -> E} {Y : Ω -> F}

/--
theorem `indepFun_iff_pdf_prod_eq_pdf_mul_pdf` / 定理 `indepFun_iff_pdf_prod_eq_pdf_mul_pdf`

English:
theorem indepFun_iff_pdf_prod_eq_pdf_mul_pdf
  proof: by
  have : HasPDF X ℙ μ := quasiMeasurePreserving_hasPDF' (μ := μ.prod ν) (fun ω => (X ω, Y ω))
    quasiMeasurePreserving_fst
  have : HasPDF Y ℙ ν := quasiMeasurePreserving_hasPDF' (μ := μ.prod ν) (fun ω => (X ω, Y ω))
    quasiMeasurePreserving_snd
  have h₀ : (ℙ.map X).prod (ℙ.map Y) =
      (μ

中文:
定理 indepFun_iff_pdf_prod_eq_pdf_mul_pdf
  证明: by
  have : HasPDF X ℙ μ := quasiMeasurePreserving_hasPDF' (μ := μ.prod ν) (fun ω => (X ω, Y ω))
    quasiMeasurePreserving_fst
  have : HasPDF Y ℙ ν := quasiMeasurePreserving_hasPDF' (μ := μ.prod ν) (fun ω => (X ω, Y ω))
    quasiMeasurePreserving_snd
  have h₀ : (ℙ.map X).prod (ℙ.map Y) =
      (μ

Depends on / 依赖: HasPDF, aemeasurable, hs.prod, lintegral_prod_mul, measurable_pdf, prod_eq, prod_restrict, quasiMeasurePreserving_fst, quasiMeasurePreserving_hasPDF, quasiMeasurePreserving_snd, withDensity, withDensity_apply
-/
theorem indepFun_iff_pdf_prod_eq_pdf_mul_pdf
    [IsFiniteMeasure ℙ] [SigmaFinite μ] [SigmaFinite ν] [HasPDF (fun ω => (X ω, Y ω)) ℙ (μ.prod ν)] :
    IndepFun X Y ℙ ↔
      pdf (fun ω => (X ω, Y ω)) ℙ (μ.prod ν) =ᵐ[μ.prod ν] fun z => pdf X ℙ μ z.1 * pdf Y ℙ ν z.2 := by
  have : HasPDF X ℙ μ := quasiMeasurePreserving_hasPDF' (μ := μ.prod ν) (fun ω => (X ω, Y ω))
    quasiMeasurePreserving_fst
  have : HasPDF Y ℙ ν := quasiMeasurePreserving_hasPDF' (μ := μ.prod ν) (fun ω => (X ω, Y ω))
    quasiMeasurePreserving_snd
  have h₀ : (ℙ.map X).prod (ℙ.map Y) =
      (μ.prod ν).withDensity fun z => pdf X ℙ μ z.1 * pdf Y ℙ ν z.2 :=
    prod_eq fun s t hs ht => by rw [withDensity_apply _ (hs.prod ht), ← prod_restrict,
      lintegral_prod_mul (measurable_pdf X ℙ μ).aemeasurable (measurable_pdf Y ℙ ν).aemeasurable,
      map_eq_setLIntegral_pdf X ℙ μ hs, map_eq_setLIntegral_pdf Y ℙ ν ht]
  rw [indepFun_iff_map_prod_eq_prod_map_map (HasPDF.aemeasurable X ℙ μ) (HasPDF.aemeasurable Y ℙ ν)]; rw [← eq_of_map_eq_withDensity]; rw [h₀]
  exact (((measurable_pdf X ℙ μ).comp measurable_fst).mul
    ((measurable_pdf Y ℙ ν).comp measurable_snd)).aemeasurable

end TwoVariables

end pdf

end MeasureTheory

section Group

namespace ProbabilityTheory

variable {Ω G : Type*} {mΩ : MeasurableSpace Ω} {ℙ : Measure Ω} [Group G] {mG : MeasurableSpace G}
  [MeasurableMul₂ G] [MeasurableInv G] {μ : Measure G} [IsMulLeftInvariant μ] {X Y : Ω -> G}

@[to_additive]
/--
theorem `IndepFun.mul_hasPDF'` / 定理 `IndepFun.mul_hasPDF'`

English:
theorem IndepFun.mul_hasPDF'
  statement: [SFinite μ] [HasPDF X ℙ μ] [HasPDF Y ℙ μ]
  proof: by
  have : AEMeasurable X ℙ := HasPDF.aemeasurable' μ
  have : AEMeasurable Y ℙ := HasPDF.aemeasurable' μ
  rw [hasPDF_iff_of_aemeasurable (by fun_prop)]; rw [hXY.map_mul_eq_map_mconv_map₀' (by fun_prop) (by fun_prop) σX σY]
  refine ⟨?_, mconv_absolutelyContinuous HasPDF.absolutelyContinuous⟩
  ap

中文:
定理 IndepFun.mul_hasPDF'
  结论: [SFinite μ] [HasPDF X ℙ μ] [HasPDF Y ℙ μ]
  证明: by
  have : AEMeasurable X ℙ := HasPDF.aemeasurable' μ
  have : AEMeasurable Y ℙ := HasPDF.aemeasurable' μ
  rw [hasPDF_iff_of_aemeasurable (by fun_prop)]; rw [hXY.map_mul_eq_map_mconv_map₀' (by fun_prop) (by fun_prop) σX σY]
  refine ⟨?_, mconv_absolutelyContinuous HasPDF.absolutelyContinuous⟩
  ap

Depends on / 依赖: AEMeasurable, HasPDF, HasPDF.absolutelyContinuous, HasPDF.aemeasurable, HaveLebesgueDecomposition, HaveLebesgueDecomposition.mconv, absolutelyContinuous, aemeasurable, fun_prop, hXY.map_mul_eq_map_mconv_map, hasPDF_iff_of_aemeasurable, mconv_absolutelyContinuous
-/
theorem IndepFun.mul_hasPDF' [SFinite μ] [HasPDF X ℙ μ] [HasPDF Y ℙ μ]
    (σX : SigmaFinite (ℙ.map X)) (σY : SigmaFinite (ℙ.map Y)) (hXY : IndepFun X Y ℙ) :
    HasPDF (X * Y) ℙ μ := by
  have : AEMeasurable X ℙ := HasPDF.aemeasurable' μ
  have : AEMeasurable Y ℙ := HasPDF.aemeasurable' μ
  rw [hasPDF_iff_of_aemeasurable (by fun_prop)]; rw [hXY.map_mul_eq_map_mconv_map₀' (by fun_prop) (by fun_prop) σX σY]
  refine ⟨?_, mconv_absolutelyContinuous HasPDF.absolutelyContinuous⟩
  apply HaveLebesgueDecomposition.mconv <;> exact HasPDF.absolutelyContinuous

@[to_additive]
/--
theorem `IndepFun.mul_hasPDF` / 定理 `IndepFun.mul_hasPDF`

English:
theorem IndepFun.mul_hasPDF
  statement: [SFinite μ] [HasPDF X ℙ μ] [HasPDF Y ℙ μ] [IsFiniteMeasure ℙ]
  proof: by
  apply hXY.mul_hasPDF' <;> apply IsFiniteMeasure.toSigmaFinite

@[to_additive]

中文:
定理 IndepFun.mul_hasPDF
  结论: [SFinite μ] [HasPDF X ℙ μ] [HasPDF Y ℙ μ] [IsFiniteMeasure ℙ]
  证明: by
  apply hXY.mul_hasPDF' <;> apply IsFiniteMeasure.toSigmaFinite

@[to_additive]

Depends on / 依赖: IsFiniteMeasure, IsFiniteMeasure.toSigmaFinite, hXY.mul_hasPDF, mul_hasPDF, toSigmaFinite
-/
theorem IndepFun.mul_hasPDF [SFinite μ] [HasPDF X ℙ μ] [HasPDF Y ℙ μ] [IsFiniteMeasure ℙ]
  (hXY : IndepFun X Y ℙ) : HasPDF (X * Y) ℙ μ := by
  apply hXY.mul_hasPDF' <;> apply IsFiniteMeasure.toSigmaFinite

@[to_additive]
/--
theorem `IndepFun.pdf_mul_eq_mlconvolution_pdf'` / 定理 `IndepFun.pdf_mul_eq_mlconvolution_pdf'`

English:
theorem IndepFun.pdf_mul_eq_mlconvolution_pdf'
  statement: [SigmaFinite μ] [HasPDF X ℙ μ] [HasPDF Y ℙ μ]
  proof: by
  rw [pdf]; rw [hXY.map_mul_eq_map_mconv_map₀' (HasPDF.aemeasurable' μ) (HasPDF.aemeasurable' μ) σX σY]
  apply rnDeriv_mconv' <;> exact HasPDF.absolutelyContinuous

@[to_additive]

中文:
定理 IndepFun.pdf_mul_eq_mlconvolution_pdf'
  结论: [SigmaFinite μ] [HasPDF X ℙ μ] [HasPDF Y ℙ μ]
  证明: by
  rw [pdf]; rw [hXY.map_mul_eq_map_mconv_map₀' (HasPDF.aemeasurable' μ) (HasPDF.aemeasurable' μ) σX σY]
  apply rnDeriv_mconv' <;> exact HasPDF.absolutelyContinuous

@[to_additive]

Depends on / 依赖: HasPDF, HasPDF.absolutelyContinuous, HasPDF.aemeasurable, absolutelyContinuous, aemeasurable, hXY.map_mul_eq_map_mconv_map, rnDeriv_mconv
-/
theorem IndepFun.pdf_mul_eq_mlconvolution_pdf' [SigmaFinite μ] [HasPDF X ℙ μ] [HasPDF Y ℙ μ]
    (σX : SigmaFinite (ℙ.map X)) (σY : SigmaFinite (ℙ.map Y)) (hXY : IndepFun X Y ℙ) :
    pdf (X * Y) ℙ μ =ᵐ[μ] pdf X ℙ μ ⋆ₘₗ[μ] pdf Y ℙ μ := by
  rw [pdf]; rw [hXY.map_mul_eq_map_mconv_map₀' (HasPDF.aemeasurable' μ) (HasPDF.aemeasurable' μ) σX σY]
  apply rnDeriv_mconv' <;> exact HasPDF.absolutelyContinuous

@[to_additive]
/--
theorem `IndepFun.pdf_mul_eq_mlconvolution_pdf` / 定理 `IndepFun.pdf_mul_eq_mlconvolution_pdf`

English:
theorem IndepFun.pdf_mul_eq_mlconvolution_pdf
  statement: [SFinite μ] [HasPDF X ℙ μ] [HasPDF Y ℙ μ]
  proof: by
  rw [pdf]; rw [hXY.map_mul_eq_map_mconv_map₀ (HasPDF.aemeasurable' μ) (HasPDF.aemeasurable' μ)]
  apply rnDeriv_mconv <;> exact HasPDF.absolutelyContinuous

中文:
定理 IndepFun.pdf_mul_eq_mlconvolution_pdf
  结论: [SFinite μ] [HasPDF X ℙ μ] [HasPDF Y ℙ μ]
  证明: by
  rw [pdf]; rw [hXY.map_mul_eq_map_mconv_map₀ (HasPDF.aemeasurable' μ) (HasPDF.aemeasurable' μ)]
  apply rnDeriv_mconv <;> exact HasPDF.absolutelyContinuous

Depends on / 依赖: HasPDF, HasPDF.absolutelyContinuous, HasPDF.aemeasurable, absolutelyContinuous, aemeasurable, hXY.map_mul_eq_map_mconv_map, rnDeriv_mconv
-/
theorem IndepFun.pdf_mul_eq_mlconvolution_pdf [SFinite μ] [HasPDF X ℙ μ] [HasPDF Y ℙ μ]
    [IsFiniteMeasure ℙ] (hXY : IndepFun X Y ℙ) :
    pdf (X * Y) ℙ μ =ᵐ[μ] pdf X ℙ μ ⋆ₘₗ[μ] pdf Y ℙ μ := by
  rw [pdf]; rw [hXY.map_mul_eq_map_mconv_map₀ (HasPDF.aemeasurable' μ) (HasPDF.aemeasurable' μ)]
  apply rnDeriv_mconv <;> exact HasPDF.absolutelyContinuous

end ProbabilityTheory

end Group
