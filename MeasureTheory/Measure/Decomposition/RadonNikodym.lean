/-
Copyright (c) 2021 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying, Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.Measure.Decomposition.Lebesgue

/-!
# Radon-Nikodym theorem

This file proves the Radon-Nikodym theorem. The Radon-Nikodym theorem states that, given measures
`μ, ν`, if `HaveLebesgueDecomposition μ ν`, then `μ` is absolutely continuous with respect to
`ν` if and only if there exists a measurable function `f : α → ℝ≥0∞` such that `μ = fν`.
In particular, we have `f = rnDeriv μ ν`.

The Radon-Nikodym theorem will allow us to define many important concepts in probability theory,
most notably probability cumulative functions. It could also be used to define the conditional
expectation of a real function, but we take a different approach (see the file
`MeasureTheory/Function/ConditionalExpectation`).

## Main results

* `MeasureTheory.Measure.absolutelyContinuous_iff_withDensity_rnDeriv_eq` :
  the Radon-Nikodym theorem
* `MeasureTheory.SignedMeasure.absolutelyContinuous_iff_withDensityᵥ_rnDeriv_eq` :
  the Radon-Nikodym theorem for signed measures

The file also contains properties of `rnDeriv` that use the Radon-Nikodym theorem, notably
* `MeasureTheory.Measure.rnDeriv_withDensity_left`: the Radon-Nikodym derivative of
  `μ.withDensity f` with respect to `ν` is `f * μ.rnDeriv ν`.
* `MeasureTheory.Measure.rnDeriv_withDensity_right`: the Radon-Nikodym derivative of
  `μ` with respect to `ν.withDensity f` is `f⁻¹ * μ.rnDeriv ν`.
* `MeasureTheory.Measure.inv_rnDeriv`: `(μ.rnDeriv ν)⁻¹ =ᵐ[μ] ν.rnDeriv μ`.
* `MeasureTheory.Measure.setLIntegral_rnDeriv`: `∫⁻ x in s, μ.rnDeriv ν x ∂ν = μ s` if `μ ≪ ν`.
  There is also a version of this result for the Bochner integral.

## Tags

Radon-Nikodym theorem
-/

public section

assert_not_exists InnerProductSpace
assert_not_exists MeasureTheory.VectorMeasure

noncomputable section

open scoped MeasureTheory NNReal ENNReal

variable {α β : Type*} {m : MeasurableSpace α}

namespace MeasureTheory

namespace Measure

/--
theorem `withDensity_rnDeriv_eq` / 定理 `withDensity_rnDeriv_eq`

English:
theorem withDensity_rnDeriv_eq
  given: (μ ν : Measure α) [HaveLebesgueDecomposition μ ν] (h : μ ≪ ν)
  proof: by
  suffices μ.singularPart ν = 0 by
    conv_rhs => rw [haveLebesgueDecomposition_add μ ν, this, zero_add]
  exact (singularPart_eq_zero μ ν).mpr h

中文:
定理 withDensity_rnDeriv_eq
  条件: (μ ν : 测度 α) [有Lebesgue分解 μ ν] (h : μ ≪ ν)
  证明: by
  suffices μ.singularPart ν = 0 by
    conv_rhs => rw [haveLebesgueDecomposition_add μ ν, this, zero_add]
  exact (singularPart_eq_zero μ ν).mpr h

Depends on / 依赖: conv_rhs, haveLebesgueDecomposition_add, singularPart, singularPart_eq_zero, zero_add
-/
theorem withDensity_rnDeriv_eq (μ ν : Measure α) [HaveLebesgueDecomposition μ ν] (h : μ ≪ ν) :
    ν.withDensity (rnDeriv μ ν) = μ := by
  suffices μ.singularPart ν = 0 by
    conv_rhs => rw [haveLebesgueDecomposition_add μ ν, this, zero_add]
  exact (singularPart_eq_zero μ ν).mpr h

variable {μ ν : Measure α}

/--
theorem `absolutelyContinuous_iff_withDensity_rnDeriv_eq` / 定理 `absolutelyContinuous_iff_withDensity_rnDeriv_eq`

English:
theorem absolutelyContinuous_iff_withDensity_rnDeriv_eq
  proof: ⟨withDensity_rnDeriv_eq μ ν, fun h => h ▸ withDensity_absolutelyContinuous _ _⟩

中文:
定理 absolutelyContinuous_iff_withDensity_rnDeriv_eq
  证明: ⟨withDensity_rnDeriv_eq μ ν, fun h => h ▸ withDensity_absolutelyContinuous _ _⟩

Depends on / 依赖: withDensity_absolutelyContinuous, withDensity_rnDeriv_eq
-/
theorem absolutelyContinuous_iff_withDensity_rnDeriv_eq
    [HaveLebesgueDecomposition μ ν] : μ ≪ ν ↔ ν.withDensity (rnDeriv μ ν) = μ :=
  ⟨withDensity_rnDeriv_eq μ ν, fun h => h ▸ withDensity_absolutelyContinuous _ _⟩

/--
lemma `rnDeriv_pos` / 引理 `rnDeriv_pos`

English:
lemma rnDeriv_pos
  given: [HaveLebesgueDecomposition μ ν] (hμν : μ ≪ ν)
  proof: by
  rw [← Measure.withDensity_rnDeriv_eq _ _ hμν]; rw [ae_withDensity_iff (Measure.measurable_rnDeriv _ _)]; rw [Measure.withDensity_rnDeriv_eq _ _ hμν]
  exact ae_of_all _ (fun x hx => hx.pos)

中文:
引理 rnDeriv_pos
  条件: [有Lebesgue分解 μ ν] (hμν : μ ≪ ν)
  证明: by
  rw [← Measure.withDensity_rnDeriv_eq _ _ hμν]; rw [ae_withDensity_iff (Measure.measurable_rnDeriv _ _)]; rw [Measure.withDensity_rnDeriv_eq _ _ hμν]
  exact ae_of_all _ (fun x hx => hx.pos)

Depends on / 依赖: Measure, Measure.measurable_rnDeriv, Measure.withDensity_rnDeriv_eq, ae_of_all, ae_withDensity_iff, hx.pos, measurable_rnDeriv, withDensity_rnDeriv_eq
-/
lemma rnDeriv_pos [HaveLebesgueDecomposition μ ν] (hμν : μ ≪ ν) :
    forallᵐ x ∂μ, 0 < μ.rnDeriv ν x := by
  rw [← Measure.withDensity_rnDeriv_eq _ _ hμν]; rw [ae_withDensity_iff (Measure.measurable_rnDeriv _ _)]; rw [Measure.withDensity_rnDeriv_eq _ _ hμν]
  exact ae_of_all _ (fun x hx => hx.pos)

/--
lemma `rnDeriv_pos'` / 引理 `rnDeriv_pos'`

English:
lemma rnDeriv_pos'
  given: [HaveLebesgueDecomposition ν μ] [SigmaFinite μ] (hμν : μ ≪ ν)
  proof: by
  refine (absolutelyContinuous_withDensity_rnDeriv hμν).ae_le ?_
  filter_upwards [Measure.rnDeriv_pos (withDensity_absolutelyContinuous μ (ν.rnDeriv μ)),
    (withDensity_absolutelyContinuous μ (ν.rnDeriv μ)).ae_le
    (Measure.rnDeriv_withDensity μ (Measure.measurable_rnDeriv ν μ))] with x hx h

中文:
引理 rnDeriv_pos'
  条件: [有Lebesgue分解 ν μ] [σ有限 μ] (hμν : μ ≪ ν)
  证明: by
  refine (absolutelyContinuous_withDensity_rnDeriv hμν).ae_le ?_
  filter_upwards [Measure.rnDeriv_pos (withDensity_absolutelyContinuous μ (ν.rnDeriv μ)),
    (withDensity_absolutelyContinuous μ (ν.rnDeriv μ)).ae_le
    (Measure.rnDeriv_withDensity μ (Measure.measurable_rnDeriv ν μ))] with x hx h

Depends on / 依赖: Measure, Measure.measurable_rnDeriv, Measure.rnDeriv_pos, Measure.rnDeriv_withDensity, absolutelyContinuous_withDensity_rnDeriv, ae_le, filter_upwards, measurable_rnDeriv, rnDeriv, rnDeriv_pos, rnDeriv_withDensity, withDensity_absolutelyContinuous
-/
lemma rnDeriv_pos' [HaveLebesgueDecomposition ν μ] [SigmaFinite μ] (hμν : μ ≪ ν) :
    forallᵐ x ∂μ, 0 < ν.rnDeriv μ x := by
  refine (absolutelyContinuous_withDensity_rnDeriv hμν).ae_le ?_
  filter_upwards [Measure.rnDeriv_pos (withDensity_absolutelyContinuous μ (ν.rnDeriv μ)),
    (withDensity_absolutelyContinuous μ (ν.rnDeriv μ)).ae_le
    (Measure.rnDeriv_withDensity μ (Measure.measurable_rnDeriv ν μ))] with x hx hx2
  rwa [← hx2]

section rnDeriv_withDensity_leftRight

variable {f : α -> Real>=0∞}

/--
lemma `rnDeriv_withDensity_withDensity_rnDeriv_left` / 引理 `rnDeriv_withDensity_withDensity_rnDeriv_left`

English:
lemma rnDeriv_withDensity_withDensity_rnDeriv_left
  statement: (μ ν : Measure α) [SigmaFinite μ] [SigmaFinite ν]
  proof: by
  conv_rhs => rw [μ.haveLebesgueDecomposition_add ν, add_comm, withDensity_add_measure]
  have : SigmaFinite ((μ.singularPart ν).withDensity f) :=
    SigmaFinite.withDensity_of_ne_top (ae_mono (Measure.singularPart_le _ _) hf_ne_top)
  have : SigmaFinite ((ν.withDensity (μ.rnDeriv ν)).withDensit

中文:
引理 rnDeriv_withDensity_withDensity_rnDeriv_left
  结论: (μ ν : 测度 α) [σ有限 μ] [σ有限 ν]
  证明: by
  conv_rhs => rw [μ.haveLebesgueDecomposition_add ν, add_comm, withDensity_add_measure]
  have : SigmaFinite ((μ.singularPart ν).withDensity f) :=
    SigmaFinite.withDensity_of_ne_top (ae_mono (Measure.singularPart_le _ _) hf_ne_top)
  have : SigmaFinite ((ν.withDensity (μ.rnDeriv ν)).withDensit

Depends on / 依赖: Measure, Measure.singularPart_le, Measure.withDensity_rnDeriv_le, SigmaFinite, SigmaFinite.withDensity_of_ne_top, add_comm, ae_mono, conv_rhs, haveLebesgueDecomposition_add, hf_ne_top, mutuallySingular_singularPart, rnDeriv, rnDeriv_add_of_mutuallySingular, singularPart, singularPart_le, withDensity, withDensity_add_measure, withDensity_of_ne_top, withDensity_rnDeriv_le
-/
lemma rnDeriv_withDensity_withDensity_rnDeriv_left (μ ν : Measure α) [SigmaFinite μ] [SigmaFinite ν]
    (hf_ne_top : forallᵐ x ∂μ, f x != ∞) :
    ((ν.withDensity (μ.rnDeriv ν)).withDensity f).rnDeriv ν =ᵐ[ν] (μ.withDensity f).rnDeriv ν := by
  conv_rhs => rw [μ.haveLebesgueDecomposition_add ν, add_comm, withDensity_add_measure]
  have : SigmaFinite ((μ.singularPart ν).withDensity f) :=
    SigmaFinite.withDensity_of_ne_top (ae_mono (Measure.singularPart_le _ _) hf_ne_top)
  have : SigmaFinite ((ν.withDensity (μ.rnDeriv ν)).withDensity f) :=
    SigmaFinite.withDensity_of_ne_top (ae_mono (Measure.withDensity_rnDeriv_le _ _) hf_ne_top)
  exact (rnDeriv_add_of_mutuallySingular _ _ _ (mutuallySingular_singularPart μ ν).withDensity).symm

/--
lemma `rnDeriv_withDensity_withDensity_rnDeriv_right` / 引理 `rnDeriv_withDensity_withDensity_rnDeriv_right`

English:
lemma rnDeriv_withDensity_withDensity_rnDeriv_right
  statement: (μ ν : Measure α) [SigmaFinite μ]
  proof: by
  conv_rhs => rw [μ.haveLebesgueDecomposition_add ν, add_comm]
  have hν_ac : ν ≪ ν.withDensity f := withDensity_absolutelyContinuous' hf hf_ne_zero
  refine hν_ac.ae_eq ?_
  have : SigmaFinite (ν.withDensity f) := SigmaFinite.withDensity_of_ne_top hf_ne_top
  refine (rnDeriv_add_of_mutuallySingu

中文:
引理 rnDeriv_withDensity_withDensity_rnDeriv_right
  结论: (μ ν : 测度 α) [σ有限 μ]
  证明: by
  conv_rhs => rw [μ.haveLebesgueDecomposition_add ν, add_comm]
  have hν_ac : ν ≪ ν.withDensity f := withDensity_absolutelyContinuous' hf hf_ne_zero
  refine hν_ac.ae_eq ?_
  have : SigmaFinite (ν.withDensity f) := SigmaFinite.withDensity_of_ne_top hf_ne_top
  refine (rnDeriv_add_of_mutuallySingu

Depends on / 依赖: SigmaFinite, SigmaFinite.withDensity_of_ne_top, _ac.ae_eq, add_comm, ae_eq, conv_rhs, haveLebesgueDecomposition_add, hf_ne_top, hf_ne_zero, mutuallySingular_singularPart, rnDeriv_add_of_mutuallySingular, symm.withDensity, withDensity, withDensity_absolutelyContinuous, withDensity_of_ne_top
-/
lemma rnDeriv_withDensity_withDensity_rnDeriv_right (μ ν : Measure α) [SigmaFinite μ]
    [SigmaFinite ν] (hf : AEMeasurable f ν) (hf_ne_zero : forallᵐ x ∂ν, f x != 0)
    (hf_ne_top : forallᵐ x ∂ν, f x != ∞) :
    (ν.withDensity (μ.rnDeriv ν)).rnDeriv (ν.withDensity f) =ᵐ[ν] μ.rnDeriv (ν.withDensity f) := by
  conv_rhs => rw [μ.haveLebesgueDecomposition_add ν, add_comm]
  have hν_ac : ν ≪ ν.withDensity f := withDensity_absolutelyContinuous' hf hf_ne_zero
  refine hν_ac.ae_eq ?_
  have : SigmaFinite (ν.withDensity f) := SigmaFinite.withDensity_of_ne_top hf_ne_top
  refine (rnDeriv_add_of_mutuallySingular _ _ _ ?_).symm
  exact ((mutuallySingular_singularPart μ ν).symm.withDensity).symm

/--
lemma `rnDeriv_withDensity_left_of_absolutelyContinuous` / 引理 `rnDeriv_withDensity_left_of_absolutelyContinuous`

English:
lemma rnDeriv_withDensity_left_of_absolutelyContinuous
  statement: {ν : Measure α} [SigmaFinite μ]
  proof: by
  refine (Measure.eq_rnDeriv₀ ?_ Measure.MutuallySingular.zero_left ?_).symm
  · exact hf.mul (Measure.measurable_rnDeriv _ _).aemeasurable
  · ext1 s hs
    rw [zero_add]; rw [withDensity_apply _ hs]; rw [withDensity_apply _ hs]
    conv_lhs => rw [← Measure.withDensity_rnDeriv_eq _ _ hμν]
    r

中文:
引理 rnDeriv_withDensity_left_of_absolutelyContinuous
  结论: {ν : 测度 α} [σ有限 μ]
  证明: by
  refine (Measure.eq_rnDeriv₀ ?_ Measure.MutuallySingular.zero_left ?_).symm
  · exact hf.mul (Measure.measurable_rnDeriv _ _).aemeasurable
  · ext1 s hs
    rw [zero_add]; rw [withDensity_apply _ hs]; rw [withDensity_apply _ hs]
    conv_lhs => rw [← Measure.withDensity_rnDeriv_eq _ _ hμν]
    r

Depends on / 依赖: Measure, Measure.MutuallySingular.zero_left, Measure.eq_rnDeriv, Measure.measurable, Measure.measurable_rnDeriv, Measure.rnDeriv_lt_top, Measure.withDensity_rnDeriv_eq, MutuallySingular, Pi.mul_apply, ae_restrict_of_ae, aemeasurable, conv_lhs, hf.mul, measurable, measurable_rnDeriv, mul_apply, mul_comm, rnDeriv_lt_top, withDensity_apply, withDensity_rnDeriv_eq
-/
lemma rnDeriv_withDensity_left_of_absolutelyContinuous {ν : Measure α} [SigmaFinite μ]
    [SigmaFinite ν] (hμν : μ ≪ ν) (hf : AEMeasurable f ν) :
    (μ.withDensity f).rnDeriv ν =ᵐ[ν] fun x => f x * μ.rnDeriv ν x := by
  refine (Measure.eq_rnDeriv₀ ?_ Measure.MutuallySingular.zero_left ?_).symm
  · exact hf.mul (Measure.measurable_rnDeriv _ _).aemeasurable
  · ext1 s hs
    rw [zero_add]; rw [withDensity_apply _ hs]; rw [withDensity_apply _ hs]
    conv_lhs => rw [← Measure.withDensity_rnDeriv_eq _ _ hμν]
    rw [setLIntegral_withDensity_eq_setLIntegral_mul_non_measurable₀ _ _ _ hs]
    · congr with x
      rw [mul_comm]
      simp only [Pi.mul_apply]
    · refine ae_restrict_of_ae ?_
      exact Measure.rnDeriv_lt_top _ _
    · exact (Measure.measurable_rnDeriv _ _).aemeasurable

/--
lemma `rnDeriv_withDensity_left` / 引理 `rnDeriv_withDensity_left`

English:
lemma rnDeriv_withDensity_left
  statement: {μ ν : Measure α} [SigmaFinite μ] [SigmaFinite ν]
  proof: by
  let μ' := ν.withDensity (μ.rnDeriv ν)
  have hμ'ν : μ' ≪ ν := withDensity_absolutelyContinuous _ _
  have h := rnDeriv_withDensity_left_of_absolutelyContinuous hμ'ν hfν
  have h1 : μ'.rnDeriv ν =ᵐ[ν] μ.rnDeriv ν :=
    Measure.rnDeriv_withDensity _ (Measure.measurable_rnDeriv _ _)
  have h2 : (

中文:
引理 rnDeriv_withDensity_left
  结论: {μ ν : 测度 α} [σ有限 μ] [σ有限 ν]
  证明: by
  let μ' := ν.withDensity (μ.rnDeriv ν)
  have hμ'ν : μ' ≪ ν := withDensity_absolutelyContinuous _ _
  have h := rnDeriv_withDensity_left_of_absolutelyContinuous hμ'ν hfν
  have h1 : μ'.rnDeriv ν =ᵐ[ν] μ.rnDeriv ν :=
    Measure.rnDeriv_withDensity _ (Measure.measurable_rnDeriv _ _)
  have h2 : (

Depends on / 依赖: Measure, Measure.measurable_rnDeriv, Measure.rnDeriv_withDensity, filter_upwards, hf_ne_top, measurable_rnDeriv, rnDeriv, rnDeriv_withDensity, rnDeriv_withDensity_left_of_absolutelyContinuous, rnDeriv_withDensity_withDensity_rnDeriv_left, withDensity, withDensity_absolutelyContinuous
-/
lemma rnDeriv_withDensity_left {μ ν : Measure α} [SigmaFinite μ] [SigmaFinite ν]
    (hfν : AEMeasurable f ν) (hf_ne_top : forallᵐ x ∂μ, f x != ∞) :
    (μ.withDensity f).rnDeriv ν =ᵐ[ν] fun x => f x * μ.rnDeriv ν x := by
  let μ' := ν.withDensity (μ.rnDeriv ν)
  have hμ'ν : μ' ≪ ν := withDensity_absolutelyContinuous _ _
  have h := rnDeriv_withDensity_left_of_absolutelyContinuous hμ'ν hfν
  have h1 : μ'.rnDeriv ν =ᵐ[ν] μ.rnDeriv ν :=
    Measure.rnDeriv_withDensity _ (Measure.measurable_rnDeriv _ _)
  have h2 : (μ'.withDensity f).rnDeriv ν =ᵐ[ν] (μ.withDensity f).rnDeriv ν := by
    exact rnDeriv_withDensity_withDensity_rnDeriv_left μ ν hf_ne_top
  filter_upwards [h, h1, h2] with x hx hx1 hx2
  rw [← hx2]; rw [hx]; rw [hx1]

/--
lemma `rnDeriv_withDensity_right_of_absolutelyContinuous` / 引理 `rnDeriv_withDensity_right_of_absolutelyContinuous`

English:
lemma rnDeriv_withDensity_right_of_absolutelyContinuous
  statement: {ν : Measure α}
  proof: by
  have : SigmaFinite (ν.withDensity f) := SigmaFinite.withDensity_of_ne_top hf_ne_top
  refine (withDensity_absolutelyContinuous' hf hf_ne_zero).ae_eq ?_
  refine (Measure.eq_rnDeriv₀ (ν := ν.withDensity f) ?_ Measure.MutuallySingular.zero_left ?_).symm
  · exact (hf.inv.mono_ac (withDensity_abso

中文:
引理 rnDeriv_withDensity_right_of_absolutelyContinuous
  结论: {ν : 测度 α}
  证明: by
  have : SigmaFinite (ν.withDensity f) := SigmaFinite.withDensity_of_ne_top hf_ne_top
  refine (withDensity_absolutelyContinuous' hf hf_ne_zero).ae_eq ?_
  refine (Measure.eq_rnDeriv₀ (ν := ν.withDensity f) ?_ Measure.MutuallySingular.zero_left ?_).symm
  · exact (hf.inv.mono_ac (withDensity_abso

Depends on / 依赖: Measure, Measure.MutuallySingular.zero_left, Measure.eq_rnDeriv, Measure.measurable_rnDeriv, Measure.withDensity_rnDeriv_eq, MutuallySingular, SigmaFinite, SigmaFinite.withDensity_of_ne_top, ae_eq, aemeasurable, conv_lhs, hf.inv.mono_ac, hf_ne_top, hf_ne_zero, measurable_rnDeriv, mono_ac, withDensity, withDensity_absolutelyContinuous, withDensity_apply, withDensity_of_ne_top
-/
lemma rnDeriv_withDensity_right_of_absolutelyContinuous {ν : Measure α}
    [HaveLebesgueDecomposition μ ν] [SigmaFinite ν] (hμν : μ ≪ ν) (hf : AEMeasurable f ν)
    (hf_ne_zero : forallᵐ x ∂ν, f x != 0) (hf_ne_top : forallᵐ x ∂ν, f x != ∞) :
    μ.rnDeriv (ν.withDensity f) =ᵐ[ν] fun x => (f x)⁻¹ * μ.rnDeriv ν x := by
  have : SigmaFinite (ν.withDensity f) := SigmaFinite.withDensity_of_ne_top hf_ne_top
  refine (withDensity_absolutelyContinuous' hf hf_ne_zero).ae_eq ?_
  refine (Measure.eq_rnDeriv₀ (ν := ν.withDensity f) ?_ Measure.MutuallySingular.zero_left ?_).symm
  · exact (hf.inv.mono_ac (withDensity_absolutelyContinuous _ _)).mul
      (Measure.measurable_rnDeriv _ _).aemeasurable
  · ext1 s hs
    conv_lhs => rw [← Measure.withDensity_rnDeriv_eq _ _ hμν]
    rw [zero_add]; rw [withDensity_apply _ hs]; rw [withDensity_apply _ hs]
    rw [setLIntegral_withDensity_eq_setLIntegral_mul_non_measurable₀ _ _ _ hs]
    · simp only [Pi.mul_apply]
      have : (fun a => f a * ((f a)⁻¹ * μ.rnDeriv ν a)) =ᵐ[ν] μ.rnDeriv ν := by
        filter_upwards [hf_ne_zero, hf_ne_top] with x hx1 hx2
        simp [← mul_assoc, ENNReal.mul_inv_cancel, hx1, hx2]
      rw [lintegral_congr_ae (ae_restrict_of_ae this)]
    · refine ae_restrict_of_ae ?_
      filter_upwards [hf_ne_top] with x hx using hx.lt_top
    · exact hf.restrict

/--
lemma `rnDeriv_withDensity_right` / 引理 `rnDeriv_withDensity_right`

English:
lemma rnDeriv_withDensity_right
  statement: (μ ν : Measure α) [SigmaFinite μ] [SigmaFinite ν]
  proof: by
  let μ' := ν.withDensity (μ.rnDeriv ν)
  have h₁ : μ'.rnDeriv (ν.withDensity f) =ᵐ[ν] μ.rnDeriv (ν.withDensity f) :=
    rnDeriv_withDensity_withDensity_rnDeriv_right μ ν hf hf_ne_zero hf_ne_top
  have h₂ : μ.rnDeriv ν =ᵐ[ν] μ'.rnDeriv ν :=
    (Measure.rnDeriv_withDensity _ (Measure.measurable_

中文:
引理 rnDeriv_withDensity_right
  结论: (μ ν : 测度 α) [σ有限 μ] [σ有限 ν]
  证明: by
  let μ' := ν.withDensity (μ.rnDeriv ν)
  have h₁ : μ'.rnDeriv (ν.withDensity f) =ᵐ[ν] μ.rnDeriv (ν.withDensity f) :=
    rnDeriv_withDensity_withDensity_rnDeriv_right μ ν hf hf_ne_zero hf_ne_top
  have h₂ : μ.rnDeriv ν =ᵐ[ν] μ'.rnDeriv ν :=
    (Measure.rnDeriv_withDensity _ (Measure.measurable_

Depends on / 依赖: Measure, Measure.measurable_rnDeriv, Measure.rnDeriv_withDensity, filter_upwards, hf_ne_top, hf_ne_zero, hx_eq, measurable_rnDeriv, rnDeriv, rnDeriv_withDensity, rnDeriv_withDensity_right_of_absolutelyContinuous, rnDeriv_withDensity_withDensity_rnDeriv_right, withDensity, withDensity_absolutelyContinuous
-/
lemma rnDeriv_withDensity_right (μ ν : Measure α) [SigmaFinite μ] [SigmaFinite ν]
    (hf : AEMeasurable f ν) (hf_ne_zero : forallᵐ x ∂ν, f x != 0) (hf_ne_top : forallᵐ x ∂ν, f x != ∞) :
    μ.rnDeriv (ν.withDensity f) =ᵐ[ν] fun x => (f x)⁻¹ * μ.rnDeriv ν x := by
  let μ' := ν.withDensity (μ.rnDeriv ν)
  have h₁ : μ'.rnDeriv (ν.withDensity f) =ᵐ[ν] μ.rnDeriv (ν.withDensity f) :=
    rnDeriv_withDensity_withDensity_rnDeriv_right μ ν hf hf_ne_zero hf_ne_top
  have h₂ : μ.rnDeriv ν =ᵐ[ν] μ'.rnDeriv ν :=
    (Measure.rnDeriv_withDensity _ (Measure.measurable_rnDeriv _ _)).symm
  have hμ' := rnDeriv_withDensity_right_of_absolutelyContinuous
    (withDensity_absolutelyContinuous ν (μ.rnDeriv ν)) hf hf_ne_zero hf_ne_top
  filter_upwards [h₁, h₂, hμ'] with x hx₁ hx₂ hx_eq
  rw [← hx₁]; rw [hx₂]; rw [hx_eq]

end rnDeriv_withDensity_leftRight

/--
lemma `rnDeriv_eq_zero_of_mutuallySingular` / 引理 `rnDeriv_eq_zero_of_mutuallySingular`

English:
lemma rnDeriv_eq_zero_of_mutuallySingular
  statement: {ν' : Measure α} [HaveLebesgueDecomposition μ ν']
  proof: by
  let t := h.nullSet
  have ht : MeasurableSet t := h.measurableSet_nullSet
  refine ae_of_ae_restrict_of_ae_restrict_compl t ?_ (by simp [t])
  change μ.rnDeriv ν' =ᵐ[ν.restrict t] 0
  have : μ.rnDeriv ν' =ᵐ[ν.restrict t] (μ.restrict t).rnDeriv ν' := by
    have h : (μ.restrict t).rnDeriv ν' =ᵐ[

中文:
引理 rnDeriv_eq_zero_of_mutuallySingular
  结论: {ν' : 测度 α} [有Lebesgue分解 μ ν']
  证明: by
  let t := h.nullSet
  have ht : MeasurableSet t := h.measurableSet_nullSet
  refine ae_of_ae_restrict_of_ae_restrict_compl t ?_ (by simp [t])
  change μ.rnDeriv ν' =ᵐ[ν.restrict t] 0
  have : μ.rnDeriv ν' =ᵐ[ν.restrict t] (μ.restrict t).rnDeriv ν' := by
    have h : (μ.restrict t).rnDeriv ν' =ᵐ[

Depends on / 依赖: EventuallyEq, Filter, Filter.EventuallyEq, MeasurableSet, Set.indicator_of_mem, ae_le, ae_of_ae_restrict_of_ae_restrict_compl, ae_restrict_iff, filter_upwards, h.measurableSet_nullSet, h.nullSet, indicator, indicator_of_mem, measurableSet_nullSet, nullSet, restrict, rnDeriv, rnDeriv_restrict, t.indicator, this.trans
-/
lemma rnDeriv_eq_zero_of_mutuallySingular {ν' : Measure α} [HaveLebesgueDecomposition μ ν']
    [SigmaFinite ν'] (h : μ ⟂ₘ ν) (hνν' : ν ≪ ν') :
    μ.rnDeriv ν' =ᵐ[ν] 0 := by
  let t := h.nullSet
  have ht : MeasurableSet t := h.measurableSet_nullSet
  refine ae_of_ae_restrict_of_ae_restrict_compl t ?_ (by simp [t])
  change μ.rnDeriv ν' =ᵐ[ν.restrict t] 0
  have : μ.rnDeriv ν' =ᵐ[ν.restrict t] (μ.restrict t).rnDeriv ν' := by
    have h : (μ.restrict t).rnDeriv ν' =ᵐ[ν] t.indicator (μ.rnDeriv ν') :=
      hνν'.ae_le (rnDeriv_restrict μ ν' ht)
    rw [Filter.EventuallyEq]; rw [ae_restrict_iff' ht]
    filter_upwards [h] with x hx hxt
    rw [hx]; rw [Set.indicator_of_mem hxt]
  refine this.trans ?_
  simp only [t, MutuallySingular.restrict_nullSet]
  suffices (0 : Measure α).rnDeriv ν' =ᵐ[ν'] 0 by
    have h_ac' : ν.restrict t ≪ ν' := restrict_le_self.absolutelyContinuous.trans hνν'
    exact h_ac'.ae_le this
  exact rnDeriv_zero _

variable (μ ν) in
/--
lemma `rnDeriv_eq_zero_ae_singularPart` / 引理 `rnDeriv_eq_zero_ae_singularPart`

English:
lemma rnDeriv_eq_zero_ae_singularPart
  given: [SigmaFinite μ] [SigmaFinite ν]
  proof: by
  refine rnDeriv_eq_zero_of_mutuallySingular (mutuallySingular_singularPart ν μ).symm ?_
  exact (Measure.singularPart_le _ _).absolutelyContinuous

中文:
引理 rnDeriv_eq_zero_ae_singularPart
  条件: [σ有限 μ] [σ有限 ν]
  证明: by
  refine rnDeriv_eq_zero_of_mutuallySingular (mutuallySingular_singularPart ν μ).symm ?_
  exact (Measure.singularPart_le _ _).absolutelyContinuous

Depends on / 依赖: Measure, Measure.singularPart_le, absolutelyContinuous, mutuallySingular_singularPart, rnDeriv_eq_zero_of_mutuallySingular, singularPart_le
-/
lemma rnDeriv_eq_zero_ae_singularPart [SigmaFinite μ] [SigmaFinite ν] :
    forallᵐ x ∂(ν.singularPart μ), μ.rnDeriv ν x = 0 := by
  refine rnDeriv_eq_zero_of_mutuallySingular (mutuallySingular_singularPart ν μ).symm ?_
  exact (Measure.singularPart_le _ _).absolutelyContinuous

/--
lemma `rnDeriv_add_right_of_absolutelyContinuous_of_mutuallySingular` / 引理 `rnDeriv_add_right_of_absolutelyContinuous_of_mutuallySingular`

English:
lemma rnDeriv_add_right_of_absolutelyContinuous_of_mutuallySingular
  statement: {ν' : Measure α}
  proof: by
  let t := hνν'.nullSet
  have ht : MeasurableSet t := hνν'.measurableSet_nullSet
  refine ae_of_ae_restrict_of_ae_restrict_compl t (by simp [t]) ?_
  change μ.rnDeriv (ν + ν') =ᵐ[ν.restrict tᶜ] μ.rnDeriv ν
  rw [← withDensity_eq_iff_of_sigmaFinite (μ := ν.restrict tᶜ)
    (Measure.measurable_rnD

中文:
引理 rnDeriv_add_right_of_absolutelyContinuous_of_mutuallySingular
  结论: {ν' : 测度 α}
  证明: by
  let t := hνν'.nullSet
  have ht : MeasurableSet t := hνν'.measurableSet_nullSet
  refine ae_of_ae_restrict_of_ae_restrict_compl t (by simp [t]) ?_
  change μ.rnDeriv (ν + ν') =ᵐ[ν.restrict tᶜ] μ.rnDeriv ν
  rw [← withDensity_eq_iff_of_sigmaFinite (μ := ν.restrict tᶜ)
    (Measure.measurable_rnD

Depends on / 依赖: MeasurableSet, Measure, Measure.measurable_rnDeriv, ae_of_ae_restrict_of_ae_restrict_compl, aemeasurable, measurableSet_nullSet, measurable_rnDeriv, nullSet, restrict, rnDeriv, withDensity, withDensity_eq_iff_of_sigmaFinite
-/
lemma rnDeriv_add_right_of_absolutelyContinuous_of_mutuallySingular {ν' : Measure α}
    [HaveLebesgueDecomposition μ ν] [HaveLebesgueDecomposition μ (ν + ν')] [SigmaFinite ν]
    (hμν : μ ≪ ν) (hνν' : ν ⟂ₘ ν') :
    μ.rnDeriv (ν + ν') =ᵐ[ν] μ.rnDeriv ν := by
  let t := hνν'.nullSet
  have ht : MeasurableSet t := hνν'.measurableSet_nullSet
  refine ae_of_ae_restrict_of_ae_restrict_compl t (by simp [t]) ?_
  change μ.rnDeriv (ν + ν') =ᵐ[ν.restrict tᶜ] μ.rnDeriv ν
  rw [← withDensity_eq_iff_of_sigmaFinite (μ := ν.restrict tᶜ)
    (Measure.measurable_rnDeriv _ _).aemeasurable (Measure.measurable_rnDeriv _ _).aemeasurable]
  have : (ν.restrict tᶜ).withDensity (μ.rnDeriv (ν + ν'))
      = ((ν + ν').restrict tᶜ).withDensity (μ.rnDeriv (ν + ν')) := by simp [t]
  rw [this]; rw [← restrict_withDensity ht.compl]; rw [← restrict_withDensity ht.compl]; rw [Measure.withDensity_rnDeriv_eq _ _ (hμν.add_right ν')]; rw [Measure.withDensity_rnDeriv_eq _ _ hμν]

/--
lemma `rnDeriv_add_right_of_mutuallySingular'` / 引理 `rnDeriv_add_right_of_mutuallySingular'`

English:
lemma rnDeriv_add_right_of_mutuallySingular'
  statement: {ν' : Measure α}
  proof: by
  have h_ac : ν ≪ ν + ν' := Measure.AbsolutelyContinuous.rfl.add_right _
  rw [haveLebesgueDecomposition_add μ ν]
  have h₁ := rnDeriv_add' (μ.singularPart ν) (ν.withDensity (μ.rnDeriv ν)) (ν + ν')
  have h₂ := rnDeriv_add' (μ.singularPart ν) (ν.withDensity (μ.rnDeriv ν)) ν
  refine (Filter.Event

中文:
引理 rnDeriv_add_right_of_mutuallySingular'
  结论: {ν' : 测度 α}
  证明: by
  have h_ac : ν ≪ ν + ν' := Measure.AbsolutelyContinuous.rfl.add_right _
  rw [haveLebesgueDecomposition_add μ ν]
  have h₁ := rnDeriv_add' (μ.singularPart ν) (ν.withDensity (μ.rnDeriv ν)) (ν + ν')
  have h₂ := rnDeriv_add' (μ.singularPart ν) (ν.withDensity (μ.rnDeriv ν)) ν
  refine (Filter.Event

Depends on / 依赖: AbsolutelyContinuous, EventuallyEq, Filter, Filter.EventuallyEq.trans, Measure, Measure.AbsolutelyContinuous.rfl.add_right, add_right, ae_le, h_ac, h_ac.ae_le, haveLebesgueDecomposition_add, rnDeriv, rnDeriv_add, rnDeriv_add_right_of_absolutelyContinuous_of_mutuallySingular, singularPart, withDensity, withDensity_absolutelyContinuous
-/
lemma rnDeriv_add_right_of_mutuallySingular' {ν' : Measure α}
    [SigmaFinite μ] [SigmaFinite ν] [SigmaFinite ν']
    (hμν' : μ ⟂ₘ ν') (hνν' : ν ⟂ₘ ν') :
    μ.rnDeriv (ν + ν') =ᵐ[ν] μ.rnDeriv ν := by
  have h_ac : ν ≪ ν + ν' := Measure.AbsolutelyContinuous.rfl.add_right _
  rw [haveLebesgueDecomposition_add μ ν]
  have h₁ := rnDeriv_add' (μ.singularPart ν) (ν.withDensity (μ.rnDeriv ν)) (ν + ν')
  have h₂ := rnDeriv_add' (μ.singularPart ν) (ν.withDensity (μ.rnDeriv ν)) ν
  refine (Filter.EventuallyEq.trans (h_ac.ae_le h₁) ?_).trans h₂.symm
  have h₃ := rnDeriv_add_right_of_absolutelyContinuous_of_mutuallySingular
    (withDensity_absolutelyContinuous ν (μ.rnDeriv ν)) hνν'
  have h₄ : (μ.singularPart ν).rnDeriv (ν + ν') =ᵐ[ν] 0 := by
    refine h_ac.ae_eq ?_
    simp only [rnDeriv_eq_zero, MutuallySingular.add_right_iff]
    exact ⟨mutuallySingular_singularPart μ ν, hμν'.singularPart ν⟩
  have h₅ : (μ.singularPart ν).rnDeriv ν =ᵐ[ν] 0 := rnDeriv_singularPart μ ν
  filter_upwards [h₃, h₄, h₅] with x hx₃ hx₄ hx₅
  simp only [Pi.add_apply]
  rw [hx₃]; rw [hx₄]; rw [hx₅]

/--
lemma `rnDeriv_add_right_of_mutuallySingular` / 引理 `rnDeriv_add_right_of_mutuallySingular`

English:
lemma rnDeriv_add_right_of_mutuallySingular
  statement: {ν' : Measure α}
  proof: by
  have h_ac : ν ≪ ν + ν' := Measure.AbsolutelyContinuous.rfl.add_right _
  rw [haveLebesgueDecomposition_add μ ν']
  have h₁ := rnDeriv_add' (μ.singularPart ν') (ν'.withDensity (μ.rnDeriv ν')) (ν + ν')
  have h₂ := rnDeriv_add' (μ.singularPart ν') (ν'.withDensity (μ.rnDeriv ν')) ν
  refine (Filte

中文:
引理 rnDeriv_add_right_of_mutuallySingular
  结论: {ν' : 测度 α}
  证明: by
  have h_ac : ν ≪ ν + ν' := Measure.AbsolutelyContinuous.rfl.add_right _
  rw [haveLebesgueDecomposition_add μ ν']
  have h₁ := rnDeriv_add' (μ.singularPart ν') (ν'.withDensity (μ.rnDeriv ν')) (ν + ν')
  have h₂ := rnDeriv_add' (μ.singularPart ν') (ν'.withDensity (μ.rnDeriv ν')) ν
  refine (Filte

Depends on / 依赖: AbsolutelyContinuous, EventuallyEq, Filter, Filter.EventuallyEq.trans, Measure, Measure.AbsolutelyContinuous.rfl.add_right, add_right, ae_le, h_ac, h_ac.ae_le, haveLebesgueDecomposition_add, rnDeriv, rnDeriv_add, rnDeriv_add_right_of_mutuallySingular, singularPart, withDensity
-/
lemma rnDeriv_add_right_of_mutuallySingular {ν' : Measure α}
    [SigmaFinite μ] [SigmaFinite ν] [SigmaFinite ν'] (hνν' : ν ⟂ₘ ν') :
    μ.rnDeriv (ν + ν') =ᵐ[ν] μ.rnDeriv ν := by
  have h_ac : ν ≪ ν + ν' := Measure.AbsolutelyContinuous.rfl.add_right _
  rw [haveLebesgueDecomposition_add μ ν']
  have h₁ := rnDeriv_add' (μ.singularPart ν') (ν'.withDensity (μ.rnDeriv ν')) (ν + ν')
  have h₂ := rnDeriv_add' (μ.singularPart ν') (ν'.withDensity (μ.rnDeriv ν')) ν
  refine (Filter.EventuallyEq.trans (h_ac.ae_le h₁) ?_).trans h₂.symm
  have h₃ := rnDeriv_add_right_of_mutuallySingular' (?_ : μ.singularPart ν' ⟂ₘ ν') hνν'
  · have h₄ : (ν'.withDensity (rnDeriv μ ν')).rnDeriv (ν + ν') =ᵐ[ν] 0 := by
      refine rnDeriv_eq_zero_of_mutuallySingular ?_ h_ac
      exact hνν'.symm.withDensity
    have h₅ : (ν'.withDensity (rnDeriv μ ν')).rnDeriv ν =ᵐ[ν] 0 := by
      rw [rnDeriv_eq_zero]
      exact hνν'.symm.withDensity
    filter_upwards [h₃, h₄, h₅] with x hx₃ hx₄ hx₅
    rw [Pi.add_apply]; rw [Pi.add_apply]; rw [hx₃]; rw [hx₄]; rw [hx₅]
  exact mutuallySingular_singularPart μ ν'

/--
lemma `rnDeriv_withDensity_rnDeriv` / 引理 `rnDeriv_withDensity_rnDeriv`

English:
lemma rnDeriv_withDensity_rnDeriv
  given: [SigmaFinite μ] [SigmaFinite ν] (hμν : μ ≪ ν)
  proof: by
  conv_rhs => rw [ν.haveLebesgueDecomposition_add μ, add_comm]
  refine (absolutelyContinuous_withDensity_rnDeriv hμν).ae_eq ?_
  exact (rnDeriv_add_right_of_mutuallySingular
    (Measure.mutuallySingular_singularPart ν μ).symm.withDensity).symm

中文:
引理 rnDeriv_withDensity_rnDeriv
  条件: [σ有限 μ] [σ有限 ν] (hμν : μ ≪ ν)
  证明: by
  conv_rhs => rw [ν.haveLebesgueDecomposition_add μ, add_comm]
  refine (absolutelyContinuous_withDensity_rnDeriv hμν).ae_eq ?_
  exact (rnDeriv_add_right_of_mutuallySingular
    (Measure.mutuallySingular_singularPart ν μ).symm.withDensity).symm

Depends on / 依赖: Measure, Measure.mutuallySingular_singularPart, absolutelyContinuous_withDensity_rnDeriv, add_comm, ae_eq, conv_rhs, haveLebesgueDecomposition_add, mutuallySingular_singularPart, rnDeriv_add_right_of_mutuallySingular, symm.withDensity, withDensity
-/
lemma rnDeriv_withDensity_rnDeriv [SigmaFinite μ] [SigmaFinite ν] (hμν : μ ≪ ν) :
    μ.rnDeriv (μ.withDensity (ν.rnDeriv μ)) =ᵐ[μ] μ.rnDeriv ν := by
  conv_rhs => rw [ν.haveLebesgueDecomposition_add μ, add_comm]
  refine (absolutelyContinuous_withDensity_rnDeriv hμν).ae_eq ?_
  exact (rnDeriv_add_right_of_mutuallySingular
    (Measure.mutuallySingular_singularPart ν μ).symm.withDensity).symm

/--
lemma `inv_rnDeriv_aux` / 引理 `inv_rnDeriv_aux`

English:
lemma inv_rnDeriv_aux
  statement: [HaveLebesgueDecomposition μ ν] [HaveLebesgueDecomposition ν μ]
  proof: by
  suffices μ.withDensity (μ.rnDeriv ν)⁻¹ = μ.withDensity (ν.rnDeriv μ) by
    calc (μ.rnDeriv ν)⁻¹ =ᵐ[μ] (μ.withDensity (μ.rnDeriv ν)⁻¹).rnDeriv μ :=
          (rnDeriv_withDensity _ (measurable_rnDeriv _ _).inv).symm
    _ = (μ.withDensity (ν.rnDeriv μ)).rnDeriv μ := by rw [this]
    _ =ᵐ[μ] ν.r

中文:
引理 inv_rnDeriv_aux
  结论: [有Lebesgue分解 μ ν] [有Lebesgue分解 ν μ]
  证明: by
  suffices μ.withDensity (μ.rnDeriv ν)⁻¹ = μ.withDensity (ν.rnDeriv μ) by
    calc (μ.rnDeriv ν)⁻¹ =ᵐ[μ] (μ.withDensity (μ.rnDeriv ν)⁻¹).rnDeriv μ :=
          (rnDeriv_withDensity _ (measurable_rnDeriv _ _).inv).symm
    _ = (μ.withDensity (ν.rnDeriv μ)).rnDeriv μ := by rw [this]
    _ =ᵐ[μ] ν.r

Depends on / 依赖: measurable_rnDeriv, rnDeriv, rnDeriv_withDensity, withDensity, withDensity_rnDeriv_eq
-/
lemma inv_rnDeriv_aux [HaveLebesgueDecomposition μ ν] [HaveLebesgueDecomposition ν μ]
    [SigmaFinite μ] (hμν : μ ≪ ν) (hνμ : ν ≪ μ) :
    (μ.rnDeriv ν)⁻¹ =ᵐ[μ] ν.rnDeriv μ := by
  suffices μ.withDensity (μ.rnDeriv ν)⁻¹ = μ.withDensity (ν.rnDeriv μ) by
    calc (μ.rnDeriv ν)⁻¹ =ᵐ[μ] (μ.withDensity (μ.rnDeriv ν)⁻¹).rnDeriv μ :=
          (rnDeriv_withDensity _ (measurable_rnDeriv _ _).inv).symm
    _ = (μ.withDensity (ν.rnDeriv μ)).rnDeriv μ := by rw [this]
    _ =ᵐ[μ] ν.rnDeriv μ := rnDeriv_withDensity _ (measurable_rnDeriv _ _)
  rw [withDensity_rnDeriv_eq _ _ hνμ]; rw [← withDensity_rnDeriv_eq _ _ hμν]
  conv in ((ν.withDensity (μ.rnDeriv ν)).rnDeriv ν)⁻¹ => rw [withDensity_rnDeriv_eq _ _ hμν]
  change (ν.withDensity (μ.rnDeriv ν)).withDensity (fun x => (μ.rnDeriv ν x)⁻¹) = ν
  rw [withDensity_inv_same (measurable_rnDeriv _ _)
    (by filter_upwards [hνμ.ae_le (rnDeriv_pos hμν)] with x hx using hx.ne')
    (rnDeriv_ne_top _ _)]

/--
lemma `inv_rnDeriv` / 引理 `inv_rnDeriv`

English:
lemma inv_rnDeriv
  given: [SigmaFinite μ] [SigmaFinite ν] (hμν : μ ≪ ν)
  proof: by
  suffices (μ.rnDeriv ν)⁻¹ =ᵐ[μ] (μ.rnDeriv (μ.withDensity (ν.rnDeriv μ)))⁻¹
      ∧ ν.rnDeriv μ =ᵐ[μ] (μ.withDensity (ν.rnDeriv μ)).rnDeriv μ by
    refine (this.1.trans (Filter.EventuallyEq.trans ?_ this.2.symm))
    exact Measure.inv_rnDeriv_aux (absolutelyContinuous_withDensity_rnDeriv hμν)
 

中文:
引理 inv_rnDeriv
  条件: [σ有限 μ] [σ有限 ν] (hμν : μ ≪ ν)
  证明: by
  suffices (μ.rnDeriv ν)⁻¹ =ᵐ[μ] (μ.rnDeriv (μ.withDensity (ν.rnDeriv μ)))⁻¹
      ∧ ν.rnDeriv μ =ᵐ[μ] (μ.withDensity (ν.rnDeriv μ)).rnDeriv μ by
    refine (this.1.trans (Filter.EventuallyEq.trans ?_ this.2.symm))
    exact Measure.inv_rnDeriv_aux (absolutelyContinuous_withDensity_rnDeriv hμν)
 

Depends on / 依赖: EventuallyEq, Filter, Filter.EventuallyEq.trans, Measure, Measure.inv_rnDeriv_aux, Measure.measurabl, Measure.rnDeriv_withDensity, Pi.inv_apply, absolutelyContinuous_withDensity_rnDeriv, filter_upwards, hx.symm, inv_apply, inv_inj, inv_rnDeriv_aux, measurabl, rnDeriv, rnDeriv_withDensity, rnDeriv_withDensity_rnDeriv, withDensity, withDensity_absolutelyContinuous
-/
lemma inv_rnDeriv [SigmaFinite μ] [SigmaFinite ν] (hμν : μ ≪ ν) :
    (μ.rnDeriv ν)⁻¹ =ᵐ[μ] ν.rnDeriv μ := by
  suffices (μ.rnDeriv ν)⁻¹ =ᵐ[μ] (μ.rnDeriv (μ.withDensity (ν.rnDeriv μ)))⁻¹
      ∧ ν.rnDeriv μ =ᵐ[μ] (μ.withDensity (ν.rnDeriv μ)).rnDeriv μ by
    refine (this.1.trans (Filter.EventuallyEq.trans ?_ this.2.symm))
    exact Measure.inv_rnDeriv_aux (absolutelyContinuous_withDensity_rnDeriv hμν)
      (withDensity_absolutelyContinuous _ _)
  constructor
  · filter_upwards [rnDeriv_withDensity_rnDeriv hμν] with x hx
    simp only [Pi.inv_apply, inv_inj]
    exact hx.symm
  · exact (Measure.rnDeriv_withDensity μ (Measure.measurable_rnDeriv ν μ)).symm

/--
lemma `inv_rnDeriv'` / 引理 `inv_rnDeriv'`

English:
lemma inv_rnDeriv'
  given: [SigmaFinite μ] [SigmaFinite ν] (hμν : μ ≪ ν)
  proof: by
  filter_upwards [inv_rnDeriv hμν] with x hx; simp only [Pi.inv_apply, ← hx, inv_inv]

中文:
引理 inv_rnDeriv'
  条件: [σ有限 μ] [σ有限 ν] (hμν : μ ≪ ν)
  证明: by
  filter_upwards [inv_rnDeriv hμν] with x hx; simp only [Pi.inv_apply, ← hx, inv_inv]

Depends on / 依赖: Pi.inv_apply, filter_upwards, inv_apply, inv_inv, inv_rnDeriv
-/
lemma inv_rnDeriv' [SigmaFinite μ] [SigmaFinite ν] (hμν : μ ≪ ν) :
    (ν.rnDeriv μ)⁻¹ =ᵐ[μ] μ.rnDeriv ν := by
  filter_upwards [inv_rnDeriv hμν] with x hx; simp only [Pi.inv_apply, ← hx, inv_inv]

variable (ν) in
/--
lemma `ae_rnDeriv_ne_zero_imp_of_ae` / 引理 `ae_rnDeriv_ne_zero_imp_of_ae`

English:
lemma ae_rnDeriv_ne_zero_imp_of_ae
  statement: [SigmaFinite μ] [SigmaFinite ν] {p : α -> Prop}
  proof: by
  rw [ν.haveLebesgueDecomposition_add μ]; rw [ae_add_measure_iff]
  constructor
  · rw [← ν.haveLebesgueDecomposition_add μ]
    have : forallᵐ x ∂(ν.singularPart μ), μ.rnDeriv ν x = 0 := μ.rnDeriv_eq_zero_ae_singularPart ν
    filter_upwards [this] with x hx h_absurd using absurd hx h_absurd
  ·

中文:
引理 ae_rnDeriv_ne_zero_imp_of_ae
  结论: [σ有限 μ] [σ有限 ν] {p : α -> 命题}
  证明: by
  rw [ν.haveLebesgueDecomposition_add μ]; rw [ae_add_measure_iff]
  constructor
  · rw [← ν.haveLebesgueDecomposition_add μ]
    have : forallᵐ x ∂(ν.singularPart μ), μ.rnDeriv ν x = 0 := μ.rnDeriv_eq_zero_ae_singularPart ν
    filter_upwards [this] with x hx h_absurd using absurd hx h_absurd
  ·

Depends on / 依赖: absurd, ae_add_measure_iff, filter_upwards, h_absurd, h_ac, haveLebesgueDecomposition_add, rnDeriv, rnDeriv_eq_zero_ae_singularPart, singularPart, withDensity, withDensity_absolutelyContinuous
-/
lemma ae_rnDeriv_ne_zero_imp_of_ae [SigmaFinite μ] [SigmaFinite ν] {p : α -> Prop}
    (h : forallᵐ a ∂μ, p a) :
    forallᵐ a ∂ν, μ.rnDeriv ν a != 0 -> p a := by
  rw [ν.haveLebesgueDecomposition_add μ]; rw [ae_add_measure_iff]
  constructor
  · rw [← ν.haveLebesgueDecomposition_add μ]
    have : forallᵐ x ∂(ν.singularPart μ), μ.rnDeriv ν x = 0 := μ.rnDeriv_eq_zero_ae_singularPart ν
    filter_upwards [this] with x hx h_absurd using absurd hx h_absurd
  · have h_ac : μ.withDensity (ν.rnDeriv μ) ≪ μ := withDensity_absolutelyContinuous _ _
    rw [← ν.haveLebesgueDecomposition_add μ]
    suffices forallᵐx ∂μ, μ.rnDeriv ν x != 0 -> p x from h_ac this
    filter_upwards [h] with _ h _ using h

section integral

/--
lemma `setLIntegral_rnDeriv_le` / 引理 `setLIntegral_rnDeriv_le`

English:
lemma setLIntegral_rnDeriv_le
  given: (s : Set α)
  proof: (withDensity_apply_le _ _).trans (Measure.le_iff'.1 (withDensity_rnDeriv_le μ ν) s)

中文:
引理 setL整数egral_rnDeriv_le
  条件: (s : 集合 α)
  证明: (withDensity_apply_le _ _).trans (Measure.le_iff'.1 (withDensity_rnDeriv_le μ ν) s)

Depends on / 依赖: Measure, Measure.le_iff, le_iff, withDensity_apply_le, withDensity_rnDeriv_le
-/
lemma setLIntegral_rnDeriv_le (s : Set α) :
    ∫⁻ x in s, μ.rnDeriv ν x ∂ν <= μ s :=
  (withDensity_apply_le _ _).trans (Measure.le_iff'.1 (withDensity_rnDeriv_le μ ν) s)

/--
lemma `lintegral_rnDeriv_le` / 引理 `lintegral_rnDeriv_le`

English:
lemma lintegral_rnDeriv_le
  statement: ∫⁻ x, μ.rnDeriv ν x ∂ν <= μ Set.univ
  proof: (setLIntegral_univ _).symm ▸ Measure.setLIntegral_rnDeriv_le Set.univ

中文:
引理 lintegral_rnDeriv_le
  结论: ∫⁻ x, μ.rnDeriv ν x ∂ν <= μ 集合.univ
  证明: (setLIntegral_univ _).symm ▸ Measure.setLIntegral_rnDeriv_le Set.univ

Depends on / 依赖: Measure, Measure.setLIntegral_rnDeriv_le, Set.univ, setLIntegral_rnDeriv_le, setLIntegral_univ
-/
lemma lintegral_rnDeriv_le : ∫⁻ x, μ.rnDeriv ν x ∂ν <= μ Set.univ :=
  (setLIntegral_univ _).symm ▸ Measure.setLIntegral_rnDeriv_le Set.univ

/--
lemma `setLIntegral_rnDeriv'` / 引理 `setLIntegral_rnDeriv'`

English:
lemma setLIntegral_rnDeriv'
  statement: [HaveLebesgueDecomposition μ ν] (hμν : μ ≪ ν) {s : Set α}
  proof: by
  rw [← withDensity_apply _ hs]; rw [Measure.withDensity_rnDeriv_eq _ _ hμν]

中文:
引理 setL整数egral_rnDeriv'
  结论: [有Lebesgue分解 μ ν] (hμν : μ ≪ ν) {s : 集合 α}
  证明: by
  rw [← withDensity_apply _ hs]; rw [Measure.withDensity_rnDeriv_eq _ _ hμν]

Depends on / 依赖: Measure, Measure.withDensity_rnDeriv_eq, withDensity_apply, withDensity_rnDeriv_eq
-/
lemma setLIntegral_rnDeriv' [HaveLebesgueDecomposition μ ν] (hμν : μ ≪ ν) {s : Set α}
    (hs : MeasurableSet s) :
    ∫⁻ x in s, μ.rnDeriv ν x ∂ν = μ s := by
  rw [← withDensity_apply _ hs]; rw [Measure.withDensity_rnDeriv_eq _ _ hμν]

/--
lemma `setLIntegral_rnDeriv` / 引理 `setLIntegral_rnDeriv`

English:
lemma setLIntegral_rnDeriv
  statement: [HaveLebesgueDecomposition μ ν] [SFinite ν]
  proof: by
  rw [← withDensity_apply' _ s]; rw [Measure.withDensity_rnDeriv_eq _ _ hμν]

中文:
引理 setL整数egral_rnDeriv
  结论: [有Lebesgue分解 μ ν] [SFinite ν]
  证明: by
  rw [← withDensity_apply' _ s]; rw [Measure.withDensity_rnDeriv_eq _ _ hμν]

Depends on / 依赖: Measure, Measure.withDensity_rnDeriv_eq, withDensity_apply, withDensity_rnDeriv_eq
-/
lemma setLIntegral_rnDeriv [HaveLebesgueDecomposition μ ν] [SFinite ν]
    (hμν : μ ≪ ν) (s : Set α) :
    ∫⁻ x in s, μ.rnDeriv ν x ∂ν = μ s := by
  rw [← withDensity_apply' _ s]; rw [Measure.withDensity_rnDeriv_eq _ _ hμν]

/--
lemma `lintegral_rnDeriv` / 引理 `lintegral_rnDeriv`

English:
lemma lintegral_rnDeriv
  given: [HaveLebesgueDecomposition μ ν] (hμν : μ ≪ ν)
  proof: by
  rw [← setLIntegral_univ]; rw [setLIntegral_rnDeriv' hμν MeasurableSet.univ]

中文:
引理 lintegral_rnDeriv
  条件: [有Lebesgue分解 μ ν] (hμν : μ ≪ ν)
  证明: by
  rw [← setLIntegral_univ]; rw [setLIntegral_rnDeriv' hμν MeasurableSet.univ]

Depends on / 依赖: MeasurableSet, MeasurableSet.univ, setLIntegral_rnDeriv, setLIntegral_univ
-/
lemma lintegral_rnDeriv [HaveLebesgueDecomposition μ ν] (hμν : μ ≪ ν) :
    ∫⁻ x, μ.rnDeriv ν x ∂ν = μ Set.univ := by
  rw [← setLIntegral_univ]; rw [setLIntegral_rnDeriv' hμν MeasurableSet.univ]

/--
lemma `integrableOn_toReal_rnDeriv` / 引理 `integrableOn_toReal_rnDeriv`

English:
lemma integrableOn_toReal_rnDeriv
  given: {s : Set α} (hμs : μ s != ∞)
  proof: by
  refine integrable_toReal_of_lintegral_ne_top (Measure.measurable_rnDeriv _ _).aemeasurable ?_
  exact ((setLIntegral_rnDeriv_le _).trans_lt hμs.lt_top).ne

中文:
引理 integrableOn_to实数_rnDeriv
  条件: {s : 集合 α} (hμs : μ s != ∞)
  证明: by
  refine integrable_toReal_of_lintegral_ne_top (Measure.measurable_rnDeriv _ _).aemeasurable ?_
  exact ((setLIntegral_rnDeriv_le _).trans_lt hμs.lt_top).ne

Depends on / 依赖: Measure, Measure.measurable_rnDeriv, aemeasurable, integrable_toReal_of_lintegral_ne_top, lt_top, measurable_rnDeriv, s.lt_top, setLIntegral_rnDeriv_le, trans_lt
-/
lemma integrableOn_toReal_rnDeriv {s : Set α} (hμs : μ s != ∞) :
    IntegrableOn (fun x => (μ.rnDeriv ν x).toReal) s ν := by
  refine integrable_toReal_of_lintegral_ne_top (Measure.measurable_rnDeriv _ _).aemeasurable ?_
  exact ((setLIntegral_rnDeriv_le _).trans_lt hμs.lt_top).ne

/--
lemma `setIntegral_toReal_rnDeriv_eq_withDensity'` / 引理 `setIntegral_toReal_rnDeriv_eq_withDensity'`

English:
lemma setIntegral_toReal_rnDeriv_eq_withDensity'
  statement: [SigmaFinite μ]
  proof: by
  rw [integral_toReal (Measure.measurable_rnDeriv _ _).aemeasurable]; rw [measureReal_def]
  · rw [ENNReal.toReal_eq_toReal_iff, ← withDensity_apply _ hs]
    simp
  · exact ae_restrict_of_ae (Measure.rnDeriv_lt_top _ _)

中文:
引理 set整数egral_to实数_rnDeriv_eq_withDensity'
  结论: [σ有限 μ]
  证明: by
  rw [integral_toReal (Measure.measurable_rnDeriv _ _).aemeasurable]; rw [measureReal_def]
  · rw [ENNReal.toReal_eq_toReal_iff, ← withDensity_apply _ hs]
    simp
  · exact ae_restrict_of_ae (Measure.rnDeriv_lt_top _ _)

Depends on / 依赖: ENNReal, ENNReal.toReal_eq_toReal_iff, Measure, Measure.measurable_rnDeriv, Measure.rnDeriv_lt_top, ae_restrict_of_ae, aemeasurable, integral_toReal, measurable_rnDeriv, measureReal_def, rnDeriv_lt_top, toReal_eq_toReal_iff, withDensity_apply
-/
lemma setIntegral_toReal_rnDeriv_eq_withDensity' [SigmaFinite μ]
    {s : Set α} (hs : MeasurableSet s) :
    ∫ x in s, (μ.rnDeriv ν x).toReal ∂ν = (ν.withDensity (μ.rnDeriv ν)).real s := by
  rw [integral_toReal (Measure.measurable_rnDeriv _ _).aemeasurable]; rw [measureReal_def]
  · rw [ENNReal.toReal_eq_toReal_iff, ← withDensity_apply _ hs]
    simp
  · exact ae_restrict_of_ae (Measure.rnDeriv_lt_top _ _)

/--
lemma `setIntegral_toReal_rnDeriv_eq_withDensity` / 引理 `setIntegral_toReal_rnDeriv_eq_withDensity`

English:
lemma setIntegral_toReal_rnDeriv_eq_withDensity
  given: [SigmaFinite μ] [SFinite ν] (s : Set α)
  proof: by
  rw [integral_toReal (Measure.measurable_rnDeriv _ _).aemeasurable]; rw [measureReal_def]
  · rw [ENNReal.toReal_eq_toReal_iff, ← withDensity_apply' _ s]
    simp
  · exact ae_restrict_of_ae (Measure.rnDeriv_lt_top _ _)

中文:
引理 set整数egral_to实数_rnDeriv_eq_withDensity
  条件: [σ有限 μ] [SFinite ν] (s : 集合 α)
  证明: by
  rw [integral_toReal (Measure.measurable_rnDeriv _ _).aemeasurable]; rw [measureReal_def]
  · rw [ENNReal.toReal_eq_toReal_iff, ← withDensity_apply' _ s]
    simp
  · exact ae_restrict_of_ae (Measure.rnDeriv_lt_top _ _)

Depends on / 依赖: ENNReal, ENNReal.toReal_eq_toReal_iff, Measure, Measure.measurable_rnDeriv, Measure.rnDeriv_lt_top, ae_restrict_of_ae, aemeasurable, integral_toReal, measurable_rnDeriv, measureReal_def, rnDeriv_lt_top, toReal_eq_toReal_iff, withDensity_apply
-/
lemma setIntegral_toReal_rnDeriv_eq_withDensity [SigmaFinite μ] [SFinite ν] (s : Set α) :
    ∫ x in s, (μ.rnDeriv ν x).toReal ∂ν = (ν.withDensity (μ.rnDeriv ν)).real s := by
  rw [integral_toReal (Measure.measurable_rnDeriv _ _).aemeasurable]; rw [measureReal_def]
  · rw [ENNReal.toReal_eq_toReal_iff, ← withDensity_apply' _ s]
    simp
  · exact ae_restrict_of_ae (Measure.rnDeriv_lt_top _ _)

/--
lemma `setIntegral_toReal_rnDeriv_le` / 引理 `setIntegral_toReal_rnDeriv_le`

English:
lemma setIntegral_toReal_rnDeriv_le
  given: [SigmaFinite μ] {s : Set α} (hμs : μ s != ∞)
  proof: by
  set t := toMeasurable μ s with ht
  have ht_m : MeasurableSet t := measurableSet_toMeasurable μ s
  have hμt : μ t != ∞ := by rwa [ht, measure_toMeasurable s]
  calc ∫ x in s, (μ.rnDeriv ν x).toReal ∂ν
    <= ∫ x in t, (μ.rnDeriv ν x).toReal ∂ν := by
        refine setIntegral_mono_set ?_ ?_ (L

中文:
引理 set整数egral_to实数_rnDeriv_le
  条件: [σ有限 μ] {s : 集合 α} (hμs : μ s != ∞)
  证明: by
  set t := toMeasurable μ s with ht
  have ht_m : MeasurableSet t := measurableSet_toMeasurable μ s
  have hμt : μ t != ∞ := by rwa [ht, measure_toMeasurable s]
  calc ∫ x in s, (μ.rnDeriv ν x).toReal ∂ν
    <= ∫ x in t, (μ.rnDeriv ν x).toReal ∂ν := by
        refine setIntegral_mono_set ?_ ?_ (L

Depends on / 依赖: LE.le.eventuallyLE, MeasurableSet, ae_of_all, eventuallyLE, ht_m, integrableOn_toReal_rnDeriv, measurableSet_toMeasurable, measure_toMeasurable, rnDeriv, setIntegral_mono_set, setIntegral_toReal_rnDeriv_eq_withDensity, subset_toMeasurable, toMeasurable, toReal, withDensity
-/
lemma setIntegral_toReal_rnDeriv_le [SigmaFinite μ] {s : Set α} (hμs : μ s != ∞) :
    ∫ x in s, (μ.rnDeriv ν x).toReal ∂ν <= μ.real s := by
  set t := toMeasurable μ s with ht
  have ht_m : MeasurableSet t := measurableSet_toMeasurable μ s
  have hμt : μ t != ∞ := by rwa [ht, measure_toMeasurable s]
  calc ∫ x in s, (μ.rnDeriv ν x).toReal ∂ν
    <= ∫ x in t, (μ.rnDeriv ν x).toReal ∂ν := by
        refine setIntegral_mono_set ?_ ?_ (LE.le.eventuallyLE (subset_toMeasurable _ _))
        · exact integrableOn_toReal_rnDeriv hμt
        · exact ae_of_all _ (by simp)
  _ = (withDensity ν (rnDeriv μ ν)).real t := setIntegral_toReal_rnDeriv_eq_withDensity' ht_m
  _ <= μ.real t := by
        simp only [measureReal_def]
        gcongr
        apply withDensity_rnDeriv_le
  _ = μ.real s := by rw [measureReal_def, measureReal_def, measure_toMeasurable s]

/--
lemma `setIntegral_toReal_rnDeriv'` / 引理 `setIntegral_toReal_rnDeriv'`

English:
lemma setIntegral_toReal_rnDeriv'
  statement: [SigmaFinite μ] [HaveLebesgueDecomposition μ ν]
  proof: by
  rw [setIntegral_toReal_rnDeriv_eq_withDensity' hs]; rw [Measure.withDensity_rnDeriv_eq _ _ hμν]; rw [measureReal_def]

中文:
引理 set整数egral_to实数_rnDeriv'
  结论: [σ有限 μ] [有Lebesgue分解 μ ν]
  证明: by
  rw [setIntegral_toReal_rnDeriv_eq_withDensity' hs]; rw [Measure.withDensity_rnDeriv_eq _ _ hμν]; rw [measureReal_def]

Depends on / 依赖: Measure, Measure.withDensity_rnDeriv_eq, measureReal_def, setIntegral_toReal_rnDeriv_eq_withDensity, withDensity_rnDeriv_eq
-/
lemma setIntegral_toReal_rnDeriv' [SigmaFinite μ] [HaveLebesgueDecomposition μ ν]
    (hμν : μ ≪ ν) {s : Set α} (hs : MeasurableSet s) :
    ∫ x in s, (μ.rnDeriv ν x).toReal ∂ν = μ.real s := by
  rw [setIntegral_toReal_rnDeriv_eq_withDensity' hs]; rw [Measure.withDensity_rnDeriv_eq _ _ hμν]; rw [measureReal_def]

/--
lemma `setIntegral_toReal_rnDeriv` / 引理 `setIntegral_toReal_rnDeriv`

English:
lemma setIntegral_toReal_rnDeriv
  given: [SigmaFinite μ] [SigmaFinite ν] (hμν : μ ≪ ν) (s : Set α)
  proof: by
  rw [setIntegral_toReal_rnDeriv_eq_withDensity s]; rw [Measure.withDensity_rnDeriv_eq _ _ hμν]

中文:
引理 set整数egral_to实数_rnDeriv
  条件: [σ有限 μ] [σ有限 ν] (hμν : μ ≪ ν) (s : 集合 α)
  证明: by
  rw [setIntegral_toReal_rnDeriv_eq_withDensity s]; rw [Measure.withDensity_rnDeriv_eq _ _ hμν]

Depends on / 依赖: Measure, Measure.withDensity_rnDeriv_eq, h.le, setIntegral_toReal_rnDeriv_eq_withDensity, withDensity_rnDeriv_eq
-/
lemma setIntegral_toReal_rnDeriv [SigmaFinite μ] [SigmaFinite ν] (hμν : μ ≪ ν) (s : Set α) :
    ∫ x in s, (μ.rnDeriv ν x).toReal ∂ν = μ.real s := by
  rw [setIntegral_toReal_rnDeriv_eq_withDensity s]; rw [Measure.withDensity_rnDeriv_eq _ _ hμν]

/--
lemma `integral_toReal_rnDeriv` / 引理 `integral_toReal_rnDeriv`

English:
lemma integral_toReal_rnDeriv
  given: [SigmaFinite μ] [SigmaFinite ν] (hμν : μ ≪ ν)
  proof: by
  rw [← setIntegral_univ]; rw [setIntegral_toReal_rnDeriv hμν Set.univ]

中文:
引理 integral_to实数_rnDeriv
  条件: [σ有限 μ] [σ有限 ν] (hμν : μ ≪ ν)
  证明: by
  rw [← setIntegral_univ]; rw [setIntegral_toReal_rnDeriv hμν Set.univ]

Depends on / 依赖: Set.univ, h.lt, setIntegral_toReal_rnDeriv, setIntegral_univ
-/
lemma integral_toReal_rnDeriv [SigmaFinite μ] [SigmaFinite ν] (hμν : μ ≪ ν) :
    ∫ x, (μ.rnDeriv ν x).toReal ∂ν = μ.real Set.univ := by
  rw [← setIntegral_univ]; rw [setIntegral_toReal_rnDeriv hμν Set.univ]

/--
lemma `integral_toReal_rnDeriv'` / 引理 `integral_toReal_rnDeriv'`

English:
lemma integral_toReal_rnDeriv'
  given: [IsFiniteMeasure μ] [SigmaFinite ν]
  proof: by
  rw [measureReal_def]; rw [measureReal_def]; rw [← ENNReal.toReal_sub_of_le (μ.singularPart_le ν Set.univ) (measure_ne_top _ _)]; rw [← Measure.sub_apply .univ (Measure.singularPart_le μ ν)]; rw [Measure.measure_sub_singularPart]; rw [← measureReal_def]; rw [← Measure.setIntegral_toReal_rnDeriv_

中文:
引理 integral_to实数_rnDeriv'
  条件: [是有限测度 μ] [σ有限 ν]
  证明: by
  rw [measureReal_def]; rw [measureReal_def]; rw [← ENNReal.toReal_sub_of_le (μ.singularPart_le ν Set.univ) (measure_ne_top _ _)]; rw [← Measure.sub_apply .univ (Measure.singularPart_le μ ν)]; rw [Measure.measure_sub_singularPart]; rw [← measureReal_def]; rw [← Measure.setIntegral_toReal_rnDeriv_

Depends on / 依赖: ENNReal, ENNReal.toReal_sub_of_le, Measure, Measure.measure_sub_singularPart, Measure.setIntegral_toReal_rnDeriv_eq_withDensity, Measure.singularPart_le, Measure.sub_apply, Set.univ, compare, h.compare, measureReal_def, measure_ne_top, measure_sub_singularPart, setIntegral_toReal_rnDeriv_eq_withDensity, setIntegral_univ, singularPart_le, sub_apply, toReal_sub_of_le
-/
lemma integral_toReal_rnDeriv' [IsFiniteMeasure μ] [SigmaFinite ν] :
    ∫ x, (μ.rnDeriv ν x).toReal ∂ν = μ.real Set.univ - (μ.singularPart ν).real Set.univ := by
  rw [measureReal_def]; rw [measureReal_def]; rw [← ENNReal.toReal_sub_of_le (μ.singularPart_le ν Set.univ) (measure_ne_top _ _)]; rw [← Measure.sub_apply .univ (Measure.singularPart_le μ ν)]; rw [Measure.measure_sub_singularPart]; rw [← measureReal_def]; rw [← Measure.setIntegral_toReal_rnDeriv_eq_withDensity]; rw [setIntegral_univ]

end integral

/--
lemma `rnDeriv_mul_rnDeriv` / 引理 `rnDeriv_mul_rnDeriv`

English:
lemma rnDeriv_mul_rnDeriv
  statement: {κ : Measure α} [SigmaFinite μ] [SigmaFinite ν] [SigmaFinite κ]
  proof: by
  refine (rnDeriv_withDensity_left ?_ ?_).symm.trans ?_
  · exact (Measure.measurable_rnDeriv _ _).aemeasurable
  · exact rnDeriv_ne_top _ _
  · rw [Measure.withDensity_rnDeriv_eq _ _ hμν]

中文:
引理 rnDeriv_mul_rnDeriv
  结论: {κ : 测度 α} [σ有限 μ] [σ有限 ν] [σ有限 κ]
  证明: by
  refine (rnDeriv_withDensity_left ?_ ?_).symm.trans ?_
  · exact (Measure.measurable_rnDeriv _ _).aemeasurable
  · exact rnDeriv_ne_top _ _
  · rw [Measure.withDensity_rnDeriv_eq _ _ hμν]

Depends on / 依赖: Measure, Measure.measurable_rnDeriv, Measure.withDensity_rnDeriv_eq, aemeasurable, h.min, measurable_rnDeriv, rnDeriv_ne_top, rnDeriv_withDensity_left, symm.trans, withDensity_rnDeriv_eq
-/
lemma rnDeriv_mul_rnDeriv {κ : Measure α} [SigmaFinite μ] [SigmaFinite ν] [SigmaFinite κ]
    (hμν : μ ≪ ν) :
    μ.rnDeriv ν * ν.rnDeriv κ =ᵐ[κ] μ.rnDeriv κ := by
  refine (rnDeriv_withDensity_left ?_ ?_).symm.trans ?_
  · exact (Measure.measurable_rnDeriv _ _).aemeasurable
  · exact rnDeriv_ne_top _ _
  · rw [Measure.withDensity_rnDeriv_eq _ _ hμν]

/--
lemma `rnDeriv_mul_rnDeriv'` / 引理 `rnDeriv_mul_rnDeriv'`

English:
lemma rnDeriv_mul_rnDeriv'
  statement: {κ : Measure α} [SigmaFinite μ] [SigmaFinite ν] [SigmaFinite κ]
  proof: by
  obtain ⟨h_meas, h_sing, hμν⟩ := Measure.haveLebesgueDecomposition_spec μ ν
  filter_upwards [hνκ <| Measure.rnDeriv_add' (μ.singularPart ν) (ν.withDensity (μ.rnDeriv ν)) κ,
hνκ Measure.rnDeriv_withDensity_left_of_absolutelyContinuous hνκ h_meas.aemeasurable,
    Measure.rnDeriv_eq_zero_of_mutua

中文:
引理 rnDeriv_mul_rnDeriv'
  结论: {κ : 测度 α} [σ有限 μ] [σ有限 ν] [σ有限 κ]
  证明: by
  obtain ⟨h_meas, h_sing, hμν⟩ := Measure.haveLebesgueDecomposition_spec μ ν
  filter_upwards [hνκ <| Measure.rnDeriv_add' (μ.singularPart ν) (ν.withDensity (μ.rnDeriv ν)) κ,
hνκ Measure.rnDeriv_withDensity_left_of_absolutelyContinuous hνκ h_meas.aemeasurable,
    Measure.rnDeriv_eq_zero_of_mutua

Depends on / 依赖: Measure, Measure.haveLebesgueDecomposition_spec, Measure.rnDeriv_add, Measure.rnDeriv_eq_zero_of_mutuallySingular, Measure.rnDeriv_withDensity_left_of_absolutelyContinuous, Pi.add_apply, Pi.mul_apply, Pi.zero_apply, add_apply, aemeasurable, filter_upwards, h_meas, h_meas.aemeasurable, h_sing, haveLebesgueDecomposition_spec, mul_apply, nth_rw, rnDeriv, rnDeriv_add, rnDeriv_eq_zero_of_mutuallySingular
-/
lemma rnDeriv_mul_rnDeriv' {κ : Measure α} [SigmaFinite μ] [SigmaFinite ν] [SigmaFinite κ]
    (hνκ : ν ≪ κ) :
    μ.rnDeriv ν * ν.rnDeriv κ =ᵐ[ν] μ.rnDeriv κ := by
  obtain ⟨h_meas, h_sing, hμν⟩ := Measure.haveLebesgueDecomposition_spec μ ν
  filter_upwards [hνκ <| Measure.rnDeriv_add' (μ.singularPart ν) (ν.withDensity (μ.rnDeriv ν)) κ,
hνκ Measure.rnDeriv_withDensity_left_of_absolutelyContinuous hνκ h_meas.aemeasurable,
    Measure.rnDeriv_eq_zero_of_mutuallySingular h_sing hνκ] with x hx1 hx2 hx3
  nth_rw 2 [hμν]
  rw [hx1]; rw [Pi.add_apply]; rw [hx2]; rw [Pi.mul_apply]; rw [hx3]; rw [Pi.zero_apply]; rw [zero_add]

/--
lemma `rnDeriv_le_one_of_le` / 引理 `rnDeriv_le_one_of_le`

English:
lemma rnDeriv_le_one_of_le
  given: (hμν : μ <= ν) [SigmaFinite ν]
  statement: μ.rnDeriv ν <=ᵐ[ν] 1
  proof: by
  refine ae_le_of_forall_setLIntegral_le_of_sigmaFinite (μ.measurable_rnDeriv ν) fun s _ _ => ?_
  simp only [Pi.one_apply, MeasureTheory.setLIntegral_one]
  exact (Measure.setLIntegral_rnDeriv_le s).trans (hμν s)

中文:
引理 rnDeriv_le_one_of_le
  条件: (hμν : μ <= ν) [σ有限 ν]
  结论: μ.rnDeriv ν <=ᵐ[ν] 1
  证明: by
  refine ae_le_of_forall_setLIntegral_le_of_sigmaFinite (μ.measurable_rnDeriv ν) fun s _ _ => ?_
  simp only [Pi.one_apply, MeasureTheory.setLIntegral_one]
  exact (Measure.setLIntegral_rnDeriv_le s).trans (hμν s)

Depends on / 依赖: Measure, Measure.setLIntegral_rnDeriv_le, MeasureTheory, MeasureTheory.setLIntegral_one, Pi.one_apply, ae_le_of_forall_setLIntegral_le_of_sigmaFinite, measurable_rnDeriv, one_apply, setLIntegral_one, setLIntegral_rnDeriv_le
-/
lemma rnDeriv_le_one_of_le (hμν : μ <= ν) [SigmaFinite ν] : μ.rnDeriv ν <=ᵐ[ν] 1 := by
  refine ae_le_of_forall_setLIntegral_le_of_sigmaFinite (μ.measurable_rnDeriv ν) fun s _ _ => ?_
  simp only [Pi.one_apply, MeasureTheory.setLIntegral_one]
  exact (Measure.setLIntegral_rnDeriv_le s).trans (hμν s)

/--
lemma `rnDeriv_le_one_iff_le` / 引理 `rnDeriv_le_one_iff_le`

English:
lemma rnDeriv_le_one_iff_le
  given: [HaveLebesgueDecomposition μ ν] [SigmaFinite ν] (hμν : μ ≪ ν)
  proof: by
  refine ⟨fun h s => ?_, fun h => rnDeriv_le_one_of_le h⟩
  rw [← withDensity_rnDeriv_eq _ _ hμν]; rw [withDensity_apply']; rw [← setLIntegral_one]
  exact setLIntegral_mono_ae aemeasurable_const (h.mono fun _ hh _ => hh)

中文:
引理 rnDeriv_le_one_iff_le
  条件: [有Lebesgue分解 μ ν] [σ有限 ν] (hμν : μ ≪ ν)
  证明: by
  refine ⟨fun h s => ?_, fun h => rnDeriv_le_one_of_le h⟩
  rw [← withDensity_rnDeriv_eq _ _ hμν]; rw [withDensity_apply']; rw [← setLIntegral_one]
  exact setLIntegral_mono_ae aemeasurable_const (h.mono fun _ hh _ => hh)

Depends on / 依赖: aemeasurable_const, h.mono, rnDeriv_le_one_of_le, setLIntegral_mono_ae, setLIntegral_one, withDensity_apply, withDensity_rnDeriv_eq
-/
lemma rnDeriv_le_one_iff_le [HaveLebesgueDecomposition μ ν] [SigmaFinite ν] (hμν : μ ≪ ν) :
    μ.rnDeriv ν <=ᵐ[ν] 1 ↔ μ <= ν := by
  refine ⟨fun h s => ?_, fun h => rnDeriv_le_one_of_le h⟩
  rw [← withDensity_rnDeriv_eq _ _ hμν]; rw [withDensity_apply']; rw [← setLIntegral_one]
  exact setLIntegral_mono_ae aemeasurable_const (h.mono fun _ hh _ => hh)

/--
lemma `rnDeriv_eq_one_iff_eq` / 引理 `rnDeriv_eq_one_iff_eq`

English:
lemma rnDeriv_eq_one_iff_eq
  given: [HaveLebesgueDecomposition μ ν] [SigmaFinite ν] (hμν : μ ≪ ν)
  proof: by
  refine ⟨fun h => ?_, fun h => h ▸ ν.rnDeriv_self⟩
  rw [← withDensity_rnDeriv_eq _ _ hμν]; rw [withDensity_congr_ae h]; rw [withDensity_one]

中文:
引理 rnDeriv_eq_one_iff_eq
  条件: [有Lebesgue分解 μ ν] [σ有限 ν] (hμν : μ ≪ ν)
  证明: by
  refine ⟨fun h => ?_, fun h => h ▸ ν.rnDeriv_self⟩
  rw [← withDensity_rnDeriv_eq _ _ hμν]; rw [withDensity_congr_ae h]; rw [withDensity_one]

Depends on / 依赖: le_refl, rnDeriv_self, withDensity_congr_ae, withDensity_one, withDensity_rnDeriv_eq
-/
lemma rnDeriv_eq_one_iff_eq [HaveLebesgueDecomposition μ ν] [SigmaFinite ν] (hμν : μ ≪ ν) :
    μ.rnDeriv ν =ᵐ[ν] 1 ↔ μ = ν := by
  refine ⟨fun h => ?_, fun h => h ▸ ν.rnDeriv_self⟩
  rw [← withDensity_rnDeriv_eq _ _ hμν]; rw [withDensity_congr_ae h]; rw [withDensity_one]

section Ratio

/--
lemma `rnDeriv_add_self` / 引理 `rnDeriv_add_self`

English:
lemma rnDeriv_add_self
  given: (μ ν : Measure α) [SigmaFinite μ] [SigmaFinite ν]
  proof: by
  have hν_ac : μ ≪ ν + μ := rfl.absolutelyContinuous.add_right' _
  filter_upwards [ν.rnDeriv_add' μ μ, μ.rnDeriv_self, Measure.inv_rnDeriv hν_ac] with a h1 h2 h3
  rw [Pi.inv_apply]; rw [h1]; rw [Pi.add_apply]; rw [h2]; rw [inv_eq_iff_eq_inv] at h3
  rw [h3]

中文:
引理 rnDeriv_add_self
  条件: (μ ν : 测度 α) [σ有限 μ] [σ有限 ν]
  证明: by
  have hν_ac : μ ≪ ν + μ := rfl.absolutelyContinuous.add_right' _
  filter_upwards [ν.rnDeriv_add' μ μ, μ.rnDeriv_self, Measure.inv_rnDeriv hν_ac] with a h1 h2 h3
  rw [Pi.inv_apply]; rw [h1]; rw [Pi.add_apply]; rw [h2]; rw [inv_eq_iff_eq_inv] at h3
  rw [h3]

Depends on / 依赖: Measure, Measure.inv_rnDeriv, Pi.add_apply, Pi.inv_apply, absolutelyContinuous, add_apply, add_right, filter_upwards, inv_apply, inv_eq_iff_eq_inv, inv_rnDeriv, le_antisymm, rfl.absolutelyContinuous.add_right, rnDeriv_add, rnDeriv_self
-/
lemma rnDeriv_add_self (μ ν : Measure α) [SigmaFinite μ] [SigmaFinite ν] :
    μ.rnDeriv (ν + μ) =ᵐ[μ] fun x => (ν.rnDeriv μ x + 1)⁻¹ := by
  have hν_ac : μ ≪ ν + μ := rfl.absolutelyContinuous.add_right' _
  filter_upwards [ν.rnDeriv_add' μ μ, μ.rnDeriv_self, Measure.inv_rnDeriv hν_ac] with a h1 h2 h3
  rw [Pi.inv_apply]; rw [h1]; rw [Pi.add_apply]; rw [h2]; rw [inv_eq_iff_eq_inv] at h3
  rw [h3]

/--
lemma `rnDeriv_self_add` / 引理 `rnDeriv_self_add`

English:
lemma rnDeriv_self_add
  given: (μ ν : Measure α) [SigmaFinite μ] [SigmaFinite ν]
  proof: by
  have h_add : (μ + ν).rnDeriv (μ + ν) =ᵐ[ν] μ.rnDeriv (μ + ν) + ν.rnDeriv (μ + ν) :=
    (ae_add_measure_iff.mp (μ.rnDeriv_add' ν (μ + ν))).2
  have h_one_add := (ae_add_measure_iff.mp (μ + ν).rnDeriv_self).2
  have : (μ.rnDeriv (μ + ν)) =ᵐ[ν] fun x => 1 - (μ.rnDeriv ν x + 1)⁻¹ := by
    filter_

中文:
引理 rnDeriv_self_add
  条件: (μ ν : 测度 α) [σ有限 μ] [σ有限 ν]
  证明: by
  have h_add : (μ + ν).rnDeriv (μ + ν) =ᵐ[ν] μ.rnDeriv (μ + ν) + ν.rnDeriv (μ + ν) :=
    (ae_add_measure_iff.mp (μ.rnDeriv_add' ν (μ + ν))).2
  have h_one_add := (ae_add_measure_iff.mp (μ + ν).rnDeriv_self).2
  have : (μ.rnDeriv (μ + ν)) =ᵐ[ν] fun x => 1 - (μ.rnDeriv ν x + 1)⁻¹ := by
    filter_

Depends on / 依赖: DecidableEq, Pi.add_apply, add_apply, ae_add_measure_iff, ae_add_measure_iff.mp, div_eq_mul_inv, filter_upwards, h_add, h_one_add, ha_lt_top, nth_rw, rnDeriv, rnDeriv_add, rnDeriv_add_self, rnDeriv_lt_top, rnDeriv_self
-/
lemma rnDeriv_self_add (μ ν : Measure α) [SigmaFinite μ] [SigmaFinite ν] :
    μ.rnDeriv (μ + ν) =ᵐ[ν] fun x => μ.rnDeriv ν x / (μ.rnDeriv ν x + 1) := by
  have h_add : (μ + ν).rnDeriv (μ + ν) =ᵐ[ν] μ.rnDeriv (μ + ν) + ν.rnDeriv (μ + ν) :=
    (ae_add_measure_iff.mp (μ.rnDeriv_add' ν (μ + ν))).2
  have h_one_add := (ae_add_measure_iff.mp (μ + ν).rnDeriv_self).2
  have : (μ.rnDeriv (μ + ν)) =ᵐ[ν] fun x => 1 - (μ.rnDeriv ν x + 1)⁻¹ := by
    filter_upwards [h_add, h_one_add, rnDeriv_add_self ν μ] with a h4 h5 h6
    rw [h5]; rw [Pi.add_apply] at h4
    nth_rw 1 [h4, h6]
    simp
  filter_upwards [this, μ.rnDeriv_lt_top ν] with a ha ha_lt_top
  rw [ha]; rw [div_eq_mul_inv]
  refine ENNReal.sub_eq_of_eq_add (by simp) ?_
  nth_rewrite 2 [← one_mul (μ.rnDeriv ν a + 1)⁻¹]
  have h := add_mul (μ.rnDeriv ν a) 1 (μ.rnDeriv ν a + 1)⁻¹
  rwa [ENNReal.mul_inv_cancel (by simp) (by simp [ha_lt_top.ne])] at h

/--
lemma `rnDeriv_eq_div_rnDeriv_add` / 引理 `rnDeriv_eq_div_rnDeriv_add`

English:
lemma rnDeriv_eq_div_rnDeriv_add
  given: (μ ν : Measure α) [SigmaFinite μ] [SigmaFinite ν]
  proof: by
  filter_upwards [rnDeriv_add_self ν μ, rnDeriv_self_add μ ν, μ.rnDeriv_lt_top ν]
      with a ha1 ha2 ha_lt_top
  rw [ha1]; rw [ha2]; rw [ENNReal.div_eq_inv_mul]; rw [inv_inv]; rw [ENNReal.div_eq_inv_mul]; rw [← mul_assoc]; rw [ENNReal.mul_inv_cancel]; rw [one_mul]
  · simp
  · simp [ha_lt_top.n

中文:
引理 rnDeriv_eq_div_rnDeriv_add
  条件: (μ ν : 测度 α) [σ有限 μ] [σ有限 ν]
  证明: by
  filter_upwards [rnDeriv_add_self ν μ, rnDeriv_self_add μ ν, μ.rnDeriv_lt_top ν]
      with a ha1 ha2 ha_lt_top
  rw [ha1]; rw [ha2]; rw [ENNReal.div_eq_inv_mul]; rw [inv_inv]; rw [ENNReal.div_eq_inv_mul]; rw [← mul_assoc]; rw [ENNReal.mul_inv_cancel]; rw [one_mul]
  · simp
  · simp [ha_lt_top.n

Depends on / 依赖: ENNReal, ENNReal.div_eq_inv_mul, ENNReal.mul_inv_cancel, div_eq_inv_mul, filter_upwards, ha_lt_top, ha_lt_top.ne, inv_inv, mul_assoc, mul_inv_cancel, one_mul, rnDeriv_add_self, rnDeriv_lt_top, rnDeriv_self_add
-/
lemma rnDeriv_eq_div_rnDeriv_add (μ ν : Measure α) [SigmaFinite μ] [SigmaFinite ν] :
    μ.rnDeriv ν =ᵐ[ν] fun x => μ.rnDeriv (μ + ν) x / ν.rnDeriv (μ + ν) x := by
  filter_upwards [rnDeriv_add_self ν μ, rnDeriv_self_add μ ν, μ.rnDeriv_lt_top ν]
      with a ha1 ha2 ha_lt_top
  rw [ha1]; rw [ha2]; rw [ENNReal.div_eq_inv_mul]; rw [inv_inv]; rw [ENNReal.div_eq_inv_mul]; rw [← mul_assoc]; rw [ENNReal.mul_inv_cancel]; rw [one_mul]
  · simp
  · simp [ha_lt_top.ne]

/--
lemma `rnDeriv_div_rnDeriv_eq_div_rnDeriv_add` / 引理 `rnDeriv_div_rnDeriv_eq_div_rnDeriv_add`

English:
lemma rnDeriv_div_rnDeriv_eq_div_rnDeriv_add
  statement: {ξ : Measure α}
  proof: by
  have h1 : μ.rnDeriv (μ + ν) * (μ + ν).rnDeriv ξ =ᵐ[ξ] μ.rnDeriv ξ :=
    Measure.rnDeriv_mul_rnDeriv (rfl.absolutelyContinuous.add_right _)
  have h2 : ν.rnDeriv (μ + ν) * (μ + ν).rnDeriv ξ =ᵐ[ξ] ν.rnDeriv ξ :=
    Measure.rnDeriv_mul_rnDeriv (rfl.absolutelyContinuous.add_right' _)
  have h_ac 

中文:
引理 rnDeriv_div_rnDeriv_eq_div_rnDeriv_add
  结论: {ξ : 测度 α}
  证明: by
  have h1 : μ.rnDeriv (μ + ν) * (μ + ν).rnDeriv ξ =ᵐ[ξ] μ.rnDeriv ξ :=
    Measure.rnDeriv_mul_rnDeriv (rfl.absolutelyContinuous.add_right _)
  have h2 : ν.rnDeriv (μ + ν) * (μ + ν).rnDeriv ξ =ᵐ[ξ] ν.rnDeriv ξ :=
    Measure.rnDeriv_mul_rnDeriv (rfl.absolutelyContinuous.add_right' _)
  have h_ac 

Depends on / 依赖: Measure, Measure.rnDeriv_mul_rnDeriv, Measure.rnDeriv_pos, absolutelyContinuous, add_left, add_right, filter_upwards, h_ac, h_lt_top1, h_lt_top2, h_pos, rfl.absolutelyContinuous.add_right, rnDeriv, rnDeriv_lt_top, rnDeriv_mul_rnDeriv, rnDeriv_pos
-/
lemma rnDeriv_div_rnDeriv_eq_div_rnDeriv_add {ξ : Measure α}
    [SigmaFinite μ] [SigmaFinite ν] [SigmaFinite ξ]
    (hμ : μ ≪ ξ) (hν : ν ≪ ξ) :
    (fun x => μ.rnDeriv ξ x / ν.rnDeriv ξ x)
      =ᵐ[μ + ν] fun x => μ.rnDeriv (μ + ν) x / ν.rnDeriv (μ + ν) x := by
  have h1 : μ.rnDeriv (μ + ν) * (μ + ν).rnDeriv ξ =ᵐ[ξ] μ.rnDeriv ξ :=
    Measure.rnDeriv_mul_rnDeriv (rfl.absolutelyContinuous.add_right _)
  have h2 : ν.rnDeriv (μ + ν) * (μ + ν).rnDeriv ξ =ᵐ[ξ] ν.rnDeriv ξ :=
    Measure.rnDeriv_mul_rnDeriv (rfl.absolutelyContinuous.add_right' _)
  have h_ac : μ + ν ≪ ξ := hμ.add_left hν
  filter_upwards [h_ac h1, h_ac h2, h_ac <| (μ + ν).rnDeriv_lt_top ξ, ν.rnDeriv_lt_top (μ + ν),
    Measure.rnDeriv_pos h_ac] with a h1 h2 h_lt_top1 h_lt_top2 h_pos
  rw [← h1]; rw [← h2]; rw [Pi.mul_apply]; rw [Pi.mul_apply]; rw [div_eq_mul_inv]; rw [ENNReal.mul_inv (Or.inr h_lt_top1.ne) (Or.inl h_lt_top2.ne)]; rw [div_eq_mul_inv]; rw [mul_assoc]; rw [mul_comm ((μ + ν).rnDeriv ξ a)]; rw [mul_assoc]; rw [ENNReal.inv_mul_cancel h_pos.ne' h_lt_top1.ne]; rw [mul_one]

/--
lemma `rnDeriv_eq_div` / 引理 `rnDeriv_eq_div`

English:
lemma rnDeriv_eq_div
  statement: {ξ : Measure α} [SigmaFinite μ] [SigmaFinite ν] [SigmaFinite ξ]
  proof: by
  have hν_ac : ν ≪ μ + ν := rfl.absolutelyContinuous.add_right' _
  filter_upwards [μ.rnDeriv_eq_div_rnDeriv_add ν,
    hν_ac (rnDeriv_div_rnDeriv_eq_div_rnDeriv_add hμ hν)] with a h1 h2 using h1.trans h2.symm

中文:
引理 rnDeriv_eq_div
  结论: {ξ : 测度 α} [σ有限 μ] [σ有限 ν] [σ有限 ξ]
  证明: by
  have hν_ac : ν ≪ μ + ν := rfl.absolutelyContinuous.add_right' _
  filter_upwards [μ.rnDeriv_eq_div_rnDeriv_add ν,
    hν_ac (rnDeriv_div_rnDeriv_eq_div_rnDeriv_add hμ hν)] with a h1 h2 using h1.trans h2.symm

Depends on / 依赖: absolutelyContinuous, add_right, filter_upwards, h1.trans, h2.symm, le_total, rfl.absolutelyContinuous.add_right, rnDeriv_div_rnDeriv_eq_div_rnDeriv_add, rnDeriv_eq_div_rnDeriv_add
-/
lemma rnDeriv_eq_div {ξ : Measure α} [SigmaFinite μ] [SigmaFinite ν] [SigmaFinite ξ]
    (hμ : μ ≪ ξ) (hν : ν ≪ ξ) :
    μ.rnDeriv ν =ᵐ[ν] fun x => μ.rnDeriv ξ x / ν.rnDeriv ξ x := by
  have hν_ac : ν ≪ μ + ν := rfl.absolutelyContinuous.add_right' _
  filter_upwards [μ.rnDeriv_eq_div_rnDeriv_add ν,
    hν_ac (rnDeriv_div_rnDeriv_eq_div_rnDeriv_add hμ hν)] with a h1 h2 using h1.trans h2.symm

end Ratio

section MeasurableEmbedding

variable {mβ : MeasurableSpace β} {f : α -> β}

/--
lemma `_root_.MeasurableEmbedding.rnDeriv_map_aux` / 引理 `_root_.MeasurableEmbedding.rnDeriv_map_aux`

English:
lemma _root_.MeasurableEmbedding.rnDeriv_map_aux
  statement: (hf : MeasurableEmbedding f)
  proof: by
  refine ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite ?_ ?_ (fun s _ _ => ?_)
  · exact (Measure.measurable_rnDeriv _ _).comp hf.measurable
  · exact Measure.measurable_rnDeriv _ _
  rw [← hf.lintegral_map]; rw [Measure.setLIntegral_rnDeriv hμν]
  have hs_eq : s = f ⁻¹' f '' s := by rw [hf.inje

中文:
引理 _root_.可测嵌入.rnDeriv_map_aux
  结论: (hf : 可测嵌入 f)
  证明: by
  refine ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite ?_ ?_ (fun s _ _ => ?_)
  · exact (Measure.measurable_rnDeriv _ _).comp hf.measurable
  · exact Measure.measurable_rnDeriv _ _
  rw [← hf.lintegral_map]; rw [Measure.setLIntegral_rnDeriv hμν]
  have hs_eq : s = f ⁻¹' f '' s := by rw [hf.inje

Depends on / 依赖: Measure, Measure.measurable_rnDeriv, Measure.setLIntegral_rnDeriv, SigmaFinite, absolutelyContinuous_map, ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite, hf.absolutelyContinuous_map, hf.injective.preimage_image, hf.lintegral_map, hf.map_apply, hf.measurable, hf.restrict_map, hf.sigmaFinite_map, hs_eq, injective, lintegral_map, map_apply, measurable, measurable_rnDeriv, preimage_image
-/
lemma _root_.MeasurableEmbedding.rnDeriv_map_aux (hf : MeasurableEmbedding f)
    (hμν : μ ≪ ν) [SigmaFinite μ] [SigmaFinite ν] :
    (fun x => (μ.map f).rnDeriv (ν.map f) (f x)) =ᵐ[ν] μ.rnDeriv ν := by
  refine ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite ?_ ?_ (fun s _ _ => ?_)
  · exact (Measure.measurable_rnDeriv _ _).comp hf.measurable
  · exact Measure.measurable_rnDeriv _ _
  rw [← hf.lintegral_map]; rw [Measure.setLIntegral_rnDeriv hμν]
  have hs_eq : s = f ⁻¹' f '' s := by rw [hf.injective.preimage_image]
  have : SigmaFinite (ν.map f) := hf.sigmaFinite_map
  rw [hs_eq]; rw [← hf.restrict_map]; rw [Measure.setLIntegral_rnDeriv (hf.absolutelyContinuous_map hμν)]; rw [hf.map_apply]

/--
lemma `_root_.MeasurableEmbedding.rnDeriv_map` / 引理 `_root_.MeasurableEmbedding.rnDeriv_map`

English:
lemma _root_.MeasurableEmbedding.rnDeriv_map
  statement: (hf : MeasurableEmbedding f)
  proof: by
  rw [μ.haveLebesgueDecomposition_add ν]; rw [Measure.map_add _ _ hf.measurable]
  have : SigmaFinite (map f ν) := hf.sigmaFinite_map
  have : SigmaFinite (map f (μ.singularPart ν)) := hf.sigmaFinite_map
  have : SigmaFinite (map f (ν.withDensity (μ.rnDeriv ν))) := hf.sigmaFinite_map
  have h_add

中文:
引理 _root_.可测嵌入.rnDeriv_map
  结论: (hf : 可测嵌入 f)
  证明: by
  rw [μ.haveLebesgueDecomposition_add ν]; rw [Measure.map_add _ _ hf.measurable]
  have : SigmaFinite (map f ν) := hf.sigmaFinite_map
  have : SigmaFinite (map f (μ.singularPart ν)) := hf.sigmaFinite_map
  have : SigmaFinite (map f (ν.withDensity (μ.rnDeriv ν))) := hf.sigmaFinite_map
  have h_add

Depends on / 依赖: EventuallyEq, Filter, Filter.EventuallyEq, Measure, Measure.map_add, Measure.rnDeriv_add, SigmaFinite, ae_map_iff, h_add, h_add.trans, haveLebesgueDecomposition_add, hf.ae_map_iff, hf.measurable, hf.sigmaFinite_map, map_add, measurable, rnDeriv, rnDeriv_add, sigmaFinite_map, singularPart
-/
lemma _root_.MeasurableEmbedding.rnDeriv_map (hf : MeasurableEmbedding f)
    (μ ν : Measure α) [SigmaFinite μ] [SigmaFinite ν] :
    (fun x => (μ.map f).rnDeriv (ν.map f) (f x)) =ᵐ[ν] μ.rnDeriv ν := by
  rw [μ.haveLebesgueDecomposition_add ν]; rw [Measure.map_add _ _ hf.measurable]
  have : SigmaFinite (map f ν) := hf.sigmaFinite_map
  have : SigmaFinite (map f (μ.singularPart ν)) := hf.sigmaFinite_map
  have : SigmaFinite (map f (ν.withDensity (μ.rnDeriv ν))) := hf.sigmaFinite_map
  have h_add := Measure.rnDeriv_add' ((μ.singularPart ν).map f)
    ((ν.withDensity (μ.rnDeriv ν)).map f) (ν.map f)
  rw [Filter.EventuallyEq]; rw [hf.ae_map_iff]; rw [← Filter.EventuallyEq] at h_add
  refine h_add.trans ((Measure.rnDeriv_add' _ _ _).trans ?_).symm
  refine Filter.EventuallyEq.add ?_ ?_
  · refine (Measure.rnDeriv_singularPart μ ν).trans ?_
    symm
    suffices (fun x => ((μ.singularPart ν).map f).rnDeriv (ν.map f) x) =ᵐ[ν.map f] 0 by
      rw [Filter.EventuallyEq]; rw [hf.ae_map_iff] at this
      exact this
    refine Measure.rnDeriv_eq_zero_of_mutuallySingular ?_ Measure.AbsolutelyContinuous.rfl
    exact hf.mutuallySingular_map (μ.mutuallySingular_singularPart ν)
  · exact (hf.rnDeriv_map_aux (withDensity_absolutelyContinuous _ _)).symm

/--
lemma `_root_.MeasurableEmbedding.map_withDensity_rnDeriv` / 引理 `_root_.MeasurableEmbedding.map_withDensity_rnDeriv`

English:
lemma _root_.MeasurableEmbedding.map_withDensity_rnDeriv
  statement: (hf : MeasurableEmbedding f)
  proof: by
  ext s hs
  rw [hf.map_apply]; rw [withDensity_apply _ (hf.measurable hs)]; rw [withDensity_apply _ hs]; rw [setLIntegral_map hs (Measure.measurable_rnDeriv _ _) hf.measurable]
  refine setLIntegral_congr_fun_ae (hf.measurable hs) ?_
  filter_upwards [hf.rnDeriv_map μ ν] with a ha _ using ha.sym

中文:
引理 _root_.可测嵌入.map_withDensity_rnDeriv
  结论: (hf : 可测嵌入 f)
  证明: by
  ext s hs
  rw [hf.map_apply]; rw [withDensity_apply _ (hf.measurable hs)]; rw [withDensity_apply _ hs]; rw [setLIntegral_map hs (Measure.measurable_rnDeriv _ _) hf.measurable]
  refine setLIntegral_congr_fun_ae (hf.measurable hs) ?_
  filter_upwards [hf.rnDeriv_map μ ν] with a ha _ using ha.sym

Depends on / 依赖: Measure, Measure.measurable_rnDeriv, filter_upwards, ha.symm, hf.map_apply, hf.measurable, hf.rnDeriv_map, map_apply, measurable, measurable_rnDeriv, rnDeriv_map, setLIntegral_congr_fun_ae, setLIntegral_map, withDensity_apply
-/
lemma _root_.MeasurableEmbedding.map_withDensity_rnDeriv (hf : MeasurableEmbedding f)
    (μ ν : Measure α) [SigmaFinite μ] [SigmaFinite ν] :
    (ν.withDensity (μ.rnDeriv ν)).map f = (ν.map f).withDensity ((μ.map f).rnDeriv (ν.map f)) := by
  ext s hs
  rw [hf.map_apply]; rw [withDensity_apply _ (hf.measurable hs)]; rw [withDensity_apply _ hs]; rw [setLIntegral_map hs (Measure.measurable_rnDeriv _ _) hf.measurable]
  refine setLIntegral_congr_fun_ae (hf.measurable hs) ?_
  filter_upwards [hf.rnDeriv_map μ ν] with a ha _ using ha.symm

/--
lemma `_root_.MeasurableEmbedding.singularPart_map` / 引理 `_root_.MeasurableEmbedding.singularPart_map`

English:
lemma _root_.MeasurableEmbedding.singularPart_map
  statement: (hf : MeasurableEmbedding f)
  proof: by
  have h_add : μ.map f = (μ.singularPart ν).map f
      + (ν.map f).withDensity ((μ.map f).rnDeriv (ν.map f)) := by
    conv_lhs => rw [μ.haveLebesgueDecomposition_add ν]
    rw [Measure.map_add _ _ hf.measurable]; rw [← hf.map_withDensity_rnDeriv μ ν]
  refine (Measure.eq_singularPart (Measure.m

中文:
引理 _root_.可测嵌入.singularPart_map
  结论: (hf : 可测嵌入 f)
  证明: by
  have h_add : μ.map f = (μ.singularPart ν).map f
      + (ν.map f).withDensity ((μ.map f).rnDeriv (ν.map f)) := by
    conv_lhs => rw [μ.haveLebesgueDecomposition_add ν]
    rw [Measure.map_add _ _ hf.measurable]; rw [← hf.map_withDensity_rnDeriv μ ν]
  refine (Measure.eq_singularPart (Measure.m

Depends on / 依赖: Measure, Measure.eq_singularPart, Measure.map_add, Measure.measurable_rnDeriv, conv_lhs, eq_singularPart, h_add, haveLebesgueDecomposition_add, hf.map_withDensity_rnDeriv, hf.measurable, hf.mutuallySingular_map, map_add, map_withDensity_rnDeriv, measurable, measurable_rnDeriv, mutuallySingular_map, mutuallySingular_singularPart, rnDeriv, singularPart, withDensity
-/
lemma _root_.MeasurableEmbedding.singularPart_map (hf : MeasurableEmbedding f)
    (μ ν : Measure α) [SigmaFinite μ] [SigmaFinite ν] :
    (μ.map f).singularPart (ν.map f) = (μ.singularPart ν).map f := by
  have h_add : μ.map f = (μ.singularPart ν).map f
      + (ν.map f).withDensity ((μ.map f).rnDeriv (ν.map f)) := by
    conv_lhs => rw [μ.haveLebesgueDecomposition_add ν]
    rw [Measure.map_add _ _ hf.measurable]; rw [← hf.map_withDensity_rnDeriv μ ν]
  refine (Measure.eq_singularPart (Measure.measurable_rnDeriv _ _) ?_ h_add).symm
  exact hf.mutuallySingular_map (μ.mutuallySingular_singularPart ν)

end MeasurableEmbedding

end Measure

section IntegralRNDerivMul

open Measure

variable {α : Type*} {m : MeasurableSpace α} {μ ν : Measure α}

/--
theorem `lintegral_rnDeriv_mul` / 定理 `lintegral_rnDeriv_mul`

English:
theorem lintegral_rnDeriv_mul
  statement: [HaveLebesgueDecomposition μ ν] (hμν : μ ≪ ν) {f : α -> Real>=0∞}
  proof: by
  nth_rw 2 [← withDensity_rnDeriv_eq μ ν hμν]
  rw [lintegral_withDensity_eq_lintegral_mul₀ (measurable_rnDeriv μ ν).aemeasurable hf]
  simp only [Pi.mul_apply]

中文:
定理 lintegral_rnDeriv_mul
  结论: [有Lebesgue分解 μ ν] (hμν : μ ≪ ν) {f : α -> 实数>=0∞}
  证明: by
  nth_rw 2 [← withDensity_rnDeriv_eq μ ν hμν]
  rw [lintegral_withDensity_eq_lintegral_mul₀ (measurable_rnDeriv μ ν).aemeasurable hf]
  simp only [Pi.mul_apply]

Depends on / 依赖: Pi.mul_apply, aemeasurable, measurable_rnDeriv, mul_apply, nth_rw, withDensity_rnDeriv_eq
-/
theorem lintegral_rnDeriv_mul [HaveLebesgueDecomposition μ ν] (hμν : μ ≪ ν) {f : α -> Real>=0∞}
    (hf : AEMeasurable f ν) : ∫⁻ x, μ.rnDeriv ν x * f x ∂ν = ∫⁻ x, f x ∂μ := by
  nth_rw 2 [← withDensity_rnDeriv_eq μ ν hμν]
  rw [lintegral_withDensity_eq_lintegral_mul₀ (measurable_rnDeriv μ ν).aemeasurable hf]
  simp only [Pi.mul_apply]

/--
lemma `setLIntegral_rnDeriv_mul` / 引理 `setLIntegral_rnDeriv_mul`

English:
lemma setLIntegral_rnDeriv_mul
  statement: [HaveLebesgueDecomposition μ ν] (hμν : μ ≪ ν) {f : α -> Real>=0∞}
  proof: by
  nth_rw 2 [← Measure.withDensity_rnDeriv_eq μ ν hμν]
  rw [setLIntegral_withDensity_eq_lintegral_mul₀ (measurable_rnDeriv μ ν).aemeasurable hf hs]
  simp only [Pi.mul_apply]

中文:
引理 setL整数egral_rnDeriv_mul
  结论: [有Lebesgue分解 μ ν] (hμν : μ ≪ ν) {f : α -> 实数>=0∞}
  证明: by
  nth_rw 2 [← Measure.withDensity_rnDeriv_eq μ ν hμν]
  rw [setLIntegral_withDensity_eq_lintegral_mul₀ (measurable_rnDeriv μ ν).aemeasurable hf hs]
  simp only [Pi.mul_apply]

Depends on / 依赖: Measure, Measure.withDensity_rnDeriv_eq, Pi.mul_apply, aemeasurable, measurable_rnDeriv, mul_apply, nth_rw, withDensity_rnDeriv_eq
-/
lemma setLIntegral_rnDeriv_mul [HaveLebesgueDecomposition μ ν] (hμν : μ ≪ ν) {f : α -> Real>=0∞}
    (hf : AEMeasurable f ν) {s : Set α} (hs : MeasurableSet s) :
    ∫⁻ x in s, μ.rnDeriv ν x * f x ∂ν = ∫⁻ x in s, f x ∂μ := by
  nth_rw 2 [← Measure.withDensity_rnDeriv_eq μ ν hμν]
  rw [setLIntegral_withDensity_eq_lintegral_mul₀ (measurable_rnDeriv μ ν).aemeasurable hf hs]
  simp only [Pi.mul_apply]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E] [HaveLebesgueDecomposition μ ν]
  [SigmaFinite μ] {f : α -> E}

/--
theorem `integrable_rnDeriv_smul_iff` / 定理 `integrable_rnDeriv_smul_iff`

English:
theorem integrable_rnDeriv_smul_iff
  given: (hμν : μ ≪ ν)
  proof: by
  nth_rw 2 [← withDensity_rnDeriv_eq μ ν hμν]
  rw [← integrable_withDensity_iff_integrable_smul' (E := E)
    (measurable_rnDeriv μ ν) (rnDeriv_lt_top μ ν)]

中文:
定理 integrable_rnDeriv_smul_iff
  条件: (hμν : μ ≪ ν)
  证明: by
  nth_rw 2 [← withDensity_rnDeriv_eq μ ν hμν]
  rw [← integrable_withDensity_iff_integrable_smul' (E := E)
    (measurable_rnDeriv μ ν) (rnDeriv_lt_top μ ν)]

Depends on / 依赖: integrable_withDensity_iff_integrable_smul, measurable_rnDeriv, nth_rw, rnDeriv_lt_top, withDensity_rnDeriv_eq
-/
theorem integrable_rnDeriv_smul_iff (hμν : μ ≪ ν) :
    Integrable (fun x => (μ.rnDeriv ν x).toReal • f x) ν ↔ Integrable f μ := by
  nth_rw 2 [← withDensity_rnDeriv_eq μ ν hμν]
  rw [← integrable_withDensity_iff_integrable_smul' (E := E)
    (measurable_rnDeriv μ ν) (rnDeriv_lt_top μ ν)]

/--
lemma `integrable_toReal_rnDeriv_mul_iff` / 引理 `integrable_toReal_rnDeriv_mul_iff`

English:
lemma integrable_toReal_rnDeriv_mul_iff
  given: (hμν : μ ≪ ν) {f : α -> Real}
  proof: integrable_rnDeriv_smul_iff hμν

中文:
引理 integrable_to实数_rnDeriv_mul_iff
  条件: (hμν : μ ≪ ν) {f : α -> 实数}
  证明: integrable_rnDeriv_smul_iff hμν

Depends on / 依赖: integrable_rnDeriv_smul_iff
-/
lemma integrable_toReal_rnDeriv_mul_iff (hμν : μ ≪ ν) {f : α -> Real} :
    Integrable (fun x => (μ.rnDeriv ν x).toReal * f x) ν ↔ Integrable f μ :=
  integrable_rnDeriv_smul_iff hμν

/--
theorem `integral_rnDeriv_smul` / 定理 `integral_rnDeriv_smul`

English:
theorem integral_rnDeriv_smul
  given: (hμν : μ ≪ ν)
  proof: by
  rw [← integral_withDensity_eq_integral_toReal_smul (measurable_rnDeriv _ _) (rnDeriv_lt_top _ _)]; rw [withDensity_rnDeriv_eq _ _ hμν]

中文:
定理 integral_rnDeriv_smul
  条件: (hμν : μ ≪ ν)
  证明: by
  rw [← integral_withDensity_eq_integral_toReal_smul (measurable_rnDeriv _ _) (rnDeriv_lt_top _ _)]; rw [withDensity_rnDeriv_eq _ _ hμν]

Depends on / 依赖: integral_withDensity_eq_integral_toReal_smul, measurable_rnDeriv, rnDeriv_lt_top, withDensity_rnDeriv_eq
-/
theorem integral_rnDeriv_smul (hμν : μ ≪ ν) :
    ∫ x, (μ.rnDeriv ν x).toReal • f x ∂ν = ∫ x, f x ∂μ := by
  rw [← integral_withDensity_eq_integral_toReal_smul (measurable_rnDeriv _ _) (rnDeriv_lt_top _ _)]; rw [withDensity_rnDeriv_eq _ _ hμν]

/--
lemma `integral_toReal_rnDeriv_mul` / 引理 `integral_toReal_rnDeriv_mul`

English:
lemma integral_toReal_rnDeriv_mul
  given: (hμν : μ ≪ ν) {f : α -> Real}
  proof: integral_rnDeriv_smul hμν

中文:
引理 integral_to实数_rnDeriv_mul
  条件: (hμν : μ ≪ ν) {f : α -> 实数}
  证明: integral_rnDeriv_smul hμν

Depends on / 依赖: integral_rnDeriv_smul
-/
lemma integral_toReal_rnDeriv_mul (hμν : μ ≪ ν) {f : α -> Real} :
    ∫ x, (μ.rnDeriv ν x).toReal * f x ∂ν = ∫ x, f x ∂μ := integral_rnDeriv_smul hμν

/--
lemma `setIntegral_rnDeriv_smul` / 引理 `setIntegral_rnDeriv_smul`

English:
lemma setIntegral_rnDeriv_smul
  given: (hμν : μ ≪ ν) {s : Set α} (hs : MeasurableSet s)
  proof: by
  rw [← setIntegral_withDensity_eq_setIntegral_toReal_smul]; rw [withDensity_rnDeriv_eq _ _ hμν]
  exacts [measurable_rnDeriv _ _, ae_restrict_of_ae (rnDeriv_lt_top _ _), hs]

中文:
引理 set整数egral_rnDeriv_smul
  条件: (hμν : μ ≪ ν) {s : 集合 α} (hs : 可测集 s)
  证明: by
  rw [← setIntegral_withDensity_eq_setIntegral_toReal_smul]; rw [withDensity_rnDeriv_eq _ _ hμν]
  exacts [measurable_rnDeriv _ _, ae_restrict_of_ae (rnDeriv_lt_top _ _), hs]

Depends on / 依赖: ae_restrict_of_ae, exacts, measurable_rnDeriv, rnDeriv_lt_top, setIntegral_withDensity_eq_setIntegral_toReal_smul, withDensity_rnDeriv_eq
-/
lemma setIntegral_rnDeriv_smul (hμν : μ ≪ ν) {s : Set α} (hs : MeasurableSet s) :
    ∫ x in s, (μ.rnDeriv ν x).toReal • f x ∂ν = ∫ x in s, f x ∂μ := by
  rw [← setIntegral_withDensity_eq_setIntegral_toReal_smul]; rw [withDensity_rnDeriv_eq _ _ hμν]
  exacts [measurable_rnDeriv _ _, ae_restrict_of_ae (rnDeriv_lt_top _ _), hs]

/--
lemma `setIntegral_toReal_rnDeriv_mul` / 引理 `setIntegral_toReal_rnDeriv_mul`

English:
lemma setIntegral_toReal_rnDeriv_mul
  given: (hμν : μ ≪ ν) {f : α -> Real} {s : Set α} (hs : MeasurableSet s)
  proof: setIntegral_rnDeriv_smul hμν hs

omit [HaveLebesgueDecomposition μ ν] in

中文:
引理 set整数egral_to实数_rnDeriv_mul
  条件: (hμν : μ ≪ ν) {f : α -> 实数} {s : 集合 α} (hs : 可测集 s)
  证明: setIntegral_rnDeriv_smul hμν hs

omit [HaveLebesgueDecomposition μ ν] in

Depends on / 依赖: setIntegral_rnDeriv_smul
-/
lemma setIntegral_toReal_rnDeriv_mul (hμν : μ ≪ ν) {f : α -> Real} {s : Set α} (hs : MeasurableSet s) :
    ∫ x in s, (μ.rnDeriv ν x).toReal * f x ∂ν = ∫ x in s, f x ∂μ :=
  setIntegral_rnDeriv_smul hμν hs

omit [HaveLebesgueDecomposition μ ν] in
/--
lemma `setIntegral_rnDeriv_smul'` / 引理 `setIntegral_rnDeriv_smul'`

English:
lemma setIntegral_rnDeriv_smul'
  given: [SigmaFinite ν] (hμν : μ ≪ ν) (s : Set α)
  proof: by
  rw [← setIntegral_withDensity_eq_setIntegral_toReal_smul']; rw [withDensity_rnDeriv_eq _ _ hμν]
  exacts [measurable_rnDeriv _ _, ae_restrict_of_ae (rnDeriv_lt_top _ _)]

omit [HaveLebesgueDecomposition μ ν] in

中文:
引理 set整数egral_rnDeriv_smul'
  条件: [σ有限 ν] (hμν : μ ≪ ν) (s : 集合 α)
  证明: by
  rw [← setIntegral_withDensity_eq_setIntegral_toReal_smul']; rw [withDensity_rnDeriv_eq _ _ hμν]
  exacts [measurable_rnDeriv _ _, ae_restrict_of_ae (rnDeriv_lt_top _ _)]

omit [HaveLebesgueDecomposition μ ν] in

Depends on / 依赖: ae_restrict_of_ae, exacts, measurable_rnDeriv, rnDeriv_lt_top, setIntegral_withDensity_eq_setIntegral_toReal_smul, withDensity_rnDeriv_eq
-/
lemma setIntegral_rnDeriv_smul' [SigmaFinite ν] (hμν : μ ≪ ν) (s : Set α) :
    ∫ x in s, (μ.rnDeriv ν x).toReal • f x ∂ν = ∫ x in s, f x ∂μ := by
  rw [← setIntegral_withDensity_eq_setIntegral_toReal_smul']; rw [withDensity_rnDeriv_eq _ _ hμν]
  exacts [measurable_rnDeriv _ _, ae_restrict_of_ae (rnDeriv_lt_top _ _)]

omit [HaveLebesgueDecomposition μ ν] in
/--
lemma `setIntegral_toReal_rnDeriv_mul'` / 引理 `setIntegral_toReal_rnDeriv_mul'`

English:
lemma setIntegral_toReal_rnDeriv_mul'
  given: [SigmaFinite ν] (hμν : μ ≪ ν) (f : α -> Real) (s : Set α)
  proof: setIntegral_rnDeriv_smul' hμν s

中文:
引理 set整数egral_to实数_rnDeriv_mul'
  条件: [σ有限 ν] (hμν : μ ≪ ν) (f : α -> 实数) (s : 集合 α)
  证明: setIntegral_rnDeriv_smul' hμν s

Depends on / 依赖: setIntegral_rnDeriv_smul
-/
lemma setIntegral_toReal_rnDeriv_mul' [SigmaFinite ν] (hμν : μ ≪ ν) (f : α -> Real) (s : Set α) :
    ∫ x in s, (μ.rnDeriv ν x).toReal * f x ∂ν = ∫ x in s, f x ∂μ :=
  setIntegral_rnDeriv_smul' hμν s

end IntegralRNDerivMul

section Conv

open Measure

variable {G : Type*} [Group G] {mG : MeasurableSpace G} [MeasurableMul₂ G] [MeasurableInv G]
  {μ : Measure G} [IsMulLeftInvariant μ]

@[to_additive]
/--
theorem `mconv_eq_withDensity_mlconvolution_rnDeriv` / 定理 `mconv_eq_withDensity_mlconvolution_rnDeriv`

English:
theorem mconv_eq_withDensity_mlconvolution_rnDeriv
  statement: [SFinite μ] {ν₁ ν₂ : Measure G}
  proof: by
  rw [← mconv_withDensity_eq_mlconvolution (by fun_prop) (by fun_prop)]; rw [withDensity_rnDeriv_eq _ _ hν₁]; rw [withDensity_rnDeriv_eq _ _ hν₂]

@[to_additive]

中文:
定理 mconv_eq_withDensity_mlconvolution_rnDeriv
  结论: [SFinite μ] {ν₁ ν₂ : 测度 G}
  证明: by
  rw [← mconv_withDensity_eq_mlconvolution (by fun_prop) (by fun_prop)]; rw [withDensity_rnDeriv_eq _ _ hν₁]; rw [withDensity_rnDeriv_eq _ _ hν₂]

@[to_additive]

Depends on / 依赖: fun_prop, mconv_withDensity_eq_mlconvolution, withDensity_rnDeriv_eq
-/
theorem mconv_eq_withDensity_mlconvolution_rnDeriv [SFinite μ] {ν₁ ν₂ : Measure G}
    [ν₁.HaveLebesgueDecomposition μ] [ν₂.HaveLebesgueDecomposition μ]
    (hν₁ : ν₁ ≪ μ) (hν₂ : ν₂ ≪ μ) :
    ν₁ ∗ₘ ν₂ = μ.withDensity (ν₁.rnDeriv μ ⋆ₘₗ[μ] ν₂.rnDeriv μ) := by
  rw [← mconv_withDensity_eq_mlconvolution (by fun_prop) (by fun_prop)]; rw [withDensity_rnDeriv_eq _ _ hν₁]; rw [withDensity_rnDeriv_eq _ _ hν₂]

@[to_additive]
/--
theorem `HaveLebesgueDecomposition.mconv` / 定理 `HaveLebesgueDecomposition.mconv`

English:
theorem HaveLebesgueDecomposition.mconv
  statement: [SFinite μ] {ν₁ ν₂ : Measure G}
  proof: ⟨⟨0, (ν₁.rnDeriv μ) ⋆ₘₗ[μ] (ν₂.rnDeriv μ)⟩, by fun_prop, by simp,
    by simpa using mconv_eq_withDensity_mlconvolution_rnDeriv hν₁ hν₂⟩

@[to_additive]

中文:
定理 有Lebesgue分解.mconv
  结论: [SFinite μ] {ν₁ ν₂ : 测度 G}
  证明: ⟨⟨0, (ν₁.rnDeriv μ) ⋆ₘₗ[μ] (ν₂.rnDeriv μ)⟩, by fun_prop, by simp,
    by simpa using mconv_eq_withDensity_mlconvolution_rnDeriv hν₁ hν₂⟩

@[to_additive]

Depends on / 依赖: fun_prop, mconv_eq_withDensity_mlconvolution_rnDeriv, rnDeriv
-/
theorem HaveLebesgueDecomposition.mconv [SFinite μ] {ν₁ ν₂ : Measure G}
    [ν₁.HaveLebesgueDecomposition μ] [ν₂.HaveLebesgueDecomposition μ]
    (hν₁ : ν₁ ≪ μ) (hν₂ : ν₂ ≪ μ) : (ν₁ ∗ₘ ν₂).HaveLebesgueDecomposition μ :=
  ⟨⟨0, (ν₁.rnDeriv μ) ⋆ₘₗ[μ] (ν₂.rnDeriv μ)⟩, by fun_prop, by simp,
    by simpa using mconv_eq_withDensity_mlconvolution_rnDeriv hν₁ hν₂⟩

@[to_additive]
/--
theorem `rnDeriv_mconv` / 定理 `rnDeriv_mconv`

English:
theorem rnDeriv_mconv
  statement: [SFinite μ] {ν₁ ν₂ : Measure G} [IsFiniteMeasure ν₁] [IsFiniteMeasure ν₂]
  proof: by
  have := HaveLebesgueDecomposition.mconv hν₁ hν₂
  rw [← withDensity_eq_iff (by fun_prop) (by fun_prop)]; rw [withDensity_rnDeriv_eq _ _ (mconv_absolutelyContinuous hν₂)]; rw [mconv_eq_withDensity_mlconvolution_rnDeriv hν₁ hν₂]
  exact (lintegral_rnDeriv_lt_top (ν₁ ∗ₘ ν₂) μ).ne

@[to_additive]

中文:
定理 rnDeriv_mconv
  结论: [SFinite μ] {ν₁ ν₂ : 测度 G} [是有限测度 ν₁] [是有限测度 ν₂]
  证明: by
  have := HaveLebesgueDecomposition.mconv hν₁ hν₂
  rw [← withDensity_eq_iff (by fun_prop) (by fun_prop)]; rw [withDensity_rnDeriv_eq _ _ (mconv_absolutelyContinuous hν₂)]; rw [mconv_eq_withDensity_mlconvolution_rnDeriv hν₁ hν₂]
  exact (lintegral_rnDeriv_lt_top (ν₁ ∗ₘ ν₂) μ).ne

@[to_additive]

Depends on / 依赖: HaveLebesgueDecomposition, HaveLebesgueDecomposition.mconv, fun_prop, lintegral_rnDeriv_lt_top, mconv_absolutelyContinuous, mconv_eq_withDensity_mlconvolution_rnDeriv, withDensity_eq_iff, withDensity_rnDeriv_eq
-/
theorem rnDeriv_mconv [SFinite μ] {ν₁ ν₂ : Measure G} [IsFiniteMeasure ν₁] [IsFiniteMeasure ν₂]
    [ν₁.HaveLebesgueDecomposition μ] [ν₂.HaveLebesgueDecomposition μ]
    (hν₁ : ν₁ ≪ μ) (hν₂ : ν₂ ≪ μ) :
    (ν₁ ∗ₘ ν₂).rnDeriv μ =ᵐ[μ] (ν₁.rnDeriv μ) ⋆ₘₗ[μ] (ν₂.rnDeriv μ) := by
  have := HaveLebesgueDecomposition.mconv hν₁ hν₂
  rw [← withDensity_eq_iff (by fun_prop) (by fun_prop)]; rw [withDensity_rnDeriv_eq _ _ (mconv_absolutelyContinuous hν₂)]; rw [mconv_eq_withDensity_mlconvolution_rnDeriv hν₁ hν₂]
  exact (lintegral_rnDeriv_lt_top (ν₁ ∗ₘ ν₂) μ).ne

@[to_additive]
/--
theorem `rnDeriv_mconv'` / 定理 `rnDeriv_mconv'`

English:
theorem rnDeriv_mconv'
  statement: [SigmaFinite μ] {ν₁ ν₂ : Measure G} [SigmaFinite ν₁] [SigmaFinite ν₂]
  proof: by
  rw [← withDensity_eq_iff_of_sigmaFinite (by fun_prop) (by fun_prop)]; rw [← mconv_eq_withDensity_mlconvolution_rnDeriv hν₁ hν₂]; rw [withDensity_rnDeriv_eq _ _ (mconv_absolutelyContinuous hν₂)]

中文:
定理 rnDeriv_mconv'
  结论: [σ有限 μ] {ν₁ ν₂ : 测度 G} [σ有限 ν₁] [σ有限 ν₂]
  证明: by
  rw [← withDensity_eq_iff_of_sigmaFinite (by fun_prop) (by fun_prop)]; rw [← mconv_eq_withDensity_mlconvolution_rnDeriv hν₁ hν₂]; rw [withDensity_rnDeriv_eq _ _ (mconv_absolutelyContinuous hν₂)]

Depends on / 依赖: fun_prop, mconv_absolutelyContinuous, mconv_eq_withDensity_mlconvolution_rnDeriv, withDensity_eq_iff_of_sigmaFinite, withDensity_rnDeriv_eq
-/
theorem rnDeriv_mconv' [SigmaFinite μ] {ν₁ ν₂ : Measure G} [SigmaFinite ν₁] [SigmaFinite ν₂]
    (hν₁ : ν₁ ≪ μ) (hν₂ : ν₂ ≪ μ) :
    (ν₁ ∗ₘ ν₂).rnDeriv μ =ᵐ[μ] (ν₁.rnDeriv μ) ⋆ₘₗ[μ] (ν₂.rnDeriv μ) := by
  rw [← withDensity_eq_iff_of_sigmaFinite (by fun_prop) (by fun_prop)]; rw [← mconv_eq_withDensity_mlconvolution_rnDeriv hν₁ hν₂]; rw [withDensity_rnDeriv_eq _ _ (mconv_absolutelyContinuous hν₂)]

end Conv

end MeasureTheory
