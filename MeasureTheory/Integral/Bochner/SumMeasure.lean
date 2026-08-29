/-
Copyright (c) 2026 Etienne Marion. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Etienne Marion
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn

import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Integral with respect to a sum of measures

In this file we prove that a function `f` is integrable with respect to a countable sum of measures
`Measure.sum μ` if and only if `f` is integrable with respect to each `μ i` and the sequence
`fun i ↦ ∫ x, ‖f x‖ ∂μ i` is summable. We then show that under this integrability condition,
`∫ x, f x ∂Measure.sum μ = ∑' i, ∫ f x ∂μ i`.

We specialize these results to the case where each measure is a Dirac mass,
i.e. `μ i = (c i) • .dirac (x i)`.

Finally we compute integrals over countable and finite spaces or sets.

## Main statements

* `integrable_sum_measure_iff`: A function `f` is integrable with respect to a countable sum
  of measures `Measure.sum μ` if and only if `f` is integrable with respect to each `μ i` and the
  sequence `fun i ↦ ∫ x, ‖f x‖ ∂μ i` is summable.
* `integrable_sum_dirac_iff`: A function `f` is integrable with respect to a countable sum
  of Dirac masses `Measure.sum (fun i ↦ (c i) • Measure.dirac (x i))` if and only if
  the sequence `fun i ↦ (c i).toReal * ‖f (x i)‖` is summable.
* `hasSum_integral_measure`: If `f` is integrable with respect to `Measure.sum μ`,
  then the sequence `fun i ↦ ∫ x, f x ∂μ i` is summable and its sum is `∫ x, f x ∂Measure.sum μ`.
* `integral_sum_dirac_eq_tsum`: If the sequence `fun i ↦ (c i).toReal * ‖f (x i)‖` is summable,
  then `∑' i, (c i).toReal • f (x i) = ∫ x, f x, ∂Measure.sum (fun i ↦ (c i) • .dirac (x i))`.

## Tags

sum of measures, integral, Dirac mass
-/

public section

open Filter Set
open scoped ENNReal NNReal Topology

namespace MeasureTheory

variable {ι X E : Type*} [Countable ι] {mX : MeasurableSpace X} [NormedAddCommGroup E]
  {μ : ι -> Measure X} {f : X -> E}

section Integrable

/--
lemma `integrable_sum_measure` / 引理 `integrable_sum_measure`

English:
lemma integrable_sum_measure
  proof: by
  refine ⟨aestronglyMeasurable_sum_measure_iff.mpr fun i => (hf i).aestronglyMeasurable, ?_⟩
  · rw [HasFiniteIntegral, lintegral_sum_measure]
    convert! h.tsum_ofReal_lt_top with i
    rw [ofReal_integral_eq_lintegral_ofReal (hf i).norm]
    · simp_rw [ofReal_norm]
    · exact ae_of_all _ fun _ => by positivity

omit [Countable ι] in

中文:
引理 integrable_sum_measure
  证明: by
  refine ⟨aestronglyMeasurable_sum_measure_iff.mpr fun i => (hf i).aestronglyMeasurable, ?_⟩
  · rw [HasFiniteIntegral, lintegral_sum_measure]
    convert! h.tsum_ofReal_lt_top with i
    rw [ofReal_integral_eq_lintegral_ofReal (hf i).norm]
    · simp_rw [ofReal_norm]
    · exact ae_of_all _ fun _ => by positivity

omit [Countable ι] in

Depends on / 依赖: HasFiniteIntegral, ae_of_all, aestronglyMeasurable, aestronglyMeasurable_sum_measure_iff, aestronglyMeasurable_sum_measure_iff.mpr, convert, h.tsum_ofReal_lt_top, lintegral_sum_measure, ofReal_integral_eq_lintegral_ofReal, ofReal_norm, simp_rw, tsum_ofReal_lt_top
-/
lemma integrable_sum_measure
    (hf : forall i, Integrable f (μ i)) (h : Summable (fun i => ∫ x, ‖f x‖ ∂μ i)) :
    Integrable f (Measure.sum μ) := by
  refine ⟨aestronglyMeasurable_sum_measure_iff.mpr fun i => (hf i).aestronglyMeasurable, ?_⟩
  · rw [HasFiniteIntegral, lintegral_sum_measure]
    convert! h.tsum_ofReal_lt_top with i
    rw [ofReal_integral_eq_lintegral_ofReal (hf i).norm]
    · simp_rw [ofReal_norm]
    · exact ae_of_all _ fun _ => by positivity

omit [Countable ι] in
/--
lemma `Integrable.summable_integral` / 引理 `Integrable.summable_integral`

English:
lemma Integrable.summable_integral
  given: (hf : Integrable f (Measure.sum μ))
  proof: by
  convert! ENNReal.summable_toReal (f := fun i => ∫⁻ x, ‖f x‖ₑ ∂μ i) ?_ with i
  · rw [← integral_toReal ?_ (by simp)]
    · simp
    · exact (hf.aestronglyMeasurable.mono_measure (Measure.le_sum _ i)).enorm
  rw [← lintegral_sum_measure]
  exact hf.2.ne

中文:
引理 可积.summable_integral
  条件: (hf : 可积 f (测度.求和 μ))
  证明: by
  convert! ENNReal.summable_toReal (f := fun i => ∫⁻ x, ‖f x‖ₑ ∂μ i) ?_ with i
  · rw [← integral_toReal ?_ (by simp)]
    · simp
    · exact (hf.aestronglyMeasurable.mono_measure (Measure.le_sum _ i)).enorm
  rw [← lintegral_sum_measure]
  exact hf.2.ne

Depends on / 依赖: ENNReal, ENNReal.summable_toReal, Measure, Measure.le_sum, aestronglyMeasurable, convert, hf.aestronglyMeasurable.mono_measure, integral_toReal, le_sum, lintegral_sum_measure, mono_measure, summable_toReal
-/
lemma Integrable.summable_integral (hf : Integrable f (Measure.sum μ)) :
    Summable (fun i => ∫ x, ‖f x‖ ∂μ i) := by
  convert! ENNReal.summable_toReal (f := fun i => ∫⁻ x, ‖f x‖ₑ ∂μ i) ?_ with i
  · rw [← integral_toReal ?_ (by simp)]
    · simp
    · exact (hf.aestronglyMeasurable.mono_measure (Measure.le_sum _ i)).enorm
  rw [← lintegral_sum_measure]
  exact hf.2.ne

/--
lemma `integrable_sum_measure_iff` / 引理 `integrable_sum_measure_iff`

English:
lemma integrable_sum_measure_iff
  proof: ⟨fun i => h.mono_measure (Measure.le_sum _ i), h.summable_integral⟩
  mpr h := integrable_sum_measure h.1 h.2

中文:
引理 integrable_sum_measure_iff
  证明: ⟨fun i => h.mono_measure (Measure.le_sum _ i), h.summable_integral⟩
  mpr h := integrable_sum_measure h.1 h.2

Depends on / 依赖: Measure, Measure.le_sum, h.mono_measure, h.summable_integral, le_sum, mono_measure, summable_integral
-/
lemma integrable_sum_measure_iff :
    Integrable f (Measure.sum μ) ↔
      (forall i, Integrable f (μ i)) ∧ Summable (fun i => ∫ x, ‖f x‖ ∂μ i) where
  mp h := ⟨fun i => h.mono_measure (Measure.le_sum _ i), h.summable_integral⟩
  mpr h := integrable_sum_measure h.1 h.2

section Dirac

variable [MeasurableSingletonClass X] {x : ι -> X} {c : ι -> Real>=0∞}

/--
lemma `integrable_sum_dirac` / 引理 `integrable_sum_dirac`

English:
lemma integrable_sum_dirac
  given: (hc : forall i, c i != ∞) (h : Summable (fun i => (c i).toReal * ‖f (x i)‖))
  proof: integrable_sum_measure (fun i => (integrable_dirac (by simp)).smul_measure (hc i))
    (by simpa using h)

omit [Countable ι] in

中文:
引理 integrable_sum_dirac
  条件: (hc : 对任意 i, c i != ∞) (h : Summable (fun i => (c i).to实数 * ‖f (x i)‖))
  证明: integrable_sum_measure (fun i => (integrable_dirac (by simp)).smul_measure (hc i))
    (by simpa using h)

omit [Countable ι] in

Depends on / 依赖: integrable_dirac, integrable_sum_measure, smul_measure
-/
lemma integrable_sum_dirac (hc : forall i, c i != ∞) (h : Summable (fun i => (c i).toReal * ‖f (x i)‖)) :
    Integrable f (Measure.sum (fun i => (c i) • .dirac (x i))) :=
  integrable_sum_measure (fun i => (integrable_dirac (by simp)).smul_measure (hc i))
    (by simpa using h)

omit [Countable ι] in
/--
lemma `Integrable.summable_of_dirac` / 引理 `Integrable.summable_of_dirac`

English:
lemma Integrable.summable_of_dirac
  proof: by
  simpa using hf.summable_integral

中文:
引理 可积.summable_of_dirac
  证明: by
  simpa using hf.summable_integral

Depends on / 依赖: hf.summable_integral, summable_integral
-/
lemma Integrable.summable_of_dirac
    (hf : Integrable f (Measure.sum (fun i => (c i) • .dirac (x i)))) :
    Summable (fun i => (c i).toReal * ‖f (x i)‖) := by
  simpa using hf.summable_integral

/--
lemma `integrable_sum_dirac_iff` / 引理 `integrable_sum_dirac_iff`

English:
lemma integrable_sum_dirac_iff
  given: (hc : forall i, c i != ∞)
  proof: h.summable_of_dirac
  mpr h := integrable_sum_dirac hc h

中文:
引理 integrable_sum_dirac_iff
  条件: (hc : 对任意 i, c i != ∞)
  证明: h.summable_of_dirac
  mpr h := integrable_sum_dirac hc h

Depends on / 依赖: h.summable_of_dirac, summable_of_dirac
-/
lemma integrable_sum_dirac_iff (hc : forall i, c i != ∞) :
    Integrable f (Measure.sum (fun i => (c i) • .dirac (x i))) ↔
      Summable (fun i => (c i).toReal * ‖f (x i)‖) where
  mp h := h.summable_of_dirac
  mpr h := integrable_sum_dirac hc h

end Dirac

end Integrable

section Integral

variable [NormedSpace Real E]

omit [Countable ι] in
/--
theorem `hasSum_integral_measure` / 定理 `hasSum_integral_measure`

English:
theorem hasSum_integral_measure
  given: (hf : Integrable f (Measure.sum μ))
  proof: by
  have hfi : forall i, Integrable f (μ i) := fun i => hf.mono_measure (Measure.le_sum _ _)
  simp only [HasSum, ← integral_finsetSum_measure fun i _ => hfi i]
  refine Metric.nhds_basis_ball.tendsto_right_iff.mpr fun ε ε0 => ?_
  lift ε to Real>=0 using ε0.le
  have hf_lt : (∫⁻ x, ‖f x‖ₑ ∂Measure.sum μ) < ∞ := hf.2
  have hmem : forallᶠ y in 𝓝 (∫⁻ x, ‖f x‖ₑ ∂Measure.sum μ), (∫⁻ x, ‖f x‖ₑ ∂Measure.sum μ) < y + ε := by
    refine tendsto_id.add tendsto_const_nhds (lt_mem_nhds (α := Real>=0∞) <| ENNReal.lt_add_right ?_ ?_)
    exacts [hf_lt.ne, ENNReal.coe_ne_zero.2 (NNReal.coe_ne_zero.1 ε0.ne')]
  refine ((hasSum_lintegral_measure (fun x => ‖f x‖ₑ) μ).eventually hmem).mono fun s hs => ?_
  obtain ⟨ν, hν⟩ : exists ν, (∑ i in s, μ i) + ν = Measure.sum μ := by
    refine ⟨Measure.sum fun i : ↥(sᶜ : Set ι) => μ i, ?_⟩
    simpa only [← Measure.sum_coe_finset] using! Measure.sum_add_sum_compl (s : Set ι) μ
  rw [Metric.mem_ball]; rw [← coe_nndist]; rw [NNReal.coe_lt_coe]; rw [← ENNReal.coe_lt_coe]; rw [← hν]
  rw [← hν]; rw [integrable_add_measure] at hf
  refine (nndist_integral_add_measure_le_lintegral hf.1 hf.2).trans_lt ?_
  rw [← hν]; rw [lintegral_add_measure]; rw [lintegral_finsetSum_measure] at hs
  exact lt_of_add_lt_add_left hs

omit [Countable ι] in

中文:
定理 hasSum_integral_measure
  条件: (hf : 可积 f (测度.求和 μ))
  证明: by
  have hfi : forall i, Integrable f (μ i) := fun i => hf.mono_measure (Measure.le_sum _ _)
  simp only [HasSum, ← integral_finsetSum_measure fun i _ => hfi i]
  refine Metric.nhds_basis_ball.tendsto_right_iff.mpr fun ε ε0 => ?_
  lift ε to Real>=0 using ε0.le
  have hf_lt : (∫⁻ x, ‖f x‖ₑ ∂Measure.sum μ) < ∞ := hf.2
  have hmem : forallᶠ y in 𝓝 (∫⁻ x, ‖f x‖ₑ ∂Measure.sum μ), (∫⁻ x, ‖f x‖ₑ ∂Measure.sum μ) < y + ε := by
    refine tendsto_id.add tendsto_const_nhds (lt_mem_nhds (α := Real>=0∞) <| ENNReal.lt_add_right ?_ ?_)
    exacts [hf_lt.ne, ENNReal.coe_ne_zero.2 (NNReal.coe_ne_zero.1 ε0.ne')]
  refine ((hasSum_lintegral_measure (fun x => ‖f x‖ₑ) μ).eventually hmem).mono fun s hs => ?_
  obtain ⟨ν, hν⟩ : exists ν, (∑ i in s, μ i) + ν = Measure.sum μ := by
    refine ⟨Measure.sum fun i : ↥(sᶜ : Set ι) => μ i, ?_⟩
    simpa only [← Measure.sum_coe_finset] using! Measure.sum_add_sum_compl (s : Set ι) μ
  rw [Metric.mem_ball]; rw [← coe_nndist]; rw [NNReal.coe_lt_coe]; rw [← ENNReal.coe_lt_coe]; rw [← hν]
  rw [← hν]; rw [integrable_add_measure] at hf
  refine (nndist_integral_add_measure_le_lintegral hf.1 hf.2).trans_lt ?_
  rw [← hν]; rw [lintegral_add_measure]; rw [lintegral_finsetSum_measure] at hs
  exact lt_of_add_lt_add_left hs

omit [Countable ι] in

Depends on / 依赖: ENNReal, ENNReal.lt_add_, HasSum, Integrable, Measure, Measure.le_sum, Measure.sum, Metric, Metric.nhds_basis_ball.tendsto_right_iff.mpr, hf.mono_measure, hf_lt, integral_finsetSum_measure, le_sum, lt_add_, lt_mem_nhds, mono_measure, nhds_basis_ball, tendsto_const_nhds, tendsto_id, tendsto_id.add
-/
theorem hasSum_integral_measure (hf : Integrable f (Measure.sum μ)) :
    HasSum (fun i => ∫ x, f x ∂μ i) (∫ x, f x ∂Measure.sum μ) := by
  have hfi : forall i, Integrable f (μ i) := fun i => hf.mono_measure (Measure.le_sum _ _)
  simp only [HasSum, ← integral_finsetSum_measure fun i _ => hfi i]
  refine Metric.nhds_basis_ball.tendsto_right_iff.mpr fun ε ε0 => ?_
  lift ε to Real>=0 using ε0.le
  have hf_lt : (∫⁻ x, ‖f x‖ₑ ∂Measure.sum μ) < ∞ := hf.2
  have hmem : forallᶠ y in 𝓝 (∫⁻ x, ‖f x‖ₑ ∂Measure.sum μ), (∫⁻ x, ‖f x‖ₑ ∂Measure.sum μ) < y + ε := by
    refine tendsto_id.add tendsto_const_nhds (lt_mem_nhds (α := Real>=0∞) <| ENNReal.lt_add_right ?_ ?_)
    exacts [hf_lt.ne, ENNReal.coe_ne_zero.2 (NNReal.coe_ne_zero.1 ε0.ne')]
  refine ((hasSum_lintegral_measure (fun x => ‖f x‖ₑ) μ).eventually hmem).mono fun s hs => ?_
  obtain ⟨ν, hν⟩ : exists ν, (∑ i in s, μ i) + ν = Measure.sum μ := by
    refine ⟨Measure.sum fun i : ↥(sᶜ : Set ι) => μ i, ?_⟩
    simpa only [← Measure.sum_coe_finset] using! Measure.sum_add_sum_compl (s : Set ι) μ
  rw [Metric.mem_ball]; rw [← coe_nndist]; rw [NNReal.coe_lt_coe]; rw [← ENNReal.coe_lt_coe]; rw [← hν]
  rw [← hν]; rw [integrable_add_measure] at hf
  refine (nndist_integral_add_measure_le_lintegral hf.1 hf.2).trans_lt ?_
  rw [← hν]; rw [lintegral_add_measure]; rw [lintegral_finsetSum_measure] at hs
  exact lt_of_add_lt_add_left hs

omit [Countable ι] in
/--
theorem `integral_sum_measure` / 定理 `integral_sum_measure`

English:
theorem integral_sum_measure
  given: (hf : Integrable f (Measure.sum μ))
  proof: (hasSum_integral_measure hf).tsum_eq.symm

中文:
定理 integral_sum_measure
  条件: (hf : 可积 f (测度.求和 μ))
  证明: (hasSum_integral_measure hf).tsum_eq.symm

Depends on / 依赖: hasSum_integral_measure, tsum_eq, tsum_eq.symm
-/
theorem integral_sum_measure (hf : Integrable f (Measure.sum μ)) :
    ∫ x, f x ∂Measure.sum μ = ∑' i, ∫ x, f x ∂μ i :=
  (hasSum_integral_measure hf).tsum_eq.symm

section Dirac

variable [MeasurableSingletonClass X] {x : ι -> X} {c : ι -> Real>=0∞}

/--
lemma `integral_sum_dirac` / 引理 `integral_sum_dirac`

English:
lemma integral_sum_dirac
  given: [FiniteDimensional Real E] (hc : forall i, c i != ∞)
  proof: by
  by_cases hf : Integrable f (.sum (fun i => (c i) • .dirac (x i)))
  · rw [integral_sum_measure hf]
    congr with i
    rw [integral_smul_measure]; rw [integral_dirac]
  · rw [integral_undef hf, tsum_eq_zero_of_not_summable]
    apply mt Summable.norm
    convert! mt (integrable_sum_dirac hc) hf
    simp [norm_smul]

中文:
引理 integral_sum_dirac
  条件: [有限维 实数 E] (hc : 对任意 i, c i != ∞)
  证明: by
  by_cases hf : Integrable f (.sum (fun i => (c i) • .dirac (x i)))
  · rw [integral_sum_measure hf]
    congr with i
    rw [integral_smul_measure]; rw [integral_dirac]
  · rw [integral_undef hf, tsum_eq_zero_of_not_summable]
    apply mt Summable.norm
    convert! mt (integrable_sum_dirac hc) hf
    simp [norm_smul]

Depends on / 依赖: Integrable, Summable, Summable.norm, convert, integrable_sum_dirac, integral_dirac, integral_smul_measure, integral_sum_measure, integral_undef, norm_smul, tsum_eq_zero_of_not_summable
-/
lemma integral_sum_dirac [FiniteDimensional Real E] (hc : forall i, c i != ∞) :
    ∫ x, f x ∂Measure.sum (fun i => (c i) • .dirac (x i)) = ∑' i, (c i).toReal • f (x i) := by
  by_cases hf : Integrable f (.sum (fun i => (c i) • .dirac (x i)))
  · rw [integral_sum_measure hf]
    congr with i
    rw [integral_smul_measure]; rw [integral_dirac]
  · rw [integral_undef hf, tsum_eq_zero_of_not_summable]
    apply mt Summable.norm
    convert! mt (integrable_sum_dirac hc) hf
    simp [norm_smul]

/--
lemma `hasSum_integral_sum_dirac` / 引理 `hasSum_integral_sum_dirac`

English:
lemma hasSum_integral_sum_dirac
  statement: [CompleteSpace E] (hc : forall i, c i != ∞)
  proof: by
  simpa using hasSum_integral_measure (integrable_sum_dirac hc hf)

中文:
引理 hasSum_integral_sum_dirac
  结论: [完备空间 E] (hc : 对任意 i, c i != ∞)
  证明: by
  simpa using hasSum_integral_measure (integrable_sum_dirac hc hf)

Depends on / 依赖: hasSum_integral_measure, integrable_sum_dirac
-/
lemma hasSum_integral_sum_dirac [CompleteSpace E] (hc : forall i, c i != ∞)
    (hf : Summable (fun i => (c i).toReal * ‖f (x i)‖)) :
    HasSum (fun i => (c i).toReal • f (x i))
      (∫ x, f x ∂Measure.sum (fun i => (c i) • .dirac (x i))) := by
  simpa using hasSum_integral_measure (integrable_sum_dirac hc hf)

/--
lemma `integral_sum_dirac_eq_tsum` / 引理 `integral_sum_dirac_eq_tsum`

English:
lemma integral_sum_dirac_eq_tsum
  statement: [CompleteSpace E] (hc : forall i, c i != ∞)
  proof: (hasSum_integral_sum_dirac hc hf).tsum_eq.symm

中文:
引理 integral_sum_dirac_eq_tsum
  结论: [完备空间 E] (hc : 对任意 i, c i != ∞)
  证明: (hasSum_integral_sum_dirac hc hf).tsum_eq.symm

Depends on / 依赖: hasSum_integral_sum_dirac, tsum_eq, tsum_eq.symm
-/
lemma integral_sum_dirac_eq_tsum [CompleteSpace E] (hc : forall i, c i != ∞)
    (hf : Summable (fun i => (c i).toReal * ‖f (x i)‖)) :
    ∫ x, f x ∂Measure.sum (fun i => (c i) • .dirac (x i)) = ∑' i, (c i).toReal • f (x i) :=
  (hasSum_integral_sum_dirac hc hf).tsum_eq.symm

end Dirac

section DiscreteSpace

variable [CompleteSpace E] [MeasurableSingletonClass X] {μ : Measure X}

/--
theorem `integral_countable` / 定理 `integral_countable`

English:
theorem integral_countable
  given: [Countable X] (hf : Integrable f μ)
  proof: by
  rw [← Measure.sum_smul_dirac μ] at hf
  rw [← Measure.sum_smul_dirac μ]; rw [integral_sum_measure hf]
  congr 1 with a : 1
  rw [integral_smul_measure]; rw [integral_dirac]; rw [Measure.sum_smul_dirac]; rw [measureReal_def]

@[deprecated (since := "2026-03-09")] alias integral_countable' := integral_countable

中文:
定理 integral_countable
  条件: [可数 X] (hf : 可积 f μ)
  证明: by
  rw [← Measure.sum_smul_dirac μ] at hf
  rw [← Measure.sum_smul_dirac μ]; rw [integral_sum_measure hf]
  congr 1 with a : 1
  rw [integral_smul_measure]; rw [integral_dirac]; rw [Measure.sum_smul_dirac]; rw [measureReal_def]

@[deprecated (since := "2026-03-09")] alias integral_countable' := integral_countable

Depends on / 依赖: Measure, Measure.sum_smul_dirac, integral_dirac, integral_smul_measure, integral_sum_measure, measureReal_def, sum_smul_dirac
-/
theorem integral_countable [Countable X] (hf : Integrable f μ) :
    ∫ x, f x ∂μ = ∑' x, μ.real {x} • f x := by
  rw [← Measure.sum_smul_dirac μ] at hf
  rw [← Measure.sum_smul_dirac μ]; rw [integral_sum_measure hf]
  congr 1 with a : 1
  rw [integral_smul_measure]; rw [integral_dirac]; rw [Measure.sum_smul_dirac]; rw [measureReal_def]

@[deprecated (since := "2026-03-09")] alias integral_countable' := integral_countable

/--
theorem `setIntegral_countable` / 定理 `setIntegral_countable`

English:
theorem setIntegral_countable
  given: (f : X -> E) {s : Set X} (hs : s.Countable) (hf : IntegrableOn f s μ)
  proof: by
  have hi : Countable { x // x in s } := Iff.mpr countable_coe_iff hs
  have hf' : Integrable (fun (x : s) => f x) (Measure.comap Subtype.val μ) := by
    rw [IntegrableOn]; rw [← map_comap_subtype_coe]; rw [integrable_map_measure] at hf
    · apply hf
    · exact Integrable.aestronglyMeasurable hf
    · exact Measurable.aemeasurable measurable_subtype_coe
    · exact Countable.measurableSet hs
  rw [← integral_subtype_comap hs.measurableSet]; rw [integral_countable hf']
  congr 1 with a : 1
  rw [measureReal_def]; rw [Measure.comap_apply Subtype.val Subtype.coe_injective
    (fun s' hs' => MeasurableSet.subtype_image (Countable.measurableSet hs) hs') _
    (MeasurableSet.singleton a)]
  simp [measureReal_def]

中文:
定理 set整数egral_countable
  条件: (f : X -> E) {s : 集合 X} (hs : s.可数) (hf : 整数egrableOn f s μ)
  证明: by
  have hi : Countable { x // x in s } := Iff.mpr countable_coe_iff hs
  have hf' : Integrable (fun (x : s) => f x) (Measure.comap Subtype.val μ) := by
    rw [IntegrableOn]; rw [← map_comap_subtype_coe]; rw [integrable_map_measure] at hf
    · apply hf
    · exact Integrable.aestronglyMeasurable hf
    · exact Measurable.aemeasurable measurable_subtype_coe
    · exact Countable.measurableSet hs
  rw [← integral_subtype_comap hs.measurableSet]; rw [integral_countable hf']
  congr 1 with a : 1
  rw [measureReal_def]; rw [Measure.comap_apply Subtype.val Subtype.coe_injective
    (fun s' hs' => MeasurableSet.subtype_image (Countable.measurableSet hs) hs') _
    (MeasurableSet.singleton a)]
  simp [measureReal_def]

Depends on / 依赖: Countable, Countable.measurableSet, Iff.mpr, Integrable, Integrable.aestronglyMeasurable, IntegrableOn, Measurable, Measurable.aemeasurable, Measure, Measure.comap, Subtype, Subtype.val, aemeasurable, aestronglyMeasurable, countable_coe_iff, hs.measurableSet, integrable_map_measure, integral_countable, integral_subtype_comap, map_comap_subtype_coe
-/
theorem setIntegral_countable (f : X -> E) {s : Set X} (hs : s.Countable) (hf : IntegrableOn f s μ) :
    ∫ x in s, f x ∂μ = ∑' x : s, μ.real {(x : X)} • f x := by
  have hi : Countable { x // x in s } := Iff.mpr countable_coe_iff hs
  have hf' : Integrable (fun (x : s) => f x) (Measure.comap Subtype.val μ) := by
    rw [IntegrableOn]; rw [← map_comap_subtype_coe]; rw [integrable_map_measure] at hf
    · apply hf
    · exact Integrable.aestronglyMeasurable hf
    · exact Measurable.aemeasurable measurable_subtype_coe
    · exact Countable.measurableSet hs
  rw [← integral_subtype_comap hs.measurableSet]; rw [integral_countable hf']
  congr 1 with a : 1
  rw [measureReal_def]; rw [Measure.comap_apply Subtype.val Subtype.coe_injective
    (fun s' hs' => MeasurableSet.subtype_image (Countable.measurableSet hs) hs') _
    (MeasurableSet.singleton a)]
  simp [measureReal_def]

/--
theorem `setIntegral_finset` / 定理 `setIntegral_finset`

English:
theorem setIntegral_finset
  given: (s : Finset X) (hf : IntegrableOn f s μ)
  proof: by
  rw [setIntegral_countable _ s.countable_toSet hf]; rw [← Finset.tsum_subtype']

@[deprecated (since := "2026-03-09")] alias integral_finset := setIntegral_finset

中文:
定理 set整数egral_finset
  条件: (s : 有限集 X) (hf : 整数egrableOn f s μ)
  证明: by
  rw [setIntegral_countable _ s.countable_toSet hf]; rw [← Finset.tsum_subtype']

@[deprecated (since := "2026-03-09")] alias integral_finset := setIntegral_finset

Depends on / 依赖: Finset, Finset.tsum_subtype, countable_toSet, s.countable_toSet, setIntegral_countable, tsum_subtype
-/
theorem setIntegral_finset (s : Finset X) (hf : IntegrableOn f s μ) :
    ∫ x in s, f x ∂μ = ∑ x in s, μ.real {x} • f x := by
  rw [setIntegral_countable _ s.countable_toSet hf]; rw [← Finset.tsum_subtype']

@[deprecated (since := "2026-03-09")] alias integral_finset := setIntegral_finset

/--
theorem `integral_fintype` / 定理 `integral_fintype`

English:
theorem integral_fintype
  given: [Fintype X] (hf : Integrable f μ)
  proof: by
  -- NB: Integrable f does not follow from Fintype, because the measure itself could be non-finite
  rw [← setIntegral_finset .univ]; rw [Finset.coe_univ]; rw [Measure.restrict_univ]
  simp [Finset.coe_univ, hf]

中文:
定理 integral_fintype
  条件: [有限类型 X] (hf : 可积 f μ)
  证明: by
  -- NB: Integrable f does not follow from Fintype, because the measure itself could be non-finite
  rw [← setIntegral_finset .univ]; rw [Finset.coe_univ]; rw [Measure.restrict_univ]
  simp [Finset.coe_univ, hf]
-/
theorem integral_fintype [Fintype X] (hf : Integrable f μ) :
    ∫ x, f x ∂μ = ∑ x, μ.real {x} • f x := by
  -- NB: Integrable f does not follow from Fintype, because the measure itself could be non-finite
  rw [← setIntegral_finset .univ]; rw [Finset.coe_univ]; rw [Measure.restrict_univ]
  simp [Finset.coe_univ, hf]

/--
lemma `integral_count` / 引理 `integral_count`

English:
lemma integral_count
  given: [Fintype X] (f : X -> E)
  proof: by simp [integral_fintype]

中文:
引理 integral_count
  条件: [有限类型 X] (f : X -> E)
  证明: by simp [integral_fintype]
-/
@[simp] lemma integral_count [Fintype X] (f : X -> E) :
    ∫ x, f x ∂.count = ∑ a, f a := by simp [integral_fintype]

end DiscreteSpace

end Integral

end MeasureTheory
