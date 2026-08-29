/-
Copyright (c) 2022 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.Analysis.Normed.Module.Basic

/-! # A lemma about measurability with density under scalar multiplication in normed spaces -/

public section


open MeasureTheory Filter ENNReal Set

open NNReal ENNReal

variable {α : Type*} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α}

/--
theorem `aemeasurable_withDensity_iff` / 定理 `aemeasurable_withDensity_iff`

English:
theorem aemeasurable_withDensity_iff
  statement: {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  proof: by
  constructor
  · rintro ⟨g', g'meas, hg'⟩
    have A : MeasurableSet { x : α | f x != 0 } := (hf (measurableSet_singleton 0)).compl
    refine ⟨fun x => (f x : Real) • g' x, hf.coe_nnreal_real.smul g'meas, ?_⟩
    apply @ae_of_ae_restrict_of_ae_restrict_compl _ _ _ { x | f x != 0 }
    · rw [EventuallyEq, ae_withDensity_iff hf.coe_nnreal_ennreal] at hg'
      rw [ae_restrict_iff' A]
      filter_upwards [hg']
      intro a ha h'a
      have : (f a : Real>=0∞) != 0 := by simpa only [Ne, ENNReal.coe_eq_zero] using h'a
      rw [ha this]
    · filter_upwards [ae_restrict_mem A.compl]
      intro x hx
      simp only [Classical.not_not, mem_ofPred_eq, mem_compl_iff] at hx
      simp [hx]
  · rintro ⟨g', g'meas, hg'⟩
    refine ⟨fun x => (f x : Real)⁻¹ • g' x, hf.coe_nnreal_real.inv.smul g'meas, ?_⟩
    rw [EventuallyEq]; rw [ae_withDensity_iff hf.coe_nnreal_ennreal]
    filter_upwards [hg']
    intro x hx h'x
    rw [← hx]; rw [smul_smul]; rw [inv_mul_cancel₀]; rw [one_smul]
    simp only [Ne, ENNReal.coe_eq_zero] at h'x
    simpa only [NNReal.coe_eq_zero, Ne] using h'x

中文:
定理 aemeasurable_withDensity_iff
  结论: {E : 类型} [赋范交换加群 E] [赋范空间 实数 E]
  证明: by
  constructor
  · rintro ⟨g', g'meas, hg'⟩
    have A : MeasurableSet { x : α | f x != 0 } := (hf (measurableSet_singleton 0)).compl
    refine ⟨fun x => (f x : Real) • g' x, hf.coe_nnreal_real.smul g'meas, ?_⟩
    apply @ae_of_ae_restrict_of_ae_restrict_compl _ _ _ { x | f x != 0 }
    · rw [EventuallyEq, ae_withDensity_iff hf.coe_nnreal_ennreal] at hg'
      rw [ae_restrict_iff' A]
      filter_upwards [hg']
      intro a ha h'a
      have : (f a : Real>=0∞) != 0 := by simpa only [Ne, ENNReal.coe_eq_zero] using h'a
      rw [ha this]
    · filter_upwards [ae_restrict_mem A.compl]
      intro x hx
      simp only [Classical.not_not, mem_ofPred_eq, mem_compl_iff] at hx
      simp [hx]
  · rintro ⟨g', g'meas, hg'⟩
    refine ⟨fun x => (f x : Real)⁻¹ • g' x, hf.coe_nnreal_real.inv.smul g'meas, ?_⟩
    rw [EventuallyEq]; rw [ae_withDensity_iff hf.coe_nnreal_ennreal]
    filter_upwards [hg']
    intro x hx h'x
    rw [← hx]; rw [smul_smul]; rw [inv_mul_cancel₀]; rw [one_smul]
    simp only [Ne, ENNReal.coe_eq_zero] at h'x
    simpa only [NNReal.coe_eq_zero, Ne] using h'x

Depends on / 依赖: ENNReal, ENNReal.coe_eq_zero, EventuallyEq, MeasurableSet, ae_of_ae_restrict_of_ae_restrict_compl, ae_restrict_iff, ae_withDensity_iff, coe_eq_zero, coe_nnreal_ennreal, coe_nnreal_real, filter_upwards, hf.coe_nnreal_ennreal, hf.coe_nnreal_real.smul, measurableSet_singleton
-/
theorem aemeasurable_withDensity_iff {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E] {f : α -> Real>=0}
    (hf : Measurable f) {g : α -> E} :
    AEMeasurable g (μ.withDensity fun x => (f x : Real>=0∞)) ↔
      AEMeasurable (fun x => (f x : Real) • g x) μ := by
  constructor
  · rintro ⟨g', g'meas, hg'⟩
    have A : MeasurableSet { x : α | f x != 0 } := (hf (measurableSet_singleton 0)).compl
    refine ⟨fun x => (f x : Real) • g' x, hf.coe_nnreal_real.smul g'meas, ?_⟩
    apply @ae_of_ae_restrict_of_ae_restrict_compl _ _ _ { x | f x != 0 }
    · rw [EventuallyEq, ae_withDensity_iff hf.coe_nnreal_ennreal] at hg'
      rw [ae_restrict_iff' A]
      filter_upwards [hg']
      intro a ha h'a
      have : (f a : Real>=0∞) != 0 := by simpa only [Ne, ENNReal.coe_eq_zero] using h'a
      rw [ha this]
    · filter_upwards [ae_restrict_mem A.compl]
      intro x hx
      simp only [Classical.not_not, mem_ofPred_eq, mem_compl_iff] at hx
      simp [hx]
  · rintro ⟨g', g'meas, hg'⟩
    refine ⟨fun x => (f x : Real)⁻¹ • g' x, hf.coe_nnreal_real.inv.smul g'meas, ?_⟩
    rw [EventuallyEq]; rw [ae_withDensity_iff hf.coe_nnreal_ennreal]
    filter_upwards [hg']
    intro x hx h'x
    rw [← hx]; rw [smul_smul]; rw [inv_mul_cancel₀]; rw [one_smul]
    simp only [Ne, ENNReal.coe_eq_zero] at h'x
    simpa only [NNReal.coe_eq_zero, Ne] using h'x
