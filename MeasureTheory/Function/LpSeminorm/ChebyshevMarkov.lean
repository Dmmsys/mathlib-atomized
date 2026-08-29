/-
Copyright (c) 2022 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying
-/
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

/-!
# Chebyshev-Markov inequality in terms of Lp seminorms

In this file we formulate several versions of the Chebyshev-Markov inequality
in terms of the `MeasureTheory.eLpNorm` seminorm.
-/

public section
open scoped NNReal ENNReal

namespace MeasureTheory

variable {α E ε' : Type*} {m0 : MeasurableSpace α} [NormedAddCommGroup E]
  [TopologicalSpace ε'] [ContinuousENorm ε']
  {p : Real>=0∞} (μ : Measure α)

/--
theorem `pow_mul_meas_ge_le_eLpNorm` / 定理 `pow_mul_meas_ge_le_eLpNorm`

English:
theorem pow_mul_meas_ge_le_eLpNorm
  statement: (hp_ne_zero : p != 0) (hp_ne_top : p != ∞)
  proof: by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp_ne_zero hp_ne_top]
  gcongr
  exact mul_meas_ge_le_lintegral₀ (hf.enorm.pow_const _) ε

中文:
定理 pow_mul_meas_ge_le_eLpNorm
  结论: (hp_ne_zero : p != 0) (hp_ne_top : p != ∞)
  证明: by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp_ne_zero hp_ne_top]
  gcongr
  exact mul_meas_ge_le_lintegral₀ (hf.enorm.pow_const _) ε

Depends on / 依赖: eLpNorm_eq_lintegral_rpow_enorm_toReal, hf.enorm.pow_const, hp_ne_top, hp_ne_zero, pow_const
-/
theorem pow_mul_meas_ge_le_eLpNorm (hp_ne_zero : p != 0) (hp_ne_top : p != ∞)
    {f : α -> ε'} (hf : AEStronglyMeasurable f μ) (ε : Real>=0∞) :
    (ε * μ { x | ε <= ‖f x‖ₑ ^ p.toReal }) ^ (1 / p.toReal) <= eLpNorm f p μ := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp_ne_zero hp_ne_top]
  gcongr
  exact mul_meas_ge_le_lintegral₀ (hf.enorm.pow_const _) ε

/--
theorem `mul_meas_ge_le_pow_eLpNorm` / 定理 `mul_meas_ge_le_pow_eLpNorm`

English:
theorem mul_meas_ge_le_pow_eLpNorm
  statement: (hp_ne_zero : p != 0) (hp_ne_top : p != ∞)
  proof: by
  have : 1 / p.toReal * p.toReal = 1 := by
    refine one_div_mul_cancel ?_
    rw [Ne]; rw [ENNReal.toReal_eq_zero_iff]
    exact not_or_intro hp_ne_zero hp_ne_top
  rw [← ENNReal.rpow_one (ε * μ { x | ε <= ‖f x‖ₑ ^ p.toReal })]; rw [← this]; rw [ENNReal.rpow_mul]
  gcongr
  exact pow_mul_meas_g

中文:
定理 mul_meas_ge_le_pow_eLpNorm
  结论: (hp_ne_zero : p != 0) (hp_ne_top : p != ∞)
  证明: by
  have : 1 / p.toReal * p.toReal = 1 := by
    refine one_div_mul_cancel ?_
    rw [Ne]; rw [ENNReal.toReal_eq_zero_iff]
    exact not_or_intro hp_ne_zero hp_ne_top
  rw [← ENNReal.rpow_one (ε * μ { x | ε <= ‖f x‖ₑ ^ p.toReal })]; rw [← this]; rw [ENNReal.rpow_mul]
  gcongr
  exact pow_mul_meas_g

Depends on / 依赖: ENNReal, ENNReal.rpow_mul, ENNReal.rpow_one, ENNReal.toReal_eq_zero_iff, hp_ne_top, hp_ne_zero, not_or_intro, one_div_mul_cancel, p.toReal, pow_mul_meas_ge_le_eLpNorm, rpow_mul, rpow_one, toReal, toReal_eq_zero_iff
-/
theorem mul_meas_ge_le_pow_eLpNorm (hp_ne_zero : p != 0) (hp_ne_top : p != ∞)
    {f : α -> ε'} (hf : AEStronglyMeasurable f μ) (ε : Real>=0∞) :
    ε * μ { x | ε <= ‖f x‖ₑ ^ p.toReal } <= eLpNorm f p μ ^ p.toReal := by
  have : 1 / p.toReal * p.toReal = 1 := by
    refine one_div_mul_cancel ?_
    rw [Ne]; rw [ENNReal.toReal_eq_zero_iff]
    exact not_or_intro hp_ne_zero hp_ne_top
  rw [← ENNReal.rpow_one (ε * μ { x | ε <= ‖f x‖ₑ ^ p.toReal })]; rw [← this]; rw [ENNReal.rpow_mul]
  gcongr
  exact pow_mul_meas_ge_le_eLpNorm μ hp_ne_zero hp_ne_top hf ε

/--
theorem `mul_meas_ge_le_pow_eLpNorm'` / 定理 `mul_meas_ge_le_pow_eLpNorm'`

English:
theorem mul_meas_ge_le_pow_eLpNorm'
  statement: (hp_ne_zero : p != 0) (hp_ne_top : p != ∞)
  proof: by
  convert! mul_meas_ge_le_pow_eLpNorm μ hp_ne_zero hp_ne_top hf (ε ^ p.toReal) using 4
  ext x
  rw [ENNReal.rpow_le_rpow_iff (ENNReal.toReal_pos hp_ne_zero hp_ne_top)]

中文:
定理 mul_meas_ge_le_pow_eLpNorm'
  结论: (hp_ne_zero : p != 0) (hp_ne_top : p != ∞)
  证明: by
  convert! mul_meas_ge_le_pow_eLpNorm μ hp_ne_zero hp_ne_top hf (ε ^ p.toReal) using 4
  ext x
  rw [ENNReal.rpow_le_rpow_iff (ENNReal.toReal_pos hp_ne_zero hp_ne_top)]

Depends on / 依赖: ENNReal, ENNReal.rpow_le_rpow_iff, ENNReal.toReal_pos, convert, hp_ne_top, hp_ne_zero, mul_meas_ge_le_pow_eLpNorm, p.toReal, rpow_le_rpow_iff, toReal, toReal_pos
-/
theorem mul_meas_ge_le_pow_eLpNorm' (hp_ne_zero : p != 0) (hp_ne_top : p != ∞)
    {f : α -> ε'} (hf : AEStronglyMeasurable f μ) (ε : Real>=0∞) :
    ε ^ p.toReal * μ { x | ε <= ‖f x‖ₑ } <= eLpNorm f p μ ^ p.toReal := by
  convert! mul_meas_ge_le_pow_eLpNorm μ hp_ne_zero hp_ne_top hf (ε ^ p.toReal) using 4
  ext x
  rw [ENNReal.rpow_le_rpow_iff (ENNReal.toReal_pos hp_ne_zero hp_ne_top)]

/--
theorem `meas_ge_le_mul_pow_eLpNorm_enorm` / 定理 `meas_ge_le_mul_pow_eLpNorm_enorm`

English:
theorem meas_ge_le_mul_pow_eLpNorm_enorm
  statement: (hp_ne_zero : p != 0) (hp_ne_top : p != ∞)
  proof: by
  by_cases h : ε = ∞
  · have : (0 : Real>=0∞) ^ p.toReal = 0 := by
      rw [ENNReal.zero_rpow_of_pos (ENNReal.toReal_pos hp_ne_zero hp_ne_top)]
    simp [h, this, hmeas_top]
  · have hεpow : ε ^ p.toReal != 0 := (ENNReal.rpow_pos (pos_iff_ne_zero.2 hε) h).ne.symm
    have hεpow' : ε ^ p.toReal 

中文:
定理 meas_ge_le_mul_pow_eLpNorm_enorm
  结论: (hp_ne_zero : p != 0) (hp_ne_top : p != ∞)
  证明: by
  by_cases h : ε = ∞
  · have : (0 : Real>=0∞) ^ p.toReal = 0 := by
      rw [ENNReal.zero_rpow_of_pos (ENNReal.toReal_pos hp_ne_zero hp_ne_top)]
    simp [h, this, hmeas_top]
  · have hεpow : ε ^ p.toReal != 0 := (ENNReal.rpow_pos (pos_iff_ne_zero.2 hε) h).ne.symm
    have hεpow' : ε ^ p.toReal 

Depends on / 依赖: ENNReal, ENNReal.inv_rpow, ENNReal.mul_inv_cancel, ENNReal.mul_le_mul_iff_right, ENNReal.rpow_pos, ENNReal.toReal_pos, ENNReal.zero_rpow_of_pos, finiteness, hmeas_top, hp_ne, hp_ne_top, hp_ne_zero, inv_rpow, mul_assoc, mul_inv_cancel, mul_le_mul_iff_right, mul_meas_ge_le_pow_eLpNorm, ne.symm, one_mul, p.toReal
-/
theorem meas_ge_le_mul_pow_eLpNorm_enorm (hp_ne_zero : p != 0) (hp_ne_top : p != ∞)
    {f : α -> ε'} (hf : AEStronglyMeasurable f μ)
    {ε : Real>=0∞} (hε : ε != 0) (hmeas_top : ε = ∞ -> μ {x | ‖f x‖ₑ = ⊤} = 0) :
    μ { x | ε <= ‖f x‖ₑ } <= ε⁻¹ ^ p.toReal * eLpNorm f p μ ^ p.toReal := by
  by_cases h : ε = ∞
  · have : (0 : Real>=0∞) ^ p.toReal = 0 := by
      rw [ENNReal.zero_rpow_of_pos (ENNReal.toReal_pos hp_ne_zero hp_ne_top)]
    simp [h, this, hmeas_top]
  · have hεpow : ε ^ p.toReal != 0 := (ENNReal.rpow_pos (pos_iff_ne_zero.2 hε) h).ne.symm
    have hεpow' : ε ^ p.toReal != ∞ := by finiteness
    rw [ENNReal.inv_rpow]; rw [← ENNReal.mul_le_mul_iff_right hεpow hεpow']; rw [← mul_assoc]; rw [ENNReal.mul_inv_cancel hεpow hεpow']; rw [one_mul]
    exact mul_meas_ge_le_pow_eLpNorm' μ hp_ne_zero hp_ne_top hf ε

/--
theorem `MemLp.meas_ge_lt_top'_enorm` / 定理 `MemLp.meas_ge_lt_top'_enorm`

English:
theorem MemLp.meas_ge_lt_top'_enorm
  statement: {μ : Measure α} {f : α -> ε'} (hℒp : MemLp f p μ)
  proof: by
  apply meas_ge_le_mul_pow_eLpNorm_enorm μ hp_ne_zero hp_ne_top hℒp.aestronglyMeasurable hε hε'
.trans_lt (ENNReal.mul_lt_top ?_ ?_)
  · simp [hε, lt_top_iff_ne_top]
  · simp [hℒp.eLpNorm_lt_top.ne, lt_top_iff_ne_top]

中文:
定理 MemLp.meas_ge_lt_top'_enorm
  结论: {μ : 测度 α} {f : α -> ε'} (hℒp : MemLp f p μ)
  证明: by
  apply meas_ge_le_mul_pow_eLpNorm_enorm μ hp_ne_zero hp_ne_top hℒp.aestronglyMeasurable hε hε'
.trans_lt (ENNReal.mul_lt_top ?_ ?_)
  · simp [hε, lt_top_iff_ne_top]
  · simp [hℒp.eLpNorm_lt_top.ne, lt_top_iff_ne_top]

Depends on / 依赖: ENNReal, ENNReal.mul_lt_top, aestronglyMeasurable, eLpNorm_lt_top, hp_ne_top, hp_ne_zero, lt_top_iff_ne_top, meas_ge_le_mul_pow_eLpNorm_enorm, mul_lt_top, p.aestronglyMeasurable, p.eLpNorm_lt_top.ne, trans_lt
-/
theorem MemLp.meas_ge_lt_top'_enorm {μ : Measure α} {f : α -> ε'} (hℒp : MemLp f p μ)
    (hp_ne_zero : p != 0) (hp_ne_top : p != ∞)
    {ε : Real>=0∞} (hε : ε != 0) (hε' : ε = ∞ -> μ {x | ‖f x‖ₑ = ⊤} = 0) :
    μ { x | ε <= ‖f x‖ₑ } < ∞ := by
  apply meas_ge_le_mul_pow_eLpNorm_enorm μ hp_ne_zero hp_ne_top hℒp.aestronglyMeasurable hε hε'
.trans_lt (ENNReal.mul_lt_top ?_ ?_)
  · simp [hε, lt_top_iff_ne_top]
  · simp [hℒp.eLpNorm_lt_top.ne, lt_top_iff_ne_top]

/--
theorem `MemLp.meas_ge_lt_top'` / 定理 `MemLp.meas_ge_lt_top'`

English:
theorem MemLp.meas_ge_lt_top'
  statement: {μ : Measure α} {f : α -> E} (hℒp : MemLp f p μ) (hp_ne_zero : p != 0)
  proof: by
  by_cases h : ε = ∞
  · simp [h]
  exact hℒp.meas_ge_lt_top'_enorm hp_ne_zero hp_ne_top hε (by simp)

中文:
定理 MemLp.meas_ge_lt_top'
  结论: {μ : 测度 α} {f : α -> E} (hℒp : MemLp f p μ) (hp_ne_zero : p != 0)
  证明: by
  by_cases h : ε = ∞
  · simp [h]
  exact hℒp.meas_ge_lt_top'_enorm hp_ne_zero hp_ne_top hε (by simp)
-/
theorem MemLp.meas_ge_lt_top' {μ : Measure α} {f : α -> E} (hℒp : MemLp f p μ) (hp_ne_zero : p != 0)
    (hp_ne_top : p != ∞) {ε : Real>=0∞} (hε : ε != 0) :
    μ { x | ε <= ‖f x‖₊ } < ∞ := by
  by_cases h : ε = ∞
  · simp [h]
  exact hℒp.meas_ge_lt_top'_enorm hp_ne_zero hp_ne_top hε (by simp)

/--
theorem `MemLp.meas_ge_lt_top_enorm` / 定理 `MemLp.meas_ge_lt_top_enorm`

English:
theorem MemLp.meas_ge_lt_top_enorm
  statement: {μ : Measure α} {f : α -> ε'} (hℒp : MemLp f p μ)
  proof: hℒp.meas_ge_lt_top'_enorm hp_ne_zero hp_ne_top (by simp [hε]) (by simp)

中文:
定理 MemLp.meas_ge_lt_top_enorm
  结论: {μ : 测度 α} {f : α -> ε'} (hℒp : MemLp f p μ)
  证明: hℒp.meas_ge_lt_top'_enorm hp_ne_zero hp_ne_top (by simp [hε]) (by simp)

Depends on / 依赖: _enorm, hp_ne_top, hp_ne_zero, meas_ge_lt_top, p.meas_ge_lt_top
-/
theorem MemLp.meas_ge_lt_top_enorm {μ : Measure α} {f : α -> ε'} (hℒp : MemLp f p μ)
    (hp_ne_zero : p != 0) (hp_ne_top : p != ∞) {ε : Real>=0} (hε : ε != 0) :
    μ { x | ε <= ‖f x‖ₑ } < ∞ :=
  hℒp.meas_ge_lt_top'_enorm hp_ne_zero hp_ne_top (by simp [hε]) (by simp)

/--
theorem `MemLp.meas_ge_lt_top` / 定理 `MemLp.meas_ge_lt_top`

English:
theorem MemLp.meas_ge_lt_top
  statement: {μ : Measure α} {f : α -> E} (hℒp : MemLp f p μ) (hp_ne_zero : p != 0)
  proof: by
  simp_rw [← ENNReal.coe_le_coe]
  apply hℒp.meas_ge_lt_top' hp_ne_zero hp_ne_top (by simp [hε])

中文:
定理 MemLp.meas_ge_lt_top
  结论: {μ : 测度 α} {f : α -> E} (hℒp : MemLp f p μ) (hp_ne_zero : p != 0)
  证明: by
  simp_rw [← ENNReal.coe_le_coe]
  apply hℒp.meas_ge_lt_top' hp_ne_zero hp_ne_top (by simp [hε])

Depends on / 依赖: ENNReal, ENNReal.coe_le_coe, coe_le_coe, hp_ne_top, hp_ne_zero, meas_ge_lt_top, p.meas_ge_lt_top, simp_rw
-/
theorem MemLp.meas_ge_lt_top {μ : Measure α} {f : α -> E} (hℒp : MemLp f p μ) (hp_ne_zero : p != 0)
    (hp_ne_top : p != ∞) {ε : Real>=0} (hε : ε != 0) :
    μ { x | ε <= ‖f x‖₊ } < ∞ := by
  simp_rw [← ENNReal.coe_le_coe]
  apply hℒp.meas_ge_lt_top' hp_ne_zero hp_ne_top (by simp [hε])

end MeasureTheory
