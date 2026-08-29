/-
Copyright (c) 2024 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic

import Mathlib.Analysis.RCLike.Lemmas
import Mathlib.Tactic.Positivity.Finset

/-!
# Real-valued Lᵖ norm

This file proves theorems about `MeasureTheory.lpNorm`,
a real-valued version of `MeasureTheory.eLpNorm`.
-/

open Filter
open scoped BigOperators ComplexConjugate ENNReal NNReal

public section

namespace MeasureTheory
variable {α E : Type*} {m : MeasurableSpace α} {p : Real>=0∞} {q : Real} {μ ν : Measure α}
  [NormedAddCommGroup E] {f g h : α -> E}

/--
lemma `toReal_eLpNorm` / 引理 `toReal_eLpNorm`

English:
lemma toReal_eLpNorm
  given: (hf : AEStronglyMeasurable f μ)
  statement: (eLpNorm f p μ).toReal = lpNorm f p μ
  proof: by
  rw [lpNorm]; rw [if_pos hf]

中文:
引理 toReal_eLpNorm
  条件: (hf : AEStronglyMeasurable f μ)
  结论: (eLpNorm f p μ).to实数 = lpNorm f p μ
  证明: by
  rw [lpNorm]; rw [if_pos hf]

Depends on / 依赖: if_pos, lpNorm
-/
lemma toReal_eLpNorm (hf : AEStronglyMeasurable f μ) : (eLpNorm f p μ).toReal = lpNorm f p μ := by
  rw [lpNorm]; rw [if_pos hf]

/--
lemma `ofReal_lpNorm` / 引理 `ofReal_lpNorm`

English:
lemma ofReal_lpNorm
  given: (hf : MemLp f p μ)
  statement: .ofReal (lpNorm f p μ) = eLpNorm f p μ
  proof: by
  rw [← toReal_eLpNorm hf.aestronglyMeasurable]; rw [ENNReal.ofReal_toReal hf.eLpNorm_ne_top]

@[simp]

中文:
引理 ofReal_lpNorm
  条件: (hf : MemLp f p μ)
  结论: .of实数 (lpNorm f p μ) = eLpNorm f p μ
  证明: by
  rw [← toReal_eLpNorm hf.aestronglyMeasurable]; rw [ENNReal.ofReal_toReal hf.eLpNorm_ne_top]

@[simp]

Depends on / 依赖: ENNReal, ENNReal.ofReal_toReal, aestronglyMeasurable, eLpNorm_ne_top, hf.aestronglyMeasurable, hf.eLpNorm_ne_top, ofReal_toReal, toReal_eLpNorm
-/
lemma ofReal_lpNorm (hf : MemLp f p μ) : .ofReal (lpNorm f p μ) = eLpNorm f p μ := by
  rw [← toReal_eLpNorm hf.aestronglyMeasurable]; rw [ENNReal.ofReal_toReal hf.eLpNorm_ne_top]

@[simp]
/--
lemma `lpNorm_of_not_aestronglyMeasurable` / 引理 `lpNorm_of_not_aestronglyMeasurable`

English:
lemma lpNorm_of_not_aestronglyMeasurable
  given: (hf : ¬ AEStronglyMeasurable f μ)
  statement: lpNorm f p μ = 0
  proof: if_neg hf

@[simp]

中文:
引理 lpNorm_of_not_aestronglyMeasurable
  条件: (hf : ¬ AEStronglyMeasurable f μ)
  结论: lpNorm f p μ = 0
  证明: if_neg hf

@[simp]

Depends on / 依赖: if_neg
-/
lemma lpNorm_of_not_aestronglyMeasurable (hf : ¬ AEStronglyMeasurable f μ) : lpNorm f p μ = 0 :=
  if_neg hf

@[simp]
/--
lemma `lpNorm_of_not_memLp` / 引理 `lpNorm_of_not_memLp`

English:
lemma lpNorm_of_not_memLp
  given: (hf' : ¬ MemLp f p μ)
  statement: lpNorm f p μ = 0
  proof: by simp_all [MemLp, lpNorm]

中文:
引理 lpNorm_of_not_memLp
  条件: (hf' : ¬ MemLp f p μ)
  结论: lpNorm f p μ = 0
  证明: by simp_all [MemLp, lpNorm]

Depends on / 依赖: lpNorm
-/
lemma lpNorm_of_not_memLp (hf' : ¬ MemLp f p μ) : lpNorm f p μ = 0 := by simp_all [MemLp, lpNorm]

/--
lemma `lpNorm_nonneg` / 引理 `lpNorm_nonneg`

English:
lemma lpNorm_nonneg
  statement: 0 <= lpNorm f p μ
  proof: by simp [lpNorm, apply_ite]

中文:
引理 lpNorm_nonneg
  结论: 0 <= lpNorm f p μ
  证明: by simp [lpNorm, apply_ite]
-/
@[simp] lemma lpNorm_nonneg : 0 <= lpNorm f p μ := by simp [lpNorm, apply_ite]

/--
lemma `lpNorm_eq_integral_norm_rpow_toReal` / 引理 `lpNorm_eq_integral_norm_rpow_toReal`

English:
lemma lpNorm_eq_integral_norm_rpow_toReal
  statement: (hp₀ : p != 0) (hp : p != ∞)
  proof: by
  rw [← toReal_eLpNorm hf]; rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp₀ hp]; rw [← ENNReal.toReal_rpow]; rw [← integral_toReal]
  · simp [← ENNReal.toReal_rpow]
  · simp_rw [← ofReal_norm]
    borelize E
    fun_prop
  · exact .of_forall fun x => ENNReal.rpow_lt_top_of_nonneg (by positivity) (

中文:
引理 lpNorm_eq_integral_norm_rpow_toReal
  结论: (hp₀ : p != 0) (hp : p != ∞)
  证明: by
  rw [← toReal_eLpNorm hf]; rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp₀ hp]; rw [← ENNReal.toReal_rpow]; rw [← integral_toReal]
  · simp [← ENNReal.toReal_rpow]
  · simp_rw [← ofReal_norm]
    borelize E
    fun_prop
  · exact .of_forall fun x => ENNReal.rpow_lt_top_of_nonneg (by positivity) (

Depends on / 依赖: ENNReal, ENNReal.rpow_lt_top_of_nonneg, ENNReal.toReal_rpow, borelize, eLpNorm_eq_lintegral_rpow_enorm_toReal, fun_prop, integral_toReal, ofReal_norm, of_forall, rpow_lt_top_of_nonneg, simp_rw, toReal_eLpNorm, toReal_rpow
-/
lemma lpNorm_eq_integral_norm_rpow_toReal (hp₀ : p != 0) (hp : p != ∞)
    (hf : AEStronglyMeasurable f μ) :
    lpNorm f p μ = (∫ x, ‖f x‖ ^ p.toReal ∂μ) ^ p.toReal⁻¹ := by
  rw [← toReal_eLpNorm hf]; rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp₀ hp]; rw [← ENNReal.toReal_rpow]; rw [← integral_toReal]
  · simp [← ENNReal.toReal_rpow]
  · simp_rw [← ofReal_norm]
    borelize E
    fun_prop
  · exact .of_forall fun x => ENNReal.rpow_lt_top_of_nonneg (by positivity) (by simp)

/--
lemma `lpNorm_nnreal_eq_integral_norm_rpow` / 引理 `lpNorm_nnreal_eq_integral_norm_rpow`

English:
lemma lpNorm_nnreal_eq_integral_norm_rpow
  given: {p : Real>=0} (hp : p != 0) (hf : AEStronglyMeasurable f μ)
  proof: by
  rw [lpNorm_eq_integral_norm_rpow_toReal (by positivity) (by simp) hf]; simp

中文:
引理 lpNorm_nnreal_eq_integral_norm_rpow
  条件: {p : 实数>=0} (hp : p != 0) (hf : AEStronglyMeasurable f μ)
  证明: by
  rw [lpNorm_eq_integral_norm_rpow_toReal (by positivity) (by simp) hf]; simp

Depends on / 依赖: lpNorm_eq_integral_norm_rpow_toReal
-/
lemma lpNorm_nnreal_eq_integral_norm_rpow {p : Real>=0} (hp : p != 0) (hf : AEStronglyMeasurable f μ) :
    lpNorm f p μ = (∫ x, ‖f x‖ ^ (p : Real) ∂μ) ^ (p⁻¹ : Real) := by
  rw [lpNorm_eq_integral_norm_rpow_toReal (by positivity) (by simp) hf]; simp

/--
lemma `lpNorm_one_eq_integral_norm` / 引理 `lpNorm_one_eq_integral_norm`

English:
lemma lpNorm_one_eq_integral_norm
  given: (hf : AEStronglyMeasurable f μ)
  proof: by
  simp [lpNorm_eq_integral_norm_rpow_toReal one_ne_zero ENNReal.coe_ne_top hf]

中文:
引理 lpNorm_one_eq_integral_norm
  条件: (hf : AEStronglyMeasurable f μ)
  证明: by
  simp [lpNorm_eq_integral_norm_rpow_toReal one_ne_zero ENNReal.coe_ne_top hf]

Depends on / 依赖: ENNReal, ENNReal.coe_ne_top, coe_ne_top, lpNorm_eq_integral_norm_rpow_toReal, one_ne_zero
-/
lemma lpNorm_one_eq_integral_norm (hf : AEStronglyMeasurable f μ) :
    lpNorm f 1 μ = ∫ x, ‖f x‖ ∂μ := by
  simp [lpNorm_eq_integral_norm_rpow_toReal one_ne_zero ENNReal.coe_ne_top hf]

/--
lemma `lpNorm_exponent_zero` / 引理 `lpNorm_exponent_zero`

English:
lemma lpNorm_exponent_zero
  given: (f : α -> E)
  statement: lpNorm f 0 μ = 0
  proof: by simp [lpNorm]

中文:
引理 lpNorm_exponent_zero
  条件: (f : α -> E)
  结论: lpNorm f 0 μ = 0
  证明: by simp [lpNorm]
-/
@[simp] lemma lpNorm_exponent_zero (f : α -> E) : lpNorm f 0 μ = 0 := by simp [lpNorm]
/--
lemma `lpNorm_measure_zero` / 引理 `lpNorm_measure_zero`

English:
lemma lpNorm_measure_zero
  given: (f : α -> E)
  statement: lpNorm f p (0 : Measure α) = 0
  proof: by simp [lpNorm]

中文:
引理 lpNorm_measure_zero
  条件: (f : α -> E)
  结论: lpNorm f p (0 : Measure α) = 0
  证明: by simp [lpNorm]
-/
@[simp] lemma lpNorm_measure_zero (f : α -> E) : lpNorm f p (0 : Measure α) = 0 := by simp [lpNorm]

/--
lemma `ae_le_lpNorm_exponent_top` / 引理 `ae_le_lpNorm_exponent_top`

English:
lemma ae_le_lpNorm_exponent_top
  given: (hf : MemLp f ∞ μ)
  statement: forallᵐ x ∂μ, ‖f x‖ <= lpNorm f ∞ μ
  proof: by
  simpa only [← toReal_eLpNorm hf.aestronglyMeasurable, ← ENNReal.ofReal_le_iff_le_toReal hf.2.ne,
    ofReal_norm] using! ae_le_eLpNormEssSup

中文:
引理 ae_le_lpNorm_exponent_top
  条件: (hf : MemLp f ∞ μ)
  结论: 对任意ᵐ x ∂μ, ‖f x‖ <= lpNorm f ∞ μ
  证明: by
  simpa only [← toReal_eLpNorm hf.aestronglyMeasurable, ← ENNReal.ofReal_le_iff_le_toReal hf.2.ne,
    ofReal_norm] using! ae_le_eLpNormEssSup

Depends on / 依赖: ENNReal, ENNReal.ofReal_le_iff_le_toReal, ae_le_eLpNormEssSup, aestronglyMeasurable, hf.aestronglyMeasurable, ofReal_le_iff_le_toReal, ofReal_norm, toReal_eLpNorm
-/
lemma ae_le_lpNorm_exponent_top (hf : MemLp f ∞ μ) : forallᵐ x ∂μ, ‖f x‖ <= lpNorm f ∞ μ := by
  simpa only [← toReal_eLpNorm hf.aestronglyMeasurable, ← ENNReal.ofReal_le_iff_le_toReal hf.2.ne,
    ofReal_norm] using! ae_le_eLpNormEssSup

/--
lemma `lpNorm_exponent_top_eq_essSup` / 引理 `lpNorm_exponent_top_eq_essSup`

English:
lemma lpNorm_exponent_top_eq_essSup
  given: (hf : MemLp f ∞ μ)
  statement: lpNorm f ∞ μ = essSup (‖f ·‖) μ
  proof: by
  simp only [← toReal_eLpNorm hf.aestronglyMeasurable, eLpNorm_exponent_top, eLpNormEssSup]
  refine ENNReal.toReal_essSup (by simp) ⟨lpNorm f ∞ μ, ?_⟩
  simpa [-toReal_enorm, lpNorm] using! ae_le_lpNorm_exponent_top hf

@[simp]

中文:
引理 lpNorm_exponent_top_eq_essSup
  条件: (hf : MemLp f ∞ μ)
  结论: lpNorm f ∞ μ = essSup (‖f ·‖) μ
  证明: by
  simp only [← toReal_eLpNorm hf.aestronglyMeasurable, eLpNorm_exponent_top, eLpNormEssSup]
  refine ENNReal.toReal_essSup (by simp) ⟨lpNorm f ∞ μ, ?_⟩
  simpa [-toReal_enorm, lpNorm] using! ae_le_lpNorm_exponent_top hf

@[simp]

Depends on / 依赖: ENNReal, ENNReal.toReal_essSup, ae_le_lpNorm_exponent_top, aestronglyMeasurable, eLpNormEssSup, eLpNorm_exponent_top, hf.aestronglyMeasurable, lpNorm, toReal_eLpNorm, toReal_enorm, toReal_essSup
-/
lemma lpNorm_exponent_top_eq_essSup (hf : MemLp f ∞ μ) : lpNorm f ∞ μ = essSup (‖f ·‖) μ := by
  simp only [← toReal_eLpNorm hf.aestronglyMeasurable, eLpNorm_exponent_top, eLpNormEssSup]
  refine ENNReal.toReal_essSup (by simp) ⟨lpNorm f ∞ μ, ?_⟩
  simpa [-toReal_enorm, lpNorm] using! ae_le_lpNorm_exponent_top hf

@[simp]
/--
lemma `lpNorm_zero` / 引理 `lpNorm_zero`

English:
lemma lpNorm_zero
  given: (p : Real>=0∞) (μ : Measure α)
  statement: lpNorm (0 : α -> E) p μ = 0
  proof: by simp [lpNorm]

@[simp]

中文:
引理 lpNorm_zero
  条件: (p : 实数>=0∞) (μ : Measure α)
  结论: lpNorm (0 : α -> E) p μ = 0
  证明: by simp [lpNorm]

@[simp]

Depends on / 依赖: lpNorm
-/
lemma lpNorm_zero (p : Real>=0∞) (μ : Measure α) : lpNorm (0 : α -> E) p μ = 0 := by simp [lpNorm]

@[simp]
/--
lemma `lpNorm_fun_zero` / 引理 `lpNorm_fun_zero`

English:
lemma lpNorm_fun_zero
  given: (p : Real>=0∞) (μ : Measure α)
  statement: lpNorm (fun _ => 0 : α -> E) p μ = 0
  proof: by
  simp [lpNorm]

@[simp]

中文:
引理 lpNorm_fun_zero
  条件: (p : 实数>=0∞) (μ : Measure α)
  结论: lpNorm (fun _ => 0 : α -> E) p μ = 0
  证明: by
  simp [lpNorm]

@[simp]

Depends on / 依赖: lpNorm
-/
lemma lpNorm_fun_zero (p : Real>=0∞) (μ : Measure α) : lpNorm (fun _ => 0 : α -> E) p μ = 0 := by
  simp [lpNorm]

@[simp]
/--
lemma `lpNorm_eq_zero` / 引理 `lpNorm_eq_zero`

English:
lemma lpNorm_eq_zero
  given: (hf : MemLp f p μ) (hp : p != 0)
  statement: lpNorm f p μ = 0 ↔ f =ᵐ[μ] 0
  proof: by
  simp [← toReal_eLpNorm hf.aestronglyMeasurable, ENNReal.toReal_eq_zero_iff, hf.eLpNorm_ne_top,
    eLpNorm_eq_zero_iff hf.1 hp]

中文:
引理 lpNorm_eq_zero
  条件: (hf : MemLp f p μ) (hp : p != 0)
  结论: lpNorm f p μ = 0 ↔ f =ᵐ[μ] 0
  证明: by
  simp [← toReal_eLpNorm hf.aestronglyMeasurable, ENNReal.toReal_eq_zero_iff, hf.eLpNorm_ne_top,
    eLpNorm_eq_zero_iff hf.1 hp]

Depends on / 依赖: ENNReal, ENNReal.toReal_eq_zero_iff, aestronglyMeasurable, eLpNorm_eq_zero_iff, eLpNorm_ne_top, hf.aestronglyMeasurable, hf.eLpNorm_ne_top, toReal_eLpNorm, toReal_eq_zero_iff
-/
lemma lpNorm_eq_zero (hf : MemLp f p μ) (hp : p != 0) : lpNorm f p μ = 0 ↔ f =ᵐ[μ] 0 := by
  simp [← toReal_eLpNorm hf.aestronglyMeasurable, ENNReal.toReal_eq_zero_iff, hf.eLpNorm_ne_top,
    eLpNorm_eq_zero_iff hf.1 hp]

/--
lemma `lpNorm_of_isEmpty` / 引理 `lpNorm_of_isEmpty`

English:
lemma lpNorm_of_isEmpty
  given: [IsEmpty α] (f : α -> E) (p : Real>=0∞)
  statement: lpNorm f p μ = 0
  proof: by
  simp [Subsingleton.elim f 0]

中文:
引理 lpNorm_of_isEmpty
  条件: [IsEmpty α] (f : α -> E) (p : 实数>=0∞)
  结论: lpNorm f p μ = 0
  证明: by
  simp [Subsingleton.elim f 0]
-/
@[simp] lemma lpNorm_of_isEmpty [IsEmpty α] (f : α -> E) (p : Real>=0∞) : lpNorm f p μ = 0 := by
  simp [Subsingleton.elim f 0]

/--
lemma `lpNorm_neg` / 引理 `lpNorm_neg`

English:
lemma lpNorm_neg
  given: (f : α -> E) (p : Real>=0∞) (μ : Measure α)
  proof: by
  by_cases hf : AEStronglyMeasurable f μ
  · simp [← toReal_eLpNorm, hf, hf.neg]
  · rw [lpNorm_of_not_aestronglyMeasurable hf,
lpNorm_of_not_aestronglyMeasurable fun h => hf by simpa using h.neg]

中文:
引理 lpNorm_neg
  条件: (f : α -> E) (p : 实数>=0∞) (μ : Measure α)
  证明: by
  by_cases hf : AEStronglyMeasurable f μ
  · simp [← toReal_eLpNorm, hf, hf.neg]
  · rw [lpNorm_of_not_aestronglyMeasurable hf,
lpNorm_of_not_aestronglyMeasurable fun h => hf by simpa using h.neg]
-/
@[simp] lemma lpNorm_neg (f : α -> E) (p : Real>=0∞) (μ : Measure α) :
    lpNorm (-f) p μ = lpNorm f p μ := by
  by_cases hf : AEStronglyMeasurable f μ
  · simp [← toReal_eLpNorm, hf, hf.neg]
  · rw [lpNorm_of_not_aestronglyMeasurable hf,
lpNorm_of_not_aestronglyMeasurable fun h => hf by simpa using h.neg]

/--
lemma `lpNorm_fun_neg` / 引理 `lpNorm_fun_neg`

English:
lemma lpNorm_fun_neg
  given: (f : α -> E) (p : Real>=0∞) (μ : Measure α)
  proof: lpNorm_neg ..

中文:
引理 lpNorm_fun_neg
  条件: (f : α -> E) (p : 实数>=0∞) (μ : Measure α)
  证明: lpNorm_neg ..
-/
@[simp] lemma lpNorm_fun_neg (f : α -> E) (p : Real>=0∞) (μ : Measure α) :
    lpNorm (fun x => -f x) p μ = lpNorm f p μ := lpNorm_neg ..

/--
lemma `lpNorm_sub_comm` / 引理 `lpNorm_sub_comm`

English:
lemma lpNorm_sub_comm
  given: (f g : α -> E) (p : Real>=0∞) (μ : Measure α)
  proof: by rw [← lpNorm_neg]; simp

中文:
引理 lpNorm_sub_comm
  条件: (f g : α -> E) (p : 实数>=0∞) (μ : Measure α)
  证明: by rw [← lpNorm_neg]; simp

Depends on / 依赖: lpNorm_neg
-/
lemma lpNorm_sub_comm (f g : α -> E) (p : Real>=0∞) (μ : Measure α) :
    lpNorm (f - g) p μ = lpNorm (g - f) p μ := by rw [← lpNorm_neg]; simp

/--
lemma `lpNorm_norm` / 引理 `lpNorm_norm`

English:
lemma lpNorm_norm
  given: (hf : AEStronglyMeasurable f μ) (p : Real>=0∞)
  proof: by
  rw [← toReal_eLpNorm hf]; rw [← toReal_eLpNorm (by fun_prop)]; simp

中文:
引理 lpNorm_norm
  条件: (hf : AEStronglyMeasurable f μ) (p : 实数>=0∞)
  证明: by
  rw [← toReal_eLpNorm hf]; rw [← toReal_eLpNorm (by fun_prop)]; simp
-/
@[simp] lemma lpNorm_norm (hf : AEStronglyMeasurable f μ) (p : Real>=0∞) :
    lpNorm (fun x => ‖f x‖) p μ = lpNorm f p μ := by
  rw [← toReal_eLpNorm hf]; rw [← toReal_eLpNorm (by fun_prop)]; simp

/--
lemma `lpNorm_abs` / 引理 `lpNorm_abs`

English:
lemma lpNorm_abs
  given: {f : α -> Real} (hf : AEStronglyMeasurable f μ) (p : Real>=0∞)
  proof: lpNorm_norm hf p

中文:
引理 lpNorm_abs
  条件: {f : α -> 实数} (hf : AEStronglyMeasurable f μ) (p : 实数>=0∞)
  证明: lpNorm_norm hf p
-/
@[simp] lemma lpNorm_abs {f : α -> Real} (hf : AEStronglyMeasurable f μ) (p : Real>=0∞) :
    lpNorm (|f|) p μ = lpNorm f p μ := lpNorm_norm hf p

/--
lemma `lpNorm_fun_abs` / 引理 `lpNorm_fun_abs`

English:
lemma lpNorm_fun_abs
  given: {f : α -> Real} (hf : AEStronglyMeasurable f μ) (p : Real>=0∞)
  proof: lpNorm_abs hf _

中文:
引理 lpNorm_fun_abs
  条件: {f : α -> 实数} (hf : AEStronglyMeasurable f μ) (p : 实数>=0∞)
  证明: lpNorm_abs hf _
-/
@[simp] lemma lpNorm_fun_abs {f : α -> Real} (hf : AEStronglyMeasurable f μ) (p : Real>=0∞) :
    lpNorm (fun x => |f x|) p μ = lpNorm f p μ := lpNorm_abs hf _

/--
lemma `lpNorm_const` / 引理 `lpNorm_const`

English:
lemma lpNorm_const
  given: (hp : p != 0) (hμ : μ != 0) (c : E)
  proof: by
  simp [lpNorm, eLpNorm_const c hp hμ, Measure.real, ENNReal.toReal_rpow,
    aestronglyMeasurable_const]

中文:
引理 lpNorm_const
  条件: (hp : p != 0) (hμ : μ != 0) (c : E)
  证明: by
  simp [lpNorm, eLpNorm_const c hp hμ, Measure.real, ENNReal.toReal_rpow,
    aestronglyMeasurable_const]
-/
@[simp] lemma lpNorm_const (hp : p != 0) (hμ : μ != 0) (c : E) :
    lpNorm (fun _x => c) p μ = ‖c‖ * μ.real .univ ^ p.toReal⁻¹ := by
  simp [lpNorm, eLpNorm_const c hp hμ, Measure.real, ENNReal.toReal_rpow,
    aestronglyMeasurable_const]

/--
lemma `lpNorm_const'` / 引理 `lpNorm_const'`

English:
lemma lpNorm_const'
  given: (hp₀ : p != 0) (hp : p != ∞) (c : E)
  proof: by
  simp [lpNorm, eLpNorm_const' c hp₀ hp, Measure.real, ENNReal.toReal_rpow,
    aestronglyMeasurable_const]

中文:
引理 lpNorm_const'
  条件: (hp₀ : p != 0) (hp : p != ∞) (c : E)
  证明: by
  simp [lpNorm, eLpNorm_const' c hp₀ hp, Measure.real, ENNReal.toReal_rpow,
    aestronglyMeasurable_const]
-/
@[simp] lemma lpNorm_const' (hp₀ : p != 0) (hp : p != ∞) (c : E) :
    lpNorm (fun _x => c) p μ = ‖c‖ * μ.real .univ ^ p.toReal⁻¹ := by
  simp [lpNorm, eLpNorm_const' c hp₀ hp, Measure.real, ENNReal.toReal_rpow,
    aestronglyMeasurable_const]

section NormedField
variable {𝕜 : Type*} [NormedField 𝕜]

/--
lemma `lpNorm_one` / 引理 `lpNorm_one`

English:
lemma lpNorm_one
  given: (hp : p != 0) (hμ : μ != 0)
  proof: by
  simp [Pi.one_def, lpNorm_const hp hμ, Measure.real, ENNReal.toReal_rpow]

中文:
引理 lpNorm_one
  条件: (hp : p != 0) (hμ : μ != 0)
  证明: by
  simp [Pi.one_def, lpNorm_const hp hμ, Measure.real, ENNReal.toReal_rpow]
-/
@[simp] lemma lpNorm_one (hp : p != 0) (hμ : μ != 0) :
    lpNorm (1 : α -> 𝕜) p μ = μ.real .univ ^ (p.toReal⁻¹ : Real) := by
  simp [Pi.one_def, lpNorm_const hp hμ, Measure.real, ENNReal.toReal_rpow]

/--
lemma `lpNorm_one'` / 引理 `lpNorm_one'`

English:
lemma lpNorm_one'
  given: (hp₀ : p != 0) (hp : p != ∞) (μ : Measure α)
  proof: by
  simp [Pi.one_def, lpNorm_const' hp₀ hp, Measure.real, ENNReal.toReal_rpow]

中文:
引理 lpNorm_one'
  条件: (hp₀ : p != 0) (hp : p != ∞) (μ : Measure α)
  证明: by
  simp [Pi.one_def, lpNorm_const' hp₀ hp, Measure.real, ENNReal.toReal_rpow]
-/
@[simp] lemma lpNorm_one' (hp₀ : p != 0) (hp : p != ∞) (μ : Measure α) :
    lpNorm (1 : α -> 𝕜) p μ = μ.real .univ ^ (p.toReal⁻¹ : Real) := by
  simp [Pi.one_def, lpNorm_const' hp₀ hp, Measure.real, ENNReal.toReal_rpow]

/--
lemma `lpNorm_const_smul` / 引理 `lpNorm_const_smul`

English:
lemma lpNorm_const_smul
  given: [Module 𝕜 E] [NormSMulClass 𝕜 E] (c : 𝕜) (f : α -> E) (μ : Measure α)
  proof: by
  by_cases hf : AEStronglyMeasurable f μ
  · simp [lpNorm, eLpNorm_const_smul, hf, hf.const_smul]
  obtain rfl | hc := eq_or_ne c 0
  · simp
  rw [lpNorm_of_not_aestronglyMeasurable hf]; rw [lpNorm_of_not_aestronglyMeasurable fun h => hf <| by
    simpa [hc] using h.const_smul c⁻¹]
  simp

中文:
引理 lpNorm_const_smul
  条件: [Module 𝕜 E] [NormSMulClass 𝕜 E] (c : 𝕜) (f : α -> E) (μ : Measure α)
  证明: by
  by_cases hf : AEStronglyMeasurable f μ
  · simp [lpNorm, eLpNorm_const_smul, hf, hf.const_smul]
  obtain rfl | hc := eq_or_ne c 0
  · simp
  rw [lpNorm_of_not_aestronglyMeasurable hf]; rw [lpNorm_of_not_aestronglyMeasurable fun h => hf <| by
    simpa [hc] using h.const_smul c⁻¹]
  simp

Depends on / 依赖: AEStronglyMeasurable, const_smul, eLpNorm_const_smul, eq_or_ne, h.const_smul, hf.const_smul, lpNorm, lpNorm_of_not_aestronglyMeasurable
-/
lemma lpNorm_const_smul [Module 𝕜 E] [NormSMulClass 𝕜 E] (c : 𝕜) (f : α -> E) (μ : Measure α) :
    lpNorm (c • f) p μ = ‖c‖₊ * lpNorm f p μ := by
  by_cases hf : AEStronglyMeasurable f μ
  · simp [lpNorm, eLpNorm_const_smul, hf, hf.const_smul]
  obtain rfl | hc := eq_or_ne c 0
  · simp
  rw [lpNorm_of_not_aestronglyMeasurable hf]; rw [lpNorm_of_not_aestronglyMeasurable fun h => hf <| by
    simpa [hc] using h.const_smul c⁻¹]
  simp

/--
lemma `lpNorm_nsmul` / 引理 `lpNorm_nsmul`

English:
lemma lpNorm_nsmul
  given: [NormedSpace Real E] (n : Nat) (f : α -> E) (μ : Measure α)
  proof: by
  simpa [Nat.cast_smul_eq_nsmul] using lpNorm_const_smul (n : Real) f μ (p := p)

中文:
引理 lpNorm_nsmul
  条件: [NormedSpace 实数 E] (n : 自然数) (f : α -> E) (μ : Measure α)
  证明: by
  simpa [Nat.cast_smul_eq_nsmul] using lpNorm_const_smul (n : Real) f μ (p := p)

Depends on / 依赖: Nat.cast_smul_eq_nsmul, cast_smul_eq_nsmul, lpNorm_const_smul
-/
lemma lpNorm_nsmul [NormedSpace Real E] (n : Nat) (f : α -> E) (μ : Measure α) :
    lpNorm (n • f) p μ = n • lpNorm f p μ := by
  simpa [Nat.cast_smul_eq_nsmul] using lpNorm_const_smul (n : Real) f μ (p := p)

variable [NormedSpace Real 𝕜]

/--
lemma `lpNorm_natCast_mul` / 引理 `lpNorm_natCast_mul`

English:
lemma lpNorm_natCast_mul
  given: (n : Nat) (f : α -> 𝕜) (p : Real>=0∞) (μ : Measure α)
  proof: by
  simpa only [nsmul_eq_mul] using lpNorm_nsmul n f μ

中文:
引理 lpNorm_natCast_mul
  条件: (n : 自然数) (f : α -> 𝕜) (p : 实数>=0∞) (μ : Measure α)
  证明: by
  simpa only [nsmul_eq_mul] using lpNorm_nsmul n f μ

Depends on / 依赖: lpNorm_nsmul, nsmul_eq_mul
-/
lemma lpNorm_natCast_mul (n : Nat) (f : α -> 𝕜) (p : Real>=0∞) (μ : Measure α) :
    lpNorm ((n : α -> 𝕜) * f) p μ = n * lpNorm f p μ := by
  simpa only [nsmul_eq_mul] using lpNorm_nsmul n f μ

/--
lemma `lpNorm_fun_natCast_mul` / 引理 `lpNorm_fun_natCast_mul`

English:
lemma lpNorm_fun_natCast_mul
  given: (n : Nat) (f : α -> 𝕜) (p : Real>=0∞) (μ : Measure α)
  proof: lpNorm_natCast_mul ..

中文:
引理 lpNorm_fun_natCast_mul
  条件: (n : 自然数) (f : α -> 𝕜) (p : 实数>=0∞) (μ : Measure α)
  证明: lpNorm_natCast_mul ..

Depends on / 依赖: lpNorm_natCast_mul
-/
lemma lpNorm_fun_natCast_mul (n : Nat) (f : α -> 𝕜) (p : Real>=0∞) (μ : Measure α) :
    lpNorm (n * f ·) p μ = n * lpNorm f p μ := lpNorm_natCast_mul ..

/--
lemma `lpNorm_mul_natCast` / 引理 `lpNorm_mul_natCast`

English:
lemma lpNorm_mul_natCast
  given: (f : α -> 𝕜) (n : Nat) (p : Real>=0∞) (μ : Measure α)
  proof: by
  simpa only [mul_comm] using lpNorm_natCast_mul n f p μ

中文:
引理 lpNorm_mul_natCast
  条件: (f : α -> 𝕜) (n : 自然数) (p : 实数>=0∞) (μ : Measure α)
  证明: by
  simpa only [mul_comm] using lpNorm_natCast_mul n f p μ

Depends on / 依赖: lpNorm_natCast_mul, mul_comm
-/
lemma lpNorm_mul_natCast (f : α -> 𝕜) (n : Nat) (p : Real>=0∞) (μ : Measure α) :
    lpNorm (f * (n : α -> 𝕜)) p μ = lpNorm f p μ * n := by
  simpa only [mul_comm] using lpNorm_natCast_mul n f p μ

/--
lemma `lpNorm_fun_mul_natCast` / 引理 `lpNorm_fun_mul_natCast`

English:
lemma lpNorm_fun_mul_natCast
  given: (f : α -> 𝕜) (n : Nat) (p : Real>=0∞) (μ : Measure α)
  proof: lpNorm_mul_natCast ..

中文:
引理 lpNorm_fun_mul_natCast
  条件: (f : α -> 𝕜) (n : 自然数) (p : 实数>=0∞) (μ : Measure α)
  证明: lpNorm_mul_natCast ..

Depends on / 依赖: lpNorm_mul_natCast
-/
lemma lpNorm_fun_mul_natCast (f : α -> 𝕜) (n : Nat) (p : Real>=0∞) (μ : Measure α) :
    lpNorm (f · * n) p μ = lpNorm f p μ * n := lpNorm_mul_natCast ..

/--
lemma `lpNorm_div_natCast` / 引理 `lpNorm_div_natCast`

English:
lemma lpNorm_div_natCast
  statement: [CharZero 𝕜] {n : Nat} (hn : n != 0) (f : α -> 𝕜) (p : Real>=0∞)
  proof: by
  rw [eq_div_iff (by positivity)]; rw [← lpNorm_mul_natCast]; simp [Pi.mul_def, hn]

中文:
引理 lpNorm_div_natCast
  结论: [CharZero 𝕜] {n : 自然数} (hn : n != 0) (f : α -> 𝕜) (p : 实数>=0∞)
  证明: by
  rw [eq_div_iff (by positivity)]; rw [← lpNorm_mul_natCast]; simp [Pi.mul_def, hn]

Depends on / 依赖: Pi.mul_def, eq_div_iff, lpNorm_mul_natCast, mul_def
-/
lemma lpNorm_div_natCast [CharZero 𝕜] {n : Nat} (hn : n != 0) (f : α -> 𝕜) (p : Real>=0∞)
    (μ : Measure α) : lpNorm (f / (n : α -> 𝕜)) p μ = lpNorm f p μ / n := by
  rw [eq_div_iff (by positivity)]; rw [← lpNorm_mul_natCast]; simp [Pi.mul_def, hn]

/--
lemma `lpNorm_fun_div_natCast` / 引理 `lpNorm_fun_div_natCast`

English:
lemma lpNorm_fun_div_natCast
  statement: [CharZero 𝕜] {n : Nat} (hn : n != 0) (f : α -> 𝕜) (p : Real>=0∞)
  proof: lpNorm_div_natCast hn ..

中文:
引理 lpNorm_fun_div_natCast
  结论: [CharZero 𝕜] {n : 自然数} (hn : n != 0) (f : α -> 𝕜) (p : 实数>=0∞)
  证明: lpNorm_div_natCast hn ..

Depends on / 依赖: lpNorm_div_natCast
-/
lemma lpNorm_fun_div_natCast [CharZero 𝕜] {n : Nat} (hn : n != 0) (f : α -> 𝕜) (p : Real>=0∞)
    (μ : Measure α) : lpNorm (f · / n) p μ = lpNorm f p μ / n := lpNorm_div_natCast hn ..

end NormedField

/--
lemma `lpNorm_add_le` / 引理 `lpNorm_add_le`

English:
lemma lpNorm_add_le
  given: (hf : MemLp f p μ) (hp : 1 <= p)
  proof: by
  by_cases hg : MemLp g p μ
  · rw [← toReal_eLpNorm (hf.add hg).aestronglyMeasurable,
      ← toReal_eLpNorm hf.aestronglyMeasurable, ← toReal_eLpNorm hg.aestronglyMeasurable,
      ← ENNReal.toReal_add hf.eLpNorm_ne_top hg.eLpNorm_ne_top]
    gcongr
    exacts [ENNReal.add_ne_top.2 ⟨hf.eLpNorm_

中文:
引理 lpNorm_add_le
  条件: (hf : MemLp f p μ) (hp : 1 <= p)
  证明: by
  by_cases hg : MemLp g p μ
  · rw [← toReal_eLpNorm (hf.add hg).aestronglyMeasurable,
      ← toReal_eLpNorm hf.aestronglyMeasurable, ← toReal_eLpNorm hg.aestronglyMeasurable,
      ← ENNReal.toReal_add hf.eLpNorm_ne_top hg.eLpNorm_ne_top]
    gcongr
    exacts [ENNReal.add_ne_top.2 ⟨hf.eLpNorm_

Depends on / 依赖: ENNReal, ENNReal.add_ne_top, ENNReal.toReal_add, add_ne_top, aestronglyMeasurable, eLpNorm_add_le, eLpNorm_ne_top, exacts, hf.add, hf.aestronglyMeasurable, hf.eLpNorm_ne_top, hfg.sub, hg.aestronglyMeasurable, hg.eLpNorm_ne_top, lpNorm_of_not_memLp, toReal_add, toReal_eLpNorm
-/
lemma lpNorm_add_le (hf : MemLp f p μ) (hp : 1 <= p) :
    lpNorm (f + g) p μ <= lpNorm f p μ + lpNorm g p μ := by
  by_cases hg : MemLp g p μ
  · rw [← toReal_eLpNorm (hf.add hg).aestronglyMeasurable,
      ← toReal_eLpNorm hf.aestronglyMeasurable, ← toReal_eLpNorm hg.aestronglyMeasurable,
      ← ENNReal.toReal_add hf.eLpNorm_ne_top hg.eLpNorm_ne_top]
    gcongr
    exacts [ENNReal.add_ne_top.2 ⟨hf.eLpNorm_ne_top, hg.eLpNorm_ne_top⟩,
      eLpNorm_add_le hf.aestronglyMeasurable hg.aestronglyMeasurable hp]
  · rw [lpNorm_of_not_memLp fun hfg => hg <| by simpa using hfg.sub hf, lpNorm_of_not_memLp hg]
    simp

/--
lemma `lpNorm_add_le'` / 引理 `lpNorm_add_le'`

English:
lemma lpNorm_add_le'
  given: (hg : MemLp g p μ) (hp : 1 <= p)
  proof: by
  simpa [add_comm] using lpNorm_add_le hg (g := f) hp

中文:
引理 lpNorm_add_le'
  条件: (hg : MemLp g p μ) (hp : 1 <= p)
  证明: by
  simpa [add_comm] using lpNorm_add_le hg (g := f) hp

Depends on / 依赖: add_comm, lpNorm_add_le
-/
lemma lpNorm_add_le' (hg : MemLp g p μ) (hp : 1 <= p) :
    lpNorm (f + g) p μ <= lpNorm f p μ + lpNorm g p μ := by
  simpa [add_comm] using lpNorm_add_le hg (g := f) hp

/--
lemma `lpNorm_sub_le` / 引理 `lpNorm_sub_le`

English:
lemma lpNorm_sub_le
  given: (hf : MemLp f p μ) (hp : 1 <= p)
  proof: by
  simpa [sub_eq_add_neg] using lpNorm_add_le hf (g := -g) hp

中文:
引理 lpNorm_sub_le
  条件: (hf : MemLp f p μ) (hp : 1 <= p)
  证明: by
  simpa [sub_eq_add_neg] using lpNorm_add_le hf (g := -g) hp

Depends on / 依赖: lpNorm_add_le, sub_eq_add_neg
-/
lemma lpNorm_sub_le (hf : MemLp f p μ) (hp : 1 <= p) :
    lpNorm (f - g) p μ <= lpNorm f p μ + lpNorm g p μ := by
  simpa [sub_eq_add_neg] using lpNorm_add_le hf (g := -g) hp

/--
lemma `lpNorm_le_lpNorm_add_lpNorm_sub'` / 引理 `lpNorm_le_lpNorm_add_lpNorm_sub'`

English:
lemma lpNorm_le_lpNorm_add_lpNorm_sub'
  given: (hg : MemLp g p μ) (hp : 1 <= p)
  proof: by
  simpa using lpNorm_add_le hg (g := f - g) hp

中文:
引理 lpNorm_le_lpNorm_add_lpNorm_sub'
  条件: (hg : MemLp g p μ) (hp : 1 <= p)
  证明: by
  simpa using lpNorm_add_le hg (g := f - g) hp

Depends on / 依赖: lpNorm_add_le
-/
lemma lpNorm_le_lpNorm_add_lpNorm_sub' (hg : MemLp g p μ) (hp : 1 <= p) :
    lpNorm f p μ <= lpNorm g p μ + lpNorm (f - g) p μ := by
  simpa using lpNorm_add_le hg (g := f - g) hp

/--
lemma `lpNorm_le_lpNorm_add_lpNorm_sub` / 引理 `lpNorm_le_lpNorm_add_lpNorm_sub`

English:
lemma lpNorm_le_lpNorm_add_lpNorm_sub
  given: (hg : MemLp g p μ) (hp : 1 <= p)
  proof: by
  simpa [neg_add_eq_sub] using lpNorm_add_le hg.neg (g := g - f) hp

中文:
引理 lpNorm_le_lpNorm_add_lpNorm_sub
  条件: (hg : MemLp g p μ) (hp : 1 <= p)
  证明: by
  simpa [neg_add_eq_sub] using lpNorm_add_le hg.neg (g := g - f) hp

Depends on / 依赖: hg.neg, lpNorm_add_le, neg_add_eq_sub
-/
lemma lpNorm_le_lpNorm_add_lpNorm_sub (hg : MemLp g p μ) (hp : 1 <= p) :
    lpNorm f p μ <= lpNorm g p μ + lpNorm (g - f) p μ := by
  simpa [neg_add_eq_sub] using lpNorm_add_le hg.neg (g := g - f) hp

/--
lemma `lpNorm_le_add_lpNorm_add` / 引理 `lpNorm_le_add_lpNorm_add`

English:
lemma lpNorm_le_add_lpNorm_add
  given: (hg : MemLp g p μ) (hp : 1 <= p)
  proof: by
  simpa using lpNorm_add_le' (f := f + g) hg.neg hp

中文:
引理 lpNorm_le_add_lpNorm_add
  条件: (hg : MemLp g p μ) (hp : 1 <= p)
  证明: by
  simpa using lpNorm_add_le' (f := f + g) hg.neg hp

Depends on / 依赖: hg.neg, lpNorm_add_le
-/
lemma lpNorm_le_add_lpNorm_add (hg : MemLp g p μ) (hp : 1 <= p) :
    lpNorm f p μ <= lpNorm (f + g) p μ + lpNorm g p μ := by
  simpa using lpNorm_add_le' (f := f + g) hg.neg hp

/--
lemma `lpNorm_sub_le_lpNorm_sub_add_lpNorm_sub` / 引理 `lpNorm_sub_le_lpNorm_sub_add_lpNorm_sub`

English:
lemma lpNorm_sub_le_lpNorm_sub_add_lpNorm_sub
  given: (hf : MemLp f p μ) (hg : MemLp g p μ) (hp : 1 <= p)
  proof: by
  simpa using lpNorm_add_le (hf.sub hg) (g := g - h) hp

中文:
引理 lpNorm_sub_le_lpNorm_sub_add_lpNorm_sub
  条件: (hf : MemLp f p μ) (hg : MemLp g p μ) (hp : 1 <= p)
  证明: by
  simpa using lpNorm_add_le (hf.sub hg) (g := g - h) hp

Depends on / 依赖: hf.sub, lpNorm_add_le
-/
lemma lpNorm_sub_le_lpNorm_sub_add_lpNorm_sub (hf : MemLp f p μ) (hg : MemLp g p μ) (hp : 1 <= p) :
    lpNorm (f - h) p μ <= lpNorm (f - g) p μ + lpNorm (g - h) p μ := by
  simpa using lpNorm_add_le (hf.sub hg) (g := g - h) hp

/--
lemma `lpNorm_sum_le` / 引理 `lpNorm_sum_le`

English:
lemma lpNorm_sum_le
  statement: {ι : Type*} {s : Finset ι} {f : ι -> α -> E} (hf : forall i in s, MemLp (f i) p μ)
  proof: by
  rw [← Finset.sum_congr rfl fun i hi => toReal_eLpNorm (hf i hi).aestronglyMeasurable]; rw [← ENNReal.toReal_sum fun i hi => (hf i hi).2.ne]; rw [← toReal_eLpNorm (Finset.aestronglyMeasurable_sum _ fun i hi => (hf i hi).aestronglyMeasurable)]
  grw [eLpNorm_sum_le (fun i hi => (hf _ hi).aestrong

中文:
引理 lpNorm_sum_le
  结论: {ι : 类型} {s : Finset ι} {f : ι -> α -> E} (hf : 对任意 i in s, MemLp (f i) p μ)
  证明: by
  rw [← Finset.sum_congr rfl fun i hi => toReal_eLpNorm (hf i hi).aestronglyMeasurable]; rw [← ENNReal.toReal_sum fun i hi => (hf i hi).2.ne]; rw [← toReal_eLpNorm (Finset.aestronglyMeasurable_sum _ fun i hi => (hf i hi).aestronglyMeasurable)]
  grw [eLpNorm_sum_le (fun i hi => (hf _ hi).aestrong

Depends on / 依赖: ENNReal, ENNReal.toReal_sum, Finset, Finset.aestronglyMeasurable_sum, Finset.sum_congr, aestronglyMeasurable, aestronglyMeasurable_sum, eLpNorm_sum_le, sum_congr, toReal_eLpNorm, toReal_sum
-/
lemma lpNorm_sum_le {ι : Type*} {s : Finset ι} {f : ι -> α -> E} (hf : forall i in s, MemLp (f i) p μ)
    (hp : 1 <= p) : lpNorm (∑ i in s, f i) p μ <= ∑ i in s, lpNorm (f i) p μ := by
  rw [← Finset.sum_congr rfl fun i hi => toReal_eLpNorm (hf i hi).aestronglyMeasurable]; rw [← ENNReal.toReal_sum fun i hi => (hf i hi).2.ne]; rw [← toReal_eLpNorm (Finset.aestronglyMeasurable_sum _ fun i hi => (hf i hi).aestronglyMeasurable)]
  grw [eLpNorm_sum_le (fun i hi => (hf _ hi).aestronglyMeasurable) hp]
  simpa using fun i hi => (hf i hi).2.ne

-- TODO: Golf using `eLpNorm_expect_le` once it exists
/--
lemma `lpNorm_expect_le` / 引理 `lpNorm_expect_le`

English:
lemma lpNorm_expect_le
  statement: [Module Rat>=0 E] [NormedSpace Real E] {ι : Type*} {s : Finset ι}
  proof: by
  obtain rfl | hs := s.eq_empty_or_nonempty
  · simp
  refine (le_inv_smul_iff_of_pos <| by positivity).2 ?_
  rw [Nat.cast_smul_eq_nsmul]; rw [← lpNorm_nsmul]; rw [Finset.card_smul_expect]
  exact lpNorm_sum_le hf hp

中文:
引理 lpNorm_expect_le
  结论: [Module Rat>=0 E] [NormedSpace 实数 E] {ι : 类型} {s : Finset ι}
  证明: by
  obtain rfl | hs := s.eq_empty_or_nonempty
  · simp
  refine (le_inv_smul_iff_of_pos <| by positivity).2 ?_
  rw [Nat.cast_smul_eq_nsmul]; rw [← lpNorm_nsmul]; rw [Finset.card_smul_expect]
  exact lpNorm_sum_le hf hp

Depends on / 依赖: Finset, Finset.card_smul_expect, Nat.cast_smul_eq_nsmul, card_smul_expect, cast_smul_eq_nsmul, eq_empty_or_nonempty, le_inv_smul_iff_of_pos, lpNorm_nsmul, lpNorm_sum_le, s.eq_empty_or_nonempty
-/
lemma lpNorm_expect_le [Module Rat>=0 E] [NormedSpace Real E] {ι : Type*} {s : Finset ι}
    {f : ι -> α -> E} (hf : forall i in s, MemLp (f i) p μ) (hp : 1 <= p) :
    lpNorm (𝔼 i in s, f i) p μ <= 𝔼 i in s, lpNorm (f i) p μ := by
  obtain rfl | hs := s.eq_empty_or_nonempty
  · simp
  refine (le_inv_smul_iff_of_pos <| by positivity).2 ?_
  rw [Nat.cast_smul_eq_nsmul]; rw [← lpNorm_nsmul]; rw [Finset.card_smul_expect]
  exact lpNorm_sum_le hf hp

/--
lemma `lpNorm_mono_real` / 引理 `lpNorm_mono_real`

English:
lemma lpNorm_mono_real
  given: {g : α -> Real} (hg : MemLp g p μ) (h : forall x, ‖f x‖ <= g x)
  proof: by
  by_cases hf : AEStronglyMeasurable f μ
  · rw [← toReal_eLpNorm hf, ← toReal_eLpNorm hg.aestronglyMeasurable]
    exact ENNReal.toNNReal_mono (hg.eLpNorm_ne_top) (eLpNorm_mono_real h)
  · simp [hf]

中文:
引理 lpNorm_mono_real
  条件: {g : α -> 实数} (hg : MemLp g p μ) (h : 对任意 x, ‖f x‖ <= g x)
  证明: by
  by_cases hf : AEStronglyMeasurable f μ
  · rw [← toReal_eLpNorm hf, ← toReal_eLpNorm hg.aestronglyMeasurable]
    exact ENNReal.toNNReal_mono (hg.eLpNorm_ne_top) (eLpNorm_mono_real h)
  · simp [hf]

Depends on / 依赖: AEStronglyMeasurable, ENNReal, ENNReal.toNNReal_mono, aestronglyMeasurable, eLpNorm_mono_real, eLpNorm_ne_top, hg.aestronglyMeasurable, hg.eLpNorm_ne_top, toNNReal_mono, toReal_eLpNorm
-/
lemma lpNorm_mono_real {g : α -> Real} (hg : MemLp g p μ) (h : forall x, ‖f x‖ <= g x) :
    lpNorm f p μ <= lpNorm g p μ := by
  by_cases hf : AEStronglyMeasurable f μ
  · rw [← toReal_eLpNorm hf, ← toReal_eLpNorm hg.aestronglyMeasurable]
    exact ENNReal.toNNReal_mono (hg.eLpNorm_ne_top) (eLpNorm_mono_real h)
  · simp [hf]

/--
lemma `lpNorm_smul_measure_of_ne_zero` / 引理 `lpNorm_smul_measure_of_ne_zero`

English:
lemma lpNorm_smul_measure_of_ne_zero
  given: {f : α -> E} {c : Real>=0} (hc : c != 0)
  proof: by
  by_cases hf : AEStronglyMeasurable f μ
  · simp [← toReal_eLpNorm, hf, hf.smul_measure, eLpNorm_smul_measure_of_ne_zero' hc f p μ]
    simp [ENNReal.smul_def, NNReal.smul_def]
  · rw [lpNorm_of_not_aestronglyMeasurable hf, lpNorm_of_not_aestronglyMeasurable fun h => hf <| by
      simpa [hc] us

中文:
引理 lpNorm_smul_measure_of_ne_zero
  条件: {f : α -> E} {c : 实数>=0} (hc : c != 0)
  证明: by
  by_cases hf : AEStronglyMeasurable f μ
  · simp [← toReal_eLpNorm, hf, hf.smul_measure, eLpNorm_smul_measure_of_ne_zero' hc f p μ]
    simp [ENNReal.smul_def, NNReal.smul_def]
  · rw [lpNorm_of_not_aestronglyMeasurable hf, lpNorm_of_not_aestronglyMeasurable fun h => hf <| by
      simpa [hc] us

Depends on / 依赖: AEStronglyMeasurable, ENNReal, ENNReal.smul_def, NNReal, NNReal.smul_def, eLpNorm_smul_measure_of_ne_zero, h.smul_measure, hf.smul_measure, lpNorm_of_not_aestronglyMeasurable, smul_def, smul_measure, toReal_eLpNorm
-/
lemma lpNorm_smul_measure_of_ne_zero {f : α -> E} {c : Real>=0} (hc : c != 0) :
    lpNorm f p (c • μ) = c ^ p.toReal⁻¹ • lpNorm f p μ := by
  by_cases hf : AEStronglyMeasurable f μ
  · simp [← toReal_eLpNorm, hf, hf.smul_measure, eLpNorm_smul_measure_of_ne_zero' hc f p μ]
    simp [ENNReal.smul_def, NNReal.smul_def]
  · rw [lpNorm_of_not_aestronglyMeasurable hf, lpNorm_of_not_aestronglyMeasurable fun h => hf <| by
      simpa [hc] using h.smul_measure c⁻¹]
    simp

/--
lemma `lpNorm_smul_measure_of_ne_top` / 引理 `lpNorm_smul_measure_of_ne_top`

English:
lemma lpNorm_smul_measure_of_ne_top
  given: (hp : p != ∞) {f : α -> E} (c : Real>=0)
  proof: by
  by_cases hf : AEStronglyMeasurable f μ
  · simp [← toReal_eLpNorm, hf, hf.smul_measure, eLpNorm_smul_measure_of_ne_top' hp]
    simp [ENNReal.smul_def, NNReal.smul_def]
  obtain rfl | hp₀ := eq_or_ne p 0
  · simp
  obtain rfl | hc := eq_or_ne c 0
  · rw [NNReal.zero_rpow (by simp [ENNReal.toRea

中文:
引理 lpNorm_smul_measure_of_ne_top
  条件: (hp : p != ∞) {f : α -> E} (c : 实数>=0)
  证明: by
  by_cases hf : AEStronglyMeasurable f μ
  · simp [← toReal_eLpNorm, hf, hf.smul_measure, eLpNorm_smul_measure_of_ne_top' hp]
    simp [ENNReal.smul_def, NNReal.smul_def]
  obtain rfl | hp₀ := eq_or_ne p 0
  · simp
  obtain rfl | hc := eq_or_ne c 0
  · rw [NNReal.zero_rpow (by simp [ENNReal.toRea

Depends on / 依赖: AEStronglyMeasurable, ENNReal, ENNReal.smul_def, ENNReal.toReal_eq_zero_iff, NNReal, NNReal.smul_def, NNReal.zero_rpow, eLpNorm_smul_measure_of_ne_top, eq_or_ne, h.smul_measure, hf.smul_measure, lpNorm_of_not_aestronglyMeasurable, smul_def, smul_measure, toReal_eLpNorm, toReal_eq_zero_iff, zero_rpow
-/
lemma lpNorm_smul_measure_of_ne_top (hp : p != ∞) {f : α -> E} (c : Real>=0) :
    lpNorm f p (c • μ) = c ^ p.toReal⁻¹ • lpNorm f p μ := by
  by_cases hf : AEStronglyMeasurable f μ
  · simp [← toReal_eLpNorm, hf, hf.smul_measure, eLpNorm_smul_measure_of_ne_top' hp]
    simp [ENNReal.smul_def, NNReal.smul_def]
  obtain rfl | hp₀ := eq_or_ne p 0
  · simp
  obtain rfl | hc := eq_or_ne c 0
  · rw [NNReal.zero_rpow (by simp [ENNReal.toReal_eq_zero_iff, *])]
    simp
  rw [lpNorm_of_not_aestronglyMeasurable hf]; rw [lpNorm_of_not_aestronglyMeasurable fun h => hf <| by
    simpa [hc] using h.smul_measure c⁻¹]
  simp

/--
lemma `lpNorm_conj` / 引理 `lpNorm_conj`

English:
lemma lpNorm_conj
  given: {K : Type*} [RCLike K] (f : α -> K) (p : Real>=0∞) (μ : Measure α)
  proof: by
  by_cases hf : AEStronglyMeasurable f μ
  · rw [← lpNorm_norm hf, ← lpNorm_norm]
    · simp
    · exact (continuous_star.measurable.comp_aemeasurable hf.aemeasurable).aestronglyMeasurable
  · rw [lpNorm_of_not_aestronglyMeasurable hf, lpNorm_of_not_aestronglyMeasurable fun h => hf ?_]
    simpa 

中文:
引理 lpNorm_conj
  条件: {K : 类型} [RCLike K] (f : α -> K) (p : 实数>=0∞) (μ : Measure α)
  证明: by
  by_cases hf : AEStronglyMeasurable f μ
  · rw [← lpNorm_norm hf, ← lpNorm_norm]
    · simp
    · exact (continuous_star.measurable.comp_aemeasurable hf.aemeasurable).aestronglyMeasurable
  · rw [lpNorm_of_not_aestronglyMeasurable hf, lpNorm_of_not_aestronglyMeasurable fun h => hf ?_]
    simpa 
-/
@[simp] lemma lpNorm_conj {K : Type*} [RCLike K] (f : α -> K) (p : Real>=0∞) (μ : Measure α) :
    lpNorm (conj f) p μ = lpNorm f p μ := by
  by_cases hf : AEStronglyMeasurable f μ
  · rw [← lpNorm_norm hf, ← lpNorm_norm]
    · simp
    · exact (continuous_star.measurable.comp_aemeasurable hf.aemeasurable).aestronglyMeasurable
  · rw [lpNorm_of_not_aestronglyMeasurable hf, lpNorm_of_not_aestronglyMeasurable fun h => hf ?_]
    simpa [Function.comp_def]
      using (continuous_star.measurable.comp_aemeasurable h.aemeasurable).aestronglyMeasurable

end MeasureTheory
