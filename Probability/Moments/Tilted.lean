/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.Measure.Tilted
public import Mathlib.Probability.Moments.MGFAnalytic

/-!
# Results relating `Measure.tilted` to `mgf` and `cgf`

For a random variable `X : Ω → ℝ` and a measure `μ`, the tilted measure `μ.tilted (t * X ·)` is
linked to the moment-generating function (`mgf`) and the cumulant-generating function (`cgf`)
of `X`.

## Main statements

* `integral_tilted_mul_self`: the integral of `X` against the tilted measure `μ.tilted (t * X ·)`
  is the first derivative of the cumulant-generating function of `X` at `t`.
  `(μ.tilted (t * X ·))[X] = deriv (cgf X μ) t`
* `variance_tilted_mul`: the variance of `X` under the tilted measure `μ.tilted (t * X ·)`
  is the second derivative of the cumulant-generating function of `X` at `t`.
  `Var[X; μ.tilted (t * X ·)] = iteratedDeriv 2 (cgf X μ) t`

-/

public section


open MeasureTheory Real Set Finset

open scoped NNReal ENNReal ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ ν : Measure Ω} {X : Ω -> Real} {t u : Real}

namespace ProbabilityTheory

section Apply


/--
lemma `tilted_mul_apply_mgf'` / 引理 `tilted_mul_apply_mgf'`

English:
lemma tilted_mul_apply_mgf'
  given: {s : Set Ω} (hs : MeasurableSet s)
  proof: by
  rw [tilted_apply' _ _ hs]; rw [mgf]

中文:
引理 tilted_mul_apply_mgf'
  条件: {s : 集合 Ω} (hs : 可测集 s)
  证明: by
  rw [tilted_apply' _ _ hs]; rw [mgf]

Depends on / 依赖: tilted_apply
-/
lemma tilted_mul_apply_mgf' {s : Set Ω} (hs : MeasurableSet s) :
    μ.tilted (t * X ·) s = ∫⁻ a in s, ENNReal.ofReal (exp (t * X a) / mgf X μ t) ∂μ := by
  rw [tilted_apply' _ _ hs]; rw [mgf]

/--
lemma `tilted_mul_apply_mgf` / 引理 `tilted_mul_apply_mgf`

English:
lemma tilted_mul_apply_mgf
  given: [SFinite μ] (s : Set Ω)
  proof: by
  rw [tilted_apply]; rw [mgf]

中文:
引理 tilted_mul_apply_mgf
  条件: [SFinite μ] (s : 集合 Ω)
  证明: by
  rw [tilted_apply]; rw [mgf]

Depends on / 依赖: tilted_apply
-/
lemma tilted_mul_apply_mgf [SFinite μ] (s : Set Ω) :
    μ.tilted (t * X ·) s = ∫⁻ a in s, ENNReal.ofReal (exp (t * X a) / mgf X μ t) ∂μ := by
  rw [tilted_apply]; rw [mgf]

/--
lemma `tilted_mul_apply_cgf'` / 引理 `tilted_mul_apply_cgf'`

English:
lemma tilted_mul_apply_cgf'
  statement: {s : Set Ω} (hs : MeasurableSet s)
  proof: by
  rcases eq_zero_or_neZero μ with rfl | hμ
  · simp
  · simp_rw [tilted_mul_apply_mgf' hs, exp_sub, exp_cgf ht]

中文:
引理 tilted_mul_apply_cgf'
  结论: {s : 集合 Ω} (hs : 可测集 s)
  证明: by
  rcases eq_zero_or_neZero μ with rfl | hμ
  · simp
  · simp_rw [tilted_mul_apply_mgf' hs, exp_sub, exp_cgf ht]

Depends on / 依赖: eq_zero_or_neZero, exp_cgf, exp_sub, simp_rw, tilted_mul_apply_mgf
-/
lemma tilted_mul_apply_cgf' {s : Set Ω} (hs : MeasurableSet s)
    (ht : Integrable (fun ω => exp (t * X ω)) μ) :
    μ.tilted (t * X ·) s = ∫⁻ a in s, ENNReal.ofReal (exp (t * X a - cgf X μ t)) ∂μ := by
  rcases eq_zero_or_neZero μ with rfl | hμ
  · simp
  · simp_rw [tilted_mul_apply_mgf' hs, exp_sub, exp_cgf ht]

/--
lemma `tilted_mul_apply_cgf` / 引理 `tilted_mul_apply_cgf`

English:
lemma tilted_mul_apply_cgf
  given: [SFinite μ] (s : Set Ω) (ht : Integrable (fun ω => exp (t * X ω)) μ)
  proof: by
  rcases eq_zero_or_neZero μ with rfl | hμ
  · simp
  · simp_rw [tilted_mul_apply_mgf s, exp_sub, exp_cgf ht]

中文:
引理 tilted_mul_apply_cgf
  条件: [SFinite μ] (s : 集合 Ω) (ht : 可积 (fun ω => exp (t * X ω)) μ)
  证明: by
  rcases eq_zero_or_neZero μ with rfl | hμ
  · simp
  · simp_rw [tilted_mul_apply_mgf s, exp_sub, exp_cgf ht]

Depends on / 依赖: eq_zero_or_neZero, exp_cgf, exp_sub, simp_rw, tilted_mul_apply_mgf
-/
lemma tilted_mul_apply_cgf [SFinite μ] (s : Set Ω) (ht : Integrable (fun ω => exp (t * X ω)) μ) :
    μ.tilted (t * X ·) s = ∫⁻ a in s, ENNReal.ofReal (exp (t * X a - cgf X μ t)) ∂μ := by
  rcases eq_zero_or_neZero μ with rfl | hμ
  · simp
  · simp_rw [tilted_mul_apply_mgf s, exp_sub, exp_cgf ht]

/--
lemma `tilted_mul_apply_eq_ofReal_integral_mgf'` / 引理 `tilted_mul_apply_eq_ofReal_integral_mgf'`

English:
lemma tilted_mul_apply_eq_ofReal_integral_mgf'
  given: {s : Set Ω} (hs : MeasurableSet s)
  proof: by
  rw [tilted_apply_eq_ofReal_integral' _ hs]; rw [mgf]

中文:
引理 tilted_mul_apply_eq_of实数_integral_mgf'
  条件: {s : 集合 Ω} (hs : 可测集 s)
  证明: by
  rw [tilted_apply_eq_ofReal_integral' _ hs]; rw [mgf]

Depends on / 依赖: tilted_apply_eq_ofReal_integral
-/
lemma tilted_mul_apply_eq_ofReal_integral_mgf' {s : Set Ω} (hs : MeasurableSet s) :
    μ.tilted (t * X ·) s = ENNReal.ofReal (∫ a in s, exp (t * X a) / mgf X μ t ∂μ) := by
  rw [tilted_apply_eq_ofReal_integral' _ hs]; rw [mgf]

/--
lemma `tilted_mul_apply_eq_ofReal_integral_mgf` / 引理 `tilted_mul_apply_eq_ofReal_integral_mgf`

English:
lemma tilted_mul_apply_eq_ofReal_integral_mgf
  given: [SFinite μ] (s : Set Ω)
  proof: by
  rw [tilted_apply_eq_ofReal_integral _ s]; rw [mgf]

中文:
引理 tilted_mul_apply_eq_of实数_integral_mgf
  条件: [SFinite μ] (s : 集合 Ω)
  证明: by
  rw [tilted_apply_eq_ofReal_integral _ s]; rw [mgf]

Depends on / 依赖: tilted_apply_eq_ofReal_integral
-/
lemma tilted_mul_apply_eq_ofReal_integral_mgf [SFinite μ] (s : Set Ω) :
    μ.tilted (t * X ·) s = ENNReal.ofReal (∫ a in s, exp (t * X a) / mgf X μ t ∂μ) := by
  rw [tilted_apply_eq_ofReal_integral _ s]; rw [mgf]

/--
lemma `tilted_mul_apply_eq_ofReal_integral_cgf'` / 引理 `tilted_mul_apply_eq_ofReal_integral_cgf'`

English:
lemma tilted_mul_apply_eq_ofReal_integral_cgf'
  statement: {s : Set Ω} (hs : MeasurableSet s)
  proof: by
  rcases eq_zero_or_neZero μ with rfl | hμ
  · simp
  · simp_rw [tilted_mul_apply_eq_ofReal_integral_mgf' hs, exp_sub]
    rwa [exp_cgf]

中文:
引理 tilted_mul_apply_eq_of实数_integral_cgf'
  结论: {s : 集合 Ω} (hs : 可测集 s)
  证明: by
  rcases eq_zero_or_neZero μ with rfl | hμ
  · simp
  · simp_rw [tilted_mul_apply_eq_ofReal_integral_mgf' hs, exp_sub]
    rwa [exp_cgf]

Depends on / 依赖: eq_zero_or_neZero, exp_cgf, exp_sub, simp_rw, tilted_mul_apply_eq_ofReal_integral_mgf
-/
lemma tilted_mul_apply_eq_ofReal_integral_cgf' {s : Set Ω} (hs : MeasurableSet s)
    (ht : Integrable (fun ω => exp (t * X ω)) μ) :
    μ.tilted (t * X ·) s = ENNReal.ofReal (∫ a in s, exp (t * X a - cgf X μ t) ∂μ) := by
  rcases eq_zero_or_neZero μ with rfl | hμ
  · simp
  · simp_rw [tilted_mul_apply_eq_ofReal_integral_mgf' hs, exp_sub]
    rwa [exp_cgf]

/--
lemma `tilted_mul_apply_eq_ofReal_integral_cgf` / 引理 `tilted_mul_apply_eq_ofReal_integral_cgf`

English:
lemma tilted_mul_apply_eq_ofReal_integral_cgf
  statement: [SFinite μ] (s : Set Ω)
  proof: by
  rcases eq_zero_or_neZero μ with rfl | hμ
  · simp
  · simp_rw [tilted_mul_apply_eq_ofReal_integral_mgf s, exp_sub]
    rwa [exp_cgf]

中文:
引理 tilted_mul_apply_eq_of实数_integral_cgf
  结论: [SFinite μ] (s : 集合 Ω)
  证明: by
  rcases eq_zero_or_neZero μ with rfl | hμ
  · simp
  · simp_rw [tilted_mul_apply_eq_ofReal_integral_mgf s, exp_sub]
    rwa [exp_cgf]

Depends on / 依赖: eq_zero_or_neZero, exp_cgf, exp_sub, simp_rw, tilted_mul_apply_eq_ofReal_integral_mgf
-/
lemma tilted_mul_apply_eq_ofReal_integral_cgf [SFinite μ] (s : Set Ω)
    (ht : Integrable (fun ω => exp (t * X ω)) μ) :
    μ.tilted (t * X ·) s = ENNReal.ofReal (∫ a in s, exp (t * X a - cgf X μ t) ∂μ) := by
  rcases eq_zero_or_neZero μ with rfl | hμ
  · simp
  · simp_rw [tilted_mul_apply_eq_ofReal_integral_mgf s, exp_sub]
    rwa [exp_cgf]

end Apply

section Integral

/-! ### Integral of `tilted` expressed with `mgf` or `cgf`. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]

/--
lemma `setIntegral_tilted_mul_eq_mgf'` / 引理 `setIntegral_tilted_mul_eq_mgf'`

English:
lemma setIntegral_tilted_mul_eq_mgf'
  given: (g : Ω -> E) {s : Set Ω} (hs : MeasurableSet s)
  proof: by
  rw [setIntegral_tilted' _ _ hs]; rw [mgf]

中文:
引理 set整数egral_tilted_mul_eq_mgf'
  条件: (g : Ω -> E) {s : 集合 Ω} (hs : 可测集 s)
  证明: by
  rw [setIntegral_tilted' _ _ hs]; rw [mgf]

Depends on / 依赖: setIntegral_tilted
-/
lemma setIntegral_tilted_mul_eq_mgf' (g : Ω -> E) {s : Set Ω} (hs : MeasurableSet s) :
    ∫ x in s, g x ∂(μ.tilted (t * X ·)) = ∫ x in s, (exp (t * X x) / mgf X μ t) • (g x) ∂μ := by
  rw [setIntegral_tilted' _ _ hs]; rw [mgf]

/--
lemma `setIntegral_tilted_mul_eq_mgf` / 引理 `setIntegral_tilted_mul_eq_mgf`

English:
lemma setIntegral_tilted_mul_eq_mgf
  given: [SFinite μ] (g : Ω -> E) (s : Set Ω)
  proof: by
  rw [setIntegral_tilted]; rw [mgf]

中文:
引理 set整数egral_tilted_mul_eq_mgf
  条件: [SFinite μ] (g : Ω -> E) (s : 集合 Ω)
  证明: by
  rw [setIntegral_tilted]; rw [mgf]

Depends on / 依赖: setIntegral_tilted
-/
lemma setIntegral_tilted_mul_eq_mgf [SFinite μ] (g : Ω -> E) (s : Set Ω) :
    ∫ x in s, g x ∂(μ.tilted (t * X ·)) = ∫ x in s, (exp (t * X x) / mgf X μ t) • (g x) ∂μ := by
  rw [setIntegral_tilted]; rw [mgf]

/--
lemma `setIntegral_tilted_mul_eq_cgf'` / 引理 `setIntegral_tilted_mul_eq_cgf'`

English:
lemma setIntegral_tilted_mul_eq_cgf'
  statement: (g : Ω -> E) {s : Set Ω}
  proof: by
  rcases eq_zero_or_neZero μ with rfl | hμ
  · simp
  · simp_rw [setIntegral_tilted_mul_eq_mgf' _ hs, exp_sub, exp_cgf ht]

中文:
引理 set整数egral_tilted_mul_eq_cgf'
  结论: (g : Ω -> E) {s : 集合 Ω}
  证明: by
  rcases eq_zero_or_neZero μ with rfl | hμ
  · simp
  · simp_rw [setIntegral_tilted_mul_eq_mgf' _ hs, exp_sub, exp_cgf ht]

Depends on / 依赖: eq_zero_or_neZero, exp_cgf, exp_sub, setIntegral_tilted_mul_eq_mgf, simp_rw
-/
lemma setIntegral_tilted_mul_eq_cgf' (g : Ω -> E) {s : Set Ω}
    (hs : MeasurableSet s) (ht : Integrable (fun ω => exp (t * X ω)) μ) :
    ∫ x in s, g x ∂(μ.tilted (t * X ·)) = ∫ x in s, exp (t * X x - cgf X μ t) • (g x) ∂μ := by
  rcases eq_zero_or_neZero μ with rfl | hμ
  · simp
  · simp_rw [setIntegral_tilted_mul_eq_mgf' _ hs, exp_sub, exp_cgf ht]

/--
lemma `setIntegral_tilted_mul_eq_cgf` / 引理 `setIntegral_tilted_mul_eq_cgf`

English:
lemma setIntegral_tilted_mul_eq_cgf
  statement: [SFinite μ] (g : Ω -> E) (s : Set Ω)
  proof: by
  rcases eq_zero_or_neZero μ with rfl | hμ
  · simp
  · simp_rw [setIntegral_tilted_mul_eq_mgf, exp_sub, exp_cgf ht]

中文:
引理 set整数egral_tilted_mul_eq_cgf
  结论: [SFinite μ] (g : Ω -> E) (s : 集合 Ω)
  证明: by
  rcases eq_zero_or_neZero μ with rfl | hμ
  · simp
  · simp_rw [setIntegral_tilted_mul_eq_mgf, exp_sub, exp_cgf ht]

Depends on / 依赖: eq_zero_or_neZero, exp_cgf, exp_sub, setIntegral_tilted_mul_eq_mgf, simp_rw
-/
lemma setIntegral_tilted_mul_eq_cgf [SFinite μ] (g : Ω -> E) (s : Set Ω)
    (ht : Integrable (fun ω => exp (t * X ω)) μ) :
    ∫ x in s, g x ∂(μ.tilted (t * X ·)) = ∫ x in s, exp (t * X x - cgf X μ t) • (g x) ∂μ := by
  rcases eq_zero_or_neZero μ with rfl | hμ
  · simp
  · simp_rw [setIntegral_tilted_mul_eq_mgf, exp_sub, exp_cgf ht]

/--
lemma `integral_tilted_mul_eq_mgf` / 引理 `integral_tilted_mul_eq_mgf`

English:
lemma integral_tilted_mul_eq_mgf
  given: (g : Ω -> E)
  proof: by
  rw [integral_tilted]; rw [mgf]

中文:
引理 integral_tilted_mul_eq_mgf
  条件: (g : Ω -> E)
  证明: by
  rw [integral_tilted]; rw [mgf]

Depends on / 依赖: integral_tilted
-/
lemma integral_tilted_mul_eq_mgf (g : Ω -> E) :
    ∫ ω, g ω ∂(μ.tilted (t * X ·)) = ∫ ω, (exp (t * X ω) / mgf X μ t) • (g ω) ∂μ := by
  rw [integral_tilted]; rw [mgf]

/--
lemma `integral_tilted_mul_eq_cgf` / 引理 `integral_tilted_mul_eq_cgf`

English:
lemma integral_tilted_mul_eq_cgf
  given: (g : Ω -> E) (ht : Integrable (fun ω => exp (t * X ω)) μ)
  proof: by
  rcases eq_zero_or_neZero μ with rfl | hμ
  · simp
  · simp_rw [integral_tilted_mul_eq_mgf, exp_sub]
    rwa [exp_cgf]

中文:
引理 integral_tilted_mul_eq_cgf
  条件: (g : Ω -> E) (ht : 可积 (fun ω => exp (t * X ω)) μ)
  证明: by
  rcases eq_zero_or_neZero μ with rfl | hμ
  · simp
  · simp_rw [integral_tilted_mul_eq_mgf, exp_sub]
    rwa [exp_cgf]

Depends on / 依赖: eq_zero_or_neZero, exp_cgf, exp_sub, integral_tilted_mul_eq_mgf, simp_rw
-/
lemma integral_tilted_mul_eq_cgf (g : Ω -> E) (ht : Integrable (fun ω => exp (t * X ω)) μ) :
    ∫ ω, g ω ∂(μ.tilted (t * X ·)) = ∫ ω, exp (t * X ω - cgf X μ t) • (g ω) ∂μ := by
  rcases eq_zero_or_neZero μ with rfl | hμ
  · simp
  · simp_rw [integral_tilted_mul_eq_mgf, exp_sub]
    rwa [exp_cgf]

/--
lemma `integral_tilted_mul_self` / 引理 `integral_tilted_mul_self`

English:
lemma integral_tilted_mul_self
  given: (ht : t in interior (integrableExpSet X μ))
  proof: by
  simp_rw [integral_tilted_mul_eq_mgf, deriv_cgf ht, ← integral_div, smul_eq_mul]
  congr with ω
  ring

中文:
引理 integral_tilted_mul_self
  条件: (ht : t in interior (integrableExpSet X μ))
  证明: by
  simp_rw [integral_tilted_mul_eq_mgf, deriv_cgf ht, ← integral_div, smul_eq_mul]
  congr with ω
  ring

Depends on / 依赖: deriv_cgf, integral_div, integral_tilted_mul_eq_mgf, simp_rw, smul_eq_mul
-/
lemma integral_tilted_mul_self (ht : t in interior (integrableExpSet X μ)) :
    (μ.tilted (t * X ·))[X] = deriv (cgf X μ) t := by
  simp_rw [integral_tilted_mul_eq_mgf, deriv_cgf ht, ← integral_div, smul_eq_mul]
  congr with ω
  ring

end Integral

/--
lemma `memLp_tilted_mul` / 引理 `memLp_tilted_mul`

English:
lemma memLp_tilted_mul
  given: (ht : t in interior (integrableExpSet X μ)) (p : Real>=0)
  proof: by
  have hX : AEMeasurable X μ := aemeasurable_of_mem_interior_integrableExpSet ht
  by_cases hp : p = 0
  · simpa [hp] using hX.aestronglyMeasurable.mono_ac (tilted_absolutelyContinuous _ _)
  refine ⟨hX.aestronglyMeasurable.mono_ac (tilted_absolutelyContinuous _ _), ?_⟩
  rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top]
  rotate_left
  · simp [hp]
  · simp
  simp_rw [ENNReal.coe_toReal, ← ofReal_norm, norm_eq_abs,
    ENNReal.ofReal_rpow_of_nonneg (x := |X _|) (p := p) (abs_nonneg (X _)) p.2]
  refine Integrable.lintegral_lt_top ?_
  simp_rw [integrable_tilted_iff (interior_subset (s := integrableExpSet X μ) ht),
    smul_eq_mul, mul_comm]
  exact integrable_rpow_abs_mul_exp_of_mem_interior_integrableExpSet ht p.2

中文:
引理 memLp_tilted_mul
  条件: (ht : t in interior (integrableExpSet X μ)) (p : 实数>=0)
  证明: by
  have hX : AEMeasurable X μ := aemeasurable_of_mem_interior_integrableExpSet ht
  by_cases hp : p = 0
  · simpa [hp] using hX.aestronglyMeasurable.mono_ac (tilted_absolutelyContinuous _ _)
  refine ⟨hX.aestronglyMeasurable.mono_ac (tilted_absolutelyContinuous _ _), ?_⟩
  rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top]
  rotate_left
  · simp [hp]
  · simp
  simp_rw [ENNReal.coe_toReal, ← ofReal_norm, norm_eq_abs,
    ENNReal.ofReal_rpow_of_nonneg (x := |X _|) (p := p) (abs_nonneg (X _)) p.2]
  refine Integrable.lintegral_lt_top ?_
  simp_rw [integrable_tilted_iff (interior_subset (s := integrableExpSet X μ) ht),
    smul_eq_mul, mul_comm]
  exact integrable_rpow_abs_mul_exp_of_mem_interior_integrableExpSet ht p.2

Depends on / 依赖: AEMeasurable, ENNReal, ENNReal.coe_toReal, ENNReal.ofReal_rpow_of_nonneg, Integrable, abs_nonneg, aemeasurable_of_mem_interior_integrableExpSet, aestronglyMeasurable, coe_toReal, eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top, hX.aestronglyMeasurable.mono_ac, mono_ac, norm_eq_abs, ofReal_norm, ofReal_rpow_of_nonneg, rotate_left, simp_rw, tilted_absolutelyContinuous
-/
lemma memLp_tilted_mul (ht : t in interior (integrableExpSet X μ)) (p : Real>=0) :
    MemLp X p (μ.tilted (t * X ·)) := by
  have hX : AEMeasurable X μ := aemeasurable_of_mem_interior_integrableExpSet ht
  by_cases hp : p = 0
  · simpa [hp] using hX.aestronglyMeasurable.mono_ac (tilted_absolutelyContinuous _ _)
  refine ⟨hX.aestronglyMeasurable.mono_ac (tilted_absolutelyContinuous _ _), ?_⟩
  rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top]
  rotate_left
  · simp [hp]
  · simp
  simp_rw [ENNReal.coe_toReal, ← ofReal_norm, norm_eq_abs,
    ENNReal.ofReal_rpow_of_nonneg (x := |X _|) (p := p) (abs_nonneg (X _)) p.2]
  refine Integrable.lintegral_lt_top ?_
  simp_rw [integrable_tilted_iff (interior_subset (s := integrableExpSet X μ) ht),
    smul_eq_mul, mul_comm]
  exact integrable_rpow_abs_mul_exp_of_mem_interior_integrableExpSet ht p.2

/--
lemma `variance_tilted_mul` / 引理 `variance_tilted_mul`

English:
lemma variance_tilted_mul
  given: (ht : t in interior (integrableExpSet X μ))
  proof: by
  rw [variance_eq_integral]
  swap; · exact (memLp_tilted_mul ht 1).aestronglyMeasurable.aemeasurable
  rw [integral_tilted_mul_self ht]; rw [iteratedDeriv_two_cgf_eq_integral ht]; rw [integral_tilted_mul_eq_mgf]; rw [← integral_div]
  simp only [smul_eq_mul]
  congr with ω
  ring

中文:
引理 variance_tilted_mul
  条件: (ht : t in interior (integrableExpSet X μ))
  证明: by
  rw [variance_eq_integral]
  swap; · exact (memLp_tilted_mul ht 1).aestronglyMeasurable.aemeasurable
  rw [integral_tilted_mul_self ht]; rw [iteratedDeriv_two_cgf_eq_integral ht]; rw [integral_tilted_mul_eq_mgf]; rw [← integral_div]
  simp only [smul_eq_mul]
  congr with ω
  ring

Depends on / 依赖: aemeasurable, aestronglyMeasurable, aestronglyMeasurable.aemeasurable, integral_div, integral_tilted_mul_eq_mgf, integral_tilted_mul_self, iteratedDeriv_two_cgf_eq_integral, memLp_tilted_mul, smul_eq_mul, variance_eq_integral
-/
lemma variance_tilted_mul (ht : t in interior (integrableExpSet X μ)) :
    Var[X; μ.tilted (t * X ·)] = iteratedDeriv 2 (cgf X μ) t := by
  rw [variance_eq_integral]
  swap; · exact (memLp_tilted_mul ht 1).aestronglyMeasurable.aemeasurable
  rw [integral_tilted_mul_self ht]; rw [iteratedDeriv_two_cgf_eq_integral ht]; rw [integral_tilted_mul_eq_mgf]; rw [← integral_div]
  simp only [smul_eq_mul]
  congr with ω
  ring

end ProbabilityTheory
