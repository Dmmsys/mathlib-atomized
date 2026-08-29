/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
-/
module

public import Mathlib.InformationTheory.KullbackLeibler.KLFun
public import Mathlib.MeasureTheory.Measure.Decomposition.IntegralRNDeriv

/-!
# Kullback-Leibler divergence

The Kullback-Leibler divergence is a measure of the difference between two measures.

## Main definitions

* `klDiv μ ν`: Kullback-Leibler divergence between two measures, with value in `ℝ≥0∞`,
  defined as `∞` if `μ` is not absolutely continuous with respect to `ν` or
  if the log-likelihood ratio `llr μ ν` is not integrable with respect to `μ`, and by
  `ENNReal.ofReal (∫ x, llr μ ν x ∂μ + ν.real - μ.real univ)` otherwise.

Note that our Kullback-Leibler divergence is nonnegative by definition (it takes value in `ℝ≥0∞`).
However `∫ x, llr μ ν x ∂μ + ν.real univ - μ.real univ` is nonnegative for all finite
measures `μ ≪ ν`, as proved in the lemma `integral_llr_add_sub_measure_univ_nonneg`.
That lemma is our version of Gibbs' inequality ("the Kullback-Leibler divergence is nonnegative").

## Main statements

* `klDiv_eq_zero_iff` : the Kullback-Leibler divergence between two finite measures is zero if and
  only if the two measures are equal.

## Implementation details

The Kullback-Leibler divergence on probability measures is `∫ x, llr μ ν x ∂μ` if `μ ≪ ν`
(and the log-likelihood ratio is integrable) and `∞` otherwise.
The definition we use extends this to finite measures by introducing a correction term
`ν.real univ - μ.real univ`. The definition of the divergence thus uses the formula
`∫ x, llr μ ν x ∂μ + ν.real univ - μ.real univ`, which is nonnegative for all finite
measures `μ ≪ ν`. This also makes `klDiv μ ν` equal to an f-divergence: it equals the integral
`∫ x, klFun (μ.rnDeriv ν x).toReal ∂ν`, in which `klFun x = x * log x + 1 - x`.

-/

@[expose] public section

open Real MeasureTheory Set

open scoped ENNReal NNReal

namespace InformationTheory

variable {α : Type*} {mα : MeasurableSpace α} {μ ν : Measure α}

open scoped Classical in
/-- Kullback-Leibler divergence between two measures. -/
noncomputable irreducible_def klDiv (μ ν : Measure α) : Real>=0∞ :=
  if μ ≪ ν ∧ Integrable (llr μ ν) μ
    then ENNReal.ofReal (∫ x, llr μ ν x ∂μ + ν.real univ - μ.real univ)
    else ∞

/--
lemma `klDiv_of_ac_of_integrable` / 引理 `klDiv_of_ac_of_integrable`

English:
lemma klDiv_of_ac_of_integrable
  given: (h1 : μ ≪ ν) (h2 : Integrable (llr μ ν) μ)
  proof: by
  rw [klDiv_def]
  exact if_pos ⟨h1, h2⟩

@[simp]

中文:
引理 klDiv_of_ac_of_integrable
  条件: (h1 : μ ≪ ν) (h2 : 可积 (llr μ ν) μ)
  证明: by
  rw [klDiv_def]
  exact if_pos ⟨h1, h2⟩

@[simp]

Depends on / 依赖: if_pos, klDiv_def
-/
lemma klDiv_of_ac_of_integrable (h1 : μ ≪ ν) (h2 : Integrable (llr μ ν) μ) :
    klDiv μ ν = ENNReal.ofReal (∫ x, llr μ ν x ∂μ + ν.real univ - μ.real univ) := by
  rw [klDiv_def]
  exact if_pos ⟨h1, h2⟩

@[simp]
/--
lemma `klDiv_of_not_ac` / 引理 `klDiv_of_not_ac`

English:
lemma klDiv_of_not_ac
  given: (h : ¬ μ ≪ ν)
  statement: klDiv μ ν = ∞
  proof: by
  rw [klDiv_def]
  exact if_neg (not_and_of_not_left _ h)

@[simp]

中文:
引理 klDiv_of_not_ac
  条件: (h : ¬ μ ≪ ν)
  结论: klDiv μ ν = ∞
  证明: by
  rw [klDiv_def]
  exact if_neg (not_and_of_not_left _ h)

@[simp]

Depends on / 依赖: if_neg, klDiv_def, not_and_of_not_left
-/
lemma klDiv_of_not_ac (h : ¬ μ ≪ ν) : klDiv μ ν = ∞ := by
  rw [klDiv_def]
  exact if_neg (not_and_of_not_left _ h)

@[simp]
/--
lemma `klDiv_of_not_integrable` / 引理 `klDiv_of_not_integrable`

English:
lemma klDiv_of_not_integrable
  given: (h : ¬ Integrable (llr μ ν) μ)
  statement: klDiv μ ν = ∞
  proof: by
  rw [klDiv_def]
  exact if_neg (not_and_of_not_right _ h)

@[simp]

中文:
引理 klDiv_of_not_integrable
  条件: (h : ¬ 可积 (llr μ ν) μ)
  结论: klDiv μ ν = ∞
  证明: by
  rw [klDiv_def]
  exact if_neg (not_and_of_not_right _ h)

@[simp]

Depends on / 依赖: if_neg, klDiv_def, not_and_of_not_right
-/
lemma klDiv_of_not_integrable (h : ¬ Integrable (llr μ ν) μ) : klDiv μ ν = ∞ := by
  rw [klDiv_def]
  exact if_neg (not_and_of_not_right _ h)

@[simp]
/--
lemma `klDiv_self` / 引理 `klDiv_self`

English:
lemma klDiv_self
  given: (μ : Measure α) [SigmaFinite μ]
  statement: klDiv μ μ = 0
  proof: by
  have h := llr_self μ
  rw [klDiv_def]; rw [if_pos]
  · simp [integral_congr_ae h]
  · rw [integrable_congr h]
    exact ⟨Measure.AbsolutelyContinuous.rfl, integrable_zero _ _ μ⟩

@[simp]

中文:
引理 klDiv_self
  条件: (μ : 测度 α) [σ有限 μ]
  结论: klDiv μ μ = 0
  证明: by
  have h := llr_self μ
  rw [klDiv_def]; rw [if_pos]
  · simp [integral_congr_ae h]
  · rw [integrable_congr h]
    exact ⟨Measure.AbsolutelyContinuous.rfl, integrable_zero _ _ μ⟩

@[simp]

Depends on / 依赖: AbsolutelyContinuous, Measure, Measure.AbsolutelyContinuous.rfl, if_pos, integrable_congr, integrable_zero, integral_congr_ae, klDiv_def, llr_self
-/
lemma klDiv_self (μ : Measure α) [SigmaFinite μ] : klDiv μ μ = 0 := by
  have h := llr_self μ
  rw [klDiv_def]; rw [if_pos]
  · simp [integral_congr_ae h]
  · rw [integrable_congr h]
    exact ⟨Measure.AbsolutelyContinuous.rfl, integrable_zero _ _ μ⟩

@[simp]
/--
lemma `klDiv_zero_left` / 引理 `klDiv_zero_left`

English:
lemma klDiv_zero_left
  given: [IsFiniteMeasure ν]
  statement: klDiv 0 ν = ν univ
  proof: by
  convert! klDiv_of_ac_of_integrable (Measure.AbsolutelyContinuous.zero _) integrable_zero_measure
  simp

@[simp]

中文:
引理 klDiv_zero_left
  条件: [是有限测度 ν]
  结论: klDiv 0 ν = ν univ
  证明: by
  convert! klDiv_of_ac_of_integrable (Measure.AbsolutelyContinuous.zero _) integrable_zero_measure
  simp

@[simp]

Depends on / 依赖: AbsolutelyContinuous, Measure, Measure.AbsolutelyContinuous.zero, convert, integrable_zero_measure, klDiv_of_ac_of_integrable
-/
lemma klDiv_zero_left [IsFiniteMeasure ν] : klDiv 0 ν = ν univ := by
  convert! klDiv_of_ac_of_integrable (Measure.AbsolutelyContinuous.zero _) integrable_zero_measure
  simp

@[simp]
/--
lemma `klDiv_zero_right` / 引理 `klDiv_zero_right`

English:
lemma klDiv_zero_right
  given: [NeZero μ]
  statement: klDiv μ 0 = ∞
  proof: klDiv_of_not_ac (Measure.absolutelyContinuous_zero_iff.mp.mt (NeZero.ne _))

中文:
引理 klDiv_zero_right
  条件: [NeZero μ]
  结论: klDiv μ 0 = ∞
  证明: klDiv_of_not_ac (Measure.absolutelyContinuous_zero_iff.mp.mt (NeZero.ne _))

Depends on / 依赖: Measure, Measure.absolutelyContinuous_zero_iff.mp.mt, NeZero, NeZero.ne, absolutelyContinuous_zero_iff, klDiv_of_not_ac
-/
lemma klDiv_zero_right [NeZero μ] : klDiv μ 0 = ∞ :=
  klDiv_of_not_ac (Measure.absolutelyContinuous_zero_iff.mp.mt (NeZero.ne _))

/--
lemma `klDiv_eq_top_iff` / 引理 `klDiv_eq_top_iff`

English:
lemma klDiv_eq_top_iff
  statement: klDiv μ ν = ∞ ↔ μ ≪ ν -> ¬ Integrable (llr μ ν) μ
  proof: by
  constructor <;> intro h
  · contrapose! h
    simp [klDiv_of_ac_of_integrable h.1 h.2]
  · rcases or_not_of_imp h with (h | h) <;> simp [h]

中文:
引理 klDiv_eq_top_iff
  结论: klDiv μ ν = ∞ ↔ μ ≪ ν -> ¬ 可积 (llr μ ν) μ
  证明: by
  constructor <;> intro h
  · contrapose! h
    simp [klDiv_of_ac_of_integrable h.1 h.2]
  · rcases or_not_of_imp h with (h | h) <;> simp [h]

Depends on / 依赖: contrapose, klDiv_of_ac_of_integrable, or_not_of_imp
-/
lemma klDiv_eq_top_iff : klDiv μ ν = ∞ ↔ μ ≪ ν -> ¬ Integrable (llr μ ν) μ := by
  constructor <;> intro h
  · contrapose! h
    simp [klDiv_of_ac_of_integrable h.1 h.2]
  · rcases or_not_of_imp h with (h | h) <;> simp [h]

/--
lemma `klDiv_ne_top_iff` / 引理 `klDiv_ne_top_iff`

English:
lemma klDiv_ne_top_iff
  statement: klDiv μ ν != ∞ ↔ μ ≪ ν ∧ Integrable (llr μ ν) μ
  proof: by
  simp [ne_eq, klDiv_eq_top_iff]

中文:
引理 klDiv_ne_top_iff
  结论: klDiv μ ν != ∞ ↔ μ ≪ ν ∧ 可积 (llr μ ν) μ
  证明: by
  simp [ne_eq, klDiv_eq_top_iff]

Depends on / 依赖: klDiv_eq_top_iff, ne_eq
-/
lemma klDiv_ne_top_iff : klDiv μ ν != ∞ ↔ μ ≪ ν ∧ Integrable (llr μ ν) μ := by
  simp [ne_eq, klDiv_eq_top_iff]

/--
lemma `klDiv_ne_top` / 引理 `klDiv_ne_top`

English:
lemma klDiv_ne_top
  given: (hμν : μ ≪ ν) (h_int : Integrable (llr μ ν) μ)
  statement: klDiv μ ν != ∞
  proof: klDiv_ne_top_iff.mpr ⟨hμν, h_int⟩

中文:
引理 klDiv_ne_top
  条件: (hμν : μ ≪ ν) (h_int : 可积 (llr μ ν) μ)
  结论: klDiv μ ν != ∞
  证明: klDiv_ne_top_iff.mpr ⟨hμν, h_int⟩

Depends on / 依赖: h_int, klDiv_ne_top_iff, klDiv_ne_top_iff.mpr
-/
lemma klDiv_ne_top (hμν : μ ≪ ν) (h_int : Integrable (llr μ ν) μ) : klDiv μ ν != ∞ :=
  klDiv_ne_top_iff.mpr ⟨hμν, h_int⟩

section AlternativeFormulas

variable [IsFiniteMeasure μ] [IsFiniteMeasure ν]

open scoped Classical in
/--
lemma `klDiv_eq_integral_klFun` / 引理 `klDiv_eq_integral_klFun`

English:
lemma klDiv_eq_integral_klFun
  proof: by
  rw [klDiv_def]
  exact if_ctx_congr Iff.rfl (fun h => by rw [integral_klFun_rnDeriv h.1 h.2]) fun _ => rfl

中文:
引理 klDiv_eq_integral_klFun
  证明: by
  rw [klDiv_def]
  exact if_ctx_congr Iff.rfl (fun h => by rw [integral_klFun_rnDeriv h.1 h.2]) fun _ => rfl

Depends on / 依赖: Iff.rfl, if_ctx_congr, integral_klFun_rnDeriv, klDiv_def
-/
lemma klDiv_eq_integral_klFun :
    klDiv μ ν = if μ ≪ ν ∧ Integrable (llr μ ν) μ
      then ENNReal.ofReal (∫ x, klFun (μ.rnDeriv ν x).toReal ∂ν)
      else ∞ := by
  rw [klDiv_def]
  exact if_ctx_congr Iff.rfl (fun h => by rw [integral_klFun_rnDeriv h.1 h.2]) fun _ => rfl

open scoped Classical in
/--
lemma `klDiv_eq_lintegral_klFun` / 引理 `klDiv_eq_lintegral_klFun`

English:
lemma klDiv_eq_lintegral_klFun
  proof: by
  rw [klDiv_eq_integral_klFun]
  by_cases hμν : μ ≪ ν
  swap; · simp [hμν]
  have h_int_iff := lintegral_ofReal_ne_top_iff_integrable
    (f := fun x => klFun (μ.rnDeriv ν x).toReal) (μ := ν) ?_ ?_
  rotate_left
  · exact Measurable.aestronglyMeasurable (by fun_prop)
  · exact ae_of_all _ fun _ => klFun_nonneg ENNReal.toReal_nonneg
  by_cases h_int : Integrable (llr μ ν) μ
  · simp only [hμν, h_int, and_self, ↓reduceIte]
    rw [ofReal_integral_eq_lintegral_ofReal]
    · rwa [integrable_klFun_rnDeriv_iff hμν]
    · exact ae_of_all _ fun _ => klFun_nonneg ENNReal.toReal_nonneg
  · rw [← not_iff_not, ne_eq, Decidable.not_not] at h_int_iff
    symm
    simp [hμν, h_int, h_int_iff, integrable_klFun_rnDeriv_iff hμν]

中文:
引理 klDiv_eq_lintegral_klFun
  证明: by
  rw [klDiv_eq_integral_klFun]
  by_cases hμν : μ ≪ ν
  swap; · simp [hμν]
  have h_int_iff := lintegral_ofReal_ne_top_iff_integrable
    (f := fun x => klFun (μ.rnDeriv ν x).toReal) (μ := ν) ?_ ?_
  rotate_left
  · exact Measurable.aestronglyMeasurable (by fun_prop)
  · exact ae_of_all _ fun _ => klFun_nonneg ENNReal.toReal_nonneg
  by_cases h_int : Integrable (llr μ ν) μ
  · simp only [hμν, h_int, and_self, ↓reduceIte]
    rw [ofReal_integral_eq_lintegral_ofReal]
    · rwa [integrable_klFun_rnDeriv_iff hμν]
    · exact ae_of_all _ fun _ => klFun_nonneg ENNReal.toReal_nonneg
  · rw [← not_iff_not, ne_eq, Decidable.not_not] at h_int_iff
    symm
    simp [hμν, h_int, h_int_iff, integrable_klFun_rnDeriv_iff hμν]

Depends on / 依赖: ENNReal, ENNReal.toReal_nonneg, Integrable, Measurable, Measurable.aestronglyMeasurable, ae_o, ae_of_all, aestronglyMeasurable, and_self, fun_prop, h_int, h_int_iff, integrable_klFun_rnDeriv_iff, klDiv_eq_integral_klFun, klFun_nonneg, lintegral_ofReal_ne_top_iff_integrable, ofReal_integral_eq_lintegral_ofReal, reduceIte, rnDeriv, rotate_left
-/
lemma klDiv_eq_lintegral_klFun :
    klDiv μ ν = if μ ≪ ν then ∫⁻ x, ENNReal.ofReal (klFun (μ.rnDeriv ν x).toReal) ∂ν else ∞ := by
  rw [klDiv_eq_integral_klFun]
  by_cases hμν : μ ≪ ν
  swap; · simp [hμν]
  have h_int_iff := lintegral_ofReal_ne_top_iff_integrable
    (f := fun x => klFun (μ.rnDeriv ν x).toReal) (μ := ν) ?_ ?_
  rotate_left
  · exact Measurable.aestronglyMeasurable (by fun_prop)
  · exact ae_of_all _ fun _ => klFun_nonneg ENNReal.toReal_nonneg
  by_cases h_int : Integrable (llr μ ν) μ
  · simp only [hμν, h_int, and_self, ↓reduceIte]
    rw [ofReal_integral_eq_lintegral_ofReal]
    · rwa [integrable_klFun_rnDeriv_iff hμν]
    · exact ae_of_all _ fun _ => klFun_nonneg ENNReal.toReal_nonneg
  · rw [← not_iff_not, ne_eq, Decidable.not_not] at h_int_iff
    symm
    simp [hμν, h_int, h_int_iff, integrable_klFun_rnDeriv_iff hμν]

/--
lemma `klDiv_eq_lintegral_klFun_of_ac` / 引理 `klDiv_eq_lintegral_klFun_of_ac`

English:
lemma klDiv_eq_lintegral_klFun_of_ac
  given: (h_ac : μ ≪ ν)
  proof: by
  simp [klDiv_eq_lintegral_klFun, h_ac]

中文:
引理 klDiv_eq_lintegral_klFun_of_ac
  条件: (h_ac : μ ≪ ν)
  证明: by
  simp [klDiv_eq_lintegral_klFun, h_ac]

Depends on / 依赖: h_ac, klDiv_eq_lintegral_klFun
-/
lemma klDiv_eq_lintegral_klFun_of_ac (h_ac : μ ≪ ν) :
    klDiv μ ν = ∫⁻ x, ENNReal.ofReal (klFun (μ.rnDeriv ν x).toReal) ∂ν := by
  simp [klDiv_eq_lintegral_klFun, h_ac]

end AlternativeFormulas

section Real

variable [IsFiniteMeasure μ] [IsFiniteMeasure ν]

/--
lemma `integral_llr_add_sub_measure_univ_nonneg` / 引理 `integral_llr_add_sub_measure_univ_nonneg`

English:
lemma integral_llr_add_sub_measure_univ_nonneg
  given: (hμν : μ ≪ ν) (h_int : Integrable (llr μ ν) μ)
  proof: by
  rw [← integral_klFun_rnDeriv hμν h_int]
  exact integral_nonneg fun x => klFun_nonneg ENNReal.toReal_nonneg

中文:
引理 integral_llr_add_sub_measure_univ_nonneg
  条件: (hμν : μ ≪ ν) (h_int : 可积 (llr μ ν) μ)
  证明: by
  rw [← integral_klFun_rnDeriv hμν h_int]
  exact integral_nonneg fun x => klFun_nonneg ENNReal.toReal_nonneg

Depends on / 依赖: ENNReal, ENNReal.toReal_nonneg, h_int, integral_klFun_rnDeriv, integral_nonneg, klFun_nonneg, toReal_nonneg
-/
lemma integral_llr_add_sub_measure_univ_nonneg (hμν : μ ≪ ν) (h_int : Integrable (llr μ ν) μ) :
    0 <= ∫ x, llr μ ν x ∂μ + ν.real univ - μ.real univ := by
  rw [← integral_klFun_rnDeriv hμν h_int]
  exact integral_nonneg fun x => klFun_nonneg ENNReal.toReal_nonneg

/--
lemma `toReal_klDiv` / 引理 `toReal_klDiv`

English:
lemma toReal_klDiv
  given: (h : μ ≪ ν) (h_int : Integrable (llr μ ν) μ)
  proof: by
  rw [klDiv_of_ac_of_integrable h h_int]; rw [ENNReal.toReal_ofReal]
  exact integral_llr_add_sub_measure_univ_nonneg h h_int

中文:
引理 to实数_klDiv
  条件: (h : μ ≪ ν) (h_int : 可积 (llr μ ν) μ)
  证明: by
  rw [klDiv_of_ac_of_integrable h h_int]; rw [ENNReal.toReal_ofReal]
  exact integral_llr_add_sub_measure_univ_nonneg h h_int

Depends on / 依赖: ENNReal, ENNReal.toReal_ofReal, h_int, integral_llr_add_sub_measure_univ_nonneg, klDiv_of_ac_of_integrable, toReal_ofReal
-/
lemma toReal_klDiv (h : μ ≪ ν) (h_int : Integrable (llr μ ν) μ) :
    (klDiv μ ν).toReal = ∫ a, llr μ ν a ∂μ + ν.real univ - μ.real univ := by
  rw [klDiv_of_ac_of_integrable h h_int]; rw [ENNReal.toReal_ofReal]
  exact integral_llr_add_sub_measure_univ_nonneg h h_int

/--
lemma `toReal_klDiv_of_measure_eq` / 引理 `toReal_klDiv_of_measure_eq`

English:
lemma toReal_klDiv_of_measure_eq
  given: (h : μ ≪ ν) (h_eq : μ univ = ν univ)
  proof: by
  by_cases h_int : Integrable (llr μ ν) μ
  · simp [toReal_klDiv h h_int, h_eq, measureReal_def]
  · rw [klDiv_of_not_integrable h_int, integral_undef h_int, ENNReal.toReal_top]

中文:
引理 to实数_klDiv_of_measure_eq
  条件: (h : μ ≪ ν) (h_eq : μ univ = ν univ)
  证明: by
  by_cases h_int : Integrable (llr μ ν) μ
  · simp [toReal_klDiv h h_int, h_eq, measureReal_def]
  · rw [klDiv_of_not_integrable h_int, integral_undef h_int, ENNReal.toReal_top]

Depends on / 依赖: ENNReal, ENNReal.toReal_top, Integrable, h_eq, h_int, integral_undef, klDiv_of_not_integrable, measureReal_def, toReal_klDiv, toReal_top
-/
lemma toReal_klDiv_of_measure_eq (h : μ ≪ ν) (h_eq : μ univ = ν univ) :
    (klDiv μ ν).toReal = ∫ a, llr μ ν a ∂μ := by
  by_cases h_int : Integrable (llr μ ν) μ
  · simp [toReal_klDiv h h_int, h_eq, measureReal_def]
  · rw [klDiv_of_not_integrable h_int, integral_undef h_int, ENNReal.toReal_top]

/--
lemma `toReal_klDiv_eq_integral_klFun` / 引理 `toReal_klDiv_eq_integral_klFun`

English:
lemma toReal_klDiv_eq_integral_klFun
  given: (h : μ ≪ ν)
  proof: by
  by_cases h_int : Integrable (llr μ ν) μ
  · rw [klDiv_eq_integral_klFun, if_pos ⟨h, h_int⟩, ENNReal.toReal_ofReal]
    exact integral_nonneg fun _ => klFun_nonneg ENNReal.toReal_nonneg
  · rw [integral_undef]
    · rw [klDiv_of_not_integrable h_int, ENNReal.toReal_top]
    · rwa [integrable_klFun_rnDeriv_iff h]

中文:
引理 to实数_klDiv_eq_integral_klFun
  条件: (h : μ ≪ ν)
  证明: by
  by_cases h_int : Integrable (llr μ ν) μ
  · rw [klDiv_eq_integral_klFun, if_pos ⟨h, h_int⟩, ENNReal.toReal_ofReal]
    exact integral_nonneg fun _ => klFun_nonneg ENNReal.toReal_nonneg
  · rw [integral_undef]
    · rw [klDiv_of_not_integrable h_int, ENNReal.toReal_top]
    · rwa [integrable_klFun_rnDeriv_iff h]

Depends on / 依赖: ENNReal, ENNReal.toReal_nonneg, ENNReal.toReal_ofReal, ENNReal.toReal_top, Integrable, h_int, if_pos, integrable_klFun_rnDeriv_iff, integral_nonneg, integral_undef, klDiv_eq_integral_klFun, klDiv_of_not_integrable, klFun_nonneg, toReal_nonneg, toReal_ofReal, toReal_top
-/
lemma toReal_klDiv_eq_integral_klFun (h : μ ≪ ν) :
    (klDiv μ ν).toReal = ∫ x, klFun (μ.rnDeriv ν x).toReal ∂ν := by
  by_cases h_int : Integrable (llr μ ν) μ
  · rw [klDiv_eq_integral_klFun, if_pos ⟨h, h_int⟩, ENNReal.toReal_ofReal]
    exact integral_nonneg fun _ => klFun_nonneg ENNReal.toReal_nonneg
  · rw [integral_undef]
    · rw [klDiv_of_not_integrable h_int, ENNReal.toReal_top]
    · rwa [integrable_klFun_rnDeriv_iff h]

/--
lemma `toReal_klDiv_smul_left` / 引理 `toReal_klDiv_smul_left`

English:
lemma toReal_klDiv_smul_left
  given: (hμν : μ ≪ ν) (h_int : Integrable (llr μ ν) μ) (c : Real>=0)
  proof: by
  by_cases hc : c = 0
  · simp [hc, measureReal_def]
  have h_llr := llr_smul_nnreal_left hμν c (by simpa)
  rw [toReal_klDiv hμν h_int]; rw [toReal_klDiv (hμν.smul_left c)]
  swap
  · refine Integrable.smul_measure_nnreal ?_
    rw [integrable_congr h_llr]
    fun_prop
  simp only [integral_smul_nnreal_measure, measureReal_nnreal_smul_apply]
  rw [integral_congr_ae h_llr]; rw [integral_add h_int (integrable_const _)]
  have h_smul (a : Real) : c • a = c * a := rfl
  simp [h_smul]
  ring

中文:
引理 to实数_klDiv_smul_left
  条件: (hμν : μ ≪ ν) (h_int : 可积 (llr μ ν) μ) (c : 实数>=0)
  证明: by
  by_cases hc : c = 0
  · simp [hc, measureReal_def]
  have h_llr := llr_smul_nnreal_left hμν c (by simpa)
  rw [toReal_klDiv hμν h_int]; rw [toReal_klDiv (hμν.smul_left c)]
  swap
  · refine Integrable.smul_measure_nnreal ?_
    rw [integrable_congr h_llr]
    fun_prop
  simp only [integral_smul_nnreal_measure, measureReal_nnreal_smul_apply]
  rw [integral_congr_ae h_llr]; rw [integral_add h_int (integrable_const _)]
  have h_smul (a : Real) : c • a = c * a := rfl
  simp [h_smul]
  ring

Depends on / 依赖: Integrable, Integrable.smul_measure_nnreal, fun_prop, h_int, h_llr, h_smul, integrable_congr, integrable_const, integral_add, integral_congr_ae, integral_smul_nnreal_measure, llr_smul_nnreal_left, measureReal_def, measureReal_nnreal_smul_apply, smul_left, smul_measure_nnreal, toReal_klDiv
-/
lemma toReal_klDiv_smul_left (hμν : μ ≪ ν) (h_int : Integrable (llr μ ν) μ) (c : Real>=0) :
    (klDiv (c • μ) ν).toReal =
      c * (klDiv μ ν).toReal + (1 - c) * ν.real univ + c * log c * μ.real univ := by
  by_cases hc : c = 0
  · simp [hc, measureReal_def]
  have h_llr := llr_smul_nnreal_left hμν c (by simpa)
  rw [toReal_klDiv hμν h_int]; rw [toReal_klDiv (hμν.smul_left c)]
  swap
  · refine Integrable.smul_measure_nnreal ?_
    rw [integrable_congr h_llr]
    fun_prop
  simp only [integral_smul_nnreal_measure, measureReal_nnreal_smul_apply]
  rw [integral_congr_ae h_llr]; rw [integral_add h_int (integrable_const _)]
  have h_smul (a : Real) : c • a = c * a := rfl
  simp [h_smul]
  ring

/--
lemma `toReal_klDiv_smul_right_eq_smul_left` / 引理 `toReal_klDiv_smul_right_eq_smul_left`

English:
lemma toReal_klDiv_smul_right_eq_smul_left
  statement: (hμν : μ ≪ ν) (h_int : Integrable (llr μ ν) μ)
  proof: by
  by_cases hc : c = 0
  · simp only [hc, zero_smul, NNReal.coe_zero, inv_zero, klDiv_zero_left, zero_mul]
    rcases eq_zero_or_neZero μ with rfl | hμ <;> simp
  have h_llr_left := llr_smul_nnreal_left hμν c⁻¹ (by simpa)
  have h_llr_right := llr_smul_nnreal_right hμν c (by simpa)
  rw [toReal_klDiv]; rw [toReal_klDiv]
  rotate_left
  · exact hμν.smul_left _
  · refine Integrable.smul_measure_nnreal ?_
    rw [integrable_congr h_llr_left]
    fun_prop
  · exact hμν.smul_right (by simpa)
  · rw [integrable_congr h_llr_right]
    fun_prop
  have h_smul (c : Real>=0) (a : Real) : c • a = c * a := rfl
  simp only [measureReal_nnreal_smul_apply, integral_smul_nnreal_measure, h_smul, NNReal.coe_inv]
  have h_llr_smul_inv := llr_smul_inv_left_eq_smul_right hμν c (by simpa) (by simp)
  simp only [← ENNReal.coe_inv hc, Measure.coe_nnreal_smul] at h_llr_smul_inv
  rw [integral_congr_ae h_llr_smul_inv]; rw [mul_sub]; rw [mul_add]; rw [mul_inv_cancel_left₀ (by simpa)]; rw [mul_inv_cancel_left₀ (by simpa)]

中文:
引理 to实数_klDiv_smul_right_eq_smul_left
  结论: (hμν : μ ≪ ν) (h_int : 可积 (llr μ ν) μ)
  证明: by
  by_cases hc : c = 0
  · simp only [hc, zero_smul, NNReal.coe_zero, inv_zero, klDiv_zero_left, zero_mul]
    rcases eq_zero_or_neZero μ with rfl | hμ <;> simp
  have h_llr_left := llr_smul_nnreal_left hμν c⁻¹ (by simpa)
  have h_llr_right := llr_smul_nnreal_right hμν c (by simpa)
  rw [toReal_klDiv]; rw [toReal_klDiv]
  rotate_left
  · exact hμν.smul_left _
  · refine Integrable.smul_measure_nnreal ?_
    rw [integrable_congr h_llr_left]
    fun_prop
  · exact hμν.smul_right (by simpa)
  · rw [integrable_congr h_llr_right]
    fun_prop
  have h_smul (c : Real>=0) (a : Real) : c • a = c * a := rfl
  simp only [measureReal_nnreal_smul_apply, integral_smul_nnreal_measure, h_smul, NNReal.coe_inv]
  have h_llr_smul_inv := llr_smul_inv_left_eq_smul_right hμν c (by simpa) (by simp)
  simp only [← ENNReal.coe_inv hc, Measure.coe_nnreal_smul] at h_llr_smul_inv
  rw [integral_congr_ae h_llr_smul_inv]; rw [mul_sub]; rw [mul_add]; rw [mul_inv_cancel_left₀ (by simpa)]; rw [mul_inv_cancel_left₀ (by simpa)]

Depends on / 依赖: Integrable, Integrable.smul_measure_nnreal, NNReal, NNReal.coe_zero, coe_zero, eq_zero_or_neZero, fun_prop, h_llr_left, h_llr_right, integrable_congr, inv_zero, klDiv_zero_left, llr_smul_nnreal_left, llr_smul_nnreal_right, rotate_left, smul_left, smul_measure_nnreal, smul_right, toReal_klDiv, zero_mul
-/
lemma toReal_klDiv_smul_right_eq_smul_left (hμν : μ ≪ ν) (h_int : Integrable (llr μ ν) μ)
    (c : Real>=0) :
    (klDiv μ (c • ν)).toReal = c * (klDiv (c⁻¹ • μ) ν).toReal := by
  by_cases hc : c = 0
  · simp only [hc, zero_smul, NNReal.coe_zero, inv_zero, klDiv_zero_left, zero_mul]
    rcases eq_zero_or_neZero μ with rfl | hμ <;> simp
  have h_llr_left := llr_smul_nnreal_left hμν c⁻¹ (by simpa)
  have h_llr_right := llr_smul_nnreal_right hμν c (by simpa)
  rw [toReal_klDiv]; rw [toReal_klDiv]
  rotate_left
  · exact hμν.smul_left _
  · refine Integrable.smul_measure_nnreal ?_
    rw [integrable_congr h_llr_left]
    fun_prop
  · exact hμν.smul_right (by simpa)
  · rw [integrable_congr h_llr_right]
    fun_prop
  have h_smul (c : Real>=0) (a : Real) : c • a = c * a := rfl
  simp only [measureReal_nnreal_smul_apply, integral_smul_nnreal_measure, h_smul, NNReal.coe_inv]
  have h_llr_smul_inv := llr_smul_inv_left_eq_smul_right hμν c (by simpa) (by simp)
  simp only [← ENNReal.coe_inv hc, Measure.coe_nnreal_smul] at h_llr_smul_inv
  rw [integral_congr_ae h_llr_smul_inv]; rw [mul_sub]; rw [mul_add]; rw [mul_inv_cancel_left₀ (by simpa)]; rw [mul_inv_cancel_left₀ (by simpa)]

/--
lemma `toReal_klDiv_smul_right` / 引理 `toReal_klDiv_smul_right`

English:
lemma toReal_klDiv_smul_right
  statement: (hμν : μ ≪ ν) (h_int : Integrable (llr μ ν) μ)
  proof: by
  rw [toReal_klDiv_smul_right_eq_smul_left hμν h_int c]; rw [toReal_klDiv_smul_left hμν h_int c⁻¹]
  simp only [NNReal.coe_inv, log_inv, mul_neg, neg_mul, ← sub_eq_add_neg]
  field_simp

中文:
引理 to实数_klDiv_smul_right
  结论: (hμν : μ ≪ ν) (h_int : 可积 (llr μ ν) μ)
  证明: by
  rw [toReal_klDiv_smul_right_eq_smul_left hμν h_int c]; rw [toReal_klDiv_smul_left hμν h_int c⁻¹]
  simp only [NNReal.coe_inv, log_inv, mul_neg, neg_mul, ← sub_eq_add_neg]
  field_simp

Depends on / 依赖: NNReal, NNReal.coe_inv, coe_inv, h_int, log_inv, mul_neg, neg_mul, sub_eq_add_neg, toReal_klDiv_smul_left, toReal_klDiv_smul_right_eq_smul_left
-/
lemma toReal_klDiv_smul_right (hμν : μ ≪ ν) (h_int : Integrable (llr μ ν) μ)
    {c : Real>=0} (hc : c != 0) :
    (klDiv μ (c • ν)).toReal =
      (klDiv μ ν).toReal + (c - 1) * ν.real univ - log c * μ.real univ := by
  rw [toReal_klDiv_smul_right_eq_smul_left hμν h_int c]; rw [toReal_klDiv_smul_left hμν h_int c⁻¹]
  simp only [NNReal.coe_inv, log_inv, mul_neg, neg_mul, ← sub_eq_add_neg]
  field_simp

/--
lemma `toReal_klDiv_smul_same` / 引理 `toReal_klDiv_smul_same`

English:
lemma toReal_klDiv_smul_same
  given: (hμν : μ ≪ ν) (h_int : Integrable (llr μ ν) μ) (c : Real>=0)
  proof: by
  by_cases hc : c = 0
  · simp [hc]
  rw [toReal_klDiv_smul_right_eq_smul_left]; rw [smul_smul]; rw [inv_mul_cancel₀ hc]; rw [one_smul]
  · exact hμν.smul_left c
  · refine Integrable.smul_measure_nnreal ?_
    rw [integrable_congr (llr_smul_nnreal_left hμν c (by simpa))]
    fun_prop

中文:
引理 to实数_klDiv_smul_same
  条件: (hμν : μ ≪ ν) (h_int : 可积 (llr μ ν) μ) (c : 实数>=0)
  证明: by
  by_cases hc : c = 0
  · simp [hc]
  rw [toReal_klDiv_smul_right_eq_smul_left]; rw [smul_smul]; rw [inv_mul_cancel₀ hc]; rw [one_smul]
  · exact hμν.smul_left c
  · refine Integrable.smul_measure_nnreal ?_
    rw [integrable_congr (llr_smul_nnreal_left hμν c (by simpa))]
    fun_prop

Depends on / 依赖: Integrable, Integrable.smul_measure_nnreal, fun_prop, integrable_congr, llr_smul_nnreal_left, one_smul, smul_left, smul_measure_nnreal, smul_smul, toReal_klDiv_smul_right_eq_smul_left
-/
lemma toReal_klDiv_smul_same (hμν : μ ≪ ν) (h_int : Integrable (llr μ ν) μ) (c : Real>=0) :
    (klDiv (c • μ) (c • ν)).toReal = c * (klDiv μ ν).toReal := by
  by_cases hc : c = 0
  · simp [hc]
  rw [toReal_klDiv_smul_right_eq_smul_left]; rw [smul_smul]; rw [inv_mul_cancel₀ hc]; rw [one_smul]
  · exact hμν.smul_left c
  · refine Integrable.smul_measure_nnreal ?_
    rw [integrable_congr (llr_smul_nnreal_left hμν c (by simpa))]
    fun_prop

end Real

/--
lemma `klDiv_smul_right_eq_smul_left` / 引理 `klDiv_smul_right_eq_smul_left`

English:
lemma klDiv_smul_right_eq_smul_left
  given: [IsFiniteMeasure μ] [IsFiniteMeasure ν] {c : Real>=0} (hc : c != 0)
  proof: by
  have hc' : (c : Real>=0∞) != 0 := by simpa
  have hμ_smul : μ = c • (c⁻¹ • μ) := by rw [smul_smul, mul_inv_cancel₀ hc, one_smul]
  have hν_smul : ν = c⁻¹ • (c • ν) := by rw [smul_smul, inv_mul_cancel₀ hc, one_smul]
  by_cases hμν : μ ≪ ν
  swap
  · rw [klDiv_of_not_ac, klDiv_of_not_ac, ENNReal.mul_top hc']
    · refine fun h_contra => hμν ?_
      rw [hμ_smul]
      exact h_contra.smul_left _
    · refine fun h_contra => hμν ?_
      rw [hν_smul]
      exact h_contra.smul_right (by simpa)
  have hμν_right := hμν.smul_right hc'
  simp only [Measure.coe_nnreal_smul] at hμν_right
  by_cases h_int : Integrable (llr μ ν) μ
  swap
  · rw [klDiv_of_not_integrable, klDiv_of_not_integrable, ENNReal.mul_top hc']
    · refine fun h_contra => h_int ?_
      rw [hμ_smul]
      refine Integrable.smul_measure_nnreal ?_
      rw [integrable_congr (llr_smul_nnreal_left (hμν.smul_left _) c hc)]
      fun_prop
    · refine fun h_contra => h_int ?_
      rw [hν_smul]
      have : IsFiniteMeasure ((c : Real>=0∞) • ν) := by
        simp only [Measure.coe_nnreal_smul]
        infer_instance
      have h := llr_smul_nnreal_right (hμν.smul_right hc') c⁻¹ (by simpa)
      simp only [Measure.coe_nnreal_smul, NNReal.coe_inv, log_inv, sub_neg_eq_add] at h
      rw [integrable_congr h]
      fun_prop
  have h_int_left : Integrable (llr (c⁻¹ • μ) ν) (c⁻¹ • μ) := by
    refine Integrable.smul_measure_nnreal ?_
    rw [integrable_congr (llr_smul_nnreal_left hμν c⁻¹ (by simpa))]
    fun_prop
  have h_int_right : Integrable (llr μ (c • ν)) μ := by
    rw [integrable_congr (llr_smul_nnreal_right hμν c (by simpa))]
    fun_prop
  rw [← ENNReal.ofReal_toReal (klDiv_ne_top hμν_right h_int_right)]; rw [toReal_klDiv_smul_right_eq_smul_left hμν h_int c]
  simp only [NNReal.zero_le_coe, ENNReal.ofReal_mul, ENNReal.ofReal_coe_nnreal]
  rw [ENNReal.ofReal_toReal]
  exact klDiv_ne_top (hμν.smul_left _) h_int_left

中文:
引理 klDiv_smul_right_eq_smul_left
  条件: [是有限测度 μ] [是有限测度 ν] {c : 实数>=0} (hc : c != 0)
  证明: by
  have hc' : (c : Real>=0∞) != 0 := by simpa
  have hμ_smul : μ = c • (c⁻¹ • μ) := by rw [smul_smul, mul_inv_cancel₀ hc, one_smul]
  have hν_smul : ν = c⁻¹ • (c • ν) := by rw [smul_smul, inv_mul_cancel₀ hc, one_smul]
  by_cases hμν : μ ≪ ν
  swap
  · rw [klDiv_of_not_ac, klDiv_of_not_ac, ENNReal.mul_top hc']
    · refine fun h_contra => hμν ?_
      rw [hμ_smul]
      exact h_contra.smul_left _
    · refine fun h_contra => hμν ?_
      rw [hν_smul]
      exact h_contra.smul_right (by simpa)
  have hμν_right := hμν.smul_right hc'
  simp only [Measure.coe_nnreal_smul] at hμν_right
  by_cases h_int : Integrable (llr μ ν) μ
  swap
  · rw [klDiv_of_not_integrable, klDiv_of_not_integrable, ENNReal.mul_top hc']
    · refine fun h_contra => h_int ?_
      rw [hμ_smul]
      refine Integrable.smul_measure_nnreal ?_
      rw [integrable_congr (llr_smul_nnreal_left (hμν.smul_left _) c hc)]
      fun_prop
    · refine fun h_contra => h_int ?_
      rw [hν_smul]
      have : IsFiniteMeasure ((c : Real>=0∞) • ν) := by
        simp only [Measure.coe_nnreal_smul]
        infer_instance
      have h := llr_smul_nnreal_right (hμν.smul_right hc') c⁻¹ (by simpa)
      simp only [Measure.coe_nnreal_smul, NNReal.coe_inv, log_inv, sub_neg_eq_add] at h
      rw [integrable_congr h]
      fun_prop
  have h_int_left : Integrable (llr (c⁻¹ • μ) ν) (c⁻¹ • μ) := by
    refine Integrable.smul_measure_nnreal ?_
    rw [integrable_congr (llr_smul_nnreal_left hμν c⁻¹ (by simpa))]
    fun_prop
  have h_int_right : Integrable (llr μ (c • ν)) μ := by
    rw [integrable_congr (llr_smul_nnreal_right hμν c (by simpa))]
    fun_prop
  rw [← ENNReal.ofReal_toReal (klDiv_ne_top hμν_right h_int_right)]; rw [toReal_klDiv_smul_right_eq_smul_left hμν h_int c]
  simp only [NNReal.zero_le_coe, ENNReal.ofReal_mul, ENNReal.ofReal_coe_nnreal]
  rw [ENNReal.ofReal_toReal]
  exact klDiv_ne_top (hμν.smul_left _) h_int_left

Depends on / 依赖: ENNReal, ENNReal.mul_top, h_contra, h_contra.smul_left, h_contra.smul_right, klDiv_of_not_ac, mul_top, one_smul, smul_left, smul_right, smul_smul
-/
lemma klDiv_smul_right_eq_smul_left [IsFiniteMeasure μ] [IsFiniteMeasure ν] {c : Real>=0} (hc : c != 0) :
    klDiv μ (c • ν) = c * klDiv (c⁻¹ • μ) ν := by
  have hc' : (c : Real>=0∞) != 0 := by simpa
  have hμ_smul : μ = c • (c⁻¹ • μ) := by rw [smul_smul, mul_inv_cancel₀ hc, one_smul]
  have hν_smul : ν = c⁻¹ • (c • ν) := by rw [smul_smul, inv_mul_cancel₀ hc, one_smul]
  by_cases hμν : μ ≪ ν
  swap
  · rw [klDiv_of_not_ac, klDiv_of_not_ac, ENNReal.mul_top hc']
    · refine fun h_contra => hμν ?_
      rw [hμ_smul]
      exact h_contra.smul_left _
    · refine fun h_contra => hμν ?_
      rw [hν_smul]
      exact h_contra.smul_right (by simpa)
  have hμν_right := hμν.smul_right hc'
  simp only [Measure.coe_nnreal_smul] at hμν_right
  by_cases h_int : Integrable (llr μ ν) μ
  swap
  · rw [klDiv_of_not_integrable, klDiv_of_not_integrable, ENNReal.mul_top hc']
    · refine fun h_contra => h_int ?_
      rw [hμ_smul]
      refine Integrable.smul_measure_nnreal ?_
      rw [integrable_congr (llr_smul_nnreal_left (hμν.smul_left _) c hc)]
      fun_prop
    · refine fun h_contra => h_int ?_
      rw [hν_smul]
      have : IsFiniteMeasure ((c : Real>=0∞) • ν) := by
        simp only [Measure.coe_nnreal_smul]
        infer_instance
      have h := llr_smul_nnreal_right (hμν.smul_right hc') c⁻¹ (by simpa)
      simp only [Measure.coe_nnreal_smul, NNReal.coe_inv, log_inv, sub_neg_eq_add] at h
      rw [integrable_congr h]
      fun_prop
  have h_int_left : Integrable (llr (c⁻¹ • μ) ν) (c⁻¹ • μ) := by
    refine Integrable.smul_measure_nnreal ?_
    rw [integrable_congr (llr_smul_nnreal_left hμν c⁻¹ (by simpa))]
    fun_prop
  have h_int_right : Integrable (llr μ (c • ν)) μ := by
    rw [integrable_congr (llr_smul_nnreal_right hμν c (by simpa))]
    fun_prop
  rw [← ENNReal.ofReal_toReal (klDiv_ne_top hμν_right h_int_right)]; rw [toReal_klDiv_smul_right_eq_smul_left hμν h_int c]
  simp only [NNReal.zero_le_coe, ENNReal.ofReal_mul, ENNReal.ofReal_coe_nnreal]
  rw [ENNReal.ofReal_toReal]
  exact klDiv_ne_top (hμν.smul_left _) h_int_left

/--
lemma `klDiv_smul_same` / 引理 `klDiv_smul_same`

English:
lemma klDiv_smul_same
  given: [IsFiniteMeasure μ] [IsFiniteMeasure ν] (c : Real>=0)
  proof: by
  by_cases hc : c = 0
  · simp [hc]
  have hc' : (c : Real>=0∞) != 0 := by simpa
  have hμ_smul (μ : Measure α) : μ = c⁻¹ • (c • μ) := by
    rw [smul_smul]; rw [inv_mul_cancel₀ hc]; rw [one_smul]
  by_cases hμν : μ ≪ ν
  swap
  · rw [klDiv_of_not_ac hμν, klDiv_of_not_ac, ENNReal.mul_top hc']
    refine fun h_contra => hμν ?_
    rw [hμ_smul μ]; rw [hμ_smul ν]
    exact h_contra.smul _
  by_cases h_int : Integrable (llr μ ν) μ
  swap
  · rw [klDiv_of_not_integrable h_int, klDiv_of_not_integrable, ENNReal.mul_top hc']
    refine fun h_contra => h_int ?_
    rw [hμ_smul μ]; rw [hμ_smul ν]
    refine Integrable.smul_measure_nnreal ?_
    rw [integrable_congr (llr_smul_nnreal_same (hμν.smul c) c⁻¹ (by simpa))]
    fun_prop
  rw [← ENNReal.ofReal_toReal (klDiv_ne_top (hμν.smul c) _)]; rw [← ENNReal.ofReal_toReal (klDiv_ne_top hμν h_int)]
  swap
  · refine Integrable.smul_measure_nnreal ?_
    rw [integrable_congr (llr_smul_nnreal_same hμν c hc)]
    fun_prop
  simp [toReal_klDiv_smul_same hμν h_int]

中文:
引理 klDiv_smul_same
  条件: [是有限测度 μ] [是有限测度 ν] (c : 实数>=0)
  证明: by
  by_cases hc : c = 0
  · simp [hc]
  have hc' : (c : Real>=0∞) != 0 := by simpa
  have hμ_smul (μ : Measure α) : μ = c⁻¹ • (c • μ) := by
    rw [smul_smul]; rw [inv_mul_cancel₀ hc]; rw [one_smul]
  by_cases hμν : μ ≪ ν
  swap
  · rw [klDiv_of_not_ac hμν, klDiv_of_not_ac, ENNReal.mul_top hc']
    refine fun h_contra => hμν ?_
    rw [hμ_smul μ]; rw [hμ_smul ν]
    exact h_contra.smul _
  by_cases h_int : Integrable (llr μ ν) μ
  swap
  · rw [klDiv_of_not_integrable h_int, klDiv_of_not_integrable, ENNReal.mul_top hc']
    refine fun h_contra => h_int ?_
    rw [hμ_smul μ]; rw [hμ_smul ν]
    refine Integrable.smul_measure_nnreal ?_
    rw [integrable_congr (llr_smul_nnreal_same (hμν.smul c) c⁻¹ (by simpa))]
    fun_prop
  rw [← ENNReal.ofReal_toReal (klDiv_ne_top (hμν.smul c) _)]; rw [← ENNReal.ofReal_toReal (klDiv_ne_top hμν h_int)]
  swap
  · refine Integrable.smul_measure_nnreal ?_
    rw [integrable_congr (llr_smul_nnreal_same hμν c hc)]
    fun_prop
  simp [toReal_klDiv_smul_same hμν h_int]

Depends on / 依赖: ENNReal, ENNReal.mul_top, Integrable, Measure, h_contra, h_contra.smul, h_int, klDiv_of_not_ac, klDiv_of_not_integrable, mul_top, one_smul, smul_smul
-/
lemma klDiv_smul_same [IsFiniteMeasure μ] [IsFiniteMeasure ν] (c : Real>=0) :
    klDiv (c • μ) (c • ν) = c * klDiv μ ν := by
  by_cases hc : c = 0
  · simp [hc]
  have hc' : (c : Real>=0∞) != 0 := by simpa
  have hμ_smul (μ : Measure α) : μ = c⁻¹ • (c • μ) := by
    rw [smul_smul]; rw [inv_mul_cancel₀ hc]; rw [one_smul]
  by_cases hμν : μ ≪ ν
  swap
  · rw [klDiv_of_not_ac hμν, klDiv_of_not_ac, ENNReal.mul_top hc']
    refine fun h_contra => hμν ?_
    rw [hμ_smul μ]; rw [hμ_smul ν]
    exact h_contra.smul _
  by_cases h_int : Integrable (llr μ ν) μ
  swap
  · rw [klDiv_of_not_integrable h_int, klDiv_of_not_integrable, ENNReal.mul_top hc']
    refine fun h_contra => h_int ?_
    rw [hμ_smul μ]; rw [hμ_smul ν]
    refine Integrable.smul_measure_nnreal ?_
    rw [integrable_congr (llr_smul_nnreal_same (hμν.smul c) c⁻¹ (by simpa))]
    fun_prop
  rw [← ENNReal.ofReal_toReal (klDiv_ne_top (hμν.smul c) _)]; rw [← ENNReal.ofReal_toReal (klDiv_ne_top hμν h_int)]
  swap
  · refine Integrable.smul_measure_nnreal ?_
    rw [integrable_congr (llr_smul_nnreal_same hμν c hc)]
    fun_prop
  simp [toReal_klDiv_smul_same hμν h_int]

section Inequalities

variable [IsFiniteMeasure μ] [IsFiniteMeasure ν]

/--
lemma `integral_llr_add_mul_log_nonneg` / 引理 `integral_llr_add_mul_log_nonneg`

English:
lemma integral_llr_add_mul_log_nonneg
  given: (hμν : μ ≪ ν) (h_int : Integrable (llr μ ν) μ)
  proof: by
  by_cases hμ : μ = 0
  · simp [hμ]
  by_cases hν : ν = 0
  · refine absurd ?_ hμ
    rw [hν] at hμν
    exact Measure.absolutelyContinuous_zero_iff.mp hμν
  have : NeZero ν := ⟨hν⟩
  let ν' := (ν univ)⁻¹ • ν
  have hμν' : μ ≪ ν' := hμν.trans (Measure.absolutelyContinuous_smul (by simp))
  have h := integral_llr_add_sub_measure_univ_nonneg hμν' ?_
  swap
  · rw [integrable_congr (llr_smul_right hμν (ν univ)⁻¹ (by simp) (by simp [hν]))]
    exact h_int.sub (integrable_const _)
  rw [integral_congr_ae (llr_smul_right hμν (ν univ)⁻¹ (by simp) (by simp [hν])),
    integral_sub h_int (integrable_const _), integral_const, smul_eq_mul] at h
  simpa using! h

中文:
引理 integral_llr_add_mul_log_nonneg
  条件: (hμν : μ ≪ ν) (h_int : 可积 (llr μ ν) μ)
  证明: by
  by_cases hμ : μ = 0
  · simp [hμ]
  by_cases hν : ν = 0
  · refine absurd ?_ hμ
    rw [hν] at hμν
    exact Measure.absolutelyContinuous_zero_iff.mp hμν
  have : NeZero ν := ⟨hν⟩
  let ν' := (ν univ)⁻¹ • ν
  have hμν' : μ ≪ ν' := hμν.trans (Measure.absolutelyContinuous_smul (by simp))
  have h := integral_llr_add_sub_measure_univ_nonneg hμν' ?_
  swap
  · rw [integrable_congr (llr_smul_right hμν (ν univ)⁻¹ (by simp) (by simp [hν]))]
    exact h_int.sub (integrable_const _)
  rw [integral_congr_ae (llr_smul_right hμν (ν univ)⁻¹ (by simp) (by simp [hν])),
    integral_sub h_int (integrable_const _), integral_const, smul_eq_mul] at h
  simpa using! h

Depends on / 依赖: Measure, Measure.absolutelyContinuous_smul, Measure.absolutelyContinuous_zero_iff.mp, NeZero, absolutelyContinuous_smul, absolutelyContinuous_zero_iff, absurd, h_int, h_int.sub, integrable_congr, integrable_const, integral_congr_ae, integral_llr_add_sub_measure_univ_nonneg, llr_smul_right
-/
lemma integral_llr_add_mul_log_nonneg (hμν : μ ≪ ν) (h_int : Integrable (llr μ ν) μ) :
    0 <= ∫ x, llr μ ν x ∂μ + μ.real univ * log (ν.real univ) + 1 - μ.real univ := by
  by_cases hμ : μ = 0
  · simp [hμ]
  by_cases hν : ν = 0
  · refine absurd ?_ hμ
    rw [hν] at hμν
    exact Measure.absolutelyContinuous_zero_iff.mp hμν
  have : NeZero ν := ⟨hν⟩
  let ν' := (ν univ)⁻¹ • ν
  have hμν' : μ ≪ ν' := hμν.trans (Measure.absolutelyContinuous_smul (by simp))
  have h := integral_llr_add_sub_measure_univ_nonneg hμν' ?_
  swap
  · rw [integrable_congr (llr_smul_right hμν (ν univ)⁻¹ (by simp) (by simp [hν]))]
    exact h_int.sub (integrable_const _)
  rw [integral_congr_ae (llr_smul_right hμν (ν univ)⁻¹ (by simp) (by simp [hν])),
    integral_sub h_int (integrable_const _), integral_const, smul_eq_mul] at h
  simpa using! h

/--
lemma `mul_klFun_le_toReal_klDiv` / 引理 `mul_klFun_le_toReal_klDiv`

English:
lemma mul_klFun_le_toReal_klDiv
  given: (hμν : μ ≪ ν) (h_int : Integrable (llr μ ν) μ)
  proof: by
  calc ν.real univ * klFun (μ.real univ / ν.real univ)
  _ <= ∫ x, klFun (μ.rnDeriv ν x).toReal ∂ν := by
    refine mul_le_integral_rnDeriv_of_ac convexOn_klFun continuous_klFun.continuousWithinAt ?_ hμν
    rwa [integrable_klFun_rnDeriv_iff hμν]
  _ = (klDiv μ ν).toReal := by rw [toReal_klDiv_eq_integral_klFun hμν]

中文:
引理 mul_klFun_le_to实数_klDiv
  条件: (hμν : μ ≪ ν) (h_int : 可积 (llr μ ν) μ)
  证明: by
  calc ν.real univ * klFun (μ.real univ / ν.real univ)
  _ <= ∫ x, klFun (μ.rnDeriv ν x).toReal ∂ν := by
    refine mul_le_integral_rnDeriv_of_ac convexOn_klFun continuous_klFun.continuousWithinAt ?_ hμν
    rwa [integrable_klFun_rnDeriv_iff hμν]
  _ = (klDiv μ ν).toReal := by rw [toReal_klDiv_eq_integral_klFun hμν]

Depends on / 依赖: continuousWithinAt, continuous_klFun, continuous_klFun.continuousWithinAt, convexOn_klFun, integrable_klFun_rnDeriv_iff, mul_le_integral_rnDeriv_of_ac, rnDeriv, toReal, toReal_klDiv_eq_integral_klFun
-/
lemma mul_klFun_le_toReal_klDiv (hμν : μ ≪ ν) (h_int : Integrable (llr μ ν) μ) :
    ν.real univ * klFun (μ.real univ / ν.real univ) <= (klDiv μ ν).toReal := by
  calc ν.real univ * klFun (μ.real univ / ν.real univ)
  _ <= ∫ x, klFun (μ.rnDeriv ν x).toReal ∂ν := by
    refine mul_le_integral_rnDeriv_of_ac convexOn_klFun continuous_klFun.continuousWithinAt ?_ hμν
    rwa [integrable_klFun_rnDeriv_iff hμν]
  _ = (klDiv μ ν).toReal := by rw [toReal_klDiv_eq_integral_klFun hμν]

/--
lemma `mul_log_le_toReal_klDiv` / 引理 `mul_log_le_toReal_klDiv`

English:
lemma mul_log_le_toReal_klDiv
  given: (hμν : μ ≪ ν) (h_int : Integrable (llr μ ν) μ)
  proof: by
  by_cases hμ : μ = 0
  · simp [hμ, measureReal_def]
  by_cases hν : ν = 0
  · refine absurd ?_ hμ
    rw [hν] at hμν
    exact Measure.absolutelyContinuous_zero_iff.mp hμν
  refine (le_of_eq ?_).trans (mul_klFun_le_toReal_klDiv hμν h_int)
  have : ν.real univ * (μ.real univ / ν.real univ) = μ.real univ := by
    rw [mul_div_cancel₀]; simp [ENNReal.toReal_eq_zero_iff, hν, measureReal_def]
  rw [klFun]; rw [mul_sub]; rw [mul_add]; rw [mul_one]; rw [← mul_assoc]; rw [this]

中文:
引理 mul_log_le_to实数_klDiv
  条件: (hμν : μ ≪ ν) (h_int : 可积 (llr μ ν) μ)
  证明: by
  by_cases hμ : μ = 0
  · simp [hμ, measureReal_def]
  by_cases hν : ν = 0
  · refine absurd ?_ hμ
    rw [hν] at hμν
    exact Measure.absolutelyContinuous_zero_iff.mp hμν
  refine (le_of_eq ?_).trans (mul_klFun_le_toReal_klDiv hμν h_int)
  have : ν.real univ * (μ.real univ / ν.real univ) = μ.real univ := by
    rw [mul_div_cancel₀]; simp [ENNReal.toReal_eq_zero_iff, hν, measureReal_def]
  rw [klFun]; rw [mul_sub]; rw [mul_add]; rw [mul_one]; rw [← mul_assoc]; rw [this]

Depends on / 依赖: ENNReal, ENNReal.toReal_eq_zero_iff, Measure, Measure.absolutelyContinuous_zero_iff.mp, absolutelyContinuous_zero_iff, absurd, h_int, le_of_eq, measureReal_def, mul_add, mul_assoc, mul_klFun_le_toReal_klDiv, mul_one, mul_sub, toReal_eq_zero_iff
-/
lemma mul_log_le_toReal_klDiv (hμν : μ ≪ ν) (h_int : Integrable (llr μ ν) μ) :
    μ.real univ * log (μ.real univ / ν.real univ) + ν.real univ - μ.real univ
      <= (klDiv μ ν).toReal := by
  by_cases hμ : μ = 0
  · simp [hμ, measureReal_def]
  by_cases hν : ν = 0
  · refine absurd ?_ hμ
    rw [hν] at hμν
    exact Measure.absolutelyContinuous_zero_iff.mp hμν
  refine (le_of_eq ?_).trans (mul_klFun_le_toReal_klDiv hμν h_int)
  have : ν.real univ * (μ.real univ / ν.real univ) = μ.real univ := by
    rw [mul_div_cancel₀]; simp [ENNReal.toReal_eq_zero_iff, hν, measureReal_def]
  rw [klFun]; rw [mul_sub]; rw [mul_add]; rw [mul_one]; rw [← mul_assoc]; rw [this]

/--
lemma `mul_log_le_klDiv` / 引理 `mul_log_le_klDiv`

English:
lemma mul_log_le_klDiv
  given: (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
  proof: by
  by_cases hμν : μ ≪ ν
  swap; · simp [hμν]
  by_cases h_int : Integrable (llr μ ν) μ
  swap; · simp [h_int]
  rw [← ENNReal.ofReal_toReal (a := klDiv μ ν)]
  · exact ENNReal.ofReal_le_ofReal (mul_log_le_toReal_klDiv hμν h_int)
  · rw [klDiv_ne_top_iff]
    exact ⟨hμν, h_int⟩

中文:
引理 mul_log_le_klDiv
  条件: (μ ν : 测度 α) [是有限测度 μ] [是有限测度 ν]
  证明: by
  by_cases hμν : μ ≪ ν
  swap; · simp [hμν]
  by_cases h_int : Integrable (llr μ ν) μ
  swap; · simp [h_int]
  rw [← ENNReal.ofReal_toReal (a := klDiv μ ν)]
  · exact ENNReal.ofReal_le_ofReal (mul_log_le_toReal_klDiv hμν h_int)
  · rw [klDiv_ne_top_iff]
    exact ⟨hμν, h_int⟩

Depends on / 依赖: ENNReal, ENNReal.ofReal_le_ofReal, ENNReal.ofReal_toReal, Integrable, h_int, klDiv_ne_top_iff, mul_log_le_toReal_klDiv, ofReal_le_ofReal, ofReal_toReal
-/
lemma mul_log_le_klDiv (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    ENNReal.ofReal (μ.real univ * log (μ.real univ / ν.real univ)
        + ν.real univ - μ.real univ)
      <= klDiv μ ν := by
  by_cases hμν : μ ≪ ν
  swap; · simp [hμν]
  by_cases h_int : Integrable (llr μ ν) μ
  swap; · simp [h_int]
  rw [← ENNReal.ofReal_toReal (a := klDiv μ ν)]
  · exact ENNReal.ofReal_le_ofReal (mul_log_le_toReal_klDiv hμν h_int)
  · rw [klDiv_ne_top_iff]
    exact ⟨hμν, h_int⟩

end Inequalities

/--
lemma `klDiv_eq_zero_iff` / 引理 `klDiv_eq_zero_iff`

English:
lemma klDiv_eq_zero_iff
  given: [IsFiniteMeasure μ] [IsFiniteMeasure ν]
  proof: by
  refine ⟨fun h => ?_, fun h => h ▸ klDiv_self _⟩
  have h_ne : klDiv μ ν != ⊤ := by simp [h]
  rw [klDiv_ne_top_iff] at h_ne
  rw [klDiv_eq_lintegral_klFun]; rw [if_pos h_ne.1]; rw [lintegral_eq_zero_iff (by fun_prop)] at h
  refine (Measure.rnDeriv_eq_one_iff_eq h_ne.1).mp ?_
  filter_upwards [h] with x hx
  simp only [Pi.zero_apply, ENNReal.ofReal_eq_zero] at hx
  have hx' : klFun (μ.rnDeriv ν x).toReal = 0 := le_antisymm hx (klFun_nonneg ENNReal.toReal_nonneg)
  rwa [klFun_eq_zero_iff ENNReal.toReal_nonneg, ENNReal.toReal_eq_one_iff] at hx'

中文:
引理 klDiv_eq_zero_iff
  条件: [是有限测度 μ] [是有限测度 ν]
  证明: by
  refine ⟨fun h => ?_, fun h => h ▸ klDiv_self _⟩
  have h_ne : klDiv μ ν != ⊤ := by simp [h]
  rw [klDiv_ne_top_iff] at h_ne
  rw [klDiv_eq_lintegral_klFun]; rw [if_pos h_ne.1]; rw [lintegral_eq_zero_iff (by fun_prop)] at h
  refine (Measure.rnDeriv_eq_one_iff_eq h_ne.1).mp ?_
  filter_upwards [h] with x hx
  simp only [Pi.zero_apply, ENNReal.ofReal_eq_zero] at hx
  have hx' : klFun (μ.rnDeriv ν x).toReal = 0 := le_antisymm hx (klFun_nonneg ENNReal.toReal_nonneg)
  rwa [klFun_eq_zero_iff ENNReal.toReal_nonneg, ENNReal.toReal_eq_one_iff] at hx'

Depends on / 依赖: ENNReal, ENNReal.ofReal_eq_zero, ENNReal.toReal_nonneg, Measure, Measure.rnDeriv_eq_one_iff_eq, Pi.zero_apply, filter_upwards, fun_prop, h_ne, if_pos, klDiv_eq_lintegral_klFun, klDiv_ne_top_iff, klDiv_self, klFun_eq_zero_iff, klFun_nonneg, le_antisymm, lintegral_eq_zero_iff, ofReal_eq_zero, rnDeriv, rnDeriv_eq_one_iff_eq
-/
lemma klDiv_eq_zero_iff [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    klDiv μ ν = 0 ↔ μ = ν := by
  refine ⟨fun h => ?_, fun h => h ▸ klDiv_self _⟩
  have h_ne : klDiv μ ν != ⊤ := by simp [h]
  rw [klDiv_ne_top_iff] at h_ne
  rw [klDiv_eq_lintegral_klFun]; rw [if_pos h_ne.1]; rw [lintegral_eq_zero_iff (by fun_prop)] at h
  refine (Measure.rnDeriv_eq_one_iff_eq h_ne.1).mp ?_
  filter_upwards [h] with x hx
  simp only [Pi.zero_apply, ENNReal.ofReal_eq_zero] at hx
  have hx' : klFun (μ.rnDeriv ν x).toReal = 0 := le_antisymm hx (klFun_nonneg ENNReal.toReal_nonneg)
  rwa [klFun_eq_zero_iff ENNReal.toReal_nonneg, ENNReal.toReal_eq_one_iff] at hx'

end InformationTheory
