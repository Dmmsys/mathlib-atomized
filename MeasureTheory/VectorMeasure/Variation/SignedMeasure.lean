/-
Copyright (c) 2025 Oliver Butterley. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley, Yoh Tanimoto
-/
module

public import Mathlib.MeasureTheory.VectorMeasure.Decomposition.Jordan
public import Mathlib.MeasureTheory.VectorMeasure.Variation.Basic
/-!
# Equivalence of variation definitions for signed measures

For a `SignedMeasure`, two definitions of variation are available:
* the supremum-based `VectorMeasure.variation`,
* the Hahn–Jordan-based `SignedMeasure.totalVariation`.

In this file the two notions are shown to coincide.

## Main results

* `MeasureTheory.SignedMeasure.totalVariation_eq_variation`: `μ.totalVariation = μ.variation`.

-/

public section

open scoped ENNReal NNReal

namespace MeasureTheory.SignedMeasure

variable {X : Type*} {mX : MeasurableSpace X} (μ : SignedMeasure X)

/--
theorem `norm_le_totalVariation` / 定理 `norm_le_totalVariation`

English:
theorem norm_le_totalVariation
  given: (s : SignedMeasure X) (i : Set X)
  proof: by
  by_cases hi : MeasurableSet i
  · rw [s.apply_eq_posPart_real_sub_negPart_real hi, totalVariation, measureReal_add_apply]
    grind [measureReal_nonneg, Real.norm_eq_abs]
  · simp [hi]

中文:
定理 norm_le_totalVariation
  条件: (s : 符号测度 X) (i : 集合 X)
  证明: by
  by_cases hi : MeasurableSet i
  · rw [s.apply_eq_posPart_real_sub_negPart_real hi, totalVariation, measureReal_add_apply]
    grind [measureReal_nonneg, Real.norm_eq_abs]
  · simp [hi]

Depends on / 依赖: MeasurableSet, Real.norm_eq_abs, apply_eq_posPart_real_sub_negPart_real, measureReal_add_apply, measureReal_nonneg, norm_eq_abs, s.apply_eq_posPart_real_sub_negPart_real, totalVariation
-/
theorem norm_le_totalVariation (s : SignedMeasure X) (i : Set X) :
    ‖s i‖ <= s.totalVariation.real i := by
  by_cases hi : MeasurableSet i
  · rw [s.apply_eq_posPart_real_sub_negPart_real hi, totalVariation, measureReal_add_apply]
    grind [measureReal_nonneg, Real.norm_eq_abs]
  · simp [hi]

/--
theorem `enorm_le_totalVariation` / 定理 `enorm_le_totalVariation`

English:
theorem enorm_le_totalVariation
  given: (s : SignedMeasure X) (i : Set X)
  proof: calc
  _ = ENNReal.ofReal ‖s i‖ := (ofReal_norm _).symm
  _ <= ENNReal.ofReal (s.totalVariation.real i) :=
    ENNReal.ofReal_le_ofReal (s.norm_le_totalVariation i)
  _ = _ := by rw [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]

中文:
定理 enorm_le_totalVariation
  条件: (s : 符号测度 X) (i : 集合 X)
  证明: calc
  _ = ENNReal.ofReal ‖s i‖ := (ofReal_norm _).symm
  _ <= ENNReal.ofReal (s.totalVariation.real i) :=
    ENNReal.ofReal_le_ofReal (s.norm_le_totalVariation i)
  _ = _ := by rw [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]
-/
theorem enorm_le_totalVariation (s : SignedMeasure X) (i : Set X) :
    ‖s i‖ₑ <= s.totalVariation i := calc
  _ = ENNReal.ofReal ‖s i‖ := (ofReal_norm _).symm
  _ <= ENNReal.ofReal (s.totalVariation.real i) :=
    ENNReal.ofReal_le_ofReal (s.norm_le_totalVariation i)
  _ = _ := by rw [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]

/--
lemma `toMeasureOfZeroLE_apply_eq_enorm` / 引理 `toMeasureOfZeroLE_apply_eq_enorm`

English:
lemma toMeasureOfZeroLE_apply_eq_enorm
  statement: {i j : Set X} (him : MeasurableSet i) (hi : 0 <=[i] μ)
  proof: by
  have : 0 <= μ (i inter j) :=
    μ.nonneg_of_zero_le_restrict (μ.zero_le_restrict_subset ‹_› Set.inter_subset_left ‹_›)
  rw [Real.enorm_of_nonneg this]; rw [μ.toMeasureOfZeroLE_apply hi him hjm]; rw [ENNReal.ofReal_eq_coe_nnreal]

中文:
引理 toMeasureOfZeroLE_apply_eq_enorm
  结论: {i j : 集合 X} (him : 可测集 i) (hi : 0 <=[i] μ)
  证明: by
  have : 0 <= μ (i inter j) :=
    μ.nonneg_of_zero_le_restrict (μ.zero_le_restrict_subset ‹_› Set.inter_subset_left ‹_›)
  rw [Real.enorm_of_nonneg this]; rw [μ.toMeasureOfZeroLE_apply hi him hjm]; rw [ENNReal.ofReal_eq_coe_nnreal]
-/
private lemma toMeasureOfZeroLE_apply_eq_enorm {i j : Set X} (him : MeasurableSet i) (hi : 0 <=[i] μ)
    (hjm : MeasurableSet j) : μ.toMeasureOfZeroLE i him hi j = ‖μ (i inter j)‖ₑ := by
  have : 0 <= μ (i inter j) :=
    μ.nonneg_of_zero_le_restrict (μ.zero_le_restrict_subset ‹_› Set.inter_subset_left ‹_›)
  rw [Real.enorm_of_nonneg this]; rw [μ.toMeasureOfZeroLE_apply hi him hjm]; rw [ENNReal.ofReal_eq_coe_nnreal]

/--
lemma `toMeasureOfLEZero_apply_eq_enorm` / 引理 `toMeasureOfLEZero_apply_eq_enorm`

English:
lemma toMeasureOfLEZero_apply_eq_enorm
  statement: {i j : Set X} (him : MeasurableSet i)
  proof: by
  have : μ (i inter j) <= 0 :=
    μ.nonpos_of_restrict_le_zero (μ.restrict_le_zero_subset ‹_› Set.inter_subset_left ‹_›)
  rw [← enorm_neg]; rw [Real.enorm_of_nonneg (neg_nonneg.mpr this)]; rw [μ.toMeasureOfLEZero_apply hi him hjm]; rw [ENNReal.ofReal_eq_coe_nnreal]

中文:
引理 toMeasureOfLEZero_apply_eq_enorm
  结论: {i j : 集合 X} (him : 可测集 i)
  证明: by
  have : μ (i inter j) <= 0 :=
    μ.nonpos_of_restrict_le_zero (μ.restrict_le_zero_subset ‹_› Set.inter_subset_left ‹_›)
  rw [← enorm_neg]; rw [Real.enorm_of_nonneg (neg_nonneg.mpr this)]; rw [μ.toMeasureOfLEZero_apply hi him hjm]; rw [ENNReal.ofReal_eq_coe_nnreal]
-/
private lemma toMeasureOfLEZero_apply_eq_enorm {i j : Set X} (him : MeasurableSet i)
    (hi : μ <=[i] 0) (hjm : MeasurableSet j) :
    μ.toMeasureOfLEZero i him hi j = ‖μ (i inter j)‖ₑ := by
  have : μ (i inter j) <= 0 :=
    μ.nonpos_of_restrict_le_zero (μ.restrict_le_zero_subset ‹_› Set.inter_subset_left ‹_›)
  rw [← enorm_neg]; rw [Real.enorm_of_nonneg (neg_nonneg.mpr this)]; rw [μ.toMeasureOfLEZero_apply hi him hjm]; rw [ENNReal.ofReal_eq_coe_nnreal]

/--
theorem `totalVariation_eq_variation` / 定理 `totalVariation_eq_variation`

English:
theorem totalVariation_eq_variation
  given: (μ : SignedMeasure X)
  statement: μ.totalVariation = μ.variation
  proof: by
  ext r hr
  apply le_antisymm
  · obtain ⟨s, hs, hpos, hneg, hposPart, hnegPart⟩ := μ.toJordanDecomposition_spec
    calc μ.totalVariation r
      _ = ‖μ (s inter r)‖ₑ + ‖μ (sᶜ inter r)‖ₑ := by
          rw [totalVariation]; rw [Measure.add_apply]; rw [hposPart]; rw [hnegPart]; rw [μ.toMeasureOf

中文:
定理 totalVariation_eq_variation
  条件: (μ : 符号测度 X)
  结论: μ.totalVariation = μ.variation
  证明: by
  ext r hr
  apply le_antisymm
  · obtain ⟨s, hs, hpos, hneg, hposPart, hnegPart⟩ := μ.toJordanDecomposition_spec
    calc μ.totalVariation r
      _ = ‖μ (s inter r)‖ₑ + ‖μ (sᶜ inter r)‖ₑ := by
          rw [totalVariation]; rw [Measure.add_apply]; rw [hposPart]; rw [hnegPart]; rw [μ.toMeasureOf

Depends on / 依赖: Measure, Measure.add_apply, add_apply, add_le_add, enorm_measure_le_variation, hnegPart, hposPart, hs.compl, le_antisymm, toJordanDecomposition_spec, toMeasureOfLEZero_apply_eq_enorm, toMeasureOfZeroLE_apply_eq_enorm, totalVariation, variation
-/
theorem totalVariation_eq_variation (μ : SignedMeasure X) : μ.totalVariation = μ.variation := by
  ext r hr
  apply le_antisymm
  · obtain ⟨s, hs, hpos, hneg, hposPart, hnegPart⟩ := μ.toJordanDecomposition_spec
    calc μ.totalVariation r
      _ = ‖μ (s inter r)‖ₑ + ‖μ (sᶜ inter r)‖ₑ := by
          rw [totalVariation]; rw [Measure.add_apply]; rw [hposPart]; rw [hnegPart]; rw [μ.toMeasureOfZeroLE_apply_eq_enorm hs hpos hr]; rw [μ.toMeasureOfLEZero_apply_eq_enorm hs.compl hneg hr]
      _ <= μ.variation (s inter r) + μ.variation (sᶜ inter r) :=
          add_le_add (μ.enorm_measure_le_variation _) (μ.enorm_measure_le_variation _)
      _ = μ.variation ((s inter r) union (sᶜ inter r)) :=
        (measure_union (by grind) (hs.compl.inter hr)).symm
      _ = μ.variation r := by congr; grind
  · apply VectorMeasure.variation_le_of_forall_enorm_le
    exact fun s _ => enorm_le_totalVariation μ s

end MeasureTheory.SignedMeasure
