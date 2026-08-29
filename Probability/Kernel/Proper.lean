/-
Copyright (c) 2024 Yaël Dillies, Kalle Kytölä, Kin Yau James Wong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Kalle Kytölä, Kin Yau James Wong
-/
module

public import Mathlib.Probability.Kernel.Composition.CompNotation

/-!
# Proper kernels

This file defines properness of measure kernels.

For two σ-algebras `𝓑 ≤ 𝓧`, a `𝓑, 𝓧`-kernel `π : X → Measure X` is proper if
`∫ x, g x * f x ∂(π x₀) = g x₀ * ∫ x, f x ∂(π x₀)` for all `x₀ : X`, `𝓧`-measurable function `f`
and `𝓑`-measurable function `g`.

By the standard machine, this is equivalent to having that, for all `B ∈ 𝓑`, `π` restricted to `B`
is the same as `π` times the indicator of `B`.

This should be thought of as the condition under which one can meaningfully restrict a kernel to an
event.

## TODO

Prove the `integral` versions of the `lintegral` lemmas below
-/

public section

open MeasureTheory ENNReal NNReal Set
open scoped ProbabilityTheory

namespace ProbabilityTheory.Kernel
variable {X : Type*} {𝓑 𝓧 : MeasurableSpace X} {π : Kernel[𝓑, 𝓧] X X} {A B : Set X}
  {f g : X -> Real>=0∞} {x₀ : X}

/--
Definition of `IsProper` / `IsProper` 的定义

English:
structure IsProper
  parameters: (π : Kernel[𝓑, 𝓧] X X)
  axioms and operations (1):
    - restrict_eq_indicator_smul' : forall ⦃B : Set X⦄ (hB : MeasurableSet[𝓑 ⊓ 𝓧] B) (x : X), π.restrict (inf_le_right (b := 𝓧) _ hB) x = B.indicator (fun _ => (1 : Real>=0∞)) x • π x

中文:
结构 IsProper
  参数: (π : Kernel[𝓑, 𝓧] X X)
  公理与运算 (1 个):
    - restrict_eq_indicator_smul' : 对任意 ⦃B : Set X⦄ (hB : MeasurableSet[𝓑 ⊓ 𝓧] B) (x : X), π.restrict (inf_le_right (b := 𝓧) _ hB) x = B.indicator (fun _ => (1 : 实数>=0∞)) x • π x

Depends on / 依赖: B.indicator, indicator
-/
structure IsProper (π : Kernel[𝓑, 𝓧] X X) : Prop where
  restrict_eq_indicator_smul' :
    forall ⦃B : Set X⦄ (hB : MeasurableSet[𝓑 ⊓ 𝓧] B) (x : X),
      π.restrict (inf_le_right (b := 𝓧) _ hB) x = B.indicator (fun _ => (1 : Real>=0∞)) x • π x

/--
lemma `isProper_iff_restrict_eq_indicator_smul` / 引理 `isProper_iff_restrict_eq_indicator_smul`

English:
lemma isProper_iff_restrict_eq_indicator_smul
  given: (h𝓑𝓧 : 𝓑 <= 𝓧)
  proof: by
  refine ⟨fun ⟨h⟩ => ?_, fun h => ⟨?_⟩⟩ <;> simpa +instances only [inf_eq_left.2 h𝓑𝓧] using h

中文:
引理 isProper_iff_restrict_eq_indicator_smul
  条件: (h𝓑𝓧 : 𝓑 <= 𝓧)
  证明: by
  refine ⟨fun ⟨h⟩ => ?_, fun h => ⟨?_⟩⟩ <;> simpa +instances only [inf_eq_left.2 h𝓑𝓧] using h

Depends on / 依赖: inf_eq_left, instances
-/
lemma isProper_iff_restrict_eq_indicator_smul (h𝓑𝓧 : 𝓑 <= 𝓧) :
    IsProper π ↔ forall ⦃B : Set X⦄ (hB : MeasurableSet[𝓑] B) (x : X),
      π.restrict (h𝓑𝓧 _ hB) x = B.indicator (fun _ => (1 : Real>=0∞)) x • π x := by
  refine ⟨fun ⟨h⟩ => ?_, fun h => ⟨?_⟩⟩ <;> simpa +instances only [inf_eq_left.2 h𝓑𝓧] using h

/--
lemma `isProper_iff_inter_eq_indicator_mul` / 引理 `isProper_iff_inter_eq_indicator_mul`

English:
lemma isProper_iff_inter_eq_indicator_mul
  given: (h𝓑𝓧 : 𝓑 <= 𝓧)
  proof: by
  calc
    _ ↔ forall ⦃A : Set X⦄ (_hA : MeasurableSet[𝓧] A) ⦃B : Set X⦄ (hB : MeasurableSet[𝓑] B) (x : X),
          π.restrict (h𝓑𝓧 _ hB) x A = B.indicator 1 x * π x A := by
      simp [isProper_iff_restrict_eq_indicator_smul h𝓑𝓧, Measure.ext_iff]; aesop
    _ ↔ _ := by congr! 5 with A hA B hB 

中文:
引理 isProper_iff_inter_eq_indicator_mul
  条件: (h𝓑𝓧 : 𝓑 <= 𝓧)
  证明: by
  calc
    _ ↔ forall ⦃A : Set X⦄ (_hA : MeasurableSet[𝓧] A) ⦃B : Set X⦄ (hB : MeasurableSet[𝓑] B) (x : X),
          π.restrict (h𝓑𝓧 _ hB) x A = B.indicator 1 x * π x A := by
      simp [isProper_iff_restrict_eq_indicator_smul h𝓑𝓧, Measure.ext_iff]; aesop
    _ ↔ _ := by congr! 5 with A hA B hB 

Depends on / 依赖: B.indicator, MeasurableSet, Measure, Measure.ext_iff, Measure.restrict_apply, ext_iff, indicator, isProper_iff_restrict_eq_indicator_smul, restrict, restrict_apply
-/
lemma isProper_iff_inter_eq_indicator_mul (h𝓑𝓧 : 𝓑 <= 𝓧) :
    IsProper π ↔
      forall ⦃A : Set X⦄ (_hA : MeasurableSet[𝓧] A) ⦃B : Set X⦄ (_hB : MeasurableSet[𝓑] B) (x : X),
        π x (A inter B) = B.indicator 1 x * π x A := by
  calc
    _ ↔ forall ⦃A : Set X⦄ (_hA : MeasurableSet[𝓧] A) ⦃B : Set X⦄ (hB : MeasurableSet[𝓑] B) (x : X),
          π.restrict (h𝓑𝓧 _ hB) x A = B.indicator 1 x * π x A := by
      simp [isProper_iff_restrict_eq_indicator_smul h𝓑𝓧, Measure.ext_iff]; aesop
    _ ↔ _ := by congr! 5 with A hA B hB x; rw [restrict_apply, Measure.restrict_apply hA]

alias ⟨IsProper.restrict_eq_indicator_smul, IsProper.of_restrict_eq_indicator_smul⟩ :=
  isProper_iff_restrict_eq_indicator_smul

alias ⟨IsProper.inter_eq_indicator_mul, IsProper.of_inter_eq_indicator_mul⟩ :=
  isProper_iff_inter_eq_indicator_mul

/--
lemma `IsProper.setLIntegral_eq_comp` / 引理 `IsProper.setLIntegral_eq_comp`

English:
lemma IsProper.setLIntegral_eq_comp
  statement: (hπ : IsProper π) (h𝓑𝓧 : 𝓑 <= 𝓧) {μ : Measure[𝓧] X}
  proof: by
  rw [Measure.bind_apply (by measurability) (π.measurable.mono h𝓑𝓧 le_rfl).aemeasurable]
  simp only [hπ.inter_eq_indicator_mul h𝓑𝓧 hA hB, ← indicator_mul_const, Pi.one_apply, one_mul]
  rw [← lintegral_indicator (h𝓑𝓧 _ hB)]
  rfl

中文:
引理 IsProper.setLIntegral_eq_comp
  结论: (hπ : Is命题er π) (h𝓑𝓧 : 𝓑 <= 𝓧) {μ : Measure[𝓧] X}
  证明: by
  rw [Measure.bind_apply (by measurability) (π.measurable.mono h𝓑𝓧 le_rfl).aemeasurable]
  simp only [hπ.inter_eq_indicator_mul h𝓑𝓧 hA hB, ← indicator_mul_const, Pi.one_apply, one_mul]
  rw [← lintegral_indicator (h𝓑𝓧 _ hB)]
  rfl

Depends on / 依赖: Measure, Measure.bind_apply, Pi.one_apply, aemeasurable, bind_apply, indicator_mul_const, inter_eq_indicator_mul, le_rfl, lintegral_indicator, measurability, measurable, measurable.mono, one_apply, one_mul
-/
lemma IsProper.setLIntegral_eq_comp (hπ : IsProper π) (h𝓑𝓧 : 𝓑 <= 𝓧) {μ : Measure[𝓧] X}
    (hA : MeasurableSet[𝓧] A) (hB : MeasurableSet[𝓑] B) :
    ∫⁻ a in B, π a A ∂μ = (π ∘ₘ μ) (A inter B) := by
  rw [Measure.bind_apply (by measurability) (π.measurable.mono h𝓑𝓧 le_rfl).aemeasurable]
  simp only [hπ.inter_eq_indicator_mul h𝓑𝓧 hA hB, ← indicator_mul_const, Pi.one_apply, one_mul]
  rw [← lintegral_indicator (h𝓑𝓧 _ hB)]
  rfl

/--
lemma `IsProper.lintegral_indicator_mul_indicator` / 引理 `IsProper.lintegral_indicator_mul_indicator`

English:
lemma IsProper.lintegral_indicator_mul_indicator
  statement: (hπ : IsProper π) (h𝓑𝓧 : 𝓑 <= 𝓧)
  proof: by
  simp_rw [← inter_indicator_mul]
  rw [lintegral_indicator ((h𝓑𝓧 _ hB).inter hA)]; rw [lintegral_indicator hA]
  simp only [MeasureTheory.lintegral_const, MeasurableSet.univ, Measure.restrict_apply, univ_inter,
    Pi.one_apply, one_mul]
  rw [← hπ.inter_eq_indicator_mul h𝓑𝓧 hA hB]; rw [inter_co

中文:
引理 IsProper.lintegral_indicator_mul_indicator
  结论: (hπ : Is命题er π) (h𝓑𝓧 : 𝓑 <= 𝓧)
  证明: by
  simp_rw [← inter_indicator_mul]
  rw [lintegral_indicator ((h𝓑𝓧 _ hB).inter hA)]; rw [lintegral_indicator hA]
  simp only [MeasureTheory.lintegral_const, MeasurableSet.univ, Measure.restrict_apply, univ_inter,
    Pi.one_apply, one_mul]
  rw [← hπ.inter_eq_indicator_mul h𝓑𝓧 hA hB]; rw [inter_co
-/
private lemma IsProper.lintegral_indicator_mul_indicator (hπ : IsProper π) (h𝓑𝓧 : 𝓑 <= 𝓧)
    (hA : MeasurableSet[𝓧] A) (hB : MeasurableSet[𝓑] B) :
    ∫⁻ x, B.indicator 1 x * A.indicator 1 x ∂(π x₀) =
      B.indicator 1 x₀ * ∫⁻ x, A.indicator 1 x ∂(π x₀) := by
  simp_rw [← inter_indicator_mul]
  rw [lintegral_indicator ((h𝓑𝓧 _ hB).inter hA)]; rw [lintegral_indicator hA]
  simp only [MeasureTheory.lintegral_const, MeasurableSet.univ, Measure.restrict_apply, univ_inter,
    Pi.one_apply, one_mul]
  rw [← hπ.inter_eq_indicator_mul h𝓑𝓧 hA hB]; rw [inter_comm]

/--
lemma `IsProper.lintegral_indicator_mul` / 引理 `IsProper.lintegral_indicator_mul`

English:
lemma IsProper.lintegral_indicator_mul
  statement: (hπ : IsProper π) (h𝓑𝓧 : 𝓑 <= 𝓧)
  proof: by
  refine hf.ennreal_induction ?_ ?_ ?_
  · rintro c A hA
    simp_rw [← smul_indicator_one_apply, mul_smul_comm, smul_eq_mul]
    rw [lintegral_const_mul]; rw [lintegral_const_mul]; rw [hπ.lintegral_indicator_mul_indicator h𝓑𝓧 hA hB]; rw [mul_left_comm] <;> measurability
  · rintro f₁ f₂ - _ _ hf

中文:
引理 IsProper.lintegral_indicator_mul
  结论: (hπ : Is命题er π) (h𝓑𝓧 : 𝓑 <= 𝓧)
  证明: by
  refine hf.ennreal_induction ?_ ?_ ?_
  · rintro c A hA
    simp_rw [← smul_indicator_one_apply, mul_smul_comm, smul_eq_mul]
    rw [lintegral_const_mul]; rw [lintegral_const_mul]; rw [hπ.lintegral_indicator_mul_indicator h𝓑𝓧 hA hB]; rw [mul_left_comm] <;> measurability
  · rintro f₁ f₂ - _ _ hf
-/
private lemma IsProper.lintegral_indicator_mul (hπ : IsProper π) (h𝓑𝓧 : 𝓑 <= 𝓧)
    (hf : Measurable[𝓧] f) (hB : MeasurableSet[𝓑] B) :
    ∫⁻ x, B.indicator 1 x * f x ∂(π x₀) = B.indicator 1 x₀ * ∫⁻ x, f x ∂(π x₀) := by
  refine hf.ennreal_induction ?_ ?_ ?_
  · rintro c A hA
    simp_rw [← smul_indicator_one_apply, mul_smul_comm, smul_eq_mul]
    rw [lintegral_const_mul]; rw [lintegral_const_mul]; rw [hπ.lintegral_indicator_mul_indicator h𝓑𝓧 hA hB]; rw [mul_left_comm] <;> measurability
  · rintro f₁ f₂ - _ _ hf₁ hf₂
    simp only [Pi.add_apply, mul_add]
    rw [lintegral_add_right]; rw [lintegral_add_right]; rw [hf₁]; rw [hf₂]; rw [mul_add] <;> measurability
  · rintro f' hf'_meas hf'_mono hf'
    simp_rw [ENNReal.mul_iSup]
    rw [lintegral_iSup (by measurability)]; rw [lintegral_iSup hf'_meas hf'_mono]; rw [ENNReal.mul_iSup]
    · simp_rw [hf']
    · exact hf'_mono.const_mul zero_le

/--
lemma `IsProper.setLIntegral_eq_indicator_mul_lintegral` / 引理 `IsProper.setLIntegral_eq_indicator_mul_lintegral`

English:
lemma IsProper.setLIntegral_eq_indicator_mul_lintegral
  statement: (hπ : IsProper π) (h𝓑𝓧 : 𝓑 <= 𝓧)
  proof: by
  simp [← hπ.lintegral_indicator_mul h𝓑𝓧 hf hB, ← indicator_mul_left,
    lintegral_indicator (h𝓑𝓧 _ hB)]

中文:
引理 IsProper.setLIntegral_eq_indicator_mul_lintegral
  结论: (hπ : Is命题er π) (h𝓑𝓧 : 𝓑 <= 𝓧)
  证明: by
  simp [← hπ.lintegral_indicator_mul h𝓑𝓧 hf hB, ← indicator_mul_left,
    lintegral_indicator (h𝓑𝓧 _ hB)]

Depends on / 依赖: indicator_mul_left, lintegral_indicator, lintegral_indicator_mul
-/
lemma IsProper.setLIntegral_eq_indicator_mul_lintegral (hπ : IsProper π) (h𝓑𝓧 : 𝓑 <= 𝓧)
    (hf : Measurable[𝓧] f) (hB : MeasurableSet[𝓑] B) (x₀ : X) :
    ∫⁻ x in B, f x ∂(π x₀) = B.indicator 1 x₀ * ∫⁻ x, f x ∂(π x₀) := by
  simp [← hπ.lintegral_indicator_mul h𝓑𝓧 hf hB, ← indicator_mul_left,
    lintegral_indicator (h𝓑𝓧 _ hB)]

/--
lemma `IsProper.setLIntegral_inter_eq_indicator_mul_setLIntegral` / 引理 `IsProper.setLIntegral_inter_eq_indicator_mul_setLIntegral`

English:
lemma IsProper.setLIntegral_inter_eq_indicator_mul_setLIntegral
  statement: (hπ : IsProper π) (h𝓑𝓧 : 𝓑 <= 𝓧)
  proof: by
  rw [← lintegral_indicator hA]; rw [← hπ.setLIntegral_eq_indicator_mul_lintegral h𝓑𝓧 _ hB]; rw [setLIntegral_indicator] <;> measurability

中文:
引理 IsProper.setLIntegral_inter_eq_indicator_mul_setLIntegral
  结论: (hπ : Is命题er π) (h𝓑𝓧 : 𝓑 <= 𝓧)
  证明: by
  rw [← lintegral_indicator hA]; rw [← hπ.setLIntegral_eq_indicator_mul_lintegral h𝓑𝓧 _ hB]; rw [setLIntegral_indicator] <;> measurability

Depends on / 依赖: lintegral_indicator, measurability, setLIntegral_eq_indicator_mul_lintegral, setLIntegral_indicator
-/
lemma IsProper.setLIntegral_inter_eq_indicator_mul_setLIntegral (hπ : IsProper π) (h𝓑𝓧 : 𝓑 <= 𝓧)
    (hf : Measurable[𝓧] f) (hA : MeasurableSet[𝓧] A) (hB : MeasurableSet[𝓑] B) (x₀ : X) :
    ∫⁻ x in A inter B, f x ∂(π x₀) = B.indicator 1 x₀ * ∫⁻ x in A, f x ∂(π x₀) := by
  rw [← lintegral_indicator hA]; rw [← hπ.setLIntegral_eq_indicator_mul_lintegral h𝓑𝓧 _ hB]; rw [setLIntegral_indicator] <;> measurability

/--
lemma `IsProper.lintegral_mul` / 引理 `IsProper.lintegral_mul`

English:
lemma IsProper.lintegral_mul
  statement: (hπ : IsProper π) (h𝓑𝓧 : 𝓑 <= 𝓧) (hf : Measurable[𝓧] f)
  proof: by
  refine hg.ennreal_induction ?_ ?_ ?_
  · rintro c A hA
    simp_rw [← smul_indicator_one_apply, smul_mul_assoc, smul_eq_mul]
    rw [lintegral_const_mul]; rw [hπ.lintegral_indicator_mul h𝓑𝓧 hf hA]
    · measurability
  · rintro g₁ g₂ - _ hg₂_meas hg₁ hg₂
    simp only [Pi.add_apply, add_mul]
  

中文:
引理 IsProper.lintegral_mul
  结论: (hπ : Is命题er π) (h𝓑𝓧 : 𝓑 <= 𝓧) (hf : Measurable[𝓧] f)
  证明: by
  refine hg.ennreal_induction ?_ ?_ ?_
  · rintro c A hA
    simp_rw [← smul_indicator_one_apply, smul_mul_assoc, smul_eq_mul]
    rw [lintegral_const_mul]; rw [hπ.lintegral_indicator_mul h𝓑𝓧 hf hA]
    · measurability
  · rintro g₁ g₂ - _ hg₂_meas hg₁ hg₂
    simp only [Pi.add_apply, add_mul]
  

Depends on / 依赖: ENNReal, ENNReal.iSup_mul, Pi.add_apply, _meas, _meas.mono, _mono, add_apply, add_mul, ennreal_induction, fun_mul, hg.ennreal_induction, iSup_mul, le_rfl, lintegral_add_right, lintegral_const_mul, lintegral_iSup, lintegral_indicator_mul, measurability, simp_rw, smul_eq_mul
-/
lemma IsProper.lintegral_mul (hπ : IsProper π) (h𝓑𝓧 : 𝓑 <= 𝓧) (hf : Measurable[𝓧] f)
    (hg : Measurable[𝓑] g) (x₀ : X) :
    ∫⁻ x, g x * f x ∂(π x₀) = g x₀ * ∫⁻ x, f x ∂(π x₀) := by
  refine hg.ennreal_induction ?_ ?_ ?_
  · rintro c A hA
    simp_rw [← smul_indicator_one_apply, smul_mul_assoc, smul_eq_mul]
    rw [lintegral_const_mul]; rw [hπ.lintegral_indicator_mul h𝓑𝓧 hf hA]
    · measurability
  · rintro g₁ g₂ - _ hg₂_meas hg₁ hg₂
    simp only [Pi.add_apply, add_mul]
    rw [lintegral_add_right]; rw [hg₁]; rw [hg₂]
    · exact (hg₂_meas.mono h𝓑𝓧 le_rfl).mul hf
  · rintro g' hg'_meas hg'_mono hg'
    simp_rw [ENNReal.iSup_mul]
    rw [lintegral_iSup (fun n => ((hg'_meas _).mono h𝓑𝓧 le_rfl).fun_mul hf)
      (hg'_mono.mul_const zero_le)]
    simp_rw [hg']

end ProbabilityTheory.Kernel
