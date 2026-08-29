/-
Copyright (c) 2025 Loic Simon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Loic Simon
-/
module

public import Mathlib.MeasureTheory.Measure.Decomposition.Hahn
public import Mathlib.MeasureTheory.Measure.Sub
public import Mathlib.MeasureTheory.VectorMeasure.Decomposition.Jordan

/-!
# Jordan decomposition from signed measure subtraction

This file develops the Jordan decomposition of the signed measure `μ - ν` for finite measures `μ`
and `ν`, expressing it as the pair `(μ - ν, ν - μ)` of mutually singular finite measures.

The key tool is the Hahn decomposition theorem, which yields a measurable partition of the space
where `μ ≤ ν` and `ν ≤ μ`, and the measure difference behaves like a signed measure difference.

## Main results

* `toJordanDecomposition_toSignedMeasure_sub`:
  The Jordan decomposition of `μ.toSignedMeasure - ν.toSignedMeasure` is given by
  `(μ - ν, ν - μ)`. It relies on the following intermediate results.
* `mutually_singular_measure_sub`:
  The measures `μ - ν` and `ν - μ` are mutually singular.
* `sub_toSignedMeasure_eq_toSignedMeasure_sub`:
  The signed measure `μ.toSignedMeasure - ν.toSignedMeasure` equals
  `(μ - ν).toSignedMeasure - (ν - μ).toSignedMeasure`.
-/

@[expose] public section

open scoped ENNReal NNReal

namespace MeasureTheory.Measure

noncomputable section

variable {X : Type*} {mX : MeasurableSpace X}
variable {s : Set X}
variable {μ ν : Measure X}

/--
lemma `sub_apply_eq_zero_of_isHahnDecomposition` / 引理 `sub_apply_eq_zero_of_isHahnDecomposition`

English:
lemma sub_apply_eq_zero_of_isHahnDecomposition
  proof: by
  rw [← restrict_eq_zero]; rw [restrict_sub_eq_restrict_sub_restrict hs.measurableSet]
  exact sub_eq_zero_of_le hs.le_on

中文:
引理 sub_apply_eq_zero_of_isHahnDecomposition
  证明: by
  rw [← restrict_eq_zero]; rw [restrict_sub_eq_restrict_sub_restrict hs.measurableSet]
  exact sub_eq_zero_of_le hs.le_on

Depends on / 依赖: hs.le_on, hs.measurableSet, le_on, measurableSet, restrict_eq_zero, restrict_sub_eq_restrict_sub_restrict, sub_eq_zero_of_le
-/
lemma sub_apply_eq_zero_of_isHahnDecomposition
    (hs : IsHahnDecomposition μ ν s) : (μ - ν) s = 0 := by
  rw [← restrict_eq_zero]; rw [restrict_sub_eq_restrict_sub_restrict hs.measurableSet]
  exact sub_eq_zero_of_le hs.le_on

variable [IsFiniteMeasure μ] [IsFiniteMeasure ν]

/--
theorem `mutually_singular_measure_sub` / 定理 `mutually_singular_measure_sub`

English:
theorem mutually_singular_measure_sub
  proof: by
  obtain ⟨s, hs⟩ := exists_isHahnDecomposition μ ν
  exact ⟨s, hs.measurableSet,
    sub_apply_eq_zero_of_isHahnDecomposition hs,
    sub_apply_eq_zero_of_isHahnDecomposition hs.compl⟩

中文:
定理 mutually_singular_measure_sub
  证明: by
  obtain ⟨s, hs⟩ := exists_isHahnDecomposition μ ν
  exact ⟨s, hs.measurableSet,
    sub_apply_eq_zero_of_isHahnDecomposition hs,
    sub_apply_eq_zero_of_isHahnDecomposition hs.compl⟩

Depends on / 依赖: exists_isHahnDecomposition, hs.compl, hs.measurableSet, measurableSet, sub_apply_eq_zero_of_isHahnDecomposition
-/
theorem mutually_singular_measure_sub :
    (μ - ν).MutuallySingular (ν - μ) := by
  obtain ⟨s, hs⟩ := exists_isHahnDecomposition μ ν
  exact ⟨s, hs.measurableSet,
    sub_apply_eq_zero_of_isHahnDecomposition hs,
    sub_apply_eq_zero_of_isHahnDecomposition hs.compl⟩

/--
lemma `toSignedMeasure_restrict_sub` / 引理 `toSignedMeasure_restrict_sub`

English:
lemma toSignedMeasure_restrict_sub
  given: (hs : IsHahnDecomposition μ ν s)
  proof: by
  have hmeas := hs.measurableSet
  rw [eq_sub_iff_add_eq]; rw [toSignedMeasure_restrict_eq_restrict_toSignedMeasure _ _ hmeas]; rw [← toSignedMeasure_add]
  simp only [restrict_sub_eq_restrict_sub_restrict, hmeas, sub_add_cancel_of_le hs.le_on]
  exact (toSignedMeasure_restrict_eq_restrict_toSign

中文:
引理 toSignedMeasure_restrict_sub
  条件: (hs : IsHahnDecomposition μ ν s)
  证明: by
  have hmeas := hs.measurableSet
  rw [eq_sub_iff_add_eq]; rw [toSignedMeasure_restrict_eq_restrict_toSignedMeasure _ _ hmeas]; rw [← toSignedMeasure_add]
  simp only [restrict_sub_eq_restrict_sub_restrict, hmeas, sub_add_cancel_of_le hs.le_on]
  exact (toSignedMeasure_restrict_eq_restrict_toSign

Depends on / 依赖: eq_sub_iff_add_eq, hs.le_on, hs.measurableSet, le_on, measurableSet, restrict_sub_eq_restrict_sub_restrict, sub_add_cancel_of_le, toSignedMeasure_add, toSignedMeasure_restrict_eq_restrict_toSignedMeasure
-/
lemma toSignedMeasure_restrict_sub (hs : IsHahnDecomposition μ ν s) :
    ((ν - μ).restrict s).toSignedMeasure =
      ν.toSignedMeasure.restrict s - μ.toSignedMeasure.restrict s := by
  have hmeas := hs.measurableSet
  rw [eq_sub_iff_add_eq]; rw [toSignedMeasure_restrict_eq_restrict_toSignedMeasure _ _ hmeas]; rw [← toSignedMeasure_add]
  simp only [restrict_sub_eq_restrict_sub_restrict, hmeas, sub_add_cancel_of_le hs.le_on]
  exact (toSignedMeasure_restrict_eq_restrict_toSignedMeasure _ _ hmeas).symm

/--
theorem `sub_toSignedMeasure_eq_toSignedMeasure_sub` / 定理 `sub_toSignedMeasure_eq_toSignedMeasure_sub`

English:
theorem sub_toSignedMeasure_eq_toSignedMeasure_sub
  proof: by
  obtain ⟨s, hs⟩ := exists_isHahnDecomposition μ ν
  have hsc := hs.compl
  have h₁ := toSignedMeasure_restrict_sub hs
  have h₂ := toSignedMeasure_restrict_sub hsc
have h₁' := toSignedMeasure_congr restrict_eq_zero.mpr
    sub_apply_eq_zero_of_isHahnDecomposition hs
have h₂' := toSignedMeasure_c

中文:
定理 sub_toSignedMeasure_eq_toSignedMeasure_sub
  证明: by
  obtain ⟨s, hs⟩ := exists_isHahnDecomposition μ ν
  have hsc := hs.compl
  have h₁ := toSignedMeasure_restrict_sub hs
  have h₂ := toSignedMeasure_restrict_sub hsc
have h₁' := toSignedMeasure_congr restrict_eq_zero.mpr
    sub_apply_eq_zero_of_isHahnDecomposition hs
have h₂' := toSignedMeasure_c

Depends on / 依赖: VectorMeasure, VectorMeasure.restrict_add_restrict_compl, exists_isHahnDecomposition, hs.compl, hs.measurableSet, measurableSet, restrict_add_restrict_compl, restrict_eq_zero, restrict_eq_zero.mpr, sub_apply_eq_zero_of_isHahnDecomposition, toSignedMeasure, toSignedMeasure_congr, toSignedMeasure_restrict_sub
-/
theorem sub_toSignedMeasure_eq_toSignedMeasure_sub :
    μ.toSignedMeasure - ν.toSignedMeasure =
      (μ - ν).toSignedMeasure - (ν - μ).toSignedMeasure := by
  obtain ⟨s, hs⟩ := exists_isHahnDecomposition μ ν
  have hsc := hs.compl
  have h₁ := toSignedMeasure_restrict_sub hs
  have h₂ := toSignedMeasure_restrict_sub hsc
have h₁' := toSignedMeasure_congr restrict_eq_zero.mpr
    sub_apply_eq_zero_of_isHahnDecomposition hs
have h₂' := toSignedMeasure_congr restrict_eq_zero.mpr
  sub_apply_eq_zero_of_isHahnDecomposition hsc
  have partition₁ := VectorMeasure.restrict_add_restrict_compl (v := (μ - ν).toSignedMeasure)
    hs.measurableSet
  have partition₂ := VectorMeasure.restrict_add_restrict_compl (v := (ν - μ).toSignedMeasure)
    hs.measurableSet
  rw [toSignedMeasure_restrict_eq_restrict_toSignedMeasure _ _ hs.measurableSet]; rw [toSignedMeasure_restrict_eq_restrict_toSignedMeasure _ _ hs.measurableSet.compl]
    at partition₁ partition₂
  rw [h₁']; rw [h₂] at partition₁
  rw [h₁]; rw [h₂'] at partition₂
  simp only [toSignedMeasure_zero, zero_add] at partition₁ partition₂
  rw [← VectorMeasure.restrict_add_restrict_compl (v := μ.toSignedMeasure) hs.measurableSet]; rw [← VectorMeasure.restrict_add_restrict_compl (v := ν.toSignedMeasure) hs.measurableSet]; rw [← partition₁]; rw [← partition₂]
  abel

/--
Definition of `jordanDecompositionOfToSignedMeasureSub` / `jordanDecompositionOfToSignedMeasureSub` 的定义

English:
definition jordanDecompositionOfToSignedMeasureSub
  body: μ - ν
  negPart := ν - μ
  mutuallySingular := mutually_singular_measure_sub

中文:
定义 jordanDecompositionOfToSignedMeasureSub
  定义体: μ - ν
  negPart := ν - μ
  mutuallySingular := mutually_singular_measure_sub
-/
def jordanDecompositionOfToSignedMeasureSub
    (μ ν : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ν] : JordanDecomposition X where
  posPart := μ - ν
  negPart := ν - μ
  mutuallySingular := mutually_singular_measure_sub

/--
lemma `jordanDecompositionOfToSignedMeasureSub_posPart` / 引理 `jordanDecompositionOfToSignedMeasureSub_posPart`

English:
lemma jordanDecompositionOfToSignedMeasureSub_posPart
  proof: rfl

中文:
引理 jordanDecompositionOfToSignedMeasureSub_posPart
  证明: rfl
-/
lemma jordanDecompositionOfToSignedMeasureSub_posPart :
    (jordanDecompositionOfToSignedMeasureSub μ ν).posPart = μ - ν := rfl

/--
lemma `jordanDecompositionOfToSignedMeasureSub_negPart` / 引理 `jordanDecompositionOfToSignedMeasureSub_negPart`

English:
lemma jordanDecompositionOfToSignedMeasureSub_negPart
  proof: rfl

中文:
引理 jordanDecompositionOfToSignedMeasureSub_negPart
  证明: rfl
-/
lemma jordanDecompositionOfToSignedMeasureSub_negPart :
    (jordanDecompositionOfToSignedMeasureSub μ ν).negPart = ν - μ := rfl

/--
lemma `jordanDecompositionOfToSignedMeasureSub_toSignedMeasure` / 引理 `jordanDecompositionOfToSignedMeasureSub_toSignedMeasure`

English:
lemma jordanDecompositionOfToSignedMeasureSub_toSignedMeasure
  proof: by
  simp_rw [JordanDecomposition.toSignedMeasure, jordanDecompositionOfToSignedMeasureSub_posPart,
    jordanDecompositionOfToSignedMeasureSub_negPart, ← sub_toSignedMeasure_eq_toSignedMeasure_sub]

中文:
引理 jordanDecompositionOfToSignedMeasureSub_toSignedMeasure
  证明: by
  simp_rw [JordanDecomposition.toSignedMeasure, jordanDecompositionOfToSignedMeasureSub_posPart,
    jordanDecompositionOfToSignedMeasureSub_negPart, ← sub_toSignedMeasure_eq_toSignedMeasure_sub]

Depends on / 依赖: JordanDecomposition, JordanDecomposition.toSignedMeasure, jordanDecompositionOfToSignedMeasureSub_negPart, jordanDecompositionOfToSignedMeasureSub_posPart, simp_rw, sub_toSignedMeasure_eq_toSignedMeasure_sub, toSignedMeasure
-/
lemma jordanDecompositionOfToSignedMeasureSub_toSignedMeasure :
    (jordanDecompositionOfToSignedMeasureSub μ ν).toSignedMeasure =
    μ.toSignedMeasure - ν.toSignedMeasure := by
  simp_rw [JordanDecomposition.toSignedMeasure, jordanDecompositionOfToSignedMeasureSub_posPart,
    jordanDecompositionOfToSignedMeasureSub_negPart, ← sub_toSignedMeasure_eq_toSignedMeasure_sub]

/-- The Jordan decomposition of `μ.toSignedMeasure - ν.toSignedMeasure` is `(μ - ν, ν - μ)`. -/
@[simp]
/--
theorem `toJordanDecomposition_toSignedMeasure_sub` / 定理 `toJordanDecomposition_toSignedMeasure_sub`

English:
theorem toJordanDecomposition_toSignedMeasure_sub
  proof: by
  apply JordanDecomposition.toSignedMeasure_injective
  rw [SignedMeasure.toSignedMeasure_toJordanDecomposition]; rw [jordanDecompositionOfToSignedMeasureSub_toSignedMeasure]

中文:
定理 toJordanDecomposition_toSignedMeasure_sub
  证明: by
  apply JordanDecomposition.toSignedMeasure_injective
  rw [SignedMeasure.toSignedMeasure_toJordanDecomposition]; rw [jordanDecompositionOfToSignedMeasureSub_toSignedMeasure]

Depends on / 依赖: JordanDecomposition, JordanDecomposition.toSignedMeasure_injective, SignedMeasure, SignedMeasure.toSignedMeasure_toJordanDecomposition, jordanDecompositionOfToSignedMeasureSub_toSignedMeasure, toSignedMeasure_injective, toSignedMeasure_toJordanDecomposition
-/
theorem toJordanDecomposition_toSignedMeasure_sub :
    (μ.toSignedMeasure - ν.toSignedMeasure).toJordanDecomposition =
      jordanDecompositionOfToSignedMeasureSub μ ν := by
  apply JordanDecomposition.toSignedMeasure_injective
  rw [SignedMeasure.toSignedMeasure_toJordanDecomposition]; rw [jordanDecompositionOfToSignedMeasureSub_toSignedMeasure]

end

end MeasureTheory.Measure
