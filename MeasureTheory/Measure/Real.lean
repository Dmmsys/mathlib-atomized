/-
Copyright (c) 2025 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite

/-!
# Measures as real-valued functions

Given a measure `μ`, we have defined `μ.real` as the function sending a set `s` to `(μ s).toReal`.
In this file, we develop a basic API around this notion.

We essentially copy relevant lemmas from the files `MeasureSpaceDef.lean`, `NullMeasurable.lean` and
`MeasureSpace.lean`, and adapt them by replacing in their name `measure` with `measureReal`.

Many lemmas require an assumption that some set has finite measure. These assumptions are written
in the form `(h : μ s ≠ ∞ := by finiteness)`, where `finiteness` is a tactic for goals of
the form `≠ ∞`.

There are certainly many missing lemmas. The missing ones should be added as they are needed.

There are no lemmas on infinite sums, as summability issues are really
more painful with reals than nonnegative extended reals. They should probably be added in the long
run.
-/

public section

open MeasureTheory Measure Set
open scoped ENNReal NNReal Function symmDiff

namespace MeasureTheory

variable {α β ι : Type*} {_ : MeasurableSpace α} {μ : Measure α} {s s₁ s₂ s₃ t t₁ t₂ u : Set α}

/--
theorem `measureReal_eq_zero_iff` / 定理 `measureReal_eq_zero_iff`

English:
theorem measureReal_eq_zero_iff
  given: (h : μ s != ∞ := by finiteness)
  proof: by
  rw [Measure.real]; rw [ENNReal.toReal_eq_zero_iff]
  exact or_iff_left h

中文:
定理 measure实数_eq_zero_iff
  条件: (h : μ s != ∞ := by finiteness)
  证明: by
  rw [Measure.real]; rw [ENNReal.toReal_eq_zero_iff]
  exact or_iff_left h

Depends on / 依赖: ENNReal, ENNReal.toReal_eq_zero_iff, Measure, Measure.real, finiteness, or_iff_left, toReal_eq_zero_iff
-/
theorem measureReal_eq_zero_iff (h : μ s != ∞ := by finiteness) :
    μ.real s = 0 ↔ μ s = 0 := by
  rw [Measure.real]; rw [ENNReal.toReal_eq_zero_iff]
  exact or_iff_left h

/--
theorem `measureReal_ne_zero_iff` / 定理 `measureReal_ne_zero_iff`

English:
theorem measureReal_ne_zero_iff
  given: (h : μ s != ∞ := by finiteness)
  proof: by
  simp [measureReal_eq_zero_iff, h]

中文:
定理 measure实数_ne_zero_iff
  条件: (h : μ s != ∞ := by finiteness)
  证明: by
  simp [measureReal_eq_zero_iff, h]

Depends on / 依赖: finiteness, measureReal_eq_zero_iff
-/
theorem measureReal_ne_zero_iff (h : μ s != ∞ := by finiteness) :
    μ.real s != 0 ↔ μ s != 0 := by
  simp [measureReal_eq_zero_iff, h]

/--
theorem `measureReal_zero` / 定理 `measureReal_zero`

English:
theorem measureReal_zero
  statement: (0 : Measure α).real = 0
  proof: rfl

中文:
定理 measure实数_zero
  结论: (0 : 测度 α).real = 0
  证明: rfl
-/
@[simp] theorem measureReal_zero : (0 : Measure α).real = 0 := rfl

/--
theorem `measureReal_zero_apply` / 定理 `measureReal_zero_apply`

English:
theorem measureReal_zero_apply
  given: (s : Set α)
  statement: (0 : Measure α).real s = 0
  proof: rfl

中文:
定理 measure实数_zero_apply
  条件: (s : 集合 α)
  结论: (0 : 测度 α).real s = 0
  证明: rfl
-/
theorem measureReal_zero_apply (s : Set α) : (0 : Measure α).real s = 0 := rfl

/--
theorem `measureReal_nonneg` / 定理 `measureReal_nonneg`

English:
theorem measureReal_nonneg
  statement: 0 <= μ.real s
  proof: ENNReal.toReal_nonneg

中文:
定理 measure实数_nonneg
  结论: 0 <= μ.real s
  证明: ENNReal.toReal_nonneg
-/
@[simp] theorem measureReal_nonneg : 0 <= μ.real s := ENNReal.toReal_nonneg

/--
theorem `measureReal_empty` / 定理 `measureReal_empty`

English:
theorem measureReal_empty
  statement: μ.real ∅ = 0
  proof: by simp [Measure.real]

@[simp]

中文:
定理 measure实数_empty
  结论: μ.real ∅ = 0
  证明: by simp [Measure.real]

@[simp]
-/
@[simp] theorem measureReal_empty : μ.real ∅ = 0 := by simp [Measure.real]

@[simp]
/--
theorem `measureReal_univ_pos` / 定理 `measureReal_univ_pos`

English:
theorem measureReal_univ_pos
  given: [IsFiniteMeasure μ] [NeZero μ]
  statement: 0 < μ.real Set.univ
  proof: ENNReal.toReal_pos (NeZero.ne (μ Set.univ)) (by finiteness)

中文:
定理 measure实数_univ_pos
  条件: [是有限测度 μ] [NeZero μ]
  结论: 0 < μ.real 集合.univ
  证明: ENNReal.toReal_pos (NeZero.ne (μ Set.univ)) (by finiteness)

Depends on / 依赖: ENNReal, ENNReal.toReal_pos, NeZero, NeZero.ne, Set.univ, finiteness, toReal_pos
-/
theorem measureReal_univ_pos [IsFiniteMeasure μ] [NeZero μ] : 0 < μ.real Set.univ :=
  ENNReal.toReal_pos (NeZero.ne (μ Set.univ)) (by finiteness)

/--
theorem `measureReal_univ_ne_zero` / 定理 `measureReal_univ_ne_zero`

English:
theorem measureReal_univ_ne_zero
  given: [IsFiniteMeasure μ] [NeZero μ]
  statement: μ.real Set.univ != 0
  proof: measureReal_univ_pos.ne'

@[simp]

中文:
定理 measure实数_univ_ne_zero
  条件: [是有限测度 μ] [NeZero μ]
  结论: μ.real 集合.univ != 0
  证明: measureReal_univ_pos.ne'

@[simp]

Depends on / 依赖: measureReal_univ_pos, measureReal_univ_pos.ne
-/
theorem measureReal_univ_ne_zero [IsFiniteMeasure μ] [NeZero μ] : μ.real Set.univ != 0 :=
  measureReal_univ_pos.ne'

@[simp]
/--
theorem `ofReal_measureReal` / 定理 `ofReal_measureReal`

English:
theorem ofReal_measureReal
  given: (h : μ s != ∞ := by finiteness)
  statement: ENNReal.ofReal (μ.real s) = μ s
  proof: by
  simp [measureReal_def, h]

中文:
定理 of实数_measure实数
  条件: (h : μ s != ∞ := by finiteness)
  结论: 广义非负实数.of实数 (μ.real s) = μ s
  证明: by
  simp [measureReal_def, h]

Depends on / 依赖: ENNReal, ENNReal.ofReal, finiteness, measureReal_def, ofReal
-/
theorem ofReal_measureReal (h : μ s != ∞ := by finiteness) : ENNReal.ofReal (μ.real s) = μ s := by
  simp [measureReal_def, h]

/--
theorem `nonempty_of_measureReal_ne_zero` / 定理 `nonempty_of_measureReal_ne_zero`

English:
theorem nonempty_of_measureReal_ne_zero
  given: (h : μ.real s != 0)
  statement: s.Nonempty
  proof: nonempty_iff_ne_empty.2 fun h' => h h'.symm ▸ measureReal_empty

中文:
定理 nonempty_of_measure实数_ne_zero
  条件: (h : μ.real s != 0)
  结论: s.非空
  证明: nonempty_iff_ne_empty.2 fun h' => h h'.symm ▸ measureReal_empty

Depends on / 依赖: measureReal_empty, nonempty_iff_ne_empty
-/
theorem nonempty_of_measureReal_ne_zero (h : μ.real s != 0) : s.Nonempty :=
nonempty_iff_ne_empty.2 fun h' => h h'.symm ▸ measureReal_empty

/--
theorem `measureReal_ennreal_smul_apply` / 定理 `measureReal_ennreal_smul_apply`

English:
theorem measureReal_ennreal_smul_apply
  given: (c : Real>=0∞)
  proof: by
  simp [Measure.real]

中文:
定理 measure实数_ennreal_smul_apply
  条件: (c : 实数>=0∞)
  证明: by
  simp [Measure.real]
-/
@[simp] theorem measureReal_ennreal_smul_apply (c : Real>=0∞) :
    (c • μ).real s = c.toReal * μ.real s := by
  simp [Measure.real]

/--
theorem `measureReal_nnreal_smul_apply` / 定理 `measureReal_nnreal_smul_apply`

English:
theorem measureReal_nnreal_smul_apply
  given: (c : Real>=0)
  proof: by
  simp [measureReal_def]

中文:
定理 measure实数_nnreal_smul_apply
  条件: (c : 实数>=0)
  证明: by
  simp [measureReal_def]
-/
@[simp] theorem measureReal_nnreal_smul_apply (c : Real>=0) :
    (c • μ).real s = c * μ.real s := by
  simp [measureReal_def]

/--
theorem `map_measureReal_apply_of_aemeasurable` / 定理 `map_measureReal_apply_of_aemeasurable`

English:
theorem map_measureReal_apply_of_aemeasurable
  statement: [MeasurableSpace β] {f : α -> β}
  proof: by
  simp_rw [measureReal_def, map_apply_of_aemeasurable hf hs]

中文:
定理 map_measure实数_apply_of_aemeasurable
  结论: [可测空间 β] {f : α -> β}
  证明: by
  simp_rw [measureReal_def, map_apply_of_aemeasurable hf hs]

Depends on / 依赖: map_apply_of_aemeasurable, measureReal_def, simp_rw
-/
theorem map_measureReal_apply_of_aemeasurable [MeasurableSpace β] {f : α -> β}
    (hf : AEMeasurable f μ) {s : Set β} (hs : MeasurableSet s) :
    (μ.map f).real s = μ.real (f ⁻¹' s) := by
  simp_rw [measureReal_def, map_apply_of_aemeasurable hf hs]

/--
theorem `map_measureReal_apply` / 定理 `map_measureReal_apply`

English:
theorem map_measureReal_apply
  statement: [MeasurableSpace β] {f : α -> β} (hf : Measurable f)
  proof: map_measureReal_apply_of_aemeasurable hf.aemeasurable hs

中文:
定理 map_measure实数_apply
  结论: [可测空间 β] {f : α -> β} (hf : 可测 f)
  证明: map_measureReal_apply_of_aemeasurable hf.aemeasurable hs

Depends on / 依赖: aemeasurable, hf.aemeasurable, map_measureReal_apply_of_aemeasurable
-/
theorem map_measureReal_apply [MeasurableSpace β] {f : α -> β} (hf : Measurable f)
    {s : Set β} (hs : MeasurableSet s) : (μ.map f).real s = μ.real (f ⁻¹' s) :=
  map_measureReal_apply_of_aemeasurable hf.aemeasurable hs

/--
theorem `measureReal_mono` / 定理 `measureReal_mono`

English:
theorem measureReal_mono
  given: (h : s₁ subseteq s₂) (h₂ : μ s₂ != ∞ := by finiteness)
  proof: ENNReal.toReal_mono h₂ (measure_mono h)

中文:
定理 measure实数_mono
  条件: (h : s₁ subseteq s₂) (h₂ : μ s₂ != ∞ := by finiteness)
  证明: ENNReal.toReal_mono h₂ (measure_mono h)
-/
@[gcongr] theorem measureReal_mono (h : s₁ subseteq s₂) (h₂ : μ s₂ != ∞ := by finiteness) :
    μ.real s₁ <= μ.real s₂ :=
  ENNReal.toReal_mono h₂ (measure_mono h)

/--
theorem `measureReal_eq_measureReal_iff` / 定理 `measureReal_eq_measureReal_iff`

English:
theorem measureReal_eq_measureReal_iff
  statement: {m : MeasurableSpace β} {ν : Measure β} {t : Set β}
  proof: by
  simp [measureReal_def, ENNReal.toReal_eq_toReal_iff' h₁ h₂]

中文:
定理 measure实数_eq_measure实数_iff
  结论: {m : 可测空间 β} {ν : 测度 β} {t : 集合 β}
  证明: by
  simp [measureReal_def, ENNReal.toReal_eq_toReal_iff' h₁ h₂]

Depends on / 依赖: ENNReal, ENNReal.toReal_eq_toReal_iff, finiteness, measureReal_def, toReal_eq_toReal_iff
-/
theorem measureReal_eq_measureReal_iff {m : MeasurableSpace β} {ν : Measure β} {t : Set β}
    (h₁ : μ s != ∞ := by finiteness) (h₂ : ν t != ∞ := by finiteness) :
    μ.real s = ν.real t ↔ μ s = ν t := by
  simp [measureReal_def, ENNReal.toReal_eq_toReal_iff' h₁ h₂]

/--
theorem `measureReal_restrict_apply₀` / 定理 `measureReal_restrict_apply₀`

English:
theorem measureReal_restrict_apply₀
  given: (ht : NullMeasurableSet t (μ.restrict s))
  proof: by
  simp only [measureReal_def, restrict_apply₀ ht]

@[simp]

中文:
定理 measure实数_restrict_apply₀
  条件: (ht : NullMeasurableSet t (μ.restrict s))
  证明: by
  simp only [measureReal_def, restrict_apply₀ ht]

@[simp]

Depends on / 依赖: measureReal_def
-/
theorem measureReal_restrict_apply₀ (ht : NullMeasurableSet t (μ.restrict s)) :
    (μ.restrict s).real t = μ.real (t inter s) := by
  simp only [measureReal_def, restrict_apply₀ ht]

@[simp]
/--
theorem `measureReal_restrict_apply` / 定理 `measureReal_restrict_apply`

English:
theorem measureReal_restrict_apply
  given: (ht : MeasurableSet t)
  proof: by
  simp only [measureReal_def, restrict_apply ht]

中文:
定理 measure实数_restrict_apply
  条件: (ht : 可测集 t)
  证明: by
  simp only [measureReal_def, restrict_apply ht]

Depends on / 依赖: measureReal_def, restrict_apply
-/
theorem measureReal_restrict_apply (ht : MeasurableSet t) :
    (μ.restrict s).real t = μ.real (t inter s) := by
  simp only [measureReal_def, restrict_apply ht]

/--
theorem `measureReal_restrict_apply_univ` / 定理 `measureReal_restrict_apply_univ`

English:
theorem measureReal_restrict_apply_univ
  given: (s : Set α)
  statement: (μ.restrict s).real univ = μ.real s
  proof: by
  simp

@[simp]

中文:
定理 measure实数_restrict_apply_univ
  条件: (s : 集合 α)
  结论: (μ.restrict s).real univ = μ.real s
  证明: by
  simp

@[simp]
-/
theorem measureReal_restrict_apply_univ (s : Set α) : (μ.restrict s).real univ = μ.real s := by
  simp

@[simp]
/--
theorem `measureReal_restrict_apply'` / 定理 `measureReal_restrict_apply'`

English:
theorem measureReal_restrict_apply'
  given: (hs : MeasurableSet s)
  proof: by
  simp only [measureReal_def, restrict_apply' hs]

中文:
定理 measure实数_restrict_apply'
  条件: (hs : 可测集 s)
  证明: by
  simp only [measureReal_def, restrict_apply' hs]

Depends on / 依赖: measureReal_def, restrict_apply
-/
theorem measureReal_restrict_apply' (hs : MeasurableSet s) :
    (μ.restrict s).real t = μ.real (t inter s) := by
  simp only [measureReal_def, restrict_apply' hs]

/--
theorem `measureReal_restrict_apply₀'` / 定理 `measureReal_restrict_apply₀'`

English:
theorem measureReal_restrict_apply₀'
  given: (hs : NullMeasurableSet s μ)
  statement: μ.restrict s t = μ (t inter s)
  proof: by
  simp only [restrict_apply₀' hs]

@[simp]

中文:
定理 measure实数_restrict_apply₀'
  条件: (hs : NullMeasurableSet s μ)
  结论: μ.restrict s t = μ (t inter s)
  证明: by
  simp only [restrict_apply₀' hs]

@[simp]
-/
theorem measureReal_restrict_apply₀' (hs : NullMeasurableSet s μ) : μ.restrict s t = μ (t inter s) := by
  simp only [restrict_apply₀' hs]

@[simp]
/--
theorem `measureReal_restrict_apply_self` / 定理 `measureReal_restrict_apply_self`

English:
theorem measureReal_restrict_apply_self
  given: (s : Set α)
  statement: (μ.restrict s).real s = μ.real s
  proof: by
  simp [measureReal_def]

中文:
定理 measure实数_restrict_apply_self
  条件: (s : 集合 α)
  结论: (μ.restrict s).real s = μ.real s
  证明: by
  simp [measureReal_def]

Depends on / 依赖: measureReal_def
-/
theorem measureReal_restrict_apply_self (s : Set α) : (μ.restrict s).real s = μ.real s := by
  simp [measureReal_def]

/--
theorem `measureReal_mono_null` / 定理 `measureReal_mono_null`

English:
theorem measureReal_mono_null
  given: (h : s₁ subseteq s₂) (h₂ : μ.real s₂ = 0) (h'₂ : μ s₂ != ∞ := by finiteness)
  proof: by
  rw [measureReal_eq_zero_iff h'₂] at h₂
  simp [Measure.real, measure_mono_null h h₂]

中文:
定理 measure实数_mono_null
  条件: (h : s₁ subseteq s₂) (h₂ : μ.real s₂ = 0) (h'₂ : μ s₂ != ∞ := by finiteness)
  证明: by
  rw [measureReal_eq_zero_iff h'₂] at h₂
  simp [Measure.real, measure_mono_null h h₂]

Depends on / 依赖: Measure, Measure.real, finiteness, measureReal_eq_zero_iff, measure_mono_null
-/
theorem measureReal_mono_null (h : s₁ subseteq s₂) (h₂ : μ.real s₂ = 0) (h'₂ : μ s₂ != ∞ := by finiteness) :
    μ.real s₁ = 0 := by
  rw [measureReal_eq_zero_iff h'₂] at h₂
  simp [Measure.real, measure_mono_null h h₂]

/--
theorem `measureReal_le_measureReal_union_left` / 定理 `measureReal_le_measureReal_union_left`

English:
theorem measureReal_le_measureReal_union_left
  given: (h : μ t != ∞ := by finiteness)
  proof: by
  rcases eq_top_or_lt_top (μ s) with hs | hs
  · simp [Measure.real, hs]
  · exact measureReal_mono subset_union_left (measure_union_lt_top hs h.lt_top).ne

中文:
定理 measure实数_le_measure实数_union_left
  条件: (h : μ t != ∞ := by finiteness)
  证明: by
  rcases eq_top_or_lt_top (μ s) with hs | hs
  · simp [Measure.real, hs]
  · exact measureReal_mono subset_union_left (measure_union_lt_top hs h.lt_top).ne

Depends on / 依赖: Measure, Measure.real, eq_top_or_lt_top, finiteness, h.lt_top, lt_top, measureReal_mono, measure_union_lt_top, subset_union_left
-/
theorem measureReal_le_measureReal_union_left (h : μ t != ∞ := by finiteness) :
    μ.real s <= μ.real (s union t) := by
  rcases eq_top_or_lt_top (μ s) with hs | hs
  · simp [Measure.real, hs]
  · exact measureReal_mono subset_union_left (measure_union_lt_top hs h.lt_top).ne

/--
theorem `measureReal_le_measureReal_union_right` / 定理 `measureReal_le_measureReal_union_right`

English:
theorem measureReal_le_measureReal_union_right
  given: (h : μ s != ∞ := by finiteness)
  proof: by
  rw [union_comm]
  exact measureReal_le_measureReal_union_left h

中文:
定理 measure实数_le_measure实数_union_right
  条件: (h : μ s != ∞ := by finiteness)
  证明: by
  rw [union_comm]
  exact measureReal_le_measureReal_union_left h

Depends on / 依赖: finiteness, measureReal_le_measureReal_union_left, union_comm
-/
theorem measureReal_le_measureReal_union_right (h : μ s != ∞ := by finiteness) :
    μ.real t <= μ.real (s union t) := by
  rw [union_comm]
  exact measureReal_le_measureReal_union_left h

/--
theorem `measureReal_union_le` / 定理 `measureReal_union_le`

English:
theorem measureReal_union_le
  given: (s₁ s₂ : Set α)
  statement: μ.real (s₁ union s₂) <= μ.real s₁ + μ.real s₂
  proof: by
  rcases eq_top_or_lt_top (μ (s₁ union s₂)) with h | h
  · simp only [Measure.real, h, ENNReal.toReal_top]
    exact add_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
  · have A : μ s₁ != ∞ := measure_ne_top_of_subset subset_union_left h.ne
    have B : μ s₂ != ∞ := measure_ne_top_of_subset 

中文:
定理 measure实数_union_le
  条件: (s₁ s₂ : 集合 α)
  结论: μ.real (s₁ union s₂) <= μ.real s₁ + μ.real s₂
  证明: by
  rcases eq_top_or_lt_top (μ (s₁ union s₂)) with h | h
  · simp only [Measure.real, h, ENNReal.toReal_top]
    exact add_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
  · have A : μ s₁ != ∞ := measure_ne_top_of_subset subset_union_left h.ne
    have B : μ s₂ != ∞ := measure_ne_top_of_subset 

Depends on / 依赖: ENNReal, ENNReal.toReal_add, ENNReal.toReal_mono, ENNReal.toReal_nonneg, ENNReal.toReal_top, Measure, Measure.real, add_nonneg, eq_top_or_lt_top, h.ne, measure_ne_top_of_subset, measure_union_le, subset_union_left, subset_union_right, toReal_add, toReal_mono, toReal_nonneg, toReal_top
-/
theorem measureReal_union_le (s₁ s₂ : Set α) : μ.real (s₁ union s₂) <= μ.real s₁ + μ.real s₂ := by
  rcases eq_top_or_lt_top (μ (s₁ union s₂)) with h | h
  · simp only [Measure.real, h, ENNReal.toReal_top]
    exact add_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
  · have A : μ s₁ != ∞ := measure_ne_top_of_subset subset_union_left h.ne
    have B : μ s₂ != ∞ := measure_ne_top_of_subset subset_union_right h.ne
    simp only [Measure.real, ← ENNReal.toReal_add A B]
    exact ENNReal.toReal_mono (by simp [A, B]) (measure_union_le _ _)

/--
theorem `measureReal_biUnion_finset_le` / 定理 `measureReal_biUnion_finset_le`

English:
theorem measureReal_biUnion_finset_le
  given: (s : Finset β) (f : β -> Set α)
  proof: by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert _ _ hx IH =>
    simp only [hx, Finset.mem_insert, iUnion_iUnion_eq_or_left, not_false_eq_true,
      Finset.sum_insert]
    exact (measureReal_union_le _ _).trans (by gcongr)

中文:
定理 measure实数_biUnion_finset_le
  条件: (s : 有限集 β) (f : β -> 集合 α)
  证明: by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert _ _ hx IH =>
    simp only [hx, Finset.mem_insert, iUnion_iUnion_eq_or_left, not_false_eq_true,
      Finset.sum_insert]
    exact (measureReal_union_le _ _).trans (by gcongr)

Depends on / 依赖: Finset, Finset.induction_on, Finset.mem_insert, Finset.sum_insert, classical, iUnion_iUnion_eq_or_left, induction_on, insert, measureReal_union_le, mem_insert, not_false_eq_true, sum_insert
-/
theorem measureReal_biUnion_finset_le (s : Finset β) (f : β -> Set α) :
    μ.real (⋃ b in s, f b) <= ∑ p in s, μ.real (f p) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert _ _ hx IH =>
    simp only [hx, Finset.mem_insert, iUnion_iUnion_eq_or_left, not_false_eq_true,
      Finset.sum_insert]
    exact (measureReal_union_le _ _).trans (by gcongr)

/--
theorem `measureReal_iUnion_fintype_le` / 定理 `measureReal_iUnion_fintype_le`

English:
theorem measureReal_iUnion_fintype_le
  given: [Fintype β] (f : β -> Set α)
  proof: by
  convert! measureReal_biUnion_finset_le Finset.univ f
  simp

中文:
定理 measure实数_iUnion_fintype_le
  条件: [有限类型 β] (f : β -> 集合 α)
  证明: by
  convert! measureReal_biUnion_finset_le Finset.univ f
  simp

Depends on / 依赖: Finset, Finset.univ, convert, measureReal_biUnion_finset_le
-/
theorem measureReal_iUnion_fintype_le [Fintype β] (f : β -> Set α) :
    μ.real (⋃ b, f b) <= ∑ p, μ.real (f p) := by
  convert! measureReal_biUnion_finset_le Finset.univ f
  simp

/--
theorem `measureReal_iUnion_fintype` / 定理 `measureReal_iUnion_fintype`

English:
theorem measureReal_iUnion_fintype
  statement: [Fintype β] {f : β -> Set α} (hn : Pairwise (Disjoint on f))
  proof: by
  simp_rw [measureReal_def, measure_iUnion hn h, tsum_fintype,
    ENNReal.toReal_sum (fun i _hi => h' i)]

中文:
定理 measure实数_iUnion_fintype
  结论: [有限类型 β] {f : β -> 集合 α} (hn : 两两 (Disjoint on f))
  证明: by
  simp_rw [measureReal_def, measure_iUnion hn h, tsum_fintype,
    ENNReal.toReal_sum (fun i _hi => h' i)]

Depends on / 依赖: ENNReal, ENNReal.toReal_sum, finiteness, measureReal_def, measure_iUnion, simp_rw, toReal_sum, tsum_fintype
-/
theorem measureReal_iUnion_fintype [Fintype β] {f : β -> Set α} (hn : Pairwise (Disjoint on f))
    (h : forall i, MeasurableSet (f i)) (h' : forall i, μ (f i) != ∞ := by finiteness) :
    μ.real (⋃ b, f b) = ∑ p, μ.real (f p) := by
  simp_rw [measureReal_def, measure_iUnion hn h, tsum_fintype,
    ENNReal.toReal_sum (fun i _hi => h' i)]

/--
theorem `measureReal_union_null` / 定理 `measureReal_union_null`

English:
theorem measureReal_union_null
  given: (h₁ : μ.real s₁ = 0) (h₂ : μ.real s₂ = 0)
  proof: le_antisymm ((measureReal_union_le s₁ s₂).trans (by simp [h₁, h₂])) measureReal_nonneg

@[simp]

中文:
定理 measure实数_union_null
  条件: (h₁ : μ.real s₁ = 0) (h₂ : μ.real s₂ = 0)
  证明: le_antisymm ((measureReal_union_le s₁ s₂).trans (by simp [h₁, h₂])) measureReal_nonneg

@[simp]

Depends on / 依赖: le_antisymm, measureReal_nonneg, measureReal_union_le
-/
theorem measureReal_union_null (h₁ : μ.real s₁ = 0) (h₂ : μ.real s₂ = 0) :
    μ.real (s₁ union s₂) = 0 :=
  le_antisymm ((measureReal_union_le s₁ s₂).trans (by simp [h₁, h₂])) measureReal_nonneg

@[simp]
/--
theorem `measureReal_union_null_iff` / 定理 `measureReal_union_null_iff`

English:
theorem measureReal_union_null_iff
  proof: ⟨fun h => ⟨measureReal_mono_null subset_union_left h (by finiteness),
      measureReal_mono_null subset_union_right h (by finiteness)⟩,
  fun h => measureReal_union_null h.1 h.2⟩

中文:
定理 measure实数_union_null_iff
  证明: ⟨fun h => ⟨measureReal_mono_null subset_union_left h (by finiteness),
      measureReal_mono_null subset_union_right h (by finiteness)⟩,
  fun h => measureReal_union_null h.1 h.2⟩

Depends on / 依赖: finiteness, measureReal_mono_null, measureReal_union_null, subset_union_left, subset_union_right
-/
theorem measureReal_union_null_iff
    (h₁ : μ s₁ != ∞ := by finiteness) (h₂ : μ s₂ != ∞ := by finiteness) :
    μ.real (s₁ union s₂) = 0 ↔ μ.real s₁ = 0 ∧ μ.real s₂ = 0 :=
  ⟨fun h => ⟨measureReal_mono_null subset_union_left h (by finiteness),
      measureReal_mono_null subset_union_right h (by finiteness)⟩,
  fun h => measureReal_union_null h.1 h.2⟩

/--
theorem `measureReal_congr` / 定理 `measureReal_congr`

English:
theorem measureReal_congr
  given: (H : s =ᵐ[μ] t)
  statement: μ.real s = μ.real t
  proof: by
  simp [Measure.real, measure_congr H]

中文:
定理 measure实数_congr
  条件: (H : s =ᵐ[μ] t)
  结论: μ.real s = μ.real t
  证明: by
  simp [Measure.real, measure_congr H]

Depends on / 依赖: Measure, Measure.real, measure_congr
-/
theorem measureReal_congr (H : s =ᵐ[μ] t) : μ.real s = μ.real t := by
  simp [Measure.real, measure_congr H]

/--
theorem `measureReal_inter_add_sdiff₀` / 定理 `measureReal_inter_add_sdiff₀`

English:
theorem measureReal_inter_add_sdiff₀
  statement: (ht : NullMeasurableSet t μ)
  proof: by
  simp only [measureReal_def]
  rw [← ENNReal.toReal_add]; rw [measure_inter_add_sdiff₀ s ht]
  · exact measure_ne_top_of_subset inter_subset_left h
  · exact measure_ne_top_of_subset sdiff_subset h

@[deprecated (since := "2026-06-03")]
alias measureReal_inter_add_diff₀ := measureReal_inter_add_

中文:
定理 measure实数_inter_add_sdiff₀
  结论: (ht : NullMeasurableSet t μ)
  证明: by
  simp only [measureReal_def]
  rw [← ENNReal.toReal_add]; rw [measure_inter_add_sdiff₀ s ht]
  · exact measure_ne_top_of_subset inter_subset_left h
  · exact measure_ne_top_of_subset sdiff_subset h

@[deprecated (since := "2026-06-03")]
alias measureReal_inter_add_diff₀ := measureReal_inter_add_

Depends on / 依赖: ENNReal, ENNReal.toReal_add, finiteness, inter_subset_left, measureReal_def, measure_ne_top_of_subset, sdiff_subset, toReal_add
-/
theorem measureReal_inter_add_sdiff₀ (ht : NullMeasurableSet t μ)
    (h : μ s != ∞ := by finiteness) :
    μ.real (s inter t) + μ.real (s \ t) = μ.real s := by
  simp only [measureReal_def]
  rw [← ENNReal.toReal_add]; rw [measure_inter_add_sdiff₀ s ht]
  · exact measure_ne_top_of_subset inter_subset_left h
  · exact measure_ne_top_of_subset sdiff_subset h

@[deprecated (since := "2026-06-03")]
alias measureReal_inter_add_diff₀ := measureReal_inter_add_sdiff₀

/--
theorem `measureReal_union_add_inter₀` / 定理 `measureReal_union_add_inter₀`

English:
theorem measureReal_union_add_inter₀
  statement: (ht : NullMeasurableSet t μ)
  proof: by
  have : μ (s union t) != ∞ :=
    ((measure_union_le _ _).trans_lt (ENNReal.add_lt_top.2 ⟨h₁.lt_top, h₂.lt_top⟩ )).ne
  rw [← measureReal_inter_add_sdiff₀ ht this]; rw [Set.union_inter_cancel_right]; rw [union_sdiff_right]; rw [← measureReal_inter_add_sdiff₀ ht h₁]
  ac_rfl

中文:
定理 measure实数_union_add_inter₀
  结论: (ht : NullMeasurableSet t μ)
  证明: by
  have : μ (s union t) != ∞ :=
    ((measure_union_le _ _).trans_lt (ENNReal.add_lt_top.2 ⟨h₁.lt_top, h₂.lt_top⟩ )).ne
  rw [← measureReal_inter_add_sdiff₀ ht this]; rw [Set.union_inter_cancel_right]; rw [union_sdiff_right]; rw [← measureReal_inter_add_sdiff₀ ht h₁]
  ac_rfl

Depends on / 依赖: ENNReal, ENNReal.add_lt_top, Set.union_inter_cancel_right, add_lt_top, finiteness, lt_top, measure_union_le, trans_lt, union_inter_cancel_right, union_sdiff_right
-/
theorem measureReal_union_add_inter₀ (ht : NullMeasurableSet t μ)
    (h₁ : μ s != ∞ := by finiteness) (h₂ : μ t != ∞ := by finiteness) :
    μ.real (s union t) + μ.real (s inter t) = μ.real s + μ.real t := by
  have : μ (s union t) != ∞ :=
    ((measure_union_le _ _).trans_lt (ENNReal.add_lt_top.2 ⟨h₁.lt_top, h₂.lt_top⟩ )).ne
  rw [← measureReal_inter_add_sdiff₀ ht this]; rw [Set.union_inter_cancel_right]; rw [union_sdiff_right]; rw [← measureReal_inter_add_sdiff₀ ht h₁]
  ac_rfl

/--
theorem `measureReal_union_add_inter₀'` / 定理 `measureReal_union_add_inter₀'`

English:
theorem measureReal_union_add_inter₀'
  statement: (hs : NullMeasurableSet s μ)
  proof: by
  rw [union_comm]; rw [inter_comm]; rw [measureReal_union_add_inter₀ hs h₂ h₁]; rw [add_comm]

中文:
定理 measure实数_union_add_inter₀'
  结论: (hs : NullMeasurableSet s μ)
  证明: by
  rw [union_comm]; rw [inter_comm]; rw [measureReal_union_add_inter₀ hs h₂ h₁]; rw [add_comm]

Depends on / 依赖: add_comm, finiteness, inter_comm, union_comm
-/
theorem measureReal_union_add_inter₀' (hs : NullMeasurableSet s μ)
    (h₁ : μ s != ∞ := by finiteness) (h₂ : μ t != ∞ := by finiteness) :
    μ.real (s union t) + μ.real (s inter t) = μ.real s + μ.real t := by
  rw [union_comm]; rw [inter_comm]; rw [measureReal_union_add_inter₀ hs h₂ h₁]; rw [add_comm]

/--
theorem `measureReal_union₀` / 定理 `measureReal_union₀`

English:
theorem measureReal_union₀
  statement: (ht : NullMeasurableSet t μ) (hd : AEDisjoint μ s t)
  proof: by
  simp only [Measure.real]
  rw [measure_union₀ ht hd]; rw [ENNReal.toReal_add h₁ h₂]

中文:
定理 measure实数_union₀
  结论: (ht : NullMeasurableSet t μ) (hd : AEDisjoint μ s t)
  证明: by
  simp only [Measure.real]
  rw [measure_union₀ ht hd]; rw [ENNReal.toReal_add h₁ h₂]

Depends on / 依赖: ENNReal, ENNReal.toReal_add, Measure, Measure.real, finiteness, toReal_add
-/
theorem measureReal_union₀ (ht : NullMeasurableSet t μ) (hd : AEDisjoint μ s t)
    (h₁ : μ s != ∞ := by finiteness) (h₂ : μ t != ∞ := by finiteness) :
    μ.real (s union t) = μ.real s + μ.real t := by
  simp only [Measure.real]
  rw [measure_union₀ ht hd]; rw [ENNReal.toReal_add h₁ h₂]

/--
theorem `measureReal_union₀'` / 定理 `measureReal_union₀'`

English:
theorem measureReal_union₀'
  statement: (hs : NullMeasurableSet s μ) (hd : AEDisjoint μ s t)
  proof: by
  rw [union_comm]; rw [measureReal_union₀ hs (AEDisjoint.symm hd) h₂ h₁]; rw [add_comm]

中文:
定理 measure实数_union₀'
  结论: (hs : NullMeasurableSet s μ) (hd : AEDisjoint μ s t)
  证明: by
  rw [union_comm]; rw [measureReal_union₀ hs (AEDisjoint.symm hd) h₂ h₁]; rw [add_comm]

Depends on / 依赖: AEDisjoint, AEDisjoint.symm, add_comm, finiteness, union_comm
-/
theorem measureReal_union₀' (hs : NullMeasurableSet s μ) (hd : AEDisjoint μ s t)
    (h₁ : μ s != ∞ := by finiteness) (h₂ : μ t != ∞ := by finiteness) :
    μ.real (s union t) = μ.real s + μ.real t := by
  rw [union_comm]; rw [measureReal_union₀ hs (AEDisjoint.symm hd) h₂ h₁]; rw [add_comm]

/--
theorem `measureReal_add_measureReal_compl₀` / 定理 `measureReal_add_measureReal_compl₀`

English:
theorem measureReal_add_measureReal_compl₀
  given: [IsFiniteMeasure μ] (hs : NullMeasurableSet s μ)
  proof: by
  rw [← measureReal_union₀' hs aedisjoint_compl_right]; rw [union_compl_self]

中文:
定理 measure实数_add_measure实数_compl₀
  条件: [是有限测度 μ] (hs : NullMeasurableSet s μ)
  证明: by
  rw [← measureReal_union₀' hs aedisjoint_compl_right]; rw [union_compl_self]

Depends on / 依赖: aedisjoint_compl_right, union_compl_self
-/
theorem measureReal_add_measureReal_compl₀ [IsFiniteMeasure μ] (hs : NullMeasurableSet s μ) :
    μ.real s + μ.real sᶜ = μ.real univ := by
  rw [← measureReal_union₀' hs aedisjoint_compl_right]; rw [union_compl_self]

/--
theorem `measureReal_add_measureReal_compl` / 定理 `measureReal_add_measureReal_compl`

English:
theorem measureReal_add_measureReal_compl
  given: [IsFiniteMeasure μ] (h : MeasurableSet s)
  proof: measureReal_add_measureReal_compl₀ h.nullMeasurableSet

中文:
定理 measure实数_add_measure实数_compl
  条件: [是有限测度 μ] (h : 可测集 s)
  证明: measureReal_add_measureReal_compl₀ h.nullMeasurableSet

Depends on / 依赖: h.nullMeasurableSet, nullMeasurableSet
-/
theorem measureReal_add_measureReal_compl [IsFiniteMeasure μ] (h : MeasurableSet s) :
    μ.real s + μ.real sᶜ = μ.real univ :=
  measureReal_add_measureReal_compl₀ h.nullMeasurableSet

/--
theorem `measureReal_union` / 定理 `measureReal_union`

English:
theorem measureReal_union
  statement: (hd : Disjoint s₁ s₂) (h : MeasurableSet s₂)
  proof: measureReal_union₀ h.nullMeasurableSet hd.aedisjoint h₁ h₂

中文:
定理 measure实数_union
  结论: (hd : Disjoint s₁ s₂) (h : 可测集 s₂)
  证明: measureReal_union₀ h.nullMeasurableSet hd.aedisjoint h₁ h₂

Depends on / 依赖: aedisjoint, finiteness, h.nullMeasurableSet, hd.aedisjoint, nullMeasurableSet
-/
theorem measureReal_union (hd : Disjoint s₁ s₂) (h : MeasurableSet s₂)
    (h₁ : μ s₁ != ∞ := by finiteness) (h₂ : μ s₂ != ∞ := by finiteness) :
    μ.real (s₁ union s₂) = μ.real s₁ + μ.real s₂ :=
  measureReal_union₀ h.nullMeasurableSet hd.aedisjoint h₁ h₂

/--
theorem `measureReal_union'` / 定理 `measureReal_union'`

English:
theorem measureReal_union'
  statement: (hd : Disjoint s₁ s₂) (h : MeasurableSet s₁)
  proof: measureReal_union₀' h.nullMeasurableSet hd.aedisjoint h₁ h₂

中文:
定理 measure实数_union'
  结论: (hd : Disjoint s₁ s₂) (h : 可测集 s₁)
  证明: measureReal_union₀' h.nullMeasurableSet hd.aedisjoint h₁ h₂

Depends on / 依赖: aedisjoint, finiteness, h.nullMeasurableSet, hd.aedisjoint, nullMeasurableSet
-/
theorem measureReal_union' (hd : Disjoint s₁ s₂) (h : MeasurableSet s₁)
    (h₁ : μ s₁ != ∞ := by finiteness) (h₂ : μ s₂ != ∞ := by finiteness) :
    μ.real (s₁ union s₂) = μ.real s₁ + μ.real s₂ :=
  measureReal_union₀' h.nullMeasurableSet hd.aedisjoint h₁ h₂

/--
theorem `measureReal_inter_add_sdiff` / 定理 `measureReal_inter_add_sdiff`

English:
theorem measureReal_inter_add_sdiff
  statement: (ht : MeasurableSet t)
  proof: by
  simp only [Measure.real]
  rw [← ENNReal.toReal_add]; rw [measure_inter_add_sdiff _ ht]
  · exact measure_ne_top_of_subset inter_subset_left h
  · exact measure_ne_top_of_subset sdiff_subset h

@[deprecated (since := "2026-06-03")]
alias measureReal_inter_add_diff := measureReal_inter_add_sdiff

中文:
定理 measure实数_inter_add_sdiff
  结论: (ht : 可测集 t)
  证明: by
  simp only [Measure.real]
  rw [← ENNReal.toReal_add]; rw [measure_inter_add_sdiff _ ht]
  · exact measure_ne_top_of_subset inter_subset_left h
  · exact measure_ne_top_of_subset sdiff_subset h

@[deprecated (since := "2026-06-03")]
alias measureReal_inter_add_diff := measureReal_inter_add_sdiff

Depends on / 依赖: ENNReal, ENNReal.toReal_add, Measure, Measure.real, finiteness, inter_subset_left, measure_inter_add_sdiff, measure_ne_top_of_subset, sdiff_subset, toReal_add
-/
theorem measureReal_inter_add_sdiff (ht : MeasurableSet t)
    (h : μ s != ∞ := by finiteness) :
    μ.real (s inter t) + μ.real (s \ t) = μ.real s := by
  simp only [Measure.real]
  rw [← ENNReal.toReal_add]; rw [measure_inter_add_sdiff _ ht]
  · exact measure_ne_top_of_subset inter_subset_left h
  · exact measure_ne_top_of_subset sdiff_subset h

@[deprecated (since := "2026-06-03")]
alias measureReal_inter_add_diff := measureReal_inter_add_sdiff

/--
theorem `measureReal_sdiff_add_inter` / 定理 `measureReal_sdiff_add_inter`

English:
theorem measureReal_sdiff_add_inter
  statement: (ht : MeasurableSet t)
  proof: (add_comm _ _).trans (measureReal_inter_add_sdiff ht h)

@[deprecated (since := "2026-06-03")]
alias measureReal_diff_add_inter := measureReal_sdiff_add_inter

中文:
定理 measure实数_sdiff_add_inter
  结论: (ht : 可测集 t)
  证明: (add_comm _ _).trans (measureReal_inter_add_sdiff ht h)

@[deprecated (since := "2026-06-03")]
alias measureReal_diff_add_inter := measureReal_sdiff_add_inter

Depends on / 依赖: add_comm, finiteness, measureReal_inter_add_sdiff
-/
theorem measureReal_sdiff_add_inter (ht : MeasurableSet t)
    (h : μ s != ∞ := by finiteness) :
    μ.real (s \ t) + μ.real (s inter t) = μ.real s :=
  (add_comm _ _).trans (measureReal_inter_add_sdiff ht h)

@[deprecated (since := "2026-06-03")]
alias measureReal_diff_add_inter := measureReal_sdiff_add_inter

/--
theorem `measureReal_union_add_inter` / 定理 `measureReal_union_add_inter`

English:
theorem measureReal_union_add_inter
  statement: (ht : MeasurableSet t)
  proof: measureReal_union_add_inter₀ ht.nullMeasurableSet h₁ h₂

中文:
定理 measure实数_union_add_inter
  结论: (ht : 可测集 t)
  证明: measureReal_union_add_inter₀ ht.nullMeasurableSet h₁ h₂

Depends on / 依赖: finiteness, ht.nullMeasurableSet, nullMeasurableSet
-/
theorem measureReal_union_add_inter (ht : MeasurableSet t)
    (h₁ : μ s != ∞ := by finiteness) (h₂ : μ t != ∞ := by finiteness) :
    μ.real (s union t) + μ.real (s inter t) = μ.real s + μ.real t :=
  measureReal_union_add_inter₀ ht.nullMeasurableSet h₁ h₂

/--
theorem `measureReal_union_add_inter'` / 定理 `measureReal_union_add_inter'`

English:
theorem measureReal_union_add_inter'
  statement: (hs : MeasurableSet s)
  proof: measureReal_union_add_inter₀' hs.nullMeasurableSet h₁ h₂

中文:
定理 measure实数_union_add_inter'
  结论: (hs : 可测集 s)
  证明: measureReal_union_add_inter₀' hs.nullMeasurableSet h₁ h₂

Depends on / 依赖: finiteness, hs.nullMeasurableSet, nullMeasurableSet
-/
theorem measureReal_union_add_inter' (hs : MeasurableSet s)
    (h₁ : μ s != ∞ := by finiteness) (h₂ : μ t != ∞ := by finiteness) :
    μ.real (s union t) + μ.real (s inter t) = μ.real s + μ.real t :=
  measureReal_union_add_inter₀' hs.nullMeasurableSet h₁ h₂

/--
lemma `measureReal_symmDiff_eq` / 引理 `measureReal_symmDiff_eq`

English:
lemma measureReal_symmDiff_eq
  statement: (hs : MeasurableSet s) (ht : MeasurableSet t)
  proof: by
  simp only [Measure.real]
  rw [← ENNReal.toReal_add]; rw [measure_symmDiff_eq hs.nullMeasurableSet ht.nullMeasurableSet]
  · exact measure_ne_top_of_subset sdiff_subset h₁
  · exact measure_ne_top_of_subset sdiff_subset h₂

中文:
引理 measure实数_symmDiff_eq
  结论: (hs : 可测集 s) (ht : 可测集 t)
  证明: by
  simp only [Measure.real]
  rw [← ENNReal.toReal_add]; rw [measure_symmDiff_eq hs.nullMeasurableSet ht.nullMeasurableSet]
  · exact measure_ne_top_of_subset sdiff_subset h₁
  · exact measure_ne_top_of_subset sdiff_subset h₂

Depends on / 依赖: ENNReal, ENNReal.toReal_add, Measure, Measure.real, finiteness, hs.nullMeasurableSet, ht.nullMeasurableSet, measure_ne_top_of_subset, measure_symmDiff_eq, nullMeasurableSet, sdiff_subset, toReal_add
-/
lemma measureReal_symmDiff_eq (hs : MeasurableSet s) (ht : MeasurableSet t)
    (h₁ : μ s != ∞ := by finiteness) (h₂ : μ t != ∞ := by finiteness) :
    μ.real (s ∆ t) = μ.real (s \ t) + μ.real (t \ s) := by
  simp only [Measure.real]
  rw [← ENNReal.toReal_add]; rw [measure_symmDiff_eq hs.nullMeasurableSet ht.nullMeasurableSet]
  · exact measure_ne_top_of_subset sdiff_subset h₁
  · exact measure_ne_top_of_subset sdiff_subset h₂

/--
lemma `measureReal_symmDiff_le` / 引理 `measureReal_symmDiff_le`

English:
lemma measureReal_symmDiff_le
  statement: (u : Set α)
  proof: by
  rcases eq_top_or_lt_top (μ u) with hu | hu
  · simp only [measureReal_def, measure_symmDiff_eq_top h₁ hu, ENNReal.toReal_top]
    exact add_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
  · exact le_trans (measureReal_mono (symmDiff_triangle s t u)
        (measure_union_ne_top (by finiten

中文:
引理 measure实数_symmDiff_le
  结论: (u : 集合 α)
  证明: by
  rcases eq_top_or_lt_top (μ u) with hu | hu
  · simp only [measureReal_def, measure_symmDiff_eq_top h₁ hu, ENNReal.toReal_top]
    exact add_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
  · exact le_trans (measureReal_mono (symmDiff_triangle s t u)
        (measure_union_ne_top (by finiten

Depends on / 依赖: ENNReal, ENNReal.toReal_nonneg, ENNReal.toReal_top, add_nonneg, eq_top_or_lt_top, finiteness, le_trans, measureReal_def, measureReal_mono, measureReal_union_le, measure_symmDiff_eq_top, measure_union_ne_top, symmDiff_triangle, toReal_nonneg, toReal_top
-/
lemma measureReal_symmDiff_le (u : Set α)
    (h₁ : μ s != ∞ := by finiteness) (h₂ : μ t != ∞ := by finiteness) :
    μ.real (s ∆ u) <= μ.real (s ∆ t) + μ.real (t ∆ u) := by
  rcases eq_top_or_lt_top (μ u) with hu | hu
  · simp only [measureReal_def, measure_symmDiff_eq_top h₁ hu, ENNReal.toReal_top]
    exact add_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
  · exact le_trans (measureReal_mono (symmDiff_triangle s t u)
        (measure_union_ne_top (by finiteness) (by finiteness)))
      (measureReal_union_le (s ∆ t) (t ∆ u))

/--
theorem `measureReal_biUnion_finset₀` / 定理 `measureReal_biUnion_finset₀`

English:
theorem measureReal_biUnion_finset₀
  statement: {s : Finset ι} {f : ι -> Set α}
  proof: by
  simp only [measureReal_def, measure_biUnion_finset₀ hd hm, ENNReal.toReal_sum h]

中文:
定理 measure实数_biUnion_finset₀
  结论: {s : 有限集 ι} {f : ι -> 集合 α}
  证明: by
  simp only [measureReal_def, measure_biUnion_finset₀ hd hm, ENNReal.toReal_sum h]

Depends on / 依赖: ENNReal, ENNReal.toReal_sum, finiteness, measureReal_def, toReal_sum
-/
theorem measureReal_biUnion_finset₀ {s : Finset ι} {f : ι -> Set α}
    (hd : Set.Pairwise (↑s) (AEDisjoint μ on f)) (hm : forall b in s, NullMeasurableSet (f b) μ)
    (h : forall b in s, μ (f b) != ∞ := by finiteness) :
    μ.real (⋃ b in s, f b) = ∑ p in s, μ.real (f p) := by
  simp only [measureReal_def, measure_biUnion_finset₀ hd hm, ENNReal.toReal_sum h]

/--
theorem `measureReal_biUnion_finset` / 定理 `measureReal_biUnion_finset`

English:
theorem measureReal_biUnion_finset
  statement: {s : Finset ι} {f : ι -> Set α} (hd : PairwiseDisjoint (↑s) f)
  proof: measureReal_biUnion_finset₀ hd.aedisjoint (fun b hb => (hm b hb).nullMeasurableSet) h

中文:
定理 measure实数_biUnion_finset
  结论: {s : 有限集 ι} {f : ι -> 集合 α} (hd : PairwiseDisjoint (↑s) f)
  证明: measureReal_biUnion_finset₀ hd.aedisjoint (fun b hb => (hm b hb).nullMeasurableSet) h

Depends on / 依赖: aedisjoint, finiteness, hd.aedisjoint, nullMeasurableSet
-/
theorem measureReal_biUnion_finset {s : Finset ι} {f : ι -> Set α} (hd : PairwiseDisjoint (↑s) f)
    (hm : forall b in s, MeasurableSet (f b)) (h : forall b in s, μ (f b) != ∞ := by finiteness) :
    μ.real (⋃ b in s, f b) = ∑ p in s, μ.real (f p) :=
  measureReal_biUnion_finset₀ hd.aedisjoint (fun b hb => (hm b hb).nullMeasurableSet) h

/--
theorem `sum_measureReal_preimage_singleton` / 定理 `sum_measureReal_preimage_singleton`

English:
theorem sum_measureReal_preimage_singleton
  statement: (s : Finset β) {f : α -> β}
  proof: by
  simp only [measureReal_def, ← sum_measure_preimage_singleton s hf, ENNReal.toReal_sum h]

中文:
定理 sum_measure实数_preimage_singleton
  结论: (s : 有限集 β) {f : α -> β}
  证明: by
  simp only [measureReal_def, ← sum_measure_preimage_singleton s hf, ENNReal.toReal_sum h]

Depends on / 依赖: ENNReal, ENNReal.toReal_sum, finiteness, measureReal_def, sum_measure_preimage_singleton, toReal_sum
-/
theorem sum_measureReal_preimage_singleton (s : Finset β) {f : α -> β}
    (hf : forall y in s, MeasurableSet (f ⁻¹' {y})) (h : forall a in s, μ (f ⁻¹' {a}) != ∞ := by finiteness) :
    (∑ b in s, μ.real (f ⁻¹' {b})) = μ.real (f ⁻¹' s) := by
  simp only [measureReal_def, ← sum_measure_preimage_singleton s hf, ENNReal.toReal_sum h]

/--
theorem `sum_measureReal_singleton` / 定理 `sum_measureReal_singleton`

English:
theorem sum_measureReal_singleton
  statement: [MeasurableSingletonClass α] [SigmaFinite μ]
  proof: by
  simp [measureReal_def, ← ENNReal.toReal_sum (fun _ _ => ne_of_lt measure_singleton_lt_top)]

中文:
定理 sum_measure实数_singleton
  结论: [MeasurableSingleton类 α] [σ有限 μ]
  证明: by
  simp [measureReal_def, ← ENNReal.toReal_sum (fun _ _ => ne_of_lt measure_singleton_lt_top)]
-/
@[simp] theorem sum_measureReal_singleton [MeasurableSingletonClass α] [SigmaFinite μ]
    (s : Finset α) :
    (∑ b in s, μ.real {b}) = μ.real s := by
  simp [measureReal_def, ← ENNReal.toReal_sum (fun _ _ => ne_of_lt measure_singleton_lt_top)]

/--
theorem `measureReal_sdiff_null'` / 定理 `measureReal_sdiff_null'`

English:
theorem measureReal_sdiff_null'
  given: (h : μ.real (s₁ inter s₂) = 0) (h' : μ s₁ != ∞ := by finiteness)
  proof: by
  simp only [measureReal_def]
  rw [measure_sdiff_null']
  exact (measureReal_eq_zero_iff (measure_ne_top_of_subset inter_subset_left h')).1 h

@[deprecated (since := "2026-06-03")] alias measureReal_diff_null' := measureReal_sdiff_null'

中文:
定理 measure实数_sdiff_null'
  条件: (h : μ.real (s₁ inter s₂) = 0) (h' : μ s₁ != ∞ := by finiteness)
  证明: by
  simp only [measureReal_def]
  rw [measure_sdiff_null']
  exact (measureReal_eq_zero_iff (measure_ne_top_of_subset inter_subset_left h')).1 h

@[deprecated (since := "2026-06-03")] alias measureReal_diff_null' := measureReal_sdiff_null'

Depends on / 依赖: finiteness, inter_subset_left, measureReal_def, measureReal_eq_zero_iff, measure_ne_top_of_subset, measure_sdiff_null
-/
theorem measureReal_sdiff_null' (h : μ.real (s₁ inter s₂) = 0) (h' : μ s₁ != ∞ := by finiteness) :
    μ.real (s₁ \ s₂) = μ.real s₁ := by
  simp only [measureReal_def]
  rw [measure_sdiff_null']
  exact (measureReal_eq_zero_iff (measure_ne_top_of_subset inter_subset_left h')).1 h

@[deprecated (since := "2026-06-03")] alias measureReal_diff_null' := measureReal_sdiff_null'

/--
theorem `measureReal_sdiff_null` / 定理 `measureReal_sdiff_null`

English:
theorem measureReal_sdiff_null
  given: (h : μ.real s₂ = 0) (h' : μ s₂ != ∞ := by finiteness)
  proof: by
  rcases eq_top_or_lt_top (μ s₁) with H | H
  · simp [measureReal_def, H, measure_sdiff_eq_top H h']
  · exact measureReal_sdiff_null' (measureReal_mono_null inter_subset_right h h') H.ne

@[deprecated (since := "2026-06-03")] alias measureReal_diff_null := measureReal_sdiff_null

中文:
定理 measure实数_sdiff_null
  条件: (h : μ.real s₂ = 0) (h' : μ s₂ != ∞ := by finiteness)
  证明: by
  rcases eq_top_or_lt_top (μ s₁) with H | H
  · simp [measureReal_def, H, measure_sdiff_eq_top H h']
  · exact measureReal_sdiff_null' (measureReal_mono_null inter_subset_right h h') H.ne

@[deprecated (since := "2026-06-03")] alias measureReal_diff_null := measureReal_sdiff_null

Depends on / 依赖: H.ne, eq_top_or_lt_top, finiteness, inter_subset_right, measureReal_def, measureReal_mono_null, measureReal_sdiff_null, measure_sdiff_eq_top
-/
theorem measureReal_sdiff_null (h : μ.real s₂ = 0) (h' : μ s₂ != ∞ := by finiteness) :
    μ.real (s₁ \ s₂) = μ.real s₁ := by
  rcases eq_top_or_lt_top (μ s₁) with H | H
  · simp [measureReal_def, H, measure_sdiff_eq_top H h']
  · exact measureReal_sdiff_null' (measureReal_mono_null inter_subset_right h h') H.ne

@[deprecated (since := "2026-06-03")] alias measureReal_diff_null := measureReal_sdiff_null

/--
theorem `measureReal_add_sdiff` / 定理 `measureReal_add_sdiff`

English:
theorem measureReal_add_sdiff
  statement: (hs : MeasurableSet s)
  proof: by
  rw [← measureReal_union' (@disjoint_sdiff_right _ s t) hs h₁
    (measure_ne_top_of_subset sdiff_subset h₂)]; rw [union_sdiff_self]

@[deprecated (since := "2026-06-03")] alias measureReal_add_diff := measureReal_add_sdiff

中文:
定理 measure实数_add_sdiff
  结论: (hs : 可测集 s)
  证明: by
  rw [← measureReal_union' (@disjoint_sdiff_right _ s t) hs h₁
    (measure_ne_top_of_subset sdiff_subset h₂)]; rw [union_sdiff_self]

@[deprecated (since := "2026-06-03")] alias measureReal_add_diff := measureReal_add_sdiff

Depends on / 依赖: disjoint_sdiff_right, finiteness, measureReal_union, measure_ne_top_of_subset, sdiff_subset, union_sdiff_self
-/
theorem measureReal_add_sdiff (hs : MeasurableSet s)
    (h₁ : μ s != ∞ := by finiteness) (h₂ : μ t != ∞ := by finiteness) :
    μ.real s + μ.real (t \ s) = μ.real (s union t) := by
  rw [← measureReal_union' (@disjoint_sdiff_right _ s t) hs h₁
    (measure_ne_top_of_subset sdiff_subset h₂)]; rw [union_sdiff_self]

@[deprecated (since := "2026-06-03")] alias measureReal_add_diff := measureReal_add_sdiff

/--
theorem `measureReal_sdiff'` / 定理 `measureReal_sdiff'`

English:
theorem measureReal_sdiff'
  statement: (hm : MeasurableSet t)
  proof: by
  rw [union_comm]; rw [← measureReal_add_sdiff hm h₂ h₁]
  ring

@[deprecated (since := "2026-06-03")] alias measureReal_diff' := measureReal_sdiff'

中文:
定理 measure实数_sdiff'
  结论: (hm : 可测集 t)
  证明: by
  rw [union_comm]; rw [← measureReal_add_sdiff hm h₂ h₁]
  ring

@[deprecated (since := "2026-06-03")] alias measureReal_diff' := measureReal_sdiff'

Depends on / 依赖: finiteness, measureReal_add_sdiff, union_comm
-/
theorem measureReal_sdiff' (hm : MeasurableSet t)
    (h₁ : μ s != ∞ := by finiteness) (h₂ : μ t != ∞ := by finiteness) :
    μ.real (s \ t) = μ.real (s union t) - μ.real t := by
  rw [union_comm]; rw [← measureReal_add_sdiff hm h₂ h₁]
  ring

@[deprecated (since := "2026-06-03")] alias measureReal_diff' := measureReal_sdiff'

/--
theorem `measureReal_sdiff` / 定理 `measureReal_sdiff`

English:
theorem measureReal_sdiff
  given: (h : s₂ subseteq s₁) (h₂ : MeasurableSet s₂) (h₁ : μ s₁ != ∞ := by finiteness)
  proof: by
  rw [measureReal_sdiff' h₂ h₁ (measure_ne_top_of_subset h h₁)]; rw [union_eq_self_of_subset_right h]

@[deprecated (since := "2026-06-03")] alias measureReal_diff := measureReal_sdiff

中文:
定理 measure实数_sdiff
  条件: (h : s₂ subseteq s₁) (h₂ : 可测集 s₂) (h₁ : μ s₁ != ∞ := by finiteness)
  证明: by
  rw [measureReal_sdiff' h₂ h₁ (measure_ne_top_of_subset h h₁)]; rw [union_eq_self_of_subset_right h]

@[deprecated (since := "2026-06-03")] alias measureReal_diff := measureReal_sdiff

Depends on / 依赖: finiteness, measureReal_sdiff, measure_ne_top_of_subset, union_eq_self_of_subset_right
-/
theorem measureReal_sdiff (h : s₂ subseteq s₁) (h₂ : MeasurableSet s₂) (h₁ : μ s₁ != ∞ := by finiteness) :
    μ.real (s₁ \ s₂) = μ.real s₁ - μ.real s₂ := by
  rw [measureReal_sdiff' h₂ h₁ (measure_ne_top_of_subset h h₁)]; rw [union_eq_self_of_subset_right h]

@[deprecated (since := "2026-06-03")] alias measureReal_diff := measureReal_sdiff

/--
theorem `le_measureReal_sdiff` / 定理 `le_measureReal_sdiff`

English:
theorem le_measureReal_sdiff
  given: (h : μ s₂ != ∞ := by finiteness)
  proof: by
  simp only [tsub_le_iff_left]
  calc
    μ.real s₁ <= μ.real (s₂ union s₁) := measureReal_le_measureReal_union_right h
    _ = μ.real (s₂ union s₁ \ s₂) := congr_arg μ.real union_sdiff_self.symm
    _ <= μ.real s₂ + μ.real (s₁ \ s₂) := measureReal_union_le _ _

@[deprecated (since := "2026-06-03

中文:
定理 le_measure实数_sdiff
  条件: (h : μ s₂ != ∞ := by finiteness)
  证明: by
  simp only [tsub_le_iff_left]
  calc
    μ.real s₁ <= μ.real (s₂ union s₁) := measureReal_le_measureReal_union_right h
    _ = μ.real (s₂ union s₁ \ s₂) := congr_arg μ.real union_sdiff_self.symm
    _ <= μ.real s₂ + μ.real (s₁ \ s₂) := measureReal_union_le _ _

@[deprecated (since := "2026-06-03

Depends on / 依赖: congr_arg, finiteness, measureReal_le_measureReal_union_right, measureReal_union_le, tsub_le_iff_left, union_sdiff_self, union_sdiff_self.symm
-/
theorem le_measureReal_sdiff (h : μ s₂ != ∞ := by finiteness) :
    μ.real s₁ - μ.real s₂ <= μ.real (s₁ \ s₂) := by
  simp only [tsub_le_iff_left]
  calc
    μ.real s₁ <= μ.real (s₂ union s₁) := measureReal_le_measureReal_union_right h
    _ = μ.real (s₂ union s₁ \ s₂) := congr_arg μ.real union_sdiff_self.symm
    _ <= μ.real s₂ + μ.real (s₁ \ s₂) := measureReal_union_le _ _

@[deprecated (since := "2026-06-03")] alias le_measureReal_diff := le_measureReal_sdiff

/--
theorem `measureReal_sdiff_lt_of_lt_add` / 定理 `measureReal_sdiff_lt_of_lt_add`

English:
theorem measureReal_sdiff_lt_of_lt_add
  statement: (hs : MeasurableSet s) (hst : s subseteq t) (ε : Real)
  proof: by
  rw [measureReal_sdiff hst hs ht']; linarith

@[deprecated (since := "2026-06-03")]
alias measureReal_diff_lt_of_lt_add := measureReal_sdiff_lt_of_lt_add

中文:
定理 measure实数_sdiff_lt_of_lt_add
  结论: (hs : 可测集 s) (hst : s subseteq t) (ε : 实数)
  证明: by
  rw [measureReal_sdiff hst hs ht']; linarith

@[deprecated (since := "2026-06-03")]
alias measureReal_diff_lt_of_lt_add := measureReal_sdiff_lt_of_lt_add

Depends on / 依赖: finiteness, measureReal_sdiff
-/
theorem measureReal_sdiff_lt_of_lt_add (hs : MeasurableSet s) (hst : s subseteq t) (ε : Real)
    (h : μ.real t < μ.real s + ε) (ht' : μ t != ∞ := by finiteness) :
    μ.real (t \ s) < ε := by
  rw [measureReal_sdiff hst hs ht']; linarith

@[deprecated (since := "2026-06-03")]
alias measureReal_diff_lt_of_lt_add := measureReal_sdiff_lt_of_lt_add

/--
theorem `measureReal_sdiff_le_iff_le_add` / 定理 `measureReal_sdiff_le_iff_le_add`

English:
theorem measureReal_sdiff_le_iff_le_add
  statement: (hs : MeasurableSet s) (hst : s subseteq t) (ε : Real)
  proof: by
  rw [measureReal_sdiff hst hs ht']; rw [tsub_le_iff_left]

@[deprecated (since := "2026-06-03")]
alias measureReal_diff_le_iff_le_add := measureReal_sdiff_le_iff_le_add

中文:
定理 measure实数_sdiff_le_iff_le_add
  结论: (hs : 可测集 s) (hst : s subseteq t) (ε : 实数)
  证明: by
  rw [measureReal_sdiff hst hs ht']; rw [tsub_le_iff_left]

@[deprecated (since := "2026-06-03")]
alias measureReal_diff_le_iff_le_add := measureReal_sdiff_le_iff_le_add

Depends on / 依赖: finiteness, measureReal_sdiff, tsub_le_iff_left
-/
theorem measureReal_sdiff_le_iff_le_add (hs : MeasurableSet s) (hst : s subseteq t) (ε : Real)
    (ht' : μ t != ∞ := by finiteness) :
    μ.real (t \ s) <= ε ↔ μ.real t <= μ.real s + ε := by
  rw [measureReal_sdiff hst hs ht']; rw [tsub_le_iff_left]

@[deprecated (since := "2026-06-03")]
alias measureReal_diff_le_iff_le_add := measureReal_sdiff_le_iff_le_add

/--
theorem `measureReal_eq_measureReal_of_null_sdiff` / 定理 `measureReal_eq_measureReal_of_null_sdiff`

English:
theorem measureReal_eq_measureReal_of_null_sdiff
  statement: (hst : s subseteq t)
  proof: by
  rw [measureReal_eq_zero_iff h] at h_nulldiff
  simp [measureReal_def, measure_eq_measure_of_null_sdiff hst h_nulldiff]

@[deprecated (since := "2026-06-03")]
alias measureReal_eq_measureReal_of_null_diff := measureReal_eq_measureReal_of_null_sdiff

中文:
定理 measure实数_eq_measure实数_of_null_sdiff
  结论: (hst : s subseteq t)
  证明: by
  rw [measureReal_eq_zero_iff h] at h_nulldiff
  simp [measureReal_def, measure_eq_measure_of_null_sdiff hst h_nulldiff]

@[deprecated (since := "2026-06-03")]
alias measureReal_eq_measureReal_of_null_diff := measureReal_eq_measureReal_of_null_sdiff

Depends on / 依赖: finiteness, h_nulldiff, measureReal_def, measureReal_eq_zero_iff, measure_eq_measure_of_null_sdiff
-/
theorem measureReal_eq_measureReal_of_null_sdiff (hst : s subseteq t)
    (h_nulldiff : μ.real (t \ s) = 0) (h : μ (t \ s) != ∞ := by finiteness) :
    μ.real s = μ.real t := by
  rw [measureReal_eq_zero_iff h] at h_nulldiff
  simp [measureReal_def, measure_eq_measure_of_null_sdiff hst h_nulldiff]

@[deprecated (since := "2026-06-03")]
alias measureReal_eq_measureReal_of_null_diff := measureReal_eq_measureReal_of_null_sdiff

/--
theorem `measureReal_eq_measureReal_of_between_null_sdiff` / 定理 `measureReal_eq_measureReal_of_between_null_sdiff`

English:
theorem measureReal_eq_measureReal_of_between_null_sdiff
  proof: by
  have A : μ s₁ = μ s₂ ∧ μ s₂ = μ s₃ :=
    measure_eq_measure_of_between_null_sdiff h12 h23 ((measureReal_eq_zero_iff h').1 h_nulldiff)
  simp [measureReal_def, A.1, A.2]

中文:
定理 measure实数_eq_measure实数_of_between_null_sdiff
  证明: by
  have A : μ s₁ = μ s₂ ∧ μ s₂ = μ s₃ :=
    measure_eq_measure_of_between_null_sdiff h12 h23 ((measureReal_eq_zero_iff h').1 h_nulldiff)
  simp [measureReal_def, A.1, A.2]

Depends on / 依赖: finiteness, h_nulldiff, measureReal_def, measureReal_eq_zero_iff, measure_eq_measure_of_between_null_sdiff
-/
theorem measureReal_eq_measureReal_of_between_null_sdiff
    (h12 : s₁ subseteq s₂) (h23 : s₂ subseteq s₃) (h_nulldiff : μ.real (s₃ \ s₁) = 0)
    (h' : μ (s₃ \ s₁) != ∞ := by finiteness) :
    μ.real s₁ = μ.real s₂ ∧ μ.real s₂ = μ.real s₃ := by
  have A : μ s₁ = μ s₂ ∧ μ s₂ = μ s₃ :=
    measure_eq_measure_of_between_null_sdiff h12 h23 ((measureReal_eq_zero_iff h').1 h_nulldiff)
  simp [measureReal_def, A.1, A.2]

/--
theorem `measureReal_eq_measureReal_smaller_of_between_null_sdiff` / 定理 `measureReal_eq_measureReal_smaller_of_between_null_sdiff`

English:
theorem measureReal_eq_measureReal_smaller_of_between_null_sdiff
  statement: (h12 : s₁ subseteq s₂)
  proof: (measureReal_eq_measureReal_of_between_null_sdiff h12 h23 h_nulldiff h').1

@[deprecated (since := "2026-06-03")]
alias measureReal_eq_measureReal_smaller_of_between_null_diff :=
  measureReal_eq_measureReal_smaller_of_between_null_sdiff

中文:
定理 measure实数_eq_measure实数_smaller_of_between_null_sdiff
  结论: (h12 : s₁ subseteq s₂)
  证明: (measureReal_eq_measureReal_of_between_null_sdiff h12 h23 h_nulldiff h').1

@[deprecated (since := "2026-06-03")]
alias measureReal_eq_measureReal_smaller_of_between_null_diff :=
  measureReal_eq_measureReal_smaller_of_between_null_sdiff

Depends on / 依赖: finiteness, h_nulldiff, measureReal_eq_measureReal_of_between_null_sdiff
-/
theorem measureReal_eq_measureReal_smaller_of_between_null_sdiff (h12 : s₁ subseteq s₂)
    (h23 : s₂ subseteq s₃) (h_nulldiff : μ.real (s₃ \ s₁) = 0)
    (h' : μ (s₃ \ s₁) != ∞ := by finiteness) :
    μ.real s₁ = μ.real s₂ :=
  (measureReal_eq_measureReal_of_between_null_sdiff h12 h23 h_nulldiff h').1

@[deprecated (since := "2026-06-03")]
alias measureReal_eq_measureReal_smaller_of_between_null_diff :=
  measureReal_eq_measureReal_smaller_of_between_null_sdiff

/--
theorem `measureReal_eq_measureReal_larger_of_between_null_sdiff` / 定理 `measureReal_eq_measureReal_larger_of_between_null_sdiff`

English:
theorem measureReal_eq_measureReal_larger_of_between_null_sdiff
  statement: (h12 : s₁ subseteq s₂)
  proof: (measureReal_eq_measureReal_of_between_null_sdiff h12 h23 h_nulldiff h').2

@[deprecated (since := "2026-06-03")]
alias measureReal_eq_measureReal_larger_of_between_null_diff :=
  measureReal_eq_measureReal_larger_of_between_null_sdiff

中文:
定理 measure实数_eq_measure实数_larger_of_between_null_sdiff
  结论: (h12 : s₁ subseteq s₂)
  证明: (measureReal_eq_measureReal_of_between_null_sdiff h12 h23 h_nulldiff h').2

@[deprecated (since := "2026-06-03")]
alias measureReal_eq_measureReal_larger_of_between_null_diff :=
  measureReal_eq_measureReal_larger_of_between_null_sdiff

Depends on / 依赖: finiteness, h_nulldiff, measureReal_eq_measureReal_of_between_null_sdiff
-/
theorem measureReal_eq_measureReal_larger_of_between_null_sdiff (h12 : s₁ subseteq s₂)
    (h23 : s₂ subseteq s₃) (h_nulldiff : μ.real (s₃ \ s₁) = 0) (h' : μ (s₃ \ s₁) != ∞ := by finiteness) :
    μ.real s₂ = μ.real s₃ :=
  (measureReal_eq_measureReal_of_between_null_sdiff h12 h23 h_nulldiff h').2

@[deprecated (since := "2026-06-03")]
alias measureReal_eq_measureReal_larger_of_between_null_diff :=
  measureReal_eq_measureReal_larger_of_between_null_sdiff

/--
theorem `measureReal_compl` / 定理 `measureReal_compl`

English:
theorem measureReal_compl
  given: [IsFiniteMeasure μ] (h₁ : MeasurableSet s)
  proof: by
  rw [compl_eq_univ_sdiff]
  exact measureReal_sdiff (subset_univ s) h₁

中文:
定理 measure实数_compl
  条件: [是有限测度 μ] (h₁ : 可测集 s)
  证明: by
  rw [compl_eq_univ_sdiff]
  exact measureReal_sdiff (subset_univ s) h₁

Depends on / 依赖: compl_eq_univ_sdiff, measureReal_sdiff, subset_univ
-/
theorem measureReal_compl [IsFiniteMeasure μ] (h₁ : MeasurableSet s) :
    μ.real sᶜ = μ.real univ - μ.real s := by
  rw [compl_eq_univ_sdiff]
  exact measureReal_sdiff (subset_univ s) h₁

/--
theorem `measureReal_compl₀` / 定理 `measureReal_compl₀`

English:
theorem measureReal_compl₀
  given: [IsFiniteMeasure μ] (h₁ : NullMeasurableSet s μ)
  proof: by
  linarith [measureReal_add_measureReal_compl₀ h₁]

中文:
定理 measure实数_compl₀
  条件: [是有限测度 μ] (h₁ : NullMeasurableSet s μ)
  证明: by
  linarith [measureReal_add_measureReal_compl₀ h₁]
-/
theorem measureReal_compl₀ [IsFiniteMeasure μ] (h₁ : NullMeasurableSet s μ) :
    μ.real sᶜ = μ.real univ - μ.real s := by
  linarith [measureReal_add_measureReal_compl₀ h₁]

/--
theorem `measureReal_union_congr_of_subset` / 定理 `measureReal_union_congr_of_subset`

English:
theorem measureReal_union_congr_of_subset
  statement: (hs : s₁ subseteq s₂)
  proof: by
  simp only [measureReal_def]
  rw [measure_union_congr_of_subset hs _ ht]
  · exact (ENNReal.toReal_le_toReal h₂ (measure_ne_top_of_subset ht h₂)).1 htμ
  · exact (ENNReal.toReal_le_toReal h₁ (measure_ne_top_of_subset hs h₁)).1 hsμ

中文:
定理 measure实数_union_congr_of_subset
  结论: (hs : s₁ subseteq s₂)
  证明: by
  simp only [measureReal_def]
  rw [measure_union_congr_of_subset hs _ ht]
  · exact (ENNReal.toReal_le_toReal h₂ (measure_ne_top_of_subset ht h₂)).1 htμ
  · exact (ENNReal.toReal_le_toReal h₁ (measure_ne_top_of_subset hs h₁)).1 hsμ

Depends on / 依赖: ENNReal, ENNReal.toReal_le_toReal, finiteness, measureReal_def, measure_ne_top_of_subset, measure_union_congr_of_subset, toReal_le_toReal
-/
theorem measureReal_union_congr_of_subset (hs : s₁ subseteq s₂)
    (hsμ : μ.real s₂ <= μ.real s₁) (ht : t₁ subseteq t₂) (htμ : μ.real t₂ <= μ.real t₁)
    (h₁ : μ s₂ != ∞ := by finiteness) (h₂ : μ t₂ != ∞ := by finiteness) :
    μ.real (s₁ union t₁) = μ.real (s₂ union t₂) := by
  simp only [measureReal_def]
  rw [measure_union_congr_of_subset hs _ ht]
  · exact (ENNReal.toReal_le_toReal h₂ (measure_ne_top_of_subset ht h₂)).1 htμ
  · exact (ENNReal.toReal_le_toReal h₁ (measure_ne_top_of_subset hs h₁)).1 hsμ

/--
theorem `sum_measureReal_le_measureReal_univ` / 定理 `sum_measureReal_le_measureReal_univ`

English:
theorem sum_measureReal_le_measureReal_univ
  statement: [IsFiniteMeasure μ] {s : Finset ι} {t : ι -> Set α}
  proof: by
  simp only [measureReal_def]
  rw [← ENNReal.toReal_sum (by finiteness)]
  apply ENNReal.toReal_mono (by finiteness)
  exact sum_measure_le_measure_univ (fun i mi => (h i mi).nullMeasurableSet) H.aedisjoint

中文:
定理 sum_measure实数_le_measure实数_univ
  结论: [是有限测度 μ] {s : 有限集 ι} {t : ι -> 集合 α}
  证明: by
  simp only [measureReal_def]
  rw [← ENNReal.toReal_sum (by finiteness)]
  apply ENNReal.toReal_mono (by finiteness)
  exact sum_measure_le_measure_univ (fun i mi => (h i mi).nullMeasurableSet) H.aedisjoint

Depends on / 依赖: ENNReal, ENNReal.toReal_mono, ENNReal.toReal_sum, H.aedisjoint, aedisjoint, finiteness, measureReal_def, nullMeasurableSet, sum_measure_le_measure_univ, toReal_mono, toReal_sum
-/
theorem sum_measureReal_le_measureReal_univ [IsFiniteMeasure μ] {s : Finset ι} {t : ι -> Set α}
    (h : forall i in s, MeasurableSet (t i)) (H : Set.PairwiseDisjoint (↑s) t) :
    (∑ i in s, μ.real (t i)) <= μ.real univ := by
  simp only [measureReal_def]
  rw [← ENNReal.toReal_sum (by finiteness)]
  apply ENNReal.toReal_mono (by finiteness)
  exact sum_measure_le_measure_univ (fun i mi => (h i mi).nullMeasurableSet) H.aedisjoint

/--
theorem `measureReal_add_apply` / 定理 `measureReal_add_apply`

English:
theorem measureReal_add_apply
  statement: {μ₁ μ₂ : Measure α} (h₁ : μ₁ s != ∞ := by finiteness)
  proof: by
  simp only [measureReal_def, add_apply, ENNReal.toReal_add h₁ h₂]

中文:
定理 measure实数_add_apply
  结论: {μ₁ μ₂ : 测度 α} (h₁ : μ₁ s != ∞ := by finiteness)
  证明: by
  simp only [measureReal_def, add_apply, ENNReal.toReal_add h₁ h₂]

Depends on / 依赖: ENNReal, ENNReal.toReal_add, add_apply, finiteness, measureReal_def, toReal_add
-/
theorem measureReal_add_apply {μ₁ μ₂ : Measure α} (h₁ : μ₁ s != ∞ := by finiteness)
    (h₂ : μ₂ s != ∞ := by finiteness) :
    (μ₁ + μ₂).real s = μ₁.real s + μ₂.real s := by
  simp only [measureReal_def, add_apply, ENNReal.toReal_add h₁ h₂]

/--
theorem `exists_nonempty_inter_of_measureReal_univ_lt_sum_measureReal` / 定理 `exists_nonempty_inter_of_measureReal_univ_lt_sum_measureReal`

English:
theorem exists_nonempty_inter_of_measureReal_univ_lt_sum_measureReal
  statement: [IsFiniteMeasure μ]
  proof: by
  apply exists_nonempty_inter_of_measure_univ_lt_sum_measure μ
    (fun i mi => (h i mi).nullMeasurableSet)
  simp only [Measure.real] at H
  apply (ENNReal.toReal_lt_toReal (by finiteness) _).1
  · convert! H
    rw [ENNReal.toReal_sum (by finiteness)]
  · exact (ENNReal.sum_lt_top.mpr (fun i hi

中文:
定理 存在_nonempty_inter_of_measure实数_univ_lt_sum_measure实数
  结论: [是有限测度 μ]
  证明: by
  apply exists_nonempty_inter_of_measure_univ_lt_sum_measure μ
    (fun i mi => (h i mi).nullMeasurableSet)
  simp only [Measure.real] at H
  apply (ENNReal.toReal_lt_toReal (by finiteness) _).1
  · convert! H
    rw [ENNReal.toReal_sum (by finiteness)]
  · exact (ENNReal.sum_lt_top.mpr (fun i hi

Depends on / 依赖: ENNReal, ENNReal.sum_lt_top.mpr, ENNReal.toReal_lt_toReal, ENNReal.toReal_sum, Measure, Measure.real, convert, exists_nonempty_inter_of_measure_univ_lt_sum_measure, finiteness, measure_lt_top, nullMeasurableSet, sum_lt_top, toReal_lt_toReal, toReal_sum
-/
theorem exists_nonempty_inter_of_measureReal_univ_lt_sum_measureReal [IsFiniteMeasure μ]
    {s : Finset ι} {t : ι -> Set α} (h : forall i in s, MeasurableSet (t i))
    (H : μ.real univ < ∑ i in s, μ.real (t i)) :
    exists i in s, exists j in s, exists _h : i != j, (t i inter t j).Nonempty := by
  apply exists_nonempty_inter_of_measure_univ_lt_sum_measure μ
    (fun i mi => (h i mi).nullMeasurableSet)
  simp only [Measure.real] at H
  apply (ENNReal.toReal_lt_toReal (by finiteness) _).1
  · convert! H
    rw [ENNReal.toReal_sum (by finiteness)]
  · exact (ENNReal.sum_lt_top.mpr (fun i hi => measure_lt_top ..)).ne

/--
theorem `nonempty_inter_of_measureReal_lt_add` / 定理 `nonempty_inter_of_measureReal_lt_add`

English:
theorem nonempty_inter_of_measureReal_lt_add
  proof: by
  apply nonempty_inter_of_measure_lt_add μ ht h's h't ?_
  apply (ENNReal.toReal_lt_toReal hu _).1
  · rw [ENNReal.toReal_add (measure_ne_top_of_subset h's hu) (measure_ne_top_of_subset h't hu)]
    exact h
  · exact ENNReal.add_ne_top.2 ⟨measure_ne_top_of_subset h's hu, measure_ne_top_of_subset 

中文:
定理 nonempty_inter_of_measure实数_lt_add
  证明: by
  apply nonempty_inter_of_measure_lt_add μ ht h's h't ?_
  apply (ENNReal.toReal_lt_toReal hu _).1
  · rw [ENNReal.toReal_add (measure_ne_top_of_subset h's hu) (measure_ne_top_of_subset h't hu)]
    exact h
  · exact ENNReal.add_ne_top.2 ⟨measure_ne_top_of_subset h's hu, measure_ne_top_of_subset 

Depends on / 依赖: ENNReal, ENNReal.add_ne_top, ENNReal.toReal_add, ENNReal.toReal_lt_toReal, Nonempty, add_ne_top, finiteness, measure_ne_top_of_subset, nonempty_inter_of_measure_lt_add, toReal_add, toReal_lt_toReal
-/
theorem nonempty_inter_of_measureReal_lt_add
    (ht : MeasurableSet t) (h's : s subseteq u) (h't : t subseteq u) (h : μ.real u < μ.real s + μ.real t)
    (hu : μ u != ∞ := by finiteness) :
    (s inter t).Nonempty := by
  apply nonempty_inter_of_measure_lt_add μ ht h's h't ?_
  apply (ENNReal.toReal_lt_toReal hu _).1
  · rw [ENNReal.toReal_add (measure_ne_top_of_subset h's hu) (measure_ne_top_of_subset h't hu)]
    exact h
  · exact ENNReal.add_ne_top.2 ⟨measure_ne_top_of_subset h's hu, measure_ne_top_of_subset h't hu⟩

/--
theorem `nonempty_inter_of_measureReal_lt_add'` / 定理 `nonempty_inter_of_measureReal_lt_add'`

English:
theorem nonempty_inter_of_measureReal_lt_add'
  proof: by
  rw [add_comm] at h
  rw [inter_comm]
  exact nonempty_inter_of_measureReal_lt_add hs h't h's h hu

中文:
定理 nonempty_inter_of_measure实数_lt_add'
  证明: by
  rw [add_comm] at h
  rw [inter_comm]
  exact nonempty_inter_of_measureReal_lt_add hs h't h's h hu

Depends on / 依赖: Nonempty, add_comm, finiteness, inter_comm, nonempty_inter_of_measureReal_lt_add
-/
theorem nonempty_inter_of_measureReal_lt_add'
    (hs : MeasurableSet s) (h's : s subseteq u) (h't : t subseteq u) (h : μ.real u < μ.real s + μ.real t)
    (hu : μ u != ∞ := by finiteness) :
    (s inter t).Nonempty := by
  rw [add_comm] at h
  rw [inter_comm]
  exact nonempty_inter_of_measureReal_lt_add hs h't h's h hu

variable [IsProbabilityMeasure μ]

/--
lemma `probReal_compl_eq_one_sub₀` / 引理 `probReal_compl_eq_one_sub₀`

English:
lemma probReal_compl_eq_one_sub₀
  given: (h : NullMeasurableSet s μ)
  statement: μ.real sᶜ = 1 - μ.real s
  proof: by
  rw [measureReal_compl₀ h]; rw [probReal_univ]

中文:
引理 prob实数_compl_eq_one_sub₀
  条件: (h : NullMeasurableSet s μ)
  结论: μ.real sᶜ = 1 - μ.real s
  证明: by
  rw [measureReal_compl₀ h]; rw [probReal_univ]

Depends on / 依赖: probReal_univ
-/
lemma probReal_compl_eq_one_sub₀ (h : NullMeasurableSet s μ) : μ.real sᶜ = 1 - μ.real s := by
  rw [measureReal_compl₀ h]; rw [probReal_univ]

/--
lemma `probReal_compl_eq_one_sub` / 引理 `probReal_compl_eq_one_sub`

English:
lemma probReal_compl_eq_one_sub
  given: (hs : MeasurableSet s)
  statement: μ.real sᶜ = 1 - μ.real s
  proof: probReal_compl_eq_one_sub₀ hs.nullMeasurableSet

中文:
引理 prob实数_compl_eq_one_sub
  条件: (hs : 可测集 s)
  结论: μ.real sᶜ = 1 - μ.real s
  证明: probReal_compl_eq_one_sub₀ hs.nullMeasurableSet

Depends on / 依赖: hs.nullMeasurableSet, nullMeasurableSet
-/
lemma probReal_compl_eq_one_sub (hs : MeasurableSet s) : μ.real sᶜ = 1 - μ.real s :=
  probReal_compl_eq_one_sub₀ hs.nullMeasurableSet

end MeasureTheory

namespace Mathlib.Meta.Positivity

open Lean Meta Qq Function

/-- Extension for the `positivity` tactic: applications of `μ.real` are nonnegative. -/
@[positivity MeasureTheory.Measure.real _ _]
meta def evalMeasureReal : PositivityExt where eval {_ _} _zα pα? e :=
  match pα? with | none => pure .none | some _ => do
  let .app (.app _ a) b ← whnfR e | throwError "not measureReal"
  let p ← mkAppOptM ``MeasureTheory.measureReal_nonneg #[none, none, a, b]
  pure (.nonnegative p)

end Mathlib.Meta.Positivity
