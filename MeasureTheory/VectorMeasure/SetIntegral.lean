/-
Copyright (c) 2026 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.VectorMeasure.Integral

/-!
# Set integral

In this file we prove properties of `∫ᵛ x in s, f x ∂[B; μ]`. Recall that this notation
is defined as `∫ᵛ x, f x ∂[B; μ.restrict s]`.

The API in this file is modelled on the API for the Bochner integral.
-/

@[expose] public section

assert_not_exists InnerProductSpace

open Filter Function MeasureTheory RCLike Set TopologicalSpace Topology ContinuousLinearMap
open scoped ENNReal NNReal Finset

variable {ι X E F G H : Type*} {mX : MeasurableSpace X}
  [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedAddCommGroup G] [NormedAddCommGroup H]
  {μ ν : VectorMeasure X F} {f g : X -> E} {s t : Set X}

namespace MeasureTheory.VectorMeasure

/--
theorem `IntegrableOn.mono` / 定理 `IntegrableOn.mono`

English:
theorem IntegrableOn.mono
  given: (hs : MeasurableSet s) (hts : t subseteq s) (h : μ.IntegrableOn f s)
  proof: by
  by_cases ht : MeasurableSet t; swap
  · simp [VectorMeasure.IntegrableOn, restrict_not_measurable _ ht]
  apply Integrable.mono_measure h
  simp [variation_restrict, hs, ht, Measure.restrict_mono hts le_rfl]

中文:
定理 整数egrableOn.mono
  条件: (hs : 可测集 s) (hts : t subseteq s) (h : μ.整数egrableOn f s)
  证明: by
  by_cases ht : MeasurableSet t; swap
  · simp [VectorMeasure.IntegrableOn, restrict_not_measurable _ ht]
  apply Integrable.mono_measure h
  simp [variation_restrict, hs, ht, Measure.restrict_mono hts le_rfl]
-/
theorem IntegrableOn.mono (hs : MeasurableSet s) (hts : t subseteq s) (h : μ.IntegrableOn f s) :
    μ.IntegrableOn f t := by
  by_cases ht : MeasurableSet t; swap
  · simp [VectorMeasure.IntegrableOn, restrict_not_measurable _ ht]
  apply Integrable.mono_measure h
  simp [variation_restrict, hs, ht, Measure.restrict_mono hts le_rfl]

/--
theorem `IntegrableOn.union` / 定理 `IntegrableOn.union`

English:
theorem IntegrableOn.union
  statement: (hs : MeasurableSet s) (ht : MeasurableSet t)
  proof: by
  apply Integrable.mono_measure (hf.add_measure h'f)
  grw [variation_restrict_le, Measure.restrict_union_le]
  simp [variation_restrict, hs, ht]

中文:
定理 整数egrableOn.union
  结论: (hs : 可测集 s) (ht : 可测集 t)
  证明: by
  apply Integrable.mono_measure (hf.add_measure h'f)
  grw [variation_restrict_le, Measure.restrict_union_le]
  simp [variation_restrict, hs, ht]
-/
theorem IntegrableOn.union (hs : MeasurableSet s) (ht : MeasurableSet t)
    (hf : μ.IntegrableOn f s) (h'f : μ.IntegrableOn f t) :
    μ.IntegrableOn f (s union t) := by
  apply Integrable.mono_measure (hf.add_measure h'f)
  grw [variation_restrict_le, Measure.restrict_union_le]
  simp [variation_restrict, hs, ht]

/--
theorem `IntegrableOn.empty` / 定理 `IntegrableOn.empty`

English:
theorem IntegrableOn.empty
  statement: μ.IntegrableOn f ∅
  proof: by
  simp [VectorMeasure.IntegrableOn]

中文:
定理 整数egrableOn.empty
  结论: μ.整数egrableOn f ∅
  证明: by
  simp [VectorMeasure.IntegrableOn]
-/
@[simp, nolint simpNF] theorem IntegrableOn.empty : μ.IntegrableOn f ∅ := by
  simp [VectorMeasure.IntegrableOn]

/--
theorem `IntegrableOn.biUnion_finite` / 定理 `IntegrableOn.biUnion_finite`

English:
theorem IntegrableOn.biUnion_finite
  proof: by
  induction s, hs using Set.Finite.induction_on with
  | empty => simp
  | insert _ h's hf =>
    simp only [mem_insert_iff, forall_eq_or_imp, iUnion_iUnion_eq_or_left] at ht h't ⊢
    exact IntegrableOn.union ht.1 (h's.measurableSet_biUnion ht.2) h't.1 (hf ht.2 h't.2)

中文:
定理 整数egrableOn.biUnion_finite
  证明: by
  induction s, hs using Set.Finite.induction_on with
  | empty => simp
  | insert _ h's hf =>
    simp only [mem_insert_iff, forall_eq_or_imp, iUnion_iUnion_eq_or_left] at ht h't ⊢
    exact IntegrableOn.union ht.1 (h's.measurableSet_biUnion ht.2) h't.1 (hf ht.2 h't.2)

Depends on / 依赖: Finite, IntegrableOn, IntegrableOn.union, Set.Finite.induction_on, forall_eq_or_imp, iUnion_iUnion_eq_or_left, induction_on, insert, measurableSet_biUnion, mem_insert_iff, s.measurableSet_biUnion
-/
theorem IntegrableOn.biUnion_finite
    {s : Set ι} (hs : s.Finite) {t : ι -> Set X} (ht : forall i in s, MeasurableSet (t i))
    (h't : forall i in s, μ.IntegrableOn f (t i)) :
    μ.IntegrableOn f (⋃ i in s, t i) := by
  induction s, hs using Set.Finite.induction_on with
  | empty => simp
  | insert _ h's hf =>
    simp only [mem_insert_iff, forall_eq_or_imp, iUnion_iUnion_eq_or_left] at ht h't ⊢
    exact IntegrableOn.union ht.1 (h's.measurableSet_biUnion ht.2) h't.1 (hf ht.2 h't.2)

/--
theorem `IntegrableOn.biUnion_finset` / 定理 `IntegrableOn.biUnion_finset`

English:
theorem IntegrableOn.biUnion_finset
  statement: {s : Finset ι} {t : ι -> Set X}
  proof: IntegrableOn.biUnion_finite s.finite_toSet ht h't

中文:
定理 整数egrableOn.biUnion_finset
  结论: {s : 有限集 ι} {t : ι -> 集合 X}
  证明: IntegrableOn.biUnion_finite s.finite_toSet ht h't

Depends on / 依赖: IntegrableOn, IntegrableOn.biUnion_finite, biUnion_finite, finite_toSet, s.finite_toSet
-/
theorem IntegrableOn.biUnion_finset {s : Finset ι} {t : ι -> Set X}
    (ht : forall i in s, MeasurableSet (t i)) (h't : forall i in s, μ.IntegrableOn f (t i)) :
    μ.IntegrableOn f (⋃ i in s, t i) :=
  IntegrableOn.biUnion_finite s.finite_toSet ht h't

/--
theorem `IntegrableOn.iUnion_finite` / 定理 `IntegrableOn.iUnion_finite`

English:
theorem IntegrableOn.iUnion_finite
  statement: [Finite ι] {t : ι -> Set X}
  proof: by
  cases nonempty_fintype ι
  simpa using IntegrableOn.biUnion_finset (f := f) (μ := μ) (s := Finset.univ) (t := t)
    (fun i hi => ht i) (fun i hi => h't i)

中文:
定理 整数egrableOn.iUnion_finite
  结论: [有限 ι] {t : ι -> 集合 X}
  证明: by
  cases nonempty_fintype ι
  simpa using IntegrableOn.biUnion_finset (f := f) (μ := μ) (s := Finset.univ) (t := t)
    (fun i hi => ht i) (fun i hi => h't i)

Depends on / 依赖: Finset, Finset.univ, IntegrableOn, IntegrableOn.biUnion_finset, biUnion_finset, nonempty_fintype
-/
theorem IntegrableOn.iUnion_finite [Finite ι] {t : ι -> Set X}
    (ht : forall i, MeasurableSet (t i)) (h't : forall i, μ.IntegrableOn f (t i)) :
    μ.IntegrableOn f (⋃ i, t i) := by
  cases nonempty_fintype ι
  simpa using IntegrableOn.biUnion_finset (f := f) (μ := μ) (s := Finset.univ) (t := t)
    (fun i hi => ht i) (fun i hi => h't i)

/--
theorem `integrableOn_univ` / 定理 `integrableOn_univ`

English:
theorem integrableOn_univ
  statement: μ.IntegrableOn f univ ↔ μ.Integrable f
  proof: by
  simp [VectorMeasure.IntegrableOn]

中文:
定理 integrableOn_univ
  结论: μ.整数egrableOn f univ ↔ μ.可积 f
  证明: by
  simp [VectorMeasure.IntegrableOn]
-/
@[simp] theorem integrableOn_univ : μ.IntegrableOn f univ ↔ μ.Integrable f := by
  simp [VectorMeasure.IntegrableOn]

/--
theorem `Integrable.integrableOn` / 定理 `Integrable.integrableOn`

English:
theorem Integrable.integrableOn
  given: (h : μ.Integrable f)
  statement: μ.IntegrableOn f s
  proof: by
  rw [← integrableOn_univ] at h
  exact h.mono MeasurableSet.univ (subset_univ _)

中文:
定理 可积.integrableOn
  条件: (h : μ.可积 f)
  结论: μ.整数egrableOn f s
  证明: by
  rw [← integrableOn_univ] at h
  exact h.mono MeasurableSet.univ (subset_univ _)
-/
theorem Integrable.integrableOn (h : μ.Integrable f) : μ.IntegrableOn f s := by
  rw [← integrableOn_univ] at h
  exact h.mono MeasurableSet.univ (subset_univ _)

/--
theorem `integrable_indicator_iff` / 定理 `integrable_indicator_iff`

English:
theorem integrable_indicator_iff
  given: (hs : MeasurableSet s)
  proof: by
  simp [VectorMeasure.Integrable, VectorMeasure.IntegrableOn, MeasureTheory.IntegrableOn,
    MeasureTheory.integrable_indicator_iff hs, variation_restrict hs]

中文:
定理 integrable_indicator_iff
  条件: (hs : 可测集 s)
  证明: by
  simp [VectorMeasure.Integrable, VectorMeasure.IntegrableOn, MeasureTheory.IntegrableOn,
    MeasureTheory.integrable_indicator_iff hs, variation_restrict hs]

Depends on / 依赖: Integrable, IntegrableOn, MeasureTheory, MeasureTheory.IntegrableOn, MeasureTheory.integrable_indicator_iff, VectorMeasure, VectorMeasure.Integrable, VectorMeasure.IntegrableOn, integrable_indicator_iff, variation_restrict
-/
theorem integrable_indicator_iff (hs : MeasurableSet s) :
    μ.Integrable (indicator s f) ↔ μ.IntegrableOn f s := by
  simp [VectorMeasure.Integrable, VectorMeasure.IntegrableOn, MeasureTheory.IntegrableOn,
    MeasureTheory.integrable_indicator_iff hs, variation_restrict hs]

/--
theorem `IntegrableOn.integrable_indicator` / 定理 `IntegrableOn.integrable_indicator`

English:
theorem IntegrableOn.integrable_indicator
  given: (h : μ.IntegrableOn f s) (hs : MeasurableSet s)
  proof: (integrable_indicator_iff hs).2 h

中文:
定理 整数egrableOn.integrable_indicator
  条件: (h : μ.整数egrableOn f s) (hs : 可测集 s)
  证明: (integrable_indicator_iff hs).2 h
-/
theorem IntegrableOn.integrable_indicator (h : μ.IntegrableOn f s) (hs : MeasurableSet s) :
    μ.Integrable (indicator s f) :=
  (integrable_indicator_iff hs).2 h

variable [NormedSpace Real E] [NormedSpace Real F] [NormedSpace Real G] [NormedSpace Real H]
  {B : E ->L[Real] F ->L[Real] G}

/--
theorem `setIntegral_eq_zero_of_not_measurableSet` / 定理 `setIntegral_eq_zero_of_not_measurableSet`

English:
theorem setIntegral_eq_zero_of_not_measurableSet
  given: (hs : ¬MeasurableSet s)
  proof: by
  simp [restrict_not_measurable _ hs]

中文:
定理 set整数egral_eq_zero_of_not_measurableSet
  条件: (hs : ¬可测集 s)
  证明: by
  simp [restrict_not_measurable _ hs]

Depends on / 依赖: restrict_not_measurable
-/
theorem setIntegral_eq_zero_of_not_measurableSet (hs : ¬MeasurableSet s) :
    ∫ᵛ x in s, f x ∂[B; μ] = 0 := by
  simp [restrict_not_measurable _ hs]

/--
theorem `setIntegral_congr_ae` / 定理 `setIntegral_congr_ae`

English:
theorem setIntegral_congr_ae
  given: (h : forallᵐ x ∂μ.variation, x in s -> f x = g x)
  proof: by
  by_cases hs : MeasurableSet s; swap
  · simp [setIntegral_eq_zero_of_not_measurableSet hs]
  apply integral_congr_ae
  rw [variation_restrict hs]
  exact (ae_restrict_iff' hs).2 h

中文:
定理 set整数egral_congr_ae
  条件: (h : 对任意ᵐ x ∂μ.variation, x in s -> f x = g x)
  证明: by
  by_cases hs : MeasurableSet s; swap
  · simp [setIntegral_eq_zero_of_not_measurableSet hs]
  apply integral_congr_ae
  rw [variation_restrict hs]
  exact (ae_restrict_iff' hs).2 h

Depends on / 依赖: MeasurableSet, ae_restrict_iff, integral_congr_ae, setIntegral_eq_zero_of_not_measurableSet, variation_restrict
-/
theorem setIntegral_congr_ae (h : forallᵐ x ∂μ.variation, x in s -> f x = g x) :
    ∫ᵛ x in s, f x ∂[B; μ] = ∫ᵛ x in s, g x ∂[B; μ] := by
  by_cases hs : MeasurableSet s; swap
  · simp [setIntegral_eq_zero_of_not_measurableSet hs]
  apply integral_congr_ae
  rw [variation_restrict hs]
  exact (ae_restrict_iff' hs).2 h

/--
theorem `setIntegral_congr_fun` / 定理 `setIntegral_congr_fun`

English:
theorem setIntegral_congr_fun
  given: (h : EqOn f g s)
  proof: setIntegral_congr_ae Eventually.of_forall h

中文:
定理 set整数egral_congr_fun
  条件: (h : EqOn f g s)
  证明: setIntegral_congr_ae Eventually.of_forall h

Depends on / 依赖: Eventually, Eventually.of_forall, of_forall, setIntegral_congr_ae
-/
theorem setIntegral_congr_fun (h : EqOn f g s) :
    ∫ᵛ x in s, f x ∂[B; μ] = ∫ᵛ x in s, g x ∂[B; μ] :=
setIntegral_congr_ae Eventually.of_forall h

/--
theorem `setIntegral_union` / 定理 `setIntegral_union`

English:
theorem setIntegral_union
  statement: (hst : Disjoint s t) (hs : MeasurableSet s) (ht : MeasurableSet t)
  proof: by
  rw [← integral_add_vectorMeasure hfs hft]; rw [μ.restrict_union hst hs ht]

中文:
定理 set整数egral_union
  结论: (hst : Disjoint s t) (hs : 可测集 s) (ht : 可测集 t)
  证明: by
  rw [← integral_add_vectorMeasure hfs hft]; rw [μ.restrict_union hst hs ht]

Depends on / 依赖: integral_add_vectorMeasure, restrict_union
-/
theorem setIntegral_union (hst : Disjoint s t) (hs : MeasurableSet s) (ht : MeasurableSet t)
    (hfs : μ.IntegrableOn f s) (hft : μ.IntegrableOn f t) :
    ∫ᵛ x in s union t, f x ∂[B; μ] = ∫ᵛ x in s, f x ∂[B; μ] + ∫ᵛ x in t, f x ∂[B; μ] := by
  rw [← integral_add_vectorMeasure hfs hft]; rw [μ.restrict_union hst hs ht]

/--
theorem `setIntegral_sdiff` / 定理 `setIntegral_sdiff`

English:
theorem setIntegral_sdiff
  statement: (hs : MeasurableSet s) (ht : MeasurableSet t)
  proof: by
  rw [eq_sub_iff_add_eq]; rw [← setIntegral_union (by grind) (hs.diff ht) ht (hfs.mono hs sdiff_subset)
    (hfs.mono hs hts)]; rw [sdiff_union_of_subset hts]

中文:
定理 set整数egral_sdiff
  结论: (hs : 可测集 s) (ht : 可测集 t)
  证明: by
  rw [eq_sub_iff_add_eq]; rw [← setIntegral_union (by grind) (hs.diff ht) ht (hfs.mono hs sdiff_subset)
    (hfs.mono hs hts)]; rw [sdiff_union_of_subset hts]

Depends on / 依赖: eq_sub_iff_add_eq, hfs.mono, hs.diff, sdiff_subset, sdiff_union_of_subset, setIntegral_union
-/
theorem setIntegral_sdiff (hs : MeasurableSet s) (ht : MeasurableSet t)
    (hfs : μ.IntegrableOn f s) (hts : t subseteq s) :
    ∫ᵛ x in s \ t, f x ∂[B; μ] = ∫ᵛ x in s, f x ∂[B; μ] - ∫ᵛ x in t, f x ∂[B; μ] := by
  rw [eq_sub_iff_add_eq]; rw [← setIntegral_union (by grind) (hs.diff ht) ht (hfs.mono hs sdiff_subset)
    (hfs.mono hs hts)]; rw [sdiff_union_of_subset hts]

/--
theorem `setIntegral_inter_add_sdiff` / 定理 `setIntegral_inter_add_sdiff`

English:
theorem setIntegral_inter_add_sdiff
  statement: (hs : MeasurableSet s) (ht : MeasurableSet t)
  proof: by
  rw [← μ.restrict_inter_add_sdiff hs ht]; rw [integral_add_vectorMeasure (hfs.mono hs inter_subset_left) (hfs.mono hs sdiff_subset)]

中文:
定理 set整数egral_inter_add_sdiff
  结论: (hs : 可测集 s) (ht : 可测集 t)
  证明: by
  rw [← μ.restrict_inter_add_sdiff hs ht]; rw [integral_add_vectorMeasure (hfs.mono hs inter_subset_left) (hfs.mono hs sdiff_subset)]

Depends on / 依赖: hfs.mono, integral_add_vectorMeasure, inter_subset_left, restrict_inter_add_sdiff, sdiff_subset
-/
theorem setIntegral_inter_add_sdiff (hs : MeasurableSet s) (ht : MeasurableSet t)
    (hfs : μ.IntegrableOn f s) :
    ∫ᵛ x in s inter t, f x ∂[B; μ] + ∫ᵛ x in s \ t, f x ∂[B; μ] = ∫ᵛ x in s, f x ∂[B; μ] := by
  rw [← μ.restrict_inter_add_sdiff hs ht]; rw [integral_add_vectorMeasure (hfs.mono hs inter_subset_left) (hfs.mono hs sdiff_subset)]

/--
theorem `setIntegral_biUnion_finset` / 定理 `setIntegral_biUnion_finset`

English:
theorem setIntegral_biUnion_finset
  statement: {ι : Type*} (t : Finset ι) {s : ι -> Set X}
  proof: by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | insert _ _ hat IH =>
    simp only [Finset.coe_insert, Finset.forall_mem_insert, Set.pairwise_insert,
      Finset.set_biUnion_insert] at hs hf h's ⊢
    rw [setIntegral_union]
    · rw [Finset.sum_insert hat, IH hs.2 h's.1 hf.2]
    · simp only [disjoint_iUnion_right]
      exact fun i hi => (h's.2 i hi (ne_of_mem_of_not_mem hi hat).symm).1
    · exact hs.1
    · exact Finset.measurableSet_biUnion _ hs.2
    · exact hf.1
    · apply IntegrableOn.biUnion_finset hs.2 hf.2

中文:
定理 set整数egral_biUnion_finset
  结论: {ι : 类型} (t : 有限集 ι) {s : ι -> 集合 X}
  证明: by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | insert _ _ hat IH =>
    simp only [Finset.coe_insert, Finset.forall_mem_insert, Set.pairwise_insert,
      Finset.set_biUnion_insert] at hs hf h's ⊢
    rw [setIntegral_union]
    · rw [Finset.sum_insert hat, IH hs.2 h's.1 hf.2]
    · simp only [disjoint_iUnion_right]
      exact fun i hi => (h's.2 i hi (ne_of_mem_of_not_mem hi hat).symm).1
    · exact hs.1
    · exact Finset.measurableSet_biUnion _ hs.2
    · exact hf.1
    · apply IntegrableOn.biUnion_finset hs.2 hf.2

Depends on / 依赖: Finset, Finset.coe_insert, Finset.forall_mem_insert, Finset.induction_on, Finset.measurableSet_biUnion, Finset.set_biUnion_insert, Finset.sum_insert, IntegrableOn, IntegrableOn.biUnion_finset, Set.pairwise_insert, biUnion_finset, classical, coe_insert, disjoint_iUnion_right, forall_mem_insert, induction_on, insert, measurableSet_biUnion, ne_of_mem_of_not_mem, pairwise_insert
-/
theorem setIntegral_biUnion_finset {ι : Type*} (t : Finset ι) {s : ι -> Set X}
    (hs : forall i in t, MeasurableSet (s i)) (h's : Set.Pairwise (↑t) (Disjoint on s))
    (hf : forall i in t, μ.IntegrableOn f (s i)) :
    ∫ᵛ x in ⋃ i in t, s i, f x ∂[B; μ] = ∑ i in t, ∫ᵛ x in s i, f x ∂[B; μ] := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | insert _ _ hat IH =>
    simp only [Finset.coe_insert, Finset.forall_mem_insert, Set.pairwise_insert,
      Finset.set_biUnion_insert] at hs hf h's ⊢
    rw [setIntegral_union]
    · rw [Finset.sum_insert hat, IH hs.2 h's.1 hf.2]
    · simp only [disjoint_iUnion_right]
      exact fun i hi => (h's.2 i hi (ne_of_mem_of_not_mem hi hat).symm).1
    · exact hs.1
    · exact Finset.measurableSet_biUnion _ hs.2
    · exact hf.1
    · apply IntegrableOn.biUnion_finset hs.2 hf.2

/--
theorem `setIntegral_iUnion_fintype` / 定理 `setIntegral_iUnion_fintype`

English:
theorem setIntegral_iUnion_fintype
  statement: {ι : Type*} [Fintype ι] {s : ι -> Set X}
  proof: by
  convert setIntegral_biUnion_finset Finset.univ (fun i _ => hs i) _ fun i _ => hf i
  · simp
  · simp [pairwise_univ, h's]

中文:
定理 set整数egral_iUnion_fintype
  结论: {ι : 类型} [有限类型 ι] {s : ι -> 集合 X}
  证明: by
  convert setIntegral_biUnion_finset Finset.univ (fun i _ => hs i) _ fun i _ => hf i
  · simp
  · simp [pairwise_univ, h's]

Depends on / 依赖: Finset, Finset.univ, convert, pairwise_univ, setIntegral_biUnion_finset
-/
theorem setIntegral_iUnion_fintype {ι : Type*} [Fintype ι] {s : ι -> Set X}
    (hs : forall i, MeasurableSet (s i)) (h's : Pairwise (Disjoint on s))
    (hf : forall i, μ.IntegrableOn f (s i)) :
    ∫ᵛ x in ⋃ i, s i, f x ∂[B; μ] = ∑ i, ∫ᵛ x in s i, f x ∂[B; μ] := by
  convert setIntegral_biUnion_finset Finset.univ (fun i _ => hs i) _ fun i _ => hf i
  · simp
  · simp [pairwise_univ, h's]

/--
theorem `setIntegral_empty` / 定理 `setIntegral_empty`

English:
theorem setIntegral_empty
  statement: ∫ᵛ x in ∅, f x ∂[B; μ] = 0
  proof: by simp

中文:
定理 set整数egral_empty
  结论: ∫ᵛ x in ∅, f x ∂[B; μ] = 0
  证明: by simp
-/
theorem setIntegral_empty : ∫ᵛ x in ∅, f x ∂[B; μ] = 0 := by simp

/--
theorem `setIntegral_univ` / 定理 `setIntegral_univ`

English:
theorem setIntegral_univ
  statement: ∫ᵛ x in univ, f x ∂[B; μ] = ∫ᵛ x, f x ∂[B; μ]
  proof: by simp

中文:
定理 set整数egral_univ
  结论: ∫ᵛ x in univ, f x ∂[B; μ] = ∫ᵛ x, f x ∂[B; μ]
  证明: by simp
-/
theorem setIntegral_univ : ∫ᵛ x in univ, f x ∂[B; μ] = ∫ᵛ x, f x ∂[B; μ] := by simp

/--
theorem `setIntegral_add_compl` / 定理 `setIntegral_add_compl`

English:
theorem setIntegral_add_compl
  given: (hs : MeasurableSet s) (hfi : μ.Integrable f)
  proof: by
  rw [← setIntegral_union disjoint_compl_right
    hs hs.compl hfi.integrableOn hfi.integrableOn]; rw [union_compl_self]; rw [setIntegral_univ]

中文:
定理 set整数egral_add_compl
  条件: (hs : 可测集 s) (hfi : μ.可积 f)
  证明: by
  rw [← setIntegral_union disjoint_compl_right
    hs hs.compl hfi.integrableOn hfi.integrableOn]; rw [union_compl_self]; rw [setIntegral_univ]

Depends on / 依赖: disjoint_compl_right, hfi.integrableOn, hs.compl, integrableOn, setIntegral_union, setIntegral_univ, union_compl_self
-/
theorem setIntegral_add_compl (hs : MeasurableSet s) (hfi : μ.Integrable f) :
    ∫ᵛ x in s, f x ∂[B; μ] + ∫ᵛ x in sᶜ, f x ∂[B; μ] = ∫ᵛ x, f x ∂[B; μ] := by
  rw [← setIntegral_union disjoint_compl_right
    hs hs.compl hfi.integrableOn hfi.integrableOn]; rw [union_compl_self]; rw [setIntegral_univ]

/--
theorem `setIntegral_compl` / 定理 `setIntegral_compl`

English:
theorem setIntegral_compl
  given: (hs : MeasurableSet s) (hfi : μ.Integrable f)
  proof: by
  rw [← setIntegral_add_compl (μ := μ) hs hfi]; rw [add_sub_cancel_left]

中文:
定理 set整数egral_compl
  条件: (hs : 可测集 s) (hfi : μ.可积 f)
  证明: by
  rw [← setIntegral_add_compl (μ := μ) hs hfi]; rw [add_sub_cancel_left]

Depends on / 依赖: add_sub_cancel_left, setIntegral_add_compl
-/
theorem setIntegral_compl (hs : MeasurableSet s) (hfi : μ.Integrable f) :
    ∫ᵛ x in sᶜ, f x ∂[B; μ] = ∫ᵛ x, f x ∂[B; μ] - ∫ᵛ x in s, f x ∂[B; μ] := by
  rw [← setIntegral_add_compl (μ := μ) hs hfi]; rw [add_sub_cancel_left]

/--
theorem `integral_indicator` / 定理 `integral_indicator`

English:
theorem integral_indicator
  given: (hs : MeasurableSet s)
  proof: by
  by_cases hfi : μ.IntegrableOn f s; swap
  · rw [integral_undef hfi, integral_undef]
    rw [integrable_indicator_iff hs]
    simpa [transpose_restrict, variation_restrict hs] using hfi
  calc
    ∫ᵛ x, indicator s f x ∂[B; μ]
    _ = ∫ᵛ x in s, indicator s f x ∂[B; μ] + ∫ᵛ x in sᶜ, indicator s f x ∂[B; μ] :=
      (setIntegral_add_compl hs (hfi.integrable_indicator hs)).symm
    _ = ∫ᵛ x in s, f x ∂[B; μ] + ∫ᵛ x in sᶜ, 0 ∂[B; μ] := by
      apply congr_arg₂ (· + ·) (integral_congr_ae ?_) (integral_congr_ae ?_)
      · rw [variation_restrict hs]
        exact indicator_ae_eq_restrict hs
      · rw [variation_restrict hs.compl]
        exact indicator_ae_eq_restrict_compl hs
    _ = ∫ᵛ x in s, f x ∂[B; μ] := by simp

中文:
定理 integral_indicator
  条件: (hs : 可测集 s)
  证明: by
  by_cases hfi : μ.IntegrableOn f s; swap
  · rw [integral_undef hfi, integral_undef]
    rw [integrable_indicator_iff hs]
    simpa [transpose_restrict, variation_restrict hs] using hfi
  calc
    ∫ᵛ x, indicator s f x ∂[B; μ]
    _ = ∫ᵛ x in s, indicator s f x ∂[B; μ] + ∫ᵛ x in sᶜ, indicator s f x ∂[B; μ] :=
      (setIntegral_add_compl hs (hfi.integrable_indicator hs)).symm
    _ = ∫ᵛ x in s, f x ∂[B; μ] + ∫ᵛ x in sᶜ, 0 ∂[B; μ] := by
      apply congr_arg₂ (· + ·) (integral_congr_ae ?_) (integral_congr_ae ?_)
      · rw [variation_restrict hs]
        exact indicator_ae_eq_restrict hs
      · rw [variation_restrict hs.compl]
        exact indicator_ae_eq_restrict_compl hs
    _ = ∫ᵛ x in s, f x ∂[B; μ] := by simp

Depends on / 依赖: IntegrableOn, hfi.integrable_indicator, indicator, integrable_indicator, integrable_indicator_iff, integral_congr_ae, integral_undef, setIntegral_add_compl, transpose_restrict, variation_r, variation_restrict
-/
theorem integral_indicator (hs : MeasurableSet s) :
    ∫ᵛ x, indicator s f x ∂[B; μ] = ∫ᵛ x in s, f x ∂[B; μ] := by
  by_cases hfi : μ.IntegrableOn f s; swap
  · rw [integral_undef hfi, integral_undef]
    rw [integrable_indicator_iff hs]
    simpa [transpose_restrict, variation_restrict hs] using hfi
  calc
    ∫ᵛ x, indicator s f x ∂[B; μ]
    _ = ∫ᵛ x in s, indicator s f x ∂[B; μ] + ∫ᵛ x in sᶜ, indicator s f x ∂[B; μ] :=
      (setIntegral_add_compl hs (hfi.integrable_indicator hs)).symm
    _ = ∫ᵛ x in s, f x ∂[B; μ] + ∫ᵛ x in sᶜ, 0 ∂[B; μ] := by
      apply congr_arg₂ (· + ·) (integral_congr_ae ?_) (integral_congr_ae ?_)
      · rw [variation_restrict hs]
        exact indicator_ae_eq_restrict hs
      · rw [variation_restrict hs.compl]
        exact indicator_ae_eq_restrict_compl hs
    _ = ∫ᵛ x in s, f x ∂[B; μ] := by simp

/--
theorem `setIntegral_indicator` / 定理 `setIntegral_indicator`

English:
theorem setIntegral_indicator
  given: (hs : MeasurableSet s) (ht : MeasurableSet t)
  proof: by
  rw [integral_indicator ht]; rw [μ.restrict_restrict ht hs]; rw [Set.inter_comm]

中文:
定理 set整数egral_indicator
  条件: (hs : 可测集 s) (ht : 可测集 t)
  证明: by
  rw [integral_indicator ht]; rw [μ.restrict_restrict ht hs]; rw [Set.inter_comm]

Depends on / 依赖: Set.inter_comm, integral_indicator, inter_comm, restrict_restrict
-/
theorem setIntegral_indicator (hs : MeasurableSet s) (ht : MeasurableSet t) :
    ∫ᵛ x in s, t.indicator f x ∂[B; μ] = ∫ᵛ x in s inter t, f x ∂[B; μ] := by
  rw [integral_indicator ht]; rw [μ.restrict_restrict ht hs]; rw [Set.inter_comm]

/--
theorem `setIntegral_congr_set` / 定理 `setIntegral_congr_set`

English:
theorem setIntegral_congr_set
  proof: by
  rw [← integral_indicator hs]; rw [← integral_indicator ht]
  apply integral_congr_ae
  filter_upwards [hst] with x hx
  replace hx : x in s ↔ x in t := by simpa using! hx
  simp [indicator]
  grind

中文:
定理 set整数egral_congr_set
  证明: by
  rw [← integral_indicator hs]; rw [← integral_indicator ht]
  apply integral_congr_ae
  filter_upwards [hst] with x hx
  replace hx : x in s ↔ x in t := by simpa using! hx
  simp [indicator]
  grind

Depends on / 依赖: filter_upwards, indicator, integral_congr_ae, integral_indicator, replace
-/
theorem setIntegral_congr_set
    (hs : MeasurableSet s) (ht : MeasurableSet t) (hst : s =ᵐ[μ.variation] t) :
    ∫ᵛ x in s, f x ∂[B; μ] = ∫ᵛ x in t, f x ∂[B; μ] := by
  rw [← integral_indicator hs]; rw [← integral_indicator ht]
  apply integral_congr_ae
  filter_upwards [hst] with x hx
  replace hx : x in s ↔ x in t := by simpa using! hx
  simp [indicator]
  grind

/--
theorem `integral_piecewise` / 定理 `integral_piecewise`

English:
theorem integral_piecewise
  statement: [DecidablePred (· in s)]
  proof: by
  rw [← Set.indicator_add_compl_eq_piecewise]; rw [integral_add (hf.integrable_indicator hs) (hg.integrable_indicator hs.compl)]; rw [integral_indicator hs]; rw [integral_indicator hs.compl]

中文:
定理 integral_piecewise
  结论: [DecidablePred (· in s)]
  证明: by
  rw [← Set.indicator_add_compl_eq_piecewise]; rw [integral_add (hf.integrable_indicator hs) (hg.integrable_indicator hs.compl)]; rw [integral_indicator hs]; rw [integral_indicator hs.compl]

Depends on / 依赖: Set.indicator_add_compl_eq_piecewise, hf.integrable_indicator, hg.integrable_indicator, hs.compl, indicator_add_compl_eq_piecewise, integrable_indicator, integral_add, integral_indicator
-/
theorem integral_piecewise [DecidablePred (· in s)]
    (hs : MeasurableSet s) (hf : μ.IntegrableOn f s) (hg : μ.IntegrableOn g sᶜ) :
    ∫ᵛ x, s.piecewise f g x ∂[B; μ] = ∫ᵛ x in s, f x ∂[B; μ] + ∫ᵛ x in sᶜ, g x ∂[B; μ] := by
  rw [← Set.indicator_add_compl_eq_piecewise]; rw [integral_add (hf.integrable_indicator hs) (hg.integrable_indicator hs.compl)]; rw [integral_indicator hs]; rw [integral_indicator hs.compl]

/--
theorem `setIntegral_eq_zero_of_ae_eq_zero` / 定理 `setIntegral_eq_zero_of_ae_eq_zero`

English:
theorem setIntegral_eq_zero_of_ae_eq_zero
  proof: by
  by_cases ht : MeasurableSet t; swap
  · simp [setIntegral_eq_zero_of_not_measurableSet ht]
  by_cases hf : AEStronglyMeasurable f (μ.restrict t).variation; swap
  · rw [integral_undef]
    contrapose hf
    exact hf.1
  simp only [variation_restrict ht] at hf
  have : ∫ᵛ x in t, hf.mk f x ∂[B; μ] = 0 := by
    refine integral_eq_zero_of_ae ?_
    simp only [variation_restrict ht]
    apply (ae_restrict_iff' ht).2
    filter_upwards [ae_imp_of_ae_restrict hf.ae_eq_mk, ht_eq] with x hx h'x h''x
    rw [← hx h''x]
    exact h'x h''x
  rw [← this]
  apply integral_congr_ae
  simp only [variation_restrict ht]
  exact hf.ae_eq_mk

中文:
定理 set整数egral_eq_zero_of_ae_eq_zero
  证明: by
  by_cases ht : MeasurableSet t; swap
  · simp [setIntegral_eq_zero_of_not_measurableSet ht]
  by_cases hf : AEStronglyMeasurable f (μ.restrict t).variation; swap
  · rw [integral_undef]
    contrapose hf
    exact hf.1
  simp only [variation_restrict ht] at hf
  have : ∫ᵛ x in t, hf.mk f x ∂[B; μ] = 0 := by
    refine integral_eq_zero_of_ae ?_
    simp only [variation_restrict ht]
    apply (ae_restrict_iff' ht).2
    filter_upwards [ae_imp_of_ae_restrict hf.ae_eq_mk, ht_eq] with x hx h'x h''x
    rw [← hx h''x]
    exact h'x h''x
  rw [← this]
  apply integral_congr_ae
  simp only [variation_restrict ht]
  exact hf.ae_eq_mk

Depends on / 依赖: AEStronglyMeasurable, MeasurableSet, ae_eq_mk, ae_imp_of_ae_restrict, ae_restrict_iff, contrapose, filter_upwards, hf.ae_eq_mk, hf.mk, ht_eq, integral_eq_zero_of_ae, integral_undef, restrict, setIntegral_eq_zero_of_not_measurableSet, variation, variation_restrict
-/
theorem setIntegral_eq_zero_of_ae_eq_zero
    (ht_eq : forallᵐ x ∂μ.variation, x in t -> f x = 0) :
    ∫ᵛ x in t, f x ∂[B; μ] = 0 := by
  by_cases ht : MeasurableSet t; swap
  · simp [setIntegral_eq_zero_of_not_measurableSet ht]
  by_cases hf : AEStronglyMeasurable f (μ.restrict t).variation; swap
  · rw [integral_undef]
    contrapose hf
    exact hf.1
  simp only [variation_restrict ht] at hf
  have : ∫ᵛ x in t, hf.mk f x ∂[B; μ] = 0 := by
    refine integral_eq_zero_of_ae ?_
    simp only [variation_restrict ht]
    apply (ae_restrict_iff' ht).2
    filter_upwards [ae_imp_of_ae_restrict hf.ae_eq_mk, ht_eq] with x hx h'x h''x
    rw [← hx h''x]
    exact h'x h''x
  rw [← this]
  apply integral_congr_ae
  simp only [variation_restrict ht]
  exact hf.ae_eq_mk

/--
theorem `setIntegral_eq_zero_of_forall_eq_zero` / 定理 `setIntegral_eq_zero_of_forall_eq_zero`

English:
theorem setIntegral_eq_zero_of_forall_eq_zero
  given: (ht_eq : forall x in t, f x = 0)
  proof: setIntegral_eq_zero_of_ae_eq_zero (Eventually.of_forall ht_eq)

中文:
定理 set整数egral_eq_zero_of_对任意_eq_zero
  条件: (ht_eq : 对任意 x in t, f x = 0)
  证明: setIntegral_eq_zero_of_ae_eq_zero (Eventually.of_forall ht_eq)

Depends on / 依赖: Eventually, Eventually.of_forall, ht_eq, of_forall, setIntegral_eq_zero_of_ae_eq_zero
-/
theorem setIntegral_eq_zero_of_forall_eq_zero (ht_eq : forall x in t, f x = 0) :
    ∫ᵛ x in t, f x ∂[B; μ] = 0 :=
  setIntegral_eq_zero_of_ae_eq_zero (Eventually.of_forall ht_eq)

/--
theorem `frequently_ae_ne_zero_of_setIntegral_ne_zero` / 定理 `frequently_ae_ne_zero_of_setIntegral_ne_zero`

English:
theorem frequently_ae_ne_zero_of_setIntegral_ne_zero
  given: (hU : ∫ᵛ x in t, f x ∂[B; μ] != 0)
  proof: by
  have ht : MeasurableSet t := by
    contrapose! hU
    simp [setIntegral_eq_zero_of_not_measurableSet hU]
  rw [← variation_restrict ht]
  exact frequently_ae_ne_zero_of_integral_ne_zero hU

中文:
定理 frequently_ae_ne_zero_of_set整数egral_ne_zero
  条件: (hU : ∫ᵛ x in t, f x ∂[B; μ] != 0)
  证明: by
  have ht : MeasurableSet t := by
    contrapose! hU
    simp [setIntegral_eq_zero_of_not_measurableSet hU]
  rw [← variation_restrict ht]
  exact frequently_ae_ne_zero_of_integral_ne_zero hU

Depends on / 依赖: MeasurableSet, contrapose, frequently_ae_ne_zero_of_integral_ne_zero, setIntegral_eq_zero_of_not_measurableSet, variation_restrict
-/
theorem frequently_ae_ne_zero_of_setIntegral_ne_zero (hU : ∫ᵛ x in t, f x ∂[B; μ] != 0) :
    existsᶠ x in ae (μ.variation.restrict t), f x != 0 := by
  have ht : MeasurableSet t := by
    contrapose! hU
    simp [setIntegral_eq_zero_of_not_measurableSet hU]
  rw [← variation_restrict ht]
  exact frequently_ae_ne_zero_of_integral_ne_zero hU

/--
theorem `exists_ne_zero_of_setIntegral_ne_zero` / 定理 `exists_ne_zero_of_setIntegral_ne_zero`

English:
theorem exists_ne_zero_of_setIntegral_ne_zero
  given: (hU : ∫ᵛ x in t, f x ∂[B; μ] != 0)
  proof: by
  contrapose! hU; exact setIntegral_eq_zero_of_forall_eq_zero hU

中文:
定理 存在_ne_zero_of_set整数egral_ne_zero
  条件: (hU : ∫ᵛ x in t, f x ∂[B; μ] != 0)
  证明: by
  contrapose! hU; exact setIntegral_eq_zero_of_forall_eq_zero hU

Depends on / 依赖: contrapose, setIntegral_eq_zero_of_forall_eq_zero
-/
theorem exists_ne_zero_of_setIntegral_ne_zero (hU : ∫ᵛ x in t, f x ∂[B; μ] != 0) :
    exists x, x in t ∧ f x != 0 := by
  contrapose! hU; exact setIntegral_eq_zero_of_forall_eq_zero hU

/--
theorem `setIntegral_of_variation_apply_eq_zero` / 定理 `setIntegral_of_variation_apply_eq_zero`

English:
theorem setIntegral_of_variation_apply_eq_zero
  statement: (f : X -> E) {s : Set X}
  proof: by
  by_cases h's : MeasurableSet s; swap
  · simp [restrict_not_measurable μ h's]
  have : (μ.restrict s).variation = 0 := by
    rw [variation_restrict h's]
    apply Measure.restrict_eq_zero.2 hs
  have : μ.restrict s = 0 := variation_eq_zero.1 this
  simp [this]

中文:
定理 set整数egral_of_variation_apply_eq_zero
  结论: (f : X -> E) {s : 集合 X}
  证明: by
  by_cases h's : MeasurableSet s; swap
  · simp [restrict_not_measurable μ h's]
  have : (μ.restrict s).variation = 0 := by
    rw [variation_restrict h's]
    apply Measure.restrict_eq_zero.2 hs
  have : μ.restrict s = 0 := variation_eq_zero.1 this
  simp [this]

Depends on / 依赖: MeasurableSet, Measure, Measure.restrict_eq_zero, restrict, restrict_eq_zero, restrict_not_measurable, variation, variation_eq_zero, variation_restrict
-/
theorem setIntegral_of_variation_apply_eq_zero (f : X -> E) {s : Set X}
    (hs : μ.variation s = 0) :
    ∫ᵛ x in s, f x ∂[B; μ] = 0 := by
  by_cases h's : MeasurableSet s; swap
  · simp [restrict_not_measurable μ h's]
  have : (μ.restrict s).variation = 0 := by
    rw [variation_restrict h's]
    apply Measure.restrict_eq_zero.2 hs
  have : μ.restrict s = 0 := variation_eq_zero.1 this
  simp [this]

/--
theorem `setIntegral_dirac'` / 定理 `setIntegral_dirac'`

English:
theorem setIntegral_dirac'
  statement: {mX : MeasurableSpace X} [CompleteSpace G] {a : X} {v : F}
  proof: by
  rw [restrict_dirac hs]
  split_ifs
  · exact integral_dirac' hf
  · exact integral_zero_vectorMeasure

中文:
定理 set整数egral_dirac'
  结论: {mX : 可测空间 X} [完备空间 G] {a : X} {v : F}
  证明: by
  rw [restrict_dirac hs]
  split_ifs
  · exact integral_dirac' hf
  · exact integral_zero_vectorMeasure

Depends on / 依赖: integral_dirac, integral_zero_vectorMeasure, restrict_dirac, split_ifs
-/
theorem setIntegral_dirac' {mX : MeasurableSpace X} [CompleteSpace G] {a : X} {v : F}
    (hf : StronglyMeasurable f) {s : Set X} (hs : MeasurableSet s) [Decidable (a in s)] :
    ∫ᵛ x in s, f x ∂[B; VectorMeasure.dirac a v] = if a in s then B (f a) v else 0 := by
  rw [restrict_dirac hs]
  split_ifs
  · exact integral_dirac' hf
  · exact integral_zero_vectorMeasure

/--
theorem `setIntegral_dirac` / 定理 `setIntegral_dirac`

English:
theorem setIntegral_dirac
  statement: [MeasurableSpace X] [MeasurableSingletonClass X] [CompleteSpace G]
  proof: by
  rw [restrict_dirac hs]
  split_ifs
  · exact integral_dirac
  · exact integral_zero_vectorMeasure

中文:
定理 set整数egral_dirac
  结论: [可测空间 X] [MeasurableSingleton类 X] [完备空间 G]
  证明: by
  rw [restrict_dirac hs]
  split_ifs
  · exact integral_dirac
  · exact integral_zero_vectorMeasure

Depends on / 依赖: integral_dirac, integral_zero_vectorMeasure, restrict_dirac, split_ifs
-/
theorem setIntegral_dirac [MeasurableSpace X] [MeasurableSingletonClass X] [CompleteSpace G]
    {a : X} {v : F} {s : Set X} (hs : MeasurableSet s) [Decidable (a in s)] :
    ∫ᵛ x in s, f x ∂[B; VectorMeasure.dirac a v] = if a in s then B (f a) v else 0 := by
  rw [restrict_dirac hs]
  split_ifs
  · exact integral_dirac
  · exact integral_zero_vectorMeasure

/--
theorem `integral_singleton'` / 定理 `integral_singleton'`

English:
theorem integral_singleton'
  given: [CompleteSpace G] {a : X} (hf : StronglyMeasurable f)
  proof: by
  simp only [restrict_singleton, integral_dirac' hf]

中文:
定理 integral_singleton'
  条件: [完备空间 G] {a : X} (hf : StronglyMeasurable f)
  证明: by
  simp only [restrict_singleton, integral_dirac' hf]

Depends on / 依赖: integral_dirac, restrict_singleton
-/
theorem integral_singleton' [CompleteSpace G] {a : X} (hf : StronglyMeasurable f) :
    ∫ᵛ a in {a}, f a ∂[B; μ] = B (f a) (μ {a}) := by
  simp only [restrict_singleton, integral_dirac' hf]

/--
theorem `integral_singleton` / 定理 `integral_singleton`

English:
theorem integral_singleton
  given: [MeasurableSingletonClass X] {a : X} [CompleteSpace G]
  proof: by
  simp only [restrict_singleton, integral_dirac]

中文:
定理 integral_singleton
  条件: [MeasurableSingleton类 X] {a : X} [完备空间 G]
  证明: by
  simp only [restrict_singleton, integral_dirac]

Depends on / 依赖: integral_dirac, restrict_singleton
-/
theorem integral_singleton [MeasurableSingletonClass X] {a : X} [CompleteSpace G] :
    ∫ᵛ a in {a}, f a ∂[B; μ] = B (f a) (μ {a}) := by
  simp only [restrict_singleton, integral_dirac]

/--
theorem `setIntegral_union_eq_left_of_ae` / 定理 `setIntegral_union_eq_left_of_ae`

English:
theorem setIntegral_union_eq_left_of_ae
  statement: (hs : MeasurableSet s) (ht : MeasurableSet t)
  proof: by
  rw [← integral_indicator hs]; rw [← integral_indicator (hs.union ht)]
  apply integral_congr_ae
  rw [ae_restrict_iff' ht] at ht_eq
  filter_upwards [ht_eq] with x hx
  classical
  simp only [indicator_apply, mem_union]
  grind

中文:
定理 set整数egral_union_eq_left_of_ae
  结论: (hs : 可测集 s) (ht : 可测集 t)
  证明: by
  rw [← integral_indicator hs]; rw [← integral_indicator (hs.union ht)]
  apply integral_congr_ae
  rw [ae_restrict_iff' ht] at ht_eq
  filter_upwards [ht_eq] with x hx
  classical
  simp only [indicator_apply, mem_union]
  grind

Depends on / 依赖: ae_restrict_iff, classical, filter_upwards, hs.union, ht_eq, indicator_apply, integral_congr_ae, integral_indicator, mem_union
-/
theorem setIntegral_union_eq_left_of_ae (hs : MeasurableSet s) (ht : MeasurableSet t)
    (ht_eq : forallᵐ x ∂μ.variation.restrict t, f x = 0) :
    ∫ᵛ x in s union t, f x ∂[B; μ] = ∫ᵛ x in s, f x ∂[B; μ] := by
  rw [← integral_indicator hs]; rw [← integral_indicator (hs.union ht)]
  apply integral_congr_ae
  rw [ae_restrict_iff' ht] at ht_eq
  filter_upwards [ht_eq] with x hx
  classical
  simp only [indicator_apply, mem_union]
  grind

/--
theorem `setIntegral_union_eq_left_of_forall` / 定理 `setIntegral_union_eq_left_of_forall`

English:
theorem setIntegral_union_eq_left_of_forall
  statement: (hs : MeasurableSet s) (ht : MeasurableSet t)
  proof: by
  apply setIntegral_union_eq_left_of_ae hs ht
  rw [ae_restrict_iff' ht]
  filter_upwards with x using ht_eq x

中文:
定理 set整数egral_union_eq_left_of_对任意
  结论: (hs : 可测集 s) (ht : 可测集 t)
  证明: by
  apply setIntegral_union_eq_left_of_ae hs ht
  rw [ae_restrict_iff' ht]
  filter_upwards with x using ht_eq x

Depends on / 依赖: ae_restrict_iff, filter_upwards, ht_eq, setIntegral_union_eq_left_of_ae
-/
theorem setIntegral_union_eq_left_of_forall (hs : MeasurableSet s) (ht : MeasurableSet t)
    (ht_eq : forall x in t, f x = 0) : ∫ᵛ x in s union t, f x ∂[B; μ] = ∫ᵛ x in s, f x ∂[B; μ] := by
  apply setIntegral_union_eq_left_of_ae hs ht
  rw [ae_restrict_iff' ht]
  filter_upwards with x using ht_eq x

/--
theorem `setIntegral_eq_of_subset_of_ae_sdiff_eq_zero` / 定理 `setIntegral_eq_of_subset_of_ae_sdiff_eq_zero`

English:
theorem setIntegral_eq_of_subset_of_ae_sdiff_eq_zero
  statement: (hs : MeasurableSet s) (ht : MeasurableSet t)
  proof: by
  rwa [← union_sdiff_cancel hts, setIntegral_union_eq_left_of_ae hs (ht.diff hs)]

中文:
定理 set整数egral_eq_of_subset_of_ae_sdiff_eq_zero
  结论: (hs : 可测集 s) (ht : 可测集 t)
  证明: by
  rwa [← union_sdiff_cancel hts, setIntegral_union_eq_left_of_ae hs (ht.diff hs)]

Depends on / 依赖: ht.diff, setIntegral_union_eq_left_of_ae, union_sdiff_cancel
-/
theorem setIntegral_eq_of_subset_of_ae_sdiff_eq_zero (hs : MeasurableSet s) (ht : MeasurableSet t)
    (hts : s subseteq t) (h't : forallᵐ x ∂μ.variation.restrict (t \ s), f x = 0) :
    ∫ᵛ x in t, f x ∂[B; μ] = ∫ᵛ x in s, f x ∂[B; μ] := by
  rwa [← union_sdiff_cancel hts, setIntegral_union_eq_left_of_ae hs (ht.diff hs)]

/--
theorem `setIntegral_eq_of_subset_of_forall_sdiff_eq_zero` / 定理 `setIntegral_eq_of_subset_of_forall_sdiff_eq_zero`

English:
theorem setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
  proof: by
  apply setIntegral_eq_of_subset_of_ae_sdiff_eq_zero hs ht hts
  apply (ae_restrict_iff' (ht.diff hs)).2
  filter_upwards with x using h't x

中文:
定理 set整数egral_eq_of_subset_of_对任意_sdiff_eq_zero
  证明: by
  apply setIntegral_eq_of_subset_of_ae_sdiff_eq_zero hs ht hts
  apply (ae_restrict_iff' (ht.diff hs)).2
  filter_upwards with x using h't x

Depends on / 依赖: ae_restrict_iff, filter_upwards, ht.diff, setIntegral_eq_of_subset_of_ae_sdiff_eq_zero
-/
theorem setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
    (hs : MeasurableSet s) (ht : MeasurableSet t) (hts : s subseteq t)
    (h't : forall x in t \ s, f x = 0) : ∫ᵛ x in t, f x ∂[B; μ] = ∫ᵛ x in s, f x ∂[B; μ] := by
  apply setIntegral_eq_of_subset_of_ae_sdiff_eq_zero hs ht hts
  apply (ae_restrict_iff' (ht.diff hs)).2
  filter_upwards with x using h't x

/--
theorem `setIntegral_eq_integral_of_ae_compl_eq_zero` / 定理 `setIntegral_eq_integral_of_ae_compl_eq_zero`

English:
theorem setIntegral_eq_integral_of_ae_compl_eq_zero
  statement: (hs : MeasurableSet s)
  proof: by
  symm
  nth_rw 1 [← setIntegral_univ]
  apply setIntegral_eq_of_subset_of_ae_sdiff_eq_zero hs MeasurableSet.univ (subset_univ _)
  apply (ae_restrict_iff' (MeasurableSet.univ.diff hs)).2
  filter_upwards [h] with x hx h'x using hx h'x.2

中文:
定理 set整数egral_eq_integral_of_ae_compl_eq_zero
  结论: (hs : 可测集 s)
  证明: by
  symm
  nth_rw 1 [← setIntegral_univ]
  apply setIntegral_eq_of_subset_of_ae_sdiff_eq_zero hs MeasurableSet.univ (subset_univ _)
  apply (ae_restrict_iff' (MeasurableSet.univ.diff hs)).2
  filter_upwards [h] with x hx h'x using hx h'x.2

Depends on / 依赖: MeasurableSet, MeasurableSet.univ, MeasurableSet.univ.diff, ae_restrict_iff, filter_upwards, nth_rw, setIntegral_eq_of_subset_of_ae_sdiff_eq_zero, setIntegral_univ, subset_univ
-/
theorem setIntegral_eq_integral_of_ae_compl_eq_zero (hs : MeasurableSet s)
    (h : forallᵐ x ∂μ.variation, x ∉ s -> f x = 0) :
    ∫ᵛ x in s, f x ∂[B; μ] = ∫ᵛ x, f x ∂[B; μ] := by
  symm
  nth_rw 1 [← setIntegral_univ]
  apply setIntegral_eq_of_subset_of_ae_sdiff_eq_zero hs MeasurableSet.univ (subset_univ _)
  apply (ae_restrict_iff' (MeasurableSet.univ.diff hs)).2
  filter_upwards [h] with x hx h'x using hx h'x.2

/--
theorem `setIntegral_eq_integral_of_forall_compl_eq_zero` / 定理 `setIntegral_eq_integral_of_forall_compl_eq_zero`

English:
theorem setIntegral_eq_integral_of_forall_compl_eq_zero
  statement: (hs : MeasurableSet s)
  proof: setIntegral_eq_integral_of_ae_compl_eq_zero hs (Eventually.of_forall h)

中文:
定理 set整数egral_eq_integral_of_对任意_compl_eq_zero
  结论: (hs : 可测集 s)
  证明: setIntegral_eq_integral_of_ae_compl_eq_zero hs (Eventually.of_forall h)

Depends on / 依赖: Eventually, Eventually.of_forall, of_forall, setIntegral_eq_integral_of_ae_compl_eq_zero
-/
theorem setIntegral_eq_integral_of_forall_compl_eq_zero (hs : MeasurableSet s)
    (h : forall x, x ∉ s -> f x = 0) :
    ∫ᵛ x in s, f x ∂[B; μ] = ∫ᵛ x, f x ∂[B; μ] :=
  setIntegral_eq_integral_of_ae_compl_eq_zero hs (Eventually.of_forall h)

/--
theorem `setIntegral_const` / 定理 `setIntegral_const`

English:
theorem setIntegral_const
  statement: [CompleteSpace G] [IsFiniteMeasure (μ.variation.restrict s)]
  proof: by
  by_cases hs : MeasurableSet s
  · have : IsFiniteMeasure (μ.restrict s).variation := by
      rwa [variation_restrict hs]
    rw [integral_const]; rw [restrict_apply _ hs MeasurableSet.univ]; rw [univ_inter]
  · simp [setIntegral_eq_zero_of_not_measurableSet hs, μ.not_measurable hs]

@[simp]

中文:
定理 set整数egral_const
  结论: [完备空间 G] [是有限测度 (μ.variation.restrict s)]
  证明: by
  by_cases hs : MeasurableSet s
  · have : IsFiniteMeasure (μ.restrict s).variation := by
      rwa [variation_restrict hs]
    rw [integral_const]; rw [restrict_apply _ hs MeasurableSet.univ]; rw [univ_inter]
  · simp [setIntegral_eq_zero_of_not_measurableSet hs, μ.not_measurable hs]

@[simp]

Depends on / 依赖: IsFiniteMeasure, MeasurableSet, MeasurableSet.univ, integral_const, not_measurable, restrict, restrict_apply, setIntegral_eq_zero_of_not_measurableSet, univ_inter, variation, variation_restrict
-/
theorem setIntegral_const [CompleteSpace G] [IsFiniteMeasure (μ.variation.restrict s)]
    (c : E) : ∫ᵛ _ in s, c ∂[B; μ] = B c (μ s) := by
  by_cases hs : MeasurableSet s
  · have : IsFiniteMeasure (μ.restrict s).variation := by
      rwa [variation_restrict hs]
    rw [integral_const]; rw [restrict_apply _ hs MeasurableSet.univ]; rw [univ_inter]
  · simp [setIntegral_eq_zero_of_not_measurableSet hs, μ.not_measurable hs]

@[simp]
/--
theorem `integral_indicator_const` / 定理 `integral_indicator_const`

English:
theorem integral_indicator_const
  statement: [CompleteSpace G]
  proof: by
  rw [integral_indicator s_meas]; rw [← setIntegral_const]

中文:
定理 integral_indicator_const
  结论: [完备空间 G]
  证明: by
  rw [integral_indicator s_meas]; rw [← setIntegral_const]

Depends on / 依赖: integral_indicator, s_meas, setIntegral_const
-/
theorem integral_indicator_const [CompleteSpace G]
    (e : E) ⦃s : Set X⦄ [IsFiniteMeasure (μ.variation.restrict s)]
    (s_meas : MeasurableSet s) :
    ∫ᵛ x, s.indicator (fun _ : X => e) x ∂[B; μ] = B e (μ s) := by
  rw [integral_indicator s_meas]; rw [← setIntegral_const]

/--
theorem `setIntegral_map` / 定理 `setIntegral_map`

English:
theorem setIntegral_map
  statement: {β : Type*} [MeasurableSpace β]
  proof: by
  rw [restrict_map μ hφ hs]; rw [integral_map hφ hfm hfi'.integrableOn]

中文:
定理 set整数egral_map
  结论: {β : 类型} [可测空间 β]
  证明: by
  rw [restrict_map μ hφ hs]; rw [integral_map hφ hfm hfi'.integrableOn]

Depends on / 依赖: integrableOn, integral_map, restrict_map
-/
theorem setIntegral_map {β : Type*} [MeasurableSpace β]
    {φ : X -> β} (hφ : Measurable φ) {f : β -> E} {s : Set β} (hs : MeasurableSet s)
    (hfm : AEStronglyMeasurable f ((μ.restrict (φ ⁻¹' s)).variation.map φ))
    (hfi' : μ.Integrable (f ∘ φ)) :
    ∫ᵛ y in s, f y ∂[B; μ.map φ] = ∫ᵛ x in φ ⁻¹' s, f (φ x) ∂[B; μ] := by
  rw [restrict_map μ hφ hs]; rw [integral_map hφ hfm hfi'.integrableOn]

/--
theorem `_root_.MeasurableEmbedding.setIntegral_map_vectorMeasure` / 定理 `_root_.MeasurableEmbedding.setIntegral_map_vectorMeasure`

English:
theorem _root_.MeasurableEmbedding.setIntegral_map_vectorMeasure
  statement: {β : Type*} [MeasurableSpace β]
  proof: by
  rw [restrict_map μ hφ.measurable hs]; rw [hφ.integral_map_vectorMeasure]

中文:
定理 _root_.可测嵌入.set整数egral_map_vectorMeasure
  结论: {β : 类型} [可测空间 β]
  证明: by
  rw [restrict_map μ hφ.measurable hs]; rw [hφ.integral_map_vectorMeasure]

Depends on / 依赖: integral_map_vectorMeasure, measurable, restrict_map
-/
theorem _root_.MeasurableEmbedding.setIntegral_map_vectorMeasure {β : Type*} [MeasurableSpace β]
    {φ : X -> β} {f : β -> E} (hφ : MeasurableEmbedding φ) {s : Set β} (hs : MeasurableSet s) :
    ∫ᵛ y in s, f y ∂[B; μ.map φ] = ∫ᵛ x in φ ⁻¹' s, f (φ x) ∂[B; μ] := by
  rw [restrict_map μ hφ.measurable hs]; rw [hφ.integral_map_vectorMeasure]

/--
theorem `_root_.Topology.IsClosedEmbedding.setIntegral_map_vectorMeasure` / 定理 `_root_.Topology.IsClosedEmbedding.setIntegral_map_vectorMeasure`

English:
theorem _root_.Topology.IsClosedEmbedding.setIntegral_map_vectorMeasure
  proof: hφ.measurableEmbedding.setIntegral_map_vectorMeasure hs

中文:
定理 _root_.拓扑.是闭嵌入.set整数egral_map_vectorMeasure
  证明: hφ.measurableEmbedding.setIntegral_map_vectorMeasure hs

Depends on / 依赖: measurableEmbedding, measurableEmbedding.setIntegral_map_vectorMeasure, setIntegral_map_vectorMeasure
-/
theorem _root_.Topology.IsClosedEmbedding.setIntegral_map_vectorMeasure
    [TopologicalSpace X] [BorelSpace X] {β : Type*}
    [MeasurableSpace β] [TopologicalSpace β] [BorelSpace β] {φ : X -> β} {f : β -> E} {s : Set β}
    (hs : MeasurableSet s) (hφ : IsClosedEmbedding φ) :
    ∫ᵛ y in s, f y ∂[B; μ.map φ] = ∫ᵛ x in φ ⁻¹' s, f (φ x) ∂[B; μ] :=
  hφ.measurableEmbedding.setIntegral_map_vectorMeasure hs

/--
theorem `setIntegral_map_equiv` / 定理 `setIntegral_map_equiv`

English:
theorem setIntegral_map_equiv
  statement: {β : Type*} [MeasurableSpace β] {e : X ≃ᵐ β} {f : β -> E} {s : Set β}
  proof: e.measurableEmbedding.setIntegral_map_vectorMeasure hs

中文:
定理 set整数egral_map_equiv
  结论: {β : 类型} [可测空间 β] {e : X ≃ᵐ β} {f : β -> E} {s : 集合 β}
  证明: e.measurableEmbedding.setIntegral_map_vectorMeasure hs

Depends on / 依赖: e.measurableEmbedding.setIntegral_map_vectorMeasure, measurableEmbedding, setIntegral_map_vectorMeasure
-/
theorem setIntegral_map_equiv {β : Type*} [MeasurableSpace β] {e : X ≃ᵐ β} {f : β -> E} {s : Set β}
    (hs : MeasurableSet s) :
    ∫ᵛ y in s, f y ∂[B; μ.map e] = ∫ᵛ x in e ⁻¹' s, f (e x) ∂[B; μ] :=
  e.measurableEmbedding.setIntegral_map_vectorMeasure hs

/--
theorem `continuousLinearMap_apply_integral` / 定理 `continuousLinearMap_apply_integral`

English:
theorem continuousLinearMap_apply_integral
  proof: by
  apply hf.induction (P := fun f => C (∫ᵛ y, f y ∂[B; μ]) = ∫ᵛ y, f y ∂[((compL Real F G H C) ∘L B); μ])
  · intro c s hs hc
    have : IsFiniteMeasure (μ.variation.restrict s) := ⟨by simpa⟩
    simp [integral_indicator_const _ hs]
  · intro f g _ f_int g_int hf hg
    simp only [Pi.add_apply]
    simp [integral_fun_add, f_int, g_int, hf, hg]
  · apply isClosed_eq
    · apply C.continuous.comp continuous_integral
    · exact continuous_integral
  · intro f g hfg _ hf
    rw [← integral_congr_ae hfg]; rw [← integral_congr_ae hfg]; rw [hf]

中文:
定理 continuousLinearMap_apply_integral
  证明: by
  apply hf.induction (P := fun f => C (∫ᵛ y, f y ∂[B; μ]) = ∫ᵛ y, f y ∂[((compL Real F G H C) ∘L B); μ])
  · intro c s hs hc
    have : IsFiniteMeasure (μ.variation.restrict s) := ⟨by simpa⟩
    simp [integral_indicator_const _ hs]
  · intro f g _ f_int g_int hf hg
    simp only [Pi.add_apply]
    simp [integral_fun_add, f_int, g_int, hf, hg]
  · apply isClosed_eq
    · apply C.continuous.comp continuous_integral
    · exact continuous_integral
  · intro f g hfg _ hf
    rw [← integral_congr_ae hfg]; rw [← integral_congr_ae hfg]; rw [hf]

Depends on / 依赖: C.continuous.comp, IsFiniteMeasure, Pi.add_apply, add_apply, continuous, continuous_integral, f_int, g_int, hf.induction, integral_congr_ae, integral_fun_add, integral_indicator_const, isClosed_eq, restrict, variation, variation.restrict
-/
theorem continuousLinearMap_apply_integral
    [CompleteSpace G] [CompleteSpace H]
    {C : G ->L[Real] H} (hf : Integrable f μ.variation) :
    C (∫ᵛ y, f y ∂[B; μ]) = ∫ᵛ y, f y ∂[((compL Real F G H C) ∘L B); μ] := by
  apply hf.induction (P := fun f => C (∫ᵛ y, f y ∂[B; μ]) = ∫ᵛ y, f y ∂[((compL Real F G H C) ∘L B); μ])
  · intro c s hs hc
    have : IsFiniteMeasure (μ.variation.restrict s) := ⟨by simpa⟩
    simp [integral_indicator_const _ hs]
  · intro f g _ f_int g_int hf hg
    simp only [Pi.add_apply]
    simp [integral_fun_add, f_int, g_int, hf, hg]
  · apply isClosed_eq
    · apply C.continuous.comp continuous_integral
    · exact continuous_integral
  · intro f g hfg _ hf
    rw [← integral_congr_ae hfg]; rw [← integral_congr_ae hfg]; rw [hf]

/--
theorem `integral_continuousLinearMap_comp` / 定理 `integral_continuousLinearMap_comp`

English:
theorem integral_continuousLinearMap_comp
  proof: by
  by_cases hG : CompleteSpace G; swap
  · simp [integral_of_not_completeSpace hG]
  apply hf.induction (P := fun f => ∫ᵛ y, C (f y) ∂[B; μ] = ∫ᵛ y, f y ∂[B ∘L C; μ])
  · intro c s hs hc
    have : IsFiniteMeasure (μ.variation.restrict s) := ⟨by simpa⟩
    rw [integral_indicator_const _ hs]
    have : (fun y => C (s.indicator (fun x => c) y)) = s.indicator (fun x => C c) := by
      ext; simp only [indicator]; grind
    simp_rw [this]
    rw [integral_indicator_const _ hs]
    rfl
  · intro f g _ f_int g_int hf hg
    simp only [Pi.add_apply, _root_.map_add]
    rw [integral_fun_add (C.integrable_comp f_int) (C.integrable_comp g_int)]; rw [hf]; rw [hg]; rw [integral_fun_add f_int g_int]
  · apply isClosed_eq
    · have I (f : Lp H 1 μ.variation) : ∫ᵛ x, C (f x) ∂[B; μ] = ∫ᵛ x, (C.compLp f) x ∂[B; μ] :=
        (integral_congr_ae (coeFn_compLp _ _)).symm
      simp_rw [I]
      exact continuous_integral.comp (C.compLpL 1 μ.variation).continuous
    · exact continuous_integral
  · intro f g hfg _ hf
    have : forallᵐ x ∂μ.variation, C (f x) = C (g x) := by
      filter_upwards [hfg] with x hx using by simp [hx]
    rw [← integral_congr_ae hfg]; rw [← integral_congr_ae this]; rw [hf]

中文:
定理 integral_continuousLinearMap_comp
  证明: by
  by_cases hG : CompleteSpace G; swap
  · simp [integral_of_not_completeSpace hG]
  apply hf.induction (P := fun f => ∫ᵛ y, C (f y) ∂[B; μ] = ∫ᵛ y, f y ∂[B ∘L C; μ])
  · intro c s hs hc
    have : IsFiniteMeasure (μ.variation.restrict s) := ⟨by simpa⟩
    rw [integral_indicator_const _ hs]
    have : (fun y => C (s.indicator (fun x => c) y)) = s.indicator (fun x => C c) := by
      ext; simp only [indicator]; grind
    simp_rw [this]
    rw [integral_indicator_const _ hs]
    rfl
  · intro f g _ f_int g_int hf hg
    simp only [Pi.add_apply, _root_.map_add]
    rw [integral_fun_add (C.integrable_comp f_int) (C.integrable_comp g_int)]; rw [hf]; rw [hg]; rw [integral_fun_add f_int g_int]
  · apply isClosed_eq
    · have I (f : Lp H 1 μ.variation) : ∫ᵛ x, C (f x) ∂[B; μ] = ∫ᵛ x, (C.compLp f) x ∂[B; μ] :=
        (integral_congr_ae (coeFn_compLp _ _)).symm
      simp_rw [I]
      exact continuous_integral.comp (C.compLpL 1 μ.variation).continuous
    · exact continuous_integral
  · intro f g hfg _ hf
    have : forallᵐ x ∂μ.variation, C (f x) = C (g x) := by
      filter_upwards [hfg] with x hx using by simp [hx]
    rw [← integral_congr_ae hfg]; rw [← integral_congr_ae this]; rw [hf]

Depends on / 依赖: CompleteSpace, IsFiniteMeasure, Pi.add_, add_, f_int, g_int, hf.induction, indicator, integral_indicator_const, integral_of_not_completeSpace, restrict, s.indicator, simp_rw, variation, variation.restrict
-/
theorem integral_continuousLinearMap_comp
    {f : X -> H} {C : H ->L[Real] E} (hf : Integrable f μ.variation) :
    ∫ᵛ y, C (f y) ∂[B; μ] = ∫ᵛ y, f y ∂[B ∘L C; μ] := by
  by_cases hG : CompleteSpace G; swap
  · simp [integral_of_not_completeSpace hG]
  apply hf.induction (P := fun f => ∫ᵛ y, C (f y) ∂[B; μ] = ∫ᵛ y, f y ∂[B ∘L C; μ])
  · intro c s hs hc
    have : IsFiniteMeasure (μ.variation.restrict s) := ⟨by simpa⟩
    rw [integral_indicator_const _ hs]
    have : (fun y => C (s.indicator (fun x => c) y)) = s.indicator (fun x => C c) := by
      ext; simp only [indicator]; grind
    simp_rw [this]
    rw [integral_indicator_const _ hs]
    rfl
  · intro f g _ f_int g_int hf hg
    simp only [Pi.add_apply, _root_.map_add]
    rw [integral_fun_add (C.integrable_comp f_int) (C.integrable_comp g_int)]; rw [hf]; rw [hg]; rw [integral_fun_add f_int g_int]
  · apply isClosed_eq
    · have I (f : Lp H 1 μ.variation) : ∫ᵛ x, C (f x) ∂[B; μ] = ∫ᵛ x, (C.compLp f) x ∂[B; μ] :=
        (integral_congr_ae (coeFn_compLp _ _)).symm
      simp_rw [I]
      exact continuous_integral.comp (C.compLpL 1 μ.variation).continuous
    · exact continuous_integral
  · intro f g hfg _ hf
    have : forallᵐ x ∂μ.variation, C (f x) = C (g x) := by
      filter_upwards [hfg] with x hx using by simp [hx]
    rw [← integral_congr_ae hfg]; rw [← integral_congr_ae this]; rw [hf]

/--
theorem `enorm_setIntegral_le_of_enorm_le_const_ae` / 定理 `enorm_setIntegral_le_of_enorm_le_const_ae`

English:
theorem enorm_setIntegral_le_of_enorm_le_const_ae
  statement: {C : Real>=0∞}
  proof: by
  by_cases hs : MeasurableSet s; swap
  · simp [setIntegral_eq_zero_of_not_measurableSet hs]
  rw [← variation_restrict hs] at hC
  apply (enorm_integral_le_of_enorm_le_const hC).trans
  rw [variation_restrict hs]; rw [Measure.restrict_apply MeasurableSet.univ]
  simp

中文:
定理 enorm_set整数egral_le_of_enorm_le_const_ae
  结论: {C : 实数>=0∞}
  证明: by
  by_cases hs : MeasurableSet s; swap
  · simp [setIntegral_eq_zero_of_not_measurableSet hs]
  rw [← variation_restrict hs] at hC
  apply (enorm_integral_le_of_enorm_le_const hC).trans
  rw [variation_restrict hs]; rw [Measure.restrict_apply MeasurableSet.univ]
  simp

Depends on / 依赖: MeasurableSet, MeasurableSet.univ, Measure, Measure.restrict_apply, enorm_integral_le_of_enorm_le_const, restrict_apply, setIntegral_eq_zero_of_not_measurableSet, variation_restrict
-/
theorem enorm_setIntegral_le_of_enorm_le_const_ae {C : Real>=0∞}
    (hC : forallᵐ x ∂μ.variation.restrict s, ‖f x‖ₑ <= C) :
    ‖∫ᵛ x in s, f x ∂[B; μ]‖ₑ <= C * ‖B‖ₑ * μ.variation s := by
  by_cases hs : MeasurableSet s; swap
  · simp [setIntegral_eq_zero_of_not_measurableSet hs]
  rw [← variation_restrict hs] at hC
  apply (enorm_integral_le_of_enorm_le_const hC).trans
  rw [variation_restrict hs]; rw [Measure.restrict_apply MeasurableSet.univ]
  simp

/--
theorem `enorm_setIntegral_le_of_enorm_le_const` / 定理 `enorm_setIntegral_le_of_enorm_le_const`

English:
theorem enorm_setIntegral_le_of_enorm_le_const
  statement: {C : Real>=0∞}
  proof: by
  by_cases hs : MeasurableSet s; swap
  · simp [setIntegral_eq_zero_of_not_measurableSet hs]
  apply enorm_setIntegral_le_of_enorm_le_const_ae
  apply (ae_restrict_iff' hs).2
  filter_upwards with x using hC x

中文:
定理 enorm_set整数egral_le_of_enorm_le_const
  结论: {C : 实数>=0∞}
  证明: by
  by_cases hs : MeasurableSet s; swap
  · simp [setIntegral_eq_zero_of_not_measurableSet hs]
  apply enorm_setIntegral_le_of_enorm_le_const_ae
  apply (ae_restrict_iff' hs).2
  filter_upwards with x using hC x

Depends on / 依赖: MeasurableSet, ae_restrict_iff, enorm_setIntegral_le_of_enorm_le_const_ae, filter_upwards, setIntegral_eq_zero_of_not_measurableSet
-/
theorem enorm_setIntegral_le_of_enorm_le_const {C : Real>=0∞}
    (hC : forall x in s, ‖f x‖ₑ <= C) :
    ‖∫ᵛ x in s, f x ∂[B; μ]‖ₑ <= C * ‖B‖ₑ * μ.variation s := by
  by_cases hs : MeasurableSet s; swap
  · simp [setIntegral_eq_zero_of_not_measurableSet hs]
  apply enorm_setIntegral_le_of_enorm_le_const_ae
  apply (ae_restrict_iff' hs).2
  filter_upwards with x using hC x

/--
theorem `norm_setIntegral_le_of_norm_le_const_ae` / 定理 `norm_setIntegral_le_of_norm_le_const_ae`

English:
theorem norm_setIntegral_le_of_norm_le_const_ae
  statement: {C : Real}
  proof: by
  by_cases hs : MeasurableSet s; swap
  · simp only [setIntegral_eq_zero_of_not_measurableSet hs, norm_zero]
    by_cases h's : μ.variation s = 0
    · simp [Measure.real, h's]
    · have : NeBot (ae (μ.variation.restrict s)) := by simpa using h's
      obtain ⟨x, hx⟩ : exists x, ‖f x‖ <= C := hC.exists
      have : 0 <= C := le_trans (norm_nonneg _) hx
      positivity
  rw [← variation_restrict hs] at hC h
  apply (norm_integral_le_of_norm_le_const hC).trans_eq
  simp [variation_restrict hs]

中文:
定理 norm_set整数egral_le_of_norm_le_const_ae
  结论: {C : 实数}
  证明: by
  by_cases hs : MeasurableSet s; swap
  · simp only [setIntegral_eq_zero_of_not_measurableSet hs, norm_zero]
    by_cases h's : μ.variation s = 0
    · simp [Measure.real, h's]
    · have : NeBot (ae (μ.variation.restrict s)) := by simpa using h's
      obtain ⟨x, hx⟩ : exists x, ‖f x‖ <= C := hC.exists
      have : 0 <= C := le_trans (norm_nonneg _) hx
      positivity
  rw [← variation_restrict hs] at hC h
  apply (norm_integral_le_of_norm_le_const hC).trans_eq
  simp [variation_restrict hs]

Depends on / 依赖: MeasurableSet, Measure, Measure.real, hC.exists, le_trans, norm_integral_le_of_norm_le_const, norm_nonneg, norm_zero, restrict, setIntegral_eq_zero_of_not_measurableSet, trans_eq, variation, variation.restrict, variation_restrict
-/
theorem norm_setIntegral_le_of_norm_le_const_ae {C : Real}
    [h : IsFiniteMeasure (μ.variation.restrict s)]
    (hC : forallᵐ x ∂μ.variation.restrict s, ‖f x‖ <= C) :
    ‖∫ᵛ x in s, f x ∂[B; μ]‖ <= C * ‖B‖ * μ.variation.real s := by
  by_cases hs : MeasurableSet s; swap
  · simp only [setIntegral_eq_zero_of_not_measurableSet hs, norm_zero]
    by_cases h's : μ.variation s = 0
    · simp [Measure.real, h's]
    · have : NeBot (ae (μ.variation.restrict s)) := by simpa using h's
      obtain ⟨x, hx⟩ : exists x, ‖f x‖ <= C := hC.exists
      have : 0 <= C := le_trans (norm_nonneg _) hx
      positivity
  rw [← variation_restrict hs] at hC h
  apply (norm_integral_le_of_norm_le_const hC).trans_eq
  simp [variation_restrict hs]

/--
theorem `norm_setIntegral_le_of_norm_le_const` / 定理 `norm_setIntegral_le_of_norm_le_const`

English:
theorem norm_setIntegral_le_of_norm_le_const
  statement: {C : Real}
  proof: by
  rcases eq_empty_or_nonempty s with rfl | ⟨x, hx⟩
  · simp
  by_cases hs : MeasurableSet s; swap
  · simp only [setIntegral_eq_zero_of_not_measurableSet hs, norm_zero]
    have : 0 <= C := le_trans (norm_nonneg _) (hC x hx)
    positivity
  apply norm_setIntegral_le_of_norm_le_const_ae
  filter_upwards [ae_restrict_mem hs] with x hx using hC x hx

中文:
定理 norm_set整数egral_le_of_norm_le_const
  结论: {C : 实数}
  证明: by
  rcases eq_empty_or_nonempty s with rfl | ⟨x, hx⟩
  · simp
  by_cases hs : MeasurableSet s; swap
  · simp only [setIntegral_eq_zero_of_not_measurableSet hs, norm_zero]
    have : 0 <= C := le_trans (norm_nonneg _) (hC x hx)
    positivity
  apply norm_setIntegral_le_of_norm_le_const_ae
  filter_upwards [ae_restrict_mem hs] with x hx using hC x hx

Depends on / 依赖: MeasurableSet, ae_restrict_mem, eq_empty_or_nonempty, filter_upwards, le_trans, norm_nonneg, norm_setIntegral_le_of_norm_le_const_ae, norm_zero, setIntegral_eq_zero_of_not_measurableSet
-/
theorem norm_setIntegral_le_of_norm_le_const {C : Real}
    [h : IsFiniteMeasure (μ.variation.restrict s)]
    (hC : forall x in s, ‖f x‖ <= C) :
    ‖∫ᵛ x in s, f x ∂[B; μ]‖ <= C * ‖B‖ * μ.variation.real s := by
  rcases eq_empty_or_nonempty s with rfl | ⟨x, hx⟩
  · simp
  by_cases hs : MeasurableSet s; swap
  · simp only [setIntegral_eq_zero_of_not_measurableSet hs, norm_zero]
    have : 0 <= C := le_trans (norm_nonneg _) (hC x hx)
    positivity
  apply norm_setIntegral_le_of_norm_le_const_ae
  filter_upwards [ae_restrict_mem hs] with x hx using hC x hx

/--
theorem `enorm_setIntegral_le_lintegral_enorm` / 定理 `enorm_setIntegral_le_lintegral_enorm`

English:
theorem enorm_setIntegral_le_lintegral_enorm
  proof: by
  grw [enorm_integral_le_lintegral_enorm, variation_restrict_le]

中文:
定理 enorm_set整数egral_le_lintegral_enorm
  证明: by
  grw [enorm_integral_le_lintegral_enorm, variation_restrict_le]

Depends on / 依赖: enorm_integral_le_lintegral_enorm, variation_restrict_le
-/
theorem enorm_setIntegral_le_lintegral_enorm :
    ‖∫ᵛ x in s, f x ∂[B; μ]‖ₑ <= ‖B‖ₑ * ∫⁻ x in s, ‖f x‖ₑ ∂μ.variation := by
  grw [enorm_integral_le_lintegral_enorm, variation_restrict_le]

/--
theorem `enorm_setIntegral_le_lintegral_enorm_transpose` / 定理 `enorm_setIntegral_le_lintegral_enorm_transpose`

English:
theorem enorm_setIntegral_le_lintegral_enorm_transpose
  proof: by
  grw [enorm_integral_le_lintegral_enorm_transpose, transpose_restrict,variation_restrict_le]

中文:
定理 enorm_set整数egral_le_lintegral_enorm_transpose
  证明: by
  grw [enorm_integral_le_lintegral_enorm_transpose, transpose_restrict,variation_restrict_le]

Depends on / 依赖: enorm_integral_le_lintegral_enorm_transpose, transpose_restrict, variation_restrict_le
-/
theorem enorm_setIntegral_le_lintegral_enorm_transpose :
    ‖∫ᵛ x in s, f x ∂[B; μ]‖ₑ <= ∫⁻ x in s, ‖f x‖ₑ ∂(μ.transpose B).variation := by
  grw [enorm_integral_le_lintegral_enorm_transpose, transpose_restrict,variation_restrict_le]

/--
theorem `hasSum_setIntegral_iUnion_nat` / 定理 `hasSum_setIntegral_iUnion_nat`

English:
theorem hasSum_setIntegral_iUnion_nat
  statement: {s : Nat -> Set X}
  proof: by
  by_cases hG : CompleteSpace G; swap
  · simp [integral_of_not_completeSpace hG]
  have I : ∑' i, ‖B‖ₑ * ∫⁻ x in s i, ‖f x‖ₑ ∂μ.variation < ∞ := calc
    ∑' i, ‖B‖ₑ * ∫⁻ x in s i, ‖f x‖ₑ ∂μ.variation
    _ = ‖B‖ₑ * ∫⁻ x in (⋃ i, s i), ‖f x‖ₑ ∂μ.variation := by
      rw [ENNReal.tsum_mul_left]; rw [lintegral_iUnion hm hd]
    _ < ∞ := by
      simp only [VectorMeasure.IntegrableOn, VectorMeasure.Integrable,
        variation_restrict (MeasurableSet.iUnion hm)] at hfi
      exact ENNReal.mul_lt_top (by simp) hfi.2
  have : Summable (fun n => ∫ᵛ x in s n, f x ∂[B; μ]) := by
    apply Summable.of_enorm (lt_of_le_of_lt _ I).ne
    gcongr
    exact enorm_setIntegral_le_lintegral_enorm
  apply (Summable.hasSum_iff_tendsto_nat this).2
  simp_rw [tendsto_iff_edist_tendsto_0, edist_eq_enorm_sub, enorm_sub_rev]
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (ENNReal.tendsto_sum_nat_add _ I.ne) (by positivity) (fun N => ?_)
  have : ⋃ n, s n = (⋃ n in Finset.range N, s n) union (⋃ n, s (n + N)) := by
    ext x
    have : (exists i, x in s (i + N)) ↔ (exists i >= N, x in s i) :=
      ⟨fun ⟨i, hi⟩ => ⟨i + N, by grind⟩, fun ⟨i, hi, h'i⟩ => ⟨i - N, by grind⟩⟩
    simp only [mem_iUnion, Finset.mem_range, mem_union, exists_prop, this, ge_iff_le]
    grind
  rw [this]; rw [setIntegral_union]; rotate_left
  · simp only [Finset.mem_range, disjoint_iUnion_right, disjoint_iUnion_left]
    intro i j hi
    apply hd (by grind)
  · apply MeasurableSet.biUnion (Finset.countable_toSet _) (fun i hi => hm i)
  · apply MeasurableSet.iUnion (fun i => hm _)
  · apply hfi.mono (MeasurableSet.iUnion hm) (by simp [subset_iUnion s])
  · apply hfi.mono (MeasurableSet.iUnion hm) (by simp [subset_iUnion s])
  rw [setIntegral_biUnion_finset]; rotate_left
  · exact fun i hi => hm i
  · exact fun i hi j hj hij => hd hij
  · exact fun i hi => hfi.mono (MeasurableSet.iUnion hm) (by simp [subset_iUnion s])
  simp only [add_sub_cancel_left]
  apply enorm_setIntegral_le_lintegral_enorm.trans_eq
  rw [lintegral_iUnion (fun i => hm _)]; rw [ENNReal.tsum_mul_left]
  exact fun i j hij => hd (by grind)

中文:
定理 hasSum_set整数egral_iUnion_nat
  结论: {s : 自然数 -> 集合 X}
  证明: by
  by_cases hG : CompleteSpace G; swap
  · simp [integral_of_not_completeSpace hG]
  have I : ∑' i, ‖B‖ₑ * ∫⁻ x in s i, ‖f x‖ₑ ∂μ.variation < ∞ := calc
    ∑' i, ‖B‖ₑ * ∫⁻ x in s i, ‖f x‖ₑ ∂μ.variation
    _ = ‖B‖ₑ * ∫⁻ x in (⋃ i, s i), ‖f x‖ₑ ∂μ.variation := by
      rw [ENNReal.tsum_mul_left]; rw [lintegral_iUnion hm hd]
    _ < ∞ := by
      simp only [VectorMeasure.IntegrableOn, VectorMeasure.Integrable,
        variation_restrict (MeasurableSet.iUnion hm)] at hfi
      exact ENNReal.mul_lt_top (by simp) hfi.2
  have : Summable (fun n => ∫ᵛ x in s n, f x ∂[B; μ]) := by
    apply Summable.of_enorm (lt_of_le_of_lt _ I).ne
    gcongr
    exact enorm_setIntegral_le_lintegral_enorm
  apply (Summable.hasSum_iff_tendsto_nat this).2
  simp_rw [tendsto_iff_edist_tendsto_0, edist_eq_enorm_sub, enorm_sub_rev]
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (ENNReal.tendsto_sum_nat_add _ I.ne) (by positivity) (fun N => ?_)
  have : ⋃ n, s n = (⋃ n in Finset.range N, s n) union (⋃ n, s (n + N)) := by
    ext x
    have : (exists i, x in s (i + N)) ↔ (exists i >= N, x in s i) :=
      ⟨fun ⟨i, hi⟩ => ⟨i + N, by grind⟩, fun ⟨i, hi, h'i⟩ => ⟨i - N, by grind⟩⟩
    simp only [mem_iUnion, Finset.mem_range, mem_union, exists_prop, this, ge_iff_le]
    grind
  rw [this]; rw [setIntegral_union]; rotate_left
  · simp only [Finset.mem_range, disjoint_iUnion_right, disjoint_iUnion_left]
    intro i j hi
    apply hd (by grind)
  · apply MeasurableSet.biUnion (Finset.countable_toSet _) (fun i hi => hm i)
  · apply MeasurableSet.iUnion (fun i => hm _)
  · apply hfi.mono (MeasurableSet.iUnion hm) (by simp [subset_iUnion s])
  · apply hfi.mono (MeasurableSet.iUnion hm) (by simp [subset_iUnion s])
  rw [setIntegral_biUnion_finset]; rotate_left
  · exact fun i hi => hm i
  · exact fun i hi j hj hij => hd hij
  · exact fun i hi => hfi.mono (MeasurableSet.iUnion hm) (by simp [subset_iUnion s])
  simp only [add_sub_cancel_left]
  apply enorm_setIntegral_le_lintegral_enorm.trans_eq
  rw [lintegral_iUnion (fun i => hm _)]; rw [ENNReal.tsum_mul_left]
  exact fun i j hij => hd (by grind)
-/
private theorem hasSum_setIntegral_iUnion_nat {s : Nat -> Set X}
    (hm : forall i, MeasurableSet (s i)) (hd : Pairwise (Disjoint on s))
    (hfi : μ.IntegrableOn f (⋃ i, s i)) :
    HasSum (fun n => ∫ᵛ x in s n, f x ∂[B; μ]) (∫ᵛ x in ⋃ n, s n, f x ∂[B; μ]) := by
  by_cases hG : CompleteSpace G; swap
  · simp [integral_of_not_completeSpace hG]
  have I : ∑' i, ‖B‖ₑ * ∫⁻ x in s i, ‖f x‖ₑ ∂μ.variation < ∞ := calc
    ∑' i, ‖B‖ₑ * ∫⁻ x in s i, ‖f x‖ₑ ∂μ.variation
    _ = ‖B‖ₑ * ∫⁻ x in (⋃ i, s i), ‖f x‖ₑ ∂μ.variation := by
      rw [ENNReal.tsum_mul_left]; rw [lintegral_iUnion hm hd]
    _ < ∞ := by
      simp only [VectorMeasure.IntegrableOn, VectorMeasure.Integrable,
        variation_restrict (MeasurableSet.iUnion hm)] at hfi
      exact ENNReal.mul_lt_top (by simp) hfi.2
  have : Summable (fun n => ∫ᵛ x in s n, f x ∂[B; μ]) := by
    apply Summable.of_enorm (lt_of_le_of_lt _ I).ne
    gcongr
    exact enorm_setIntegral_le_lintegral_enorm
  apply (Summable.hasSum_iff_tendsto_nat this).2
  simp_rw [tendsto_iff_edist_tendsto_0, edist_eq_enorm_sub, enorm_sub_rev]
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (ENNReal.tendsto_sum_nat_add _ I.ne) (by positivity) (fun N => ?_)
  have : ⋃ n, s n = (⋃ n in Finset.range N, s n) union (⋃ n, s (n + N)) := by
    ext x
    have : (exists i, x in s (i + N)) ↔ (exists i >= N, x in s i) :=
      ⟨fun ⟨i, hi⟩ => ⟨i + N, by grind⟩, fun ⟨i, hi, h'i⟩ => ⟨i - N, by grind⟩⟩
    simp only [mem_iUnion, Finset.mem_range, mem_union, exists_prop, this, ge_iff_le]
    grind
  rw [this]; rw [setIntegral_union]; rotate_left
  · simp only [Finset.mem_range, disjoint_iUnion_right, disjoint_iUnion_left]
    intro i j hi
    apply hd (by grind)
  · apply MeasurableSet.biUnion (Finset.countable_toSet _) (fun i hi => hm i)
  · apply MeasurableSet.iUnion (fun i => hm _)
  · apply hfi.mono (MeasurableSet.iUnion hm) (by simp [subset_iUnion s])
  · apply hfi.mono (MeasurableSet.iUnion hm) (by simp [subset_iUnion s])
  rw [setIntegral_biUnion_finset]; rotate_left
  · exact fun i hi => hm i
  · exact fun i hi j hj hij => hd hij
  · exact fun i hi => hfi.mono (MeasurableSet.iUnion hm) (by simp [subset_iUnion s])
  simp only [add_sub_cancel_left]
  apply enorm_setIntegral_le_lintegral_enorm.trans_eq
  rw [lintegral_iUnion (fun i => hm _)]; rw [ENNReal.tsum_mul_left]
  exact fun i j hij => hd (by grind)

/--
theorem `hasSum_setIntegral_iUnion` / 定理 `hasSum_setIntegral_iUnion`

English:
theorem hasSum_setIntegral_iUnion
  statement: {ι : Type*} [Countable ι] {s : ι -> Set X}
  proof: by
  rcases finite_or_infinite ι with hι | hι
  · let : Fintype ι := Fintype.ofFinite ι
    have : ∫ᵛ x in ⋃ n, s n, f x ∂[B; μ] = ∑ i, ∫ᵛ x in s i, f x ∂[B; μ] := by
      rw [setIntegral_iUnion_fintype hm hd (fun i => ?_)]
      exact hfi.mono (MeasurableSet.iUnion hm) (by simp [subset_iUnion s])
    rw [this]
    apply hasSum_fintype
  obtain ⟨e⟩ : Nonempty (ι ≃ Nat) := nonempty_equiv_of_countable
  rw [← e.symm.surjective.iUnion_comp]; rw [← e.symm.hasSum_iff]
  apply hasSum_setIntegral_iUnion_nat (fun i => hm _) (fun i j hij => hd (by simp [hij]))
  rwa [e.symm.surjective.iUnion_comp]

中文:
定理 hasSum_set整数egral_iUnion
  结论: {ι : 类型} [可数 ι] {s : ι -> 集合 X}
  证明: by
  rcases finite_or_infinite ι with hι | hι
  · let : Fintype ι := Fintype.ofFinite ι
    have : ∫ᵛ x in ⋃ n, s n, f x ∂[B; μ] = ∑ i, ∫ᵛ x in s i, f x ∂[B; μ] := by
      rw [setIntegral_iUnion_fintype hm hd (fun i => ?_)]
      exact hfi.mono (MeasurableSet.iUnion hm) (by simp [subset_iUnion s])
    rw [this]
    apply hasSum_fintype
  obtain ⟨e⟩ : Nonempty (ι ≃ Nat) := nonempty_equiv_of_countable
  rw [← e.symm.surjective.iUnion_comp]; rw [← e.symm.hasSum_iff]
  apply hasSum_setIntegral_iUnion_nat (fun i => hm _) (fun i j hij => hd (by simp [hij]))
  rwa [e.symm.surjective.iUnion_comp]

Depends on / 依赖: Fintype, Fintype.ofFinite, MeasurableSet, MeasurableSet.iUnion, Nonempty, e.symm.hasSum_iff, e.symm.surjective.iUnion_comp, finite_or_infinite, hasSum_fintype, hasSum_iff, hasSum_setIntegral_iUnion_nat, hfi.mono, iUnion, iUnion_comp, nonempty_equiv_of_countable, ofFinite, setIntegral_iUnion_fintype, subset_iUnion, surjective
-/
theorem hasSum_setIntegral_iUnion {ι : Type*} [Countable ι] {s : ι -> Set X}
    (hm : forall i, MeasurableSet (s i)) (hd : Pairwise (Disjoint on s))
    (hfi : μ.IntegrableOn f (⋃ i, s i)) :
    HasSum (fun n => ∫ᵛ x in s n, f x ∂[B; μ]) (∫ᵛ x in ⋃ n, s n, f x ∂[B; μ]) := by
  rcases finite_or_infinite ι with hι | hι
  · let : Fintype ι := Fintype.ofFinite ι
    have : ∫ᵛ x in ⋃ n, s n, f x ∂[B; μ] = ∑ i, ∫ᵛ x in s i, f x ∂[B; μ] := by
      rw [setIntegral_iUnion_fintype hm hd (fun i => ?_)]
      exact hfi.mono (MeasurableSet.iUnion hm) (by simp [subset_iUnion s])
    rw [this]
    apply hasSum_fintype
  obtain ⟨e⟩ : Nonempty (ι ≃ Nat) := nonempty_equiv_of_countable
  rw [← e.symm.surjective.iUnion_comp]; rw [← e.symm.hasSum_iff]
  apply hasSum_setIntegral_iUnion_nat (fun i => hm _) (fun i j hij => hd (by simp [hij]))
  rwa [e.symm.surjective.iUnion_comp]

/--
theorem `integral_iUnion` / 定理 `integral_iUnion`

English:
theorem integral_iUnion
  statement: {ι : Type*} [Countable ι] {s : ι -> Set X} (hm : forall i, MeasurableSet (s i))
  proof: (HasSum.tsum_eq (hasSum_setIntegral_iUnion hm hd hfi)).symm

中文:
定理 integral_iUnion
  结论: {ι : 类型} [可数 ι] {s : ι -> 集合 X} (hm : 对任意 i, 可测集 (s i))
  证明: (HasSum.tsum_eq (hasSum_setIntegral_iUnion hm hd hfi)).symm

Depends on / 依赖: HasSum, HasSum.tsum_eq, hasSum_setIntegral_iUnion, tsum_eq
-/
theorem integral_iUnion {ι : Type*} [Countable ι] {s : ι -> Set X} (hm : forall i, MeasurableSet (s i))
    (hd : Pairwise (Disjoint on s)) (hfi : μ.IntegrableOn f (⋃ i, s i)) :
    ∫ᵛ x in ⋃ n, s n, f x ∂[B; μ] = ∑' n, ∫ᵛ x in s n, f x ∂[B; μ] :=
  (HasSum.tsum_eq (hasSum_setIntegral_iUnion hm hd hfi)).symm

/--
theorem `setIntegral_toSignedMeasure` / 定理 `setIntegral_toSignedMeasure`

English:
theorem setIntegral_toSignedMeasure
  statement: {μ : Measure X} [IsFiniteMeasure μ]
  proof: by
  rw [← integral_toSignedMeasure]; rw [restrict_toSignedMeasure hs]

中文:
定理 set整数egral_toSignedMeasure
  结论: {μ : 测度 X} [是有限测度 μ]
  证明: by
  rw [← integral_toSignedMeasure]; rw [restrict_toSignedMeasure hs]
-/
@[simp] theorem setIntegral_toSignedMeasure {μ : Measure X} [IsFiniteMeasure μ]
    {f : X -> G} {s : Set X} (hs : MeasurableSet s) :
    ∫ᵛ x in s, f x ∂<•μ.toSignedMeasure = ∫ x in s, f x ∂μ := by
  rw [← integral_toSignedMeasure]; rw [restrict_toSignedMeasure hs]

/--
theorem `Integrable.tendsto_setIntegral_nhds_zero` / 定理 `Integrable.tendsto_setIntegral_nhds_zero`

English:
theorem Integrable.tendsto_setIntegral_nhds_zero
  statement: {ι : Type*}
  proof: by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simp_rw [← coe_nnnorm, ← NNReal.coe_zero, NNReal.tendsto_coe, ← ENNReal.tendsto_coe,
    ENNReal.coe_zero]
  have : Tendsto (fun i => ‖B‖ₑ * ∫⁻ (x : X) in s i, ‖f x‖ₑ ∂μ.variation) l (𝓝 (‖B‖ₑ * 0)) :=
    ENNReal.Tendsto.const_mul (tendsto_setLIntegral_zero (ne_of_lt hf.2) hs) (by simp)
  rw [mul_zero] at this
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds this (fun i => zero_le)
  intro i
  apply enorm_integral_le_lintegral_enorm.trans
  dsimp
  gcongr
  exact variation_restrict_le

中文:
定理 可积.tendsto_set整数egral_nhds_zero
  结论: {ι : 类型}
  证明: by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simp_rw [← coe_nnnorm, ← NNReal.coe_zero, NNReal.tendsto_coe, ← ENNReal.tendsto_coe,
    ENNReal.coe_zero]
  have : Tendsto (fun i => ‖B‖ₑ * ∫⁻ (x : X) in s i, ‖f x‖ₑ ∂μ.variation) l (𝓝 (‖B‖ₑ * 0)) :=
    ENNReal.Tendsto.const_mul (tendsto_setLIntegral_zero (ne_of_lt hf.2) hs) (by simp)
  rw [mul_zero] at this
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds this (fun i => zero_le)
  intro i
  apply enorm_integral_le_lintegral_enorm.trans
  dsimp
  gcongr
  exact variation_restrict_le
-/
theorem Integrable.tendsto_setIntegral_nhds_zero {ι : Type*}
    (hf : μ.Integrable f) {l : Filter ι} {s : ι -> Set X}
    (hs : Tendsto (μ.variation ∘ s) l (𝓝 0)) :
    Tendsto (fun i => ∫ᵛ x in s i, f x ∂[B; μ]) l (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simp_rw [← coe_nnnorm, ← NNReal.coe_zero, NNReal.tendsto_coe, ← ENNReal.tendsto_coe,
    ENNReal.coe_zero]
  have : Tendsto (fun i => ‖B‖ₑ * ∫⁻ (x : X) in s i, ‖f x‖ₑ ∂μ.variation) l (𝓝 (‖B‖ₑ * 0)) :=
    ENNReal.Tendsto.const_mul (tendsto_setLIntegral_zero (ne_of_lt hf.2) hs) (by simp)
  rw [mul_zero] at this
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds this (fun i => zero_le)
  intro i
  apply enorm_integral_le_lintegral_enorm.trans
  dsimp
  gcongr
  exact variation_restrict_le

/--
lemma `tendsto_setIntegral_of_L1` / 引理 `tendsto_setIntegral_of_L1`

English:
lemma tendsto_setIntegral_of_L1
  statement: {ι} (f : X -> E)
  proof: by
  refine tendsto_integral_of_L1 f ?_ ?_ ?_
  · apply hfi.mono_measure
    grw [variation_restrict_le, Measure.restrict_le_self]
  · filter_upwards [hFi] with i hi using hi.restrict
  · simp_rw [← eLpNorm_one_eq_lintegral_enorm] at hF ⊢
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hF (fun _ => zero_le)
      (fun i => ?_)
    apply eLpNorm_mono_measure
    grw [variation_restrict_le]
    apply Measure.restrict_le_self

中文:
引理 tendsto_set整数egral_of_L1
  结论: {ι} (f : X -> E)
  证明: by
  refine tendsto_integral_of_L1 f ?_ ?_ ?_
  · apply hfi.mono_measure
    grw [variation_restrict_le, Measure.restrict_le_self]
  · filter_upwards [hFi] with i hi using hi.restrict
  · simp_rw [← eLpNorm_one_eq_lintegral_enorm] at hF ⊢
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hF (fun _ => zero_le)
      (fun i => ?_)
    apply eLpNorm_mono_measure
    grw [variation_restrict_le]
    apply Measure.restrict_le_self

Depends on / 依赖: Measure, Measure.restrict_le_self, eLpNorm_mono_measure, eLpNorm_one_eq_lintegral_enorm, filter_upwards, hfi.mono_measure, hi.restrict, mono_measure, restrict, restrict_le_self, simp_rw, tendsto_const_nhds, tendsto_integral_of_L1, tendsto_of_tendsto_of_tendsto_of_le_of_le, variation_restrict_le, zero_le
-/
lemma tendsto_setIntegral_of_L1 {ι} (f : X -> E)
    (hfi : AEStronglyMeasurable f μ.variation) {F : ι -> X -> E}
    {l : Filter ι} (hFi : forallᶠ i in l, μ.Integrable (F i))
    (hF : Tendsto (fun i => ∫⁻ x, ‖F i x - f x‖ₑ ∂μ.variation) l (𝓝 0))
    (s : Set X) :
    Tendsto (fun i => ∫ᵛ x in s, F i x ∂[B; μ]) l (𝓝 (∫ᵛ x in s, f x ∂[B; μ])) := by
  refine tendsto_integral_of_L1 f ?_ ?_ ?_
  · apply hfi.mono_measure
    grw [variation_restrict_le, Measure.restrict_le_self]
  · filter_upwards [hFi] with i hi using hi.restrict
  · simp_rw [← eLpNorm_one_eq_lintegral_enorm] at hF ⊢
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hF (fun _ => zero_le)
      (fun i => ?_)
    apply eLpNorm_mono_measure
    grw [variation_restrict_le]
    apply Measure.restrict_le_self

/--
lemma `tendsto_setIntegral_of_L1'` / 引理 `tendsto_setIntegral_of_L1'`

English:
lemma tendsto_setIntegral_of_L1'
  statement: {ι} (f : X -> E)
  proof: by
  refine tendsto_setIntegral_of_L1 f hfi hFi ?_ s
  simp_rw [eLpNorm_one_eq_lintegral_enorm, Pi.sub_apply] at hF
  exact hF

中文:
引理 tendsto_set整数egral_of_L1'
  结论: {ι} (f : X -> E)
  证明: by
  refine tendsto_setIntegral_of_L1 f hfi hFi ?_ s
  simp_rw [eLpNorm_one_eq_lintegral_enorm, Pi.sub_apply] at hF
  exact hF

Depends on / 依赖: Pi.sub_apply, eLpNorm_one_eq_lintegral_enorm, simp_rw, sub_apply, tendsto_setIntegral_of_L1
-/
lemma tendsto_setIntegral_of_L1' {ι} (f : X -> E)
    (hfi : AEStronglyMeasurable f μ.variation) {F : ι -> X -> E}
    {l : Filter ι} (hFi : forallᶠ i in l, μ.Integrable (F i))
    (hF : Tendsto (fun i => eLpNorm (F i - f) 1 μ.variation) l (𝓝 0))
    (s : Set X) :
    Tendsto (fun i => ∫ᵛ x in s, F i x ∂[B; μ]) l (𝓝 (∫ᵛ x in s, f x ∂[B; μ])) := by
  refine tendsto_setIntegral_of_L1 f hfi hFi ?_ s
  simp_rw [eLpNorm_one_eq_lintegral_enorm, Pi.sub_apply] at hF
  exact hF

end MeasureTheory.VectorMeasure
