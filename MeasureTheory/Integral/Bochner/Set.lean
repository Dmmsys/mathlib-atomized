/-
Copyright (c) 2020 Zhouhang Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou, Yury Kudryashov
-/
module

public import Mathlib.Combinatorics.Enumerative.InclusionExclusion
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Topology.MetricSpace.ThickenedIndicator

/-!
# Set integral

In this file we prove some properties of `∫ x in s, f x ∂μ`. Recall that this notation
is defined as `∫ x, f x ∂(μ.restrict s)`. In `integral_indicator` we prove that for a measurable
function `f` and a measurable set `s` this definition coincides with another natural definition:
`∫ x, indicator s f x ∂μ = ∫ x in s, f x ∂μ`, where `indicator s f x` is equal to `f x` for `x ∈ s`
and is zero otherwise.

Since `∫ x in s, f x ∂μ` is a notation, one can rewrite or apply any theorem about `∫ x, f x ∂μ`
directly. In this file we prove some theorems about dependence of `∫ x in s, f x ∂μ` on `s`, e.g.
`setIntegral_union`, `setIntegral_empty`, `setIntegral_univ`.

We use the property `IntegrableOn f s μ := Integrable f (μ.restrict s)`, defined in
`MeasureTheory.IntegrableOn`. We also defined in that same file a predicate
`IntegrableAtFilter (f : X → E) (l : Filter X) (μ : Measure X)` saying that `f` is integrable at
some set `s ∈ l`.

## Notation

We provide the following notations for expressing the integral of a function on a set :
* `∫ x in s, f x ∂μ` is `MeasureTheory.integral (μ.restrict s) f`
* `∫ x in s, f x` is `∫ x in s, f x ∂volume`

Note that the set notations are defined in the file
`Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`,
but we reference them here because all theorems about set integrals are in this file.
-/

@[expose] public section

assert_not_exists InnerProductSpace

open Filter Function MeasureTheory RCLike Set TopologicalSpace Topology
open scoped ENNReal NNReal Finset

variable {X Y E F : Type*}

namespace MeasureTheory

variable {mX : MeasurableSpace X}

section NormedAddCommGroup

variable [NormedAddCommGroup E] [NormedSpace Real E]
  {f g : X -> E} {s t : Set X} {μ : Measure X}

/--
theorem `setIntegral_congr_ae₀` / 定理 `setIntegral_congr_ae₀`

English:
theorem setIntegral_congr_ae₀
  given: (hs : NullMeasurableSet s μ) (h : forallᵐ x ∂μ, x in s -> f x = g x)
  proof: integral_congr_ae ((ae_restrict_iff'₀ hs).2 h)

中文:
定理 set整数egral_congr_ae₀
  条件: (hs : NullMeasurableSet s μ) (h : 对任意ᵐ x ∂μ, x in s -> f x = g x)
  证明: integral_congr_ae ((ae_restrict_iff'₀ hs).2 h)

Depends on / 依赖: ae_restrict_iff, integral_congr_ae
-/
theorem setIntegral_congr_ae₀ (hs : NullMeasurableSet s μ) (h : forallᵐ x ∂μ, x in s -> f x = g x) :
    ∫ x in s, f x ∂μ = ∫ x in s, g x ∂μ :=
  integral_congr_ae ((ae_restrict_iff'₀ hs).2 h)

/--
theorem `setIntegral_congr_ae` / 定理 `setIntegral_congr_ae`

English:
theorem setIntegral_congr_ae
  given: (hs : MeasurableSet s) (h : forallᵐ x ∂μ, x in s -> f x = g x)
  proof: integral_congr_ae ((ae_restrict_iff' hs).2 h)

中文:
定理 set整数egral_congr_ae
  条件: (hs : 可测集 s) (h : 对任意ᵐ x ∂μ, x in s -> f x = g x)
  证明: integral_congr_ae ((ae_restrict_iff' hs).2 h)

Depends on / 依赖: ae_restrict_iff, integral_congr_ae
-/
theorem setIntegral_congr_ae (hs : MeasurableSet s) (h : forallᵐ x ∂μ, x in s -> f x = g x) :
    ∫ x in s, f x ∂μ = ∫ x in s, g x ∂μ :=
  integral_congr_ae ((ae_restrict_iff' hs).2 h)

/--
theorem `setIntegral_congr_fun₀` / 定理 `setIntegral_congr_fun₀`

English:
theorem setIntegral_congr_fun₀
  given: (hs : NullMeasurableSet s μ) (h : EqOn f g s)
  proof: setIntegral_congr_ae₀ hs Eventually.of_forall h

中文:
定理 set整数egral_congr_fun₀
  条件: (hs : NullMeasurableSet s μ) (h : EqOn f g s)
  证明: setIntegral_congr_ae₀ hs Eventually.of_forall h

Depends on / 依赖: Eventually, Eventually.of_forall, of_forall
-/
theorem setIntegral_congr_fun₀ (hs : NullMeasurableSet s μ) (h : EqOn f g s) :
    ∫ x in s, f x ∂μ = ∫ x in s, g x ∂μ :=
setIntegral_congr_ae₀ hs Eventually.of_forall h

/--
theorem `setIntegral_congr_fun` / 定理 `setIntegral_congr_fun`

English:
theorem setIntegral_congr_fun
  given: (hs : MeasurableSet s) (h : EqOn f g s)
  proof: setIntegral_congr_ae hs Eventually.of_forall h

中文:
定理 set整数egral_congr_fun
  条件: (hs : 可测集 s) (h : EqOn f g s)
  证明: setIntegral_congr_ae hs Eventually.of_forall h

Depends on / 依赖: Eventually, Eventually.of_forall, of_forall, setIntegral_congr_ae
-/
theorem setIntegral_congr_fun (hs : MeasurableSet s) (h : EqOn f g s) :
    ∫ x in s, f x ∂μ = ∫ x in s, g x ∂μ :=
setIntegral_congr_ae hs Eventually.of_forall h

/--
theorem `setIntegral_congr_set` / 定理 `setIntegral_congr_set`

English:
theorem setIntegral_congr_set
  given: (hst : s =ᵐ[μ] t)
  statement: ∫ x in s, f x ∂μ = ∫ x in t, f x ∂μ
  proof: by
  rw [Measure.restrict_congr_set hst]

中文:
定理 set整数egral_congr_set
  条件: (hst : s =ᵐ[μ] t)
  结论: ∫ x in s, f x ∂μ = ∫ x in t, f x ∂μ
  证明: by
  rw [Measure.restrict_congr_set hst]

Depends on / 依赖: Measure, Measure.restrict_congr_set, restrict_congr_set
-/
theorem setIntegral_congr_set (hst : s =ᵐ[μ] t) : ∫ x in s, f x ∂μ = ∫ x in t, f x ∂μ := by
  rw [Measure.restrict_congr_set hst]

/--
theorem `setIntegral_union₀` / 定理 `setIntegral_union₀`

English:
theorem setIntegral_union₀
  statement: (hst : AEDisjoint μ s t) (ht : NullMeasurableSet t μ)
  proof: by
  simp only [Measure.restrict_union₀ hst ht, integral_add_measure hfs hft]

@[deprecated (since := "2026-03-04")] alias integral_union_ae := setIntegral_union₀

中文:
定理 set整数egral_union₀
  结论: (hst : AEDisjoint μ s t) (ht : NullMeasurableSet t μ)
  证明: by
  simp only [Measure.restrict_union₀ hst ht, integral_add_measure hfs hft]

@[deprecated (since := "2026-03-04")] alias integral_union_ae := setIntegral_union₀

Depends on / 依赖: Measure, Measure.restrict_union, integral_add_measure
-/
theorem setIntegral_union₀ (hst : AEDisjoint μ s t) (ht : NullMeasurableSet t μ)
    (hfs : IntegrableOn f s μ) (hft : IntegrableOn f t μ) :
    ∫ x in s union t, f x ∂μ = ∫ x in s, f x ∂μ + ∫ x in t, f x ∂μ := by
  simp only [Measure.restrict_union₀ hst ht, integral_add_measure hfs hft]

@[deprecated (since := "2026-03-04")] alias integral_union_ae := setIntegral_union₀

/--
theorem `setIntegral_union` / 定理 `setIntegral_union`

English:
theorem setIntegral_union
  statement: (hst : Disjoint s t) (ht : MeasurableSet t) (hfs : IntegrableOn f s μ)
  proof: setIntegral_union₀ hst.aedisjoint ht.nullMeasurableSet hfs hft

中文:
定理 set整数egral_union
  结论: (hst : Disjoint s t) (ht : 可测集 t) (hfs : 整数egrableOn f s μ)
  证明: setIntegral_union₀ hst.aedisjoint ht.nullMeasurableSet hfs hft

Depends on / 依赖: aedisjoint, hst.aedisjoint, ht.nullMeasurableSet, nullMeasurableSet
-/
theorem setIntegral_union (hst : Disjoint s t) (ht : MeasurableSet t) (hfs : IntegrableOn f s μ)
    (hft : IntegrableOn f t μ) : ∫ x in s union t, f x ∂μ = ∫ x in s, f x ∂μ + ∫ x in t, f x ∂μ :=
  setIntegral_union₀ hst.aedisjoint ht.nullMeasurableSet hfs hft

/--
theorem `setIntegral_sdiff₀` / 定理 `setIntegral_sdiff₀`

English:
theorem setIntegral_sdiff₀
  given: (ht : NullMeasurableSet t μ) (hfs : IntegrableOn f s μ) (hts : t subseteq s)
  proof: by
  rw [eq_sub_iff_add_eq]; rw [← setIntegral_union₀]; rw [sdiff_union_of_subset hts]
  exacts [disjoint_sdiff_self_left.aedisjoint, ht, hfs.mono_set sdiff_subset, hfs.mono_set hts]

@[deprecated (since := "2026-06-03")] alias setIntegral_diff₀ := setIntegral_sdiff₀

中文:
定理 set整数egral_sdiff₀
  条件: (ht : NullMeasurableSet t μ) (hfs : 整数egrableOn f s μ) (hts : t subseteq s)
  证明: by
  rw [eq_sub_iff_add_eq]; rw [← setIntegral_union₀]; rw [sdiff_union_of_subset hts]
  exacts [disjoint_sdiff_self_left.aedisjoint, ht, hfs.mono_set sdiff_subset, hfs.mono_set hts]

@[deprecated (since := "2026-06-03")] alias setIntegral_diff₀ := setIntegral_sdiff₀

Depends on / 依赖: aedisjoint, disjoint_sdiff_self_left, disjoint_sdiff_self_left.aedisjoint, eq_sub_iff_add_eq, exacts, hfs.mono_set, mono_set, sdiff_subset, sdiff_union_of_subset
-/
theorem setIntegral_sdiff₀ (ht : NullMeasurableSet t μ) (hfs : IntegrableOn f s μ) (hts : t subseteq s) :
    ∫ x in s \ t, f x ∂μ = ∫ x in s, f x ∂μ - ∫ x in t, f x ∂μ := by
  rw [eq_sub_iff_add_eq]; rw [← setIntegral_union₀]; rw [sdiff_union_of_subset hts]
  exacts [disjoint_sdiff_self_left.aedisjoint, ht, hfs.mono_set sdiff_subset, hfs.mono_set hts]

@[deprecated (since := "2026-06-03")] alias setIntegral_diff₀ := setIntegral_sdiff₀

/--
theorem `setIntegral_sdiff` / 定理 `setIntegral_sdiff`

English:
theorem setIntegral_sdiff
  given: (ht : MeasurableSet t) (hfs : IntegrableOn f s μ) (hts : t subseteq s)
  proof: setIntegral_sdiff₀ ht.nullMeasurableSet hfs hts

@[deprecated (since := "2026-06-03")] alias setIntegral_diff := setIntegral_sdiff

@[deprecated (since := "2026-03-04")] alias integral_diff := setIntegral_sdiff

中文:
定理 set整数egral_sdiff
  条件: (ht : 可测集 t) (hfs : 整数egrableOn f s μ) (hts : t subseteq s)
  证明: setIntegral_sdiff₀ ht.nullMeasurableSet hfs hts

@[deprecated (since := "2026-06-03")] alias setIntegral_diff := setIntegral_sdiff

@[deprecated (since := "2026-03-04")] alias integral_diff := setIntegral_sdiff

Depends on / 依赖: ht.nullMeasurableSet, nullMeasurableSet
-/
theorem setIntegral_sdiff (ht : MeasurableSet t) (hfs : IntegrableOn f s μ) (hts : t subseteq s) :
    ∫ x in s \ t, f x ∂μ = ∫ x in s, f x ∂μ - ∫ x in t, f x ∂μ :=
  setIntegral_sdiff₀ ht.nullMeasurableSet hfs hts

@[deprecated (since := "2026-06-03")] alias setIntegral_diff := setIntegral_sdiff

@[deprecated (since := "2026-03-04")] alias integral_diff := setIntegral_sdiff

/--
theorem `integral_inter_add_sdiff₀` / 定理 `integral_inter_add_sdiff₀`

English:
theorem integral_inter_add_sdiff₀
  given: (ht : NullMeasurableSet t μ) (hfs : IntegrableOn f s μ)
  proof: by
  rw [← Measure.restrict_inter_add_sdiff₀ s ht]; rw [integral_add_measure]
  · exact Integrable.mono_measure hfs (Measure.restrict_mono inter_subset_left le_rfl)
  · exact Integrable.mono_measure hfs (Measure.restrict_mono sdiff_subset le_rfl)

@[deprecated (since := "2026-06-03")] alias integral_inter_add_diff₀ := integral_inter_add_sdiff₀

中文:
定理 integral_inter_add_sdiff₀
  条件: (ht : NullMeasurableSet t μ) (hfs : 整数egrableOn f s μ)
  证明: by
  rw [← Measure.restrict_inter_add_sdiff₀ s ht]; rw [integral_add_measure]
  · exact Integrable.mono_measure hfs (Measure.restrict_mono inter_subset_left le_rfl)
  · exact Integrable.mono_measure hfs (Measure.restrict_mono sdiff_subset le_rfl)

@[deprecated (since := "2026-06-03")] alias integral_inter_add_diff₀ := integral_inter_add_sdiff₀

Depends on / 依赖: Integrable, Integrable.mono_measure, Measure, Measure.restrict_inter_add_sdiff, Measure.restrict_mono, integral_add_measure, inter_subset_left, le_rfl, mono_measure, restrict_mono, sdiff_subset
-/
theorem integral_inter_add_sdiff₀ (ht : NullMeasurableSet t μ) (hfs : IntegrableOn f s μ) :
    ∫ x in s inter t, f x ∂μ + ∫ x in s \ t, f x ∂μ = ∫ x in s, f x ∂μ := by
  rw [← Measure.restrict_inter_add_sdiff₀ s ht]; rw [integral_add_measure]
  · exact Integrable.mono_measure hfs (Measure.restrict_mono inter_subset_left le_rfl)
  · exact Integrable.mono_measure hfs (Measure.restrict_mono sdiff_subset le_rfl)

@[deprecated (since := "2026-06-03")] alias integral_inter_add_diff₀ := integral_inter_add_sdiff₀

/--
theorem `integral_inter_add_sdiff` / 定理 `integral_inter_add_sdiff`

English:
theorem integral_inter_add_sdiff
  given: (ht : MeasurableSet t) (hfs : IntegrableOn f s μ)
  proof: integral_inter_add_sdiff₀ ht.nullMeasurableSet hfs

@[deprecated (since := "2026-06-03")] alias integral_inter_add_diff := integral_inter_add_sdiff

中文:
定理 integral_inter_add_sdiff
  条件: (ht : 可测集 t) (hfs : 整数egrableOn f s μ)
  证明: integral_inter_add_sdiff₀ ht.nullMeasurableSet hfs

@[deprecated (since := "2026-06-03")] alias integral_inter_add_diff := integral_inter_add_sdiff

Depends on / 依赖: ht.nullMeasurableSet, nullMeasurableSet
-/
theorem integral_inter_add_sdiff (ht : MeasurableSet t) (hfs : IntegrableOn f s μ) :
    ∫ x in s inter t, f x ∂μ + ∫ x in s \ t, f x ∂μ = ∫ x in s, f x ∂μ :=
  integral_inter_add_sdiff₀ ht.nullMeasurableSet hfs

@[deprecated (since := "2026-06-03")] alias integral_inter_add_diff := integral_inter_add_sdiff

/--
theorem `integral_biUnion_finset` / 定理 `integral_biUnion_finset`

English:
theorem integral_biUnion_finset
  statement: {ι : Type*} (t : Finset ι) {s : ι -> Set X}
  proof: by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | insert _ _ hat IH =>
    simp only [Finset.coe_insert, Finset.forall_mem_insert, Set.pairwise_insert,
      Finset.set_biUnion_insert] at hs hf h's ⊢
    rw [setIntegral_union _ _ hf.1 (integrableOn_finset_iUnion.2 hf.2)]
    · rw [Finset.sum_insert hat, IH hs.2 h's.1 hf.2]
    · simp only [disjoint_iUnion_right]
      exact fun i hi => (h's.2 i hi (ne_of_mem_of_not_mem hi hat).symm).1
    · exact Finset.measurableSet_biUnion _ hs.2

中文:
定理 integral_biUnion_finset
  结论: {ι : 类型} (t : 有限集 ι) {s : ι -> 集合 X}
  证明: by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | insert _ _ hat IH =>
    simp only [Finset.coe_insert, Finset.forall_mem_insert, Set.pairwise_insert,
      Finset.set_biUnion_insert] at hs hf h's ⊢
    rw [setIntegral_union _ _ hf.1 (integrableOn_finset_iUnion.2 hf.2)]
    · rw [Finset.sum_insert hat, IH hs.2 h's.1 hf.2]
    · simp only [disjoint_iUnion_right]
      exact fun i hi => (h's.2 i hi (ne_of_mem_of_not_mem hi hat).symm).1
    · exact Finset.measurableSet_biUnion _ hs.2

Depends on / 依赖: Finset, Finset.coe_insert, Finset.forall_mem_insert, Finset.induction_on, Finset.measurableSet_biUnion, Finset.set_biUnion_insert, Finset.sum_insert, Set.pairwise_insert, classical, coe_insert, disjoint_iUnion_right, forall_mem_insert, induction_on, insert, integrableOn_finset_iUnion, measurableSet_biUnion, ne_of_mem_of_not_mem, pairwise_insert, setIntegral_union, set_biUnion_insert
-/
theorem integral_biUnion_finset {ι : Type*} (t : Finset ι) {s : ι -> Set X}
    (hs : forall i in t, MeasurableSet (s i)) (h's : Set.Pairwise (↑t) (Disjoint on s))
    (hf : forall i in t, IntegrableOn f (s i) μ) :
    ∫ x in ⋃ i in t, s i, f x ∂μ = ∑ i in t, ∫ x in s i, f x ∂μ := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | insert _ _ hat IH =>
    simp only [Finset.coe_insert, Finset.forall_mem_insert, Set.pairwise_insert,
      Finset.set_biUnion_insert] at hs hf h's ⊢
    rw [setIntegral_union _ _ hf.1 (integrableOn_finset_iUnion.2 hf.2)]
    · rw [Finset.sum_insert hat, IH hs.2 h's.1 hf.2]
    · simp only [disjoint_iUnion_right]
      exact fun i hi => (h's.2 i hi (ne_of_mem_of_not_mem hi hat).symm).1
    · exact Finset.measurableSet_biUnion _ hs.2

/--
theorem `integral_iUnion_fintype` / 定理 `integral_iUnion_fintype`

English:
theorem integral_iUnion_fintype
  statement: {ι : Type*} [Fintype ι] {s : ι -> Set X}
  proof: by
  convert! integral_biUnion_finset Finset.univ (fun i _ => hs i) _ fun i _ => hf i
  · simp
  · simp [pairwise_univ, h's]

中文:
定理 integral_iUnion_fintype
  结论: {ι : 类型} [有限类型 ι] {s : ι -> 集合 X}
  证明: by
  convert! integral_biUnion_finset Finset.univ (fun i _ => hs i) _ fun i _ => hf i
  · simp
  · simp [pairwise_univ, h's]

Depends on / 依赖: Finset, Finset.univ, convert, integral_biUnion_finset, pairwise_univ
-/
theorem integral_iUnion_fintype {ι : Type*} [Fintype ι] {s : ι -> Set X}
    (hs : forall i, MeasurableSet (s i)) (h's : Pairwise (Disjoint on s))
    (hf : forall i, IntegrableOn f (s i) μ) : ∫ x in ⋃ i, s i, f x ∂μ = ∑ i, ∫ x in s i, f x ∂μ := by
  convert! integral_biUnion_finset Finset.univ (fun i _ => hs i) _ fun i _ => hf i
  · simp
  · simp [pairwise_univ, h's]

/--
theorem `setIntegral_empty` / 定理 `setIntegral_empty`

English:
theorem setIntegral_empty
  statement: ∫ x in ∅, f x ∂μ = 0
  proof: by
  rw [Measure.restrict_empty]; rw [integral_zero_measure]

中文:
定理 set整数egral_empty
  结论: ∫ x in ∅, f x ∂μ = 0
  证明: by
  rw [Measure.restrict_empty]; rw [integral_zero_measure]

Depends on / 依赖: Measure, Measure.restrict_empty, integral_zero_measure, restrict_empty
-/
theorem setIntegral_empty : ∫ x in ∅, f x ∂μ = 0 := by
  rw [Measure.restrict_empty]; rw [integral_zero_measure]

/--
theorem `setIntegral_univ` / 定理 `setIntegral_univ`

English:
theorem setIntegral_univ
  statement: ∫ x in univ, f x ∂μ = ∫ x, f x ∂μ
  proof: by rw [Measure.restrict_univ]

中文:
定理 set整数egral_univ
  结论: ∫ x in univ, f x ∂μ = ∫ x, f x ∂μ
  证明: by rw [Measure.restrict_univ]

Depends on / 依赖: Measure, Measure.restrict_univ, restrict_univ
-/
theorem setIntegral_univ : ∫ x in univ, f x ∂μ = ∫ x, f x ∂μ := by rw [Measure.restrict_univ]

/--
lemma `integral_eq_setIntegral` / 引理 `integral_eq_setIntegral`

English:
lemma integral_eq_setIntegral
  given: (hs : forallᵐ x ∂μ, x in s) (f : X -> E)
  proof: by
  rw [← setIntegral_univ]; rw [← setIntegral_congr_set]; rwa [ae_eq_univ]

中文:
引理 integral_eq_set整数egral
  条件: (hs : 对任意ᵐ x ∂μ, x in s) (f : X -> E)
  证明: by
  rw [← setIntegral_univ]; rw [← setIntegral_congr_set]; rwa [ae_eq_univ]

Depends on / 依赖: ae_eq_univ, setIntegral_congr_set, setIntegral_univ
-/
lemma integral_eq_setIntegral (hs : forallᵐ x ∂μ, x in s) (f : X -> E) :
    ∫ x, f x ∂μ = ∫ x in s, f x ∂μ := by
  rw [← setIntegral_univ]; rw [← setIntegral_congr_set]; rwa [ae_eq_univ]

/--
theorem `integral_add_compl₀` / 定理 `integral_add_compl₀`

English:
theorem integral_add_compl₀
  given: (hs : NullMeasurableSet s μ) (hfi : Integrable f μ)
  proof: by
  have := setIntegral_union₀ disjoint_compl_right.aedisjoint
    hs.compl hfi.integrableOn hfi.integrableOn
  rw [← this]; rw [union_compl_self]; rw [setIntegral_univ]

中文:
定理 integral_add_compl₀
  条件: (hs : NullMeasurableSet s μ) (hfi : 可积 f μ)
  证明: by
  have := setIntegral_union₀ disjoint_compl_right.aedisjoint
    hs.compl hfi.integrableOn hfi.integrableOn
  rw [← this]; rw [union_compl_self]; rw [setIntegral_univ]

Depends on / 依赖: aedisjoint, disjoint_compl_right, disjoint_compl_right.aedisjoint, hfi.integrableOn, hs.compl, integrableOn, setIntegral_univ, union_compl_self
-/
theorem integral_add_compl₀ (hs : NullMeasurableSet s μ) (hfi : Integrable f μ) :
    ∫ x in s, f x ∂μ + ∫ x in sᶜ, f x ∂μ = ∫ x, f x ∂μ := by
  have := setIntegral_union₀ disjoint_compl_right.aedisjoint
    hs.compl hfi.integrableOn hfi.integrableOn
  rw [← this]; rw [union_compl_self]; rw [setIntegral_univ]

/--
theorem `integral_add_compl` / 定理 `integral_add_compl`

English:
theorem integral_add_compl
  given: (hs : MeasurableSet s) (hfi : Integrable f μ)
  proof: integral_add_compl₀ hs.nullMeasurableSet hfi

中文:
定理 integral_add_compl
  条件: (hs : 可测集 s) (hfi : 可积 f μ)
  证明: integral_add_compl₀ hs.nullMeasurableSet hfi

Depends on / 依赖: hs.nullMeasurableSet, nullMeasurableSet
-/
theorem integral_add_compl (hs : MeasurableSet s) (hfi : Integrable f μ) :
    ∫ x in s, f x ∂μ + ∫ x in sᶜ, f x ∂μ = ∫ x, f x ∂μ :=
  integral_add_compl₀ hs.nullMeasurableSet hfi

/--
theorem `setIntegral_compl₀` / 定理 `setIntegral_compl₀`

English:
theorem setIntegral_compl₀
  given: (hs : NullMeasurableSet s μ) (hfi : Integrable f μ)
  proof: by
  rw [← integral_add_compl₀ (μ := μ) hs hfi]; rw [add_sub_cancel_left]

中文:
定理 set整数egral_compl₀
  条件: (hs : NullMeasurableSet s μ) (hfi : 可积 f μ)
  证明: by
  rw [← integral_add_compl₀ (μ := μ) hs hfi]; rw [add_sub_cancel_left]

Depends on / 依赖: add_sub_cancel_left
-/
theorem setIntegral_compl₀ (hs : NullMeasurableSet s μ) (hfi : Integrable f μ) :
    ∫ x in sᶜ, f x ∂μ = ∫ x, f x ∂μ - ∫ x in s, f x ∂μ := by
  rw [← integral_add_compl₀ (μ := μ) hs hfi]; rw [add_sub_cancel_left]

/--
theorem `setIntegral_compl` / 定理 `setIntegral_compl`

English:
theorem setIntegral_compl
  given: (hs : MeasurableSet s) (hfi : Integrable f μ)
  proof: setIntegral_compl₀ hs.nullMeasurableSet hfi

中文:
定理 set整数egral_compl
  条件: (hs : 可测集 s) (hfi : 可积 f μ)
  证明: setIntegral_compl₀ hs.nullMeasurableSet hfi

Depends on / 依赖: hs.nullMeasurableSet, nullMeasurableSet
-/
theorem setIntegral_compl (hs : MeasurableSet s) (hfi : Integrable f μ) :
    ∫ x in sᶜ, f x ∂μ = ∫ x, f x ∂μ - ∫ x in s, f x ∂μ :=
  setIntegral_compl₀ hs.nullMeasurableSet hfi

/--
theorem `integral_indicator` / 定理 `integral_indicator`

English:
theorem integral_indicator
  given: (hs : MeasurableSet s)
  proof: by
  by_cases hfi : IntegrableOn f s μ; swap
  · rw [integral_undef hfi, integral_undef]
    rwa [integrable_indicator_iff hs]
  calc
    ∫ x, indicator s f x ∂μ = ∫ x in s, indicator s f x ∂μ + ∫ x in sᶜ, indicator s f x ∂μ :=
      (integral_add_compl hs (hfi.integrable_indicator hs)).symm
    _ = ∫ x in s, f x ∂μ + ∫ x in sᶜ, 0 ∂μ :=
      (congr_arg₂ (· + ·) (integral_congr_ae (indicator_ae_eq_restrict hs))
        (integral_congr_ae (indicator_ae_eq_restrict_compl hs)))
    _ = ∫ x in s, f x ∂μ := by simp

中文:
定理 integral_indicator
  条件: (hs : 可测集 s)
  证明: by
  by_cases hfi : IntegrableOn f s μ; swap
  · rw [integral_undef hfi, integral_undef]
    rwa [integrable_indicator_iff hs]
  calc
    ∫ x, indicator s f x ∂μ = ∫ x in s, indicator s f x ∂μ + ∫ x in sᶜ, indicator s f x ∂μ :=
      (integral_add_compl hs (hfi.integrable_indicator hs)).symm
    _ = ∫ x in s, f x ∂μ + ∫ x in sᶜ, 0 ∂μ :=
      (congr_arg₂ (· + ·) (integral_congr_ae (indicator_ae_eq_restrict hs))
        (integral_congr_ae (indicator_ae_eq_restrict_compl hs)))
    _ = ∫ x in s, f x ∂μ := by simp

Depends on / 依赖: IntegrableOn, hfi.integrable_indicator, indicator, indicator_ae_eq_restrict, indicator_ae_eq_restrict_compl, integrable_indicator, integrable_indicator_iff, integral_add_compl, integral_congr_ae, integral_undef
-/
theorem integral_indicator (hs : MeasurableSet s) :
    ∫ x, indicator s f x ∂μ = ∫ x in s, f x ∂μ := by
  by_cases hfi : IntegrableOn f s μ; swap
  · rw [integral_undef hfi, integral_undef]
    rwa [integrable_indicator_iff hs]
  calc
    ∫ x, indicator s f x ∂μ = ∫ x in s, indicator s f x ∂μ + ∫ x in sᶜ, indicator s f x ∂μ :=
      (integral_add_compl hs (hfi.integrable_indicator hs)).symm
    _ = ∫ x in s, f x ∂μ + ∫ x in sᶜ, 0 ∂μ :=
      (congr_arg₂ (· + ·) (integral_congr_ae (indicator_ae_eq_restrict hs))
        (integral_congr_ae (indicator_ae_eq_restrict_compl hs)))
    _ = ∫ x in s, f x ∂μ := by simp

/--
theorem `integral_indicator₀` / 定理 `integral_indicator₀`

English:
theorem integral_indicator₀
  given: (hs : NullMeasurableSet s μ)
  proof: by
  rw [← integral_congr_ae (indicator_ae_eq_of_ae_eq_set hs.toMeasurable_ae_eq)]; rw [integral_indicator (measurableSet_toMeasurable _ _)]; rw [Measure.restrict_congr_set hs.toMeasurable_ae_eq]

中文:
定理 integral_indicator₀
  条件: (hs : NullMeasurableSet s μ)
  证明: by
  rw [← integral_congr_ae (indicator_ae_eq_of_ae_eq_set hs.toMeasurable_ae_eq)]; rw [integral_indicator (measurableSet_toMeasurable _ _)]; rw [Measure.restrict_congr_set hs.toMeasurable_ae_eq]

Depends on / 依赖: Measure, Measure.restrict_congr_set, hs.toMeasurable_ae_eq, indicator_ae_eq_of_ae_eq_set, integral_congr_ae, integral_indicator, measurableSet_toMeasurable, restrict_congr_set, toMeasurable_ae_eq
-/
theorem integral_indicator₀ (hs : NullMeasurableSet s μ) :
    ∫ x, indicator s f x ∂μ = ∫ x in s, f x ∂μ := by
  rw [← integral_congr_ae (indicator_ae_eq_of_ae_eq_set hs.toMeasurable_ae_eq)]; rw [integral_indicator (measurableSet_toMeasurable _ _)]; rw [Measure.restrict_congr_set hs.toMeasurable_ae_eq]

/--
lemma `integral_integral_indicator` / 引理 `integral_integral_indicator`

English:
lemma integral_integral_indicator
  statement: {mY : MeasurableSpace Y} {ν : Measure Y} (f : X -> Y -> E)
  proof: by
  simp_rw [← integral_indicator hs, integral_indicator₂]

中文:
引理 integral_integral_indicator
  结论: {mY : 可测空间 Y} {ν : 测度 Y} (f : X -> Y -> E)
  证明: by
  simp_rw [← integral_indicator hs, integral_indicator₂]

Depends on / 依赖: integral_indicator, simp_rw
-/
lemma integral_integral_indicator {mY : MeasurableSpace Y} {ν : Measure Y} (f : X -> Y -> E)
    {s : Set X} (hs : MeasurableSet s) :
    ∫ x, ∫ y, s.indicator (f · y) x ∂ν ∂μ = ∫ x in s, ∫ y, f x y ∂ν ∂μ := by
  simp_rw [← integral_indicator hs, integral_indicator₂]

/--
theorem `setIntegral_indicator` / 定理 `setIntegral_indicator`

English:
theorem setIntegral_indicator
  given: (ht : MeasurableSet t)
  proof: by
  rw [integral_indicator ht]; rw [Measure.restrict_restrict ht]; rw [Set.inter_comm]

中文:
定理 set整数egral_indicator
  条件: (ht : 可测集 t)
  证明: by
  rw [integral_indicator ht]; rw [Measure.restrict_restrict ht]; rw [Set.inter_comm]

Depends on / 依赖: Measure, Measure.restrict_restrict, Set.inter_comm, integral_indicator, inter_comm, restrict_restrict
-/
theorem setIntegral_indicator (ht : MeasurableSet t) :
    ∫ x in s, t.indicator f x ∂μ = ∫ x in s inter t, f x ∂μ := by
  rw [integral_indicator ht]; rw [Measure.restrict_restrict ht]; rw [Set.inter_comm]

/--
theorem `integral_biUnion_eq_sum_powerset` / 定理 `integral_biUnion_eq_sum_powerset`

English:
theorem integral_biUnion_eq_sum_powerset
  statement: {ι : Type*} {t : Finset ι} {s : ι -> Set X}
  proof: by
  simp_rw [← integral_smul, ← integral_indicator (Finset.measurableSet_biUnion _ hs)]
  have A (u) (hu : u in t.powerset.filter (·.Nonempty)) : MeasurableSet (⋂ i in u, s i) := by
    refine u.measurableSet_biInter fun i hi => hs i ?_
    grind
  have : ∑ x in t.powerset with x.Nonempty, ∫ (a : X) in ⋂ i in x, s i, (-1 : Real) ^ (#x + 1) • f a ∂μ
      = ∑ x in t.powerset with x.Nonempty, ∫ a, indicator (⋂ i in x, s i)
        (fun a => (-1 : Real) ^ (#x + 1) • f a) a ∂μ := by
    apply Finset.sum_congr rfl (fun x hx => ?_)
    rw [← integral_indicator (A x hx)]
  rw [this]; rw [← integral_finsetSum]; swap
  · intro u hu
    rw [integrable_indicator_iff (A u hu)]
    apply Integrable.smul
    simp only [Finset.mem_filter, Finset.mem_powerset] at hu
    rcases hu.2 with ⟨i, hi⟩
    exact (hf i (hu.1 hi)).mono (biInter_subset_of_mem hi) le_rfl
  congr with x
  convert! Finset.indicator_biUnion_eq_sum_powerset t s f x with u hu
  rw [indicator_smul_apply]
  norm_cast

中文:
定理 integral_biUnion_eq_sum_powerset
  结论: {ι : 类型} {t : 有限集 ι} {s : ι -> 集合 X}
  证明: by
  simp_rw [← integral_smul, ← integral_indicator (Finset.measurableSet_biUnion _ hs)]
  have A (u) (hu : u in t.powerset.filter (·.Nonempty)) : MeasurableSet (⋂ i in u, s i) := by
    refine u.measurableSet_biInter fun i hi => hs i ?_
    grind
  have : ∑ x in t.powerset with x.Nonempty, ∫ (a : X) in ⋂ i in x, s i, (-1 : Real) ^ (#x + 1) • f a ∂μ
      = ∑ x in t.powerset with x.Nonempty, ∫ a, indicator (⋂ i in x, s i)
        (fun a => (-1 : Real) ^ (#x + 1) • f a) a ∂μ := by
    apply Finset.sum_congr rfl (fun x hx => ?_)
    rw [← integral_indicator (A x hx)]
  rw [this]; rw [← integral_finsetSum]; swap
  · intro u hu
    rw [integrable_indicator_iff (A u hu)]
    apply Integrable.smul
    simp only [Finset.mem_filter, Finset.mem_powerset] at hu
    rcases hu.2 with ⟨i, hi⟩
    exact (hf i (hu.1 hi)).mono (biInter_subset_of_mem hi) le_rfl
  congr with x
  convert! Finset.indicator_biUnion_eq_sum_powerset t s f x with u hu
  rw [indicator_smul_apply]
  norm_cast

Depends on / 依赖: Finset, Finset.measurableSet_biUnion, Finset.sum_congr, MeasurableSet, Nonempty, filter, indicator, integral_indicator, integral_smul, measurableSet_biInter, measurableSet_biUnion, powerset, simp_rw, sum_congr, t.powerset, t.powerset.filter, u.measurableSet_biInter, x.Nonempty
-/
theorem integral_biUnion_eq_sum_powerset {ι : Type*} {t : Finset ι} {s : ι -> Set X}
    (hs : forall i in t, MeasurableSet (s i)) (hf : forall i in t, IntegrableOn f (s i) μ) :
    ∫ x in ⋃ i in t, s i, f x ∂μ = ∑ u in t.powerset with u.Nonempty,
      (-1 : Real) ^ (#u + 1) • ∫ x in ⋂ i in u, s i, f x ∂μ := by
  simp_rw [← integral_smul, ← integral_indicator (Finset.measurableSet_biUnion _ hs)]
  have A (u) (hu : u in t.powerset.filter (·.Nonempty)) : MeasurableSet (⋂ i in u, s i) := by
    refine u.measurableSet_biInter fun i hi => hs i ?_
    grind
  have : ∑ x in t.powerset with x.Nonempty, ∫ (a : X) in ⋂ i in x, s i, (-1 : Real) ^ (#x + 1) • f a ∂μ
      = ∑ x in t.powerset with x.Nonempty, ∫ a, indicator (⋂ i in x, s i)
        (fun a => (-1 : Real) ^ (#x + 1) • f a) a ∂μ := by
    apply Finset.sum_congr rfl (fun x hx => ?_)
    rw [← integral_indicator (A x hx)]
  rw [this]; rw [← integral_finsetSum]; swap
  · intro u hu
    rw [integrable_indicator_iff (A u hu)]
    apply Integrable.smul
    simp only [Finset.mem_filter, Finset.mem_powerset] at hu
    rcases hu.2 with ⟨i, hi⟩
    exact (hf i (hu.1 hi)).mono (biInter_subset_of_mem hi) le_rfl
  congr with x
  convert! Finset.indicator_biUnion_eq_sum_powerset t s f x with u hu
  rw [indicator_smul_apply]
  norm_cast

/--
theorem `ofReal_setIntegral_one_of_measure_ne_top` / 定理 `ofReal_setIntegral_one_of_measure_ne_top`

English:
theorem ofReal_setIntegral_one_of_measure_ne_top
  statement: {X : Type*} {m : MeasurableSpace X}
  proof: calc
    ENNReal.ofReal (∫ _ in s, (1 : Real) ∂μ) = ENNReal.ofReal (∫ _ in s, ‖(1 : Real)‖ ∂μ) := by
      simp only [norm_one]
    _ = ∫⁻ _ in s, 1 ∂μ := by simp [measureReal_def, hs]
    _ = μ s := setLIntegral_one _

中文:
定理 of实数_set整数egral_one_of_measure_ne_top
  结论: {X : 类型} {m : 可测空间 X}
  证明: calc
    ENNReal.ofReal (∫ _ in s, (1 : Real) ∂μ) = ENNReal.ofReal (∫ _ in s, ‖(1 : Real)‖ ∂μ) := by
      simp only [norm_one]
    _ = ∫⁻ _ in s, 1 ∂μ := by simp [measureReal_def, hs]
    _ = μ s := setLIntegral_one _

Depends on / 依赖: ENNReal, ENNReal.ofReal, finiteness, measureReal_def, norm_one, ofReal, setLIntegral_one
-/
theorem ofReal_setIntegral_one_of_measure_ne_top {X : Type*} {m : MeasurableSpace X}
    {μ : Measure X} {s : Set X} (hs : μ s != ∞ := by finiteness) :
    ENNReal.ofReal (∫ _ in s, (1 : Real) ∂μ) = μ s :=
  calc
    ENNReal.ofReal (∫ _ in s, (1 : Real) ∂μ) = ENNReal.ofReal (∫ _ in s, ‖(1 : Real)‖ ∂μ) := by
      simp only [norm_one]
    _ = ∫⁻ _ in s, 1 ∂μ := by simp [measureReal_def, hs]
    _ = μ s := setLIntegral_one _

/--
theorem `ofReal_setIntegral_one` / 定理 `ofReal_setIntegral_one`

English:
theorem ofReal_setIntegral_one
  statement: {X : Type*} {_ : MeasurableSpace X} (μ : Measure X)
  proof: ofReal_setIntegral_one_of_measure_ne_top

中文:
定理 of实数_set整数egral_one
  结论: {X : 类型} {_ : 可测空间 X} (μ : 测度 X)
  证明: ofReal_setIntegral_one_of_measure_ne_top

Depends on / 依赖: ofReal_setIntegral_one_of_measure_ne_top
-/
theorem ofReal_setIntegral_one {X : Type*} {_ : MeasurableSpace X} (μ : Measure X)
    [IsFiniteMeasure μ] (s : Set X) : ENNReal.ofReal (∫ _ in s, (1 : Real) ∂μ) = μ s :=
  ofReal_setIntegral_one_of_measure_ne_top

/--
theorem `setIntegral_one_eq_measureReal` / 定理 `setIntegral_one_eq_measureReal`

English:
theorem setIntegral_one_eq_measureReal
  statement: {X : Type*} {m : MeasurableSpace X}
  proof: by simp

中文:
定理 set整数egral_one_eq_measure实数
  结论: {X : 类型} {m : 可测空间 X}
  证明: by simp
-/
theorem setIntegral_one_eq_measureReal {X : Type*} {m : MeasurableSpace X}
    {μ : Measure X} {s : Set X} :
    ∫ _ in s, (1 : Real) ∂μ = μ.real s := by simp

/--
theorem `measureReal_biUnion_eq_sum_powerset` / 定理 `measureReal_biUnion_eq_sum_powerset`

English:
theorem measureReal_biUnion_eq_sum_powerset
  statement: {ι : Type*} {t : Finset ι} {s : ι -> Set X}
  proof: by
  simp_rw [← setIntegral_one_eq_measureReal]
  apply integral_biUnion_eq_sum_powerset hs
  intro i hi
  simpa using (hf i hi).lt_top

中文:
定理 measure实数_biUnion_eq_sum_powerset
  结论: {ι : 类型} {t : 有限集 ι} {s : ι -> 集合 X}
  证明: by
  simp_rw [← setIntegral_one_eq_measureReal]
  apply integral_biUnion_eq_sum_powerset hs
  intro i hi
  simpa using (hf i hi).lt_top

Depends on / 依赖: Nonempty, finiteness, integral_biUnion_eq_sum_powerset, lt_top, powerset, setIntegral_one_eq_measureReal, simp_rw, t.powerset, u.Nonempty
-/
theorem measureReal_biUnion_eq_sum_powerset {ι : Type*} {t : Finset ι} {s : ι -> Set X}
    (hs : forall i in t, MeasurableSet (s i)) (hf : forall i in t, μ (s i) != ∞ := by finiteness) :
    μ.real (⋃ i in t, s i) = ∑ u in t.powerset with u.Nonempty,
      (-1 : Real) ^ (#u + 1) * μ.real (⋂ i in u, s i) := by
  simp_rw [← setIntegral_one_eq_measureReal]
  apply integral_biUnion_eq_sum_powerset hs
  intro i hi
  simpa using (hf i hi).lt_top

/--
theorem `integral_piecewise` / 定理 `integral_piecewise`

English:
theorem integral_piecewise
  statement: [DecidablePred (· in s)] (hs : MeasurableSet s) (hf : IntegrableOn f s μ)
  proof: by
  rw [← Set.indicator_add_compl_eq_piecewise]; rw [integral_add' (hf.integrable_indicator hs) (hg.integrable_indicator hs.compl)]; rw [integral_indicator hs]; rw [integral_indicator hs.compl]

中文:
定理 integral_piecewise
  结论: [DecidablePred (· in s)] (hs : 可测集 s) (hf : 整数egrableOn f s μ)
  证明: by
  rw [← Set.indicator_add_compl_eq_piecewise]; rw [integral_add' (hf.integrable_indicator hs) (hg.integrable_indicator hs.compl)]; rw [integral_indicator hs]; rw [integral_indicator hs.compl]

Depends on / 依赖: Set.indicator_add_compl_eq_piecewise, hf.integrable_indicator, hg.integrable_indicator, hs.compl, indicator_add_compl_eq_piecewise, integrable_indicator, integral_add, integral_indicator
-/
theorem integral_piecewise [DecidablePred (· in s)] (hs : MeasurableSet s) (hf : IntegrableOn f s μ)
    (hg : IntegrableOn g sᶜ μ) :
    ∫ x, s.piecewise f g x ∂μ = ∫ x in s, f x ∂μ + ∫ x in sᶜ, g x ∂μ := by
  rw [← Set.indicator_add_compl_eq_piecewise]; rw [integral_add' (hf.integrable_indicator hs) (hg.integrable_indicator hs.compl)]; rw [integral_indicator hs]; rw [integral_indicator hs.compl]

/--
theorem `tendsto_setIntegral_of_monotone₀` / 定理 `tendsto_setIntegral_of_monotone₀`

English:
theorem tendsto_setIntegral_of_monotone₀
  proof: by
  refine .of_neBot_imp fun hne => ?_
  have := (atTop_neBot_iff.mp hne).2
  have hfi' : ∫⁻ x in ⋃ n, s n, ‖f x‖₊ ∂μ < ∞ := hfi.2
  set S := ⋃ i, s i
  have hSm : NullMeasurableSet S μ := MeasurableSet.iUnion_of_monotone h_mono hsm
  have hsub {i} : s i subseteq S := subset_iUnion s i
  rw [← withDensity_apply₀ _ hSm] at hfi'
  set ν := μ.withDensity (‖f ·‖ₑ) with hν
  refine Metric.nhds_basis_closedBall.tendsto_right_iff.2 fun ε ε0 => ?_
  lift ε to Real>=0 using ε0.le
  have : forallᶠ i in atTop, ν (s i) in Icc (ν S - ε) (ν S + ε) :=
    tendsto_measure_iUnion_atTop h_mono (ENNReal.Icc_mem_nhds hfi'.ne (ENNReal.coe_pos.2 ε0).ne')
  filter_upwards [this] with i hi
  rw [mem_closedBall_iff_norm']; rw [← setIntegral_sdiff₀ (hsm i) hfi hsub]; rw [← coe_nnnorm]; rw [NNReal.coe_le_coe]; rw [← ENNReal.coe_le_coe]
  refine (enorm_integral_le_lintegral_enorm _).trans ?_
  have hsm' : NullMeasurableSet (s i) ν := (hsm i).mono_ac (withDensity_absolutelyContinuous ..)
  rw [← withDensity_apply₀ _ (hSm.diff (hsm _))]; rw [← hν]; rw [measure_sdiff hsub hsm']
  exacts [tsub_le_iff_tsub_le.mp hi.1,
    (hi.2.trans_lt <| ENNReal.add_lt_top.2 ⟨hfi', ENNReal.coe_lt_top⟩).ne]

中文:
定理 tendsto_set整数egral_of_monotone₀
  证明: by
  refine .of_neBot_imp fun hne => ?_
  have := (atTop_neBot_iff.mp hne).2
  have hfi' : ∫⁻ x in ⋃ n, s n, ‖f x‖₊ ∂μ < ∞ := hfi.2
  set S := ⋃ i, s i
  have hSm : NullMeasurableSet S μ := MeasurableSet.iUnion_of_monotone h_mono hsm
  have hsub {i} : s i subseteq S := subset_iUnion s i
  rw [← withDensity_apply₀ _ hSm] at hfi'
  set ν := μ.withDensity (‖f ·‖ₑ) with hν
  refine Metric.nhds_basis_closedBall.tendsto_right_iff.2 fun ε ε0 => ?_
  lift ε to Real>=0 using ε0.le
  have : forallᶠ i in atTop, ν (s i) in Icc (ν S - ε) (ν S + ε) :=
    tendsto_measure_iUnion_atTop h_mono (ENNReal.Icc_mem_nhds hfi'.ne (ENNReal.coe_pos.2 ε0).ne')
  filter_upwards [this] with i hi
  rw [mem_closedBall_iff_norm']; rw [← setIntegral_sdiff₀ (hsm i) hfi hsub]; rw [← coe_nnnorm]; rw [NNReal.coe_le_coe]; rw [← ENNReal.coe_le_coe]
  refine (enorm_integral_le_lintegral_enorm _).trans ?_
  have hsm' : NullMeasurableSet (s i) ν := (hsm i).mono_ac (withDensity_absolutelyContinuous ..)
  rw [← withDensity_apply₀ _ (hSm.diff (hsm _))]; rw [← hν]; rw [measure_sdiff hsub hsm']
  exacts [tsub_le_iff_tsub_le.mp hi.1,
    (hi.2.trans_lt <| ENNReal.add_lt_top.2 ⟨hfi', ENNReal.coe_lt_top⟩).ne]

Depends on / 依赖: MeasurableSet, MeasurableSet.iUnion_of_monotone, Metric, Metric.nhds_basis_closedBall.tendsto_right_iff, NullMeasurableSet, atTop_neBot_iff, atTop_neBot_iff.mp, h_mono, iUnion_of_monotone, nhds_basis_closedBall, of_neBot_imp, subset_iUnion, subseteq, tendsto_right_iff, withDensity
-/
theorem tendsto_setIntegral_of_monotone₀
    {ι : Type*} [Preorder ι] [(atTop : Filter ι).IsCountablyGenerated]
    {s : ι -> Set X} (hsm : forall i, NullMeasurableSet (s i) μ) (h_mono : Monotone s)
    (hfi : IntegrableOn f (⋃ n, s n) μ) :
    Tendsto (fun i => ∫ x in s i, f x ∂μ) atTop (𝓝 (∫ x in ⋃ n, s n, f x ∂μ)) := by
  refine .of_neBot_imp fun hne => ?_
  have := (atTop_neBot_iff.mp hne).2
  have hfi' : ∫⁻ x in ⋃ n, s n, ‖f x‖₊ ∂μ < ∞ := hfi.2
  set S := ⋃ i, s i
  have hSm : NullMeasurableSet S μ := MeasurableSet.iUnion_of_monotone h_mono hsm
  have hsub {i} : s i subseteq S := subset_iUnion s i
  rw [← withDensity_apply₀ _ hSm] at hfi'
  set ν := μ.withDensity (‖f ·‖ₑ) with hν
  refine Metric.nhds_basis_closedBall.tendsto_right_iff.2 fun ε ε0 => ?_
  lift ε to Real>=0 using ε0.le
  have : forallᶠ i in atTop, ν (s i) in Icc (ν S - ε) (ν S + ε) :=
    tendsto_measure_iUnion_atTop h_mono (ENNReal.Icc_mem_nhds hfi'.ne (ENNReal.coe_pos.2 ε0).ne')
  filter_upwards [this] with i hi
  rw [mem_closedBall_iff_norm']; rw [← setIntegral_sdiff₀ (hsm i) hfi hsub]; rw [← coe_nnnorm]; rw [NNReal.coe_le_coe]; rw [← ENNReal.coe_le_coe]
  refine (enorm_integral_le_lintegral_enorm _).trans ?_
  have hsm' : NullMeasurableSet (s i) ν := (hsm i).mono_ac (withDensity_absolutelyContinuous ..)
  rw [← withDensity_apply₀ _ (hSm.diff (hsm _))]; rw [← hν]; rw [measure_sdiff hsub hsm']
  exacts [tsub_le_iff_tsub_le.mp hi.1,
    (hi.2.trans_lt <| ENNReal.add_lt_top.2 ⟨hfi', ENNReal.coe_lt_top⟩).ne]

/--
theorem `tendsto_setIntegral_of_monotone` / 定理 `tendsto_setIntegral_of_monotone`

English:
theorem tendsto_setIntegral_of_monotone
  proof: tendsto_setIntegral_of_monotone₀ (hsm · |>.nullMeasurableSet) h_mono hfi

中文:
定理 tendsto_set整数egral_of_monotone
  证明: tendsto_setIntegral_of_monotone₀ (hsm · |>.nullMeasurableSet) h_mono hfi

Depends on / 依赖: h_mono, nullMeasurableSet
-/
theorem tendsto_setIntegral_of_monotone
    {ι : Type*} [Preorder ι] [(atTop : Filter ι).IsCountablyGenerated]
    {s : ι -> Set X} (hsm : forall i, MeasurableSet (s i)) (h_mono : Monotone s)
    (hfi : IntegrableOn f (⋃ n, s n) μ) :
    Tendsto (fun i => ∫ x in s i, f x ∂μ) atTop (𝓝 (∫ x in ⋃ n, s n, f x ∂μ)) :=
  tendsto_setIntegral_of_monotone₀ (hsm · |>.nullMeasurableSet) h_mono hfi

/--
theorem `tendsto_setIntegral_of_antitone` / 定理 `tendsto_setIntegral_of_antitone`

English:
theorem tendsto_setIntegral_of_antitone
  proof: by
  refine .of_neBot_imp fun hne => ?_
  have := (atTop_neBot_iff.mp hne).2
  rcases hfi with ⟨i₀, hi₀⟩
  suffices Tendsto (∫ x in s i₀, f x ∂μ - ∫ x in s i₀ \ s ·, f x ∂μ) atTop
      (𝓝 (∫ x in s i₀, f x ∂μ - ∫ x in ⋃ i, s i₀ \ s i, f x ∂μ)) by
convert! this.congr' (eventually_ge_atTop i₀).mono fun i hi => ?_
    · rw [← sdiff_iInter, setIntegral_sdiff _ hi₀ (iInter_subset _ _), sub_sub_cancel]
      exact .iInter_of_antitone h_anti hsm
    · rw [setIntegral_sdiff (hsm i) hi₀ (h_anti hi), sub_sub_cancel]
  apply tendsto_const_nhds.sub
  refine tendsto_setIntegral_of_monotone (by measurability) ?_ ?_
  · exact fun i j h => sdiff_subset_sdiff_right (h_anti h)
  · rw [← sdiff_iInter]
    exact hi₀.mono_set sdiff_subset

中文:
定理 tendsto_set整数egral_of_antitone
  证明: by
  refine .of_neBot_imp fun hne => ?_
  have := (atTop_neBot_iff.mp hne).2
  rcases hfi with ⟨i₀, hi₀⟩
  suffices Tendsto (∫ x in s i₀, f x ∂μ - ∫ x in s i₀ \ s ·, f x ∂μ) atTop
      (𝓝 (∫ x in s i₀, f x ∂μ - ∫ x in ⋃ i, s i₀ \ s i, f x ∂μ)) by
convert! this.congr' (eventually_ge_atTop i₀).mono fun i hi => ?_
    · rw [← sdiff_iInter, setIntegral_sdiff _ hi₀ (iInter_subset _ _), sub_sub_cancel]
      exact .iInter_of_antitone h_anti hsm
    · rw [setIntegral_sdiff (hsm i) hi₀ (h_anti hi), sub_sub_cancel]
  apply tendsto_const_nhds.sub
  refine tendsto_setIntegral_of_monotone (by measurability) ?_ ?_
  · exact fun i j h => sdiff_subset_sdiff_right (h_anti h)
  · rw [← sdiff_iInter]
    exact hi₀.mono_set sdiff_subset

Depends on / 依赖: Tendsto, atTop_neBot_iff, atTop_neBot_iff.mp, convert, eventually_ge_atTop, h_anti, iInter_of_antitone, iInter_subset, of_neBot_imp, sdiff_iInter, setIntegral_sdiff, sub_sub_cancel, tendsto_c, this.congr
-/
theorem tendsto_setIntegral_of_antitone
    {ι : Type*} [Preorder ι] [(atTop : Filter ι).IsCountablyGenerated]
    {s : ι -> Set X} (hsm : forall i, MeasurableSet (s i)) (h_anti : Antitone s)
    (hfi : exists i, IntegrableOn f (s i) μ) :
    Tendsto (fun i => ∫ x in s i, f x ∂μ) atTop (𝓝 (∫ x in ⋂ n, s n, f x ∂μ)) := by
  refine .of_neBot_imp fun hne => ?_
  have := (atTop_neBot_iff.mp hne).2
  rcases hfi with ⟨i₀, hi₀⟩
  suffices Tendsto (∫ x in s i₀, f x ∂μ - ∫ x in s i₀ \ s ·, f x ∂μ) atTop
      (𝓝 (∫ x in s i₀, f x ∂μ - ∫ x in ⋃ i, s i₀ \ s i, f x ∂μ)) by
convert! this.congr' (eventually_ge_atTop i₀).mono fun i hi => ?_
    · rw [← sdiff_iInter, setIntegral_sdiff _ hi₀ (iInter_subset _ _), sub_sub_cancel]
      exact .iInter_of_antitone h_anti hsm
    · rw [setIntegral_sdiff (hsm i) hi₀ (h_anti hi), sub_sub_cancel]
  apply tendsto_const_nhds.sub
  refine tendsto_setIntegral_of_monotone (by measurability) ?_ ?_
  · exact fun i j h => sdiff_subset_sdiff_right (h_anti h)
  · rw [← sdiff_iInter]
    exact hi₀.mono_set sdiff_subset

/--
theorem `hasSum_integral_iUnion_ae` / 定理 `hasSum_integral_iUnion_ae`

English:
theorem hasSum_integral_iUnion_ae
  statement: {ι : Type*} [Countable ι] {s : ι -> Set X}
  proof: by
  simp only [IntegrableOn, Measure.restrict_iUnion_ae hd hm] at hfi ⊢
  exact hasSum_integral_measure hfi

中文:
定理 hasSum_integral_iUnion_ae
  结论: {ι : 类型} [可数 ι] {s : ι -> 集合 X}
  证明: by
  simp only [IntegrableOn, Measure.restrict_iUnion_ae hd hm] at hfi ⊢
  exact hasSum_integral_measure hfi

Depends on / 依赖: IntegrableOn, Measure, Measure.restrict_iUnion_ae, hasSum_integral_measure, restrict_iUnion_ae
-/
theorem hasSum_integral_iUnion_ae {ι : Type*} [Countable ι] {s : ι -> Set X}
    (hm : forall i, NullMeasurableSet (s i) μ) (hd : Pairwise (AEDisjoint μ on s))
    (hfi : IntegrableOn f (⋃ i, s i) μ) :
    HasSum (fun n => ∫ x in s n, f x ∂μ) (∫ x in ⋃ n, s n, f x ∂μ) := by
  simp only [IntegrableOn, Measure.restrict_iUnion_ae hd hm] at hfi ⊢
  exact hasSum_integral_measure hfi

/--
theorem `hasSum_integral_iUnion` / 定理 `hasSum_integral_iUnion`

English:
theorem hasSum_integral_iUnion
  statement: {ι : Type*} [Countable ι] {s : ι -> Set X}
  proof: hasSum_integral_iUnion_ae (fun i => (hm i).nullMeasurableSet) (hd.mono fun _ _ h => h.aedisjoint)
    hfi

中文:
定理 hasSum_integral_iUnion
  结论: {ι : 类型} [可数 ι] {s : ι -> 集合 X}
  证明: hasSum_integral_iUnion_ae (fun i => (hm i).nullMeasurableSet) (hd.mono fun _ _ h => h.aedisjoint)
    hfi

Depends on / 依赖: aedisjoint, h.aedisjoint, hasSum_integral_iUnion_ae, hd.mono, nullMeasurableSet
-/
theorem hasSum_integral_iUnion {ι : Type*} [Countable ι] {s : ι -> Set X}
    (hm : forall i, MeasurableSet (s i)) (hd : Pairwise (Disjoint on s))
    (hfi : IntegrableOn f (⋃ i, s i) μ) :
    HasSum (fun n => ∫ x in s n, f x ∂μ) (∫ x in ⋃ n, s n, f x ∂μ) :=
  hasSum_integral_iUnion_ae (fun i => (hm i).nullMeasurableSet) (hd.mono fun _ _ h => h.aedisjoint)
    hfi

/--
theorem `integral_iUnion` / 定理 `integral_iUnion`

English:
theorem integral_iUnion
  statement: {ι : Type*} [Countable ι] {s : ι -> Set X} (hm : forall i, MeasurableSet (s i))
  proof: (HasSum.tsum_eq (hasSum_integral_iUnion hm hd hfi)).symm

中文:
定理 integral_iUnion
  结论: {ι : 类型} [可数 ι] {s : ι -> 集合 X} (hm : 对任意 i, 可测集 (s i))
  证明: (HasSum.tsum_eq (hasSum_integral_iUnion hm hd hfi)).symm

Depends on / 依赖: HasSum, HasSum.tsum_eq, hasSum_integral_iUnion, tsum_eq
-/
theorem integral_iUnion {ι : Type*} [Countable ι] {s : ι -> Set X} (hm : forall i, MeasurableSet (s i))
    (hd : Pairwise (Disjoint on s)) (hfi : IntegrableOn f (⋃ i, s i) μ) :
    ∫ x in ⋃ n, s n, f x ∂μ = ∑' n, ∫ x in s n, f x ∂μ :=
  (HasSum.tsum_eq (hasSum_integral_iUnion hm hd hfi)).symm

/--
theorem `integral_iUnion_ae` / 定理 `integral_iUnion_ae`

English:
theorem integral_iUnion_ae
  statement: {ι : Type*} [Countable ι] {s : ι -> Set X}
  proof: (HasSum.tsum_eq (hasSum_integral_iUnion_ae hm hd hfi)).symm

中文:
定理 integral_iUnion_ae
  结论: {ι : 类型} [可数 ι] {s : ι -> 集合 X}
  证明: (HasSum.tsum_eq (hasSum_integral_iUnion_ae hm hd hfi)).symm

Depends on / 依赖: HasSum, HasSum.tsum_eq, hasSum_integral_iUnion_ae, tsum_eq
-/
theorem integral_iUnion_ae {ι : Type*} [Countable ι] {s : ι -> Set X}
    (hm : forall i, NullMeasurableSet (s i) μ) (hd : Pairwise (AEDisjoint μ on s))
    (hfi : IntegrableOn f (⋃ i, s i) μ) : ∫ x in ⋃ n, s n, f x ∂μ = ∑' n, ∫ x in s n, f x ∂μ :=
  (HasSum.tsum_eq (hasSum_integral_iUnion_ae hm hd hfi)).symm

/--
theorem `setIntegral_eq_zero_of_ae_eq_zero` / 定理 `setIntegral_eq_zero_of_ae_eq_zero`

English:
theorem setIntegral_eq_zero_of_ae_eq_zero
  given: (ht_eq : forallᵐ x ∂μ, x in t -> f x = 0)
  proof: by
  by_cases hf : AEStronglyMeasurable f (μ.restrict t); swap
  · rw [integral_undef]
    contrapose hf
    exact hf.1
  have : ∫ x in t, hf.mk f x ∂μ = 0 := by
    refine integral_eq_zero_of_ae ?_
    rw [EventuallyEq]; rw [ae_restrict_iff (hf.stronglyMeasurable_mk.measurableSet_eq_fun stronglyMeasurable_zero)]
    filter_upwards [ae_imp_of_ae_restrict hf.ae_eq_mk, ht_eq] with x hx h'x h''x
    rw [← hx h''x]
    exact h'x h''x
  rw [← this]
  exact integral_congr_ae hf.ae_eq_mk

中文:
定理 set整数egral_eq_zero_of_ae_eq_zero
  条件: (ht_eq : 对任意ᵐ x ∂μ, x in t -> f x = 0)
  证明: by
  by_cases hf : AEStronglyMeasurable f (μ.restrict t); swap
  · rw [integral_undef]
    contrapose hf
    exact hf.1
  have : ∫ x in t, hf.mk f x ∂μ = 0 := by
    refine integral_eq_zero_of_ae ?_
    rw [EventuallyEq]; rw [ae_restrict_iff (hf.stronglyMeasurable_mk.measurableSet_eq_fun stronglyMeasurable_zero)]
    filter_upwards [ae_imp_of_ae_restrict hf.ae_eq_mk, ht_eq] with x hx h'x h''x
    rw [← hx h''x]
    exact h'x h''x
  rw [← this]
  exact integral_congr_ae hf.ae_eq_mk

Depends on / 依赖: AEStronglyMeasurable, EventuallyEq, ae_eq_mk, ae_imp_of_ae_restrict, ae_restrict_iff, contrapose, filter_upwards, hf.ae_eq_mk, hf.mk, hf.stronglyMeasurable_mk.measurableSet_eq_fun, ht_eq, integral_congr_ae, integral_eq_zero_of_ae, integral_undef, measurableSet_eq_fun, restrict, stronglyMeasurable_mk, stronglyMeasurable_zero
-/
theorem setIntegral_eq_zero_of_ae_eq_zero (ht_eq : forallᵐ x ∂μ, x in t -> f x = 0) :
    ∫ x in t, f x ∂μ = 0 := by
  by_cases hf : AEStronglyMeasurable f (μ.restrict t); swap
  · rw [integral_undef]
    contrapose hf
    exact hf.1
  have : ∫ x in t, hf.mk f x ∂μ = 0 := by
    refine integral_eq_zero_of_ae ?_
    rw [EventuallyEq]; rw [ae_restrict_iff (hf.stronglyMeasurable_mk.measurableSet_eq_fun stronglyMeasurable_zero)]
    filter_upwards [ae_imp_of_ae_restrict hf.ae_eq_mk, ht_eq] with x hx h'x h''x
    rw [← hx h''x]
    exact h'x h''x
  rw [← this]
  exact integral_congr_ae hf.ae_eq_mk

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
    ∫ x in t, f x ∂μ = 0 :=
  setIntegral_eq_zero_of_ae_eq_zero (Eventually.of_forall ht_eq)

/--
theorem `frequently_ae_ne_zero_of_setIntegral_ne_zero` / 定理 `frequently_ae_ne_zero_of_setIntegral_ne_zero`

English:
theorem frequently_ae_ne_zero_of_setIntegral_ne_zero
  given: (hU : ∫ x in t, f x ∂μ != 0)
  proof: frequently_ae_ne_zero_of_integral_ne_zero hU

中文:
定理 frequently_ae_ne_zero_of_set整数egral_ne_zero
  条件: (hU : ∫ x in t, f x ∂μ != 0)
  证明: frequently_ae_ne_zero_of_integral_ne_zero hU

Depends on / 依赖: frequently_ae_ne_zero_of_integral_ne_zero
-/
theorem frequently_ae_ne_zero_of_setIntegral_ne_zero (hU : ∫ x in t, f x ∂μ != 0) :
    existsᶠ x in ae (μ.restrict t), f x != 0 :=
  frequently_ae_ne_zero_of_integral_ne_zero hU

/--
theorem `exists_ne_zero_of_setIntegral_ne_zero` / 定理 `exists_ne_zero_of_setIntegral_ne_zero`

English:
theorem exists_ne_zero_of_setIntegral_ne_zero
  given: (hU : ∫ x in t, f x ∂μ != 0)
  proof: by
  contrapose! hU; exact setIntegral_eq_zero_of_forall_eq_zero hU

中文:
定理 存在_ne_zero_of_set整数egral_ne_zero
  条件: (hU : ∫ x in t, f x ∂μ != 0)
  证明: by
  contrapose! hU; exact setIntegral_eq_zero_of_forall_eq_zero hU

Depends on / 依赖: contrapose, setIntegral_eq_zero_of_forall_eq_zero
-/
theorem exists_ne_zero_of_setIntegral_ne_zero (hU : ∫ x in t, f x ∂μ != 0) :
    exists x, x in t ∧ f x != 0 := by
  contrapose! hU; exact setIntegral_eq_zero_of_forall_eq_zero hU

/--
theorem `integral_union_eq_left_of_ae_aux` / 定理 `integral_union_eq_left_of_ae_aux`

English:
theorem integral_union_eq_left_of_ae_aux
  statement: (ht_eq : forallᵐ x ∂μ.restrict t, f x = 0)
  proof: by
  let k := f ⁻¹' {0}
  have hk : MeasurableSet k := by borelize E; exact haux.measurable (measurableSet_singleton _)
  have h's : IntegrableOn f s μ := H.mono subset_union_left le_rfl
  have A : forall u : Set X, ∫ x in u inter k, f x ∂μ = 0 := fun u =>
    setIntegral_eq_zero_of_forall_eq_zero fun x hx => hx.2
  rw [← integral_inter_add_sdiff hk h's]; rw [← integral_inter_add_sdiff hk H]; rw [A]; rw [A]; rw [zero_add]; rw [zero_add]; rw [union_sdiff_distrib]; rw [union_comm]
  apply setIntegral_congr_set
  rw [union_ae_eq_right]
  apply measure_mono_null sdiff_subset
  rw [measure_eq_zero_iff_ae_notMem]
  filter_upwards [ae_imp_of_ae_restrict ht_eq] with x hx h'x using h'x.2 (hx h'x.1)

中文:
定理 integral_union_eq_left_of_ae_aux
  结论: (ht_eq : 对任意ᵐ x ∂μ.restrict t, f x = 0)
  证明: by
  let k := f ⁻¹' {0}
  have hk : MeasurableSet k := by borelize E; exact haux.measurable (measurableSet_singleton _)
  have h's : IntegrableOn f s μ := H.mono subset_union_left le_rfl
  have A : forall u : Set X, ∫ x in u inter k, f x ∂μ = 0 := fun u =>
    setIntegral_eq_zero_of_forall_eq_zero fun x hx => hx.2
  rw [← integral_inter_add_sdiff hk h's]; rw [← integral_inter_add_sdiff hk H]; rw [A]; rw [A]; rw [zero_add]; rw [zero_add]; rw [union_sdiff_distrib]; rw [union_comm]
  apply setIntegral_congr_set
  rw [union_ae_eq_right]
  apply measure_mono_null sdiff_subset
  rw [measure_eq_zero_iff_ae_notMem]
  filter_upwards [ae_imp_of_ae_restrict ht_eq] with x hx h'x using h'x.2 (hx h'x.1)

Depends on / 依赖: H.mono, IntegrableOn, MeasurableSet, borelize, haux.measurable, integral_inter_add_sdiff, le_rfl, measurable, measurableSet_singleton, setIntegral_congr_set, setIntegral_eq_zero_of_forall_eq_zero, subset_union_left, union_comm, union_sdiff_distrib, zero_add
-/
theorem integral_union_eq_left_of_ae_aux (ht_eq : forallᵐ x ∂μ.restrict t, f x = 0)
    (haux : StronglyMeasurable f) (H : IntegrableOn f (s union t) μ) :
    ∫ x in s union t, f x ∂μ = ∫ x in s, f x ∂μ := by
  let k := f ⁻¹' {0}
  have hk : MeasurableSet k := by borelize E; exact haux.measurable (measurableSet_singleton _)
  have h's : IntegrableOn f s μ := H.mono subset_union_left le_rfl
  have A : forall u : Set X, ∫ x in u inter k, f x ∂μ = 0 := fun u =>
    setIntegral_eq_zero_of_forall_eq_zero fun x hx => hx.2
  rw [← integral_inter_add_sdiff hk h's]; rw [← integral_inter_add_sdiff hk H]; rw [A]; rw [A]; rw [zero_add]; rw [zero_add]; rw [union_sdiff_distrib]; rw [union_comm]
  apply setIntegral_congr_set
  rw [union_ae_eq_right]
  apply measure_mono_null sdiff_subset
  rw [measure_eq_zero_iff_ae_notMem]
  filter_upwards [ae_imp_of_ae_restrict ht_eq] with x hx h'x using h'x.2 (hx h'x.1)

/--
theorem `integral_union_eq_left_of_ae` / 定理 `integral_union_eq_left_of_ae`

English:
theorem integral_union_eq_left_of_ae
  given: (ht_eq : forallᵐ x ∂μ.restrict t, f x = 0)
  proof: by
  have ht : IntegrableOn f t μ := by apply integrableOn_zero.congr_fun_ae; symm; exact ht_eq
  by_cases H : IntegrableOn f (s union t) μ; swap
  · rw [integral_undef H, integral_undef]; simpa [integrableOn_union, ht] using! H
  let f' := H.1.mk f
  calc
    ∫ x : X in s union t, f x ∂μ = ∫ x : X in s union t, f' x ∂μ := integral_congr_ae H.1.ae_eq_mk
    _ = ∫ x in s, f' x ∂μ := by
      apply
        integral_union_eq_left_of_ae_aux _ H.1.stronglyMeasurable_mk (H.congr_fun_ae H.1.ae_eq_mk)
      filter_upwards [ht_eq,
        ae_mono (Measure.restrict_mono subset_union_right le_rfl) H.1.ae_eq_mk] with x hx h'x
      rw [← h'x]; rw [hx]
    _ = ∫ x in s, f x ∂μ :=
      integral_congr_ae
        (ae_mono (Measure.restrict_mono subset_union_left le_rfl) H.1.ae_eq_mk.symm)

中文:
定理 integral_union_eq_left_of_ae
  条件: (ht_eq : 对任意ᵐ x ∂μ.restrict t, f x = 0)
  证明: by
  have ht : IntegrableOn f t μ := by apply integrableOn_zero.congr_fun_ae; symm; exact ht_eq
  by_cases H : IntegrableOn f (s union t) μ; swap
  · rw [integral_undef H, integral_undef]; simpa [integrableOn_union, ht] using! H
  let f' := H.1.mk f
  calc
    ∫ x : X in s union t, f x ∂μ = ∫ x : X in s union t, f' x ∂μ := integral_congr_ae H.1.ae_eq_mk
    _ = ∫ x in s, f' x ∂μ := by
      apply
        integral_union_eq_left_of_ae_aux _ H.1.stronglyMeasurable_mk (H.congr_fun_ae H.1.ae_eq_mk)
      filter_upwards [ht_eq,
        ae_mono (Measure.restrict_mono subset_union_right le_rfl) H.1.ae_eq_mk] with x hx h'x
      rw [← h'x]; rw [hx]
    _ = ∫ x in s, f x ∂μ :=
      integral_congr_ae
        (ae_mono (Measure.restrict_mono subset_union_left le_rfl) H.1.ae_eq_mk.symm)

Depends on / 依赖: H.congr_fun_ae, IntegrableOn, ae_eq_mk, ae_mono, congr_fun_ae, filter_upwards, ht_eq, integrableOn_union, integrableOn_zero, integrableOn_zero.congr_fun_ae, integral_congr_ae, integral_undef, integral_union_eq_left_of_ae_aux, stronglyMeasurable_mk
-/
theorem integral_union_eq_left_of_ae (ht_eq : forallᵐ x ∂μ.restrict t, f x = 0) :
    ∫ x in s union t, f x ∂μ = ∫ x in s, f x ∂μ := by
  have ht : IntegrableOn f t μ := by apply integrableOn_zero.congr_fun_ae; symm; exact ht_eq
  by_cases H : IntegrableOn f (s union t) μ; swap
  · rw [integral_undef H, integral_undef]; simpa [integrableOn_union, ht] using! H
  let f' := H.1.mk f
  calc
    ∫ x : X in s union t, f x ∂μ = ∫ x : X in s union t, f' x ∂μ := integral_congr_ae H.1.ae_eq_mk
    _ = ∫ x in s, f' x ∂μ := by
      apply
        integral_union_eq_left_of_ae_aux _ H.1.stronglyMeasurable_mk (H.congr_fun_ae H.1.ae_eq_mk)
      filter_upwards [ht_eq,
        ae_mono (Measure.restrict_mono subset_union_right le_rfl) H.1.ae_eq_mk] with x hx h'x
      rw [← h'x]; rw [hx]
    _ = ∫ x in s, f x ∂μ :=
      integral_congr_ae
        (ae_mono (Measure.restrict_mono subset_union_left le_rfl) H.1.ae_eq_mk.symm)

/--
theorem `integral_union_eq_left_of_forall₀` / 定理 `integral_union_eq_left_of_forall₀`

English:
theorem integral_union_eq_left_of_forall₀
  statement: {f : X -> E} (ht : NullMeasurableSet t μ)
  proof: integral_union_eq_left_of_ae ((ae_restrict_iff'₀ ht).2 (Eventually.of_forall ht_eq))

中文:
定理 integral_union_eq_left_of_对任意₀
  结论: {f : X -> E} (ht : NullMeasurableSet t μ)
  证明: integral_union_eq_left_of_ae ((ae_restrict_iff'₀ ht).2 (Eventually.of_forall ht_eq))

Depends on / 依赖: Eventually, Eventually.of_forall, ae_restrict_iff, ht_eq, integral_union_eq_left_of_ae, of_forall
-/
theorem integral_union_eq_left_of_forall₀ {f : X -> E} (ht : NullMeasurableSet t μ)
    (ht_eq : forall x in t, f x = 0) : ∫ x in s union t, f x ∂μ = ∫ x in s, f x ∂μ :=
  integral_union_eq_left_of_ae ((ae_restrict_iff'₀ ht).2 (Eventually.of_forall ht_eq))

/--
theorem `integral_union_eq_left_of_forall` / 定理 `integral_union_eq_left_of_forall`

English:
theorem integral_union_eq_left_of_forall
  statement: {f : X -> E} (ht : MeasurableSet t)
  proof: integral_union_eq_left_of_forall₀ ht.nullMeasurableSet ht_eq

中文:
定理 integral_union_eq_left_of_对任意
  结论: {f : X -> E} (ht : 可测集 t)
  证明: integral_union_eq_left_of_forall₀ ht.nullMeasurableSet ht_eq

Depends on / 依赖: ht.nullMeasurableSet, ht_eq, nullMeasurableSet
-/
theorem integral_union_eq_left_of_forall {f : X -> E} (ht : MeasurableSet t)
    (ht_eq : forall x in t, f x = 0) : ∫ x in s union t, f x ∂μ = ∫ x in s, f x ∂μ :=
  integral_union_eq_left_of_forall₀ ht.nullMeasurableSet ht_eq

/--
theorem `setIntegral_eq_of_subset_of_ae_sdiff_eq_zero_aux` / 定理 `setIntegral_eq_of_subset_of_ae_sdiff_eq_zero_aux`

English:
theorem setIntegral_eq_of_subset_of_ae_sdiff_eq_zero_aux
  statement: (hts : s subseteq t)
  proof: by
  let k := f ⁻¹' {0}
  have hk : MeasurableSet k := by borelize E; exact haux.measurable (measurableSet_singleton _)
  calc
    ∫ x in t, f x ∂μ = ∫ x in t inter k, f x ∂μ + ∫ x in t \ k, f x ∂μ := by
      rw [integral_inter_add_sdiff hk h'aux]
    _ = ∫ x in t \ k, f x ∂μ := by
      rw [setIntegral_eq_zero_of_forall_eq_zero fun x hx => ?_]; rw [zero_add]; exact hx.2
    _ = ∫ x in s \ k, f x ∂μ := by
      apply setIntegral_congr_set
      filter_upwards [h't] with x hx
      change (x in t \ k) = (x in s \ k)
      simp only [eq_iff_iff, and_congr_left_iff, Set.mem_sdiff]
      intro h'x
      by_cases xs : x in s
      · simp only [xs, hts xs]
      · simp only [xs, iff_false]
        intro xt
        exact h'x (hx ⟨xt, xs⟩)
    _ = ∫ x in s inter k, f x ∂μ + ∫ x in s \ k, f x ∂μ := by
      have : forall x in s inter k, f x = 0 := fun x hx => hx.2
      rw [setIntegral_eq_zero_of_forall_eq_zero this]; rw [zero_add]
    _ = ∫ x in s, f x ∂μ := by rw [integral_inter_add_sdiff hk (h'aux.mono hts le_rfl)]

@[deprecated (since := "2026-06-03")]
alias setIntegral_eq_of_subset_of_ae_diff_eq_zero_aux :=
  setIntegral_eq_of_subset_of_ae_sdiff_eq_zero_aux

中文:
定理 set整数egral_eq_of_subset_of_ae_sdiff_eq_zero_aux
  结论: (hts : s subseteq t)
  证明: by
  let k := f ⁻¹' {0}
  have hk : MeasurableSet k := by borelize E; exact haux.measurable (measurableSet_singleton _)
  calc
    ∫ x in t, f x ∂μ = ∫ x in t inter k, f x ∂μ + ∫ x in t \ k, f x ∂μ := by
      rw [integral_inter_add_sdiff hk h'aux]
    _ = ∫ x in t \ k, f x ∂μ := by
      rw [setIntegral_eq_zero_of_forall_eq_zero fun x hx => ?_]; rw [zero_add]; exact hx.2
    _ = ∫ x in s \ k, f x ∂μ := by
      apply setIntegral_congr_set
      filter_upwards [h't] with x hx
      change (x in t \ k) = (x in s \ k)
      simp only [eq_iff_iff, and_congr_left_iff, Set.mem_sdiff]
      intro h'x
      by_cases xs : x in s
      · simp only [xs, hts xs]
      · simp only [xs, iff_false]
        intro xt
        exact h'x (hx ⟨xt, xs⟩)
    _ = ∫ x in s inter k, f x ∂μ + ∫ x in s \ k, f x ∂μ := by
      have : forall x in s inter k, f x = 0 := fun x hx => hx.2
      rw [setIntegral_eq_zero_of_forall_eq_zero this]; rw [zero_add]
    _ = ∫ x in s, f x ∂μ := by rw [integral_inter_add_sdiff hk (h'aux.mono hts le_rfl)]

@[deprecated (since := "2026-06-03")]
alias setIntegral_eq_of_subset_of_ae_diff_eq_zero_aux :=
  setIntegral_eq_of_subset_of_ae_sdiff_eq_zero_aux

Depends on / 依赖: MeasurableSet, borelize, eq_iff_iff, filter_upwards, haux.measurable, integral_inter_add_sdiff, measurable, measurableSet_singleton, setIntegral_congr_set, setIntegral_eq_zero_of_forall_eq_zero, zero_add
-/
theorem setIntegral_eq_of_subset_of_ae_sdiff_eq_zero_aux (hts : s subseteq t)
    (h't : forallᵐ x ∂μ, x in t \ s -> f x = 0) (haux : StronglyMeasurable f)
    (h'aux : IntegrableOn f t μ) : ∫ x in t, f x ∂μ = ∫ x in s, f x ∂μ := by
  let k := f ⁻¹' {0}
  have hk : MeasurableSet k := by borelize E; exact haux.measurable (measurableSet_singleton _)
  calc
    ∫ x in t, f x ∂μ = ∫ x in t inter k, f x ∂μ + ∫ x in t \ k, f x ∂μ := by
      rw [integral_inter_add_sdiff hk h'aux]
    _ = ∫ x in t \ k, f x ∂μ := by
      rw [setIntegral_eq_zero_of_forall_eq_zero fun x hx => ?_]; rw [zero_add]; exact hx.2
    _ = ∫ x in s \ k, f x ∂μ := by
      apply setIntegral_congr_set
      filter_upwards [h't] with x hx
      change (x in t \ k) = (x in s \ k)
      simp only [eq_iff_iff, and_congr_left_iff, Set.mem_sdiff]
      intro h'x
      by_cases xs : x in s
      · simp only [xs, hts xs]
      · simp only [xs, iff_false]
        intro xt
        exact h'x (hx ⟨xt, xs⟩)
    _ = ∫ x in s inter k, f x ∂μ + ∫ x in s \ k, f x ∂μ := by
      have : forall x in s inter k, f x = 0 := fun x hx => hx.2
      rw [setIntegral_eq_zero_of_forall_eq_zero this]; rw [zero_add]
    _ = ∫ x in s, f x ∂μ := by rw [integral_inter_add_sdiff hk (h'aux.mono hts le_rfl)]

@[deprecated (since := "2026-06-03")]
alias setIntegral_eq_of_subset_of_ae_diff_eq_zero_aux :=
  setIntegral_eq_of_subset_of_ae_sdiff_eq_zero_aux

/--
theorem `setIntegral_eq_of_subset_of_ae_sdiff_eq_zero` / 定理 `setIntegral_eq_of_subset_of_ae_sdiff_eq_zero`

English:
theorem setIntegral_eq_of_subset_of_ae_sdiff_eq_zero
  statement: (ht : NullMeasurableSet t μ) (hts : s subseteq t)
  proof: by
  by_cases h : IntegrableOn f t μ; swap
  · have : ¬IntegrableOn f s μ := fun H => h (H.of_ae_sdiff_eq_zero ht h't)
    rw [integral_undef h]; rw [integral_undef this]
  let f' := h.1.mk f
  calc
    ∫ x in t, f x ∂μ = ∫ x in t, f' x ∂μ := integral_congr_ae h.1.ae_eq_mk
    _ = ∫ x in s, f' x ∂μ := by
      apply
        setIntegral_eq_of_subset_of_ae_sdiff_eq_zero_aux hts _ h.1.stronglyMeasurable_mk
          (h.congr h.1.ae_eq_mk)
      filter_upwards [h't, ae_imp_of_ae_restrict h.1.ae_eq_mk] with x hx h'x h''x
      rw [← h'x h''x.1]; rw [hx h''x]
    _ = ∫ x in s, f x ∂μ := by
      apply integral_congr_ae
      apply ae_restrict_of_ae_restrict_of_subset hts
      exact h.1.ae_eq_mk.symm

@[deprecated (since := "2026-06-03")]
alias setIntegral_eq_of_subset_of_ae_diff_eq_zero := setIntegral_eq_of_subset_of_ae_sdiff_eq_zero

中文:
定理 set整数egral_eq_of_subset_of_ae_sdiff_eq_zero
  结论: (ht : NullMeasurableSet t μ) (hts : s subseteq t)
  证明: by
  by_cases h : IntegrableOn f t μ; swap
  · have : ¬IntegrableOn f s μ := fun H => h (H.of_ae_sdiff_eq_zero ht h't)
    rw [integral_undef h]; rw [integral_undef this]
  let f' := h.1.mk f
  calc
    ∫ x in t, f x ∂μ = ∫ x in t, f' x ∂μ := integral_congr_ae h.1.ae_eq_mk
    _ = ∫ x in s, f' x ∂μ := by
      apply
        setIntegral_eq_of_subset_of_ae_sdiff_eq_zero_aux hts _ h.1.stronglyMeasurable_mk
          (h.congr h.1.ae_eq_mk)
      filter_upwards [h't, ae_imp_of_ae_restrict h.1.ae_eq_mk] with x hx h'x h''x
      rw [← h'x h''x.1]; rw [hx h''x]
    _ = ∫ x in s, f x ∂μ := by
      apply integral_congr_ae
      apply ae_restrict_of_ae_restrict_of_subset hts
      exact h.1.ae_eq_mk.symm

@[deprecated (since := "2026-06-03")]
alias setIntegral_eq_of_subset_of_ae_diff_eq_zero := setIntegral_eq_of_subset_of_ae_sdiff_eq_zero

Depends on / 依赖: H.of_ae_sdiff_eq_zero, IntegrableOn, ae_eq_mk, ae_imp_of_ae_restrict, filter_upwards, h.congr, integral_congr_ae, integral_undef, of_ae_sdiff_eq_zero, setIntegral_eq_of_subset_of_ae_sdiff_eq_zero_aux, stronglyMeasurable_mk
-/
theorem setIntegral_eq_of_subset_of_ae_sdiff_eq_zero (ht : NullMeasurableSet t μ) (hts : s subseteq t)
    (h't : forallᵐ x ∂μ, x in t \ s -> f x = 0) : ∫ x in t, f x ∂μ = ∫ x in s, f x ∂μ := by
  by_cases h : IntegrableOn f t μ; swap
  · have : ¬IntegrableOn f s μ := fun H => h (H.of_ae_sdiff_eq_zero ht h't)
    rw [integral_undef h]; rw [integral_undef this]
  let f' := h.1.mk f
  calc
    ∫ x in t, f x ∂μ = ∫ x in t, f' x ∂μ := integral_congr_ae h.1.ae_eq_mk
    _ = ∫ x in s, f' x ∂μ := by
      apply
        setIntegral_eq_of_subset_of_ae_sdiff_eq_zero_aux hts _ h.1.stronglyMeasurable_mk
          (h.congr h.1.ae_eq_mk)
      filter_upwards [h't, ae_imp_of_ae_restrict h.1.ae_eq_mk] with x hx h'x h''x
      rw [← h'x h''x.1]; rw [hx h''x]
    _ = ∫ x in s, f x ∂μ := by
      apply integral_congr_ae
      apply ae_restrict_of_ae_restrict_of_subset hts
      exact h.1.ae_eq_mk.symm

@[deprecated (since := "2026-06-03")]
alias setIntegral_eq_of_subset_of_ae_diff_eq_zero := setIntegral_eq_of_subset_of_ae_sdiff_eq_zero

/--
theorem `setIntegral_eq_of_subset_of_forall_sdiff_eq_zero` / 定理 `setIntegral_eq_of_subset_of_forall_sdiff_eq_zero`

English:
theorem setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
  statement: (ht : MeasurableSet t) (hts : s subseteq t)
  proof: setIntegral_eq_of_subset_of_ae_sdiff_eq_zero ht.nullMeasurableSet hts
    (Eventually.of_forall fun x hx => h't x hx)

@[deprecated (since := "2026-06-03")]
alias setIntegral_eq_of_subset_of_forall_diff_eq_zero :=
  setIntegral_eq_of_subset_of_forall_sdiff_eq_zero

中文:
定理 set整数egral_eq_of_subset_of_对任意_sdiff_eq_zero
  结论: (ht : 可测集 t) (hts : s subseteq t)
  证明: setIntegral_eq_of_subset_of_ae_sdiff_eq_zero ht.nullMeasurableSet hts
    (Eventually.of_forall fun x hx => h't x hx)

@[deprecated (since := "2026-06-03")]
alias setIntegral_eq_of_subset_of_forall_diff_eq_zero :=
  setIntegral_eq_of_subset_of_forall_sdiff_eq_zero

Depends on / 依赖: Eventually, Eventually.of_forall, ht.nullMeasurableSet, nullMeasurableSet, of_forall, setIntegral_eq_of_subset_of_ae_sdiff_eq_zero
-/
theorem setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (ht : MeasurableSet t) (hts : s subseteq t)
    (h't : forall x in t \ s, f x = 0) : ∫ x in t, f x ∂μ = ∫ x in s, f x ∂μ :=
  setIntegral_eq_of_subset_of_ae_sdiff_eq_zero ht.nullMeasurableSet hts
    (Eventually.of_forall fun x hx => h't x hx)

@[deprecated (since := "2026-06-03")]
alias setIntegral_eq_of_subset_of_forall_diff_eq_zero :=
  setIntegral_eq_of_subset_of_forall_sdiff_eq_zero

/--
theorem `setIntegral_eq_integral_of_ae_compl_eq_zero` / 定理 `setIntegral_eq_integral_of_ae_compl_eq_zero`

English:
theorem setIntegral_eq_integral_of_ae_compl_eq_zero
  given: (h : forallᵐ x ∂μ, x ∉ s -> f x = 0)
  proof: by
  symm
  nth_rw 1 [← setIntegral_univ]
  apply setIntegral_eq_of_subset_of_ae_sdiff_eq_zero nullMeasurableSet_univ (subset_univ _)
  filter_upwards [h] with x hx h'x using hx h'x.2

中文:
定理 set整数egral_eq_integral_of_ae_compl_eq_zero
  条件: (h : 对任意ᵐ x ∂μ, x ∉ s -> f x = 0)
  证明: by
  symm
  nth_rw 1 [← setIntegral_univ]
  apply setIntegral_eq_of_subset_of_ae_sdiff_eq_zero nullMeasurableSet_univ (subset_univ _)
  filter_upwards [h] with x hx h'x using hx h'x.2

Depends on / 依赖: filter_upwards, nth_rw, nullMeasurableSet_univ, setIntegral_eq_of_subset_of_ae_sdiff_eq_zero, setIntegral_univ, subset_univ
-/
theorem setIntegral_eq_integral_of_ae_compl_eq_zero (h : forallᵐ x ∂μ, x ∉ s -> f x = 0) :
    ∫ x in s, f x ∂μ = ∫ x, f x ∂μ := by
  symm
  nth_rw 1 [← setIntegral_univ]
  apply setIntegral_eq_of_subset_of_ae_sdiff_eq_zero nullMeasurableSet_univ (subset_univ _)
  filter_upwards [h] with x hx h'x using hx h'x.2

/--
theorem `setIntegral_eq_integral_of_forall_compl_eq_zero` / 定理 `setIntegral_eq_integral_of_forall_compl_eq_zero`

English:
theorem setIntegral_eq_integral_of_forall_compl_eq_zero
  given: (h : forall x, x ∉ s -> f x = 0)
  proof: setIntegral_eq_integral_of_ae_compl_eq_zero (Eventually.of_forall h)

中文:
定理 set整数egral_eq_integral_of_对任意_compl_eq_zero
  条件: (h : 对任意 x, x ∉ s -> f x = 0)
  证明: setIntegral_eq_integral_of_ae_compl_eq_zero (Eventually.of_forall h)

Depends on / 依赖: Eventually, Eventually.of_forall, of_forall, setIntegral_eq_integral_of_ae_compl_eq_zero
-/
theorem setIntegral_eq_integral_of_forall_compl_eq_zero (h : forall x, x ∉ s -> f x = 0) :
    ∫ x in s, f x ∂μ = ∫ x, f x ∂μ :=
  setIntegral_eq_integral_of_ae_compl_eq_zero (Eventually.of_forall h)

/--
theorem `setIntegral_neg_eq_setIntegral_nonpos` / 定理 `setIntegral_neg_eq_setIntegral_nonpos`

English:
theorem setIntegral_neg_eq_setIntegral_nonpos
  statement: [PartialOrder E] {f : X -> E}
  proof: by
  have h_union : {x | f x <= 0} = {x | f x < 0} union {x | f x = 0} := by
    simp_rw [le_iff_lt_or_eq, ofPred_or]
  rw [h_union]
  have B : NullMeasurableSet {x | f x = 0} μ :=
    hf.nullMeasurableSet_eq_fun aestronglyMeasurable_zero
  symm
  refine integral_union_eq_left_of_ae ?_
  filter_upwards [ae_restrict_mem₀ B] with x hx using hx

中文:
定理 set整数egral_neg_eq_set整数egral_nonpos
  结论: [偏序 E] {f : X -> E}
  证明: by
  have h_union : {x | f x <= 0} = {x | f x < 0} union {x | f x = 0} := by
    simp_rw [le_iff_lt_or_eq, ofPred_or]
  rw [h_union]
  have B : NullMeasurableSet {x | f x = 0} μ :=
    hf.nullMeasurableSet_eq_fun aestronglyMeasurable_zero
  symm
  refine integral_union_eq_left_of_ae ?_
  filter_upwards [ae_restrict_mem₀ B] with x hx using hx

Depends on / 依赖: NullMeasurableSet, aestronglyMeasurable_zero, filter_upwards, h_union, hf.nullMeasurableSet_eq_fun, integral_union_eq_left_of_ae, le_iff_lt_or_eq, nullMeasurableSet_eq_fun, ofPred_or, simp_rw
-/
theorem setIntegral_neg_eq_setIntegral_nonpos [PartialOrder E] {f : X -> E}
    (hf : AEStronglyMeasurable f μ) :
    ∫ x in {x | f x < 0}, f x ∂μ = ∫ x in {x | f x <= 0}, f x ∂μ := by
  have h_union : {x | f x <= 0} = {x | f x < 0} union {x | f x = 0} := by
    simp_rw [le_iff_lt_or_eq, ofPred_or]
  rw [h_union]
  have B : NullMeasurableSet {x | f x = 0} μ :=
    hf.nullMeasurableSet_eq_fun aestronglyMeasurable_zero
  symm
  refine integral_union_eq_left_of_ae ?_
  filter_upwards [ae_restrict_mem₀ B] with x hx using hx

/--
theorem `integral_norm_eq_pos_sub_neg` / 定理 `integral_norm_eq_pos_sub_neg`

English:
theorem integral_norm_eq_pos_sub_neg
  given: {f : X -> Real} (hfi : Integrable f μ)
  proof: have h_meas : NullMeasurableSet {x | 0 <= f x} μ :=
    aestronglyMeasurable_const.nullMeasurableSet_le hfi.1
  calc
    ∫ x, ‖f x‖ ∂μ = ∫ x in {x | 0 <= f x}, ‖f x‖ ∂μ + ∫ x in {x | 0 <= f x}ᶜ, ‖f x‖ ∂μ := by
      rw [← integral_add_compl₀ h_meas hfi.norm]
    _ = ∫ x in {x | 0 <= f x}, f x ∂μ + ∫ x in {x | 0 <= f x}ᶜ, ‖f x‖ ∂μ := by
      congr 1
      refine setIntegral_congr_fun₀ h_meas fun x hx => ?_
      rw [Real.norm_eq_abs]; rw [abs_eq_self.mpr _]
      exact hx
    _ = ∫ x in {x | 0 <= f x}, f x ∂μ - ∫ x in {x | 0 <= f x}ᶜ, f x ∂μ := by
      congr 1
      rw [← integral_neg]
      refine setIntegral_congr_fun₀ h_meas.compl fun x hx => ?_
      rw [Real.norm_eq_abs]; rw [abs_eq_neg_self.mpr _]
      rw [Set.mem_compl_iff]; rw [Set.notMem_ofPred_iff] at hx
      linarith
    _ = ∫ x in {x | 0 <= f x}, f x ∂μ - ∫ x in {x | f x <= 0}, f x ∂μ := by
      rw [← setIntegral_neg_eq_setIntegral_nonpos hfi.1]; rw [compl_ofPred]; simp only [not_le]

中文:
定理 integral_norm_eq_pos_sub_neg
  条件: {f : X -> 实数} (hfi : 可积 f μ)
  证明: have h_meas : NullMeasurableSet {x | 0 <= f x} μ :=
    aestronglyMeasurable_const.nullMeasurableSet_le hfi.1
  calc
    ∫ x, ‖f x‖ ∂μ = ∫ x in {x | 0 <= f x}, ‖f x‖ ∂μ + ∫ x in {x | 0 <= f x}ᶜ, ‖f x‖ ∂μ := by
      rw [← integral_add_compl₀ h_meas hfi.norm]
    _ = ∫ x in {x | 0 <= f x}, f x ∂μ + ∫ x in {x | 0 <= f x}ᶜ, ‖f x‖ ∂μ := by
      congr 1
      refine setIntegral_congr_fun₀ h_meas fun x hx => ?_
      rw [Real.norm_eq_abs]; rw [abs_eq_self.mpr _]
      exact hx
    _ = ∫ x in {x | 0 <= f x}, f x ∂μ - ∫ x in {x | 0 <= f x}ᶜ, f x ∂μ := by
      congr 1
      rw [← integral_neg]
      refine setIntegral_congr_fun₀ h_meas.compl fun x hx => ?_
      rw [Real.norm_eq_abs]; rw [abs_eq_neg_self.mpr _]
      rw [Set.mem_compl_iff]; rw [Set.notMem_ofPred_iff] at hx
      linarith
    _ = ∫ x in {x | 0 <= f x}, f x ∂μ - ∫ x in {x | f x <= 0}, f x ∂μ := by
      rw [← setIntegral_neg_eq_setIntegral_nonpos hfi.1]; rw [compl_ofPred]; simp only [not_le]

Depends on / 依赖: NullMeasurableSet, Real.norm_eq_abs, abs_eq_self, abs_eq_self.mpr, aestronglyMeasurable_const, aestronglyMeasurable_const.nullMeasurableSet_le, h_meas, hfi.norm, norm_eq_abs, nullMeasurableSet_le
-/
theorem integral_norm_eq_pos_sub_neg {f : X -> Real} (hfi : Integrable f μ) :
    ∫ x, ‖f x‖ ∂μ = ∫ x in {x | 0 <= f x}, f x ∂μ - ∫ x in {x | f x <= 0}, f x ∂μ :=
  have h_meas : NullMeasurableSet {x | 0 <= f x} μ :=
    aestronglyMeasurable_const.nullMeasurableSet_le hfi.1
  calc
    ∫ x, ‖f x‖ ∂μ = ∫ x in {x | 0 <= f x}, ‖f x‖ ∂μ + ∫ x in {x | 0 <= f x}ᶜ, ‖f x‖ ∂μ := by
      rw [← integral_add_compl₀ h_meas hfi.norm]
    _ = ∫ x in {x | 0 <= f x}, f x ∂μ + ∫ x in {x | 0 <= f x}ᶜ, ‖f x‖ ∂μ := by
      congr 1
      refine setIntegral_congr_fun₀ h_meas fun x hx => ?_
      rw [Real.norm_eq_abs]; rw [abs_eq_self.mpr _]
      exact hx
    _ = ∫ x in {x | 0 <= f x}, f x ∂μ - ∫ x in {x | 0 <= f x}ᶜ, f x ∂μ := by
      congr 1
      rw [← integral_neg]
      refine setIntegral_congr_fun₀ h_meas.compl fun x hx => ?_
      rw [Real.norm_eq_abs]; rw [abs_eq_neg_self.mpr _]
      rw [Set.mem_compl_iff]; rw [Set.notMem_ofPred_iff] at hx
      linarith
    _ = ∫ x in {x | 0 <= f x}, f x ∂μ - ∫ x in {x | f x <= 0}, f x ∂μ := by
      rw [← setIntegral_neg_eq_setIntegral_nonpos hfi.1]; rw [compl_ofPred]; simp only [not_le]

/--
theorem `setIntegral_const` / 定理 `setIntegral_const`

English:
theorem setIntegral_const
  given: [CompleteSpace E] (c : E)
  statement: ∫ _ in s, c ∂μ = μ.real s • c
  proof: by
  rw [integral_const]; rw [measureReal_restrict_apply_univ]

@[simp]

中文:
定理 set整数egral_const
  条件: [完备空间 E] (c : E)
  结论: ∫ _ in s, c ∂μ = μ.real s • c
  证明: by
  rw [integral_const]; rw [measureReal_restrict_apply_univ]

@[simp]

Depends on / 依赖: integral_const, measureReal_restrict_apply_univ
-/
theorem setIntegral_const [CompleteSpace E] (c : E) : ∫ _ in s, c ∂μ = μ.real s • c := by
  rw [integral_const]; rw [measureReal_restrict_apply_univ]

@[simp]
/--
theorem `integral_indicator_const` / 定理 `integral_indicator_const`

English:
theorem integral_indicator_const
  given: [CompleteSpace E] (e : E) ⦃s
  statement: Set X⦄ (s_meas : MeasurableSet s) :
  proof: by
  rw [integral_indicator s_meas]; rw [← setIntegral_const]

@[simp]

中文:
定理 integral_indicator_const
  条件: [完备空间 E] (e : E) ⦃s
  结论: 集合 X⦄ (s_meas : 可测集 s) :
  证明: by
  rw [integral_indicator s_meas]; rw [← setIntegral_const]

@[simp]

Depends on / 依赖: integral_indicator, s_meas, setIntegral_const
-/
theorem integral_indicator_const [CompleteSpace E] (e : E) ⦃s : Set X⦄ (s_meas : MeasurableSet s) :
    ∫ x : X, s.indicator (fun _ : X => e) x ∂μ = μ.real s • e := by
  rw [integral_indicator s_meas]; rw [← setIntegral_const]

@[simp]
/--
theorem `integral_indicator_one` / 定理 `integral_indicator_one`

English:
theorem integral_indicator_one
  given: ⦃s
  statement: Set X⦄ (hs : MeasurableSet s) :
  proof: (integral_indicator_const 1 hs).trans ((smul_eq_mul ..).trans (mul_one _))

中文:
定理 integral_indicator_one
  条件: ⦃s
  结论: 集合 X⦄ (hs : 可测集 s) :
  证明: (integral_indicator_const 1 hs).trans ((smul_eq_mul ..).trans (mul_one _))

Depends on / 依赖: integral_indicator_const, mul_one, smul_eq_mul
-/
theorem integral_indicator_one ⦃s : Set X⦄ (hs : MeasurableSet s) :
    ∫ x, s.indicator 1 x ∂μ = μ.real s :=
  (integral_indicator_const 1 hs).trans ((smul_eq_mul ..).trans (mul_one _))

/--
theorem `setIntegral_indicatorConstLp` / 定理 `setIntegral_indicatorConstLp`

English:
theorem setIntegral_indicatorConstLp
  statement: [CompleteSpace E]
  proof: calc
    ∫ x in s, indicatorConstLp p ht hμt e x ∂μ = ∫ x in s, t.indicator (fun _ => e) x ∂μ := by
      rw [setIntegral_congr_ae hs (indicatorConstLp_coeFn.mono fun x hx _ => hx)]
    _ = (μ.real (t inter s)) • e := by rw [integral_indicator_const _ ht, measureReal_restrict_apply ht]

中文:
定理 set整数egral_indicatorConstLp
  结论: [完备空间 E]
  证明: calc
    ∫ x in s, indicatorConstLp p ht hμt e x ∂μ = ∫ x in s, t.indicator (fun _ => e) x ∂μ := by
      rw [setIntegral_congr_ae hs (indicatorConstLp_coeFn.mono fun x hx _ => hx)]
    _ = (μ.real (t inter s)) • e := by rw [integral_indicator_const _ ht, measureReal_restrict_apply ht]

Depends on / 依赖: indicator, indicatorConstLp, indicatorConstLp_coeFn, indicatorConstLp_coeFn.mono, integral_indicator_const, measureReal_restrict_apply, setIntegral_congr_ae, t.indicator
-/
theorem setIntegral_indicatorConstLp [CompleteSpace E]
    {p : Real>=0∞} (hs : MeasurableSet s) (ht : MeasurableSet t) (hμt : μ t != ∞) (e : E) :
    ∫ x in s, indicatorConstLp p ht hμt e x ∂μ = μ.real (t inter s) • e :=
  calc
    ∫ x in s, indicatorConstLp p ht hμt e x ∂μ = ∫ x in s, t.indicator (fun _ => e) x ∂μ := by
      rw [setIntegral_congr_ae hs (indicatorConstLp_coeFn.mono fun x hx _ => hx)]
    _ = (μ.real (t inter s)) • e := by rw [integral_indicator_const _ ht, measureReal_restrict_apply ht]

/--
theorem `integral_indicatorConstLp` / 定理 `integral_indicatorConstLp`

English:
theorem integral_indicatorConstLp
  statement: [CompleteSpace E]
  proof: calc
    ∫ x, indicatorConstLp p ht hμt e x ∂μ = ∫ x in univ, indicatorConstLp p ht hμt e x ∂μ := by
      rw [setIntegral_univ]
    _ = μ.real (t inter univ) • e := setIntegral_indicatorConstLp MeasurableSet.univ ht hμt e
    _ = μ.real t • e := by rw [inter_univ]

中文:
定理 integral_indicatorConstLp
  结论: [完备空间 E]
  证明: calc
    ∫ x, indicatorConstLp p ht hμt e x ∂μ = ∫ x in univ, indicatorConstLp p ht hμt e x ∂μ := by
      rw [setIntegral_univ]
    _ = μ.real (t inter univ) • e := setIntegral_indicatorConstLp MeasurableSet.univ ht hμt e
    _ = μ.real t • e := by rw [inter_univ]

Depends on / 依赖: MeasurableSet, MeasurableSet.univ, indicatorConstLp, inter_univ, setIntegral_indicatorConstLp, setIntegral_univ
-/
theorem integral_indicatorConstLp [CompleteSpace E]
    {p : Real>=0∞} (ht : MeasurableSet t) (hμt : μ t != ∞) (e : E) :
    ∫ x, indicatorConstLp p ht hμt e x ∂μ = μ.real t • e :=
  calc
    ∫ x, indicatorConstLp p ht hμt e x ∂μ = ∫ x in univ, indicatorConstLp p ht hμt e x ∂μ := by
      rw [setIntegral_univ]
    _ = μ.real (t inter univ) • e := setIntegral_indicatorConstLp MeasurableSet.univ ht hμt e
    _ = μ.real t • e := by rw [inter_univ]

/--
theorem `setIntegral_map` / 定理 `setIntegral_map`

English:
theorem setIntegral_map
  statement: {Y} [MeasurableSpace Y] {g : X -> Y} {f : Y -> E} {s : Set Y}
  proof: by
  rw [Measure.restrict_map_of_aemeasurable hg hs]; rw [integral_map (hg.mono_measure Measure.restrict_le_self) (hf.mono_measure _)]
  exact Measure.map_mono_of_aemeasurable Measure.restrict_le_self hg

中文:
定理 set整数egral_map
  结论: {Y} [可测空间 Y] {g : X -> Y} {f : Y -> E} {s : 集合 Y}
  证明: by
  rw [Measure.restrict_map_of_aemeasurable hg hs]; rw [integral_map (hg.mono_measure Measure.restrict_le_self) (hf.mono_measure _)]
  exact Measure.map_mono_of_aemeasurable Measure.restrict_le_self hg

Depends on / 依赖: Measure, Measure.map_mono_of_aemeasurable, Measure.restrict_le_self, Measure.restrict_map_of_aemeasurable, hf.mono_measure, hg.mono_measure, integral_map, map_mono_of_aemeasurable, mono_measure, restrict_le_self, restrict_map_of_aemeasurable
-/
theorem setIntegral_map {Y} [MeasurableSpace Y] {g : X -> Y} {f : Y -> E} {s : Set Y}
    (hs : MeasurableSet s) (hf : AEStronglyMeasurable f (Measure.map g μ)) (hg : AEMeasurable g μ) :
    ∫ y in s, f y ∂Measure.map g μ = ∫ x in g ⁻¹' s, f (g x) ∂μ := by
  rw [Measure.restrict_map_of_aemeasurable hg hs]; rw [integral_map (hg.mono_measure Measure.restrict_le_self) (hf.mono_measure _)]
  exact Measure.map_mono_of_aemeasurable Measure.restrict_le_self hg

/--
theorem `_root_.MeasurableEmbedding.setIntegral_map` / 定理 `_root_.MeasurableEmbedding.setIntegral_map`

English:
theorem _root_.MeasurableEmbedding.setIntegral_map
  statement: {Y} {_ : MeasurableSpace Y} {f : X -> Y}
  proof: by
  rw [hf.restrict_map]; rw [hf.integral_map]

中文:
定理 _root_.可测嵌入.set整数egral_map
  结论: {Y} {_ : 可测空间 Y} {f : X -> Y}
  证明: by
  rw [hf.restrict_map]; rw [hf.integral_map]

Depends on / 依赖: hf.integral_map, hf.restrict_map, integral_map, restrict_map
-/
theorem _root_.MeasurableEmbedding.setIntegral_map {Y} {_ : MeasurableSpace Y} {f : X -> Y}
    (hf : MeasurableEmbedding f) (g : Y -> E) (s : Set Y) :
    ∫ y in s, g y ∂Measure.map f μ = ∫ x in f ⁻¹' s, g (f x) ∂μ := by
  rw [hf.restrict_map]; rw [hf.integral_map]

/--
theorem `_root_.Topology.IsClosedEmbedding.setIntegral_map` / 定理 `_root_.Topology.IsClosedEmbedding.setIntegral_map`

English:
theorem _root_.Topology.IsClosedEmbedding.setIntegral_map
  statement: [TopologicalSpace X] [BorelSpace X] {Y}
  proof: hg.measurableEmbedding.setIntegral_map _ _

中文:
定理 _root_.拓扑.是闭嵌入.set整数egral_map
  结论: [拓扑空间 X] [Borel空间 X] {Y}
  证明: hg.measurableEmbedding.setIntegral_map _ _

Depends on / 依赖: hg.measurableEmbedding.setIntegral_map, measurableEmbedding, setIntegral_map
-/
theorem _root_.Topology.IsClosedEmbedding.setIntegral_map [TopologicalSpace X] [BorelSpace X] {Y}
    [MeasurableSpace Y] [TopologicalSpace Y] [BorelSpace Y] {g : X -> Y} {f : Y -> E} (s : Set Y)
    (hg : IsClosedEmbedding g) : ∫ y in s, f y ∂Measure.map g μ = ∫ x in g ⁻¹' s, f (g x) ∂μ :=
  hg.measurableEmbedding.setIntegral_map _ _

/--
theorem `MeasurePreserving.setIntegral_preimage_emb` / 定理 `MeasurePreserving.setIntegral_preimage_emb`

English:
theorem MeasurePreserving.setIntegral_preimage_emb
  statement: {Y} {_ : MeasurableSpace Y} {f : X -> Y} {ν}
  proof: (h₁.restrict_preimage_emb h₂ s).integral_comp h₂ _

中文:
定理 保测.set整数egral_preimage_emb
  结论: {Y} {_ : 可测空间 Y} {f : X -> Y} {ν}
  证明: (h₁.restrict_preimage_emb h₂ s).integral_comp h₂ _

Depends on / 依赖: integral_comp, restrict_preimage_emb
-/
theorem MeasurePreserving.setIntegral_preimage_emb {Y} {_ : MeasurableSpace Y} {f : X -> Y} {ν}
    (h₁ : MeasurePreserving f μ ν) (h₂ : MeasurableEmbedding f) (g : Y -> E) (s : Set Y) :
    ∫ x in f ⁻¹' s, g (f x) ∂μ = ∫ y in s, g y ∂ν :=
  (h₁.restrict_preimage_emb h₂ s).integral_comp h₂ _

/--
theorem `MeasurePreserving.setIntegral_image_emb` / 定理 `MeasurePreserving.setIntegral_image_emb`

English:
theorem MeasurePreserving.setIntegral_image_emb
  statement: {Y} {_ : MeasurableSpace Y} {f : X -> Y} {ν}
  proof: Eq.symm (h₁.restrict_image_emb h₂ s).integral_comp h₂ _

中文:
定理 保测.set整数egral_image_emb
  结论: {Y} {_ : 可测空间 Y} {f : X -> Y} {ν}
  证明: Eq.symm (h₁.restrict_image_emb h₂ s).integral_comp h₂ _

Depends on / 依赖: Eq.symm, integral_comp, restrict_image_emb
-/
theorem MeasurePreserving.setIntegral_image_emb {Y} {_ : MeasurableSpace Y} {f : X -> Y} {ν}
    (h₁ : MeasurePreserving f μ ν) (h₂ : MeasurableEmbedding f) (g : Y -> E) (s : Set X) :
    ∫ y in f '' s, g y ∂ν = ∫ x in s, g (f x) ∂μ :=
Eq.symm (h₁.restrict_image_emb h₂ s).integral_comp h₂ _

/--
theorem `setIntegral_map_equiv` / 定理 `setIntegral_map_equiv`

English:
theorem setIntegral_map_equiv
  given: {Y} [MeasurableSpace Y] (e : X ≃ᵐ Y) (f : Y -> E) (s : Set Y)
  proof: e.measurableEmbedding.setIntegral_map f s

中文:
定理 set整数egral_map_equiv
  条件: {Y} [可测空间 Y] (e : X ≃ᵐ Y) (f : Y -> E) (s : 集合 Y)
  证明: e.measurableEmbedding.setIntegral_map f s

Depends on / 依赖: e.measurableEmbedding.setIntegral_map, measurableEmbedding, setIntegral_map
-/
theorem setIntegral_map_equiv {Y} [MeasurableSpace Y] (e : X ≃ᵐ Y) (f : Y -> E) (s : Set Y) :
    ∫ y in s, f y ∂Measure.map e μ = ∫ x in e ⁻¹' s, f (e x) ∂μ :=
  e.measurableEmbedding.setIntegral_map f s

/--
theorem `norm_setIntegral_le_of_norm_le_const_ae` / 定理 `norm_setIntegral_le_of_norm_le_const_ae`

English:
theorem norm_setIntegral_le_of_norm_le_const_ae
  statement: {C : Real} (hs : μ s < ∞)
  proof: by
  rw [← Measure.restrict_apply_univ] at *
  have : IsFiniteMeasure (μ.restrict s) := ⟨hs⟩
  simpa using norm_integral_le_of_norm_le_const hC

中文:
定理 norm_set整数egral_le_of_norm_le_const_ae
  结论: {C : 实数} (hs : μ s < ∞)
  证明: by
  rw [← Measure.restrict_apply_univ] at *
  have : IsFiniteMeasure (μ.restrict s) := ⟨hs⟩
  simpa using norm_integral_le_of_norm_le_const hC

Depends on / 依赖: IsFiniteMeasure, Measure, Measure.restrict_apply_univ, norm_integral_le_of_norm_le_const, restrict, restrict_apply_univ
-/
theorem norm_setIntegral_le_of_norm_le_const_ae {C : Real} (hs : μ s < ∞)
    (hC : forallᵐ x ∂μ.restrict s, ‖f x‖ <= C) : ‖∫ x in s, f x ∂μ‖ <= C * μ.real s := by
  rw [← Measure.restrict_apply_univ] at *
  have : IsFiniteMeasure (μ.restrict s) := ⟨hs⟩
  simpa using norm_integral_le_of_norm_le_const hC

/--
theorem `norm_setIntegral_le_of_norm_le_const_ae'` / 定理 `norm_setIntegral_le_of_norm_le_const_ae'`

English:
theorem norm_setIntegral_le_of_norm_le_const_ae'
  statement: {C : Real} (hs : μ s < ∞)
  proof: by
  by_cases hfm : AEStronglyMeasurable f (μ.restrict s)
  · apply norm_setIntegral_le_of_norm_le_const_ae hs
    have A : forallᵐ x : X ∂μ, x in s -> ‖AEStronglyMeasurable.mk f hfm x‖ <= C := by
      filter_upwards [hC, hfm.ae_mem_imp_eq_mk] with _ h1 h2 h3
      rw [← h2 h3]
      exact h1 h3
    have B : MeasurableSet {x | ‖hfm.mk f x‖ <= C} :=
      hfm.stronglyMeasurable_mk.norm.measurable measurableSet_Iic
    filter_upwards [hfm.ae_eq_mk, (ae_restrict_iff B).2 A] with _ h1 _
    rwa [h1]
  · rw [integral_non_aestronglyMeasurable hfm]
    have : existsᵐ (x : X) ∂μ, x in s := by
      apply frequently_ae_mem_iff.mpr
      contrapose hfm
      simp [Measure.restrict_eq_zero.mpr hfm]
    rcases (this.and_eventually hC).exists with ⟨x, hx, h'x⟩
    have : 0 <= C := (norm_nonneg _).trans (h'x hx)
    simp only [norm_zero, ge_iff_le]
    positivity

中文:
定理 norm_set整数egral_le_of_norm_le_const_ae'
  结论: {C : 实数} (hs : μ s < ∞)
  证明: by
  by_cases hfm : AEStronglyMeasurable f (μ.restrict s)
  · apply norm_setIntegral_le_of_norm_le_const_ae hs
    have A : forallᵐ x : X ∂μ, x in s -> ‖AEStronglyMeasurable.mk f hfm x‖ <= C := by
      filter_upwards [hC, hfm.ae_mem_imp_eq_mk] with _ h1 h2 h3
      rw [← h2 h3]
      exact h1 h3
    have B : MeasurableSet {x | ‖hfm.mk f x‖ <= C} :=
      hfm.stronglyMeasurable_mk.norm.measurable measurableSet_Iic
    filter_upwards [hfm.ae_eq_mk, (ae_restrict_iff B).2 A] with _ h1 _
    rwa [h1]
  · rw [integral_non_aestronglyMeasurable hfm]
    have : existsᵐ (x : X) ∂μ, x in s := by
      apply frequently_ae_mem_iff.mpr
      contrapose hfm
      simp [Measure.restrict_eq_zero.mpr hfm]
    rcases (this.and_eventually hC).exists with ⟨x, hx, h'x⟩
    have : 0 <= C := (norm_nonneg _).trans (h'x hx)
    simp only [norm_zero, ge_iff_le]
    positivity

Depends on / 依赖: AEStronglyMeasurable, AEStronglyMeasurable.mk, MeasurableSet, ae_eq_mk, ae_mem_imp_eq_mk, ae_restrict_iff, filter_upwards, hfm.ae_eq_mk, hfm.ae_mem_imp_eq_mk, hfm.mk, hfm.stronglyMeasurable_mk.norm.measurable, integral_non_aestronglyMeasurable, measurable, measurableSet_Iic, norm_setIntegral_le_of_norm_le_const_ae, restrict, stronglyMeasurable_mk
-/
theorem norm_setIntegral_le_of_norm_le_const_ae' {C : Real} (hs : μ s < ∞)
    (hC : forallᵐ x ∂μ, x in s -> ‖f x‖ <= C) : ‖∫ x in s, f x ∂μ‖ <= C * μ.real s := by
  by_cases hfm : AEStronglyMeasurable f (μ.restrict s)
  · apply norm_setIntegral_le_of_norm_le_const_ae hs
    have A : forallᵐ x : X ∂μ, x in s -> ‖AEStronglyMeasurable.mk f hfm x‖ <= C := by
      filter_upwards [hC, hfm.ae_mem_imp_eq_mk] with _ h1 h2 h3
      rw [← h2 h3]
      exact h1 h3
    have B : MeasurableSet {x | ‖hfm.mk f x‖ <= C} :=
      hfm.stronglyMeasurable_mk.norm.measurable measurableSet_Iic
    filter_upwards [hfm.ae_eq_mk, (ae_restrict_iff B).2 A] with _ h1 _
    rwa [h1]
  · rw [integral_non_aestronglyMeasurable hfm]
    have : existsᵐ (x : X) ∂μ, x in s := by
      apply frequently_ae_mem_iff.mpr
      contrapose hfm
      simp [Measure.restrict_eq_zero.mpr hfm]
    rcases (this.and_eventually hC).exists with ⟨x, hx, h'x⟩
    have : 0 <= C := (norm_nonneg _).trans (h'x hx)
    simp only [norm_zero, ge_iff_le]
    positivity

/--
theorem `norm_setIntegral_le_of_norm_le_const` / 定理 `norm_setIntegral_le_of_norm_le_const`

English:
theorem norm_setIntegral_le_of_norm_le_const
  given: {C : Real} (hs : μ s < ∞) (hC : forall x in s, ‖f x‖ <= C)
  proof: norm_setIntegral_le_of_norm_le_const_ae' hs (Eventually.of_forall hC)

中文:
定理 norm_set整数egral_le_of_norm_le_const
  条件: {C : 实数} (hs : μ s < ∞) (hC : 对任意 x in s, ‖f x‖ <= C)
  证明: norm_setIntegral_le_of_norm_le_const_ae' hs (Eventually.of_forall hC)

Depends on / 依赖: Eventually, Eventually.of_forall, norm_setIntegral_le_of_norm_le_const_ae, of_forall
-/
theorem norm_setIntegral_le_of_norm_le_const {C : Real} (hs : μ s < ∞) (hC : forall x in s, ‖f x‖ <= C) :
    ‖∫ x in s, f x ∂μ‖ <= C * μ.real s :=
  norm_setIntegral_le_of_norm_le_const_ae' hs (Eventually.of_forall hC)

/--
theorem `norm_integral_sub_setIntegral_le` / 定理 `norm_integral_sub_setIntegral_le`

English:
theorem norm_integral_sub_setIntegral_le
  statement: [IsFiniteMeasure μ] {C : Real}
  proof: by
  have h0 : ∫ (x : X), f x ∂μ - ∫ x in s, f x ∂μ = ∫ x in sᶜ, f x ∂μ := by
    rw [sub_eq_iff_eq_add]; rw [add_comm]; rw [integral_add_compl hs hf1]
  have h1 : ∫ x in sᶜ, ‖f x‖ ∂μ <= ∫ _ in sᶜ, C ∂μ :=
    integral_mono_ae hf1.norm.restrict (integrable_const C) (ae_restrict_of_ae hf)
  have h2 : ∫ _ in sᶜ, C ∂μ = μ.real sᶜ * C := by
    rw [setIntegral_const C]; rw [smul_eq_mul]
  rw [h0]; rw [← h2]
  exact le_trans (norm_integral_le_integral_norm f) h1

中文:
定理 norm_integral_sub_set整数egral_le
  结论: [是有限测度 μ] {C : 实数}
  证明: by
  have h0 : ∫ (x : X), f x ∂μ - ∫ x in s, f x ∂μ = ∫ x in sᶜ, f x ∂μ := by
    rw [sub_eq_iff_eq_add]; rw [add_comm]; rw [integral_add_compl hs hf1]
  have h1 : ∫ x in sᶜ, ‖f x‖ ∂μ <= ∫ _ in sᶜ, C ∂μ :=
    integral_mono_ae hf1.norm.restrict (integrable_const C) (ae_restrict_of_ae hf)
  have h2 : ∫ _ in sᶜ, C ∂μ = μ.real sᶜ * C := by
    rw [setIntegral_const C]; rw [smul_eq_mul]
  rw [h0]; rw [← h2]
  exact le_trans (norm_integral_le_integral_norm f) h1

Depends on / 依赖: add_comm, ae_restrict_of_ae, hf1.norm.restrict, integrable_const, integral_add_compl, integral_mono_ae, le_trans, norm_integral_le_integral_norm, restrict, setIntegral_const, smul_eq_mul, sub_eq_iff_eq_add
-/
theorem norm_integral_sub_setIntegral_le [IsFiniteMeasure μ] {C : Real}
    (hf : forallᵐ (x : X) ∂μ, ‖f x‖ <= C) {s : Set X} (hs : MeasurableSet s) (hf1 : Integrable f μ) :
    ‖∫ (x : X), f x ∂μ - ∫ x in s, f x ∂μ‖ <= μ.real sᶜ * C := by
  have h0 : ∫ (x : X), f x ∂μ - ∫ x in s, f x ∂μ = ∫ x in sᶜ, f x ∂μ := by
    rw [sub_eq_iff_eq_add]; rw [add_comm]; rw [integral_add_compl hs hf1]
  have h1 : ∫ x in sᶜ, ‖f x‖ ∂μ <= ∫ _ in sᶜ, C ∂μ :=
    integral_mono_ae hf1.norm.restrict (integrable_const C) (ae_restrict_of_ae hf)
  have h2 : ∫ _ in sᶜ, C ∂μ = μ.real sᶜ * C := by
    rw [setIntegral_const C]; rw [smul_eq_mul]
  rw [h0]; rw [← h2]
  exact le_trans (norm_integral_le_integral_norm f) h1

/--
theorem `setIntegral_eq_zero_iff_of_nonneg_ae` / 定理 `setIntegral_eq_zero_iff_of_nonneg_ae`

English:
theorem setIntegral_eq_zero_iff_of_nonneg_ae
  statement: {f : X -> Real} (hf : 0 <=ᵐ[μ.restrict s] f)
  proof: integral_eq_zero_iff_of_nonneg_ae hf hfi

中文:
定理 set整数egral_eq_zero_iff_of_nonneg_ae
  结论: {f : X -> 实数} (hf : 0 <=ᵐ[μ.restrict s] f)
  证明: integral_eq_zero_iff_of_nonneg_ae hf hfi

Depends on / 依赖: integral_eq_zero_iff_of_nonneg_ae
-/
theorem setIntegral_eq_zero_iff_of_nonneg_ae {f : X -> Real} (hf : 0 <=ᵐ[μ.restrict s] f)
    (hfi : IntegrableOn f s μ) : ∫ x in s, f x ∂μ = 0 ↔ f =ᵐ[μ.restrict s] 0 :=
  integral_eq_zero_iff_of_nonneg_ae hf hfi

/--
theorem `setIntegral_pos_iff_support_of_nonneg_ae` / 定理 `setIntegral_pos_iff_support_of_nonneg_ae`

English:
theorem setIntegral_pos_iff_support_of_nonneg_ae
  statement: {f : X -> Real} (hf : 0 <=ᵐ[μ.restrict s] f)
  proof: by
  rw [integral_pos_iff_support_of_nonneg_ae hf hfi]; rw [Measure.restrict_apply₀]
  rw [support_eq_preimage]
  exact hfi.aestronglyMeasurable.aemeasurable.nullMeasurable (measurableSet_singleton 0).compl

中文:
定理 set整数egral_pos_iff_support_of_nonneg_ae
  结论: {f : X -> 实数} (hf : 0 <=ᵐ[μ.restrict s] f)
  证明: by
  rw [integral_pos_iff_support_of_nonneg_ae hf hfi]; rw [Measure.restrict_apply₀]
  rw [support_eq_preimage]
  exact hfi.aestronglyMeasurable.aemeasurable.nullMeasurable (measurableSet_singleton 0).compl

Depends on / 依赖: Measure, Measure.restrict_apply, aemeasurable, aestronglyMeasurable, hfi.aestronglyMeasurable.aemeasurable.nullMeasurable, integral_pos_iff_support_of_nonneg_ae, measurableSet_singleton, nullMeasurable, support_eq_preimage
-/
theorem setIntegral_pos_iff_support_of_nonneg_ae {f : X -> Real} (hf : 0 <=ᵐ[μ.restrict s] f)
    (hfi : IntegrableOn f s μ) : (0 < ∫ x in s, f x ∂μ) ↔ 0 < μ (support f inter s) := by
  rw [integral_pos_iff_support_of_nonneg_ae hf hfi]; rw [Measure.restrict_apply₀]
  rw [support_eq_preimage]
  exact hfi.aestronglyMeasurable.aemeasurable.nullMeasurable (measurableSet_singleton 0).compl

/--
theorem `setIntegral_gt_gt` / 定理 `setIntegral_gt_gt`

English:
theorem setIntegral_gt_gt
  statement: {R : Real} {f : X -> Real} (hR : 0 <= R)
  proof: by
  have : IntegrableOn (fun _ => R) {x | ↑R < f x} μ := by
    refine ⟨aestronglyMeasurable_const, lt_of_le_of_lt ?_ hfint.2⟩
refine setLIntegral_mono_ae hfint.1.enorm ae_of_all _ fun x hx => ?_
    simp only [ENNReal.coe_le_coe, Real.nnnorm_of_nonneg hR, enorm_eq_nnnorm,
      Real.nnnorm_of_nonneg (hR.trans <| le_of_lt hx)]
    exact le_of_lt hx
  rw [← sub_pos]; rw [← smul_eq_mul]; rw [← setIntegral_const]; rw [← integral_sub hfint this]; rw [setIntegral_pos_iff_support_of_nonneg_ae]
  · rw [← pos_iff_ne_zero] at hμ
    rwa [Set.inter_eq_self_of_subset_right]
    exact fun x hx => Ne.symm (ne_of_lt <| sub_pos.2 hx)
  · rw [Pi.zero_def, EventuallyLE, ae_restrict_iff₀]
· exact Eventually.of_forall fun x hx => sub_nonneg.2 le_of_lt hx
    · exact nullMeasurableSet_le aemeasurable_zero (hfint.1.aemeasurable.sub aemeasurable_const)
  · exact Integrable.sub hfint this

中文:
定理 set整数egral_gt_gt
  结论: {R : 实数} {f : X -> 实数} (hR : 0 <= R)
  证明: by
  have : IntegrableOn (fun _ => R) {x | ↑R < f x} μ := by
    refine ⟨aestronglyMeasurable_const, lt_of_le_of_lt ?_ hfint.2⟩
refine setLIntegral_mono_ae hfint.1.enorm ae_of_all _ fun x hx => ?_
    simp only [ENNReal.coe_le_coe, Real.nnnorm_of_nonneg hR, enorm_eq_nnnorm,
      Real.nnnorm_of_nonneg (hR.trans <| le_of_lt hx)]
    exact le_of_lt hx
  rw [← sub_pos]; rw [← smul_eq_mul]; rw [← setIntegral_const]; rw [← integral_sub hfint this]; rw [setIntegral_pos_iff_support_of_nonneg_ae]
  · rw [← pos_iff_ne_zero] at hμ
    rwa [Set.inter_eq_self_of_subset_right]
    exact fun x hx => Ne.symm (ne_of_lt <| sub_pos.2 hx)
  · rw [Pi.zero_def, EventuallyLE, ae_restrict_iff₀]
· exact Eventually.of_forall fun x hx => sub_nonneg.2 le_of_lt hx
    · exact nullMeasurableSet_le aemeasurable_zero (hfint.1.aemeasurable.sub aemeasurable_const)
  · exact Integrable.sub hfint this

Depends on / 依赖: ENNReal, ENNReal.coe_le_coe, IntegrableOn, Real.nnnorm_of_nonneg, ae_of_all, aestronglyMeasurable_const, coe_le_coe, enorm_eq_nnnorm, hR.trans, integral_sub, le_of_lt, lt_of_le_of_lt, nnnorm_of_nonneg, pos_iff_ne_zero, setIntegral_const, setIntegral_pos_iff_support_of_nonneg_ae, setLIntegral_mono_ae, smul_eq_mul, sub_pos
-/
theorem setIntegral_gt_gt {R : Real} {f : X -> Real} (hR : 0 <= R)
    (hfint : IntegrableOn f {x | ↑R < f x} μ) (hμ : μ {x | ↑R < f x} != 0) :
    μ.real {x | ↑R < f x} * R < ∫ x in {x | ↑R < f x}, f x ∂μ := by
  have : IntegrableOn (fun _ => R) {x | ↑R < f x} μ := by
    refine ⟨aestronglyMeasurable_const, lt_of_le_of_lt ?_ hfint.2⟩
refine setLIntegral_mono_ae hfint.1.enorm ae_of_all _ fun x hx => ?_
    simp only [ENNReal.coe_le_coe, Real.nnnorm_of_nonneg hR, enorm_eq_nnnorm,
      Real.nnnorm_of_nonneg (hR.trans <| le_of_lt hx)]
    exact le_of_lt hx
  rw [← sub_pos]; rw [← smul_eq_mul]; rw [← setIntegral_const]; rw [← integral_sub hfint this]; rw [setIntegral_pos_iff_support_of_nonneg_ae]
  · rw [← pos_iff_ne_zero] at hμ
    rwa [Set.inter_eq_self_of_subset_right]
    exact fun x hx => Ne.symm (ne_of_lt <| sub_pos.2 hx)
  · rw [Pi.zero_def, EventuallyLE, ae_restrict_iff₀]
· exact Eventually.of_forall fun x hx => sub_nonneg.2 le_of_lt hx
    · exact nullMeasurableSet_le aemeasurable_zero (hfint.1.aemeasurable.sub aemeasurable_const)
  · exact Integrable.sub hfint this

/--
theorem `setIntegral_trim` / 定理 `setIntegral_trim`

English:
theorem setIntegral_trim
  statement: {X} {m m0 : MeasurableSpace X} {μ : Measure X} (hm : m <= m0) {f : X -> E}
  proof: by
  rwa [integral_trim hm hf_meas, restrict_trim hm μ]

中文:
定理 set整数egral_trim
  结论: {X} {m m0 : 可测空间 X} {μ : 测度 X} (hm : m <= m0) {f : X -> E}
  证明: by
  rwa [integral_trim hm hf_meas, restrict_trim hm μ]

Depends on / 依赖: hf_meas, integral_trim, restrict_trim
-/
theorem setIntegral_trim {X} {m m0 : MeasurableSpace X} {μ : Measure X} (hm : m <= m0) {f : X -> E}
    (hf_meas : StronglyMeasurable[m] f) {s : Set X} (hs : MeasurableSet[m] s) :
    ∫ x in s, f x ∂μ = ∫ x in s, f x ∂μ.trim hm := by
  rwa [integral_trim hm hf_meas, restrict_trim hm μ]

/-! ### Lemmas about adding and removing interval boundaries

The primed lemmas take explicit arguments about the endpoint having zero measure, while the
unprimed ones use `[NullSingletonClass μ]`.
-/

section PartialOrder

variable [PartialOrder X] {x y : X}

/--
theorem `integral_Icc_eq_integral_Ioc'` / 定理 `integral_Icc_eq_integral_Ioc'`

English:
theorem integral_Icc_eq_integral_Ioc'
  given: (hx : μ {x} = 0)
  proof: setIntegral_congr_set (Ioc_ae_eq_Icc' hx).symm

中文:
定理 integral_Icc_eq_integral_Ioc'
  条件: (hx : μ {x} = 0)
  证明: setIntegral_congr_set (Ioc_ae_eq_Icc' hx).symm

Depends on / 依赖: Ioc_ae_eq_Icc, setIntegral_congr_set
-/
theorem integral_Icc_eq_integral_Ioc' (hx : μ {x} = 0) :
    ∫ t in Icc x y, f t ∂μ = ∫ t in Ioc x y, f t ∂μ :=
  setIntegral_congr_set (Ioc_ae_eq_Icc' hx).symm

/--
theorem `integral_Icc_eq_integral_Ico'` / 定理 `integral_Icc_eq_integral_Ico'`

English:
theorem integral_Icc_eq_integral_Ico'
  given: (hy : μ {y} = 0)
  proof: setIntegral_congr_set (Ico_ae_eq_Icc' hy).symm

中文:
定理 integral_Icc_eq_integral_Ico'
  条件: (hy : μ {y} = 0)
  证明: setIntegral_congr_set (Ico_ae_eq_Icc' hy).symm

Depends on / 依赖: Ico_ae_eq_Icc, setIntegral_congr_set
-/
theorem integral_Icc_eq_integral_Ico' (hy : μ {y} = 0) :
    ∫ t in Icc x y, f t ∂μ = ∫ t in Ico x y, f t ∂μ :=
  setIntegral_congr_set (Ico_ae_eq_Icc' hy).symm

/--
theorem `integral_Ioc_eq_integral_Ioo'` / 定理 `integral_Ioc_eq_integral_Ioo'`

English:
theorem integral_Ioc_eq_integral_Ioo'
  given: (hy : μ {y} = 0)
  proof: setIntegral_congr_set (Ioo_ae_eq_Ioc' hy).symm

中文:
定理 integral_Ioc_eq_integral_Ioo'
  条件: (hy : μ {y} = 0)
  证明: setIntegral_congr_set (Ioo_ae_eq_Ioc' hy).symm

Depends on / 依赖: Ioo_ae_eq_Ioc, setIntegral_congr_set
-/
theorem integral_Ioc_eq_integral_Ioo' (hy : μ {y} = 0) :
    ∫ t in Ioc x y, f t ∂μ = ∫ t in Ioo x y, f t ∂μ :=
  setIntegral_congr_set (Ioo_ae_eq_Ioc' hy).symm

/--
theorem `integral_Ico_eq_integral_Ioo'` / 定理 `integral_Ico_eq_integral_Ioo'`

English:
theorem integral_Ico_eq_integral_Ioo'
  given: (hx : μ {x} = 0)
  proof: setIntegral_congr_set (Ioo_ae_eq_Ico' hx).symm

中文:
定理 integral_Ico_eq_integral_Ioo'
  条件: (hx : μ {x} = 0)
  证明: setIntegral_congr_set (Ioo_ae_eq_Ico' hx).symm

Depends on / 依赖: Ioo_ae_eq_Ico, setIntegral_congr_set
-/
theorem integral_Ico_eq_integral_Ioo' (hx : μ {x} = 0) :
    ∫ t in Ico x y, f t ∂μ = ∫ t in Ioo x y, f t ∂μ :=
  setIntegral_congr_set (Ioo_ae_eq_Ico' hx).symm

/--
theorem `integral_Icc_eq_integral_Ioo'` / 定理 `integral_Icc_eq_integral_Ioo'`

English:
theorem integral_Icc_eq_integral_Ioo'
  given: (hx : μ {x} = 0) (hy : μ {y} = 0)
  proof: setIntegral_congr_set (Ioo_ae_eq_Icc' hx hy).symm

中文:
定理 integral_Icc_eq_integral_Ioo'
  条件: (hx : μ {x} = 0) (hy : μ {y} = 0)
  证明: setIntegral_congr_set (Ioo_ae_eq_Icc' hx hy).symm

Depends on / 依赖: Ioo_ae_eq_Icc, setIntegral_congr_set
-/
theorem integral_Icc_eq_integral_Ioo' (hx : μ {x} = 0) (hy : μ {y} = 0) :
    ∫ t in Icc x y, f t ∂μ = ∫ t in Ioo x y, f t ∂μ :=
  setIntegral_congr_set (Ioo_ae_eq_Icc' hx hy).symm

/--
theorem `integral_Iic_eq_integral_Iio'` / 定理 `integral_Iic_eq_integral_Iio'`

English:
theorem integral_Iic_eq_integral_Iio'
  given: (hx : μ {x} = 0)
  proof: setIntegral_congr_set (Iio_ae_eq_Iic' hx).symm

中文:
定理 integral_Iic_eq_integral_Iio'
  条件: (hx : μ {x} = 0)
  证明: setIntegral_congr_set (Iio_ae_eq_Iic' hx).symm

Depends on / 依赖: Iio_ae_eq_Iic, setIntegral_congr_set
-/
theorem integral_Iic_eq_integral_Iio' (hx : μ {x} = 0) :
    ∫ t in Iic x, f t ∂μ = ∫ t in Iio x, f t ∂μ :=
  setIntegral_congr_set (Iio_ae_eq_Iic' hx).symm

/--
theorem `integral_Ici_eq_integral_Ioi'` / 定理 `integral_Ici_eq_integral_Ioi'`

English:
theorem integral_Ici_eq_integral_Ioi'
  given: (hx : μ {x} = 0)
  proof: setIntegral_congr_set (Ioi_ae_eq_Ici' hx).symm

中文:
定理 integral_Ici_eq_integral_Ioi'
  条件: (hx : μ {x} = 0)
  证明: setIntegral_congr_set (Ioi_ae_eq_Ici' hx).symm

Depends on / 依赖: Ioi_ae_eq_Ici, setIntegral_congr_set
-/
theorem integral_Ici_eq_integral_Ioi' (hx : μ {x} = 0) :
    ∫ t in Ici x, f t ∂μ = ∫ t in Ioi x, f t ∂μ :=
  setIntegral_congr_set (Ioi_ae_eq_Ici' hx).symm

variable [NullSingletonClass μ]

/--
theorem `integral_Icc_eq_integral_Ioc` / 定理 `integral_Icc_eq_integral_Ioc`

English:
theorem integral_Icc_eq_integral_Ioc
  statement: ∫ t in Icc x y, f t ∂μ = ∫ t in Ioc x y, f t ∂μ
  proof: integral_Icc_eq_integral_Ioc' measure_singleton x

中文:
定理 integral_Icc_eq_integral_Ioc
  结论: ∫ t in 闭区间 x y, f t ∂μ = ∫ t in 左开右闭区间 x y, f t ∂μ
  证明: integral_Icc_eq_integral_Ioc' measure_singleton x

Depends on / 依赖: integral_Icc_eq_integral_Ioc, measure_singleton
-/
theorem integral_Icc_eq_integral_Ioc : ∫ t in Icc x y, f t ∂μ = ∫ t in Ioc x y, f t ∂μ :=
integral_Icc_eq_integral_Ioc' measure_singleton x

/--
theorem `integral_Icc_eq_integral_Ico` / 定理 `integral_Icc_eq_integral_Ico`

English:
theorem integral_Icc_eq_integral_Ico
  statement: ∫ t in Icc x y, f t ∂μ = ∫ t in Ico x y, f t ∂μ
  proof: integral_Icc_eq_integral_Ico' measure_singleton y

中文:
定理 integral_Icc_eq_integral_Ico
  结论: ∫ t in 闭区间 x y, f t ∂μ = ∫ t in 左闭右开区间 x y, f t ∂μ
  证明: integral_Icc_eq_integral_Ico' measure_singleton y

Depends on / 依赖: integral_Icc_eq_integral_Ico, measure_singleton
-/
theorem integral_Icc_eq_integral_Ico : ∫ t in Icc x y, f t ∂μ = ∫ t in Ico x y, f t ∂μ :=
integral_Icc_eq_integral_Ico' measure_singleton y

/--
theorem `integral_Ioc_eq_integral_Ioo` / 定理 `integral_Ioc_eq_integral_Ioo`

English:
theorem integral_Ioc_eq_integral_Ioo
  statement: ∫ t in Ioc x y, f t ∂μ = ∫ t in Ioo x y, f t ∂μ
  proof: integral_Ioc_eq_integral_Ioo' measure_singleton y

中文:
定理 integral_Ioc_eq_integral_Ioo
  结论: ∫ t in 左开右闭区间 x y, f t ∂μ = ∫ t in 开区间 x y, f t ∂μ
  证明: integral_Ioc_eq_integral_Ioo' measure_singleton y

Depends on / 依赖: integral_Ioc_eq_integral_Ioo, measure_singleton
-/
theorem integral_Ioc_eq_integral_Ioo : ∫ t in Ioc x y, f t ∂μ = ∫ t in Ioo x y, f t ∂μ :=
integral_Ioc_eq_integral_Ioo' measure_singleton y

/--
theorem `integral_Ico_eq_integral_Ioo` / 定理 `integral_Ico_eq_integral_Ioo`

English:
theorem integral_Ico_eq_integral_Ioo
  statement: ∫ t in Ico x y, f t ∂μ = ∫ t in Ioo x y, f t ∂μ
  proof: integral_Ico_eq_integral_Ioo' measure_singleton x

中文:
定理 integral_Ico_eq_integral_Ioo
  结论: ∫ t in 左闭右开区间 x y, f t ∂μ = ∫ t in 开区间 x y, f t ∂μ
  证明: integral_Ico_eq_integral_Ioo' measure_singleton x

Depends on / 依赖: integral_Ico_eq_integral_Ioo, measure_singleton
-/
theorem integral_Ico_eq_integral_Ioo : ∫ t in Ico x y, f t ∂μ = ∫ t in Ioo x y, f t ∂μ :=
integral_Ico_eq_integral_Ioo' measure_singleton x

/--
theorem `integral_Ico_eq_integral_Ioc` / 定理 `integral_Ico_eq_integral_Ioc`

English:
theorem integral_Ico_eq_integral_Ioc
  statement: ∫ t in Ico x y, f t ∂μ = ∫ t in Ioc x y, f t ∂μ
  proof: by
  rw [integral_Ico_eq_integral_Ioo]; rw [integral_Ioc_eq_integral_Ioo]

中文:
定理 integral_Ico_eq_integral_Ioc
  结论: ∫ t in 左闭右开区间 x y, f t ∂μ = ∫ t in 左开右闭区间 x y, f t ∂μ
  证明: by
  rw [integral_Ico_eq_integral_Ioo]; rw [integral_Ioc_eq_integral_Ioo]

Depends on / 依赖: integral_Ico_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo
-/
theorem integral_Ico_eq_integral_Ioc : ∫ t in Ico x y, f t ∂μ = ∫ t in Ioc x y, f t ∂μ := by
  rw [integral_Ico_eq_integral_Ioo]; rw [integral_Ioc_eq_integral_Ioo]

/--
theorem `integral_Icc_eq_integral_Ioo` / 定理 `integral_Icc_eq_integral_Ioo`

English:
theorem integral_Icc_eq_integral_Ioo
  statement: ∫ t in Icc x y, f t ∂μ = ∫ t in Ioo x y, f t ∂μ
  proof: by
  rw [integral_Icc_eq_integral_Ico]; rw [integral_Ico_eq_integral_Ioo]

中文:
定理 integral_Icc_eq_integral_Ioo
  结论: ∫ t in 闭区间 x y, f t ∂μ = ∫ t in 开区间 x y, f t ∂μ
  证明: by
  rw [integral_Icc_eq_integral_Ico]; rw [integral_Ico_eq_integral_Ioo]

Depends on / 依赖: integral_Icc_eq_integral_Ico, integral_Ico_eq_integral_Ioo
-/
theorem integral_Icc_eq_integral_Ioo : ∫ t in Icc x y, f t ∂μ = ∫ t in Ioo x y, f t ∂μ := by
  rw [integral_Icc_eq_integral_Ico]; rw [integral_Ico_eq_integral_Ioo]

/--
theorem `integral_Iic_eq_integral_Iio` / 定理 `integral_Iic_eq_integral_Iio`

English:
theorem integral_Iic_eq_integral_Iio
  statement: ∫ t in Iic x, f t ∂μ = ∫ t in Iio x, f t ∂μ
  proof: integral_Iic_eq_integral_Iio' measure_singleton x

中文:
定理 integral_Iic_eq_integral_Iio
  结论: ∫ t in 左无界右闭区间 x, f t ∂μ = ∫ t in 左无界右开区间 x, f t ∂μ
  证明: integral_Iic_eq_integral_Iio' measure_singleton x

Depends on / 依赖: integral_Iic_eq_integral_Iio, measure_singleton
-/
theorem integral_Iic_eq_integral_Iio : ∫ t in Iic x, f t ∂μ = ∫ t in Iio x, f t ∂μ :=
integral_Iic_eq_integral_Iio' measure_singleton x

/--
theorem `integral_Ici_eq_integral_Ioi` / 定理 `integral_Ici_eq_integral_Ioi`

English:
theorem integral_Ici_eq_integral_Ioi
  statement: ∫ t in Ici x, f t ∂μ = ∫ t in Ioi x, f t ∂μ
  proof: integral_Ici_eq_integral_Ioi' measure_singleton x

中文:
定理 integral_Ici_eq_integral_Ioi
  结论: ∫ t in 左闭右无界区间 x, f t ∂μ = ∫ t in 左开右无界区间 x, f t ∂μ
  证明: integral_Ici_eq_integral_Ioi' measure_singleton x

Depends on / 依赖: integral_Ici_eq_integral_Ioi, measure_singleton
-/
theorem integral_Ici_eq_integral_Ioi : ∫ t in Ici x, f t ∂μ = ∫ t in Ioi x, f t ∂μ :=
integral_Ici_eq_integral_Ioi' measure_singleton x

end PartialOrder

end NormedAddCommGroup

section Mono

variable [NormedAddCommGroup E] [NormedSpace Real E] [PartialOrder E]
    [IsOrderedAddMonoid E] [IsOrderedModule Real E]
    {μ : Measure X} {f g : X -> E} {s t : Set X}

/--
theorem `setIntegral_mono_set` / 定理 `setIntegral_mono_set`

English:
theorem setIntegral_mono_set
  statement: [OrderClosedTopology E] (hfi : IntegrableOn f t μ)
  proof: integral_mono_measure (Measure.restrict_mono_ae hst) hf hfi

中文:
定理 set整数egral_mono_set
  结论: [OrderClosed拓扑 E] (hfi : 整数egrableOn f t μ)
  证明: integral_mono_measure (Measure.restrict_mono_ae hst) hf hfi

Depends on / 依赖: Measure, Measure.restrict_mono_ae, integral_mono_measure, restrict_mono_ae
-/
theorem setIntegral_mono_set [OrderClosedTopology E] (hfi : IntegrableOn f t μ)
    (hf : 0 <=ᵐ[μ.restrict t] f) (hst : s <=ᵐ[μ] t) :
    ∫ x in s, f x ∂μ <= ∫ x in t, f x ∂μ :=
  integral_mono_measure (Measure.restrict_mono_ae hst) hf hfi

/--
theorem `setIntegral_le_integral` / 定理 `setIntegral_le_integral`

English:
theorem setIntegral_le_integral
  given: [OrderClosedTopology E] (hfi : Integrable f μ) (hf : 0 <=ᵐ[μ] f)
  proof: integral_mono_measure (Measure.restrict_le_self) hf hfi

中文:
定理 set整数egral_le_integral
  条件: [OrderClosed拓扑 E] (hfi : 可积 f μ) (hf : 0 <=ᵐ[μ] f)
  证明: integral_mono_measure (Measure.restrict_le_self) hf hfi

Depends on / 依赖: Measure, Measure.restrict_le_self, integral_mono_measure, restrict_le_self
-/
theorem setIntegral_le_integral [OrderClosedTopology E] (hfi : Integrable f μ) (hf : 0 <=ᵐ[μ] f) :
    ∫ x in s, f x ∂μ <= ∫ x, f x ∂μ :=
  integral_mono_measure (Measure.restrict_le_self) hf hfi

variable [ClosedIciTopology E]

section
variable (hf : IntegrableOn f s μ) (hg : IntegrableOn g s μ)
include hf hg

/--
theorem `setIntegral_mono_ae_restrict` / 定理 `setIntegral_mono_ae_restrict`

English:
theorem setIntegral_mono_ae_restrict
  given: (h : f <=ᵐ[μ.restrict s] g)
  proof: by
  by_cases hE : CompleteSpace E
  · exact integral_mono_ae hf hg h
  · simp [integral, hE]

中文:
定理 set整数egral_mono_ae_restrict
  条件: (h : f <=ᵐ[μ.restrict s] g)
  证明: by
  by_cases hE : CompleteSpace E
  · exact integral_mono_ae hf hg h
  · simp [integral, hE]

Depends on / 依赖: CompleteSpace, integral, integral_mono_ae
-/
theorem setIntegral_mono_ae_restrict (h : f <=ᵐ[μ.restrict s] g) :
    ∫ x in s, f x ∂μ <= ∫ x in s, g x ∂μ := by
  by_cases hE : CompleteSpace E
  · exact integral_mono_ae hf hg h
  · simp [integral, hE]

/--
theorem `setIntegral_mono_ae` / 定理 `setIntegral_mono_ae`

English:
theorem setIntegral_mono_ae
  given: (h : f <=ᵐ[μ] g)
  statement: ∫ x in s, f x ∂μ <= ∫ x in s, g x ∂μ
  proof: setIntegral_mono_ae_restrict hf hg (ae_restrict_of_ae h)

中文:
定理 set整数egral_mono_ae
  条件: (h : f <=ᵐ[μ] g)
  结论: ∫ x in s, f x ∂μ <= ∫ x in s, g x ∂μ
  证明: setIntegral_mono_ae_restrict hf hg (ae_restrict_of_ae h)

Depends on / 依赖: ae_restrict_of_ae, setIntegral_mono_ae_restrict
-/
theorem setIntegral_mono_ae (h : f <=ᵐ[μ] g) : ∫ x in s, f x ∂μ <= ∫ x in s, g x ∂μ :=
  setIntegral_mono_ae_restrict hf hg (ae_restrict_of_ae h)

/--
theorem `setIntegral_mono_on` / 定理 `setIntegral_mono_on`

English:
theorem setIntegral_mono_on
  given: (hs : MeasurableSet s) (h : forall x in s, f x <= g x)
  proof: setIntegral_mono_ae_restrict hf hg
    (by simp [hs, EventuallyLE, eventually_inf_principal, ae_of_all _ h])

中文:
定理 set整数egral_mono_on
  条件: (hs : 可测集 s) (h : 对任意 x in s, f x <= g x)
  证明: setIntegral_mono_ae_restrict hf hg
    (by simp [hs, EventuallyLE, eventually_inf_principal, ae_of_all _ h])

Depends on / 依赖: EventuallyLE, ae_of_all, eventually_inf_principal, setIntegral_mono_ae_restrict
-/
theorem setIntegral_mono_on (hs : MeasurableSet s) (h : forall x in s, f x <= g x) :
    ∫ x in s, f x ∂μ <= ∫ x in s, g x ∂μ :=
  setIntegral_mono_ae_restrict hf hg
    (by simp [hs, EventuallyLE, eventually_inf_principal, ae_of_all _ h])

/--
theorem `setIntegral_mono_on_ae` / 定理 `setIntegral_mono_on_ae`

English:
theorem setIntegral_mono_on_ae
  given: (hs : MeasurableSet s) (h : forallᵐ x ∂μ, x in s -> f x <= g x)
  proof: by
  refine setIntegral_mono_ae_restrict hf hg ?_; rwa [EventuallyLE, ae_restrict_iff' hs]

中文:
定理 set整数egral_mono_on_ae
  条件: (hs : 可测集 s) (h : 对任意ᵐ x ∂μ, x in s -> f x <= g x)
  证明: by
  refine setIntegral_mono_ae_restrict hf hg ?_; rwa [EventuallyLE, ae_restrict_iff' hs]

Depends on / 依赖: EventuallyLE, ae_restrict_iff, setIntegral_mono_ae_restrict
-/
theorem setIntegral_mono_on_ae (hs : MeasurableSet s) (h : forallᵐ x ∂μ, x in s -> f x <= g x) :
    ∫ x in s, f x ∂μ <= ∫ x in s, g x ∂μ := by
  refine setIntegral_mono_ae_restrict hf hg ?_; rwa [EventuallyLE, ae_restrict_iff' hs]

/--
lemma `setIntegral_mono_on_ae₀` / 引理 `setIntegral_mono_on_ae₀`

English:
lemma setIntegral_mono_on_ae₀
  given: (hs : NullMeasurableSet s μ) (h : forallᵐ x ∂μ, x in s -> f x <= g x)
  proof: by
  rw [setIntegral_congr_set hs.toMeasurable_ae_eq.symm]; rw [setIntegral_congr_set hs.toMeasurable_ae_eq.symm]
  refine setIntegral_mono_on_ae ?_ ?_ ?_ ?_
  · rwa [integrableOn_congr_set_ae hs.toMeasurable_ae_eq]
  · rwa [integrableOn_congr_set_ae hs.toMeasurable_ae_eq]
  · exact measurableSet_toMeasurable μ s
  · filter_upwards [hs.toMeasurable_ae_eq.mem_iff, h] with x hx h
    rwa [hx]

@[gcongr high] -- higher priority than `integral_mono`

中文:
引理 set整数egral_mono_on_ae₀
  条件: (hs : NullMeasurableSet s μ) (h : 对任意ᵐ x ∂μ, x in s -> f x <= g x)
  证明: by
  rw [setIntegral_congr_set hs.toMeasurable_ae_eq.symm]; rw [setIntegral_congr_set hs.toMeasurable_ae_eq.symm]
  refine setIntegral_mono_on_ae ?_ ?_ ?_ ?_
  · rwa [integrableOn_congr_set_ae hs.toMeasurable_ae_eq]
  · rwa [integrableOn_congr_set_ae hs.toMeasurable_ae_eq]
  · exact measurableSet_toMeasurable μ s
  · filter_upwards [hs.toMeasurable_ae_eq.mem_iff, h] with x hx h
    rwa [hx]

@[gcongr high] -- higher priority than `integral_mono`

Depends on / 依赖: filter_upwards, hs.toMeasurable_ae_eq, hs.toMeasurable_ae_eq.mem_iff, hs.toMeasurable_ae_eq.symm, integrableOn_congr_set_ae, measurableSet_toMeasurable, mem_iff, setIntegral_congr_set, setIntegral_mono_on_ae, toMeasurable_ae_eq
-/
lemma setIntegral_mono_on_ae₀ (hs : NullMeasurableSet s μ) (h : forallᵐ x ∂μ, x in s -> f x <= g x) :
    ∫ x in s, f x ∂μ <= ∫ x in s, g x ∂μ := by
  rw [setIntegral_congr_set hs.toMeasurable_ae_eq.symm]; rw [setIntegral_congr_set hs.toMeasurable_ae_eq.symm]
  refine setIntegral_mono_on_ae ?_ ?_ ?_ ?_
  · rwa [integrableOn_congr_set_ae hs.toMeasurable_ae_eq]
  · rwa [integrableOn_congr_set_ae hs.toMeasurable_ae_eq]
  · exact measurableSet_toMeasurable μ s
  · filter_upwards [hs.toMeasurable_ae_eq.mem_iff, h] with x hx h
    rwa [hx]

@[gcongr high] -- higher priority than `integral_mono`
-- this lemma is better because it also gives the `x ∈ s` hypothesis
/--
lemma `setIntegral_mono_on₀` / 引理 `setIntegral_mono_on₀`

English:
lemma setIntegral_mono_on₀
  given: (hs : NullMeasurableSet s μ) (h : forall x in s, f x <= g x)
  proof: setIntegral_mono_on_ae₀ hf hg hs (Eventually.of_forall h)

中文:
引理 set整数egral_mono_on₀
  条件: (hs : NullMeasurableSet s μ) (h : 对任意 x in s, f x <= g x)
  证明: setIntegral_mono_on_ae₀ hf hg hs (Eventually.of_forall h)

Depends on / 依赖: Eventually, Eventually.of_forall, of_forall
-/
lemma setIntegral_mono_on₀ (hs : NullMeasurableSet s μ) (h : forall x in s, f x <= g x) :
    ∫ x in s, f x ∂μ <= ∫ x in s, g x ∂μ :=
  setIntegral_mono_on_ae₀ hf hg hs (Eventually.of_forall h)

/--
theorem `setIntegral_mono` / 定理 `setIntegral_mono`

English:
theorem setIntegral_mono
  given: (h : f <= g)
  statement: ∫ x in s, f x ∂μ <= ∫ x in s, g x ∂μ
  proof: integral_mono hf hg h

中文:
定理 set整数egral_mono
  条件: (h : f <= g)
  结论: ∫ x in s, f x ∂μ <= ∫ x in s, g x ∂μ
  证明: integral_mono hf hg h

Depends on / 依赖: integral_mono
-/
theorem setIntegral_mono (h : f <= g) : ∫ x in s, f x ∂μ <= ∫ x in s, g x ∂μ :=
  integral_mono hf hg h

end

/--
theorem `setIntegral_ge_of_const_le` / 定理 `setIntegral_ge_of_const_le`

English:
theorem setIntegral_ge_of_const_le
  statement: [CompleteSpace E] {c : E} (hs : MeasurableSet s) (hμs : μ s != ∞)
  proof: by
  rw [← setIntegral_const c]
  exact setIntegral_mono_on (integrableOn_const hμs) hfint hs hf

中文:
定理 set整数egral_ge_of_const_le
  结论: [完备空间 E] {c : E} (hs : 可测集 s) (hμs : μ s != ∞)
  证明: by
  rw [← setIntegral_const c]
  exact setIntegral_mono_on (integrableOn_const hμs) hfint hs hf

Depends on / 依赖: integrableOn_const, setIntegral_const, setIntegral_mono_on
-/
theorem setIntegral_ge_of_const_le [CompleteSpace E] {c : E} (hs : MeasurableSet s) (hμs : μ s != ∞)
    (hf : forall x in s, c <= f x) (hfint : IntegrableOn (fun x : X => f x) s μ) :
    μ.real s • c <= ∫ x in s, f x ∂μ := by
  rw [← setIntegral_const c]
  exact setIntegral_mono_on (integrableOn_const hμs) hfint hs hf

/--
theorem `setIntegral_ge_of_const_le_real` / 定理 `setIntegral_ge_of_const_le_real`

English:
theorem setIntegral_ge_of_const_le_real
  statement: {f : X -> Real} {c : Real} (hs : MeasurableSet s) (hμs : μ s != ∞)
  proof: by
  simpa [mul_comm] using setIntegral_ge_of_const_le hs hμs hf hfint

中文:
定理 set整数egral_ge_of_const_le_real
  结论: {f : X -> 实数} {c : 实数} (hs : 可测集 s) (hμs : μ s != ∞)
  证明: by
  simpa [mul_comm] using setIntegral_ge_of_const_le hs hμs hf hfint

Depends on / 依赖: mul_comm, setIntegral_ge_of_const_le
-/
theorem setIntegral_ge_of_const_le_real {f : X -> Real} {c : Real} (hs : MeasurableSet s) (hμs : μ s != ∞)
    (hf : forall x in s, c <= f x) (hfint : IntegrableOn (fun x : X => f x) s μ) :
    c * μ.real s <= ∫ x in s, f x ∂μ := by
  simpa [mul_comm] using setIntegral_ge_of_const_le hs hμs hf hfint

end Mono

section Nonneg

variable {μ : Measure X} {f : X -> Real} {s : Set X}

/--
theorem `setIntegral_nonneg_of_ae_restrict` / 定理 `setIntegral_nonneg_of_ae_restrict`

English:
theorem setIntegral_nonneg_of_ae_restrict
  given: (hf : 0 <=ᵐ[μ.restrict s] f)
  statement: 0 <= ∫ x in s, f x ∂μ
  proof: integral_nonneg_of_ae hf

中文:
定理 set整数egral_nonneg_of_ae_restrict
  条件: (hf : 0 <=ᵐ[μ.restrict s] f)
  结论: 0 <= ∫ x in s, f x ∂μ
  证明: integral_nonneg_of_ae hf

Depends on / 依赖: integral_nonneg_of_ae
-/
theorem setIntegral_nonneg_of_ae_restrict (hf : 0 <=ᵐ[μ.restrict s] f) : 0 <= ∫ x in s, f x ∂μ :=
  integral_nonneg_of_ae hf

/--
theorem `setIntegral_nonneg_of_ae` / 定理 `setIntegral_nonneg_of_ae`

English:
theorem setIntegral_nonneg_of_ae
  given: (hf : 0 <=ᵐ[μ] f)
  statement: 0 <= ∫ x in s, f x ∂μ
  proof: setIntegral_nonneg_of_ae_restrict (ae_restrict_of_ae hf)

中文:
定理 set整数egral_nonneg_of_ae
  条件: (hf : 0 <=ᵐ[μ] f)
  结论: 0 <= ∫ x in s, f x ∂μ
  证明: setIntegral_nonneg_of_ae_restrict (ae_restrict_of_ae hf)

Depends on / 依赖: ae_restrict_of_ae, setIntegral_nonneg_of_ae_restrict
-/
theorem setIntegral_nonneg_of_ae (hf : 0 <=ᵐ[μ] f) : 0 <= ∫ x in s, f x ∂μ :=
  setIntegral_nonneg_of_ae_restrict (ae_restrict_of_ae hf)

/--
theorem `setIntegral_nonneg` / 定理 `setIntegral_nonneg`

English:
theorem setIntegral_nonneg
  given: (hs : MeasurableSet s) (hf : forall x, x in s -> 0 <= f x)
  proof: setIntegral_nonneg_of_ae_restrict ((ae_restrict_iff' hs).mpr (ae_of_all μ hf))

中文:
定理 set整数egral_nonneg
  条件: (hs : 可测集 s) (hf : 对任意 x, x in s -> 0 <= f x)
  证明: setIntegral_nonneg_of_ae_restrict ((ae_restrict_iff' hs).mpr (ae_of_all μ hf))

Depends on / 依赖: ae_of_all, ae_restrict_iff, setIntegral_nonneg_of_ae_restrict
-/
theorem setIntegral_nonneg (hs : MeasurableSet s) (hf : forall x, x in s -> 0 <= f x) :
    0 <= ∫ x in s, f x ∂μ :=
  setIntegral_nonneg_of_ae_restrict ((ae_restrict_iff' hs).mpr (ae_of_all μ hf))

/--
theorem `setIntegral_nonneg_ae` / 定理 `setIntegral_nonneg_ae`

English:
theorem setIntegral_nonneg_ae
  given: (hs : MeasurableSet s) (hf : forallᵐ x ∂μ, x in s -> 0 <= f x)
  proof: setIntegral_nonneg_of_ae_restrict by rwa [EventuallyLE, ae_restrict_iff' hs]

中文:
定理 set整数egral_nonneg_ae
  条件: (hs : 可测集 s) (hf : 对任意ᵐ x ∂μ, x in s -> 0 <= f x)
  证明: setIntegral_nonneg_of_ae_restrict by rwa [EventuallyLE, ae_restrict_iff' hs]

Depends on / 依赖: EventuallyLE, ae_restrict_iff, setIntegral_nonneg_of_ae_restrict
-/
theorem setIntegral_nonneg_ae (hs : MeasurableSet s) (hf : forallᵐ x ∂μ, x in s -> 0 <= f x) :
    0 <= ∫ x in s, f x ∂μ :=
setIntegral_nonneg_of_ae_restrict by rwa [EventuallyLE, ae_restrict_iff' hs]

/--
theorem `setIntegral_le_nonneg` / 定理 `setIntegral_le_nonneg`

English:
theorem setIntegral_le_nonneg
  statement: {s : Set X} (hs : MeasurableSet s) (hf : StronglyMeasurable f)
  proof: by
  rw [← integral_indicator hs]; rw [←
    integral_indicator (stronglyMeasurable_const.measurableSet_le hf)]
  exact
    integral_mono (hfi.indicator hs)
      (hfi.indicator (stronglyMeasurable_const.measurableSet_le hf))
      (indicator_le_indicator_nonneg s f)

中文:
定理 set整数egral_le_nonneg
  结论: {s : 集合 X} (hs : 可测集 s) (hf : StronglyMeasurable f)
  证明: by
  rw [← integral_indicator hs]; rw [←
    integral_indicator (stronglyMeasurable_const.measurableSet_le hf)]
  exact
    integral_mono (hfi.indicator hs)
      (hfi.indicator (stronglyMeasurable_const.measurableSet_le hf))
      (indicator_le_indicator_nonneg s f)

Depends on / 依赖: hfi.indicator, indicator, indicator_le_indicator_nonneg, integral_indicator, integral_mono, measurableSet_le, stronglyMeasurable_const, stronglyMeasurable_const.measurableSet_le
-/
theorem setIntegral_le_nonneg {s : Set X} (hs : MeasurableSet s) (hf : StronglyMeasurable f)
    (hfi : Integrable f μ) : ∫ x in s, f x ∂μ <= ∫ x in {y | 0 <= f y}, f x ∂μ := by
  rw [← integral_indicator hs]; rw [←
    integral_indicator (stronglyMeasurable_const.measurableSet_le hf)]
  exact
    integral_mono (hfi.indicator hs)
      (hfi.indicator (stronglyMeasurable_const.measurableSet_le hf))
      (indicator_le_indicator_nonneg s f)

/--
theorem `setIntegral_nonpos_of_ae_restrict` / 定理 `setIntegral_nonpos_of_ae_restrict`

English:
theorem setIntegral_nonpos_of_ae_restrict
  given: (hf : f <=ᵐ[μ.restrict s] 0)
  statement: ∫ x in s, f x ∂μ <= 0
  proof: integral_nonpos_of_ae hf

中文:
定理 set整数egral_nonpos_of_ae_restrict
  条件: (hf : f <=ᵐ[μ.restrict s] 0)
  结论: ∫ x in s, f x ∂μ <= 0
  证明: integral_nonpos_of_ae hf

Depends on / 依赖: integral_nonpos_of_ae
-/
theorem setIntegral_nonpos_of_ae_restrict (hf : f <=ᵐ[μ.restrict s] 0) : ∫ x in s, f x ∂μ <= 0 :=
  integral_nonpos_of_ae hf

/--
theorem `setIntegral_nonpos_of_ae` / 定理 `setIntegral_nonpos_of_ae`

English:
theorem setIntegral_nonpos_of_ae
  given: (hf : f <=ᵐ[μ] 0)
  statement: ∫ x in s, f x ∂μ <= 0
  proof: setIntegral_nonpos_of_ae_restrict (ae_restrict_of_ae hf)

中文:
定理 set整数egral_nonpos_of_ae
  条件: (hf : f <=ᵐ[μ] 0)
  结论: ∫ x in s, f x ∂μ <= 0
  证明: setIntegral_nonpos_of_ae_restrict (ae_restrict_of_ae hf)

Depends on / 依赖: ae_restrict_of_ae, setIntegral_nonpos_of_ae_restrict
-/
theorem setIntegral_nonpos_of_ae (hf : f <=ᵐ[μ] 0) : ∫ x in s, f x ∂μ <= 0 :=
  setIntegral_nonpos_of_ae_restrict (ae_restrict_of_ae hf)

/--
theorem `setIntegral_nonpos_ae` / 定理 `setIntegral_nonpos_ae`

English:
theorem setIntegral_nonpos_ae
  given: (hs : MeasurableSet s) (hf : forallᵐ x ∂μ, x in s -> f x <= 0)
  proof: setIntegral_nonpos_of_ae_restrict by rwa [EventuallyLE, ae_restrict_iff' hs]

中文:
定理 set整数egral_nonpos_ae
  条件: (hs : 可测集 s) (hf : 对任意ᵐ x ∂μ, x in s -> f x <= 0)
  证明: setIntegral_nonpos_of_ae_restrict by rwa [EventuallyLE, ae_restrict_iff' hs]

Depends on / 依赖: EventuallyLE, ae_restrict_iff, setIntegral_nonpos_of_ae_restrict
-/
theorem setIntegral_nonpos_ae (hs : MeasurableSet s) (hf : forallᵐ x ∂μ, x in s -> f x <= 0) :
    ∫ x in s, f x ∂μ <= 0 :=
setIntegral_nonpos_of_ae_restrict by rwa [EventuallyLE, ae_restrict_iff' hs]

/--
theorem `setIntegral_nonpos` / 定理 `setIntegral_nonpos`

English:
theorem setIntegral_nonpos
  given: (hs : MeasurableSet s) (hf : forall x, x in s -> f x <= 0)
  proof: setIntegral_nonpos_ae hs ae_of_all μ hf

中文:
定理 set整数egral_nonpos
  条件: (hs : 可测集 s) (hf : 对任意 x, x in s -> f x <= 0)
  证明: setIntegral_nonpos_ae hs ae_of_all μ hf

Depends on / 依赖: ae_of_all, setIntegral_nonpos_ae
-/
theorem setIntegral_nonpos (hs : MeasurableSet s) (hf : forall x, x in s -> f x <= 0) :
    ∫ x in s, f x ∂μ <= 0 :=
setIntegral_nonpos_ae hs ae_of_all μ hf

/--
theorem `setIntegral_nonpos_le` / 定理 `setIntegral_nonpos_le`

English:
theorem setIntegral_nonpos_le
  statement: {s : Set X} (hs : MeasurableSet s) (hf : StronglyMeasurable f)
  proof: by
  rw [← integral_indicator hs]; rw [←
    integral_indicator (hf.measurableSet_le stronglyMeasurable_const)]
  exact
    integral_mono (hfi.indicator (hf.measurableSet_le stronglyMeasurable_const))
      (hfi.indicator hs) (indicator_nonpos_le_indicator s f)

中文:
定理 set整数egral_nonpos_le
  结论: {s : 集合 X} (hs : 可测集 s) (hf : StronglyMeasurable f)
  证明: by
  rw [← integral_indicator hs]; rw [←
    integral_indicator (hf.measurableSet_le stronglyMeasurable_const)]
  exact
    integral_mono (hfi.indicator (hf.measurableSet_le stronglyMeasurable_const))
      (hfi.indicator hs) (indicator_nonpos_le_indicator s f)

Depends on / 依赖: hf.measurableSet_le, hfi.indicator, indicator, indicator_nonpos_le_indicator, integral_indicator, integral_mono, measurableSet_le, stronglyMeasurable_const
-/
theorem setIntegral_nonpos_le {s : Set X} (hs : MeasurableSet s) (hf : StronglyMeasurable f)
    (hfi : Integrable f μ) : ∫ x in {y | f y <= 0}, f x ∂μ <= ∫ x in s, f x ∂μ := by
  rw [← integral_indicator hs]; rw [←
    integral_indicator (hf.measurableSet_le stronglyMeasurable_const)]
  exact
    integral_mono (hfi.indicator (hf.measurableSet_le stronglyMeasurable_const))
      (hfi.indicator hs) (indicator_nonpos_le_indicator s f)

/--
lemma `Integrable.measure_le_integral` / 引理 `Integrable.measure_le_integral`

English:
lemma Integrable.measure_le_integral
  statement: {f : X -> Real} (f_int : Integrable f μ) (f_nonneg : 0 <=ᵐ[μ] f)
  proof: by
  rw [ofReal_integral_eq_lintegral_ofReal f_int f_nonneg]
  apply meas_le_lintegral₀
  · exact ENNReal.continuous_ofReal.measurable.comp_aemeasurable f_int.1.aemeasurable
  · intro x hx
    simpa using ENNReal.ofReal_le_ofReal (hs x hx)

中文:
引理 可积.measure_le_integral
  结论: {f : X -> 实数} (f_int : 可积 f μ) (f_nonneg : 0 <=ᵐ[μ] f)
  证明: by
  rw [ofReal_integral_eq_lintegral_ofReal f_int f_nonneg]
  apply meas_le_lintegral₀
  · exact ENNReal.continuous_ofReal.measurable.comp_aemeasurable f_int.1.aemeasurable
  · intro x hx
    simpa using ENNReal.ofReal_le_ofReal (hs x hx)

Depends on / 依赖: ENNReal, ENNReal.continuous_ofReal.measurable.comp_aemeasurable, ENNReal.ofReal_le_ofReal, aemeasurable, comp_aemeasurable, continuous_ofReal, f_int, f_nonneg, measurable, ofReal_integral_eq_lintegral_ofReal, ofReal_le_ofReal
-/
lemma Integrable.measure_le_integral {f : X -> Real} (f_int : Integrable f μ) (f_nonneg : 0 <=ᵐ[μ] f)
    {s : Set X} (hs : forall x in s, 1 <= f x) :
    μ s <= ENNReal.ofReal (∫ x, f x ∂μ) := by
  rw [ofReal_integral_eq_lintegral_ofReal f_int f_nonneg]
  apply meas_le_lintegral₀
  · exact ENNReal.continuous_ofReal.measurable.comp_aemeasurable f_int.1.aemeasurable
  · intro x hx
    simpa using ENNReal.ofReal_le_ofReal (hs x hx)

/--
lemma `integral_le_measure` / 引理 `integral_le_measure`

English:
lemma integral_le_measure
  statement: {f : X -> Real} {s : Set X}
  proof: by
  by_cases H : Integrable f μ; swap
  · simp [integral_undef H]
  let g x := max (f x) 0
  have g_int : Integrable g μ := H.pos_part
  have : ENNReal.ofReal (∫ x, f x ∂μ) <= ENNReal.ofReal (∫ x, g x ∂μ) := by
    apply ENNReal.ofReal_le_ofReal
    exact integral_mono H g_int (fun x => le_max_left _ _)
  apply this.trans
  rw [ofReal_integral_eq_lintegral_ofReal g_int (Eventually.of_forall (fun x => le_max_right _ _))]
  apply lintegral_le_meas
  · intro x
    apply ENNReal.ofReal_le_of_le_toReal
    by_cases H : x in s
    · simpa [g] using hs x H
    · apply le_trans _ zero_le_one
      simpa [g] using h's x H
  · intro x hx
    simpa [g] using h's x hx

中文:
引理 integral_le_measure
  结论: {f : X -> 实数} {s : 集合 X}
  证明: by
  by_cases H : Integrable f μ; swap
  · simp [integral_undef H]
  let g x := max (f x) 0
  have g_int : Integrable g μ := H.pos_part
  have : ENNReal.ofReal (∫ x, f x ∂μ) <= ENNReal.ofReal (∫ x, g x ∂μ) := by
    apply ENNReal.ofReal_le_ofReal
    exact integral_mono H g_int (fun x => le_max_left _ _)
  apply this.trans
  rw [ofReal_integral_eq_lintegral_ofReal g_int (Eventually.of_forall (fun x => le_max_right _ _))]
  apply lintegral_le_meas
  · intro x
    apply ENNReal.ofReal_le_of_le_toReal
    by_cases H : x in s
    · simpa [g] using hs x H
    · apply le_trans _ zero_le_one
      simpa [g] using h's x H
  · intro x hx
    simpa [g] using h's x hx

Depends on / 依赖: ENNReal, ENNReal.ofReal, ENNReal.ofReal_le_ofReal, ENNReal.ofReal_le_of_le_toReal, Eventually, Eventually.of_forall, H.pos_part, Integrable, g_int, integral_mono, integral_undef, le_max_left, le_max_right, lintegral_le_meas, ofReal, ofReal_integral_eq_lintegral_ofReal, ofReal_le_ofReal, ofReal_le_of_le_toReal, of_forall, pos_part
-/
lemma integral_le_measure {f : X -> Real} {s : Set X}
    (hs : forall x in s, f x <= 1) (h's : forall x in sᶜ, f x <= 0) :
    ENNReal.ofReal (∫ x, f x ∂μ) <= μ s := by
  by_cases H : Integrable f μ; swap
  · simp [integral_undef H]
  let g x := max (f x) 0
  have g_int : Integrable g μ := H.pos_part
  have : ENNReal.ofReal (∫ x, f x ∂μ) <= ENNReal.ofReal (∫ x, g x ∂μ) := by
    apply ENNReal.ofReal_le_ofReal
    exact integral_mono H g_int (fun x => le_max_left _ _)
  apply this.trans
  rw [ofReal_integral_eq_lintegral_ofReal g_int (Eventually.of_forall (fun x => le_max_right _ _))]
  apply lintegral_le_meas
  · intro x
    apply ENNReal.ofReal_le_of_le_toReal
    by_cases H : x in s
    · simpa [g] using hs x H
    · apply le_trans _ zero_le_one
      simpa [g] using h's x H
  · intro x hx
    simpa [g] using h's x hx

/--
lemma `setIntegral_mono_of_nonneg` / 引理 `setIntegral_mono_of_nonneg`

English:
lemma setIntegral_mono_of_nonneg
  statement: {g : X -> Real} (hf : forall x in s, 0 <= f x)
  proof: by
  by_cases h'f : AEStronglyMeasurable f (μ.restrict s); swap
  · rw [integral_non_aestronglyMeasurable h'f]
    apply integral_nonneg_of_ae
    apply (ae_restrict_iff₀ ?_).2
    · filter_upwards with x hx using (hf x hx).trans (h x hx)
    · exact nullMeasurableSet_le aemeasurable_const hg.aemeasurable
  refine integral_mono_of_nonneg ?_ hg ?_
  · apply (ae_restrict_iff₀ ?_).2
    · filter_upwards with x hx using hf x hx
    · exact nullMeasurableSet_le aemeasurable_const h'f.aemeasurable
  · apply (ae_restrict_iff₀ ?_).2
    · filter_upwards with x hx using h x hx
    · exact nullMeasurableSet_le h'f.aemeasurable hg.aemeasurable

中文:
引理 set整数egral_mono_of_nonneg
  结论: {g : X -> 实数} (hf : 对任意 x in s, 0 <= f x)
  证明: by
  by_cases h'f : AEStronglyMeasurable f (μ.restrict s); swap
  · rw [integral_non_aestronglyMeasurable h'f]
    apply integral_nonneg_of_ae
    apply (ae_restrict_iff₀ ?_).2
    · filter_upwards with x hx using (hf x hx).trans (h x hx)
    · exact nullMeasurableSet_le aemeasurable_const hg.aemeasurable
  refine integral_mono_of_nonneg ?_ hg ?_
  · apply (ae_restrict_iff₀ ?_).2
    · filter_upwards with x hx using hf x hx
    · exact nullMeasurableSet_le aemeasurable_const h'f.aemeasurable
  · apply (ae_restrict_iff₀ ?_).2
    · filter_upwards with x hx using h x hx
    · exact nullMeasurableSet_le h'f.aemeasurable hg.aemeasurable

Depends on / 依赖: AEStronglyMeasurable, aemeasurable, aemeasurable_const, f.aemeasurable, filter_upwards, hg.aemeasurable, integral_mono_of_nonneg, integral_non_aestronglyMeasurable, integral_nonneg_of_ae, nullMeasurableSet_le, restrict
-/
lemma setIntegral_mono_of_nonneg {g : X -> Real} (hf : forall x in s, 0 <= f x)
    (h : forall x in s, f x <= g x) (hg : IntegrableOn g s μ) :
    ∫ x in s, f x ∂μ <= ∫ x in s, g x ∂μ := by
  by_cases h'f : AEStronglyMeasurable f (μ.restrict s); swap
  · rw [integral_non_aestronglyMeasurable h'f]
    apply integral_nonneg_of_ae
    apply (ae_restrict_iff₀ ?_).2
    · filter_upwards with x hx using (hf x hx).trans (h x hx)
    · exact nullMeasurableSet_le aemeasurable_const hg.aemeasurable
  refine integral_mono_of_nonneg ?_ hg ?_
  · apply (ae_restrict_iff₀ ?_).2
    · filter_upwards with x hx using hf x hx
    · exact nullMeasurableSet_le aemeasurable_const h'f.aemeasurable
  · apply (ae_restrict_iff₀ ?_).2
    · filter_upwards with x hx using h x hx
    · exact nullMeasurableSet_le h'f.aemeasurable hg.aemeasurable

end Nonneg

section IntegrableUnion

variable {ι : Type*} [Countable ι] {μ : Measure X} [NormedAddCommGroup E]

/--
theorem `integrableOn_iUnion_of_summable_integral_norm` / 定理 `integrableOn_iUnion_of_summable_integral_norm`

English:
theorem integrableOn_iUnion_of_summable_integral_norm
  statement: {f : X -> E} {s : ι -> Set X}
  proof: by
  refine ⟨AEStronglyMeasurable.iUnion fun i => (hi i).1, (lintegral_iUnion_le _ _).trans_lt ?_⟩
  have B := fun i => lintegral_coe_eq_integral (fun x : X => ‖f x‖₊) (hi i).norm
  simp_rw [enorm_eq_nnnorm, tsum_congr B]
  have S' : Summable fun i : ι =>
      (NNReal.mk (∫ x : X in s i, ‖f x‖₊ ∂μ) (integral_nonneg fun x => NNReal.coe_nonneg _)) := by
    rw [← NNReal.summable_coe]; exact h
  have S'' := ENNReal.tsum_coe_eq S'.hasSum
  simp_rw [ENNReal.coe_nnreal_eq, NNReal.coe_mk, coe_nnnorm] at S''
  convert! ENNReal.ofReal_lt_top

中文:
定理 integrableOn_iUnion_of_summable_integral_norm
  结论: {f : X -> E} {s : ι -> 集合 X}
  证明: by
  refine ⟨AEStronglyMeasurable.iUnion fun i => (hi i).1, (lintegral_iUnion_le _ _).trans_lt ?_⟩
  have B := fun i => lintegral_coe_eq_integral (fun x : X => ‖f x‖₊) (hi i).norm
  simp_rw [enorm_eq_nnnorm, tsum_congr B]
  have S' : Summable fun i : ι =>
      (NNReal.mk (∫ x : X in s i, ‖f x‖₊ ∂μ) (integral_nonneg fun x => NNReal.coe_nonneg _)) := by
    rw [← NNReal.summable_coe]; exact h
  have S'' := ENNReal.tsum_coe_eq S'.hasSum
  simp_rw [ENNReal.coe_nnreal_eq, NNReal.coe_mk, coe_nnnorm] at S''
  convert! ENNReal.ofReal_lt_top

Depends on / 依赖: AEStronglyMeasurable, AEStronglyMeasurable.iUnion, ENNRea, ENNReal, ENNReal.coe_nnreal_eq, ENNReal.tsum_coe_eq, NNReal, NNReal.coe_mk, NNReal.coe_nonneg, NNReal.mk, NNReal.summable_coe, Summable, coe_mk, coe_nnnorm, coe_nnreal_eq, coe_nonneg, convert, enorm_eq_nnnorm, hasSum, iUnion
-/
theorem integrableOn_iUnion_of_summable_integral_norm {f : X -> E} {s : ι -> Set X}
    (hi : forall i : ι, IntegrableOn f (s i) μ)
    (h : Summable fun i : ι => ∫ x : X in s i, ‖f x‖ ∂μ) : IntegrableOn f (iUnion s) μ := by
  refine ⟨AEStronglyMeasurable.iUnion fun i => (hi i).1, (lintegral_iUnion_le _ _).trans_lt ?_⟩
  have B := fun i => lintegral_coe_eq_integral (fun x : X => ‖f x‖₊) (hi i).norm
  simp_rw [enorm_eq_nnnorm, tsum_congr B]
  have S' : Summable fun i : ι =>
      (NNReal.mk (∫ x : X in s i, ‖f x‖₊ ∂μ) (integral_nonneg fun x => NNReal.coe_nonneg _)) := by
    rw [← NNReal.summable_coe]; exact h
  have S'' := ENNReal.tsum_coe_eq S'.hasSum
  simp_rw [ENNReal.coe_nnreal_eq, NNReal.coe_mk, coe_nnnorm] at S''
  convert! ENNReal.ofReal_lt_top

variable [TopologicalSpace X] [BorelSpace X] [T2Space X] [IsLocallyFiniteMeasure μ]

/--
theorem `integrableOn_iUnion_of_summable_norm_restrict` / 定理 `integrableOn_iUnion_of_summable_norm_restrict`

English:
theorem integrableOn_iUnion_of_summable_norm_restrict
  statement: {f : C(X, E)} {s : ι -> Compacts X}
  proof: by
  refine
    integrableOn_iUnion_of_summable_integral_norm
      (fun i => (map_continuous f).continuousOn.integrableOn_compact (s i).isCompact)
      (.of_nonneg_of_le (fun ι => integral_nonneg fun x => norm_nonneg _) (fun i => ?_) hf)
  rw [← (Real.norm_of_nonneg (integral_nonneg fun x => norm_nonneg _) : ‖_‖ = ∫ x in s i]; rw [‖f x‖ ∂μ)]
  exact
    norm_setIntegral_le_of_norm_le_const (s i).isCompact.measure_lt_top
      fun x hx => (norm_norm (f x)).symm ▸ (f.restrict (s i : Set X)).norm_coe_le_norm ⟨x, hx⟩

中文:
定理 integrableOn_iUnion_of_summable_norm_restrict
  结论: {f : C(X, E)} {s : ι -> 余mpacts X}
  证明: by
  refine
    integrableOn_iUnion_of_summable_integral_norm
      (fun i => (map_continuous f).continuousOn.integrableOn_compact (s i).isCompact)
      (.of_nonneg_of_le (fun ι => integral_nonneg fun x => norm_nonneg _) (fun i => ?_) hf)
  rw [← (Real.norm_of_nonneg (integral_nonneg fun x => norm_nonneg _) : ‖_‖ = ∫ x in s i]; rw [‖f x‖ ∂μ)]
  exact
    norm_setIntegral_le_of_norm_le_const (s i).isCompact.measure_lt_top
      fun x hx => (norm_norm (f x)).symm ▸ (f.restrict (s i : Set X)).norm_coe_le_norm ⟨x, hx⟩

Depends on / 依赖: Real.norm_of_nonneg, continuousOn, continuousOn.integrableOn_compact, f.restrict, integrableOn_compact, integrableOn_iUnion_of_summable_integral_norm, integral_nonneg, isCompact, isCompact.measure_lt_top, map_continuous, measure_lt_top, norm_coe_le_norm, norm_nonneg, norm_norm, norm_of_nonneg, norm_setIntegral_le_of_norm_le_const, of_nonneg_of_le, restrict
-/
theorem integrableOn_iUnion_of_summable_norm_restrict {f : C(X, E)} {s : ι -> Compacts X}
    (hf : Summable fun i : ι => ‖f.restrict (s i)‖ * μ.real (s i)) :
    IntegrableOn f (⋃ i : ι, s i) μ := by
  refine
    integrableOn_iUnion_of_summable_integral_norm
      (fun i => (map_continuous f).continuousOn.integrableOn_compact (s i).isCompact)
      (.of_nonneg_of_le (fun ι => integral_nonneg fun x => norm_nonneg _) (fun i => ?_) hf)
  rw [← (Real.norm_of_nonneg (integral_nonneg fun x => norm_nonneg _) : ‖_‖ = ∫ x in s i]; rw [‖f x‖ ∂μ)]
  exact
    norm_setIntegral_le_of_norm_le_const (s i).isCompact.measure_lt_top
      fun x hx => (norm_norm (f x)).symm ▸ (f.restrict (s i : Set X)).norm_coe_le_norm ⟨x, hx⟩

/--
theorem `integrable_of_summable_norm_restrict` / 定理 `integrable_of_summable_norm_restrict`

English:
theorem integrable_of_summable_norm_restrict
  statement: {f : C(X, E)} {s : ι -> Compacts X}
  proof: by
  simpa only [hs, integrableOn_univ] using integrableOn_iUnion_of_summable_norm_restrict hf

中文:
定理 integrable_of_summable_norm_restrict
  结论: {f : C(X, E)} {s : ι -> 余mpacts X}
  证明: by
  simpa only [hs, integrableOn_univ] using integrableOn_iUnion_of_summable_norm_restrict hf

Depends on / 依赖: integrableOn_iUnion_of_summable_norm_restrict, integrableOn_univ
-/
theorem integrable_of_summable_norm_restrict {f : C(X, E)} {s : ι -> Compacts X}
    (hf : Summable fun i : ι => ‖f.restrict (s i)‖ * μ.real (s i))
    (hs : ⋃ i : ι, ↑(s i) = (univ : Set X)) : Integrable f μ := by
  simpa only [hs, integrableOn_univ] using integrableOn_iUnion_of_summable_norm_restrict hf

end IntegrableUnion

/-! ### Continuity of the set integral

We prove that for any set `s`, the function
`fun f : X →₁[μ] E => ∫ x in s, f x ∂μ` is continuous. -/

section ContinuousSetIntegral

variable [NormedAddCommGroup E]
  {𝕜 : Type*} [NormedRing 𝕜] [NormedAddCommGroup F] [Module 𝕜 F] [IsBoundedSMul 𝕜 F]
  {p : Real>=0∞} {μ : Measure X}

/--
theorem `Lp_toLp_restrict_add` / 定理 `Lp_toLp_restrict_add`

English:
theorem Lp_toLp_restrict_add
  given: (f g : Lp E p μ) (s : Set X)
  proof: by
  ext1
  refine (ae_restrict_of_ae (Lp.coeFn_add f g)).mp ?_
  refine
    (Lp.coeFn_add (MemLp.toLp f ((Lp.memLp f).restrict s))
          (MemLp.toLp g ((Lp.memLp g).restrict s))).mp ?_
  refine (MemLp.coeFn_toLp ((Lp.memLp f).restrict s)).mp ?_
  refine (MemLp.coeFn_toLp ((Lp.memLp g).restrict s)).mp ?_
  refine (MemLp.coeFn_toLp ((Lp.memLp (f + g)).restrict s)).mono fun x hx1 hx2 hx3 hx4 hx5 => ?_
  rw [hx4]; rw [hx1]; rw [Pi.add_apply]; rw [hx2]; rw [hx3]; rw [hx5]; rw [Pi.add_apply]

中文:
定理 Lp_toLp_restrict_add
  条件: (f g : Lp E p μ) (s : 集合 X)
  证明: by
  ext1
  refine (ae_restrict_of_ae (Lp.coeFn_add f g)).mp ?_
  refine
    (Lp.coeFn_add (MemLp.toLp f ((Lp.memLp f).restrict s))
          (MemLp.toLp g ((Lp.memLp g).restrict s))).mp ?_
  refine (MemLp.coeFn_toLp ((Lp.memLp f).restrict s)).mp ?_
  refine (MemLp.coeFn_toLp ((Lp.memLp g).restrict s)).mp ?_
  refine (MemLp.coeFn_toLp ((Lp.memLp (f + g)).restrict s)).mono fun x hx1 hx2 hx3 hx4 hx5 => ?_
  rw [hx4]; rw [hx1]; rw [Pi.add_apply]; rw [hx2]; rw [hx3]; rw [hx5]; rw [Pi.add_apply]

Depends on / 依赖: Lp.coeFn_add, Lp.memLp, MemLp.coeFn_toLp, MemLp.toLp, Pi.add_apply, add_apply, ae_restrict_of_ae, coeFn_add, coeFn_toLp, restrict
-/
theorem Lp_toLp_restrict_add (f g : Lp E p μ) (s : Set X) :
    ((Lp.memLp (f + g)).restrict s).toLp (⇑(f + g)) =
      ((Lp.memLp f).restrict s).toLp f + ((Lp.memLp g).restrict s).toLp g := by
  ext1
  refine (ae_restrict_of_ae (Lp.coeFn_add f g)).mp ?_
  refine
    (Lp.coeFn_add (MemLp.toLp f ((Lp.memLp f).restrict s))
          (MemLp.toLp g ((Lp.memLp g).restrict s))).mp ?_
  refine (MemLp.coeFn_toLp ((Lp.memLp f).restrict s)).mp ?_
  refine (MemLp.coeFn_toLp ((Lp.memLp g).restrict s)).mp ?_
  refine (MemLp.coeFn_toLp ((Lp.memLp (f + g)).restrict s)).mono fun x hx1 hx2 hx3 hx4 hx5 => ?_
  rw [hx4]; rw [hx1]; rw [Pi.add_apply]; rw [hx2]; rw [hx3]; rw [hx5]; rw [Pi.add_apply]

/--
theorem `Lp_toLp_restrict_smul` / 定理 `Lp_toLp_restrict_smul`

English:
theorem Lp_toLp_restrict_smul
  given: (c : 𝕜) (f : Lp F p μ) (s : Set X)
  proof: by
  ext1
  refine (ae_restrict_of_ae (Lp.coeFn_smul c f)).mp ?_
  refine (MemLp.coeFn_toLp ((Lp.memLp f).restrict s)).mp ?_
  refine (MemLp.coeFn_toLp ((Lp.memLp (c • f)).restrict s)).mp ?_
  refine
    (Lp.coeFn_smul c (MemLp.toLp f ((Lp.memLp f).restrict s))).mono fun x hx1 hx2 hx3 hx4 => ?_
  simp only [hx2, hx1, hx3, hx4, Pi.smul_apply]

中文:
定理 Lp_toLp_restrict_smul
  条件: (c : 𝕜) (f : Lp F p μ) (s : 集合 X)
  证明: by
  ext1
  refine (ae_restrict_of_ae (Lp.coeFn_smul c f)).mp ?_
  refine (MemLp.coeFn_toLp ((Lp.memLp f).restrict s)).mp ?_
  refine (MemLp.coeFn_toLp ((Lp.memLp (c • f)).restrict s)).mp ?_
  refine
    (Lp.coeFn_smul c (MemLp.toLp f ((Lp.memLp f).restrict s))).mono fun x hx1 hx2 hx3 hx4 => ?_
  simp only [hx2, hx1, hx3, hx4, Pi.smul_apply]

Depends on / 依赖: Lp.coeFn_smul, Lp.memLp, MemLp.coeFn_toLp, MemLp.toLp, Pi.smul_apply, ae_restrict_of_ae, coeFn_smul, coeFn_toLp, restrict, smul_apply
-/
theorem Lp_toLp_restrict_smul (c : 𝕜) (f : Lp F p μ) (s : Set X) :
    ((Lp.memLp (c • f)).restrict s).toLp (⇑(c • f)) = c • ((Lp.memLp f).restrict s).toLp f := by
  ext1
  refine (ae_restrict_of_ae (Lp.coeFn_smul c f)).mp ?_
  refine (MemLp.coeFn_toLp ((Lp.memLp f).restrict s)).mp ?_
  refine (MemLp.coeFn_toLp ((Lp.memLp (c • f)).restrict s)).mp ?_
  refine
    (Lp.coeFn_smul c (MemLp.toLp f ((Lp.memLp f).restrict s))).mono fun x hx1 hx2 hx3 hx4 => ?_
  simp only [hx2, hx1, hx3, hx4, Pi.smul_apply]

/--
theorem `norm_Lp_toLp_restrict_le` / 定理 `norm_Lp_toLp_restrict_le`

English:
theorem norm_Lp_toLp_restrict_le
  given: (s : Set X) (f : Lp E p μ)
  proof: by
  rw [Lp.norm_def]; rw [Lp.norm_def]; rw [eLpNorm_congr_ae (MemLp.coeFn_toLp _)]
  refine ENNReal.toReal_mono (Lp.eLpNorm_ne_top _) ?_
  exact eLpNorm_mono_measure _ Measure.restrict_le_self

中文:
定理 norm_Lp_toLp_restrict_le
  条件: (s : 集合 X) (f : Lp E p μ)
  证明: by
  rw [Lp.norm_def]; rw [Lp.norm_def]; rw [eLpNorm_congr_ae (MemLp.coeFn_toLp _)]
  refine ENNReal.toReal_mono (Lp.eLpNorm_ne_top _) ?_
  exact eLpNorm_mono_measure _ Measure.restrict_le_self

Depends on / 依赖: ENNReal, ENNReal.toReal_mono, Lp.eLpNorm_ne_top, Lp.norm_def, Measure, Measure.restrict_le_self, MemLp.coeFn_toLp, coeFn_toLp, eLpNorm_congr_ae, eLpNorm_mono_measure, eLpNorm_ne_top, norm_def, restrict_le_self, toReal_mono
-/
theorem norm_Lp_toLp_restrict_le (s : Set X) (f : Lp E p μ) :
    ‖((Lp.memLp f).restrict s).toLp f‖ <= ‖f‖ := by
  rw [Lp.norm_def]; rw [Lp.norm_def]; rw [eLpNorm_congr_ae (MemLp.coeFn_toLp _)]
  refine ENNReal.toReal_mono (Lp.eLpNorm_ne_top _) ?_
  exact eLpNorm_mono_measure _ Measure.restrict_le_self

variable (X F 𝕜) in
/--
Definition of `LpToLpRestrictCLM` / `LpToLpRestrictCLM` 的定义

English:
definition LpToLpRestrictCLM
  signature: (μ : Measure X) (p : Real>=0∞) [hp : Fact (1 <= p)] (s : Set X)
  body: @LinearMap.mkContinuous 𝕜 𝕜 (Lp F p μ) (Lp F p (μ.restrict s)) _ _ _ _ _ _ (RingHom.id 𝕜)
    ⟨⟨fun f => MemLp.toLp f ((Lp.memLp f).restrict s), fun f g => Lp_toLp_restrict_add f g s⟩,
      fun c f => Lp_toLp_restrict_smul c f s⟩
    1 (by intro f; rw [one_mul]; exact norm_Lp_toLp_restrict_le s f)

中文:
定义 LpToLpRestrictCLM
  签名: (μ : 测度 X) (p : 实数>=0∞) [hp : Fact (1 <= p)] (s : 集合 X)
  定义体: @LinearMap.mkContinuous 𝕜 𝕜 (Lp F p μ) (Lp F p (μ.restrict s)) _ _ _ _ _ _ (RingHom.id 𝕜)
    ⟨⟨fun f => MemLp.toLp f ((Lp.memLp f).restrict s), fun f g => Lp_toLp_restrict_add f g s⟩,
      fun c f => Lp_toLp_restrict_smul c f s⟩
    1 (by intro f; rw [one_mul]; exact norm_Lp_toLp_restrict_le s f)

Depends on / 依赖: LinearMap, LinearMap.mkContinuous, Lp.memLp, Lp_toLp_restrict_add, Lp_toLp_restrict_smul, MemLp.toLp, RingHom, RingHom.id, mkContinuous, norm_Lp_toLp_restrict_le, one_mul, restrict
-/
noncomputable def LpToLpRestrictCLM (μ : Measure X) (p : Real>=0∞) [hp : Fact (1 <= p)] (s : Set X) :
    Lp F p μ ->L[𝕜] Lp F p (μ.restrict s) :=
  @LinearMap.mkContinuous 𝕜 𝕜 (Lp F p μ) (Lp F p (μ.restrict s)) _ _ _ _ _ _ (RingHom.id 𝕜)
    ⟨⟨fun f => MemLp.toLp f ((Lp.memLp f).restrict s), fun f g => Lp_toLp_restrict_add f g s⟩,
      fun c f => Lp_toLp_restrict_smul c f s⟩
    1 (by intro f; rw [one_mul]; exact norm_Lp_toLp_restrict_le s f)

variable (𝕜) in
/--
theorem `LpToLpRestrictCLM_coeFn` / 定理 `LpToLpRestrictCLM_coeFn`

English:
theorem LpToLpRestrictCLM_coeFn
  given: [Fact (1 <= p)] (s : Set X) (f : Lp F p μ)
  proof: MemLp.coeFn_toLp ((Lp.memLp f).restrict s)

@[continuity]

中文:
定理 LpToLpRestrictCLM_coeFn
  条件: [Fact (1 <= p)] (s : 集合 X) (f : Lp F p μ)
  证明: MemLp.coeFn_toLp ((Lp.memLp f).restrict s)

@[continuity]

Depends on / 依赖: Lp.memLp, MemLp.coeFn_toLp, coeFn_toLp, restrict
-/
theorem LpToLpRestrictCLM_coeFn [Fact (1 <= p)] (s : Set X) (f : Lp F p μ) :
    LpToLpRestrictCLM X F 𝕜 μ p s f =ᵐ[μ.restrict s] f :=
  MemLp.coeFn_toLp ((Lp.memLp f).restrict s)

@[continuity]
/--
theorem `continuous_setIntegral` / 定理 `continuous_setIntegral`

English:
theorem continuous_setIntegral
  given: [NormedSpace Real E] (s : Set X)
  proof: by
  have : Fact ((1 : Real>=0∞) <= 1) := ⟨le_rfl⟩
  have h_comp :
    (fun f : X ->₁[μ] E => ∫ x in s, f x ∂μ) =
      integral (μ.restrict s) ∘ fun f => LpToLpRestrictCLM X E Real μ 1 s f := by
    ext1 f
    rw [Function.comp_apply]; rw [integral_congr_ae (LpToLpRestrictCLM_coeFn Real s f)]
  rw [h_comp]
  exact continuous_integral.comp (LpToLpRestrictCLM X E Real μ 1 s).continuous

中文:
定理 continuous_set整数egral
  条件: [赋范空间 实数 E] (s : 集合 X)
  证明: by
  have : Fact ((1 : Real>=0∞) <= 1) := ⟨le_rfl⟩
  have h_comp :
    (fun f : X ->₁[μ] E => ∫ x in s, f x ∂μ) =
      integral (μ.restrict s) ∘ fun f => LpToLpRestrictCLM X E Real μ 1 s f := by
    ext1 f
    rw [Function.comp_apply]; rw [integral_congr_ae (LpToLpRestrictCLM_coeFn Real s f)]
  rw [h_comp]
  exact continuous_integral.comp (LpToLpRestrictCLM X E Real μ 1 s).continuous

Depends on / 依赖: Function, Function.comp_apply, LpToLpRestrictCLM, LpToLpRestrictCLM_coeFn, comp_apply, continuous, continuous_integral, continuous_integral.comp, h_comp, integral, integral_congr_ae, le_rfl, restrict
-/
theorem continuous_setIntegral [NormedSpace Real E] (s : Set X) :
    Continuous fun f : X ->₁[μ] E => ∫ x in s, f x ∂μ := by
  have : Fact ((1 : Real>=0∞) <= 1) := ⟨le_rfl⟩
  have h_comp :
    (fun f : X ->₁[μ] E => ∫ x in s, f x ∂μ) =
      integral (μ.restrict s) ∘ fun f => LpToLpRestrictCLM X E Real μ 1 s f := by
    ext1 f
    rw [Function.comp_apply]; rw [integral_congr_ae (LpToLpRestrictCLM_coeFn Real s f)]
  rw [h_comp]
  exact continuous_integral.comp (LpToLpRestrictCLM X E Real μ 1 s).continuous

end ContinuousSetIntegral

end MeasureTheory

section OpenPos

open Measure

variable [MeasurableSpace X] [TopologicalSpace X] [OpensMeasurableSpace X]
  {μ : Measure X} [IsOpenPosMeasure μ]

/--
theorem `Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero` / 定理 `Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero`

English:
theorem Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero
  statement: [IsFiniteMeasureOnCompacts μ]
  proof: integral_pos_of_integrable_nonneg_nonzero f_cont (f_cont.integrable_of_hasCompactSupport f_comp)
    f_nonneg f_x

中文:
定理 连续.integral_pos_of_hasCompactSupport_nonneg_nonzero
  结论: [紧集上有限测度 μ]
  证明: integral_pos_of_integrable_nonneg_nonzero f_cont (f_cont.integrable_of_hasCompactSupport f_comp)
    f_nonneg f_x

Depends on / 依赖: f_comp, f_cont, f_cont.integrable_of_hasCompactSupport, f_nonneg, integrable_of_hasCompactSupport, integral_pos_of_integrable_nonneg_nonzero
-/
theorem Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero [IsFiniteMeasureOnCompacts μ]
    {f : X -> Real} {x : X} (f_cont : Continuous f) (f_comp : HasCompactSupport f) (f_nonneg : 0 <= f)
    (f_x : f x != 0) : 0 < ∫ x, f x ∂μ :=
  integral_pos_of_integrable_nonneg_nonzero f_cont (f_cont.integrable_of_hasCompactSupport f_comp)
    f_nonneg f_x

end OpenPos

section Support

variable {M : Type*} [NormedAddCommGroup M] [NormedSpace Real M] {mX : MeasurableSpace X}
  {ν : Measure X} {F : X -> M}

/--
theorem `MeasureTheory.setIntegral_support` / 定理 `MeasureTheory.setIntegral_support`

English:
theorem MeasureTheory.setIntegral_support
  statement: ∫ x in support F, F x ∂ν = ∫ x, F x ∂ν
  proof: by
  nth_rw 2 [← setIntegral_univ]
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero MeasurableSet.univ (subset_univ (support F))]
exact fun _ hx => notMem_support.mp notMem_of_mem_sdiff hx

中文:
定理 测度论.set整数egral_support
  结论: ∫ x in support F, F x ∂ν = ∫ x, F x ∂ν
  证明: by
  nth_rw 2 [← setIntegral_univ]
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero MeasurableSet.univ (subset_univ (support F))]
exact fun _ hx => notMem_support.mp notMem_of_mem_sdiff hx

Depends on / 依赖: MeasurableSet, MeasurableSet.univ, notMem_of_mem_sdiff, notMem_support, notMem_support.mp, nth_rw, setIntegral_eq_of_subset_of_forall_sdiff_eq_zero, setIntegral_univ, subset_univ, support
-/
theorem MeasureTheory.setIntegral_support : ∫ x in support F, F x ∂ν = ∫ x, F x ∂ν := by
  nth_rw 2 [← setIntegral_univ]
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero MeasurableSet.univ (subset_univ (support F))]
exact fun _ hx => notMem_support.mp notMem_of_mem_sdiff hx

/--
theorem `MeasureTheory.setIntegral_tsupport` / 定理 `MeasureTheory.setIntegral_tsupport`

English:
theorem MeasureTheory.setIntegral_tsupport
  given: [TopologicalSpace X]
  proof: by
  nth_rw 2 [← setIntegral_univ]
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero MeasurableSet.univ
    (subset_univ (tsupport F))]
exact fun _ hx => image_eq_zero_of_notMem_tsupport notMem_of_mem_sdiff hx

中文:
定理 测度论.set整数egral_tsupport
  条件: [拓扑空间 X]
  证明: by
  nth_rw 2 [← setIntegral_univ]
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero MeasurableSet.univ
    (subset_univ (tsupport F))]
exact fun _ hx => image_eq_zero_of_notMem_tsupport notMem_of_mem_sdiff hx

Depends on / 依赖: MeasurableSet, MeasurableSet.univ, image_eq_zero_of_notMem_tsupport, notMem_of_mem_sdiff, nth_rw, setIntegral_eq_of_subset_of_forall_sdiff_eq_zero, setIntegral_univ, subset_univ, tsupport
-/
theorem MeasureTheory.setIntegral_tsupport [TopologicalSpace X] :
    ∫ x in tsupport F, F x ∂ν = ∫ x, F x ∂ν := by
  nth_rw 2 [← setIntegral_univ]
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero MeasurableSet.univ
    (subset_univ (tsupport F))]
exact fun _ hx => image_eq_zero_of_notMem_tsupport notMem_of_mem_sdiff hx

end Support

section thickenedIndicator

variable [MeasurableSpace X] [PseudoEMetricSpace X]

/--
theorem `measure_le_lintegral_thickenedIndicatorAux` / 定理 `measure_le_lintegral_thickenedIndicatorAux`

English:
theorem measure_le_lintegral_thickenedIndicatorAux
  statement: (μ : Measure X) {E : Set X}
  proof: by
  convert_to lintegral μ (E.indicator fun _ => (1 : Real>=0∞)) <= lintegral μ (thickenedIndicatorAux δ E)
  · rw [lintegral_indicator E_mble]
    simp only [lintegral_one, Measure.restrict_apply, MeasurableSet.univ, univ_inter]
  · apply lintegral_mono
    apply indicator_le_thickenedIndicatorAux

中文:
定理 measure_le_lintegral_thickenedIndicatorAux
  结论: (μ : 测度 X) {E : 集合 X}
  证明: by
  convert_to lintegral μ (E.indicator fun _ => (1 : Real>=0∞)) <= lintegral μ (thickenedIndicatorAux δ E)
  · rw [lintegral_indicator E_mble]
    simp only [lintegral_one, Measure.restrict_apply, MeasurableSet.univ, univ_inter]
  · apply lintegral_mono
    apply indicator_le_thickenedIndicatorAux

Depends on / 依赖: E.indicator, E_mble, MeasurableSet, MeasurableSet.univ, Measure, Measure.restrict_apply, convert_to, indicator, indicator_le_thickenedIndicatorAux, lintegral, lintegral_indicator, lintegral_mono, lintegral_one, restrict_apply, thickenedIndicatorAux, univ_inter
-/
theorem measure_le_lintegral_thickenedIndicatorAux (μ : Measure X) {E : Set X}
    (E_mble : MeasurableSet E) (δ : Real) : μ E <= ∫⁻ x, (thickenedIndicatorAux δ E x : Real>=0∞) ∂μ := by
  convert_to lintegral μ (E.indicator fun _ => (1 : Real>=0∞)) <= lintegral μ (thickenedIndicatorAux δ E)
  · rw [lintegral_indicator E_mble]
    simp only [lintegral_one, Measure.restrict_apply, MeasurableSet.univ, univ_inter]
  · apply lintegral_mono
    apply indicator_le_thickenedIndicatorAux

set_option backward.defeqAttrib.useBackward true in
/--
theorem `measure_le_lintegral_thickenedIndicator` / 定理 `measure_le_lintegral_thickenedIndicator`

English:
theorem measure_le_lintegral_thickenedIndicator
  statement: (μ : Measure X) {E : Set X}
  proof: by
  convert! measure_le_lintegral_thickenedIndicatorAux μ E_mble δ
  dsimp
  simp only [thickenedIndicatorAux_lt_top.ne, ENNReal.coe_toNNReal, Ne, not_false_iff]

中文:
定理 measure_le_lintegral_thickenedIndicator
  结论: (μ : 测度 X) {E : 集合 X}
  证明: by
  convert! measure_le_lintegral_thickenedIndicatorAux μ E_mble δ
  dsimp
  simp only [thickenedIndicatorAux_lt_top.ne, ENNReal.coe_toNNReal, Ne, not_false_iff]

Depends on / 依赖: ENNReal, ENNReal.coe_toNNReal, E_mble, coe_toNNReal, convert, measure_le_lintegral_thickenedIndicatorAux, not_false_iff, thickenedIndicatorAux_lt_top, thickenedIndicatorAux_lt_top.ne
-/
theorem measure_le_lintegral_thickenedIndicator (μ : Measure X) {E : Set X}
    (E_mble : MeasurableSet E) {δ : Real} (δ_pos : 0 < δ) :
    μ E <= ∫⁻ x, (thickenedIndicator δ_pos E x : Real>=0∞) ∂μ := by
  convert! measure_le_lintegral_thickenedIndicatorAux μ E_mble δ
  dsimp
  simp only [thickenedIndicatorAux_lt_top.ne, ENNReal.coe_toNNReal, Ne, not_false_iff]

end thickenedIndicator

-- We declare a new `{X : Type*}` to discard the instance `[MeasurableSpace X]`
-- which has been in scope for the entire file up to this point.
variable {X : Type*}

section BilinearMap

namespace MeasureTheory

variable {X : Type*} {f : X -> Real} {m m0 : MeasurableSpace X} {μ : Measure X}

/--
theorem `Integrable.simpleFunc_mul` / 定理 `Integrable.simpleFunc_mul`

English:
theorem Integrable.simpleFunc_mul
  given: (g : SimpleFunc X Real) (hf : Integrable f μ)
  proof: by
  refine
    SimpleFunc.induction (fun c s hs => ?_)
      (fun g₁ g₂ _ h_int₁ h_int₂ =>
        (h_int₁.add h_int₂).congr (by rw [SimpleFunc.coe_add, add_mul]))
      g
  simp only [SimpleFunc.const_zero, SimpleFunc.coe_piecewise, SimpleFunc.coe_const,
    SimpleFunc.coe_zero, Set.piecewise_eq_indicator]
  have : Set.indicator s (Function.const X c) * f = s.indicator (c • f) := by
    ext1 x
    by_cases hx : x in s
    · simp only [hx, Pi.mul_apply, Set.indicator_of_mem, Pi.smul_apply, smul_eq_mul,
        ← Function.const_def]
    · simp only [hx, Pi.mul_apply, Set.indicator_of_notMem, not_false_iff, zero_mul]
  rw [this]; rw [integrable_indicator_iff hs]
  exact (hf.smul c).integrableOn

中文:
定理 可积.simpleFunc_mul
  条件: (g : SimpleFunc X 实数) (hf : 可积 f μ)
  证明: by
  refine
    SimpleFunc.induction (fun c s hs => ?_)
      (fun g₁ g₂ _ h_int₁ h_int₂ =>
        (h_int₁.add h_int₂).congr (by rw [SimpleFunc.coe_add, add_mul]))
      g
  simp only [SimpleFunc.const_zero, SimpleFunc.coe_piecewise, SimpleFunc.coe_const,
    SimpleFunc.coe_zero, Set.piecewise_eq_indicator]
  have : Set.indicator s (Function.const X c) * f = s.indicator (c • f) := by
    ext1 x
    by_cases hx : x in s
    · simp only [hx, Pi.mul_apply, Set.indicator_of_mem, Pi.smul_apply, smul_eq_mul,
        ← Function.const_def]
    · simp only [hx, Pi.mul_apply, Set.indicator_of_notMem, not_false_iff, zero_mul]
  rw [this]; rw [integrable_indicator_iff hs]
  exact (hf.smul c).integrableOn

Depends on / 依赖: Function, Function.const, Function.const_def, Pi.mul_apply, Pi.smul_apply, Set.indicator, Set.indicator_of_mem, Set.piecewise_eq_indicator, SimpleFunc, SimpleFunc.coe_add, SimpleFunc.coe_const, SimpleFunc.coe_piecewise, SimpleFunc.coe_zero, SimpleFunc.const_zero, SimpleFunc.induction, add_mul, coe_add, coe_const, coe_piecewise, coe_zero
-/
theorem Integrable.simpleFunc_mul (g : SimpleFunc X Real) (hf : Integrable f μ) :
    Integrable (⇑g * f) μ := by
  refine
    SimpleFunc.induction (fun c s hs => ?_)
      (fun g₁ g₂ _ h_int₁ h_int₂ =>
        (h_int₁.add h_int₂).congr (by rw [SimpleFunc.coe_add, add_mul]))
      g
  simp only [SimpleFunc.const_zero, SimpleFunc.coe_piecewise, SimpleFunc.coe_const,
    SimpleFunc.coe_zero, Set.piecewise_eq_indicator]
  have : Set.indicator s (Function.const X c) * f = s.indicator (c • f) := by
    ext1 x
    by_cases hx : x in s
    · simp only [hx, Pi.mul_apply, Set.indicator_of_mem, Pi.smul_apply, smul_eq_mul,
        ← Function.const_def]
    · simp only [hx, Pi.mul_apply, Set.indicator_of_notMem, not_false_iff, zero_mul]
  rw [this]; rw [integrable_indicator_iff hs]
  exact (hf.smul c).integrableOn

/--
theorem `Integrable.simpleFunc_mul'` / 定理 `Integrable.simpleFunc_mul'`

English:
theorem Integrable.simpleFunc_mul'
  given: (hm : m <= m0) (g : @SimpleFunc X m Real) (hf : Integrable f μ)
  proof: by
  rw [← SimpleFunc.coe_toLargerSpace_eq hm g]; exact hf.simpleFunc_mul (g.toLargerSpace hm)

中文:
定理 可积.simpleFunc_mul'
  条件: (hm : m <= m0) (g : @SimpleFunc X m 实数) (hf : 可积 f μ)
  证明: by
  rw [← SimpleFunc.coe_toLargerSpace_eq hm g]; exact hf.simpleFunc_mul (g.toLargerSpace hm)

Depends on / 依赖: SimpleFunc, SimpleFunc.coe_toLargerSpace_eq, coe_toLargerSpace_eq, g.toLargerSpace, hf.simpleFunc_mul, simpleFunc_mul, toLargerSpace
-/
theorem Integrable.simpleFunc_mul' (hm : m <= m0) (g : @SimpleFunc X m Real) (hf : Integrable f μ) :
    Integrable (⇑g * f) μ := by
  rw [← SimpleFunc.coe_toLargerSpace_eq hm g]; exact hf.simpleFunc_mul (g.toLargerSpace hm)

end MeasureTheory

end BilinearMap

section ParametricIntegral

variable {G 𝕜 : Type*} [TopologicalSpace X]
  [TopologicalSpace Y] [MeasurableSpace Y] [OpensMeasurableSpace Y] {μ : Measure Y}
  [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace Real E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedAddCommGroup G] [NormedSpace 𝕜 G]

open Metric ContinuousLinearMap

/--
theorem `continuous_parametric_integral_of_continuous` / 定理 `continuous_parametric_integral_of_continuous`

English:
theorem continuous_parametric_integral_of_continuous
  proof: by
  rw [continuous_iff_continuousAt]
  intro x₀
  rcases exists_compact_mem_nhds x₀ with ⟨U, U_cpct, U_nhds⟩
  rcases (U_cpct.prod hs).bddAbove_image hf.norm.continuousOn with ⟨M, hM⟩
  apply continuousAt_of_dominated
  · filter_upwards with x using Continuous.aestronglyMeasurable (by fun_prop)
  · filter_upwards [U_nhds] with x x_in
    rw [ae_restrict_iff]
    · filter_upwards with t t_in using hM (mem_image_of_mem _ <| mk_mem_prod x_in t_in)
    · exact (isClosed_le (by fun_prop) (by fun_prop)).measurableSet
  · exact integrableOn_const hs.measure_ne_top
  · filter_upwards using (by fun_prop)

中文:
定理 continuous_parametric_integral_of_continuous
  证明: by
  rw [continuous_iff_continuousAt]
  intro x₀
  rcases exists_compact_mem_nhds x₀ with ⟨U, U_cpct, U_nhds⟩
  rcases (U_cpct.prod hs).bddAbove_image hf.norm.continuousOn with ⟨M, hM⟩
  apply continuousAt_of_dominated
  · filter_upwards with x using Continuous.aestronglyMeasurable (by fun_prop)
  · filter_upwards [U_nhds] with x x_in
    rw [ae_restrict_iff]
    · filter_upwards with t t_in using hM (mem_image_of_mem _ <| mk_mem_prod x_in t_in)
    · exact (isClosed_le (by fun_prop) (by fun_prop)).measurableSet
  · exact integrableOn_const hs.measure_ne_top
  · filter_upwards using (by fun_prop)

Depends on / 依赖: Continuous, Continuous.aestronglyMeasurable, U_cpct, U_cpct.prod, U_nhds, ae_restrict_iff, aestronglyMeasurable, bddAbove_image, continuousAt_of_dominated, continuousOn, continuous_iff_continuousAt, exists_compact_mem_nhds, filter_upwards, fun_prop, hf.norm.continuousOn, isClosed_le, measurableSet, mem_image_of_mem, mk_mem_prod, t_in
-/
theorem continuous_parametric_integral_of_continuous
    [FirstCountableTopology X] [LocallyCompactSpace X]
    [SecondCountableTopologyEither Y E] [IsLocallyFiniteMeasure μ]
    {f : X -> Y -> E} (hf : Continuous f.uncurry) {s : Set Y} (hs : IsCompact s) :
    Continuous (∫ y in s, f · y ∂μ) := by
  rw [continuous_iff_continuousAt]
  intro x₀
  rcases exists_compact_mem_nhds x₀ with ⟨U, U_cpct, U_nhds⟩
  rcases (U_cpct.prod hs).bddAbove_image hf.norm.continuousOn with ⟨M, hM⟩
  apply continuousAt_of_dominated
  · filter_upwards with x using Continuous.aestronglyMeasurable (by fun_prop)
  · filter_upwards [U_nhds] with x x_in
    rw [ae_restrict_iff]
    · filter_upwards with t t_in using hM (mem_image_of_mem _ <| mk_mem_prod x_in t_in)
    · exact (isClosed_le (by fun_prop) (by fun_prop)).measurableSet
  · exact integrableOn_const hs.measure_ne_top
  · filter_upwards using (by fun_prop)

/--
lemma `continuousOn_integral_bilinear_of_locally_integrable_of_compact_support` / 引理 `continuousOn_integral_bilinear_of_locally_integrable_of_compact_support`

English:
lemma continuousOn_integral_bilinear_of_locally_integrable_of_compact_support
  proof: by
  have A : forall p in s, Continuous (f p) := fun p hp => by
    refine hf.comp_continuous (.prodMk_right _) fun y => ?_
    simpa only [prodMk_mem_set_prod_eq, mem_univ, and_true] using hp
  intro q hq
  apply Metric.continuousWithinAt_iff'.2 (fun ε εpos => ?_)
  obtain ⟨δ, δpos, hδ⟩ : exists (δ : Real), 0 < δ ∧ ∫ x in k, ‖L‖ * ‖g x‖ * δ ∂μ < ε := by
    simpa [integral_mul_const] using exists_pos_mul_lt εpos _
  obtain ⟨v, v_mem, hv⟩ : exists v in 𝓝[s] q, forall p in v, forall x in k, dist (f p x) (f q x) < δ :=
    hk.mem_uniformity_of_prod
      (hf.mono (Set.prod_mono_right (subset_univ k))) hq (dist_mem_uniformity δpos)
  simp_rw [dist_eq_norm] at hv ⊢
  have I : forall p in s, IntegrableOn (fun y => L (g y) (f p y)) k μ := by
    intro p hp
    obtain ⟨C, hC⟩ : exists C, forall y, ‖f p y‖ <= C := by
      have : ContinuousOn (f p) k := by
        have : ContinuousOn (fun y => (p, y)) k := by fun_prop
        exact hf.comp this (by simp [MapsTo, hp])
      rcases IsCompact.exists_bound_of_continuousOn hk this with ⟨C, hC⟩
      refine ⟨max C 0, fun y => ?_⟩
      by_cases hx : y in k
      · exact (hC y hx).trans (le_max_left _ _)
      · simp [hfs p y hp hx]
    have : IntegrableOn (fun y => ‖L‖ * ‖g y‖ * C) k μ :=
      (hg.norm.const_mul _).mul_const _
    apply Integrable.mono' this ?_ ?_
    · borelize G
      apply L.aestronglyMeasurable_comp₂ hg.aestronglyMeasurable
      apply StronglyMeasurable.aestronglyMeasurable
      apply Continuous.stronglyMeasurable_of_support_subset_isCompact (A p hp) hk
      apply support_subset_iff'.2 (fun y hy => hfs p y hp hy)
    · apply Eventually.of_forall (fun y => (le_opNorm₂ L (g y) (f p y)).trans ?_)
      gcongr
      apply hC
  filter_upwards [v_mem, self_mem_nhdsWithin] with p hp h'p
  calc
  ‖∫ x, L (g x) (f p x) ∂μ - ∫ x, L (g x) (f q x) ∂μ‖
    = ‖∫ x in k, L (g x) (f p x) ∂μ - ∫ x in k, L (g x) (f q x) ∂μ‖ := by
      congr 2
      · refine (setIntegral_eq_integral_of_forall_compl_eq_zero (fun y hy => ?_)).symm
        simp [hfs p y h'p hy]
      · refine (setIntegral_eq_integral_of_forall_compl_eq_zero (fun y hy => ?_)).symm
        simp [hfs q y hq hy]
  _ = ‖∫ x in k, L (g x) (f p x) - L (g x) (f q x) ∂μ‖ := by rw [integral_sub (I p h'p) (I q hq)]
  _ <= ∫ x in k, ‖L (g x) (f p x) - L (g x) (f q x)‖ ∂μ := norm_integral_le_integral_norm _
  _ <= ∫ x in k, ‖L‖ * ‖g x‖ * δ ∂μ := by
      apply integral_mono_of_nonneg (Eventually.of_forall (fun y => by positivity))
      · exact (hg.norm.const_mul _).mul_const _
      · filter_upwards with y
        by_cases hy : y in k
        · specialize hv p hp y hy
          calc
          ‖L (g y) (f p y) - L (g y) (f q y)‖
            = ‖L (g y) (f p y - f q y)‖ := by simp only [map_sub]
          _ <= ‖L‖ * ‖g y‖ * ‖f p y - f q y‖ := le_opNorm₂ _ _ _
          _ <= ‖L‖ * ‖g y‖ * δ := by gcongr
        · simp only [hfs p y h'p hy, hfs q y hq hy, sub_self, norm_zero]
          positivity
  _ < ε := hδ

中文:
引理 continuousOn_integral_bilinear_of_locally_integrable_of_compact_support
  证明: by
  have A : forall p in s, Continuous (f p) := fun p hp => by
    refine hf.comp_continuous (.prodMk_right _) fun y => ?_
    simpa only [prodMk_mem_set_prod_eq, mem_univ, and_true] using hp
  intro q hq
  apply Metric.continuousWithinAt_iff'.2 (fun ε εpos => ?_)
  obtain ⟨δ, δpos, hδ⟩ : exists (δ : Real), 0 < δ ∧ ∫ x in k, ‖L‖ * ‖g x‖ * δ ∂μ < ε := by
    simpa [integral_mul_const] using exists_pos_mul_lt εpos _
  obtain ⟨v, v_mem, hv⟩ : exists v in 𝓝[s] q, forall p in v, forall x in k, dist (f p x) (f q x) < δ :=
    hk.mem_uniformity_of_prod
      (hf.mono (Set.prod_mono_right (subset_univ k))) hq (dist_mem_uniformity δpos)
  simp_rw [dist_eq_norm] at hv ⊢
  have I : forall p in s, IntegrableOn (fun y => L (g y) (f p y)) k μ := by
    intro p hp
    obtain ⟨C, hC⟩ : exists C, forall y, ‖f p y‖ <= C := by
      have : ContinuousOn (f p) k := by
        have : ContinuousOn (fun y => (p, y)) k := by fun_prop
        exact hf.comp this (by simp [MapsTo, hp])
      rcases IsCompact.exists_bound_of_continuousOn hk this with ⟨C, hC⟩
      refine ⟨max C 0, fun y => ?_⟩
      by_cases hx : y in k
      · exact (hC y hx).trans (le_max_left _ _)
      · simp [hfs p y hp hx]
    have : IntegrableOn (fun y => ‖L‖ * ‖g y‖ * C) k μ :=
      (hg.norm.const_mul _).mul_const _
    apply Integrable.mono' this ?_ ?_
    · borelize G
      apply L.aestronglyMeasurable_comp₂ hg.aestronglyMeasurable
      apply StronglyMeasurable.aestronglyMeasurable
      apply Continuous.stronglyMeasurable_of_support_subset_isCompact (A p hp) hk
      apply support_subset_iff'.2 (fun y hy => hfs p y hp hy)
    · apply Eventually.of_forall (fun y => (le_opNorm₂ L (g y) (f p y)).trans ?_)
      gcongr
      apply hC
  filter_upwards [v_mem, self_mem_nhdsWithin] with p hp h'p
  calc
  ‖∫ x, L (g x) (f p x) ∂μ - ∫ x, L (g x) (f q x) ∂μ‖
    = ‖∫ x in k, L (g x) (f p x) ∂μ - ∫ x in k, L (g x) (f q x) ∂μ‖ := by
      congr 2
      · refine (setIntegral_eq_integral_of_forall_compl_eq_zero (fun y hy => ?_)).symm
        simp [hfs p y h'p hy]
      · refine (setIntegral_eq_integral_of_forall_compl_eq_zero (fun y hy => ?_)).symm
        simp [hfs q y hq hy]
  _ = ‖∫ x in k, L (g x) (f p x) - L (g x) (f q x) ∂μ‖ := by rw [integral_sub (I p h'p) (I q hq)]
  _ <= ∫ x in k, ‖L (g x) (f p x) - L (g x) (f q x)‖ ∂μ := norm_integral_le_integral_norm _
  _ <= ∫ x in k, ‖L‖ * ‖g x‖ * δ ∂μ := by
      apply integral_mono_of_nonneg (Eventually.of_forall (fun y => by positivity))
      · exact (hg.norm.const_mul _).mul_const _
      · filter_upwards with y
        by_cases hy : y in k
        · specialize hv p hp y hy
          calc
          ‖L (g y) (f p y) - L (g y) (f q y)‖
            = ‖L (g y) (f p y - f q y)‖ := by simp only [map_sub]
          _ <= ‖L‖ * ‖g y‖ * ‖f p y - f q y‖ := le_opNorm₂ _ _ _
          _ <= ‖L‖ * ‖g y‖ * δ := by gcongr
        · simp only [hfs p y h'p hy, hfs q y hq hy, sub_self, norm_zero]
          positivity
  _ < ε := hδ

Depends on / 依赖: Continuous, Metric, Metric.continuousWithinAt_iff, and_true, comp_continuous, continuousWithinAt_iff, exists_pos_mul_lt, hf.comp_continuous, integral_mul_const, mem_univ, prodMk_mem_set_prod_eq, prodMk_right, v_mem
-/
lemma continuousOn_integral_bilinear_of_locally_integrable_of_compact_support
    [NormedSpace 𝕜 E] (L : F ->L[𝕜] G ->L[𝕜] E)
    {f : X -> Y -> G} {s : Set X} {k : Set Y} {g : Y -> F}
    (hk : IsCompact k) (hf : ContinuousOn f.uncurry (s ×ˢ univ))
    (hfs : forall p, forall x, p in s -> x ∉ k -> f p x = 0) (hg : IntegrableOn g k μ) :
    ContinuousOn (fun x => ∫ y, L (g y) (f x y) ∂μ) s := by
  have A : forall p in s, Continuous (f p) := fun p hp => by
    refine hf.comp_continuous (.prodMk_right _) fun y => ?_
    simpa only [prodMk_mem_set_prod_eq, mem_univ, and_true] using hp
  intro q hq
  apply Metric.continuousWithinAt_iff'.2 (fun ε εpos => ?_)
  obtain ⟨δ, δpos, hδ⟩ : exists (δ : Real), 0 < δ ∧ ∫ x in k, ‖L‖ * ‖g x‖ * δ ∂μ < ε := by
    simpa [integral_mul_const] using exists_pos_mul_lt εpos _
  obtain ⟨v, v_mem, hv⟩ : exists v in 𝓝[s] q, forall p in v, forall x in k, dist (f p x) (f q x) < δ :=
    hk.mem_uniformity_of_prod
      (hf.mono (Set.prod_mono_right (subset_univ k))) hq (dist_mem_uniformity δpos)
  simp_rw [dist_eq_norm] at hv ⊢
  have I : forall p in s, IntegrableOn (fun y => L (g y) (f p y)) k μ := by
    intro p hp
    obtain ⟨C, hC⟩ : exists C, forall y, ‖f p y‖ <= C := by
      have : ContinuousOn (f p) k := by
        have : ContinuousOn (fun y => (p, y)) k := by fun_prop
        exact hf.comp this (by simp [MapsTo, hp])
      rcases IsCompact.exists_bound_of_continuousOn hk this with ⟨C, hC⟩
      refine ⟨max C 0, fun y => ?_⟩
      by_cases hx : y in k
      · exact (hC y hx).trans (le_max_left _ _)
      · simp [hfs p y hp hx]
    have : IntegrableOn (fun y => ‖L‖ * ‖g y‖ * C) k μ :=
      (hg.norm.const_mul _).mul_const _
    apply Integrable.mono' this ?_ ?_
    · borelize G
      apply L.aestronglyMeasurable_comp₂ hg.aestronglyMeasurable
      apply StronglyMeasurable.aestronglyMeasurable
      apply Continuous.stronglyMeasurable_of_support_subset_isCompact (A p hp) hk
      apply support_subset_iff'.2 (fun y hy => hfs p y hp hy)
    · apply Eventually.of_forall (fun y => (le_opNorm₂ L (g y) (f p y)).trans ?_)
      gcongr
      apply hC
  filter_upwards [v_mem, self_mem_nhdsWithin] with p hp h'p
  calc
  ‖∫ x, L (g x) (f p x) ∂μ - ∫ x, L (g x) (f q x) ∂μ‖
    = ‖∫ x in k, L (g x) (f p x) ∂μ - ∫ x in k, L (g x) (f q x) ∂μ‖ := by
      congr 2
      · refine (setIntegral_eq_integral_of_forall_compl_eq_zero (fun y hy => ?_)).symm
        simp [hfs p y h'p hy]
      · refine (setIntegral_eq_integral_of_forall_compl_eq_zero (fun y hy => ?_)).symm
        simp [hfs q y hq hy]
  _ = ‖∫ x in k, L (g x) (f p x) - L (g x) (f q x) ∂μ‖ := by rw [integral_sub (I p h'p) (I q hq)]
  _ <= ∫ x in k, ‖L (g x) (f p x) - L (g x) (f q x)‖ ∂μ := norm_integral_le_integral_norm _
  _ <= ∫ x in k, ‖L‖ * ‖g x‖ * δ ∂μ := by
      apply integral_mono_of_nonneg (Eventually.of_forall (fun y => by positivity))
      · exact (hg.norm.const_mul _).mul_const _
      · filter_upwards with y
        by_cases hy : y in k
        · specialize hv p hp y hy
          calc
          ‖L (g y) (f p y) - L (g y) (f q y)‖
            = ‖L (g y) (f p y - f q y)‖ := by simp only [map_sub]
          _ <= ‖L‖ * ‖g y‖ * ‖f p y - f q y‖ := le_opNorm₂ _ _ _
          _ <= ‖L‖ * ‖g y‖ * δ := by gcongr
        · simp only [hfs p y h'p hy, hfs q y hq hy, sub_self, norm_zero]
          positivity
  _ < ε := hδ

/--
lemma `continuousOn_integral_of_compact_support` / 引理 `continuousOn_integral_of_compact_support`

English:
lemma continuousOn_integral_of_compact_support
  proof: by
  simpa using continuousOn_integral_bilinear_of_locally_integrable_of_compact_support (lsmul Real Real)
    hk hf hfs (integrableOn_const hk.measure_ne_top) (g := fun _ => 1)

中文:
引理 continuousOn_integral_of_compact_support
  证明: by
  simpa using continuousOn_integral_bilinear_of_locally_integrable_of_compact_support (lsmul Real Real)
    hk hf hfs (integrableOn_const hk.measure_ne_top) (g := fun _ => 1)

Depends on / 依赖: continuousOn_integral_bilinear_of_locally_integrable_of_compact_support, hk.measure_ne_top, integrableOn_const, measure_ne_top
-/
lemma continuousOn_integral_of_compact_support
    {f : X -> Y -> E} {s : Set X} {k : Set Y} [IsFiniteMeasureOnCompacts μ]
    (hk : IsCompact k) (hf : ContinuousOn f.uncurry (s ×ˢ univ))
    (hfs : forall p, forall x, p in s -> x ∉ k -> f p x = 0) :
    ContinuousOn (fun x => ∫ y, f x y ∂μ) s := by
  simpa using continuousOn_integral_bilinear_of_locally_integrable_of_compact_support (lsmul Real Real)
    hk hf hfs (integrableOn_const hk.measure_ne_top) (g := fun _ => 1)

end ParametricIntegral
