/-
Copyright (c) 2025 Oliver Butterley. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley, Yoh Tanimoto
-/
module

public import Mathlib.MeasureTheory.VectorMeasure.Basic
public import Mathlib.Order.Partition.Finpartition

/-!
# Pre-variation of a subadditive set function

Given a σ-subadditive `ℝ≥0∞`-valued set function `f`, we define the pre-variation as the supremum
over finite measurable partitions of the sum of `f` on the parts. This construction yields a
measure.

## Main definitions

* `IsSigmaSubadditiveSetFun f`: `f` is σ-subadditive on measurable sets
* `ennrealPreVariation f`: the `VectorMeasure X ℝ≥0∞` built from a σ-subadditive function
* `preVariation f`: the `Measure X` built from a σ-subadditive function

## References

* [Walter Rudin, Real and Complex Analysis.][Rud87]

-/

@[expose] public section

variable {X : Type*} [MeasurableSpace X]

open NNReal ENNReal Function

namespace MeasureTheory

/-!
## Pre-variation of a subadditive `ℝ≥0∞`-valued function

Given a set function `f : Set X → ℝ≥0∞` we can define another set function by taking the supremum
over all finite partitions of measurable sets `E i` of the sum of `∑ i, f (E i)`. If `f` is
σ-subadditive then the function defined is an `ℝ≥0∞`-valued measure.
-/

section

variable (f : Set X -> Real>=0∞)

open scoped Classical in
/--
Definition of `preVariationFun` / `preVariationFun` 的定义

English:
definition preVariationFun
  signature: (s : Set X)
  body: if h : MeasurableSet s then
    ⨆ (P : Finpartition (⟨s, h⟩ : Subtype MeasurableSet)), ∑ p in P.parts, f p
  else 0

中文:
定义 preVariationFun
  签名: (s : 集合 X)
  定义体: if h : MeasurableSet s then
    ⨆ (P : Finpartition (⟨s, h⟩ : Subtype MeasurableSet)), ∑ p in P.parts, f p
  else 0

Depends on / 依赖: Finpartition, MeasurableSet, P.parts, Subtype
-/
noncomputable def preVariationFun (s : Set X) : Real>=0∞ :=
  if h : MeasurableSet s then
    ⨆ (P : Finpartition (⟨s, h⟩ : Subtype MeasurableSet)), ∑ p in P.parts, f p
  else 0

/--
lemma `preVariationFun_apply` / 引理 `preVariationFun_apply`

English:
lemma preVariationFun_apply
  given: {s : Set X} (h : MeasurableSet s)
  proof: by
  simp [preVariationFun, h]

中文:
引理 preVariationFun_apply
  条件: {s : 集合 X} (h : 可测集 s)
  证明: by
  simp [preVariationFun, h]

Depends on / 依赖: preVariationFun
-/
lemma preVariationFun_apply {s : Set X} (h : MeasurableSet s) :
    preVariationFun f s =
      ⨆ (P : Finpartition (⟨s, h⟩ : Subtype MeasurableSet)), ∑ p in P.parts, f p := by
  simp [preVariationFun, h]

/--
lemma `preVariationFun_of_not_measurableSet` / 引理 `preVariationFun_of_not_measurableSet`

English:
lemma preVariationFun_of_not_measurableSet
  given: {s : Set X} (h : ¬ MeasurableSet s)
  proof: by
  simp [preVariationFun, h]

中文:
引理 preVariationFun_of_not_measurableSet
  条件: {s : 集合 X} (h : ¬ 可测集 s)
  证明: by
  simp [preVariationFun, h]

Depends on / 依赖: preVariationFun
-/
lemma preVariationFun_of_not_measurableSet {s : Set X} (h : ¬ MeasurableSet s) :
    preVariationFun f s = 0 := by
  simp [preVariationFun, h]

end

namespace preVariation

variable (f : Set X -> Real>=0∞)

/--
lemma `empty` / 引理 `empty`

English:
lemma empty
  statement: preVariationFun f ∅ = 0
  proof: by simp [preVariationFun]

@[simp]

中文:
引理 empty
  结论: preVariationFun f ∅ = 0
  证明: by simp [preVariationFun]

@[simp]

Depends on / 依赖: preVariationFun
-/
lemma empty : preVariationFun f ∅ = 0 := by simp [preVariationFun]

@[simp]
/--
lemma `zero` / 引理 `zero`

English:
lemma zero
  statement: preVariationFun (0 : Set X -> Real>=0∞) = 0
  proof: by ext; simp [preVariationFun]

中文:
引理 zero
  结论: preVariationFun (0 : 集合 X -> 实数>=0∞) = 0
  证明: by ext; simp [preVariationFun]

Depends on / 依赖: preVariationFun
-/
lemma zero : preVariationFun (0 : Set X -> Real>=0∞) = 0 := by ext; simp [preVariationFun]

/--
lemma `sum_le` / 引理 `sum_le`

English:
lemma sum_le
  statement: {s : Set X} (hs : MeasurableSet s)
  proof: by
  simpa [preVariationFun, hs, le_iSup_iff] using fun _ a => a P

中文:
引理 sum_le
  结论: {s : 集合 X} (hs : 可测集 s)
  证明: by
  simpa [preVariationFun, hs, le_iSup_iff] using fun _ a => a P

Depends on / 依赖: le_iSup_iff, preVariationFun
-/
lemma sum_le {s : Set X} (hs : MeasurableSet s)
    (P : Finpartition (⟨s, hs⟩ : Subtype MeasurableSet)) :
    ∑ p in P.parts, f p <= preVariationFun f s := by
  simpa [preVariationFun, hs, le_iSup_iff] using fun _ a => a P

/--
Definition of `_root_.Finpartition.toMeasurableSet` / `_root_.Finpartition.toMeasurableSet` 的定义

English:
abbreviation _root_.Finpartition.toMeasurableSet
  signature: {s : Set X} (P : Finpartition s)
  body: P.toSubtype (by measurability) (by measurability) (by measurability) hs hP

中文:
缩写 _root_.有限分拆.toMeasurableSet
  签名: {s : 集合 X} (P : 有限分拆 s)
  定义体: P.toSubtype (by measurability) (by measurability) (by measurability) hs hP

Depends on / 依赖: P.toSubtype, measurability, toSubtype
-/
noncomputable abbrev _root_.Finpartition.toMeasurableSet {s : Set X} (P : Finpartition s)
    (hs : MeasurableSet s) (hP : forall p in P.parts, MeasurableSet p) :
    Finpartition (⟨s, hs⟩ : Subtype MeasurableSet) :=
  P.toSubtype (by measurability) (by measurability) (by measurability) hs hP

/--
lemma `sum_le'` / 引理 `sum_le'`

English:
lemma sum_le'
  statement: {s : Set X} (hs : MeasurableSet s)
  proof: by
  simp only [P.sum_eq_sum_finpartition_subtype (by measurability) (by measurability)
    (by measurability) hs hP f, sum_le f hs (P.toMeasurableSet hs hP)]

中文:
引理 sum_le'
  结论: {s : 集合 X} (hs : 可测集 s)
  证明: by
  simp only [P.sum_eq_sum_finpartition_subtype (by measurability) (by measurability)
    (by measurability) hs hP f, sum_le f hs (P.toMeasurableSet hs hP)]

Depends on / 依赖: P.sum_eq_sum_finpartition_subtype, P.toMeasurableSet, measurability, sum_eq_sum_finpartition_subtype, sum_le, toMeasurableSet
-/
lemma sum_le' {s : Set X} (hs : MeasurableSet s)
    (P : Finpartition s) (hP : forall p in P.parts, MeasurableSet p) :
    ∑ p in P.parts, f p <= preVariationFun f s := by
  simp only [P.sum_eq_sum_finpartition_subtype (by measurability) (by measurability)
    (by measurability) hs hP f, sum_le f hs (P.toMeasurableSet hs hP)]

/--
lemma `sum_le_preVariationFun_of_subset` / 引理 `sum_le_preVariationFun_of_subset`

English:
lemma sum_le_preVariationFun_of_subset
  statement: {s₁ s₂ : Set X} (hs₁ : MeasurableSet s₁)
  proof: by
  calc
    ∑ p in P.parts, f p <= ∑ p in (P.extendOfLE h).parts, f p :=
      Finset.sum_le_sum_of_subset (P.parts_subset_extendOfLE h)
    _ <= preVariationFun f s₂ := sum_le f hs₂ _

中文:
引理 sum_le_preVariationFun_of_subset
  结论: {s₁ s₂ : 集合 X} (hs₁ : 可测集 s₁)
  证明: by
  calc
    ∑ p in P.parts, f p <= ∑ p in (P.extendOfLE h).parts, f p :=
      Finset.sum_le_sum_of_subset (P.parts_subset_extendOfLE h)
    _ <= preVariationFun f s₂ := sum_le f hs₂ _

Depends on / 依赖: Finset, Finset.sum_le_sum_of_subset, P.extendOfLE, P.parts, P.parts_subset_extendOfLE, extendOfLE, parts_subset_extendOfLE, preVariationFun, sum_le, sum_le_sum_of_subset
-/
lemma sum_le_preVariationFun_of_subset {s₁ s₂ : Set X} (hs₁ : MeasurableSet s₁)
    (hs₂ : MeasurableSet s₂) (h : s₁ subseteq s₂) (P : Finpartition (⟨s₁, hs₁⟩ : Subtype MeasurableSet)) :
    ∑ p in P.parts, f p <= preVariationFun f s₂ := by
  calc
    ∑ p in P.parts, f p <= ∑ p in (P.extendOfLE h).parts, f p :=
      Finset.sum_le_sum_of_subset (P.parts_subset_extendOfLE h)
    _ <= preVariationFun f s₂ := sum_le f hs₂ _

/--
lemma `mono` / 引理 `mono`

English:
lemma mono
  given: {s₁ s₂ : Set X} (hs₂ : MeasurableSet s₂) (h : s₁ subseteq s₂)
  proof: by
  by_cases hs₁ : MeasurableSet s₁
  · have := sum_le_preVariationFun_of_subset f hs₁ hs₂ h
    simp_all [preVariationFun]
  · simp [preVariationFun, hs₁]

中文:
引理 mono
  条件: {s₁ s₂ : 集合 X} (hs₂ : 可测集 s₂) (h : s₁ subseteq s₂)
  证明: by
  by_cases hs₁ : MeasurableSet s₁
  · have := sum_le_preVariationFun_of_subset f hs₁ hs₂ h
    simp_all [preVariationFun]
  · simp [preVariationFun, hs₁]

Depends on / 依赖: MeasurableSet, preVariationFun, sum_le_preVariationFun_of_subset
-/
lemma mono {s₁ s₂ : Set X} (hs₂ : MeasurableSet s₂) (h : s₁ subseteq s₂) :
    preVariationFun f s₁ <= preVariationFun f s₂ := by
  by_cases hs₁ : MeasurableSet s₁
  · have := sum_le_preVariationFun_of_subset f hs₁ hs₂ h
    simp_all [preVariationFun]
  · simp [preVariationFun, hs₁]

/--
lemma `exists_Finpartition_sum_gt` / 引理 `exists_Finpartition_sum_gt`

English:
lemma exists_Finpartition_sum_gt
  statement: {s : Set X} (hs : MeasurableSet s) {a : Real>=0∞}
  proof: by
  simp_all [preVariationFun, lt_iSup_iff]

中文:
引理 存在_Finpartition_sum_gt
  结论: {s : 集合 X} (hs : 可测集 s) {a : 实数>=0∞}
  证明: by
  simp_all [preVariationFun, lt_iSup_iff]

Depends on / 依赖: lt_iSup_iff, preVariationFun
-/
lemma exists_Finpartition_sum_gt {s : Set X} (hs : MeasurableSet s) {a : Real>=0∞}
    (ha : a < preVariationFun f s) : exists P : Finpartition (⟨s, hs⟩ : Subtype MeasurableSet),
    a < ∑ p in P.parts, f p := by
  simp_all [preVariationFun, lt_iSup_iff]

/--
lemma `exists_Finpartition_sum_ge` / 引理 `exists_Finpartition_sum_ge`

English:
lemma exists_Finpartition_sum_ge
  statement: {s : Set X} (hs : MeasurableSet s) {ε : Real>=0} (hε : 0 < ε)
  proof: by
  let ε' := min ε (preVariationFun f s).toNNReal
  have hε' : ε' <= preVariationFun f s := by simp_all [ε']
  have : ε' <= ε := by simp_all [ε']
  obtain hw | hw : preVariationFun f s != 0 ∨ preVariationFun f s = 0 := ne_or_eq _ _
  · have : 0 < ε' := by
      simp only [lt_inf_iff, ε']
      exact ⟨hε, toNNReal_pos hw h⟩
    let a := preVariationFun f s - ε'
    have ha : a < preVariationFun f s := ENNReal.sub_lt_self h hw (by positivity)
    obtain ⟨P, hP⟩ := exists_Finpartition_sum_gt f hs ha
    use P
    calc preVariationFun f s
      _ = a + ε' := (tsub_add_cancel_of_le hε').symm
      _ <= ∑ p in P.parts, f p + ε' := by
        exact (ENNReal.add_le_add_iff_right coe_ne_top).mpr (le_of_lt hP)
      _ <= ∑ p in P.parts, f p + ε := by gcongr
  · simp [*]

中文:
引理 存在_Finpartition_sum_ge
  结论: {s : 集合 X} (hs : 可测集 s) {ε : 实数>=0} (hε : 0 < ε)
  证明: by
  let ε' := min ε (preVariationFun f s).toNNReal
  have hε' : ε' <= preVariationFun f s := by simp_all [ε']
  have : ε' <= ε := by simp_all [ε']
  obtain hw | hw : preVariationFun f s != 0 ∨ preVariationFun f s = 0 := ne_or_eq _ _
  · have : 0 < ε' := by
      simp only [lt_inf_iff, ε']
      exact ⟨hε, toNNReal_pos hw h⟩
    let a := preVariationFun f s - ε'
    have ha : a < preVariationFun f s := ENNReal.sub_lt_self h hw (by positivity)
    obtain ⟨P, hP⟩ := exists_Finpartition_sum_gt f hs ha
    use P
    calc preVariationFun f s
      _ = a + ε' := (tsub_add_cancel_of_le hε').symm
      _ <= ∑ p in P.parts, f p + ε' := by
        exact (ENNReal.add_le_add_iff_right coe_ne_top).mpr (le_of_lt hP)
      _ <= ∑ p in P.parts, f p + ε := by gcongr
  · simp [*]

Depends on / 依赖: ENNReal, ENNReal.sub_lt_self, exists_Finpartition_sum_gt, lt_inf_iff, ne_or_eq, preVariationFun, sub_lt_self, toNNReal, toNNReal_pos
-/
lemma exists_Finpartition_sum_ge {s : Set X} (hs : MeasurableSet s) {ε : Real>=0} (hε : 0 < ε)
    (h : preVariationFun f s != ∞) :
    exists P : Finpartition (⟨s, hs⟩ : Subtype MeasurableSet),
    preVariationFun f s <= ∑ p in P.parts, f p + ε := by
  let ε' := min ε (preVariationFun f s).toNNReal
  have hε' : ε' <= preVariationFun f s := by simp_all [ε']
  have : ε' <= ε := by simp_all [ε']
  obtain hw | hw : preVariationFun f s != 0 ∨ preVariationFun f s = 0 := ne_or_eq _ _
  · have : 0 < ε' := by
      simp only [lt_inf_iff, ε']
      exact ⟨hε, toNNReal_pos hw h⟩
    let a := preVariationFun f s - ε'
    have ha : a < preVariationFun f s := ENNReal.sub_lt_self h hw (by positivity)
    obtain ⟨P, hP⟩ := exists_Finpartition_sum_gt f hs ha
    use P
    calc preVariationFun f s
      _ = a + ε' := (tsub_add_cancel_of_le hε').symm
      _ <= ∑ p in P.parts, f p + ε' := by
        exact (ENNReal.add_le_add_iff_right coe_ne_top).mpr (le_of_lt hP)
      _ <= ∑ p in P.parts, f p + ε := by gcongr
  · simp [*]

/--
lemma `exists_Finpartition_sum_ge'` / 引理 `exists_Finpartition_sum_ge'`

English:
lemma exists_Finpartition_sum_ge'
  statement: {s : Set X} (hs : MeasurableSet s) {ε : Real>=0∞} (hε : 0 < ε)
  proof: by
  rcases eq_top_or_lt_top ε with rfl | h'ε
  · simp
  lift ε to NNReal using h'ε.ne
  exact exists_Finpartition_sum_ge _ hs (by simpa using hε) h

中文:
引理 存在_Finpartition_sum_ge'
  结论: {s : 集合 X} (hs : 可测集 s) {ε : 实数>=0∞} (hε : 0 < ε)
  证明: by
  rcases eq_top_or_lt_top ε with rfl | h'ε
  · simp
  lift ε to NNReal using h'ε.ne
  exact exists_Finpartition_sum_ge _ hs (by simpa using hε) h

Depends on / 依赖: NNReal, eq_top_or_lt_top, exists_Finpartition_sum_ge
-/
lemma exists_Finpartition_sum_ge' {s : Set X} (hs : MeasurableSet s) {ε : Real>=0∞} (hε : 0 < ε)
    (h : preVariationFun f s != ∞) :
    exists P : Finpartition (⟨s, hs⟩ : Subtype MeasurableSet),
    preVariationFun f s <= ∑ p in P.parts, f p + ε := by
  rcases eq_top_or_lt_top ε with rfl | h'ε
  · simp
  lift ε to NNReal using h'ε.ne
  exact exists_Finpartition_sum_ge _ hs (by simpa using hε) h

/--
lemma `sum_le_preVariationFun_iUnion'` / 引理 `sum_le_preVariationFun_iUnion'`

English:
lemma sum_le_preVariationFun_iUnion'
  statement: {s : Nat -> Set X} (hs : forall i, MeasurableSet (s i))
  proof: by
  let s' (i : Nat) : Subtype MeasurableSet := ⟨s i, hs i⟩
  have hs_disj : Set.PairwiseDisjoint (Finset.range n : Set Nat) s' := fun i _ j _ hij => by
    simp only [Function.onFun, disjoint_iff, Subtype.ext_iff]
    exact Set.disjoint_iff_inter_eq_empty.mp (hs' hij)
  let Q := Finpartition.combine P hs_disj.supIndep
  have hQ_le : (Finset.range n).sup s' <= ⟨⋃ i, s i, MeasurableSet.iUnion hs⟩ := by
    rw [← Subtype.coe_le_coe]; rw [Finset.sup_coe (Psup := by measurability)]; rw [Finset.sup_set_eq_biUnion]
    exact Set.iUnion₂_subset fun i _ => Set.subset_iUnion s i
  let R := Q.extendOfLE hQ_le
  calc ∑ i in Finset.range n, ∑ p in (P i).parts, f p
    _ = ∑ p in Q.parts, f p := (Finpartition.sum_combine P hs_disj.supIndep (fun p => f p)).symm
    _ <= ∑ p in R.parts, f p := Finset.sum_le_sum_of_subset (Q.parts_subset_extendOfLE hQ_le)
    _ <= preVariationFun f (⋃ i, s i) := sum_le f (MeasurableSet.iUnion hs) R

中文:
引理 sum_le_preVariationFun_iUnion'
  结论: {s : 自然数 -> 集合 X} (hs : 对任意 i, 可测集 (s i))
  证明: by
  let s' (i : Nat) : Subtype MeasurableSet := ⟨s i, hs i⟩
  have hs_disj : Set.PairwiseDisjoint (Finset.range n : Set Nat) s' := fun i _ j _ hij => by
    simp only [Function.onFun, disjoint_iff, Subtype.ext_iff]
    exact Set.disjoint_iff_inter_eq_empty.mp (hs' hij)
  let Q := Finpartition.combine P hs_disj.supIndep
  have hQ_le : (Finset.range n).sup s' <= ⟨⋃ i, s i, MeasurableSet.iUnion hs⟩ := by
    rw [← Subtype.coe_le_coe]; rw [Finset.sup_coe (Psup := by measurability)]; rw [Finset.sup_set_eq_biUnion]
    exact Set.iUnion₂_subset fun i _ => Set.subset_iUnion s i
  let R := Q.extendOfLE hQ_le
  calc ∑ i in Finset.range n, ∑ p in (P i).parts, f p
    _ = ∑ p in Q.parts, f p := (Finpartition.sum_combine P hs_disj.supIndep (fun p => f p)).symm
    _ <= ∑ p in R.parts, f p := Finset.sum_le_sum_of_subset (Q.parts_subset_extendOfLE hQ_le)
    _ <= preVariationFun f (⋃ i, s i) := sum_le f (MeasurableSet.iUnion hs) R

Depends on / 依赖: Finpartition, Finpartition.combine, Finset, Finset.range, Finset.sup_coe, Finset.sup_set_eq_biUnion, Function, Function.onFun, MeasurableSet, MeasurableSet.iUnion, PairwiseDisjoint, Set.PairwiseDisjoint, Set.disjoint_iff_inter_eq_empty.mp, Subtype, Subtype.coe_le_coe, Subtype.ext_iff, coe_le_coe, combine, disjoint_iff, disjoint_iff_inter_eq_empty
-/
lemma sum_le_preVariationFun_iUnion' {s : Nat -> Set X} (hs : forall i, MeasurableSet (s i))
    (hs' : Pairwise (Disjoint on s))
    (P : forall (i : Nat), Finpartition (⟨s i, hs i⟩ : Subtype MeasurableSet)) (n : Nat) :
    ∑ i in Finset.range n, ∑ p in (P i).parts, f p <= preVariationFun f (⋃ i, s i) := by
  let s' (i : Nat) : Subtype MeasurableSet := ⟨s i, hs i⟩
  have hs_disj : Set.PairwiseDisjoint (Finset.range n : Set Nat) s' := fun i _ j _ hij => by
    simp only [Function.onFun, disjoint_iff, Subtype.ext_iff]
    exact Set.disjoint_iff_inter_eq_empty.mp (hs' hij)
  let Q := Finpartition.combine P hs_disj.supIndep
  have hQ_le : (Finset.range n).sup s' <= ⟨⋃ i, s i, MeasurableSet.iUnion hs⟩ := by
    rw [← Subtype.coe_le_coe]; rw [Finset.sup_coe (Psup := by measurability)]; rw [Finset.sup_set_eq_biUnion]
    exact Set.iUnion₂_subset fun i _ => Set.subset_iUnion s i
  let R := Q.extendOfLE hQ_le
  calc ∑ i in Finset.range n, ∑ p in (P i).parts, f p
    _ = ∑ p in Q.parts, f p := (Finpartition.sum_combine P hs_disj.supIndep (fun p => f p)).symm
    _ <= ∑ p in R.parts, f p := Finset.sum_le_sum_of_subset (Q.parts_subset_extendOfLE hQ_le)
    _ <= preVariationFun f (⋃ i, s i) := sum_le f (MeasurableSet.iUnion hs) R

/--
lemma `sum_le_preVariationFun_iUnion` / 引理 `sum_le_preVariationFun_iUnion`

English:
lemma sum_le_preVariationFun_iUnion
  statement: {s : Nat -> Set X} (hs : forall i, MeasurableSet (s i))
  proof: by
  refine ENNReal.tsum_le_of_sum_range_le fun n => ?_
  by_cases hn : n = 0
  · simp [hn]
  refine ENNReal.le_of_forall_pos_le_add fun ε' hε' hsnetop => ?_
  let ε := ε' / n
  have hε : 0 < ε := by positivity
have hs'' i : preVariationFun f (s i) != ⊤ := lt_top_iff_ne_top.mp
    (mono f (MeasurableSet.iUnion hs) (Set.subset_iUnion s i)).trans_lt hsnetop
  -- For each set `s i` we choose a Finpartition `P i` such that, for each `i`,
  -- `preVariationFun f (s i) ≤ ∑ p ∈ (P i), f p + ε`.
  choose P hP using fun i => exists_Finpartition_sum_ge f (hs i) (hε) (hs'' i)
  calc ∑ i in Finset.range n, preVariationFun f (s i)
    _ <= ∑ i in Finset.range n, (∑ p in (P i).parts, f p + ε) := Finset.sum_le_sum fun i _ => hP i
    _ = ∑ i in Finset.range n, ∑ p in (P i).parts, f p + ε' := by
      rw [Finset.sum_add_distrib]; norm_cast
      simp [show n * ε = ε' by field]
    _ <= preVariationFun f (⋃ i, s i) + ε' := by
      gcongr; exact sum_le_preVariationFun_iUnion' f hs hs' P n

中文:
引理 sum_le_preVariationFun_iUnion
  结论: {s : 自然数 -> 集合 X} (hs : 对任意 i, 可测集 (s i))
  证明: by
  refine ENNReal.tsum_le_of_sum_range_le fun n => ?_
  by_cases hn : n = 0
  · simp [hn]
  refine ENNReal.le_of_forall_pos_le_add fun ε' hε' hsnetop => ?_
  let ε := ε' / n
  have hε : 0 < ε := by positivity
have hs'' i : preVariationFun f (s i) != ⊤ := lt_top_iff_ne_top.mp
    (mono f (MeasurableSet.iUnion hs) (Set.subset_iUnion s i)).trans_lt hsnetop
  -- For each set `s i` we choose a Finpartition `P i` such that, for each `i`,
  -- `preVariationFun f (s i) ≤ ∑ p ∈ (P i), f p + ε`.
  choose P hP using fun i => exists_Finpartition_sum_ge f (hs i) (hε) (hs'' i)
  calc ∑ i in Finset.range n, preVariationFun f (s i)
    _ <= ∑ i in Finset.range n, (∑ p in (P i).parts, f p + ε) := Finset.sum_le_sum fun i _ => hP i
    _ = ∑ i in Finset.range n, ∑ p in (P i).parts, f p + ε' := by
      rw [Finset.sum_add_distrib]; norm_cast
      simp [show n * ε = ε' by field]
    _ <= preVariationFun f (⋃ i, s i) + ε' := by
      gcongr; exact sum_le_preVariationFun_iUnion' f hs hs' P n

Depends on / 依赖: ENNReal, ENNReal.le_of_forall_pos_le_add, ENNReal.tsum_le_of_sum_range_le, MeasurableSet, MeasurableSet.iUnion, Set.subset_iUnion, hsnetop, iUnion, le_of_forall_pos_le_add, lt_top_iff_ne_top, lt_top_iff_ne_top.mp, preVariationFun, subset_iUnion, trans_lt, tsum_le_of_sum_range_le
-/
lemma sum_le_preVariationFun_iUnion {s : Nat -> Set X} (hs : forall i, MeasurableSet (s i))
    (hs' : Pairwise (Disjoint on s)) :
    ∑' i, preVariationFun f (s i) <= preVariationFun f (⋃ i, s i) := by
  refine ENNReal.tsum_le_of_sum_range_le fun n => ?_
  by_cases hn : n = 0
  · simp [hn]
  refine ENNReal.le_of_forall_pos_le_add fun ε' hε' hsnetop => ?_
  let ε := ε' / n
  have hε : 0 < ε := by positivity
have hs'' i : preVariationFun f (s i) != ⊤ := lt_top_iff_ne_top.mp
    (mono f (MeasurableSet.iUnion hs) (Set.subset_iUnion s i)).trans_lt hsnetop
  -- For each set `s i` we choose a Finpartition `P i` such that, for each `i`,
  -- `preVariationFun f (s i) ≤ ∑ p ∈ (P i), f p + ε`.
  choose P hP using fun i => exists_Finpartition_sum_ge f (hs i) (hε) (hs'' i)
  calc ∑ i in Finset.range n, preVariationFun f (s i)
    _ <= ∑ i in Finset.range n, (∑ p in (P i).parts, f p + ε) := Finset.sum_le_sum fun i _ => hP i
    _ = ∑ i in Finset.range n, ∑ p in (P i).parts, f p + ε' := by
      rw [Finset.sum_add_distrib]; norm_cast
      simp [show n * ε = ε' by field]
    _ <= preVariationFun f (⋃ i, s i) + ε' := by
      gcongr; exact sum_le_preVariationFun_iUnion' f hs hs' P n

end preVariation

/--
Definition of `IsSigmaSubadditiveSetFun` / `IsSigmaSubadditiveSetFun` 的定义

English:
definition IsSigmaSubadditiveSetFun
  signature: (f : Set X -> Real>=0∞)
  body: forall (s : Nat -> {t : Set X // MeasurableSet t}), Pairwise (Disjoint on (Subtype.val ∘ s)) ->
    f (⋃ i, (s i).val) <= ∑' i, f (s i)

中文:
定义 IsSigmaSubadditiveSetFun
  签名: (f : 集合 X -> 实数>=0∞)
  定义体: forall (s : Nat -> {t : Set X // MeasurableSet t}), Pairwise (Disjoint on (Subtype.val ∘ s)) ->
    f (⋃ i, (s i).val) <= ∑' i, f (s i)

Depends on / 依赖: Disjoint, MeasurableSet, Pairwise, Subtype, Subtype.val
-/
def IsSigmaSubadditiveSetFun (f : Set X -> Real>=0∞) : Prop :=
  forall (s : Nat -> {t : Set X // MeasurableSet t}), Pairwise (Disjoint on (Subtype.val ∘ s)) ->
    f (⋃ i, (s i).val) <= ∑' i, f (s i)

/--
lemma `isSigmaSubadditiveSetFun_zero` / 引理 `isSigmaSubadditiveSetFun_zero`

English:
lemma isSigmaSubadditiveSetFun_zero
  statement: IsSigmaSubadditiveSetFun (0 : Set X -> Real>=0∞)
  proof: by intro; simp

中文:
引理 isSigmaSubadditiveSetFun_zero
  结论: IsSigmaSubadditiveSetFun (0 : 集合 X -> 实数>=0∞)
  证明: by intro; simp
-/
lemma isSigmaSubadditiveSetFun_zero : IsSigmaSubadditiveSetFun (0 : Set X -> Real>=0∞) := by intro; simp

namespace preVariation

variable {f : Set X -> Real>=0∞}

/--
lemma `iUnion` / 引理 `iUnion`

English:
lemma iUnion
  statement: (hf : IsSigmaSubadditiveSetFun f) (hf' : f ∅ = 0) (s : Nat -> Set X)
  proof: by
  refine ENNReal.summable.hasSum_iff.mpr (le_antisymm (sum_le_preVariationFun_iUnion f hs hs') ?_)
  refine ENNReal.le_tsum_of_forall_lt_exists_sum fun b hb => ?_
  simp only [preVariationFun, MeasurableSet.iUnion hs, reduceDIte, lt_iSup_iff] at hb
  obtain ⟨Q, hQ⟩ := hb
  let s' (i : Nat) : Subtype MeasurableSet := ⟨s i, hs i⟩
  let P (i : Nat) := Q.restrict (b := s' i) (Set.subset_iUnion s i)
  have splitting : ∑ q in Q.parts, f q <= ∑' i, ∑ p in (P i).parts, f p := by
    calc ∑ q in Q.parts, f q
      _ <= ∑ q in Q.parts, ∑' i, f (q ⊓ s' i) := by
          apply Finset.sum_le_sum fun q hq => ?_
          have hq_eq : q.val = ⋃ i, q.val inter s i := by
            rw [← Set.inter_iUnion]; exact (Set.inter_eq_left.mpr (Q.le hq)).symm
          let t (i : Nat) : Subtype MeasurableSet := ⟨q.val inter s i, q.2.inter (hs i)⟩
          have ht_disj : Pairwise (Disjoint on (Subtype.val ∘ t)) :=
            fun i j hij => (hs' hij).mono Set.inter_subset_right Set.inter_subset_right
          calc f q
            _ = f (⋃ i, q.val inter s i) := congrArg f hq_eq
            _ = f (⋃ i, (t i).val) := rfl
            _ <= ∑' i, f (t i) := hf t ht_disj
            _ = ∑' i, f (q ⊓ s' i) := rfl
      _ = ∑' i, ∑ q in Q.parts, f (q ⊓ s' i) :=
          (Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)).symm
      _ = ∑' i, ∑ p in (P i).parts, f p := by
          congr 1; funext i
          exact (Q.sum_restrict _ (fun p => f p) hf').symm
obtain ⟨n, hn⟩ := lt_iSup_iff.mp ENNReal.tsum_eq_iSup_nat ▸ lt_of_lt_of_le hQ splitting
  have bound (i : Nat) : ∑ p in (P i).parts, f p <= preVariationFun f (s i) := sum_le f (hs i) (P i)
  exact ⟨Finset.range n, lt_of_lt_of_le hn (Finset.sum_le_sum fun i _ => bound i)⟩

中文:
引理 iUnion
  结论: (hf : IsSigmaSubadditiveSetFun f) (hf' : f ∅ = 0) (s : 自然数 -> 集合 X)
  证明: by
  refine ENNReal.summable.hasSum_iff.mpr (le_antisymm (sum_le_preVariationFun_iUnion f hs hs') ?_)
  refine ENNReal.le_tsum_of_forall_lt_exists_sum fun b hb => ?_
  simp only [preVariationFun, MeasurableSet.iUnion hs, reduceDIte, lt_iSup_iff] at hb
  obtain ⟨Q, hQ⟩ := hb
  let s' (i : Nat) : Subtype MeasurableSet := ⟨s i, hs i⟩
  let P (i : Nat) := Q.restrict (b := s' i) (Set.subset_iUnion s i)
  have splitting : ∑ q in Q.parts, f q <= ∑' i, ∑ p in (P i).parts, f p := by
    calc ∑ q in Q.parts, f q
      _ <= ∑ q in Q.parts, ∑' i, f (q ⊓ s' i) := by
          apply Finset.sum_le_sum fun q hq => ?_
          have hq_eq : q.val = ⋃ i, q.val inter s i := by
            rw [← Set.inter_iUnion]; exact (Set.inter_eq_left.mpr (Q.le hq)).symm
          let t (i : Nat) : Subtype MeasurableSet := ⟨q.val inter s i, q.2.inter (hs i)⟩
          have ht_disj : Pairwise (Disjoint on (Subtype.val ∘ t)) :=
            fun i j hij => (hs' hij).mono Set.inter_subset_right Set.inter_subset_right
          calc f q
            _ = f (⋃ i, q.val inter s i) := congrArg f hq_eq
            _ = f (⋃ i, (t i).val) := rfl
            _ <= ∑' i, f (t i) := hf t ht_disj
            _ = ∑' i, f (q ⊓ s' i) := rfl
      _ = ∑' i, ∑ q in Q.parts, f (q ⊓ s' i) :=
          (Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)).symm
      _ = ∑' i, ∑ p in (P i).parts, f p := by
          congr 1; funext i
          exact (Q.sum_restrict _ (fun p => f p) hf').symm
obtain ⟨n, hn⟩ := lt_iSup_iff.mp ENNReal.tsum_eq_iSup_nat ▸ lt_of_lt_of_le hQ splitting
  have bound (i : Nat) : ∑ p in (P i).parts, f p <= preVariationFun f (s i) := sum_le f (hs i) (P i)
  exact ⟨Finset.range n, lt_of_lt_of_le hn (Finset.sum_le_sum fun i _ => bound i)⟩

Depends on / 依赖: ENNReal, ENNReal.le_tsum_of_forall_lt_exists_sum, ENNReal.summable.hasSum_iff.mpr, MeasurableSet, MeasurableSet.iUnion, Q.parts, Q.restrict, Set.subset_iUnion, Subtype, hasSum_iff, iUnion, le_antisymm, le_tsum_of_forall_lt_exists_sum, lt_iSup_iff, preVariationFun, reduceDIte, restrict, splitting, subset_iUnion, sum_le_preVariationFun_iUnion
-/
lemma iUnion (hf : IsSigmaSubadditiveSetFun f) (hf' : f ∅ = 0) (s : Nat -> Set X)
    (hs : forall i, MeasurableSet (s i)) (hs' : Pairwise (Disjoint on s)) :
    HasSum (fun i => preVariationFun f (s i)) (preVariationFun f (⋃ i, s i)) := by
  refine ENNReal.summable.hasSum_iff.mpr (le_antisymm (sum_le_preVariationFun_iUnion f hs hs') ?_)
  refine ENNReal.le_tsum_of_forall_lt_exists_sum fun b hb => ?_
  simp only [preVariationFun, MeasurableSet.iUnion hs, reduceDIte, lt_iSup_iff] at hb
  obtain ⟨Q, hQ⟩ := hb
  let s' (i : Nat) : Subtype MeasurableSet := ⟨s i, hs i⟩
  let P (i : Nat) := Q.restrict (b := s' i) (Set.subset_iUnion s i)
  have splitting : ∑ q in Q.parts, f q <= ∑' i, ∑ p in (P i).parts, f p := by
    calc ∑ q in Q.parts, f q
      _ <= ∑ q in Q.parts, ∑' i, f (q ⊓ s' i) := by
          apply Finset.sum_le_sum fun q hq => ?_
          have hq_eq : q.val = ⋃ i, q.val inter s i := by
            rw [← Set.inter_iUnion]; exact (Set.inter_eq_left.mpr (Q.le hq)).symm
          let t (i : Nat) : Subtype MeasurableSet := ⟨q.val inter s i, q.2.inter (hs i)⟩
          have ht_disj : Pairwise (Disjoint on (Subtype.val ∘ t)) :=
            fun i j hij => (hs' hij).mono Set.inter_subset_right Set.inter_subset_right
          calc f q
            _ = f (⋃ i, q.val inter s i) := congrArg f hq_eq
            _ = f (⋃ i, (t i).val) := rfl
            _ <= ∑' i, f (t i) := hf t ht_disj
            _ = ∑' i, f (q ⊓ s' i) := rfl
      _ = ∑' i, ∑ q in Q.parts, f (q ⊓ s' i) :=
          (Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)).symm
      _ = ∑' i, ∑ p in (P i).parts, f p := by
          congr 1; funext i
          exact (Q.sum_restrict _ (fun p => f p) hf').symm
obtain ⟨n, hn⟩ := lt_iSup_iff.mp ENNReal.tsum_eq_iSup_nat ▸ lt_of_lt_of_le hQ splitting
  have bound (i : Nat) : ∑ p in (P i).parts, f p <= preVariationFun f (s i) := sum_le f (hs i) (P i)
  exact ⟨Finset.range n, lt_of_lt_of_le hn (Finset.sum_le_sum fun i _ => bound i)⟩

end preVariation

/-!
## Construction of measures from σ-subadditive functions
-/

variable (f : Set X -> Real>=0∞)

/--
Definition of `ennrealPreVariation` / `ennrealPreVariation` 的定义

English:
definition ennrealPreVariation
  signature: (hf : IsSigmaSubadditiveSetFun f) (hf' : f ∅ = 0)
  body: preVariationFun f
  empty' := preVariation.empty f
  not_measurable' _ h := by simp [preVariationFun, h]
  m_iUnion' := preVariation.iUnion hf hf'

中文:
定义 ennrealPreVariation
  签名: (hf : IsSigmaSubadditiveSetFun f) (hf' : f ∅ = 0)
  定义体: preVariationFun f
  empty' := preVariation.empty f
  not_measurable' _ h := by simp [preVariationFun, h]
  m_iUnion' := preVariation.iUnion hf hf'

Depends on / 依赖: preVariationFun
-/
noncomputable def ennrealPreVariation (hf : IsSigmaSubadditiveSetFun f) (hf' : f ∅ = 0) :
    VectorMeasure X Real>=0∞ where
  measureOf' := preVariationFun f
  empty' := preVariation.empty f
  not_measurable' _ h := by simp [preVariationFun, h]
  m_iUnion' := preVariation.iUnion hf hf'

/--
lemma `ennrealPreVariation_apply` / 引理 `ennrealPreVariation_apply`

English:
lemma ennrealPreVariation_apply
  given: (hf : IsSigmaSubadditiveSetFun f) (hf' : f ∅ = 0) (s : Set X)
  proof: rfl

@[simp]

中文:
引理 ennrealPreVariation_apply
  条件: (hf : IsSigmaSubadditiveSetFun f) (hf' : f ∅ = 0) (s : 集合 X)
  证明: rfl

@[simp]
-/
lemma ennrealPreVariation_apply (hf : IsSigmaSubadditiveSetFun f) (hf' : f ∅ = 0) (s : Set X) :
  ennrealPreVariation f hf hf' s = preVariationFun f s := rfl

@[simp]
/--
lemma `ennrealPreVariation_zero` / 引理 `ennrealPreVariation_zero`

English:
lemma ennrealPreVariation_zero
  proof: by
  ext; simp [ennrealPreVariation_apply]

中文:
引理 ennrealPreVariation_zero
  证明: by
  ext; simp [ennrealPreVariation_apply]

Depends on / 依赖: ennrealPreVariation_apply
-/
lemma ennrealPreVariation_zero :
    ennrealPreVariation (0 : Set X -> Real>=0∞) isSigmaSubadditiveSetFun_zero (by simp) = 0 := by
  ext; simp [ennrealPreVariation_apply]

/--
Definition of `preVariation` / `preVariation` 的定义

English:
definition preVariation
  signature: (hf : IsSigmaSubadditiveSetFun f) (hf' : f ∅ = 0)
  body: (ennrealPreVariation f hf hf').ennrealToMeasure

中文:
定义 preVariation
  签名: (hf : IsSigmaSubadditiveSetFun f) (hf' : f ∅ = 0)
  定义体: (ennrealPreVariation f hf hf').ennrealToMeasure

Depends on / 依赖: ennrealPreVariation, ennrealToMeasure
-/
noncomputable def preVariation (hf : IsSigmaSubadditiveSetFun f) (hf' : f ∅ = 0) : Measure X :=
  (ennrealPreVariation f hf hf').ennrealToMeasure

/--
lemma `preVariation_apply` / 引理 `preVariation_apply`

English:
lemma preVariation_apply
  given: (hf : IsSigmaSubadditiveSetFun f) (hf' : f ∅ = 0) (s : Set X)
  proof: rfl

@[simp]

中文:
引理 preVariation_apply
  条件: (hf : IsSigmaSubadditiveSetFun f) (hf' : f ∅ = 0) (s : 集合 X)
  证明: rfl

@[simp]
-/
lemma preVariation_apply (hf : IsSigmaSubadditiveSetFun f) (hf' : f ∅ = 0) (s : Set X) :
    preVariation f hf hf' s = (ennrealPreVariation f hf hf').ennrealToMeasure s := rfl

@[simp]
/--
lemma `preVariation_zero` / 引理 `preVariation_zero`

English:
lemma preVariation_zero
  proof: by
  ext; simp [preVariation_apply]

中文:
引理 preVariation_zero
  证明: by
  ext; simp [preVariation_apply]

Depends on / 依赖: preVariation_apply
-/
lemma preVariation_zero :
    preVariation (0 : Set X -> Real>=0∞) isSigmaSubadditiveSetFun_zero (by simp) = 0 := by
  ext; simp [preVariation_apply]

end MeasureTheory
