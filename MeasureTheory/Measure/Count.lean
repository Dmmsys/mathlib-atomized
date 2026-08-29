/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
module

public import Mathlib.MeasureTheory.Measure.Dirac

import Mathlib.SetTheory.Cardinal.ENNReal

/-!
# Counting measure

In this file we define the counting measure `MeasureTheory.Measure.count`
as `MeasureTheory.Measure.sum MeasureTheory.Measure.dirac`
and prove basic properties of this measure.
-/

@[expose] public section

open Set
open scoped ENNReal Finset

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {s : Set α}

noncomputable section

namespace MeasureTheory.Measure

/--
Definition of `count` / `count` 的定义

English:
definition count
  signature: : Measure α
  body: sum dirac

中文:
定义 count
  签名: : 测度 α
  定义体: sum dirac
-/
def count : Measure α :=
  sum dirac

/--
lemma `count_ne_zero''` / 引理 `count_ne_zero''`

English:
lemma count_ne_zero''
  given: [Nonempty α]
  statement: (count : Measure α) != 0
  proof: by simp [count]

中文:
引理 count_ne_zero''
  条件: [非空 α]
  结论: (count : 测度 α) != 0
  证明: by simp [count]
-/
@[simp] lemma count_ne_zero'' [Nonempty α] : (count : Measure α) != 0 := by simp [count]

/--
theorem `le_count_apply` / 定理 `le_count_apply`

English:
theorem le_count_apply
  statement: ∑' _ : s, (1 : Real>=0∞) <= count s
  proof: calc
    (∑' _ : s, 1 : Real>=0∞) = ∑' i, indicator s 1 i := tsum_subtype s 1
    _ <= ∑' i, dirac i s := ENNReal.tsum_le_tsum fun _ => le_dirac_apply
    _ <= count s := le_sum_apply _ _

中文:
定理 le_count_apply
  结论: ∑' _ : s, (1 : 实数>=0∞) <= count s
  证明: calc
    (∑' _ : s, 1 : Real>=0∞) = ∑' i, indicator s 1 i := tsum_subtype s 1
    _ <= ∑' i, dirac i s := ENNReal.tsum_le_tsum fun _ => le_dirac_apply
    _ <= count s := le_sum_apply _ _

Depends on / 依赖: ENNReal, ENNReal.tsum_le_tsum, indicator, le_dirac_apply, le_sum_apply, tsum_le_tsum, tsum_subtype
-/
theorem le_count_apply : ∑' _ : s, (1 : Real>=0∞) <= count s :=
  calc
    (∑' _ : s, 1 : Real>=0∞) = ∑' i, indicator s 1 i := tsum_subtype s 1
    _ <= ∑' i, dirac i s := ENNReal.tsum_le_tsum fun _ => le_dirac_apply
    _ <= count s := le_sum_apply _ _

/--
theorem `count_apply` / 定理 `count_apply`

English:
theorem count_apply
  given: (hs : MeasurableSet s)
  statement: count s = s.encard
  proof: by
  simp [count, hs, ← tsum_subtype]

@[simp]

中文:
定理 count_apply
  条件: (hs : 可测集 s)
  结论: count s = s.encard
  证明: by
  simp [count, hs, ← tsum_subtype]

@[simp]

Depends on / 依赖: tsum_subtype
-/
theorem count_apply (hs : MeasurableSet s) : count s = s.encard := by
  simp [count, hs, ← tsum_subtype]

@[simp]
/--
theorem `count_apply_finset'` / 定理 `count_apply_finset'`

English:
theorem count_apply_finset'
  given: {s : Finset α} (hs : MeasurableSet (s : Set α))
  proof: by simp [count_apply hs]

@[simp]

中文:
定理 count_apply_finset'
  条件: {s : 有限集 α} (hs : 可测集 (s : 集合 α))
  证明: by simp [count_apply hs]

@[simp]

Depends on / 依赖: IsUpperModularLattice, IsUpperModularLattice.to_isWeakUpperModularLattice, count_apply, to_isWeakUpperModularLattice
-/
theorem count_apply_finset' {s : Finset α} (hs : MeasurableSet (s : Set α)) :
    count (↑s : Set α) = #s := by simp [count_apply hs]

@[simp]
/--
theorem `count_apply_finset` / 定理 `count_apply_finset`

English:
theorem count_apply_finset
  given: [MeasurableSingletonClass α] (s : Finset α)
  proof: count_apply_finset' s.measurableSet

中文:
定理 count_apply_finset
  条件: [MeasurableSingleton类 α] (s : 有限集 α)
  证明: count_apply_finset' s.measurableSet

Depends on / 依赖: count_apply_finset, measurableSet, s.measurableSet
-/
theorem count_apply_finset [MeasurableSingletonClass α] (s : Finset α) :
    count (↑s : Set α) = #s :=
  count_apply_finset' s.measurableSet

/--
theorem `count_apply_finite'` / 定理 `count_apply_finite'`

English:
theorem count_apply_finite'
  given: {s : Set α} (s_fin : s.Finite) (s_mble : MeasurableSet s)
  proof: by
  simp [←
    @count_apply_finset' _ _ s_fin.toFinset (by simpa only [Finite.coe_toFinset] using s_mble)]

中文:
定理 count_apply_finite'
  条件: {s : 集合 α} (s_fin : s.有限) (s_mble : 可测集 s)
  证明: by
  simp [←
    @count_apply_finset' _ _ s_fin.toFinset (by simpa only [Finite.coe_toFinset] using s_mble)]

Depends on / 依赖: Finite, Finite.coe_toFinset, coe_toFinset, count_apply_finset, s_fin, s_fin.toFinset, s_mble, toFinset
-/
theorem count_apply_finite' {s : Set α} (s_fin : s.Finite) (s_mble : MeasurableSet s) :
    count s = #s_fin.toFinset := by
  simp [←
    @count_apply_finset' _ _ s_fin.toFinset (by simpa only [Finite.coe_toFinset] using s_mble)]

/--
theorem `count_apply_finite` / 定理 `count_apply_finite`

English:
theorem count_apply_finite
  given: [MeasurableSingletonClass α] (s : Set α) (hs : s.Finite)
  proof: by rw [← count_apply_finset, Finite.coe_toFinset]

中文:
定理 count_apply_finite
  条件: [MeasurableSingleton类 α] (s : 集合 α) (hs : s.有限)
  证明: by rw [← count_apply_finset, Finite.coe_toFinset]

Depends on / 依赖: Finite, Finite.coe_toFinset, coe_toFinset, count_apply_finset
-/
theorem count_apply_finite [MeasurableSingletonClass α] (s : Set α) (hs : s.Finite) :
    count s = #hs.toFinset := by rw [← count_apply_finset, Finite.coe_toFinset]

/--
theorem `count_apply_infinite` / 定理 `count_apply_infinite`

English:
theorem count_apply_infinite
  given: (hs : s.Infinite)
  statement: count s = ∞
  proof: by
  refine top_unique (le_of_tendsto' ENNReal.tendsto_nat_nhds_top fun n => ?_)
  rcases hs.exists_subset_card_eq n with ⟨t, ht, rfl⟩
  calc
    (#t : Real>=0∞) = ∑ i in t, 1 := by simp
    _ = ∑' i : (t : Set α), 1 := (t.tsum_subtype 1).symm
    _ <= count (t : Set α) := le_count_apply
    _ <= count s := measure_mono ht

@[simp]

中文:
定理 count_apply_infinite
  条件: (hs : s.无限)
  结论: count s = ∞
  证明: by
  refine top_unique (le_of_tendsto' ENNReal.tendsto_nat_nhds_top fun n => ?_)
  rcases hs.exists_subset_card_eq n with ⟨t, ht, rfl⟩
  calc
    (#t : Real>=0∞) = ∑ i in t, 1 := by simp
    _ = ∑' i : (t : Set α), 1 := (t.tsum_subtype 1).symm
    _ <= count (t : Set α) := le_count_apply
    _ <= count s := measure_mono ht

@[simp]

Depends on / 依赖: ENNReal, ENNReal.tendsto_nat_nhds_top, exists_subset_card_eq, hs.exists_subset_card_eq, le_count_apply, le_of_tendsto, measure_mono, t.tsum_subtype, tendsto_nat_nhds_top, top_unique, tsum_subtype
-/
theorem count_apply_infinite (hs : s.Infinite) : count s = ∞ := by
  refine top_unique (le_of_tendsto' ENNReal.tendsto_nat_nhds_top fun n => ?_)
  rcases hs.exists_subset_card_eq n with ⟨t, ht, rfl⟩
  calc
    (#t : Real>=0∞) = ∑ i in t, 1 := by simp
    _ = ∑' i : (t : Set α), 1 := (t.tsum_subtype 1).symm
    _ <= count (t : Set α) := le_count_apply
    _ <= count s := measure_mono ht

@[simp]
/--
theorem `count_apply_eq_top'` / 定理 `count_apply_eq_top'`

English:
theorem count_apply_eq_top'
  given: (s_mble : MeasurableSet s)
  statement: count s = ∞ ↔ s.Infinite
  proof: by
  by_cases hs : s.Finite
  · simp [Set.Infinite, hs, count_apply_finite' hs s_mble]
  · change s.Infinite at hs
    simp [hs, count_apply_infinite]

@[simp]

中文:
定理 count_apply_eq_top'
  条件: (s_mble : 可测集 s)
  结论: count s = ∞ ↔ s.无限
  证明: by
  by_cases hs : s.Finite
  · simp [Set.Infinite, hs, count_apply_finite' hs s_mble]
  · change s.Infinite at hs
    simp [hs, count_apply_infinite]

@[simp]

Depends on / 依赖: Finite, Infinite, Set.Infinite, count_apply_finite, count_apply_infinite, s.Finite, s.Infinite, s_mble
-/
theorem count_apply_eq_top' (s_mble : MeasurableSet s) : count s = ∞ ↔ s.Infinite := by
  by_cases hs : s.Finite
  · simp [Set.Infinite, hs, count_apply_finite' hs s_mble]
  · change s.Infinite at hs
    simp [hs, count_apply_infinite]

@[simp]
/--
theorem `count_apply_eq_top` / 定理 `count_apply_eq_top`

English:
theorem count_apply_eq_top
  given: [MeasurableSingletonClass α]
  statement: count s = ∞ ↔ s.Infinite
  proof: by
  by_cases hs : s.Finite
  · exact count_apply_eq_top' hs.measurableSet
  · change s.Infinite at hs
    simp [hs, count_apply_infinite]

@[simp]

中文:
定理 count_apply_eq_top
  条件: [MeasurableSingleton类 α]
  结论: count s = ∞ ↔ s.无限
  证明: by
  by_cases hs : s.Finite
  · exact count_apply_eq_top' hs.measurableSet
  · change s.Infinite at hs
    simp [hs, count_apply_infinite]

@[simp]

Depends on / 依赖: Finite, Infinite, count_apply_eq_top, count_apply_infinite, hs.measurableSet, measurableSet, s.Finite, s.Infinite
-/
theorem count_apply_eq_top [MeasurableSingletonClass α] : count s = ∞ ↔ s.Infinite := by
  by_cases hs : s.Finite
  · exact count_apply_eq_top' hs.measurableSet
  · change s.Infinite at hs
    simp [hs, count_apply_infinite]

@[simp]
/--
theorem `count_apply_lt_top'` / 定理 `count_apply_lt_top'`

English:
theorem count_apply_lt_top'
  given: (s_mble : MeasurableSet s)
  statement: count s < ∞ ↔ s.Finite
  proof: calc
    count s < ∞ ↔ count s != ∞ := lt_top_iff_ne_top
    _ ↔ ¬s.Infinite := not_congr (count_apply_eq_top' s_mble)
    _ ↔ s.Finite := Classical.not_not

@[simp]

中文:
定理 count_apply_lt_top'
  条件: (s_mble : 可测集 s)
  结论: count s < ∞ ↔ s.有限
  证明: calc
    count s < ∞ ↔ count s != ∞ := lt_top_iff_ne_top
    _ ↔ ¬s.Infinite := not_congr (count_apply_eq_top' s_mble)
    _ ↔ s.Finite := Classical.not_not

@[simp]

Depends on / 依赖: Classical, Classical.not_not, Finite, Infinite, count_apply_eq_top, lt_top_iff_ne_top, not_congr, not_not, s.Finite, s.Infinite, s_mble
-/
theorem count_apply_lt_top' (s_mble : MeasurableSet s) : count s < ∞ ↔ s.Finite :=
  calc
    count s < ∞ ↔ count s != ∞ := lt_top_iff_ne_top
    _ ↔ ¬s.Infinite := not_congr (count_apply_eq_top' s_mble)
    _ ↔ s.Finite := Classical.not_not

@[simp]
/--
theorem `count_apply_lt_top` / 定理 `count_apply_lt_top`

English:
theorem count_apply_lt_top
  given: [MeasurableSingletonClass α]
  statement: count s < ∞ ↔ s.Finite
  proof: calc
    count s < ∞ ↔ count s != ∞ := lt_top_iff_ne_top
    _ ↔ ¬s.Infinite := not_congr count_apply_eq_top
    _ ↔ s.Finite := Classical.not_not

@[simp]

中文:
定理 count_apply_lt_top
  条件: [MeasurableSingleton类 α]
  结论: count s < ∞ ↔ s.有限
  证明: calc
    count s < ∞ ↔ count s != ∞ := lt_top_iff_ne_top
    _ ↔ ¬s.Infinite := not_congr count_apply_eq_top
    _ ↔ s.Finite := Classical.not_not

@[simp]

Depends on / 依赖: Classical, Classical.not_not, Finite, Infinite, count_apply_eq_top, lt_top_iff_ne_top, not_congr, not_not, s.Finite, s.Infinite
-/
theorem count_apply_lt_top [MeasurableSingletonClass α] : count s < ∞ ↔ s.Finite :=
  calc
    count s < ∞ ↔ count s != ∞ := lt_top_iff_ne_top
    _ ↔ ¬s.Infinite := not_congr count_apply_eq_top
    _ ↔ s.Finite := Classical.not_not

@[simp]
/--
theorem `count_eq_zero_iff` / 定理 `count_eq_zero_iff`

English:
theorem count_eq_zero_iff
  statement: count s = 0 ↔ s = ∅ where
  proof: eq_empty_of_forall_notMem fun x hx => by
    simpa [hx] using ((ENNReal.le_tsum x).trans <| le_sum_apply _ _).trans_eq h
  mpr := by rintro rfl; exact measure_empty

中文:
定理 count_eq_zero_iff
  结论: count s = 0 ↔ s = ∅ where
  证明: eq_empty_of_forall_notMem fun x hx => by
    simpa [hx] using ((ENNReal.le_tsum x).trans <| le_sum_apply _ _).trans_eq h
  mpr := by rintro rfl; exact measure_empty

Depends on / 依赖: ENNReal, ENNReal.le_tsum, eq_empty_of_forall_notMem, le_sum_apply, le_tsum, measure_empty, trans_eq
-/
theorem count_eq_zero_iff : count s = 0 ↔ s = ∅ where
  mp h := eq_empty_of_forall_notMem fun x hx => by
    simpa [hx] using ((ENNReal.le_tsum x).trans <| le_sum_apply _ _).trans_eq h
  mpr := by rintro rfl; exact measure_empty

/--
lemma `count_ne_zero_iff` / 引理 `count_ne_zero_iff`

English:
lemma count_ne_zero_iff
  statement: count s != 0 ↔ s.Nonempty
  proof: count_eq_zero_iff.not.trans nonempty_iff_ne_empty.symm

alias ⟨_, count_ne_zero⟩ := count_ne_zero_iff

@[simp]

中文:
引理 count_ne_zero_iff
  结论: count s != 0 ↔ s.非空
  证明: count_eq_zero_iff.not.trans nonempty_iff_ne_empty.symm

alias ⟨_, count_ne_zero⟩ := count_ne_zero_iff

@[simp]

Depends on / 依赖: count_eq_zero_iff, count_eq_zero_iff.not.trans, nonempty_iff_ne_empty, nonempty_iff_ne_empty.symm
-/
lemma count_ne_zero_iff : count s != 0 ↔ s.Nonempty :=
  count_eq_zero_iff.not.trans nonempty_iff_ne_empty.symm

alias ⟨_, count_ne_zero⟩ := count_ne_zero_iff

@[simp]
/--
lemma `ae_count_iff` / 引理 `ae_count_iff`

English:
lemma ae_count_iff
  given: {p : α -> Prop}
  statement: (forallᵐ x ∂count, p x) ↔ forall x, p x
  proof: by
  refine ⟨fun h x => ?_, ae_of_all _⟩
  rw [ae_iff]; rw [count_eq_zero_iff] at h
  by_contra hx
  rwa [← mem_empty_iff_false x, ← h]

@[simp]

中文:
引理 ae_count_iff
  条件: {p : α -> 命题}
  结论: (对任意ᵐ x ∂count, p x) ↔ 对任意 x, p x
  证明: by
  refine ⟨fun h x => ?_, ae_of_all _⟩
  rw [ae_iff]; rw [count_eq_zero_iff] at h
  by_contra hx
  rwa [← mem_empty_iff_false x, ← h]

@[simp]

Depends on / 依赖: ae_iff, ae_of_all, count_eq_zero_iff, mem_empty_iff_false
-/
lemma ae_count_iff {p : α -> Prop} : (forallᵐ x ∂count, p x) ↔ forall x, p x := by
  refine ⟨fun h x => ?_, ae_of_all _⟩
  rw [ae_iff]; rw [count_eq_zero_iff] at h
  by_contra hx
  rwa [← mem_empty_iff_false x, ← h]

@[simp]
/--
theorem `count_singleton'` / 定理 `count_singleton'`

English:
theorem count_singleton'
  given: {a : α} (ha : MeasurableSet ({a} : Set α))
  statement: count ({a} : Set α) = 1
  proof: by
  rw [count_apply_finite' (Set.finite_singleton a) ha]; rw [Set.Finite.toFinset]
  simp

中文:
定理 count_singleton'
  条件: {a : α} (ha : 可测集 ({a} : 集合 α))
  结论: count ({a} : 集合 α) = 1
  证明: by
  rw [count_apply_finite' (Set.finite_singleton a) ha]; rw [Set.Finite.toFinset]
  simp

Depends on / 依赖: Finite, Set.Finite.toFinset, Set.finite_singleton, count_apply_finite, finite_singleton, toFinset
-/
theorem count_singleton' {a : α} (ha : MeasurableSet ({a} : Set α)) : count ({a} : Set α) = 1 := by
  rw [count_apply_finite' (Set.finite_singleton a) ha]; rw [Set.Finite.toFinset]
  simp

/--
theorem `count_singleton` / 定理 `count_singleton`

English:
theorem count_singleton
  given: [MeasurableSingletonClass α] (a : α)
  statement: count ({a} : Set α) = 1
  proof: count_singleton' (measurableSet_singleton a)

@[simp]

中文:
定理 count_singleton
  条件: [MeasurableSingleton类 α] (a : α)
  结论: count ({a} : 集合 α) = 1
  证明: count_singleton' (measurableSet_singleton a)

@[simp]

Depends on / 依赖: count_singleton, measurableSet_singleton
-/
theorem count_singleton [MeasurableSingletonClass α] (a : α) : count ({a} : Set α) = 1 :=
  count_singleton' (measurableSet_singleton a)

@[simp]
/--
theorem `_root_.MeasureTheory.count_real_singleton'` / 定理 `_root_.MeasureTheory.count_real_singleton'`

English:
theorem _root_.MeasureTheory.count_real_singleton'
  proof: by
  rw [measureReal_def]; rw [count_singleton' ha]; rw [ENNReal.toReal_one]

中文:
定理 _root_.测度论.count_real_singleton'
  证明: by
  rw [measureReal_def]; rw [count_singleton' ha]; rw [ENNReal.toReal_one]

Depends on / 依赖: ENNReal, ENNReal.toReal_one, count_singleton, measureReal_def, toReal_one
-/
theorem _root_.MeasureTheory.count_real_singleton'
    {a : α} (ha : MeasurableSet ({a} : Set α)) :
    count.real ({a} : Set α) = 1 := by
  rw [measureReal_def]; rw [count_singleton' ha]; rw [ENNReal.toReal_one]

/--
theorem `_root_.MeasureTheory.count_real_singleton` / 定理 `_root_.MeasureTheory.count_real_singleton`

English:
theorem _root_.MeasureTheory.count_real_singleton
  given: [MeasurableSingletonClass α] (a : α)
  proof: count_real_singleton' (measurableSet_singleton a)

中文:
定理 _root_.测度论.count_real_singleton
  条件: [MeasurableSingleton类 α] (a : α)
  证明: count_real_singleton' (measurableSet_singleton a)

Depends on / 依赖: count_real_singleton, measurableSet_singleton
-/
theorem _root_.MeasureTheory.count_real_singleton [MeasurableSingletonClass α] (a : α) :
    count.real ({a} : Set α) = 1 :=
  count_real_singleton' (measurableSet_singleton a)

/--
theorem `count_injective_image'` / 定理 `count_injective_image'`

English:
theorem count_injective_image'
  statement: {f : β -> α} (hf : Function.Injective f) {s : Set β}
  proof: by
  classical
  by_cases hs : s.Finite
  · lift s to Finset β using hs
    rw [← Finset.coe_image]; rw [count_apply_finset' _]; rw [count_apply_finset' s_mble]; rw [s.card_image_of_injective hf]
    simpa only [Finset.coe_image] using fs_mble
  · rw [count_apply_infinite hs]
    rw [← finite_image_iff hf.injOn] at hs
    rw [count_apply_infinite hs]

中文:
定理 count_injective_image'
  结论: {f : β -> α} (hf : 函数.单射 f) {s : 集合 β}
  证明: by
  classical
  by_cases hs : s.Finite
  · lift s to Finset β using hs
    rw [← Finset.coe_image]; rw [count_apply_finset' _]; rw [count_apply_finset' s_mble]; rw [s.card_image_of_injective hf]
    simpa only [Finset.coe_image] using fs_mble
  · rw [count_apply_infinite hs]
    rw [← finite_image_iff hf.injOn] at hs
    rw [count_apply_infinite hs]

Depends on / 依赖: Finite, Finset, Finset.coe_image, card_image_of_injective, classical, coe_image, count_apply_finset, count_apply_infinite, finite_image_iff, fs_mble, hf.injOn, s.Finite, s.card_image_of_injective, s_mble
-/
theorem count_injective_image' {f : β -> α} (hf : Function.Injective f) {s : Set β}
    (s_mble : MeasurableSet s) (fs_mble : MeasurableSet (f '' s)) : count (f '' s) = count s := by
  classical
  by_cases hs : s.Finite
  · lift s to Finset β using hs
    rw [← Finset.coe_image]; rw [count_apply_finset' _]; rw [count_apply_finset' s_mble]; rw [s.card_image_of_injective hf]
    simpa only [Finset.coe_image] using fs_mble
  · rw [count_apply_infinite hs]
    rw [← finite_image_iff hf.injOn] at hs
    rw [count_apply_infinite hs]

/--
theorem `count_injective_image` / 定理 `count_injective_image`

English:
theorem count_injective_image
  statement: [MeasurableSingletonClass α] [MeasurableSingletonClass β] {f : β -> α}
  proof: by
  by_cases hs : s.Finite
  · exact count_injective_image' hf hs.measurableSet (Finite.image f hs).measurableSet
  rw [count_apply_infinite hs]
  rw [← finite_image_iff hf.injOn] at hs
  rw [count_apply_infinite hs]

中文:
定理 count_injective_image
  结论: [MeasurableSingleton类 α] [MeasurableSingleton类 β] {f : β -> α}
  证明: by
  by_cases hs : s.Finite
  · exact count_injective_image' hf hs.measurableSet (Finite.image f hs).measurableSet
  rw [count_apply_infinite hs]
  rw [← finite_image_iff hf.injOn] at hs
  rw [count_apply_infinite hs]

Depends on / 依赖: Finite, Finite.image, count_apply_infinite, count_injective_image, finite_image_iff, hf.injOn, hs.measurableSet, measurableSet, s.Finite
-/
theorem count_injective_image [MeasurableSingletonClass α] [MeasurableSingletonClass β] {f : β -> α}
    (hf : Function.Injective f) (s : Set β) : count (f '' s) = count s := by
  by_cases hs : s.Finite
  · exact count_injective_image' hf hs.measurableSet (Finite.image f hs).measurableSet
  rw [count_apply_infinite hs]
  rw [← finite_image_iff hf.injOn] at hs
  rw [count_apply_infinite hs]

/--
Instance `count.instSigmaFinite` / 实例 `count.instSigmaFinite`

English:
instance count.instSigmaFinite
  signature: [MeasurableSingletonClass α] [Countable α]
  body: by simp [sigmaFinite_iff_measure_singleton_lt_top]

中文:
实例 count.instSigmaFinite
  签名: [MeasurableSingleton类 α] [可数 α]
  定义体: by simp [sigmaFinite_iff_measure_singleton_lt_top]

Depends on / 依赖: sigmaFinite_iff_measure_singleton_lt_top
-/
instance count.instSigmaFinite [MeasurableSingletonClass α] [Countable α] :
    SigmaFinite (count : Measure α) := by simp [sigmaFinite_iff_measure_singleton_lt_top]

/--
Instance `count.isFiniteMeasure` / 实例 `count.isFiniteMeasure`

English:
instance count.isFiniteMeasure
  signature: [Finite α]
  body: ⟨by simp [Measure.count_apply]⟩

@[simp]

中文:
实例 count.isFiniteMeasure
  签名: [有限 α]
  定义体: ⟨by simp [Measure.count_apply]⟩

@[simp]

Depends on / 依赖: IsLowerModularLattice, IsModularLattice, IsModularLattice.to_isLowerModularLattice, Measure, Measure.count_apply, count_apply, to_isLowerModularLattice
-/
instance count.isFiniteMeasure [Finite α] :
    IsFiniteMeasure (Measure.count : Measure α) :=
  ⟨by simp [Measure.count_apply]⟩

@[simp]
/--
lemma `count_univ` / 引理 `count_univ`

English:
lemma count_univ
  statement: count (univ : Set α) = ENat.card α
  proof: by simp [count_apply .univ, encard_univ]

中文:
引理 count_univ
  结论: count (univ : 集合 α) = E自然数.card α
  证明: by simp [count_apply .univ, encard_univ]

Depends on / 依赖: IsModularLattice, IsModularLattice.to_isUpperModularLattice, IsUpperModularLattice, count_apply, encard_univ, to_isUpperModularLattice
-/
lemma count_univ : count (univ : Set α) = ENat.card α := by simp [count_apply .univ, encard_univ]

/--
lemma `count_real_univ` / 引理 `count_real_univ`

English:
lemma count_real_univ
  statement: count.real (.univ : Set α) = Nat.card α
  proof: by simp [Measure.real]

中文:
引理 count_real_univ
  结论: count.real (.univ : 集合 α) = 自然数.card α
  证明: by simp [Measure.real]
-/
@[simp] lemma count_real_univ : count.real (.univ : Set α) = Nat.card α := by simp [Measure.real]

/--
Instance `neZero_count` / 实例 `neZero_count`

English:
instance neZero_count
  signature: [Nonempty α]
  body: by rintro h; simpa using congr($h .univ)

中文:
实例 neZero_count
  签名: [非空 α]
  定义体: by rintro h; simpa using congr($h .univ)
-/
instance neZero_count [Nonempty α] : NeZero (count : Measure α) where
  out := by rintro h; simpa using congr($h .univ)

/--
lemma `_root_.Subsingleton.count_eq_dirac` / 引理 `_root_.Subsingleton.count_eq_dirac`

English:
lemma _root_.Subsingleton.count_eq_dirac
  given: [Subsingleton α] (i : α)
  proof: by
  calc count
      = count.restrict univ := by simp
    _ = count.restrict {i} := by congr; ext j; simp [Subsingleton.elim j i]
    _ = dirac i := by simp

中文:
引理 _root_.子单例.count_eq_dirac
  条件: [子单例 α] (i : α)
  证明: by
  calc count
      = count.restrict univ := by simp
    _ = count.restrict {i} := by congr; ext j; simp [Subsingleton.elim j i]
    _ = dirac i := by simp

Depends on / 依赖: Subsingleton, Subsingleton.elim, count.restrict, restrict
-/
lemma _root_.Subsingleton.count_eq_dirac [Subsingleton α] (i : α) :
    count = dirac i := by
  calc count
      = count.restrict univ := by simp
    _ = count.restrict {i} := by congr; ext j; simp [Subsingleton.elim j i]
    _ = dirac i := by simp

/--
lemma `_root_.Unique.count_eq_dirac` / 引理 `_root_.Unique.count_eq_dirac`

English:
lemma _root_.Unique.count_eq_dirac
  given: [Unique α]
  statement: count = dirac (default : α)
  proof: Subsingleton.count_eq_dirac _

中文:
引理 _root_.唯一.count_eq_dirac
  条件: [唯一 α]
  结论: count = dirac (default : α)
  证明: Subsingleton.count_eq_dirac _

Depends on / 依赖: DistribLattice, IsModularLattice, Subsingleton, Subsingleton.count_eq_dirac, count_eq_dirac
-/
lemma _root_.Unique.count_eq_dirac [Unique α] : count = dirac (default : α) :=
  Subsingleton.count_eq_dirac _

/--
lemma `_root_.Function.Injective.map_count_le` / 引理 `_root_.Function.Injective.map_count_le`

English:
lemma _root_.Function.Injective.map_count_le
  statement: {f : α -> β}
  proof: by
  refine le_intro fun s hs _ => ?_
  rw [map_apply h2f hs]; rw [count_apply (hs.preimage h2f)]; rw [count_apply hs]; rw [← hf.encard_image]
  have := image_preimage_subset f s
  gcongr

中文:
引理 _root_.函数.单射.map_count_le
  结论: {f : α -> β}
  证明: by
  refine le_intro fun s hs _ => ?_
  rw [map_apply h2f hs]; rw [count_apply (hs.preimage h2f)]; rw [count_apply hs]; rw [← hf.encard_image]
  have := image_preimage_subset f s
  gcongr

Depends on / 依赖: count_apply, encard_image, hf.encard_image, hs.preimage, image_preimage_subset, le_intro, map_apply, preimage
-/
lemma _root_.Function.Injective.map_count_le {f : α -> β}
    (hf : f.Injective) (h2f : Measurable f) : count.map f <= count := by
  refine le_intro fun s hs _ => ?_
  rw [map_apply h2f hs]; rw [count_apply (hs.preimage h2f)]; rw [count_apply hs]; rw [← hf.encard_image]
  have := image_preimage_subset f s
  gcongr

end Measure

end MeasureTheory
