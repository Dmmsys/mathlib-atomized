/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
module

public import Mathlib.MeasureTheory.MeasurableSpace.CountablyGenerated
public import Mathlib.MeasureTheory.Measure.MutuallySingular
public import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite

/-!
# Dirac measure

In this file we define the Dirac measure `MeasureTheory.Measure.dirac a`
and prove some basic facts about it.
-/

@[expose] public section

open Function Set
open scoped ENNReal NNReal

noncomputable section

variable {α β δ : Type*} [MeasurableSpace α] [MeasurableSpace β] {s : Set α} {a : α}

namespace MeasureTheory

namespace Measure

/--
Definition of `dirac` / `dirac` 的定义

English:
definition dirac
  signature: (a : α)
  body: (OuterMeasure.dirac a).toMeasure (by simp)

中文:
定义 dirac
  签名: (a : α)
  定义体: (OuterMeasure.dirac a).toMeasure (by simp)

Depends on / 依赖: OuterMeasure, OuterMeasure.dirac, toMeasure
-/
def dirac (a : α) : Measure α := (OuterMeasure.dirac a).toMeasure (by simp)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MeasureSpace PUnit
  body: ⟨dirac PUnit.unit⟩

中文:
实例 :
  签名: MeasureSpace PUnit
  定义体: ⟨dirac PUnit.unit⟩

Depends on / 依赖: PUnit.unit
-/
instance : MeasureSpace PUnit :=
  ⟨dirac PUnit.unit⟩

/--
theorem `le_dirac_apply` / 定理 `le_dirac_apply`

English:
theorem le_dirac_apply
  given: {a}
  statement: s.indicator 1 a <= dirac a s
  proof: OuterMeasure.dirac_apply a s ▸ le_toMeasure_apply _ _ _

@[simp]

中文:
定理 le_dirac_apply
  条件: {a}
  结论: s.indicator 1 a <= dirac a s
  证明: OuterMeasure.dirac_apply a s ▸ le_toMeasure_apply _ _ _

@[simp]

Depends on / 依赖: OuterMeasure, OuterMeasure.dirac_apply, dirac_apply, le_toMeasure_apply
-/
theorem le_dirac_apply {a} : s.indicator 1 a <= dirac a s :=
  OuterMeasure.dirac_apply a s ▸ le_toMeasure_apply _ _ _

@[simp]
/--
theorem `dirac_apply'` / 定理 `dirac_apply'`

English:
theorem dirac_apply'
  given: (a : α) (hs : MeasurableSet s)
  statement: dirac a s = s.indicator 1 a
  proof: toMeasure_apply _ _ hs

中文:
定理 dirac_apply'
  条件: (a : α) (hs : MeasurableSet s)
  结论: dirac a s = s.indicator 1 a
  证明: toMeasure_apply _ _ hs

Depends on / 依赖: toMeasure_apply
-/
theorem dirac_apply' (a : α) (hs : MeasurableSet s) : dirac a s = s.indicator 1 a :=
  toMeasure_apply _ _ hs

/--
theorem `dirac_apply_eq_zero_or_one` / 定理 `dirac_apply_eq_zero_or_one`

English:
theorem dirac_apply_eq_zero_or_one
  proof: by
  rw [← measure_toMeasurable s]; rw [dirac_apply' a (measurableSet_toMeasurable ..)]; rw [indicator]
  simp only [Pi.one_apply, ite_eq_right_iff, one_ne_zero, imp_false, ite_eq_left_iff, zero_ne_one,
    not_not]
  tauto

@[simp]

中文:
定理 dirac_apply_eq_zero_or_one
  证明: by
  rw [← measure_toMeasurable s]; rw [dirac_apply' a (measurableSet_toMeasurable ..)]; rw [indicator]
  simp only [Pi.one_apply, ite_eq_right_iff, one_ne_zero, imp_false, ite_eq_left_iff, zero_ne_one,
    not_not]
  tauto

@[simp]

Depends on / 依赖: Pi.one_apply, dirac_apply, imp_false, indicator, ite_eq_left_iff, ite_eq_right_iff, measurableSet_toMeasurable, measure_toMeasurable, not_not, one_apply, one_ne_zero, zero_ne_one
-/
theorem dirac_apply_eq_zero_or_one :
    dirac a s = 0 ∨ dirac a s = 1 := by
  rw [← measure_toMeasurable s]; rw [dirac_apply' a (measurableSet_toMeasurable ..)]; rw [indicator]
  simp only [Pi.one_apply, ite_eq_right_iff, one_ne_zero, imp_false, ite_eq_left_iff, zero_ne_one,
    not_not]
  tauto

@[simp]
/--
theorem `dirac_apply_ne_zero_iff_eq_one` / 定理 `dirac_apply_ne_zero_iff_eq_one`

English:
theorem dirac_apply_ne_zero_iff_eq_one
  proof: dirac_apply_eq_zero_or_one.resolve_left
  mpr := ne_zero_of_eq_one

@[simp]

中文:
定理 dirac_apply_ne_zero_iff_eq_one
  证明: dirac_apply_eq_zero_or_one.resolve_left
  mpr := ne_zero_of_eq_one

@[simp]

Depends on / 依赖: dirac_apply_eq_zero_or_one, dirac_apply_eq_zero_or_one.resolve_left, resolve_left
-/
theorem dirac_apply_ne_zero_iff_eq_one :
    dirac a s != 0 ↔ dirac a s = 1 where
  mp := dirac_apply_eq_zero_or_one.resolve_left
  mpr := ne_zero_of_eq_one

@[simp]
/--
theorem `dirac_apply_ne_one_iff_eq_zero` / 定理 `dirac_apply_ne_one_iff_eq_zero`

English:
theorem dirac_apply_ne_one_iff_eq_zero
  proof: dirac_apply_eq_zero_or_one.resolve_right
  mpr h := h ▸ zero_ne_one

@[simp]

中文:
定理 dirac_apply_ne_one_iff_eq_zero
  证明: dirac_apply_eq_zero_or_one.resolve_right
  mpr h := h ▸ zero_ne_one

@[simp]

Depends on / 依赖: dirac_apply_eq_zero_or_one, dirac_apply_eq_zero_or_one.resolve_right, resolve_right
-/
theorem dirac_apply_ne_one_iff_eq_zero :
    dirac a s != 1 ↔ dirac a s = 0 where
  mp := dirac_apply_eq_zero_or_one.resolve_right
  mpr h := h ▸ zero_ne_one

@[simp]
/--
theorem `dirac_apply_of_mem` / 定理 `dirac_apply_of_mem`

English:
theorem dirac_apply_of_mem
  given: {a : α} (h : a in s)
  statement: dirac a s = 1
  proof: by
  have : forall t : Set α, a in t -> t.indicator (1 : α -> Real>=0∞) a = 1 := fun t ht => indicator_of_mem ht 1
  refine le_antisymm (this univ trivial ▸ ?_) (this s h ▸ le_dirac_apply)
  rw [← dirac_apply' a MeasurableSet.univ]
  exact measure_mono (subset_univ s)

@[simp]

中文:
定理 dirac_apply_of_mem
  条件: {a : α} (h : a in s)
  结论: dirac a s = 1
  证明: by
  have : forall t : Set α, a in t -> t.indicator (1 : α -> Real>=0∞) a = 1 := fun t ht => indicator_of_mem ht 1
  refine le_antisymm (this univ trivial ▸ ?_) (this s h ▸ le_dirac_apply)
  rw [← dirac_apply' a MeasurableSet.univ]
  exact measure_mono (subset_univ s)

@[simp]

Depends on / 依赖: MeasurableSet, MeasurableSet.univ, dirac_apply, indicator, indicator_of_mem, le_antisymm, le_dirac_apply, measure_mono, subset_univ, t.indicator
-/
theorem dirac_apply_of_mem {a : α} (h : a in s) : dirac a s = 1 := by
  have : forall t : Set α, a in t -> t.indicator (1 : α -> Real>=0∞) a = 1 := fun t ht => indicator_of_mem ht 1
  refine le_antisymm (this univ trivial ▸ ?_) (this s h ▸ le_dirac_apply)
  rw [← dirac_apply' a MeasurableSet.univ]
  exact measure_mono (subset_univ s)

@[simp]
/--
theorem `dirac_apply` / 定理 `dirac_apply`

English:
theorem dirac_apply
  given: [MeasurableSingletonClass α] (a : α) (s : Set α)
  proof: by
  by_cases h : a in s; · rw [dirac_apply_of_mem h, indicator_of_mem h, Pi.one_apply]
  rw [indicator_of_notMem h]; rw [← nonpos_iff_eq_zero]
  calc
    dirac a s <= dirac a {a}ᶜ := measure_mono (subset_compl_comm.1 <| singleton_subset_iff.2 h)
    _ = 0 := by simp [dirac_apply' _ (measurableSet_s

中文:
定理 dirac_apply
  条件: [MeasurableSingletonClass α] (a : α) (s : Set α)
  证明: by
  by_cases h : a in s; · rw [dirac_apply_of_mem h, indicator_of_mem h, Pi.one_apply]
  rw [indicator_of_notMem h]; rw [← nonpos_iff_eq_zero]
  calc
    dirac a s <= dirac a {a}ᶜ := measure_mono (subset_compl_comm.1 <| singleton_subset_iff.2 h)
    _ = 0 := by simp [dirac_apply' _ (measurableSet_s

Depends on / 依赖: Pi.one_apply, dirac_apply, dirac_apply_of_mem, indicator_of_mem, indicator_of_notMem, measurableSet_singleton, measure_mono, nonpos_iff_eq_zero, one_apply, singleton_subset_iff, subset_compl_comm
-/
theorem dirac_apply [MeasurableSingletonClass α] (a : α) (s : Set α) :
    dirac a s = s.indicator 1 a := by
  by_cases h : a in s; · rw [dirac_apply_of_mem h, indicator_of_mem h, Pi.one_apply]
  rw [indicator_of_notMem h]; rw [← nonpos_iff_eq_zero]
  calc
    dirac a s <= dirac a {a}ᶜ := measure_mono (subset_compl_comm.1 <| singleton_subset_iff.2 h)
    _ = 0 := by simp [dirac_apply' _ (measurableSet_singleton _).compl]

/--
lemma `dirac_ne_zero` / 引理 `dirac_ne_zero`

English:
lemma dirac_ne_zero
  statement: dirac a != 0
  proof: fun h => by simpa [h] using dirac_apply_of_mem (mem_univ a)

@[simp]

中文:
引理 dirac_ne_zero
  结论: dirac a != 0
  证明: fun h => by simpa [h] using dirac_apply_of_mem (mem_univ a)

@[simp]
-/
@[simp] lemma dirac_ne_zero : dirac a != 0 :=
  fun h => by simpa [h] using dirac_apply_of_mem (mem_univ a)

@[simp]
/--
theorem `map_dirac'` / 定理 `map_dirac'`

English:
theorem map_dirac'
  given: {f : α -> β} (hf : Measurable f) (a : α)
  statement: (dirac a).map f = dirac (f a)
  proof: by
  classical
  exact ext fun s hs => by simp [hs, map_apply hf hs, hf hs, indicator_apply]

@[simp]

中文:
定理 map_dirac'
  条件: {f : α -> β} (hf : Measurable f) (a : α)
  结论: (dirac a).map f = dirac (f a)
  证明: by
  classical
  exact ext fun s hs => by simp [hs, map_apply hf hs, hf hs, indicator_apply]

@[simp]

Depends on / 依赖: classical, indicator_apply, map_apply
-/
theorem map_dirac' {f : α -> β} (hf : Measurable f) (a : α) : (dirac a).map f = dirac (f a) := by
  classical
  exact ext fun s hs => by simp [hs, map_apply hf hs, hf hs, indicator_apply]

@[simp]
/--
lemma `map_const` / 引理 `map_const`

English:
lemma map_const
  given: (μ : Measure α) (c : β)
  statement: μ.map (fun _ => c) = (μ Set.univ) • dirac c
  proof: by
  ext s hs
  simp only [Measure.coe_smul, Pi.smul_apply,
    dirac_apply' _ hs, smul_eq_mul]
  classical
  rw [Measure.map_apply measurable_const hs]; rw [Set.preimage_const]
  by_cases hsc : c in s
  · rw [(Set.indicator_eq_one_iff_mem _).mpr hsc, mul_one, if_pos hsc]
  · rw [if_neg hsc, (Set.in

中文:
引理 map_const
  条件: (μ : Measure α) (c : β)
  结论: μ.map (fun _ => c) = (μ Set.univ) • dirac c
  证明: by
  ext s hs
  simp only [Measure.coe_smul, Pi.smul_apply,
    dirac_apply' _ hs, smul_eq_mul]
  classical
  rw [Measure.map_apply measurable_const hs]; rw [Set.preimage_const]
  by_cases hsc : c in s
  · rw [(Set.indicator_eq_one_iff_mem _).mpr hsc, mul_one, if_pos hsc]
  · rw [if_neg hsc, (Set.in

Depends on / 依赖: Measure, Measure.coe_smul, Measure.map_apply, Pi.smul_apply, Set.indicator_eq_one_iff_mem, Set.indicator_eq_zero_iff_notMem, Set.preimage_const, classical, coe_smul, dirac_apply, if_neg, if_pos, indicator_eq_one_iff_mem, indicator_eq_zero_iff_notMem, map_apply, measurable_const, measure_empty, mul_one, mul_zero, preimage_const
-/
lemma map_const (μ : Measure α) (c : β) : μ.map (fun _ => c) = (μ Set.univ) • dirac c := by
  ext s hs
  simp only [Measure.coe_smul, Pi.smul_apply,
    dirac_apply' _ hs, smul_eq_mul]
  classical
  rw [Measure.map_apply measurable_const hs]; rw [Set.preimage_const]
  by_cases hsc : c in s
  · rw [(Set.indicator_eq_one_iff_mem _).mpr hsc, mul_one, if_pos hsc]
  · rw [if_neg hsc, (Set.indicator_eq_zero_iff_notMem _).mpr hsc, measure_empty, mul_zero]

@[simp]
/--
theorem `restrict_singleton` / 定理 `restrict_singleton`

English:
theorem restrict_singleton
  given: (μ : Measure α) (a : α)
  statement: μ.restrict {a} = μ {a} • dirac a
  proof: by
  ext1 s hs
  by_cases ha : a in s
  · have : s inter {a} = {a} := by simpa
    simp [*]
  · have : s inter {a} = ∅ := inter_singleton_eq_empty.2 ha
    simp [*]

中文:
定理 restrict_singleton
  条件: (μ : Measure α) (a : α)
  结论: μ.restrict {a} = μ {a} • dirac a
  证明: by
  ext1 s hs
  by_cases ha : a in s
  · have : s inter {a} = {a} := by simpa
    simp [*]
  · have : s inter {a} = ∅ := inter_singleton_eq_empty.2 ha
    simp [*]

Depends on / 依赖: inter_singleton_eq_empty
-/
theorem restrict_singleton (μ : Measure α) (a : α) : μ.restrict {a} = μ {a} • dirac a := by
  ext1 s hs
  by_cases ha : a in s
  · have : s inter {a} = {a} := by simpa
    simp [*]
  · have : s inter {a} = ∅ := inter_singleton_eq_empty.2 ha
    simp [*]

/--
theorem `ext_of_singleton` / 定理 `ext_of_singleton`

English:
theorem ext_of_singleton
  given: [Countable α] {μ ν : Measure α} (h : forall a, μ {a} = ν {a})
  statement: μ = ν
  proof: ext_of_sUnion_eq_univ (countable_range singleton) (by aesop) (by simp_all)

中文:
定理 ext_of_singleton
  条件: [Countable α] {μ ν : Measure α} (h : 对任意 a, μ {a} = ν {a})
  结论: μ = ν
  证明: ext_of_sUnion_eq_univ (countable_range singleton) (by aesop) (by simp_all)

Depends on / 依赖: countable_range, ext_of_sUnion_eq_univ, singleton
-/
theorem ext_of_singleton [Countable α] {μ ν : Measure α} (h : forall a, μ {a} = ν {a}) : μ = ν :=
  ext_of_sUnion_eq_univ (countable_range singleton) (by aesop) (by simp_all)

/--
theorem `ext_iff_singleton` / 定理 `ext_iff_singleton`

English:
theorem ext_iff_singleton
  given: [Countable α] {μ ν : Measure α}
  statement: μ = ν ↔ forall a, μ {a} = ν {a}
  proof: ⟨fun h _ => h ▸ rfl, ext_of_singleton⟩

中文:
定理 ext_iff_singleton
  条件: [Countable α] {μ ν : Measure α}
  结论: μ = ν ↔ 对任意 a, μ {a} = ν {a}
  证明: ⟨fun h _ => h ▸ rfl, ext_of_singleton⟩

Depends on / 依赖: ext_of_singleton
-/
theorem ext_iff_singleton [Countable α] {μ ν : Measure α} : μ = ν ↔ forall a, μ {a} = ν {a} :=
  ⟨fun h _ => h ▸ rfl, ext_of_singleton⟩

/--
theorem `_root_.MeasureTheory.ext_iff_measureReal_singleton` / 定理 `_root_.MeasureTheory.ext_iff_measureReal_singleton`

English:
theorem _root_.MeasureTheory.ext_iff_measureReal_singleton
  statement: [Countable α]
  proof: by
  rw [Measure.ext_iff_singleton]
  congr! with x
  rw [measureReal_def]; rw [measureReal_def]; rw [ENNReal.toReal_eq_toReal_iff]
  simp [measure_singleton_lt_top, ne_of_lt]

alias ⟨_, ext_of_measureReal_singleton⟩ := MeasureTheory.ext_iff_measureReal_singleton

中文:
定理 _root_.MeasureTheory.ext_iff_measureReal_singleton
  结论: [Countable α]
  证明: by
  rw [Measure.ext_iff_singleton]
  congr! with x
  rw [measureReal_def]; rw [measureReal_def]; rw [ENNReal.toReal_eq_toReal_iff]
  simp [measure_singleton_lt_top, ne_of_lt]

alias ⟨_, ext_of_measureReal_singleton⟩ := MeasureTheory.ext_iff_measureReal_singleton

Depends on / 依赖: ENNReal, ENNReal.toReal_eq_toReal_iff, Measure, Measure.ext_iff_singleton, ext_iff_singleton, measureReal_def, measure_singleton_lt_top, ne_of_lt, toReal_eq_toReal_iff
-/
theorem _root_.MeasureTheory.ext_iff_measureReal_singleton [Countable α]
    {μ1 μ2 : Measure α} [SigmaFinite μ1] [SigmaFinite μ2] :
    μ1 = μ2 ↔ forall x, μ1.real {x} = μ2.real {x} := by
  rw [Measure.ext_iff_singleton]
  congr! with x
  rw [measureReal_def]; rw [measureReal_def]; rw [ENNReal.toReal_eq_toReal_iff]
  simp [measure_singleton_lt_top, ne_of_lt]

alias ⟨_, ext_of_measureReal_singleton⟩ := MeasureTheory.ext_iff_measureReal_singleton

/--
theorem `map_eq_sum` / 定理 `map_eq_sum`

English:
theorem map_eq_sum
  statement: [Countable β] [MeasurableSingletonClass β] (μ : Measure α) (f : α -> β)
  proof: by
  ext s
  have : forall y in s, MeasurableSet (f ⁻¹' {y}) := fun y _ => hf (measurableSet_singleton _)
  simp [← tsum_measure_preimage_singleton (to_countable s) this, *,
    tsum_subtype s fun b => μ (f ⁻¹' {b}), ← indicator_mul_right s fun b => μ (f ⁻¹' {b})]

中文:
定理 map_eq_sum
  结论: [Countable β] [MeasurableSingletonClass β] (μ : Measure α) (f : α -> β)
  证明: by
  ext s
  have : forall y in s, MeasurableSet (f ⁻¹' {y}) := fun y _ => hf (measurableSet_singleton _)
  simp [← tsum_measure_preimage_singleton (to_countable s) this, *,
    tsum_subtype s fun b => μ (f ⁻¹' {b}), ← indicator_mul_right s fun b => μ (f ⁻¹' {b})]

Depends on / 依赖: MeasurableSet, indicator_mul_right, measurableSet_singleton, to_countable, tsum_measure_preimage_singleton, tsum_subtype
-/
theorem map_eq_sum [Countable β] [MeasurableSingletonClass β] (μ : Measure α) (f : α -> β)
    (hf : Measurable f) : μ.map f = sum fun b : β => μ (f ⁻¹' {b}) • dirac b := by
  ext s
  have : forall y in s, MeasurableSet (f ⁻¹' {y}) := fun y _ => hf (measurableSet_singleton _)
  simp [← tsum_measure_preimage_singleton (to_countable s) this, *,
    tsum_subtype s fun b => μ (f ⁻¹' {b}), ← indicator_mul_right s fun b => μ (f ⁻¹' {b})]

/-- A measure on a countable type is a sum of Dirac measures. -/
@[simp]
/--
theorem `sum_smul_dirac` / 定理 `sum_smul_dirac`

English:
theorem sum_smul_dirac
  given: [Countable α] [MeasurableSingletonClass α] (μ : Measure α)
  proof: by simpa using (map_eq_sum μ id measurable_id).symm

中文:
定理 sum_smul_dirac
  条件: [Countable α] [MeasurableSingletonClass α] (μ : Measure α)
  证明: by simpa using (map_eq_sum μ id measurable_id).symm

Depends on / 依赖: map_eq_sum, measurable_id
-/
theorem sum_smul_dirac [Countable α] [MeasurableSingletonClass α] (μ : Measure α) :
    (sum fun a => μ {a} • dirac a) = μ := by simpa using (map_eq_sum μ id measurable_id).symm

/--
lemma `sum_smul_dirac_singleton` / 引理 `sum_smul_dirac_singleton`

English:
lemma sum_smul_dirac_singleton
  given: [MeasurableSingletonClass α] {f : α -> Real>=0∞} {a : α}
  proof: by
  simp +contextual [tsum_eq_single a]

中文:
引理 sum_smul_dirac_singleton
  条件: [MeasurableSingletonClass α] {f : α -> 实数>=0∞} {a : α}
  证明: by
  simp +contextual [tsum_eq_single a]

Depends on / 依赖: contextual, tsum_eq_single
-/
lemma sum_smul_dirac_singleton [MeasurableSingletonClass α] {f : α -> Real>=0∞} {a : α} :
    sum (fun b : α => f b • dirac b) {a} = f a := by
  simp +contextual [tsum_eq_single a]

/--
lemma `exists_sum_smul_dirac` / 引理 `exists_sum_smul_dirac`

English:
lemma exists_sum_smul_dirac
  given: [Countable α] (μ : Measure α)
  proof: by
  let measurableAtoms := measurableAtom '' (Set.univ : Set α)
  have h_nonempty (s : measurableAtoms) : Set.Nonempty s.1 := by
    obtain ⟨y, _, hy⟩ := s.2
    rw [← hy]
    exact ⟨y, mem_measurableAtom_self y⟩
  let points : measurableAtoms -> α := fun s => (h_nonempty s).some
  have h_points_me

中文:
引理 exists_sum_smul_dirac
  条件: [Countable α] (μ : Measure α)
  证明: by
  let measurableAtoms := measurableAtom '' (Set.univ : Set α)
  have h_nonempty (s : measurableAtoms) : Set.Nonempty s.1 := by
    obtain ⟨y, _, hy⟩ := s.2
    rw [← hy]
    exact ⟨y, mem_measurableAtom_self y⟩
  let points : measurableAtoms -> α := fun s => (h_nonempty s).some
  have h_points_me

Depends on / 依赖: MeasurableSet, MeasurableSet.measurableAtom_of_countable, Measure, Measure.smul_ap, Nonempty, Set.Nonempty, Set.range, Set.univ, ext_of_measurableAtoms, h_nonempty, h_points_mem, measurableAtom, measurableAtom_of_countable, measurableAtoms, mem_measurableAtom_self, points, smul_ap, some_mem, sum_apply
-/
lemma exists_sum_smul_dirac [Countable α] (μ : Measure α) :
    exists s : Set α, μ = Measure.sum (fun x : s => μ (measurableAtom x) • dirac (x : α)) := by
  let measurableAtoms := measurableAtom '' (Set.univ : Set α)
  have h_nonempty (s : measurableAtoms) : Set.Nonempty s.1 := by
    obtain ⟨y, _, hy⟩ := s.2
    rw [← hy]
    exact ⟨y, mem_measurableAtom_self y⟩
  let points : measurableAtoms -> α := fun s => (h_nonempty s).some
  have h_points_mem (s : measurableAtoms) : points s in s.1 := (h_nonempty s).some_mem
  refine ⟨Set.range points, ext_of_measurableAtoms fun x => ?_⟩
  rw [sum_apply _ (MeasurableSet.measurableAtom_of_countable x)]
  simp only [Measure.smul_apply, smul_eq_mul]
  simp_rw [dirac_apply' _ (MeasurableSet.measurableAtom_of_countable x)]
  rw [tsum_eq_single ⟨points ⟨measurableAtom x]; rw [by simp [measurableAtoms]⟩, by simp⟩]
  · rw [indicator_of_mem]
    · simp only [Pi.one_apply, mul_one]
      congr 1
      refine (measurableAtom_eq_of_mem ?_).symm
      convert! h_points_mem _
      simp
    · convert! h_points_mem _
      simp
  · simp only [ne_eq, mul_eq_zero, indicator_apply_eq_zero, Pi.one_apply, one_ne_zero, imp_false,
      Subtype.forall, Set.mem_range, Subtype.exists, Subtype.mk.injEq, forall_exists_index]
    refine fun y s hs hsy hyx => .inr fun hyx' => hyx ?_
    rw [← hsy]
    congr
    have h1 : measurableAtom y = measurableAtom x := measurableAtom_eq_of_mem hyx'
    have h2 : measurableAtom y = s := by
      specialize h_points_mem ⟨s, hs⟩
      obtain ⟨z, _, hz⟩ := hs
      simp only at h_points_mem
      rw [← hz]; rw [← hsy]
      refine measurableAtom_eq_of_mem ?_
      convert! h_points_mem
    rw [← h2]; rw [h1]

/--
theorem `tsum_indicator_apply_singleton` / 定理 `tsum_indicator_apply_singleton`

English:
theorem tsum_indicator_apply_singleton
  statement: [Countable α] [MeasurableSingletonClass α] (μ : Measure α)
  proof: by
  classical
  calc
    (∑' x : α, s.indicator (fun x => μ {x}) x) =
      Measure.sum (fun a => μ {a} • Measure.dirac a) s := by
      simp only [Measure.sum_apply _ hs, Measure.smul_apply, smul_eq_mul, Measure.dirac_apply,
        Set.indicator_apply, mul_ite, Pi.one_apply, mul_one, mul_zero]
  

中文:
定理 tsum_indicator_apply_singleton
  结论: [Countable α] [MeasurableSingletonClass α] (μ : Measure α)
  证明: by
  classical
  calc
    (∑' x : α, s.indicator (fun x => μ {x}) x) =
      Measure.sum (fun a => μ {a} • Measure.dirac a) s := by
      simp only [Measure.sum_apply _ hs, Measure.smul_apply, smul_eq_mul, Measure.dirac_apply,
        Set.indicator_apply, mul_ite, Pi.one_apply, mul_one, mul_zero]
  

Depends on / 依赖: Measure, Measure.dirac, Measure.dirac_apply, Measure.smul_apply, Measure.sum, Measure.sum_apply, Pi.one_apply, Set.indicator_apply, classical, dirac_apply, indicator, indicator_apply, mul_ite, mul_one, mul_zero, one_apply, s.indicator, smul_apply, smul_eq_mul, sum_apply
-/
theorem tsum_indicator_apply_singleton [Countable α] [MeasurableSingletonClass α] (μ : Measure α)
    (s : Set α) (hs : MeasurableSet s) : (∑' x : α, s.indicator (fun x => μ {x}) x) = μ s := by
  classical
  calc
    (∑' x : α, s.indicator (fun x => μ {x}) x) =
      Measure.sum (fun a => μ {a} • Measure.dirac a) s := by
      simp only [Measure.sum_apply _ hs, Measure.smul_apply, smul_eq_mul, Measure.dirac_apply,
        Set.indicator_apply, mul_ite, Pi.one_apply, mul_one, mul_zero]
    _ = μ s := by rw [μ.sum_smul_dirac]

end Measure

open Measure

/--
theorem `mem_ae_dirac_iff` / 定理 `mem_ae_dirac_iff`

English:
theorem mem_ae_dirac_iff
  given: {a : α} (hs : MeasurableSet s)
  statement: s in ae (dirac a) ↔ a in s
  proof: by
  by_cases a in s <;> simp [mem_ae_iff, dirac_apply', hs.compl, *]

中文:
定理 mem_ae_dirac_iff
  条件: {a : α} (hs : MeasurableSet s)
  结论: s in ae (dirac a) ↔ a in s
  证明: by
  by_cases a in s <;> simp [mem_ae_iff, dirac_apply', hs.compl, *]

Depends on / 依赖: dirac_apply, hs.compl, mem_ae_iff
-/
theorem mem_ae_dirac_iff {a : α} (hs : MeasurableSet s) : s in ae (dirac a) ↔ a in s := by
  by_cases a in s <;> simp [mem_ae_iff, dirac_apply', hs.compl, *]

/--
theorem `ae_dirac_iff` / 定理 `ae_dirac_iff`

English:
theorem ae_dirac_iff
  given: {a : α} {p : α -> Prop} (hp : MeasurableSet { x | p x })
  proof: mem_ae_dirac_iff hp

@[simp]

中文:
定理 ae_dirac_iff
  条件: {a : α} {p : α -> 命题} (hp : MeasurableSet { x | p x })
  证明: mem_ae_dirac_iff hp

@[simp]
-/
@[simp] theorem ae_dirac_iff {a : α} {p : α -> Prop} (hp : MeasurableSet { x | p x }) :
    (forallᵐ x ∂dirac a, p x) ↔ p a :=
  mem_ae_dirac_iff hp

@[simp]
/--
theorem `ae_dirac_eq` / 定理 `ae_dirac_eq`

English:
theorem ae_dirac_eq
  given: [MeasurableSingletonClass α] (a : α)
  statement: ae (dirac a) = pure a
  proof: by
  ext s
  simp [mem_ae_iff, imp_false]

中文:
定理 ae_dirac_eq
  条件: [MeasurableSingletonClass α] (a : α)
  结论: ae (dirac a) = pure a
  证明: by
  ext s
  simp [mem_ae_iff, imp_false]

Depends on / 依赖: imp_false, mem_ae_iff
-/
theorem ae_dirac_eq [MeasurableSingletonClass α] (a : α) : ae (dirac a) = pure a := by
  ext s
  simp [mem_ae_iff, imp_false]

/--
theorem `ae_eq_dirac'` / 定理 `ae_eq_dirac'`

English:
theorem ae_eq_dirac'
  given: [MeasurableSingletonClass β] {a : α} {f : α -> β} (hf : Measurable f)
  proof: (ae_dirac_iff <| show MeasurableSet (f ⁻¹' {f a}) from hf <| measurableSet_singleton _).2 rfl

中文:
定理 ae_eq_dirac'
  条件: [MeasurableSingletonClass β] {a : α} {f : α -> β} (hf : Measurable f)
  证明: (ae_dirac_iff <| show MeasurableSet (f ⁻¹' {f a}) from hf <| measurableSet_singleton _).2 rfl

Depends on / 依赖: MeasurableSet, ae_dirac_iff, measurableSet_singleton
-/
theorem ae_eq_dirac' [MeasurableSingletonClass β] {a : α} {f : α -> β} (hf : Measurable f) :
    f =ᵐ[dirac a] const α (f a) :=
  (ae_dirac_iff <| show MeasurableSet (f ⁻¹' {f a}) from hf <| measurableSet_singleton _).2 rfl

/--
theorem `ae_eq_dirac` / 定理 `ae_eq_dirac`

English:
theorem ae_eq_dirac
  given: [MeasurableSingletonClass α] {a : α} (f : α -> δ)
  proof: by simp [Filter.EventuallyEq]

@[fun_prop]

中文:
定理 ae_eq_dirac
  条件: [MeasurableSingletonClass α] {a : α} (f : α -> δ)
  证明: by simp [Filter.EventuallyEq]

@[fun_prop]

Depends on / 依赖: EventuallyEq, Filter, Filter.EventuallyEq
-/
theorem ae_eq_dirac [MeasurableSingletonClass α] {a : α} (f : α -> δ) :
    f =ᵐ[dirac a] const α (f a) := by simp [Filter.EventuallyEq]

@[fun_prop]
/--
lemma `aemeasurable_dirac` / 引理 `aemeasurable_dirac`

English:
lemma aemeasurable_dirac
  given: [MeasurableSingletonClass α] {a : α} {f : α -> β}
  proof: ⟨fun _ => f a, measurable_const, ae_eq_dirac f⟩

@[simp]

中文:
引理 aemeasurable_dirac
  条件: [MeasurableSingletonClass α] {a : α} {f : α -> β}
  证明: ⟨fun _ => f a, measurable_const, ae_eq_dirac f⟩

@[simp]

Depends on / 依赖: ae_eq_dirac, measurable_const
-/
lemma aemeasurable_dirac [MeasurableSingletonClass α] {a : α} {f : α -> β} :
    AEMeasurable f (Measure.dirac a) :=
  ⟨fun _ => f a, measurable_const, ae_eq_dirac f⟩

@[simp]
/--
theorem `Measure.map_dirac` / 定理 `Measure.map_dirac`

English:
theorem Measure.map_dirac
  statement: [MeasurableSingletonClass α] [MeasurableSingletonClass β]
  proof: by
  classical
  ext s hs
  rw [map_apply_of_aemeasurable (by fun_prop) hs]
  simp [indicator_apply]

中文:
定理 Measure.map_dirac
  结论: [MeasurableSingletonClass α] [MeasurableSingletonClass β]
  证明: by
  classical
  ext s hs
  rw [map_apply_of_aemeasurable (by fun_prop) hs]
  simp [indicator_apply]

Depends on / 依赖: classical, fun_prop, indicator_apply, map_apply_of_aemeasurable
-/
theorem Measure.map_dirac [MeasurableSingletonClass α] [MeasurableSingletonClass β]
    {f : α -> β} (a : α) : (dirac a).map f = dirac (f a) := by
  classical
  ext s hs
  rw [map_apply_of_aemeasurable (by fun_prop) hs]
  simp [indicator_apply]

/--
Instance `Measure.dirac.isProbabilityMeasure` / 实例 `Measure.dirac.isProbabilityMeasure`

English:
instance Measure.dirac.isProbabilityMeasure
  signature: {x : α}
  body: ⟨dirac_apply_of_mem mem_univ x⟩

中文:
实例 Measure.dirac.isProbabilityMeasure
  签名: {x : α}
  定义体: ⟨dirac_apply_of_mem mem_univ x⟩

Depends on / 依赖: dirac_apply_of_mem, mem_univ
-/
instance Measure.dirac.isProbabilityMeasure {x : α} : IsProbabilityMeasure (dirac x) :=
⟨dirac_apply_of_mem mem_univ x⟩

/--
lemma `_root_.HasSum.isProbabilityMeasure_sum_dirac_ennreal` / 引理 `_root_.HasSum.isProbabilityMeasure_sum_dirac_ennreal`

English:
lemma _root_.HasSum.isProbabilityMeasure_sum_dirac_ennreal
  statement: {ι : Type*} {mδ : MeasurableSpace δ}
  proof: by simp [h.tsum_eq]

中文:
引理 _root_.HasSum.isProbabilityMeasure_sum_dirac_ennreal
  结论: {ι : 类型} {mδ : MeasurableSpace δ}
  证明: by simp [h.tsum_eq]

Depends on / 依赖: h.tsum_eq, tsum_eq
-/
lemma _root_.HasSum.isProbabilityMeasure_sum_dirac_ennreal {ι : Type*} {mδ : MeasurableSpace δ}
    {c : ι -> Real>=0∞} {d : ι -> δ} (h : HasSum c 1) :
    IsProbabilityMeasure (Measure.sum fun i => c i • .dirac (d i)) where
  measure_univ := by simp [h.tsum_eq]

/--
lemma `_root_.HasSum.isProbabilityMeasure_sum_dirac_nnreal` / 引理 `_root_.HasSum.isProbabilityMeasure_sum_dirac_nnreal`

English:
lemma _root_.HasSum.isProbabilityMeasure_sum_dirac_nnreal
  statement: {ι : Type*} {mδ : MeasurableSpace δ}
  proof: (ENNReal.hasSum_coe.2 h).isProbabilityMeasure_sum_dirac_ennreal

中文:
引理 _root_.HasSum.isProbabilityMeasure_sum_dirac_nnreal
  结论: {ι : 类型} {mδ : MeasurableSpace δ}
  证明: (ENNReal.hasSum_coe.2 h).isProbabilityMeasure_sum_dirac_ennreal

Depends on / 依赖: ENNReal, ENNReal.hasSum_coe, hasSum_coe, isProbabilityMeasure_sum_dirac_ennreal
-/
lemma _root_.HasSum.isProbabilityMeasure_sum_dirac_nnreal {ι : Type*} {mδ : MeasurableSpace δ}
    {c : ι -> Real>=0} {d : ι -> δ} (h : HasSum c 1) :
    IsProbabilityMeasure (Measure.sum fun i => c i • .dirac (d i)) :=
  (ENNReal.hasSum_coe.2 h).isProbabilityMeasure_sum_dirac_ennreal

/--
lemma `_root_.HasSum.isProbabilityMeasure_sum_dirac` / 引理 `_root_.HasSum.isProbabilityMeasure_sum_dirac`

English:
lemma _root_.HasSum.isProbabilityMeasure_sum_dirac
  statement: {ι : Type*} {mδ : MeasurableSpace δ}
  proof: HasSum.isProbabilityMeasure_sum_dirac_nnreal (by simpa using h2.toNNReal h1)

中文:
引理 _root_.HasSum.isProbabilityMeasure_sum_dirac
  结论: {ι : 类型} {mδ : MeasurableSpace δ}
  证明: HasSum.isProbabilityMeasure_sum_dirac_nnreal (by simpa using h2.toNNReal h1)

Depends on / 依赖: HasSum, HasSum.isProbabilityMeasure_sum_dirac_nnreal, h2.toNNReal, isProbabilityMeasure_sum_dirac_nnreal, toNNReal
-/
lemma _root_.HasSum.isProbabilityMeasure_sum_dirac {ι : Type*} {mδ : MeasurableSpace δ}
    {c : ι -> Real} {d : ι -> δ} (h1 : forall i, 0 <= c i) (h2 : HasSum c 1) :
    IsProbabilityMeasure (Measure.sum fun i => ENNReal.ofReal (c i) • .dirac (d i)) :=
  HasSum.isProbabilityMeasure_sum_dirac_nnreal (by simpa using h2.toNNReal h1)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [hα
  signature: : Nonempty α] : Nonempty {μ : Measure α // IsProbabilityMeasure μ}
  body: ⟨Measure.dirac hα.some, inferInstance⟩

中文:
实例 [hα
  签名: : Nonempty α] : Nonempty {μ : Measure α // IsProbabilityMeasure μ}
  定义体: ⟨Measure.dirac hα.some, inferInstance⟩

Depends on / 依赖: Measure, Measure.dirac
-/
instance [hα : Nonempty α] : Nonempty {μ : Measure α // IsProbabilityMeasure μ} :=
  ⟨Measure.dirac hα.some, inferInstance⟩


/--
Instance `Measure.dirac.instIsFiniteMeasure` / 实例 `Measure.dirac.instIsFiniteMeasure`

English:
instance Measure.dirac.instIsFiniteMeasure
  signature: {a : α}
  body: inferInstance

中文:
实例 Measure.dirac.instIsFiniteMeasure
  签名: {a : α}
  定义体: inferInstance
-/
instance Measure.dirac.instIsFiniteMeasure {a : α} : IsFiniteMeasure (dirac a) := inferInstance
/--
Instance `Measure.dirac.instSigmaFinite` / 实例 `Measure.dirac.instSigmaFinite`

English:
instance Measure.dirac.instSigmaFinite
  signature: {a : α}
  body: inferInstance

中文:
实例 Measure.dirac.instSigmaFinite
  签名: {a : α}
  定义体: inferInstance
-/
instance Measure.dirac.instSigmaFinite {a : α} : SigmaFinite (dirac a) := inferInstance

/--
theorem `dirac_eq_one_iff_mem` / 定理 `dirac_eq_one_iff_mem`

English:
theorem dirac_eq_one_iff_mem
  given: (hs : MeasurableSet s)
  statement: dirac a s = 1 ↔ a in s
  proof: by
  rw [← prob_compl_eq_zero_iff hs]; rw [← mem_ae_iff]
  apply mem_ae_dirac_iff hs

中文:
定理 dirac_eq_one_iff_mem
  条件: (hs : MeasurableSet s)
  结论: dirac a s = 1 ↔ a in s
  证明: by
  rw [← prob_compl_eq_zero_iff hs]; rw [← mem_ae_iff]
  apply mem_ae_dirac_iff hs

Depends on / 依赖: mem_ae_dirac_iff, mem_ae_iff, prob_compl_eq_zero_iff
-/
theorem dirac_eq_one_iff_mem (hs : MeasurableSet s) : dirac a s = 1 ↔ a in s := by
  rw [← prob_compl_eq_zero_iff hs]; rw [← mem_ae_iff]
  apply mem_ae_dirac_iff hs

/--
theorem `dirac_eq_zero_iff_not_mem` / 定理 `dirac_eq_zero_iff_not_mem`

English:
theorem dirac_eq_zero_iff_not_mem
  given: (hs : MeasurableSet s)
  statement: dirac a s = 0 ↔ a ∉ s
  proof: by
  rw [← compl_compl s]; rw [← mem_ae_iff]; rw [notMem_compl_iff]
  apply mem_ae_dirac_iff (MeasurableSet.compl_iff.mpr hs)

中文:
定理 dirac_eq_zero_iff_not_mem
  条件: (hs : MeasurableSet s)
  结论: dirac a s = 0 ↔ a ∉ s
  证明: by
  rw [← compl_compl s]; rw [← mem_ae_iff]; rw [notMem_compl_iff]
  apply mem_ae_dirac_iff (MeasurableSet.compl_iff.mpr hs)

Depends on / 依赖: MeasurableSet, MeasurableSet.compl_iff.mpr, compl_compl, compl_iff, mem_ae_dirac_iff, mem_ae_iff, notMem_compl_iff
-/
theorem dirac_eq_zero_iff_not_mem (hs : MeasurableSet s) : dirac a s = 0 ↔ a ∉ s := by
  rw [← compl_compl s]; rw [← mem_ae_iff]; rw [notMem_compl_iff]
  apply mem_ae_dirac_iff (MeasurableSet.compl_iff.mpr hs)

/--
theorem `restrict_dirac'` / 定理 `restrict_dirac'`

English:
theorem restrict_dirac'
  given: (hs : MeasurableSet s) [Decidable (a in s)]
  proof: by
  split_ifs with has
  · apply restrict_eq_self_of_ae_mem
    rw [ae_dirac_iff] <;> assumption
  · rw [restrict_eq_zero, dirac_apply' _ hs, indicator_of_notMem has]

中文:
定理 restrict_dirac'
  条件: (hs : MeasurableSet s) [Decidable (a in s)]
  证明: by
  split_ifs with has
  · apply restrict_eq_self_of_ae_mem
    rw [ae_dirac_iff] <;> assumption
  · rw [restrict_eq_zero, dirac_apply' _ hs, indicator_of_notMem has]

Depends on / 依赖: ae_dirac_iff, dirac_apply, indicator_of_notMem, restrict_eq_self_of_ae_mem, restrict_eq_zero, split_ifs
-/
theorem restrict_dirac' (hs : MeasurableSet s) [Decidable (a in s)] :
    (Measure.dirac a).restrict s = if a in s then Measure.dirac a else 0 := by
  split_ifs with has
  · apply restrict_eq_self_of_ae_mem
    rw [ae_dirac_iff] <;> assumption
  · rw [restrict_eq_zero, dirac_apply' _ hs, indicator_of_notMem has]

/--
theorem `restrict_dirac` / 定理 `restrict_dirac`

English:
theorem restrict_dirac
  given: [MeasurableSingletonClass α] [Decidable (a in s)]
  proof: by
  split_ifs with has
  · apply restrict_eq_self_of_ae_mem
    rwa [ae_dirac_eq]
  · rw [restrict_eq_zero, dirac_apply, indicator_of_notMem has]

中文:
定理 restrict_dirac
  条件: [MeasurableSingletonClass α] [Decidable (a in s)]
  证明: by
  split_ifs with has
  · apply restrict_eq_self_of_ae_mem
    rwa [ae_dirac_eq]
  · rw [restrict_eq_zero, dirac_apply, indicator_of_notMem has]

Depends on / 依赖: ae_dirac_eq, dirac_apply, indicator_of_notMem, restrict_eq_self_of_ae_mem, restrict_eq_zero, split_ifs
-/
theorem restrict_dirac [MeasurableSingletonClass α] [Decidable (a in s)] :
    (Measure.dirac a).restrict s = if a in s then Measure.dirac a else 0 := by
  split_ifs with has
  · apply restrict_eq_self_of_ae_mem
    rwa [ae_dirac_eq]
  · rw [restrict_eq_zero, dirac_apply, indicator_of_notMem has]

/--
lemma `mutuallySingular_dirac` / 引理 `mutuallySingular_dirac`

English:
lemma mutuallySingular_dirac
  statement: [MeasurableSingletonClass α] (x : α) (μ : Measure α)
  proof: ⟨{x}ᶜ, (MeasurableSet.singleton x).compl, by simp, by simp⟩

中文:
引理 mutuallySingular_dirac
  结论: [MeasurableSingletonClass α] (x : α) (μ : Measure α)
  证明: ⟨{x}ᶜ, (MeasurableSet.singleton x).compl, by simp, by simp⟩

Depends on / 依赖: MeasurableSet, MeasurableSet.singleton, singleton
-/
lemma mutuallySingular_dirac [MeasurableSingletonClass α] (x : α) (μ : Measure α)
    [NullSingletonClass μ] :
    Measure.dirac x ⟂ₘ μ :=
  ⟨{x}ᶜ, (MeasurableSet.singleton x).compl, by simp, by simp⟩

section dirac_injective

/--
lemma `dirac_eq_dirac_iff_forall_mem_iff_mem` / 引理 `dirac_eq_dirac_iff_forall_mem_iff_mem`

English:
lemma dirac_eq_dirac_iff_forall_mem_iff_mem
  given: {x y : α}
  proof: by
  constructor
  · intro h A A_mble
    have obs := congr_arg (fun μ => μ A) h
    simp only [Measure.dirac_apply' _ A_mble] at obs
    by_cases x_in_A : x in A
    · simpa only [x_in_A, indicator_of_mem, Pi.one_apply, true_iff, Eq.comm (a := (1 : Real>=0∞)),
                  indicator_eq_one_iff

中文:
引理 dirac_eq_dirac_iff_forall_mem_iff_mem
  条件: {x y : α}
  证明: by
  constructor
  · intro h A A_mble
    have obs := congr_arg (fun μ => μ A) h
    simp only [Measure.dirac_apply' _ A_mble] at obs
    by_cases x_in_A : x in A
    · simpa only [x_in_A, indicator_of_mem, Pi.one_apply, true_iff, Eq.comm (a := (1 : Real>=0∞)),
                  indicator_eq_one_iff

Depends on / 依赖: A_mble, Eq.comm, Measure, Measure.dirac_apply, Pi.one_apply, congr_arg, dirac_apply, false_iff, imp_false, indicator_apply_eq_zero, indicator_eq_one_iff_mem, indicator_of_mem, indicator_of_notMem, not_false_eq_true, one_apply, one_ne_zero, true_iff, x_in_A
-/
lemma dirac_eq_dirac_iff_forall_mem_iff_mem {x y : α} :
    Measure.dirac x = Measure.dirac y ↔ forall A, MeasurableSet A -> (x in A ↔ y in A) := by
  constructor
  · intro h A A_mble
    have obs := congr_arg (fun μ => μ A) h
    simp only [Measure.dirac_apply' _ A_mble] at obs
    by_cases x_in_A : x in A
    · simpa only [x_in_A, indicator_of_mem, Pi.one_apply, true_iff, Eq.comm (a := (1 : Real>=0∞)),
                  indicator_eq_one_iff_mem] using obs
    · simpa only [x_in_A, indicator_of_notMem, Eq.comm (a := (0 : Real>=0∞)), indicator_apply_eq_zero,
                  false_iff, not_false_eq_true, Pi.one_apply, one_ne_zero, imp_false] using obs
  · intro h
    ext A A_mble
    by_cases x_in_A : x in A
    · simp only [Measure.dirac_apply' _ A_mble, x_in_A, indicator_of_mem, Pi.one_apply,
                 (h A A_mble).mp x_in_A]
    · have y_notin_A : y ∉ A := by simp_all only [not_false_eq_true]
      simp only [Measure.dirac_apply' _ A_mble, x_in_A, y_notin_A,
                 not_false_eq_true, indicator_of_notMem]

/--
lemma `dirac_ne_dirac_iff_exists_measurableSet` / 引理 `dirac_ne_dirac_iff_exists_measurableSet`

English:
lemma dirac_ne_dirac_iff_exists_measurableSet
  given: {x y : α}
  proof: by
  apply not_iff_not.mp
  simp only [ne_eq, not_not, not_exists, not_and, dirac_eq_dirac_iff_forall_mem_iff_mem]
  refine ⟨fun h A A_mble => by simp only [h A A_mble, imp_self], fun h A A_mble => ?_⟩
  by_cases x_in_A : x in A
  · simp only [x_in_A, h A A_mble x_in_A]
  · simpa only [x_in_A, false

中文:
引理 dirac_ne_dirac_iff_exists_measurableSet
  条件: {x y : α}
  证明: by
  apply not_iff_not.mp
  simp only [ne_eq, not_not, not_exists, not_and, dirac_eq_dirac_iff_forall_mem_iff_mem]
  refine ⟨fun h A A_mble => by simp only [h A A_mble, imp_self], fun h A A_mble => ?_⟩
  by_cases x_in_A : x in A
  · simp only [x_in_A, h A A_mble x_in_A]
  · simpa only [x_in_A, false

Depends on / 依赖: A_mble, MeasurableSet, MeasurableSet.compl_iff.mpr, compl_iff, dirac_eq_dirac_iff_forall_mem_iff_mem, false_iff, imp_self, ne_eq, not_and, not_exists, not_iff_not, not_iff_not.mp, not_not, x_in_A
-/
lemma dirac_ne_dirac_iff_exists_measurableSet {x y : α} :
    Measure.dirac x != Measure.dirac y ↔ exists A, MeasurableSet A ∧ x in A ∧ y ∉ A := by
  apply not_iff_not.mp
  simp only [ne_eq, not_not, not_exists, not_and, dirac_eq_dirac_iff_forall_mem_iff_mem]
  refine ⟨fun h A A_mble => by simp only [h A A_mble, imp_self], fun h A A_mble => ?_⟩
  by_cases x_in_A : x in A
  · simp only [x_in_A, h A A_mble x_in_A]
  · simpa only [x_in_A, false_iff] using! h Aᶜ (MeasurableSet.compl_iff.mpr A_mble) x_in_A

open MeasurableSpace
/--
lemma `dirac_ne_dirac` / 引理 `dirac_ne_dirac`

English:
lemma dirac_ne_dirac
  given: [SeparatesPoints α] {x y : α} (x_ne_y : x != y)
  proof: by
  obtain ⟨A, A_mble, x_in_A, y_notin_A⟩ := exists_measurableSet_of_ne x_ne_y
  exact dirac_ne_dirac_iff_exists_measurableSet.mpr ⟨A, A_mble, x_in_A, y_notin_A⟩

中文:
引理 dirac_ne_dirac
  条件: [SeparatesPoints α] {x y : α} (x_ne_y : x != y)
  证明: by
  obtain ⟨A, A_mble, x_in_A, y_notin_A⟩ := exists_measurableSet_of_ne x_ne_y
  exact dirac_ne_dirac_iff_exists_measurableSet.mpr ⟨A, A_mble, x_in_A, y_notin_A⟩

Depends on / 依赖: A_mble, dirac_ne_dirac_iff_exists_measurableSet, dirac_ne_dirac_iff_exists_measurableSet.mpr, exists_measurableSet_of_ne, x_in_A, x_ne_y, y_notin_A
-/
lemma dirac_ne_dirac [SeparatesPoints α] {x y : α} (x_ne_y : x != y) :
    Measure.dirac x != Measure.dirac y := by
  obtain ⟨A, A_mble, x_in_A, y_notin_A⟩ := exists_measurableSet_of_ne x_ne_y
  exact dirac_ne_dirac_iff_exists_measurableSet.mpr ⟨A, A_mble, x_in_A, y_notin_A⟩

/--
lemma `dirac_ne_dirac_iff` / 引理 `dirac_ne_dirac_iff`

English:
lemma dirac_ne_dirac_iff
  given: [SeparatesPoints α] {x y : α}
  proof: ⟨fun h x_eq_y => h congrArg dirac x_eq_y, fun h => dirac_ne_dirac h⟩

中文:
引理 dirac_ne_dirac_iff
  条件: [SeparatesPoints α] {x y : α}
  证明: ⟨fun h x_eq_y => h congrArg dirac x_eq_y, fun h => dirac_ne_dirac h⟩

Depends on / 依赖: dirac_ne_dirac, x_eq_y
-/
lemma dirac_ne_dirac_iff [SeparatesPoints α] {x y : α} :
    Measure.dirac x != Measure.dirac y ↔ x != y :=
⟨fun h x_eq_y => h congrArg dirac x_eq_y, fun h => dirac_ne_dirac h⟩

/--
lemma `dirac_eq_dirac_iff` / 引理 `dirac_eq_dirac_iff`

English:
lemma dirac_eq_dirac_iff
  given: [SeparatesPoints α] {x y : α}
  proof: not_iff_not.mp dirac_ne_dirac_iff

中文:
引理 dirac_eq_dirac_iff
  条件: [SeparatesPoints α] {x y : α}
  证明: not_iff_not.mp dirac_ne_dirac_iff

Depends on / 依赖: dirac_ne_dirac_iff, not_iff_not, not_iff_not.mp
-/
lemma dirac_eq_dirac_iff [SeparatesPoints α] {x y : α} :
    Measure.dirac x = Measure.dirac y ↔ x = y := not_iff_not.mp dirac_ne_dirac_iff

/--
lemma `injective_dirac` / 引理 `injective_dirac`

English:
lemma injective_dirac
  given: [SeparatesPoints α]
  proof: fun x y x_ne_y => by rwa [← dirac_eq_dirac_iff]

中文:
引理 injective_dirac
  条件: [SeparatesPoints α]
  证明: fun x y x_ne_y => by rwa [← dirac_eq_dirac_iff]

Depends on / 依赖: dirac_eq_dirac_iff, x_ne_y
-/
lemma injective_dirac [SeparatesPoints α] :
    Function.Injective (fun (x : α) => dirac x) := fun x y x_ne_y => by rwa [← dirac_eq_dirac_iff]

end dirac_injective

end MeasureTheory

namespace MeasureTheory.Measure
variable {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  [MeasurableSingletonClass α] {f : β -> α} {μ : Measure α} {s : Finset α} {a₁ a₂ : α}

/--
lemma `ae_mem_finset_iff` / 引理 `ae_mem_finset_iff`

English:
lemma ae_mem_finset_iff
  statement: (forallᵐ a ∂μ, a in s) ↔ μ = ∑ a in s, μ {a} • .dirac a where
  proof: by
    ext t ht
    rw [← measure_sdiff_null (s := t) hμ]
    dsimp
    rw [Set.sdiff_compl]; rw [← (s : Set α).biUnion_of_singleton]
    simp_rw [Finset.mem_coe, Set.inter_iUnion]
    rw [measure_biUnion_finset (fun i hi j hj hij => .inter_left' _ <| .inter_right' _ ?_)
      (by measurability)]
  

中文:
引理 ae_mem_finset_iff
  结论: (对任意ᵐ a ∂μ, a in s) ↔ μ = ∑ a in s, μ {a} • .dirac a where
  证明: by
    ext t ht
    rw [← measure_sdiff_null (s := t) hμ]
    dsimp
    rw [Set.sdiff_compl]; rw [← (s : Set α).biUnion_of_singleton]
    simp_rw [Finset.mem_coe, Set.inter_iUnion]
    rw [measure_biUnion_finset (fun i hi j hj hij => .inter_left' _ <| .inter_right' _ ?_)
      (by measurability)]
  

Depends on / 依赖: Finset, Finset.mem_coe, Finset.sum_apply, Set.inter_iUnion, Set.sdiff_compl, ae_finsetSum_measure_iff, ae_smul_measure, biUnion_of_singleton, coe_finsetSum, inter_iUnion, inter_left, inter_right, measurability, measure_biUnion_finset, measure_sdiff_null, mem_coe, sdiff_compl, simp_rw, smul_apply, sum_apply
-/
lemma ae_mem_finset_iff : (forallᵐ a ∂μ, a in s) ↔ μ = ∑ a in s, μ {a} • .dirac a where
  mp hμ := by
    ext t ht
    rw [← measure_sdiff_null (s := t) hμ]
    dsimp
    rw [Set.sdiff_compl]; rw [← (s : Set α).biUnion_of_singleton]
    simp_rw [Finset.mem_coe, Set.inter_iUnion]
    rw [measure_biUnion_finset (fun i hi j hj hij => .inter_left' _ <| .inter_right' _ ?_)
      (by measurability)]
    · simp only [coe_finsetSum, Finset.sum_apply, smul_apply]
      congr with a
      by_cases ha : a in t <;> simp [*]
    simpa
  mpr hμ := by rw [hμ, ae_finsetSum_measure_iff]; exact fun i hi => ae_smul_measure (by simpa) _

/--
lemma `ae_eq_or_eq_iff_eq_dirac_add_dirac` / 引理 `ae_eq_or_eq_iff_eq_dirac_add_dirac`

English:
lemma ae_eq_or_eq_iff_eq_dirac_add_dirac
  given: (ha : a₁ != a₂)
  proof: by
  -- FIXME: Why does `simpa using ...` not work?
  convert! ae_mem_finset_iff (s := .cons a₁ { a₂ } <| by simpa) <;> simp

中文:
引理 ae_eq_or_eq_iff_eq_dirac_add_dirac
  条件: (ha : a₁ != a₂)
  证明: by
  -- FIXME: Why does `simpa using ...` not work?
  convert! ae_mem_finset_iff (s := .cons a₁ { a₂ } <| by simpa) <;> simp
-/
lemma ae_eq_or_eq_iff_eq_dirac_add_dirac (ha : a₁ != a₂) :
    (forallᵐ a ∂μ, a = a₁ ∨ a = a₂) ↔ μ = μ {a₁} • .dirac a₁ + μ {a₂} • .dirac a₂ := by
  -- FIXME: Why does `simpa using ...` not work?
  convert! ae_mem_finset_iff (s := .cons a₁ { a₂ } <| by simpa) <;> simp

/--
lemma `ae_mem_finset_iff_map_eq_sum_dirac` / 引理 `ae_mem_finset_iff_map_eq_sum_dirac`

English:
lemma ae_mem_finset_iff_map_eq_sum_dirac
  given: {μ : Measure β} (hf : AEMeasurable f μ)
  proof: by
  rw [← ae_map_iff hf (by measurability)]; rw [ae_mem_finset_iff]
  simp [map_apply₀ hf]

中文:
引理 ae_mem_finset_iff_map_eq_sum_dirac
  条件: {μ : Measure β} (hf : AEMeasurable f μ)
  证明: by
  rw [← ae_map_iff hf (by measurability)]; rw [ae_mem_finset_iff]
  simp [map_apply₀ hf]

Depends on / 依赖: ae_map_iff, ae_mem_finset_iff, measurability
-/
lemma ae_mem_finset_iff_map_eq_sum_dirac {μ : Measure β} (hf : AEMeasurable f μ) :
    (forallᵐ b ∂μ, f b in s) ↔ μ.map f = ∑ a in s, μ (f ⁻¹' {a}) • .dirac a := by
  rw [← ae_map_iff hf (by measurability)]; rw [ae_mem_finset_iff]
  simp [map_apply₀ hf]

/--
lemma `ae_eq_or_eq_iff_map_eq_dirac_add_dirac` / 引理 `ae_eq_or_eq_iff_map_eq_dirac_add_dirac`

English:
lemma ae_eq_or_eq_iff_map_eq_dirac_add_dirac
  statement: {μ : Measure β} (hf : AEMeasurable f μ)
  proof: by
  -- FIXME: Why does `simpa using ...` not work?
  convert! ae_mem_finset_iff_map_eq_sum_dirac (s := .cons a₁ { a₂ } <| by simpa) hf <;> simp

中文:
引理 ae_eq_or_eq_iff_map_eq_dirac_add_dirac
  结论: {μ : Measure β} (hf : AEMeasurable f μ)
  证明: by
  -- FIXME: Why does `simpa using ...` not work?
  convert! ae_mem_finset_iff_map_eq_sum_dirac (s := .cons a₁ { a₂ } <| by simpa) hf <;> simp
-/
lemma ae_eq_or_eq_iff_map_eq_dirac_add_dirac {μ : Measure β} (hf : AEMeasurable f μ)
    (ha : a₁ != a₂) :
    (forallᵐ b ∂μ, f b = a₁ ∨ f b = a₂) ↔
      μ.map f = μ (f ⁻¹' {a₁}) • .dirac a₁ + μ (f ⁻¹' {a₂}) • .dirac a₂ := by
  -- FIXME: Why does `simpa using ...` not work?
  convert! ae_mem_finset_iff_map_eq_sum_dirac (s := .cons a₁ { a₂ } <| by simpa) hf <;> simp

end MeasureTheory.Measure
