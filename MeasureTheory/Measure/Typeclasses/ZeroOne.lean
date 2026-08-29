/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/

module

public import Mathlib.MeasureTheory.Constructions.Polish.Basic
public import Mathlib.MeasureTheory.Measure.Dirac

/-!

We introduce the typeclass `IsZeroOneMeasure` for measures that only take the values `0` and `1`.

## Main definitions

* `IsZeroOneMeasure`: a measure is a zero-one measure if it only takes the values `0`
  or `1`.

## Main statements

* `exists_eq_dirac`: in a standard Borel space, a zero-one measure that is not the zero measure is
  a Dirac measure.

-/

@[expose] public section

open Set

namespace MeasureTheory

variable {α : Type*} {mα : MeasurableSpace α}

/--
Definition of `IsZeroOneMeasure` / `IsZeroOneMeasure` 的定义

English:
class IsZeroOneMeasure
  parameters: (μ : Measure α)
  axioms and operations (1):
    - zero_one₀ : forall ⦃s⦄, MeasurableSet s -> μ s = 0 ∨ μ s = 1

中文:
类 是ZeroOneMeasure
  参数: (μ : 测度 α)
  公理与运算 (1 个):
    - zero_one₀ : 对任意 ⦃s⦄, 可测集 s -> μ s = 0 ∨ μ s = 1
-/
class IsZeroOneMeasure (μ : Measure α) : Prop where
  zero_one₀ : forall ⦃s⦄, MeasurableSet s -> μ s = 0 ∨ μ s = 1

/--
lemma `Measure.zero_one` / 引理 `Measure.zero_one`

English:
lemma Measure.zero_one
  given: (μ : Measure α) [IsZeroOneMeasure μ]
  proof: by
  intro s
  by_cases hs : MeasurableSet s
  · exact IsZeroOneMeasure.zero_one₀ hs
  · obtain ⟨t, _, mt, ht⟩ := exists_measurable_superset μ s
    rw [← ht]
    exact IsZeroOneMeasure.zero_one₀ mt

中文:
引理 测度.zero_one
  条件: (μ : 测度 α) [是ZeroOneMeasure μ]
  证明: by
  intro s
  by_cases hs : MeasurableSet s
  · exact IsZeroOneMeasure.zero_one₀ hs
  · obtain ⟨t, _, mt, ht⟩ := exists_measurable_superset μ s
    rw [← ht]
    exact IsZeroOneMeasure.zero_one₀ mt

Depends on / 依赖: IsZeroOneMeasure, IsZeroOneMeasure.zero_one, MeasurableSet, exists_measurable_superset
-/
lemma Measure.zero_one (μ : Measure α) [IsZeroOneMeasure μ] :
    forall s, μ s = 0 ∨ μ s = 1 := by
  intro s
  by_cases hs : MeasurableSet s
  · exact IsZeroOneMeasure.zero_one₀ hs
  · obtain ⟨t, _, mt, ht⟩ := exists_measurable_superset μ s
    rw [← ht]
    exact IsZeroOneMeasure.zero_one₀ mt

variable {μ : Measure α} [IsZeroOneMeasure μ]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsZeroOrProbabilityMeasure μ
  body: μ.zero_one univ

中文:
实例 :
  签名: 是ZeroOrProbabilityMeasure μ
  定义体: μ.zero_one univ

Depends on / 依赖: zero_one
-/
instance : IsZeroOrProbabilityMeasure μ where
  measure_univ := μ.zero_one univ

namespace IsZeroOneMeasure

/--
lemma `exists_measure_eq_one_iff_measure_univ_eq_one` / 引理 `exists_measure_eq_one_iff_measure_univ_eq_one`

English:
lemma exists_measure_eq_one_iff_measure_univ_eq_one
  statement: (exists s, μ s = 1) ↔ μ univ = 1
  proof: by
  constructor
  · rintro ⟨s, h⟩
    rcases μ.zero_one univ with (h₀ | h₁)
· have := measure_mono (μ := μ) subset_univ s
      rw [h] at this
      simp_all
    · exact h₁
  · intro h
    exact ⟨univ, h⟩

中文:
引理 存在_measure_eq_one_iff_measure_univ_eq_one
  结论: (存在 s, μ s = 1) ↔ μ univ = 1
  证明: by
  constructor
  · rintro ⟨s, h⟩
    rcases μ.zero_one univ with (h₀ | h₁)
· have := measure_mono (μ := μ) subset_univ s
      rw [h] at this
      simp_all
    · exact h₁
  · intro h
    exact ⟨univ, h⟩

Depends on / 依赖: measure_mono, subset_univ, zero_one
-/
lemma exists_measure_eq_one_iff_measure_univ_eq_one : (exists s, μ s = 1) ↔ μ univ = 1 := by
  constructor
  · rintro ⟨s, h⟩
    rcases μ.zero_one univ with (h₀ | h₁)
· have := measure_mono (μ := μ) subset_univ s
      rw [h] at this
      simp_all
    · exact h₁
  · intro h
    exact ⟨univ, h⟩

/--
lemma `measure_univ` / 引理 `measure_univ`

English:
lemma measure_univ
  given: {s : Set α} (hμs : μ s = 1)
  statement: μ univ = 1
  proof: (exists_measure_eq_one_iff_measure_univ_eq_one).mp ⟨s, hμs⟩

中文:
引理 measure_univ
  条件: {s : 集合 α} (hμs : μ s = 1)
  结论: μ univ = 1
  证明: (exists_measure_eq_one_iff_measure_univ_eq_one).mp ⟨s, hμs⟩

Depends on / 依赖: exists_measure_eq_one_iff_measure_univ_eq_one
-/
lemma measure_univ {s : Set α} (hμs : μ s = 1) : μ univ = 1 :=
  (exists_measure_eq_one_iff_measure_univ_eq_one).mp ⟨s, hμs⟩

/--
lemma `measure_inter_eq_one` / 引理 `measure_inter_eq_one`

English:
lemma measure_inter_eq_one
  statement: {s t : Set α} (hs : MeasurableSet s) (ht : MeasurableSet t)
  proof: by
  have : μ (s inter t) <= μ s := measure_mono inter_subset_left
  have : μ (s inter t) <= μ t := measure_mono inter_subset_right
  rcases μ.zero_one s with (_ | hμs)
    <;> rcases μ.zero_one t with (_ | hμt)
    <;> rcases μ.zero_one (s inter t)
  all_goals try simp_all only [zero_le, zero_ne_one]
  suffices μ (s inter t)ᶜ <= 0 by
    rw [measure_compl (hs.inter ht) (by simp)]; rw [measure_univ ‹_›] at this
    simp_all
  calc
  _ = μ (sᶜ union tᶜ) := by simp [compl_inter]
  _ <= μ sᶜ + μ tᶜ := measure_union_le _ _
  _ <= 0 := by
    rw [measure_compl hs (by simp)]; rw [measure_univ hμs]; rw [hμs]; rw [tsub_self]; rw [measure_compl ht (by simp)]; rw [measure_univ hμt]; rw [hμt]; rw [tsub_self]
    simp

中文:
引理 measure_inter_eq_one
  结论: {s t : 集合 α} (hs : 可测集 s) (ht : 可测集 t)
  证明: by
  have : μ (s inter t) <= μ s := measure_mono inter_subset_left
  have : μ (s inter t) <= μ t := measure_mono inter_subset_right
  rcases μ.zero_one s with (_ | hμs)
    <;> rcases μ.zero_one t with (_ | hμt)
    <;> rcases μ.zero_one (s inter t)
  all_goals try simp_all only [zero_le, zero_ne_one]
  suffices μ (s inter t)ᶜ <= 0 by
    rw [measure_compl (hs.inter ht) (by simp)]; rw [measure_univ ‹_›] at this
    simp_all
  calc
  _ = μ (sᶜ union tᶜ) := by simp [compl_inter]
  _ <= μ sᶜ + μ tᶜ := measure_union_le _ _
  _ <= 0 := by
    rw [measure_compl hs (by simp)]; rw [measure_univ hμs]; rw [hμs]; rw [tsub_self]; rw [measure_compl ht (by simp)]; rw [measure_univ hμt]; rw [hμt]; rw [tsub_self]
    simp

Depends on / 依赖: all_goals, compl_inter, hs.inter, inter_subset_left, inter_subset_right, measure_compl, measure_mono, measure_union_le, measure_univ, zero_le, zero_ne_one, zero_one
-/
lemma measure_inter_eq_one {s t : Set α} (hs : MeasurableSet s) (ht : MeasurableSet t)
    (hμs : μ s = 1) (hμt : μ t = 1) : μ (s inter t) = 1 := by
  have : μ (s inter t) <= μ s := measure_mono inter_subset_left
  have : μ (s inter t) <= μ t := measure_mono inter_subset_right
  rcases μ.zero_one s with (_ | hμs)
    <;> rcases μ.zero_one t with (_ | hμt)
    <;> rcases μ.zero_one (s inter t)
  all_goals try simp_all only [zero_le, zero_ne_one]
  suffices μ (s inter t)ᶜ <= 0 by
    rw [measure_compl (hs.inter ht) (by simp)]; rw [measure_univ ‹_›] at this
    simp_all
  calc
  _ = μ (sᶜ union tᶜ) := by simp [compl_inter]
  _ <= μ sᶜ + μ tᶜ := measure_union_le _ _
  _ <= 0 := by
    rw [measure_compl hs (by simp)]; rw [measure_univ hμs]; rw [hμs]; rw [tsub_self]; rw [measure_compl ht (by simp)]; rw [measure_univ hμt]; rw [hμt]; rw [tsub_self]
    simp

/--
lemma `measure_inter_eq_prod` / 引理 `measure_inter_eq_prod`

English:
lemma measure_inter_eq_prod
  given: {s t : Set α} (hs : MeasurableSet s) (ht : MeasurableSet t)
  proof: by
  have : μ (s inter t) <= μ s := measure_mono inter_subset_left
  have : μ (s inter t) <= μ t := measure_mono inter_subset_right
  cases μ.zero_one s <;> cases μ.zero_one t <;> cases μ.zero_one (s inter t)
  all_goals try simp_all [measure_inter_eq_one]

中文:
引理 measure_inter_eq_prod
  条件: {s t : 集合 α} (hs : 可测集 s) (ht : 可测集 t)
  证明: by
  have : μ (s inter t) <= μ s := measure_mono inter_subset_left
  have : μ (s inter t) <= μ t := measure_mono inter_subset_right
  cases μ.zero_one s <;> cases μ.zero_one t <;> cases μ.zero_one (s inter t)
  all_goals try simp_all [measure_inter_eq_one]

Depends on / 依赖: all_goals, inter_subset_left, inter_subset_right, measure_inter_eq_one, measure_mono, zero_one
-/
lemma measure_inter_eq_prod {s t : Set α} (hs : MeasurableSet s) (ht : MeasurableSet t) :
    μ (s inter t) = μ s * μ t := by
  have : μ (s inter t) <= μ s := measure_mono inter_subset_left
  have : μ (s inter t) <= μ t := measure_mono inter_subset_right
  cases μ.zero_one s <;> cases μ.zero_one t <;> cases μ.zero_one (s inter t)
  all_goals try simp_all [measure_inter_eq_one]

/--
theorem `exists_eq_dirac` / 定理 `exists_eq_dirac`

English:
theorem exists_eq_dirac
  given: [StandardBorelSpace α] [NeZero μ]
  statement: exists x₀, μ = Measure.dirac x₀
  proof: by
  have : IsProbabilityMeasure μ := by
    rcases IsZeroOrProbabilityMeasure.measure_univ (μ := μ) with (h | h)
    · simp_all
    · exact ⟨h⟩
  obtain ⟨A, hAm, hAsep⟩ := exists_seq_separating (α := α) MeasurableSet.univ univ
  let B := fun n => if h : μ (A n) = 1 then A n else (A n)ᶜ
  have mBn : MeasurableSet (⋂ n, B n) := by
    refine MeasurableSet.iInter fun n => ?_
    simp only [dite_eq_ite, B]
    split_ifs
    · exact hAm n
    · exact (hAm n).compl
  have hBn : μ (⋂ n, B n) = 1 := by
    refine (prob_compl_eq_zero_iff mBn).mp ?_
    simp only [dite_eq_ite, compl_iInter, measure_iUnion_null_iff, B]
    intro n
    split_ifs with h
    · simp_all
    · rw [compl_compl]
      rcases μ.zero_one (A n) with (h₀ | h₁)
      · exact h₀
      · simp_all
  obtain ⟨x₀, hx₀⟩ : exists x₀, ⋂ n, B n = {x₀} := by
    simp_rw [eq_singleton_iff_unique_mem]
    have neBn : (⋂ n, B n).Nonempty := by
      by_contra! h
      rw [h] at hBn
      simp_all
    refine ⟨neBn.some, neBn.some_mem, fun y hy => ?_⟩
    refine hAsep y (by trivial) neBn.some (by trivial) fun n => ?_
    have hsome := neBn.some_mem
    simp only [dite_eq_ite, mem_iInter, B] at hsome hy
    specialize hsome n
    specialize hy n
    constructor
    · intro h
      split_ifs at hy with hμAn
      · simpa [hμAn] using! hsome
      · contradiction
    · intro h
      split_ifs at hsome with hμAn
      · simpa [hμAn] using! hy
      · contradiction
  use x₀
  ext s hs
  by_cases h : x₀ in s
  · simp [h]
    have : μ {x₀} <= μ s := measure_mono (μ := μ) (by grind)
    rw [← hx₀]; rw [hBn] at this
    simp_all
  · simp [h]
    have : μ s <= μ {x₀}ᶜ := measure_mono (μ := μ) (by grind)
    rw [← hx₀]; rw [measure_compl mBn (by simp)]; rw [MeasureTheory.measure_univ]; rw [hBn] at this
    simp_all

中文:
定理 存在_eq_dirac
  条件: [StandardBorel空间 α] [NeZero μ]
  结论: 存在 x₀, μ = 测度.dirac x₀
  证明: by
  have : IsProbabilityMeasure μ := by
    rcases IsZeroOrProbabilityMeasure.measure_univ (μ := μ) with (h | h)
    · simp_all
    · exact ⟨h⟩
  obtain ⟨A, hAm, hAsep⟩ := exists_seq_separating (α := α) MeasurableSet.univ univ
  let B := fun n => if h : μ (A n) = 1 then A n else (A n)ᶜ
  have mBn : MeasurableSet (⋂ n, B n) := by
    refine MeasurableSet.iInter fun n => ?_
    simp only [dite_eq_ite, B]
    split_ifs
    · exact hAm n
    · exact (hAm n).compl
  have hBn : μ (⋂ n, B n) = 1 := by
    refine (prob_compl_eq_zero_iff mBn).mp ?_
    simp only [dite_eq_ite, compl_iInter, measure_iUnion_null_iff, B]
    intro n
    split_ifs with h
    · simp_all
    · rw [compl_compl]
      rcases μ.zero_one (A n) with (h₀ | h₁)
      · exact h₀
      · simp_all
  obtain ⟨x₀, hx₀⟩ : exists x₀, ⋂ n, B n = {x₀} := by
    simp_rw [eq_singleton_iff_unique_mem]
    have neBn : (⋂ n, B n).Nonempty := by
      by_contra! h
      rw [h] at hBn
      simp_all
    refine ⟨neBn.some, neBn.some_mem, fun y hy => ?_⟩
    refine hAsep y (by trivial) neBn.some (by trivial) fun n => ?_
    have hsome := neBn.some_mem
    simp only [dite_eq_ite, mem_iInter, B] at hsome hy
    specialize hsome n
    specialize hy n
    constructor
    · intro h
      split_ifs at hy with hμAn
      · simpa [hμAn] using! hsome
      · contradiction
    · intro h
      split_ifs at hsome with hμAn
      · simpa [hμAn] using! hy
      · contradiction
  use x₀
  ext s hs
  by_cases h : x₀ in s
  · simp [h]
    have : μ {x₀} <= μ s := measure_mono (μ := μ) (by grind)
    rw [← hx₀]; rw [hBn] at this
    simp_all
  · simp [h]
    have : μ s <= μ {x₀}ᶜ := measure_mono (μ := μ) (by grind)
    rw [← hx₀]; rw [measure_compl mBn (by simp)]; rw [MeasureTheory.measure_univ]; rw [hBn] at this
    simp_all

Depends on / 依赖: IsProbabilityMeasure, IsZeroOrProbabilityMeasure, IsZeroOrProbabilityMeasure.measure_univ, MeasurableSet, MeasurableSet.iInter, MeasurableSet.univ, dite_eq_ite, exists_seq_separating, iInter, measure_univ, prob_compl_eq_zero_iff, split_ifs
-/
theorem exists_eq_dirac [StandardBorelSpace α] [NeZero μ] : exists x₀, μ = Measure.dirac x₀ := by
  have : IsProbabilityMeasure μ := by
    rcases IsZeroOrProbabilityMeasure.measure_univ (μ := μ) with (h | h)
    · simp_all
    · exact ⟨h⟩
  obtain ⟨A, hAm, hAsep⟩ := exists_seq_separating (α := α) MeasurableSet.univ univ
  let B := fun n => if h : μ (A n) = 1 then A n else (A n)ᶜ
  have mBn : MeasurableSet (⋂ n, B n) := by
    refine MeasurableSet.iInter fun n => ?_
    simp only [dite_eq_ite, B]
    split_ifs
    · exact hAm n
    · exact (hAm n).compl
  have hBn : μ (⋂ n, B n) = 1 := by
    refine (prob_compl_eq_zero_iff mBn).mp ?_
    simp only [dite_eq_ite, compl_iInter, measure_iUnion_null_iff, B]
    intro n
    split_ifs with h
    · simp_all
    · rw [compl_compl]
      rcases μ.zero_one (A n) with (h₀ | h₁)
      · exact h₀
      · simp_all
  obtain ⟨x₀, hx₀⟩ : exists x₀, ⋂ n, B n = {x₀} := by
    simp_rw [eq_singleton_iff_unique_mem]
    have neBn : (⋂ n, B n).Nonempty := by
      by_contra! h
      rw [h] at hBn
      simp_all
    refine ⟨neBn.some, neBn.some_mem, fun y hy => ?_⟩
    refine hAsep y (by trivial) neBn.some (by trivial) fun n => ?_
    have hsome := neBn.some_mem
    simp only [dite_eq_ite, mem_iInter, B] at hsome hy
    specialize hsome n
    specialize hy n
    constructor
    · intro h
      split_ifs at hy with hμAn
      · simpa [hμAn] using! hsome
      · contradiction
    · intro h
      split_ifs at hsome with hμAn
      · simpa [hμAn] using! hy
      · contradiction
  use x₀
  ext s hs
  by_cases h : x₀ in s
  · simp [h]
    have : μ {x₀} <= μ s := measure_mono (μ := μ) (by grind)
    rw [← hx₀]; rw [hBn] at this
    simp_all
  · simp [h]
    have : μ s <= μ {x₀}ᶜ := measure_mono (μ := μ) (by grind)
    rw [← hx₀]; rw [measure_compl mBn (by simp)]; rw [MeasureTheory.measure_univ]; rw [hBn] at this
    simp_all

end IsZeroOneMeasure

end MeasureTheory
