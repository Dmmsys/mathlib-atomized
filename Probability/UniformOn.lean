/-
Copyright (c) 2022 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying, Bhavik Mehta
-/
module

public import Mathlib.Probability.ConditionalProbability
public import Mathlib.MeasureTheory.Measure.Count
public import Mathlib.MeasureTheory.Constructions.Pi

import Mathlib.Data.Fintype.Pi

/-!
# Classical probability

The classical formulation of probability states that the probability of an event occurring in a
finite probability space is the ratio of that event to all possible events.
This notion can be expressed with measure theory using
the counting measure. In particular, given the sets `s` and `t`, we define the probability of `t`
occurring in `s` to be `|s|⁻¹ * |s ∩ t|`. With this definition, we recover the probability over
the entire sample space when `s = Set.univ`.

Classical probability is often used in combinatorics and we prove some useful lemmas in this file
for that purpose.

## Main definition

* `ProbabilityTheory.uniformOn`: given a set `s`, `uniformOn s` is the counting measure
  conditioned on `s`. This is a probability measure when `s` is finite and nonempty.

## Notes

The original aim of this file is to provide a measure-theoretic method of describing the
probability an element of a set `s` satisfies some predicate `P`. Our current formulation still
allows us to describe this by abusing the definitional equality of sets and predicates by simply
writing `uniformOn s P`. We should avoid this however as none of the lemmas are written for
predicates.
-/

@[expose] public section


noncomputable section

open ProbabilityTheory

open MeasureTheory MeasurableSpace Finset

namespace ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω] {s : Set Ω}

/--
Definition of `uniformOn` / `uniformOn` 的定义

English:
definition uniformOn
  signature: (s : Set Ω)
  body: Measure.count[|s]
deriving IsZeroOrProbabilityMeasure

@[simp]

中文:
定义 uniformOn
  签名: (s : Set Ω)
  定义体: Measure.count[|s]
deriving IsZeroOrProbabilityMeasure

@[simp]

Depends on / 依赖: Measure, Measure.count
-/
def uniformOn (s : Set Ω) : Measure Ω :=
  Measure.count[|s]
deriving IsZeroOrProbabilityMeasure

@[simp]
/--
theorem `uniformOn_empty_meas` / 定理 `uniformOn_empty_meas`

English:
theorem uniformOn_empty_meas
  statement: (uniformOn ∅ : Measure Ω) = 0
  proof: by simp [uniformOn]

中文:
定理 uniformOn_empty_meas
  结论: (uniformOn ∅ : Measure Ω) = 0
  证明: by simp [uniformOn]

Depends on / 依赖: uniformOn
-/
theorem uniformOn_empty_meas : (uniformOn ∅ : Measure Ω) = 0 := by simp [uniformOn]

/--
theorem `uniformOn_empty` / 定理 `uniformOn_empty`

English:
theorem uniformOn_empty
  given: {s : Set Ω}
  statement: uniformOn s ∅ = 0
  proof: by simp

中文:
定理 uniformOn_empty
  条件: {s : Set Ω}
  结论: uniformOn s ∅ = 0
  证明: by simp
-/
theorem uniformOn_empty {s : Set Ω} : uniformOn s ∅ = 0 := by simp

/--
lemma `uniformOn_eq_zero'` / 引理 `uniformOn_eq_zero'`

English:
lemma uniformOn_eq_zero'
  given: (hs : MeasurableSet s)
  statement: uniformOn s = 0 ↔ s.Infinite ∨ s = ∅
  proof: by
  simp [uniformOn, hs]

中文:
引理 uniformOn_eq_zero'
  条件: (hs : MeasurableSet s)
  结论: uniformOn s = 0 ↔ s.Infinite ∨ s = ∅
  证明: by
  simp [uniformOn, hs]
-/
@[simp] lemma uniformOn_eq_zero' (hs : MeasurableSet s) : uniformOn s = 0 ↔ s.Infinite ∨ s = ∅ := by
  simp [uniformOn, hs]

/--
lemma `uniformOn_eq_zero` / 引理 `uniformOn_eq_zero`

English:
lemma uniformOn_eq_zero
  given: [MeasurableSingletonClass Ω]
  proof: by simp [uniformOn]

中文:
引理 uniformOn_eq_zero
  条件: [MeasurableSingletonClass Ω]
  证明: by simp [uniformOn]
-/
@[simp] lemma uniformOn_eq_zero [MeasurableSingletonClass Ω] :
    uniformOn s = 0 ↔ s.Infinite ∨ s = ∅ := by simp [uniformOn]

/--
theorem `finite_of_uniformOn_ne_zero` / 定理 `finite_of_uniformOn_ne_zero`

English:
theorem finite_of_uniformOn_ne_zero
  given: {s t : Set Ω} (h : uniformOn s t != 0)
  statement: s.Finite
  proof: by
  by_contra hs'
  simp [uniformOn, cond, Measure.count_apply_infinite hs'] at h

中文:
定理 finite_of_uniformOn_ne_zero
  条件: {s t : Set Ω} (h : uniformOn s t != 0)
  结论: s.Finite
  证明: by
  by_contra hs'
  simp [uniformOn, cond, Measure.count_apply_infinite hs'] at h

Depends on / 依赖: Measure, Measure.count_apply_infinite, count_apply_infinite, uniformOn
-/
theorem finite_of_uniformOn_ne_zero {s t : Set Ω} (h : uniformOn s t != 0) : s.Finite := by
  by_contra hs'
  simp [uniformOn, cond, Measure.count_apply_infinite hs'] at h

/--
theorem `uniformOn_univ` / 定理 `uniformOn_univ`

English:
theorem uniformOn_univ
  given: [Fintype Ω] {s : Set Ω}
  proof: by
  simp [uniformOn, cond_apply, ← ENNReal.div_eq_inv_mul]

中文:
定理 uniformOn_univ
  条件: [Fintype Ω] {s : Set Ω}
  证明: by
  simp [uniformOn, cond_apply, ← ENNReal.div_eq_inv_mul]

Depends on / 依赖: ENNReal, ENNReal.div_eq_inv_mul, cond_apply, div_eq_inv_mul, uniformOn
-/
theorem uniformOn_univ [Fintype Ω] {s : Set Ω} :
    uniformOn Set.univ s = Measure.count s / Fintype.card Ω := by
  simp [uniformOn, cond_apply, ← ENNReal.div_eq_inv_mul]

/--
theorem `isProbabilityMeasure_uniformOn'` / 定理 `isProbabilityMeasure_uniformOn'`

English:
theorem isProbabilityMeasure_uniformOn'
  statement: {s : Set Ω}
  proof: by
  apply cond_isProbabilityMeasure_of_finite
  · rwa [Measure.count_ne_zero_iff]
.ne · exact (Measure.count_apply_lt_top' hs_meas).2 hs_fin

中文:
定理 isProbabilityMeasure_uniformOn'
  结论: {s : Set Ω}
  证明: by
  apply cond_isProbabilityMeasure_of_finite
  · rwa [Measure.count_ne_zero_iff]
.ne · exact (Measure.count_apply_lt_top' hs_meas).2 hs_fin

Depends on / 依赖: Measure, Measure.count_apply_lt_top, Measure.count_ne_zero_iff, cond_isProbabilityMeasure_of_finite, count_apply_lt_top, count_ne_zero_iff, hs_fin, hs_meas
-/
theorem isProbabilityMeasure_uniformOn' {s : Set Ω}
    (hs_fin : s.Finite) (hs_nonempty : s.Nonempty) (hs_meas : MeasurableSet s) :
    IsProbabilityMeasure (uniformOn s) := by
  apply cond_isProbabilityMeasure_of_finite
  · rwa [Measure.count_ne_zero_iff]
.ne · exact (Measure.count_apply_lt_top' hs_meas).2 hs_fin

/--
Instance `instIsProbabilityMeasure_uniformOn_univ` / 实例 `instIsProbabilityMeasure_uniformOn_univ`

English:
instance instIsProbabilityMeasure_uniformOn_univ
  signature: [Finite Ω] [Nonempty Ω]
  body: isProbabilityMeasure_uniformOn' Set.finite_univ Set.univ_nonempty .univ

中文:
实例 instIsProbabilityMeasure_uniformOn_univ
  签名: [Finite Ω] [Nonempty Ω]
  定义体: isProbabilityMeasure_uniformOn' Set.finite_univ Set.univ_nonempty .univ

Depends on / 依赖: Set.finite_univ, Set.univ_nonempty, finite_univ, isProbabilityMeasure_uniformOn, univ_nonempty
-/
instance instIsProbabilityMeasure_uniformOn_univ [Finite Ω] [Nonempty Ω] :
    IsProbabilityMeasure (uniformOn (.univ : Set Ω)) :=
  isProbabilityMeasure_uniformOn' Set.finite_univ Set.univ_nonempty .univ

/--
lemma `uniformOn_apply_finset'` / 引理 `uniformOn_apply_finset'`

English:
lemma uniformOn_apply_finset'
  statement: {Ω : Type*} [DecidableEq Ω] {_ : MeasurableSpace Ω} {s t : Finset Ω}
  proof: by
  rw [uniformOn]; rw [cond_apply hs]; rw [Measure.count_apply_finset' hs]; rw [← coe_inter]; rw [Measure.count_apply_finset']
  · rw [div_eq_mul_inv, mul_comm]
  rw [coe_inter]
  exact hs.inter ht

中文:
引理 uniformOn_apply_finset'
  结论: {Ω : 类型} [DecidableEq Ω] {_ : MeasurableSpace Ω} {s t : Finset Ω}
  证明: by
  rw [uniformOn]; rw [cond_apply hs]; rw [Measure.count_apply_finset' hs]; rw [← coe_inter]; rw [Measure.count_apply_finset']
  · rw [div_eq_mul_inv, mul_comm]
  rw [coe_inter]
  exact hs.inter ht

Depends on / 依赖: Measure, Measure.count_apply_finset, coe_inter, cond_apply, count_apply_finset, div_eq_mul_inv, hs.inter, mul_comm, uniformOn
-/
lemma uniformOn_apply_finset' {Ω : Type*} [DecidableEq Ω] {_ : MeasurableSpace Ω} {s t : Finset Ω}
    (hs : MeasurableSet (s : Set Ω)) (ht : MeasurableSet (t : Set Ω)) :
    uniformOn (s : Set Ω) (t : Set Ω) = #(s inter t) / #s := by
  rw [uniformOn]; rw [cond_apply hs]; rw [Measure.count_apply_finset' hs]; rw [← coe_inter]; rw [Measure.count_apply_finset']
  · rw [div_eq_mul_inv, mul_comm]
  rw [coe_inter]
  exact hs.inter ht

variable [MeasurableSingletonClass Ω]

/--
lemma `uniformOn_apply_finset` / 引理 `uniformOn_apply_finset`

English:
lemma uniformOn_apply_finset
  given: [DecidableEq Ω] {s t : Finset Ω}
  proof: uniformOn_apply_finset' s.measurableSet t.measurableSet

中文:
引理 uniformOn_apply_finset
  条件: [DecidableEq Ω] {s t : Finset Ω}
  证明: uniformOn_apply_finset' s.measurableSet t.measurableSet

Depends on / 依赖: measurableSet, s.measurableSet, t.measurableSet, uniformOn_apply_finset
-/
lemma uniformOn_apply_finset [DecidableEq Ω] {s t : Finset Ω} :
    uniformOn (s : Set Ω) (t : Set Ω) = #(s inter t) / #s :=
  uniformOn_apply_finset' s.measurableSet t.measurableSet

/--
theorem `isProbabilityMeasure_uniformOn` / 定理 `isProbabilityMeasure_uniformOn`

English:
theorem isProbabilityMeasure_uniformOn
  given: {s : Set Ω} (hs : s.Finite) (hs' : s.Nonempty)
  proof: by
  apply cond_isProbabilityMeasure_of_finite
  · rwa [Measure.count_ne_zero_iff]
  · exact (Measure.count_apply_lt_top.2 hs).ne

@[deprecated (since := "2026-01-26")]
alias uniformOn_isProbabilityMeasure := isProbabilityMeasure_uniformOn

中文:
定理 isProbabilityMeasure_uniformOn
  条件: {s : Set Ω} (hs : s.Finite) (hs' : s.Nonempty)
  证明: by
  apply cond_isProbabilityMeasure_of_finite
  · rwa [Measure.count_ne_zero_iff]
  · exact (Measure.count_apply_lt_top.2 hs).ne

@[deprecated (since := "2026-01-26")]
alias uniformOn_isProbabilityMeasure := isProbabilityMeasure_uniformOn

Depends on / 依赖: Measure, Measure.count_apply_lt_top, Measure.count_ne_zero_iff, cond_isProbabilityMeasure_of_finite, count_apply_lt_top, count_ne_zero_iff
-/
theorem isProbabilityMeasure_uniformOn {s : Set Ω} (hs : s.Finite) (hs' : s.Nonempty) :
    IsProbabilityMeasure (uniformOn s) := by
  apply cond_isProbabilityMeasure_of_finite
  · rwa [Measure.count_ne_zero_iff]
  · exact (Measure.count_apply_lt_top.2 hs).ne

@[deprecated (since := "2026-01-26")]
alias uniformOn_isProbabilityMeasure := isProbabilityMeasure_uniformOn

/--
theorem `uniformOn_singleton` / 定理 `uniformOn_singleton`

English:
theorem uniformOn_singleton
  given: (ω : Ω) (t : Set Ω) [Decidable (ω in t)]
  proof: by
  rw [uniformOn]; rw [cond_apply (measurableSet_singleton ω)]; rw [Measure.count_singleton]; rw [inv_one]; rw [one_mul]
  split_ifs
  · rw [(by simpa : ({ω} : Set Ω) inter t = {ω}), Measure.count_singleton]
  · simpa

中文:
定理 uniformOn_singleton
  条件: (ω : Ω) (t : Set Ω) [Decidable (ω in t)]
  证明: by
  rw [uniformOn]; rw [cond_apply (measurableSet_singleton ω)]; rw [Measure.count_singleton]; rw [inv_one]; rw [one_mul]
  split_ifs
  · rw [(by simpa : ({ω} : Set Ω) inter t = {ω}), Measure.count_singleton]
  · simpa

Depends on / 依赖: Measure, Measure.count_singleton, cond_apply, count_singleton, inv_one, measurableSet_singleton, one_mul, split_ifs, uniformOn
-/
theorem uniformOn_singleton (ω : Ω) (t : Set Ω) [Decidable (ω in t)] :
    uniformOn {ω} t = if ω in t then 1 else 0 := by
  rw [uniformOn]; rw [cond_apply (measurableSet_singleton ω)]; rw [Measure.count_singleton]; rw [inv_one]; rw [one_mul]
  split_ifs
  · rw [(by simpa : ({ω} : Set Ω) inter t = {ω}), Measure.count_singleton]
  · simpa

variable {s t u : Set Ω}

/--
theorem `uniformOn_inter_self` / 定理 `uniformOn_inter_self`

English:
theorem uniformOn_inter_self
  given: (hs : s.Finite)
  statement: uniformOn s (s inter t) = uniformOn s t
  proof: by
  rw [uniformOn]; rw [cond_inter_self hs.measurableSet]

中文:
定理 uniformOn_inter_self
  条件: (hs : s.Finite)
  结论: uniformOn s (s inter t) = uniformOn s t
  证明: by
  rw [uniformOn]; rw [cond_inter_self hs.measurableSet]

Depends on / 依赖: cond_inter_self, hs.measurableSet, measurableSet, uniformOn
-/
theorem uniformOn_inter_self (hs : s.Finite) : uniformOn s (s inter t) = uniformOn s t := by
  rw [uniformOn]; rw [cond_inter_self hs.measurableSet]

/--
theorem `uniformOn_self` / 定理 `uniformOn_self`

English:
theorem uniformOn_self
  given: (hs : s.Finite) (hs' : s.Nonempty)
  statement: uniformOn s s = 1
  proof: by
  rw [uniformOn]; rw [cond_apply hs.measurableSet]; rw [Set.inter_self]; rw [ENNReal.inv_mul_cancel]
  · rwa [Measure.count_ne_zero_iff]
  · exact (Measure.count_apply_lt_top.2 hs).ne

中文:
定理 uniformOn_self
  条件: (hs : s.Finite) (hs' : s.Nonempty)
  结论: uniformOn s s = 1
  证明: by
  rw [uniformOn]; rw [cond_apply hs.measurableSet]; rw [Set.inter_self]; rw [ENNReal.inv_mul_cancel]
  · rwa [Measure.count_ne_zero_iff]
  · exact (Measure.count_apply_lt_top.2 hs).ne

Depends on / 依赖: ENNReal, ENNReal.inv_mul_cancel, Measure, Measure.count_apply_lt_top, Measure.count_ne_zero_iff, Set.inter_self, cond_apply, count_apply_lt_top, count_ne_zero_iff, hs.measurableSet, inter_self, inv_mul_cancel, measurableSet, uniformOn
-/
theorem uniformOn_self (hs : s.Finite) (hs' : s.Nonempty) : uniformOn s s = 1 := by
  rw [uniformOn]; rw [cond_apply hs.measurableSet]; rw [Set.inter_self]; rw [ENNReal.inv_mul_cancel]
  · rwa [Measure.count_ne_zero_iff]
  · exact (Measure.count_apply_lt_top.2 hs).ne

/--
theorem `uniformOn_eq_one_of` / 定理 `uniformOn_eq_one_of`

English:
theorem uniformOn_eq_one_of
  given: (hs : s.Finite) (hs' : s.Nonempty) (ht : s subseteq t)
  proof: by
  have := isProbabilityMeasure_uniformOn hs hs'
  refine eq_of_le_of_not_lt prob_le_one ?_
  rw [not_lt]; rw [← uniformOn_self hs hs']
  exact measure_mono ht

中文:
定理 uniformOn_eq_one_of
  条件: (hs : s.Finite) (hs' : s.Nonempty) (ht : s subseteq t)
  证明: by
  have := isProbabilityMeasure_uniformOn hs hs'
  refine eq_of_le_of_not_lt prob_le_one ?_
  rw [not_lt]; rw [← uniformOn_self hs hs']
  exact measure_mono ht

Depends on / 依赖: eq_of_le_of_not_lt, isProbabilityMeasure_uniformOn, measure_mono, not_lt, prob_le_one, uniformOn_self
-/
theorem uniformOn_eq_one_of (hs : s.Finite) (hs' : s.Nonempty) (ht : s subseteq t) :
    uniformOn s t = 1 := by
  have := isProbabilityMeasure_uniformOn hs hs'
  refine eq_of_le_of_not_lt prob_le_one ?_
  rw [not_lt]; rw [← uniformOn_self hs hs']
  exact measure_mono ht

/--
theorem `pred_true_of_uniformOn_eq_one` / 定理 `pred_true_of_uniformOn_eq_one`

English:
theorem pred_true_of_uniformOn_eq_one
  given: (h : uniformOn s t = 1)
  statement: s subseteq t
  proof: by
  have hsf := finite_of_uniformOn_ne_zero (by rw [h]; exact one_ne_zero)
  rw [uniformOn]; rw [cond_apply hsf.measurableSet]; rw [mul_comm] at h
  replace h := ENNReal.eq_inv_of_mul_eq_one_left h
  rw [inv_inv]; rw [Measure.count_apply_finite _ hsf]; rw [Measure.count_apply_finite _ (hsf.inter_of

中文:
定理 pred_true_of_uniformOn_eq_one
  条件: (h : uniformOn s t = 1)
  结论: s subseteq t
  证明: by
  have hsf := finite_of_uniformOn_ne_zero (by rw [h]; exact one_ne_zero)
  rw [uniformOn]; rw [cond_apply hsf.measurableSet]; rw [mul_comm] at h
  replace h := ENNReal.eq_inv_of_mul_eq_one_left h
  rw [inv_inv]; rw [Measure.count_apply_finite _ hsf]; rw [Measure.count_apply_finite _ (hsf.inter_of

Depends on / 依赖: ENNReal, ENNReal.eq_inv_of_mul_eq_one_left, Finite, Finset, Finset.eq_of_subset_of_card_le, Measure, Measure.count_apply_finite, Nat.cast_inj, Set.Finite.toFin, Set.Finite.toFinset_inj, cast_inj, cond_apply, count_apply_finite, eq_inv_of_mul_eq_one_left, eq_of_subset_of_card_le, finite_of_uniformOn_ne_zero, hsf.inter_of_left, hsf.measurableSet, inter_of_left, inv_inv
-/
theorem pred_true_of_uniformOn_eq_one (h : uniformOn s t = 1) : s subseteq t := by
  have hsf := finite_of_uniformOn_ne_zero (by rw [h]; exact one_ne_zero)
  rw [uniformOn]; rw [cond_apply hsf.measurableSet]; rw [mul_comm] at h
  replace h := ENNReal.eq_inv_of_mul_eq_one_left h
  rw [inv_inv]; rw [Measure.count_apply_finite _ hsf]; rw [Measure.count_apply_finite _ (hsf.inter_of_left _)]; rw [Nat.cast_inj] at h
  suffices s inter t = s by exact this ▸ fun x hx => hx.2
  rw [← @Set.Finite.toFinset_inj _ _ _ (hsf.inter_of_left _) hsf]
  exact Finset.eq_of_subset_of_card_le (Set.Finite.toFinset_mono s.inter_subset_left) h.ge

/--
theorem `uniformOn_eq_zero_iff` / 定理 `uniformOn_eq_zero_iff`

English:
theorem uniformOn_eq_zero_iff
  given: (hs : s.Finite)
  statement: uniformOn s t = 0 ↔ s inter t = ∅
  proof: by
  simp [uniformOn, cond_apply hs.measurableSet, Measure.count_apply_eq_top, Set.not_infinite.2 hs,
    Measure.count_apply_finite _ (hs.inter_of_left _)]

中文:
定理 uniformOn_eq_zero_iff
  条件: (hs : s.Finite)
  结论: uniformOn s t = 0 ↔ s inter t = ∅
  证明: by
  simp [uniformOn, cond_apply hs.measurableSet, Measure.count_apply_eq_top, Set.not_infinite.2 hs,
    Measure.count_apply_finite _ (hs.inter_of_left _)]

Depends on / 依赖: Measure, Measure.count_apply_eq_top, Measure.count_apply_finite, Set.not_infinite, cond_apply, count_apply_eq_top, count_apply_finite, hs.inter_of_left, hs.measurableSet, inter_of_left, measurableSet, not_infinite, uniformOn
-/
theorem uniformOn_eq_zero_iff (hs : s.Finite) : uniformOn s t = 0 ↔ s inter t = ∅ := by
  simp [uniformOn, cond_apply hs.measurableSet, Measure.count_apply_eq_top, Set.not_infinite.2 hs,
    Measure.count_apply_finite _ (hs.inter_of_left _)]

/--
theorem `uniformOn_of_univ` / 定理 `uniformOn_of_univ`

English:
theorem uniformOn_of_univ
  given: (hs : s.Finite) (hs' : s.Nonempty)
  statement: uniformOn s Set.univ = 1
  proof: uniformOn_eq_one_of hs hs' s.subset_univ

中文:
定理 uniformOn_of_univ
  条件: (hs : s.Finite) (hs' : s.Nonempty)
  结论: uniformOn s Set.univ = 1
  证明: uniformOn_eq_one_of hs hs' s.subset_univ

Depends on / 依赖: s.subset_univ, subset_univ, uniformOn_eq_one_of
-/
theorem uniformOn_of_univ (hs : s.Finite) (hs' : s.Nonempty) : uniformOn s Set.univ = 1 :=
  uniformOn_eq_one_of hs hs' s.subset_univ

/--
theorem `uniformOn_inter` / 定理 `uniformOn_inter`

English:
theorem uniformOn_inter
  given: (hs : s.Finite)
  proof: by
  by_cases hst : s inter t = ∅
  · rw [hst, uniformOn_empty_meas, Measure.coe_zero, Pi.zero_apply, zero_mul,
      uniformOn_eq_zero_iff hs, ← Set.inter_assoc, hst, Set.empty_inter]
  rw [uniformOn]; rw [uniformOn]; rw [cond_apply hs.measurableSet]; rw [cond_apply hs.measurableSet]; rw [cond_appl

中文:
定理 uniformOn_inter
  条件: (hs : s.Finite)
  证明: by
  by_cases hst : s inter t = ∅
  · rw [hst, uniformOn_empty_meas, Measure.coe_zero, Pi.zero_apply, zero_mul,
      uniformOn_eq_zero_iff hs, ← Set.inter_assoc, hst, Set.empty_inter]
  rw [uniformOn]; rw [uniformOn]; rw [cond_apply hs.measurableSet]; rw [cond_apply hs.measurableSet]; rw [cond_appl

Depends on / 依赖: ENNReal, ENNReal.mul_inv_cancel, Measure, Measure.coe_zero, Measure.count, Pi.zero_apply, Set.empty_inter, Set.inter_assoc, coe_zero, cond_apply, empty_inter, hs.inter_of_left, hs.measurableSet, inter_assoc, inter_of_left, measurableSet, mul_assoc, mul_comm, mul_inv_cancel, one_mul
-/
theorem uniformOn_inter (hs : s.Finite) :
    uniformOn s (t inter u) = uniformOn (s inter t) u * uniformOn s t := by
  by_cases hst : s inter t = ∅
  · rw [hst, uniformOn_empty_meas, Measure.coe_zero, Pi.zero_apply, zero_mul,
      uniformOn_eq_zero_iff hs, ← Set.inter_assoc, hst, Set.empty_inter]
  rw [uniformOn]; rw [uniformOn]; rw [cond_apply hs.measurableSet]; rw [cond_apply hs.measurableSet]; rw [cond_apply (hs.inter_of_left _).measurableSet]; rw [mul_comm _ (Measure.count (s inter t))]; rw [← mul_assoc]; rw [mul_comm _ (Measure.count (s inter t))]; rw [← mul_assoc]; rw [ENNReal.mul_inv_cancel]; rw [one_mul]; rw [mul_comm]; rw [Set.inter_assoc]
  · rwa [← Measure.count_eq_zero_iff] at hst
  · exact (Measure.count_apply_lt_top.2 <| hs.inter_of_left _).ne

/--
theorem `uniformOn_inter'` / 定理 `uniformOn_inter'`

English:
theorem uniformOn_inter'
  given: (hs : s.Finite)
  proof: by
  rw [← Set.inter_comm]
  exact uniformOn_inter hs

中文:
定理 uniformOn_inter'
  条件: (hs : s.Finite)
  证明: by
  rw [← Set.inter_comm]
  exact uniformOn_inter hs

Depends on / 依赖: Set.inter_comm, inter_comm, uniformOn_inter
-/
theorem uniformOn_inter' (hs : s.Finite) :
    uniformOn s (t inter u) = uniformOn (s inter u) t * uniformOn s u := by
  rw [← Set.inter_comm]
  exact uniformOn_inter hs

/--
theorem `uniformOn_union` / 定理 `uniformOn_union`

English:
theorem uniformOn_union
  given: (hs : s.Finite) (htu : Disjoint t u)
  proof: by
  rw [uniformOn]; rw [cond_apply hs.measurableSet]; rw [cond_apply hs.measurableSet]; rw [cond_apply hs.measurableSet]; rw [Set.inter_union_distrib_left]; rw [measure_union]; rw [mul_add]
  exacts [htu.mono inf_le_right inf_le_right, (hs.inter_of_left _).measurableSet]

中文:
定理 uniformOn_union
  条件: (hs : s.Finite) (htu : Disjoint t u)
  证明: by
  rw [uniformOn]; rw [cond_apply hs.measurableSet]; rw [cond_apply hs.measurableSet]; rw [cond_apply hs.measurableSet]; rw [Set.inter_union_distrib_left]; rw [measure_union]; rw [mul_add]
  exacts [htu.mono inf_le_right inf_le_right, (hs.inter_of_left _).measurableSet]

Depends on / 依赖: Set.inter_union_distrib_left, cond_apply, exacts, hs.inter_of_left, hs.measurableSet, htu.mono, inf_le_right, inter_of_left, inter_union_distrib_left, measurableSet, measure_union, mul_add, uniformOn
-/
theorem uniformOn_union (hs : s.Finite) (htu : Disjoint t u) :
    uniformOn s (t union u) = uniformOn s t + uniformOn s u := by
  rw [uniformOn]; rw [cond_apply hs.measurableSet]; rw [cond_apply hs.measurableSet]; rw [cond_apply hs.measurableSet]; rw [Set.inter_union_distrib_left]; rw [measure_union]; rw [mul_add]
  exacts [htu.mono inf_le_right inf_le_right, (hs.inter_of_left _).measurableSet]

/--
theorem `uniformOn_compl` / 定理 `uniformOn_compl`

English:
theorem uniformOn_compl
  given: (t : Set Ω) (hs : s.Finite) (hs' : s.Nonempty)
  proof: by
  rw [← uniformOn_union hs disjoint_compl_right]; rw [Set.union_compl_self]; rw [(isProbabilityMeasure_uniformOn hs hs').measure_univ]

中文:
定理 uniformOn_compl
  条件: (t : Set Ω) (hs : s.Finite) (hs' : s.Nonempty)
  证明: by
  rw [← uniformOn_union hs disjoint_compl_right]; rw [Set.union_compl_self]; rw [(isProbabilityMeasure_uniformOn hs hs').measure_univ]

Depends on / 依赖: Set.union_compl_self, disjoint_compl_right, isProbabilityMeasure_uniformOn, measure_univ, uniformOn_union, union_compl_self
-/
theorem uniformOn_compl (t : Set Ω) (hs : s.Finite) (hs' : s.Nonempty) :
    uniformOn s t + uniformOn s tᶜ = 1 := by
  rw [← uniformOn_union hs disjoint_compl_right]; rw [Set.union_compl_self]; rw [(isProbabilityMeasure_uniformOn hs hs').measure_univ]

/--
theorem `uniformOn_disjoint_union` / 定理 `uniformOn_disjoint_union`

English:
theorem uniformOn_disjoint_union
  given: (hs : s.Finite) (ht : t.Finite) (hst : Disjoint s t)
  proof: by
  rcases s.eq_empty_or_nonempty with (rfl | hs') <;> rcases t.eq_empty_or_nonempty with (rfl | ht')
  · simp
  · simp [uniformOn_self ht ht']
  · simp [uniformOn_self hs hs']
  rw [uniformOn]; rw [uniformOn]; rw [uniformOn]; rw [cond_apply hs.measurableSet]; rw [cond_apply ht.measurableSet]; rw [

中文:
定理 uniformOn_disjoint_union
  条件: (hs : s.Finite) (ht : t.Finite) (hst : Disjoint s t)
  证明: by
  rcases s.eq_empty_or_nonempty with (rfl | hs') <;> rcases t.eq_empty_or_nonempty with (rfl | ht')
  · simp
  · simp [uniformOn_self ht ht']
  · simp [uniformOn_self hs hs']
  rw [uniformOn]; rw [uniformOn]; rw [uniformOn]; rw [cond_apply hs.measurableSet]; rw [cond_apply ht.measurableSet]; rw [

Depends on / 依赖: Set.union_inter_cancel_left, Set.union_inter_cancel_right, cond_apply, conv_lhs, eq_empty_or_nonempty, hs.measurableSet, hs.union, ht.measurableSet, measurableSet, s.eq_empty_or_nonempty, t.eq_empty_or_nonempty, uniformOn, uniformOn_self, union_inter_cancel_left, union_inter_cancel_right
-/
theorem uniformOn_disjoint_union (hs : s.Finite) (ht : t.Finite) (hst : Disjoint s t) :
    uniformOn s u * uniformOn (s union t) s + uniformOn t u * uniformOn (s union t) t =
      uniformOn (s union t) u := by
  rcases s.eq_empty_or_nonempty with (rfl | hs') <;> rcases t.eq_empty_or_nonempty with (rfl | ht')
  · simp
  · simp [uniformOn_self ht ht']
  · simp [uniformOn_self hs hs']
  rw [uniformOn]; rw [uniformOn]; rw [uniformOn]; rw [cond_apply hs.measurableSet]; rw [cond_apply ht.measurableSet]; rw [cond_apply (hs.union ht).measurableSet]; rw [cond_apply (hs.union ht).measurableSet]; rw [cond_apply (hs.union ht).measurableSet]
  conv_lhs =>
    rw [Set.union_inter_cancel_left]; rw [Set.union_inter_cancel_right]; rw [mul_comm (Measure.count (s union t))⁻¹]; rw [mul_comm (Measure.count (s union t))⁻¹]; rw [← mul_assoc]; rw [← mul_assoc]; rw [mul_comm _ (Measure.count s)]; rw [mul_comm _ (Measure.count t)]; rw [← mul_assoc]; rw [← mul_assoc]
  rw [ENNReal.mul_inv_cancel]; rw [ENNReal.mul_inv_cancel]; rw [one_mul]; rw [one_mul]; rw [← add_mul]; rw [← measure_union]; rw [Set.union_inter_distrib_right]; rw [mul_comm]
  exacts [hst.mono inf_le_left inf_le_left, (ht.inter_of_left _).measurableSet,
    Measure.count_ne_zero ht', (Measure.count_apply_lt_top.2 ht).ne, Measure.count_ne_zero hs',
    (Measure.count_apply_lt_top.2 hs).ne]

/--
theorem `uniformOn_add_compl_eq` / 定理 `uniformOn_add_compl_eq`

English:
theorem uniformOn_add_compl_eq
  given: (u t : Set Ω) (hs : s.Finite)
  proof: by
  conv_rhs =>
    rw [(by simp : s = s inter u union s inter uᶜ)]; rw [← uniformOn_disjoint_union (hs.inter_of_left _) (hs.inter_of_left _)
      (disjoint_compl_right.mono inf_le_right inf_le_right)]
  simp [uniformOn_inter_self hs]

中文:
定理 uniformOn_add_compl_eq
  条件: (u t : Set Ω) (hs : s.Finite)
  证明: by
  conv_rhs =>
    rw [(by simp : s = s inter u union s inter uᶜ)]; rw [← uniformOn_disjoint_union (hs.inter_of_left _) (hs.inter_of_left _)
      (disjoint_compl_right.mono inf_le_right inf_le_right)]
  simp [uniformOn_inter_self hs]

Depends on / 依赖: conv_rhs, disjoint_compl_right, disjoint_compl_right.mono, hs.inter_of_left, inf_le_right, inter_of_left, uniformOn_disjoint_union, uniformOn_inter_self
-/
theorem uniformOn_add_compl_eq (u t : Set Ω) (hs : s.Finite) :
    uniformOn (s inter u) t * uniformOn s u + uniformOn (s inter uᶜ) t * uniformOn s uᶜ =
      uniformOn s t := by
  conv_rhs =>
    rw [(by simp : s = s inter u union s inter uᶜ)]; rw [← uniformOn_disjoint_union (hs.inter_of_left _) (hs.inter_of_left _)
      (disjoint_compl_right.mono inf_le_right inf_le_right)]
  simp [uniformOn_inter_self hs]

variable {ι : Type*} [Fintype ι]

/--
lemma `uniformOn_pi` / 引理 `uniformOn_pi`

English:
lemma uniformOn_pi
  given: [Finite Ω] {f : ι -> Set Ω}
  proof: by
  refine (MeasureTheory.Measure.pi_eq fun t ht => ?_).symm
  lift f to ι -> Finset Ω using by simp [Set.toFinite]
  lift t to ι -> Finset Ω using by simp [Set.toFinite]
  classical
  simp [← Fintype.coe_piFinset, uniformOn_apply_finset, ← Fintype.piFinset_inter,
    ENNReal.prod_div_distrib_of_ne

中文:
引理 uniformOn_pi
  条件: [Finite Ω] {f : ι -> Set Ω}
  证明: by
  refine (MeasureTheory.Measure.pi_eq fun t ht => ?_).symm
  lift f to ι -> Finset Ω using by simp [Set.toFinite]
  lift t to ι -> Finset Ω using by simp [Set.toFinite]
  classical
  simp [← Fintype.coe_piFinset, uniformOn_apply_finset, ← Fintype.piFinset_inter,
    ENNReal.prod_div_distrib_of_ne

Depends on / 依赖: ENNReal, ENNReal.prod_div_distrib_of_ne_top, Finset, Fintype, Fintype.coe_piFinset, Fintype.piFinset_inter, Measure, MeasureTheory, MeasureTheory.Measure.pi_eq, Set.toFinite, classical, coe_piFinset, piFinset_inter, pi_eq, prod_div_distrib_of_ne_top, toFinite, uniformOn_apply_finset
-/
lemma uniformOn_pi [Finite Ω] {f : ι -> Set Ω} :
    uniformOn (Set.univ.pi f) = Measure.pi fun i => uniformOn (f i) := by
  refine (MeasureTheory.Measure.pi_eq fun t ht => ?_).symm
  lift f to ι -> Finset Ω using by simp [Set.toFinite]
  lift t to ι -> Finset Ω using by simp [Set.toFinite]
  classical
  simp [← Fintype.coe_piFinset, uniformOn_apply_finset, ← Fintype.piFinset_inter,
    ENNReal.prod_div_distrib_of_ne_top]

end ProbabilityTheory
