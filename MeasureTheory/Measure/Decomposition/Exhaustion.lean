/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite

/-!
# Method of exhaustion

If `μ, ν` are two measures with `ν` s-finite, then there exists a set `s` such that
`μ` is sigma-finite on `s`, and for all sets `t ⊆ sᶜ`, either `ν t = 0` or `μ t = ∞`.

## Main definitions

* `MeasureTheory.Measure.sigmaFiniteSetWRT`: if such a set exists, `μ.sigmaFiniteSetWRT ν` is
  a measurable set such that `μ.restrict (μ.sigmaFiniteSetWRT ν)` is sigma-finite and
  for all sets `t ⊆ (μ.sigmaFiniteSetWRT ν)ᶜ`, either `ν t = 0` or `μ t = ∞`.
  If no such set exists (which is only possible if `ν` is not s-finite), we define
  `μ.sigmaFiniteSetWRT ν = ∅`.
* `MeasureTheory.Measure.sigmaFiniteSet`: for an s-finite measure `μ`, a measurable set such that
  `μ.restrict μ.sigmaFiniteSet` is sigma-finite, and for all sets `s ⊆ μ.sigmaFiniteSetᶜ`,
  either `μ s = 0` or `μ s = ∞`.
  Defined as `μ.sigmaFiniteSetWRT μ`.

## Main statements

* `measure_eq_top_of_subset_compl_sigmaFiniteSetWRT`: for s-finite `ν`, for all sets `s`
  in `(sigmaFiniteSetWRT μ ν)ᶜ`, if `ν s ≠ 0` then `μ s = ∞`.
* An instance showing that `μ.restrict (sigmaFiniteSetWRT μ ν)` is sigma-finite.
* `restrict_compl_sigmaFiniteSetWRT`: if `μ ≪ ν` and `ν` is s-finite, then
  `μ.restrict (μ.sigmaFiniteSetWRT ν)ᶜ = ∞ • ν.restrict (μ.sigmaFiniteSetWRT ν)ᶜ`. As a consequence,
  that restriction is s-finite.

* An instance showing that `μ.restrict μ.sigmaFiniteSet` is sigma-finite.
* `restrict_compl_sigmaFiniteSet_eq_zero_or_top`: the measure `μ.restrict μ.sigmaFiniteSetᶜ` takes
  only two values: 0 and ∞ .
* `measure_compl_sigmaFiniteSet_eq_zero_iff_sigmaFinite`: a measure `μ` is sigma-finite
  iff `μ μ.sigmaFiniteSetᶜ = 0`.

## References

* [P. R. Halmos, *Measure theory*, 17.3 and 30.11][halmos1950measure]

-/

@[expose] public section

assert_not_exists MeasureTheory.Measure.rnDeriv
assert_not_exists MeasureTheory.VectorMeasure

open scoped ENNReal Topology

open Filter

namespace MeasureTheory

variable {α : Type*} {mα : MeasurableSpace α} {μ ν : Measure α} {s t : Set α}

open scoped Classical in
-- Note: `Set` has no computational content, but Lean still attempts to compile it.
-- See https://github.com/leanprover/lean4/issues/14084.
/--
Definition of `Measure.sigmaFiniteSetWRT` / `Measure.sigmaFiniteSetWRT` 的定义

English:
definition Measure.sigmaFiniteSetWRT
  signature: (μ ν : Measure α)
  body: if h : exists s : Set α, MeasurableSet s ∧ SigmaFinite (μ.restrict s)
    ∧ (forall t, t subseteq sᶜ -> ν t != 0 -> μ t = ∞)
  then h.choose
  else ∅

@[measurability]

中文:
定义 测度.sigmaFiniteSetWRT
  签名: (μ ν : 测度 α)
  定义体: if h : exists s : Set α, MeasurableSet s ∧ SigmaFinite (μ.restrict s)
    ∧ (forall t, t subseteq sᶜ -> ν t != 0 -> μ t = ∞)
  then h.choose
  else ∅

@[measurability]

Depends on / 依赖: MeasurableSet, SigmaFinite, h.choose, restrict, subseteq
-/
noncomputable def Measure.sigmaFiniteSetWRT (μ ν : Measure α) : Set α :=
  if h : exists s : Set α, MeasurableSet s ∧ SigmaFinite (μ.restrict s)
    ∧ (forall t, t subseteq sᶜ -> ν t != 0 -> μ t = ∞)
  then h.choose
  else ∅

@[measurability]
/--
lemma `measurableSet_sigmaFiniteSetWRT` / 引理 `measurableSet_sigmaFiniteSetWRT`

English:
lemma measurableSet_sigmaFiniteSetWRT
  proof: by
  rw [Measure.sigmaFiniteSetWRT]
  split_ifs with h
  · exact h.choose_spec.1
  · exact MeasurableSet.empty

中文:
引理 measurableSet_sigmaFiniteSetWRT
  证明: by
  rw [Measure.sigmaFiniteSetWRT]
  split_ifs with h
  · exact h.choose_spec.1
  · exact MeasurableSet.empty

Depends on / 依赖: MeasurableSet, MeasurableSet.empty, Measure, Measure.sigmaFiniteSetWRT, choose_spec, h.choose_spec, sigmaFiniteSetWRT, split_ifs
-/
lemma measurableSet_sigmaFiniteSetWRT :
    MeasurableSet (μ.sigmaFiniteSetWRT ν) := by
  rw [Measure.sigmaFiniteSetWRT]
  split_ifs with h
  · exact h.choose_spec.1
  · exact MeasurableSet.empty

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SigmaFinite (μ.restrict (μ.sigmaFiniteSetWRT ν))
  body: by
  rw [Measure.sigmaFiniteSetWRT]
  split_ifs with h
  · exact h.choose_spec.2.1
  · rw [Measure.restrict_empty]
    infer_instance

中文:
实例 :
  签名: σ有限 (μ.restrict (μ.sigmaFiniteSetWRT ν))
  定义体: by
  rw [Measure.sigmaFiniteSetWRT]
  split_ifs with h
  · exact h.choose_spec.2.1
  · rw [Measure.restrict_empty]
    infer_instance

Depends on / 依赖: Measure, Measure.restrict_empty, Measure.sigmaFiniteSetWRT, choose_spec, h.choose_spec, infer_instance, restrict_empty, sigmaFiniteSetWRT, split_ifs
-/
instance : SigmaFinite (μ.restrict (μ.sigmaFiniteSetWRT ν)) := by
  rw [Measure.sigmaFiniteSetWRT]
  split_ifs with h
  · exact h.choose_spec.2.1
  · rw [Measure.restrict_empty]
    infer_instance

section IsFiniteMeasure

/-! We prove that the condition in the definition of `sigmaFiniteSetWRT` is true for finite
measures. Since every s-finite measure is absolutely continuous with respect to a finite measure,
the condition will then also be true for s-finite measures. -/

/--
lemma `exists_isSigmaFiniteSet_measure_ge` / 引理 `exists_isSigmaFiniteSet_measure_ge`

English:
lemma exists_isSigmaFiniteSet_measure_ge
  given: (μ ν : Measure α) [IsFiniteMeasure ν] (n : Nat)
  proof: by
  by_cases! hC_lt : 1 / n < ⨆ (s) (_ : MeasurableSet s) (_ : SigmaFinite (μ.restrict s)), ν s
  · have h_lt_top : ⨆ (s) (_ : MeasurableSet s) (_ : SigmaFinite (μ.restrict s)), ν s < ∞ := by
      refine (?_ : ⨆ (s) (_ : MeasurableSet s)
        (_ : SigmaFinite (μ.restrict s)), ν s <= ν Set.univ)

中文:
引理 存在_isSigmaFiniteSet_measure_ge
  条件: (μ ν : 测度 α) [是有限测度 ν] (n : 自然数)
  证明: by
  by_cases! hC_lt : 1 / n < ⨆ (s) (_ : MeasurableSet s) (_ : SigmaFinite (μ.restrict s)), ν s
  · have h_lt_top : ⨆ (s) (_ : MeasurableSet s) (_ : SigmaFinite (μ.restrict s)), ν s < ∞ := by
      refine (?_ : ⨆ (s) (_ : MeasurableSet s)
        (_ : SigmaFinite (μ.restrict s)), ν s <= ν Set.univ)

Depends on / 依赖: ENNReal, ENNReal.sub_lt_self, MeasurableSet, Set.subset_univ, Set.univ, SigmaFinite, exists_lt_of_lt_ciSup, hC_lt, hC_lt.ne, h_lt_top, h_lt_top.ne, iSup_le, measure_lt_top, measure_mono, restrict, sub_lt_self, subset_univ, trans_lt
-/
lemma exists_isSigmaFiniteSet_measure_ge (μ ν : Measure α) [IsFiniteMeasure ν] (n : Nat) :
    exists t, MeasurableSet t ∧ SigmaFinite (μ.restrict t)
      ∧ (⨆ (s) (_ : MeasurableSet s) (_ : SigmaFinite (μ.restrict s)), ν s) - 1 / n <= ν t := by
  by_cases! hC_lt : 1 / n < ⨆ (s) (_ : MeasurableSet s) (_ : SigmaFinite (μ.restrict s)), ν s
  · have h_lt_top : ⨆ (s) (_ : MeasurableSet s) (_ : SigmaFinite (μ.restrict s)), ν s < ∞ := by
      refine (?_ : ⨆ (s) (_ : MeasurableSet s)
        (_ : SigmaFinite (μ.restrict s)), ν s <= ν Set.univ).trans_lt (measure_lt_top _ _)
      refine iSup_le (fun s => ?_)
      exact iSup_le (fun _ => iSup_le (fun _ => measure_mono (Set.subset_univ s)))
    obtain ⟨t, ht⟩ := exists_lt_of_lt_ciSup
      (ENNReal.sub_lt_self h_lt_top.ne hC_lt.ne_bot (by simp) :
          (⨆ (s) (_ : MeasurableSet s) (_ : SigmaFinite (μ.restrict s)), ν s) - 1 / n
        < ⨆ (s) (_ : MeasurableSet s) (_ : SigmaFinite (μ.restrict s)), ν s)
    have ht_meas : MeasurableSet t := by
      by_contra h_notMem
      simp only [h_notMem] at ht
      simp at ht
    have ht_mem : SigmaFinite (μ.restrict t) := by
      by_contra h_notMem
      simp only [h_notMem] at ht
      simp at ht
    refine ⟨t, ht_meas, ht_mem, ?_⟩
    simp only [ht_meas, ht_mem, iSup_true] at ht
    exact ht.le
  · refine ⟨∅, MeasurableSet.empty, by rw [Measure.restrict_empty]; infer_instance, ?_⟩
    rw [tsub_eq_zero_of_le hC_lt]
    exact zero_le

-- Note: `Set` has no computational content, but Lean still attempts to compile it.
-- See https://github.com/leanprover/lean4/issues/14084.
/--
Definition of `Measure.sigmaFiniteSetGE` / `Measure.sigmaFiniteSetGE` 的定义

English:
definition Measure.sigmaFiniteSetGE
  signature: (μ ν : Measure α) [IsFiniteMeasure ν] (n : Nat)
  body: (exists_isSigmaFiniteSet_measure_ge μ ν n).choose

中文:
定义 测度.sigmaFiniteSetGE
  签名: (μ ν : 测度 α) [是有限测度 ν] (n : 自然数)
  定义体: (exists_isSigmaFiniteSet_measure_ge μ ν n).choose

Depends on / 依赖: exists_isSigmaFiniteSet_measure_ge
-/
noncomputable def Measure.sigmaFiniteSetGE (μ ν : Measure α) [IsFiniteMeasure ν] (n : Nat) : Set α :=
  (exists_isSigmaFiniteSet_measure_ge μ ν n).choose

/--
lemma `measurableSet_sigmaFiniteSetGE` / 引理 `measurableSet_sigmaFiniteSetGE`

English:
lemma measurableSet_sigmaFiniteSetGE
  given: [IsFiniteMeasure ν] (n : Nat)
  proof: (exists_isSigmaFiniteSet_measure_ge μ ν n).choose_spec.1

中文:
引理 measurableSet_sigmaFiniteSetGE
  条件: [是有限测度 ν] (n : 自然数)
  证明: (exists_isSigmaFiniteSet_measure_ge μ ν n).choose_spec.1

Depends on / 依赖: choose_spec, exists_isSigmaFiniteSet_measure_ge
-/
lemma measurableSet_sigmaFiniteSetGE [IsFiniteMeasure ν] (n : Nat) :
    MeasurableSet (μ.sigmaFiniteSetGE ν n) :=
  (exists_isSigmaFiniteSet_measure_ge μ ν n).choose_spec.1

/--
lemma `sigmaFinite_restrict_sigmaFiniteSetGE` / 引理 `sigmaFinite_restrict_sigmaFiniteSetGE`

English:
lemma sigmaFinite_restrict_sigmaFiniteSetGE
  given: (μ ν : Measure α) [IsFiniteMeasure ν] (n : Nat)
  proof: (exists_isSigmaFiniteSet_measure_ge μ ν n).choose_spec.2.1

中文:
引理 sigmaFinite_restrict_sigmaFiniteSetGE
  条件: (μ ν : 测度 α) [是有限测度 ν] (n : 自然数)
  证明: (exists_isSigmaFiniteSet_measure_ge μ ν n).choose_spec.2.1

Depends on / 依赖: choose_spec, exists_isSigmaFiniteSet_measure_ge
-/
lemma sigmaFinite_restrict_sigmaFiniteSetGE (μ ν : Measure α) [IsFiniteMeasure ν] (n : Nat) :
    SigmaFinite (μ.restrict (μ.sigmaFiniteSetGE ν n)) :=
  (exists_isSigmaFiniteSet_measure_ge μ ν n).choose_spec.2.1

/--
lemma `measure_sigmaFiniteSetGE_le` / 引理 `measure_sigmaFiniteSetGE_le`

English:
lemma measure_sigmaFiniteSetGE_le
  given: (μ ν : Measure α) [IsFiniteMeasure ν] (n : Nat)
  proof: by
  refine (le_iSup (f := fun s => _)
    (sigmaFinite_restrict_sigmaFiniteSetGE μ ν n)).trans ?_
  exact le_iSup₂ (f := fun s _ => ⨆ (_ : SigmaFinite (μ.restrict s)), ν s) (μ.sigmaFiniteSetGE ν n)
    (measurableSet_sigmaFiniteSetGE n)

中文:
引理 measure_sigmaFiniteSetGE_le
  条件: (μ ν : 测度 α) [是有限测度 ν] (n : 自然数)
  证明: by
  refine (le_iSup (f := fun s => _)
    (sigmaFinite_restrict_sigmaFiniteSetGE μ ν n)).trans ?_
  exact le_iSup₂ (f := fun s _ => ⨆ (_ : SigmaFinite (μ.restrict s)), ν s) (μ.sigmaFiniteSetGE ν n)
    (measurableSet_sigmaFiniteSetGE n)

Depends on / 依赖: SigmaFinite, le_iSup, measurableSet_sigmaFiniteSetGE, restrict, sigmaFiniteSetGE, sigmaFinite_restrict_sigmaFiniteSetGE
-/
lemma measure_sigmaFiniteSetGE_le (μ ν : Measure α) [IsFiniteMeasure ν] (n : Nat) :
    ν (μ.sigmaFiniteSetGE ν n)
      <= ⨆ (s) (_ : MeasurableSet s) (_ : SigmaFinite (μ.restrict s)), ν s := by
  refine (le_iSup (f := fun s => _)
    (sigmaFinite_restrict_sigmaFiniteSetGE μ ν n)).trans ?_
  exact le_iSup₂ (f := fun s _ => ⨆ (_ : SigmaFinite (μ.restrict s)), ν s) (μ.sigmaFiniteSetGE ν n)
    (measurableSet_sigmaFiniteSetGE n)

/--
lemma `measure_sigmaFiniteSetGE_ge` / 引理 `measure_sigmaFiniteSetGE_ge`

English:
lemma measure_sigmaFiniteSetGE_ge
  given: (μ ν : Measure α) [IsFiniteMeasure ν] (n : Nat)
  proof: (exists_isSigmaFiniteSet_measure_ge μ ν n).choose_spec.2.2

中文:
引理 measure_sigmaFiniteSetGE_ge
  条件: (μ ν : 测度 α) [是有限测度 ν] (n : 自然数)
  证明: (exists_isSigmaFiniteSet_measure_ge μ ν n).choose_spec.2.2

Depends on / 依赖: choose_spec, exists_isSigmaFiniteSet_measure_ge
-/
lemma measure_sigmaFiniteSetGE_ge (μ ν : Measure α) [IsFiniteMeasure ν] (n : Nat) :
    (⨆ (s) (_ : MeasurableSet s) (_ : SigmaFinite (μ.restrict s)), ν s) - 1 / n
      <= ν (μ.sigmaFiniteSetGE ν n) :=
  (exists_isSigmaFiniteSet_measure_ge μ ν n).choose_spec.2.2

/--
lemma `tendsto_measure_sigmaFiniteSetGE` / 引理 `tendsto_measure_sigmaFiniteSetGE`

English:
lemma tendsto_measure_sigmaFiniteSetGE
  given: (μ ν : Measure α) [IsFiniteMeasure ν]
  proof: by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le ?_
    tendsto_const_nhds (measure_sigmaFiniteSetGE_ge μ ν) (measure_sigmaFiniteSetGE_le μ ν)
  nth_rewrite 2 [← tsub_zero (⨆ (s) (_ : MeasurableSet s) (_ : SigmaFinite (μ.restrict s)), ν s)]
  refine ENNReal.Tendsto.sub tendsto_const_nhds ?_ (Or

中文:
引理 tendsto_measure_sigmaFiniteSetGE
  条件: (μ ν : 测度 α) [是有限测度 ν]
  证明: by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le ?_
    tendsto_const_nhds (measure_sigmaFiniteSetGE_ge μ ν) (measure_sigmaFiniteSetGE_le μ ν)
  nth_rewrite 2 [← tsub_zero (⨆ (s) (_ : MeasurableSet s) (_ : SigmaFinite (μ.restrict s)), ν s)]
  refine ENNReal.Tendsto.sub tendsto_const_nhds ?_ (Or

Depends on / 依赖: ENNReal, ENNReal.Tendsto.sub, ENNReal.tendsto_inv_nat_nhds_zero, ENNReal.zero_ne_top, MeasurableSet, Or.inr, SigmaFinite, Tendsto, measure_sigmaFiniteSetGE_ge, measure_sigmaFiniteSetGE_le, nth_rewrite, one_div, restrict, tendsto_const_nhds, tendsto_inv_nat_nhds_zero, tendsto_of_tendsto_of_tendsto_of_le_of_le, tsub_zero, zero_ne_top
-/
lemma tendsto_measure_sigmaFiniteSetGE (μ ν : Measure α) [IsFiniteMeasure ν] :
    Tendsto (fun n => ν (μ.sigmaFiniteSetGE ν n)) atTop
      (𝓝 (⨆ (s) (_ : MeasurableSet s) (_ : SigmaFinite (μ.restrict s)), ν s)) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le ?_
    tendsto_const_nhds (measure_sigmaFiniteSetGE_ge μ ν) (measure_sigmaFiniteSetGE_le μ ν)
  nth_rewrite 2 [← tsub_zero (⨆ (s) (_ : MeasurableSet s) (_ : SigmaFinite (μ.restrict s)), ν s)]
  refine ENNReal.Tendsto.sub tendsto_const_nhds ?_ (Or.inr ENNReal.zero_ne_top)
  simp only [one_div]
  exact ENNReal.tendsto_inv_nat_nhds_zero

-- Note: `Set` has no computational content, but Lean still attempts to compile it.
-- See https://github.com/leanprover/lean4/issues/14084.
/--
Definition of `Measure.sigmaFiniteSetWRT'` / `Measure.sigmaFiniteSetWRT'` 的定义

English:
definition Measure.sigmaFiniteSetWRT'
  signature: (μ ν : Measure α) [IsFiniteMeasure ν]
  body: ⋃ n, μ.sigmaFiniteSetGE ν n

中文:
定义 测度.sigmaFiniteSetWRT'
  签名: (μ ν : 测度 α) [是有限测度 ν]
  定义体: ⋃ n, μ.sigmaFiniteSetGE ν n

Depends on / 依赖: sigmaFiniteSetGE
-/
noncomputable def Measure.sigmaFiniteSetWRT' (μ ν : Measure α) [IsFiniteMeasure ν] : Set α :=
  ⋃ n, μ.sigmaFiniteSetGE ν n

/--
lemma `measurableSet_sigmaFiniteSetWRT'` / 引理 `measurableSet_sigmaFiniteSetWRT'`

English:
lemma measurableSet_sigmaFiniteSetWRT'
  given: [IsFiniteMeasure ν]
  proof: MeasurableSet.iUnion measurableSet_sigmaFiniteSetGE

中文:
引理 measurableSet_sigmaFiniteSetWRT'
  条件: [是有限测度 ν]
  证明: MeasurableSet.iUnion measurableSet_sigmaFiniteSetGE

Depends on / 依赖: MeasurableSet, MeasurableSet.iUnion, iUnion, measurableSet_sigmaFiniteSetGE
-/
lemma measurableSet_sigmaFiniteSetWRT' [IsFiniteMeasure ν] :
    MeasurableSet (μ.sigmaFiniteSetWRT' ν) :=
  MeasurableSet.iUnion measurableSet_sigmaFiniteSetGE

/--
lemma `sigmaFinite_restrict_sigmaFiniteSetWRT'` / 引理 `sigmaFinite_restrict_sigmaFiniteSetWRT'`

English:
lemma sigmaFinite_restrict_sigmaFiniteSetWRT'
  given: (μ ν : Measure α) [IsFiniteMeasure ν]
  proof: by
  have := sigmaFinite_restrict_sigmaFiniteSetGE μ ν
  let f : Nat × Nat -> Set α := fun p : Nat × Nat => (μ.sigmaFiniteSetWRT' ν)ᶜ
    union (spanningSets (μ.restrict (μ.sigmaFiniteSetGE ν p.1)) p.2 inter (μ.sigmaFiniteSetGE ν p.1))
  suffices (μ.restrict (μ.sigmaFiniteSetWRT' ν)).FiniteSpanningS

中文:
引理 sigmaFinite_restrict_sigmaFiniteSetWRT'
  条件: (μ ν : 测度 α) [是有限测度 ν]
  证明: by
  have := sigmaFinite_restrict_sigmaFiniteSetGE μ ν
  let f : Nat × Nat -> Set α := fun p : Nat × Nat => (μ.sigmaFiniteSetWRT' ν)ᶜ
    union (spanningSets (μ.restrict (μ.sigmaFiniteSetGE ν p.1)) p.2 inter (μ.sigmaFiniteSetGE ν p.1))
  suffices (μ.restrict (μ.sigmaFiniteSetWRT' ν)).FiniteSpanningS

Depends on / 依赖: FiniteSpanningSetsIn, Nat.pairEquiv.symm, Nat.pairEquiv_symm_apply, Set.range, measure_union_lt_top_i, pairEquiv, pairEquiv_symm_apply, restrict, sigmaFinite, sigmaFiniteSetGE, sigmaFiniteSetWRT, sigmaFinite_restrict_sigmaFiniteSetGE, spanningSets, this.sigmaFinite
-/
lemma sigmaFinite_restrict_sigmaFiniteSetWRT' (μ ν : Measure α) [IsFiniteMeasure ν] :
    SigmaFinite (μ.restrict (μ.sigmaFiniteSetWRT' ν)) := by
  have := sigmaFinite_restrict_sigmaFiniteSetGE μ ν
  let f : Nat × Nat -> Set α := fun p : Nat × Nat => (μ.sigmaFiniteSetWRT' ν)ᶜ
    union (spanningSets (μ.restrict (μ.sigmaFiniteSetGE ν p.1)) p.2 inter (μ.sigmaFiniteSetGE ν p.1))
  suffices (μ.restrict (μ.sigmaFiniteSetWRT' ν)).FiniteSpanningSetsIn (Set.range f) from
    this.sigmaFinite
  let e : Nat ≃ Nat × Nat := Nat.pairEquiv.symm
  refine ⟨fun n => f (e n), fun _ => by simp, fun n => ?_, ?_⟩
  · simp only [Nat.pairEquiv_symm_apply, measure_union_lt_top_iff, f, e]
    rw [Measure.restrict_apply' measurableSet_sigmaFiniteSetWRT']; rw [Set.compl_inter_self]; rw [Measure.restrict_apply' measurableSet_sigmaFiniteSetWRT']
    simp only [measure_empty, ENNReal.zero_lt_top, true_and]
    refine (measure_mono Set.inter_subset_left).trans_lt ?_
    rw [← Measure.restrict_apply' (measurableSet_sigmaFiniteSetGE _)]
    exact measure_spanningSets_lt_top _ _
  · simp only [Nat.pairEquiv_symm_apply, f, e]
    rw [← Set.union_iUnion]
    suffices ⋃ n, (spanningSets (μ.restrict (μ.sigmaFiniteSetGE ν (Nat.unpair n).1)) n.unpair.2
        inter μ.sigmaFiniteSetGE ν n.unpair.1) = μ.sigmaFiniteSetWRT' ν by
      rw [this]; rw [Set.compl_union_self]
    calc ⋃ n, (spanningSets (μ.restrict (μ.sigmaFiniteSetGE ν (Nat.unpair n).1)) n.unpair.2
        inter μ.sigmaFiniteSetGE ν n.unpair.1)
      = ⋃ n, ⋃ m, (spanningSets (μ.restrict (μ.sigmaFiniteSetGE ν n)) m
            inter μ.sigmaFiniteSetGE ν n) :=
          Set.iUnion_unpair (fun n m => spanningSets (μ.restrict (μ.sigmaFiniteSetGE ν n)) m
            inter μ.sigmaFiniteSetGE ν n)
    _ = ⋃ n, μ.sigmaFiniteSetGE ν n := by
        refine Set.iUnion_congr (fun n => ?_)
        rw [← Set.iUnion_inter]; rw [iUnion_spanningSets]; rw [Set.univ_inter]
    _ = μ.sigmaFiniteSetWRT' ν := rfl

/--
lemma `measure_sigmaFiniteSetWRT'` / 引理 `measure_sigmaFiniteSetWRT'`

English:
lemma measure_sigmaFiniteSetWRT'
  given: (μ ν : Measure α) [IsFiniteMeasure ν]
  proof: by
  apply le_antisymm
  · refine (le_iSup (f := fun _ => _)
      (sigmaFinite_restrict_sigmaFiniteSetWRT' μ ν)).trans ?_
    exact le_iSup₂ (f := fun s _ => ⨆ (_ : SigmaFinite (μ.restrict s)), ν s) (μ.sigmaFiniteSetWRT' ν)
      measurableSet_sigmaFiniteSetWRT'
  · exact le_of_tendsto' (tendsto_me

中文:
引理 measure_sigmaFiniteSetWRT'
  条件: (μ ν : 测度 α) [是有限测度 ν]
  证明: by
  apply le_antisymm
  · refine (le_iSup (f := fun _ => _)
      (sigmaFinite_restrict_sigmaFiniteSetWRT' μ ν)).trans ?_
    exact le_iSup₂ (f := fun s _ => ⨆ (_ : SigmaFinite (μ.restrict s)), ν s) (μ.sigmaFiniteSetWRT' ν)
      measurableSet_sigmaFiniteSetWRT'
  · exact le_of_tendsto' (tendsto_me

Depends on / 依赖: Set.subset_iUnion, SigmaFinite, le_antisymm, le_iSup, le_of_tendsto, measurableSet_sigmaFiniteSetWRT, measure_mono, restrict, sigmaFiniteSetWRT, sigmaFinite_restrict_sigmaFiniteSetWRT, subset_iUnion, tendsto_measure_sigmaFiniteSetGE
-/
lemma measure_sigmaFiniteSetWRT' (μ ν : Measure α) [IsFiniteMeasure ν] :
    ν (μ.sigmaFiniteSetWRT' ν)
      = ⨆ (s) (_ : MeasurableSet s) (_ : SigmaFinite (μ.restrict s)), ν s := by
  apply le_antisymm
  · refine (le_iSup (f := fun _ => _)
      (sigmaFinite_restrict_sigmaFiniteSetWRT' μ ν)).trans ?_
    exact le_iSup₂ (f := fun s _ => ⨆ (_ : SigmaFinite (μ.restrict s)), ν s) (μ.sigmaFiniteSetWRT' ν)
      measurableSet_sigmaFiniteSetWRT'
  · exact le_of_tendsto' (tendsto_measure_sigmaFiniteSetGE μ ν)
      (fun _ => measure_mono (Set.subset_iUnion _ _))

/--
lemma `measure_eq_top_of_subset_compl_sigmaFiniteSetWRT'_of_measurableSet` / 引理 `measure_eq_top_of_subset_compl_sigmaFiniteSetWRT'_of_measurableSet`

English:
lemma measure_eq_top_of_subset_compl_sigmaFiniteSetWRT'_of_measurableSet
  statement: [IsFiniteMeasure ν]
  proof: by
  suffices ¬ SigmaFinite (μ.restrict s) by
    by_contra h
    have h_lt_top : Fact (μ s < ∞) := ⟨Ne.lt_top h⟩
    exact this inferInstance
  intro hsσ
  have h_lt : ν (μ.sigmaFiniteSetWRT' ν) < ν (μ.sigmaFiniteSetWRT' ν union s) := by
    rw [measure_union _ hs]
    · exact ENNReal.lt_add_right 

中文:
引理 measure_eq_top_of_subset_compl_sigmaFiniteSetWRT'_of_measurableSet
  结论: [是有限测度 ν]
  证明: by
  suffices ¬ SigmaFinite (μ.restrict s) by
    by_contra h
    have h_lt_top : Fact (μ s < ∞) := ⟨Ne.lt_top h⟩
    exact this inferInstance
  intro hsσ
  have h_lt : ν (μ.sigmaFiniteSetWRT' ν) < ν (μ.sigmaFiniteSetWRT' ν union s) := by
    rw [measure_union _ hs]
    · exact ENNReal.lt_add_right 

Depends on / 依赖: ENNReal, ENNReal.lt_add_right, Ne.lt_top, SigmaFinite, conv_rhs, disjoint_compl_right, disjoint_compl_right.mono_right, h_le, h_lt, h_lt_top, hs_subset, le_iSup, lt_add_right, lt_top, measure_ne_top, measure_sigmaFiniteSetWRT, measure_union, mono_right, restrict, sigmaFiniteSetWRT
-/
lemma measure_eq_top_of_subset_compl_sigmaFiniteSetWRT'_of_measurableSet [IsFiniteMeasure ν]
    (hs : MeasurableSet s) (hs_subset : s subseteq (μ.sigmaFiniteSetWRT' ν)ᶜ) (hνs : ν s != 0) :
    μ s = ∞ := by
  suffices ¬ SigmaFinite (μ.restrict s) by
    by_contra h
    have h_lt_top : Fact (μ s < ∞) := ⟨Ne.lt_top h⟩
    exact this inferInstance
  intro hsσ
  have h_lt : ν (μ.sigmaFiniteSetWRT' ν) < ν (μ.sigmaFiniteSetWRT' ν union s) := by
    rw [measure_union _ hs]
    · exact ENNReal.lt_add_right (measure_ne_top _ _) hνs
    · exact disjoint_compl_right.mono_right hs_subset
  have h_le : ν (μ.sigmaFiniteSetWRT' ν union s) <= ν (μ.sigmaFiniteSetWRT' ν) := by
    conv_rhs => rw [measure_sigmaFiniteSetWRT']
    refine (le_iSup
      (f := fun (_ : SigmaFinite (μ.restrict (μ.sigmaFiniteSetWRT' ν union s))) => _) ?_).trans ?_
    · have := sigmaFinite_restrict_sigmaFiniteSetWRT' μ ν
      infer_instance
    · exact le_iSup₂ (f := fun s _ => ⨆ (_ : SigmaFinite (μ.restrict _)), ν s)
        (μ.sigmaFiniteSetWRT' ν union s) (measurableSet_sigmaFiniteSetWRT'.union hs)
  exact h_lt.not_ge h_le

/--
lemma `measure_eq_top_of_subset_compl_sigmaFiniteSetWRT'` / 引理 `measure_eq_top_of_subset_compl_sigmaFiniteSetWRT'`

English:
lemma measure_eq_top_of_subset_compl_sigmaFiniteSetWRT'
  statement: [IsFiniteMeasure ν]
  proof: by
  rw [measure_eq_iInf]
  simp_rw [iInf_eq_top]
  suffices forall t, t subseteq (μ.sigmaFiniteSetWRT' ν)ᶜ -> s subseteq t -> MeasurableSet t -> μ t = ∞ by
    intro t hts ht
    suffices μ (t inter (μ.sigmaFiniteSetWRT' ν)ᶜ) = ∞ from
      measure_mono_top Set.inter_subset_left this
    have hs_su

中文:
引理 measure_eq_top_of_subset_compl_sigmaFiniteSetWRT'
  结论: [是有限测度 ν]
  证明: by
  rw [measure_eq_iInf]
  simp_rw [iInf_eq_top]
  suffices forall t, t subseteq (μ.sigmaFiniteSetWRT' ν)ᶜ -> s subseteq t -> MeasurableSet t -> μ t = ∞ by
    intro t hts ht
    suffices μ (t inter (μ.sigmaFiniteSetWRT' ν)ᶜ) = ∞ from
      measure_mono_top Set.inter_subset_left this
    have hs_su
-/
lemma measure_eq_top_of_subset_compl_sigmaFiniteSetWRT' [IsFiniteMeasure ν]
    (hs_subset : s subseteq (μ.sigmaFiniteSetWRT' ν)ᶜ) (hνs : ν s != 0) :
    μ s = ∞ := by
  rw [measure_eq_iInf]
  simp_rw [iInf_eq_top]
  suffices forall t, t subseteq (μ.sigmaFiniteSetWRT' ν)ᶜ -> s subseteq t -> MeasurableSet t -> μ t = ∞ by
    intro t hts ht
    suffices μ (t inter (μ.sigmaFiniteSetWRT' ν)ᶜ) = ∞ from
      measure_mono_top Set.inter_subset_left this
    have hs_subset_t : s subseteq t inter (μ.sigmaFiniteSetWRT' ν)ᶜ := Set.subset_inter hts hs_subset
    exact this (t inter (μ.sigmaFiniteSetWRT' ν)ᶜ) Set.inter_subset_right hs_subset_t
      (ht.inter measurableSet_sigmaFiniteSetWRT'.compl)
  intro t ht_subset hst ht
  refine measure_eq_top_of_subset_compl_sigmaFiniteSetWRT'_of_measurableSet ht ht_subset ?_
  exact fun hνt => hνs (measure_mono_null hst hνt)

end IsFiniteMeasure

section SFinite

/--
lemma `measure_eq_top_of_subset_compl_sigmaFiniteSetWRT` / 引理 `measure_eq_top_of_subset_compl_sigmaFiniteSetWRT`

English:
lemma measure_eq_top_of_subset_compl_sigmaFiniteSetWRT
  statement: [SFinite ν]
  proof: by
  have ⟨ν', hν', hνν', _⟩ := exists_isFiniteMeasure_absolutelyContinuous ν
  have h : exists s : Set α, MeasurableSet s ∧ SigmaFinite (μ.restrict s)
      ∧ (forall t subseteq sᶜ, ν t != 0 -> μ t = ∞) := by
    refine ⟨μ.sigmaFiniteSetWRT' ν', measurableSet_sigmaFiniteSetWRT',
      sigmaFinite_r

中文:
引理 measure_eq_top_of_subset_compl_sigmaFiniteSetWRT
  结论: [SFinite ν]
  证明: by
  have ⟨ν', hν', hνν', _⟩ := exists_isFiniteMeasure_absolutelyContinuous ν
  have h : exists s : Set α, MeasurableSet s ∧ SigmaFinite (μ.restrict s)
      ∧ (forall t subseteq sᶜ, ν t != 0 -> μ t = ∞) := by
    refine ⟨μ.sigmaFiniteSetWRT' ν', measurableSet_sigmaFiniteSetWRT',
      sigmaFinite_r

Depends on / 依赖: MeasurableSet, Measure, Measure.sigmaFiniteSetWRT, SigmaFinite, dif_pos, exists_isFiniteMeasure_absolutelyContinuous, hs_subset, ht_subset, measurableSet_sigmaFiniteSetWRT, measure_eq_top_of_subset_compl_sigmaFiniteSetWRT, restrict, sigmaFiniteSetWRT, sigmaFinite_restrict_sigmaFiniteSetWRT, subseteq
-/
lemma measure_eq_top_of_subset_compl_sigmaFiniteSetWRT [SFinite ν]
    (hs_subset : s subseteq (μ.sigmaFiniteSetWRT ν)ᶜ) (hνs : ν s != 0) :
    μ s = ∞ := by
  have ⟨ν', hν', hνν', _⟩ := exists_isFiniteMeasure_absolutelyContinuous ν
  have h : exists s : Set α, MeasurableSet s ∧ SigmaFinite (μ.restrict s)
      ∧ (forall t subseteq sᶜ, ν t != 0 -> μ t = ∞) := by
    refine ⟨μ.sigmaFiniteSetWRT' ν', measurableSet_sigmaFiniteSetWRT',
      sigmaFinite_restrict_sigmaFiniteSetWRT' _ _,
      fun t ht_subset hνt => measure_eq_top_of_subset_compl_sigmaFiniteSetWRT' ht_subset ?_⟩
    exact fun hν't => hνt (hνν' hν't)
  rw [Measure.sigmaFiniteSetWRT]; rw [dif_pos h] at hs_subset
  exact h.choose_spec.2.2 s hs_subset hνs

/--
lemma `restrict_compl_sigmaFiniteSetWRT` / 引理 `restrict_compl_sigmaFiniteSetWRT`

English:
lemma restrict_compl_sigmaFiniteSetWRT
  given: [SFinite ν] (hμν : μ ≪ ν)
  proof: by
  ext s
  rw [Measure.restrict_apply' measurableSet_sigmaFiniteSetWRT.compl]; rw [Measure.smul_apply]; rw [smul_eq_mul]; rw [Measure.restrict_apply' measurableSet_sigmaFiniteSetWRT.compl]
  by_cases hνs : ν (s inter (μ.sigmaFiniteSetWRT ν)ᶜ) = 0
  · rw [hνs, mul_zero]
    exact hμν hνs
  · rw [EN

中文:
引理 restrict_compl_sigmaFiniteSetWRT
  条件: [SFinite ν] (hμν : μ ≪ ν)
  证明: by
  ext s
  rw [Measure.restrict_apply' measurableSet_sigmaFiniteSetWRT.compl]; rw [Measure.smul_apply]; rw [smul_eq_mul]; rw [Measure.restrict_apply' measurableSet_sigmaFiniteSetWRT.compl]
  by_cases hνs : ν (s inter (μ.sigmaFiniteSetWRT ν)ᶜ) = 0
  · rw [hνs, mul_zero]
    exact hμν hνs
  · rw [EN

Depends on / 依赖: ENNReal, ENNReal.top_mul, Measure, Measure.restrict_apply, Measure.smul_apply, Set.inter_subset_right, inter_subset_right, measurableSet_sigmaFiniteSetWRT, measurableSet_sigmaFiniteSetWRT.compl, measure_eq_top_of_subset_compl_sigmaFiniteSetWRT, mul_zero, restrict_apply, sigmaFiniteSetWRT, smul_apply, smul_eq_mul, top_mul
-/
lemma restrict_compl_sigmaFiniteSetWRT [SFinite ν] (hμν : μ ≪ ν) :
    μ.restrict (μ.sigmaFiniteSetWRT ν)ᶜ = ∞ • ν.restrict (μ.sigmaFiniteSetWRT ν)ᶜ := by
  ext s
  rw [Measure.restrict_apply' measurableSet_sigmaFiniteSetWRT.compl]; rw [Measure.smul_apply]; rw [smul_eq_mul]; rw [Measure.restrict_apply' measurableSet_sigmaFiniteSetWRT.compl]
  by_cases hνs : ν (s inter (μ.sigmaFiniteSetWRT ν)ᶜ) = 0
  · rw [hνs, mul_zero]
    exact hμν hνs
  · rw [ENNReal.top_mul hνs, measure_eq_top_of_subset_compl_sigmaFiniteSetWRT
      Set.inter_subset_right hνs]

end SFinite

@[simp]
/--
lemma `measure_compl_sigmaFiniteSetWRT` / 引理 `measure_compl_sigmaFiniteSetWRT`

English:
lemma measure_compl_sigmaFiniteSetWRT
  given: (hμν : μ ≪ ν) [SigmaFinite μ] [SFinite ν]
  proof: by
  have h : ν (μ.sigmaFiniteSetWRT ν)ᶜ != 0 -> μ (μ.sigmaFiniteSetWRT ν)ᶜ = ∞ :=
    measure_eq_top_of_subset_compl_sigmaFiniteSetWRT subset_rfl
  by_contra h0
  refine ENNReal.top_ne_zero ?_
  rw [← h h0]; rw [← Measure.iSup_restrict_spanningSets]
  simp_rw [Measure.restrict_apply' (measurableSet

中文:
引理 measure_compl_sigmaFiniteSetWRT
  条件: (hμν : μ ≪ ν) [σ有限 μ] [SFinite ν]
  证明: by
  have h : ν (μ.sigmaFiniteSetWRT ν)ᶜ != 0 -> μ (μ.sigmaFiniteSetWRT ν)ᶜ = ∞ :=
    measure_eq_top_of_subset_compl_sigmaFiniteSetWRT subset_rfl
  by_contra h0
  refine ENNReal.top_ne_zero ?_
  rw [← h h0]; rw [← Measure.iSup_restrict_spanningSets]
  simp_rw [Measure.restrict_apply' (measurableSet

Depends on / 依赖: ENNReal, ENNReal.iSup_eq_zero, ENNReal.top_ne_zero, Measure, Measure.iSup_restrict_spanningSets, Measure.restrict_apply, Set.inter_subset_left, h_ne_zero, h_zero_top, iSup_eq_zero, iSup_restrict_spanningSets, inter_subset_left, measurableSet_spanningSets, measure_eq_top_of_subset_compl_sigmaFiniteSetWRT, restrict_apply, sigmaFiniteSetWRT, simp_rw, spanningSets, subset_rfl, top_ne_zero
-/
lemma measure_compl_sigmaFiniteSetWRT (hμν : μ ≪ ν) [SigmaFinite μ] [SFinite ν] :
    ν (μ.sigmaFiniteSetWRT ν)ᶜ = 0 := by
  have h : ν (μ.sigmaFiniteSetWRT ν)ᶜ != 0 -> μ (μ.sigmaFiniteSetWRT ν)ᶜ = ∞ :=
    measure_eq_top_of_subset_compl_sigmaFiniteSetWRT subset_rfl
  by_contra h0
  refine ENNReal.top_ne_zero ?_
  rw [← h h0]; rw [← Measure.iSup_restrict_spanningSets]
  simp_rw [Measure.restrict_apply' (measurableSet_spanningSets μ _), ENNReal.iSup_eq_zero]
  intro i
  by_contra h_ne_zero
  have h_zero_top := measure_eq_top_of_subset_compl_sigmaFiniteSetWRT
    (Set.inter_subset_left : (μ.sigmaFiniteSetWRT ν)ᶜ inter spanningSets μ i subseteq _) ?_
  swap; · exact fun h => h_ne_zero (hμν h)
  refine absurd h_zero_top (ne_of_lt ?_)
  exact (measure_mono Set.inter_subset_right).trans_lt (measure_spanningSets_lt_top μ i)

section SigmaFiniteSet

-- Note: `Set` has no computational content, but Lean still attempts to compile it.
-- See https://github.com/leanprover/lean4/issues/14084.
/--
Definition of `Measure.sigmaFiniteSet` / `Measure.sigmaFiniteSet` 的定义

English:
definition Measure.sigmaFiniteSet
  signature: (μ : Measure α)
  body: μ.sigmaFiniteSetWRT μ

@[measurability]

中文:
定义 测度.sigmaFiniteSet
  签名: (μ : 测度 α)
  定义体: μ.sigmaFiniteSetWRT μ

@[measurability]

Depends on / 依赖: PartialOrder, PartialOrder.lift, finset, sigmaFiniteSetWRT
-/
noncomputable def Measure.sigmaFiniteSet (μ : Measure α) : Set α := μ.sigmaFiniteSetWRT μ

@[measurability]
/--
lemma `measurableSet_sigmaFiniteSet` / 引理 `measurableSet_sigmaFiniteSet`

English:
lemma measurableSet_sigmaFiniteSet
  statement: MeasurableSet μ.sigmaFiniteSet
  proof: measurableSet_sigmaFiniteSetWRT

中文:
引理 measurableSet_sigmaFiniteSet
  结论: 可测集 μ.sigmaFiniteSet
  证明: measurableSet_sigmaFiniteSetWRT

Depends on / 依赖: measurableSet_sigmaFiniteSetWRT
-/
lemma measurableSet_sigmaFiniteSet : MeasurableSet μ.sigmaFiniteSet :=
  measurableSet_sigmaFiniteSetWRT

/--
lemma `measure_eq_zero_or_top_of_subset_compl_sigmaFiniteSet` / 引理 `measure_eq_zero_or_top_of_subset_compl_sigmaFiniteSet`

English:
lemma measure_eq_zero_or_top_of_subset_compl_sigmaFiniteSet
  statement: [SFinite μ]
  proof: by
  rw [or_iff_not_imp_left]
  exact measure_eq_top_of_subset_compl_sigmaFiniteSetWRT ht_subset

中文:
引理 measure_eq_zero_or_top_of_subset_compl_sigmaFiniteSet
  结论: [SFinite μ]
  证明: by
  rw [or_iff_not_imp_left]
  exact measure_eq_top_of_subset_compl_sigmaFiniteSetWRT ht_subset

Depends on / 依赖: ht_subset, measure_eq_top_of_subset_compl_sigmaFiniteSetWRT, or_iff_not_imp_left
-/
lemma measure_eq_zero_or_top_of_subset_compl_sigmaFiniteSet [SFinite μ]
    (ht_subset : t subseteq μ.sigmaFiniteSetᶜ) :
    μ t = 0 ∨ μ t = ∞ := by
  rw [or_iff_not_imp_left]
  exact measure_eq_top_of_subset_compl_sigmaFiniteSetWRT ht_subset

/--
lemma `restrict_compl_sigmaFiniteSet_eq_zero_or_top` / 引理 `restrict_compl_sigmaFiniteSet_eq_zero_or_top`

English:
lemma restrict_compl_sigmaFiniteSet_eq_zero_or_top
  given: (μ : Measure α) [SFinite μ] (s : Set α)
  proof: by
  rw [Measure.restrict_apply' measurableSet_sigmaFiniteSet.compl]
  exact measure_eq_zero_or_top_of_subset_compl_sigmaFiniteSet Set.inter_subset_right

中文:
引理 restrict_compl_sigmaFiniteSet_eq_zero_or_top
  条件: (μ : 测度 α) [SFinite μ] (s : 集合 α)
  证明: by
  rw [Measure.restrict_apply' measurableSet_sigmaFiniteSet.compl]
  exact measure_eq_zero_or_top_of_subset_compl_sigmaFiniteSet Set.inter_subset_right

Depends on / 依赖: Measure, Measure.restrict_apply, Set.inter_subset_right, inter_subset_right, measurableSet_sigmaFiniteSet, measurableSet_sigmaFiniteSet.compl, measure_eq_zero_or_top_of_subset_compl_sigmaFiniteSet, restrict_apply
-/
lemma restrict_compl_sigmaFiniteSet_eq_zero_or_top (μ : Measure α) [SFinite μ] (s : Set α) :
    μ.restrict μ.sigmaFiniteSetᶜ s = 0 ∨ μ.restrict μ.sigmaFiniteSetᶜ s = ∞ := by
  rw [Measure.restrict_apply' measurableSet_sigmaFiniteSet.compl]
  exact measure_eq_zero_or_top_of_subset_compl_sigmaFiniteSet Set.inter_subset_right

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SigmaFinite (μ.restrict μ.sigmaFiniteSet)
  body: by
  rw [Measure.sigmaFiniteSet]
  infer_instance

中文:
实例 :
  签名: σ有限 (μ.restrict μ.sigmaFiniteSet)
  定义体: by
  rw [Measure.sigmaFiniteSet]
  infer_instance

Depends on / 依赖: Measure, Measure.sigmaFiniteSet, infer_instance, sigmaFiniteSet
-/
instance : SigmaFinite (μ.restrict μ.sigmaFiniteSet) := by
  rw [Measure.sigmaFiniteSet]
  infer_instance

/--
lemma `sigmaFinite_of_measure_compl_sigmaFiniteSet_eq_zero` / 引理 `sigmaFinite_of_measure_compl_sigmaFiniteSet_eq_zero`

English:
lemma sigmaFinite_of_measure_compl_sigmaFiniteSet_eq_zero
  given: (h : μ μ.sigmaFiniteSetᶜ = 0)
  proof: by
  rw [← Measure.restrict_add_restrict_compl (μ := μ) (measurableSet_sigmaFiniteSet (μ := μ))]; rw [Measure.restrict_eq_zero.mpr h]; rw [add_zero]
  infer_instance

@[simp]

中文:
引理 sigmaFinite_of_measure_compl_sigmaFiniteSet_eq_zero
  条件: (h : μ μ.sigmaFiniteSetᶜ = 0)
  证明: by
  rw [← Measure.restrict_add_restrict_compl (μ := μ) (measurableSet_sigmaFiniteSet (μ := μ))]; rw [Measure.restrict_eq_zero.mpr h]; rw [add_zero]
  infer_instance

@[simp]

Depends on / 依赖: Measure, Measure.restrict_add_restrict_compl, Measure.restrict_eq_zero.mpr, add_zero, infer_instance, measurableSet_sigmaFiniteSet, restrict_add_restrict_compl, restrict_eq_zero
-/
lemma sigmaFinite_of_measure_compl_sigmaFiniteSet_eq_zero (h : μ μ.sigmaFiniteSetᶜ = 0) :
    SigmaFinite μ := by
  rw [← Measure.restrict_add_restrict_compl (μ := μ) (measurableSet_sigmaFiniteSet (μ := μ))]; rw [Measure.restrict_eq_zero.mpr h]; rw [add_zero]
  infer_instance

@[simp]
/--
lemma `measure_compl_sigmaFiniteSet` / 引理 `measure_compl_sigmaFiniteSet`

English:
lemma measure_compl_sigmaFiniteSet
  given: (μ : Measure α) [SigmaFinite μ]
  statement: μ μ.sigmaFiniteSetᶜ = 0
  proof: measure_compl_sigmaFiniteSetWRT Measure.AbsolutelyContinuous.rfl

中文:
引理 measure_compl_sigmaFiniteSet
  条件: (μ : 测度 α) [σ有限 μ]
  结论: μ μ.sigmaFiniteSetᶜ = 0
  证明: measure_compl_sigmaFiniteSetWRT Measure.AbsolutelyContinuous.rfl

Depends on / 依赖: AbsolutelyContinuous, Measure, Measure.AbsolutelyContinuous.rfl, measure_compl_sigmaFiniteSetWRT
-/
lemma measure_compl_sigmaFiniteSet (μ : Measure α) [SigmaFinite μ] : μ μ.sigmaFiniteSetᶜ = 0 :=
  measure_compl_sigmaFiniteSetWRT Measure.AbsolutelyContinuous.rfl

/--
lemma `measure_compl_sigmaFiniteSet_eq_zero_iff_sigmaFinite` / 引理 `measure_compl_sigmaFiniteSet_eq_zero_iff_sigmaFinite`

English:
lemma measure_compl_sigmaFiniteSet_eq_zero_iff_sigmaFinite
  given: (μ : Measure α)
  proof: ⟨sigmaFinite_of_measure_compl_sigmaFiniteSet_eq_zero, fun _ => measure_compl_sigmaFiniteSet μ⟩

中文:
引理 measure_compl_sigmaFiniteSet_eq_zero_iff_sigmaFinite
  条件: (μ : 测度 α)
  证明: ⟨sigmaFinite_of_measure_compl_sigmaFiniteSet_eq_zero, fun _ => measure_compl_sigmaFiniteSet μ⟩

Depends on / 依赖: measure_compl_sigmaFiniteSet, sigmaFinite_of_measure_compl_sigmaFiniteSet_eq_zero
-/
lemma measure_compl_sigmaFiniteSet_eq_zero_iff_sigmaFinite (μ : Measure α) :
    μ μ.sigmaFiniteSetᶜ = 0 ↔ SigmaFinite μ :=
  ⟨sigmaFinite_of_measure_compl_sigmaFiniteSet_eq_zero, fun _ => measure_compl_sigmaFiniteSet μ⟩

end SigmaFiniteSet

end MeasureTheory
