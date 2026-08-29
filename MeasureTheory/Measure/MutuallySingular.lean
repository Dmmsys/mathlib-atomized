/-
Copyright (c) 2021 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying, Yury Kudryashov
-/
module

public import Mathlib.MeasureTheory.Measure.Restrict

/-! # Mutually singular measures

Two measures `μ`, `ν` are said to be mutually singular (`MeasureTheory.Measure.MutuallySingular`,
localized notation `μ ⟂ₘ ν`) if there exists a measurable set `s` such that `μ s = 0` and
`ν sᶜ = 0`. The measurability of `s` is an unnecessary assumption (see
`MeasureTheory.Measure.MutuallySingular.mk`) but we keep it because this way `rcases (h : μ ⟂ₘ ν)`
gives us a measurable set and usually it is easy to prove measurability.

In this file we define the predicate `MeasureTheory.Measure.MutuallySingular` and prove basic
facts about it.

## Tags

measure, mutually singular
-/

@[expose] public section


open Set

open MeasureTheory NNReal ENNReal Filter

namespace MeasureTheory

namespace Measure

variable {α : Type*} {m0 : MeasurableSpace α} {μ μ₁ μ₂ ν ν₁ ν₂ : Measure α}

/--
Definition of `MutuallySingular` / `MutuallySingular` 的定义

English:
definition MutuallySingular
  signature: {_ : MeasurableSpace α} (μ ν : Measure α)
  body: exists s : Set α, MeasurableSet s ∧ μ s = 0 ∧ ν sᶜ = 0

@[inherit_doc MeasureTheory.Measure.MutuallySingular]
scoped[MeasureTheory] infixl:60 " ⟂ₘ " => MeasureTheory.Measure.MutuallySingular

中文:
定义 MutuallySingular
  签名: {_ : MeasurableSpace α} (μ ν : Measure α)
  定义体: exists s : Set α, MeasurableSet s ∧ μ s = 0 ∧ ν sᶜ = 0

@[inherit_doc MeasureTheory.Measure.MutuallySingular]
scoped[MeasureTheory] infixl:60 " ⟂ₘ " => MeasureTheory.Measure.MutuallySingular

Depends on / 依赖: MeasurableSet
-/
def MutuallySingular {_ : MeasurableSpace α} (μ ν : Measure α) : Prop :=
  exists s : Set α, MeasurableSet s ∧ μ s = 0 ∧ ν sᶜ = 0

@[inherit_doc MeasureTheory.Measure.MutuallySingular]
scoped[MeasureTheory] infixl:60 " ⟂ₘ " => MeasureTheory.Measure.MutuallySingular

namespace MutuallySingular

/--
theorem `mk` / 定理 `mk`

English:
theorem mk
  given: {s t : Set α} (hs : μ s = 0) (ht : ν t = 0) (hst : univ subseteq s union t)
  proof: by
  use toMeasurable μ s, measurableSet_toMeasurable _ _, (measure_toMeasurable _).trans hs
  refine measure_mono_null (fun x hx => (hst trivial).resolve_left fun hxs => hx ?_) ht
  exact subset_toMeasurable _ _ hxs

中文:
定理 mk
  条件: {s t : Set α} (hs : μ s = 0) (ht : ν t = 0) (hst : univ subseteq s union t)
  证明: by
  use toMeasurable μ s, measurableSet_toMeasurable _ _, (measure_toMeasurable _).trans hs
  refine measure_mono_null (fun x hx => (hst trivial).resolve_left fun hxs => hx ?_) ht
  exact subset_toMeasurable _ _ hxs

Depends on / 依赖: measurableSet_toMeasurable, measure_mono_null, measure_toMeasurable, resolve_left, subset_toMeasurable, toMeasurable
-/
theorem mk {s t : Set α} (hs : μ s = 0) (ht : ν t = 0) (hst : univ subseteq s union t) :
    MutuallySingular μ ν := by
  use toMeasurable μ s, measurableSet_toMeasurable _ _, (measure_toMeasurable _).trans hs
  refine measure_mono_null (fun x hx => (hst trivial).resolve_left fun hxs => hx ?_) ht
  exact subset_toMeasurable _ _ hxs

-- Note: `Set` has no computational content, but Lean still attempts to compile it.
-- See https://github.com/leanprover/lean4/issues/14084.
/--
Definition of `nullSet` / `nullSet` 的定义

English:
definition nullSet
  signature: (h : μ ⟂ₘ ν)
  body: h.choose

中文:
定义 nullSet
  签名: (h : μ ⟂ₘ ν)
  定义体: h.choose

Depends on / 依赖: h.choose
-/
noncomputable def nullSet (h : μ ⟂ₘ ν) : Set α := h.choose

/--
lemma `measurableSet_nullSet` / 引理 `measurableSet_nullSet`

English:
lemma measurableSet_nullSet
  given: (h : μ ⟂ₘ ν)
  statement: MeasurableSet h.nullSet
  proof: h.choose_spec.1

@[simp]

中文:
引理 measurableSet_nullSet
  条件: (h : μ ⟂ₘ ν)
  结论: MeasurableSet h.nullSet
  证明: h.choose_spec.1

@[simp]

Depends on / 依赖: choose_spec, h.choose_spec
-/
lemma measurableSet_nullSet (h : μ ⟂ₘ ν) : MeasurableSet h.nullSet := h.choose_spec.1

@[simp]
/--
lemma `measure_nullSet` / 引理 `measure_nullSet`

English:
lemma measure_nullSet
  given: (h : μ ⟂ₘ ν)
  statement: μ h.nullSet = 0
  proof: h.choose_spec.2.1

@[simp]

中文:
引理 measure_nullSet
  条件: (h : μ ⟂ₘ ν)
  结论: μ h.nullSet = 0
  证明: h.choose_spec.2.1

@[simp]

Depends on / 依赖: choose_spec, h.choose_spec
-/
lemma measure_nullSet (h : μ ⟂ₘ ν) : μ h.nullSet = 0 := h.choose_spec.2.1

@[simp]
/--
lemma `measure_compl_nullSet` / 引理 `measure_compl_nullSet`

English:
lemma measure_compl_nullSet
  given: (h : μ ⟂ₘ ν)
  statement: ν h.nullSetᶜ = 0
  proof: h.choose_spec.2.2

中文:
引理 measure_compl_nullSet
  条件: (h : μ ⟂ₘ ν)
  结论: ν h.nullSetᶜ = 0
  证明: h.choose_spec.2.2

Depends on / 依赖: choose_spec, h.choose_spec
-/
lemma measure_compl_nullSet (h : μ ⟂ₘ ν) : ν h.nullSetᶜ = 0 := h.choose_spec.2.2

-- TODO: this is proved by simp, but is not simplified in other contexts without the @[simp]
-- attribute. Also, the linter does not complain about that attribute.
@[simp]
/--
lemma `restrict_nullSet` / 引理 `restrict_nullSet`

English:
lemma restrict_nullSet
  given: (h : μ ⟂ₘ ν)
  statement: μ.restrict h.nullSet = 0
  proof: by simp

中文:
引理 restrict_nullSet
  条件: (h : μ ⟂ₘ ν)
  结论: μ.restrict h.nullSet = 0
  证明: by simp
-/
lemma restrict_nullSet (h : μ ⟂ₘ ν) : μ.restrict h.nullSet = 0 := by simp

-- TODO: this is proved by simp, but is not simplified in other contexts without the @[simp]
-- attribute. Also, the linter does not complain about that attribute.
@[simp]
/--
lemma `restrict_compl_nullSet` / 引理 `restrict_compl_nullSet`

English:
lemma restrict_compl_nullSet
  given: (h : μ ⟂ₘ ν)
  statement: ν.restrict h.nullSetᶜ = 0
  proof: by simp

@[simp]

中文:
引理 restrict_compl_nullSet
  条件: (h : μ ⟂ₘ ν)
  结论: ν.restrict h.nullSetᶜ = 0
  证明: by simp

@[simp]
-/
lemma restrict_compl_nullSet (h : μ ⟂ₘ ν) : ν.restrict h.nullSetᶜ = 0 := by simp

@[simp]
/--
theorem `zero_right` / 定理 `zero_right`

English:
theorem zero_right
  statement: μ ⟂ₘ 0
  proof: ⟨∅, MeasurableSet.empty, measure_empty, rfl⟩

@[symm]

中文:
定理 zero_right
  结论: μ ⟂ₘ 0
  证明: ⟨∅, MeasurableSet.empty, measure_empty, rfl⟩

@[symm]

Depends on / 依赖: MeasurableSet, MeasurableSet.empty, measure_empty
-/
theorem zero_right : μ ⟂ₘ 0 :=
  ⟨∅, MeasurableSet.empty, measure_empty, rfl⟩

@[symm]
/--
theorem `symm` / 定理 `symm`

English:
theorem symm
  given: (h : ν ⟂ₘ μ)
  statement: μ ⟂ₘ ν
  proof: let ⟨i, hi, his, hit⟩ := h
  ⟨iᶜ, hi.compl, hit, (compl_compl i).symm ▸ his⟩

中文:
定理 symm
  条件: (h : ν ⟂ₘ μ)
  结论: μ ⟂ₘ ν
  证明: let ⟨i, hi, his, hit⟩ := h
  ⟨iᶜ, hi.compl, hit, (compl_compl i).symm ▸ his⟩

Depends on / 依赖: compl_compl, hi.compl
-/
theorem symm (h : ν ⟂ₘ μ) : μ ⟂ₘ ν :=
  let ⟨i, hi, his, hit⟩ := h
  ⟨iᶜ, hi.compl, hit, (compl_compl i).symm ▸ his⟩

/--
theorem `comm` / 定理 `comm`

English:
theorem comm
  statement: μ ⟂ₘ ν ↔ ν ⟂ₘ μ
  proof: ⟨fun h => h.symm, fun h => h.symm⟩

@[simp]

中文:
定理 comm
  结论: μ ⟂ₘ ν ↔ ν ⟂ₘ μ
  证明: ⟨fun h => h.symm, fun h => h.symm⟩

@[simp]

Depends on / 依赖: h.symm
-/
theorem comm : μ ⟂ₘ ν ↔ ν ⟂ₘ μ :=
  ⟨fun h => h.symm, fun h => h.symm⟩

@[simp]
/--
theorem `zero_left` / 定理 `zero_left`

English:
theorem zero_left
  statement: 0 ⟂ₘ μ
  proof: zero_right.symm

中文:
定理 zero_left
  结论: 0 ⟂ₘ μ
  证明: zero_right.symm

Depends on / 依赖: zero_right, zero_right.symm
-/
theorem zero_left : 0 ⟂ₘ μ :=
  zero_right.symm

/--
theorem `mono_ac` / 定理 `mono_ac`

English:
theorem mono_ac
  given: (h : μ₁ ⟂ₘ ν₁) (hμ : μ₂ ≪ μ₁) (hν : ν₂ ≪ ν₁)
  statement: μ₂ ⟂ₘ ν₂
  proof: let ⟨s, hs, h₁, h₂⟩ := h
  ⟨s, hs, hμ h₁, hν h₂⟩

中文:
定理 mono_ac
  条件: (h : μ₁ ⟂ₘ ν₁) (hμ : μ₂ ≪ μ₁) (hν : ν₂ ≪ ν₁)
  结论: μ₂ ⟂ₘ ν₂
  证明: let ⟨s, hs, h₁, h₂⟩ := h
  ⟨s, hs, hμ h₁, hν h₂⟩
-/
theorem mono_ac (h : μ₁ ⟂ₘ ν₁) (hμ : μ₂ ≪ μ₁) (hν : ν₂ ≪ ν₁) : μ₂ ⟂ₘ ν₂ :=
  let ⟨s, hs, h₁, h₂⟩ := h
  ⟨s, hs, hμ h₁, hν h₂⟩

/--
lemma `congr_ac` / 引理 `congr_ac`

English:
lemma congr_ac
  given: (hμμ₂ : μ ≪ μ₂) (hμ₂μ : μ₂ ≪ μ) (hνν₂ : ν ≪ ν₂) (hν₂ν : ν₂ ≪ ν)
  proof: ⟨fun h => h.mono_ac hμ₂μ hν₂ν, fun h => h.mono_ac hμμ₂ hνν₂⟩

中文:
引理 congr_ac
  条件: (hμμ₂ : μ ≪ μ₂) (hμ₂μ : μ₂ ≪ μ) (hνν₂ : ν ≪ ν₂) (hν₂ν : ν₂ ≪ ν)
  证明: ⟨fun h => h.mono_ac hμ₂μ hν₂ν, fun h => h.mono_ac hμμ₂ hνν₂⟩

Depends on / 依赖: h.mono_ac, mono_ac
-/
lemma congr_ac (hμμ₂ : μ ≪ μ₂) (hμ₂μ : μ₂ ≪ μ) (hνν₂ : ν ≪ ν₂) (hν₂ν : ν₂ ≪ ν) :
    μ ⟂ₘ ν ↔ μ₂ ⟂ₘ ν₂ :=
  ⟨fun h => h.mono_ac hμ₂μ hν₂ν, fun h => h.mono_ac hμμ₂ hνν₂⟩

/--
theorem `mono` / 定理 `mono`

English:
theorem mono
  given: (h : μ₁ ⟂ₘ ν₁) (hμ : μ₂ <= μ₁) (hν : ν₂ <= ν₁)
  statement: μ₂ ⟂ₘ ν₂
  proof: h.mono_ac hμ.absolutelyContinuous hν.absolutelyContinuous

@[simp]

中文:
定理 mono
  条件: (h : μ₁ ⟂ₘ ν₁) (hμ : μ₂ <= μ₁) (hν : ν₂ <= ν₁)
  结论: μ₂ ⟂ₘ ν₂
  证明: h.mono_ac hμ.absolutelyContinuous hν.absolutelyContinuous

@[simp]

Depends on / 依赖: absolutelyContinuous, h.mono_ac, mono_ac
-/
theorem mono (h : μ₁ ⟂ₘ ν₁) (hμ : μ₂ <= μ₁) (hν : ν₂ <= ν₁) : μ₂ ⟂ₘ ν₂ :=
  h.mono_ac hμ.absolutelyContinuous hν.absolutelyContinuous

@[simp]
/--
lemma `self_iff` / 引理 `self_iff`

English:
lemma self_iff
  given: (μ : Measure α)
  statement: μ ⟂ₘ μ ↔ μ = 0
  proof: by
  refine ⟨?_, fun h => by (rw [h]; exact zero_left)⟩
  rintro ⟨s, hs, hμs, hμs_compl⟩
  suffices μ Set.univ = 0 by rwa [measure_univ_eq_zero] at this
  rw [← Set.union_compl_self s]; rw [measure_union disjoint_compl_right hs.compl]; rw [hμs]; rw [hμs_compl]; rw [add_zero]

@[simp]

中文:
引理 self_iff
  条件: (μ : Measure α)
  结论: μ ⟂ₘ μ ↔ μ = 0
  证明: by
  refine ⟨?_, fun h => by (rw [h]; exact zero_left)⟩
  rintro ⟨s, hs, hμs, hμs_compl⟩
  suffices μ Set.univ = 0 by rwa [measure_univ_eq_zero] at this
  rw [← Set.union_compl_self s]; rw [measure_union disjoint_compl_right hs.compl]; rw [hμs]; rw [hμs_compl]; rw [add_zero]

@[simp]

Depends on / 依赖: Set.union_compl_self, Set.univ, add_zero, disjoint_compl_right, hs.compl, measure_union, measure_univ_eq_zero, union_compl_self, zero_left
-/
lemma self_iff (μ : Measure α) : μ ⟂ₘ μ ↔ μ = 0 := by
  refine ⟨?_, fun h => by (rw [h]; exact zero_left)⟩
  rintro ⟨s, hs, hμs, hμs_compl⟩
  suffices μ Set.univ = 0 by rwa [measure_univ_eq_zero] at this
  rw [← Set.union_compl_self s]; rw [measure_union disjoint_compl_right hs.compl]; rw [hμs]; rw [hμs_compl]; rw [add_zero]

@[simp]
/--
theorem `sum_left` / 定理 `sum_left`

English:
theorem sum_left
  given: {ι : Type*} [Countable ι] {μ : ι -> Measure α}
  statement: sum μ ⟂ₘ ν ↔ forall i, μ i ⟂ₘ ν
  proof: by
  refine ⟨fun h i => h.mono (le_sum _ _) le_rfl, fun H => ?_⟩
  choose s hsm hsμ hsν using H
  refine ⟨⋂ i, s i, MeasurableSet.iInter hsm, ?_, ?_⟩
  · rw [sum_apply _ (MeasurableSet.iInter hsm), ENNReal.tsum_eq_zero]
    exact fun i => measure_mono_null (iInter_subset _ _) (hsμ i)
  · rwa [compl_

中文:
定理 sum_left
  条件: {ι : 类型} [Countable ι] {μ : ι -> Measure α}
  结论: sum μ ⟂ₘ ν ↔ 对任意 i, μ i ⟂ₘ ν
  证明: by
  refine ⟨fun h i => h.mono (le_sum _ _) le_rfl, fun H => ?_⟩
  choose s hsm hsμ hsν using H
  refine ⟨⋂ i, s i, MeasurableSet.iInter hsm, ?_, ?_⟩
  · rw [sum_apply _ (MeasurableSet.iInter hsm), ENNReal.tsum_eq_zero]
    exact fun i => measure_mono_null (iInter_subset _ _) (hsμ i)
  · rwa [compl_

Depends on / 依赖: ENNReal, ENNReal.tsum_eq_zero, MeasurableSet, MeasurableSet.iInter, compl_iInter, h.mono, iInter, iInter_subset, le_rfl, le_sum, measure_iUnion_null_iff, measure_mono_null, sum_apply, tsum_eq_zero
-/
theorem sum_left {ι : Type*} [Countable ι] {μ : ι -> Measure α} : sum μ ⟂ₘ ν ↔ forall i, μ i ⟂ₘ ν := by
  refine ⟨fun h i => h.mono (le_sum _ _) le_rfl, fun H => ?_⟩
  choose s hsm hsμ hsν using H
  refine ⟨⋂ i, s i, MeasurableSet.iInter hsm, ?_, ?_⟩
  · rw [sum_apply _ (MeasurableSet.iInter hsm), ENNReal.tsum_eq_zero]
    exact fun i => measure_mono_null (iInter_subset _ _) (hsμ i)
  · rwa [compl_iInter, measure_iUnion_null_iff]

@[simp]
/--
theorem `sum_right` / 定理 `sum_right`

English:
theorem sum_right
  given: {ι : Type*} [Countable ι] {ν : ι -> Measure α}
  statement: μ ⟂ₘ sum ν ↔ forall i, μ ⟂ₘ ν i
  proof: comm.trans sum_left.trans forall_congr' fun _ => comm

@[simp]

中文:
定理 sum_right
  条件: {ι : 类型} [Countable ι] {ν : ι -> Measure α}
  结论: μ ⟂ₘ sum ν ↔ 对任意 i, μ ⟂ₘ ν i
  证明: comm.trans sum_left.trans forall_congr' fun _ => comm

@[simp]

Depends on / 依赖: comm.trans, forall_congr, sum_left, sum_left.trans
-/
theorem sum_right {ι : Type*} [Countable ι] {ν : ι -> Measure α} : μ ⟂ₘ sum ν ↔ forall i, μ ⟂ₘ ν i :=
comm.trans sum_left.trans forall_congr' fun _ => comm

@[simp]
/--
theorem `add_left_iff` / 定理 `add_left_iff`

English:
theorem add_left_iff
  statement: μ₁ + μ₂ ⟂ₘ ν ↔ μ₁ ⟂ₘ ν ∧ μ₂ ⟂ₘ ν
  proof: by
  rw [← sum_cond]; rw [sum_left]; rw [Bool.forall_bool]; rw [cond]; rw [cond]; rw [and_comm]

@[simp]

中文:
定理 add_left_iff
  结论: μ₁ + μ₂ ⟂ₘ ν ↔ μ₁ ⟂ₘ ν ∧ μ₂ ⟂ₘ ν
  证明: by
  rw [← sum_cond]; rw [sum_left]; rw [Bool.forall_bool]; rw [cond]; rw [cond]; rw [and_comm]

@[simp]

Depends on / 依赖: Bool.forall_bool, and_comm, forall_bool, sum_cond, sum_left
-/
theorem add_left_iff : μ₁ + μ₂ ⟂ₘ ν ↔ μ₁ ⟂ₘ ν ∧ μ₂ ⟂ₘ ν := by
  rw [← sum_cond]; rw [sum_left]; rw [Bool.forall_bool]; rw [cond]; rw [cond]; rw [and_comm]

@[simp]
/--
theorem `add_right_iff` / 定理 `add_right_iff`

English:
theorem add_right_iff
  statement: μ ⟂ₘ ν₁ + ν₂ ↔ μ ⟂ₘ ν₁ ∧ μ ⟂ₘ ν₂
  proof: comm.trans add_left_iff.trans and_congr comm comm

中文:
定理 add_right_iff
  结论: μ ⟂ₘ ν₁ + ν₂ ↔ μ ⟂ₘ ν₁ ∧ μ ⟂ₘ ν₂
  证明: comm.trans add_left_iff.trans and_congr comm comm

Depends on / 依赖: add_left_iff, add_left_iff.trans, and_congr, comm.trans
-/
theorem add_right_iff : μ ⟂ₘ ν₁ + ν₂ ↔ μ ⟂ₘ ν₁ ∧ μ ⟂ₘ ν₂ :=
comm.trans add_left_iff.trans and_congr comm comm

/--
theorem `add_left` / 定理 `add_left`

English:
theorem add_left
  given: (h₁ : ν₁ ⟂ₘ μ) (h₂ : ν₂ ⟂ₘ μ)
  statement: ν₁ + ν₂ ⟂ₘ μ
  proof: add_left_iff.2 ⟨h₁, h₂⟩

中文:
定理 add_left
  条件: (h₁ : ν₁ ⟂ₘ μ) (h₂ : ν₂ ⟂ₘ μ)
  结论: ν₁ + ν₂ ⟂ₘ μ
  证明: add_left_iff.2 ⟨h₁, h₂⟩

Depends on / 依赖: add_left_iff
-/
theorem add_left (h₁ : ν₁ ⟂ₘ μ) (h₂ : ν₂ ⟂ₘ μ) : ν₁ + ν₂ ⟂ₘ μ :=
  add_left_iff.2 ⟨h₁, h₂⟩

/--
theorem `add_right` / 定理 `add_right`

English:
theorem add_right
  given: (h₁ : μ ⟂ₘ ν₁) (h₂ : μ ⟂ₘ ν₂)
  statement: μ ⟂ₘ ν₁ + ν₂
  proof: add_right_iff.2 ⟨h₁, h₂⟩

中文:
定理 add_right
  条件: (h₁ : μ ⟂ₘ ν₁) (h₂ : μ ⟂ₘ ν₂)
  结论: μ ⟂ₘ ν₁ + ν₂
  证明: add_right_iff.2 ⟨h₁, h₂⟩

Depends on / 依赖: add_right_iff
-/
theorem add_right (h₁ : μ ⟂ₘ ν₁) (h₂ : μ ⟂ₘ ν₂) : μ ⟂ₘ ν₁ + ν₂ :=
  add_right_iff.2 ⟨h₁, h₂⟩

/--
theorem `smul` / 定理 `smul`

English:
theorem smul
  given: (r : Real>=0∞) (h : ν ⟂ₘ μ)
  statement: r • ν ⟂ₘ μ
  proof: h.mono_ac (AbsolutelyContinuous.rfl.smul_left r) AbsolutelyContinuous.rfl

中文:
定理 smul
  条件: (r : 实数>=0∞) (h : ν ⟂ₘ μ)
  结论: r • ν ⟂ₘ μ
  证明: h.mono_ac (AbsolutelyContinuous.rfl.smul_left r) AbsolutelyContinuous.rfl

Depends on / 依赖: AbsolutelyContinuous, AbsolutelyContinuous.rfl, AbsolutelyContinuous.rfl.smul_left, h.mono_ac, mono_ac, smul_left
-/
theorem smul (r : Real>=0∞) (h : ν ⟂ₘ μ) : r • ν ⟂ₘ μ :=
  h.mono_ac (AbsolutelyContinuous.rfl.smul_left r) AbsolutelyContinuous.rfl

/--
theorem `smul_nnreal` / 定理 `smul_nnreal`

English:
theorem smul_nnreal
  given: (r : Real>=0) (h : ν ⟂ₘ μ)
  statement: r • ν ⟂ₘ μ
  proof: h.smul r

中文:
定理 smul_nnreal
  条件: (r : 实数>=0) (h : ν ⟂ₘ μ)
  结论: r • ν ⟂ₘ μ
  证明: h.smul r

Depends on / 依赖: h.smul
-/
theorem smul_nnreal (r : Real>=0) (h : ν ⟂ₘ μ) : r • ν ⟂ₘ μ :=
  h.smul r

/--
lemma `restrict` / 引理 `restrict`

English:
lemma restrict
  given: (h : μ ⟂ₘ ν) (s : Set α)
  statement: μ.restrict s ⟂ₘ ν
  proof: by
  refine ⟨h.nullSet, h.measurableSet_nullSet, ?_, h.measure_compl_nullSet⟩
  rw [Measure.restrict_apply h.measurableSet_nullSet]
  exact measure_mono_null Set.inter_subset_left h.measure_nullSet

中文:
引理 restrict
  条件: (h : μ ⟂ₘ ν) (s : Set α)
  结论: μ.restrict s ⟂ₘ ν
  证明: by
  refine ⟨h.nullSet, h.measurableSet_nullSet, ?_, h.measure_compl_nullSet⟩
  rw [Measure.restrict_apply h.measurableSet_nullSet]
  exact measure_mono_null Set.inter_subset_left h.measure_nullSet

Depends on / 依赖: Measure, Measure.restrict_apply, Set.inter_subset_left, h.measurableSet_nullSet, h.measure_compl_nullSet, h.measure_nullSet, h.nullSet, inter_subset_left, measurableSet_nullSet, measure_compl_nullSet, measure_mono_null, measure_nullSet, nullSet, restrict_apply
-/
lemma restrict (h : μ ⟂ₘ ν) (s : Set α) : μ.restrict s ⟂ₘ ν := by
  refine ⟨h.nullSet, h.measurableSet_nullSet, ?_, h.measure_compl_nullSet⟩
  rw [Measure.restrict_apply h.measurableSet_nullSet]
  exact measure_mono_null Set.inter_subset_left h.measure_nullSet

end MutuallySingular

/--
lemma `eq_zero_of_absolutelyContinuous_of_mutuallySingular` / 引理 `eq_zero_of_absolutelyContinuous_of_mutuallySingular`

English:
lemma eq_zero_of_absolutelyContinuous_of_mutuallySingular
  statement: {μ ν : Measure α}
  proof: by
  rw [← Measure.MutuallySingular.self_iff]
  exact h_ms.mono_ac Measure.AbsolutelyContinuous.rfl h_ac

中文:
引理 eq_zero_of_absolutelyContinuous_of_mutuallySingular
  结论: {μ ν : Measure α}
  证明: by
  rw [← Measure.MutuallySingular.self_iff]
  exact h_ms.mono_ac Measure.AbsolutelyContinuous.rfl h_ac

Depends on / 依赖: AbsolutelyContinuous, Measure, Measure.AbsolutelyContinuous.rfl, Measure.MutuallySingular.self_iff, MutuallySingular, h_ac, h_ms, h_ms.mono_ac, mono_ac, self_iff
-/
lemma eq_zero_of_absolutelyContinuous_of_mutuallySingular {μ ν : Measure α}
    (h_ac : μ ≪ ν) (h_ms : μ ⟂ₘ ν) :
    μ = 0 := by
  rw [← Measure.MutuallySingular.self_iff]
  exact h_ms.mono_ac Measure.AbsolutelyContinuous.rfl h_ac

/--
lemma `absolutelyContinuous_of_add_of_mutuallySingular` / 引理 `absolutelyContinuous_of_add_of_mutuallySingular`

English:
lemma absolutelyContinuous_of_add_of_mutuallySingular
  statement: {ν₁ ν₂ : Measure α}
  proof: by
  refine AbsolutelyContinuous.mk fun s hs hs_zero => ?_
  let t := h_ms.nullSet
  have ht : MeasurableSet t := h_ms.measurableSet_nullSet
  have htμ : μ t = 0 := h_ms.measure_nullSet
  have htν₂ : ν₂ tᶜ = 0 := h_ms.measure_compl_nullSet
  have : μ s = μ (s inter tᶜ) := by
    conv_lhs => rw [← in

中文:
引理 absolutelyContinuous_of_add_of_mutuallySingular
  结论: {ν₁ ν₂ : Measure α}
  证明: by
  refine AbsolutelyContinuous.mk fun s hs hs_zero => ?_
  let t := h_ms.nullSet
  have ht : MeasurableSet t := h_ms.measurableSet_nullSet
  have htμ : μ t = 0 := h_ms.measure_nullSet
  have htν₂ : ν₂ tᶜ = 0 := h_ms.measure_compl_nullSet
  have : μ s = μ (s inter tᶜ) := by
    conv_lhs => rw [← in

Depends on / 依赖: AbsolutelyContinuous, AbsolutelyContinuous.mk, MeasurableSet, conv_lhs, disjoint_compl_right, disjoint_compl_right.inter_right, h_ms, h_ms.measurableSet_nullSet, h_ms.measure_compl_nullSet, h_ms.measure_nullSet, h_ms.nullSet, hs.inter, hs_zero, ht.compl, inter_left, inter_right, inter_union_compl, measurableSet_nullSet, measure_compl_nullSet, measure_inter_null_of_null_right
-/
lemma absolutelyContinuous_of_add_of_mutuallySingular {ν₁ ν₂ : Measure α}
    (h : μ ≪ ν₁ + ν₂) (h_ms : μ ⟂ₘ ν₂) : μ ≪ ν₁ := by
  refine AbsolutelyContinuous.mk fun s hs hs_zero => ?_
  let t := h_ms.nullSet
  have ht : MeasurableSet t := h_ms.measurableSet_nullSet
  have htμ : μ t = 0 := h_ms.measure_nullSet
  have htν₂ : ν₂ tᶜ = 0 := h_ms.measure_compl_nullSet
  have : μ s = μ (s inter tᶜ) := by
    conv_lhs => rw [← inter_union_compl s t]
    rw [measure_union]; rw [measure_inter_null_of_null_right _ htμ]; rw [zero_add]
    · exact (disjoint_compl_right.inter_right' _).inter_left' _
    · exact hs.inter ht.compl
  rw [this]
  refine h ?_
  simp only [Measure.coe_add, Pi.add_apply, add_eq_zero]
  exact ⟨measure_inter_null_of_null_left _ hs_zero, measure_inter_null_of_null_right _ htν₂⟩

/--
lemma `_root_.MeasurableEmbedding.mutuallySingular_map` / 引理 `_root_.MeasurableEmbedding.mutuallySingular_map`

English:
lemma _root_.MeasurableEmbedding.mutuallySingular_map
  statement: {β : Type*} {_ : MeasurableSpace β}
  proof: by
  refine ⟨f '' hμν.nullSet, hf.measurableSet_image' hμν.measurableSet_nullSet, ?_, ?_⟩
  · rw [hf.map_apply, hf.injective.preimage_image, hμν.measure_nullSet]
  · rw [hf.map_apply, Set.preimage_compl, hf.injective.preimage_image, hμν.measure_compl_nullSet]

中文:
引理 _root_.MeasurableEmbedding.mutuallySingular_map
  结论: {β : 类型} {_ : MeasurableSpace β}
  证明: by
  refine ⟨f '' hμν.nullSet, hf.measurableSet_image' hμν.measurableSet_nullSet, ?_, ?_⟩
  · rw [hf.map_apply, hf.injective.preimage_image, hμν.measure_nullSet]
  · rw [hf.map_apply, Set.preimage_compl, hf.injective.preimage_image, hμν.measure_compl_nullSet]

Depends on / 依赖: Set.preimage_compl, hf.injective.preimage_image, hf.map_apply, hf.measurableSet_image, injective, map_apply, measurableSet_image, measurableSet_nullSet, measure_compl_nullSet, measure_nullSet, nullSet, preimage_compl, preimage_image
-/
lemma _root_.MeasurableEmbedding.mutuallySingular_map {β : Type*} {_ : MeasurableSpace β}
    {f : α -> β} (hf : MeasurableEmbedding f) (hμν : μ ⟂ₘ ν) :
    μ.map f ⟂ₘ ν.map f := by
  refine ⟨f '' hμν.nullSet, hf.measurableSet_image' hμν.measurableSet_nullSet, ?_, ?_⟩
  · rw [hf.map_apply, hf.injective.preimage_image, hμν.measure_nullSet]
  · rw [hf.map_apply, Set.preimage_compl, hf.injective.preimage_image, hμν.measure_compl_nullSet]

/--
lemma `exists_null_set_measure_lt_of_disjoint` / 引理 `exists_null_set_measure_lt_of_disjoint`

English:
lemma exists_null_set_measure_lt_of_disjoint
  given: (h : Disjoint μ ν) {ε : Real>=0} (hε : 0 < ε)
  proof: by
  have h₁ : (μ ⊓ ν) univ = 0 := le_bot_iff.1 (h (inf_le_left (b := ν)) inf_le_right) ▸ rfl
  simp_rw [Measure.inf_apply MeasurableSet.univ, inter_univ] at h₁
  have h₂ : forall n : Nat, exists t, μ t + ν tᶜ < ε * (1 / 2) ^ n := by
    intro n
    obtain ⟨m, ⟨t, ht₁, rfl⟩, hm₂⟩ :
        exists x 

中文:
引理 exists_null_set_measure_lt_of_disjoint
  条件: (h : Disjoint μ ν) {ε : 实数>=0} (hε : 0 < ε)
  证明: by
  have h₁ : (μ ⊓ ν) univ = 0 := le_bot_iff.1 (h (inf_le_left (b := ν)) inf_le_right) ▸ rfl
  simp_rw [Measure.inf_apply MeasurableSet.univ, inter_univ] at h₁
  have h₂ : forall n : Nat, exists t, μ t + ν tᶜ < ε * (1 / 2) ^ n := by
    intro n
    obtain ⟨m, ⟨t, ht₁, rfl⟩, hm₂⟩ :
        exists x 

Depends on / 依赖: ENNReal, ENNReal.mul_pos, MeasurableSet, MeasurableSet.univ, Measure, Measure.inf_apply, exists_lt_of_csInf_lt, inf_apply, inf_le_left, inf_le_right, inter_univ, le_bot_iff, mul_pos, ne.symm, simp_rw
-/
lemma exists_null_set_measure_lt_of_disjoint (h : Disjoint μ ν) {ε : Real>=0} (hε : 0 < ε) :
    exists s, μ s = 0 ∧ ν sᶜ <= 2 * ε := by
  have h₁ : (μ ⊓ ν) univ = 0 := le_bot_iff.1 (h (inf_le_left (b := ν)) inf_le_right) ▸ rfl
  simp_rw [Measure.inf_apply MeasurableSet.univ, inter_univ] at h₁
  have h₂ : forall n : Nat, exists t, μ t + ν tᶜ < ε * (1 / 2) ^ n := by
    intro n
    obtain ⟨m, ⟨t, ht₁, rfl⟩, hm₂⟩ :
        exists x in {m | exists t, m = μ t + ν tᶜ}, x < ε * (1 / 2 : Real>=0∞) ^ n := by
refine exists_lt_of_csInf_lt ⟨ν univ, ∅, by simp⟩ h₁ ▸ ENNReal.mul_pos ?_ (by simp)
      norm_cast
      exact hε.ne.symm
    exact ⟨t, hm₂⟩
  choose t ht₂ using h₂
  refine ⟨⋂ n, t n, ?_, ?_⟩
  · refine eq_zero_of_le_mul_pow (by simp)
      fun n => ((measure_mono <| iInter_subset_of_subset n fun _ ht => ht).trans
      (le_add_right le_rfl)).trans (ht₂ n).le
  · rw [compl_iInter, (by simp [ENNReal.tsum_mul_left, mul_comm] :
      2 * (ε : Real>=0∞) = ∑' (n : Nat), ε * (1 / 2 : Real>=0∞) ^ n)]
    refine (measure_iUnion_le _).trans ?_
    exact ENNReal.summable.tsum_le_tsum (fun n => (le_add_left le_rfl).trans (ht₂ n).le)
      ENNReal.summable

/--
lemma `mutuallySingular_of_disjoint` / 引理 `mutuallySingular_of_disjoint`

English:
lemma mutuallySingular_of_disjoint
  given: (h : Disjoint μ ν)
  statement: μ ⟂ₘ ν
  proof: by
  have h' (n : Nat) : exists s, μ s = 0 ∧ ν sᶜ <= (1 / 2) ^ n := by
    convert!
exists_null_set_measure_lt_of_disjoint h (ε := (1 / 2) ^ (n + 1)) pow_pos (by simp) (n + 1)
    conv =>
      -- this tweak is needed due to the known issue of `norm_cast` with numeric fractions
      enter [1, 1]
  

中文:
引理 mutuallySingular_of_disjoint
  条件: (h : Disjoint μ ν)
  结论: μ ⟂ₘ ν
  证明: by
  have h' (n : Nat) : exists s, μ s = 0 ∧ ν sᶜ <= (1 / 2) ^ n := by
    convert!
exists_null_set_measure_lt_of_disjoint h (ε := (1 / 2) ^ (n + 1)) pow_pos (by simp) (n + 1)
    conv =>
      -- this tweak is needed due to the known issue of `norm_cast` with numeric fractions
      enter [1, 1]
  

Depends on / 依赖: another, c.eq_empty_or_nonempty, construction, convert, disjunct, edge_case_construction, eq_empty_or_nonempty, exists_null_set_measure_lt_of_disjoint, hcnemp, operator, pow_pos, proof_post_zorn, proof_that, proof_that_construction_respects_whatever, proof_that_edge_case_construction_contains_all_stuff_in_c, proof_that_edge_case_construction_respects_whatever, variant, whatever, zorn_subset
-/
lemma mutuallySingular_of_disjoint (h : Disjoint μ ν) : μ ⟂ₘ ν := by
  have h' (n : Nat) : exists s, μ s = 0 ∧ ν sᶜ <= (1 / 2) ^ n := by
    convert!
exists_null_set_measure_lt_of_disjoint h (ε := (1 / 2) ^ (n + 1)) pow_pos (by simp) (n + 1)
    conv =>
      -- this tweak is needed due to the known issue of `norm_cast` with numeric fractions
      enter [1, 1]
      equals ((1 : Real>=0) / (2 : Real>=0)) => rfl
    norm_cast
    ring
  choose s hs₂ hs₃ using h'
  refine Measure.MutuallySingular.mk (t := (⋃ n, s n)ᶜ) (measure_iUnion_null hs₂) ?_ ?_
  · rw [compl_iUnion]
refine eq_zero_of_le_mul_pow (ε := 1) (by simp : (1 / 2 : Real>=0∞) < 1) fun n => ?_
    rw [ENNReal.coe_one]; rw [one_mul]
    exact (measure_mono <| iInter_subset_of_subset n fun _ ht => ht).trans (hs₃ n)
  · rw [union_compl_self]

/--
lemma `MutuallySingular.disjoint` / 引理 `MutuallySingular.disjoint`

English:
lemma MutuallySingular.disjoint
  given: (h : μ ⟂ₘ ν)
  statement: Disjoint μ ν
  proof: by
  have h_bot_iff (ξ : Measure α) : ξ <= ⊥ ↔ ξ = 0 := by
    rw [le_bot_iff]
    rfl
  intro ξ hξμ hξν
  rw [h_bot_iff]
  ext s hs
  simp only [Measure.coe_zero, Pi.zero_apply]
  rw [← inter_union_compl s h.nullSet]; rw [measure_union]; rw [add_eq_zero]
· exact ⟨measure_inter_null_of_null_right _ 

中文:
引理 MutuallySingular.disjoint
  条件: (h : μ ⟂ₘ ν)
  结论: Disjoint μ ν
  证明: by
  have h_bot_iff (ξ : Measure α) : ξ <= ⊥ ↔ ξ = 0 := by
    rw [le_bot_iff]
    rfl
  intro ξ hξμ hξν
  rw [h_bot_iff]
  ext s hs
  simp only [Measure.coe_zero, Pi.zero_apply]
  rw [← inter_union_compl s h.nullSet]; rw [measure_union]; rw [add_eq_zero]
· exact ⟨measure_inter_null_of_null_right _ 

Depends on / 依赖: Disjoint, Disjoint.mono, Measure, Measure.coe_zero, Pi.zero_apply, absolutelyContinuous_of_le, add_eq_zero, coe_zero, disjoint_compl_righ, h.measure_compl_nullSet, h.measure_nullSet, h.nullSet, h_bot_iff, inter_subset_right, inter_union_compl, le_bot_iff, measure_compl_nullSet, measure_inter_null_of_null_right, measure_nullSet, measure_union
-/
lemma MutuallySingular.disjoint (h : μ ⟂ₘ ν) : Disjoint μ ν := by
  have h_bot_iff (ξ : Measure α) : ξ <= ⊥ ↔ ξ = 0 := by
    rw [le_bot_iff]
    rfl
  intro ξ hξμ hξν
  rw [h_bot_iff]
  ext s hs
  simp only [Measure.coe_zero, Pi.zero_apply]
  rw [← inter_union_compl s h.nullSet]; rw [measure_union]; rw [add_eq_zero]
· exact ⟨measure_inter_null_of_null_right _ absolutelyContinuous_of_le hξμ h.measure_nullSet,
measure_inter_null_of_null_right _ absolutelyContinuous_of_le hξν h.measure_compl_nullSet⟩
  · exact Disjoint.mono inter_subset_right inter_subset_right disjoint_compl_right
  · exact hs.inter h.measurableSet_nullSet.compl

/--
lemma `MutuallySingular.disjoint_ae` / 引理 `MutuallySingular.disjoint_ae`

English:
lemma MutuallySingular.disjoint_ae
  given: (h : μ ⟂ₘ ν)
  statement: Disjoint (ae μ) (ae ν)
  proof: by
  rw [disjoint_iff_inf_le]
  intro s _
  refine ⟨s union h.nullSetᶜ, ?_, s union h.nullSet, ?_, ?_⟩
  · rw [mem_ae_iff, compl_union, compl_compl]
    exact measure_inter_null_of_null_right _ h.measure_nullSet
  · rw [mem_ae_iff, compl_union]
    exact measure_inter_null_of_null_right _ h.measure_

中文:
引理 MutuallySingular.disjoint_ae
  条件: (h : μ ⟂ₘ ν)
  结论: Disjoint (ae μ) (ae ν)
  证明: by
  rw [disjoint_iff_inf_le]
  intro s _
  refine ⟨s union h.nullSetᶜ, ?_, s union h.nullSet, ?_, ?_⟩
  · rw [mem_ae_iff, compl_union, compl_compl]
    exact measure_inter_null_of_null_right _ h.measure_nullSet
  · rw [mem_ae_iff, compl_union]
    exact measure_inter_null_of_null_right _ h.measure_

Depends on / 依赖: compl_compl, compl_union, disjoint_iff_inf_le, h.measure_compl_nullSet, h.measure_nullSet, h.nullSet, inter_union_compl, measure_compl_nullSet, measure_inter_null_of_null_right, measure_nullSet, mem_ae_iff, nullSet, union_eq_compl_compl_inter_compl
-/
lemma MutuallySingular.disjoint_ae (h : μ ⟂ₘ ν) : Disjoint (ae μ) (ae ν) := by
  rw [disjoint_iff_inf_le]
  intro s _
  refine ⟨s union h.nullSetᶜ, ?_, s union h.nullSet, ?_, ?_⟩
  · rw [mem_ae_iff, compl_union, compl_compl]
    exact measure_inter_null_of_null_right _ h.measure_nullSet
  · rw [mem_ae_iff, compl_union]
    exact measure_inter_null_of_null_right _ h.measure_compl_nullSet
  · rw [union_eq_compl_compl_inter_compl, union_eq_compl_compl_inter_compl,
      ← compl_union, compl_compl, inter_union_compl, compl_compl]

/--
lemma `disjoint_of_disjoint_ae` / 引理 `disjoint_of_disjoint_ae`

English:
lemma disjoint_of_disjoint_ae
  given: (h : Disjoint (ae μ) (ae ν))
  statement: Disjoint μ ν
  proof: by
  simp_rw [Filter.disjoint_iff, mem_ae_iff] at h
  obtain ⟨s, hs, t, ht, hst⟩ := h
  rw [disjoint_iff_inf_le]
  have : (⊥ : Measure α) = 0 := rfl
  refine Measure.le_intro fun u hu _ => ?_
  simp only [Measure.inf_apply hu, this, coe_zero, Pi.zero_apply, nonpos_iff_eq_zero]
  refine csInf_eq_bot_

中文:
引理 disjoint_of_disjoint_ae
  条件: (h : Disjoint (ae μ) (ae ν))
  结论: Disjoint μ ν
  证明: by
  simp_rw [Filter.disjoint_iff, mem_ae_iff] at h
  obtain ⟨s, hs, t, ht, hst⟩ := h
  rw [disjoint_iff_inf_le]
  have : (⊥ : Measure α) = 0 := rfl
  refine Measure.le_intro fun u hu _ => ?_
  simp only [Measure.inf_apply hu, this, coe_zero, Pi.zero_apply, nonpos_iff_eq_zero]
  refine csInf_eq_bot_

Depends on / 依赖: Filter, Filter.disjoint_iff, Measure, Measure.inf_apply, Measure.le_intro, Pi.zero_apply, coe_zero, csInf_eq_bot_of_bot_mem, disjoint_iff, disjoint_iff_inf_le, hst.subset_compl_left, inf_apply, inter_subset_left, inter_subset_left.trans, le_intro, measure_mono_null, mem_ae_iff, nonpos_iff_eq_zero, simp_rw, subset_compl_left
-/
lemma disjoint_of_disjoint_ae (h : Disjoint (ae μ) (ae ν)) : Disjoint μ ν := by
  simp_rw [Filter.disjoint_iff, mem_ae_iff] at h
  obtain ⟨s, hs, t, ht, hst⟩ := h
  rw [disjoint_iff_inf_le]
  have : (⊥ : Measure α) = 0 := rfl
  refine Measure.le_intro fun u hu _ => ?_
  simp only [Measure.inf_apply hu, this, coe_zero, Pi.zero_apply, nonpos_iff_eq_zero]
  refine csInf_eq_bot_of_bot_mem ⟨t, ?_⟩
  simp [measure_mono_null (inter_subset_left.trans hst.subset_compl_left) hs,
    measure_mono_null inter_subset_left ht]

/--
lemma `mutuallySingular_tfae` / 引理 `mutuallySingular_tfae`

English:
lemma mutuallySingular_tfae
  statement: List.TFAE
  proof: by
  tfae_have 1 -> 2
  | h => h.disjoint
  tfae_have 2 -> 1
  | h => mutuallySingular_of_disjoint h
  tfae_have 1 -> 3
  | h => h.disjoint_ae
  tfae_have 3 -> 2
  | h => disjoint_of_disjoint_ae h
  tfae_finish

中文:
引理 mutuallySingular_tfae
  结论: List.TFAE
  证明: by
  tfae_have 1 -> 2
  | h => h.disjoint
  tfae_have 2 -> 1
  | h => mutuallySingular_of_disjoint h
  tfae_have 1 -> 3
  | h => h.disjoint_ae
  tfae_have 3 -> 2
  | h => disjoint_of_disjoint_ae h
  tfae_finish

Depends on / 依赖: disjoint, disjoint_ae, disjoint_of_disjoint_ae, h.disjoint, h.disjoint_ae, mutuallySingular_of_disjoint, tfae_finish, tfae_have
-/
lemma mutuallySingular_tfae : List.TFAE
    [ μ ⟂ₘ ν,
      Disjoint μ ν,
      Disjoint (ae μ) (ae ν) ] := by
  tfae_have 1 -> 2
  | h => h.disjoint
  tfae_have 2 -> 1
  | h => mutuallySingular_of_disjoint h
  tfae_have 1 -> 3
  | h => h.disjoint_ae
  tfae_have 3 -> 2
  | h => disjoint_of_disjoint_ae h
  tfae_finish

/--
lemma `mutuallySingular_iff_disjoint` / 引理 `mutuallySingular_iff_disjoint`

English:
lemma mutuallySingular_iff_disjoint
  statement: μ ⟂ₘ ν ↔ Disjoint μ ν
  proof: mutuallySingular_tfae.out 0 1

中文:
引理 mutuallySingular_iff_disjoint
  结论: μ ⟂ₘ ν ↔ Disjoint μ ν
  证明: mutuallySingular_tfae.out 0 1

Depends on / 依赖: mutuallySingular_tfae, mutuallySingular_tfae.out
-/
lemma mutuallySingular_iff_disjoint : μ ⟂ₘ ν ↔ Disjoint μ ν :=
  mutuallySingular_tfae.out 0 1

/--
lemma `mutuallySingular_iff_disjoint_ae` / 引理 `mutuallySingular_iff_disjoint_ae`

English:
lemma mutuallySingular_iff_disjoint_ae
  statement: μ ⟂ₘ ν ↔ Disjoint (ae μ) (ae ν)
  proof: mutuallySingular_tfae.out 0 2

中文:
引理 mutuallySingular_iff_disjoint_ae
  结论: μ ⟂ₘ ν ↔ Disjoint (ae μ) (ae ν)
  证明: mutuallySingular_tfae.out 0 2

Depends on / 依赖: mutuallySingular_tfae, mutuallySingular_tfae.out
-/
lemma mutuallySingular_iff_disjoint_ae : μ ⟂ₘ ν ↔ Disjoint (ae μ) (ae ν) :=
  mutuallySingular_tfae.out 0 2

end Measure

end MeasureTheory
