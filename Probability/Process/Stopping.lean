/-
Copyright (c) 2021 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying, Rémy Degenne
-/
module

public import Mathlib.Probability.Process.Adapted
public import Mathlib.MeasureTheory.Constructions.BorelSpace.WithTop
public import Mathlib.Data.ENat.Lattice

/-!
# Stopping times, stopped processes and stopped values

Definition and properties of stopping times.

## Main definitions

* `MeasureTheory.IsStoppingTime`: a stopping time with respect to some filtration `f` on a
  measurable space `Ω` is a function `τ : Ω → WithTop ι` such that for all `i : ι`,
  the preimage of `{j | j ≤ i}` along `τ` is `f i`-measurable
* `MeasureTheory.IsStoppingTime.measurableSpace`: the σ-algebra associated with a stopping time

## Main results

* `IsStronglyProgressive.stoppedProcess`: the stopped process of a progressively measurable process
  is progressively measurable.
* `memLp_stoppedProcess`: if a process belongs to `ℒp` at every time in `ℕ`, then its stopped
  process belongs to `ℒp` as well.

## Implementation notes

For a filtration on a type `ι`, we define stopping times as functions from the measurable space `Ω`
to `WithTop ι`, which allows stopping times that can take an infinite value, represented by
`⊤ : WithTop ι`.

This means that if we have a process `X : ι → Ω → β` and a stopping time `τ : Ω → WithTop ι`, then
to consider the value of `X` at the stopping time `τ ω`, we need to write `X (τ ω).untopA ω`,
in which `(τ ω).untopA` is the value of `τ ω` in `ι` if `τ ω ≠ ⊤` and some arbitrary value if
`τ ω = ⊤`.

While indexing would be more convenient if we defined stopping times as functions from `Ω` to `ι`,
this would prevent us from using stopping times as in standard mathematical literature, where a
typical example of stopping time is the first time an event occurs, which may never happen.
Consider for example the first time a coin lands heads when flipping it infinitely many times:
this is almost surely finite, but possibly infinite. We could also not use a function `Ω → ι` with
arbitrary value for the infinite case, because this would be incompatible with the stopping time
property.

## Tags

stopping time, stochastic process

-/

@[expose] public section

open Filter Order TopologicalSpace WithTop

open scoped MeasureTheory NNReal ENNReal Topology

namespace MeasureTheory

variable {Ω β ι : Type*} {m : MeasurableSpace Ω}

/-! ### Stopping times -/


/--
Definition of `IsStoppingTime` / `IsStoppingTime` 的定义

English:
definition IsStoppingTime
  signature: [Preorder ι] (f : Filtration ι m) (τ : Ω -> WithTop ι)
  body: forall i : ι, MeasurableSet[f i] {ω | τ ω <= i}

中文:
定义 IsStoppingTime
  签名: [Preorder ι] (f : Filtration ι m) (τ : Ω -> WithTop ι)
  定义体: forall i : ι, MeasurableSet[f i] {ω | τ ω <= i}

Depends on / 依赖: MeasurableSet
-/
def IsStoppingTime [Preorder ι] (f : Filtration ι m) (τ : Ω -> WithTop ι) :=
forall i : ι, MeasurableSet[f i] {ω | τ ω <= i}

/--
theorem `isStoppingTime_const` / 定理 `isStoppingTime_const`

English:
theorem isStoppingTime_const
  given: [Preorder ι] (f : Filtration ι m) (i : ι)
  proof: fun j => by simp only [MeasurableSet.const]

中文:
定理 isStoppingTime_const
  条件: [Preorder ι] (f : Filtration ι m) (i : ι)
  证明: fun j => by simp only [MeasurableSet.const]

Depends on / 依赖: MeasurableSet, MeasurableSet.const
-/
theorem isStoppingTime_const [Preorder ι] (f : Filtration ι m) (i : ι) :
    IsStoppingTime f fun _ => i := fun j => by simp only [MeasurableSet.const]

section MeasurableSet

section Preorder

variable [Preorder ι] {f : Filtration ι m} {τ : Ω -> WithTop ι}

/--
theorem `IsStoppingTime.measurableSet_le` / 定理 `IsStoppingTime.measurableSet_le`

English:
theorem IsStoppingTime.measurableSet_le
  given: (hτ : IsStoppingTime f τ) (i : ι)
  proof: hτ i

中文:
定理 IsStoppingTime.measurableSet_le
  条件: (hτ : IsStoppingTime f τ) (i : ι)
  证明: hτ i
-/
protected theorem IsStoppingTime.measurableSet_le (hτ : IsStoppingTime f τ) (i : ι) :
    MeasurableSet[f i] {ω | τ ω <= i} :=
  hτ i

/--
theorem `IsStoppingTime.measurableSet_lt_of_pred` / 定理 `IsStoppingTime.measurableSet_lt_of_pred`

English:
theorem IsStoppingTime.measurableSet_lt_of_pred
  given: [PredOrder ι] (hτ : IsStoppingTime f τ) (i : ι)
  proof: by
  by_cases hi_min : IsMin i
  · suffices {ω : Ω | τ ω < i} = ∅ by rw [this]; exact @MeasurableSet.empty _ (f i)
    ext1 ω
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    rw [isMin_iff_forall_not_lt] at hi_min
    cases τ ω with
    | top => simp
    | coe t => exact mod

中文:
定理 IsStoppingTime.measurableSet_lt_of_pred
  条件: [PredOrder ι] (hτ : IsStoppingTime f τ) (i : ι)
  证明: by
  by_cases hi_min : IsMin i
  · suffices {ω : Ω | τ ω < i} = ∅ by rw [this]; exact @MeasurableSet.empty _ (f i)
    ext1 ω
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    rw [isMin_iff_forall_not_lt] at hi_min
    cases τ ω with
    | top => simp
    | coe t => exact mod

Depends on / 依赖: MeasurableSet, MeasurableSet.empty, Set.Iic, Set.mem_empty_iff_false, Set.mem_ofPred_eq, coe_le_coe, coe_lt_coe, f.mono, hi_min, iff_false, isMin_iff_forall_not_lt, le_pred_iff_of_not_isMin, mem_empty_iff_false, mem_ofPred_eq, mod_cast
-/
theorem IsStoppingTime.measurableSet_lt_of_pred [PredOrder ι] (hτ : IsStoppingTime f τ) (i : ι) :
    MeasurableSet[f i] {ω | τ ω < i} := by
  by_cases hi_min : IsMin i
  · suffices {ω : Ω | τ ω < i} = ∅ by rw [this]; exact @MeasurableSet.empty _ (f i)
    ext1 ω
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    rw [isMin_iff_forall_not_lt] at hi_min
    cases τ ω with
    | top => simp
    | coe t => exact mod_cast hi_min t
  have : {ω : Ω | τ ω < i} = τ ⁻¹' Set.Iic (pred i : ι) := by
    ext ω
    push _ in _
    cases τ ω with
    | top => simp
    | coe t =>
      simp only [coe_lt_coe, coe_le_coe]
      rw [le_pred_iff_of_not_isMin hi_min]
  rw [this]
  exact f.mono (pred_le i) _ (hτ.measurableSet_le <| pred i)

end Preorder

section CountableStoppingTime

namespace IsStoppingTime

variable [PartialOrder ι] {τ : Ω -> WithTop ι} {f : Filtration ι m}

/--
theorem `measurableSet_eq_of_countable_range` / 定理 `measurableSet_eq_of_countable_range`

English:
theorem measurableSet_eq_of_countable_range
  statement: (hτ : IsStoppingTime f τ)
  proof: by
  have : {ω | τ ω = i} = {ω | τ ω <= i} \ ⋃ (j in Set.range τ) (_ : j < i), {ω | τ ω <= j} := by
    ext1 a
    simp only [Set.mem_ofPred_eq, Set.mem_range, Set.iUnion_exists, Set.iUnion_iUnion_eq',
      Set.mem_sdiff, Set.mem_iUnion, exists_prop, not_exists, not_and]
    constructor <;> intro h

中文:
定理 measurableSet_eq_of_countable_range
  结论: (hτ : IsStoppingTime f τ)
  证明: by
  have : {ω | τ ω = i} = {ω | τ ω <= i} \ ⋃ (j in Set.range τ) (_ : j < i), {ω | τ ω <= j} := by
    ext1 a
    simp only [Set.mem_ofPred_eq, Set.mem_range, Set.iUnion_exists, Set.iUnion_iUnion_eq',
      Set.mem_sdiff, Set.mem_iUnion, exists_prop, not_exists, not_and]
    constructor <;> intro h
-/
protected theorem measurableSet_eq_of_countable_range (hτ : IsStoppingTime f τ)
    (h_countable : (Set.range τ).Countable) (i : ι) : MeasurableSet[f i] {ω | τ ω = i} := by
  have : {ω | τ ω = i} = {ω | τ ω <= i} \ ⋃ (j in Set.range τ) (_ : j < i), {ω | τ ω <= j} := by
    ext1 a
    simp only [Set.mem_ofPred_eq, Set.mem_range, Set.iUnion_exists, Set.iUnion_iUnion_eq',
      Set.mem_sdiff, Set.mem_iUnion, exists_prop, not_exists, not_and]
    constructor <;> intro h
    · simp only [h, lt_iff_le_not_ge, le_refl, and_imp, imp_self, imp_true_iff, and_self_iff]
    · exact h.1.eq_or_lt.resolve_right fun h_lt => h.2 a h_lt le_rfl
  rw [this]
  refine (hτ.measurableSet_le i).diff ?_
  refine MeasurableSet.biUnion h_countable fun j _ => ?_
  classical
  rw [Set.iUnion_eq_if]
  split_ifs with hji
  · lift j to ι using (ne_top_of_lt hji)
    exact f.mono (mod_cast hji.le) _ (hτ.measurableSet_le j)
  · exact @MeasurableSet.empty _ (f i)

/--
theorem `measurableSet_eq_of_countable` / 定理 `measurableSet_eq_of_countable`

English:
theorem measurableSet_eq_of_countable
  given: [Countable ι] (hτ : IsStoppingTime f τ) (i : ι)
  proof: hτ.measurableSet_eq_of_countable_range (Set.to_countable _) i

中文:
定理 measurableSet_eq_of_countable
  条件: [Countable ι] (hτ : IsStoppingTime f τ) (i : ι)
  证明: hτ.measurableSet_eq_of_countable_range (Set.to_countable _) i
-/
protected theorem measurableSet_eq_of_countable [Countable ι] (hτ : IsStoppingTime f τ) (i : ι) :
    MeasurableSet[f i] {ω | τ ω = i} :=
  hτ.measurableSet_eq_of_countable_range (Set.to_countable _) i

/--
theorem `measurableSet_lt_of_countable_range` / 定理 `measurableSet_lt_of_countable_range`

English:
theorem measurableSet_lt_of_countable_range
  statement: (hτ : IsStoppingTime f τ)
  proof: by
  have : {ω | τ ω < i} = {ω | τ ω <= i} \ {ω | τ ω = i} := by ext1 ω; simp [lt_iff_le_and_ne]
  rw [this]
  exact (hτ.measurableSet_le i).diff (hτ.measurableSet_eq_of_countable_range h_countable i)

中文:
定理 measurableSet_lt_of_countable_range
  结论: (hτ : IsStoppingTime f τ)
  证明: by
  have : {ω | τ ω < i} = {ω | τ ω <= i} \ {ω | τ ω = i} := by ext1 ω; simp [lt_iff_le_and_ne]
  rw [this]
  exact (hτ.measurableSet_le i).diff (hτ.measurableSet_eq_of_countable_range h_countable i)
-/
protected theorem measurableSet_lt_of_countable_range (hτ : IsStoppingTime f τ)
    (h_countable : (Set.range τ).Countable) (i : ι) : MeasurableSet[f i] {ω | τ ω < i} := by
  have : {ω | τ ω < i} = {ω | τ ω <= i} \ {ω | τ ω = i} := by ext1 ω; simp [lt_iff_le_and_ne]
  rw [this]
  exact (hτ.measurableSet_le i).diff (hτ.measurableSet_eq_of_countable_range h_countable i)

/--
theorem `measurableSet_lt_of_countable` / 定理 `measurableSet_lt_of_countable`

English:
theorem measurableSet_lt_of_countable
  given: [Countable ι] (hτ : IsStoppingTime f τ) (i : ι)
  proof: hτ.measurableSet_lt_of_countable_range (Set.to_countable _) i

中文:
定理 measurableSet_lt_of_countable
  条件: [Countable ι] (hτ : IsStoppingTime f τ) (i : ι)
  证明: hτ.measurableSet_lt_of_countable_range (Set.to_countable _) i
-/
protected theorem measurableSet_lt_of_countable [Countable ι] (hτ : IsStoppingTime f τ) (i : ι) :
    MeasurableSet[f i] {ω | τ ω < i} :=
  hτ.measurableSet_lt_of_countable_range (Set.to_countable _) i

/--
theorem `measurableSet_ge_of_countable_range` / 定理 `measurableSet_ge_of_countable_range`

English:
theorem measurableSet_ge_of_countable_range
  statement: {ι} [LinearOrder ι] {τ : Ω -> WithTop ι}
  proof: by
  have : {ω | i <= τ ω} = {ω | τ ω < i}ᶜ := by
    ext1 ω; simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, not_lt]
  rw [this]
  exact (hτ.measurableSet_lt_of_countable_range h_countable i).compl

中文:
定理 measurableSet_ge_of_countable_range
  结论: {ι} [LinearOrder ι] {τ : Ω -> WithTop ι}
  证明: by
  have : {ω | i <= τ ω} = {ω | τ ω < i}ᶜ := by
    ext1 ω; simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, not_lt]
  rw [this]
  exact (hτ.measurableSet_lt_of_countable_range h_countable i).compl
-/
protected theorem measurableSet_ge_of_countable_range {ι} [LinearOrder ι] {τ : Ω -> WithTop ι}
    {f : Filtration ι m} (hτ : IsStoppingTime f τ) (h_countable : (Set.range τ).Countable) (i : ι) :
    MeasurableSet[f i] {ω | i <= τ ω} := by
  have : {ω | i <= τ ω} = {ω | τ ω < i}ᶜ := by
    ext1 ω; simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, not_lt]
  rw [this]
  exact (hτ.measurableSet_lt_of_countable_range h_countable i).compl

/--
theorem `measurableSet_ge_of_countable` / 定理 `measurableSet_ge_of_countable`

English:
theorem measurableSet_ge_of_countable
  statement: {ι} [LinearOrder ι] {τ : Ω -> WithTop ι}
  proof: hτ.measurableSet_ge_of_countable_range (Set.to_countable _) i

中文:
定理 measurableSet_ge_of_countable
  结论: {ι} [LinearOrder ι] {τ : Ω -> WithTop ι}
  证明: hτ.measurableSet_ge_of_countable_range (Set.to_countable _) i
-/
protected theorem measurableSet_ge_of_countable {ι} [LinearOrder ι] {τ : Ω -> WithTop ι}
    {f : Filtration ι m} [Countable ι] (hτ : IsStoppingTime f τ) (i : ι) :
    MeasurableSet[f i] {ω | i <= τ ω} :=
  hτ.measurableSet_ge_of_countable_range (Set.to_countable _) i

end IsStoppingTime

end CountableStoppingTime

section LinearOrder

variable [LinearOrder ι] {f : Filtration ι m} {τ : Ω -> WithTop ι}

/--
theorem `IsStoppingTime.measurableSet_gt` / 定理 `IsStoppingTime.measurableSet_gt`

English:
theorem IsStoppingTime.measurableSet_gt
  given: (hτ : IsStoppingTime f τ) (i : ι)
  proof: by
  have : {ω | i < τ ω} = {ω | τ ω <= i}ᶜ := by
    ext1 ω; simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, not_le]
  rw [this]
  exact (hτ.measurableSet_le i).compl

中文:
定理 IsStoppingTime.measurableSet_gt
  条件: (hτ : IsStoppingTime f τ) (i : ι)
  证明: by
  have : {ω | i < τ ω} = {ω | τ ω <= i}ᶜ := by
    ext1 ω; simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, not_le]
  rw [this]
  exact (hτ.measurableSet_le i).compl

Depends on / 依赖: Set.mem_compl_iff, Set.mem_ofPred_eq, measurableSet_le, mem_compl_iff, mem_ofPred_eq, not_le
-/
theorem IsStoppingTime.measurableSet_gt (hτ : IsStoppingTime f τ) (i : ι) :
    MeasurableSet[f i] {ω | i < τ ω} := by
  have : {ω | i < τ ω} = {ω | τ ω <= i}ᶜ := by
    ext1 ω; simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, not_le]
  rw [this]
  exact (hτ.measurableSet_le i).compl

section TopologicalSpace

variable [TopologicalSpace ι] [OrderTopology ι] [FirstCountableTopology ι]

/--
theorem `IsStoppingTime.measurableSet_lt_of_isLUB` / 定理 `IsStoppingTime.measurableSet_lt_of_isLUB`

English:
theorem IsStoppingTime.measurableSet_lt_of_isLUB
  statement: (hτ : IsStoppingTime f τ) (i : ι)
  proof: by
  by_cases hi_min : IsMin i
  · suffices {ω | τ ω < i} = ∅ by rw [this]; exact @MeasurableSet.empty _ (f i)
    ext1 ω
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    cases τ ω with
    | top => simp
    | coe t => norm_cast; exact isMin_iff_forall_not_lt.mp hi_min t
  o

中文:
定理 IsStoppingTime.measurableSet_lt_of_isLUB
  结论: (hτ : IsStoppingTime f τ) (i : ι)
  证明: by
  by_cases hi_min : IsMin i
  · suffices {ω | τ ω < i} = ∅ by rw [this]; exact @MeasurableSet.empty _ (f i)
    ext1 ω
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    cases τ ω with
    | top => simp
    | coe t => norm_cast; exact isMin_iff_forall_not_lt.mp hi_min t
  o

Depends on / 依赖: MeasurableSet, MeasurableSet.empty, Monotone, Set.mem_empty_iff_false, Set.mem_ofPred_eq, Tendsto, exists_seq_monotone_tendsto, h_Iio_eq_, h_bound, h_lub, h_lub.exists_seq_monotone_tendsto, h_tendsto, hi_min, iff_false, isMin_iff_forall_not_lt, isMin_iff_forall_not_lt.mp, mem_empty_iff_false, mem_ofPred_eq, not_isMin_iff, not_isMin_iff.mp
-/
theorem IsStoppingTime.measurableSet_lt_of_isLUB (hτ : IsStoppingTime f τ) (i : ι)
    (h_lub : IsLUB (Set.Iio i) i) : MeasurableSet[f i] {ω | τ ω < i} := by
  by_cases hi_min : IsMin i
  · suffices {ω | τ ω < i} = ∅ by rw [this]; exact @MeasurableSet.empty _ (f i)
    ext1 ω
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    cases τ ω with
    | top => simp
    | coe t => norm_cast; exact isMin_iff_forall_not_lt.mp hi_min t
  obtain ⟨seq, -, -, h_tendsto, h_bound⟩ :
      exists seq : Nat -> ι, Monotone seq ∧ (forall j, seq j <= i) ∧ Tendsto seq atTop (𝓝 i) ∧ forall j, seq j < i :=
    h_lub.exists_seq_monotone_tendsto (not_isMin_iff.mp hi_min)
  have h_Iio_eq_Union : Set.Iio (i : WithTop ι) = ⋃ j, {k : WithTop ι | k <= seq j} := by
    ext1 k
    push _ in _
    refine ⟨fun hk_lt_i => ?_, fun h_exists_k_le_seq => ?_⟩
    · rw [tendsto_atTop'] at h_tendsto
      cases k with
      | top => simp at hk_lt_i
      | coe k =>
        norm_cast at hk_lt_i ⊢
        have h_nhds : Set.Ici k in 𝓝 i :=
          mem_nhds_iff.mpr ⟨Set.Ioi k, Set.Ioi_subset_Ici le_rfl, isOpen_Ioi, hk_lt_i⟩
        obtain ⟨a, ha⟩ : exists a : Nat, forall b : Nat, b >= a -> k <= seq b := h_tendsto (Set.Ici k) h_nhds
        exact ⟨a, ha a le_rfl⟩
    · obtain ⟨j, hk_seq_j⟩ := h_exists_k_le_seq
      exact hk_seq_j.trans_lt (mod_cast h_bound j)
  have h_lt_eq_preimage : {ω | τ ω < i} = τ ⁻¹' Set.Iio i := by
    ext1 ω; push _ in _; rfl
  rw [h_lt_eq_preimage]; rw [h_Iio_eq_Union]
  simp only [Set.preimage_iUnion, Set.preimage_ofPred_eq]
  exact MeasurableSet.iUnion fun n => f.mono (h_bound n).le _ (hτ.measurableSet_le (seq n))

/--
theorem `IsStoppingTime.measurableSet_lt` / 定理 `IsStoppingTime.measurableSet_lt`

English:
theorem IsStoppingTime.measurableSet_lt
  given: (hτ : IsStoppingTime f τ) (i : ι)
  proof: by
  obtain ⟨i', hi'_lub⟩ : exists i', IsLUB (Set.Iio i) i' := exists_lub_Iio i
  rcases lub_Iio_eq_self_or_Iio_eq_Iic i hi'_lub with hi'_eq_i | h_Iio_eq_Iic
  · rw [← hi'_eq_i] at hi'_lub ⊢
    exact hτ.measurableSet_lt_of_isLUB i' hi'_lub
  · have h_lt_eq_preimage : {ω : Ω | τ ω < i} = τ ⁻¹' Set.I

中文:
定理 IsStoppingTime.measurableSet_lt
  条件: (hτ : IsStoppingTime f τ) (i : ι)
  证明: by
  obtain ⟨i', hi'_lub⟩ : exists i', IsLUB (Set.Iio i) i' := exists_lub_Iio i
  rcases lub_Iio_eq_self_or_Iio_eq_Iic i hi'_lub with hi'_eq_i | h_Iio_eq_Iic
  · rw [← hi'_eq_i] at hi'_lub ⊢
    exact hτ.measurableSet_lt_of_isLUB i' hi'_lub
  · have h_lt_eq_preimage : {ω : Ω | τ ω < i} = τ ⁻¹' Set.I

Depends on / 依赖: Set.Iic, Set.Iio, WithTop, _eq_i, _lub, exists_lub_Iio, f.mono, h_Iio_eq_Iic, h_lt_eq_preimage, image_coe_Iic, image_coe_Iio, le_o, lub_Iio_eq_self_or_Iio_eq_Iic, measurableSet_lt_of_isLUB
-/
theorem IsStoppingTime.measurableSet_lt (hτ : IsStoppingTime f τ) (i : ι) :
    MeasurableSet[f i] {ω | τ ω < i} := by
  obtain ⟨i', hi'_lub⟩ : exists i', IsLUB (Set.Iio i) i' := exists_lub_Iio i
  rcases lub_Iio_eq_self_or_Iio_eq_Iic i hi'_lub with hi'_eq_i | h_Iio_eq_Iic
  · rw [← hi'_eq_i] at hi'_lub ⊢
    exact hτ.measurableSet_lt_of_isLUB i' hi'_lub
  · have h_lt_eq_preimage : {ω : Ω | τ ω < i} = τ ⁻¹' Set.Iio i := rfl
    have h_Iio_eq_Iic' : Set.Iio (i : WithTop ι) = Set.Iic (i' : WithTop ι) := by
      rw [← image_coe_Iio]; rw [← image_coe_Iic]; rw [h_Iio_eq_Iic]
    rw [h_lt_eq_preimage]; rw [h_Iio_eq_Iic']
    exact f.mono (le_of_isLUB_Iio i hi'_lub) _ (hτ.measurableSet_le i')

/--
theorem `IsStoppingTime.measurableSet_ge` / 定理 `IsStoppingTime.measurableSet_ge`

English:
theorem IsStoppingTime.measurableSet_ge
  given: (hτ : IsStoppingTime f τ) (i : ι)
  proof: by
  have : {ω | i <= τ ω} = {ω | τ ω < i}ᶜ := by
    ext1 ω; simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, not_lt]
  rw [this]
  exact (hτ.measurableSet_lt i).compl

中文:
定理 IsStoppingTime.measurableSet_ge
  条件: (hτ : IsStoppingTime f τ) (i : ι)
  证明: by
  have : {ω | i <= τ ω} = {ω | τ ω < i}ᶜ := by
    ext1 ω; simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, not_lt]
  rw [this]
  exact (hτ.measurableSet_lt i).compl

Depends on / 依赖: Set.mem_compl_iff, Set.mem_ofPred_eq, measurableSet_lt, mem_compl_iff, mem_ofPred_eq, not_lt
-/
theorem IsStoppingTime.measurableSet_ge (hτ : IsStoppingTime f τ) (i : ι) :
    MeasurableSet[f i] {ω | i <= τ ω} := by
  have : {ω | i <= τ ω} = {ω | τ ω < i}ᶜ := by
    ext1 ω; simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, not_lt]
  rw [this]
  exact (hτ.measurableSet_lt i).compl

/--
theorem `IsStoppingTime.measurableSet_eq` / 定理 `IsStoppingTime.measurableSet_eq`

English:
theorem IsStoppingTime.measurableSet_eq
  given: (hτ : IsStoppingTime f τ) (i : ι)
  proof: by
  have : {ω | τ ω = i} = {ω | τ ω <= i} inter {ω | τ ω >= i} := by
    ext1 ω; simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, le_antisymm_iff]
  rw [this]
  exact (hτ.measurableSet_le i).inter (hτ.measurableSet_ge i)

中文:
定理 IsStoppingTime.measurableSet_eq
  条件: (hτ : IsStoppingTime f τ) (i : ι)
  证明: by
  have : {ω | τ ω = i} = {ω | τ ω <= i} inter {ω | τ ω >= i} := by
    ext1 ω; simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, le_antisymm_iff]
  rw [this]
  exact (hτ.measurableSet_le i).inter (hτ.measurableSet_ge i)

Depends on / 依赖: Set.mem_inter_iff, Set.mem_ofPred_eq, le_antisymm_iff, measurableSet_ge, measurableSet_le, mem_inter_iff, mem_ofPred_eq
-/
theorem IsStoppingTime.measurableSet_eq (hτ : IsStoppingTime f τ) (i : ι) :
    MeasurableSet[f i] {ω | τ ω = i} := by
  have : {ω | τ ω = i} = {ω | τ ω <= i} inter {ω | τ ω >= i} := by
    ext1 ω; simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, le_antisymm_iff]
  rw [this]
  exact (hτ.measurableSet_le i).inter (hτ.measurableSet_ge i)

/--
theorem `IsStoppingTime.measurableSet_eq_le` / 定理 `IsStoppingTime.measurableSet_eq_le`

English:
theorem IsStoppingTime.measurableSet_eq_le
  given: (hτ : IsStoppingTime f τ) {i j : ι} (hle : i <= j)
  proof: f.mono hle _ hτ.measurableSet_eq i

中文:
定理 IsStoppingTime.measurableSet_eq_le
  条件: (hτ : IsStoppingTime f τ) {i j : ι} (hle : i <= j)
  证明: f.mono hle _ hτ.measurableSet_eq i

Depends on / 依赖: f.mono, measurableSet_eq
-/
theorem IsStoppingTime.measurableSet_eq_le (hτ : IsStoppingTime f τ) {i j : ι} (hle : i <= j) :
    MeasurableSet[f j] {ω | τ ω = i} :=
f.mono hle _ hτ.measurableSet_eq i

/--
theorem `IsStoppingTime.measurableSet_lt_le` / 定理 `IsStoppingTime.measurableSet_lt_le`

English:
theorem IsStoppingTime.measurableSet_lt_le
  given: (hτ : IsStoppingTime f τ) {i j : ι} (hle : i <= j)
  proof: f.mono hle _ hτ.measurableSet_lt i

中文:
定理 IsStoppingTime.measurableSet_lt_le
  条件: (hτ : IsStoppingTime f τ) {i j : ι} (hle : i <= j)
  证明: f.mono hle _ hτ.measurableSet_lt i

Depends on / 依赖: f.mono, measurableSet_lt
-/
theorem IsStoppingTime.measurableSet_lt_le (hτ : IsStoppingTime f τ) {i j : ι} (hle : i <= j) :
    MeasurableSet[f j] {ω | τ ω < i} :=
f.mono hle _ hτ.measurableSet_lt i

end TopologicalSpace

end LinearOrder

section Countable

/--
theorem `isStoppingTime_of_measurableSet_eq` / 定理 `isStoppingTime_of_measurableSet_eq`

English:
theorem isStoppingTime_of_measurableSet_eq
  statement: [Preorder ι] [Countable ι] {f : Filtration ι m}
  proof: by
  intro i
  have h_eq_iUnion : {ω | τ ω <= i} = ⋃ k <= i, {ω | τ ω = k} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, exists_prop]
    cases τ ω with
    | top => simp
    | coe a => norm_cast; simp
  rw [h_eq_iUnion]
  refine MeasurableSet.biUnion (Set.to_countable _) fun k h

中文:
定理 isStoppingTime_of_measurableSet_eq
  结论: [Preorder ι] [Countable ι] {f : Filtration ι m}
  证明: by
  intro i
  have h_eq_iUnion : {ω | τ ω <= i} = ⋃ k <= i, {ω | τ ω = k} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, exists_prop]
    cases τ ω with
    | top => simp
    | coe a => norm_cast; simp
  rw [h_eq_iUnion]
  refine MeasurableSet.biUnion (Set.to_countable _) fun k h

Depends on / 依赖: MeasurableSet, MeasurableSet.biUnion, Set.mem_iUnion, Set.mem_ofPred_eq, Set.to_countable, biUnion, exists_prop, f.mono, h_eq_iUnion, mem_iUnion, mem_ofPred_eq, to_countable
-/
theorem isStoppingTime_of_measurableSet_eq [Preorder ι] [Countable ι] {f : Filtration ι m}
    {τ : Ω -> WithTop ι} (hτ : forall i, MeasurableSet[f i] {ω | τ ω = i}) : IsStoppingTime f τ := by
  intro i
  have h_eq_iUnion : {ω | τ ω <= i} = ⋃ k <= i, {ω | τ ω = k} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, exists_prop]
    cases τ ω with
    | top => simp
    | coe a => norm_cast; simp
  rw [h_eq_iUnion]
  refine MeasurableSet.biUnion (Set.to_countable _) fun k hk => ?_
  exact f.mono hk _ (hτ k)

end Countable

section IsRightContinuous

open Filtration

variable [ConditionallyCompleteLinearOrder ι] [TopologicalSpace ι] [OrderTopology ι]
    [FirstCountableTopology ι] {f : Filtration ι m} {τ : Ω -> WithTop ι}

set_option backward.isDefEq.respectTransparency false in
/--
lemma `isStoppingTime_of_measurableSet_lt_of_isRightContinuous'` / 引理 `isStoppingTime_of_measurableSet_lt_of_isRightContinuous'`

English:
lemma isStoppingTime_of_measurableSet_lt_of_isRightContinuous'
  statement: [hf : f.IsRightContinuous]
  proof: by
  intro t
  by_cases ht : 𝓝[>] t = ⊥
  · have h_eq : {ω | τ ω <= t} = {ω | τ ω < t} union {ω | τ ω = t} := by ext; grind
    rw [h_eq]
    exact (hτ1 t).union (hτ2 t ht)
  have : (𝓝[>] t).NeBot := ⟨ht⟩
  -- now `t` is a limit point on the right
  obtain ⟨s, hs_gt, hs_tendsto⟩ : exists s : Nat -> 

中文:
引理 isStoppingTime_of_measurableSet_lt_of_isRightContinuous'
  结论: [hf : f.IsRightContinuous]
  证明: by
  intro t
  by_cases ht : 𝓝[>] t = ⊥
  · have h_eq : {ω | τ ω <= t} = {ω | τ ω < t} union {ω | τ ω = t} := by ext; grind
    rw [h_eq]
    exact (hτ1 t).union (hτ2 t ht)
  have : (𝓝[>] t).NeBot := ⟨ht⟩
  -- now `t` is a limit point on the right
  obtain ⟨s, hs_gt, hs_tendsto⟩ : exists s : Nat -> 

Depends on / 依赖: h_eq
-/
lemma isStoppingTime_of_measurableSet_lt_of_isRightContinuous' [hf : f.IsRightContinuous]
    (hτ1 : forall i, MeasurableSet[f i] {ω | τ ω < i})
    (hτ2 : forall i, 𝓝[>] i = ⊥ -> MeasurableSet[f i] {ω | τ ω = i}) :
    IsStoppingTime f τ := by
  intro t
  by_cases ht : 𝓝[>] t = ⊥
  · have h_eq : {ω | τ ω <= t} = {ω | τ ω < t} union {ω | τ ω = t} := by ext; grind
    rw [h_eq]
    exact (hτ1 t).union (hτ2 t ht)
  have : (𝓝[>] t).NeBot := ⟨ht⟩
  -- now `t` is a limit point on the right
  obtain ⟨s, hs_gt, hs_tendsto⟩ : exists s : Nat -> ι, (forall n, t < s n) ∧ Tendsto s atTop (𝓝 t) := by
    have h_freq : existsᶠ x in 𝓝[>] t, t < x :=
Eventually.frequently eventually_nhdsWithin_of_forall fun _ hx => hx
    have := exists_seq_forall_of_frequently h_freq
    simp_rw [tendsto_nhdsWithin_iff] at this
    obtain ⟨s, ⟨hs_tendsto, _⟩, hs_gt⟩ := this
    exact ⟨s, hs_gt, hs_tendsto⟩
  have h_exists_lt (u : ι) (hu : t < u) : exists i, s i < u :=
    Eventually.exists (f := atTop) (hs_tendsto.eventually_lt_const hu)
  have h_exists_lt' (u : WithTop ι) (hu : t < u) : exists i, s i < u := by
    refine Eventually.exists (f := atTop) ?_
    have hs_tendsto' : Tendsto (fun n => (s n : WithTop ι)) atTop (𝓝 (t : WithTop ι)) :=
      WithTop.continuous_coe.continuousAt.tendsto.comp hs_tendsto
    exact hs_tendsto'.eventually_lt_const hu
  -- we write `{τ ≤ t}` as a countable intersection of `{τ < s n}`
  have h_eq_iInter : {ω | τ ω <= t} = ⋂ m, {ω | τ ω < s m} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iInter]
    refine ⟨fun h_le m => h_le.trans_lt (mod_cast (hs_gt m)), fun h_lt => ?_⟩
    refine le_of_forall_gt fun u hu => ?_
    obtain ⟨i, hi⟩ : exists i, s i < u := h_exists_lt' u hu
    exact (h_lt i).trans hi
  rw [h_eq_iInter]
  have h𝓕_eq_iInf : f t = ⨅ m, f (s m) := by
    nth_rw 1 [← hf.eq, Filtration.rightCont_eq_of_neBot_nhdsGT]
    refine le_antisymm ?_ ?_
    · simp only [gt_iff_lt, le_iInf_iff]
      exact fun i => iInf₂_le (s i) (hs_gt i)
    · simp only [gt_iff_lt, le_iInf_iff]
      intro i hti
      obtain ⟨m, hm⟩ := h_exists_lt i hti
      exact (iInf_le _ m).trans (f.mono hm.le)
  rw [h𝓕_eq_iInf]
  simp only [MeasurableSpace.measurableSet_sInf, Set.mem_range, forall_exists_index,
    forall_apply_eq_imp_iff]
  intro k
  have h_eq_k : ⋂ m, {ω | τ ω < s m} = ⋂ (m) (hm : s m <= s k), {ω | τ ω < s m} := by
    ext x
    simp only [Set.mem_iInter, Set.mem_ofPred_eq]
    refine ⟨fun h m _ => h m, fun h m => ?_⟩
    rcases le_total (s m) (s k) with hmk | hkm
    · exact h m hmk
    · exact (h k le_rfl).trans_le (mod_cast hkm)
  rw [h_eq_k]
  exact MeasurableSet.iInter fun m => MeasurableSet.iInter fun hm => f.mono hm _ (hτ1 (s m))

/--
lemma `isStoppingTime_of_measurableSet_lt_of_isRightContinuous` / 引理 `isStoppingTime_of_measurableSet_lt_of_isRightContinuous`

English:
lemma isStoppingTime_of_measurableSet_lt_of_isRightContinuous
  statement: [DenselyOrdered ι] [NoMaxOrder ι]
  proof: isStoppingTime_of_measurableSet_lt_of_isRightContinuous' hτ
 fun _ hi => absurd hi (NeBot.ne inferInstance)

中文:
引理 isStoppingTime_of_measurableSet_lt_of_isRightContinuous
  结论: [DenselyOrdered ι] [NoMaxOrder ι]
  证明: isStoppingTime_of_measurableSet_lt_of_isRightContinuous' hτ
 fun _ hi => absurd hi (NeBot.ne inferInstance)

Depends on / 依赖: NeBot.ne, absurd, isStoppingTime_of_measurableSet_lt_of_isRightContinuous
-/
lemma isStoppingTime_of_measurableSet_lt_of_isRightContinuous [DenselyOrdered ι] [NoMaxOrder ι]
    {τ : Ω -> WithTop ι} [f.IsRightContinuous] (hτ : forall i, MeasurableSet[f i] {ω | τ ω < i}) :
    IsStoppingTime f τ :=
  isStoppingTime_of_measurableSet_lt_of_isRightContinuous' hτ
 fun _ hi => absurd hi (NeBot.ne inferInstance)

end IsRightContinuous

end MeasurableSet

namespace IsStoppingTime

/--
theorem `max` / 定理 `max`

English:
theorem max
  statement: [LinearOrder ι] {f : Filtration ι m} {τ π : Ω -> WithTop ι}
  proof: by
  intro i
  simp_rw [max_le_iff, Set.ofPred_and]
  exact (hτ i).inter (hπ i)

中文:
定理 max
  结论: [LinearOrder ι] {f : Filtration ι m} {τ π : Ω -> WithTop ι}
  证明: by
  intro i
  simp_rw [max_le_iff, Set.ofPred_and]
  exact (hτ i).inter (hπ i)
-/
protected theorem max [LinearOrder ι] {f : Filtration ι m} {τ π : Ω -> WithTop ι}
    (hτ : IsStoppingTime f τ)
    (hπ : IsStoppingTime f π) : IsStoppingTime f fun ω => max (τ ω) (π ω) := by
  intro i
  simp_rw [max_le_iff, Set.ofPred_and]
  exact (hτ i).inter (hπ i)

/--
theorem `max_const` / 定理 `max_const`

English:
theorem max_const
  statement: [LinearOrder ι] {f : Filtration ι m} {τ : Ω -> WithTop ι}
  proof: hτ.max (isStoppingTime_const f i)

中文:
定理 max_const
  结论: [LinearOrder ι] {f : Filtration ι m} {τ : Ω -> WithTop ι}
  证明: hτ.max (isStoppingTime_const f i)
-/
protected theorem max_const [LinearOrder ι] {f : Filtration ι m} {τ : Ω -> WithTop ι}
    (hτ : IsStoppingTime f τ) (i : ι) : IsStoppingTime f fun ω => max (τ ω) i :=
  hτ.max (isStoppingTime_const f i)

/--
theorem `min` / 定理 `min`

English:
theorem min
  statement: [LinearOrder ι] {f : Filtration ι m} {τ π : Ω -> WithTop ι}
  proof: by
  intro i
  simp_rw [min_le_iff, Set.ofPred_or]
  exact (hτ i).union (hπ i)

中文:
定理 min
  结论: [LinearOrder ι] {f : Filtration ι m} {τ π : Ω -> WithTop ι}
  证明: by
  intro i
  simp_rw [min_le_iff, Set.ofPred_or]
  exact (hτ i).union (hπ i)
-/
protected theorem min [LinearOrder ι] {f : Filtration ι m} {τ π : Ω -> WithTop ι}
    (hτ : IsStoppingTime f τ) (hπ : IsStoppingTime f π) :
    IsStoppingTime f fun ω => min (τ ω) (π ω) := by
  intro i
  simp_rw [min_le_iff, Set.ofPred_or]
  exact (hτ i).union (hπ i)

/--
theorem `min_const` / 定理 `min_const`

English:
theorem min_const
  statement: [LinearOrder ι] {f : Filtration ι m} {τ : Ω -> WithTop ι}
  proof: hτ.min (isStoppingTime_const f i)

中文:
定理 min_const
  结论: [LinearOrder ι] {f : Filtration ι m} {τ : Ω -> WithTop ι}
  证明: hτ.min (isStoppingTime_const f i)
-/
protected theorem min_const [LinearOrder ι] {f : Filtration ι m} {τ : Ω -> WithTop ι}
    (hτ : IsStoppingTime f τ) (i : ι) : IsStoppingTime f fun ω => min (τ ω) i :=
  hτ.min (isStoppingTime_const f i)

/--
lemma `biInf` / 引理 `biInf`

English:
lemma biInf
  statement: [ConditionallyCompleteLinearOrderBot ι] [TopologicalSpace ι]
  proof: by
refine isStoppingTime_of_measurableSet_lt_of_isRightContinuous
    fun i => MeasurableSet.of_compl ?_
  rw [(_ : {ω | ⨅ n in s]; rw [τ n ω < i}ᶜ = ⋂ n in s]; rw [{ω | i <= τ n ω})]
· exact MeasurableSet.biInter hs fun n hn => (hτ n hn).measurableSet_ge i
  · ext ω
    simp

中文:
引理 biInf
  结论: [ConditionallyCompleteLinearOrderBot ι] [TopologicalSpace ι]
  证明: by
refine isStoppingTime_of_measurableSet_lt_of_isRightContinuous
    fun i => MeasurableSet.of_compl ?_
  rw [(_ : {ω | ⨅ n in s]; rw [τ n ω < i}ᶜ = ⋂ n in s]; rw [{ω | i <= τ n ω})]
· exact MeasurableSet.biInter hs fun n hn => (hτ n hn).measurableSet_ge i
  · ext ω
    simp
-/
protected lemma biInf [ConditionallyCompleteLinearOrderBot ι] [TopologicalSpace ι]
    [OrderTopology ι] [DenselyOrdered ι] [FirstCountableTopology ι] [NoMaxOrder ι]
    {κ : Type*} {f : Filtration ι m} {τ : κ -> Ω -> WithTop ι} {s : Set κ} (hs : s.Countable)
    [f.IsRightContinuous] (hτ : forall n in s, IsStoppingTime f (τ n)) :
    IsStoppingTime f (fun ω => ⨅ n in s, τ n ω) := by
refine isStoppingTime_of_measurableSet_lt_of_isRightContinuous
    fun i => MeasurableSet.of_compl ?_
  rw [(_ : {ω | ⨅ n in s]; rw [τ n ω < i}ᶜ = ⋂ n in s]; rw [{ω | i <= τ n ω})]
· exact MeasurableSet.biInter hs fun n hn => (hτ n hn).measurableSet_ge i
  · ext ω
    simp

/--
lemma `iInf` / 引理 `iInf`

English:
lemma iInf
  statement: [ConditionallyCompleteLinearOrderBot ι] [TopologicalSpace ι]
  proof: by
  convert! IsStoppingTime.biInf (κ := κ) Set.countable_univ (fun n _ => hτ n) using 2
  simp

中文:
引理 iInf
  结论: [ConditionallyCompleteLinearOrderBot ι] [TopologicalSpace ι]
  证明: by
  convert! IsStoppingTime.biInf (κ := κ) Set.countable_univ (fun n _ => hτ n) using 2
  simp
-/
protected lemma iInf [ConditionallyCompleteLinearOrderBot ι] [TopologicalSpace ι]
    [OrderTopology ι] [DenselyOrdered ι] [FirstCountableTopology ι] [NoMaxOrder ι]
    {κ : Type*} [Countable κ] {f : Filtration ι m} {τ : κ -> Ω -> WithTop ι}
    [f.IsRightContinuous] (hτ : forall n, IsStoppingTime f (τ n)) :
    IsStoppingTime f (fun ω => ⨅ n, τ n ω) := by
  convert! IsStoppingTime.biInf (κ := κ) Set.countable_univ (fun n _ => hτ n) using 2
  simp

/--
theorem `add_const` / 定理 `add_const`

English:
theorem add_const
  statement: [AddGroup ι] [Preorder ι] [AddRightMono ι]
  proof: by
  intro j
  simp only
  have h_eq : {ω | τ ω + i <= j} = {ω | τ ω <= j - i} := by
    ext ω
    simp only [Set.mem_ofPred_eq, coe_sub]
    cases τ ω with
    | top => simp
    | coe a => norm_cast; simp_rw [← le_sub_iff_add_le]
  rw [h_eq]
  exact f.mono (sub_le_self j hi) _ (hτ (j - i))

中文:
定理 add_const
  结论: [AddGroup ι] [Preorder ι] [AddRightMono ι]
  证明: by
  intro j
  simp only
  have h_eq : {ω | τ ω + i <= j} = {ω | τ ω <= j - i} := by
    ext ω
    simp only [Set.mem_ofPred_eq, coe_sub]
    cases τ ω with
    | top => simp
    | coe a => norm_cast; simp_rw [← le_sub_iff_add_le]
  rw [h_eq]
  exact f.mono (sub_le_self j hi) _ (hτ (j - i))

Depends on / 依赖: Set.mem_ofPred_eq, coe_sub, f.mono, h_eq, le_sub_iff_add_le, mem_ofPred_eq, simp_rw, sub_le_self
-/
theorem add_const [AddGroup ι] [Preorder ι] [AddRightMono ι]
    [AddLeftMono ι] {f : Filtration ι m} {τ : Ω -> WithTop ι} (hτ : IsStoppingTime f τ)
    {i : ι} (hi : 0 <= i) : IsStoppingTime f fun ω => τ ω + i := by
  intro j
  simp only
  have h_eq : {ω | τ ω + i <= j} = {ω | τ ω <= j - i} := by
    ext ω
    simp only [Set.mem_ofPred_eq, coe_sub]
    cases τ ω with
    | top => simp
    | coe a => norm_cast; simp_rw [← le_sub_iff_add_le]
  rw [h_eq]
  exact f.mono (sub_le_self j hi) _ (hτ (j - i))

/--
theorem `add_const'` / 定理 `add_const'`

English:
theorem add_const'
  statement: [Add ι] [LinearOrder ι] [CanonicallyOrderedAdd ι] [Countable ι]
  proof: by
  intro j
  have h : {ω | τ ω + i <= j} = ⋃ k : {k | k + i <= j}, {ω | τ ω = k} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
    cases τ ω with
    | top => simp
    | coe a => simp; norm_cast
  exact h ▸ MeasurableSet.iUnion fun k => hτ.measurableSet_eq_le (le_of_add_le_left

中文:
定理 add_const'
  结论: [Add ι] [LinearOrder ι] [CanonicallyOrderedAdd ι] [Countable ι]
  证明: by
  intro j
  have h : {ω | τ ω + i <= j} = ⋃ k : {k | k + i <= j}, {ω | τ ω = k} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
    cases τ ω with
    | top => simp
    | coe a => simp; norm_cast
  exact h ▸ MeasurableSet.iUnion fun k => hτ.measurableSet_eq_le (le_of_add_le_left

Depends on / 依赖: MeasurableSet, MeasurableSet.iUnion, Set.mem_iUnion, Set.mem_ofPred_eq, iUnion, le_of_add_le_left, measurableSet_eq_le, mem_iUnion, mem_ofPred_eq
-/
theorem add_const' [Add ι] [LinearOrder ι] [CanonicallyOrderedAdd ι] [Countable ι]
    [TopologicalSpace ι] [OrderTopology ι]
    {f : Filtration ι m} {τ : Ω -> WithTop ι}
    (hτ : IsStoppingTime f τ) (i : ι) :
    IsStoppingTime f fun ω => τ ω + i := by
  intro j
  have h : {ω | τ ω + i <= j} = ⋃ k : {k | k + i <= j}, {ω | τ ω = k} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
    cases τ ω with
    | top => simp
    | coe a => simp; norm_cast
  exact h ▸ MeasurableSet.iUnion fun k => hτ.measurableSet_eq_le (le_of_add_le_left k.2)

/--
theorem `add` / 定理 `add`

English:
theorem add
  statement: [Add ι] [LinearOrder ι] [CanonicallyOrderedAdd ι] [Countable ι]
  proof: by
  intro j
  have h : {ω | (τ + π) ω <= j} = ⋃ k : Set.Iic j, {ω | π ω = k} inter {ω | τ ω + k <= j} := by
    ext ω
    simp only [Pi.add_apply, Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff]
    cases τ ω with
    | top => simp
    | coe a =>
      cases π ω with
      | top => simp
     

中文:
定理 add
  结论: [Add ι] [LinearOrder ι] [CanonicallyOrderedAdd ι] [Countable ι]
  证明: by
  intro j
  have h : {ω | (τ + π) ω <= j} = ⋃ k : Set.Iic j, {ω | π ω = k} inter {ω | τ ω + k <= j} := by
    ext ω
    simp only [Pi.add_apply, Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff]
    cases τ ω with
    | top => simp
    | coe a =>
      cases π ω with
      | top => simp
     

Depends on / 依赖: MeasurableSet, MeasurableSet.iUnion, Pi.add_apply, Set.Iic, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_ofPred_eq, add_apply, add_const, iUnion, le_of_add_le_right, measurableSet_eq_le, mem_iUnion, mem_inter_iff, mem_ofPred_eq
-/
theorem add [Add ι] [LinearOrder ι] [CanonicallyOrderedAdd ι] [Countable ι]
    [TopologicalSpace ι] [OrderTopology ι]
    {f : Filtration ι m} {τ π : Ω -> WithTop ι}
    (hτ : IsStoppingTime f τ) (hπ : IsStoppingTime f π) :
    IsStoppingTime f (τ + π) := by
  intro j
  have h : {ω | (τ + π) ω <= j} = ⋃ k : Set.Iic j, {ω | π ω = k} inter {ω | τ ω + k <= j} := by
    ext ω
    simp only [Pi.add_apply, Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff]
    cases τ ω with
    | top => simp
    | coe a =>
      cases π ω with
      | top => simp
      | coe b => norm_cast; simpa using le_of_add_le_right
  exact h ▸ MeasurableSet.iUnion fun k => (hπ.measurableSet_eq_le k.2).inter (hτ.add_const' k.1 j)

section Preorder

variable [Preorder ι] {f : Filtration ι m} {τ π : Ω -> WithTop ι}

/-- The associated σ-algebra with a stopping time. -/
@[instance_reducible]
/--
Definition of `measurableSpace` / `measurableSpace` 的定义

English:
definition measurableSpace
  signature: (hτ : IsStoppingTime f τ)
  body: MeasurableSet[⨆ t, f t] s ∧ forall i : ι, MeasurableSet[f i] (s inter {ω | τ ω <= i})
  measurableSet_empty := by simp
  measurableSet_compl s hs := by
    refine ⟨hs.1.compl, fun i => ?_⟩
    rw [(_ : sᶜ inter {ω | τ ω <= i} = (sᶜ union {ω | τ ω <= i}ᶜ) inter {ω | τ ω <= i})]
    · refine Measurabl

中文:
定义 measurableSpace
  签名: (hτ : IsStoppingTime f τ)
  定义体: MeasurableSet[⨆ t, f t] s ∧ forall i : ι, MeasurableSet[f i] (s inter {ω | τ ω <= i})
  measurableSet_empty := by simp
  measurableSet_compl s hs := by
    refine ⟨hs.1.compl, fun i => ?_⟩
    rw [(_ : sᶜ inter {ω | τ ω <= i} = (sᶜ union {ω | τ ω <= i}ᶜ) inter {ω | τ ω <= i})]
    · refine Measurabl
-/
protected def measurableSpace (hτ : IsStoppingTime f τ) : MeasurableSpace Ω where
  MeasurableSet' s := MeasurableSet[⨆ t, f t] s ∧ forall i : ι, MeasurableSet[f i] (s inter {ω | τ ω <= i})
  measurableSet_empty := by simp
  measurableSet_compl s hs := by
    refine ⟨hs.1.compl, fun i => ?_⟩
    rw [(_ : sᶜ inter {ω | τ ω <= i} = (sᶜ union {ω | τ ω <= i}ᶜ) inter {ω | τ ω <= i})]
    · refine MeasurableSet.inter ?_ ?_
      · rw [← Set.compl_inter]
        exact (hs.2 i).compl
      · exact hτ i
    · rw [Set.union_inter_distrib_right]
      simp only [Set.compl_inter_self, Set.union_empty]
  measurableSet_iUnion s hs := by
    refine ⟨MeasurableSet.iUnion fun i => (hs i).1, fun i => ?_⟩
    replace hs := fun i => (hs i).2
    rw [forall_comm] at hs
    rw [Set.iUnion_inter]
    exact MeasurableSet.iUnion (hs i)

/--
theorem `measurableSet` / 定理 `measurableSet`

English:
theorem measurableSet
  given: (hτ : IsStoppingTime f τ) (s : Set Ω)
  proof: Iff.rfl

中文:
定理 measurableSet
  条件: (hτ : IsStoppingTime f τ) (s : Set Ω)
  证明: Iff.rfl
-/
protected theorem measurableSet (hτ : IsStoppingTime f τ) (s : Set Ω) :
    MeasurableSet[hτ.measurableSpace] s
      ↔ MeasurableSet[⨆ t, f t] s ∧ forall i : ι, MeasurableSet[f i] (s inter {ω | τ ω <= i}) :=
  Iff.rfl

/--
theorem `measurableSpace_mono` / 定理 `measurableSpace_mono`

English:
theorem measurableSpace_mono
  given: (hτ : IsStoppingTime f τ) (hπ : IsStoppingTime f π) (hle : τ <= π)
  proof: by
  refine fun s hs => ⟨hs.1, fun i => ?_⟩
  rw [(_ : s inter {ω | π ω <= i} = s inter {ω | τ ω <= i} inter {ω | π ω <= i})]
  · exact (hs.2 i).inter (hπ i)
  · ext
    simp only [Set.mem_inter_iff, iff_self_and, and_congr_left_iff, Set.mem_ofPred_eq]
    intro hle' _
    exact le_trans (hle _) hle

中文:
定理 measurableSpace_mono
  条件: (hτ : IsStoppingTime f τ) (hπ : IsStoppingTime f π) (hle : τ <= π)
  证明: by
  refine fun s hs => ⟨hs.1, fun i => ?_⟩
  rw [(_ : s inter {ω | π ω <= i} = s inter {ω | τ ω <= i} inter {ω | π ω <= i})]
  · exact (hs.2 i).inter (hπ i)
  · ext
    simp only [Set.mem_inter_iff, iff_self_and, and_congr_left_iff, Set.mem_ofPred_eq]
    intro hle' _
    exact le_trans (hle _) hle

Depends on / 依赖: Set.mem_inter_iff, Set.mem_ofPred_eq, and_congr_left_iff, iff_self_and, le_trans, mem_inter_iff, mem_ofPred_eq
-/
theorem measurableSpace_mono (hτ : IsStoppingTime f τ) (hπ : IsStoppingTime f π) (hle : τ <= π) :
    hτ.measurableSpace <= hπ.measurableSpace := by
  refine fun s hs => ⟨hs.1, fun i => ?_⟩
  rw [(_ : s inter {ω | π ω <= i} = s inter {ω | τ ω <= i} inter {ω | π ω <= i})]
  · exact (hs.2 i).inter (hπ i)
  · ext
    simp only [Set.mem_inter_iff, iff_self_and, and_congr_left_iff, Set.mem_ofPred_eq]
    intro hle' _
    exact le_trans (hle _) hle'

/--
theorem `measurableSpace_le'` / 定理 `measurableSpace_le'`

English:
theorem measurableSpace_le'
  given: (hτ : IsStoppingTime f τ)
  proof: fun _ hs => hs.1

中文:
定理 measurableSpace_le'
  条件: (hτ : IsStoppingTime f τ)
  证明: fun _ hs => hs.1
-/
theorem measurableSpace_le' (hτ : IsStoppingTime f τ) :
    hτ.measurableSpace <= ⨆ t, f t := fun _ hs => hs.1

/--
theorem `measurableSpace_le` / 定理 `measurableSpace_le`

English:
theorem measurableSpace_le
  given: (hτ : IsStoppingTime f τ)
  statement: hτ.measurableSpace <= m
  proof: hτ.measurableSpace_le'.trans (iSup_le f.le)

@[simp]

中文:
定理 measurableSpace_le
  条件: (hτ : IsStoppingTime f τ)
  结论: hτ.measurableSpace <= m
  证明: hτ.measurableSpace_le'.trans (iSup_le f.le)

@[simp]

Depends on / 依赖: f.le, iSup_le, measurableSpace_le
-/
theorem measurableSpace_le (hτ : IsStoppingTime f τ) : hτ.measurableSpace <= m :=
  hτ.measurableSpace_le'.trans (iSup_le f.le)

@[simp]
/--
theorem `measurableSpace_const` / 定理 `measurableSpace_const`

English:
theorem measurableSpace_const
  given: (f : Filtration ι m) (i : ι)
  proof: by
  ext1 s
  rw [IsStoppingTime.measurableSet]
  constructor <;> intro h
  · have h' := h.2 i
    simpa only [le_refl, Set.ofPred_true, Set.inter_univ] using h'
  · refine ⟨le_iSup f i s h, fun j => ?_⟩
    by_cases hij : i <= j
    · norm_cast
      simp only [hij, Set.ofPred_true, Set.inter_univ]

中文:
定理 measurableSpace_const
  条件: (f : Filtration ι m) (i : ι)
  证明: by
  ext1 s
  rw [IsStoppingTime.measurableSet]
  constructor <;> intro h
  · have h' := h.2 i
    simpa only [le_refl, Set.ofPred_true, Set.inter_univ] using h'
  · refine ⟨le_iSup f i s h, fun j => ?_⟩
    by_cases hij : i <= j
    · norm_cast
      simp only [hij, Set.ofPred_true, Set.inter_univ]

Depends on / 依赖: IsStoppingTime, IsStoppingTime.measurableSet, MeasurableSet, MeasurableSet.empty, Set.inter_empty, Set.inter_univ, Set.ofPred_false, Set.ofPred_true, f.mono, inter_empty, inter_univ, le_iSup, le_refl, measurableSet, ofPred_false, ofPred_true
-/
theorem measurableSpace_const (f : Filtration ι m) (i : ι) :
    (isStoppingTime_const f i).measurableSpace = f i := by
  ext1 s
  rw [IsStoppingTime.measurableSet]
  constructor <;> intro h
  · have h' := h.2 i
    simpa only [le_refl, Set.ofPred_true, Set.inter_univ] using h'
  · refine ⟨le_iSup f i s h, fun j => ?_⟩
    by_cases hij : i <= j
    · norm_cast
      simp only [hij, Set.ofPred_true, Set.inter_univ]
      exact f.mono hij _ h
    · norm_cast
      simp only [hij, Set.ofPred_false, Set.inter_empty, @MeasurableSet.empty _ (f.1 j)]

/--
theorem `measurableSet_inter_eq_iff` / 定理 `measurableSet_inter_eq_iff`

English:
theorem measurableSet_inter_eq_iff
  given: (hτ : IsStoppingTime f τ) (s : Set Ω) (i : ι)
  proof: by
  have : forall j, {ω : Ω | τ ω = i} inter {ω : Ω | τ ω <= j} = {ω : Ω | τ ω = i} inter {_ω | i <= j} := by
    intro j
    ext1 ω
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, and_congr_right_iff]
    intro hxi
    rw [hxi]
  constructor <;> intro h
  · simpa [Set.inter_assoc, this] using

中文:
定理 measurableSet_inter_eq_iff
  条件: (hτ : IsStoppingTime f τ) (s : Set Ω) (i : ι)
  证明: by
  have : forall j, {ω : Ω | τ ω = i} inter {ω : Ω | τ ω <= j} = {ω : Ω | τ ω = i} inter {_ω | i <= j} := by
    intro j
    ext1 ω
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, and_congr_right_iff]
    intro hxi
    rw [hxi]
  constructor <;> intro h
  · simpa [Set.inter_assoc, this] using

Depends on / 依赖: Set.inter_assoc, Set.inter_univ, Set.mem_inter_iff, Set.mem_ofPred_eq, Set.ofPred_true, and_congr_right_iff, f.mono, inter_assoc, inter_univ, le_iSup, mem_inter_iff, mem_ofPred_eq, ofPred_true
-/
theorem measurableSet_inter_eq_iff (hτ : IsStoppingTime f τ) (s : Set Ω) (i : ι) :
    MeasurableSet[hτ.measurableSpace] (s inter {ω | τ ω = i}) ↔
      MeasurableSet[f i] (s inter {ω | τ ω = i}) := by
  have : forall j, {ω : Ω | τ ω = i} inter {ω : Ω | τ ω <= j} = {ω : Ω | τ ω = i} inter {_ω | i <= j} := by
    intro j
    ext1 ω
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, and_congr_right_iff]
    intro hxi
    rw [hxi]
  constructor <;> intro h
  · simpa [Set.inter_assoc, this] using h.2 i
  · refine ⟨le_iSup f i _ h, fun j => ?_⟩
    rw [Set.inter_assoc]; rw [this]
    by_cases hij : i <= j
    · norm_cast
      simp only [hij, Set.ofPred_true, Set.inter_univ]
      exact f.mono hij _ h
    · simp [hij]

/--
theorem `measurableSpace_le_of_le_const` / 定理 `measurableSpace_le_of_le_const`

English:
theorem measurableSpace_le_of_le_const
  given: (hτ : IsStoppingTime f τ) {i : ι} (hτ_le : forall ω, τ ω <= i)
  proof: (measurableSpace_mono hτ _ hτ_le).trans (measurableSpace_const _ _).le

中文:
定理 measurableSpace_le_of_le_const
  条件: (hτ : IsStoppingTime f τ) {i : ι} (hτ_le : 对任意 ω, τ ω <= i)
  证明: (measurableSpace_mono hτ _ hτ_le).trans (measurableSpace_const _ _).le

Depends on / 依赖: measurableSpace_const, measurableSpace_mono
-/
theorem measurableSpace_le_of_le_const (hτ : IsStoppingTime f τ) {i : ι} (hτ_le : forall ω, τ ω <= i) :
    hτ.measurableSpace <= f i :=
  (measurableSpace_mono hτ _ hτ_le).trans (measurableSpace_const _ _).le

/--
theorem `measurableSpace_le_of_le` / 定理 `measurableSpace_le_of_le`

English:
theorem measurableSpace_le_of_le
  given: (hτ : IsStoppingTime f τ) {n : ι} (hτ_le : forall ω, τ ω <= n)
  proof: (hτ.measurableSpace_le_of_le_const hτ_le).trans (f.le n)

中文:
定理 measurableSpace_le_of_le
  条件: (hτ : IsStoppingTime f τ) {n : ι} (hτ_le : 对任意 ω, τ ω <= n)
  证明: (hτ.measurableSpace_le_of_le_const hτ_le).trans (f.le n)

Depends on / 依赖: f.le, measurableSpace_le_of_le_const
-/
theorem measurableSpace_le_of_le (hτ : IsStoppingTime f τ) {n : ι} (hτ_le : forall ω, τ ω <= n) :
    hτ.measurableSpace <= m :=
  (hτ.measurableSpace_le_of_le_const hτ_le).trans (f.le n)

/--
theorem `le_measurableSpace_of_const_le` / 定理 `le_measurableSpace_of_const_le`

English:
theorem le_measurableSpace_of_const_le
  given: (hτ : IsStoppingTime f τ) {i : ι} (hτ_le : forall ω, i <= τ ω)
  proof: (measurableSpace_const _ _).symm.le.trans (measurableSpace_mono _ hτ hτ_le)

中文:
定理 le_measurableSpace_of_const_le
  条件: (hτ : IsStoppingTime f τ) {i : ι} (hτ_le : 对任意 ω, i <= τ ω)
  证明: (measurableSpace_const _ _).symm.le.trans (measurableSpace_mono _ hτ hτ_le)

Depends on / 依赖: measurableSpace_const, measurableSpace_mono, symm.le.trans
-/
theorem le_measurableSpace_of_const_le (hτ : IsStoppingTime f τ) {i : ι} (hτ_le : forall ω, i <= τ ω) :
    f i <= hτ.measurableSpace :=
  (measurableSpace_const _ _).symm.le.trans (measurableSpace_mono _ hτ hτ_le)

end Preorder

/--
Instance `sigmaFinite_stopping_time` / 实例 `sigmaFinite_stopping_time`

English:
instance sigmaFinite_stopping_time
  signature: {ι} [SemilatticeSup ι] [OrderBot ι]
  body: by
  refine @sigmaFiniteTrim_mono _ _ ?_ _ _ _ ?_ ?_
  · exact f ⊥
  · exact hτ.le_measurableSpace_of_const_le fun _ => bot_le
  · infer_instance

中文:
实例 sigmaFinite_stopping_time
  签名: {ι} [SemilatticeSup ι] [OrderBot ι]
  定义体: by
  refine @sigmaFiniteTrim_mono _ _ ?_ _ _ _ ?_ ?_
  · exact f ⊥
  · exact hτ.le_measurableSpace_of_const_le fun _ => bot_le
  · infer_instance

Depends on / 依赖: bot_le, infer_instance, le_measurableSpace_of_const_le, sigmaFiniteTrim_mono
-/
instance sigmaFinite_stopping_time {ι} [SemilatticeSup ι] [OrderBot ι]
    {μ : Measure Ω} {f : Filtration ι m}
    {τ : Ω -> WithTop ι} [SigmaFiniteFiltration μ f] (hτ : IsStoppingTime f τ) :
    SigmaFinite (μ.trim hτ.measurableSpace_le) := by
  refine @sigmaFiniteTrim_mono _ _ ?_ _ _ _ ?_ ?_
  · exact f ⊥
  · exact hτ.le_measurableSpace_of_const_le fun _ => bot_le
  · infer_instance

/--
Instance `sigmaFinite_stopping_time_of_le` / 实例 `sigmaFinite_stopping_time_of_le`

English:
instance sigmaFinite_stopping_time_of_le
  signature: {ι} [SemilatticeSup ι] [OrderBot ι] {μ : Measure Ω}
  body: by
  refine @sigmaFiniteTrim_mono _ _ ?_ _ _ _ ?_ ?_
  · exact f ⊥
  · exact hτ.le_measurableSpace_of_const_le fun _ => bot_le
  · infer_instance

中文:
实例 sigmaFinite_stopping_time_of_le
  签名: {ι} [SemilatticeSup ι] [OrderBot ι] {μ : Measure Ω}
  定义体: by
  refine @sigmaFiniteTrim_mono _ _ ?_ _ _ _ ?_ ?_
  · exact f ⊥
  · exact hτ.le_measurableSpace_of_const_le fun _ => bot_le
  · infer_instance

Depends on / 依赖: bot_le, infer_instance, le_measurableSpace_of_const_le, sigmaFiniteTrim_mono
-/
instance sigmaFinite_stopping_time_of_le {ι} [SemilatticeSup ι] [OrderBot ι] {μ : Measure Ω}
    {f : Filtration ι m} {τ : Ω -> WithTop ι} [SigmaFiniteFiltration μ f]
    (hτ : IsStoppingTime f τ) {n : ι}
    (hτ_le : forall ω, τ ω <= n) : SigmaFinite (μ.trim (hτ.measurableSpace_le_of_le hτ_le)) := by
  refine @sigmaFiniteTrim_mono _ _ ?_ _ _ _ ?_ ?_
  · exact f ⊥
  · exact hτ.le_measurableSpace_of_const_le fun _ => bot_le
  · infer_instance

section LinearOrder

variable [LinearOrder ι] {f : Filtration ι m} {τ π : Ω -> WithTop ι}

/--
theorem `measurableSet_le'` / 定理 `measurableSet_le'`

English:
theorem measurableSet_le'
  given: (hτ : IsStoppingTime f τ) (i : ι)
  proof: by
  refine ⟨le_iSup f i _ (hτ i), fun j => ?_⟩
  have : {ω : Ω | τ ω <= i} inter {ω : Ω | τ ω <= j} = {ω : Ω | τ ω <= min i j} := by
    ext1 ω
    simp [Set.mem_inter_iff, Set.mem_ofPred_eq]
  rw [this]
  exact f.mono (min_le_right i j) _ (hτ _)

中文:
定理 measurableSet_le'
  条件: (hτ : IsStoppingTime f τ) (i : ι)
  证明: by
  refine ⟨le_iSup f i _ (hτ i), fun j => ?_⟩
  have : {ω : Ω | τ ω <= i} inter {ω : Ω | τ ω <= j} = {ω : Ω | τ ω <= min i j} := by
    ext1 ω
    simp [Set.mem_inter_iff, Set.mem_ofPred_eq]
  rw [this]
  exact f.mono (min_le_right i j) _ (hτ _)
-/
protected theorem measurableSet_le' (hτ : IsStoppingTime f τ) (i : ι) :
    MeasurableSet[hτ.measurableSpace] {ω | τ ω <= i} := by
  refine ⟨le_iSup f i _ (hτ i), fun j => ?_⟩
  have : {ω : Ω | τ ω <= i} inter {ω : Ω | τ ω <= j} = {ω : Ω | τ ω <= min i j} := by
    ext1 ω
    simp [Set.mem_inter_iff, Set.mem_ofPred_eq]
  rw [this]
  exact f.mono (min_le_right i j) _ (hτ _)

/--
theorem `measurableSet_gt'` / 定理 `measurableSet_gt'`

English:
theorem measurableSet_gt'
  given: (hτ : IsStoppingTime f τ) (i : ι)
  proof: by
  have : {ω : Ω | i < τ ω} = {ω : Ω | τ ω <= i}ᶜ := by ext1 ω; simp
  rw [this]
  exact (hτ.measurableSet_le' i).compl

中文:
定理 measurableSet_gt'
  条件: (hτ : IsStoppingTime f τ) (i : ι)
  证明: by
  have : {ω : Ω | i < τ ω} = {ω : Ω | τ ω <= i}ᶜ := by ext1 ω; simp
  rw [this]
  exact (hτ.measurableSet_le' i).compl

Depends on / 依赖: IsAddTorsionFree, Rat.den_mul_eq_num, den_mul_eq_num, den_nz, nsmul_eq_mul, of_module_rat, otimes, q.den, q.den_nz, smul_assoc, smul_right_injective, smul_tmul, tmul_smul
-/
protected theorem measurableSet_gt' (hτ : IsStoppingTime f τ) (i : ι) :
    MeasurableSet[hτ.measurableSpace] {ω | i < τ ω} := by
  have : {ω : Ω | i < τ ω} = {ω : Ω | τ ω <= i}ᶜ := by ext1 ω; simp
  rw [this]
  exact (hτ.measurableSet_le' i).compl

/--
theorem `measurableSet_eq'` / 定理 `measurableSet_eq'`

English:
theorem measurableSet_eq'
  statement: [TopologicalSpace ι] [OrderTopology ι]
  proof: by
  rw [← Set.univ_inter {ω | τ ω = i}]; rw [measurableSet_inter_eq_iff]; rw [Set.univ_inter]
  exact hτ.measurableSet_eq i

中文:
定理 measurableSet_eq'
  结论: [TopologicalSpace ι] [OrderTopology ι]
  证明: by
  rw [← Set.univ_inter {ω | τ ω = i}]; rw [measurableSet_inter_eq_iff]; rw [Set.univ_inter]
  exact hτ.measurableSet_eq i
-/
protected theorem measurableSet_eq' [TopologicalSpace ι] [OrderTopology ι]
    [FirstCountableTopology ι] (hτ : IsStoppingTime f τ) (i : ι) :
    MeasurableSet[hτ.measurableSpace] {ω | τ ω = i} := by
  rw [← Set.univ_inter {ω | τ ω = i}]; rw [measurableSet_inter_eq_iff]; rw [Set.univ_inter]
  exact hτ.measurableSet_eq i

/--
theorem `measurableSet_ge'` / 定理 `measurableSet_ge'`

English:
theorem measurableSet_ge'
  statement: [TopologicalSpace ι] [OrderTopology ι]
  proof: by
  have : {ω | i <= τ ω} = {ω | τ ω = i} union {ω | i < τ ω} := by
    ext1 ω
    simp only [le_iff_lt_or_eq, Set.mem_ofPred_eq, Set.mem_union]
    cases τ ω with
    | top => simp
    | coe a =>
      norm_cast
      rw [@eq_comm _ i]; rw [or_comm]
  rw [this]
  exact (hτ.measurableSet_eq' i).uni

中文:
定理 measurableSet_ge'
  结论: [TopologicalSpace ι] [OrderTopology ι]
  证明: by
  have : {ω | i <= τ ω} = {ω | τ ω = i} union {ω | i < τ ω} := by
    ext1 ω
    simp only [le_iff_lt_or_eq, Set.mem_ofPred_eq, Set.mem_union]
    cases τ ω with
    | top => simp
    | coe a =>
      norm_cast
      rw [@eq_comm _ i]; rw [or_comm]
  rw [this]
  exact (hτ.measurableSet_eq' i).uni
-/
protected theorem measurableSet_ge' [TopologicalSpace ι] [OrderTopology ι]
    [FirstCountableTopology ι] (hτ : IsStoppingTime f τ) (i : ι) :
    MeasurableSet[hτ.measurableSpace] {ω | i <= τ ω} := by
  have : {ω | i <= τ ω} = {ω | τ ω = i} union {ω | i < τ ω} := by
    ext1 ω
    simp only [le_iff_lt_or_eq, Set.mem_ofPred_eq, Set.mem_union]
    cases τ ω with
    | top => simp
    | coe a =>
      norm_cast
      rw [@eq_comm _ i]; rw [or_comm]
  rw [this]
  exact (hτ.measurableSet_eq' i).union (hτ.measurableSet_gt' i)

/--
theorem `measurableSet_lt'` / 定理 `measurableSet_lt'`

English:
theorem measurableSet_lt'
  statement: [TopologicalSpace ι] [OrderTopology ι]
  proof: by
  have : {ω | τ ω < i} = {ω | τ ω <= i} \ {ω | τ ω = i} := by
    ext1 ω
    simp only [lt_iff_le_and_ne, Set.mem_ofPred_eq, Set.mem_sdiff]
  rw [this]
  exact (hτ.measurableSet_le' i).diff (hτ.measurableSet_eq' i)

中文:
定理 measurableSet_lt'
  结论: [TopologicalSpace ι] [OrderTopology ι]
  证明: by
  have : {ω | τ ω < i} = {ω | τ ω <= i} \ {ω | τ ω = i} := by
    ext1 ω
    simp only [lt_iff_le_and_ne, Set.mem_ofPred_eq, Set.mem_sdiff]
  rw [this]
  exact (hτ.measurableSet_le' i).diff (hτ.measurableSet_eq' i)
-/
protected theorem measurableSet_lt' [TopologicalSpace ι] [OrderTopology ι]
    [FirstCountableTopology ι] (hτ : IsStoppingTime f τ) (i : ι) :
    MeasurableSet[hτ.measurableSpace] {ω | τ ω < i} := by
  have : {ω | τ ω < i} = {ω | τ ω <= i} \ {ω | τ ω = i} := by
    ext1 ω
    simp only [lt_iff_le_and_ne, Set.mem_ofPred_eq, Set.mem_sdiff]
  rw [this]
  exact (hτ.measurableSet_le' i).diff (hτ.measurableSet_eq' i)

section Countable

/--
theorem `measurableSet_eq_of_countable_range'` / 定理 `measurableSet_eq_of_countable_range'`

English:
theorem measurableSet_eq_of_countable_range'
  statement: (hτ : IsStoppingTime f τ)
  proof: by
  rw [← Set.univ_inter {ω | τ ω = i}]; rw [measurableSet_inter_eq_iff]; rw [Set.univ_inter]
  exact hτ.measurableSet_eq_of_countable_range h_countable i

中文:
定理 measurableSet_eq_of_countable_range'
  结论: (hτ : IsStoppingTime f τ)
  证明: by
  rw [← Set.univ_inter {ω | τ ω = i}]; rw [measurableSet_inter_eq_iff]; rw [Set.univ_inter]
  exact hτ.measurableSet_eq_of_countable_range h_countable i
-/
protected theorem measurableSet_eq_of_countable_range' (hτ : IsStoppingTime f τ)
    (h_countable : (Set.range τ).Countable) (i : ι) :
    MeasurableSet[hτ.measurableSpace] {ω | τ ω = i} := by
  rw [← Set.univ_inter {ω | τ ω = i}]; rw [measurableSet_inter_eq_iff]; rw [Set.univ_inter]
  exact hτ.measurableSet_eq_of_countable_range h_countable i

/--
theorem `measurableSet_eq_of_countable'` / 定理 `measurableSet_eq_of_countable'`

English:
theorem measurableSet_eq_of_countable'
  given: [Countable ι] (hτ : IsStoppingTime f τ) (i : ι)
  proof: hτ.measurableSet_eq_of_countable_range' (Set.to_countable _) i

中文:
定理 measurableSet_eq_of_countable'
  条件: [Countable ι] (hτ : IsStoppingTime f τ) (i : ι)
  证明: hτ.measurableSet_eq_of_countable_range' (Set.to_countable _) i
-/
protected theorem measurableSet_eq_of_countable' [Countable ι] (hτ : IsStoppingTime f τ) (i : ι) :
    MeasurableSet[hτ.measurableSpace] {ω | τ ω = i} :=
  hτ.measurableSet_eq_of_countable_range' (Set.to_countable _) i

/--
theorem `measurableSet_ge_of_countable_range'` / 定理 `measurableSet_ge_of_countable_range'`

English:
theorem measurableSet_ge_of_countable_range'
  statement: (hτ : IsStoppingTime f τ)
  proof: by
  have : {ω | i <= τ ω} = {ω | τ ω = i} union {ω | i < τ ω} := by
    ext1 ω
    simp only [le_iff_lt_or_eq, Set.mem_ofPred_eq, Set.mem_union]
    cases τ ω with
    | top => simp
    | coe a =>
      norm_cast
      rw [@eq_comm _ i]; rw [or_comm]
  rw [this]
  exact (hτ.measurableSet_eq_of_coun

中文:
定理 measurableSet_ge_of_countable_range'
  结论: (hτ : IsStoppingTime f τ)
  证明: by
  have : {ω | i <= τ ω} = {ω | τ ω = i} union {ω | i < τ ω} := by
    ext1 ω
    simp only [le_iff_lt_or_eq, Set.mem_ofPred_eq, Set.mem_union]
    cases τ ω with
    | top => simp
    | coe a =>
      norm_cast
      rw [@eq_comm _ i]; rw [or_comm]
  rw [this]
  exact (hτ.measurableSet_eq_of_coun
-/
protected theorem measurableSet_ge_of_countable_range' (hτ : IsStoppingTime f τ)
    (h_countable : (Set.range τ).Countable) (i : ι) :
    MeasurableSet[hτ.measurableSpace] {ω | i <= τ ω} := by
  have : {ω | i <= τ ω} = {ω | τ ω = i} union {ω | i < τ ω} := by
    ext1 ω
    simp only [le_iff_lt_or_eq, Set.mem_ofPred_eq, Set.mem_union]
    cases τ ω with
    | top => simp
    | coe a =>
      norm_cast
      rw [@eq_comm _ i]; rw [or_comm]
  rw [this]
  exact (hτ.measurableSet_eq_of_countable_range' h_countable i).union (hτ.measurableSet_gt' i)

/--
theorem `measurableSet_ge_of_countable'` / 定理 `measurableSet_ge_of_countable'`

English:
theorem measurableSet_ge_of_countable'
  given: [Countable ι] (hτ : IsStoppingTime f τ) (i : ι)
  proof: hτ.measurableSet_ge_of_countable_range' (Set.to_countable _) i

中文:
定理 measurableSet_ge_of_countable'
  条件: [Countable ι] (hτ : IsStoppingTime f τ) (i : ι)
  证明: hτ.measurableSet_ge_of_countable_range' (Set.to_countable _) i
-/
protected theorem measurableSet_ge_of_countable' [Countable ι] (hτ : IsStoppingTime f τ) (i : ι) :
    MeasurableSet[hτ.measurableSpace] {ω | i <= τ ω} :=
  hτ.measurableSet_ge_of_countable_range' (Set.to_countable _) i

/--
theorem `measurableSet_lt_of_countable_range'` / 定理 `measurableSet_lt_of_countable_range'`

English:
theorem measurableSet_lt_of_countable_range'
  statement: (hτ : IsStoppingTime f τ)
  proof: by
  have : {ω | τ ω < i} = {ω | τ ω <= i} \ {ω | τ ω = i} := by
    ext1 ω
    simp only [lt_iff_le_and_ne, Set.mem_ofPred_eq, Set.mem_sdiff]
  rw [this]
  exact (hτ.measurableSet_le' i).diff (hτ.measurableSet_eq_of_countable_range' h_countable i)

中文:
定理 measurableSet_lt_of_countable_range'
  结论: (hτ : IsStoppingTime f τ)
  证明: by
  have : {ω | τ ω < i} = {ω | τ ω <= i} \ {ω | τ ω = i} := by
    ext1 ω
    simp only [lt_iff_le_and_ne, Set.mem_ofPred_eq, Set.mem_sdiff]
  rw [this]
  exact (hτ.measurableSet_le' i).diff (hτ.measurableSet_eq_of_countable_range' h_countable i)
-/
protected theorem measurableSet_lt_of_countable_range' (hτ : IsStoppingTime f τ)
    (h_countable : (Set.range τ).Countable) (i : ι) :
    MeasurableSet[hτ.measurableSpace] {ω | τ ω < i} := by
  have : {ω | τ ω < i} = {ω | τ ω <= i} \ {ω | τ ω = i} := by
    ext1 ω
    simp only [lt_iff_le_and_ne, Set.mem_ofPred_eq, Set.mem_sdiff]
  rw [this]
  exact (hτ.measurableSet_le' i).diff (hτ.measurableSet_eq_of_countable_range' h_countable i)

/--
theorem `measurableSet_lt_of_countable'` / 定理 `measurableSet_lt_of_countable'`

English:
theorem measurableSet_lt_of_countable'
  given: [Countable ι] (hτ : IsStoppingTime f τ) (i : ι)
  proof: hτ.measurableSet_lt_of_countable_range' (Set.to_countable _) i

中文:
定理 measurableSet_lt_of_countable'
  条件: [Countable ι] (hτ : IsStoppingTime f τ) (i : ι)
  证明: hτ.measurableSet_lt_of_countable_range' (Set.to_countable _) i
-/
protected theorem measurableSet_lt_of_countable' [Countable ι] (hτ : IsStoppingTime f τ) (i : ι) :
    MeasurableSet[hτ.measurableSpace] {ω | τ ω < i} :=
  hτ.measurableSet_lt_of_countable_range' (Set.to_countable _) i

end Countable

/--
theorem `measurable` / 定理 `measurable`

English:
theorem measurable
  statement: [TopologicalSpace ι]
  proof: by
  refine measurable_of_Iic fun i => ?_
  cases i with
  | top => simp
  | coe i => exact hτ.measurableSet_le' i

中文:
定理 measurable
  结论: [TopologicalSpace ι]
  证明: by
  refine measurable_of_Iic fun i => ?_
  cases i with
  | top => simp
  | coe i => exact hτ.measurableSet_le' i
-/
protected theorem measurable [TopologicalSpace ι]
    [OrderTopology ι] [SecondCountableTopology ι] (hτ : IsStoppingTime f τ) :
    Measurable[hτ.measurableSpace] τ := by
  refine measurable_of_Iic fun i => ?_
  cases i with
  | top => simp
  | coe i => exact hτ.measurableSet_le' i

/--
theorem `measurable'` / 定理 `measurable'`

English:
theorem measurable'
  statement: [TopologicalSpace ι]
  proof: hτ.measurable.mono (measurableSpace_le hτ) le_rfl

中文:
定理 measurable'
  结论: [TopologicalSpace ι]
  证明: hτ.measurable.mono (measurableSpace_le hτ) le_rfl
-/
protected theorem measurable' [TopologicalSpace ι]
    [OrderTopology ι] [SecondCountableTopology ι] (hτ : IsStoppingTime f τ) :
    Measurable τ := hτ.measurable.mono (measurableSpace_le hτ) le_rfl

/--
theorem `measurable_iSup` / 定理 `measurable_iSup`

English:
theorem measurable_iSup
  statement: [TopologicalSpace ι]
  proof: hτ.measurable.mono (measurableSpace_le' hτ) le_rfl

中文:
定理 measurable_iSup
  结论: [TopologicalSpace ι]
  证明: hτ.measurable.mono (measurableSpace_le' hτ) le_rfl
-/
protected theorem measurable_iSup [TopologicalSpace ι]
    [OrderTopology ι] [SecondCountableTopology ι] (hτ : IsStoppingTime f τ) :
    Measurable[⨆ t, f t] τ := hτ.measurable.mono (measurableSpace_le' hτ) le_rfl

/--
lemma `measurableSet_eq_top` / 引理 `measurableSet_eq_top`

English:
lemma measurableSet_eq_top
  statement: [TopologicalSpace ι]
  proof: (measurableSet_singleton _).preimage hτ.measurable'

中文:
引理 measurableSet_eq_top
  结论: [TopologicalSpace ι]
  证明: (measurableSet_singleton _).preimage hτ.measurable'
-/
protected lemma measurableSet_eq_top [TopologicalSpace ι]
    [OrderTopology ι] [SecondCountableTopology ι] (hτ : IsStoppingTime f τ) :
    MeasurableSet {ω | τ ω = ⊤} :=
  (measurableSet_singleton _).preimage hτ.measurable'

/--
lemma `measurableSet_eq_top'` / 引理 `measurableSet_eq_top'`

English:
lemma measurableSet_eq_top'
  statement: [TopologicalSpace ι]
  proof: (measurableSet_singleton _).preimage hτ.measurable_iSup

中文:
引理 measurableSet_eq_top'
  结论: [TopologicalSpace ι]
  证明: (measurableSet_singleton _).preimage hτ.measurable_iSup
-/
protected lemma measurableSet_eq_top' [TopologicalSpace ι]
    [OrderTopology ι] [SecondCountableTopology ι] (hτ : IsStoppingTime f τ) :
    MeasurableSet[⨆ t, f t] {ω | τ ω = ⊤} :=
  (measurableSet_singleton _).preimage hτ.measurable_iSup

/--
theorem `measurable_of_le` / 定理 `measurable_of_le`

English:
theorem measurable_of_le
  statement: [TopologicalSpace ι]
  proof: hτ.measurable.mono (measurableSpace_le_of_le_const _ hτ_le) le_rfl

中文:
定理 measurable_of_le
  结论: [TopologicalSpace ι]
  证明: hτ.measurable.mono (measurableSpace_le_of_le_const _ hτ_le) le_rfl
-/
protected theorem measurable_of_le [TopologicalSpace ι]
    [OrderTopology ι] [SecondCountableTopology ι] (hτ : IsStoppingTime f τ) {i : ι}
    (hτ_le : forall ω, τ ω <= i) : Measurable[f i] τ :=
  hτ.measurable.mono (measurableSpace_le_of_le_const _ hτ_le) le_rfl

/--
theorem `measurableSpace_min` / 定理 `measurableSpace_min`

English:
theorem measurableSpace_min
  given: (hτ : IsStoppingTime f τ) (hπ : IsStoppingTime f π)
  proof: by
  refine le_antisymm ?_ ?_
  · exact le_inf (measurableSpace_mono _ hτ fun _ => min_le_left _ _)
      (measurableSpace_mono _ hπ fun _ => min_le_right _ _)
  · intro s
    change MeasurableSet[hτ.measurableSpace] s ∧ MeasurableSet[hπ.measurableSpace] s ->
      MeasurableSet[(hτ.min hπ).measurab

中文:
定理 measurableSpace_min
  条件: (hτ : IsStoppingTime f τ) (hπ : IsStoppingTime f π)
  证明: by
  refine le_antisymm ?_ ?_
  · exact le_inf (measurableSpace_mono _ hτ fun _ => min_le_left _ _)
      (measurableSpace_mono _ hπ fun _ => min_le_right _ _)
  · intro s
    change MeasurableSet[hτ.measurableSpace] s ∧ MeasurableSet[hπ.measurableSpace] s ->
      MeasurableSet[(hτ.min hπ).measurab

Depends on / 依赖: IsStoppingTime, IsStoppingTime.measurableSet, MeasurableSet, Set.inter_union_distrib_left, inter_union_distrib_left, le_antisymm, le_inf, measurableSet, measurableSpace, measurableSpace_mono, min_le_left, min_le_right, simp_rw
-/
theorem measurableSpace_min (hτ : IsStoppingTime f τ) (hπ : IsStoppingTime f π) :
    (hτ.min hπ).measurableSpace = hτ.measurableSpace ⊓ hπ.measurableSpace := by
  refine le_antisymm ?_ ?_
  · exact le_inf (measurableSpace_mono _ hτ fun _ => min_le_left _ _)
      (measurableSpace_mono _ hπ fun _ => min_le_right _ _)
  · intro s
    change MeasurableSet[hτ.measurableSpace] s ∧ MeasurableSet[hπ.measurableSpace] s ->
      MeasurableSet[(hτ.min hπ).measurableSpace] s
    simp_rw [IsStoppingTime.measurableSet]
    have : forall i, {ω | min (τ ω) (π ω) <= i} = {ω | τ ω <= i} union {ω | π ω <= i} := by
      intro i; ext1 ω; simp
    simp_rw [this, Set.inter_union_distrib_left]
    exact fun h => ⟨h.1.1, fun i => (h.left.2 i).union (h.right.2 i)⟩

/--
theorem `measurableSet_min_iff` / 定理 `measurableSet_min_iff`

English:
theorem measurableSet_min_iff
  given: (hτ : IsStoppingTime f τ) (hπ : IsStoppingTime f π) (s : Set Ω)
  proof: by
  rw [measurableSpace_min hτ hπ]; rfl

中文:
定理 measurableSet_min_iff
  条件: (hτ : IsStoppingTime f τ) (hπ : IsStoppingTime f π) (s : Set Ω)
  证明: by
  rw [measurableSpace_min hτ hπ]; rfl

Depends on / 依赖: measurableSpace_min
-/
theorem measurableSet_min_iff (hτ : IsStoppingTime f τ) (hπ : IsStoppingTime f π) (s : Set Ω) :
    MeasurableSet[(hτ.min hπ).measurableSpace] s ↔
      MeasurableSet[hτ.measurableSpace] s ∧ MeasurableSet[hπ.measurableSpace] s := by
  rw [measurableSpace_min hτ hπ]; rfl

/--
theorem `measurableSpace_min_const` / 定理 `measurableSpace_min_const`

English:
theorem measurableSpace_min_const
  given: (hτ : IsStoppingTime f τ) {i : ι}
  proof: by
  rw [hτ.measurableSpace_min (isStoppingTime_const _ i)]; rw [measurableSpace_const]

中文:
定理 measurableSpace_min_const
  条件: (hτ : IsStoppingTime f τ) {i : ι}
  证明: by
  rw [hτ.measurableSpace_min (isStoppingTime_const _ i)]; rw [measurableSpace_const]

Depends on / 依赖: isStoppingTime_const, measurableSpace_const, measurableSpace_min
-/
theorem measurableSpace_min_const (hτ : IsStoppingTime f τ) {i : ι} :
    (hτ.min_const i).measurableSpace = hτ.measurableSpace ⊓ f i := by
  rw [hτ.measurableSpace_min (isStoppingTime_const _ i)]; rw [measurableSpace_const]

/--
theorem `measurableSet_min_const_iff` / 定理 `measurableSet_min_const_iff`

English:
theorem measurableSet_min_const_iff
  given: (hτ : IsStoppingTime f τ) (s : Set Ω) {i : ι}
  proof: by
  rw [measurableSpace_min_const hτ]; apply MeasurableSpace.measurableSet_inf

中文:
定理 measurableSet_min_const_iff
  条件: (hτ : IsStoppingTime f τ) (s : Set Ω) {i : ι}
  证明: by
  rw [measurableSpace_min_const hτ]; apply MeasurableSpace.measurableSet_inf

Depends on / 依赖: MeasurableSpace, MeasurableSpace.measurableSet_inf, measurableSet_inf, measurableSpace_min_const
-/
theorem measurableSet_min_const_iff (hτ : IsStoppingTime f τ) (s : Set Ω) {i : ι} :
    MeasurableSet[(hτ.min_const i).measurableSpace] s ↔
      MeasurableSet[hτ.measurableSpace] s ∧ MeasurableSet[f i] s := by
  rw [measurableSpace_min_const hτ]; apply MeasurableSpace.measurableSet_inf

/--
theorem `measurableSet_inter_le` / 定理 `measurableSet_inter_le`

English:
theorem measurableSet_inter_le
  statement: [TopologicalSpace ι] [SecondCountableTopology ι] [OrderTopology ι]
  proof: by
  simp_rw [IsStoppingTime.measurableSet] at hs ⊢
  have h_eq i : s inter {ω | τ ω <= π ω} inter {ω | min (τ ω) (π ω) <= i} =
      s inter {ω | τ ω <= i} inter {ω | min (τ ω) (π ω) <= i} inter
        {ω | min (τ ω) i <= min (min (τ ω) (π ω)) i} := by
    ext ω
    by_cases hτi : τ ω <= i <;> gri

中文:
定理 measurableSet_inter_le
  结论: [TopologicalSpace ι] [SecondCountableTopology ι] [OrderTopology ι]
  证明: by
  simp_rw [IsStoppingTime.measurableSet] at hs ⊢
  have h_eq i : s inter {ω | τ ω <= π ω} inter {ω | min (τ ω) (π ω) <= i} =
      s inter {ω | τ ω <= i} inter {ω | min (τ ω) (π ω) <= i} inter
        {ω | min (τ ω) i <= min (min (τ ω) (π ω)) i} := by
    ext ω
    by_cases hτi : τ ω <= i <;> gri

Depends on / 依赖: Filtration, Filtration.seq, IsStoppingTime, IsStoppingTime.measurableSet, h_eq, measurableSet, measurableSet_le, measurable_iSup, simp_rw
-/
theorem measurableSet_inter_le [TopologicalSpace ι] [SecondCountableTopology ι] [OrderTopology ι]
    (hτ : IsStoppingTime f τ) (hπ : IsStoppingTime f π)
    (s : Set Ω) (hs : MeasurableSet[hτ.measurableSpace] s) :
    MeasurableSet[(hτ.min hπ).measurableSpace] (s inter {ω | τ ω <= π ω}) := by
  simp_rw [IsStoppingTime.measurableSet] at hs ⊢
  have h_eq i : s inter {ω | τ ω <= π ω} inter {ω | min (τ ω) (π ω) <= i} =
      s inter {ω | τ ω <= i} inter {ω | min (τ ω) (π ω) <= i} inter
        {ω | min (τ ω) i <= min (min (τ ω) (π ω)) i} := by
    ext ω
    by_cases hτi : τ ω <= i <;> grind
  simp_rw [h_eq]
  refine ⟨hs.1.inter (measurableSet_le hτ.measurable_iSup hπ.measurable_iSup), fun i => ?_⟩
  refine ((hs.2 i).inter ((hτ.min hπ) i)).inter ?_
  apply @measurableSet_le _ _ _ _ _ (Filtration.seq f i) _ _ _ _ _ ?_ ?_
  · exact (hτ.min_const i).measurable_of_le fun _ => min_le_right _ _
  · exact ((hτ.min hπ).min_const i).measurable_of_le fun _ => min_le_right _ _

/--
theorem `measurableSet_inter_le_iff` / 定理 `measurableSet_inter_le_iff`

English:
theorem measurableSet_inter_le_iff
  statement: [TopologicalSpace ι] [SecondCountableTopology ι]
  proof: by
  constructor <;> intro h
  · have : s inter {ω | τ ω <= π ω} = s inter {ω | τ ω <= π ω} inter {ω | τ ω <= π ω} := by
      rw [Set.inter_assoc]; rw [Set.inter_self]
    rw [this]
    exact measurableSet_inter_le _ hπ _ h
  · rw [measurableSet_min_iff hτ hπ] at h
    exact h.1

中文:
定理 measurableSet_inter_le_iff
  结论: [TopologicalSpace ι] [SecondCountableTopology ι]
  证明: by
  constructor <;> intro h
  · have : s inter {ω | τ ω <= π ω} = s inter {ω | τ ω <= π ω} inter {ω | τ ω <= π ω} := by
      rw [Set.inter_assoc]; rw [Set.inter_self]
    rw [this]
    exact measurableSet_inter_le _ hπ _ h
  · rw [measurableSet_min_iff hτ hπ] at h
    exact h.1

Depends on / 依赖: Set.inter_assoc, Set.inter_self, inter_assoc, inter_self, measurableSet_inter_le, measurableSet_min_iff
-/
theorem measurableSet_inter_le_iff [TopologicalSpace ι] [SecondCountableTopology ι]
    [OrderTopology ι] (hτ : IsStoppingTime f τ)
    (hπ : IsStoppingTime f π) (s : Set Ω) :
    MeasurableSet[hτ.measurableSpace] (s inter {ω | τ ω <= π ω}) ↔
      MeasurableSet[(hτ.min hπ).measurableSpace] (s inter {ω | τ ω <= π ω}) := by
  constructor <;> intro h
  · have : s inter {ω | τ ω <= π ω} = s inter {ω | τ ω <= π ω} inter {ω | τ ω <= π ω} := by
      rw [Set.inter_assoc]; rw [Set.inter_self]
    rw [this]
    exact measurableSet_inter_le _ hπ _ h
  · rw [measurableSet_min_iff hτ hπ] at h
    exact h.1

/--
theorem `measurableSet_inter_le_const_iff` / 定理 `measurableSet_inter_le_const_iff`

English:
theorem measurableSet_inter_le_const_iff
  given: (hτ : IsStoppingTime f τ) (s : Set Ω) (i : ι)
  proof: by
  rw [IsStoppingTime.measurableSet_min_iff hτ (isStoppingTime_const _ i)]; rw [IsStoppingTime.measurableSpace_const]; rw [IsStoppingTime.measurableSet]
  refine ⟨fun h => ⟨h, ?_⟩, fun h => h.1⟩
  have h' := h.2 i
  rwa [Set.inter_assoc, Set.inter_self] at h'

中文:
定理 measurableSet_inter_le_const_iff
  条件: (hτ : IsStoppingTime f τ) (s : Set Ω) (i : ι)
  证明: by
  rw [IsStoppingTime.measurableSet_min_iff hτ (isStoppingTime_const _ i)]; rw [IsStoppingTime.measurableSpace_const]; rw [IsStoppingTime.measurableSet]
  refine ⟨fun h => ⟨h, ?_⟩, fun h => h.1⟩
  have h' := h.2 i
  rwa [Set.inter_assoc, Set.inter_self] at h'

Depends on / 依赖: IsStoppingTime, IsStoppingTime.measurableSet, IsStoppingTime.measurableSet_min_iff, IsStoppingTime.measurableSpace_const, Set.inter_assoc, Set.inter_self, inter_assoc, inter_self, isStoppingTime_const, measurableSet, measurableSet_min_iff, measurableSpace_const
-/
theorem measurableSet_inter_le_const_iff (hτ : IsStoppingTime f τ) (s : Set Ω) (i : ι) :
    MeasurableSet[hτ.measurableSpace] (s inter {ω | τ ω <= i}) ↔
      MeasurableSet[(hτ.min_const i).measurableSpace] (s inter {ω | τ ω <= i}) := by
  rw [IsStoppingTime.measurableSet_min_iff hτ (isStoppingTime_const _ i)]; rw [IsStoppingTime.measurableSpace_const]; rw [IsStoppingTime.measurableSet]
  refine ⟨fun h => ⟨h, ?_⟩, fun h => h.1⟩
  have h' := h.2 i
  rwa [Set.inter_assoc, Set.inter_self] at h'

/--
theorem `measurableSet_le_stopping_time` / 定理 `measurableSet_le_stopping_time`

English:
theorem measurableSet_le_stopping_time
  statement: [TopologicalSpace ι] [SecondCountableTopology ι]
  proof: by
  rw [hτ.measurableSet]
  refine ⟨measurableSet_le hτ.measurable_iSup hπ.measurable_iSup, fun j => ?_⟩
  have : {ω | τ ω <= π ω} inter {ω | τ ω <= j} = {ω | min (τ ω) j <= min (π ω) j} inter {ω | τ ω <= j} := by
    ext
    simpa using fun a b => Std.IsPreorder.le_trans _ _ _ a b
  rw [this]
  re

中文:
定理 measurableSet_le_stopping_time
  结论: [TopologicalSpace ι] [SecondCountableTopology ι]
  证明: by
  rw [hτ.measurableSet]
  refine ⟨measurableSet_le hτ.measurable_iSup hπ.measurable_iSup, fun j => ?_⟩
  have : {ω | τ ω <= π ω} inter {ω | τ ω <= j} = {ω | min (τ ω) j <= min (π ω) j} inter {ω | τ ω <= j} := by
    ext
    simpa using fun a b => Std.IsPreorder.le_trans _ _ _ a b
  rw [this]
  re

Depends on / 依赖: Filtration, Filtration.seq, IsPreorder, MeasurableSet, MeasurableSet.inter, Std.IsPreorder.le_trans, le_trans, measurableSet, measurableSet_le, measurable_iSup, measurable_of_le, min_const, min_le_right
-/
theorem measurableSet_le_stopping_time [TopologicalSpace ι] [SecondCountableTopology ι]
    [OrderTopology ι] (hτ : IsStoppingTime f τ)
    (hπ : IsStoppingTime f π) : MeasurableSet[hτ.measurableSpace] {ω | τ ω <= π ω} := by
  rw [hτ.measurableSet]
  refine ⟨measurableSet_le hτ.measurable_iSup hπ.measurable_iSup, fun j => ?_⟩
  have : {ω | τ ω <= π ω} inter {ω | τ ω <= j} = {ω | min (τ ω) j <= min (π ω) j} inter {ω | τ ω <= j} := by
    ext
    simpa using fun a b => Std.IsPreorder.le_trans _ _ _ a b
  rw [this]
  refine MeasurableSet.inter ?_ (hτ.measurableSet_le j)
  apply @measurableSet_le _ _ _ _ _ (Filtration.seq f j) _ _ _ _ _ ?_ ?_
  · exact (hτ.min_const j).measurable_of_le fun _ => min_le_right _ _
  · exact (hπ.min_const j).measurable_of_le fun _ => min_le_right _ _

/--
theorem `measurableSet_stopping_time_le_min` / 定理 `measurableSet_stopping_time_le_min`

English:
theorem measurableSet_stopping_time_le_min
  statement: [TopologicalSpace ι] [SecondCountableTopology ι]
  proof: by
  rw [← Set.univ_inter {ω : Ω | τ ω <= π ω}]; rw [← hτ.measurableSet_inter_le_iff hπ]; rw [Set.univ_inter]
  exact measurableSet_le_stopping_time hτ hπ

中文:
定理 measurableSet_stopping_time_le_min
  结论: [TopologicalSpace ι] [SecondCountableTopology ι]
  证明: by
  rw [← Set.univ_inter {ω : Ω | τ ω <= π ω}]; rw [← hτ.measurableSet_inter_le_iff hπ]; rw [Set.univ_inter]
  exact measurableSet_le_stopping_time hτ hπ

Depends on / 依赖: Set.univ_inter, measurableSet_inter_le_iff, measurableSet_le_stopping_time, univ_inter
-/
theorem measurableSet_stopping_time_le_min [TopologicalSpace ι] [SecondCountableTopology ι]
    [OrderTopology ι] (hτ : IsStoppingTime f τ) (hπ : IsStoppingTime f π) :
    MeasurableSet[(hτ.min hπ).measurableSpace] {ω | τ ω <= π ω} := by
  rw [← Set.univ_inter {ω : Ω | τ ω <= π ω}]; rw [← hτ.measurableSet_inter_le_iff hπ]; rw [Set.univ_inter]
  exact measurableSet_le_stopping_time hτ hπ

/--
theorem `measurableSet_stopping_time_le` / 定理 `measurableSet_stopping_time_le`

English:
theorem measurableSet_stopping_time_le
  statement: [TopologicalSpace ι] [SecondCountableTopology ι]
  proof: by
  have : MeasurableSet[(hτ.min hπ).measurableSpace] {ω | τ ω <= π ω} :=
    measurableSet_stopping_time_le_min hτ hπ
  rw [measurableSet_min_iff hτ hπ] at this; exact this.2

中文:
定理 measurableSet_stopping_time_le
  结论: [TopologicalSpace ι] [SecondCountableTopology ι]
  证明: by
  have : MeasurableSet[(hτ.min hπ).measurableSpace] {ω | τ ω <= π ω} :=
    measurableSet_stopping_time_le_min hτ hπ
  rw [measurableSet_min_iff hτ hπ] at this; exact this.2

Depends on / 依赖: MeasurableSet, measurableSet_min_iff, measurableSet_stopping_time_le_min, measurableSpace
-/
theorem measurableSet_stopping_time_le [TopologicalSpace ι] [SecondCountableTopology ι]
    [OrderTopology ι] (hτ : IsStoppingTime f τ) (hπ : IsStoppingTime f π) :
    MeasurableSet[hπ.measurableSpace] {ω | τ ω <= π ω} := by
  have : MeasurableSet[(hτ.min hπ).measurableSpace] {ω | τ ω <= π ω} :=
    measurableSet_stopping_time_le_min hτ hπ
  rw [measurableSet_min_iff hτ hπ] at this; exact this.2

/--
theorem `measurableSet_eq_stopping_time_min` / 定理 `measurableSet_eq_stopping_time_min`

English:
theorem measurableSet_eq_stopping_time_min
  statement: [TopologicalSpace ι]
  proof: by
  have : {ω | τ ω = π ω} = {ω | τ ω <= π ω} inter {ω | π ω <= τ ω} := by
    ext; simp only [Set.mem_ofPred_eq, le_antisymm_iff, Set.mem_inter_iff]
  rw [this]
  refine MeasurableSet.inter (measurableSet_stopping_time_le_min hτ hπ) ?_
  convert! (measurableSet_stopping_time_le_min hπ hτ) using 3


中文:
定理 measurableSet_eq_stopping_time_min
  结论: [TopologicalSpace ι]
  证明: by
  have : {ω | τ ω = π ω} = {ω | τ ω <= π ω} inter {ω | π ω <= τ ω} := by
    ext; simp only [Set.mem_ofPred_eq, le_antisymm_iff, Set.mem_inter_iff]
  rw [this]
  refine MeasurableSet.inter (measurableSet_stopping_time_le_min hτ hπ) ?_
  convert! (measurableSet_stopping_time_le_min hπ hτ) using 3


Depends on / 依赖: MeasurableSet, MeasurableSet.inter, Set.mem_inter_iff, Set.mem_ofPred_eq, convert, le_antisymm_iff, measurableSet_stopping_time_le_min, mem_inter_iff, mem_ofPred_eq, min_comm
-/
theorem measurableSet_eq_stopping_time_min [TopologicalSpace ι]
    [OrderTopology ι] [SecondCountableTopology ι]
    (hτ : IsStoppingTime f τ) (hπ : IsStoppingTime f π) :
    MeasurableSet[(hτ.min hπ).measurableSpace] {ω | τ ω = π ω} := by
  have : {ω | τ ω = π ω} = {ω | τ ω <= π ω} inter {ω | π ω <= τ ω} := by
    ext; simp only [Set.mem_ofPred_eq, le_antisymm_iff, Set.mem_inter_iff]
  rw [this]
  refine MeasurableSet.inter (measurableSet_stopping_time_le_min hτ hπ) ?_
  convert! (measurableSet_stopping_time_le_min hπ hτ) using 3
  rw [min_comm]

/--
theorem `measurableSet_eq_stopping_time` / 定理 `measurableSet_eq_stopping_time`

English:
theorem measurableSet_eq_stopping_time
  statement: [TopologicalSpace ι] [OrderTopology ι]
  proof: by
  have h := measurableSet_eq_stopping_time_min hτ hπ
  rw [measurableSet_min_iff hτ hπ] at h
  exact h.1

中文:
定理 measurableSet_eq_stopping_time
  结论: [TopologicalSpace ι] [OrderTopology ι]
  证明: by
  have h := measurableSet_eq_stopping_time_min hτ hπ
  rw [measurableSet_min_iff hτ hπ] at h
  exact h.1

Depends on / 依赖: measurableSet_eq_stopping_time_min, measurableSet_min_iff
-/
theorem measurableSet_eq_stopping_time [TopologicalSpace ι] [OrderTopology ι]
    [SecondCountableTopology ι]
    (hτ : IsStoppingTime f τ) (hπ : IsStoppingTime f π) :
    MeasurableSet[hτ.measurableSpace] {ω | τ ω = π ω} := by
  have h := measurableSet_eq_stopping_time_min hτ hπ
  rw [measurableSet_min_iff hτ hπ] at h
  exact h.1

end LinearOrder

end IsStoppingTime

section LinearOrder

/-! ## Stopped value and stopped process -/

variable [Nonempty ι] {u v : ι -> Ω -> β} {τ σ : Ω -> WithTop ι}

/-- Given a map `u : ι → Ω → E`, its stopped value with respect to the stopping
time `τ` is the map `x ↦ u (τ ω) ω`. -/
noncomputable
/--
Definition of `stoppedValue` / `stoppedValue` 的定义

English:
definition stoppedValue
  signature: (u : ι -> Ω -> β) (τ : Ω -> WithTop ι)
  body: fun ω => u (τ ω).untopA ω

@[simp]

中文:
定义 stoppedValue
  签名: (u : ι -> Ω -> β) (τ : Ω -> WithTop ι)
  定义体: fun ω => u (τ ω).untopA ω

@[simp]

Depends on / 依赖: untopA
-/
def stoppedValue (u : ι -> Ω -> β) (τ : Ω -> WithTop ι) : Ω -> β := fun ω => u (τ ω).untopA ω

@[simp]
/--
theorem `stoppedValue_const` / 定理 `stoppedValue_const`

English:
theorem stoppedValue_const
  given: (u : ι -> Ω -> β) (i : ι)
  statement: (stoppedValue u fun _ => i) = u i
  proof: rfl

中文:
定理 stoppedValue_const
  条件: (u : ι -> Ω -> β) (i : ι)
  结论: (stoppedValue u fun _ => i) = u i
  证明: rfl
-/
theorem stoppedValue_const (u : ι -> Ω -> β) (i : ι) : (stoppedValue u fun _ => i) = u i := rfl

/--
lemma `stoppedValue_comp` / 引理 `stoppedValue_comp`

English:
lemma stoppedValue_comp
  given: {γ : Type*} (f : β -> γ)
  proof: rfl

中文:
引理 stoppedValue_comp
  条件: {γ : 类型} (f : β -> γ)
  证明: rfl
-/
@[simp] lemma stoppedValue_comp {γ : Type*} (f : β -> γ) :
    stoppedValue (fun t ω => f (u t ω)) τ = fun ω => f (stoppedValue u τ ω) := rfl

/--
lemma `stoppedValue_norm` / 引理 `stoppedValue_norm`

English:
lemma stoppedValue_norm
  given: [SeminormedAddCommGroup β]
  proof: rfl

@[to_additive (attr := simp)]

中文:
引理 stoppedValue_norm
  条件: [SeminormedAddCommGroup β]
  证明: rfl

@[to_additive (attr := simp)]
-/
lemma stoppedValue_norm [SeminormedAddCommGroup β] :
    stoppedValue (fun t ω => ‖u t ω‖) τ = fun ω => ‖stoppedValue u τ ω‖ := rfl

@[to_additive (attr := simp)]
/--
lemma `stoppedValue_inv` / 引理 `stoppedValue_inv`

English:
lemma stoppedValue_inv
  given: [Inv β]
  statement: stoppedValue (u⁻¹) τ = (stoppedValue u τ)⁻¹
  proof: rfl

@[to_additive (attr := simp)]

中文:
引理 stoppedValue_inv
  条件: [Inv β]
  结论: stoppedValue (u⁻¹) τ = (stoppedValue u τ)⁻¹
  证明: rfl

@[to_additive (attr := simp)]
-/
lemma stoppedValue_inv [Inv β] : stoppedValue (u⁻¹) τ = (stoppedValue u τ)⁻¹ := rfl

@[to_additive (attr := simp)]
/--
lemma `stoppedValue_mul` / 引理 `stoppedValue_mul`

English:
lemma stoppedValue_mul
  given: [Mul β]
  proof: rfl

@[to_additive (attr := simp)]

中文:
引理 stoppedValue_mul
  条件: [Mul β]
  证明: rfl

@[to_additive (attr := simp)]
-/
lemma stoppedValue_mul [Mul β] :
    stoppedValue (u * v) τ = stoppedValue u τ * stoppedValue v τ := rfl

@[to_additive (attr := simp)]
/--
lemma `stoppedValue_div` / 引理 `stoppedValue_div`

English:
lemma stoppedValue_div
  given: [Div β]
  proof: rfl

中文:
引理 stoppedValue_div
  条件: [Div β]
  证明: rfl
-/
lemma stoppedValue_div [Div β] :
    stoppedValue (u / v) τ = stoppedValue u τ / stoppedValue v τ := rfl

/--
lemma `stoppedValue_const_smul` / 引理 `stoppedValue_const_smul`

English:
lemma stoppedValue_const_smul
  given: {𝕜 : Type*} [SMul 𝕜 β] (c : 𝕜)
  proof: rfl

中文:
引理 stoppedValue_const_smul
  条件: {𝕜 : 类型} [SMul 𝕜 β] (c : 𝕜)
  证明: rfl
-/
@[simp] lemma stoppedValue_const_smul {𝕜 : Type*} [SMul 𝕜 β] (c : 𝕜) :
    stoppedValue (c • u) τ = c • stoppedValue u τ := rfl

/--
lemma `stoppedValue_const_bot` / 引理 `stoppedValue_const_bot`

English:
lemma stoppedValue_const_bot
  given: [Bot ι]
  proof: by
  ext; simp [stoppedValue, ← WithTop.coe_bot]

中文:
引理 stoppedValue_const_bot
  条件: [Bot ι]
  证明: by
  ext; simp [stoppedValue, ← WithTop.coe_bot]
-/
@[simp] lemma stoppedValue_const_bot [Bot ι] :
    stoppedValue u (fun _ => ⊥) = u ⊥ := by
  ext; simp [stoppedValue, ← WithTop.coe_bot]

variable [LinearOrder ι]

/-- Given a map `u : ι → Ω → E`, the stopped process with respect to `τ` is `u i ω` if
`i ≤ τ ω`, and `u (τ ω) ω` otherwise.

Intuitively, the stopped process stops evolving once the stopping time has occurred. -/
noncomputable
/--
Definition of `stoppedProcess` / `stoppedProcess` 的定义

English:
definition stoppedProcess
  signature: (u : ι -> Ω -> β) (τ : Ω -> WithTop ι)
  body: fun i ω => u (min (i : WithTop ι) (τ ω)).untopA ω

中文:
定义 stoppedProcess
  签名: (u : ι -> Ω -> β) (τ : Ω -> WithTop ι)
  定义体: fun i ω => u (min (i : WithTop ι) (τ ω)).untopA ω

Depends on / 依赖: WithTop, untopA
-/
def stoppedProcess (u : ι -> Ω -> β) (τ : Ω -> WithTop ι) : ι -> Ω -> β :=
  fun i ω => u (min (i : WithTop ι) (τ ω)).untopA ω

/--
theorem `stoppedProcess_eq_stoppedValue` / 定理 `stoppedProcess_eq_stoppedValue`

English:
theorem stoppedProcess_eq_stoppedValue
  proof: rfl

中文:
定理 stoppedProcess_eq_stoppedValue
  证明: rfl
-/
theorem stoppedProcess_eq_stoppedValue :
    stoppedProcess u τ = fun i : ι => stoppedValue u fun ω => min i (τ ω) := rfl

/--
theorem `stoppedProcess_eq_stoppedValue_apply` / 定理 `stoppedProcess_eq_stoppedValue_apply`

English:
theorem stoppedProcess_eq_stoppedValue_apply
  given: (i : ι) (ω : Ω)
  proof: rfl

中文:
定理 stoppedProcess_eq_stoppedValue_apply
  条件: (i : ι) (ω : Ω)
  证明: rfl
-/
theorem stoppedProcess_eq_stoppedValue_apply (i : ι) (ω : Ω) :
    stoppedProcess u τ i ω = stoppedValue u (fun ω => min i (τ ω)) ω := rfl

/--
lemma `stoppedProcess_const` / 引理 `stoppedProcess_const`

English:
lemma stoppedProcess_const
  given: {u₀ : Ω -> β}
  proof: rfl

中文:
引理 stoppedProcess_const
  条件: {u₀ : Ω -> β}
  证明: rfl
-/
@[simp] lemma stoppedProcess_const {u₀ : Ω -> β} :
    stoppedProcess (fun _ => u₀) τ = fun _ => u₀ := rfl

/--
lemma `stoppedProcess_comp` / 引理 `stoppedProcess_comp`

English:
lemma stoppedProcess_comp
  given: {γ : Type*} (f : β -> γ)
  proof: rfl

中文:
引理 stoppedProcess_comp
  条件: {γ : 类型} (f : β -> γ)
  证明: rfl
-/
@[simp] lemma stoppedProcess_comp {γ : Type*} (f : β -> γ) :
    stoppedProcess (fun t ω => f (u t ω)) τ = fun i ω => f (stoppedProcess u τ i ω) := rfl

/--
lemma `stoppedProcess_norm` / 引理 `stoppedProcess_norm`

English:
lemma stoppedProcess_norm
  given: [SeminormedAddCommGroup β]
  proof: rfl

@[to_additive (attr := simp)]

中文:
引理 stoppedProcess_norm
  条件: [SeminormedAddCommGroup β]
  证明: rfl

@[to_additive (attr := simp)]
-/
lemma stoppedProcess_norm [SeminormedAddCommGroup β] :
    stoppedProcess (fun t ω => ‖u t ω‖) τ = fun i ω => ‖stoppedProcess u τ i ω‖ := rfl

@[to_additive (attr := simp)]
/--
lemma `stoppedProcess_inv` / 引理 `stoppedProcess_inv`

English:
lemma stoppedProcess_inv
  given: [Inv β]
  statement: stoppedProcess (u⁻¹) τ = (stoppedProcess u τ)⁻¹
  proof: rfl

@[to_additive (attr := simp)]

中文:
引理 stoppedProcess_inv
  条件: [Inv β]
  结论: stoppedProcess (u⁻¹) τ = (stoppedProcess u τ)⁻¹
  证明: rfl

@[to_additive (attr := simp)]
-/
lemma stoppedProcess_inv [Inv β] : stoppedProcess (u⁻¹) τ = (stoppedProcess u τ)⁻¹ := rfl

@[to_additive (attr := simp)]
/--
lemma `stoppedProcess_mul` / 引理 `stoppedProcess_mul`

English:
lemma stoppedProcess_mul
  given: [Mul β]
  proof: rfl

@[to_additive (attr := simp)]

中文:
引理 stoppedProcess_mul
  条件: [Mul β]
  证明: rfl

@[to_additive (attr := simp)]
-/
lemma stoppedProcess_mul [Mul β] :
    stoppedProcess (u * v) τ = stoppedProcess u τ * stoppedProcess v τ := rfl

@[to_additive (attr := simp)]
/--
lemma `stoppedProcess_div` / 引理 `stoppedProcess_div`

English:
lemma stoppedProcess_div
  given: [Div β]
  proof: rfl

中文:
引理 stoppedProcess_div
  条件: [Div β]
  证明: rfl
-/
lemma stoppedProcess_div [Div β] :
    stoppedProcess (u / v) τ = stoppedProcess u τ / stoppedProcess v τ := rfl

/--
lemma `stoppedProcess_const_smul` / 引理 `stoppedProcess_const_smul`

English:
lemma stoppedProcess_const_smul
  given: {𝕜 : Type*} [SMul 𝕜 β] (c : 𝕜)
  proof: rfl

中文:
引理 stoppedProcess_const_smul
  条件: {𝕜 : 类型} [SMul 𝕜 β] (c : 𝕜)
  证明: rfl
-/
@[simp] lemma stoppedProcess_const_smul {𝕜 : Type*} [SMul 𝕜 β] (c : 𝕜) :
    stoppedProcess (c • u) τ = c • stoppedProcess u τ := rfl

/--
lemma `stoppedProcess_const_bot` / 引理 `stoppedProcess_const_bot`

English:
lemma stoppedProcess_const_bot
  given: [OrderBot ι]
  proof: by
  ext; simp [stoppedProcess, ← WithTop.coe_bot]

中文:
引理 stoppedProcess_const_bot
  条件: [OrderBot ι]
  证明: by
  ext; simp [stoppedProcess, ← WithTop.coe_bot]
-/
@[simp] lemma stoppedProcess_const_bot [OrderBot ι] :
    stoppedProcess u (fun _ => ⊥) = fun _ => u ⊥ := by
  ext; simp [stoppedProcess, ← WithTop.coe_bot]

/--
lemma `stoppedProcess_const_top` / 引理 `stoppedProcess_const_top`

English:
lemma stoppedProcess_const_top
  statement: stoppedProcess u (fun _ => ⊤) = u
  proof: by
  ext; simp [stoppedProcess]

中文:
引理 stoppedProcess_const_top
  结论: stoppedProcess u (fun _ => ⊤) = u
  证明: by
  ext; simp [stoppedProcess]
-/
@[simp] lemma stoppedProcess_const_top : stoppedProcess u (fun _ => ⊤) = u := by
  ext; simp [stoppedProcess]

/--
theorem `stoppedValue_stoppedProcess` / 定理 `stoppedValue_stoppedProcess`

English:
theorem stoppedValue_stoppedProcess
  proof: by
  ext ω
  simp only [stoppedValue, stoppedProcess, ne_eq, ite_not]
  cases σ ω <;> cases τ ω <;> simp

中文:
定理 stoppedValue_stoppedProcess
  证明: by
  ext ω
  simp only [stoppedValue, stoppedProcess, ne_eq, ite_not]
  cases σ ω <;> cases τ ω <;> simp

Depends on / 依赖: ite_not, ne_eq, stoppedProcess, stoppedValue
-/
theorem stoppedValue_stoppedProcess :
    stoppedValue (stoppedProcess u τ) σ =
      fun ω => if σ ω != ⊤ then stoppedValue u (fun ω => min (σ ω) (τ ω)) ω
      else stoppedValue u (fun ω => min (Classical.arbitrary ι) (τ ω)) ω := by
  ext ω
  simp only [stoppedValue, stoppedProcess, ne_eq, ite_not]
  cases σ ω <;> cases τ ω <;> simp

/--
theorem `stoppedValue_stoppedProcess_apply` / 定理 `stoppedValue_stoppedProcess_apply`

English:
theorem stoppedValue_stoppedProcess_apply
  given: {ω : Ω} (hω : σ ω != ⊤)
  proof: by
  simp [stoppedValue_stoppedProcess, hω]

中文:
定理 stoppedValue_stoppedProcess_apply
  条件: {ω : Ω} (hω : σ ω != ⊤)
  证明: by
  simp [stoppedValue_stoppedProcess, hω]

Depends on / 依赖: stoppedValue_stoppedProcess
-/
theorem stoppedValue_stoppedProcess_apply {ω : Ω} (hω : σ ω != ⊤) :
    stoppedValue (stoppedProcess u τ) σ ω = stoppedValue u (fun ω => min (σ ω) (τ ω)) ω := by
  simp [stoppedValue_stoppedProcess, hω]

/--
theorem `stoppedValue_stoppedProcess_ae_eq` / 定理 `stoppedValue_stoppedProcess_ae_eq`

English:
theorem stoppedValue_stoppedProcess_ae_eq
  statement: {μ : Measure Ω}
  proof: by
  filter_upwards [hσ] with ω hσ using by simp [stoppedValue_stoppedProcess, hσ]

中文:
定理 stoppedValue_stoppedProcess_ae_eq
  结论: {μ : Measure Ω}
  证明: by
  filter_upwards [hσ] with ω hσ using by simp [stoppedValue_stoppedProcess, hσ]

Depends on / 依赖: filter_upwards, stoppedValue_stoppedProcess
-/
theorem stoppedValue_stoppedProcess_ae_eq {μ : Measure Ω}
    (hσ : forallᵐ ω ∂μ, σ ω != ⊤) :
    stoppedValue (stoppedProcess u τ) σ =ᵐ[μ] stoppedValue u (fun ω => min (σ ω) (τ ω)) := by
  filter_upwards [hσ] with ω hσ using by simp [stoppedValue_stoppedProcess, hσ]

/--
theorem `stoppedProcess_eq_of_le` / 定理 `stoppedProcess_eq_of_le`

English:
theorem stoppedProcess_eq_of_le
  given: {i : ι} {ω : Ω} (h : i <= τ ω)
  proof: by simp [stoppedProcess, min_eq_left h]

中文:
定理 stoppedProcess_eq_of_le
  条件: {i : ι} {ω : Ω} (h : i <= τ ω)
  证明: by simp [stoppedProcess, min_eq_left h]

Depends on / 依赖: min_eq_left, stoppedProcess
-/
theorem stoppedProcess_eq_of_le {i : ι} {ω : Ω} (h : i <= τ ω) :
    stoppedProcess u τ i ω = u i ω := by simp [stoppedProcess, min_eq_left h]

/--
theorem `stoppedProcess_eq_of_ge` / 定理 `stoppedProcess_eq_of_ge`

English:
theorem stoppedProcess_eq_of_ge
  given: {i : ι} {ω : Ω} (h : τ ω <= i)
  proof: by simp [stoppedProcess, min_eq_right h]

中文:
定理 stoppedProcess_eq_of_ge
  条件: {i : ι} {ω : Ω} (h : τ ω <= i)
  证明: by simp [stoppedProcess, min_eq_right h]

Depends on / 依赖: min_eq_right, stoppedProcess
-/
theorem stoppedProcess_eq_of_ge {i : ι} {ω : Ω} (h : τ ω <= i) :
    stoppedProcess u τ i ω = u (τ ω).untopA ω := by simp [stoppedProcess, min_eq_right h]

/--
lemma `stoppedProcess_indicator_comm` / 引理 `stoppedProcess_indicator_comm`

English:
lemma stoppedProcess_indicator_comm
  given: [Zero β] {s : Set Ω} (i : ι)
  proof: by
  ext ω
  by_cases hω : ω in s <;> simp [stoppedProcess, hω]

中文:
引理 stoppedProcess_indicator_comm
  条件: [Zero β] {s : Set Ω} (i : ι)
  证明: by
  ext ω
  by_cases hω : ω in s <;> simp [stoppedProcess, hω]

Depends on / 依赖: stoppedProcess
-/
lemma stoppedProcess_indicator_comm [Zero β] {s : Set Ω} (i : ι) :
    stoppedProcess (fun i => s.indicator (u i)) τ i = s.indicator (stoppedProcess u τ i) := by
  ext ω
  by_cases hω : ω in s <;> simp [stoppedProcess, hω]

/--
lemma `stoppedProcess_indicator_comm'` / 引理 `stoppedProcess_indicator_comm'`

English:
lemma stoppedProcess_indicator_comm'
  given: [Zero β] {s : Set Ω}
  proof: by
  ext i ω
  rw [stoppedProcess_indicator_comm]

@[simp]

中文:
引理 stoppedProcess_indicator_comm'
  条件: [Zero β] {s : Set Ω}
  证明: by
  ext i ω
  rw [stoppedProcess_indicator_comm]

@[simp]

Depends on / 依赖: stoppedProcess_indicator_comm
-/
lemma stoppedProcess_indicator_comm' [Zero β] {s : Set Ω} :
    stoppedProcess (fun i => s.indicator (u i)) τ = fun i => s.indicator (stoppedProcess u τ i) := by
  ext i ω
  rw [stoppedProcess_indicator_comm]

@[simp]
/--
theorem `stoppedProcess_stoppedProcess` / 定理 `stoppedProcess_stoppedProcess`

English:
theorem stoppedProcess_stoppedProcess
  proof: by
  ext i ω
  simp_rw [stoppedProcess]
  by_cases hτ : τ ω = ⊤
  · simp [hτ]
  by_cases hσ : σ ω = ⊤
  · simp [hσ]
  by_cases hστ : σ ω <= τ ω
  · rw [min_eq_left, untopA_eq_untop coe_ne_top]
    · simp [hστ]
    · refine le_trans ?_ hστ
      simp [untopA_eq_untop]
  · nth_rewrite 2 [untopA_eq_unt

中文:
定理 stoppedProcess_stoppedProcess
  证明: by
  ext i ω
  simp_rw [stoppedProcess]
  by_cases hτ : τ ω = ⊤
  · simp [hτ]
  by_cases hσ : σ ω = ⊤
  · simp [hσ]
  by_cases hστ : σ ω <= τ ω
  · rw [min_eq_left, untopA_eq_untop coe_ne_top]
    · simp [hστ]
    · refine le_trans ?_ hστ
      simp [untopA_eq_untop]
  · nth_rewrite 2 [untopA_eq_unt

Depends on / 依赖: Pi.inf_apply, coe_ne_top, coe_untop, inf_apply, le_trans, lt_of_le_of_lt, lt_top_iff_ne_top, min_assoc, min_eq_left, min_le_right, nth_rewrite, simp_rw, stoppedProcess, untopA_eq_untop
-/
theorem stoppedProcess_stoppedProcess :
    stoppedProcess (stoppedProcess u τ) σ = stoppedProcess u (σ ⊓ τ) := by
  ext i ω
  simp_rw [stoppedProcess]
  by_cases hτ : τ ω = ⊤
  · simp [hτ]
  by_cases hσ : σ ω = ⊤
  · simp [hσ]
  by_cases hστ : σ ω <= τ ω
  · rw [min_eq_left, untopA_eq_untop coe_ne_top]
    · simp [hστ]
    · refine le_trans ?_ hστ
      simp [untopA_eq_untop]
  · nth_rewrite 2 [untopA_eq_untop]
    · rw [coe_untop, min_assoc, Pi.inf_apply]
    · exact (lt_of_le_of_lt (min_le_right _ _) <| lt_top_iff_ne_top.2 hσ).ne

/--
theorem `stoppedProcess_stoppedProcess'` / 定理 `stoppedProcess_stoppedProcess'`

English:
theorem stoppedProcess_stoppedProcess'
  proof: by
  rw [stoppedProcess_stoppedProcess]; rfl

中文:
定理 stoppedProcess_stoppedProcess'
  证明: by
  rw [stoppedProcess_stoppedProcess]; rfl

Depends on / 依赖: stoppedProcess_stoppedProcess
-/
theorem stoppedProcess_stoppedProcess' :
    stoppedProcess (stoppedProcess u τ) σ = stoppedProcess u (fun ω => min (σ ω) (τ ω)) := by
  rw [stoppedProcess_stoppedProcess]; rfl

/--
theorem `stoppedProcess_stoppedProcess_of_le_right` / 定理 `stoppedProcess_stoppedProcess_of_le_right`

English:
theorem stoppedProcess_stoppedProcess_of_le_right
  given: (h : σ <= τ)
  proof: by simp [h]

中文:
定理 stoppedProcess_stoppedProcess_of_le_right
  条件: (h : σ <= τ)
  证明: by simp [h]
-/
theorem stoppedProcess_stoppedProcess_of_le_right (h : σ <= τ) :
    stoppedProcess (stoppedProcess u τ) σ = stoppedProcess u σ := by simp [h]

/--
theorem `stoppedProcess_stoppedProcess_of_le_left` / 定理 `stoppedProcess_stoppedProcess_of_le_left`

English:
theorem stoppedProcess_stoppedProcess_of_le_left
  given: (h : τ <= σ)
  proof: by simp [h]

中文:
定理 stoppedProcess_stoppedProcess_of_le_left
  条件: (h : τ <= σ)
  证明: by simp [h]

Depends on / 依赖: AlgHom, AlgHom.ext, mul_one
-/
theorem stoppedProcess_stoppedProcess_of_le_left (h : τ <= σ) :
    stoppedProcess (stoppedProcess u τ) σ = stoppedProcess u τ := by simp [h]

section Progressive

variable [MeasurableSpace ι] [TopologicalSpace ι] [OrderTopology ι] [SecondCountableTopology ι]
  [BorelSpace ι] [TopologicalSpace β] {f : Filtration ι m}

/--
theorem `isStronglyProgressive_min_stopping_time` / 定理 `isStronglyProgressive_min_stopping_time`

English:
theorem isStronglyProgressive_min_stopping_time
  statement: [PseudoMetrizableSpace ι]
  proof: by
  refine fun i => (Measurable.untopA ?_).stronglyMeasurable
  let m_prod : MeasurableSpace (Set.Iic i × Ω) := Subtype.instMeasurableSpace.prod (f i)
  let m_set : forall t : Set (Set.Iic i × Ω), MeasurableSpace t := fun _ =>
    @Subtype.instMeasurableSpace (Set.Iic i × Ω) _ m_prod
  let s := {p 

中文:
定理 isStronglyProgressive_min_stopping_time
  结论: [PseudoMetrizableSpace ι]
  证明: by
  refine fun i => (Measurable.untopA ?_).stronglyMeasurable
  let m_prod : MeasurableSpace (Set.Iic i × Ω) := Subtype.instMeasurableSpace.prod (f i)
  let m_set : forall t : Set (Set.Iic i × Ω), MeasurableSpace t := fun _ =>
    @Subtype.instMeasurableSpace (Set.Iic i × Ω) _ m_prod
  let s := {p 

Depends on / 依赖: AlgHom, AlgHom.ext, Measurable, Measurable.untopA, MeasurableSet, MeasurableSpace, Set.Iic, Subtype, Subtype.instMeasurableSpace, Subtype.instMeasurableSpace.prod, h_meas_fst, instMeasurableSpace, m_prod, m_set, measurable_snd, one_mul, stronglyMeasurable, untopA
-/
theorem isStronglyProgressive_min_stopping_time [PseudoMetrizableSpace ι]
    (hτ : IsStoppingTime f τ) :
    IsStronglyProgressive f fun i ω => (min (i : WithTop ι) (τ ω)).untopA := by
  refine fun i => (Measurable.untopA ?_).stronglyMeasurable
  let m_prod : MeasurableSpace (Set.Iic i × Ω) := Subtype.instMeasurableSpace.prod (f i)
  let m_set : forall t : Set (Set.Iic i × Ω), MeasurableSpace t := fun _ =>
    @Subtype.instMeasurableSpace (Set.Iic i × Ω) _ m_prod
  let s := {p : Set.Iic i × Ω | τ p.2 <= i}
  have hs : MeasurableSet[m_prod] s := @measurable_snd (Set.Iic i) Ω _ (f i) _ (hτ i)
  have h_meas_fst : forall t : Set (Set.Iic i × Ω),
      Measurable[m_set t] fun x : t => ((x : Set.Iic i × Ω).fst : ι) :=
    fun t => (@measurable_subtype_coe (Set.Iic i × Ω) m_prod _).fst.subtype_val
  refine measurable_of_restrict_of_restrict_compl hs ?_ ?_
  · refine Measurable.min (h_meas_fst s).withTop_coe ?_
    refine measurable_of_Iic fun j => ?_
    cases j with
    | top => simp
    | coe j =>
      have h_set_eq : (fun x : s => τ (x : Set.Iic i × Ω).snd) ⁻¹' Set.Iic j =
          (fun x : s => (x : Set.Iic i × Ω).snd) ⁻¹' {ω | τ ω <= min i j} := by
        ext1 ω
        simp only [Set.mem_preimage, Set.mem_Iic, coe_min, le_inf_iff,
          Set.preimage_ofPred_eq, Set.mem_ofPred_eq, iff_and_self]
        exact fun _ => ω.prop
      rw [h_set_eq]
      suffices h_meas : @Measurable _ _ (m_set s) (f i) fun x : s => (x : Set.Iic i × Ω).snd from
        h_meas (f.mono (min_le_left _ _) _ (hτ.measurableSet_le (min i j)))
      exact measurable_snd.comp (@measurable_subtype_coe _ m_prod _)
  · let sc := sᶜ
    suffices h_min_eq_left :
      (fun x : sc => min (↑(x : Set.Iic i × Ω).fst) (τ (x : Set.Iic i × Ω).snd)) = fun x : sc =>
        ↑(x : Set.Iic i × Ω).fst by
      simp +unfoldPartialApp only [sc, Set.domRestrict, h_min_eq_left]
      exact (h_meas_fst _).withTop_coe
    ext1 ω
    rw [min_eq_left]
    have hx_fst_le : ↑(ω : Set.Iic i × Ω).fst <= i := (ω : Set.Iic i × Ω).fst.prop
    by_cases h : τ (ω : Set.Iic i × Ω).2 = ⊤
    · simp [h]
    · lift τ (ω : Set.Iic i × Ω).2 to ι using h with t ht
      norm_cast
      refine hx_fst_le.trans (le_of_lt ?_)
      convert! ω.prop
      simp only [sc, s, not_le, Set.mem_compl_iff, Set.mem_ofPred_eq, ← ht]
      norm_cast

@[deprecated (since := "2026-04-24")]
alias progMeasurable_min_stopping_time := isStronglyProgressive_min_stopping_time

/--
theorem `IsStronglyProgressive.stoppedProcess` / 定理 `IsStronglyProgressive.stoppedProcess`

English:
theorem IsStronglyProgressive.stoppedProcess
  statement: [PseudoMetrizableSpace ι]
  proof: by
  have h_meas := isStronglyProgressive_min_stopping_time hτ
  refine h.comp h_meas fun i ω => ?_
  cases τ ω with
  | top => simp
  | coe t =>
    rcases le_total i t with h_it | h_ti
    · simp [(mod_cast h_it : (i : WithTop ι) <= t)]
    · simpa [(mod_cast h_ti : t <= (i : WithTop ι))]

@[depre

中文:
定理 IsStronglyProgressive.stoppedProcess
  结论: [PseudoMetrizableSpace ι]
  证明: by
  have h_meas := isStronglyProgressive_min_stopping_time hτ
  refine h.comp h_meas fun i ω => ?_
  cases τ ω with
  | top => simp
  | coe t =>
    rcases le_total i t with h_it | h_ti
    · simp [(mod_cast h_it : (i : WithTop ι) <= t)]
    · simpa [(mod_cast h_ti : t <= (i : WithTop ι))]

@[depre

Depends on / 依赖: WithTop, h.comp, h_it, h_meas, h_ti, isStronglyProgressive_min_stopping_time, le_total, mod_cast
-/
theorem IsStronglyProgressive.stoppedProcess [PseudoMetrizableSpace ι]
    (h : IsStronglyProgressive f u) (hτ : IsStoppingTime f τ) :
    IsStronglyProgressive f (stoppedProcess u τ) := by
  have h_meas := isStronglyProgressive_min_stopping_time hτ
  refine h.comp h_meas fun i ω => ?_
  cases τ ω with
  | top => simp
  | coe t =>
    rcases le_total i t with h_it | h_ti
    · simp [(mod_cast h_it : (i : WithTop ι) <= t)]
    · simpa [(mod_cast h_ti : t <= (i : WithTop ι))]

@[deprecated (since := "2026-04-24")]
alias ProgMeasurable.stoppedProcess := IsStronglyProgressive.stoppedProcess

/--
theorem `IsStronglyProgressive.stronglyAdapted_stoppedProcess` / 定理 `IsStronglyProgressive.stronglyAdapted_stoppedProcess`

English:
theorem IsStronglyProgressive.stronglyAdapted_stoppedProcess
  statement: [PseudoMetrizableSpace ι]
  proof: (h.stoppedProcess hτ).stronglyAdapted

@[deprecated (since := "2026-04-24")]
alias ProgMeasurable.stronglyAdapted_stoppedProcess :=
  IsStronglyProgressive.stronglyAdapted_stoppedProcess

中文:
定理 IsStronglyProgressive.stronglyAdapted_stoppedProcess
  结论: [PseudoMetrizableSpace ι]
  证明: (h.stoppedProcess hτ).stronglyAdapted

@[deprecated (since := "2026-04-24")]
alias ProgMeasurable.stronglyAdapted_stoppedProcess :=
  IsStronglyProgressive.stronglyAdapted_stoppedProcess

Depends on / 依赖: h.stoppedProcess, stoppedProcess, stronglyAdapted
-/
theorem IsStronglyProgressive.stronglyAdapted_stoppedProcess [PseudoMetrizableSpace ι]
    (h : IsStronglyProgressive f u) (hτ : IsStoppingTime f τ) :
    StronglyAdapted f (MeasureTheory.stoppedProcess u τ) :=
  (h.stoppedProcess hτ).stronglyAdapted

@[deprecated (since := "2026-04-24")]
alias ProgMeasurable.stronglyAdapted_stoppedProcess :=
  IsStronglyProgressive.stronglyAdapted_stoppedProcess

/--
theorem `IsStronglyProgressive.stronglyMeasurable_stoppedProcess` / 定理 `IsStronglyProgressive.stronglyMeasurable_stoppedProcess`

English:
theorem IsStronglyProgressive.stronglyMeasurable_stoppedProcess
  statement: [PseudoMetrizableSpace ι]
  proof: (hu.stronglyAdapted_stoppedProcess hτ i).mono (f.le _)

中文:
定理 IsStronglyProgressive.stronglyMeasurable_stoppedProcess
  结论: [PseudoMetrizableSpace ι]
  证明: (hu.stronglyAdapted_stoppedProcess hτ i).mono (f.le _)

Depends on / 依赖: f.le, hu.stronglyAdapted_stoppedProcess, stronglyAdapted_stoppedProcess
-/
theorem IsStronglyProgressive.stronglyMeasurable_stoppedProcess [PseudoMetrizableSpace ι]
    (hu : IsStronglyProgressive f u) (hτ : IsStoppingTime f τ) (i : ι) :
    StronglyMeasurable (MeasureTheory.stoppedProcess u τ i) :=
  (hu.stronglyAdapted_stoppedProcess hτ i).mono (f.le _)

/--
theorem `stronglyMeasurable_stoppedValue_of_le` / 定理 `stronglyMeasurable_stoppedValue_of_le`

English:
theorem stronglyMeasurable_stoppedValue_of_le
  statement: (h : IsStronglyProgressive f u)
  proof: by
  have hτ_le' ω : (τ ω).untopA <= n := untopA_le (hτ_le ω)
  have : stoppedValue u τ =
      (fun p : Set.Iic n × Ω => u (↑p.fst) p.snd) ∘ fun ω => (⟨(τ ω).untopA, hτ_le' ω⟩, ω) := by
    ext1 ω; simp only [stoppedValue, Function.comp_apply]
  rw [this]
  refine StronglyMeasurable.comp_measurable

中文:
定理 stronglyMeasurable_stoppedValue_of_le
  结论: (h : IsStronglyProgressive f u)
  证明: by
  have hτ_le' ω : (τ ω).untopA <= n := untopA_le (hτ_le ω)
  have : stoppedValue u τ =
      (fun p : Set.Iic n × Ω => u (↑p.fst) p.snd) ∘ fun ω => (⟨(τ ω).untopA, hτ_le' ω⟩, ω) := by
    ext1 ω; simp only [stoppedValue, Function.comp_apply]
  rw [this]
  refine StronglyMeasurable.comp_measurable

Depends on / 依赖: Function, Function.comp_apply, Measurable, Measurable.subtype_mk, Set.Iic, StronglyMeasurable, StronglyMeasurable.comp_measurable, comp_apply, comp_measurable, measurable_id, measurable_of_le, p.fst, p.snd, prodMk, stoppedValue, subtype_mk, untopA, untopA_le
-/
theorem stronglyMeasurable_stoppedValue_of_le (h : IsStronglyProgressive f u)
    (hτ : IsStoppingTime f τ) {n : ι} (hτ_le : forall ω, τ ω <= n) :
    StronglyMeasurable[f n] (stoppedValue u τ) := by
  have hτ_le' ω : (τ ω).untopA <= n := untopA_le (hτ_le ω)
  have : stoppedValue u τ =
      (fun p : Set.Iic n × Ω => u (↑p.fst) p.snd) ∘ fun ω => (⟨(τ ω).untopA, hτ_le' ω⟩, ω) := by
    ext1 ω; simp only [stoppedValue, Function.comp_apply]
  rw [this]
  refine StronglyMeasurable.comp_measurable (h n) ?_
  refine (Measurable.subtype_mk ?_).prodMk measurable_id
  exact (hτ.measurable_of_le hτ_le).untopA

/--
lemma `measurableSet_preimage_stoppedValue_inter` / 引理 `measurableSet_preimage_stoppedValue_inter`

English:
lemma measurableSet_preimage_stoppedValue_inter
  statement: [PseudoMetrizableSpace β] [MeasurableSpace β]
  proof: by
  have h_str_meas : forall i, StronglyMeasurable[f i] (stoppedValue u fun ω => min (τ ω) i) := fun i =>
    stronglyMeasurable_stoppedValue_of_le hf_prog (hτ.min_const i) fun _ => min_le_right _ _
  suffices stoppedValue u τ ⁻¹' t inter {ω : Ω | τ ω <= i} =
      (stoppedValue u fun ω => min (τ ω

中文:
引理 measurableSet_preimage_stoppedValue_inter
  结论: [PseudoMetrizableSpace β] [MeasurableSpace β]
  证明: by
  have h_str_meas : forall i, StronglyMeasurable[f i] (stoppedValue u fun ω => min (τ ω) i) := fun i =>
    stronglyMeasurable_stoppedValue_of_le hf_prog (hτ.min_const i) fun _ => min_le_right _ _
  suffices stoppedValue u τ ⁻¹' t inter {ω : Ω | τ ω <= i} =
      (stoppedValue u fun ω => min (τ ω

Depends on / 依赖: Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_preimage, StronglyMeasurable, and_congr, h_str_meas, hf_prog, measurable, measurableSet_le, mem_inter_iff, mem_ofPred_eq, mem_preimage, min_const, min_le_right, stoppedValue, stronglyMeasurable_stoppedValue_of_le
-/
lemma measurableSet_preimage_stoppedValue_inter [PseudoMetrizableSpace β] [MeasurableSpace β]
    [BorelSpace β]
    (hf_prog : IsStronglyProgressive f u) (hτ : IsStoppingTime f τ)
    {t : Set β} (ht : MeasurableSet t) (i : ι) :
    MeasurableSet[f i] (stoppedValue u τ ⁻¹' t inter {ω | τ ω <= i}) := by
  have h_str_meas : forall i, StronglyMeasurable[f i] (stoppedValue u fun ω => min (τ ω) i) := fun i =>
    stronglyMeasurable_stoppedValue_of_le hf_prog (hτ.min_const i) fun _ => min_le_right _ _
  suffices stoppedValue u τ ⁻¹' t inter {ω : Ω | τ ω <= i} =
      (stoppedValue u fun ω => min (τ ω) i) ⁻¹' t inter {ω : Ω | τ ω <= i} by
    rw [this]; exact ((h_str_meas i).measurable ht).inter (hτ.measurableSet_le i)
  ext1 ω
  simp only [stoppedValue, Set.mem_inter_iff, Set.mem_preimage, Set.mem_ofPred_eq,
    and_congr_left_iff]
  intro h
  rw [min_eq_left h]

/--
theorem `measurable_stoppedValue` / 定理 `measurable_stoppedValue`

English:
theorem measurable_stoppedValue
  statement: [PseudoMetrizableSpace β] [MeasurableSpace β] [BorelSpace β]
  proof: by
  have h_str_meas : forall i, StronglyMeasurable[f i] (stoppedValue u fun ω => min (τ ω) i) := fun i =>
    stronglyMeasurable_stoppedValue_of_le hf_prog (hτ.min_const i) fun _ => min_le_right _ _
  intro t ht
  refine ⟨?_, fun i => measurableSet_preimage_stoppedValue_inter hf_prog hτ ht i⟩
  obt

中文:
定理 measurable_stoppedValue
  结论: [PseudoMetrizableSpace β] [MeasurableSpace β] [BorelSpace β]
  证明: by
  have h_str_meas : forall i, StronglyMeasurable[f i] (stoppedValue u fun ω => min (τ ω) i) := fun i =>
    stronglyMeasurable_stoppedValue_of_le hf_prog (hτ.min_const i) fun _ => min_le_right _ _
  intro t ht
  refine ⟨?_, fun i => measurableSet_preimage_stoppedValue_inter hf_prog hτ ht i⟩
  obt

Depends on / 依赖: Filter, StronglyMeasurable, exists_seq_tendsto, h_seq_tendsto, h_str_meas, hf_prog, measurableSet_preimage_stoppedValue_inter, min_const, min_le_right, stoppedValue, stronglyMeasurable_stoppedValue_of_le
-/
theorem measurable_stoppedValue [PseudoMetrizableSpace β] [MeasurableSpace β] [BorelSpace β]
    (hf_prog : IsStronglyProgressive f u) (hτ : IsStoppingTime f τ) :
    Measurable[hτ.measurableSpace] (stoppedValue u τ) := by
  have h_str_meas : forall i, StronglyMeasurable[f i] (stoppedValue u fun ω => min (τ ω) i) := fun i =>
    stronglyMeasurable_stoppedValue_of_le hf_prog (hτ.min_const i) fun _ => min_le_right _ _
  intro t ht
  refine ⟨?_, fun i => measurableSet_preimage_stoppedValue_inter hf_prog hτ ht i⟩
  obtain ⟨seq : Nat -> ι, h_seq_tendsto⟩ := (atTop : Filter ι).exists_seq_tendsto
  have : stoppedValue u τ ⁻¹' t
      = (⋃ n, stoppedValue u τ ⁻¹' t inter {ω | τ ω <= seq n})
        union (stoppedValue u τ ⁻¹' t inter {ω | τ ω = ⊤}) := by
    ext1 ω
    simp only [Set.mem_preimage, Set.mem_union, Set.mem_iUnion, Set.mem_inter_iff,
      Set.mem_ofPred_eq, exists_and_left]
    rw [← and_or_left]; rw [iff_self_and]
    intro _
    by_cases h : τ ω = ⊤
    · exact .inr h
    · lift τ ω to ι using h with t
      simp only [coe_le_coe, coe_ne_top, or_false]
      rw [tendsto_atTop] at h_seq_tendsto
      exact (h_seq_tendsto t).exists
  rw [this]
  refine MeasurableSet.union ?_ ?_
  · exact MeasurableSet.iUnion fun i => le_iSup f (seq i) _
      (measurableSet_preimage_stoppedValue_inter hf_prog hτ ht (seq i))
  · have : stoppedValue u τ ⁻¹' t inter {ω | τ ω = ⊤}
       = (fun ω => u (Classical.arbitrary ι) ω) ⁻¹' t inter {ω | τ ω = ⊤} := by
      ext ω
      simp only [Set.mem_inter_iff, Set.mem_preimage, stoppedValue, untopA,
        Set.mem_ofPred_eq, and_congr_left_iff]
      intro h
      simp [h]
    rw [this]
    refine MeasurableSet.inter (ht.preimage ?_) hτ.measurableSet_eq_top'
    exact (hf_prog.stronglyAdapted (Classical.arbitrary ι)).measurable.mono
      (le_iSup f (Classical.arbitrary ι)) le_rfl

end Progressive

end LinearOrder

section StoppedValueOfMemFinset

variable [Nonempty ι] {μ : Measure Ω} {τ : Ω -> WithTop ι} {E : Type*} {p : Real>=0∞} {u : ι -> Ω -> E}

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `stoppedValue_eq_of_mem_finset` / 定理 `stoppedValue_eq_of_mem_finset`

English:
theorem stoppedValue_eq_of_mem_finset
  statement: [AddCommMonoid E] {s : Finset ι}
  proof: by
  ext y
  classical
  rw [stoppedValue]; rw [Finset.sum_apply]; rw [Finset.sum_indicator_eq_sum_filter]
  suffices {i in s | y in {ω : Ω | τ ω = (i : ι)}} = ({(τ y).untopA} : Finset ι) by
    rw [this]; rw [Finset.sum_singleton]
  ext1 ω
  simp only [Set.mem_ofPred_eq, Finset.mem_filter, Finset.m

中文:
定理 stoppedValue_eq_of_mem_finset
  结论: [AddCommMonoid E] {s : Finset ι}
  证明: by
  ext y
  classical
  rw [stoppedValue]; rw [Finset.sum_apply]; rw [Finset.sum_indicator_eq_sum_filter]
  suffices {i in s | y in {ω : Ω | τ ω = (i : ι)}} = ({(τ y).untopA} : Finset ι) by
    rw [this]; rw [Finset.sum_singleton]
  ext1 ω
  simp only [Set.mem_ofPred_eq, Finset.mem_filter, Finset.m

Depends on / 依赖: Finset, Finset.mem_filter, Finset.mem_singleton, Finset.sum_apply, Finset.sum_indicator_eq_sum_filter, Finset.sum_singleton, Set.mem_ofPred_eq, classical, h_contra, mem_filter, mem_ofPred_eq, mem_singleton, specialize, stoppedValue, sum_apply, sum_indicator_eq_sum_filter, sum_singleton, untopA
-/
theorem stoppedValue_eq_of_mem_finset [AddCommMonoid E] {s : Finset ι}
   (hbdd : forall ω, τ ω in (WithTop.some '' s)) :
    stoppedValue u τ = ∑ i in s, Set.indicator {ω | τ ω = i} (u i) := by
  ext y
  classical
  rw [stoppedValue]; rw [Finset.sum_apply]; rw [Finset.sum_indicator_eq_sum_filter]
  suffices {i in s | y in {ω : Ω | τ ω = (i : ι)}} = ({(τ y).untopA} : Finset ι) by
    rw [this]; rw [Finset.sum_singleton]
  ext1 ω
  simp only [Set.mem_ofPred_eq, Finset.mem_filter, Finset.mem_singleton]
  constructor <;> intro h
  · simp [h.2]
  · simp only [h]
    specialize hbdd y
    have : τ y != ⊤ := fun h_contra => by simp [h_contra] at hbdd
    lift τ y to ι using this with i hi
    simpa using hbdd

/--
theorem `stoppedValue_eq'` / 定理 `stoppedValue_eq'`

English:
theorem stoppedValue_eq'
  statement: [Preorder ι] [LocallyFiniteOrderBot ι] [AddCommMonoid E] {N : ι}
  proof: by
  refine stoppedValue_eq_of_mem_finset fun ω => ?_
  simp only [Finset.coe_Iic, Set.mem_image]
  specialize hbdd ω
  have h_top : τ ω != ⊤ := fun h_contra => by simp [h_contra] at hbdd
  lift τ ω to ι using h_top with i hi
  exact ⟨i, mod_cast hbdd, rfl⟩

中文:
定理 stoppedValue_eq'
  结论: [Preorder ι] [LocallyFiniteOrderBot ι] [AddCommMonoid E] {N : ι}
  证明: by
  refine stoppedValue_eq_of_mem_finset fun ω => ?_
  simp only [Finset.coe_Iic, Set.mem_image]
  specialize hbdd ω
  have h_top : τ ω != ⊤ := fun h_contra => by simp [h_contra] at hbdd
  lift τ ω to ι using h_top with i hi
  exact ⟨i, mod_cast hbdd, rfl⟩

Depends on / 依赖: Finset, Finset.coe_Iic, Set.mem_image, coe_Iic, h_contra, h_top, mem_image, mod_cast, specialize, stoppedValue_eq_of_mem_finset
-/
theorem stoppedValue_eq' [Preorder ι] [LocallyFiniteOrderBot ι] [AddCommMonoid E] {N : ι}
    (hbdd : forall ω, τ ω <= N) :
    stoppedValue u τ = ∑ i in Finset.Iic N, Set.indicator {ω | τ ω = i} (u i) := by
  refine stoppedValue_eq_of_mem_finset fun ω => ?_
  simp only [Finset.coe_Iic, Set.mem_image]
  specialize hbdd ω
  have h_top : τ ω != ⊤ := fun h_contra => by simp [h_contra] at hbdd
  lift τ ω to ι using h_top with i hi
  exact ⟨i, mod_cast hbdd, rfl⟩

/--
theorem `stoppedProcess_eq_of_mem_finset` / 定理 `stoppedProcess_eq_of_mem_finset`

English:
theorem stoppedProcess_eq_of_mem_finset
  statement: [LinearOrder ι] [AddCommMonoid E] {s : Finset ι} (n : ι)
  proof: by
  ext ω
  rw [Pi.add_apply]; rw [Finset.sum_apply]
  rcases le_or_gt (n : WithTop ι) (τ ω) with h | h
  · rw [stoppedProcess_eq_of_le h, Set.indicator_of_mem, Finset.sum_eq_zero, add_zero]
    · intro m hm
      refine Set.indicator_of_notMem ?_ _
      rw [Finset.mem_filter] at hm
      simp onl

中文:
定理 stoppedProcess_eq_of_mem_finset
  结论: [LinearOrder ι] [AddCommMonoid E] {s : Finset ι} (n : ι)
  证明: by
  ext ω
  rw [Pi.add_apply]; rw [Finset.sum_apply]
  rcases le_or_gt (n : WithTop ι) (τ ω) with h | h
  · rw [stoppedProcess_eq_of_le h, Set.indicator_of_mem, Finset.sum_eq_zero, add_zero]
    · intro m hm
      refine Set.indicator_of_notMem ?_ _
      rw [Finset.mem_filter] at hm
      simp onl

Depends on / 依赖: Finset, Finset.mem_filter, Finset.sum_apply, Finset.sum_eq_zero, Pi.add_apply, Set.indicator_of_mem, Set.indicator_of_notMem, Set.mem_ofPred_eq, WithTop, add_apply, add_zero, h_contra, h_top, indicator_of_mem, indicator_of_notMem, le_of_lt, le_or_gt, lt_of_lt_of_le, mem_filter, mem_ofPred_eq
-/
theorem stoppedProcess_eq_of_mem_finset [LinearOrder ι] [AddCommMonoid E] {s : Finset ι} (n : ι)
    (hbdd : forall ω, τ ω < n -> τ ω in WithTop.some '' s) :
    stoppedProcess u τ n = Set.indicator {a | n <= τ a} (u n) +
      ∑ i in s with i < n, Set.indicator {ω | τ ω = i} (u i) := by
  ext ω
  rw [Pi.add_apply]; rw [Finset.sum_apply]
  rcases le_or_gt (n : WithTop ι) (τ ω) with h | h
  · rw [stoppedProcess_eq_of_le h, Set.indicator_of_mem, Finset.sum_eq_zero, add_zero]
    · intro m hm
      refine Set.indicator_of_notMem ?_ _
      rw [Finset.mem_filter] at hm
      simp only [Set.mem_ofPred_eq]
      refine (lt_of_lt_of_le ?_ h).ne'
      exact mod_cast hm.2
    · exact h
  · rw [stoppedProcess_eq_of_ge (le_of_lt h)]
    have h_top : τ ω != ⊤ := fun h_contra => by simp [h_contra] at h
    specialize hbdd ω h
    lift τ ω to ι using h_top with i hi
    rw [Finset.sum_eq_single_of_mem i]
    · simp only [untopD_coe]
      rw [Set.indicator_of_notMem]; rw [zero_add]; rw [Set.indicator_of_mem] <;> rw [Set.mem_ofPred]
      · exact hi.symm
      · rw [← hi]
        exact not_le.2 h
    · rw [Finset.mem_filter]
      simp only [Set.mem_image, Finset.mem_coe, coe_eq_coe, exists_eq_right] at hbdd
      exact ⟨hbdd, mod_cast h⟩
    · intro b _ hneq
      rw [Set.indicator_of_notMem]
      rw [Set.mem_ofPred]; rw [← hi]
      exact mod_cast hneq.symm

/--
theorem `stoppedProcess_eq''` / 定理 `stoppedProcess_eq''`

English:
theorem stoppedProcess_eq''
  given: [LinearOrder ι] [LocallyFiniteOrderBot ι] [AddCommMonoid E] (n : ι)
  proof: by
  have h_mem : forall ω, τ ω < n -> τ ω in WithTop.some '' (Finset.Iio n) := by
    intro ω h
    simp only [Finset.coe_Iio, Set.mem_image, Set.mem_Iio]
    have h_top : τ ω != ⊤ := fun h_contra => by simp [h_contra] at h
    lift τ ω to ι using h_top with i hi
    exact ⟨i, mod_cast h, rfl⟩
  rw

中文:
定理 stoppedProcess_eq''
  条件: [LinearOrder ι] [LocallyFiniteOrderBot ι] [AddCommMonoid E] (n : ι)
  证明: by
  have h_mem : forall ω, τ ω < n -> τ ω in WithTop.some '' (Finset.Iio n) := by
    intro ω h
    simp only [Finset.coe_Iio, Set.mem_image, Set.mem_Iio]
    have h_top : τ ω != ⊤ := fun h_contra => by simp [h_contra] at h
    lift τ ω to ι using h_top with i hi
    exact ⟨i, mod_cast h, rfl⟩
  rw

Depends on / 依赖: Finset, Finset.Iio, Finset.coe_Iio, Set.mem_Iio, Set.mem_image, WithTop, WithTop.some, coe_Iio, h_contra, h_mem, h_top, mem_Iio, mem_image, mod_cast, stoppedProcess_eq_of_mem_finset
-/
theorem stoppedProcess_eq'' [LinearOrder ι] [LocallyFiniteOrderBot ι] [AddCommMonoid E] (n : ι) :
    stoppedProcess u τ n = Set.indicator {a | n <= τ a} (u n) +
      ∑ i in Finset.Iio n, Set.indicator {ω | τ ω = i} (u i) := by
  have h_mem : forall ω, τ ω < n -> τ ω in WithTop.some '' (Finset.Iio n) := by
    intro ω h
    simp only [Finset.coe_Iio, Set.mem_image, Set.mem_Iio]
    have h_top : τ ω != ⊤ := fun h_contra => by simp [h_contra] at h
    lift τ ω to ι using h_top with i hi
    exact ⟨i, mod_cast h, rfl⟩
  rw [stoppedProcess_eq_of_mem_finset n h_mem]
  congr with i
  simp

section StoppedValue

variable [PartialOrder ι] {ℱ : Filtration ι m} [NormedAddCommGroup E]

/--
theorem `memLp_stoppedValue_of_mem_finset` / 定理 `memLp_stoppedValue_of_mem_finset`

English:
theorem memLp_stoppedValue_of_mem_finset
  statement: (hτ : IsStoppingTime ℱ τ) (hu : forall n, MemLp (u n) p μ)
  proof: by
  rw [stoppedValue_eq_of_mem_finset hbdd]
  refine memLp_finsetSum' _ fun i _ => MemLp.indicator ?_ (hu i)
  refine ℱ.le i {a : Ω | τ a = i} (hτ.measurableSet_eq_of_countable_range ?_ i)
  have : Set.range τ subseteq WithTop.some '' s := by
    rintro x ⟨y, rfl⟩
    exact hbdd y
.countable exact 

中文:
定理 memLp_stoppedValue_of_mem_finset
  结论: (hτ : IsStoppingTime ℱ τ) (hu : 对任意 n, MemLp (u n) p μ)
  证明: by
  rw [stoppedValue_eq_of_mem_finset hbdd]
  refine memLp_finsetSum' _ fun i _ => MemLp.indicator ?_ (hu i)
  refine ℱ.le i {a : Ω | τ a = i} (hτ.measurableSet_eq_of_countable_range ?_ i)
  have : Set.range τ subseteq WithTop.some '' s := by
    rintro x ⟨y, rfl⟩
    exact hbdd y
.countable exact 

Depends on / 依赖: Finset, Finset.finite_toSet, MemLp.indicator, Set.range, WithTop, WithTop.some, countable, finite_toSet, indicator, measurableSet_eq_of_countable_range, memLp_finsetSum, stoppedValue_eq_of_mem_finset, subset, subseteq
-/
theorem memLp_stoppedValue_of_mem_finset (hτ : IsStoppingTime ℱ τ) (hu : forall n, MemLp (u n) p μ)
    {s : Finset ι} (hbdd : forall ω, τ ω in WithTop.some '' s) :
    MemLp (stoppedValue u τ) p μ := by
  rw [stoppedValue_eq_of_mem_finset hbdd]
  refine memLp_finsetSum' _ fun i _ => MemLp.indicator ?_ (hu i)
  refine ℱ.le i {a : Ω | τ a = i} (hτ.measurableSet_eq_of_countable_range ?_ i)
  have : Set.range τ subseteq WithTop.some '' s := by
    rintro x ⟨y, rfl⟩
    exact hbdd y
.countable exact ((Finset.finite_toSet s).image _).subset this

/--
theorem `memLp_stoppedValue` / 定理 `memLp_stoppedValue`

English:
theorem memLp_stoppedValue
  statement: [LocallyFiniteOrderBot ι] (hτ : IsStoppingTime ℱ τ)
  proof: by
  refine memLp_stoppedValue_of_mem_finset hτ hu (s := Finset.Iic N) fun ω => ?_
  simp only [Finset.coe_Iic, Set.mem_image, Set.mem_Iic]
  specialize hbdd ω
  have h_top : τ ω != ⊤ := fun h_contra => by simp [h_contra] at hbdd
  lift τ ω to ι using h_top with i hi
  exact ⟨i, mod_cast hbdd, rfl⟩

中文:
定理 memLp_stoppedValue
  结论: [LocallyFiniteOrderBot ι] (hτ : IsStoppingTime ℱ τ)
  证明: by
  refine memLp_stoppedValue_of_mem_finset hτ hu (s := Finset.Iic N) fun ω => ?_
  simp only [Finset.coe_Iic, Set.mem_image, Set.mem_Iic]
  specialize hbdd ω
  have h_top : τ ω != ⊤ := fun h_contra => by simp [h_contra] at hbdd
  lift τ ω to ι using h_top with i hi
  exact ⟨i, mod_cast hbdd, rfl⟩

Depends on / 依赖: Finset, Finset.Iic, Finset.coe_Iic, Set.mem_Iic, Set.mem_image, coe_Iic, h_contra, h_top, memLp_stoppedValue_of_mem_finset, mem_Iic, mem_image, mod_cast, specialize
-/
theorem memLp_stoppedValue [LocallyFiniteOrderBot ι] (hτ : IsStoppingTime ℱ τ)
    (hu : forall n, MemLp (u n) p μ) {N : ι} (hbdd : forall ω, τ ω <= N) : MemLp (stoppedValue u τ) p μ := by
  refine memLp_stoppedValue_of_mem_finset hτ hu (s := Finset.Iic N) fun ω => ?_
  simp only [Finset.coe_Iic, Set.mem_image, Set.mem_Iic]
  specialize hbdd ω
  have h_top : τ ω != ⊤ := fun h_contra => by simp [h_contra] at hbdd
  lift τ ω to ι using h_top with i hi
  exact ⟨i, mod_cast hbdd, rfl⟩

/--
theorem `integrable_stoppedValue_of_mem_finset` / 定理 `integrable_stoppedValue_of_mem_finset`

English:
theorem integrable_stoppedValue_of_mem_finset
  statement: (hτ : IsStoppingTime ℱ τ)
  proof: by
  simp_rw [← memLp_one_iff_integrable] at hu ⊢
  exact memLp_stoppedValue_of_mem_finset hτ hu hbdd

中文:
定理 integrable_stoppedValue_of_mem_finset
  结论: (hτ : IsStoppingTime ℱ τ)
  证明: by
  simp_rw [← memLp_one_iff_integrable] at hu ⊢
  exact memLp_stoppedValue_of_mem_finset hτ hu hbdd

Depends on / 依赖: memLp_one_iff_integrable, memLp_stoppedValue_of_mem_finset, simp_rw
-/
theorem integrable_stoppedValue_of_mem_finset (hτ : IsStoppingTime ℱ τ)
    (hu : forall n, Integrable (u n) μ) {s : Finset ι} (hbdd : forall ω, τ ω in WithTop.some '' s) :
    Integrable (stoppedValue u τ) μ := by
  simp_rw [← memLp_one_iff_integrable] at hu ⊢
  exact memLp_stoppedValue_of_mem_finset hτ hu hbdd

variable (ι)

/--
theorem `integrable_stoppedValue` / 定理 `integrable_stoppedValue`

English:
theorem integrable_stoppedValue
  statement: [LocallyFiniteOrderBot ι] (hτ : IsStoppingTime ℱ τ)
  proof: by
  refine integrable_stoppedValue_of_mem_finset hτ hu (s := Finset.Iic N) fun ω => ?_
  simp only [Finset.coe_Iic, Set.mem_image, Set.mem_Iic]
  specialize hbdd ω
  have h_top : τ ω != ⊤ := fun h_contra => by simp [h_contra] at hbdd
  lift τ ω to ι using h_top with i hi
  exact ⟨i, mod_cast hbdd, 

中文:
定理 integrable_stoppedValue
  结论: [LocallyFiniteOrderBot ι] (hτ : IsStoppingTime ℱ τ)
  证明: by
  refine integrable_stoppedValue_of_mem_finset hτ hu (s := Finset.Iic N) fun ω => ?_
  simp only [Finset.coe_Iic, Set.mem_image, Set.mem_Iic]
  specialize hbdd ω
  have h_top : τ ω != ⊤ := fun h_contra => by simp [h_contra] at hbdd
  lift τ ω to ι using h_top with i hi
  exact ⟨i, mod_cast hbdd, 

Depends on / 依赖: Algebra, Algebra.TensorProduct.lmulEquiv, CompatibleSMul, Finset, Finset.Iic, Finset.coe_Iic, Set.mem_Iic, Set.mem_image, TensorProduct, TensorProduct.CompatibleSMul, bijective, coe_Iic, h_contra, h_top, integrable_stoppedValue_of_mem_finset, lmulEquiv, mem_Iic, mem_image, mod_cast, of_algebraMap_surjective
-/
theorem integrable_stoppedValue [LocallyFiniteOrderBot ι] (hτ : IsStoppingTime ℱ τ)
    (hu : forall n, Integrable (u n) μ) {N : ι} (hbdd : forall ω, τ ω <= N) :
    Integrable (stoppedValue u τ) μ := by
  refine integrable_stoppedValue_of_mem_finset hτ hu (s := Finset.Iic N) fun ω => ?_
  simp only [Finset.coe_Iic, Set.mem_image, Set.mem_Iic]
  specialize hbdd ω
  have h_top : τ ω != ⊤ := fun h_contra => by simp [h_contra] at hbdd
  lift τ ω to ι using h_top with i hi
  exact ⟨i, mod_cast hbdd, rfl⟩

end StoppedValue

section StoppedProcess

variable [LinearOrder ι] [TopologicalSpace ι] [OrderTopology ι] [FirstCountableTopology ι]
  {ℱ : Filtration ι m} [NormedAddCommGroup E]

/--
theorem `memLp_stoppedProcess_of_mem_finset` / 定理 `memLp_stoppedProcess_of_mem_finset`

English:
theorem memLp_stoppedProcess_of_mem_finset
  statement: (hτ : IsStoppingTime ℱ τ) (hu : forall n, MemLp (u n) p μ)
  proof: by
  rw [stoppedProcess_eq_of_mem_finset n hbdd]
  refine MemLp.add ?_ ?_
  · exact MemLp.indicator (ℱ.le n {a : Ω | n <= τ a} (hτ.measurableSet_ge n)) (hu n)
  · suffices MemLp (fun ω => ∑ i in s with i < n, {a : Ω | τ a = i}.indicator (u i) ω) p μ by
      convert! this using 1; ext1 ω; simp only 

中文:
定理 memLp_stoppedProcess_of_mem_finset
  结论: (hτ : IsStoppingTime ℱ τ) (hu : 对任意 n, MemLp (u n) p μ)
  证明: by
  rw [stoppedProcess_eq_of_mem_finset n hbdd]
  refine MemLp.add ?_ ?_
  · exact MemLp.indicator (ℱ.le n {a : Ω | n <= τ a} (hτ.measurableSet_ge n)) (hu n)
  · suffices MemLp (fun ω => ∑ i in s with i < n, {a : Ω | τ a = i}.indicator (u i) ω) p μ by
      convert! this using 1; ext1 ω; simp only 

Depends on / 依赖: Finset, Finset.sum_apply, MemLp.add, MemLp.indicator, convert, indicator, measurableSet_eq, measurableSet_ge, memLp_finsetSum, stoppedProcess_eq_of_mem_finset, sum_apply
-/
theorem memLp_stoppedProcess_of_mem_finset (hτ : IsStoppingTime ℱ τ) (hu : forall n, MemLp (u n) p μ)
    (n : ι) {s : Finset ι} (hbdd : forall ω, τ ω < n -> τ ω in WithTop.some '' s) :
    MemLp (stoppedProcess u τ n) p μ := by
  rw [stoppedProcess_eq_of_mem_finset n hbdd]
  refine MemLp.add ?_ ?_
  · exact MemLp.indicator (ℱ.le n {a : Ω | n <= τ a} (hτ.measurableSet_ge n)) (hu n)
  · suffices MemLp (fun ω => ∑ i in s with i < n, {a : Ω | τ a = i}.indicator (u i) ω) p μ by
      convert! this using 1; ext1 ω; simp only [Finset.sum_apply]
    refine memLp_finsetSum _ fun i _ => MemLp.indicator ?_ (hu i)
    exact ℱ.le i {a : Ω | τ a = i} (hτ.measurableSet_eq i)

/--
theorem `memLp_stoppedProcess` / 定理 `memLp_stoppedProcess`

English:
theorem memLp_stoppedProcess
  statement: [LocallyFiniteOrderBot ι] (hτ : IsStoppingTime ℱ τ)
  proof: by
  refine memLp_stoppedProcess_of_mem_finset hτ hu n (s := Finset.Iic n) fun ω h => ?_
  simp only [Finset.coe_Iic, Set.mem_image, Set.mem_Iic]
  have h_top : τ ω != ⊤ := fun h_contra => by simp [h_contra] at h
  lift τ ω to ι using h_top with i hi
  exact ⟨i, mod_cast h.le, rfl⟩

中文:
定理 memLp_stoppedProcess
  结论: [LocallyFiniteOrderBot ι] (hτ : IsStoppingTime ℱ τ)
  证明: by
  refine memLp_stoppedProcess_of_mem_finset hτ hu n (s := Finset.Iic n) fun ω h => ?_
  simp only [Finset.coe_Iic, Set.mem_image, Set.mem_Iic]
  have h_top : τ ω != ⊤ := fun h_contra => by simp [h_contra] at h
  lift τ ω to ι using h_top with i hi
  exact ⟨i, mod_cast h.le, rfl⟩

Depends on / 依赖: Finset, Finset.Iic, Finset.coe_Iic, Set.mem_Iic, Set.mem_image, coe_Iic, h.le, h_contra, h_top, memLp_stoppedProcess_of_mem_finset, mem_Iic, mem_image, mod_cast
-/
theorem memLp_stoppedProcess [LocallyFiniteOrderBot ι] (hτ : IsStoppingTime ℱ τ)
    (hu : forall n, MemLp (u n) p μ) (n : ι) :
    MemLp (stoppedProcess u τ n) p μ := by
  refine memLp_stoppedProcess_of_mem_finset hτ hu n (s := Finset.Iic n) fun ω h => ?_
  simp only [Finset.coe_Iic, Set.mem_image, Set.mem_Iic]
  have h_top : τ ω != ⊤ := fun h_contra => by simp [h_contra] at h
  lift τ ω to ι using h_top with i hi
  exact ⟨i, mod_cast h.le, rfl⟩

/--
theorem `integrable_stoppedProcess_of_mem_finset` / 定理 `integrable_stoppedProcess_of_mem_finset`

English:
theorem integrable_stoppedProcess_of_mem_finset
  statement: (hτ : IsStoppingTime ℱ τ)
  proof: by
  simp_rw [← memLp_one_iff_integrable] at hu ⊢
  exact memLp_stoppedProcess_of_mem_finset hτ hu n hbdd

中文:
定理 integrable_stoppedProcess_of_mem_finset
  结论: (hτ : IsStoppingTime ℱ τ)
  证明: by
  simp_rw [← memLp_one_iff_integrable] at hu ⊢
  exact memLp_stoppedProcess_of_mem_finset hτ hu n hbdd

Depends on / 依赖: memLp_one_iff_integrable, memLp_stoppedProcess_of_mem_finset, simp_rw
-/
theorem integrable_stoppedProcess_of_mem_finset (hτ : IsStoppingTime ℱ τ)
    (hu : forall n, Integrable (u n) μ) (n : ι) {s : Finset ι}
    (hbdd : forall ω, τ ω < n -> τ ω in WithTop.some '' s) :
    Integrable (stoppedProcess u τ n) μ := by
  simp_rw [← memLp_one_iff_integrable] at hu ⊢
  exact memLp_stoppedProcess_of_mem_finset hτ hu n hbdd

/--
theorem `integrable_stoppedProcess` / 定理 `integrable_stoppedProcess`

English:
theorem integrable_stoppedProcess
  statement: [LocallyFiniteOrderBot ι] (hτ : IsStoppingTime ℱ τ)
  proof: by
  refine integrable_stoppedProcess_of_mem_finset hτ hu n (s := Finset.Iic n) fun ω h => ?_
  simp only [Finset.coe_Iic, Set.mem_image, Set.mem_Iic]
  have h_top : τ ω != ⊤ := fun h_contra => by simp [h_contra] at h
  lift τ ω to ι using h_top with i hi
  exact ⟨i, mod_cast h.le, rfl⟩

中文:
定理 integrable_stoppedProcess
  结论: [LocallyFiniteOrderBot ι] (hτ : IsStoppingTime ℱ τ)
  证明: by
  refine integrable_stoppedProcess_of_mem_finset hτ hu n (s := Finset.Iic n) fun ω h => ?_
  simp only [Finset.coe_Iic, Set.mem_image, Set.mem_Iic]
  have h_top : τ ω != ⊤ := fun h_contra => by simp [h_contra] at h
  lift τ ω to ι using h_top with i hi
  exact ⟨i, mod_cast h.le, rfl⟩

Depends on / 依赖: Finset, Finset.Iic, Finset.coe_Iic, Set.mem_Iic, Set.mem_image, coe_Iic, h.le, h_contra, h_top, integrable_stoppedProcess_of_mem_finset, mem_Iic, mem_image, mod_cast
-/
theorem integrable_stoppedProcess [LocallyFiniteOrderBot ι] (hτ : IsStoppingTime ℱ τ)
    (hu : forall n, Integrable (u n) μ) (n : ι) : Integrable (stoppedProcess u τ n) μ := by
  refine integrable_stoppedProcess_of_mem_finset hτ hu n (s := Finset.Iic n) fun ω h => ?_
  simp only [Finset.coe_Iic, Set.mem_image, Set.mem_Iic]
  have h_top : τ ω != ⊤ := fun h_contra => by simp [h_contra] at h
  lift τ ω to ι using h_top with i hi
  exact ⟨i, mod_cast h.le, rfl⟩

end StoppedProcess

end StoppedValueOfMemFinset

section StronglyAdaptedStoppedProcess

variable [TopologicalSpace β] [PseudoMetrizableSpace β] [Nonempty ι] [LinearOrder ι]
  [TopologicalSpace ι] [SecondCountableTopology ι] [OrderTopology ι]
  [MeasurableSpace ι] [BorelSpace ι]
  {f : Filtration ι m} {u : ι -> Ω -> β} {τ : Ω -> WithTop ι}

/--
theorem `StronglyAdapted.stoppedProcess` / 定理 `StronglyAdapted.stoppedProcess`

English:
theorem StronglyAdapted.stoppedProcess
  statement: [MetrizableSpace ι] (hu : StronglyAdapted f u)
  proof: ((hu.isStronglyProgressive_of_continuous hu_cont).stoppedProcess hτ).stronglyAdapted

中文:
定理 StronglyAdapted.stoppedProcess
  结论: [MetrizableSpace ι] (hu : StronglyAdapted f u)
  证明: ((hu.isStronglyProgressive_of_continuous hu_cont).stoppedProcess hτ).stronglyAdapted

Depends on / 依赖: hu.isStronglyProgressive_of_continuous, hu_cont, isStronglyProgressive_of_continuous, stoppedProcess, stronglyAdapted
-/
theorem StronglyAdapted.stoppedProcess [MetrizableSpace ι] (hu : StronglyAdapted f u)
    (hu_cont : forall ω, Continuous fun i => u i ω) (hτ : IsStoppingTime f τ) :
    StronglyAdapted f (stoppedProcess u τ) :=
  ((hu.isStronglyProgressive_of_continuous hu_cont).stoppedProcess hτ).stronglyAdapted

/--
theorem `StronglyAdapted.stoppedProcess_of_discrete` / 定理 `StronglyAdapted.stoppedProcess_of_discrete`

English:
theorem StronglyAdapted.stoppedProcess_of_discrete
  statement: [DiscreteTopology ι] (hu : StronglyAdapted f u)
  proof: (hu.isStronglyProgressive_of_discrete.stoppedProcess hτ).stronglyAdapted

中文:
定理 StronglyAdapted.stoppedProcess_of_discrete
  结论: [DiscreteTopology ι] (hu : StronglyAdapted f u)
  证明: (hu.isStronglyProgressive_of_discrete.stoppedProcess hτ).stronglyAdapted

Depends on / 依赖: hu.isStronglyProgressive_of_discrete.stoppedProcess, isStronglyProgressive_of_discrete, stoppedProcess, stronglyAdapted
-/
theorem StronglyAdapted.stoppedProcess_of_discrete [DiscreteTopology ι] (hu : StronglyAdapted f u)
    (hτ : IsStoppingTime f τ) : StronglyAdapted f (MeasureTheory.stoppedProcess u τ) :=
  (hu.isStronglyProgressive_of_discrete.stoppedProcess hτ).stronglyAdapted

/--
theorem `StronglyAdapted.stronglyMeasurable_stoppedProcess` / 定理 `StronglyAdapted.stronglyMeasurable_stoppedProcess`

English:
theorem StronglyAdapted.stronglyMeasurable_stoppedProcess
  statement: [MetrizableSpace ι]
  proof: (hu.isStronglyProgressive_of_continuous hu_cont).stronglyMeasurable_stoppedProcess hτ n

中文:
定理 StronglyAdapted.stronglyMeasurable_stoppedProcess
  结论: [MetrizableSpace ι]
  证明: (hu.isStronglyProgressive_of_continuous hu_cont).stronglyMeasurable_stoppedProcess hτ n

Depends on / 依赖: hu.isStronglyProgressive_of_continuous, hu_cont, isStronglyProgressive_of_continuous, stronglyMeasurable_stoppedProcess
-/
theorem StronglyAdapted.stronglyMeasurable_stoppedProcess [MetrizableSpace ι]
    (hu : StronglyAdapted f u) (hu_cont : forall ω, Continuous fun i => u i ω) (hτ : IsStoppingTime f τ)
    (n : ι) : StronglyMeasurable (MeasureTheory.stoppedProcess u τ n) :=
  (hu.isStronglyProgressive_of_continuous hu_cont).stronglyMeasurable_stoppedProcess hτ n

/--
theorem `StronglyAdapted.stronglyMeasurable_stoppedProcess_of_discrete` / 定理 `StronglyAdapted.stronglyMeasurable_stoppedProcess_of_discrete`

English:
theorem StronglyAdapted.stronglyMeasurable_stoppedProcess_of_discrete
  statement: [DiscreteTopology ι]
  proof: hu.isStronglyProgressive_of_discrete.stronglyMeasurable_stoppedProcess hτ n

中文:
定理 StronglyAdapted.stronglyMeasurable_stoppedProcess_of_discrete
  结论: [DiscreteTopology ι]
  证明: hu.isStronglyProgressive_of_discrete.stronglyMeasurable_stoppedProcess hτ n

Depends on / 依赖: hu.isStronglyProgressive_of_discrete.stronglyMeasurable_stoppedProcess, isStronglyProgressive_of_discrete, stronglyMeasurable_stoppedProcess
-/
theorem StronglyAdapted.stronglyMeasurable_stoppedProcess_of_discrete [DiscreteTopology ι]
    (hu : StronglyAdapted f u) (hτ : IsStoppingTime f τ) (n : ι) :
    StronglyMeasurable (MeasureTheory.stoppedProcess u τ n) :=
  hu.isStronglyProgressive_of_discrete.stronglyMeasurable_stoppedProcess hτ n

end StronglyAdaptedStoppedProcess

section Nat

/-! ### Filtrations indexed by `ℕ` -/


open Filtration

variable {u : Nat -> Ω -> β} {τ π : Ω -> Nat∞}

/--
theorem `stoppedValue_sub_eq_sum` / 定理 `stoppedValue_sub_eq_sum`

English:
theorem stoppedValue_sub_eq_sum
  given: [AddCommGroup β] (hle : τ <= π) (hπ : forall ω, π ω != ∞)
  proof: by
  ext ω
  have h_le' : (τ ω).untopA <= (π ω).untopA := untopA_mono (mod_cast hπ ω) (hle ω)
  rw [Finset.sum_Ico_eq_sub _ h_le']; rw [Finset.sum_range_sub]; rw [Finset.sum_range_sub]
  simp [stoppedValue]

中文:
定理 stoppedValue_sub_eq_sum
  条件: [AddCommGroup β] (hle : τ <= π) (hπ : 对任意 ω, π ω != ∞)
  证明: by
  ext ω
  have h_le' : (τ ω).untopA <= (π ω).untopA := untopA_mono (mod_cast hπ ω) (hle ω)
  rw [Finset.sum_Ico_eq_sub _ h_le']; rw [Finset.sum_range_sub]; rw [Finset.sum_range_sub]
  simp [stoppedValue]

Depends on / 依赖: Finset, Finset.sum_Ico_eq_sub, Finset.sum_range_sub, h_le, mod_cast, stoppedValue, sum_Ico_eq_sub, sum_range_sub, untopA, untopA_mono
-/
theorem stoppedValue_sub_eq_sum [AddCommGroup β] (hle : τ <= π) (hπ : forall ω, π ω != ∞) :
    stoppedValue u π - stoppedValue u τ = fun ω =>
      (∑ i in Finset.Ico (τ ω).untopA (π ω).untopA, (u (i + 1) - u i)) ω := by
  ext ω
  have h_le' : (τ ω).untopA <= (π ω).untopA := untopA_mono (mod_cast hπ ω) (hle ω)
  rw [Finset.sum_Ico_eq_sub _ h_le']; rw [Finset.sum_range_sub]; rw [Finset.sum_range_sub]
  simp [stoppedValue]

/--
theorem `stoppedValue_sub_eq_sum'` / 定理 `stoppedValue_sub_eq_sum'`

English:
theorem stoppedValue_sub_eq_sum'
  given: [AddCommGroup β] (hle : τ <= π) {N : Nat} (hbdd : forall ω, π ω <= N)
  proof: by
  have hπ_top ω : π ω != ⊤ := fun h => by specialize hbdd ω; simp [h] at hbdd
  have hτ_top ω : τ ω != ⊤ := ne_top_of_le_ne_top (hπ_top ω) (mod_cast hle ω)
  rw [stoppedValue_sub_eq_sum hle]
  swap; · intro ω; exact mod_cast hπ_top ω
  ext ω
  simp only [Finset.sum_apply, Finset.sum_indicator_eq_

中文:
定理 stoppedValue_sub_eq_sum'
  条件: [AddCommGroup β] (hle : τ <= π) {N : 自然数} (hbdd : 对任意 ω, π ω <= N)
  证明: by
  have hπ_top ω : π ω != ⊤ := fun h => by specialize hbdd ω; simp [h] at hbdd
  have hτ_top ω : τ ω != ⊤ := ne_top_of_le_ne_top (hπ_top ω) (mod_cast hle ω)
  rw [stoppedValue_sub_eq_sum hle]
  swap; · intro ω; exact mod_cast hπ_top ω
  ext ω
  simp only [Finset.sum_apply, Finset.sum_indicator_eq_

Depends on / 依赖: Finset, Finset.mem_Ico, Finset.sum_apply, Finset.sum_congr, Finset.sum_indicator_eq_sum_filter, Set.mem_ofPred_eq, mem_Ico, mem_ofPred_eq, mod_cast, ne_top_of_le_ne_top, specialize, stoppedValue_sub_eq_sum, sum_apply, sum_congr, sum_indicator_eq_sum_filter
-/
theorem stoppedValue_sub_eq_sum' [AddCommGroup β] (hle : τ <= π) {N : Nat} (hbdd : forall ω, π ω <= N) :
    stoppedValue u π - stoppedValue u τ = fun ω =>
      (∑ i in Finset.range (N + 1), Set.indicator {ω | τ ω <= i ∧ i < π ω} (u (i + 1) - u i)) ω := by
  have hπ_top ω : π ω != ⊤ := fun h => by specialize hbdd ω; simp [h] at hbdd
  have hτ_top ω : τ ω != ⊤ := ne_top_of_le_ne_top (hπ_top ω) (mod_cast hle ω)
  rw [stoppedValue_sub_eq_sum hle]
  swap; · intro ω; exact mod_cast hπ_top ω
  ext ω
  simp only [Finset.sum_apply, Finset.sum_indicator_eq_sum_filter]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext i
  simp only [Set.mem_ofPred_eq, Finset.mem_Ico]
  specialize hbdd ω
  lift τ ω to Nat using hτ_top ω with t ht
  lift π ω to Nat using hπ_top ω with b hb
  simp only [Nat.cast_le] at hbdd
  simp
  grind

section AddCommMonoid

variable [AddCommMonoid β]

/--
theorem `stoppedValue_eq` / 定理 `stoppedValue_eq`

English:
theorem stoppedValue_eq
  given: {N : Nat} (hbdd : forall ω, τ ω <= N)
  statement: stoppedValue u τ = fun x =>
  proof: by
  refine stoppedValue_eq_of_mem_finset fun ω => ?_
  specialize hbdd ω
  have h_top : τ ω != ⊤ := fun h_contra => by simp [h_contra] at hbdd
  lift τ ω to Nat using h_top with t ht
  simp only [Nat.cast_le] at hbdd
  simp only [ENat.some_eq_natCast, Finset.coe_range]
  exact ⟨t, by simpa, Nat.cas

中文:
定理 stoppedValue_eq
  条件: {N : 自然数} (hbdd : 对任意 ω, τ ω <= N)
  结论: stoppedValue u τ = fun x =>
  证明: by
  refine stoppedValue_eq_of_mem_finset fun ω => ?_
  specialize hbdd ω
  have h_top : τ ω != ⊤ := fun h_contra => by simp [h_contra] at hbdd
  lift τ ω to Nat using h_top with t ht
  simp only [Nat.cast_le] at hbdd
  simp only [ENat.some_eq_natCast, Finset.coe_range]
  exact ⟨t, by simpa, Nat.cas

Depends on / 依赖: ENat.some_eq_natCast, Finset, Finset.coe_range, Nat.cast_inj.mpr, Nat.cast_le, cast_inj, cast_le, coe_range, h_contra, h_top, some_eq_natCast, specialize, stoppedValue_eq_of_mem_finset
-/
theorem stoppedValue_eq {N : Nat} (hbdd : forall ω, τ ω <= N) : stoppedValue u τ = fun x =>
    (∑ i in Finset.range (N + 1), Set.indicator {ω | τ ω = i} (u i)) x := by
  refine stoppedValue_eq_of_mem_finset fun ω => ?_
  specialize hbdd ω
  have h_top : τ ω != ⊤ := fun h_contra => by simp [h_contra] at hbdd
  lift τ ω to Nat using h_top with t ht
  simp only [Nat.cast_le] at hbdd
  simp only [ENat.some_eq_natCast, Finset.coe_range]
  exact ⟨t, by simpa, Nat.cast_inj.mpr rfl⟩

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `stoppedProcess_eq` / 定理 `stoppedProcess_eq`

English:
theorem stoppedProcess_eq
  given: (n : Nat)
  statement: stoppedProcess u τ n = Set.indicator {a | n <= τ a} (u n) +
  proof: by
  rw [stoppedProcess_eq'' n]
  congr with i
  rw [Finset.mem_Iio]; rw [Finset.mem_range]

中文:
定理 stoppedProcess_eq
  条件: (n : 自然数)
  结论: stoppedProcess u τ n = Set.indicator {a | n <= τ a} (u n) +
  证明: by
  rw [stoppedProcess_eq'' n]
  congr with i
  rw [Finset.mem_Iio]; rw [Finset.mem_range]

Depends on / 依赖: Finset, Finset.mem_Iio, Finset.mem_range, mem_Iio, mem_range, stoppedProcess_eq
-/
theorem stoppedProcess_eq (n : Nat) : stoppedProcess u τ n = Set.indicator {a | n <= τ a} (u n) +
    ∑ i in Finset.range n, Set.indicator {ω | τ ω = i} (u i) := by
  rw [stoppedProcess_eq'' n]
  congr with i
  rw [Finset.mem_Iio]; rw [Finset.mem_range]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `stoppedProcess_eq'` / 定理 `stoppedProcess_eq'`

English:
theorem stoppedProcess_eq'
  given: (n : Nat)
  statement: stoppedProcess u τ n = Set.indicator {a | n + 1 <= τ a} (u n) +
  proof: by
  have : {a | n <= τ a}.indicator (u n) =
      {a | n + 1 <= τ a}.indicator (u n) + {a | τ a = n}.indicator (u n) := by
    ext x
    rw [add_comm]; rw [Pi.add_apply]; rw [← Set.indicator_union_of_notMem_inter]
    · simp_rw [@eq_comm _ _ (n : WithTop Nat), @le_iff_eq_or_lt _ _ (n : WithTop Nat)

中文:
定理 stoppedProcess_eq'
  条件: (n : 自然数)
  结论: stoppedProcess u τ n = Set.indicator {a | n + 1 <= τ a} (u n) +
  证明: by
  have : {a | n <= τ a}.indicator (u n) =
      {a | n + 1 <= τ a}.indicator (u n) + {a | τ a = n}.indicator (u n) := by
    ext x
    rw [add_comm]; rw [Pi.add_apply]; rw [← Set.indicator_union_of_notMem_inter]
    · simp_rw [@eq_comm _ _ (n : WithTop Nat), @le_iff_eq_or_lt _ _ (n : WithTop Nat)

Depends on / 依赖: Nat.cast_lt, Pi.add_apply, Set.indicator_union_of_notMem_inter, Set.me, Set.mem_ofPred_eq, Set.ofPred_or, WithTop, add_apply, add_comm, cast_lt, eq_comm, indicator, indicator_union_of_notMem_inter, le_iff_eq_or_lt, mem_ofPred_eq, ofPred_or, simp_rw
-/
theorem stoppedProcess_eq' (n : Nat) : stoppedProcess u τ n = Set.indicator {a | n + 1 <= τ a} (u n) +
    ∑ i in Finset.range (n + 1), Set.indicator {a | τ a = i} (u i) := by
  have : {a | n <= τ a}.indicator (u n) =
      {a | n + 1 <= τ a}.indicator (u n) + {a | τ a = n}.indicator (u n) := by
    ext x
    rw [add_comm]; rw [Pi.add_apply]; rw [← Set.indicator_union_of_notMem_inter]
    · simp_rw [@eq_comm _ _ (n : WithTop Nat), @le_iff_eq_or_lt _ _ (n : WithTop Nat)]
      have : {a | ↑n + 1 <= τ a} = {a | ↑n < τ a} := by
        ext ω
        simp only [Set.mem_ofPred_eq]
        cases τ ω with
        | top => simp
        | coe t =>
          simp only [Nat.cast_lt]
          norm_cast
      rw [this]; rw [Set.ofPred_or]
    · rintro ⟨h₁, h₂⟩
      rw [Set.mem_ofPred] at h₁ h₂
      rw [h₁] at h₂
      norm_cast at h₂
      grind
  rw [stoppedProcess_eq]; rw [this]; rw [Finset.sum_range_succ_comm]; rw [← add_assoc]

end AddCommMonoid

end Nat

section PiecewiseConst

variable [Preorder ι] {𝒢 : Filtration ι m} {τ η : Ω -> WithTop ι} {i j : ι} {s : Set Ω}
  [DecidablePred (· in s)]

/--
theorem `IsStoppingTime.piecewise_of_le` / 定理 `IsStoppingTime.piecewise_of_le`

English:
theorem IsStoppingTime.piecewise_of_le
  statement: (hτ_st : IsStoppingTime 𝒢 τ) (hη_st : IsStoppingTime 𝒢 η)
  proof: by
  intro n
  have : {ω | s.piecewise τ η ω <= n} = s inter {ω | τ ω <= n} union sᶜ inter {ω | η ω <= n} := by
    ext1 ω
    simp only [Set.piecewise, Set.mem_ofPred_eq]
    by_cases hx : ω in s <;> simp [hx]
  rw [this]
  by_cases hin : i <= n
  · have hs_n : MeasurableSet[𝒢 n] s := 𝒢.mono hin _ 

中文:
定理 IsStoppingTime.piecewise_of_le
  结论: (hτ_st : IsStoppingTime 𝒢 τ) (hη_st : IsStoppingTime 𝒢 η)
  证明: by
  intro n
  have : {ω | s.piecewise τ η ω <= n} = s inter {ω | τ ω <= n} union sᶜ inter {ω | η ω <= n} := by
    ext1 ω
    simp only [Set.piecewise, Set.mem_ofPred_eq]
    by_cases hx : ω in s <;> simp [hx]
  rw [this]
  by_cases hin : i <= n
  · have hs_n : MeasurableSet[𝒢 n] s := 𝒢.mono hin _ 

Depends on / 依赖: MeasurableSet, Set.mem_ofPred_eq, Set.piecewise, hs_n, hs_n.compl.inter, hs_n.inter, mem_ofPred_eq, mod_cast, piecewise, s.piecewise
-/
theorem IsStoppingTime.piecewise_of_le (hτ_st : IsStoppingTime 𝒢 τ) (hη_st : IsStoppingTime 𝒢 η)
    (hτ : forall ω, i <= τ ω) (hη : forall ω, i <= η ω) (hs : MeasurableSet[𝒢 i] s) :
    IsStoppingTime 𝒢 (s.piecewise τ η) := by
  intro n
  have : {ω | s.piecewise τ η ω <= n} = s inter {ω | τ ω <= n} union sᶜ inter {ω | η ω <= n} := by
    ext1 ω
    simp only [Set.piecewise, Set.mem_ofPred_eq]
    by_cases hx : ω in s <;> simp [hx]
  rw [this]
  by_cases hin : i <= n
  · have hs_n : MeasurableSet[𝒢 n] s := 𝒢.mono hin _ hs
    exact (hs_n.inter (hτ_st n)).union (hs_n.compl.inter (hη_st n))
  · have hτn : forall ω, ¬τ ω <= n := fun ω hτn => hin (mod_cast (hτ ω).trans hτn)
    have hηn : forall ω, ¬η ω <= n := fun ω hηn => hin (mod_cast (hη ω).trans hηn)
    simp [hτn, hηn, @MeasurableSet.empty _ _]

/--
theorem `isStoppingTime_piecewise_const` / 定理 `isStoppingTime_piecewise_const`

English:
theorem isStoppingTime_piecewise_const
  given: (hij : i <= j) (hs : MeasurableSet[𝒢 i] s)
  proof: (isStoppingTime_const 𝒢 i).piecewise_of_le (isStoppingTime_const 𝒢 j) (fun _ => le_rfl)
    (fun _ => mod_cast hij) hs

中文:
定理 isStoppingTime_piecewise_const
  条件: (hij : i <= j) (hs : MeasurableSet[𝒢 i] s)
  证明: (isStoppingTime_const 𝒢 i).piecewise_of_le (isStoppingTime_const 𝒢 j) (fun _ => le_rfl)
    (fun _ => mod_cast hij) hs

Depends on / 依赖: isStoppingTime_const, le_rfl, mod_cast, piecewise_of_le
-/
theorem isStoppingTime_piecewise_const (hij : i <= j) (hs : MeasurableSet[𝒢 i] s) :
    IsStoppingTime 𝒢 (s.piecewise (fun _ => i) fun _ => j) :=
  (isStoppingTime_const 𝒢 i).piecewise_of_le (isStoppingTime_const 𝒢 j) (fun _ => le_rfl)
    (fun _ => mod_cast hij) hs

/--
theorem `stoppedValue_piecewise_const` / 定理 `stoppedValue_piecewise_const`

English:
theorem stoppedValue_piecewise_const
  given: {ι' α : Type*} [Nonempty ι'] {i j : ι'} {f : ι' -> Ω -> α}
  proof: by
  ext ω; rw [stoppedValue]; by_cases hx : ω in s <;> simp [hx]

中文:
定理 stoppedValue_piecewise_const
  条件: {ι' α : 类型} [Nonempty ι'] {i j : ι'} {f : ι' -> Ω -> α}
  证明: by
  ext ω; rw [stoppedValue]; by_cases hx : ω in s <;> simp [hx]

Depends on / 依赖: stoppedValue
-/
theorem stoppedValue_piecewise_const {ι' α : Type*} [Nonempty ι'] {i j : ι'} {f : ι' -> Ω -> α} :
    stoppedValue f (s.piecewise (fun _ => i) fun _ => j) = s.piecewise (f i) (f j) := by
  ext ω; rw [stoppedValue]; by_cases hx : ω in s <;> simp [hx]

/--
theorem `stoppedValue_piecewise_const'` / 定理 `stoppedValue_piecewise_const'`

English:
theorem stoppedValue_piecewise_const'
  statement: {ι' α : Type*} [AddCommGroup α]
  proof: by
  ext ω; rw [stoppedValue]; by_cases hx : ω in s <;> simp [hx]

中文:
定理 stoppedValue_piecewise_const'
  结论: {ι' α : 类型} [AddCommGroup α]
  证明: by
  ext ω; rw [stoppedValue]; by_cases hx : ω in s <;> simp [hx]

Depends on / 依赖: stoppedValue
-/
theorem stoppedValue_piecewise_const' {ι' α : Type*} [AddCommGroup α]
    [Nonempty ι'] {i j : ι'} {f : ι' -> Ω -> α} :
    stoppedValue f (s.piecewise (fun _ => i) fun _ => j) =
    s.indicator (f i) + sᶜ.indicator (f j) := by
  ext ω; rw [stoppedValue]; by_cases hx : ω in s <;> simp [hx]

end PiecewiseConst

section Condexp

/-! ### Conditional expectation with respect to the σ-algebra generated by a stopping time -/


variable [LinearOrder ι] {μ : Measure Ω} {ℱ : Filtration ι m} {τ σ : Ω -> WithTop ι} {E : Type*}
  [NormedAddCommGroup E] [NormedSpace Real E] [CompleteSpace E] {f : Ω -> E}

/--
theorem `condExp_stopping_time_ae_eq_restrict_eq_of_countable_range` / 定理 `condExp_stopping_time_ae_eq_restrict_eq_of_countable_range`

English:
theorem condExp_stopping_time_ae_eq_restrict_eq_of_countable_range
  statement: [SigmaFiniteFiltration μ ℱ]
  proof: by
  refine condExp_ae_eq_restrict_of_measurableSpace_eq_on
    (hτ.measurableSpace_le) (ℱ.le i)
    (hτ.measurableSet_eq_of_countable_range' h_countable i) fun t => ?_
  rw [Set.inter_comm _ t]; rw [IsStoppingTime.measurableSet_inter_eq_iff]

中文:
定理 condExp_stopping_time_ae_eq_restrict_eq_of_countable_range
  结论: [SigmaFiniteFiltration μ ℱ]
  证明: by
  refine condExp_ae_eq_restrict_of_measurableSpace_eq_on
    (hτ.measurableSpace_le) (ℱ.le i)
    (hτ.measurableSet_eq_of_countable_range' h_countable i) fun t => ?_
  rw [Set.inter_comm _ t]; rw [IsStoppingTime.measurableSet_inter_eq_iff]

Depends on / 依赖: IsStoppingTime, IsStoppingTime.measurableSet_inter_eq_iff, Set.inter_comm, condExp_ae_eq_restrict_of_measurableSpace_eq_on, h_countable, inter_comm, measurableSet_eq_of_countable_range, measurableSet_inter_eq_iff, measurableSpace_le
-/
theorem condExp_stopping_time_ae_eq_restrict_eq_of_countable_range [SigmaFiniteFiltration μ ℱ]
    (hτ : IsStoppingTime ℱ τ) (h_countable : (Set.range τ).Countable)
    [SigmaFinite (μ.trim (hτ.measurableSpace_le))] (i : ι) :
    μ[f | hτ.measurableSpace] =ᵐ[μ.restrict {x | τ x = i}] μ[f | ℱ i] := by
  refine condExp_ae_eq_restrict_of_measurableSpace_eq_on
    (hτ.measurableSpace_le) (ℱ.le i)
    (hτ.measurableSet_eq_of_countable_range' h_countable i) fun t => ?_
  rw [Set.inter_comm _ t]; rw [IsStoppingTime.measurableSet_inter_eq_iff]

/--
theorem `condExp_stopping_time_ae_eq_restrict_eq_of_countable` / 定理 `condExp_stopping_time_ae_eq_restrict_eq_of_countable`

English:
theorem condExp_stopping_time_ae_eq_restrict_eq_of_countable
  statement: [Countable ι]
  proof: condExp_stopping_time_ae_eq_restrict_eq_of_countable_range hτ (Set.to_countable _) i

中文:
定理 condExp_stopping_time_ae_eq_restrict_eq_of_countable
  结论: [Countable ι]
  证明: condExp_stopping_time_ae_eq_restrict_eq_of_countable_range hτ (Set.to_countable _) i

Depends on / 依赖: Set.to_countable, condExp_stopping_time_ae_eq_restrict_eq_of_countable_range, to_countable
-/
theorem condExp_stopping_time_ae_eq_restrict_eq_of_countable [Countable ι]
    [SigmaFiniteFiltration μ ℱ] (hτ : IsStoppingTime ℱ τ)
    [SigmaFinite (μ.trim hτ.measurableSpace_le)] (i : ι) :
    μ[f | hτ.measurableSpace] =ᵐ[μ.restrict {x | τ x = i}] μ[f | ℱ i] :=
  condExp_stopping_time_ae_eq_restrict_eq_of_countable_range hτ (Set.to_countable _) i

/--
theorem `condExp_min_stopping_time_ae_eq_restrict_le_const` / 定理 `condExp_min_stopping_time_ae_eq_restrict_le_const`

English:
theorem condExp_min_stopping_time_ae_eq_restrict_le_const
  statement: (hτ : IsStoppingTime ℱ τ) (i : ι)
  proof: by
  have : SigmaFinite (μ.trim hτ.measurableSpace_le) :=
    haveI h_le : (hτ.min_const i).measurableSpace <= hτ.measurableSpace := by
      rw [IsStoppingTime.measurableSpace_min_const]
      exact inf_le_left
    sigmaFiniteTrim_mono _ h_le
  refine (condExp_ae_eq_restrict_of_measurableSpace_eq_o

中文:
定理 condExp_min_stopping_time_ae_eq_restrict_le_const
  结论: (hτ : IsStoppingTime ℱ τ) (i : ι)
  证明: by
  have : SigmaFinite (μ.trim hτ.measurableSpace_le) :=
    haveI h_le : (hτ.min_const i).measurableSpace <= hτ.measurableSpace := by
      rw [IsStoppingTime.measurableSpace_min_const]
      exact inf_le_left
    sigmaFiniteTrim_mono _ h_le
  refine (condExp_ae_eq_restrict_of_measurableSpace_eq_o

Depends on / 依赖: IsStoppingTime, IsStoppingTime.measurableSpace_min_const, Set.inter_comm, SigmaFinite, condExp_ae_eq_restrict_of_measurableSpace_eq_on, h_le, inf_le_left, inter_comm, measurableSet_inter_le_const_iff, measurableSet_le, measurableSpace, measurableSpace_le, measurableSpace_min_const, min_const, sigmaFiniteTrim_mono
-/
theorem condExp_min_stopping_time_ae_eq_restrict_le_const (hτ : IsStoppingTime ℱ τ) (i : ι)
    [SigmaFinite (μ.trim (hτ.min_const i).measurableSpace_le)] :
    μ[f | (hτ.min_const i).measurableSpace] =ᵐ[μ.restrict {x | τ x <= i}]
      μ[f | hτ.measurableSpace] := by
  have : SigmaFinite (μ.trim hτ.measurableSpace_le) :=
    haveI h_le : (hτ.min_const i).measurableSpace <= hτ.measurableSpace := by
      rw [IsStoppingTime.measurableSpace_min_const]
      exact inf_le_left
    sigmaFiniteTrim_mono _ h_le
  refine (condExp_ae_eq_restrict_of_measurableSpace_eq_on hτ.measurableSpace_le
    (hτ.min_const i).measurableSpace_le (hτ.measurableSet_le' i) fun t => ?_).symm
  rw [Set.inter_comm _ t]; rw [hτ.measurableSet_inter_le_const_iff]

variable [TopologicalSpace ι] [OrderTopology ι]

/--
theorem `condExp_stopping_time_ae_eq_restrict_eq` / 定理 `condExp_stopping_time_ae_eq_restrict_eq`

English:
theorem condExp_stopping_time_ae_eq_restrict_eq
  statement: [FirstCountableTopology ι]
  proof: by
  refine condExp_ae_eq_restrict_of_measurableSpace_eq_on hτ.measurableSpace_le (ℱ.le i)
    (hτ.measurableSet_eq' i) fun t => ?_
  rw [Set.inter_comm _ t]; rw [IsStoppingTime.measurableSet_inter_eq_iff]

中文:
定理 condExp_stopping_time_ae_eq_restrict_eq
  结论: [FirstCountableTopology ι]
  证明: by
  refine condExp_ae_eq_restrict_of_measurableSpace_eq_on hτ.measurableSpace_le (ℱ.le i)
    (hτ.measurableSet_eq' i) fun t => ?_
  rw [Set.inter_comm _ t]; rw [IsStoppingTime.measurableSet_inter_eq_iff]

Depends on / 依赖: IsStoppingTime, IsStoppingTime.measurableSet_inter_eq_iff, Set.inter_comm, condExp_ae_eq_restrict_of_measurableSpace_eq_on, inter_comm, measurableSet_eq, measurableSet_inter_eq_iff, measurableSpace_le
-/
theorem condExp_stopping_time_ae_eq_restrict_eq [FirstCountableTopology ι]
    [SigmaFiniteFiltration μ ℱ] (hτ : IsStoppingTime ℱ τ)
    [SigmaFinite (μ.trim hτ.measurableSpace_le)] (i : ι) :
    μ[f | hτ.measurableSpace] =ᵐ[μ.restrict {x | τ x = i}] μ[f | ℱ i] := by
  refine condExp_ae_eq_restrict_of_measurableSpace_eq_on hτ.measurableSpace_le (ℱ.le i)
    (hτ.measurableSet_eq' i) fun t => ?_
  rw [Set.inter_comm _ t]; rw [IsStoppingTime.measurableSet_inter_eq_iff]

/--
theorem `condExp_min_stopping_time_ae_eq_restrict_le` / 定理 `condExp_min_stopping_time_ae_eq_restrict_le`

English:
theorem condExp_min_stopping_time_ae_eq_restrict_le
  statement: [SecondCountableTopology ι]
  proof: by
  have : SigmaFinite (μ.trim hτ.measurableSpace_le) :=
    sigmaFiniteTrim_mono _ (hτ.measurableSpace_min hσ ▸ inf_le_left)
  refine (condExp_ae_eq_restrict_of_measurableSpace_eq_on hτ.measurableSpace_le
    (hτ.min hσ).measurableSpace_le (hτ.measurableSet_le_stopping_time hσ) fun t => ?_).symm
 

中文:
定理 condExp_min_stopping_time_ae_eq_restrict_le
  结论: [SecondCountableTopology ι]
  证明: by
  have : SigmaFinite (μ.trim hτ.measurableSpace_le) :=
    sigmaFiniteTrim_mono _ (hτ.measurableSpace_min hσ ▸ inf_le_left)
  refine (condExp_ae_eq_restrict_of_measurableSpace_eq_on hτ.measurableSpace_le
    (hτ.min hσ).measurableSpace_le (hτ.measurableSet_le_stopping_time hσ) fun t => ?_).symm
 

Depends on / 依赖: Set.inter_comm, SigmaFinite, condExp_ae_eq_restrict_of_measurableSpace_eq_on, inf_le_left, inter_comm, measurableSet_inter_le_iff, measurableSet_le_stopping_time, measurableSpace_le, measurableSpace_min, sigmaFiniteTrim_mono
-/
theorem condExp_min_stopping_time_ae_eq_restrict_le [SecondCountableTopology ι]
    (hτ : IsStoppingTime ℱ τ) (hσ : IsStoppingTime ℱ σ)
    [SigmaFinite (μ.trim (hτ.min hσ).measurableSpace_le)] :
    μ[f | (hτ.min hσ).measurableSpace] =ᵐ[μ.restrict {x | τ x <= σ x}]
      μ[f | hτ.measurableSpace] := by
  have : SigmaFinite (μ.trim hτ.measurableSpace_le) :=
    sigmaFiniteTrim_mono _ (hτ.measurableSpace_min hσ ▸ inf_le_left)
  refine (condExp_ae_eq_restrict_of_measurableSpace_eq_on hτ.measurableSpace_le
    (hτ.min hσ).measurableSpace_le (hτ.measurableSet_le_stopping_time hσ) fun t => ?_).symm
  rw [Set.inter_comm _ t]; rw [hτ.measurableSet_inter_le_iff hσ]

end Condexp

end MeasureTheory
