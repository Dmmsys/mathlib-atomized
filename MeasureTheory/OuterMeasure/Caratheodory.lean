/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
module

public import Mathlib.MeasureTheory.OuterMeasure.OfFunction
public import Mathlib.MeasureTheory.PiSystem

/-!
# The Carathéodory σ-algebra of an outer measure

Given an outer measure `m`, the Carathéodory-measurable sets are the sets `s` such that
for all sets `t` we have `m t = m (t ∩ s) + m (t \ s)`. This forms a measurable space.

## Main definitions and statements

* `MeasureTheory.OuterMeasure.caratheodory` is the Carathéodory-measurable space
  of an outer measure.

## References

* <https://en.wikipedia.org/wiki/Outer_measure>
* <https://en.wikipedia.org/wiki/Carath%C3%A9odory%27s_criterion>

## Tags

Carathéodory-measurable, Carathéodory's criterion

-/

@[expose] public section

noncomputable section

open Set Function Filter
open scoped NNReal Topology ENNReal

namespace MeasureTheory
namespace OuterMeasure

section CaratheodoryMeasurable

universe u

variable {α : Type u} (m : OuterMeasure α)

attribute [local simp] Set.inter_comm Set.inter_left_comm Set.inter_assoc

variable {s s₁ s₂ : Set α}

/--
Definition of `IsCaratheodory` / `IsCaratheodory` 的定义

English:
definition IsCaratheodory
  signature: (s : Set α)
  body: forall t, m t = m (t inter s) + m (t \ s)

中文:
定义 IsCaratheodory
  签名: (s : 集合 α)
  定义体: forall t, m t = m (t inter s) + m (t \ s)
-/
def IsCaratheodory (s : Set α) : Prop :=
  forall t, m t = m (t inter s) + m (t \ s)

/--
theorem `isCaratheodory_iff_le'` / 定理 `isCaratheodory_iff_le'`

English:
theorem isCaratheodory_iff_le'
  given: {s : Set α}
  proof: forall_congr' fun _ => le_antisymm_iff.trans and_iff_right measure_le_inter_add_sdiff _ _ _

@[simp]

中文:
定理 isCaratheodory_iff_le'
  条件: {s : 集合 α}
  证明: forall_congr' fun _ => le_antisymm_iff.trans and_iff_right measure_le_inter_add_sdiff _ _ _

@[simp]

Depends on / 依赖: and_iff_right, forall_congr, le_antisymm_iff, le_antisymm_iff.trans, measure_le_inter_add_sdiff
-/
theorem isCaratheodory_iff_le' {s : Set α} :
    IsCaratheodory m s ↔ forall t, m (t inter s) + m (t \ s) <= m t :=
forall_congr' fun _ => le_antisymm_iff.trans and_iff_right measure_le_inter_add_sdiff _ _ _

@[simp]
/--
theorem `isCaratheodory_empty` / 定理 `isCaratheodory_empty`

English:
theorem isCaratheodory_empty
  statement: IsCaratheodory m ∅
  proof: by simp [IsCaratheodory, sdiff_empty]

中文:
定理 isCaratheodory_empty
  结论: IsCaratheodory m ∅
  证明: by simp [IsCaratheodory, sdiff_empty]

Depends on / 依赖: IsCaratheodory, sdiff_empty
-/
theorem isCaratheodory_empty : IsCaratheodory m ∅ := by simp [IsCaratheodory, sdiff_empty]

/--
theorem `isCaratheodory_compl` / 定理 `isCaratheodory_compl`

English:
theorem isCaratheodory_compl
  statement: IsCaratheodory m s₁ -> IsCaratheodory m s₁ᶜ
  proof: by
  simp [IsCaratheodory, sdiff_eq, add_comm]

@[simp]

中文:
定理 isCaratheodory_compl
  结论: IsCaratheodory m s₁ -> IsCaratheodory m s₁ᶜ
  证明: by
  simp [IsCaratheodory, sdiff_eq, add_comm]

@[simp]

Depends on / 依赖: IsCaratheodory, add_comm, sdiff_eq
-/
theorem isCaratheodory_compl : IsCaratheodory m s₁ -> IsCaratheodory m s₁ᶜ := by
  simp [IsCaratheodory, sdiff_eq, add_comm]

@[simp]
/--
theorem `isCaratheodory_compl_iff` / 定理 `isCaratheodory_compl_iff`

English:
theorem isCaratheodory_compl_iff
  statement: IsCaratheodory m sᶜ ↔ IsCaratheodory m s
  proof: ⟨fun h => by simpa using isCaratheodory_compl m h, isCaratheodory_compl m⟩

中文:
定理 isCaratheodory_compl_iff
  结论: IsCaratheodory m sᶜ ↔ IsCaratheodory m s
  证明: ⟨fun h => by simpa using isCaratheodory_compl m h, isCaratheodory_compl m⟩

Depends on / 依赖: isCaratheodory_compl
-/
theorem isCaratheodory_compl_iff : IsCaratheodory m sᶜ ↔ IsCaratheodory m s :=
  ⟨fun h => by simpa using isCaratheodory_compl m h, isCaratheodory_compl m⟩

/--
theorem `isCaratheodory_union` / 定理 `isCaratheodory_union`

English:
theorem isCaratheodory_union
  given: (h₁ : IsCaratheodory m s₁) (h₂ : IsCaratheodory m s₂)
  proof: fun t => by
  rw [h₁ t]; rw [h₂ (t inter s₁)]; rw [h₂ (t \ s₁)]; rw [h₁ (t inter (s₁ union s₂))]; rw [inter_sdiff_assoc _ _ s₁]; rw [Set.inter_assoc _ _ s₁]; rw [inter_eq_self_of_subset_right Set.subset_union_left]; rw [union_sdiff_left]; rw [h₂ (t inter s₁)]
  simp [sdiff_eq, add_assoc]

中文:
定理 isCaratheodory_union
  条件: (h₁ : IsCaratheodory m s₁) (h₂ : IsCaratheodory m s₂)
  证明: fun t => by
  rw [h₁ t]; rw [h₂ (t inter s₁)]; rw [h₂ (t \ s₁)]; rw [h₁ (t inter (s₁ union s₂))]; rw [inter_sdiff_assoc _ _ s₁]; rw [Set.inter_assoc _ _ s₁]; rw [inter_eq_self_of_subset_right Set.subset_union_left]; rw [union_sdiff_left]; rw [h₂ (t inter s₁)]
  simp [sdiff_eq, add_assoc]

Depends on / 依赖: Set.inter_assoc, Set.subset_union_left, add_assoc, inter_assoc, inter_eq_self_of_subset_right, inter_sdiff_assoc, sdiff_eq, subset_union_left, union_sdiff_left
-/
theorem isCaratheodory_union (h₁ : IsCaratheodory m s₁) (h₂ : IsCaratheodory m s₂) :
    IsCaratheodory m (s₁ union s₂) := fun t => by
  rw [h₁ t]; rw [h₂ (t inter s₁)]; rw [h₂ (t \ s₁)]; rw [h₁ (t inter (s₁ union s₂))]; rw [inter_sdiff_assoc _ _ s₁]; rw [Set.inter_assoc _ _ s₁]; rw [inter_eq_self_of_subset_right Set.subset_union_left]; rw [union_sdiff_left]; rw [h₂ (t inter s₁)]
  simp [sdiff_eq, add_assoc]

variable {m} in
/--
lemma `IsCaratheodory.biUnion_of_finite` / 引理 `IsCaratheodory.biUnion_of_finite`

English:
lemma IsCaratheodory.biUnion_of_finite
  statement: {ι : Type*} {s : ι -> Set α} {t : Set ι} (ht : t.Finite)
  proof: by
  classical
  lift t to Finset ι using ht
  induction t using Finset.induction_on with
  | empty => simp
  | insert i t hi IH =>
    simp only [Finset.mem_coe, Finset.mem_insert, iUnion_iUnion_eq_or_left] at h ⊢
    exact m.isCaratheodory_union (h _ <| Or.inl rfl) (IH fun _ hj => h _ <| Or.inr hj

中文:
引理 IsCaratheodory.biUnion_of_finite
  结论: {ι : 类型} {s : ι -> 集合 α} {t : 集合 ι} (ht : t.有限)
  证明: by
  classical
  lift t to Finset ι using ht
  induction t using Finset.induction_on with
  | empty => simp
  | insert i t hi IH =>
    simp only [Finset.mem_coe, Finset.mem_insert, iUnion_iUnion_eq_or_left] at h ⊢
    exact m.isCaratheodory_union (h _ <| Or.inl rfl) (IH fun _ hj => h _ <| Or.inr hj

Depends on / 依赖: Finset, Finset.induction_on, Finset.mem_coe, Finset.mem_insert, Or.inl, Or.inr, classical, iUnion_iUnion_eq_or_left, induction_on, insert, isCaratheodory_union, m.isCaratheodory_union, mem_coe, mem_insert
-/
lemma IsCaratheodory.biUnion_of_finite {ι : Type*} {s : ι -> Set α} {t : Set ι} (ht : t.Finite)
    (h : forall i in t, m.IsCaratheodory (s i)) :
    m.IsCaratheodory (⋃ i in t, s i) := by
  classical
  lift t to Finset ι using ht
  induction t using Finset.induction_on with
  | empty => simp
  | insert i t hi IH =>
    simp only [Finset.mem_coe, Finset.mem_insert, iUnion_iUnion_eq_or_left] at h ⊢
    exact m.isCaratheodory_union (h _ <| Or.inl rfl) (IH fun _ hj => h _ <| Or.inr hj)

/--
theorem `measure_inter_union` / 定理 `measure_inter_union`

English:
theorem measure_inter_union
  given: (h : s₁ inter s₂ subseteq ∅) (h₁ : IsCaratheodory m s₁) {t : Set α}
  proof: by
  rw [h₁]; rw [Set.inter_assoc]; rw [Set.union_inter_cancel_left]; rw [inter_sdiff_assoc]; rw [union_sdiff_cancel_left h]

中文:
定理 measure_inter_union
  条件: (h : s₁ inter s₂ subseteq ∅) (h₁ : IsCaratheodory m s₁) {t : 集合 α}
  证明: by
  rw [h₁]; rw [Set.inter_assoc]; rw [Set.union_inter_cancel_left]; rw [inter_sdiff_assoc]; rw [union_sdiff_cancel_left h]

Depends on / 依赖: Set.inter_assoc, Set.union_inter_cancel_left, inter_assoc, inter_sdiff_assoc, union_inter_cancel_left, union_sdiff_cancel_left
-/
theorem measure_inter_union (h : s₁ inter s₂ subseteq ∅) (h₁ : IsCaratheodory m s₁) {t : Set α} :
    m (t inter (s₁ union s₂)) = m (t inter s₁) + m (t inter s₂) := by
  rw [h₁]; rw [Set.inter_assoc]; rw [Set.union_inter_cancel_left]; rw [inter_sdiff_assoc]; rw [union_sdiff_cancel_left h]

/--
theorem `isCaratheodory_iUnion_lt` / 定理 `isCaratheodory_iUnion_lt`

English:
theorem isCaratheodory_iUnion_lt
  given: {s : Nat -> Set α}

中文:
定理 isCaratheodory_iUnion_lt
  条件: {s : 自然数 -> 集合 α}
-/
theorem isCaratheodory_iUnion_lt {s : Nat -> Set α} :
    forall {n : Nat}, (forall i < n, IsCaratheodory m (s i)) -> IsCaratheodory m (⋃ i < n, s i)
  | 0, _ => by simp
  | n + 1, h => by
    rw [biUnion_lt_succ]
    exact isCaratheodory_union m
            (isCaratheodory_iUnion_lt fun i hi => h i <| lt_of_lt_of_le hi <| Nat.le_succ _)
            (h n (le_refl (n + 1)))

/--
theorem `isCaratheodory_inter` / 定理 `isCaratheodory_inter`

English:
theorem isCaratheodory_inter
  given: (h₁ : IsCaratheodory m s₁) (h₂ : IsCaratheodory m s₂)
  proof: by
  rw [← isCaratheodory_compl_iff]; rw [Set.compl_inter]
  exact isCaratheodory_union _ (isCaratheodory_compl _ h₁) (isCaratheodory_compl _ h₂)

中文:
定理 isCaratheodory_inter
  条件: (h₁ : IsCaratheodory m s₁) (h₂ : IsCaratheodory m s₂)
  证明: by
  rw [← isCaratheodory_compl_iff]; rw [Set.compl_inter]
  exact isCaratheodory_union _ (isCaratheodory_compl _ h₁) (isCaratheodory_compl _ h₂)

Depends on / 依赖: Set.compl_inter, compl_inter, isCaratheodory_compl, isCaratheodory_compl_iff, isCaratheodory_union
-/
theorem isCaratheodory_inter (h₁ : IsCaratheodory m s₁) (h₂ : IsCaratheodory m s₂) :
    IsCaratheodory m (s₁ inter s₂) := by
  rw [← isCaratheodory_compl_iff]; rw [Set.compl_inter]
  exact isCaratheodory_union _ (isCaratheodory_compl _ h₁) (isCaratheodory_compl _ h₂)

/--
lemma `isCaratheodory_sdiff` / 引理 `isCaratheodory_sdiff`

English:
lemma isCaratheodory_sdiff
  given: (h₁ : IsCaratheodory m s₁) (h₂ : IsCaratheodory m s₂)
  proof: m.isCaratheodory_inter h₁ (m.isCaratheodory_compl h₂)

@[deprecated (since := "2026-06-03")] alias isCaratheodory_diff := isCaratheodory_sdiff

中文:
引理 isCaratheodory_sdiff
  条件: (h₁ : IsCaratheodory m s₁) (h₂ : IsCaratheodory m s₂)
  证明: m.isCaratheodory_inter h₁ (m.isCaratheodory_compl h₂)

@[deprecated (since := "2026-06-03")] alias isCaratheodory_diff := isCaratheodory_sdiff

Depends on / 依赖: isCaratheodory_compl, isCaratheodory_inter, m.isCaratheodory_compl, m.isCaratheodory_inter
-/
lemma isCaratheodory_sdiff (h₁ : IsCaratheodory m s₁) (h₂ : IsCaratheodory m s₂) :
    IsCaratheodory m (s₁ \ s₂) := m.isCaratheodory_inter h₁ (m.isCaratheodory_compl h₂)

@[deprecated (since := "2026-06-03")] alias isCaratheodory_diff := isCaratheodory_sdiff

/--
lemma `isCaratheodory_partialSups` / 引理 `isCaratheodory_partialSups`

English:
lemma isCaratheodory_partialSups
  statement: {ι : Type*} [Preorder ι] [LocallyFiniteOrderBot ι]
  proof: by
  simpa only [partialSups_apply, Finset.sup'_eq_sup, Finset.sup_set_eq_biUnion, ← Finset.mem_coe,
    Finset.coe_Iic] using .biUnion_of_finite (finite_Iic _) (fun j _ => h j)

中文:
引理 isCaratheodory_partialSups
  结论: {ι : 类型} [预序 ι] [LocallyFiniteOrderBot ι]
  证明: by
  simpa only [partialSups_apply, Finset.sup'_eq_sup, Finset.sup_set_eq_biUnion, ← Finset.mem_coe,
    Finset.coe_Iic] using .biUnion_of_finite (finite_Iic _) (fun j _ => h j)

Depends on / 依赖: Finset, Finset.coe_Iic, Finset.mem_coe, Finset.sup, Finset.sup_set_eq_biUnion, _eq_sup, biUnion_of_finite, coe_Iic, finite_Iic, mem_coe, partialSups_apply, sup_set_eq_biUnion
-/
lemma isCaratheodory_partialSups {ι : Type*} [Preorder ι] [LocallyFiniteOrderBot ι]
    {s : ι -> Set α} (h : forall i, m.IsCaratheodory (s i)) (i : ι) :
    m.IsCaratheodory (partialSups s i) := by
  simpa only [partialSups_apply, Finset.sup'_eq_sup, Finset.sup_set_eq_biUnion, ← Finset.mem_coe,
    Finset.coe_Iic] using .biUnion_of_finite (finite_Iic _) (fun j _ => h j)

/--
lemma `isCaratheodory_disjointed` / 引理 `isCaratheodory_disjointed`

English:
lemma isCaratheodory_disjointed
  statement: {ι : Type*} [Preorder ι] [LocallyFiniteOrderBot ι]
  proof: disjointedRec (fun _ j ht => m.isCaratheodory_sdiff ht <| h j) (h i)

中文:
引理 isCaratheodory_disjointed
  结论: {ι : 类型} [预序 ι] [LocallyFiniteOrderBot ι]
  证明: disjointedRec (fun _ j ht => m.isCaratheodory_sdiff ht <| h j) (h i)

Depends on / 依赖: disjointedRec, isCaratheodory_sdiff, m.isCaratheodory_sdiff
-/
lemma isCaratheodory_disjointed {ι : Type*} [Preorder ι] [LocallyFiniteOrderBot ι]
    {s : ι -> Set α} (h : forall i, m.IsCaratheodory (s i)) (i : ι) :
    m.IsCaratheodory (disjointed s i) :=
  disjointedRec (fun _ j ht => m.isCaratheodory_sdiff ht <| h j) (h i)

/--
theorem `isCaratheodory_sum` / 定理 `isCaratheodory_sum`

English:
theorem isCaratheodory_sum
  statement: {s : Nat -> Set α} (h : forall i, IsCaratheodory m (s i))

中文:
定理 isCaratheodory_sum
  结论: {s : 自然数 -> 集合 α} (h : 对任意 i, IsCaratheodory m (s i))
-/
theorem isCaratheodory_sum {s : Nat -> Set α} (h : forall i, IsCaratheodory m (s i))
    (hd : Pairwise (Disjoint on s)) {t : Set α} :
    forall {n}, (∑ i in Finset.range n, m (t inter s i)) = m (t inter ⋃ i < n, s i)
  | 0 => by simp
  | Nat.succ n => by
    rw [biUnion_lt_succ]; rw [Finset.sum_range_succ]; rw [Set.union_comm]; rw [isCaratheodory_sum h hd]; rw [m.measure_inter_union _ (h n)]; rw [add_comm]
    intro a
    simpa using fun (h₁ : a in s n) i (hi : i < n) h₂ => (hd (ne_of_gt hi)).le_bot ⟨h₁, h₂⟩

/--
theorem `isCaratheodory_iUnion_of_disjoint` / 定理 `isCaratheodory_iUnion_of_disjoint`

English:
theorem isCaratheodory_iUnion_of_disjoint
  statement: {s : Nat -> Set α} (h : forall i, IsCaratheodory m (s i))
  proof: by
  apply (isCaratheodory_iff_le' m).mpr
  intro t
  have hp : m (t inter ⋃ i, s i) <= ⨆ n, m (t inter ⋃ i < n, s i) := by
    convert! measure_iUnion_le (μ := m) fun i => t inter s i using 1
    · simp [inter_iUnion]
    · simp [ENNReal.tsum_eq_iSup_nat, isCaratheodory_sum m h hd]
  grw [hp, ENNRe

中文:
定理 isCaratheodory_iUnion_of_disjoint
  结论: {s : 自然数 -> 集合 α} (h : 对任意 i, IsCaratheodory m (s i))
  证明: by
  apply (isCaratheodory_iff_le' m).mpr
  intro t
  have hp : m (t inter ⋃ i, s i) <= ⨆ n, m (t inter ⋃ i < n, s i) := by
    convert! measure_iUnion_le (μ := m) fun i => t inter s i using 1
    · simp [inter_iUnion]
    · simp [ENNReal.tsum_eq_iSup_nat, isCaratheodory_sum m h hd]
  grw [hp, ENNRe

Depends on / 依赖: ENNReal, ENNReal.iSup_add, ENNReal.tsum_eq_iSup_nat, convert, iSup_add, iSup_le, iUnion_subset, inter_iUnion, isCaratheodory_iUnion_lt, isCaratheodory_iff_le, isCaratheodory_sum, measure_iUnion_le, tsum_eq_iSup_nat
-/
theorem isCaratheodory_iUnion_of_disjoint {s : Nat -> Set α} (h : forall i, IsCaratheodory m (s i))
    (hd : Pairwise (Disjoint on s)) : IsCaratheodory m (⋃ i, s i) := by
  apply (isCaratheodory_iff_le' m).mpr
  intro t
  have hp : m (t inter ⋃ i, s i) <= ⨆ n, m (t inter ⋃ i < n, s i) := by
    convert! measure_iUnion_le (μ := m) fun i => t inter s i using 1
    · simp [inter_iUnion]
    · simp [ENNReal.tsum_eq_iSup_nat, isCaratheodory_sum m h hd]
  grw [hp, ENNReal.iSup_add]
  refine iSup_le fun n => ?_
  rw [isCaratheodory_iUnion_lt _ (fun i _ => h i) t (n := n)]
  gcongr with i
  exact iUnion_subset fun _ => .rfl

/--
lemma `isCaratheodory_iUnion` / 引理 `isCaratheodory_iUnion`

English:
lemma isCaratheodory_iUnion
  given: {s : Nat -> Set α} (h : forall i, m.IsCaratheodory (s i))
  proof: by
  rw [← iUnion_disjointed]
  exact m.isCaratheodory_iUnion_of_disjoint (m.isCaratheodory_disjointed h)
    (disjoint_disjointed _)

中文:
引理 isCaratheodory_iUnion
  条件: {s : 自然数 -> 集合 α} (h : 对任意 i, m.IsCaratheodory (s i))
  证明: by
  rw [← iUnion_disjointed]
  exact m.isCaratheodory_iUnion_of_disjoint (m.isCaratheodory_disjointed h)
    (disjoint_disjointed _)

Depends on / 依赖: disjoint_disjointed, iUnion_disjointed, isCaratheodory_disjointed, isCaratheodory_iUnion_of_disjoint, m.isCaratheodory_disjointed, m.isCaratheodory_iUnion_of_disjoint
-/
lemma isCaratheodory_iUnion {s : Nat -> Set α} (h : forall i, m.IsCaratheodory (s i)) :
    m.IsCaratheodory (⋃ i, s i) := by
  rw [← iUnion_disjointed]
  exact m.isCaratheodory_iUnion_of_disjoint (m.isCaratheodory_disjointed h)
    (disjoint_disjointed _)

/--
theorem `f_iUnion` / 定理 `f_iUnion`

English:
theorem f_iUnion
  given: {s : Nat -> Set α} (h : forall i, IsCaratheodory m (s i)) (hd : Pairwise (Disjoint on s))
  proof: by
  refine le_antisymm (measure_iUnion_le s) ?_
  rw [ENNReal.tsum_eq_iSup_nat]
  refine iSup_le fun n => ?_
  have := @isCaratheodory_sum _ m _ h hd univ n
  simp only [inter_comm, inter_univ, univ_inter] at this; simp only [this]
  exact m.mono (iUnion₂_subset fun i _ => subset_iUnion _ i)

中文:
定理 f_iUnion
  条件: {s : 自然数 -> 集合 α} (h : 对任意 i, IsCaratheodory m (s i)) (hd : 两两 (Disjoint on s))
  证明: by
  refine le_antisymm (measure_iUnion_le s) ?_
  rw [ENNReal.tsum_eq_iSup_nat]
  refine iSup_le fun n => ?_
  have := @isCaratheodory_sum _ m _ h hd univ n
  simp only [inter_comm, inter_univ, univ_inter] at this; simp only [this]
  exact m.mono (iUnion₂_subset fun i _ => subset_iUnion _ i)

Depends on / 依赖: ENNReal, ENNReal.tsum_eq_iSup_nat, iSup_le, inter_comm, inter_univ, isCaratheodory_sum, le_antisymm, m.mono, measure_iUnion_le, subset_iUnion, tsum_eq_iSup_nat, univ_inter
-/
theorem f_iUnion {s : Nat -> Set α} (h : forall i, IsCaratheodory m (s i)) (hd : Pairwise (Disjoint on s)) :
    m (⋃ i, s i) = ∑' i, m (s i) := by
  refine le_antisymm (measure_iUnion_le s) ?_
  rw [ENNReal.tsum_eq_iSup_nat]
  refine iSup_le fun n => ?_
  have := @isCaratheodory_sum _ m _ h hd univ n
  simp only [inter_comm, inter_univ, univ_inter] at this; simp only [this]
  exact m.mono (iUnion₂_subset fun i _ => subset_iUnion _ i)

/--
Definition of `caratheodoryDynkin` / `caratheodoryDynkin` 的定义

English:
definition caratheodoryDynkin
  signature: : MeasurableSpace.DynkinSystem α where
  body: IsCaratheodory m
  has_empty := isCaratheodory_empty m
  has_compl s := isCaratheodory_compl m s
  has_iUnion_nat _ hf hn := by apply isCaratheodory_iUnion m hf

中文:
定义 caratheodoryDynkin
  签名: : 可测空间.DynkinSystem α where
  定义体: IsCaratheodory m
  has_empty := isCaratheodory_empty m
  has_compl s := isCaratheodory_compl m s
  has_iUnion_nat _ hf hn := by apply isCaratheodory_iUnion m hf

Depends on / 依赖: IsCaratheodory
-/
def caratheodoryDynkin : MeasurableSpace.DynkinSystem α where
  Has := IsCaratheodory m
  has_empty := isCaratheodory_empty m
  has_compl s := isCaratheodory_compl m s
  has_iUnion_nat _ hf hn := by apply isCaratheodory_iUnion m hf

/-- Given an outer measure `μ`, the Carathéodory-measurable space is
  defined such that `s` is measurable if `∀ t, μ t = μ (t ∩ s) + μ (t \ s)`. -/
@[instance_reducible]
/--
Definition of `caratheodory` / `caratheodory` 的定义

English:
definition caratheodory
  signature: : MeasurableSpace α
  body: by
  apply MeasurableSpace.DynkinSystem.toMeasurableSpace (caratheodoryDynkin m)
  intro s₁ s₂
  apply isCaratheodory_inter

中文:
定义 caratheodory
  签名: : 可测空间 α
  定义体: by
  apply MeasurableSpace.DynkinSystem.toMeasurableSpace (caratheodoryDynkin m)
  intro s₁ s₂
  apply isCaratheodory_inter
-/
protected def caratheodory : MeasurableSpace α := by
  apply MeasurableSpace.DynkinSystem.toMeasurableSpace (caratheodoryDynkin m)
  intro s₁ s₂
  apply isCaratheodory_inter

/--
theorem `isCaratheodory_iff` / 定理 `isCaratheodory_iff`

English:
theorem isCaratheodory_iff
  given: {s : Set α}
  proof: Iff.rfl

中文:
定理 isCaratheodory_iff
  条件: {s : 集合 α}
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem isCaratheodory_iff {s : Set α} :
    MeasurableSet[OuterMeasure.caratheodory m] s ↔ forall t, m t = m (t inter s) + m (t \ s) :=
  Iff.rfl

/--
theorem `isCaratheodory_iff_le` / 定理 `isCaratheodory_iff_le`

English:
theorem isCaratheodory_iff_le
  given: {s : Set α}
  proof: isCaratheodory_iff_le' m

中文:
定理 isCaratheodory_iff_le
  条件: {s : 集合 α}
  证明: isCaratheodory_iff_le' m

Depends on / 依赖: isCaratheodory_iff_le
-/
theorem isCaratheodory_iff_le {s : Set α} :
    MeasurableSet[OuterMeasure.caratheodory m] s ↔ forall t, m (t inter s) + m (t \ s) <= m t :=
  isCaratheodory_iff_le' m

/--
theorem `iUnion_eq_of_caratheodory` / 定理 `iUnion_eq_of_caratheodory`

English:
theorem iUnion_eq_of_caratheodory
  statement: {s : Nat -> Set α}
  proof: f_iUnion m h hd

中文:
定理 iUnion_eq_of_caratheodory
  结论: {s : 自然数 -> 集合 α}
  证明: f_iUnion m h hd
-/
protected theorem iUnion_eq_of_caratheodory {s : Nat -> Set α}
    (h : forall i, MeasurableSet[OuterMeasure.caratheodory m] (s i)) (hd : Pairwise (Disjoint on s)) :
    m (⋃ i, s i) = ∑' i, m (s i) :=
  f_iUnion m h hd

end CaratheodoryMeasurable

variable {α : Type*}

/--
theorem `ofFunction_caratheodory` / 定理 `ofFunction_caratheodory`

English:
theorem ofFunction_caratheodory
  statement: {m : Set α -> Real>=0∞} {s : Set α} {h₀ : m ∅ = 0}
  proof: by
  apply (isCaratheodory_iff_le _).mpr
  refine fun t => le_iInf fun f => le_iInf fun hf => ?_
  refine
    le_trans
      (add_le_add ((iInf_le_of_le fun i => f i inter s) <| iInf_le _ ?_)
        ((iInf_le_of_le fun i => f i \ s) <| iInf_le _ ?_))
      ?_
  · rw [← iUnion_inter]
    exact inter

中文:
定理 ofFunction_caratheodory
  结论: {m : 集合 α -> 实数>=0∞} {s : 集合 α} {h₀ : m ∅ = 0}
  证明: by
  apply (isCaratheodory_iff_le _).mpr
  refine fun t => le_iInf fun f => le_iInf fun hf => ?_
  refine
    le_trans
      (add_le_add ((iInf_le_of_le fun i => f i inter s) <| iInf_le _ ?_)
        ((iInf_le_of_le fun i => f i \ s) <| iInf_le _ ?_))
      ?_
  · rw [← iUnion_inter]
    exact inter

Depends on / 依赖: ENNReal, ENNReal.tsum_add, ENNReal.tsum_le_tsum, add_le_add, iInf_le, iInf_le_of_le, iUnion_inter, iUnion_sdiff, inter_subset_inter_left, isCaratheodory_iff_le, le_iInf, le_trans, sdiff_subset_sdiff_left, tsum_add, tsum_le_tsum
-/
theorem ofFunction_caratheodory {m : Set α -> Real>=0∞} {s : Set α} {h₀ : m ∅ = 0}
    (hs : forall t, m (t inter s) + m (t \ s) <= m t) :
    MeasurableSet[(OuterMeasure.ofFunction m h₀).caratheodory] s := by
  apply (isCaratheodory_iff_le _).mpr
  refine fun t => le_iInf fun f => le_iInf fun hf => ?_
  refine
    le_trans
      (add_le_add ((iInf_le_of_le fun i => f i inter s) <| iInf_le _ ?_)
        ((iInf_le_of_le fun i => f i \ s) <| iInf_le _ ?_))
      ?_
  · rw [← iUnion_inter]
    exact inter_subset_inter_left _ hf
  · rw [← iUnion_sdiff]
    exact sdiff_subset_sdiff_left hf
  · rw [← ENNReal.tsum_add]
    exact ENNReal.tsum_le_tsum fun i => hs _

/--
theorem `boundedBy_caratheodory` / 定理 `boundedBy_caratheodory`

English:
theorem boundedBy_caratheodory
  statement: {m : Set α -> Real>=0∞} {s : Set α}
  proof: by
  apply ofFunction_caratheodory; intro t
  rcases t.eq_empty_or_nonempty with rfl | h
  · simp [Set.not_nonempty_empty]
  · convert! le_trans _ (hs t)
    · simp [h]
    exact add_le_add iSup_const_le iSup_const_le

@[simp]

中文:
定理 boundedBy_caratheodory
  结论: {m : 集合 α -> 实数>=0∞} {s : 集合 α}
  证明: by
  apply ofFunction_caratheodory; intro t
  rcases t.eq_empty_or_nonempty with rfl | h
  · simp [Set.not_nonempty_empty]
  · convert! le_trans _ (hs t)
    · simp [h]
    exact add_le_add iSup_const_le iSup_const_le

@[simp]

Depends on / 依赖: Set.not_nonempty_empty, add_le_add, convert, eq_empty_or_nonempty, iSup_const_le, le_trans, not_nonempty_empty, ofFunction_caratheodory, t.eq_empty_or_nonempty
-/
theorem boundedBy_caratheodory {m : Set α -> Real>=0∞} {s : Set α}
    (hs : forall t, m (t inter s) + m (t \ s) <= m t) : MeasurableSet[(boundedBy m).caratheodory] s := by
  apply ofFunction_caratheodory; intro t
  rcases t.eq_empty_or_nonempty with rfl | h
  · simp [Set.not_nonempty_empty]
  · convert! le_trans _ (hs t)
    · simp [h]
    exact add_le_add iSup_const_le iSup_const_le

@[simp]
/--
theorem `zero_caratheodory` / 定理 `zero_caratheodory`

English:
theorem zero_caratheodory
  statement: (0 : OuterMeasure α).caratheodory = ⊤
  proof: top_unique fun _ _ _ => (add_zero _).symm

中文:
定理 zero_caratheodory
  结论: (0 : 外测度 α).caratheodory = ⊤
  证明: top_unique fun _ _ _ => (add_zero _).symm

Depends on / 依赖: add_zero, top_unique
-/
theorem zero_caratheodory : (0 : OuterMeasure α).caratheodory = ⊤ :=
  top_unique fun _ _ _ => (add_zero _).symm

/--
theorem `top_caratheodory` / 定理 `top_caratheodory`

English:
theorem top_caratheodory
  statement: (⊤ : OuterMeasure α).caratheodory = ⊤
  proof: top_unique fun s _ =>
    (isCaratheodory_iff_le _).2 fun t =>
      t.eq_empty_or_nonempty.elim (fun ht => by simp [ht]) fun ht => by
        simp only [ht, top_apply, le_top]

中文:
定理 top_caratheodory
  结论: (⊤ : 外测度 α).caratheodory = ⊤
  证明: top_unique fun s _ =>
    (isCaratheodory_iff_le _).2 fun t =>
      t.eq_empty_or_nonempty.elim (fun ht => by simp [ht]) fun ht => by
        simp only [ht, top_apply, le_top]

Depends on / 依赖: eq_empty_or_nonempty, isCaratheodory_iff_le, le_top, t.eq_empty_or_nonempty.elim, top_apply, top_unique
-/
theorem top_caratheodory : (⊤ : OuterMeasure α).caratheodory = ⊤ :=
  top_unique fun s _ =>
    (isCaratheodory_iff_le _).2 fun t =>
      t.eq_empty_or_nonempty.elim (fun ht => by simp [ht]) fun ht => by
        simp only [ht, top_apply, le_top]

/--
theorem `le_add_caratheodory` / 定理 `le_add_caratheodory`

English:
theorem le_add_caratheodory
  given: (m₁ m₂ : OuterMeasure α)
  proof: fun s ⟨hs₁, hs₂⟩ t => by simp [hs₁ t, hs₂ t, add_left_comm, add_assoc]

中文:
定理 le_add_caratheodory
  条件: (m₁ m₂ : 外测度 α)
  证明: fun s ⟨hs₁, hs₂⟩ t => by simp [hs₁ t, hs₂ t, add_left_comm, add_assoc]

Depends on / 依赖: add_assoc, add_left_comm
-/
theorem le_add_caratheodory (m₁ m₂ : OuterMeasure α) :
    m₁.caratheodory ⊓ m₂.caratheodory <= (m₁ + m₂ : OuterMeasure α).caratheodory :=
  fun s ⟨hs₁, hs₂⟩ t => by simp [hs₁ t, hs₂ t, add_left_comm, add_assoc]

/--
theorem `le_sum_caratheodory` / 定理 `le_sum_caratheodory`

English:
theorem le_sum_caratheodory
  given: {ι} (m : ι -> OuterMeasure α)
  proof: fun s h t => by
  simp [fun i => MeasurableSpace.measurableSet_iInf.1 h i t, ENNReal.tsum_add]

中文:
定理 le_sum_caratheodory
  条件: {ι} (m : ι -> 外测度 α)
  证明: fun s h t => by
  simp [fun i => MeasurableSpace.measurableSet_iInf.1 h i t, ENNReal.tsum_add]

Depends on / 依赖: ENNReal, ENNReal.tsum_add, MeasurableSpace, MeasurableSpace.measurableSet_iInf, measurableSet_iInf, tsum_add
-/
theorem le_sum_caratheodory {ι} (m : ι -> OuterMeasure α) :
    ⨅ i, (m i).caratheodory <= (sum m).caratheodory := fun s h t => by
  simp [fun i => MeasurableSpace.measurableSet_iInf.1 h i t, ENNReal.tsum_add]

/--
theorem `le_smul_caratheodory` / 定理 `le_smul_caratheodory`

English:
theorem le_smul_caratheodory
  given: (a : Real>=0∞) (m : OuterMeasure α)
  proof: fun s h t => by
      simp only [smul_apply, smul_eq_mul]
      rw [(isCaratheodory_iff m).mp h t]
      simp [mul_add]

@[simp]

中文:
定理 le_smul_caratheodory
  条件: (a : 实数>=0∞) (m : 外测度 α)
  证明: fun s h t => by
      simp only [smul_apply, smul_eq_mul]
      rw [(isCaratheodory_iff m).mp h t]
      simp [mul_add]

@[simp]

Depends on / 依赖: isCaratheodory_iff, mul_add, smul_apply, smul_eq_mul
-/
theorem le_smul_caratheodory (a : Real>=0∞) (m : OuterMeasure α) :
    m.caratheodory <= (a • m).caratheodory := fun s h t => by
      simp only [smul_apply, smul_eq_mul]
      rw [(isCaratheodory_iff m).mp h t]
      simp [mul_add]

@[simp]
/--
theorem `dirac_caratheodory` / 定理 `dirac_caratheodory`

English:
theorem dirac_caratheodory
  given: (a : α)
  statement: (dirac a).caratheodory = ⊤
  proof: top_unique fun s _ t => by
    by_cases ht : a in t; swap; · simp [ht]
    by_cases hs : a in s <;> simp [*]

中文:
定理 dirac_caratheodory
  条件: (a : α)
  结论: (dirac a).caratheodory = ⊤
  证明: top_unique fun s _ t => by
    by_cases ht : a in t; swap; · simp [ht]
    by_cases hs : a in s <;> simp [*]

Depends on / 依赖: top_unique
-/
theorem dirac_caratheodory (a : α) : (dirac a).caratheodory = ⊤ :=
  top_unique fun s _ t => by
    by_cases ht : a in t; swap; · simp [ht]
    by_cases hs : a in s <;> simp [*]

end OuterMeasure

end MeasureTheory
