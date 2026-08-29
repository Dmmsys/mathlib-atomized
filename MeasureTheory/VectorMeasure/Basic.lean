/-
Copyright (c) 2021 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying
-/
module

public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.Topology.Algebra.InfiniteSum.Module

/-!

# Vector-valued measures

This file defines vector-valued measures, which are σ-additive functions from a set to an
additive monoid `M` such that it maps the empty set and non-measurable sets to zero. In the case
that `M = ℝ`, we called the vector measure a signed measure and write `SignedMeasure α`.
Similarly, when `M = ℂ`, we call the measure a complex measure and write `ComplexMeasure α`
(defined in `MeasureTheory/Measure/Complex`).

## Main definitions

* `MeasureTheory.VectorMeasure` is a vector-valued, σ-additive function that maps the empty
  and non-measurable sets to zero.
* `MeasureTheory.VectorMeasure.map` is the pushforward of a vector measure along a function.
* `MeasureTheory.VectorMeasure.restrict` is the restriction of a vector measure on some set.

## Notation

* `v ≤[i] w` means that the vector measure `v` restricted on the set `i` is less than or equal
  to the vector measure `w` restricted on `i`, i.e. `v.restrict i ≤ w.restrict i`.

## Implementation notes

We require all non-measurable sets to be mapped to zero in order for the extensionality lemma
to only compare the underlying functions for measurable sets.

We use `HasSum` instead of `tsum` in the definition of vector measures in comparison to `Measure`
since this provides summability.

## Tags

vector measure, signed measure, complex measure
-/

@[expose] public section


noncomputable section

open NNReal ENNReal Filter

open scoped Topology Function -- required for scoped `on` notation
namespace MeasureTheory

variable {α β : Type*} {m : MeasurableSpace α}

/--
Definition of `VectorMeasure` / `VectorMeasure` 的定义

English:
structure VectorMeasure
  parameters: (α : Type*) [MeasurableSpace α] (M : Type*) [AddCommMonoid M]
  axioms and operations (4):
    - measureOf' : Set α -> M
    - empty' : measureOf' ∅ = 0
    - not_measurable'(⦃i) : Set α⦄ : ¬MeasurableSet i -> measureOf' i = 0
    - m_iUnion'(⦃f) : Nat -> Set α⦄ : (forall i, MeasurableSet (f i)) -> Pairwise (Disjoint on f) -> HasSum (fun i => measureOf' (f i)) (measureOf' (⋃ i, f i))

中文:
结构 向量测度
  参数: (α : 类型) [可测空间 α] (M : 类型) [加法交换幺半群 M]
  公理与运算 (4 个):
    - measureOf' : 集合 α -> M
    - empty' : measureOf' ∅ = 0
    - not_measurable'(⦃i) : 集合 α⦄ : ¬可测集 i -> measureOf' i = 0
    - m_iUnion'(⦃f) : 自然数 -> 集合 α⦄ : (对任意 i, 可测集 (f i)) -> 两两 (Disjoint on f) -> HasSum (fun i => measureOf' (f i)) (measureOf' (⋃ i, f i))
-/
structure VectorMeasure (α : Type*) [MeasurableSpace α] (M : Type*) [AddCommMonoid M]
    [TopologicalSpace M] where
  /-- The measure of sets -/
  measureOf' : Set α -> M
  /-- The empty set has measure zero -/
  empty' : measureOf' ∅ = 0
  /-- Non-measurable sets have measure zero -/
  not_measurable' ⦃i : Set α⦄ : ¬MeasurableSet i -> measureOf' i = 0
  /-- The measure is σ-additive -/
  m_iUnion' ⦃f : Nat -> Set α⦄ : (forall i, MeasurableSet (f i)) -> Pairwise (Disjoint on f) ->
    HasSum (fun i => measureOf' (f i)) (measureOf' (⋃ i, f i))

/--
Definition of `SignedMeasure` / `SignedMeasure` 的定义

English:
abbreviation SignedMeasure
  signature: (α : Type*) [MeasurableSpace α]
  body: VectorMeasure α Real

中文:
缩写 符号测度
  签名: (α : 类型) [可测空间 α]
  定义体: VectorMeasure α Real

Depends on / 依赖: VectorMeasure
-/
abbrev SignedMeasure (α : Type*) [MeasurableSpace α] :=
  VectorMeasure α Real

open Set

namespace VectorMeasure

section

variable {M : Type*} [AddCommMonoid M] [TopologicalSpace M]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: FunLike (VectorMeasure α M) (Set α) M
  body: VectorMeasure.measureOf'
  coe_injective v w h := by
    cases v; cases w; congr

@[simp]

中文:
实例 :
  签名: 函数状 (向量测度 α M) (集合 α) M
  定义体: VectorMeasure.measureOf'
  coe_injective v w h := by
    cases v; cases w; congr

@[simp]

Depends on / 依赖: VectorMeasure, VectorMeasure.measureOf, measureOf
-/
instance : FunLike (VectorMeasure α M) (Set α) M where
  coe := VectorMeasure.measureOf'
  coe_injective v w h := by
    cases v; cases w; congr

@[simp]
/--
theorem `coe_mk` / 定理 `coe_mk`

English:
theorem coe_mk
  given: (v : Set α -> M) (h₁) (h₂) (h₃)
  statement: (mk v h₁ h₂ h₃ : VectorMeasure α M) = v
  proof: rfl

initialize_simps_projections VectorMeasure (measureOf' -> apply)

@[simp]

中文:
定理 coe_mk
  条件: (v : 集合 α -> M) (h₁) (h₂) (h₃)
  结论: (mk v h₁ h₂ h₃ : 向量测度 α M) = v
  证明: rfl

initialize_simps_projections VectorMeasure (measureOf' -> apply)

@[simp]
-/
theorem coe_mk (v : Set α -> M) (h₁) (h₂) (h₃) : (mk v h₁ h₂ h₃ : VectorMeasure α M) = v := rfl

initialize_simps_projections VectorMeasure (measureOf' -> apply)

@[simp]
/--
theorem `empty` / 定理 `empty`

English:
theorem empty
  given: (v : VectorMeasure α M)
  statement: v ∅ = 0
  proof: v.empty'

@[simp]

中文:
定理 empty
  条件: (v : 向量测度 α M)
  结论: v ∅ = 0
  证明: v.empty'

@[simp]

Depends on / 依赖: v.empty
-/
theorem empty (v : VectorMeasure α M) : v ∅ = 0 :=
  v.empty'

@[simp]
/--
theorem `not_measurable` / 定理 `not_measurable`

English:
theorem not_measurable
  given: (v : VectorMeasure α M) {i : Set α} (hi : ¬MeasurableSet i)
  statement: v i = 0
  proof: v.not_measurable' hi

中文:
定理 not_measurable
  条件: (v : 向量测度 α M) {i : 集合 α} (hi : ¬可测集 i)
  结论: v i = 0
  证明: v.not_measurable' hi

Depends on / 依赖: not_measurable, v.not_measurable
-/
theorem not_measurable (v : VectorMeasure α M) {i : Set α} (hi : ¬MeasurableSet i) : v i = 0 :=
  v.not_measurable' hi

/--
theorem `m_iUnion` / 定理 `m_iUnion`

English:
theorem m_iUnion
  statement: (v : VectorMeasure α M) {f : Nat -> Set α} (hf₁ : forall i, MeasurableSet (f i))
  proof: v.m_iUnion' hf₁ hf₂

@[deprecated (since := "2026-06-10")] alias coe_injective := DFunLike.coe_injective

@[deprecated (since := "2026-06-10")] alias ext_iff' := DFunLike.ext_iff

中文:
定理 m_iUnion
  结论: (v : 向量测度 α M) {f : 自然数 -> 集合 α} (hf₁ : 对任意 i, 可测集 (f i))
  证明: v.m_iUnion' hf₁ hf₂

@[deprecated (since := "2026-06-10")] alias coe_injective := DFunLike.coe_injective

@[deprecated (since := "2026-06-10")] alias ext_iff' := DFunLike.ext_iff

Depends on / 依赖: m_iUnion, v.m_iUnion
-/
theorem m_iUnion (v : VectorMeasure α M) {f : Nat -> Set α} (hf₁ : forall i, MeasurableSet (f i))
    (hf₂ : Pairwise (Disjoint on f)) : HasSum (fun i => v (f i)) (v (⋃ i, f i)) :=
  v.m_iUnion' hf₁ hf₂

@[deprecated (since := "2026-06-10")] alias coe_injective := DFunLike.coe_injective

@[deprecated (since := "2026-06-10")] alias ext_iff' := DFunLike.ext_iff

/--
theorem `ext_iff` / 定理 `ext_iff`

English:
theorem ext_iff
  given: (v w : VectorMeasure α M)
  statement: v = w ↔ forall i : Set α, MeasurableSet i -> v i = w i
  proof: by
  constructor
  · rintro rfl _ _
    rfl
  · rw [DFunLike.ext_iff]
    intro h i
    by_cases hi : MeasurableSet i
    · exact h i hi
    · simp_rw [not_measurable _ hi]

@[ext]

中文:
定理 ext_iff
  条件: (v w : 向量测度 α M)
  结论: v = w ↔ 对任意 i : 集合 α, 可测集 i -> v i = w i
  证明: by
  constructor
  · rintro rfl _ _
    rfl
  · rw [DFunLike.ext_iff]
    intro h i
    by_cases hi : MeasurableSet i
    · exact h i hi
    · simp_rw [not_measurable _ hi]

@[ext]

Depends on / 依赖: DFunLike, DFunLike.ext_iff, MeasurableSet, ext_iff, not_measurable, simp_rw
-/
theorem ext_iff (v w : VectorMeasure α M) : v = w ↔ forall i : Set α, MeasurableSet i -> v i = w i := by
  constructor
  · rintro rfl _ _
    rfl
  · rw [DFunLike.ext_iff]
    intro h i
    by_cases hi : MeasurableSet i
    · exact h i hi
    · simp_rw [not_measurable _ hi]

@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: {s t : VectorMeasure α M} (h : forall i : Set α, MeasurableSet i -> s i = t i)
  statement: s = t
  proof: (ext_iff s t).2 h

中文:
定理 ext
  条件: {s t : 向量测度 α M} (h : 对任意 i : 集合 α, 可测集 i -> s i = t i)
  结论: s = t
  证明: (ext_iff s t).2 h

Depends on / 依赖: ext_iff
-/
theorem ext {s t : VectorMeasure α M} (h : forall i : Set α, MeasurableSet i -> s i = t i) : s = t :=
  (ext_iff s t).2 h

variable [Countable β] {v : VectorMeasure α M} {f : β -> Set α}

/--
theorem `hasSum_of_disjoint_iUnion` / 定理 `hasSum_of_disjoint_iUnion`

English:
theorem hasSum_of_disjoint_iUnion
  given: (hm : forall i, MeasurableSet (f i)) (hd : Pairwise (Disjoint on f))
  proof: by
  rcases Countable.exists_injective_nat β with ⟨e, he⟩
  rw [← hasSum_extend_zero he]
  convert! m_iUnion v (f := Function.extend e f fun _ => ∅) _ _
  · simp only [Pi.zero_def, Function.apply_extend v, Function.comp_def, empty]
  · exact (iSup_extend_bot he _).symm
  · simp [Function.apply_extend MeasurableSet, Function.comp_def, hm]
  · exact hd.disjoint_extend_bot (he.factorsThrough _)

中文:
定理 hasSum_of_disjoint_iUnion
  条件: (hm : 对任意 i, 可测集 (f i)) (hd : 两两 (Disjoint on f))
  证明: by
  rcases Countable.exists_injective_nat β with ⟨e, he⟩
  rw [← hasSum_extend_zero he]
  convert! m_iUnion v (f := Function.extend e f fun _ => ∅) _ _
  · simp only [Pi.zero_def, Function.apply_extend v, Function.comp_def, empty]
  · exact (iSup_extend_bot he _).symm
  · simp [Function.apply_extend MeasurableSet, Function.comp_def, hm]
  · exact hd.disjoint_extend_bot (he.factorsThrough _)

Depends on / 依赖: Countable, Countable.exists_injective_nat, Function, Function.apply_extend, Function.comp_def, Function.extend, MeasurableSet, Pi.zero_def, apply_extend, comp_def, convert, disjoint_extend_bot, exists_injective_nat, extend, factorsThrough, hasSum_extend_zero, hd.disjoint_extend_bot, he.factorsThrough, iSup_extend_bot, m_iUnion
-/
theorem hasSum_of_disjoint_iUnion (hm : forall i, MeasurableSet (f i)) (hd : Pairwise (Disjoint on f)) :
    HasSum (fun i => v (f i)) (v (⋃ i, f i)) := by
  rcases Countable.exists_injective_nat β with ⟨e, he⟩
  rw [← hasSum_extend_zero he]
  convert! m_iUnion v (f := Function.extend e f fun _ => ∅) _ _
  · simp only [Pi.zero_def, Function.apply_extend v, Function.comp_def, empty]
  · exact (iSup_extend_bot he _).symm
  · simp [Function.apply_extend MeasurableSet, Function.comp_def, hm]
  · exact hd.disjoint_extend_bot (he.factorsThrough _)

/--
theorem `of_if` / 定理 `of_if`

English:
theorem of_if
  given: {ι : Type*} {x : ι} {B : Set ι} {A : Set α} [Decidable (x in B)]
  proof: by
  split_ifs with h <;> simp [h]

中文:
定理 of_if
  条件: {ι : 类型} {x : ι} {B : 集合 ι} {A : 集合 α} [可判定 (x in B)]
  证明: by
  split_ifs with h <;> simp [h]

Depends on / 依赖: split_ifs
-/
theorem of_if {ι : Type*} {x : ι} {B : Set ι} {A : Set α} [Decidable (x in B)] :
    v (if x in B then A else ∅) = indicator B (fun _ => v A) x := by
  split_ifs with h <;> simp [h]

variable [T2Space M]

/--
theorem `of_disjoint_iUnion` / 定理 `of_disjoint_iUnion`

English:
theorem of_disjoint_iUnion
  given: (hm : forall i, MeasurableSet (f i)) (hd : Pairwise (Disjoint on f))
  proof: (hasSum_of_disjoint_iUnion hm hd).tsum_eq.symm

中文:
定理 of_disjoint_iUnion
  条件: (hm : 对任意 i, 可测集 (f i)) (hd : 两两 (Disjoint on f))
  证明: (hasSum_of_disjoint_iUnion hm hd).tsum_eq.symm

Depends on / 依赖: hasSum_of_disjoint_iUnion, tsum_eq, tsum_eq.symm
-/
theorem of_disjoint_iUnion (hm : forall i, MeasurableSet (f i)) (hd : Pairwise (Disjoint on f)) :
    v (⋃ i, f i) = ∑' i, v (f i) :=
  (hasSum_of_disjoint_iUnion hm hd).tsum_eq.symm

/--
theorem `of_biUnion` / 定理 `of_biUnion`

English:
theorem of_biUnion
  statement: {ι : Type*} {s : Set ι} {f : ι -> Set α} (hs : s.Countable)
  proof: by
  have := hs.toEncodable
  rw [biUnion_eq_iUnion]
  apply of_disjoint_iUnion
  · exact fun x => h x x.2
  · exact hd.on_injective Subtype.coe_injective fun x => x.2

中文:
定理 of_biUnion
  结论: {ι : 类型} {s : 集合 ι} {f : ι -> 集合 α} (hs : s.可数)
  证明: by
  have := hs.toEncodable
  rw [biUnion_eq_iUnion]
  apply of_disjoint_iUnion
  · exact fun x => h x x.2
  · exact hd.on_injective Subtype.coe_injective fun x => x.2

Depends on / 依赖: Subtype, Subtype.coe_injective, biUnion_eq_iUnion, coe_injective, hd.on_injective, hs.toEncodable, of_disjoint_iUnion, on_injective, toEncodable
-/
theorem of_biUnion {ι : Type*} {s : Set ι} {f : ι -> Set α} (hs : s.Countable)
    (hd : s.Pairwise (Disjoint on f)) (h : forall b in s, MeasurableSet (f b)) :
    v (⋃ b in s, f b) = ∑' p : s, v (f p) := by
  have := hs.toEncodable
  rw [biUnion_eq_iUnion]
  apply of_disjoint_iUnion
  · exact fun x => h x x.2
  · exact hd.on_injective Subtype.coe_injective fun x => x.2

/--
theorem `of_biUnion_finset` / 定理 `of_biUnion_finset`

English:
theorem of_biUnion_finset
  statement: {ι : Type*} {s : Finset ι} {f : ι -> Set α} (hd : PairwiseDisjoint (↑s) f)
  proof: by
  rw [← Finset.sum_attach]; rw [Finset.attach_eq_univ]; rw [← tsum_fintype (L := .unconditional s)]
  exact of_biUnion s.countable_toSet hd hm

中文:
定理 of_biUnion_finset
  结论: {ι : 类型} {s : 有限集 ι} {f : ι -> 集合 α} (hd : PairwiseDisjoint (↑s) f)
  证明: by
  rw [← Finset.sum_attach]; rw [Finset.attach_eq_univ]; rw [← tsum_fintype (L := .unconditional s)]
  exact of_biUnion s.countable_toSet hd hm

Depends on / 依赖: Finset, Finset.attach_eq_univ, Finset.sum_attach, attach_eq_univ, countable_toSet, of_biUnion, s.countable_toSet, sum_attach, tsum_fintype, unconditional
-/
theorem of_biUnion_finset {ι : Type*} {s : Finset ι} {f : ι -> Set α} (hd : PairwiseDisjoint (↑s) f)
    (hm : forall b in s, MeasurableSet (f b)) : v (⋃ b in s, f b) = ∑ p in s, v (f p) := by
  rw [← Finset.sum_attach]; rw [Finset.attach_eq_univ]; rw [← tsum_fintype (L := .unconditional s)]
  exact of_biUnion s.countable_toSet hd hm

/--
theorem `of_union` / 定理 `of_union`

English:
theorem of_union
  given: {A B : Set α} (h : Disjoint A B) (hA : MeasurableSet A) (hB : MeasurableSet B)
  proof: by
  rw [Set.union_eq_iUnion]; rw [of_disjoint_iUnion]; rw [tsum_fintype]; rw [Fintype.sum_bool]; rw [cond]; rw [cond]
  exacts [fun b => Bool.casesOn b hB hA, pairwise_disjoint_on_bool.2 h]

中文:
定理 of_union
  条件: {A B : 集合 α} (h : Disjoint A B) (hA : 可测集 A) (hB : 可测集 B)
  证明: by
  rw [Set.union_eq_iUnion]; rw [of_disjoint_iUnion]; rw [tsum_fintype]; rw [Fintype.sum_bool]; rw [cond]; rw [cond]
  exacts [fun b => Bool.casesOn b hB hA, pairwise_disjoint_on_bool.2 h]

Depends on / 依赖: Bool.casesOn, Fintype, Fintype.sum_bool, Set.union_eq_iUnion, casesOn, exacts, of_disjoint_iUnion, pairwise_disjoint_on_bool, sum_bool, tsum_fintype, union_eq_iUnion
-/
theorem of_union {A B : Set α} (h : Disjoint A B) (hA : MeasurableSet A) (hB : MeasurableSet B) :
    v (A union B) = v A + v B := by
  rw [Set.union_eq_iUnion]; rw [of_disjoint_iUnion]; rw [tsum_fintype]; rw [Fintype.sum_bool]; rw [cond]; rw [cond]
  exacts [fun b => Bool.casesOn b hB hA, pairwise_disjoint_on_bool.2 h]

/--
theorem `of_add_of_sdiff` / 定理 `of_add_of_sdiff`

English:
theorem of_add_of_sdiff
  given: {A B : Set α} (hA : MeasurableSet A) (hB : MeasurableSet B) (h : A subseteq B)
  proof: by
  rw [← of_union (@Set.disjoint_sdiff_right _ A B) hA (hB.diff hA)]; rw [Set.union_sdiff_cancel h]

@[deprecated (since := "2026-06-03")] alias of_add_of_diff := of_add_of_sdiff

中文:
定理 of_add_of_sdiff
  条件: {A B : 集合 α} (hA : 可测集 A) (hB : 可测集 B) (h : A subseteq B)
  证明: by
  rw [← of_union (@Set.disjoint_sdiff_right _ A B) hA (hB.diff hA)]; rw [Set.union_sdiff_cancel h]

@[deprecated (since := "2026-06-03")] alias of_add_of_diff := of_add_of_sdiff

Depends on / 依赖: Set.disjoint_sdiff_right, Set.union_sdiff_cancel, disjoint_sdiff_right, hB.diff, of_union, union_sdiff_cancel
-/
theorem of_add_of_sdiff {A B : Set α} (hA : MeasurableSet A) (hB : MeasurableSet B) (h : A subseteq B) :
    v A + v (B \ A) = v B := by
  rw [← of_union (@Set.disjoint_sdiff_right _ A B) hA (hB.diff hA)]; rw [Set.union_sdiff_cancel h]

@[deprecated (since := "2026-06-03")] alias of_add_of_diff := of_add_of_sdiff

/--
theorem `of_sdiff` / 定理 `of_sdiff`

English:
theorem of_sdiff
  statement: {M : Type*} [AddCommGroup M] [TopologicalSpace M] [T2Space M]
  proof: by
  rw [← of_add_of_sdiff hA hB h]; rw [add_sub_cancel_left]

@[deprecated (since := "2026-06-03")] alias of_diff := of_sdiff

中文:
定理 of_sdiff
  结论: {M : 类型} [加法交换群 M] [拓扑空间 M] [T2空间 M]
  证明: by
  rw [← of_add_of_sdiff hA hB h]; rw [add_sub_cancel_left]

@[deprecated (since := "2026-06-03")] alias of_diff := of_sdiff

Depends on / 依赖: add_sub_cancel_left, of_add_of_sdiff
-/
theorem of_sdiff {M : Type*} [AddCommGroup M] [TopologicalSpace M] [T2Space M]
    {v : VectorMeasure α M} {A B : Set α} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (h : A subseteq B) : v (B \ A) = v B - v A := by
  rw [← of_add_of_sdiff hA hB h]; rw [add_sub_cancel_left]

@[deprecated (since := "2026-06-03")] alias of_diff := of_sdiff

/--
theorem `of_compl` / 定理 `of_compl`

English:
theorem of_compl
  statement: {M : Type*} [AddCommGroup M] [TopologicalSpace M] [T2Space M]
  proof: by
  simpa [compl_eq_univ_sdiff] using of_sdiff hA .univ (v := v) (subset_univ _)

中文:
定理 of_compl
  结论: {M : 类型} [加法交换群 M] [拓扑空间 M] [T2空间 M]
  证明: by
  simpa [compl_eq_univ_sdiff] using of_sdiff hA .univ (v := v) (subset_univ _)

Depends on / 依赖: compl_eq_univ_sdiff, of_sdiff, subset_univ
-/
theorem of_compl {M : Type*} [AddCommGroup M] [TopologicalSpace M] [T2Space M]
    {v : VectorMeasure α M} {A : Set α} (hA : MeasurableSet A) :
    v Aᶜ = v univ - v A := by
  simpa [compl_eq_univ_sdiff] using of_sdiff hA .univ (v := v) (subset_univ _)

/--
theorem `of_sdiff_of_sdiff_eq_zero` / 定理 `of_sdiff_of_sdiff_eq_zero`

English:
theorem of_sdiff_of_sdiff_eq_zero
  statement: {A B : Set α} (hA : MeasurableSet A) (hB : MeasurableSet B)
  proof: by
  symm
  calc
    v A = v (A \ B union A inter B) := by simp only [Set.sdiff_union_inter]
    _ = v (A \ B) + v (A inter B) := by
      rw [of_union]
      · rw [disjoint_comm]
        exact Set.disjoint_of_subset_left A.inter_subset_right disjoint_sdiff_self_right
      · exact hA.diff hB
      · exact hA.inter hB
    _ = v (A \ B) + v (A inter B union B \ A) := by
      rw [of_union]; rw [h']; rw [add_zero]
      · exact Set.disjoint_of_subset_left A.inter_subset_left disjoint_sdiff_self_right
      · exact hA.inter hB
      · exact hB.diff hA
    _ = v (A \ B) + v B := by rw [Set.union_comm, Set.inter_comm, Set.sdiff_union_inter]

@[deprecated (since := "2026-06-03")] alias of_diff_of_diff_eq_zero := of_sdiff_of_sdiff_eq_zero

中文:
定理 of_sdiff_of_sdiff_eq_zero
  结论: {A B : 集合 α} (hA : 可测集 A) (hB : 可测集 B)
  证明: by
  symm
  calc
    v A = v (A \ B union A inter B) := by simp only [Set.sdiff_union_inter]
    _ = v (A \ B) + v (A inter B) := by
      rw [of_union]
      · rw [disjoint_comm]
        exact Set.disjoint_of_subset_left A.inter_subset_right disjoint_sdiff_self_right
      · exact hA.diff hB
      · exact hA.inter hB
    _ = v (A \ B) + v (A inter B union B \ A) := by
      rw [of_union]; rw [h']; rw [add_zero]
      · exact Set.disjoint_of_subset_left A.inter_subset_left disjoint_sdiff_self_right
      · exact hA.inter hB
      · exact hB.diff hA
    _ = v (A \ B) + v B := by rw [Set.union_comm, Set.inter_comm, Set.sdiff_union_inter]

@[deprecated (since := "2026-06-03")] alias of_diff_of_diff_eq_zero := of_sdiff_of_sdiff_eq_zero

Depends on / 依赖: A.inter_subset_left, A.inter_subset_right, Set.disjoint_of_subset_left, Set.sdiff_union_inter, Std.Refl, Std.Total, Std.Total.to_refl, add_zero, disjoint_comm, disjoint_of_subset_left, disjoint_sdiff_self_right, hA.diff, hA.inter, hB.diff, inter_subset_left, inter_subset_right, of_union, sdiff_union_inter, to_refl
-/
theorem of_sdiff_of_sdiff_eq_zero {A B : Set α} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (h' : v (B \ A) = 0) : v (A \ B) + v B = v A := by
  symm
  calc
    v A = v (A \ B union A inter B) := by simp only [Set.sdiff_union_inter]
    _ = v (A \ B) + v (A inter B) := by
      rw [of_union]
      · rw [disjoint_comm]
        exact Set.disjoint_of_subset_left A.inter_subset_right disjoint_sdiff_self_right
      · exact hA.diff hB
      · exact hA.inter hB
    _ = v (A \ B) + v (A inter B union B \ A) := by
      rw [of_union]; rw [h']; rw [add_zero]
      · exact Set.disjoint_of_subset_left A.inter_subset_left disjoint_sdiff_self_right
      · exact hA.inter hB
      · exact hB.diff hA
    _ = v (A \ B) + v B := by rw [Set.union_comm, Set.inter_comm, Set.sdiff_union_inter]

@[deprecated (since := "2026-06-03")] alias of_diff_of_diff_eq_zero := of_sdiff_of_sdiff_eq_zero

/--
theorem `of_iUnion_nonneg` / 定理 `of_iUnion_nonneg`

English:
theorem of_iUnion_nonneg
  statement: {M : Type*} [TopologicalSpace M]
  proof: (v.of_disjoint_iUnion hf₁ hf₂).symm ▸ tsum_nonneg hf₃

中文:
定理 of_iUnion_nonneg
  结论: {M : 类型} [拓扑空间 M]
  证明: (v.of_disjoint_iUnion hf₁ hf₂).symm ▸ tsum_nonneg hf₃

Depends on / 依赖: of_disjoint_iUnion, tsum_nonneg, v.of_disjoint_iUnion
-/
theorem of_iUnion_nonneg {M : Type*} [TopologicalSpace M]
    [AddCommMonoid M] [PartialOrder M] [IsOrderedAddMonoid M]
    [OrderClosedTopology M] {v : VectorMeasure α M} (hf₁ : forall i, MeasurableSet (f i))
    (hf₂ : Pairwise (Disjoint on f)) (hf₃ : forall i, 0 <= v (f i)) : 0 <= v (⋃ i, f i) :=
  (v.of_disjoint_iUnion hf₁ hf₂).symm ▸ tsum_nonneg hf₃

/--
theorem `of_iUnion_nonpos` / 定理 `of_iUnion_nonpos`

English:
theorem of_iUnion_nonpos
  statement: {M : Type*} [TopologicalSpace M]
  proof: (v.of_disjoint_iUnion hf₁ hf₂).symm ▸ tsum_nonpos hf₃

中文:
定理 of_iUnion_nonpos
  结论: {M : 类型} [拓扑空间 M]
  证明: (v.of_disjoint_iUnion hf₁ hf₂).symm ▸ tsum_nonpos hf₃

Depends on / 依赖: of_disjoint_iUnion, tsum_nonpos, v.of_disjoint_iUnion
-/
theorem of_iUnion_nonpos {M : Type*} [TopologicalSpace M]
    [AddCommMonoid M] [PartialOrder M] [IsOrderedAddMonoid M]
    [OrderClosedTopology M] {v : VectorMeasure α M} (hf₁ : forall i, MeasurableSet (f i))
    (hf₂ : Pairwise (Disjoint on f)) (hf₃ : forall i, v (f i) <= 0) : v (⋃ i, f i) <= 0 :=
  (v.of_disjoint_iUnion hf₁ hf₂).symm ▸ tsum_nonpos hf₃

/--
theorem `of_nonneg_disjoint_union_eq_zero` / 定理 `of_nonneg_disjoint_union_eq_zero`

English:
theorem of_nonneg_disjoint_union_eq_zero
  statement: {s : SignedMeasure α} {A B : Set α} (h : Disjoint A B)
  proof: by
  rw [of_union h hA₁ hB₁] at hAB
  linarith

中文:
定理 of_nonneg_disjoint_union_eq_zero
  结论: {s : 符号测度 α} {A B : 集合 α} (h : Disjoint A B)
  证明: by
  rw [of_union h hA₁ hB₁] at hAB
  linarith

Depends on / 依赖: of_union
-/
theorem of_nonneg_disjoint_union_eq_zero {s : SignedMeasure α} {A B : Set α} (h : Disjoint A B)
    (hA₁ : MeasurableSet A) (hB₁ : MeasurableSet B) (hA₂ : 0 <= s A) (hB₂ : 0 <= s B)
    (hAB : s (A union B) = 0) : s A = 0 := by
  rw [of_union h hA₁ hB₁] at hAB
  linarith

/--
theorem `of_nonpos_disjoint_union_eq_zero` / 定理 `of_nonpos_disjoint_union_eq_zero`

English:
theorem of_nonpos_disjoint_union_eq_zero
  statement: {s : SignedMeasure α} {A B : Set α} (h : Disjoint A B)
  proof: by
  rw [of_union h hA₁ hB₁] at hAB
  linarith

中文:
定理 of_nonpos_disjoint_union_eq_zero
  结论: {s : 符号测度 α} {A B : 集合 α} (h : Disjoint A B)
  证明: by
  rw [of_union h hA₁ hB₁] at hAB
  linarith

Depends on / 依赖: of_union
-/
theorem of_nonpos_disjoint_union_eq_zero {s : SignedMeasure α} {A B : Set α} (h : Disjoint A B)
    (hA₁ : MeasurableSet A) (hB₁ : MeasurableSet B) (hA₂ : s A <= 0) (hB₂ : s B <= 0)
    (hAB : s (A union B) = 0) : s A = 0 := by
  rw [of_union h hA₁ hB₁] at hAB
  linarith

/--
theorem `tendsto_vectorMeasure_iUnion_atTop_nat` / 定理 `tendsto_vectorMeasure_iUnion_atTop_nat`

English:
theorem tendsto_vectorMeasure_iUnion_atTop_nat
  proof: by
  set t : Nat -> Set α := disjointed s
  have ht n : MeasurableSet (t n) := .disjointed (fun n => hs n) n
  have : HasSum (fun n => v (t n)) (v (⋃ n, s n)) := by
    rw [← iUnion_disjointed]
    apply m_iUnion _ ht (disjoint_disjointed _)
  convert! (HasSum.tendsto_sum_nat this).comp (tendsto_add_atTop_nat 1) with n
  dsimp
  rw [← of_biUnion_finset]
  · rw [biUnion_range_succ_disjointed, Monotone.partialSups_eq hm]
  · exact fun i hi j hj hij => disjoint_disjointed _ hij
  · exact fun b hb => ht _

中文:
定理 tendsto_vectorMeasure_iUnion_atTop_nat
  证明: by
  set t : Nat -> Set α := disjointed s
  have ht n : MeasurableSet (t n) := .disjointed (fun n => hs n) n
  have : HasSum (fun n => v (t n)) (v (⋃ n, s n)) := by
    rw [← iUnion_disjointed]
    apply m_iUnion _ ht (disjoint_disjointed _)
  convert! (HasSum.tendsto_sum_nat this).comp (tendsto_add_atTop_nat 1) with n
  dsimp
  rw [← of_biUnion_finset]
  · rw [biUnion_range_succ_disjointed, Monotone.partialSups_eq hm]
  · exact fun i hi j hj hij => disjoint_disjointed _ hij
  · exact fun b hb => ht _

Depends on / 依赖: HasSum, HasSum.tendsto_sum_nat, MeasurableSet, Monotone, Monotone.partialSups_eq, biUnion_range_succ_disjointed, convert, disjoint_disjointed, disjointed, iUnion_disjointed, m_iUnion, of_biUnion_finset, partialSups_eq, tendsto_add_atTop_nat, tendsto_sum_nat
-/
theorem tendsto_vectorMeasure_iUnion_atTop_nat
    {s : Nat -> Set α} (hm : Monotone s) (hs : forall i, MeasurableSet (s i)) :
    Tendsto (fun n => v (s n)) atTop (𝓝 (v (⋃ n, s n))) := by
  set t : Nat -> Set α := disjointed s
  have ht n : MeasurableSet (t n) := .disjointed (fun n => hs n) n
  have : HasSum (fun n => v (t n)) (v (⋃ n, s n)) := by
    rw [← iUnion_disjointed]
    apply m_iUnion _ ht (disjoint_disjointed _)
  convert! (HasSum.tendsto_sum_nat this).comp (tendsto_add_atTop_nat 1) with n
  dsimp
  rw [← of_biUnion_finset]
  · rw [biUnion_range_succ_disjointed, Monotone.partialSups_eq hm]
  · exact fun i hi j hj hij => disjoint_disjointed _ hij
  · exact fun b hb => ht _

/--
theorem `tendsto_vectorMeasure_iInter_atTop_nat` / 定理 `tendsto_vectorMeasure_iInter_atTop_nat`

English:
theorem tendsto_vectorMeasure_iInter_atTop_nat
  proof: by
  have I n : v (s n) = v univ - v (s n)ᶜ := by simp [of_compl (hs n)]
  have J : v (⋂ n, s n) = v univ - v (⋃ n, (s n)ᶜ) := by
    rw [← of_compl (MeasurableSet.iUnion (fun n => (hs n).compl))]
    simp
  simp_rw [I, J]
  apply tendsto_const_nhds.sub
  exact tendsto_vectorMeasure_iUnion_atTop_nat (fun i j hij => by simpa using hm hij)
    (fun i => (hs i).compl)

中文:
定理 tendsto_vectorMeasure_i整数er_atTop_nat
  证明: by
  have I n : v (s n) = v univ - v (s n)ᶜ := by simp [of_compl (hs n)]
  have J : v (⋂ n, s n) = v univ - v (⋃ n, (s n)ᶜ) := by
    rw [← of_compl (MeasurableSet.iUnion (fun n => (hs n).compl))]
    simp
  simp_rw [I, J]
  apply tendsto_const_nhds.sub
  exact tendsto_vectorMeasure_iUnion_atTop_nat (fun i j hij => by simpa using hm hij)
    (fun i => (hs i).compl)

Depends on / 依赖: MeasurableSet, MeasurableSet.iUnion, iUnion, of_compl, simp_rw, tendsto_const_nhds, tendsto_const_nhds.sub, tendsto_vectorMeasure_iUnion_atTop_nat
-/
theorem tendsto_vectorMeasure_iInter_atTop_nat
    {M : Type*} [AddCommGroup M] [TopologicalSpace M] [T2Space M] [ContinuousSub M]
    {v : VectorMeasure α M} {s : Nat -> Set α} (hm : Antitone s) (hs : forall i, MeasurableSet (s i)) :
    Tendsto (fun n => v (s n)) atTop (𝓝 (v (⋂ n, s n))) := by
  have I n : v (s n) = v univ - v (s n)ᶜ := by simp [of_compl (hs n)]
  have J : v (⋂ n, s n) = v univ - v (⋃ n, (s n)ᶜ) := by
    rw [← of_compl (MeasurableSet.iUnion (fun n => (hs n).compl))]
    simp
  simp_rw [I, J]
  apply tendsto_const_nhds.sub
  exact tendsto_vectorMeasure_iUnion_atTop_nat (fun i j hij => by simpa using hm hij)
    (fun i => (hs i).compl)

/--
theorem `ext_of_generateFrom` / 定理 `ext_of_generateFrom`

English:
theorem ext_of_generateFrom
  statement: {M : Type*} [AddCommGroup M] [TopologicalSpace M] [T2Space M]
  proof: by
  ext s hs
  induction s, hs using MeasurableSpace.induction_on_inter hA hC with
  | empty => simp
  | basic t ht => exact hμν t ht
  | compl t htm iht =>
    simp [of_compl, iht, htm, h_univ]
  | iUnion f hfd hfm ihf =>
    simp [of_disjoint_iUnion, hfm, hfd, ihf]

中文:
定理 ext_of_generateFrom
  结论: {M : 类型} [加法交换群 M] [拓扑空间 M] [T2空间 M]
  证明: by
  ext s hs
  induction s, hs using MeasurableSpace.induction_on_inter hA hC with
  | empty => simp
  | basic t ht => exact hμν t ht
  | compl t htm iht =>
    simp [of_compl, iht, htm, h_univ]
  | iUnion f hfd hfm ihf =>
    simp [of_disjoint_iUnion, hfm, hfd, ihf]

Depends on / 依赖: MeasurableSpace, MeasurableSpace.induction_on_inter, h_univ, iUnion, induction_on_inter, of_compl, of_disjoint_iUnion
-/
theorem ext_of_generateFrom {M : Type*} [AddCommGroup M] [TopologicalSpace M] [T2Space M]
    {X : Type*} {mX : MeasurableSpace X} {μ ν : VectorMeasure X M}
    (C : Set (Set X)) (hμν : forall s in C, μ s = ν s)
    (hA : mX = MeasurableSpace.generateFrom C) (hC : IsPiSystem C)
    (h_univ : μ Set.univ = ν Set.univ) : μ = ν := by
  ext s hs
  induction s, hs using MeasurableSpace.induction_on_inter hA hC with
  | empty => simp
  | basic t ht => exact hμν t ht
  | compl t htm iht =>
    simp [of_compl, iht, htm, h_univ]
  | iUnion f hfd hfm ihf =>
    simp [of_disjoint_iUnion, hfm, hfd, ihf]

end

section SMul

variable {M : Type*} [AddCommMonoid M] [TopologicalSpace M]
variable {R : Type*} [Semiring R] [DistribMulAction R M] [ContinuousConstSMul R M]

/-- Given a scalar `r` and a vector measure `v`, `smul r v` is the vector measure corresponding to
the set function `s : Set α => r • (v s)`. -/
@[instance_reducible]
/--
Definition of `smul` / `smul` 的定义

English:
definition smul
  signature: (r : R) (v : VectorMeasure α M)
  body: r • ⇑v
  empty' := by rw [Pi.smul_apply, empty, smul_zero]
  not_measurable' _ hi := by rw [Pi.smul_apply, v.not_measurable hi, smul_zero]
  m_iUnion' _ hf₁ hf₂ := by exact HasSum.const_smul _ (v.m_iUnion hf₁ hf₂)

中文:
定义 smul
  签名: (r : R) (v : 向量测度 α M)
  定义体: r • ⇑v
  empty' := by rw [Pi.smul_apply, empty, smul_zero]
  not_measurable' _ hi := by rw [Pi.smul_apply, v.not_measurable hi, smul_zero]
  m_iUnion' _ hf₁ hf₂ := by exact HasSum.const_smul _ (v.m_iUnion hf₁ hf₂)
-/
def smul (r : R) (v : VectorMeasure α M) : VectorMeasure α M where
  measureOf' := r • ⇑v
  empty' := by rw [Pi.smul_apply, empty, smul_zero]
  not_measurable' _ hi := by rw [Pi.smul_apply, v.not_measurable hi, smul_zero]
  m_iUnion' _ hf₁ hf₂ := by exact HasSum.const_smul _ (v.m_iUnion hf₁ hf₂)

/--
Instance `instSMul` / 实例 `instSMul`

English:
instance instSMul
  signature: : SMul R (VectorMeasure α M)
  body: ⟨smul⟩

中文:
实例 instSMul
  签名: : 标量乘法 R (向量测度 α M)
  定义体: ⟨smul⟩
-/
instance instSMul : SMul R (VectorMeasure α M) :=
  ⟨smul⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsSMulApply R (VectorMeasure α M) (Set α) M
  body: rfl

@[deprecated (since := "2026-06-10")] alias coe_smul := FunLike.coe_smul

@[deprecated (since := "2026-06-10")] protected alias smul_apply := smul_apply

中文:
实例 :
  签名: 是SMulApply R (向量测度 α M) (集合 α) M
  定义体: rfl

@[deprecated (since := "2026-06-10")] alias coe_smul := FunLike.coe_smul

@[deprecated (since := "2026-06-10")] protected alias smul_apply := smul_apply
-/
instance : IsSMulApply R (VectorMeasure α M) (Set α) M where
  smul_apply _ _ _ := rfl

@[deprecated (since := "2026-06-10")] alias coe_smul := FunLike.coe_smul

@[deprecated (since := "2026-06-10")] protected alias smul_apply := smul_apply

end SMul

section AddCommMonoid

variable {M : Type*} [AddCommMonoid M] [TopologicalSpace M]

/--
Instance `instZero` / 实例 `instZero`

English:
instance instZero
  signature: : Zero (VectorMeasure α M)
  body: ⟨⟨0, rfl, fun _ _ => rfl, fun _ _ _ => hasSum_zero⟩⟩

中文:
实例 instZero
  签名: : 零 (向量测度 α M)
  定义体: ⟨⟨0, rfl, fun _ _ => rfl, fun _ _ _ => hasSum_zero⟩⟩

Depends on / 依赖: hasSum_zero
-/
instance instZero : Zero (VectorMeasure α M) :=
  ⟨⟨0, rfl, fun _ _ => rfl, fun _ _ _ => hasSum_zero⟩⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsZeroApply (VectorMeasure α M) (Set α) M
  body: rfl

中文:
实例 :
  签名: 是ZeroApply (向量测度 α M) (集合 α) M
  定义体: rfl
-/
instance : IsZeroApply (VectorMeasure α M) (Set α) M where
  zero_apply _ := rfl

/--
Instance `instInhabited` / 实例 `instInhabited`

English:
instance instInhabited
  signature: : Inhabited (VectorMeasure α M)
  body: ⟨0⟩

@[nontriviality]

中文:
实例 instInhabited
  签名: : 可居 (向量测度 α M)
  定义体: ⟨0⟩

@[nontriviality]
-/
instance instInhabited : Inhabited (VectorMeasure α M) :=
  ⟨0⟩

@[nontriviality]
/--
lemma `apply_eq_zero_of_isEmpty` / 引理 `apply_eq_zero_of_isEmpty`

English:
lemma apply_eq_zero_of_isEmpty
  given: [IsEmpty α] (μ : VectorMeasure α M) (s : Set α)
  proof: by
  simp [eq_empty_of_isEmpty s]

中文:
引理 apply_eq_zero_of_isEmpty
  条件: [是空 α] (μ : 向量测度 α M) (s : 集合 α)
  证明: by
  simp [eq_empty_of_isEmpty s]

Depends on / 依赖: eq_empty_of_isEmpty, extend_partialOrder
-/
lemma apply_eq_zero_of_isEmpty [IsEmpty α] (μ : VectorMeasure α M) (s : Set α) :
    μ s = 0 := by
  simp [eq_empty_of_isEmpty s]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsEmpty
  signature: α] : Subsingleton (VectorMeasure α M)
  body: ⟨fun μ ν => by ext; rw [apply_eq_zero_of_isEmpty, apply_eq_zero_of_isEmpty]⟩

中文:
实例 [是空
  签名: α] : 子单例 (向量测度 α M)
  定义体: ⟨fun μ ν => by ext; rw [apply_eq_zero_of_isEmpty, apply_eq_zero_of_isEmpty]⟩

Depends on / 依赖: apply_eq_zero_of_isEmpty
-/
instance [IsEmpty α] : Subsingleton (VectorMeasure α M) :=
  ⟨fun μ ν => by ext; rw [apply_eq_zero_of_isEmpty, apply_eq_zero_of_isEmpty]⟩

/--
theorem `eq_zero_of_isEmpty` / 定理 `eq_zero_of_isEmpty`

English:
theorem eq_zero_of_isEmpty
  given: [IsEmpty α] (μ : VectorMeasure α M)
  statement: μ = 0
  proof: Subsingleton.elim μ 0

@[deprecated (since := "2026-06-10")] alias coe_zero := FunLike.coe_zero

@[deprecated (since := "2026-06-10")] protected alias zero_apply := zero_apply

中文:
定理 eq_zero_of_isEmpty
  条件: [是空 α] (μ : 向量测度 α M)
  结论: μ = 0
  证明: Subsingleton.elim μ 0

@[deprecated (since := "2026-06-10")] alias coe_zero := FunLike.coe_zero

@[deprecated (since := "2026-06-10")] protected alias zero_apply := zero_apply

Depends on / 依赖: Subsingleton, Subsingleton.elim
-/
theorem eq_zero_of_isEmpty [IsEmpty α] (μ : VectorMeasure α M) : μ = 0 :=
  Subsingleton.elim μ 0

@[deprecated (since := "2026-06-10")] alias coe_zero := FunLike.coe_zero

@[deprecated (since := "2026-06-10")] protected alias zero_apply := zero_apply

variable [ContinuousAdd M]

/--
Definition of `add` / `add` 的定义

English:
definition add
  signature: (v w : VectorMeasure α M)
  body: v + w
  empty' := by simp
  not_measurable' _ hi := by rw [Pi.add_apply, v.not_measurable hi, w.not_measurable hi, add_zero]
  m_iUnion' _ hf₁ hf₂ := HasSum.add (v.m_iUnion hf₁ hf₂) (w.m_iUnion hf₁ hf₂)

中文:
定义 add
  签名: (v w : 向量测度 α M)
  定义体: v + w
  empty' := by simp
  not_measurable' _ hi := by rw [Pi.add_apply, v.not_measurable hi, w.not_measurable hi, add_zero]
  m_iUnion' _ hf₁ hf₂ := HasSum.add (v.m_iUnion hf₁ hf₂) (w.m_iUnion hf₁ hf₂)
-/
def add (v w : VectorMeasure α M) : VectorMeasure α M where
  measureOf' := v + w
  empty' := by simp
  not_measurable' _ hi := by rw [Pi.add_apply, v.not_measurable hi, w.not_measurable hi, add_zero]
  m_iUnion' _ hf₁ hf₂ := HasSum.add (v.m_iUnion hf₁ hf₂) (w.m_iUnion hf₁ hf₂)

/--
Instance `instAdd` / 实例 `instAdd`

English:
instance instAdd
  signature: : Add (VectorMeasure α M)
  body: ⟨add⟩

中文:
实例 instAdd
  签名: : 加法 (向量测度 α M)
  定义体: ⟨add⟩
-/
instance instAdd : Add (VectorMeasure α M) :=
  ⟨add⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsAddApply (VectorMeasure α M) (Set α) M
  body: rfl

@[deprecated (since := "2026-06-10")] alias coe_add := FunLike.coe_add

@[deprecated (since := "2026-06-10")] protected alias add_apply := add_apply

中文:
实例 :
  签名: 是加法Apply (向量测度 α M) (集合 α) M
  定义体: rfl

@[deprecated (since := "2026-06-10")] alias coe_add := FunLike.coe_add

@[deprecated (since := "2026-06-10")] protected alias add_apply := add_apply
-/
instance : IsAddApply (VectorMeasure α M) (Set α) M where
  add_apply _ _ _ := rfl

@[deprecated (since := "2026-06-10")] alias coe_add := FunLike.coe_add

@[deprecated (since := "2026-06-10")] protected alias add_apply := add_apply

/--
Instance `instAddCommMonoid` / 实例 `instAddCommMonoid`

English:
instance instAddCommMonoid
  signature: : AddCommMonoid (VectorMeasure α M)
  body: fast_instance% FunLike.addCommMonoid

@[deprecated (since := "2026-06-10")] alias coeFnAddMonoidHom := FunLike.coeAddMonoidHom

@[deprecated (since := "2026-06-10")] alias coeFnAddMonoidHom_apply := FunLike.coeAddMonoidHom_apply

@[deprecated (since := "2026-06-10")] alias coe_finsetSum := FunLike.coe_sum

中文:
实例 instAddCommMonoid
  签名: : 加法交换幺半群 (向量测度 α M)
  定义体: fast_instance% FunLike.addCommMonoid

@[deprecated (since := "2026-06-10")] alias coeFnAddMonoidHom := FunLike.coeAddMonoidHom

@[deprecated (since := "2026-06-10")] alias coeFnAddMonoidHom_apply := FunLike.coeAddMonoidHom_apply

@[deprecated (since := "2026-06-10")] alias coe_finsetSum := FunLike.coe_sum

Depends on / 依赖: FunLike, FunLike.addCommMonoid, addCommMonoid, fast_instance
-/
instance instAddCommMonoid : AddCommMonoid (VectorMeasure α M) :=
  fast_instance% FunLike.addCommMonoid

@[deprecated (since := "2026-06-10")] alias coeFnAddMonoidHom := FunLike.coeAddMonoidHom

@[deprecated (since := "2026-06-10")] alias coeFnAddMonoidHom_apply := FunLike.coeAddMonoidHom_apply

@[deprecated (since := "2026-06-10")] alias coe_finsetSum := FunLike.coe_sum

end AddCommMonoid

section AddCommGroup

variable {M : Type*} [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]

/--
Definition of `neg` / `neg` 的定义

English:
definition neg
  signature: (v : VectorMeasure α M)
  body: -v
  empty' := by simp
  not_measurable' _ hi := by rw [Pi.neg_apply, neg_eq_zero, v.not_measurable hi]
m_iUnion' _ hf₁ hf₂ := HasSum.neg v.m_iUnion hf₁ hf₂

中文:
定义 neg
  签名: (v : 向量测度 α M)
  定义体: -v
  empty' := by simp
  not_measurable' _ hi := by rw [Pi.neg_apply, neg_eq_zero, v.not_measurable hi]
m_iUnion' _ hf₁ hf₂ := HasSum.neg v.m_iUnion hf₁ hf₂
-/
def neg (v : VectorMeasure α M) : VectorMeasure α M where
  measureOf' := -v
  empty' := by simp
  not_measurable' _ hi := by rw [Pi.neg_apply, neg_eq_zero, v.not_measurable hi]
m_iUnion' _ hf₁ hf₂ := HasSum.neg v.m_iUnion hf₁ hf₂

/--
Instance `instNeg` / 实例 `instNeg`

English:
instance instNeg
  signature: : Neg (VectorMeasure α M)
  body: ⟨neg⟩

中文:
实例 instNeg
  签名: : 取负 (向量测度 α M)
  定义体: ⟨neg⟩
-/
instance instNeg : Neg (VectorMeasure α M) :=
  ⟨neg⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsNegApply (VectorMeasure α M) (Set α) M
  body: rfl

@[deprecated (since := "2026-06-10")] alias coe_neg := FunLike.coe_neg

@[deprecated (since := "2026-06-10")] protected alias neg_apply := neg_apply

中文:
实例 :
  签名: 是NegApply (向量测度 α M) (集合 α) M
  定义体: rfl

@[deprecated (since := "2026-06-10")] alias coe_neg := FunLike.coe_neg

@[deprecated (since := "2026-06-10")] protected alias neg_apply := neg_apply
-/
instance : IsNegApply (VectorMeasure α M) (Set α) M where
  neg_apply _ _ := rfl

@[deprecated (since := "2026-06-10")] alias coe_neg := FunLike.coe_neg

@[deprecated (since := "2026-06-10")] protected alias neg_apply := neg_apply

/--
Definition of `sub` / `sub` 的定义

English:
definition sub
  signature: (v w : VectorMeasure α M)
  body: v - w
  empty' := by simp
  not_measurable' _ hi := by rw [Pi.sub_apply, v.not_measurable hi, w.not_measurable hi, sub_zero]
  m_iUnion' _ hf₁ hf₂ := HasSum.sub (v.m_iUnion hf₁ hf₂) (w.m_iUnion hf₁ hf₂)

中文:
定义 sub
  签名: (v w : 向量测度 α M)
  定义体: v - w
  empty' := by simp
  not_measurable' _ hi := by rw [Pi.sub_apply, v.not_measurable hi, w.not_measurable hi, sub_zero]
  m_iUnion' _ hf₁ hf₂ := HasSum.sub (v.m_iUnion hf₁ hf₂) (w.m_iUnion hf₁ hf₂)
-/
def sub (v w : VectorMeasure α M) : VectorMeasure α M where
  measureOf' := v - w
  empty' := by simp
  not_measurable' _ hi := by rw [Pi.sub_apply, v.not_measurable hi, w.not_measurable hi, sub_zero]
  m_iUnion' _ hf₁ hf₂ := HasSum.sub (v.m_iUnion hf₁ hf₂) (w.m_iUnion hf₁ hf₂)

/--
Instance `instSub` / 实例 `instSub`

English:
instance instSub
  signature: : Sub (VectorMeasure α M)
  body: ⟨sub⟩

中文:
实例 instSub
  签名: : 减法 (向量测度 α M)
  定义体: ⟨sub⟩
-/
instance instSub : Sub (VectorMeasure α M) :=
  ⟨sub⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsSubApply (VectorMeasure α M) (Set α) M
  body: rfl

@[deprecated (since := "2026-06-10")] alias coe_sub := FunLike.coe_sub

@[deprecated (since := "2026-06-10")] protected alias sub_apply := sub_apply

中文:
实例 :
  签名: 是SubApply (向量测度 α M) (集合 α) M
  定义体: rfl

@[deprecated (since := "2026-06-10")] alias coe_sub := FunLike.coe_sub

@[deprecated (since := "2026-06-10")] protected alias sub_apply := sub_apply
-/
instance : IsSubApply (VectorMeasure α M) (Set α) M where
  sub_apply _ _ _ := rfl

@[deprecated (since := "2026-06-10")] alias coe_sub := FunLike.coe_sub

@[deprecated (since := "2026-06-10")] protected alias sub_apply := sub_apply

/--
Instance `instAddCommGroup` / 实例 `instAddCommGroup`

English:
instance instAddCommGroup
  signature: : AddCommGroup (VectorMeasure α M)
  body: fast_instance% FunLike.addCommGroup

中文:
实例 instAddCommGroup
  签名: : 加法交换群 (向量测度 α M)
  定义体: fast_instance% FunLike.addCommGroup

Depends on / 依赖: FunLike, FunLike.addCommGroup, addCommGroup, fast_instance
-/
instance instAddCommGroup : AddCommGroup (VectorMeasure α M) := fast_instance% FunLike.addCommGroup

end AddCommGroup

section DistribMulAction

variable {M : Type*} [AddCommMonoid M] [TopologicalSpace M]
variable {R : Type*} [Semiring R] [DistribMulAction R M] [ContinuousConstSMul R M]

/--
Instance `instDistribMulAction` / 实例 `instDistribMulAction`

English:
instance instDistribMulAction
  signature: [ContinuousAdd M]
  body: fast_instance% FunLike.distribMulAction

中文:
实例 instDistribMulAction
  签名: [连续加法 M]
  定义体: fast_instance% FunLike.distribMulAction

Depends on / 依赖: FunLike, FunLike.distribMulAction, distribMulAction, fast_instance
-/
instance instDistribMulAction [ContinuousAdd M] : DistribMulAction R (VectorMeasure α M) :=
  fast_instance% FunLike.distribMulAction

end DistribMulAction

section Module

variable {M : Type*} [AddCommMonoid M] [TopologicalSpace M]
variable {R : Type*} [Semiring R] [Module R M] [ContinuousConstSMul R M]

/--
Instance `instModule` / 实例 `instModule`

English:
instance instModule
  signature: [ContinuousAdd M]
  body: fast_instance% FunLike.module

中文:
实例 instModule
  签名: [连续加法 M]
  定义体: fast_instance% FunLike.module

Depends on / 依赖: FunLike, FunLike.module, fast_instance, module
-/
instance instModule [ContinuousAdd M] : Module R (VectorMeasure α M) :=
  fast_instance% FunLike.module

end Module

section Dirac

variable {M : Type*} [AddCommMonoid M] [TopologicalSpace M] [MeasurableSpace β]
  {x : β} {v : M} {s : Set β}

open scoped Classical in
/--
Definition of `dirac` / `dirac` 的定义

English:
definition dirac
  signature: (x : β) (v : M)
  body: if MeasurableSet s ∧ x in s then v else 0
  empty' := by simp
  not_measurable' := by simp +contextual
  m_iUnion' f f_meas f_disj := by
    by_cases hx : x in ⋃ i, f i; swap
    · simp only [mem_iUnion, not_exists] at hx
      simp [hx, hasSum_zero]
    have : MeasurableSet (⋃ i, f i) := by
      apply MeasurableSet.iUnion f_meas
    simp only [f_meas, true_and, MeasurableSet.iUnion f_meas, hx, and_self, ↓reduceIte]
    obtain ⟨j, hj⟩ : exists j, x in f j := by simpa using hx
    nth_rewrite 2 [show v = if x in f j then v else 0 by simp [hj]]
    apply hasSum_single
    intro i hi
    have : Disjoint (f i) (f j) := f_disj hi
    grind

中文:
定义 dirac
  签名: (x : β) (v : M)
  定义体: if MeasurableSet s ∧ x in s then v else 0
  empty' := by simp
  not_measurable' := by simp +contextual
  m_iUnion' f f_meas f_disj := by
    by_cases hx : x in ⋃ i, f i; swap
    · simp only [mem_iUnion, not_exists] at hx
      simp [hx, hasSum_zero]
    have : MeasurableSet (⋃ i, f i) := by
      apply MeasurableSet.iUnion f_meas
    simp only [f_meas, true_and, MeasurableSet.iUnion f_meas, hx, and_self, ↓reduceIte]
    obtain ⟨j, hj⟩ : exists j, x in f j := by simpa using hx
    nth_rewrite 2 [show v = if x in f j then v else 0 by simp [hj]]
    apply hasSum_single
    intro i hi
    have : Disjoint (f i) (f j) := f_disj hi
    grind

Depends on / 依赖: MeasurableSet
-/
def dirac (x : β) (v : M) : VectorMeasure β M where
  measureOf' s := if MeasurableSet s ∧ x in s then v else 0
  empty' := by simp
  not_measurable' := by simp +contextual
  m_iUnion' f f_meas f_disj := by
    by_cases hx : x in ⋃ i, f i; swap
    · simp only [mem_iUnion, not_exists] at hx
      simp [hx, hasSum_zero]
    have : MeasurableSet (⋃ i, f i) := by
      apply MeasurableSet.iUnion f_meas
    simp only [f_meas, true_and, MeasurableSet.iUnion f_meas, hx, and_self, ↓reduceIte]
    obtain ⟨j, hj⟩ : exists j, x in f j := by simpa using hx
    nth_rewrite 2 [show v = if x in f j then v else 0 by simp [hj]]
    apply hasSum_single
    intro i hi
    have : Disjoint (f i) (f j) := f_disj hi
    grind

/--
lemma `dirac_apply_of_mem` / 引理 `dirac_apply_of_mem`

English:
lemma dirac_apply_of_mem
  given: (hs : MeasurableSet s) (hx : x in s)
  statement: dirac x v s = v
  proof: if_pos (And.intro hs hx)

中文:
引理 dirac_apply_of_mem
  条件: (hs : 可测集 s) (hx : x in s)
  结论: dirac x v s = v
  证明: if_pos (And.intro hs hx)
-/
@[simp] lemma dirac_apply_of_mem (hs : MeasurableSet s) (hx : x in s) : dirac x v s = v :=
  if_pos (And.intro hs hx)

/--
lemma `dirac_apply_of_notMem` / 引理 `dirac_apply_of_notMem`

English:
lemma dirac_apply_of_notMem
  given: (hx : x ∉ s)
  statement: dirac x v s = 0
  proof: by
  simp [dirac, hx]

中文:
引理 dirac_apply_of_notMem
  条件: (hx : x ∉ s)
  结论: dirac x v s = 0
  证明: by
  simp [dirac, hx]
-/
@[simp] lemma dirac_apply_of_notMem (hx : x ∉ s) : dirac x v s = 0 := by
  simp [dirac, hx]

/--
lemma `dirac_zero` / 引理 `dirac_zero`

English:
lemma dirac_zero
  statement: dirac x (0 : M) = 0
  proof: by
  ext s hs
  simp [dirac]

中文:
引理 dirac_zero
  结论: dirac x (0 : M) = 0
  证明: by
  ext s hs
  simp [dirac]
-/
@[simp] lemma dirac_zero : dirac x (0 : M) = 0 := by
  ext s hs
  simp [dirac]

end Dirac

end VectorMeasure

namespace Measure

open scoped Classical in
/--
Definition of `toSignedMeasure` / `toSignedMeasure` 的定义

English:
definition toSignedMeasure
  signature: (μ : Measure α) [hμ : IsFiniteMeasure μ]
  body: if MeasurableSet s then μ.real s else 0
  empty' := by simp
  not_measurable' _ hi := if_neg hi
  m_iUnion' f hf₁ hf₂ := by
    simp only [*, MeasurableSet.iUnion hf₁, if_true, measure_iUnion hf₂ hf₁, measureReal_def]
    rw [ENNReal.tsum_toReal_eq]
    exacts [(summable_measure_toReal hf₁ hf₂).hasSum, fun _ => measure_ne_top _ _]

中文:
定义 toSignedMeasure
  签名: (μ : 测度 α) [hμ : 是有限测度 μ]
  定义体: if MeasurableSet s then μ.real s else 0
  empty' := by simp
  not_measurable' _ hi := if_neg hi
  m_iUnion' f hf₁ hf₂ := by
    simp only [*, MeasurableSet.iUnion hf₁, if_true, measure_iUnion hf₂ hf₁, measureReal_def]
    rw [ENNReal.tsum_toReal_eq]
    exacts [(summable_measure_toReal hf₁ hf₂).hasSum, fun _ => measure_ne_top _ _]

Depends on / 依赖: MeasurableSet
-/
def toSignedMeasure (μ : Measure α) [hμ : IsFiniteMeasure μ] : SignedMeasure α where
  measureOf' s := if MeasurableSet s then μ.real s else 0
  empty' := by simp
  not_measurable' _ hi := if_neg hi
  m_iUnion' f hf₁ hf₂ := by
    simp only [*, MeasurableSet.iUnion hf₁, if_true, measure_iUnion hf₂ hf₁, measureReal_def]
    rw [ENNReal.tsum_toReal_eq]
    exacts [(summable_measure_toReal hf₁ hf₂).hasSum, fun _ => measure_ne_top _ _]

open scoped Classical in
@[simp]
/--
theorem `toSignedMeasure_apply` / 定理 `toSignedMeasure_apply`

English:
theorem toSignedMeasure_apply
  given: (μ : Measure α) [hμ : IsFiniteMeasure μ] (i : Set α)
  proof: rfl

中文:
定理 toSignedMeasure_apply
  条件: (μ : 测度 α) [hμ : 是有限测度 μ] (i : 集合 α)
  证明: rfl
-/
theorem toSignedMeasure_apply (μ : Measure α) [hμ : IsFiniteMeasure μ] (i : Set α) :
    μ.toSignedMeasure i = if MeasurableSet i then μ.real i else 0 := rfl

/--
theorem `toSignedMeasure_apply_measurable` / 定理 `toSignedMeasure_apply_measurable`

English:
theorem toSignedMeasure_apply_measurable
  statement: {μ : Measure α} [IsFiniteMeasure μ] {i : Set α}
  proof: if_pos hi

中文:
定理 toSignedMeasure_apply_measurable
  结论: {μ : 测度 α} [是有限测度 μ] {i : 集合 α}
  证明: if_pos hi

Depends on / 依赖: if_pos
-/
theorem toSignedMeasure_apply_measurable {μ : Measure α} [IsFiniteMeasure μ] {i : Set α}
    (hi : MeasurableSet i) : μ.toSignedMeasure i = μ.real i :=
  if_pos hi

-- Without this lemma, `singularPart_neg` in
-- `Mathlib/MeasureTheory/Measure/Decomposition/Lebesgue.lean` is extremely slow
/--
theorem `toSignedMeasure_congr` / 定理 `toSignedMeasure_congr`

English:
theorem toSignedMeasure_congr
  statement: {μ ν : Measure α} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
  proof: by
  congr

中文:
定理 toSignedMeasure_congr
  结论: {μ ν : 测度 α} [是有限测度 μ] [是有限测度 ν]
  证明: by
  congr
-/
theorem toSignedMeasure_congr {μ ν : Measure α} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : μ = ν) : μ.toSignedMeasure = ν.toSignedMeasure := by
  congr

/--
theorem `toSignedMeasure_eq_toSignedMeasure_iff` / 定理 `toSignedMeasure_eq_toSignedMeasure_iff`

English:
theorem toSignedMeasure_eq_toSignedMeasure_iff
  statement: {μ ν : Measure α} [IsFiniteMeasure μ]
  proof: by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · ext1 i hi
    have : μ.toSignedMeasure i = ν.toSignedMeasure i := by rw [h]
    rwa [toSignedMeasure_apply_measurable hi, toSignedMeasure_apply_measurable hi,
        measureReal_eq_measureReal_iff] at this
  · congr

@[simp]

中文:
定理 toSignedMeasure_eq_toSignedMeasure_iff
  结论: {μ ν : 测度 α} [是有限测度 μ]
  证明: by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · ext1 i hi
    have : μ.toSignedMeasure i = ν.toSignedMeasure i := by rw [h]
    rwa [toSignedMeasure_apply_measurable hi, toSignedMeasure_apply_measurable hi,
        measureReal_eq_measureReal_iff] at this
  · congr

@[simp]

Depends on / 依赖: measureReal_eq_measureReal_iff, toSignedMeasure, toSignedMeasure_apply_measurable
-/
theorem toSignedMeasure_eq_toSignedMeasure_iff {μ ν : Measure α} [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] : μ.toSignedMeasure = ν.toSignedMeasure ↔ μ = ν := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · ext1 i hi
    have : μ.toSignedMeasure i = ν.toSignedMeasure i := by rw [h]
    rwa [toSignedMeasure_apply_measurable hi, toSignedMeasure_apply_measurable hi,
        measureReal_eq_measureReal_iff] at this
  · congr

@[simp]
/--
theorem `toSignedMeasure_zero` / 定理 `toSignedMeasure_zero`

English:
theorem toSignedMeasure_zero
  statement: (0 : Measure α).toSignedMeasure = 0
  proof: by
  ext i hi
  simp [hi]

@[simp]

中文:
定理 toSignedMeasure_zero
  结论: (0 : 测度 α).toSignedMeasure = 0
  证明: by
  ext i hi
  simp [hi]

@[simp]
-/
theorem toSignedMeasure_zero : (0 : Measure α).toSignedMeasure = 0 := by
  ext i hi
  simp [hi]

@[simp]
/--
theorem `toSignedMeasure_add` / 定理 `toSignedMeasure_add`

English:
theorem toSignedMeasure_add
  given: (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
  proof: by
  ext i hi
  rw [toSignedMeasure_apply_measurable hi]; rw [measureReal_add_apply]; rw [_root_.add_apply]; rw [toSignedMeasure_apply_measurable hi]; rw [toSignedMeasure_apply_measurable hi]

@[simp]

中文:
定理 toSignedMeasure_add
  条件: (μ ν : 测度 α) [是有限测度 μ] [是有限测度 ν]
  证明: by
  ext i hi
  rw [toSignedMeasure_apply_measurable hi]; rw [measureReal_add_apply]; rw [_root_.add_apply]; rw [toSignedMeasure_apply_measurable hi]; rw [toSignedMeasure_apply_measurable hi]

@[simp]

Depends on / 依赖: _root_, _root_.add_apply, add_apply, measureReal_add_apply, toSignedMeasure_apply_measurable
-/
theorem toSignedMeasure_add (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    (μ + ν).toSignedMeasure = μ.toSignedMeasure + ν.toSignedMeasure := by
  ext i hi
  rw [toSignedMeasure_apply_measurable hi]; rw [measureReal_add_apply]; rw [_root_.add_apply]; rw [toSignedMeasure_apply_measurable hi]; rw [toSignedMeasure_apply_measurable hi]

@[simp]
/--
theorem `toSignedMeasure_smul` / 定理 `toSignedMeasure_smul`

English:
theorem toSignedMeasure_smul
  given: (μ : Measure α) [IsFiniteMeasure μ] (r : Real>=0)
  proof: by
  ext i hi
  rw [toSignedMeasure_apply_measurable hi]; rw [_root_.smul_apply]; rw [toSignedMeasure_apply_measurable hi]; rw [measureReal_nnreal_smul_apply]
  rfl

中文:
定理 toSignedMeasure_smul
  条件: (μ : 测度 α) [是有限测度 μ] (r : 实数>=0)
  证明: by
  ext i hi
  rw [toSignedMeasure_apply_measurable hi]; rw [_root_.smul_apply]; rw [toSignedMeasure_apply_measurable hi]; rw [measureReal_nnreal_smul_apply]
  rfl

Depends on / 依赖: _root_, _root_.smul_apply, measureReal_nnreal_smul_apply, smul_apply, toSignedMeasure_apply_measurable
-/
theorem toSignedMeasure_smul (μ : Measure α) [IsFiniteMeasure μ] (r : Real>=0) :
    (r • μ).toSignedMeasure = r • μ.toSignedMeasure := by
  ext i hi
  rw [toSignedMeasure_apply_measurable hi]; rw [_root_.smul_apply]; rw [toSignedMeasure_apply_measurable hi]; rw [measureReal_nnreal_smul_apply]
  rfl

open scoped Classical in
/--
Definition of `toENNRealVectorMeasure` / `toENNRealVectorMeasure` 的定义

English:
definition toENNRealVectorMeasure
  signature: (μ : Measure α)
  body: if MeasurableSet i then μ i else 0
  empty' := by simp
  not_measurable' _ hi := if_neg hi
  m_iUnion' _ hf₁ hf₂ := by
    rw [Summable.hasSum_iff ENNReal.summable]; rw [if_pos (MeasurableSet.iUnion hf₁)]; rw [MeasureTheory.measure_iUnion hf₂ hf₁]
    exact tsum_congr fun n => if_pos (hf₁ n)

中文:
定义 toENN实数VectorMeasure
  签名: (μ : 测度 α)
  定义体: if MeasurableSet i then μ i else 0
  empty' := by simp
  not_measurable' _ hi := if_neg hi
  m_iUnion' _ hf₁ hf₂ := by
    rw [Summable.hasSum_iff ENNReal.summable]; rw [if_pos (MeasurableSet.iUnion hf₁)]; rw [MeasureTheory.measure_iUnion hf₂ hf₁]
    exact tsum_congr fun n => if_pos (hf₁ n)

Depends on / 依赖: MeasurableSet
-/
def toENNRealVectorMeasure (μ : Measure α) : VectorMeasure α Real>=0∞ where
  measureOf' i := if MeasurableSet i then μ i else 0
  empty' := by simp
  not_measurable' _ hi := if_neg hi
  m_iUnion' _ hf₁ hf₂ := by
    rw [Summable.hasSum_iff ENNReal.summable]; rw [if_pos (MeasurableSet.iUnion hf₁)]; rw [MeasureTheory.measure_iUnion hf₂ hf₁]
    exact tsum_congr fun n => if_pos (hf₁ n)

open scoped Classical in
@[simp]
/--
theorem `toENNRealVectorMeasure_apply` / 定理 `toENNRealVectorMeasure_apply`

English:
theorem toENNRealVectorMeasure_apply
  given: (μ : Measure α) (i : Set α)
  proof: rfl

中文:
定理 toENN实数VectorMeasure_apply
  条件: (μ : 测度 α) (i : 集合 α)
  证明: rfl
-/
theorem toENNRealVectorMeasure_apply (μ : Measure α) (i : Set α) :
    μ.toENNRealVectorMeasure i = if MeasurableSet i then μ i else 0 := rfl

/--
theorem `toENNRealVectorMeasure_apply_measurable` / 定理 `toENNRealVectorMeasure_apply_measurable`

English:
theorem toENNRealVectorMeasure_apply_measurable
  given: {μ : Measure α} {i : Set α} (hi : MeasurableSet i)
  proof: if_pos hi

@[simp]

中文:
定理 toENN实数VectorMeasure_apply_measurable
  条件: {μ : 测度 α} {i : 集合 α} (hi : 可测集 i)
  证明: if_pos hi

@[simp]

Depends on / 依赖: if_pos
-/
theorem toENNRealVectorMeasure_apply_measurable {μ : Measure α} {i : Set α} (hi : MeasurableSet i) :
    μ.toENNRealVectorMeasure i = μ i :=
  if_pos hi

@[simp]
/--
theorem `toENNRealVectorMeasure_zero` / 定理 `toENNRealVectorMeasure_zero`

English:
theorem toENNRealVectorMeasure_zero
  statement: (0 : Measure α).toENNRealVectorMeasure = 0
  proof: by
  ext i
  simp

@[simp]

中文:
定理 toENN实数VectorMeasure_zero
  结论: (0 : 测度 α).toENN实数VectorMeasure = 0
  证明: by
  ext i
  simp

@[simp]
-/
theorem toENNRealVectorMeasure_zero : (0 : Measure α).toENNRealVectorMeasure = 0 := by
  ext i
  simp

@[simp]
/--
theorem `toENNRealVectorMeasure_add` / 定理 `toENNRealVectorMeasure_add`

English:
theorem toENNRealVectorMeasure_add
  given: (μ ν : Measure α)
  proof: by
  refine MeasureTheory.VectorMeasure.ext fun i hi => ?_
  rw [toENNRealVectorMeasure_apply_measurable hi]; rw [add_apply]; rw [_root_.add_apply]; rw [toENNRealVectorMeasure_apply_measurable hi]; rw [toENNRealVectorMeasure_apply_measurable hi]

中文:
定理 toENN实数VectorMeasure_add
  条件: (μ ν : 测度 α)
  证明: by
  refine MeasureTheory.VectorMeasure.ext fun i hi => ?_
  rw [toENNRealVectorMeasure_apply_measurable hi]; rw [add_apply]; rw [_root_.add_apply]; rw [toENNRealVectorMeasure_apply_measurable hi]; rw [toENNRealVectorMeasure_apply_measurable hi]

Depends on / 依赖: MeasureTheory, MeasureTheory.VectorMeasure.ext, VectorMeasure, _root_, _root_.add_apply, add_apply, toENNRealVectorMeasure_apply_measurable
-/
theorem toENNRealVectorMeasure_add (μ ν : Measure α) :
    (μ + ν).toENNRealVectorMeasure = μ.toENNRealVectorMeasure + ν.toENNRealVectorMeasure := by
  refine MeasureTheory.VectorMeasure.ext fun i hi => ?_
  rw [toENNRealVectorMeasure_apply_measurable hi]; rw [add_apply]; rw [_root_.add_apply]; rw [toENNRealVectorMeasure_apply_measurable hi]; rw [toENNRealVectorMeasure_apply_measurable hi]

/--
theorem `toSignedMeasure_sub_apply` / 定理 `toSignedMeasure_sub_apply`

English:
theorem toSignedMeasure_sub_apply
  statement: {μ ν : Measure α} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
  proof: by
  rw [_root_.sub_apply]; rw [toSignedMeasure_apply_measurable hi]; rw [Measure.toSignedMeasure_apply_measurable hi]

中文:
定理 toSignedMeasure_sub_apply
  结论: {μ ν : 测度 α} [是有限测度 μ] [是有限测度 ν]
  证明: by
  rw [_root_.sub_apply]; rw [toSignedMeasure_apply_measurable hi]; rw [Measure.toSignedMeasure_apply_measurable hi]

Depends on / 依赖: Measure, Measure.toSignedMeasure_apply_measurable, _root_, _root_.sub_apply, sub_apply, toSignedMeasure_apply_measurable
-/
theorem toSignedMeasure_sub_apply {μ ν : Measure α} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {i : Set α} (hi : MeasurableSet i) :
    (μ.toSignedMeasure - ν.toSignedMeasure) i = μ.real i - ν.real i := by
  rw [_root_.sub_apply]; rw [toSignedMeasure_apply_measurable hi]; rw [Measure.toSignedMeasure_apply_measurable hi]

end Measure

namespace VectorMeasure

open Measure

section

/--
Definition of `ennrealToMeasure` / `ennrealToMeasure` 的定义

English:
definition ennrealToMeasure
  signature: {_ : MeasurableSpace α} (v : VectorMeasure α Real>=0∞)
  body: ofMeasurable (fun s _ => v s) v.empty fun _ hf₁ hf₂ => v.of_disjoint_iUnion hf₁ hf₂

中文:
定义 ennrealToMeasure
  签名: {_ : 可测空间 α} (v : 向量测度 α 实数>=0∞)
  定义体: ofMeasurable (fun s _ => v s) v.empty fun _ hf₁ hf₂ => v.of_disjoint_iUnion hf₁ hf₂

Depends on / 依赖: ofMeasurable, of_disjoint_iUnion, v.empty, v.of_disjoint_iUnion
-/
def ennrealToMeasure {_ : MeasurableSpace α} (v : VectorMeasure α Real>=0∞) : Measure α :=
  ofMeasurable (fun s _ => v s) v.empty fun _ hf₁ hf₂ => v.of_disjoint_iUnion hf₁ hf₂

/--
theorem `ennrealToMeasure_apply` / 定理 `ennrealToMeasure_apply`

English:
theorem ennrealToMeasure_apply
  statement: {m : MeasurableSpace α} {v : VectorMeasure α Real>=0∞} {s : Set α}
  proof: by
  rw [ennrealToMeasure]; rw [ofMeasurable_apply _ hs]

@[simp]

中文:
定理 ennrealToMeasure_apply
  结论: {m : 可测空间 α} {v : 向量测度 α 实数>=0∞} {s : 集合 α}
  证明: by
  rw [ennrealToMeasure]; rw [ofMeasurable_apply _ hs]

@[simp]

Depends on / 依赖: ennrealToMeasure, ofMeasurable_apply
-/
theorem ennrealToMeasure_apply {m : MeasurableSpace α} {v : VectorMeasure α Real>=0∞} {s : Set α}
    (hs : MeasurableSet s) : ennrealToMeasure v s = v s := by
  rw [ennrealToMeasure]; rw [ofMeasurable_apply _ hs]

@[simp]
/--
theorem `ennrealToMeasure_zero` / 定理 `ennrealToMeasure_zero`

English:
theorem ennrealToMeasure_zero
  statement: ennrealToMeasure (0 : VectorMeasure α Real>=0∞) = 0
  proof: by
  simp [ennrealToMeasure]

@[simp]

中文:
定理 ennrealToMeasure_zero
  结论: ennrealToMeasure (0 : 向量测度 α 实数>=0∞) = 0
  证明: by
  simp [ennrealToMeasure]

@[simp]

Depends on / 依赖: ennrealToMeasure
-/
theorem ennrealToMeasure_zero : ennrealToMeasure (0 : VectorMeasure α Real>=0∞) = 0 := by
  simp [ennrealToMeasure]

@[simp]
/--
theorem `_root_.MeasureTheory.Measure.toENNRealVectorMeasure_ennrealToMeasure` / 定理 `_root_.MeasureTheory.Measure.toENNRealVectorMeasure_ennrealToMeasure`

English:
theorem _root_.MeasureTheory.Measure.toENNRealVectorMeasure_ennrealToMeasure
  proof: ext fun s hs => by
  rw [toENNRealVectorMeasure_apply_measurable hs]; rw [ennrealToMeasure_apply hs]

@[simp]

中文:
定理 _root_.测度论.测度.toENN实数VectorMeasure_ennrealToMeasure
  证明: ext fun s hs => by
  rw [toENNRealVectorMeasure_apply_measurable hs]; rw [ennrealToMeasure_apply hs]

@[simp]

Depends on / 依赖: ennrealToMeasure_apply, toENNRealVectorMeasure_apply_measurable
-/
theorem _root_.MeasureTheory.Measure.toENNRealVectorMeasure_ennrealToMeasure
    (μ : VectorMeasure α Real>=0∞) :
    toENNRealVectorMeasure (ennrealToMeasure μ) = μ := ext fun s hs => by
  rw [toENNRealVectorMeasure_apply_measurable hs]; rw [ennrealToMeasure_apply hs]

@[simp]
/--
theorem `ennrealToMeasure_toENNRealVectorMeasure` / 定理 `ennrealToMeasure_toENNRealVectorMeasure`

English:
theorem ennrealToMeasure_toENNRealVectorMeasure
  given: (μ : Measure α)
  proof: Measure.ext fun s hs => by
  rw [ennrealToMeasure_apply hs]; rw [toENNRealVectorMeasure_apply_measurable hs]

中文:
定理 ennrealToMeasure_toENN实数VectorMeasure
  条件: (μ : 测度 α)
  证明: Measure.ext fun s hs => by
  rw [ennrealToMeasure_apply hs]; rw [toENNRealVectorMeasure_apply_measurable hs]

Depends on / 依赖: Measure, Measure.ext, ennrealToMeasure_apply, toENNRealVectorMeasure_apply_measurable
-/
theorem ennrealToMeasure_toENNRealVectorMeasure (μ : Measure α) :
    ennrealToMeasure (toENNRealVectorMeasure μ) = μ := Measure.ext fun s hs => by
  rw [ennrealToMeasure_apply hs]; rw [toENNRealVectorMeasure_apply_measurable hs]

/-- The equiv between `VectorMeasure α ℝ≥0∞` and `Measure α` formed by
`MeasureTheory.VectorMeasure.ennrealToMeasure` and
`MeasureTheory.Measure.toENNRealVectorMeasure`. -/
@[simps]
/--
Definition of `equivMeasure` / `equivMeasure` 的定义

English:
definition equivMeasure
  signature: [MeasurableSpace α]
  body: ennrealToMeasure
  invFun := toENNRealVectorMeasure
  left_inv := toENNRealVectorMeasure_ennrealToMeasure
  right_inv := ennrealToMeasure_toENNRealVectorMeasure

中文:
定义 equivMeasure
  签名: [可测空间 α]
  定义体: ennrealToMeasure
  invFun := toENNRealVectorMeasure
  left_inv := toENNRealVectorMeasure_ennrealToMeasure
  right_inv := ennrealToMeasure_toENNRealVectorMeasure

Depends on / 依赖: ennrealToMeasure
-/
def equivMeasure [MeasurableSpace α] : VectorMeasure α Real>=0∞ ≃ Measure α where
  toFun := ennrealToMeasure
  invFun := toENNRealVectorMeasure
  left_inv := toENNRealVectorMeasure_ennrealToMeasure
  right_inv := ennrealToMeasure_toENNRealVectorMeasure

end

section

variable {mα : MeasurableSpace α} [MeasurableSpace β]
variable {M : Type*} [AddCommMonoid M] [TopologicalSpace M]
variable (v : VectorMeasure α M)

open scoped Classical in
/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: (v : VectorMeasure α M) (f : α -> β)
  body: if hf : Measurable f then
    { measureOf' := fun s => if MeasurableSet s then v (f ⁻¹' s) else 0
      empty' := by simp
      not_measurable' := fun _ hi => if_neg hi
      m_iUnion' := by
        intro g hg₁ hg₂
        convert! v.m_iUnion (fun i => hf (hg₁ i)) fun i j hij => (hg₂ hij).preimage _
        · rw [if_pos (hg₁ _)]
        · rw [Set.preimage_iUnion, if_pos (MeasurableSet.iUnion hg₁)] }
  else 0

中文:
定义 map
  签名: (v : 向量测度 α M) (f : α -> β)
  定义体: if hf : Measurable f then
    { measureOf' := fun s => if MeasurableSet s then v (f ⁻¹' s) else 0
      empty' := by simp
      not_measurable' := fun _ hi => if_neg hi
      m_iUnion' := by
        intro g hg₁ hg₂
        convert! v.m_iUnion (fun i => hf (hg₁ i)) fun i j hij => (hg₂ hij).preimage _
        · rw [if_pos (hg₁ _)]
        · rw [Set.preimage_iUnion, if_pos (MeasurableSet.iUnion hg₁)] }
  else 0

Depends on / 依赖: Measurable, MeasurableSet, MeasurableSet.iUnion, Set.preimage_iUnion, convert, iUnion, if_neg, if_pos, m_iUnion, measureOf, not_measurable, preimage, preimage_iUnion, v.m_iUnion
-/
def map (v : VectorMeasure α M) (f : α -> β) : VectorMeasure β M :=
  if hf : Measurable f then
    { measureOf' := fun s => if MeasurableSet s then v (f ⁻¹' s) else 0
      empty' := by simp
      not_measurable' := fun _ hi => if_neg hi
      m_iUnion' := by
        intro g hg₁ hg₂
        convert! v.m_iUnion (fun i => hf (hg₁ i)) fun i j hij => (hg₂ hij).preimage _
        · rw [if_pos (hg₁ _)]
        · rw [Set.preimage_iUnion, if_pos (MeasurableSet.iUnion hg₁)] }
  else 0

/--
theorem `map_not_measurable` / 定理 `map_not_measurable`

English:
theorem map_not_measurable
  given: {f : α -> β} (hf : ¬Measurable f)
  statement: v.map f = 0
  proof: dif_neg hf

中文:
定理 map_not_measurable
  条件: {f : α -> β} (hf : ¬可测 f)
  结论: v.map f = 0
  证明: dif_neg hf

Depends on / 依赖: dif_neg
-/
theorem map_not_measurable {f : α -> β} (hf : ¬Measurable f) : v.map f = 0 :=
  dif_neg hf

/--
theorem `map_apply` / 定理 `map_apply`

English:
theorem map_apply
  given: {f : α -> β} (hf : Measurable f) {s : Set β} (hs : MeasurableSet s)
  proof: by
  rw [map]; rw [dif_pos hf]
  exact if_pos hs

@[simp]

中文:
定理 map_apply
  条件: {f : α -> β} (hf : 可测 f) {s : 集合 β} (hs : 可测集 s)
  证明: by
  rw [map]; rw [dif_pos hf]
  exact if_pos hs

@[simp]

Depends on / 依赖: dif_pos, if_pos
-/
theorem map_apply {f : α -> β} (hf : Measurable f) {s : Set β} (hs : MeasurableSet s) :
    v.map f s = v (f ⁻¹' s) := by
  rw [map]; rw [dif_pos hf]
  exact if_pos hs

@[simp]
/--
theorem `map_id` / 定理 `map_id`

English:
theorem map_id
  statement: v.map id = v
  proof: ext fun i hi => by rw [map_apply v measurable_id hi, Set.preimage_id]

@[simp]

中文:
定理 map_id
  结论: v.map id = v
  证明: ext fun i hi => by rw [map_apply v measurable_id hi, Set.preimage_id]

@[simp]

Depends on / 依赖: Set.preimage_id, map_apply, measurable_id, preimage_id
-/
theorem map_id : v.map id = v :=
  ext fun i hi => by rw [map_apply v measurable_id hi, Set.preimage_id]

@[simp]
/--
theorem `map_zero` / 定理 `map_zero`

English:
theorem map_zero
  given: (f : α -> β)
  statement: (0 : VectorMeasure α M).map f = 0
  proof: by
  by_cases hf : Measurable f
  · ext i hi
    rw [map_apply _ hf hi]; rw [zero_apply]; rw [zero_apply]
  · exact dif_neg hf

中文:
定理 map_zero
  条件: (f : α -> β)
  结论: (0 : 向量测度 α M).map f = 0
  证明: by
  by_cases hf : Measurable f
  · ext i hi
    rw [map_apply _ hf hi]; rw [zero_apply]; rw [zero_apply]
  · exact dif_neg hf

Depends on / 依赖: Measurable, dif_neg, map_apply, zero_apply
-/
theorem map_zero (f : α -> β) : (0 : VectorMeasure α M).map f = 0 := by
  by_cases hf : Measurable f
  · ext i hi
    rw [map_apply _ hf hi]; rw [zero_apply]; rw [zero_apply]
  · exact dif_neg hf

section

variable {N : Type*} [AddCommMonoid N] [TopologicalSpace N]

/--
Definition of `mapRange` / `mapRange` 的定义

English:
definition mapRange
  signature: (v : VectorMeasure α M) (f : M ->+ N) (hf : Continuous f)
  body: f (v s)
  empty' := by rw [empty, AddMonoidHom.map_zero]
  not_measurable' i hi := by rw [not_measurable v hi, AddMonoidHom.map_zero]
  m_iUnion' _ hg₁ hg₂ := HasSum.map (v.m_iUnion hg₁ hg₂) f hf

@[simp]

中文:
定义 mapRange
  签名: (v : 向量测度 α M) (f : M ->+ N) (hf : 连续 f)
  定义体: f (v s)
  empty' := by rw [empty, AddMonoidHom.map_zero]
  not_measurable' i hi := by rw [not_measurable v hi, AddMonoidHom.map_zero]
  m_iUnion' _ hg₁ hg₂ := HasSum.map (v.m_iUnion hg₁ hg₂) f hf

@[simp]
-/
def mapRange (v : VectorMeasure α M) (f : M ->+ N) (hf : Continuous f) : VectorMeasure α N where
  measureOf' s := f (v s)
  empty' := by rw [empty, AddMonoidHom.map_zero]
  not_measurable' i hi := by rw [not_measurable v hi, AddMonoidHom.map_zero]
  m_iUnion' _ hg₁ hg₂ := HasSum.map (v.m_iUnion hg₁ hg₂) f hf

@[simp]
/--
theorem `mapRange_apply` / 定理 `mapRange_apply`

English:
theorem mapRange_apply
  given: {f : M ->+ N} (hf : Continuous f) {s : Set α}
  statement: v.mapRange f hf s = f (v s)
  proof: rfl

@[simp]

中文:
定理 mapRange_apply
  条件: {f : M ->+ N} (hf : 连续 f) {s : 集合 α}
  结论: v.mapRange f hf s = f (v s)
  证明: rfl

@[simp]
-/
theorem mapRange_apply {f : M ->+ N} (hf : Continuous f) {s : Set α} : v.mapRange f hf s = f (v s) :=
  rfl

@[simp]
/--
theorem `mapRange_id` / 定理 `mapRange_id`

English:
theorem mapRange_id
  statement: v.mapRange (AddMonoidHom.id M) continuous_id = v
  proof: by
  ext
  rfl

@[simp]

中文:
定理 mapRange_id
  结论: v.mapRange (加法幺半群态射.id M) continuous_id = v
  证明: by
  ext
  rfl

@[simp]
-/
theorem mapRange_id : v.mapRange (AddMonoidHom.id M) continuous_id = v := by
  ext
  rfl

@[simp]
/--
theorem `mapRange_zero` / 定理 `mapRange_zero`

English:
theorem mapRange_zero
  given: {f : M ->+ N} (hf : Continuous f)
  proof: by
  ext
  simp

中文:
定理 mapRange_zero
  条件: {f : M ->+ N} (hf : 连续 f)
  证明: by
  ext
  simp
-/
theorem mapRange_zero {f : M ->+ N} (hf : Continuous f) :
    mapRange (0 : VectorMeasure α M) f hf = 0 := by
  ext
  simp

section ContinuousAdd

variable [ContinuousAdd M] [ContinuousAdd N]

@[simp]
/--
theorem `mapRange_add` / 定理 `mapRange_add`

English:
theorem mapRange_add
  given: {v w : VectorMeasure α M} {f : M ->+ N} (hf : Continuous f)
  proof: by
  ext
  simp

中文:
定理 mapRange_add
  条件: {v w : 向量测度 α M} {f : M ->+ N} (hf : 连续 f)
  证明: by
  ext
  simp
-/
theorem mapRange_add {v w : VectorMeasure α M} {f : M ->+ N} (hf : Continuous f) :
    (v + w).mapRange f hf = v.mapRange f hf + w.mapRange f hf := by
  ext
  simp

/--
Definition of `mapRangeHom` / `mapRangeHom` 的定义

English:
definition mapRangeHom
  signature: {α : Type*} [MeasurableSpace α] (f : M ->+ N) (hf : Continuous f)
  body: v.mapRange f hf
  map_zero' := mapRange_zero hf
  map_add' _ _ := mapRange_add hf

中文:
定义 mapRangeHom
  签名: {α : 类型} [可测空间 α] (f : M ->+ N) (hf : 连续 f)
  定义体: v.mapRange f hf
  map_zero' := mapRange_zero hf
  map_add' _ _ := mapRange_add hf

Depends on / 依赖: mapRange, v.mapRange
-/
def mapRangeHom {α : Type*} [MeasurableSpace α] (f : M ->+ N) (hf : Continuous f) :
    VectorMeasure α M ->+ VectorMeasure α N where
  toFun v := v.mapRange f hf
  map_zero' := mapRange_zero hf
  map_add' _ _ := mapRange_add hf

end ContinuousAdd

section Module

variable {R : Type*} [Semiring R] [Module R M] [Module R N]

variable [ContinuousConstSMul R M] [ContinuousConstSMul R N]

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
theorem `mapRange_smul` / 定理 `mapRange_smul`

English:
theorem mapRange_smul
  given: {v : VectorMeasure α M} {f : M ->ₗ[R] N} (hf : Continuous f) {c : R}
  proof: by
  ext; simp

中文:
定理 mapRange_smul
  条件: {v : 向量测度 α M} {f : M ->ₗ[R] N} (hf : 连续 f) {c : R}
  证明: by
  ext; simp
-/
theorem mapRange_smul {v : VectorMeasure α M} {f : M ->ₗ[R] N} (hf : Continuous f) {c : R} :
    (c • v).mapRange f.toAddMonoidHom hf = c • (v.mapRange f.toAddMonoidHom hf) := by
  ext; simp

variable [ContinuousAdd M] [ContinuousAdd N]

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `mapRangeₗ` / `mapRangeₗ` 的定义

English:
definition mapRangeₗ
  signature: {α : Type*} [MeasurableSpace α] (f : M ->ₗ[R] N) (hf : Continuous f)
  body: v.mapRange f.toAddMonoidHom hf
  map_add' _ _ := mapRange_add hf
  map_smul' _ _ := mapRange_smul hf

中文:
定义 mapRangeₗ
  签名: {α : 类型} [可测空间 α] (f : M ->ₗ[R] N) (hf : 连续 f)
  定义体: v.mapRange f.toAddMonoidHom hf
  map_add' _ _ := mapRange_add hf
  map_smul' _ _ := mapRange_smul hf

Depends on / 依赖: f.toAddMonoidHom, mapRange, toAddMonoidHom, v.mapRange
-/
def mapRangeₗ {α : Type*} [MeasurableSpace α] (f : M ->ₗ[R] N) (hf : Continuous f) :
    VectorMeasure α M ->ₗ[R] VectorMeasure α N where
  toFun v := v.mapRange f.toAddMonoidHom hf
  map_add' _ _ := mapRange_add hf
  map_smul' _ _ := mapRange_smul hf

end Module

end

open scoped Classical in
/--
Definition of `restrict` / `restrict` 的定义

English:
definition restrict
  signature: (v : VectorMeasure α M) (i : Set α)
  body: if hi : MeasurableSet i then
    { measureOf' := fun s => if MeasurableSet s then v (s inter i) else 0
      empty' := by simp
      not_measurable' := fun _ hi => if_neg hi
      m_iUnion' := by
        intro f hf₁ hf₂
        convert!
          v.m_iUnion (fun n => (hf₁ n).inter hi)
            (hf₂.mono fun i j => Disjoint.mono inf_le_left inf_le_left)
        · rw [if_pos (hf₁ _)]
        · rw [Set.iUnion_inter, if_pos (MeasurableSet.iUnion hf₁)] }
  else 0

中文:
定义 restrict
  签名: (v : 向量测度 α M) (i : 集合 α)
  定义体: if hi : MeasurableSet i then
    { measureOf' := fun s => if MeasurableSet s then v (s inter i) else 0
      empty' := by simp
      not_measurable' := fun _ hi => if_neg hi
      m_iUnion' := by
        intro f hf₁ hf₂
        convert!
          v.m_iUnion (fun n => (hf₁ n).inter hi)
            (hf₂.mono fun i j => Disjoint.mono inf_le_left inf_le_left)
        · rw [if_pos (hf₁ _)]
        · rw [Set.iUnion_inter, if_pos (MeasurableSet.iUnion hf₁)] }
  else 0
-/
@[no_expose] def restrict (v : VectorMeasure α M) (i : Set α) : VectorMeasure α M :=
  if hi : MeasurableSet i then
    { measureOf' := fun s => if MeasurableSet s then v (s inter i) else 0
      empty' := by simp
      not_measurable' := fun _ hi => if_neg hi
      m_iUnion' := by
        intro f hf₁ hf₂
        convert!
          v.m_iUnion (fun n => (hf₁ n).inter hi)
            (hf₂.mono fun i j => Disjoint.mono inf_le_left inf_le_left)
        · rw [if_pos (hf₁ _)]
        · rw [Set.iUnion_inter, if_pos (MeasurableSet.iUnion hf₁)] }
  else 0

/--
theorem `restrict_not_measurable` / 定理 `restrict_not_measurable`

English:
theorem restrict_not_measurable
  given: {i : Set α} (hi : ¬MeasurableSet i)
  statement: v.restrict i = 0
  proof: dif_neg hi

中文:
定理 restrict_not_measurable
  条件: {i : 集合 α} (hi : ¬可测集 i)
  结论: v.restrict i = 0
  证明: dif_neg hi

Depends on / 依赖: dif_neg
-/
theorem restrict_not_measurable {i : Set α} (hi : ¬MeasurableSet i) : v.restrict i = 0 :=
  dif_neg hi

/--
theorem `restrict_apply` / 定理 `restrict_apply`

English:
theorem restrict_apply
  given: {i : Set α} (hi : MeasurableSet i) {j : Set α} (hj : MeasurableSet j)
  proof: by
  rw [restrict]; rw [dif_pos hi]
  exact if_pos hj

中文:
定理 restrict_apply
  条件: {i : 集合 α} (hi : 可测集 i) {j : 集合 α} (hj : 可测集 j)
  证明: by
  rw [restrict]; rw [dif_pos hi]
  exact if_pos hj

Depends on / 依赖: dif_pos, if_pos, restrict
-/
theorem restrict_apply {i : Set α} (hi : MeasurableSet i) {j : Set α} (hj : MeasurableSet j) :
    v.restrict i j = v (j inter i) := by
  rw [restrict]; rw [dif_pos hi]
  exact if_pos hj

/--
theorem `restrict_apply_univ` / 定理 `restrict_apply_univ`

English:
theorem restrict_apply_univ
  given: {i : Set α}
  proof: by
  by_cases hi : MeasurableSet i
  · simp [restrict_apply, hi]
  · simp [restrict_not_measurable, hi]

中文:
定理 restrict_apply_univ
  条件: {i : 集合 α}
  证明: by
  by_cases hi : MeasurableSet i
  · simp [restrict_apply, hi]
  · simp [restrict_not_measurable, hi]
-/
@[simp] theorem restrict_apply_univ {i : Set α} :
    v.restrict i univ = v i := by
  by_cases hi : MeasurableSet i
  · simp [restrict_apply, hi]
  · simp [restrict_not_measurable, hi]

/--
theorem `restrict_eq_self` / 定理 `restrict_eq_self`

English:
theorem restrict_eq_self
  statement: {i : Set α} (hi : MeasurableSet i) {j : Set α} (hj : MeasurableSet j)
  proof: by
  rw [restrict_apply v hi hj]; rw [Set.inter_eq_left.2 hij]

@[simp]

中文:
定理 restrict_eq_self
  结论: {i : 集合 α} (hi : 可测集 i) {j : 集合 α} (hj : 可测集 j)
  证明: by
  rw [restrict_apply v hi hj]; rw [Set.inter_eq_left.2 hij]

@[simp]

Depends on / 依赖: Set.inter_eq_left, inter_eq_left, restrict_apply
-/
theorem restrict_eq_self {i : Set α} (hi : MeasurableSet i) {j : Set α} (hj : MeasurableSet j)
    (hij : j subseteq i) : v.restrict i j = v j := by
  rw [restrict_apply v hi hj]; rw [Set.inter_eq_left.2 hij]

@[simp]
/--
theorem `restrict_empty` / 定理 `restrict_empty`

English:
theorem restrict_empty
  statement: v.restrict ∅ = 0
  proof: ext fun i hi => by
    rw [restrict_apply v MeasurableSet.empty hi]; rw [Set.inter_empty]; rw [v.empty]; rw [zero_apply]

@[simp]

中文:
定理 restrict_empty
  结论: v.restrict ∅ = 0
  证明: ext fun i hi => by
    rw [restrict_apply v MeasurableSet.empty hi]; rw [Set.inter_empty]; rw [v.empty]; rw [zero_apply]

@[simp]

Depends on / 依赖: MeasurableSet, MeasurableSet.empty, Set.inter_empty, inter_empty, restrict_apply, v.empty, zero_apply
-/
theorem restrict_empty : v.restrict ∅ = 0 :=
  ext fun i hi => by
    rw [restrict_apply v MeasurableSet.empty hi]; rw [Set.inter_empty]; rw [v.empty]; rw [zero_apply]

@[simp]
/--
theorem `restrict_univ` / 定理 `restrict_univ`

English:
theorem restrict_univ
  statement: v.restrict Set.univ = v
  proof: ext fun i hi => by rw [restrict_apply v MeasurableSet.univ hi, Set.inter_univ]

@[simp]

中文:
定理 restrict_univ
  结论: v.restrict 集合.univ = v
  证明: ext fun i hi => by rw [restrict_apply v MeasurableSet.univ hi, Set.inter_univ]

@[simp]

Depends on / 依赖: MeasurableSet, MeasurableSet.univ, Set.inter_univ, inter_univ, restrict_apply
-/
theorem restrict_univ : v.restrict Set.univ = v :=
  ext fun i hi => by rw [restrict_apply v MeasurableSet.univ hi, Set.inter_univ]

@[simp]
/--
theorem `restrict_zero` / 定理 `restrict_zero`

English:
theorem restrict_zero
  given: {i : Set α}
  statement: (0 : VectorMeasure α M).restrict i = 0
  proof: by
  by_cases hi : MeasurableSet i
  · ext j hj
    rw [restrict_apply 0 hi hj]; rw [zero_apply]; rw [zero_apply]
  · exact dif_neg hi

中文:
定理 restrict_zero
  条件: {i : 集合 α}
  结论: (0 : 向量测度 α M).restrict i = 0
  证明: by
  by_cases hi : MeasurableSet i
  · ext j hj
    rw [restrict_apply 0 hi hj]; rw [zero_apply]; rw [zero_apply]
  · exact dif_neg hi

Depends on / 依赖: MeasurableSet, dif_neg, restrict_apply, zero_apply
-/
theorem restrict_zero {i : Set α} : (0 : VectorMeasure α M).restrict i = 0 := by
  by_cases hi : MeasurableSet i
  · ext j hj
    rw [restrict_apply 0 hi hj]; rw [zero_apply]; rw [zero_apply]
  · exact dif_neg hi

/--
theorem `restrict_dirac` / 定理 `restrict_dirac`

English:
theorem restrict_dirac
  given: {s : Set α} {x : α} {m : M} (hs : MeasurableSet s) [Decidable (x in s)]
  proof: by
  classical
  ext t ht
  simp only [hs, ht, restrict_apply]
  split_ifs with has <;> simp [dirac, ht, ht.inter hs, has]

@[simp]

中文:
定理 restrict_dirac
  条件: {s : 集合 α} {x : α} {m : M} (hs : 可测集 s) [可判定 (x in s)]
  证明: by
  classical
  ext t ht
  simp only [hs, ht, restrict_apply]
  split_ifs with has <;> simp [dirac, ht, ht.inter hs, has]

@[simp]

Depends on / 依赖: classical, ht.inter, restrict_apply, split_ifs
-/
theorem restrict_dirac {s : Set α} {x : α} {m : M} (hs : MeasurableSet s) [Decidable (x in s)] :
    (dirac x m).restrict s = if x in s then dirac x m else 0 := by
  classical
  ext t ht
  simp only [hs, ht, restrict_apply]
  split_ifs with has <;> simp [dirac, ht, ht.inter hs, has]

@[simp]
/--
theorem `restrict_dirac_of_mem` / 定理 `restrict_dirac_of_mem`

English:
theorem restrict_dirac_of_mem
  given: {s : Set α} {x : α} {m : M} (hs : MeasurableSet s) (hx : x in s)
  proof: by
  classical
  simp [restrict_dirac, hs, hx]

@[simp]

中文:
定理 restrict_dirac_of_mem
  条件: {s : 集合 α} {x : α} {m : M} (hs : 可测集 s) (hx : x in s)
  证明: by
  classical
  simp [restrict_dirac, hs, hx]

@[simp]

Depends on / 依赖: classical, restrict_dirac
-/
theorem restrict_dirac_of_mem {s : Set α} {x : α} {m : M} (hs : MeasurableSet s) (hx : x in s) :
    (dirac x m).restrict s = dirac x m := by
  classical
  simp [restrict_dirac, hs, hx]

@[simp]
/--
theorem `restrict_dirac_of_notMem` / 定理 `restrict_dirac_of_notMem`

English:
theorem restrict_dirac_of_notMem
  given: {s : Set α} {x : α} {m : M} (hx : x ∉ s)
  proof: by
  classical
  by_cases hs : MeasurableSet s
  · simp [restrict_dirac, hs, hx]
  · simp [restrict, hs]

@[simp]

中文:
定理 restrict_dirac_of_notMem
  条件: {s : 集合 α} {x : α} {m : M} (hx : x ∉ s)
  证明: by
  classical
  by_cases hs : MeasurableSet s
  · simp [restrict_dirac, hs, hx]
  · simp [restrict, hs]

@[simp]

Depends on / 依赖: MeasurableSet, classical, restrict, restrict_dirac
-/
theorem restrict_dirac_of_notMem {s : Set α} {x : α} {m : M} (hx : x ∉ s) :
    (dirac x m).restrict s = 0 := by
  classical
  by_cases hs : MeasurableSet s
  · simp [restrict_dirac, hs, hx]
  · simp [restrict, hs]

@[simp]
/--
theorem `restrict_singleton` / 定理 `restrict_singleton`

English:
theorem restrict_singleton
  given: {a : α}
  statement: v.restrict {a} = dirac a (v {a})
  proof: by
  by_cases h : MeasurableSet {a}
  · ext s hs
    by_cases ha : a in s <;> simp [*, restrict_apply]
  · simp [restrict, h]

中文:
定理 restrict_singleton
  条件: {a : α}
  结论: v.restrict {a} = dirac a (v {a})
  证明: by
  by_cases h : MeasurableSet {a}
  · ext s hs
    by_cases ha : a in s <;> simp [*, restrict_apply]
  · simp [restrict, h]

Depends on / 依赖: MeasurableSet, restrict, restrict_apply
-/
theorem restrict_singleton {a : α} : v.restrict {a} = dirac a (v {a}) := by
  by_cases h : MeasurableSet {a}
  · ext s hs
    by_cases ha : a in s <;> simp [*, restrict_apply]
  · simp [restrict, h]

/--
theorem `restrict_restrict` / 定理 `restrict_restrict`

English:
theorem restrict_restrict
  given: {s t : Set α} (hs : MeasurableSet s) (ht : MeasurableSet t)
  proof: by
  ext u hu
  simp [restrict_apply, hs, hu, ht, Set.inter_assoc]

中文:
定理 restrict_restrict
  条件: {s t : 集合 α} (hs : 可测集 s) (ht : 可测集 t)
  证明: by
  ext u hu
  simp [restrict_apply, hs, hu, ht, Set.inter_assoc]

Depends on / 依赖: Set.inter_assoc, inter_assoc, restrict_apply
-/
theorem restrict_restrict {s t : Set α} (hs : MeasurableSet s) (ht : MeasurableSet t) :
    (v.restrict t).restrict s = v.restrict (s inter t) := by
  ext u hu
  simp [restrict_apply, hs, hu, ht, Set.inter_assoc]

/--
theorem `restrict_map` / 定理 `restrict_map`

English:
theorem restrict_map
  given: {f : α -> β} (hf : Measurable f) {s : Set β} (hs : MeasurableSet s)
  proof: by
  ext t ht
  simp [map_apply, hs, hf hs, restrict_apply, ht, hf, hf ht]

中文:
定理 restrict_map
  条件: {f : α -> β} (hf : 可测 f) {s : 集合 β} (hs : 可测集 s)
  证明: by
  ext t ht
  simp [map_apply, hs, hf hs, restrict_apply, ht, hf, hf ht]

Depends on / 依赖: map_apply, restrict_apply
-/
theorem restrict_map {f : α -> β} (hf : Measurable f) {s : Set β} (hs : MeasurableSet s) :
    (v.map f).restrict s = (v.restrict (f ⁻¹' s)).map f := by
  ext t ht
  simp [map_apply, hs, hf hs, restrict_apply, ht, hf, hf ht]

/--
theorem `restrict_toSignedMeasure` / 定理 `restrict_toSignedMeasure`

English:
theorem restrict_toSignedMeasure
  statement: {μ : Measure α} [IsFiniteMeasure μ]
  proof: by
  ext t ht
  rw [restrict_apply _ hs ht]; rw [Measure.toSignedMeasure_apply_measurable (ht.inter hs)]; rw [Measure.toSignedMeasure_apply_measurable ht]; rw [measureReal_restrict_apply ht]

中文:
定理 restrict_toSignedMeasure
  结论: {μ : 测度 α} [是有限测度 μ]
  证明: by
  ext t ht
  rw [restrict_apply _ hs ht]; rw [Measure.toSignedMeasure_apply_measurable (ht.inter hs)]; rw [Measure.toSignedMeasure_apply_measurable ht]; rw [measureReal_restrict_apply ht]

Depends on / 依赖: Measure, Measure.toSignedMeasure_apply_measurable, ht.inter, measureReal_restrict_apply, restrict_apply, toSignedMeasure_apply_measurable
-/
theorem restrict_toSignedMeasure {μ : Measure α} [IsFiniteMeasure μ]
    {s : Set α} (hs : MeasurableSet s) :
    μ.toSignedMeasure.restrict s = (μ.restrict s).toSignedMeasure := by
  ext t ht
  rw [restrict_apply _ hs ht]; rw [Measure.toSignedMeasure_apply_measurable (ht.inter hs)]; rw [Measure.toSignedMeasure_apply_measurable ht]; rw [measureReal_restrict_apply ht]

section ContinuousAdd

variable [ContinuousAdd M]

/--
theorem `map_add` / 定理 `map_add`

English:
theorem map_add
  given: (v w : VectorMeasure α M) (f : α -> β)
  statement: (v + w).map f = v.map f + w.map f
  proof: by
  by_cases hf : Measurable f
  · ext i hi
    simp [map_apply _ hf hi]
  · simp [map, dif_neg hf]

中文:
定理 map_add
  条件: (v w : 向量测度 α M) (f : α -> β)
  结论: (v + w).map f = v.map f + w.map f
  证明: by
  by_cases hf : Measurable f
  · ext i hi
    simp [map_apply _ hf hi]
  · simp [map, dif_neg hf]

Depends on / 依赖: Measurable, dif_neg, map_apply
-/
theorem map_add (v w : VectorMeasure α M) (f : α -> β) : (v + w).map f = v.map f + w.map f := by
  by_cases hf : Measurable f
  · ext i hi
    simp [map_apply _ hf hi]
  · simp [map, dif_neg hf]

/-- `VectorMeasure.map` as an additive monoid homomorphism. -/
@[simps]
/--
Definition of `mapGm` / `mapGm` 的定义

English:
definition mapGm
  signature: {α : Type*} [MeasurableSpace α] (f : α -> β)
  body: v.map f
  map_zero' := map_zero f
  map_add' _ _ := map_add _ _ f

@[simp]

中文:
定义 mapGm
  签名: {α : 类型} [可测空间 α] (f : α -> β)
  定义体: v.map f
  map_zero' := map_zero f
  map_add' _ _ := map_add _ _ f

@[simp]

Depends on / 依赖: v.map
-/
def mapGm {α : Type*} [MeasurableSpace α] (f : α -> β) : VectorMeasure α M ->+ VectorMeasure β M where
  toFun v := v.map f
  map_zero' := map_zero f
  map_add' _ _ := map_add _ _ f

@[simp]
/--
theorem `restrict_add` / 定理 `restrict_add`

English:
theorem restrict_add
  given: (v w : VectorMeasure α M) (i : Set α)
  proof: by
  by_cases hi : MeasurableSet i
  · ext j hj
    simp [restrict_apply _ hi hj]
  · simp [restrict_not_measurable _ hi]

中文:
定理 restrict_add
  条件: (v w : 向量测度 α M) (i : 集合 α)
  证明: by
  by_cases hi : MeasurableSet i
  · ext j hj
    simp [restrict_apply _ hi hj]
  · simp [restrict_not_measurable _ hi]

Depends on / 依赖: MeasurableSet, restrict_apply, restrict_not_measurable
-/
theorem restrict_add (v w : VectorMeasure α M) (i : Set α) :
    (v + w).restrict i = v.restrict i + w.restrict i := by
  by_cases hi : MeasurableSet i
  · ext j hj
    simp [restrict_apply _ hi hj]
  · simp [restrict_not_measurable _ hi]

/-- `VectorMeasure.restrict` as an additive monoid homomorphism. -/
@[simps]
/--
Definition of `restrictGm` / `restrictGm` 的定义

English:
definition restrictGm
  signature: {α : Type*} [MeasurableSpace α] (i : Set α)
  body: v.restrict i
  map_zero' := restrict_zero
  map_add' _ _ := restrict_add _ _ i

中文:
定义 restrictGm
  签名: {α : 类型} [可测空间 α] (i : 集合 α)
  定义体: v.restrict i
  map_zero' := restrict_zero
  map_add' _ _ := restrict_add _ _ i

Depends on / 依赖: restrict, v.restrict
-/
def restrictGm {α : Type*} [MeasurableSpace α] (i : Set α) :
    VectorMeasure α M ->+ VectorMeasure α M where
  toFun v := v.restrict i
  map_zero' := restrict_zero
  map_add' _ _ := restrict_add _ _ i

end ContinuousAdd

section Partition

variable {M : Type*} [TopologicalSpace M] [AddCommMonoid M] [T2Space M] [ContinuousAdd M]
variable {v : VectorMeasure α M} {i s t : Set α}

@[simp]
/--
theorem `restrict_add_restrict_compl` / 定理 `restrict_add_restrict_compl`

English:
theorem restrict_add_restrict_compl
  given: (hi : MeasurableSet i)
  proof: by
  ext A hA
  rw [_root_.add_apply]; rw [restrict_apply _ hi hA]; rw [restrict_apply _ hi.compl hA]; rw [← of_union _ (hA.inter hi) (hA.inter hi.compl)]
  · simp
.inter_left' A · exact disjoint_compl_right.inter_right' A

中文:
定理 restrict_add_restrict_compl
  条件: (hi : 可测集 i)
  证明: by
  ext A hA
  rw [_root_.add_apply]; rw [restrict_apply _ hi hA]; rw [restrict_apply _ hi.compl hA]; rw [← of_union _ (hA.inter hi) (hA.inter hi.compl)]
  · simp
.inter_left' A · exact disjoint_compl_right.inter_right' A

Depends on / 依赖: _root_, _root_.add_apply, add_apply, disjoint_compl_right, disjoint_compl_right.inter_right, hA.inter, hi.compl, inter_left, inter_right, of_union, restrict_apply
-/
theorem restrict_add_restrict_compl (hi : MeasurableSet i) :
    v.restrict i + v.restrict iᶜ = v := by
  ext A hA
  rw [_root_.add_apply]; rw [restrict_apply _ hi hA]; rw [restrict_apply _ hi.compl hA]; rw [← of_union _ (hA.inter hi) (hA.inter hi.compl)]
  · simp
.inter_left' A · exact disjoint_compl_right.inter_right' A

/--
theorem `restrict_inter_add_sdiff` / 定理 `restrict_inter_add_sdiff`

English:
theorem restrict_inter_add_sdiff
  given: (hs : MeasurableSet s) (ht : MeasurableSet t)
  proof: by
  ext u hu
  simp only [_root_.add_apply, restrict_apply, hs, hu, hs.inter ht, hs.diff ht]
  rw [← of_union (by grind) (hu.inter (hs.inter ht)) (hu.inter (hs.diff ht))]
  congr
  grind

@[deprecated (since := "2026-06-03")] alias restrict_inter_add_diff := restrict_inter_add_sdiff

中文:
定理 restrict_inter_add_sdiff
  条件: (hs : 可测集 s) (ht : 可测集 t)
  证明: by
  ext u hu
  simp only [_root_.add_apply, restrict_apply, hs, hu, hs.inter ht, hs.diff ht]
  rw [← of_union (by grind) (hu.inter (hs.inter ht)) (hu.inter (hs.diff ht))]
  congr
  grind

@[deprecated (since := "2026-06-03")] alias restrict_inter_add_diff := restrict_inter_add_sdiff

Depends on / 依赖: _root_, _root_.add_apply, add_apply, hs.diff, hs.inter, hu.inter, of_union, restrict_apply
-/
theorem restrict_inter_add_sdiff (hs : MeasurableSet s) (ht : MeasurableSet t) :
    v.restrict (s inter t) + v.restrict (s \ t) = v.restrict s := by
  ext u hu
  simp only [_root_.add_apply, restrict_apply, hs, hu, hs.inter ht, hs.diff ht]
  rw [← of_union (by grind) (hu.inter (hs.inter ht)) (hu.inter (hs.diff ht))]
  congr
  grind

@[deprecated (since := "2026-06-03")] alias restrict_inter_add_diff := restrict_inter_add_sdiff

/--
theorem `restrict_union_add_inter` / 定理 `restrict_union_add_inter`

English:
theorem restrict_union_add_inter
  given: (hs : MeasurableSet s) (ht : MeasurableSet t)
  proof: by
  rw [← v.restrict_inter_add_sdiff (hs.union ht) ht]; rw [union_inter_cancel_right]; rw [union_sdiff_right]; rw [← v.restrict_inter_add_sdiff hs ht]; rw [add_comm]; rw [← add_assoc]; rw [add_right_comm]

中文:
定理 restrict_union_add_inter
  条件: (hs : 可测集 s) (ht : 可测集 t)
  证明: by
  rw [← v.restrict_inter_add_sdiff (hs.union ht) ht]; rw [union_inter_cancel_right]; rw [union_sdiff_right]; rw [← v.restrict_inter_add_sdiff hs ht]; rw [add_comm]; rw [← add_assoc]; rw [add_right_comm]

Depends on / 依赖: add_assoc, add_comm, add_right_comm, hs.union, restrict_inter_add_sdiff, union_inter_cancel_right, union_sdiff_right, v.restrict_inter_add_sdiff
-/
theorem restrict_union_add_inter (hs : MeasurableSet s) (ht : MeasurableSet t) :
    v.restrict (s union t) + v.restrict (s inter t) = v.restrict s + v.restrict t := by
  rw [← v.restrict_inter_add_sdiff (hs.union ht) ht]; rw [union_inter_cancel_right]; rw [union_sdiff_right]; rw [← v.restrict_inter_add_sdiff hs ht]; rw [add_comm]; rw [← add_assoc]; rw [add_right_comm]

/--
theorem `restrict_union` / 定理 `restrict_union`

English:
theorem restrict_union
  given: (h : Disjoint s t) (hs : MeasurableSet s) (ht : MeasurableSet t)
  proof: by
  simp [← v.restrict_union_add_inter hs ht, disjoint_iff_inter_eq_empty.mp h]

中文:
定理 restrict_union
  条件: (h : Disjoint s t) (hs : 可测集 s) (ht : 可测集 t)
  证明: by
  simp [← v.restrict_union_add_inter hs ht, disjoint_iff_inter_eq_empty.mp h]

Depends on / 依赖: disjoint_iff_inter_eq_empty, disjoint_iff_inter_eq_empty.mp, restrict_union_add_inter, v.restrict_union_add_inter
-/
theorem restrict_union (h : Disjoint s t) (hs : MeasurableSet s) (ht : MeasurableSet t) :
    v.restrict (s union t) = v.restrict s + v.restrict t := by
  simp [← v.restrict_union_add_inter hs ht, disjoint_iff_inter_eq_empty.mp h]

end Partition

section Sub

variable {M : Type*} [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]

@[simp]
/--
theorem `restrict_neg` / 定理 `restrict_neg`

English:
theorem restrict_neg
  given: (v : VectorMeasure α M) (i : Set α)
  proof: by
  by_cases hi : MeasurableSet i
  · ext j hj; simp [restrict_apply _ hi hj]
  · simp [restrict_not_measurable _ hi]

@[simp]

中文:
定理 restrict_neg
  条件: (v : 向量测度 α M) (i : 集合 α)
  证明: by
  by_cases hi : MeasurableSet i
  · ext j hj; simp [restrict_apply _ hi hj]
  · simp [restrict_not_measurable _ hi]

@[simp]

Depends on / 依赖: MeasurableSet, restrict_apply, restrict_not_measurable
-/
theorem restrict_neg (v : VectorMeasure α M) (i : Set α) :
    (-v).restrict i = -(v.restrict i) := by
  by_cases hi : MeasurableSet i
  · ext j hj; simp [restrict_apply _ hi hj]
  · simp [restrict_not_measurable _ hi]

@[simp]
/--
theorem `restrict_sub` / 定理 `restrict_sub`

English:
theorem restrict_sub
  given: (v w : VectorMeasure α M) (i : Set α)
  proof: by
  simp [sub_eq_add_neg, restrict_add, restrict_neg]

中文:
定理 restrict_sub
  条件: (v w : 向量测度 α M) (i : 集合 α)
  证明: by
  simp [sub_eq_add_neg, restrict_add, restrict_neg]

Depends on / 依赖: restrict_add, restrict_neg, sub_eq_add_neg
-/
theorem restrict_sub (v w : VectorMeasure α M) (i : Set α) :
    (v - w).restrict i = v.restrict i - w.restrict i := by
  simp [sub_eq_add_neg, restrict_add, restrict_neg]

end Sub

end

section

variable [MeasurableSpace β]
variable {M : Type*} [AddCommMonoid M] [TopologicalSpace M]
variable {R : Type*} [Semiring R] [DistribMulAction R M] [ContinuousConstSMul R M]

@[simp]
/--
theorem `map_smul` / 定理 `map_smul`

English:
theorem map_smul
  given: {v : VectorMeasure α M} {f : α -> β} (c : R)
  statement: (c • v).map f = c • v.map f
  proof: by
  by_cases hf : Measurable f
  · ext i hi
    simp [map_apply _ hf hi]
  · simp only [map, dif_neg hf]
    -- `smul_zero` does not work since we do not require `ContinuousAdd`
    ext i
    simp

@[simp]

中文:
定理 map_smul
  条件: {v : 向量测度 α M} {f : α -> β} (c : R)
  结论: (c • v).map f = c • v.map f
  证明: by
  by_cases hf : Measurable f
  · ext i hi
    simp [map_apply _ hf hi]
  · simp only [map, dif_neg hf]
    -- `smul_zero` does not work since we do not require `ContinuousAdd`
    ext i
    simp

@[simp]

Depends on / 依赖: Measurable, dif_neg, map_apply
-/
theorem map_smul {v : VectorMeasure α M} {f : α -> β} (c : R) : (c • v).map f = c • v.map f := by
  by_cases hf : Measurable f
  · ext i hi
    simp [map_apply _ hf hi]
  · simp only [map, dif_neg hf]
    -- `smul_zero` does not work since we do not require `ContinuousAdd`
    ext i
    simp

@[simp]
/--
theorem `restrict_smul` / 定理 `restrict_smul`

English:
theorem restrict_smul
  given: {v : VectorMeasure α M} {i : Set α} (c : R)
  proof: by
  by_cases hi : MeasurableSet i
  · ext j hj
    simp [restrict_apply _ hi hj]
  · simp only [restrict_not_measurable _ hi]
    -- `smul_zero` does not work since we do not require `ContinuousAdd`
    ext j
    simp

中文:
定理 restrict_smul
  条件: {v : 向量测度 α M} {i : 集合 α} (c : R)
  证明: by
  by_cases hi : MeasurableSet i
  · ext j hj
    simp [restrict_apply _ hi hj]
  · simp only [restrict_not_measurable _ hi]
    -- `smul_zero` does not work since we do not require `ContinuousAdd`
    ext j
    simp

Depends on / 依赖: MeasurableSet, restrict_apply, restrict_not_measurable
-/
theorem restrict_smul {v : VectorMeasure α M} {i : Set α} (c : R) :
    (c • v).restrict i = c • v.restrict i := by
  by_cases hi : MeasurableSet i
  · ext j hj
    simp [restrict_apply _ hi hj]
  · simp only [restrict_not_measurable _ hi]
    -- `smul_zero` does not work since we do not require `ContinuousAdd`
    ext j
    simp

end

section

variable [MeasurableSpace β]
variable {M : Type*} [AddCommMonoid M] [TopologicalSpace M]
variable {R : Type*} [Semiring R] [Module R M] [ContinuousConstSMul R M] [ContinuousAdd M]

/-- `VectorMeasure.map` as a linear map. -/
@[simps]
/--
Definition of `mapₗ` / `mapₗ` 的定义

English:
definition mapₗ
  signature: (f : α -> β)
  body: v.map f
  map_add' _ _ := map_add _ _ f
  map_smul' _ _ := map_smul _

中文:
定义 mapₗ
  签名: (f : α -> β)
  定义体: v.map f
  map_add' _ _ := map_add _ _ f
  map_smul' _ _ := map_smul _

Depends on / 依赖: v.map
-/
def mapₗ (f : α -> β) : VectorMeasure α M ->ₗ[R] VectorMeasure β M where
  toFun v := v.map f
  map_add' _ _ := map_add _ _ f
  map_smul' _ _ := map_smul _

/-- `VectorMeasure.restrict` as an additive monoid homomorphism. -/
@[simps]
/--
Definition of `restrictₗ` / `restrictₗ` 的定义

English:
definition restrictₗ
  signature: (i : Set α)
  body: v.restrict i
  map_add' _ _ := restrict_add _ _ i
  map_smul' _ _ := restrict_smul _

中文:
定义 restrictₗ
  签名: (i : 集合 α)
  定义体: v.restrict i
  map_add' _ _ := restrict_add _ _ i
  map_smul' _ _ := restrict_smul _

Depends on / 依赖: restrict, v.restrict
-/
def restrictₗ (i : Set α) : VectorMeasure α M ->ₗ[R] VectorMeasure α M where
  toFun v := v.restrict i
  map_add' _ _ := restrict_add _ _ i
  map_smul' _ _ := restrict_smul _

end

section

variable {M : Type*} [TopologicalSpace M] [AddCommMonoid M] [PartialOrder M]

/--
Instance `instPartialOrder` / 实例 `instPartialOrder`

English:
instance instPartialOrder
  signature: : PartialOrder (VectorMeasure α M) where
  body: forall i, MeasurableSet i -> v i <= w i
  le_refl _ _ _ := le_rfl
  le_trans _ _ _ h₁ h₂ i hi := le_trans (h₁ i hi) (h₂ i hi)
  le_antisymm _ _ h₁ h₂ := ext fun i hi => le_antisymm (h₁ i hi) (h₂ i hi)

中文:
实例 instPartialOrder
  签名: : 偏序 (向量测度 α M) where
  定义体: forall i, MeasurableSet i -> v i <= w i
  le_refl _ _ _ := le_rfl
  le_trans _ _ _ h₁ h₂ i hi := le_trans (h₁ i hi) (h₂ i hi)
  le_antisymm _ _ h₁ h₂ := ext fun i hi => le_antisymm (h₁ i hi) (h₂ i hi)

Depends on / 依赖: MeasurableSet
-/
instance instPartialOrder : PartialOrder (VectorMeasure α M) where
  le v w := forall i, MeasurableSet i -> v i <= w i
  le_refl _ _ _ := le_rfl
  le_trans _ _ _ h₁ h₂ i hi := le_trans (h₁ i hi) (h₂ i hi)
  le_antisymm _ _ h₁ h₂ := ext fun i hi => le_antisymm (h₁ i hi) (h₂ i hi)

variable {v w : VectorMeasure α M}

/--
theorem `le_iff` / 定理 `le_iff`

English:
theorem le_iff
  statement: v <= w ↔ forall i, MeasurableSet i -> v i <= w i
  proof: Iff.rfl

中文:
定理 le_iff
  结论: v <= w ↔ 对任意 i, 可测集 i -> v i <= w i
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem le_iff : v <= w ↔ forall i, MeasurableSet i -> v i <= w i := Iff.rfl

/--
theorem `le_iff'` / 定理 `le_iff'`

English:
theorem le_iff'
  statement: v <= w ↔ forall i, v i <= w i
  proof: by
  refine ⟨fun h i => ?_, fun h i _ => h i⟩
  by_cases hi : MeasurableSet i
  · exact h i hi
  · rw [v.not_measurable hi, w.not_measurable hi]

中文:
定理 le_iff'
  结论: v <= w ↔ 对任意 i, v i <= w i
  证明: by
  refine ⟨fun h i => ?_, fun h i _ => h i⟩
  by_cases hi : MeasurableSet i
  · exact h i hi
  · rw [v.not_measurable hi, w.not_measurable hi]

Depends on / 依赖: MeasurableSet, not_measurable, v.not_measurable, w.not_measurable
-/
theorem le_iff' : v <= w ↔ forall i, v i <= w i := by
  refine ⟨fun h i => ?_, fun h i _ => h i⟩
  by_cases hi : MeasurableSet i
  · exact h i hi
  · rw [v.not_measurable hi, w.not_measurable hi]

end

/-- `v ≤[i] w` is notation for `v.restrict i ≤ w.restrict i`. -/
scoped[MeasureTheory]
  notation3:50 v " <=[" i:50 "] " w:50 =>
    MeasureTheory.VectorMeasure.restrict v i <= MeasureTheory.VectorMeasure.restrict w i

section

variable {M : Type*} [TopologicalSpace M] [AddCommMonoid M] [PartialOrder M]
variable (v w : VectorMeasure α M)

/--
theorem `restrict_le_restrict_iff` / 定理 `restrict_le_restrict_iff`

English:
theorem restrict_le_restrict_iff
  given: {i : Set α} (hi : MeasurableSet i)
  proof: ⟨fun h j hj₁ hj₂ => restrict_eq_self v hi hj₁ hj₂ ▸ restrict_eq_self w hi hj₁ hj₂ ▸ h j hj₁,
    fun h => le_iff.1 fun _ hj =>
      (restrict_apply v hi hj).symm ▸ (restrict_apply w hi hj).symm ▸
      h (hj.inter hi) Set.inter_subset_right⟩

中文:
定理 restrict_le_restrict_iff
  条件: {i : 集合 α} (hi : 可测集 i)
  证明: ⟨fun h j hj₁ hj₂ => restrict_eq_self v hi hj₁ hj₂ ▸ restrict_eq_self w hi hj₁ hj₂ ▸ h j hj₁,
    fun h => le_iff.1 fun _ hj =>
      (restrict_apply v hi hj).symm ▸ (restrict_apply w hi hj).symm ▸
      h (hj.inter hi) Set.inter_subset_right⟩

Depends on / 依赖: Set.inter_subset_right, hj.inter, inter_subset_right, le_iff, restrict_apply, restrict_eq_self
-/
theorem restrict_le_restrict_iff {i : Set α} (hi : MeasurableSet i) :
    v <=[i] w ↔ forall ⦃j⦄, MeasurableSet j -> j subseteq i -> v j <= w j :=
  ⟨fun h j hj₁ hj₂ => restrict_eq_self v hi hj₁ hj₂ ▸ restrict_eq_self w hi hj₁ hj₂ ▸ h j hj₁,
    fun h => le_iff.1 fun _ hj =>
      (restrict_apply v hi hj).symm ▸ (restrict_apply w hi hj).symm ▸
      h (hj.inter hi) Set.inter_subset_right⟩

/--
theorem `subset_le_of_restrict_le_restrict` / 定理 `subset_le_of_restrict_le_restrict`

English:
theorem subset_le_of_restrict_le_restrict
  statement: {i : Set α} (hi : MeasurableSet i) (hi₂ : v <=[i] w)
  proof: by
  by_cases hj₁ : MeasurableSet j
  · exact (restrict_le_restrict_iff _ _ hi).1 hi₂ hj₁ hj
  · rw [v.not_measurable hj₁, w.not_measurable hj₁]

中文:
定理 subset_le_of_restrict_le_restrict
  结论: {i : 集合 α} (hi : 可测集 i) (hi₂ : v <=[i] w)
  证明: by
  by_cases hj₁ : MeasurableSet j
  · exact (restrict_le_restrict_iff _ _ hi).1 hi₂ hj₁ hj
  · rw [v.not_measurable hj₁, w.not_measurable hj₁]

Depends on / 依赖: MeasurableSet, not_measurable, restrict_le_restrict_iff, v.not_measurable, w.not_measurable
-/
theorem subset_le_of_restrict_le_restrict {i : Set α} (hi : MeasurableSet i) (hi₂ : v <=[i] w)
    {j : Set α} (hj : j subseteq i) : v j <= w j := by
  by_cases hj₁ : MeasurableSet j
  · exact (restrict_le_restrict_iff _ _ hi).1 hi₂ hj₁ hj
  · rw [v.not_measurable hj₁, w.not_measurable hj₁]

/--
theorem `restrict_le_restrict_of_subset_le` / 定理 `restrict_le_restrict_of_subset_le`

English:
theorem restrict_le_restrict_of_subset_le
  statement: {i : Set α}
  proof: by
  by_cases hi : MeasurableSet i
  · exact (restrict_le_restrict_iff _ _ hi).2 h
  · rw [restrict_not_measurable v hi, restrict_not_measurable w hi]

中文:
定理 restrict_le_restrict_of_subset_le
  结论: {i : 集合 α}
  证明: by
  by_cases hi : MeasurableSet i
  · exact (restrict_le_restrict_iff _ _ hi).2 h
  · rw [restrict_not_measurable v hi, restrict_not_measurable w hi]

Depends on / 依赖: MeasurableSet, restrict_le_restrict_iff, restrict_not_measurable
-/
theorem restrict_le_restrict_of_subset_le {i : Set α}
    (h : forall ⦃j⦄, MeasurableSet j -> j subseteq i -> v j <= w j) : v <=[i] w := by
  by_cases hi : MeasurableSet i
  · exact (restrict_le_restrict_iff _ _ hi).2 h
  · rw [restrict_not_measurable v hi, restrict_not_measurable w hi]

/--
theorem `restrict_le_restrict_subset` / 定理 `restrict_le_restrict_subset`

English:
theorem restrict_le_restrict_subset
  statement: {i j : Set α} (hi₁ : MeasurableSet i) (hi₂ : v <=[i] w)
  proof: restrict_le_restrict_of_subset_le v w fun _ _ hk₂ =>
    subset_le_of_restrict_le_restrict v w hi₁ hi₂ (Set.Subset.trans hk₂ hij)

中文:
定理 restrict_le_restrict_subset
  结论: {i j : 集合 α} (hi₁ : 可测集 i) (hi₂ : v <=[i] w)
  证明: restrict_le_restrict_of_subset_le v w fun _ _ hk₂ =>
    subset_le_of_restrict_le_restrict v w hi₁ hi₂ (Set.Subset.trans hk₂ hij)

Depends on / 依赖: Set.Subset.trans, Subset, restrict_le_restrict_of_subset_le, subset_le_of_restrict_le_restrict
-/
theorem restrict_le_restrict_subset {i j : Set α} (hi₁ : MeasurableSet i) (hi₂ : v <=[i] w)
    (hij : j subseteq i) : v <=[j] w :=
  restrict_le_restrict_of_subset_le v w fun _ _ hk₂ =>
    subset_le_of_restrict_le_restrict v w hi₁ hi₂ (Set.Subset.trans hk₂ hij)

/--
theorem `le_restrict_empty` / 定理 `le_restrict_empty`

English:
theorem le_restrict_empty
  statement: v <=[∅] w
  proof: by
  simp

中文:
定理 le_restrict_empty
  结论: v <=[∅] w
  证明: by
  simp
-/
theorem le_restrict_empty : v <=[∅] w := by
  simp

/--
theorem `le_restrict_univ_iff_le` / 定理 `le_restrict_univ_iff_le`

English:
theorem le_restrict_univ_iff_le
  statement: v <=[Set.univ] w ↔ v <= w
  proof: by
  simp

中文:
定理 le_restrict_univ_iff_le
  结论: v <=[集合.univ] w ↔ v <= w
  证明: by
  simp
-/
theorem le_restrict_univ_iff_le : v <=[Set.univ] w ↔ v <= w := by
  simp

end

section

variable {M : Type*} [TopologicalSpace M]
  [AddCommGroup M] [PartialOrder M] [IsOrderedAddMonoid M] [IsTopologicalAddGroup M]
variable (v w : VectorMeasure α M)

nonrec theorem neg_le_neg {i : Set α} (hi : MeasurableSet i) (h : v <=[i] w) : -w <=[i] -v := by
  intro j hj₁
  rw [restrict_apply _ hi hj₁]; rw [restrict_apply _ hi hj₁]; rw [neg_apply]; rw [neg_apply]
  refine neg_le_neg ?_
  rw [← restrict_apply _ hi hj₁]; rw [← restrict_apply _ hi hj₁]
  exact h j hj₁

/--
theorem `neg_le_neg_iff` / 定理 `neg_le_neg_iff`

English:
theorem neg_le_neg_iff
  given: {i : Set α} (hi : MeasurableSet i)
  statement: -w <=[i] -v ↔ v <=[i] w
  proof: ⟨fun h => neg_neg v ▸ neg_neg w ▸ neg_le_neg _ _ hi h, fun h => neg_le_neg _ _ hi h⟩

中文:
定理 neg_le_neg_iff
  条件: {i : 集合 α} (hi : 可测集 i)
  结论: -w <=[i] -v ↔ v <=[i] w
  证明: ⟨fun h => neg_neg v ▸ neg_neg w ▸ neg_le_neg _ _ hi h, fun h => neg_le_neg _ _ hi h⟩

Depends on / 依赖: neg_le_neg, neg_neg
-/
theorem neg_le_neg_iff {i : Set α} (hi : MeasurableSet i) : -w <=[i] -v ↔ v <=[i] w :=
  ⟨fun h => neg_neg v ▸ neg_neg w ▸ neg_le_neg _ _ hi h, fun h => neg_le_neg _ _ hi h⟩

end

section

variable {M : Type*} [TopologicalSpace M]
  [AddCommMonoid M] [PartialOrder M] [IsOrderedAddMonoid M] [OrderClosedTopology M]
variable (v w : VectorMeasure α M) {i j : Set α}

/--
theorem `restrict_le_restrict_iUnion` / 定理 `restrict_le_restrict_iUnion`

English:
theorem restrict_le_restrict_iUnion
  statement: {f : Nat -> Set α} (hf₁ : forall n, MeasurableSet (f n))
  proof: by
  refine restrict_le_restrict_of_subset_le v w fun a ha₁ ha₂ => ?_
  have ha₃ : ⋃ n, a inter disjointed f n = a := by
    rwa [← Set.inter_iUnion, iUnion_disjointed, Set.inter_eq_left]
  have ha₄ : Pairwise (Disjoint on fun n => a inter disjointed f n) :=
    (disjoint_disjointed _).mono fun i j => Disjoint.mono inf_le_right inf_le_right
  rw [← ha₃]; rw [v.of_disjoint_iUnion _ ha₄]; rw [w.of_disjoint_iUnion _ ha₄]
  · refine Summable.tsum_le_tsum (fun n => (restrict_le_restrict_iff v w (hf₁ n)).1 (hf₂ n) ?_ ?_)
      ?_ ?_
    · exact ha₁.inter (MeasurableSet.disjointed hf₁ n)
    · exact Set.Subset.trans Set.inter_subset_right (disjointed_subset _ _)
    · refine (v.m_iUnion (fun n => ?_) ?_).summable
      · exact ha₁.inter (MeasurableSet.disjointed hf₁ n)
      · exact (disjoint_disjointed _).mono fun i j => Disjoint.mono inf_le_right inf_le_right
    · refine (w.m_iUnion (fun n => ?_) ?_).summable
      · exact ha₁.inter (MeasurableSet.disjointed hf₁ n)
      · exact (disjoint_disjointed _).mono fun i j => Disjoint.mono inf_le_right inf_le_right
  · intro n
    exact ha₁.inter (MeasurableSet.disjointed hf₁ n)
  · exact fun n => ha₁.inter (MeasurableSet.disjointed hf₁ n)

中文:
定理 restrict_le_restrict_iUnion
  结论: {f : 自然数 -> 集合 α} (hf₁ : 对任意 n, 可测集 (f n))
  证明: by
  refine restrict_le_restrict_of_subset_le v w fun a ha₁ ha₂ => ?_
  have ha₃ : ⋃ n, a inter disjointed f n = a := by
    rwa [← Set.inter_iUnion, iUnion_disjointed, Set.inter_eq_left]
  have ha₄ : Pairwise (Disjoint on fun n => a inter disjointed f n) :=
    (disjoint_disjointed _).mono fun i j => Disjoint.mono inf_le_right inf_le_right
  rw [← ha₃]; rw [v.of_disjoint_iUnion _ ha₄]; rw [w.of_disjoint_iUnion _ ha₄]
  · refine Summable.tsum_le_tsum (fun n => (restrict_le_restrict_iff v w (hf₁ n)).1 (hf₂ n) ?_ ?_)
      ?_ ?_
    · exact ha₁.inter (MeasurableSet.disjointed hf₁ n)
    · exact Set.Subset.trans Set.inter_subset_right (disjointed_subset _ _)
    · refine (v.m_iUnion (fun n => ?_) ?_).summable
      · exact ha₁.inter (MeasurableSet.disjointed hf₁ n)
      · exact (disjoint_disjointed _).mono fun i j => Disjoint.mono inf_le_right inf_le_right
    · refine (w.m_iUnion (fun n => ?_) ?_).summable
      · exact ha₁.inter (MeasurableSet.disjointed hf₁ n)
      · exact (disjoint_disjointed _).mono fun i j => Disjoint.mono inf_le_right inf_le_right
  · intro n
    exact ha₁.inter (MeasurableSet.disjointed hf₁ n)
  · exact fun n => ha₁.inter (MeasurableSet.disjointed hf₁ n)

Depends on / 依赖: Disjoint, Disjoint.mono, Pairwise, Set.inter_eq_left, Set.inter_iUnion, Summable, Summable.tsum_le_tsum, disjoint_disjointed, disjointed, iUnion_disjointed, inf_le_right, inter_eq_left, inter_iUnion, of_disjoint_iUnion, restrict_le_restrict_iff, restrict_le_restrict_of_subset_le, tsum_le_tsum, v.of_disjoint_iUnion, w.of_disjoint_iUnion
-/
theorem restrict_le_restrict_iUnion {f : Nat -> Set α} (hf₁ : forall n, MeasurableSet (f n))
    (hf₂ : forall n, v <=[f n] w) : v <=[⋃ n, f n] w := by
  refine restrict_le_restrict_of_subset_le v w fun a ha₁ ha₂ => ?_
  have ha₃ : ⋃ n, a inter disjointed f n = a := by
    rwa [← Set.inter_iUnion, iUnion_disjointed, Set.inter_eq_left]
  have ha₄ : Pairwise (Disjoint on fun n => a inter disjointed f n) :=
    (disjoint_disjointed _).mono fun i j => Disjoint.mono inf_le_right inf_le_right
  rw [← ha₃]; rw [v.of_disjoint_iUnion _ ha₄]; rw [w.of_disjoint_iUnion _ ha₄]
  · refine Summable.tsum_le_tsum (fun n => (restrict_le_restrict_iff v w (hf₁ n)).1 (hf₂ n) ?_ ?_)
      ?_ ?_
    · exact ha₁.inter (MeasurableSet.disjointed hf₁ n)
    · exact Set.Subset.trans Set.inter_subset_right (disjointed_subset _ _)
    · refine (v.m_iUnion (fun n => ?_) ?_).summable
      · exact ha₁.inter (MeasurableSet.disjointed hf₁ n)
      · exact (disjoint_disjointed _).mono fun i j => Disjoint.mono inf_le_right inf_le_right
    · refine (w.m_iUnion (fun n => ?_) ?_).summable
      · exact ha₁.inter (MeasurableSet.disjointed hf₁ n)
      · exact (disjoint_disjointed _).mono fun i j => Disjoint.mono inf_le_right inf_le_right
  · intro n
    exact ha₁.inter (MeasurableSet.disjointed hf₁ n)
  · exact fun n => ha₁.inter (MeasurableSet.disjointed hf₁ n)

/--
theorem `restrict_le_restrict_countable_iUnion` / 定理 `restrict_le_restrict_countable_iUnion`

English:
theorem restrict_le_restrict_countable_iUnion
  statement: [Countable β] {f : β -> Set α}
  proof: by
  cases nonempty_encodable β
  rw [← Encodable.iUnion_decode₂]
  refine restrict_le_restrict_iUnion v w ?_ ?_
  · intro n
    measurability
  · intro n
    rcases Encodable.decode₂ β n with - | b
    · simp
    · simp [hf₂ b]

中文:
定理 restrict_le_restrict_countable_iUnion
  结论: [可数 β] {f : β -> 集合 α}
  证明: by
  cases nonempty_encodable β
  rw [← Encodable.iUnion_decode₂]
  refine restrict_le_restrict_iUnion v w ?_ ?_
  · intro n
    measurability
  · intro n
    rcases Encodable.decode₂ β n with - | b
    · simp
    · simp [hf₂ b]

Depends on / 依赖: Encodable, Encodable.decode, Encodable.iUnion_decode, measurability, nonempty_encodable, restrict_le_restrict_iUnion
-/
theorem restrict_le_restrict_countable_iUnion [Countable β] {f : β -> Set α}
    (hf₁ : forall b, MeasurableSet (f b)) (hf₂ : forall b, v <=[f b] w) : v <=[⋃ b, f b] w := by
  cases nonempty_encodable β
  rw [← Encodable.iUnion_decode₂]
  refine restrict_le_restrict_iUnion v w ?_ ?_
  · intro n
    measurability
  · intro n
    rcases Encodable.decode₂ β n with - | b
    · simp
    · simp [hf₂ b]

/--
theorem `restrict_le_restrict_union` / 定理 `restrict_le_restrict_union`

English:
theorem restrict_le_restrict_union
  statement: (hi₁ : MeasurableSet i) (hi₂ : v <=[i] w) (hj₁ : MeasurableSet j)
  proof: by
  rw [Set.union_eq_iUnion]
  refine restrict_le_restrict_countable_iUnion v w ?_ ?_
  · measurability
  · rintro (_ | _) <;> simpa

中文:
定理 restrict_le_restrict_union
  结论: (hi₁ : 可测集 i) (hi₂ : v <=[i] w) (hj₁ : 可测集 j)
  证明: by
  rw [Set.union_eq_iUnion]
  refine restrict_le_restrict_countable_iUnion v w ?_ ?_
  · measurability
  · rintro (_ | _) <;> simpa

Depends on / 依赖: Set.union_eq_iUnion, measurability, restrict_le_restrict_countable_iUnion, union_eq_iUnion
-/
theorem restrict_le_restrict_union (hi₁ : MeasurableSet i) (hi₂ : v <=[i] w) (hj₁ : MeasurableSet j)
    (hj₂ : v <=[j] w) : v <=[i union j] w := by
  rw [Set.union_eq_iUnion]
  refine restrict_le_restrict_countable_iUnion v w ?_ ?_
  · measurability
  · rintro (_ | _) <;> simpa

end

section

variable {M : Type*} [TopologicalSpace M] [AddCommMonoid M] [PartialOrder M]
variable (v w : VectorMeasure α M) {i j : Set α}

/--
theorem `nonneg_of_zero_le_restrict` / 定理 `nonneg_of_zero_le_restrict`

English:
theorem nonneg_of_zero_le_restrict
  given: (hi₂ : 0 <=[i] v)
  statement: 0 <= v i
  proof: by
  by_cases hi₁ : MeasurableSet i
  · exact (restrict_le_restrict_iff _ _ hi₁).1 hi₂ hi₁ Set.Subset.rfl
  · rw [v.not_measurable hi₁]

中文:
定理 nonneg_of_zero_le_restrict
  条件: (hi₂ : 0 <=[i] v)
  结论: 0 <= v i
  证明: by
  by_cases hi₁ : MeasurableSet i
  · exact (restrict_le_restrict_iff _ _ hi₁).1 hi₂ hi₁ Set.Subset.rfl
  · rw [v.not_measurable hi₁]

Depends on / 依赖: MeasurableSet, Set.Subset.rfl, Subset, not_measurable, restrict_le_restrict_iff, v.not_measurable
-/
theorem nonneg_of_zero_le_restrict (hi₂ : 0 <=[i] v) : 0 <= v i := by
  by_cases hi₁ : MeasurableSet i
  · exact (restrict_le_restrict_iff _ _ hi₁).1 hi₂ hi₁ Set.Subset.rfl
  · rw [v.not_measurable hi₁]

/--
theorem `nonpos_of_restrict_le_zero` / 定理 `nonpos_of_restrict_le_zero`

English:
theorem nonpos_of_restrict_le_zero
  given: (hi₂ : v <=[i] 0)
  statement: v i <= 0
  proof: by
  by_cases hi₁ : MeasurableSet i
  · exact (restrict_le_restrict_iff _ _ hi₁).1 hi₂ hi₁ Set.Subset.rfl
  · rw [v.not_measurable hi₁]

中文:
定理 nonpos_of_restrict_le_zero
  条件: (hi₂ : v <=[i] 0)
  结论: v i <= 0
  证明: by
  by_cases hi₁ : MeasurableSet i
  · exact (restrict_le_restrict_iff _ _ hi₁).1 hi₂ hi₁ Set.Subset.rfl
  · rw [v.not_measurable hi₁]

Depends on / 依赖: MeasurableSet, Set.Subset.rfl, Subset, not_measurable, restrict_le_restrict_iff, v.not_measurable
-/
theorem nonpos_of_restrict_le_zero (hi₂ : v <=[i] 0) : v i <= 0 := by
  by_cases hi₁ : MeasurableSet i
  · exact (restrict_le_restrict_iff _ _ hi₁).1 hi₂ hi₁ Set.Subset.rfl
  · rw [v.not_measurable hi₁]

/--
theorem `zero_le_restrict_not_measurable` / 定理 `zero_le_restrict_not_measurable`

English:
theorem zero_le_restrict_not_measurable
  given: (hi : ¬MeasurableSet i)
  statement: 0 <=[i] v
  proof: by
  rw [restrict_zero]; rw [restrict_not_measurable _ hi]

中文:
定理 zero_le_restrict_not_measurable
  条件: (hi : ¬可测集 i)
  结论: 0 <=[i] v
  证明: by
  rw [restrict_zero]; rw [restrict_not_measurable _ hi]

Depends on / 依赖: restrict_not_measurable, restrict_zero
-/
theorem zero_le_restrict_not_measurable (hi : ¬MeasurableSet i) : 0 <=[i] v := by
  rw [restrict_zero]; rw [restrict_not_measurable _ hi]

/--
theorem `restrict_le_zero_of_not_measurable` / 定理 `restrict_le_zero_of_not_measurable`

English:
theorem restrict_le_zero_of_not_measurable
  given: (hi : ¬MeasurableSet i)
  statement: v <=[i] 0
  proof: by
  rw [restrict_zero]; rw [restrict_not_measurable _ hi]

中文:
定理 restrict_le_zero_of_not_measurable
  条件: (hi : ¬可测集 i)
  结论: v <=[i] 0
  证明: by
  rw [restrict_zero]; rw [restrict_not_measurable _ hi]

Depends on / 依赖: restrict_not_measurable, restrict_zero
-/
theorem restrict_le_zero_of_not_measurable (hi : ¬MeasurableSet i) : v <=[i] 0 := by
  rw [restrict_zero]; rw [restrict_not_measurable _ hi]

/--
theorem `measurable_of_not_zero_le_restrict` / 定理 `measurable_of_not_zero_le_restrict`

English:
theorem measurable_of_not_zero_le_restrict
  given: (hi : ¬0 <=[i] v)
  statement: MeasurableSet i
  proof: Not.imp_symm (zero_le_restrict_not_measurable _) hi

中文:
定理 measurable_of_not_zero_le_restrict
  条件: (hi : ¬0 <=[i] v)
  结论: 可测集 i
  证明: Not.imp_symm (zero_le_restrict_not_measurable _) hi

Depends on / 依赖: Not.imp_symm, imp_symm, zero_le_restrict_not_measurable
-/
theorem measurable_of_not_zero_le_restrict (hi : ¬0 <=[i] v) : MeasurableSet i :=
  Not.imp_symm (zero_le_restrict_not_measurable _) hi

/--
theorem `measurable_of_not_restrict_le_zero` / 定理 `measurable_of_not_restrict_le_zero`

English:
theorem measurable_of_not_restrict_le_zero
  given: (hi : ¬v <=[i] 0)
  statement: MeasurableSet i
  proof: Not.imp_symm (restrict_le_zero_of_not_measurable _) hi

中文:
定理 measurable_of_not_restrict_le_zero
  条件: (hi : ¬v <=[i] 0)
  结论: 可测集 i
  证明: Not.imp_symm (restrict_le_zero_of_not_measurable _) hi

Depends on / 依赖: Not.imp_symm, imp_symm, restrict_le_zero_of_not_measurable
-/
theorem measurable_of_not_restrict_le_zero (hi : ¬v <=[i] 0) : MeasurableSet i :=
  Not.imp_symm (restrict_le_zero_of_not_measurable _) hi

/--
theorem `zero_le_restrict_subset` / 定理 `zero_le_restrict_subset`

English:
theorem zero_le_restrict_subset
  given: (hi₁ : MeasurableSet i) (hij : j subseteq i) (hi₂ : 0 <=[i] v)
  statement: 0 <=[j] v
  proof: restrict_le_restrict_of_subset_le _ _ fun _ hk₁ hk₂ =>
    (restrict_le_restrict_iff _ _ hi₁).1 hi₂ hk₁ (Set.Subset.trans hk₂ hij)

中文:
定理 zero_le_restrict_subset
  条件: (hi₁ : 可测集 i) (hij : j subseteq i) (hi₂ : 0 <=[i] v)
  结论: 0 <=[j] v
  证明: restrict_le_restrict_of_subset_le _ _ fun _ hk₁ hk₂ =>
    (restrict_le_restrict_iff _ _ hi₁).1 hi₂ hk₁ (Set.Subset.trans hk₂ hij)

Depends on / 依赖: Set.Subset.trans, Subset, restrict_le_restrict_iff, restrict_le_restrict_of_subset_le
-/
theorem zero_le_restrict_subset (hi₁ : MeasurableSet i) (hij : j subseteq i) (hi₂ : 0 <=[i] v) : 0 <=[j] v :=
  restrict_le_restrict_of_subset_le _ _ fun _ hk₁ hk₂ =>
    (restrict_le_restrict_iff _ _ hi₁).1 hi₂ hk₁ (Set.Subset.trans hk₂ hij)

/--
theorem `restrict_le_zero_subset` / 定理 `restrict_le_zero_subset`

English:
theorem restrict_le_zero_subset
  given: (hi₁ : MeasurableSet i) (hij : j subseteq i) (hi₂ : v <=[i] 0)
  statement: v <=[j] 0
  proof: restrict_le_restrict_of_subset_le _ _ fun _ hk₁ hk₂ =>
    (restrict_le_restrict_iff _ _ hi₁).1 hi₂ hk₁ (Set.Subset.trans hk₂ hij)

中文:
定理 restrict_le_zero_subset
  条件: (hi₁ : 可测集 i) (hij : j subseteq i) (hi₂ : v <=[i] 0)
  结论: v <=[j] 0
  证明: restrict_le_restrict_of_subset_le _ _ fun _ hk₁ hk₂ =>
    (restrict_le_restrict_iff _ _ hi₁).1 hi₂ hk₁ (Set.Subset.trans hk₂ hij)

Depends on / 依赖: Set.Subset.trans, Subset, restrict_le_restrict_iff, restrict_le_restrict_of_subset_le
-/
theorem restrict_le_zero_subset (hi₁ : MeasurableSet i) (hij : j subseteq i) (hi₂ : v <=[i] 0) : v <=[j] 0 :=
  restrict_le_restrict_of_subset_le _ _ fun _ hk₁ hk₂ =>
    (restrict_le_restrict_iff _ _ hi₁).1 hi₂ hk₁ (Set.Subset.trans hk₂ hij)

end

section

variable {M : Type*} [TopologicalSpace M] [AddCommMonoid M] [LinearOrder M]
variable (v w : VectorMeasure α M) {i j : Set α}

/--
theorem `exists_pos_measure_of_not_restrict_le_zero` / 定理 `exists_pos_measure_of_not_restrict_le_zero`

English:
theorem exists_pos_measure_of_not_restrict_le_zero
  given: (hi : ¬v <=[i] 0)
  proof: by
  have hi₁ : MeasurableSet i := measurable_of_not_restrict_le_zero _ hi
  rw [restrict_le_restrict_iff _ _ hi₁] at hi
  push Not at hi
  exact hi

中文:
定理 存在_pos_measure_of_not_restrict_le_zero
  条件: (hi : ¬v <=[i] 0)
  证明: by
  have hi₁ : MeasurableSet i := measurable_of_not_restrict_le_zero _ hi
  rw [restrict_le_restrict_iff _ _ hi₁] at hi
  push Not at hi
  exact hi

Depends on / 依赖: MeasurableSet, measurable_of_not_restrict_le_zero, restrict_le_restrict_iff
-/
theorem exists_pos_measure_of_not_restrict_le_zero (hi : ¬v <=[i] 0) :
    exists j : Set α, MeasurableSet j ∧ j subseteq i ∧ 0 < v j := by
  have hi₁ : MeasurableSet i := measurable_of_not_restrict_le_zero _ hi
  rw [restrict_le_restrict_iff _ _ hi₁] at hi
  push Not at hi
  exact hi

end

section

variable {M : Type*} [TopologicalSpace M] [AddCommMonoid M] [PartialOrder M]
  [AddLeftMono M] [ContinuousAdd M]

/--
Instance `instAddLeftMono` / 实例 `instAddLeftMono`

English:
instance instAddLeftMono
  signature: : AddLeftMono (VectorMeasure α M)
  body: ⟨fun _ _ _ h i hi => by simp only [_root_.add_apply]; grw [h i hi]⟩

中文:
实例 instAddLeftMono
  签名: : AddLeftMono (向量测度 α M)
  定义体: ⟨fun _ _ _ h i hi => by simp only [_root_.add_apply]; grw [h i hi]⟩

Depends on / 依赖: _root_, _root_.add_apply, add_apply
-/
instance instAddLeftMono : AddLeftMono (VectorMeasure α M) :=
  ⟨fun _ _ _ h i hi => by simp only [_root_.add_apply]; grw [h i hi]⟩

end

section

variable {L M N : Type*}
variable [AddCommMonoid L] [TopologicalSpace L] [AddCommMonoid M] [TopologicalSpace M]
  [AddCommMonoid N] [TopologicalSpace N]

/--
Definition of `AbsolutelyContinuous` / `AbsolutelyContinuous` 的定义

English:
definition AbsolutelyContinuous
  signature: (v : VectorMeasure α M) (w : VectorMeasure α N)
  body: forall ⦃s : Set α⦄, w s = 0 -> v s = 0

@[inherit_doc VectorMeasure.AbsolutelyContinuous]
scoped[MeasureTheory] infixl:50 " ≪ᵥ " => MeasureTheory.VectorMeasure.AbsolutelyContinuous

中文:
定义 AbsolutelyContinuous
  签名: (v : 向量测度 α M) (w : 向量测度 α N)
  定义体: forall ⦃s : Set α⦄, w s = 0 -> v s = 0

@[inherit_doc VectorMeasure.AbsolutelyContinuous]
scoped[MeasureTheory] infixl:50 " ≪ᵥ " => MeasureTheory.VectorMeasure.AbsolutelyContinuous
-/
def AbsolutelyContinuous (v : VectorMeasure α M) (w : VectorMeasure α N) :=
  forall ⦃s : Set α⦄, w s = 0 -> v s = 0

@[inherit_doc VectorMeasure.AbsolutelyContinuous]
scoped[MeasureTheory] infixl:50 " ≪ᵥ " => MeasureTheory.VectorMeasure.AbsolutelyContinuous

open MeasureTheory

namespace AbsolutelyContinuous

variable {v : VectorMeasure α M} {w : VectorMeasure α N}

/--
theorem `mk` / 定理 `mk`

English:
theorem mk
  given: (h : forall ⦃s : Set α⦄, MeasurableSet s -> w s = 0 -> v s = 0)
  statement: v ≪ᵥ w
  proof: by
  intro s hs
  by_cases hmeas : MeasurableSet s
  · exact h hmeas hs
  · exact not_measurable v hmeas

中文:
定理 mk
  条件: (h : 对任意 ⦃s : 集合 α⦄, 可测集 s -> w s = 0 -> v s = 0)
  结论: v ≪ᵥ w
  证明: by
  intro s hs
  by_cases hmeas : MeasurableSet s
  · exact h hmeas hs
  · exact not_measurable v hmeas

Depends on / 依赖: MeasurableSet, not_measurable
-/
theorem mk (h : forall ⦃s : Set α⦄, MeasurableSet s -> w s = 0 -> v s = 0) : v ≪ᵥ w := by
  intro s hs
  by_cases hmeas : MeasurableSet s
  · exact h hmeas hs
  · exact not_measurable v hmeas

/--
theorem `eq` / 定理 `eq`

English:
theorem eq
  given: {w : VectorMeasure α M} (h : v = w)
  statement: v ≪ᵥ w
  proof: fun _ hs => h.symm ▸ hs

@[refl]

中文:
定理 eq
  条件: {w : 向量测度 α M} (h : v = w)
  结论: v ≪ᵥ w
  证明: fun _ hs => h.symm ▸ hs

@[refl]

Depends on / 依赖: h.symm
-/
theorem eq {w : VectorMeasure α M} (h : v = w) : v ≪ᵥ w :=
  fun _ hs => h.symm ▸ hs

@[refl]
/--
theorem `refl` / 定理 `refl`

English:
theorem refl
  given: (v : VectorMeasure α M)
  statement: v ≪ᵥ v
  proof: eq rfl

@[trans]

中文:
定理 refl
  条件: (v : 向量测度 α M)
  结论: v ≪ᵥ v
  证明: eq rfl

@[trans]
-/
theorem refl (v : VectorMeasure α M) : v ≪ᵥ v :=
  eq rfl

@[trans]
/--
theorem `trans` / 定理 `trans`

English:
theorem trans
  statement: {u : VectorMeasure α L} {v : VectorMeasure α M} {w : VectorMeasure α N} (huv : u ≪ᵥ v)
  proof: fun _ hs => huv hvw hs

中文:
定理 trans
  结论: {u : 向量测度 α L} {v : 向量测度 α M} {w : 向量测度 α N} (huv : u ≪ᵥ v)
  证明: fun _ hs => huv hvw hs
-/
theorem trans {u : VectorMeasure α L} {v : VectorMeasure α M} {w : VectorMeasure α N} (huv : u ≪ᵥ v)
    (hvw : v ≪ᵥ w) : u ≪ᵥ w :=
fun _ hs => huv hvw hs

/--
theorem `zero` / 定理 `zero`

English:
theorem zero
  given: (v : VectorMeasure α N)
  statement: (0 : VectorMeasure α M) ≪ᵥ v
  proof: fun s _ => zero_apply s

中文:
定理 zero
  条件: (v : 向量测度 α N)
  结论: (0 : 向量测度 α M) ≪ᵥ v
  证明: fun s _ => zero_apply s

Depends on / 依赖: zero_apply
-/
theorem zero (v : VectorMeasure α N) : (0 : VectorMeasure α M) ≪ᵥ v :=
  fun s _ => zero_apply s

/--
theorem `neg_left` / 定理 `neg_left`

English:
theorem neg_left
  statement: {M : Type*} [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  proof: by
  intro s hs
  rw [neg_apply]; rw [h hs]; rw [neg_zero]

中文:
定理 neg_left
  结论: {M : 类型} [加法交换群 M] [拓扑空间 M] [是拓扑加群 M]
  证明: by
  intro s hs
  rw [neg_apply]; rw [h hs]; rw [neg_zero]

Depends on / 依赖: neg_apply, neg_zero
-/
theorem neg_left {M : Type*} [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
    {v : VectorMeasure α M} {w : VectorMeasure α N} (h : v ≪ᵥ w) : -v ≪ᵥ w := by
  intro s hs
  rw [neg_apply]; rw [h hs]; rw [neg_zero]

/--
theorem `neg_right` / 定理 `neg_right`

English:
theorem neg_right
  statement: {N : Type*} [AddCommGroup N] [TopologicalSpace N] [IsTopologicalAddGroup N]
  proof: by
  intro s hs
  rw [neg_apply]; rw [neg_eq_zero] at hs
  exact h hs

中文:
定理 neg_right
  结论: {N : 类型} [加法交换群 N] [拓扑空间 N] [是拓扑加群 N]
  证明: by
  intro s hs
  rw [neg_apply]; rw [neg_eq_zero] at hs
  exact h hs

Depends on / 依赖: neg_apply, neg_eq_zero
-/
theorem neg_right {N : Type*} [AddCommGroup N] [TopologicalSpace N] [IsTopologicalAddGroup N]
    {v : VectorMeasure α M} {w : VectorMeasure α N} (h : v ≪ᵥ w) : v ≪ᵥ -w := by
  intro s hs
  rw [neg_apply]; rw [neg_eq_zero] at hs
  exact h hs

/--
theorem `add` / 定理 `add`

English:
theorem add
  statement: [ContinuousAdd M] {v₁ v₂ : VectorMeasure α M} {w : VectorMeasure α N} (hv₁ : v₁ ≪ᵥ w)
  proof: by
  intro s hs
  rw [_root_.add_apply]; rw [hv₁ hs]; rw [hv₂ hs]; rw [zero_add]

中文:
定理 add
  结论: [连续加法 M] {v₁ v₂ : 向量测度 α M} {w : 向量测度 α N} (hv₁ : v₁ ≪ᵥ w)
  证明: by
  intro s hs
  rw [_root_.add_apply]; rw [hv₁ hs]; rw [hv₂ hs]; rw [zero_add]

Depends on / 依赖: _root_, _root_.add_apply, add_apply, zero_add
-/
theorem add [ContinuousAdd M] {v₁ v₂ : VectorMeasure α M} {w : VectorMeasure α N} (hv₁ : v₁ ≪ᵥ w)
    (hv₂ : v₂ ≪ᵥ w) : v₁ + v₂ ≪ᵥ w := by
  intro s hs
  rw [_root_.add_apply]; rw [hv₁ hs]; rw [hv₂ hs]; rw [zero_add]

/--
theorem `sub` / 定理 `sub`

English:
theorem sub
  statement: {M : Type*} [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  proof: by
  intro s hs
  rw [sub_apply]; rw [hv₁ hs]; rw [hv₂ hs]; rw [zero_sub]; rw [neg_zero]

中文:
定理 sub
  结论: {M : 类型} [加法交换群 M] [拓扑空间 M] [是拓扑加群 M]
  证明: by
  intro s hs
  rw [sub_apply]; rw [hv₁ hs]; rw [hv₂ hs]; rw [zero_sub]; rw [neg_zero]

Depends on / 依赖: neg_zero, sub_apply, zero_sub
-/
theorem sub {M : Type*} [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
    {v₁ v₂ : VectorMeasure α M} {w : VectorMeasure α N} (hv₁ : v₁ ≪ᵥ w) (hv₂ : v₂ ≪ᵥ w) :
    v₁ - v₂ ≪ᵥ w := by
  intro s hs
  rw [sub_apply]; rw [hv₁ hs]; rw [hv₂ hs]; rw [zero_sub]; rw [neg_zero]

/--
theorem `smul` / 定理 `smul`

English:
theorem smul
  statement: {R : Type*} [Semiring R] [DistribMulAction R M] [ContinuousConstSMul R M] {r : R}
  proof: by
  intro s hs
  rw [_root_.smul_apply]; rw [h hs]; rw [smul_zero]

中文:
定理 smul
  结论: {R : 类型} [半环 R] [分配乘法作用 R M] [连续常数标量乘法 R M] {r : R}
  证明: by
  intro s hs
  rw [_root_.smul_apply]; rw [h hs]; rw [smul_zero]

Depends on / 依赖: _root_, _root_.smul_apply, smul_apply, smul_zero
-/
theorem smul {R : Type*} [Semiring R] [DistribMulAction R M] [ContinuousConstSMul R M] {r : R}
    {v : VectorMeasure α M} {w : VectorMeasure α N} (h : v ≪ᵥ w) : r • v ≪ᵥ w := by
  intro s hs
  rw [_root_.smul_apply]; rw [h hs]; rw [smul_zero]

/--
theorem `map` / 定理 `map`

English:
theorem map
  given: [MeasureSpace β] (h : v ≪ᵥ w) (f : α -> β)
  statement: v.map f ≪ᵥ w.map f
  proof: by
  by_cases hf : Measurable f
  · refine mk fun s hs hws => ?_
    rw [map_apply _ hf hs] at hws ⊢
    exact h hws
  · intro s _
    rw [map_not_measurable v hf]; rw [zero_apply]

中文:
定理 map
  条件: [测度空间 β] (h : v ≪ᵥ w) (f : α -> β)
  结论: v.map f ≪ᵥ w.map f
  证明: by
  by_cases hf : Measurable f
  · refine mk fun s hs hws => ?_
    rw [map_apply _ hf hs] at hws ⊢
    exact h hws
  · intro s _
    rw [map_not_measurable v hf]; rw [zero_apply]

Depends on / 依赖: Measurable, map_apply, map_not_measurable, zero_apply
-/
theorem map [MeasureSpace β] (h : v ≪ᵥ w) (f : α -> β) : v.map f ≪ᵥ w.map f := by
  by_cases hf : Measurable f
  · refine mk fun s hs hws => ?_
    rw [map_apply _ hf hs] at hws ⊢
    exact h hws
  · intro s _
    rw [map_not_measurable v hf]; rw [zero_apply]

/--
theorem `ennrealToMeasure` / 定理 `ennrealToMeasure`

English:
theorem ennrealToMeasure
  given: {μ : VectorMeasure α Real>=0∞}
  proof: by
  constructor <;> intro h
  · refine mk fun s hmeas hs => h ?_
    rw [← hs]; rw [ennrealToMeasure_apply hmeas]
  · intro s hs
    by_cases hmeas : MeasurableSet s
    · rw [ennrealToMeasure_apply hmeas] at hs
      exact h hs
    · exact not_measurable v hmeas

中文:
定理 ennrealToMeasure
  条件: {μ : 向量测度 α 实数>=0∞}
  证明: by
  constructor <;> intro h
  · refine mk fun s hmeas hs => h ?_
    rw [← hs]; rw [ennrealToMeasure_apply hmeas]
  · intro s hs
    by_cases hmeas : MeasurableSet s
    · rw [ennrealToMeasure_apply hmeas] at hs
      exact h hs
    · exact not_measurable v hmeas

Depends on / 依赖: MeasurableSet, ennrealToMeasure_apply, not_measurable
-/
theorem ennrealToMeasure {μ : VectorMeasure α Real>=0∞} :
    (forall ⦃s : Set α⦄, μ.ennrealToMeasure s = 0 -> v s = 0) ↔ v ≪ᵥ μ := by
  constructor <;> intro h
  · refine mk fun s hmeas hs => h ?_
    rw [← hs]; rw [ennrealToMeasure_apply hmeas]
  · intro s hs
    by_cases hmeas : MeasurableSet s
    · rw [ennrealToMeasure_apply hmeas] at hs
      exact h hs
    · exact not_measurable v hmeas

end AbsolutelyContinuous

/--
Definition of `MutuallySingular` / `MutuallySingular` 的定义

English:
definition MutuallySingular
  signature: (v : VectorMeasure α M) (w : VectorMeasure α N)
  body: exists s : Set α, MeasurableSet s ∧ (forall t subseteq s, v t = 0) ∧ forall t subseteq sᶜ, w t = 0

@[inherit_doc VectorMeasure.MutuallySingular]
scoped[MeasureTheory] infixl:60 " ⟂ᵥ " => MeasureTheory.VectorMeasure.MutuallySingular

中文:
定义 互奇异
  签名: (v : 向量测度 α M) (w : 向量测度 α N)
  定义体: exists s : Set α, MeasurableSet s ∧ (forall t subseteq s, v t = 0) ∧ forall t subseteq sᶜ, w t = 0

@[inherit_doc VectorMeasure.MutuallySingular]
scoped[MeasureTheory] infixl:60 " ⟂ᵥ " => MeasureTheory.VectorMeasure.MutuallySingular

Depends on / 依赖: MeasurableSet, subseteq
-/
def MutuallySingular (v : VectorMeasure α M) (w : VectorMeasure α N) : Prop :=
  exists s : Set α, MeasurableSet s ∧ (forall t subseteq s, v t = 0) ∧ forall t subseteq sᶜ, w t = 0

@[inherit_doc VectorMeasure.MutuallySingular]
scoped[MeasureTheory] infixl:60 " ⟂ᵥ " => MeasureTheory.VectorMeasure.MutuallySingular

namespace MutuallySingular

variable {v v₁ v₂ : VectorMeasure α M} {w w₁ w₂ : VectorMeasure α N}

/--
theorem `mk` / 定理 `mk`

English:
theorem mk
  statement: (s : Set α) (hs : MeasurableSet s) (h₁ : forall t subseteq s, MeasurableSet t -> v t = 0)
  proof: by
  refine ⟨s, hs, fun t hst => ?_, fun t hst => ?_⟩ <;> by_cases ht : MeasurableSet t
  · exact h₁ t hst ht
  · exact not_measurable v ht
  · exact h₂ t hst ht
  · exact not_measurable w ht

中文:
定理 mk
  结论: (s : 集合 α) (hs : 可测集 s) (h₁ : 对任意 t subseteq s, 可测集 t -> v t = 0)
  证明: by
  refine ⟨s, hs, fun t hst => ?_, fun t hst => ?_⟩ <;> by_cases ht : MeasurableSet t
  · exact h₁ t hst ht
  · exact not_measurable v ht
  · exact h₂ t hst ht
  · exact not_measurable w ht

Depends on / 依赖: MeasurableSet, not_measurable
-/
theorem mk (s : Set α) (hs : MeasurableSet s) (h₁ : forall t subseteq s, MeasurableSet t -> v t = 0)
    (h₂ : forall t subseteq sᶜ, MeasurableSet t -> w t = 0) : v ⟂ᵥ w := by
  refine ⟨s, hs, fun t hst => ?_, fun t hst => ?_⟩ <;> by_cases ht : MeasurableSet t
  · exact h₁ t hst ht
  · exact not_measurable v ht
  · exact h₂ t hst ht
  · exact not_measurable w ht

/--
theorem `symm` / 定理 `symm`

English:
theorem symm
  given: (h : v ⟂ᵥ w)
  statement: w ⟂ᵥ v
  proof: let ⟨s, hmeas, hs₁, hs₂⟩ := h
  ⟨sᶜ, hmeas.compl, hs₂, fun t ht => hs₁ _ (compl_compl s ▸ ht : t subseteq s)⟩

中文:
定理 symm
  条件: (h : v ⟂ᵥ w)
  结论: w ⟂ᵥ v
  证明: let ⟨s, hmeas, hs₁, hs₂⟩ := h
  ⟨sᶜ, hmeas.compl, hs₂, fun t ht => hs₁ _ (compl_compl s ▸ ht : t subseteq s)⟩

Depends on / 依赖: compl_compl, hmeas.compl, subseteq
-/
theorem symm (h : v ⟂ᵥ w) : w ⟂ᵥ v :=
  let ⟨s, hmeas, hs₁, hs₂⟩ := h
  ⟨sᶜ, hmeas.compl, hs₂, fun t ht => hs₁ _ (compl_compl s ▸ ht : t subseteq s)⟩

/--
theorem `zero_right` / 定理 `zero_right`

English:
theorem zero_right
  statement: v ⟂ᵥ (0 : VectorMeasure α N)
  proof: ⟨∅, MeasurableSet.empty, fun _ ht => (Set.subset_empty_iff.1 ht).symm ▸ v.empty,
    fun _ _ => zero_apply _⟩

中文:
定理 zero_right
  结论: v ⟂ᵥ (0 : 向量测度 α N)
  证明: ⟨∅, MeasurableSet.empty, fun _ ht => (Set.subset_empty_iff.1 ht).symm ▸ v.empty,
    fun _ _ => zero_apply _⟩

Depends on / 依赖: MeasurableSet, MeasurableSet.empty, Set.subset_empty_iff, subset_empty_iff, v.empty, zero_apply
-/
theorem zero_right : v ⟂ᵥ (0 : VectorMeasure α N) :=
  ⟨∅, MeasurableSet.empty, fun _ ht => (Set.subset_empty_iff.1 ht).symm ▸ v.empty,
    fun _ _ => zero_apply _⟩

/--
theorem `zero_left` / 定理 `zero_left`

English:
theorem zero_left
  statement: (0 : VectorMeasure α M) ⟂ᵥ w
  proof: zero_right.symm

中文:
定理 zero_left
  结论: (0 : 向量测度 α M) ⟂ᵥ w
  证明: zero_right.symm

Depends on / 依赖: zero_right, zero_right.symm
-/
theorem zero_left : (0 : VectorMeasure α M) ⟂ᵥ w :=
  zero_right.symm

/--
theorem `add_left` / 定理 `add_left`

English:
theorem add_left
  given: [T2Space N] [ContinuousAdd M] (h₁ : v₁ ⟂ᵥ w) (h₂ : v₂ ⟂ᵥ w)
  statement: v₁ + v₂ ⟂ᵥ w
  proof: by
  obtain ⟨u, hmu, hu₁, hu₂⟩ := h₁
  obtain ⟨v, hmv, hv₁, hv₂⟩ := h₂
  refine mk (u inter v) (hmu.inter hmv) (fun t ht _ => ?_) fun t ht hmt => ?_
  · rw [_root_.add_apply, hu₁ _ (Set.subset_inter_iff.1 ht).1, hv₁ _ (Set.subset_inter_iff.1 ht).2,
      zero_add]
  · rw [Set.compl_inter] at ht
    rw [(_ : t = uᶜ inter t union vᶜ \ uᶜ inter t)]; rw [of_union _ (hmu.compl.inter hmt) ((hmv.compl.diff hmu.compl).inter hmt)]; rw [hu₂]; rw [hv₂]; rw [add_zero]
    · exact Set.Subset.trans Set.inter_subset_left sdiff_subset
    · exact Set.inter_subset_left
    · exact disjoint_sdiff_self_right.mono Set.inter_subset_left Set.inter_subset_left
    · apply Set.Subset.antisymm <;> intro x hx
      · by_cases hxu' : x in uᶜ
        · exact Or.inl ⟨hxu', hx⟩
        rcases ht hx with (hxu | hxv)
        exacts [False.elim (hxu' hxu), Or.inr ⟨⟨hxv, hxu'⟩, hx⟩]
      · rcases hx with hx | hx <;> exact hx.2

中文:
定理 add_left
  条件: [T2空间 N] [连续加法 M] (h₁ : v₁ ⟂ᵥ w) (h₂ : v₂ ⟂ᵥ w)
  结论: v₁ + v₂ ⟂ᵥ w
  证明: by
  obtain ⟨u, hmu, hu₁, hu₂⟩ := h₁
  obtain ⟨v, hmv, hv₁, hv₂⟩ := h₂
  refine mk (u inter v) (hmu.inter hmv) (fun t ht _ => ?_) fun t ht hmt => ?_
  · rw [_root_.add_apply, hu₁ _ (Set.subset_inter_iff.1 ht).1, hv₁ _ (Set.subset_inter_iff.1 ht).2,
      zero_add]
  · rw [Set.compl_inter] at ht
    rw [(_ : t = uᶜ inter t union vᶜ \ uᶜ inter t)]; rw [of_union _ (hmu.compl.inter hmt) ((hmv.compl.diff hmu.compl).inter hmt)]; rw [hu₂]; rw [hv₂]; rw [add_zero]
    · exact Set.Subset.trans Set.inter_subset_left sdiff_subset
    · exact Set.inter_subset_left
    · exact disjoint_sdiff_self_right.mono Set.inter_subset_left Set.inter_subset_left
    · apply Set.Subset.antisymm <;> intro x hx
      · by_cases hxu' : x in uᶜ
        · exact Or.inl ⟨hxu', hx⟩
        rcases ht hx with (hxu | hxv)
        exacts [False.elim (hxu' hxu), Or.inr ⟨⟨hxv, hxu'⟩, hx⟩]
      · rcases hx with hx | hx <;> exact hx.2

Depends on / 依赖: Set.Subset.trans, Set.compl_inter, Set.inter_subset_left, Set.subset_inter_iff, Subset, _root_, _root_.add_apply, add_apply, add_zero, compl_inter, hmu.compl, hmu.compl.inter, hmu.inter, hmv.compl.diff, inter_subset_left, of_union, sdiff_subset, subset_inter_iff, zero_add
-/
theorem add_left [T2Space N] [ContinuousAdd M] (h₁ : v₁ ⟂ᵥ w) (h₂ : v₂ ⟂ᵥ w) : v₁ + v₂ ⟂ᵥ w := by
  obtain ⟨u, hmu, hu₁, hu₂⟩ := h₁
  obtain ⟨v, hmv, hv₁, hv₂⟩ := h₂
  refine mk (u inter v) (hmu.inter hmv) (fun t ht _ => ?_) fun t ht hmt => ?_
  · rw [_root_.add_apply, hu₁ _ (Set.subset_inter_iff.1 ht).1, hv₁ _ (Set.subset_inter_iff.1 ht).2,
      zero_add]
  · rw [Set.compl_inter] at ht
    rw [(_ : t = uᶜ inter t union vᶜ \ uᶜ inter t)]; rw [of_union _ (hmu.compl.inter hmt) ((hmv.compl.diff hmu.compl).inter hmt)]; rw [hu₂]; rw [hv₂]; rw [add_zero]
    · exact Set.Subset.trans Set.inter_subset_left sdiff_subset
    · exact Set.inter_subset_left
    · exact disjoint_sdiff_self_right.mono Set.inter_subset_left Set.inter_subset_left
    · apply Set.Subset.antisymm <;> intro x hx
      · by_cases hxu' : x in uᶜ
        · exact Or.inl ⟨hxu', hx⟩
        rcases ht hx with (hxu | hxv)
        exacts [False.elim (hxu' hxu), Or.inr ⟨⟨hxv, hxu'⟩, hx⟩]
      · rcases hx with hx | hx <;> exact hx.2

/--
theorem `add_right` / 定理 `add_right`

English:
theorem add_right
  given: [T2Space M] [ContinuousAdd N] (h₁ : v ⟂ᵥ w₁) (h₂ : v ⟂ᵥ w₂)
  statement: v ⟂ᵥ w₁ + w₂
  proof: (add_left h₁.symm h₂.symm).symm

中文:
定理 add_right
  条件: [T2空间 M] [连续加法 N] (h₁ : v ⟂ᵥ w₁) (h₂ : v ⟂ᵥ w₂)
  结论: v ⟂ᵥ w₁ + w₂
  证明: (add_left h₁.symm h₂.symm).symm

Depends on / 依赖: add_left
-/
theorem add_right [T2Space M] [ContinuousAdd N] (h₁ : v ⟂ᵥ w₁) (h₂ : v ⟂ᵥ w₂) : v ⟂ᵥ w₁ + w₂ :=
  (add_left h₁.symm h₂.symm).symm

/--
theorem `smul_right` / 定理 `smul_right`

English:
theorem smul_right
  statement: {R : Type*} [Semiring R] [DistribMulAction R N] [ContinuousConstSMul R N]
  proof: let ⟨s, hmeas, hs₁, hs₂⟩ := h
  ⟨s, hmeas, hs₁, fun t ht => by simp only [_root_.smul_apply, hs₂ t ht, smul_zero]⟩

中文:
定理 smul_right
  结论: {R : 类型} [半环 R] [分配乘法作用 R N] [连续常数标量乘法 R N]
  证明: let ⟨s, hmeas, hs₁, hs₂⟩ := h
  ⟨s, hmeas, hs₁, fun t ht => by simp only [_root_.smul_apply, hs₂ t ht, smul_zero]⟩

Depends on / 依赖: _root_, _root_.smul_apply, smul_apply, smul_zero
-/
theorem smul_right {R : Type*} [Semiring R] [DistribMulAction R N] [ContinuousConstSMul R N]
    (r : R) (h : v ⟂ᵥ w) : v ⟂ᵥ r • w :=
  let ⟨s, hmeas, hs₁, hs₂⟩ := h
  ⟨s, hmeas, hs₁, fun t ht => by simp only [_root_.smul_apply, hs₂ t ht, smul_zero]⟩

/--
theorem `smul_left` / 定理 `smul_left`

English:
theorem smul_left
  statement: {R : Type*} [Semiring R] [DistribMulAction R M] [ContinuousConstSMul R M] (r : R)
  proof: (smul_right r h.symm).symm

中文:
定理 smul_left
  结论: {R : 类型} [半环 R] [分配乘法作用 R M] [连续常数标量乘法 R M] (r : R)
  证明: (smul_right r h.symm).symm

Depends on / 依赖: h.symm, smul_right
-/
theorem smul_left {R : Type*} [Semiring R] [DistribMulAction R M] [ContinuousConstSMul R M] (r : R)
    (h : v ⟂ᵥ w) : r • v ⟂ᵥ w :=
  (smul_right r h.symm).symm

/--
theorem `neg_left` / 定理 `neg_left`

English:
theorem neg_left
  statement: {M : Type*} [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  proof: by
  obtain ⟨u, hmu, hu₁, hu₂⟩ := h
  refine ⟨u, hmu, fun s hs => ?_, hu₂⟩
  rw [neg_apply v s]; rw [neg_eq_zero]
  exact hu₁ s hs

中文:
定理 neg_left
  结论: {M : 类型} [加法交换群 M] [拓扑空间 M] [是拓扑加群 M]
  证明: by
  obtain ⟨u, hmu, hu₁, hu₂⟩ := h
  refine ⟨u, hmu, fun s hs => ?_, hu₂⟩
  rw [neg_apply v s]; rw [neg_eq_zero]
  exact hu₁ s hs

Depends on / 依赖: neg_apply, neg_eq_zero
-/
theorem neg_left {M : Type*} [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
    {v : VectorMeasure α M} {w : VectorMeasure α N} (h : v ⟂ᵥ w) : -v ⟂ᵥ w := by
  obtain ⟨u, hmu, hu₁, hu₂⟩ := h
  refine ⟨u, hmu, fun s hs => ?_, hu₂⟩
  rw [neg_apply v s]; rw [neg_eq_zero]
  exact hu₁ s hs

/--
theorem `neg_right` / 定理 `neg_right`

English:
theorem neg_right
  statement: {N : Type*} [AddCommGroup N] [TopologicalSpace N] [IsTopologicalAddGroup N]
  proof: h.symm.neg_left.symm

@[simp]

中文:
定理 neg_right
  结论: {N : 类型} [加法交换群 N] [拓扑空间 N] [是拓扑加群 N]
  证明: h.symm.neg_left.symm

@[simp]

Depends on / 依赖: h.symm.neg_left.symm, neg_left
-/
theorem neg_right {N : Type*} [AddCommGroup N] [TopologicalSpace N] [IsTopologicalAddGroup N]
    {v : VectorMeasure α M} {w : VectorMeasure α N} (h : v ⟂ᵥ w) : v ⟂ᵥ -w :=
  h.symm.neg_left.symm

@[simp]
/--
theorem `neg_left_iff` / 定理 `neg_left_iff`

English:
theorem neg_left_iff
  statement: {M : Type*} [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  proof: ⟨fun h => neg_neg v ▸ h.neg_left, neg_left⟩

@[simp]

中文:
定理 neg_left_iff
  结论: {M : 类型} [加法交换群 M] [拓扑空间 M] [是拓扑加群 M]
  证明: ⟨fun h => neg_neg v ▸ h.neg_left, neg_left⟩

@[simp]

Depends on / 依赖: h.neg_left, neg_left, neg_neg
-/
theorem neg_left_iff {M : Type*} [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
    {v : VectorMeasure α M} {w : VectorMeasure α N} : -v ⟂ᵥ w ↔ v ⟂ᵥ w :=
  ⟨fun h => neg_neg v ▸ h.neg_left, neg_left⟩

@[simp]
/--
theorem `neg_right_iff` / 定理 `neg_right_iff`

English:
theorem neg_right_iff
  statement: {N : Type*} [AddCommGroup N] [TopologicalSpace N] [IsTopologicalAddGroup N]
  proof: ⟨fun h => neg_neg w ▸ h.neg_right, neg_right⟩

中文:
定理 neg_right_iff
  结论: {N : 类型} [加法交换群 N] [拓扑空间 N] [是拓扑加群 N]
  证明: ⟨fun h => neg_neg w ▸ h.neg_right, neg_right⟩

Depends on / 依赖: h.neg_right, neg_neg, neg_right
-/
theorem neg_right_iff {N : Type*} [AddCommGroup N] [TopologicalSpace N] [IsTopologicalAddGroup N]
    {v : VectorMeasure α M} {w : VectorMeasure α N} : v ⟂ᵥ -w ↔ v ⟂ᵥ w :=
  ⟨fun h => neg_neg w ▸ h.neg_right, neg_right⟩

end MutuallySingular

section Trim

open scoped Classical in
/-- Restriction of a vector measure onto a sub-σ-algebra. -/
@[simps]
/--
Definition of `trim` / `trim` 的定义

English:
definition trim
  signature: {m n : MeasurableSpace α} (v : VectorMeasure α M) (hle : m <= n)
  body: @VectorMeasure.mk α m M _ _
    (fun i => if MeasurableSet[m] i then v i else 0)
    (by rw [if_pos (@MeasurableSet.empty _ m), v.empty])
    (fun i hi => by rw [if_neg hi])
    (fun f hf₁ hf₂ => by
      have hf₁' : forall k, MeasurableSet[n] (f k) := fun k => hle _ (hf₁ k)
      convert! v.m_iUnion hf₁' hf₂ using 1
      · ext n
        rw [if_pos (hf₁ n)]
      · rw [if_pos (@MeasurableSet.iUnion _ _ m _ _ hf₁)])

中文:
定义 trim
  签名: {m n : 可测空间 α} (v : 向量测度 α M) (hle : m <= n)
  定义体: @VectorMeasure.mk α m M _ _
    (fun i => if MeasurableSet[m] i then v i else 0)
    (by rw [if_pos (@MeasurableSet.empty _ m), v.empty])
    (fun i hi => by rw [if_neg hi])
    (fun f hf₁ hf₂ => by
      have hf₁' : forall k, MeasurableSet[n] (f k) := fun k => hle _ (hf₁ k)
      convert! v.m_iUnion hf₁' hf₂ using 1
      · ext n
        rw [if_pos (hf₁ n)]
      · rw [if_pos (@MeasurableSet.iUnion _ _ m _ _ hf₁)])

Depends on / 依赖: MeasurableSet, MeasurableSet.empty, MeasurableSet.iUnion, VectorMeasure, VectorMeasure.mk, convert, iUnion, if_neg, if_pos, m_iUnion, v.empty, v.m_iUnion
-/
def trim {m n : MeasurableSpace α} (v : VectorMeasure α M) (hle : m <= n) :
    @VectorMeasure α m M _ _ :=
  @VectorMeasure.mk α m M _ _
    (fun i => if MeasurableSet[m] i then v i else 0)
    (by rw [if_pos (@MeasurableSet.empty _ m), v.empty])
    (fun i hi => by rw [if_neg hi])
    (fun f hf₁ hf₂ => by
      have hf₁' : forall k, MeasurableSet[n] (f k) := fun k => hle _ (hf₁ k)
      convert! v.m_iUnion hf₁' hf₂ using 1
      · ext n
        rw [if_pos (hf₁ n)]
      · rw [if_pos (@MeasurableSet.iUnion _ _ m _ _ hf₁)])

variable {n : MeasurableSpace α} {v : VectorMeasure α M}

/--
theorem `trim_eq_self` / 定理 `trim_eq_self`

English:
theorem trim_eq_self
  statement: v.trim le_rfl = v
  proof: by
  ext i hi
  exact if_pos hi

@[simp]

中文:
定理 trim_eq_self
  结论: v.trim le_rfl = v
  证明: by
  ext i hi
  exact if_pos hi

@[simp]

Depends on / 依赖: if_pos
-/
theorem trim_eq_self : v.trim le_rfl = v := by
  ext i hi
  exact if_pos hi

@[simp]
/--
theorem `zero_trim` / 定理 `zero_trim`

English:
theorem zero_trim
  given: (hle : m <= n)
  statement: (0 : VectorMeasure α M).trim hle = 0
  proof: by
  ext i hi
  exact if_pos hi

中文:
定理 zero_trim
  条件: (hle : m <= n)
  结论: (0 : 向量测度 α M).trim hle = 0
  证明: by
  ext i hi
  exact if_pos hi

Depends on / 依赖: if_pos
-/
theorem zero_trim (hle : m <= n) : (0 : VectorMeasure α M).trim hle = 0 := by
  ext i hi
  exact if_pos hi

/--
theorem `trim_measurableSet_eq` / 定理 `trim_measurableSet_eq`

English:
theorem trim_measurableSet_eq
  given: (hle : m <= n) {i : Set α} (hi : MeasurableSet[m] i)
  proof: if_pos hi

中文:
定理 trim_measurableSet_eq
  条件: (hle : m <= n) {i : 集合 α} (hi : 可测集[m] i)
  证明: if_pos hi

Depends on / 依赖: if_pos
-/
theorem trim_measurableSet_eq (hle : m <= n) {i : Set α} (hi : MeasurableSet[m] i) :
    v.trim hle i = v i :=
  if_pos hi

/--
theorem `restrict_trim` / 定理 `restrict_trim`

English:
theorem restrict_trim
  given: (hle : m <= n) {i : Set α} (hi : MeasurableSet[m] i)
  proof: by
  ext j hj
  rw [@restrict_apply _ m]; rw [trim_measurableSet_eq hle hj]; rw [restrict_apply]; rw [trim_measurableSet_eq]
  all_goals measurability

中文:
定理 restrict_trim
  条件: (hle : m <= n) {i : 集合 α} (hi : 可测集[m] i)
  证明: by
  ext j hj
  rw [@restrict_apply _ m]; rw [trim_measurableSet_eq hle hj]; rw [restrict_apply]; rw [trim_measurableSet_eq]
  all_goals measurability

Depends on / 依赖: all_goals, measurability, restrict_apply, trim_measurableSet_eq
-/
theorem restrict_trim (hle : m <= n) {i : Set α} (hi : MeasurableSet[m] i) :
    @VectorMeasure.restrict α m M _ _ (v.trim hle) i = (v.restrict i).trim hle := by
  ext j hj
  rw [@restrict_apply _ m]; rw [trim_measurableSet_eq hle hj]; rw [restrict_apply]; rw [trim_measurableSet_eq]
  all_goals measurability

end Trim

end

end VectorMeasure

namespace SignedMeasure

open VectorMeasure

open MeasureTheory

/--
Definition of `toMeasureOfZeroLE'` / `toMeasureOfZeroLE'` 的定义

English:
definition toMeasureOfZeroLE'
  signature: (s : SignedMeasure α) (i : Set α) (hi : 0 <=[i] s) (j : Set α)
  body: ((↑) : Real>=0 -> Real>=0∞) (.mk (s.restrict i j) (le_trans (by simp) (hi j hj)))

中文:
定义 toMeasureOfZeroLE'
  签名: (s : 符号测度 α) (i : 集合 α) (hi : 0 <=[i] s) (j : 集合 α)
  定义体: ((↑) : Real>=0 -> Real>=0∞) (.mk (s.restrict i j) (le_trans (by simp) (hi j hj)))

Depends on / 依赖: le_trans, restrict, s.restrict
-/
def toMeasureOfZeroLE' (s : SignedMeasure α) (i : Set α) (hi : 0 <=[i] s) (j : Set α)
    (hj : MeasurableSet j) : Real>=0∞ :=
  ((↑) : Real>=0 -> Real>=0∞) (.mk (s.restrict i j) (le_trans (by simp) (hi j hj)))

/--
Definition of `toMeasureOfZeroLE` / `toMeasureOfZeroLE` 的定义

English:
definition toMeasureOfZeroLE
  signature: (s : SignedMeasure α) (i : Set α) (hi₁ : MeasurableSet i) (hi₂ : 0 <=[i] s)
  body: by
  refine Measure.ofMeasurable (s.toMeasureOfZeroLE' i hi₂) ?_ ?_
  · simp_rw [toMeasureOfZeroLE', s.restrict_apply hi₁ MeasurableSet.empty, Set.empty_inter i,
      s.empty]
    rfl
  · intro f hf₁ hf₂
    have h₁ : forall n, MeasurableSet (i inter f n) := fun n => hi₁.inter (hf₁ n)
    have h₂ : Pairwise (Disjoint on fun n : Nat => i inter f n) := by
      intro n m hnm
      exact ((hf₂ hnm).inf_left' i).inf_right' i
    simp only [toMeasureOfZeroLE', s.restrict_apply hi₁ (MeasurableSet.iUnion hf₁), Set.inter_comm,
      Set.inter_iUnion, s.of_disjoint_iUnion h₁ h₂]
    have h : forall n, 0 <= s (i inter f n) := fun n =>
      s.nonneg_of_zero_le_restrict (s.zero_le_restrict_subset hi₁ Set.inter_subset_left hi₂)
    rw [NNReal.coe_tsum_of_nonneg h]; rw [ENNReal.coe_tsum]
    · refine tsum_congr fun n => ?_
      simp_rw [s.restrict_apply hi₁ (hf₁ n), Set.inter_comm]
    · exact (NNReal.summable_mk h).2 (s.m_iUnion h₁ h₂).summable

中文:
定义 toMeasureOfZeroLE
  签名: (s : 符号测度 α) (i : 集合 α) (hi₁ : 可测集 i) (hi₂ : 0 <=[i] s)
  定义体: by
  refine Measure.ofMeasurable (s.toMeasureOfZeroLE' i hi₂) ?_ ?_
  · simp_rw [toMeasureOfZeroLE', s.restrict_apply hi₁ MeasurableSet.empty, Set.empty_inter i,
      s.empty]
    rfl
  · intro f hf₁ hf₂
    have h₁ : forall n, MeasurableSet (i inter f n) := fun n => hi₁.inter (hf₁ n)
    have h₂ : Pairwise (Disjoint on fun n : Nat => i inter f n) := by
      intro n m hnm
      exact ((hf₂ hnm).inf_left' i).inf_right' i
    simp only [toMeasureOfZeroLE', s.restrict_apply hi₁ (MeasurableSet.iUnion hf₁), Set.inter_comm,
      Set.inter_iUnion, s.of_disjoint_iUnion h₁ h₂]
    have h : forall n, 0 <= s (i inter f n) := fun n =>
      s.nonneg_of_zero_le_restrict (s.zero_le_restrict_subset hi₁ Set.inter_subset_left hi₂)
    rw [NNReal.coe_tsum_of_nonneg h]; rw [ENNReal.coe_tsum]
    · refine tsum_congr fun n => ?_
      simp_rw [s.restrict_apply hi₁ (hf₁ n), Set.inter_comm]
    · exact (NNReal.summable_mk h).2 (s.m_iUnion h₁ h₂).summable

Depends on / 依赖: Disjoint, MeasurableSet, MeasurableSet.empty, MeasurableSet.iUnion, Measure, Measure.ofMeasurable, Pairwise, Set.empty_inter, Set.inter_comm, Set.inter_iUni, empty_inter, iUnion, inf_left, inf_right, inter_comm, inter_iUni, ofMeasurable, restrict_apply, s.empty, s.restrict_apply
-/
def toMeasureOfZeroLE (s : SignedMeasure α) (i : Set α) (hi₁ : MeasurableSet i) (hi₂ : 0 <=[i] s) :
    Measure α := by
  refine Measure.ofMeasurable (s.toMeasureOfZeroLE' i hi₂) ?_ ?_
  · simp_rw [toMeasureOfZeroLE', s.restrict_apply hi₁ MeasurableSet.empty, Set.empty_inter i,
      s.empty]
    rfl
  · intro f hf₁ hf₂
    have h₁ : forall n, MeasurableSet (i inter f n) := fun n => hi₁.inter (hf₁ n)
    have h₂ : Pairwise (Disjoint on fun n : Nat => i inter f n) := by
      intro n m hnm
      exact ((hf₂ hnm).inf_left' i).inf_right' i
    simp only [toMeasureOfZeroLE', s.restrict_apply hi₁ (MeasurableSet.iUnion hf₁), Set.inter_comm,
      Set.inter_iUnion, s.of_disjoint_iUnion h₁ h₂]
    have h : forall n, 0 <= s (i inter f n) := fun n =>
      s.nonneg_of_zero_le_restrict (s.zero_le_restrict_subset hi₁ Set.inter_subset_left hi₂)
    rw [NNReal.coe_tsum_of_nonneg h]; rw [ENNReal.coe_tsum]
    · refine tsum_congr fun n => ?_
      simp_rw [s.restrict_apply hi₁ (hf₁ n), Set.inter_comm]
    · exact (NNReal.summable_mk h).2 (s.m_iUnion h₁ h₂).summable

variable (s : SignedMeasure α) {i j : Set α}

/--
theorem `toMeasureOfZeroLE_apply` / 定理 `toMeasureOfZeroLE_apply`

English:
theorem toMeasureOfZeroLE_apply
  given: (hi : 0 <=[i] s) (hi₁ : MeasurableSet i) (hj₁ : MeasurableSet j)
  proof: by
  simp_rw [toMeasureOfZeroLE, Measure.ofMeasurable_apply _ hj₁, toMeasureOfZeroLE',
    s.restrict_apply hi₁ hj₁, Set.inter_comm]

中文:
定理 toMeasureOfZeroLE_apply
  条件: (hi : 0 <=[i] s) (hi₁ : 可测集 i) (hj₁ : 可测集 j)
  证明: by
  simp_rw [toMeasureOfZeroLE, Measure.ofMeasurable_apply _ hj₁, toMeasureOfZeroLE',
    s.restrict_apply hi₁ hj₁, Set.inter_comm]

Depends on / 依赖: Measure, Measure.ofMeasurable_apply, Set.inter_comm, inter_comm, ofMeasurable_apply, restrict_apply, s.restrict_apply, simp_rw, toMeasureOfZeroLE
-/
theorem toMeasureOfZeroLE_apply (hi : 0 <=[i] s) (hi₁ : MeasurableSet i) (hj₁ : MeasurableSet j) :
    s.toMeasureOfZeroLE i hi₁ hi j = ((↑) : Real>=0 -> Real>=0∞) (.mk (s (i inter j)) (nonneg_of_zero_le_restrict
      s (zero_le_restrict_subset s hi₁ Set.inter_subset_left hi))) := by
  simp_rw [toMeasureOfZeroLE, Measure.ofMeasurable_apply _ hj₁, toMeasureOfZeroLE',
    s.restrict_apply hi₁ hj₁, Set.inter_comm]

/--
theorem `toMeasureOfZeroLE_real_apply` / 定理 `toMeasureOfZeroLE_real_apply`

English:
theorem toMeasureOfZeroLE_real_apply
  statement: (hi : 0 <=[i] s) (hi₁ : MeasurableSet i)
  proof: by
  simp [measureReal_def, toMeasureOfZeroLE_apply, hj₁]

中文:
定理 toMeasureOfZeroLE_real_apply
  结论: (hi : 0 <=[i] s) (hi₁ : 可测集 i)
  证明: by
  simp [measureReal_def, toMeasureOfZeroLE_apply, hj₁]

Depends on / 依赖: measureReal_def, toMeasureOfZeroLE_apply
-/
theorem toMeasureOfZeroLE_real_apply (hi : 0 <=[i] s) (hi₁ : MeasurableSet i)
    (hj₁ : MeasurableSet j) :
    (s.toMeasureOfZeroLE i hi₁ hi).real j = s (i inter j) := by
  simp [measureReal_def, toMeasureOfZeroLE_apply, hj₁]

/--
Definition of `toMeasureOfLEZero` / `toMeasureOfLEZero` 的定义

English:
definition toMeasureOfLEZero
  signature: (s : SignedMeasure α) (i : Set α) (hi₁ : MeasurableSet i) (hi₂ : s <=[i] 0)
  body: toMeasureOfZeroLE (-s) i hi₁ @neg_zero (VectorMeasure α Real) _ ▸ neg_le_neg _ _ hi₁ hi₂

中文:
定义 toMeasureOfLEZero
  签名: (s : 符号测度 α) (i : 集合 α) (hi₁ : 可测集 i) (hi₂ : s <=[i] 0)
  定义体: toMeasureOfZeroLE (-s) i hi₁ @neg_zero (VectorMeasure α Real) _ ▸ neg_le_neg _ _ hi₁ hi₂

Depends on / 依赖: VectorMeasure, neg_le_neg, neg_zero, toMeasureOfZeroLE
-/
def toMeasureOfLEZero (s : SignedMeasure α) (i : Set α) (hi₁ : MeasurableSet i) (hi₂ : s <=[i] 0) :
    Measure α :=
toMeasureOfZeroLE (-s) i hi₁ @neg_zero (VectorMeasure α Real) _ ▸ neg_le_neg _ _ hi₁ hi₂

/--
theorem `toMeasureOfLEZero_apply` / 定理 `toMeasureOfLEZero_apply`

English:
theorem toMeasureOfLEZero_apply
  given: (hi : s <=[i] 0) (hi₁ : MeasurableSet i) (hj₁ : MeasurableSet j)
  proof: by
  simp [toMeasureOfLEZero, toMeasureOfZeroLE_apply _ _ _ hj₁]

中文:
定理 toMeasureOfLEZero_apply
  条件: (hi : s <=[i] 0) (hi₁ : 可测集 i) (hj₁ : 可测集 j)
  证明: by
  simp [toMeasureOfLEZero, toMeasureOfZeroLE_apply _ _ _ hj₁]

Depends on / 依赖: toMeasureOfLEZero, toMeasureOfZeroLE_apply
-/
theorem toMeasureOfLEZero_apply (hi : s <=[i] 0) (hi₁ : MeasurableSet i) (hj₁ : MeasurableSet j) :
    s.toMeasureOfLEZero i hi₁ hi j =
    ((↑) : Real>=0 -> Real>=0∞) (NNReal.mk (-s (i inter j)) (neg_apply s (i inter j) ▸
      nonneg_of_zero_le_restrict _ (zero_le_restrict_subset _ hi₁ Set.inter_subset_left
      (@neg_zero (VectorMeasure α Real) _ ▸ neg_le_neg _ _ hi₁ hi)))) := by
  simp [toMeasureOfLEZero, toMeasureOfZeroLE_apply _ _ _ hj₁]

/--
theorem `toMeasureOfLEZero_real_apply` / 定理 `toMeasureOfLEZero_real_apply`

English:
theorem toMeasureOfLEZero_real_apply
  statement: (hi : s <=[i] 0) (hi₁ : MeasurableSet i)
  proof: by
  simp [measureReal_def, toMeasureOfLEZero_apply _ hi hi₁ hj₁]

中文:
定理 toMeasureOfLEZero_real_apply
  结论: (hi : s <=[i] 0) (hi₁ : 可测集 i)
  证明: by
  simp [measureReal_def, toMeasureOfLEZero_apply _ hi hi₁ hj₁]

Depends on / 依赖: measureReal_def, toMeasureOfLEZero_apply
-/
theorem toMeasureOfLEZero_real_apply (hi : s <=[i] 0) (hi₁ : MeasurableSet i)
    (hj₁ : MeasurableSet j) :
    (s.toMeasureOfLEZero i hi₁ hi).real j = -s (i inter j) := by
  simp [measureReal_def, toMeasureOfLEZero_apply _ hi hi₁ hj₁]

/--
Instance `toMeasureOfZeroLE_finite` / 实例 `toMeasureOfZeroLE_finite`

English:
instance toMeasureOfZeroLE_finite
  signature: (hi : 0 <=[i] s) (hi₁ : MeasurableSet i)
  body: by
    rw [toMeasureOfZeroLE_apply s hi hi₁ MeasurableSet.univ]
    exact ENNReal.coe_lt_top

中文:
实例 toMeasureOfZeroLE_finite
  签名: (hi : 0 <=[i] s) (hi₁ : 可测集 i)
  定义体: by
    rw [toMeasureOfZeroLE_apply s hi hi₁ MeasurableSet.univ]
    exact ENNReal.coe_lt_top

Depends on / 依赖: ENNReal, ENNReal.coe_lt_top, MeasurableSet, MeasurableSet.univ, coe_lt_top, toMeasureOfZeroLE_apply
-/
instance toMeasureOfZeroLE_finite (hi : 0 <=[i] s) (hi₁ : MeasurableSet i) :
    IsFiniteMeasure (s.toMeasureOfZeroLE i hi₁ hi) where
  measure_univ_lt_top := by
    rw [toMeasureOfZeroLE_apply s hi hi₁ MeasurableSet.univ]
    exact ENNReal.coe_lt_top

/--
Instance `toMeasureOfLEZero_finite` / 实例 `toMeasureOfLEZero_finite`

English:
instance toMeasureOfLEZero_finite
  signature: (hi : s <=[i] 0) (hi₁ : MeasurableSet i)
  body: by
    rw [toMeasureOfLEZero_apply s hi hi₁ MeasurableSet.univ]
    exact ENNReal.coe_lt_top

中文:
实例 toMeasureOfLEZero_finite
  签名: (hi : s <=[i] 0) (hi₁ : 可测集 i)
  定义体: by
    rw [toMeasureOfLEZero_apply s hi hi₁ MeasurableSet.univ]
    exact ENNReal.coe_lt_top

Depends on / 依赖: ENNReal, ENNReal.coe_lt_top, MeasurableSet, MeasurableSet.univ, coe_lt_top, toMeasureOfLEZero_apply
-/
instance toMeasureOfLEZero_finite (hi : s <=[i] 0) (hi₁ : MeasurableSet i) :
    IsFiniteMeasure (s.toMeasureOfLEZero i hi₁ hi) where
  measure_univ_lt_top := by
    rw [toMeasureOfLEZero_apply s hi hi₁ MeasurableSet.univ]
    exact ENNReal.coe_lt_top

/--
theorem `toMeasureOfZeroLE_toSignedMeasure` / 定理 `toMeasureOfZeroLE_toSignedMeasure`

English:
theorem toMeasureOfZeroLE_toSignedMeasure
  given: (hs : 0 <=[Set.univ] s)
  proof: by
  ext i hi
  simp [hi, toMeasureOfZeroLE_apply _ _ _ hi, measureReal_def]

中文:
定理 toMeasureOfZeroLE_toSignedMeasure
  条件: (hs : 0 <=[集合.univ] s)
  证明: by
  ext i hi
  simp [hi, toMeasureOfZeroLE_apply _ _ _ hi, measureReal_def]

Depends on / 依赖: measureReal_def, toMeasureOfZeroLE_apply
-/
theorem toMeasureOfZeroLE_toSignedMeasure (hs : 0 <=[Set.univ] s) :
    (s.toMeasureOfZeroLE Set.univ MeasurableSet.univ hs).toSignedMeasure = s := by
  ext i hi
  simp [hi, toMeasureOfZeroLE_apply _ _ _ hi, measureReal_def]

/--
theorem `toMeasureOfLEZero_toSignedMeasure` / 定理 `toMeasureOfLEZero_toSignedMeasure`

English:
theorem toMeasureOfLEZero_toSignedMeasure
  given: (hs : s <=[Set.univ] 0)
  proof: by
  ext i hi
  simp [hi, toMeasureOfLEZero_apply _ _ _ hi, measureReal_def]

中文:
定理 toMeasureOfLEZero_toSignedMeasure
  条件: (hs : s <=[集合.univ] 0)
  证明: by
  ext i hi
  simp [hi, toMeasureOfLEZero_apply _ _ _ hi, measureReal_def]

Depends on / 依赖: measureReal_def, toMeasureOfLEZero_apply
-/
theorem toMeasureOfLEZero_toSignedMeasure (hs : s <=[Set.univ] 0) :
    (s.toMeasureOfLEZero Set.univ MeasurableSet.univ hs).toSignedMeasure = -s := by
  ext i hi
  simp [hi, toMeasureOfLEZero_apply _ _ _ hi, measureReal_def]

end SignedMeasure

namespace Measure

open VectorMeasure

variable (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν] (s : Set α)

/--
theorem `zero_le_toSignedMeasure` / 定理 `zero_le_toSignedMeasure`

English:
theorem zero_le_toSignedMeasure
  statement: 0 <= μ.toSignedMeasure
  proof: by
  rw [← le_restrict_univ_iff_le]
  refine restrict_le_restrict_of_subset_le _ _ fun j hj₁ _ => ?_
  simp [hj₁]

中文:
定理 zero_le_toSignedMeasure
  结论: 0 <= μ.toSignedMeasure
  证明: by
  rw [← le_restrict_univ_iff_le]
  refine restrict_le_restrict_of_subset_le _ _ fun j hj₁ _ => ?_
  simp [hj₁]

Depends on / 依赖: le_restrict_univ_iff_le, restrict_le_restrict_of_subset_le
-/
theorem zero_le_toSignedMeasure : 0 <= μ.toSignedMeasure := by
  rw [← le_restrict_univ_iff_le]
  refine restrict_le_restrict_of_subset_le _ _ fun j hj₁ _ => ?_
  simp [hj₁]

/--
theorem `toSignedMeasure_toMeasureOfZeroLE` / 定理 `toSignedMeasure_toMeasureOfZeroLE`

English:
theorem toSignedMeasure_toMeasureOfZeroLE
  proof: by
  refine Measure.ext fun i hi => ?_
  lift μ i to Real>=0 using (measure_lt_top _ _).ne with m hm
  rw [SignedMeasure.toMeasureOfZeroLE_apply _ _ _ hi]; rw [ENNReal.coe_inj]
  congr
  simp [hi, ← hm, measureReal_def]

中文:
定理 toSignedMeasure_toMeasureOfZeroLE
  证明: by
  refine Measure.ext fun i hi => ?_
  lift μ i to Real>=0 using (measure_lt_top _ _).ne with m hm
  rw [SignedMeasure.toMeasureOfZeroLE_apply _ _ _ hi]; rw [ENNReal.coe_inj]
  congr
  simp [hi, ← hm, measureReal_def]

Depends on / 依赖: ENNReal, ENNReal.coe_inj, Measure, Measure.ext, SignedMeasure, SignedMeasure.toMeasureOfZeroLE_apply, coe_inj, measureReal_def, measure_lt_top, toMeasureOfZeroLE_apply
-/
theorem toSignedMeasure_toMeasureOfZeroLE :
    μ.toSignedMeasure.toMeasureOfZeroLE Set.univ MeasurableSet.univ
      ((le_restrict_univ_iff_le _ _).2 (zero_le_toSignedMeasure μ)) = μ := by
  refine Measure.ext fun i hi => ?_
  lift μ i to Real>=0 using (measure_lt_top _ _).ne with m hm
  rw [SignedMeasure.toMeasureOfZeroLE_apply _ _ _ hi]; rw [ENNReal.coe_inj]
  congr
  simp [hi, ← hm, measureReal_def]

/--
theorem `toSignedMeasure_restrict_eq_restrict_toSignedMeasure` / 定理 `toSignedMeasure_restrict_eq_restrict_toSignedMeasure`

English:
theorem toSignedMeasure_restrict_eq_restrict_toSignedMeasure
  given: (hs : MeasurableSet s)
  proof: by
  ext A hA
  simp [VectorMeasure.restrict_apply, hA, hs]

中文:
定理 toSignedMeasure_restrict_eq_restrict_toSignedMeasure
  条件: (hs : 可测集 s)
  证明: by
  ext A hA
  simp [VectorMeasure.restrict_apply, hA, hs]

Depends on / 依赖: VectorMeasure, VectorMeasure.restrict_apply, restrict_apply
-/
theorem toSignedMeasure_restrict_eq_restrict_toSignedMeasure (hs : MeasurableSet s) :
    μ.toSignedMeasure.restrict s = (μ.restrict s).toSignedMeasure := by
  ext A hA
  simp [VectorMeasure.restrict_apply, hA, hs]

/--
theorem `toSignedMeasure_le_toSignedMeasure_iff` / 定理 `toSignedMeasure_le_toSignedMeasure_iff`

English:
theorem toSignedMeasure_le_toSignedMeasure_iff
  proof: by
  rw [Measure.le_iff]; rw [VectorMeasure.le_iff]
  congrm forall s, (hs : MeasurableSet s) -> ?_
  simp_rw [toSignedMeasure_apply_measurable hs, real_def]
  apply ENNReal.toReal_le_toReal <;> finiteness

中文:
定理 toSignedMeasure_le_toSignedMeasure_iff
  证明: by
  rw [Measure.le_iff]; rw [VectorMeasure.le_iff]
  congrm forall s, (hs : MeasurableSet s) -> ?_
  simp_rw [toSignedMeasure_apply_measurable hs, real_def]
  apply ENNReal.toReal_le_toReal <;> finiteness

Depends on / 依赖: ENNReal, ENNReal.toReal_le_toReal, MeasurableSet, Measure, Measure.le_iff, VectorMeasure, VectorMeasure.le_iff, congrm, finiteness, le_iff, real_def, simp_rw, toReal_le_toReal, toSignedMeasure_apply_measurable
-/
theorem toSignedMeasure_le_toSignedMeasure_iff :
    μ.toSignedMeasure <= ν.toSignedMeasure ↔ μ <= ν := by
  rw [Measure.le_iff]; rw [VectorMeasure.le_iff]
  congrm forall s, (hs : MeasurableSet s) -> ?_
  simp_rw [toSignedMeasure_apply_measurable hs, real_def]
  apply ENNReal.toReal_le_toReal <;> finiteness

end Measure

end MeasureTheory
