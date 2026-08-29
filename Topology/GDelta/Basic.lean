/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Yury Kudryashov
-/
module

public import Mathlib.Order.Filter.CountableInter
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Data.Set.Notation
import Mathlib.Topology.Constructions

/-!
# `Gδ` sets

In this file we define `Gδ` sets and prove their basic properties.

## Main definitions

* `IsGδ`: a set `s` is a `Gδ` set if it can be represented as an intersection
  of countably many open sets;

* `residual`: the σ-filter of residual sets. A set `s` is called *residual* if it includes a
  countable intersection of dense open sets.

* `IsNowhereDense`: a set is called *nowhere dense* iff its closure has empty interior
* `IsMeagre`: a set `s` is called *meagre* iff its complement is residual

## Main results

We prove that finite or countable intersections of Gδ sets are Gδ sets.

- `isClosed_isNowhereDense_iff_compl`: a closed set is nowhere dense iff
  its complement is open and dense
- `isMeagre_iff_countable_union_isNowhereDense`: a set is meagre iff it is contained in a countable
  union of nowhere dense sets
- subsets of meagre sets are meagre; countable unions of meagre sets are meagre

See `Mathlib/Topology/GDelta/MetrizableSpace.lean` for the proof that
continuity set of a function from a topological space to a metrizable space is a Gδ set.

## Tags

Gδ set, residual set, nowhere dense set, meagre set
-/

@[expose] public section

assert_not_exists UniformSpace

noncomputable section

open Topology TopologicalSpace Filter Encodable Set

variable {X Y ι : Type*} {ι' : Sort*}


section IsGδ

variable [TopologicalSpace X]

/--
Definition of `IsGδ` / `IsGδ` 的定义

English:
definition IsGδ
  signature: (s : Set X)
  body: exists T : Set (Set X), (forall t in T, IsOpen t) ∧ T.Countable ∧ s = ⋂₀ T

中文:
定义 IsGδ
  签名: (s : 集合 X)
  定义体: exists T : Set (Set X), (forall t in T, IsOpen t) ∧ T.Countable ∧ s = ⋂₀ T

Depends on / 依赖: Countable, IsOpen, T.Countable
-/
def IsGδ (s : Set X) : Prop :=
  exists T : Set (Set X), (forall t in T, IsOpen t) ∧ T.Countable ∧ s = ⋂₀ T

/--
theorem `IsOpen.isGδ` / 定理 `IsOpen.isGδ`

English:
theorem IsOpen.isGδ
  given: {s : Set X} (h : IsOpen s)
  statement: IsGδ s
  proof: ⟨{s}, by simp [h], countable_singleton _, (Set.sInter_singleton _).symm⟩

@[simp]

中文:
定理 是开集.isGδ
  条件: {s : 集合 X} (h : 是开集 s)
  结论: IsGδ s
  证明: ⟨{s}, by simp [h], countable_singleton _, (Set.sInter_singleton _).symm⟩

@[simp]

Depends on / 依赖: Set.sInter_singleton, countable_singleton, sInter_singleton
-/
theorem IsOpen.isGδ {s : Set X} (h : IsOpen s) : IsGδ s :=
  ⟨{s}, by simp [h], countable_singleton _, (Set.sInter_singleton _).symm⟩

@[simp]
/--
theorem `IsGδ.empty` / 定理 `IsGδ.empty`

English:
theorem IsGδ.empty
  statement: IsGδ (∅ : Set X)
  proof: isOpen_empty.isGδ


@[simp]

中文:
定理 IsGδ.empty
  结论: IsGδ (∅ : 集合 X)
  证明: isOpen_empty.isGδ


@[simp]
-/
protected theorem IsGδ.empty : IsGδ (∅ : Set X) :=
  isOpen_empty.isGδ


@[simp]
/--
theorem `IsGδ.univ` / 定理 `IsGδ.univ`

English:
theorem IsGδ.univ
  statement: IsGδ (univ : Set X)
  proof: isOpen_univ.isGδ

中文:
定理 IsGδ.univ
  结论: IsGδ (univ : 集合 X)
  证明: isOpen_univ.isGδ
-/
protected theorem IsGδ.univ : IsGδ (univ : Set X) :=
  isOpen_univ.isGδ


/--
theorem `IsGδ.biInter_of_isOpen` / 定理 `IsGδ.biInter_of_isOpen`

English:
theorem IsGδ.biInter_of_isOpen
  statement: {I : Set ι} (hI : I.Countable) {f : ι -> Set X}
  proof: ⟨f '' I, by rwa [forall_mem_image], hI.image _, by rw [sInter_image]⟩

中文:
定理 IsGδ.bi整数er_of_isOpen
  结论: {I : 集合 ι} (hI : I.可数) {f : ι -> 集合 X}
  证明: ⟨f '' I, by rwa [forall_mem_image], hI.image _, by rw [sInter_image]⟩

Depends on / 依赖: forall_mem_image, hI.image, sInter_image
-/
theorem IsGδ.biInter_of_isOpen {I : Set ι} (hI : I.Countable) {f : ι -> Set X}
    (hf : forall i in I, IsOpen (f i)) : IsGδ (⋂ i in I, f i) :=
  ⟨f '' I, by rwa [forall_mem_image], hI.image _, by rw [sInter_image]⟩


/--
theorem `IsGδ.iInter_of_isOpen` / 定理 `IsGδ.iInter_of_isOpen`

English:
theorem IsGδ.iInter_of_isOpen
  given: [Countable ι'] {f : ι' -> Set X} (hf : forall i, IsOpen (f i))
  proof: ⟨range f, by rwa [forall_mem_range], countable_range _, by rw [sInter_range]⟩

中文:
定理 IsGδ.i整数er_of_isOpen
  条件: [可数 ι'] {f : ι' -> 集合 X} (hf : 对任意 i, 是开集 (f i))
  证明: ⟨range f, by rwa [forall_mem_range], countable_range _, by rw [sInter_range]⟩

Depends on / 依赖: countable_range, forall_mem_range, sInter_range
-/
theorem IsGδ.iInter_of_isOpen [Countable ι'] {f : ι' -> Set X} (hf : forall i, IsOpen (f i)) :
    IsGδ (⋂ i, f i) :=
  ⟨range f, by rwa [forall_mem_range], countable_range _, by rw [sInter_range]⟩


/--
lemma `isGδ_iff_eq_iInter_nat` / 引理 `isGδ_iff_eq_iInter_nat`

English:
lemma isGδ_iff_eq_iInter_nat
  given: {s : Set X}
  proof: by
  refine ⟨?_, ?_⟩
  · rintro ⟨T, hT, T_count, rfl⟩
    rcases Set.eq_empty_or_nonempty T with rfl | hT
    · exact ⟨fun _n => univ, fun _n => isOpen_univ, by simp⟩
    · obtain ⟨f, hf⟩ : exists (f : Nat -> Set X), T = range f := Countable.exists_eq_range T_count hT
      exact ⟨f, by simp_all, by

中文:
引理 isGδ_iff_eq_i整数er_nat
  条件: {s : 集合 X}
  证明: by
  refine ⟨?_, ?_⟩
  · rintro ⟨T, hT, T_count, rfl⟩
    rcases Set.eq_empty_or_nonempty T with rfl | hT
    · exact ⟨fun _n => univ, fun _n => isOpen_univ, by simp⟩
    · obtain ⟨f, hf⟩ : exists (f : Nat -> Set X), T = range f := Countable.exists_eq_range T_count hT
      exact ⟨f, by simp_all, by

Depends on / 依赖: Countable, Countable.exists_eq_range, Set.eq_empty_or_nonempty, T_count, eq_empty_or_nonempty, exists_eq_range, iInter_of_isOpen, isOpen_univ
-/
lemma isGδ_iff_eq_iInter_nat {s : Set X} :
    IsGδ s ↔ exists (f : Nat -> Set X), (forall n, IsOpen (f n)) ∧ s = ⋂ n, f n := by
  refine ⟨?_, ?_⟩
  · rintro ⟨T, hT, T_count, rfl⟩
    rcases Set.eq_empty_or_nonempty T with rfl | hT
    · exact ⟨fun _n => univ, fun _n => isOpen_univ, by simp⟩
    · obtain ⟨f, hf⟩ : exists (f : Nat -> Set X), T = range f := Countable.exists_eq_range T_count hT
      exact ⟨f, by simp_all, by simp [hf]⟩
  · rintro ⟨f, hf, rfl⟩
    exact .iInter_of_isOpen hf

alias ⟨IsGδ.eq_iInter_nat, _⟩ := isGδ_iff_eq_iInter_nat

/--
theorem `IsGδ.iInter` / 定理 `IsGδ.iInter`

English:
theorem IsGδ.iInter
  given: [Countable ι'] {s : ι' -> Set X} (hs : forall i, IsGδ (s i))
  proof: by
  choose T hTo hTc hTs using hs
  obtain rfl : s = fun i => ⋂₀ T i := funext hTs
  refine ⟨⋃ i, T i, ?_, countable_iUnion hTc, (sInter_iUnion _).symm⟩
  simpa [@forall_comm ι'] using hTo

中文:
定理 IsGδ.i整数er
  条件: [可数 ι'] {s : ι' -> 集合 X} (hs : 对任意 i, IsGδ (s i))
  证明: by
  choose T hTo hTc hTs using hs
  obtain rfl : s = fun i => ⋂₀ T i := funext hTs
  refine ⟨⋃ i, T i, ?_, countable_iUnion hTc, (sInter_iUnion _).symm⟩
  simpa [@forall_comm ι'] using hTo
-/
protected theorem IsGδ.iInter [Countable ι'] {s : ι' -> Set X} (hs : forall i, IsGδ (s i)) :
    IsGδ (⋂ i, s i) := by
  choose T hTo hTc hTs using hs
  obtain rfl : s = fun i => ⋂₀ T i := funext hTs
  refine ⟨⋃ i, T i, ?_, countable_iUnion hTc, (sInter_iUnion _).symm⟩
  simpa [@forall_comm ι'] using hTo

/--
theorem `IsGδ.biInter` / 定理 `IsGδ.biInter`

English:
theorem IsGδ.biInter
  statement: {s : Set ι} (hs : s.Countable) {t : forall i in s, Set X}
  proof: by
  rw [biInter_eq_iInter]
  have := hs.to_subtype
  exact .iInter fun x => ht x x.2

中文:
定理 IsGδ.bi整数er
  结论: {s : 集合 ι} (hs : s.可数) {t : 对任意 i in s, 集合 X}
  证明: by
  rw [biInter_eq_iInter]
  have := hs.to_subtype
  exact .iInter fun x => ht x x.2

Depends on / 依赖: biInter_eq_iInter, hs.to_subtype, iInter, to_subtype
-/
theorem IsGδ.biInter {s : Set ι} (hs : s.Countable) {t : forall i in s, Set X}
    (ht : forall (i) (hi : i in s), IsGδ (t i hi)) : IsGδ (⋂ i in s, t i ‹_›) := by
  rw [biInter_eq_iInter]
  have := hs.to_subtype
  exact .iInter fun x => ht x x.2


/--
theorem `IsGδ.sInter` / 定理 `IsGδ.sInter`

English:
theorem IsGδ.sInter
  given: {S : Set (Set X)} (h : forall s in S, IsGδ s) (hS : S.Countable)
  statement: IsGδ (⋂₀ S)
  proof: by
  simpa only [sInter_eq_biInter] using IsGδ.biInter hS h

中文:
定理 IsGδ.集合交集
  条件: {S : 集合 (集合 X)} (h : 对任意 s in S, IsGδ s) (hS : S.可数)
  结论: IsGδ (⋂₀ S)
  证明: by
  simpa only [sInter_eq_biInter] using IsGδ.biInter hS h

Depends on / 依赖: biInter, sInter_eq_biInter
-/
theorem IsGδ.sInter {S : Set (Set X)} (h : forall s in S, IsGδ s) (hS : S.Countable) : IsGδ (⋂₀ S) := by
  simpa only [sInter_eq_biInter] using IsGδ.biInter hS h


/--
theorem `IsGδ.inter` / 定理 `IsGδ.inter`

English:
theorem IsGδ.inter
  given: {s t : Set X} (hs : IsGδ s) (ht : IsGδ t)
  statement: IsGδ (s inter t)
  proof: by
  rw [inter_eq_iInter]
  exact .iInter (Bool.forall_bool.2 ⟨ht, hs⟩)

中文:
定理 IsGδ.inter
  条件: {s t : 集合 X} (hs : IsGδ s) (ht : IsGδ t)
  结论: IsGδ (s inter t)
  证明: by
  rw [inter_eq_iInter]
  exact .iInter (Bool.forall_bool.2 ⟨ht, hs⟩)

Depends on / 依赖: Bool.forall_bool, forall_bool, iInter, inter_eq_iInter
-/
theorem IsGδ.inter {s t : Set X} (hs : IsGδ s) (ht : IsGδ t) : IsGδ (s inter t) := by
  rw [inter_eq_iInter]
  exact .iInter (Bool.forall_bool.2 ⟨ht, hs⟩)

/--
theorem `IsGδ.union` / 定理 `IsGδ.union`

English:
theorem IsGδ.union
  given: {s t : Set X} (hs : IsGδ s) (ht : IsGδ t)
  statement: IsGδ (s union t)
  proof: by
  rcases hs with ⟨S, Sopen, Scount, rfl⟩
  rcases ht with ⟨T, Topen, Tcount, rfl⟩
  rw [sInter_union_sInter]
  refine .biInter_of_isOpen (Scount.prod Tcount) ?_
  rintro ⟨a, b⟩ ⟨ha, hb⟩
  exact (Sopen a ha).union (Topen b hb)

中文:
定理 IsGδ.union
  条件: {s t : 集合 X} (hs : IsGδ s) (ht : IsGδ t)
  结论: IsGδ (s union t)
  证明: by
  rcases hs with ⟨S, Sopen, Scount, rfl⟩
  rcases ht with ⟨T, Topen, Tcount, rfl⟩
  rw [sInter_union_sInter]
  refine .biInter_of_isOpen (Scount.prod Tcount) ?_
  rintro ⟨a, b⟩ ⟨ha, hb⟩
  exact (Sopen a ha).union (Topen b hb)

Depends on / 依赖: Scount, Scount.prod, Tcount, biInter_of_isOpen, sInter_union_sInter
-/
theorem IsGδ.union {s t : Set X} (hs : IsGδ s) (ht : IsGδ t) : IsGδ (s union t) := by
  rcases hs with ⟨S, Sopen, Scount, rfl⟩
  rcases ht with ⟨T, Topen, Tcount, rfl⟩
  rw [sInter_union_sInter]
  refine .biInter_of_isOpen (Scount.prod Tcount) ?_
  rintro ⟨a, b⟩ ⟨ha, hb⟩
  exact (Sopen a ha).union (Topen b hb)

/--
theorem `IsGδ.sUnion` / 定理 `IsGδ.sUnion`

English:
theorem IsGδ.sUnion
  given: {S : Set (Set X)} (hS : S.Finite) (h : forall s in S, IsGδ s)
  statement: IsGδ (⋃₀ S)
  proof: by
  induction S, hS using Set.Finite.induction_on with
  | empty => simp
  | insert _ _ ih =>
    simp only [forall_mem_insert, sUnion_insert] at *
    exact h.1.union (ih h.2)

中文:
定理 IsGδ.集合并集
  条件: {S : 集合 (集合 X)} (hS : S.有限) (h : 对任意 s in S, IsGδ s)
  结论: IsGδ (⋃₀ S)
  证明: by
  induction S, hS using Set.Finite.induction_on with
  | empty => simp
  | insert _ _ ih =>
    simp only [forall_mem_insert, sUnion_insert] at *
    exact h.1.union (ih h.2)

Depends on / 依赖: Finite, Set.Finite.induction_on, forall_mem_insert, induction_on, insert, sUnion_insert
-/
theorem IsGδ.sUnion {S : Set (Set X)} (hS : S.Finite) (h : forall s in S, IsGδ s) : IsGδ (⋃₀ S) := by
  induction S, hS using Set.Finite.induction_on with
  | empty => simp
  | insert _ _ ih =>
    simp only [forall_mem_insert, sUnion_insert] at *
    exact h.1.union (ih h.2)

/--
theorem `IsGδ.biUnion` / 定理 `IsGδ.biUnion`

English:
theorem IsGδ.biUnion
  given: {s : Set ι} (hs : s.Finite) {f : ι -> Set X} (h : forall i in s, IsGδ (f i))
  proof: by
  rw [← sUnion_image]
  exact .sUnion (hs.image _) (forall_mem_image.2 h)

中文:
定理 IsGδ.biUnion
  条件: {s : 集合 ι} (hs : s.有限) {f : ι -> 集合 X} (h : 对任意 i in s, IsGδ (f i))
  证明: by
  rw [← sUnion_image]
  exact .sUnion (hs.image _) (forall_mem_image.2 h)

Depends on / 依赖: forall_mem_image, hs.image, sUnion, sUnion_image
-/
theorem IsGδ.biUnion {s : Set ι} (hs : s.Finite) {f : ι -> Set X} (h : forall i in s, IsGδ (f i)) :
    IsGδ (⋃ i in s, f i) := by
  rw [← sUnion_image]
  exact .sUnion (hs.image _) (forall_mem_image.2 h)

/--
theorem `IsGδ.iUnion` / 定理 `IsGδ.iUnion`

English:
theorem IsGδ.iUnion
  given: [Finite ι'] {f : ι' -> Set X} (h : forall i, IsGδ (f i))
  statement: IsGδ (⋃ i, f i)
  proof: .sUnion (finite_range _) forall_mem_range.2 h

中文:
定理 IsGδ.iUnion
  条件: [有限 ι'] {f : ι' -> 集合 X} (h : 对任意 i, IsGδ (f i))
  结论: IsGδ (⋃ i, f i)
  证明: .sUnion (finite_range _) forall_mem_range.2 h

Depends on / 依赖: finite_range, forall_mem_range, sUnion
-/
theorem IsGδ.iUnion [Finite ι'] {f : ι' -> Set X} (h : forall i, IsGδ (f i)) : IsGδ (⋃ i, f i) :=
.sUnion (finite_range _) forall_mem_range.2 h

/--
theorem `IsGδ.preimage` / 定理 `IsGδ.preimage`

English:
theorem IsGδ.preimage
  statement: [TopologicalSpace Y] {f : X -> Y} {s : Set Y} (hf : Continuous f)
  proof: by
  obtain ⟨U, hU1, hU2⟩ := hs.eq_iInter_nat
  simp_all only [preimage_iInter]
  exact IsGδ.iInter_of_isOpen (fun i => hf.isOpen_preimage (U i) (hU1 i))

@[deprecated (since := "2026-05-19")] alias isGδ_induced := IsGδ.preimage

中文:
定理 IsGδ.原像
  结论: [拓扑空间 Y] {f : X -> Y} {s : 集合 Y} (hf : 连续 f)
  证明: by
  obtain ⟨U, hU1, hU2⟩ := hs.eq_iInter_nat
  simp_all only [preimage_iInter]
  exact IsGδ.iInter_of_isOpen (fun i => hf.isOpen_preimage (U i) (hU1 i))

@[deprecated (since := "2026-05-19")] alias isGδ_induced := IsGδ.preimage

Depends on / 依赖: eq_iInter_nat, hf.isOpen_preimage, hs.eq_iInter_nat, iInter_of_isOpen, isOpen_preimage, preimage_iInter
-/
theorem IsGδ.preimage [TopologicalSpace Y] {f : X -> Y} {s : Set Y} (hf : Continuous f)
    (hs : IsGδ s) : IsGδ (f ⁻¹' s) := by
  obtain ⟨U, hU1, hU2⟩ := hs.eq_iInter_nat
  simp_all only [preimage_iInter]
  exact IsGδ.iInter_of_isOpen (fun i => hf.isOpen_preimage (U i) (hU1 i))

@[deprecated (since := "2026-05-19")] alias isGδ_induced := IsGδ.preimage

end IsGδ

section residual

variable [TopologicalSpace X]

/--
Definition of `residual` / `residual` 的定义

English:
definition residual
  signature: (X : Type*) [TopologicalSpace X]
  body: Filter.countableGenerate { t | IsOpen t ∧ Dense t }

中文:
定义 residual
  签名: (X : 类型) [拓扑空间 X]
  定义体: Filter.countableGenerate { t | IsOpen t ∧ Dense t }

Depends on / 依赖: Filter, Filter.countableGenerate, IsOpen, countableGenerate
-/
def residual (X : Type*) [TopologicalSpace X] : Filter X :=
  Filter.countableGenerate { t | IsOpen t ∧ Dense t }

/--
Instance `countableInterFilter_residual` / 实例 `countableInterFilter_residual`

English:
instance countableInterFilter_residual
  signature: : CountableInterFilter (residual X)
  body: by
  rw [residual]; infer_instance

中文:
实例 countable整数erFilter_residual
  签名: : 余untable整数erFilter (residual X)
  定义体: by
  rw [residual]; infer_instance

Depends on / 依赖: infer_instance, residual
-/
instance countableInterFilter_residual : CountableInterFilter (residual X) := by
  rw [residual]; infer_instance

/--
theorem `residual_of_dense_open` / 定理 `residual_of_dense_open`

English:
theorem residual_of_dense_open
  given: {s : Set X} (ho : IsOpen s) (hd : Dense s)
  statement: s in residual X
  proof: CountableGenerateSets.basic ⟨ho, hd⟩

中文:
定理 residual_of_dense_open
  条件: {s : 集合 X} (ho : 是开集 s) (hd : 稠密 s)
  结论: s in residual X
  证明: CountableGenerateSets.basic ⟨ho, hd⟩

Depends on / 依赖: CountableGenerateSets, CountableGenerateSets.basic
-/
theorem residual_of_dense_open {s : Set X} (ho : IsOpen s) (hd : Dense s) : s in residual X :=
  CountableGenerateSets.basic ⟨ho, hd⟩

/--
theorem `residual_of_dense_Gδ` / 定理 `residual_of_dense_Gδ`

English:
theorem residual_of_dense_Gδ
  given: {s : Set X} (ho : IsGδ s) (hd : Dense s)
  statement: s in residual X
  proof: by
  rcases ho with ⟨T, To, Tct, rfl⟩
  exact
    (countable_sInter_mem Tct).mpr fun t tT =>
      residual_of_dense_open (To t tT) (hd.mono (sInter_subset_of_mem tT))

中文:
定理 residual_of_dense_Gδ
  条件: {s : 集合 X} (ho : IsGδ s) (hd : 稠密 s)
  结论: s in residual X
  证明: by
  rcases ho with ⟨T, To, Tct, rfl⟩
  exact
    (countable_sInter_mem Tct).mpr fun t tT =>
      residual_of_dense_open (To t tT) (hd.mono (sInter_subset_of_mem tT))

Depends on / 依赖: countable_sInter_mem, hd.mono, residual_of_dense_open, sInter_subset_of_mem
-/
theorem residual_of_dense_Gδ {s : Set X} (ho : IsGδ s) (hd : Dense s) : s in residual X := by
  rcases ho with ⟨T, To, Tct, rfl⟩
  exact
    (countable_sInter_mem Tct).mpr fun t tT =>
      residual_of_dense_open (To t tT) (hd.mono (sInter_subset_of_mem tT))

/--
theorem `mem_residual_iff` / 定理 `mem_residual_iff`

English:
theorem mem_residual_iff
  given: {s : Set X}
  proof: mem_countableGenerate_iff.trans by simp_rw [subset_def, mem_ofPred, forall_and, and_assoc]

中文:
定理 mem_residual_iff
  条件: {s : 集合 X}
  证明: mem_countableGenerate_iff.trans by simp_rw [subset_def, mem_ofPred, forall_and, and_assoc]

Depends on / 依赖: and_assoc, forall_and, mem_countableGenerate_iff, mem_countableGenerate_iff.trans, mem_ofPred, simp_rw, subset_def
-/
theorem mem_residual_iff {s : Set X} :
    s in residual X ↔
      exists S : Set (Set X), (forall t in S, IsOpen t) ∧ (forall t in S, Dense t) ∧ S.Countable ∧ ⋂₀ S subseteq s :=
mem_countableGenerate_iff.trans by simp_rw [subset_def, mem_ofPred, forall_and, and_assoc]

end residual

section IsMeagre
open Function TopologicalSpace Set
variable [TopologicalSpace X]

/--
Definition of `IsNowhereDense` / `IsNowhereDense` 的定义

English:
definition IsNowhereDense
  signature: (s : Set X)
  body: interior (closure s) = ∅

中文:
定义 IsNowhereDense
  签名: (s : 集合 X)
  定义体: interior (closure s) = ∅

Depends on / 依赖: closure, interior
-/
def IsNowhereDense (s : Set X) := interior (closure s) = ∅

/-- The empty set is nowhere dense. -/
@[simp]
/--
lemma `isNowhereDense_empty` / 引理 `isNowhereDense_empty`

English:
lemma isNowhereDense_empty
  statement: IsNowhereDense (∅ : Set X)
  proof: by
  rw [IsNowhereDense]; rw [closure_empty]; rw [interior_empty]

中文:
引理 isNowhereDense_empty
  结论: IsNowhereDense (∅ : 集合 X)
  证明: by
  rw [IsNowhereDense]; rw [closure_empty]; rw [interior_empty]

Depends on / 依赖: IsNowhereDense, closure_empty, interior_empty
-/
lemma isNowhereDense_empty : IsNowhereDense (∅ : Set X) := by
  rw [IsNowhereDense]; rw [closure_empty]; rw [interior_empty]

/-- A subset of a nowhere dense set is nowhere dense. -/
@[gcongr]
/--
lemma `IsNowhereDense.mono` / 引理 `IsNowhereDense.mono`

English:
lemma IsNowhereDense.mono
  given: {s t : Set X} (ht : t subseteq s) (hs : IsNowhereDense s)
  statement: IsNowhereDense t
  proof: Set.eq_empty_of_subset_empty by grw [ht]; rw [hs]

中文:
引理 IsNowhereDense.mono
  条件: {s t : 集合 X} (ht : t subseteq s) (hs : IsNowhereDense s)
  结论: IsNowhereDense t
  证明: Set.eq_empty_of_subset_empty by grw [ht]; rw [hs]

Depends on / 依赖: Set.eq_empty_of_subset_empty, eq_empty_of_subset_empty
-/
lemma IsNowhereDense.mono {s t : Set X} (ht : t subseteq s) (hs : IsNowhereDense s) : IsNowhereDense t :=
Set.eq_empty_of_subset_empty by grw [ht]; rw [hs]

/--
lemma `IsClosed.isNowhereDense_iff` / 引理 `IsClosed.isNowhereDense_iff`

English:
lemma IsClosed.isNowhereDense_iff
  given: {s : Set X} (hs : IsClosed s)
  proof: by
  rw [IsNowhereDense]; rw [IsClosed.closure_eq hs]

中文:
引理 是闭集.isNowhereDense_iff
  条件: {s : 集合 X} (hs : 是闭集 s)
  证明: by
  rw [IsNowhereDense]; rw [IsClosed.closure_eq hs]

Depends on / 依赖: IsClosed, IsClosed.closure_eq, IsNowhereDense, closure_eq
-/
lemma IsClosed.isNowhereDense_iff {s : Set X} (hs : IsClosed s) :
    IsNowhereDense s ↔ interior s = ∅ := by
  rw [IsNowhereDense]; rw [IsClosed.closure_eq hs]

/--
lemma `IsNowhereDense.closure` / 引理 `IsNowhereDense.closure`

English:
lemma IsNowhereDense.closure
  given: {s : Set X} (hs : IsNowhereDense s)
  proof: by
  rwa [IsNowhereDense, closure_closure]

中文:
引理 IsNowhereDense.closure
  条件: {s : 集合 X} (hs : IsNowhereDense s)
  证明: by
  rwa [IsNowhereDense, closure_closure]
-/
protected lemma IsNowhereDense.closure {s : Set X} (hs : IsNowhereDense s) :
    IsNowhereDense (closure s) := by
  rwa [IsNowhereDense, closure_closure]

/--
lemma `IsNowhereDense.subset_of_closed_isNowhereDense` / 引理 `IsNowhereDense.subset_of_closed_isNowhereDense`

English:
lemma IsNowhereDense.subset_of_closed_isNowhereDense
  given: {s : Set X} (hs : IsNowhereDense s)
  proof: ⟨closure s, subset_closure, ⟨hs.closure, isClosed_closure⟩⟩

中文:
引理 IsNowhereDense.subset_of_closed_isNowhereDense
  条件: {s : 集合 X} (hs : IsNowhereDense s)
  证明: ⟨closure s, subset_closure, ⟨hs.closure, isClosed_closure⟩⟩

Depends on / 依赖: closure, hs.closure, isClosed_closure, subset_closure
-/
lemma IsNowhereDense.subset_of_closed_isNowhereDense {s : Set X} (hs : IsNowhereDense s) :
    exists t : Set X, s subseteq t ∧ IsNowhereDense t ∧ IsClosed t :=
  ⟨closure s, subset_closure, ⟨hs.closure, isClosed_closure⟩⟩

/--
lemma `isClosed_isNowhereDense_iff_compl` / 引理 `isClosed_isNowhereDense_iff_compl`

English:
lemma isClosed_isNowhereDense_iff_compl
  given: {s : Set X}
  proof: by
  rw [and_congr_right IsClosed.isNowhereDense_iff]; rw [isOpen_compl_iff]; rw [interior_eq_empty_iff_dense_compl]

中文:
引理 isClosed_isNowhereDense_iff_compl
  条件: {s : 集合 X}
  证明: by
  rw [and_congr_right IsClosed.isNowhereDense_iff]; rw [isOpen_compl_iff]; rw [interior_eq_empty_iff_dense_compl]

Depends on / 依赖: IsClosed, IsClosed.isNowhereDense_iff, and_congr_right, interior_eq_empty_iff_dense_compl, isNowhereDense_iff, isOpen_compl_iff
-/
lemma isClosed_isNowhereDense_iff_compl {s : Set X} :
    IsClosed s ∧ IsNowhereDense s ↔ IsOpen sᶜ ∧ Dense sᶜ := by
  rw [and_congr_right IsClosed.isNowhereDense_iff]; rw [isOpen_compl_iff]; rw [interior_eq_empty_iff_dense_compl]

/--
lemma `isNowhereDense_iff_disjoint` / 引理 `isNowhereDense_iff_disjoint`

English:
lemma isNowhereDense_iff_disjoint
  given: {s : Set X}
  proof: ⟨fun H => H ▸ disjoint_empty _, fun H =>
.eq_bot_of_self⟩ .mono_left interior_subset H.closure_left isOpen_interior

中文:
引理 isNowhereDense_iff_disjoint
  条件: {s : 集合 X}
  证明: ⟨fun H => H ▸ disjoint_empty _, fun H =>
.eq_bot_of_self⟩ .mono_left interior_subset H.closure_left isOpen_interior

Depends on / 依赖: H.closure_left, closure_left, disjoint_empty, eq_bot_of_self, interior_subset, isOpen_interior, mono_left
-/
lemma isNowhereDense_iff_disjoint {s : Set X} :
    IsNowhereDense s ↔ Disjoint s (interior (closure s)) :=
  ⟨fun H => H ▸ disjoint_empty _, fun H =>
.eq_bot_of_self⟩ .mono_left interior_subset H.closure_left isOpen_interior

/--
lemma `isNowhereDense_iff_forall_notMem_nhds` / 引理 `isNowhereDense_iff_forall_notMem_nhds`

English:
lemma isNowhereDense_iff_forall_notMem_nhds
  given: {s : Set X}
  proof: by
  simp [isNowhereDense_iff_disjoint, disjoint_iff_inter_eq_empty, eq_empty_iff_forall_notMem,
    mem_interior_iff_mem_nhds]

中文:
引理 isNowhereDense_iff_对任意_notMem_nhds
  条件: {s : 集合 X}
  证明: by
  simp [isNowhereDense_iff_disjoint, disjoint_iff_inter_eq_empty, eq_empty_iff_forall_notMem,
    mem_interior_iff_mem_nhds]

Depends on / 依赖: disjoint_iff_inter_eq_empty, eq_empty_iff_forall_notMem, isNowhereDense_iff_disjoint, mem_interior_iff_mem_nhds
-/
lemma isNowhereDense_iff_forall_notMem_nhds {s : Set X} :
    IsNowhereDense s ↔ forall x in s, closure s ∉ 𝓝 x := by
  simp [isNowhereDense_iff_disjoint, disjoint_iff_inter_eq_empty, eq_empty_iff_forall_notMem,
    mem_interior_iff_mem_nhds]

/--
lemma `Topology.IsInducing.isNowhereDense_image` / 引理 `Topology.IsInducing.isNowhereDense_image`

English:
lemma Topology.IsInducing.isNowhereDense_image
  statement: [TopologicalSpace Y] {f : X -> Y}
  proof: by
  rw [isNowhereDense_iff_forall_notMem_nhds]; rw [forall_mem_image] at *
  simp_rw [hf.nhds_eq_comap, hf.closure_eq_preimage_closure_image] at h
  exact fun x x_mem hx => h x x_mem (preimage_mem_comap hx)

中文:
引理 拓扑.是Inducing.isNowhereDense_image
  结论: [拓扑空间 Y] {f : X -> Y}
  证明: by
  rw [isNowhereDense_iff_forall_notMem_nhds]; rw [forall_mem_image] at *
  simp_rw [hf.nhds_eq_comap, hf.closure_eq_preimage_closure_image] at h
  exact fun x x_mem hx => h x x_mem (preimage_mem_comap hx)

Depends on / 依赖: closure_eq_preimage_closure_image, forall_mem_image, hf.closure_eq_preimage_closure_image, hf.nhds_eq_comap, isNowhereDense_iff_forall_notMem_nhds, nhds_eq_comap, preimage_mem_comap, simp_rw, x_mem
-/
lemma Topology.IsInducing.isNowhereDense_image [TopologicalSpace Y] {f : X -> Y}
    (hf : Topology.IsInducing f) {s : Set X} (h : IsNowhereDense s) : IsNowhereDense (f '' s) := by
  rw [isNowhereDense_iff_forall_notMem_nhds]; rw [forall_mem_image] at *
  simp_rw [hf.nhds_eq_comap, hf.closure_eq_preimage_closure_image] at h
  exact fun x x_mem hx => h x x_mem (preimage_mem_comap hx)

/--
lemma `IsNowhereDense.image_val` / 引理 `IsNowhereDense.image_val`

English:
lemma IsNowhereDense.image_val
  statement: {Y : Set X} {s : Set Y}
  proof: Topology.IsInducing.subtypeVal.isNowhereDense_image hs

中文:
引理 IsNowhereDense.image_val
  结论: {Y : 集合 X} {s : 集合 Y}
  证明: Topology.IsInducing.subtypeVal.isNowhereDense_image hs

Depends on / 依赖: IsInducing, Topology, Topology.IsInducing.subtypeVal.isNowhereDense_image, isNowhereDense_image, subtypeVal
-/
lemma IsNowhereDense.image_val {Y : Set X} {s : Set Y}
    (hs : IsNowhereDense s) : IsNowhereDense (s : Set X) :=
  Topology.IsInducing.subtypeVal.isNowhereDense_image hs

/--
Definition of `IsMeagre` / `IsMeagre` 的定义

English:
definition IsMeagre
  signature: (s : Set X)
  body: sᶜ in residual X

中文:
定义 IsMeagre
  签名: (s : 集合 X)
  定义体: sᶜ in residual X

Depends on / 依赖: residual
-/
def IsMeagre (s : Set X) := sᶜ in residual X

/--
lemma `IsMeagre.empty` / 引理 `IsMeagre.empty`

English:
lemma IsMeagre.empty
  statement: IsMeagre (∅ : Set X)
  proof: by
  rw [IsMeagre]; rw [compl_empty]
  exact Filter.univ_mem

中文:
引理 IsMeagre.empty
  结论: IsMeagre (∅ : 集合 X)
  证明: by
  rw [IsMeagre]; rw [compl_empty]
  exact Filter.univ_mem

Depends on / 依赖: Filter, Filter.univ_mem, IsMeagre, compl_empty, univ_mem
-/
lemma IsMeagre.empty : IsMeagre (∅ : Set X) := by
  rw [IsMeagre]; rw [compl_empty]
  exact Filter.univ_mem

/-- Subsets of meagre sets are meagre. -/
@[gcongr]
/--
lemma `IsMeagre.mono` / 引理 `IsMeagre.mono`

English:
lemma IsMeagre.mono
  given: {s t : Set X} (hts : t subseteq s) (hs : IsMeagre s)
  statement: IsMeagre t
  proof: Filter.mem_of_superset hs (compl_subset_compl.mpr hts)

中文:
引理 IsMeagre.mono
  条件: {s t : 集合 X} (hts : t subseteq s) (hs : IsMeagre s)
  结论: IsMeagre t
  证明: Filter.mem_of_superset hs (compl_subset_compl.mpr hts)

Depends on / 依赖: Filter, Filter.mem_of_superset, compl_subset_compl, compl_subset_compl.mpr, mem_of_superset
-/
lemma IsMeagre.mono {s t : Set X} (hts : t subseteq s) (hs : IsMeagre s) : IsMeagre t :=
  Filter.mem_of_superset hs (compl_subset_compl.mpr hts)

/--
lemma `IsMeagre.inter` / 引理 `IsMeagre.inter`

English:
lemma IsMeagre.inter
  given: {s t : Set X} (hs : IsMeagre s)
  statement: IsMeagre (s inter t)
  proof: hs.mono inter_subset_left

中文:
引理 IsMeagre.inter
  条件: {s t : 集合 X} (hs : IsMeagre s)
  结论: IsMeagre (s inter t)
  证明: hs.mono inter_subset_left

Depends on / 依赖: hs.mono, inter_subset_left
-/
lemma IsMeagre.inter {s t : Set X} (hs : IsMeagre s) : IsMeagre (s inter t) :=
  hs.mono inter_subset_left

/--
lemma `IsMeagre.union` / 引理 `IsMeagre.union`

English:
lemma IsMeagre.union
  given: {s t : Set X} (hs : IsMeagre s) (ht : IsMeagre t)
  statement: IsMeagre (s union t)
  proof: by
  rw [IsMeagre]; rw [compl_union]
  exact inter_mem hs ht

中文:
引理 IsMeagre.union
  条件: {s t : 集合 X} (hs : IsMeagre s) (ht : IsMeagre t)
  结论: IsMeagre (s union t)
  证明: by
  rw [IsMeagre]; rw [compl_union]
  exact inter_mem hs ht

Depends on / 依赖: IsMeagre, compl_union, inter_mem
-/
lemma IsMeagre.union {s t : Set X} (hs : IsMeagre s) (ht : IsMeagre t) : IsMeagre (s union t) := by
  rw [IsMeagre]; rw [compl_union]
  exact inter_mem hs ht

/--
lemma `isMeagre_iUnion` / 引理 `isMeagre_iUnion`

English:
lemma isMeagre_iUnion
  given: [Countable ι'] {f : ι' -> Set X} (hs : forall i, IsMeagre (f i))
  proof: by
  rw [IsMeagre]; rw [compl_iUnion]
  exact countable_iInter_mem.mpr hs

中文:
引理 isMeagre_iUnion
  条件: [可数 ι'] {f : ι' -> 集合 X} (hs : 对任意 i, IsMeagre (f i))
  证明: by
  rw [IsMeagre]; rw [compl_iUnion]
  exact countable_iInter_mem.mpr hs

Depends on / 依赖: IsMeagre, compl_iUnion, countable_iInter_mem, countable_iInter_mem.mpr
-/
lemma isMeagre_iUnion [Countable ι'] {f : ι' -> Set X} (hs : forall i, IsMeagre (f i)) :
    IsMeagre (⋃ i, f i) := by
  rw [IsMeagre]; rw [compl_iUnion]
  exact countable_iInter_mem.mpr hs

/--
lemma `isMeagre_biUnion` / 引理 `isMeagre_biUnion`

English:
lemma isMeagre_biUnion
  statement: {I : Set ι} (c : I.Countable) {f : ι -> Set X}
  proof: by
  suffices IsMeagre (⋃ i : I, f i) by simpa
  have : Countable I := c
  apply isMeagre_iUnion
  intro ⟨i, hi⟩
  exact h i hi

中文:
引理 isMeagre_biUnion
  结论: {I : 集合 ι} (c : I.可数) {f : ι -> 集合 X}
  证明: by
  suffices IsMeagre (⋃ i : I, f i) by simpa
  have : Countable I := c
  apply isMeagre_iUnion
  intro ⟨i, hi⟩
  exact h i hi

Depends on / 依赖: Countable, IsMeagre, isMeagre_iUnion
-/
lemma isMeagre_biUnion {I : Set ι} (c : I.Countable) {f : ι -> Set X}
    (h : forall i in I, IsMeagre (f i)) : IsMeagre (⋃ i in I, f i) := by
  suffices IsMeagre (⋃ i : I, f i) by simpa
  have : Countable I := c
  apply isMeagre_iUnion
  intro ⟨i, hi⟩
  exact h i hi

/--
lemma `isMeagre_iff_countable_union_isNowhereDense` / 引理 `isMeagre_iff_countable_union_isNowhereDense`

English:
lemma isMeagre_iff_countable_union_isNowhereDense
  given: {s : Set X}
  proof: by
  rw [IsMeagre]; rw [mem_residual_iff]; rw [compl_bijective.surjective.image_surjective.exists]
  simp_rw [← and_assoc, ← forall_and, forall_mem_image, ← isClosed_isNowhereDense_iff_compl,
    sInter_image, ← compl_iUnion₂, compl_subset_compl, ← sUnion_eq_biUnion, and_assoc]
  refine ⟨fun ⟨S, hS,

中文:
引理 isMeagre_iff_countable_union_isNowhereDense
  条件: {s : 集合 X}
  证明: by
  rw [IsMeagre]; rw [mem_residual_iff]; rw [compl_bijective.surjective.image_surjective.exists]
  simp_rw [← and_assoc, ← forall_and, forall_mem_image, ← isClosed_isNowhereDense_iff_compl,
    sInter_image, ← compl_iUnion₂, compl_subset_compl, ← sUnion_eq_biUnion, and_assoc]
  refine ⟨fun ⟨S, hS,

Depends on / 依赖: IsMeagre, and_assoc, closure, compl_bijective, compl_bijective.surjective.image_surjective.exists, compl_compl_image, compl_subset_compl, forall_and, forall_mem_image, hc.image, image_surjective, isClosed_closure, isClosed_isNowhereDense_iff_compl, mem_residual_iff, sInter_image, sUnion_eq_biUnion, simp_rw, surjective
-/
lemma isMeagre_iff_countable_union_isNowhereDense {s : Set X} :
    IsMeagre s ↔ exists S : Set (Set X), (forall t in S, IsNowhereDense t) ∧ S.Countable ∧ s subseteq ⋃₀ S := by
  rw [IsMeagre]; rw [mem_residual_iff]; rw [compl_bijective.surjective.image_surjective.exists]
  simp_rw [← and_assoc, ← forall_and, forall_mem_image, ← isClosed_isNowhereDense_iff_compl,
    sInter_image, ← compl_iUnion₂, compl_subset_compl, ← sUnion_eq_biUnion, and_assoc]
  refine ⟨fun ⟨S, hS, hc, hsub⟩ => ⟨S, fun s hs => (hS hs).2, ?_, hsub⟩, ?_⟩
  · rw [← compl_compl_image S]; exact hc.image _
  · intro ⟨S, hS, hc, hsub⟩
    use closure '' S
    rw [forall_mem_image]
    exact ⟨fun s hs => ⟨isClosed_closure, (hS s hs).closure⟩,
      (hc.image _).image _, hsub.trans (sUnion_mono_subsets fun s => subset_closure)⟩

/--
lemma `nonempty_of_not_isMeagre` / 引理 `nonempty_of_not_isMeagre`

English:
lemma nonempty_of_not_isMeagre
  given: {s : Set X} (hs : ¬IsMeagre s)
  statement: s.Nonempty
  proof: by
  contrapose! hs
  simpa [hs] using IsMeagre.empty

中文:
引理 nonempty_of_not_isMeagre
  条件: {s : 集合 X} (hs : ¬IsMeagre s)
  结论: s.非空
  证明: by
  contrapose! hs
  simpa [hs] using IsMeagre.empty

Depends on / 依赖: IsMeagre, IsMeagre.empty, contrapose
-/
lemma nonempty_of_not_isMeagre {s : Set X} (hs : ¬IsMeagre s) : s.Nonempty := by
  contrapose! hs
  simpa [hs] using IsMeagre.empty

/--
lemma `IsNowhereDense.isMeagre` / 引理 `IsNowhereDense.isMeagre`

English:
lemma IsNowhereDense.isMeagre
  given: {s : Set X} (h : IsNowhereDense s)
  statement: IsMeagre s
  proof: by
  rw [isMeagre_iff_countable_union_isNowhereDense]
  exact ⟨{s}, by simpa, by simp, by simp⟩

中文:
引理 IsNowhereDense.isMeagre
  条件: {s : 集合 X} (h : IsNowhereDense s)
  结论: IsMeagre s
  证明: by
  rw [isMeagre_iff_countable_union_isNowhereDense]
  exact ⟨{s}, by simpa, by simp, by simp⟩

Depends on / 依赖: isMeagre_iff_countable_union_isNowhereDense
-/
lemma IsNowhereDense.isMeagre {s : Set X} (h : IsNowhereDense s) : IsMeagre s := by
  rw [isMeagre_iff_countable_union_isNowhereDense]
  exact ⟨{s}, by simpa, by simp, by simp⟩

/--
lemma `exists_of_not_isMeagre_biUnion` / 引理 `exists_of_not_isMeagre_biUnion`

English:
lemma exists_of_not_isMeagre_biUnion
  statement: {I : Set ι}
  proof: by
  contrapose! h
  exact isMeagre_biUnion c h

中文:
引理 存在_of_not_isMeagre_biUnion
  结论: {I : 集合 ι}
  证明: by
  contrapose! h
  exact isMeagre_biUnion c h

Depends on / 依赖: contrapose, isMeagre_biUnion
-/
lemma exists_of_not_isMeagre_biUnion {I : Set ι}
    (c : I.Countable) {A : ι -> Set X} (h : ¬IsMeagre (⋃ i in I, A i)) :
    exists i in I, ¬IsMeagre (A i) := by
  contrapose! h
  exact isMeagre_biUnion c h

/--
lemma `Topology.IsInducing.isMeagre_image` / 引理 `Topology.IsInducing.isMeagre_image`

English:
lemma Topology.IsInducing.isMeagre_image
  statement: [TopologicalSpace Y] {f : X -> Y}
  proof: by
  rw [isMeagre_iff_countable_union_isNowhereDense] at *
  obtain ⟨T, isNowhereDense, countable, cover⟩ := h
  refine ⟨(Set.image f) '' T, ?isNowhereDense, countable.image _, ?cover⟩
  case isNowhereDense =>
    intro u ⟨t, tT, tu⟩
    rw [← tu]
    apply hf.isNowhereDense_image (isNowhereDense t 

中文:
引理 拓扑.是Inducing.isMeagre_image
  结论: [拓扑空间 Y] {f : X -> Y}
  证明: by
  rw [isMeagre_iff_countable_union_isNowhereDense] at *
  obtain ⟨T, isNowhereDense, countable, cover⟩ := h
  refine ⟨(Set.image f) '' T, ?isNowhereDense, countable.image _, ?cover⟩
  case isNowhereDense =>
    intro u ⟨t, tT, tu⟩
    rw [← tu]
    apply hf.isNowhereDense_image (isNowhereDense t 

Depends on / 依赖: Set.image, Set.image_sUnion, countable, countable.image, hf.isNowhereDense_image, image_sUnion, isMeagre_iff_countable_union_isNowhereDense, isNowhereDense, isNowhereDense_image
-/
lemma Topology.IsInducing.isMeagre_image [TopologicalSpace Y] {f : X -> Y}
    (hf : Topology.IsInducing f) {s : Set X} (h : IsMeagre s) : IsMeagre (f '' s) := by
  rw [isMeagre_iff_countable_union_isNowhereDense] at *
  obtain ⟨T, isNowhereDense, countable, cover⟩ := h
  refine ⟨(Set.image f) '' T, ?isNowhereDense, countable.image _, ?cover⟩
  case isNowhereDense =>
    intro u ⟨t, tT, tu⟩
    rw [← tu]
    apply hf.isNowhereDense_image (isNowhereDense t tT)
  case cover =>
    rw [← Set.image_sUnion]
    grw [cover]

/--
lemma `IsMeagre.image_val` / 引理 `IsMeagre.image_val`

English:
lemma IsMeagre.image_val
  given: {s : Set X} {m : Set s} (h : IsMeagre (m : Set s))
  proof: Topology.IsInducing.subtypeVal.isMeagre_image h

中文:
引理 IsMeagre.image_val
  条件: {s : 集合 X} {m : 集合 s} (h : IsMeagre (m : 集合 s))
  证明: Topology.IsInducing.subtypeVal.isMeagre_image h

Depends on / 依赖: IsInducing, Topology, Topology.IsInducing.subtypeVal.isMeagre_image, isMeagre_image, subtypeVal
-/
lemma IsMeagre.image_val {s : Set X} {m : Set s} (h : IsMeagre (m : Set s)) :
    IsMeagre (m : Set X) := Topology.IsInducing.subtypeVal.isMeagre_image h

end IsMeagre
