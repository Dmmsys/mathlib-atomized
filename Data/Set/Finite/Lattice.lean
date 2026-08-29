/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Kyle Miller
-/
module

public import Mathlib.Data.Set.Finite.Powerset
public import Mathlib.Data.Set.Finite.Range
public import Mathlib.Data.Set.Lattice.Image

import Mathlib.Data.Fintype.Option

/-!
# Finiteness of unions and intersections

## Implementation notes

Each result in this file should come in three forms: a `Fintype` instance, a `Finite` instance
and a `Set.Finite` constructor.

## Tags

finite sets
-/

@[expose] public section

assert_not_exists IsOrderedRing MonoidWithZero

open Set Function

universe u v w x

variable {α : Type u} {β : Type v} {ι : Sort w} {γ : Type x}

namespace Set

/-! ### Fintype instances

Every instance here should have a corresponding `Set.Finite` constructor in the next section.
-/

section FintypeInstances

/--
Instance `fintypeiUnion` / 实例 `fintypeiUnion`

English:
instance fintypeiUnion
  signature: [DecidableEq α] [Fintype (PLift ι)] (f : ι -> Set α) [forall i, Fintype (f i)]
  body: Fintype.ofFinset (Finset.univ.biUnion fun i : PLift ι => (f i.down).toFinset) by simp

中文:
实例 fintypeiUnion
  签名: [DecidableEq α] [Fintype (PLift ι)] (f : ι -> Set α) [对任意 i, Fintype (f i)]
  定义体: Fintype.ofFinset (Finset.univ.biUnion fun i : PLift ι => (f i.down).toFinset) by simp

Depends on / 依赖: Finset, Finset.univ.biUnion, Fintype, Fintype.ofFinset, biUnion, i.down, ofFinset, toFinset
-/
instance fintypeiUnion [DecidableEq α] [Fintype (PLift ι)] (f : ι -> Set α) [forall i, Fintype (f i)] :
    Fintype (⋃ i, f i) :=
Fintype.ofFinset (Finset.univ.biUnion fun i : PLift ι => (f i.down).toFinset) by simp

/--
Instance `fintypesUnion` / 实例 `fintypesUnion`

English:
instance fintypesUnion
  signature: [DecidableEq α] {s : Set (Set α)} [Fintype s]
  body: by
  rw [sUnion_eq_iUnion]
  exact @Set.fintypeiUnion _ _ _ _ _ H

中文:
实例 fintypesUnion
  签名: [DecidableEq α] {s : Set (Set α)} [Fintype s]
  定义体: by
  rw [sUnion_eq_iUnion]
  exact @Set.fintypeiUnion _ _ _ _ _ H

Depends on / 依赖: Set.fintypeiUnion, fintypeiUnion, sUnion_eq_iUnion
-/
instance fintypesUnion [DecidableEq α] {s : Set (Set α)} [Fintype s]
    [H : forall t : s, Fintype (t : Set α)] : Fintype (⋃₀ s) := by
  rw [sUnion_eq_iUnion]
  exact @Set.fintypeiUnion _ _ _ _ _ H

/--
lemma `toFinset_iUnion` / 引理 `toFinset_iUnion`

English:
lemma toFinset_iUnion
  statement: [Fintype β] [DecidableEq α] (f : β -> Set α)
  proof: by
  ext v
  simp only [mem_toFinset, mem_iUnion, Finset.mem_biUnion, Finset.mem_univ, true_and]

中文:
引理 toFinset_iUnion
  结论: [Fintype β] [DecidableEq α] (f : β -> Set α)
  证明: by
  ext v
  simp only [mem_toFinset, mem_iUnion, Finset.mem_biUnion, Finset.mem_univ, true_and]

Depends on / 依赖: Finset, Finset.mem_biUnion, Finset.mem_univ, mem_biUnion, mem_iUnion, mem_toFinset, mem_univ, true_and
-/
lemma toFinset_iUnion [Fintype β] [DecidableEq α] (f : β -> Set α)
    [forall w, Fintype (f w)] :
    Set.toFinset (⋃ (x : β), f x) =
    Finset.biUnion (Finset.univ : Finset β) (fun x => (f x).toFinset) := by
  ext v
  simp only [mem_toFinset, mem_iUnion, Finset.mem_biUnion, Finset.mem_univ, true_and]

/-- A union of sets with `Fintype` structure over a set with `Fintype` structure has a `Fintype`
structure. -/
@[instance_reducible]
/--
Definition of `fintypeBiUnion` / `fintypeBiUnion` 的定义

English:
definition fintypeBiUnion
  signature: [DecidableEq α] {ι : Type*} (s : Set ι) [Fintype s] (t : ι -> Set α)
  body: haveI : forall i : toFinset s, Fintype (t i) := fun i => H i (mem_toFinset.1 i.2)
  Fintype.ofFinset (s.toFinset.attach.biUnion fun x => (t x).toFinset) fun x => by simp

中文:
定义 fintypeBiUnion
  签名: [DecidableEq α] {ι : 类型} (s : Set ι) [Fintype s] (t : ι -> Set α)
  定义体: haveI : forall i : toFinset s, Fintype (t i) := fun i => H i (mem_toFinset.1 i.2)
  Fintype.ofFinset (s.toFinset.attach.biUnion fun x => (t x).toFinset) fun x => by simp

Depends on / 依赖: Fintype, Fintype.ofFinset, attach, biUnion, mem_toFinset, ofFinset, s.toFinset.attach.biUnion, toFinset
-/
def fintypeBiUnion [DecidableEq α] {ι : Type*} (s : Set ι) [Fintype s] (t : ι -> Set α)
    (H : forall i in s, Fintype (t i)) : Fintype (⋃ x in s, t x) :=
  haveI : forall i : toFinset s, Fintype (t i) := fun i => H i (mem_toFinset.1 i.2)
  Fintype.ofFinset (s.toFinset.attach.biUnion fun x => (t x).toFinset) fun x => by simp

/--
Instance `fintypeBiUnion'` / 实例 `fintypeBiUnion'`

English:
instance fintypeBiUnion'
  signature: [DecidableEq α] {ι : Type*} (s : Set ι) [Fintype s] (t : ι -> Set α)
  body: Fintype.ofFinset (s.toFinset.biUnion fun x => (t x).toFinset) by simp

中文:
实例 fintypeBiUnion'
  签名: [DecidableEq α] {ι : 类型} (s : Set ι) [Fintype s] (t : ι -> Set α)
  定义体: Fintype.ofFinset (s.toFinset.biUnion fun x => (t x).toFinset) by simp

Depends on / 依赖: Fintype, Fintype.ofFinset, biUnion, ofFinset, s.toFinset.biUnion, toFinset
-/
instance fintypeBiUnion' [DecidableEq α] {ι : Type*} (s : Set ι) [Fintype s] (t : ι -> Set α)
    [forall i, Fintype (t i)] : Fintype (⋃ x in s, t x) :=
Fintype.ofFinset (s.toFinset.biUnion fun x => (t x).toFinset) by simp

end FintypeInstances

end Set

/-! ### Finite instances

There is seemingly some overlap between the following instances and the `Fintype` instances
in `Data.Set.Finite`. While every `Fintype` instance gives a `Finite` instance, those
instances that depend on `Fintype` or `Decidable` instances need an additional `Finite` instance
to be able to generally apply.

Some set instances do not appear here since they are consequences of others, for example
`Subtype.Finite` for subsets of a finite type.
-/


namespace Finite.Set

/--
Instance `finite_iUnion` / 实例 `finite_iUnion`

English:
instance finite_iUnion
  signature: [Finite ι] (f : ι -> Set α) [forall i, Finite (f i)]
  body: by
  have : Fintype (PLift ι) := Fintype.ofFinite _
  have : forall i, Fintype (f i) := fun i => Fintype.ofFinite _
  classical apply (fintypeiUnion _).finite

中文:
实例 finite_iUnion
  签名: [Finite ι] (f : ι -> Set α) [对任意 i, Finite (f i)]
  定义体: by
  have : Fintype (PLift ι) := Fintype.ofFinite _
  have : forall i, Fintype (f i) := fun i => Fintype.ofFinite _
  classical apply (fintypeiUnion _).finite

Depends on / 依赖: Fintype, Fintype.ofFinite, classical, finite, fintypeiUnion, ofFinite
-/
instance finite_iUnion [Finite ι] (f : ι -> Set α) [forall i, Finite (f i)] : Finite (⋃ i, f i) := by
  have : Fintype (PLift ι) := Fintype.ofFinite _
  have : forall i, Fintype (f i) := fun i => Fintype.ofFinite _
  classical apply (fintypeiUnion _).finite

/--
Instance `finite_sUnion` / 实例 `finite_sUnion`

English:
instance finite_sUnion
  signature: {s : Set (Set α)} [Finite s] [H : forall t : s, Finite (t : Set α)]
  body: by
  rw [sUnion_eq_iUnion]
  exact @Finite.Set.finite_iUnion _ _ _ _ H

中文:
实例 finite_sUnion
  签名: {s : Set (Set α)} [Finite s] [H : 对任意 t : s, Finite (t : Set α)]
  定义体: by
  rw [sUnion_eq_iUnion]
  exact @Finite.Set.finite_iUnion _ _ _ _ H

Depends on / 依赖: Finite, Finite.Set.finite_iUnion, finite_iUnion, sUnion_eq_iUnion
-/
instance finite_sUnion {s : Set (Set α)} [Finite s] [H : forall t : s, Finite (t : Set α)] :
    Finite (⋃₀ s) := by
  rw [sUnion_eq_iUnion]
  exact @Finite.Set.finite_iUnion _ _ _ _ H

/--
theorem `finite_biUnion` / 定理 `finite_biUnion`

English:
theorem finite_biUnion
  statement: {ι : Type*} (s : Set ι) [Finite s] (t : ι -> Set α)
  proof: by
  rw [biUnion_eq_iUnion]
  have : forall i : s, Finite (t i) := fun i => H i i.property
  infer_instance

中文:
定理 finite_biUnion
  结论: {ι : 类型} (s : Set ι) [Finite s] (t : ι -> Set α)
  证明: by
  rw [biUnion_eq_iUnion]
  have : forall i : s, Finite (t i) := fun i => H i i.property
  infer_instance

Depends on / 依赖: Finite, biUnion_eq_iUnion, i.property, infer_instance, property
-/
theorem finite_biUnion {ι : Type*} (s : Set ι) [Finite s] (t : ι -> Set α)
    (H : forall i in s, Finite (t i)) : Finite (⋃ x in s, t x) := by
  rw [biUnion_eq_iUnion]
  have : forall i : s, Finite (t i) := fun i => H i i.property
  infer_instance

/--
Instance `finite_biUnion'` / 实例 `finite_biUnion'`

English:
instance finite_biUnion'
  signature: {ι : Type*} (s : Set ι) [Finite s] (t : ι -> Set α) [forall i, Finite (t i)]
  body: finite_biUnion s t fun _ _ => inferInstance

中文:
实例 finite_biUnion'
  签名: {ι : 类型} (s : Set ι) [Finite s] (t : ι -> Set α) [对任意 i, Finite (t i)]
  定义体: finite_biUnion s t fun _ _ => inferInstance

Depends on / 依赖: finite_biUnion
-/
instance finite_biUnion' {ι : Type*} (s : Set ι) [Finite s] (t : ι -> Set α) [forall i, Finite (t i)] :
    Finite (⋃ x in s, t x) :=
  finite_biUnion s t fun _ _ => inferInstance

/--
Instance `finite_biUnion''` / 实例 `finite_biUnion''`

English:
instance finite_biUnion''
  signature: {ι : Type*} (p : ι -> Prop) [h : Finite { x | p x }] (t : ι -> Set α)
  body: @Finite.Set.finite_biUnion' _ _ (Set.ofPred p) h t _

中文:
实例 finite_biUnion''
  签名: {ι : 类型} (p : ι -> 命题) [h : Finite { x | p x }] (t : ι -> Set α)
  定义体: @Finite.Set.finite_biUnion' _ _ (Set.ofPred p) h t _

Depends on / 依赖: Finite, Finite.Set.finite_biUnion, Set.ofPred, finite_biUnion, ofPred
-/
instance finite_biUnion'' {ι : Type*} (p : ι -> Prop) [h : Finite { x | p x }] (t : ι -> Set α)
    [forall i, Finite (t i)] : Finite (⋃ (x) (_ : p x), t x) :=
  @Finite.Set.finite_biUnion' _ _ (Set.ofPred p) h t _

/--
Instance `finite_iInter` / 实例 `finite_iInter`

English:
instance finite_iInter
  signature: {ι : Sort*} [Nonempty ι] (t : ι -> Set α) [forall i, Finite (t i)]
  body: Finite.Set.subset (t <| Classical.arbitrary ι) (iInter_subset _ _)

中文:
实例 finite_iInter
  签名: {ι : Sort*} [Nonempty ι] (t : ι -> Set α) [对任意 i, Finite (t i)]
  定义体: Finite.Set.subset (t <| Classical.arbitrary ι) (iInter_subset _ _)

Depends on / 依赖: Classical, Classical.arbitrary, Finite, Finite.Set.subset, arbitrary, iInter_subset, subset
-/
instance finite_iInter {ι : Sort*} [Nonempty ι] (t : ι -> Set α) [forall i, Finite (t i)] :
    Finite (⋂ i, t i) :=
  Finite.Set.subset (t <| Classical.arbitrary ι) (iInter_subset _ _)

end Finite.Set

namespace Set

/-! ### Constructors for `Set.Finite`

Every constructor here should have a corresponding `Fintype` instance in the previous section
(or in the `Fintype` module).

The implementation of these constructors ideally should be no more than `Set.toFinite`,
after possibly setting up some `Fintype` and classical `Decidable` instances.
-/


section SetFiniteConstructors

/--
theorem `finite_iUnion` / 定理 `finite_iUnion`

English:
theorem finite_iUnion
  given: [Finite ι] {f : ι -> Set α} (H : forall i, (f i).Finite)
  statement: (⋃ i, f i).Finite
  proof: haveI := fun i => (H i).to_subtype
  toFinite _

中文:
定理 finite_iUnion
  条件: [Finite ι] {f : ι -> Set α} (H : 对任意 i, (f i).Finite)
  结论: (⋃ i, f i).Finite
  证明: haveI := fun i => (H i).to_subtype
  toFinite _

Depends on / 依赖: toFinite, to_subtype
-/
theorem finite_iUnion [Finite ι] {f : ι -> Set α} (H : forall i, (f i).Finite) : (⋃ i, f i).Finite :=
  haveI := fun i => (H i).to_subtype
  toFinite _

/--
theorem `Finite.biUnion'` / 定理 `Finite.biUnion'`

English:
theorem Finite.biUnion'
  statement: {ι} {s : Set ι} (hs : s.Finite) {t : forall i in s, Set α}
  proof: by
  have := hs.to_subtype
  rw [biUnion_eq_iUnion]
  apply finite_iUnion fun i : s => ht i.1 i.2

中文:
定理 Finite.biUnion'
  结论: {ι} {s : Set ι} (hs : s.Finite) {t : 对任意 i in s, Set α}
  证明: by
  have := hs.to_subtype
  rw [biUnion_eq_iUnion]
  apply finite_iUnion fun i : s => ht i.1 i.2

Depends on / 依赖: biUnion_eq_iUnion, finite_iUnion, hs.to_subtype, to_subtype
-/
theorem Finite.biUnion' {ι} {s : Set ι} (hs : s.Finite) {t : forall i in s, Set α}
    (ht : forall i (hi : i in s), (t i hi).Finite) : (⋃ i in s, t i ‹_›).Finite := by
  have := hs.to_subtype
  rw [biUnion_eq_iUnion]
  apply finite_iUnion fun i : s => ht i.1 i.2

/--
theorem `Finite.biUnion` / 定理 `Finite.biUnion`

English:
theorem Finite.biUnion
  statement: {ι} {s : Set ι} (hs : s.Finite) {t : ι -> Set α}
  proof: hs.biUnion' ht

中文:
定理 Finite.biUnion
  结论: {ι} {s : Set ι} (hs : s.Finite) {t : ι -> Set α}
  证明: hs.biUnion' ht

Depends on / 依赖: biUnion, hs.biUnion
-/
theorem Finite.biUnion {ι} {s : Set ι} (hs : s.Finite) {t : ι -> Set α}
    (ht : forall i in s, (t i).Finite) : (⋃ i in s, t i).Finite :=
  hs.biUnion' ht

/--
theorem `Finite.sUnion` / 定理 `Finite.sUnion`

English:
theorem Finite.sUnion
  given: {s : Set (Set α)} (hs : s.Finite) (H : forall t in s, Set.Finite t)
  proof: by
  simpa only [sUnion_eq_biUnion] using hs.biUnion H

中文:
定理 Finite.sUnion
  条件: {s : Set (Set α)} (hs : s.Finite) (H : 对任意 t in s, Set.Finite t)
  证明: by
  simpa only [sUnion_eq_biUnion] using hs.biUnion H

Depends on / 依赖: biUnion, hs.biUnion, sUnion_eq_biUnion
-/
theorem Finite.sUnion {s : Set (Set α)} (hs : s.Finite) (H : forall t in s, Set.Finite t) :
    (⋃₀ s).Finite := by
  simpa only [sUnion_eq_biUnion] using hs.biUnion H

/--
theorem `Finite.sInter` / 定理 `Finite.sInter`

English:
theorem Finite.sInter
  given: {α : Type*} {s : Set (Set α)} {t : Set α} (ht : t in s) (hf : t.Finite)
  proof: hf.subset (sInter_subset_of_mem ht)

中文:
定理 Finite.sInter
  条件: {α : 类型} {s : Set (Set α)} {t : Set α} (ht : t in s) (hf : t.Finite)
  证明: hf.subset (sInter_subset_of_mem ht)

Depends on / 依赖: hf.subset, sInter_subset_of_mem, subset
-/
theorem Finite.sInter {α : Type*} {s : Set (Set α)} {t : Set α} (ht : t in s) (hf : t.Finite) :
    (⋂₀ s).Finite :=
  hf.subset (sInter_subset_of_mem ht)

/--
theorem `Finite.iUnion` / 定理 `Finite.iUnion`

English:
theorem Finite.iUnion
  statement: {ι : Type*} {s : ι -> Set α} {t : Set ι} (ht : t.Finite)
  proof: by
  suffices ⋃ i, s i subseteq ⋃ i in t, s i by exact (ht.biUnion hs).subset this
  refine iUnion_subset fun i x hx => ?_
  by_cases hi : i in t
  · exact mem_biUnion hi hx
  · rw [he i hi, mem_empty_iff_false] at hx
    contradiction

中文:
定理 Finite.iUnion
  结论: {ι : 类型} {s : ι -> Set α} {t : Set ι} (ht : t.Finite)
  证明: by
  suffices ⋃ i, s i subseteq ⋃ i in t, s i by exact (ht.biUnion hs).subset this
  refine iUnion_subset fun i x hx => ?_
  by_cases hi : i in t
  · exact mem_biUnion hi hx
  · rw [he i hi, mem_empty_iff_false] at hx
    contradiction

Depends on / 依赖: biUnion, ht.biUnion, iUnion_subset, mem_biUnion, mem_empty_iff_false, subset, subseteq
-/
theorem Finite.iUnion {ι : Type*} {s : ι -> Set α} {t : Set ι} (ht : t.Finite)
    (hs : forall i in t, (s i).Finite) (he : forall i, i ∉ t -> s i = ∅) : (⋃ i, s i).Finite := by
  suffices ⋃ i, s i subseteq ⋃ i in t, s i by exact (ht.biUnion hs).subset this
  refine iUnion_subset fun i x hx => ?_
  by_cases hi : i in t
  · exact mem_biUnion hi hx
  · rw [he i hi, mem_empty_iff_false] at hx
    contradiction

/--
lemma `finite_iUnion_iff` / 引理 `finite_iUnion_iff`

English:
lemma finite_iUnion_iff
  given: {ι : Type*} {s : ι -> Set α} (hs : Pairwise fun i j => Disjoint (s i) (s j))
  proof: by
refine ⟨fun i => h.subset subset_iUnion _ _, ?_⟩
    let u (i : {i | (s i).Nonempty}) : ⋃ i, s i := ⟨i.2.choose, mem_iUnion.2 ⟨i.1, i.2.choose_spec⟩⟩
    have u_inj : Function.Injective u := by
      rintro ⟨i, hi⟩ ⟨j, hj⟩ hij
      ext
refine hs.eq not_disjoint_iff.2 ⟨u ⟨i, hi⟩, hi.choose_spec, 

中文:
引理 finite_iUnion_iff
  条件: {ι : 类型} {s : ι -> Set α} (hs : Pairwise fun i j => Disjoint (s i) (s j))
  证明: by
refine ⟨fun i => h.subset subset_iUnion _ _, ?_⟩
    let u (i : {i | (s i).Nonempty}) : ⋃ i, s i := ⟨i.2.choose, mem_iUnion.2 ⟨i.1, i.2.choose_spec⟩⟩
    have u_inj : Function.Injective u := by
      rintro ⟨i, hi⟩ ⟨j, hj⟩ hij
      ext
refine hs.eq not_disjoint_iff.2 ⟨u ⟨i, hi⟩, hi.choose_spec, 

Depends on / 依赖: Finite, Function, Function.Injective, Injective, Nonempty, choose_spec, h.subset, hi.choose_spec, hj.choose_spec, hs.eq, iUnion, mem_iUnion, not_disjoint_iff, not_nonempty_iff_eq_empty, of_injective, subset, subset_iUnion, u_inj
-/
lemma finite_iUnion_iff {ι : Type*} {s : ι -> Set α} (hs : Pairwise fun i j => Disjoint (s i) (s j)) :
    (⋃ i, s i).Finite ↔ (forall i, (s i).Finite) ∧ {i | (s i).Nonempty}.Finite where
  mp h := by
refine ⟨fun i => h.subset subset_iUnion _ _, ?_⟩
    let u (i : {i | (s i).Nonempty}) : ⋃ i, s i := ⟨i.2.choose, mem_iUnion.2 ⟨i.1, i.2.choose_spec⟩⟩
    have u_inj : Function.Injective u := by
      rintro ⟨i, hi⟩ ⟨j, hj⟩ hij
      ext
refine hs.eq not_disjoint_iff.2 ⟨u ⟨i, hi⟩, hi.choose_spec, ?_⟩
      rw [hij]
      exact hj.choose_spec
    have : Finite (⋃ i, s i) := h
    exact .of_injective u u_inj
  mpr h := h.2.iUnion (fun _ _ => h.1 _) (by simp [not_nonempty_iff_eq_empty])

/--
lemma `Infinite.iUnion` / 引理 `Infinite.iUnion`

English:
lemma Infinite.iUnion
  given: {ι : Sort*} {s : ι -> Set α} (i : ι) (hi : (s i).Infinite)
  proof: fun h => hi (h.subset (Set.subset_iUnion s i))

中文:
引理 Infinite.iUnion
  条件: {ι : Sort*} {s : ι -> Set α} (i : ι) (hi : (s i).Infinite)
  证明: fun h => hi (h.subset (Set.subset_iUnion s i))
-/
protected lemma Infinite.iUnion {ι : Sort*} {s : ι -> Set α} (i : ι) (hi : (s i).Infinite) :
    (⋃ i, s i).Infinite :=
  fun h => hi (h.subset (Set.subset_iUnion s i))

/--
lemma `Infinite.iUnion₂` / 引理 `Infinite.iUnion₂`

English:
lemma Infinite.iUnion₂
  statement: {ι : Sort*} {κ : ι -> Sort*} {s : forall i, κ i -> Set α} (i : ι) (j : κ i)
  proof: fun hc => hij (hc.subset <| subset_iUnion₂ _ _)

中文:
引理 Infinite.iUnion₂
  结论: {ι : Sort*} {κ : ι -> Sort*} {s : 对任意 i, κ i -> Set α} (i : ι) (j : κ i)
  证明: fun hc => hij (hc.subset <| subset_iUnion₂ _ _)

Depends on / 依赖: hc.subset, subset
-/
lemma Infinite.iUnion₂ {ι : Sort*} {κ : ι -> Sort*} {s : forall i, κ i -> Set α} (i : ι) (j : κ i)
    (hij : (s i j).Infinite) : (⋃ (i) (j), s i j).Infinite :=
  fun hc => hij (hc.subset <| subset_iUnion₂ _ _)

/--
lemma `finite_iUnion_of_subsingleton` / 引理 `finite_iUnion_of_subsingleton`

English:
lemma finite_iUnion_of_subsingleton
  given: {ι : Sort*} [Subsingleton ι] {s : ι -> Set α}
  proof: by
  rw [← iUnion_plift_down]; rw [finite_iUnion_iff _root_.Subsingleton.pairwise]
  simp [PLift.forall, Finite.of_subsingleton]

中文:
引理 finite_iUnion_of_subsingleton
  条件: {ι : Sort*} [Subsingleton ι] {s : ι -> Set α}
  证明: by
  rw [← iUnion_plift_down]; rw [finite_iUnion_iff _root_.Subsingleton.pairwise]
  simp [PLift.forall, Finite.of_subsingleton]
-/
@[simp] lemma finite_iUnion_of_subsingleton {ι : Sort*} [Subsingleton ι] {s : ι -> Set α} :
    (⋃ i, s i).Finite ↔ forall i, (s i).Finite := by
  rw [← iUnion_plift_down]; rw [finite_iUnion_iff _root_.Subsingleton.pairwise]
  simp [PLift.forall, Finite.of_subsingleton]

/--
lemma `PairwiseDisjoint.finite_biUnion_iff` / 引理 `PairwiseDisjoint.finite_biUnion_iff`

English:
lemma PairwiseDisjoint.finite_biUnion_iff
  given: {f : β -> Set α} {s : Set β} (hs : s.PairwiseDisjoint f)
  proof: by
  rw [finite_iUnion_iff (by aesop (add unfold safe [Pairwise]; rw [PairwiseDisjoint]; rw [Set.Pairwise]))]
  simp

中文:
引理 PairwiseDisjoint.finite_biUnion_iff
  条件: {f : β -> Set α} {s : Set β} (hs : s.PairwiseDisjoint f)
  证明: by
  rw [finite_iUnion_iff (by aesop (add unfold safe [Pairwise]; rw [PairwiseDisjoint]; rw [Set.Pairwise]))]
  simp

Depends on / 依赖: Pairwise, PairwiseDisjoint, Set.Pairwise, finite_iUnion_iff
-/
lemma PairwiseDisjoint.finite_biUnion_iff {f : β -> Set α} {s : Set β} (hs : s.PairwiseDisjoint f) :
    (⋃ i in s, f i).Finite ↔ (forall i in s, (f i).Finite) ∧ {i in s | (f i).Nonempty}.Finite := by
  rw [finite_iUnion_iff (by aesop (add unfold safe [Pairwise]; rw [PairwiseDisjoint]; rw [Set.Pairwise]))]
  simp

section preimage
variable {f : α -> β} {s : Set β}

/--
theorem `Finite.preimage'` / 定理 `Finite.preimage'`

English:
theorem Finite.preimage'
  given: (h : s.Finite) (hf : forall b in s, (f ⁻¹' {b}).Finite)
  proof: by
  rw [← Set.biUnion_preimage_singleton]
  exact Set.Finite.biUnion h hf

中文:
定理 Finite.preimage'
  条件: (h : s.Finite) (hf : 对任意 b in s, (f ⁻¹' {b}).Finite)
  证明: by
  rw [← Set.biUnion_preimage_singleton]
  exact Set.Finite.biUnion h hf

Depends on / 依赖: Finite, Set.Finite.biUnion, Set.biUnion_preimage_singleton, biUnion, biUnion_preimage_singleton
-/
theorem Finite.preimage' (h : s.Finite) (hf : forall b in s, (f ⁻¹' {b}).Finite) :
    (f ⁻¹' s).Finite := by
  rw [← Set.biUnion_preimage_singleton]
  exact Set.Finite.biUnion h hf

end preimage

/--
theorem `union_finset_finite_of_range_finite` / 定理 `union_finset_finite_of_range_finite`

English:
theorem union_finset_finite_of_range_finite
  given: (f : α -> Finset β) (h : (range f).Finite)
  proof: by
  rw [← biUnion_range]
  exact h.biUnion fun y _ => y.finite_toSet

中文:
定理 union_finset_finite_of_range_finite
  条件: (f : α -> Finset β) (h : (range f).Finite)
  证明: by
  rw [← biUnion_range]
  exact h.biUnion fun y _ => y.finite_toSet

Depends on / 依赖: biUnion, biUnion_range, finite_toSet, h.biUnion, y.finite_toSet
-/
theorem union_finset_finite_of_range_finite (f : α -> Finset β) (h : (range f).Finite) :
    (⋃ a, (f a : Set β)).Finite := by
  rw [← biUnion_range]
  exact h.biUnion fun y _ => y.finite_toSet

end SetFiniteConstructors

/--
lemma `Finite.of_finite_fibers` / 引理 `Finite.of_finite_fibers`

English:
lemma Finite.of_finite_fibers
  statement: (f : α -> β) {s : Set α} (himage : (f '' s).Finite)
  proof: (himage.biUnion hfibers).subset fun x => by aesop

中文:
引理 Finite.of_finite_fibers
  结论: (f : α -> β) {s : Set α} (himage : (f '' s).Finite)
  证明: (himage.biUnion hfibers).subset fun x => by aesop

Depends on / 依赖: biUnion, hfibers, himage, himage.biUnion, subset
-/
lemma Finite.of_finite_fibers (f : α -> β) {s : Set α} (himage : (f '' s).Finite)
    (hfibers : forall x in f '' s, (s inter f ⁻¹' {x}).Finite) : s.Finite :=
  (himage.biUnion hfibers).subset fun x => by aesop


/--
theorem `finite_subset_iUnion` / 定理 `finite_subset_iUnion`

English:
theorem finite_subset_iUnion
  given: {s : Set α} (hs : s.Finite) {ι} {t : ι -> Set α} (h : s subseteq ⋃ i, t i)
  proof: by
  have := hs.to_subtype
  choose f hf using show forall x : s, exists i, x.1 in t i by simpa [subset_def] using h
  refine ⟨range f, finite_range f, fun x hx => ?_⟩
  rw [biUnion_range]; rw [mem_iUnion]
  exact ⟨⟨x, hx⟩, hf _⟩

中文:
定理 finite_subset_iUnion
  条件: {s : Set α} (hs : s.Finite) {ι} {t : ι -> Set α} (h : s subseteq ⋃ i, t i)
  证明: by
  have := hs.to_subtype
  choose f hf using show forall x : s, exists i, x.1 in t i by simpa [subset_def] using h
  refine ⟨range f, finite_range f, fun x hx => ?_⟩
  rw [biUnion_range]; rw [mem_iUnion]
  exact ⟨⟨x, hx⟩, hf _⟩

Depends on / 依赖: biUnion_range, finite_range, hs.to_subtype, mem_iUnion, subset_def, to_subtype
-/
theorem finite_subset_iUnion {s : Set α} (hs : s.Finite) {ι} {t : ι -> Set α} (h : s subseteq ⋃ i, t i) :
    exists I : Set ι, I.Finite ∧ s subseteq ⋃ i in I, t i := by
  have := hs.to_subtype
  choose f hf using show forall x : s, exists i, x.1 in t i by simpa [subset_def] using h
  refine ⟨range f, finite_range f, fun x hx => ?_⟩
  rw [biUnion_range]; rw [mem_iUnion]
  exact ⟨⟨x, hx⟩, hf _⟩

/--
theorem `eq_finite_iUnion_of_finite_subset_iUnion` / 定理 `eq_finite_iUnion_of_finite_subset_iUnion`

English:
theorem eq_finite_iUnion_of_finite_subset_iUnion
  statement: {ι} {s : ι -> Set α} {t : Set α} (tfin : t.Finite)
  proof: let ⟨I, Ifin, hI⟩ := finite_subset_iUnion tfin h
  ⟨I, Ifin, fun x => s x inter t, fun _ => tfin.subset inter_subset_right, fun _ =>
    inter_subset_left, by
    ext x
    rw [mem_iUnion]
    constructor
    · intro x_in
      rcases mem_iUnion.mp (hI x_in) with ⟨i, _, ⟨hi, rfl⟩, H⟩
      exact ⟨⟨i

中文:
定理 eq_finite_iUnion_of_finite_subset_iUnion
  结论: {ι} {s : ι -> Set α} {t : Set α} (tfin : t.Finite)
  证明: let ⟨I, Ifin, hI⟩ := finite_subset_iUnion tfin h
  ⟨I, Ifin, fun x => s x inter t, fun _ => tfin.subset inter_subset_right, fun _ =>
    inter_subset_left, by
    ext x
    rw [mem_iUnion]
    constructor
    · intro x_in
      rcases mem_iUnion.mp (hI x_in) with ⟨i, _, ⟨hi, rfl⟩, H⟩
      exact ⟨⟨i

Depends on / 依赖: finite_subset_iUnion, inter_subset_left, inter_subset_right, mem_iUnion, mem_iUnion.mp, subset, tfin.subset, x_in
-/
theorem eq_finite_iUnion_of_finite_subset_iUnion {ι} {s : ι -> Set α} {t : Set α} (tfin : t.Finite)
    (h : t subseteq ⋃ i, s i) :
    exists I : Set ι,
      I.Finite ∧
        exists σ : { i | i in I } -> Set α, (forall i, (σ i).Finite) ∧ (forall i, σ i subseteq s i) ∧ t = ⋃ i, σ i :=
  let ⟨I, Ifin, hI⟩ := finite_subset_iUnion tfin h
  ⟨I, Ifin, fun x => s x inter t, fun _ => tfin.subset inter_subset_right, fun _ =>
    inter_subset_left, by
    ext x
    rw [mem_iUnion]
    constructor
    · intro x_in
      rcases mem_iUnion.mp (hI x_in) with ⟨i, _, ⟨hi, rfl⟩, H⟩
      exact ⟨⟨i, hi⟩, ⟨H, x_in⟩⟩
    · rintro ⟨i, -, H⟩
      exact H⟩

/-! ### Infinite sets -/

variable {s t : Set α}

/--
theorem `infinite_iUnion` / 定理 `infinite_iUnion`

English:
theorem infinite_iUnion
  given: {ι : Type*} [Infinite ι] {s : ι -> Set α} (hs : Function.Injective s)
  proof: fun hfin => @not_injective_infinite_finite ι _ _ hfin.finite_subsets.to_subtype
    (fun i => ⟨s i, subset_iUnion _ _⟩) fun _ _ h_eq => hs (Subtype.ext_iff.1 h_eq)

中文:
定理 infinite_iUnion
  条件: {ι : 类型} [Infinite ι] {s : ι -> Set α} (hs : Function.Injective s)
  证明: fun hfin => @not_injective_infinite_finite ι _ _ hfin.finite_subsets.to_subtype
    (fun i => ⟨s i, subset_iUnion _ _⟩) fun _ _ h_eq => hs (Subtype.ext_iff.1 h_eq)

Depends on / 依赖: Subtype, Subtype.ext_iff, ext_iff, finite_subsets, h_eq, hfin.finite_subsets.to_subtype, not_injective_infinite_finite, subset_iUnion, to_subtype
-/
theorem infinite_iUnion {ι : Type*} [Infinite ι] {s : ι -> Set α} (hs : Function.Injective s) :
    (⋃ i, s i).Infinite :=
  fun hfin => @not_injective_infinite_finite ι _ _ hfin.finite_subsets.to_subtype
    (fun i => ⟨s i, subset_iUnion _ _⟩) fun _ _ h_eq => hs (Subtype.ext_iff.1 h_eq)

/--
theorem `Infinite.biUnion` / 定理 `Infinite.biUnion`

English:
theorem Infinite.biUnion
  statement: {ι : Type*} {s : ι -> Set α} {a : Set ι} (ha : a.Infinite)
  proof: by
  rw [biUnion_eq_iUnion]
  have _ := ha.to_subtype
  exact infinite_iUnion fun ⟨i,hi⟩ ⟨j,hj⟩ hij => by simp [hs hi hj hij]

中文:
定理 Infinite.biUnion
  结论: {ι : 类型} {s : ι -> Set α} {a : Set ι} (ha : a.Infinite)
  证明: by
  rw [biUnion_eq_iUnion]
  have _ := ha.to_subtype
  exact infinite_iUnion fun ⟨i,hi⟩ ⟨j,hj⟩ hij => by simp [hs hi hj hij]

Depends on / 依赖: biUnion_eq_iUnion, ha.to_subtype, infinite_iUnion, to_subtype
-/
theorem Infinite.biUnion {ι : Type*} {s : ι -> Set α} {a : Set ι} (ha : a.Infinite)
    (hs : a.InjOn s) : (⋃ i in a, s i).Infinite := by
  rw [biUnion_eq_iUnion]
  have _ := ha.to_subtype
  exact infinite_iUnion fun ⟨i,hi⟩ ⟨j,hj⟩ hij => by simp [hs hi hj hij]

/--
theorem `Infinite.sUnion` / 定理 `Infinite.sUnion`

English:
theorem Infinite.sUnion
  given: {s : Set (Set α)} (hs : s.Infinite)
  statement: (⋃₀ s).Infinite
  proof: by
  rw [sUnion_eq_iUnion]
  have _ := hs.to_subtype
  exact infinite_iUnion Subtype.coe_injective

中文:
定理 Infinite.sUnion
  条件: {s : Set (Set α)} (hs : s.Infinite)
  结论: (⋃₀ s).Infinite
  证明: by
  rw [sUnion_eq_iUnion]
  have _ := hs.to_subtype
  exact infinite_iUnion Subtype.coe_injective

Depends on / 依赖: Subtype, Subtype.coe_injective, coe_injective, hs.to_subtype, infinite_iUnion, sUnion_eq_iUnion, to_subtype
-/
theorem Infinite.sUnion {s : Set (Set α)} (hs : s.Infinite) : (⋃₀ s).Infinite := by
  rw [sUnion_eq_iUnion]
  have _ := hs.to_subtype
  exact infinite_iUnion Subtype.coe_injective

/-! ### Order properties -/

@[to_dual]
/--
lemma `map_finite_biSup` / 引理 `map_finite_biSup`

English:
lemma map_finite_biSup
  statement: {F ι : Type*} [CompleteLattice α] [CompleteLattice β] [FunLike F α β]
  proof: by
  have := map_finset_sup f hs.toFinset g
  simp only [Finset.sup_eq_iSup, hs.mem_toFinset, comp_apply] at this
  exact this

@[to_dual]

中文:
引理 map_finite_biSup
  结论: {F ι : 类型} [CompleteLattice α] [CompleteLattice β] [FunLike F α β]
  证明: by
  have := map_finset_sup f hs.toFinset g
  simp only [Finset.sup_eq_iSup, hs.mem_toFinset, comp_apply] at this
  exact this

@[to_dual]

Depends on / 依赖: Finset, Finset.sup_eq_iSup, comp_apply, hs.mem_toFinset, hs.toFinset, map_finset_sup, mem_toFinset, sup_eq_iSup, toFinset
-/
lemma map_finite_biSup {F ι : Type*} [CompleteLattice α] [CompleteLattice β] [FunLike F α β]
    [SupBotHomClass F α β] {s : Set ι} (hs : s.Finite) (f : F) (g : ι -> α) :
    f (⨆ x in s, g x) = ⨆ x in s, f (g x) := by
  have := map_finset_sup f hs.toFinset g
  simp only [Finset.sup_eq_iSup, hs.mem_toFinset, comp_apply] at this
  exact this

@[to_dual]
/--
lemma `map_finite_iSup` / 引理 `map_finite_iSup`

English:
lemma map_finite_iSup
  statement: {F ι : Type*} [CompleteLattice α] [CompleteLattice β] [FunLike F α β]
  proof: by
  rw [← iSup_univ (f := g)]; rw [← iSup_univ (f := fun i => f (g i))]
  exact map_finite_biSup finite_univ f g

@[to_dual]

中文:
引理 map_finite_iSup
  结论: {F ι : 类型} [CompleteLattice α] [CompleteLattice β] [FunLike F α β]
  证明: by
  rw [← iSup_univ (f := g)]; rw [← iSup_univ (f := fun i => f (g i))]
  exact map_finite_biSup finite_univ f g

@[to_dual]

Depends on / 依赖: finite_univ, iSup_univ, map_finite_biSup
-/
lemma map_finite_iSup {F ι : Type*} [CompleteLattice α] [CompleteLattice β] [FunLike F α β]
    [SupBotHomClass F α β] [Finite ι] (f : F) (g : ι -> α) :
    f (⨆ i, g i) = ⨆ i, f (g i) := by
  rw [← iSup_univ (f := g)]; rw [← iSup_univ (f := fun i => f (g i))]
  exact map_finite_biSup finite_univ f g

@[to_dual]
/--
theorem `Finite.iSup_biInf_of_monotone` / 定理 `Finite.iSup_biInf_of_monotone`

English:
theorem Finite.iSup_biInf_of_monotone
  statement: {ι ι' α : Type*} [Preorder ι'] [Nonempty ι']
  proof: by
  induction s, hs using Set.Finite.induction_on with
  | empty => simp [iSup_const]
  | insert _ _ ihs =>
    rw [forall_mem_insert] at hf
    simp only [iInf_insert, ← ihs hf.2]
    exact iSup_inf_of_monotone hf.1 fun j₁ j₂ hj => iInf₂_mono fun i hi => hf.2 i hi hj

@[to_dual]

中文:
定理 Finite.iSup_biInf_of_monotone
  结论: {ι ι' α : 类型} [Preorder ι'] [Nonempty ι']
  证明: by
  induction s, hs using Set.Finite.induction_on with
  | empty => simp [iSup_const]
  | insert _ _ ihs =>
    rw [forall_mem_insert] at hf
    simp only [iInf_insert, ← ihs hf.2]
    exact iSup_inf_of_monotone hf.1 fun j₁ j₂ hj => iInf₂_mono fun i hi => hf.2 i hi hj

@[to_dual]

Depends on / 依赖: Finite, Set.Finite.induction_on, forall_mem_insert, iInf_insert, iSup_const, iSup_inf_of_monotone, induction_on, insert
-/
theorem Finite.iSup_biInf_of_monotone {ι ι' α : Type*} [Preorder ι'] [Nonempty ι']
    [IsDirectedOrder ι'] [Order.Frame α] {s : Set ι} (hs : s.Finite) {f : ι -> ι' -> α}
    (hf : forall i in s, Monotone (f i)) : ⨆ j, ⨅ i in s, f i j = ⨅ i in s, ⨆ j, f i j := by
  induction s, hs using Set.Finite.induction_on with
  | empty => simp [iSup_const]
  | insert _ _ ihs =>
    rw [forall_mem_insert] at hf
    simp only [iInf_insert, ← ihs hf.2]
    exact iSup_inf_of_monotone hf.1 fun j₁ j₂ hj => iInf₂_mono fun i hi => hf.2 i hi hj

@[to_dual]
/--
theorem `Finite.iSup_biInf_of_antitone` / 定理 `Finite.iSup_biInf_of_antitone`

English:
theorem Finite.iSup_biInf_of_antitone
  statement: {ι ι' α : Type*} [Preorder ι'] [Nonempty ι']
  proof: @Finite.iSup_biInf_of_monotone ι ι'ᵒᵈ α _ _ _ _ _ hs _ fun i hi => (hf i hi).dual_left

@[to_dual]

中文:
定理 Finite.iSup_biInf_of_antitone
  结论: {ι ι' α : 类型} [Preorder ι'] [Nonempty ι']
  证明: @Finite.iSup_biInf_of_monotone ι ι'ᵒᵈ α _ _ _ _ _ hs _ fun i hi => (hf i hi).dual_left

@[to_dual]

Depends on / 依赖: Finite, Finite.iSup_biInf_of_monotone, dual_left, iSup_biInf_of_monotone
-/
theorem Finite.iSup_biInf_of_antitone {ι ι' α : Type*} [Preorder ι'] [Nonempty ι']
    [IsCodirectedOrder ι'] [Order.Frame α] {s : Set ι} (hs : s.Finite) {f : ι -> ι' -> α}
    (hf : forall i in s, Antitone (f i)) : ⨆ j, ⨅ i in s, f i j = ⨅ i in s, ⨆ j, f i j :=
  @Finite.iSup_biInf_of_monotone ι ι'ᵒᵈ α _ _ _ _ _ hs _ fun i hi => (hf i hi).dual_left

@[to_dual]
/--
theorem `_root_.iSup_iInf_of_monotone` / 定理 `_root_.iSup_iInf_of_monotone`

English:
theorem _root_.iSup_iInf_of_monotone
  statement: {ι ι' α : Type*} [Finite ι] [Preorder ι'] [Nonempty ι']
  proof: by
  simpa only [iInf_univ] using finite_univ.iSup_biInf_of_monotone fun i _ => hf i

@[to_dual]

中文:
定理 _root_.iSup_iInf_of_monotone
  结论: {ι ι' α : 类型} [Finite ι] [Preorder ι'] [Nonempty ι']
  证明: by
  simpa only [iInf_univ] using finite_univ.iSup_biInf_of_monotone fun i _ => hf i

@[to_dual]

Depends on / 依赖: finite_univ, finite_univ.iSup_biInf_of_monotone, iInf_univ, iSup_biInf_of_monotone
-/
theorem _root_.iSup_iInf_of_monotone {ι ι' α : Type*} [Finite ι] [Preorder ι'] [Nonempty ι']
    [IsDirectedOrder ι'] [Order.Frame α] {f : ι -> ι' -> α} (hf : forall i, Monotone (f i)) :
    ⨆ j, ⨅ i, f i j = ⨅ i, ⨆ j, f i j := by
  simpa only [iInf_univ] using finite_univ.iSup_biInf_of_monotone fun i _ => hf i

@[to_dual]
/--
theorem `_root_.iSup_iInf_of_antitone` / 定理 `_root_.iSup_iInf_of_antitone`

English:
theorem _root_.iSup_iInf_of_antitone
  statement: {ι ι' α : Type*} [Finite ι] [Preorder ι'] [Nonempty ι']
  proof: @iSup_iInf_of_monotone ι ι'ᵒᵈ α _ _ _ _ _ _ fun i => (hf i).dual_left

@[deprecated (since := "2026-02-03")] protected alias iSup_iInf_of_monotone := iSup_iInf_of_monotone
@[deprecated (since := "2026-02-03")] protected alias iSup_iInf_of_antitone := iSup_iInf_of_antitone
@[deprecated (since := "202

中文:
定理 _root_.iSup_iInf_of_antitone
  结论: {ι ι' α : 类型} [Finite ι] [Preorder ι'] [Nonempty ι']
  证明: @iSup_iInf_of_monotone ι ι'ᵒᵈ α _ _ _ _ _ _ fun i => (hf i).dual_left

@[deprecated (since := "2026-02-03")] protected alias iSup_iInf_of_monotone := iSup_iInf_of_monotone
@[deprecated (since := "2026-02-03")] protected alias iSup_iInf_of_antitone := iSup_iInf_of_antitone
@[deprecated (since := "202

Depends on / 依赖: dual_left, iSup_iInf_of_monotone
-/
theorem _root_.iSup_iInf_of_antitone {ι ι' α : Type*} [Finite ι] [Preorder ι'] [Nonempty ι']
    [IsCodirectedOrder ι'] [Order.Frame α] {f : ι -> ι' -> α} (hf : forall i, Antitone (f i)) :
    ⨆ j, ⨅ i, f i j = ⨅ i, ⨆ j, f i j :=
  @iSup_iInf_of_monotone ι ι'ᵒᵈ α _ _ _ _ _ _ fun i => (hf i).dual_left

@[deprecated (since := "2026-02-03")] protected alias iSup_iInf_of_monotone := iSup_iInf_of_monotone
@[deprecated (since := "2026-02-03")] protected alias iSup_iInf_of_antitone := iSup_iInf_of_antitone
@[deprecated (since := "2026-02-03")] protected alias iInf_iSup_of_monotone := iInf_iSup_of_monotone
@[deprecated (since := "2026-02-03")] protected alias iInf_iSup_of_antitone := iInf_iSup_of_antitone

/--
theorem `iUnion_iInter_of_monotone` / 定理 `iUnion_iInter_of_monotone`

English:
theorem iUnion_iInter_of_monotone
  statement: {ι ι' α : Type*} [Finite ι] [Preorder ι'] [IsDirectedOrder ι']
  proof: iSup_iInf_of_monotone hs

中文:
定理 iUnion_iInter_of_monotone
  结论: {ι ι' α : 类型} [Finite ι] [Preorder ι'] [IsDirectedOrder ι']
  证明: iSup_iInf_of_monotone hs

Depends on / 依赖: iSup_iInf_of_monotone
-/
theorem iUnion_iInter_of_monotone {ι ι' α : Type*} [Finite ι] [Preorder ι'] [IsDirectedOrder ι']
    [Nonempty ι'] {s : ι -> ι' -> Set α} (hs : forall i, Monotone (s i)) :
    ⋃ j : ι', ⋂ i : ι, s i j = ⋂ i : ι, ⋃ j : ι', s i j :=
  iSup_iInf_of_monotone hs

/--
theorem `iUnion_iInter_of_antitone` / 定理 `iUnion_iInter_of_antitone`

English:
theorem iUnion_iInter_of_antitone
  statement: {ι ι' α : Type*} [Finite ι] [Preorder ι']
  proof: iSup_iInf_of_antitone hs

中文:
定理 iUnion_iInter_of_antitone
  结论: {ι ι' α : 类型} [Finite ι] [Preorder ι']
  证明: iSup_iInf_of_antitone hs

Depends on / 依赖: iSup_iInf_of_antitone
-/
theorem iUnion_iInter_of_antitone {ι ι' α : Type*} [Finite ι] [Preorder ι']
    [IsCodirectedOrder ι'] [Nonempty ι'] {s : ι -> ι' -> Set α} (hs : forall i, Antitone (s i)) :
    ⋃ j : ι', ⋂ i : ι, s i j = ⋂ i : ι, ⋃ j : ι', s i j :=
  iSup_iInf_of_antitone hs

/--
theorem `iInter_iUnion_of_monotone` / 定理 `iInter_iUnion_of_monotone`

English:
theorem iInter_iUnion_of_monotone
  statement: {ι ι' α : Type*} [Finite ι] [Preorder ι']
  proof: iInf_iSup_of_monotone hs

中文:
定理 iInter_iUnion_of_monotone
  结论: {ι ι' α : 类型} [Finite ι] [Preorder ι']
  证明: iInf_iSup_of_monotone hs

Depends on / 依赖: iInf_iSup_of_monotone
-/
theorem iInter_iUnion_of_monotone {ι ι' α : Type*} [Finite ι] [Preorder ι']
    [IsCodirectedOrder ι'] [Nonempty ι'] {s : ι -> ι' -> Set α} (hs : forall i, Monotone (s i)) :
    ⋂ j : ι', ⋃ i : ι, s i j = ⋃ i : ι, ⋂ j : ι', s i j :=
  iInf_iSup_of_monotone hs

/--
theorem `iInter_iUnion_of_antitone` / 定理 `iInter_iUnion_of_antitone`

English:
theorem iInter_iUnion_of_antitone
  statement: {ι ι' α : Type*} [Finite ι] [Preorder ι'] [IsDirectedOrder ι']
  proof: iInf_iSup_of_antitone hs

中文:
定理 iInter_iUnion_of_antitone
  结论: {ι ι' α : 类型} [Finite ι] [Preorder ι'] [IsDirectedOrder ι']
  证明: iInf_iSup_of_antitone hs

Depends on / 依赖: iInf_iSup_of_antitone
-/
theorem iInter_iUnion_of_antitone {ι ι' α : Type*} [Finite ι] [Preorder ι'] [IsDirectedOrder ι']
    [Nonempty ι'] {s : ι -> ι' -> Set α} (hs : forall i, Antitone (s i)) :
    ⋂ j : ι', ⋃ i : ι, s i j = ⋃ i : ι, ⋂ j : ι', s i j :=
  iInf_iSup_of_antitone hs

/--
theorem `iUnion_pi_of_monotone` / 定理 `iUnion_pi_of_monotone`

English:
theorem iUnion_pi_of_monotone
  statement: {ι ι' : Type*} [LinearOrder ι'] [Nonempty ι'] {α : ι -> Type*}
  proof: by
  simp only [pi_def, biInter_eq_iInter, preimage_iUnion]
  have := hI.fintype.finite
  refine iUnion_iInter_of_monotone (ι' := ι') (fun (i : I) j₁ j₂ h => ?_)
exact preimage_mono hs i i.2 h

中文:
定理 iUnion_pi_of_monotone
  结论: {ι ι' : 类型} [LinearOrder ι'] [Nonempty ι'] {α : ι -> 类型}
  证明: by
  simp only [pi_def, biInter_eq_iInter, preimage_iUnion]
  have := hI.fintype.finite
  refine iUnion_iInter_of_monotone (ι' := ι') (fun (i : I) j₁ j₂ h => ?_)
exact preimage_mono hs i i.2 h

Depends on / 依赖: biInter_eq_iInter, finite, fintype, hI.fintype.finite, iUnion_iInter_of_monotone, pi_def, preimage_iUnion, preimage_mono
-/
theorem iUnion_pi_of_monotone {ι ι' : Type*} [LinearOrder ι'] [Nonempty ι'] {α : ι -> Type*}
    {I : Set ι} {s : forall i, ι' -> Set (α i)} (hI : I.Finite) (hs : forall i in I, Monotone (s i)) :
    ⋃ j : ι', I.pi (fun i => s i j) = I.pi fun i => ⋃ j, s i j := by
  simp only [pi_def, biInter_eq_iInter, preimage_iUnion]
  have := hI.fintype.finite
  refine iUnion_iInter_of_monotone (ι' := ι') (fun (i : I) j₁ j₂ h => ?_)
exact preimage_mono hs i i.2 h

/--
theorem `iUnion_univ_pi_of_monotone` / 定理 `iUnion_univ_pi_of_monotone`

English:
theorem iUnion_univ_pi_of_monotone
  statement: {ι ι' : Type*} [LinearOrder ι'] [Nonempty ι'] [Finite ι]
  proof: iUnion_pi_of_monotone finite_univ fun i _ => hs i

中文:
定理 iUnion_univ_pi_of_monotone
  结论: {ι ι' : 类型} [LinearOrder ι'] [Nonempty ι'] [Finite ι]
  证明: iUnion_pi_of_monotone finite_univ fun i _ => hs i

Depends on / 依赖: finite_univ, iUnion_pi_of_monotone
-/
theorem iUnion_univ_pi_of_monotone {ι ι' : Type*} [LinearOrder ι'] [Nonempty ι'] [Finite ι]
    {α : ι -> Type*} {s : forall i, ι' -> Set (α i)} (hs : forall i, Monotone (s i)) :
    ⋃ j : ι', pi univ (fun i => s i j) = pi univ fun i => ⋃ j, s i j :=
  iUnion_pi_of_monotone finite_univ fun i _ => hs i

/--
theorem `_root_.iInf_iSup_eq_of_finite` / 定理 `_root_.iInf_iSup_eq_of_finite`

English:
theorem _root_.iInf_iSup_eq_of_finite
  statement: {ι : Sort v} {κ : ι -> Sort w} [Order.Frame α] [Finite ι]
  proof: by
  suffices forall {ι : Type v} {κ : ι -> Type w} [Finite ι] (f : Π a, κ a -> α),
      ⨅ a, ⨆ b, f a b = ⨆ g : (Π a, κ a), ⨅ a, f a (g a) by
    simpa [← Equiv.plift.symm.iInf_comp, ← Equiv.plift.symm.iSup_comp,
        ← (Equiv.plift.piCongr fun a => @Equiv.plift (κ a.down)).symm.iSup_comp] usin

中文:
定理 _root_.iInf_iSup_eq_of_finite
  结论: {ι : Sort v} {κ : ι -> Sort w} [Order.Frame α] [Finite ι]
  证明: by
  suffices forall {ι : Type v} {κ : ι -> Type w} [Finite ι] (f : Π a, κ a -> α),
      ⨅ a, ⨆ b, f a b = ⨆ g : (Π a, κ a), ⨅ a, f a (g a) by
    simpa [← Equiv.plift.symm.iInf_comp, ← Equiv.plift.symm.iSup_comp,
        ← (Equiv.plift.piCongr fun a => @Equiv.plift (κ a.down)).symm.iSup_comp] usin

Depends on / 依赖: Equiv.plift, Equiv.plift.piCongr, Equiv.plift.symm.iInf_comp, Equiv.plift.symm.iSup_comp, Finite, Finite.induction_empty_option, a.down, b.down, e.iInf_comp, e.piCongrLeft, iInf_comp, iSup_comp, induction_empty_option, of_equiv, piCongr, piCongrLeft, symm.iSup_comp
-/
theorem _root_.iInf_iSup_eq_of_finite {ι : Sort v} {κ : ι -> Sort w} [Order.Frame α] [Finite ι]
    {f : Π a, κ a -> α} : ⨅ a, ⨆ b, f a b = ⨆ g : (Π a, κ a), ⨅ a, f a (g a) := by
  suffices forall {ι : Type v} {κ : ι -> Type w} [Finite ι] (f : Π a, κ a -> α),
      ⨅ a, ⨆ b, f a b = ⨆ g : (Π a, κ a), ⨅ a, f a (g a) by
    simpa [← Equiv.plift.symm.iInf_comp, ← Equiv.plift.symm.iSup_comp,
        ← (Equiv.plift.piCongr fun a => @Equiv.plift (κ a.down)).symm.iSup_comp] using!
      this (κ := fun a => PLift (κ a.down)) fun (a : PLift ι) b => f a.down b.down
  intro ι κ _ f
  induction ι using Finite.induction_empty_option with
  | of_equiv e h => simp [← e.iInf_comp, ← e.piCongrLeft κ |>.iSup_comp, h]
  | h_empty => simp [iInf_of_empty, iSup_const]
  | h_option h =>
    simp only [iInf_option, h, ← (Equiv.piOptionEquivProd (β := κ)).symm.iSup_comp,
      Equiv.piOptionEquivProd_symm_apply, iSup_prod, ← inf_iSup_eq, ← iSup_inf_eq]

/--
theorem `_root_.iSup_iInf_eq_of_finite` / 定理 `_root_.iSup_iInf_eq_of_finite`

English:
theorem _root_.iSup_iInf_eq_of_finite
  statement: {ι : Sort v} {κ : ι -> Sort w} [Order.Coframe α] [Finite ι]
  proof: iInf_iSup_eq_of_finite (α := αᵒᵈ)

中文:
定理 _root_.iSup_iInf_eq_of_finite
  结论: {ι : Sort v} {κ : ι -> Sort w} [Order.Coframe α] [Finite ι]
  证明: iInf_iSup_eq_of_finite (α := αᵒᵈ)

Depends on / 依赖: iInf_iSup_eq_of_finite
-/
theorem _root_.iSup_iInf_eq_of_finite {ι : Sort v} {κ : ι -> Sort w} [Order.Coframe α] [Finite ι]
    {f : forall a, κ a -> α} : ⨆ a, ⨅ b, f a b = ⨅ g : forall a, κ a, ⨆ a, f a (g a) :=
  iInf_iSup_eq_of_finite (α := αᵒᵈ)

/--
theorem `Finite.biInf_iSup_eq` / 定理 `Finite.biInf_iSup_eq`

English:
theorem Finite.biInf_iSup_eq
  statement: {ι : Type v} {κ : ι -> Sort w} [Nonempty (Π a, κ a)] [Order.Frame α]
  proof: by
  classical
  suffices h : forall {κ : ι -> Type w} [Nonempty (Π a, κ a)] (f : Π a, κ a -> α),
      ⨅ a in s, ⨆ b, f a b = ⨆ g : (Π a, κ a), ⨅ a in s, f a (g a) by
    have : Nonempty (Π a, PLift (κ a)) := (Equiv.piCongrRight fun _ => Equiv.plift).nonempty
    simpa [← Equiv.plift.symm.iSup_comp

中文:
定理 Finite.biInf_iSup_eq
  结论: {ι : 类型v} {κ : ι -> Sort w} [Nonempty (Π a, κ a)] [Order.Frame α]
  证明: by
  classical
  suffices h : forall {κ : ι -> Type w} [Nonempty (Π a, κ a)] (f : Π a, κ a -> α),
      ⨅ a in s, ⨆ b, f a b = ⨆ g : (Π a, κ a), ⨅ a in s, f a (g a) by
    have : Nonempty (Π a, PLift (κ a)) := (Equiv.piCongrRight fun _ => Equiv.plift).nonempty
    simpa [← Equiv.plift.symm.iSup_comp

Depends on / 依赖: Equiv.piCongrRight, Equiv.plift, Equiv.plift.symm.iSup_comp, Nonempty, b.down, classical, hs.to_subtype, iSup_comp, nonempty, piCongrRight, symm.iSup_comp, to_subtype
-/
theorem Finite.biInf_iSup_eq {ι : Type v} {κ : ι -> Sort w} [Nonempty (Π a, κ a)] [Order.Frame α]
    {s : Set ι} (hs : s.Finite) {f : Π a, κ a -> α} :
    ⨅ a in s, ⨆ b, f a b = ⨆ g : (Π a, κ a), ⨅ a in s, f a (g a) := by
  classical
  suffices h : forall {κ : ι -> Type w} [Nonempty (Π a, κ a)] (f : Π a, κ a -> α),
      ⨅ a in s, ⨆ b, f a b = ⨆ g : (Π a, κ a), ⨅ a in s, f a (g a) by
    have : Nonempty (Π a, PLift (κ a)) := (Equiv.piCongrRight fun _ => Equiv.plift).nonempty
    simpa [← Equiv.plift.symm.iSup_comp, ← (Equiv.piCongrRight fun _ => Equiv.plift).symm.iSup_comp]
      using h (κ := fun a => PLift (κ a)) fun a b => f a b.down
  intro κ _ f
  have := hs.to_subtype
  have : Nonempty (Π a : { a // a ∉ s }, κ ↑a) := ‹Nonempty (Π a, κ a)›.map fun f a => f a
  simp [← iInf_subtype'', iInf_iSup_eq_of_finite (ι := s),
.symm.iSup_comp, iSup_prod, iSup_const] ← Equiv.piEquivPiSubtypeProd (· in s) _

/--
theorem `Finite.biSup_iInf_eq` / 定理 `Finite.biSup_iInf_eq`

English:
theorem Finite.biSup_iInf_eq
  statement: {ι : Type v} {κ : ι -> Sort w} [Nonempty (forall a, κ a)] [Order.Coframe α]
  proof: hs.biInf_iSup_eq (α := αᵒᵈ)

中文:
定理 Finite.biSup_iInf_eq
  结论: {ι : 类型v} {κ : ι -> Sort w} [Nonempty (对任意 a, κ a)] [Order.Coframe α]
  证明: hs.biInf_iSup_eq (α := αᵒᵈ)

Depends on / 依赖: biInf_iSup_eq, hs.biInf_iSup_eq
-/
theorem Finite.biSup_iInf_eq {ι : Type v} {κ : ι -> Sort w} [Nonempty (forall a, κ a)] [Order.Coframe α]
    {s : Set ι} (hs : s.Finite) {f : forall a, κ a -> α} :
    ⨆ a in s, ⨅ b, f a b = ⨅ g : forall a, κ a, ⨆ a in s, f a (g a) :=
  hs.biInf_iSup_eq (α := αᵒᵈ)

section

variable [Preorder α] [IsDirectedOrder α] [Nonempty α] {s : Set α}

/-- A finite set is bounded above. -/
@[to_dual /-- A finite set is bounded below. -/]
/--
theorem `Finite.bddAbove` / 定理 `Finite.bddAbove`

English:
theorem Finite.bddAbove
  given: (hs : s.Finite)
  statement: BddAbove s
  proof: Finite.induction_on _ hs bddAbove_empty fun _ _ h => h.insert _

中文:
定理 Finite.bddAbove
  条件: (hs : s.Finite)
  结论: BddAbove s
  证明: Finite.induction_on _ hs bddAbove_empty fun _ _ h => h.insert _
-/
protected theorem Finite.bddAbove (hs : s.Finite) : BddAbove s :=
  Finite.induction_on _ hs bddAbove_empty fun _ _ h => h.insert _

/-- A finite union of sets which are all bounded above is still bounded above. -/
@[to_dual /-- A finite union of sets which are all bounded below is still bounded below. -/]
/--
theorem `Finite.bddAbove_biUnion` / 定理 `Finite.bddAbove_biUnion`

English:
theorem Finite.bddAbove_biUnion
  given: {I : Set β} {S : β -> Set α} (H : I.Finite)
  proof: by
  induction I, H using Set.Finite.induction_on with
  | empty => simp only [biUnion_empty, bddAbove_empty, forall_mem_empty]
  | insert _ _ hs => simp only [biUnion_insert, forall_mem_insert, bddAbove_union, hs]

@[to_dual]

中文:
定理 Finite.bddAbove_biUnion
  条件: {I : Set β} {S : β -> Set α} (H : I.Finite)
  证明: by
  induction I, H using Set.Finite.induction_on with
  | empty => simp only [biUnion_empty, bddAbove_empty, forall_mem_empty]
  | insert _ _ hs => simp only [biUnion_insert, forall_mem_insert, bddAbove_union, hs]

@[to_dual]

Depends on / 依赖: Finite, Set.Finite.induction_on, bddAbove_empty, bddAbove_union, biUnion_empty, biUnion_insert, forall_mem_empty, forall_mem_insert, induction_on, insert
-/
theorem Finite.bddAbove_biUnion {I : Set β} {S : β -> Set α} (H : I.Finite) :
    BddAbove (⋃ i in I, S i) ↔ forall i in I, BddAbove (S i) := by
  induction I, H using Set.Finite.induction_on with
  | empty => simp only [biUnion_empty, bddAbove_empty, forall_mem_empty]
  | insert _ _ hs => simp only [biUnion_insert, forall_mem_insert, bddAbove_union, hs]

@[to_dual]
/--
theorem `infinite_of_not_bddAbove` / 定理 `infinite_of_not_bddAbove`

English:
theorem infinite_of_not_bddAbove
  statement: ¬BddAbove s -> s.Infinite
  proof: mt Finite.bddAbove

中文:
定理 infinite_of_not_bddAbove
  结论: ¬BddAbove s -> s.Infinite
  证明: mt Finite.bddAbove

Depends on / 依赖: Finite, Finite.bddAbove, bddAbove
-/
theorem infinite_of_not_bddAbove : ¬BddAbove s -> s.Infinite :=
  mt Finite.bddAbove

end

end Set

/-- A finset is bounded above. -/
@[to_dual /-- A finset is bounded below. -/]
/--
theorem `Finset.bddAbove` / 定理 `Finset.bddAbove`

English:
theorem Finset.bddAbove
  given: [SemilatticeSup α] [Nonempty α] (s : Finset α)
  proof: s.finite_toSet.bddAbove

中文:
定理 Finset.bddAbove
  条件: [SemilatticeSup α] [Nonempty α] (s : Finset α)
  证明: s.finite_toSet.bddAbove
-/
protected theorem Finset.bddAbove [SemilatticeSup α] [Nonempty α] (s : Finset α) :
    BddAbove (↑s : Set α) :=
  s.finite_toSet.bddAbove

section LinearOrder
variable [LinearOrder α] {s : Set α}

/--
lemma `Set.finite_sdiff_iUnion_Ioo` / 引理 `Set.finite_sdiff_iUnion_Ioo`

English:
lemma Set.finite_sdiff_iUnion_Ioo
  given: (s : Set α)
  statement: (s \ ⋃ (x in s) (y in s), Ioo x y).Finite
  proof: Set.finite_of_forall_not_lt_lt fun _x hx _y hy _z hz hxy hyz => hy.2 mem_iUnion₂_of_mem hx.1
    mem_iUnion₂_of_mem hz.1 ⟨hxy, hyz⟩

@[deprecated (since := "2026-06-03")]
alias Set.finite_diff_iUnion_Ioo := Set.finite_sdiff_iUnion_Ioo

中文:
引理 Set.finite_sdiff_iUnion_Ioo
  条件: (s : Set α)
  结论: (s \ ⋃ (x in s) (y in s), Ioo x y).Finite
  证明: Set.finite_of_forall_not_lt_lt fun _x hx _y hy _z hz hxy hyz => hy.2 mem_iUnion₂_of_mem hx.1
    mem_iUnion₂_of_mem hz.1 ⟨hxy, hyz⟩

@[deprecated (since := "2026-06-03")]
alias Set.finite_diff_iUnion_Ioo := Set.finite_sdiff_iUnion_Ioo

Depends on / 依赖: Set.finite_of_forall_not_lt_lt, finite_of_forall_not_lt_lt
-/
lemma Set.finite_sdiff_iUnion_Ioo (s : Set α) : (s \ ⋃ (x in s) (y in s), Ioo x y).Finite :=
Set.finite_of_forall_not_lt_lt fun _x hx _y hy _z hz hxy hyz => hy.2 mem_iUnion₂_of_mem hx.1
    mem_iUnion₂_of_mem hz.1 ⟨hxy, hyz⟩

@[deprecated (since := "2026-06-03")]
alias Set.finite_diff_iUnion_Ioo := Set.finite_sdiff_iUnion_Ioo

/--
lemma `Set.finite_sdiff_iUnion_Ioo'` / 引理 `Set.finite_sdiff_iUnion_Ioo'`

English:
lemma Set.finite_sdiff_iUnion_Ioo'
  given: (s : Set α)
  statement: (s \ ⋃ x : s × s, Ioo x.1 x.2).Finite
  proof: by
  simpa only [iUnion, iSup_prod, iSup_subtype] using s.finite_sdiff_iUnion_Ioo

@[deprecated (since := "2026-06-03")]
alias Set.finite_diff_iUnion_Ioo' := Set.finite_sdiff_iUnion_Ioo'

中文:
引理 Set.finite_sdiff_iUnion_Ioo'
  条件: (s : Set α)
  结论: (s \ ⋃ x : s × s, Ioo x.1 x.2).Finite
  证明: by
  simpa only [iUnion, iSup_prod, iSup_subtype] using s.finite_sdiff_iUnion_Ioo

@[deprecated (since := "2026-06-03")]
alias Set.finite_diff_iUnion_Ioo' := Set.finite_sdiff_iUnion_Ioo'

Depends on / 依赖: finite_sdiff_iUnion_Ioo, iSup_prod, iSup_subtype, iUnion, s.finite_sdiff_iUnion_Ioo
-/
lemma Set.finite_sdiff_iUnion_Ioo' (s : Set α) : (s \ ⋃ x : s × s, Ioo x.1 x.2).Finite := by
  simpa only [iUnion, iSup_prod, iSup_subtype] using s.finite_sdiff_iUnion_Ioo

@[deprecated (since := "2026-06-03")]
alias Set.finite_diff_iUnion_Ioo' := Set.finite_sdiff_iUnion_Ioo'

/--
lemma `Directed.exists_mem_subset_of_finset_subset_biUnion` / 引理 `Directed.exists_mem_subset_of_finset_subset_biUnion`

English:
lemma Directed.exists_mem_subset_of_finset_subset_biUnion
  statement: {α ι : Type*} [Nonempty ι]
  proof: by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons b t hbt iht =>
    simp only [Finset.coe_cons, Set.insert_subset_iff, Set.mem_iUnion] at hs ⊢
    rcases hs.imp_right iht with ⟨⟨i, hi⟩, j, hj⟩
    rcases h i j with ⟨k, hik, hjk⟩
    exact ⟨k, hik hi, hj.trans hjk⟩

中文:
引理 Directed.exists_mem_subset_of_finset_subset_biUnion
  结论: {α ι : 类型} [Nonempty ι]
  证明: by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons b t hbt iht =>
    simp only [Finset.coe_cons, Set.insert_subset_iff, Set.mem_iUnion] at hs ⊢
    rcases hs.imp_right iht with ⟨⟨i, hi⟩, j, hj⟩
    rcases h i j with ⟨k, hik, hjk⟩
    exact ⟨k, hik hi, hj.trans hjk⟩

Depends on / 依赖: Finset, Finset.coe_cons, Finset.cons_induction, Set.insert_subset_iff, Set.mem_iUnion, coe_cons, cons_induction, hj.trans, hs.imp_right, imp_right, insert_subset_iff, mem_iUnion
-/
lemma Directed.exists_mem_subset_of_finset_subset_biUnion {α ι : Type*} [Nonempty ι]
    {f : ι -> Set α} (h : Directed (· subseteq ·) f) {s : Finset α} (hs : (s : Set α) subseteq ⋃ i, f i) :
    exists i, (s : Set α) subseteq f i := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons b t hbt iht =>
    simp only [Finset.coe_cons, Set.insert_subset_iff, Set.mem_iUnion] at hs ⊢
    rcases hs.imp_right iht with ⟨⟨i, hi⟩, j, hj⟩
    rcases h i j with ⟨k, hik, hjk⟩
    exact ⟨k, hik hi, hj.trans hjk⟩

/--
theorem `DirectedOn.exists_mem_subset_of_finset_subset_biUnion` / 定理 `DirectedOn.exists_mem_subset_of_finset_subset_biUnion`

English:
theorem DirectedOn.exists_mem_subset_of_finset_subset_biUnion
  statement: {α ι : Type*} {f : ι -> Set α}
  proof: by
  rw [Set.biUnion_eq_iUnion] at hs
  have := hn.coe_sort
  simpa using (directed_comp.2 hc.directed_val).exists_mem_subset_of_finset_subset_biUnion hs

中文:
定理 DirectedOn.exists_mem_subset_of_finset_subset_biUnion
  结论: {α ι : 类型} {f : ι -> Set α}
  证明: by
  rw [Set.biUnion_eq_iUnion] at hs
  have := hn.coe_sort
  simpa using (directed_comp.2 hc.directed_val).exists_mem_subset_of_finset_subset_biUnion hs

Depends on / 依赖: Set.biUnion_eq_iUnion, biUnion_eq_iUnion, coe_sort, directed_comp, directed_val, exists_mem_subset_of_finset_subset_biUnion, hc.directed_val, hn.coe_sort
-/
theorem DirectedOn.exists_mem_subset_of_finset_subset_biUnion {α ι : Type*} {f : ι -> Set α}
    {c : Set ι} (hn : c.Nonempty) (hc : DirectedOn (fun i j => f i subseteq f j) c) {s : Finset α}
    (hs : (s : Set α) subseteq ⋃ i in c, f i) : exists i in c, (s : Set α) subseteq f i := by
  rw [Set.biUnion_eq_iUnion] at hs
  have := hn.coe_sort
  simpa using (directed_comp.2 hc.directed_val).exists_mem_subset_of_finset_subset_biUnion hs

/--
theorem `DirectedOn.exists_mem_subset_of_finite_of_subset_sUnion` / 定理 `DirectedOn.exists_mem_subset_of_finite_of_subset_sUnion`

English:
theorem DirectedOn.exists_mem_subset_of_finite_of_subset_sUnion
  statement: {α : Type*} {c : Set (Set α)}
  proof: by
  rw [← hs.coe_toFinset]; rw [sUnion_eq_biUnion] at hsc
  have := DirectedOn.exists_mem_subset_of_finset_subset_biUnion hn hc hsc
  exact hs.coe_toFinset ▸ this

中文:
定理 DirectedOn.exists_mem_subset_of_finite_of_subset_sUnion
  结论: {α : 类型} {c : Set (Set α)}
  证明: by
  rw [← hs.coe_toFinset]; rw [sUnion_eq_biUnion] at hsc
  have := DirectedOn.exists_mem_subset_of_finset_subset_biUnion hn hc hsc
  exact hs.coe_toFinset ▸ this

Depends on / 依赖: DirectedOn, DirectedOn.exists_mem_subset_of_finset_subset_biUnion, coe_toFinset, exists_mem_subset_of_finset_subset_biUnion, hs.coe_toFinset, sUnion_eq_biUnion
-/
theorem DirectedOn.exists_mem_subset_of_finite_of_subset_sUnion {α : Type*} {c : Set (Set α)}
    (hn : c.Nonempty) (hc : DirectedOn (· subseteq ·) c) {s : Set α} (hs : s.Finite)
    (hsc : s subseteq sUnion c) : exists t in c, s subseteq t := by
  rw [← hs.coe_toFinset]; rw [sUnion_eq_biUnion] at hsc
  have := DirectedOn.exists_mem_subset_of_finset_subset_biUnion hn hc hsc
  exact hs.coe_toFinset ▸ this

end LinearOrder
