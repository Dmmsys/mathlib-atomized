/-
Copyright (c) 2022 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Data.Finset.Pairwise

/-!
# Sums of collections of Finsupp, and their support

This file provides results about the `Finsupp.support` of sums of collections of `Finsupp`,
including sums of `List`, `Multiset`, and `Finset`.

The support of the sum is a subset of the union of the supports:
* `List.support_sum_subset`
* `Multiset.support_sum_subset`
* `Finset.support_sum_subset`

The support of the sum of pairwise disjoint finsupps is equal to the union of the supports
* `List.support_sum_eq`
* `Multiset.support_sum_eq`
* `Finset.support_sum_eq`

Member in the support of the indexed union over a collection iff
it is a member of the support of a member of the collection:
* `List.mem_foldr_sup_support_iff`
* `Multiset.mem_sup_map_support_iff`
* `Finset.mem_sup_support_iff`

-/

public section


variable {ι M : Type*} [DecidableEq ι]

/--
theorem `List.support_sum_subset` / 定理 `List.support_sum_subset`

English:
theorem List.support_sum_subset
  given: [AddZeroClass M] (l : List (ι ->₀ M))
  proof: by
  induction l with
  | nil => simp
  | cons hd tl IH =>
    simp only [List.sum_cons]
    exact Finsupp.support_add.trans (Finset.union_subset_union Finset.Subset.rfl IH)

中文:
定理 列表.support_sum_subset
  条件: [加法零类 M] (l : 列表 (ι ->₀ M))
  证明: by
  induction l with
  | nil => simp
  | cons hd tl IH =>
    simp only [List.sum_cons]
    exact Finsupp.support_add.trans (Finset.union_subset_union Finset.Subset.rfl IH)

Depends on / 依赖: Finset, Finset.Subset.rfl, Finset.union_subset_union, Finsupp, Finsupp.support_add.trans, List.sum_cons, Subset, sum_cons, support_add, union_subset_union
-/
theorem List.support_sum_subset [AddZeroClass M] (l : List (ι ->₀ M)) :
    l.sum.support subseteq l.foldr (Finsupp.support · ⊔ ·) ∅ := by
  induction l with
  | nil => simp
  | cons hd tl IH =>
    simp only [List.sum_cons]
    exact Finsupp.support_add.trans (Finset.union_subset_union Finset.Subset.rfl IH)

/--
theorem `Multiset.support_sum_subset` / 定理 `Multiset.support_sum_subset`

English:
theorem Multiset.support_sum_subset
  given: [AddCommMonoid M] (s : Multiset (ι ->₀ M))
  proof: by
  induction s using Quot.inductionOn
  simpa only [Multiset.quot_mk_to_coe'', Multiset.sum_coe, Multiset.map_coe, Multiset.sup_coe,
    List.foldr_map] using! List.support_sum_subset _

中文:
定理 Multiset.support_sum_subset
  条件: [加法交换幺半群 M] (s : Multiset (ι ->₀ M))
  证明: by
  induction s using Quot.inductionOn
  simpa only [Multiset.quot_mk_to_coe'', Multiset.sum_coe, Multiset.map_coe, Multiset.sup_coe,
    List.foldr_map] using! List.support_sum_subset _

Depends on / 依赖: List.foldr_map, List.support_sum_subset, Multiset, Multiset.map_coe, Multiset.quot_mk_to_coe, Multiset.sum_coe, Multiset.sup_coe, Quot.inductionOn, foldr_map, inductionOn, map_coe, quot_mk_to_coe, sum_coe, sup_coe, support_sum_subset
-/
theorem Multiset.support_sum_subset [AddCommMonoid M] (s : Multiset (ι ->₀ M)) :
    s.sum.support subseteq (s.map Finsupp.support).sup := by
  induction s using Quot.inductionOn
  simpa only [Multiset.quot_mk_to_coe'', Multiset.sum_coe, Multiset.map_coe, Multiset.sup_coe,
    List.foldr_map] using! List.support_sum_subset _

/--
theorem `Finset.support_sum_subset` / 定理 `Finset.support_sum_subset`

English:
theorem Finset.support_sum_subset
  given: [AddCommMonoid M] (s : Finset (ι ->₀ M))
  proof: by
  convert! Multiset.support_sum_subset s.1; simp

中文:
定理 有限集.support_sum_subset
  条件: [加法交换幺半群 M] (s : 有限集 (ι ->₀ M))
  证明: by
  convert! Multiset.support_sum_subset s.1; simp

Depends on / 依赖: Multiset, Multiset.support_sum_subset, convert, support_sum_subset
-/
theorem Finset.support_sum_subset [AddCommMonoid M] (s : Finset (ι ->₀ M)) :
    (s.sum id).support subseteq Finset.sup s Finsupp.support := by
  convert! Multiset.support_sum_subset s.1; simp

/--
theorem `List.mem_foldr_sup_support_iff` / 定理 `List.mem_foldr_sup_support_iff`

English:
theorem List.mem_foldr_sup_support_iff
  given: [Zero M] {l : List (ι ->₀ M)} {x : ι}
  proof: by
  simp only [Finset.sup_eq_union, Finsupp.mem_support_iff]
  induction l with
  | nil => simp
  | cons hd tl IH =>
    simp only [foldr, Finset.mem_union, Finsupp.mem_support_iff, ne_eq, IH,
      mem_cons, exists_eq_or_imp]

中文:
定理 列表.mem_foldr_sup_support_iff
  条件: [零 M] {l : 列表 (ι ->₀ M)} {x : ι}
  证明: by
  simp only [Finset.sup_eq_union, Finsupp.mem_support_iff]
  induction l with
  | nil => simp
  | cons hd tl IH =>
    simp only [foldr, Finset.mem_union, Finsupp.mem_support_iff, ne_eq, IH,
      mem_cons, exists_eq_or_imp]

Depends on / 依赖: Finset, Finset.mem_union, Finset.sup_eq_union, Finsupp, Finsupp.mem_support_iff, exists_eq_or_imp, mem_cons, mem_support_iff, mem_union, ne_eq, sup_eq_union
-/
theorem List.mem_foldr_sup_support_iff [Zero M] {l : List (ι ->₀ M)} {x : ι} :
    x in l.foldr (Finsupp.support · ⊔ ·) ∅ ↔ exists f in l, x in f.support := by
  simp only [Finset.sup_eq_union, Finsupp.mem_support_iff]
  induction l with
  | nil => simp
  | cons hd tl IH =>
    simp only [foldr, Finset.mem_union, Finsupp.mem_support_iff, ne_eq, IH,
      mem_cons, exists_eq_or_imp]

/--
theorem `Multiset.mem_sup_map_support_iff` / 定理 `Multiset.mem_sup_map_support_iff`

English:
theorem Multiset.mem_sup_map_support_iff
  given: [Zero M] {s : Multiset (ι ->₀ M)} {x : ι}
  proof: Quot.inductionOn s fun _ => by
    simpa only [Multiset.quot_mk_to_coe'', Multiset.map_coe, Multiset.sup_coe, List.foldr_map]
    using! List.mem_foldr_sup_support_iff

中文:
定理 Multiset.mem_sup_map_support_iff
  条件: [零 M] {s : Multiset (ι ->₀ M)} {x : ι}
  证明: Quot.inductionOn s fun _ => by
    simpa only [Multiset.quot_mk_to_coe'', Multiset.map_coe, Multiset.sup_coe, List.foldr_map]
    using! List.mem_foldr_sup_support_iff

Depends on / 依赖: List.foldr_map, List.mem_foldr_sup_support_iff, Multiset, Multiset.map_coe, Multiset.quot_mk_to_coe, Multiset.sup_coe, Quot.inductionOn, foldr_map, inductionOn, map_coe, mem_foldr_sup_support_iff, quot_mk_to_coe, sup_coe
-/
theorem Multiset.mem_sup_map_support_iff [Zero M] {s : Multiset (ι ->₀ M)} {x : ι} :
    x in (s.map Finsupp.support).sup ↔ exists f in s, x in f.support :=
  Quot.inductionOn s fun _ => by
    simpa only [Multiset.quot_mk_to_coe'', Multiset.map_coe, Multiset.sup_coe, List.foldr_map]
    using! List.mem_foldr_sup_support_iff

/--
theorem `Finset.mem_sup_support_iff` / 定理 `Finset.mem_sup_support_iff`

English:
theorem Finset.mem_sup_support_iff
  given: [Zero M] {s : Finset (ι ->₀ M)} {x : ι}
  proof: Multiset.mem_sup_map_support_iff

中文:
定理 有限集.mem_sup_support_iff
  条件: [零 M] {s : 有限集 (ι ->₀ M)} {x : ι}
  证明: Multiset.mem_sup_map_support_iff

Depends on / 依赖: Multiset, Multiset.mem_sup_map_support_iff, mem_sup_map_support_iff
-/
theorem Finset.mem_sup_support_iff [Zero M] {s : Finset (ι ->₀ M)} {x : ι} :
    x in s.sup Finsupp.support ↔ exists f in s, x in f.support :=
  Multiset.mem_sup_map_support_iff

open scoped Function -- required for scoped `on` notation

/--
theorem `List.support_sum_eq` / 定理 `List.support_sum_eq`

English:
theorem List.support_sum_eq
  statement: [AddZeroClass M] (l : List (ι ->₀ M))
  proof: by
  induction l with
  | nil => simp
  | cons hd tl IH =>
    simp only [List.pairwise_cons] at hl
    simp only [List.sum_cons, List.foldr_cons]
    rw [Finsupp.support_add_eq]; rw [IH hl.right]; rw [Finset.sup_eq_union]
    suffices _root_.Disjoint hd.support (tl.foldr (fun x y => (Finsupp.support x ⊔ y)) ∅) by
      exact Finset.disjoint_of_subset_right (List.support_sum_subset _) this
    rw [← List.foldr_map]; rw [← Finset.bot_eq_empty]; rw [List.foldr_sup_eq_sup_toFinset]; rw [Finset.disjoint_sup_right]
    intro f hf
    simp only [List.mem_toFinset, List.mem_map] at hf
    obtain ⟨f, hf, rfl⟩ := hf
    exact hl.left _ hf

中文:
定理 列表.support_sum_eq
  结论: [加法零类 M] (l : 列表 (ι ->₀ M))
  证明: by
  induction l with
  | nil => simp
  | cons hd tl IH =>
    simp only [List.pairwise_cons] at hl
    simp only [List.sum_cons, List.foldr_cons]
    rw [Finsupp.support_add_eq]; rw [IH hl.right]; rw [Finset.sup_eq_union]
    suffices _root_.Disjoint hd.support (tl.foldr (fun x y => (Finsupp.support x ⊔ y)) ∅) by
      exact Finset.disjoint_of_subset_right (List.support_sum_subset _) this
    rw [← List.foldr_map]; rw [← Finset.bot_eq_empty]; rw [List.foldr_sup_eq_sup_toFinset]; rw [Finset.disjoint_sup_right]
    intro f hf
    simp only [List.mem_toFinset, List.mem_map] at hf
    obtain ⟨f, hf, rfl⟩ := hf
    exact hl.left _ hf

Depends on / 依赖: Disjoint, Finset, Finset.bot_eq_empty, Finset.disjoint_of_subset_right, Finset.disjoint_sup_right, Finset.sup_eq_union, Finsupp, Finsupp.support, Finsupp.support_add_eq, List.foldr_cons, List.foldr_map, List.foldr_sup_eq_sup_toFinset, List.pairwise_cons, List.sum_cons, List.support_sum_subset, _root_, _root_.Disjoint, bot_eq_empty, disjoint_of_subset_right, disjoint_sup_right
-/
theorem List.support_sum_eq [AddZeroClass M] (l : List (ι ->₀ M))
    (hl : l.Pairwise (_root_.Disjoint on Finsupp.support)) :
    l.sum.support = l.foldr (Finsupp.support · ⊔ ·) ∅ := by
  induction l with
  | nil => simp
  | cons hd tl IH =>
    simp only [List.pairwise_cons] at hl
    simp only [List.sum_cons, List.foldr_cons]
    rw [Finsupp.support_add_eq]; rw [IH hl.right]; rw [Finset.sup_eq_union]
    suffices _root_.Disjoint hd.support (tl.foldr (fun x y => (Finsupp.support x ⊔ y)) ∅) by
      exact Finset.disjoint_of_subset_right (List.support_sum_subset _) this
    rw [← List.foldr_map]; rw [← Finset.bot_eq_empty]; rw [List.foldr_sup_eq_sup_toFinset]; rw [Finset.disjoint_sup_right]
    intro f hf
    simp only [List.mem_toFinset, List.mem_map] at hf
    obtain ⟨f, hf, rfl⟩ := hf
    exact hl.left _ hf

/--
theorem `Multiset.support_sum_eq` / 定理 `Multiset.support_sum_eq`

English:
theorem Multiset.support_sum_eq
  statement: [AddCommMonoid M] (s : Multiset (ι ->₀ M))
  proof: by
  induction s using Quot.inductionOn with | _ a
  obtain ⟨l, hl, hd⟩ := hs
  suffices a.Pairwise (_root_.Disjoint on Finsupp.support) by
    convert! List.support_sum_eq a this
    simp only [quot_mk_to_coe'', map_coe, sup_coe,
      Finset.sup_eq_union, Finset.bot_eq_empty, List.foldr_map]
  simp only [Multiset.quot_mk_to_coe'', Multiset.coe_eq_coe] at hl
  exact hl.symm.pairwise hd fun h => _root_.Disjoint.symm h

中文:
定理 Multiset.support_sum_eq
  结论: [加法交换幺半群 M] (s : Multiset (ι ->₀ M))
  证明: by
  induction s using Quot.inductionOn with | _ a
  obtain ⟨l, hl, hd⟩ := hs
  suffices a.Pairwise (_root_.Disjoint on Finsupp.support) by
    convert! List.support_sum_eq a this
    simp only [quot_mk_to_coe'', map_coe, sup_coe,
      Finset.sup_eq_union, Finset.bot_eq_empty, List.foldr_map]
  simp only [Multiset.quot_mk_to_coe'', Multiset.coe_eq_coe] at hl
  exact hl.symm.pairwise hd fun h => _root_.Disjoint.symm h

Depends on / 依赖: Disjoint, Finset, Finset.bot_eq_empty, Finset.sup_eq_union, Finsupp, Finsupp.support, List.foldr_map, List.support_sum_eq, Multiset, Multiset.coe_eq_coe, Multiset.quot_mk_to_coe, Pairwise, Quot.inductionOn, _root_, _root_.Disjoint, _root_.Disjoint.symm, a.Pairwise, bot_eq_empty, coe_eq_coe, convert
-/
theorem Multiset.support_sum_eq [AddCommMonoid M] (s : Multiset (ι ->₀ M))
    (hs : s.Pairwise (_root_.Disjoint on Finsupp.support)) :
    s.sum.support = (s.map Finsupp.support).sup := by
  induction s using Quot.inductionOn with | _ a
  obtain ⟨l, hl, hd⟩ := hs
  suffices a.Pairwise (_root_.Disjoint on Finsupp.support) by
    convert! List.support_sum_eq a this
    simp only [quot_mk_to_coe'', map_coe, sup_coe,
      Finset.sup_eq_union, Finset.bot_eq_empty, List.foldr_map]
  simp only [Multiset.quot_mk_to_coe'', Multiset.coe_eq_coe] at hl
  exact hl.symm.pairwise hd fun h => _root_.Disjoint.symm h

/--
theorem `Finset.support_sum_eq` / 定理 `Finset.support_sum_eq`

English:
theorem Finset.support_sum_eq
  statement: [AddCommMonoid M] (s : Finset (ι ->₀ M))
  proof: by
  classical
  suffices s.1.Pairwise (_root_.Disjoint on Finsupp.support) by
    convert! Multiset.support_sum_eq s.1 this
    exact (Finset.sum_val _).symm
  obtain ⟨l, hl, hn⟩ : exists l : List (ι ->₀ M), l.toFinset = s ∧ l.Nodup := by
    refine ⟨s.toList, ?_, Finset.nodup_toList _⟩
    simp
  subst hl
  rwa [List.toFinset_val, List.dedup_eq_self.mpr hn, Multiset.pairwise_coe_iff_pairwise,
    ← List.pairwiseDisjoint_iff_coe_toFinset_pairwise_disjoint hn]

中文:
定理 有限集.support_sum_eq
  结论: [加法交换幺半群 M] (s : 有限集 (ι ->₀ M))
  证明: by
  classical
  suffices s.1.Pairwise (_root_.Disjoint on Finsupp.support) by
    convert! Multiset.support_sum_eq s.1 this
    exact (Finset.sum_val _).symm
  obtain ⟨l, hl, hn⟩ : exists l : List (ι ->₀ M), l.toFinset = s ∧ l.Nodup := by
    refine ⟨s.toList, ?_, Finset.nodup_toList _⟩
    simp
  subst hl
  rwa [List.toFinset_val, List.dedup_eq_self.mpr hn, Multiset.pairwise_coe_iff_pairwise,
    ← List.pairwiseDisjoint_iff_coe_toFinset_pairwise_disjoint hn]

Depends on / 依赖: Disjoint, Finset, Finset.nodup_toList, Finset.sum_val, Finsupp, Finsupp.support, List.dedup_eq_self.mpr, List.pairwiseDisjoint_iff_coe_toFinset_pairwise_disjoint, List.toFinset_val, Multiset, Multiset.pairwise_coe_iff_pairwise, Multiset.support_sum_eq, Pairwise, _root_, _root_.Disjoint, classical, convert, dedup_eq_self, l.Nodup, l.toFinset
-/
theorem Finset.support_sum_eq [AddCommMonoid M] (s : Finset (ι ->₀ M))
    (hs : (s : Set (ι ->₀ M)).PairwiseDisjoint Finsupp.support) :
    (s.sum id).support = Finset.sup s Finsupp.support := by
  classical
  suffices s.1.Pairwise (_root_.Disjoint on Finsupp.support) by
    convert! Multiset.support_sum_eq s.1 this
    exact (Finset.sum_val _).symm
  obtain ⟨l, hl, hn⟩ : exists l : List (ι ->₀ M), l.toFinset = s ∧ l.Nodup := by
    refine ⟨s.toList, ?_, Finset.nodup_toList _⟩
    simp
  subst hl
  rwa [List.toFinset_val, List.dedup_eq_self.mpr hn, Multiset.pairwise_coe_iff_pairwise,
    ← List.pairwiseDisjoint_iff_coe_toFinset_pairwise_disjoint hn]
