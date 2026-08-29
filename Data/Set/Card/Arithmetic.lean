/-
Copyright (c) 2025 Pim Otte. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pim Otte
-/
module

public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Data.Set.Card
public import Mathlib.SetTheory.Cardinal.Arithmetic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Results using cardinal arithmetic

This file contains results using cardinal arithmetic that are not in the main cardinal theory files.
It has been separated out to not burden `Mathlib/Data/Set/Card.lean` with extra imports.

## Main results

- `exists_union_disjoint_ncard_eq_of_even`: Given a set `s` with an even cardinality, there exist
  disjoint sets `t` and `u` such that `t ∪ u = s` and `t.ncard = u.ncard`.
- `exists_union_disjoint_cardinal_eq_iff` is the same, except using cardinal notation.
-/

public section

variable {α ι : Type*}

open scoped Finset

/--
theorem `Finset.exists_disjoint_union_of_even_card` / 定理 `Finset.exists_disjoint_union_of_even_card`

English:
theorem Finset.exists_disjoint_union_of_even_card
  given: [DecidableEq α] {s : Finset α} (he : Even #s)
  proof: let ⟨n, hn⟩ := he
  let ⟨t, ht, ht'⟩ := exists_subset_card_eq (show n <= #s by lia)
  ⟨t, s \ t, by simp [card_sdiff_of_subset, disjoint_sdiff, *]⟩

中文:
定理 有限集.存在_disjoint_union_of_even_card
  条件: [DecidableEq α] {s : 有限集 α} (he : Even #s)
  证明: let ⟨n, hn⟩ := he
  let ⟨t, ht, ht'⟩ := exists_subset_card_eq (show n <= #s by lia)
  ⟨t, s \ t, by simp [card_sdiff_of_subset, disjoint_sdiff, *]⟩

Depends on / 依赖: card_sdiff_of_subset, disjoint_sdiff, exists_subset_card_eq
-/
theorem Finset.exists_disjoint_union_of_even_card [DecidableEq α] {s : Finset α} (he : Even #s) :
    exists (t u : Finset α), t union u = s ∧ Disjoint t u ∧ #t = #u :=
  let ⟨n, hn⟩ := he
  let ⟨t, ht, ht'⟩ := exists_subset_card_eq (show n <= #s by lia)
  ⟨t, s \ t, by simp [card_sdiff_of_subset, disjoint_sdiff, *]⟩

/--
theorem `Finset.exists_disjoint_union_of_even_card_iff` / 定理 `Finset.exists_disjoint_union_of_even_card_iff`

English:
theorem Finset.exists_disjoint_union_of_even_card_iff
  given: [DecidableEq α] (s : Finset α)
  proof: ⟨Finset.exists_disjoint_union_of_even_card, by
    rintro ⟨t, u, rfl, hdtu, hctu⟩
    simp_all⟩

@[simp]

中文:
定理 有限集.存在_disjoint_union_of_even_card_iff
  条件: [DecidableEq α] (s : 有限集 α)
  证明: ⟨Finset.exists_disjoint_union_of_even_card, by
    rintro ⟨t, u, rfl, hdtu, hctu⟩
    simp_all⟩

@[simp]

Depends on / 依赖: Finset, Finset.exists_disjoint_union_of_even_card, exists_disjoint_union_of_even_card
-/
theorem Finset.exists_disjoint_union_of_even_card_iff [DecidableEq α] (s : Finset α) :
    Even #s ↔ exists (t u : Finset α), t union u = s ∧ Disjoint t u ∧ #t = #u :=
  ⟨Finset.exists_disjoint_union_of_even_card, by
    rintro ⟨t, u, rfl, hdtu, hctu⟩
    simp_all⟩

@[simp]
/--
lemma `finsum_one` / 引理 `finsum_one`

English:
lemma finsum_one
  given: {s : Set α}
  statement: ∑ᶠ i in s, 1 = s.ncard
  proof: by
  obtain hs | hs := s.infinite_or_finite
  · rw [hs.ncard]
    by_cases h : 1 = 0
    · simp [h]
    · exact finsum_mem_eq_zero_of_infinite (by simpa [Function.support_const h])
  · simp [finsum_mem_eq_finite_toFinset_sum _ hs, Set.ncard_eq_toFinset_card s hs]

中文:
引理 finsum_one
  条件: {s : 集合 α}
  结论: ∑ᶠ i in s, 1 = s.ncard
  证明: by
  obtain hs | hs := s.infinite_or_finite
  · rw [hs.ncard]
    by_cases h : 1 = 0
    · simp [h]
    · exact finsum_mem_eq_zero_of_infinite (by simpa [Function.support_const h])
  · simp [finsum_mem_eq_finite_toFinset_sum _ hs, Set.ncard_eq_toFinset_card s hs]

Depends on / 依赖: Function, Function.support_const, Set.ncard_eq_toFinset_card, finsum_mem_eq_finite_toFinset_sum, finsum_mem_eq_zero_of_infinite, hs.ncard, infinite_or_finite, ncard_eq_toFinset_card, s.infinite_or_finite, support_const
-/
lemma finsum_one {s : Set α} : ∑ᶠ i in s, 1 = s.ncard := by
  obtain hs | hs := s.infinite_or_finite
  · rw [hs.ncard]
    by_cases h : 1 = 0
    · simp [h]
    · exact finsum_mem_eq_zero_of_infinite (by simpa [Function.support_const h])
  · simp [finsum_mem_eq_finite_toFinset_sum _ hs, Set.ncard_eq_toFinset_card s hs]

namespace Finset

/--
lemma `set_ncard_biUnion_le` / 引理 `set_ncard_biUnion_le`

English:
lemma set_ncard_biUnion_le
  given: (t : Finset ι) (s : ι -> Set α)
  proof: t.apply_union_le_sum (by simp) (Set.ncard_union_le _ _)

中文:
引理 set_ncard_biUnion_le
  条件: (t : 有限集 ι) (s : ι -> 集合 α)
  证明: t.apply_union_le_sum (by simp) (Set.ncard_union_le _ _)

Depends on / 依赖: Set.ncard_union_le, apply_union_le_sum, ncard_union_le, t.apply_union_le_sum
-/
lemma set_ncard_biUnion_le (t : Finset ι) (s : ι -> Set α) :
    (⋃ i in t, s i).ncard <= ∑ i in t, (s i).ncard :=
  t.apply_union_le_sum (by simp) (Set.ncard_union_le _ _)

/--
lemma `set_encard_biUnion_le` / 引理 `set_encard_biUnion_le`

English:
lemma set_encard_biUnion_le
  given: (t : Finset ι) (s : ι -> Set α)
  proof: t.apply_union_le_sum (by simp) (Set.encard_union_le _ _)

中文:
引理 set_encard_biUnion_le
  条件: (t : 有限集 ι) (s : ι -> 集合 α)
  证明: t.apply_union_le_sum (by simp) (Set.encard_union_le _ _)

Depends on / 依赖: Set.encard_union_le, apply_union_le_sum, encard_union_le, t.apply_union_le_sum
-/
lemma set_encard_biUnion_le (t : Finset ι) (s : ι -> Set α) :
    (⋃ i in t, s i).encard <= ∑ i in t, (s i).encard :=
  t.apply_union_le_sum (by simp) (Set.encard_union_le _ _)

end Finset

namespace Set

variable {s : Set α}

open Cardinal

/--
theorem `Infinite.exists_union_disjoint_cardinal_eq_of_infinite` / 定理 `Infinite.exists_union_disjoint_cardinal_eq_of_infinite`

English:
theorem Infinite.exists_union_disjoint_cardinal_eq_of_infinite
  given: (h : s.Infinite)
  proof: by
  have := h.to_subtype
  obtain ⟨f⟩ : Nonempty (s ≃ s oplus s) := by
    rw [← Cardinal.eq]; rw [← add_def]; rw [add_mk_eq_self]
  refine ⟨Subtype.val '' f ⁻¹' (range .inl), Subtype.val '' f ⁻¹' (range .inr), ?_, ?_, ?_⟩
  · simp [← image_union, ← preimage_union]
  · exact disjoint_image_of_injec

中文:
定理 无限.存在_union_disjoint_cardinal_eq_of_infinite
  条件: (h : s.无限)
  证明: by
  have := h.to_subtype
  obtain ⟨f⟩ : Nonempty (s ≃ s oplus s) := by
    rw [← Cardinal.eq]; rw [← add_def]; rw [add_mk_eq_self]
  refine ⟨Subtype.val '' f ⁻¹' (range .inl), Subtype.val '' f ⁻¹' (range .inr), ?_, ?_, ?_⟩
  · simp [← image_union, ← preimage_union]
  · exact disjoint_image_of_injec

Depends on / 依赖: Cardinal, Cardinal.eq, Nonempty, Subtype, Subtype.val, Subtype.val_injective, add_def, add_mk_eq_self, disjoint, disjoint_image_of_injective, h.to_subtype, image_union, isCompl_range_inl_range_inr, isCompl_range_inl_range_inr.disjoint.preimage, mk_image_eq, preimage, preimage_union, to_subtype, val_injective
-/
theorem Infinite.exists_union_disjoint_cardinal_eq_of_infinite (h : s.Infinite) :
    exists (t u : Set α), t union u = s ∧ Disjoint t u ∧ #t = #u := by
  have := h.to_subtype
  obtain ⟨f⟩ : Nonempty (s ≃ s oplus s) := by
    rw [← Cardinal.eq]; rw [← add_def]; rw [add_mk_eq_self]
  refine ⟨Subtype.val '' f ⁻¹' (range .inl), Subtype.val '' f ⁻¹' (range .inr), ?_, ?_, ?_⟩
  · simp [← image_union, ← preimage_union]
  · exact disjoint_image_of_injective Subtype.val_injective
      (isCompl_range_inl_range_inr.disjoint.preimage f)
  · simp [mk_image_eq Subtype.val_injective]

/--
theorem `exists_union_disjoint_cardinal_eq_of_even` / 定理 `exists_union_disjoint_cardinal_eq_of_even`

English:
theorem exists_union_disjoint_cardinal_eq_of_even
  given: (he : Even s.ncard)
  proof: by
  obtain hs | hs := s.infinite_or_finite
  · exact hs.exists_union_disjoint_cardinal_eq_of_infinite
  classical
  rw [ncard_eq_toFinset_card s hs] at he
  obtain ⟨t, u, hutu, hdtu, hctu⟩ := Finset.exists_disjoint_union_of_even_card he
  use t, u
  simp [← Finset.coe_union, *]

中文:
定理 存在_union_disjoint_cardinal_eq_of_even
  条件: (he : Even s.ncard)
  证明: by
  obtain hs | hs := s.infinite_or_finite
  · exact hs.exists_union_disjoint_cardinal_eq_of_infinite
  classical
  rw [ncard_eq_toFinset_card s hs] at he
  obtain ⟨t, u, hutu, hdtu, hctu⟩ := Finset.exists_disjoint_union_of_even_card he
  use t, u
  simp [← Finset.coe_union, *]

Depends on / 依赖: Finset, Finset.coe_union, Finset.exists_disjoint_union_of_even_card, classical, coe_union, exists_disjoint_union_of_even_card, exists_union_disjoint_cardinal_eq_of_infinite, hs.exists_union_disjoint_cardinal_eq_of_infinite, infinite_or_finite, ncard_eq_toFinset_card, s.infinite_or_finite
-/
theorem exists_union_disjoint_cardinal_eq_of_even (he : Even s.ncard) :
    exists (t u : Set α), t union u = s ∧ Disjoint t u ∧ #t = #u := by
  obtain hs | hs := s.infinite_or_finite
  · exact hs.exists_union_disjoint_cardinal_eq_of_infinite
  classical
  rw [ncard_eq_toFinset_card s hs] at he
  obtain ⟨t, u, hutu, hdtu, hctu⟩ := Finset.exists_disjoint_union_of_even_card he
  use t, u
  simp [← Finset.coe_union, *]

/--
theorem `exists_union_disjoint_ncard_eq_of_even` / 定理 `exists_union_disjoint_ncard_eq_of_even`

English:
theorem exists_union_disjoint_ncard_eq_of_even
  given: (he : Even s.ncard)
  proof: by
  obtain ⟨t, u, hutu, hdtu, hctu⟩ := exists_union_disjoint_cardinal_eq_of_even he
  exact ⟨t, u, hutu, hdtu, congrArg Cardinal.toNat hctu⟩

中文:
定理 存在_union_disjoint_ncard_eq_of_even
  条件: (he : Even s.ncard)
  证明: by
  obtain ⟨t, u, hutu, hdtu, hctu⟩ := exists_union_disjoint_cardinal_eq_of_even he
  exact ⟨t, u, hutu, hdtu, congrArg Cardinal.toNat hctu⟩

Depends on / 依赖: Cardinal, Cardinal.toNat, exists_union_disjoint_cardinal_eq_of_even
-/
theorem exists_union_disjoint_ncard_eq_of_even (he : Even s.ncard) :
    exists (t u : Set α), t union u = s ∧ Disjoint t u ∧ t.ncard = u.ncard := by
  obtain ⟨t, u, hutu, hdtu, hctu⟩ := exists_union_disjoint_cardinal_eq_of_even he
  exact ⟨t, u, hutu, hdtu, congrArg Cardinal.toNat hctu⟩

/--
theorem `exists_union_disjoint_cardinal_eq_iff` / 定理 `exists_union_disjoint_cardinal_eq_iff`

English:
theorem exists_union_disjoint_cardinal_eq_iff
  given: (s : Set α)
  proof: by
  use exists_union_disjoint_cardinal_eq_of_even
  rintro ⟨t, u, rfl, hdtu, hctu⟩
  obtain hfin | hnfin := (t union u).finite_or_infinite
  · rw [finite_union] at hfin
    have hn : t.ncard = u.ncard := congrArg Cardinal.toNat hctu
    rw [ncard_union_eq hdtu hfin.1 hfin.2]; rw [hn]
    exact Even

中文:
定理 存在_union_disjoint_cardinal_eq_iff
  条件: (s : 集合 α)
  证明: by
  use exists_union_disjoint_cardinal_eq_of_even
  rintro ⟨t, u, rfl, hdtu, hctu⟩
  obtain hfin | hnfin := (t union u).finite_or_infinite
  · rw [finite_union] at hfin
    have hn : t.ncard = u.ncard := congrArg Cardinal.toNat hctu
    rw [ncard_union_eq hdtu hfin.1 hfin.2]; rw [hn]
    exact Even

Depends on / 依赖: Cardinal, Cardinal.toNat, Even.add_self, add_self, exists_union_disjoint_cardinal_eq_of_even, finite_or_infinite, finite_union, hnfin.ncard, ncard_union_eq, t.ncard, u.ncard
-/
theorem exists_union_disjoint_cardinal_eq_iff (s : Set α) :
    Even (s.ncard) ↔ exists (t u : Set α), t union u = s ∧ Disjoint t u ∧ #t = #u := by
  use exists_union_disjoint_cardinal_eq_of_even
  rintro ⟨t, u, rfl, hdtu, hctu⟩
  obtain hfin | hnfin := (t union u).finite_or_infinite
  · rw [finite_union] at hfin
    have hn : t.ncard = u.ncard := congrArg Cardinal.toNat hctu
    rw [ncard_union_eq hdtu hfin.1 hfin.2]; rw [hn]
    exact Even.add_self u.ncard
  · simp [hnfin.ncard]

open scoped Function

/--
lemma `Finite.ncard_biUnion` / 引理 `Finite.ncard_biUnion`

English:
lemma Finite.ncard_biUnion
  statement: {t : Set ι} (ht : t.Finite) {s : ι -> Set α} (hs : forall i in t, (s i).Finite)
  proof: by
  rw [← finsum_one]; rw [finsum_mem_biUnion h ht hs]; rw [finsum_mem_congr rfl fun i hi => finsum_one]

中文:
引理 有限.ncard_biUnion
  结论: {t : 集合 ι} (ht : t.有限) {s : ι -> 集合 α} (hs : 对任意 i in t, (s i).有限)
  证明: by
  rw [← finsum_one]; rw [finsum_mem_biUnion h ht hs]; rw [finsum_mem_congr rfl fun i hi => finsum_one]

Depends on / 依赖: finsum_mem_biUnion, finsum_mem_congr, finsum_one
-/
lemma Finite.ncard_biUnion {t : Set ι} (ht : t.Finite) {s : ι -> Set α} (hs : forall i in t, (s i).Finite)
    (h : t.PairwiseDisjoint s) : (⋃ i in t, s i).ncard = ∑ᶠ i in t, (s i).ncard := by
  rw [← finsum_one]; rw [finsum_mem_biUnion h ht hs]; rw [finsum_mem_congr rfl fun i hi => finsum_one]

/--
lemma `ncard_iUnion_of_finite` / 引理 `ncard_iUnion_of_finite`

English:
lemma ncard_iUnion_of_finite
  statement: [Finite ι] {s : ι -> Set α} (hs : forall i, (s i).Finite)
  proof: by
  rw [← finsum_mem_univ]; rw [← finite_univ.ncard_biUnion (by simpa) (fun _ _ _ _ hab => h hab)]
  simp

中文:
引理 ncard_iUnion_of_finite
  结论: [有限 ι] {s : ι -> 集合 α} (hs : 对任意 i, (s i).有限)
  证明: by
  rw [← finsum_mem_univ]; rw [← finite_univ.ncard_biUnion (by simpa) (fun _ _ _ _ hab => h hab)]
  simp

Depends on / 依赖: finite_univ, finite_univ.ncard_biUnion, finsum_mem_univ, ncard_biUnion
-/
lemma ncard_iUnion_of_finite [Finite ι] {s : ι -> Set α} (hs : forall i, (s i).Finite)
    (h : Pairwise (Disjoint on s)) : (⋃ i, s i).ncard = ∑ᶠ i : ι, (s i).ncard := by
  rw [← finsum_mem_univ]; rw [← finite_univ.ncard_biUnion (by simpa) (fun _ _ _ _ hab => h hab)]
  simp

/--
lemma `Finite.encard_biUnion` / 引理 `Finite.encard_biUnion`

English:
lemma Finite.encard_biUnion
  statement: {t : Set ι} (ht : t.Finite) {s : ι -> Set α}
  proof: by
  by_cases! h : forall i in t, (s i).Finite
  · have : (⋃ i in t, s i).Finite := ht.biUnion (fun i hi => h i hi)
    rw [← this.cast_ncard_eq]; rw [ncard_biUnion ht h hs]; rw [← finsum_mem_congr rfl fun i hi => (h i hi).cast_ncard_eq]; rw [Nat.cast_finsum_mem ht]
  · obtain ⟨i, hi, (hn : (s i).In

中文:
引理 有限.encard_biUnion
  结论: {t : 集合 ι} (ht : t.有限) {s : ι -> 集合 α}
  证明: by
  by_cases! h : forall i in t, (s i).Finite
  · have : (⋃ i in t, s i).Finite := ht.biUnion (fun i hi => h i hi)
    rw [← this.cast_ncard_eq]; rw [ncard_biUnion ht h hs]; rw [← finsum_mem_congr rfl fun i hi => (h i hi).cast_ncard_eq]; rw [Nat.cast_finsum_mem ht]
  · obtain ⟨i, hi, (hn : (s i).In

Depends on / 依赖: Finite, Infinite, Nat.cast_finsum_mem, Set.insert_sdiff_self_of_mem, biUnion, cast_finsum_mem, cast_ncard_eq, finsum_mem_congr, finsum_mem_insert, ht.biUnion, ht.sdiff, insert_sdiff_self_of_mem, mem_singleton, ncard_biUnion, notMem_sdiff_of_mem, this.cast_ncard_eq
-/
lemma Finite.encard_biUnion {t : Set ι} (ht : t.Finite) {s : ι -> Set α}
    (hs : t.PairwiseDisjoint s) : (⋃ i in t, s i).encard = ∑ᶠ i in t, (s i).encard := by
  by_cases! h : forall i in t, (s i).Finite
  · have : (⋃ i in t, s i).Finite := ht.biUnion (fun i hi => h i hi)
    rw [← this.cast_ncard_eq]; rw [ncard_biUnion ht h hs]; rw [← finsum_mem_congr rfl fun i hi => (h i hi).cast_ncard_eq]; rw [Nat.cast_finsum_mem ht]
  · obtain ⟨i, hi, (hn : (s i).Infinite)⟩ := h
    rw [← Set.insert_sdiff_self_of_mem hi]; rw [finsum_mem_insert _ (notMem_sdiff_of_mem <| mem_singleton i) ht.sdiff]
    simp [hn]

/--
lemma `encard_iUnion_of_finite` / 引理 `encard_iUnion_of_finite`

English:
lemma encard_iUnion_of_finite
  given: [Finite ι] {s : ι -> Set α} (hs : Pairwise (Disjoint on s))
  proof: by
  rw [← finsum_mem_univ]; rw [← finite_univ.encard_biUnion (fun a _ b _ hab => hs hab)]
  simp

中文:
引理 encard_iUnion_of_finite
  条件: [有限 ι] {s : ι -> 集合 α} (hs : 两两 (Disjoint on s))
  证明: by
  rw [← finsum_mem_univ]; rw [← finite_univ.encard_biUnion (fun a _ b _ hab => hs hab)]
  simp

Depends on / 依赖: encard_biUnion, finite_univ, finite_univ.encard_biUnion, finsum_mem_univ
-/
lemma encard_iUnion_of_finite [Finite ι] {s : ι -> Set α} (hs : Pairwise (Disjoint on s)) :
    (⋃ i, s i).encard = ∑ᶠ i, (s i).encard := by
  rw [← finsum_mem_univ]; rw [← finite_univ.encard_biUnion (fun a _ b _ hab => hs hab)]
  simp

/--
lemma `Finite.ncard_biUnion_le` / 引理 `Finite.ncard_biUnion_le`

English:
lemma Finite.ncard_biUnion_le
  given: {t : Set ι} (ht : t.Finite) (s : ι -> Set α)
  proof: by
  simpa [← finsum_mem_eq_finite_toFinset_sum] using ht.toFinset.set_ncard_biUnion_le s

中文:
引理 有限.ncard_biUnion_le
  条件: {t : 集合 ι} (ht : t.有限) (s : ι -> 集合 α)
  证明: by
  simpa [← finsum_mem_eq_finite_toFinset_sum] using ht.toFinset.set_ncard_biUnion_le s

Depends on / 依赖: finsum_mem_eq_finite_toFinset_sum, ht.toFinset.set_ncard_biUnion_le, set_ncard_biUnion_le, toFinset
-/
lemma Finite.ncard_biUnion_le {t : Set ι} (ht : t.Finite) (s : ι -> Set α) :
    (⋃ i in t, s i).ncard <= ∑ᶠ i in t, (s i).ncard := by
  simpa [← finsum_mem_eq_finite_toFinset_sum] using ht.toFinset.set_ncard_biUnion_le s

/--
lemma `Finite.encard_biUnion_le` / 引理 `Finite.encard_biUnion_le`

English:
lemma Finite.encard_biUnion_le
  given: {t : Set ι} (ht : t.Finite) (s : ι -> Set α)
  proof: by
  simpa [← finsum_mem_eq_finite_toFinset_sum] using ht.toFinset.set_encard_biUnion_le s

中文:
引理 有限.encard_biUnion_le
  条件: {t : 集合 ι} (ht : t.有限) (s : ι -> 集合 α)
  证明: by
  simpa [← finsum_mem_eq_finite_toFinset_sum] using ht.toFinset.set_encard_biUnion_le s

Depends on / 依赖: finsum_mem_eq_finite_toFinset_sum, ht.toFinset.set_encard_biUnion_le, set_encard_biUnion_le, toFinset
-/
lemma Finite.encard_biUnion_le {t : Set ι} (ht : t.Finite) (s : ι -> Set α) :
    (⋃ i in t, s i).encard <= ∑ᶠ i in t, (s i).encard := by
  simpa [← finsum_mem_eq_finite_toFinset_sum] using ht.toFinset.set_encard_biUnion_le s

/--
lemma `ncard_iUnion_le_of_fintype` / 引理 `ncard_iUnion_le_of_fintype`

English:
lemma ncard_iUnion_le_of_fintype
  given: [Fintype ι] (s : ι -> Set α)
  proof: by
  simpa using Finset.univ.set_ncard_biUnion_le s

中文:
引理 ncard_iUnion_le_of_fintype
  条件: [有限类型 ι] (s : ι -> 集合 α)
  证明: by
  simpa using Finset.univ.set_ncard_biUnion_le s

Depends on / 依赖: Finset, Finset.univ.set_ncard_biUnion_le, set_ncard_biUnion_le
-/
lemma ncard_iUnion_le_of_fintype [Fintype ι] (s : ι -> Set α) :
    (⋃ i, s i).ncard <= ∑ i, (s i).ncard := by
  simpa using Finset.univ.set_ncard_biUnion_le s

/--
lemma `encard_iUnion_le_of_fintype` / 引理 `encard_iUnion_le_of_fintype`

English:
lemma encard_iUnion_le_of_fintype
  given: [Fintype ι] (s : ι -> Set α)
  proof: by
  simpa using Finset.univ.set_encard_biUnion_le s

中文:
引理 encard_iUnion_le_of_fintype
  条件: [有限类型 ι] (s : ι -> 集合 α)
  证明: by
  simpa using Finset.univ.set_encard_biUnion_le s

Depends on / 依赖: Finset, Finset.univ.set_encard_biUnion_le, set_encard_biUnion_le
-/
lemma encard_iUnion_le_of_fintype [Fintype ι] (s : ι -> Set α) :
    (⋃ i, s i).encard <= ∑ i, (s i).encard := by
  simpa using Finset.univ.set_encard_biUnion_le s

/--
lemma `ncard_iUnion_le_of_finite` / 引理 `ncard_iUnion_le_of_finite`

English:
lemma ncard_iUnion_le_of_finite
  given: [Finite ι] (s : ι -> Set α)
  proof: by
  simpa using finite_univ.ncard_biUnion_le s

中文:
引理 ncard_iUnion_le_of_finite
  条件: [有限 ι] (s : ι -> 集合 α)
  证明: by
  simpa using finite_univ.ncard_biUnion_le s

Depends on / 依赖: finite_univ, finite_univ.ncard_biUnion_le, ncard_biUnion_le
-/
lemma ncard_iUnion_le_of_finite [Finite ι] (s : ι -> Set α) :
    (⋃ i, s i).ncard <= ∑ᶠ i, (s i).ncard := by
  simpa using finite_univ.ncard_biUnion_le s

/--
lemma `encard_iUnion_le_of_finite` / 引理 `encard_iUnion_le_of_finite`

English:
lemma encard_iUnion_le_of_finite
  given: [Finite ι] (s : ι -> Set α)
  proof: by
  simpa using finite_univ.encard_biUnion_le s

中文:
引理 encard_iUnion_le_of_finite
  条件: [有限 ι] (s : ι -> 集合 α)
  证明: by
  simpa using finite_univ.encard_biUnion_le s

Depends on / 依赖: encard_biUnion_le, finite_univ, finite_univ.encard_biUnion_le
-/
lemma encard_iUnion_le_of_finite [Finite ι] (s : ι -> Set α) :
    (⋃ i, s i).encard <= ∑ᶠ i, (s i).encard := by
  simpa using finite_univ.encard_biUnion_le s

end Set
