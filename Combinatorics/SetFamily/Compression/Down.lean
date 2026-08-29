/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Lattice.Fold

/-!
# Down-compressions

This file defines down-compression.

Down-compressing `𝒜 : Finset (Finset α)` along `a : α` means removing `a` from the elements of `𝒜`,
when the resulting set is not already in `𝒜`.

## Main declarations

* `Finset.nonMemberSubfamily`: `𝒜.nonMemberSubfamily a` is the subfamily of sets not containing
  `a`.
* `Finset.memberSubfamily`: `𝒜.memberSubfamily a` is the image of the subfamily of sets containing
  `a` under removing `a`.
* `Down.compression`: Down-compression.

## Notation

`𝓓 a 𝒜` is notation for `Down.compress a 𝒜` in scope `SetFamily`.

## References

* https://github.com/b-mehta/maths-notes/blob/master/iii/mich/combinatorics.pdf

## Tags

compression, down-compression
-/

@[expose] public section


variable {α : Type*} [DecidableEq α] {𝒜 : Finset (Finset α)} {s : Finset α} {a : α}

namespace Finset

/--
Definition of `nonMemberSubfamily` / `nonMemberSubfamily` 的定义

English:
definition nonMemberSubfamily
  signature: (a : α) (𝒜 : Finset (Finset α))
  body: {s in 𝒜 | a ∉ s}

中文:
定义 nonMemberSubfamily
  签名: (a : α) (𝒜 : 有限集 (有限集 α))
  定义体: {s in 𝒜 | a ∉ s}
-/
def nonMemberSubfamily (a : α) (𝒜 : Finset (Finset α)) : Finset (Finset α) := {s in 𝒜 | a ∉ s}

/--
Definition of `memberSubfamily` / `memberSubfamily` 的定义

English:
definition memberSubfamily
  signature: (a : α) (𝒜 : Finset (Finset α))
  body: {s in 𝒜 | a in s}.image fun s => erase s a

@[simp]

中文:
定义 memberSubfamily
  签名: (a : α) (𝒜 : 有限集 (有限集 α))
  定义体: {s in 𝒜 | a in s}.image fun s => erase s a

@[simp]
-/
def memberSubfamily (a : α) (𝒜 : Finset (Finset α)) : Finset (Finset α) :=
  {s in 𝒜 | a in s}.image fun s => erase s a

@[simp]
/--
theorem `mem_nonMemberSubfamily` / 定理 `mem_nonMemberSubfamily`

English:
theorem mem_nonMemberSubfamily
  statement: s in 𝒜.nonMemberSubfamily a ↔ s in 𝒜 ∧ a ∉ s
  proof: by
  simp [nonMemberSubfamily]

@[simp]

中文:
定理 mem_nonMemberSubfamily
  结论: s in 𝒜.nonMemberSubfamily a ↔ s in 𝒜 ∧ a ∉ s
  证明: by
  simp [nonMemberSubfamily]

@[simp]

Depends on / 依赖: nonMemberSubfamily
-/
theorem mem_nonMemberSubfamily : s in 𝒜.nonMemberSubfamily a ↔ s in 𝒜 ∧ a ∉ s := by
  simp [nonMemberSubfamily]

@[simp]
/--
theorem `mem_memberSubfamily` / 定理 `mem_memberSubfamily`

English:
theorem mem_memberSubfamily
  statement: s in 𝒜.memberSubfamily a ↔ insert a s in 𝒜 ∧ a ∉ s
  proof: by
  simp_rw [memberSubfamily, mem_image, mem_filter]
  refine ⟨?_, fun h => ⟨insert a s, ⟨h.1, by simp⟩, erase_insert h.2⟩⟩
  rintro ⟨s, ⟨hs1, hs2⟩, rfl⟩
  rw [insert_erase hs2]
  exact ⟨hs1, notMem_erase _ _⟩

中文:
定理 mem_memberSubfamily
  结论: s in 𝒜.memberSubfamily a ↔ insert a s in 𝒜 ∧ a ∉ s
  证明: by
  simp_rw [memberSubfamily, mem_image, mem_filter]
  refine ⟨?_, fun h => ⟨insert a s, ⟨h.1, by simp⟩, erase_insert h.2⟩⟩
  rintro ⟨s, ⟨hs1, hs2⟩, rfl⟩
  rw [insert_erase hs2]
  exact ⟨hs1, notMem_erase _ _⟩

Depends on / 依赖: erase_insert, insert, insert_erase, mem_filter, mem_image, memberSubfamily, notMem_erase, simp_rw
-/
theorem mem_memberSubfamily : s in 𝒜.memberSubfamily a ↔ insert a s in 𝒜 ∧ a ∉ s := by
  simp_rw [memberSubfamily, mem_image, mem_filter]
  refine ⟨?_, fun h => ⟨insert a s, ⟨h.1, by simp⟩, erase_insert h.2⟩⟩
  rintro ⟨s, ⟨hs1, hs2⟩, rfl⟩
  rw [insert_erase hs2]
  exact ⟨hs1, notMem_erase _ _⟩

/--
theorem `nonMemberSubfamily_inter` / 定理 `nonMemberSubfamily_inter`

English:
theorem nonMemberSubfamily_inter
  given: (a : α) (𝒜 ℬ : Finset (Finset α))
  proof: filter_inter_distrib _ _ _

中文:
定理 nonMemberSubfamily_inter
  条件: (a : α) (𝒜 ℬ : 有限集 (有限集 α))
  证明: filter_inter_distrib _ _ _

Depends on / 依赖: filter_inter_distrib
-/
theorem nonMemberSubfamily_inter (a : α) (𝒜 ℬ : Finset (Finset α)) :
    (𝒜 inter ℬ).nonMemberSubfamily a = 𝒜.nonMemberSubfamily a inter ℬ.nonMemberSubfamily a :=
  filter_inter_distrib _ _ _

/--
theorem `memberSubfamily_inter` / 定理 `memberSubfamily_inter`

English:
theorem memberSubfamily_inter
  given: (a : α) (𝒜 ℬ : Finset (Finset α))
  proof: by
  unfold memberSubfamily
  rw [filter_inter_distrib]; rw [image_inter_of_injOn _ _ ((erase_injOn' _).mono _)]
  simp

中文:
定理 memberSubfamily_inter
  条件: (a : α) (𝒜 ℬ : 有限集 (有限集 α))
  证明: by
  unfold memberSubfamily
  rw [filter_inter_distrib]; rw [image_inter_of_injOn _ _ ((erase_injOn' _).mono _)]
  simp

Depends on / 依赖: erase_injOn, filter_inter_distrib, image_inter_of_injOn, memberSubfamily
-/
theorem memberSubfamily_inter (a : α) (𝒜 ℬ : Finset (Finset α)) :
    (𝒜 inter ℬ).memberSubfamily a = 𝒜.memberSubfamily a inter ℬ.memberSubfamily a := by
  unfold memberSubfamily
  rw [filter_inter_distrib]; rw [image_inter_of_injOn _ _ ((erase_injOn' _).mono _)]
  simp

/--
theorem `nonMemberSubfamily_union` / 定理 `nonMemberSubfamily_union`

English:
theorem nonMemberSubfamily_union
  given: (a : α) (𝒜 ℬ : Finset (Finset α))
  proof: filter_union _ _ _

中文:
定理 nonMemberSubfamily_union
  条件: (a : α) (𝒜 ℬ : 有限集 (有限集 α))
  证明: filter_union _ _ _

Depends on / 依赖: filter_union
-/
theorem nonMemberSubfamily_union (a : α) (𝒜 ℬ : Finset (Finset α)) :
    (𝒜 union ℬ).nonMemberSubfamily a = 𝒜.nonMemberSubfamily a union ℬ.nonMemberSubfamily a :=
  filter_union _ _ _

/--
theorem `memberSubfamily_union` / 定理 `memberSubfamily_union`

English:
theorem memberSubfamily_union
  given: (a : α) (𝒜 ℬ : Finset (Finset α))
  proof: by
  simp_rw [memberSubfamily, filter_union, image_union]

中文:
定理 memberSubfamily_union
  条件: (a : α) (𝒜 ℬ : 有限集 (有限集 α))
  证明: by
  simp_rw [memberSubfamily, filter_union, image_union]

Depends on / 依赖: filter_union, image_union, memberSubfamily, simp_rw
-/
theorem memberSubfamily_union (a : α) (𝒜 ℬ : Finset (Finset α)) :
    (𝒜 union ℬ).memberSubfamily a = 𝒜.memberSubfamily a union ℬ.memberSubfamily a := by
  simp_rw [memberSubfamily, filter_union, image_union]

/--
theorem `card_memberSubfamily_add_card_nonMemberSubfamily` / 定理 `card_memberSubfamily_add_card_nonMemberSubfamily`

English:
theorem card_memberSubfamily_add_card_nonMemberSubfamily
  given: (a : α) (𝒜 : Finset (Finset α))
  proof: by
  rw [memberSubfamily]; rw [nonMemberSubfamily]; rw [card_image_of_injOn]
  · conv_rhs => rw [← card_filter_add_card_filter_not (fun s => (a in s))]
  · apply (erase_injOn' _).mono
    simp

中文:
定理 card_memberSubfamily_add_card_nonMemberSubfamily
  条件: (a : α) (𝒜 : 有限集 (有限集 α))
  证明: by
  rw [memberSubfamily]; rw [nonMemberSubfamily]; rw [card_image_of_injOn]
  · conv_rhs => rw [← card_filter_add_card_filter_not (fun s => (a in s))]
  · apply (erase_injOn' _).mono
    simp

Depends on / 依赖: card_filter_add_card_filter_not, card_image_of_injOn, conv_rhs, erase_injOn, memberSubfamily, nonMemberSubfamily
-/
theorem card_memberSubfamily_add_card_nonMemberSubfamily (a : α) (𝒜 : Finset (Finset α)) :
    #(𝒜.memberSubfamily a) + #(𝒜.nonMemberSubfamily a) = #𝒜 := by
  rw [memberSubfamily]; rw [nonMemberSubfamily]; rw [card_image_of_injOn]
  · conv_rhs => rw [← card_filter_add_card_filter_not (fun s => (a in s))]
  · apply (erase_injOn' _).mono
    simp

/--
theorem `memberSubfamily_union_nonMemberSubfamily` / 定理 `memberSubfamily_union_nonMemberSubfamily`

English:
theorem memberSubfamily_union_nonMemberSubfamily
  given: (a : α) (𝒜 : Finset (Finset α))
  proof: by
  ext s
  simp only [mem_union, mem_memberSubfamily, mem_nonMemberSubfamily, mem_image]
  constructor
  · rintro (h | h)
    · exact ⟨_, h.1, erase_insert h.2⟩
    · exact ⟨_, h.1, erase_eq_of_notMem h.2⟩
  · rintro ⟨s, hs, rfl⟩
    by_cases ha : a in s
    · exact Or.inl ⟨by rwa [insert_erase ha], notMem_erase _ _⟩
    · exact Or.inr ⟨by rwa [erase_eq_of_notMem ha], notMem_erase _ _⟩

@[simp]

中文:
定理 memberSubfamily_union_nonMemberSubfamily
  条件: (a : α) (𝒜 : 有限集 (有限集 α))
  证明: by
  ext s
  simp only [mem_union, mem_memberSubfamily, mem_nonMemberSubfamily, mem_image]
  constructor
  · rintro (h | h)
    · exact ⟨_, h.1, erase_insert h.2⟩
    · exact ⟨_, h.1, erase_eq_of_notMem h.2⟩
  · rintro ⟨s, hs, rfl⟩
    by_cases ha : a in s
    · exact Or.inl ⟨by rwa [insert_erase ha], notMem_erase _ _⟩
    · exact Or.inr ⟨by rwa [erase_eq_of_notMem ha], notMem_erase _ _⟩

@[simp]

Depends on / 依赖: Or.inl, Or.inr, erase_eq_of_notMem, erase_insert, insert_erase, mem_image, mem_memberSubfamily, mem_nonMemberSubfamily, mem_union, notMem_erase
-/
theorem memberSubfamily_union_nonMemberSubfamily (a : α) (𝒜 : Finset (Finset α)) :
    𝒜.memberSubfamily a union 𝒜.nonMemberSubfamily a = 𝒜.image fun s => s.erase a := by
  ext s
  simp only [mem_union, mem_memberSubfamily, mem_nonMemberSubfamily, mem_image]
  constructor
  · rintro (h | h)
    · exact ⟨_, h.1, erase_insert h.2⟩
    · exact ⟨_, h.1, erase_eq_of_notMem h.2⟩
  · rintro ⟨s, hs, rfl⟩
    by_cases ha : a in s
    · exact Or.inl ⟨by rwa [insert_erase ha], notMem_erase _ _⟩
    · exact Or.inr ⟨by rwa [erase_eq_of_notMem ha], notMem_erase _ _⟩

@[simp]
/--
theorem `memberSubfamily_memberSubfamily` / 定理 `memberSubfamily_memberSubfamily`

English:
theorem memberSubfamily_memberSubfamily
  statement: (𝒜.memberSubfamily a).memberSubfamily a = ∅
  proof: by
  ext
  simp

@[simp]

中文:
定理 memberSubfamily_memberSubfamily
  结论: (𝒜.memberSubfamily a).memberSubfamily a = ∅
  证明: by
  ext
  simp

@[simp]
-/
theorem memberSubfamily_memberSubfamily : (𝒜.memberSubfamily a).memberSubfamily a = ∅ := by
  ext
  simp

@[simp]
/--
theorem `memberSubfamily_nonMemberSubfamily` / 定理 `memberSubfamily_nonMemberSubfamily`

English:
theorem memberSubfamily_nonMemberSubfamily
  statement: (𝒜.nonMemberSubfamily a).memberSubfamily a = ∅
  proof: by
  ext
  simp

@[simp]

中文:
定理 memberSubfamily_nonMemberSubfamily
  结论: (𝒜.nonMemberSubfamily a).memberSubfamily a = ∅
  证明: by
  ext
  simp

@[simp]
-/
theorem memberSubfamily_nonMemberSubfamily : (𝒜.nonMemberSubfamily a).memberSubfamily a = ∅ := by
  ext
  simp

@[simp]
/--
theorem `nonMemberSubfamily_memberSubfamily` / 定理 `nonMemberSubfamily_memberSubfamily`

English:
theorem nonMemberSubfamily_memberSubfamily
  proof: by
  ext
  simp

@[simp]

中文:
定理 nonMemberSubfamily_memberSubfamily
  证明: by
  ext
  simp

@[simp]
-/
theorem nonMemberSubfamily_memberSubfamily :
    (𝒜.memberSubfamily a).nonMemberSubfamily a = 𝒜.memberSubfamily a := by
  ext
  simp

@[simp]
/--
theorem `nonMemberSubfamily_nonMemberSubfamily` / 定理 `nonMemberSubfamily_nonMemberSubfamily`

English:
theorem nonMemberSubfamily_nonMemberSubfamily
  proof: by
  ext
  simp

中文:
定理 nonMemberSubfamily_nonMemberSubfamily
  证明: by
  ext
  simp
-/
theorem nonMemberSubfamily_nonMemberSubfamily :
    (𝒜.nonMemberSubfamily a).nonMemberSubfamily a = 𝒜.nonMemberSubfamily a := by
  ext
  simp

/--
lemma `memberSubfamily_image_insert` / 引理 `memberSubfamily_image_insert`

English:
lemma memberSubfamily_image_insert
  given: (h𝒜 : forall s in 𝒜, a ∉ s)
  proof: by
  ext s
  simp only [mem_memberSubfamily, mem_image]
  refine ⟨?_, fun hs => ⟨⟨s, hs, rfl⟩, h𝒜 _ hs⟩⟩
  rintro ⟨⟨t, ht, hts⟩, hs⟩
  rwa [← insert_erase_invOn.2.injOn (h𝒜 _ ht) hs hts]

中文:
引理 memberSubfamily_image_insert
  条件: (h𝒜 : 对任意 s in 𝒜, a ∉ s)
  证明: by
  ext s
  simp only [mem_memberSubfamily, mem_image]
  refine ⟨?_, fun hs => ⟨⟨s, hs, rfl⟩, h𝒜 _ hs⟩⟩
  rintro ⟨⟨t, ht, hts⟩, hs⟩
  rwa [← insert_erase_invOn.2.injOn (h𝒜 _ ht) hs hts]

Depends on / 依赖: insert_erase_invOn, mem_image, mem_memberSubfamily
-/
lemma memberSubfamily_image_insert (h𝒜 : forall s in 𝒜, a ∉ s) :
    (𝒜.image <| insert a).memberSubfamily a = 𝒜 := by
  ext s
  simp only [mem_memberSubfamily, mem_image]
  refine ⟨?_, fun hs => ⟨⟨s, hs, rfl⟩, h𝒜 _ hs⟩⟩
  rintro ⟨⟨t, ht, hts⟩, hs⟩
  rwa [← insert_erase_invOn.2.injOn (h𝒜 _ ht) hs hts]

/--
lemma `nonMemberSubfamily_image_insert` / 引理 `nonMemberSubfamily_image_insert`

English:
lemma nonMemberSubfamily_image_insert
  statement: (𝒜.image <| insert a).nonMemberSubfamily a = ∅
  proof: by
  simp [eq_empty_iff_forall_notMem]

中文:
引理 nonMemberSubfamily_image_insert
  结论: (𝒜.像 <| insert a).nonMemberSubfamily a = ∅
  证明: by
  simp [eq_empty_iff_forall_notMem]
-/
@[simp] lemma nonMemberSubfamily_image_insert : (𝒜.image <| insert a).nonMemberSubfamily a = ∅ := by
  simp [eq_empty_iff_forall_notMem]

/--
lemma `memberSubfamily_image_erase` / 引理 `memberSubfamily_image_erase`

English:
lemma memberSubfamily_image_erase
  statement: (𝒜.image (erase · a)).memberSubfamily a = ∅
  proof: by
  simp [eq_empty_iff_forall_notMem,
    (ne_of_mem_of_not_mem' (mem_insert_self _ _) (notMem_erase _ _)).symm]

中文:
引理 memberSubfamily_image_erase
  结论: (𝒜.像 (erase · a)).memberSubfamily a = ∅
  证明: by
  simp [eq_empty_iff_forall_notMem,
    (ne_of_mem_of_not_mem' (mem_insert_self _ _) (notMem_erase _ _)).symm]
-/
@[simp] lemma memberSubfamily_image_erase : (𝒜.image (erase · a)).memberSubfamily a = ∅ := by
  simp [eq_empty_iff_forall_notMem,
    (ne_of_mem_of_not_mem' (mem_insert_self _ _) (notMem_erase _ _)).symm]

/--
lemma `image_insert_memberSubfamily` / 引理 `image_insert_memberSubfamily`

English:
lemma image_insert_memberSubfamily
  given: (𝒜 : Finset (Finset α)) (a : α)
  proof: by
  ext s
  simp only [mem_memberSubfamily, mem_image, mem_filter]
  refine ⟨?_, fun ⟨hs, ha⟩ => ⟨erase s a, ⟨?_, notMem_erase _ _⟩, insert_erase ha⟩⟩
  · rintro ⟨s, ⟨hs, -⟩, rfl⟩
    exact ⟨hs, mem_insert_self _ _⟩
  · rwa [insert_erase ha]

中文:
引理 image_insert_memberSubfamily
  条件: (𝒜 : 有限集 (有限集 α)) (a : α)
  证明: by
  ext s
  simp only [mem_memberSubfamily, mem_image, mem_filter]
  refine ⟨?_, fun ⟨hs, ha⟩ => ⟨erase s a, ⟨?_, notMem_erase _ _⟩, insert_erase ha⟩⟩
  · rintro ⟨s, ⟨hs, -⟩, rfl⟩
    exact ⟨hs, mem_insert_self _ _⟩
  · rwa [insert_erase ha]

Depends on / 依赖: insert_erase, mem_filter, mem_image, mem_insert_self, mem_memberSubfamily, notMem_erase
-/
lemma image_insert_memberSubfamily (𝒜 : Finset (Finset α)) (a : α) :
    (𝒜.memberSubfamily a).image (insert a) = {s in 𝒜 | a in s} := by
  ext s
  simp only [mem_memberSubfamily, mem_image, mem_filter]
  refine ⟨?_, fun ⟨hs, ha⟩ => ⟨erase s a, ⟨?_, notMem_erase _ _⟩, insert_erase ha⟩⟩
  · rintro ⟨s, ⟨hs, -⟩, rfl⟩
    exact ⟨hs, mem_insert_self _ _⟩
  · rwa [insert_erase ha]

/-- Induction principle for finset families. To prove a statement for every finset family,
it suffices to prove it for
* the empty finset family.
* the finset family which only contains the empty finset.
* `ℬ ∪ {s ∪ {a} | s ∈ 𝒞}` assuming the property for `ℬ` and `𝒞`, where `a` is an element of the
  ground type and `𝒜` and `ℬ` are families of finsets not containing `a`.
  Note that instead of giving `ℬ` and `𝒞`, the `subfamily` case gives you
  `𝒜 = ℬ ∪ {s ∪ {a} | s ∈ 𝒞}`, so that `ℬ = 𝒜.nonMemberSubfamily` and `𝒞 = 𝒜.memberSubfamily`.

This is a way of formalising induction on `n` where `𝒜` is a finset family on `n` elements.

See also `Finset.family_induction_on.` -/
@[elab_as_elim]
/--
lemma `memberFamily_induction_on` / 引理 `memberFamily_induction_on`

English:
lemma memberFamily_induction_on
  statement: {p : Finset (Finset α) -> Prop}
  proof: by
  set u := 𝒜.sup id
  have hu : forall s in 𝒜, s subseteq u := fun s => le_sup (f := id)
  clear_value u
  induction u using Finset.induction generalizing 𝒜 with
  | empty =>
    simp_rw [subset_empty] at hu
    rw [← subset_singleton_iff']; rw [subset_singleton_iff] at hu
    obtain rfl | rfl := hu <;> assumption
  | insert a u _ ih =>
    refine subfamily a (ih _ ?_) (ih _ ?_)
    · simp only [mem_nonMemberSubfamily, and_imp]
exact fun s hs has => (subset_insert_iff_of_notMem has).1 hu _ hs
    · simp only [mem_memberSubfamily, and_imp]
exact fun s hs ha => (insert_subset_insert_iff ha).1 hu _ hs

中文:
引理 memberFamily_induction_on
  结论: {p : 有限集 (有限集 α) -> 命题}
  证明: by
  set u := 𝒜.sup id
  have hu : forall s in 𝒜, s subseteq u := fun s => le_sup (f := id)
  clear_value u
  induction u using Finset.induction generalizing 𝒜 with
  | empty =>
    simp_rw [subset_empty] at hu
    rw [← subset_singleton_iff']; rw [subset_singleton_iff] at hu
    obtain rfl | rfl := hu <;> assumption
  | insert a u _ ih =>
    refine subfamily a (ih _ ?_) (ih _ ?_)
    · simp only [mem_nonMemberSubfamily, and_imp]
exact fun s hs has => (subset_insert_iff_of_notMem has).1 hu _ hs
    · simp only [mem_memberSubfamily, and_imp]
exact fun s hs ha => (insert_subset_insert_iff ha).1 hu _ hs

Depends on / 依赖: Finset, Finset.induction, and_imp, clear_value, generalizing, insert, le_sup, mem_memberSubfamil, mem_nonMemberSubfamily, simp_rw, subfamily, subset_empty, subset_insert_iff_of_notMem, subset_singleton_iff, subseteq
-/
lemma memberFamily_induction_on {p : Finset (Finset α) -> Prop}
    (𝒜 : Finset (Finset α)) (empty : p ∅) (singleton_empty : p {∅})
    (subfamily : forall (a : α) ⦃𝒜 : Finset (Finset α)⦄,
      p (𝒜.nonMemberSubfamily a) -> p (𝒜.memberSubfamily a) -> p 𝒜) : p 𝒜 := by
  set u := 𝒜.sup id
  have hu : forall s in 𝒜, s subseteq u := fun s => le_sup (f := id)
  clear_value u
  induction u using Finset.induction generalizing 𝒜 with
  | empty =>
    simp_rw [subset_empty] at hu
    rw [← subset_singleton_iff']; rw [subset_singleton_iff] at hu
    obtain rfl | rfl := hu <;> assumption
  | insert a u _ ih =>
    refine subfamily a (ih _ ?_) (ih _ ?_)
    · simp only [mem_nonMemberSubfamily, and_imp]
exact fun s hs has => (subset_insert_iff_of_notMem has).1 hu _ hs
    · simp only [mem_memberSubfamily, and_imp]
exact fun s hs ha => (insert_subset_insert_iff ha).1 hu _ hs

/-- Induction principle for finset families. To prove a statement for every finset family,
it suffices to prove it for
* the empty finset family.
* the finset family which only contains the empty finset.
* `{s ∪ {a} | s ∈ 𝒜}` assuming the property for `𝒜` a family of finsets not containing `a`.
* `ℬ ∪ 𝒞` assuming the property for `ℬ` and `𝒞`, where `a` is an element of the ground type and
  `ℬ` is a family of finsets not containing `a` and `𝒞` a family of finsets containing `a`.
  Note that instead of giving `ℬ` and `𝒞`, the `subfamily` case gives you `𝒜 = ℬ ∪ 𝒞`, so that
  `ℬ = {s ∈ 𝒜 | a ∉ s}` and `𝒞 = {s ∈ 𝒜 | a ∈ s}`.

This is a way of formalising induction on `n` where `𝒜` is a finset family on `n` elements.

See also `Finset.memberFamily_induction_on.` -/
@[elab_as_elim]
/--
lemma `family_induction_on` / 引理 `family_induction_on`

English:
lemma family_induction_on
  statement: {p : Finset (Finset α) -> Prop}
  proof: by
  refine memberFamily_induction_on 𝒜 empty singleton_empty fun a 𝒜 h𝒜₀ h𝒜₁ => subfamily a h𝒜₀ ?_
  rw [← image_insert_memberSubfamily]
  exact image_insert _ (by simp) h𝒜₁

中文:
引理 family_induction_on
  结论: {p : 有限集 (有限集 α) -> 命题}
  证明: by
  refine memberFamily_induction_on 𝒜 empty singleton_empty fun a 𝒜 h𝒜₀ h𝒜₁ => subfamily a h𝒜₀ ?_
  rw [← image_insert_memberSubfamily]
  exact image_insert _ (by simp) h𝒜₁
-/
protected lemma family_induction_on {p : Finset (Finset α) -> Prop}
    (𝒜 : Finset (Finset α)) (empty : p ∅) (singleton_empty : p {∅})
    (image_insert : forall (a : α) ⦃𝒜 : Finset (Finset α)⦄,
      (forall s in 𝒜, a ∉ s) -> p 𝒜 -> p (𝒜.image <| insert a))
    (subfamily : forall (a : α) ⦃𝒜 : Finset (Finset α)⦄,
      p {s in 𝒜 | a ∉ s} -> p {s in 𝒜 | a in s} -> p 𝒜) : p 𝒜 := by
  refine memberFamily_induction_on 𝒜 empty singleton_empty fun a 𝒜 h𝒜₀ h𝒜₁ => subfamily a h𝒜₀ ?_
  rw [← image_insert_memberSubfamily]
  exact image_insert _ (by simp) h𝒜₁

end Finset

open Finset

-- The namespace is here to distinguish from other compressions.
namespace Down

/--
Definition of `compression` / `compression` 的定义

English:
definition compression
  signature: (a : α) (𝒜 : Finset (Finset α))
  body: {s in 𝒜 | erase s a in 𝒜}.disjUnion {s in 𝒜.image fun s => erase s a | s ∉ 𝒜}
    disjoint_left.2 fun _s h₁ h₂ => (mem_filter.1 h₂).2 (mem_filter.1 h₁).1

@[inherit_doc]
scoped[FinsetFamily] notation "𝓓 " => Down.compression

中文:
定义 compression
  签名: (a : α) (𝒜 : 有限集 (有限集 α))
  定义体: {s in 𝒜 | erase s a in 𝒜}.disjUnion {s in 𝒜.image fun s => erase s a | s ∉ 𝒜}
    disjoint_left.2 fun _s h₁ h₂ => (mem_filter.1 h₂).2 (mem_filter.1 h₁).1

@[inherit_doc]
scoped[FinsetFamily] notation "𝓓 " => Down.compression

Depends on / 依赖: disjUnion, disjoint_left, mem_filter
-/
def compression (a : α) (𝒜 : Finset (Finset α)) : Finset (Finset α) :=
{s in 𝒜 | erase s a in 𝒜}.disjUnion {s in 𝒜.image fun s => erase s a | s ∉ 𝒜}
    disjoint_left.2 fun _s h₁ h₂ => (mem_filter.1 h₂).2 (mem_filter.1 h₁).1

@[inherit_doc]
scoped[FinsetFamily] notation "𝓓 " => Down.compression

open FinsetFamily

/--
theorem `mem_compression` / 定理 `mem_compression`

English:
theorem mem_compression
  statement: s in 𝓓 a 𝒜 ↔ s in 𝒜 ∧ s.erase a in 𝒜 ∨ s ∉ 𝒜 ∧ insert a s in 𝒜
  proof: by
  simp_rw [compression, mem_disjUnion, mem_filter, mem_image, and_comm (a := s ∉ 𝒜)]
  refine
    or_congr_right
      (and_congr_left fun hs =>
⟨?_, fun h => ⟨_, h, erase_insert insert_ne_self.1 ne_of_mem_of_not_mem h hs⟩⟩)
  rintro ⟨t, ht, rfl⟩
  rwa [insert_erase (erase_ne_self.1 (ne_of_mem_of_not_mem ht hs).symm)]

中文:
定理 mem_compression
  结论: s in 𝓓 a 𝒜 ↔ s in 𝒜 ∧ s.erase a in 𝒜 ∨ s ∉ 𝒜 ∧ insert a s in 𝒜
  证明: by
  simp_rw [compression, mem_disjUnion, mem_filter, mem_image, and_comm (a := s ∉ 𝒜)]
  refine
    or_congr_right
      (and_congr_left fun hs =>
⟨?_, fun h => ⟨_, h, erase_insert insert_ne_self.1 ne_of_mem_of_not_mem h hs⟩⟩)
  rintro ⟨t, ht, rfl⟩
  rwa [insert_erase (erase_ne_self.1 (ne_of_mem_of_not_mem ht hs).symm)]

Depends on / 依赖: and_comm, and_congr_left, compression, erase_insert, erase_ne_self, insert_erase, insert_ne_self, mem_disjUnion, mem_filter, mem_image, ne_of_mem_of_not_mem, or_congr_right, simp_rw
-/
theorem mem_compression : s in 𝓓 a 𝒜 ↔ s in 𝒜 ∧ s.erase a in 𝒜 ∨ s ∉ 𝒜 ∧ insert a s in 𝒜 := by
  simp_rw [compression, mem_disjUnion, mem_filter, mem_image, and_comm (a := s ∉ 𝒜)]
  refine
    or_congr_right
      (and_congr_left fun hs =>
⟨?_, fun h => ⟨_, h, erase_insert insert_ne_self.1 ne_of_mem_of_not_mem h hs⟩⟩)
  rintro ⟨t, ht, rfl⟩
  rwa [insert_erase (erase_ne_self.1 (ne_of_mem_of_not_mem ht hs).symm)]

/--
theorem `erase_mem_compression` / 定理 `erase_mem_compression`

English:
theorem erase_mem_compression
  given: (hs : s in 𝒜)
  statement: s.erase a in 𝓓 a 𝒜
  proof: by
  simp_rw [mem_compression, erase_idem, and_self_iff]
  refine (em _).imp_right fun h => ⟨h, ?_⟩
  rwa [insert_erase (erase_ne_self.1 (ne_of_mem_of_not_mem hs h).symm)]

中文:
定理 erase_mem_compression
  条件: (hs : s in 𝒜)
  结论: s.erase a in 𝓓 a 𝒜
  证明: by
  simp_rw [mem_compression, erase_idem, and_self_iff]
  refine (em _).imp_right fun h => ⟨h, ?_⟩
  rwa [insert_erase (erase_ne_self.1 (ne_of_mem_of_not_mem hs h).symm)]

Depends on / 依赖: and_self_iff, erase_idem, erase_ne_self, imp_right, insert_erase, mem_compression, ne_of_mem_of_not_mem, simp_rw
-/
theorem erase_mem_compression (hs : s in 𝒜) : s.erase a in 𝓓 a 𝒜 := by
  simp_rw [mem_compression, erase_idem, and_self_iff]
  refine (em _).imp_right fun h => ⟨h, ?_⟩
  rwa [insert_erase (erase_ne_self.1 (ne_of_mem_of_not_mem hs h).symm)]

-- This is a special case of `erase_mem_compression` once we have `compression_idem`.
/--
theorem `erase_mem_compression_of_mem_compression` / 定理 `erase_mem_compression_of_mem_compression`

English:
theorem erase_mem_compression_of_mem_compression
  statement: s in 𝓓 a 𝒜 -> s.erase a in 𝓓 a 𝒜
  proof: by
  simp_rw [mem_compression, erase_idem]
  refine Or.imp (fun h => ⟨h.2, h.2⟩) fun h => ?_
  rwa [erase_eq_of_notMem (insert_ne_self.1 <| ne_of_mem_of_not_mem h.2 h.1)]

中文:
定理 erase_mem_compression_of_mem_compression
  结论: s in 𝓓 a 𝒜 -> s.erase a in 𝓓 a 𝒜
  证明: by
  simp_rw [mem_compression, erase_idem]
  refine Or.imp (fun h => ⟨h.2, h.2⟩) fun h => ?_
  rwa [erase_eq_of_notMem (insert_ne_self.1 <| ne_of_mem_of_not_mem h.2 h.1)]

Depends on / 依赖: Or.imp, erase_eq_of_notMem, erase_idem, insert_ne_self, mem_compression, ne_of_mem_of_not_mem, simp_rw
-/
theorem erase_mem_compression_of_mem_compression : s in 𝓓 a 𝒜 -> s.erase a in 𝓓 a 𝒜 := by
  simp_rw [mem_compression, erase_idem]
  refine Or.imp (fun h => ⟨h.2, h.2⟩) fun h => ?_
  rwa [erase_eq_of_notMem (insert_ne_self.1 <| ne_of_mem_of_not_mem h.2 h.1)]

/--
theorem `mem_compression_of_insert_mem_compression` / 定理 `mem_compression_of_insert_mem_compression`

English:
theorem mem_compression_of_insert_mem_compression
  given: (h : insert a s in 𝓓 a 𝒜)
  statement: s in 𝓓 a 𝒜
  proof: by
  by_cases ha : a in s
  · rwa [insert_eq_of_mem ha] at h
  · rw [← erase_insert ha]
    exact erase_mem_compression_of_mem_compression h

中文:
定理 mem_compression_of_insert_mem_compression
  条件: (h : insert a s in 𝓓 a 𝒜)
  结论: s in 𝓓 a 𝒜
  证明: by
  by_cases ha : a in s
  · rwa [insert_eq_of_mem ha] at h
  · rw [← erase_insert ha]
    exact erase_mem_compression_of_mem_compression h

Depends on / 依赖: erase_insert, erase_mem_compression_of_mem_compression, insert_eq_of_mem
-/
theorem mem_compression_of_insert_mem_compression (h : insert a s in 𝓓 a 𝒜) : s in 𝓓 a 𝒜 := by
  by_cases ha : a in s
  · rwa [insert_eq_of_mem ha] at h
  · rw [← erase_insert ha]
    exact erase_mem_compression_of_mem_compression h

/-- Down-compressing a family is idempotent. -/
@[simp]
/--
theorem `compression_idem` / 定理 `compression_idem`

English:
theorem compression_idem
  given: (a : α) (𝒜 : Finset (Finset α))
  statement: 𝓓 a (𝓓 a 𝒜) = 𝓓 a 𝒜
  proof: by
  ext s
  refine mem_compression.trans ⟨?_, fun h => Or.inl ⟨h, erase_mem_compression_of_mem_compression h⟩⟩
  rintro (h | h)
  · exact h.1
  · cases h.1 (mem_compression_of_insert_mem_compression h.2)

中文:
定理 compression_idem
  条件: (a : α) (𝒜 : 有限集 (有限集 α))
  结论: 𝓓 a (𝓓 a 𝒜) = 𝓓 a 𝒜
  证明: by
  ext s
  refine mem_compression.trans ⟨?_, fun h => Or.inl ⟨h, erase_mem_compression_of_mem_compression h⟩⟩
  rintro (h | h)
  · exact h.1
  · cases h.1 (mem_compression_of_insert_mem_compression h.2)

Depends on / 依赖: Or.inl, erase_mem_compression_of_mem_compression, mem_compression, mem_compression.trans, mem_compression_of_insert_mem_compression
-/
theorem compression_idem (a : α) (𝒜 : Finset (Finset α)) : 𝓓 a (𝓓 a 𝒜) = 𝓓 a 𝒜 := by
  ext s
  refine mem_compression.trans ⟨?_, fun h => Or.inl ⟨h, erase_mem_compression_of_mem_compression h⟩⟩
  rintro (h | h)
  · exact h.1
  · cases h.1 (mem_compression_of_insert_mem_compression h.2)

/-- Down-compressing a family doesn't change its size. -/
@[simp]
/--
theorem `card_compression` / 定理 `card_compression`

English:
theorem card_compression
  given: (a : α) (𝒜 : Finset (Finset α))
  statement: #(𝓓 a 𝒜) = #𝒜
  proof: by
  rw [compression]; rw [card_disjUnion]; rw [filter_image]; rw [card_image_of_injOn ((erase_injOn' _).mono fun s hs => _)]; rw [← card_union_of_disjoint]
  · conv_rhs => rw [← filter_union_filter_not_eq (fun s => (erase s a in 𝒜)) 𝒜]
  · exact disjoint_filter_filter_not 𝒜 𝒜 (fun s => (erase s a in 𝒜))
  intro s hs
  rw [mem_coe]; rw [mem_filter] at hs
  exact not_imp_comm.1 erase_eq_of_notMem (ne_of_mem_of_not_mem hs.1 hs.2).symm

中文:
定理 card_compression
  条件: (a : α) (𝒜 : 有限集 (有限集 α))
  结论: #(𝓓 a 𝒜) = #𝒜
  证明: by
  rw [compression]; rw [card_disjUnion]; rw [filter_image]; rw [card_image_of_injOn ((erase_injOn' _).mono fun s hs => _)]; rw [← card_union_of_disjoint]
  · conv_rhs => rw [← filter_union_filter_not_eq (fun s => (erase s a in 𝒜)) 𝒜]
  · exact disjoint_filter_filter_not 𝒜 𝒜 (fun s => (erase s a in 𝒜))
  intro s hs
  rw [mem_coe]; rw [mem_filter] at hs
  exact not_imp_comm.1 erase_eq_of_notMem (ne_of_mem_of_not_mem hs.1 hs.2).symm

Depends on / 依赖: card_disjUnion, card_image_of_injOn, card_union_of_disjoint, compression, conv_rhs, disjoint_filter_filter_not, erase_eq_of_notMem, erase_injOn, filter_image, filter_union_filter_not_eq, mem_coe, mem_filter, ne_of_mem_of_not_mem, not_imp_comm
-/
theorem card_compression (a : α) (𝒜 : Finset (Finset α)) : #(𝓓 a 𝒜) = #𝒜 := by
  rw [compression]; rw [card_disjUnion]; rw [filter_image]; rw [card_image_of_injOn ((erase_injOn' _).mono fun s hs => _)]; rw [← card_union_of_disjoint]
  · conv_rhs => rw [← filter_union_filter_not_eq (fun s => (erase s a in 𝒜)) 𝒜]
  · exact disjoint_filter_filter_not 𝒜 𝒜 (fun s => (erase s a in 𝒜))
  intro s hs
  rw [mem_coe]; rw [mem_filter] at hs
  exact not_imp_comm.1 erase_eq_of_notMem (ne_of_mem_of_not_mem hs.1 hs.2).symm

end Down
