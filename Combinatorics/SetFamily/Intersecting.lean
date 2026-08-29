/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Data.Fintype.Card
public import Mathlib.Order.UpperLower.Basic

/-!
# Intersecting families

This file defines intersecting families and proves their basic properties.

## Main declarations

* `Set.Intersecting`: Predicate for a set of elements in a generalized Boolean algebra to be an
  intersecting family.
* `Set.Intersecting.card_le`: An intersecting family can only take up to half the elements, because
  `a` and `aᶜ` cannot simultaneously be in it.
* `Set.Intersecting.is_max_iff_card_eq`: Any maximal intersecting family takes up half the elements.
* `Set.IsIntersectingOf`: Predicate stating that a family `𝒜` of finsets is `L`-intersecting, i.e.,
  meaning the intersection size of every pair of distinct members of `𝒜` belongs to `L ⊆ ℕ`.

## References

* [D. J. Kleitman, *Families of non-disjoint subsets*][kleitman1966]
-/

@[expose] public section

assert_not_exists Monoid

open Finset

namespace Set

section SemilatticeInf

variable {α : Type*}

variable [SemilatticeInf α] [OrderBot α] {s t : Set α} {a b c : α}

/--
Definition of `Intersecting` / `Intersecting` 的定义

English:
definition Intersecting
  signature: (s : Set α)
  body: forall ⦃a⦄, a in s -> forall ⦃b⦄, b in s -> ¬Disjoint a b

@[gcongr, mono]

中文:
定义 Intersecting
  签名: (s : Set α)
  定义体: forall ⦃a⦄, a in s -> forall ⦃b⦄, b in s -> ¬Disjoint a b

@[gcongr, mono]

Depends on / 依赖: Disjoint
-/
def Intersecting (s : Set α) : Prop :=
  forall ⦃a⦄, a in s -> forall ⦃b⦄, b in s -> ¬Disjoint a b

@[gcongr, mono]
/--
theorem `Intersecting.mono` / 定理 `Intersecting.mono`

English:
theorem Intersecting.mono
  given: (h : t subseteq s) (hs : s.Intersecting)
  statement: t.Intersecting
  proof: fun _a ha _b hb =>
  hs (h ha) (h hb)

中文:
定理 Intersecting.mono
  条件: (h : t subseteq s) (hs : s.整数ersecting)
  结论: t.整数ersecting
  证明: fun _a ha _b hb =>
  hs (h ha) (h hb)
-/
theorem Intersecting.mono (h : t subseteq s) (hs : s.Intersecting) : t.Intersecting := fun _a ha _b hb =>
  hs (h ha) (h hb)

/--
theorem `Intersecting.bot_notMem` / 定理 `Intersecting.bot_notMem`

English:
theorem Intersecting.bot_notMem
  given: (hs : s.Intersecting)
  statement: ⊥ ∉ s
  proof: fun h => hs h h disjoint_bot_left

中文:
定理 Intersecting.bot_notMem
  条件: (hs : s.整数ersecting)
  结论: ⊥ ∉ s
  证明: fun h => hs h h disjoint_bot_left

Depends on / 依赖: disjoint_bot_left
-/
theorem Intersecting.bot_notMem (hs : s.Intersecting) : ⊥ ∉ s := fun h => hs h h disjoint_bot_left

/--
theorem `Intersecting.ne_bot` / 定理 `Intersecting.ne_bot`

English:
theorem Intersecting.ne_bot
  given: (hs : s.Intersecting) (ha : a in s)
  statement: a != ⊥
  proof: ne_of_mem_of_not_mem ha hs.bot_notMem

中文:
定理 Intersecting.ne_bot
  条件: (hs : s.整数ersecting) (ha : a in s)
  结论: a != ⊥
  证明: ne_of_mem_of_not_mem ha hs.bot_notMem

Depends on / 依赖: bot_notMem, hs.bot_notMem, ne_of_mem_of_not_mem
-/
theorem Intersecting.ne_bot (hs : s.Intersecting) (ha : a in s) : a != ⊥ :=
  ne_of_mem_of_not_mem ha hs.bot_notMem

/--
theorem `intersecting_empty` / 定理 `intersecting_empty`

English:
theorem intersecting_empty
  statement: (∅ : Set α).Intersecting
  proof: fun _ => False.elim

@[simp]

中文:
定理 intersecting_empty
  结论: (∅ : Set α).整数ersecting
  证明: fun _ => False.elim

@[simp]

Depends on / 依赖: False.elim
-/
theorem intersecting_empty : (∅ : Set α).Intersecting := fun _ => False.elim

@[simp]
/--
theorem `intersecting_singleton` / 定理 `intersecting_singleton`

English:
theorem intersecting_singleton
  statement: ({a} : Set α).Intersecting ↔ a != ⊥
  proof: by simp [Intersecting]

中文:
定理 intersecting_singleton
  结论: ({a} : Set α).整数ersecting ↔ a != ⊥
  证明: by simp [Intersecting]

Depends on / 依赖: Intersecting
-/
theorem intersecting_singleton : ({a} : Set α).Intersecting ↔ a != ⊥ := by simp [Intersecting]

/--
theorem `Intersecting.insert` / 定理 `Intersecting.insert`

English:
theorem Intersecting.insert
  statement: (hs : s.Intersecting) (ha : a != ⊥)
  proof: by
  rintro b (rfl | hb) c (rfl | hc)
  · rwa [disjoint_self]
  · exact h _ hc
  · exact fun H => h _ hb H.symm
  · exact hs hb hc

中文:
定理 Intersecting.insert
  结论: (hs : s.整数ersecting) (ha : a != ⊥)
  证明: by
  rintro b (rfl | hb) c (rfl | hc)
  · rwa [disjoint_self]
  · exact h _ hc
  · exact fun H => h _ hb H.symm
  · exact hs hb hc
-/
protected theorem Intersecting.insert (hs : s.Intersecting) (ha : a != ⊥)
    (h : forall b in s, ¬Disjoint a b) : (insert a s).Intersecting := by
  rintro b (rfl | hb) c (rfl | hc)
  · rwa [disjoint_self]
  · exact h _ hc
  · exact fun H => h _ hb H.symm
  · exact hs hb hc

/--
theorem `intersecting_insert` / 定理 `intersecting_insert`

English:
theorem intersecting_insert
  proof: ⟨fun h =>
⟨h.mono subset_insert _ _, h.ne_bot mem_insert _ _, fun _b hb =>
h (mem_insert _ _) mem_insert_of_mem _ hb⟩,
    fun h => h.1.insert h.2.1 h.2.2⟩

中文:
定理 intersecting_insert
  证明: ⟨fun h =>
⟨h.mono subset_insert _ _, h.ne_bot mem_insert _ _, fun _b hb =>
h (mem_insert _ _) mem_insert_of_mem _ hb⟩,
    fun h => h.1.insert h.2.1 h.2.2⟩

Depends on / 依赖: h.mono, h.ne_bot, insert, mem_insert, mem_insert_of_mem, ne_bot, subset_insert
-/
theorem intersecting_insert :
    (insert a s).Intersecting ↔ s.Intersecting ∧ a != ⊥ ∧ forall b in s, ¬Disjoint a b :=
  ⟨fun h =>
⟨h.mono subset_insert _ _, h.ne_bot mem_insert _ _, fun _b hb =>
h (mem_insert _ _) mem_insert_of_mem _ hb⟩,
    fun h => h.1.insert h.2.1 h.2.2⟩

/--
theorem `intersecting_iff_pairwise_not_disjoint` / 定理 `intersecting_iff_pairwise_not_disjoint`

English:
theorem intersecting_iff_pairwise_not_disjoint
  proof: by
  refine ⟨fun h => ⟨fun a ha b hb _ => h ha hb, ?_⟩, fun h a ha b hb hab => ?_⟩
  · rintro rfl
    exact intersecting_singleton.1 h rfl
  have := h.1.eq ha hb (Classical.not_not.2 hab)
  rw [this]; rw [disjoint_self] at hab
  rw [hab] at hb
  exact
    h.2
      (eq_singleton_iff_unique_mem.2
   

中文:
定理 intersecting_iff_pairwise_not_disjoint
  证明: by
  refine ⟨fun h => ⟨fun a ha b hb _ => h ha hb, ?_⟩, fun h a ha b hb hab => ?_⟩
  · rintro rfl
    exact intersecting_singleton.1 h rfl
  have := h.1.eq ha hb (Classical.not_not.2 hab)
  rw [this]; rw [disjoint_self] at hab
  rw [hab] at hb
  exact
    h.2
      (eq_singleton_iff_unique_mem.2
   

Depends on / 依赖: Classical, Classical.not_not, H.symm, disjoint_bot_left, disjoint_self, eq_singleton_iff_unique_mem, intersecting_singleton, not_ne_iff, not_not
-/
theorem intersecting_iff_pairwise_not_disjoint :
    s.Intersecting ↔ (s.Pairwise fun a b => ¬Disjoint a b) ∧ s != {⊥} := by
  refine ⟨fun h => ⟨fun a ha b hb _ => h ha hb, ?_⟩, fun h a ha b hb hab => ?_⟩
  · rintro rfl
    exact intersecting_singleton.1 h rfl
  have := h.1.eq ha hb (Classical.not_not.2 hab)
  rw [this]; rw [disjoint_self] at hab
  rw [hab] at hb
  exact
    h.2
      (eq_singleton_iff_unique_mem.2
        ⟨hb, fun c hc => not_ne_iff.1 fun H => h.1 hb hc H.symm disjoint_bot_left⟩)

/--
theorem `Subsingleton.intersecting` / 定理 `Subsingleton.intersecting`

English:
theorem Subsingleton.intersecting
  given: (hs : s.Subsingleton)
  statement: s.Intersecting ↔ s != {⊥}
  proof: intersecting_iff_pairwise_not_disjoint.trans and_iff_right hs.pairwise _

中文:
定理 Subsingleton.intersecting
  条件: (hs : s.Subsingleton)
  结论: s.整数ersecting ↔ s != {⊥}
  证明: intersecting_iff_pairwise_not_disjoint.trans and_iff_right hs.pairwise _
-/
protected theorem Subsingleton.intersecting (hs : s.Subsingleton) : s.Intersecting ↔ s != {⊥} :=
intersecting_iff_pairwise_not_disjoint.trans and_iff_right hs.pairwise _

/--
theorem `intersecting_iff_eq_empty_of_subsingleton` / 定理 `intersecting_iff_eq_empty_of_subsingleton`

English:
theorem intersecting_iff_eq_empty_of_subsingleton
  given: [Subsingleton α] (s : Set α)
  proof: by
  refine
    subsingleton_of_subsingleton.intersecting.trans
      ⟨not_imp_comm.2 fun h => subsingleton_of_subsingleton.eq_singleton_of_mem ?_, ?_⟩
  · obtain ⟨a, ha⟩ := nonempty_iff_ne_empty.2 h
    rwa [Subsingleton.elim ⊥ a]
  · rintro rfl
    exact (Set.singleton_nonempty _).ne_empty.symm

中文:
定理 intersecting_iff_eq_empty_of_subsingleton
  条件: [Subsingleton α] (s : Set α)
  证明: by
  refine
    subsingleton_of_subsingleton.intersecting.trans
      ⟨not_imp_comm.2 fun h => subsingleton_of_subsingleton.eq_singleton_of_mem ?_, ?_⟩
  · obtain ⟨a, ha⟩ := nonempty_iff_ne_empty.2 h
    rwa [Subsingleton.elim ⊥ a]
  · rintro rfl
    exact (Set.singleton_nonempty _).ne_empty.symm

Depends on / 依赖: Set.singleton_nonempty, Subsingleton, Subsingleton.elim, eq_singleton_of_mem, intersecting, ne_empty, ne_empty.symm, nonempty_iff_ne_empty, not_imp_comm, singleton_nonempty, subsingleton_of_subsingleton, subsingleton_of_subsingleton.eq_singleton_of_mem, subsingleton_of_subsingleton.intersecting.trans
-/
theorem intersecting_iff_eq_empty_of_subsingleton [Subsingleton α] (s : Set α) :
    s.Intersecting ↔ s = ∅ := by
  refine
    subsingleton_of_subsingleton.intersecting.trans
      ⟨not_imp_comm.2 fun h => subsingleton_of_subsingleton.eq_singleton_of_mem ?_, ?_⟩
  · obtain ⟨a, ha⟩ := nonempty_iff_ne_empty.2 h
    rwa [Subsingleton.elim ⊥ a]
  · rintro rfl
    exact (Set.singleton_nonempty _).ne_empty.symm

/--
theorem `Intersecting.isUpperSet` / 定理 `Intersecting.isUpperSet`

English:
theorem Intersecting.isUpperSet
  statement: (hs : s.Intersecting)
  proof: by
  rintro a b hab ha
  rw [h (Insert.insert b s) _ (subset_insert _ _)]
  · exact mem_insert _ _
  exact
hs.insert (mt (eq_bot_mono hab) <| hs.ne_bot ha) fun c hc hbc => hs ha hc hbc.mono_left hab

中文:
定理 Intersecting.isUpperSet
  结论: (hs : s.整数ersecting)
  证明: by
  rintro a b hab ha
  rw [h (Insert.insert b s) _ (subset_insert _ _)]
  · exact mem_insert _ _
  exact
hs.insert (mt (eq_bot_mono hab) <| hs.ne_bot ha) fun c hc hbc => hs ha hc hbc.mono_left hab
-/
protected theorem Intersecting.isUpperSet (hs : s.Intersecting)
    (h : forall t : Set α, t.Intersecting -> s subseteq t -> s = t) : IsUpperSet s := by
  rintro a b hab ha
  rw [h (Insert.insert b s) _ (subset_insert _ _)]
  · exact mem_insert _ _
  exact
hs.insert (mt (eq_bot_mono hab) <| hs.ne_bot ha) fun c hc hbc => hs ha hc hbc.mono_left hab

/--
theorem `Intersecting.isUpperSet'` / 定理 `Intersecting.isUpperSet'`

English:
theorem Intersecting.isUpperSet'
  statement: {s : Finset α} (hs : (s : Set α).Intersecting)
  proof: by
  classical
    rintro a b hab ha
    rw [h (Insert.insert b s) _ (Finset.subset_insert _ _)]
    · exact mem_insert_self _ _
    rw [coe_insert]
    exact
hs.insert (mt (eq_bot_mono hab) <| hs.ne_bot ha) fun c hc hbc => hs ha hc hbc.mono_left hab

中文:
定理 Intersecting.isUpperSet'
  结论: {s : Finset α} (hs : (s : Set α).整数ersecting)
  证明: by
  classical
    rintro a b hab ha
    rw [h (Insert.insert b s) _ (Finset.subset_insert _ _)]
    · exact mem_insert_self _ _
    rw [coe_insert]
    exact
hs.insert (mt (eq_bot_mono hab) <| hs.ne_bot ha) fun c hc hbc => hs ha hc hbc.mono_left hab

Depends on / 依赖: Finset, Finset.subset_insert, Insert, Insert.insert, classical, coe_insert, eq_bot_mono, hbc.mono_left, hs.insert, hs.ne_bot, insert, mem_insert_self, mono_left, ne_bot, subset_insert
-/
theorem Intersecting.isUpperSet' {s : Finset α} (hs : (s : Set α).Intersecting)
    (h : forall t : Finset α, (t : Set α).Intersecting -> s subseteq t -> s = t) : IsUpperSet (s : Set α) := by
  classical
    rintro a b hab ha
    rw [h (Insert.insert b s) _ (Finset.subset_insert _ _)]
    · exact mem_insert_self _ _
    rw [coe_insert]
    exact
hs.insert (mt (eq_bot_mono hab) <| hs.ne_bot ha) fun c hc hbc => hs ha hc hbc.mono_left hab

end SemilatticeInf

section

variable {α : Type*}

/--
theorem `Intersecting.exists_mem_set` / 定理 `Intersecting.exists_mem_set`

English:
theorem Intersecting.exists_mem_set
  statement: {𝒜 : Set (Set α)} (h𝒜 : 𝒜.Intersecting) {s t : Set α}
  proof: not_disjoint_iff.1 h𝒜 hs ht

中文:
定理 Intersecting.exists_mem_set
  结论: {𝒜 : Set (Set α)} (h𝒜 : 𝒜.整数ersecting) {s t : Set α}
  证明: not_disjoint_iff.1 h𝒜 hs ht

Depends on / 依赖: not_disjoint_iff
-/
theorem Intersecting.exists_mem_set {𝒜 : Set (Set α)} (h𝒜 : 𝒜.Intersecting) {s t : Set α}
    (hs : s in 𝒜) (ht : t in 𝒜) : exists a, a in s ∧ a in t :=
not_disjoint_iff.1 h𝒜 hs ht

/--
theorem `Intersecting.exists_mem_finset` / 定理 `Intersecting.exists_mem_finset`

English:
theorem Intersecting.exists_mem_finset
  statement: [DecidableEq α] {𝒜 : Set (Finset α)} (h𝒜 : 𝒜.Intersecting)
  proof: not_disjoint_iff.1 disjoint_coe.not.2 h𝒜 hs ht

中文:
定理 Intersecting.exists_mem_finset
  结论: [DecidableEq α] {𝒜 : Set (Finset α)} (h𝒜 : 𝒜.整数ersecting)
  证明: not_disjoint_iff.1 disjoint_coe.not.2 h𝒜 hs ht

Depends on / 依赖: disjoint_coe, disjoint_coe.not, not_disjoint_iff
-/
theorem Intersecting.exists_mem_finset [DecidableEq α] {𝒜 : Set (Finset α)} (h𝒜 : 𝒜.Intersecting)
    {s t : Finset α} (hs : s in 𝒜) (ht : t in 𝒜) : exists a, a in s ∧ a in t :=
not_disjoint_iff.1 disjoint_coe.not.2 h𝒜 hs ht

variable [BooleanAlgebra α]

/--
theorem `Intersecting.compl_notMem` / 定理 `Intersecting.compl_notMem`

English:
theorem Intersecting.compl_notMem
  given: {s : Set α} (hs : s.Intersecting) {a : α} (ha : a in s)
  proof: fun h => hs ha h disjoint_compl_right

中文:
定理 Intersecting.compl_notMem
  条件: {s : Set α} (hs : s.整数ersecting) {a : α} (ha : a in s)
  证明: fun h => hs ha h disjoint_compl_right

Depends on / 依赖: disjoint_compl_right
-/
theorem Intersecting.compl_notMem {s : Set α} (hs : s.Intersecting) {a : α} (ha : a in s) :
    aᶜ ∉ s := fun h => hs ha h disjoint_compl_right

/--
theorem `Intersecting.notMem` / 定理 `Intersecting.notMem`

English:
theorem Intersecting.notMem
  given: {s : Set α} (hs : s.Intersecting) {a : α} (ha : aᶜ in s)
  statement: a ∉ s
  proof: fun h => hs ha h disjoint_compl_left

中文:
定理 Intersecting.notMem
  条件: {s : Set α} (hs : s.整数ersecting) {a : α} (ha : aᶜ in s)
  结论: a ∉ s
  证明: fun h => hs ha h disjoint_compl_left

Depends on / 依赖: disjoint_compl_left
-/
theorem Intersecting.notMem {s : Set α} (hs : s.Intersecting) {a : α} (ha : aᶜ in s) : a ∉ s :=
  fun h => hs ha h disjoint_compl_left

/--
theorem `Intersecting.disjoint_map_compl` / 定理 `Intersecting.disjoint_map_compl`

English:
theorem Intersecting.disjoint_map_compl
  given: {s : Finset α} (hs : (s : Set α).Intersecting)
  proof: by
  rw [Finset.disjoint_left]
  rintro x hx hxc
  obtain ⟨x, hx', rfl⟩ := mem_map.mp hxc
  exact hs.compl_notMem hx' hx

中文:
定理 Intersecting.disjoint_map_compl
  条件: {s : Finset α} (hs : (s : Set α).整数ersecting)
  证明: by
  rw [Finset.disjoint_left]
  rintro x hx hxc
  obtain ⟨x, hx', rfl⟩ := mem_map.mp hxc
  exact hs.compl_notMem hx' hx

Depends on / 依赖: Finset, Finset.disjoint_left, compl_notMem, disjoint_left, hs.compl_notMem, mem_map, mem_map.mp
-/
theorem Intersecting.disjoint_map_compl {s : Finset α} (hs : (s : Set α).Intersecting) :
    Disjoint s (s.map ⟨compl, compl_injective⟩) := by
  rw [Finset.disjoint_left]
  rintro x hx hxc
  obtain ⟨x, hx', rfl⟩ := mem_map.mp hxc
  exact hs.compl_notMem hx' hx

/--
theorem `Intersecting.card_le` / 定理 `Intersecting.card_le`

English:
theorem Intersecting.card_le
  given: [Fintype α] {s : Finset α} (hs : (s : Set α).Intersecting)
  proof: by
  refine (s.disjUnion _ hs.disjoint_map_compl).card_le_univ.trans_eq' ?_
  rw [Nat.two_mul]; rw [card_disjUnion]; rw [card_map]

中文:
定理 Intersecting.card_le
  条件: [Fintype α] {s : Finset α} (hs : (s : Set α).整数ersecting)
  证明: by
  refine (s.disjUnion _ hs.disjoint_map_compl).card_le_univ.trans_eq' ?_
  rw [Nat.two_mul]; rw [card_disjUnion]; rw [card_map]

Depends on / 依赖: Nat.two_mul, card_disjUnion, card_le_univ, card_le_univ.trans_eq, card_map, disjUnion, disjoint_map_compl, hs.disjoint_map_compl, s.disjUnion, trans_eq, two_mul
-/
theorem Intersecting.card_le [Fintype α] {s : Finset α} (hs : (s : Set α).Intersecting) :
    2 * #s <= Fintype.card α := by
  refine (s.disjUnion _ hs.disjoint_map_compl).card_le_univ.trans_eq' ?_
  rw [Nat.two_mul]; rw [card_disjUnion]; rw [card_map]

variable [Nontrivial α] [Fintype α] {s : Finset α}

-- Note, this lemma is false when `α` has exactly one element and boring when `α` is empty.
/--
theorem `Intersecting.is_max_iff_card_eq` / 定理 `Intersecting.is_max_iff_card_eq`

English:
theorem Intersecting.is_max_iff_card_eq
  given: (hs : (s : Set α).Intersecting)
  proof: by
  classical
refine ⟨fun h => ?_, fun h t ht hst => Finset.eq_of_subset_of_card_le hst
      Nat.le_of_mul_le_mul_left (ht.card_le.trans_eq h.symm) Nat.two_pos⟩
    suffices s.disjUnion (s.map ⟨compl, compl_injective⟩) hs.disjoint_map_compl = Finset.univ by
      rw [Fintype.card]; rw [← this]; rw

中文:
定理 Intersecting.is_max_iff_card_eq
  条件: (hs : (s : Set α).整数ersecting)
  证明: by
  classical
refine ⟨fun h => ?_, fun h t ht hst => Finset.eq_of_subset_of_card_le hst
      Nat.le_of_mul_le_mul_left (ht.card_le.trans_eq h.symm) Nat.two_pos⟩
    suffices s.disjUnion (s.map ⟨compl, compl_injective⟩) hs.disjoint_map_compl = Finset.univ by
      rw [Fintype.card]; rw [← this]; rw

Depends on / 依赖: Embedding, Finset, Finset.eq_of_subset_of_card_le, Finset.univ, Fintype, Fintype.card, Function, Function.Embedding.coeFn_mk, Nat.le_of_mul_le_mul_left, Nat.two_mul, Nat.two_pos, card_disjUnion, card_le, card_map, classical, coeFn_mk, coe_eq_univ, coe_map, coe_union, compl_compl
-/
theorem Intersecting.is_max_iff_card_eq (hs : (s : Set α).Intersecting) :
    (forall t : Finset α, (t : Set α).Intersecting -> s subseteq t -> s = t) ↔ 2 * #s = Fintype.card α := by
  classical
refine ⟨fun h => ?_, fun h t ht hst => Finset.eq_of_subset_of_card_le hst
      Nat.le_of_mul_le_mul_left (ht.card_le.trans_eq h.symm) Nat.two_pos⟩
    suffices s.disjUnion (s.map ⟨compl, compl_injective⟩) hs.disjoint_map_compl = Finset.univ by
      rw [Fintype.card]; rw [← this]; rw [Nat.two_mul]; rw [card_disjUnion]; rw [card_map]
    rw [← coe_eq_univ]; rw [disjUnion_eq_union]; rw [coe_union]; rw [coe_map]; rw [Function.Embedding.coeFn_mk]; rw [image_eq_preimage_of_inverse compl_compl compl_compl]
    refine eq_univ_of_forall fun a => ?_
    simp_rw [mem_union, mem_preimage]
    by_contra! ha
    refine s.ne_insert_of_notMem _ ha.1 (h _ ?_ <| s.subset_insert _)
    rw [coe_insert]
refine hs.insert ?_ fun b hb hab => ha.2 (hs.isUpperSet' h) hab.le_compl_left hb
    rintro rfl
    have := h {⊤} (by rw [coe_singleton]; exact intersecting_singleton.2 top_ne_bot)
    rw [compl_bot] at ha
    rw [coe_eq_empty.1 ((hs.isUpperSet' h).top_notMem.1 ha.2)] at this
    exact Finset.singleton_ne_empty _ (this <| Finset.empty_subset _).symm

/--
theorem `Intersecting.exists_card_eq` / 定理 `Intersecting.exists_card_eq`

English:
theorem Intersecting.exists_card_eq
  given: (hs : (s : Set α).Intersecting)
  proof: by
  have := hs.card_le
  rw [Nat.mul_comm]; rw [← Nat.le_div_iff_mul_le Nat.two_pos] at this
  revert hs
  refine s.strongDownwardInductionOn ?_ this
  rintro s ih _hcard hs
  by_cases! h : forall t : Finset α, (t : Set α).Intersecting -> s subseteq t -> s = t
  · exact ⟨s, Subset.rfl, hs.is_max_if

中文:
定理 Intersecting.exists_card_eq
  条件: (hs : (s : Set α).整数ersecting)
  证明: by
  have := hs.card_le
  rw [Nat.mul_comm]; rw [← Nat.le_div_iff_mul_le Nat.two_pos] at this
  revert hs
  refine s.strongDownwardInductionOn ?_ this
  rintro s ih _hcard hs
  by_cases! h : forall t : Finset α, (t : Set α).Intersecting -> s subseteq t -> s = t
  · exact ⟨s, Subset.rfl, hs.is_max_if

Depends on / 依赖: And.imp_left, Finset, Intersecting, Nat.le_div_iff_mul_le, Nat.mul_comm, Nat.two_pos, Subset, Subset.rfl, _hcard, _root_, _root_.ssubset_iff_subset_ne, card_le, hs.card_le, hs.is_max_iff_card_eq, ht.card_le, imp_left, is_max_iff_card_eq, le_div_iff_mul_le, mul_comm, revert
-/
theorem Intersecting.exists_card_eq (hs : (s : Set α).Intersecting) :
    exists t, s subseteq t ∧ 2 * #t = Fintype.card α ∧ (t : Set α).Intersecting := by
  have := hs.card_le
  rw [Nat.mul_comm]; rw [← Nat.le_div_iff_mul_le Nat.two_pos] at this
  revert hs
  refine s.strongDownwardInductionOn ?_ this
  rintro s ih _hcard hs
  by_cases! h : forall t : Finset α, (t : Set α).Intersecting -> s subseteq t -> s = t
  · exact ⟨s, Subset.rfl, hs.is_max_iff_card_eq.1 h, hs⟩
  obtain ⟨t, ht, hst⟩ := h
  refine (ih ?_ (_root_.ssubset_iff_subset_ne.2 hst) ht).imp fun u => And.imp_left hst.1.trans
  rw [Nat.le_div_iff_mul_le Nat.two_pos]; rw [Nat.mul_comm]
  exact ht.card_le

end

/-!
### `L`-intersecting families

This section defines `L`-intersecting families and establishes their basic properties.
-/

variable {L L' : Set Nat}
variable {α : Type*} [DecidableEq α]
variable {𝒜 ℬ : Set (Finset α)}

/--
Definition of `IsIntersectingOf` / `IsIntersectingOf` 的定义

English:
definition IsIntersectingOf
  signature: (L : Set Nat) (𝒜 : Set (Finset α))
  body: 𝒜.Pairwise fun s t => #(s inter t) in L

中文:
定义 IsIntersectingOf
  签名: (L : Set 自然数) (𝒜 : Set (Finset α))
  定义体: 𝒜.Pairwise fun s t => #(s inter t) in L

Depends on / 依赖: Pairwise
-/
def IsIntersectingOf (L : Set Nat) (𝒜 : Set (Finset α)) : Prop := 𝒜.Pairwise fun s t => #(s inter t) in L

namespace IsIntersectingOf

/--
An `L`-intersecting family is also `L'`-intersecting whenever `L ⊆ L'`.
-/
@[gcongr]
/--
theorem `mono` / 定理 `mono`

English:
theorem mono
  given: (h : L subseteq L') (hL : IsIntersectingOf L 𝒜)
  statement: IsIntersectingOf L' 𝒜
  proof: by tauto

中文:
定理 mono
  条件: (h : L subseteq L') (hL : Is整数ersectingOf L 𝒜)
  结论: Is整数ersectingOf L' 𝒜
  证明: by tauto
-/
theorem mono (h : L subseteq L') (hL : IsIntersectingOf L 𝒜) : IsIntersectingOf L' 𝒜 := by tauto

/--
An `L`-intersecting family remains `L`-intersecting under restriction to any subfamily.
-/
@[gcongr]
/--
theorem `anti` / 定理 `anti`

English:
theorem anti
  given: (h : ℬ subseteq 𝒜) (h𝒜 : IsIntersectingOf L 𝒜)
  statement: IsIntersectingOf L ℬ
  proof: Pairwise.mono h h𝒜

中文:
定理 anti
  条件: (h : ℬ subseteq 𝒜) (h𝒜 : Is整数ersectingOf L 𝒜)
  结论: Is整数ersectingOf L ℬ
  证明: Pairwise.mono h h𝒜

Depends on / 依赖: Pairwise, Pairwise.mono
-/
theorem anti (h : ℬ subseteq 𝒜) (h𝒜 : IsIntersectingOf L 𝒜) : IsIntersectingOf L ℬ := Pairwise.mono h h𝒜

/--
The empty family of finite sets is `L`-intersecting, vacuously, because it contains no pairs of
sets.
-/
@[simp]
/--
theorem `empty` / 定理 `empty`

English:
theorem empty
  statement: IsIntersectingOf L (∅ : Set (Finset α))
  proof: by tauto

中文:
定理 empty
  结论: Is整数ersectingOf L (∅ : Set (Finset α))
  证明: by tauto
-/
protected theorem empty : IsIntersectingOf L (∅ : Set (Finset α)) := by tauto

/--
Every family of finite sets is `univ`-intersecting.
-/
@[simp]
/--
theorem `univ` / 定理 `univ`

English:
theorem univ
  statement: IsIntersectingOf univ 𝒜
  proof: 𝒜.pairwise_of_forall _ fun _ _ => trivial

中文:
定理 univ
  结论: Is整数ersectingOf univ 𝒜
  证明: 𝒜.pairwise_of_forall _ fun _ _ => trivial
-/
protected theorem univ : IsIntersectingOf univ 𝒜 := 𝒜.pairwise_of_forall _ fun _ _ => trivial

end IsIntersectingOf

end Set
