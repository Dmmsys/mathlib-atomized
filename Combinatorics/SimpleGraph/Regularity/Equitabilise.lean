/-
Copyright (c) 2022 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
module

public import Mathlib.Algebra.Order.Ring.Canonical
public import Mathlib.Order.Partition.Equipartition

/-!
# Equitabilising a partition

This file allows to blow partitions up into parts of controlled size. Given a partition `P` and
`a b m : ℕ`, we want to find a partition `Q` with `a` parts of size `m` and `b` parts of size
`m + 1` such that all parts of `P` are "as close as possible" to unions of parts of `Q`. By
"as close as possible", we mean that each part of `P` can be written as the union of some parts of
`Q` along with at most `m` other elements.

## Main declarations

* `Finpartition.equitabilise`: `P.equitabilise h` where `h : a * m + b * (m + 1)` is a partition
  with `a` parts of size `m` and `b` parts of size `m + 1` which almost refines `P`.
* `Finpartition.exists_equipartition_card_eq`: We can find equipartitions of arbitrary size.

## References

[Yaël Dillies, Bhavik Mehta, *Formalising Szemerédi’s Regularity Lemma in Lean*][srl_itp]
-/

@[expose] public section


open Finset Nat

namespace Finpartition

variable {α : Type*} [DecidableEq α] {s t : Finset α} {m n a b : Nat} {P : Finpartition s}

/--
theorem `equitabilise_aux` / 定理 `equitabilise_aux`

English:
theorem equitabilise_aux
  given: (hs : a * m + b * (m + 1) = #s)
  proof: by
  -- Get rid of the easy case `m = 0`
  obtain rfl | m_pos := m.eq_zero_or_pos
  · refine ⟨⊥, by simp, ?_, by simpa [Finset.filter_true_of_mem] using hs.symm⟩
    simp only [le_zero_iff, card_eq_zero, mem_biUnion, mem_filter, id,
      and_assoc, sdiff_eq_empty_iff_subset, subset_iff]
    exact fun x hx a ha =>
      ⟨{a}, mem_map_of_mem _ (P.le hx ha), singleton_subset_iff.2 ha, mem_singleton_self _⟩
  -- Prove the case `m > 0` by strong induction on `s`
  induction s using Finset.strongInduction generalizing a b with | H s ih => _
  -- If `a = b = 0`, then `s = ∅` and we can partition into zero parts
  by_cases hab : a = 0 ∧ b = 0
  · -- Rewrite using `← bot_eq_empty` because we have theorems about `Finpartition ⊥`,
    -- and nothing about `Finpartition ∅`, even though they are defeq in this case.
    -- TODO: specialize the `Finpartition ⊥` lemmas to `Finpartition ∅`?
    simp only [hab.1, hab.2, add_zero, zero_mul, eq_comm, card_eq_zero, ← bot_eq_empty] at hs
    subst hs
    exact ⟨Finpartition.empty _, by simp, by simp [Unique.eq_default P, -bot_eq_empty],
      by simp [hab.2]⟩
  simp_rw [not_and_or, ← Ne.eq_def, ← pos_iff_ne_zero] at hab
  -- `n` will be the size of the smallest part
  set n := if 0 < a then m else m + 1 with hn
  -- Some easy facts about it
  obtain ⟨hn₀, hn₁, hn₂, hn₃⟩ : 0 < n ∧ n <= m + 1 ∧ n <= a * m + b * (m + 1) ∧
      ite (0 < a) (a - 1) a * m + ite (0 < a) b (b - 1) * (m + 1) = #s - n := by
    rw [hn]; rw [← hs]
    split_ifs with h <;> rw [tsub_mul, one_mul]
    · refine ⟨m_pos, le_succ _, le_add_right (Nat.le_mul_of_pos_left _ ‹0 < a›), ?_⟩
      rw [tsub_add_eq_add_tsub (Nat.le_mul_of_pos_left _ h)]
    · refine ⟨succ_pos', le_rfl,
        le_add_left (Nat.le_mul_of_pos_left _ <| hab.resolve_left ‹¬0 < a›), ?_⟩
      rw [← add_tsub_assoc_of_le (Nat.le_mul_of_pos_left _ <| hab.resolve_left ‹¬0 < a›)]
  /- We will call the inductive hypothesis on a partition of `s \ t` for a carefully chosen `t ⊆ s`.
    To decide which, however, we must distinguish the case where all parts of `P` have size `m` (in
    which case we take `t` to be an arbitrary subset of `s` of size `n`) from the case where at
    least one part `u` of `P` has size `m + 1` (in which case we take `t` to be an arbitrary subset
    of `u` of size `n`). The rest of each branch is just tedious calculations to satisfy the
    induction hypothesis. -/
  by_cases! h : forall u in P.parts, #u < m + 1
  · obtain ⟨t, hts, htn⟩ := exists_subset_card_eq (hn₂.trans_eq hs)
    have ht : t.Nonempty := by rwa [← card_pos, htn]
    have hcard : ite (0 < a) (a - 1) a * m + ite (0 < a) b (b - 1) * (m + 1) = #(s \ t) := by
      rw [card_sdiff_of_subset ‹t subseteq s›]; rw [htn]; rw [hn₃]
    obtain ⟨R, hR₁, _, hR₃⟩ :=
      @ih (s \ t) (sdiff_ssubset hts ‹t.Nonempty›) (if 0 < a then a - 1 else a)
        (if 0 < a then b else b - 1) (P.avoid t) hcard
    refine ⟨R.extend ht.ne_empty sdiff_disjoint (sdiff_sup_cancel hts), ?_, ?_, ?_⟩
    · simp only [extend_parts, mem_insert, forall_eq_or_imp, and_iff_left hR₁, htn, hn]
      exact ite_eq_or_eq _ _ _
    · exact fun x hx => (card_le_card sdiff_subset).trans (Nat.lt_succ_iff.1 <| h _ hx)
    simp_rw [extend_parts, filter_insert, htn, n, m.succ_ne_self.symm.ite_eq_right_iff]
    split_ifs with ha
    · rw [hR₃, if_pos ha]
    rw [card_insert_of_notMem]; rw [hR₃]; rw [if_neg ha]; rw [tsub_add_cancel_of_le]
    · exact hab.resolve_left ha
    · intro H; exact ht.ne_empty (le_sdiff_right.1 <| R.le <| filter_subset _ _ H)
  obtain ⟨u, hu₁, hu₂⟩ := h
  obtain ⟨t, htu, htn⟩ := exists_subset_card_eq (hn₁.trans hu₂)
  have ht : t.Nonempty := by rwa [← card_pos, htn]
  have hcard : ite (0 < a) (a - 1) a * m + ite (0 < a) b (b - 1) * (m + 1) = #(s \ t) := by
    rw [card_sdiff_of_subset (htu.trans <| P.le hu₁)]; rw [htn]; rw [hn₃]
  obtain ⟨R, hR₁, hR₂, hR₃⟩ :=
    @ih (s \ t) (sdiff_ssubset (htu.trans <| P.le hu₁) ht) (if 0 < a then a - 1 else a)
      (if 0 < a then b else b - 1) (P.avoid t) hcard
  refine
    ⟨R.extend ht.ne_empty sdiff_disjoint (sdiff_sup_cancel <| htu.trans <| P.le hu₁), ?_, ?_, ?_⟩
  · simp only [mem_insert, forall_eq_or_imp, extend_parts, and_iff_left hR₁, htn, hn]
    exact ite_eq_or_eq _ _ _
  · conv in _ in _ => rw [← insert_erase hu₁]
    simp only [mem_insert, forall_eq_or_imp, extend_parts]
refine ⟨?_, fun x hx => (card_le_card ?_).trans hR₂ x ?_⟩
    · simp only [filter_insert, if_pos htu, biUnion_insert, id]
      obtain rfl | hut := eq_or_ne u t
      · rw [sdiff_eq_empty_iff_subset.2 subset_union_left]
        exact bot_le
      refine
        (card_le_card fun i => ?_).trans
          (hR₂ (u \ t) <| P.mem_avoid.2 ⟨u, hu₁, fun i => hut <| i.antisymm htu, rfl⟩)
      simpa using fun hi₁ hi₂ hi₃ =>
⟨⟨hi₁, hi₂⟩, fun x hx hx' => hi₃ _ hx hx'.trans sdiff_subset⟩
    · apply sdiff_subset_sdiff Subset.rfl (biUnion_subset_biUnion_of_subset_left _ _)
      exact filter_subset_filter _ (subset_insert _ _)
    simp only [avoid, ofErase, mem_erase, mem_image, bot_eq_empty]
    exact
      ⟨(nonempty_of_mem_parts _ <| mem_of_mem_erase hx).ne_empty, _, mem_of_mem_erase hx,
        (disjoint_of_subset_right htu <|
P.disjoint (mem_of_mem_erase hx) hu₁ ne_of_mem_erase hx).sdiff_eq_left⟩
  simp only [extend_parts, filter_insert, htn, hn, m.succ_ne_self.symm.ite_eq_right_iff]
  split_ifs with h
  · rw [hR₃, if_pos h]
  · rw [card_insert_of_notMem, hR₃, if_neg h, Nat.sub_add_cancel (hab.resolve_left h)]
    intro H; exact ht.ne_empty (le_sdiff_right.1 <| R.le <| filter_subset _ _ H)

中文:
定理 equitabilise_aux
  条件: (hs : a * m + b * (m + 1) = #s)
  证明: by
  -- Get rid of the easy case `m = 0`
  obtain rfl | m_pos := m.eq_zero_or_pos
  · refine ⟨⊥, by simp, ?_, by simpa [Finset.filter_true_of_mem] using hs.symm⟩
    simp only [le_zero_iff, card_eq_zero, mem_biUnion, mem_filter, id,
      and_assoc, sdiff_eq_empty_iff_subset, subset_iff]
    exact fun x hx a ha =>
      ⟨{a}, mem_map_of_mem _ (P.le hx ha), singleton_subset_iff.2 ha, mem_singleton_self _⟩
  -- Prove the case `m > 0` by strong induction on `s`
  induction s using Finset.strongInduction generalizing a b with | H s ih => _
  -- If `a = b = 0`, then `s = ∅` and we can partition into zero parts
  by_cases hab : a = 0 ∧ b = 0
  · -- Rewrite using `← bot_eq_empty` because we have theorems about `Finpartition ⊥`,
    -- and nothing about `Finpartition ∅`, even though they are defeq in this case.
    -- TODO: specialize the `Finpartition ⊥` lemmas to `Finpartition ∅`?
    simp only [hab.1, hab.2, add_zero, zero_mul, eq_comm, card_eq_zero, ← bot_eq_empty] at hs
    subst hs
    exact ⟨Finpartition.empty _, by simp, by simp [Unique.eq_default P, -bot_eq_empty],
      by simp [hab.2]⟩
  simp_rw [not_and_or, ← Ne.eq_def, ← pos_iff_ne_zero] at hab
  -- `n` will be the size of the smallest part
  set n := if 0 < a then m else m + 1 with hn
  -- Some easy facts about it
  obtain ⟨hn₀, hn₁, hn₂, hn₃⟩ : 0 < n ∧ n <= m + 1 ∧ n <= a * m + b * (m + 1) ∧
      ite (0 < a) (a - 1) a * m + ite (0 < a) b (b - 1) * (m + 1) = #s - n := by
    rw [hn]; rw [← hs]
    split_ifs with h <;> rw [tsub_mul, one_mul]
    · refine ⟨m_pos, le_succ _, le_add_right (Nat.le_mul_of_pos_left _ ‹0 < a›), ?_⟩
      rw [tsub_add_eq_add_tsub (Nat.le_mul_of_pos_left _ h)]
    · refine ⟨succ_pos', le_rfl,
        le_add_left (Nat.le_mul_of_pos_left _ <| hab.resolve_left ‹¬0 < a›), ?_⟩
      rw [← add_tsub_assoc_of_le (Nat.le_mul_of_pos_left _ <| hab.resolve_left ‹¬0 < a›)]
  /- We will call the inductive hypothesis on a partition of `s \ t` for a carefully chosen `t ⊆ s`.
    To decide which, however, we must distinguish the case where all parts of `P` have size `m` (in
    which case we take `t` to be an arbitrary subset of `s` of size `n`) from the case where at
    least one part `u` of `P` has size `m + 1` (in which case we take `t` to be an arbitrary subset
    of `u` of size `n`). The rest of each branch is just tedious calculations to satisfy the
    induction hypothesis. -/
  by_cases! h : forall u in P.parts, #u < m + 1
  · obtain ⟨t, hts, htn⟩ := exists_subset_card_eq (hn₂.trans_eq hs)
    have ht : t.Nonempty := by rwa [← card_pos, htn]
    have hcard : ite (0 < a) (a - 1) a * m + ite (0 < a) b (b - 1) * (m + 1) = #(s \ t) := by
      rw [card_sdiff_of_subset ‹t subseteq s›]; rw [htn]; rw [hn₃]
    obtain ⟨R, hR₁, _, hR₃⟩ :=
      @ih (s \ t) (sdiff_ssubset hts ‹t.Nonempty›) (if 0 < a then a - 1 else a)
        (if 0 < a then b else b - 1) (P.avoid t) hcard
    refine ⟨R.extend ht.ne_empty sdiff_disjoint (sdiff_sup_cancel hts), ?_, ?_, ?_⟩
    · simp only [extend_parts, mem_insert, forall_eq_or_imp, and_iff_left hR₁, htn, hn]
      exact ite_eq_or_eq _ _ _
    · exact fun x hx => (card_le_card sdiff_subset).trans (Nat.lt_succ_iff.1 <| h _ hx)
    simp_rw [extend_parts, filter_insert, htn, n, m.succ_ne_self.symm.ite_eq_right_iff]
    split_ifs with ha
    · rw [hR₃, if_pos ha]
    rw [card_insert_of_notMem]; rw [hR₃]; rw [if_neg ha]; rw [tsub_add_cancel_of_le]
    · exact hab.resolve_left ha
    · intro H; exact ht.ne_empty (le_sdiff_right.1 <| R.le <| filter_subset _ _ H)
  obtain ⟨u, hu₁, hu₂⟩ := h
  obtain ⟨t, htu, htn⟩ := exists_subset_card_eq (hn₁.trans hu₂)
  have ht : t.Nonempty := by rwa [← card_pos, htn]
  have hcard : ite (0 < a) (a - 1) a * m + ite (0 < a) b (b - 1) * (m + 1) = #(s \ t) := by
    rw [card_sdiff_of_subset (htu.trans <| P.le hu₁)]; rw [htn]; rw [hn₃]
  obtain ⟨R, hR₁, hR₂, hR₃⟩ :=
    @ih (s \ t) (sdiff_ssubset (htu.trans <| P.le hu₁) ht) (if 0 < a then a - 1 else a)
      (if 0 < a then b else b - 1) (P.avoid t) hcard
  refine
    ⟨R.extend ht.ne_empty sdiff_disjoint (sdiff_sup_cancel <| htu.trans <| P.le hu₁), ?_, ?_, ?_⟩
  · simp only [mem_insert, forall_eq_or_imp, extend_parts, and_iff_left hR₁, htn, hn]
    exact ite_eq_or_eq _ _ _
  · conv in _ in _ => rw [← insert_erase hu₁]
    simp only [mem_insert, forall_eq_or_imp, extend_parts]
refine ⟨?_, fun x hx => (card_le_card ?_).trans hR₂ x ?_⟩
    · simp only [filter_insert, if_pos htu, biUnion_insert, id]
      obtain rfl | hut := eq_or_ne u t
      · rw [sdiff_eq_empty_iff_subset.2 subset_union_left]
        exact bot_le
      refine
        (card_le_card fun i => ?_).trans
          (hR₂ (u \ t) <| P.mem_avoid.2 ⟨u, hu₁, fun i => hut <| i.antisymm htu, rfl⟩)
      simpa using fun hi₁ hi₂ hi₃ =>
⟨⟨hi₁, hi₂⟩, fun x hx hx' => hi₃ _ hx hx'.trans sdiff_subset⟩
    · apply sdiff_subset_sdiff Subset.rfl (biUnion_subset_biUnion_of_subset_left _ _)
      exact filter_subset_filter _ (subset_insert _ _)
    simp only [avoid, ofErase, mem_erase, mem_image, bot_eq_empty]
    exact
      ⟨(nonempty_of_mem_parts _ <| mem_of_mem_erase hx).ne_empty, _, mem_of_mem_erase hx,
        (disjoint_of_subset_right htu <|
P.disjoint (mem_of_mem_erase hx) hu₁ ne_of_mem_erase hx).sdiff_eq_left⟩
  simp only [extend_parts, filter_insert, htn, hn, m.succ_ne_self.symm.ite_eq_right_iff]
  split_ifs with h
  · rw [hR₃, if_pos h]
  · rw [card_insert_of_notMem, hR₃, if_neg h, Nat.sub_add_cancel (hab.resolve_left h)]
    intro H; exact ht.ne_empty (le_sdiff_right.1 <| R.le <| filter_subset _ _ H)
-/
theorem equitabilise_aux (hs : a * m + b * (m + 1) = #s) :
    exists Q : Finpartition s,
      (forall x : Finset α, x in Q.parts -> #x = m ∨ #x = m + 1) ∧
        (forall x, x in P.parts -> #(x \ {y in Q.parts | y subseteq x}.biUnion id) <= m) ∧
          #{i in Q.parts | #i = m + 1} = b := by
  -- Get rid of the easy case `m = 0`
  obtain rfl | m_pos := m.eq_zero_or_pos
  · refine ⟨⊥, by simp, ?_, by simpa [Finset.filter_true_of_mem] using hs.symm⟩
    simp only [le_zero_iff, card_eq_zero, mem_biUnion, mem_filter, id,
      and_assoc, sdiff_eq_empty_iff_subset, subset_iff]
    exact fun x hx a ha =>
      ⟨{a}, mem_map_of_mem _ (P.le hx ha), singleton_subset_iff.2 ha, mem_singleton_self _⟩
  -- Prove the case `m > 0` by strong induction on `s`
  induction s using Finset.strongInduction generalizing a b with | H s ih => _
  -- If `a = b = 0`, then `s = ∅` and we can partition into zero parts
  by_cases hab : a = 0 ∧ b = 0
  · -- Rewrite using `← bot_eq_empty` because we have theorems about `Finpartition ⊥`,
    -- and nothing about `Finpartition ∅`, even though they are defeq in this case.
    -- TODO: specialize the `Finpartition ⊥` lemmas to `Finpartition ∅`?
    simp only [hab.1, hab.2, add_zero, zero_mul, eq_comm, card_eq_zero, ← bot_eq_empty] at hs
    subst hs
    exact ⟨Finpartition.empty _, by simp, by simp [Unique.eq_default P, -bot_eq_empty],
      by simp [hab.2]⟩
  simp_rw [not_and_or, ← Ne.eq_def, ← pos_iff_ne_zero] at hab
  -- `n` will be the size of the smallest part
  set n := if 0 < a then m else m + 1 with hn
  -- Some easy facts about it
  obtain ⟨hn₀, hn₁, hn₂, hn₃⟩ : 0 < n ∧ n <= m + 1 ∧ n <= a * m + b * (m + 1) ∧
      ite (0 < a) (a - 1) a * m + ite (0 < a) b (b - 1) * (m + 1) = #s - n := by
    rw [hn]; rw [← hs]
    split_ifs with h <;> rw [tsub_mul, one_mul]
    · refine ⟨m_pos, le_succ _, le_add_right (Nat.le_mul_of_pos_left _ ‹0 < a›), ?_⟩
      rw [tsub_add_eq_add_tsub (Nat.le_mul_of_pos_left _ h)]
    · refine ⟨succ_pos', le_rfl,
        le_add_left (Nat.le_mul_of_pos_left _ <| hab.resolve_left ‹¬0 < a›), ?_⟩
      rw [← add_tsub_assoc_of_le (Nat.le_mul_of_pos_left _ <| hab.resolve_left ‹¬0 < a›)]
  /- We will call the inductive hypothesis on a partition of `s \ t` for a carefully chosen `t ⊆ s`.
    To decide which, however, we must distinguish the case where all parts of `P` have size `m` (in
    which case we take `t` to be an arbitrary subset of `s` of size `n`) from the case where at
    least one part `u` of `P` has size `m + 1` (in which case we take `t` to be an arbitrary subset
    of `u` of size `n`). The rest of each branch is just tedious calculations to satisfy the
    induction hypothesis. -/
  by_cases! h : forall u in P.parts, #u < m + 1
  · obtain ⟨t, hts, htn⟩ := exists_subset_card_eq (hn₂.trans_eq hs)
    have ht : t.Nonempty := by rwa [← card_pos, htn]
    have hcard : ite (0 < a) (a - 1) a * m + ite (0 < a) b (b - 1) * (m + 1) = #(s \ t) := by
      rw [card_sdiff_of_subset ‹t subseteq s›]; rw [htn]; rw [hn₃]
    obtain ⟨R, hR₁, _, hR₃⟩ :=
      @ih (s \ t) (sdiff_ssubset hts ‹t.Nonempty›) (if 0 < a then a - 1 else a)
        (if 0 < a then b else b - 1) (P.avoid t) hcard
    refine ⟨R.extend ht.ne_empty sdiff_disjoint (sdiff_sup_cancel hts), ?_, ?_, ?_⟩
    · simp only [extend_parts, mem_insert, forall_eq_or_imp, and_iff_left hR₁, htn, hn]
      exact ite_eq_or_eq _ _ _
    · exact fun x hx => (card_le_card sdiff_subset).trans (Nat.lt_succ_iff.1 <| h _ hx)
    simp_rw [extend_parts, filter_insert, htn, n, m.succ_ne_self.symm.ite_eq_right_iff]
    split_ifs with ha
    · rw [hR₃, if_pos ha]
    rw [card_insert_of_notMem]; rw [hR₃]; rw [if_neg ha]; rw [tsub_add_cancel_of_le]
    · exact hab.resolve_left ha
    · intro H; exact ht.ne_empty (le_sdiff_right.1 <| R.le <| filter_subset _ _ H)
  obtain ⟨u, hu₁, hu₂⟩ := h
  obtain ⟨t, htu, htn⟩ := exists_subset_card_eq (hn₁.trans hu₂)
  have ht : t.Nonempty := by rwa [← card_pos, htn]
  have hcard : ite (0 < a) (a - 1) a * m + ite (0 < a) b (b - 1) * (m + 1) = #(s \ t) := by
    rw [card_sdiff_of_subset (htu.trans <| P.le hu₁)]; rw [htn]; rw [hn₃]
  obtain ⟨R, hR₁, hR₂, hR₃⟩ :=
    @ih (s \ t) (sdiff_ssubset (htu.trans <| P.le hu₁) ht) (if 0 < a then a - 1 else a)
      (if 0 < a then b else b - 1) (P.avoid t) hcard
  refine
    ⟨R.extend ht.ne_empty sdiff_disjoint (sdiff_sup_cancel <| htu.trans <| P.le hu₁), ?_, ?_, ?_⟩
  · simp only [mem_insert, forall_eq_or_imp, extend_parts, and_iff_left hR₁, htn, hn]
    exact ite_eq_or_eq _ _ _
  · conv in _ in _ => rw [← insert_erase hu₁]
    simp only [mem_insert, forall_eq_or_imp, extend_parts]
refine ⟨?_, fun x hx => (card_le_card ?_).trans hR₂ x ?_⟩
    · simp only [filter_insert, if_pos htu, biUnion_insert, id]
      obtain rfl | hut := eq_or_ne u t
      · rw [sdiff_eq_empty_iff_subset.2 subset_union_left]
        exact bot_le
      refine
        (card_le_card fun i => ?_).trans
          (hR₂ (u \ t) <| P.mem_avoid.2 ⟨u, hu₁, fun i => hut <| i.antisymm htu, rfl⟩)
      simpa using fun hi₁ hi₂ hi₃ =>
⟨⟨hi₁, hi₂⟩, fun x hx hx' => hi₃ _ hx hx'.trans sdiff_subset⟩
    · apply sdiff_subset_sdiff Subset.rfl (biUnion_subset_biUnion_of_subset_left _ _)
      exact filter_subset_filter _ (subset_insert _ _)
    simp only [avoid, ofErase, mem_erase, mem_image, bot_eq_empty]
    exact
      ⟨(nonempty_of_mem_parts _ <| mem_of_mem_erase hx).ne_empty, _, mem_of_mem_erase hx,
        (disjoint_of_subset_right htu <|
P.disjoint (mem_of_mem_erase hx) hu₁ ne_of_mem_erase hx).sdiff_eq_left⟩
  simp only [extend_parts, filter_insert, htn, hn, m.succ_ne_self.symm.ite_eq_right_iff]
  split_ifs with h
  · rw [hR₃, if_pos h]
  · rw [card_insert_of_notMem, hR₃, if_neg h, Nat.sub_add_cancel (hab.resolve_left h)]
    intro H; exact ht.ne_empty (le_sdiff_right.1 <| R.le <| filter_subset _ _ H)

variable (h : a * m + b * (m + 1) = #s)

/--
Definition of `equitabilise` / `equitabilise` 的定义

English:
definition equitabilise
  signature: : Finpartition s
  body: (P.equitabilise_aux h).choose

中文:
定义 equitabilise
  签名: : 有限分拆 s
  定义体: (P.equitabilise_aux h).choose

Depends on / 依赖: P.equitabilise_aux, equitabilise_aux
-/
noncomputable def equitabilise : Finpartition s :=
  (P.equitabilise_aux h).choose

variable {h}

/--
theorem `card_eq_of_mem_parts_equitabilise` / 定理 `card_eq_of_mem_parts_equitabilise`

English:
theorem card_eq_of_mem_parts_equitabilise
  proof: (P.equitabilise_aux h).choose_spec.1 _

中文:
定理 card_eq_of_mem_parts_equitabilise
  证明: (P.equitabilise_aux h).choose_spec.1 _

Depends on / 依赖: P.equitabilise_aux, choose_spec, equitabilise_aux
-/
theorem card_eq_of_mem_parts_equitabilise :
    t in (P.equitabilise h).parts -> #t = m ∨ #t = m + 1 :=
  (P.equitabilise_aux h).choose_spec.1 _

/--
theorem `equitabilise_isEquipartition` / 定理 `equitabilise_isEquipartition`

English:
theorem equitabilise_isEquipartition
  statement: (P.equitabilise h).IsEquipartition
  proof: Set.equitableOn_iff_exists_eq_eq_add_one.2 ⟨m, fun _ => card_eq_of_mem_parts_equitabilise⟩

中文:
定理 equitabilise_isEquipartition
  结论: (P.equitabilise h).IsEquipartition
  证明: Set.equitableOn_iff_exists_eq_eq_add_one.2 ⟨m, fun _ => card_eq_of_mem_parts_equitabilise⟩

Depends on / 依赖: Set.equitableOn_iff_exists_eq_eq_add_one, card_eq_of_mem_parts_equitabilise, equitableOn_iff_exists_eq_eq_add_one
-/
theorem equitabilise_isEquipartition : (P.equitabilise h).IsEquipartition :=
  Set.equitableOn_iff_exists_eq_eq_add_one.2 ⟨m, fun _ => card_eq_of_mem_parts_equitabilise⟩

variable (P h)

/--
theorem `card_filter_equitabilise_big` / 定理 `card_filter_equitabilise_big`

English:
theorem card_filter_equitabilise_big
  statement: #{u in (P.equitabilise h).parts | #u = m + 1} = b
  proof: (P.equitabilise_aux h).choose_spec.2.2

中文:
定理 card_filter_equitabilise_big
  结论: #{u in (P.equitabilise h).parts | #u = m + 1} = b
  证明: (P.equitabilise_aux h).choose_spec.2.2

Depends on / 依赖: P.equitabilise_aux, choose_spec, equitabilise_aux
-/
theorem card_filter_equitabilise_big : #{u in (P.equitabilise h).parts | #u = m + 1} = b :=
  (P.equitabilise_aux h).choose_spec.2.2

/--
theorem `card_filter_equitabilise_small` / 定理 `card_filter_equitabilise_small`

English:
theorem card_filter_equitabilise_small
  given: (hm : m != 0)
  proof: by
  refine (mul_eq_mul_right_iff.1 <| (add_left_inj (b * (m + 1))).1 ?_).resolve_right hm
  rw [h]; rw [← (P.equitabilise h).sum_card_parts]
  have hunion :
    (P.equitabilise h).parts =
      {u in (P.equitabilise h).parts | #u = m} union {u in (P.equitabilise h).parts | #u = m + 1} := by
    rw [← filter_or]; rw [filter_true_of_mem]
    exact fun x => card_eq_of_mem_parts_equitabilise
  nth_rw 2 [hunion]
  rw [sum_union]; rw [sum_const_nat fun x hx => (mem_filter.1 hx).2]; rw [sum_const_nat fun x hx => (mem_filter.1 hx).2]; rw [P.card_filter_equitabilise_big]
  refine disjoint_filter_filter' _ _ ?_
  intro x ha hb i h
  apply succ_ne_self m _
  exact (hb i h).symm.trans (ha i h)

中文:
定理 card_filter_equitabilise_small
  条件: (hm : m != 0)
  证明: by
  refine (mul_eq_mul_right_iff.1 <| (add_left_inj (b * (m + 1))).1 ?_).resolve_right hm
  rw [h]; rw [← (P.equitabilise h).sum_card_parts]
  have hunion :
    (P.equitabilise h).parts =
      {u in (P.equitabilise h).parts | #u = m} union {u in (P.equitabilise h).parts | #u = m + 1} := by
    rw [← filter_or]; rw [filter_true_of_mem]
    exact fun x => card_eq_of_mem_parts_equitabilise
  nth_rw 2 [hunion]
  rw [sum_union]; rw [sum_const_nat fun x hx => (mem_filter.1 hx).2]; rw [sum_const_nat fun x hx => (mem_filter.1 hx).2]; rw [P.card_filter_equitabilise_big]
  refine disjoint_filter_filter' _ _ ?_
  intro x ha hb i h
  apply succ_ne_self m _
  exact (hb i h).symm.trans (ha i h)

Depends on / 依赖: P.equitabilise, add_left_inj, card_eq_of_mem_parts_equitabilise, equitabilise, filter_or, filter_true_of_mem, hunion, mem_filter, mul_eq_mul_right_iff, nth_rw, resolve_right, sum_card_parts, sum_const_nat, sum_union
-/
theorem card_filter_equitabilise_small (hm : m != 0) :
    #{u in (P.equitabilise h).parts | #u = m} = a := by
  refine (mul_eq_mul_right_iff.1 <| (add_left_inj (b * (m + 1))).1 ?_).resolve_right hm
  rw [h]; rw [← (P.equitabilise h).sum_card_parts]
  have hunion :
    (P.equitabilise h).parts =
      {u in (P.equitabilise h).parts | #u = m} union {u in (P.equitabilise h).parts | #u = m + 1} := by
    rw [← filter_or]; rw [filter_true_of_mem]
    exact fun x => card_eq_of_mem_parts_equitabilise
  nth_rw 2 [hunion]
  rw [sum_union]; rw [sum_const_nat fun x hx => (mem_filter.1 hx).2]; rw [sum_const_nat fun x hx => (mem_filter.1 hx).2]; rw [P.card_filter_equitabilise_big]
  refine disjoint_filter_filter' _ _ ?_
  intro x ha hb i h
  apply succ_ne_self m _
  exact (hb i h).symm.trans (ha i h)

/--
theorem `card_parts_equitabilise` / 定理 `card_parts_equitabilise`

English:
theorem card_parts_equitabilise
  given: (hm : m != 0)
  statement: #(P.equitabilise h).parts = a + b
  proof: by
  rw [← filter_true_of_mem fun x => card_eq_of_mem_parts_equitabilise]; rw [filter_or]; rw [card_union_of_disjoint]; rw [P.card_filter_equitabilise_small _ hm]; rw [P.card_filter_equitabilise_big]
  aesop (add norm disjoint_filter)

中文:
定理 card_parts_equitabilise
  条件: (hm : m != 0)
  结论: #(P.equitabilise h).parts = a + b
  证明: by
  rw [← filter_true_of_mem fun x => card_eq_of_mem_parts_equitabilise]; rw [filter_or]; rw [card_union_of_disjoint]; rw [P.card_filter_equitabilise_small _ hm]; rw [P.card_filter_equitabilise_big]
  aesop (add norm disjoint_filter)

Depends on / 依赖: P.card_filter_equitabilise_big, P.card_filter_equitabilise_small, card_eq_of_mem_parts_equitabilise, card_filter_equitabilise_big, card_filter_equitabilise_small, card_union_of_disjoint, disjoint_filter, filter_or, filter_true_of_mem
-/
theorem card_parts_equitabilise (hm : m != 0) : #(P.equitabilise h).parts = a + b := by
  rw [← filter_true_of_mem fun x => card_eq_of_mem_parts_equitabilise]; rw [filter_or]; rw [card_union_of_disjoint]; rw [P.card_filter_equitabilise_small _ hm]; rw [P.card_filter_equitabilise_big]
  aesop (add norm disjoint_filter)

/--
theorem `card_parts_equitabilise_subset_le` / 定理 `card_parts_equitabilise_subset_le`

English:
theorem card_parts_equitabilise_subset_le
  proof: (Classical.choose_spec <| P.equitabilise_aux h).2.1 t

中文:
定理 card_parts_equitabilise_subset_le
  证明: (Classical.choose_spec <| P.equitabilise_aux h).2.1 t

Depends on / 依赖: Classical, Classical.choose_spec, P.equitabilise_aux, choose_spec, equitabilise_aux
-/
theorem card_parts_equitabilise_subset_le :
    t in P.parts -> #(t \ {u in (P.equitabilise h).parts | u subseteq t}.biUnion id) <= m :=
  (Classical.choose_spec <| P.equitabilise_aux h).2.1 t

variable (s)

/--
theorem `exists_equipartition_card_eq` / 定理 `exists_equipartition_card_eq`

English:
theorem exists_equipartition_card_eq
  given: (hn : n != 0) (hs : n <= #s)
  proof: by
  rw [← pos_iff_ne_zero] at hn
  have : (n - #s % n) * (#s / n) + #s % n * (#s / n + 1) = #s := by
    rw [tsub_mul]; rw [mul_add]; rw [← add_assoc]; rw [tsub_add_cancel_of_le (Nat.mul_le_mul_right _ (mod_lt _ hn).le)]; rw [mul_one]; rw [add_comm]; rw [mod_add_div]
  refine
    ⟨(indiscrete (card_pos.1 <| hn.trans_le hs).ne_empty).equitabilise this,
      equitabilise_isEquipartition, ?_⟩
  rw [card_parts_equitabilise _ _ (Nat.div_pos hs hn).ne']; rw [tsub_add_cancel_of_le (mod_lt _ hn).le]

中文:
定理 存在_equipartition_card_eq
  条件: (hn : n != 0) (hs : n <= #s)
  证明: by
  rw [← pos_iff_ne_zero] at hn
  have : (n - #s % n) * (#s / n) + #s % n * (#s / n + 1) = #s := by
    rw [tsub_mul]; rw [mul_add]; rw [← add_assoc]; rw [tsub_add_cancel_of_le (Nat.mul_le_mul_right _ (mod_lt _ hn).le)]; rw [mul_one]; rw [add_comm]; rw [mod_add_div]
  refine
    ⟨(indiscrete (card_pos.1 <| hn.trans_le hs).ne_empty).equitabilise this,
      equitabilise_isEquipartition, ?_⟩
  rw [card_parts_equitabilise _ _ (Nat.div_pos hs hn).ne']; rw [tsub_add_cancel_of_le (mod_lt _ hn).le]

Depends on / 依赖: Nat.div_pos, Nat.mul_le_mul_right, add_assoc, add_comm, card_parts_equitabilise, card_pos, div_pos, equitabilise, equitabilise_isEquipartition, hn.trans_le, indiscrete, mod_add_div, mod_lt, mul_add, mul_le_mul_right, mul_one, ne_empty, pos_iff_ne_zero, trans_le, tsub_add_cancel_of_le
-/
theorem exists_equipartition_card_eq (hn : n != 0) (hs : n <= #s) :
    exists P : Finpartition s, P.IsEquipartition ∧ #P.parts = n := by
  rw [← pos_iff_ne_zero] at hn
  have : (n - #s % n) * (#s / n) + #s % n * (#s / n + 1) = #s := by
    rw [tsub_mul]; rw [mul_add]; rw [← add_assoc]; rw [tsub_add_cancel_of_le (Nat.mul_le_mul_right _ (mod_lt _ hn).le)]; rw [mul_one]; rw [add_comm]; rw [mod_add_div]
  refine
    ⟨(indiscrete (card_pos.1 <| hn.trans_le hs).ne_empty).equitabilise this,
      equitabilise_isEquipartition, ?_⟩
  rw [card_parts_equitabilise _ _ (Nat.div_pos hs hn).ne']; rw [tsub_add_cancel_of_le (mod_lt _ hn).le]

end Finpartition
