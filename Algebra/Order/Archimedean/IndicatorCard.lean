/-
Copyright (c) 2024 Damien Thomine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damien Thomine
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Indicator
public import Mathlib.Algebra.Order.Archimedean.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Group.Indicator
public import Mathlib.Order.LiminfLimsup
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# Cardinality and limit of sum of indicators

This file contains results relating the cardinality of subsets of ℕ and limits,
limsups of sums of indicators.

## Tags
finite, indicator, limsup, tendsto
-/

public section

namespace Set

open Filter Finset

/--
lemma `sum_indicator_eventually_eq_card` / 引理 `sum_indicator_eventually_eq_card`

English:
lemma sum_indicator_eventually_eq_card
  statement: {α : Type*} [AddCommMonoid α] (a : α) {s : Set Nat}
  proof: by
  have key : forall x in hs.toFinset, s.indicator (fun _ => a) x = a := by
    intro x hx
    rw [indicator_of_mem (hs.mem_toFinset.1 hx) (fun _ => a)]
  rw [Nat.card_eq_card_finite_toFinset hs]; rw [← sum_eq_card_nsmul key]; rw [eventually_atTop]
  obtain ⟨m, hm⟩ := hs.bddAbove
  refine ⟨m + 1, 

中文:
引理 sum_indicator_eventually_eq_card
  结论: {α : 类型} [加法交换幺半群 α] (a : α) {s : 集合 自然数}
  证明: by
  have key : forall x in hs.toFinset, s.indicator (fun _ => a) x = a := by
    intro x hx
    rw [indicator_of_mem (hs.mem_toFinset.1 hx) (fun _ => a)]
  rw [Nat.card_eq_card_finite_toFinset hs]; rw [← sum_eq_card_nsmul key]; rw [eventually_atTop]
  obtain ⟨m, hm⟩ := hs.bddAbove
  refine ⟨m + 1, 

Depends on / 依赖: Finset, Finset.mem_range, Nat.card_eq_card_finite_toFinset, Nat.lt_of_succ_le, bddAbove, card_eq_card_finite_toFinset, eventually_atTop, hs.bddAbove, hs.mem_toFinset, hs.toFinset, indicator, indicator_of_mem, indicator_of_no, lt_of_succ_le, mem_range, mem_toFinset, mem_upperBounds, s.indicator, sum_eq_card_nsmul, sum_subset
-/
lemma sum_indicator_eventually_eq_card {α : Type*} [AddCommMonoid α] (a : α) {s : Set Nat}
    (hs : s.Finite) :
    forallᶠ n in atTop, ∑ k in Finset.range n, s.indicator (fun _ => a) k = (Nat.card s) • a := by
  have key : forall x in hs.toFinset, s.indicator (fun _ => a) x = a := by
    intro x hx
    rw [indicator_of_mem (hs.mem_toFinset.1 hx) (fun _ => a)]
  rw [Nat.card_eq_card_finite_toFinset hs]; rw [← sum_eq_card_nsmul key]; rw [eventually_atTop]
  obtain ⟨m, hm⟩ := hs.bddAbove
  refine ⟨m + 1, fun n n_m => (sum_subset ?_ ?_).symm⟩ <;> intro x <;> rw [hs.mem_toFinset]
  · rw [Finset.mem_range]
    exact fun x_s => ((mem_upperBounds.1 hm) x x_s).trans_lt (Nat.lt_of_succ_le n_m)
  · exact fun _ x_s => indicator_of_notMem x_s (fun _ => a)

/--
lemma `infinite_iff_tendsto_sum_indicator_atTop` / 引理 `infinite_iff_tendsto_sum_indicator_atTop`

English:
lemma infinite_iff_tendsto_sum_indicator_atTop
  statement: {R : Type*}
  proof: by
  constructor
  · have h_mono : Monotone fun n => ∑ k in Finset.range n, s.indicator (fun _ => r) k := by
      refine (sum_mono_set_of_nonneg ?_).comp range_mono
      exact (fun _ => indicator_nonneg (fun _ _ => h.le) _)
    rw [h_mono.tendsto_atTop_atTop_iff]
    intro hs n
    obtain ⟨n', hn'

中文:
引理 infinite_iff_tendsto_sum_indicator_atTop
  结论: {R : 类型}
  证明: by
  constructor
  · have h_mono : Monotone fun n => ∑ k in Finset.range n, s.indicator (fun _ => r) k := by
      refine (sum_mono_set_of_nonneg ?_).comp range_mono
      exact (fun _ => indicator_nonneg (fun _ _ => h.le) _)
    rw [h_mono.tendsto_atTop_atTop_iff]
    intro hs n
    obtain ⟨n', hn'

Depends on / 依赖: Finset, Finset.mem_range, Finset.range, Monotone, bddAbove, exists_lt_nsmul, exists_subset_card_eq, h.le, h_mono, h_mono.tendsto_atTop_atTop_iff, hs.exists_subset_card_eq, indicator, indicator_nonneg, mem_range, range_mono, s.indicator, subseteq, sum_mono_set_of_nonneg, t.bddAbove, t_card
-/
lemma infinite_iff_tendsto_sum_indicator_atTop {R : Type*}
    [AddCommMonoid R] [PartialOrder R] [IsOrderedAddMonoid R]
    [AddLeftStrictMono R] [Archimedean R] {r : R} (h : 0 < r) {s : Set Nat} :
    s.Infinite ↔ atTop.Tendsto (fun n => ∑ k in Finset.range n, s.indicator (fun _ => r) k) atTop := by
  constructor
  · have h_mono : Monotone fun n => ∑ k in Finset.range n, s.indicator (fun _ => r) k := by
      refine (sum_mono_set_of_nonneg ?_).comp range_mono
      exact (fun _ => indicator_nonneg (fun _ _ => h.le) _)
    rw [h_mono.tendsto_atTop_atTop_iff]
    intro hs n
    obtain ⟨n', hn'⟩ := exists_lt_nsmul h n
    obtain ⟨t, t_s, t_card⟩ := hs.exists_subset_card_eq n'
    obtain ⟨m, hm⟩ := t.bddAbove
    use m + 1
    grw [hn', ← t_s]
    have h : t subseteq Finset.range (m + 1) := by
      intro i i_t
      rw [Finset.mem_range]
      exact (hm i_t).trans_lt (lt_add_one m)
    rw [sum_indicator_subset (fun _ => r) h]; rw [sum_eq_card_nsmul (fun _ _ => rfl)]; rw [t_card]
  · contrapose!
    intro hs
    rw [tendsto_congr' (sum_indicator_eventually_eq_card r hs)]; rw [tendsto_atTop_atTop]
    push Not
    obtain ⟨m, hm⟩ := exists_lt_nsmul h (Nat.card s • r)
    exact ⟨m • r, fun n => ⟨n, le_refl n, not_le_of_gt hm⟩⟩

/--
lemma `limsup_eq_tendsto_sum_indicator_atTop` / 引理 `limsup_eq_tendsto_sum_indicator_atTop`

English:
lemma limsup_eq_tendsto_sum_indicator_atTop
  statement: {α R : Type*}
  proof: by
  nth_rw 1 [← Nat.cofinite_eq_atTop, cofinite.limsup_set_eq]
  ext ω
  rw [mem_ofPred_eq]; rw [mem_ofPred_eq]; rw [infinite_iff_tendsto_sum_indicator_atTop h]; rw [iff_eq_eq]
  congr

中文:
引理 limsup_eq_tendsto_sum_indicator_atTop
  结论: {α R : 类型}
  证明: by
  nth_rw 1 [← Nat.cofinite_eq_atTop, cofinite.limsup_set_eq]
  ext ω
  rw [mem_ofPred_eq]; rw [mem_ofPred_eq]; rw [infinite_iff_tendsto_sum_indicator_atTop h]; rw [iff_eq_eq]
  congr

Depends on / 依赖: Nat.cofinite_eq_atTop, cofinite, cofinite.limsup_set_eq, cofinite_eq_atTop, iff_eq_eq, infinite_iff_tendsto_sum_indicator_atTop, limsup_set_eq, mem_ofPred_eq, nth_rw
-/
lemma limsup_eq_tendsto_sum_indicator_atTop {α R : Type*}
    [AddCommMonoid R] [PartialOrder R] [IsOrderedAddMonoid R]
    [AddLeftStrictMono R] [Archimedean R] {r : R} (h : 0 < r) (s : Nat -> Set α) :
    atTop.limsup s = { ω | atTop.Tendsto
      (fun n => ∑ k in Finset.range n, (s k).indicator (fun _ => r) ω) atTop } := by
  nth_rw 1 [← Nat.cofinite_eq_atTop, cofinite.limsup_set_eq]
  ext ω
  rw [mem_ofPred_eq]; rw [mem_ofPred_eq]; rw [infinite_iff_tendsto_sum_indicator_atTop h]; rw [iff_eq_eq]
  congr

end Set
