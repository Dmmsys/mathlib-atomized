/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic.NormNum

/-!
# Some facts about finite rings
-/

public section


open Finset ZMod

section Ring

variable {R : Type*} [Ring R] [Fintype R] [DecidableEq R]

/--
lemma `Finset.univ_of_card_le_two` / 引理 `Finset.univ_of_card_le_two`

English:
lemma Finset.univ_of_card_le_two
  given: (h : Fintype.card R <= 2)
  proof: by
  rcases subsingleton_or_nontrivial R
  · exact le_antisymm (fun a _ => by simp [Subsingleton.elim a 0]) (Finset.subset_univ _)
  · refine (eq_of_subset_of_card_le (subset_univ _) ?_).symm
    convert! h
    simp

中文:
引理 有限集.univ_of_card_le_two
  条件: (h : 有限类型.card R <= 2)
  证明: by
  rcases subsingleton_or_nontrivial R
  · exact le_antisymm (fun a _ => by simp [Subsingleton.elim a 0]) (Finset.subset_univ _)
  · refine (eq_of_subset_of_card_le (subset_univ _) ?_).symm
    convert! h
    simp

Depends on / 依赖: Finset, Finset.subset_univ, Subsingleton, Subsingleton.elim, convert, eq_of_subset_of_card_le, le_antisymm, subset_univ, subsingleton_or_nontrivial
-/
lemma Finset.univ_of_card_le_two (h : Fintype.card R <= 2) :
    (univ : Finset R) = {0, 1} := by
  rcases subsingleton_or_nontrivial R
  · exact le_antisymm (fun a _ => by simp [Subsingleton.elim a 0]) (Finset.subset_univ _)
  · refine (eq_of_subset_of_card_le (subset_univ _) ?_).symm
    convert! h
    simp

/--
lemma `Finset.univ_of_card_le_three` / 引理 `Finset.univ_of_card_le_three`

English:
lemma Finset.univ_of_card_le_three
  given: (h : Fintype.card R <= 3)
  proof: by
  refine (eq_of_subset_of_card_le (subset_univ _) ?_).symm
  rcases lt_or_eq_of_le h with h | h
  · apply card_le_card
    rw [Finset.univ_of_card_le_two (Nat.lt_succ_iff.1 h)]
    simp
  · have : Nontrivial R := by
      refine Fintype.one_lt_card_iff_nontrivial.1 ?_
      rw [h]
      simp
    

中文:
引理 有限集.univ_of_card_le_three
  条件: (h : 有限类型.card R <= 3)
  证明: by
  refine (eq_of_subset_of_card_le (subset_univ _) ?_).symm
  rcases lt_or_eq_of_le h with h | h
  · apply card_le_card
    rw [Finset.univ_of_card_le_two (Nat.lt_succ_iff.1 h)]
    simp
  · have : Nontrivial R := by
      refine Fintype.one_lt_card_iff_nontrivial.1 ?_
      rw [h]
      simp
    

Depends on / 依赖: Finset, Finset.univ_of_card_le_two, Fintype, Fintype.one_lt_card_iff_nontrivial, Nat.lt_succ_iff, Nat.prime_three, Nontrivial, add_eq_zero_iff_eq_neg, apply_fun, card_insert_of_notMem, card_le_card, card_singleton, card_univ, eq_of_subset_of_card_le, lt_or_eq_of_le, lt_succ_iff, mem_singleton, one_add_one_eq_two, one_lt_card_iff_nontrivial, prime_three
-/
lemma Finset.univ_of_card_le_three (h : Fintype.card R <= 3) :
    (univ : Finset R) = {0, 1, -1} := by
  refine (eq_of_subset_of_card_le (subset_univ _) ?_).symm
  rcases lt_or_eq_of_le h with h | h
  · apply card_le_card
    rw [Finset.univ_of_card_le_two (Nat.lt_succ_iff.1 h)]
    simp
  · have : Nontrivial R := by
      refine Fintype.one_lt_card_iff_nontrivial.1 ?_
      rw [h]
      simp
    rw [card_univ]; rw [h]; rw [card_insert_of_notMem]; rw [card_insert_of_notMem]; rw [card_singleton]
    · rw [mem_singleton]
      intro H
      rw [← add_eq_zero_iff_eq_neg]; rw [one_add_one_eq_two] at H
      apply_fun (ringEquivOfPrime R Nat.prime_three h).symm at H
      simp only [map_ofNat, map_zero] at H
      replace H : ((2 : Nat) : ZMod 3) = 0 := H
      rw [natCast_eq_zero_iff] at H
      norm_num at H
    · simp

end Ring

section MonoidWithZero

variable (M₀ : Type*) [MonoidWithZero M₀] [Nontrivial M₀]

open scoped Classical in
/--
theorem `card_units_lt` / 定理 `card_units_lt`

English:
theorem card_units_lt
  given: [Fintype M₀]
  statement: Fintype.card M₀ˣ < Fintype.card M₀
  proof: Fintype.card_lt_of_injective_of_notMem Units.val Units.val_injective not_isUnit_zero

中文:
定理 card_units_lt
  条件: [有限类型 M₀]
  结论: 有限类型.card M₀ˣ < 有限类型.card M₀
  证明: Fintype.card_lt_of_injective_of_notMem Units.val Units.val_injective not_isUnit_zero

Depends on / 依赖: Fintype, Fintype.card_lt_of_injective_of_notMem, Units.val, Units.val_injective, card_lt_of_injective_of_notMem, not_isUnit_zero, val_injective
-/
theorem card_units_lt [Fintype M₀] : Fintype.card M₀ˣ < Fintype.card M₀ :=
  Fintype.card_lt_of_injective_of_notMem Units.val Units.val_injective not_isUnit_zero

/--
lemma `natCard_units_lt` / 引理 `natCard_units_lt`

English:
lemma natCard_units_lt
  given: [Finite M₀]
  statement: Nat.card M₀ˣ < Nat.card M₀
  proof: by
  have : Fintype M₀ := Fintype.ofFinite M₀
  simpa only [Fintype.card_eq_nat_card] using card_units_lt M₀

中文:
引理 natCard_units_lt
  条件: [有限 M₀]
  结论: 自然数.card M₀ˣ < 自然数.card M₀
  证明: by
  have : Fintype M₀ := Fintype.ofFinite M₀
  simpa only [Fintype.card_eq_nat_card] using card_units_lt M₀

Depends on / 依赖: Fintype, Fintype.card_eq_nat_card, Fintype.ofFinite, card_eq_nat_card, card_units_lt, ofFinite
-/
lemma natCard_units_lt [Finite M₀] : Nat.card M₀ˣ < Nat.card M₀ := by
  have : Fintype M₀ := Fintype.ofFinite M₀
  simpa only [Fintype.card_eq_nat_card] using card_units_lt M₀

variable {M₀}

/--
lemma `orderOf_lt_card` / 引理 `orderOf_lt_card`

English:
lemma orderOf_lt_card
  given: [Finite M₀] (a : M₀)
  statement: orderOf a < Nat.card M₀
  proof: by
  by_cases h : IsUnit a
  · rw [← h.unit_spec, orderOf_units]
exact orderOf_le_card.trans_lt natCard_units_lt M₀
  · rw [orderOf_eq_zero_iff'.mpr fun n hn ha => h <| IsUnit.of_pow_eq_one ha hn.ne']
    exact Nat.card_pos

中文:
引理 orderOf_lt_card
  条件: [有限 M₀] (a : M₀)
  结论: orderOf a < 自然数.card M₀
  证明: by
  by_cases h : IsUnit a
  · rw [← h.unit_spec, orderOf_units]
exact orderOf_le_card.trans_lt natCard_units_lt M₀
  · rw [orderOf_eq_zero_iff'.mpr fun n hn ha => h <| IsUnit.of_pow_eq_one ha hn.ne']
    exact Nat.card_pos

Depends on / 依赖: IsUnit, IsUnit.of_pow_eq_one, Nat.card_pos, card_pos, h.unit_spec, hn.ne, natCard_units_lt, of_pow_eq_one, orderOf_eq_zero_iff, orderOf_le_card, orderOf_le_card.trans_lt, orderOf_units, trans_lt, unit_spec
-/
lemma orderOf_lt_card [Finite M₀] (a : M₀) : orderOf a < Nat.card M₀ := by
  by_cases h : IsUnit a
  · rw [← h.unit_spec, orderOf_units]
exact orderOf_le_card.trans_lt natCard_units_lt M₀
  · rw [orderOf_eq_zero_iff'.mpr fun n hn ha => h <| IsUnit.of_pow_eq_one ha hn.ne']
    exact Nat.card_pos

end MonoidWithZero

/--
lemma `ZMod.orderOf_lt` / 引理 `ZMod.orderOf_lt`

English:
lemma ZMod.orderOf_lt
  given: {n : Nat} (hn : 1 < n) (a : ZMod n)
  statement: orderOf a < n
  proof: have : NeZero n := ⟨Nat.ne_zero_of_lt hn⟩
  have : Nontrivial (ZMod n) := nontrivial_iff.mpr hn.ne'
(orderOf_lt_card a).trans_eq Nat.card_zmod n

中文:
引理 ZMod.orderOf_lt
  条件: {n : 自然数} (hn : 1 < n) (a : ZMod n)
  结论: orderOf a < n
  证明: have : NeZero n := ⟨Nat.ne_zero_of_lt hn⟩
  have : Nontrivial (ZMod n) := nontrivial_iff.mpr hn.ne'
(orderOf_lt_card a).trans_eq Nat.card_zmod n

Depends on / 依赖: Nat.card_zmod, Nat.ne_zero_of_lt, NeZero, Nontrivial, card_zmod, hn.ne, ne_zero_of_lt, nontrivial_iff, nontrivial_iff.mpr, orderOf_lt_card, trans_eq
-/
lemma ZMod.orderOf_lt {n : Nat} (hn : 1 < n) (a : ZMod n) : orderOf a < n :=
  have : NeZero n := ⟨Nat.ne_zero_of_lt hn⟩
  have : Nontrivial (ZMod n) := nontrivial_iff.mpr hn.ne'
(orderOf_lt_card a).trans_eq Nat.card_zmod n
