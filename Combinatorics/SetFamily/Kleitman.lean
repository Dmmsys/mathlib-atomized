/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Combinatorics.SetFamily.HarrisKleitman
public import Mathlib.Combinatorics.SetFamily.Intersecting

/-!
# Kleitman's bound on the size of intersecting families

An intersecting family on `n` elements has size at most `2ⁿ⁻¹`, so we could naïvely think that two
intersecting families could cover all `2ⁿ` sets. But actually that's not case because for example
none of them can contain the empty set. Intersecting families are in some sense correlated.
Kleitman's bound stipulates that `k` intersecting families cover at most `2ⁿ - 2ⁿ⁻ᵏ` sets.

## Main declarations

* `Finset.card_biUnion_le_of_intersecting`: Kleitman's theorem.

## References

* [D. J. Kleitman, *Families of non-disjoint subsets*][kleitman1966]
-/

public section


open Finset

open Fintype (card)

variable {ι α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]

/--
theorem `Finset.card_biUnion_le_of_intersecting` / 定理 `Finset.card_biUnion_le_of_intersecting`

English:
theorem Finset.card_biUnion_le_of_intersecting
  statement: (s : Finset ι) (f : ι -> Finset (Finset α))
  proof: by
  have : DecidableEq ι := by
    classical
    infer_instance
  obtain hs | hs := le_total (Fintype.card α) #s
  · rw [tsub_eq_zero_of_le hs, pow_zero]
    refine (card_le_card <| biUnion_subset.2 fun i hi a ha =>
mem_compl.2 notMem_singleton.2 (hf _ hi).ne_bot ha).trans_eq ?_
    rw [card_compl]

中文:
定理 Finset.card_biUnion_le_of_intersecting
  结论: (s : Finset ι) (f : ι -> Finset (Finset α))
  证明: by
  have : DecidableEq ι := by
    classical
    infer_instance
  obtain hs | hs := le_total (Fintype.card α) #s
  · rw [tsub_eq_zero_of_le hs, pow_zero]
    refine (card_le_card <| biUnion_subset.2 fun i hi a ha =>
mem_compl.2 notMem_singleton.2 (hf _ hi).ne_bot ha).trans_eq ?_
    rw [card_compl]

Depends on / 依赖: DecidableEq, Finset, Finset.cons_induction, Fintype, Fintype.card, Fintype.card_finset, biUnion_subset, card_compl, card_finset, card_le_card, card_singleton, classical, cons_induction, generalizing, infer_instance, le_total, mem_compl, ne_bot, notMem_singleton, pow_zero
-/
theorem Finset.card_biUnion_le_of_intersecting (s : Finset ι) (f : ι -> Finset (Finset α))
    (hf : forall i in s, (f i : Set (Finset α)).Intersecting) :
    #(s.biUnion f) <= 2 ^ Fintype.card α - 2 ^ (Fintype.card α - #s) := by
  have : DecidableEq ι := by
    classical
    infer_instance
  obtain hs | hs := le_total (Fintype.card α) #s
  · rw [tsub_eq_zero_of_le hs, pow_zero]
    refine (card_le_card <| biUnion_subset.2 fun i hi a ha =>
mem_compl.2 notMem_singleton.2 (hf _ hi).ne_bot ha).trans_eq ?_
    rw [card_compl]; rw [Fintype.card_finset]; rw [card_singleton]
  induction s using Finset.cons_induction generalizing f with
  | empty => simp
  | cons i s hi ih =>
  set f' : ι -> Finset (Finset α) :=
    fun j => if hj : j in cons i s hi then (hf j hj).exists_card_eq.choose else ∅
  have hf₁ : forall j, j in cons i s hi -> f j subseteq f' j ∧ 2 * #(f' j) =
      2 ^ Fintype.card α ∧ (f' j : Set (Finset α)).Intersecting := by
    rintro j hj
    simp_rw [f', dif_pos hj, ← Fintype.card_finset]
    exact Classical.choose_spec (hf j hj).exists_card_eq
  have hf₂ : forall j, j in cons i s hi -> IsUpperSet (f' j : Set (Finset α)) := by
    refine fun j hj => (hf₁ _ hj).2.2.isUpperSet' ((hf₁ _ hj).2.2.is_max_iff_card_eq.2 ?_)
    rw [Fintype.card_finset]
    exact (hf₁ _ hj).2.1
  refine (card_le_card <| biUnion_mono fun j hj => (hf₁ _ hj).1).trans ?_
  nth_rw 1 [cons_eq_insert i]
  rw [biUnion_insert]
  refine (card_mono <| @le_sup_sdiff _ _ (f' i) _).trans ((card_union_le _ _).trans ?_)
  rw [union_sdiff_left]; rw [sdiff_eq_inter_compl]
  refine le_of_mul_le_mul_left ?_ (pow_pos (zero_lt_two' Nat) <| Fintype.card α + 1)
  rw [pow_succ]; rw [mul_add]; rw [mul_assoc]; rw [mul_comm _ 2]; rw [mul_assoc]
  refine (add_le_add
      ((mul_le_mul_iff_right₀ <| pow_pos (zero_lt_two' Nat) _).2
      (hf₁ _ <| mem_cons_self _ _).2.2.card_le) <|
(mul_le_mul_iff_right₀ <| zero_lt_two' Nat).2 IsUpperSet.card_inter_le_finset ?_ ?_).trans ?_
  · rw [coe_biUnion]
exact isUpperSet_iUnion₂ fun i hi => hf₂ _ subset_cons _ hi
  · rw [coe_compl]
    exact (hf₂ _ <| mem_cons_self _ _).compl
  rw [mul_tsub]; rw [card_compl]; rw [Fintype.card_finset]; rw [mul_left_comm]; rw [mul_tsub]; rw [(hf₁ _ <| mem_cons_self _ _).2.1]; rw [two_mul]; rw [add_tsub_cancel_left]; rw [← mul_tsub]; rw [← mul_two]; rw [mul_assoc]; rw [← add_mul]; rw [mul_comm]
  gcongr
  refine (add_le_add_right
    (ih _ (fun i hi => (hf₁ _ <| subset_cons _ hi).2.2)
    ((card_le_card <| subset_cons _).trans hs)) _).trans ?_
  rw [mul_tsub]; rw [two_mul]; rw [← pow_succ']; rw [← add_tsub_assoc_of_le (pow_right_mono₀ (one_le_two : (1 : Nat) <= 2) tsub_le_self)]; rw [tsub_add_eq_add_tsub hs]; rw [card_cons]; rw [add_tsub_add_eq_tsub_right]
