/-
Copyright (c) 2024 Pim Otte. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pim Otte
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Lemmas
public import Mathlib.Data.Set.Finite.Lattice
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# Big operators on a finset in the natural numbers

This file contains the results concerning the interaction of finset big operators with natural
numbers.
-/

public section

variable {ι : Type*}

namespace Finset

/--
lemma `even_sum_iff_even_card_odd` / 引理 `even_sum_iff_even_card_odd`

English:
lemma even_sum_iff_even_card_odd
  given: {s : Finset ι} (f : ι -> Nat)
  proof: by
  rw [← Finset.sum_filter_add_sum_filter_not _ (fun x => Even (f x))]; rw [Nat.even_add]
  simp only [Finset.mem_filter, and_imp, imp_self, implies_true, Finset.even_sum, true_iff]
  rw [Nat.even_iff]; rw [Finset.sum_nat_mod]; rw [Finset.sum_filter]
  simp +contextual only [Nat.not_even_iff_odd, 

中文:
引理 even_sum_iff_even_card_odd
  条件: {s : 有限集 ι} (f : ι -> 自然数)
  证明: by
  rw [← Finset.sum_filter_add_sum_filter_not _ (fun x => Even (f x))]; rw [Nat.even_add]
  simp only [Finset.mem_filter, and_imp, imp_self, implies_true, Finset.even_sum, true_iff]
  rw [Nat.even_iff]; rw [Finset.sum_nat_mod]; rw [Finset.sum_filter]
  simp +contextual only [Nat.not_even_iff_odd, 

Depends on / 依赖: Finset, Finset.card_eq_sum_ones, Finset.even_sum, Finset.mem_filter, Finset.sum_filter, Finset.sum_filter_add_sum_filter_not, Finset.sum_nat_mod, Nat.even_add, Nat.even_iff, Nat.not_even_iff_odd, Nat.odd_iff.mp, and_imp, card_eq_sum_ones, contextual, even_add, even_iff, even_sum, imp_self, implies_true, mem_filter
-/
lemma even_sum_iff_even_card_odd {s : Finset ι} (f : ι -> Nat) :
    Even (∑ i in s, f i) ↔ Even #{x in s | Odd (f x)} := by
  rw [← Finset.sum_filter_add_sum_filter_not _ (fun x => Even (f x))]; rw [Nat.even_add]
  simp only [Finset.mem_filter, and_imp, imp_self, implies_true, Finset.even_sum, true_iff]
  rw [Nat.even_iff]; rw [Finset.sum_nat_mod]; rw [Finset.sum_filter]
  simp +contextual only [Nat.not_even_iff_odd, Nat.odd_iff.mp]
  simp_rw [← Finset.sum_filter, ← Nat.even_iff, Finset.card_eq_sum_ones]

/--
lemma `odd_sum_iff_odd_card_odd` / 引理 `odd_sum_iff_odd_card_odd`

English:
lemma odd_sum_iff_odd_card_odd
  given: {s : Finset ι} (f : ι -> Nat)
  proof: by
  simp only [← Nat.not_even_iff_odd, even_sum_iff_even_card_odd]

中文:
引理 odd_sum_iff_odd_card_odd
  条件: {s : 有限集 ι} (f : ι -> 自然数)
  证明: by
  simp only [← Nat.not_even_iff_odd, even_sum_iff_even_card_odd]

Depends on / 依赖: Nat.not_even_iff_odd, even_sum_iff_even_card_odd, not_even_iff_odd
-/
lemma odd_sum_iff_odd_card_odd {s : Finset ι} (f : ι -> Nat) :
    Odd (∑ i in s, f i) ↔ Odd #{x in s | Odd (f x)} := by
  simp only [← Nat.not_even_iff_odd, even_sum_iff_even_card_odd]

/--
theorem `card_preimage_eq_sum_card_image_eq` / 定理 `card_preimage_eq_sum_card_image_eq`

English:
theorem card_preimage_eq_sum_card_image_eq
  statement: {M : Type*} {f : ι -> M} {s : Finset M}
  proof: by
  classical
  -- `t = s ∩ Set.range f` as a `Finset`
  let t := (Set.finite_coe_iff.mp (Finite.Set.finite_inter_of_left ↑s (Set.range f))).toFinset
  rw [show Nat.card (f ⁻¹' s) = Nat.card (f ⁻¹' t) by simp [t]]
  rw [show ∑ b in s]; rw [Nat.card {a //f a = b} = ∑ b in t]; rw [Nat.card {a | f a =

中文:
定理 card_preimage_eq_sum_card_image_eq
  结论: {M : 类型} {f : ι -> M} {s : 有限集 M}
  证明: by
  classical
  -- `t = s ∩ Set.range f` as a `Finset`
  let t := (Set.finite_coe_iff.mp (Finite.Set.finite_inter_of_left ↑s (Set.range f))).toFinset
  rw [show Nat.card (f ⁻¹' s) = Nat.card (f ⁻¹' t) by simp [t]]
  rw [show ∑ b in s]; rw [Nat.card {a //f a = b} = ∑ b in t]; rw [Nat.card {a | f a =

Depends on / 依赖: classical
-/
theorem card_preimage_eq_sum_card_image_eq {M : Type*} {f : ι -> M} {s : Finset M}
    (hb : forall b in s, Set.Finite {a | f a = b}) :
    Nat.card (f ⁻¹' s) = ∑ b in s, Nat.card {a // f a = b} := by
  classical
  -- `t = s ∩ Set.range f` as a `Finset`
  let t := (Set.finite_coe_iff.mp (Finite.Set.finite_inter_of_left ↑s (Set.range f))).toFinset
  rw [show Nat.card (f ⁻¹' s) = Nat.card (f ⁻¹' t) by simp [t]]
  rw [show ∑ b in s]; rw [Nat.card {a //f a = b} = ∑ b in t]; rw [Nat.card {a | f a = b} by
    exact (Finset.sum_subset (by simp [t]) (by aesop)).symm]
  have ht : Set.Finite (f ⁻¹' t) := Set.Finite.preimage' (finite_toSet t) (by aesop)
  rw [Nat.card_eq_card_finite_toFinset ht]; rw [Finset.card_eq_sum_card_image (f := f)]
  refine Finset.sum_congr ?_ fun m hm => ?_
  · simpa [← Finset.coe_inj, t] using Set.image_preimage_eq_inter_range
  · rw [Nat.card_eq_card_finite_toFinset (hb _ (by aesop))]
    suffices {a | f a = m} subseteq ht.toFinset from
      congr_arg (Finset.card ·) (Finset.ext_iff.mpr fun a => by simpa using fun h => this h)
    intro _ h
    simp_all

end Finset
