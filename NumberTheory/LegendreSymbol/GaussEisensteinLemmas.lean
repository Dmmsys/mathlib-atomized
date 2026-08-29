/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
module

public import Mathlib.Data.Nat.Prime.Factorial
public import Mathlib.NumberTheory.LegendreSymbol.Basic

/-!
# Lemmas of Gauss and Eisenstein

This file contains the Lemmas of Gauss and Eisenstein on the Legendre symbol.
The main results are `ZMod.gauss_lemma` and `ZMod.eisenstein_lemma`.
-/

public section


open Finset Nat

open scoped Nat

section GaussEisenstein

namespace ZMod

/--
theorem `Ico_map_valMinAbs_natAbs_eq_Ico_map_id` / 定理 `Ico_map_valMinAbs_natAbs_eq_Ico_map_id`

English:
theorem Ico_map_valMinAbs_natAbs_eq_Ico_map_id
  statement: (p : Nat) [hp : Fact p.Prime] (a : ZMod p)
  proof: by
  have he : forall {x}, x in Ico 1 (p / 2).succ -> x != 0 ∧ x <= p / 2 := by grind
  have hep : forall {x}, x in Ico 1 (p / 2).succ -> x < p := fun hx =>
    lt_of_le_of_lt (he hx).2 (Nat.div_lt_self hp.1.pos (by decide))
  have hpe : forall {x}, x in Ico 1 (p / 2).succ -> ¬p ∣ x := fun hx hpx =>
    not_lt_of_ge (le_of_dvd (Nat.pos_of_ne_zero (he hx).1) hpx) (hep hx)
  have hmem : forall (x : Nat) (_ : x in Ico 1 (p / 2).succ),
      (a * x : ZMod p).valMinAbs.natAbs in Ico 1 (p / 2).succ := by
    intro x hx
    simp [hap, CharP.cast_eq_zero_iff (ZMod p) p, hpe hx, one_le_iff_ne_zero, natAbs_valMinAbs_le _]
  have hsurj : forall (b : Nat) (hb : b in Ico 1 (p / 2).succ),
      exists x, exists _ : x in Ico 1 (p / 2).succ, (a * x : ZMod p).valMinAbs.natAbs = b := by
    intro b hb
    refine ⟨(b / a : ZMod p).valMinAbs.natAbs, mem_Ico.mpr ⟨?_, ?_⟩, ?_⟩
    · apply Nat.pos_of_ne_zero
      simp only [div_eq_mul_inv, hap, CharP.cast_eq_zero_iff (ZMod p) p, hpe hb, not_false_iff,
        valMinAbs_eq_zero, inv_eq_zero, Int.natAbs_eq_zero, Ne, _root_.mul_eq_zero, or_self_iff]
    · apply lt_succ_of_le; apply natAbs_valMinAbs_le
    · rw [natCast_natAbs_valMinAbs]
      split_ifs
      · rw [mul_div_cancel₀ _ hap, valMinAbs_def_pos, val_cast_of_lt (hep hb),
          if_pos (le_of_lt_succ (mem_Ico.1 hb).2), Int.natAbs_natCast]
      · rw [mul_neg, mul_div_cancel₀ _ hap, natAbs_valMinAbs_neg, valMinAbs_def_pos,
          val_cast_of_lt (hep hb), if_pos (le_of_lt_succ (mem_Ico.1 hb).2), Int.natAbs_natCast]
  exact Multiset.map_eq_map_of_bij_of_nodup _ _ (Finset.nodup _) (Finset.nodup _)
    (fun x _ => (a * x : ZMod p).valMinAbs.natAbs) hmem
    (inj_on_of_surj_on_of_card_le _ hmem hsurj le_rfl) hsurj (fun _ _ => rfl)

中文:
定理 Ico_map_valMinAbs_natAbs_eq_Ico_map_id
  结论: (p : 自然数) [hp : Fact p.素] (a : ZMod p)
  证明: by
  have he : forall {x}, x in Ico 1 (p / 2).succ -> x != 0 ∧ x <= p / 2 := by grind
  have hep : forall {x}, x in Ico 1 (p / 2).succ -> x < p := fun hx =>
    lt_of_le_of_lt (he hx).2 (Nat.div_lt_self hp.1.pos (by decide))
  have hpe : forall {x}, x in Ico 1 (p / 2).succ -> ¬p ∣ x := fun hx hpx =>
    not_lt_of_ge (le_of_dvd (Nat.pos_of_ne_zero (he hx).1) hpx) (hep hx)
  have hmem : forall (x : Nat) (_ : x in Ico 1 (p / 2).succ),
      (a * x : ZMod p).valMinAbs.natAbs in Ico 1 (p / 2).succ := by
    intro x hx
    simp [hap, CharP.cast_eq_zero_iff (ZMod p) p, hpe hx, one_le_iff_ne_zero, natAbs_valMinAbs_le _]
  have hsurj : forall (b : Nat) (hb : b in Ico 1 (p / 2).succ),
      exists x, exists _ : x in Ico 1 (p / 2).succ, (a * x : ZMod p).valMinAbs.natAbs = b := by
    intro b hb
    refine ⟨(b / a : ZMod p).valMinAbs.natAbs, mem_Ico.mpr ⟨?_, ?_⟩, ?_⟩
    · apply Nat.pos_of_ne_zero
      simp only [div_eq_mul_inv, hap, CharP.cast_eq_zero_iff (ZMod p) p, hpe hb, not_false_iff,
        valMinAbs_eq_zero, inv_eq_zero, Int.natAbs_eq_zero, Ne, _root_.mul_eq_zero, or_self_iff]
    · apply lt_succ_of_le; apply natAbs_valMinAbs_le
    · rw [natCast_natAbs_valMinAbs]
      split_ifs
      · rw [mul_div_cancel₀ _ hap, valMinAbs_def_pos, val_cast_of_lt (hep hb),
          if_pos (le_of_lt_succ (mem_Ico.1 hb).2), Int.natAbs_natCast]
      · rw [mul_neg, mul_div_cancel₀ _ hap, natAbs_valMinAbs_neg, valMinAbs_def_pos,
          val_cast_of_lt (hep hb), if_pos (le_of_lt_succ (mem_Ico.1 hb).2), Int.natAbs_natCast]
  exact Multiset.map_eq_map_of_bij_of_nodup _ _ (Finset.nodup _) (Finset.nodup _)
    (fun x _ => (a * x : ZMod p).valMinAbs.natAbs) hmem
    (inj_on_of_surj_on_of_card_le _ hmem hsurj le_rfl) hsurj (fun _ _ => rfl)

Depends on / 依赖: Nat.div_lt_self, Nat.pos_of_ne_zero, div_lt_self, le_of_dvd, lt_of_le_of_lt, natAbs, not_lt_of_ge, pos_of_ne_zero, valMinAbs, valMinAbs.natAbs
-/
theorem Ico_map_valMinAbs_natAbs_eq_Ico_map_id (p : Nat) [hp : Fact p.Prime] (a : ZMod p)
    (hap : a != 0) : ((Ico 1 (p / 2).succ).1.map fun (x : Nat) => (a * x).valMinAbs.natAbs) =
    (Ico 1 (p / 2).succ).1.map fun a => a := by
  have he : forall {x}, x in Ico 1 (p / 2).succ -> x != 0 ∧ x <= p / 2 := by grind
  have hep : forall {x}, x in Ico 1 (p / 2).succ -> x < p := fun hx =>
    lt_of_le_of_lt (he hx).2 (Nat.div_lt_self hp.1.pos (by decide))
  have hpe : forall {x}, x in Ico 1 (p / 2).succ -> ¬p ∣ x := fun hx hpx =>
    not_lt_of_ge (le_of_dvd (Nat.pos_of_ne_zero (he hx).1) hpx) (hep hx)
  have hmem : forall (x : Nat) (_ : x in Ico 1 (p / 2).succ),
      (a * x : ZMod p).valMinAbs.natAbs in Ico 1 (p / 2).succ := by
    intro x hx
    simp [hap, CharP.cast_eq_zero_iff (ZMod p) p, hpe hx, one_le_iff_ne_zero, natAbs_valMinAbs_le _]
  have hsurj : forall (b : Nat) (hb : b in Ico 1 (p / 2).succ),
      exists x, exists _ : x in Ico 1 (p / 2).succ, (a * x : ZMod p).valMinAbs.natAbs = b := by
    intro b hb
    refine ⟨(b / a : ZMod p).valMinAbs.natAbs, mem_Ico.mpr ⟨?_, ?_⟩, ?_⟩
    · apply Nat.pos_of_ne_zero
      simp only [div_eq_mul_inv, hap, CharP.cast_eq_zero_iff (ZMod p) p, hpe hb, not_false_iff,
        valMinAbs_eq_zero, inv_eq_zero, Int.natAbs_eq_zero, Ne, _root_.mul_eq_zero, or_self_iff]
    · apply lt_succ_of_le; apply natAbs_valMinAbs_le
    · rw [natCast_natAbs_valMinAbs]
      split_ifs
      · rw [mul_div_cancel₀ _ hap, valMinAbs_def_pos, val_cast_of_lt (hep hb),
          if_pos (le_of_lt_succ (mem_Ico.1 hb).2), Int.natAbs_natCast]
      · rw [mul_neg, mul_div_cancel₀ _ hap, natAbs_valMinAbs_neg, valMinAbs_def_pos,
          val_cast_of_lt (hep hb), if_pos (le_of_lt_succ (mem_Ico.1 hb).2), Int.natAbs_natCast]
  exact Multiset.map_eq_map_of_bij_of_nodup _ _ (Finset.nodup _) (Finset.nodup _)
    (fun x _ => (a * x : ZMod p).valMinAbs.natAbs) hmem
    (inj_on_of_surj_on_of_card_le _ hmem hsurj le_rfl) hsurj (fun _ _ => rfl)

/--
theorem `gauss_lemma_aux₁` / 定理 `gauss_lemma_aux₁`

English:
theorem gauss_lemma_aux₁
  given: (p : Nat) [Fact p.Prime] {a : Int} (hap : (a : ZMod p) != 0)
  proof: calc
    (a ^ (p / 2) * (p / 2)! : ZMod p) = ∏ x in Ico 1 (p / 2).succ, a * x := by
      rw [prod_mul_distrib]; rw [← prod_natCast]; rw [prod_Ico_id_eq_factorial]; rw [prod_const]; rw [card_Ico]; rw [Nat.add_one_sub_one]; simp
    _ = ∏ x in Ico 1 (p / 2).succ, ↑((a * x : ZMod p).val) := by simp
    _ = ∏ x in Ico 1 (p / 2).succ, (if (a * x : ZMod p).val <= p / 2 then (1 : ZMod p) else -1) *
        (a * x : ZMod p).valMinAbs.natAbs :=
      (prod_congr rfl fun _ _ => by
        simp only [natCast_natAbs_valMinAbs]
        split_ifs <;> simp)
    _ = (-1 : ZMod p) ^ #{x in Ico 1 (p / 2).succ | ¬(a * x.cast : ZMod p).val <= p / 2} *
          ∏ x in Ico 1 (p / 2).succ, ↑((a * x : ZMod p).valMinAbs.natAbs) := by
      rw [prod_mul_distrib]; rw [Finset.prod_ite]
      simp
    _ = (-1 : ZMod p) ^ #{x in Ico 1 (p / 2).succ | ¬(a * x.cast : ZMod p).val <= p / 2} *
          (p / 2)! := by
      rw [← prod_natCast]; rw [Finset.prod_eq_multiset_prod]; rw [Ico_map_valMinAbs_natAbs_eq_Ico_map_id p a hap]; rw [← Finset.prod_eq_multiset_prod]; rw [prod_Ico_id_eq_factorial]

中文:
定理 gauss_lemma_aux₁
  条件: (p : 自然数) [Fact p.素] {a : 整数} (hap : (a : ZMod p) != 0)
  证明: calc
    (a ^ (p / 2) * (p / 2)! : ZMod p) = ∏ x in Ico 1 (p / 2).succ, a * x := by
      rw [prod_mul_distrib]; rw [← prod_natCast]; rw [prod_Ico_id_eq_factorial]; rw [prod_const]; rw [card_Ico]; rw [Nat.add_one_sub_one]; simp
    _ = ∏ x in Ico 1 (p / 2).succ, ↑((a * x : ZMod p).val) := by simp
    _ = ∏ x in Ico 1 (p / 2).succ, (if (a * x : ZMod p).val <= p / 2 then (1 : ZMod p) else -1) *
        (a * x : ZMod p).valMinAbs.natAbs :=
      (prod_congr rfl fun _ _ => by
        simp only [natCast_natAbs_valMinAbs]
        split_ifs <;> simp)
    _ = (-1 : ZMod p) ^ #{x in Ico 1 (p / 2).succ | ¬(a * x.cast : ZMod p).val <= p / 2} *
          ∏ x in Ico 1 (p / 2).succ, ↑((a * x : ZMod p).valMinAbs.natAbs) := by
      rw [prod_mul_distrib]; rw [Finset.prod_ite]
      simp
    _ = (-1 : ZMod p) ^ #{x in Ico 1 (p / 2).succ | ¬(a * x.cast : ZMod p).val <= p / 2} *
          (p / 2)! := by
      rw [← prod_natCast]; rw [Finset.prod_eq_multiset_prod]; rw [Ico_map_valMinAbs_natAbs_eq_Ico_map_id p a hap]; rw [← Finset.prod_eq_multiset_prod]; rw [prod_Ico_id_eq_factorial]
-/
private theorem gauss_lemma_aux₁ (p : Nat) [Fact p.Prime] {a : Int} (hap : (a : ZMod p) != 0) :
    (a ^ (p / 2) * (p / 2)! : ZMod p) =
     (-1 : ZMod p) ^ #{x in Ico 1 (p / 2).succ | ¬ (a * x.cast : ZMod p).val <= p / 2} * (p / 2)! :=
  calc
    (a ^ (p / 2) * (p / 2)! : ZMod p) = ∏ x in Ico 1 (p / 2).succ, a * x := by
      rw [prod_mul_distrib]; rw [← prod_natCast]; rw [prod_Ico_id_eq_factorial]; rw [prod_const]; rw [card_Ico]; rw [Nat.add_one_sub_one]; simp
    _ = ∏ x in Ico 1 (p / 2).succ, ↑((a * x : ZMod p).val) := by simp
    _ = ∏ x in Ico 1 (p / 2).succ, (if (a * x : ZMod p).val <= p / 2 then (1 : ZMod p) else -1) *
        (a * x : ZMod p).valMinAbs.natAbs :=
      (prod_congr rfl fun _ _ => by
        simp only [natCast_natAbs_valMinAbs]
        split_ifs <;> simp)
    _ = (-1 : ZMod p) ^ #{x in Ico 1 (p / 2).succ | ¬(a * x.cast : ZMod p).val <= p / 2} *
          ∏ x in Ico 1 (p / 2).succ, ↑((a * x : ZMod p).valMinAbs.natAbs) := by
      rw [prod_mul_distrib]; rw [Finset.prod_ite]
      simp
    _ = (-1 : ZMod p) ^ #{x in Ico 1 (p / 2).succ | ¬(a * x.cast : ZMod p).val <= p / 2} *
          (p / 2)! := by
      rw [← prod_natCast]; rw [Finset.prod_eq_multiset_prod]; rw [Ico_map_valMinAbs_natAbs_eq_Ico_map_id p a hap]; rw [← Finset.prod_eq_multiset_prod]; rw [prod_Ico_id_eq_factorial]

/--
theorem `gauss_lemma_aux` / 定理 `gauss_lemma_aux`

English:
theorem gauss_lemma_aux
  given: (p : Nat) [hp : Fact p.Prime] {a : Int} (hap : (a : ZMod p) != 0)
  proof: (mul_left_inj' (show ((p / 2)! : ZMod p) != 0 by
    rw [Ne]; rw [CharP.cast_eq_zero_iff (ZMod p) p]; rw [hp.1.dvd_factorial]; rw [not_le]
    exact Nat.div_lt_self hp.1.pos (by decide))).1 <| by
      simpa using gauss_lemma_aux₁ p hap

中文:
定理 gauss_lemma_aux
  条件: (p : 自然数) [hp : Fact p.素] {a : 整数} (hap : (a : ZMod p) != 0)
  证明: (mul_left_inj' (show ((p / 2)! : ZMod p) != 0 by
    rw [Ne]; rw [CharP.cast_eq_zero_iff (ZMod p) p]; rw [hp.1.dvd_factorial]; rw [not_le]
    exact Nat.div_lt_self hp.1.pos (by decide))).1 <| by
      simpa using gauss_lemma_aux₁ p hap

Depends on / 依赖: CharP.cast_eq_zero_iff, Nat.div_lt_self, cast_eq_zero_iff, div_lt_self, dvd_factorial, mul_left_inj, not_le
-/
theorem gauss_lemma_aux (p : Nat) [hp : Fact p.Prime] {a : Int} (hap : (a : ZMod p) != 0) :
    (a ^ (p / 2) : ZMod p) =
      ((-1) ^ #{x in Ico 1 (p / 2).succ | p / 2 < (a * x.cast : ZMod p).val} :) :=
  (mul_left_inj' (show ((p / 2)! : ZMod p) != 0 by
    rw [Ne]; rw [CharP.cast_eq_zero_iff (ZMod p) p]; rw [hp.1.dvd_factorial]; rw [not_le]
    exact Nat.div_lt_self hp.1.pos (by decide))).1 <| by
      simpa using gauss_lemma_aux₁ p hap

/--
theorem `gauss_lemma` / 定理 `gauss_lemma`

English:
theorem gauss_lemma
  given: {p : Nat} [h : Fact p.Prime] {a : Int} (hp : p != 2) (ha0 : (a : ZMod p) != 0)
  proof: by
  replace hp : Odd p := h.out.odd_of_ne_two hp
  have : (legendreSym p a : ZMod p) =
      (((-1) ^ #{x in Ico 1 (p / 2).succ | p / 2 < (a * x.cast : ZMod p).val} : Int) : ZMod p) := by
    rw [legendreSym.eq_pow]; rw [gauss_lemma_aux p ha0]
  cases legendreSym.eq_one_or_neg_one p ha0 <;>
  cases neg_one_pow_eq_or Int #{x in Ico 1 (p / 2).succ | p / 2 < (a * x.cast : ZMod p).val} <;>
  simp_all [ne_neg_self hp one_ne_zero, (ne_neg_self hp one_ne_zero).symm]

中文:
定理 gauss_lemma
  条件: {p : 自然数} [h : Fact p.素] {a : 整数} (hp : p != 2) (ha0 : (a : ZMod p) != 0)
  证明: by
  replace hp : Odd p := h.out.odd_of_ne_two hp
  have : (legendreSym p a : ZMod p) =
      (((-1) ^ #{x in Ico 1 (p / 2).succ | p / 2 < (a * x.cast : ZMod p).val} : Int) : ZMod p) := by
    rw [legendreSym.eq_pow]; rw [gauss_lemma_aux p ha0]
  cases legendreSym.eq_one_or_neg_one p ha0 <;>
  cases neg_one_pow_eq_or Int #{x in Ico 1 (p / 2).succ | p / 2 < (a * x.cast : ZMod p).val} <;>
  simp_all [ne_neg_self hp one_ne_zero, (ne_neg_self hp one_ne_zero).symm]

Depends on / 依赖: eq_one_or_neg_one, eq_pow, gauss_lemma_aux, h.out.odd_of_ne_two, legendreSym, legendreSym.eq_one_or_neg_one, legendreSym.eq_pow, ne_neg_self, neg_one_pow_eq_or, odd_of_ne_two, one_ne_zero, replace, x.cast
-/
theorem gauss_lemma {p : Nat} [h : Fact p.Prime] {a : Int} (hp : p != 2) (ha0 : (a : ZMod p) != 0) :
    legendreSym p a = (-1) ^ #{x in Ico 1 (p / 2).succ | p / 2 < (a * x.cast : ZMod p).val} := by
  replace hp : Odd p := h.out.odd_of_ne_two hp
  have : (legendreSym p a : ZMod p) =
      (((-1) ^ #{x in Ico 1 (p / 2).succ | p / 2 < (a * x.cast : ZMod p).val} : Int) : ZMod p) := by
    rw [legendreSym.eq_pow]; rw [gauss_lemma_aux p ha0]
  cases legendreSym.eq_one_or_neg_one p ha0 <;>
  cases neg_one_pow_eq_or Int #{x in Ico 1 (p / 2).succ | p / 2 < (a * x.cast : ZMod p).val} <;>
  simp_all [ne_neg_self hp one_ne_zero, (ne_neg_self hp one_ne_zero).symm]

/--
theorem `eisenstein_lemma_aux₁` / 定理 `eisenstein_lemma_aux₁`

English:
theorem eisenstein_lemma_aux₁
  statement: (p : Nat) [Fact p.Prime] [hp2 : Fact (p % 2 = 1)] {a : Nat}
  proof: have hp2 : (p : ZMod 2) = (1 : Nat) := (natCast_eq_natCast_iff _ _ _).2 hp2.1
  calc
    ((∑ x in Ico 1 (p / 2).succ, a * x : Nat) : ZMod 2) =
        ((∑ x in Ico 1 (p / 2).succ, (a * x % p + p * (a * x / p)) : Nat) : ZMod 2) := by
      simp only [mod_add_div]
    _ = (∑ x in Ico 1 (p / 2).succ, ((a * x : Nat) : ZMod p).val : Nat) +
        (∑ x in Ico 1 (p / 2).succ, a * x / p : Nat) := by
      simp only [val_natCast]
      simp [sum_add_distrib, ← mul_sum, Nat.cast_add, Nat.cast_mul, Nat.cast_sum, hp2]
    _ = _ :=
congr_arg (· + _)
        calc
          ((∑ x in Ico 1 (p / 2).succ, ((a * x : Nat) : ZMod p).val : Nat) : ZMod 2) =
              ∑ x in Ico 1 (p / 2).succ, (((a * x : ZMod p).valMinAbs +
                if (a * x : ZMod p).val <= p / 2 then 0 else p : Int) : ZMod 2) := by
            simp only [(val_eq_ite_valMinAbs _).symm]; simp [Nat.cast_sum]
          _ = #{x in Ico 1 (p / 2).succ | p / 2 < (a * x.cast : ZMod p).val} +
              (∑ x in Ico 1 (p / 2).succ, (a * x.cast : ZMod p).valMinAbs.natAbs : Nat) := by
            simp [add_comm, sum_add_distrib, Finset.sum_ite, hp2, Nat.cast_sum]
          _ = _ := by
            rw [Finset.sum_eq_multiset_sum]; rw [Ico_map_valMinAbs_natAbs_eq_Ico_map_id p a hap]; rw [←
              Finset.sum_eq_multiset_sum]

中文:
定理 eisenstein_lemma_aux₁
  结论: (p : 自然数) [Fact p.素] [hp2 : Fact (p % 2 = 1)] {a : 自然数}
  证明: have hp2 : (p : ZMod 2) = (1 : Nat) := (natCast_eq_natCast_iff _ _ _).2 hp2.1
  calc
    ((∑ x in Ico 1 (p / 2).succ, a * x : Nat) : ZMod 2) =
        ((∑ x in Ico 1 (p / 2).succ, (a * x % p + p * (a * x / p)) : Nat) : ZMod 2) := by
      simp only [mod_add_div]
    _ = (∑ x in Ico 1 (p / 2).succ, ((a * x : Nat) : ZMod p).val : Nat) +
        (∑ x in Ico 1 (p / 2).succ, a * x / p : Nat) := by
      simp only [val_natCast]
      simp [sum_add_distrib, ← mul_sum, Nat.cast_add, Nat.cast_mul, Nat.cast_sum, hp2]
    _ = _ :=
congr_arg (· + _)
        calc
          ((∑ x in Ico 1 (p / 2).succ, ((a * x : Nat) : ZMod p).val : Nat) : ZMod 2) =
              ∑ x in Ico 1 (p / 2).succ, (((a * x : ZMod p).valMinAbs +
                if (a * x : ZMod p).val <= p / 2 then 0 else p : Int) : ZMod 2) := by
            simp only [(val_eq_ite_valMinAbs _).symm]; simp [Nat.cast_sum]
          _ = #{x in Ico 1 (p / 2).succ | p / 2 < (a * x.cast : ZMod p).val} +
              (∑ x in Ico 1 (p / 2).succ, (a * x.cast : ZMod p).valMinAbs.natAbs : Nat) := by
            simp [add_comm, sum_add_distrib, Finset.sum_ite, hp2, Nat.cast_sum]
          _ = _ := by
            rw [Finset.sum_eq_multiset_sum]; rw [Ico_map_valMinAbs_natAbs_eq_Ico_map_id p a hap]; rw [←
              Finset.sum_eq_multiset_sum]
-/
private theorem eisenstein_lemma_aux₁ (p : Nat) [Fact p.Prime] [hp2 : Fact (p % 2 = 1)] {a : Nat}
    (hap : (a : ZMod p) != 0) :
    ((∑ x in Ico 1 (p / 2).succ, a * x : Nat) : ZMod 2) =
      #{x in Ico 1 (p / 2).succ | p / 2 < (a * x.cast : ZMod p).val} +
        ∑ x in Ico 1 (p / 2).succ, x + (∑ x in Ico 1 (p / 2).succ, a * x / p : Nat) :=
  have hp2 : (p : ZMod 2) = (1 : Nat) := (natCast_eq_natCast_iff _ _ _).2 hp2.1
  calc
    ((∑ x in Ico 1 (p / 2).succ, a * x : Nat) : ZMod 2) =
        ((∑ x in Ico 1 (p / 2).succ, (a * x % p + p * (a * x / p)) : Nat) : ZMod 2) := by
      simp only [mod_add_div]
    _ = (∑ x in Ico 1 (p / 2).succ, ((a * x : Nat) : ZMod p).val : Nat) +
        (∑ x in Ico 1 (p / 2).succ, a * x / p : Nat) := by
      simp only [val_natCast]
      simp [sum_add_distrib, ← mul_sum, Nat.cast_add, Nat.cast_mul, Nat.cast_sum, hp2]
    _ = _ :=
congr_arg (· + _)
        calc
          ((∑ x in Ico 1 (p / 2).succ, ((a * x : Nat) : ZMod p).val : Nat) : ZMod 2) =
              ∑ x in Ico 1 (p / 2).succ, (((a * x : ZMod p).valMinAbs +
                if (a * x : ZMod p).val <= p / 2 then 0 else p : Int) : ZMod 2) := by
            simp only [(val_eq_ite_valMinAbs _).symm]; simp [Nat.cast_sum]
          _ = #{x in Ico 1 (p / 2).succ | p / 2 < (a * x.cast : ZMod p).val} +
              (∑ x in Ico 1 (p / 2).succ, (a * x.cast : ZMod p).valMinAbs.natAbs : Nat) := by
            simp [add_comm, sum_add_distrib, Finset.sum_ite, hp2, Nat.cast_sum]
          _ = _ := by
            rw [Finset.sum_eq_multiset_sum]; rw [Ico_map_valMinAbs_natAbs_eq_Ico_map_id p a hap]; rw [←
              Finset.sum_eq_multiset_sum]

/--
theorem `eisenstein_lemma_aux` / 定理 `eisenstein_lemma_aux`

English:
theorem eisenstein_lemma_aux
  statement: (p : Nat) [Fact p.Prime] [Fact (p % 2 = 1)] {a : Nat} (ha2 : a % 2 = 1)
  proof: have ha2 : (a : ZMod 2) = (1 : Nat) := (natCast_eq_natCast_iff _ _ _).2 ha2
(natCast_eq_natCast_iff _ _ 2).1 sub_eq_zero.1 by
    simpa [add_left_comm, sub_eq_add_neg, ← mul_sum, mul_comm, ha2, Nat.cast_sum,
      add_neg_eq_iff_eq_add.symm, add_assoc] using
      Eq.symm (eisenstein_lemma_aux₁ p hap)

中文:
定理 eisenstein_lemma_aux
  结论: (p : 自然数) [Fact p.素] [Fact (p % 2 = 1)] {a : 自然数} (ha2 : a % 2 = 1)
  证明: have ha2 : (a : ZMod 2) = (1 : Nat) := (natCast_eq_natCast_iff _ _ _).2 ha2
(natCast_eq_natCast_iff _ _ 2).1 sub_eq_zero.1 by
    simpa [add_left_comm, sub_eq_add_neg, ← mul_sum, mul_comm, ha2, Nat.cast_sum,
      add_neg_eq_iff_eq_add.symm, add_assoc] using
      Eq.symm (eisenstein_lemma_aux₁ p hap)

Depends on / 依赖: Eq.symm, Nat.cast_sum, add_assoc, add_left_comm, add_neg_eq_iff_eq_add, add_neg_eq_iff_eq_add.symm, cast_sum, mul_comm, mul_sum, natCast_eq_natCast_iff, sub_eq_add_neg, sub_eq_zero
-/
theorem eisenstein_lemma_aux (p : Nat) [Fact p.Prime] [Fact (p % 2 = 1)] {a : Nat} (ha2 : a % 2 = 1)
    (hap : (a : ZMod p) != 0) :
    #{x in Ico 1 (p / 2).succ | p / 2 < (a * x.cast : ZMod p).val} ≡
      ∑ x in Ico 1 (p / 2).succ, x * a / p [MOD 2] :=
  have ha2 : (a : ZMod 2) = (1 : Nat) := (natCast_eq_natCast_iff _ _ _).2 ha2
(natCast_eq_natCast_iff _ _ 2).1 sub_eq_zero.1 by
    simpa [add_left_comm, sub_eq_add_neg, ← mul_sum, mul_comm, ha2, Nat.cast_sum,
      add_neg_eq_iff_eq_add.symm, add_assoc] using
      Eq.symm (eisenstein_lemma_aux₁ p hap)

/--
theorem `div_eq_filter_card` / 定理 `div_eq_filter_card`

English:
theorem div_eq_filter_card
  given: {a b c : Nat} (hb0 : 0 < b) (hc : a / b <= c)
  proof: calc
    a / b = #(Ico 1 (a / b).succ) := by simp
    _ = #{x in Ico 1 c.succ | x * b <= a} :=
congr_arg _ Finset.ext fun x => by
        have : x * b <= a -> x <= c := fun h => le_trans (by rwa [le_div_iff_mul_le hb0]) hc
        simp [le_div_iff_mul_le hb0]; tauto

中文:
定理 div_eq_filter_card
  条件: {a b c : 自然数} (hb0 : 0 < b) (hc : a / b <= c)
  证明: calc
    a / b = #(Ico 1 (a / b).succ) := by simp
    _ = #{x in Ico 1 c.succ | x * b <= a} :=
congr_arg _ Finset.ext fun x => by
        have : x * b <= a -> x <= c := fun h => le_trans (by rwa [le_div_iff_mul_le hb0]) hc
        simp [le_div_iff_mul_le hb0]; tauto

Depends on / 依赖: Finset, Finset.ext, c.succ, congr_arg, le_div_iff_mul_le, le_trans
-/
theorem div_eq_filter_card {a b c : Nat} (hb0 : 0 < b) (hc : a / b <= c) :
    a / b = #{x in Ico 1 c.succ | x * b <= a} :=
  calc
    a / b = #(Ico 1 (a / b).succ) := by simp
    _ = #{x in Ico 1 c.succ | x * b <= a} :=
congr_arg _ Finset.ext fun x => by
        have : x * b <= a -> x <= c := fun h => le_trans (by rwa [le_div_iff_mul_le hb0]) hc
        simp [le_div_iff_mul_le hb0]; tauto

/--
theorem `sum_Ico_eq_card_lt` / 定理 `sum_Ico_eq_card_lt`

English:
theorem sum_Ico_eq_card_lt
  given: {p q : Nat}
  proof: if hp0 : p = 0 then by simp [hp0]
  else
    calc
      ∑ a in Ico 1 (p / 2).succ, a * q / p =
          ∑ a in Ico 1 (p / 2).succ, #{x in Ico 1 (q / 2).succ | x * p <= a * q} :=
Finset.sum_congr rfl fun x hx => div_eq_filter_card (Nat.pos_of_ne_zero hp0)
          calc
            x * q / p <= p / 2 * q / p := by have := le_of_lt_succ (mem_Ico.mp hx).2; gcongr
            _ <= _ := Nat.div_mul_div_le_div _ _ _
      _ = _ := by simp only [card_eq_sum_ones, sum_filter, sum_product]

中文:
定理 sum_Ico_eq_card_lt
  条件: {p q : 自然数}
  证明: if hp0 : p = 0 then by simp [hp0]
  else
    calc
      ∑ a in Ico 1 (p / 2).succ, a * q / p =
          ∑ a in Ico 1 (p / 2).succ, #{x in Ico 1 (q / 2).succ | x * p <= a * q} :=
Finset.sum_congr rfl fun x hx => div_eq_filter_card (Nat.pos_of_ne_zero hp0)
          calc
            x * q / p <= p / 2 * q / p := by have := le_of_lt_succ (mem_Ico.mp hx).2; gcongr
            _ <= _ := Nat.div_mul_div_le_div _ _ _
      _ = _ := by simp only [card_eq_sum_ones, sum_filter, sum_product]
-/
private theorem sum_Ico_eq_card_lt {p q : Nat} :
    ∑ a in Ico 1 (p / 2).succ, a * q / p =
      #{x in Ico 1 (p / 2).succ ×ˢ Ico 1 (q / 2).succ | x.2 * p <= x.1 * q} :=
  if hp0 : p = 0 then by simp [hp0]
  else
    calc
      ∑ a in Ico 1 (p / 2).succ, a * q / p =
          ∑ a in Ico 1 (p / 2).succ, #{x in Ico 1 (q / 2).succ | x * p <= a * q} :=
Finset.sum_congr rfl fun x hx => div_eq_filter_card (Nat.pos_of_ne_zero hp0)
          calc
            x * q / p <= p / 2 * q / p := by have := le_of_lt_succ (mem_Ico.mp hx).2; gcongr
            _ <= _ := Nat.div_mul_div_le_div _ _ _
      _ = _ := by simp only [card_eq_sum_ones, sum_filter, sum_product]

/--
theorem `sum_mul_div_add_sum_mul_div_eq_mul` / 定理 `sum_mul_div_add_sum_mul_div_eq_mul`

English:
theorem sum_mul_div_add_sum_mul_div_eq_mul
  given: (p q : Nat) [hp : Fact p.Prime] (hq0 : (q : ZMod p) != 0)
  proof: by
  have hswap :
    #{x in Ico 1 (q / 2).succ ×ˢ Ico 1 (p / 2).succ | x.2 * q <= x.1 * p} =
      #{x in Ico 1 (p / 2).succ ×ˢ Ico 1 (q / 2).succ | x.1 * q <= x.2 * p} :=
    card_equiv (Equiv.prodComm _ _)
      (fun ⟨_, _⟩ => by
        simp +contextual only [mem_filter, Prod.swap_prod_mk,
          mem_product, Equiv.prodComm_apply, and_assoc, and_left_comm])
  have hdisj :
    Disjoint {x in Ico 1 (p / 2).succ ×ˢ Ico 1 (q / 2).succ | x.2 * p <= x.1 * q}
      {x in Ico 1 (p / 2).succ ×ˢ Ico 1 (q / 2).succ | x.1 * q <= x.2 * p} := by
    apply disjoint_filter.2 fun x hx hpq hqp => ?_
    have hxp : x.1 < p := lt_of_le_of_lt (b := p / 2)
      (by grind) (Nat.div_lt_self hp.1.pos (by decide))
    have : (x.1 : ZMod p) = 0 := by
      simpa [hq0] using congr_arg ((↑) : Nat -> ZMod p) (le_antisymm hpq hqp)
    apply_fun ZMod.val at this
    rw [val_cast_of_lt hxp]; rw [val_zero] at this
    simp only [this, nonpos_iff_eq_zero, mem_Ico, one_ne_zero, false_and, mem_product] at hx
  have hunion :
      {x in Ico 1 (p / 2).succ ×ˢ Ico 1 (q / 2).succ | x.2 * p <= x.1 * q} union
        {x in Ico 1 (p / 2).succ ×ˢ Ico 1 (q / 2).succ | x.1 * q <= x.2 * p} =
      Ico 1 (p / 2).succ ×ˢ Ico 1 (q / 2).succ :=
    Finset.ext fun x => by
      have := le_total (x.2 * p) (x.1 * q)
      simp only [mem_union, mem_filter, mem_Ico, mem_product]
      tauto
  rw [sum_Ico_eq_card_lt]; rw [sum_Ico_eq_card_lt]; rw [hswap]; rw [← card_union_of_disjoint hdisj]; rw [hunion]; rw [card_product]
  simp only [card_Ico, succ_sub_succ_eq_sub, Nat.sub_zero]

中文:
定理 sum_mul_div_add_sum_mul_div_eq_mul
  条件: (p q : 自然数) [hp : Fact p.素] (hq0 : (q : ZMod p) != 0)
  证明: by
  have hswap :
    #{x in Ico 1 (q / 2).succ ×ˢ Ico 1 (p / 2).succ | x.2 * q <= x.1 * p} =
      #{x in Ico 1 (p / 2).succ ×ˢ Ico 1 (q / 2).succ | x.1 * q <= x.2 * p} :=
    card_equiv (Equiv.prodComm _ _)
      (fun ⟨_, _⟩ => by
        simp +contextual only [mem_filter, Prod.swap_prod_mk,
          mem_product, Equiv.prodComm_apply, and_assoc, and_left_comm])
  have hdisj :
    Disjoint {x in Ico 1 (p / 2).succ ×ˢ Ico 1 (q / 2).succ | x.2 * p <= x.1 * q}
      {x in Ico 1 (p / 2).succ ×ˢ Ico 1 (q / 2).succ | x.1 * q <= x.2 * p} := by
    apply disjoint_filter.2 fun x hx hpq hqp => ?_
    have hxp : x.1 < p := lt_of_le_of_lt (b := p / 2)
      (by grind) (Nat.div_lt_self hp.1.pos (by decide))
    have : (x.1 : ZMod p) = 0 := by
      simpa [hq0] using congr_arg ((↑) : Nat -> ZMod p) (le_antisymm hpq hqp)
    apply_fun ZMod.val at this
    rw [val_cast_of_lt hxp]; rw [val_zero] at this
    simp only [this, nonpos_iff_eq_zero, mem_Ico, one_ne_zero, false_and, mem_product] at hx
  have hunion :
      {x in Ico 1 (p / 2).succ ×ˢ Ico 1 (q / 2).succ | x.2 * p <= x.1 * q} union
        {x in Ico 1 (p / 2).succ ×ˢ Ico 1 (q / 2).succ | x.1 * q <= x.2 * p} =
      Ico 1 (p / 2).succ ×ˢ Ico 1 (q / 2).succ :=
    Finset.ext fun x => by
      have := le_total (x.2 * p) (x.1 * q)
      simp only [mem_union, mem_filter, mem_Ico, mem_product]
      tauto
  rw [sum_Ico_eq_card_lt]; rw [sum_Ico_eq_card_lt]; rw [hswap]; rw [← card_union_of_disjoint hdisj]; rw [hunion]; rw [card_product]
  simp only [card_Ico, succ_sub_succ_eq_sub, Nat.sub_zero]

Depends on / 依赖: Disjoint, Equiv.prodComm, Equiv.prodComm_apply, Prod.swap_prod_mk, and_assoc, and_left_comm, card_equiv, contextual, mem_filter, mem_product, prodComm, prodComm_apply, swap_prod_mk
-/
theorem sum_mul_div_add_sum_mul_div_eq_mul (p q : Nat) [hp : Fact p.Prime] (hq0 : (q : ZMod p) != 0) :
    ∑ a in Ico 1 (p / 2).succ, a * q / p + ∑ a in Ico 1 (q / 2).succ, a * p / q =
    p / 2 * (q / 2) := by
  have hswap :
    #{x in Ico 1 (q / 2).succ ×ˢ Ico 1 (p / 2).succ | x.2 * q <= x.1 * p} =
      #{x in Ico 1 (p / 2).succ ×ˢ Ico 1 (q / 2).succ | x.1 * q <= x.2 * p} :=
    card_equiv (Equiv.prodComm _ _)
      (fun ⟨_, _⟩ => by
        simp +contextual only [mem_filter, Prod.swap_prod_mk,
          mem_product, Equiv.prodComm_apply, and_assoc, and_left_comm])
  have hdisj :
    Disjoint {x in Ico 1 (p / 2).succ ×ˢ Ico 1 (q / 2).succ | x.2 * p <= x.1 * q}
      {x in Ico 1 (p / 2).succ ×ˢ Ico 1 (q / 2).succ | x.1 * q <= x.2 * p} := by
    apply disjoint_filter.2 fun x hx hpq hqp => ?_
    have hxp : x.1 < p := lt_of_le_of_lt (b := p / 2)
      (by grind) (Nat.div_lt_self hp.1.pos (by decide))
    have : (x.1 : ZMod p) = 0 := by
      simpa [hq0] using congr_arg ((↑) : Nat -> ZMod p) (le_antisymm hpq hqp)
    apply_fun ZMod.val at this
    rw [val_cast_of_lt hxp]; rw [val_zero] at this
    simp only [this, nonpos_iff_eq_zero, mem_Ico, one_ne_zero, false_and, mem_product] at hx
  have hunion :
      {x in Ico 1 (p / 2).succ ×ˢ Ico 1 (q / 2).succ | x.2 * p <= x.1 * q} union
        {x in Ico 1 (p / 2).succ ×ˢ Ico 1 (q / 2).succ | x.1 * q <= x.2 * p} =
      Ico 1 (p / 2).succ ×ˢ Ico 1 (q / 2).succ :=
    Finset.ext fun x => by
      have := le_total (x.2 * p) (x.1 * q)
      simp only [mem_union, mem_filter, mem_Ico, mem_product]
      tauto
  rw [sum_Ico_eq_card_lt]; rw [sum_Ico_eq_card_lt]; rw [hswap]; rw [← card_union_of_disjoint hdisj]; rw [hunion]; rw [card_product]
  simp only [card_Ico, succ_sub_succ_eq_sub, Nat.sub_zero]

/--
theorem `eisenstein_lemma` / 定理 `eisenstein_lemma`

English:
theorem eisenstein_lemma
  statement: {p : Nat} [Fact p.Prime] (hp : p != 2) {a : Nat} (ha1 : a % 2 = 1)
  proof: by
  have hp' : Fact (p % 2 = 1) := ⟨(Nat.Prime.mod_two_eq_one_iff_ne_two Fact.out).mpr hp⟩
  have ha0' : ((a : Int) : ZMod p) != 0 := by norm_cast
  rw [neg_one_pow_eq_pow_mod_two]; rw [gauss_lemma hp ha0']; rw [neg_one_pow_eq_pow_mod_two]; rw [(by norm_cast : ((a : Int) : ZMod p) = (a : ZMod p))]; rw [show _ = _ from eisenstein_lemma_aux p ha1 ha0]

中文:
定理 eisenstein_lemma
  结论: {p : 自然数} [Fact p.素] (hp : p != 2) {a : 自然数} (ha1 : a % 2 = 1)
  证明: by
  have hp' : Fact (p % 2 = 1) := ⟨(Nat.Prime.mod_two_eq_one_iff_ne_two Fact.out).mpr hp⟩
  have ha0' : ((a : Int) : ZMod p) != 0 := by norm_cast
  rw [neg_one_pow_eq_pow_mod_two]; rw [gauss_lemma hp ha0']; rw [neg_one_pow_eq_pow_mod_two]; rw [(by norm_cast : ((a : Int) : ZMod p) = (a : ZMod p))]; rw [show _ = _ from eisenstein_lemma_aux p ha1 ha0]

Depends on / 依赖: Fact.out, Nat.Prime.mod_two_eq_one_iff_ne_two, eisenstein_lemma_aux, gauss_lemma, mod_two_eq_one_iff_ne_two, neg_one_pow_eq_pow_mod_two
-/
theorem eisenstein_lemma {p : Nat} [Fact p.Prime] (hp : p != 2) {a : Nat} (ha1 : a % 2 = 1)
    (ha0 : (a : ZMod p) != 0) : legendreSym p a = (-1) ^ ∑ x in Ico 1 (p / 2).succ, x * a / p := by
  have hp' : Fact (p % 2 = 1) := ⟨(Nat.Prime.mod_two_eq_one_iff_ne_two Fact.out).mpr hp⟩
  have ha0' : ((a : Int) : ZMod p) != 0 := by norm_cast
  rw [neg_one_pow_eq_pow_mod_two]; rw [gauss_lemma hp ha0']; rw [neg_one_pow_eq_pow_mod_two]; rw [(by norm_cast : ((a : Int) : ZMod p) = (a : ZMod p))]; rw [show _ = _ from eisenstein_lemma_aux p ha1 ha0]

end ZMod

end GaussEisenstein
