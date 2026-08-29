/-
Copyright (c) 2022 John Nicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Nicol
-/
module

public import Mathlib.FieldTheory.Finite.Basic

/-!
# Wilson's theorem.

This file contains a proof of Wilson's theorem.

The heavy lifting is mostly done by the previous `wilsons_lemma`,
but here we also prove the other logical direction.

This could be generalized to similar results about finite abelian groups.

## References

* [Wilson's Theorem](https://en.wikipedia.org/wiki/Wilson%27s_theorem)

## TODO

* Give `wilsons_lemma` a descriptive name.
-/

public section

assert_not_exists legendreSym.quadratic_reciprocity

open Finset Nat FiniteField ZMod

open scoped Nat

namespace ZMod

variable (p : Nat) [Fact p.Prime]

/-- **Wilson's Lemma**: the product of `1`, ..., `p-1` is `-1` modulo `p`. -/
@[simp]
/--
theorem `wilsons_lemma` / 定理 `wilsons_lemma`

English:
theorem wilsons_lemma
  statement: ((p - 1)! : ZMod p) = -1
  proof: by
  refine
    calc
      ((p - 1)! : ZMod p) = ∏ x in Ico 1 (succ (p - 1)), (x : ZMod p) := by
        rw [← Finset.prod_Ico_id_eq_factorial]; rw [prod_natCast]
      _ = ∏ x : (ZMod p)ˣ, (x : ZMod p) := ?_
      _ = -1 := by
        simp_rw [← Units.coeHom_apply, ← map_prod (Units.coeHom (ZMod p)

中文:
定理 wilsons_lemma
  结论: ((p - 1)! : ZMod p) = -1
  证明: by
  refine
    calc
      ((p - 1)! : ZMod p) = ∏ x in Ico 1 (succ (p - 1)), (x : ZMod p) := by
        rw [← Finset.prod_Ico_id_eq_factorial]; rw [prod_natCast]
      _ = ∏ x : (ZMod p)ˣ, (x : ZMod p) := ?_
      _ = -1 := by
        simp_rw [← Units.coeHom_apply, ← map_prod (Units.coeHom (ZMod p)

Depends on / 依赖: Fact.out, Finset, Finset.prod_Ico_id_eq_factorial, Nat.succ_su, Units.coeHom, Units.coeHom_apply, Units.val_neg, Units.val_one, coeHom, coeHom_apply, map_prod, mem_Ico, p.Prime, prod_Ico_id_eq_factorial, prod_bij, prod_natCast, prod_univ_units_id_eq_neg_one, simp_rw, succ_su, val_neg
-/
theorem wilsons_lemma : ((p - 1)! : ZMod p) = -1 := by
  refine
    calc
      ((p - 1)! : ZMod p) = ∏ x in Ico 1 (succ (p - 1)), (x : ZMod p) := by
        rw [← Finset.prod_Ico_id_eq_factorial]; rw [prod_natCast]
      _ = ∏ x : (ZMod p)ˣ, (x : ZMod p) := ?_
      _ = -1 := by
        simp_rw [← Units.coeHom_apply, ← map_prod (Units.coeHom (ZMod p)),
          prod_univ_units_id_eq_neg_one, Units.coeHom_apply, Units.val_neg, Units.val_one]
  have hp : 0 < p := (Fact.out (p := p.Prime)).pos
  symm
  refine prod_bij (fun a _ => (a : ZMod p).val) ?_ ?_ ?_ ?_
  · intro a ha
    rw [mem_Ico]; rw [← Nat.succ_sub hp]; rw [Nat.add_one_sub_one]
    constructor
    · apply Nat.pos_of_ne_zero; rw [← @val_zero p]
      intro h; apply Units.ne_zero a (val_injective p h)
    · exact val_lt _
  · intro _ _ _ _ h; rw [Units.ext_iff]; exact val_injective p h
  · intro b hb
    rw [mem_Ico]; rw [Nat.succ_le_iff]; rw [← succ_sub hp]; rw [Nat.add_one_sub_one]; rw [pos_iff_ne_zero] at hb
    refine ⟨Units.mk0 b ?_, Finset.mem_univ _, ?_⟩
    · intro h; apply hb.1; apply_fun val at h
      simpa only [val_cast_of_lt hb.right, val_zero] using h
    · simp only [val_cast_of_lt hb.right, Units.val_mk0]
  · rintro a -; simp only [cast_id, natCast_val]

@[simp]
/--
theorem `prod_Ico_one_prime` / 定理 `prod_Ico_one_prime`

English:
theorem prod_Ico_one_prime
  statement: ∏ x in Ico 1 p, (x : ZMod p) = -1
  proof: by
  -- Porting note: was `conv in Ico 1 p =>`
  conv =>
    congr
    congr
    rw [← Nat.add_one_sub_one p]; rw [succ_sub (Fact.out (p := p.Prime)).pos]
  rw [← prod_natCast]; rw [Finset.prod_Ico_id_eq_factorial]; rw [wilsons_lemma]

中文:
定理 prod_Ico_one_prime
  结论: ∏ x in Ico 1 p, (x : ZMod p) = -1
  证明: by
  -- Porting note: was `conv in Ico 1 p =>`
  conv =>
    congr
    congr
    rw [← Nat.add_one_sub_one p]; rw [succ_sub (Fact.out (p := p.Prime)).pos]
  rw [← prod_natCast]; rw [Finset.prod_Ico_id_eq_factorial]; rw [wilsons_lemma]
-/
theorem prod_Ico_one_prime : ∏ x in Ico 1 p, (x : ZMod p) = -1 := by
  -- Porting note: was `conv in Ico 1 p =>`
  conv =>
    congr
    congr
    rw [← Nat.add_one_sub_one p]; rw [succ_sub (Fact.out (p := p.Prime)).pos]
  rw [← prod_natCast]; rw [Finset.prod_Ico_id_eq_factorial]; rw [wilsons_lemma]

end ZMod

namespace Nat

variable {n : Nat}

/--
theorem `prime_of_fac_equiv_neg_one` / 定理 `prime_of_fac_equiv_neg_one`

English:
theorem prime_of_fac_equiv_neg_one
  given: (h : ((n - 1)! : ZMod n) = -1) (h1 : n != 1)
  statement: Prime n
  proof: by
  rcases eq_or_ne n 0 with (rfl | h0)
  · norm_num at h
  replace h1 : 1 < n := n.two_le_iff.mpr ⟨h0, h1⟩
  by_contra h2
  obtain ⟨m, hm1, hm2 : 1 < m, hm3⟩ := exists_dvd_of_not_prime2 h1 h2
  have hm : m ∣ (n - 1)! := Nat.dvd_factorial (pos_of_gt hm2) (le_pred_of_lt hm3)
  refine hm2.ne' (Nat.dv

中文:
定理 prime_of_fac_equiv_neg_one
  条件: (h : ((n - 1)! : ZMod n) = -1) (h1 : n != 1)
  结论: Prime n
  证明: by
  rcases eq_or_ne n 0 with (rfl | h0)
  · norm_num at h
  replace h1 : 1 < n := n.two_le_iff.mpr ⟨h0, h1⟩
  by_contra h2
  obtain ⟨m, hm1, hm2 : 1 < m, hm3⟩ := exists_dvd_of_not_prime2 h1 h2
  have hm : m ∣ (n - 1)! := Nat.dvd_factorial (pos_of_gt hm2) (le_pred_of_lt hm3)
  refine hm2.ne' (Nat.dv

Depends on / 依赖: Nat.dvd_add_right, Nat.dvd_factorial, Nat.dvd_one.mp, ZMod.natCast_eq_zero_iff, cast_add, cast_one, dvd_add_right, dvd_factorial, dvd_one, eq_or_ne, exists_dvd_of_not_prime2, hm1.trans, hm2.ne, le_pred_of_lt, n.two_le_iff.mpr, natCast_eq_zero_iff, neg_add_cancel, pos_of_gt, replace, two_le_iff
-/
theorem prime_of_fac_equiv_neg_one (h : ((n - 1)! : ZMod n) = -1) (h1 : n != 1) : Prime n := by
  rcases eq_or_ne n 0 with (rfl | h0)
  · norm_num at h
  replace h1 : 1 < n := n.two_le_iff.mpr ⟨h0, h1⟩
  by_contra h2
  obtain ⟨m, hm1, hm2 : 1 < m, hm3⟩ := exists_dvd_of_not_prime2 h1 h2
  have hm : m ∣ (n - 1)! := Nat.dvd_factorial (pos_of_gt hm2) (le_pred_of_lt hm3)
  refine hm2.ne' (Nat.dvd_one.mp ((Nat.dvd_add_right hm).mp (hm1.trans ?_)))
  rw [← ZMod.natCast_eq_zero_iff]; rw [cast_add]; rw [cast_one]; rw [h]; rw [neg_add_cancel]

/--
theorem `prime_iff_fac_equiv_neg_one` / 定理 `prime_iff_fac_equiv_neg_one`

English:
theorem prime_iff_fac_equiv_neg_one
  given: (h : n != 1)
  statement: Prime n ↔ ((n - 1)! : ZMod n) = -1
  proof: by
  refine ⟨fun h1 => ?_, fun h2 => prime_of_fac_equiv_neg_one h2 h⟩
  have := Fact.mk h1
  exact ZMod.wilsons_lemma n

中文:
定理 prime_iff_fac_equiv_neg_one
  条件: (h : n != 1)
  结论: Prime n ↔ ((n - 1)! : ZMod n) = -1
  证明: by
  refine ⟨fun h1 => ?_, fun h2 => prime_of_fac_equiv_neg_one h2 h⟩
  have := Fact.mk h1
  exact ZMod.wilsons_lemma n

Depends on / 依赖: Fact.mk, ZMod.wilsons_lemma, prime_of_fac_equiv_neg_one, wilsons_lemma
-/
theorem prime_iff_fac_equiv_neg_one (h : n != 1) : Prime n ↔ ((n - 1)! : ZMod n) = -1 := by
  refine ⟨fun h1 => ?_, fun h2 => prime_of_fac_equiv_neg_one h2 h⟩
  have := Fact.mk h1
  exact ZMod.wilsons_lemma n

end Nat
