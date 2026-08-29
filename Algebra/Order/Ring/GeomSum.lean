/-
Copyright (c) 2019 Neil Strickland. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Neil Strickland
-/
module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Ring.GeomSum

/-!
# Partial sums of geometric series in an ordered ring

This file upper- and lower-bounds the values of the geometric series $\sum_{i=0}^{n-1} x^i$ and
$\sum_{i=0}^{n-1} x^i y^{n-1-i}$ and variants thereof. We also provide some bounds on the
"geometric" sum of `a/b^i` where `a b : ℕ`.
-/

public section

assert_not_exists Field

open Finset MulOpposite

variable {R : Type*}

section Semiring
variable [Semiring R] [PartialOrder R] [IsStrictOrderedRing R] {n : Nat} {x : R}

/--
lemma `geom_sum_pos` / 引理 `geom_sum_pos`

English:
lemma geom_sum_pos
  given: (hx : 0 <= x) (hn : n != 0)
  statement: 0 < ∑ i in range n, x ^ i
  proof: sum_pos' (fun _ _ => pow_nonneg hx _) ⟨0, mem_range.2 hn.bot_lt, by simp⟩

中文:
引理 geom_sum_pos
  条件: (hx : 0 <= x) (hn : n != 0)
  结论: 0 < ∑ i in range n, x ^ i
  证明: sum_pos' (fun _ _ => pow_nonneg hx _) ⟨0, mem_range.2 hn.bot_lt, by simp⟩

Depends on / 依赖: bot_lt, hn.bot_lt, mem_range, pow_nonneg, sum_pos
-/
lemma geom_sum_pos (hx : 0 <= x) (hn : n != 0) : 0 < ∑ i in range n, x ^ i :=
  sum_pos' (fun _ _ => pow_nonneg hx _) ⟨0, mem_range.2 hn.bot_lt, by simp⟩

end Semiring

section Ring
variable [Ring R]

section PartialOrder
variable [PartialOrder R]

section IsOrderedRing
variable [IsOrderedRing R] {x : R}

/--
lemma `geom_sum_alternating_of_le_neg_one` / 引理 `geom_sum_alternating_of_le_neg_one`

English:
lemma geom_sum_alternating_of_le_neg_one
  given: (hx : x + 1 <= 0) (n : Nat)
  proof: by
  have hx0 : x <= 0 := (le_add_of_nonneg_right zero_le_one).trans hx
  induction n with
  | zero => simp only [range_zero, sum_empty, le_refl, ite_true, Even.zero]
  | succ n ih =>
    simp only [Nat.even_add_one, geom_sum_succ]
    split_ifs at ih ⊢ with h
    · rw [le_add_iff_nonneg_left]
     

中文:
引理 geom_sum_alternating_of_le_neg_one
  条件: (hx : x + 1 <= 0) (n : 自然数)
  证明: by
  have hx0 : x <= 0 := (le_add_of_nonneg_right zero_le_one).trans hx
  induction n with
  | zero => simp only [range_zero, sum_empty, le_refl, ite_true, Even.zero]
  | succ n ih =>
    simp only [Nat.even_add_one, geom_sum_succ]
    split_ifs at ih ⊢ with h
    · rw [le_add_iff_nonneg_left]
     

Depends on / 依赖: Even.zero, Nat.even_add_one, even_add_one, geom_sum_succ, ite_true, le_add_iff_nonneg_left, le_add_of_nonneg_right, le_refl, mul_le_mul_of_nonpos_left, mul_nonneg_of_nonpos_of_nonpos, mul_one, range_zero, split_ifs, sum_empty, zero_le_one
-/
lemma geom_sum_alternating_of_le_neg_one (hx : x + 1 <= 0) (n : Nat) :
    if Even n then (∑ i in range n, x ^ i) <= 0 else 1 <= ∑ i in range n, x ^ i := by
  have hx0 : x <= 0 := (le_add_of_nonneg_right zero_le_one).trans hx
  induction n with
  | zero => simp only [range_zero, sum_empty, le_refl, ite_true, Even.zero]
  | succ n ih =>
    simp only [Nat.even_add_one, geom_sum_succ]
    split_ifs at ih ⊢ with h
    · rw [le_add_iff_nonneg_left]
      exact mul_nonneg_of_nonpos_of_nonpos hx0 ih
    · grw [← hx]
      gcongr
      simpa only [mul_one] using mul_le_mul_of_nonpos_left ih hx0

end IsOrderedRing

section IsStrictOrderedRing
variable [IsStrictOrderedRing R] {n : Nat} {x : R}

/--
lemma `geom_sum_pos_and_lt_one` / 引理 `geom_sum_pos_and_lt_one`

English:
lemma geom_sum_pos_and_lt_one
  given: (hx : x < 0) (hx' : 0 < x + 1) (hn : 1 < n)
  proof: by
  refine Nat.le_induction ?_ ?_ n (show 2 <= n from hn)
  · rw [geom_sum_two]
    exact ⟨hx', (add_lt_iff_neg_right _).2 hx⟩
  clear hn
  intro n _ ihn
  rw [geom_sum_succ]; rw [add_lt_iff_neg_right]; rw [← neg_lt_iff_pos_add']; rw [neg_mul_eq_neg_mul]
  exact
    ⟨mul_lt_one_of_nonneg_of_lt_one_

中文:
引理 geom_sum_pos_and_lt_one
  条件: (hx : x < 0) (hx' : 0 < x + 1) (hn : 1 < n)
  证明: by
  refine Nat.le_induction ?_ ?_ n (show 2 <= n from hn)
  · rw [geom_sum_two]
    exact ⟨hx', (add_lt_iff_neg_right _).2 hx⟩
  clear hn
  intro n _ ihn
  rw [geom_sum_succ]; rw [add_lt_iff_neg_right]; rw [← neg_lt_iff_pos_add']; rw [neg_mul_eq_neg_mul]
  exact
    ⟨mul_lt_one_of_nonneg_of_lt_one_

Depends on / 依赖: Nat.le_induction, add_lt_iff_neg_right, geom_sum_succ, geom_sum_two, hx.le, le_induction, mul_lt_one_of_nonneg_of_lt_one_left, mul_neg_of_neg_of_pos, neg_lt_iff_pos_add, neg_mul_eq_neg_mul, neg_nonneg
-/
lemma geom_sum_pos_and_lt_one (hx : x < 0) (hx' : 0 < x + 1) (hn : 1 < n) :
    0 < ∑ i in range n, x ^ i ∧ ∑ i in range n, x ^ i < 1 := by
  refine Nat.le_induction ?_ ?_ n (show 2 <= n from hn)
  · rw [geom_sum_two]
    exact ⟨hx', (add_lt_iff_neg_right _).2 hx⟩
  clear hn
  intro n _ ihn
  rw [geom_sum_succ]; rw [add_lt_iff_neg_right]; rw [← neg_lt_iff_pos_add']; rw [neg_mul_eq_neg_mul]
  exact
    ⟨mul_lt_one_of_nonneg_of_lt_one_left (neg_nonneg.2 hx.le) (neg_lt_iff_pos_add'.2 hx') ihn.2.le,
      mul_neg_of_neg_of_pos hx ihn.1⟩

/--
lemma `geom_sum_alternating_of_lt_neg_one` / 引理 `geom_sum_alternating_of_lt_neg_one`

English:
lemma geom_sum_alternating_of_lt_neg_one
  given: (hx : x + 1 < 0) (hn : 1 < n)
  proof: by
  have hx0 : x < 0 := (le_add_of_nonneg_right zero_le_one).trans_lt hx
  refine Nat.le_induction ?_ ?_ n (show 2 <= n from hn)
  · simp only [geom_sum_two, lt_add_iff_pos_left, ite_true, hx, even_two]
  clear hn
  intro n _ ihn
  simp only [Nat.even_add_one, geom_sum_succ]
  split_ifs at ihn ⊢ wi

中文:
引理 geom_sum_alternating_of_lt_neg_one
  条件: (hx : x + 1 < 0) (hn : 1 < n)
  证明: by
  have hx0 : x < 0 := (le_add_of_nonneg_right zero_le_one).trans_lt hx
  refine Nat.le_induction ?_ ?_ n (show 2 <= n from hn)
  · simp only [geom_sum_two, lt_add_iff_pos_left, ite_true, hx, even_two]
  clear hn
  intro n _ ihn
  simp only [Nat.even_add_one, geom_sum_succ]
  split_ifs at ihn ⊢ wi

Depends on / 依赖: Nat.even_add_one, Nat.le_induction, even_add_one, even_two, geom_sum_succ, geom_sum_two, hx.le, ite_true, le_add_of_nonneg_right, le_induction, lt_add_iff_pos_left, mul_lt_mul_of_neg_left, mul_one, mul_pos_of_neg_of_neg, split_ifs, trans_lt, zero_le_one
-/
lemma geom_sum_alternating_of_lt_neg_one (hx : x + 1 < 0) (hn : 1 < n) :
    if Even n then ∑ i in range n, x ^ i < 0 else 1 < ∑ i in range n, x ^ i := by
  have hx0 : x < 0 := (le_add_of_nonneg_right zero_le_one).trans_lt hx
  refine Nat.le_induction ?_ ?_ n (show 2 <= n from hn)
  · simp only [geom_sum_two, lt_add_iff_pos_left, ite_true, hx, even_two]
  clear hn
  intro n _ ihn
  simp only [Nat.even_add_one, geom_sum_succ]
  split_ifs at ihn ⊢ with hn'
  · rw [lt_add_iff_pos_left]
    exact mul_pos_of_neg_of_neg hx0 ihn
  · grw [← hx.le]
    gcongr
    simpa only [mul_one] using mul_lt_mul_of_neg_left ihn hx0

end IsStrictOrderedRing
end PartialOrder

section LinearOrder
variable [LinearOrder R] [IsStrictOrderedRing R] {n : Nat} {x : R}

/--
lemma `geom_sum_pos'` / 引理 `geom_sum_pos'`

English:
lemma geom_sum_pos'
  given: (hx : 0 < x + 1) (hn : n != 0)
  statement: 0 < ∑ i in range n, x ^ i
  proof: by
  obtain _ | _ | n := n
  · cases hn rfl
  · simp only [zero_add, range_one, sum_singleton, pow_zero, zero_lt_one]
  obtain hx' | hx' := lt_or_ge x 0
  · exact (geom_sum_pos_and_lt_one hx' hx n.one_lt_succ_succ).1
  · exact geom_sum_pos hx' (by simp)

中文:
引理 geom_sum_pos'
  条件: (hx : 0 < x + 1) (hn : n != 0)
  结论: 0 < ∑ i in range n, x ^ i
  证明: by
  obtain _ | _ | n := n
  · cases hn rfl
  · simp only [zero_add, range_one, sum_singleton, pow_zero, zero_lt_one]
  obtain hx' | hx' := lt_or_ge x 0
  · exact (geom_sum_pos_and_lt_one hx' hx n.one_lt_succ_succ).1
  · exact geom_sum_pos hx' (by simp)

Depends on / 依赖: geom_sum_pos, geom_sum_pos_and_lt_one, lt_or_ge, n.one_lt_succ_succ, one_lt_succ_succ, pow_zero, range_one, sum_singleton, zero_add, zero_lt_one
-/
lemma geom_sum_pos' (hx : 0 < x + 1) (hn : n != 0) : 0 < ∑ i in range n, x ^ i := by
  obtain _ | _ | n := n
  · cases hn rfl
  · simp only [zero_add, range_one, sum_singleton, pow_zero, zero_lt_one]
  obtain hx' | hx' := lt_or_ge x 0
  · exact (geom_sum_pos_and_lt_one hx' hx n.one_lt_succ_succ).1
  · exact geom_sum_pos hx' (by simp)

/--
lemma `Odd.geom_sum_pos` / 引理 `Odd.geom_sum_pos`

English:
lemma Odd.geom_sum_pos
  given: (h : Odd n)
  statement: 0 < ∑ i in range n, x ^ i
  proof: by
  rcases n with (_ | _ | k)
  · exact (Nat.not_odd_zero h).elim
  · simp only [zero_add, range_one, sum_singleton, pow_zero, zero_lt_one]
  rw [← Nat.not_even_iff_odd] at h
  rcases lt_trichotomy (x + 1) 0 with (hx | hx | hx)
  · have := geom_sum_alternating_of_lt_neg_one hx k.one_lt_succ_succ
  

中文:
引理 Odd.geom_sum_pos
  条件: (h : Odd n)
  结论: 0 < ∑ i in range n, x ^ i
  证明: by
  rcases n with (_ | _ | k)
  · exact (Nat.not_odd_zero h).elim
  · simp only [zero_add, range_one, sum_singleton, pow_zero, zero_lt_one]
  rw [← Nat.not_even_iff_odd] at h
  rcases lt_trichotomy (x + 1) 0 with (hx | hx | hx)
  · have := geom_sum_alternating_of_lt_neg_one hx k.one_lt_succ_succ
  

Depends on / 依赖: Nat.not_even_iff_odd, Nat.not_odd_zero, eq_neg_of_add_eq_zero_left, geom_sum_alternating_of_lt_neg_one, geom_sum_pos, if_false, k.one_lt_succ_succ, k.succ.succ_ne_zero, lt_trichotomy, neg_one_geom_sum, not_even_iff_odd, not_odd_zero, one_lt_succ_succ, pow_zero, range_one, succ_ne_zero, sum_singleton, zero_add, zero_lt_one, zero_lt_one.trans
-/
lemma Odd.geom_sum_pos (h : Odd n) : 0 < ∑ i in range n, x ^ i := by
  rcases n with (_ | _ | k)
  · exact (Nat.not_odd_zero h).elim
  · simp only [zero_add, range_one, sum_singleton, pow_zero, zero_lt_one]
  rw [← Nat.not_even_iff_odd] at h
  rcases lt_trichotomy (x + 1) 0 with (hx | hx | hx)
  · have := geom_sum_alternating_of_lt_neg_one hx k.one_lt_succ_succ
    simp only [h, if_false] at this
    exact zero_lt_one.trans this
  · simp only [eq_neg_of_add_eq_zero_left hx, h, neg_one_geom_sum, if_false, zero_lt_one]
  · exact geom_sum_pos' hx k.succ.succ_ne_zero

/--
lemma `geom_sum_pos_iff` / 引理 `geom_sum_pos_iff`

English:
lemma geom_sum_pos_iff
  given: (hn : n != 0)
  statement: 0 < ∑ i in range n, x ^ i ↔ Odd n ∨ 0 < x + 1
  proof: by
  refine ⟨fun h => ?_, ?_⟩
  · rw [or_iff_not_imp_left, ← not_le, Nat.not_odd_iff_even]
    refine fun hn hx => h.not_ge ?_
    simpa [if_pos hn] using geom_sum_alternating_of_le_neg_one hx n
  · rintro (hn | hx')
    · exact hn.geom_sum_pos
    · exact geom_sum_pos' hx' hn

中文:
引理 geom_sum_pos_iff
  条件: (hn : n != 0)
  结论: 0 < ∑ i in range n, x ^ i ↔ Odd n ∨ 0 < x + 1
  证明: by
  refine ⟨fun h => ?_, ?_⟩
  · rw [or_iff_not_imp_left, ← not_le, Nat.not_odd_iff_even]
    refine fun hn hx => h.not_ge ?_
    simpa [if_pos hn] using geom_sum_alternating_of_le_neg_one hx n
  · rintro (hn | hx')
    · exact hn.geom_sum_pos
    · exact geom_sum_pos' hx' hn

Depends on / 依赖: Nat.not_odd_iff_even, geom_sum_alternating_of_le_neg_one, geom_sum_pos, h.not_ge, hn.geom_sum_pos, if_pos, not_ge, not_le, not_odd_iff_even, or_iff_not_imp_left
-/
lemma geom_sum_pos_iff (hn : n != 0) : 0 < ∑ i in range n, x ^ i ↔ Odd n ∨ 0 < x + 1 := by
  refine ⟨fun h => ?_, ?_⟩
  · rw [or_iff_not_imp_left, ← not_le, Nat.not_odd_iff_even]
    refine fun hn hx => h.not_ge ?_
    simpa [if_pos hn] using geom_sum_alternating_of_le_neg_one hx n
  · rintro (hn | hx')
    · exact hn.geom_sum_pos
    · exact geom_sum_pos' hx' hn

/--
lemma `geom_sum_ne_zero` / 引理 `geom_sum_ne_zero`

English:
lemma geom_sum_ne_zero
  given: (hx : x != -1) (hn : n != 0)
  statement: ∑ i in range n, x ^ i != 0
  proof: by
  obtain _ | _ | n := n
  · cases hn rfl
  · simp only [zero_add, range_one, sum_singleton, pow_zero, ne_eq, one_ne_zero, not_false_eq_true]
  rw [Ne]; rw [eq_neg_iff_add_eq_zero]; rw [← Ne] at hx
  obtain h | h := hx.lt_or_gt
  · have := geom_sum_alternating_of_lt_neg_one h n.one_lt_succ_succ
  

中文:
引理 geom_sum_ne_zero
  条件: (hx : x != -1) (hn : n != 0)
  结论: ∑ i in range n, x ^ i != 0
  证明: by
  obtain _ | _ | n := n
  · cases hn rfl
  · simp only [zero_add, range_one, sum_singleton, pow_zero, ne_eq, one_ne_zero, not_false_eq_true]
  rw [Ne]; rw [eq_neg_iff_add_eq_zero]; rw [← Ne] at hx
  obtain h | h := hx.lt_or_gt
  · have := geom_sum_alternating_of_lt_neg_one h n.one_lt_succ_succ
  

Depends on / 依赖: eq_neg_iff_add_eq_zero, geom_sum_alternating_of_lt_neg_one, geom_sum_pos, hx.lt_or_gt, lt_or_gt, n.one_lt_succ_succ, n.succ.succ_ne_zero, ne_eq, not_false_eq_true, one_lt_succ_succ, one_ne_zero, pow_zero, range_one, split_ifs, succ_ne_zero, sum_singleton, this.ne, zero_add, zero_lt_one, zero_lt_one.trans
-/
lemma geom_sum_ne_zero (hx : x != -1) (hn : n != 0) : ∑ i in range n, x ^ i != 0 := by
  obtain _ | _ | n := n
  · cases hn rfl
  · simp only [zero_add, range_one, sum_singleton, pow_zero, ne_eq, one_ne_zero, not_false_eq_true]
  rw [Ne]; rw [eq_neg_iff_add_eq_zero]; rw [← Ne] at hx
  obtain h | h := hx.lt_or_gt
  · have := geom_sum_alternating_of_lt_neg_one h n.one_lt_succ_succ
    split_ifs at this
    · exact this.ne
    · exact (zero_lt_one.trans this).ne'
  · exact (geom_sum_pos' h n.succ.succ_ne_zero).ne'

/--
lemma `geom_sum_eq_zero_iff_neg_one` / 引理 `geom_sum_eq_zero_iff_neg_one`

English:
lemma geom_sum_eq_zero_iff_neg_one
  given: (hn : n != 0)
  statement: ∑ i in range n, x ^ i = 0 ↔ x = -1 ∧ Even n
  proof: by
  refine ⟨fun h => ?_, @fun ⟨h, hn⟩ => by simp only [h, hn, neg_one_geom_sum, if_true]⟩
  contrapose! h
  have hx := eq_or_ne x (-1)
  rcases hx with hx | hx
  · rw [hx, neg_one_geom_sum]
    simp only [h hx, ite_false, ne_eq, one_ne_zero, not_false_eq_true]
  · exact geom_sum_ne_zero hx hn

中文:
引理 geom_sum_eq_zero_iff_neg_one
  条件: (hn : n != 0)
  结论: ∑ i in range n, x ^ i = 0 ↔ x = -1 ∧ Even n
  证明: by
  refine ⟨fun h => ?_, @fun ⟨h, hn⟩ => by simp only [h, hn, neg_one_geom_sum, if_true]⟩
  contrapose! h
  have hx := eq_or_ne x (-1)
  rcases hx with hx | hx
  · rw [hx, neg_one_geom_sum]
    simp only [h hx, ite_false, ne_eq, one_ne_zero, not_false_eq_true]
  · exact geom_sum_ne_zero hx hn

Depends on / 依赖: contrapose, eq_or_ne, geom_sum_ne_zero, if_true, ite_false, ne_eq, neg_one_geom_sum, not_false_eq_true, one_ne_zero
-/
lemma geom_sum_eq_zero_iff_neg_one (hn : n != 0) : ∑ i in range n, x ^ i = 0 ↔ x = -1 ∧ Even n := by
  refine ⟨fun h => ?_, @fun ⟨h, hn⟩ => by simp only [h, hn, neg_one_geom_sum, if_true]⟩
  contrapose! h
  have hx := eq_or_ne x (-1)
  rcases hx with hx | hx
  · rw [hx, neg_one_geom_sum]
    simp only [h hx, ite_false, ne_eq, one_ne_zero, not_false_eq_true]
  · exact geom_sum_ne_zero hx hn

/--
lemma `geom_sum_neg_iff` / 引理 `geom_sum_neg_iff`

English:
lemma geom_sum_neg_iff
  given: (hn : n != 0)
  statement: ∑ i in range n, x ^ i < 0 ↔ Even n ∧ x + 1 < 0
  proof: by
  rw [← not_iff_not]; rw [not_lt]; rw [le_iff_lt_or_eq]; rw [eq_comm]; rw [or_congr (geom_sum_pos_iff hn) (geom_sum_eq_zero_iff_neg_one hn)]; rw [← Nat.not_even_iff_odd]; rw [←
    add_eq_zero_iff_eq_neg]; rw [not_and]; rw [not_lt]; rw [le_iff_lt_or_eq]; rw [eq_comm]; rw [← imp_iff_not_or]; rw [o

中文:
引理 geom_sum_neg_iff
  条件: (hn : n != 0)
  结论: ∑ i in range n, x ^ i < 0 ↔ Even n ∧ x + 1 < 0
  证明: by
  rw [← not_iff_not]; rw [not_lt]; rw [le_iff_lt_or_eq]; rw [eq_comm]; rw [or_congr (geom_sum_pos_iff hn) (geom_sum_eq_zero_iff_neg_one hn)]; rw [← Nat.not_even_iff_odd]; rw [←
    add_eq_zero_iff_eq_neg]; rw [not_and]; rw [not_lt]; rw [le_iff_lt_or_eq]; rw [eq_comm]; rw [← imp_iff_not_or]; rw [o

Depends on / 依赖: Decidable, Decidable.and_or_imp, Nat.not_even_iff_odd, add_eq_zero_iff_eq_neg, and_comm, and_or_imp, eq_comm, geom_sum_eq_zero_iff_neg_one, geom_sum_pos_iff, imp_iff_not_or, le_iff_lt_or_eq, not_and, not_even_iff_odd, not_iff_not, not_lt, or_comm, or_congr
-/
lemma geom_sum_neg_iff (hn : n != 0) : ∑ i in range n, x ^ i < 0 ↔ Even n ∧ x + 1 < 0 := by
  rw [← not_iff_not]; rw [not_lt]; rw [le_iff_lt_or_eq]; rw [eq_comm]; rw [or_congr (geom_sum_pos_iff hn) (geom_sum_eq_zero_iff_neg_one hn)]; rw [← Nat.not_even_iff_odd]; rw [←
    add_eq_zero_iff_eq_neg]; rw [not_and]; rw [not_lt]; rw [le_iff_lt_or_eq]; rw [eq_comm]; rw [← imp_iff_not_or]; rw [or_comm]; rw [and_comm]; rw [Decidable.and_or_imp]; rw [or_comm]

end LinearOrder
end Ring


/--
lemma `Nat.pred_mul_geom_sum_le` / 引理 `Nat.pred_mul_geom_sum_le`

English:
lemma Nat.pred_mul_geom_sum_le
  given: (a b n : Nat)
  proof: calc
    ((b - 1) * ∑ i in range n.succ, a / b ^ i) =
    (∑ i in range n, a / b ^ (i + 1) * b) + a * b - ((∑ i in range n, a / b ^ i) + a / b ^ n) := by
      rw [Nat.sub_mul]; rw [mul_comm]; rw [sum_mul]; rw [one_mul]; rw [sum_range_succ']; rw [sum_range_succ]; rw [pow_zero]; rw [Nat.div_one]
    

中文:
引理 Nat.pred_mul_geom_sum_le
  条件: (a b n : 自然数)
  证明: calc
    ((b - 1) * ∑ i in range n.succ, a / b ^ i) =
    (∑ i in range n, a / b ^ (i + 1) * b) + a * b - ((∑ i in range n, a / b ^ i) + a / b ^ n) := by
      rw [Nat.sub_mul]; rw [mul_comm]; rw [sum_mul]; rw [one_mul]; rw [sum_range_succ']; rw [sum_range_succ]; rw [pow_zero]; rw [Nat.div_one]
    

Depends on / 依赖: Nat.div_div_eq_div_mul, Nat.div_mul_le_self, Nat.div_one, Nat.sub_mul, add_tsub_a, div_div_eq_div_mul, div_mul_le_self, div_one, mul_comm, n.succ, one_mul, pow_succ, pow_zero, sub_mul, sum_mul, sum_range_succ
-/
lemma Nat.pred_mul_geom_sum_le (a b n : Nat) :
    ((b - 1) * ∑ i in range n.succ, a / b ^ i) <= a * b - a / b ^ n :=
  calc
    ((b - 1) * ∑ i in range n.succ, a / b ^ i) =
    (∑ i in range n, a / b ^ (i + 1) * b) + a * b - ((∑ i in range n, a / b ^ i) + a / b ^ n) := by
      rw [Nat.sub_mul]; rw [mul_comm]; rw [sum_mul]; rw [one_mul]; rw [sum_range_succ']; rw [sum_range_succ]; rw [pow_zero]; rw [Nat.div_one]
    _ <= (∑ i in range n, a / b ^ i) + a * b - ((∑ i in range n, a / b ^ i) + a / b ^ n) := by
      gcongr with i hi
      rw [pow_succ]; rw [← Nat.div_div_eq_div_mul]
      exact Nat.div_mul_le_self _ _
    _ = a * b - a / b ^ n := add_tsub_add_eq_tsub_left _ _ _

/--
lemma `Nat.geom_sum_le` / 引理 `Nat.geom_sum_le`

English:
lemma Nat.geom_sum_le
  given: {b : Nat} (hb : 2 <= b) (a n : Nat)
  proof: by
  refine (Nat.le_div_iff_mul_le <| tsub_pos_of_lt hb).2 ?_
  rcases n with - | n
  · rw [sum_range_zero, zero_mul]
    exact Nat.zero_le _
  rw [mul_comm]
  exact (Nat.pred_mul_geom_sum_le a b n).trans tsub_le_self

中文:
引理 Nat.geom_sum_le
  条件: {b : 自然数} (hb : 2 <= b) (a n : 自然数)
  证明: by
  refine (Nat.le_div_iff_mul_le <| tsub_pos_of_lt hb).2 ?_
  rcases n with - | n
  · rw [sum_range_zero, zero_mul]
    exact Nat.zero_le _
  rw [mul_comm]
  exact (Nat.pred_mul_geom_sum_le a b n).trans tsub_le_self

Depends on / 依赖: Nat.le_div_iff_mul_le, Nat.pred_mul_geom_sum_le, Nat.zero_le, le_div_iff_mul_le, mul_comm, pred_mul_geom_sum_le, sum_range_zero, tsub_le_self, tsub_pos_of_lt, zero_le, zero_mul
-/
lemma Nat.geom_sum_le {b : Nat} (hb : 2 <= b) (a n : Nat) :
    ∑ i in range n, a / b ^ i <= a * b / (b - 1) := by
  refine (Nat.le_div_iff_mul_le <| tsub_pos_of_lt hb).2 ?_
  rcases n with - | n
  · rw [sum_range_zero, zero_mul]
    exact Nat.zero_le _
  rw [mul_comm]
  exact (Nat.pred_mul_geom_sum_le a b n).trans tsub_le_self

/--
lemma `Nat.geom_sum_Ico_le` / 引理 `Nat.geom_sum_Ico_le`

English:
lemma Nat.geom_sum_Ico_le
  given: {b : Nat} (hb : 2 <= b) (a n : Nat)
  proof: by
  rcases n with - | n
  · rw [Ico_eq_empty_of_le (by lia), sum_empty]
    exact Nat.zero_le _
  rw [← add_le_add_iff_left a]
  calc
    (a + ∑ i in Ico 1 n.succ, a / b ^ i) = a / b ^ 0 + ∑ i in Ico 1 n.succ, a / b ^ i := by
      rw [pow_zero]; rw [Nat.div_one]
    _ = ∑ i in range n.succ, a / b 

中文:
引理 Nat.geom_sum_Ico_le
  条件: {b : 自然数} (hb : 2 <= b) (a n : 自然数)
  证明: by
  rcases n with - | n
  · rw [Ico_eq_empty_of_le (by lia), sum_empty]
    exact Nat.zero_le _
  rw [← add_le_add_iff_left a]
  calc
    (a + ∑ i in Ico 1 n.succ, a / b ^ i) = a / b ^ 0 + ∑ i in Ico 1 n.succ, a / b ^ i := by
      rw [pow_zero]; rw [Nat.div_one]
    _ = ∑ i in range n.succ, a / b 

Depends on / 依赖: Finset, Finset.insert_Ico_add_one_left_eq_Ico, Ico_eq_empty_of_le, Nat.div_one, Nat.geom_sum_le, Nat.succ_pos, Nat.zero_le, add_le_add_iff_left, add_t, div_one, geom_sum_le, insert_Ico_add_one_left_eq_Ico, mul_add, n.succ, pow_zero, range_eq_Ico, succ_pos, sum_empty, sum_insert, zero_le
-/
lemma Nat.geom_sum_Ico_le {b : Nat} (hb : 2 <= b) (a n : Nat) :
    ∑ i in Ico 1 n, a / b ^ i <= a / (b - 1) := by
  rcases n with - | n
  · rw [Ico_eq_empty_of_le (by lia), sum_empty]
    exact Nat.zero_le _
  rw [← add_le_add_iff_left a]
  calc
    (a + ∑ i in Ico 1 n.succ, a / b ^ i) = a / b ^ 0 + ∑ i in Ico 1 n.succ, a / b ^ i := by
      rw [pow_zero]; rw [Nat.div_one]
    _ = ∑ i in range n.succ, a / b ^ i := by
      rw [range_eq_Ico]; rw [← Finset.insert_Ico_add_one_left_eq_Ico (Nat.succ_pos _)]; rw [sum_insert] <;>
        simp
    _ <= a * b / (b - 1) := Nat.geom_sum_le hb a _
    _ = (a * 1 + a * (b - 1)) / (b - 1) := by rw [← mul_add, add_tsub_cancel_of_le (by lia)]
    _ = a + a / (b - 1) := by rw [mul_one, Nat.add_mul_div_right _ _ (tsub_pos_of_lt hb), add_comm]

variable {m n : Nat} {s : Finset Nat}

/--
lemma `Nat.geomSum_lt` / 引理 `Nat.geomSum_lt`

English:
lemma Nat.geomSum_lt
  given: (hm : 2 <= m) (hs : forall k in s, k < n)
  statement: ∑ k in s, m ^ k < m ^ n
  proof: calc
    ∑ k in s, m ^ k <= ∑ k in range n, m ^ k := sum_le_sum_of_subset fun _ hk =>
mem_range.2 hs _ hk
    _ = (m ^ n - 1) / (m - 1) := Nat.geomSum_eq hm _
    _ <= m ^ n - 1 := Nat.div_le_self _ _
    _ < m ^ n := tsub_lt_self (Nat.pow_pos <| by lia) (by lia)

中文:
引理 Nat.geomSum_lt
  条件: (hm : 2 <= m) (hs : 对任意 k in s, k < n)
  结论: ∑ k in s, m ^ k < m ^ n
  证明: calc
    ∑ k in s, m ^ k <= ∑ k in range n, m ^ k := sum_le_sum_of_subset fun _ hk =>
mem_range.2 hs _ hk
    _ = (m ^ n - 1) / (m - 1) := Nat.geomSum_eq hm _
    _ <= m ^ n - 1 := Nat.div_le_self _ _
    _ < m ^ n := tsub_lt_self (Nat.pow_pos <| by lia) (by lia)

Depends on / 依赖: Nat.div_le_self, Nat.geomSum_eq, Nat.pow_pos, div_le_self, geomSum_eq, mem_range, pow_pos, sum_le_sum_of_subset, tsub_lt_self
-/
lemma Nat.geomSum_lt (hm : 2 <= m) (hs : forall k in s, k < n) : ∑ k in s, m ^ k < m ^ n :=
  calc
    ∑ k in s, m ^ k <= ∑ k in range n, m ^ k := sum_le_sum_of_subset fun _ hk =>
mem_range.2 hs _ hk
    _ = (m ^ n - 1) / (m - 1) := Nat.geomSum_eq hm _
    _ <= m ^ n - 1 := Nat.div_le_self _ _
    _ < m ^ n := tsub_lt_self (Nat.pow_pos <| by lia) (by lia)
