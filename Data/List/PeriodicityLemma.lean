/-
Copyright (c) 2025 Štěpán Holub. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Štěpán Holub
-/
module

public import Mathlib.Algebra.Order.Group.Nat
public import Mathlib.Order.Lattice.Nat
public import Mathlib.Tactic.TacticAnalysis.Declarations

/-! # Periods of words (Lists)

This file defines the notion of a period of a word (list) and proves the Periodicity Lemma.

## Implementation notes

The definition of a period is given in terms of self-overlap.
Equivalent characterizations in terms of indices and modular arithmetic are also provided.

## Tags

periodicity lemma, Fine-Wilf theorem, period, periodicity

-/

@[expose] public section

variable {α : Type _}

open Nat

namespace List
/--
Definition of `HasPeriod` / `HasPeriod` 的定义

English:
definition HasPeriod
  signature: (w : List α) (p : Nat)
  body: w <+: take p w ++ w

中文:
定义 HasPeriod
  签名: (w : List α) (p : 自然数)
  定义体: w <+: take p w ++ w
-/
def HasPeriod (w : List α) (p : Nat) : Prop := w <+: take p w ++ w

/--
lemma `hasPeriod_iff_getElem?` / 引理 `hasPeriod_iff_getElem?`

English:
lemma hasPeriod_iff_getElem?
  given: {p : Nat} {w : List α}
  proof: by
  constructor
  · rw [HasPeriod]
    intro pref j len
    have i1 : j < w.length := by lia
    have i2 : j + p < w.length := by lia
    have min : p < w.length := by lia
    have : j + p - (List.take p w).length = j := by
      simp_all [min_eq_left_of_lt]
    simp_all [getElem_append_right, IsPr

中文:
引理 hasPeriod_iff_getElem?
  条件: {p : 自然数} {w : List α}
  证明: by
  constructor
  · rw [HasPeriod]
    intro pref j len
    have i1 : j < w.length := by lia
    have i2 : j + p < w.length := by lia
    have min : p < w.length := by lia
    have : j + p - (List.take p w).length = j := by
      simp_all [min_eq_left_of_lt]
    simp_all [getElem_append_right, IsPr

Depends on / 依赖: HasPeriod, IsPrefix, IsPrefix.getElem, List.take, getElem, getElem_append_right, getElem_drop, length, length_drop, min_eq_left_of_lt, prefix_iff_getElem, w.length
-/
lemma hasPeriod_iff_getElem? {p : Nat} {w : List α} :
    HasPeriod w p ↔ forall i < w.length - p, w[i]? = w[i + p]? := by
  constructor
  · rw [HasPeriod]
    intro pref j len
    have i1 : j < w.length := by lia
    have i2 : j + p < w.length := by lia
    have min : p < w.length := by lia
    have : j + p - (List.take p w).length = j := by
      simp_all [min_eq_left_of_lt]
    simp_all [getElem_append_right, IsPrefix.getElem pref, min_eq_left_of_lt]
  · intro lhs
    rw [HasPeriod]
    have drop : drop p w <+: w := by
      simp only [prefix_iff_getElem?, length_drop, getElem_drop]
      intro i leni
      have len : i + p < w.length := by lia
      simp_all only [getElem?_pos, add_comm p i]
    rw [← prefix_append_right_inj (w.take p)] at drop
    simp_all

@[simp]
/--
lemma `hasPeriod_zero` / 引理 `hasPeriod_zero`

English:
lemma hasPeriod_zero
  given: (w : List α)
  statement: HasPeriod w 0
  proof: by
  simp [HasPeriod]

@[simp]

中文:
引理 hasPeriod_zero
  条件: (w : List α)
  结论: HasPeriod w 0
  证明: by
  simp [HasPeriod]

@[simp]

Depends on / 依赖: HasPeriod
-/
lemma hasPeriod_zero (w : List α) : HasPeriod w 0 := by
  simp [HasPeriod]

@[simp]
/--
lemma `hasPeriod_of_length_le` / 引理 `hasPeriod_of_length_le`

English:
lemma hasPeriod_of_length_le
  given: (w : List α) (p : Nat) (large : w.length <= p)
  statement: HasPeriod w p
  proof: by
  rw [HasPeriod]; simp_all [(take_eq_self_iff w).mpr large]

中文:
引理 hasPeriod_of_length_le
  条件: (w : List α) (p : 自然数) (large : w.length <= p)
  结论: HasPeriod w p
  证明: by
  rw [HasPeriod]; simp_all [(take_eq_self_iff w).mpr large]

Depends on / 依赖: HasPeriod, take_eq_self_iff
-/
lemma hasPeriod_of_length_le (w : List α) (p : Nat) (large : w.length <= p) : HasPeriod w p := by
  rw [HasPeriod]; simp_all [(take_eq_self_iff w).mpr large]

/--
lemma `hasPeriod_empty` / 引理 `hasPeriod_empty`

English:
lemma hasPeriod_empty
  given: (p : Nat)
  statement: HasPeriod ([] : List α) p
  proof: by
  simp

中文:
引理 hasPeriod_empty
  条件: (p : 自然数)
  结论: HasPeriod ([] : List α) p
  证明: by
  simp
-/
lemma hasPeriod_empty (p : Nat) : HasPeriod ([] : List α) p := by
  simp

/--
lemma `HasPeriod.getElem?_mod` / 引理 `HasPeriod.getElem?_mod`

English:
lemma HasPeriod.getElem?_mod
  statement: (p i : Nat) (w : List α) (per : HasPeriod w p)
  proof: by
  by_cases p_zero : p = 0
  · rw [p_zero, mod_zero]
  · cases lt_or_ge i p with
    | inl small =>
        have eq : i % p = i := mod_eq_of_lt small
        rw [eq]
    | inr large =>
        have len' : i - p < w.length := by lia
        have IH : w[(i - p) % p]? = w[i - p]? := per.getElem?_mod 

中文:
引理 HasPeriod.getElem?_mod
  结论: (p i : 自然数) (w : List α) (per : HasPeriod w p)
  证明: by
  by_cases p_zero : p = 0
  · rw [p_zero, mod_zero]
  · cases lt_or_ge i p with
    | inl small =>
        have eq : i % p = i := mod_eq_of_lt small
        rw [eq]
    | inr large =>
        have len' : i - p < w.length := by lia
        have IH : w[(i - p) % p]? = w[i - p]? := per.getElem?_mod 

Depends on / 依赖: Nat.sub_add_cancel, _mod, getElem, hasPeriod_iff_getElem, length, lt_or_ge, mod_eq_of_lt, mod_eq_sub_mod, mod_zero, p_zero, per.getElem, sub_add_cancel, w.length
-/
lemma HasPeriod.getElem?_mod (p i : Nat) (w : List α) (per : HasPeriod w p)
    (less : i < w.length) : w[i % p]? = w[i]? := by
  by_cases p_zero : p = 0
  · rw [p_zero, mod_zero]
  · cases lt_or_ge i p with
    | inl small =>
        have eq : i % p = i := mod_eq_of_lt small
        rw [eq]
    | inr large =>
        have len' : i - p < w.length := by lia
        have IH : w[(i - p) % p]? = w[i - p]? := per.getElem?_mod p (i - p) w len'
        rw [hasPeriod_iff_getElem?] at per
        have minus : i - p < w.length - p := by lia
        have per' := per (i - p) minus
        simp only [large, Nat.sub_add_cancel] at per'
        have mod : i % p = (i - p) % p := mod_eq_sub_mod large
        aesop

/--
lemma `hasPeriod_iff_forall_getElem?_mod` / 引理 `hasPeriod_iff_forall_getElem?_mod`

English:
lemma hasPeriod_iff_forall_getElem?_mod
  given: {p : Nat} {w : List α}
  proof: by
  constructor
  · intro per i len
    exact Eq.symm (per.getElem?_mod p i w len)
  · intro mod
    rw [hasPeriod_iff_getElem?]
    intro i less
    rw [mod (i + p) (by lia)]; rw [add_mod_right]; rw [mod i (by lia)]

中文:
引理 hasPeriod_iff_forall_getElem?_mod
  条件: {p : 自然数} {w : List α}
  证明: by
  constructor
  · intro per i len
    exact Eq.symm (per.getElem?_mod p i w len)
  · intro mod
    rw [hasPeriod_iff_getElem?]
    intro i less
    rw [mod (i + p) (by lia)]; rw [add_mod_right]; rw [mod i (by lia)]

Depends on / 依赖: Eq.symm, _mod, add_mod_right, getElem, hasPeriod_iff_getElem, per.getElem
-/
lemma hasPeriod_iff_forall_getElem?_mod {p : Nat} {w : List α} :
    HasPeriod w p ↔ (forall i < w.length, w[i]? = w[i % p]?) := by
  constructor
  · intro per i len
    exact Eq.symm (per.getElem?_mod p i w len)
  · intro mod
    rw [hasPeriod_iff_getElem?]
    intro i less
    rw [mod (i + p) (by lia)]; rw [add_mod_right]; rw [mod i (by lia)]

/--
lemma `HasPeriod.factor` / 引理 `HasPeriod.factor`

English:
lemma HasPeriod.factor
  given: {u v w : List α} {p : Nat} (per : HasPeriod (u ++ v ++ w) p)
  proof: by
  suffices forall j < v.length - p, v[j]? = v[j + p]? by simpa [hasPeriod_iff_getElem?]
  intro j len
  have shift_position : (u ++ (v ++ w))[j + u.length]? = v[j]? := by
    rw [getElem?_append_right]; rw [Nat.add_sub_cancel]; rw [getElem?_append_left]
    all_goals lia
  have shift_position' : 

中文:
引理 HasPeriod.factor
  条件: {u v w : List α} {p : 自然数} (per : HasPeriod (u ++ v ++ w) p)
  证明: by
  suffices forall j < v.length - p, v[j]? = v[j + p]? by simpa [hasPeriod_iff_getElem?]
  intro j len
  have shift_position : (u ++ (v ++ w))[j + u.length]? = v[j]? := by
    rw [getElem?_append_right]; rw [Nat.add_sub_cancel]; rw [getElem?_append_left]
    all_goals lia
  have shift_position' : 

Depends on / 依赖: Nat.add_sub_cancel, _append_left, _append_right, add_sub_cancel, all_goals, getElem, hasPeriod_iff_getElem, length, shift_position, u.length, v.length
-/
lemma HasPeriod.factor {u v w : List α} {p : Nat} (per : HasPeriod (u ++ v ++ w) p) :
    HasPeriod v p := by
  suffices forall j < v.length - p, v[j]? = v[j + p]? by simpa [hasPeriod_iff_getElem?]
  intro j len
  have shift_position : (u ++ (v ++ w))[j + u.length]? = v[j]? := by
    rw [getElem?_append_right]; rw [Nat.add_sub_cancel]; rw [getElem?_append_left]
    all_goals lia
  have shift_position' : (u ++ (v ++ w))[j + u.length + p]? = v[j + p]? := by
    have eq : j + u.length + p - u.length = j + p := by lia
    rw [getElem?_append_right]
    · rw [getElem?_append_left]
      · exact congrArg (getElem? v) eq
      · lia
    · lia
  have : forall i < u.length + (v.length + w.length) - p,
      (u ++ (v ++ w))[i]? = (u ++ (v ++ w))[i + p]? := by
    simp_all [hasPeriod_iff_getElem?]
  rw [← shift_position']; rw [← shift_position]
  exact this (j + u.length) (by lia)

/--
lemma `HasPeriod.infix` / 引理 `HasPeriod.infix`

English:
lemma HasPeriod.infix
  given: {u w : List α} {p : Nat} (per : HasPeriod w p) (h : u <:+: w)
  proof: by
  obtain ⟨s, t, rfl⟩ := h
  exact per.factor

中文:
引理 HasPeriod.infix
  条件: {u w : List α} {p : 自然数} (per : HasPeriod w p) (h : u <:+: w)
  证明: by
  obtain ⟨s, t, rfl⟩ := h
  exact per.factor

Depends on / 依赖: factor, per.factor
-/
lemma HasPeriod.infix {u w : List α} {p : Nat} (per : HasPeriod w p) (h : u <:+: w) :
    HasPeriod u p := by
  obtain ⟨s, t, rfl⟩ := h
  exact per.factor

/--
lemma `HasPeriod.drop_prefix` / 引理 `HasPeriod.drop_prefix`

English:
lemma HasPeriod.drop_prefix
  given: {w : List α} (p : Nat) (per : HasPeriod w p)
  proof: by
  rw [← prefix_append_right_inj (take p w)]
  simp_all [HasPeriod, take_append_drop]

中文:
引理 HasPeriod.drop_prefix
  条件: {w : List α} (p : 自然数) (per : HasPeriod w p)
  证明: by
  rw [← prefix_append_right_inj (take p w)]
  simp_all [HasPeriod, take_append_drop]

Depends on / 依赖: HasPeriod, prefix_append_right_inj, take_append_drop
-/
lemma HasPeriod.drop_prefix {w : List α} (p : Nat) (per : HasPeriod w p) :
    drop p w <+: w := by
  rw [← prefix_append_right_inj (take p w)]
  simp_all [HasPeriod, take_append_drop]

/--
lemma `HasPeriod.take_append` / 引理 `HasPeriod.take_append`

English:
lemma HasPeriod.take_append
  statement: (p n : Nat) (w : List α) (dvd : p ∣ n)
  proof: by
  rcases Nat.eq_zero_or_pos p with rfl | p_pos
  · simp_all [HasPeriod]
  rcases Nat.eq_zero_or_pos n with rfl | pos
  · simp_all
  rw [hasPeriod_iff_forall_getElem?_mod]
  have mod_w : forall i < w.length, w[i % p]? = w[i]? := (per.getElem?_mod)
  suffices forall i < n + w.length, (take n w ++ w

中文:
引理 HasPeriod.take_append
  结论: (p n : 自然数) (w : List α) (dvd : p ∣ n)
  证明: by
  rcases Nat.eq_zero_or_pos p with rfl | p_pos
  · simp_all [HasPeriod]
  rcases Nat.eq_zero_or_pos n with rfl | pos
  · simp_all
  rw [hasPeriod_iff_forall_getElem?_mod]
  have mod_w : forall i < w.length, w[i % p]? = w[i]? := (per.getElem?_mod)
  suffices forall i < n + w.length, (take n w ++ w

Depends on / 依赖: HasPeriod, Nat.eq_zero_or_pos, _mod, eq_zero_or_pos, getElem, hasPeriod_iff_forall_getElem, indices, j_lt_n, length, less_i, less_j, mod_p, mod_w, p_pos, per.getElem, w.length, within
-/
lemma HasPeriod.take_append (p n : Nat) (w : List α) (dvd : p ∣ n)
    (len : n <= w.length) (per : HasPeriod w p) : HasPeriod (take n w ++ w) p := by
  rcases Nat.eq_zero_or_pos p with rfl | p_pos
  · simp_all [HasPeriod]
  rcases Nat.eq_zero_or_pos n with rfl | pos
  · simp_all
  rw [hasPeriod_iff_forall_getElem?_mod]
  have mod_w : forall i < w.length, w[i % p]? = w[i]? := (per.getElem?_mod)
  suffices forall i < n + w.length, (take n w ++ w)[i]? = (take n w ++ w)[i % p]? by simp_all
  intro i less_i
  have mod_p : forall j < n + length w, (take n w ++ w)[j]? = w[j % p]? := by
    intro j less_j
    by_cases j_lt_n : j < n
    · -- indices within `take n w` can be reduced due to the period of `w`
      calc
        (take n w ++ w)[j]? = (take n w)[j]? := getElem?_append_left (by simp_all)
        _ = w[j]? := getElem?_take_of_lt j_lt_n
        _ = w[j % p]? := Eq.symm (mod_w j (by lia))
    · -- larger indices are indices of `w` decreased by `n`
      have j_minus : j - n < w.length := by lia
      have n_le_j : n <= j := le_of_not_gt j_lt_n; clear j_lt_n;
      have j_mod : (j - n) % p = j % p := by
        calc
          (j - n) % p = (j - p * (n / p)) % p := by rw [Nat.mul_div_cancel' dvd]
          _ = j % p := sub_mul_mod ((Nat.mul_div_cancel' dvd).symm ▸ n_le_j)
      calc
        (take n w ++ w)[j]? = w[j - (take n w).length]? := getElem?_append_right (by simp_all)
        _ = w[j - n]? := by simp_all
        _ = w[(j - n) % p]? := Eq.symm (mod_w (j - n) (by lia))
        _ = w[j % p]? := by rw [j_mod]
  have less_mod : i % p < n + w.length := by
    have : i % p < p := mod_lt i p_pos; have : p <= n := le_of_dvd pos dvd; lia
  rw [mod_p i less_i]; rw [mod_p (i % p) less_mod]; rw [mod_mod]

/--
lemma `HasPeriod.drop_of_hasPeriod_add` / 引理 `HasPeriod.drop_of_hasPeriod_add`

English:
lemma HasPeriod.drop_of_hasPeriod_add
  statement: {q k : Nat} {w : List α}
  proof: by
  rw [hasPeriod_iff_getElem?] at per_plus per_q ⊢
  simp only [length_drop, getElem?_drop]
  intro i i_lt
  calc
     w[q + i]? = w[i + q]? := congrArg (getElem? w) (add_comm q i)
     _ = w[i]? := (per_q i (by lia)).symm
     _ = w[i + (k + q)]? := per_plus i (by lia)
     _ = w[q + (i + k)]? :=

中文:
引理 HasPeriod.drop_of_hasPeriod_add
  结论: {q k : 自然数} {w : List α}
  证明: by
  rw [hasPeriod_iff_getElem?] at per_plus per_q ⊢
  simp only [length_drop, getElem?_drop]
  intro i i_lt
  calc
     w[q + i]? = w[i + q]? := congrArg (getElem? w) (add_comm q i)
     _ = w[i]? := (per_q i (by lia)).symm
     _ = w[i + (k + q)]? := per_plus i (by lia)
     _ = w[q + (i + k)]? :=

Depends on / 依赖: _drop, add_comm, congr_arg, getElem, hasPeriod_iff_getElem, i_lt, length_drop, per_plus, per_q
-/
lemma HasPeriod.drop_of_hasPeriod_add {q k : Nat} {w : List α}
    (per_q : HasPeriod w q) (per_plus : HasPeriod w (k + q)) :
    HasPeriod (drop q w) k := by
  rw [hasPeriod_iff_getElem?] at per_plus per_q ⊢
  simp only [length_drop, getElem?_drop]
  intro i i_lt
  calc
     w[q + i]? = w[i + q]? := congrArg (getElem? w) (add_comm q i)
     _ = w[i]? := (per_q i (by lia)).symm
     _ = w[i + (k + q)]? := per_plus i (by lia)
     _ = w[q + (i + k)]? := congr_arg (getElem? w) (by lia)

/--
theorem `HasPeriod.gcd` / 定理 `HasPeriod.gcd`

English:
theorem HasPeriod.gcd
  statement: {w : List α} {p q : Nat} (per_p : HasPeriod w p) (per_q : HasPeriod w q)
  proof: by
  rcases Nat.eq_zero_or_pos p with rfl | p_pos
  · simp_all [HasPeriod]
  rcases Nat.eq_zero_or_pos q with rfl | q_pos
  · simp_all
  cases hyp : compare p q with
  | lt => -- if `p` is less than `q`, switch the two periods
      have p_lt_q := Nat.compare_eq_lt.mp hyp
      exact (gcd_comm q p ▸

中文:
定理 HasPeriod.gcd
  结论: {w : List α} {p q : 自然数} (per_p : HasPeriod w p) (per_q : HasPeriod w q)
  证明: by
  rcases Nat.eq_zero_or_pos p with rfl | p_pos
  · simp_all [HasPeriod]
  rcases Nat.eq_zero_or_pos q with rfl | q_pos
  · simp_all
  cases hyp : compare p q with
  | lt => -- if `p` is less than `q`, switch the two periods
      have p_lt_q := Nat.compare_eq_lt.mp hyp
      exact (gcd_comm q p ▸

Depends on / 依赖: HasPeriod, Nat.compare_eq_eq, Nat.compare_eq_gt.mp, Nat.compare_eq_lt.mp, Nat.eq_zero_or_pos, add_comm, compare, compare_eq_eq, compare_eq_gt, compare_eq_lt, eq_zero_or_pos, gcd_comm, gcd_eq_left_iff_dvd, gcd_lt_p, p.gcd, p_lt_q, p_pos, per_p, per_q, per_q.gcd
-/
theorem HasPeriod.gcd {w : List α} {p q : Nat} (per_p : HasPeriod w p) (per_q : HasPeriod w q)
    (len : p + q - p.gcd q <= w.length) : HasPeriod w (p.gcd q) := by
  rcases Nat.eq_zero_or_pos p with rfl | p_pos
  · simp_all [HasPeriod]
  rcases Nat.eq_zero_or_pos q with rfl | q_pos
  · simp_all
  cases hyp : compare p q with
  | lt => -- if `p` is less than `q`, switch the two periods
      have p_lt_q := Nat.compare_eq_lt.mp hyp
      exact (gcd_comm q p ▸ per_q.gcd) per_p (add_comm p q ▸ len)
  | eq => simpa [(Nat.compare_eq_eq).mp hyp]
  | gt =>
      have q_lt_p : q < p := Nat.compare_eq_gt.mp hyp
      have gcd_lt_p : p.gcd q < p := by
        have : p.gcd q != p := by
          simp [gcd_eq_left_iff_dvd, not_dvd_of_pos_of_lt q_pos q_lt_p]
        exact this.lt_of_le (gcd_le_left q p_pos)
      have per_diff : HasPeriod (drop q w) (p - q) := by
        have : p = (p - q) + q := by lia
        exact per_q.drop_of_hasPeriod_add (this ▸ per_p)
      have per_q' : HasPeriod (drop q w) q := by
        apply @HasPeriod.factor _ (take q w) (drop q w) [] q
        all_goals simp_all
      have gcd_stable : (p - q).gcd q = p.gcd q := gcd_sub_self_left (le_of_lt q_lt_p)
      have drop_len : q <= (drop q w).length := by
        rw [length_drop]
        have : p.gcd q <= p - q := by
          rw [← gcd_stable]; apply gcd_le_left q; lia
        lia
      have take_eq : take q (drop q w) = take q w := by
          let ⟨z, hz⟩ := per_q.drop_prefix
          convert_to take q (drop q w) = take q (drop q w ++ z)
          · rw [hz]
          exact (take_append_of_le_length drop_len).symm
      -- the induction step
      have IH : HasPeriod (drop q w) ((p - q).gcd q) :=
        per_diff.gcd per_q' (by simp; lia)
      convert_to HasPeriod (take q (drop q w) ++ drop q w) (p.gcd q)
      · rw [take_eq, take_append_drop q w]
      · exact (gcd_stable ▸ IH).take_append (p.gcd q) q (drop q w)
          (gcd_dvd_right p q) drop_len
  termination_by (q, p)
  decreasing_by
    all_goals grind

end List
