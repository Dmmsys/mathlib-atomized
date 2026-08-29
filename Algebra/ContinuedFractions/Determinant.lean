/-
Copyright (c) 2020 Kevin Kappelmann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Kappelmann
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.ContinuedFractions.ContinuantsRecurrence
public import Mathlib.Algebra.ContinuedFractions.TerminatedStable
public import Mathlib.Tactic.Ring

/-!
# Determinant Formula for Generalized Continued Fraction

We derive the so-called *determinant formula* for `GenContFract`:
`Aₙ * Bₙ₊₁ - Bₙ * Aₙ₊₁ = (-a₀) * (-a₁) * .. * (-aₙ)`.

## References

- https://en.wikipedia.org/wiki/Generalized_continued_fraction#The_determinant_formula

-/

public section

open GenContFract

variable {K : Type*} [Field K]

namespace GenContFract

variable {g : GenContFract K} {n : Nat}

/--
theorem `determinant_aux` / 定理 `determinant_aux`

English:
theorem determinant_aux
  given: (hyp : n = 0 ∨ ¬g.TerminatedAt (n - 1))
  proof: by
  induction n with
  | zero => simp [contsAux]
  | succ n IH =>
    -- set up some shorthand notation
    let conts := contsAux g (n + 2)
    set pred_conts := contsAux g (n + 1) with pred_conts_eq
    set ppred_conts := contsAux g n with ppred_conts_eq
    let pA := pred_conts.a
    let pB := pred_conts.b
    let ppA := ppred_conts.a
    let ppB := ppred_conts.b
    -- let's change the goal to something more readable
    change pA * conts.b - pB * conts.a = ∏ i in Finset.range (n + 1), -(g.partNums.get? i).getD 0
    have not_terminated_at_n : ¬TerminatedAt g n := Or.resolve_left hyp n.succ_ne_zero
    obtain ⟨gp, s_nth_eq⟩ : exists gp, g.s.get? n = some gp :=
      Option.ne_none_iff_exists'.1 not_terminated_at_n
    -- unfold the recurrence relation for `conts` once and simplify to derive the following
    suffices ppA * pB - ppB * pA = ∏ i in Finset.range n, - (g.partNums.get? i).getD 0 by
      rw [Finset.prod_range_succ]; rw [← this]; rw [partNum_eq_s_a s_nth_eq]; rw [Option.getD_some]
      subst conts
      rw [contsAux_recurrence s_nth_eq ppred_conts_eq pred_conts_eq]
      ring
exact IH Or.inr mt (terminated_stable <| n.sub_le 1) not_terminated_at_n

中文:
定理 determinant_aux
  条件: (hyp : n = 0 ∨ ¬g.TerminatedAt (n - 1))
  证明: by
  induction n with
  | zero => simp [contsAux]
  | succ n IH =>
    -- set up some shorthand notation
    let conts := contsAux g (n + 2)
    set pred_conts := contsAux g (n + 1) with pred_conts_eq
    set ppred_conts := contsAux g n with ppred_conts_eq
    let pA := pred_conts.a
    let pB := pred_conts.b
    let ppA := ppred_conts.a
    let ppB := ppred_conts.b
    -- let's change the goal to something more readable
    change pA * conts.b - pB * conts.a = ∏ i in Finset.range (n + 1), -(g.partNums.get? i).getD 0
    have not_terminated_at_n : ¬TerminatedAt g n := Or.resolve_left hyp n.succ_ne_zero
    obtain ⟨gp, s_nth_eq⟩ : exists gp, g.s.get? n = some gp :=
      Option.ne_none_iff_exists'.1 not_terminated_at_n
    -- unfold the recurrence relation for `conts` once and simplify to derive the following
    suffices ppA * pB - ppB * pA = ∏ i in Finset.range n, - (g.partNums.get? i).getD 0 by
      rw [Finset.prod_range_succ]; rw [← this]; rw [partNum_eq_s_a s_nth_eq]; rw [Option.getD_some]
      subst conts
      rw [contsAux_recurrence s_nth_eq ppred_conts_eq pred_conts_eq]
      ring
exact IH Or.inr mt (terminated_stable <| n.sub_le 1) not_terminated_at_n
-/
private theorem determinant_aux (hyp : n = 0 ∨ ¬g.TerminatedAt (n - 1)) :
    (g.contsAux n).a * (g.contsAux (n + 1)).b -
      (g.contsAux n).b * (g.contsAux (n + 1)).a =
        ∏ i in Finset.range n, - (g.partNums.get? i).getD 0 := by
  induction n with
  | zero => simp [contsAux]
  | succ n IH =>
    -- set up some shorthand notation
    let conts := contsAux g (n + 2)
    set pred_conts := contsAux g (n + 1) with pred_conts_eq
    set ppred_conts := contsAux g n with ppred_conts_eq
    let pA := pred_conts.a
    let pB := pred_conts.b
    let ppA := ppred_conts.a
    let ppB := ppred_conts.b
    -- let's change the goal to something more readable
    change pA * conts.b - pB * conts.a = ∏ i in Finset.range (n + 1), -(g.partNums.get? i).getD 0
    have not_terminated_at_n : ¬TerminatedAt g n := Or.resolve_left hyp n.succ_ne_zero
    obtain ⟨gp, s_nth_eq⟩ : exists gp, g.s.get? n = some gp :=
      Option.ne_none_iff_exists'.1 not_terminated_at_n
    -- unfold the recurrence relation for `conts` once and simplify to derive the following
    suffices ppA * pB - ppB * pA = ∏ i in Finset.range n, - (g.partNums.get? i).getD 0 by
      rw [Finset.prod_range_succ]; rw [← this]; rw [partNum_eq_s_a s_nth_eq]; rw [Option.getD_some]
      subst conts
      rw [contsAux_recurrence s_nth_eq ppred_conts_eq pred_conts_eq]
      ring
exact IH Or.inr mt (terminated_stable <| n.sub_le 1) not_terminated_at_n

/--
theorem `determinant` / 定理 `determinant`

English:
theorem determinant
  proof: by
rcases em TerminatedAt g n with terminatedAt_n | not_terminatedAt_n
  · rw [dens_stable_of_terminated n.le_succ terminatedAt_n,
      nums_stable_of_terminated n.le_succ terminatedAt_n, Finset.prod_range_succ,
      partNum_none_iff_s_none.mpr terminatedAt_n]
    grind
· exact determinant_aux Or.inr not_terminatedAt_n

中文:
定理 determinant
  证明: by
rcases em TerminatedAt g n with terminatedAt_n | not_terminatedAt_n
  · rw [dens_stable_of_terminated n.le_succ terminatedAt_n,
      nums_stable_of_terminated n.le_succ terminatedAt_n, Finset.prod_range_succ,
      partNum_none_iff_s_none.mpr terminatedAt_n]
    grind
· exact determinant_aux Or.inr not_terminatedAt_n

Depends on / 依赖: Finset, Finset.prod_range_succ, Or.inr, TerminatedAt, dens_stable_of_terminated, determinant_aux, le_succ, n.le_succ, not_terminatedAt_n, nums_stable_of_terminated, partNum_none_iff_s_none, partNum_none_iff_s_none.mpr, prod_range_succ, terminatedAt_n
-/
theorem determinant :
    g.nums n * g.dens (n + 1) - g.dens n * g.nums (n + 1) =
      ∏ i in Finset.range (n + 1), - (g.partNums.get? i).getD 0 := by
rcases em TerminatedAt g n with terminatedAt_n | not_terminatedAt_n
  · rw [dens_stable_of_terminated n.le_succ terminatedAt_n,
      nums_stable_of_terminated n.le_succ terminatedAt_n, Finset.prod_range_succ,
      partNum_none_iff_s_none.mpr terminatedAt_n]
    grind
· exact determinant_aux Or.inr not_terminatedAt_n
end GenContFract

namespace SimpContFract

variable {s : SimpContFract K} {n : Nat}

/--
theorem `determinant` / 定理 `determinant`

English:
theorem determinant
  given: (not_terminatedAt_n : ¬(↑s : GenContFract K).TerminatedAt n)
  proof: calc
  _ = ∏ i in Finset.range (n + 1), - ((↑s : GenContFract K).partNums.get? i).getD 0 :=
    (↑s : GenContFract K).determinant
  _ = ∏ i in Finset.range (n + 1), -1 := Finset.prod_congr rfl fun i hi => by
    rw [Finset.mem_range] at hi
    obtain ⟨gp, s_ith_eq⟩ : exists gp, (↑s : GenContFract K).s.get? i = some gp :=
Option.ne_none_iff_exists'.1 mt (terminated_stable <| Nat.le_of_succ_le_succ hi) ‹_›
    rw [partNum_eq_s_a s_ith_eq]; rw [s.property i gp.a <| partNum_eq_s_a s_ith_eq]; rw [Option.getD_some]
  _ = (-1) ^ (n + 1) := by rw [Finset.prod_const, Finset.card_range]

中文:
定理 determinant
  条件: (not_terminatedAt_n : ¬(↑s : GenContFract K).TerminatedAt n)
  证明: calc
  _ = ∏ i in Finset.range (n + 1), - ((↑s : GenContFract K).partNums.get? i).getD 0 :=
    (↑s : GenContFract K).determinant
  _ = ∏ i in Finset.range (n + 1), -1 := Finset.prod_congr rfl fun i hi => by
    rw [Finset.mem_range] at hi
    obtain ⟨gp, s_ith_eq⟩ : exists gp, (↑s : GenContFract K).s.get? i = some gp :=
Option.ne_none_iff_exists'.1 mt (terminated_stable <| Nat.le_of_succ_le_succ hi) ‹_›
    rw [partNum_eq_s_a s_ith_eq]; rw [s.property i gp.a <| partNum_eq_s_a s_ith_eq]; rw [Option.getD_some]
  _ = (-1) ^ (n + 1) := by rw [Finset.prod_const, Finset.card_range]
-/
theorem determinant (not_terminatedAt_n : ¬(↑s : GenContFract K).TerminatedAt n) :
    (↑s : GenContFract K).nums n * (↑s : GenContFract K).dens (n + 1) -
      (↑s : GenContFract K).dens n * (↑s : GenContFract K).nums (n + 1) = (-1) ^ (n + 1) := calc
  _ = ∏ i in Finset.range (n + 1), - ((↑s : GenContFract K).partNums.get? i).getD 0 :=
    (↑s : GenContFract K).determinant
  _ = ∏ i in Finset.range (n + 1), -1 := Finset.prod_congr rfl fun i hi => by
    rw [Finset.mem_range] at hi
    obtain ⟨gp, s_ith_eq⟩ : exists gp, (↑s : GenContFract K).s.get? i = some gp :=
Option.ne_none_iff_exists'.1 mt (terminated_stable <| Nat.le_of_succ_le_succ hi) ‹_›
    rw [partNum_eq_s_a s_ith_eq]; rw [s.property i gp.a <| partNum_eq_s_a s_ith_eq]; rw [Option.getD_some]
  _ = (-1) ^ (n + 1) := by rw [Finset.prod_const, Finset.card_range]

end SimpContFract
