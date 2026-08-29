/-
Copyright (c) 2019 Kevin Kappelmann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Kappelmann
-/
module

public import Mathlib.Algebra.ContinuedFractions.Translations

/-!
# Recurrence Lemmas for the Continuants (`conts`) Function of Continued Fractions

## Summary

Given a generalized continued fraction `g`, for all `n ≥ 1`, we prove that the continuants (`conts`)
function indeed satisfies the following recurrences:
- `Aₙ = bₙ * Aₙ₋₁ + aₙ * Aₙ₋₂`, and
- `Bₙ = bₙ * Bₙ₋₁ + aₙ * Bₙ₋₂`.
-/

public section


namespace GenContFract

variable {K : Type*} {g : GenContFract K} {n : Nat} [DivisionRing K]

/--
theorem `contsAux_recurrence` / 定理 `contsAux_recurrence`

English:
theorem contsAux_recurrence
  statement: {gp ppred pred : Pair K} (nth_s_eq : g.s.get? n = some gp)
  proof: by
  simp [*, contsAux, nextConts, nextDen, nextNum]

中文:
定理 contsAux_recurrence
  结论: {gp ppred pred : 对 K} (nth_s_eq : g.s.get? n = some gp)
  证明: by
  simp [*, contsAux, nextConts, nextDen, nextNum]

Depends on / 依赖: contsAux, nextConts, nextDen, nextNum
-/
theorem contsAux_recurrence {gp ppred pred : Pair K} (nth_s_eq : g.s.get? n = some gp)
    (nth_contsAux_eq : g.contsAux n = ppred)
    (succ_nth_contsAux_eq : g.contsAux (n + 1) = pred) :
    g.contsAux (n + 2) = ⟨gp.b * pred.a + gp.a * ppred.a, gp.b * pred.b + gp.a * ppred.b⟩ := by
  simp [*, contsAux, nextConts, nextDen, nextNum]

/--
theorem `conts_recurrenceAux` / 定理 `conts_recurrenceAux`

English:
theorem conts_recurrenceAux
  statement: {gp ppred pred : Pair K} (nth_s_eq : g.s.get? n = some gp)
  proof: by
  rw [nth_cont_eq_succ_nth_contAux]; rw [contsAux_recurrence nth_s_eq nth_contsAux_eq succ_nth_contsAux_eq]

中文:
定理 conts_recurrenceAux
  结论: {gp ppred pred : 对 K} (nth_s_eq : g.s.get? n = some gp)
  证明: by
  rw [nth_cont_eq_succ_nth_contAux]; rw [contsAux_recurrence nth_s_eq nth_contsAux_eq succ_nth_contsAux_eq]

Depends on / 依赖: contsAux_recurrence, nth_cont_eq_succ_nth_contAux, nth_contsAux_eq, nth_s_eq, succ_nth_contsAux_eq
-/
theorem conts_recurrenceAux {gp ppred pred : Pair K} (nth_s_eq : g.s.get? n = some gp)
    (nth_contsAux_eq : g.contsAux n = ppred)
    (succ_nth_contsAux_eq : g.contsAux (n + 1) = pred) :
    g.conts (n + 1) = ⟨gp.b * pred.a + gp.a * ppred.a, gp.b * pred.b + gp.a * ppred.b⟩ := by
  rw [nth_cont_eq_succ_nth_contAux]; rw [contsAux_recurrence nth_s_eq nth_contsAux_eq succ_nth_contsAux_eq]

/--
theorem `conts_recurrence` / 定理 `conts_recurrence`

English:
theorem conts_recurrence
  statement: {gp ppred pred : Pair K} (succ_nth_s_eq : g.s.get? (n + 1) = some gp)
  proof: contsAux_recurrence succ_nth_s_eq nth_conts_eq succ_nth_conts_eq

中文:
定理 conts_recurrence
  结论: {gp ppred pred : 对 K} (succ_nth_s_eq : g.s.get? (n + 1) = some gp)
  证明: contsAux_recurrence succ_nth_s_eq nth_conts_eq succ_nth_conts_eq

Depends on / 依赖: contsAux_recurrence, nth_conts_eq, succ_nth_conts_eq, succ_nth_s_eq
-/
theorem conts_recurrence {gp ppred pred : Pair K} (succ_nth_s_eq : g.s.get? (n + 1) = some gp)
    (nth_conts_eq : g.conts n = ppred) (succ_nth_conts_eq : g.conts (n + 1) = pred) :
    g.conts (n + 2) = ⟨gp.b * pred.a + gp.a * ppred.a, gp.b * pred.b + gp.a * ppred.b⟩ :=
  contsAux_recurrence succ_nth_s_eq nth_conts_eq succ_nth_conts_eq

/--
theorem `nums_recurrence` / 定理 `nums_recurrence`

English:
theorem nums_recurrence
  statement: {gp : Pair K} {ppredA predA : K}
  proof: by
  obtain ⟨ppredConts, nth_conts_eq, ⟨rfl⟩⟩ : exists conts, g.conts n = conts ∧ conts.a = ppredA :=
    exists_conts_a_of_num nth_num_eq
  obtain ⟨predConts, succ_nth_conts_eq, ⟨rfl⟩⟩ :
      exists conts, g.conts (n + 1) = conts ∧ conts.a = predA :=
    exists_conts_a_of_num succ_nth_num_eq
  rw [num_eq_conts_a]; rw [conts_recurrence succ_nth_s_eq nth_conts_eq succ_nth_conts_eq]

中文:
定理 nums_recurrence
  结论: {gp : 对 K} {ppredA predA : K}
  证明: by
  obtain ⟨ppredConts, nth_conts_eq, ⟨rfl⟩⟩ : exists conts, g.conts n = conts ∧ conts.a = ppredA :=
    exists_conts_a_of_num nth_num_eq
  obtain ⟨predConts, succ_nth_conts_eq, ⟨rfl⟩⟩ :
      exists conts, g.conts (n + 1) = conts ∧ conts.a = predA :=
    exists_conts_a_of_num succ_nth_num_eq
  rw [num_eq_conts_a]; rw [conts_recurrence succ_nth_s_eq nth_conts_eq succ_nth_conts_eq]

Depends on / 依赖: conts.a, conts_recurrence, exists_conts_a_of_num, g.conts, nth_conts_eq, nth_num_eq, num_eq_conts_a, ppredA, ppredConts, predConts, succ_nth_conts_eq, succ_nth_num_eq, succ_nth_s_eq
-/
theorem nums_recurrence {gp : Pair K} {ppredA predA : K}
    (succ_nth_s_eq : g.s.get? (n + 1) = some gp) (nth_num_eq : g.nums n = ppredA)
    (succ_nth_num_eq : g.nums (n + 1) = predA) :
    g.nums (n + 2) = gp.b * predA + gp.a * ppredA := by
  obtain ⟨ppredConts, nth_conts_eq, ⟨rfl⟩⟩ : exists conts, g.conts n = conts ∧ conts.a = ppredA :=
    exists_conts_a_of_num nth_num_eq
  obtain ⟨predConts, succ_nth_conts_eq, ⟨rfl⟩⟩ :
      exists conts, g.conts (n + 1) = conts ∧ conts.a = predA :=
    exists_conts_a_of_num succ_nth_num_eq
  rw [num_eq_conts_a]; rw [conts_recurrence succ_nth_s_eq nth_conts_eq succ_nth_conts_eq]

/--
theorem `dens_recurrence` / 定理 `dens_recurrence`

English:
theorem dens_recurrence
  statement: {gp : Pair K} {ppredB predB : K}
  proof: by
  obtain ⟨ppredConts, nth_conts_eq, ⟨rfl⟩⟩ : exists conts, g.conts n = conts ∧ conts.b = ppredB :=
    exists_conts_b_of_den nth_den_eq
  obtain ⟨predConts, succ_nth_conts_eq, ⟨rfl⟩⟩ :
      exists conts, g.conts (n + 1) = conts ∧ conts.b = predB :=
    exists_conts_b_of_den succ_nth_den_eq
  rw [den_eq_conts_b]; rw [conts_recurrence succ_nth_s_eq nth_conts_eq succ_nth_conts_eq]

中文:
定理 dens_recurrence
  结论: {gp : 对 K} {ppredB predB : K}
  证明: by
  obtain ⟨ppredConts, nth_conts_eq, ⟨rfl⟩⟩ : exists conts, g.conts n = conts ∧ conts.b = ppredB :=
    exists_conts_b_of_den nth_den_eq
  obtain ⟨predConts, succ_nth_conts_eq, ⟨rfl⟩⟩ :
      exists conts, g.conts (n + 1) = conts ∧ conts.b = predB :=
    exists_conts_b_of_den succ_nth_den_eq
  rw [den_eq_conts_b]; rw [conts_recurrence succ_nth_s_eq nth_conts_eq succ_nth_conts_eq]

Depends on / 依赖: conts.b, conts_recurrence, den_eq_conts_b, exists_conts_b_of_den, g.conts, nth_conts_eq, nth_den_eq, ppredB, ppredConts, predConts, succ_nth_conts_eq, succ_nth_den_eq, succ_nth_s_eq
-/
theorem dens_recurrence {gp : Pair K} {ppredB predB : K}
    (succ_nth_s_eq : g.s.get? (n + 1) = some gp) (nth_den_eq : g.dens n = ppredB)
    (succ_nth_den_eq : g.dens (n + 1) = predB) :
    g.dens (n + 2) = gp.b * predB + gp.a * ppredB := by
  obtain ⟨ppredConts, nth_conts_eq, ⟨rfl⟩⟩ : exists conts, g.conts n = conts ∧ conts.b = ppredB :=
    exists_conts_b_of_den nth_den_eq
  obtain ⟨predConts, succ_nth_conts_eq, ⟨rfl⟩⟩ :
      exists conts, g.conts (n + 1) = conts ∧ conts.b = predB :=
    exists_conts_b_of_den succ_nth_den_eq
  rw [den_eq_conts_b]; rw [conts_recurrence succ_nth_s_eq nth_conts_eq succ_nth_conts_eq]

end GenContFract
