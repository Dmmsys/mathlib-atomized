/-
Copyright (c) 2025 Antoine Chambert-Loir, María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, María Inés de Frutos-Fernández
-/
module

public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.CharP.Invertible
public import Mathlib.Data.Finset.NatAntidiagonal
public import Mathlib.Data.Nat.Choose.Basic

/-!
# Invertibility of factorials

This file contains lemmas providing sufficient conditions for the cast of `n!` to a (semi)ring `A`
to be a unit.

-/

public section

namespace IsUnit

open Nat
section Semiring

variable {A : Type*} [Semiring A]

/--
theorem `natCast_factorial_of_le` / 定理 `natCast_factorial_of_le`

English:
theorem natCast_factorial_of_le
  statement: {n : Nat} (hn_fac : IsUnit (n ! : A))
  proof: by
  obtain ⟨k, rfl⟩ := exists_add_of_le hmn
  clear hmn
  induction k generalizing m with
  | zero => simpa using hn_fac
  | succ k ih =>
    rw [← add_assoc]; rw [add_right_comm] at hn_fac
    have := ih hn_fac
    rw [Nat.factorial_succ]; rw [Nat.cast_mul]; rw [Nat.cast_commute _ _ |>.isUnit_mul_

中文:
定理 natCast_factorial_of_le
  结论: {n : 自然数} (hn_fac : IsUnit (n ! : A))
  证明: by
  obtain ⟨k, rfl⟩ := exists_add_of_le hmn
  clear hmn
  induction k generalizing m with
  | zero => simpa using hn_fac
  | succ k ih =>
    rw [← add_assoc]; rw [add_right_comm] at hn_fac
    have := ih hn_fac
    rw [Nat.factorial_succ]; rw [Nat.cast_mul]; rw [Nat.cast_commute _ _ |>.isUnit_mul_

Depends on / 依赖: Nat.cast_commute, Nat.cast_mul, Nat.factorial_succ, add_assoc, add_right_comm, cast_commute, cast_mul, exists_add_of_le, factorial_succ, generalizing, hn_fac, isUnit_mul_iff
-/
theorem natCast_factorial_of_le {n : Nat} (hn_fac : IsUnit (n ! : A))
    {m : Nat} (hmn : m <= n) : IsUnit (m ! : A) := by
  obtain ⟨k, rfl⟩ := exists_add_of_le hmn
  clear hmn
  induction k generalizing m with
  | zero => simpa using hn_fac
  | succ k ih =>
    rw [← add_assoc]; rw [add_right_comm] at hn_fac
    have := ih hn_fac
    rw [Nat.factorial_succ]; rw [Nat.cast_mul]; rw [Nat.cast_commute _ _ |>.isUnit_mul_iff] at this
    exact this.2

/--
theorem `natCast_factorial_of_lt` / 定理 `natCast_factorial_of_lt`

English:
theorem natCast_factorial_of_lt
  statement: {n : Nat} (hn_fac : IsUnit ((n - 1)! : A))
  proof: hn_fac.natCast_factorial_of_le le_sub_one_of_lt hmn

中文:
定理 natCast_factorial_of_lt
  结论: {n : 自然数} (hn_fac : IsUnit ((n - 1)! : A))
  证明: hn_fac.natCast_factorial_of_le le_sub_one_of_lt hmn

Depends on / 依赖: hn_fac, hn_fac.natCast_factorial_of_le, le_sub_one_of_lt, natCast_factorial_of_le
-/
theorem natCast_factorial_of_lt {n : Nat} (hn_fac : IsUnit ((n - 1)! : A))
    {m : Nat} (hmn : m < n) : IsUnit (m ! : A) :=
hn_fac.natCast_factorial_of_le le_sub_one_of_lt hmn

/--
theorem `natCast_factorial_of_algebra` / 定理 `natCast_factorial_of_algebra`

English:
theorem natCast_factorial_of_algebra
  given: (K : Type*) [Semifield K] [CharZero K] [Algebra K A] (n : Nat)
  proof: by
  suffices IsUnit (n ! : K) by
    simpa using this.map (algebraMap K A)
  simp [isUnit_iff_ne_zero, n.factorial_ne_zero]

中文:
定理 natCast_factorial_of_algebra
  条件: (K : 类型) [Semifield K] [CharZero K] [Algebra K A] (n : 自然数)
  证明: by
  suffices IsUnit (n ! : K) by
    simpa using this.map (algebraMap K A)
  simp [isUnit_iff_ne_zero, n.factorial_ne_zero]

Depends on / 依赖: IsUnit, algebraMap, factorial_ne_zero, isUnit_iff_ne_zero, n.factorial_ne_zero, this.map
-/
theorem natCast_factorial_of_algebra (K : Type*) [Semifield K] [CharZero K] [Algebra K A] (n : Nat) :
    IsUnit (n ! : A) := by
  suffices IsUnit (n ! : K) by
    simpa using this.map (algebraMap K A)
  simp [isUnit_iff_ne_zero, n.factorial_ne_zero]

end Semiring

section CharP

variable {A : Type*} [Ring A] (p : Nat) [Fact (Nat.Prime p)] [CharP A p]

/--
theorem `natCast_factorial_iff_of_charP` / 定理 `natCast_factorial_iff_of_charP`

English:
theorem natCast_factorial_iff_of_charP
  given: {n : Nat}
  statement: IsUnit (n ! : A) ↔ n < p
  proof: by
  have hp : p.Prime := Fact.out
  induction n with
  | zero => simp [hp.pos]
  | succ n ih =>
    -- TODO: why is `.symm.symm` needed here!?
    rw [factorial_succ]; rw [cast_mul]; rw [Nat.cast_commute _ _ |>.isUnit_mul_iff]; rw [ih.symm.symm]; rw [← Nat.add_one_le_iff]; rw [CharP.isUnit_natCast_

中文:
定理 natCast_factorial_iff_of_charP
  条件: {n : 自然数}
  结论: IsUnit (n ! : A) ↔ n < p
  证明: by
  have hp : p.Prime := Fact.out
  induction n with
  | zero => simp [hp.pos]
  | succ n ih =>
    -- TODO: why is `.symm.symm` needed here!?
    rw [factorial_succ]; rw [cast_mul]; rw [Nat.cast_commute _ _ |>.isUnit_mul_iff]; rw [ih.symm.symm]; rw [← Nat.add_one_le_iff]; rw [CharP.isUnit_natCast_

Depends on / 依赖: Fact.out, hp.pos, p.Prime
-/
theorem natCast_factorial_iff_of_charP {n : Nat} : IsUnit (n ! : A) ↔ n < p := by
  have hp : p.Prime := Fact.out
  induction n with
  | zero => simp [hp.pos]
  | succ n ih =>
    -- TODO: why is `.symm.symm` needed here!?
    rw [factorial_succ]; rw [cast_mul]; rw [Nat.cast_commute _ _ |>.isUnit_mul_iff]; rw [ih.symm.symm]; rw [← Nat.add_one_le_iff]; rw [CharP.isUnit_natCast_iff hp]
    exact ⟨fun ⟨h1, h2⟩ => lt_of_le_of_ne h2 (mt (· ▸ dvd_rfl) h1),
      fun h => ⟨not_dvd_of_pos_of_lt (Nat.succ_pos _) h, h.le⟩⟩

end CharP

section Nilpotent

variable {A : Type*} [CommRing A] {n p : Nat} (hp : IsNilpotent (p : A))
include hp

/--
lemma `natCast_of_isNilpotent_of_coprime` / 引理 `natCast_of_isNilpotent_of_coprime`

English:
lemma natCast_of_isNilpotent_of_coprime
  given: (h : p.Coprime n)
  proof: by
  obtain ⟨m, hm⟩ := hp
  suffices exists a b : A, p ^ m * a + n * b = 1 by
    obtain ⟨a, b, h⟩ := this
    refine .of_mul_eq_one b ?_
    simpa [hm] using h
  refine ⟨(p ^ m).gcdA n, (p ^ m).gcdB n, ?_⟩
  norm_cast
  rw [← Nat.cast_one]; rw [← Int.cast_natCast 1]; rw [← (h.pow_left m).gcd_eq_one

中文:
引理 natCast_of_isNilpotent_of_coprime
  条件: (h : p.Coprime n)
  证明: by
  obtain ⟨m, hm⟩ := hp
  suffices exists a b : A, p ^ m * a + n * b = 1 by
    obtain ⟨a, b, h⟩ := this
    refine .of_mul_eq_one b ?_
    simpa [hm] using h
  refine ⟨(p ^ m).gcdA n, (p ^ m).gcdB n, ?_⟩
  norm_cast
  rw [← Nat.cast_one]; rw [← Int.cast_natCast 1]; rw [← (h.pow_left m).gcd_eq_one

Depends on / 依赖: Int.cast_natCast, Nat.cast_one, Nat.gcd_eq_gcd_ab, cast_natCast, cast_one, gcd_eq_gcd_ab, gcd_eq_one, h.pow_left, of_mul_eq_one, pow_left
-/
lemma natCast_of_isNilpotent_of_coprime (h : p.Coprime n) :
    IsUnit (n : A) := by
  obtain ⟨m, hm⟩ := hp
  suffices exists a b : A, p ^ m * a + n * b = 1 by
    obtain ⟨a, b, h⟩ := this
    refine .of_mul_eq_one b ?_
    simpa [hm] using h
  refine ⟨(p ^ m).gcdA n, (p ^ m).gcdB n, ?_⟩
  norm_cast
  rw [← Nat.cast_one]; rw [← Int.cast_natCast 1]; rw [← (h.pow_left m).gcd_eq_one]; rw [Nat.gcd_eq_gcd_ab]

/--
theorem `natCast_factorial_of_isNilpotent` / 定理 `natCast_factorial_of_isNilpotent`

English:
theorem natCast_factorial_of_isNilpotent
  given: [Fact p.Prime] (h : n < p)
  proof: by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [factorial_succ, cast_mul, IsUnit.mul_iff]
    refine ⟨.natCast_of_isNilpotent_of_coprime hp ?_, ih (by lia)⟩
    rw [Nat.Prime.coprime_iff_not_dvd Fact.out]
    exact Nat.not_dvd_of_pos_of_lt (by lia) h

中文:
定理 natCast_factorial_of_isNilpotent
  条件: [Fact p.Prime] (h : n < p)
  证明: by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [factorial_succ, cast_mul, IsUnit.mul_iff]
    refine ⟨.natCast_of_isNilpotent_of_coprime hp ?_, ih (by lia)⟩
    rw [Nat.Prime.coprime_iff_not_dvd Fact.out]
    exact Nat.not_dvd_of_pos_of_lt (by lia) h

Depends on / 依赖: Fact.out, IsUnit, IsUnit.mul_iff, Nat.Prime.coprime_iff_not_dvd, Nat.not_dvd_of_pos_of_lt, cast_mul, coprime_iff_not_dvd, factorial_succ, mul_iff, natCast_of_isNilpotent_of_coprime, not_dvd_of_pos_of_lt
-/
theorem natCast_factorial_of_isNilpotent [Fact p.Prime] (h : n < p) :
    IsUnit (n ! : A) := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [factorial_succ, cast_mul, IsUnit.mul_iff]
    refine ⟨.natCast_of_isNilpotent_of_coprime hp ?_, ih (by lia)⟩
    rw [Nat.Prime.coprime_iff_not_dvd Fact.out]
    exact Nat.not_dvd_of_pos_of_lt (by lia) h

end Nilpotent

end IsUnit

open Nat Ring

/--
lemma `Nat.castChoose_eq` / 引理 `Nat.castChoose_eq`

English:
lemma Nat.castChoose_eq
  statement: {A : Type*} [CommSemiring A] {m : Nat} {k : Nat × Nat}
  proof: by
  rw [Finset.mem_antidiagonal] at hk
  subst hk
  rw [eq_mul_inverse_iff_mul_eq]; rw [eq_mul_inverse_iff_mul_eq]; rw [← Nat.cast_mul]; rw [← Nat.cast_mul]; rw [add_comm]; rw [Nat.add_choose_mul_factorial_mul_factorial] <;>
    apply hm.natCast_factorial_of_le
  exacts [Nat.le_add_right k.1 k.2, N

中文:
引理 Nat.castChoose_eq
  结论: {A : 类型} [CommSemiring A] {m : 自然数} {k : 自然数 × 自然数}
  证明: by
  rw [Finset.mem_antidiagonal] at hk
  subst hk
  rw [eq_mul_inverse_iff_mul_eq]; rw [eq_mul_inverse_iff_mul_eq]; rw [← Nat.cast_mul]; rw [← Nat.cast_mul]; rw [add_comm]; rw [Nat.add_choose_mul_factorial_mul_factorial] <;>
    apply hm.natCast_factorial_of_le
  exacts [Nat.le_add_right k.1 k.2, N

Depends on / 依赖: Finset, Finset.mem_antidiagonal, Nat.add_choose_mul_factorial_mul_factorial, Nat.cast_mul, Nat.le_add_left, Nat.le_add_right, add_choose_mul_factorial_mul_factorial, add_comm, cast_mul, eq_mul_inverse_iff_mul_eq, exacts, hm.natCast_factorial_of_le, le_add_left, le_add_right, mem_antidiagonal, natCast_factorial_of_le
-/
lemma Nat.castChoose_eq {A : Type*} [CommSemiring A] {m : Nat} {k : Nat × Nat}
    (hm : IsUnit (m ! : A)) (hk : k in Finset.antidiagonal m) :
    (choose m k.1 : A) = ↑m ! * inverse ↑k.1! * inverse ↑k.2! := by
  rw [Finset.mem_antidiagonal] at hk
  subst hk
  rw [eq_mul_inverse_iff_mul_eq]; rw [eq_mul_inverse_iff_mul_eq]; rw [← Nat.cast_mul]; rw [← Nat.cast_mul]; rw [add_comm]; rw [Nat.add_choose_mul_factorial_mul_factorial] <;>
    apply hm.natCast_factorial_of_le
  exacts [Nat.le_add_right k.1 k.2, Nat.le_add_left k.2 k.1]
