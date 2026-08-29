/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Johannes Hölzl, Kim Morrison, Jens Wagemaker
-/
module

public import Mathlib.Algebra.Order.Group.Finset
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Algebra.Polynomial.Eval.SMul
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.RingTheory.EuclideanDomain
public import Mathlib.RingTheory.UniqueFactorizationDomain.NormalizedFactors
public import Mathlib.Algebra.NoZeroSMulDivisors.Basic

/-!
# Theory of univariate polynomials

This file starts looking like the ring theory of $R[X]$

-/

@[expose] public section


noncomputable section

open Polynomial
open scoped Nat

namespace Polynomial

universe u v w y z

variable {R : Type u} {S : Type v} {k : Type y} {A : Type z} {a b : R} {n : Nat}

section CommRing

variable [CommRing R]

/--
theorem `rootMultiplicity_sub_one_le_derivative_rootMultiplicity_of_ne_zero` / 定理 `rootMultiplicity_sub_one_le_derivative_rootMultiplicity_of_ne_zero`

English:
theorem rootMultiplicity_sub_one_le_derivative_rootMultiplicity_of_ne_zero
  proof: (le_rootMultiplicity_iff hnezero).2
    pow_sub_one_dvd_derivative_of_pow_dvd (p.pow_rootMultiplicity_dvd t)

中文:
定理 rootMultiplicity_sub_one_le_derivative_rootMultiplicity_of_ne_zero
  证明: (le_rootMultiplicity_iff hnezero).2
    pow_sub_one_dvd_derivative_of_pow_dvd (p.pow_rootMultiplicity_dvd t)

Depends on / 依赖: hnezero, le_rootMultiplicity_iff, p.pow_rootMultiplicity_dvd, pow_rootMultiplicity_dvd, pow_sub_one_dvd_derivative_of_pow_dvd
-/
theorem rootMultiplicity_sub_one_le_derivative_rootMultiplicity_of_ne_zero
    (p : R[X]) (t : R) (hnezero : derivative p != 0) :
    p.rootMultiplicity t - 1 <= p.derivative.rootMultiplicity t :=
(le_rootMultiplicity_iff hnezero).2
    pow_sub_one_dvd_derivative_of_pow_dvd (p.pow_rootMultiplicity_dvd t)

/--
theorem `derivative_rootMultiplicity_of_root_of_mem_nonZeroDivisors` / 定理 `derivative_rootMultiplicity_of_root_of_mem_nonZeroDivisors`

English:
theorem derivative_rootMultiplicity_of_root_of_mem_nonZeroDivisors
  proof: by
  by_cases h : p = 0
  · simp only [h, map_zero, rootMultiplicity_zero]
  obtain ⟨g, hp, hndvd⟩ := p.exists_eq_pow_rootMultiplicity_mul_and_not_dvd h t
  set m := p.rootMultiplicity t
have hm : m - 1 + 1 = m := Nat.sub_add_cancel (rootMultiplicity_pos h).2 hpt
  have hndvd : ¬(X - C t) ^ m ∣ deri

中文:
定理 derivative_rootMultiplicity_of_root_of_mem_nonZeroDivisors
  证明: by
  by_cases h : p = 0
  · simp only [h, map_zero, rootMultiplicity_zero]
  obtain ⟨g, hp, hndvd⟩ := p.exists_eq_pow_rootMultiplicity_mul_and_not_dvd h t
  set m := p.rootMultiplicity t
have hm : m - 1 + 1 = m := Nat.sub_add_cancel (rootMultiplicity_pos h).2 hpt
  have hndvd : ¬(X - C t) ^ m ∣ deri

Depends on / 依赖: Nat.sub_add_cancel, derivative, derivative_X_sub_C_pow, derivative_mul, dvd_add_left, dvd_cancel_left_mem_n, dvd_mul_right, exists_eq_pow_rootMultiplicity_mul_and_not_dvd, map_zero, mul_assoc, mul_comm, p.exists_eq_pow_rootMultiplicity_mul_and_not_dvd, p.rootMultiplicity, pow_succ, rootMultiplicity, rootMultiplicity_pos, rootMultiplicity_zero, sub_add_cancel
-/
theorem derivative_rootMultiplicity_of_root_of_mem_nonZeroDivisors
    {p : R[X]} {t : R} (hpt : Polynomial.IsRoot p t)
    (hnzd : (p.rootMultiplicity t : R) in nonZeroDivisors R) :
    (derivative p).rootMultiplicity t = p.rootMultiplicity t - 1 := by
  by_cases h : p = 0
  · simp only [h, map_zero, rootMultiplicity_zero]
  obtain ⟨g, hp, hndvd⟩ := p.exists_eq_pow_rootMultiplicity_mul_and_not_dvd h t
  set m := p.rootMultiplicity t
have hm : m - 1 + 1 = m := Nat.sub_add_cancel (rootMultiplicity_pos h).2 hpt
  have hndvd : ¬(X - C t) ^ m ∣ derivative p := by
    rw [hp]; rw [derivative_mul]; rw [dvd_add_left (dvd_mul_right _ _)]; rw [derivative_X_sub_C_pow]; rw [← hm]; rw [pow_succ]; rw [hm]; rw [mul_comm (C _)]; rw [mul_assoc]; rw [dvd_cancel_left_mem_nonZeroDivisors (monic_X_sub_C t |>.pow _ |>.mem_nonZeroDivisors)]
    rw [dvd_iff_isRoot]; rw [IsRoot] at hndvd ⊢
    rwa [eval_mul, eval_C, mul_left_mem_nonZeroDivisors_eq_zero_iff hnzd]
  have hnezero : derivative p != 0 := fun h => hndvd (by rw [h]; exact dvd_zero _)
  exact le_antisymm (by rwa [rootMultiplicity_le_iff hnezero, hm])
    (rootMultiplicity_sub_one_le_derivative_rootMultiplicity_of_ne_zero _ t hnezero)

/--
theorem `isRoot_iterate_derivative_of_lt_rootMultiplicity` / 定理 `isRoot_iterate_derivative_of_lt_rootMultiplicity`

English:
theorem isRoot_iterate_derivative_of_lt_rootMultiplicity
  statement: {p : R[X]} {t : R} {n : Nat}
  proof: dvd_iff_isRoot.mp (dvd_pow_self _ <| Nat.sub_ne_zero_of_lt hn).trans
    (pow_sub_dvd_iterate_derivative_of_pow_dvd _ <| p.pow_rootMultiplicity_dvd t)

中文:
定理 isRoot_iterate_derivative_of_lt_rootMultiplicity
  结论: {p : R[X]} {t : R} {n : 自然数}
  证明: dvd_iff_isRoot.mp (dvd_pow_self _ <| Nat.sub_ne_zero_of_lt hn).trans
    (pow_sub_dvd_iterate_derivative_of_pow_dvd _ <| p.pow_rootMultiplicity_dvd t)

Depends on / 依赖: Nat.sub_ne_zero_of_lt, dvd_iff_isRoot, dvd_iff_isRoot.mp, dvd_pow_self, p.pow_rootMultiplicity_dvd, pow_rootMultiplicity_dvd, pow_sub_dvd_iterate_derivative_of_pow_dvd, sub_ne_zero_of_lt
-/
theorem isRoot_iterate_derivative_of_lt_rootMultiplicity {p : R[X]} {t : R} {n : Nat}
    (hn : n < p.rootMultiplicity t) : (derivative^[n] p).IsRoot t :=
dvd_iff_isRoot.mp (dvd_pow_self _ <| Nat.sub_ne_zero_of_lt hn).trans
    (pow_sub_dvd_iterate_derivative_of_pow_dvd _ <| p.pow_rootMultiplicity_dvd t)

open Finset in
/--
theorem `eval_iterate_derivative_rootMultiplicity` / 定理 `eval_iterate_derivative_rootMultiplicity`

English:
theorem eval_iterate_derivative_rootMultiplicity
  given: {p : R[X]} {t : R}
  proof: by
  set m := p.rootMultiplicity t with hm
  conv_lhs => rw [← p.pow_mul_divByMonic_rootMultiplicity_eq t, ← hm]
  rw [iterate_derivative_mul]; rw [eval_finsetSum]; rw [sum_eq_single_of_mem _ (mem_range.mpr m.succ_pos)]
  · rw [m.choose_zero_right, one_smul, eval_mul, m.sub_zero, iterate_derivative_

中文:
定理 eval_iterate_derivative_rootMultiplicity
  条件: {p : R[X]} {t : R}
  证明: by
  set m := p.rootMultiplicity t with hm
  conv_lhs => rw [← p.pow_mul_divByMonic_rootMultiplicity_eq t, ← hm]
  rw [iterate_derivative_mul]; rw [eval_finsetSum]; rw [sum_eq_single_of_mem _ (mem_range.mpr m.succ_pos)]
  · rw [m.choose_zero_right, one_smul, eval_mul, m.sub_zero, iterate_derivative_

Depends on / 依赖: Nat.sub_sub_self, choose_zero_right, conv_lhs, eval_finsetSum, eval_mul, eval_natCast, eval_pow, eval_smul, iterate_derivative_X_sub_pow, iterate_derivative_X_sub_pow_self, iterate_derivative_mul, m.choose_zero_right, m.sub_zero, m.succ_pos, mem_range, mem_range.mpr, mem_range_succ_iff, mem_range_succ_iff.mp, nsmul_eq_mul, one_smul
-/
theorem eval_iterate_derivative_rootMultiplicity {p : R[X]} {t : R} :
    (derivative^[p.rootMultiplicity t] p).eval t =
      (p.rootMultiplicity t).factorial • (p /ₘ (X - C t) ^ p.rootMultiplicity t).eval t := by
  set m := p.rootMultiplicity t with hm
  conv_lhs => rw [← p.pow_mul_divByMonic_rootMultiplicity_eq t, ← hm]
  rw [iterate_derivative_mul]; rw [eval_finsetSum]; rw [sum_eq_single_of_mem _ (mem_range.mpr m.succ_pos)]
  · rw [m.choose_zero_right, one_smul, eval_mul, m.sub_zero, iterate_derivative_X_sub_pow_self,
      eval_natCast, nsmul_eq_mul]; rfl
  · intro b hb hb0
    rw [iterate_derivative_X_sub_pow]; rw [eval_smul]; rw [eval_mul]; rw [eval_smul]; rw [eval_pow]; rw [Nat.sub_sub_self (mem_range_succ_iff.mp hb)]; rw [eval_sub]; rw [eval_X]; rw [eval_C]; rw [sub_self]; rw [zero_pow hb0]; rw [smul_zero]; rw [zero_mul]; rw [smul_zero]

/--
theorem `lt_rootMultiplicity_of_isRoot_iterate_derivative_of_mem_nonZeroDivisors` / 定理 `lt_rootMultiplicity_of_isRoot_iterate_derivative_of_mem_nonZeroDivisors`

English:
theorem lt_rootMultiplicity_of_isRoot_iterate_derivative_of_mem_nonZeroDivisors
  proof: by
  by_contra! h'
  replace hroot := hroot _ h'
  simp only [IsRoot, eval_iterate_derivative_rootMultiplicity] at hroot
  obtain ⟨q, hq⟩ : ((rootMultiplicity t p)! : R) ∣ n ! := by gcongr
  rw [hq]; rw [mul_mem_nonZeroDivisors] at hnzd
  rw [nsmul_eq_mul]; rw [mul_left_mem_nonZeroDivisors_eq_zero_i

中文:
定理 lt_rootMultiplicity_of_isRoot_iterate_derivative_of_mem_nonZeroDivisors
  证明: by
  by_contra! h'
  replace hroot := hroot _ h'
  simp only [IsRoot, eval_iterate_derivative_rootMultiplicity] at hroot
  obtain ⟨q, hq⟩ : ((rootMultiplicity t p)! : R) ∣ n ! := by gcongr
  rw [hq]; rw [mul_mem_nonZeroDivisors] at hnzd
  rw [nsmul_eq_mul]; rw [mul_left_mem_nonZeroDivisors_eq_zero_i

Depends on / 依赖: IsRoot, eval_divByMonic_pow_rootMultiplicity_ne_zero, eval_iterate_derivative_rootMultiplicity, mul_left_mem_nonZeroDivisors_eq_zero_iff, mul_mem_nonZeroDivisors, nsmul_eq_mul, replace, rootMultiplicity
-/
theorem lt_rootMultiplicity_of_isRoot_iterate_derivative_of_mem_nonZeroDivisors
    {p : R[X]} {t : R} {n : Nat} (h : p != 0)
    (hroot : forall m <= n, (derivative^[m] p).IsRoot t)
    (hnzd : (n.factorial : R) in nonZeroDivisors R) :
    n < p.rootMultiplicity t := by
  by_contra! h'
  replace hroot := hroot _ h'
  simp only [IsRoot, eval_iterate_derivative_rootMultiplicity] at hroot
  obtain ⟨q, hq⟩ : ((rootMultiplicity t p)! : R) ∣ n ! := by gcongr
  rw [hq]; rw [mul_mem_nonZeroDivisors] at hnzd
  rw [nsmul_eq_mul]; rw [mul_left_mem_nonZeroDivisors_eq_zero_iff hnzd.1] at hroot
  exact eval_divByMonic_pow_rootMultiplicity_ne_zero t h hroot

/--
theorem `lt_rootMultiplicity_of_isRoot_iterate_derivative_of_mem_nonZeroDivisors'` / 定理 `lt_rootMultiplicity_of_isRoot_iterate_derivative_of_mem_nonZeroDivisors'`

English:
theorem lt_rootMultiplicity_of_isRoot_iterate_derivative_of_mem_nonZeroDivisors'
  proof: by
  apply lt_rootMultiplicity_of_isRoot_iterate_derivative_of_mem_nonZeroDivisors h hroot
  clear hroot
  induction n with
  | zero =>
    simp only [Nat.factorial_zero, Nat.cast_one]
    exact Submonoid.one_mem _
  | succ n ih =>
    rw [Nat.factorial_succ]; rw [Nat.cast_mul]; rw [mul_mem_nonZeroD

中文:
定理 lt_rootMultiplicity_of_isRoot_iterate_derivative_of_mem_nonZeroDivisors'
  证明: by
  apply lt_rootMultiplicity_of_isRoot_iterate_derivative_of_mem_nonZeroDivisors h hroot
  clear hroot
  induction n with
  | zero =>
    simp only [Nat.factorial_zero, Nat.cast_one]
    exact Submonoid.one_mem _
  | succ n ih =>
    rw [Nat.factorial_succ]; rw [Nat.cast_mul]; rw [mul_mem_nonZeroD

Depends on / 依赖: Nat.cast_mul, Nat.cast_one, Nat.factorial_succ, Nat.factorial_zero, Submonoid, Submonoid.one_mem, cast_mul, cast_one, factorial_succ, factorial_zero, h.trans, le_rfl, le_succ, lt_rootMultiplicity_of_isRoot_iterate_derivative_of_mem_nonZeroDivisors, mul_mem_nonZeroDivisors, n.le_succ, n.succ_ne_zero, one_mem, succ_ne_zero
-/
theorem lt_rootMultiplicity_of_isRoot_iterate_derivative_of_mem_nonZeroDivisors'
    {p : R[X]} {t : R} {n : Nat} (h : p != 0)
    (hroot : forall m <= n, (derivative^[m] p).IsRoot t)
    (hnzd : forall m <= n, m != 0 -> (m : R) in nonZeroDivisors R) :
    n < p.rootMultiplicity t := by
  apply lt_rootMultiplicity_of_isRoot_iterate_derivative_of_mem_nonZeroDivisors h hroot
  clear hroot
  induction n with
  | zero =>
    simp only [Nat.factorial_zero, Nat.cast_one]
    exact Submonoid.one_mem _
  | succ n ih =>
    rw [Nat.factorial_succ]; rw [Nat.cast_mul]; rw [mul_mem_nonZeroDivisors]
    exact ⟨hnzd _ le_rfl n.succ_ne_zero, ih fun m h => hnzd m (h.trans n.le_succ)⟩

/--
theorem `lt_rootMultiplicity_iff_isRoot_iterate_derivative_of_mem_nonZeroDivisors` / 定理 `lt_rootMultiplicity_iff_isRoot_iterate_derivative_of_mem_nonZeroDivisors`

English:
theorem lt_rootMultiplicity_iff_isRoot_iterate_derivative_of_mem_nonZeroDivisors
  proof: ⟨fun hn _ hm => isRoot_iterate_derivative_of_lt_rootMultiplicity hm.trans_lt hn,
    fun hr => lt_rootMultiplicity_of_isRoot_iterate_derivative_of_mem_nonZeroDivisors h hr hnzd⟩

中文:
定理 lt_rootMultiplicity_iff_isRoot_iterate_derivative_of_mem_nonZeroDivisors
  证明: ⟨fun hn _ hm => isRoot_iterate_derivative_of_lt_rootMultiplicity hm.trans_lt hn,
    fun hr => lt_rootMultiplicity_of_isRoot_iterate_derivative_of_mem_nonZeroDivisors h hr hnzd⟩

Depends on / 依赖: hm.trans_lt, isRoot_iterate_derivative_of_lt_rootMultiplicity, lt_rootMultiplicity_of_isRoot_iterate_derivative_of_mem_nonZeroDivisors, trans_lt
-/
theorem lt_rootMultiplicity_iff_isRoot_iterate_derivative_of_mem_nonZeroDivisors
    {p : R[X]} {t : R} {n : Nat} (h : p != 0)
    (hnzd : (n.factorial : R) in nonZeroDivisors R) :
    n < p.rootMultiplicity t ↔ forall m <= n, (derivative^[m] p).IsRoot t :=
⟨fun hn _ hm => isRoot_iterate_derivative_of_lt_rootMultiplicity hm.trans_lt hn,
    fun hr => lt_rootMultiplicity_of_isRoot_iterate_derivative_of_mem_nonZeroDivisors h hr hnzd⟩

/--
theorem `lt_rootMultiplicity_iff_isRoot_iterate_derivative_of_mem_nonZeroDivisors'` / 定理 `lt_rootMultiplicity_iff_isRoot_iterate_derivative_of_mem_nonZeroDivisors'`

English:
theorem lt_rootMultiplicity_iff_isRoot_iterate_derivative_of_mem_nonZeroDivisors'
  proof: ⟨fun hn _ hm => isRoot_iterate_derivative_of_lt_rootMultiplicity Nat.lt_of_le_of_lt hm hn,
    fun hr => lt_rootMultiplicity_of_isRoot_iterate_derivative_of_mem_nonZeroDivisors' h hr hnzd⟩

中文:
定理 lt_rootMultiplicity_iff_isRoot_iterate_derivative_of_mem_nonZeroDivisors'
  证明: ⟨fun hn _ hm => isRoot_iterate_derivative_of_lt_rootMultiplicity Nat.lt_of_le_of_lt hm hn,
    fun hr => lt_rootMultiplicity_of_isRoot_iterate_derivative_of_mem_nonZeroDivisors' h hr hnzd⟩

Depends on / 依赖: Nat.lt_of_le_of_lt, isRoot_iterate_derivative_of_lt_rootMultiplicity, lt_of_le_of_lt, lt_rootMultiplicity_of_isRoot_iterate_derivative_of_mem_nonZeroDivisors
-/
theorem lt_rootMultiplicity_iff_isRoot_iterate_derivative_of_mem_nonZeroDivisors'
    {p : R[X]} {t : R} {n : Nat} (h : p != 0)
    (hnzd : forall m <= n, m != 0 -> (m : R) in nonZeroDivisors R) :
    n < p.rootMultiplicity t ↔ forall m <= n, (derivative^[m] p).IsRoot t :=
⟨fun hn _ hm => isRoot_iterate_derivative_of_lt_rootMultiplicity Nat.lt_of_le_of_lt hm hn,
    fun hr => lt_rootMultiplicity_of_isRoot_iterate_derivative_of_mem_nonZeroDivisors' h hr hnzd⟩

/--
theorem `one_lt_rootMultiplicity_iff_isRoot_iterate_derivative` / 定理 `one_lt_rootMultiplicity_iff_isRoot_iterate_derivative`

English:
theorem one_lt_rootMultiplicity_iff_isRoot_iterate_derivative
  proof: lt_rootMultiplicity_iff_isRoot_iterate_derivative_of_mem_nonZeroDivisors h
    (by rw [Nat.factorial_one, Nat.cast_one]; exact Submonoid.one_mem _)

中文:
定理 one_lt_rootMultiplicity_iff_isRoot_iterate_derivative
  证明: lt_rootMultiplicity_iff_isRoot_iterate_derivative_of_mem_nonZeroDivisors h
    (by rw [Nat.factorial_one, Nat.cast_one]; exact Submonoid.one_mem _)

Depends on / 依赖: Nat.cast_one, Nat.factorial_one, Submonoid, Submonoid.one_mem, cast_one, factorial_one, lt_rootMultiplicity_iff_isRoot_iterate_derivative_of_mem_nonZeroDivisors, one_mem
-/
theorem one_lt_rootMultiplicity_iff_isRoot_iterate_derivative
    {p : R[X]} {t : R} (h : p != 0) :
    1 < p.rootMultiplicity t ↔ forall m <= 1, (derivative^[m] p).IsRoot t :=
  lt_rootMultiplicity_iff_isRoot_iterate_derivative_of_mem_nonZeroDivisors h
    (by rw [Nat.factorial_one, Nat.cast_one]; exact Submonoid.one_mem _)

/--
theorem `one_lt_rootMultiplicity_iff_isRoot` / 定理 `one_lt_rootMultiplicity_iff_isRoot`

English:
theorem one_lt_rootMultiplicity_iff_isRoot
  proof: by
  rw [one_lt_rootMultiplicity_iff_isRoot_iterate_derivative h]
  refine ⟨fun h => ⟨h 0 (by simp), h 1 (by simp)⟩, fun ⟨h0, h1⟩ m hm => ?_⟩
  obtain (_ | _ | m) := m
  exacts [h0, h1, by lia]

中文:
定理 one_lt_rootMultiplicity_iff_isRoot
  证明: by
  rw [one_lt_rootMultiplicity_iff_isRoot_iterate_derivative h]
  refine ⟨fun h => ⟨h 0 (by simp), h 1 (by simp)⟩, fun ⟨h0, h1⟩ m hm => ?_⟩
  obtain (_ | _ | m) := m
  exacts [h0, h1, by lia]

Depends on / 依赖: exacts, one_lt_rootMultiplicity_iff_isRoot_iterate_derivative
-/
theorem one_lt_rootMultiplicity_iff_isRoot
    {p : R[X]} {t : R} (h : p != 0) :
    1 < p.rootMultiplicity t ↔ p.IsRoot t ∧ (derivative p).IsRoot t := by
  rw [one_lt_rootMultiplicity_iff_isRoot_iterate_derivative h]
  refine ⟨fun h => ⟨h 0 (by simp), h 1 (by simp)⟩, fun ⟨h0, h1⟩ m hm => ?_⟩
  obtain (_ | _ | m) := m
  exacts [h0, h1, by lia]

end CommRing

section IsDomain

variable [CommRing R]

/--
theorem `one_lt_rootMultiplicity_iff_isRoot_gcd` / 定理 `one_lt_rootMultiplicity_iff_isRoot_gcd`

English:
theorem one_lt_rootMultiplicity_iff_isRoot_gcd
  proof: by
  simp_rw [one_lt_rootMultiplicity_iff_isRoot h, ← dvd_iff_isRoot, dvd_gcd_iff]

中文:
定理 one_lt_rootMultiplicity_iff_isRoot_gcd
  证明: by
  simp_rw [one_lt_rootMultiplicity_iff_isRoot h, ← dvd_iff_isRoot, dvd_gcd_iff]

Depends on / 依赖: dvd_gcd_iff, dvd_iff_isRoot, one_lt_rootMultiplicity_iff_isRoot, simp_rw
-/
theorem one_lt_rootMultiplicity_iff_isRoot_gcd
    [GCDMonoid R[X]] {p : R[X]} {t : R} (h : p != 0) :
    1 < p.rootMultiplicity t ↔ (gcd p (derivative p)).IsRoot t := by
  simp_rw [one_lt_rootMultiplicity_iff_isRoot h, ← dvd_iff_isRoot, dvd_gcd_iff]

variable [NoZeroDivisors R]

/--
theorem `derivative_rootMultiplicity_of_root` / 定理 `derivative_rootMultiplicity_of_root`

English:
theorem derivative_rootMultiplicity_of_root
  given: [CharZero R] {p : R[X]} {t : R} (hpt : p.IsRoot t)
  proof: by
  by_cases h : p = 0
  · rw [h, map_zero, rootMultiplicity_zero]
exact derivative_rootMultiplicity_of_root_of_mem_nonZeroDivisors hpt
mem_nonZeroDivisors_of_ne_zero Nat.cast_ne_zero.2 ((rootMultiplicity_pos h).2 hpt).ne'

中文:
定理 derivative_rootMultiplicity_of_root
  条件: [CharZero R] {p : R[X]} {t : R} (hpt : p.IsRoot t)
  证明: by
  by_cases h : p = 0
  · rw [h, map_zero, rootMultiplicity_zero]
exact derivative_rootMultiplicity_of_root_of_mem_nonZeroDivisors hpt
mem_nonZeroDivisors_of_ne_zero Nat.cast_ne_zero.2 ((rootMultiplicity_pos h).2 hpt).ne'

Depends on / 依赖: Nat.cast_ne_zero, cast_ne_zero, derivative_rootMultiplicity_of_root_of_mem_nonZeroDivisors, map_zero, mem_nonZeroDivisors_of_ne_zero, rootMultiplicity_pos, rootMultiplicity_zero
-/
theorem derivative_rootMultiplicity_of_root [CharZero R] {p : R[X]} {t : R} (hpt : p.IsRoot t) :
    p.derivative.rootMultiplicity t = p.rootMultiplicity t - 1 := by
  by_cases h : p = 0
  · rw [h, map_zero, rootMultiplicity_zero]
exact derivative_rootMultiplicity_of_root_of_mem_nonZeroDivisors hpt
mem_nonZeroDivisors_of_ne_zero Nat.cast_ne_zero.2 ((rootMultiplicity_pos h).2 hpt).ne'

/--
theorem `rootMultiplicity_sub_one_le_derivative_rootMultiplicity` / 定理 `rootMultiplicity_sub_one_le_derivative_rootMultiplicity`

English:
theorem rootMultiplicity_sub_one_le_derivative_rootMultiplicity
  given: [CharZero R] (p : R[X]) (t : R)
  proof: by
  by_cases h : p.IsRoot t
  · exact (derivative_rootMultiplicity_of_root h).symm.le
  · simp [rootMultiplicity_eq_zero h]

中文:
定理 rootMultiplicity_sub_one_le_derivative_rootMultiplicity
  条件: [CharZero R] (p : R[X]) (t : R)
  证明: by
  by_cases h : p.IsRoot t
  · exact (derivative_rootMultiplicity_of_root h).symm.le
  · simp [rootMultiplicity_eq_zero h]

Depends on / 依赖: IsRoot, derivative_rootMultiplicity_of_root, p.IsRoot, rootMultiplicity_eq_zero, symm.le
-/
theorem rootMultiplicity_sub_one_le_derivative_rootMultiplicity [CharZero R] (p : R[X]) (t : R) :
    p.rootMultiplicity t - 1 <= p.derivative.rootMultiplicity t := by
  by_cases h : p.IsRoot t
  · exact (derivative_rootMultiplicity_of_root h).symm.le
  · simp [rootMultiplicity_eq_zero h]

/--
theorem `lt_rootMultiplicity_of_isRoot_iterate_derivative` / 定理 `lt_rootMultiplicity_of_isRoot_iterate_derivative`

English:
theorem lt_rootMultiplicity_of_isRoot_iterate_derivative
  proof: lt_rootMultiplicity_of_isRoot_iterate_derivative_of_mem_nonZeroDivisors h hroot
mem_nonZeroDivisors_of_ne_zero Nat.cast_ne_zero.2 by positivity

中文:
定理 lt_rootMultiplicity_of_isRoot_iterate_derivative
  证明: lt_rootMultiplicity_of_isRoot_iterate_derivative_of_mem_nonZeroDivisors h hroot
mem_nonZeroDivisors_of_ne_zero Nat.cast_ne_zero.2 by positivity

Depends on / 依赖: Nat.cast_ne_zero, cast_ne_zero, lt_rootMultiplicity_of_isRoot_iterate_derivative_of_mem_nonZeroDivisors, mem_nonZeroDivisors_of_ne_zero
-/
theorem lt_rootMultiplicity_of_isRoot_iterate_derivative
    [CharZero R] {p : R[X]} {t : R} {n : Nat} (h : p != 0)
    (hroot : forall m <= n, (derivative^[m] p).IsRoot t) :
    n < p.rootMultiplicity t :=
lt_rootMultiplicity_of_isRoot_iterate_derivative_of_mem_nonZeroDivisors h hroot
mem_nonZeroDivisors_of_ne_zero Nat.cast_ne_zero.2 by positivity

/--
theorem `lt_rootMultiplicity_iff_isRoot_iterate_derivative` / 定理 `lt_rootMultiplicity_iff_isRoot_iterate_derivative`

English:
theorem lt_rootMultiplicity_iff_isRoot_iterate_derivative
  proof: ⟨fun hn _ hm => isRoot_iterate_derivative_of_lt_rootMultiplicity Nat.lt_of_le_of_lt hm hn,
    fun hr => lt_rootMultiplicity_of_isRoot_iterate_derivative h hr⟩

中文:
定理 lt_rootMultiplicity_iff_isRoot_iterate_derivative
  证明: ⟨fun hn _ hm => isRoot_iterate_derivative_of_lt_rootMultiplicity Nat.lt_of_le_of_lt hm hn,
    fun hr => lt_rootMultiplicity_of_isRoot_iterate_derivative h hr⟩

Depends on / 依赖: Nat.lt_of_le_of_lt, isRoot_iterate_derivative_of_lt_rootMultiplicity, lt_of_le_of_lt, lt_rootMultiplicity_of_isRoot_iterate_derivative
-/
theorem lt_rootMultiplicity_iff_isRoot_iterate_derivative
    [CharZero R] {p : R[X]} {t : R} {n : Nat} (h : p != 0) :
    n < p.rootMultiplicity t ↔ forall m <= n, (derivative^[m] p).IsRoot t :=
⟨fun hn _ hm => isRoot_iterate_derivative_of_lt_rootMultiplicity Nat.lt_of_le_of_lt hm hn,
    fun hr => lt_rootMultiplicity_of_isRoot_iterate_derivative h hr⟩

/--
theorem `isRoot_of_isRoot_of_dvd_derivative_mul` / 定理 `isRoot_of_isRoot_of_dvd_derivative_mul`

English:
theorem isRoot_of_isRoot_of_dvd_derivative_mul
  statement: [CharZero R] {f g : R[X]} (hf0 : f != 0)
  proof: by
  rcases hfd with ⟨r, hr⟩
  have hdf0 : derivative f != 0 := by
    contrapose haf
    rw [eq_C_of_derivative_eq_zero haf] at hf0 ⊢
exact not_isRoot_C _ _ C_ne_zero.mp hf0
  by_contra hg
  have hdfg0 : f.derivative * g != 0 := mul_ne_zero hdf0 (by rintro rfl; simp at hg)
  have hr' := congr_arg (

中文:
定理 isRoot_of_isRoot_of_dvd_derivative_mul
  结论: [CharZero R] {f g : R[X]} (hf0 : f != 0)
  证明: by
  rcases hfd with ⟨r, hr⟩
  have hdf0 : derivative f != 0 := by
    contrapose haf
    rw [eq_C_of_derivative_eq_zero haf] at hf0 ⊢
exact not_isRoot_C _ _ C_ne_zero.mp hf0
  by_contra hg
  have hdfg0 : f.derivative * g != 0 := mul_ne_zero hdf0 (by rintro rfl; simp at hg)
  have hr' := congr_arg (

Depends on / 依赖: C_ne_zero, C_ne_zero.mp, IsDomain, add_zero, congr_arg, contrapose, derivative, derivative_rootMultiplicity_of_root, eq_C_of_derivative_eq_zero, f.derivative, mul_ne_zero, not_isRoot_C, rootMultiplicity, rootMultiplicity_eq_zero, rootMultiplicity_mul
-/
theorem isRoot_of_isRoot_of_dvd_derivative_mul [CharZero R] {f g : R[X]} (hf0 : f != 0)
    (hfd : f ∣ f.derivative * g) {a : R} (haf : f.IsRoot a) : g.IsRoot a := by
  rcases hfd with ⟨r, hr⟩
  have hdf0 : derivative f != 0 := by
    contrapose haf
    rw [eq_C_of_derivative_eq_zero haf] at hf0 ⊢
exact not_isRoot_C _ _ C_ne_zero.mp hf0
  by_contra hg
  have hdfg0 : f.derivative * g != 0 := mul_ne_zero hdf0 (by rintro rfl; simp at hg)
  have hr' := congr_arg (rootMultiplicity a) hr
  have : IsDomain R := {}
  rw [rootMultiplicity_mul hdfg0]; rw [derivative_rootMultiplicity_of_root haf]; rw [rootMultiplicity_eq_zero hg]; rw [add_zero]; rw [rootMultiplicity_mul (hr ▸ hdfg0)]; rw [add_comm]; rw [Nat.sub_eq_iff_eq_add (Nat.succ_le_iff.2 ((rootMultiplicity_pos hf0).2 haf))] at hr'
  lia


/--
Instance `instNormalizationMonoid` / 实例 `instNormalizationMonoid`

English:
instance instNormalizationMonoid
  signature: [NormalizationMonoid R]
  body: ⟨C ↑(normUnit p.leadingCoeff), C ↑(normUnit p.leadingCoeff)⁻¹, by
      rw [← map_mul]; rw [Units.mul_inv]; rw [C_1], by rw [← map_mul, Units.inv_mul, C_1]⟩
  normUnit_zero := Units.ext (by simp)
  normUnit_one := Units.ext (by simp)
normUnit_mul_units u h := Units.ext by
    dsimp only [Units.val_m

中文:
实例 instNormalizationMonoid
  签名: [NormalizationMonoid R]
  定义体: ⟨C ↑(normUnit p.leadingCoeff), C ↑(normUnit p.leadingCoeff)⁻¹, by
      rw [← map_mul]; rw [Units.mul_inv]; rw [C_1], by rw [← map_mul, Units.inv_mul, C_1]⟩
  normUnit_zero := Units.ext (by simp)
  normUnit_one := Units.ext (by simp)
normUnit_mul_units u h := Units.ext by
    dsimp only [Units.val_m

Depends on / 依赖: Units.eq_inv_mul_iff_mul_eq, Units.ext, Units.inv_mul, Units.mul_inv, Units.val_mul, eq_inv_mul_iff_mul_eq, inv_mul, isUnit_iff, leadingCoeff, leadingCoeff_C, leadingCoeff_mul, leadingCoeff_ne_zero, map_mul, mul_inv, normUnit, normUnit_mul_units, normUnit_one, normUnit_zero, p.leadingCoeff, val_mul
-/
instance instNormalizationMonoid [NormalizationMonoid R] : NormalizationMonoid R[X] where
  normUnit p :=
    ⟨C ↑(normUnit p.leadingCoeff), C ↑(normUnit p.leadingCoeff)⁻¹, by
      rw [← map_mul]; rw [Units.mul_inv]; rw [C_1], by rw [← map_mul, Units.inv_mul, C_1]⟩
  normUnit_zero := Units.ext (by simp)
  normUnit_one := Units.ext (by simp)
normUnit_mul_units u h := Units.ext by
    dsimp only [Units.val_mul]
    obtain ⟨_, ⟨w, rfl⟩, h2⟩ := isUnit_iff.1 ⟨u, rfl⟩
    rw [leadingCoeff_mul]; rw [← h2]; rw [leadingCoeff_C]; rw [normUnit_mul_units _ (leadingCoeff_ne_zero.2 h)]; rw [Units.eq_inv_mul_iff_mul_eq]; rw [Units.val_mul]; rw [C_mul]; rw [← mul_assoc]; rw [← h2]; rw [← C_mul]
    simp

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [StrongNormalizationMonoid
  signature: R] : StrongNormalizationMonoid R[X] where
  body: Units.ext
      (by
        dsimp
        rw [Ne]; rw [← leadingCoeff_eq_zero] at *
        simp_rw [normUnit, leadingCoeff_mul, normUnit_mul hp0 hq0, Units.val_mul, C_mul])
  normUnit_coe_units := normUnit_coe_units

中文:
实例 [StrongNormalizationMonoid
  签名: R] : StrongNormalizationMonoid R[X] where
  定义体: Units.ext
      (by
        dsimp
        rw [Ne]; rw [← leadingCoeff_eq_zero] at *
        simp_rw [normUnit, leadingCoeff_mul, normUnit_mul hp0 hq0, Units.val_mul, C_mul])
  normUnit_coe_units := normUnit_coe_units

Depends on / 依赖: C_mul, Units.ext, Units.val_mul, leadingCoeff_eq_zero, leadingCoeff_mul, normUnit, normUnit_coe_units, normUnit_mul, simp_rw, val_mul
-/
instance [StrongNormalizationMonoid R] : StrongNormalizationMonoid R[X] where
  normUnit_mul hp0 hq0 :=
    Units.ext
      (by
        dsimp
        rw [Ne]; rw [← leadingCoeff_eq_zero] at *
        simp_rw [normUnit, leadingCoeff_mul, normUnit_mul hp0 hq0, Units.val_mul, C_mul])
  normUnit_coe_units := normUnit_coe_units

section NormalizationMonoid

variable [NormalizationMonoid R]

@[simp]
/--
theorem `coe_normUnit` / 定理 `coe_normUnit`

English:
theorem coe_normUnit
  given: {p : R[X]}
  statement: (normUnit p : R[X]) = C ↑(normUnit p.leadingCoeff)
  proof: by
  simp [normUnit]

@[simp]

中文:
定理 coe_normUnit
  条件: {p : R[X]}
  结论: (normUnit p : R[X]) = C ↑(normUnit p.leadingCoeff)
  证明: by
  simp [normUnit]

@[simp]

Depends on / 依赖: normUnit
-/
theorem coe_normUnit {p : R[X]} : (normUnit p : R[X]) = C ↑(normUnit p.leadingCoeff) := by
  simp [normUnit]

@[simp]
/--
theorem `leadingCoeff_normalize` / 定理 `leadingCoeff_normalize`

English:
theorem leadingCoeff_normalize
  given: (p : R[X])
  proof: by simp [normalize_apply]

中文:
定理 leadingCoeff_normalize
  条件: (p : R[X])
  证明: by simp [normalize_apply]

Depends on / 依赖: normalize_apply
-/
theorem leadingCoeff_normalize (p : R[X]) :
    leadingCoeff (normalize p) = normalize (leadingCoeff p) := by simp [normalize_apply]

/--
theorem `Monic.normalize_eq_self` / 定理 `Monic.normalize_eq_self`

English:
theorem Monic.normalize_eq_self
  given: {p : R[X]} (hp : p.Monic)
  statement: normalize p = p
  proof: by
  simp only [Polynomial.coe_normUnit, normalize_apply, hp.leadingCoeff, normUnit_one,
    Units.val_one, Polynomial.C.map_one, mul_one]

中文:
定理 Monic.normalize_eq_self
  条件: {p : R[X]} (hp : p.Monic)
  结论: normalize p = p
  证明: by
  simp only [Polynomial.coe_normUnit, normalize_apply, hp.leadingCoeff, normUnit_one,
    Units.val_one, Polynomial.C.map_one, mul_one]

Depends on / 依赖: Polynomial, Polynomial.C.map_one, Polynomial.coe_normUnit, Units.val_one, coe_normUnit, hp.leadingCoeff, leadingCoeff, map_one, mul_one, normUnit_one, normalize_apply, val_one
-/
theorem Monic.normalize_eq_self {p : R[X]} (hp : p.Monic) : normalize p = p := by
  simp only [Polynomial.coe_normUnit, normalize_apply, hp.leadingCoeff, normUnit_one,
    Units.val_one, Polynomial.C.map_one, mul_one]

/--
theorem `roots_normalize` / 定理 `roots_normalize`

English:
theorem roots_normalize
  given: {R} [CommRing R] [IsDomain R] [NormalizationMonoid R] {p : R[X]}
  proof: by
  rw [normalize_apply]; rw [mul_comm]; rw [coe_normUnit]; rw [roots_C_mul _ (normUnit (leadingCoeff p)).ne_zero]

中文:
定理 roots_normalize
  条件: {R} [CommRing R] [IsDomain R] [NormalizationMonoid R] {p : R[X]}
  证明: by
  rw [normalize_apply]; rw [mul_comm]; rw [coe_normUnit]; rw [roots_C_mul _ (normUnit (leadingCoeff p)).ne_zero]

Depends on / 依赖: coe_normUnit, leadingCoeff, mul_comm, ne_zero, normUnit, normalize_apply, roots_C_mul
-/
theorem roots_normalize {R} [CommRing R] [IsDomain R] [NormalizationMonoid R] {p : R[X]} :
    (normalize p).roots = p.roots := by
  rw [normalize_apply]; rw [mul_comm]; rw [coe_normUnit]; rw [roots_C_mul _ (normUnit (leadingCoeff p)).ne_zero]

/--
theorem `normUnit_X` / 定理 `normUnit_X`

English:
theorem normUnit_X
  statement: normUnit (X : R[X]) = 1
  proof: by
  have := coe_normUnit (R := R) (p := X)
  rwa [leadingCoeff_X, normUnit_one, Units.val_one, map_one, Units.val_eq_one] at this

中文:
定理 normUnit_X
  结论: normUnit (X : R[X]) = 1
  证明: by
  have := coe_normUnit (R := R) (p := X)
  rwa [leadingCoeff_X, normUnit_one, Units.val_one, map_one, Units.val_eq_one] at this

Depends on / 依赖: Units.val_eq_one, Units.val_one, coe_normUnit, leadingCoeff_X, map_one, normUnit_one, val_eq_one, val_one
-/
theorem normUnit_X : normUnit (X : R[X]) = 1 := by
  have := coe_normUnit (R := R) (p := X)
  rwa [leadingCoeff_X, normUnit_one, Units.val_one, map_one, Units.val_eq_one] at this

/--
theorem `X_eq_normalize` / 定理 `X_eq_normalize`

English:
theorem X_eq_normalize
  statement: X = normalize (X : R[X])
  proof: by
  simp only [normalize_apply, normUnit_X, Units.val_one, mul_one]

中文:
定理 X_eq_normalize
  结论: X = normalize (X : R[X])
  证明: by
  simp only [normalize_apply, normUnit_X, Units.val_one, mul_one]

Depends on / 依赖: Units.val_one, mul_one, normUnit_X, normalize_apply, val_one
-/
theorem X_eq_normalize : X = normalize (X : R[X]) := by
  simp only [normalize_apply, normUnit_X, Units.val_one, mul_one]

end NormalizationMonoid

end IsDomain

section DivisionRing

variable [DivisionRing R] {p q : R[X]}

/--
theorem `degree_pos_of_ne_zero_of_nonunit` / 定理 `degree_pos_of_ne_zero_of_nonunit`

English:
theorem degree_pos_of_ne_zero_of_nonunit
  given: (hp0 : p != 0) (hp : ¬IsUnit p)
  statement: 0 < degree p
  proof: lt_of_not_ge fun h => by
    rw [eq_C_of_degree_le_zero h] at hp0 hp
    exact hp (IsUnit.map C (IsUnit.mk0 (coeff p 0) (mt C_inj.2 (by simpa using hp0))))

中文:
定理 degree_pos_of_ne_zero_of_nonunit
  条件: (hp0 : p != 0) (hp : ¬IsUnit p)
  结论: 0 < degree p
  证明: lt_of_not_ge fun h => by
    rw [eq_C_of_degree_le_zero h] at hp0 hp
    exact hp (IsUnit.map C (IsUnit.mk0 (coeff p 0) (mt C_inj.2 (by simpa using hp0))))

Depends on / 依赖: C_inj, IsUnit, IsUnit.map, IsUnit.mk0, eq_C_of_degree_le_zero, lt_of_not_ge
-/
theorem degree_pos_of_ne_zero_of_nonunit (hp0 : p != 0) (hp : ¬IsUnit p) : 0 < degree p :=
  lt_of_not_ge fun h => by
    rw [eq_C_of_degree_le_zero h] at hp0 hp
    exact hp (IsUnit.map C (IsUnit.mk0 (coeff p 0) (mt C_inj.2 (by simpa using hp0))))

end DivisionRing

section SimpleRing

variable [Ring R] [IsSimpleRing R] [Semiring S] [Nontrivial S] {p q : R[X]}

@[simp]
/--
theorem `map_eq_zero` / 定理 `map_eq_zero`

English:
theorem map_eq_zero
  given: (f : R ->+* S)
  statement: p.map f = 0 ↔ p = 0
  proof: Polynomial.map_eq_zero_iff f.injective

中文:
定理 map_eq_zero
  条件: (f : R ->+* S)
  结论: p.map f = 0 ↔ p = 0
  证明: Polynomial.map_eq_zero_iff f.injective
-/
protected theorem map_eq_zero (f : R ->+* S) : p.map f = 0 ↔ p = 0 :=
  Polynomial.map_eq_zero_iff f.injective

/--
theorem `map_ne_zero` / 定理 `map_ne_zero`

English:
theorem map_ne_zero
  given: {f : R ->+* S} (hp : p != 0)
  statement: p.map f != 0
  proof: mt (Polynomial.map_eq_zero f).1 hp

@[simp]

中文:
定理 map_ne_zero
  条件: {f : R ->+* S} (hp : p != 0)
  结论: p.map f != 0
  证明: mt (Polynomial.map_eq_zero f).1 hp

@[simp]

Depends on / 依赖: Polynomial, Polynomial.map_eq_zero, map_eq_zero
-/
theorem map_ne_zero {f : R ->+* S} (hp : p != 0) : p.map f != 0 :=
  mt (Polynomial.map_eq_zero f).1 hp

@[simp]
/--
theorem `degree_map` / 定理 `degree_map`

English:
theorem degree_map
  given: (p : R[X]) (f : R ->+* S)
  statement: (p.map f).degree = p.degree
  proof: degree_map_eq_of_injective f.injective _

@[simp]

中文:
定理 degree_map
  条件: (p : R[X]) (f : R ->+* S)
  结论: (p.map f).degree = p.degree
  证明: degree_map_eq_of_injective f.injective _

@[simp]

Depends on / 依赖: degree_map_eq_of_injective, f.injective, injective
-/
theorem degree_map (p : R[X]) (f : R ->+* S) : (p.map f).degree = p.degree :=
  degree_map_eq_of_injective f.injective _

@[simp]
/--
theorem `natDegree_map` / 定理 `natDegree_map`

English:
theorem natDegree_map
  given: (f : R ->+* S)
  statement: (p.map f).natDegree = p.natDegree
  proof: natDegree_map_eq_of_injective f.injective _

@[simp]

中文:
定理 natDegree_map
  条件: (f : R ->+* S)
  结论: (p.map f).natDegree = p.natDegree
  证明: natDegree_map_eq_of_injective f.injective _

@[simp]

Depends on / 依赖: f.injective, injective, natDegree_map_eq_of_injective
-/
theorem natDegree_map (f : R ->+* S) : (p.map f).natDegree = p.natDegree :=
  natDegree_map_eq_of_injective f.injective _

@[simp]
/--
theorem `leadingCoeff_map` / 定理 `leadingCoeff_map`

English:
theorem leadingCoeff_map
  given: (f : R ->+* S)
  statement: (p.map f).leadingCoeff = f p.leadingCoeff
  proof: leadingCoeff_map_of_injective f.injective _

中文:
定理 leadingCoeff_map
  条件: (f : R ->+* S)
  结论: (p.map f).leadingCoeff = f p.leadingCoeff
  证明: leadingCoeff_map_of_injective f.injective _

Depends on / 依赖: f.injective, injective, leadingCoeff_map_of_injective
-/
theorem leadingCoeff_map (f : R ->+* S) : (p.map f).leadingCoeff = f p.leadingCoeff :=
  leadingCoeff_map_of_injective f.injective _

/--
theorem `nextCoeff_map_eq` / 定理 `nextCoeff_map_eq`

English:
theorem nextCoeff_map_eq
  given: (p : R[X]) (f : R ->+* S)
  statement: (p.map f).nextCoeff = f p.nextCoeff
  proof: nextCoeff_map f.injective _

中文:
定理 nextCoeff_map_eq
  条件: (p : R[X]) (f : R ->+* S)
  结论: (p.map f).nextCoeff = f p.nextCoeff
  证明: nextCoeff_map f.injective _

Depends on / 依赖: f.injective, injective, nextCoeff_map
-/
theorem nextCoeff_map_eq (p : R[X]) (f : R ->+* S) : (p.map f).nextCoeff = f p.nextCoeff :=
  nextCoeff_map f.injective _

/--
theorem `monic_map_iff` / 定理 `monic_map_iff`

English:
theorem monic_map_iff
  given: {f : R ->+* S} {p : R[X]}
  statement: (p.map f).Monic ↔ p.Monic
  proof: .symm Function.Injective.monic_map_iff f.injective

中文:
定理 monic_map_iff
  条件: {f : R ->+* S} {p : R[X]}
  结论: (p.map f).Monic ↔ p.Monic
  证明: .symm Function.Injective.monic_map_iff f.injective
-/
@[simp] theorem monic_map_iff {f : R ->+* S} {p : R[X]} : (p.map f).Monic ↔ p.Monic :=
.symm Function.Injective.monic_map_iff f.injective

end SimpleRing

section Field

variable [Field R] {p q : R[X]}

/--
theorem `isUnit_iff_degree_eq_zero` / 定理 `isUnit_iff_degree_eq_zero`

English:
theorem isUnit_iff_degree_eq_zero
  statement: IsUnit p ↔ degree p = 0
  proof: ⟨degree_eq_zero_of_isUnit, fun h =>
    have : degree p <= 0 := by simp [*]
    have hc : coeff p 0 != 0 := fun hc => by
      rw [eq_C_of_degree_le_zero this]; rw [hc] at h; simp only [map_zero] at h; contradiction
    isUnit_iff_dvd_one.2
      ⟨C (coeff p 0)⁻¹, by
        conv in p => rw [eq_C_of

中文:
定理 isUnit_iff_degree_eq_zero
  结论: IsUnit p ↔ degree p = 0
  证明: ⟨degree_eq_zero_of_isUnit, fun h =>
    have : degree p <= 0 := by simp [*]
    have hc : coeff p 0 != 0 := fun hc => by
      rw [eq_C_of_degree_le_zero this]; rw [hc] at h; simp only [map_zero] at h; contradiction
    isUnit_iff_dvd_one.2
      ⟨C (coeff p 0)⁻¹, by
        conv in p => rw [eq_C_of

Depends on / 依赖: C_mul, degree, degree_eq_zero_of_isUnit, eq_C_of_degree_le_zero, isUnit_iff_dvd_one, map_zero
-/
theorem isUnit_iff_degree_eq_zero : IsUnit p ↔ degree p = 0 :=
  ⟨degree_eq_zero_of_isUnit, fun h =>
    have : degree p <= 0 := by simp [*]
    have hc : coeff p 0 != 0 := fun hc => by
      rw [eq_C_of_degree_le_zero this]; rw [hc] at h; simp only [map_zero] at h; contradiction
    isUnit_iff_dvd_one.2
      ⟨C (coeff p 0)⁻¹, by
        conv in p => rw [eq_C_of_degree_le_zero this]
        rw [← C_mul]; rw [mul_inv_cancel₀ hc]; rw [C_1]⟩⟩

/--
Definition of `div` / `div` 的定义

English:
definition div
  signature: (p q : R[X])
  body: C (leadingCoeff q)⁻¹ * (p /ₘ (q * C (leadingCoeff q)⁻¹))

中文:
定义 div
  签名: (p q : R[X])
  定义体: C (leadingCoeff q)⁻¹ * (p /ₘ (q * C (leadingCoeff q)⁻¹))

Depends on / 依赖: leadingCoeff
-/
def div (p q : R[X]) :=
  C (leadingCoeff q)⁻¹ * (p /ₘ (q * C (leadingCoeff q)⁻¹))

/--
Definition of `mod` / `mod` 的定义

English:
definition mod
  signature: (p q : R[X])
  body: p %ₘ (q * C (leadingCoeff q)⁻¹)

中文:
定义 mod
  签名: (p q : R[X])
  定义体: p %ₘ (q * C (leadingCoeff q)⁻¹)

Depends on / 依赖: leadingCoeff
-/
def mod (p q : R[X]) :=
  p %ₘ (q * C (leadingCoeff q)⁻¹)

/--
theorem `quotient_mul_add_remainder_eq_aux` / 定理 `quotient_mul_add_remainder_eq_aux`

English:
theorem quotient_mul_add_remainder_eq_aux
  given: (p q : R[X])
  statement: q * div p q + mod p q = p
  proof: by
  by_cases h : q = 0
  · simp only [h, zero_mul, mod, modByMonic_zero, zero_add]
  · conv =>
      rhs
      rw [← modByMonic_add_div p (q * C q.leadingCoeff⁻¹)]
    rw [div]; rw [mod]; rw [add_comm]; rw [mul_assoc]

中文:
定理 quotient_mul_add_remainder_eq_aux
  条件: (p q : R[X])
  结论: q * div p q + mod p q = p
  证明: by
  by_cases h : q = 0
  · simp only [h, zero_mul, mod, modByMonic_zero, zero_add]
  · conv =>
      rhs
      rw [← modByMonic_add_div p (q * C q.leadingCoeff⁻¹)]
    rw [div]; rw [mod]; rw [add_comm]; rw [mul_assoc]
-/
private theorem quotient_mul_add_remainder_eq_aux (p q : R[X]) : q * div p q + mod p q = p := by
  by_cases h : q = 0
  · simp only [h, zero_mul, mod, modByMonic_zero, zero_add]
  · conv =>
      rhs
      rw [← modByMonic_add_div p (q * C q.leadingCoeff⁻¹)]
    rw [div]; rw [mod]; rw [add_comm]; rw [mul_assoc]

/--
theorem `remainder_lt_aux` / 定理 `remainder_lt_aux`

English:
theorem remainder_lt_aux
  given: (p : R[X]) (hq : q != 0)
  statement: degree (mod p q) < degree q
  proof: by
  rw [← degree_mul_leadingCoeff_inv q hq]
  exact degree_modByMonic_lt p (monic_mul_leadingCoeff_inv hq)

中文:
定理 remainder_lt_aux
  条件: (p : R[X]) (hq : q != 0)
  结论: degree (mod p q) < degree q
  证明: by
  rw [← degree_mul_leadingCoeff_inv q hq]
  exact degree_modByMonic_lt p (monic_mul_leadingCoeff_inv hq)
-/
private theorem remainder_lt_aux (p : R[X]) (hq : q != 0) : degree (mod p q) < degree q := by
  rw [← degree_mul_leadingCoeff_inv q hq]
  exact degree_modByMonic_lt p (monic_mul_leadingCoeff_inv hq)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Div R[X]
  body: ⟨div⟩

中文:
实例 :
  签名: Div R[X]
  定义体: ⟨div⟩
-/
instance : Div R[X] :=
  ⟨div⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Mod R[X]
  body: ⟨mod⟩

中文:
实例 :
  签名: Mod R[X]
  定义体: ⟨mod⟩
-/
instance : Mod R[X] :=
  ⟨mod⟩

/--
theorem `div_def` / 定理 `div_def`

English:
theorem div_def
  statement: p / q = C (leadingCoeff q)⁻¹ * (p /ₘ (q * C (leadingCoeff q)⁻¹))
  proof: rfl

中文:
定理 div_def
  结论: p / q = C (leadingCoeff q)⁻¹ * (p /ₘ (q * C (leadingCoeff q)⁻¹))
  证明: rfl
-/
theorem div_def : p / q = C (leadingCoeff q)⁻¹ * (p /ₘ (q * C (leadingCoeff q)⁻¹)) :=
  rfl

/--
theorem `mod_def` / 定理 `mod_def`

English:
theorem mod_def
  statement: p % q = p %ₘ (q * C (leadingCoeff q)⁻¹)
  proof: rfl

中文:
定理 mod_def
  结论: p % q = p %ₘ (q * C (leadingCoeff q)⁻¹)
  证明: rfl
-/
theorem mod_def : p % q = p %ₘ (q * C (leadingCoeff q)⁻¹) := rfl

/--
theorem `modByMonic_eq_mod` / 定理 `modByMonic_eq_mod`

English:
theorem modByMonic_eq_mod
  given: (p : R[X]) (hq : Monic q)
  statement: p %ₘ q = p % q
  proof: show p %ₘ q = p %ₘ (q * C (leadingCoeff q)⁻¹) by
    simp only [Monic.def.1 hq, inv_one, mul_one, C_1]

中文:
定理 modByMonic_eq_mod
  条件: (p : R[X]) (hq : Monic q)
  结论: p %ₘ q = p % q
  证明: show p %ₘ q = p %ₘ (q * C (leadingCoeff q)⁻¹) by
    simp only [Monic.def.1 hq, inv_one, mul_one, C_1]

Depends on / 依赖: Monic.def, inv_one, leadingCoeff, mul_one
-/
theorem modByMonic_eq_mod (p : R[X]) (hq : Monic q) : p %ₘ q = p % q :=
  show p %ₘ q = p %ₘ (q * C (leadingCoeff q)⁻¹) by
    simp only [Monic.def.1 hq, inv_one, mul_one, C_1]

/--
theorem `divByMonic_eq_div` / 定理 `divByMonic_eq_div`

English:
theorem divByMonic_eq_div
  given: (p : R[X]) (hq : Monic q)
  statement: p /ₘ q = p / q
  proof: show p /ₘ q = C (leadingCoeff q)⁻¹ * (p /ₘ (q * C (leadingCoeff q)⁻¹)) by
    simp only [Monic.def.1 hq, inv_one, C_1, one_mul, mul_one]

中文:
定理 divByMonic_eq_div
  条件: (p : R[X]) (hq : Monic q)
  结论: p /ₘ q = p / q
  证明: show p /ₘ q = C (leadingCoeff q)⁻¹ * (p /ₘ (q * C (leadingCoeff q)⁻¹)) by
    simp only [Monic.def.1 hq, inv_one, C_1, one_mul, mul_one]

Depends on / 依赖: Monic.def, inv_one, leadingCoeff, mul_one, one_mul
-/
theorem divByMonic_eq_div (p : R[X]) (hq : Monic q) : p /ₘ q = p / q :=
  show p /ₘ q = C (leadingCoeff q)⁻¹ * (p /ₘ (q * C (leadingCoeff q)⁻¹)) by
    simp only [Monic.def.1 hq, inv_one, C_1, one_mul, mul_one]

/--
theorem `mod_X_sub_C_eq_C_eval` / 定理 `mod_X_sub_C_eq_C_eval`

English:
theorem mod_X_sub_C_eq_C_eval
  given: (p : R[X]) (a : R)
  statement: p % (X - C a) = C (p.eval a)
  proof: modByMonic_eq_mod p (monic_X_sub_C a) ▸ modByMonic_X_sub_C_eq_C_eval _ _

中文:
定理 mod_X_sub_C_eq_C_eval
  条件: (p : R[X]) (a : R)
  结论: p % (X - C a) = C (p.eval a)
  证明: modByMonic_eq_mod p (monic_X_sub_C a) ▸ modByMonic_X_sub_C_eq_C_eval _ _

Depends on / 依赖: modByMonic_X_sub_C_eq_C_eval, modByMonic_eq_mod, monic_X_sub_C
-/
theorem mod_X_sub_C_eq_C_eval (p : R[X]) (a : R) : p % (X - C a) = C (p.eval a) :=
  modByMonic_eq_mod p (monic_X_sub_C a) ▸ modByMonic_X_sub_C_eq_C_eval _ _

/--
theorem `mul_div_eq_iff_isRoot` / 定理 `mul_div_eq_iff_isRoot`

English:
theorem mul_div_eq_iff_isRoot
  statement: (X - C a) * (p / (X - C a)) = p ↔ IsRoot p a
  proof: divByMonic_eq_div p (monic_X_sub_C a) ▸ mul_divByMonic_eq_iff_isRoot

alias ⟨_, IsRoot.mul_div_eq⟩ := mul_div_eq_iff_isRoot

中文:
定理 mul_div_eq_iff_isRoot
  结论: (X - C a) * (p / (X - C a)) = p ↔ IsRoot p a
  证明: divByMonic_eq_div p (monic_X_sub_C a) ▸ mul_divByMonic_eq_iff_isRoot

alias ⟨_, IsRoot.mul_div_eq⟩ := mul_div_eq_iff_isRoot

Depends on / 依赖: divByMonic_eq_div, monic_X_sub_C, mul_divByMonic_eq_iff_isRoot
-/
theorem mul_div_eq_iff_isRoot : (X - C a) * (p / (X - C a)) = p ↔ IsRoot p a :=
  divByMonic_eq_div p (monic_X_sub_C a) ▸ mul_divByMonic_eq_iff_isRoot

alias ⟨_, IsRoot.mul_div_eq⟩ := mul_div_eq_iff_isRoot

/--
Instance `instEuclideanDomain` / 实例 `instEuclideanDomain`

English:
instance instEuclideanDomain
  signature: : EuclideanDomain R[X]
  body: { Polynomial.commRing,
    Polynomial.nontrivial with
    quotient := (· / ·)
    quotient_zero := by simp [div_def]
    remainder := (· % ·)
    r := _
    r_wellFounded := degree_lt_wf
    quotient_mul_add_remainder_eq := private quotient_mul_add_remainder_eq_aux
    remainder_lt := private fun _ 

中文:
实例 instEuclideanDomain
  签名: : EuclideanDomain R[X]
  定义体: { Polynomial.commRing,
    Polynomial.nontrivial with
    quotient := (· / ·)
    quotient_zero := by simp [div_def]
    remainder := (· % ·)
    r := _
    r_wellFounded := degree_lt_wf
    quotient_mul_add_remainder_eq := private quotient_mul_add_remainder_eq_aux
    remainder_lt := private fun _ 

Depends on / 依赖: Polynomial, Polynomial.commRing, Polynomial.nontrivial, commRing, degree_le_mul_left, degree_lt_wf, div_def, mul_left_not_lt, nontrivial, not_lt_of_ge, private, quotient, quotient_mul_add_remainder_eq, quotient_mul_add_remainder_eq_aux, quotient_zero, r_wellFounded, remainder, remainder_lt, remainder_lt_aux
-/
instance instEuclideanDomain : EuclideanDomain R[X] :=
  { Polynomial.commRing,
    Polynomial.nontrivial with
    quotient := (· / ·)
    quotient_zero := by simp [div_def]
    remainder := (· % ·)
    r := _
    r_wellFounded := degree_lt_wf
    quotient_mul_add_remainder_eq := private quotient_mul_add_remainder_eq_aux
    remainder_lt := private fun _ _ hq => remainder_lt_aux _ hq
    mul_left_not_lt := fun _ _ hq => not_lt_of_ge (degree_le_mul_left _ hq) }

/--
theorem `mod_eq_self_iff` / 定理 `mod_eq_self_iff`

English:
theorem mod_eq_self_iff
  given: (hq0 : q != 0)
  statement: p % q = p ↔ degree p < degree q
  proof: ⟨fun h => h ▸ EuclideanDomain.mod_lt _ hq0, fun h => by
    have : ¬degree (q * C (leadingCoeff q)⁻¹) <= degree p :=
not_le_of_gt by rwa [degree_mul_leadingCoeff_inv q hq0]
    rw [mod_def]; rw [modByMonic]; rw [dif_pos (monic_mul_leadingCoeff_inv hq0)]
    unfold divModByMonicAux
    dsimp
    simp

中文:
定理 mod_eq_self_iff
  条件: (hq0 : q != 0)
  结论: p % q = p ↔ degree p < degree q
  证明: ⟨fun h => h ▸ EuclideanDomain.mod_lt _ hq0, fun h => by
    have : ¬degree (q * C (leadingCoeff q)⁻¹) <= degree p :=
not_le_of_gt by rwa [degree_mul_leadingCoeff_inv q hq0]
    rw [mod_def]; rw [modByMonic]; rw [dif_pos (monic_mul_leadingCoeff_inv hq0)]
    unfold divModByMonicAux
    dsimp
    simp

Depends on / 依赖: EuclideanDomain, EuclideanDomain.mod_lt, degree, degree_mul_leadingCoeff_inv, dif_pos, divModByMonicAux, false_and, if_false, leadingCoeff, modByMonic, mod_def, mod_lt, monic_mul_leadingCoeff_inv, not_le_of_gt
-/
theorem mod_eq_self_iff (hq0 : q != 0) : p % q = p ↔ degree p < degree q :=
  ⟨fun h => h ▸ EuclideanDomain.mod_lt _ hq0, fun h => by
    have : ¬degree (q * C (leadingCoeff q)⁻¹) <= degree p :=
not_le_of_gt by rwa [degree_mul_leadingCoeff_inv q hq0]
    rw [mod_def]; rw [modByMonic]; rw [dif_pos (monic_mul_leadingCoeff_inv hq0)]
    unfold divModByMonicAux
    dsimp
    simp only [this, false_and, if_false]⟩

/--
theorem `div_eq_zero_iff` / 定理 `div_eq_zero_iff`

English:
theorem div_eq_zero_iff
  given: (hq0 : q != 0)
  statement: p / q = 0 ↔ degree p < degree q
  proof: ⟨fun h => by
    have := EuclideanDomain.div_add_mod p q
    rwa [h, mul_zero, zero_add, mod_eq_self_iff hq0] at this,
  fun h => by
    have hlt : degree p < degree (q * C (leadingCoeff q)⁻¹) := by
      rwa [degree_mul_leadingCoeff_inv q hq0]
    have hm : Monic (q * C (leadingCoeff q)⁻¹) := monic

中文:
定理 div_eq_zero_iff
  条件: (hq0 : q != 0)
  结论: p / q = 0 ↔ degree p < degree q
  证明: ⟨fun h => by
    have := EuclideanDomain.div_add_mod p q
    rwa [h, mul_zero, zero_add, mod_eq_self_iff hq0] at this,
  fun h => by
    have hlt : degree p < degree (q * C (leadingCoeff q)⁻¹) := by
      rwa [degree_mul_leadingCoeff_inv q hq0]
    have hm : Monic (q * C (leadingCoeff q)⁻¹) := monic
-/
protected theorem div_eq_zero_iff (hq0 : q != 0) : p / q = 0 ↔ degree p < degree q :=
  ⟨fun h => by
    have := EuclideanDomain.div_add_mod p q
    rwa [h, mul_zero, zero_add, mod_eq_self_iff hq0] at this,
  fun h => by
    have hlt : degree p < degree (q * C (leadingCoeff q)⁻¹) := by
      rwa [degree_mul_leadingCoeff_inv q hq0]
    have hm : Monic (q * C (leadingCoeff q)⁻¹) := monic_mul_leadingCoeff_inv hq0
    rw [div_def]; rw [(divByMonic_eq_zero_iff hm).2 hlt]; rw [mul_zero]⟩

/--
theorem `degree_add_div` / 定理 `degree_add_div`

English:
theorem degree_add_div
  given: (hq0 : q != 0) (hpq : degree q <= degree p)
  proof: by
  have : degree (p % q) < degree (q * (p / q)) :=
    calc
      degree (p % q) < degree q := EuclideanDomain.mod_lt _ hq0
      _ <= _ := degree_le_mul_left _ (mt (Polynomial.div_eq_zero_iff hq0).1 (not_lt_of_ge hpq))
  conv_rhs =>
    rw [← EuclideanDomain.div_add_mod p q]; rw [degree_add_eq_le

中文:
定理 degree_add_div
  条件: (hq0 : q != 0) (hpq : degree q <= degree p)
  证明: by
  have : degree (p % q) < degree (q * (p / q)) :=
    calc
      degree (p % q) < degree q := EuclideanDomain.mod_lt _ hq0
      _ <= _ := degree_le_mul_left _ (mt (Polynomial.div_eq_zero_iff hq0).1 (not_lt_of_ge hpq))
  conv_rhs =>
    rw [← EuclideanDomain.div_add_mod p q]; rw [degree_add_eq_le

Depends on / 依赖: EuclideanDomain, EuclideanDomain.div_add_mod, EuclideanDomain.mod_lt, Polynomial, Polynomial.div_eq_zero_iff, conv_rhs, degree, degree_add_eq_left_of_degree_lt, degree_le_mul_left, degree_mul, div_add_mod, div_eq_zero_iff, mod_lt, not_lt_of_ge
-/
theorem degree_add_div (hq0 : q != 0) (hpq : degree q <= degree p) :
    degree q + degree (p / q) = degree p := by
  have : degree (p % q) < degree (q * (p / q)) :=
    calc
      degree (p % q) < degree q := EuclideanDomain.mod_lt _ hq0
      _ <= _ := degree_le_mul_left _ (mt (Polynomial.div_eq_zero_iff hq0).1 (not_lt_of_ge hpq))
  conv_rhs =>
    rw [← EuclideanDomain.div_add_mod p q]; rw [degree_add_eq_left_of_degree_lt this]; rw [degree_mul]

/--
theorem `degree_div_le` / 定理 `degree_div_le`

English:
theorem degree_div_le
  given: (p q : R[X])
  statement: degree (p / q) <= degree p
  proof: by
  by_cases hq : q = 0
  · simp [hq]
  · rw [div_def, mul_comm, degree_mul_leadingCoeff_inv _ hq]; exact degree_divByMonic_le _ _

中文:
定理 degree_div_le
  条件: (p q : R[X])
  结论: degree (p / q) <= degree p
  证明: by
  by_cases hq : q = 0
  · simp [hq]
  · rw [div_def, mul_comm, degree_mul_leadingCoeff_inv _ hq]; exact degree_divByMonic_le _ _

Depends on / 依赖: degree_divByMonic_le, degree_mul_leadingCoeff_inv, div_def, mul_comm
-/
theorem degree_div_le (p q : R[X]) : degree (p / q) <= degree p := by
  by_cases hq : q = 0
  · simp [hq]
  · rw [div_def, mul_comm, degree_mul_leadingCoeff_inv _ hq]; exact degree_divByMonic_le _ _

/--
theorem `degree_div_lt` / 定理 `degree_div_lt`

English:
theorem degree_div_lt
  given: (hp : p != 0) (hq : 0 < degree q)
  statement: degree (p / q) < degree p
  proof: by
  have hq0 : q != 0 := fun hq0 => by simp [hq0] at hq
  rw [div_def]; rw [mul_comm]; rw [degree_mul_leadingCoeff_inv _ hq0]
  exact degree_divByMonic_lt _ (q * C q.leadingCoeff⁻¹) hp
    (by rw [degree_mul_leadingCoeff_inv _ hq0]; exact hq)

中文:
定理 degree_div_lt
  条件: (hp : p != 0) (hq : 0 < degree q)
  结论: degree (p / q) < degree p
  证明: by
  have hq0 : q != 0 := fun hq0 => by simp [hq0] at hq
  rw [div_def]; rw [mul_comm]; rw [degree_mul_leadingCoeff_inv _ hq0]
  exact degree_divByMonic_lt _ (q * C q.leadingCoeff⁻¹) hp
    (by rw [degree_mul_leadingCoeff_inv _ hq0]; exact hq)

Depends on / 依赖: degree_divByMonic_lt, degree_mul_leadingCoeff_inv, div_def, leadingCoeff, mul_comm, q.leadingCoeff
-/
theorem degree_div_lt (hp : p != 0) (hq : 0 < degree q) : degree (p / q) < degree p := by
  have hq0 : q != 0 := fun hq0 => by simp [hq0] at hq
  rw [div_def]; rw [mul_comm]; rw [degree_mul_leadingCoeff_inv _ hq0]
  exact degree_divByMonic_lt _ (q * C q.leadingCoeff⁻¹) hp
    (by rw [degree_mul_leadingCoeff_inv _ hq0]; exact hq)

/--
theorem `isUnit_map` / 定理 `isUnit_map`

English:
theorem isUnit_map
  given: [Field k] (f : R ->+* k)
  statement: IsUnit (p.map f) ↔ IsUnit p
  proof: by
  simp_rw [isUnit_iff_degree_eq_zero, degree_map]

中文:
定理 isUnit_map
  条件: [Field k] (f : R ->+* k)
  结论: IsUnit (p.map f) ↔ IsUnit p
  证明: by
  simp_rw [isUnit_iff_degree_eq_zero, degree_map]

Depends on / 依赖: degree_map, isUnit_iff_degree_eq_zero, simp_rw
-/
theorem isUnit_map [Field k] (f : R ->+* k) : IsUnit (p.map f) ↔ IsUnit p := by
  simp_rw [isUnit_iff_degree_eq_zero, degree_map]

/--
theorem `map_div` / 定理 `map_div`

English:
theorem map_div
  given: [Field k] (f : R ->+* k)
  statement: (p / q).map f = p.map f / q.map f
  proof: by
  if hq0 : q = 0 then simp [hq0]
  else
    rw [div_def]; rw [div_def]; rw [Polynomial.map_mul]; rw [map_divByMonic f (monic_mul_leadingCoeff_inv hq0)]; rw [Polynomial.map_mul]; rw [map_C]; rw [leadingCoeff_map]; rw [map_inv₀]

中文:
定理 map_div
  条件: [Field k] (f : R ->+* k)
  结论: (p / q).map f = p.map f / q.map f
  证明: by
  if hq0 : q = 0 then simp [hq0]
  else
    rw [div_def]; rw [div_def]; rw [Polynomial.map_mul]; rw [map_divByMonic f (monic_mul_leadingCoeff_inv hq0)]; rw [Polynomial.map_mul]; rw [map_C]; rw [leadingCoeff_map]; rw [map_inv₀]

Depends on / 依赖: Polynomial, Polynomial.map_mul, div_def, leadingCoeff_map, map_C, map_divByMonic, map_mul, monic_mul_leadingCoeff_inv
-/
theorem map_div [Field k] (f : R ->+* k) : (p / q).map f = p.map f / q.map f := by
  if hq0 : q = 0 then simp [hq0]
  else
    rw [div_def]; rw [div_def]; rw [Polynomial.map_mul]; rw [map_divByMonic f (monic_mul_leadingCoeff_inv hq0)]; rw [Polynomial.map_mul]; rw [map_C]; rw [leadingCoeff_map]; rw [map_inv₀]

/--
theorem `map_mod` / 定理 `map_mod`

English:
theorem map_mod
  given: [Field k] (f : R ->+* k)
  statement: (p % q).map f = p.map f % q.map f
  proof: by
  by_cases hq0 : q = 0
  · simp [hq0]
  · rw [mod_def, mod_def, leadingCoeff_map f, ← map_inv₀ f, ← map_C f, ← Polynomial.map_mul f,
      map_modByMonic f (monic_mul_leadingCoeff_inv hq0)]

中文:
定理 map_mod
  条件: [Field k] (f : R ->+* k)
  结论: (p % q).map f = p.map f % q.map f
  证明: by
  by_cases hq0 : q = 0
  · simp [hq0]
  · rw [mod_def, mod_def, leadingCoeff_map f, ← map_inv₀ f, ← map_C f, ← Polynomial.map_mul f,
      map_modByMonic f (monic_mul_leadingCoeff_inv hq0)]

Depends on / 依赖: Polynomial, Polynomial.map_mul, leadingCoeff_map, map_C, map_modByMonic, map_mul, mod_def, monic_mul_leadingCoeff_inv
-/
theorem map_mod [Field k] (f : R ->+* k) : (p % q).map f = p.map f % q.map f := by
  by_cases hq0 : q = 0
  · simp [hq0]
  · rw [mod_def, mod_def, leadingCoeff_map f, ← map_inv₀ f, ← map_C f, ← Polynomial.map_mul f,
      map_modByMonic f (monic_mul_leadingCoeff_inv hq0)]

/--
lemma `natDegree_mod_lt` / 引理 `natDegree_mod_lt`

English:
lemma natDegree_mod_lt
  given: [Field k] (p : k[X]) {q : k[X]} (hq : q.natDegree != 0)
  proof: by
  have hq' : q.leadingCoeff != 0 := by
    rw [leadingCoeff_ne_zero]
    contrapose hq
    simp [hq]
  rw [mod_def]
  refine (natDegree_modByMonic_lt p ?_ ?_).trans_le ?_
  · refine monic_mul_C_of_leadingCoeff_mul_eq_one ?_
    rw [mul_inv_eq_one₀ hq']
  · contrapose hq
    rw [← natDegree_mul_C_

中文:
引理 natDegree_mod_lt
  条件: [Field k] (p : k[X]) {q : k[X]} (hq : q.natDegree != 0)
  证明: by
  have hq' : q.leadingCoeff != 0 := by
    rw [leadingCoeff_ne_zero]
    contrapose hq
    simp [hq]
  rw [mod_def]
  refine (natDegree_modByMonic_lt p ?_ ?_).trans_le ?_
  · refine monic_mul_C_of_leadingCoeff_mul_eq_one ?_
    rw [mul_inv_eq_one₀ hq']
  · contrapose hq
    rw [← natDegree_mul_C_

Depends on / 依赖: contrapose, leadingCoeff, leadingCoeff_ne_zero, mod_def, monic_mul_C_of_leadingCoeff_mul_eq_one, natDegree_modByMonic_lt, natDegree_mul_C_eq_of_mul_eq_one, natDegree_mul_C_le, q.leadingCoeff, trans_le
-/
lemma natDegree_mod_lt [Field k] (p : k[X]) {q : k[X]} (hq : q.natDegree != 0) :
    (p % q).natDegree < q.natDegree := by
  have hq' : q.leadingCoeff != 0 := by
    rw [leadingCoeff_ne_zero]
    contrapose hq
    simp [hq]
  rw [mod_def]
  refine (natDegree_modByMonic_lt p ?_ ?_).trans_le ?_
  · refine monic_mul_C_of_leadingCoeff_mul_eq_one ?_
    rw [mul_inv_eq_one₀ hq']
  · contrapose hq
    rw [← natDegree_mul_C_eq_of_mul_eq_one ((inv_mul_eq_one₀ hq').mpr rfl)]
    simp [hq]
  · exact natDegree_mul_C_le q q.leadingCoeff⁻¹

/--
theorem `degree_mod_lt` / 定理 `degree_mod_lt`

English:
theorem degree_mod_lt
  given: (p : R[X]) {q : R[X]} (hq : q != 0)
  statement: (p % q).degree < q.degree
  proof: by
  rw [Polynomial.mod_def]
  refine (Polynomial.degree_modByMonic_lt p ?_).trans_eq (by simp)
  simp [Polynomial.Monic.def, hq]

中文:
定理 degree_mod_lt
  条件: (p : R[X]) {q : R[X]} (hq : q != 0)
  结论: (p % q).degree < q.degree
  证明: by
  rw [Polynomial.mod_def]
  refine (Polynomial.degree_modByMonic_lt p ?_).trans_eq (by simp)
  simp [Polynomial.Monic.def, hq]

Depends on / 依赖: Polynomial, Polynomial.Monic.def, Polynomial.degree_modByMonic_lt, Polynomial.mod_def, degree_modByMonic_lt, mod_def, trans_eq
-/
theorem degree_mod_lt (p : R[X]) {q : R[X]} (hq : q != 0) : (p % q).degree < q.degree := by
  rw [Polynomial.mod_def]
  refine (Polynomial.degree_modByMonic_lt p ?_).trans_eq (by simp)
  simp [Polynomial.Monic.def, hq]

/--
theorem `add_mod` / 定理 `add_mod`

English:
theorem add_mod
  given: (p₁ p₂ q : R[X])
  statement: (p₁ + p₂) % q = p₁ % q + p₂ % q
  proof: by
  simp [Polynomial.mod_def, Polynomial.add_modByMonic]

中文:
定理 add_mod
  条件: (p₁ p₂ q : R[X])
  结论: (p₁ + p₂) % q = p₁ % q + p₂ % q
  证明: by
  simp [Polynomial.mod_def, Polynomial.add_modByMonic]

Depends on / 依赖: Polynomial, Polynomial.add_modByMonic, Polynomial.mod_def, add_modByMonic, mod_def
-/
theorem add_mod (p₁ p₂ q : R[X]) : (p₁ + p₂) % q = p₁ % q + p₂ % q := by
  simp [Polynomial.mod_def, Polynomial.add_modByMonic]

/--
theorem `sub_mod` / 定理 `sub_mod`

English:
theorem sub_mod
  given: (p₁ p₂ q : R[X])
  statement: (p₁ - p₂) % q = p₁ % q - p₂ % q
  proof: by
  simp [Polynomial.mod_def, Polynomial.sub_modByMonic]

中文:
定理 sub_mod
  条件: (p₁ p₂ q : R[X])
  结论: (p₁ - p₂) % q = p₁ % q - p₂ % q
  证明: by
  simp [Polynomial.mod_def, Polynomial.sub_modByMonic]

Depends on / 依赖: Polynomial, Polynomial.mod_def, Polynomial.sub_modByMonic, mod_def, sub_modByMonic
-/
theorem sub_mod (p₁ p₂ q : R[X]) : (p₁ - p₂) % q = p₁ % q - p₂ % q := by
  simp [Polynomial.mod_def, Polynomial.sub_modByMonic]

/--
theorem `mul_mod` / 定理 `mul_mod`

English:
theorem mul_mod
  given: (p₁ p₂ q : R[X])
  statement: (p₁ * p₂) % q = (p₁ % q) * (p₂ % q) % q
  proof: by
  simp_rw [Polynomial.mod_def]
  apply Polynomial.mul_modByMonic

中文:
定理 mul_mod
  条件: (p₁ p₂ q : R[X])
  结论: (p₁ * p₂) % q = (p₁ % q) * (p₂ % q) % q
  证明: by
  simp_rw [Polynomial.mod_def]
  apply Polynomial.mul_modByMonic

Depends on / 依赖: Polynomial, Polynomial.mod_def, Polynomial.mul_modByMonic, mod_def, mul_modByMonic, simp_rw
-/
theorem mul_mod (p₁ p₂ q : R[X]) : (p₁ * p₂) % q = (p₁ % q) * (p₂ % q) % q := by
  simp_rw [Polynomial.mod_def]
  apply Polynomial.mul_modByMonic

section

open EuclideanDomain

/--
theorem `gcd_map` / 定理 `gcd_map`

English:
theorem gcd_map
  given: [Field k] [DecidableEq R] [DecidableEq k] (f : R ->+* k)
  proof: GCD.induction p q (fun x => by simp_rw [Polynomial.map_zero, EuclideanDomain.gcd_zero_left])
    fun x y _ ih => by rw [gcd_val, ← map_mod, ih, ← gcd_val]

中文:
定理 gcd_map
  条件: [Field k] [DecidableEq R] [DecidableEq k] (f : R ->+* k)
  证明: GCD.induction p q (fun x => by simp_rw [Polynomial.map_zero, EuclideanDomain.gcd_zero_left])
    fun x y _ ih => by rw [gcd_val, ← map_mod, ih, ← gcd_val]

Depends on / 依赖: EuclideanDomain, EuclideanDomain.gcd_zero_left, GCD.induction, Polynomial, Polynomial.map_zero, gcd_val, gcd_zero_left, map_mod, map_zero, simp_rw
-/
theorem gcd_map [Field k] [DecidableEq R] [DecidableEq k] (f : R ->+* k) :
    gcd (p.map f) (q.map f) = (gcd p q).map f :=
  GCD.induction p q (fun x => by simp_rw [Polynomial.map_zero, EuclideanDomain.gcd_zero_left])
    fun x y _ ih => by rw [gcd_val, ← map_mod, ih, ← gcd_val]

end

/--
theorem `eval₂_gcd_eq_zero` / 定理 `eval₂_gcd_eq_zero`

English:
theorem eval₂_gcd_eq_zero
  statement: [CommSemiring k] [DecidableEq R]
  proof: by
  rw [EuclideanDomain.gcd_eq_gcd_ab f g]; rw [Polynomial.eval₂_add]; rw [Polynomial.eval₂_mul]; rw [Polynomial.eval₂_mul]; rw [hf]; rw [hg]; rw [zero_mul]; rw [zero_mul]; rw [zero_add]

中文:
定理 eval₂_gcd_eq_zero
  结论: [CommSemiring k] [DecidableEq R]
  证明: by
  rw [EuclideanDomain.gcd_eq_gcd_ab f g]; rw [Polynomial.eval₂_add]; rw [Polynomial.eval₂_mul]; rw [Polynomial.eval₂_mul]; rw [hf]; rw [hg]; rw [zero_mul]; rw [zero_mul]; rw [zero_add]

Depends on / 依赖: EuclideanDomain, EuclideanDomain.gcd_eq_gcd_ab, Polynomial, Polynomial.eval, gcd_eq_gcd_ab, zero_add, zero_mul
-/
theorem eval₂_gcd_eq_zero [CommSemiring k] [DecidableEq R]
    {ϕ : R ->+* k} {f g : R[X]} {α : k} (hf : f.eval₂ ϕ α = 0)
    (hg : g.eval₂ ϕ α = 0) : (EuclideanDomain.gcd f g).eval₂ ϕ α = 0 := by
  rw [EuclideanDomain.gcd_eq_gcd_ab f g]; rw [Polynomial.eval₂_add]; rw [Polynomial.eval₂_mul]; rw [Polynomial.eval₂_mul]; rw [hf]; rw [hg]; rw [zero_mul]; rw [zero_mul]; rw [zero_add]

/--
theorem `eval_gcd_eq_zero` / 定理 `eval_gcd_eq_zero`

English:
theorem eval_gcd_eq_zero
  statement: [DecidableEq R] {f g : R[X]} {α : R}
  proof: eval₂_gcd_eq_zero hf hg

中文:
定理 eval_gcd_eq_zero
  结论: [DecidableEq R] {f g : R[X]} {α : R}
  证明: eval₂_gcd_eq_zero hf hg
-/
theorem eval_gcd_eq_zero [DecidableEq R] {f g : R[X]} {α : R}
    (hf : f.eval α = 0) (hg : g.eval α = 0) : (EuclideanDomain.gcd f g).eval α = 0 :=
  eval₂_gcd_eq_zero hf hg

/--
theorem `root_left_of_root_gcd` / 定理 `root_left_of_root_gcd`

English:
theorem root_left_of_root_gcd
  statement: [CommSemiring k] [DecidableEq R] {ϕ : R ->+* k} {f g : R[X]} {α : k}
  proof: by
  obtain ⟨p, hp⟩ := EuclideanDomain.gcd_dvd_left f g
  rw [hp]; rw [Polynomial.eval₂_mul]; rw [hα]; rw [zero_mul]

中文:
定理 root_left_of_root_gcd
  结论: [CommSemiring k] [DecidableEq R] {ϕ : R ->+* k} {f g : R[X]} {α : k}
  证明: by
  obtain ⟨p, hp⟩ := EuclideanDomain.gcd_dvd_left f g
  rw [hp]; rw [Polynomial.eval₂_mul]; rw [hα]; rw [zero_mul]

Depends on / 依赖: EuclideanDomain, EuclideanDomain.gcd_dvd_left, Polynomial, Polynomial.eval, gcd_dvd_left, zero_mul
-/
theorem root_left_of_root_gcd [CommSemiring k] [DecidableEq R] {ϕ : R ->+* k} {f g : R[X]} {α : k}
    (hα : (EuclideanDomain.gcd f g).eval₂ ϕ α = 0) : f.eval₂ ϕ α = 0 := by
  obtain ⟨p, hp⟩ := EuclideanDomain.gcd_dvd_left f g
  rw [hp]; rw [Polynomial.eval₂_mul]; rw [hα]; rw [zero_mul]

/--
theorem `root_right_of_root_gcd` / 定理 `root_right_of_root_gcd`

English:
theorem root_right_of_root_gcd
  statement: [CommSemiring k] [DecidableEq R] {ϕ : R ->+* k} {f g : R[X]} {α : k}
  proof: by
  obtain ⟨p, hp⟩ := EuclideanDomain.gcd_dvd_right f g
  rw [hp]; rw [Polynomial.eval₂_mul]; rw [hα]; rw [zero_mul]

中文:
定理 root_right_of_root_gcd
  结论: [CommSemiring k] [DecidableEq R] {ϕ : R ->+* k} {f g : R[X]} {α : k}
  证明: by
  obtain ⟨p, hp⟩ := EuclideanDomain.gcd_dvd_right f g
  rw [hp]; rw [Polynomial.eval₂_mul]; rw [hα]; rw [zero_mul]

Depends on / 依赖: EuclideanDomain, EuclideanDomain.gcd_dvd_right, Polynomial, Polynomial.eval, gcd_dvd_right, zero_mul
-/
theorem root_right_of_root_gcd [CommSemiring k] [DecidableEq R] {ϕ : R ->+* k} {f g : R[X]} {α : k}
    (hα : (EuclideanDomain.gcd f g).eval₂ ϕ α = 0) : g.eval₂ ϕ α = 0 := by
  obtain ⟨p, hp⟩ := EuclideanDomain.gcd_dvd_right f g
  rw [hp]; rw [Polynomial.eval₂_mul]; rw [hα]; rw [zero_mul]

/--
theorem `root_gcd_iff_root_left_right` / 定理 `root_gcd_iff_root_left_right`

English:
theorem root_gcd_iff_root_left_right
  statement: [CommSemiring k] [DecidableEq R]
  proof: ⟨fun h => ⟨root_left_of_root_gcd h, root_right_of_root_gcd h⟩, fun h => eval₂_gcd_eq_zero h.1 h.2⟩

中文:
定理 root_gcd_iff_root_left_right
  结论: [CommSemiring k] [DecidableEq R]
  证明: ⟨fun h => ⟨root_left_of_root_gcd h, root_right_of_root_gcd h⟩, fun h => eval₂_gcd_eq_zero h.1 h.2⟩

Depends on / 依赖: root_left_of_root_gcd, root_right_of_root_gcd
-/
theorem root_gcd_iff_root_left_right [CommSemiring k] [DecidableEq R]
    {ϕ : R ->+* k} {f g : R[X]} {α : k} :
    (EuclideanDomain.gcd f g).eval₂ ϕ α = 0 ↔ f.eval₂ ϕ α = 0 ∧ g.eval₂ ϕ α = 0 :=
  ⟨fun h => ⟨root_left_of_root_gcd h, root_right_of_root_gcd h⟩, fun h => eval₂_gcd_eq_zero h.1 h.2⟩

/--
theorem `isRoot_gcd_iff_isRoot_left_right` / 定理 `isRoot_gcd_iff_isRoot_left_right`

English:
theorem isRoot_gcd_iff_isRoot_left_right
  given: [DecidableEq R] {f g : R[X]} {α : R}
  proof: root_gcd_iff_root_left_right

中文:
定理 isRoot_gcd_iff_isRoot_left_right
  条件: [DecidableEq R] {f g : R[X]} {α : R}
  证明: root_gcd_iff_root_left_right

Depends on / 依赖: root_gcd_iff_root_left_right
-/
theorem isRoot_gcd_iff_isRoot_left_right [DecidableEq R] {f g : R[X]} {α : R} :
    (EuclideanDomain.gcd f g).IsRoot α ↔ f.IsRoot α ∧ g.IsRoot α :=
  root_gcd_iff_root_left_right

/--
theorem `isCoprime_map` / 定理 `isCoprime_map`

English:
theorem isCoprime_map
  given: [Field k] (f : R ->+* k)
  statement: IsCoprime (p.map f) (q.map f) ↔ IsCoprime p q
  proof: by
  classical
  rw [← EuclideanDomain.gcd_isUnit_iff]; rw [← EuclideanDomain.gcd_isUnit_iff]; rw [gcd_map]; rw [isUnit_map]

中文:
定理 isCoprime_map
  条件: [Field k] (f : R ->+* k)
  结论: IsCoprime (p.map f) (q.map f) ↔ IsCoprime p q
  证明: by
  classical
  rw [← EuclideanDomain.gcd_isUnit_iff]; rw [← EuclideanDomain.gcd_isUnit_iff]; rw [gcd_map]; rw [isUnit_map]

Depends on / 依赖: EuclideanDomain, EuclideanDomain.gcd_isUnit_iff, classical, gcd_isUnit_iff, gcd_map, isUnit_map
-/
theorem isCoprime_map [Field k] (f : R ->+* k) : IsCoprime (p.map f) (q.map f) ↔ IsCoprime p q := by
  classical
  rw [← EuclideanDomain.gcd_isUnit_iff]; rw [← EuclideanDomain.gcd_isUnit_iff]; rw [gcd_map]; rw [isUnit_map]

/--
theorem `mem_roots_map` / 定理 `mem_roots_map`

English:
theorem mem_roots_map
  given: [CommRing k] [IsDomain k] {f : R ->+* k} {x : k} (hp : p != 0)
  proof: by
  rw [mem_roots (map_ne_zero hp)]; rw [IsRoot]; rw [Polynomial.eval_map]

中文:
定理 mem_roots_map
  条件: [CommRing k] [IsDomain k] {f : R ->+* k} {x : k} (hp : p != 0)
  证明: by
  rw [mem_roots (map_ne_zero hp)]; rw [IsRoot]; rw [Polynomial.eval_map]

Depends on / 依赖: IsRoot, Polynomial, Polynomial.eval_map, eval_map, map_ne_zero, mem_roots
-/
theorem mem_roots_map [CommRing k] [IsDomain k] {f : R ->+* k} {x : k} (hp : p != 0) :
    x in (p.map f).roots ↔ p.eval₂ f x = 0 := by
  rw [mem_roots (map_ne_zero hp)]; rw [IsRoot]; rw [Polynomial.eval_map]

/--
theorem `rootSet_monomial` / 定理 `rootSet_monomial`

English:
theorem rootSet_monomial
  statement: [CommRing S] [IsDomain S] [Algebra R S] {n : Nat} (hn : n != 0) {a : R}
  proof: by
  classical
  rw [rootSet]; rw [aroots_monomial ha]; rw [Multiset.toFinset_nsmul _ _ hn]; rw [Multiset.toFinset_singleton]; rw [Finset.coe_singleton]

中文:
定理 rootSet_monomial
  结论: [CommRing S] [IsDomain S] [Algebra R S] {n : 自然数} (hn : n != 0) {a : R}
  证明: by
  classical
  rw [rootSet]; rw [aroots_monomial ha]; rw [Multiset.toFinset_nsmul _ _ hn]; rw [Multiset.toFinset_singleton]; rw [Finset.coe_singleton]

Depends on / 依赖: Finset, Finset.coe_singleton, Multiset, Multiset.toFinset_nsmul, Multiset.toFinset_singleton, aroots_monomial, classical, coe_singleton, rootSet, toFinset_nsmul, toFinset_singleton
-/
theorem rootSet_monomial [CommRing S] [IsDomain S] [Algebra R S] {n : Nat} (hn : n != 0) {a : R}
    (ha : a != 0) : (monomial n a).rootSet S = {0} := by
  classical
  rw [rootSet]; rw [aroots_monomial ha]; rw [Multiset.toFinset_nsmul _ _ hn]; rw [Multiset.toFinset_singleton]; rw [Finset.coe_singleton]

/--
theorem `rootSet_C_mul_X_pow` / 定理 `rootSet_C_mul_X_pow`

English:
theorem rootSet_C_mul_X_pow
  statement: [CommRing S] [IsDomain S] [Algebra R S] {n : Nat} (hn : n != 0) {a : R}
  proof: by
  rw [C_mul_X_pow_eq_monomial]; rw [rootSet_monomial hn ha]

中文:
定理 rootSet_C_mul_X_pow
  结论: [CommRing S] [IsDomain S] [Algebra R S] {n : 自然数} (hn : n != 0) {a : R}
  证明: by
  rw [C_mul_X_pow_eq_monomial]; rw [rootSet_monomial hn ha]

Depends on / 依赖: C_mul_X_pow_eq_monomial, rootSet_monomial
-/
theorem rootSet_C_mul_X_pow [CommRing S] [IsDomain S] [Algebra R S] {n : Nat} (hn : n != 0) {a : R}
    (ha : a != 0) : rootSet (C a * X ^ n) S = {0} := by
  rw [C_mul_X_pow_eq_monomial]; rw [rootSet_monomial hn ha]

/--
theorem `rootSet_X_pow` / 定理 `rootSet_X_pow`

English:
theorem rootSet_X_pow
  given: [CommRing S] [IsDomain S] [Algebra R S] {n : Nat} (hn : n != 0)
  proof: by
  rw [← one_mul (X ^ n : R[X]), ← C_1, rootSet_C_mul_X_pow hn]
  exact one_ne_zero

中文:
定理 rootSet_X_pow
  条件: [CommRing S] [IsDomain S] [Algebra R S] {n : 自然数} (hn : n != 0)
  证明: by
  rw [← one_mul (X ^ n : R[X]), ← C_1, rootSet_C_mul_X_pow hn]
  exact one_ne_zero

Depends on / 依赖: one_mul, one_ne_zero, rootSet_C_mul_X_pow
-/
theorem rootSet_X_pow [CommRing S] [IsDomain S] [Algebra R S] {n : Nat} (hn : n != 0) :
    (X ^ n : R[X]).rootSet S = {0} := by
  rw [← one_mul (X ^ n : R[X]), ← C_1, rootSet_C_mul_X_pow hn]
  exact one_ne_zero

/--
theorem `rootSet_prod` / 定理 `rootSet_prod`

English:
theorem rootSet_prod
  statement: [CommRing S] [IsDomain S] [Algebra R S] {ι : Type*} (f : ι -> R[X])
  proof: by
  classical
  simp only [rootSet, aroots, ← Finset.mem_coe]
  rw [Polynomial.map_prod]; rw [roots_prod]; rw [Finset.bind_toFinset]; rw [s.val_toFinset]; rw [Finset.coe_biUnion]
  rwa [← Polynomial.map_prod, Ne, Polynomial.map_eq_zero]

中文:
定理 rootSet_prod
  结论: [CommRing S] [IsDomain S] [Algebra R S] {ι : 类型} (f : ι -> R[X])
  证明: by
  classical
  simp only [rootSet, aroots, ← Finset.mem_coe]
  rw [Polynomial.map_prod]; rw [roots_prod]; rw [Finset.bind_toFinset]; rw [s.val_toFinset]; rw [Finset.coe_biUnion]
  rwa [← Polynomial.map_prod, Ne, Polynomial.map_eq_zero]

Depends on / 依赖: Finset, Finset.bind_toFinset, Finset.coe_biUnion, Finset.mem_coe, Polynomial, Polynomial.map_eq_zero, Polynomial.map_prod, aroots, bind_toFinset, classical, coe_biUnion, map_eq_zero, map_prod, mem_coe, rootSet, roots_prod, s.val_toFinset, val_toFinset
-/
theorem rootSet_prod [CommRing S] [IsDomain S] [Algebra R S] {ι : Type*} (f : ι -> R[X])
    (s : Finset ι) (h : s.prod f != 0) : (s.prod f).rootSet S = ⋃ i in s, (f i).rootSet S := by
  classical
  simp only [rootSet, aroots, ← Finset.mem_coe]
  rw [Polynomial.map_prod]; rw [roots_prod]; rw [Finset.bind_toFinset]; rw [s.val_toFinset]; rw [Finset.coe_biUnion]
  rwa [← Polynomial.map_prod, Ne, Polynomial.map_eq_zero]

/--
theorem `roots_C_mul_X_sub_C` / 定理 `roots_C_mul_X_sub_C`

English:
theorem roots_C_mul_X_sub_C
  given: (b : R) (ha : a != 0)
  statement: (C a * X - C b).roots = {a⁻¹ * b}
  proof: by
  simp [roots_C_mul_X_sub_C_of_IsUnit b ⟨a, a⁻¹, mul_inv_cancel₀ ha, inv_mul_cancel₀ ha⟩]

中文:
定理 roots_C_mul_X_sub_C
  条件: (b : R) (ha : a != 0)
  结论: (C a * X - C b).roots = {a⁻¹ * b}
  证明: by
  simp [roots_C_mul_X_sub_C_of_IsUnit b ⟨a, a⁻¹, mul_inv_cancel₀ ha, inv_mul_cancel₀ ha⟩]

Depends on / 依赖: roots_C_mul_X_sub_C_of_IsUnit
-/
theorem roots_C_mul_X_sub_C (b : R) (ha : a != 0) : (C a * X - C b).roots = {a⁻¹ * b} := by
  simp [roots_C_mul_X_sub_C_of_IsUnit b ⟨a, a⁻¹, mul_inv_cancel₀ ha, inv_mul_cancel₀ ha⟩]

/--
theorem `roots_C_mul_X_add_C` / 定理 `roots_C_mul_X_add_C`

English:
theorem roots_C_mul_X_add_C
  given: (b : R) (ha : a != 0)
  statement: (C a * X + C b).roots = {-(a⁻¹ * b)}
  proof: by
  simp [roots_C_mul_X_add_C_of_IsUnit b ⟨a, a⁻¹, mul_inv_cancel₀ ha, inv_mul_cancel₀ ha⟩]

中文:
定理 roots_C_mul_X_add_C
  条件: (b : R) (ha : a != 0)
  结论: (C a * X + C b).roots = {-(a⁻¹ * b)}
  证明: by
  simp [roots_C_mul_X_add_C_of_IsUnit b ⟨a, a⁻¹, mul_inv_cancel₀ ha, inv_mul_cancel₀ ha⟩]

Depends on / 依赖: roots_C_mul_X_add_C_of_IsUnit
-/
theorem roots_C_mul_X_add_C (b : R) (ha : a != 0) : (C a * X + C b).roots = {-(a⁻¹ * b)} := by
  simp [roots_C_mul_X_add_C_of_IsUnit b ⟨a, a⁻¹, mul_inv_cancel₀ ha, inv_mul_cancel₀ ha⟩]

/--
theorem `roots_degree_eq_one` / 定理 `roots_degree_eq_one`

English:
theorem roots_degree_eq_one
  given: (h : degree p = 1)
  statement: p.roots = {-((p.coeff 1)⁻¹ * p.coeff 0)}
  proof: by
  rw [eq_X_add_C_of_degree_le_one (show degree p <= 1 by rw [h])]
  have : p.coeff 1 != 0 := coeff_ne_zero_of_eq_degree h
  simp [roots_C_mul_X_add_C _ this]

中文:
定理 roots_degree_eq_one
  条件: (h : degree p = 1)
  结论: p.roots = {-((p.coeff 1)⁻¹ * p.coeff 0)}
  证明: by
  rw [eq_X_add_C_of_degree_le_one (show degree p <= 1 by rw [h])]
  have : p.coeff 1 != 0 := coeff_ne_zero_of_eq_degree h
  simp [roots_C_mul_X_add_C _ this]

Depends on / 依赖: coeff_ne_zero_of_eq_degree, degree, eq_X_add_C_of_degree_le_one, p.coeff, roots_C_mul_X_add_C
-/
theorem roots_degree_eq_one (h : degree p = 1) : p.roots = {-((p.coeff 1)⁻¹ * p.coeff 0)} := by
  rw [eq_X_add_C_of_degree_le_one (show degree p <= 1 by rw [h])]
  have : p.coeff 1 != 0 := coeff_ne_zero_of_eq_degree h
  simp [roots_C_mul_X_add_C _ this]

/--
theorem `exists_root_of_degree_eq_one` / 定理 `exists_root_of_degree_eq_one`

English:
theorem exists_root_of_degree_eq_one
  given: (h : degree p = 1)
  statement: exists x, IsRoot p x
  proof: ⟨-((p.coeff 1)⁻¹ * p.coeff 0), by
    rw [← mem_roots (by simp [← zero_le_degree_iff]; rw [h])]
    simp [roots_degree_eq_one h]⟩

中文:
定理 exists_root_of_degree_eq_one
  条件: (h : degree p = 1)
  结论: 存在 x, IsRoot p x
  证明: ⟨-((p.coeff 1)⁻¹ * p.coeff 0), by
    rw [← mem_roots (by simp [← zero_le_degree_iff]; rw [h])]
    simp [roots_degree_eq_one h]⟩

Depends on / 依赖: mem_roots, p.coeff, roots_degree_eq_one, zero_le_degree_iff
-/
theorem exists_root_of_degree_eq_one (h : degree p = 1) : exists x, IsRoot p x :=
  ⟨-((p.coeff 1)⁻¹ * p.coeff 0), by
    rw [← mem_roots (by simp [← zero_le_degree_iff]; rw [h])]
    simp [roots_degree_eq_one h]⟩

/--
theorem `coeff_inv_units` / 定理 `coeff_inv_units`

English:
theorem coeff_inv_units
  given: (u : R[X]ˣ) (n : Nat)
  statement: ((↑u : R[X]).coeff n)⁻¹ = (↑u⁻¹ : R[X]).coeff n
  proof: by
  rw [eq_C_of_degree_eq_zero (degree_coe_units u)]; rw [eq_C_of_degree_eq_zero (degree_coe_units u⁻¹)]; rw [coeff_C]; rw [coeff_C]; rw [inv_eq_one_div]
  split_ifs
  · rw [div_eq_iff_mul_eq (coeff_coe_units_zero_ne_zero u), coeff_zero_eq_eval_zero,
        coeff_zero_eq_eval_zero, ← eval_mul, ← U

中文:
定理 coeff_inv_units
  条件: (u : R[X]ˣ) (n : 自然数)
  结论: ((↑u : R[X]).coeff n)⁻¹ = (↑u⁻¹ : R[X]).coeff n
  证明: by
  rw [eq_C_of_degree_eq_zero (degree_coe_units u)]; rw [eq_C_of_degree_eq_zero (degree_coe_units u⁻¹)]; rw [coeff_C]; rw [coeff_C]; rw [inv_eq_one_div]
  split_ifs
  · rw [div_eq_iff_mul_eq (coeff_coe_units_zero_ne_zero u), coeff_zero_eq_eval_zero,
        coeff_zero_eq_eval_zero, ← eval_mul, ← U

Depends on / 依赖: Units.val_mul, coeff_C, coeff_coe_units_zero_ne_zero, coeff_zero_eq_eval_zero, degree_coe_units, div_eq_iff_mul_eq, eq_C_of_degree_eq_zero, eval_mul, inv_eq_one_div, inv_mul_cancel, split_ifs, val_mul
-/
theorem coeff_inv_units (u : R[X]ˣ) (n : Nat) : ((↑u : R[X]).coeff n)⁻¹ = (↑u⁻¹ : R[X]).coeff n := by
  rw [eq_C_of_degree_eq_zero (degree_coe_units u)]; rw [eq_C_of_degree_eq_zero (degree_coe_units u⁻¹)]; rw [coeff_C]; rw [coeff_C]; rw [inv_eq_one_div]
  split_ifs
  · rw [div_eq_iff_mul_eq (coeff_coe_units_zero_ne_zero u), coeff_zero_eq_eval_zero,
        coeff_zero_eq_eval_zero, ← eval_mul, ← Units.val_mul, inv_mul_cancel]
    simp
  · simp

/--
theorem `monic_normalize` / 定理 `monic_normalize`

English:
theorem monic_normalize
  given: [DecidableEq R] (hp0 : p != 0)
  statement: Monic (normalize p)
  proof: by
  rw [Ne]; rw [← leadingCoeff_eq_zero]; rw [← Ne]; rw [← isUnit_iff_ne_zero] at hp0
  rw [Monic]; rw [leadingCoeff_normalize]; rw [normalize_eq_one]
  apply hp0

中文:
定理 monic_normalize
  条件: [DecidableEq R] (hp0 : p != 0)
  结论: Monic (normalize p)
  证明: by
  rw [Ne]; rw [← leadingCoeff_eq_zero]; rw [← Ne]; rw [← isUnit_iff_ne_zero] at hp0
  rw [Monic]; rw [leadingCoeff_normalize]; rw [normalize_eq_one]
  apply hp0

Depends on / 依赖: isUnit_iff_ne_zero, leadingCoeff_eq_zero, leadingCoeff_normalize, normalize_eq_one
-/
theorem monic_normalize [DecidableEq R] (hp0 : p != 0) : Monic (normalize p) := by
  rw [Ne]; rw [← leadingCoeff_eq_zero]; rw [← Ne]; rw [← isUnit_iff_ne_zero] at hp0
  rw [Monic]; rw [leadingCoeff_normalize]; rw [normalize_eq_one]
  apply hp0

/--
theorem `normalize_eq_self_iff_monic` / 定理 `normalize_eq_self_iff_monic`

English:
theorem normalize_eq_self_iff_monic
  given: [DecidableEq R] {p : R[X]} (hp : p != 0)
  proof: ⟨fun h => h ▸ monic_normalize hp, fun h => Monic.normalize_eq_self h⟩

中文:
定理 normalize_eq_self_iff_monic
  条件: [DecidableEq R] {p : R[X]} (hp : p != 0)
  证明: ⟨fun h => h ▸ monic_normalize hp, fun h => Monic.normalize_eq_self h⟩

Depends on / 依赖: Monic.normalize_eq_self, monic_normalize, normalize_eq_self
-/
theorem normalize_eq_self_iff_monic [DecidableEq R] {p : R[X]} (hp : p != 0) :
    normalize p = p ↔ p.Monic :=
  ⟨fun h => h ▸ monic_normalize hp, fun h => Monic.normalize_eq_self h⟩

/--
theorem `leadingCoeff_div` / 定理 `leadingCoeff_div`

English:
theorem leadingCoeff_div
  given: (hpq : q.degree <= p.degree)
  proof: by
  by_cases hq : q = 0
  · simp [hq]
  rw [div_def]; rw [leadingCoeff_mul]; rw [leadingCoeff_C]; rw [leadingCoeff_divByMonic_of_monic (monic_mul_leadingCoeff_inv hq) _]; rw [mul_comm]; rw [div_eq_mul_inv]
  rwa [degree_mul_leadingCoeff_inv q hq]

中文:
定理 leadingCoeff_div
  条件: (hpq : q.degree <= p.degree)
  证明: by
  by_cases hq : q = 0
  · simp [hq]
  rw [div_def]; rw [leadingCoeff_mul]; rw [leadingCoeff_C]; rw [leadingCoeff_divByMonic_of_monic (monic_mul_leadingCoeff_inv hq) _]; rw [mul_comm]; rw [div_eq_mul_inv]
  rwa [degree_mul_leadingCoeff_inv q hq]

Depends on / 依赖: degree_mul_leadingCoeff_inv, div_def, div_eq_mul_inv, leadingCoeff_C, leadingCoeff_divByMonic_of_monic, leadingCoeff_mul, monic_mul_leadingCoeff_inv, mul_comm
-/
theorem leadingCoeff_div (hpq : q.degree <= p.degree) :
    (p / q).leadingCoeff = p.leadingCoeff / q.leadingCoeff := by
  by_cases hq : q = 0
  · simp [hq]
  rw [div_def]; rw [leadingCoeff_mul]; rw [leadingCoeff_C]; rw [leadingCoeff_divByMonic_of_monic (monic_mul_leadingCoeff_inv hq) _]; rw [mul_comm]; rw [div_eq_mul_inv]
  rwa [degree_mul_leadingCoeff_inv q hq]

/--
theorem `div_C_mul` / 定理 `div_C_mul`

English:
theorem div_C_mul
  statement: p / (C a * q) = C a⁻¹ * (p / q)
  proof: by
  by_cases ha : a = 0
  · simp [ha]
  simp only [div_def, leadingCoeff_mul, mul_inv, leadingCoeff_C, C.map_mul, mul_assoc]
  congr 3
  rw [mul_left_comm q]; rw [← mul_assoc]; rw [← C.map_mul]; rw [mul_inv_cancel₀ ha]; rw [C.map_one]; rw [one_mul]

中文:
定理 div_C_mul
  结论: p / (C a * q) = C a⁻¹ * (p / q)
  证明: by
  by_cases ha : a = 0
  · simp [ha]
  simp only [div_def, leadingCoeff_mul, mul_inv, leadingCoeff_C, C.map_mul, mul_assoc]
  congr 3
  rw [mul_left_comm q]; rw [← mul_assoc]; rw [← C.map_mul]; rw [mul_inv_cancel₀ ha]; rw [C.map_one]; rw [one_mul]

Depends on / 依赖: C.map_mul, C.map_one, div_def, leadingCoeff_C, leadingCoeff_mul, map_mul, map_one, mul_assoc, mul_inv, mul_left_comm, one_mul
-/
theorem div_C_mul : p / (C a * q) = C a⁻¹ * (p / q) := by
  by_cases ha : a = 0
  · simp [ha]
  simp only [div_def, leadingCoeff_mul, mul_inv, leadingCoeff_C, C.map_mul, mul_assoc]
  congr 3
  rw [mul_left_comm q]; rw [← mul_assoc]; rw [← C.map_mul]; rw [mul_inv_cancel₀ ha]; rw [C.map_one]; rw [one_mul]

/--
lemma `div_C` / 引理 `div_C`

English:
lemma div_C
  statement: p / C a = p * C a⁻¹
  proof: by
  simpa [mul_comm] using div_C_mul (q := 1)

中文:
引理 div_C
  结论: p / C a = p * C a⁻¹
  证明: by
  simpa [mul_comm] using div_C_mul (q := 1)

Depends on / 依赖: div_C_mul, mul_comm
-/
lemma div_C : p / C a = p * C a⁻¹ := by
  simpa [mul_comm] using div_C_mul (q := 1)

/--
lemma `C_div` / 引理 `C_div`

English:
lemma C_div
  statement: C (a / b) = C a / C b
  proof: by
  rw [div_C]; rw [← C_mul]; rw [div_eq_mul_inv]

中文:
引理 C_div
  结论: C (a / b) = C a / C b
  证明: by
  rw [div_C]; rw [← C_mul]; rw [div_eq_mul_inv]

Depends on / 依赖: C_mul, div_C, div_eq_mul_inv
-/
lemma C_div : C (a / b) = C a / C b := by
  rw [div_C]; rw [← C_mul]; rw [div_eq_mul_inv]

/--
theorem `C_mul_dvd` / 定理 `C_mul_dvd`

English:
theorem C_mul_dvd
  given: (ha : a != 0)
  statement: C a * p ∣ q ↔ p ∣ q
  proof: ⟨fun h => dvd_trans (dvd_mul_left _ _) h, fun ⟨r, hr⟩ =>
    ⟨C a⁻¹ * r, by
      rw [mul_assoc]; rw [mul_left_comm p]; rw [← mul_assoc]; rw [← C.map_mul]; rw [mul_inv_cancel₀ ha]; rw [C.map_one]; rw [one_mul]; rw [hr]⟩⟩

中文:
定理 C_mul_dvd
  条件: (ha : a != 0)
  结论: C a * p ∣ q ↔ p ∣ q
  证明: ⟨fun h => dvd_trans (dvd_mul_left _ _) h, fun ⟨r, hr⟩ =>
    ⟨C a⁻¹ * r, by
      rw [mul_assoc]; rw [mul_left_comm p]; rw [← mul_assoc]; rw [← C.map_mul]; rw [mul_inv_cancel₀ ha]; rw [C.map_one]; rw [one_mul]; rw [hr]⟩⟩

Depends on / 依赖: C.map_mul, C.map_one, dvd_mul_left, dvd_trans, map_mul, map_one, mul_assoc, mul_left_comm, one_mul
-/
theorem C_mul_dvd (ha : a != 0) : C a * p ∣ q ↔ p ∣ q :=
  ⟨fun h => dvd_trans (dvd_mul_left _ _) h, fun ⟨r, hr⟩ =>
    ⟨C a⁻¹ * r, by
      rw [mul_assoc]; rw [mul_left_comm p]; rw [← mul_assoc]; rw [← C.map_mul]; rw [mul_inv_cancel₀ ha]; rw [C.map_one]; rw [one_mul]; rw [hr]⟩⟩

/--
theorem `dvd_C_mul` / 定理 `dvd_C_mul`

English:
theorem dvd_C_mul
  given: (ha : a != 0)
  statement: p ∣ Polynomial.C a * q ↔ p ∣ q
  proof: ⟨fun ⟨r, hr⟩ =>
    ⟨C a⁻¹ * r, by
      rw [mul_left_comm p]; rw [← hr]; rw [← mul_assoc]; rw [← C.map_mul]; rw [inv_mul_cancel₀ ha]; rw [C.map_one]; rw [one_mul]⟩,
    fun h => dvd_trans h (dvd_mul_left _ _)⟩

中文:
定理 dvd_C_mul
  条件: (ha : a != 0)
  结论: p ∣ Polynomial.C a * q ↔ p ∣ q
  证明: ⟨fun ⟨r, hr⟩ =>
    ⟨C a⁻¹ * r, by
      rw [mul_left_comm p]; rw [← hr]; rw [← mul_assoc]; rw [← C.map_mul]; rw [inv_mul_cancel₀ ha]; rw [C.map_one]; rw [one_mul]⟩,
    fun h => dvd_trans h (dvd_mul_left _ _)⟩

Depends on / 依赖: C.map_mul, C.map_one, dvd_mul_left, dvd_trans, map_mul, map_one, mul_assoc, mul_left_comm, one_mul
-/
theorem dvd_C_mul (ha : a != 0) : p ∣ Polynomial.C a * q ↔ p ∣ q :=
  ⟨fun ⟨r, hr⟩ =>
    ⟨C a⁻¹ * r, by
      rw [mul_left_comm p]; rw [← hr]; rw [← mul_assoc]; rw [← C.map_mul]; rw [inv_mul_cancel₀ ha]; rw [C.map_one]; rw [one_mul]⟩,
    fun h => dvd_trans h (dvd_mul_left _ _)⟩

/--
theorem `coe_normUnit_of_ne_zero` / 定理 `coe_normUnit_of_ne_zero`

English:
theorem coe_normUnit_of_ne_zero
  given: [DecidableEq R] (hp : p != 0)
  proof: by
  have : p.leadingCoeff != 0 := mt leadingCoeff_eq_zero.mp hp
  simp [CommGroupWithZero.coe_normUnit _ this]

中文:
定理 coe_normUnit_of_ne_zero
  条件: [DecidableEq R] (hp : p != 0)
  证明: by
  have : p.leadingCoeff != 0 := mt leadingCoeff_eq_zero.mp hp
  simp [CommGroupWithZero.coe_normUnit _ this]

Depends on / 依赖: CommGroupWithZero, CommGroupWithZero.coe_normUnit, coe_normUnit, leadingCoeff, leadingCoeff_eq_zero, leadingCoeff_eq_zero.mp, p.leadingCoeff
-/
theorem coe_normUnit_of_ne_zero [DecidableEq R] (hp : p != 0) :
    (normUnit p : R[X]) = C p.leadingCoeff⁻¹ := by
  have : p.leadingCoeff != 0 := mt leadingCoeff_eq_zero.mp hp
  simp [CommGroupWithZero.coe_normUnit _ this]

/--
theorem `map_dvd_map'` / 定理 `map_dvd_map'`

English:
theorem map_dvd_map'
  given: [Field k] (f : R ->+* k) {x y : R[X]}
  statement: x.map f ∣ y.map f ↔ x ∣ y
  proof: by
  by_cases H : x = 0
  · rw [H, Polynomial.map_zero, zero_dvd_iff, zero_dvd_iff, Polynomial.map_eq_zero]
  · classical
    rw [← normalize_dvd_iff]; rw [← @normalize_dvd_iff R[X], normalize_apply, normalize_apply,
      coe_normUnit_of_ne_zero H, coe_normUnit_of_ne_zero (mt (Polynomial.map_eq_zer

中文:
定理 map_dvd_map'
  条件: [Field k] (f : R ->+* k) {x y : R[X]}
  结论: x.map f ∣ y.map f ↔ x ∣ y
  证明: by
  by_cases H : x = 0
  · rw [H, Polynomial.map_zero, zero_dvd_iff, zero_dvd_iff, Polynomial.map_eq_zero]
  · classical
    rw [← normalize_dvd_iff]; rw [← @normalize_dvd_iff R[X], normalize_apply, normalize_apply,
      coe_normUnit_of_ne_zero H, coe_normUnit_of_ne_zero (mt (Polynomial.map_eq_zer

Depends on / 依赖: Polynomial, Polynomial.map_eq_zero, Polynomial.map_mul, Polynomial.map_zero, classical, coe_normUnit_of_ne_zero, f.injective, injective, leadingCoeff_map, map_C, map_dvd_map, map_eq_zero, map_mul, map_zero, monic_mul_leadingCoeff_inv, normalize_apply, normalize_dvd_iff, zero_dvd_iff
-/
theorem map_dvd_map' [Field k] (f : R ->+* k) {x y : R[X]} : x.map f ∣ y.map f ↔ x ∣ y := by
  by_cases H : x = 0
  · rw [H, Polynomial.map_zero, zero_dvd_iff, zero_dvd_iff, Polynomial.map_eq_zero]
  · classical
    rw [← normalize_dvd_iff]; rw [← @normalize_dvd_iff R[X], normalize_apply, normalize_apply,
      coe_normUnit_of_ne_zero H, coe_normUnit_of_ne_zero (mt (Polynomial.map_eq_zero f).1 H),
      leadingCoeff_map, ← map_inv₀ f, ← map_C, ← Polynomial.map_mul,
      map_dvd_map _ f.injective (monic_mul_leadingCoeff_inv H)]

@[simp]
/--
theorem `degree_normalize` / 定理 `degree_normalize`

English:
theorem degree_normalize
  given: [DecidableEq R]
  statement: degree (normalize p) = degree p
  proof: by
  simp [normalize_apply]

中文:
定理 degree_normalize
  条件: [DecidableEq R]
  结论: degree (normalize p) = degree p
  证明: by
  simp [normalize_apply]

Depends on / 依赖: normalize_apply
-/
theorem degree_normalize [DecidableEq R] : degree (normalize p) = degree p := by
  simp [normalize_apply]

/--
theorem `prime_of_degree_eq_one` / 定理 `prime_of_degree_eq_one`

English:
theorem prime_of_degree_eq_one
  given: (hp1 : degree p = 1)
  statement: Prime p
  proof: by
  classical
  have : Prime (normalize p) :=
    Monic.prime_of_degree_eq_one (hp1 ▸ degree_normalize)
      (monic_normalize fun hp0 => absurd hp1 (by simp [hp0]))
  exact (normalize_associated _).prime this

中文:
定理 prime_of_degree_eq_one
  条件: (hp1 : degree p = 1)
  结论: Prime p
  证明: by
  classical
  have : Prime (normalize p) :=
    Monic.prime_of_degree_eq_one (hp1 ▸ degree_normalize)
      (monic_normalize fun hp0 => absurd hp1 (by simp [hp0]))
  exact (normalize_associated _).prime this

Depends on / 依赖: Monic.prime_of_degree_eq_one, absurd, classical, degree_normalize, monic_normalize, normalize, normalize_associated, prime_of_degree_eq_one
-/
theorem prime_of_degree_eq_one (hp1 : degree p = 1) : Prime p := by
  classical
  have : Prime (normalize p) :=
    Monic.prime_of_degree_eq_one (hp1 ▸ degree_normalize)
      (monic_normalize fun hp0 => absurd hp1 (by simp [hp0]))
  exact (normalize_associated _).prime this

/--
theorem `irreducible_of_degree_eq_one` / 定理 `irreducible_of_degree_eq_one`

English:
theorem irreducible_of_degree_eq_one
  given: (hp1 : degree p = 1)
  statement: Irreducible p
  proof: (prime_of_degree_eq_one hp1).irreducible

中文:
定理 irreducible_of_degree_eq_one
  条件: (hp1 : degree p = 1)
  结论: Irreducible p
  证明: (prime_of_degree_eq_one hp1).irreducible

Depends on / 依赖: irreducible, prime_of_degree_eq_one
-/
theorem irreducible_of_degree_eq_one (hp1 : degree p = 1) : Irreducible p :=
  (prime_of_degree_eq_one hp1).irreducible

/--
theorem `not_irreducible_C` / 定理 `not_irreducible_C`

English:
theorem not_irreducible_C
  given: (x : R)
  statement: ¬Irreducible (C x)
  proof: by
  by_cases H : x = 0
  · rw [H, C_0]
    exact not_irreducible_zero
· exact fun hx => hx.not_isUnit isUnit_C.2 isUnit_iff_ne_zero.2 H

中文:
定理 not_irreducible_C
  条件: (x : R)
  结论: ¬Irreducible (C x)
  证明: by
  by_cases H : x = 0
  · rw [H, C_0]
    exact not_irreducible_zero
· exact fun hx => hx.not_isUnit isUnit_C.2 isUnit_iff_ne_zero.2 H

Depends on / 依赖: hx.not_isUnit, isUnit_C, isUnit_iff_ne_zero, not_irreducible_zero, not_isUnit
-/
theorem not_irreducible_C (x : R) : ¬Irreducible (C x) := by
  by_cases H : x = 0
  · rw [H, C_0]
    exact not_irreducible_zero
· exact fun hx => hx.not_isUnit isUnit_C.2 isUnit_iff_ne_zero.2 H

/--
theorem `degree_pos_of_irreducible` / 定理 `degree_pos_of_irreducible`

English:
theorem degree_pos_of_irreducible
  given: (hp : Irreducible p)
  statement: 0 < p.degree
  proof: lt_of_not_ge fun hp0 =>
    have := eq_C_of_degree_le_zero hp0
not_irreducible_C (p.coeff 0) this ▸ hp

中文:
定理 degree_pos_of_irreducible
  条件: (hp : Irreducible p)
  结论: 0 < p.degree
  证明: lt_of_not_ge fun hp0 =>
    have := eq_C_of_degree_le_zero hp0
not_irreducible_C (p.coeff 0) this ▸ hp

Depends on / 依赖: eq_C_of_degree_le_zero, lt_of_not_ge, not_irreducible_C, p.coeff
-/
theorem degree_pos_of_irreducible (hp : Irreducible p) : 0 < p.degree :=
  lt_of_not_ge fun hp0 =>
    have := eq_C_of_degree_le_zero hp0
not_irreducible_C (p.coeff 0) this ▸ hp

/--
theorem `X_sub_C_mul_divByMonic_eq_sub_modByMonic` / 定理 `X_sub_C_mul_divByMonic_eq_sub_modByMonic`

English:
theorem X_sub_C_mul_divByMonic_eq_sub_modByMonic
  given: {K : Type*} [Ring K] (f : K[X]) (a : K)
  proof: by
  rw [eq_sub_iff_add_eq]; rw [← eq_sub_iff_add_eq']; rw [modByMonic_eq_sub_mul_div]

中文:
定理 X_sub_C_mul_divByMonic_eq_sub_modByMonic
  条件: {K : 类型} [Ring K] (f : K[X]) (a : K)
  证明: by
  rw [eq_sub_iff_add_eq]; rw [← eq_sub_iff_add_eq']; rw [modByMonic_eq_sub_mul_div]

Depends on / 依赖: eq_sub_iff_add_eq, modByMonic_eq_sub_mul_div
-/
theorem X_sub_C_mul_divByMonic_eq_sub_modByMonic {K : Type*} [Ring K] (f : K[X]) (a : K) :
    (X - C a) * (f /ₘ (X - C a)) = f - f %ₘ (X - C a) := by
  rw [eq_sub_iff_add_eq]; rw [← eq_sub_iff_add_eq']; rw [modByMonic_eq_sub_mul_div]

/--
theorem `divByMonic_add_X_sub_C_mul_derivative_divByMonic_eq_derivative` / 定理 `divByMonic_add_X_sub_C_mul_derivative_divByMonic_eq_derivative`

English:
theorem divByMonic_add_X_sub_C_mul_derivative_divByMonic_eq_derivative
  proof: by
have key := by apply congrArg derivative X_sub_C_mul_divByMonic_eq_sub_modByMonic f a
  simpa only [derivative_mul, derivative_sub, derivative_X, derivative_C, sub_zero, one_mul,
    modByMonic_X_sub_C_eq_C_eval] using key

中文:
定理 divByMonic_add_X_sub_C_mul_derivative_divByMonic_eq_derivative
  证明: by
have key := by apply congrArg derivative X_sub_C_mul_divByMonic_eq_sub_modByMonic f a
  simpa only [derivative_mul, derivative_sub, derivative_X, derivative_C, sub_zero, one_mul,
    modByMonic_X_sub_C_eq_C_eval] using key

Depends on / 依赖: X_sub_C_mul_divByMonic_eq_sub_modByMonic, derivative, derivative_C, derivative_X, derivative_mul, derivative_sub, modByMonic_X_sub_C_eq_C_eval, one_mul, sub_zero
-/
theorem divByMonic_add_X_sub_C_mul_derivative_divByMonic_eq_derivative
    {K : Type*} [CommRing K] (f : K[X]) (a : K) :
    f /ₘ (X - C a) + (X - C a) * derivative (f /ₘ (X - C a)) = derivative f := by
have key := by apply congrArg derivative X_sub_C_mul_divByMonic_eq_sub_modByMonic f a
  simpa only [derivative_mul, derivative_sub, derivative_X, derivative_C, sub_zero, one_mul,
    modByMonic_X_sub_C_eq_C_eval] using key

/--
theorem `X_sub_C_dvd_derivative_of_X_sub_C_dvd_divByMonic` / 定理 `X_sub_C_dvd_derivative_of_X_sub_C_dvd_divByMonic`

English:
theorem X_sub_C_dvd_derivative_of_X_sub_C_dvd_divByMonic
  statement: {K : Type*} [Field K] (f : K[X]) {a : K}
  proof: by
  have key := divByMonic_add_X_sub_C_mul_derivative_divByMonic_eq_derivative f a
  have ⟨u,hu⟩ := hf
  rw [← key]; rw [hu]; rw [← mul_add (X - C a) u _]
  use (u + derivative ((X - C a) * u))

中文:
定理 X_sub_C_dvd_derivative_of_X_sub_C_dvd_divByMonic
  结论: {K : 类型} [Field K] (f : K[X]) {a : K}
  证明: by
  have key := divByMonic_add_X_sub_C_mul_derivative_divByMonic_eq_derivative f a
  have ⟨u,hu⟩ := hf
  rw [← key]; rw [hu]; rw [← mul_add (X - C a) u _]
  use (u + derivative ((X - C a) * u))

Depends on / 依赖: derivative, divByMonic_add_X_sub_C_mul_derivative_divByMonic_eq_derivative, mul_add
-/
theorem X_sub_C_dvd_derivative_of_X_sub_C_dvd_divByMonic {K : Type*} [Field K] (f : K[X]) {a : K}
    (hf : (X - C a) ∣ f /ₘ (X - C a)) : X - C a ∣ derivative f := by
  have key := divByMonic_add_X_sub_C_mul_derivative_divByMonic_eq_derivative f a
  have ⟨u,hu⟩ := hf
  rw [← key]; rw [hu]; rw [← mul_add (X - C a) u _]
  use (u + derivative ((X - C a) * u))

/--
theorem `isCoprime_of_is_root_of_eval_derivative_ne_zero` / 定理 `isCoprime_of_is_root_of_eval_derivative_ne_zero`

English:
theorem isCoprime_of_is_root_of_eval_derivative_ne_zero
  statement: {K : Type*} [Field K] (f : K[X]) (a : K)
  proof: by
  refine Or.resolve_left
      (EuclideanDomain.dvd_or_coprime (X - C a) (f /ₘ (X - C a))
        (irreducible_of_degree_eq_one (Polynomial.degree_X_sub_C a))) ?_
  contrapose hf' with h
  have : X - C a ∣ derivative f := X_sub_C_dvd_derivative_of_X_sub_C_dvd_divByMonic f h
  rw [← modByMonic_eq_

中文:
定理 isCoprime_of_is_root_of_eval_derivative_ne_zero
  结论: {K : 类型} [Field K] (f : K[X]) (a : K)
  证明: by
  refine Or.resolve_left
      (EuclideanDomain.dvd_or_coprime (X - C a) (f /ₘ (X - C a))
        (irreducible_of_degree_eq_one (Polynomial.degree_X_sub_C a))) ?_
  contrapose hf' with h
  have : X - C a ∣ derivative f := X_sub_C_dvd_derivative_of_X_sub_C_dvd_divByMonic f h
  rw [← modByMonic_eq_

Depends on / 依赖: C_inj, EuclideanDomain, EuclideanDomain.dvd_or_coprime, Or.resolve_left, Polynomial, Polynomial.degree_X_sub_C, X_sub_C_dvd_derivative_of_X_sub_C_dvd_divByMonic, contrapose, degree_X_sub_C, derivative, dvd_or_coprime, irreducible_of_degree_eq_one, modByMonic_X_sub_C_eq_C_eval, modByMonic_eq_zero_iff_dvd, monic_X_sub_C, resolve_left
-/
theorem isCoprime_of_is_root_of_eval_derivative_ne_zero {K : Type*} [Field K] (f : K[X]) (a : K)
    (hf' : f.derivative.eval a != 0) : IsCoprime (X - C a : K[X]) (f /ₘ (X - C a)) := by
  refine Or.resolve_left
      (EuclideanDomain.dvd_or_coprime (X - C a) (f /ₘ (X - C a))
        (irreducible_of_degree_eq_one (Polynomial.degree_X_sub_C a))) ?_
  contrapose hf' with h
  have : X - C a ∣ derivative f := X_sub_C_dvd_derivative_of_X_sub_C_dvd_divByMonic f h
  rw [← modByMonic_eq_zero_iff_dvd (monic_X_sub_C _)]; rw [modByMonic_X_sub_C_eq_C_eval] at this
  rwa [← C_inj, C_0]

/--
theorem `irreducible_iff_degree_lt` / 定理 `irreducible_iff_degree_lt`

English:
theorem irreducible_iff_degree_lt
  given: (p : R[X]) (hp0 : p != 0) (hpu : ¬ IsUnit p)
  proof: by
  rw [← irreducible_mul_leadingCoeff_inv]; rw [(monic_mul_leadingCoeff_inv hp0).irreducible_iff_degree_lt]
  · simp [hp0, natDegree_mul_leadingCoeff_inv]
  · contrapose hpu
    exact .of_mul_eq_one _ hpu

中文:
定理 irreducible_iff_degree_lt
  条件: (p : R[X]) (hp0 : p != 0) (hpu : ¬ IsUnit p)
  证明: by
  rw [← irreducible_mul_leadingCoeff_inv]; rw [(monic_mul_leadingCoeff_inv hp0).irreducible_iff_degree_lt]
  · simp [hp0, natDegree_mul_leadingCoeff_inv]
  · contrapose hpu
    exact .of_mul_eq_one _ hpu

Depends on / 依赖: contrapose, irreducible_iff_degree_lt, irreducible_mul_leadingCoeff_inv, monic_mul_leadingCoeff_inv, natDegree_mul_leadingCoeff_inv, of_mul_eq_one
-/
theorem irreducible_iff_degree_lt (p : R[X]) (hp0 : p != 0) (hpu : ¬ IsUnit p) :
    Irreducible p ↔ forall q, q.degree <= ↑(natDegree p / 2) -> q ∣ p -> IsUnit q := by
  rw [← irreducible_mul_leadingCoeff_inv]; rw [(monic_mul_leadingCoeff_inv hp0).irreducible_iff_degree_lt]
  · simp [hp0, natDegree_mul_leadingCoeff_inv]
  · contrapose hpu
    exact .of_mul_eq_one _ hpu

/--
theorem `irreducible_iff_lt_natDegree_lt` / 定理 `irreducible_iff_lt_natDegree_lt`

English:
theorem irreducible_iff_lt_natDegree_lt
  given: {p : R[X]} (hp0 : p != 0) (hpu : ¬ IsUnit p)
  proof: by
  have : p * C (leadingCoeff p)⁻¹ != 1 := by
    contrapose hpu
    exact .of_mul_eq_one _ hpu
  rw [← irreducible_mul_leadingCoeff_inv]; rw [(monic_mul_leadingCoeff_inv hp0).irreducible_iff_lt_natDegree_lt this]; rw [natDegree_mul_leadingCoeff_inv _ hp0]
  simp only [IsUnit.dvd_mul_right
    (is

中文:
定理 irreducible_iff_lt_natDegree_lt
  条件: {p : R[X]} (hp0 : p != 0) (hpu : ¬ IsUnit p)
  证明: by
  have : p * C (leadingCoeff p)⁻¹ != 1 := by
    contrapose hpu
    exact .of_mul_eq_one _ hpu
  rw [← irreducible_mul_leadingCoeff_inv]; rw [(monic_mul_leadingCoeff_inv hp0).irreducible_iff_lt_natDegree_lt this]; rw [natDegree_mul_leadingCoeff_inv _ hp0]
  simp only [IsUnit.dvd_mul_right
    (is

Depends on / 依赖: IsUnit, IsUnit.dvd_mul_right, IsUnit.mk0, contrapose, dvd_mul_right, inv_ne_zero, irreducible_iff_lt_natDegree_lt, irreducible_mul_leadingCoeff_inv, isUnit_C, isUnit_C.mpr, leadingCoeff, leadingCoeff_ne_zero, leadingCoeff_ne_zero.mpr, monic_mul_leadingCoeff_inv, natDegree_mul_leadingCoeff_inv, of_mul_eq_one
-/
theorem irreducible_iff_lt_natDegree_lt {p : R[X]} (hp0 : p != 0) (hpu : ¬ IsUnit p) :
    Irreducible p ↔ forall q, Monic q -> natDegree q in Finset.Ioc 0 (natDegree p / 2) -> ¬ q ∣ p := by
  have : p * C (leadingCoeff p)⁻¹ != 1 := by
    contrapose hpu
    exact .of_mul_eq_one _ hpu
  rw [← irreducible_mul_leadingCoeff_inv]; rw [(monic_mul_leadingCoeff_inv hp0).irreducible_iff_lt_natDegree_lt this]; rw [natDegree_mul_leadingCoeff_inv _ hp0]
  simp only [IsUnit.dvd_mul_right
    (isUnit_C.mpr (IsUnit.mk0 (leadingCoeff p)⁻¹ (inv_ne_zero (leadingCoeff_ne_zero.mpr hp0))))]

open UniqueFactorizationMonoid in
/--
theorem `leadingCoeff_mul_prod_normalizedFactors` / 定理 `leadingCoeff_mul_prod_normalizedFactors`

English:
theorem leadingCoeff_mul_prod_normalizedFactors
  given: [DecidableEq R] (a : R[X])
  proof: by
  by_cases ha : a = 0
  · simp [ha]
  rw [prod_normalizedFactors_eq]; rw [normalize_apply]; rw [coe_normUnit]; rw [CommGroupWithZero.coe_normUnit]; rw [mul_comm]; rw [mul_assoc]; rw [← map_mul]; rw [inv_mul_cancel₀] <;>
  simp_all

中文:
定理 leadingCoeff_mul_prod_normalizedFactors
  条件: [DecidableEq R] (a : R[X])
  证明: by
  by_cases ha : a = 0
  · simp [ha]
  rw [prod_normalizedFactors_eq]; rw [normalize_apply]; rw [coe_normUnit]; rw [CommGroupWithZero.coe_normUnit]; rw [mul_comm]; rw [mul_assoc]; rw [← map_mul]; rw [inv_mul_cancel₀] <;>
  simp_all

Depends on / 依赖: CommGroupWithZero, CommGroupWithZero.coe_normUnit, coe_normUnit, map_mul, mul_assoc, mul_comm, normalize_apply, prod_normalizedFactors_eq
-/
theorem leadingCoeff_mul_prod_normalizedFactors [DecidableEq R] (a : R[X]) :
    C a.leadingCoeff * (normalizedFactors a).prod = a := by
  by_cases ha : a = 0
  · simp [ha]
  rw [prod_normalizedFactors_eq]; rw [normalize_apply]; rw [coe_normUnit]; rw [CommGroupWithZero.coe_normUnit]; rw [mul_comm]; rw [mul_assoc]; rw [← map_mul]; rw [inv_mul_cancel₀] <;>
  simp_all

open UniqueFactorizationMonoid in
/--
theorem `mem_normalizedFactors_iff` / 定理 `mem_normalizedFactors_iff`

English:
theorem mem_normalizedFactors_iff
  given: [DecidableEq R] (hq : q != 0)
  proof: by
  by_cases hp : p = 0
  · simpa [hp] using zero_notMem_normalizedFactors _
  · rw [mem_normalizedFactors_iff' hq, normalize_eq_self_iff_monic hp]

中文:
定理 mem_normalizedFactors_iff
  条件: [DecidableEq R] (hq : q != 0)
  证明: by
  by_cases hp : p = 0
  · simpa [hp] using zero_notMem_normalizedFactors _
  · rw [mem_normalizedFactors_iff' hq, normalize_eq_self_iff_monic hp]
-/
protected theorem mem_normalizedFactors_iff [DecidableEq R] (hq : q != 0) :
    p in normalizedFactors q ↔ Irreducible p ∧ p.Monic ∧ p ∣ q := by
  by_cases hp : p = 0
  · simpa [hp] using zero_notMem_normalizedFactors _
  · rw [mem_normalizedFactors_iff' hq, normalize_eq_self_iff_monic hp]

variable (p) in
@[simp]
/--
theorem `map_normalize` / 定理 `map_normalize`

English:
theorem map_normalize
  given: [DecidableEq R] [Field S] [DecidableEq S] (f : R ->+* S)
  proof: by
  by_cases hp : p = 0
  · simp [hp]
  · simp [normalize_apply, Polynomial.map_mul, normUnit, hp]

中文:
定理 map_normalize
  条件: [DecidableEq R] [Field S] [DecidableEq S] (f : R ->+* S)
  证明: by
  by_cases hp : p = 0
  · simp [hp]
  · simp [normalize_apply, Polynomial.map_mul, normUnit, hp]

Depends on / 依赖: Polynomial, Polynomial.map_mul, map_mul, normUnit, normalize_apply
-/
theorem map_normalize [DecidableEq R] [Field S] [DecidableEq S] (f : R ->+* S) :
    map f (normalize p) = normalize (map f p) := by
  by_cases hp : p = 0
  · simp [hp]
  · simp [normalize_apply, Polynomial.map_mul, normUnit, hp]

/--
theorem `monic_mapAlg_iff` / 定理 `monic_mapAlg_iff`

English:
theorem monic_mapAlg_iff
  given: [Semiring S] [Nontrivial S] [Algebra R S] {p : R[X]}
  proof: by
  simp [mapAlg_eq_map, monic_map_iff]

中文:
定理 monic_mapAlg_iff
  条件: [Semiring S] [Nontrivial S] [Algebra R S] {p : R[X]}
  证明: by
  simp [mapAlg_eq_map, monic_map_iff]

Depends on / 依赖: mapAlg_eq_map, monic_map_iff
-/
theorem monic_mapAlg_iff [Semiring S] [Nontrivial S] [Algebra R S] {p : R[X]} :
    (mapAlg R S p).Monic ↔ p.Monic := by
  simp [mapAlg_eq_map, monic_map_iff]

/--
theorem `mod_eq_of_dvd_sub` / 定理 `mod_eq_of_dvd_sub`

English:
theorem mod_eq_of_dvd_sub
  given: {p₁ p₂ q : R[X]} (h : q ∣ p₁ - p₂)
  statement: p₁ % q = p₂ % q
  proof: by
  obtain rfl | hq := eq_or_ne q 0
  · simpa [sub_eq_zero] using h
  simp_rw [Polynomial.mod_def]
  apply Polynomial.modByMonic_eq_of_dvd_sub (by simp [Polynomial.Monic.def, hq])
  rw [mul_comm]
  exact (Polynomial.C_mul_dvd (by simpa using hq)).mpr h

中文:
定理 mod_eq_of_dvd_sub
  条件: {p₁ p₂ q : R[X]} (h : q ∣ p₁ - p₂)
  结论: p₁ % q = p₂ % q
  证明: by
  obtain rfl | hq := eq_or_ne q 0
  · simpa [sub_eq_zero] using h
  simp_rw [Polynomial.mod_def]
  apply Polynomial.modByMonic_eq_of_dvd_sub (by simp [Polynomial.Monic.def, hq])
  rw [mul_comm]
  exact (Polynomial.C_mul_dvd (by simpa using hq)).mpr h

Depends on / 依赖: C_mul_dvd, Polynomial, Polynomial.C_mul_dvd, Polynomial.Monic.def, Polynomial.modByMonic_eq_of_dvd_sub, Polynomial.mod_def, eq_or_ne, modByMonic_eq_of_dvd_sub, mod_def, mul_comm, simp_rw, sub_eq_zero
-/
theorem mod_eq_of_dvd_sub {p₁ p₂ q : R[X]} (h : q ∣ p₁ - p₂) : p₁ % q = p₂ % q := by
  obtain rfl | hq := eq_or_ne q 0
  · simpa [sub_eq_zero] using h
  simp_rw [Polynomial.mod_def]
  apply Polynomial.modByMonic_eq_of_dvd_sub (by simp [Polynomial.Monic.def, hq])
  rw [mul_comm]
  exact (Polynomial.C_mul_dvd (by simpa using hq)).mpr h

end Field

end Polynomial

namespace Irreducible

variable {F : Type*} [DivisionSemiring F] {f : F[X]}

/--
theorem `natDegree_pos` / 定理 `natDegree_pos`

English:
theorem natDegree_pos
  given: (h : Irreducible f)
  statement: 0 < f.natDegree
  proof: Nat.pos_of_ne_zero fun H => by
  obtain ⟨x, hf⟩ := natDegree_eq_zero.1 H
  by_cases hx : x = 0
  · rw [← hf, hx, map_zero] at h; exact not_irreducible_zero h
  exact h.1 (hf ▸ isUnit_C.2 (Ne.isUnit hx))

中文:
定理 natDegree_pos
  条件: (h : Irreducible f)
  结论: 0 < f.natDegree
  证明: Nat.pos_of_ne_zero fun H => by
  obtain ⟨x, hf⟩ := natDegree_eq_zero.1 H
  by_cases hx : x = 0
  · rw [← hf, hx, map_zero] at h; exact not_irreducible_zero h
  exact h.1 (hf ▸ isUnit_C.2 (Ne.isUnit hx))

Depends on / 依赖: Nat.pos_of_ne_zero, Ne.isUnit, isUnit, isUnit_C, map_zero, natDegree_eq_zero, not_irreducible_zero, pos_of_ne_zero
-/
theorem natDegree_pos (h : Irreducible f) : 0 < f.natDegree := Nat.pos_of_ne_zero fun H => by
  obtain ⟨x, hf⟩ := natDegree_eq_zero.1 H
  by_cases hx : x = 0
  · rw [← hf, hx, map_zero] at h; exact not_irreducible_zero h
  exact h.1 (hf ▸ isUnit_C.2 (Ne.isUnit hx))

/--
theorem `degree_pos` / 定理 `degree_pos`

English:
theorem degree_pos
  given: (h : Irreducible f)
  statement: 0 < f.degree
  proof: by
  rw [← natDegree_pos_iff_degree_pos]
  exact h.natDegree_pos

中文:
定理 degree_pos
  条件: (h : Irreducible f)
  结论: 0 < f.degree
  证明: by
  rw [← natDegree_pos_iff_degree_pos]
  exact h.natDegree_pos

Depends on / 依赖: h.natDegree_pos, natDegree_pos, natDegree_pos_iff_degree_pos
-/
theorem degree_pos (h : Irreducible f) : 0 < f.degree := by
  rw [← natDegree_pos_iff_degree_pos]
  exact h.natDegree_pos

end Irreducible
