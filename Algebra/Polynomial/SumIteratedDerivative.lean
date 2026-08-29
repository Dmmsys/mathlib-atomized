/-
Copyright (c) 2022 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.Algebra.Polynomial.Degree.Lemmas
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Algebra.Polynomial.Eval.SMul

/-!
# Sum of iterated derivatives

This file introduces `Polynomial.sumIDeriv`, the sum of the iterated derivatives of a polynomial,
as a linear map. This is used in particular in the proof of the Lindemann-Weierstrass theorem
(see https://github.com/leanprover-community/mathlib4/pull/6718).

## Main results

* `Polynomial.sumIDeriv`: Sum of iterated derivatives of a polynomial, as a linear map
* `Polynomial.sumIDeriv_apply`, `Polynomial.sumIDeriv_apply_of_lt`,
  `Polynomial.sumIDeriv_apply_of_le`: `Polynomial.sumIDeriv` expressed as a sum
* `Polynomial.sumIDeriv_C`, `Polynomial.sumIDeriv_X`: `Polynomial.sumIDeriv` applied to simple
  polynomials
* `Polynomial.sumIDeriv_map`: `Polynomial.sumIDeriv` commutes with `Polynomial.map`
* `Polynomial.sumIDeriv_derivative`: `Polynomial.sumIDeriv` commutes with `Polynomial.derivative`
* `Polynomial.sumIDeriv_eq_self_add`: `sumIDeriv p = p + derivative (sumIDeriv p)`
* `Polynomial.exists_iterate_derivative_eq_factorial_smul`: the `k`-th iterated derivative of a
  polynomial has a common factor `k!`
* `Polynomial.aeval_iterate_derivative_of_lt`, `Polynomial.aeval_iterate_derivative_self`,
  `Polynomial.aeval_iterate_derivative_of_ge`: applying `Polynomial.aeval` to iterated derivatives
* `Polynomial.aeval_sumIDeriv`, `Polynomial.aeval_sumIDeriv_of_pos`: applying `Polynomial.aeval` to
  `Polynomial.sumIDeriv`

-/

@[expose] public section

open Finset
open scoped Nat

namespace Polynomial

variable {R S : Type*}

section Semiring

variable [Semiring R] [Semiring S]

/--
Definition of `sumIDeriv` / `sumIDeriv` 的定义

English:
definition sumIDeriv
  signature: : R[X] ->ₗ[R] R[X]
  body: Finsupp.lsum Nat (fun _ => LinearMap.id) ∘ₗ derivativeFinsupp

中文:
定义 sumIDeriv
  签名: : R[X] ->ₗ[R] R[X]
  定义体: Finsupp.lsum Nat (fun _ => LinearMap.id) ∘ₗ derivativeFinsupp

Depends on / 依赖: Finsupp, Finsupp.lsum, LinearMap, LinearMap.id, derivativeFinsupp
-/
noncomputable def sumIDeriv : R[X] ->ₗ[R] R[X] :=
  Finsupp.lsum Nat (fun _ => LinearMap.id) ∘ₗ derivativeFinsupp

/--
theorem `sumIDeriv_apply` / 定理 `sumIDeriv_apply`

English:
theorem sumIDeriv_apply
  given: (p : R[X])
  proof: by
  dsimp [sumIDeriv]
  exact Finsupp.sum_of_support_subset _ (by simp) _ (by simp)

中文:
定理 sumIDeriv_apply
  条件: (p : R[X])
  证明: by
  dsimp [sumIDeriv]
  exact Finsupp.sum_of_support_subset _ (by simp) _ (by simp)

Depends on / 依赖: Finsupp, Finsupp.sum_of_support_subset, sumIDeriv, sum_of_support_subset
-/
theorem sumIDeriv_apply (p : R[X]) :
    sumIDeriv p = ∑ i in range (p.natDegree + 1), derivative^[i] p := by
  dsimp [sumIDeriv]
  exact Finsupp.sum_of_support_subset _ (by simp) _ (by simp)

/--
theorem `sumIDeriv_apply_of_lt` / 定理 `sumIDeriv_apply_of_lt`

English:
theorem sumIDeriv_apply_of_lt
  given: {p : R[X]} {n : Nat} (hn : p.natDegree < n)
  proof: by
  dsimp [sumIDeriv]
  exact Finsupp.sum_of_support_subset _ (by simp [hn]) _ (by simp)

中文:
定理 sumIDeriv_apply_of_lt
  条件: {p : R[X]} {n : 自然数} (hn : p.natDegree < n)
  证明: by
  dsimp [sumIDeriv]
  exact Finsupp.sum_of_support_subset _ (by simp [hn]) _ (by simp)

Depends on / 依赖: Finsupp, Finsupp.sum_of_support_subset, sumIDeriv, sum_of_support_subset
-/
theorem sumIDeriv_apply_of_lt {p : R[X]} {n : Nat} (hn : p.natDegree < n) :
    sumIDeriv p = ∑ i in range n, derivative^[i] p := by
  dsimp [sumIDeriv]
  exact Finsupp.sum_of_support_subset _ (by simp [hn]) _ (by simp)

/--
theorem `sumIDeriv_apply_of_le` / 定理 `sumIDeriv_apply_of_le`

English:
theorem sumIDeriv_apply_of_le
  given: {p : R[X]} {n : Nat} (hn : p.natDegree <= n)
  proof: by
  dsimp [sumIDeriv]
  exact Finsupp.sum_of_support_subset _ (by simp [hn]) _ (by simp)

@[simp]

中文:
定理 sumIDeriv_apply_of_le
  条件: {p : R[X]} {n : 自然数} (hn : p.natDegree <= n)
  证明: by
  dsimp [sumIDeriv]
  exact Finsupp.sum_of_support_subset _ (by simp [hn]) _ (by simp)

@[simp]

Depends on / 依赖: Finsupp, Finsupp.sum_of_support_subset, sumIDeriv, sum_of_support_subset
-/
theorem sumIDeriv_apply_of_le {p : R[X]} {n : Nat} (hn : p.natDegree <= n) :
    sumIDeriv p = ∑ i in range (n + 1), derivative^[i] p := by
  dsimp [sumIDeriv]
  exact Finsupp.sum_of_support_subset _ (by simp [hn]) _ (by simp)

@[simp]
/--
theorem `sumIDeriv_C` / 定理 `sumIDeriv_C`

English:
theorem sumIDeriv_C
  given: (a : R)
  statement: sumIDeriv (C a) = C a
  proof: by
  rw [sumIDeriv_apply]; rw [natDegree_C]; rw [zero_add]; rw [sum_range_one]; rw [Function.iterate_zero_apply]

@[simp]

中文:
定理 sumIDeriv_C
  条件: (a : R)
  结论: sumIDeriv (C a) = C a
  证明: by
  rw [sumIDeriv_apply]; rw [natDegree_C]; rw [zero_add]; rw [sum_range_one]; rw [Function.iterate_zero_apply]

@[simp]

Depends on / 依赖: Function, Function.iterate_zero_apply, iterate_zero_apply, natDegree_C, sumIDeriv_apply, sum_range_one, zero_add
-/
theorem sumIDeriv_C (a : R) : sumIDeriv (C a) = C a := by
  rw [sumIDeriv_apply]; rw [natDegree_C]; rw [zero_add]; rw [sum_range_one]; rw [Function.iterate_zero_apply]

@[simp]
/--
theorem `sumIDeriv_X` / 定理 `sumIDeriv_X`

English:
theorem sumIDeriv_X
  statement: sumIDeriv X = X + C 1
  proof: by
  rw [sumIDeriv_apply]; rw [natDegree_X]; rw [sum_range_succ]; rw [sum_range_one]; rw [Function.iterate_zero_apply]; rw [Function.iterate_one]; rw [derivative_X]; rw [eq_natCast]; rw [Nat.cast_one]

@[simp]

中文:
定理 sumIDeriv_X
  结论: sumIDeriv X = X + C 1
  证明: by
  rw [sumIDeriv_apply]; rw [natDegree_X]; rw [sum_range_succ]; rw [sum_range_one]; rw [Function.iterate_zero_apply]; rw [Function.iterate_one]; rw [derivative_X]; rw [eq_natCast]; rw [Nat.cast_one]

@[simp]

Depends on / 依赖: Function, Function.iterate_one, Function.iterate_zero_apply, Nat.cast_one, cast_one, derivative_X, eq_natCast, iterate_one, iterate_zero_apply, natDegree_X, sumIDeriv_apply, sum_range_one, sum_range_succ
-/
theorem sumIDeriv_X : sumIDeriv X = X + C 1 := by
  rw [sumIDeriv_apply]; rw [natDegree_X]; rw [sum_range_succ]; rw [sum_range_one]; rw [Function.iterate_zero_apply]; rw [Function.iterate_one]; rw [derivative_X]; rw [eq_natCast]; rw [Nat.cast_one]

@[simp]
/--
theorem `sumIDeriv_map` / 定理 `sumIDeriv_map`

English:
theorem sumIDeriv_map
  given: (p : R[X]) (f : R ->+* S)
  proof: by
  let n := max (p.map f).natDegree p.natDegree
  rw [sumIDeriv_apply_of_le (le_max_left _ _ : _ <= n)]
  rw [sumIDeriv_apply_of_le (le_max_right _ _ : _ <= n)]
  simp_rw [Polynomial.map_sum, iterate_derivative_map p f]

中文:
定理 sumIDeriv_map
  条件: (p : R[X]) (f : R ->+* S)
  证明: by
  let n := max (p.map f).natDegree p.natDegree
  rw [sumIDeriv_apply_of_le (le_max_left _ _ : _ <= n)]
  rw [sumIDeriv_apply_of_le (le_max_right _ _ : _ <= n)]
  simp_rw [Polynomial.map_sum, iterate_derivative_map p f]

Depends on / 依赖: Polynomial, Polynomial.map_sum, iterate_derivative_map, le_max_left, le_max_right, map_sum, natDegree, p.map, p.natDegree, simp_rw, sumIDeriv_apply_of_le
-/
theorem sumIDeriv_map (p : R[X]) (f : R ->+* S) :
    sumIDeriv (p.map f) = (sumIDeriv p).map f := by
  let n := max (p.map f).natDegree p.natDegree
  rw [sumIDeriv_apply_of_le (le_max_left _ _ : _ <= n)]
  rw [sumIDeriv_apply_of_le (le_max_right _ _ : _ <= n)]
  simp_rw [Polynomial.map_sum, iterate_derivative_map p f]

/--
theorem `sumIDeriv_derivative` / 定理 `sumIDeriv_derivative`

English:
theorem sumIDeriv_derivative
  given: (p : R[X])
  statement: sumIDeriv (derivative p) = derivative (sumIDeriv p)
  proof: by
  rw [sumIDeriv_apply_of_le ((natDegree_derivative_le p).trans tsub_le_self)]; rw [sumIDeriv_apply]; rw [derivative_sum]
  simp_rw [← Function.iterate_succ_apply, Function.iterate_succ_apply']

中文:
定理 sumIDeriv_derivative
  条件: (p : R[X])
  结论: sumIDeriv (derivative p) = derivative (sumIDeriv p)
  证明: by
  rw [sumIDeriv_apply_of_le ((natDegree_derivative_le p).trans tsub_le_self)]; rw [sumIDeriv_apply]; rw [derivative_sum]
  simp_rw [← Function.iterate_succ_apply, Function.iterate_succ_apply']

Depends on / 依赖: Function, Function.iterate_succ_apply, derivative_sum, iterate_succ_apply, natDegree_derivative_le, simp_rw, sumIDeriv_apply, sumIDeriv_apply_of_le, tsub_le_self
-/
theorem sumIDeriv_derivative (p : R[X]) : sumIDeriv (derivative p) = derivative (sumIDeriv p) := by
  rw [sumIDeriv_apply_of_le ((natDegree_derivative_le p).trans tsub_le_self)]; rw [sumIDeriv_apply]; rw [derivative_sum]
  simp_rw [← Function.iterate_succ_apply, Function.iterate_succ_apply']

/--
theorem `sumIDeriv_eq_self_add` / 定理 `sumIDeriv_eq_self_add`

English:
theorem sumIDeriv_eq_self_add
  given: (p : R[X])
  statement: sumIDeriv p = p + derivative (sumIDeriv p)
  proof: by
  rw [sumIDeriv_apply]; rw [derivative_sum]; rw [sum_range_succ']; rw [sum_range_succ]; rw [add_comm]; rw [← add_zero (Finset.sum _ _)]
  simp_rw [← Function.iterate_succ_apply' derivative, Nat.succ_eq_add_one,
    Function.iterate_zero_apply, iterate_derivative_eq_zero (Nat.lt_succ_self _)]

中文:
定理 sumIDeriv_eq_self_add
  条件: (p : R[X])
  结论: sumIDeriv p = p + derivative (sumIDeriv p)
  证明: by
  rw [sumIDeriv_apply]; rw [derivative_sum]; rw [sum_range_succ']; rw [sum_range_succ]; rw [add_comm]; rw [← add_zero (Finset.sum _ _)]
  simp_rw [← Function.iterate_succ_apply' derivative, Nat.succ_eq_add_one,
    Function.iterate_zero_apply, iterate_derivative_eq_zero (Nat.lt_succ_self _)]

Depends on / 依赖: Finset, Finset.sum, Function, Function.iterate_succ_apply, Function.iterate_zero_apply, Nat.lt_succ_self, Nat.succ_eq_add_one, add_comm, add_zero, derivative, derivative_sum, iterate_derivative_eq_zero, iterate_succ_apply, iterate_zero_apply, lt_succ_self, simp_rw, succ_eq_add_one, sumIDeriv_apply, sum_range_succ
-/
theorem sumIDeriv_eq_self_add (p : R[X]) : sumIDeriv p = p + derivative (sumIDeriv p) := by
  rw [sumIDeriv_apply]; rw [derivative_sum]; rw [sum_range_succ']; rw [sum_range_succ]; rw [add_comm]; rw [← add_zero (Finset.sum _ _)]
  simp_rw [← Function.iterate_succ_apply' derivative, Nat.succ_eq_add_one,
    Function.iterate_zero_apply, iterate_derivative_eq_zero (Nat.lt_succ_self _)]

/--
theorem `exists_iterate_derivative_eq_factorial_smul` / 定理 `exists_iterate_derivative_eq_factorial_smul`

English:
theorem exists_iterate_derivative_eq_factorial_smul
  given: (p : R[X]) (k : Nat)
  proof: by
  refine ⟨_, (natDegree_sum_le _ _).trans ?_, iterate_derivative_eq_factorial_smul_sum p k⟩
  rw [fold_max_le]
  refine ⟨Nat.zero_le _, fun i hi => ?_⟩
  dsimp only [Function.comp]
exact (natDegree_C_mul_le _ _).trans (natDegree_X_pow_le _).trans
(le_natDegree_of_mem_supp _ hi).trans natDegree_it

中文:
定理 存在_iterate_derivative_eq_factorial_smul
  条件: (p : R[X]) (k : 自然数)
  证明: by
  refine ⟨_, (natDegree_sum_le _ _).trans ?_, iterate_derivative_eq_factorial_smul_sum p k⟩
  rw [fold_max_le]
  refine ⟨Nat.zero_le _, fun i hi => ?_⟩
  dsimp only [Function.comp]
exact (natDegree_C_mul_le _ _).trans (natDegree_X_pow_le _).trans
(le_natDegree_of_mem_supp _ hi).trans natDegree_it

Depends on / 依赖: Function, Function.comp, Nat.zero_le, fold_max_le, iterate_derivative_eq_factorial_smul_sum, le_natDegree_of_mem_supp, natDegree_C_mul_le, natDegree_X_pow_le, natDegree_iterate_derivative, natDegree_sum_le, zero_le
-/
theorem exists_iterate_derivative_eq_factorial_smul (p : R[X]) (k : Nat) :
    exists gp : R[X], gp.natDegree <= p.natDegree - k ∧ derivative^[k] p = k ! • gp := by
  refine ⟨_, (natDegree_sum_le _ _).trans ?_, iterate_derivative_eq_factorial_smul_sum p k⟩
  rw [fold_max_le]
  refine ⟨Nat.zero_le _, fun i hi => ?_⟩
  dsimp only [Function.comp]
exact (natDegree_C_mul_le _ _).trans (natDegree_X_pow_le _).trans
(le_natDegree_of_mem_supp _ hi).trans natDegree_iterate_derivative _ _

end Semiring

section CommSemiring

variable [CommSemiring R] {A : Type*} [CommRing A] [Algebra R A]

/--
theorem `aeval_iterate_derivative_of_lt` / 定理 `aeval_iterate_derivative_of_lt`

English:
theorem aeval_iterate_derivative_of_lt
  statement: (p : R[X]) (q : Nat) (r : A) {p' : A[X]}
  proof: by
  have h (x) : (X - C r) ^ (q - (k - x)) = (X - C r) ^ 1 * (X - C r) ^ (q - (k - x) - 1) := by
    rw [← pow_add]; rw [add_tsub_cancel_of_le]
    rw [Nat.lt_iff_add_one_le] at hk
    exact (le_tsub_of_add_le_left hk).trans (tsub_le_tsub_left (tsub_le_self : _ <= k) _)
  rw [aeval_def]; rw [eval₂_

中文:
定理 aeval_iterate_derivative_of_lt
  结论: (p : R[X]) (q : 自然数) (r : A) {p' : A[X]}
  证明: by
  have h (x) : (X - C r) ^ (q - (k - x)) = (X - C r) ^ 1 * (X - C r) ^ (q - (k - x) - 1) := by
    rw [← pow_add]; rw [add_tsub_cancel_of_le]
    rw [Nat.lt_iff_add_one_le] at hk
    exact (le_tsub_of_add_le_left hk).trans (tsub_le_tsub_left (tsub_le_self : _ <= k) _)
  rw [aeval_def]; rw [eval₂_

Depends on / 依赖: Nat.lt_iff_add_one_le, add_tsub_cancel_of_le, aeval_def, eval_, eval_mul, eval_sub, iterate_derivative_X_sub_pow, iterate_derivative_map, iterate_derivative_mul, le_tsub_of_add_le_left, lt_iff_add_one_le, mul_assoc, mul_smul_comm, mul_sum, pow_add, pow_one, simp_rw, smul_mul_assoc, smul_smul, tsub_le_self
-/
theorem aeval_iterate_derivative_of_lt (p : R[X]) (q : Nat) (r : A) {p' : A[X]}
    (hp : p.map (algebraMap R A) = (X - C r) ^ q * p') {k : Nat} (hk : k < q) :
    aeval r (derivative^[k] p) = 0 := by
  have h (x) : (X - C r) ^ (q - (k - x)) = (X - C r) ^ 1 * (X - C r) ^ (q - (k - x) - 1) := by
    rw [← pow_add]; rw [add_tsub_cancel_of_le]
    rw [Nat.lt_iff_add_one_le] at hk
    exact (le_tsub_of_add_le_left hk).trans (tsub_le_tsub_left (tsub_le_self : _ <= k) _)
  rw [aeval_def]; rw [eval₂_eq_eval_map]; rw [← iterate_derivative_map]
  simp_rw [hp, iterate_derivative_mul, iterate_derivative_X_sub_pow, ← smul_mul_assoc, smul_smul,
    h, ← mul_smul_comm, mul_assoc, ← mul_sum, eval_mul, pow_one, eval_sub, eval_X, eval_C, sub_self,
    zero_mul]

/--
theorem `aeval_iterate_derivative_self` / 定理 `aeval_iterate_derivative_self`

English:
theorem aeval_iterate_derivative_self
  statement: (p : R[X]) (q : Nat) (r : A) {p' : A[X]}
  proof: by
  have h (x) (h : 1 <= x) (h' : x <= q) :
      (X - C r) ^ (q - (q - x)) = (X - C r) ^ 1 * (X - C r) ^ (q - (q - x) - 1) := by
    rw [← pow_add]; rw [add_tsub_cancel_of_le]
    rwa [tsub_tsub_cancel_of_le h']
  rw [aeval_def]; rw [eval₂_eq_eval_map]; rw [← iterate_derivative_map]
  simp_rw [hp,

中文:
定理 aeval_iterate_derivative_self
  结论: (p : R[X]) (q : 自然数) (r : A) {p' : A[X]}
  证明: by
  have h (x) (h : 1 <= x) (h' : x <= q) :
      (X - C r) ^ (q - (q - x)) = (X - C r) ^ 1 * (X - C r) ^ (q - (q - x) - 1) := by
    rw [← pow_add]; rw [add_tsub_cancel_of_le]
    rwa [tsub_tsub_cancel_of_le h']
  rw [aeval_def]; rw [eval₂_eq_eval_map]; rw [← iterate_derivative_map]
  simp_rw [hp,

Depends on / 依赖: Nat.choose_zero_right, Nat.descFactorial_self, add_tsub_cancel_of_le, aeval_def, choose_zero_right, descFactorial_self, iterate_derivative_X_sub_pow, iterate_derivative_map, iterate_derivative_mul, one_mul, pow_add, pow_zer, simp_rw, smul_mul_assoc, smul_smul, sum_range_succ, tsub_self, tsub_tsub_cancel_of_le, tsub_zero
-/
theorem aeval_iterate_derivative_self (p : R[X]) (q : Nat) (r : A) {p' : A[X]}
    (hp : p.map (algebraMap R A) = (X - C r) ^ q * p') :
    aeval r (derivative^[q] p) = q ! • p'.eval r := by
  have h (x) (h : 1 <= x) (h' : x <= q) :
      (X - C r) ^ (q - (q - x)) = (X - C r) ^ 1 * (X - C r) ^ (q - (q - x) - 1) := by
    rw [← pow_add]; rw [add_tsub_cancel_of_le]
    rwa [tsub_tsub_cancel_of_le h']
  rw [aeval_def]; rw [eval₂_eq_eval_map]; rw [← iterate_derivative_map]
  simp_rw [hp, iterate_derivative_mul, iterate_derivative_X_sub_pow, ← smul_mul_assoc, smul_smul]
  rw [sum_range_succ']; rw [Nat.choose_zero_right]; rw [one_mul]; rw [tsub_zero]; rw [Nat.descFactorial_self]; rw [tsub_self]; rw [pow_zero]; rw [smul_mul_assoc]; rw [one_mul]; rw [Function.iterate_zero_apply]; rw [eval_add]; rw [eval_smul]
  convert! zero_add _
  rw [eval_finsetSum]
  apply sum_eq_zero
  intro x hx
  rw [h (x + 1) le_add_self (Nat.add_one_le_iff.mpr (mem_range.mp hx))]; rw [pow_one]; rw [eval_mul]; rw [eval_smul]; rw [eval_mul]; rw [eval_sub]; rw [eval_X]; rw [eval_C]; rw [sub_self]; rw [zero_mul]; rw [smul_zero]; rw [zero_mul]

variable (A)

/--
theorem `aeval_iterate_derivative_of_ge` / 定理 `aeval_iterate_derivative_of_ge`

English:
theorem aeval_iterate_derivative_of_ge
  given: (p : R[X]) (q : Nat) {k : Nat} (hk : q <= k)
  proof: by
  obtain ⟨p', p'_le, hp'⟩ := exists_iterate_derivative_eq_factorial_smul p k
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hk
  refine ⟨((q + k).descFactorial k : R[X]) * p', (natDegree_C_mul_le _ _).trans p'_le, fun r => ?_⟩
  simp_rw [hp', nsmul_eq_mul, map_mul, map_natCast, ← mul_assoc, ← Nat.c

中文:
定理 aeval_iterate_derivative_of_ge
  条件: (p : R[X]) (q : 自然数) {k : 自然数} (hk : q <= k)
  证明: by
  obtain ⟨p', p'_le, hp'⟩ := exists_iterate_derivative_eq_factorial_smul p k
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hk
  refine ⟨((q + k).descFactorial k : R[X]) * p', (natDegree_C_mul_le _ _).trans p'_le, fun r => ?_⟩
  simp_rw [hp', nsmul_eq_mul, map_mul, map_natCast, ← mul_assoc, ← Nat.c

Depends on / 依赖: Nat.add_descFactorial_eq_ascFactorial, Nat.cast_mul, Nat.exists_eq_add_of_le, Nat.factorial_mul_ascFactorial, add_descFactorial_eq_ascFactorial, cast_mul, descFactorial, exists_eq_add_of_le, exists_iterate_derivative_eq_factorial_smul, factorial_mul_ascFactorial, map_mul, map_natCast, mul_assoc, natDegree_C_mul_le, nsmul_eq_mul, simp_rw
-/
theorem aeval_iterate_derivative_of_ge (p : R[X]) (q : Nat) {k : Nat} (hk : q <= k) :
    exists gp : R[X], gp.natDegree <= p.natDegree - k ∧
      forall r : A, aeval r (derivative^[k] p) = q ! • aeval r gp := by
  obtain ⟨p', p'_le, hp'⟩ := exists_iterate_derivative_eq_factorial_smul p k
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hk
  refine ⟨((q + k).descFactorial k : R[X]) * p', (natDegree_C_mul_le _ _).trans p'_le, fun r => ?_⟩
  simp_rw [hp', nsmul_eq_mul, map_mul, map_natCast, ← mul_assoc, ← Nat.cast_mul,
    Nat.add_descFactorial_eq_ascFactorial, Nat.factorial_mul_ascFactorial]

/--
theorem `aeval_sumIDeriv_eq_eval` / 定理 `aeval_sumIDeriv_eq_eval`

English:
theorem aeval_sumIDeriv_eq_eval
  given: (p : R[X]) (r : A)
  proof: by
  rw [aeval_def]; rw [eval]; rw [sumIDeriv_map]; rw [eval₂_map]; rw [RingHom.id_comp]

中文:
定理 aeval_sumIDeriv_eq_eval
  条件: (p : R[X]) (r : A)
  证明: by
  rw [aeval_def]; rw [eval]; rw [sumIDeriv_map]; rw [eval₂_map]; rw [RingHom.id_comp]

Depends on / 依赖: RingHom, RingHom.id_comp, aeval_def, id_comp, sumIDeriv_map
-/
theorem aeval_sumIDeriv_eq_eval (p : R[X]) (r : A) :
    aeval r (sumIDeriv p) = eval r (sumIDeriv (map (algebraMap R A) p)) := by
  rw [aeval_def]; rw [eval]; rw [sumIDeriv_map]; rw [eval₂_map]; rw [RingHom.id_comp]

/--
theorem `aeval_sumIDeriv` / 定理 `aeval_sumIDeriv`

English:
theorem aeval_sumIDeriv
  given: (p : R[X]) (q : Nat)
  proof: by
  have h (k) :
      exists gp : R[X], gp.natDegree <= p.natDegree - q ∧
        forall (r : A), (X - C r) ^ q ∣ p.map (algebraMap R A) ->
          aeval r (derivative^[k] p) = q ! • aeval r gp := by
    cases lt_or_ge k q with
    | inl hk =>
      use 0
      rw [natDegree_zero]
      use Nat.

中文:
定理 aeval_sumIDeriv
  条件: (p : R[X]) (q : 自然数)
  证明: by
  have h (k) :
      exists gp : R[X], gp.natDegree <= p.natDegree - q ∧
        forall (r : A), (X - C r) ^ q ∣ p.map (algebraMap R A) ->
          aeval r (derivative^[k] p) = q ! • aeval r gp := by
    cases lt_or_ge k q with
    | inl hk =>
      use 0
      rw [natDegree_zero]
      use Nat.

Depends on / 依赖: Nat.zero_le, aeval_iterate_derivative_of_ge, aeval_iterate_derivative_of_lt, algebraMap, derivative, gp.natDegree, gp_le, gp_le.trans, lt_or_ge, map_zero, natDegree, natDegree_zero, p.map, p.natDegree, smul_zero, tsub_le_tsub_left, zero_le
-/
theorem aeval_sumIDeriv (p : R[X]) (q : Nat) :
    exists gp : R[X], gp.natDegree <= p.natDegree - q ∧
      forall (r : A), (X - C r) ^ q ∣ p.map (algebraMap R A) ->
        aeval r (sumIDeriv p) = q ! • aeval r gp := by
  have h (k) :
      exists gp : R[X], gp.natDegree <= p.natDegree - q ∧
        forall (r : A), (X - C r) ^ q ∣ p.map (algebraMap R A) ->
          aeval r (derivative^[k] p) = q ! • aeval r gp := by
    cases lt_or_ge k q with
    | inl hk =>
      use 0
      rw [natDegree_zero]
      use Nat.zero_le _
      intro r ⟨p', hp⟩
      rw [map_zero]; rw [smul_zero]; rw [aeval_iterate_derivative_of_lt p q r hp hk]
    | inr hk =>
      obtain ⟨gp, gp_le, h⟩ := aeval_iterate_derivative_of_ge A p q hk
      exact ⟨gp, gp_le.trans (tsub_le_tsub_left hk _), fun r _ => h r⟩
  choose c h using h
  choose c_le hc using h
  refine ⟨(range (p.natDegree + 1)).sum c, ?_, ?_⟩
  · refine (natDegree_sum_le _ _).trans ?_
    rw [fold_max_le]
    exact ⟨Nat.zero_le _, fun i _ => c_le i⟩
  intro r ⟨p', hp⟩
  rw [sumIDeriv_apply]; rw [map_sum]; simp_rw [hc _ r ⟨_, hp⟩, map_sum, smul_sum]

/--
theorem `aeval_sumIDeriv_of_pos` / 定理 `aeval_sumIDeriv_of_pos`

English:
theorem aeval_sumIDeriv_of_pos
  statement: [Nontrivial A] [NoZeroDivisors A] (p : R[X]) {q : Nat} (hq : 0 < q)
  proof: by
  rcases eq_or_ne p 0 with (rfl | p0)
  · use 0
    rw [natDegree_zero]
    use Nat.zero_le _
    intro r p' hp
    rw [map_zero]; rw [map_zero]; rw [smul_zero]; rw [add_zero]
    rw [Polynomial.map_zero] at hp
    replace hp := (mul_eq_zero.mp hp.symm).resolve_left ?_
    · rw [hp, eval_zero, sm

中文:
定理 aeval_sumIDeriv_of_pos
  结论: [非平凡 A] [无零因子 A] (p : R[X]) {q : 自然数} (hq : 0 < q)
  证明: by
  rcases eq_or_ne p 0 with (rfl | p0)
  · use 0
    rw [natDegree_zero]
    use Nat.zero_le _
    intro r p' hp
    rw [map_zero]; rw [map_zero]; rw [smul_zero]; rw [add_zero]
    rw [Polynomial.map_zero] at hp
    replace hp := (mul_eq_zero.mp hp.symm).resolve_left ?_
    · rw [hp, eval_zero, sm

Depends on / 依赖: Nat.zero_le, Polynomial, Polynomial.map_zero, X_sub_C_ne_zero, add_zero, aeval_iterate_derivative_of_ge, c_le, eq_or_ne, eq_zero_of_pow_eq_zero, eval_zero, hp.symm, map_zero, mul_eq_zero, mul_eq_zero.mp, natDegree, natDegree_zero, p.natDegree, replace, resolve_left, smul_zero
-/
theorem aeval_sumIDeriv_of_pos [Nontrivial A] [NoZeroDivisors A] (p : R[X]) {q : Nat} (hq : 0 < q)
    (inj_amap : Function.Injective (algebraMap R A)) :
    exists gp : R[X], gp.natDegree <= p.natDegree - q ∧
      forall (r : A) {p' : A[X]},
        p.map (algebraMap R A) = (X - C r) ^ (q - 1) * p' ->
        aeval r (sumIDeriv p) = (q - 1)! • p'.eval r + q ! • aeval r gp := by
  rcases eq_or_ne p 0 with (rfl | p0)
  · use 0
    rw [natDegree_zero]
    use Nat.zero_le _
    intro r p' hp
    rw [map_zero]; rw [map_zero]; rw [smul_zero]; rw [add_zero]
    rw [Polynomial.map_zero] at hp
    replace hp := (mul_eq_zero.mp hp.symm).resolve_left ?_
    · rw [hp, eval_zero, smul_zero]
    exact fun h => X_sub_C_ne_zero r (eq_zero_of_pow_eq_zero h)
  let c k := if hk : q <= k then (aeval_iterate_derivative_of_ge A p q hk).choose else 0
  have c_le (k) : (c k).natDegree <= p.natDegree - k := by
    dsimp only [c]
    split_ifs with h
    · exact (aeval_iterate_derivative_of_ge A p q h).choose_spec.1
    · rw [natDegree_zero]; exact Nat.zero_le _
  have hc (k) (hk : q <= k) : forall (r : A), aeval r (derivative^[k] p) = q ! • aeval r (c k) := by
    simp_rw [c, dif_pos hk]
    exact (aeval_iterate_derivative_of_ge A p q hk).choose_spec.2
  refine ⟨∑ x in Ico q (p.natDegree + 1), c x, ?_, ?_⟩
  · refine (natDegree_sum_le _ _).trans ?_
    rw [fold_max_le]
    exact ⟨Nat.zero_le _, fun i hi => (c_le i).trans (tsub_le_tsub_left (mem_Ico.mp hi).1 _)⟩
  intro r p' hp
  have : range (p.natDegree + 1) = range q union Ico q (p.natDegree + 1) := by
    rw [range_eq_Ico]; rw [range_eq_Ico]; rw [Ico_union_Ico_eq_Ico hq.le]
    rw [← tsub_le_iff_right]
    calc
      q - 1 <= q - 1 + p'.natDegree := le_self_add
      _ = (p.map <| algebraMap R A).natDegree := by
        rw [hp]; rw [natDegree_mul]; rw [natDegree_pow]; rw [natDegree_X_sub_C]; rw [mul_one]; rw [← Nat.sub_add_comm (Nat.one_le_of_lt hq)]
        · exact pow_ne_zero _ (X_sub_C_ne_zero r)
        · rintro rfl
          rw [mul_zero]; rw [Polynomial.map_eq_zero_iff inj_amap] at hp
          exact p0 hp
      _ <= p.natDegree := natDegree_map_le
  rw [← zero_add ((q - 1)! • p'.eval r)]
  rw [sumIDeriv_apply]; rw [map_sum]; rw [map_sum]; rw [this]
  have : range q = range (q - 1 + 1) := by rw [tsub_add_cancel_of_le (Nat.one_le_of_lt hq)]
  rw [sum_union]; rw [this]; rw [sum_range_succ]
  · congr 2
    · apply sum_eq_zero
      exact fun x hx => aeval_iterate_derivative_of_lt p _ r hp (mem_range.mp hx)
    · rw [← aeval_iterate_derivative_self _ _ _ hp]
    · rw [smul_sum, sum_congr rfl]
      intro k hk
      exact hc k (mem_Ico.mp hk).1 r
  · rw [range_eq_Ico, disjoint_iff_inter_eq_empty, eq_empty_iff_forall_notMem]
    intro x hx
    rw [mem_inter]; rw [mem_Ico]; rw [mem_Ico] at hx
    exact hx.1.2.not_ge hx.2.1

end CommSemiring

/--
theorem `eval_sumIDeriv_of_pos` / 定理 `eval_sumIDeriv_of_pos`

English:
theorem eval_sumIDeriv_of_pos
  proof: by
  simpa using aeval_sumIDeriv_of_pos R p hq Function.injective_id

中文:
定理 eval_sumIDeriv_of_pos
  证明: by
  simpa using aeval_sumIDeriv_of_pos R p hq Function.injective_id

Depends on / 依赖: Function, Function.injective_id, aeval_sumIDeriv_of_pos, injective_id
-/
theorem eval_sumIDeriv_of_pos
    [CommRing R] [Nontrivial R] [NoZeroDivisors R] (p : R[X]) {q : Nat} (hq : 0 < q) :
    exists gp : R[X], gp.natDegree <= p.natDegree - q ∧
      forall (r : R) {p' : R[X]},
        p = ((X : R[X]) - C r) ^ (q - 1) * p' ->
        eval r (sumIDeriv p) = (q - 1)! • p'.eval r + q ! • eval r gp := by
  simpa using aeval_sumIDeriv_of_pos R p hq Function.injective_id

end Polynomial
