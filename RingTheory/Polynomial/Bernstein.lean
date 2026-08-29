/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Algebra.Polynomial.Eval.SMul
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Mathlib.RingTheory.Polynomial.Pochhammer

/-!
# Bernstein polynomials

The definition of the Bernstein polynomials
```
bernsteinPolynomial (R : Type*) [CommRing R] (n ν : ℕ) : R[X] :=
(choose n ν) * X^ν * (1 - X)^(n - ν)
```
and the fact that for `ν : Fin (n+1)` these are linearly independent over `ℚ`.

We prove the basic identities
* `(Finset.range (n + 1)).sum (fun ν ↦ bernsteinPolynomial R n ν) = 1`
* `(Finset.range (n + 1)).sum (fun ν ↦ ν • bernsteinPolynomial R n ν) = n • X`
* `(Finset.range (n + 1)).sum (fun ν ↦ (ν * (ν-1)) • bernsteinPolynomial R n ν) = (n * (n-1)) • X^2`

## Notes

See also `Mathlib/Analysis/SpecialFunctions/Bernstein.lean`, which defines the Bernstein
approximations of a continuous function `f : C([0,1], ℝ)`, and shows that these converge uniformly
to `f`.
-/

@[expose] public section


noncomputable section

open Nat (choose)

open Polynomial (X)

open scoped Polynomial

variable (R : Type*) [CommRing R]

/--
Definition of `bernsteinPolynomial` / `bernsteinPolynomial` 的定义

English:
definition bernsteinPolynomial
  signature: (n ν : Nat)
  body: (choose n ν : R[X]) * X ^ ν * (1 - X) ^ (n - ν)

example : bernsteinPolynomial Int 3 2 = 3 * X ^ 2 - 3 * X ^ 3 := by
  norm_num [bernsteinPolynomial, choose]
  ring

中文:
定义 bernsteinPolynomial
  签名: (n ν : 自然数)
  定义体: (choose n ν : R[X]) * X ^ ν * (1 - X) ^ (n - ν)

example : bernsteinPolynomial Int 3 2 = 3 * X ^ 2 - 3 * X ^ 3 := by
  norm_num [bernsteinPolynomial, choose]
  ring
-/
def bernsteinPolynomial (n ν : Nat) : R[X] :=
  (choose n ν : R[X]) * X ^ ν * (1 - X) ^ (n - ν)

example : bernsteinPolynomial Int 3 2 = 3 * X ^ 2 - 3 * X ^ 3 := by
  norm_num [bernsteinPolynomial, choose]
  ring

namespace bernsteinPolynomial

/--
theorem `eq_zero_of_lt` / 定理 `eq_zero_of_lt`

English:
theorem eq_zero_of_lt
  given: {n ν : Nat} (h : n < ν)
  statement: bernsteinPolynomial R n ν = 0
  proof: by
  simp [bernsteinPolynomial, Nat.choose_eq_zero_of_lt h]

中文:
定理 eq_zero_of_lt
  条件: {n ν : 自然数} (h : n < ν)
  结论: bernsteinPolynomial R n ν = 0
  证明: by
  simp [bernsteinPolynomial, Nat.choose_eq_zero_of_lt h]

Depends on / 依赖: Nat.choose_eq_zero_of_lt, bernsteinPolynomial, choose_eq_zero_of_lt
-/
theorem eq_zero_of_lt {n ν : Nat} (h : n < ν) : bernsteinPolynomial R n ν = 0 := by
  simp [bernsteinPolynomial, Nat.choose_eq_zero_of_lt h]

section

variable {R} {S : Type*} [CommRing S]

@[simp]
/--
theorem `map` / 定理 `map`

English:
theorem map
  given: (f : R ->+* S) (n ν : Nat)
  proof: by simp [bernsteinPolynomial]

中文:
定理 map
  条件: (f : R ->+* S) (n ν : 自然数)
  证明: by simp [bernsteinPolynomial]

Depends on / 依赖: bernsteinPolynomial
-/
theorem map (f : R ->+* S) (n ν : Nat) :
    (bernsteinPolynomial R n ν).map f = bernsteinPolynomial S n ν := by simp [bernsteinPolynomial]

end

/--
theorem `flip` / 定理 `flip`

English:
theorem flip
  given: (n ν : Nat) (h : ν <= n)
  proof: by
  simp [bernsteinPolynomial, h, tsub_tsub_assoc, mul_right_comm]

中文:
定理 flip
  条件: (n ν : 自然数) (h : ν <= n)
  证明: by
  simp [bernsteinPolynomial, h, tsub_tsub_assoc, mul_right_comm]

Depends on / 依赖: bernsteinPolynomial, mul_right_comm, tsub_tsub_assoc
-/
theorem flip (n ν : Nat) (h : ν <= n) :
    (bernsteinPolynomial R n ν).comp (1 - X) = bernsteinPolynomial R n (n - ν) := by
  simp [bernsteinPolynomial, h, tsub_tsub_assoc, mul_right_comm]

/--
theorem `flip'` / 定理 `flip'`

English:
theorem flip'
  given: (n ν : Nat) (h : ν <= n)
  proof: by
  simp [← flip _ _ _ h, Polynomial.comp_assoc]

中文:
定理 flip'
  条件: (n ν : 自然数) (h : ν <= n)
  证明: by
  simp [← flip _ _ _ h, Polynomial.comp_assoc]

Depends on / 依赖: Polynomial, Polynomial.comp_assoc, comp_assoc
-/
theorem flip' (n ν : Nat) (h : ν <= n) :
    bernsteinPolynomial R n ν = (bernsteinPolynomial R n (n - ν)).comp (1 - X) := by
  simp [← flip _ _ _ h, Polynomial.comp_assoc]

/--
theorem `eval_at_0` / 定理 `eval_at_0`

English:
theorem eval_at_0
  given: (n ν : Nat)
  statement: (bernsteinPolynomial R n ν).eval 0 = if ν = 0 then 1 else 0
  proof: by
  rw [bernsteinPolynomial]
  split_ifs with h
  · subst h; simp
  · simp [zero_pow h]

中文:
定理 eval_at_0
  条件: (n ν : 自然数)
  结论: (bernsteinPolynomial R n ν).eval 0 = if ν = 0 then 1 else 0
  证明: by
  rw [bernsteinPolynomial]
  split_ifs with h
  · subst h; simp
  · simp [zero_pow h]

Depends on / 依赖: bernsteinPolynomial, split_ifs, zero_pow
-/
theorem eval_at_0 (n ν : Nat) : (bernsteinPolynomial R n ν).eval 0 = if ν = 0 then 1 else 0 := by
  rw [bernsteinPolynomial]
  split_ifs with h
  · subst h; simp
  · simp [zero_pow h]

/--
theorem `eval_at_1` / 定理 `eval_at_1`

English:
theorem eval_at_1
  given: (n ν : Nat)
  statement: (bernsteinPolynomial R n ν).eval 1 = if ν = n then 1 else 0
  proof: by
  rw [bernsteinPolynomial]
  split_ifs with h
  · subst h; simp
  · obtain hνn | hnν := Ne.lt_or_gt h
    · simp [zero_pow <| Nat.sub_ne_zero_of_lt hνn]
    · simp [Nat.choose_eq_zero_of_lt hnν]

中文:
定理 eval_at_1
  条件: (n ν : 自然数)
  结论: (bernsteinPolynomial R n ν).eval 1 = if ν = n then 1 else 0
  证明: by
  rw [bernsteinPolynomial]
  split_ifs with h
  · subst h; simp
  · obtain hνn | hnν := Ne.lt_or_gt h
    · simp [zero_pow <| Nat.sub_ne_zero_of_lt hνn]
    · simp [Nat.choose_eq_zero_of_lt hnν]

Depends on / 依赖: Nat.choose_eq_zero_of_lt, Nat.sub_ne_zero_of_lt, Ne.lt_or_gt, bernsteinPolynomial, choose_eq_zero_of_lt, lt_or_gt, split_ifs, sub_ne_zero_of_lt, zero_pow
-/
theorem eval_at_1 (n ν : Nat) : (bernsteinPolynomial R n ν).eval 1 = if ν = n then 1 else 0 := by
  rw [bernsteinPolynomial]
  split_ifs with h
  · subst h; simp
  · obtain hνn | hnν := Ne.lt_or_gt h
    · simp [zero_pow <| Nat.sub_ne_zero_of_lt hνn]
    · simp [Nat.choose_eq_zero_of_lt hnν]

/--
theorem `derivative_succ_aux` / 定理 `derivative_succ_aux`

English:
theorem derivative_succ_aux
  given: (n ν : Nat)
  proof: by
  rw [bernsteinPolynomial]
  suffices ((n + 1).choose (ν + 1) : R[X]) * ((↑(ν + 1 : Nat) : R[X]) * X ^ ν) * (1 - X) ^ (n - ν) -
      ((n + 1).choose (ν + 1) : R[X]) * X ^ (ν + 1) * ((↑(n - ν) : R[X]) * (1 - X) ^ (n - ν - 1)) =
      (↑(n + 1) : R[X]) * ((n.choose ν : R[X]) * X ^ ν * (1 - X) ^ (n

中文:
定理 derivative_succ_aux
  条件: (n ν : 自然数)
  证明: by
  rw [bernsteinPolynomial]
  suffices ((n + 1).choose (ν + 1) : R[X]) * ((↑(ν + 1 : Nat) : R[X]) * X ^ ν) * (1 - X) ^ (n - ν) -
      ((n + 1).choose (ν + 1) : R[X]) * X ^ (ν + 1) * ((↑(n - ν) : R[X]) * (1 - X) ^ (n - ν - 1)) =
      (↑(n + 1) : R[X]) * ((n.choose ν : R[X]) * X ^ ν * (1 - X) ^ (n

Depends on / 依赖: Nat.succ_sub_succ_eq_sub, Polynomial, Polynomial.derivative_mul, Polynomial.derivative_natCast, Polynomial.derivative_pow, bernsteinPolynomial, derivative_mul, derivative_natCast, derivative_pow, n.choose, sub_eq_add_neg, succ_sub_succ_eq_sub
-/
theorem derivative_succ_aux (n ν : Nat) :
    Polynomial.derivative (bernsteinPolynomial R (n + 1) (ν + 1)) =
      (n + 1) * (bernsteinPolynomial R n ν - bernsteinPolynomial R n (ν + 1)) := by
  rw [bernsteinPolynomial]
  suffices ((n + 1).choose (ν + 1) : R[X]) * ((↑(ν + 1 : Nat) : R[X]) * X ^ ν) * (1 - X) ^ (n - ν) -
      ((n + 1).choose (ν + 1) : R[X]) * X ^ (ν + 1) * ((↑(n - ν) : R[X]) * (1 - X) ^ (n - ν - 1)) =
      (↑(n + 1) : R[X]) * ((n.choose ν : R[X]) * X ^ ν * (1 - X) ^ (n - ν) -
        (n.choose (ν + 1) : R[X]) * X ^ (ν + 1) * (1 - X) ^ (n - (ν + 1))) by
    simpa [Polynomial.derivative_pow, ← sub_eq_add_neg, Nat.succ_sub_succ_eq_sub,
      Polynomial.derivative_mul, Polynomial.derivative_natCast, zero_mul,
      Nat.cast_add, algebraMap.coe_one, Polynomial.derivative_X, mul_one, zero_add,
      Polynomial.derivative_sub, Polynomial.derivative_one, zero_sub, mul_neg, Nat.sub_zero,
      bernsteinPolynomial, map_add, map_natCast, Nat.cast_one]
  conv_rhs => rw [mul_sub]
  -- We'll prove the two terms match up separately.
  refine congr (congr_arg Sub.sub ?_) ?_
  · simp only [← mul_assoc]
    apply congr (congr_arg (· * ·) (congr (congr_arg (· * ·) _) rfl)) rfl
    -- Now it's just about binomial coefficients
    exact mod_cast congr_arg (fun m : Nat => (m : R[X])) (Nat.add_one_mul_choose_eq n ν).symm
  · rw [← tsub_add_eq_tsub_tsub, ← mul_assoc, ← mul_assoc]; congr 1
    rw [mul_comm]; rw [← mul_assoc]; rw [← mul_assoc]; congr 1
    norm_cast
    congr 1
    convert! (Nat.choose_mul_succ_eq n (ν + 1)).symm using 1
    · convert! mul_comm _ _ using 2
      simp
    · apply mul_comm

/--
theorem `derivative_succ` / 定理 `derivative_succ`

English:
theorem derivative_succ
  given: (n ν : Nat)
  statement: Polynomial.derivative (bernsteinPolynomial R n (ν + 1)) =
  proof: by
  cases n
  · simp [bernsteinPolynomial]
  · rw [Nat.cast_succ]; apply derivative_succ_aux

中文:
定理 derivative_succ
  条件: (n ν : 自然数)
  结论: Polynomial.derivative (bernsteinPolynomial R n (ν + 1)) =
  证明: by
  cases n
  · simp [bernsteinPolynomial]
  · rw [Nat.cast_succ]; apply derivative_succ_aux

Depends on / 依赖: Nat.cast_succ, bernsteinPolynomial, cast_succ, derivative_succ_aux
-/
theorem derivative_succ (n ν : Nat) : Polynomial.derivative (bernsteinPolynomial R n (ν + 1)) =
    n * (bernsteinPolynomial R (n - 1) ν - bernsteinPolynomial R (n - 1) (ν + 1)) := by
  cases n
  · simp [bernsteinPolynomial]
  · rw [Nat.cast_succ]; apply derivative_succ_aux

/--
theorem `derivative_zero` / 定理 `derivative_zero`

English:
theorem derivative_zero
  given: (n : Nat)
  proof: by
  simp [bernsteinPolynomial, Polynomial.derivative_pow]

中文:
定理 derivative_zero
  条件: (n : 自然数)
  证明: by
  simp [bernsteinPolynomial, Polynomial.derivative_pow]

Depends on / 依赖: Polynomial, Polynomial.derivative_pow, bernsteinPolynomial, derivative_pow
-/
theorem derivative_zero (n : Nat) :
    Polynomial.derivative (bernsteinPolynomial R n 0) = -n * bernsteinPolynomial R (n - 1) 0 := by
  simp [bernsteinPolynomial, Polynomial.derivative_pow]

/--
theorem `iterate_derivative_at_0_eq_zero_of_lt` / 定理 `iterate_derivative_at_0_eq_zero_of_lt`

English:
theorem iterate_derivative_at_0_eq_zero_of_lt
  given: (n : Nat) {ν k : Nat}
  proof: by
  rcases ν with - | ν
  · rintro ⟨⟩
  · rw [Nat.lt_succ_iff]
    induction k generalizing n ν with
    | zero => simp [eval_at_0]
    | succ k ih =>
      simp only [derivative_succ, Function.comp_apply,
        Function.iterate_succ, Polynomial.iterate_derivative_sub,
        Polynomial.iterate_

中文:
定理 iterate_derivative_at_0_eq_zero_of_lt
  条件: (n : 自然数) {ν k : 自然数}
  证明: by
  rcases ν with - | ν
  · rintro ⟨⟩
  · rw [Nat.lt_succ_iff]
    induction k generalizing n ν with
    | zero => simp [eval_at_0]
    | succ k ih =>
      simp only [derivative_succ, Function.comp_apply,
        Function.iterate_succ, Polynomial.iterate_derivative_sub,
        Polynomial.iterate_

Depends on / 依赖: Function, Function.comp_apply, Function.iterate_succ, Nat.le_of_succ_le, Nat.lt_succ_iff, Nat.pred_le_pred, Nat.succ_pred_eq_of_p, Polynomial, Polynomial.eval_mul, Polynomial.eval_natCast, Polynomial.eval_sub, Polynomial.iterate_derivative_natCast_mul, Polynomial.iterate_derivative_sub, comp_apply, convert, derivative_succ, eval_at_0, eval_mul, eval_natCast, eval_sub
-/
theorem iterate_derivative_at_0_eq_zero_of_lt (n : Nat) {ν k : Nat} :
    k < ν -> (Polynomial.derivative^[k] (bernsteinPolynomial R n ν)).eval 0 = 0 := by
  rcases ν with - | ν
  · rintro ⟨⟩
  · rw [Nat.lt_succ_iff]
    induction k generalizing n ν with
    | zero => simp [eval_at_0]
    | succ k ih =>
      simp only [derivative_succ, Function.comp_apply,
        Function.iterate_succ, Polynomial.iterate_derivative_sub,
        Polynomial.iterate_derivative_natCast_mul, Polynomial.eval_mul, Polynomial.eval_natCast,
        Polynomial.eval_sub]
      intro h
      apply mul_eq_zero_of_right
      rw [ih _ _ (Nat.le_of_succ_le h)]; rw [sub_zero]
      convert! ih _ _ (Nat.pred_le_pred h)
      exact (Nat.succ_pred_eq_of_pos (k.succ_pos.trans_le h)).symm

@[simp]
/--
theorem `iterate_derivative_succ_at_0_eq_zero` / 定理 `iterate_derivative_succ_at_0_eq_zero`

English:
theorem iterate_derivative_succ_at_0_eq_zero
  given: (n ν : Nat)
  proof: iterate_derivative_at_0_eq_zero_of_lt R n (lt_add_one ν)

中文:
定理 iterate_derivative_succ_at_0_eq_zero
  条件: (n ν : 自然数)
  证明: iterate_derivative_at_0_eq_zero_of_lt R n (lt_add_one ν)

Depends on / 依赖: iterate_derivative_at_0_eq_zero_of_lt, lt_add_one
-/
theorem iterate_derivative_succ_at_0_eq_zero (n ν : Nat) :
    (Polynomial.derivative^[ν] (bernsteinPolynomial R n (ν + 1))).eval 0 = 0 :=
  iterate_derivative_at_0_eq_zero_of_lt R n (lt_add_one ν)

open Polynomial

@[simp]
/--
theorem `iterate_derivative_at_0` / 定理 `iterate_derivative_at_0`

English:
theorem iterate_derivative_at_0
  given: (n ν : Nat)
  proof: by
  by_cases! h : ν <= n
  · induction ν generalizing n with
    | zero => simp [eval_at_0]
    | succ ν ih =>
      have h' : ν <= n - 1 := le_tsub_of_add_le_right h
      simp only [derivative_succ, ih (n - 1) h', iterate_derivative_succ_at_0_eq_zero,
        Nat.succ_sub_succ_eq_sub, sub_zero, i

中文:
定理 iterate_derivative_at_0
  条件: (n ν : 自然数)
  证明: by
  by_cases! h : ν <= n
  · induction ν generalizing n with
    | zero => simp [eval_at_0]
    | succ ν ih =>
      have h' : ν <= n - 1 := le_tsub_of_add_le_right h
      simp only [derivative_succ, ih (n - 1) h', iterate_derivative_succ_at_0_eq_zero,
        Nat.succ_sub_succ_eq_sub, sub_zero, i

Depends on / 依赖: Function, Function.comp_apply, Function.iterate_succ, Nat.succ_sub_succ_eq_sub, ascPochhammer_succ_left, comp_apply, derivative_succ, eq_zero_or_po, eval_X, eval_add, eval_at_0, eval_comp, eval_mul, eval_natCast, eval_one, eval_sub, generalizing, iterate_derivative_natCast_mul, iterate_derivative_sub, iterate_derivative_succ_at_0_eq_zero
-/
theorem iterate_derivative_at_0 (n ν : Nat) :
    (Polynomial.derivative^[ν] (bernsteinPolynomial R n ν)).eval 0 =
      (ascPochhammer R ν).eval ((n - (ν - 1) : Nat) : R) := by
  by_cases! h : ν <= n
  · induction ν generalizing n with
    | zero => simp [eval_at_0]
    | succ ν ih =>
      have h' : ν <= n - 1 := le_tsub_of_add_le_right h
      simp only [derivative_succ, ih (n - 1) h', iterate_derivative_succ_at_0_eq_zero,
        Nat.succ_sub_succ_eq_sub, sub_zero, iterate_derivative_sub,
        iterate_derivative_natCast_mul, eval_one, eval_mul, eval_add, eval_sub, eval_X, eval_comp,
        eval_natCast, Function.comp_apply, Function.iterate_succ, ascPochhammer_succ_left]
      obtain rfl | h'' := ν.eq_zero_or_pos
      · simp
      · have : n - 1 - (ν - 1) = n - ν := by lia
        rw [this]; rw [ascPochhammer_eval_succ]; rw [Nat.sub_zero]
        rw_mod_cast [tsub_add_cancel_of_le (h'.trans n.pred_le)]
  · rw [tsub_eq_zero_iff_le.mpr (Nat.le_sub_one_of_lt h), eq_zero_of_lt R h]
    simp [pos_iff_ne_zero.mp (pos_of_gt h)]

/--
theorem `iterate_derivative_at_0_ne_zero` / 定理 `iterate_derivative_at_0_ne_zero`

English:
theorem iterate_derivative_at_0_ne_zero
  given: [CharZero R] (n ν : Nat) (h : ν <= n)
  proof: by
  simp only [bernsteinPolynomial.iterate_derivative_at_0, Ne]
  simp only [← ascPochhammer_eval_cast]
  norm_cast
  apply ne_of_gt
  obtain rfl | h' := Nat.eq_zero_or_pos ν
  · simp
  · rw [← Nat.succ_pred_eq_of_pos h'] at h
    exact ascPochhammer_pos _ _ (tsub_pos_of_lt (Nat.lt_of_succ_le h))

中文:
定理 iterate_derivative_at_0_ne_zero
  条件: [CharZero R] (n ν : 自然数) (h : ν <= n)
  证明: by
  simp only [bernsteinPolynomial.iterate_derivative_at_0, Ne]
  simp only [← ascPochhammer_eval_cast]
  norm_cast
  apply ne_of_gt
  obtain rfl | h' := Nat.eq_zero_or_pos ν
  · simp
  · rw [← Nat.succ_pred_eq_of_pos h'] at h
    exact ascPochhammer_pos _ _ (tsub_pos_of_lt (Nat.lt_of_succ_le h))

Depends on / 依赖: Nat.eq_zero_or_pos, Nat.lt_of_succ_le, Nat.succ_pred_eq_of_pos, ascPochhammer_eval_cast, ascPochhammer_pos, bernsteinPolynomial, bernsteinPolynomial.iterate_derivative_at_0, eq_zero_or_pos, iterate_derivative_at_0, lt_of_succ_le, ne_of_gt, succ_pred_eq_of_pos, tsub_pos_of_lt
-/
theorem iterate_derivative_at_0_ne_zero [CharZero R] (n ν : Nat) (h : ν <= n) :
    (Polynomial.derivative^[ν] (bernsteinPolynomial R n ν)).eval 0 != 0 := by
  simp only [bernsteinPolynomial.iterate_derivative_at_0, Ne]
  simp only [← ascPochhammer_eval_cast]
  norm_cast
  apply ne_of_gt
  obtain rfl | h' := Nat.eq_zero_or_pos ν
  · simp
  · rw [← Nat.succ_pred_eq_of_pos h'] at h
    exact ascPochhammer_pos _ _ (tsub_pos_of_lt (Nat.lt_of_succ_le h))



/--
theorem `iterate_derivative_at_1_eq_zero_of_lt` / 定理 `iterate_derivative_at_1_eq_zero_of_lt`

English:
theorem iterate_derivative_at_1_eq_zero_of_lt
  given: (n : Nat) {ν k : Nat}
  proof: by
  intro w
  rw [flip' _ _ _ (tsub_pos_iff_lt.mp (pos_of_gt w)).le]
  simp [Polynomial.eval_comp, iterate_derivative_at_0_eq_zero_of_lt R n w]

@[simp]

中文:
定理 iterate_derivative_at_1_eq_zero_of_lt
  条件: (n : 自然数) {ν k : 自然数}
  证明: by
  intro w
  rw [flip' _ _ _ (tsub_pos_iff_lt.mp (pos_of_gt w)).le]
  simp [Polynomial.eval_comp, iterate_derivative_at_0_eq_zero_of_lt R n w]

@[simp]

Depends on / 依赖: Polynomial, Polynomial.eval_comp, eval_comp, iterate_derivative_at_0_eq_zero_of_lt, pos_of_gt, tsub_pos_iff_lt, tsub_pos_iff_lt.mp
-/
theorem iterate_derivative_at_1_eq_zero_of_lt (n : Nat) {ν k : Nat} :
    k < n - ν -> (Polynomial.derivative^[k] (bernsteinPolynomial R n ν)).eval 1 = 0 := by
  intro w
  rw [flip' _ _ _ (tsub_pos_iff_lt.mp (pos_of_gt w)).le]
  simp [Polynomial.eval_comp, iterate_derivative_at_0_eq_zero_of_lt R n w]

@[simp]
/--
theorem `iterate_derivative_at_1` / 定理 `iterate_derivative_at_1`

English:
theorem iterate_derivative_at_1
  given: (n ν : Nat) (h : ν <= n)
  proof: by
  rw [flip' _ _ _ h]
  simp only [iterate_derivative_comp_one_sub_X, eval_mul, eval_pow, eval_neg, eval_one, eval_comp,
    eval_sub, eval_X, sub_self, iterate_derivative_at_0]
  obtain rfl | h' := h.eq_or_lt
  · simp
  · norm_cast
    congr
    lia

中文:
定理 iterate_derivative_at_1
  条件: (n ν : 自然数) (h : ν <= n)
  证明: by
  rw [flip' _ _ _ h]
  simp only [iterate_derivative_comp_one_sub_X, eval_mul, eval_pow, eval_neg, eval_one, eval_comp,
    eval_sub, eval_X, sub_self, iterate_derivative_at_0]
  obtain rfl | h' := h.eq_or_lt
  · simp
  · norm_cast
    congr
    lia

Depends on / 依赖: eq_or_lt, eval_X, eval_comp, eval_mul, eval_neg, eval_one, eval_pow, eval_sub, h.eq_or_lt, iterate_derivative_at_0, iterate_derivative_comp_one_sub_X, sub_self
-/
theorem iterate_derivative_at_1 (n ν : Nat) (h : ν <= n) :
    (Polynomial.derivative^[n - ν] (bernsteinPolynomial R n ν)).eval 1 =
      (-1) ^ (n - ν) * (ascPochhammer R (n - ν)).eval (ν + 1 : R) := by
  rw [flip' _ _ _ h]
  simp only [iterate_derivative_comp_one_sub_X, eval_mul, eval_pow, eval_neg, eval_one, eval_comp,
    eval_sub, eval_X, sub_self, iterate_derivative_at_0]
  obtain rfl | h' := h.eq_or_lt
  · simp
  · norm_cast
    congr
    lia

/--
theorem `iterate_derivative_at_1_ne_zero` / 定理 `iterate_derivative_at_1_ne_zero`

English:
theorem iterate_derivative_at_1_ne_zero
  given: [CharZero R] (n ν : Nat) (h : ν <= n)
  proof: by
  rw [bernsteinPolynomial.iterate_derivative_at_1 _ _ _ h]; rw [Ne]; rw [neg_one_pow_mul_eq_zero_iff]; rw [←
    Nat.cast_succ]; rw [← ascPochhammer_eval_cast]; rw [← Nat.cast_zero]; rw [Nat.cast_inj]
  exact (ascPochhammer_pos _ _ (Nat.succ_pos ν)).ne'

中文:
定理 iterate_derivative_at_1_ne_zero
  条件: [CharZero R] (n ν : 自然数) (h : ν <= n)
  证明: by
  rw [bernsteinPolynomial.iterate_derivative_at_1 _ _ _ h]; rw [Ne]; rw [neg_one_pow_mul_eq_zero_iff]; rw [←
    Nat.cast_succ]; rw [← ascPochhammer_eval_cast]; rw [← Nat.cast_zero]; rw [Nat.cast_inj]
  exact (ascPochhammer_pos _ _ (Nat.succ_pos ν)).ne'

Depends on / 依赖: Nat.cast_inj, Nat.cast_succ, Nat.cast_zero, Nat.succ_pos, ascPochhammer_eval_cast, ascPochhammer_pos, bernsteinPolynomial, bernsteinPolynomial.iterate_derivative_at_1, cast_inj, cast_succ, cast_zero, iterate_derivative_at_1, neg_one_pow_mul_eq_zero_iff, succ_pos
-/
theorem iterate_derivative_at_1_ne_zero [CharZero R] (n ν : Nat) (h : ν <= n) :
    (Polynomial.derivative^[n - ν] (bernsteinPolynomial R n ν)).eval 1 != 0 := by
  rw [bernsteinPolynomial.iterate_derivative_at_1 _ _ _ h]; rw [Ne]; rw [neg_one_pow_mul_eq_zero_iff]; rw [←
    Nat.cast_succ]; rw [← ascPochhammer_eval_cast]; rw [← Nat.cast_zero]; rw [Nat.cast_inj]
  exact (ascPochhammer_pos _ _ (Nat.succ_pos ν)).ne'

open Submodule

/--
theorem `linearIndependent_aux` / 定理 `linearIndependent_aux`

English:
theorem linearIndependent_aux
  given: (n k : Nat) (h : k <= n + 1)
  proof: by
  induction k with
  | zero => apply linearIndependent_empty_type
  | succ k ih =>
    apply linearIndependent_finSucc'.mpr
    fconstructor
    · exact ih (le_of_lt h)
    · -- The actual work!
      -- We show that the (n-k)-th derivative at 1 doesn't vanish,
      -- but vanishes for everythin

中文:
定理 linearIndependent_aux
  条件: (n k : 自然数) (h : k <= n + 1)
  证明: by
  induction k with
  | zero => apply linearIndependent_empty_type
  | succ k ih =>
    apply linearIndependent_finSucc'.mpr
    fconstructor
    · exact ih (le_of_lt h)
    · -- The actual work!
      -- We show that the (n-k)-th derivative at 1 doesn't vanish,
      -- but vanishes for everythin

Depends on / 依赖: actual, fconstructor, le_of_lt, linearIndependent_empty_type, linearIndependent_finSucc
-/
theorem linearIndependent_aux (n k : Nat) (h : k <= n + 1) :
    LinearIndependent Rat fun ν : Fin k => bernsteinPolynomial Rat n ν := by
  induction k with
  | zero => apply linearIndependent_empty_type
  | succ k ih =>
    apply linearIndependent_finSucc'.mpr
    fconstructor
    · exact ih (le_of_lt h)
    · -- The actual work!
      -- We show that the (n-k)-th derivative at 1 doesn't vanish,
      -- but vanishes for everything in the span.
      clear ih
      simp only [add_le_add_iff_right] at h
      simp only [Fin.val_last, Fin.init_def]
      dsimp
      apply notMem_span_of_apply_notMem_span_image (@Polynomial.derivative Rat _ ^ (n - k))
      -- Note: https://github.com/leanprover-community/mathlib4/pull/8386 had to change `span_image` into `span_image _`
      simp only [not_exists, not_and, Submodule.mem_map, Submodule.span_image _]
      intro p m
      apply_fun Polynomial.eval (1 : Rat)
      simp only [Module.End.pow_apply]
      -- The right-hand side is nonzero,
      -- so it will suffice to show the left-hand side is always zero.
      suffices (Polynomial.derivative^[n - k] p).eval 1 = 0 by
        rw [this]
        exact (iterate_derivative_at_1_ne_zero Rat n k h).symm
      refine span_induction ?_ ?_ ?_ ?_ m
      · simp only [Set.mem_range, forall_exists_index, forall_apply_eq_imp_iff]
        rintro ⟨a, w⟩; simp only
        rw [iterate_derivative_at_1_eq_zero_of_lt Rat n ((tsub_lt_tsub_iff_left_of_le h).mpr w)]
      · simp
      · intro x y _ _ hx hy; simp [hx, hy]
      · intro a x _ h; simp [h]

/--
theorem `linearIndependent` / 定理 `linearIndependent`

English:
theorem linearIndependent
  given: (n : Nat)
  proof: linearIndependent_aux n (n + 1) le_rfl

中文:
定理 linearIndependent
  条件: (n : 自然数)
  证明: linearIndependent_aux n (n + 1) le_rfl

Depends on / 依赖: le_rfl, linearIndependent_aux
-/
theorem linearIndependent (n : Nat) :
    LinearIndependent Rat fun ν : Fin (n + 1) => bernsteinPolynomial Rat n ν :=
  linearIndependent_aux n (n + 1) le_rfl

/--
theorem `sum` / 定理 `sum`

English:
theorem sum
  given: (n : Nat)
  statement: (∑ ν in Finset.range (n + 1), bernsteinPolynomial R n ν) = 1
  proof: calc
    (∑ ν in Finset.range (n + 1), bernsteinPolynomial R n ν) = (X + (1 - X)) ^ n := by
      rw [add_pow]
      simp only [bernsteinPolynomial, mul_comm, mul_assoc]
    _ = 1 := by simp

中文:
定理 sum
  条件: (n : 自然数)
  结论: (∑ ν in Finset.range (n + 1), bernsteinPolynomial R n ν) = 1
  证明: calc
    (∑ ν in Finset.range (n + 1), bernsteinPolynomial R n ν) = (X + (1 - X)) ^ n := by
      rw [add_pow]
      simp only [bernsteinPolynomial, mul_comm, mul_assoc]
    _ = 1 := by simp

Depends on / 依赖: Finset, Finset.range, add_pow, bernsteinPolynomial, mul_assoc, mul_comm
-/
theorem sum (n : Nat) : (∑ ν in Finset.range (n + 1), bernsteinPolynomial R n ν) = 1 :=
  calc
    (∑ ν in Finset.range (n + 1), bernsteinPolynomial R n ν) = (X + (1 - X)) ^ n := by
      rw [add_pow]
      simp only [bernsteinPolynomial, mul_comm, mul_assoc]
    _ = 1 := by simp

open Polynomial

open MvPolynomial hiding X

/--
theorem `sum_smul` / 定理 `sum_smul`

English:
theorem sum_smul
  given: (n : Nat)
  proof: by
  -- We calculate the `x`-derivative of `(x+y)^n`, evaluated at `y=(1-x)`,
  -- either directly or by using the binomial theorem.
  -- We'll work in `MvPolynomial Bool R`.
  let x : MvPolynomial Bool R := MvPolynomial.X true
  let y : MvPolynomial Bool R := MvPolynomial.X false
  have pderiv_true

中文:
定理 sum_smul
  条件: (n : 自然数)
  证明: by
  -- We calculate the `x`-derivative of `(x+y)^n`, evaluated at `y=(1-x)`,
  -- either directly or by using the binomial theorem.
  -- We'll work in `MvPolynomial Bool R`.
  let x : MvPolynomial Bool R := MvPolynomial.X true
  let y : MvPolynomial Bool R := MvPolynomial.X false
  have pderiv_true
-/
theorem sum_smul (n : Nat) :
    (∑ ν in Finset.range (n + 1), ν • bernsteinPolynomial R n ν) = n • X := by
  -- We calculate the `x`-derivative of `(x+y)^n`, evaluated at `y=(1-x)`,
  -- either directly or by using the binomial theorem.
  -- We'll work in `MvPolynomial Bool R`.
  let x : MvPolynomial Bool R := MvPolynomial.X true
  let y : MvPolynomial Bool R := MvPolynomial.X false
  have pderiv_true_x : pderiv true x = 1 := by rw [pderiv_X]; rfl
  have pderiv_true_y : pderiv true y = 0 := by rw [pderiv_X]; rfl
  let e : Bool -> R[X] := fun i => cond i X (1 - X)
  -- Start with `(x+y)^n = (x+y)^n`,
  -- take the `x`-derivative, evaluate at `x=X, y=1-X`, and multiply by `X`:
  trans MvPolynomial.aeval e (pderiv true ((x + y) ^ n)) * X
  -- On the left-hand side we'll use the binomial theorem, then simplify.
  · -- We first prepare a tedious rewrite:
    have w : forall k : Nat, k • bernsteinPolynomial R n k =
        (k : R[X]) * Polynomial.X ^ (k - 1) * (1 - Polynomial.X) ^ (n - k) * (n.choose k : R[X]) *
          Polynomial.X := by
      rintro (_ | k)
      · simp
      · rw [bernsteinPolynomial]
        simp only [← natCast_mul, Nat.add_succ_sub_one, add_zero, pow_succ]
        push_cast
        ring
    rw [add_pow]; rw [map_sum (pderiv true)]; rw [map_sum (MvPolynomial.aeval e)]; rw [Finset.sum_mul]
    -- Step inside the sum:
    refine Finset.sum_congr rfl fun k _ => (w k).trans ?_
    simp only [x, y, e, pderiv_true_x, pderiv_true_y, smul_eq_mul, nsmul_eq_mul,
      Bool.cond_true, Bool.cond_false, add_zero, mul_one, mul_zero, MvPolynomial.aeval_X,
      MvPolynomial.pderiv_mul, Derivation.leibniz_pow, Derivation.map_natCast, map_natCast, map_pow,
      map_mul]
  · rw [(pderiv true).leibniz_pow, (pderiv true).map_add, pderiv_true_x, pderiv_true_y]
    simp only [x, y, e, smul_eq_mul, nsmul_eq_mul, map_natCast, map_pow, map_add,
      map_mul, Bool.cond_true, Bool.cond_false, MvPolynomial.aeval_X, add_sub_cancel,
      one_pow, add_zero, mul_one]

/--
theorem `sum_mul_smul` / 定理 `sum_mul_smul`

English:
theorem sum_mul_smul
  given: (n : Nat)
  proof: by
  -- We calculate the second `x`-derivative of `(x+y)^n`, evaluated at `y=(1-x)`,
  -- either directly or by using the binomial theorem.
  -- We'll work in `MvPolynomial Bool R`.
  let x : MvPolynomial Bool R := MvPolynomial.X true
  let y : MvPolynomial Bool R := MvPolynomial.X false
  have pder

中文:
定理 sum_mul_smul
  条件: (n : 自然数)
  证明: by
  -- We calculate the second `x`-derivative of `(x+y)^n`, evaluated at `y=(1-x)`,
  -- either directly or by using the binomial theorem.
  -- We'll work in `MvPolynomial Bool R`.
  let x : MvPolynomial Bool R := MvPolynomial.X true
  let y : MvPolynomial Bool R := MvPolynomial.X false
  have pder
-/
theorem sum_mul_smul (n : Nat) :
    (∑ ν in Finset.range (n + 1), (ν * (ν - 1)) • bernsteinPolynomial R n ν) =
      (n * (n - 1)) • X ^ 2 := by
  -- We calculate the second `x`-derivative of `(x+y)^n`, evaluated at `y=(1-x)`,
  -- either directly or by using the binomial theorem.
  -- We'll work in `MvPolynomial Bool R`.
  let x : MvPolynomial Bool R := MvPolynomial.X true
  let y : MvPolynomial Bool R := MvPolynomial.X false
  have pderiv_true_x : pderiv true x = 1 := by rw [pderiv_X]; rfl
  have pderiv_true_y : pderiv true y = 0 := by rw [pderiv_X]; rfl
  let e : Bool -> R[X] := fun i => cond i X (1 - X)
  -- Start with `(x+y)^n = (x+y)^n`,
  -- take the second `x`-derivative, evaluate at `x=X, y=1-X`, and multiply by `X`:
  trans MvPolynomial.aeval e (pderiv true (pderiv true ((x + y) ^ n))) * X ^ 2
  -- On the left-hand side we'll use the binomial theorem, then simplify.
  · -- We first prepare a tedious rewrite:
    have w : forall k : Nat, (k * (k - 1)) • bernsteinPolynomial R n k =
        (n.choose k : R[X]) * ((1 - Polynomial.X) ^ (n - k) *
          ((k : R[X]) * ((↑(k - 1) : R[X]) * Polynomial.X ^ (k - 1 - 1)))) * Polynomial.X ^ 2 := by
      rintro (_ | _ | k)
      · simp
      · simp
      · rw [bernsteinPolynomial]
        simp only [← natCast_mul, Nat.add_succ_sub_one, add_zero, pow_succ]
        push_cast
        ring
    rw [add_pow]; rw [map_sum (pderiv true)]; rw [map_sum (pderiv true)]; rw [map_sum (MvPolynomial.aeval e)]; rw [Finset.sum_mul]
    -- Step inside the sum:
    refine Finset.sum_congr rfl fun k _ => (w k).trans ?_
    simp only [x, y, e, pderiv_true_x, pderiv_true_y, smul_eq_mul, nsmul_eq_mul,
      Bool.cond_true, Bool.cond_false, add_zero, zero_add, mul_zero, mul_one,
      MvPolynomial.aeval_X,
      Derivation.leibniz_pow, Derivation.leibniz, Derivation.map_natCast, map_natCast, map_pow,
      map_mul]
  -- On the right-hand side, we'll just simplify.
  · simp only [x, y, e, (pderiv _).leibniz_pow,
      (pderiv true).map_add, pderiv_true_x, pderiv_true_y, smul_eq_mul, add_zero,
      mul_one, map_nsmul, map_pow, map_add, Bool.cond_true,
      Bool.cond_false, MvPolynomial.aeval_X, add_sub_cancel, one_pow, smul_smul,
      smul_one_mul]

/--
theorem `variance` / 定理 `variance`

English:
theorem variance
  given: (n : Nat)
  proof: by
  have p : ((((Finset.range (n + 1)).sum fun ν => (ν * (ν - 1)) • bernsteinPolynomial R n ν) +
      (1 - (2 * n) • Polynomial.X) * (Finset.range (n + 1)).sum fun ν =>
        ν • bernsteinPolynomial R n ν) + n ^ 2 • X ^ 2 *
          (Finset.range (n + 1)).sum fun ν => bernsteinPolynomial R n ν)

中文:
定理 variance
  条件: (n : 自然数)
  证明: by
  have p : ((((Finset.range (n + 1)).sum fun ν => (ν * (ν - 1)) • bernsteinPolynomial R n ν) +
      (1 - (2 * n) • Polynomial.X) * (Finset.range (n + 1)).sum fun ν =>
        ν • bernsteinPolynomial R n ν) + n ^ 2 • X ^ 2 *
          (Finset.range (n + 1)).sum fun ν => bernsteinPolynomial R n ν)

Depends on / 依赖: Finset, Finset.mul_sum, Finset.range, Finset.sum_add_distrib, Polynomial, Polynomial.X, add_mul, bernsteinPolynomial, mul_assoc, mul_sum, natCast_mul, sum_add_distrib
-/
theorem variance (n : Nat) :
    (∑ ν in Finset.range (n + 1), (n • Polynomial.X - (ν : R[X])) ^ 2 * bernsteinPolynomial R n ν) =
      n • Polynomial.X * ((1 : R[X]) - Polynomial.X) := by
  have p : ((((Finset.range (n + 1)).sum fun ν => (ν * (ν - 1)) • bernsteinPolynomial R n ν) +
      (1 - (2 * n) • Polynomial.X) * (Finset.range (n + 1)).sum fun ν =>
        ν • bernsteinPolynomial R n ν) + n ^ 2 • X ^ 2 *
          (Finset.range (n + 1)).sum fun ν => bernsteinPolynomial R n ν) = _ :=
    rfl
  conv at p =>
    lhs
    rw [Finset.mul_sum]; rw [Finset.mul_sum]; rw [← Finset.sum_add_distrib]; rw [← Finset.sum_add_distrib]
    simp only [← natCast_mul]
    simp only [← mul_assoc]
    simp only [← add_mul]
  conv at p =>
    rhs
    rw [sum]; rw [sum_smul]; rw [sum_mul_smul]; rw [← natCast_mul]
  calc
    _ = _ := Finset.sum_congr rfl fun k m => ?_
    _ = _ := p
    _ = _ := ?_
  · congr 1; simp only [← natCast_mul, push_cast]
    cases k <;> · simp; ring
  · simp only [← natCast_mul, push_cast]
    cases n
    · simp
    · simp; ring

end bernsteinPolynomial
