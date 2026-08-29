/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Julian Kuelshammer, Heather Macbeth, Mitchell Lee
-/
module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Algebra.Polynomial.Degree.Lemmas
public import Mathlib.Algebra.Polynomial.Sequence
public import Mathlib.Algebra.Ring.NegOnePow
public import Mathlib.Tactic.LinearCombination
public import Mathlib.LinearAlgebra.Span.Basic

/-!
# Chebyshev polynomials

The Chebyshev polynomials are families of polynomials indexed by `ℤ`,
with integral coefficients.

## Main definitions

* `Polynomial.Chebyshev.T`: the Chebyshev polynomials of the first kind.
* `Polynomial.Chebyshev.U`: the Chebyshev polynomials of the second kind.
* `Polynomial.Chebyshev.C`: the rescaled Chebyshev polynomials of the first kind (also known as the
  Vieta–Lucas polynomials), given by $C_n(2x) = 2T_n(x)$.
* `Polynomial.Chebyshev.S`: the rescaled Chebyshev polynomials of the second kind (also known as the
  Vieta–Fibonacci polynomials), given by $S_n(2x) = U_n(x)$.

## Main statements

* The formal derivative of the Chebyshev polynomials of the first kind is a scalar multiple of the
  Chebyshev polynomials of the second kind.
* `Polynomial.Chebyshev.T_mul_T`, twice the product of the `m`-th and `k`-th Chebyshev polynomials
  of the first kind is the sum of the `m + k`-th and `m - k`-th Chebyshev polynomials of the first
  kind. There is a similar statement `Polynomial.Chebyshev.C_mul_C` for the `C` polynomials.
* `Polynomial.Chebyshev.T_mul`, the `(m * n)`-th Chebyshev polynomial of the first kind is the
  composition of the `m`-th and `n`-th Chebyshev polynomials of the first kind. There is a similar
  statement `Polynomial.Chebyshev.C_mul` for the `C` polynomials.

## Implementation details

Since Chebyshev polynomials have interesting behaviour over the complex numbers and modulo `p`,
we define them to have coefficients in an arbitrary commutative ring, even though
technically `ℤ` would suffice.
The benefit of allowing arbitrary coefficient rings, is that the statements afterwards are clean,
and do not have `map (Int.castRingHom R)` interfering all the time.

## References

[Lionel Ponton, _Roots of the Chebyshev polynomials: A purely algebraic approach_]
[ponton2020chebyshev]

## TODO

* Redefine and/or relate the definition of Chebyshev polynomials to `LinearRecurrence`.
* Add explicit formula involving square roots for Chebyshev polynomials
-/

@[expose] public section

namespace Polynomial.Chebyshev

open Polynomial

variable (R R' : Type*) [CommRing R] [CommRing R']

/--
Definition of `T` / `T` 的定义

English:
definition T
  signature: : Int -> R[X]

中文:
定义 T
  签名: : 整数 -> R[X]
-/
noncomputable def T : Int -> R[X]
  | 0 => 1
  | 1 => X
  | (n : Nat) + 2 => 2 * X * T (n + 1) - T n
  | -((n : Nat) + 1) => 2 * X * T (-n) - T (-n + 1)
  termination_by n => Int.natAbs n + Int.natAbs (n - 1)

/-- Induction principle used for proving facts about Chebyshev polynomials. -/
@[elab_as_elim]
/--
theorem `induct` / 定理 `induct`

English:
theorem induct
  statement: (motive : Int -> Prop)
  proof: T.induct motive zero one add_two fun n hn hnm => by
    simpa only [Int.negSucc_eq, neg_add] using! neg_add_one n hn hnm

中文:
定理 induct
  结论: (motive : 整数 -> 命题)
  证明: T.induct motive zero one add_two fun n hn hnm => by
    simpa only [Int.negSucc_eq, neg_add] using! neg_add_one n hn hnm
-/
protected theorem induct (motive : Int -> Prop)
    (zero : motive 0)
    (one : motive 1)
    (add_two : forall (n : Nat), motive (↑n + 1) -> motive ↑n -> motive (↑n + 2))
    (neg_add_one : forall (n : Nat), motive (-↑n) -> motive (-↑n + 1) -> motive (-↑n - 1)) :
    forall (a : Int), motive a :=
  T.induct motive zero one add_two fun n hn hnm => by
    simpa only [Int.negSucc_eq, neg_add] using! neg_add_one n hn hnm

/-- Another induction principle used for proving facts about Chebyshev polynomials,
    which is sometimes easier to use -/
@[elab_as_elim]
/--
theorem `induct'` / 定理 `induct'`

English:
theorem induct'
  statement: (motive : Int -> Prop)
  proof: by
  refine Chebyshev.induct motive zero one add_two ?_
  have neg' (n : Int) (h : motive (-n)) : motive n := by
    convert! neg (-n) h; rw [neg_neg]
  intro n h₀ h₁
  cases n with
  | zero => exact neg 1 h₁
  | succ n =>
    apply neg (n + 2) (add_two n (neg' _ h₀) (neg' n ?_))
    convert! h₁ using 1; omega

@[simp]

中文:
定理 induct'
  结论: (motive : 整数 -> 命题)
  证明: by
  refine Chebyshev.induct motive zero one add_two ?_
  have neg' (n : Int) (h : motive (-n)) : motive n := by
    convert! neg (-n) h; rw [neg_neg]
  intro n h₀ h₁
  cases n with
  | zero => exact neg 1 h₁
  | succ n =>
    apply neg (n + 2) (add_two n (neg' _ h₀) (neg' n ?_))
    convert! h₁ using 1; omega

@[simp]
-/
protected theorem induct' (motive : Int -> Prop)
    (zero : motive 0)
    (one : motive 1)
    (add_two : forall (n : Nat), motive (↑n + 1) -> motive ↑n -> motive (↑n + 2))
    (neg : forall (n : Int), motive n -> motive (-n)) :
    forall (a : Int), motive a := by
  refine Chebyshev.induct motive zero one add_two ?_
  have neg' (n : Int) (h : motive (-n)) : motive n := by
    convert! neg (-n) h; rw [neg_neg]
  intro n h₀ h₁
  cases n with
  | zero => exact neg 1 h₁
  | succ n =>
    apply neg (n + 2) (add_two n (neg' _ h₀) (neg' n ?_))
    convert! h₁ using 1; omega

@[simp]
/--
theorem `T_add_two` / 定理 `T_add_two`

English:
theorem T_add_two
  statement: forall n, T R (n + 2) = 2 * X * T R (n + 1) - T R n

中文:
定理 T_add_two
  结论: 对任意 n, T R (n + 2) = 2 * X * T R (n + 1) - T R n

Depends on / 依赖: Int.negSucc_eq, T.eq_4, eq_4, negSucc_eq, ring_nf
-/
theorem T_add_two : forall n, T R (n + 2) = 2 * X * T R (n + 1) - T R n
  | (k : Nat) => T.eq_3 R k
  | -(k + 1 : Nat) => by linear_combination (norm := (simp [Int.negSucc_eq]; ring_nf)) T.eq_4 R k

/--
theorem `T_add_one` / 定理 `T_add_one`

English:
theorem T_add_one
  given: (n : Int)
  statement: T R (n + 1) = 2 * X * T R n - T R (n - 1)
  proof: by
  linear_combination (norm := ring_nf) T_add_two R (n - 1)

中文:
定理 T_add_one
  条件: (n : 整数)
  结论: T R (n + 1) = 2 * X * T R n - T R (n - 1)
  证明: by
  linear_combination (norm := ring_nf) T_add_two R (n - 1)

Depends on / 依赖: T_add_two, linear_combination, ring_nf
-/
theorem T_add_one (n : Int) : T R (n + 1) = 2 * X * T R n - T R (n - 1) := by
  linear_combination (norm := ring_nf) T_add_two R (n - 1)

/--
theorem `T_sub_two` / 定理 `T_sub_two`

English:
theorem T_sub_two
  given: (n : Int)
  statement: T R (n - 2) = 2 * X * T R (n - 1) - T R n
  proof: by
  linear_combination (norm := ring_nf) T_add_two R (n - 2)

中文:
定理 T_sub_two
  条件: (n : 整数)
  结论: T R (n - 2) = 2 * X * T R (n - 1) - T R n
  证明: by
  linear_combination (norm := ring_nf) T_add_two R (n - 2)

Depends on / 依赖: T_add_two, linear_combination, ring_nf
-/
theorem T_sub_two (n : Int) : T R (n - 2) = 2 * X * T R (n - 1) - T R n := by
  linear_combination (norm := ring_nf) T_add_two R (n - 2)

/--
theorem `T_sub_one` / 定理 `T_sub_one`

English:
theorem T_sub_one
  given: (n : Int)
  statement: T R (n - 1) = 2 * X * T R n - T R (n + 1)
  proof: by
  linear_combination (norm := ring_nf) T_add_two R (n - 1)

中文:
定理 T_sub_one
  条件: (n : 整数)
  结论: T R (n - 1) = 2 * X * T R n - T R (n + 1)
  证明: by
  linear_combination (norm := ring_nf) T_add_two R (n - 1)

Depends on / 依赖: T_add_two, linear_combination, ring_nf
-/
theorem T_sub_one (n : Int) : T R (n - 1) = 2 * X * T R n - T R (n + 1) := by
  linear_combination (norm := ring_nf) T_add_two R (n - 1)

/--
theorem `T_eq` / 定理 `T_eq`

English:
theorem T_eq
  given: (n : Int)
  statement: T R n = 2 * X * T R (n - 1) - T R (n - 2)
  proof: by
  linear_combination (norm := ring_nf) T_add_two R (n - 2)

@[simp]

中文:
定理 T_eq
  条件: (n : 整数)
  结论: T R n = 2 * X * T R (n - 1) - T R (n - 2)
  证明: by
  linear_combination (norm := ring_nf) T_add_two R (n - 2)

@[simp]

Depends on / 依赖: T_add_two, linear_combination, ring_nf
-/
theorem T_eq (n : Int) : T R n = 2 * X * T R (n - 1) - T R (n - 2) := by
  linear_combination (norm := ring_nf) T_add_two R (n - 2)

@[simp]
/--
theorem `T_zero` / 定理 `T_zero`

English:
theorem T_zero
  statement: T R 0 = 1
  proof: by simp [T]

@[simp]

中文:
定理 T_zero
  结论: T R 0 = 1
  证明: by simp [T]

@[simp]
-/
theorem T_zero : T R 0 = 1 := by simp [T]

@[simp]
/--
theorem `T_one` / 定理 `T_one`

English:
theorem T_one
  statement: T R 1 = X
  proof: by simp [T]

中文:
定理 T_one
  结论: T R 1 = X
  证明: by simp [T]
-/
theorem T_one : T R 1 = X := by simp [T]

/--
theorem `T_neg_one` / 定理 `T_neg_one`

English:
theorem T_neg_one
  statement: T R (-1) = X
  proof: by
  change T R (Int.negSucc 0) = X
  rw [T]
  suffices 2 * X - X = X by simpa
  ring

中文:
定理 T_neg_one
  结论: T R (-1) = X
  证明: by
  change T R (Int.negSucc 0) = X
  rw [T]
  suffices 2 * X - X = X by simpa
  ring

Depends on / 依赖: Int.negSucc, negSucc
-/
theorem T_neg_one : T R (-1) = X := by
  change T R (Int.negSucc 0) = X
  rw [T]
  suffices 2 * X - X = X by simpa
  ring


/--
theorem `T_two` / 定理 `T_two`

English:
theorem T_two
  statement: T R 2 = 2 * X ^ 2 - 1
  proof: by
  unfold T; simp [pow_two, mul_assoc]

@[simp]

中文:
定理 T_two
  结论: T R 2 = 2 * X ^ 2 - 1
  证明: by
  unfold T; simp [pow_two, mul_assoc]

@[simp]

Depends on / 依赖: mul_assoc, pow_two
-/
theorem T_two : T R 2 = 2 * X ^ 2 - 1 := by
  unfold T; simp [pow_two, mul_assoc]

@[simp]
/--
theorem `T_neg` / 定理 `T_neg`

English:
theorem T_neg
  given: (n : Int)
  statement: T R (-n) = T R n
  proof: by
  induction n using Polynomial.Chebyshev.induct with
  | zero => rfl
  | one => simp only [T_neg_one, T_one]
  | add_two n ih1 ih2 =>
    have h₁ := T_add_two R n
    have h₂ := T_sub_two R (-n)
    linear_combination (norm := ring_nf) (2 * (X : R[X])) * ih1 - ih2 - h₁ + h₂
  | neg_add_one n ih1 ih2 =>
    have h₁ := T_add_one R n
    have h₂ := T_sub_one R (-n)
    linear_combination (norm := ring_nf) (2 * (X : R[X])) * ih1 - ih2 + h₁ - h₂

中文:
定理 T_neg
  条件: (n : 整数)
  结论: T R (-n) = T R n
  证明: by
  induction n using Polynomial.Chebyshev.induct with
  | zero => rfl
  | one => simp only [T_neg_one, T_one]
  | add_two n ih1 ih2 =>
    have h₁ := T_add_two R n
    have h₂ := T_sub_two R (-n)
    linear_combination (norm := ring_nf) (2 * (X : R[X])) * ih1 - ih2 - h₁ + h₂
  | neg_add_one n ih1 ih2 =>
    have h₁ := T_add_one R n
    have h₂ := T_sub_one R (-n)
    linear_combination (norm := ring_nf) (2 * (X : R[X])) * ih1 - ih2 + h₁ - h₂

Depends on / 依赖: Chebyshev, Polynomial, Polynomial.Chebyshev.induct, T_add_one, T_add_two, T_neg_one, T_one, T_sub_one, T_sub_two, add_two, induct, linear_combination, neg_add_one, ring_nf
-/
theorem T_neg (n : Int) : T R (-n) = T R n := by
  induction n using Polynomial.Chebyshev.induct with
  | zero => rfl
  | one => simp only [T_neg_one, T_one]
  | add_two n ih1 ih2 =>
    have h₁ := T_add_two R n
    have h₂ := T_sub_two R (-n)
    linear_combination (norm := ring_nf) (2 * (X : R[X])) * ih1 - ih2 - h₁ + h₂
  | neg_add_one n ih1 ih2 =>
    have h₁ := T_add_one R n
    have h₂ := T_sub_one R (-n)
    linear_combination (norm := ring_nf) (2 * (X : R[X])) * ih1 - ih2 + h₁ - h₂

/--
theorem `T_natAbs` / 定理 `T_natAbs`

English:
theorem T_natAbs
  given: (n : Int)
  statement: T R n.natAbs = T R n
  proof: by
  obtain h | h := Int.natAbs_eq n <;> nth_rw 2 [h]; simp

中文:
定理 T_natAbs
  条件: (n : 整数)
  结论: T R n.natAbs = T R n
  证明: by
  obtain h | h := Int.natAbs_eq n <;> nth_rw 2 [h]; simp

Depends on / 依赖: Int.natAbs_eq, natAbs_eq, nth_rw
-/
theorem T_natAbs (n : Int) : T R n.natAbs = T R n := by
  obtain h | h := Int.natAbs_eq n <;> nth_rw 2 [h]; simp

/--
theorem `T_neg_two` / 定理 `T_neg_two`

English:
theorem T_neg_two
  statement: T R (-2) = 2 * X ^ 2 - 1
  proof: by simp [T_two]

@[simp]

中文:
定理 T_neg_two
  结论: T R (-2) = 2 * X ^ 2 - 1
  证明: by simp [T_two]

@[simp]

Depends on / 依赖: T_two
-/
theorem T_neg_two : T R (-2) = 2 * X ^ 2 - 1 := by simp [T_two]

@[simp]
/--
theorem `T_eval_one` / 定理 `T_eval_one`

English:
theorem T_eval_one
  given: (n : Int)
  statement: (T R n).eval 1 = 1
  proof: by
  induction n using Polynomial.Chebyshev.induct with
  | zero => simp
  | one => simp
  | add_two n ih1 ih2 => simp [T_add_two, ih1, ih2]; norm_num
  | neg_add_one n ih1 ih2 => simp [T_sub_one, -T_neg, ih1, ih2]; norm_num

中文:
定理 T_eval_one
  条件: (n : 整数)
  结论: (T R n).eval 1 = 1
  证明: by
  induction n using Polynomial.Chebyshev.induct with
  | zero => simp
  | one => simp
  | add_two n ih1 ih2 => simp [T_add_two, ih1, ih2]; norm_num
  | neg_add_one n ih1 ih2 => simp [T_sub_one, -T_neg, ih1, ih2]; norm_num

Depends on / 依赖: Chebyshev, Polynomial, Polynomial.Chebyshev.induct, T_add_two, T_neg, T_sub_one, add_two, induct, neg_add_one
-/
theorem T_eval_one (n : Int) : (T R n).eval 1 = 1 := by
  induction n using Polynomial.Chebyshev.induct with
  | zero => simp
  | one => simp
  | add_two n ih1 ih2 => simp [T_add_two, ih1, ih2]; norm_num
  | neg_add_one n ih1 ih2 => simp [T_sub_one, -T_neg, ih1, ih2]; norm_num

set_option backward.isDefEq.respectTransparency false in
/--
theorem `T_eval_neg_one` / 定理 `T_eval_neg_one`

English:
theorem T_eval_neg_one
  given: (n : Int)
  statement: (T R n).eval (-1) = n.negOnePow
  proof: by
  induction n using Polynomial.Chebyshev.induct with
  | zero => simp
  | one => simp
  | add_two n ih1 ih2 =>
    simp only [T_add_two, eval_sub, eval_mul, eval_ofNat, eval_X, mul_neg, mul_one, ih1,
      Int.negOnePow_add, Int.negOnePow_one, Units.val_neg, Int.cast_neg, neg_mul, neg_neg, ih2,
      Int.negOnePow_def 2]
    norm_cast
    norm_num
    ring
  | neg_add_one n ih1 ih2 =>
    simp only [T_sub_one, eval_sub, eval_mul, eval_ofNat, eval_X, mul_neg, mul_one, ih1, neg_mul,
      ih2, Int.negOnePow_add, Int.negOnePow_one, Units.val_neg, Int.cast_neg, sub_neg_eq_add,
      Int.negOnePow_sub]
    ring

中文:
定理 T_eval_neg_one
  条件: (n : 整数)
  结论: (T R n).eval (-1) = n.negOnePow
  证明: by
  induction n using Polynomial.Chebyshev.induct with
  | zero => simp
  | one => simp
  | add_two n ih1 ih2 =>
    simp only [T_add_two, eval_sub, eval_mul, eval_ofNat, eval_X, mul_neg, mul_one, ih1,
      Int.negOnePow_add, Int.negOnePow_one, Units.val_neg, Int.cast_neg, neg_mul, neg_neg, ih2,
      Int.negOnePow_def 2]
    norm_cast
    norm_num
    ring
  | neg_add_one n ih1 ih2 =>
    simp only [T_sub_one, eval_sub, eval_mul, eval_ofNat, eval_X, mul_neg, mul_one, ih1, neg_mul,
      ih2, Int.negOnePow_add, Int.negOnePow_one, Units.val_neg, Int.cast_neg, sub_neg_eq_add,
      Int.negOnePow_sub]
    ring

Depends on / 依赖: Chebyshev, Int.cast_neg, Int.negOnePow_add, Int.negOnePow_def, Int.negOnePow_one, Polynomial, Polynomial.Chebyshev.induct, T_add_two, T_sub_one, Units.val_, Units.val_neg, add_two, cast_neg, eval_X, eval_mul, eval_ofNat, eval_sub, induct, mul_neg, mul_one
-/
theorem T_eval_neg_one (n : Int) : (T R n).eval (-1) = n.negOnePow := by
  induction n using Polynomial.Chebyshev.induct with
  | zero => simp
  | one => simp
  | add_two n ih1 ih2 =>
    simp only [T_add_two, eval_sub, eval_mul, eval_ofNat, eval_X, mul_neg, mul_one, ih1,
      Int.negOnePow_add, Int.negOnePow_one, Units.val_neg, Int.cast_neg, neg_mul, neg_neg, ih2,
      Int.negOnePow_def 2]
    norm_cast
    norm_num
    ring
  | neg_add_one n ih1 ih2 =>
    simp only [T_sub_one, eval_sub, eval_mul, eval_ofNat, eval_X, mul_neg, mul_one, ih1, neg_mul,
      ih2, Int.negOnePow_add, Int.negOnePow_one, Units.val_neg, Int.cast_neg, sub_neg_eq_add,
      Int.negOnePow_sub]
    ring

/--
theorem `T_eval_zero` / 定理 `T_eval_zero`

English:
theorem T_eval_zero
  given: (n : Int)
  proof: by
  induction n using Polynomial.Chebyshev.induct with
  | zero => simp
  | one => simp
  | add_two n ih1 ih2 =>
    have : ((n : Int) + 2) / 2 = (n : Int) / 2 + 1 := by lia
    by_cases Even n <;> simp_all [Int.negOnePow_add]
  | neg_add_one n ih1 ih2 =>
    have : (-(n : Int) + 1) / 2 = (-(n : Int) - 1) / 2 + 1 := by lia
    by_cases Even n <;> simp_all [T_sub_one, ← Int.not_even_iff_odd, Int.negOnePow_add]

@[simp]

中文:
定理 T_eval_zero
  条件: (n : 整数)
  证明: by
  induction n using Polynomial.Chebyshev.induct with
  | zero => simp
  | one => simp
  | add_two n ih1 ih2 =>
    have : ((n : Int) + 2) / 2 = (n : Int) / 2 + 1 := by lia
    by_cases Even n <;> simp_all [Int.negOnePow_add]
  | neg_add_one n ih1 ih2 =>
    have : (-(n : Int) + 1) / 2 = (-(n : Int) - 1) / 2 + 1 := by lia
    by_cases Even n <;> simp_all [T_sub_one, ← Int.not_even_iff_odd, Int.negOnePow_add]

@[simp]

Depends on / 依赖: Chebyshev, Int.negOnePow_add, Int.not_even_iff_odd, Polynomial, Polynomial.Chebyshev.induct, T_sub_one, add_two, induct, negOnePow_add, neg_add_one, not_even_iff_odd
-/
theorem T_eval_zero (n : Int) :
    (T R n).eval 0 = (if Even n then (n / 2).negOnePow else 0 : Int) := by
  induction n using Polynomial.Chebyshev.induct with
  | zero => simp
  | one => simp
  | add_two n ih1 ih2 =>
    have : ((n : Int) + 2) / 2 = (n : Int) / 2 + 1 := by lia
    by_cases Even n <;> simp_all [Int.negOnePow_add]
  | neg_add_one n ih1 ih2 =>
    have : (-(n : Int) + 1) / 2 = (-(n : Int) - 1) / 2 + 1 := by lia
    by_cases Even n <;> simp_all [T_sub_one, ← Int.not_even_iff_odd, Int.negOnePow_add]

@[simp]
/--
theorem `T_eval_zero_of_even` / 定理 `T_eval_zero_of_even`

English:
theorem T_eval_zero_of_even
  given: {n : Int} (hn : Even n)
  statement: (T R n).eval 0 = (n / 2).negOnePow
  proof: by
  simp [T_eval_zero, hn]

中文:
定理 T_eval_zero_of_even
  条件: {n : 整数} (hn : Even n)
  结论: (T R n).eval 0 = (n / 2).negOnePow
  证明: by
  simp [T_eval_zero, hn]

Depends on / 依赖: T_eval_zero
-/
theorem T_eval_zero_of_even {n : Int} (hn : Even n) : (T R n).eval 0 = (n / 2).negOnePow := by
  simp [T_eval_zero, hn]

/--
theorem `T_eval_two_mul_zero` / 定理 `T_eval_two_mul_zero`

English:
theorem T_eval_two_mul_zero
  given: (n : Int)
  statement: (T R (2 * n)).eval 0 = n.negOnePow
  proof: by simp

@[simp]

中文:
定理 T_eval_two_mul_zero
  条件: (n : 整数)
  结论: (T R (2 * n)).eval 0 = n.negOnePow
  证明: by simp

@[simp]
-/
theorem T_eval_two_mul_zero (n : Int) : (T R (2 * n)).eval 0 = n.negOnePow := by simp

@[simp]
/--
theorem `T_eval_zero_of_odd` / 定理 `T_eval_zero_of_odd`

English:
theorem T_eval_zero_of_odd
  given: {n : Int} (hn : Odd n)
  statement: (T R n).eval 0 = 0
  proof: by
  simp [T_eval_zero, ← Int.not_odd_iff_even, hn]

@[simp]

中文:
定理 T_eval_zero_of_odd
  条件: {n : 整数} (hn : Odd n)
  结论: (T R n).eval 0 = 0
  证明: by
  simp [T_eval_zero, ← Int.not_odd_iff_even, hn]

@[simp]

Depends on / 依赖: Int.not_odd_iff_even, T_eval_zero, not_odd_iff_even
-/
theorem T_eval_zero_of_odd {n : Int} (hn : Odd n) : (T R n).eval 0 = 0 := by
  simp [T_eval_zero, ← Int.not_odd_iff_even, hn]

@[simp]
/--
theorem `degree_T` / 定理 `degree_T`

English:
theorem degree_T
  given: [IsDomain R] [NeZero (2 : R)] (n : Int)
  statement: (T R n).degree = n.natAbs
  proof: by
  induction n using Chebyshev.induct' with
  | zero => simp
  | one => simp
  | add_two n ih1 ih2 =>
    have : (2 * X * T R (n + 1)).degree = ↑(n + 2) := by
      rw [mul_assoc]; rw [← C_ofNat]; rw [degree_C_mul two_ne_zero]; rw [mul_comm]; rw [degree_mul_X]; rw [ih1]
      norm_cast
    rw [T_add_two]; rw [degree_sub_eq_left_of_degree_lt]
    · rw [this]; norm_cast
    · rw [ih2, this]; tauto
  | neg n ih => simp [ih]

@[simp]

中文:
定理 degree_T
  条件: [是整环 R] [NeZero (2 : R)] (n : 整数)
  结论: (T R n).degree = n.natAbs
  证明: by
  induction n using Chebyshev.induct' with
  | zero => simp
  | one => simp
  | add_two n ih1 ih2 =>
    have : (2 * X * T R (n + 1)).degree = ↑(n + 2) := by
      rw [mul_assoc]; rw [← C_ofNat]; rw [degree_C_mul two_ne_zero]; rw [mul_comm]; rw [degree_mul_X]; rw [ih1]
      norm_cast
    rw [T_add_two]; rw [degree_sub_eq_left_of_degree_lt]
    · rw [this]; norm_cast
    · rw [ih2, this]; tauto
  | neg n ih => simp [ih]

@[simp]

Depends on / 依赖: C_ofNat, Chebyshev, Chebyshev.induct, T_add_two, add_two, degree, degree_C_mul, degree_mul_X, degree_sub_eq_left_of_degree_lt, induct, mul_assoc, mul_comm, two_ne_zero
-/
theorem degree_T [IsDomain R] [NeZero (2 : R)] (n : Int) : (T R n).degree = n.natAbs := by
  induction n using Chebyshev.induct' with
  | zero => simp
  | one => simp
  | add_two n ih1 ih2 =>
    have : (2 * X * T R (n + 1)).degree = ↑(n + 2) := by
      rw [mul_assoc]; rw [← C_ofNat]; rw [degree_C_mul two_ne_zero]; rw [mul_comm]; rw [degree_mul_X]; rw [ih1]
      norm_cast
    rw [T_add_two]; rw [degree_sub_eq_left_of_degree_lt]
    · rw [this]; norm_cast
    · rw [ih2, this]; tauto
  | neg n ih => simp [ih]

@[simp]
/--
theorem `natDegree_T` / 定理 `natDegree_T`

English:
theorem natDegree_T
  given: [IsDomain R] [NeZero (2 : R)] (n : Int)
  statement: (T R n).natDegree = n.natAbs
  proof: natDegree_eq_of_degree_eq_some (degree_T R n)

@[simp]

中文:
定理 natDegree_T
  条件: [是整环 R] [NeZero (2 : R)] (n : 整数)
  结论: (T R n).natDegree = n.natAbs
  证明: natDegree_eq_of_degree_eq_some (degree_T R n)

@[simp]

Depends on / 依赖: degree_T, natDegree_eq_of_degree_eq_some
-/
theorem natDegree_T [IsDomain R] [NeZero (2 : R)] (n : Int) : (T R n).natDegree = n.natAbs :=
  natDegree_eq_of_degree_eq_some (degree_T R n)

@[simp]
/--
theorem `leadingCoeff_T` / 定理 `leadingCoeff_T`

English:
theorem leadingCoeff_T
  given: [IsDomain R] [NeZero (2 : R)] (n : Int)
  proof: by
  induction n using Chebyshev.induct' with
  | zero => simp
  | one => simp
  | add_two n ih1 ih2 =>
    have : leadingCoeff (2 : R[X]) = 2 := by
      change leadingCoeff (C 2) = 2
      rw [leadingCoeff_C]
    rw [T_add_two]; rw [leadingCoeff_sub_of_degree_lt]; rw [leadingCoeff_mul]; rw [ih1]; rw [leadingCoeff_mul]; rw [leadingCoeff_X]; rw [this]
    · norm_cast; simp [pow_add, mul_comm]
    · rw [mul_assoc, ← C_ofNat, degree_C_mul two_ne_zero, mul_comm, degree_mul_X, degree_T,
        degree_T]
      tauto
  | neg n ih => simp [ih]

@[simp]

中文:
定理 leadingCoeff_T
  条件: [是整环 R] [NeZero (2 : R)] (n : 整数)
  证明: by
  induction n using Chebyshev.induct' with
  | zero => simp
  | one => simp
  | add_two n ih1 ih2 =>
    have : leadingCoeff (2 : R[X]) = 2 := by
      change leadingCoeff (C 2) = 2
      rw [leadingCoeff_C]
    rw [T_add_two]; rw [leadingCoeff_sub_of_degree_lt]; rw [leadingCoeff_mul]; rw [ih1]; rw [leadingCoeff_mul]; rw [leadingCoeff_X]; rw [this]
    · norm_cast; simp [pow_add, mul_comm]
    · rw [mul_assoc, ← C_ofNat, degree_C_mul two_ne_zero, mul_comm, degree_mul_X, degree_T,
        degree_T]
      tauto
  | neg n ih => simp [ih]

@[simp]

Depends on / 依赖: C_ofNat, Chebyshev, Chebyshev.induct, T_add_two, add_two, degree_C_mul, degree_T, degree_mul_X, induct, leadingCoeff, leadingCoeff_C, leadingCoeff_X, leadingCoeff_mul, leadingCoeff_sub_of_degree_lt, mul_assoc, mul_comm, pow_add, two_ne_zero
-/
theorem leadingCoeff_T [IsDomain R] [NeZero (2 : R)] (n : Int) :
    (T R n).leadingCoeff = 2 ^ (n.natAbs - 1) := by
  induction n using Chebyshev.induct' with
  | zero => simp
  | one => simp
  | add_two n ih1 ih2 =>
    have : leadingCoeff (2 : R[X]) = 2 := by
      change leadingCoeff (C 2) = 2
      rw [leadingCoeff_C]
    rw [T_add_two]; rw [leadingCoeff_sub_of_degree_lt]; rw [leadingCoeff_mul]; rw [ih1]; rw [leadingCoeff_mul]; rw [leadingCoeff_X]; rw [this]
    · norm_cast; simp [pow_add, mul_comm]
    · rw [mul_assoc, ← C_ofNat, degree_C_mul two_ne_zero, mul_comm, degree_mul_X, degree_T,
        degree_T]
      tauto
  | neg n ih => simp [ih]

@[simp]
/--
theorem `T_eval_neg` / 定理 `T_eval_neg`

English:
theorem T_eval_neg
  given: (n : Int) (x : R)
  statement: (T R n).eval (-x) = n.negOnePow * (T R n).eval x
  proof: by
  induction n using Chebyshev.induct' with
  | zero => simp
  | one => simp
  | add_two n ih1 ih2 =>
    trans (n + 2 : Int).negOnePow * (2 * x * (T R (n + 1)).eval x - (T R n).eval x)
    · simp only [T_add_two, eval_sub, eval_mul, eval_ofNat, eval_X, mul_neg, ih1, Int.negOnePow_add,
        Int.negOnePow_one, Units.val_neg, Int.cast_neg, ih2, Int.negOnePow_even 2 even_two]
      ring_nf
    · simp
  | neg n ih => simp [ih]

中文:
定理 T_eval_neg
  条件: (n : 整数) (x : R)
  结论: (T R n).eval (-x) = n.negOnePow * (T R n).eval x
  证明: by
  induction n using Chebyshev.induct' with
  | zero => simp
  | one => simp
  | add_two n ih1 ih2 =>
    trans (n + 2 : Int).negOnePow * (2 * x * (T R (n + 1)).eval x - (T R n).eval x)
    · simp only [T_add_two, eval_sub, eval_mul, eval_ofNat, eval_X, mul_neg, ih1, Int.negOnePow_add,
        Int.negOnePow_one, Units.val_neg, Int.cast_neg, ih2, Int.negOnePow_even 2 even_two]
      ring_nf
    · simp
  | neg n ih => simp [ih]

Depends on / 依赖: Chebyshev, Chebyshev.induct, Int.cast_neg, Int.negOnePow_add, Int.negOnePow_even, Int.negOnePow_one, T_add_two, Units.val_neg, add_two, cast_neg, eval_X, eval_mul, eval_ofNat, eval_sub, even_two, induct, mul_neg, negOnePow, negOnePow_add, negOnePow_even
-/
theorem T_eval_neg (n : Int) (x : R) : (T R n).eval (-x) = n.negOnePow * (T R n).eval x := by
  induction n using Chebyshev.induct' with
  | zero => simp
  | one => simp
  | add_two n ih1 ih2 =>
    trans (n + 2 : Int).negOnePow * (2 * x * (T R (n + 1)).eval x - (T R n).eval x)
    · simp only [T_add_two, eval_sub, eval_mul, eval_ofNat, eval_X, mul_neg, ih1, Int.negOnePow_add,
        Int.negOnePow_one, Units.val_neg, Int.cast_neg, ih2, Int.negOnePow_even 2 even_two]
      ring_nf
    · simp
  | neg n ih => simp [ih]

/--
theorem `T_ne_zero` / 定理 `T_ne_zero`

English:
theorem T_ne_zero
  given: (n : Int) [IsDomain R] [NeZero (2 : R)]
  statement: T R n != 0
  proof: (T R n).degree_ne_bot.mp (by simp [degree_T R n])

中文:
定理 T_ne_zero
  条件: (n : 整数) [是整环 R] [NeZero (2 : R)]
  结论: T R n != 0
  证明: (T R n).degree_ne_bot.mp (by simp [degree_T R n])

Depends on / 依赖: degree_T, degree_ne_bot, degree_ne_bot.mp
-/
theorem T_ne_zero (n : Int) [IsDomain R] [NeZero (2 : R)] : T R n != 0 :=
  (T R n).degree_ne_bot.mp (by simp [degree_T R n])

/--
Definition of `chebyshevTsequence` / `chebyshevTsequence` 的定义

English:
definition chebyshevTsequence
  signature: [IsDomain R] [NeZero (2 : R)]
  body: T R n
  degree_eq' n := by simp [degree_T]

中文:
定义 chebyshevTsequence
  签名: [是整环 R] [NeZero (2 : R)]
  定义体: T R n
  degree_eq' n := by simp [degree_T]
-/
noncomputable def chebyshevTsequence [IsDomain R] [NeZero (2 : R)] : Polynomial.Sequence R where
  elems' n := T R n
  degree_eq' n := by simp [degree_T]

/--
Definition of `U` / `U` 的定义

English:
definition U
  signature: : Int -> R[X]

中文:
定义 U
  签名: : 整数 -> R[X]
-/
noncomputable def U : Int -> R[X]
  | 0 => 1
  | 1 => 2 * X
  | (n : Nat) + 2 => 2 * X * U (n + 1) - U n
  | -((n : Nat) + 1) => 2 * X * U (-n) - U (-n + 1)
  termination_by n => Int.natAbs n + Int.natAbs (n - 1)

@[simp]
/--
theorem `U_add_two` / 定理 `U_add_two`

English:
theorem U_add_two
  statement: forall n, U R (n + 2) = 2 * X * U R (n + 1) - U R n

中文:
定理 U_add_two
  结论: 对任意 n, U R (n + 2) = 2 * X * U R (n + 1) - U R n

Depends on / 依赖: Int.negSucc_eq, U.eq_4, eq_4, negSucc_eq, ring_nf
-/
theorem U_add_two : forall n, U R (n + 2) = 2 * X * U R (n + 1) - U R n
  | (k : Nat) => U.eq_3 R k
  | -(k + 1 : Nat) => by linear_combination (norm := (simp [Int.negSucc_eq]; ring_nf)) U.eq_4 R k

/--
theorem `U_add_one` / 定理 `U_add_one`

English:
theorem U_add_one
  given: (n : Int)
  statement: U R (n + 1) = 2 * X * U R n - U R (n - 1)
  proof: by
  linear_combination (norm := ring_nf) U_add_two R (n - 1)

中文:
定理 U_add_one
  条件: (n : 整数)
  结论: U R (n + 1) = 2 * X * U R n - U R (n - 1)
  证明: by
  linear_combination (norm := ring_nf) U_add_two R (n - 1)

Depends on / 依赖: U_add_two, linear_combination, ring_nf
-/
theorem U_add_one (n : Int) : U R (n + 1) = 2 * X * U R n - U R (n - 1) := by
  linear_combination (norm := ring_nf) U_add_two R (n - 1)

/--
theorem `U_sub_two` / 定理 `U_sub_two`

English:
theorem U_sub_two
  given: (n : Int)
  statement: U R (n - 2) = 2 * X * U R (n - 1) - U R n
  proof: by
  linear_combination (norm := ring_nf) U_add_two R (n - 2)

中文:
定理 U_sub_two
  条件: (n : 整数)
  结论: U R (n - 2) = 2 * X * U R (n - 1) - U R n
  证明: by
  linear_combination (norm := ring_nf) U_add_two R (n - 2)

Depends on / 依赖: U_add_two, linear_combination, ring_nf
-/
theorem U_sub_two (n : Int) : U R (n - 2) = 2 * X * U R (n - 1) - U R n := by
  linear_combination (norm := ring_nf) U_add_two R (n - 2)

/--
theorem `U_sub_one` / 定理 `U_sub_one`

English:
theorem U_sub_one
  given: (n : Int)
  statement: U R (n - 1) = 2 * X * U R n - U R (n + 1)
  proof: by
  linear_combination (norm := ring_nf) U_add_two R (n - 1)

中文:
定理 U_sub_one
  条件: (n : 整数)
  结论: U R (n - 1) = 2 * X * U R n - U R (n + 1)
  证明: by
  linear_combination (norm := ring_nf) U_add_two R (n - 1)

Depends on / 依赖: U_add_two, linear_combination, ring_nf
-/
theorem U_sub_one (n : Int) : U R (n - 1) = 2 * X * U R n - U R (n + 1) := by
  linear_combination (norm := ring_nf) U_add_two R (n - 1)

/--
theorem `U_eq` / 定理 `U_eq`

English:
theorem U_eq
  given: (n : Int)
  statement: U R n = 2 * X * U R (n - 1) - U R (n - 2)
  proof: by
  linear_combination (norm := ring_nf) U_add_two R (n - 2)

@[simp]

中文:
定理 U_eq
  条件: (n : 整数)
  结论: U R n = 2 * X * U R (n - 1) - U R (n - 2)
  证明: by
  linear_combination (norm := ring_nf) U_add_two R (n - 2)

@[simp]

Depends on / 依赖: U_add_two, linear_combination, ring_nf
-/
theorem U_eq (n : Int) : U R n = 2 * X * U R (n - 1) - U R (n - 2) := by
  linear_combination (norm := ring_nf) U_add_two R (n - 2)

@[simp]
/--
theorem `U_zero` / 定理 `U_zero`

English:
theorem U_zero
  statement: U R 0 = 1
  proof: by simp [U]

@[simp]

中文:
定理 U_zero
  结论: U R 0 = 1
  证明: by simp [U]

@[simp]
-/
theorem U_zero : U R 0 = 1 := by simp [U]

@[simp]
/--
theorem `U_one` / 定理 `U_one`

English:
theorem U_one
  statement: U R 1 = 2 * X
  proof: by simp [U]

@[simp]

中文:
定理 U_one
  结论: U R 1 = 2 * X
  证明: by simp [U]

@[simp]
-/
theorem U_one : U R 1 = 2 * X := by simp [U]

@[simp]
/--
theorem `U_neg_one` / 定理 `U_neg_one`

English:
theorem U_neg_one
  statement: U R (-1) = 0
  proof: by simpa using U_sub_one R 0

中文:
定理 U_neg_one
  结论: U R (-1) = 0
  证明: by simpa using U_sub_one R 0

Depends on / 依赖: U_sub_one
-/
theorem U_neg_one : U R (-1) = 0 := by simpa using U_sub_one R 0

/--
theorem `U_two` / 定理 `U_two`

English:
theorem U_two
  statement: U R 2 = 4 * X ^ 2 - 1
  proof: by
  have := U_add_two R 0
  simp only [zero_add, U_one, U_zero] at this
  linear_combination this

@[simp]

中文:
定理 U_two
  结论: U R 2 = 4 * X ^ 2 - 1
  证明: by
  have := U_add_two R 0
  simp only [zero_add, U_one, U_zero] at this
  linear_combination this

@[simp]

Depends on / 依赖: U_add_two, U_one, U_zero, linear_combination, zero_add
-/
theorem U_two : U R 2 = 4 * X ^ 2 - 1 := by
  have := U_add_two R 0
  simp only [zero_add, U_one, U_zero] at this
  linear_combination this

@[simp]
/--
theorem `U_neg_two` / 定理 `U_neg_two`

English:
theorem U_neg_two
  statement: U R (-2) = -1
  proof: by
  simpa [zero_sub, Int.reduceNeg, U_neg_one, mul_zero, U_zero] using U_sub_two R 0

中文:
定理 U_neg_two
  结论: U R (-2) = -1
  证明: by
  simpa [zero_sub, Int.reduceNeg, U_neg_one, mul_zero, U_zero] using U_sub_two R 0

Depends on / 依赖: Int.reduceNeg, U_neg_one, U_sub_two, U_zero, mul_zero, reduceNeg, zero_sub
-/
theorem U_neg_two : U R (-2) = -1 := by
  simpa [zero_sub, Int.reduceNeg, U_neg_one, mul_zero, U_zero] using U_sub_two R 0

/--
theorem `U_neg_sub_one` / 定理 `U_neg_sub_one`

English:
theorem U_neg_sub_one
  given: (n : Int)
  statement: U R (-n - 1) = -U R (n - 1)
  proof: by
  induction n using Polynomial.Chebyshev.induct with
  | zero => simp
  | one => simp
  | add_two n ih1 ih2 =>
    have h₁ := U_add_one R n
    have h₂ := U_sub_two R (-n - 1)
    linear_combination (norm := ring_nf) 2 * (X : R[X]) * ih1 - ih2 + h₁ + h₂
  | neg_add_one n ih1 ih2 =>
    have h₁ := U_eq R n
    have h₂ := U_sub_two R (-n)
    linear_combination (norm := ring_nf) 2 * (X : R[X]) * ih1 - ih2 + h₁ + h₂

中文:
定理 U_neg_sub_one
  条件: (n : 整数)
  结论: U R (-n - 1) = -U R (n - 1)
  证明: by
  induction n using Polynomial.Chebyshev.induct with
  | zero => simp
  | one => simp
  | add_two n ih1 ih2 =>
    have h₁ := U_add_one R n
    have h₂ := U_sub_two R (-n - 1)
    linear_combination (norm := ring_nf) 2 * (X : R[X]) * ih1 - ih2 + h₁ + h₂
  | neg_add_one n ih1 ih2 =>
    have h₁ := U_eq R n
    have h₂ := U_sub_two R (-n)
    linear_combination (norm := ring_nf) 2 * (X : R[X]) * ih1 - ih2 + h₁ + h₂

Depends on / 依赖: Chebyshev, Polynomial, Polynomial.Chebyshev.induct, U_add_one, U_eq, U_sub_two, add_two, induct, linear_combination, neg_add_one, ring_nf
-/
theorem U_neg_sub_one (n : Int) : U R (-n - 1) = -U R (n - 1) := by
  induction n using Polynomial.Chebyshev.induct with
  | zero => simp
  | one => simp
  | add_two n ih1 ih2 =>
    have h₁ := U_add_one R n
    have h₂ := U_sub_two R (-n - 1)
    linear_combination (norm := ring_nf) 2 * (X : R[X]) * ih1 - ih2 + h₁ + h₂
  | neg_add_one n ih1 ih2 =>
    have h₁ := U_eq R n
    have h₂ := U_sub_two R (-n)
    linear_combination (norm := ring_nf) 2 * (X : R[X]) * ih1 - ih2 + h₁ + h₂

/--
theorem `U_neg` / 定理 `U_neg`

English:
theorem U_neg
  given: (n : Int)
  statement: U R (-n) = -U R (n - 2)
  proof: by simpa [sub_sub] using U_neg_sub_one R (n - 1)

@[simp]

中文:
定理 U_neg
  条件: (n : 整数)
  结论: U R (-n) = -U R (n - 2)
  证明: by simpa [sub_sub] using U_neg_sub_one R (n - 1)

@[simp]

Depends on / 依赖: U_neg_sub_one, sub_sub
-/
theorem U_neg (n : Int) : U R (-n) = -U R (n - 2) := by simpa [sub_sub] using U_neg_sub_one R (n - 1)

@[simp]
/--
theorem `U_neg_sub_two` / 定理 `U_neg_sub_two`

English:
theorem U_neg_sub_two
  given: (n : Int)
  statement: U R (-n - 2) = -U R n
  proof: by
  simpa [sub_eq_add_neg, add_comm] using U_neg R (n + 2)

@[simp]

中文:
定理 U_neg_sub_two
  条件: (n : 整数)
  结论: U R (-n - 2) = -U R n
  证明: by
  simpa [sub_eq_add_neg, add_comm] using U_neg R (n + 2)

@[simp]

Depends on / 依赖: U_neg, add_comm, sub_eq_add_neg
-/
theorem U_neg_sub_two (n : Int) : U R (-n - 2) = -U R n := by
  simpa [sub_eq_add_neg, add_comm] using U_neg R (n + 2)

@[simp]
/--
theorem `U_eval_one` / 定理 `U_eval_one`

English:
theorem U_eval_one
  given: (n : Int)
  statement: (U R n).eval 1 = n + 1
  proof: by
  induction n using Polynomial.Chebyshev.induct with
  | zero => simp
  | one => simp; norm_num
  | add_two n ih1 ih2 =>
    simp only [U_add_two, eval_sub, eval_mul, eval_ofNat, eval_X, mul_one, ih1,
      Int.cast_add, Int.cast_natCast, Int.cast_one, ih2, Int.cast_ofNat]
    ring
  | neg_add_one n ih1 ih2 =>
    simp only [U_sub_one, eval_sub, eval_mul, eval_ofNat, eval_X, mul_one,
      ih1, Int.cast_neg, Int.cast_natCast, ih2, Int.cast_add, Int.cast_one, Int.cast_sub,
      sub_add_cancel]
    ring

中文:
定理 U_eval_one
  条件: (n : 整数)
  结论: (U R n).eval 1 = n + 1
  证明: by
  induction n using Polynomial.Chebyshev.induct with
  | zero => simp
  | one => simp; norm_num
  | add_two n ih1 ih2 =>
    simp only [U_add_two, eval_sub, eval_mul, eval_ofNat, eval_X, mul_one, ih1,
      Int.cast_add, Int.cast_natCast, Int.cast_one, ih2, Int.cast_ofNat]
    ring
  | neg_add_one n ih1 ih2 =>
    simp only [U_sub_one, eval_sub, eval_mul, eval_ofNat, eval_X, mul_one,
      ih1, Int.cast_neg, Int.cast_natCast, ih2, Int.cast_add, Int.cast_one, Int.cast_sub,
      sub_add_cancel]
    ring

Depends on / 依赖: Chebyshev, Int.cast_add, Int.cast_natCast, Int.cast_neg, Int.cast_ofNat, Int.cast_one, Int.cast_sub, Polynomial, Polynomial.Chebyshev.induct, U_add_two, U_sub_one, add_two, cast_add, cast_natCast, cast_neg, cast_ofNat, cast_one, cast_sub, eval_X, eval_mul
-/
theorem U_eval_one (n : Int) : (U R n).eval 1 = n + 1 := by
  induction n using Polynomial.Chebyshev.induct with
  | zero => simp
  | one => simp; norm_num
  | add_two n ih1 ih2 =>
    simp only [U_add_two, eval_sub, eval_mul, eval_ofNat, eval_X, mul_one, ih1,
      Int.cast_add, Int.cast_natCast, Int.cast_one, ih2, Int.cast_ofNat]
    ring
  | neg_add_one n ih1 ih2 =>
    simp only [U_sub_one, eval_sub, eval_mul, eval_ofNat, eval_X, mul_one,
      ih1, Int.cast_neg, Int.cast_natCast, ih2, Int.cast_add, Int.cast_one, Int.cast_sub,
      sub_add_cancel]
    ring

set_option backward.isDefEq.respectTransparency false in
/--
theorem `U_eval_neg_one` / 定理 `U_eval_neg_one`

English:
theorem U_eval_neg_one
  given: (n : Int)
  statement: (U R n).eval (-1) = n.negOnePow * (n + 1)
  proof: by
  induction n using Polynomial.Chebyshev.induct with
  | zero => simp
  | one => simp; norm_num
  | add_two n ih1 ih2 =>
    simp only [U_add_two, eval_sub, eval_mul, eval_ofNat, eval_X, mul_neg, mul_one, ih1,
      Int.cast_add, Int.cast_natCast, Int.cast_one, neg_mul, ih2, Int.cast_ofNat, Int.negOnePow_add,
      Int.negOnePow_def 2]
    norm_cast
    norm_num
    ring
  | neg_add_one n ih1 ih2 =>
    simp only [U_sub_one, eval_sub, eval_mul, eval_ofNat, eval_X, mul_neg, mul_one, ih1,
      Int.cast_neg, Int.cast_natCast, Int.negOnePow_neg, neg_mul, ih2, Int.cast_add, Int.cast_one,
      Int.cast_sub, sub_add_cancel, Int.negOnePow_sub, Int.negOnePow_add]
    norm_cast
    norm_num
    ring

中文:
定理 U_eval_neg_one
  条件: (n : 整数)
  结论: (U R n).eval (-1) = n.negOnePow * (n + 1)
  证明: by
  induction n using Polynomial.Chebyshev.induct with
  | zero => simp
  | one => simp; norm_num
  | add_two n ih1 ih2 =>
    simp only [U_add_two, eval_sub, eval_mul, eval_ofNat, eval_X, mul_neg, mul_one, ih1,
      Int.cast_add, Int.cast_natCast, Int.cast_one, neg_mul, ih2, Int.cast_ofNat, Int.negOnePow_add,
      Int.negOnePow_def 2]
    norm_cast
    norm_num
    ring
  | neg_add_one n ih1 ih2 =>
    simp only [U_sub_one, eval_sub, eval_mul, eval_ofNat, eval_X, mul_neg, mul_one, ih1,
      Int.cast_neg, Int.cast_natCast, Int.negOnePow_neg, neg_mul, ih2, Int.cast_add, Int.cast_one,
      Int.cast_sub, sub_add_cancel, Int.negOnePow_sub, Int.negOnePow_add]
    norm_cast
    norm_num
    ring

Depends on / 依赖: Chebyshev, Int.cast_add, Int.cast_natCast, Int.cast_neg, Int.cast_ofNat, Int.cast_one, Int.negOnePow_add, Int.negOnePow_def, Int.negOnePow_n, Polynomial, Polynomial.Chebyshev.induct, U_add_two, U_sub_one, add_two, cast_add, cast_natCast, cast_neg, cast_ofNat, cast_one, eval_X
-/
theorem U_eval_neg_one (n : Int) : (U R n).eval (-1) = n.negOnePow * (n + 1) := by
  induction n using Polynomial.Chebyshev.induct with
  | zero => simp
  | one => simp; norm_num
  | add_two n ih1 ih2 =>
    simp only [U_add_two, eval_sub, eval_mul, eval_ofNat, eval_X, mul_neg, mul_one, ih1,
      Int.cast_add, Int.cast_natCast, Int.cast_one, neg_mul, ih2, Int.cast_ofNat, Int.negOnePow_add,
      Int.negOnePow_def 2]
    norm_cast
    norm_num
    ring
  | neg_add_one n ih1 ih2 =>
    simp only [U_sub_one, eval_sub, eval_mul, eval_ofNat, eval_X, mul_neg, mul_one, ih1,
      Int.cast_neg, Int.cast_natCast, Int.negOnePow_neg, neg_mul, ih2, Int.cast_add, Int.cast_one,
      Int.cast_sub, sub_add_cancel, Int.negOnePow_sub, Int.negOnePow_add]
    norm_cast
    norm_num
    ring

/--
theorem `U_eval_zero` / 定理 `U_eval_zero`

English:
theorem U_eval_zero
  given: (n : Int)
  proof: by
  induction n using Polynomial.Chebyshev.induct with
  | zero => simp
  | one => simp
  | add_two n ih1 ih2 =>
    have : ((n : Int) + 2) / 2 = (n : Int) / 2 + 1 := by lia
    by_cases Even n <;> simp_all [Int.negOnePow_add]
  | neg_add_one n ih1 ih2 =>
    have : (-(n : Int) + 1) / 2 = (-(n : Int) - 1) / 2 + 1 := by lia
    by_cases Even n <;> simp_all [U_sub_one, ← Int.not_even_iff_odd, Int.negOnePow_add]

@[simp]

中文:
定理 U_eval_zero
  条件: (n : 整数)
  证明: by
  induction n using Polynomial.Chebyshev.induct with
  | zero => simp
  | one => simp
  | add_two n ih1 ih2 =>
    have : ((n : Int) + 2) / 2 = (n : Int) / 2 + 1 := by lia
    by_cases Even n <;> simp_all [Int.negOnePow_add]
  | neg_add_one n ih1 ih2 =>
    have : (-(n : Int) + 1) / 2 = (-(n : Int) - 1) / 2 + 1 := by lia
    by_cases Even n <;> simp_all [U_sub_one, ← Int.not_even_iff_odd, Int.negOnePow_add]

@[simp]

Depends on / 依赖: Chebyshev, Int.negOnePow_add, Int.not_even_iff_odd, Polynomial, Polynomial.Chebyshev.induct, U_sub_one, add_two, induct, negOnePow_add, neg_add_one, not_even_iff_odd
-/
theorem U_eval_zero (n : Int) :
    (U R n).eval 0 = (if Even n then (n / 2).negOnePow else 0 : Int) := by
  induction n using Polynomial.Chebyshev.induct with
  | zero => simp
  | one => simp
  | add_two n ih1 ih2 =>
    have : ((n : Int) + 2) / 2 = (n : Int) / 2 + 1 := by lia
    by_cases Even n <;> simp_all [Int.negOnePow_add]
  | neg_add_one n ih1 ih2 =>
    have : (-(n : Int) + 1) / 2 = (-(n : Int) - 1) / 2 + 1 := by lia
    by_cases Even n <;> simp_all [U_sub_one, ← Int.not_even_iff_odd, Int.negOnePow_add]

@[simp]
/--
theorem `U_eval_zero_of_even` / 定理 `U_eval_zero_of_even`

English:
theorem U_eval_zero_of_even
  given: {n : Int} (hn : Even n)
  statement: (U R n).eval 0 = (n / 2).negOnePow
  proof: by
  simp [U_eval_zero, hn]

中文:
定理 U_eval_zero_of_even
  条件: {n : 整数} (hn : Even n)
  结论: (U R n).eval 0 = (n / 2).negOnePow
  证明: by
  simp [U_eval_zero, hn]

Depends on / 依赖: U_eval_zero
-/
theorem U_eval_zero_of_even {n : Int} (hn : Even n) : (U R n).eval 0 = (n / 2).negOnePow := by
  simp [U_eval_zero, hn]

/--
theorem `U_eval_two_mul_zero` / 定理 `U_eval_two_mul_zero`

English:
theorem U_eval_two_mul_zero
  given: (n : Int)
  statement: (U R (2 * n)).eval 0 = n.negOnePow
  proof: by simp

@[simp]

中文:
定理 U_eval_two_mul_zero
  条件: (n : 整数)
  结论: (U R (2 * n)).eval 0 = n.negOnePow
  证明: by simp

@[simp]
-/
theorem U_eval_two_mul_zero (n : Int) : (U R (2 * n)).eval 0 = n.negOnePow := by simp

@[simp]
/--
theorem `U_eval_zero_of_odd` / 定理 `U_eval_zero_of_odd`

English:
theorem U_eval_zero_of_odd
  given: {n : Int} (hn : Odd n)
  statement: (U R n).eval 0 = 0
  proof: by
  simp [U_eval_zero, ← Int.not_odd_iff_even, hn]

@[simp]

中文:
定理 U_eval_zero_of_odd
  条件: {n : 整数} (hn : Odd n)
  结论: (U R n).eval 0 = 0
  证明: by
  simp [U_eval_zero, ← Int.not_odd_iff_even, hn]

@[simp]

Depends on / 依赖: Int.not_odd_iff_even, U_eval_zero, not_odd_iff_even
-/
theorem U_eval_zero_of_odd {n : Int} (hn : Odd n) : (U R n).eval 0 = 0 := by
  simp [U_eval_zero, ← Int.not_odd_iff_even, hn]

@[simp]
/--
theorem `degree_U_natCast` / 定理 `degree_U_natCast`

English:
theorem degree_U_natCast
  given: [IsDomain R] [NeZero (2 : R)] (n : Nat)
  statement: (U R n).degree = n
  proof: by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one =>
    norm_cast
    rw [U_one]; rw [← C_ofNat]; rw [degree_C_mul_X two_ne_zero]
  | more n ih1 ih2 =>
    push_cast; push_cast at ih2
    have : (2 * X * U R (n + 1)).degree = ↑(n + 2) := by
      rw [mul_assoc]; rw [← C_ofNat]; rw [degree_C_mul two_ne_zero]; rw [mul_comm]; rw [degree_mul_X]; rw [ih2]
      norm_cast
    rw [U_add_two]; rw [degree_sub_eq_left_of_degree_lt]
    · rw [this]; norm_cast
    · rw [ih1, this]; norm_cast; omega

@[simp]

中文:
定理 degree_U_natCast
  条件: [是整环 R] [NeZero (2 : R)] (n : 自然数)
  结论: (U R n).degree = n
  证明: by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one =>
    norm_cast
    rw [U_one]; rw [← C_ofNat]; rw [degree_C_mul_X two_ne_zero]
  | more n ih1 ih2 =>
    push_cast; push_cast at ih2
    have : (2 * X * U R (n + 1)).degree = ↑(n + 2) := by
      rw [mul_assoc]; rw [← C_ofNat]; rw [degree_C_mul two_ne_zero]; rw [mul_comm]; rw [degree_mul_X]; rw [ih2]
      norm_cast
    rw [U_add_two]; rw [degree_sub_eq_left_of_degree_lt]
    · rw [this]; norm_cast
    · rw [ih1, this]; norm_cast; omega

@[simp]

Depends on / 依赖: C_ofNat, Nat.twoStepInduction, U_add_two, U_one, degree, degree_C_mul, degree_C_mul_X, degree_mul_X, degree_sub_eq_left_of_degree_lt, mul_assoc, mul_comm, twoStepInduction, two_ne_zero
-/
theorem degree_U_natCast [IsDomain R] [NeZero (2 : R)] (n : Nat) : (U R n).degree = n := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one =>
    norm_cast
    rw [U_one]; rw [← C_ofNat]; rw [degree_C_mul_X two_ne_zero]
  | more n ih1 ih2 =>
    push_cast; push_cast at ih2
    have : (2 * X * U R (n + 1)).degree = ↑(n + 2) := by
      rw [mul_assoc]; rw [← C_ofNat]; rw [degree_C_mul two_ne_zero]; rw [mul_comm]; rw [degree_mul_X]; rw [ih2]
      norm_cast
    rw [U_add_two]; rw [degree_sub_eq_left_of_degree_lt]
    · rw [this]; norm_cast
    · rw [ih1, this]; norm_cast; omega

@[simp]
/--
theorem `natDegree_U_natCast` / 定理 `natDegree_U_natCast`

English:
theorem natDegree_U_natCast
  given: [IsDomain R] [NeZero (2 : R)] (n : Nat)
  statement: (U R n).natDegree = n
  proof: natDegree_eq_of_degree_eq_some (degree_U_natCast R n)

中文:
定理 natDegree_U_natCast
  条件: [是整环 R] [NeZero (2 : R)] (n : 自然数)
  结论: (U R n).natDegree = n
  证明: natDegree_eq_of_degree_eq_some (degree_U_natCast R n)

Depends on / 依赖: degree_U_natCast, natDegree_eq_of_degree_eq_some
-/
theorem natDegree_U_natCast [IsDomain R] [NeZero (2 : R)] (n : Nat) : (U R n).natDegree = n :=
  natDegree_eq_of_degree_eq_some (degree_U_natCast R n)

/--
theorem `degree_U_neg_one` / 定理 `degree_U_neg_one`

English:
theorem degree_U_neg_one
  statement: (U R (-1)).degree = ⊥
  proof: by simp

中文:
定理 degree_U_neg_one
  结论: (U R (-1)).degree = ⊥
  证明: by simp
-/
theorem degree_U_neg_one : (U R (-1)).degree = ⊥ := by simp

/--
theorem `natDegree_U_neg_one` / 定理 `natDegree_U_neg_one`

English:
theorem natDegree_U_neg_one
  statement: (U R (-1)).natDegree = 0
  proof: by simp

中文:
定理 natDegree_U_neg_one
  结论: (U R (-1)).natDegree = 0
  证明: by simp
-/
theorem natDegree_U_neg_one : (U R (-1)).natDegree = 0 := by simp

/--
theorem `degree_U_of_ne_neg_one` / 定理 `degree_U_of_ne_neg_one`

English:
theorem degree_U_of_ne_neg_one
  given: [IsDomain R] [NeZero (2 : R)] (n : Int) (hn : n != -1)
  proof: by
  obtain ⟨m, rfl | rfl⟩ := n.eq_nat_or_neg
  case inl => rw [degree_U_natCast R m]; norm_cast
  case inr =>
    rw [U_neg]; rw [degree_neg]
    cases m with
    | zero => simp
    | succ m =>
      cases m with
      | zero => contradiction
      | succ m =>
        trans (U R m).degree
        · congr; omega
        · rw [degree_U_natCast R m]; norm_cast

中文:
定理 degree_U_of_ne_neg_one
  条件: [是整环 R] [NeZero (2 : R)] (n : 整数) (hn : n != -1)
  证明: by
  obtain ⟨m, rfl | rfl⟩ := n.eq_nat_or_neg
  case inl => rw [degree_U_natCast R m]; norm_cast
  case inr =>
    rw [U_neg]; rw [degree_neg]
    cases m with
    | zero => simp
    | succ m =>
      cases m with
      | zero => contradiction
      | succ m =>
        trans (U R m).degree
        · congr; omega
        · rw [degree_U_natCast R m]; norm_cast

Depends on / 依赖: U_neg, degree, degree_U_natCast, degree_neg, eq_nat_or_neg, n.eq_nat_or_neg
-/
theorem degree_U_of_ne_neg_one [IsDomain R] [NeZero (2 : R)] (n : Int) (hn : n != -1) :
    (U R n).degree = ↑((n + 1).natAbs - 1) := by
  obtain ⟨m, rfl | rfl⟩ := n.eq_nat_or_neg
  case inl => rw [degree_U_natCast R m]; norm_cast
  case inr =>
    rw [U_neg]; rw [degree_neg]
    cases m with
    | zero => simp
    | succ m =>
      cases m with
      | zero => contradiction
      | succ m =>
        trans (U R m).degree
        · congr; omega
        · rw [degree_U_natCast R m]; norm_cast

/--
theorem `natDegree_U` / 定理 `natDegree_U`

English:
theorem natDegree_U
  given: [IsDomain R] [NeZero (2 : R)] (n : Int)
  proof: by
  by_cases n = -1
  case pos hn => subst hn; simp
  case neg hn => exact natDegree_eq_of_degree_eq_some (degree_U_of_ne_neg_one R n hn)

@[simp]

中文:
定理 natDegree_U
  条件: [是整环 R] [NeZero (2 : R)] (n : 整数)
  证明: by
  by_cases n = -1
  case pos hn => subst hn; simp
  case neg hn => exact natDegree_eq_of_degree_eq_some (degree_U_of_ne_neg_one R n hn)

@[simp]

Depends on / 依赖: degree_U_of_ne_neg_one, natDegree_eq_of_degree_eq_some
-/
theorem natDegree_U [IsDomain R] [NeZero (2 : R)] (n : Int) :
    (U R n).natDegree = (n + 1).natAbs - 1 := by
  by_cases n = -1
  case pos hn => subst hn; simp
  case neg hn => exact natDegree_eq_of_degree_eq_some (degree_U_of_ne_neg_one R n hn)

@[simp]
/--
theorem `leadingCoeff_U_natCast` / 定理 `leadingCoeff_U_natCast`

English:
theorem leadingCoeff_U_natCast
  given: [IsDomain R] [NeZero (2 : R)] (n : Nat)
  proof: by
  have : leadingCoeff (2 : R[X]) = 2 := by
    rw [← C_ofNat]; rw [leadingCoeff_C]
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simp [this]
  | more n ih1 ih2 =>
    push_cast; push_cast at ih2
    rw [U_add_two]; rw [leadingCoeff_sub_of_degree_lt]; rw [leadingCoeff_mul]; rw [ih2]; rw [leadingCoeff_mul]; rw [leadingCoeff_X]; rw [this]
    · norm_cast; rw [pow_add, pow_add]; ring_nf
    · norm_cast
      rw [mul_assoc]; rw [← C_ofNat]; rw [degree_C_mul two_ne_zero]; rw [mul_comm]; rw [degree_mul_X]; rw [degree_U_natCast R n]; rw [degree_U_natCast R (n + 1)]
      norm_cast; omega

@[simp]

中文:
定理 leadingCoeff_U_natCast
  条件: [是整环 R] [NeZero (2 : R)] (n : 自然数)
  证明: by
  have : leadingCoeff (2 : R[X]) = 2 := by
    rw [← C_ofNat]; rw [leadingCoeff_C]
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simp [this]
  | more n ih1 ih2 =>
    push_cast; push_cast at ih2
    rw [U_add_two]; rw [leadingCoeff_sub_of_degree_lt]; rw [leadingCoeff_mul]; rw [ih2]; rw [leadingCoeff_mul]; rw [leadingCoeff_X]; rw [this]
    · norm_cast; rw [pow_add, pow_add]; ring_nf
    · norm_cast
      rw [mul_assoc]; rw [← C_ofNat]; rw [degree_C_mul two_ne_zero]; rw [mul_comm]; rw [degree_mul_X]; rw [degree_U_natCast R n]; rw [degree_U_natCast R (n + 1)]
      norm_cast; omega

@[simp]

Depends on / 依赖: C_ofNat, Nat.twoStepInduction, U_add_two, degree_C_mul, degree_mul_X, leadingCoeff, leadingCoeff_C, leadingCoeff_X, leadingCoeff_mul, leadingCoeff_sub_of_degree_lt, mul_assoc, mul_comm, pow_add, ring_nf, twoStepInduction, two_ne_zero
-/
theorem leadingCoeff_U_natCast [IsDomain R] [NeZero (2 : R)] (n : Nat) :
    (U R n).leadingCoeff = 2 ^ n := by
  have : leadingCoeff (2 : R[X]) = 2 := by
    rw [← C_ofNat]; rw [leadingCoeff_C]
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simp [this]
  | more n ih1 ih2 =>
    push_cast; push_cast at ih2
    rw [U_add_two]; rw [leadingCoeff_sub_of_degree_lt]; rw [leadingCoeff_mul]; rw [ih2]; rw [leadingCoeff_mul]; rw [leadingCoeff_X]; rw [this]
    · norm_cast; rw [pow_add, pow_add]; ring_nf
    · norm_cast
      rw [mul_assoc]; rw [← C_ofNat]; rw [degree_C_mul two_ne_zero]; rw [mul_comm]; rw [degree_mul_X]; rw [degree_U_natCast R n]; rw [degree_U_natCast R (n + 1)]
      norm_cast; omega

@[simp]
/--
theorem `U_eval_neg` / 定理 `U_eval_neg`

English:
theorem U_eval_neg
  given: (n : Nat) (x : R)
  statement: (U R n).eval (-x) = (n : Int).negOnePow * (U R n).eval x
  proof: by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simp
  | more n ih1 ih2 =>
    trans (n + 2 : Int).negOnePow * (2 * x * (U R (n + 1)).eval x - (U R n).eval x)
    · push_cast; push_cast at ih2
      rw [U_add_two]; rw [eval_sub]; rw [eval_mul]; rw [eval_mul]; rw [ih1]; rw [ih2]; rw [Int.negOnePow_succ]; rw [Int.negOnePow_add]; rw [Int.negOnePow_even 2 even_two]
      simp; ring
    · simp

中文:
定理 U_eval_neg
  条件: (n : 自然数) (x : R)
  结论: (U R n).eval (-x) = (n : 整数).negOnePow * (U R n).eval x
  证明: by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simp
  | more n ih1 ih2 =>
    trans (n + 2 : Int).negOnePow * (2 * x * (U R (n + 1)).eval x - (U R n).eval x)
    · push_cast; push_cast at ih2
      rw [U_add_two]; rw [eval_sub]; rw [eval_mul]; rw [eval_mul]; rw [ih1]; rw [ih2]; rw [Int.negOnePow_succ]; rw [Int.negOnePow_add]; rw [Int.negOnePow_even 2 even_two]
      simp; ring
    · simp

Depends on / 依赖: Int.negOnePow_add, Int.negOnePow_even, Int.negOnePow_succ, Nat.twoStepInduction, U_add_two, eval_mul, eval_sub, even_two, negOnePow, negOnePow_add, negOnePow_even, negOnePow_succ, twoStepInduction
-/
theorem U_eval_neg (n : Nat) (x : R) : (U R n).eval (-x) = (n : Int).negOnePow * (U R n).eval x := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simp
  | more n ih1 ih2 =>
    trans (n + 2 : Int).negOnePow * (2 * x * (U R (n + 1)).eval x - (U R n).eval x)
    · push_cast; push_cast at ih2
      rw [U_add_two]; rw [eval_sub]; rw [eval_mul]; rw [eval_mul]; rw [ih1]; rw [ih2]; rw [Int.negOnePow_succ]; rw [Int.negOnePow_add]; rw [Int.negOnePow_even 2 even_two]
      simp; ring
    · simp

/--
theorem `U_ne_zero` / 定理 `U_ne_zero`

English:
theorem U_ne_zero
  given: (n : Int) [IsDomain R] [NeZero (2 : R)] (hn : n != -1)
  statement: U R n != 0
  proof: (U R n).degree_ne_bot.mp (by simp [degree_U_of_ne_neg_one R n hn])

中文:
定理 U_ne_zero
  条件: (n : 整数) [是整环 R] [NeZero (2 : R)] (hn : n != -1)
  结论: U R n != 0
  证明: (U R n).degree_ne_bot.mp (by simp [degree_U_of_ne_neg_one R n hn])

Depends on / 依赖: degree_U_of_ne_neg_one, degree_ne_bot, degree_ne_bot.mp
-/
theorem U_ne_zero (n : Int) [IsDomain R] [NeZero (2 : R)] (hn : n != -1) : U R n != 0 :=
  (U R n).degree_ne_bot.mp (by simp [degree_U_of_ne_neg_one R n hn])

/--
theorem `U_eq_zero_iff` / 定理 `U_eq_zero_iff`

English:
theorem U_eq_zero_iff
  given: (n : Int) [IsDomain R] [NeZero (2 : R)]
  proof: ⟨fun h => by contrapose! h; exact U_ne_zero R n h, fun h => by simp [h]⟩

中文:
定理 U_eq_zero_iff
  条件: (n : 整数) [是整环 R] [NeZero (2 : R)]
  证明: ⟨fun h => by contrapose! h; exact U_ne_zero R n h, fun h => by simp [h]⟩

Depends on / 依赖: U_ne_zero, contrapose
-/
theorem U_eq_zero_iff (n : Int) [IsDomain R] [NeZero (2 : R)] :
    U R n = 0 ↔ n = -1 :=
  ⟨fun h => by contrapose! h; exact U_ne_zero R n h, fun h => by simp [h]⟩

/--
theorem `U_eq_X_mul_U_add_T` / 定理 `U_eq_X_mul_U_add_T`

English:
theorem U_eq_X_mul_U_add_T
  given: (n : Int)
  statement: U R (n + 1) = X * U R n + T R (n + 1)
  proof: by
  induction n using Polynomial.Chebyshev.induct with
  | zero => simp [two_mul]
  | one => simp [U_two, T_two]; ring
  | add_two n ih1 ih2 =>
    have h₁ := U_add_two R (n + 1)
    have h₂ := U_add_two R n
    have h₃ := T_add_two R (n + 1)
    linear_combination (norm := ring_nf) -h₃ - (X : R[X]) * h₂ + h₁ + 2 * (X : R[X]) * ih1 - ih2
  | neg_add_one n ih1 ih2 =>
    have h₁ := U_add_two R (-n - 1)
    have h₂ := U_add_two R (-n)
    have h₃ := T_add_two R (-n)
    linear_combination (norm := ring_nf) -h₃ + h₂ - (X : R[X]) * h₁ - ih2 + 2 * (X : R[X]) * ih1

中文:
定理 U_eq_X_mul_U_add_T
  条件: (n : 整数)
  结论: U R (n + 1) = X * U R n + T R (n + 1)
  证明: by
  induction n using Polynomial.Chebyshev.induct with
  | zero => simp [two_mul]
  | one => simp [U_two, T_two]; ring
  | add_two n ih1 ih2 =>
    have h₁ := U_add_two R (n + 1)
    have h₂ := U_add_two R n
    have h₃ := T_add_two R (n + 1)
    linear_combination (norm := ring_nf) -h₃ - (X : R[X]) * h₂ + h₁ + 2 * (X : R[X]) * ih1 - ih2
  | neg_add_one n ih1 ih2 =>
    have h₁ := U_add_two R (-n - 1)
    have h₂ := U_add_two R (-n)
    have h₃ := T_add_two R (-n)
    linear_combination (norm := ring_nf) -h₃ + h₂ - (X : R[X]) * h₁ - ih2 + 2 * (X : R[X]) * ih1

Depends on / 依赖: Chebyshev, Polynomial, Polynomial.Chebyshev.induct, T_add_two, T_two, U_add_two, U_two, add_two, induct, linear_combination, neg_add_one, ring_nf, two_mul
-/
theorem U_eq_X_mul_U_add_T (n : Int) : U R (n + 1) = X * U R n + T R (n + 1) := by
  induction n using Polynomial.Chebyshev.induct with
  | zero => simp [two_mul]
  | one => simp [U_two, T_two]; ring
  | add_two n ih1 ih2 =>
    have h₁ := U_add_two R (n + 1)
    have h₂ := U_add_two R n
    have h₃ := T_add_two R (n + 1)
    linear_combination (norm := ring_nf) -h₃ - (X : R[X]) * h₂ + h₁ + 2 * (X : R[X]) * ih1 - ih2
  | neg_add_one n ih1 ih2 =>
    have h₁ := U_add_two R (-n - 1)
    have h₂ := U_add_two R (-n)
    have h₃ := T_add_two R (-n)
    linear_combination (norm := ring_nf) -h₃ + h₂ - (X : R[X]) * h₁ - ih2 + 2 * (X : R[X]) * ih1

/--
theorem `T_eq_U_sub_X_mul_U` / 定理 `T_eq_U_sub_X_mul_U`

English:
theorem T_eq_U_sub_X_mul_U
  given: (n : Int)
  statement: T R n = U R n - X * U R (n - 1)
  proof: by
  linear_combination (norm := ring_nf) - U_eq_X_mul_U_add_T R (n - 1)

中文:
定理 T_eq_U_sub_X_mul_U
  条件: (n : 整数)
  结论: T R n = U R n - X * U R (n - 1)
  证明: by
  linear_combination (norm := ring_nf) - U_eq_X_mul_U_add_T R (n - 1)

Depends on / 依赖: U_eq_X_mul_U_add_T, linear_combination, ring_nf
-/
theorem T_eq_U_sub_X_mul_U (n : Int) : T R n = U R n - X * U R (n - 1) := by
  linear_combination (norm := ring_nf) - U_eq_X_mul_U_add_T R (n - 1)

/--
theorem `T_eq_X_mul_T_sub_pol_U` / 定理 `T_eq_X_mul_T_sub_pol_U`

English:
theorem T_eq_X_mul_T_sub_pol_U
  given: (n : Int)
  statement: T R (n + 2) = X * T R (n + 1) - (1 - X ^ 2) * U R n
  proof: by
  have h₁ := U_eq_X_mul_U_add_T R n
  have h₂ := U_eq_X_mul_U_add_T R (n + 1)
  have h₃ := U_add_two R n
  linear_combination (norm := ring_nf) h₃ - h₂ + (X : R[X]) * h₁

中文:
定理 T_eq_X_mul_T_sub_pol_U
  条件: (n : 整数)
  结论: T R (n + 2) = X * T R (n + 1) - (1 - X ^ 2) * U R n
  证明: by
  have h₁ := U_eq_X_mul_U_add_T R n
  have h₂ := U_eq_X_mul_U_add_T R (n + 1)
  have h₃ := U_add_two R n
  linear_combination (norm := ring_nf) h₃ - h₂ + (X : R[X]) * h₁

Depends on / 依赖: U_add_two, U_eq_X_mul_U_add_T, linear_combination, ring_nf
-/
theorem T_eq_X_mul_T_sub_pol_U (n : Int) : T R (n + 2) = X * T R (n + 1) - (1 - X ^ 2) * U R n := by
  have h₁ := U_eq_X_mul_U_add_T R n
  have h₂ := U_eq_X_mul_U_add_T R (n + 1)
  have h₃ := U_add_two R n
  linear_combination (norm := ring_nf) h₃ - h₂ + (X : R[X]) * h₁

/--
theorem `one_sub_X_sq_mul_U_eq_pol_in_T` / 定理 `one_sub_X_sq_mul_U_eq_pol_in_T`

English:
theorem one_sub_X_sq_mul_U_eq_pol_in_T
  given: (n : Int)
  proof: by
  linear_combination T_eq_X_mul_T_sub_pol_U R n

中文:
定理 one_sub_X_sq_mul_U_eq_pol_in_T
  条件: (n : 整数)
  证明: by
  linear_combination T_eq_X_mul_T_sub_pol_U R n

Depends on / 依赖: T_eq_X_mul_T_sub_pol_U, linear_combination
-/
theorem one_sub_X_sq_mul_U_eq_pol_in_T (n : Int) :
    (1 - X ^ 2) * U R n = X * T R (n + 1) - T R (n + 2) := by
  linear_combination T_eq_X_mul_T_sub_pol_U R n

/--
theorem `T_eq_X_mul_U_sub_U` / 定理 `T_eq_X_mul_U_sub_U`

English:
theorem T_eq_X_mul_U_sub_U
  given: (n : Int)
  statement: T R (n + 2) = X * U R (n + 1) - U R n
  proof: by
  have h := T_eq_U_sub_X_mul_U (R := R) (-(n + 2))
  rw [T_neg]; rw [U_neg]; rw [Int.add_sub_cancel]; rw [← neg_add' _ 1]; rw [U_neg]; rw [show n + 2 + 1 - 2 = n + 1 by ring] at h
  linear_combination (norm := ring_nf) h

中文:
定理 T_eq_X_mul_U_sub_U
  条件: (n : 整数)
  结论: T R (n + 2) = X * U R (n + 1) - U R n
  证明: by
  have h := T_eq_U_sub_X_mul_U (R := R) (-(n + 2))
  rw [T_neg]; rw [U_neg]; rw [Int.add_sub_cancel]; rw [← neg_add' _ 1]; rw [U_neg]; rw [show n + 2 + 1 - 2 = n + 1 by ring] at h
  linear_combination (norm := ring_nf) h

Depends on / 依赖: Int.add_sub_cancel, T_eq_U_sub_X_mul_U, T_neg, U_neg, add_sub_cancel, linear_combination, neg_add, ring_nf
-/
theorem T_eq_X_mul_U_sub_U (n : Int) : T R (n + 2) = X * U R (n + 1) - U R n := by
  have h := T_eq_U_sub_X_mul_U (R := R) (-(n + 2))
  rw [T_neg]; rw [U_neg]; rw [Int.add_sub_cancel]; rw [← neg_add' _ 1]; rw [U_neg]; rw [show n + 2 + 1 - 2 = n + 1 by ring] at h
  linear_combination (norm := ring_nf) h

/--
theorem `two_mul_T_eq_U_sub_U` / 定理 `two_mul_T_eq_U_sub_U`

English:
theorem two_mul_T_eq_U_sub_U
  given: (n : Int)
  statement: 2 * T R (n + 2) = U R (n + 2) - U R n
  proof: by
  linear_combination (norm := ring_nf) (T_eq_U_sub_X_mul_U R (n + 2)) + (T_eq_X_mul_U_sub_U R n)

中文:
定理 two_mul_T_eq_U_sub_U
  条件: (n : 整数)
  结论: 2 * T R (n + 2) = U R (n + 2) - U R n
  证明: by
  linear_combination (norm := ring_nf) (T_eq_U_sub_X_mul_U R (n + 2)) + (T_eq_X_mul_U_sub_U R n)

Depends on / 依赖: T_eq_U_sub_X_mul_U, T_eq_X_mul_U_sub_U, linear_combination, ring_nf
-/
theorem two_mul_T_eq_U_sub_U (n : Int) : 2 * T R (n + 2) = U R (n + 2) - U R n := by
  linear_combination (norm := ring_nf) (T_eq_U_sub_X_mul_U R (n + 2)) + (T_eq_X_mul_U_sub_U R n)

/--
theorem `U_eq_two_mul_T_add_U` / 定理 `U_eq_two_mul_T_add_U`

English:
theorem U_eq_two_mul_T_add_U
  given: (n : Int)
  statement: U R (n + 2) = 2 * T R (n + 2) + U R n
  proof: by
  linear_combination (norm := ring_nf) - (two_mul_T_eq_U_sub_U R n)

中文:
定理 U_eq_two_mul_T_add_U
  条件: (n : 整数)
  结论: U R (n + 2) = 2 * T R (n + 2) + U R n
  证明: by
  linear_combination (norm := ring_nf) - (two_mul_T_eq_U_sub_U R n)

Depends on / 依赖: linear_combination, ring_nf, two_mul_T_eq_U_sub_U
-/
theorem U_eq_two_mul_T_add_U (n : Int) : U R (n + 2) = 2 * T R (n + 2) + U R n := by
  linear_combination (norm := ring_nf) - (two_mul_T_eq_U_sub_U R n)

/--
theorem `U_mem_span_T` / 定理 `U_mem_span_T`

English:
theorem U_mem_span_T
  given: (n : Nat)
  statement: U R n in Submodule.span Nat ((fun m : Nat => T R m) '' Set.Icc 0 n)
  proof: by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one =>
    rw [show U R (1 : Nat) = 2 * T R 1 by simp]; rw [← smul_eq_mul]; norm_cast
    exact Submodule.smul_of_tower_mem _ 2 (Submodule.mem_span_of_mem ⟨1, by simp⟩)
  | more n h₀ _ =>
    push_cast; rw [U_eq_two_mul_T_add_U, ← smul_eq_mul]; norm_cast
    refine Submodule.add_mem _ ?_ ((Submodule.span_mono (by grind)) h₀)
    · exact Submodule.smul_of_tower_mem _ 2
        (Submodule.mem_span_of_mem ⟨n + 2, by simp⟩)

中文:
定理 U_mem_span_T
  条件: (n : 自然数)
  结论: U R n in 子模.span 自然数 ((fun m : 自然数 => T R m) '' 集合.闭区间 0 n)
  证明: by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one =>
    rw [show U R (1 : Nat) = 2 * T R 1 by simp]; rw [← smul_eq_mul]; norm_cast
    exact Submodule.smul_of_tower_mem _ 2 (Submodule.mem_span_of_mem ⟨1, by simp⟩)
  | more n h₀ _ =>
    push_cast; rw [U_eq_two_mul_T_add_U, ← smul_eq_mul]; norm_cast
    refine Submodule.add_mem _ ?_ ((Submodule.span_mono (by grind)) h₀)
    · exact Submodule.smul_of_tower_mem _ 2
        (Submodule.mem_span_of_mem ⟨n + 2, by simp⟩)

Depends on / 依赖: Nat.twoStepInduction, Submodule, Submodule.add_mem, Submodule.mem_span_of_mem, Submodule.smul_of_tower_mem, Submodule.span_mono, U_eq_two_mul_T_add_U, add_mem, mem_span_of_mem, smul_eq_mul, smul_of_tower_mem, span_mono, twoStepInduction
-/
theorem U_mem_span_T (n : Nat) : U R n in Submodule.span Nat ((fun m : Nat => T R m) '' Set.Icc 0 n) := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one =>
    rw [show U R (1 : Nat) = 2 * T R 1 by simp]; rw [← smul_eq_mul]; norm_cast
    exact Submodule.smul_of_tower_mem _ 2 (Submodule.mem_span_of_mem ⟨1, by simp⟩)
  | more n h₀ _ =>
    push_cast; rw [U_eq_two_mul_T_add_U, ← smul_eq_mul]; norm_cast
    refine Submodule.add_mem _ ?_ ((Submodule.span_mono (by grind)) h₀)
    · exact Submodule.smul_of_tower_mem _ 2
        (Submodule.mem_span_of_mem ⟨n + 2, by simp⟩)

/--
Definition of `C` / `C` 的定义

English:
definition C
  signature: : Int -> R[X]

中文:
定义 C
  签名: : 整数 -> R[X]
-/
noncomputable def C : Int -> R[X]
  | 0 => 2
  | 1 => X
  | (n : Nat) + 2 => X * C (n + 1) - C n
  | -((n : Nat) + 1) => X * C (-n) - C (-n + 1)
  termination_by n => Int.natAbs n + Int.natAbs (n - 1)

@[simp]
/--
theorem `C_add_two` / 定理 `C_add_two`

English:
theorem C_add_two
  statement: forall n, C R (n + 2) = X * C R (n + 1) - C R n

中文:
定理 C_add_two
  结论: 对任意 n, C R (n + 2) = X * C R (n + 1) - C R n

Depends on / 依赖: C.eq_4, Int.negSucc_eq, eq_4, negSucc_eq, ring_nf
-/
theorem C_add_two : forall n, C R (n + 2) = X * C R (n + 1) - C R n
  | (k : Nat) => C.eq_3 R k
  | -(k + 1 : Nat) => by linear_combination (norm := (simp [Int.negSucc_eq]; ring_nf)) C.eq_4 R k

/--
theorem `C_add_one` / 定理 `C_add_one`

English:
theorem C_add_one
  given: (n : Int)
  statement: C R (n + 1) = X * C R n - C R (n - 1)
  proof: by
  linear_combination (norm := ring_nf) C_add_two R (n - 1)

中文:
定理 C_add_one
  条件: (n : 整数)
  结论: C R (n + 1) = X * C R n - C R (n - 1)
  证明: by
  linear_combination (norm := ring_nf) C_add_two R (n - 1)

Depends on / 依赖: C_add_two, linear_combination, ring_nf
-/
theorem C_add_one (n : Int) : C R (n + 1) = X * C R n - C R (n - 1) := by
  linear_combination (norm := ring_nf) C_add_two R (n - 1)

/--
theorem `C_sub_two` / 定理 `C_sub_two`

English:
theorem C_sub_two
  given: (n : Int)
  statement: C R (n - 2) = X * C R (n - 1) - C R n
  proof: by
  linear_combination (norm := ring_nf) C_add_two R (n - 2)

中文:
定理 C_sub_two
  条件: (n : 整数)
  结论: C R (n - 2) = X * C R (n - 1) - C R n
  证明: by
  linear_combination (norm := ring_nf) C_add_two R (n - 2)

Depends on / 依赖: C_add_two, linear_combination, ring_nf
-/
theorem C_sub_two (n : Int) : C R (n - 2) = X * C R (n - 1) - C R n := by
  linear_combination (norm := ring_nf) C_add_two R (n - 2)

/--
theorem `C_sub_one` / 定理 `C_sub_one`

English:
theorem C_sub_one
  given: (n : Int)
  statement: C R (n - 1) = X * C R n - C R (n + 1)
  proof: by
  linear_combination (norm := ring_nf) C_add_two R (n - 1)

中文:
定理 C_sub_one
  条件: (n : 整数)
  结论: C R (n - 1) = X * C R n - C R (n + 1)
  证明: by
  linear_combination (norm := ring_nf) C_add_two R (n - 1)

Depends on / 依赖: C_add_two, linear_combination, ring_nf
-/
theorem C_sub_one (n : Int) : C R (n - 1) = X * C R n - C R (n + 1) := by
  linear_combination (norm := ring_nf) C_add_two R (n - 1)

/--
theorem `C_eq` / 定理 `C_eq`

English:
theorem C_eq
  given: (n : Int)
  statement: C R n = X * C R (n - 1) - C R (n - 2)
  proof: by
  linear_combination (norm := ring_nf) C_add_two R (n - 2)

@[simp]

中文:
定理 C_eq
  条件: (n : 整数)
  结论: C R n = X * C R (n - 1) - C R (n - 2)
  证明: by
  linear_combination (norm := ring_nf) C_add_two R (n - 2)

@[simp]

Depends on / 依赖: C_add_two, linear_combination, ring_nf
-/
theorem C_eq (n : Int) : C R n = X * C R (n - 1) - C R (n - 2) := by
  linear_combination (norm := ring_nf) C_add_two R (n - 2)

@[simp]
/--
theorem `C_zero` / 定理 `C_zero`

English:
theorem C_zero
  statement: C R 0 = 2
  proof: by simp [C]

@[simp]

中文:
定理 C_zero
  结论: C R 0 = 2
  证明: by simp [C]

@[simp]
-/
theorem C_zero : C R 0 = 2 := by simp [C]

@[simp]
/--
theorem `C_one` / 定理 `C_one`

English:
theorem C_one
  statement: C R 1 = X
  proof: by simp [C]

中文:
定理 C_one
  结论: C R 1 = X
  证明: by simp [C]
-/
theorem C_one : C R 1 = X := by simp [C]

/--
theorem `C_neg_one` / 定理 `C_neg_one`

English:
theorem C_neg_one
  statement: C R (-1) = X
  proof: by
  change C R (Int.negSucc 0) = X
  rw [C]
  suffices X * 2 - X = X by simpa
  ring

中文:
定理 C_neg_one
  结论: C R (-1) = X
  证明: by
  change C R (Int.negSucc 0) = X
  rw [C]
  suffices X * 2 - X = X by simpa
  ring

Depends on / 依赖: Int.negSucc, negSucc
-/
theorem C_neg_one : C R (-1) = X := by
  change C R (Int.negSucc 0) = X
  rw [C]
  suffices X * 2 - X = X by simpa
  ring

/--
theorem `C_two` / 定理 `C_two`

English:
theorem C_two
  statement: C R 2 = X ^ 2 - 2
  proof: by
  simpa [pow_two, mul_assoc] using C_add_two R 0

@[simp]

中文:
定理 C_two
  结论: C R 2 = X ^ 2 - 2
  证明: by
  simpa [pow_two, mul_assoc] using C_add_two R 0

@[simp]

Depends on / 依赖: C_add_two, mul_assoc, pow_two
-/
theorem C_two : C R 2 = X ^ 2 - 2 := by
  simpa [pow_two, mul_assoc] using C_add_two R 0

@[simp]
/--
theorem `C_neg` / 定理 `C_neg`

English:
theorem C_neg
  given: (n : Int)
  statement: C R (-n) = C R n
  proof: by
  induction n using Polynomial.Chebyshev.induct with
  | zero => rfl
  | one => simp only [C_neg_one, C_one]
  | add_two n ih1 ih2 =>
    have h₁ := C_add_two R n
    have h₂ := C_sub_two R (-n)
    linear_combination (norm := ring_nf) (X : R[X]) * ih1 - ih2 - h₁ + h₂
  | neg_add_one n ih1 ih2 =>
    have h₁ := C_add_one R n
    have h₂ := C_sub_one R (-n)
    linear_combination (norm := ring_nf) (X : R[X]) * ih1 - ih2 + h₁ - h₂

中文:
定理 C_neg
  条件: (n : 整数)
  结论: C R (-n) = C R n
  证明: by
  induction n using Polynomial.Chebyshev.induct with
  | zero => rfl
  | one => simp only [C_neg_one, C_one]
  | add_two n ih1 ih2 =>
    have h₁ := C_add_two R n
    have h₂ := C_sub_two R (-n)
    linear_combination (norm := ring_nf) (X : R[X]) * ih1 - ih2 - h₁ + h₂
  | neg_add_one n ih1 ih2 =>
    have h₁ := C_add_one R n
    have h₂ := C_sub_one R (-n)
    linear_combination (norm := ring_nf) (X : R[X]) * ih1 - ih2 + h₁ - h₂

Depends on / 依赖: C_add_one, C_add_two, C_neg_one, C_one, C_sub_one, C_sub_two, Chebyshev, Polynomial, Polynomial.Chebyshev.induct, add_two, induct, linear_combination, neg_add_one, ring_nf
-/
theorem C_neg (n : Int) : C R (-n) = C R n := by
  induction n using Polynomial.Chebyshev.induct with
  | zero => rfl
  | one => simp only [C_neg_one, C_one]
  | add_two n ih1 ih2 =>
    have h₁ := C_add_two R n
    have h₂ := C_sub_two R (-n)
    linear_combination (norm := ring_nf) (X : R[X]) * ih1 - ih2 - h₁ + h₂
  | neg_add_one n ih1 ih2 =>
    have h₁ := C_add_one R n
    have h₂ := C_sub_one R (-n)
    linear_combination (norm := ring_nf) (X : R[X]) * ih1 - ih2 + h₁ - h₂

/--
theorem `C_natAbs` / 定理 `C_natAbs`

English:
theorem C_natAbs
  given: (n : Int)
  statement: C R n.natAbs = C R n
  proof: by
  obtain h | h := Int.natAbs_eq n <;> nth_rw 2 [h]; simp

中文:
定理 C_natAbs
  条件: (n : 整数)
  结论: C R n.natAbs = C R n
  证明: by
  obtain h | h := Int.natAbs_eq n <;> nth_rw 2 [h]; simp

Depends on / 依赖: Int.natAbs_eq, natAbs_eq, nth_rw
-/
theorem C_natAbs (n : Int) : C R n.natAbs = C R n := by
  obtain h | h := Int.natAbs_eq n <;> nth_rw 2 [h]; simp

/--
theorem `C_neg_two` / 定理 `C_neg_two`

English:
theorem C_neg_two
  statement: C R (-2) = X ^ 2 - 2
  proof: by simp [C_two]

中文:
定理 C_neg_two
  结论: C R (-2) = X ^ 2 - 2
  证明: by simp [C_two]

Depends on / 依赖: C_two
-/
theorem C_neg_two : C R (-2) = X ^ 2 - 2 := by simp [C_two]

/--
theorem `C_comp_two_mul_X` / 定理 `C_comp_two_mul_X`

English:
theorem C_comp_two_mul_X
  given: (n : Int)
  statement: (C R n).comp (2 * X) = 2 * T R n
  proof: by
  induction n using Polynomial.Chebyshev.induct with
  | zero => simp
  | one => simp
  | add_two n ih1 ih2 =>
    simp_rw [C_add_two, T_add_two, sub_comp, mul_comp, X_comp, ih1, ih2]
    ring
  | neg_add_one n ih1 ih2 =>
    simp_rw [C_sub_one, T_sub_one, sub_comp, mul_comp, X_comp, ih1, ih2]
    ring

@[simp]

中文:
定理 C_comp_two_mul_X
  条件: (n : 整数)
  结论: (C R n).comp (2 * X) = 2 * T R n
  证明: by
  induction n using Polynomial.Chebyshev.induct with
  | zero => simp
  | one => simp
  | add_two n ih1 ih2 =>
    simp_rw [C_add_two, T_add_two, sub_comp, mul_comp, X_comp, ih1, ih2]
    ring
  | neg_add_one n ih1 ih2 =>
    simp_rw [C_sub_one, T_sub_one, sub_comp, mul_comp, X_comp, ih1, ih2]
    ring

@[simp]

Depends on / 依赖: C_add_two, C_sub_one, Chebyshev, Polynomial, Polynomial.Chebyshev.induct, T_add_two, T_sub_one, X_comp, add_two, induct, mul_comp, neg_add_one, simp_rw, sub_comp
-/
theorem C_comp_two_mul_X (n : Int) : (C R n).comp (2 * X) = 2 * T R n := by
  induction n using Polynomial.Chebyshev.induct with
  | zero => simp
  | one => simp
  | add_two n ih1 ih2 =>
    simp_rw [C_add_two, T_add_two, sub_comp, mul_comp, X_comp, ih1, ih2]
    ring
  | neg_add_one n ih1 ih2 =>
    simp_rw [C_sub_one, T_sub_one, sub_comp, mul_comp, X_comp, ih1, ih2]
    ring

@[simp]
/--
theorem `C_eval_two` / 定理 `C_eval_two`

English:
theorem C_eval_two
  given: (n : Int)
  statement: (C R n).eval 2 = 2
  proof: by
  induction n using Polynomial.Chebyshev.induct with
  | zero => simp
  | one => simp
  | add_two n ih1 ih2 => simp [C_add_two, ih1, ih2]; norm_num
  | neg_add_one n ih1 ih2 => simp [C_sub_one, -C_neg, ih1, ih2]; norm_num

中文:
定理 C_eval_two
  条件: (n : 整数)
  结论: (C R n).eval 2 = 2
  证明: by
  induction n using Polynomial.Chebyshev.induct with
  | zero => simp
  | one => simp
  | add_two n ih1 ih2 => simp [C_add_two, ih1, ih2]; norm_num
  | neg_add_one n ih1 ih2 => simp [C_sub_one, -C_neg, ih1, ih2]; norm_num

Depends on / 依赖: C_add_two, C_neg, C_sub_one, Chebyshev, Polynomial, Polynomial.Chebyshev.induct, add_two, induct, neg_add_one
-/
theorem C_eval_two (n : Int) : (C R n).eval 2 = 2 := by
  induction n using Polynomial.Chebyshev.induct with
  | zero => simp
  | one => simp
  | add_two n ih1 ih2 => simp [C_add_two, ih1, ih2]; norm_num
  | neg_add_one n ih1 ih2 => simp [C_sub_one, -C_neg, ih1, ih2]; norm_num

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `C_eval_neg_two` / 定理 `C_eval_neg_two`

English:
theorem C_eval_neg_two
  given: (n : Int)
  statement: (C R n).eval (-2) = 2 * n.negOnePow
  proof: by
  induction n using Polynomial.Chebyshev.induct with
  | zero => simp
  | one => simp
  | add_two n ih1 ih2 =>
    simp only [C_add_two, eval_sub, eval_mul, eval_X, mul_neg, mul_one, ih1,
      Int.negOnePow_add, Int.negOnePow_one, Units.val_neg, Int.cast_neg, neg_mul, neg_neg, ih2,
      Int.negOnePow_def 2]
    norm_cast
    norm_num
    ring
  | neg_add_one n ih1 ih2 =>
    simp only [C_sub_one, eval_sub, eval_mul, eval_X, mul_neg, mul_one, ih1, neg_mul,
      ih2, Int.negOnePow_add, Int.negOnePow_one, Units.val_neg, Int.cast_neg, sub_neg_eq_add,
      Int.negOnePow_sub]
    ring

中文:
定理 C_eval_neg_two
  条件: (n : 整数)
  结论: (C R n).eval (-2) = 2 * n.negOnePow
  证明: by
  induction n using Polynomial.Chebyshev.induct with
  | zero => simp
  | one => simp
  | add_two n ih1 ih2 =>
    simp only [C_add_two, eval_sub, eval_mul, eval_X, mul_neg, mul_one, ih1,
      Int.negOnePow_add, Int.negOnePow_one, Units.val_neg, Int.cast_neg, neg_mul, neg_neg, ih2,
      Int.negOnePow_def 2]
    norm_cast
    norm_num
    ring
  | neg_add_one n ih1 ih2 =>
    simp only [C_sub_one, eval_sub, eval_mul, eval_X, mul_neg, mul_one, ih1, neg_mul,
      ih2, Int.negOnePow_add, Int.negOnePow_one, Units.val_neg, Int.cast_neg, sub_neg_eq_add,
      Int.negOnePow_sub]
    ring

Depends on / 依赖: C_add_two, C_sub_one, Chebyshev, Int.cast_neg, Int.negOnePow_add, Int.negOnePow_def, Int.negOnePow_one, Polynomial, Polynomial.Chebyshev.induct, Units.val_neg, add_two, cast_neg, eval_X, eval_mul, eval_sub, induct, mul_neg, mul_one, negOnePow_add, negOnePow_def
-/
theorem C_eval_neg_two (n : Int) : (C R n).eval (-2) = 2 * n.negOnePow := by
  induction n using Polynomial.Chebyshev.induct with
  | zero => simp
  | one => simp
  | add_two n ih1 ih2 =>
    simp only [C_add_two, eval_sub, eval_mul, eval_X, mul_neg, mul_one, ih1,
      Int.negOnePow_add, Int.negOnePow_one, Units.val_neg, Int.cast_neg, neg_mul, neg_neg, ih2,
      Int.negOnePow_def 2]
    norm_cast
    norm_num
    ring
  | neg_add_one n ih1 ih2 =>
    simp only [C_sub_one, eval_sub, eval_mul, eval_X, mul_neg, mul_one, ih1, neg_mul,
      ih2, Int.negOnePow_add, Int.negOnePow_one, Units.val_neg, Int.cast_neg, sub_neg_eq_add,
      Int.negOnePow_sub]
    ring

/--
theorem `C_eq_two_mul_T_comp_half_mul_X` / 定理 `C_eq_two_mul_T_comp_half_mul_X`

English:
theorem C_eq_two_mul_T_comp_half_mul_X
  given: [Invertible (2 : R)] (n : Int)
  proof: by
  have := congr_arg (·.comp (Polynomial.C ⅟2 * X)) (C_comp_two_mul_X R n)
  simp_rw [comp_assoc, mul_comp, ofNat_comp, X_comp, ← mul_assoc, ← C_eq_natCast, ← C_mul,
    Nat.cast_ofNat, mul_invOf_self', map_one, one_mul, comp_X, map_ofNat] at this
  assumption

中文:
定理 C_eq_two_mul_T_comp_half_mul_X
  条件: [可逆 (2 : R)] (n : 整数)
  证明: by
  have := congr_arg (·.comp (Polynomial.C ⅟2 * X)) (C_comp_two_mul_X R n)
  simp_rw [comp_assoc, mul_comp, ofNat_comp, X_comp, ← mul_assoc, ← C_eq_natCast, ← C_mul,
    Nat.cast_ofNat, mul_invOf_self', map_one, one_mul, comp_X, map_ofNat] at this
  assumption

Depends on / 依赖: C_comp_two_mul_X, C_eq_natCast, C_mul, Nat.cast_ofNat, Polynomial, Polynomial.C, X_comp, cast_ofNat, comp_X, comp_assoc, congr_arg, map_ofNat, map_one, mul_assoc, mul_comp, mul_invOf_self, ofNat_comp, one_mul, simp_rw
-/
theorem C_eq_two_mul_T_comp_half_mul_X [Invertible (2 : R)] (n : Int) :
    C R n = 2 * (T R n).comp (Polynomial.C ⅟2 * X) := by
  have := congr_arg (·.comp (Polynomial.C ⅟2 * X)) (C_comp_two_mul_X R n)
  simp_rw [comp_assoc, mul_comp, ofNat_comp, X_comp, ← mul_assoc, ← C_eq_natCast, ← C_mul,
    Nat.cast_ofNat, mul_invOf_self', map_one, one_mul, comp_X, map_ofNat] at this
  assumption

/--
theorem `T_eq_half_mul_C_comp_two_mul_X` / 定理 `T_eq_half_mul_C_comp_two_mul_X`

English:
theorem T_eq_half_mul_C_comp_two_mul_X
  given: [Invertible (2 : R)] (n : Int)
  proof: by
  rw [C_comp_two_mul_X]; rw [← mul_assoc]; rw [← map_ofNat Polynomial.C 2]; rw [← map_mul]; rw [invOf_mul_self']; rw [map_one]; rw [one_mul]

中文:
定理 T_eq_half_mul_C_comp_two_mul_X
  条件: [可逆 (2 : R)] (n : 整数)
  证明: by
  rw [C_comp_two_mul_X]; rw [← mul_assoc]; rw [← map_ofNat Polynomial.C 2]; rw [← map_mul]; rw [invOf_mul_self']; rw [map_one]; rw [one_mul]

Depends on / 依赖: C_comp_two_mul_X, Polynomial, Polynomial.C, invOf_mul_self, map_mul, map_ofNat, map_one, mul_assoc, one_mul
-/
theorem T_eq_half_mul_C_comp_two_mul_X [Invertible (2 : R)] (n : Int) :
    T R n = Polynomial.C ⅟2 * (C R n).comp (2 * X) := by
  rw [C_comp_two_mul_X]; rw [← mul_assoc]; rw [← map_ofNat Polynomial.C 2]; rw [← map_mul]; rw [invOf_mul_self']; rw [map_one]; rw [one_mul]

/--
Definition of `S` / `S` 的定义

English:
definition S
  signature: : Int -> R[X]

中文:
定义 S
  签名: : 整数 -> R[X]
-/
noncomputable def S : Int -> R[X]
  | 0 => 1
  | 1 => X
  | (n : Nat) + 2 => X * S (n + 1) - S n
  | -((n : Nat) + 1) => X * S (-n) - S (-n + 1)
  termination_by n => Int.natAbs n + Int.natAbs (n - 1)

@[simp]
/--
theorem `S_add_two` / 定理 `S_add_two`

English:
theorem S_add_two
  statement: forall n, S R (n + 2) = X * S R (n + 1) - S R n

中文:
定理 S_add_two
  结论: 对任意 n, S R (n + 2) = X * S R (n + 1) - S R n

Depends on / 依赖: Int.negSucc_eq, S.eq_4, eq_4, negSucc_eq, ring_nf
-/
theorem S_add_two : forall n, S R (n + 2) = X * S R (n + 1) - S R n
  | (k : Nat) => S.eq_3 R k
  | -(k + 1 : Nat) => by linear_combination (norm := (simp [Int.negSucc_eq]; ring_nf)) S.eq_4 R k

/--
theorem `S_add_one` / 定理 `S_add_one`

English:
theorem S_add_one
  given: (n : Int)
  statement: S R (n + 1) = X * S R n - S R (n - 1)
  proof: by
  linear_combination (norm := ring_nf) S_add_two R (n - 1)

中文:
定理 S_add_one
  条件: (n : 整数)
  结论: S R (n + 1) = X * S R n - S R (n - 1)
  证明: by
  linear_combination (norm := ring_nf) S_add_two R (n - 1)

Depends on / 依赖: S_add_two, linear_combination, ring_nf
-/
theorem S_add_one (n : Int) : S R (n + 1) = X * S R n - S R (n - 1) := by
  linear_combination (norm := ring_nf) S_add_two R (n - 1)

/--
theorem `S_sub_two` / 定理 `S_sub_two`

English:
theorem S_sub_two
  given: (n : Int)
  statement: S R (n - 2) = X * S R (n - 1) - S R n
  proof: by
  linear_combination (norm := ring_nf) S_add_two R (n - 2)

中文:
定理 S_sub_two
  条件: (n : 整数)
  结论: S R (n - 2) = X * S R (n - 1) - S R n
  证明: by
  linear_combination (norm := ring_nf) S_add_two R (n - 2)

Depends on / 依赖: S_add_two, linear_combination, ring_nf
-/
theorem S_sub_two (n : Int) : S R (n - 2) = X * S R (n - 1) - S R n := by
  linear_combination (norm := ring_nf) S_add_two R (n - 2)

/--
theorem `S_sub_one` / 定理 `S_sub_one`

English:
theorem S_sub_one
  given: (n : Int)
  statement: S R (n - 1) = X * S R n - S R (n + 1)
  proof: by
  linear_combination (norm := ring_nf) S_add_two R (n - 1)

中文:
定理 S_sub_one
  条件: (n : 整数)
  结论: S R (n - 1) = X * S R n - S R (n + 1)
  证明: by
  linear_combination (norm := ring_nf) S_add_two R (n - 1)

Depends on / 依赖: S_add_two, linear_combination, ring_nf
-/
theorem S_sub_one (n : Int) : S R (n - 1) = X * S R n - S R (n + 1) := by
  linear_combination (norm := ring_nf) S_add_two R (n - 1)

/--
theorem `S_eq` / 定理 `S_eq`

English:
theorem S_eq
  given: (n : Int)
  statement: S R n = X * S R (n - 1) - S R (n - 2)
  proof: by
  linear_combination (norm := ring_nf) S_add_two R (n - 2)

@[simp]

中文:
定理 S_eq
  条件: (n : 整数)
  结论: S R n = X * S R (n - 1) - S R (n - 2)
  证明: by
  linear_combination (norm := ring_nf) S_add_two R (n - 2)

@[simp]

Depends on / 依赖: S_add_two, linear_combination, ring_nf
-/
theorem S_eq (n : Int) : S R n = X * S R (n - 1) - S R (n - 2) := by
  linear_combination (norm := ring_nf) S_add_two R (n - 2)

@[simp]
/--
theorem `S_zero` / 定理 `S_zero`

English:
theorem S_zero
  statement: S R 0 = 1
  proof: by simp [S]

@[simp]

中文:
定理 S_zero
  结论: S R 0 = 1
  证明: by simp [S]

@[simp]
-/
theorem S_zero : S R 0 = 1 := by simp [S]

@[simp]
/--
theorem `S_one` / 定理 `S_one`

English:
theorem S_one
  statement: S R 1 = X
  proof: by simp [S]

@[simp]

中文:
定理 S_one
  结论: S R 1 = X
  证明: by simp [S]

@[simp]
-/
theorem S_one : S R 1 = X := by simp [S]

@[simp]
/--
theorem `S_neg_one` / 定理 `S_neg_one`

English:
theorem S_neg_one
  statement: S R (-1) = 0
  proof: by simpa using S_sub_one R 0

中文:
定理 S_neg_one
  结论: S R (-1) = 0
  证明: by simpa using S_sub_one R 0

Depends on / 依赖: S_sub_one
-/
theorem S_neg_one : S R (-1) = 0 := by simpa using S_sub_one R 0

/--
theorem `S_two` / 定理 `S_two`

English:
theorem S_two
  statement: S R 2 = X ^ 2 - 1
  proof: by
  have := S_add_two R 0
  simp only [zero_add, S_one, S_zero] at this
  linear_combination this

@[simp]

中文:
定理 S_two
  结论: S R 2 = X ^ 2 - 1
  证明: by
  have := S_add_two R 0
  simp only [zero_add, S_one, S_zero] at this
  linear_combination this

@[simp]

Depends on / 依赖: S_add_two, S_one, S_zero, linear_combination, zero_add
-/
theorem S_two : S R 2 = X ^ 2 - 1 := by
  have := S_add_two R 0
  simp only [zero_add, S_one, S_zero] at this
  linear_combination this

@[simp]
/--
theorem `S_neg_two` / 定理 `S_neg_two`

English:
theorem S_neg_two
  statement: S R (-2) = -1
  proof: by
  simpa [zero_sub, Int.reduceNeg, S_neg_one, mul_zero, S_zero] using S_sub_two R 0

中文:
定理 S_neg_two
  结论: S R (-2) = -1
  证明: by
  simpa [zero_sub, Int.reduceNeg, S_neg_one, mul_zero, S_zero] using S_sub_two R 0

Depends on / 依赖: Int.reduceNeg, S_neg_one, S_sub_two, S_zero, mul_zero, reduceNeg, zero_sub
-/
theorem S_neg_two : S R (-2) = -1 := by
  simpa [zero_sub, Int.reduceNeg, S_neg_one, mul_zero, S_zero] using S_sub_two R 0

/--
theorem `S_neg_sub_one` / 定理 `S_neg_sub_one`

English:
theorem S_neg_sub_one
  given: (n : Int)
  statement: S R (-n - 1) = -S R (n - 1)
  proof: by
  induction n using Polynomial.Chebyshev.induct with
  | zero => simp
  | one => simp
  | add_two n ih1 ih2 =>
    have h₁ := S_add_one R n
    have h₂ := S_sub_two R (-n - 1)
    linear_combination (norm := ring_nf) (X : R[X]) * ih1 - ih2 + h₁ + h₂
  | neg_add_one n ih1 ih2 =>
    have h₁ := S_eq R n
    have h₂ := S_sub_two R (-n)
    linear_combination (norm := ring_nf) (X : R[X]) * ih1 - ih2 + h₁ + h₂

中文:
定理 S_neg_sub_one
  条件: (n : 整数)
  结论: S R (-n - 1) = -S R (n - 1)
  证明: by
  induction n using Polynomial.Chebyshev.induct with
  | zero => simp
  | one => simp
  | add_two n ih1 ih2 =>
    have h₁ := S_add_one R n
    have h₂ := S_sub_two R (-n - 1)
    linear_combination (norm := ring_nf) (X : R[X]) * ih1 - ih2 + h₁ + h₂
  | neg_add_one n ih1 ih2 =>
    have h₁ := S_eq R n
    have h₂ := S_sub_two R (-n)
    linear_combination (norm := ring_nf) (X : R[X]) * ih1 - ih2 + h₁ + h₂

Depends on / 依赖: Chebyshev, Polynomial, Polynomial.Chebyshev.induct, S_add_one, S_eq, S_sub_two, add_two, induct, linear_combination, neg_add_one, ring_nf
-/
theorem S_neg_sub_one (n : Int) : S R (-n - 1) = -S R (n - 1) := by
  induction n using Polynomial.Chebyshev.induct with
  | zero => simp
  | one => simp
  | add_two n ih1 ih2 =>
    have h₁ := S_add_one R n
    have h₂ := S_sub_two R (-n - 1)
    linear_combination (norm := ring_nf) (X : R[X]) * ih1 - ih2 + h₁ + h₂
  | neg_add_one n ih1 ih2 =>
    have h₁ := S_eq R n
    have h₂ := S_sub_two R (-n)
    linear_combination (norm := ring_nf) (X : R[X]) * ih1 - ih2 + h₁ + h₂

/--
theorem `S_neg` / 定理 `S_neg`

English:
theorem S_neg
  given: (n : Int)
  statement: S R (-n) = -S R (n - 2)
  proof: by simpa [sub_sub] using S_neg_sub_one R (n - 1)

@[simp]

中文:
定理 S_neg
  条件: (n : 整数)
  结论: S R (-n) = -S R (n - 2)
  证明: by simpa [sub_sub] using S_neg_sub_one R (n - 1)

@[simp]

Depends on / 依赖: S_neg_sub_one, sub_sub
-/
theorem S_neg (n : Int) : S R (-n) = -S R (n - 2) := by simpa [sub_sub] using S_neg_sub_one R (n - 1)

@[simp]
/--
theorem `S_neg_sub_two` / 定理 `S_neg_sub_two`

English:
theorem S_neg_sub_two
  given: (n : Int)
  statement: S R (-n - 2) = -S R n
  proof: by
  simpa [sub_eq_add_neg, add_comm] using S_neg R (n + 2)

@[simp]

中文:
定理 S_neg_sub_two
  条件: (n : 整数)
  结论: S R (-n - 2) = -S R n
  证明: by
  simpa [sub_eq_add_neg, add_comm] using S_neg R (n + 2)

@[simp]

Depends on / 依赖: S_neg, add_comm, sub_eq_add_neg
-/
theorem S_neg_sub_two (n : Int) : S R (-n - 2) = -S R n := by
  simpa [sub_eq_add_neg, add_comm] using S_neg R (n + 2)

@[simp]
/--
theorem `S_eval_two` / 定理 `S_eval_two`

English:
theorem S_eval_two
  given: (n : Int)
  statement: (S R n).eval 2 = n + 1
  proof: by
  induction n using Polynomial.Chebyshev.induct with
  | zero => simp
  | one => simp; norm_num
  | add_two n ih1 ih2 =>
    simp only [S_add_two, eval_sub, eval_mul, eval_X, ih1,
      Int.cast_add, Int.cast_natCast, Int.cast_one, ih2, Int.cast_ofNat]
    ring
  | neg_add_one n ih1 ih2 =>
    simp only [S_sub_one, eval_sub, eval_mul, eval_X,
      ih1, Int.cast_neg, Int.cast_natCast, ih2, Int.cast_add, Int.cast_one, Int.cast_sub,
      sub_add_cancel]
    ring

中文:
定理 S_eval_two
  条件: (n : 整数)
  结论: (S R n).eval 2 = n + 1
  证明: by
  induction n using Polynomial.Chebyshev.induct with
  | zero => simp
  | one => simp; norm_num
  | add_two n ih1 ih2 =>
    simp only [S_add_two, eval_sub, eval_mul, eval_X, ih1,
      Int.cast_add, Int.cast_natCast, Int.cast_one, ih2, Int.cast_ofNat]
    ring
  | neg_add_one n ih1 ih2 =>
    simp only [S_sub_one, eval_sub, eval_mul, eval_X,
      ih1, Int.cast_neg, Int.cast_natCast, ih2, Int.cast_add, Int.cast_one, Int.cast_sub,
      sub_add_cancel]
    ring

Depends on / 依赖: Chebyshev, Int.cast_add, Int.cast_natCast, Int.cast_neg, Int.cast_ofNat, Int.cast_one, Int.cast_sub, Polynomial, Polynomial.Chebyshev.induct, S_add_two, S_sub_one, add_two, cast_add, cast_natCast, cast_neg, cast_ofNat, cast_one, cast_sub, eval_X, eval_mul
-/
theorem S_eval_two (n : Int) : (S R n).eval 2 = n + 1 := by
  induction n using Polynomial.Chebyshev.induct with
  | zero => simp
  | one => simp; norm_num
  | add_two n ih1 ih2 =>
    simp only [S_add_two, eval_sub, eval_mul, eval_X, ih1,
      Int.cast_add, Int.cast_natCast, Int.cast_one, ih2, Int.cast_ofNat]
    ring
  | neg_add_one n ih1 ih2 =>
    simp only [S_sub_one, eval_sub, eval_mul, eval_X,
      ih1, Int.cast_neg, Int.cast_natCast, ih2, Int.cast_add, Int.cast_one, Int.cast_sub,
      sub_add_cancel]
    ring

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `S_eval_neg_two` / 定理 `S_eval_neg_two`

English:
theorem S_eval_neg_two
  given: (n : Int)
  statement: (S R n).eval (-2) = n.negOnePow * (n + 1)
  proof: by
  induction n using Polynomial.Chebyshev.induct with
  | zero => simp
  | one => simp; norm_num
  | add_two n ih1 ih2 =>
    simp only [S_add_two, eval_sub, eval_mul, eval_X, ih1,
      Int.cast_add, Int.cast_natCast, Int.cast_one, neg_mul, ih2, Int.cast_ofNat, Int.negOnePow_add,
      Int.negOnePow_def 2]
    norm_cast
    norm_num
    ring
  | neg_add_one n ih1 ih2 =>
    simp only [S_sub_one, eval_sub, eval_mul, eval_X, mul_neg, ih1,
      Int.cast_neg, Int.cast_natCast, Int.negOnePow_neg, neg_mul, ih2, Int.cast_add, Int.cast_one,
      Int.cast_sub, sub_add_cancel, Int.negOnePow_sub, Int.negOnePow_add]
    norm_cast
    norm_num
    ring

中文:
定理 S_eval_neg_two
  条件: (n : 整数)
  结论: (S R n).eval (-2) = n.negOnePow * (n + 1)
  证明: by
  induction n using Polynomial.Chebyshev.induct with
  | zero => simp
  | one => simp; norm_num
  | add_two n ih1 ih2 =>
    simp only [S_add_two, eval_sub, eval_mul, eval_X, ih1,
      Int.cast_add, Int.cast_natCast, Int.cast_one, neg_mul, ih2, Int.cast_ofNat, Int.negOnePow_add,
      Int.negOnePow_def 2]
    norm_cast
    norm_num
    ring
  | neg_add_one n ih1 ih2 =>
    simp only [S_sub_one, eval_sub, eval_mul, eval_X, mul_neg, ih1,
      Int.cast_neg, Int.cast_natCast, Int.negOnePow_neg, neg_mul, ih2, Int.cast_add, Int.cast_one,
      Int.cast_sub, sub_add_cancel, Int.negOnePow_sub, Int.negOnePow_add]
    norm_cast
    norm_num
    ring

Depends on / 依赖: Chebyshev, Int.c, Int.cast_add, Int.cast_natCast, Int.cast_neg, Int.cast_ofNat, Int.cast_one, Int.negOnePow_add, Int.negOnePow_def, Int.negOnePow_neg, Polynomial, Polynomial.Chebyshev.induct, S_add_two, S_sub_one, add_two, cast_add, cast_natCast, cast_neg, cast_ofNat, cast_one
-/
theorem S_eval_neg_two (n : Int) : (S R n).eval (-2) = n.negOnePow * (n + 1) := by
  induction n using Polynomial.Chebyshev.induct with
  | zero => simp
  | one => simp; norm_num
  | add_two n ih1 ih2 =>
    simp only [S_add_two, eval_sub, eval_mul, eval_X, ih1,
      Int.cast_add, Int.cast_natCast, Int.cast_one, neg_mul, ih2, Int.cast_ofNat, Int.negOnePow_add,
      Int.negOnePow_def 2]
    norm_cast
    norm_num
    ring
  | neg_add_one n ih1 ih2 =>
    simp only [S_sub_one, eval_sub, eval_mul, eval_X, mul_neg, ih1,
      Int.cast_neg, Int.cast_natCast, Int.negOnePow_neg, neg_mul, ih2, Int.cast_add, Int.cast_one,
      Int.cast_sub, sub_add_cancel, Int.negOnePow_sub, Int.negOnePow_add]
    norm_cast
    norm_num
    ring

/--
theorem `S_comp_two_mul_X` / 定理 `S_comp_two_mul_X`

English:
theorem S_comp_two_mul_X
  given: (n : Int)
  statement: (S R n).comp (2 * X) = U R n
  proof: by
  induction n using Polynomial.Chebyshev.induct with
  | zero => simp
  | one => simp
  | add_two n ih1 ih2 => simp_rw [U_add_two, S_add_two, sub_comp, mul_comp, X_comp, ih1, ih2]
  | neg_add_one n ih1 ih2 => simp_rw [U_sub_one, S_sub_one, sub_comp, mul_comp, X_comp, ih1, ih2]

中文:
定理 S_comp_two_mul_X
  条件: (n : 整数)
  结论: (S R n).comp (2 * X) = U R n
  证明: by
  induction n using Polynomial.Chebyshev.induct with
  | zero => simp
  | one => simp
  | add_two n ih1 ih2 => simp_rw [U_add_two, S_add_two, sub_comp, mul_comp, X_comp, ih1, ih2]
  | neg_add_one n ih1 ih2 => simp_rw [U_sub_one, S_sub_one, sub_comp, mul_comp, X_comp, ih1, ih2]

Depends on / 依赖: Chebyshev, Polynomial, Polynomial.Chebyshev.induct, S_add_two, S_sub_one, U_add_two, U_sub_one, X_comp, add_two, induct, mul_comp, neg_add_one, simp_rw, sub_comp
-/
theorem S_comp_two_mul_X (n : Int) : (S R n).comp (2 * X) = U R n := by
  induction n using Polynomial.Chebyshev.induct with
  | zero => simp
  | one => simp
  | add_two n ih1 ih2 => simp_rw [U_add_two, S_add_two, sub_comp, mul_comp, X_comp, ih1, ih2]
  | neg_add_one n ih1 ih2 => simp_rw [U_sub_one, S_sub_one, sub_comp, mul_comp, X_comp, ih1, ih2]

/--
theorem `S_sq_add_S_sq` / 定理 `S_sq_add_S_sq`

English:
theorem S_sq_add_S_sq
  given: (n : Int)
  statement: S R n ^ 2 + S R (n + 1) ^ 2 - X * S R n * S R (n + 1) = 1
  proof: by
  induction n with
  | zero => simp; ring
  | succ n ih =>
    have h₁ := S_add_two R n
    linear_combination (norm := ring_nf) (S R (2 + n) - S R n) * h₁ + ih
  | pred n ih =>
    have h₁ := S_sub_one R (-n)
    linear_combination (norm := ring_nf) (S R (-1 - n) - S R (1 - n)) * h₁ + ih

中文:
定理 S_sq_add_S_sq
  条件: (n : 整数)
  结论: S R n ^ 2 + S R (n + 1) ^ 2 - X * S R n * S R (n + 1) = 1
  证明: by
  induction n with
  | zero => simp; ring
  | succ n ih =>
    have h₁ := S_add_two R n
    linear_combination (norm := ring_nf) (S R (2 + n) - S R n) * h₁ + ih
  | pred n ih =>
    have h₁ := S_sub_one R (-n)
    linear_combination (norm := ring_nf) (S R (-1 - n) - S R (1 - n)) * h₁ + ih

Depends on / 依赖: S_add_two, S_sub_one, linear_combination, ring_nf
-/
theorem S_sq_add_S_sq (n : Int) : S R n ^ 2 + S R (n + 1) ^ 2 - X * S R n * S R (n + 1) = 1 := by
  induction n with
  | zero => simp; ring
  | succ n ih =>
    have h₁ := S_add_two R n
    linear_combination (norm := ring_nf) (S R (2 + n) - S R n) * h₁ + ih
  | pred n ih =>
    have h₁ := S_sub_one R (-n)
    linear_combination (norm := ring_nf) (S R (-1 - n) - S R (1 - n)) * h₁ + ih

/--
theorem `S_eq_U_comp_half_mul_X` / 定理 `S_eq_U_comp_half_mul_X`

English:
theorem S_eq_U_comp_half_mul_X
  given: [Invertible (2 : R)] (n : Int)
  proof: by
  have := congr_arg (·.comp (Polynomial.C ⅟2 * X)) (S_comp_two_mul_X R n)
  simp_rw [comp_assoc, mul_comp, ofNat_comp, X_comp, ← mul_assoc, ← C_eq_natCast, ← C_mul,
    Nat.cast_ofNat, mul_invOf_self', map_one, one_mul, comp_X] at this
  assumption

中文:
定理 S_eq_U_comp_half_mul_X
  条件: [可逆 (2 : R)] (n : 整数)
  证明: by
  have := congr_arg (·.comp (Polynomial.C ⅟2 * X)) (S_comp_two_mul_X R n)
  simp_rw [comp_assoc, mul_comp, ofNat_comp, X_comp, ← mul_assoc, ← C_eq_natCast, ← C_mul,
    Nat.cast_ofNat, mul_invOf_self', map_one, one_mul, comp_X] at this
  assumption

Depends on / 依赖: C_eq_natCast, C_mul, Nat.cast_ofNat, Polynomial, Polynomial.C, S_comp_two_mul_X, X_comp, cast_ofNat, comp_X, comp_assoc, congr_arg, map_one, mul_assoc, mul_comp, mul_invOf_self, ofNat_comp, one_mul, simp_rw
-/
theorem S_eq_U_comp_half_mul_X [Invertible (2 : R)] (n : Int) :
    S R n = (U R n).comp (Polynomial.C ⅟2 * X) := by
  have := congr_arg (·.comp (Polynomial.C ⅟2 * X)) (S_comp_two_mul_X R n)
  simp_rw [comp_assoc, mul_comp, ofNat_comp, X_comp, ← mul_assoc, ← C_eq_natCast, ← C_mul,
    Nat.cast_ofNat, mul_invOf_self', map_one, one_mul, comp_X] at this
  assumption

/--
theorem `S_eq_X_mul_S_add_C` / 定理 `S_eq_X_mul_S_add_C`

English:
theorem S_eq_X_mul_S_add_C
  given: (n : Int)
  statement: 2 * S R (n + 1) = X * S R n + C R (n + 1)
  proof: by
  induction n using Polynomial.Chebyshev.induct with
  | zero => simp [two_mul]
  | one => simp [S_two, C_two]; ring
  | add_two n ih1 ih2 =>
    have h₁ := S_add_two R (n + 1)
    have h₂ := S_add_two R n
    have h₃ := C_add_two R (n + 1)
    linear_combination (norm := ring_nf) -h₃ - (X : R[X]) * h₂ + 2 * h₁ + (X : R[X]) * ih1 - ih2
  | neg_add_one n ih1 ih2 =>
    have h₁ := S_add_two R (-n - 1)
    have h₂ := S_add_two R (-n)
    have h₃ := C_add_two R (-n)
    linear_combination (norm := ring_nf) -h₃ + 2 * h₂ - (X : R[X]) * h₁ - ih2 + (X : R[X]) * ih1

中文:
定理 S_eq_X_mul_S_add_C
  条件: (n : 整数)
  结论: 2 * S R (n + 1) = X * S R n + C R (n + 1)
  证明: by
  induction n using Polynomial.Chebyshev.induct with
  | zero => simp [two_mul]
  | one => simp [S_two, C_two]; ring
  | add_two n ih1 ih2 =>
    have h₁ := S_add_two R (n + 1)
    have h₂ := S_add_two R n
    have h₃ := C_add_two R (n + 1)
    linear_combination (norm := ring_nf) -h₃ - (X : R[X]) * h₂ + 2 * h₁ + (X : R[X]) * ih1 - ih2
  | neg_add_one n ih1 ih2 =>
    have h₁ := S_add_two R (-n - 1)
    have h₂ := S_add_two R (-n)
    have h₃ := C_add_two R (-n)
    linear_combination (norm := ring_nf) -h₃ + 2 * h₂ - (X : R[X]) * h₁ - ih2 + (X : R[X]) * ih1

Depends on / 依赖: C_add_two, C_two, Chebyshev, Polynomial, Polynomial.Chebyshev.induct, S_add_two, S_two, add_two, induct, linear_combination, neg_add_one, ring_nf, two_mul
-/
theorem S_eq_X_mul_S_add_C (n : Int) : 2 * S R (n + 1) = X * S R n + C R (n + 1) := by
  induction n using Polynomial.Chebyshev.induct with
  | zero => simp [two_mul]
  | one => simp [S_two, C_two]; ring
  | add_two n ih1 ih2 =>
    have h₁ := S_add_two R (n + 1)
    have h₂ := S_add_two R n
    have h₃ := C_add_two R (n + 1)
    linear_combination (norm := ring_nf) -h₃ - (X : R[X]) * h₂ + 2 * h₁ + (X : R[X]) * ih1 - ih2
  | neg_add_one n ih1 ih2 =>
    have h₁ := S_add_two R (-n - 1)
    have h₂ := S_add_two R (-n)
    have h₃ := C_add_two R (-n)
    linear_combination (norm := ring_nf) -h₃ + 2 * h₂ - (X : R[X]) * h₁ - ih2 + (X : R[X]) * ih1

/--
theorem `C_eq_S_sub_X_mul_S` / 定理 `C_eq_S_sub_X_mul_S`

English:
theorem C_eq_S_sub_X_mul_S
  given: (n : Int)
  statement: C R n = 2 * S R n - X * S R (n - 1)
  proof: by
  linear_combination (norm := ring_nf) - S_eq_X_mul_S_add_C R (n - 1)

中文:
定理 C_eq_S_sub_X_mul_S
  条件: (n : 整数)
  结论: C R n = 2 * S R n - X * S R (n - 1)
  证明: by
  linear_combination (norm := ring_nf) - S_eq_X_mul_S_add_C R (n - 1)

Depends on / 依赖: S_eq_X_mul_S_add_C, linear_combination, ring_nf
-/
theorem C_eq_S_sub_X_mul_S (n : Int) : C R n = 2 * S R n - X * S R (n - 1) := by
  linear_combination (norm := ring_nf) - S_eq_X_mul_S_add_C R (n - 1)

variable {R R'}

@[simp]
/--
theorem `map_T` / 定理 `map_T`

English:
theorem map_T
  given: (f : R ->+* R') (n : Int)
  statement: map f (T R n) = T R' n
  proof: by
  induction n using Polynomial.Chebyshev.induct with
  | zero => simp
  | one => simp
  | add_two n ih1 ih2 =>
    simp_rw [T_add_two, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_ofNat, map_X,
      ih1, ih2]
  | neg_add_one n ih1 ih2 =>
    simp_rw [T_sub_one, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_ofNat, map_X, ih1,
      ih2]

@[simp]

中文:
定理 map_T
  条件: (f : R ->+* R') (n : 整数)
  结论: map f (T R n) = T R' n
  证明: by
  induction n using Polynomial.Chebyshev.induct with
  | zero => simp
  | one => simp
  | add_two n ih1 ih2 =>
    simp_rw [T_add_two, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_ofNat, map_X,
      ih1, ih2]
  | neg_add_one n ih1 ih2 =>
    simp_rw [T_sub_one, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_ofNat, map_X, ih1,
      ih2]

@[simp]

Depends on / 依赖: Chebyshev, Polynomial, Polynomial.Chebyshev.induct, Polynomial.map_mul, Polynomial.map_ofNat, Polynomial.map_sub, T_add_two, T_sub_one, add_two, induct, map_X, map_mul, map_ofNat, map_sub, neg_add_one, simp_rw
-/
theorem map_T (f : R ->+* R') (n : Int) : map f (T R n) = T R' n := by
  induction n using Polynomial.Chebyshev.induct with
  | zero => simp
  | one => simp
  | add_two n ih1 ih2 =>
    simp_rw [T_add_two, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_ofNat, map_X,
      ih1, ih2]
  | neg_add_one n ih1 ih2 =>
    simp_rw [T_sub_one, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_ofNat, map_X, ih1,
      ih2]

@[simp]
/--
theorem `map_U` / 定理 `map_U`

English:
theorem map_U
  given: (f : R ->+* R') (n : Int)
  statement: map f (U R n) = U R' n
  proof: by
  induction n using Polynomial.Chebyshev.induct with
  | zero => simp
  | one => simp
  | add_two n ih1 ih2 =>
    simp_rw [U_add_two, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_ofNat, map_X, ih1,
      ih2]
  | neg_add_one n ih1 ih2 =>
    simp_rw [U_sub_one, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_ofNat, map_X, ih1,
      ih2]

@[simp]

中文:
定理 map_U
  条件: (f : R ->+* R') (n : 整数)
  结论: map f (U R n) = U R' n
  证明: by
  induction n using Polynomial.Chebyshev.induct with
  | zero => simp
  | one => simp
  | add_two n ih1 ih2 =>
    simp_rw [U_add_two, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_ofNat, map_X, ih1,
      ih2]
  | neg_add_one n ih1 ih2 =>
    simp_rw [U_sub_one, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_ofNat, map_X, ih1,
      ih2]

@[simp]

Depends on / 依赖: Chebyshev, Polynomial, Polynomial.Chebyshev.induct, Polynomial.map_mul, Polynomial.map_ofNat, Polynomial.map_sub, U_add_two, U_sub_one, add_two, induct, map_X, map_mul, map_ofNat, map_sub, neg_add_one, simp_rw
-/
theorem map_U (f : R ->+* R') (n : Int) : map f (U R n) = U R' n := by
  induction n using Polynomial.Chebyshev.induct with
  | zero => simp
  | one => simp
  | add_two n ih1 ih2 =>
    simp_rw [U_add_two, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_ofNat, map_X, ih1,
      ih2]
  | neg_add_one n ih1 ih2 =>
    simp_rw [U_sub_one, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_ofNat, map_X, ih1,
      ih2]

@[simp]
/--
theorem `map_C` / 定理 `map_C`

English:
theorem map_C
  given: (f : R ->+* R') (n : Int)
  statement: map f (C R n) = C R' n
  proof: by
  induction n using Polynomial.Chebyshev.induct with
  | zero => simp
  | one => simp
  | add_two n ih1 ih2 =>
    simp_rw [C_add_two, Polynomial.map_sub, Polynomial.map_mul, map_X, ih1, ih2]
  | neg_add_one n ih1 ih2 =>
    simp_rw [C_sub_one, Polynomial.map_sub, Polynomial.map_mul, map_X, ih1, ih2]

@[simp]

中文:
定理 map_C
  条件: (f : R ->+* R') (n : 整数)
  结论: map f (C R n) = C R' n
  证明: by
  induction n using Polynomial.Chebyshev.induct with
  | zero => simp
  | one => simp
  | add_two n ih1 ih2 =>
    simp_rw [C_add_two, Polynomial.map_sub, Polynomial.map_mul, map_X, ih1, ih2]
  | neg_add_one n ih1 ih2 =>
    simp_rw [C_sub_one, Polynomial.map_sub, Polynomial.map_mul, map_X, ih1, ih2]

@[simp]

Depends on / 依赖: C_add_two, C_sub_one, Chebyshev, Polynomial, Polynomial.Chebyshev.induct, Polynomial.map_mul, Polynomial.map_sub, add_two, induct, map_X, map_mul, map_sub, neg_add_one, simp_rw
-/
theorem map_C (f : R ->+* R') (n : Int) : map f (C R n) = C R' n := by
  induction n using Polynomial.Chebyshev.induct with
  | zero => simp
  | one => simp
  | add_two n ih1 ih2 =>
    simp_rw [C_add_two, Polynomial.map_sub, Polynomial.map_mul, map_X, ih1, ih2]
  | neg_add_one n ih1 ih2 =>
    simp_rw [C_sub_one, Polynomial.map_sub, Polynomial.map_mul, map_X, ih1, ih2]

@[simp]
/--
theorem `map_S` / 定理 `map_S`

English:
theorem map_S
  given: (f : R ->+* R') (n : Int)
  statement: map f (S R n) = S R' n
  proof: by
  induction n using Polynomial.Chebyshev.induct with
  | zero => simp
  | one => simp
  | add_two n ih1 ih2 =>
    simp_rw [S_add_two, Polynomial.map_sub, Polynomial.map_mul, map_X, ih1, ih2]
  | neg_add_one n ih1 ih2 =>
    simp_rw [S_sub_one, Polynomial.map_sub, Polynomial.map_mul, map_X, ih1, ih2]

@[simp]

中文:
定理 map_S
  条件: (f : R ->+* R') (n : 整数)
  结论: map f (S R n) = S R' n
  证明: by
  induction n using Polynomial.Chebyshev.induct with
  | zero => simp
  | one => simp
  | add_two n ih1 ih2 =>
    simp_rw [S_add_two, Polynomial.map_sub, Polynomial.map_mul, map_X, ih1, ih2]
  | neg_add_one n ih1 ih2 =>
    simp_rw [S_sub_one, Polynomial.map_sub, Polynomial.map_mul, map_X, ih1, ih2]

@[simp]

Depends on / 依赖: Chebyshev, Polynomial, Polynomial.Chebyshev.induct, Polynomial.map_mul, Polynomial.map_sub, S_add_two, S_sub_one, add_two, induct, map_X, map_mul, map_sub, neg_add_one, simp_rw
-/
theorem map_S (f : R ->+* R') (n : Int) : map f (S R n) = S R' n := by
  induction n using Polynomial.Chebyshev.induct with
  | zero => simp
  | one => simp
  | add_two n ih1 ih2 =>
    simp_rw [S_add_two, Polynomial.map_sub, Polynomial.map_mul, map_X, ih1, ih2]
  | neg_add_one n ih1 ih2 =>
    simp_rw [S_sub_one, Polynomial.map_sub, Polynomial.map_mul, map_X, ih1, ih2]

@[simp]
/--
theorem `aeval_T` / 定理 `aeval_T`

English:
theorem aeval_T
  given: [Algebra R R'] (x : R') (n : Int)
  statement: aeval x (T R n) = (T R' n).eval x
  proof: by
  rw [aeval_def]; rw [eval₂_eq_eval_map]; rw [map_T]

@[simp]

中文:
定理 aeval_T
  条件: [代数 R R'] (x : R') (n : 整数)
  结论: aeval x (T R n) = (T R' n).eval x
  证明: by
  rw [aeval_def]; rw [eval₂_eq_eval_map]; rw [map_T]

@[simp]

Depends on / 依赖: aeval_def, map_T
-/
theorem aeval_T [Algebra R R'] (x : R') (n : Int) : aeval x (T R n) = (T R' n).eval x := by
  rw [aeval_def]; rw [eval₂_eq_eval_map]; rw [map_T]

@[simp]
/--
theorem `aeval_U` / 定理 `aeval_U`

English:
theorem aeval_U
  given: [Algebra R R'] (x : R') (n : Int)
  statement: aeval x (U R n) = (U R' n).eval x
  proof: by
  rw [aeval_def]; rw [eval₂_eq_eval_map]; rw [map_U]

@[simp]

中文:
定理 aeval_U
  条件: [代数 R R'] (x : R') (n : 整数)
  结论: aeval x (U R n) = (U R' n).eval x
  证明: by
  rw [aeval_def]; rw [eval₂_eq_eval_map]; rw [map_U]

@[simp]

Depends on / 依赖: aeval_def, map_U
-/
theorem aeval_U [Algebra R R'] (x : R') (n : Int) : aeval x (U R n) = (U R' n).eval x := by
  rw [aeval_def]; rw [eval₂_eq_eval_map]; rw [map_U]

@[simp]
/--
theorem `aeval_C` / 定理 `aeval_C`

English:
theorem aeval_C
  given: [Algebra R R'] (x : R') (n : Int)
  statement: aeval x (C R n) = (C R' n).eval x
  proof: by
  rw [aeval_def]; rw [eval₂_eq_eval_map]; rw [map_C]

@[simp]

中文:
定理 aeval_C
  条件: [代数 R R'] (x : R') (n : 整数)
  结论: aeval x (C R n) = (C R' n).eval x
  证明: by
  rw [aeval_def]; rw [eval₂_eq_eval_map]; rw [map_C]

@[simp]

Depends on / 依赖: aeval_def, map_C
-/
theorem aeval_C [Algebra R R'] (x : R') (n : Int) : aeval x (C R n) = (C R' n).eval x := by
  rw [aeval_def]; rw [eval₂_eq_eval_map]; rw [map_C]

@[simp]
/--
theorem `aeval_S` / 定理 `aeval_S`

English:
theorem aeval_S
  given: [Algebra R R'] (x : R') (n : Int)
  statement: aeval x (S R n) = (S R' n).eval x
  proof: by
  rw [aeval_def]; rw [eval₂_eq_eval_map]; rw [map_S]

@[simp]

中文:
定理 aeval_S
  条件: [代数 R R'] (x : R') (n : 整数)
  结论: aeval x (S R n) = (S R' n).eval x
  证明: by
  rw [aeval_def]; rw [eval₂_eq_eval_map]; rw [map_S]

@[simp]

Depends on / 依赖: aeval_def, map_S
-/
theorem aeval_S [Algebra R R'] (x : R') (n : Int) : aeval x (S R n) = (S R' n).eval x := by
  rw [aeval_def]; rw [eval₂_eq_eval_map]; rw [map_S]

@[simp]
/--
theorem `algebraMap_eval_T` / 定理 `algebraMap_eval_T`

English:
theorem algebraMap_eval_T
  given: [Algebra R R'] (x : R) (n : Int)
  proof: by
  rw [← aeval_algebraMap_apply_eq_algebraMap_eval]; rw [aeval_T]

@[simp]

中文:
定理 algebraMap_eval_T
  条件: [代数 R R'] (x : R) (n : 整数)
  证明: by
  rw [← aeval_algebraMap_apply_eq_algebraMap_eval]; rw [aeval_T]

@[simp]

Depends on / 依赖: aeval_T, aeval_algebraMap_apply_eq_algebraMap_eval
-/
theorem algebraMap_eval_T [Algebra R R'] (x : R) (n : Int) :
    algebraMap R R' ((T R n).eval x) = (T R' n).eval (algebraMap R R' x) := by
  rw [← aeval_algebraMap_apply_eq_algebraMap_eval]; rw [aeval_T]

@[simp]
/--
theorem `algebraMap_eval_U` / 定理 `algebraMap_eval_U`

English:
theorem algebraMap_eval_U
  given: [Algebra R R'] (x : R) (n : Int)
  proof: by
  rw [← aeval_algebraMap_apply_eq_algebraMap_eval]; rw [aeval_U]

@[simp]

中文:
定理 algebraMap_eval_U
  条件: [代数 R R'] (x : R) (n : 整数)
  证明: by
  rw [← aeval_algebraMap_apply_eq_algebraMap_eval]; rw [aeval_U]

@[simp]

Depends on / 依赖: aeval_U, aeval_algebraMap_apply_eq_algebraMap_eval
-/
theorem algebraMap_eval_U [Algebra R R'] (x : R) (n : Int) :
    algebraMap R R' ((U R n).eval x) = (U R' n).eval (algebraMap R R' x) := by
  rw [← aeval_algebraMap_apply_eq_algebraMap_eval]; rw [aeval_U]

@[simp]
/--
theorem `algebraMap_eval_C` / 定理 `algebraMap_eval_C`

English:
theorem algebraMap_eval_C
  given: [Algebra R R'] (x : R) (n : Int)
  proof: by
  rw [← aeval_algebraMap_apply_eq_algebraMap_eval]; rw [aeval_C]

@[simp]

中文:
定理 algebraMap_eval_C
  条件: [代数 R R'] (x : R) (n : 整数)
  证明: by
  rw [← aeval_algebraMap_apply_eq_algebraMap_eval]; rw [aeval_C]

@[simp]

Depends on / 依赖: aeval_C, aeval_algebraMap_apply_eq_algebraMap_eval
-/
theorem algebraMap_eval_C [Algebra R R'] (x : R) (n : Int) :
    algebraMap R R' ((C R n).eval x) = (C R' n).eval (algebraMap R R' x) := by
  rw [← aeval_algebraMap_apply_eq_algebraMap_eval]; rw [aeval_C]

@[simp]
/--
theorem `algebraMap_eval_S` / 定理 `algebraMap_eval_S`

English:
theorem algebraMap_eval_S
  given: [Algebra R R'] (x : R) (n : Int)
  proof: by
  rw [← aeval_algebraMap_apply_eq_algebraMap_eval]; rw [aeval_S]

中文:
定理 algebraMap_eval_S
  条件: [代数 R R'] (x : R) (n : 整数)
  证明: by
  rw [← aeval_algebraMap_apply_eq_algebraMap_eval]; rw [aeval_S]

Depends on / 依赖: aeval_S, aeval_algebraMap_apply_eq_algebraMap_eval
-/
theorem algebraMap_eval_S [Algebra R R'] (x : R) (n : Int) :
    algebraMap R R' ((S R n).eval x) = (S R' n).eval (algebraMap R R' x) := by
  rw [← aeval_algebraMap_apply_eq_algebraMap_eval]; rw [aeval_S]

/--
theorem `T_derivative_eq_U` / 定理 `T_derivative_eq_U`

English:
theorem T_derivative_eq_U
  given: (n : Int)
  statement: derivative (T R n) = n * U R (n - 1)
  proof: by
  induction n using Polynomial.Chebyshev.induct with
  | zero => simp
  | one =>
    simp
  | add_two n ih1 ih2 =>
    have h₁ := congr_arg derivative (T_add_two R n)
    have h₂ := U_sub_one R n
    have h₃ := T_eq_U_sub_X_mul_U R (n + 1)
    simp only [derivative_sub, derivative_mul, derivative_ofNat, derivative_X] at h₁
    linear_combination (norm := (push_cast; ring_nf))
      h₁ - ih2 + 2 * (X : R[X]) * ih1 + 2 * h₃ - n * h₂
  | neg_add_one n ih1 ih2 =>
    have h₁ := congr_arg derivative (T_sub_one R (-n))
    have h₂ := U_sub_two R (-n)
    have h₃ := T_eq_U_sub_X_mul_U R (-n)
    simp only [derivative_sub, derivative_mul, derivative_ofNat, derivative_X] at h₁
    linear_combination (norm := (push_cast; ring_nf))
      -ih2 + 2 * (X : R[X]) * ih1 + h₁ + 2 * h₃ + (n + 1) * h₂

中文:
定理 T_derivative_eq_U
  条件: (n : 整数)
  结论: derivative (T R n) = n * U R (n - 1)
  证明: by
  induction n using Polynomial.Chebyshev.induct with
  | zero => simp
  | one =>
    simp
  | add_two n ih1 ih2 =>
    have h₁ := congr_arg derivative (T_add_two R n)
    have h₂ := U_sub_one R n
    have h₃ := T_eq_U_sub_X_mul_U R (n + 1)
    simp only [derivative_sub, derivative_mul, derivative_ofNat, derivative_X] at h₁
    linear_combination (norm := (push_cast; ring_nf))
      h₁ - ih2 + 2 * (X : R[X]) * ih1 + 2 * h₃ - n * h₂
  | neg_add_one n ih1 ih2 =>
    have h₁ := congr_arg derivative (T_sub_one R (-n))
    have h₂ := U_sub_two R (-n)
    have h₃ := T_eq_U_sub_X_mul_U R (-n)
    simp only [derivative_sub, derivative_mul, derivative_ofNat, derivative_X] at h₁
    linear_combination (norm := (push_cast; ring_nf))
      -ih2 + 2 * (X : R[X]) * ih1 + h₁ + 2 * h₃ + (n + 1) * h₂

Depends on / 依赖: Chebyshev, Polynomial, Polynomial.Chebyshev.induct, T_add_two, T_eq_U_sub_X_mul_U, T_sub_one, U_sub_one, U_sub_two, add_two, congr_arg, derivative, derivative_X, derivative_mul, derivative_ofNat, derivative_sub, induct, linear_combination, neg_add_one, ring_nf
-/
theorem T_derivative_eq_U (n : Int) : derivative (T R n) = n * U R (n - 1) := by
  induction n using Polynomial.Chebyshev.induct with
  | zero => simp
  | one =>
    simp
  | add_two n ih1 ih2 =>
    have h₁ := congr_arg derivative (T_add_two R n)
    have h₂ := U_sub_one R n
    have h₃ := T_eq_U_sub_X_mul_U R (n + 1)
    simp only [derivative_sub, derivative_mul, derivative_ofNat, derivative_X] at h₁
    linear_combination (norm := (push_cast; ring_nf))
      h₁ - ih2 + 2 * (X : R[X]) * ih1 + 2 * h₃ - n * h₂
  | neg_add_one n ih1 ih2 =>
    have h₁ := congr_arg derivative (T_sub_one R (-n))
    have h₂ := U_sub_two R (-n)
    have h₃ := T_eq_U_sub_X_mul_U R (-n)
    simp only [derivative_sub, derivative_mul, derivative_ofNat, derivative_X] at h₁
    linear_combination (norm := (push_cast; ring_nf))
      -ih2 + 2 * (X : R[X]) * ih1 + h₁ + 2 * h₃ + (n + 1) * h₂

/--
theorem `T_derivative_mem_span_T` / 定理 `T_derivative_mem_span_T`

English:
theorem T_derivative_mem_span_T
  given: (n : Nat)
  proof: by
  by_cases! hn : n = 0
  · simp [hn]
  rw [T_derivative_eq_U]; rw [← smul_eq_mul]; norm_cast
  refine Submodule.smul_of_tower_mem _ n ?_
  convert! U_mem_span_T R (n - 1) using 2 <;> grind

中文:
定理 T_derivative_mem_span_T
  条件: (n : 自然数)
  证明: by
  by_cases! hn : n = 0
  · simp [hn]
  rw [T_derivative_eq_U]; rw [← smul_eq_mul]; norm_cast
  refine Submodule.smul_of_tower_mem _ n ?_
  convert! U_mem_span_T R (n - 1) using 2 <;> grind

Depends on / 依赖: Submodule, Submodule.smul_of_tower_mem, T_derivative_eq_U, U_mem_span_T, convert, smul_eq_mul, smul_of_tower_mem
-/
theorem T_derivative_mem_span_T (n : Nat) :
    derivative (T R n) in Submodule.span Nat ((fun m : Nat => T R m) '' Set.Ico 0 n) := by
  by_cases! hn : n = 0
  · simp [hn]
  rw [T_derivative_eq_U]; rw [← smul_eq_mul]; norm_cast
  refine Submodule.smul_of_tower_mem _ n ?_
  convert! U_mem_span_T R (n - 1) using 2 <;> grind

/--
theorem `T_iterate_derivative_mem_span_T` / 定理 `T_iterate_derivative_mem_span_T`

English:
theorem T_iterate_derivative_mem_span_T
  given: (n k : Nat)
  proof: by
  induction k
  case zero =>
    rw [Function.iterate_zero_apply]
    exact Submodule.mem_span_of_mem ⟨n, by simp⟩
  case succ k ih =>
    rw [Function.iterate_succ_apply']
    suffices Submodule.span Nat ((fun m : Nat => derivative (T R m)) '' Set.Icc 0 (n - k)) <=
      Submodule.span Nat ((fun m : Nat => T R m) '' Set.Icc 0 (n - (k + 1))) by
      apply this
      convert! Submodule.apply_mem_span_image_of_mem_span (derivative.restrictScalars Nat) ih using 2
      simp [Set.image]
    refine Submodule.span_le.mpr (fun x hx => ?_)
    obtain ⟨m, hm, rfl⟩ := hx
    refine (Submodule.span_mono (by grind)) (T_derivative_mem_span_T (R := R) m)

中文:
定理 T_iterate_derivative_mem_span_T
  条件: (n k : 自然数)
  证明: by
  induction k
  case zero =>
    rw [Function.iterate_zero_apply]
    exact Submodule.mem_span_of_mem ⟨n, by simp⟩
  case succ k ih =>
    rw [Function.iterate_succ_apply']
    suffices Submodule.span Nat ((fun m : Nat => derivative (T R m)) '' Set.Icc 0 (n - k)) <=
      Submodule.span Nat ((fun m : Nat => T R m) '' Set.Icc 0 (n - (k + 1))) by
      apply this
      convert! Submodule.apply_mem_span_image_of_mem_span (derivative.restrictScalars Nat) ih using 2
      simp [Set.image]
    refine Submodule.span_le.mpr (fun x hx => ?_)
    obtain ⟨m, hm, rfl⟩ := hx
    refine (Submodule.span_mono (by grind)) (T_derivative_mem_span_T (R := R) m)

Depends on / 依赖: Function, Function.iterate_succ_apply, Function.iterate_zero_apply, Set.Icc, Set.image, Submodule, Submodule.apply_mem_span_image_of_mem_span, Submodule.mem_span_of_mem, Submodule.span, Submodule.span_le.mpr, apply_mem_span_image_of_mem_span, convert, derivative, derivative.restrictScalars, iterate_succ_apply, iterate_zero_apply, mem_span_of_mem, restrictScalars, span_le
-/
theorem T_iterate_derivative_mem_span_T (n k : Nat) :
    derivative^[k] (T R n) in Submodule.span Nat ((fun m : Nat => T R m) '' Set.Icc 0 (n - k)) := by
  induction k
  case zero =>
    rw [Function.iterate_zero_apply]
    exact Submodule.mem_span_of_mem ⟨n, by simp⟩
  case succ k ih =>
    rw [Function.iterate_succ_apply']
    suffices Submodule.span Nat ((fun m : Nat => derivative (T R m)) '' Set.Icc 0 (n - k)) <=
      Submodule.span Nat ((fun m : Nat => T R m) '' Set.Icc 0 (n - (k + 1))) by
      apply this
      convert! Submodule.apply_mem_span_image_of_mem_span (derivative.restrictScalars Nat) ih using 2
      simp [Set.image]
    refine Submodule.span_le.mpr (fun x hx => ?_)
    obtain ⟨m, hm, rfl⟩ := hx
    refine (Submodule.span_mono (by grind)) (T_derivative_mem_span_T (R := R) m)

/--
theorem `one_sub_X_sq_mul_derivative_T_eq_poly_in_T` / 定理 `one_sub_X_sq_mul_derivative_T_eq_poly_in_T`

English:
theorem one_sub_X_sq_mul_derivative_T_eq_poly_in_T
  given: (n : Int)
  proof: by
  have H₁ := one_sub_X_sq_mul_U_eq_pol_in_T R n
  have H₂ := T_derivative_eq_U (R := R) (n + 1)
  have h₁ := T_add_two R n
  linear_combination (norm := (push_cast; ring_nf))
    (-n - 1) * h₁ + (-(X : R[X]) ^ 2 + 1) * H₂ + (n + 1) * H₁

中文:
定理 one_sub_X_sq_mul_derivative_T_eq_poly_in_T
  条件: (n : 整数)
  证明: by
  have H₁ := one_sub_X_sq_mul_U_eq_pol_in_T R n
  have H₂ := T_derivative_eq_U (R := R) (n + 1)
  have h₁ := T_add_two R n
  linear_combination (norm := (push_cast; ring_nf))
    (-n - 1) * h₁ + (-(X : R[X]) ^ 2 + 1) * H₂ + (n + 1) * H₁

Depends on / 依赖: T_add_two, T_derivative_eq_U, linear_combination, one_sub_X_sq_mul_U_eq_pol_in_T, ring_nf
-/
theorem one_sub_X_sq_mul_derivative_T_eq_poly_in_T (n : Int) :
    (1 - X ^ 2) * derivative (T R (n + 1)) = (n + 1 : R[X]) * (T R n - X * T R (n + 1)) := by
  have H₁ := one_sub_X_sq_mul_U_eq_pol_in_T R n
  have H₂ := T_derivative_eq_U (R := R) (n + 1)
  have h₁ := T_add_two R n
  linear_combination (norm := (push_cast; ring_nf))
    (-n - 1) * h₁ + (-(X : R[X]) ^ 2 + 1) * H₂ + (n + 1) * H₁

/--
theorem `add_one_mul_T_eq_poly_in_U` / 定理 `add_one_mul_T_eq_poly_in_U`

English:
theorem add_one_mul_T_eq_poly_in_U
  given: (n : Int)
  proof: by
have h₁ := congr_arg derivative T_eq_X_mul_T_sub_pol_U R n
  simp only [derivative_sub, derivative_mul, derivative_X, derivative_one, derivative_X_pow,
    T_derivative_eq_U, C_eq_natCast] at h₁
  have h₂ := T_eq_U_sub_X_mul_U R (n + 1)
  linear_combination (norm := (push_cast; ring_nf))
    h₁ + (n + 2) * h₂

中文:
定理 add_one_mul_T_eq_poly_in_U
  条件: (n : 整数)
  证明: by
have h₁ := congr_arg derivative T_eq_X_mul_T_sub_pol_U R n
  simp only [derivative_sub, derivative_mul, derivative_X, derivative_one, derivative_X_pow,
    T_derivative_eq_U, C_eq_natCast] at h₁
  have h₂ := T_eq_U_sub_X_mul_U R (n + 1)
  linear_combination (norm := (push_cast; ring_nf))
    h₁ + (n + 2) * h₂

Depends on / 依赖: C_eq_natCast, T_derivative_eq_U, T_eq_U_sub_X_mul_U, T_eq_X_mul_T_sub_pol_U, congr_arg, derivative, derivative_X, derivative_X_pow, derivative_mul, derivative_one, derivative_sub, linear_combination, ring_nf
-/
theorem add_one_mul_T_eq_poly_in_U (n : Int) :
    ((n : R[X]) + 1) * T R (n + 1) = X * U R n - (1 - X ^ 2) * derivative (U R n) := by
have h₁ := congr_arg derivative T_eq_X_mul_T_sub_pol_U R n
  simp only [derivative_sub, derivative_mul, derivative_X, derivative_one, derivative_X_pow,
    T_derivative_eq_U, C_eq_natCast] at h₁
  have h₂ := T_eq_U_sub_X_mul_U R (n + 1)
  linear_combination (norm := (push_cast; ring_nf))
    h₁ + (n + 2) * h₂

/--
theorem `add_one_mul_self_mul_T_eq_poly_in_T` / 定理 `add_one_mul_self_mul_T_eq_poly_in_T`

English:
theorem add_one_mul_self_mul_T_eq_poly_in_T
  given: (n : Int)
  proof: by
  have h := T_eq_X_mul_U_sub_U (R := R) (n - 1)
  rw [T_derivative_eq_U]; rw [T_derivative_eq_U]
  linear_combination (norm := (push_cast; ring_nf))
    (n + 1) * n * h

中文:
定理 add_one_mul_self_mul_T_eq_poly_in_T
  条件: (n : 整数)
  证明: by
  have h := T_eq_X_mul_U_sub_U (R := R) (n - 1)
  rw [T_derivative_eq_U]; rw [T_derivative_eq_U]
  linear_combination (norm := (push_cast; ring_nf))
    (n + 1) * n * h

Depends on / 依赖: T_derivative_eq_U, T_eq_X_mul_U_sub_U, linear_combination, ring_nf
-/
theorem add_one_mul_self_mul_T_eq_poly_in_T (n : Int) :
    ((n + 1) * n : R[X]) * (T R (n + 1)) =
    (n : R[X]) * X * derivative (T R (n + 1)) - (n + 1 : R[X]) * derivative (T R n) := by
  have h := T_eq_X_mul_U_sub_U (R := R) (n - 1)
  rw [T_derivative_eq_U]; rw [T_derivative_eq_U]
  linear_combination (norm := (push_cast; ring_nf))
    (n + 1) * n * h

/--
theorem `one_sub_X_sq_mul_derivative_derivative_T_eq_poly_in_T` / 定理 `one_sub_X_sq_mul_derivative_derivative_T_eq_poly_in_T`

English:
theorem one_sub_X_sq_mul_derivative_derivative_T_eq_poly_in_T
  given: (n : Int)
  proof: by
have h₁ := congr_arg derivative one_sub_X_sq_mul_derivative_T_eq_poly_in_T (R := R) (n - 1)
  simp only [derivative_sub, derivative_mul, derivative_X, derivative_one, derivative_X_pow,
    C_eq_natCast, sub_add_cancel, Int.cast_sub, Int.cast_one, derivative_intCast] at h₁
  have h₂ := add_one_mul_self_mul_T_eq_poly_in_T (R := R) (n - 1)
  rw [Function.iterate_succ]; rw [Function.iterate_one]; rw [Function.comp_apply]
  linear_combination (norm := (push_cast; ring_nf))
    h₁ + h₂

中文:
定理 one_sub_X_sq_mul_derivative_derivative_T_eq_poly_in_T
  条件: (n : 整数)
  证明: by
have h₁ := congr_arg derivative one_sub_X_sq_mul_derivative_T_eq_poly_in_T (R := R) (n - 1)
  simp only [derivative_sub, derivative_mul, derivative_X, derivative_one, derivative_X_pow,
    C_eq_natCast, sub_add_cancel, Int.cast_sub, Int.cast_one, derivative_intCast] at h₁
  have h₂ := add_one_mul_self_mul_T_eq_poly_in_T (R := R) (n - 1)
  rw [Function.iterate_succ]; rw [Function.iterate_one]; rw [Function.comp_apply]
  linear_combination (norm := (push_cast; ring_nf))
    h₁ + h₂

Depends on / 依赖: C_eq_natCast, Function, Function.comp_apply, Function.iterate_one, Function.iterate_succ, Int.cast_one, Int.cast_sub, add_one_mul_self_mul_T_eq_poly_in_T, cast_one, cast_sub, comp_apply, congr_arg, derivative, derivative_X, derivative_X_pow, derivative_intCast, derivative_mul, derivative_one, derivative_sub, iterate_one
-/
theorem one_sub_X_sq_mul_derivative_derivative_T_eq_poly_in_T (n : Int) :
    (1 - X ^ 2) * derivative^[2] (T R n) = X * derivative (T R n) - (n ^ 2 : R[X]) * T R n := by
have h₁ := congr_arg derivative one_sub_X_sq_mul_derivative_T_eq_poly_in_T (R := R) (n - 1)
  simp only [derivative_sub, derivative_mul, derivative_X, derivative_one, derivative_X_pow,
    C_eq_natCast, sub_add_cancel, Int.cast_sub, Int.cast_one, derivative_intCast] at h₁
  have h₂ := add_one_mul_self_mul_T_eq_poly_in_T (R := R) (n - 1)
  rw [Function.iterate_succ]; rw [Function.iterate_one]; rw [Function.comp_apply]
  linear_combination (norm := (push_cast; ring_nf))
    h₁ + h₂

/--
theorem `one_sub_X_sq_mul_derivative_derivative_U_eq_poly_in_U` / 定理 `one_sub_X_sq_mul_derivative_derivative_U_eq_poly_in_U`

English:
theorem one_sub_X_sq_mul_derivative_derivative_U_eq_poly_in_U
  given: (n : Int)
  proof: by
have h := congr_arg derivative add_one_mul_T_eq_poly_in_U (R := R) n
  simp only [derivative_add, derivative_sub, derivative_mul, derivative_X, derivative_one,
    derivative_X_pow, derivative_intCast, C_eq_natCast, T_derivative_eq_U] at h
  rw [Function.iterate_succ]; rw [Function.iterate_one]; rw [Function.comp_apply]
  linear_combination (norm := (push_cast; ring_nf)) h

中文:
定理 one_sub_X_sq_mul_derivative_derivative_U_eq_poly_in_U
  条件: (n : 整数)
  证明: by
have h := congr_arg derivative add_one_mul_T_eq_poly_in_U (R := R) n
  simp only [derivative_add, derivative_sub, derivative_mul, derivative_X, derivative_one,
    derivative_X_pow, derivative_intCast, C_eq_natCast, T_derivative_eq_U] at h
  rw [Function.iterate_succ]; rw [Function.iterate_one]; rw [Function.comp_apply]
  linear_combination (norm := (push_cast; ring_nf)) h

Depends on / 依赖: C_eq_natCast, Function, Function.comp_apply, Function.iterate_one, Function.iterate_succ, T_derivative_eq_U, add_one_mul_T_eq_poly_in_U, comp_apply, congr_arg, derivative, derivative_X, derivative_X_pow, derivative_add, derivative_intCast, derivative_mul, derivative_one, derivative_sub, iterate_one, iterate_succ, linear_combination
-/
theorem one_sub_X_sq_mul_derivative_derivative_U_eq_poly_in_U (n : Int) :
    (1 - X ^ 2) * derivative^[2] (U R n) =
      3 * X * derivative (U R n) - ((n + 2) * n : R[X]) * U R n := by
have h := congr_arg derivative add_one_mul_T_eq_poly_in_U (R := R) n
  simp only [derivative_add, derivative_sub, derivative_mul, derivative_X, derivative_one,
    derivative_X_pow, derivative_intCast, C_eq_natCast, T_derivative_eq_U] at h
  rw [Function.iterate_succ]; rw [Function.iterate_one]; rw [Function.comp_apply]
  linear_combination (norm := (push_cast; ring_nf)) h

/--
theorem `one_sub_X_sq_mul_iterate_derivative_T_eq_poly_in_T` / 定理 `one_sub_X_sq_mul_iterate_derivative_T_eq_poly_in_T`

English:
theorem one_sub_X_sq_mul_iterate_derivative_T_eq_poly_in_T
  given: (n : Int) (k : Nat)
  proof: by
have h := congr_arg derivative^[k] one_sub_X_sq_mul_derivative_derivative_T_eq_poly_in_T
    (R := R) n
  norm_cast at h
  rw [sub_mul]; rw [iterate_derivative_sub]; rw [one_mul]; rw [← Function.iterate_add_apply]; rw [mul_comm (X ^ 2)]; rw [iterate_derivative_sub]; rw [mul_comm X]; rw [iterate_derivative_intCast_mul]; rw [iterate_derivative_derivative_mul_X_sq]; rw [iterate_derivative_derivative_mul_X] at h
  linear_combination (norm := (push_cast; ring_nf)) h
  cases k <;> grind

中文:
定理 one_sub_X_sq_mul_iterate_derivative_T_eq_poly_in_T
  条件: (n : 整数) (k : 自然数)
  证明: by
have h := congr_arg derivative^[k] one_sub_X_sq_mul_derivative_derivative_T_eq_poly_in_T
    (R := R) n
  norm_cast at h
  rw [sub_mul]; rw [iterate_derivative_sub]; rw [one_mul]; rw [← Function.iterate_add_apply]; rw [mul_comm (X ^ 2)]; rw [iterate_derivative_sub]; rw [mul_comm X]; rw [iterate_derivative_intCast_mul]; rw [iterate_derivative_derivative_mul_X_sq]; rw [iterate_derivative_derivative_mul_X] at h
  linear_combination (norm := (push_cast; ring_nf)) h
  cases k <;> grind

Depends on / 依赖: Function, Function.iterate_add_apply, congr_arg, derivative, iterate_add_apply, iterate_derivative_derivative_mul_X, iterate_derivative_derivative_mul_X_sq, iterate_derivative_intCast_mul, iterate_derivative_sub, linear_combination, mul_comm, one_mul, one_sub_X_sq_mul_derivative_derivative_T_eq_poly_in_T, ring_nf, sub_mul
-/
theorem one_sub_X_sq_mul_iterate_derivative_T_eq_poly_in_T (n : Int) (k : Nat) :
    (1 - X ^ 2) * derivative^[k + 2] (T R n) =
      (2 * k + 1 : R[X]) * X * derivative^[k + 1] (T R n) -
      (n ^ 2 - k ^ 2 : R[X]) * derivative^[k] (T R n) := by
have h := congr_arg derivative^[k] one_sub_X_sq_mul_derivative_derivative_T_eq_poly_in_T
    (R := R) n
  norm_cast at h
  rw [sub_mul]; rw [iterate_derivative_sub]; rw [one_mul]; rw [← Function.iterate_add_apply]; rw [mul_comm (X ^ 2)]; rw [iterate_derivative_sub]; rw [mul_comm X]; rw [iterate_derivative_intCast_mul]; rw [iterate_derivative_derivative_mul_X_sq]; rw [iterate_derivative_derivative_mul_X] at h
  linear_combination (norm := (push_cast; ring_nf)) h
  cases k <;> grind

/--
theorem `one_sub_X_sq_mul_iterate_derivative_U_eq_poly_in_U` / 定理 `one_sub_X_sq_mul_iterate_derivative_U_eq_poly_in_U`

English:
theorem one_sub_X_sq_mul_iterate_derivative_U_eq_poly_in_U
  given: (n : Int) (k : Nat)
  proof: by
have h := congr_arg derivative^[k] one_sub_X_sq_mul_derivative_derivative_U_eq_poly_in_U
    (R := R) n
  norm_cast at h
  rw [sub_mul]; rw [iterate_derivative_sub]; rw [one_mul]; rw [← Function.iterate_add_apply]; rw [mul_comm (X ^ 2)]; rw [iterate_derivative_sub]; rw [mul_assoc 3]; rw [← Nat.cast_three]; rw [iterate_derivative_natCast_mul]; rw [mul_comm X]; rw [iterate_derivative_intCast_mul]; rw [iterate_derivative_derivative_mul_X_sq]; rw [iterate_derivative_derivative_mul_X] at h
  linear_combination (norm := (push_cast; ring_nf)) h
  cases k <;> grind

中文:
定理 one_sub_X_sq_mul_iterate_derivative_U_eq_poly_in_U
  条件: (n : 整数) (k : 自然数)
  证明: by
have h := congr_arg derivative^[k] one_sub_X_sq_mul_derivative_derivative_U_eq_poly_in_U
    (R := R) n
  norm_cast at h
  rw [sub_mul]; rw [iterate_derivative_sub]; rw [one_mul]; rw [← Function.iterate_add_apply]; rw [mul_comm (X ^ 2)]; rw [iterate_derivative_sub]; rw [mul_assoc 3]; rw [← Nat.cast_three]; rw [iterate_derivative_natCast_mul]; rw [mul_comm X]; rw [iterate_derivative_intCast_mul]; rw [iterate_derivative_derivative_mul_X_sq]; rw [iterate_derivative_derivative_mul_X] at h
  linear_combination (norm := (push_cast; ring_nf)) h
  cases k <;> grind

Depends on / 依赖: Function, Function.iterate_add_apply, Nat.cast_three, cast_three, congr_arg, derivative, iterate_add_apply, iterate_derivative_derivative_mul_X, iterate_derivative_derivative_mul_X_sq, iterate_derivative_intCast_mul, iterate_derivative_natCast_mul, iterate_derivative_sub, linear_combinat, mul_assoc, mul_comm, one_mul, one_sub_X_sq_mul_derivative_derivative_U_eq_poly_in_U, sub_mul
-/
theorem one_sub_X_sq_mul_iterate_derivative_U_eq_poly_in_U (n : Int) (k : Nat) :
    (1 - X ^ 2) * derivative^[k + 2] (U R n) =
      (2 * k + 3 : R[X]) * X * derivative^[k + 1] (U R n) -
      ((n + 1) ^ 2 - (k + 1) ^ 2 : R[X]) * derivative^[k] (U R n) := by
have h := congr_arg derivative^[k] one_sub_X_sq_mul_derivative_derivative_U_eq_poly_in_U
    (R := R) n
  norm_cast at h
  rw [sub_mul]; rw [iterate_derivative_sub]; rw [one_mul]; rw [← Function.iterate_add_apply]; rw [mul_comm (X ^ 2)]; rw [iterate_derivative_sub]; rw [mul_assoc 3]; rw [← Nat.cast_three]; rw [iterate_derivative_natCast_mul]; rw [mul_comm X]; rw [iterate_derivative_intCast_mul]; rw [iterate_derivative_derivative_mul_X_sq]; rw [iterate_derivative_derivative_mul_X] at h
  linear_combination (norm := (push_cast; ring_nf)) h
  cases k <;> grind

/--
theorem `one_sub_X_sq_mul_iterate_derivative_T_eval` / 定理 `one_sub_X_sq_mul_iterate_derivative_T_eval`

English:
theorem one_sub_X_sq_mul_iterate_derivative_T_eval
  given: (n : Int) (k : Nat) (x : R)
  proof: by
have h := congr_arg (fun (p : R[X]) => p.eval x)
    one_sub_X_sq_mul_iterate_derivative_T_eq_poly_in_T n k
  simp only [eval_mul, eval_sub, eval_one, eval_pow,
    eval_X, eval_add, eval_ofNat, eval_natCast, eval_intCast] at h
  linear_combination (norm := (push_cast; ring_nf)) h

中文:
定理 one_sub_X_sq_mul_iterate_derivative_T_eval
  条件: (n : 整数) (k : 自然数) (x : R)
  证明: by
have h := congr_arg (fun (p : R[X]) => p.eval x)
    one_sub_X_sq_mul_iterate_derivative_T_eq_poly_in_T n k
  simp only [eval_mul, eval_sub, eval_one, eval_pow,
    eval_X, eval_add, eval_ofNat, eval_natCast, eval_intCast] at h
  linear_combination (norm := (push_cast; ring_nf)) h

Depends on / 依赖: congr_arg, eval_X, eval_add, eval_intCast, eval_mul, eval_natCast, eval_ofNat, eval_one, eval_pow, eval_sub, linear_combination, one_sub_X_sq_mul_iterate_derivative_T_eq_poly_in_T, p.eval, ring_nf
-/
theorem one_sub_X_sq_mul_iterate_derivative_T_eval (n : Int) (k : Nat) (x : R) :
    (1 - x ^ 2) * (derivative^[k + 2] (T R n)).eval x =
      (2 * k + 1) * x * (derivative^[k + 1] (T R n)).eval x -
      (n ^ 2 - k ^ 2) * (derivative^[k] (T R n)).eval x := by
have h := congr_arg (fun (p : R[X]) => p.eval x)
    one_sub_X_sq_mul_iterate_derivative_T_eq_poly_in_T n k
  simp only [eval_mul, eval_sub, eval_one, eval_pow,
    eval_X, eval_add, eval_ofNat, eval_natCast, eval_intCast] at h
  linear_combination (norm := (push_cast; ring_nf)) h

/--
theorem `one_sub_X_sq_mul_iterate_derivative_U_eval` / 定理 `one_sub_X_sq_mul_iterate_derivative_U_eval`

English:
theorem one_sub_X_sq_mul_iterate_derivative_U_eval
  given: (n : Int) (k : Nat) (x : R)
  proof: by
have h := congr_arg (fun (p : R[X]) => p.eval x)
    one_sub_X_sq_mul_iterate_derivative_U_eq_poly_in_U n k
  simp only [eval_mul, eval_sub, eval_one, eval_pow,
    eval_X, eval_add, eval_ofNat, eval_natCast, eval_intCast] at h
  linear_combination (norm := (push_cast; ring_nf)) h

中文:
定理 one_sub_X_sq_mul_iterate_derivative_U_eval
  条件: (n : 整数) (k : 自然数) (x : R)
  证明: by
have h := congr_arg (fun (p : R[X]) => p.eval x)
    one_sub_X_sq_mul_iterate_derivative_U_eq_poly_in_U n k
  simp only [eval_mul, eval_sub, eval_one, eval_pow,
    eval_X, eval_add, eval_ofNat, eval_natCast, eval_intCast] at h
  linear_combination (norm := (push_cast; ring_nf)) h

Depends on / 依赖: congr_arg, eval_X, eval_add, eval_intCast, eval_mul, eval_natCast, eval_ofNat, eval_one, eval_pow, eval_sub, linear_combination, one_sub_X_sq_mul_iterate_derivative_U_eq_poly_in_U, p.eval, ring_nf
-/
theorem one_sub_X_sq_mul_iterate_derivative_U_eval (n : Int) (k : Nat) (x : R) :
    (1 - x ^ 2) * (derivative^[k + 2] (U R n)).eval x =
      (2 * k + 3) * x * (derivative^[k + 1] (U R n)).eval x -
      ((n + 1) ^ 2 - (k + 1) ^ 2) * (derivative^[k] (U R n)).eval x := by
have h := congr_arg (fun (p : R[X]) => p.eval x)
    one_sub_X_sq_mul_iterate_derivative_U_eq_poly_in_U n k
  simp only [eval_mul, eval_sub, eval_one, eval_pow,
    eval_X, eval_add, eval_ofNat, eval_natCast, eval_intCast] at h
  linear_combination (norm := (push_cast; ring_nf)) h

/--
theorem `iterate_derivative_T_eval_one_recurrence` / 定理 `iterate_derivative_T_eval_one_recurrence`

English:
theorem iterate_derivative_T_eval_one_recurrence
  given: (n : Int) (k : Nat)
  proof: by
  have h := one_sub_X_sq_mul_iterate_derivative_T_eval (R := R) n k 1
  rw [one_pow]; rw [sub_self]; rw [zero_mul]; rw [mul_one] at h
  exact sub_eq_zero.mp h.symm

中文:
定理 iterate_derivative_T_eval_one_recurrence
  条件: (n : 整数) (k : 自然数)
  证明: by
  have h := one_sub_X_sq_mul_iterate_derivative_T_eval (R := R) n k 1
  rw [one_pow]; rw [sub_self]; rw [zero_mul]; rw [mul_one] at h
  exact sub_eq_zero.mp h.symm

Depends on / 依赖: h.symm, mul_one, one_pow, one_sub_X_sq_mul_iterate_derivative_T_eval, sub_eq_zero, sub_eq_zero.mp, sub_self, zero_mul
-/
theorem iterate_derivative_T_eval_one_recurrence (n : Int) (k : Nat) :
    (2 * k + 1) * (derivative^[k + 1] (T R n)).eval 1 =
      (n ^ 2 - k ^ 2) * (derivative^[k] (T R n)).eval 1 := by
  have h := one_sub_X_sq_mul_iterate_derivative_T_eval (R := R) n k 1
  rw [one_pow]; rw [sub_self]; rw [zero_mul]; rw [mul_one] at h
  exact sub_eq_zero.mp h.symm

/--
theorem `iterate_derivative_U_eval_one_recurrence` / 定理 `iterate_derivative_U_eval_one_recurrence`

English:
theorem iterate_derivative_U_eval_one_recurrence
  given: (n : Int) (k : Nat)
  proof: by
  have h := one_sub_X_sq_mul_iterate_derivative_U_eval (R := R) n k 1
  rw [one_pow]; rw [sub_self]; rw [zero_mul]; rw [mul_one] at h
  exact sub_eq_zero.mp h.symm

中文:
定理 iterate_derivative_U_eval_one_recurrence
  条件: (n : 整数) (k : 自然数)
  证明: by
  have h := one_sub_X_sq_mul_iterate_derivative_U_eval (R := R) n k 1
  rw [one_pow]; rw [sub_self]; rw [zero_mul]; rw [mul_one] at h
  exact sub_eq_zero.mp h.symm

Depends on / 依赖: h.symm, mul_one, one_pow, one_sub_X_sq_mul_iterate_derivative_U_eval, sub_eq_zero, sub_eq_zero.mp, sub_self, zero_mul
-/
theorem iterate_derivative_U_eval_one_recurrence (n : Int) (k : Nat) :
    (2 * k + 3) * (derivative^[k + 1] (U R n)).eval 1 =
      ((n + 1) ^ 2 - (k + 1) ^ 2) * (derivative^[k] (U R n)).eval 1 := by
  have h := one_sub_X_sq_mul_iterate_derivative_U_eval (R := R) n k 1
  rw [one_pow]; rw [sub_self]; rw [zero_mul]; rw [mul_one] at h
  exact sub_eq_zero.mp h.symm

/--
theorem `iterate_derivative_T_eval_zero_recurrence` / 定理 `iterate_derivative_T_eval_zero_recurrence`

English:
theorem iterate_derivative_T_eval_zero_recurrence
  given: (n : Int) (k : Nat)
  proof: by
  have h := one_sub_X_sq_mul_iterate_derivative_T_eval (R := R) n k 0
  rw [zero_pow two_ne_zero]; rw [sub_zero]; rw [one_mul]; rw [mul_zero]; rw [zero_mul]; rw [zero_sub] at h
  linear_combination (norm := (push_cast; ring_nf)) h

中文:
定理 iterate_derivative_T_eval_zero_recurrence
  条件: (n : 整数) (k : 自然数)
  证明: by
  have h := one_sub_X_sq_mul_iterate_derivative_T_eval (R := R) n k 0
  rw [zero_pow two_ne_zero]; rw [sub_zero]; rw [one_mul]; rw [mul_zero]; rw [zero_mul]; rw [zero_sub] at h
  linear_combination (norm := (push_cast; ring_nf)) h

Depends on / 依赖: linear_combination, mul_zero, one_mul, one_sub_X_sq_mul_iterate_derivative_T_eval, ring_nf, sub_zero, two_ne_zero, zero_mul, zero_pow, zero_sub
-/
theorem iterate_derivative_T_eval_zero_recurrence (n : Int) (k : Nat) :
    (derivative^[k + 2] (T R n)).eval 0 =
      -(n ^ 2 - k ^ 2) * (derivative^[k] (T R n)).eval 0 := by
  have h := one_sub_X_sq_mul_iterate_derivative_T_eval (R := R) n k 0
  rw [zero_pow two_ne_zero]; rw [sub_zero]; rw [one_mul]; rw [mul_zero]; rw [zero_mul]; rw [zero_sub] at h
  linear_combination (norm := (push_cast; ring_nf)) h

/--
theorem `iterate_derivative_U_eval_zero_recurrence` / 定理 `iterate_derivative_U_eval_zero_recurrence`

English:
theorem iterate_derivative_U_eval_zero_recurrence
  given: (n : Int) (k : Nat)
  proof: by
  have h := one_sub_X_sq_mul_iterate_derivative_U_eval (R := R) n k 0
  rw [zero_pow two_ne_zero]; rw [sub_zero]; rw [one_mul]; rw [mul_zero]; rw [zero_mul]; rw [zero_sub] at h
  linear_combination (norm := (push_cast; ring_nf)) h

中文:
定理 iterate_derivative_U_eval_zero_recurrence
  条件: (n : 整数) (k : 自然数)
  证明: by
  have h := one_sub_X_sq_mul_iterate_derivative_U_eval (R := R) n k 0
  rw [zero_pow two_ne_zero]; rw [sub_zero]; rw [one_mul]; rw [mul_zero]; rw [zero_mul]; rw [zero_sub] at h
  linear_combination (norm := (push_cast; ring_nf)) h

Depends on / 依赖: linear_combination, mul_zero, one_mul, one_sub_X_sq_mul_iterate_derivative_U_eval, ring_nf, sub_zero, two_ne_zero, zero_mul, zero_pow, zero_sub
-/
theorem iterate_derivative_U_eval_zero_recurrence (n : Int) (k : Nat) :
    (derivative^[k + 2] (U R n)).eval 0 =
      -((n + 1) ^ 2 - (k + 1) ^ 2) * (derivative^[k] (U R n)).eval 0 := by
  have h := one_sub_X_sq_mul_iterate_derivative_U_eval (R := R) n k 0
  rw [zero_pow two_ne_zero]; rw [sub_zero]; rw [one_mul]; rw [mul_zero]; rw [zero_mul]; rw [zero_sub] at h
  linear_combination (norm := (push_cast; ring_nf)) h

/--
theorem `iterate_derivative_T_eval_one` / 定理 `iterate_derivative_T_eval_one`

English:
theorem iterate_derivative_T_eval_one
  given: (n : Int) (k : Nat)
  proof: by
  induction k
  case zero => simp
  case succ k ih =>
    push_cast at ih ⊢
    rw [Finset.range_add_one]; rw [Finset.prod_insert Finset.notMem_range_self]; rw [mul_comm (2 * _ + 1)]; rw [mul_assoc]; rw [iterate_derivative_T_eval_one_recurrence]; rw [← mul_assoc]; rw [mul_comm _ (_ ^ 2 - _ ^ 2)]; rw [mul_assoc]; rw [ih]; rw [Finset.prod_insert Finset.notMem_range_self]

中文:
定理 iterate_derivative_T_eval_one
  条件: (n : 整数) (k : 自然数)
  证明: by
  induction k
  case zero => simp
  case succ k ih =>
    push_cast at ih ⊢
    rw [Finset.range_add_one]; rw [Finset.prod_insert Finset.notMem_range_self]; rw [mul_comm (2 * _ + 1)]; rw [mul_assoc]; rw [iterate_derivative_T_eval_one_recurrence]; rw [← mul_assoc]; rw [mul_comm _ (_ ^ 2 - _ ^ 2)]; rw [mul_assoc]; rw [ih]; rw [Finset.prod_insert Finset.notMem_range_self]

Depends on / 依赖: Finset, Finset.notMem_range_self, Finset.prod_insert, Finset.range_add_one, iterate_derivative_T_eval_one_recurrence, mul_assoc, mul_comm, notMem_range_self, prod_insert, range_add_one
-/
theorem iterate_derivative_T_eval_one (n : Int) (k : Nat) :
    (∏ l in Finset.range k, (2 * l + 1)) * (derivative^[k] (T R n)).eval 1 =
      ∏ l in Finset.range k, (n ^ 2 - l ^ 2) := by
  induction k
  case zero => simp
  case succ k ih =>
    push_cast at ih ⊢
    rw [Finset.range_add_one]; rw [Finset.prod_insert Finset.notMem_range_self]; rw [mul_comm (2 * _ + 1)]; rw [mul_assoc]; rw [iterate_derivative_T_eval_one_recurrence]; rw [← mul_assoc]; rw [mul_comm _ (_ ^ 2 - _ ^ 2)]; rw [mul_assoc]; rw [ih]; rw [Finset.prod_insert Finset.notMem_range_self]

/--
theorem `iterate_derivative_U_eval_one` / 定理 `iterate_derivative_U_eval_one`

English:
theorem iterate_derivative_U_eval_one
  given: (n : Int) (k : Nat)
  proof: by
  induction k
  case zero => simp
  case succ k ih =>
    push_cast at ih ⊢
    rw [Finset.range_add_one]; rw [Finset.prod_insert Finset.notMem_range_self]; rw [mul_comm (2 * _ + 3)]; rw [mul_assoc]; rw [iterate_derivative_U_eval_one_recurrence]; rw [← mul_assoc]; rw [mul_comm _ (_ ^ 2 - _ ^ 2)]; rw [mul_assoc]; rw [ih]; rw [Finset.prod_insert Finset.notMem_range_self]; rw [mul_assoc]

中文:
定理 iterate_derivative_U_eval_one
  条件: (n : 整数) (k : 自然数)
  证明: by
  induction k
  case zero => simp
  case succ k ih =>
    push_cast at ih ⊢
    rw [Finset.range_add_one]; rw [Finset.prod_insert Finset.notMem_range_self]; rw [mul_comm (2 * _ + 3)]; rw [mul_assoc]; rw [iterate_derivative_U_eval_one_recurrence]; rw [← mul_assoc]; rw [mul_comm _ (_ ^ 2 - _ ^ 2)]; rw [mul_assoc]; rw [ih]; rw [Finset.prod_insert Finset.notMem_range_self]; rw [mul_assoc]

Depends on / 依赖: Finset, Finset.notMem_range_self, Finset.prod_insert, Finset.range_add_one, iterate_derivative_U_eval_one_recurrence, mul_assoc, mul_comm, notMem_range_self, prod_insert, range_add_one
-/
theorem iterate_derivative_U_eval_one (n : Int) (k : Nat) :
    (∏ l in Finset.range k, (2 * l + 3)) * (derivative^[k] (U R n)).eval 1 =
      (∏ l in Finset.range k, ((n + 1) ^ 2 - (l + 1) ^ 2 : Int)) * (n + 1) := by
  induction k
  case zero => simp
  case succ k ih =>
    push_cast at ih ⊢
    rw [Finset.range_add_one]; rw [Finset.prod_insert Finset.notMem_range_self]; rw [mul_comm (2 * _ + 3)]; rw [mul_assoc]; rw [iterate_derivative_U_eval_one_recurrence]; rw [← mul_assoc]; rw [mul_comm _ (_ ^ 2 - _ ^ 2)]; rw [mul_assoc]; rw [ih]; rw [Finset.prod_insert Finset.notMem_range_self]; rw [mul_assoc]

/--
theorem `derivative_T_eval_one` / 定理 `derivative_T_eval_one`

English:
theorem derivative_T_eval_one
  given: (n : Int)
  proof: by
  simp [T_derivative_eq_U, sq]

中文:
定理 derivative_T_eval_one
  条件: (n : 整数)
  证明: by
  simp [T_derivative_eq_U, sq]

Depends on / 依赖: T_derivative_eq_U
-/
theorem derivative_T_eval_one (n : Int) :
    (derivative (T R n)).eval 1 = n ^ 2 := by
  simp [T_derivative_eq_U, sq]

/--
theorem `derivative_U_eval_one` / 定理 `derivative_U_eval_one`

English:
theorem derivative_U_eval_one
  given: (n : Int)
  proof: by
  have h := iterate_derivative_U_eval_one (R := R) n 1
  simp only [Finset.range_one, Finset.prod_singleton, Function.iterate_one] at h
  grind

中文:
定理 derivative_U_eval_one
  条件: (n : 整数)
  证明: by
  have h := iterate_derivative_U_eval_one (R := R) n 1
  simp only [Finset.range_one, Finset.prod_singleton, Function.iterate_one] at h
  grind

Depends on / 依赖: Finset, Finset.prod_singleton, Finset.range_one, Function, Function.iterate_one, iterate_derivative_U_eval_one, iterate_one, prod_singleton, range_one
-/
theorem derivative_U_eval_one (n : Int) :
    3 * (derivative (U R n)).eval 1 = (n + 2) * (n + 1) * n := by
  have h := iterate_derivative_U_eval_one (R := R) n 1
  simp only [Finset.range_one, Finset.prod_singleton, Function.iterate_one] at h
  grind

variable {𝔽 : Type*} [Field 𝔽]

/--
theorem `iterate_derivative_T_eval_one_eq_div` / 定理 `iterate_derivative_T_eval_one_eq_div`

English:
theorem iterate_derivative_T_eval_one_eq_div
  given: [CharZero 𝔽] (n : Int) (k : Nat)
  proof: by
  rw [eq_div_iff (Nat.cast_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr (fun _ _ => by positivity)))]; rw [mul_comm]; rw [iterate_derivative_T_eval_one]

中文:
定理 iterate_derivative_T_eval_one_eq_div
  条件: [特征零 𝔽] (n : 整数) (k : 自然数)
  证明: by
  rw [eq_div_iff (Nat.cast_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr (fun _ _ => by positivity)))]; rw [mul_comm]; rw [iterate_derivative_T_eval_one]

Depends on / 依赖: Finset, Finset.prod_ne_zero_iff.mpr, Nat.cast_ne_zero.mpr, cast_ne_zero, eq_div_iff, iterate_derivative_T_eval_one, mul_comm, prod_ne_zero_iff
-/
theorem iterate_derivative_T_eval_one_eq_div [CharZero 𝔽] (n : Int) (k : Nat) :
    (derivative^[k] (T 𝔽 n)).eval 1 =
      (∏ l in Finset.range k, (n ^ 2 - l ^ 2)) / (∏ l in Finset.range k, (2 * l + 1)) := by
  rw [eq_div_iff (Nat.cast_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr (fun _ _ => by positivity)))]; rw [mul_comm]; rw [iterate_derivative_T_eval_one]

/--
theorem `iterate_derivative_U_eval_one_eq_div` / 定理 `iterate_derivative_U_eval_one_eq_div`

English:
theorem iterate_derivative_U_eval_one_eq_div
  given: [CharZero 𝔽] (n : Int) (k : Nat)
  proof: by
  rw [eq_div_iff (Nat.cast_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr (fun _ _ => by positivity)))]; rw [mul_comm]; rw [iterate_derivative_U_eval_one]

中文:
定理 iterate_derivative_U_eval_one_eq_div
  条件: [特征零 𝔽] (n : 整数) (k : 自然数)
  证明: by
  rw [eq_div_iff (Nat.cast_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr (fun _ _ => by positivity)))]; rw [mul_comm]; rw [iterate_derivative_U_eval_one]

Depends on / 依赖: Finset, Finset.prod_ne_zero_iff.mpr, Nat.cast_ne_zero.mpr, cast_ne_zero, eq_div_iff, iterate_derivative_U_eval_one, mul_comm, prod_ne_zero_iff
-/
theorem iterate_derivative_U_eval_one_eq_div [CharZero 𝔽] (n : Int) (k : Nat) :
    (derivative^[k] (U 𝔽 n)).eval 1 =
      ((∏ l in Finset.range k, ((n + 1) ^ 2 - (l + 1) ^ 2) : Int) * (n + 1)) /
      (∏ l in Finset.range k, (2 * l + 3)) := by
  rw [eq_div_iff (Nat.cast_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr (fun _ _ => by positivity)))]; rw [mul_comm]; rw [iterate_derivative_U_eval_one]

/--
theorem `iterate_derivative_T_eval_one_dvd` / 定理 `iterate_derivative_T_eval_one_dvd`

English:
theorem iterate_derivative_T_eval_one_dvd
  given: (n : Int) (k : Nat)
  proof: dvd_of_mul_right_eq _ iterate_derivative_T_eval_one n k

中文:
定理 iterate_derivative_T_eval_one_dvd
  条件: (n : 整数) (k : 自然数)
  证明: dvd_of_mul_right_eq _ iterate_derivative_T_eval_one n k

Depends on / 依赖: dvd_of_mul_right_eq, iterate_derivative_T_eval_one
-/
theorem iterate_derivative_T_eval_one_dvd (n : Int) (k : Nat) :
    ((∏ l in Finset.range k, (2 * l + 1) : Nat) : 𝔽) ∣ (∏ l in Finset.range k, (n ^ 2 - l ^ 2) : Int) :=
dvd_of_mul_right_eq _ iterate_derivative_T_eval_one n k

/--
theorem `iterate_derivative_U_eval_one_dvd` / 定理 `iterate_derivative_U_eval_one_dvd`

English:
theorem iterate_derivative_U_eval_one_dvd
  given: (n : Int) (k : Nat)
  proof: dvd_of_mul_right_eq _ iterate_derivative_U_eval_one n k

中文:
定理 iterate_derivative_U_eval_one_dvd
  条件: (n : 整数) (k : 自然数)
  证明: dvd_of_mul_right_eq _ iterate_derivative_U_eval_one n k

Depends on / 依赖: dvd_of_mul_right_eq, iterate_derivative_U_eval_one
-/
theorem iterate_derivative_U_eval_one_dvd (n : Int) (k : Nat) :
    ((∏ l in Finset.range k, (2 * l + 3) : Nat) : 𝔽) ∣
      ((∏ l in Finset.range k, ((n + 1) ^ 2 - (l + 1) ^ 2) : Int) * (n + 1)) :=
dvd_of_mul_right_eq _ iterate_derivative_U_eval_one n k

/--
theorem `derivative_U_eval_one_eq_div` / 定理 `derivative_U_eval_one_eq_div`

English:
theorem derivative_U_eval_one_eq_div
  given: [neZero3 : NeZero (3 : 𝔽)] (n : Int)
  proof: eq_div_of_mul_eq neZero3.ne ((mul_comm ..).trans (derivative_U_eval_one n))

中文:
定理 derivative_U_eval_one_eq_div
  条件: [neZero3 : NeZero (3 : 𝔽)] (n : 整数)
  证明: eq_div_of_mul_eq neZero3.ne ((mul_comm ..).trans (derivative_U_eval_one n))

Depends on / 依赖: derivative_U_eval_one, eq_div_of_mul_eq, mul_comm, neZero3, neZero3.ne
-/
theorem derivative_U_eval_one_eq_div [neZero3 : NeZero (3 : 𝔽)] (n : Int) :
    (derivative (U 𝔽 n)).eval 1 = ((n + 2) * (n + 1) * n) / 3 :=
  eq_div_of_mul_eq neZero3.ne ((mul_comm ..).trans (derivative_U_eval_one n))

/--
theorem `derivative_U_eval_one_dvd` / 定理 `derivative_U_eval_one_dvd`

English:
theorem derivative_U_eval_one_dvd
  given: (n : Int)
  proof: dvd_of_mul_right_eq _ (derivative_U_eval_one n)

中文:
定理 derivative_U_eval_one_dvd
  条件: (n : 整数)
  证明: dvd_of_mul_right_eq _ (derivative_U_eval_one n)

Depends on / 依赖: derivative_U_eval_one, dvd_of_mul_right_eq
-/
theorem derivative_U_eval_one_dvd (n : Int) :
    (3 : 𝔽) ∣ (n + 2) * (n + 1) * n :=
  dvd_of_mul_right_eq _ (derivative_U_eval_one n)

variable (R)

/--
theorem `T_mul_T` / 定理 `T_mul_T`

English:
theorem T_mul_T
  given: (m k : Int)
  statement: 2 * T R m * T R k = T R (m + k) + T R (m - k)
  proof: by
  induction k using Polynomial.Chebyshev.induct with
  | zero => simp [two_mul]
  | one => rw [T_add_one, T_one]; ring
  | add_two k ih1 ih2 =>
    have h₁ := T_add_two R (m + k)
    have h₂ := T_sub_two R (m - k)
    have h₃ := T_add_two R k
    linear_combination (norm := ring_nf) 2 * T R m * h₃ - h₂ - h₁ - ih2 + 2 * (X : R[X]) * ih1
  | neg_add_one k ih1 ih2 =>
    have h₁ := T_add_two R (m + (-k - 1))
    have h₂ := T_sub_two R (m - (-k - 1))
    have h₃ := T_add_two R (-k - 1)
    linear_combination (norm := ring_nf) 2 * T R m * h₃ - h₂ - h₁ - ih2 + 2 * (X : R[X]) * ih1

中文:
定理 T_mul_T
  条件: (m k : 整数)
  结论: 2 * T R m * T R k = T R (m + k) + T R (m - k)
  证明: by
  induction k using Polynomial.Chebyshev.induct with
  | zero => simp [two_mul]
  | one => rw [T_add_one, T_one]; ring
  | add_two k ih1 ih2 =>
    have h₁ := T_add_two R (m + k)
    have h₂ := T_sub_two R (m - k)
    have h₃ := T_add_two R k
    linear_combination (norm := ring_nf) 2 * T R m * h₃ - h₂ - h₁ - ih2 + 2 * (X : R[X]) * ih1
  | neg_add_one k ih1 ih2 =>
    have h₁ := T_add_two R (m + (-k - 1))
    have h₂ := T_sub_two R (m - (-k - 1))
    have h₃ := T_add_two R (-k - 1)
    linear_combination (norm := ring_nf) 2 * T R m * h₃ - h₂ - h₁ - ih2 + 2 * (X : R[X]) * ih1

Depends on / 依赖: Chebyshev, Polynomial, Polynomial.Chebyshev.induct, T_add_one, T_add_two, T_one, T_sub_two, add_two, induct, linear_combination, neg_add_one, ring_nf, two_mul
-/
theorem T_mul_T (m k : Int) : 2 * T R m * T R k = T R (m + k) + T R (m - k) := by
  induction k using Polynomial.Chebyshev.induct with
  | zero => simp [two_mul]
  | one => rw [T_add_one, T_one]; ring
  | add_two k ih1 ih2 =>
    have h₁ := T_add_two R (m + k)
    have h₂ := T_sub_two R (m - k)
    have h₃ := T_add_two R k
    linear_combination (norm := ring_nf) 2 * T R m * h₃ - h₂ - h₁ - ih2 + 2 * (X : R[X]) * ih1
  | neg_add_one k ih1 ih2 =>
    have h₁ := T_add_two R (m + (-k - 1))
    have h₂ := T_sub_two R (m - (-k - 1))
    have h₃ := T_add_two R (-k - 1)
    linear_combination (norm := ring_nf) 2 * T R m * h₃ - h₂ - h₁ - ih2 + 2 * (X : R[X]) * ih1

/--
theorem `C_mul_C` / 定理 `C_mul_C`

English:
theorem C_mul_C
  given: (m k : Int)
  statement: C R m * C R k = C R (m + k) + C R (m - k)
  proof: by
  induction k using Polynomial.Chebyshev.induct with
  | zero => simp [mul_two]
  | one => rw [C_add_one, C_one]; ring
  | add_two k ih1 ih2 =>
    have h₁ := C_add_two R (m + k)
    have h₂ := C_sub_two R (m - k)
    have h₃ := C_add_two R k
    linear_combination (norm := ring_nf) C R m * h₃ - h₂ - h₁ - ih2 + (X : R[X]) * ih1
  | neg_add_one k ih1 ih2 =>
    have h₁ := C_add_two R (m + (-k - 1))
    have h₂ := C_sub_two R (m - (-k - 1))
    have h₃ := C_add_two R (-k - 1)
    linear_combination (norm := ring_nf) C R m * h₃ - h₂ - h₁ - ih2 + (X : R[X]) * ih1

中文:
定理 C_mul_C
  条件: (m k : 整数)
  结论: C R m * C R k = C R (m + k) + C R (m - k)
  证明: by
  induction k using Polynomial.Chebyshev.induct with
  | zero => simp [mul_two]
  | one => rw [C_add_one, C_one]; ring
  | add_two k ih1 ih2 =>
    have h₁ := C_add_two R (m + k)
    have h₂ := C_sub_two R (m - k)
    have h₃ := C_add_two R k
    linear_combination (norm := ring_nf) C R m * h₃ - h₂ - h₁ - ih2 + (X : R[X]) * ih1
  | neg_add_one k ih1 ih2 =>
    have h₁ := C_add_two R (m + (-k - 1))
    have h₂ := C_sub_two R (m - (-k - 1))
    have h₃ := C_add_two R (-k - 1)
    linear_combination (norm := ring_nf) C R m * h₃ - h₂ - h₁ - ih2 + (X : R[X]) * ih1

Depends on / 依赖: C_add_one, C_add_two, C_one, C_sub_two, Chebyshev, Polynomial, Polynomial.Chebyshev.induct, add_two, induct, linear_combination, mul_two, neg_add_one, ring_nf
-/
theorem C_mul_C (m k : Int) : C R m * C R k = C R (m + k) + C R (m - k) := by
  induction k using Polynomial.Chebyshev.induct with
  | zero => simp [mul_two]
  | one => rw [C_add_one, C_one]; ring
  | add_two k ih1 ih2 =>
    have h₁ := C_add_two R (m + k)
    have h₂ := C_sub_two R (m - k)
    have h₃ := C_add_two R k
    linear_combination (norm := ring_nf) C R m * h₃ - h₂ - h₁ - ih2 + (X : R[X]) * ih1
  | neg_add_one k ih1 ih2 =>
    have h₁ := C_add_two R (m + (-k - 1))
    have h₂ := C_sub_two R (m - (-k - 1))
    have h₃ := C_add_two R (-k - 1)
    linear_combination (norm := ring_nf) C R m * h₃ - h₂ - h₁ - ih2 + (X : R[X]) * ih1

/--
theorem `T_mul` / 定理 `T_mul`

English:
theorem T_mul
  given: (m n : Int)
  statement: T R (m * n) = (T R m).comp (T R n)
  proof: by
  induction m using Polynomial.Chebyshev.induct with
  | zero => simp
  | one => simp
  | add_two m ih1 ih2 =>
    have h₁ := T_mul_T R ((m + 1) * n) n
have h₂ := congr_arg (comp · (T R n)) T_add_two R m
    simp only [sub_comp, mul_comp, ofNat_comp, X_comp] at h₂
    linear_combination (norm := ring_nf) -ih2 - h₂ - h₁ + 2 * T R n * ih1
  | neg_add_one m ih1 ih2 =>
    have h₁ := T_mul_T R ((-m) * n) n
have h₂ := congr_arg (comp · (T R n)) T_add_two R (-m - 1)
    simp only [sub_comp, mul_comp, ofNat_comp, X_comp] at h₂
    linear_combination (norm := ring_nf) -ih2 - h₂ - h₁ + 2 * T R n * ih1

中文:
定理 T_mul
  条件: (m n : 整数)
  结论: T R (m * n) = (T R m).comp (T R n)
  证明: by
  induction m using Polynomial.Chebyshev.induct with
  | zero => simp
  | one => simp
  | add_two m ih1 ih2 =>
    have h₁ := T_mul_T R ((m + 1) * n) n
have h₂ := congr_arg (comp · (T R n)) T_add_two R m
    simp only [sub_comp, mul_comp, ofNat_comp, X_comp] at h₂
    linear_combination (norm := ring_nf) -ih2 - h₂ - h₁ + 2 * T R n * ih1
  | neg_add_one m ih1 ih2 =>
    have h₁ := T_mul_T R ((-m) * n) n
have h₂ := congr_arg (comp · (T R n)) T_add_two R (-m - 1)
    simp only [sub_comp, mul_comp, ofNat_comp, X_comp] at h₂
    linear_combination (norm := ring_nf) -ih2 - h₂ - h₁ + 2 * T R n * ih1

Depends on / 依赖: Chebyshev, Polynomial, Polynomial.Chebyshev.induct, T_add_two, T_mul_T, X_comp, add_two, congr_arg, induct, linear_combination, mul_comp, neg_add_one, ofNat_comp, ring_nf, sub_comp
-/
theorem T_mul (m n : Int) : T R (m * n) = (T R m).comp (T R n) := by
  induction m using Polynomial.Chebyshev.induct with
  | zero => simp
  | one => simp
  | add_two m ih1 ih2 =>
    have h₁ := T_mul_T R ((m + 1) * n) n
have h₂ := congr_arg (comp · (T R n)) T_add_two R m
    simp only [sub_comp, mul_comp, ofNat_comp, X_comp] at h₂
    linear_combination (norm := ring_nf) -ih2 - h₂ - h₁ + 2 * T R n * ih1
  | neg_add_one m ih1 ih2 =>
    have h₁ := T_mul_T R ((-m) * n) n
have h₂ := congr_arg (comp · (T R n)) T_add_two R (-m - 1)
    simp only [sub_comp, mul_comp, ofNat_comp, X_comp] at h₂
    linear_combination (norm := ring_nf) -ih2 - h₂ - h₁ + 2 * T R n * ih1

/--
theorem `C_mul` / 定理 `C_mul`

English:
theorem C_mul
  given: (m n : Int)
  statement: C R (m * n) = (C R m).comp (C R n)
  proof: by
  induction m using Polynomial.Chebyshev.induct with
  | zero => simp
  | one => simp
  | add_two m ih1 ih2 =>
    have h₁ := C_mul_C R ((m + 1) * n) n
have h₂ := congr_arg (comp · (C R n)) C_add_two R m
    simp only [sub_comp, mul_comp, X_comp] at h₂
    linear_combination (norm := ring_nf) -ih2 - h₂ - h₁ + C R n * ih1
  | neg_add_one m ih1 ih2 =>
    have h₁ := C_mul_C R ((-m) * n) n
have h₂ := congr_arg (comp · (C R n)) C_add_two R (-m - 1)
    simp only [sub_comp, mul_comp, X_comp] at h₂
    linear_combination (norm := ring_nf) -ih2 - h₂ - h₁ + C R n * ih1

中文:
定理 C_mul
  条件: (m n : 整数)
  结论: C R (m * n) = (C R m).comp (C R n)
  证明: by
  induction m using Polynomial.Chebyshev.induct with
  | zero => simp
  | one => simp
  | add_two m ih1 ih2 =>
    have h₁ := C_mul_C R ((m + 1) * n) n
have h₂ := congr_arg (comp · (C R n)) C_add_two R m
    simp only [sub_comp, mul_comp, X_comp] at h₂
    linear_combination (norm := ring_nf) -ih2 - h₂ - h₁ + C R n * ih1
  | neg_add_one m ih1 ih2 =>
    have h₁ := C_mul_C R ((-m) * n) n
have h₂ := congr_arg (comp · (C R n)) C_add_two R (-m - 1)
    simp only [sub_comp, mul_comp, X_comp] at h₂
    linear_combination (norm := ring_nf) -ih2 - h₂ - h₁ + C R n * ih1

Depends on / 依赖: C_add_two, C_mul_C, Chebyshev, Polynomial, Polynomial.Chebyshev.induct, X_comp, add_two, congr_arg, induct, linear_combination, mul_comp, neg_add_one, ring_nf, sub_comp
-/
theorem C_mul (m n : Int) : C R (m * n) = (C R m).comp (C R n) := by
  induction m using Polynomial.Chebyshev.induct with
  | zero => simp
  | one => simp
  | add_two m ih1 ih2 =>
    have h₁ := C_mul_C R ((m + 1) * n) n
have h₂ := congr_arg (comp · (C R n)) C_add_two R m
    simp only [sub_comp, mul_comp, X_comp] at h₂
    linear_combination (norm := ring_nf) -ih2 - h₂ - h₁ + C R n * ih1
  | neg_add_one m ih1 ih2 =>
    have h₁ := C_mul_C R ((-m) * n) n
have h₂ := congr_arg (comp · (C R n)) C_add_two R (-m - 1)
    simp only [sub_comp, mul_comp, X_comp] at h₂
    linear_combination (norm := ring_nf) -ih2 - h₂ - h₁ + C R n * ih1

end Polynomial.Chebyshev
