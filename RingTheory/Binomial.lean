/-
Copyright (c) 2023 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Carnahan
-/
module

public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.Group.Torsion
public import Mathlib.Algebra.Module.Rat
public import Mathlib.Algebra.Order.Ring.NNRat
public import Mathlib.Algebra.Polynomial.Smeval
public import Mathlib.Algebra.Ring.NegOnePow
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.RingTheory.Polynomial.Pochhammer
public import Mathlib.Tactic.Field
public import Mathlib.Tactic.Module

/-!
# Binomial rings

In this file we introduce the binomial property as a mixin, and define the `multichoose`
and `choose` functions generalizing binomial coefficients.

According to our main reference [elliott2006binomial] (which lists many equivalent conditions), a
binomial ring is a torsion-free commutative ring `R` such that for any `x ∈ R` and any `k ∈ ℕ`, the
product `x(x-1)⋯(x-k+1)` is divisible by `k!`. The torsion-free condition lets us divide by `k!`
unambiguously, so we get uniquely defined binomial coefficients.

The defining condition doesn't require commutativity or associativity, and we get a theory with
essentially the same power by replacing subtraction with addition. Thus, we consider any additive
commutative monoid with a notion of natural number exponents in which multiplication by positive
integers is injective, and demand that the evaluation of the ascending Pochhammer polynomial
`X(X+1)⋯(X+(k-1))` at any element is divisible by `k!`. The quotient is called `multichoose r k`,
because for `r` a natural number, it is the number of multisets of cardinality `k` taken from a type
of cardinality `n`.

## Definitions

* `BinomialRing`: a mixin class specifying a suitable `multichoose` function.
* `Ring.multichoose`: the quotient of an ascending Pochhammer evaluation by a factorial.
* `Ring.choose`: the quotient of a descending Pochhammer evaluation by a factorial.

## Results

* Basic results with choose and multichoose, e.g., `choose_zero_right`
* Relations between choose and multichoose, negated input.
* Fundamental recursion: `choose_succ_succ`
* Chu-Vandermonde identity: `add_choose_eq`
* Pochhammer API

## References

* [J. Elliott, *Binomial rings, integer-valued polynomials, and λ-rings*][elliott2006binomial]

## TODO

Further results in Elliot's paper:
* A CommRing is binomial if and only if it admits a λ-ring structure with trivial Adams operations.
* The free commutative binomial ring on a set `X` is the ring of integer-valued polynomials in the
  variables `X`. (also, noncommutative version?)
* Given a commutative binomial ring `A` and an `A`-algebra `B` that is complete with respect to an
  ideal `I`, formal exponentiation induces an `A`-module structure on the multiplicative subgroup
  `1 + I`.

-/

@[expose] public section

open Function Polynomial

/--
Definition of `BinomialRing` / `BinomialRing` 的定义

English:
class BinomialRing
  parameters: (R : Type*) [AddCommMonoid R] [Pow R Nat]
  axioms and operations (3):
    - [toIsAddTorsionFree : IsAddTorsionFree R]
    - multichoose : R -> Nat -> R
    - factorial_nsmul_multichoose((r : R) (n : Nat)) : n.factorial • multichoose r n = (ascPochhammer Nat n).smeval r

中文:
类 二项环
  参数: (R : 类型) [加法交换幺半群 R] [幂 R 自然数]
  公理与运算 (3 个):
    - [toIsAddTorsionFree : 是加法无挠 R]
    - multichoose : R -> 自然数 -> R
    - factorial_nsmul_multichoose((r : R) (n : 自然数)) : n.factorial • multichoose r n = (ascPochhammer 自然数 n).smeval r
-/
class BinomialRing (R : Type*) [AddCommMonoid R] [Pow R Nat] where
  -- This base class has been demoted to a field, to avoid creating
  -- an expensive global instance.
  [toIsAddTorsionFree : IsAddTorsionFree R]
  /-- A multichoose function, giving the quotient of Pochhammer evaluations by factorials. -/
  multichoose : R -> Nat -> R
  /-- The `n`th ascending Pochhammer polynomial evaluated at any element is divisible by `n!` -/
  factorial_nsmul_multichoose (r : R) (n : Nat) :
    n.factorial • multichoose r n = (ascPochhammer Nat n).smeval r

-- This is only a local instance as it otherwise causes significant slow downs
-- to every call to `grind` involving a ring. Please do not make it a global instance.
-- (~1500 heartbeats measured on `nightly-testing-2025-09-09`.)
attribute [local instance] BinomialRing.toIsAddTorsionFree

section Multichoose

namespace Ring

variable {R : Type*} [AddCommMonoid R] [Pow R Nat] [BinomialRing R]

/--
Definition of `multichoose` / `multichoose` 的定义

English:
definition multichoose
  signature: (r : R) (n : Nat)
  body: BinomialRing.multichoose r n

@[simp]

中文:
定义 multichoose
  签名: (r : R) (n : 自然数)
  定义体: BinomialRing.multichoose r n

@[simp]

Depends on / 依赖: BinomialRing, BinomialRing.multichoose, multichoose
-/
def multichoose (r : R) (n : Nat) : R := BinomialRing.multichoose r n

@[simp]
/--
theorem `multichoose_eq_multichoose` / 定理 `multichoose_eq_multichoose`

English:
theorem multichoose_eq_multichoose
  given: (r : R) (n : Nat)
  proof: rfl

中文:
定理 multichoose_eq_multichoose
  条件: (r : R) (n : 自然数)
  证明: rfl
-/
theorem multichoose_eq_multichoose (r : R) (n : Nat) :
    BinomialRing.multichoose r n = multichoose r n := rfl

/--
theorem `factorial_nsmul_multichoose_eq_ascPochhammer` / 定理 `factorial_nsmul_multichoose_eq_ascPochhammer`

English:
theorem factorial_nsmul_multichoose_eq_ascPochhammer
  given: (r : R) (n : Nat)
  proof: BinomialRing.factorial_nsmul_multichoose r n

@[simp]

中文:
定理 factorial_nsmul_multichoose_eq_ascPochhammer
  条件: (r : R) (n : 自然数)
  证明: BinomialRing.factorial_nsmul_multichoose r n

@[simp]

Depends on / 依赖: BinomialRing, BinomialRing.factorial_nsmul_multichoose, factorial_nsmul_multichoose
-/
theorem factorial_nsmul_multichoose_eq_ascPochhammer (r : R) (n : Nat) :
    n.factorial • multichoose r n = (ascPochhammer Nat n).smeval r :=
  BinomialRing.factorial_nsmul_multichoose r n

@[simp]
/--
theorem `multichoose_zero_right'` / 定理 `multichoose_zero_right'`

English:
theorem multichoose_zero_right'
  given: (r : R)
  statement: multichoose r 0 = r ^ 0
  proof: by
  rw [← nsmul_right_inj (Nat.factorial_ne_zero 0)]; rw [factorial_nsmul_multichoose_eq_ascPochhammer]; rw [ascPochhammer_zero]; rw [smeval_one]; rw [Nat.factorial]

中文:
定理 multichoose_zero_right'
  条件: (r : R)
  结论: multichoose r 0 = r ^ 0
  证明: by
  rw [← nsmul_right_inj (Nat.factorial_ne_zero 0)]; rw [factorial_nsmul_multichoose_eq_ascPochhammer]; rw [ascPochhammer_zero]; rw [smeval_one]; rw [Nat.factorial]

Depends on / 依赖: Nat.factorial, Nat.factorial_ne_zero, ascPochhammer_zero, factorial, factorial_ne_zero, factorial_nsmul_multichoose_eq_ascPochhammer, nsmul_right_inj, smeval_one
-/
theorem multichoose_zero_right' (r : R) : multichoose r 0 = r ^ 0 := by
  rw [← nsmul_right_inj (Nat.factorial_ne_zero 0)]; rw [factorial_nsmul_multichoose_eq_ascPochhammer]; rw [ascPochhammer_zero]; rw [smeval_one]; rw [Nat.factorial]

/--
theorem `multichoose_zero_right` / 定理 `multichoose_zero_right`

English:
theorem multichoose_zero_right
  statement: [MulOneClass R] [NatPowAssoc R]
  proof: by
  rw [multichoose_zero_right']; rw [npow_zero]

@[simp]

中文:
定理 multichoose_zero_right
  结论: [MulOne类 R] [自然数PowAssoc R]
  证明: by
  rw [multichoose_zero_right']; rw [npow_zero]

@[simp]

Depends on / 依赖: multichoose_zero_right, npow_zero
-/
theorem multichoose_zero_right [MulOneClass R] [NatPowAssoc R]
    (r : R) : multichoose r 0 = 1 := by
  rw [multichoose_zero_right']; rw [npow_zero]

@[simp]
/--
theorem `multichoose_one_right'` / 定理 `multichoose_one_right'`

English:
theorem multichoose_one_right'
  given: (r : R)
  statement: multichoose r 1 = r ^ 1
  proof: by
  rw [← nsmul_right_inj (Nat.factorial_ne_zero 1)]; rw [factorial_nsmul_multichoose_eq_ascPochhammer]; rw [ascPochhammer_one]; rw [smeval_X]; rw [Nat.factorial_one]; rw [one_smul]

中文:
定理 multichoose_one_right'
  条件: (r : R)
  结论: multichoose r 1 = r ^ 1
  证明: by
  rw [← nsmul_right_inj (Nat.factorial_ne_zero 1)]; rw [factorial_nsmul_multichoose_eq_ascPochhammer]; rw [ascPochhammer_one]; rw [smeval_X]; rw [Nat.factorial_one]; rw [one_smul]

Depends on / 依赖: Nat.factorial_ne_zero, Nat.factorial_one, ascPochhammer_one, factorial_ne_zero, factorial_nsmul_multichoose_eq_ascPochhammer, factorial_one, nsmul_right_inj, one_smul, smeval_X
-/
theorem multichoose_one_right' (r : R) : multichoose r 1 = r ^ 1 := by
  rw [← nsmul_right_inj (Nat.factorial_ne_zero 1)]; rw [factorial_nsmul_multichoose_eq_ascPochhammer]; rw [ascPochhammer_one]; rw [smeval_X]; rw [Nat.factorial_one]; rw [one_smul]

/--
theorem `multichoose_one_right` / 定理 `multichoose_one_right`

English:
theorem multichoose_one_right
  given: [MulOneClass R] [NatPowAssoc R] (r : R)
  statement: multichoose r 1 = r
  proof: by
  rw [multichoose_one_right']; rw [npow_one]

中文:
定理 multichoose_one_right
  条件: [MulOne类 R] [自然数PowAssoc R] (r : R)
  结论: multichoose r 1 = r
  证明: by
  rw [multichoose_one_right']; rw [npow_one]

Depends on / 依赖: multichoose_one_right, npow_one
-/
theorem multichoose_one_right [MulOneClass R] [NatPowAssoc R] (r : R) : multichoose r 1 = r := by
  rw [multichoose_one_right']; rw [npow_one]

variable {R : Type*} [NonAssocSemiring R] [Pow R Nat] [NatPowAssoc R] [BinomialRing R]

@[simp]
/--
theorem `multichoose_zero_succ` / 定理 `multichoose_zero_succ`

English:
theorem multichoose_zero_succ
  given: (k : Nat)
  statement: multichoose (0 : R) (k + 1) = 0
  proof: by
  rw [← nsmul_right_inj (Nat.factorial_ne_zero (k + 1))]; rw [factorial_nsmul_multichoose_eq_ascPochhammer]; rw [smul_zero]; rw [ascPochhammer_succ_left]; rw [smeval_X_mul]; rw [zero_mul]

中文:
定理 multichoose_zero_succ
  条件: (k : 自然数)
  结论: multichoose (0 : R) (k + 1) = 0
  证明: by
  rw [← nsmul_right_inj (Nat.factorial_ne_zero (k + 1))]; rw [factorial_nsmul_multichoose_eq_ascPochhammer]; rw [smul_zero]; rw [ascPochhammer_succ_left]; rw [smeval_X_mul]; rw [zero_mul]

Depends on / 依赖: Nat.factorial_ne_zero, ascPochhammer_succ_left, factorial_ne_zero, factorial_nsmul_multichoose_eq_ascPochhammer, nsmul_right_inj, smeval_X_mul, smul_zero, zero_mul
-/
theorem multichoose_zero_succ (k : Nat) : multichoose (0 : R) (k + 1) = 0 := by
  rw [← nsmul_right_inj (Nat.factorial_ne_zero (k + 1))]; rw [factorial_nsmul_multichoose_eq_ascPochhammer]; rw [smul_zero]; rw [ascPochhammer_succ_left]; rw [smeval_X_mul]; rw [zero_mul]

/--
theorem `ascPochhammer_succ_succ` / 定理 `ascPochhammer_succ_succ`

English:
theorem ascPochhammer_succ_succ
  given: (r : R) (k : Nat)
  proof: by
  nth_rw 1 [ascPochhammer_succ_right, ascPochhammer_succ_left, mul_comm (ascPochhammer Nat k)]
  simp only [smeval_mul, smeval_comp, smeval_add, smeval_X]
  rw [Nat.factorial]; rw [mul_smul]; rw [factorial_nsmul_multichoose_eq_ascPochhammer]
  simp only [smeval_one, npow_one, npow_zero, one_smul]
  rw [← C_eq_natCast]; rw [smeval_C]; rw [npow_zero]; rw [add_assoc]; rw [add_mul]; rw [add_comm 1]; rw [@nsmul_one]; rw [add_mul]
  rw [← @nsmul_eq_mul]; rw [@add_rotate']; rw [@succ_nsmul]; rw [add_assoc]
  simp_all only [Nat.cast_id, nsmul_eq_mul, one_mul]

中文:
定理 ascPochhammer_succ_succ
  条件: (r : R) (k : 自然数)
  证明: by
  nth_rw 1 [ascPochhammer_succ_right, ascPochhammer_succ_left, mul_comm (ascPochhammer Nat k)]
  simp only [smeval_mul, smeval_comp, smeval_add, smeval_X]
  rw [Nat.factorial]; rw [mul_smul]; rw [factorial_nsmul_multichoose_eq_ascPochhammer]
  simp only [smeval_one, npow_one, npow_zero, one_smul]
  rw [← C_eq_natCast]; rw [smeval_C]; rw [npow_zero]; rw [add_assoc]; rw [add_mul]; rw [add_comm 1]; rw [@nsmul_one]; rw [add_mul]
  rw [← @nsmul_eq_mul]; rw [@add_rotate']; rw [@succ_nsmul]; rw [add_assoc]
  simp_all only [Nat.cast_id, nsmul_eq_mul, one_mul]

Depends on / 依赖: C_eq_natCast, Nat.factorial, add_assoc, add_comm, add_mul, add_rotate, ascPochhammer, ascPochhammer_succ_left, ascPochhammer_succ_right, factorial, factorial_nsmul_multichoose_eq_ascPochhammer, mul_comm, mul_smul, npow_one, npow_zero, nsmul_eq_mul, nsmul_one, nth_rw, one_smul, smeval_C
-/
theorem ascPochhammer_succ_succ (r : R) (k : Nat) :
    smeval (ascPochhammer Nat (k + 1)) (r + 1) = Nat.factorial (k + 1) • multichoose (r + 1) k +
    smeval (ascPochhammer Nat (k + 1)) r := by
  nth_rw 1 [ascPochhammer_succ_right, ascPochhammer_succ_left, mul_comm (ascPochhammer Nat k)]
  simp only [smeval_mul, smeval_comp, smeval_add, smeval_X]
  rw [Nat.factorial]; rw [mul_smul]; rw [factorial_nsmul_multichoose_eq_ascPochhammer]
  simp only [smeval_one, npow_one, npow_zero, one_smul]
  rw [← C_eq_natCast]; rw [smeval_C]; rw [npow_zero]; rw [add_assoc]; rw [add_mul]; rw [add_comm 1]; rw [@nsmul_one]; rw [add_mul]
  rw [← @nsmul_eq_mul]; rw [@add_rotate']; rw [@succ_nsmul]; rw [add_assoc]
  simp_all only [Nat.cast_id, nsmul_eq_mul, one_mul]

/--
theorem `multichoose_succ_succ` / 定理 `multichoose_succ_succ`

English:
theorem multichoose_succ_succ
  given: (r : R) (k : Nat)
  proof: by
  rw [← nsmul_right_inj (Nat.factorial_ne_zero (k + 1))]
  simp only [factorial_nsmul_multichoose_eq_ascPochhammer, smul_add]
  rw [add_comm (smeval (ascPochhammer Nat (k + 1)) r)]; rw [ascPochhammer_succ_succ r k]

@[simp]

中文:
定理 multichoose_succ_succ
  条件: (r : R) (k : 自然数)
  证明: by
  rw [← nsmul_right_inj (Nat.factorial_ne_zero (k + 1))]
  simp only [factorial_nsmul_multichoose_eq_ascPochhammer, smul_add]
  rw [add_comm (smeval (ascPochhammer Nat (k + 1)) r)]; rw [ascPochhammer_succ_succ r k]

@[simp]

Depends on / 依赖: Nat.factorial_ne_zero, add_comm, ascPochhammer, ascPochhammer_succ_succ, factorial_ne_zero, factorial_nsmul_multichoose_eq_ascPochhammer, nsmul_right_inj, smeval, smul_add
-/
theorem multichoose_succ_succ (r : R) (k : Nat) :
    multichoose (r + 1) (k + 1) = multichoose r (k + 1) + multichoose (r + 1) k := by
  rw [← nsmul_right_inj (Nat.factorial_ne_zero (k + 1))]
  simp only [factorial_nsmul_multichoose_eq_ascPochhammer, smul_add]
  rw [add_comm (smeval (ascPochhammer Nat (k + 1)) r)]; rw [ascPochhammer_succ_succ r k]

@[simp]
/--
theorem `multichoose_one` / 定理 `multichoose_one`

English:
theorem multichoose_one
  given: (k : Nat)
  statement: multichoose (1 : R) k = 1
  proof: by
  induction k with
  | zero => exact multichoose_zero_right 1
  | succ n ih =>
    rw [show (1 : R) = 0 + 1 by exact (@zero_add R _ 1).symm]; rw [multichoose_succ_succ]; rw [multichoose_zero_succ]; rw [zero_add]; rw [zero_add]; rw [ih]

中文:
定理 multichoose_one
  条件: (k : 自然数)
  结论: multichoose (1 : R) k = 1
  证明: by
  induction k with
  | zero => exact multichoose_zero_right 1
  | succ n ih =>
    rw [show (1 : R) = 0 + 1 by exact (@zero_add R _ 1).symm]; rw [multichoose_succ_succ]; rw [multichoose_zero_succ]; rw [zero_add]; rw [zero_add]; rw [ih]

Depends on / 依赖: multichoose_succ_succ, multichoose_zero_right, multichoose_zero_succ, zero_add
-/
theorem multichoose_one (k : Nat) : multichoose (1 : R) k = 1 := by
  induction k with
  | zero => exact multichoose_zero_right 1
  | succ n ih =>
    rw [show (1 : R) = 0 + 1 by exact (@zero_add R _ 1).symm]; rw [multichoose_succ_succ]; rw [multichoose_zero_succ]; rw [zero_add]; rw [zero_add]; rw [ih]

/--
theorem `multichoose_two` / 定理 `multichoose_two`

English:
theorem multichoose_two
  given: (k : Nat)
  statement: multichoose (2 : R) k = k + 1
  proof: by
  induction k with
  | zero =>
    rw [multichoose_zero_right]; rw [Nat.cast_zero]; rw [zero_add]
  | succ n ih =>
    rw [one_add_one_eq_two.symm]; rw [multichoose_succ_succ]; rw [multichoose_one]; rw [one_add_one_eq_two]; rw [ih]; rw [Nat.cast_succ]; rw [add_comm]

中文:
定理 multichoose_two
  条件: (k : 自然数)
  结论: multichoose (2 : R) k = k + 1
  证明: by
  induction k with
  | zero =>
    rw [multichoose_zero_right]; rw [Nat.cast_zero]; rw [zero_add]
  | succ n ih =>
    rw [one_add_one_eq_two.symm]; rw [multichoose_succ_succ]; rw [multichoose_one]; rw [one_add_one_eq_two]; rw [ih]; rw [Nat.cast_succ]; rw [add_comm]

Depends on / 依赖: Nat.cast_succ, Nat.cast_zero, add_comm, cast_succ, cast_zero, multichoose_one, multichoose_succ_succ, multichoose_zero_right, one_add_one_eq_two, one_add_one_eq_two.symm, zero_add
-/
theorem multichoose_two (k : Nat) : multichoose (2 : R) k = k + 1 := by
  induction k with
  | zero =>
    rw [multichoose_zero_right]; rw [Nat.cast_zero]; rw [zero_add]
  | succ n ih =>
    rw [one_add_one_eq_two.symm]; rw [multichoose_succ_succ]; rw [multichoose_one]; rw [one_add_one_eq_two]; rw [ih]; rw [Nat.cast_succ]; rw [add_comm]

attribute [local instance] BinomialRing.toIsAddTorsionFree in
/--
lemma `map_multichoose` / 引理 `map_multichoose`

English:
lemma map_multichoose
  statement: {R S F : Type*} [Ring R] [Ring S] [BinomialRing R] [BinomialRing S]
  proof: by
  apply nsmul_right_injective n.factorial_ne_zero
  simp only [← map_nsmul, Ring.factorial_nsmul_multichoose_eq_ascPochhammer,
    ← Polynomial.eval₂_smulOneHom_eq_smeval, Polynomial.hom_eval₂, ← RingHom.coe_coe f]
  congr
  exact Subsingleton.elim _ _

中文:
引理 map_multichoose
  结论: {R S F : 类型} [环 R] [环 S] [二项环 R] [二项环 S]
  证明: by
  apply nsmul_right_injective n.factorial_ne_zero
  simp only [← map_nsmul, Ring.factorial_nsmul_multichoose_eq_ascPochhammer,
    ← Polynomial.eval₂_smulOneHom_eq_smeval, Polynomial.hom_eval₂, ← RingHom.coe_coe f]
  congr
  exact Subsingleton.elim _ _

Depends on / 依赖: Polynomial, Polynomial.eval, Polynomial.hom_eval, Ring.factorial_nsmul_multichoose_eq_ascPochhammer, RingHom, RingHom.coe_coe, Subsingleton, Subsingleton.elim, coe_coe, factorial_ne_zero, factorial_nsmul_multichoose_eq_ascPochhammer, map_nsmul, n.factorial_ne_zero, nsmul_right_injective
-/
lemma map_multichoose {R S F : Type*} [Ring R] [Ring S] [BinomialRing R] [BinomialRing S]
    [FunLike F R S] [RingHomClass F R S] (f : F) (a : R) (n : Nat) :
    f (Ring.multichoose a n) = Ring.multichoose (f a) n := by
  apply nsmul_right_injective n.factorial_ne_zero
  simp only [← map_nsmul, Ring.factorial_nsmul_multichoose_eq_ascPochhammer,
    ← Polynomial.eval₂_smulOneHom_eq_smeval, Polynomial.hom_eval₂, ← RingHom.coe_coe f]
  congr
  exact Subsingleton.elim _ _

end Ring

end Multichoose

section Pochhammer

namespace Polynomial

@[simp]
/--
theorem `ascPochhammer_smeval_cast` / 定理 `ascPochhammer_smeval_cast`

English:
theorem ascPochhammer_smeval_cast
  statement: (R : Type*) [Semiring R] {S : Type*} [NonAssocSemiring S]
  proof: by
  induction n with
  | zero => simp only [ascPochhammer_zero, smeval_one]
  | succ n hn =>
    simp only [ascPochhammer_succ_right, mul_add, smeval_add, smeval_mul_X, ← Nat.cast_comm]
    simp only [← C_eq_natCast, smeval_C_mul, hn, Nat.cast_smul_eq_nsmul R n]
    simp only [nsmul_eq_mul, Nat.cast_id]

中文:
定理 ascPochhammer_smeval_cast
  结论: (R : 类型) [半环 R] {S : 类型} [非结合半环 S]
  证明: by
  induction n with
  | zero => simp only [ascPochhammer_zero, smeval_one]
  | succ n hn =>
    simp only [ascPochhammer_succ_right, mul_add, smeval_add, smeval_mul_X, ← Nat.cast_comm]
    simp only [← C_eq_natCast, smeval_C_mul, hn, Nat.cast_smul_eq_nsmul R n]
    simp only [nsmul_eq_mul, Nat.cast_id]

Depends on / 依赖: C_eq_natCast, Nat.cast_comm, Nat.cast_id, Nat.cast_smul_eq_nsmul, ascPochhammer_succ_right, ascPochhammer_zero, cast_comm, cast_id, cast_smul_eq_nsmul, mul_add, nsmul_eq_mul, smeval_C_mul, smeval_add, smeval_mul_X, smeval_one
-/
theorem ascPochhammer_smeval_cast (R : Type*) [Semiring R] {S : Type*} [NonAssocSemiring S]
    [Pow S Nat] [Module R S] [IsScalarTower R S S] [NatPowAssoc S]
    (x : S) (n : Nat) : (ascPochhammer R n).smeval x = (ascPochhammer Nat n).smeval x := by
  induction n with
  | zero => simp only [ascPochhammer_zero, smeval_one]
  | succ n hn =>
    simp only [ascPochhammer_succ_right, mul_add, smeval_add, smeval_mul_X, ← Nat.cast_comm]
    simp only [← C_eq_natCast, smeval_C_mul, hn, Nat.cast_smul_eq_nsmul R n]
    simp only [nsmul_eq_mul, Nat.cast_id]

variable {R : Type*}

/--
theorem `ascPochhammer_smeval_eq_eval` / 定理 `ascPochhammer_smeval_eq_eval`

English:
theorem ascPochhammer_smeval_eq_eval
  given: [Semiring R] (r : R) (n : Nat)
  proof: by
  rw [eval_eq_smeval]; rw [ascPochhammer_smeval_cast R]

中文:
定理 ascPochhammer_smeval_eq_eval
  条件: [半环 R] (r : R) (n : 自然数)
  证明: by
  rw [eval_eq_smeval]; rw [ascPochhammer_smeval_cast R]

Depends on / 依赖: ascPochhammer_smeval_cast, eval_eq_smeval
-/
theorem ascPochhammer_smeval_eq_eval [Semiring R] (r : R) (n : Nat) :
    (ascPochhammer Nat n).smeval r = (ascPochhammer R n).eval r := by
  rw [eval_eq_smeval]; rw [ascPochhammer_smeval_cast R]

variable [NonAssocRing R] [Pow R Nat] [NatPowAssoc R]

/--
theorem `descPochhammer_smeval_eq_ascPochhammer` / 定理 `descPochhammer_smeval_eq_ascPochhammer`

English:
theorem descPochhammer_smeval_eq_ascPochhammer
  given: (r : R) (n : Nat)
  proof: by
  induction n with
  | zero => simp only [descPochhammer_zero, ascPochhammer_zero, smeval_one, npow_zero]
  | succ n ih =>
    rw [Nat.cast_succ]; rw [sub_add]; rw [add_sub_cancel_right]; rw [descPochhammer_succ_right]; rw [smeval_mul]; rw [ih]; rw [ascPochhammer_succ_left]; rw [X_mul]; rw [smeval_mul_X]; rw [smeval_comp]; rw [smeval_sub]; rw [← C_eq_natCast]; rw [smeval_add]; rw [smeval_one]; rw [smeval_C]
    simp only [smeval_X, npow_one, npow_zero, zsmul_one, Int.cast_natCast, one_smul]

中文:
定理 descPochhammer_smeval_eq_ascPochhammer
  条件: (r : R) (n : 自然数)
  证明: by
  induction n with
  | zero => simp only [descPochhammer_zero, ascPochhammer_zero, smeval_one, npow_zero]
  | succ n ih =>
    rw [Nat.cast_succ]; rw [sub_add]; rw [add_sub_cancel_right]; rw [descPochhammer_succ_right]; rw [smeval_mul]; rw [ih]; rw [ascPochhammer_succ_left]; rw [X_mul]; rw [smeval_mul_X]; rw [smeval_comp]; rw [smeval_sub]; rw [← C_eq_natCast]; rw [smeval_add]; rw [smeval_one]; rw [smeval_C]
    simp only [smeval_X, npow_one, npow_zero, zsmul_one, Int.cast_natCast, one_smul]

Depends on / 依赖: C_eq_natCast, Int.cast_natCast, Nat.cast_succ, X_mul, add_sub_cancel_right, ascPochhammer_succ_left, ascPochhammer_zero, cast_natCast, cast_succ, descPochhammer_succ_right, descPochhammer_zero, npow_one, npow_zero, one_smul, smeval_C, smeval_X, smeval_add, smeval_comp, smeval_mul, smeval_mul_X
-/
theorem descPochhammer_smeval_eq_ascPochhammer (r : R) (n : Nat) :
    (descPochhammer Int n).smeval r = (ascPochhammer Nat n).smeval (r - n + 1) := by
  induction n with
  | zero => simp only [descPochhammer_zero, ascPochhammer_zero, smeval_one, npow_zero]
  | succ n ih =>
    rw [Nat.cast_succ]; rw [sub_add]; rw [add_sub_cancel_right]; rw [descPochhammer_succ_right]; rw [smeval_mul]; rw [ih]; rw [ascPochhammer_succ_left]; rw [X_mul]; rw [smeval_mul_X]; rw [smeval_comp]; rw [smeval_sub]; rw [← C_eq_natCast]; rw [smeval_add]; rw [smeval_one]; rw [smeval_C]
    simp only [smeval_X, npow_one, npow_zero, zsmul_one, Int.cast_natCast, one_smul]

/--
theorem `descPochhammer_smeval_eq_descFactorial` / 定理 `descPochhammer_smeval_eq_descFactorial`

English:
theorem descPochhammer_smeval_eq_descFactorial
  given: (n k : Nat)
  proof: by
  induction k with
  | zero =>
    rw [descPochhammer_zero]; rw [Nat.descFactorial_zero]; rw [Nat.cast_one]; rw [smeval_one]; rw [npow_zero]; rw [one_smul]
  | succ k ih =>
    rw [descPochhammer_succ_right]; rw [Nat.descFactorial_succ]; rw [smeval_mul]; rw [ih]; rw [mul_comm]; rw [Nat.cast_mul]; rw [smeval_sub]; rw [smeval_X]; rw [smeval_natCast]; rw [npow_one]; rw [npow_zero]; rw [nsmul_one]
    by_cases! h : n < k
    · simp only [Nat.descFactorial_eq_zero_iff_lt.mpr h, Nat.cast_zero, zero_mul]
    · rw [Nat.cast_sub h]

中文:
定理 descPochhammer_smeval_eq_descFactorial
  条件: (n k : 自然数)
  证明: by
  induction k with
  | zero =>
    rw [descPochhammer_zero]; rw [Nat.descFactorial_zero]; rw [Nat.cast_one]; rw [smeval_one]; rw [npow_zero]; rw [one_smul]
  | succ k ih =>
    rw [descPochhammer_succ_right]; rw [Nat.descFactorial_succ]; rw [smeval_mul]; rw [ih]; rw [mul_comm]; rw [Nat.cast_mul]; rw [smeval_sub]; rw [smeval_X]; rw [smeval_natCast]; rw [npow_one]; rw [npow_zero]; rw [nsmul_one]
    by_cases! h : n < k
    · simp only [Nat.descFactorial_eq_zero_iff_lt.mpr h, Nat.cast_zero, zero_mul]
    · rw [Nat.cast_sub h]

Depends on / 依赖: Nat.cast_mul, Nat.cast_one, Nat.cast_s, Nat.cast_zero, Nat.descFactorial_eq_zero_iff_lt.mpr, Nat.descFactorial_succ, Nat.descFactorial_zero, cast_mul, cast_one, cast_s, cast_zero, descFactorial_eq_zero_iff_lt, descFactorial_succ, descFactorial_zero, descPochhammer_succ_right, descPochhammer_zero, mul_comm, npow_one, npow_zero, nsmul_one
-/
theorem descPochhammer_smeval_eq_descFactorial (n k : Nat) :
    (descPochhammer Int k).smeval (n : R) = n.descFactorial k := by
  induction k with
  | zero =>
    rw [descPochhammer_zero]; rw [Nat.descFactorial_zero]; rw [Nat.cast_one]; rw [smeval_one]; rw [npow_zero]; rw [one_smul]
  | succ k ih =>
    rw [descPochhammer_succ_right]; rw [Nat.descFactorial_succ]; rw [smeval_mul]; rw [ih]; rw [mul_comm]; rw [Nat.cast_mul]; rw [smeval_sub]; rw [smeval_X]; rw [smeval_natCast]; rw [npow_one]; rw [npow_zero]; rw [nsmul_one]
    by_cases! h : n < k
    · simp only [Nat.descFactorial_eq_zero_iff_lt.mpr h, Nat.cast_zero, zero_mul]
    · rw [Nat.cast_sub h]

/--
theorem `ascPochhammer_smeval_neg_eq_descPochhammer` / 定理 `ascPochhammer_smeval_neg_eq_descPochhammer`

English:
theorem ascPochhammer_smeval_neg_eq_descPochhammer
  given: (r : R) (k : Nat)
  proof: by
  induction k with
  | zero => simp
  | succ k ih =>
    simp only [ascPochhammer_succ_right, smeval_mul, ih, descPochhammer_succ_right, sub_eq_add_neg]
    have h : (X + (k : Nat[X])).smeval (-r) = -(X + (-k : Int[X])).smeval r := by
      simp [smeval_natCast, add_comm]
    rw [h]; rw [← neg_mul_comm]; rw [Int.natCast_add]; rw [Int.natCast_one]; rw [Int.negOnePow_succ]; rw [Units.neg_smul]; rw [Units.smul_def]; rw [Units.smul_def]; rw [← smul_mul_assoc]; rw [neg_mul]

中文:
定理 ascPochhammer_smeval_neg_eq_descPochhammer
  条件: (r : R) (k : 自然数)
  证明: by
  induction k with
  | zero => simp
  | succ k ih =>
    simp only [ascPochhammer_succ_right, smeval_mul, ih, descPochhammer_succ_right, sub_eq_add_neg]
    have h : (X + (k : Nat[X])).smeval (-r) = -(X + (-k : Int[X])).smeval r := by
      simp [smeval_natCast, add_comm]
    rw [h]; rw [← neg_mul_comm]; rw [Int.natCast_add]; rw [Int.natCast_one]; rw [Int.negOnePow_succ]; rw [Units.neg_smul]; rw [Units.smul_def]; rw [Units.smul_def]; rw [← smul_mul_assoc]; rw [neg_mul]

Depends on / 依赖: Int.natCast_add, Int.natCast_one, Int.negOnePow_succ, Units.neg_smul, Units.smul_def, add_comm, ascPochhammer_succ_right, descPochhammer_succ_right, natCast_add, natCast_one, negOnePow_succ, neg_mul, neg_mul_comm, neg_smul, smeval, smeval_mul, smeval_natCast, smul_def, smul_mul_assoc, sub_eq_add_neg
-/
theorem ascPochhammer_smeval_neg_eq_descPochhammer (r : R) (k : Nat) :
    (ascPochhammer Nat k).smeval (-r) = Int.negOnePow k • (descPochhammer Int k).smeval r := by
  induction k with
  | zero => simp
  | succ k ih =>
    simp only [ascPochhammer_succ_right, smeval_mul, ih, descPochhammer_succ_right, sub_eq_add_neg]
    have h : (X + (k : Nat[X])).smeval (-r) = -(X + (-k : Int[X])).smeval r := by
      simp [smeval_natCast, add_comm]
    rw [h]; rw [← neg_mul_comm]; rw [Int.natCast_add]; rw [Int.natCast_one]; rw [Int.negOnePow_succ]; rw [Units.neg_smul]; rw [Units.smul_def]; rw [Units.smul_def]; rw [← smul_mul_assoc]; rw [neg_mul]

end Polynomial

end Pochhammer

section Basic_Instances

open Polynomial

/--
Instance `Nat.instBinomialRing` / 实例 `Nat.instBinomialRing`

English:
instance Nat.instBinomialRing
  signature: : BinomialRing Nat where
  body: Nat.multichoose
  factorial_nsmul_multichoose r n := by
    rw [smul_eq_mul]; rw [Nat.multichoose_eq r n]; rw [← Nat.descFactorial_eq_factorial_mul_choose]; rw [← eval_eq_smeval r (ascPochhammer Nat n)]; rw [ascPochhammer_nat_eq_descFactorial]

中文:
实例 自然数.instBinomialRing
  签名: : 二项环 自然数 where
  定义体: Nat.multichoose
  factorial_nsmul_multichoose r n := by
    rw [smul_eq_mul]; rw [Nat.multichoose_eq r n]; rw [← Nat.descFactorial_eq_factorial_mul_choose]; rw [← eval_eq_smeval r (ascPochhammer Nat n)]; rw [ascPochhammer_nat_eq_descFactorial]

Depends on / 依赖: Nat.multichoose, multichoose
-/
instance Nat.instBinomialRing : BinomialRing Nat where
  multichoose := Nat.multichoose
  factorial_nsmul_multichoose r n := by
    rw [smul_eq_mul]; rw [Nat.multichoose_eq r n]; rw [← Nat.descFactorial_eq_factorial_mul_choose]; rw [← eval_eq_smeval r (ascPochhammer Nat n)]; rw [ascPochhammer_nat_eq_descFactorial]

/--
Definition of `Int.multichoose` / `Int.multichoose` 的定义

English:
definition Int.multichoose
  signature: (n : Int) (k : Nat)
  body: match n with
  | ofNat n => (Nat.choose (n + k - 1) k : Int)
  | negSucc n => Int.negOnePow k * Nat.choose (n + 1) k

中文:
定义 整数.multichoose
  签名: (n : 整数) (k : 自然数)
  定义体: match n with
  | ofNat n => (Nat.choose (n + k - 1) k : Int)
  | negSucc n => Int.negOnePow k * Nat.choose (n + 1) k

Depends on / 依赖: Int.negOnePow, Nat.choose, negOnePow, negSucc
-/
def Int.multichoose (n : Int) (k : Nat) : Int :=
  match n with
  | ofNat n => (Nat.choose (n + k - 1) k : Int)
  | negSucc n => Int.negOnePow k * Nat.choose (n + 1) k

/--
Instance `Int.instBinomialRing` / 实例 `Int.instBinomialRing`

English:
instance Int.instBinomialRing
  signature: : BinomialRing Int where
  body: Int.multichoose
  factorial_nsmul_multichoose r k := by
    rw [Int.multichoose.eq_def]; rw [nsmul_eq_mul]
    cases r with
    | ofNat n =>
      simp only [Int.ofNat_eq_natCast, Int.ofNat_mul_ofNat]
      rw [← Nat.descFactorial_eq_factorial_mul_choose]; rw [smeval_at_natCast]; rw [← eval_eq_smeval n]; rw [ascPochhammer_nat_eq_descFactorial]
    | negSucc n =>
      simp only
      rw [mul_comm]; rw [mul_assoc]; rw [← Nat.cast_mul]; rw [mul_comm _ (k.factorial)]; rw [← Nat.descFactorial_eq_factorial_mul_choose]; rw [← descPochhammer_smeval_eq_descFactorial]; rw [← Int.neg_ofNat_succ]; rw [ascPochhammer_smeval_neg_eq_descPochhammer]
      norm_cast

中文:
实例 整数.instBinomialRing
  签名: : 二项环 整数 where
  定义体: Int.multichoose
  factorial_nsmul_multichoose r k := by
    rw [Int.multichoose.eq_def]; rw [nsmul_eq_mul]
    cases r with
    | ofNat n =>
      simp only [Int.ofNat_eq_natCast, Int.ofNat_mul_ofNat]
      rw [← Nat.descFactorial_eq_factorial_mul_choose]; rw [smeval_at_natCast]; rw [← eval_eq_smeval n]; rw [ascPochhammer_nat_eq_descFactorial]
    | negSucc n =>
      simp only
      rw [mul_comm]; rw [mul_assoc]; rw [← Nat.cast_mul]; rw [mul_comm _ (k.factorial)]; rw [← Nat.descFactorial_eq_factorial_mul_choose]; rw [← descPochhammer_smeval_eq_descFactorial]; rw [← Int.neg_ofNat_succ]; rw [ascPochhammer_smeval_neg_eq_descPochhammer]
      norm_cast

Depends on / 依赖: Int.multichoose, multichoose
-/
instance Int.instBinomialRing : BinomialRing Int where
  multichoose := Int.multichoose
  factorial_nsmul_multichoose r k := by
    rw [Int.multichoose.eq_def]; rw [nsmul_eq_mul]
    cases r with
    | ofNat n =>
      simp only [Int.ofNat_eq_natCast, Int.ofNat_mul_ofNat]
      rw [← Nat.descFactorial_eq_factorial_mul_choose]; rw [smeval_at_natCast]; rw [← eval_eq_smeval n]; rw [ascPochhammer_nat_eq_descFactorial]
    | negSucc n =>
      simp only
      rw [mul_comm]; rw [mul_assoc]; rw [← Nat.cast_mul]; rw [mul_comm _ (k.factorial)]; rw [← Nat.descFactorial_eq_factorial_mul_choose]; rw [← descPochhammer_smeval_eq_descFactorial]; rw [← Int.neg_ofNat_succ]; rw [ascPochhammer_smeval_neg_eq_descPochhammer]
      norm_cast

attribute [local instance] IsAddTorsionFree.of_module_nnrat

noncomputable instance {R : Type*} [AddCommMonoid R] [Module Rat>=0 R] [Pow R Nat] : BinomialRing R where
  multichoose r n := (n.factorial : Rat>=0)⁻¹ • Polynomial.smeval (ascPochhammer Nat n) r
  factorial_nsmul_multichoose r n := by
    match_scalars
    field

end Basic_Instances

section Neg

namespace Ring

open Polynomial

variable {R : Type*} [NonAssocRing R] [Pow R Nat] [BinomialRing R]

@[simp]
/--
theorem `smeval_ascPochhammer_self_neg` / 定理 `smeval_ascPochhammer_self_neg`

English:
theorem smeval_ascPochhammer_self_neg
  statement: forall n : Nat,

中文:
定理 smeval_ascPochhammer_self_neg
  结论: 对任意 n : 自然数,
-/
theorem smeval_ascPochhammer_self_neg : forall n : Nat,
    smeval (ascPochhammer Nat n) (-n : Int) = (-1) ^ n * n.factorial
  | 0 => by
    rw [Nat.cast_zero]; rw [neg_zero]; rw [ascPochhammer_zero]; rw [Nat.factorial_zero]; rw [smeval_one]; rw [pow_zero]; rw [one_smul]; rw [pow_zero]; rw [Nat.cast_one]; rw [one_mul]
  | n + 1 => by
    rw [ascPochhammer_succ_left]; rw [smeval_X_mul]; rw [smeval_comp]; rw [smeval_add]; rw [smeval_X]; rw [smeval_one]; rw [pow_zero]; rw [pow_one]; rw [one_smul]; rw [Nat.cast_add]; rw [Nat.cast_one]; rw [neg_add_rev]; rw [neg_add_cancel_comm]; rw [smeval_ascPochhammer_self_neg n]; rw [← mul_assoc]; rw [mul_comm _ ((-1) ^ n)]; rw [show (-1 + -↑n = (-1 : Int) * (n + 1)) by lia]; rw [← mul_assoc]; rw [pow_add]; rw [pow_one]; rw [Nat.factorial]; rw [Nat.cast_mul]; rw [← mul_assoc]; rw [Nat.cast_succ]

@[simp]
/--
theorem `smeval_ascPochhammer_succ_neg` / 定理 `smeval_ascPochhammer_succ_neg`

English:
theorem smeval_ascPochhammer_succ_neg
  given: (n : Nat)
  proof: by
  rw [ascPochhammer_succ_right]; rw [smeval_mul]; rw [smeval_add]; rw [smeval_X]; rw [← C_eq_natCast]; rw [smeval_C]; rw [pow_zero]; rw [pow_one]; rw [Nat.cast_id]; rw [nsmul_eq_mul]; rw [mul_one]; rw [neg_add_cancel]; rw [mul_zero]

中文:
定理 smeval_ascPochhammer_succ_neg
  条件: (n : 自然数)
  证明: by
  rw [ascPochhammer_succ_right]; rw [smeval_mul]; rw [smeval_add]; rw [smeval_X]; rw [← C_eq_natCast]; rw [smeval_C]; rw [pow_zero]; rw [pow_one]; rw [Nat.cast_id]; rw [nsmul_eq_mul]; rw [mul_one]; rw [neg_add_cancel]; rw [mul_zero]

Depends on / 依赖: C_eq_natCast, Nat.cast_id, ascPochhammer_succ_right, cast_id, mul_one, mul_zero, neg_add_cancel, nsmul_eq_mul, pow_one, pow_zero, smeval_C, smeval_X, smeval_add, smeval_mul
-/
theorem smeval_ascPochhammer_succ_neg (n : Nat) :
    smeval (ascPochhammer Nat (n + 1)) (-n : Int) = 0 := by
  rw [ascPochhammer_succ_right]; rw [smeval_mul]; rw [smeval_add]; rw [smeval_X]; rw [← C_eq_natCast]; rw [smeval_C]; rw [pow_zero]; rw [pow_one]; rw [Nat.cast_id]; rw [nsmul_eq_mul]; rw [mul_one]; rw [neg_add_cancel]; rw [mul_zero]

/--
theorem `smeval_ascPochhammer_neg_add` / 定理 `smeval_ascPochhammer_neg_add`

English:
theorem smeval_ascPochhammer_neg_add
  given: (n : Nat)
  statement: forall k : Nat,

中文:
定理 smeval_ascPochhammer_neg_add
  条件: (n : 自然数)
  结论: 对任意 k : 自然数,
-/
theorem smeval_ascPochhammer_neg_add (n : Nat) : forall k : Nat,
    smeval (ascPochhammer Nat (n + k + 1)) (-n : Int) = 0
  | 0 => by
    rw [add_zero]; rw [smeval_ascPochhammer_succ_neg]
  | k + 1 => by
    rw [ascPochhammer_succ_right]; rw [smeval_mul]; rw [← add_assoc]; rw [smeval_ascPochhammer_neg_add n k]; rw [zero_mul]

@[simp]
/--
theorem `smeval_ascPochhammer_neg_of_lt` / 定理 `smeval_ascPochhammer_neg_of_lt`

English:
theorem smeval_ascPochhammer_neg_of_lt
  given: {n k : Nat} (h : n < k)
  proof: by
  rw [show k = n + (k - n - 1) + 1 by lia]; rw [smeval_ascPochhammer_neg_add]

中文:
定理 smeval_ascPochhammer_neg_of_lt
  条件: {n k : 自然数} (h : n < k)
  证明: by
  rw [show k = n + (k - n - 1) + 1 by lia]; rw [smeval_ascPochhammer_neg_add]

Depends on / 依赖: smeval_ascPochhammer_neg_add
-/
theorem smeval_ascPochhammer_neg_of_lt {n k : Nat} (h : n < k) :
    smeval (ascPochhammer Nat k) (-n : Int) = 0 := by
  rw [show k = n + (k - n - 1) + 1 by lia]; rw [smeval_ascPochhammer_neg_add]

/--
theorem `smeval_ascPochhammer_nat_cast` / 定理 `smeval_ascPochhammer_nat_cast`

English:
theorem smeval_ascPochhammer_nat_cast
  given: {R} [NonAssocSemiring R] [Pow R Nat] [NatPowAssoc R] (n k : Nat)
  proof: by
  rw [smeval_at_natCast (ascPochhammer Nat k) n]

中文:
定理 smeval_ascPochhammer_nat_cast
  条件: {R} [非结合半环 R] [幂 R 自然数] [自然数PowAssoc R] (n k : 自然数)
  证明: by
  rw [smeval_at_natCast (ascPochhammer Nat k) n]

Depends on / 依赖: ascPochhammer, smeval_at_natCast
-/
theorem smeval_ascPochhammer_nat_cast {R} [NonAssocSemiring R] [Pow R Nat] [NatPowAssoc R] (n k : Nat) :
    smeval (ascPochhammer Nat k) (n : R) = smeval (ascPochhammer Nat k) n := by
  rw [smeval_at_natCast (ascPochhammer Nat k) n]

/--
theorem `multichoose_neg_self` / 定理 `multichoose_neg_self`

English:
theorem multichoose_neg_self
  given: (n : Nat)
  statement: multichoose (-n : Int) n = (-1) ^ n
  proof: by
  rw [← nsmul_right_inj (Nat.factorial_ne_zero _)]; rw [factorial_nsmul_multichoose_eq_ascPochhammer]; rw [smeval_ascPochhammer_self_neg]; rw [nsmul_eq_mul]; rw [Nat.cast_comm]

@[simp]

中文:
定理 multichoose_neg_self
  条件: (n : 自然数)
  结论: multichoose (-n : 整数) n = (-1) ^ n
  证明: by
  rw [← nsmul_right_inj (Nat.factorial_ne_zero _)]; rw [factorial_nsmul_multichoose_eq_ascPochhammer]; rw [smeval_ascPochhammer_self_neg]; rw [nsmul_eq_mul]; rw [Nat.cast_comm]

@[simp]

Depends on / 依赖: Nat.cast_comm, Nat.factorial_ne_zero, cast_comm, factorial_ne_zero, factorial_nsmul_multichoose_eq_ascPochhammer, nsmul_eq_mul, nsmul_right_inj, smeval_ascPochhammer_self_neg
-/
theorem multichoose_neg_self (n : Nat) : multichoose (-n : Int) n = (-1) ^ n := by
  rw [← nsmul_right_inj (Nat.factorial_ne_zero _)]; rw [factorial_nsmul_multichoose_eq_ascPochhammer]; rw [smeval_ascPochhammer_self_neg]; rw [nsmul_eq_mul]; rw [Nat.cast_comm]

@[simp]
/--
theorem `multichoose_neg_succ` / 定理 `multichoose_neg_succ`

English:
theorem multichoose_neg_succ
  given: (n : Nat)
  statement: multichoose (-n : Int) (n + 1) = 0
  proof: by
  rw [← nsmul_right_inj (Nat.factorial_ne_zero _)]; rw [factorial_nsmul_multichoose_eq_ascPochhammer]; rw [smeval_ascPochhammer_succ_neg]; rw [smul_zero]

中文:
定理 multichoose_neg_succ
  条件: (n : 自然数)
  结论: multichoose (-n : 整数) (n + 1) = 0
  证明: by
  rw [← nsmul_right_inj (Nat.factorial_ne_zero _)]; rw [factorial_nsmul_multichoose_eq_ascPochhammer]; rw [smeval_ascPochhammer_succ_neg]; rw [smul_zero]

Depends on / 依赖: Nat.factorial_ne_zero, factorial_ne_zero, factorial_nsmul_multichoose_eq_ascPochhammer, nsmul_right_inj, smeval_ascPochhammer_succ_neg, smul_zero
-/
theorem multichoose_neg_succ (n : Nat) : multichoose (-n : Int) (n + 1) = 0 := by
  rw [← nsmul_right_inj (Nat.factorial_ne_zero _)]; rw [factorial_nsmul_multichoose_eq_ascPochhammer]; rw [smeval_ascPochhammer_succ_neg]; rw [smul_zero]

/--
theorem `multichoose_neg_add` / 定理 `multichoose_neg_add`

English:
theorem multichoose_neg_add
  given: (n k : Nat)
  statement: multichoose (-n : Int) (n + k + 1) = 0
  proof: by
  rw [← nsmul_right_inj (Nat.factorial_ne_zero (n + k + 1))]; rw [factorial_nsmul_multichoose_eq_ascPochhammer]; rw [smeval_ascPochhammer_neg_add]; rw [smul_zero]

@[simp]

中文:
定理 multichoose_neg_add
  条件: (n k : 自然数)
  结论: multichoose (-n : 整数) (n + k + 1) = 0
  证明: by
  rw [← nsmul_right_inj (Nat.factorial_ne_zero (n + k + 1))]; rw [factorial_nsmul_multichoose_eq_ascPochhammer]; rw [smeval_ascPochhammer_neg_add]; rw [smul_zero]

@[simp]

Depends on / 依赖: Nat.factorial_ne_zero, factorial_ne_zero, factorial_nsmul_multichoose_eq_ascPochhammer, nsmul_right_inj, smeval_ascPochhammer_neg_add, smul_zero
-/
theorem multichoose_neg_add (n k : Nat) : multichoose (-n : Int) (n + k + 1) = 0 := by
  rw [← nsmul_right_inj (Nat.factorial_ne_zero (n + k + 1))]; rw [factorial_nsmul_multichoose_eq_ascPochhammer]; rw [smeval_ascPochhammer_neg_add]; rw [smul_zero]

@[simp]
/--
theorem `multichoose_neg_of_lt` / 定理 `multichoose_neg_of_lt`

English:
theorem multichoose_neg_of_lt
  given: (n k : Nat) (h : n < k)
  statement: multichoose (-n : Int) k = 0
  proof: by
  rw [← nsmul_right_inj (Nat.factorial_ne_zero k)]; rw [factorial_nsmul_multichoose_eq_ascPochhammer]; rw [smeval_ascPochhammer_neg_of_lt h]; rw [smul_zero]

中文:
定理 multichoose_neg_of_lt
  条件: (n k : 自然数) (h : n < k)
  结论: multichoose (-n : 整数) k = 0
  证明: by
  rw [← nsmul_right_inj (Nat.factorial_ne_zero k)]; rw [factorial_nsmul_multichoose_eq_ascPochhammer]; rw [smeval_ascPochhammer_neg_of_lt h]; rw [smul_zero]

Depends on / 依赖: Nat.factorial_ne_zero, factorial_ne_zero, factorial_nsmul_multichoose_eq_ascPochhammer, nsmul_right_inj, smeval_ascPochhammer_neg_of_lt, smul_zero
-/
theorem multichoose_neg_of_lt (n k : Nat) (h : n < k) : multichoose (-n : Int) k = 0 := by
  rw [← nsmul_right_inj (Nat.factorial_ne_zero k)]; rw [factorial_nsmul_multichoose_eq_ascPochhammer]; rw [smeval_ascPochhammer_neg_of_lt h]; rw [smul_zero]

/--
theorem `multichoose_succ_neg_natCast` / 定理 `multichoose_succ_neg_natCast`

English:
theorem multichoose_succ_neg_natCast
  given: [NatPowAssoc R] (n : Nat)
  proof: by
  rw [← nsmul_right_inj (Nat.factorial_ne_zero (n + 1))]; rw [smul_zero]; rw [factorial_nsmul_multichoose_eq_ascPochhammer]; rw [smeval_neg_nat]; rw [smeval_ascPochhammer_succ_neg n]; rw [Int.cast_zero]

中文:
定理 multichoose_succ_neg_natCast
  条件: [自然数PowAssoc R] (n : 自然数)
  证明: by
  rw [← nsmul_right_inj (Nat.factorial_ne_zero (n + 1))]; rw [smul_zero]; rw [factorial_nsmul_multichoose_eq_ascPochhammer]; rw [smeval_neg_nat]; rw [smeval_ascPochhammer_succ_neg n]; rw [Int.cast_zero]

Depends on / 依赖: Int.cast_zero, Nat.factorial_ne_zero, cast_zero, factorial_ne_zero, factorial_nsmul_multichoose_eq_ascPochhammer, nsmul_right_inj, smeval_ascPochhammer_succ_neg, smeval_neg_nat, smul_zero
-/
theorem multichoose_succ_neg_natCast [NatPowAssoc R] (n : Nat) :
    multichoose (-n : R) (n + 1) = 0 := by
  rw [← nsmul_right_inj (Nat.factorial_ne_zero (n + 1))]; rw [smul_zero]; rw [factorial_nsmul_multichoose_eq_ascPochhammer]; rw [smeval_neg_nat]; rw [smeval_ascPochhammer_succ_neg n]; rw [Int.cast_zero]

/--
theorem `smeval_ascPochhammer_int_ofNat` / 定理 `smeval_ascPochhammer_int_ofNat`

English:
theorem smeval_ascPochhammer_int_ofNat
  given: {R} [NonAssocRing R] [Pow R Nat] [NatPowAssoc R] (r : R)

中文:
定理 smeval_ascPochhammer_int_of自然数
  条件: {R} [非结合环 R] [幂 R 自然数] [自然数PowAssoc R] (r : R)
-/
theorem smeval_ascPochhammer_int_ofNat {R} [NonAssocRing R] [Pow R Nat] [NatPowAssoc R] (r : R) :
    forall n : Nat, smeval (ascPochhammer Int n) r = smeval (ascPochhammer Nat n) r
  | 0 => by
    simp only [ascPochhammer_zero, smeval_one]
  | n + 1 => by
    simp only [ascPochhammer_succ_right, smeval_mul]
    rw [smeval_ascPochhammer_int_ofNat r n]
    simp only [smeval_add, smeval_X, ← C_eq_natCast, smeval_C, natCast_zsmul, nsmul_eq_mul,
      Nat.cast_id]

end Ring

end Neg

section Choose

namespace Ring

open Polynomial

variable {R : Type*}

section

/--
Definition of `choose` / `choose` 的定义

English:
definition choose
  signature: [AddCommGroupWithOne R] [Pow R Nat] [BinomialRing R] (r : R) (n : Nat)
  body: multichoose (r - n + 1) n

中文:
定义 choose
  签名: [加法交换带幺群 R] [幂 R 自然数] [二项环 R] (r : R) (n : 自然数)
  定义体: multichoose (r - n + 1) n

Depends on / 依赖: multichoose
-/
def choose [AddCommGroupWithOne R] [Pow R Nat] [BinomialRing R] (r : R) (n : Nat) : R :=
  multichoose (r - n + 1) n

variable [NonAssocRing R] [Pow R Nat] [BinomialRing R]

/--
theorem `multichoose_eq` / 定理 `multichoose_eq`

English:
theorem multichoose_eq
  given: (r : R) (n : Nat)
  statement: multichoose r n = choose (r + n - 1) n
  proof: by
  rw [choose]
  congr
  abel

中文:
定理 multichoose_eq
  条件: (r : R) (n : 自然数)
  结论: multichoose r n = choose (r + n - 1) n
  证明: by
  rw [choose]
  congr
  abel
-/
theorem multichoose_eq (r : R) (n : Nat) : multichoose r n = choose (r + n - 1) n := by
  rw [choose]
  congr
  abel

/--
theorem `descPochhammer_eq_factorial_smul_choose` / 定理 `descPochhammer_eq_factorial_smul_choose`

English:
theorem descPochhammer_eq_factorial_smul_choose
  given: [NatPowAssoc R] (r : R) (n : Nat)
  proof: by
  rw [choose]; rw [factorial_nsmul_multichoose_eq_ascPochhammer]; rw [descPochhammer_eq_ascPochhammer]; rw [smeval_comp]; rw [add_comm_sub]; rw [smeval_add]; rw [smeval_X]; rw [npow_one]
  have h : smeval (1 - n : Polynomial Int) r = 1 - n := by
    rw [← C_eq_natCast]; rw [← C_1]; rw [← C_sub]; rw [smeval_C]
    simp only [npow_zero, zsmul_one, Int.cast_sub, Int.cast_one, Int.cast_natCast]
  rw [h]; rw [ascPochhammer_smeval_cast]; rw [add_comm_sub]

中文:
定理 descPochhammer_eq_factorial_smul_choose
  条件: [自然数PowAssoc R] (r : R) (n : 自然数)
  证明: by
  rw [choose]; rw [factorial_nsmul_multichoose_eq_ascPochhammer]; rw [descPochhammer_eq_ascPochhammer]; rw [smeval_comp]; rw [add_comm_sub]; rw [smeval_add]; rw [smeval_X]; rw [npow_one]
  have h : smeval (1 - n : Polynomial Int) r = 1 - n := by
    rw [← C_eq_natCast]; rw [← C_1]; rw [← C_sub]; rw [smeval_C]
    simp only [npow_zero, zsmul_one, Int.cast_sub, Int.cast_one, Int.cast_natCast]
  rw [h]; rw [ascPochhammer_smeval_cast]; rw [add_comm_sub]

Depends on / 依赖: C_eq_natCast, C_sub, Int.cast_natCast, Int.cast_one, Int.cast_sub, Polynomial, add_comm_sub, ascPochhammer_smeval_cast, cast_natCast, cast_one, cast_sub, descPochhammer_eq_ascPochhammer, factorial_nsmul_multichoose_eq_ascPochhammer, npow_one, npow_zero, smeval, smeval_C, smeval_X, smeval_add, smeval_comp
-/
theorem descPochhammer_eq_factorial_smul_choose [NatPowAssoc R] (r : R) (n : Nat) :
    (descPochhammer Int n).smeval r = n.factorial • choose r n := by
  rw [choose]; rw [factorial_nsmul_multichoose_eq_ascPochhammer]; rw [descPochhammer_eq_ascPochhammer]; rw [smeval_comp]; rw [add_comm_sub]; rw [smeval_add]; rw [smeval_X]; rw [npow_one]
  have h : smeval (1 - n : Polynomial Int) r = 1 - n := by
    rw [← C_eq_natCast]; rw [← C_1]; rw [← C_sub]; rw [smeval_C]
    simp only [npow_zero, zsmul_one, Int.cast_sub, Int.cast_one, Int.cast_natCast]
  rw [h]; rw [ascPochhammer_smeval_cast]; rw [add_comm_sub]

/--
theorem `choose_natCast` / 定理 `choose_natCast`

English:
theorem choose_natCast
  given: [NatPowAssoc R] (n k : Nat)
  statement: choose (n : R) k = Nat.choose n k
  proof: by
  rw [← nsmul_right_inj (Nat.factorial_ne_zero k)]; rw [← descPochhammer_eq_factorial_smul_choose]; rw [nsmul_eq_mul]; rw [← Nat.cast_mul]; rw [← Nat.descFactorial_eq_factorial_mul_choose]; rw [← descPochhammer_smeval_eq_descFactorial]

@[simp]

中文:
定理 choose_natCast
  条件: [自然数PowAssoc R] (n k : 自然数)
  结论: choose (n : R) k = 自然数.choose n k
  证明: by
  rw [← nsmul_right_inj (Nat.factorial_ne_zero k)]; rw [← descPochhammer_eq_factorial_smul_choose]; rw [nsmul_eq_mul]; rw [← Nat.cast_mul]; rw [← Nat.descFactorial_eq_factorial_mul_choose]; rw [← descPochhammer_smeval_eq_descFactorial]

@[simp]

Depends on / 依赖: Nat.cast_mul, Nat.descFactorial_eq_factorial_mul_choose, Nat.factorial_ne_zero, cast_mul, descFactorial_eq_factorial_mul_choose, descPochhammer_eq_factorial_smul_choose, descPochhammer_smeval_eq_descFactorial, factorial_ne_zero, nsmul_eq_mul, nsmul_right_inj
-/
theorem choose_natCast [NatPowAssoc R] (n k : Nat) : choose (n : R) k = Nat.choose n k := by
  rw [← nsmul_right_inj (Nat.factorial_ne_zero k)]; rw [← descPochhammer_eq_factorial_smul_choose]; rw [nsmul_eq_mul]; rw [← Nat.cast_mul]; rw [← Nat.descFactorial_eq_factorial_mul_choose]; rw [← descPochhammer_smeval_eq_descFactorial]

@[simp]
/--
theorem `choose_zero_right'` / 定理 `choose_zero_right'`

English:
theorem choose_zero_right'
  given: (r : R)
  statement: choose r 0 = (r + 1) ^ 0
  proof: by
  dsimp only [choose]
  rw [← nsmul_right_inj (Nat.factorial_ne_zero 0)]
  simp

中文:
定理 choose_zero_right'
  条件: (r : R)
  结论: choose r 0 = (r + 1) ^ 0
  证明: by
  dsimp only [choose]
  rw [← nsmul_right_inj (Nat.factorial_ne_zero 0)]
  simp

Depends on / 依赖: Nat.factorial_ne_zero, factorial_ne_zero, nsmul_right_inj
-/
theorem choose_zero_right' (r : R) : choose r 0 = (r + 1) ^ 0 := by
  dsimp only [choose]
  rw [← nsmul_right_inj (Nat.factorial_ne_zero 0)]
  simp

/--
theorem `choose_zero_right` / 定理 `choose_zero_right`

English:
theorem choose_zero_right
  given: [NatPowAssoc R] (r : R)
  statement: choose r 0 = 1
  proof: by
  rw [choose_zero_right']; rw [npow_zero]

@[simp]

中文:
定理 choose_zero_right
  条件: [自然数PowAssoc R] (r : R)
  结论: choose r 0 = 1
  证明: by
  rw [choose_zero_right']; rw [npow_zero]

@[simp]

Depends on / 依赖: choose_zero_right, npow_zero
-/
theorem choose_zero_right [NatPowAssoc R] (r : R) : choose r 0 = 1 := by
  rw [choose_zero_right']; rw [npow_zero]

@[simp]
/--
theorem `choose_zero_succ` / 定理 `choose_zero_succ`

English:
theorem choose_zero_succ
  statement: (R) [NonAssocRing R] [Pow R Nat] [NatPowAssoc R] [BinomialRing R]
  proof: by
  rw [choose]; rw [Nat.cast_succ]; rw [zero_sub]; rw [neg_add]; rw [neg_add_cancel_right]; rw [multichoose_succ_neg_natCast]

中文:
定理 choose_zero_succ
  结论: (R) [非结合环 R] [幂 R 自然数] [自然数PowAssoc R] [二项环 R]
  证明: by
  rw [choose]; rw [Nat.cast_succ]; rw [zero_sub]; rw [neg_add]; rw [neg_add_cancel_right]; rw [multichoose_succ_neg_natCast]

Depends on / 依赖: Nat.cast_succ, cast_succ, multichoose_succ_neg_natCast, neg_add, neg_add_cancel_right, zero_sub
-/
theorem choose_zero_succ (R) [NonAssocRing R] [Pow R Nat] [NatPowAssoc R] [BinomialRing R]
    (n : Nat) : choose (0 : R) (n + 1) = 0 := by
  rw [choose]; rw [Nat.cast_succ]; rw [zero_sub]; rw [neg_add]; rw [neg_add_cancel_right]; rw [multichoose_succ_neg_natCast]

/--
theorem `choose_zero_pos` / 定理 `choose_zero_pos`

English:
theorem choose_zero_pos
  statement: (R) [NonAssocRing R] [Pow R Nat] [NatPowAssoc R] [BinomialRing R]
  proof: by
  rw [← Nat.succ_pred_eq_of_pos h_pos]; rw [choose_zero_succ]

中文:
定理 choose_zero_pos
  结论: (R) [非结合环 R] [幂 R 自然数] [自然数PowAssoc R] [二项环 R]
  证明: by
  rw [← Nat.succ_pred_eq_of_pos h_pos]; rw [choose_zero_succ]

Depends on / 依赖: Nat.succ_pred_eq_of_pos, choose_zero_succ, h_pos, succ_pred_eq_of_pos
-/
theorem choose_zero_pos (R) [NonAssocRing R] [Pow R Nat] [NatPowAssoc R] [BinomialRing R]
    {k : Nat} (h_pos : 0 < k) : choose (0 : R) k = 0 := by
  rw [← Nat.succ_pred_eq_of_pos h_pos]; rw [choose_zero_succ]

/--
theorem `choose_zero_ite` / 定理 `choose_zero_ite`

English:
theorem choose_zero_ite
  statement: (R) [NonAssocRing R] [Pow R Nat] [NatPowAssoc R] [BinomialRing R]
  proof: by
  split_ifs with hk
  · rw [hk, choose_zero_right]
  · rw [choose_zero_pos R <| Nat.pos_of_ne_zero hk]

@[simp]

中文:
定理 choose_zero_ite
  结论: (R) [非结合环 R] [幂 R 自然数] [自然数PowAssoc R] [二项环 R]
  证明: by
  split_ifs with hk
  · rw [hk, choose_zero_right]
  · rw [choose_zero_pos R <| Nat.pos_of_ne_zero hk]

@[simp]

Depends on / 依赖: Nat.pos_of_ne_zero, choose_zero_pos, choose_zero_right, pos_of_ne_zero, split_ifs
-/
theorem choose_zero_ite (R) [NonAssocRing R] [Pow R Nat] [NatPowAssoc R] [BinomialRing R]
    (k : Nat) : choose (0 : R) k = if k = 0 then 1 else 0 := by
  split_ifs with hk
  · rw [hk, choose_zero_right]
  · rw [choose_zero_pos R <| Nat.pos_of_ne_zero hk]

@[simp]
/--
theorem `choose_one_right'` / 定理 `choose_one_right'`

English:
theorem choose_one_right'
  given: (r : R)
  statement: choose r 1 = r ^ 1
  proof: by
  rw [choose]; rw [Nat.cast_one]; rw [sub_add_cancel]; rw [multichoose_one_right']

中文:
定理 choose_one_right'
  条件: (r : R)
  结论: choose r 1 = r ^ 1
  证明: by
  rw [choose]; rw [Nat.cast_one]; rw [sub_add_cancel]; rw [multichoose_one_right']

Depends on / 依赖: Nat.cast_one, cast_one, multichoose_one_right, sub_add_cancel
-/
theorem choose_one_right' (r : R) : choose r 1 = r ^ 1 := by
  rw [choose]; rw [Nat.cast_one]; rw [sub_add_cancel]; rw [multichoose_one_right']

/--
theorem `choose_one_right` / 定理 `choose_one_right`

English:
theorem choose_one_right
  given: [NatPowAssoc R] (r : R)
  statement: choose r 1 = r
  proof: by
  rw [choose_one_right']; rw [npow_one]

中文:
定理 choose_one_right
  条件: [自然数PowAssoc R] (r : R)
  结论: choose r 1 = r
  证明: by
  rw [choose_one_right']; rw [npow_one]

Depends on / 依赖: choose_one_right, npow_one
-/
theorem choose_one_right [NatPowAssoc R] (r : R) : choose r 1 = r := by
  rw [choose_one_right']; rw [npow_one]

/--
theorem `choose_neg` / 定理 `choose_neg`

English:
theorem choose_neg
  given: [NatPowAssoc R] (r : R) (n : Nat)
  proof: by
  apply (nsmul_right_inj (Nat.factorial_ne_zero n)).mp
  rw [← descPochhammer_eq_factorial_smul_choose]; rw [smul_comm]; rw [← descPochhammer_eq_factorial_smul_choose]; rw [descPochhammer_smeval_eq_ascPochhammer]; rw [show (-r - n + 1) = -(r + n - 1) by abel]; rw [ascPochhammer_smeval_neg_eq_descPochhammer]

中文:
定理 choose_neg
  条件: [自然数PowAssoc R] (r : R) (n : 自然数)
  证明: by
  apply (nsmul_right_inj (Nat.factorial_ne_zero n)).mp
  rw [← descPochhammer_eq_factorial_smul_choose]; rw [smul_comm]; rw [← descPochhammer_eq_factorial_smul_choose]; rw [descPochhammer_smeval_eq_ascPochhammer]; rw [show (-r - n + 1) = -(r + n - 1) by abel]; rw [ascPochhammer_smeval_neg_eq_descPochhammer]

Depends on / 依赖: Nat.factorial_ne_zero, ascPochhammer_smeval_neg_eq_descPochhammer, descPochhammer_eq_factorial_smul_choose, descPochhammer_smeval_eq_ascPochhammer, factorial_ne_zero, nsmul_right_inj, smul_comm
-/
theorem choose_neg [NatPowAssoc R] (r : R) (n : Nat) :
    choose (-r) n = Int.negOnePow n • choose (r + n - 1) n := by
  apply (nsmul_right_inj (Nat.factorial_ne_zero n)).mp
  rw [← descPochhammer_eq_factorial_smul_choose]; rw [smul_comm]; rw [← descPochhammer_eq_factorial_smul_choose]; rw [descPochhammer_smeval_eq_ascPochhammer]; rw [show (-r - n + 1) = -(r + n - 1) by abel]; rw [ascPochhammer_smeval_neg_eq_descPochhammer]

/--
theorem `choose_neg'` / 定理 `choose_neg'`

English:
theorem choose_neg'
  given: [NatPowAssoc R] (r : R) (n : Nat)
  proof: by
  rw [choose_neg]; rw [multichoose_eq]

中文:
定理 choose_neg'
  条件: [自然数PowAssoc R] (r : R) (n : 自然数)
  证明: by
  rw [choose_neg]; rw [multichoose_eq]

Depends on / 依赖: choose_neg, multichoose_eq
-/
theorem choose_neg' [NatPowAssoc R] (r : R) (n : Nat) :
    choose (-r) n = Int.negOnePow n • multichoose r n := by
  rw [choose_neg]; rw [multichoose_eq]

/--
theorem `descPochhammer_succ_succ_smeval` / 定理 `descPochhammer_succ_succ_smeval`

English:
theorem descPochhammer_succ_succ_smeval
  statement: {R} [NonAssocRing R] [Pow R Nat] [NatPowAssoc R]
  proof: by
  nth_rw 1 [descPochhammer_succ_left]
  rw [descPochhammer_succ_right]; rw [mul_comm (descPochhammer Int k)]
  simp only [smeval_comp, smeval_sub, smeval_mul, smeval_X, smeval_one, npow_one,
    npow_zero, one_smul, add_sub_cancel_right, sub_mul, add_mul, add_smul, one_mul]
  rw [← C_eq_natCast]; rw [smeval_C]; rw [npow_zero]; rw [add_comm (k • smeval (descPochhammer Int k) r) _]; rw [add_assoc]; rw [add_comm (k • smeval (descPochhammer Int k) r) _]; rw [← add_assoc]; rw [← add_sub_assoc]; rw [nsmul_eq_mul]; rw [zsmul_one]; rw [Int.cast_natCast]; rw [sub_add_cancel]; rw [add_comm]

中文:
定理 descPochhammer_succ_succ_smeval
  结论: {R} [非结合环 R] [幂 R 自然数] [自然数PowAssoc R]
  证明: by
  nth_rw 1 [descPochhammer_succ_left]
  rw [descPochhammer_succ_right]; rw [mul_comm (descPochhammer Int k)]
  simp only [smeval_comp, smeval_sub, smeval_mul, smeval_X, smeval_one, npow_one,
    npow_zero, one_smul, add_sub_cancel_right, sub_mul, add_mul, add_smul, one_mul]
  rw [← C_eq_natCast]; rw [smeval_C]; rw [npow_zero]; rw [add_comm (k • smeval (descPochhammer Int k) r) _]; rw [add_assoc]; rw [add_comm (k • smeval (descPochhammer Int k) r) _]; rw [← add_assoc]; rw [← add_sub_assoc]; rw [nsmul_eq_mul]; rw [zsmul_one]; rw [Int.cast_natCast]; rw [sub_add_cancel]; rw [add_comm]

Depends on / 依赖: C_eq_natCast, add_assoc, add_comm, add_mul, add_smul, add_sub_assoc, add_sub_cancel_right, descPochhammer, descPochhammer_succ_left, descPochhammer_succ_right, mul_comm, npow_one, npow_zero, nsmul_eq_m, nth_rw, one_mul, one_smul, smeval, smeval_C, smeval_X
-/
theorem descPochhammer_succ_succ_smeval {R} [NonAssocRing R] [Pow R Nat] [NatPowAssoc R]
    (r : R) (k : Nat) : smeval (descPochhammer Int (k + 1)) (r + 1) =
    (k + 1) • smeval (descPochhammer Int k) r + smeval (descPochhammer Int (k + 1)) r := by
  nth_rw 1 [descPochhammer_succ_left]
  rw [descPochhammer_succ_right]; rw [mul_comm (descPochhammer Int k)]
  simp only [smeval_comp, smeval_sub, smeval_mul, smeval_X, smeval_one, npow_one,
    npow_zero, one_smul, add_sub_cancel_right, sub_mul, add_mul, add_smul, one_mul]
  rw [← C_eq_natCast]; rw [smeval_C]; rw [npow_zero]; rw [add_comm (k • smeval (descPochhammer Int k) r) _]; rw [add_assoc]; rw [add_comm (k • smeval (descPochhammer Int k) r) _]; rw [← add_assoc]; rw [← add_sub_assoc]; rw [nsmul_eq_mul]; rw [zsmul_one]; rw [Int.cast_natCast]; rw [sub_add_cancel]; rw [add_comm]

/--
theorem `choose_succ_succ` / 定理 `choose_succ_succ`

English:
theorem choose_succ_succ
  given: [NatPowAssoc R] (r : R) (k : Nat)
  proof: by
  rw [← nsmul_right_inj (Nat.factorial_ne_zero (k + 1))]
  simp only [smul_add, ← descPochhammer_eq_factorial_smul_choose]
  rw [Nat.factorial_succ]; rw [mul_smul]; rw [← descPochhammer_eq_factorial_smul_choose r]; rw [descPochhammer_succ_succ_smeval r k]

中文:
定理 choose_succ_succ
  条件: [自然数PowAssoc R] (r : R) (k : 自然数)
  证明: by
  rw [← nsmul_right_inj (Nat.factorial_ne_zero (k + 1))]
  simp only [smul_add, ← descPochhammer_eq_factorial_smul_choose]
  rw [Nat.factorial_succ]; rw [mul_smul]; rw [← descPochhammer_eq_factorial_smul_choose r]; rw [descPochhammer_succ_succ_smeval r k]

Depends on / 依赖: Nat.factorial_ne_zero, Nat.factorial_succ, descPochhammer_eq_factorial_smul_choose, descPochhammer_succ_succ_smeval, factorial_ne_zero, factorial_succ, mul_smul, nsmul_right_inj, smul_add
-/
theorem choose_succ_succ [NatPowAssoc R] (r : R) (k : Nat) :
    choose (r + 1) (k + 1) = choose r k + choose r (k + 1) := by
  rw [← nsmul_right_inj (Nat.factorial_ne_zero (k + 1))]
  simp only [smul_add, ← descPochhammer_eq_factorial_smul_choose]
  rw [Nat.factorial_succ]; rw [mul_smul]; rw [← descPochhammer_eq_factorial_smul_choose r]; rw [descPochhammer_succ_succ_smeval r k]

/--
theorem `choose_smul_choose` / 定理 `choose_smul_choose`

English:
theorem choose_smul_choose
  given: [NatPowAssoc R] (r : R) {n k : Nat} (hkn : k <= n)
  proof: by
  rw [← nsmul_right_inj (Nat.factorial_ne_zero n)]; rw [nsmul_left_comm]; rw [← descPochhammer_eq_factorial_smul_choose]; rw [← Nat.choose_mul_factorial_mul_factorial hkn]; rw [← smul_mul_smul_comm]; rw [← descPochhammer_eq_factorial_smul_choose]; rw [mul_nsmul']; rw [← descPochhammer_eq_factorial_smul_choose]; rw [smul_mul_assoc]
  nth_rw 2 [← Nat.sub_add_cancel hkn]
  rw [add_comm]; rw [← descPochhammer_mul]; rw [smeval_mul]; rw [smeval_comp]; rw [smeval_sub]; rw [smeval_X]; rw [← C_eq_natCast]; rw [smeval_C]; rw [npow_one]; rw [npow_zero]; rw [zsmul_one]; rw [Int.cast_natCast]; rw [nsmul_eq_mul]

中文:
定理 choose_smul_choose
  条件: [自然数PowAssoc R] (r : R) {n k : 自然数} (hkn : k <= n)
  证明: by
  rw [← nsmul_right_inj (Nat.factorial_ne_zero n)]; rw [nsmul_left_comm]; rw [← descPochhammer_eq_factorial_smul_choose]; rw [← Nat.choose_mul_factorial_mul_factorial hkn]; rw [← smul_mul_smul_comm]; rw [← descPochhammer_eq_factorial_smul_choose]; rw [mul_nsmul']; rw [← descPochhammer_eq_factorial_smul_choose]; rw [smul_mul_assoc]
  nth_rw 2 [← Nat.sub_add_cancel hkn]
  rw [add_comm]; rw [← descPochhammer_mul]; rw [smeval_mul]; rw [smeval_comp]; rw [smeval_sub]; rw [smeval_X]; rw [← C_eq_natCast]; rw [smeval_C]; rw [npow_one]; rw [npow_zero]; rw [zsmul_one]; rw [Int.cast_natCast]; rw [nsmul_eq_mul]

Depends on / 依赖: C_eq_natCast, Nat.choose_mul_factorial_mul_factorial, Nat.factorial_ne_zero, Nat.sub_add_cancel, add_comm, choose_mul_factorial_mul_factorial, descPochhammer_eq_factorial_smul_choose, descPochhammer_mul, factorial_ne_zero, mul_nsmul, nsmul_left_comm, nsmul_right_inj, nth_rw, smeval_X, smeval_comp, smeval_mul, smeval_sub, smul_mul_assoc, smul_mul_smul_comm, sub_add_cancel
-/
theorem choose_smul_choose [NatPowAssoc R] (r : R) {n k : Nat} (hkn : k <= n) :
    (Nat.choose n k) • choose r n = choose r k * choose (r - k) (n - k) := by
  rw [← nsmul_right_inj (Nat.factorial_ne_zero n)]; rw [nsmul_left_comm]; rw [← descPochhammer_eq_factorial_smul_choose]; rw [← Nat.choose_mul_factorial_mul_factorial hkn]; rw [← smul_mul_smul_comm]; rw [← descPochhammer_eq_factorial_smul_choose]; rw [mul_nsmul']; rw [← descPochhammer_eq_factorial_smul_choose]; rw [smul_mul_assoc]
  nth_rw 2 [← Nat.sub_add_cancel hkn]
  rw [add_comm]; rw [← descPochhammer_mul]; rw [smeval_mul]; rw [smeval_comp]; rw [smeval_sub]; rw [smeval_X]; rw [← C_eq_natCast]; rw [smeval_C]; rw [npow_one]; rw [npow_zero]; rw [zsmul_one]; rw [Int.cast_natCast]; rw [nsmul_eq_mul]

/--
theorem `choose_add_smul_choose` / 定理 `choose_add_smul_choose`

English:
theorem choose_add_smul_choose
  given: [NatPowAssoc R] (r : R) (n k : Nat)
  proof: by
  rw [choose_smul_choose (r + k) (Nat.le_add_left k n)]; rw [Nat.add_sub_cancel]; rw [add_sub_cancel_right]

中文:
定理 choose_add_smul_choose
  条件: [自然数PowAssoc R] (r : R) (n k : 自然数)
  证明: by
  rw [choose_smul_choose (r + k) (Nat.le_add_left k n)]; rw [Nat.add_sub_cancel]; rw [add_sub_cancel_right]

Depends on / 依赖: Nat.add_sub_cancel, Nat.le_add_left, add_sub_cancel, add_sub_cancel_right, choose_smul_choose, le_add_left
-/
theorem choose_add_smul_choose [NatPowAssoc R] (r : R) (n k : Nat) :
    (Nat.choose (n + k) k) • choose (r + k) (n + k) = choose (r + k) k * choose r n := by
  rw [choose_smul_choose (r + k) (Nat.le_add_left k n)]; rw [Nat.add_sub_cancel]; rw [add_sub_cancel_right]

end

/--
theorem `choose_eq_smul` / 定理 `choose_eq_smul`

English:
theorem choose_eq_smul
  given: [Field R] [CharZero R] {a : R} {n : Nat}
  proof: by
  rw [Ring.descPochhammer_eq_factorial_smul_choose]; rw [← Nat.cast_smul_eq_nsmul R]; rw [inv_smul_smul₀]
  simpa using Nat.factorial_ne_zero n

中文:
定理 choose_eq_smul
  条件: [域 R] [特征零 R] {a : R} {n : 自然数}
  证明: by
  rw [Ring.descPochhammer_eq_factorial_smul_choose]; rw [← Nat.cast_smul_eq_nsmul R]; rw [inv_smul_smul₀]
  simpa using Nat.factorial_ne_zero n

Depends on / 依赖: Nat.cast_smul_eq_nsmul, Nat.factorial_ne_zero, Ring.descPochhammer_eq_factorial_smul_choose, cast_smul_eq_nsmul, descPochhammer_eq_factorial_smul_choose, factorial_ne_zero
-/
theorem choose_eq_smul [Field R] [CharZero R] {a : R} {n : Nat} :
    Ring.choose a n = (n.factorial : R)⁻¹ • (descPochhammer Int n).smeval a := by
  rw [Ring.descPochhammer_eq_factorial_smul_choose]; rw [← Nat.cast_smul_eq_nsmul R]; rw [inv_smul_smul₀]
  simpa using Nat.factorial_ne_zero n

open Finset

/--
theorem `descPochhammer_smeval_add` / 定理 `descPochhammer_smeval_add`

English:
theorem descPochhammer_smeval_add
  given: [Ring R] {r s : R} (k : Nat) (h : Commute r s)
  proof: by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [descPochhammer_succ_right]; rw [mul_comm]; rw [smeval_mul]; rw [sum_antidiagonal_choose_succ_mul
      fun i j => ((descPochhammer Int i).smeval r * (descPochhammer Int j).smeval s)]; rw [← sum_add_distrib]; rw [smeval_sub]; rw [smeval_X]; rw [smeval_natCast]; rw [pow_zero]; rw [pow_one]; rw [ih]; rw [mul_sum]
    refine sum_congr rfl ?_
    intro ij hij -- try to move `descPochhammer`s to right, gather multipliers.
    have hdx : (descPochhammer Int ij.1).smeval r * (X - (ij.2 : Int[X])).smeval s =
        (X - (ij.2 : Int[X])).smeval s * (descPochhammer Int ij.1).smeval r := by
      refine (commute_iff_eq ((descPochhammer Int ij.1).smeval r)
        ((X - (ij.2 : Int[X])).smeval s)).mp ?_
      exact smeval_commute Int (descPochhammer Int ij.1) (X - (ij.2 : Int[X])) h
    rw [descPochhammer_succ_right]; rw [mul_comm]; rw [smeval_mul]; rw [descPochhammer_succ_right]; rw [mul_comm]; rw [smeval_mul]; rw [← mul_assoc ((descPochhammer Int ij.1).smeval r)]; rw [hdx]
    simp only [mul_assoc _ ((descPochhammer Int ij.1).smeval r) _,
      ← mul_assoc _ _ (((descPochhammer Int ij.1).smeval r) * _)]
    have hl : (r + s - k • 1) * (k.choose ij.1) = (k.choose ij.1) * (X - (ij.2 : Int[X])).smeval s +
        ↑(k.choose ij.2) * (X - (ij.1 : Int[X])).smeval r := by
      simp only [smeval_sub, smeval_X, pow_one, smeval_natCast, pow_zero]
      rw [← Nat.choose_symm_of_eq_add (List.Nat.mem_antidiagonal.mp hij).symm]; rw [(List.Nat.mem_antidiagonal.mp hij).symm]; rw [← mul_add]; rw [Nat.cast_comm]; rw [add_smul]
      abel_nf
    rw [hl]; rw [← add_mul]

中文:
定理 descPochhammer_smeval_add
  条件: [环 R] {r s : R} (k : 自然数) (h : Commute r s)
  证明: by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [descPochhammer_succ_right]; rw [mul_comm]; rw [smeval_mul]; rw [sum_antidiagonal_choose_succ_mul
      fun i j => ((descPochhammer Int i).smeval r * (descPochhammer Int j).smeval s)]; rw [← sum_add_distrib]; rw [smeval_sub]; rw [smeval_X]; rw [smeval_natCast]; rw [pow_zero]; rw [pow_one]; rw [ih]; rw [mul_sum]
    refine sum_congr rfl ?_
    intro ij hij -- try to move `descPochhammer`s to right, gather multipliers.
    have hdx : (descPochhammer Int ij.1).smeval r * (X - (ij.2 : Int[X])).smeval s =
        (X - (ij.2 : Int[X])).smeval s * (descPochhammer Int ij.1).smeval r := by
      refine (commute_iff_eq ((descPochhammer Int ij.1).smeval r)
        ((X - (ij.2 : Int[X])).smeval s)).mp ?_
      exact smeval_commute Int (descPochhammer Int ij.1) (X - (ij.2 : Int[X])) h
    rw [descPochhammer_succ_right]; rw [mul_comm]; rw [smeval_mul]; rw [descPochhammer_succ_right]; rw [mul_comm]; rw [smeval_mul]; rw [← mul_assoc ((descPochhammer Int ij.1).smeval r)]; rw [hdx]
    simp only [mul_assoc _ ((descPochhammer Int ij.1).smeval r) _,
      ← mul_assoc _ _ (((descPochhammer Int ij.1).smeval r) * _)]
    have hl : (r + s - k • 1) * (k.choose ij.1) = (k.choose ij.1) * (X - (ij.2 : Int[X])).smeval s +
        ↑(k.choose ij.2) * (X - (ij.1 : Int[X])).smeval r := by
      simp only [smeval_sub, smeval_X, pow_one, smeval_natCast, pow_zero]
      rw [← Nat.choose_symm_of_eq_add (List.Nat.mem_antidiagonal.mp hij).symm]; rw [(List.Nat.mem_antidiagonal.mp hij).symm]; rw [← mul_add]; rw [Nat.cast_comm]; rw [add_smul]
      abel_nf
    rw [hl]; rw [← add_mul]

Depends on / 依赖: descPochhammer, descPochhammer_succ_right, gather, mul_comm, mul_sum, multipliers, pow_one, pow_zero, smeval, smeval_X, smeval_mul, smeval_natCast, smeval_sub, sum_add_distrib, sum_antidiagonal_choose_succ_mul, sum_congr
-/
theorem descPochhammer_smeval_add [Ring R] {r s : R} (k : Nat) (h : Commute r s) :
    (descPochhammer Int k).smeval (r + s) = ∑ ij in antidiagonal k,
    Nat.choose k ij.1 * ((descPochhammer Int ij.1).smeval r * (descPochhammer Int ij.2).smeval s) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [descPochhammer_succ_right]; rw [mul_comm]; rw [smeval_mul]; rw [sum_antidiagonal_choose_succ_mul
      fun i j => ((descPochhammer Int i).smeval r * (descPochhammer Int j).smeval s)]; rw [← sum_add_distrib]; rw [smeval_sub]; rw [smeval_X]; rw [smeval_natCast]; rw [pow_zero]; rw [pow_one]; rw [ih]; rw [mul_sum]
    refine sum_congr rfl ?_
    intro ij hij -- try to move `descPochhammer`s to right, gather multipliers.
    have hdx : (descPochhammer Int ij.1).smeval r * (X - (ij.2 : Int[X])).smeval s =
        (X - (ij.2 : Int[X])).smeval s * (descPochhammer Int ij.1).smeval r := by
      refine (commute_iff_eq ((descPochhammer Int ij.1).smeval r)
        ((X - (ij.2 : Int[X])).smeval s)).mp ?_
      exact smeval_commute Int (descPochhammer Int ij.1) (X - (ij.2 : Int[X])) h
    rw [descPochhammer_succ_right]; rw [mul_comm]; rw [smeval_mul]; rw [descPochhammer_succ_right]; rw [mul_comm]; rw [smeval_mul]; rw [← mul_assoc ((descPochhammer Int ij.1).smeval r)]; rw [hdx]
    simp only [mul_assoc _ ((descPochhammer Int ij.1).smeval r) _,
      ← mul_assoc _ _ (((descPochhammer Int ij.1).smeval r) * _)]
    have hl : (r + s - k • 1) * (k.choose ij.1) = (k.choose ij.1) * (X - (ij.2 : Int[X])).smeval s +
        ↑(k.choose ij.2) * (X - (ij.1 : Int[X])).smeval r := by
      simp only [smeval_sub, smeval_X, pow_one, smeval_natCast, pow_zero]
      rw [← Nat.choose_symm_of_eq_add (List.Nat.mem_antidiagonal.mp hij).symm]; rw [(List.Nat.mem_antidiagonal.mp hij).symm]; rw [← mul_add]; rw [Nat.cast_comm]; rw [add_smul]
      abel_nf
    rw [hl]; rw [← add_mul]

/--
theorem `add_choose_eq` / 定理 `add_choose_eq`

English:
theorem add_choose_eq
  given: [Ring R] [BinomialRing R] {r s : R} (k : Nat) (h : Commute r s)
  proof: by
  rw [← nsmul_right_inj (Nat.factorial_ne_zero k)]; rw [← descPochhammer_eq_factorial_smul_choose]; rw [smul_sum]; rw [descPochhammer_smeval_add _ h]
  refine sum_congr rfl ?_
  intro x hx
  rw [← Nat.choose_mul_factorial_mul_factorial (HasAntidiagonal.antidiagonal.fst_le hx)]; rw [tsub_eq_of_eq_add_rev (List.Nat.mem_antidiagonal.mp hx).symm]; rw [mul_assoc]; rw [nsmul_eq_mul]; rw [Nat.cast_mul]; rw [Nat.cast_mul]; rw [← mul_assoc _ (x.1.factorial : R)]; rw [mul_assoc _ (x.2.factorial : R)]; rw [← mul_assoc (x.2.factorial : R)]; rw [Nat.cast_commute x.2.factorial]; rw [mul_assoc _ (x.2.factorial : R)]; rw [← nsmul_eq_mul x.2.factorial]
  simp [mul_assoc, descPochhammer_eq_factorial_smul_choose]

中文:
定理 add_choose_eq
  条件: [环 R] [二项环 R] {r s : R} (k : 自然数) (h : Commute r s)
  证明: by
  rw [← nsmul_right_inj (Nat.factorial_ne_zero k)]; rw [← descPochhammer_eq_factorial_smul_choose]; rw [smul_sum]; rw [descPochhammer_smeval_add _ h]
  refine sum_congr rfl ?_
  intro x hx
  rw [← Nat.choose_mul_factorial_mul_factorial (HasAntidiagonal.antidiagonal.fst_le hx)]; rw [tsub_eq_of_eq_add_rev (List.Nat.mem_antidiagonal.mp hx).symm]; rw [mul_assoc]; rw [nsmul_eq_mul]; rw [Nat.cast_mul]; rw [Nat.cast_mul]; rw [← mul_assoc _ (x.1.factorial : R)]; rw [mul_assoc _ (x.2.factorial : R)]; rw [← mul_assoc (x.2.factorial : R)]; rw [Nat.cast_commute x.2.factorial]; rw [mul_assoc _ (x.2.factorial : R)]; rw [← nsmul_eq_mul x.2.factorial]
  simp [mul_assoc, descPochhammer_eq_factorial_smul_choose]

Depends on / 依赖: HasAntidiagonal, HasAntidiagonal.antidiagonal.fst_le, List.Nat.mem_antidiagonal.mp, Nat.cast_mul, Nat.choose_mul_factorial_mul_factorial, Nat.factorial_ne_zero, antidiagonal, cast_mul, choose_mul_factorial_mul_factorial, descPochhammer_eq_factorial_smul_choose, descPochhammer_smeval_add, factorial, factorial_ne_zero, fst_le, mem_antidiagonal, mul_assoc, nsmul_eq_mul, nsmul_right_inj, smul_sum, sum_congr
-/
theorem add_choose_eq [Ring R] [BinomialRing R] {r s : R} (k : Nat) (h : Commute r s) :
    choose (r + s) k =
      ∑ ij in antidiagonal k, choose r ij.1 * choose s ij.2 := by
  rw [← nsmul_right_inj (Nat.factorial_ne_zero k)]; rw [← descPochhammer_eq_factorial_smul_choose]; rw [smul_sum]; rw [descPochhammer_smeval_add _ h]
  refine sum_congr rfl ?_
  intro x hx
  rw [← Nat.choose_mul_factorial_mul_factorial (HasAntidiagonal.antidiagonal.fst_le hx)]; rw [tsub_eq_of_eq_add_rev (List.Nat.mem_antidiagonal.mp hx).symm]; rw [mul_assoc]; rw [nsmul_eq_mul]; rw [Nat.cast_mul]; rw [Nat.cast_mul]; rw [← mul_assoc _ (x.1.factorial : R)]; rw [mul_assoc _ (x.2.factorial : R)]; rw [← mul_assoc (x.2.factorial : R)]; rw [Nat.cast_commute x.2.factorial]; rw [mul_assoc _ (x.2.factorial : R)]; rw [← nsmul_eq_mul x.2.factorial]
  simp [mul_assoc, descPochhammer_eq_factorial_smul_choose]

/--
lemma `map_choose` / 引理 `map_choose`

English:
lemma map_choose
  statement: {R S F : Type*} [Ring R] [Ring S] [BinomialRing R] [BinomialRing S]
  proof: by
  simpa using! Ring.map_multichoose f (a - n + 1) n

中文:
引理 map_choose
  结论: {R S F : 类型} [环 R] [环 S] [二项环 R] [二项环 S]
  证明: by
  simpa using! Ring.map_multichoose f (a - n + 1) n

Depends on / 依赖: Ring.map_multichoose, map_multichoose
-/
lemma map_choose {R S F : Type*} [Ring R] [Ring S] [BinomialRing R] [BinomialRing S]
    [FunLike F R S] [RingHomClass F R S] (f : F) (a : R) (n : Nat) :
    f (Ring.choose a n) = Ring.choose (f a) n := by
  simpa using! Ring.map_multichoose f (a - n + 1) n

end Ring

end Choose
