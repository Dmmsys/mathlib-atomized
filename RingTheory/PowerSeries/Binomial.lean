/-
Copyright (c) 2024 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Carnahan
-/
module

public import Mathlib.RingTheory.Binomial
public import Mathlib.RingTheory.PowerSeries.WellKnown
public import Mathlib.Tactic.SuppressCompilation

/-!
# Binomial Power Series

We introduce formal power series of the form `(1 + X) ^ r`, where `r` is an element of a
commutative binomial ring `R`.

## Main Definitions
* `PowerSeries.binomialSeries`: A power series expansion of `(1 + X) ^ r`, where `r` is an element
  of a commutative binomial ring `R`.

## Main Results
* `PowerSeries.binomial_add`: Adding exponents yields multiplication of series.
* `PowerSeries.binomialSeries_nat`: when `r` is a natural number, we get `(1 + X) ^ r`.
* `PowerSeries.rescale_neg_one_invOneSubPow`: The image of `(1 - X) ^ (-d)` under the map
  `X ↦ (-X)` is `(1 + X) ^ (-d)`

## TODO
* When `A` is a commutative `R`-algebra, the exponentiation action makes the multiplicative group
  `1 + XA[[X]]` into an `R`-module.

-/

@[expose] public section

open Finset

suppress_compilation

variable {R A : Type*}

namespace PowerSeries

variable [CommRing R] [BinomialRing R]

/--
Definition of `binomialSeries` / `binomialSeries` 的定义

English:
definition binomialSeries
  signature: (A) [One A] [SMul R A] (r : R)
  body: mk fun n => Ring.choose r n • 1

@[simp]

中文:
定义 binomialSeries
  签名: (A) [幺 A] [标量乘法 R A] (r : R)
  定义体: mk fun n => Ring.choose r n • 1

@[simp]

Depends on / 依赖: Ring.choose
-/
def binomialSeries (A) [One A] [SMul R A] (r : R) : PowerSeries A :=
  mk fun n => Ring.choose r n • 1

@[simp]
/--
lemma `binomialSeries_coeff` / 引理 `binomialSeries_coeff`

English:
lemma binomialSeries_coeff
  given: [Semiring A] [SMul R A] (r : R) (n : Nat)
  proof: coeff_mk n fun n => Ring.choose r n • 1

@[simp]

中文:
引理 binomialSeries_coeff
  条件: [半环 A] [标量乘法 R A] (r : R) (n : 自然数)
  证明: coeff_mk n fun n => Ring.choose r n • 1

@[simp]

Depends on / 依赖: Ring.choose, coeff_mk
-/
lemma binomialSeries_coeff [Semiring A] [SMul R A] (r : R) (n : Nat) :
    coeff n (binomialSeries A r) = Ring.choose r n • 1 :=
  coeff_mk n fun n => Ring.choose r n • 1

@[simp]
/--
lemma `binomialSeries_constantCoeff` / 引理 `binomialSeries_constantCoeff`

English:
lemma binomialSeries_constantCoeff
  given: [Ring A] [Algebra R A] (r : R)
  proof: by
  simp [← coeff_zero_eq_constantCoeff_apply]

@[simp]

中文:
引理 binomialSeries_constantCoeff
  条件: [环 A] [代数 R A] (r : R)
  证明: by
  simp [← coeff_zero_eq_constantCoeff_apply]

@[simp]

Depends on / 依赖: coeff_zero_eq_constantCoeff_apply
-/
lemma binomialSeries_constantCoeff [Ring A] [Algebra R A] (r : R) :
    constantCoeff (binomialSeries A r) = 1 := by
  simp [← coeff_zero_eq_constantCoeff_apply]

@[simp]
/--
lemma `binomialSeries_add` / 引理 `binomialSeries_add`

English:
lemma binomialSeries_add
  given: [Ring A] [Algebra R A] (r s : R)
  proof: by
  ext n
  simp only [binomialSeries_coeff, Ring.add_choose_eq n (Commute.all r s), coeff_mul,
    Algebra.mul_smul_comm, mul_one, sum_smul]
  refine sum_congr rfl fun ab hab => ?_
  rw [mul_comm]; rw [mul_smul]

@[simp]

中文:
引理 binomialSeries_add
  条件: [环 A] [代数 R A] (r s : R)
  证明: by
  ext n
  simp only [binomialSeries_coeff, Ring.add_choose_eq n (Commute.all r s), coeff_mul,
    Algebra.mul_smul_comm, mul_one, sum_smul]
  refine sum_congr rfl fun ab hab => ?_
  rw [mul_comm]; rw [mul_smul]

@[simp]

Depends on / 依赖: Algebra, Algebra.mul_smul_comm, Commute, Commute.all, Ring.add_choose_eq, add_choose_eq, binomialSeries_coeff, coeff_mul, mul_comm, mul_one, mul_smul, mul_smul_comm, sum_congr, sum_smul
-/
lemma binomialSeries_add [Ring A] [Algebra R A] (r s : R) :
    binomialSeries A (r + s) = binomialSeries A r * binomialSeries A s := by
  ext n
  simp only [binomialSeries_coeff, Ring.add_choose_eq n (Commute.all r s), coeff_mul,
    Algebra.mul_smul_comm, mul_one, sum_smul]
  refine sum_congr rfl fun ab hab => ?_
  rw [mul_comm]; rw [mul_smul]

@[simp]
/--
lemma `binomialSeries_nat` / 引理 `binomialSeries_nat`

English:
lemma binomialSeries_nat
  given: [Ring A] [Algebra R A] (d : Nat)
  proof: by
  ext n
  have hright : (1 + X) ^ d = (((1 : Polynomial A) + (Polynomial.X)) ^ d).toPowerSeries := by
    simp
  rw [hright]; rw [Polynomial.coeff_coe]; rw [binomialSeries_coeff]; rw [Polynomial.coeff_one_add_X_pow]
  simp [Ring.choose_natCast, Nat.cast_smul_eq_nsmul]

@[simp]

中文:
引理 binomialSeries_nat
  条件: [环 A] [代数 R A] (d : 自然数)
  证明: by
  ext n
  have hright : (1 + X) ^ d = (((1 : Polynomial A) + (Polynomial.X)) ^ d).toPowerSeries := by
    simp
  rw [hright]; rw [Polynomial.coeff_coe]; rw [binomialSeries_coeff]; rw [Polynomial.coeff_one_add_X_pow]
  simp [Ring.choose_natCast, Nat.cast_smul_eq_nsmul]

@[simp]

Depends on / 依赖: Nat.cast_smul_eq_nsmul, Polynomial, Polynomial.X, Polynomial.coeff_coe, Polynomial.coeff_one_add_X_pow, Ring.choose_natCast, binomialSeries_coeff, cast_smul_eq_nsmul, choose_natCast, coeff_coe, coeff_one_add_X_pow, hright, toPowerSeries
-/
lemma binomialSeries_nat [Ring A] [Algebra R A] (d : Nat) :
    binomialSeries A (d : R) = (1 + X) ^ d := by
  ext n
  have hright : (1 + X) ^ d = (((1 : Polynomial A) + (Polynomial.X)) ^ d).toPowerSeries := by
    simp
  rw [hright]; rw [Polynomial.coeff_coe]; rw [binomialSeries_coeff]; rw [Polynomial.coeff_one_add_X_pow]
  simp [Ring.choose_natCast, Nat.cast_smul_eq_nsmul]

@[simp]
/--
lemma `binomialSeries_zero` / 引理 `binomialSeries_zero`

English:
lemma binomialSeries_zero
  given: [Ring A] [Algebra R A]
  proof: by
  simpa using binomialSeries_nat 0

中文:
引理 binomialSeries_zero
  条件: [环 A] [代数 R A]
  证明: by
  simpa using binomialSeries_nat 0

Depends on / 依赖: binomialSeries_nat
-/
lemma binomialSeries_zero [Ring A] [Algebra R A] :
    binomialSeries A (0 : R) = (1 : A⟦X⟧) := by
  simpa using binomialSeries_nat 0

/--
lemma `rescale_neg_one_invOneSubPow` / 引理 `rescale_neg_one_invOneSubPow`

English:
lemma rescale_neg_one_invOneSubPow
  given: [CommRing A] (d : Nat)
  proof: by
  ext n
  rw [coeff_rescale]; rw [binomialSeries_coeff]; rw [← Int.cast_negOnePow_natCast]; rw [← zsmul_eq_mul]
  cases d with
  | zero =>
    by_cases hn : n = 0 <;> simp [invOneSubPow, Ring.choose_zero_ite, hn]
  | succ d =>
    simp only [invOneSubPow, coeff_mk, Nat.cast_add, Nat.cast_one, neg

中文:
引理 rescale_neg_one_invOneSubPow
  条件: [交换环 A] (d : 自然数)
  证明: by
  ext n
  rw [coeff_rescale]; rw [binomialSeries_coeff]; rw [← Int.cast_negOnePow_natCast]; rw [← zsmul_eq_mul]
  cases d with
  | zero =>
    by_cases hn : n = 0 <;> simp [invOneSubPow, Ring.choose_zero_ite, hn]
  | succ d =>
    simp only [invOneSubPow, coeff_mk, Nat.cast_add, Nat.cast_one, neg

Depends on / 依赖: Int.cast_negOnePow_natCast, Int.reduceNeg, Nat.cast_add, Nat.cast_one, Nat.choose_symm_add, Ring.choose_neg, Ring.choose_zero_ite, Units.smul_def, binomialSeries_coeff, cast_add, cast_negOnePow_natCast, cast_one, choose_neg, choose_symm_add, choose_zero_ite, coeff_mk, coeff_rescale, invOneSubPow, mul_one, neg_add_rev
-/
lemma rescale_neg_one_invOneSubPow [CommRing A] (d : Nat) :
    rescale (-1 : A) (invOneSubPow A d) = binomialSeries A (-d : Int) := by
  ext n
  rw [coeff_rescale]; rw [binomialSeries_coeff]; rw [← Int.cast_negOnePow_natCast]; rw [← zsmul_eq_mul]
  cases d with
  | zero =>
    by_cases hn : n = 0 <;> simp [invOneSubPow, Ring.choose_zero_ite, hn]
  | succ d =>
    simp only [invOneSubPow, coeff_mk, Nat.cast_add, Nat.cast_one, neg_add_rev, Int.reduceNeg,
      zsmul_eq_mul, mul_one]
    rw [show (-1 : Int) + -d = -(d + 1) by abel]; rw [Ring.choose_neg]; rw [Nat.choose_symm_add]; rw [Units.smul_def]; rw [show (d : Int) + 1 + n - 1 = d + n by lia]; rw [← Nat.cast_add]; rw [Ring.choose_natCast]
    norm_cast

end PowerSeries
