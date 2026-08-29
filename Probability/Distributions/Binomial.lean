/-
Copyright (c) 2025 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Etienne Marion
-/
module

public import Mathlib.Probability.CondVar
public import Mathlib.Probability.Distributions.Bernoulli
public import Mathlib.Probability.Distributions.SetBernoulli

import Mathlib.MeasureTheory.MeasurableSpace.NCard
import Mathlib.Order.Interval.Set.Nat
import Mathlib.Probability.Notation

/-!
# Binomial random variables

This file defines the binomial distribution and binomial random variables,
and computes their expectation and variance. For `n : ℕ` and `p : I`,
the binomial distribution `Bin(n, p)` is defined as the cardinal of a random subset `U`
of `Set.Iic n` such that each `k ∈ Set.Iic n` belongs to `U` independently with probability `p`.

## Main definition

* `ProbabilityTheory.binomial`:
  Binomial distribution on an arbitrary semiring with parameters `n` and `p`.

## Implementation details

We provide the definition `binomial` with notation `Bin(n, P)` as the corresponding measure
over `ℕ`. We also introduce a notation `Bin(R, n p)` for the same measure but over a general
`AddMonoidWithOne R`, that stands for `Bin(n, p).map (Nat.cast : ℕ → R)`. This is in particular
useful if one is interested in the binomial distribution as a measure over `ℝ` or `ℤ`.
Results should be proven for both `Bin(n, p)` and `Bin(R, n, p)` when possible, using the first
one to prove the second. Note that results concerning `Bin(R, n, p)` may require
`[MeasurableSingletonClass R]` and/or `[CharZero R]`.

When referring to `Bin(n, p)` in names, use `binomial`. When referring to `Bin(R, n, p)`,
use `map_cast_binomial`.

## Notation

`Bin(n, p)` is the binomial distribution with parameters `n` and `p` in `ℕ`.
`Bin(R, n, p)` is the binomial distribution with parameters `n` and `p` in `R`.
-/

public section

open MeasureTheory Set Measure
open scoped NNReal ProbabilityTheory unitInterval ENNReal

namespace ProbabilityTheory
variable {R Ω : Type*} [MeasurableSpace R] [AddMonoidWithOne R] {m : MeasurableSpace Ω}
  {P : Measure Ω} {X : Ω -> R} {n : Nat} {p : I}

/-- The binomial probability distribution with parameter `p`. -/
@[expose]
/--
Definition of `binomial` / `binomial` 的定义

English:
definition binomial
  signature: (n : Nat) (p : I)
  body: setBer(Iio n, p).map ncard

中文:
定义 binomial
  签名: (n : 自然数) (p : I)
  定义体: setBer(Iio n, p).map ncard

Depends on / 依赖: setBer
-/
noncomputable def binomial (n : Nat) (p : I) : Measure Nat := setBer(Iio n, p).map ncard

/-- The binomial probability distribution with parameter `p`. -/
scoped notation3 "Bin(" n ", " p ")" => binomial n p

/-- The binomial probability distribution with parameter `p` valued in the semiring `R`. -/
scoped notation3 "Bin(" R ", " n ", " p ")" => (binomial n p).map (Nat.cast : Nat -> R)

@[simp]
/--
lemma `binomial_nat` / 引理 `binomial_nat`

English:
lemma binomial_nat
  statement: Bin(Nat, n, p) = Bin(n, p)
  proof: map_id

中文:
引理 binomial_nat
  结论: Bin(自然数, n, p) = Bin(n, p)
  证明: map_id

Depends on / 依赖: map_id
-/
lemma binomial_nat : Bin(Nat, n, p) = Bin(n, p) := map_id

/--
lemma `binomial_zero` / 引理 `binomial_zero`

English:
lemma binomial_zero
  statement: Bin(0, p) = dirac 0
  proof: by simp [binomial]

@[simp]

中文:
引理 binomial_zero
  结论: Bin(0, p) = dirac 0
  证明: by simp [binomial]

@[simp]

Depends on / 依赖: binomial
-/
lemma binomial_zero : Bin(0, p) = dirac 0 := by simp [binomial]

@[simp]
/--
lemma `map_cast_binomial_zero` / 引理 `map_cast_binomial_zero`

English:
lemma map_cast_binomial_zero
  statement: Bin(R, 0, p) = dirac 0
  proof: by
  simp [binomial, map_dirac' .of_discrete]

中文:
引理 map_cast_binomial_zero
  结论: Bin(R, 0, p) = dirac 0
  证明: by
  simp [binomial, map_dirac' .of_discrete]

Depends on / 依赖: binomial, map_dirac, of_discrete
-/
lemma map_cast_binomial_zero : Bin(R, 0, p) = dirac 0 := by
  simp [binomial, map_dirac' .of_discrete]

/--
Instance `isProbabilityMeasure_binomial` / 实例 `isProbabilityMeasure_binomial`

English:
instance isProbabilityMeasure_binomial
  signature: : IsProbabilityMeasure Bin(n, p)
  body: isProbabilityMeasure_map by fun_prop

中文:
实例 isProbabilityMeasure_binomial
  签名: : IsProbabilityMeasure Bin(n, p)
  定义体: isProbabilityMeasure_map by fun_prop

Depends on / 依赖: fun_prop, isProbabilityMeasure_map
-/
instance isProbabilityMeasure_binomial : IsProbabilityMeasure Bin(n, p) :=
isProbabilityMeasure_map by fun_prop

/--
Instance `isProbabilityMeasure_map_cast_binomial` / 实例 `isProbabilityMeasure_map_cast_binomial`

English:
instance isProbabilityMeasure_map_cast_binomial
  signature: : IsProbabilityMeasure Bin(R, n, p)
  body: isProbabilityMeasure_map .of_discrete

中文:
实例 isProbabilityMeasure_map_cast_binomial
  签名: : IsProbabilityMeasure Bin(R, n, p)
  定义体: isProbabilityMeasure_map .of_discrete

Depends on / 依赖: isProbabilityMeasure_map, of_discrete
-/
instance isProbabilityMeasure_map_cast_binomial : IsProbabilityMeasure Bin(R, n, p) :=
  isProbabilityMeasure_map .of_discrete

/--
lemma `ae_le_of_hasLaw_binomial` / 引理 `ae_le_of_hasLaw_binomial`

English:
lemma ae_le_of_hasLaw_binomial
  given: {X : Ω -> Nat} (hX : HasLaw X Bin(n, p) P)
  statement: forallᵐ ω ∂P, X ω <= n
  proof: by
  rw [hX.ae_iff (p := (· <= n)) <| by fun_prop]; rw [binomial]; rw [ae_map_iff (by fun_prop) (finite_Iic _).measurableSet]
  filter_upwards [setBernoulli_ae_subset] with s hs
  simpa using ncard_le_ncard hs

中文:
引理 ae_le_of_hasLaw_binomial
  条件: {X : Ω -> 自然数} (hX : HasLaw X Bin(n, p) P)
  结论: 对任意ᵐ ω ∂P, X ω <= n
  证明: by
  rw [hX.ae_iff (p := (· <= n)) <| by fun_prop]; rw [binomial]; rw [ae_map_iff (by fun_prop) (finite_Iic _).measurableSet]
  filter_upwards [setBernoulli_ae_subset] with s hs
  simpa using ncard_le_ncard hs

Depends on / 依赖: ae_iff, ae_map_iff, binomial, filter_upwards, finite_Iic, fun_prop, hX.ae_iff, measurableSet, ncard_le_ncard, setBernoulli_ae_subset
-/
lemma ae_le_of_hasLaw_binomial {X : Ω -> Nat} (hX : HasLaw X Bin(n, p) P) : forallᵐ ω ∂P, X ω <= n := by
  rw [hX.ae_iff (p := (· <= n)) <| by fun_prop]; rw [binomial]; rw [ae_map_iff (by fun_prop) (finite_Iic _).measurableSet]
  filter_upwards [setBernoulli_ae_subset] with s hs
  simpa using ncard_le_ncard hs

/--
lemma `binomial_real_singleton` / 引理 `binomial_real_singleton`

English:
lemma binomial_real_singleton
  given: (n k : Nat) (p : I)
  proof: by
  rw [binomial]; rw [map_ncard_setBernoulli_real_singleton (finite_Iio n)]; rw [ncard_Iio_nat]

中文:
引理 binomial_real_singleton
  条件: (n k : 自然数) (p : I)
  证明: by
  rw [binomial]; rw [map_ncard_setBernoulli_real_singleton (finite_Iio n)]; rw [ncard_Iio_nat]

Depends on / 依赖: binomial, finite_Iio, map_ncard_setBernoulli_real_singleton, ncard_Iio_nat
-/
lemma binomial_real_singleton (n k : Nat) (p : I) :
    Bin(n, p).real {k} = (n.choose k) * p ^ k * (1 - p) ^ (n - k) := by
  rw [binomial]; rw [map_ncard_setBernoulli_real_singleton (finite_Iio n)]; rw [ncard_Iio_nat]

/--
lemma `binomial_singleton` / 引理 `binomial_singleton`

English:
lemma binomial_singleton
  given: (n k : Nat) (p : I)
  proof: by
  rw [← ENNReal.ofReal_toReal (a := Bin(n]; rw [p) _) (by simp)]; rw [← measureReal_def]; rw [binomial_real_singleton]

中文:
引理 binomial_singleton
  条件: (n k : 自然数) (p : I)
  证明: by
  rw [← ENNReal.ofReal_toReal (a := Bin(n]; rw [p) _) (by simp)]; rw [← measureReal_def]; rw [binomial_real_singleton]

Depends on / 依赖: ENNReal, ENNReal.ofReal_toReal, binomial_real_singleton, measureReal_def, ofReal_toReal
-/
lemma binomial_singleton (n k : Nat) (p : I) :
    Bin(n, p) {k} = ENNReal.ofReal ((n.choose k) * p ^ k * (1 - p) ^ (n - k)) := by
  rw [← ENNReal.ofReal_toReal (a := Bin(n]; rw [p) _) (by simp)]; rw [← measureReal_def]; rw [binomial_real_singleton]

/--
lemma `map_cast_binomial_real_singleton` / 引理 `map_cast_binomial_real_singleton`

English:
lemma map_cast_binomial_real_singleton
  given: [MeasurableSingletonClass R] [CharZero R] (n k : Nat) (p : I)
  proof: by
  rw [map_measureReal_apply (by fun_prop) (by measurability)]
  convert binomial_real_singleton n k p
  ext; simp

@[simp]

中文:
引理 map_cast_binomial_real_singleton
  条件: [MeasurableSingletonClass R] [CharZero R] (n k : 自然数) (p : I)
  证明: by
  rw [map_measureReal_apply (by fun_prop) (by measurability)]
  convert binomial_real_singleton n k p
  ext; simp

@[simp]

Depends on / 依赖: binomial_real_singleton, convert, fun_prop, map_measureReal_apply, measurability
-/
lemma map_cast_binomial_real_singleton [MeasurableSingletonClass R] [CharZero R] (n k : Nat) (p : I) :
    Bin(R, n, p).real {(k : R)} = (n.choose k) * p ^ k * (1 - p) ^ (n - k) := by
  rw [map_measureReal_apply (by fun_prop) (by measurability)]
  convert binomial_real_singleton n k p
  ext; simp

@[simp]
/--
lemma `binomial_nonneg` / 引理 `binomial_nonneg`

English:
lemma binomial_nonneg
  given: {k : Nat}
  statement: (0 : Real) <= (n.choose k) * p ^ k * (1 - p) ^ (n - k)
  proof: mul_nonneg (mul_nonneg (by positivity) (pow_nonneg (by grind) _)) (pow_nonneg (by grind) _)

中文:
引理 binomial_nonneg
  条件: {k : 自然数}
  结论: (0 : 实数) <= (n.choose k) * p ^ k * (1 - p) ^ (n - k)
  证明: mul_nonneg (mul_nonneg (by positivity) (pow_nonneg (by grind) _)) (pow_nonneg (by grind) _)

Depends on / 依赖: mul_nonneg, pow_nonneg
-/
lemma binomial_nonneg {k : Nat} : (0 : Real) <= (n.choose k) * p ^ k * (1 - p) ^ (n - k) :=
    mul_nonneg (mul_nonneg (by positivity) (pow_nonneg (by grind) _)) (pow_nonneg (by grind) _)

/--
lemma `map_cast_binomial_singleton` / 引理 `map_cast_binomial_singleton`

English:
lemma map_cast_binomial_singleton
  given: [MeasurableSingletonClass R] [CharZero R] (n k : Nat) (p : I)
  proof: by
  rw [← ENNReal.ofReal_toReal (a := Bin(R]; rw [n]; rw [p) _) (by simp)]; rw [← measureReal_def]; rw [map_cast_binomial_real_singleton]

@[simp]

中文:
引理 map_cast_binomial_singleton
  条件: [MeasurableSingletonClass R] [CharZero R] (n k : 自然数) (p : I)
  证明: by
  rw [← ENNReal.ofReal_toReal (a := Bin(R]; rw [n]; rw [p) _) (by simp)]; rw [← measureReal_def]; rw [map_cast_binomial_real_singleton]

@[simp]

Depends on / 依赖: ENNReal, ENNReal.ofReal_toReal, map_cast_binomial_real_singleton, measureReal_def, ofReal_toReal
-/
lemma map_cast_binomial_singleton [MeasurableSingletonClass R] [CharZero R] (n k : Nat) (p : I) :
    Bin(R, n, p) {(k : R)} = ENNReal.ofReal ((n.choose k) * p ^ k * (1 - p) ^ (n - k)) := by
  rw [← ENNReal.ofReal_toReal (a := Bin(R]; rw [n]; rw [p) _) (by simp)]; rw [← measureReal_def]; rw [map_cast_binomial_real_singleton]

@[simp]
/--
lemma `binomial_real_zero` / 引理 `binomial_real_zero`

English:
lemma binomial_real_zero
  given: (n : Nat) (p : I)
  proof: by simp [binomial_real_singleton]

@[simp]

中文:
引理 binomial_real_zero
  条件: (n : 自然数) (p : I)
  证明: by simp [binomial_real_singleton]

@[simp]

Depends on / 依赖: binomial_real_singleton
-/
lemma binomial_real_zero (n : Nat) (p : I) :
    Bin(n, p).real {0} = (1 - p) ^ n := by simp [binomial_real_singleton]

@[simp]
/--
lemma `map_cast_binomial_real_zero` / 引理 `map_cast_binomial_real_zero`

English:
lemma map_cast_binomial_real_zero
  given: [MeasurableSingletonClass R] [CharZero R] (n : Nat) (p : I)
  proof: by
  rw [← Nat.cast_zero]; rw [map_cast_binomial_real_singleton]
  simp

@[simp]

中文:
引理 map_cast_binomial_real_zero
  条件: [MeasurableSingletonClass R] [CharZero R] (n : 自然数) (p : I)
  证明: by
  rw [← Nat.cast_zero]; rw [map_cast_binomial_real_singleton]
  simp

@[simp]

Depends on / 依赖: Nat.cast_zero, cast_zero, map_cast_binomial_real_singleton
-/
lemma map_cast_binomial_real_zero [MeasurableSingletonClass R] [CharZero R] (n : Nat) (p : I) :
    Bin(R, n, p).real {0} = (1 - p) ^ n := by
  rw [← Nat.cast_zero]; rw [map_cast_binomial_real_singleton]
  simp

@[simp]
/--
lemma `binomial_real_self` / 引理 `binomial_real_self`

English:
lemma binomial_real_self
  given: (n : Nat) (p : I)
  proof: by simp [binomial_real_singleton]

@[simp]

中文:
引理 binomial_real_self
  条件: (n : 自然数) (p : I)
  证明: by simp [binomial_real_singleton]

@[simp]

Depends on / 依赖: binomial_real_singleton
-/
lemma binomial_real_self (n : Nat) (p : I) :
    Bin(n, p).real {n} = p ^ n := by simp [binomial_real_singleton]

@[simp]
/--
lemma `map_cast_binomial_real_self` / 引理 `map_cast_binomial_real_self`

English:
lemma map_cast_binomial_real_self
  given: [MeasurableSingletonClass R] [CharZero R] (n : Nat) (p : I)
  proof: by simp [map_cast_binomial_real_singleton]

中文:
引理 map_cast_binomial_real_self
  条件: [MeasurableSingletonClass R] [CharZero R] (n : 自然数) (p : I)
  证明: by simp [map_cast_binomial_real_singleton]

Depends on / 依赖: map_cast_binomial_real_singleton
-/
lemma map_cast_binomial_real_self [MeasurableSingletonClass R] [CharZero R] (n : Nat) (p : I) :
    Bin(R, n, p).real {(n : R)} = p ^ n := by simp [map_cast_binomial_real_singleton]

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
lemma `binomial_one_eq_bernoulliMeasure` / 引理 `binomial_one_eq_bernoulliMeasure`

English:
lemma binomial_one_eq_bernoulliMeasure
  given: (p : I)
  proof: by
  refine ext_of_measureReal_singleton fun k => ?_
  match k with
  | 0 | 1 => simp
  | k + 2 => simp [binomial_real_singleton]

中文:
引理 binomial_one_eq_bernoulliMeasure
  条件: (p : I)
  证明: by
  refine ext_of_measureReal_singleton fun k => ?_
  match k with
  | 0 | 1 => simp
  | k + 2 => simp [binomial_real_singleton]

Depends on / 依赖: binomial_real_singleton, ext_of_measureReal_singleton
-/
lemma binomial_one_eq_bernoulliMeasure (p : I) :
    Bin(1, p) = Ber(1, 0, p) := by
  refine ext_of_measureReal_singleton fun k => ?_
  match k with
  | 0 | 1 => simp
  | k + 2 => simp [binomial_real_singleton]

/--
lemma `binomial_eq_sum_dirac` / 引理 `binomial_eq_sum_dirac`

English:
lemma binomial_eq_sum_dirac
  given: (n : Nat) (p : I)
  proof: by
  refine ext_of_singleton fun k => ?_
  rw [binomial_singleton]; rw [finsetSum_apply]; rw [Finset.sum_eq_single k]
  · simp
  · simp_all
  · simp_all [Nat.choose_eq_zero_of_lt]

中文:
引理 binomial_eq_sum_dirac
  条件: (n : 自然数) (p : I)
  证明: by
  refine ext_of_singleton fun k => ?_
  rw [binomial_singleton]; rw [finsetSum_apply]; rw [Finset.sum_eq_single k]
  · simp
  · simp_all
  · simp_all [Nat.choose_eq_zero_of_lt]

Depends on / 依赖: Finset, Finset.sum_eq_single, Nat.choose_eq_zero_of_lt, binomial_singleton, choose_eq_zero_of_lt, ext_of_singleton, finsetSum_apply, sum_eq_single
-/
lemma binomial_eq_sum_dirac (n : Nat) (p : I) :
    Bin(n, p) =
      ∑ k in Finset.Iic n, ENNReal.ofReal ((n.choose k) * p ^ k * (1 - p) ^ (n - k)) • dirac k := by
  refine ext_of_singleton fun k => ?_
  rw [binomial_singleton]; rw [finsetSum_apply]; rw [Finset.sum_eq_single k]
  · simp
  · simp_all
  · simp_all [Nat.choose_eq_zero_of_lt]

/--
lemma `map_cast_binomial_eq_sum_dirac` / 引理 `map_cast_binomial_eq_sum_dirac`

English:
lemma map_cast_binomial_eq_sum_dirac
  given: [MeasurableSingletonClass R] (n : Nat) (p : I)
  proof: by
  rw [binomial_eq_sum_dirac]; rw [Measure.map_finset_sum .of_discrete]
  exact Finset.sum_congr rfl fun _ _ => by rw [Measure.map_smul, map_dirac]

中文:
引理 map_cast_binomial_eq_sum_dirac
  条件: [MeasurableSingletonClass R] (n : 自然数) (p : I)
  证明: by
  rw [binomial_eq_sum_dirac]; rw [Measure.map_finset_sum .of_discrete]
  exact Finset.sum_congr rfl fun _ _ => by rw [Measure.map_smul, map_dirac]

Depends on / 依赖: Finset, Finset.sum_congr, Measure, Measure.map_finset_sum, Measure.map_smul, binomial_eq_sum_dirac, map_dirac, map_finset_sum, map_smul, of_discrete, sum_congr
-/
lemma map_cast_binomial_eq_sum_dirac [MeasurableSingletonClass R] (n : Nat) (p : I) :
    Bin(R, n, p) =
      ∑ k in Finset.Iic n, ENNReal.ofReal ((n.choose k) * p ^ k * (1 - p) ^ (n - k)) •
        dirac (k : R) := by
  rw [binomial_eq_sum_dirac]; rw [Measure.map_finset_sum .of_discrete]
  exact Finset.sum_congr rfl fun _ _ => by rw [Measure.map_smul, map_dirac]

section Integral

variable {E : Type*} [NormedAddCommGroup E]

/--
lemma `integrable_map_cast_binomial` / 引理 `integrable_map_cast_binomial`

English:
lemma integrable_map_cast_binomial
  given: [MeasurableSingletonClass R] (f : R -> E)
  proof: by
  simp [map_cast_binomial_eq_sum_dirac, integrable_finsetSum_measure, integrable_dirac,
    Integrable.smul_measure]

中文:
引理 integrable_map_cast_binomial
  条件: [MeasurableSingletonClass R] (f : R -> E)
  证明: by
  simp [map_cast_binomial_eq_sum_dirac, integrable_finsetSum_measure, integrable_dirac,
    Integrable.smul_measure]

Depends on / 依赖: Integrable, Integrable.smul_measure, integrable_dirac, integrable_finsetSum_measure, map_cast_binomial_eq_sum_dirac, smul_measure
-/
lemma integrable_map_cast_binomial [MeasurableSingletonClass R] (f : R -> E) :
    Integrable f Bin(R, n, p) := by
  simp [map_cast_binomial_eq_sum_dirac, integrable_finsetSum_measure, integrable_dirac,
    Integrable.smul_measure]

/--
lemma `integrable_binomial` / 引理 `integrable_binomial`

English:
lemma integrable_binomial
  given: (f : Nat -> E)
  proof: (integrable_map_cast_binomial f).comp_measurable .of_discrete

中文:
引理 integrable_binomial
  条件: (f : 自然数 -> E)
  证明: (integrable_map_cast_binomial f).comp_measurable .of_discrete

Depends on / 依赖: comp_measurable, integrable_map_cast_binomial, of_discrete
-/
lemma integrable_binomial (f : Nat -> E) :
    Integrable f Bin(n, p) := (integrable_map_cast_binomial f).comp_measurable .of_discrete

variable [NormedSpace Real E] [CompleteSpace E]

/--
lemma `integral_binomial` / 引理 `integral_binomial`

English:
lemma integral_binomial
  given: (f : Nat -> E)
  proof: by
  rw [binomial_eq_sum_dirac]; rw [integral_finsetSum_measure]
  · simp
  exact fun _ _ => (integrable_dirac (by simp)).smul_measure (by simp)

中文:
引理 integral_binomial
  条件: (f : 自然数 -> E)
  证明: by
  rw [binomial_eq_sum_dirac]; rw [integral_finsetSum_measure]
  · simp
  exact fun _ _ => (integrable_dirac (by simp)).smul_measure (by simp)

Depends on / 依赖: binomial_eq_sum_dirac, integrable_dirac, integral_finsetSum_measure, smul_measure
-/
lemma integral_binomial (f : Nat -> E) :
    ∫ x, f x ∂Bin(n, p) =
      ∑ k in Finset.Iic n, (n.choose k * (p : Real) ^ k * (1 - p) ^ (n - k)) • f k := by
  rw [binomial_eq_sum_dirac]; rw [integral_finsetSum_measure]
  · simp
  exact fun _ _ => (integrable_dirac (by simp)).smul_measure (by simp)

/--
lemma `integral_map_cast_binomial` / 引理 `integral_map_cast_binomial`

English:
lemma integral_map_cast_binomial
  given: [MeasurableSingletonClass R] (f : R -> E)
  proof: by
  rw [integral_map .of_discrete (integrable_map_cast_binomial f).aestronglyMeasurable]; rw [integral_binomial]

中文:
引理 integral_map_cast_binomial
  条件: [MeasurableSingletonClass R] (f : R -> E)
  证明: by
  rw [integral_map .of_discrete (integrable_map_cast_binomial f).aestronglyMeasurable]; rw [integral_binomial]

Depends on / 依赖: aestronglyMeasurable, integrable_map_cast_binomial, integral_binomial, integral_map, of_discrete
-/
lemma integral_map_cast_binomial [MeasurableSingletonClass R] (f : R -> E) :
    ∫ x, f x ∂Bin(R, n, p) =
      ∑ k in Finset.Iic n, (n.choose k * (p : Real) ^ k * (1 - p) ^ (n - k)) • f k := by
  rw [integral_map .of_discrete (integrable_map_cast_binomial f).aestronglyMeasurable]; rw [integral_binomial]

end Integral

/-! ### Binomial random variables -/

variable {X : Ω -> Real}

/-- **Expectation of a binomial random variable**.

The expectation of a binomial random variable with parameters `n` and `p` is `pn`. -/
proof_wanted integral_of_hasLaw_binomial (hX : HasLaw X Bin(Real, n, p) P) : P[X] = p.val * n

/-- **Variance of a binomial random variable**.

The variance of a binomial random variable with parameters `n` and `p` is `p(1 - p)n`. -/
proof_wanted variance_of_hasLaw_binomial (hX : HasLaw X Bin(Real, n, p) P) :
    Var[X; P] = p * (1 - p) * n

/-- **Conditional variance of a binomial random variable**.

The conditional variance of a binomial random variable is the product of the conditional
probabilities that it's equal to `0` and that it's equal to `1`. -/
proof_wanted condVar_of_hasLaw_binomial {m₀ : MeasurableSpace Ω} (hm : m <= m₀) {P : Measure[m₀] Ω}
    (hX : HasLaw X Bin(Real, n, p) P) :
    Var[X; P | m] =ᵐ[P] P[X | m] * P[1 - X | m]

end ProbabilityTheory
