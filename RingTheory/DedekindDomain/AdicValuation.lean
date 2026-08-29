/-
Copyright (c) 2022 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández
-/
module

public import Mathlib.Algebra.Order.Ring.IsNonarchimedean
public import Mathlib.Data.Int.WithZero
public import Mathlib.RingTheory.DedekindDomain.Dvr
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Valuation.ExtendToLocalization
public import Mathlib.Topology.Algebra.Valued.WithVal
public import Mathlib.RingTheory.Valuation.Discrete.Basic

/-!
# Adic valuations on Dedekind domains

Given a Dedekind domain `R` of Krull dimension 1 and a maximal ideal `v` of `R`, we define the
`v`-adic valuation on `R` and its extension to the field of fractions `K` of `R`.
We prove several properties of this valuation, including the existence of uniformizers.

We define the completion of `K` with respect to the `v`-adic valuation, denoted
`v.adicCompletion`, and its ring of integers, denoted `v.adicCompletionIntegers`.

## Main definitions
- `IsDedekindDomain.HeightOneSpectrum.intValuation v` is the `v`-adic valuation on `R`.
- `IsDedekindDomain.HeightOneSpectrum.valuation v` is the `v`-adic valuation on `K`.
- `IsDedekindDomain.HeightOneSpectrum.adicCompletion v` is the completion of `K` with respect
  to its `v`-adic valuation.
- `IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers v` is the ring of integers of
  `v.adicCompletion`.
- `IsDedekindDomain.HeightOneSpectrum.adicAbv v` is the `v`-adic absolute value on `K` defined as
  `b` raised to negative `v`-adic valuation, for some `b` in `ℝ≥0`.

## Main results
- `IsDedekindDomain.HeightOneSpectrum.intValuation_le_one` : The `v`-adic valuation on `R` is
  bounded above by 1.
- `IsDedekindDomain.HeightOneSpectrum.intValuation_lt_one_iff_dvd` : The `v`-adic valuation of
  `r : R` is less than 1 if and only if `v` divides the ideal `(r)`.
- `IsDedekindDomain.HeightOneSpectrum.intValuation_le_pow_iff_dvd` : The `v`-adic valuation of
  `r : R` is less than or equal to `WithZero.exp (-n)` if and only if `vⁿ` divides the
  ideal `(r)`.
- `IsDedekindDomain.HeightOneSpectrum.intValuation_exists_uniformizer` : There exists `π : R`
  with `v`-adic valuation `WithZero.exp (-1)`.
- `IsDedekindDomain.HeightOneSpectrum.valuation_of_mk'` : The `v`-adic valuation of `r / s : K`
  is the valuation of `r` divided by the valuation of `s`.
- `IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap` : The `v`-adic valuation on `K`
  extends the `v`-adic valuation on `R`.
- `IsDedekindDomain.HeightOneSpectrum.valuation_exists_uniformizer` : There exists `π : K` with
  `v`-adic valuation `WithZero.exp (-1)`.

## Implementation notes
We are only interested in Dedekind domains with Krull dimension 1.

## References
* [G. J. Janusz, *Algebraic Number Fields*][janusz1996]
* [J.W.S. Cassels, A. Fröhlich, *Algebraic Number Theory*][cassels1967algebraic]
* [J. Neukirch, *Algebraic Number Theory*][Neukirch1992]

## Tags
dedekind domain, dedekind ring, adic valuation
-/

@[expose] public section

noncomputable section

open WithZero Multiplicative IsDedekindDomain

variable {R : Type*} [CommRing R] [IsDedekindDomain R] {K S : Type*} [Field K] [CommSemiring S]
  [Algebra R K] [IsFractionRing R K] (v : HeightOneSpectrum R)

namespace IsDedekindDomain.HeightOneSpectrum

/-! ### Adic valuations on the Dedekind domain R -/

open scoped Classical in
/--
Definition of `intValuationDef` / `intValuationDef` 的定义

English:
definition intValuationDef
  signature: (r : R)
  body: if r = 0 then 0
  else
    exp (-(Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {r} : Ideal R)).factors : Int)

中文:
定义 intValuationDef
  签名: (r : R)
  定义体: if r = 0 then 0
  else
    exp (-(Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {r} : Ideal R)).factors : Int)

Depends on / 依赖: Associates, Associates.mk, Ideal.span, asIdeal, factors, v.asIdeal
-/
def intValuationDef (r : R) : Intᵐ⁰ :=
  if r = 0 then 0
  else
    exp (-(Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {r} : Ideal R)).factors : Int)

/--
theorem `intValuationDef_if_pos` / 定理 `intValuationDef_if_pos`

English:
theorem intValuationDef_if_pos
  given: {r : R} (hr : r = 0)
  statement: v.intValuationDef r = 0
  proof: if_pos hr

@[simp]

中文:
定理 intValuationDef_if_pos
  条件: {r : R} (hr : r = 0)
  结论: v.intValuationDef r = 0
  证明: if_pos hr

@[simp]

Depends on / 依赖: if_pos
-/
theorem intValuationDef_if_pos {r : R} (hr : r = 0) : v.intValuationDef r = 0 :=
  if_pos hr

@[simp]
/--
theorem `intValuationDef_zero` / 定理 `intValuationDef_zero`

English:
theorem intValuationDef_zero
  statement: v.intValuationDef 0 = 0
  proof: if_pos rfl

中文:
定理 intValuationDef_zero
  结论: v.intValuationDef 0 = 0
  证明: if_pos rfl

Depends on / 依赖: if_pos
-/
theorem intValuationDef_zero : v.intValuationDef 0 = 0 :=
  if_pos rfl

/--
theorem `intValuationDef_if_neg` / 定理 `intValuationDef_if_neg`

English:
theorem intValuationDef_if_neg
  given: {r : R} (hr : r != 0)
  proof: if_neg hr

中文:
定理 intValuationDef_if_neg
  条件: {r : R} (hr : r != 0)
  证明: if_neg hr

Depends on / 依赖: if_neg
-/
theorem intValuationDef_if_neg {r : R} (hr : r != 0) :
    v.intValuationDef r = exp
        (-(Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {r} : Ideal R)).factors : Int) :=
  if_neg hr

/--
theorem `intValuation.map_zero'` / 定理 `intValuation.map_zero'`

English:
theorem intValuation.map_zero'
  statement: v.intValuationDef 0 = 0
  proof: v.intValuationDef_if_pos rfl

中文:
定理 intValuation.map_zero'
  结论: v.intValuationDef 0 = 0
  证明: v.intValuationDef_if_pos rfl

Depends on / 依赖: intValuationDef_if_pos, v.intValuationDef_if_pos
-/
theorem intValuation.map_zero' : v.intValuationDef 0 = 0 :=
  v.intValuationDef_if_pos rfl

/--
theorem `intValuation.map_one'` / 定理 `intValuation.map_one'`

English:
theorem intValuation.map_one'
  statement: v.intValuationDef 1 = 1
  proof: by
  rw [v.intValuationDef_if_neg one_ne_zero]; rw [Ideal.span_singleton_one]; rw [← Ideal.one_eq_top]; rw [Associates.mk_one]; rw [Associates.factors_one]; rw [Associates.count_zero v.associates_irreducible]; rw [Int.ofNat_zero]; rw [neg_zero]; rw [exp_zero]

中文:
定理 intValuation.map_one'
  结论: v.intValuationDef 1 = 1
  证明: by
  rw [v.intValuationDef_if_neg one_ne_zero]; rw [Ideal.span_singleton_one]; rw [← Ideal.one_eq_top]; rw [Associates.mk_one]; rw [Associates.factors_one]; rw [Associates.count_zero v.associates_irreducible]; rw [Int.ofNat_zero]; rw [neg_zero]; rw [exp_zero]

Depends on / 依赖: Associates, Associates.count_zero, Associates.factors_one, Associates.mk_one, Ideal.one_eq_top, Ideal.span_singleton_one, Int.ofNat_zero, associates_irreducible, count_zero, exp_zero, factors_one, intValuationDef_if_neg, mk_one, neg_zero, ofNat_zero, one_eq_top, one_ne_zero, span_singleton_one, v.associates_irreducible, v.intValuationDef_if_neg
-/
theorem intValuation.map_one' : v.intValuationDef 1 = 1 := by
  rw [v.intValuationDef_if_neg one_ne_zero]; rw [Ideal.span_singleton_one]; rw [← Ideal.one_eq_top]; rw [Associates.mk_one]; rw [Associates.factors_one]; rw [Associates.count_zero v.associates_irreducible]; rw [Int.ofNat_zero]; rw [neg_zero]; rw [exp_zero]

/--
theorem `intValuation.map_mul'` / 定理 `intValuation.map_mul'`

English:
theorem intValuation.map_mul'
  given: (x y : R)
  proof: by
  simp only [intValuationDef]
  by_cases hx : x = 0
  · rw [hx, zero_mul, if_pos rfl, zero_mul]
  · by_cases hy : y = 0
    · rw [hy, mul_zero, if_pos rfl, mul_zero]
    · rw [if_neg hx, if_neg hy, if_neg (mul_ne_zero hx hy), ← exp_add,
        ← Ideal.span_singleton_mul_span_singleton, ← Associa

中文:
定理 intValuation.map_mul'
  条件: (x y : R)
  证明: by
  simp only [intValuationDef]
  by_cases hx : x = 0
  · rw [hx, zero_mul, if_pos rfl, zero_mul]
  · by_cases hy : y = 0
    · rw [hy, mul_zero, if_pos rfl, mul_zero]
    · rw [if_neg hx, if_neg hy, if_neg (mul_ne_zero hx hy), ← exp_add,
        ← Ideal.span_singleton_mul_span_singleton, ← Associa

Depends on / 依赖: Associates, Associates.count_mul, Associates.mk_mul_mk, Associates.mk_ne_zero, Ideal.span_singleton_mul_span_singleton, Nat.cast_add, associates_irreducible, cast_add, count_mul, exp_add, if_neg, if_pos, intValuationDef, mk_mul_mk, mk_ne_zero, mul_ne_zero, mul_zero, neg_add, span_singleton_mul_span_singleton, v.associates_irreducible
-/
theorem intValuation.map_mul' (x y : R) :
    v.intValuationDef (x * y) = v.intValuationDef x * v.intValuationDef y := by
  simp only [intValuationDef]
  by_cases hx : x = 0
  · rw [hx, zero_mul, if_pos rfl, zero_mul]
  · by_cases hy : y = 0
    · rw [hy, mul_zero, if_pos rfl, mul_zero]
    · rw [if_neg hx, if_neg hy, if_neg (mul_ne_zero hx hy), ← exp_add,
        ← Ideal.span_singleton_mul_span_singleton, ← Associates.mk_mul_mk, ← neg_add,
        Associates.count_mul (Associates.mk_ne_zero'.mpr hx) (Associates.mk_ne_zero'.mpr hy)
          v.associates_irreducible,
        Nat.cast_add]

-- TODO: unused, this is general over any linear order
/--
theorem `intValuation.le_max_iff_min_le` / 定理 `intValuation.le_max_iff_min_le`

English:
theorem intValuation.le_max_iff_min_le
  given: {a b c : Nat}
  proof: by
  rw [le_max_iff]; rw [ofAdd_le]; rw [ofAdd_le]; rw [neg_le_neg_iff]; rw [neg_le_neg_iff]; rw [Int.ofNat_le]; rw [Int.ofNat_le]; rw [← min_le_iff]

中文:
定理 intValuation.le_max_iff_min_le
  条件: {a b c : 自然数}
  证明: by
  rw [le_max_iff]; rw [ofAdd_le]; rw [ofAdd_le]; rw [neg_le_neg_iff]; rw [neg_le_neg_iff]; rw [Int.ofNat_le]; rw [Int.ofNat_le]; rw [← min_le_iff]

Depends on / 依赖: Int.ofNat_le, le_max_iff, min_le_iff, neg_le_neg_iff, ofAdd_le, ofNat_le
-/
theorem intValuation.le_max_iff_min_le {a b c : Nat} :
    Multiplicative.ofAdd (-c : Int) <=
      max (Multiplicative.ofAdd (-a : Int)) (Multiplicative.ofAdd (-b : Int)) ↔
      min a b <= c := by
  rw [le_max_iff]; rw [ofAdd_le]; rw [ofAdd_le]; rw [neg_le_neg_iff]; rw [neg_le_neg_iff]; rw [Int.ofNat_le]; rw [Int.ofNat_le]; rw [← min_le_iff]

/--
theorem `intValuation.map_add_le_max'` / 定理 `intValuation.map_add_le_max'`

English:
theorem intValuation.map_add_le_max'
  given: (x y : R)
  proof: by
  by_cases hx : x = 0
  · rw [hx, zero_add]
    order
  · by_cases hy : y = 0
    · rw [hy, add_zero]
      order
    · by_cases hxy : x + y = 0
      · rw [intValuationDef, if_pos hxy]; exact zero_le
      · rw [v.intValuationDef_if_neg hxy, v.intValuationDef_if_neg hx, v.intValuationDef_if_neg 

中文:
定理 intValuation.map_add_le_max'
  条件: (x y : R)
  证明: by
  by_cases hx : x = 0
  · rw [hx, zero_add]
    order
  · by_cases hy : y = 0
    · rw [hy, add_zero]
      order
    · by_cases hxy : x + y = 0
      · rw [intValuationDef, if_pos hxy]; exact zero_le
      · rw [v.intValuationDef_if_neg hxy, v.intValuationDef_if_neg hx, v.intValuationDef_if_neg 

Depends on / 依赖: Associates, Associates.mk, Ideal.span, Nat.cast_le, add_zero, asIdeal, cast_le, exp_le_exp, factors, if_pos, intValuationDef, intValuationDef_if_neg, le_max_iff, min_le_iff, neg_le_neg_iff, v.asIdeal, v.intValuationDef_if_neg, zero_add, zero_le
-/
theorem intValuation.map_add_le_max' (x y : R) :
    v.intValuationDef (x + y) <= max (v.intValuationDef x) (v.intValuationDef y) := by
  by_cases hx : x = 0
  · rw [hx, zero_add]
    order
  · by_cases hy : y = 0
    · rw [hy, add_zero]
      order
    · by_cases hxy : x + y = 0
      · rw [intValuationDef, if_pos hxy]; exact zero_le
      · rw [v.intValuationDef_if_neg hxy, v.intValuationDef_if_neg hx, v.intValuationDef_if_neg hy,
          le_max_iff]
        simp only [exp_le_exp, neg_le_neg_iff, Nat.cast_le, ← min_le_iff]
        set nmin :=
          min ((Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {x})).factors)
            ((Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {y})).factors)
        have h_dvd_x : x in v.asIdeal ^ nmin := by
          rw [← Associates.le_singleton_iff x nmin _]; rw [Associates.prime_pow_dvd_iff_le (Associates.mk_ne_zero'.mpr hx) _]
          · exact min_le_left _ _
          exact v.associates_irreducible
        have h_dvd_y : y in v.asIdeal ^ nmin := by
          rw [← Associates.le_singleton_iff y nmin _]; rw [Associates.prime_pow_dvd_iff_le (Associates.mk_ne_zero'.mpr hy) _]
          · exact min_le_right _ _
          exact v.associates_irreducible
        have h_dvd_xy : Associates.mk v.asIdeal ^ nmin <= Associates.mk (Ideal.span {x + y}) := by
          rw [Associates.le_singleton_iff]
          exact Ideal.add_mem (v.asIdeal ^ nmin) h_dvd_x h_dvd_y
        rw [Associates.prime_pow_dvd_iff_le (Associates.mk_ne_zero'.mpr hxy) _] at h_dvd_xy
        · exact h_dvd_xy
        exact v.associates_irreducible

/--
Definition of `intValuation` / `intValuation` 的定义

English:
definition intValuation
  signature: : Valuation R Intᵐ⁰ where
  body: v.intValuationDef
  map_zero' := intValuation.map_zero' v
  map_one' := intValuation.map_one' v
  map_mul' := intValuation.map_mul' v
  map_add_le_max' := intValuation.map_add_le_max' v

中文:
定义 intValuation
  签名: : 赋值 R 整数ᵐ⁰ where
  定义体: v.intValuationDef
  map_zero' := intValuation.map_zero' v
  map_one' := intValuation.map_one' v
  map_mul' := intValuation.map_mul' v
  map_add_le_max' := intValuation.map_add_le_max' v

Depends on / 依赖: intValuationDef, v.intValuationDef
-/
def intValuation : Valuation R Intᵐ⁰ where
  toFun := v.intValuationDef
  map_zero' := intValuation.map_zero' v
  map_one' := intValuation.map_one' v
  map_mul' := intValuation.map_mul' v
  map_add_le_max' := intValuation.map_add_le_max' v

/--
theorem `intValuation_apply` / 定理 `intValuation_apply`

English:
theorem intValuation_apply
  given: {r : R} (v : IsDedekindDomain.HeightOneSpectrum R)
  proof: rfl

中文:
定理 intValuation_apply
  条件: {r : R} (v : 是Dedekind整环.高一谱 R)
  证明: rfl
-/
theorem intValuation_apply {r : R} (v : IsDedekindDomain.HeightOneSpectrum R) :
    intValuation v r = intValuationDef v r := rfl

open scoped Classical in
/--
theorem `intValuation_def` / 定理 `intValuation_def`

English:
theorem intValuation_def
  given: {r : R}
  proof: rfl

中文:
定理 intValuation_def
  条件: {r : R}
  证明: rfl
-/
theorem intValuation_def {r : R} :
    v.intValuation r = if r = 0 then 0 else
    exp (-(Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {r} : Ideal R)).factors : Int) :=
  rfl

/--
theorem `intValuation_if_neg` / 定理 `intValuation_if_neg`

English:
theorem intValuation_if_neg
  given: {r : R} (hr : r != 0)
  proof: intValuationDef_if_neg _ hr

中文:
定理 intValuation_if_neg
  条件: {r : R} (hr : r != 0)
  证明: intValuationDef_if_neg _ hr

Depends on / 依赖: intValuationDef_if_neg
-/
theorem intValuation_if_neg {r : R} (hr : r != 0) :
    v.intValuation r = exp
        (-(Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {r} : Ideal R)).factors : Int) :=
  intValuationDef_if_neg _ hr

/--
theorem `intValuation_eq_exp_neg_multiplicity` / 定理 `intValuation_eq_exp_neg_multiplicity`

English:
theorem intValuation_eq_exp_neg_multiplicity
  given: {r : R} (hr : r != 0)
  proof: by
  have hsr : Ideal.span {r} != 0 := Submodule.span_singleton_eq_bot.mp.mt hr
  have hfm : FiniteMultiplicity v.asIdeal (Ideal.span {r}) :=
    FiniteMultiplicity.of_prime_left v.prime hsr
  rw [v.intValuation_if_neg hr]; rw [exp_inj]; rw [neg_inj]; rw [Int.natCast_inj]; rw [← ENat.natCast_inj]; r

中文:
定理 intValuation_eq_exp_neg_multiplicity
  条件: {r : R} (hr : r != 0)
  证明: by
  have hsr : Ideal.span {r} != 0 := Submodule.span_singleton_eq_bot.mp.mt hr
  have hfm : FiniteMultiplicity v.asIdeal (Ideal.span {r}) :=
    FiniteMultiplicity.of_prime_left v.prime hsr
  rw [v.intValuation_if_neg hr]; rw [exp_inj]; rw [neg_inj]; rw [Int.natCast_inj]; rw [← ENat.natCast_inj]; r

Depends on / 依赖: ENat.natCast_inj, FiniteMultiplicity, FiniteMultiplicity.emultiplicity_eq_multiplicity, FiniteMultiplicity.of_prime_left, Ideal.count_associates_factors_eq, Ideal.span, Int.natCast_inj, Submodule, Submodule.span_singleton_eq_bot.mp.mt, UniqueFactorizationMonoid, UniqueFactorizationMonoid.emultiplicity_eq_count_normalizedFactors, asIdeal, count_associates_factors_eq, emultiplicity_eq_count_normalizedFactors, emultiplicity_eq_multiplicity, exp_inj, intValuation_if_neg, irreducible, natCast_inj, neg_inj
-/
theorem intValuation_eq_exp_neg_multiplicity {r : R} (hr : r != 0) :
    v.intValuation r = exp (-multiplicity v.asIdeal (Ideal.span {r}) : Int) := by
  have hsr : Ideal.span {r} != 0 := Submodule.span_singleton_eq_bot.mp.mt hr
  have hfm : FiniteMultiplicity v.asIdeal (Ideal.span {r}) :=
    FiniteMultiplicity.of_prime_left v.prime hsr
  rw [v.intValuation_if_neg hr]; rw [exp_inj]; rw [neg_inj]; rw [Int.natCast_inj]; rw [← ENat.natCast_inj]; rw [← FiniteMultiplicity.emultiplicity_eq_multiplicity hfm]; rw [UniqueFactorizationMonoid.emultiplicity_eq_count_normalizedFactors (irreducible v) hsr]; rw [normalize_eq]; rw [Ideal.count_associates_factors_eq hsr v.isPrime v.ne_bot]

/--
theorem `intValuation_ne_zero` / 定理 `intValuation_ne_zero`

English:
theorem intValuation_ne_zero
  given: (x : R) (hx : x != 0)
  statement: v.intValuation x != 0
  proof: by
  rw [v.intValuation_if_neg hx]
  exact WithZero.coe_ne_zero

中文:
定理 intValuation_ne_zero
  条件: (x : R) (hx : x != 0)
  结论: v.intValuation x != 0
  证明: by
  rw [v.intValuation_if_neg hx]
  exact WithZero.coe_ne_zero

Depends on / 依赖: WithZero, WithZero.coe_ne_zero, coe_ne_zero, intValuation_if_neg, v.intValuation_if_neg
-/
theorem intValuation_ne_zero (x : R) (hx : x != 0) : v.intValuation x != 0 := by
  rw [v.intValuation_if_neg hx]
  exact WithZero.coe_ne_zero

/--
theorem `intValuation_ne_zero'` / 定理 `intValuation_ne_zero'`

English:
theorem intValuation_ne_zero'
  given: (x : nonZeroDivisors R)
  statement: v.intValuation x != 0
  proof: v.intValuation_ne_zero x (nonZeroDivisors.coe_ne_zero x)

中文:
定理 intValuation_ne_zero'
  条件: (x : nonZeroDivisors R)
  结论: v.intValuation x != 0
  证明: v.intValuation_ne_zero x (nonZeroDivisors.coe_ne_zero x)

Depends on / 依赖: coe_ne_zero, intValuation_ne_zero, nonZeroDivisors, nonZeroDivisors.coe_ne_zero, v.intValuation_ne_zero
-/
theorem intValuation_ne_zero' (x : nonZeroDivisors R) : v.intValuation x != 0 :=
  v.intValuation_ne_zero x (nonZeroDivisors.coe_ne_zero x)

/--
theorem `intValuation_zero_lt` / 定理 `intValuation_zero_lt`

English:
theorem intValuation_zero_lt
  given: (x : nonZeroDivisors R)
  statement: 0 < v.intValuation x
  proof: by
  rw [v.intValuation_if_neg (nonZeroDivisors.coe_ne_zero x)]
  exact WithZero.zero_lt_coe _

中文:
定理 intValuation_zero_lt
  条件: (x : nonZeroDivisors R)
  结论: 0 < v.intValuation x
  证明: by
  rw [v.intValuation_if_neg (nonZeroDivisors.coe_ne_zero x)]
  exact WithZero.zero_lt_coe _

Depends on / 依赖: WithZero, WithZero.zero_lt_coe, coe_ne_zero, intValuation_if_neg, nonZeroDivisors, nonZeroDivisors.coe_ne_zero, v.intValuation_if_neg, zero_lt_coe
-/
theorem intValuation_zero_lt (x : nonZeroDivisors R) : 0 < v.intValuation x := by
  rw [v.intValuation_if_neg (nonZeroDivisors.coe_ne_zero x)]
  exact WithZero.zero_lt_coe _

/--
theorem `intValuation_le_one` / 定理 `intValuation_le_one`

English:
theorem intValuation_le_one
  given: (x : R)
  statement: v.intValuation x <= 1
  proof: by
  obtain rfl | hx := eq_or_ne x 0
  · simp
  · rw [v.intValuation_if_neg hx, ← exp_zero, exp_le_exp, Right.neg_nonpos_iff]
    exact Int.natCast_nonneg _

中文:
定理 intValuation_le_one
  条件: (x : R)
  结论: v.intValuation x <= 1
  证明: by
  obtain rfl | hx := eq_or_ne x 0
  · simp
  · rw [v.intValuation_if_neg hx, ← exp_zero, exp_le_exp, Right.neg_nonpos_iff]
    exact Int.natCast_nonneg _

Depends on / 依赖: Int.natCast_nonneg, Right.neg_nonpos_iff, eq_or_ne, exp_le_exp, exp_zero, intValuation_if_neg, natCast_nonneg, neg_nonpos_iff, v.intValuation_if_neg
-/
theorem intValuation_le_one (x : R) : v.intValuation x <= 1 := by
  obtain rfl | hx := eq_or_ne x 0
  · simp
  · rw [v.intValuation_if_neg hx, ← exp_zero, exp_le_exp, Right.neg_nonpos_iff]
    exact Int.natCast_nonneg _

/--
theorem `intValuation_lt_one_iff_dvd` / 定理 `intValuation_lt_one_iff_dvd`

English:
theorem intValuation_lt_one_iff_dvd
  given: (r : R)
  proof: by
  by_cases hr : r = 0
  · simp [hr]
  · rw [v.intValuation_if_neg hr, ← exp_zero, exp_lt_exp,
      neg_lt_zero, ← Int.ofNat_zero, Int.ofNat_lt, zero_lt_iff]
    have h : (Ideal.span {r} : Ideal R) != 0 := by
      rw [Ne]; rw [Ideal.zero_eq_bot]; rw [Ideal.span_singleton_eq_bot]
      exact hr
 

中文:
定理 intValuation_lt_one_iff_dvd
  条件: (r : R)
  证明: by
  by_cases hr : r = 0
  · simp [hr]
  · rw [v.intValuation_if_neg hr, ← exp_zero, exp_lt_exp,
      neg_lt_zero, ← Int.ofNat_zero, Int.ofNat_lt, zero_lt_iff]
    have h : (Ideal.span {r} : Ideal R) != 0 := by
      rw [Ne]; rw [Ideal.zero_eq_bot]; rw [Ideal.span_singleton_eq_bot]
      exact hr
 

Depends on / 依赖: Associates, Associates.count_ne_zero_iff_dvd, Ideal.span, Ideal.span_singleton_eq_bot, Ideal.zero_eq_bot, Int.ofNat_lt, Int.ofNat_zero, count_ne_zero_iff_dvd, exp_lt_exp, exp_zero, intValuation_if_neg, irreducible, neg_lt_zero, ofNat_lt, ofNat_zero, span_singleton_eq_bot, v.intValuation_if_neg, v.irreducible, zero_eq_bot, zero_lt_iff
-/
theorem intValuation_lt_one_iff_dvd (r : R) :
    v.intValuation r < 1 ↔ v.asIdeal ∣ Ideal.span {r} := by
  by_cases hr : r = 0
  · simp [hr]
  · rw [v.intValuation_if_neg hr, ← exp_zero, exp_lt_exp,
      neg_lt_zero, ← Int.ofNat_zero, Int.ofNat_lt, zero_lt_iff]
    have h : (Ideal.span {r} : Ideal R) != 0 := by
      rw [Ne]; rw [Ideal.zero_eq_bot]; rw [Ideal.span_singleton_eq_bot]
      exact hr
    exact Associates.count_ne_zero_iff_dvd h v.irreducible

/--
theorem `intValuation_lt_one_iff_mem` / 定理 `intValuation_lt_one_iff_mem`

English:
theorem intValuation_lt_one_iff_mem
  given: (r : R)
  proof: by
  rw [intValuation_lt_one_iff_dvd]; rw [Ideal.dvd_span_singleton]

中文:
定理 intValuation_lt_one_iff_mem
  条件: (r : R)
  证明: by
  rw [intValuation_lt_one_iff_dvd]; rw [Ideal.dvd_span_singleton]

Depends on / 依赖: Ideal.dvd_span_singleton, dvd_span_singleton, intValuation_lt_one_iff_dvd
-/
theorem intValuation_lt_one_iff_mem (r : R) :
    v.intValuation r < 1 ↔ r in v.asIdeal := by
  rw [intValuation_lt_one_iff_dvd]; rw [Ideal.dvd_span_singleton]

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `intValuation_eq_one_iff_mem_primeCompl` / 定理 `intValuation_eq_one_iff_mem_primeCompl`

English:
theorem intValuation_eq_one_iff_mem_primeCompl
  given: (r : R)
  proof: by
  simp [Ideal.primeCompl, ← intValuation_lt_one_iff_mem, LE.le.ge_iff_eq (intValuation_le_one v r)]

中文:
定理 intValuation_eq_one_iff_mem_primeCompl
  条件: (r : R)
  证明: by
  simp [Ideal.primeCompl, ← intValuation_lt_one_iff_mem, LE.le.ge_iff_eq (intValuation_le_one v r)]

Depends on / 依赖: Ideal.primeCompl, LE.le.ge_iff_eq, ge_iff_eq, intValuation_le_one, intValuation_lt_one_iff_mem, primeCompl
-/
theorem intValuation_eq_one_iff_mem_primeCompl (r : R) :
    v.intValuation r = 1 ↔ r in v.asIdeal.primeCompl := by
  simp [Ideal.primeCompl, ← intValuation_lt_one_iff_mem, LE.le.ge_iff_eq (intValuation_le_one v r)]

/--
theorem `intValuation_le_pow_iff_dvd` / 定理 `intValuation_le_pow_iff_dvd`

English:
theorem intValuation_le_pow_iff_dvd
  given: (r : R) (n : Nat)
  proof: by
  by_cases hr : r = 0
  · simp_rw [hr, Valuation.map_zero, Ideal.dvd_span_singleton, zero_le, Submodule.zero_mem]
  · rw [v.intValuation_if_neg hr, exp_le_exp, neg_le_neg_iff, Int.ofNat_le,
      Ideal.dvd_span_singleton, ← Associates.le_singleton_iff,
      Associates.prime_pow_dvd_iff_le (Assoc

中文:
定理 intValuation_le_pow_iff_dvd
  条件: (r : R) (n : 自然数)
  证明: by
  by_cases hr : r = 0
  · simp_rw [hr, Valuation.map_zero, Ideal.dvd_span_singleton, zero_le, Submodule.zero_mem]
  · rw [v.intValuation_if_neg hr, exp_le_exp, neg_le_neg_iff, Int.ofNat_le,
      Ideal.dvd_span_singleton, ← Associates.le_singleton_iff,
      Associates.prime_pow_dvd_iff_le (Assoc

Depends on / 依赖: Associates, Associates.le_singleton_iff, Associates.mk_ne_zero, Associates.prime_pow_dvd_iff_le, Ideal.dvd_span_singleton, Int.ofNat_le, Submodule, Submodule.zero_mem, Valuation, Valuation.map_zero, associates_irreducible, dvd_span_singleton, exp_le_exp, intValuation_if_neg, le_singleton_iff, map_zero, mk_ne_zero, neg_le_neg_iff, ofNat_le, prime_pow_dvd_iff_le
-/
theorem intValuation_le_pow_iff_dvd (r : R) (n : Nat) :
    v.intValuation r <= exp (-(n : Int)) ↔ v.asIdeal ^ n ∣ Ideal.span {r} := by
  by_cases hr : r = 0
  · simp_rw [hr, Valuation.map_zero, Ideal.dvd_span_singleton, zero_le, Submodule.zero_mem]
  · rw [v.intValuation_if_neg hr, exp_le_exp, neg_le_neg_iff, Int.ofNat_le,
      Ideal.dvd_span_singleton, ← Associates.le_singleton_iff,
      Associates.prime_pow_dvd_iff_le (Associates.mk_ne_zero'.mpr hr) v.associates_irreducible]

/--
theorem `intValuation_le_pow_iff_mem` / 定理 `intValuation_le_pow_iff_mem`

English:
theorem intValuation_le_pow_iff_mem
  given: (r : R) (n : Nat)
  proof: by
  rw [intValuation_le_pow_iff_dvd]; rw [Ideal.dvd_span_singleton]

中文:
定理 intValuation_le_pow_iff_mem
  条件: (r : R) (n : 自然数)
  证明: by
  rw [intValuation_le_pow_iff_dvd]; rw [Ideal.dvd_span_singleton]

Depends on / 依赖: Ideal.dvd_span_singleton, dvd_span_singleton, intValuation_le_pow_iff_dvd
-/
theorem intValuation_le_pow_iff_mem (r : R) (n : Nat) :
    v.intValuation r <= exp (-(n : Int)) ↔ r in v.asIdeal ^ n := by
  rw [intValuation_le_pow_iff_dvd]; rw [Ideal.dvd_span_singleton]

/--
theorem `intValuation_le_exp_iff_le_emultiplicity` / 定理 `intValuation_le_exp_iff_le_emultiplicity`

English:
theorem intValuation_le_exp_iff_le_emultiplicity
  given: {r : R} {n : Nat}
  proof: by
  rw [intValuation_le_pow_iff_dvd]; rw [pow_dvd_iff_le_emultiplicity]

中文:
定理 intValuation_le_exp_iff_le_emultiplicity
  条件: {r : R} {n : 自然数}
  证明: by
  rw [intValuation_le_pow_iff_dvd]; rw [pow_dvd_iff_le_emultiplicity]

Depends on / 依赖: intValuation_le_pow_iff_dvd, pow_dvd_iff_le_emultiplicity
-/
theorem intValuation_le_exp_iff_le_emultiplicity {r : R} {n : Nat} :
    v.intValuation r <= exp (-(n : Int)) ↔ n <= emultiplicity v.asIdeal (Ideal.span {r}) := by
  rw [intValuation_le_pow_iff_dvd]; rw [pow_dvd_iff_le_emultiplicity]

/--
theorem `exp_le_intValuation_iff_emultiplicity_le` / 定理 `exp_le_intValuation_iff_emultiplicity_le`

English:
theorem exp_le_intValuation_iff_emultiplicity_le
  given: {r : R} {n : Nat}
  proof: by
  rw [← ENat.lt_natCast_add_one_iff]; rw [← ENat.natCast_one]; rw [← ENat.natCast_add]; rw [emultiplicity_lt_iff_not_dvd]; rw [← intValuation_le_pow_iff_dvd]; rw [not_le]; rw [Nat.cast_add]; rw [Nat.cast_one]; rw [neg_add]; rw [exp_add]; rw [exp_neg 1]; rw [mul_inv_lt_iff₀ (by simp)]
  by_cases h

中文:
定理 exp_le_intValuation_iff_emultiplicity_le
  条件: {r : R} {n : 自然数}
  证明: by
  rw [← ENat.lt_natCast_add_one_iff]; rw [← ENat.natCast_one]; rw [← ENat.natCast_add]; rw [emultiplicity_lt_iff_not_dvd]; rw [← intValuation_le_pow_iff_dvd]; rw [not_le]; rw [Nat.cast_add]; rw [Nat.cast_one]; rw [neg_add]; rw [exp_add]; rw [exp_neg 1]; rw [mul_inv_lt_iff₀ (by simp)]
  by_cases h

Depends on / 依赖: ENat.lt_natCast_add_one_iff, ENat.natCast_add, ENat.natCast_one, Nat.cast_add, Nat.cast_one, cast_add, cast_one, emultiplicity_lt_iff_not_dvd, exp_add, exp_neg, intValuation, intValuation_le_pow_iff_dvd, lt_mul_exp_iff_le, lt_natCast_add_one_iff, natCast_add, natCast_one, neg_add, not_le, v.intValuation
-/
theorem exp_le_intValuation_iff_emultiplicity_le {r : R} {n : Nat} :
    exp (-(n : Int)) <= v.intValuation r ↔ emultiplicity v.asIdeal (Ideal.span {r}) <= n := by
  rw [← ENat.lt_natCast_add_one_iff]; rw [← ENat.natCast_one]; rw [← ENat.natCast_add]; rw [emultiplicity_lt_iff_not_dvd]; rw [← intValuation_le_pow_iff_dvd]; rw [not_le]; rw [Nat.cast_add]; rw [Nat.cast_one]; rw [neg_add]; rw [exp_add]; rw [exp_neg 1]; rw [mul_inv_lt_iff₀ (by simp)]
  by_cases hv : v.intValuation r = 0
  · simp [hv]
  · rw [lt_mul_exp_iff_le hv]

/--
theorem `intValuation_exists_uniformizer` / 定理 `intValuation_exists_uniformizer`

English:
theorem intValuation_exists_uniformizer
  proof: by
  have hv : Irreducible (Associates.mk v.asIdeal) := v.associates_irreducible
  have hlt : v.asIdeal ^ 2 < v.asIdeal := by
    rw [← Ideal.dvdNotUnit_iff_lt]
    exact ⟨v.ne_bot, v.asIdeal, Ideal.isUnit_iff.not.mpr v.isPrime.ne_top, sq v.asIdeal⟩
  obtain ⟨π, mem, notMem⟩ := SetLike.exists_of_lt 

中文:
定理 intValuation_存在_uniformizer
  证明: by
  have hv : Irreducible (Associates.mk v.asIdeal) := v.associates_irreducible
  have hlt : v.asIdeal ^ 2 < v.asIdeal := by
    rw [← Ideal.dvdNotUnit_iff_lt]
    exact ⟨v.ne_bot, v.asIdeal, Ideal.isUnit_iff.not.mpr v.isPrime.ne_top, sq v.asIdeal⟩
  obtain ⟨π, mem, notMem⟩ := SetLike.exists_of_lt 

Depends on / 依赖: Associates, Associates.mk, Associates.mk_ne_zero, Ideal.dvdNotUnit_iff_lt, Ideal.isUnit_iff.not.mpr, Ideal.span, Irreducible, SetLike, SetLike.exists_of_lt, Submodule, Submodule.zero_mem, asIdeal, associates_irreducible, dvdNotUnit_iff_lt, exists_of_lt, intValuation_if_neg, isPrime, isUnit_iff, mk_ne_zero, ne_bot
-/
theorem intValuation_exists_uniformizer :
    exists π : R, v.intValuation π = WithZero.exp (-1 : Int) := by
  have hv : Irreducible (Associates.mk v.asIdeal) := v.associates_irreducible
  have hlt : v.asIdeal ^ 2 < v.asIdeal := by
    rw [← Ideal.dvdNotUnit_iff_lt]
    exact ⟨v.ne_bot, v.asIdeal, Ideal.isUnit_iff.not.mpr v.isPrime.ne_top, sq v.asIdeal⟩
  obtain ⟨π, mem, notMem⟩ := SetLike.exists_of_lt hlt
  have hπ : Associates.mk (Ideal.span {π}) != 0 := by
    rw [Associates.mk_ne_zero']
    intro h
    rw [h] at notMem
    exact notMem (Submodule.zero_mem (v.asIdeal ^ 2))
  use π
  rw [intValuation_if_neg _ (Associates.mk_ne_zero'.mp hπ)]; rw [exp_inj]
  apply congr_arg
  rw [← Int.ofNat_one]; rw [Int.natCast_inj]
  rw [← Ideal.dvd_span_singleton]; rw [← Associates.mk_le_mk_iff_dvd] at mem notMem
  rw [← pow_one (Associates.mk v.asIdeal)]; rw [Associates.prime_pow_dvd_iff_le hπ hv] at mem
  rw [Associates.mk_pow]; rw [Associates.prime_pow_dvd_iff_le hπ hv]; rw [not_le] at notMem
  exact Nat.eq_of_le_of_lt_succ mem notMem

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: v.intValuation.IsNontrivial
  body: have ⟨π, hπ⟩ := v.intValuation_exists_uniformizer
  ⟨π, by aesop⟩

@[simp]

中文:
实例 :
  签名: v.intValuation.是非平凡
  定义体: have ⟨π, hπ⟩ := v.intValuation_exists_uniformizer
  ⟨π, by aesop⟩

@[simp]

Depends on / 依赖: intValuation_exists_uniformizer, v.intValuation_exists_uniformizer
-/
instance : v.intValuation.IsNontrivial :=
  have ⟨π, hπ⟩ := v.intValuation_exists_uniformizer
  ⟨π, by aesop⟩

@[simp]
/--
theorem `intValuation_uniformizer` / 定理 `intValuation_uniformizer`

English:
theorem intValuation_uniformizer
  given: (π : v.intValuation.Uniformizer)
  proof: by
  simpa [Valuation.IsUniformizer.val π.valuation_gt_one, Units.ext_iff]
    using Valuation.IsRankOneDiscrete.generator_eq_exp_neg_one_of_mem_range
      v.intValuation_exists_uniformizer

中文:
定理 intValuation_uniformizer
  条件: (π : v.intValuation.一致化子)
  证明: by
  simpa [Valuation.IsUniformizer.val π.valuation_gt_one, Units.ext_iff]
    using Valuation.IsRankOneDiscrete.generator_eq_exp_neg_one_of_mem_range
      v.intValuation_exists_uniformizer

Depends on / 依赖: IsRankOneDiscrete, IsUniformizer, Units.ext_iff, Valuation, Valuation.IsRankOneDiscrete.generator_eq_exp_neg_one_of_mem_range, Valuation.IsUniformizer.val, ext_iff, generator_eq_exp_neg_one_of_mem_range, intValuation_exists_uniformizer, v.intValuation_exists_uniformizer, valuation_gt_one
-/
theorem intValuation_uniformizer (π : v.intValuation.Uniformizer) :
    v.intValuation (π.val : R) = WithZero.exp (-1) := by
  simpa [Valuation.IsUniformizer.val π.valuation_gt_one, Units.ext_iff]
    using Valuation.IsRankOneDiscrete.generator_eq_exp_neg_one_of_mem_range
      v.intValuation_exists_uniformizer

/--
theorem `intValuation_singleton` / 定理 `intValuation_singleton`

English:
theorem intValuation_singleton
  given: {r : R} (hr : r != 0) (hv : v.asIdeal = Ideal.span {r})
  proof: by
  rw [v.intValuation_if_neg hr]; rw [← hv]; rw [Associates.count_self]; rw [Int.ofNat_one]
  exact v.associates_irreducible

@[simp]

中文:
定理 intValuation_singleton
  条件: {r : R} (hr : r != 0) (hv : v.asIdeal = 理想.span {r})
  证明: by
  rw [v.intValuation_if_neg hr]; rw [← hv]; rw [Associates.count_self]; rw [Int.ofNat_one]
  exact v.associates_irreducible

@[simp]

Depends on / 依赖: Associates, Associates.count_self, Int.ofNat_one, associates_irreducible, count_self, intValuation_if_neg, ofNat_one, v.associates_irreducible, v.intValuation_if_neg
-/
theorem intValuation_singleton {r : R} (hr : r != 0) (hv : v.asIdeal = Ideal.span {r}) :
    v.intValuation r = exp (-1 : Int) := by
  rw [v.intValuation_if_neg hr]; rw [← hv]; rw [Associates.count_self]; rw [Int.ofNat_one]
  exact v.associates_irreducible

@[simp]
/--
theorem `intValuation_eq_one_iff` / 定理 `intValuation_eq_one_iff`

English:
theorem intValuation_eq_one_iff
  given: {v : HeightOneSpectrum R} {x : R}
  proof: by
  refine ⟨fun h => by simp [← (intValuation_lt_one_iff_mem _ _).not, h], fun h => ?_⟩
exact le_antisymm (v.intValuation_le_one x) by
    simp [← not_lt, (v.intValuation_lt_one_iff_mem _).not, h]

中文:
定理 intValuation_eq_one_iff
  条件: {v : 高一谱 R} {x : R}
  证明: by
  refine ⟨fun h => by simp [← (intValuation_lt_one_iff_mem _ _).not, h], fun h => ?_⟩
exact le_antisymm (v.intValuation_le_one x) by
    simp [← not_lt, (v.intValuation_lt_one_iff_mem _).not, h]

Depends on / 依赖: intValuation_le_one, intValuation_lt_one_iff_mem, le_antisymm, not_lt, v.intValuation_le_one, v.intValuation_lt_one_iff_mem
-/
theorem intValuation_eq_one_iff {v : HeightOneSpectrum R} {x : R} :
    v.intValuation x = 1 ↔ x ∉ v.asIdeal := by
  refine ⟨fun h => by simp [← (intValuation_lt_one_iff_mem _ _).not, h], fun h => ?_⟩
exact le_antisymm (v.intValuation_le_one x) by
    simp [← not_lt, (v.intValuation_lt_one_iff_mem _).not, h]

/-! ### Adic valuations on the field of fractions `K` -/

variable (K) in
/-- The `v`-adic valuation of `x : K` is the valuation of `r` divided by the valuation of `s`,
where `r` and `s` are chosen so that `x = r/s`. -/
@[no_expose]
/--
Definition of `valuation` / `valuation` 的定义

English:
definition valuation
  signature: (v : HeightOneSpectrum R)
  body: v.intValuation.extendToLocalization
    (fun r hr => Set.mem_compl <| v.intValuation_ne_zero' ⟨r, hr⟩) K

中文:
定义 valuation
  签名: (v : 高一谱 R)
  定义体: v.intValuation.extendToLocalization
    (fun r hr => Set.mem_compl <| v.intValuation_ne_zero' ⟨r, hr⟩) K

Depends on / 依赖: Set.mem_compl, extendToLocalization, intValuation, intValuation_ne_zero, mem_compl, v.intValuation.extendToLocalization, v.intValuation_ne_zero
-/
def valuation (v : HeightOneSpectrum R) : Valuation K Intᵐ⁰ :=
  v.intValuation.extendToLocalization
    (fun r hr => Set.mem_compl <| v.intValuation_ne_zero' ⟨r, hr⟩) K

/--
theorem `valuation_def` / 定理 `valuation_def`

English:
theorem valuation_def
  given: (x : K)
  proof: by rw [valuation]

中文:
定理 valuation_def
  条件: (x : K)
  证明: by rw [valuation]

Depends on / 依赖: valuation
-/
theorem valuation_def (x : K) :
    v.valuation K x =
      v.intValuation.extendToLocalization
        (fun r hr => Set.mem_compl (v.intValuation_ne_zero' ⟨r, hr⟩)) K x := by rw [valuation]

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `valuation_of_mk'` / 定理 `valuation_of_mk'`

English:
theorem valuation_of_mk'
  given: {r : R} {s : nonZeroDivisors R}
  proof: by
  rw [valuation_def]; rw [Valuation.extendToLocalization_mk']; rw [div_eq_mul_inv]

中文:
定理 valuation_of_mk'
  条件: {r : R} {s : nonZeroDivisors R}
  证明: by
  rw [valuation_def]; rw [Valuation.extendToLocalization_mk']; rw [div_eq_mul_inv]

Depends on / 依赖: Valuation, Valuation.extendToLocalization_mk, div_eq_mul_inv, extendToLocalization_mk, valuation_def
-/
theorem valuation_of_mk' {r : R} {s : nonZeroDivisors R} :
    v.valuation K (IsLocalization.mk' K r s) = v.intValuation r / v.intValuation s := by
  rw [valuation_def]; rw [Valuation.extendToLocalization_mk']; rw [div_eq_mul_inv]

set_option backward.isDefEq.respectTransparency.types false in
open scoped algebraMap in
/--
theorem `valuation_of_algebraMap` / 定理 `valuation_of_algebraMap`

English:
theorem valuation_of_algebraMap
  given: (r : R)
  statement: v.valuation K r = v.intValuation r
  proof: by
  rw [valuation_def]; rw [Valuation.extendToLocalization_apply_map_apply]

中文:
定理 valuation_of_algebraMap
  条件: (r : R)
  结论: v.valuation K r = v.intValuation r
  证明: by
  rw [valuation_def]; rw [Valuation.extendToLocalization_apply_map_apply]

Depends on / 依赖: Valuation, Valuation.extendToLocalization_apply_map_apply, extendToLocalization_apply_map_apply, valuation_def
-/
theorem valuation_of_algebraMap (r : R) : v.valuation K r = v.intValuation r := by
  rw [valuation_def]; rw [Valuation.extendToLocalization_apply_map_apply]

open scoped algebraMap in
/--
theorem `valuation_le_one` / 定理 `valuation_le_one`

English:
theorem valuation_le_one
  given: (r : R)
  statement: v.valuation K r <= 1
  proof: by
  rw [valuation_of_algebraMap]; exact v.intValuation_le_one r

中文:
定理 valuation_le_one
  条件: (r : R)
  结论: v.valuation K r <= 1
  证明: by
  rw [valuation_of_algebraMap]; exact v.intValuation_le_one r

Depends on / 依赖: intValuation_le_one, v.intValuation_le_one, valuation_of_algebraMap
-/
theorem valuation_le_one (r : R) : v.valuation K r <= 1 := by
  rw [valuation_of_algebraMap]; exact v.intValuation_le_one r

open scoped algebraMap in
/--
theorem `valuation_lt_one_iff_dvd` / 定理 `valuation_lt_one_iff_dvd`

English:
theorem valuation_lt_one_iff_dvd
  given: (r : R)
  proof: by
  rw [valuation_of_algebraMap]; exact v.intValuation_lt_one_iff_dvd r

中文:
定理 valuation_lt_one_iff_dvd
  条件: (r : R)
  证明: by
  rw [valuation_of_algebraMap]; exact v.intValuation_lt_one_iff_dvd r

Depends on / 依赖: intValuation_lt_one_iff_dvd, v.intValuation_lt_one_iff_dvd, valuation_of_algebraMap
-/
theorem valuation_lt_one_iff_dvd (r : R) :
    v.valuation K r < 1 ↔ v.asIdeal ∣ Ideal.span {r} := by
  rw [valuation_of_algebraMap]; exact v.intValuation_lt_one_iff_dvd r

open scoped algebraMap in
/--
theorem `valuation_lt_one_iff_mem` / 定理 `valuation_lt_one_iff_mem`

English:
theorem valuation_lt_one_iff_mem
  given: (r : R)
  proof: by
  rw [valuation_of_algebraMap]; exact v.intValuation_lt_one_iff_mem r

@[simp]

中文:
定理 valuation_lt_one_iff_mem
  条件: (r : R)
  证明: by
  rw [valuation_of_algebraMap]; exact v.intValuation_lt_one_iff_mem r

@[simp]

Depends on / 依赖: intValuation_lt_one_iff_mem, v.intValuation_lt_one_iff_mem, valuation_of_algebraMap
-/
theorem valuation_lt_one_iff_mem (r : R) :
    v.valuation K r < 1 ↔ r in v.asIdeal := by
  rw [valuation_of_algebraMap]; exact v.intValuation_lt_one_iff_mem r

@[simp]
/--
theorem `valuation_eq_one_iff_notMem` / 定理 `valuation_eq_one_iff_notMem`

English:
theorem valuation_eq_one_iff_notMem
  given: {r : R}
  proof: by
  rw [← HeightOneSpectrum.valuation_lt_one_iff_mem (K := K)]; rw [le_antisymm_iff]
  simp [HeightOneSpectrum.valuation_le_one]

中文:
定理 valuation_eq_one_iff_notMem
  条件: {r : R}
  证明: by
  rw [← HeightOneSpectrum.valuation_lt_one_iff_mem (K := K)]; rw [le_antisymm_iff]
  simp [HeightOneSpectrum.valuation_le_one]

Depends on / 依赖: HeightOneSpectrum, HeightOneSpectrum.valuation_le_one, HeightOneSpectrum.valuation_lt_one_iff_mem, le_antisymm_iff, valuation_le_one, valuation_lt_one_iff_mem
-/
theorem valuation_eq_one_iff_notMem {r : R} :
    v.valuation K (algebraMap R K r) = 1 ↔ r ∉ v.asIdeal := by
  rw [← HeightOneSpectrum.valuation_lt_one_iff_mem (K := K)]; rw [le_antisymm_iff]
  simp [HeightOneSpectrum.valuation_le_one]

variable (K) in
open scoped algebraMap in
/--
theorem `valuation_div_le_one_iff` / 定理 `valuation_div_le_one_iff`

English:
theorem valuation_div_le_one_iff
  statement: (a : R) {b : R} (hb : b != 0)
  proof: by
  refine ⟨fun hv => ?_, fun hb => by
    simp [valuation_of_algebraMap, intValuation_eq_one_iff.2 hb, intValuation_le_one]⟩
  contrapose! hv
  have ha₀ : a != 0 := fun _ => by simp_all
  have hva : v.valuation K a != 0 := (Valuation.ne_zero_iff _).2 (by simp [ha₀])
  have hvb : v.valuation K b !=

中文:
定理 valuation_div_le_one_iff
  结论: (a : R) {b : R} (hb : b != 0)
  证明: by
  refine ⟨fun hv => ?_, fun hb => by
    simp [valuation_of_algebraMap, intValuation_eq_one_iff.2 hb, intValuation_le_one]⟩
  contrapose! hv
  have ha₀ : a != 0 := fun _ => by simp_all
  have hva : v.valuation K a != 0 := (Valuation.ne_zero_iff _).2 (by simp [ha₀])
  have hvb : v.valuation K b !=

Depends on / 依赖: Int.sub_pos, Valuation, Valuation.ne_zero_iff, WithZero, WithZero.log_div, WithZero.log_lt_log, WithZero.log_one, contrapose, intValuation_eq_one_iff, intValuation_le_one, log_div, log_lt_log, log_one, ne_zero_iff, one_ne_zero, sub_pos, v.valuation, valuation, valuation_of_algebraMap
-/
theorem valuation_div_le_one_iff (a : R) {b : R} (hb : b != 0)
    (h : b in v.asIdeal -> a ∉ v.asIdeal) :
    v.valuation K (a / b) <= 1 ↔ b ∉ v.asIdeal := by
  refine ⟨fun hv => ?_, fun hb => by
    simp [valuation_of_algebraMap, intValuation_eq_one_iff.2 hb, intValuation_le_one]⟩
  contrapose! hv
  have ha₀ : a != 0 := fun _ => by simp_all
  have hva : v.valuation K a != 0 := (Valuation.ne_zero_iff _).2 (by simp [ha₀])
  have hvb : v.valuation K b != 0 := (Valuation.ne_zero_iff _).2 (by simp [hb])
  rw [← WithZero.log_lt_log one_ne_zero ((Valuation.ne_zero_iff _).2 (by simp [ha₀]; rw [hb])),
    map_div₀, WithZero.log_div hva hvb, WithZero.log_one, Int.sub_pos,
    WithZero.log_lt_log hvb hva]
  simpa [valuation_of_algebraMap, intValuation_eq_one_iff.2 <| h hv, intValuation_lt_one_iff_mem]

variable (K)

open scoped algebraMap in
/--
theorem `valuation_exists_uniformizer'` / 定理 `valuation_exists_uniformizer'`

English:
theorem valuation_exists_uniformizer'
  proof: by
  have ⟨π, hπ⟩ := intValuation_exists_uniformizer v
  use π
  grind [valuation_of_algebraMap]

中文:
定理 valuation_存在_uniformizer'
  证明: by
  have ⟨π, hπ⟩ := intValuation_exists_uniformizer v
  use π
  grind [valuation_of_algebraMap]

Depends on / 依赖: intValuation_exists_uniformizer, valuation_of_algebraMap
-/
theorem valuation_exists_uniformizer' :
    exists (π : R), (valuation K v) π = WithZero.exp (-1) := by
  have ⟨π, hπ⟩ := intValuation_exists_uniformizer v
  use π
  grind [valuation_of_algebraMap]

/--
theorem `valuation_exists_uniformizer` / 定理 `valuation_exists_uniformizer`

English:
theorem valuation_exists_uniformizer
  statement: exists π : K,
  proof: by
  obtain ⟨r, hr⟩ := v.valuation_exists_uniformizer' K
  use (algebraMap _ _ r)

中文:
定理 valuation_存在_uniformizer
  结论: 存在 π : K,
  证明: by
  obtain ⟨r, hr⟩ := v.valuation_exists_uniformizer' K
  use (algebraMap _ _ r)

Depends on / 依赖: algebraMap, v.valuation_exists_uniformizer, valuation_exists_uniformizer
-/
theorem valuation_exists_uniformizer : exists π : K,
    v.valuation K π = exp (-1 : Int) := by
  obtain ⟨r, hr⟩ := v.valuation_exists_uniformizer' K
  use (algebraMap _ _ r)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Valuation.IsNontrivial (v.valuation K)
  body: have ⟨π, hπ⟩ := v.valuation_exists_uniformizer K
  ⟨π, by aesop⟩

中文:
实例 :
  签名: 赋值.是非平凡 (v.valuation K)
  定义体: have ⟨π, hπ⟩ := v.valuation_exists_uniformizer K
  ⟨π, by aesop⟩

Depends on / 依赖: v.valuation_exists_uniformizer, valuation_exists_uniformizer
-/
instance : Valuation.IsNontrivial (v.valuation K) :=
  have ⟨π, hπ⟩ := v.valuation_exists_uniformizer K
  ⟨π, by aesop⟩

/--
lemma `valuation_surjective` / 引理 `valuation_surjective`

English:
lemma valuation_surjective
  proof: by
  intro x
  rcases GroupWithZero.eq_zero_or_unit x with (rfl | ⟨x, rfl⟩)
  · simp
  · obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer K
    refine ⟨π ^ (- log x.val), ?_⟩
    simp [hπ, exp_log]

中文:
引理 valuation_surjective
  证明: by
  intro x
  rcases GroupWithZero.eq_zero_or_unit x with (rfl | ⟨x, rfl⟩)
  · simp
  · obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer K
    refine ⟨π ^ (- log x.val), ?_⟩
    simp [hπ, exp_log]

Depends on / 依赖: GroupWithZero, GroupWithZero.eq_zero_or_unit, eq_zero_or_unit, exp_log, v.valuation_exists_uniformizer, valuation_exists_uniformizer, x.val
-/
lemma valuation_surjective :
    Function.Surjective (v.valuation K) := by
  intro x
  rcases GroupWithZero.eq_zero_or_unit x with (rfl | ⟨x, rfl⟩)
  · simp
  · obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer K
    refine ⟨π ^ (- log x.val), ?_⟩
    simp [hπ, exp_log]

/--
theorem `valuation_uniformizer_ne_zero` / 定理 `valuation_uniformizer_ne_zero`

English:
theorem valuation_uniformizer_ne_zero
  statement: Classical.choose (v.valuation_exists_uniformizer K) != 0
  proof: haveI hu := Classical.choose_spec (v.valuation_exists_uniformizer K)
  (Valuation.ne_zero_iff _).mp (ne_of_eq_of_ne hu WithZero.coe_ne_zero)

中文:
定理 valuation_uniformizer_ne_zero
  结论: 经典.choose (v.valuation_存在_uniformizer K) != 0
  证明: haveI hu := Classical.choose_spec (v.valuation_exists_uniformizer K)
  (Valuation.ne_zero_iff _).mp (ne_of_eq_of_ne hu WithZero.coe_ne_zero)

Depends on / 依赖: Classical, Classical.choose_spec, Valuation, Valuation.ne_zero_iff, WithZero, WithZero.coe_ne_zero, choose_spec, coe_ne_zero, ne_of_eq_of_ne, ne_zero_iff, v.valuation_exists_uniformizer, valuation_exists_uniformizer
-/
theorem valuation_uniformizer_ne_zero : Classical.choose (v.valuation_exists_uniformizer K) != 0 :=
  haveI hu := Classical.choose_spec (v.valuation_exists_uniformizer K)
  (Valuation.ne_zero_iff _).mp (ne_of_eq_of_ne hu WithZero.coe_ne_zero)

/--
theorem `mem_integers_of_valuation_le_one` / 定理 `mem_integers_of_valuation_le_one`

English:
theorem mem_integers_of_valuation_le_one
  statement: (x : K)
  proof: by
  obtain ⟨⟨n, d, hd⟩, hx⟩ := IsLocalization.surj (nonZeroDivisors R) x
  obtain rfl : x = IsLocalization.mk' K n ⟨d, hd⟩ := IsLocalization.eq_mk'_iff_mul_eq.mpr hx
  obtain rfl | hn0 := eq_or_ne n 0
  · simp
  have hd0 := nonZeroDivisors.ne_zero hd
  suffices Ideal.span {d} ∣ (Ideal.span {n} : Id

中文:
定理 mem_integers_of_valuation_le_one
  结论: (x : K)
  证明: by
  obtain ⟨⟨n, d, hd⟩, hx⟩ := IsLocalization.surj (nonZeroDivisors R) x
  obtain rfl : x = IsLocalization.mk' K n ⟨d, hd⟩ := IsLocalization.eq_mk'_iff_mul_eq.mpr hx
  obtain rfl | hn0 := eq_or_ne n 0
  · simp
  have hd0 := nonZeroDivisors.ne_zero hd
  suffices Ideal.span {d} ∣ (Ideal.span {n} : Id

Depends on / 依赖: Ideal.le_of_dvd, Ideal.span, Ideal.span_singleton_le_span_singleton, IsLocalization, IsLocalization.eq_mk, IsLocalization.mk, IsLocalization.surj, _iff_mul_eq, _iff_mul_eq.mpr, eq_mk, eq_or_ne, hx.resolve_right, le_of_dvd, map_mul, mul_comm, mul_eq_mul_left_iff, ne_zero, nonZeroDivisors, nonZeroDivisors.ne_zero, resolve_right
-/
theorem mem_integers_of_valuation_le_one (x : K)
    (h : forall v : HeightOneSpectrum R, v.valuation K x <= 1) : x in (algebraMap R K).range := by
  obtain ⟨⟨n, d, hd⟩, hx⟩ := IsLocalization.surj (nonZeroDivisors R) x
  obtain rfl : x = IsLocalization.mk' K n ⟨d, hd⟩ := IsLocalization.eq_mk'_iff_mul_eq.mpr hx
  obtain rfl | hn0 := eq_or_ne n 0
  · simp
  have hd0 := nonZeroDivisors.ne_zero hd
  suffices Ideal.span {d} ∣ (Ideal.span {n} : Ideal R) by
    obtain ⟨z, rfl⟩ := Ideal.span_singleton_le_span_singleton.1 (Ideal.le_of_dvd this)
    use z
    rw [map_mul]; rw [mul_comm]; rw [mul_eq_mul_left_iff] at hx
    exact (hx.resolve_right fun h => by simp [hd0] at h).symm
  have ine {r : R} : r != 0 -> Ideal.span {r} != ⊥ := mt Ideal.span_singleton_eq_bot.mp
  rw [← Associates.mk_le_mk_iff_dvd]; rw [← Associates.factors_le]; rw [Associates.factors_mk _ (ine hn0)]; rw [Associates.factors_mk _ (ine hd0)]; rw [WithTop.coe_le_coe]; rw [Multiset.le_iff_count]
  rintro ⟨v, hv⟩
  obtain ⟨v, rfl⟩ := Associates.mk_surjective v
  have hv' := hv
  rw [Associates.irreducible_mk]; rw [irreducible_iff_prime] at hv
  specialize h ⟨v, Ideal.isPrime_of_prime hv, hv.ne_zero⟩
  simp_rw [valuation_of_mk', intValuation_if_neg _ hn0, intValuation_if_neg _ hd0, ← exp_sub,
    ← exp_zero, exp_le_exp, Associates.factors_mk _ (ine hn0),
    Associates.factors_mk _ (ine hd0), Associates.count_some hv'] at h
  simpa using h

variable {K}

/--
theorem `eq_of_valuation_isEquiv_valuation` / 定理 `eq_of_valuation_isEquiv_valuation`

English:
theorem eq_of_valuation_isEquiv_valuation
  statement: {p q : HeightOneSpectrum R}
  proof: by
  simp_all [Valuation.isEquiv_iff_val_lt_one, HeightOneSpectrum.ext_iff, Ideal.ext_iff,
    ← valuation_lt_one_iff_mem (K := K)]

中文:
定理 eq_of_valuation_isEquiv_valuation
  结论: {p q : 高一谱 R}
  证明: by
  simp_all [Valuation.isEquiv_iff_val_lt_one, HeightOneSpectrum.ext_iff, Ideal.ext_iff,
    ← valuation_lt_one_iff_mem (K := K)]

Depends on / 依赖: HeightOneSpectrum, HeightOneSpectrum.ext_iff, Ideal.ext_iff, Valuation, Valuation.isEquiv_iff_val_lt_one, ext_iff, isEquiv_iff_val_lt_one, valuation_lt_one_iff_mem
-/
theorem eq_of_valuation_isEquiv_valuation {p q : HeightOneSpectrum R}
    (hpq : (valuation K p).IsEquiv (valuation K q)) : p = q := by
  simp_all [Valuation.isEquiv_iff_val_lt_one, HeightOneSpectrum.ext_iff, Ideal.ext_iff,
    ← valuation_lt_one_iff_mem (K := K)]

section Localization

open Localization

local instance : IsDedekindDomain
    (subalgebra.ofField K _ v.asIdeal.primeCompl_le_nonZeroDivisors) :=
  IsLocalization.AtPrime.isDedekindDomain R v.asIdeal
    (subalgebra.ofField K _ v.asIdeal.primeCompl_le_nonZeroDivisors)

local instance : IsLocalRing (subalgebra.ofField K _ v.asIdeal.primeCompl_le_nonZeroDivisors) :=
  IsLocalization.AtPrime.isLocalRing
    (subalgebra.ofField K _ v.asIdeal.primeCompl_le_nonZeroDivisors) v.asIdeal

variable (K) in
/--
Definition of `valuationSubringAtPrime` / `valuationSubringAtPrime` 的定义

English:
definition valuationSubringAtPrime
  signature: : ValuationSubring K
  body: .ofSubring (subalgebra.ofField K _ v.asIdeal.primeCompl_le_nonZeroDivisors).toSubring fun x =>
    by simpa [IsLocalization.IsInteger] using ValuationRing.isInteger_or_isInteger
        (subalgebra.ofField K _ v.asIdeal.primeCompl_le_nonZeroDivisors) x

中文:
定义 valuationSubringAtPrime
  签名: : 赋值子环 K
  定义体: .ofSubring (subalgebra.ofField K _ v.asIdeal.primeCompl_le_nonZeroDivisors).toSubring fun x =>
    by simpa [IsLocalization.IsInteger] using ValuationRing.isInteger_or_isInteger
        (subalgebra.ofField K _ v.asIdeal.primeCompl_le_nonZeroDivisors) x

Depends on / 依赖: IsInteger, IsLocalization, IsLocalization.IsInteger, ValuationRing, ValuationRing.isInteger_or_isInteger, asIdeal, isInteger_or_isInteger, ofField, ofSubring, primeCompl_le_nonZeroDivisors, subalgebra, subalgebra.ofField, toSubring, v.asIdeal.primeCompl_le_nonZeroDivisors
-/
def valuationSubringAtPrime : ValuationSubring K :=
  .ofSubring (subalgebra.ofField K _ v.asIdeal.primeCompl_le_nonZeroDivisors).toSubring fun x =>
    by simpa [IsLocalization.IsInteger] using ValuationRing.isInteger_or_isInteger
        (subalgebra.ofField K _ v.asIdeal.primeCompl_le_nonZeroDivisors) x

open IsDedekindDomain

/--
theorem `valuationSubringAtPrime_toSubring` / 定理 `valuationSubringAtPrime_toSubring`

English:
theorem valuationSubringAtPrime_toSubring
  statement: (valuationSubringAtPrime K v).toSubring
  proof: rfl

中文:
定理 valuationSubringAtPrime_toSubring
  结论: (valuationSubringAtPrime K v).toSubring
  证明: rfl
-/
theorem valuationSubringAtPrime_toSubring : (valuationSubringAtPrime K v).toSubring
    = (subalgebra.ofField K _ v.asIdeal.primeCompl_le_nonZeroDivisors).toSubring := rfl

open scoped algebraMap in
/--
theorem `valuationSubringAtPrime_le_valuation` / 定理 `valuationSubringAtPrime_le_valuation`

English:
theorem valuationSubringAtPrime_le_valuation
  proof: by
  rintro x ⟨a, s, hs, rfl⟩
  suffices (valuation K v) (a / (s : K)) <= 1 by rwa [division_def (a : K) s] at this
  rwa [valuation_div_le_one_iff (K := K) v a (by aesop) (fun _ => by contradiction)]

中文:
定理 valuationSubringAtPrime_le_valuation
  证明: by
  rintro x ⟨a, s, hs, rfl⟩
  suffices (valuation K v) (a / (s : K)) <= 1 by rwa [division_def (a : K) s] at this
  rwa [valuation_div_le_one_iff (K := K) v a (by aesop) (fun _ => by contradiction)]

Depends on / 依赖: division_def, valuation, valuation_div_le_one_iff
-/
theorem valuationSubringAtPrime_le_valuation :
    valuationSubringAtPrime K v <= (valuation K v).valuationSubring := by
  rintro x ⟨a, s, hs, rfl⟩
  suffices (valuation K v) (a / (s : K)) <= 1 by rwa [division_def (a : K) s] at this
  rwa [valuation_div_le_one_iff (K := K) v a (by aesop) (fun _ => by contradiction)]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Algebra R (valuationSubringAtPrime K v)
  body: (subalgebra.ofField K _ v.asIdeal.primeCompl_le_nonZeroDivisors).algebra'

中文:
实例 :
  签名: 代数 R (valuationSubringAtPrime K v)
  定义体: (subalgebra.ofField K _ v.asIdeal.primeCompl_le_nonZeroDivisors).algebra'

Depends on / 依赖: algebra, asIdeal, ofField, primeCompl_le_nonZeroDivisors, subalgebra, subalgebra.ofField, v.asIdeal.primeCompl_le_nonZeroDivisors
-/
instance : Algebra R (valuationSubringAtPrime K v) :=
  (subalgebra.ofField K _ v.asIdeal.primeCompl_le_nonZeroDivisors).algebra'

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsScalarTower R (valuationSubringAtPrime K v) K
  body: IsScalarTower.of_algebraMap_eq (fun _ => rfl)

中文:
实例 :
  签名: 标量塔 R (valuationSubringAtPrime K v) K
  定义体: IsScalarTower.of_algebraMap_eq (fun _ => rfl)

Depends on / 依赖: IsScalarTower, IsScalarTower.of_algebraMap_eq, of_algebraMap_eq
-/
instance : IsScalarTower R (valuationSubringAtPrime K v) K :=
  IsScalarTower.of_algebraMap_eq (fun _ => rfl)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsDedekindDomain (valuationSubringAtPrime K v)
  body: IsLocalization.AtPrime.isDedekindDomain R v.asIdeal
    (subalgebra.ofField K _ v.asIdeal.primeCompl_le_nonZeroDivisors)

中文:
实例 :
  签名: 是Dedekind整环 (valuationSubringAtPrime K v)
  定义体: IsLocalization.AtPrime.isDedekindDomain R v.asIdeal
    (subalgebra.ofField K _ v.asIdeal.primeCompl_le_nonZeroDivisors)

Depends on / 依赖: AtPrime, IsLocalization, IsLocalization.AtPrime.isDedekindDomain, asIdeal, isDedekindDomain, ofField, primeCompl_le_nonZeroDivisors, subalgebra, subalgebra.ofField, v.asIdeal, v.asIdeal.primeCompl_le_nonZeroDivisors
-/
instance : IsDedekindDomain (valuationSubringAtPrime K v) :=
  IsLocalization.AtPrime.isDedekindDomain R v.asIdeal
    (subalgebra.ofField K _ v.asIdeal.primeCompl_le_nonZeroDivisors)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Ring.KrullDimLE 1 (valuationSubringAtPrime K v)
  body: Ring.KrullDimLE.mk₁' (fun _ a _ => IsPrime.to_maximal_ideal a)

中文:
实例 :
  签名: 环.Krull维数不超过 1 (valuationSubringAtPrime K v)
  定义体: Ring.KrullDimLE.mk₁' (fun _ a _ => IsPrime.to_maximal_ideal a)

Depends on / 依赖: IsPrime, IsPrime.to_maximal_ideal, KrullDimLE, Ring.KrullDimLE.mk, to_maximal_ideal
-/
instance : Ring.KrullDimLE 1 (valuationSubringAtPrime K v) :=
  Ring.KrullDimLE.mk₁' (fun _ a _ => IsPrime.to_maximal_ideal a)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsLocalization (v.asIdeal.primeCompl) (valuationSubringAtPrime K v)
  body: Localization.subalgebra.isLocalization_ofField K (v.asIdeal.primeCompl) _

中文:
实例 :
  签名: 是Localization (v.asIdeal.primeCompl) (valuationSubringAtPrime K v)
  定义体: Localization.subalgebra.isLocalization_ofField K (v.asIdeal.primeCompl) _

Depends on / 依赖: Localization, Localization.subalgebra.isLocalization_ofField, asIdeal, isLocalization_ofField, primeCompl, subalgebra, v.asIdeal.primeCompl
-/
instance : IsLocalization (v.asIdeal.primeCompl) (valuationSubringAtPrime K v) :=
  Localization.subalgebra.isLocalization_ofField K (v.asIdeal.primeCompl) _

end Localization

/--
theorem `valuationSubringAtPrime_eq_valuationSubring` / 定理 `valuationSubringAtPrime_eq_valuationSubring`

English:
theorem valuationSubringAtPrime_eq_valuationSubring
  proof: ValuationSubring.eq_of_le_of_ne_top _ (valuationSubringAtPrime_le_valuation v)
    (by simp only [ne_eq, Valuation.valuationSubring_eq_top_iff, not_not]; infer_instance)

中文:
定理 valuationSubringAtPrime_eq_valuationSubring
  证明: ValuationSubring.eq_of_le_of_ne_top _ (valuationSubringAtPrime_le_valuation v)
    (by simp only [ne_eq, Valuation.valuationSubring_eq_top_iff, not_not]; infer_instance)

Depends on / 依赖: Valuation, Valuation.valuationSubring_eq_top_iff, ValuationSubring, ValuationSubring.eq_of_le_of_ne_top, eq_of_le_of_ne_top, infer_instance, ne_eq, not_not, valuationSubringAtPrime_le_valuation, valuationSubring_eq_top_iff
-/
theorem valuationSubringAtPrime_eq_valuationSubring :
    valuationSubringAtPrime K v = (v.valuation K).valuationSubring :=
  ValuationSubring.eq_of_le_of_ne_top _ (valuationSubringAtPrime_le_valuation v)
    (by simp only [ne_eq, Valuation.valuationSubring_eq_top_iff, not_not]; infer_instance)

/--
lemma `exists_primeCompl_mul_eq_or_mul_eq` / 引理 `exists_primeCompl_mul_eq_or_mul_eq`

English:
lemma exists_primeCompl_mul_eq_or_mul_eq
  given: (x : K)
  proof: by
  -- It's already known that the localization of `R` at `v` is a (discrete) valuation ring, so
  -- write `x` or `x⁻¹` as `n / d` with `d ∈ vᶜ`.
  obtain (⟨r, hr⟩ | ⟨r, hr⟩) :=
    ValuationRing.isInteger_or_isInteger (valuationSubringAtPrime K v) x
  <;> obtain ⟨⟨n, d⟩, hnd⟩ := IsLocalization.su

中文:
引理 存在_primeCompl_mul_eq_or_mul_eq
  条件: (x : K)
  证明: by
  -- It's already known that the localization of `R` at `v` is a (discrete) valuation ring, so
  -- write `x` or `x⁻¹` as `n / d` with `d ∈ vᶜ`.
  obtain (⟨r, hr⟩ | ⟨r, hr⟩) :=
    ValuationRing.isInteger_or_isInteger (valuationSubringAtPrime K v) x
  <;> obtain ⟨⟨n, d⟩, hnd⟩ := IsLocalization.su
-/
lemma exists_primeCompl_mul_eq_or_mul_eq (x : K) :
    exists (n : R) (d : v.asIdeal.primeCompl), x * (algebraMap R K d) = (algebraMap R K n) ∨
        x * (algebraMap R K n) = (algebraMap R K d) := by
  -- It's already known that the localization of `R` at `v` is a (discrete) valuation ring, so
  -- write `x` or `x⁻¹` as `n / d` with `d ∈ vᶜ`.
  obtain (⟨r, hr⟩ | ⟨r, hr⟩) :=
    ValuationRing.isInteger_or_isInteger (valuationSubringAtPrime K v) x
  <;> obtain ⟨⟨n, d⟩, hnd⟩ := IsLocalization.surj v.asIdeal.primeCompl r
  <;> use n, d
  <;> apply_fun algebraMap _ K at hnd
  <;> grind [=_ IsScalarTower.algebraMap_apply]

/--
theorem `exists_primeCompl_mul_eq_of_integer` / 定理 `exists_primeCompl_mul_eq_of_integer`

English:
theorem exists_primeCompl_mul_eq_of_integer
  given: (x : K) (hv : v.valuation K x <= 1)
  proof: by
  obtain ⟨n, d, (hnd | hnd)⟩ := exists_primeCompl_mul_eq_or_mul_eq v x
  · use n, d
  · refine ⟨d, ⟨n, ?_⟩, hnd⟩
    rw [← v.intValuation_eq_one_iff_mem_primeCompl]
    apply eq_one_of_one_le_mul_right hv (intValuation_le_one v n)
    rw [← (v.intValuation_eq_one_iff_mem_primeCompl d).mpr d.prop]

中文:
定理 存在_primeCompl_mul_eq_of_integer
  条件: (x : K) (hv : v.valuation K x <= 1)
  证明: by
  obtain ⟨n, d, (hnd | hnd)⟩ := exists_primeCompl_mul_eq_or_mul_eq v x
  · use n, d
  · refine ⟨d, ⟨n, ?_⟩, hnd⟩
    rw [← v.intValuation_eq_one_iff_mem_primeCompl]
    apply eq_one_of_one_le_mul_right hv (intValuation_le_one v n)
    rw [← (v.intValuation_eq_one_iff_mem_primeCompl d).mpr d.prop]

Depends on / 依赖: d.prop, eq_one_of_one_le_mul_right, exists_primeCompl_mul_eq_or_mul_eq, intValuation_eq_one_iff_mem_primeCompl, intValuation_le_one, map_mul, v.intValuation_eq_one_iff_mem_primeCompl, valuation_of_algebraMap
-/
theorem exists_primeCompl_mul_eq_of_integer (x : K) (hv : v.valuation K x <= 1) :
    exists (n : R) (d : v.asIdeal.primeCompl), x * (algebraMap R K d) = algebraMap R K n := by
  obtain ⟨n, d, (hnd | hnd)⟩ := exists_primeCompl_mul_eq_or_mul_eq v x
  · use n, d
  · refine ⟨d, ⟨n, ?_⟩, hnd⟩
    rw [← v.intValuation_eq_one_iff_mem_primeCompl]
    apply eq_one_of_one_le_mul_right hv (intValuation_le_one v n)
    rw [← (v.intValuation_eq_one_iff_mem_primeCompl d).mpr d.prop]; rw [← valuation_of_algebraMap (K := K)]; rw [← valuation_of_algebraMap (K := K)]; rw [← map_mul]; rw [hnd]

/--
theorem `exists_intValuation_mul_sub_lt` / 定理 `exists_intValuation_mul_sub_lt`

English:
theorem exists_intValuation_mul_sub_lt
  statement: {a b : R} (hv : v.intValuation b <= v.intValuation a)
  proof: by
  -- If `a = 0`, then `b = 0`, so we can take `y = 0`.
  by_cases ha: a = 0
  · subst ha
    rw [map_zero]; rw [le_zero_iff] at hv
    exact ⟨0, by simp [hv]⟩
  · have hvaz := intValuation_ne_zero v a ha
    have hγz : WithZero.coe γ != 0 := WithZero.coe_ne_zero
    -- Otherwise, find `n : ℕ` suc

中文:
定理 存在_intValuation_mul_sub_lt
  结论: {a b : R} (hv : v.intValuation b <= v.intValuation a)
  证明: by
  -- If `a = 0`, then `b = 0`, so we can take `y = 0`.
  by_cases ha: a = 0
  · subst ha
    rw [map_zero]; rw [le_zero_iff] at hv
    exact ⟨0, by simp [hv]⟩
  · have hvaz := intValuation_ne_zero v a ha
    have hγz : WithZero.coe γ != 0 := WithZero.coe_ne_zero
    -- Otherwise, find `n : ℕ` suc
-/
theorem exists_intValuation_mul_sub_lt {a b : R} (hv : v.intValuation b <= v.intValuation a)
    (γ : Multiplicative Int) : exists y, v.intValuation (b - y * a) < γ := by
  -- If `a = 0`, then `b = 0`, so we can take `y = 0`.
  by_cases ha: a = 0
  · subst ha
    rw [map_zero]; rw [le_zero_iff] at hv
    exact ⟨0, by simp [hv]⟩
  · have hvaz := intValuation_ne_zero v a ha
    have hγz : WithZero.coe γ != 0 := WithZero.coe_ne_zero
    -- Otherwise, find `n : ℕ` such that `exp (-n) < γ` and `exp(-n) < v a`.
    obtain ⟨n, hna, hnγ⟩ := exists_exp_neg_natCast_lt_and_lt hvaz hγz
    apply Exists.imp (fun _ h => lt_of_le_of_lt h hnγ)
    -- `v b ≤ v a`, so `b ∈ v.asIdeal ^ -log (v a)`.
    -- From `irreducible_pow_sup_of_ge` we know that
    -- `v.asIdeal ^ -log (v a) = v.asIdeal ^ n ⊔ Ideal.span {a}`.
    -- So, `∃ z ∈ v.asIdeal ^ n, ∃ (y: R), b = z + y * a`. This gives `z` and `y` such that
    -- `b - y * a = z` and `v z ≤ exp (-n)`, as required.
    have hvn : emultiplicity v.asIdeal (Ideal.span {a}) <= n := by
      grw [← exp_le_intValuation_iff_emultiplicity_le, hna]
    have hb : b in v.asIdeal ^ multiplicity v.asIdeal (Ideal.span {a}) := by
      rwa [← intValuation_le_pow_iff_mem, ← v.intValuation_eq_exp_neg_multiplicity ha]
    have hnz : Ideal.span {a} != ⊥ := by rwa [ne_eq, Ideal.span_singleton_eq_bot]
    simpa [← Ideal.irreducible_pow_sup_of_ge hnz v.irreducible n hvn, Submodule.mem_sup,
      ← eq_sub_iff_add_eq, ← intValuation_le_pow_iff_mem, Ideal.mem_span_singleton'] using hb

/--
theorem `exists_valuation_sub_lt_of_integer` / 定理 `exists_valuation_sub_lt_of_integer`

English:
theorem exists_valuation_sub_lt_of_integer
  statement: {x : K} (hv : v.valuation K x <= 1)
  proof: by
  -- Write `x = n / d`, with `v d = 1`.
  obtain ⟨n, ⟨d, hd⟩, hnd⟩ := exists_primeCompl_mul_eq_of_integer v x hv
  rw [← intValuation_eq_one_iff_mem_primeCompl] at hd
  have hd' : v.intValuation n <= v.intValuation d := by grw [v.intValuation_le_one n, hd]
  -- Get `a` such that `v (n - a * d) < 

中文:
定理 存在_valuation_sub_lt_of_integer
  结论: {x : K} (hv : v.valuation K x <= 1)
  证明: by
  -- Write `x = n / d`, with `v d = 1`.
  obtain ⟨n, ⟨d, hd⟩, hnd⟩ := exists_primeCompl_mul_eq_of_integer v x hv
  rw [← intValuation_eq_one_iff_mem_primeCompl] at hd
  have hd' : v.intValuation n <= v.intValuation d := by grw [v.intValuation_le_one n, hd]
  -- Get `a` such that `v (n - a * d) < 
-/
theorem exists_valuation_sub_lt_of_integer {x : K} (hv : v.valuation K x <= 1)
    (γ : (Intᵐ⁰)ˣ) : existsa, v.valuation K (algebraMap R K a - x) < γ := by
  -- Write `x = n / d`, with `v d = 1`.
  obtain ⟨n, ⟨d, hd⟩, hnd⟩ := exists_primeCompl_mul_eq_of_integer v x hv
  rw [← intValuation_eq_one_iff_mem_primeCompl] at hd
  have hd' : v.intValuation n <= v.intValuation d := by grw [v.intValuation_le_one n, hd]
  -- Get `a` such that `v (n - a * d) < γ` from the previous theorem.
  obtain ⟨a, hval⟩ := exists_intValuation_mul_sub_lt v hd' (WithZero.unitsWithZeroEquiv γ)
  rw [unitsWithZeroEquiv_apply]; rw [coe_unzero] at hval
  use a
  -- `v d = 1`, so `v (a - x) = v (x - a) = v (x - a) * v d = v (n - a * d) < γ`.
  suffices h : v.valuation K (algebraMap R K a - x) = v.intValuation (n - a * d) by rwa [h]
  rw [← valuation_of_algebraMap (K := K)]; rw [Algebra.cast]; rw [map_sub _ n]; rw [map_mul]; rw [← hnd]; rw [← sub_mul]; rw [map_mul]; rw [valuation_of_algebraMap]; rw [hd]; rw [mul_one]; rw [Valuation.map_sub_swap]

/-! ### Completions with respect to adic valuations

Given a Dedekind domain `R` with field of fractions `K` and a maximal ideal `v` of `R`, we define
the completion of `K` with respect to its `v`-adic valuation, denoted `v.adicCompletion`, and its
ring of integers, denoted `v.adicCompletionIntegers`. -/


/-- `K` as a valued field with the `v`-adic valuation. -/
@[instance_reducible]
/--
Definition of `adicValued` / `adicValued` 的定义

English:
definition adicValued
  signature: : Valued K Intᵐ⁰
  body: Valued.mk' (v.valuation K)

中文:
定义 adicValued
  签名: : 赋值 K 整数ᵐ⁰
  定义体: Valued.mk' (v.valuation K)

Depends on / 依赖: Valued, Valued.mk, v.valuation, valuation
-/
def adicValued : Valued K Intᵐ⁰ :=
  Valued.mk' (v.valuation K)

/--
theorem `adicValued_apply` / 定理 `adicValued_apply`

English:
theorem adicValued_apply
  given: {x : K}
  statement: v.adicValued.v x = v.valuation K x
  proof: rfl

@[deprecated adicValued_apply (since := "2026-01-28")]

中文:
定理 adicValued_apply
  条件: {x : K}
  结论: v.adicValued.v x = v.valuation K x
  证明: rfl

@[deprecated adicValued_apply (since := "2026-01-28")]
-/
theorem adicValued_apply {x : K} : v.adicValued.v x = v.valuation K x :=
  rfl

@[deprecated adicValued_apply (since := "2026-01-28")]
/--
theorem `adicValued_apply'` / 定理 `adicValued_apply'`

English:
theorem adicValued_apply'
  given: (x : WithVal (v.valuation K))
  proof: rfl

中文:
定理 adicValued_apply'
  条件: (x : WithVal (v.valuation K))
  证明: rfl
-/
theorem adicValued_apply' (x : WithVal (v.valuation K)) :
    v.adicValued.v (WithVal.equiv _ x) = v.valuation K (WithVal.equiv _ x) :=
  rfl

variable (K)

/--
Definition of `adicCompletion` / `adicCompletion` 的定义

English:
structure adicCompletion
  parameters: where
  axioms and operations (2):
    - ofCompletion : :
    - toCompletion : (v.valuation K).Completion

中文:
结构 adicCompletion
  参数: where
  公理与运算 (2 个):
    - ofCompletion : :
    - toCompletion : (v.valuation K).完备化
-/
structure adicCompletion where
  /-- Wrap an element of the underlying completion `(v.valuation K).Completion` into
  `adicCompletion`. -/
  ofCompletion ::
  /-- The underlying element of the completion `(v.valuation K).Completion`. -/
  toCompletion : (v.valuation K).Completion

namespace adicCompletion

open UniformSpace MonoidWithZeroHom MonoidWithZeroHom.ValueGroup₀ Filter Topology Valuation

/-- `adicCompletion.toCompletion` and `adicCompletion.ofCompletion` as an equivalence. -/
@[simps]
/--
Definition of `equivCompletion` / `equivCompletion` 的定义

English:
definition equivCompletion
  signature: : adicCompletion K v ≃ (v.valuation K).Completion where
  body: toCompletion
  invFun := ofCompletion
  left_inv _ := rfl
  right_inv _ := rfl

中文:
定义 equivCompletion
  签名: : adicCompletion K v ≃ (v.valuation K).完备化 where
  定义体: toCompletion
  invFun := ofCompletion
  left_inv _ := rfl
  right_inv _ := rfl

Depends on / 依赖: toCompletion
-/
def equivCompletion : adicCompletion K v ≃ (v.valuation K).Completion where
  toFun := toCompletion
  invFun := ofCompletion
  left_inv _ := rfl
  right_inv _ := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Field (adicCompletion K v)
  body: fast_instance% (equivCompletion K v).field

中文:
实例 :
  签名: 域 (adicCompletion K v)
  定义体: fast_instance% (equivCompletion K v).field

Depends on / 依赖: equivCompletion, fast_instance
-/
noncomputable instance : Field (adicCompletion K v) := fast_instance% (equivCompletion K v).field

/-- `adicCompletion.toCompletion` as a ring isomorphism onto the underlying completion. -/
@[simps! apply]
/--
Definition of `equiv` / `equiv` 的定义

English:
definition equiv
  signature: : adicCompletion K v ≃+* (v.valuation K).Completion where
  body: equivCompletion K v
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

中文:
定义 equiv
  签名: : adicCompletion K v ≃+* (v.valuation K).完备化 where
  定义体: equivCompletion K v
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

Depends on / 依赖: equivCompletion
-/
def equiv : adicCompletion K v ≃+* (v.valuation K).Completion where
  toEquiv := equivCompletion K v
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

/--
lemma `toCompletion_ofCompletion` / 引理 `toCompletion_ofCompletion`

English:
lemma toCompletion_ofCompletion
  given: (x : (v.valuation K).Completion)
  proof: rfl

中文:
引理 toCompletion_ofCompletion
  条件: (x : (v.valuation K).完备化)
  证明: rfl
-/
@[simp] lemma toCompletion_ofCompletion (x : (v.valuation K).Completion) :
    toCompletion (ofCompletion x : adicCompletion K v) = x := rfl
/--
lemma `ofCompletion_toCompletion` / 引理 `ofCompletion_toCompletion`

English:
lemma ofCompletion_toCompletion
  given: (x : adicCompletion K v)
  proof: rfl

中文:
引理 ofCompletion_toCompletion
  条件: (x : adicCompletion K v)
  证明: rfl
-/
@[simp] lemma ofCompletion_toCompletion (x : adicCompletion K v) :
    ofCompletion x.toCompletion = x := rfl

/--
lemma `toCompletion_zero` / 引理 `toCompletion_zero`

English:
lemma toCompletion_zero
  statement: (0 : adicCompletion K v).toCompletion = 0
  proof: rfl

中文:
引理 toCompletion_zero
  结论: (0 : adicCompletion K v).toCompletion = 0
  证明: rfl
-/
@[simp] lemma toCompletion_zero : (0 : adicCompletion K v).toCompletion = 0 := rfl
/--
lemma `toCompletion_one` / 引理 `toCompletion_one`

English:
lemma toCompletion_one
  statement: (1 : adicCompletion K v).toCompletion = 1
  proof: rfl

中文:
引理 toCompletion_one
  结论: (1 : adicCompletion K v).toCompletion = 1
  证明: rfl
-/
@[simp] lemma toCompletion_one : (1 : adicCompletion K v).toCompletion = 1 := rfl
/--
lemma `toCompletion_add` / 引理 `toCompletion_add`

English:
lemma toCompletion_add
  given: (x y : adicCompletion K v)
  proof: rfl

中文:
引理 toCompletion_add
  条件: (x y : adicCompletion K v)
  证明: rfl
-/
@[simp] lemma toCompletion_add (x y : adicCompletion K v) :
    (x + y).toCompletion = x.toCompletion + y.toCompletion := rfl
/--
lemma `toCompletion_mul` / 引理 `toCompletion_mul`

English:
lemma toCompletion_mul
  given: (x y : adicCompletion K v)
  proof: rfl

中文:
引理 toCompletion_mul
  条件: (x y : adicCompletion K v)
  证明: rfl
-/
@[simp] lemma toCompletion_mul (x y : adicCompletion K v) :
    (x * y).toCompletion = x.toCompletion * y.toCompletion := rfl

/--
theorem `toCompletion_surjective` / 定理 `toCompletion_surjective`

English:
theorem toCompletion_surjective
  statement: Function.Surjective (toCompletion (K := K) (v := v))
  proof: (equivCompletion K v).surjective

中文:
定理 toCompletion_surjective
  结论: 函数.满射 (toCompletion (K := K) (v := v))
  证明: (equivCompletion K v).surjective
-/
theorem toCompletion_surjective : Function.Surjective (toCompletion (K := K) (v := v)) :=
  (equivCompletion K v).surjective

/--
theorem `ofCompletion_surjective` / 定理 `ofCompletion_surjective`

English:
theorem ofCompletion_surjective
  statement: Function.Surjective (ofCompletion (K := K) (v := v))
  proof: (equivCompletion K v).symm.surjective

中文:
定理 ofCompletion_surjective
  结论: 函数.满射 (ofCompletion (K := K) (v := v))
  证明: (equivCompletion K v).symm.surjective
-/
theorem ofCompletion_surjective : Function.Surjective (ofCompletion (K := K) (v := v)) :=
  (equivCompletion K v).symm.surjective

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: UniformSpace (adicCompletion K v)
  body: .comap toCompletion inferInstance

中文:
实例 :
  签名: 一致空间 (adicCompletion K v)
  定义体: .comap toCompletion inferInstance

Depends on / 依赖: toCompletion
-/
noncomputable instance : UniformSpace (adicCompletion K v) := .comap toCompletion inferInstance

/--
theorem `isUniformInducing_toCompletion` / 定理 `isUniformInducing_toCompletion`

English:
theorem isUniformInducing_toCompletion
  proof: ⟨rfl⟩

中文:
定理 isUniformInducing_toCompletion
  证明: ⟨rfl⟩
-/
theorem isUniformInducing_toCompletion :
    IsUniformInducing (toCompletion (K := K) (v := v)) := ⟨rfl⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsUniformAddGroup (adicCompletion K v)
  body: IsUniformInducing.isUniformAddGroup (equiv K v).toRingHom (isUniformInducing_toCompletion K v)

中文:
实例 :
  签名: 是UniformAdd群 (adicCompletion K v)
  定义体: IsUniformInducing.isUniformAddGroup (equiv K v).toRingHom (isUniformInducing_toCompletion K v)

Depends on / 依赖: IsUniformInducing, IsUniformInducing.isUniformAddGroup, isUniformAddGroup, isUniformInducing_toCompletion, toRingHom
-/
instance : IsUniformAddGroup (adicCompletion K v) :=
  IsUniformInducing.isUniformAddGroup (equiv K v).toRingHom (isUniformInducing_toCompletion K v)

/--
Definition of `valuation` / `valuation` 的定义

English:
definition valuation
  signature: : Valuation (adicCompletion K v) Intᵐ⁰
  body: Valued.v.comap (equiv K v).toRingHom

中文:
定义 valuation
  签名: : 赋值 (adicCompletion K v) 整数ᵐ⁰
  定义体: Valued.v.comap (equiv K v).toRingHom

Depends on / 依赖: Valued, Valued.v.comap, toRingHom
-/
noncomputable def valuation : Valuation (adicCompletion K v) Intᵐ⁰ :=
  Valued.v.comap (equiv K v).toRingHom

/--
theorem `valueGroup_eq` / 定理 `valueGroup_eq`

English:
theorem valueGroup_eq
  proof: by
  simp [valuation, valueGroup, valueMonoid, ← (toCompletion_surjective K v).range_comp]; rfl

中文:
定理 valueGroup_eq
  证明: by
  simp [valuation, valueGroup, valueMonoid, ← (toCompletion_surjective K v).range_comp]; rfl

Depends on / 依赖: range_comp, toCompletion_surjective, valuation, valueGroup, valueMonoid
-/
theorem valueGroup_eq :
    valueGroup (.ofClass (valuation K v)) =
      valueGroup (.ofClass (Valued.v : Valuation (v.valuation K).Completion Intᵐ⁰)) := by
  simp [valuation, valueGroup, valueMonoid, ← (toCompletion_surjective K v).range_comp]; rfl

/--
Definition of `valueGroupEquiv` / `valueGroupEquiv` 的定义

English:
definition valueGroupEquiv
  signature: :
  body: Equiv.setCongr (by rw [valueGroup_eq K v])
  map_mul' _ _ := rfl

中文:
定义 valueGroupEquiv
  签名: :
  定义体: Equiv.setCongr (by rw [valueGroup_eq K v])
  map_mul' _ _ := rfl

Depends on / 依赖: Equiv.setCongr, setCongr, valueGroup_eq
-/
def valueGroupEquiv :
    valueGroup (.ofClass (valuation K v)) ≃*
      valueGroup (.ofClass (Valued.v : Valuation (v.valuation K).Completion Intᵐ⁰)) where
  __ := Equiv.setCongr (by rw [valueGroup_eq K v])
  map_mul' _ _ := rfl

/--
theorem `coe_valueGroupEquiv` / 定理 `coe_valueGroupEquiv`

English:
theorem coe_valueGroupEquiv
  given: (a : valueGroup (.ofClass (valuation K v)))
  proof: rfl

中文:
定理 coe_valueGroupEquiv
  条件: (a : valueGroup (.ofClass (valuation K v)))
  证明: rfl
-/
@[simp] theorem coe_valueGroupEquiv (a : valueGroup (.ofClass (valuation K v))) :
    ((valueGroupEquiv K v a : _) : Intᵐ⁰ˣ) = a := rfl

/--
Definition of `valueGroupOrderIso` / `valueGroupOrderIso` 的定义

English:
definition valueGroupOrderIso
  signature: :
  body: WithZero.map' (valueGroupEquiv K v)
  invFun := WithZero.map' (valueGroupEquiv K v).symm
  left_inv x := by match x with | 0 => simp | .coe a => simp
  right_inv y := by match y with | 0 => simp | .coe b => simp
  map_mul' := by simp
  map_le_map_iff' {a b} := by
    match a, b with
    | 0, 0 => si

中文:
定义 valueGroupOrderIso
  签名: :
  定义体: WithZero.map' (valueGroupEquiv K v)
  invFun := WithZero.map' (valueGroupEquiv K v).symm
  left_inv x := by match x with | 0 => simp | .coe a => simp
  right_inv y := by match y with | 0 => simp | .coe b => simp
  map_mul' := by simp
  map_le_map_iff' {a b} := by
    match a, b with
    | 0, 0 => si

Depends on / 依赖: WithZero, WithZero.map, valueGroupEquiv
-/
noncomputable def valueGroupOrderIso :
    ValueGroup₀ (.ofClass (valuation K v)) ≃*o
      ValueGroup₀ (.ofClass (Valued.v : Valuation (v.valuation K).Completion Intᵐ⁰)) where
  toFun := WithZero.map' (valueGroupEquiv K v)
  invFun := WithZero.map' (valueGroupEquiv K v).symm
  left_inv x := by match x with | 0 => simp | .coe a => simp
  right_inv y := by match y with | 0 => simp | .coe b => simp
  map_mul' := by simp
  map_le_map_iff' {a b} := by
    match a, b with
    | 0, 0 => simp
    | 0, .coe _ => simp
    | .coe _, 0 => simp
    | .coe a, .coe b => simp [← Subtype.coe_le_coe]

/--
theorem `coe_valueGroupOrderIso_coe` / 定理 `coe_valueGroupOrderIso_coe`

English:
theorem coe_valueGroupOrderIso_coe
  given: (a : valueGroup (.ofClass (valuation K v)))
  proof: by
  simp [valueGroupOrderIso]

中文:
定理 coe_valueGroupOrderIso_coe
  条件: (a : valueGroup (.ofClass (valuation K v)))
  证明: by
  simp [valueGroupOrderIso]
-/
@[simp] theorem coe_valueGroupOrderIso_coe (a : valueGroup (.ofClass (valuation K v))) :
    valueGroupOrderIso K v (a : ValueGroup₀ _) = (valueGroupEquiv K v a : ValueGroup₀ _) := by
  simp [valueGroupOrderIso]

/--
theorem `embedding_valueGroupOrderIso` / 定理 `embedding_valueGroupOrderIso`

English:
theorem embedding_valueGroupOrderIso
  given: (g : ValueGroup₀ (.ofClass (valuation K v)))
  proof: by
  match g with
  | 0 => simp [valueGroupOrderIso]
  | .coe a => simp [coe_valueGroupOrderIso_coe, embedding_apply, coe_valueGroupEquiv]

中文:
定理 embedding_valueGroupOrderIso
  条件: (g : ValueGroup₀ (.ofClass (valuation K v)))
  证明: by
  match g with
  | 0 => simp [valueGroupOrderIso]
  | .coe a => simp [coe_valueGroupOrderIso_coe, embedding_apply, coe_valueGroupEquiv]

Depends on / 依赖: coe_valueGroupEquiv, coe_valueGroupOrderIso_coe, embedding_apply, valueGroupOrderIso
-/
theorem embedding_valueGroupOrderIso (g : ValueGroup₀ (.ofClass (valuation K v))) :
    embedding (valueGroupOrderIso K v g) = embedding g := by
  match g with
  | 0 => simp [valueGroupOrderIso]
  | .coe a => simp [coe_valueGroupOrderIso_coe, embedding_apply, coe_valueGroupEquiv]

/--
theorem `valueGroupOrderIso_restrict` / 定理 `valueGroupOrderIso_restrict`

English:
theorem valueGroupOrderIso_restrict
  given: (x : adicCompletion K v)
  proof: by
  apply embedding_strictMono.injective
  rw [embedding_valueGroupOrderIso]; rw [embedding_restrict]; rw [embedding_restrict]; rfl

中文:
定理 valueGroupOrderIso_restrict
  条件: (x : adicCompletion K v)
  证明: by
  apply embedding_strictMono.injective
  rw [embedding_valueGroupOrderIso]; rw [embedding_restrict]; rw [embedding_restrict]; rfl

Depends on / 依赖: embedding_restrict, embedding_strictMono, embedding_strictMono.injective, embedding_valueGroupOrderIso, injective
-/
theorem valueGroupOrderIso_restrict (x : adicCompletion K v) :
    valueGroupOrderIso K v ((valuation K v).restrict x) =
      Valued.v.restrict (toCompletion x) := by
  apply embedding_strictMono.injective
  rw [embedding_valueGroupOrderIso]; rw [embedding_restrict]; rw [embedding_restrict]; rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Valued (adicCompletion K v) Intᵐ⁰
  body: valuation K v
  is_topological_valuation s := by
    rw [(isUniformInducing_toCompletion K v).isInducing.nhds_eq_comap 0]; rw [toCompletion_zero]; rw [Filter.mem_comap]
    refine ⟨fun ⟨t, ht, hts⟩ => ?_, fun ⟨γ, hγ⟩ => ?_⟩
    · obtain ⟨δ, hδ⟩ := Valued.mem_nhds_zero.1 ht
      refine ⟨Units.mapEqu

中文:
实例 :
  签名: 赋值 (adicCompletion K v) 整数ᵐ⁰
  定义体: valuation K v
  is_topological_valuation s := by
    rw [(isUniformInducing_toCompletion K v).isInducing.nhds_eq_comap 0]; rw [toCompletion_zero]; rw [Filter.mem_comap]
    refine ⟨fun ⟨t, ht, hts⟩ => ?_, fun ⟨γ, hγ⟩ => ?_⟩
    · obtain ⟨δ, hδ⟩ := Valued.mem_nhds_zero.1 ht
      refine ⟨Units.mapEqu

Depends on / 依赖: valuation
-/
noncomputable instance : Valued (adicCompletion K v) Intᵐ⁰ where
  v := valuation K v
  is_topological_valuation s := by
    rw [(isUniformInducing_toCompletion K v).isInducing.nhds_eq_comap 0]; rw [toCompletion_zero]; rw [Filter.mem_comap]
    refine ⟨fun ⟨t, ht, hts⟩ => ?_, fun ⟨γ, hγ⟩ => ?_⟩
    · obtain ⟨δ, hδ⟩ := Valued.mem_nhds_zero.1 ht
      refine ⟨Units.mapEquiv (valueGroupOrderIso K v).symm.toMulEquiv δ, fun x hx => hts (hδ ?_)⟩
      rw [Set.mem_ofPred_eq] at hx ⊢
      simpa [← map_lt_map_iff (valueGroupOrderIso K v), valueGroupOrderIso_restrict] using hx
    · refine ⟨{y | Valued.v.restrict y < ↑(Units.mapEquiv (valueGroupOrderIso K v).toMulEquiv γ)},
        ?_, fun x hx => hγ ?_⟩
      · rw [Valued.mem_nhds_zero]
        exact ⟨Units.mapEquiv (valueGroupOrderIso K v).toMulEquiv γ, subset_rfl⟩
      · rw [Set.mem_ofPred_eq, ← map_lt_map_iff (valueGroupOrderIso K v),
          valueGroupOrderIso_restrict]
        simpa using hx

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CompleteSpace (adicCompletion K v)
  body: ((isUniformInducing_toCompletion K v).completeSpace_congr (toCompletion_surjective K v)).mpr
    inferInstance

中文:
实例 :
  签名: 完备空间 (adicCompletion K v)
  定义体: ((isUniformInducing_toCompletion K v).completeSpace_congr (toCompletion_surjective K v)).mpr
    inferInstance

Depends on / 依赖: completeSpace_congr, isUniformInducing_toCompletion, toCompletion_surjective
-/
noncomputable instance : CompleteSpace (adicCompletion K v) :=
  ((isUniformInducing_toCompletion K v).completeSpace_congr (toCompletion_surjective K v)).mpr
    inferInstance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Coe (WithVal (v.valuation K)) (adicCompletion K v)
  body: ofCompletion (x : (v.valuation K).Completion)

中文:
实例 :
  签名: Coe (WithVal (v.valuation K)) (adicCompletion K v)
  定义体: ofCompletion (x : (v.valuation K).Completion)

Depends on / 依赖: Completion, ofCompletion, v.valuation, valuation
-/
instance : Coe (WithVal (v.valuation K)) (adicCompletion K v) where
  coe x := ofCompletion (x : (v.valuation K).Completion)

/-- Coercion of an element of `K` into the adic completion. -/
instance (priority := 99) : Coe K (adicCompletion K v) where
  coe k := ofCompletion (k : (v.valuation K).Completion)

/--
lemma `coe_toCompletion` / 引理 `coe_toCompletion`

English:
lemma coe_toCompletion
  given: (k : K)
  proof: rfl

中文:
引理 coe_toCompletion
  条件: (k : K)
  证明: rfl
-/
@[simp] lemma coe_toCompletion (k : K) :
    (↑k : adicCompletion K v).toCompletion = (k : (v.valuation K).Completion) := rfl

/--
theorem `valuedAdicCompletion_def` / 定理 `valuedAdicCompletion_def`

English:
theorem valuedAdicCompletion_def
  given: {x : adicCompletion K v}
  proof: rfl

中文:
定理 valuedAdicCompletion_def
  条件: {x : adicCompletion K v}
  证明: rfl
-/
theorem valuedAdicCompletion_def {x : adicCompletion K v} :
    Valued.v x = Valued.extensionValuation x.toCompletion := rfl

/--
theorem `valued_toCompletion` / 定理 `valued_toCompletion`

English:
theorem valued_toCompletion
  given: (x : adicCompletion K v)
  proof: rfl

中文:
定理 valued_toCompletion
  条件: (x : adicCompletion K v)
  证明: rfl
-/
@[simp] theorem valued_toCompletion (x : adicCompletion K v) :
    Valued.v x.toCompletion = Valued.v x := rfl

/--
theorem `valued_ofCompletion` / 定理 `valued_ofCompletion`

English:
theorem valued_ofCompletion
  given: (y : (v.valuation K).Completion)
  proof: rfl

中文:
定理 valued_ofCompletion
  条件: (y : (v.valuation K).完备化)
  证明: rfl
-/
@[simp] theorem valued_ofCompletion (y : (v.valuation K).Completion) :
    Valued.v (ofCompletion y : adicCompletion K v) = Valued.v y := rfl

/--
theorem `valued_coe` / 定理 `valued_coe`

English:
theorem valued_coe
  given: (k : K)
  proof: by
  simp

中文:
定理 valued_coe
  条件: (k : K)
  证明: by
  simp
-/
theorem valued_coe (k : K) :
    Valued.v (↑k : adicCompletion K v) = v.valuation K k := by
  simp

/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: {x y : adicCompletion K v} (h : x.toCompletion = y.toCompletion)
  statement: x = y
  proof: by
  cases x; cases y; exact congrArg ofCompletion h

中文:
定理 ext
  条件: {x y : adicCompletion K v} (h : x.toCompletion = y.toCompletion)
  结论: x = y
  证明: by
  cases x; cases y; exact congrArg ofCompletion h
-/
@[ext] theorem ext {x y : adicCompletion K v} (h : x.toCompletion = y.toCompletion) : x = y := by
  cases x; cases y; exact congrArg ofCompletion h

/--
lemma `coe_zero` / 引理 `coe_zero`

English:
lemma coe_zero
  statement: ((0 : K) : adicCompletion K v) = 0
  proof: by
  apply adicCompletion.ext; simp

中文:
引理 coe_zero
  结论: ((0 : K) : adicCompletion K v) = 0
  证明: by
  apply adicCompletion.ext; simp
-/
@[norm_cast] lemma coe_zero : ((0 : K) : adicCompletion K v) = 0 := by
  apply adicCompletion.ext; simp
/--
lemma `coe_one` / 引理 `coe_one`

English:
lemma coe_one
  statement: ((1 : K) : adicCompletion K v) = 1
  proof: by
  apply adicCompletion.ext; simp

中文:
引理 coe_one
  结论: ((1 : K) : adicCompletion K v) = 1
  证明: by
  apply adicCompletion.ext; simp
-/
@[norm_cast] lemma coe_one : ((1 : K) : adicCompletion K v) = 1 := by
  apply adicCompletion.ext; simp
/--
lemma `coe_add` / 引理 `coe_add`

English:
lemma coe_add
  given: (x y : K)
  proof: by
  apply adicCompletion.ext; simp [UniformSpace.Completion.coe_add]

中文:
引理 coe_add
  条件: (x y : K)
  证明: by
  apply adicCompletion.ext; simp [UniformSpace.Completion.coe_add]
-/
@[norm_cast] lemma coe_add (x y : K) :
    ((x + y : K) : adicCompletion K v) = ↑x + ↑y := by
  apply adicCompletion.ext; simp [UniformSpace.Completion.coe_add]
/--
lemma `coe_mul` / 引理 `coe_mul`

English:
lemma coe_mul
  given: (x y : K)
  proof: by
  apply adicCompletion.ext; simp [UniformSpace.Completion.coe_mul]

中文:
引理 coe_mul
  条件: (x y : K)
  证明: by
  apply adicCompletion.ext; simp [UniformSpace.Completion.coe_mul]
-/
@[norm_cast] lemma coe_mul (x y : K) :
    ((x * y : K) : adicCompletion K v) = ↑x * ↑y := by
  apply adicCompletion.ext; simp [UniformSpace.Completion.coe_mul]

/--
Definition of `uniformEquiv` / `uniformEquiv` 的定义

English:
definition uniformEquiv
  signature: : adicCompletion K v ≃ᵤ (v.valuation K).Completion where
  body: equivCompletion K v
  uniformContinuous_toFun := uniformContinuous_comap
  uniformContinuous_invFun :=
    (isUniformInducing_toCompletion K v).uniformContinuous_iff.mpr uniformContinuous_id

中文:
定义 uniformEquiv
  签名: : adicCompletion K v ≃ᵤ (v.valuation K).完备化 where
  定义体: equivCompletion K v
  uniformContinuous_toFun := uniformContinuous_comap
  uniformContinuous_invFun :=
    (isUniformInducing_toCompletion K v).uniformContinuous_iff.mpr uniformContinuous_id

Depends on / 依赖: equivCompletion
-/
def uniformEquiv : adicCompletion K v ≃ᵤ (v.valuation K).Completion where
  toEquiv := equivCompletion K v
  uniformContinuous_toFun := uniformContinuous_comap
  uniformContinuous_invFun :=
    (isUniformInducing_toCompletion K v).uniformContinuous_iff.mpr uniformContinuous_id

/--
theorem `continuous_toCompletion` / 定理 `continuous_toCompletion`

English:
theorem continuous_toCompletion
  statement: Continuous (toCompletion (K := K) (v := v))
  proof: (uniformEquiv K v).continuous

中文:
定理 continuous_toCompletion
  结论: 连续 (toCompletion (K := K) (v := v))
  证明: (uniformEquiv K v).continuous
-/
theorem continuous_toCompletion : Continuous (toCompletion (K := K) (v := v)) :=
  (uniformEquiv K v).continuous

/--
theorem `continuous_ofCompletion` / 定理 `continuous_ofCompletion`

English:
theorem continuous_ofCompletion
  statement: Continuous (ofCompletion (K := K) (v := v))
  proof: (uniformEquiv K v).symm.continuous

中文:
定理 continuous_ofCompletion
  结论: 连续 (ofCompletion (K := K) (v := v))
  证明: (uniformEquiv K v).symm.continuous
-/
theorem continuous_ofCompletion : Continuous (ofCompletion (K := K) (v := v)) :=
  (uniformEquiv K v).symm.continuous

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: T0Space (adicCompletion K v)
  body: (uniformEquiv K v).toHomeomorph.isEmbedding.t0Space

中文:
实例 :
  签名: T0空间 (adicCompletion K v)
  定义体: (uniformEquiv K v).toHomeomorph.isEmbedding.t0Space

Depends on / 依赖: isEmbedding, t0Space, toHomeomorph, toHomeomorph.isEmbedding.t0Space, uniformEquiv
-/
instance : T0Space (adicCompletion K v) :=
  (uniformEquiv K v).toHomeomorph.isEmbedding.t0Space

end adicCompletion

/--
lemma `valuedAdicCompletion_surjective` / 引理 `valuedAdicCompletion_surjective`

English:
lemma valuedAdicCompletion_surjective
  proof: by
  have h : Function.Surjective (Valued.v : (v.valuation K).Completion -> Intᵐ⁰) :=
Valued.valuedCompletion_surjective_iff.mpr .of_comp (v.valuation_surjective K)
  exact h.comp (adicCompletion.toCompletion_surjective K v)

中文:
引理 valuedAdicCompletion_surjective
  证明: by
  have h : Function.Surjective (Valued.v : (v.valuation K).Completion -> Intᵐ⁰) :=
Valued.valuedCompletion_surjective_iff.mpr .of_comp (v.valuation_surjective K)
  exact h.comp (adicCompletion.toCompletion_surjective K v)

Depends on / 依赖: Completion, Function, Function.Surjective, Surjective, Valued, Valued.v, Valued.valuedCompletion_surjective_iff.mpr, adicCompletion, adicCompletion.toCompletion_surjective, h.comp, of_comp, toCompletion_surjective, v.valuation, v.valuation_surjective, valuation, valuation_surjective, valuedCompletion_surjective_iff
-/
lemma valuedAdicCompletion_surjective :
    Function.Surjective (Valued.v : (v.adicCompletion K) -> Intᵐ⁰) := by
  have h : Function.Surjective (Valued.v : (v.valuation K).Completion -> Intᵐ⁰) :=
Valued.valuedCompletion_surjective_iff.mpr .of_comp (v.valuation_surjective K)
  exact h.comp (adicCompletion.toCompletion_surjective K v)

/--
lemma `adicCompletion_valueGroup_eq` / 引理 `adicCompletion_valueGroup_eq`

English:
lemma adicCompletion_valueGroup_eq
  statement: MonoidWithZeroHom.valueGroup (.ofClass (Valued.v
  proof: by
  ext n
  simp only [MonoidWithZeroHom.mem_valueGroup_iff_of_comm, ne_eq, MonoidWithZeroHom.coe_ofClass]
  refine ⟨fun ⟨a, ha0, x, hx⟩ => ?_, fun ⟨a, ha0, x, hx⟩ =>
    ⟨↑a, by simpa using ha0, ↑x, by simpa using hx⟩⟩
  obtain ⟨b, hb⟩ := valuation_surjective K v (Valued.v a)
  obtain ⟨y, hy⟩ := v

中文:
引理 adicCompletion_valueGroup_eq
  结论: 带零幺半群态射.valueGroup (.ofClass (赋值.v
  证明: by
  ext n
  simp only [MonoidWithZeroHom.mem_valueGroup_iff_of_comm, ne_eq, MonoidWithZeroHom.coe_ofClass]
  refine ⟨fun ⟨a, ha0, x, hx⟩ => ?_, fun ⟨a, ha0, x, hx⟩ =>
    ⟨↑a, by simpa using ha0, ↑x, by simpa using hx⟩⟩
  obtain ⟨b, hb⟩ := valuation_surjective K v (Valued.v a)
  obtain ⟨y, hy⟩ := v

Depends on / 依赖: adicCompletion
-/
lemma adicCompletion_valueGroup_eq : MonoidWithZeroHom.valueGroup (.ofClass (Valued.v
      (R := adicCompletion K v))) =
    MonoidWithZeroHom.valueGroup (.ofClass (valuation K v)) := by
  ext n
  simp only [MonoidWithZeroHom.mem_valueGroup_iff_of_comm, ne_eq, MonoidWithZeroHom.coe_ofClass]
  refine ⟨fun ⟨a, ha0, x, hx⟩ => ?_, fun ⟨a, ha0, x, hx⟩ =>
    ⟨↑a, by simpa using ha0, ↑x, by simpa using hx⟩⟩
  obtain ⟨b, hb⟩ := valuation_surjective K v (Valued.v a)
  obtain ⟨y, hy⟩ := valuation_surjective K v (Valued.v x)
  exact ⟨b, by rw [hb]; exact ha0, y, by rw [hb, hy]; exact hx⟩

/--
Definition of `adicCompletionIntegers` / `adicCompletionIntegers` 的定义

English:
definition adicCompletionIntegers
  signature: : ValuationSubring (v.adicCompletion K)
  body: Valued.v.valuationSubring

中文:
定义 adicCompletion整数egers
  签名: : 赋值子环 (v.adicCompletion K)
  定义体: Valued.v.valuationSubring

Depends on / 依赖: Valued, Valued.v.valuationSubring, valuationSubring
-/
def adicCompletionIntegers : ValuationSubring (v.adicCompletion K) :=
  Valued.v.valuationSubring

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (adicCompletionIntegers K v)
  body: ⟨0⟩

中文:
实例 :
  签名: 可居 (adicCompletion整数egers K v)
  定义体: ⟨0⟩
-/
instance : Inhabited (adicCompletionIntegers K v) :=
  ⟨0⟩

variable (R)

/--
theorem `mem_adicCompletionIntegers` / 定理 `mem_adicCompletionIntegers`

English:
theorem mem_adicCompletionIntegers
  given: {x : v.adicCompletion K}
  proof: Iff.rfl

中文:
定理 mem_adicCompletion整数egers
  条件: {x : v.adicCompletion K}
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_adicCompletionIntegers {x : v.adicCompletion K} :
    x in v.adicCompletionIntegers K ↔ Valued.v x <= 1 :=
  Iff.rfl

/--
theorem `notMem_adicCompletionIntegers` / 定理 `notMem_adicCompletionIntegers`

English:
theorem notMem_adicCompletionIntegers
  given: {x : v.adicCompletion K}
  proof: by
  rw [not_congr <| mem_adicCompletionIntegers R K v]
  exact not_le

中文:
定理 notMem_adicCompletion整数egers
  条件: {x : v.adicCompletion K}
  证明: by
  rw [not_congr <| mem_adicCompletionIntegers R K v]
  exact not_le

Depends on / 依赖: mem_adicCompletionIntegers, not_congr, not_le
-/
theorem notMem_adicCompletionIntegers {x : v.adicCompletion K} :
    x ∉ v.adicCompletionIntegers K ↔ 1 < Valued.v x := by
  rw [not_congr <| mem_adicCompletionIntegers R K v]
  exact not_le

section AlgebraInstances

instance (priority := 100) adicValued.has_uniform_continuous_const_smul' :
    UniformContinuousConstSMul R (WithVal <| v.valuation K) :=
  uniformContinuousConstSMul_of_continuousConstSMul R (WithVal <| v.valuation K)

section Algebra
variable [Algebra S K]

/--
Instance `adicValued.uniformContinuousConstSMul` / 实例 `adicValued.uniformContinuousConstSMul`

English:
instance adicValued.uniformContinuousConstSMul
  signature: :
  body: by
  refine ⟨fun l => ?_⟩
  simp_rw [WithVal.smul_right_def, Algebra.smul_def]
  exact (Ring.uniformContinuousConstSMul (WithVal <| v.valuation K)).uniformContinuous_const_smul _

中文:
实例 adicValued.uniformContinuousConstSMul
  签名: :
  定义体: by
  refine ⟨fun l => ?_⟩
  simp_rw [WithVal.smul_right_def, Algebra.smul_def]
  exact (Ring.uniformContinuousConstSMul (WithVal <| v.valuation K)).uniformContinuous_const_smul _

Depends on / 依赖: Algebra, Algebra.smul_def, Ring.uniformContinuousConstSMul, WithVal, WithVal.smul_right_def, simp_rw, smul_def, smul_right_def, uniformContinuousConstSMul, uniformContinuous_const_smul, v.valuation, valuation
-/
instance adicValued.uniformContinuousConstSMul :
    UniformContinuousConstSMul S (WithVal <| v.valuation K) := by
  refine ⟨fun l => ?_⟩
  simp_rw [WithVal.smul_right_def, Algebra.smul_def]
  exact (Ring.uniformContinuousConstSMul (WithVal <| v.valuation K)).uniformContinuous_const_smul _

open UniformSpace in
/--
Instance `instAlgebraCompletion` / 实例 `instAlgebraCompletion`

English:
instance instAlgebraCompletion
  signature: : Algebra S ((v.valuation K).Completion) where
  body: Completion.instSMul _ _
  algebraMap := Completion.coeRingHom.comp (algebraMap S (WithVal (v.valuation K)))
  commutes' r x := by
    induction x using Completion.induction_on with
    | hp =>
      exact isClosed_eq (continuous_const_mul _) (continuous_mul_const _)
    | ih x => rw [mul_comm]
  smu

中文:
实例 instAlgebraCompletion
  签名: : 代数 S ((v.valuation K).完备化) where
  定义体: Completion.instSMul _ _
  algebraMap := Completion.coeRingHom.comp (algebraMap S (WithVal (v.valuation K)))
  commutes' r x := by
    induction x using Completion.induction_on with
    | hp =>
      exact isClosed_eq (continuous_const_mul _) (continuous_mul_const _)
    | ih x => rw [mul_comm]
  smu

Depends on / 依赖: Completion, Completion.instSMul, instSMul
-/
noncomputable instance instAlgebraCompletion : Algebra S ((v.valuation K).Completion) where
  toSMul := Completion.instSMul _ _
  algebraMap := Completion.coeRingHom.comp (algebraMap S (WithVal (v.valuation K)))
  commutes' r x := by
    induction x using Completion.induction_on with
    | hp =>
      exact isClosed_eq (continuous_const_mul _) (continuous_mul_const _)
    | ih x => rw [mul_comm]
  smul_def' r x := by
    induction x using Completion.induction_on with
    | hp =>
      exact isClosed_eq (continuous_const_smul _) (continuous_const_mul _)
    | ih x =>
      simp [Algebra.smul_def, Completion.algebraMap_def, WithVal.algebraMap_right_apply,
        Completion.coeRingHom]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Algebra S (v.adicCompletion K)
  body: fast_instance% (adicCompletion.equivCompletion K v).algebra S

中文:
实例 :
  签名: 代数 S (v.adicCompletion K)
  定义体: fast_instance% (adicCompletion.equivCompletion K v).algebra S

Depends on / 依赖: adicCompletion, adicCompletion.equivCompletion, algebra, equivCompletion, fast_instance
-/
noncomputable instance : Algebra S (v.adicCompletion K) :=
  fast_instance% (adicCompletion.equivCompletion K v).algebra S

/--
theorem `algebraMap_adicCompletion_toCompletion` / 定理 `algebraMap_adicCompletion_toCompletion`

English:
theorem algebraMap_adicCompletion_toCompletion
  given: (r : S)
  proof: rfl

中文:
定理 algebraMap_adicCompletion_toCompletion
  条件: (r : S)
  证明: rfl
-/
theorem algebraMap_adicCompletion_toCompletion (r : S) :
    (algebraMap S (v.adicCompletion K) r).toCompletion =
      algebraMap S ((v.valuation K).Completion) r := rfl

instance {S₀ : Type*} [CommSemiring S₀] [Algebra S₀ S] [Algebra S₀ K] [IsScalarTower S₀ S K] :
    IsScalarTower S₀ S ((v.valuation K).Completion) :=
  .of_algebraMap_eq fun x => by
    exact congrArg (UniformSpace.Completion.coeRingHom (α := WithVal (v.valuation K)))
      (IsScalarTower.algebraMap_apply S₀ S (WithVal (v.valuation K)) x)

instance {S₀ : Type*} [CommSemiring S₀] [Algebra S₀ S] [Algebra S₀ K] [IsScalarTower S₀ S K] :
    IsScalarTower S₀ S (v.adicCompletion K) :=
  .of_algebraMap_eq fun x => by
    apply adicCompletion.ext
    rw [algebraMap_adicCompletion_toCompletion]; rw [algebraMap_adicCompletion_toCompletion]; rw [IsScalarTower.algebraMap_apply S₀ S ((v.valuation K).Completion)]

/--
theorem `coe_smul_adicCompletion` / 定理 `coe_smul_adicCompletion`

English:
theorem coe_smul_adicCompletion
  given: (r : S) (x : WithVal (v.valuation K))
  proof: by
  apply adicCompletion.ext
  exact UniformSpace.Completion.coe_smul r x

中文:
定理 coe_smul_adicCompletion
  条件: (r : S) (x : WithVal (v.valuation K))
  证明: by
  apply adicCompletion.ext
  exact UniformSpace.Completion.coe_smul r x

Depends on / 依赖: Completion, UniformSpace, UniformSpace.Completion.coe_smul, adicCompletion, adicCompletion.ext, coe_smul
-/
theorem coe_smul_adicCompletion (r : S) (x : WithVal (v.valuation K)) :
    (↑(r • x) : v.adicCompletion K) = r • (↑x : v.adicCompletion K) := by
  apply adicCompletion.ext
  exact UniformSpace.Completion.coe_smul r x

/--
theorem `algebraMap_adicCompletion` / 定理 `algebraMap_adicCompletion`

English:
theorem algebraMap_adicCompletion
  statement: ⇑(algebraMap S <| v.adicCompletion K) = (↑) ∘ algebraMap S K
  proof: rfl

中文:
定理 algebraMap_adicCompletion
  结论: ⇑(algebraMap S <| v.adicCompletion K) = (↑) ∘ algebraMap S K
  证明: rfl
-/
theorem algebraMap_adicCompletion : ⇑(algebraMap S <| v.adicCompletion K) = (↑) ∘ algebraMap S K :=
  rfl

variable {R} in
/--
theorem `denseRange_algebraMap` / 定理 `denseRange_algebraMap`

English:
theorem denseRange_algebraMap
  statement: DenseRange (algebraMap K (v.adicCompletion K))
  proof: by
  rw [algebraMap_adicCompletion]
  exact (adicCompletion.ofCompletion_surjective K v).denseRange.comp
    (UniformSpace.Completion.denseRange_coe.comp (WithVal.equiv _).symm.surjective.denseRange
      (UniformSpace.Completion.continuous_coe _))
    (adicCompletion.continuous_ofCompletion K v)

中文:
定理 denseRange_algebraMap
  结论: DenseRange (algebraMap K (v.adicCompletion K))
  证明: by
  rw [algebraMap_adicCompletion]
  exact (adicCompletion.ofCompletion_surjective K v).denseRange.comp
    (UniformSpace.Completion.denseRange_coe.comp (WithVal.equiv _).symm.surjective.denseRange
      (UniformSpace.Completion.continuous_coe _))
    (adicCompletion.continuous_ofCompletion K v)

Depends on / 依赖: Completion, UniformSpace, UniformSpace.Completion.continuous_coe, UniformSpace.Completion.denseRange_coe.comp, WithVal, WithVal.equiv, adicCompletion, adicCompletion.continuous_ofCompletion, adicCompletion.ofCompletion_surjective, algebraMap_adicCompletion, continuous_coe, continuous_ofCompletion, denseRange, denseRange.comp, denseRange_coe, ofCompletion_surjective, surjective, symm.surjective.denseRange
-/
theorem denseRange_algebraMap : DenseRange (algebraMap K (v.adicCompletion K)) := by
  rw [algebraMap_adicCompletion]
  exact (adicCompletion.ofCompletion_surjective K v).denseRange.comp
    (UniformSpace.Completion.denseRange_coe.comp (WithVal.equiv _).symm.surjective.denseRange
      (UniformSpace.Completion.continuous_coe _))
    (adicCompletion.continuous_ofCompletion K v)

end Algebra

/--
theorem `coe_algebraMap_mem` / 定理 `coe_algebraMap_mem`

English:
theorem coe_algebraMap_mem
  given: (r : R)
  statement: ↑((algebraMap R K) r) in adicCompletionIntegers K v
  proof: by
  rw [mem_adicCompletionIntegers]
  change Valued.v (↑((algebraMap R K) r) : adicCompletion K v).toCompletion <= 1
  rw [Valued.valuedCompletion_apply]
  simpa using v.valuation_le_one _

中文:
定理 coe_algebraMap_mem
  条件: (r : R)
  结论: ↑((algebraMap R K) r) in adicCompletion整数egers K v
  证明: by
  rw [mem_adicCompletionIntegers]
  change Valued.v (↑((algebraMap R K) r) : adicCompletion K v).toCompletion <= 1
  rw [Valued.valuedCompletion_apply]
  simpa using v.valuation_le_one _

Depends on / 依赖: Valued, Valued.v, Valued.valuedCompletion_apply, adicCompletion, algebraMap, mem_adicCompletionIntegers, toCompletion, v.valuation_le_one, valuation_le_one, valuedCompletion_apply
-/
theorem coe_algebraMap_mem (r : R) : ↑((algebraMap R K) r) in adicCompletionIntegers K v := by
  rw [mem_adicCompletionIntegers]
  change Valued.v (↑((algebraMap R K) r) : adicCompletion K v).toCompletion <= 1
  rw [Valued.valuedCompletion_apply]
  simpa using v.valuation_le_one _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Algebra R (v.adicCompletionIntegers K)
  body: ⟨r • (x : v.adicCompletion K), by
      rw [Algebra.smul_def]
      refine ValuationSubring.mul_mem _ _ _ ?_ x.2
      rw [algebraMap_adicCompletion]
      exact coe_algebraMap_mem _ _ v r⟩
  algebraMap :=
  { toFun r :=
      ⟨(algebraMap R K r : adicCompletion K v), coe_algebraMap_mem _ _ v r⟩
   

中文:
实例 :
  签名: 代数 R (v.adicCompletion整数egers K)
  定义体: ⟨r • (x : v.adicCompletion K), by
      rw [Algebra.smul_def]
      refine ValuationSubring.mul_mem _ _ _ ?_ x.2
      rw [algebraMap_adicCompletion]
      exact coe_algebraMap_mem _ _ v r⟩
  algebraMap :=
  { toFun r :=
      ⟨(algebraMap R K r : adicCompletion K v), coe_algebraMap_mem _ _ v r⟩
   

Depends on / 依赖: Algebra, Algebra.smul_def, Completion, UniformSpace, UniformSpace.Completion.coe_add, UniformSpace.Completion.coe_mul, ValuationSubring, ValuationSubring.mul_mem, adicCompletion, algebraMap, algebraMap_adicCompletion, coe_add, coe_algebraMap_mem, coe_mul, commutes, map_add, map_mul, map_one, map_zero, mul_comm
-/
instance : Algebra R (v.adicCompletionIntegers K) where
  smul r x :=
    ⟨r • (x : v.adicCompletion K), by
      rw [Algebra.smul_def]
      refine ValuationSubring.mul_mem _ _ _ ?_ x.2
      rw [algebraMap_adicCompletion]
      exact coe_algebraMap_mem _ _ v r⟩
  algebraMap :=
  { toFun r :=
      ⟨(algebraMap R K r : adicCompletion K v), coe_algebraMap_mem _ _ v r⟩
    map_one' := by ext; simp
    map_mul' x y := by
      ext
      simp [map_mul, UniformSpace.Completion.coe_mul]
    map_zero' := by ext; simp
    map_add' x y := by
      ext
      simp [map_add, UniformSpace.Completion.coe_add] }
  commutes' r x := by
    rw [mul_comm]
  smul_def' r x := by
    ext
    simp +instances only [Algebra.smul_def]
    rfl

@[simp]
/--
lemma `algebraMap_adicCompletionIntegers_apply` / 引理 `algebraMap_adicCompletionIntegers_apply`

English:
lemma algebraMap_adicCompletionIntegers_apply
  given: (r : R)
  proof: by
  rfl

中文:
引理 algebraMap_adicCompletion整数egers_apply
  条件: (r : R)
  证明: by
  rfl
-/
lemma algebraMap_adicCompletionIntegers_apply (r : R) :
    algebraMap R (v.adicCompletionIntegers K) r = (algebraMap R K r : v.adicCompletion K) := by
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [FaithfulSMul
  signature: R K] : FaithfulSMul R (v.adicCompletionIntegers K)
  body: by
  rw [faithfulSMul_iff_algebraMap_injective]
  intro x y
  rw [Subtype.ext_iff]
  simp

中文:
实例 [忠实标量乘法
  签名: R K] : 忠实标量乘法 R (v.adicCompletion整数egers K)
  定义体: by
  rw [faithfulSMul_iff_algebraMap_injective]
  intro x y
  rw [Subtype.ext_iff]
  simp

Depends on / 依赖: Subtype, Subtype.ext_iff, ext_iff, faithfulSMul_iff_algebraMap_injective
-/
instance [FaithfulSMul R K] : FaithfulSMul R (v.adicCompletionIntegers K) := by
  rw [faithfulSMul_iff_algebraMap_injective]
  intro x y
  rw [Subtype.ext_iff]
  simp

variable {R K} in
open scoped algebraMap in -- to make the coercions from `R` fire
/--
theorem `valuedAdicCompletion_eq_valuation` / 定理 `valuedAdicCompletion_eq_valuation`

English:
theorem valuedAdicCompletion_eq_valuation
  given: (r : R)
  proof: by
  rw [← adicCompletion.valued_toCompletion]
  exact Valued.valuedCompletion_apply _

中文:
定理 valuedAdicCompletion_eq_valuation
  条件: (r : R)
  证明: by
  rw [← adicCompletion.valued_toCompletion]
  exact Valued.valuedCompletion_apply _

Depends on / 依赖: Valued, Valued.valuedCompletion_apply, adicCompletion, adicCompletion.valued_toCompletion, valuedCompletion_apply, valued_toCompletion
-/
theorem valuedAdicCompletion_eq_valuation (r : R) :
    Valued.v (r : v.adicCompletion K) = v.valuation K r := by
  rw [← adicCompletion.valued_toCompletion]
  exact Valued.valuedCompletion_apply _

variable {R K} in
/--
theorem `valuedAdicCompletion_eq_valuation'` / 定理 `valuedAdicCompletion_eq_valuation'`

English:
theorem valuedAdicCompletion_eq_valuation'
  given: (k : K)
  proof: by
  rw [← adicCompletion.valued_toCompletion]
  exact Valued.valuedCompletion_apply _

中文:
定理 valuedAdicCompletion_eq_valuation'
  条件: (k : K)
  证明: by
  rw [← adicCompletion.valued_toCompletion]
  exact Valued.valuedCompletion_apply _

Depends on / 依赖: Valued, Valued.valuedCompletion_apply, adicCompletion, adicCompletion.valued_toCompletion, valuedCompletion_apply, valued_toCompletion
-/
theorem valuedAdicCompletion_eq_valuation' (k : K) :
    Valued.v (k : v.adicCompletion K) = v.valuation K k := by
  rw [← adicCompletion.valued_toCompletion]
  exact Valued.valuedCompletion_apply _

variable {R K} in
open scoped algebraMap in -- to make the coercion from `R` fire
/--
lemma `coe_mem_adicCompletionIntegers` / 引理 `coe_mem_adicCompletionIntegers`

English:
lemma coe_mem_adicCompletionIntegers
  given: (r : R)
  proof: by
  rw [mem_adicCompletionIntegers]; rw [valuedAdicCompletion_eq_valuation]
  exact valuation_le_one v r

@[simp]

中文:
引理 coe_mem_adicCompletion整数egers
  条件: (r : R)
  证明: by
  rw [mem_adicCompletionIntegers]; rw [valuedAdicCompletion_eq_valuation]
  exact valuation_le_one v r

@[simp]

Depends on / 依赖: mem_adicCompletionIntegers, valuation_le_one, valuedAdicCompletion_eq_valuation
-/
lemma coe_mem_adicCompletionIntegers (r : R) :
    (r : adicCompletion K v) in adicCompletionIntegers K v := by
  rw [mem_adicCompletionIntegers]; rw [valuedAdicCompletion_eq_valuation]
  exact valuation_le_one v r

@[simp]
/--
theorem `coe_smul_adicCompletionIntegers` / 定理 `coe_smul_adicCompletionIntegers`

English:
theorem coe_smul_adicCompletionIntegers
  given: (r : R) (x : v.adicCompletionIntegers K)
  proof: rfl

中文:
定理 coe_smul_adicCompletion整数egers
  条件: (r : R) (x : v.adicCompletion整数egers K)
  证明: rfl
-/
theorem coe_smul_adicCompletionIntegers (r : R) (x : v.adicCompletionIntegers K) :
    (↑(r • x) : v.adicCompletion K) = r • (x : v.adicCompletion K) :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Module.IsTorsionFree R (v.adicCompletionIntegers K)
  body: .of_smul_eq_zero by simp

中文:
实例 :
  签名: 模.是无挠 R (v.adicCompletion整数egers K)
  定义体: .of_smul_eq_zero by simp

Depends on / 依赖: of_smul_eq_zero
-/
instance : Module.IsTorsionFree R (v.adicCompletionIntegers K) := .of_smul_eq_zero by simp

/--
Instance `adicCompletion.instIsScalarTower'` / 实例 `adicCompletion.instIsScalarTower'`

English:
instance adicCompletion.instIsScalarTower'
  signature: :
  body: by simp only [Algebra.smul_def]; apply mul_assoc

中文:
实例 adicCompletion.instIsScalarTower'
  签名: :
  定义体: by simp only [Algebra.smul_def]; apply mul_assoc

Depends on / 依赖: Algebra, Algebra.smul_def, mul_assoc, smul_def
-/
instance adicCompletion.instIsScalarTower' :
    IsScalarTower R (v.adicCompletionIntegers K) (v.adicCompletion K) where
  smul_assoc x y z := by simp only [Algebra.smul_def]; apply mul_assoc

end AlgebraInstances

variable {R}

open nonZeroDivisors algebraMap in
variable {K} in
/--
lemma `adicCompletion.mul_nonZeroDivisor_mem_adicCompletionIntegers` / 引理 `adicCompletion.mul_nonZeroDivisor_mem_adicCompletionIntegers`

English:
lemma adicCompletion.mul_nonZeroDivisor_mem_adicCompletionIntegers
  statement: (v : HeightOneSpectrum R)
  proof: by
  by_cases ha : a in v.adicCompletionIntegers K
  · use 1
    simp [ha]
  · rw [notMem_adicCompletionIntegers] at ha
    -- let ϖ be a uniformiser
    obtain ⟨ϖ, hϖ⟩ := intValuation_exists_uniformizer v
    have : Valued.v (algebraMap R (v.adicCompletion K) ϖ) = (exp (1 : Int))⁻¹ := by
      simp

中文:
引理 adicCompletion.mul_nonZeroDivisor_mem_adicCompletion整数egers
  结论: (v : 高一谱 R)
  证明: by
  by_cases ha : a in v.adicCompletionIntegers K
  · use 1
    simp [ha]
  · rw [notMem_adicCompletionIntegers] at ha
    -- let ϖ be a uniformiser
    obtain ⟨ϖ, hϖ⟩ := intValuation_exists_uniformizer v
    have : Valued.v (algebraMap R (v.adicCompletion K) ϖ) = (exp (1 : Int))⁻¹ := by
      simp

Depends on / 依赖: adicCompletionIntegers, notMem_adicCompletionIntegers, v.adicCompletionIntegers
-/
lemma adicCompletion.mul_nonZeroDivisor_mem_adicCompletionIntegers (v : HeightOneSpectrum R)
    (a : v.adicCompletion K) : exists b in R⁰, a * b in v.adicCompletionIntegers K := by
  by_cases ha : a in v.adicCompletionIntegers K
  · use 1
    simp [ha]
  · rw [notMem_adicCompletionIntegers] at ha
    -- let ϖ be a uniformiser
    obtain ⟨ϖ, hϖ⟩ := intValuation_exists_uniformizer v
    have : Valued.v (algebraMap R (v.adicCompletion K) ϖ) = (exp (1 : Int))⁻¹ := by
      simp [valuedAdicCompletion_eq_valuation, valuation_of_algebraMap, hϖ, exp]
    have hϖ0 : ϖ != 0 := by rintro rfl; simp [exp_ne_zero.symm] at hϖ
    refine ⟨ϖ^(log (Valued.v a)).natAbs, pow_mem (mem_nonZeroDivisors_of_ne_zero hϖ0) _, ?_⟩
    -- now manually translate the goal (an inequality in ℤᵐ⁰) to an inequality of "log" of ℤ
    simp only [map_pow, mem_adicCompletionIntegers, map_mul, this, inv_pow, ← exp_nsmul, nsmul_one,
      Int.natCast_natAbs]
    exact mul_inv_le_one_of_le₀ (le_exp_log.trans (by simp [le_abs_self])) zero_le

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: FaithfulSMul (v.adicCompletionIntegers K) (v.adicCompletion K)
  body: Subsemiring.faithfulSMul _

中文:
实例 :
  签名: 忠实标量乘法 (v.adicCompletion整数egers K) (v.adicCompletion K)
  定义体: Subsemiring.faithfulSMul _

Depends on / 依赖: Subsemiring, Subsemiring.faithfulSMul, faithfulSMul
-/
instance : FaithfulSMul (v.adicCompletionIntegers K) (v.adicCompletion K) :=
  Subsemiring.faithfulSMul _

/--
theorem `adicCompletionIntegers.integers` / 定理 `adicCompletionIntegers.integers`

English:
theorem adicCompletionIntegers.integers
  proof: FaithfulSMul.algebraMap_injective _ _
  map_le_one := by simp [mem_adicCompletionIntegers]
  exists_of_le_one := by simp [mem_adicCompletionIntegers]

中文:
定理 adicCompletion整数egers.integers
  证明: FaithfulSMul.algebraMap_injective _ _
  map_le_one := by simp [mem_adicCompletionIntegers]
  exists_of_le_one := by simp [mem_adicCompletionIntegers]

Depends on / 依赖: FaithfulSMul, FaithfulSMul.algebraMap_injective, algebraMap_injective
-/
theorem adicCompletionIntegers.integers :
    (Valued.v : Valuation (v.adicCompletion K) Intᵐ⁰).Integers ↥(adicCompletionIntegers K v) where
  hom_inj := FaithfulSMul.algebraMap_injective _ _
  map_le_one := by simp [mem_adicCompletionIntegers]
  exists_of_le_one := by simp [mem_adicCompletionIntegers]

variable {K v}

/--
theorem `adicCompletionIntegers.isUnit_iff_valued_eq_one` / 定理 `adicCompletionIntegers.isUnit_iff_valued_eq_one`

English:
theorem adicCompletionIntegers.isUnit_iff_valued_eq_one
  given: {a : v.adicCompletionIntegers K}
  proof: by
  simp [Valuation.Integers.isUnit_iff_valuation_eq_one (integers K v)]

中文:
定理 adicCompletion整数egers.isUnit_iff_valued_eq_one
  条件: {a : v.adicCompletion整数egers K}
  证明: by
  simp [Valuation.Integers.isUnit_iff_valuation_eq_one (integers K v)]

Depends on / 依赖: Integers, Valuation, Valuation.Integers.isUnit_iff_valuation_eq_one, integers, isUnit_iff_valuation_eq_one
-/
theorem adicCompletionIntegers.isUnit_iff_valued_eq_one {a : v.adicCompletionIntegers K} :
    IsUnit a ↔ Valued.v a.1 = 1 := by
  simp [Valuation.Integers.isUnit_iff_valuation_eq_one (integers K v)]

/--
theorem `adicCompletionIntegers.mem_units_iff_valued_eq_one` / 定理 `adicCompletionIntegers.mem_units_iff_valued_eq_one`

English:
theorem adicCompletionIntegers.mem_units_iff_valued_eq_one
  given: {a : (v.adicCompletion K)ˣ}
  proof: by
  refine ⟨fun h => ?_, fun h =>
     ⟨h.le, by simp [mem_adicCompletionIntegers, inv_le_one_iff₀, h.symm.le]⟩⟩
  convert! isUnit_iff_valued_eq_one.1 (Submonoid.unitsEquivIsUnitSubmonoid _ ⟨_, h⟩).2

中文:
定理 adicCompletion整数egers.mem_units_iff_valued_eq_one
  条件: {a : (v.adicCompletion K)ˣ}
  证明: by
  refine ⟨fun h => ?_, fun h =>
     ⟨h.le, by simp [mem_adicCompletionIntegers, inv_le_one_iff₀, h.symm.le]⟩⟩
  convert! isUnit_iff_valued_eq_one.1 (Submonoid.unitsEquivIsUnitSubmonoid _ ⟨_, h⟩).2

Depends on / 依赖: Submonoid, Submonoid.unitsEquivIsUnitSubmonoid, convert, h.le, h.symm.le, isUnit_iff_valued_eq_one, mem_adicCompletionIntegers, unitsEquivIsUnitSubmonoid
-/
theorem adicCompletionIntegers.mem_units_iff_valued_eq_one {a : (v.adicCompletion K)ˣ} :
    a in (v.adicCompletionIntegers K).units ↔ Valued.v a.1 = 1 := by
  refine ⟨fun h => ?_, fun h =>
     ⟨h.le, by simp [mem_adicCompletionIntegers, inv_le_one_iff₀, h.symm.le]⟩⟩
  convert! isUnit_iff_valued_eq_one.1 (Submonoid.unitsEquivIsUnitSubmonoid _ ⟨_, h⟩).2

section AbsoluteValue

open WithZeroMulInt NNReal

variable (v) {b : Real>=0} (hb : 1 < b) (r : R) (x : K)

/--
Definition of `intAdicAbvDef` / `intAdicAbvDef` 的定义

English:
definition intAdicAbvDef
  signature: (r : R)
  body: toNNReal (ne_zero_of_lt hb) (v.intValuation r)

中文:
定义 intAdicAbvDef
  签名: (r : R)
  定义体: toNNReal (ne_zero_of_lt hb) (v.intValuation r)

Depends on / 依赖: intValuation, ne_zero_of_lt, toNNReal, v.intValuation
-/
def intAdicAbvDef (r : R) : Real>=0 := toNNReal (ne_zero_of_lt hb) (v.intValuation r)

/--
lemma `isNonarchimedean_intAdicAbvDef` / 引理 `isNonarchimedean_intAdicAbvDef`

English:
lemma isNonarchimedean_intAdicAbvDef
  statement: IsNonarchimedean (v.intAdicAbvDef hb)
  proof: by
  intro x y
  simp only [intAdicAbvDef]
  have h_mono := (toNNReal_strictMono hb).monotone
  rw [← h_mono.map_max]
exact h_mono v.intValuation.map_add x y

中文:
引理 isNonarchimedean_intAdicAbvDef
  结论: IsNonarchimedean (v.intAdicAbvDef hb)
  证明: by
  intro x y
  simp only [intAdicAbvDef]
  have h_mono := (toNNReal_strictMono hb).monotone
  rw [← h_mono.map_max]
exact h_mono v.intValuation.map_add x y

Depends on / 依赖: h_mono, h_mono.map_max, intAdicAbvDef, intValuation, map_add, map_max, monotone, toNNReal_strictMono, v.intValuation.map_add
-/
lemma isNonarchimedean_intAdicAbvDef : IsNonarchimedean (v.intAdicAbvDef hb) := by
  intro x y
  simp only [intAdicAbvDef]
  have h_mono := (toNNReal_strictMono hb).monotone
  rw [← h_mono.map_max]
exact h_mono v.intValuation.map_add x y

/--
Definition of `intAdicAbv` / `intAdicAbv` 的定义

English:
definition intAdicAbv
  signature: : AbsoluteValue R Real where
  body: v.intAdicAbvDef hb r
  map_mul' _ _ := by simp [intAdicAbvDef]
  nonneg' _ := zero_le_coe
  eq_zero' _ := by simp [intAdicAbvDef, intValuation_def]
  add_le' _ _ := (isNonarchimedean_intAdicAbvDef v hb).add_le fun _ => bot_le

中文:
定义 intAdicAbv
  签名: : 绝对值 R 实数 where
  定义体: v.intAdicAbvDef hb r
  map_mul' _ _ := by simp [intAdicAbvDef]
  nonneg' _ := zero_le_coe
  eq_zero' _ := by simp [intAdicAbvDef, intValuation_def]
  add_le' _ _ := (isNonarchimedean_intAdicAbvDef v hb).add_le fun _ => bot_le

Depends on / 依赖: intAdicAbvDef, v.intAdicAbvDef
-/
def intAdicAbv : AbsoluteValue R Real where
  toFun r := v.intAdicAbvDef hb r
  map_mul' _ _ := by simp [intAdicAbvDef]
  nonneg' _ := zero_le_coe
  eq_zero' _ := by simp [intAdicAbvDef, intValuation_def]
  add_le' _ _ := (isNonarchimedean_intAdicAbvDef v hb).add_le fun _ => bot_le

/--
theorem `isNonarchimedean_intAdicAbv` / 定理 `isNonarchimedean_intAdicAbv`

English:
theorem isNonarchimedean_intAdicAbv
  statement: IsNonarchimedean (v.intAdicAbv hb)
  proof: isNonarchimedean_intAdicAbvDef v hb

中文:
定理 isNonarchimedean_intAdicAbv
  结论: IsNonarchimedean (v.intAdicAbv hb)
  证明: isNonarchimedean_intAdicAbvDef v hb

Depends on / 依赖: isNonarchimedean_intAdicAbvDef
-/
theorem isNonarchimedean_intAdicAbv : IsNonarchimedean (v.intAdicAbv hb) :=
  isNonarchimedean_intAdicAbvDef v hb

/--
theorem `intAdicAbv_le_one` / 定理 `intAdicAbv_le_one`

English:
theorem intAdicAbv_le_one
  statement: v.intAdicAbv hb r <= 1
  proof: by
  simpa [intAdicAbv, intAdicAbvDef, toNNReal_le_one_iff hb] using intValuation_le_one v r

中文:
定理 intAdicAbv_le_one
  结论: v.intAdicAbv hb r <= 1
  证明: by
  simpa [intAdicAbv, intAdicAbvDef, toNNReal_le_one_iff hb] using intValuation_le_one v r

Depends on / 依赖: intAdicAbv, intAdicAbvDef, intValuation_le_one, toNNReal_le_one_iff
-/
theorem intAdicAbv_le_one : v.intAdicAbv hb r <= 1 := by
  simpa [intAdicAbv, intAdicAbvDef, toNNReal_le_one_iff hb] using intValuation_le_one v r

/--
theorem `intAdicAbv_lt_one_iff` / 定理 `intAdicAbv_lt_one_iff`

English:
theorem intAdicAbv_lt_one_iff
  statement: v.intAdicAbv hb r < 1 ↔ r in v.asIdeal
  proof: by
  simpa [intAdicAbv, intAdicAbvDef, toNNReal_lt_one_iff hb] using intValuation_lt_one_iff_mem v r

中文:
定理 intAdicAbv_lt_one_iff
  结论: v.intAdicAbv hb r < 1 ↔ r in v.asIdeal
  证明: by
  simpa [intAdicAbv, intAdicAbvDef, toNNReal_lt_one_iff hb] using intValuation_lt_one_iff_mem v r

Depends on / 依赖: intAdicAbv, intAdicAbvDef, intValuation_lt_one_iff_mem, toNNReal_lt_one_iff
-/
theorem intAdicAbv_lt_one_iff : v.intAdicAbv hb r < 1 ↔ r in v.asIdeal := by
  simpa [intAdicAbv, intAdicAbvDef, toNNReal_lt_one_iff hb] using intValuation_lt_one_iff_mem v r

/--
theorem `intAdicAbv_eq_one_iff` / 定理 `intAdicAbv_eq_one_iff`

English:
theorem intAdicAbv_eq_one_iff
  statement: v.intAdicAbv hb r = 1 ↔ r ∉ v.asIdeal
  proof: by
  contrapose
  rw [← v.intAdicAbv_lt_one_iff hb]; rw [ne_iff_lt_iff_le]
  exact intAdicAbv_le_one v hb r

中文:
定理 intAdicAbv_eq_one_iff
  结论: v.intAdicAbv hb r = 1 ↔ r ∉ v.asIdeal
  证明: by
  contrapose
  rw [← v.intAdicAbv_lt_one_iff hb]; rw [ne_iff_lt_iff_le]
  exact intAdicAbv_le_one v hb r

Depends on / 依赖: contrapose, intAdicAbv_le_one, intAdicAbv_lt_one_iff, ne_iff_lt_iff_le, v.intAdicAbv_lt_one_iff
-/
theorem intAdicAbv_eq_one_iff : v.intAdicAbv hb r = 1 ↔ r ∉ v.asIdeal := by
  contrapose
  rw [← v.intAdicAbv_lt_one_iff hb]; rw [ne_iff_lt_iff_le]
  exact intAdicAbv_le_one v hb r

/--
Definition of `adicAbvDef` / `adicAbvDef` 的定义

English:
definition adicAbvDef
  signature: (x : K)
  body: toNNReal (ne_zero_of_lt hb) (v.valuation K x)

中文:
定义 adicAbvDef
  签名: (x : K)
  定义体: toNNReal (ne_zero_of_lt hb) (v.valuation K x)

Depends on / 依赖: ne_zero_of_lt, toNNReal, v.valuation, valuation
-/
def adicAbvDef (x : K) : Real>=0 := toNNReal (ne_zero_of_lt hb) (v.valuation K x)

/--
lemma `isNonarchimedean_adicAbvDef` / 引理 `isNonarchimedean_adicAbvDef`

English:
lemma isNonarchimedean_adicAbvDef
  statement: IsNonarchimedean (α := K) (v.adicAbvDef hb)
  proof: by
  intro x y
  simp only [adicAbvDef]
  have h_mono := (toNNReal_strictMono hb).monotone
  rw [← h_mono.map_max]
  exact h_mono ((v.valuation _).map_add x y)

中文:
引理 isNonarchimedean_adicAbvDef
  结论: IsNonarchimedean (α := K) (v.adicAbvDef hb)
  证明: by
  intro x y
  simp only [adicAbvDef]
  have h_mono := (toNNReal_strictMono hb).monotone
  rw [← h_mono.map_max]
  exact h_mono ((v.valuation _).map_add x y)

Depends on / 依赖: adicAbvDef, h_mono, h_mono.map_max, map_add, map_max, monotone, toNNReal_strictMono, v.adicAbvDef, v.valuation, valuation
-/
lemma isNonarchimedean_adicAbvDef : IsNonarchimedean (α := K) (v.adicAbvDef hb) := by
  intro x y
  simp only [adicAbvDef]
  have h_mono := (toNNReal_strictMono hb).monotone
  rw [← h_mono.map_max]
  exact h_mono ((v.valuation _).map_add x y)

/--
Definition of `adicAbv` / `adicAbv` 的定义

English:
definition adicAbv
  signature: : AbsoluteValue K Real where
  body: v.adicAbvDef hb x
  map_mul' _ _ := by simp [adicAbvDef]
  nonneg' _ := zero_le_coe
  eq_zero' _ := by simp [adicAbvDef]
  add_le' _ _ := (isNonarchimedean_adicAbvDef v hb).add_le fun _ => bot_le

中文:
定义 adicAbv
  签名: : 绝对值 K 实数 where
  定义体: v.adicAbvDef hb x
  map_mul' _ _ := by simp [adicAbvDef]
  nonneg' _ := zero_le_coe
  eq_zero' _ := by simp [adicAbvDef]
  add_le' _ _ := (isNonarchimedean_adicAbvDef v hb).add_le fun _ => bot_le

Depends on / 依赖: adicAbvDef, v.adicAbvDef
-/
def adicAbv : AbsoluteValue K Real where
  toFun x := v.adicAbvDef hb x
  map_mul' _ _ := by simp [adicAbvDef]
  nonneg' _ := zero_le_coe
  eq_zero' _ := by simp [adicAbvDef]
  add_le' _ _ := (isNonarchimedean_adicAbvDef v hb).add_le fun _ => bot_le

/--
theorem `isNonarchimedean_adicAbv` / 定理 `isNonarchimedean_adicAbv`

English:
theorem isNonarchimedean_adicAbv
  statement: IsNonarchimedean (α := K) (v.adicAbv hb)
  proof: isNonarchimedean_adicAbvDef v hb

中文:
定理 isNonarchimedean_adicAbv
  结论: IsNonarchimedean (α := K) (v.adicAbv hb)
  证明: isNonarchimedean_adicAbvDef v hb

Depends on / 依赖: adicAbv, v.adicAbv
-/
theorem isNonarchimedean_adicAbv : IsNonarchimedean (α := K) (v.adicAbv hb) :=
  isNonarchimedean_adicAbvDef v hb

/--
theorem `adicAbv_of_mk'` / 定理 `adicAbv_of_mk'`

English:
theorem adicAbv_of_mk'
  given: {s : nonZeroDivisors R}
  proof: by
  simp [adicAbv, adicAbvDef, intAdicAbv, intAdicAbvDef, valuation_of_algebraMap]

中文:
定理 adicAbv_of_mk'
  条件: {s : nonZeroDivisors R}
  证明: by
  simp [adicAbv, adicAbvDef, intAdicAbv, intAdicAbvDef, valuation_of_algebraMap]

Depends on / 依赖: adicAbv, adicAbvDef, intAdicAbv, intAdicAbvDef, valuation_of_algebraMap
-/
theorem adicAbv_of_mk' {s : nonZeroDivisors R} :
    v.adicAbv hb (IsLocalization.mk' K r s) = v.intAdicAbv hb r / v.intAdicAbv hb s := by
  simp [adicAbv, adicAbvDef, intAdicAbv, intAdicAbvDef, valuation_of_algebraMap]

/--
theorem `adicAbv_of_algebraMap` / 定理 `adicAbv_of_algebraMap`

English:
theorem adicAbv_of_algebraMap
  given: (r : R)
  statement: v.adicAbv hb (algebraMap R K r) = v.intAdicAbv hb r
  proof: by
  simp [adicAbv, adicAbvDef, intAdicAbv, intAdicAbvDef, valuation_of_algebraMap]

中文:
定理 adicAbv_of_algebraMap
  条件: (r : R)
  结论: v.adicAbv hb (algebraMap R K r) = v.intAdicAbv hb r
  证明: by
  simp [adicAbv, adicAbvDef, intAdicAbv, intAdicAbvDef, valuation_of_algebraMap]

Depends on / 依赖: adicAbv, adicAbvDef, intAdicAbv, intAdicAbvDef, valuation_of_algebraMap
-/
theorem adicAbv_of_algebraMap (r : R) : v.adicAbv hb (algebraMap R K r) = v.intAdicAbv hb r := by
  simp [adicAbv, adicAbvDef, intAdicAbv, intAdicAbvDef, valuation_of_algebraMap]

/--
theorem `adicAbv_coe_le_one` / 定理 `adicAbv_coe_le_one`

English:
theorem adicAbv_coe_le_one
  statement: v.adicAbv hb (algebraMap R K r) <= 1
  proof: by
  rw [adicAbv_of_algebraMap]
  exact intAdicAbv_le_one v hb r

中文:
定理 adicAbv_coe_le_one
  结论: v.adicAbv hb (algebraMap R K r) <= 1
  证明: by
  rw [adicAbv_of_algebraMap]
  exact intAdicAbv_le_one v hb r

Depends on / 依赖: adicAbv_of_algebraMap, intAdicAbv_le_one
-/
theorem adicAbv_coe_le_one : v.adicAbv hb (algebraMap R K r) <= 1 := by
  rw [adicAbv_of_algebraMap]
  exact intAdicAbv_le_one v hb r

/--
theorem `adicAbv_coe_lt_one_iff` / 定理 `adicAbv_coe_lt_one_iff`

English:
theorem adicAbv_coe_lt_one_iff
  statement: v.adicAbv hb (algebraMap R K r) < 1 ↔ r in v.asIdeal
  proof: by
  rw [adicAbv_of_algebraMap]
  exact intAdicAbv_lt_one_iff v hb r

中文:
定理 adicAbv_coe_lt_one_iff
  结论: v.adicAbv hb (algebraMap R K r) < 1 ↔ r in v.asIdeal
  证明: by
  rw [adicAbv_of_algebraMap]
  exact intAdicAbv_lt_one_iff v hb r

Depends on / 依赖: adicAbv_of_algebraMap, intAdicAbv_lt_one_iff
-/
theorem adicAbv_coe_lt_one_iff : v.adicAbv hb (algebraMap R K r) < 1 ↔ r in v.asIdeal := by
  rw [adicAbv_of_algebraMap]
  exact intAdicAbv_lt_one_iff v hb r

/--
theorem `adicAbv_coe_eq_one_iff` / 定理 `adicAbv_coe_eq_one_iff`

English:
theorem adicAbv_coe_eq_one_iff
  statement: v.adicAbv hb (algebraMap R K r) = 1 ↔ r ∉ v.asIdeal
  proof: by
  rw [adicAbv_of_algebraMap]
  exact intAdicAbv_eq_one_iff v hb r

中文:
定理 adicAbv_coe_eq_one_iff
  结论: v.adicAbv hb (algebraMap R K r) = 1 ↔ r ∉ v.asIdeal
  证明: by
  rw [adicAbv_of_algebraMap]
  exact intAdicAbv_eq_one_iff v hb r

Depends on / 依赖: adicAbv_of_algebraMap, intAdicAbv_eq_one_iff
-/
theorem adicAbv_coe_eq_one_iff : v.adicAbv hb (algebraMap R K r) = 1 ↔ r ∉ v.asIdeal := by
  rw [adicAbv_of_algebraMap]
  exact intAdicAbv_eq_one_iff v hb r

end AbsoluteValue

end IsDedekindDomain.HeightOneSpectrum

namespace Rat

open IsDedekindDomain.HeightOneSpectrum

variable {R : Type*} [CommRing R] [IsDedekindDomain R] [Algebra R Rat] [IsFractionRing R Rat]

/--
theorem `valuation_le_one_iff_den` / 定理 `valuation_le_one_iff_den`

English:
theorem valuation_le_one_iff_den
  given: {𝔭 : HeightOneSpectrum R} {x : Rat}
  proof: by
  have : CharZero R := ⟨.of_comp (f := algebraMap R Rat) (by simpa using Nat.cast_injective)⟩
  have : (x.den : R) != 0 := by simp
  simp [x.num_div_den, ← 𝔭.valuation_div_le_one_iff Rat x.num this
    (Ideal.IsPrime.notMem_of_isCoprime_of_mem (mod_cast x.isCoprime_num_den.symm.intCast))]

中文:
定理 valuation_le_one_iff_den
  条件: {𝔭 : 高一谱 R} {x : 有理数}
  证明: by
  have : CharZero R := ⟨.of_comp (f := algebraMap R Rat) (by simpa using Nat.cast_injective)⟩
  have : (x.den : R) != 0 := by simp
  simp [x.num_div_den, ← 𝔭.valuation_div_le_one_iff Rat x.num this
    (Ideal.IsPrime.notMem_of_isCoprime_of_mem (mod_cast x.isCoprime_num_den.symm.intCast))]

Depends on / 依赖: CharZero, Ideal.IsPrime.notMem_of_isCoprime_of_mem, IsPrime, Nat.cast_injective, algebraMap, cast_injective, intCast, isCoprime_num_den, mod_cast, notMem_of_isCoprime_of_mem, num_div_den, of_comp, valuation_div_le_one_iff, x.den, x.isCoprime_num_den.symm.intCast, x.num, x.num_div_den
-/
theorem valuation_le_one_iff_den {𝔭 : HeightOneSpectrum R} {x : Rat} :
    𝔭.valuation Rat x <= 1 ↔ ↑x.den ∉ 𝔭.asIdeal := by
  have : CharZero R := ⟨.of_comp (f := algebraMap R Rat) (by simpa using Nat.cast_injective)⟩
  have : (x.den : R) != 0 := by simp
  simp [x.num_div_den, ← 𝔭.valuation_div_le_one_iff Rat x.num this
    (Ideal.IsPrime.notMem_of_isCoprime_of_mem (mod_cast x.isCoprime_num_den.symm.intCast))]

end Rat
