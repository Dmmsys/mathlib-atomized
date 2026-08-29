/-
Copyright (c) 2024 Antoine Chambert-Loir, María Inés de Frutos Fernandez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, María Inés de Frutos-Fernández
-/
module

public import Mathlib.Data.ENat.Basic
public import Mathlib.Data.Finsupp.Weight
public import Mathlib.RingTheory.MvPowerSeries.Basic

/-! # Order of multivariate power series

We work with `MvPowerSeries σ R`, for `Semiring R`, and `w : σ → ℕ`.

## Weighted Order

- `MvPowerSeries.weightedOrder`: the weighted order of a multivariate power series,
  with respect to `w`, as an element of `ℕ∞`.

- `MvPowerSeries.weightedOrder_zero`: the weighted order of `0` is `0`.

- `MvPowerSeries.ne_zero_iff_weightedOrder_finite`: a multivariate power series is nonzero if
  and only if its weighted order is finite.

- `MvPowerSeries.exists_coeff_ne_zero_of_weightedOrder`: if the weighted order is finite,
  then there exists a nonzero coefficient of weight the weighted order.

- `MvPowerSeries.weightedOrder_le` : if a coefficient is nonzero, then the weighted order is at
  most the weight of that exponent.

- `MvPowerSeries.coeff_eq_zero_of_lt_weightedOrder`: all coefficients of weights strictly less
  than the weighted order vanish.

- `MvPowerSeries.weightedOrder_eq_top_iff`: the weighted order of `f` is `⊤` if and only if `f = 0`.

- `MvPowerSeries.nat_le_weightedOrder`: if all coefficients of weight `< n` vanish, then the
  weighted order is at least `n`.

- `MvPowerSeries.weightedOrder_eq_nat_iff`: the weighted order is some integer `n` iff there
  exists a nonzero coefficient of weight `n`, and all coefficients of strictly smaller weight
  vanish.

- `MvPowerSeries.weightedOrder_monomial`, `MvPowerSeries.weightedOrder_monomial_of_ne_zero`:
  the weighted order of a monomial, of a monomial with nonzero coefficient.

- `MvPowerSeries.min_weightedOrder_le_add`: the order of the sum of two multivariate power series
  is at least the minimum of their orders.

- `MvPowerSeries.weightedOrder_add_of_weightedOrder_ne`: the `weightedOrder` of the sum of two
  formal power series is the minimum of their orders if their orders differ.

- `MvPowerSeries.le_weightedOrder_mul`: the `weightedOrder` of the product of two formal power
  series is at least the sum of their orders.

- `MvPowerSeries.coeff_mul_left_one_sub_of_lt_weightedOrder`,
  `MvPowerSeries.coeff_mul_right_one_sub_of_lt_weightedOrder`: the coefficients of `f * (1 - g)`
  and `(1 - g) * f` in weights strictly less than the weighted order of `g`.

- `MvPowerSeries.coeff_mul_prod_one_sub_of_lt_weightedOrder`: the coefficients of
  `f * Π i in s, (1 - g i)`, in weights strictly less than the weighted orders of `g i`, for
  `i ∈ s`.

## Order

- `MvPowerSeries.order`: the weighted order, for `w = (1 : σ → ℕ)`.

- `MvPowerSeries.ne_zero_iff_order_finite`: `f` is nonzero iff its order is finite.

- `MvPowerSeries.order_eq_top_iff`: the order of `f` is infinite iff `f = 0`.

- `MvPowerSeries.exists_coeff_ne_zero_of_order`: if the order is finite, then there exists a
  nonzero coefficient of degree equal to the order.

- `MvPowerSeries.order_le` : if a coefficient of some degree is nonzero, then the order
  is at least that degree.

- `MvPowerSeries.nat_le_order`: if all coefficients of degree strictly smaller than some integer
  vanish, then the order is at least that integer.

- `MvPowerSeries.order_eq_nat_iff`: the order of a power series is an integer `n` iff there exists
  a nonzero coefficient in that degree, and all coefficients below that degree vanish.

- `MvPowerSeries.order_monomial`, `MvPowerSeries.order_monomial_of_ne_zero`: the order of a
  monomial, with a nonzero coefficient

- `MvPowerSeries.min_order_le_add`: the order of a sum of two power series is at least the minimum
  of their orders.

- `MvPowerSeries.order_add_of_order_ne`: the order of a sum of two power series of distinct orders
  is the minimum of their orders.

- `MvPowerSeries.order_mul_ge`: the order of a product of two power series is at least the sum of
  their orders.

- `MvPowerSeries.coeff_mul_left_one_sub_of_lt_order`,
  `MvPowerSeries.coeff_mul_right_one_sub_of_lt_order`: the coefficients of `f * (1 - g)` and
  `(1 - g) * f` below the order of `g` coincide with that of `f`.

- `MvPowerSeries.coeff_mul_prod_one_sub_of_lt_order`: the coefficients of `f * Π i in s, (1 - g i)`
  coincide with that of `f` below the minimum of the orders of the `g i`, for `i ∈ s`.

## Homogeneous components

- `MvPowerSeries.weightedHomogeneousComponent`, `MvPowerSeries.homogeneousComponent`: the power
  series which is the sum of all monomials of given weighted degree, resp. degree.

NOTE:
Under `Finite σ`, one can use `Finsupp.finite_of_degree_le` and `Finsupp.finite_of_weight_le` to
show that they have finite support, hence correspond to `MvPolynomial`.

However, when `σ` is finite, this is not necessarily an `MvPolynomial`.
(For example: the homogeneous components of degree 1 of the multivariate power
series, all of which coefficients are `1`, is the sum of all indeterminates.)

TODO: Define a coercion to MvPolynomial.

-/

@[expose] public section

namespace MvPowerSeries

noncomputable section

open ENat WithTop Finsupp

variable {σ R : Type*} [Semiring R]

section WeightedOrder

variable (w : σ -> Nat) {f g : MvPowerSeries σ R}

/--
theorem `ne_zero_iff_exists_coeff_ne_zero_and_weight` / 定理 `ne_zero_iff_exists_coeff_ne_zero_and_weight`

English:
theorem ne_zero_iff_exists_coeff_ne_zero_and_weight
  proof: by
  simpa using ne_zero_iff_exists_coeff_ne_zero f

中文:
定理 ne_zero_iff_存在_coeff_ne_zero_and_weight
  证明: by
  simpa using ne_zero_iff_exists_coeff_ne_zero f

Depends on / 依赖: ne_zero_iff_exists_coeff_ne_zero
-/
theorem ne_zero_iff_exists_coeff_ne_zero_and_weight :
    f != 0 ↔ (exists n : Nat, exists d : σ ->₀ Nat, coeff d f != 0 ∧ weight w d = n) := by
  simpa using ne_zero_iff_exists_coeff_ne_zero f

/--
Definition of `weightedOrder` / `weightedOrder` 的定义

English:
definition weightedOrder
  signature: (f : MvPowerSeries σ R)
  body: by
  classical
  exact dite (f = 0) (fun _ => ⊤) fun h =>
    Nat.find ((ne_zero_iff_exists_coeff_ne_zero_and_weight w).mp h)

中文:
定义 weightedOrder
  签名: (f : MvPowerSeries σ R)
  定义体: by
  classical
  exact dite (f = 0) (fun _ => ⊤) fun h =>
    Nat.find ((ne_zero_iff_exists_coeff_ne_zero_and_weight w).mp h)

Depends on / 依赖: Nat.find, classical, ne_zero_iff_exists_coeff_ne_zero_and_weight
-/
def weightedOrder (f : MvPowerSeries σ R) : Nat∞ := by
  classical
  exact dite (f = 0) (fun _ => ⊤) fun h =>
    Nat.find ((ne_zero_iff_exists_coeff_ne_zero_and_weight w).mp h)

/--
theorem `weightedOrder_zero` / 定理 `weightedOrder_zero`

English:
theorem weightedOrder_zero
  statement: (0 : MvPowerSeries σ R).weightedOrder w = ⊤
  proof: by
  rw [weightedOrder]; rw [dif_pos rfl]

中文:
定理 weightedOrder_zero
  结论: (0 : MvPowerSeries σ R).weightedOrder w = ⊤
  证明: by
  rw [weightedOrder]; rw [dif_pos rfl]
-/
@[simp] theorem weightedOrder_zero : (0 : MvPowerSeries σ R).weightedOrder w = ⊤ := by
  rw [weightedOrder]; rw [dif_pos rfl]

/--
theorem `ne_zero_iff_weightedOrder_finite` / 定理 `ne_zero_iff_weightedOrder_finite`

English:
theorem ne_zero_iff_weightedOrder_finite
  proof: by
  simp only [weightedOrder, ne_eq, natCast_toNat_eq_self, dite_eq_left_iff,
    ENat.natCast_ne_top, imp_false, not_not]

中文:
定理 ne_zero_iff_weightedOrder_finite
  证明: by
  simp only [weightedOrder, ne_eq, natCast_toNat_eq_self, dite_eq_left_iff,
    ENat.natCast_ne_top, imp_false, not_not]

Depends on / 依赖: ENat.natCast_ne_top, dite_eq_left_iff, imp_false, natCast_ne_top, natCast_toNat_eq_self, ne_eq, not_not, weightedOrder
-/
theorem ne_zero_iff_weightedOrder_finite :
    f != 0 ↔ (f.weightedOrder w).toNat = f.weightedOrder w := by
  simp only [weightedOrder, ne_eq, natCast_toNat_eq_self, dite_eq_left_iff,
    ENat.natCast_ne_top, imp_false, not_not]

/-- The `0` power series is the unique power series with infinite order. -/
@[simp]
/--
theorem `weightedOrder_eq_top_iff` / 定理 `weightedOrder_eq_top_iff`

English:
theorem weightedOrder_eq_top_iff
  proof: by
  rw [← not_iff_not]; rw [← ne_eq]; rw [← ne_eq]; rw [ne_zero_iff_weightedOrder_finite w]; rw [natCast_toNat_eq_self]

中文:
定理 weightedOrder_eq_top_iff
  证明: by
  rw [← not_iff_not]; rw [← ne_eq]; rw [← ne_eq]; rw [ne_zero_iff_weightedOrder_finite w]; rw [natCast_toNat_eq_self]

Depends on / 依赖: natCast_toNat_eq_self, ne_eq, ne_zero_iff_weightedOrder_finite, not_iff_not
-/
theorem weightedOrder_eq_top_iff :
    f.weightedOrder w = ⊤ ↔ f = 0 := by
  rw [← not_iff_not]; rw [← ne_eq]; rw [← ne_eq]; rw [ne_zero_iff_weightedOrder_finite w]; rw [natCast_toNat_eq_self]

/--
theorem `exists_coeff_ne_zero_and_weightedOrder` / 定理 `exists_coeff_ne_zero_and_weightedOrder`

English:
theorem exists_coeff_ne_zero_and_weightedOrder
  proof: by
  classical
  simp_rw [weightedOrder, dif_neg ((ne_zero_iff_weightedOrder_finite w).mpr h), Nat.cast_inj]
  generalize_proofs h1
  exact Nat.find_spec h1

中文:
定理 存在_coeff_ne_zero_and_weightedOrder
  证明: by
  classical
  simp_rw [weightedOrder, dif_neg ((ne_zero_iff_weightedOrder_finite w).mpr h), Nat.cast_inj]
  generalize_proofs h1
  exact Nat.find_spec h1

Depends on / 依赖: Nat.cast_inj, Nat.find_spec, cast_inj, classical, dif_neg, find_spec, generalize_proofs, ne_zero_iff_weightedOrder_finite, simp_rw, weightedOrder
-/
theorem exists_coeff_ne_zero_and_weightedOrder
    (h : (toNat (f.weightedOrder w) : Nat∞) = f.weightedOrder w) :
    exists d, coeff d f != 0 ∧ weight w d = f.weightedOrder w := by
  classical
  simp_rw [weightedOrder, dif_neg ((ne_zero_iff_weightedOrder_finite w).mpr h), Nat.cast_inj]
  generalize_proofs h1
  exact Nat.find_spec h1

/--
theorem `weightedOrder_le` / 定理 `weightedOrder_le`

English:
theorem weightedOrder_le
  given: {d : σ ->₀ Nat} (h : coeff d f != 0)
  proof: by
  rw [weightedOrder]; rw [dif_neg]
  · simp only [ne_eq, Nat.cast_le, Nat.find_le_iff]
    exact ⟨weight w d, le_rfl, d, h, rfl⟩
  · exact (f.ne_zero_iff_exists_coeff_ne_zero_and_weight w).mpr ⟨weight w d, d, h, rfl⟩

中文:
定理 weightedOrder_le
  条件: {d : σ ->₀ 自然数} (h : coeff d f != 0)
  证明: by
  rw [weightedOrder]; rw [dif_neg]
  · simp only [ne_eq, Nat.cast_le, Nat.find_le_iff]
    exact ⟨weight w d, le_rfl, d, h, rfl⟩
  · exact (f.ne_zero_iff_exists_coeff_ne_zero_and_weight w).mpr ⟨weight w d, d, h, rfl⟩

Depends on / 依赖: Nat.cast_le, Nat.find_le_iff, cast_le, dif_neg, f.ne_zero_iff_exists_coeff_ne_zero_and_weight, find_le_iff, le_rfl, ne_eq, ne_zero_iff_exists_coeff_ne_zero_and_weight, weight, weightedOrder
-/
theorem weightedOrder_le {d : σ ->₀ Nat} (h : coeff d f != 0) :
    f.weightedOrder w <= weight w d := by
  rw [weightedOrder]; rw [dif_neg]
  · simp only [ne_eq, Nat.cast_le, Nat.find_le_iff]
    exact ⟨weight w d, le_rfl, d, h, rfl⟩
  · exact (f.ne_zero_iff_exists_coeff_ne_zero_and_weight w).mpr ⟨weight w d, d, h, rfl⟩

/--
theorem `coeff_eq_zero_of_lt_weightedOrder` / 定理 `coeff_eq_zero_of_lt_weightedOrder`

English:
theorem coeff_eq_zero_of_lt_weightedOrder
  given: {d : σ ->₀ Nat} (h : (weight w d) < f.weightedOrder w)
  proof: by
  contrapose! h; exact weightedOrder_le w h

中文:
定理 coeff_eq_zero_of_lt_weightedOrder
  条件: {d : σ ->₀ 自然数} (h : (weight w d) < f.weightedOrder w)
  证明: by
  contrapose! h; exact weightedOrder_le w h

Depends on / 依赖: contrapose, weightedOrder_le
-/
theorem coeff_eq_zero_of_lt_weightedOrder {d : σ ->₀ Nat} (h : (weight w d) < f.weightedOrder w) :
    coeff d f = 0 := by
  contrapose! h; exact weightedOrder_le w h

/--
theorem `nat_le_weightedOrder` / 定理 `nat_le_weightedOrder`

English:
theorem nat_le_weightedOrder
  given: {n : Nat} (h : forall d, weight w d < n -> coeff d f = 0)
  proof: by
  by_contra! H
  have : (f.weightedOrder w).toNat = f.weightedOrder w := by
    rw [natCast_toNat_eq_self]; exact ne_top_of_lt H
  obtain ⟨d, hfd, hd⟩ := exists_coeff_ne_zero_and_weightedOrder w this
  rw [← hd]; rw [Nat.cast_lt] at H
  exact hfd (h d H)

中文:
定理 nat_le_weightedOrder
  条件: {n : 自然数} (h : 对任意 d, weight w d < n -> coeff d f = 0)
  证明: by
  by_contra! H
  have : (f.weightedOrder w).toNat = f.weightedOrder w := by
    rw [natCast_toNat_eq_self]; exact ne_top_of_lt H
  obtain ⟨d, hfd, hd⟩ := exists_coeff_ne_zero_and_weightedOrder w this
  rw [← hd]; rw [Nat.cast_lt] at H
  exact hfd (h d H)

Depends on / 依赖: Nat.cast_lt, cast_lt, exists_coeff_ne_zero_and_weightedOrder, f.weightedOrder, natCast_toNat_eq_self, ne_top_of_lt, weightedOrder
-/
theorem nat_le_weightedOrder {n : Nat} (h : forall d, weight w d < n -> coeff d f = 0) :
    n <= f.weightedOrder w := by
  by_contra! H
  have : (f.weightedOrder w).toNat = f.weightedOrder w := by
    rw [natCast_toNat_eq_self]; exact ne_top_of_lt H
  obtain ⟨d, hfd, hd⟩ := exists_coeff_ne_zero_and_weightedOrder w this
  rw [← hd]; rw [Nat.cast_lt] at H
  exact hfd (h d H)

/--
theorem `le_weightedOrder` / 定理 `le_weightedOrder`

English:
theorem le_weightedOrder
  given: {n : Nat∞} (h : forall d : σ ->₀ Nat, weight w d < n -> coeff d f = 0)
  proof: by
  cases n
  · rw [top_le_iff, weightedOrder_eq_top_iff]
    ext d; exact h d (ENat.natCast_lt_top _)
  · apply nat_le_weightedOrder;
    simpa only [ENat.some_eq_natCast, Nat.cast_lt] using h

中文:
定理 le_weightedOrder
  条件: {n : 自然数∞} (h : 对任意 d : σ ->₀ 自然数, weight w d < n -> coeff d f = 0)
  证明: by
  cases n
  · rw [top_le_iff, weightedOrder_eq_top_iff]
    ext d; exact h d (ENat.natCast_lt_top _)
  · apply nat_le_weightedOrder;
    simpa only [ENat.some_eq_natCast, Nat.cast_lt] using h

Depends on / 依赖: ENat.natCast_lt_top, ENat.some_eq_natCast, Nat.cast_lt, cast_lt, natCast_lt_top, nat_le_weightedOrder, some_eq_natCast, top_le_iff, weightedOrder_eq_top_iff
-/
theorem le_weightedOrder {n : Nat∞} (h : forall d : σ ->₀ Nat, weight w d < n -> coeff d f = 0) :
    n <= f.weightedOrder w := by
  cases n
  · rw [top_le_iff, weightedOrder_eq_top_iff]
    ext d; exact h d (ENat.natCast_lt_top _)
  · apply nat_le_weightedOrder;
    simpa only [ENat.some_eq_natCast, Nat.cast_lt] using h

/--
theorem `weightedOrder_eq_nat` / 定理 `weightedOrder_eq_nat`

English:
theorem weightedOrder_eq_nat
  given: {n : Nat}
  proof: by
  constructor
  · intro h
    obtain ⟨d, hd⟩ := f.exists_coeff_ne_zero_and_weightedOrder w (by simp only [h, toNat_natCast])
    exact ⟨⟨d, by simpa [h, Nat.cast_inj, ne_eq] using hd⟩,
      fun e he => f.coeff_eq_zero_of_lt_weightedOrder w (by simp only [h, Nat.cast_lt, he])⟩
  · rintro ⟨⟨d, hd'

中文:
定理 weightedOrder_eq_nat
  条件: {n : 自然数}
  证明: by
  constructor
  · intro h
    obtain ⟨d, hd⟩ := f.exists_coeff_ne_zero_and_weightedOrder w (by simp only [h, toNat_natCast])
    exact ⟨⟨d, by simpa [h, Nat.cast_inj, ne_eq] using hd⟩,
      fun e he => f.coeff_eq_zero_of_lt_weightedOrder w (by simp only [h, Nat.cast_lt, he])⟩
  · rintro ⟨⟨d, hd'

Depends on / 依赖: Nat.cast_inj, Nat.cast_lt, cast_inj, cast_lt, coeff_eq_zero_of_lt_weightedOrder, exists_coeff_ne_zero_and_weightedOrder, f.coeff_eq_zero_of_lt_weightedOrder, f.exists_coeff_ne_zero_and_weightedOrder, f.weightedOrder_le, hd.symm, le_antisymm, nat_le_weightedOrder, ne_eq, toNat_natCast, weightedOrder_le
-/
theorem weightedOrder_eq_nat {n : Nat} :
    f.weightedOrder w = n ↔
      (exists d, coeff d f != 0 ∧ weight w d = n) ∧ forall d, weight w d < n -> coeff d f = 0 := by
  constructor
  · intro h
    obtain ⟨d, hd⟩ := f.exists_coeff_ne_zero_and_weightedOrder w (by simp only [h, toNat_natCast])
    exact ⟨⟨d, by simpa [h, Nat.cast_inj, ne_eq] using hd⟩,
      fun e he => f.coeff_eq_zero_of_lt_weightedOrder w (by simp only [h, Nat.cast_lt, he])⟩
  · rintro ⟨⟨d, hd', hd⟩, h⟩
    exact le_antisymm (hd.symm ▸ f.weightedOrder_le w hd') (nat_le_weightedOrder w h)

/--
theorem `weightedOrder_monomial` / 定理 `weightedOrder_monomial`

English:
theorem weightedOrder_monomial
  given: {d : σ ->₀ Nat} {a : R} [Decidable (a = 0)]
  proof: by
  classical
  split_ifs with h
  · rw [h, weightedOrder_eq_top_iff, map_zero]
  · rw [weightedOrder_eq_nat]
    constructor
    · use d
      simp only [coeff_monomial_same, ne_eq, h, not_false_eq_true, and_self]
    · intro b hb
      rw [coeff_monomial]; rw [if_neg]
      rintro rfl
      exact

中文:
定理 weightedOrder_monomial
  条件: {d : σ ->₀ 自然数} {a : R} [可判定 (a = 0)]
  证明: by
  classical
  split_ifs with h
  · rw [h, weightedOrder_eq_top_iff, map_zero]
  · rw [weightedOrder_eq_nat]
    constructor
    · use d
      simp only [coeff_monomial_same, ne_eq, h, not_false_eq_true, and_self]
    · intro b hb
      rw [coeff_monomial]; rw [if_neg]
      rintro rfl
      exact

Depends on / 依赖: and_self, classical, coeff_monomial, coeff_monomial_same, hb.false, if_neg, map_zero, ne_eq, not_false_eq_true, split_ifs, weightedOrder_eq_nat, weightedOrder_eq_top_iff
-/
theorem weightedOrder_monomial {d : σ ->₀ Nat} {a : R} [Decidable (a = 0)] :
    weightedOrder w (monomial d a) = if a = 0 then (⊤ : Nat∞) else weight w d := by
  classical
  split_ifs with h
  · rw [h, weightedOrder_eq_top_iff, map_zero]
  · rw [weightedOrder_eq_nat]
    constructor
    · use d
      simp only [coeff_monomial_same, ne_eq, h, not_false_eq_true, and_self]
    · intro b hb
      rw [coeff_monomial]; rw [if_neg]
      rintro rfl
      exact hb.false

/--
theorem `weightedOrder_monomial_of_ne_zero` / 定理 `weightedOrder_monomial_of_ne_zero`

English:
theorem weightedOrder_monomial_of_ne_zero
  given: {d : σ ->₀ Nat} {a : R} (h : a != 0)
  proof: by
  classical
  rw [weightedOrder_monomial]; rw [if_neg h]

@[simp]

中文:
定理 weightedOrder_monomial_of_ne_zero
  条件: {d : σ ->₀ 自然数} {a : R} (h : a != 0)
  证明: by
  classical
  rw [weightedOrder_monomial]; rw [if_neg h]

@[simp]

Depends on / 依赖: classical, if_neg, weightedOrder_monomial
-/
theorem weightedOrder_monomial_of_ne_zero {d : σ ->₀ Nat} {a : R} (h : a != 0) :
    weightedOrder w (monomial d a) = weight w d := by
  classical
  rw [weightedOrder_monomial]; rw [if_neg h]

@[simp]
/--
theorem `weightedOrder_one` / 定理 `weightedOrder_one`

English:
theorem weightedOrder_one
  given: [Nontrivial R]
  statement: (1 : MvPowerSeries σ R).weightedOrder w = 0
  proof: weightedOrder_monomial_of_ne_zero w one_ne_zero

中文:
定理 weightedOrder_one
  条件: [非平凡 R]
  结论: (1 : MvPowerSeries σ R).weightedOrder w = 0
  证明: weightedOrder_monomial_of_ne_zero w one_ne_zero

Depends on / 依赖: one_ne_zero, weightedOrder_monomial_of_ne_zero
-/
theorem weightedOrder_one [Nontrivial R] : (1 : MvPowerSeries σ R).weightedOrder w = 0 :=
  weightedOrder_monomial_of_ne_zero w one_ne_zero

/--
theorem `min_weightedOrder_le_add` / 定理 `min_weightedOrder_le_add`

English:
theorem min_weightedOrder_le_add
  proof: by
  apply le_weightedOrder w
  simp +contextual only
    [coeff_eq_zero_of_lt_weightedOrder w, lt_min_iff, map_add, add_zero,
      imp_true_iff]

中文:
定理 min_weightedOrder_le_add
  证明: by
  apply le_weightedOrder w
  simp +contextual only
    [coeff_eq_zero_of_lt_weightedOrder w, lt_min_iff, map_add, add_zero,
      imp_true_iff]

Depends on / 依赖: add_zero, coeff_eq_zero_of_lt_weightedOrder, contextual, imp_true_iff, le_weightedOrder, lt_min_iff, map_add
-/
theorem min_weightedOrder_le_add :
    min (f.weightedOrder w) (g.weightedOrder w) <= (f + g).weightedOrder w := by
  apply le_weightedOrder w
  simp +contextual only
    [coeff_eq_zero_of_lt_weightedOrder w, lt_min_iff, map_add, add_zero,
      imp_true_iff]

/--
theorem `weightedOrder_add_of_weightedOrder_lt.aux` / 定理 `weightedOrder_add_of_weightedOrder_lt.aux`

English:
theorem weightedOrder_add_of_weightedOrder_lt.aux
  proof: by
  obtain ⟨n, hn : (n : Nat∞) = _⟩ := ENat.ne_top_iff_exists.mp (ne_top_of_lt H)
  rw [← hn]; rw [weightedOrder_eq_nat]
  obtain ⟨d, hd', hd⟩ := ((weightedOrder_eq_nat w).mp hn.symm).1
  constructor
  · refine ⟨d, ?_, hd⟩
    rw [← hn]; rw [← hd] at H
    rw [(coeff _).map_add]; rw [coeff_eq_zero_

中文:
定理 weightedOrder_add_of_weightedOrder_lt.aux
  证明: by
  obtain ⟨n, hn : (n : Nat∞) = _⟩ := ENat.ne_top_iff_exists.mp (ne_top_of_lt H)
  rw [← hn]; rw [weightedOrder_eq_nat]
  obtain ⟨d, hd', hd⟩ := ((weightedOrder_eq_nat w).mp hn.symm).1
  constructor
  · refine ⟨d, ?_, hd⟩
    rw [← hn]; rw [← hd] at H
    rw [(coeff _).map_add]; rw [coeff_eq_zero_
-/
private theorem weightedOrder_add_of_weightedOrder_lt.aux
    (H : f.weightedOrder w < g.weightedOrder w) :
    (f + g).weightedOrder w = f.weightedOrder w := by
  obtain ⟨n, hn : (n : Nat∞) = _⟩ := ENat.ne_top_iff_exists.mp (ne_top_of_lt H)
  rw [← hn]; rw [weightedOrder_eq_nat]
  obtain ⟨d, hd', hd⟩ := ((weightedOrder_eq_nat w).mp hn.symm).1
  constructor
  · refine ⟨d, ?_, hd⟩
    rw [← hn]; rw [← hd] at H
    rw [(coeff _).map_add]; rw [coeff_eq_zero_of_lt_weightedOrder w H]; rw [add_zero]
    exact hd'
  · intro b hb
    suffices weight w b < weightedOrder w f by
      rw [(coeff _).map_add]; rw [coeff_eq_zero_of_lt_weightedOrder w this]; rw [coeff_eq_zero_of_lt_weightedOrder w (lt_trans this H)]; rw [add_zero]
    rw [← hn]; rw [Nat.cast_lt]
    exact hb

/--
theorem `weightedOrder_add_of_weightedOrder_ne` / 定理 `weightedOrder_add_of_weightedOrder_ne`

English:
theorem weightedOrder_add_of_weightedOrder_ne
  given: (h : f.weightedOrder w != g.weightedOrder w)
  proof: by
  refine le_antisymm ?_ (min_weightedOrder_le_add w)
  wlog H₁ : f.weightedOrder w < g.weightedOrder w
  · rw [add_comm f g, inf_comm]
    exact this _ h.symm ((le_of_not_gt H₁).lt_of_ne' h)
  simp only [le_inf_iff, weightedOrder_add_of_weightedOrder_lt.aux w H₁]
  exact ⟨le_rfl, le_of_lt H₁⟩

中文:
定理 weightedOrder_add_of_weightedOrder_ne
  条件: (h : f.weightedOrder w != g.weightedOrder w)
  证明: by
  refine le_antisymm ?_ (min_weightedOrder_le_add w)
  wlog H₁ : f.weightedOrder w < g.weightedOrder w
  · rw [add_comm f g, inf_comm]
    exact this _ h.symm ((le_of_not_gt H₁).lt_of_ne' h)
  simp only [le_inf_iff, weightedOrder_add_of_weightedOrder_lt.aux w H₁]
  exact ⟨le_rfl, le_of_lt H₁⟩

Depends on / 依赖: add_comm, f.weightedOrder, g.weightedOrder, h.symm, inf_comm, le_antisymm, le_inf_iff, le_of_lt, le_of_not_gt, le_rfl, lt_of_ne, min_weightedOrder_le_add, weightedOrder, weightedOrder_add_of_weightedOrder_lt, weightedOrder_add_of_weightedOrder_lt.aux
-/
theorem weightedOrder_add_of_weightedOrder_ne (h : f.weightedOrder w != g.weightedOrder w) :
    weightedOrder w (f + g) = weightedOrder w f ⊓ weightedOrder w g := by
  refine le_antisymm ?_ (min_weightedOrder_le_add w)
  wlog H₁ : f.weightedOrder w < g.weightedOrder w
  · rw [add_comm f g, inf_comm]
    exact this _ h.symm ((le_of_not_gt H₁).lt_of_ne' h)
  simp only [le_inf_iff, weightedOrder_add_of_weightedOrder_lt.aux w H₁]
  exact ⟨le_rfl, le_of_lt H₁⟩

/--
theorem `le_weightedOrder_mul` / 定理 `le_weightedOrder_mul`

English:
theorem le_weightedOrder_mul
  proof: by
  classical
  apply le_weightedOrder
  intro d hd
  rw [coeff_mul]; rw [Finset.sum_eq_zero]
  rintro ⟨i, j⟩ hij
  by_cases! hi : weight w i < f.weightedOrder w
  · rw [coeff_eq_zero_of_lt_weightedOrder w hi, zero_mul]
  · by_cases! hj : weight w j < g.weightedOrder w
    · rw [coeff_eq_zero_of_lt

中文:
定理 le_weightedOrder_mul
  证明: by
  classical
  apply le_weightedOrder
  intro d hd
  rw [coeff_mul]; rw [Finset.sum_eq_zero]
  rintro ⟨i, j⟩ hij
  by_cases! hi : weight w i < f.weightedOrder w
  · rw [coeff_eq_zero_of_lt_weightedOrder w hi, zero_mul]
  · by_cases! hj : weight w j < g.weightedOrder w
    · rw [coeff_eq_zero_of_lt

Depends on / 依赖: Finset, Finset.mem_antidiagonal, Finset.sum_eq_zero, Nat.cast_add, add_le_add, cast_add, classical, coeff_eq_zero_of_lt_weightedOrder, coeff_mul, f.weightedOrder, g.weightedOrder, le_weightedOrder, lt_of_lt_of_le, map_add, mem_antidiagonal, mul_zero, ne_of_lt, sum_eq_zero, weight, weightedOrder
-/
theorem le_weightedOrder_mul :
    f.weightedOrder w + g.weightedOrder w <= weightedOrder w (f * g) := by
  classical
  apply le_weightedOrder
  intro d hd
  rw [coeff_mul]; rw [Finset.sum_eq_zero]
  rintro ⟨i, j⟩ hij
  by_cases! hi : weight w i < f.weightedOrder w
  · rw [coeff_eq_zero_of_lt_weightedOrder w hi, zero_mul]
  · by_cases! hj : weight w j < g.weightedOrder w
    · rw [coeff_eq_zero_of_lt_weightedOrder w hj, mul_zero]
    · simp only [Finset.mem_antidiagonal] at hij
      exfalso
      apply ne_of_lt (lt_of_lt_of_le hd <| add_le_add hi hj)
      rw [← hij]; rw [map_add]; rw [Nat.cast_add]

/--
theorem `le_weightedOrder_pow` / 定理 `le_weightedOrder_pow`

English:
theorem le_weightedOrder_pow
  given: (n : Nat)
  statement: n • f.weightedOrder w <= (f ^ n).weightedOrder w
  proof: by
  induction n with
  | zero => simp
  | succ n hn => grw [succ_nsmul, pow_succ, hn, le_weightedOrder_mul]

中文:
定理 le_weightedOrder_pow
  条件: (n : 自然数)
  结论: n • f.weightedOrder w <= (f ^ n).weightedOrder w
  证明: by
  induction n with
  | zero => simp
  | succ n hn => grw [succ_nsmul, pow_succ, hn, le_weightedOrder_mul]

Depends on / 依赖: le_weightedOrder_mul, pow_succ, succ_nsmul
-/
theorem le_weightedOrder_pow (n : Nat) : n • f.weightedOrder w <= (f ^ n).weightedOrder w := by
  induction n with
  | zero => simp
  | succ n hn => grw [succ_nsmul, pow_succ, hn, le_weightedOrder_mul]

/--
theorem `le_weightedOrder_prod` / 定理 `le_weightedOrder_prod`

English:
theorem le_weightedOrder_prod
  statement: {R : Type*} [CommSemiring R] {ι : Type*} (w : σ -> Nat)
  proof: by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih => grw [Finset.sum_cons ha, Finset.prod_cons ha, ih, le_weightedOrder_mul]

alias weightedOrder_mul_ge := le_weightedOrder_mul

中文:
定理 le_weightedOrder_prod
  结论: {R : 类型} [交换半环 R] {ι : 类型} (w : σ -> 自然数)
  证明: by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih => grw [Finset.sum_cons ha, Finset.prod_cons ha, ih, le_weightedOrder_mul]

alias weightedOrder_mul_ge := le_weightedOrder_mul

Depends on / 依赖: Finset, Finset.cons_induction, Finset.prod_cons, Finset.sum_cons, cons_induction, le_weightedOrder_mul, prod_cons, sum_cons
-/
theorem le_weightedOrder_prod {R : Type*} [CommSemiring R] {ι : Type*} (w : σ -> Nat)
    (f : ι -> MvPowerSeries σ R) (s : Finset ι) :
    ∑ i in s, (f i).weightedOrder w <= (∏ i in s, f i).weightedOrder w := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih => grw [Finset.sum_cons ha, Finset.prod_cons ha, ih, le_weightedOrder_mul]

alias weightedOrder_mul_ge := le_weightedOrder_mul

/--
theorem `le_weightedOrder_smul` / 定理 `le_weightedOrder_smul`

English:
theorem le_weightedOrder_smul
  given: {a : R}
  proof: le_weightedOrder _ fun i hi => by simp [coeff_eq_zero_of_lt_weightedOrder _ hi]

中文:
定理 le_weightedOrder_smul
  条件: {a : R}
  证明: le_weightedOrder _ fun i hi => by simp [coeff_eq_zero_of_lt_weightedOrder _ hi]

Depends on / 依赖: coeff_eq_zero_of_lt_weightedOrder, le_weightedOrder
-/
theorem le_weightedOrder_smul {a : R} :
    f.weightedOrder w <= (a • f).weightedOrder w :=
  le_weightedOrder _ fun i hi => by simp [coeff_eq_zero_of_lt_weightedOrder _ hi]

section

variable {S : Type*} [Semiring S]

/--
theorem `le_weightedOrder_map` / 定理 `le_weightedOrder_map`

English:
theorem le_weightedOrder_map
  given: (φ : R ->+* S)
  proof: le_weightedOrder w fun i hi => by simp [coeff_eq_zero_of_lt_weightedOrder _ hi]

中文:
定理 le_weightedOrder_map
  条件: (φ : R ->+* S)
  证明: le_weightedOrder w fun i hi => by simp [coeff_eq_zero_of_lt_weightedOrder _ hi]

Depends on / 依赖: coeff_eq_zero_of_lt_weightedOrder, le_weightedOrder
-/
theorem le_weightedOrder_map (φ : R ->+* S) :
    f.weightedOrder w <= (f.map φ).weightedOrder w :=
  le_weightedOrder w fun i hi => by simp [coeff_eq_zero_of_lt_weightedOrder _ hi]

end

section Ring

variable {R : Type*} [Ring R] {f g : MvPowerSeries σ R}

/--
theorem `coeff_mul_left_one_sub_of_lt_weightedOrder` / 定理 `coeff_mul_left_one_sub_of_lt_weightedOrder`

English:
theorem coeff_mul_left_one_sub_of_lt_weightedOrder
  proof: by
  simp only [mul_sub, mul_one, map_sub, sub_eq_self]
  apply coeff_eq_zero_of_lt_weightedOrder w
  exact lt_of_lt_of_le (lt_of_lt_of_le h le_add_self) (le_weightedOrder_mul w)

中文:
定理 coeff_mul_left_one_sub_of_lt_weightedOrder
  证明: by
  simp only [mul_sub, mul_one, map_sub, sub_eq_self]
  apply coeff_eq_zero_of_lt_weightedOrder w
  exact lt_of_lt_of_le (lt_of_lt_of_le h le_add_self) (le_weightedOrder_mul w)

Depends on / 依赖: coeff_eq_zero_of_lt_weightedOrder, le_add_self, le_weightedOrder_mul, lt_of_lt_of_le, map_sub, mul_one, mul_sub, sub_eq_self
-/
theorem coeff_mul_left_one_sub_of_lt_weightedOrder
    {d : σ ->₀ Nat} (h : (weight w d) < g.weightedOrder w) :
    coeff d (f * (1 - g)) = coeff d f := by
  simp only [mul_sub, mul_one, map_sub, sub_eq_self]
  apply coeff_eq_zero_of_lt_weightedOrder w
  exact lt_of_lt_of_le (lt_of_lt_of_le h le_add_self) (le_weightedOrder_mul w)

/--
theorem `coeff_mul_right_one_sub_of_lt_weightedOrder` / 定理 `coeff_mul_right_one_sub_of_lt_weightedOrder`

English:
theorem coeff_mul_right_one_sub_of_lt_weightedOrder
  proof: by
  simp only [sub_mul, one_mul, map_sub, sub_eq_self]
  apply coeff_eq_zero_of_lt_weightedOrder w
  apply lt_of_lt_of_le (lt_of_lt_of_le h le_self_add) (le_weightedOrder_mul w)

中文:
定理 coeff_mul_right_one_sub_of_lt_weightedOrder
  证明: by
  simp only [sub_mul, one_mul, map_sub, sub_eq_self]
  apply coeff_eq_zero_of_lt_weightedOrder w
  apply lt_of_lt_of_le (lt_of_lt_of_le h le_self_add) (le_weightedOrder_mul w)

Depends on / 依赖: coeff_eq_zero_of_lt_weightedOrder, le_self_add, le_weightedOrder_mul, lt_of_lt_of_le, map_sub, one_mul, sub_eq_self, sub_mul
-/
theorem coeff_mul_right_one_sub_of_lt_weightedOrder
    {d : σ ->₀ Nat} (h : (weight w d) < g.weightedOrder w) :
    coeff d ((1 - g) * f) = coeff d f := by
  simp only [sub_mul, one_mul, map_sub, sub_eq_self]
  apply coeff_eq_zero_of_lt_weightedOrder w
  apply lt_of_lt_of_le (lt_of_lt_of_le h le_self_add) (le_weightedOrder_mul w)

/--
theorem `coeff_mul_prod_one_sub_of_lt_weightedOrder` / 定理 `coeff_mul_prod_one_sub_of_lt_weightedOrder`

English:
theorem coeff_mul_prod_one_sub_of_lt_weightedOrder
  statement: {R ι : Type*} [CommRing R] (d : σ ->₀ Nat)
  proof: by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.prod_empty, mul_one]
  | insert a s ha ih =>
    simp only [Finset.mem_insert, forall_eq_or_imp] at h
    rw [Finset.prod_insert ha]; rw [← mul_assoc]; rw [mul_right_comm]; rw [coeff_mul_left_one_sub_of_lt_wei

中文:
定理 coeff_mul_prod_one_sub_of_lt_weightedOrder
  结论: {R ι : 类型} [交换环 R] (d : σ ->₀ 自然数)
  证明: by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.prod_empty, mul_one]
  | insert a s ha ih =>
    simp only [Finset.mem_insert, forall_eq_or_imp] at h
    rw [Finset.prod_insert ha]; rw [← mul_assoc]; rw [mul_right_comm]; rw [coeff_mul_left_one_sub_of_lt_wei

Depends on / 依赖: Finset, Finset.induction_on, Finset.mem_insert, Finset.prod_empty, Finset.prod_insert, classical, coeff_mul_left_one_sub_of_lt_weightedOrder, forall_eq_or_imp, induction_on, insert, mem_insert, mul_assoc, mul_one, mul_right_comm, prod_empty, prod_insert
-/
theorem coeff_mul_prod_one_sub_of_lt_weightedOrder {R ι : Type*} [CommRing R] (d : σ ->₀ Nat)
    (s : Finset ι) (f : MvPowerSeries σ R) (g : ι -> MvPowerSeries σ R)
    (h : forall i in s, (weight w d) < weightedOrder w (g i)) :
    coeff d (f * ∏ i in s, (1 - g i)) = coeff d f := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.prod_empty, mul_one]
  | insert a s ha ih =>
    simp only [Finset.mem_insert, forall_eq_or_imp] at h
    rw [Finset.prod_insert ha]; rw [← mul_assoc]; rw [mul_right_comm]; rw [coeff_mul_left_one_sub_of_lt_weightedOrder w h.1]; rw [ih h.2]

@[simp]
/--
theorem `weightedOrder_neg` / 定理 `weightedOrder_neg`

English:
theorem weightedOrder_neg
  given: (f : MvPowerSeries σ R)
  statement: (-f).weightedOrder w = f.weightedOrder w
  proof: by
  by_contra! h
  have : f = 0 := by simpa using (weightedOrder_add_of_weightedOrder_ne w h).symm
  simp [this] at h

@[simp]

中文:
定理 weightedOrder_neg
  条件: (f : MvPowerSeries σ R)
  结论: (-f).weightedOrder w = f.weightedOrder w
  证明: by
  by_contra! h
  have : f = 0 := by simpa using (weightedOrder_add_of_weightedOrder_ne w h).symm
  simp [this] at h

@[simp]

Depends on / 依赖: weightedOrder_add_of_weightedOrder_ne
-/
theorem weightedOrder_neg (f : MvPowerSeries σ R) : (-f).weightedOrder w = f.weightedOrder w := by
  by_contra! h
  have : f = 0 := by simpa using (weightedOrder_add_of_weightedOrder_ne w h).symm
  simp [this] at h

@[simp]
/--
theorem `weightedOrder_toSubring` / 定理 `weightedOrder_toSubring`

English:
theorem weightedOrder_toSubring
  given: (p : MvPowerSeries σ R) (T : Subring R) (hp : forall n, p.coeff n in T)
  proof: by
  refine eq_of_le_of_ge ?_ ?_
  · refine le_weightedOrder w fun d hd => by
      simp [coeff_eq_zero_of_lt_weightedOrder w hd, ← p.coeff_toSubring T hp]
  · refine le_weightedOrder w fun d hd => by
      exact_mod_cast (coeff_toSubring p T hp) ▸ (coeff_eq_zero_of_lt_weightedOrder w hd)

中文:
定理 weightedOrder_toSubring
  条件: (p : MvPowerSeries σ R) (T : 子环 R) (hp : 对任意 n, p.coeff n in T)
  证明: by
  refine eq_of_le_of_ge ?_ ?_
  · refine le_weightedOrder w fun d hd => by
      simp [coeff_eq_zero_of_lt_weightedOrder w hd, ← p.coeff_toSubring T hp]
  · refine le_weightedOrder w fun d hd => by
      exact_mod_cast (coeff_toSubring p T hp) ▸ (coeff_eq_zero_of_lt_weightedOrder w hd)

Depends on / 依赖: coeff_eq_zero_of_lt_weightedOrder, coeff_toSubring, eq_of_le_of_ge, le_weightedOrder, p.coeff_toSubring
-/
theorem weightedOrder_toSubring (p : MvPowerSeries σ R) (T : Subring R) (hp : forall n, p.coeff n in T) :
    (p.toSubring T hp).weightedOrder w = p.weightedOrder w := by
  refine eq_of_le_of_ge ?_ ?_
  · refine le_weightedOrder w fun d hd => by
      simp [coeff_eq_zero_of_lt_weightedOrder w hd, ← p.coeff_toSubring T hp]
  · refine le_weightedOrder w fun d hd => by
      exact_mod_cast (coeff_toSubring p T hp) ▸ (coeff_eq_zero_of_lt_weightedOrder w hd)

end Ring

end WeightedOrder

section Order

variable {f g : MvPowerSeries σ R}

@[deprecated (since := "2026-01-06")]
alias eq_zero_iff_forall_coeff_eq_zero_and := eq_zero_iff_forall_coeff_zero

/--
theorem `ne_zero_iff_exists_coeff_ne_zero_and_degree` / 定理 `ne_zero_iff_exists_coeff_ne_zero_and_degree`

English:
theorem ne_zero_iff_exists_coeff_ne_zero_and_degree
  proof: by
  simp_rw [degree_eq_weight_one]
  exact ne_zero_iff_exists_coeff_ne_zero_and_weight (fun _ => 1)

中文:
定理 ne_zero_iff_存在_coeff_ne_zero_and_degree
  证明: by
  simp_rw [degree_eq_weight_one]
  exact ne_zero_iff_exists_coeff_ne_zero_and_weight (fun _ => 1)

Depends on / 依赖: degree_eq_weight_one, ne_zero_iff_exists_coeff_ne_zero_and_weight, simp_rw
-/
theorem ne_zero_iff_exists_coeff_ne_zero_and_degree :
    f != 0 ↔ (exists n : Nat, exists d : σ ->₀ Nat, coeff d f != 0 ∧ degree d = n) := by
  simp_rw [degree_eq_weight_one]
  exact ne_zero_iff_exists_coeff_ne_zero_and_weight (fun _ => 1)

/--
Definition of `order` / `order` 的定义

English:
definition order
  signature: (f : MvPowerSeries σ R)
  body: weightedOrder (fun _ => 1) f

@[simp]

中文:
定义 order
  签名: (f : MvPowerSeries σ R)
  定义体: weightedOrder (fun _ => 1) f

@[simp]

Depends on / 依赖: weightedOrder
-/
def order (f : MvPowerSeries σ R) : Nat∞ := weightedOrder (fun _ => 1) f

@[simp]
/--
theorem `order_zero` / 定理 `order_zero`

English:
theorem order_zero
  statement: (0 : MvPowerSeries σ R).order = ⊤
  proof: weightedOrder_zero _

中文:
定理 order_zero
  结论: (0 : MvPowerSeries σ R).order = ⊤
  证明: weightedOrder_zero _

Depends on / 依赖: weightedOrder_zero
-/
theorem order_zero : (0 : MvPowerSeries σ R).order = ⊤ :=
  weightedOrder_zero _

/--
theorem `ne_zero_iff_order_finite` / 定理 `ne_zero_iff_order_finite`

English:
theorem ne_zero_iff_order_finite
  statement: f != 0 ↔ f.order.toNat = f.order
  proof: ne_zero_iff_weightedOrder_finite 1

中文:
定理 ne_zero_iff_order_finite
  结论: f != 0 ↔ f.order.to自然数 = f.order
  证明: ne_zero_iff_weightedOrder_finite 1

Depends on / 依赖: ne_zero_iff_weightedOrder_finite
-/
theorem ne_zero_iff_order_finite : f != 0 ↔ f.order.toNat = f.order :=
  ne_zero_iff_weightedOrder_finite 1

/--
theorem `order_eq_top_iff` / 定理 `order_eq_top_iff`

English:
theorem order_eq_top_iff
  statement: f.order = ⊤ ↔ f = 0
  proof: weightedOrder_eq_top_iff _

中文:
定理 order_eq_top_iff
  结论: f.order = ⊤ ↔ f = 0
  证明: weightedOrder_eq_top_iff _
-/
@[simp] theorem order_eq_top_iff : f.order = ⊤ ↔ f = 0 :=
  weightedOrder_eq_top_iff _

/--
theorem `exists_coeff_ne_zero_and_order` / 定理 `exists_coeff_ne_zero_and_order`

English:
theorem exists_coeff_ne_zero_and_order
  given: (h : f.order.toNat = f.order)
  proof: by
  simp_rw [degree_eq_weight_one]
  exact exists_coeff_ne_zero_and_weightedOrder _ h

中文:
定理 存在_coeff_ne_zero_and_order
  条件: (h : f.order.to自然数 = f.order)
  证明: by
  simp_rw [degree_eq_weight_one]
  exact exists_coeff_ne_zero_and_weightedOrder _ h

Depends on / 依赖: degree_eq_weight_one, exists_coeff_ne_zero_and_weightedOrder, simp_rw
-/
theorem exists_coeff_ne_zero_and_order (h : f.order.toNat = f.order) :
    exists d : σ ->₀ Nat, coeff d f != 0 ∧ degree d = f.order := by
  simp_rw [degree_eq_weight_one]
  exact exists_coeff_ne_zero_and_weightedOrder _ h

/--
theorem `order_le` / 定理 `order_le`

English:
theorem order_le
  given: {d : σ ->₀ Nat} (h : coeff d f != 0)
  statement: f.order <= degree d
  proof: by
  rw [degree_eq_weight_one]
  exact weightedOrder_le _ h

中文:
定理 order_le
  条件: {d : σ ->₀ 自然数} (h : coeff d f != 0)
  结论: f.order <= degree d
  证明: by
  rw [degree_eq_weight_one]
  exact weightedOrder_le _ h

Depends on / 依赖: degree_eq_weight_one, weightedOrder_le
-/
theorem order_le {d : σ ->₀ Nat} (h : coeff d f != 0) : f.order <= degree d := by
  rw [degree_eq_weight_one]
  exact weightedOrder_le _ h

/--
theorem `coeff_of_lt_order` / 定理 `coeff_of_lt_order`

English:
theorem coeff_of_lt_order
  given: {d : σ ->₀ Nat} (h : degree d < f.order)
  proof: by
  rw [degree_eq_weight_one] at h
  exact coeff_eq_zero_of_lt_weightedOrder _ h

中文:
定理 coeff_of_lt_order
  条件: {d : σ ->₀ 自然数} (h : degree d < f.order)
  证明: by
  rw [degree_eq_weight_one] at h
  exact coeff_eq_zero_of_lt_weightedOrder _ h

Depends on / 依赖: coeff_eq_zero_of_lt_weightedOrder, degree_eq_weight_one
-/
theorem coeff_of_lt_order {d : σ ->₀ Nat} (h : degree d < f.order) :
    coeff d f = 0 := by
  rw [degree_eq_weight_one] at h
  exact coeff_eq_zero_of_lt_weightedOrder _ h

/--
theorem `nat_le_order` / 定理 `nat_le_order`

English:
theorem nat_le_order
  given: {n : Nat} (h : forall d, degree d < n -> coeff d f = 0)
  proof: by
  simp_rw [degree_eq_weight_one] at h
  exact nat_le_weightedOrder _ h

中文:
定理 nat_le_order
  条件: {n : 自然数} (h : 对任意 d, degree d < n -> coeff d f = 0)
  证明: by
  simp_rw [degree_eq_weight_one] at h
  exact nat_le_weightedOrder _ h

Depends on / 依赖: degree_eq_weight_one, nat_le_weightedOrder, simp_rw
-/
theorem nat_le_order {n : Nat} (h : forall d, degree d < n -> coeff d f = 0) :
    n <= f.order := by
  simp_rw [degree_eq_weight_one] at h
  exact nat_le_weightedOrder _ h

/--
theorem `le_order` / 定理 `le_order`

English:
theorem le_order
  given: {n : Nat∞} (h : forall d : σ ->₀ Nat, degree d < n -> coeff d f = 0)
  proof: by
  simp_rw [degree_eq_weight_one] at h
  exact le_weightedOrder _ h

中文:
定理 le_order
  条件: {n : 自然数∞} (h : 对任意 d : σ ->₀ 自然数, degree d < n -> coeff d f = 0)
  证明: by
  simp_rw [degree_eq_weight_one] at h
  exact le_weightedOrder _ h

Depends on / 依赖: degree_eq_weight_one, le_weightedOrder, simp_rw
-/
theorem le_order {n : Nat∞} (h : forall d : σ ->₀ Nat, degree d < n -> coeff d f = 0) :
    n <= f.order := by
  simp_rw [degree_eq_weight_one] at h
  exact le_weightedOrder _ h

/--
theorem `order_eq_nat` / 定理 `order_eq_nat`

English:
theorem order_eq_nat
  given: {n : Nat}
  proof: by
  simp_rw [degree_eq_weight_one]
  exact weightedOrder_eq_nat _

中文:
定理 order_eq_nat
  条件: {n : 自然数}
  证明: by
  simp_rw [degree_eq_weight_one]
  exact weightedOrder_eq_nat _

Depends on / 依赖: degree_eq_weight_one, simp_rw, weightedOrder_eq_nat
-/
theorem order_eq_nat {n : Nat} :
    f.order = n ↔
      (exists d, coeff d f != 0 ∧ degree d = n) ∧ forall d, degree d < n -> coeff d f = 0 := by
  simp_rw [degree_eq_weight_one]
  exact weightedOrder_eq_nat _

/--
theorem `order_monomial` / 定理 `order_monomial`

English:
theorem order_monomial
  given: {d : σ ->₀ Nat} {a : R} [Decidable (a = 0)]
  proof: by
  rw [degree_eq_weight_one]
  exact weightedOrder_monomial _

中文:
定理 order_monomial
  条件: {d : σ ->₀ 自然数} {a : R} [可判定 (a = 0)]
  证明: by
  rw [degree_eq_weight_one]
  exact weightedOrder_monomial _

Depends on / 依赖: degree_eq_weight_one, weightedOrder_monomial
-/
theorem order_monomial {d : σ ->₀ Nat} {a : R} [Decidable (a = 0)] :
    order (monomial d a) = if a = 0 then (⊤ : Nat∞) else ↑(degree d) := by
  rw [degree_eq_weight_one]
  exact weightedOrder_monomial _

/--
theorem `order_monomial_of_ne_zero` / 定理 `order_monomial_of_ne_zero`

English:
theorem order_monomial_of_ne_zero
  given: {d : σ ->₀ Nat} {a : R} (h : a != 0)
  proof: by
  rw [degree_eq_weight_one]
  exact weightedOrder_monomial_of_ne_zero _ h

中文:
定理 order_monomial_of_ne_zero
  条件: {d : σ ->₀ 自然数} {a : R} (h : a != 0)
  证明: by
  rw [degree_eq_weight_one]
  exact weightedOrder_monomial_of_ne_zero _ h

Depends on / 依赖: degree_eq_weight_one, weightedOrder_monomial_of_ne_zero
-/
theorem order_monomial_of_ne_zero {d : σ ->₀ Nat} {a : R} (h : a != 0) :
    order (monomial d a) = degree d := by
  rw [degree_eq_weight_one]
  exact weightedOrder_monomial_of_ne_zero _ h

/--
theorem `min_order_le_add` / 定理 `min_order_le_add`

English:
theorem min_order_le_add
  statement: min f.order g.order <= (f + g).order
  proof: min_weightedOrder_le_add _

中文:
定理 min_order_le_add
  结论: 最小值 f.order g.order <= (f + g).order
  证明: min_weightedOrder_le_add _

Depends on / 依赖: min_weightedOrder_le_add
-/
theorem min_order_le_add : min f.order g.order <= (f + g).order :=
  min_weightedOrder_le_add _

/--
theorem `order_add_of_order_ne` / 定理 `order_add_of_order_ne`

English:
theorem order_add_of_order_ne
  given: (h : f.order != g.order)
  proof: weightedOrder_add_of_weightedOrder_ne _ h

中文:
定理 order_add_of_order_ne
  条件: (h : f.order != g.order)
  证明: weightedOrder_add_of_weightedOrder_ne _ h

Depends on / 依赖: weightedOrder_add_of_weightedOrder_ne
-/
theorem order_add_of_order_ne (h : f.order != g.order) :
    order (f + g) = order f ⊓ order g :=
  weightedOrder_add_of_weightedOrder_ne _ h

/--
theorem `le_order_mul` / 定理 `le_order_mul`

English:
theorem le_order_mul
  statement: f.order + g.order <= order (f * g)
  proof: le_weightedOrder_mul _

alias order_mul_ge := le_order_mul

中文:
定理 le_order_mul
  结论: f.order + g.order <= order (f * g)
  证明: le_weightedOrder_mul _

alias order_mul_ge := le_order_mul

Depends on / 依赖: le_weightedOrder_mul
-/
theorem le_order_mul : f.order + g.order <= order (f * g) :=
  le_weightedOrder_mul _

alias order_mul_ge := le_order_mul

/--
theorem `le_order_pow` / 定理 `le_order_pow`

English:
theorem le_order_pow
  given: (n : Nat)
  statement: n • f.order <= (f ^ n).order
  proof: le_weightedOrder_pow _ n

中文:
定理 le_order_pow
  条件: (n : 自然数)
  结论: n • f.order <= (f ^ n).order
  证明: le_weightedOrder_pow _ n

Depends on / 依赖: le_weightedOrder_pow
-/
theorem le_order_pow (n : Nat) : n • f.order <= (f ^ n).order :=
  le_weightedOrder_pow _ n

/--
theorem `le_order_prod` / 定理 `le_order_prod`

English:
theorem le_order_prod
  statement: {R : Type*} [CommSemiring R] {ι : Type*}
  proof: le_weightedOrder_prod _ _ _

中文:
定理 le_order_prod
  结论: {R : 类型} [交换半环 R] {ι : 类型}
  证明: le_weightedOrder_prod _ _ _

Depends on / 依赖: le_weightedOrder_prod
-/
theorem le_order_prod {R : Type*} [CommSemiring R] {ι : Type*}
    (f : ι -> MvPowerSeries σ R) (s : Finset ι) : ∑ i in s, (f i).order <= (∏ i in s, f i).order :=
  le_weightedOrder_prod _ _ _

/--
theorem `one_le_order_iff_constCoeff_eq_zero` / 定理 `one_le_order_iff_constCoeff_eq_zero`

English:
theorem one_le_order_iff_constCoeff_eq_zero
  proof: by
  constructor
  · intro h
    apply coeff_of_lt_order
    simpa using Order.one_le_iff_pos.mp h
  · intro h
    refine MvPowerSeries.le_order fun d hd => ?_
    rw [Nat.cast_lt_one] at hd
    simp [(degree_eq_zero_iff d).mp hd, h]

中文:
定理 one_le_order_iff_constCoeff_eq_zero
  证明: by
  constructor
  · intro h
    apply coeff_of_lt_order
    simpa using Order.one_le_iff_pos.mp h
  · intro h
    refine MvPowerSeries.le_order fun d hd => ?_
    rw [Nat.cast_lt_one] at hd
    simp [(degree_eq_zero_iff d).mp hd, h]

Depends on / 依赖: MvPowerSeries, MvPowerSeries.le_order, Nat.cast_lt_one, Order.one_le_iff_pos.mp, cast_lt_one, coeff_of_lt_order, degree_eq_zero_iff, le_order, one_le_iff_pos
-/
theorem one_le_order_iff_constCoeff_eq_zero :
    1 <= f.order ↔ f.constantCoeff = 0 := by
  constructor
  · intro h
    apply coeff_of_lt_order
    simpa using Order.one_le_iff_pos.mp h
  · intro h
    refine MvPowerSeries.le_order fun d hd => ?_
    rw [Nat.cast_lt_one] at hd
    simp [(degree_eq_zero_iff d).mp hd, h]

/--
theorem `order_ne_zero_iff_constCoeff_eq_zero` / 定理 `order_ne_zero_iff_constCoeff_eq_zero`

English:
theorem order_ne_zero_iff_constCoeff_eq_zero
  proof: by
  rw [← Order.one_le_iff_ne_zero]; rw [one_le_order_iff_constCoeff_eq_zero]

中文:
定理 order_ne_zero_iff_constCoeff_eq_zero
  证明: by
  rw [← Order.one_le_iff_ne_zero]; rw [one_le_order_iff_constCoeff_eq_zero]

Depends on / 依赖: Order.one_le_iff_ne_zero, one_le_iff_ne_zero, one_le_order_iff_constCoeff_eq_zero
-/
theorem order_ne_zero_iff_constCoeff_eq_zero :
    f.order != 0 ↔ f.constantCoeff = 0 := by
  rw [← Order.one_le_iff_ne_zero]; rw [one_le_order_iff_constCoeff_eq_zero]

/--
theorem `le_order_pow_of_constantCoeff_eq_zero` / 定理 `le_order_pow_of_constantCoeff_eq_zero`

English:
theorem le_order_pow_of_constantCoeff_eq_zero
  given: (n : Nat) (hf : f.constantCoeff = 0)
  proof: by
  refine .trans ?_ (le_order_pow n)
  simpa using le_mul_of_one_le_right' (one_le_order_iff_constCoeff_eq_zero.mpr hf)

中文:
定理 le_order_pow_of_constantCoeff_eq_zero
  条件: (n : 自然数) (hf : f.constantCoeff = 0)
  证明: by
  refine .trans ?_ (le_order_pow n)
  simpa using le_mul_of_one_le_right' (one_le_order_iff_constCoeff_eq_zero.mpr hf)

Depends on / 依赖: le_mul_of_one_le_right, le_order_pow, one_le_order_iff_constCoeff_eq_zero, one_le_order_iff_constCoeff_eq_zero.mpr
-/
theorem le_order_pow_of_constantCoeff_eq_zero (n : Nat) (hf : f.constantCoeff = 0) :
    n <= (f ^ n).order := by
  refine .trans ?_ (le_order_pow n)
  simpa using le_mul_of_one_le_right' (one_le_order_iff_constCoeff_eq_zero.mpr hf)

/--
theorem `le_order_smul` / 定理 `le_order_smul`

English:
theorem le_order_smul
  given: {a : R}
  statement: f.order <= (a • f).order
  proof: le_weightedOrder_smul _

中文:
定理 le_order_smul
  条件: {a : R}
  结论: f.order <= (a • f).order
  证明: le_weightedOrder_smul _

Depends on / 依赖: le_weightedOrder_smul
-/
theorem le_order_smul {a : R} : f.order <= (a • f).order := le_weightedOrder_smul _

section

variable {S : Type*} [Semiring S]

/--
theorem `le_order_map` / 定理 `le_order_map`

English:
theorem le_order_map
  given: (f : R ->+* S) {φ : MvPowerSeries σ R}
  statement: φ.order <= (φ.map f).order
  proof: le_weightedOrder_map _ _

中文:
定理 le_order_map
  条件: (f : R ->+* S) {φ : MvPowerSeries σ R}
  结论: φ.order <= (φ.map f).order
  证明: le_weightedOrder_map _ _

Depends on / 依赖: le_weightedOrder_map
-/
theorem le_order_map (f : R ->+* S) {φ : MvPowerSeries σ R} : φ.order <= (φ.map f).order :=
  le_weightedOrder_map _ _

end

section Ring

variable {R : Type*} [Ring R] {f g : MvPowerSeries σ R}

/--
theorem `coeff_mul_left_one_sub_of_lt_order` / 定理 `coeff_mul_left_one_sub_of_lt_order`

English:
theorem coeff_mul_left_one_sub_of_lt_order
  given: (d : σ ->₀ Nat) (h : degree d < g.order)
  proof: by
  rw [degree_eq_weight_one] at h
  exact coeff_mul_left_one_sub_of_lt_weightedOrder _ h

中文:
定理 coeff_mul_left_one_sub_of_lt_order
  条件: (d : σ ->₀ 自然数) (h : degree d < g.order)
  证明: by
  rw [degree_eq_weight_one] at h
  exact coeff_mul_left_one_sub_of_lt_weightedOrder _ h

Depends on / 依赖: coeff_mul_left_one_sub_of_lt_weightedOrder, degree_eq_weight_one
-/
theorem coeff_mul_left_one_sub_of_lt_order (d : σ ->₀ Nat) (h : degree d < g.order) :
    coeff d (f * (1 - g)) = coeff d f := by
  rw [degree_eq_weight_one] at h
  exact coeff_mul_left_one_sub_of_lt_weightedOrder _ h

/--
theorem `coeff_mul_right_one_sub_of_lt_order` / 定理 `coeff_mul_right_one_sub_of_lt_order`

English:
theorem coeff_mul_right_one_sub_of_lt_order
  given: (d : σ ->₀ Nat) (h : degree d < g.order)
  proof: by
  rw [degree_eq_weight_one] at h
  exact coeff_mul_right_one_sub_of_lt_weightedOrder _ h

中文:
定理 coeff_mul_right_one_sub_of_lt_order
  条件: (d : σ ->₀ 自然数) (h : degree d < g.order)
  证明: by
  rw [degree_eq_weight_one] at h
  exact coeff_mul_right_one_sub_of_lt_weightedOrder _ h

Depends on / 依赖: coeff_mul_right_one_sub_of_lt_weightedOrder, degree_eq_weight_one
-/
theorem coeff_mul_right_one_sub_of_lt_order (d : σ ->₀ Nat) (h : degree d < g.order) :
    coeff d ((1 - g) * f) = coeff d f := by
  rw [degree_eq_weight_one] at h
  exact coeff_mul_right_one_sub_of_lt_weightedOrder _ h

/--
theorem `coeff_mul_prod_one_sub_of_lt_order` / 定理 `coeff_mul_prod_one_sub_of_lt_order`

English:
theorem coeff_mul_prod_one_sub_of_lt_order
  statement: {R ι : Type*} [CommRing R] (d : σ ->₀ Nat) (s : Finset ι)
  proof: by
  rw [degree_eq_weight_one]
  exact coeff_mul_prod_one_sub_of_lt_weightedOrder _ d s f g

@[simp]

中文:
定理 coeff_mul_prod_one_sub_of_lt_order
  结论: {R ι : 类型} [交换环 R] (d : σ ->₀ 自然数) (s : 有限集 ι)
  证明: by
  rw [degree_eq_weight_one]
  exact coeff_mul_prod_one_sub_of_lt_weightedOrder _ d s f g

@[simp]

Depends on / 依赖: coeff_mul_prod_one_sub_of_lt_weightedOrder, degree_eq_weight_one
-/
theorem coeff_mul_prod_one_sub_of_lt_order {R ι : Type*} [CommRing R] (d : σ ->₀ Nat) (s : Finset ι)
    (f : MvPowerSeries σ R) (g : ι -> MvPowerSeries σ R) :
    (forall i in s, degree d < order (g i)) -> coeff d (f * ∏ i in s, (1 - g i)) = coeff d f := by
  rw [degree_eq_weight_one]
  exact coeff_mul_prod_one_sub_of_lt_weightedOrder _ d s f g

@[simp]
/--
theorem `order_neg` / 定理 `order_neg`

English:
theorem order_neg
  given: (f : MvPowerSeries σ R)
  statement: (-f).order = f.order
  proof: weightedOrder_neg _ f

@[simp]

中文:
定理 order_neg
  条件: (f : MvPowerSeries σ R)
  结论: (-f).order = f.order
  证明: weightedOrder_neg _ f

@[simp]

Depends on / 依赖: weightedOrder_neg
-/
theorem order_neg (f : MvPowerSeries σ R) : (-f).order = f.order := weightedOrder_neg _ f

@[simp]
/--
theorem `order_toSubring` / 定理 `order_toSubring`

English:
theorem order_toSubring
  given: (p : MvPowerSeries σ R) (T : Subring R) (hp : forall n, p.coeff n in T)
  proof: by
  refine eq_of_le_of_ge ?_ ?_
  · exact le_order fun d hd => by simp [coeff_of_lt_order hd, ← p.coeff_toSubring T hp]
  · exact le_order fun d hd => by exact_mod_cast (coeff_toSubring p T hp) ▸ (coeff_of_lt_order hd)

中文:
定理 order_toSubring
  条件: (p : MvPowerSeries σ R) (T : 子环 R) (hp : 对任意 n, p.coeff n in T)
  证明: by
  refine eq_of_le_of_ge ?_ ?_
  · exact le_order fun d hd => by simp [coeff_of_lt_order hd, ← p.coeff_toSubring T hp]
  · exact le_order fun d hd => by exact_mod_cast (coeff_toSubring p T hp) ▸ (coeff_of_lt_order hd)

Depends on / 依赖: coeff_of_lt_order, coeff_toSubring, eq_of_le_of_ge, le_order, p.coeff_toSubring
-/
theorem order_toSubring (p : MvPowerSeries σ R) (T : Subring R) (hp : forall n, p.coeff n in T) :
    (p.toSubring T hp).order = p.order := by
  refine eq_of_le_of_ge ?_ ?_
  · exact le_order fun d hd => by simp [coeff_of_lt_order hd, ← p.coeff_toSubring T hp]
  · exact le_order fun d hd => by exact_mod_cast (coeff_toSubring p T hp) ▸ (coeff_of_lt_order hd)

end Ring

end Order

section HomogeneousComponent

variable (w : σ -> Nat)

/--
Definition of `IsWeightedHomogeneous` / `IsWeightedHomogeneous` 的定义

English:
definition IsWeightedHomogeneous
  signature: (f : MvPowerSeries σ R) (p : Nat)
  body: forall {d : σ ->₀ Nat}, f.coeff d != 0 -> weight w d = p

中文:
定义 IsWeightedHomogeneous
  签名: (f : MvPowerSeries σ R) (p : 自然数)
  定义体: forall {d : σ ->₀ Nat}, f.coeff d != 0 -> weight w d = p

Depends on / 依赖: f.coeff, weight
-/
def IsWeightedHomogeneous (f : MvPowerSeries σ R) (p : Nat) : Prop :=
  forall {d : σ ->₀ Nat}, f.coeff d != 0 -> weight w d = p

variable {w} in
/--
theorem `IsWeightedHomogeneous.coeff_eq_zero` / 定理 `IsWeightedHomogeneous.coeff_eq_zero`

English:
theorem IsWeightedHomogeneous.coeff_eq_zero
  statement: {f : MvPowerSeries σ R} {p : Nat}
  proof: by
  simpa [Classical.not_not] using mt (@hf d) hd

中文:
定理 IsWeightedHomogeneous.coeff_eq_zero
  结论: {f : MvPowerSeries σ R} {p : 自然数}
  证明: by
  simpa [Classical.not_not] using mt (@hf d) hd

Depends on / 依赖: Classical, Classical.not_not, not_not
-/
theorem IsWeightedHomogeneous.coeff_eq_zero {f : MvPowerSeries σ R} {p : Nat}
    (hf : f.IsWeightedHomogeneous w p) {d : σ ->₀ Nat} (hd : weight w d != p) :
    f.coeff d = 0 := by
  simpa [Classical.not_not] using mt (@hf d) hd

variable {w} in
/--
theorem `IsWeightedHomogeneous.add` / 定理 `IsWeightedHomogeneous.add`

English:
theorem IsWeightedHomogeneous.add
  statement: {f g : MvPowerSeries σ R} {p : Nat}
  proof: fun {d} => by
  rw [not_imp_comm]
  intro hd
  rw [map_add]; rw [hf.coeff_eq_zero hd]; rw [hg.coeff_eq_zero hd]; rw [add_zero]

中文:
定理 IsWeightedHomogeneous.add
  结论: {f g : MvPowerSeries σ R} {p : 自然数}
  证明: fun {d} => by
  rw [not_imp_comm]
  intro hd
  rw [map_add]; rw [hf.coeff_eq_zero hd]; rw [hg.coeff_eq_zero hd]; rw [add_zero]
-/
protected theorem IsWeightedHomogeneous.add {f g : MvPowerSeries σ R} {p : Nat}
    (hf : f.IsWeightedHomogeneous w p) (hg : g.IsWeightedHomogeneous w p) :
    (f + g).IsWeightedHomogeneous w p := fun {d} => by
  rw [not_imp_comm]
  intro hd
  rw [map_add]; rw [hf.coeff_eq_zero hd]; rw [hg.coeff_eq_zero hd]; rw [add_zero]

variable {w} in
/--
theorem `IsWeightedHomogeneous.mul` / 定理 `IsWeightedHomogeneous.mul`

English:
theorem IsWeightedHomogeneous.mul
  statement: {f g : MvPowerSeries σ R} {p q : Nat}
  proof: fun {d} => by
  classical
  rw [not_imp_comm]
  intro hd
  rw [coeff_mul]
  apply Finset.sum_eq_zero
  intro x hx
  rw [Finset.mem_antidiagonal] at hx
  suffices weight w x.1 != p ∨ weight w x.2 != q by
    rcases this with hp | hq
    · rw [hf.coeff_eq_zero hp, zero_mul]
    · rw [hg.coeff_eq_zero 

中文:
定理 IsWeightedHomogeneous.mul
  结论: {f g : MvPowerSeries σ R} {p q : 自然数}
  证明: fun {d} => by
  classical
  rw [not_imp_comm]
  intro hd
  rw [coeff_mul]
  apply Finset.sum_eq_zero
  intro x hx
  rw [Finset.mem_antidiagonal] at hx
  suffices weight w x.1 != p ∨ weight w x.2 != q by
    rcases this with hp | hq
    · rw [hf.coeff_eq_zero hp, zero_mul]
    · rw [hg.coeff_eq_zero 
-/
protected theorem IsWeightedHomogeneous.mul {f g : MvPowerSeries σ R} {p q : Nat}
    (hf : f.IsWeightedHomogeneous w p) (hg : g.IsWeightedHomogeneous w q) :
    (f * g).IsWeightedHomogeneous w (p + q) := fun {d} => by
  classical
  rw [not_imp_comm]
  intro hd
  rw [coeff_mul]
  apply Finset.sum_eq_zero
  intro x hx
  rw [Finset.mem_antidiagonal] at hx
  suffices weight w x.1 != p ∨ weight w x.2 != q by
    rcases this with hp | hq
    · rw [hf.coeff_eq_zero hp, zero_mul]
    · rw [hg.coeff_eq_zero hq, mul_zero]
  rw [← not_and_or]
  rintro ⟨hp, hq⟩
  apply hd
  rw [← hx]; rw [map_add]; rw [hp]; rw [hq]

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `weightedHomogeneousComponent` / `weightedHomogeneousComponent` 的定义

English:
definition weightedHomogeneousComponent
  signature: (p : Nat)
  body: if weight w d = p then coeff d f else 0
  map_add' f g := by
    ext d
    simp only [map_add, coeff_apply]
    split_ifs with h
    · rfl
    · rw [add_zero]
  map_smul' a f := by
    ext d
    simp only [map_smul,
      smul_eq_mul, RingHom.id_apply, coeff_apply, mul_ite, mul_zero]

中文:
定义 weightedHomogeneousComponent
  签名: (p : 自然数)
  定义体: if weight w d = p then coeff d f else 0
  map_add' f g := by
    ext d
    simp only [map_add, coeff_apply]
    split_ifs with h
    · rfl
    · rw [add_zero]
  map_smul' a f := by
    ext d
    simp only [map_smul,
      smul_eq_mul, RingHom.id_apply, coeff_apply, mul_ite, mul_zero]

Depends on / 依赖: weight
-/
def weightedHomogeneousComponent (p : Nat) : MvPowerSeries σ R ->ₗ[R] MvPowerSeries σ R where
  toFun f d := if weight w d = p then coeff d f else 0
  map_add' f g := by
    ext d
    simp only [map_add, coeff_apply]
    split_ifs with h
    · rfl
    · rw [add_zero]
  map_smul' a f := by
    ext d
    simp only [map_smul,
      smul_eq_mul, RingHom.id_apply, coeff_apply, mul_ite, mul_zero]

/--
theorem `coeff_weightedHomogeneousComponent` / 定理 `coeff_weightedHomogeneousComponent`

English:
theorem coeff_weightedHomogeneousComponent
  given: (p : Nat) (d : σ ->₀ Nat) (f : MvPowerSeries σ R)
  proof: rfl

中文:
定理 coeff_weightedHomogeneousComponent
  条件: (p : 自然数) (d : σ ->₀ 自然数) (f : MvPowerSeries σ R)
  证明: rfl
-/
theorem coeff_weightedHomogeneousComponent (p : Nat) (d : σ ->₀ Nat) (f : MvPowerSeries σ R) :
    coeff d (weightedHomogeneousComponent w p f) =
      if weight w d = p then coeff d f else 0 :=
  rfl

variable {w} in
/--
theorem `weightedHomogeneousComponent_of_lt_weightedOrder_eq_zero` / 定理 `weightedHomogeneousComponent_of_lt_weightedOrder_eq_zero`

English:
theorem weightedHomogeneousComponent_of_lt_weightedOrder_eq_zero
  proof: by
  ext d
  rw [coeff_weightedHomogeneousComponent]
  split_ifs with hd
  · rw [coeff_zero]
    apply coeff_eq_zero_of_lt_weightedOrder w
    rw [hd]
    exact hf
  · rw [map_zero]

中文:
定理 weightedHomogeneousComponent_of_lt_weightedOrder_eq_zero
  证明: by
  ext d
  rw [coeff_weightedHomogeneousComponent]
  split_ifs with hd
  · rw [coeff_zero]
    apply coeff_eq_zero_of_lt_weightedOrder w
    rw [hd]
    exact hf
  · rw [map_zero]

Depends on / 依赖: coeff_eq_zero_of_lt_weightedOrder, coeff_weightedHomogeneousComponent, coeff_zero, map_zero, split_ifs
-/
theorem weightedHomogeneousComponent_of_lt_weightedOrder_eq_zero
    {f : MvPowerSeries σ R} {p : Nat} (hf : p < f.weightedOrder w) :
    f.weightedHomogeneousComponent w p = 0 := by
  ext d
  rw [coeff_weightedHomogeneousComponent]
  split_ifs with hd
  · rw [coeff_zero]
    apply coeff_eq_zero_of_lt_weightedOrder w
    rw [hd]
    exact hf
  · rw [map_zero]

variable {w} in
/--
theorem `weightedHomogeneousComponent_of_weightedOrder` / 定理 `weightedHomogeneousComponent_of_weightedOrder`

English:
theorem weightedHomogeneousComponent_of_weightedOrder
  proof: by
  intro hf'
  obtain ⟨d, hd⟩ := f.exists_coeff_ne_zero_and_weightedOrder w (by rw [← hf, toNat_natCast])
  simp only [ne_eq, ← hf, Nat.cast_inj] at hd
  apply hd.1
  rw [MvPowerSeries.ext_iff] at hf'
  specialize hf' d
  simp only [coeff_weightedHomogeneousComponent, coeff_zero, ite_eq_right_iff]

中文:
定理 weightedHomogeneousComponent_of_weightedOrder
  证明: by
  intro hf'
  obtain ⟨d, hd⟩ := f.exists_coeff_ne_zero_and_weightedOrder w (by rw [← hf, toNat_natCast])
  simp only [ne_eq, ← hf, Nat.cast_inj] at hd
  apply hd.1
  rw [MvPowerSeries.ext_iff] at hf'
  specialize hf' d
  simp only [coeff_weightedHomogeneousComponent, coeff_zero, ite_eq_right_iff]

Depends on / 依赖: MvPowerSeries, MvPowerSeries.ext_iff, Nat.cast_inj, cast_inj, coeff_weightedHomogeneousComponent, coeff_zero, exists_coeff_ne_zero_and_weightedOrder, ext_iff, f.exists_coeff_ne_zero_and_weightedOrder, ite_eq_right_iff, ne_eq, specialize, toNat_natCast
-/
theorem weightedHomogeneousComponent_of_weightedOrder
    {f : MvPowerSeries σ R} {p : Nat} (hf : p = f.weightedOrder w) :
    f.weightedHomogeneousComponent w p != 0 := by
  intro hf'
  obtain ⟨d, hd⟩ := f.exists_coeff_ne_zero_and_weightedOrder w (by rw [← hf, toNat_natCast])
  simp only [ne_eq, ← hf, Nat.cast_inj] at hd
  apply hd.1
  rw [MvPowerSeries.ext_iff] at hf'
  specialize hf' d
  simp only [coeff_weightedHomogeneousComponent, coeff_zero, ite_eq_right_iff] at hf'
  exact hf' hd.2

/--
theorem `isWeightedHomogeneous_weightedHomogeneousComponent` / 定理 `isWeightedHomogeneous_weightedHomogeneousComponent`

English:
theorem isWeightedHomogeneous_weightedHomogeneousComponent
  given: (f : MvPowerSeries σ R) (p : Nat)
  proof: fun {d} => by
  rw [not_imp_comm]
  intro hd
  rw [coeff_weightedHomogeneousComponent]; rw [if_neg hd]

中文:
定理 isWeightedHomogeneous_weightedHomogeneousComponent
  条件: (f : MvPowerSeries σ R) (p : 自然数)
  证明: fun {d} => by
  rw [not_imp_comm]
  intro hd
  rw [coeff_weightedHomogeneousComponent]; rw [if_neg hd]

Depends on / 依赖: coeff_weightedHomogeneousComponent, if_neg, not_imp_comm
-/
theorem isWeightedHomogeneous_weightedHomogeneousComponent (f : MvPowerSeries σ R) (p : Nat) :
    IsWeightedHomogeneous w (f.weightedHomogeneousComponent w p) p := fun {d} => by
  rw [not_imp_comm]
  intro hd
  rw [coeff_weightedHomogeneousComponent]; rw [if_neg hd]

variable {w} in
/--
theorem `isWeightedHomogeneous_iff_eq_weightedHomogeneousComponent` / 定理 `isWeightedHomogeneous_iff_eq_weightedHomogeneousComponent`

English:
theorem isWeightedHomogeneous_iff_eq_weightedHomogeneousComponent
  proof: by
  constructor
  · intro hf
    ext d
    rw [coeff_weightedHomogeneousComponent]
    split_ifs with hd
    · rfl
    · exact hf.coeff_eq_zero hd
  · intro hf
    rw [hf]
    exact isWeightedHomogeneous_weightedHomogeneousComponent w f p

中文:
定理 isWeightedHomogeneous_iff_eq_weightedHomogeneousComponent
  证明: by
  constructor
  · intro hf
    ext d
    rw [coeff_weightedHomogeneousComponent]
    split_ifs with hd
    · rfl
    · exact hf.coeff_eq_zero hd
  · intro hf
    rw [hf]
    exact isWeightedHomogeneous_weightedHomogeneousComponent w f p

Depends on / 依赖: coeff_eq_zero, coeff_weightedHomogeneousComponent, hf.coeff_eq_zero, isWeightedHomogeneous_weightedHomogeneousComponent, split_ifs
-/
theorem isWeightedHomogeneous_iff_eq_weightedHomogeneousComponent
    {f : MvPowerSeries σ R} {p : Nat} :
    IsWeightedHomogeneous w f p ↔ f = f.weightedHomogeneousComponent w p := by
  constructor
  · intro hf
    ext d
    rw [coeff_weightedHomogeneousComponent]
    split_ifs with hd
    · rfl
    · exact hf.coeff_eq_zero hd
  · intro hf
    rw [hf]
    exact isWeightedHomogeneous_weightedHomogeneousComponent w f p

variable {w} in
/--
theorem `weightedHomogeneousComponent_mul_of_le_weightedOrder` / 定理 `weightedHomogeneousComponent_mul_of_le_weightedOrder`

English:
theorem weightedHomogeneousComponent_mul_of_le_weightedOrder
  statement: {f g : MvPowerSeries σ R} {p q : Nat}
  proof: by
  classical
  ext d
  rw [coeff_weightedHomogeneousComponent]
  split_ifs with hd
  · apply Finset.sum_congr rfl
    intro x hx
    rw [Finset.mem_antidiagonal] at hx
    rw [← hx]; rw [map_add] at hd
    simp only [coeff_weightedHomogeneousComponent]
    rcases trichotomy_of_add_eq_add hd with h

中文:
定理 weightedHomogeneousComponent_mul_of_le_weightedOrder
  结论: {f g : MvPowerSeries σ R} {p q : 自然数}
  证明: by
  classical
  ext d
  rw [coeff_weightedHomogeneousComponent]
  split_ifs with hd
  · apply Finset.sum_congr rfl
    intro x hx
    rw [Finset.mem_antidiagonal] at hx
    rw [← hx]; rw [map_add] at hd
    simp only [coeff_weightedHomogeneousComponent]
    rcases trichotomy_of_add_eq_add hd with h

Depends on / 依赖: ENat.natCast_lt_natCast, Finset, Finset.mem_antidiagonal, Finset.sum_congr, classical, coeff_eq_zero_of_lt_weightedOrder, coeff_weightedHomogeneousComponent, if_neg, if_pos, lt_of_lt_of_le, map_add, mem_antidiagonal, mul_zero, natCast_lt_natCast, ne_of_lt, split_ifs, sum_congr, trichotomy_of_add_eq_add, zero_mul
-/
theorem weightedHomogeneousComponent_mul_of_le_weightedOrder {f g : MvPowerSeries σ R} {p q : Nat}
    (hf : p <= f.weightedOrder w) (hg : q <= g.weightedOrder w) :
    weightedHomogeneousComponent w (p + q) (f * g) =
      weightedHomogeneousComponent w p f * weightedHomogeneousComponent w q g := by
  classical
  ext d
  rw [coeff_weightedHomogeneousComponent]
  split_ifs with hd
  · apply Finset.sum_congr rfl
    intro x hx
    rw [Finset.mem_antidiagonal] at hx
    rw [← hx]; rw [map_add] at hd
    simp only [coeff_weightedHomogeneousComponent]
    rcases trichotomy_of_add_eq_add hd with h | h | h
    · rw [if_pos h.1, if_pos h.2]
    · rw [if_neg (ne_of_lt h), zero_mul]
      rw [← ENat.natCast_lt_natCast] at h
      rw [coeff_eq_zero_of_lt_weightedOrder w (lt_of_lt_of_le h hf)]; rw [zero_mul]
    · rw [if_neg (ne_of_lt h), mul_zero]
      rw [← ENat.natCast_lt_natCast] at h
      rw [coeff_eq_zero_of_lt_weightedOrder w (lt_of_lt_of_le h hg)]; rw [mul_zero]
  · symm
    apply IsWeightedHomogeneous.coeff_eq_zero _ hd
    exact IsWeightedHomogeneous.mul
      (isWeightedHomogeneous_weightedHomogeneousComponent w f p)
      (isWeightedHomogeneous_weightedHomogeneousComponent w g q)

/--
Definition of `IsHomogeneous` / `IsHomogeneous` 的定义

English:
definition IsHomogeneous
  signature: (f : MvPowerSeries σ R) (p : Nat)
  body: IsWeightedHomogeneous 1 f p

中文:
定义 IsHomogeneous
  签名: (f : MvPowerSeries σ R) (p : 自然数)
  定义体: IsWeightedHomogeneous 1 f p

Depends on / 依赖: IsWeightedHomogeneous
-/
def IsHomogeneous (f : MvPowerSeries σ R) (p : Nat) : Prop :=
  IsWeightedHomogeneous 1 f p

/--
theorem `IsHomogeneous.coeff_eq_zero` / 定理 `IsHomogeneous.coeff_eq_zero`

English:
theorem IsHomogeneous.coeff_eq_zero
  statement: {f : MvPowerSeries σ R} {p : Nat}
  proof: by
  apply IsWeightedHomogeneous.coeff_eq_zero hf
  rwa [degree_eq_weight_one] at hd

中文:
定理 IsHomogeneous.coeff_eq_zero
  结论: {f : MvPowerSeries σ R} {p : 自然数}
  证明: by
  apply IsWeightedHomogeneous.coeff_eq_zero hf
  rwa [degree_eq_weight_one] at hd

Depends on / 依赖: IsWeightedHomogeneous, IsWeightedHomogeneous.coeff_eq_zero, coeff_eq_zero, degree_eq_weight_one
-/
theorem IsHomogeneous.coeff_eq_zero {f : MvPowerSeries σ R} {p : Nat}
    (hf : f.IsHomogeneous p) {d : σ ->₀ Nat} (hd : degree d != p) :
    f.coeff d = 0 := by
  apply IsWeightedHomogeneous.coeff_eq_zero hf
  rwa [degree_eq_weight_one] at hd

/--
theorem `IsHomogeneous.add` / 定理 `IsHomogeneous.add`

English:
theorem IsHomogeneous.add
  statement: {f g : MvPowerSeries σ R} {p : Nat}
  proof: IsWeightedHomogeneous.add hf hg

中文:
定理 IsHomogeneous.add
  结论: {f g : MvPowerSeries σ R} {p : 自然数}
  证明: IsWeightedHomogeneous.add hf hg
-/
protected theorem IsHomogeneous.add {f g : MvPowerSeries σ R} {p : Nat}
    (hf : f.IsHomogeneous p) (hg : g.IsHomogeneous p) :
    (f + g).IsHomogeneous p :=
  IsWeightedHomogeneous.add hf hg

/--
theorem `IsHomogeneous.mul` / 定理 `IsHomogeneous.mul`

English:
theorem IsHomogeneous.mul
  statement: {f g : MvPowerSeries σ R} {p q : Nat}
  proof: IsWeightedHomogeneous.mul hf hg

中文:
定理 IsHomogeneous.mul
  结论: {f g : MvPowerSeries σ R} {p q : 自然数}
  证明: IsWeightedHomogeneous.mul hf hg
-/
protected theorem IsHomogeneous.mul {f g : MvPowerSeries σ R} {p q : Nat}
    (hf : f.IsHomogeneous p) (hg : g.IsHomogeneous q) :
    (f * g).IsHomogeneous (p + q) :=
  IsWeightedHomogeneous.mul hf hg

/--
Definition of `homogeneousComponent` / `homogeneousComponent` 的定义

English:
definition homogeneousComponent
  signature: (p : Nat)
  body: weightedHomogeneousComponent 1 p

中文:
定义 homogeneousComponent
  签名: (p : 自然数)
  定义体: weightedHomogeneousComponent 1 p

Depends on / 依赖: weightedHomogeneousComponent
-/
def homogeneousComponent (p : Nat) : MvPowerSeries σ R ->ₗ[R] MvPowerSeries σ R :=
  weightedHomogeneousComponent 1 p

/--
theorem `coeff_homogeneousComponent` / 定理 `coeff_homogeneousComponent`

English:
theorem coeff_homogeneousComponent
  given: (p : Nat) (d : σ ->₀ Nat) (f : MvPowerSeries σ R)
  proof: by
  rw [degree_eq_weight_one]
  exact coeff_weightedHomogeneousComponent 1 p d f

中文:
定理 coeff_homogeneousComponent
  条件: (p : 自然数) (d : σ ->₀ 自然数) (f : MvPowerSeries σ R)
  证明: by
  rw [degree_eq_weight_one]
  exact coeff_weightedHomogeneousComponent 1 p d f

Depends on / 依赖: coeff_weightedHomogeneousComponent, degree_eq_weight_one
-/
theorem coeff_homogeneousComponent (p : Nat) (d : σ ->₀ Nat) (f : MvPowerSeries σ R) :
    coeff d (homogeneousComponent p f) =
      if degree d = p then coeff d f else 0 := by
  rw [degree_eq_weight_one]
  exact coeff_weightedHomogeneousComponent 1 p d f

/--
theorem `homogeneousComponent_of_lt_order_eq_zero` / 定理 `homogeneousComponent_of_lt_order_eq_zero`

English:
theorem homogeneousComponent_of_lt_order_eq_zero
  proof: weightedHomogeneousComponent_of_lt_weightedOrder_eq_zero hf

中文:
定理 homogeneousComponent_of_lt_order_eq_zero
  证明: weightedHomogeneousComponent_of_lt_weightedOrder_eq_zero hf

Depends on / 依赖: weightedHomogeneousComponent_of_lt_weightedOrder_eq_zero
-/
theorem homogeneousComponent_of_lt_order_eq_zero
    {f : MvPowerSeries σ R} {p : Nat} (hf : p < f.order) :
    f.homogeneousComponent p = 0 :=
  weightedHomogeneousComponent_of_lt_weightedOrder_eq_zero hf

/--
theorem `homogeneousComponent_of_order` / 定理 `homogeneousComponent_of_order`

English:
theorem homogeneousComponent_of_order
  proof: weightedHomogeneousComponent_of_weightedOrder hf

中文:
定理 homogeneousComponent_of_order
  证明: weightedHomogeneousComponent_of_weightedOrder hf

Depends on / 依赖: weightedHomogeneousComponent_of_weightedOrder
-/
theorem homogeneousComponent_of_order
    {f : MvPowerSeries σ R} {p : Nat} (hf : p = f.order) :
    f.homogeneousComponent p != 0 :=
  weightedHomogeneousComponent_of_weightedOrder hf

/--
theorem `isHomogeneous_homogeneousComponent` / 定理 `isHomogeneous_homogeneousComponent`

English:
theorem isHomogeneous_homogeneousComponent
  given: (f : MvPowerSeries σ R) (p : Nat)
  proof: isWeightedHomogeneous_weightedHomogeneousComponent 1 f p

中文:
定理 isHomogeneous_homogeneousComponent
  条件: (f : MvPowerSeries σ R) (p : 自然数)
  证明: isWeightedHomogeneous_weightedHomogeneousComponent 1 f p

Depends on / 依赖: isWeightedHomogeneous_weightedHomogeneousComponent
-/
theorem isHomogeneous_homogeneousComponent (f : MvPowerSeries σ R) (p : Nat) :
    IsHomogeneous (f.homogeneousComponent p) p :=
  isWeightedHomogeneous_weightedHomogeneousComponent 1 f p

/--
theorem `isHomogeneous_iff_eq_homogeneousComponent` / 定理 `isHomogeneous_iff_eq_homogeneousComponent`

English:
theorem isHomogeneous_iff_eq_homogeneousComponent
  proof: isWeightedHomogeneous_iff_eq_weightedHomogeneousComponent

中文:
定理 isHomogeneous_iff_eq_homogeneousComponent
  证明: isWeightedHomogeneous_iff_eq_weightedHomogeneousComponent

Depends on / 依赖: isWeightedHomogeneous_iff_eq_weightedHomogeneousComponent
-/
theorem isHomogeneous_iff_eq_homogeneousComponent
    {f : MvPowerSeries σ R} {p : Nat} :
    IsHomogeneous f p ↔ f = f.homogeneousComponent p :=
  isWeightedHomogeneous_iff_eq_weightedHomogeneousComponent

/--
theorem `homogeneousComponent_mul_of_le_order` / 定理 `homogeneousComponent_mul_of_le_order`

English:
theorem homogeneousComponent_mul_of_le_order
  statement: {f g : MvPowerSeries σ R} {p q : Nat}
  proof: weightedHomogeneousComponent_mul_of_le_weightedOrder hf hg

中文:
定理 homogeneousComponent_mul_of_le_order
  结论: {f g : MvPowerSeries σ R} {p q : 自然数}
  证明: weightedHomogeneousComponent_mul_of_le_weightedOrder hf hg

Depends on / 依赖: weightedHomogeneousComponent_mul_of_le_weightedOrder
-/
theorem homogeneousComponent_mul_of_le_order {f g : MvPowerSeries σ R} {p q : Nat}
    (hf : p <= f.order) (hg : q <= g.order) :
    homogeneousComponent (p + q) (f * g) =
      homogeneousComponent p f * homogeneousComponent q g :=
  weightedHomogeneousComponent_mul_of_le_weightedOrder hf hg

end HomogeneousComponent

end

end MvPowerSeries
