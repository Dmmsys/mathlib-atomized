/-
Copyright (c) 2024 María Inés de Frutos-Fernández, Filippo A. E. Nuccio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández, Filippo A. E. Nuccio
-/
module

public import Mathlib.FieldTheory.Minpoly.Field
public import Mathlib.FieldTheory.Minpoly.Finite
public import Mathlib.RingTheory.Valuation.Basic

/-!
# Minimal polynomials.

We prove some results about valuations of zero coefficients of minimal polynomials.

Let `K` be a field with a valuation `v` and let `L` be a field extension of `K`.

## Main statements

* `coeff_zero_minpoly` : for `x ∈ K` the valuation of the zeroth coefficient of the minimal
  polynomial of `algebraMap K L x` over `K` is equal to the valuation of `x`.
* `pow_coeff_zero_ne_zero_of_unit` : for any unit `x : Lˣ`, we prove that a certain power of the
  valuation of zeroth coefficient of the minimal polynomial of `x` over `K` is nonzero. This lemma
  is helpful for defining the valuation on `L` inducing `v`.
-/

public section

open Module minpoly Polynomial

variable {K : Type*} [Field K] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
  (v : Valuation K Γ₀) (L : Type*) [Field L] [Algebra K L]

namespace Valuation

/-- For `x ∈ K` the valuation of the zeroth coefficient of the minimal polynomial
of `algebraMap K L x` over `K` is equal to the valuation of `x`. -/
@[simp]
/--
theorem `coeff_zero_minpoly` / 定理 `coeff_zero_minpoly`

English:
theorem coeff_zero_minpoly
  given: (x : K)
  statement: v ((minpoly K (algebraMap K L x)).coeff 0) = v x
  proof: by
  rw [minpoly.eq_X_sub_C]; rw [coeff_sub]; rw [coeff_X_zero]; rw [coeff_C_zero]; rw [zero_sub]; rw [Valuation.map_neg]

中文:
定理 coeff_zero_minpoly
  条件: (x : K)
  结论: v ((minpoly K (algebraMap K L x)).coeff 0) = v x
  证明: by
  rw [minpoly.eq_X_sub_C]; rw [coeff_sub]; rw [coeff_X_zero]; rw [coeff_C_zero]; rw [zero_sub]; rw [Valuation.map_neg]

Depends on / 依赖: Valuation, Valuation.map_neg, coeff_C_zero, coeff_X_zero, coeff_sub, eq_X_sub_C, map_neg, minpoly, minpoly.eq_X_sub_C, zero_sub
-/
theorem coeff_zero_minpoly (x : K) : v ((minpoly K (algebraMap K L x)).coeff 0) = v x := by
  rw [minpoly.eq_X_sub_C]; rw [coeff_sub]; rw [coeff_X_zero]; rw [coeff_C_zero]; rw [zero_sub]; rw [Valuation.map_neg]

variable {L}

/--
theorem `pow_coeff_zero_ne_zero_of_unit` / 定理 `pow_coeff_zero_ne_zero_of_unit`

English:
theorem pow_coeff_zero_ne_zero_of_unit
  given: [FiniteDimensional K L] (x : L) (hx : IsUnit x)
  proof: by
  have h_alg : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
  have hx₀ : IsIntegral K x := (Algebra.IsAlgebraic.isAlgebraic x).isIntegral
  have hdeg := Nat.div_pos (natDegree_le x) (natDegree_pos hx₀)
  rw [ne_eq]; rw [pow_eq_zero_iff hdeg.ne.symm]; rw [Valuation.zero_iff]
  exact coeff_zero_ne_zero hx₀ hx.ne_zero

中文:
定理 pow_coeff_zero_ne_zero_of_unit
  条件: [有限维 K L] (x : L) (hx : 是单位 x)
  证明: by
  have h_alg : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
  have hx₀ : IsIntegral K x := (Algebra.IsAlgebraic.isAlgebraic x).isIntegral
  have hdeg := Nat.div_pos (natDegree_le x) (natDegree_pos hx₀)
  rw [ne_eq]; rw [pow_eq_zero_iff hdeg.ne.symm]; rw [Valuation.zero_iff]
  exact coeff_zero_ne_zero hx₀ hx.ne_zero

Depends on / 依赖: Algebra, Algebra.IsAlgebraic, Algebra.IsAlgebraic.isAlgebraic, Algebra.IsAlgebraic.of_finite, IsAlgebraic, IsIntegral, Nat.div_pos, Valuation, Valuation.zero_iff, coeff_zero_ne_zero, div_pos, h_alg, hdeg.ne.symm, hx.ne_zero, isAlgebraic, isIntegral, natDegree_le, natDegree_pos, ne_eq, ne_zero
-/
theorem pow_coeff_zero_ne_zero_of_unit [FiniteDimensional K L] (x : L) (hx : IsUnit x) :
    v ((minpoly K x).coeff 0) ^ (finrank K L / (minpoly K x).natDegree) != (0 : Γ₀) := by
  have h_alg : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
  have hx₀ : IsIntegral K x := (Algebra.IsAlgebraic.isAlgebraic x).isIntegral
  have hdeg := Nat.div_pos (natDegree_le x) (natDegree_pos hx₀)
  rw [ne_eq]; rw [pow_eq_zero_iff hdeg.ne.symm]; rw [Valuation.zero_iff]
  exact coeff_zero_ne_zero hx₀ hx.ne_zero

end Valuation
