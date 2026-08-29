/-
Copyright (c) 2026 Kevin H. Wilson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin H. Wilson
-/
module

public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.MeasureTheory.Integral.CircleAverage

/-!
# Fourier Coefficients of Polynomials

We define an algebra map from `ℂ[X]` to the `MeasureTheory.Lp` (with `p := 2`) space on the additive
circle and show that it sends monomials to the Fourier basis. From this, we derive that polynomial
coefficients match Fourier coefficients and prove Parseval's identity for polynomials.

## Main definitions

- `Polynomial.toAddCircle`: Algebra map from `ℂ[X]` to `C(AddCircle (2 * π), ℂ)` that evaluates
  polynomials on the unit circle.

## Main results

- `Polynomial.fourierCoeff_toAddCircle`: The `n`-th Fourier coefficient of a polynomial
  equals its `n`-th coefficient when `n` is nonnegative, else 0.
- `Polynomial.fourierCoeff_toAddCircle_natCast`: A variant of `Polynomial.fourierCoeff_toAddCircle`
  for `ℕ` arguments.
- `Polynomial.sum_sq_norm_coeff_eq_circleAverage`: Parseval's identity that the sum of the squares
  of the norms of the coefficients of a polynomial equals the average over the circle of the norm
  square of the polynomial.
-/

open Complex MeasureTheory Set AddCircle
open scoped Real

namespace Polynomial

@[expose] public section complex

variable (p : Complex[X])

local instance instTwoPiPos : Fact (0 < 2 * π) := Fact.mk Real.two_pi_pos

/--
Definition of `toAddCircle` / `toAddCircle` 的定义

English:
definition toAddCircle
  signature: : Complex[X] ->ₐ[Complex] C(AddCircle (2 * π), Complex)
  body: Polynomial.aeval { toFun c := c.toCircle }

中文:
定义 toAddCircle
  签名: : 复形[X] ->ₐ[复形] C(AddCircle (2 * π), 复形)
  定义体: Polynomial.aeval { toFun c := c.toCircle }

Depends on / 依赖: Polynomial, Polynomial.aeval, c.toCircle, toCircle
-/
noncomputable def toAddCircle : Complex[X] ->ₐ[Complex] C(AddCircle (2 * π), Complex) :=
  Polynomial.aeval { toFun c := c.toCircle }

/--
lemma `toAddCircle.integrable` / 引理 `toAddCircle.integrable`

English:
lemma toAddCircle.integrable
  proof: by
  simpa using p.toAddCircle.continuous.continuousOn.integrableOn_compact isCompact_univ

中文:
引理 toAddCircle.integrable
  证明: by
  simpa using p.toAddCircle.continuous.continuousOn.integrableOn_compact isCompact_univ

Depends on / 依赖: continuous, continuousOn, integrableOn_compact, isCompact_univ, p.toAddCircle.continuous.continuousOn.integrableOn_compact, toAddCircle
-/
lemma toAddCircle.integrable :
    Integrable p.toAddCircle (haarAddCircle (T := 2 * π)) := by
  simpa using p.toAddCircle.continuous.continuousOn.integrableOn_compact isCompact_univ

/--
theorem `toAddCircle_C_eq_smul_fourier_zero` / 定理 `toAddCircle_C_eq_smul_fourier_zero`

English:
theorem toAddCircle_C_eq_smul_fourier_zero
  given: {c : Complex}
  statement: (C c).toAddCircle = c • fourier 0
  proof: by
  ext θ; simp [toAddCircle]

中文:
定理 toAddCircle_C_eq_smul_fourier_zero
  条件: {c : 复形}
  结论: (C c).toAddCircle = c • fourier 0
  证明: by
  ext θ; simp [toAddCircle]

Depends on / 依赖: toAddCircle
-/
theorem toAddCircle_C_eq_smul_fourier_zero {c : Complex} : (C c).toAddCircle = c • fourier 0 := by
  ext θ; simp [toAddCircle]

/--
theorem `toAddCircle_X_eq_fourier_one` / 定理 `toAddCircle_X_eq_fourier_one`

English:
theorem toAddCircle_X_eq_fourier_one
  statement: (X : Complex[X]).toAddCircle = fourier 1
  proof: by
  ext θ; simp [toAddCircle]

中文:
定理 toAddCircle_X_eq_fourier_one
  结论: (X : 复形[X]).toAddCircle = fourier 1
  证明: by
  ext θ; simp [toAddCircle]

Depends on / 依赖: toAddCircle
-/
theorem toAddCircle_X_eq_fourier_one : (X : Complex[X]).toAddCircle = fourier 1 := by
  ext θ; simp [toAddCircle]

/--
theorem `toAddCircle_X_pow_eq_fourier` / 定理 `toAddCircle_X_pow_eq_fourier`

English:
theorem toAddCircle_X_pow_eq_fourier
  given: {n : Nat}
  statement: (X ^ n : Complex[X]).toAddCircle = fourier n
  proof: by
  ext θ; simp [toAddCircle, AddCircle.toCircle_nsmul]

中文:
定理 toAddCircle_X_pow_eq_fourier
  条件: {n : 自然数}
  结论: (X ^ n : 复形[X]).toAddCircle = fourier n
  证明: by
  ext θ; simp [toAddCircle, AddCircle.toCircle_nsmul]

Depends on / 依赖: AddCircle, AddCircle.toCircle_nsmul, toAddCircle, toCircle_nsmul
-/
theorem toAddCircle_X_pow_eq_fourier {n : Nat} : (X ^ n : Complex[X]).toAddCircle = fourier n := by
  ext θ; simp [toAddCircle, AddCircle.toCircle_nsmul]

/--
theorem `toAddCircle_monomial_eq_smul_fourier` / 定理 `toAddCircle_monomial_eq_smul_fourier`

English:
theorem toAddCircle_monomial_eq_smul_fourier
  given: {n : Nat} {c : Complex}
  proof: by
  ext θ; simp [toAddCircle, AddCircle.toCircle_nsmul]

中文:
定理 toAddCircle_monomial_eq_smul_fourier
  条件: {n : 自然数} {c : 复形}
  证明: by
  ext θ; simp [toAddCircle, AddCircle.toCircle_nsmul]

Depends on / 依赖: AddCircle, AddCircle.toCircle_nsmul, toAddCircle, toCircle_nsmul
-/
theorem toAddCircle_monomial_eq_smul_fourier {n : Nat} {c : Complex} :
    (monomial n c).toAddCircle = c • fourier n := by
  ext θ; simp [toAddCircle, AddCircle.toCircle_nsmul]

/--
theorem `fourierCoeff_toAddCircle` / 定理 `fourierCoeff_toAddCircle`

English:
theorem fourierCoeff_toAddCircle
  given: (n : Int)
  proof: by
.imp_right Int.eq_ofNat_of_zero_le have : n < 0 ∨ exists k : Nat, n = k := lt_or_ge n 0
  induction p using Polynomial.induction_on' with obtain (hn | ⟨k, rfl⟩) := this
  | add p q hp hq =>
    simp_all [not_le_of_gt, fourierCoeff.add (toAddCircle.integrable p) (toAddCircle.integrable q)]
  | mon

中文:
定理 fourierCoeff_toAddCircle
  条件: (n : 整数)
  证明: by
.imp_right Int.eq_ofNat_of_zero_le have : n < 0 ∨ exists k : Nat, n = k := lt_or_ge n 0
  induction p using Polynomial.induction_on' with obtain (hn | ⟨k, rfl⟩) := this
  | add p q hp hq =>
    simp_all [not_le_of_gt, fourierCoeff.add (toAddCircle.integrable p) (toAddCircle.integrable q)]
  | mon

Depends on / 依赖: Int.eq_ofNat_of_zero_le, Pi.si, Polynomial, Polynomial.induction_on, coeff_monomial, const_smul, eq_ofNat_of_zero_le, fourierCoeff, fourierCoeff.add, fourierCoeff.const_smul, fourierCoeff_fourier, imp_right, induction_on, integrable, lt_or_ge, monomial, n.natAbs, natAbs, not_le_of_gt, p.coeff
-/
theorem fourierCoeff_toAddCircle (n : Int) :
    fourierCoeff (T := 2 * π) p.toAddCircle n = if 0 <= n then p.coeff n.natAbs else 0 := by
.imp_right Int.eq_ofNat_of_zero_le have : n < 0 ∨ exists k : Nat, n = k := lt_or_ge n 0
  induction p using Polynomial.induction_on' with obtain (hn | ⟨k, rfl⟩) := this
  | add p q hp hq =>
    simp_all [not_le_of_gt, fourierCoeff.add (toAddCircle.integrable p) (toAddCircle.integrable q)]
  | monomial m a =>
    simp_all [not_le_of_gt, coeff_monomial, toAddCircle_monomial_eq_smul_fourier,
      fourierCoeff.const_smul, fourierCoeff_fourier, Pi.single_apply]
    grind

/--
theorem `fourierCoeff_toAddCircle_natCast` / 定理 `fourierCoeff_toAddCircle_natCast`

English:
theorem fourierCoeff_toAddCircle_natCast
  given: (n : Nat)
  proof: by
  simp [fourierCoeff_toAddCircle]

中文:
定理 fourierCoeff_toAddCircle_natCast
  条件: (n : 自然数)
  证明: by
  simp [fourierCoeff_toAddCircle]

Depends on / 依赖: fourierCoeff_toAddCircle, p.coeff, p.toAddCircle, toAddCircle
-/
theorem fourierCoeff_toAddCircle_natCast (n : Nat) :
    fourierCoeff (T := 2 * π) p.toAddCircle n = p.coeff n := by
  simp [fourierCoeff_toAddCircle]

/--
theorem `fourierCoeff_toAddCircle_eq_zero_of_lt_zero` / 定理 `fourierCoeff_toAddCircle_eq_zero_of_lt_zero`

English:
theorem fourierCoeff_toAddCircle_eq_zero_of_lt_zero
  given: (n : Int) (hn : n < 0)
  proof: by
  simp [fourierCoeff_toAddCircle, hn]

中文:
定理 fourierCoeff_toAddCircle_eq_zero_of_lt_zero
  条件: (n : 整数) (hn : n < 0)
  证明: by
  simp [fourierCoeff_toAddCircle, hn]

Depends on / 依赖: fourierCoeff_toAddCircle, p.toAddCircle, toAddCircle
-/
theorem fourierCoeff_toAddCircle_eq_zero_of_lt_zero (n : Int) (hn : n < 0) :
    fourierCoeff (T := 2 * π) p.toAddCircle n = 0 := by
  simp [fourierCoeff_toAddCircle, hn]

/--
theorem `sum_sq_norm_coeff_eq_circleAverage` / 定理 `sum_sq_norm_coeff_eq_circleAverage`

English:
theorem sum_sq_norm_coeff_eq_circleAverage
  statement: ∑ i in p.support, ‖p.coeff i‖ ^ 2 =
  proof: by
  -- Rewrite coefficients as Fourier coefficients
  have := tsum_sq_fourierCoeff (T := 2 * π) (p.toAddCircle.toLp 2 haarAddCircle Complex)
  simp_rw [fourierCoeff_toLp, fourierCoeff_toAddCircle] at this
  rw [tsum_eq_sum (s := p.support.map ⟨_]; rw [Nat.cast_injective⟩) (fun b hb => ?eq_zero)] at

中文:
定理 sum_sq_norm_coeff_eq_circleAverage
  结论: ∑ i in p.support, ‖p.coeff i‖ ^ 2 =
  证明: by
  -- Rewrite coefficients as Fourier coefficients
  have := tsum_sq_fourierCoeff (T := 2 * π) (p.toAddCircle.toLp 2 haarAddCircle Complex)
  simp_rw [fourierCoeff_toLp, fourierCoeff_toAddCircle] at this
  rw [tsum_eq_sum (s := p.support.map ⟨_]; rw [Nat.cast_injective⟩) (fun b hb => ?eq_zero)] at
-/
theorem sum_sq_norm_coeff_eq_circleAverage : ∑ i in p.support, ‖p.coeff i‖ ^ 2 =
    Real.circleAverage (fun θ => ‖p.eval θ‖ ^ 2) 0 1 := by
  -- Rewrite coefficients as Fourier coefficients
  have := tsum_sq_fourierCoeff (T := 2 * π) (p.toAddCircle.toLp 2 haarAddCircle Complex)
  simp_rw [fourierCoeff_toLp, fourierCoeff_toAddCircle] at this
  rw [tsum_eq_sum (s := p.support.map ⟨_]; rw [Nat.cast_injective⟩) (fun b hb => ?eq_zero)] at this
  case eq_zero =>
    obtain h | h := le_or_gt 0 b
    · lift b to Nat using h
      simpa using hb
    · simp [h]
  simp only [Finset.sum_map, Function.Embedding.coeFn_mk, Nat.cast_nonneg,
    ↓reduceIte, Int.natAbs_natCast, ContinuousMap.coe_toLp] at this
  have h1 : ∫ (t : AddCircle (2 * π)), ‖toAddCircle p t‖ ^ 2 ∂haarAddCircle =
      ∫ (t : AddCircle (2 * π)),
        ‖(ContinuousMap.toAEEqFun haarAddCircle (toAddCircle p)) t‖ ^ 2 ∂haarAddCircle := by
    refine integral_congr_ae ?_
    filter_upwards [ContinuousMap.coeFn_toAEEqFun haarAddCircle (toAddCircle p)] with t ht
    rw [← ht]
  rw [this]; rw [← h1]; rw [AddCircle.integral_haarAddCircle]; rw [Real.circleAverage]; rw [← AddCircle.intervalIntegral_preimage (2 * π) 0]
  simp [toAddCircle, toCircle, circleMap]

end complex
end Polynomial
