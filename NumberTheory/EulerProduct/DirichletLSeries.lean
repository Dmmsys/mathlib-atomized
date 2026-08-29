/-
Copyright (c) 2023 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.NumberTheory.EulerProduct.ExpLog
public import Mathlib.NumberTheory.LSeries.Dirichlet

/-!
# The Euler Product for the Riemann Zeta Function and Dirichlet L-Series

The first main result of this file is the Euler Product formula for the Riemann ζ function
$$\prod_p \frac{1}{1 - p^{-s}}
   = \lim_{n \to \infty} \prod_{p < n} \frac{1}{1 - p^{-s}} = \zeta(s)$$
for $s$ with real part $> 1$ ($p$ runs through the primes).
`riemannZeta_eulerProduct` is the second equality above. There are versions
`riemannZeta_eulerProduct_hasProd` and `riemannZeta_eulerProduct_tprod` in terms of `HasProd`
and `tprod`, respectively.

The second result is `dirichletLSeries_eulerProduct` (with variants
`dirichletLSeries_eulerProduct_hasProd` and `dirichletLSeries_eulerProduct_tprod`),
which is the analogous statement for Dirichlet L-series.
-/

@[expose] public section

open Complex

variable {s : Complex}

/-- When `s ≠ 0`, the map `n ↦ n^(-s)` is completely multiplicative and vanishes at zero. -/
noncomputable
/--
Definition of `riemannZetaSummandHom` / `riemannZetaSummandHom` 的定义

English:
definition riemannZetaSummandHom
  signature: (hs : s != 0)
  body: (n : Complex) ^ (-s)
  map_zero' := by simp [hs]
  map_one' := by simp
  map_mul' m n := by
    simpa only [Nat.cast_mul, ofReal_natCast]
      using mul_cpow_ofReal_nonneg m.cast_nonneg n.cast_nonneg _

中文:
定义 riemannZetaSummandHom
  签名: (hs : s != 0)
  定义体: (n : Complex) ^ (-s)
  map_zero' := by simp [hs]
  map_one' := by simp
  map_mul' m n := by
    simpa only [Nat.cast_mul, ofReal_natCast]
      using mul_cpow_ofReal_nonneg m.cast_nonneg n.cast_nonneg _
-/
def riemannZetaSummandHom (hs : s != 0) : Nat ->*₀ Complex where
  toFun n := (n : Complex) ^ (-s)
  map_zero' := by simp [hs]
  map_one' := by simp
  map_mul' m n := by
    simpa only [Nat.cast_mul, ofReal_natCast]
      using mul_cpow_ofReal_nonneg m.cast_nonneg n.cast_nonneg _

/-- When `χ` is a Dirichlet character and `s ≠ 0`, the map `n ↦ χ n * n^(-s)` is completely
multiplicative and vanishes at zero. -/
noncomputable
/--
Definition of `dirichletSummandHom` / `dirichletSummandHom` 的定义

English:
definition dirichletSummandHom
  signature: {n : Nat} (χ : DirichletCharacter Complex n) (hs : s != 0)
  body: χ n * (n : Complex) ^ (-s)
  map_zero' := by simp [hs]
  map_one' := by simp
  map_mul' m n := by
    simp_rw [← ofReal_natCast]
    simpa only [Nat.cast_mul, IsUnit.mul_iff, not_and, map_mul, ofReal_mul,
      mul_cpow_ofReal_nonneg m.cast_nonneg n.cast_nonneg _]
      using mul_mul_mul_comm ..

中文:
定义 dirichletSummandHom
  签名: {n : 自然数} (χ : DirichletCharacter Complex n) (hs : s != 0)
  定义体: χ n * (n : Complex) ^ (-s)
  map_zero' := by simp [hs]
  map_one' := by simp
  map_mul' m n := by
    simp_rw [← ofReal_natCast]
    simpa only [Nat.cast_mul, IsUnit.mul_iff, not_and, map_mul, ofReal_mul,
      mul_cpow_ofReal_nonneg m.cast_nonneg n.cast_nonneg _]
      using mul_mul_mul_comm ..
-/
def dirichletSummandHom {n : Nat} (χ : DirichletCharacter Complex n) (hs : s != 0) : Nat ->*₀ Complex where
  toFun n := χ n * (n : Complex) ^ (-s)
  map_zero' := by simp [hs]
  map_one' := by simp
  map_mul' m n := by
    simp_rw [← ofReal_natCast]
    simpa only [Nat.cast_mul, IsUnit.mul_iff, not_and, map_mul, ofReal_mul,
      mul_cpow_ofReal_nonneg m.cast_nonneg n.cast_nonneg _]
      using mul_mul_mul_comm ..

/--
lemma `summable_riemannZetaSummand` / 引理 `summable_riemannZetaSummand`

English:
lemma summable_riemannZetaSummand
  given: (hs : 1 < s.re)
  proof: by
  simp only [riemannZetaSummandHom, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk]
  convert! Real.summable_nat_rpow_inv.mpr hs with n
  rw [← ofReal_natCast]; rw [norm_cpow_eq_rpow_re_of_nonneg (Nat.cast_nonneg n) re_neg_ne_zero_of_one_lt_re hs]; rw [neg_re]; rw [Real.rpow_neg Nat.cast_nonneg n]

中文:
引理 summable_riemannZetaSummand
  条件: (hs : 1 < s.re)
  证明: by
  simp only [riemannZetaSummandHom, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk]
  convert! Real.summable_nat_rpow_inv.mpr hs with n
  rw [← ofReal_natCast]; rw [norm_cpow_eq_rpow_re_of_nonneg (Nat.cast_nonneg n) re_neg_ne_zero_of_one_lt_re hs]; rw [neg_re]; rw [Real.rpow_neg Nat.cast_nonneg n]

Depends on / 依赖: MonoidWithZeroHom, MonoidWithZeroHom.coe_mk, Nat.cast_nonneg, Real.rpow_neg, Real.summable_nat_rpow_inv.mpr, ZeroHom, ZeroHom.coe_mk, cast_nonneg, coe_mk, convert, neg_re, norm_cpow_eq_rpow_re_of_nonneg, ofReal_natCast, re_neg_ne_zero_of_one_lt_re, riemannZetaSummandHom, rpow_neg, summable_nat_rpow_inv
-/
lemma summable_riemannZetaSummand (hs : 1 < s.re) :
    Summable (fun n => ‖riemannZetaSummandHom (ne_zero_of_one_lt_re hs) n‖) := by
  simp only [riemannZetaSummandHom, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk]
  convert! Real.summable_nat_rpow_inv.mpr hs with n
  rw [← ofReal_natCast]; rw [norm_cpow_eq_rpow_re_of_nonneg (Nat.cast_nonneg n) re_neg_ne_zero_of_one_lt_re hs]; rw [neg_re]; rw [Real.rpow_neg Nat.cast_nonneg n]

/--
lemma `tsum_riemannZetaSummand` / 引理 `tsum_riemannZetaSummand`

English:
lemma tsum_riemannZetaSummand
  given: (hs : 1 < s.re)
  proof: by
  have hsum := summable_riemannZetaSummand hs
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow hs]; rw [hsum.of_norm.tsum_eq_zero_add]; rw [map_zero]; rw [zero_add]
  simp only [riemannZetaSummandHom, cpow_neg, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk,
    Nat.cast_add, Nat.cast_one, one_div]

中文:
引理 tsum_riemannZetaSummand
  条件: (hs : 1 < s.re)
  证明: by
  have hsum := summable_riemannZetaSummand hs
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow hs]; rw [hsum.of_norm.tsum_eq_zero_add]; rw [map_zero]; rw [zero_add]
  simp only [riemannZetaSummandHom, cpow_neg, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk,
    Nat.cast_add, Nat.cast_one, one_div]

Depends on / 依赖: MonoidWithZeroHom, MonoidWithZeroHom.coe_mk, Nat.cast_add, Nat.cast_one, ZeroHom, ZeroHom.coe_mk, cast_add, cast_one, coe_mk, cpow_neg, hsum.of_norm.tsum_eq_zero_add, map_zero, of_norm, one_div, riemannZetaSummandHom, summable_riemannZetaSummand, tsum_eq_zero_add, zero_add, zeta_eq_tsum_one_div_nat_add_one_cpow
-/
lemma tsum_riemannZetaSummand (hs : 1 < s.re) :
    ∑' (n : Nat), riemannZetaSummandHom (ne_zero_of_one_lt_re hs) n = riemannZeta s := by
  have hsum := summable_riemannZetaSummand hs
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow hs]; rw [hsum.of_norm.tsum_eq_zero_add]; rw [map_zero]; rw [zero_add]
  simp only [riemannZetaSummandHom, cpow_neg, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk,
    Nat.cast_add, Nat.cast_one, one_div]

/--
lemma `summable_dirichletSummand` / 引理 `summable_dirichletSummand`

English:
lemma summable_dirichletSummand
  given: {N : Nat} (χ : DirichletCharacter Complex N) (hs : 1 < s.re)
  proof: by
  simp only [dirichletSummandHom, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk, norm_mul]
  exact (summable_riemannZetaSummand hs).of_nonneg_of_le (fun _ => by positivity)
    (fun n => mul_le_of_le_one_left (norm_nonneg _) <| χ.norm_le_one n)

中文:
引理 summable_dirichletSummand
  条件: {N : 自然数} (χ : DirichletCharacter Complex N) (hs : 1 < s.re)
  证明: by
  simp only [dirichletSummandHom, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk, norm_mul]
  exact (summable_riemannZetaSummand hs).of_nonneg_of_le (fun _ => by positivity)
    (fun n => mul_le_of_le_one_left (norm_nonneg _) <| χ.norm_le_one n)

Depends on / 依赖: MonoidWithZeroHom, MonoidWithZeroHom.coe_mk, ZeroHom, ZeroHom.coe_mk, coe_mk, dirichletSummandHom, mul_le_of_le_one_left, norm_le_one, norm_mul, norm_nonneg, of_nonneg_of_le, summable_riemannZetaSummand
-/
lemma summable_dirichletSummand {N : Nat} (χ : DirichletCharacter Complex N) (hs : 1 < s.re) :
    Summable (fun n => ‖dirichletSummandHom χ (ne_zero_of_one_lt_re hs) n‖) := by
  simp only [dirichletSummandHom, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk, norm_mul]
  exact (summable_riemannZetaSummand hs).of_nonneg_of_le (fun _ => by positivity)
    (fun n => mul_le_of_le_one_left (norm_nonneg _) <| χ.norm_le_one n)

open scoped LSeries.notation in
/--
lemma `tsum_dirichletSummand` / 引理 `tsum_dirichletSummand`

English:
lemma tsum_dirichletSummand
  given: {N : Nat} (χ : DirichletCharacter Complex N) (hs : 1 < s.re)
  proof: by
  simp only [dirichletSummandHom, cpow_neg, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk, LSeries,
    LSeries.term_of_ne_zero' (ne_zero_of_one_lt_re hs), div_eq_mul_inv]

中文:
引理 tsum_dirichletSummand
  条件: {N : 自然数} (χ : DirichletCharacter Complex N) (hs : 1 < s.re)
  证明: by
  simp only [dirichletSummandHom, cpow_neg, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk, LSeries,
    LSeries.term_of_ne_zero' (ne_zero_of_one_lt_re hs), div_eq_mul_inv]

Depends on / 依赖: LSeries, LSeries.term_of_ne_zero, MonoidWithZeroHom, MonoidWithZeroHom.coe_mk, ZeroHom, ZeroHom.coe_mk, coe_mk, cpow_neg, dirichletSummandHom, div_eq_mul_inv, ne_zero_of_one_lt_re, term_of_ne_zero
-/
lemma tsum_dirichletSummand {N : Nat} (χ : DirichletCharacter Complex N) (hs : 1 < s.re) :
    ∑' (n : Nat), dirichletSummandHom χ (ne_zero_of_one_lt_re hs) n = L ↗χ s := by
  simp only [dirichletSummandHom, cpow_neg, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk, LSeries,
    LSeries.term_of_ne_zero' (ne_zero_of_one_lt_re hs), div_eq_mul_inv]

open Filter Nat Topology EulerProduct

/--
theorem `riemannZeta_eulerProduct_hasProd` / 定理 `riemannZeta_eulerProduct_hasProd`

English:
theorem riemannZeta_eulerProduct_hasProd
  given: (hs : 1 < s.re)
  proof: by
  rw [← tsum_riemannZetaSummand hs]
apply eulerProduct_completely_multiplicative_hasProd summable_riemannZetaSummand hs

中文:
定理 riemannZeta_eulerProduct_hasProd
  条件: (hs : 1 < s.re)
  证明: by
  rw [← tsum_riemannZetaSummand hs]
apply eulerProduct_completely_multiplicative_hasProd summable_riemannZetaSummand hs

Depends on / 依赖: eulerProduct_completely_multiplicative_hasProd, summable_riemannZetaSummand, tsum_riemannZetaSummand
-/
theorem riemannZeta_eulerProduct_hasProd (hs : 1 < s.re) :
    HasProd (fun p : Primes => (1 - (p : Complex) ^ (-s))⁻¹) (riemannZeta s) := by
  rw [← tsum_riemannZetaSummand hs]
apply eulerProduct_completely_multiplicative_hasProd summable_riemannZetaSummand hs

/--
theorem `riemannZeta_eulerProduct_tprod` / 定理 `riemannZeta_eulerProduct_tprod`

English:
theorem riemannZeta_eulerProduct_tprod
  given: (hs : 1 < s.re)
  proof: (riemannZeta_eulerProduct_hasProd hs).tprod_eq

中文:
定理 riemannZeta_eulerProduct_tprod
  条件: (hs : 1 < s.re)
  证明: (riemannZeta_eulerProduct_hasProd hs).tprod_eq

Depends on / 依赖: riemannZeta_eulerProduct_hasProd, tprod_eq
-/
theorem riemannZeta_eulerProduct_tprod (hs : 1 < s.re) :
    ∏' p : Primes, (1 - (p : Complex) ^ (-s))⁻¹ = riemannZeta s :=
  (riemannZeta_eulerProduct_hasProd hs).tprod_eq

/--
theorem `riemannZeta_eulerProduct` / 定理 `riemannZeta_eulerProduct`

English:
theorem riemannZeta_eulerProduct
  given: (hs : 1 < s.re)
  proof: by
  rw [← tsum_riemannZetaSummand hs]
apply eulerProduct_completely_multiplicative summable_riemannZetaSummand hs

中文:
定理 riemannZeta_eulerProduct
  条件: (hs : 1 < s.re)
  证明: by
  rw [← tsum_riemannZetaSummand hs]
apply eulerProduct_completely_multiplicative summable_riemannZetaSummand hs

Depends on / 依赖: eulerProduct_completely_multiplicative, summable_riemannZetaSummand, tsum_riemannZetaSummand
-/
theorem riemannZeta_eulerProduct (hs : 1 < s.re) :
    Tendsto (fun n : Nat => ∏ p in primesBelow n, (1 - (p : Complex) ^ (-s))⁻¹) atTop
      (𝓝 (riemannZeta s)) := by
  rw [← tsum_riemannZetaSummand hs]
apply eulerProduct_completely_multiplicative summable_riemannZetaSummand hs

open scoped LSeries.notation

/--
theorem `DirichletCharacter.LSeries_eulerProduct_hasProd` / 定理 `DirichletCharacter.LSeries_eulerProduct_hasProd`

English:
theorem DirichletCharacter.LSeries_eulerProduct_hasProd
  statement: {N : Nat} (χ : DirichletCharacter Complex N)
  proof: by
  rw [← tsum_dirichletSummand χ hs]
convert! eulerProduct_completely_multiplicative_hasProd summable_dirichletSummand χ hs

中文:
定理 DirichletCharacter.LSeries_eulerProduct_hasProd
  结论: {N : 自然数} (χ : DirichletCharacter Complex N)
  证明: by
  rw [← tsum_dirichletSummand χ hs]
convert! eulerProduct_completely_multiplicative_hasProd summable_dirichletSummand χ hs

Depends on / 依赖: convert, eulerProduct_completely_multiplicative_hasProd, summable_dirichletSummand, tsum_dirichletSummand
-/
theorem DirichletCharacter.LSeries_eulerProduct_hasProd {N : Nat} (χ : DirichletCharacter Complex N)
    (hs : 1 < s.re) :
    HasProd (fun p : Primes => (1 - χ p * (p : Complex) ^ (-s))⁻¹) (L ↗χ s) := by
  rw [← tsum_dirichletSummand χ hs]
convert! eulerProduct_completely_multiplicative_hasProd summable_dirichletSummand χ hs

/--
theorem `DirichletCharacter.LSeries_eulerProduct_tprod` / 定理 `DirichletCharacter.LSeries_eulerProduct_tprod`

English:
theorem DirichletCharacter.LSeries_eulerProduct_tprod
  statement: {N : Nat} (χ : DirichletCharacter Complex N)
  proof: (DirichletCharacter.LSeries_eulerProduct_hasProd χ hs).tprod_eq

中文:
定理 DirichletCharacter.LSeries_eulerProduct_tprod
  结论: {N : 自然数} (χ : DirichletCharacter Complex N)
  证明: (DirichletCharacter.LSeries_eulerProduct_hasProd χ hs).tprod_eq

Depends on / 依赖: DirichletCharacter, DirichletCharacter.LSeries_eulerProduct_hasProd, LSeries_eulerProduct_hasProd, tprod_eq
-/
theorem DirichletCharacter.LSeries_eulerProduct_tprod {N : Nat} (χ : DirichletCharacter Complex N)
    (hs : 1 < s.re) :
    ∏' p : Primes, (1 - χ p * (p : Complex) ^ (-s))⁻¹ = L ↗χ s :=
  (DirichletCharacter.LSeries_eulerProduct_hasProd χ hs).tprod_eq

/--
theorem `DirichletCharacter.LSeries_eulerProduct` / 定理 `DirichletCharacter.LSeries_eulerProduct`

English:
theorem DirichletCharacter.LSeries_eulerProduct
  statement: {N : Nat} (χ : DirichletCharacter Complex N)
  proof: by
  rw [← tsum_dirichletSummand χ hs]
apply eulerProduct_completely_multiplicative summable_dirichletSummand χ hs

中文:
定理 DirichletCharacter.LSeries_eulerProduct
  结论: {N : 自然数} (χ : DirichletCharacter Complex N)
  证明: by
  rw [← tsum_dirichletSummand χ hs]
apply eulerProduct_completely_multiplicative summable_dirichletSummand χ hs

Depends on / 依赖: eulerProduct_completely_multiplicative, summable_dirichletSummand, tsum_dirichletSummand
-/
theorem DirichletCharacter.LSeries_eulerProduct {N : Nat} (χ : DirichletCharacter Complex N)
    (hs : 1 < s.re) :
    Tendsto (fun n : Nat => ∏ p in primesBelow n, (1 - χ p * (p : Complex) ^ (-s))⁻¹) atTop
      (𝓝 (L ↗χ s)) := by
  rw [← tsum_dirichletSummand χ hs]
apply eulerProduct_completely_multiplicative summable_dirichletSummand χ hs

open LSeries

/--
theorem `DirichletCharacter.LSeries_eulerProduct_exp_log` / 定理 `DirichletCharacter.LSeries_eulerProduct_exp_log`

English:
theorem DirichletCharacter.LSeries_eulerProduct_exp_log
  statement: {N : Nat} (χ : DirichletCharacter Complex N)
  proof: by
let f := dirichletSummandHom χ ne_zero_of_one_lt_re hs
  have h n : term ↗χ s n = f n := by
    rcases eq_or_ne n 0 with rfl | hn
    · simp only [term_zero, map_zero]
    · simp only [ne_eq, hn, not_false_eq_true, term_of_ne_zero, div_eq_mul_inv,
        dirichletSummandHom, cpow_neg, MonoidWith

中文:
定理 DirichletCharacter.LSeries_eulerProduct_exp_log
  结论: {N : 自然数} (χ : DirichletCharacter Complex N)
  证明: by
let f := dirichletSummandHom χ ne_zero_of_one_lt_re hs
  have h n : term ↗χ s n = f n := by
    rcases eq_or_ne n 0 with rfl | hn
    · simp only [term_zero, map_zero]
    · simp only [ne_eq, hn, not_false_eq_true, term_of_ne_zero, div_eq_mul_inv,
        dirichletSummandHom, cpow_neg, MonoidWith

Depends on / 依赖: LSeries, MonoidWithZeroHom, MonoidWithZeroHom.coe_mk, ZeroHom, ZeroHom.coe_mk, coe_mk, cpow_neg, dirichletSummandHom, div_eq_mul_inv, eq_or_ne, exp_tsum_primes_log_eq_tsum, map_zero, ne_eq, ne_zero_of_one_lt_re, not_false_eq_true, summable_dirichletSummand, term_of_ne_zero, term_zero
-/
theorem DirichletCharacter.LSeries_eulerProduct_exp_log {N : Nat} (χ : DirichletCharacter Complex N)
    {s : Complex} (hs : 1 < s.re) :
    exp (∑' p : Nat.Primes, -log (1 - χ p * p ^ (-s))) = L ↗χ s := by
let f := dirichletSummandHom χ ne_zero_of_one_lt_re hs
  have h n : term ↗χ s n = f n := by
    rcases eq_or_ne n 0 with rfl | hn
    · simp only [term_zero, map_zero]
    · simp only [ne_eq, hn, not_false_eq_true, term_of_ne_zero, div_eq_mul_inv,
        dirichletSummandHom, cpow_neg, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk, f]
  simpa only [LSeries, h]
using! exp_tsum_primes_log_eq_tsum (f := f) summable_dirichletSummand χ hs

open DirichletCharacter

/--
theorem `ArithmeticFunction.LSeries_zeta_eulerProduct_exp_log` / 定理 `ArithmeticFunction.LSeries_zeta_eulerProduct_exp_log`

English:
theorem ArithmeticFunction.LSeries_zeta_eulerProduct_exp_log
  given: {s : Complex} (hs : 1 < s.re)
  proof: by
  convert!
    modOne_eq_one (R := Complex) ▸
      DirichletCharacter.LSeries_eulerProduct_exp_log (1 : DirichletCharacter Complex 1) hs using 7
  rw [MulChar.one_apply <| isUnit_of_subsingleton _]; rw [one_mul]

中文:
定理 ArithmeticFunction.LSeries_zeta_eulerProduct_exp_log
  条件: {s : Complex} (hs : 1 < s.re)
  证明: by
  convert!
    modOne_eq_one (R := Complex) ▸
      DirichletCharacter.LSeries_eulerProduct_exp_log (1 : DirichletCharacter Complex 1) hs using 7
  rw [MulChar.one_apply <| isUnit_of_subsingleton _]; rw [one_mul]

Depends on / 依赖: DirichletCharacter, DirichletCharacter.LSeries_eulerProduct_exp_log, LSeries_eulerProduct_exp_log, MulChar, MulChar.one_apply, convert, isUnit_of_subsingleton, modOne_eq_one, one_apply, one_mul
-/
theorem ArithmeticFunction.LSeries_zeta_eulerProduct_exp_log {s : Complex} (hs : 1 < s.re) :
    exp (∑' p : Nat.Primes, -Complex.log (1 - p ^ (-s))) = L 1 s := by
  convert!
    modOne_eq_one (R := Complex) ▸
      DirichletCharacter.LSeries_eulerProduct_exp_log (1 : DirichletCharacter Complex 1) hs using 7
  rw [MulChar.one_apply <| isUnit_of_subsingleton _]; rw [one_mul]

/--
theorem `riemannZeta_eulerProduct_exp_log` / 定理 `riemannZeta_eulerProduct_exp_log`

English:
theorem riemannZeta_eulerProduct_exp_log
  given: {s : Complex} (hs : 1 < s.re)
  proof: LSeries_one_eq_riemannZeta hs ▸ ArithmeticFunction.LSeries_zeta_eulerProduct_exp_log hs

中文:
定理 riemannZeta_eulerProduct_exp_log
  条件: {s : Complex} (hs : 1 < s.re)
  证明: LSeries_one_eq_riemannZeta hs ▸ ArithmeticFunction.LSeries_zeta_eulerProduct_exp_log hs

Depends on / 依赖: ArithmeticFunction, ArithmeticFunction.LSeries_zeta_eulerProduct_exp_log, LSeries_one_eq_riemannZeta, LSeries_zeta_eulerProduct_exp_log
-/
theorem riemannZeta_eulerProduct_exp_log {s : Complex} (hs : 1 < s.re) :
    exp (∑' p : Nat.Primes, -Complex.log (1 - p ^ (-s))) = riemannZeta s :=
  LSeries_one_eq_riemannZeta hs ▸ ArithmeticFunction.LSeries_zeta_eulerProduct_exp_log hs

/-!
### Changing the level of a Dirichlet `L`-series
-/

/--
lemma `DirichletCharacter.LSeries_changeLevel` / 引理 `DirichletCharacter.LSeries_changeLevel`

English:
lemma DirichletCharacter.LSeries_changeLevel
  statement: {M N : Nat} [NeZero N]
  proof: by
  rw [prod_eq_tprod_mulIndicator]; rw [← DirichletCharacter.LSeries_eulerProduct_tprod _ hs]; rw [← DirichletCharacter.LSeries_eulerProduct_tprod _ hs]
  -- convert to a form suitable for `tprod_subtype`
  have (f : Primes -> Complex) : ∏' (p : Primes), f p = ∏' (p : ↑{p : Nat | p.Prime}), f p :=

中文:
引理 DirichletCharacter.LSeries_changeLevel
  结论: {M N : 自然数} [NeZero N]
  证明: by
  rw [prod_eq_tprod_mulIndicator]; rw [← DirichletCharacter.LSeries_eulerProduct_tprod _ hs]; rw [← DirichletCharacter.LSeries_eulerProduct_tprod _ hs]
  -- convert to a form suitable for `tprod_subtype`
  have (f : Primes -> Complex) : ∏' (p : Primes), f p = ∏' (p : ↑{p : Nat | p.Prime}), f p :=

Depends on / 依赖: DirichletCharacter, DirichletCharacter.LSeries_eulerProduct_tprod, LSeries_eulerProduct_tprod, prod_eq_tprod_mulIndicator
-/
lemma DirichletCharacter.LSeries_changeLevel {M N : Nat} [NeZero N]
    (hMN : M ∣ N) (χ : DirichletCharacter Complex M) {s : Complex} (hs : 1 < s.re) :
    LSeries ↗(changeLevel hMN χ) s =
      LSeries ↗χ s * ∏ p in N.primeFactors, (1 - χ p * p ^ (-s)) := by
  rw [prod_eq_tprod_mulIndicator]; rw [← DirichletCharacter.LSeries_eulerProduct_tprod _ hs]; rw [← DirichletCharacter.LSeries_eulerProduct_tprod _ hs]
  -- convert to a form suitable for `tprod_subtype`
  have (f : Primes -> Complex) : ∏' (p : Primes), f p = ∏' (p : ↑{p : Nat | p.Prime}), f p := rfl
  rw [this]; rw [tprod_subtype _ fun p : Nat => (1 - (changeLevel hMN χ) p * p ^ (-s))⁻¹]; rw [this]; rw [tprod_subtype _ fun p : Nat => (1 - χ p * p ^ (-s))⁻¹]; rw [← Multipliable.tprod_mul]
  rotate_left -- deal with convergence goals first
  · exact multipliable_subtype_iff_mulIndicator.mp
      (DirichletCharacter.LSeries_eulerProduct_hasProd χ hs).multipliable
  · exact multipliable_subtype_iff_mulIndicator.mp Multipliable.of_finite
  · congr 1 with p
    simp only [Set.mulIndicator_apply, Set.mem_ofPred_eq, Finset.mem_coe, Nat.mem_primeFactors,
      ne_eq, mul_ite, mul_one]
    by_cases h : p.Prime; swap
    · simp only [h, false_and, if_false]
    simp only [h, true_and, if_true]
    by_cases hp' : p ∣ N; swap
    · simp only [hp', false_and, ↓reduceIte, inv_inj, sub_right_inj, mul_eq_mul_right_iff,
        cpow_eq_zero_iff, Nat.cast_eq_zero, h.ne_zero, ne_eq, neg_eq_zero, or_false]
      have hq : IsUnit (p : ZMod N) := (ZMod.isUnit_prime_iff_not_dvd h).mpr hp'
      simp only [hq.unit_spec ▸ DirichletCharacter.changeLevel_eq_cast_of_dvd χ hMN hq.unit,
        ZMod.cast_natCast hMN]
    · simp only [hp', NeZero.ne N, not_false_eq_true, and_self, ↓reduceIte]
      have : ¬IsUnit (p : ZMod N) := by rwa [ZMod.isUnit_prime_iff_not_dvd h, not_not]
      rw [MulChar.map_nonunit _ this]; rw [zero_mul]; rw [sub_zero]; rw [inv_one]
      refine (inv_mul_cancel₀ ?_).symm
      rw [sub_ne_zero]; rw [ne_comm]
      -- Remains to show `χ p * p ^ (-s) ≠ 1`. We show its norm is strictly `< 1`.
      apply_fun (‖·‖)
      simp only [norm_mul, norm_one]
      have ha : ‖χ p‖ <= 1 := χ.norm_le_one p
      have hb : ‖(p : Complex) ^ (-s)‖ <= 1 / 2 := norm_prime_cpow_le_one_half ⟨p, h⟩ hs
      exact ((mul_le_mul ha hb (norm_nonneg _) zero_le_one).trans_lt (by norm_num)).ne

section LogDirichlet

open Real hiding log exp_nat_mul exp_add
open ArithmeticFunction Primes Summable

variable {N : Nat} (χ : DirichletCharacter Complex N) {s : Complex}

/--
theorem `DirichletCharacter.eulerProduct_log_eq_LSeries` / 定理 `DirichletCharacter.eulerProduct_log_eq_LSeries`

English:
theorem DirichletCharacter.eulerProduct_log_eq_LSeries
  given: (hs : 1 < s.re)
  proof: by
  have hpow_le (p : Primes) : ‖χ p * (p : Complex) ^ (-s)‖ < 1 := by
    grw [norm_mul, norm_le_one, norm_natCast_cpow_of_pos (mod_cast p.prop.pos), neg_re, one_mul]
    apply rpow_lt_one_of_one_lt_of_neg (mod_cast p.prop.one_lt) (by linarith)
  rw [tsum_congr (fun p => (hasSum_taylorSeries_neg_l

中文:
定理 DirichletCharacter.eulerProduct_log_eq_LSeries
  条件: (hs : 1 < s.re)
  证明: by
  have hpow_le (p : Primes) : ‖χ p * (p : Complex) ^ (-s)‖ < 1 := by
    grw [norm_mul, norm_le_one, norm_natCast_cpow_of_pos (mod_cast p.prop.pos), neg_re, one_mul]
    apply rpow_lt_one_of_one_lt_of_neg (mod_cast p.prop.one_lt) (by linarith)
  rw [tsum_congr (fun p => (hasSum_taylorSeries_neg_l

Depends on / 依赖: Primes, Real.log, hasSum_taylorSeries_neg_log, hpow_le, mod_cast, neg_re, norm_le_one, norm_mul, norm_natCast_cpow_of_pos, one_lt, one_mul, p.prop.one_lt, p.prop.pos, rpow_lt_one_of_one_lt_of_neg, tsum_congr, tsum_eq, tsum_eq.symm
-/
theorem DirichletCharacter.eulerProduct_log_eq_LSeries (hs : 1 < s.re) :
    ∑' p : Primes, -log (1 - χ p * p ^ (-s)) = LSeries (fun n => χ n * Λ n / Real.log n) s := by
  have hpow_le (p : Primes) : ‖χ p * (p : Complex) ^ (-s)‖ < 1 := by
    grw [norm_mul, norm_le_one, norm_natCast_cpow_of_pos (mod_cast p.prop.pos), neg_re, one_mul]
    apply rpow_lt_one_of_one_lt_of_neg (mod_cast p.prop.one_lt) (by linarith)
  rw [tsum_congr (fun p => (hasSum_taylorSeries_neg_log' (hpow_le p)).tsum_eq.symm)]; rw [LSeries_def₀ (by simp)]
  let f : Nat -> Complex := fun n => χ n * Λ n / Real.log n * ((n : Complex) ^ (-s))
  calc
    _ = ∑' (p : Primes) (k : Nat), (χ (p ^ (k + 1)) * ((p ^ (k + 1) : Nat) : Complex) ^ (-s)) *
          Λ (p ^ (k + 1)) / Real.log (p ^ (k + 1)) := by
      refine tsum_congr fun p => tsum_congr fun k => ?_
      have : Complex.log p != 0 := mod_cast p.prop.log_ne_zero
      simp [mul_pow, ← cpow_nat_mul, ← natCast_cpow_natCast_mul, vonMangoldt_apply_pow,
        vonMangoldt_apply_prime p.2, field]
    _ = ∑' n : {n : Nat // IsPrimePow n}, f n := by
      rw [← tsum_primes_pow_eq]
      · exact tsum_congr fun p => tsum_congr fun k => (by unfold f; simp; ring)
      · apply comp_injective _ Subtype.coe_injective (f := f)
        apply of_norm_bounded_eventually_nat (g := (↑· ^ (-s.re)))
        · simp [hs]
        · filter_upwards [eventually_gt_atTop 1] with n hn
          simp only [f, norm_mul, norm_div, norm_real, norm_eq_abs]
          grw [norm_le_one, vonMangoldt_le_log]
          have := log_pos (x := n) (mod_cast hn)
          field_simp
          rw [← ofReal_natCast n]; rw [norm_cpow_eq_rpow_re_of_nonneg (by simp) (by simp; grind)]
          simp
    _ = _ := by
      simp only [div_eq_mul_inv _ (_ ^ _), ← cpow_neg]
      suffices (Function.support f) subseteq {n | IsPrimePow n} from
        tsum_subtype_eq_of_support_subset this
      intro n hn
      contrapose! hn
      simp [f, vonMangoldt_eq_zero_iff.mpr hn]

/--
theorem `DirichletCharacter.LSeries_eq_exp_LSeries` / 定理 `DirichletCharacter.LSeries_eq_exp_LSeries`

English:
theorem DirichletCharacter.LSeries_eq_exp_LSeries
  given: (hs : 1 < s.re)
  proof: by
  rw [← eulerProduct_log_eq_LSeries χ hs]; rw [LSeries_eulerProduct_exp_log χ hs]

中文:
定理 DirichletCharacter.LSeries_eq_exp_LSeries
  条件: (hs : 1 < s.re)
  证明: by
  rw [← eulerProduct_log_eq_LSeries χ hs]; rw [LSeries_eulerProduct_exp_log χ hs]

Depends on / 依赖: LSeries_eulerProduct_exp_log, eulerProduct_log_eq_LSeries
-/
theorem DirichletCharacter.LSeries_eq_exp_LSeries (hs : 1 < s.re) :
    exp (LSeries (fun (n : Nat) => χ n * Λ n / Real.log n) s) = L ↗χ s := by
  rw [← eulerProduct_log_eq_LSeries χ hs]; rw [LSeries_eulerProduct_exp_log χ hs]

/--
theorem `riemannZeta_eq_exp_LSeries` / 定理 `riemannZeta_eq_exp_LSeries`

English:
theorem riemannZeta_eq_exp_LSeries
  given: {s : Complex} (hs : 1 < s.re)
  proof: by
  rw [← LSeries_one_eq_riemannZeta hs]
  convert LSeries_eq_exp_LSeries (1 : DirichletCharacter Complex 1) hs
  <;> simp [MulChar.one_apply <| isUnit_of_subsingleton _]

中文:
定理 riemannZeta_eq_exp_LSeries
  条件: {s : Complex} (hs : 1 < s.re)
  证明: by
  rw [← LSeries_one_eq_riemannZeta hs]
  convert LSeries_eq_exp_LSeries (1 : DirichletCharacter Complex 1) hs
  <;> simp [MulChar.one_apply <| isUnit_of_subsingleton _]

Depends on / 依赖: DirichletCharacter, LSeries_eq_exp_LSeries, LSeries_one_eq_riemannZeta, MulChar, MulChar.one_apply, convert, isUnit_of_subsingleton, one_apply
-/
theorem riemannZeta_eq_exp_LSeries {s : Complex} (hs : 1 < s.re) :
    exp (LSeries (fun (n : Nat) => Λ n / Real.log n) s) = riemannZeta s := by
  rw [← LSeries_one_eq_riemannZeta hs]
  convert LSeries_eq_exp_LSeries (1 : DirichletCharacter Complex 1) hs
  <;> simp [MulChar.one_apply <| isUnit_of_subsingleton _]

/--
theorem `log_riemannZeta_eq` / 定理 `log_riemannZeta_eq`

English:
theorem log_riemannZeta_eq
  given: {s : Real} (hs : 1 < s)
  proof: by
  rw [← riemannZeta_eq_exp_LSeries (by simpa using hs)]; rw [LSeries_def₀ (by simp)]
  convert Real.log_exp _
  convert exp_ofReal_re _
  push_cast
  congr! 2 with p
  rw [ofReal_cpow (by positivity)]
  simp [field]

中文:
定理 log_riemannZeta_eq
  条件: {s : 实数} (hs : 1 < s)
  证明: by
  rw [← riemannZeta_eq_exp_LSeries (by simpa using hs)]; rw [LSeries_def₀ (by simp)]
  convert Real.log_exp _
  convert exp_ofReal_re _
  push_cast
  congr! 2 with p
  rw [ofReal_cpow (by positivity)]
  simp [field]

Depends on / 依赖: Real.log_exp, convert, exp_ofReal_re, log_exp, ofReal_cpow, riemannZeta_eq_exp_LSeries
-/
theorem log_riemannZeta_eq {s : Real} (hs : 1 < s) :
    Real.log (riemannZeta (s : Complex)).re = ∑' n, Λ n / (n ^ s * Real.log n) := by
  rw [← riemannZeta_eq_exp_LSeries (by simpa using hs)]; rw [LSeries_def₀ (by simp)]
  convert Real.log_exp _
  convert exp_ofReal_re _
  push_cast
  congr! 2 with p
  rw [ofReal_cpow (by positivity)]
  simp [field]

end LogDirichlet
