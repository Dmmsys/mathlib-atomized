/-
Copyright (c) 2024 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll, David Loeffler
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
public import Mathlib.NumberTheory.Harmonic.ZetaAsymp
public import Mathlib.NumberTheory.LSeries.Dirichlet
public import Mathlib.NumberTheory.LSeries.DirichletContinuation
public import Mathlib.NumberTheory.LSeries.Positivity

/-!
# The L-function of a Dirichlet character does not vanish on Re(s) ≥ 1

The main result in this file is `DirichletCharacter.LFunction_ne_zero_of_one_le_re`:
if `χ` is a Dirichlet character, `s ∈ ℂ` with `1 ≤ s.re`, and either `χ` is nontrivial or `s ≠ 1`,
then the L-function of `χ` does not vanish at `s`.

As a consequence, we have the corresponding statement for the Riemann ζ function:
`riemannZeta_ne_zero_of_one_le_re` (which does not require `s ≠ 1`, since the junk value at `s = 1`
happens to be non-zero).

These results are prerequisites for the **Prime Number Theorem** and
**Dirichlet's Theorem** on primes in arithmetic progressions.

## Outline of proofs

We split into two cases: first, the special case of (non-trivial) quadratic characters at `s = 1`;
then the remaining case when either `s ≠ 1` or `χ ^ 2 ≠ 1`.

The first case is handled using a positivity argument applied to the series `L χ s * ζ s`: we show
that this function has non-negative Dirichlet coefficients, is strictly positive for `s ≫ 0`, but
vanishes at `s = -2`, so it must have a pole somewhere in between.

The second case is dealt with using the product
`L(χ^0, 1 + x)^3 L(χ, 1 + x + I * y)^4 L(χ^2, 1 + x + 2 * I * y)`, which
we show has absolute value `≥ 1` for all positive `x` and real `y`; if `L(χ, 1 + I * y) = 0` then
this product would have to tend to 0 as `x → 0`, which is a contradiction.
-/

@[expose] public section

/- NB: Many lemmas (and some defs) in this file are private, since they concern properties of
hypothetical objects which we eventually deduce cannot exist. We have only made public the lemmas
whose hypotheses do not turn out to be contradictory.
-/

open Complex Asymptotics Topology Filter
open ArithmeticFunction hiding log

-- We use the ordering on `ℂ` given by comparing real parts for fixed imaginary part
open scoped ComplexOrder

variable {N : Nat}

namespace DirichletCharacter

section quadratic

/-!
### Convolution of a Dirichlet character with ζ

We define `DirichletCharacter.zetaMul χ` to be the arithmetic function obtained by
taking the product (as arithmetic functions = Dirichlet convolution) of the
arithmetic function `ζ` with `χ`.

We then show that for a quadratic character `χ`, this arithmetic function is multiplicative
and takes nonnegative real values.
-/

/--
Definition of `zetaMul` / `zetaMul` 的定义

English:
definition zetaMul
  signature: (χ : DirichletCharacter Complex N)
  body: .zeta * toArithmeticFunction (χ ·)

中文:
定义 zetaMul
  签名: (χ : DirichletCharacter 复形 N)
  定义体: .zeta * toArithmeticFunction (χ ·)

Depends on / 依赖: toArithmeticFunction
-/
noncomputable def zetaMul (χ : DirichletCharacter Complex N) : ArithmeticFunction Complex :=
  .zeta * toArithmeticFunction (χ ·)

/--
lemma `isMultiplicative_zetaMul` / 引理 `isMultiplicative_zetaMul`

English:
lemma isMultiplicative_zetaMul
  given: (χ : DirichletCharacter Complex N)
  statement: χ.zetaMul.IsMultiplicative
  proof: isMultiplicative_zeta.natCast.mul isMultiplicative_toArithmeticFunction χ

中文:
引理 isMultiplicative_zetaMul
  条件: (χ : DirichletCharacter 复形 N)
  结论: χ.zetaMul.是Multiplicative
  证明: isMultiplicative_zeta.natCast.mul isMultiplicative_toArithmeticFunction χ

Depends on / 依赖: isMultiplicative_toArithmeticFunction, isMultiplicative_zeta, isMultiplicative_zeta.natCast.mul, natCast
-/
lemma isMultiplicative_zetaMul (χ : DirichletCharacter Complex N) : χ.zetaMul.IsMultiplicative :=
isMultiplicative_zeta.natCast.mul isMultiplicative_toArithmeticFunction χ

/--
lemma `LSeriesSummable_zetaMul` / 引理 `LSeriesSummable_zetaMul`

English:
lemma LSeriesSummable_zetaMul
  given: (χ : DirichletCharacter Complex N) {s : Complex} (hs : 1 < s.re)
  proof: by
refine ArithmeticFunction.LSeriesSummable_mul (LSeriesSummable_zeta_iff.mpr hs)
    LSeriesSummable_of_bounded_of_one_lt_re (m := 1) (fun n hn => ?_) hs
  simpa only [toArithmeticFunction, coe_mk, hn, ↓reduceIte]
  using norm_le_one χ _

中文:
引理 LSeriesSummable_zetaMul
  条件: (χ : DirichletCharacter 复形 N) {s : 复形} (hs : 1 < s.re)
  证明: by
refine ArithmeticFunction.LSeriesSummable_mul (LSeriesSummable_zeta_iff.mpr hs)
    LSeriesSummable_of_bounded_of_one_lt_re (m := 1) (fun n hn => ?_) hs
  simpa only [toArithmeticFunction, coe_mk, hn, ↓reduceIte]
  using norm_le_one χ _

Depends on / 依赖: ArithmeticFunction, ArithmeticFunction.LSeriesSummable_mul, LSeriesSummable_mul, LSeriesSummable_of_bounded_of_one_lt_re, LSeriesSummable_zeta_iff, LSeriesSummable_zeta_iff.mpr, coe_mk, norm_le_one, reduceIte, toArithmeticFunction
-/
lemma LSeriesSummable_zetaMul (χ : DirichletCharacter Complex N) {s : Complex} (hs : 1 < s.re) :
    LSeriesSummable χ.zetaMul s := by
refine ArithmeticFunction.LSeriesSummable_mul (LSeriesSummable_zeta_iff.mpr hs)
    LSeriesSummable_of_bounded_of_one_lt_re (m := 1) (fun n hn => ?_) hs
  simpa only [toArithmeticFunction, coe_mk, hn, ↓reduceIte]
  using norm_le_one χ _

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `zetaMul_prime_pow_nonneg` / 引理 `zetaMul_prime_pow_nonneg`

English:
lemma zetaMul_prime_pow_nonneg
  statement: {χ : DirichletCharacter Complex N} (hχ : χ ^ 2 = 1) {p : Nat}
  proof: by
  simp only [zetaMul, toArithmeticFunction, coe_zeta_mul_apply, coe_mk,
    Nat.sum_divisors_prime_pow hp, pow_eq_zero_iff', hp.ne_zero, ne_eq, false_and, ↓reduceIte,
    Nat.cast_pow, map_pow]
  rcases MulChar.isQuadratic_iff_sq_eq_one.mpr hχ p with h | h | h
  · refine Finset.sum_nonneg fun i _ => ?_
    simp only [h, le_refl, pow_nonneg]
  · refine Finset.sum_nonneg fun i _ => ?_
    simp only [h, one_pow, zero_le_one]
  · simp only [h, neg_one_geom_sum]
    split_ifs
    exacts [le_rfl, zero_le_one]

中文:
引理 zetaMul_prime_pow_nonneg
  结论: {χ : DirichletCharacter 复形 N} (hχ : χ ^ 2 = 1) {p : 自然数}
  证明: by
  simp only [zetaMul, toArithmeticFunction, coe_zeta_mul_apply, coe_mk,
    Nat.sum_divisors_prime_pow hp, pow_eq_zero_iff', hp.ne_zero, ne_eq, false_and, ↓reduceIte,
    Nat.cast_pow, map_pow]
  rcases MulChar.isQuadratic_iff_sq_eq_one.mpr hχ p with h | h | h
  · refine Finset.sum_nonneg fun i _ => ?_
    simp only [h, le_refl, pow_nonneg]
  · refine Finset.sum_nonneg fun i _ => ?_
    simp only [h, one_pow, zero_le_one]
  · simp only [h, neg_one_geom_sum]
    split_ifs
    exacts [le_rfl, zero_le_one]

Depends on / 依赖: Finset, Finset.sum_nonneg, MulChar, MulChar.isQuadratic_iff_sq_eq_one.mpr, Nat.cast_pow, Nat.sum_divisors_prime_pow, cast_pow, coe_mk, coe_zeta_mul_apply, exacts, false_and, hp.ne_zero, isQuadratic_iff_sq_eq_one, le_refl, le_rfl, map_pow, ne_eq, ne_zero, neg_one_geom_sum, one_pow
-/
lemma zetaMul_prime_pow_nonneg {χ : DirichletCharacter Complex N} (hχ : χ ^ 2 = 1) {p : Nat}
    (hp : p.Prime) (k : Nat) :
    0 <= zetaMul χ (p ^ k) := by
  simp only [zetaMul, toArithmeticFunction, coe_zeta_mul_apply, coe_mk,
    Nat.sum_divisors_prime_pow hp, pow_eq_zero_iff', hp.ne_zero, ne_eq, false_and, ↓reduceIte,
    Nat.cast_pow, map_pow]
  rcases MulChar.isQuadratic_iff_sq_eq_one.mpr hχ p with h | h | h
  · refine Finset.sum_nonneg fun i _ => ?_
    simp only [h, le_refl, pow_nonneg]
  · refine Finset.sum_nonneg fun i _ => ?_
    simp only [h, one_pow, zero_le_one]
  · simp only [h, neg_one_geom_sum]
    split_ifs
    exacts [le_rfl, zero_le_one]

/--
lemma `zetaMul_nonneg` / 引理 `zetaMul_nonneg`

English:
lemma zetaMul_nonneg
  given: {χ : DirichletCharacter Complex N} (hχ : χ ^ 2 = 1) (n : Nat)
  proof: by
  rcases eq_or_ne n 0 with rfl | hn
  · simp only [ArithmeticFunction.map_zero, le_refl]
  · simpa only [χ.isMultiplicative_zetaMul.multiplicative_factorization _ hn] using!
      Finset.prod_nonneg
        fun p hp => zetaMul_prime_pow_nonneg hχ (Nat.prime_of_mem_primeFactors hp) _

中文:
引理 zetaMul_nonneg
  条件: {χ : DirichletCharacter 复形 N} (hχ : χ ^ 2 = 1) (n : 自然数)
  证明: by
  rcases eq_or_ne n 0 with rfl | hn
  · simp only [ArithmeticFunction.map_zero, le_refl]
  · simpa only [χ.isMultiplicative_zetaMul.multiplicative_factorization _ hn] using!
      Finset.prod_nonneg
        fun p hp => zetaMul_prime_pow_nonneg hχ (Nat.prime_of_mem_primeFactors hp) _

Depends on / 依赖: ArithmeticFunction, ArithmeticFunction.map_zero, Finset, Finset.prod_nonneg, Nat.prime_of_mem_primeFactors, eq_or_ne, isMultiplicative_zetaMul, isMultiplicative_zetaMul.multiplicative_factorization, le_refl, map_zero, multiplicative_factorization, prime_of_mem_primeFactors, prod_nonneg, zetaMul_prime_pow_nonneg
-/
lemma zetaMul_nonneg {χ : DirichletCharacter Complex N} (hχ : χ ^ 2 = 1) (n : Nat) :
    0 <= zetaMul χ n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp only [ArithmeticFunction.map_zero, le_refl]
  · simpa only [χ.isMultiplicative_zetaMul.multiplicative_factorization _ hn] using!
      Finset.prod_nonneg
        fun p hp => zetaMul_prime_pow_nonneg hχ (Nat.prime_of_mem_primeFactors hp) _

/-
### "Bad" Dirichlet characters

Our goal is to show that `L(χ, 1) ≠ 0` when `χ` is a (nontrivial) quadratic Dirichlet character.
To do that, we package the contradictory properties in a (private) structure
`DirichletCharacter.BadChar` and derive further statements eventually leading to a contradiction.

This entire section is private.
-/

/--
Definition of `BadChar` / `BadChar` 的定义

English:
structure BadChar
  parameters: (N : Nat) [NeZero N]
  axioms and operations (4):
    - χ : DirichletCharacter Complex N
    - χ_ne : χ != 1
    - χ_sq : χ ^ 2 = 1
    - hχ : χ.LFunction 1 = 0

中文:
结构 BadChar
  参数: (N : 自然数) [NeZero N]
  公理与运算 (4 个):
    - χ : DirichletCharacter 复形 N
    - χ_ne : χ != 1
    - χ_sq : χ ^ 2 = 1
    - hχ : χ.L函数 1 = 0
-/
private structure BadChar (N : Nat) [NeZero N] where
  /-- The character we want to show cannot exist. -/
  χ : DirichletCharacter Complex N
  χ_ne : χ != 1
  χ_sq : χ ^ 2 = 1
  hχ : χ.LFunction 1 = 0

variable [NeZero N]

namespace BadChar

/-- The product of the Riemann zeta function with the L-function of `B.χ`.
We will show that `B.F (-2) = 0` but also that `B.F (-2)` must be positive,
giving the desired contradiction. -/
private noncomputable
/--
Definition of `F` / `F` 的定义

English:
definition F
  signature: (B : BadChar N)
  body: Function.update (fun s : Complex => riemannZeta s * LFunction B.χ s) 1 (deriv (LFunction B.χ) 1)

中文:
定义 F
  签名: (B : BadChar N)
  定义体: Function.update (fun s : Complex => riemannZeta s * LFunction B.χ s) 1 (deriv (LFunction B.χ) 1)

Depends on / 依赖: Function, Function.update, LFunction, riemannZeta, update
-/
def F (B : BadChar N) : Complex -> Complex :=
  Function.update (fun s : Complex => riemannZeta s * LFunction B.χ s) 1 (deriv (LFunction B.χ) 1)

/--
lemma `F_differentiableAt_of_ne` / 引理 `F_differentiableAt_of_ne`

English:
lemma F_differentiableAt_of_ne
  given: (B : BadChar N) {s : Complex} (hs : s != 1)
  proof: by
  apply DifferentiableAt.congr_of_eventuallyEq
· exact (differentiableAt_riemannZeta hs).mul differentiableAt_LFunction B.χ s (.inl hs)
  · filter_upwards [eventually_ne_nhds hs] with t ht using Function.update_of_ne ht ..

中文:
引理 F_differentiableAt_of_ne
  条件: (B : BadChar N) {s : 复形} (hs : s != 1)
  证明: by
  apply DifferentiableAt.congr_of_eventuallyEq
· exact (differentiableAt_riemannZeta hs).mul differentiableAt_LFunction B.χ s (.inl hs)
  · filter_upwards [eventually_ne_nhds hs] with t ht using Function.update_of_ne ht ..
-/
private lemma F_differentiableAt_of_ne (B : BadChar N) {s : Complex} (hs : s != 1) :
    DifferentiableAt Complex B.F s := by
  apply DifferentiableAt.congr_of_eventuallyEq
· exact (differentiableAt_riemannZeta hs).mul differentiableAt_LFunction B.χ s (.inl hs)
  · filter_upwards [eventually_ne_nhds hs] with t ht using Function.update_of_ne ht ..

/--
lemma `F_eq_LSeries` / 引理 `F_eq_LSeries`

English:
lemma F_eq_LSeries
  given: (B : BadChar N) {s : Complex} (hs : 1 < s.re)
  proof: by
  rw [F]; rw [zetaMul]; rw [← coe_mul]; rw [LSeries_convolution']
  · have hs' : s != 1 := fun h => by simp only [h, one_re, lt_self_iff_false] at hs
    simp only [ne_eq, hs', not_false_eq_true, Function.update_of_ne, B.χ.LFunction_eq_LSeries hs]
    congr 1
    · simp_rw [← LSeries_zeta_eq_riemannZeta hs, ← natCoe_apply]
    · exact LSeries_congr B.χ.apply_eq_toArithmeticFunction_apply s
  -- summability side goals from `LSeries_convolution'`
  · exact LSeriesSummable_zeta_iff.mpr hs
· exact (LSeriesSummable_congr _ fun h => (B.χ.apply_eq_toArithmeticFunction_apply h).symm).mpr
      ZMod.LSeriesSummable_of_one_lt_re B.χ hs

中文:
引理 F_eq_LSeries
  条件: (B : BadChar N) {s : 复形} (hs : 1 < s.re)
  证明: by
  rw [F]; rw [zetaMul]; rw [← coe_mul]; rw [LSeries_convolution']
  · have hs' : s != 1 := fun h => by simp only [h, one_re, lt_self_iff_false] at hs
    simp only [ne_eq, hs', not_false_eq_true, Function.update_of_ne, B.χ.LFunction_eq_LSeries hs]
    congr 1
    · simp_rw [← LSeries_zeta_eq_riemannZeta hs, ← natCoe_apply]
    · exact LSeries_congr B.χ.apply_eq_toArithmeticFunction_apply s
  -- summability side goals from `LSeries_convolution'`
  · exact LSeriesSummable_zeta_iff.mpr hs
· exact (LSeriesSummable_congr _ fun h => (B.χ.apply_eq_toArithmeticFunction_apply h).symm).mpr
      ZMod.LSeriesSummable_of_one_lt_re B.χ hs
-/
private lemma F_eq_LSeries (B : BadChar N) {s : Complex} (hs : 1 < s.re) :
    B.F s = LSeries B.χ.zetaMul s := by
  rw [F]; rw [zetaMul]; rw [← coe_mul]; rw [LSeries_convolution']
  · have hs' : s != 1 := fun h => by simp only [h, one_re, lt_self_iff_false] at hs
    simp only [ne_eq, hs', not_false_eq_true, Function.update_of_ne, B.χ.LFunction_eq_LSeries hs]
    congr 1
    · simp_rw [← LSeries_zeta_eq_riemannZeta hs, ← natCoe_apply]
    · exact LSeries_congr B.χ.apply_eq_toArithmeticFunction_apply s
  -- summability side goals from `LSeries_convolution'`
  · exact LSeriesSummable_zeta_iff.mpr hs
· exact (LSeriesSummable_congr _ fun h => (B.χ.apply_eq_toArithmeticFunction_apply h).symm).mpr
      ZMod.LSeriesSummable_of_one_lt_re B.χ hs

/--
lemma `F_differentiable` / 引理 `F_differentiable`

English:
lemma F_differentiable
  given: (B : BadChar N)
  statement: Differentiable Complex B.F
  proof: by
  intro s
  rcases ne_or_eq s 1 with hs | rfl
  · exact B.F_differentiableAt_of_ne hs
  -- now need to deal with `s = 1`
  refine (analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt ?_ ?_).differentiableAt
  · filter_upwards [self_mem_nhdsWithin] with t ht
    exact B.F_differentiableAt_of_ne ht
  -- now reduced to showing *continuity* at s = 1
  let G := Function.update (fun s => (s - 1) * riemannZeta s) 1 1
  let H := Function.update (fun s => (B.χ.LFunction s - B.χ.LFunction 1) / (s - 1)) 1
    (deriv B.χ.LFunction 1)
  have : B.F = G * H := by
    ext1 t
    rcases eq_or_ne t 1 with rfl | ht
    · simp only [F, G, H, Pi.mul_apply, one_mul, Function.update_self]
    · simp only [F, G, H, Function.update_of_ne ht, mul_comm _ (riemannZeta _), B.hχ, sub_zero,
      Pi.mul_apply, mul_assoc, mul_div_cancel₀ _ (sub_ne_zero.mpr ht)]
  rw [this]
  apply ContinuousAt.mul
  · simpa only [G, continuousAt_update_same] using riemannZeta_residue_one
  · exact (B.χ.differentiableAt_LFunction 1 (.inr B.χ_ne)).hasDerivAt.continuousAt_div

中文:
引理 F_differentiable
  条件: (B : BadChar N)
  结论: 可微 复形 B.F
  证明: by
  intro s
  rcases ne_or_eq s 1 with hs | rfl
  · exact B.F_differentiableAt_of_ne hs
  -- now need to deal with `s = 1`
  refine (analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt ?_ ?_).differentiableAt
  · filter_upwards [self_mem_nhdsWithin] with t ht
    exact B.F_differentiableAt_of_ne ht
  -- now reduced to showing *continuity* at s = 1
  let G := Function.update (fun s => (s - 1) * riemannZeta s) 1 1
  let H := Function.update (fun s => (B.χ.LFunction s - B.χ.LFunction 1) / (s - 1)) 1
    (deriv B.χ.LFunction 1)
  have : B.F = G * H := by
    ext1 t
    rcases eq_or_ne t 1 with rfl | ht
    · simp only [F, G, H, Pi.mul_apply, one_mul, Function.update_self]
    · simp only [F, G, H, Function.update_of_ne ht, mul_comm _ (riemannZeta _), B.hχ, sub_zero,
      Pi.mul_apply, mul_assoc, mul_div_cancel₀ _ (sub_ne_zero.mpr ht)]
  rw [this]
  apply ContinuousAt.mul
  · simpa only [G, continuousAt_update_same] using riemannZeta_residue_one
  · exact (B.χ.differentiableAt_LFunction 1 (.inr B.χ_ne)).hasDerivAt.continuousAt_div
-/
private lemma F_differentiable (B : BadChar N) : Differentiable Complex B.F := by
  intro s
  rcases ne_or_eq s 1 with hs | rfl
  · exact B.F_differentiableAt_of_ne hs
  -- now need to deal with `s = 1`
  refine (analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt ?_ ?_).differentiableAt
  · filter_upwards [self_mem_nhdsWithin] with t ht
    exact B.F_differentiableAt_of_ne ht
  -- now reduced to showing *continuity* at s = 1
  let G := Function.update (fun s => (s - 1) * riemannZeta s) 1 1
  let H := Function.update (fun s => (B.χ.LFunction s - B.χ.LFunction 1) / (s - 1)) 1
    (deriv B.χ.LFunction 1)
  have : B.F = G * H := by
    ext1 t
    rcases eq_or_ne t 1 with rfl | ht
    · simp only [F, G, H, Pi.mul_apply, one_mul, Function.update_self]
    · simp only [F, G, H, Function.update_of_ne ht, mul_comm _ (riemannZeta _), B.hχ, sub_zero,
      Pi.mul_apply, mul_assoc, mul_div_cancel₀ _ (sub_ne_zero.mpr ht)]
  rw [this]
  apply ContinuousAt.mul
  · simpa only [G, continuousAt_update_same] using riemannZeta_residue_one
  · exact (B.χ.differentiableAt_LFunction 1 (.inr B.χ_ne)).hasDerivAt.continuousAt_div

/--
lemma `F_neg_two` / 引理 `F_neg_two`

English:
lemma F_neg_two
  given: (B : BadChar N)
  statement: B.F (-2 : Real) = 0
  proof: by
  have := riemannZeta_neg_two_mul_nat_add_one 0
  rw [Nat.cast_zero]; rw [zero_add]; rw [mul_one] at this
  rw [F]; rw [ofReal_neg]; rw [ofReal_ofNat]; rw [Function.update_of_ne (mod_cast (by lia : (-2 : Int) != 1))]; rw [this]; rw [zero_mul]

中文:
引理 F_neg_two
  条件: (B : BadChar N)
  结论: B.F (-2 : 实数) = 0
  证明: by
  have := riemannZeta_neg_two_mul_nat_add_one 0
  rw [Nat.cast_zero]; rw [zero_add]; rw [mul_one] at this
  rw [F]; rw [ofReal_neg]; rw [ofReal_ofNat]; rw [Function.update_of_ne (mod_cast (by lia : (-2 : Int) != 1))]; rw [this]; rw [zero_mul]
-/
private lemma F_neg_two (B : BadChar N) : B.F (-2 : Real) = 0 := by
  have := riemannZeta_neg_two_mul_nat_add_one 0
  rw [Nat.cast_zero]; rw [zero_add]; rw [mul_one] at this
  rw [F]; rw [ofReal_neg]; rw [ofReal_ofNat]; rw [Function.update_of_ne (mod_cast (by lia : (-2 : Int) != 1))]; rw [this]; rw [zero_mul]

end BadChar

/--
theorem `LFunction_apply_one_ne_zero_of_quadratic` / 定理 `LFunction_apply_one_ne_zero_of_quadratic`

English:
theorem LFunction_apply_one_ne_zero_of_quadratic
  statement: {χ : DirichletCharacter Complex N}
  proof: by
  intro hL
  -- construct a "bad character" and put together a contradiction.
  let B : BadChar N := { χ := χ, χ_sq := hχ, hχ := hL, χ_ne := χ_ne }
  refine B.F_neg_two.not_gt ?_
  refine ArithmeticFunction.LSeries_positive_of_differentiable_of_eqOn (zetaMul_nonneg hχ)
    (χ.isMultiplicative_zetaMul.map_one ▸ zero_lt_one) B.F_differentiable ?_
    (fun _ => B.F_eq_LSeries) _
  exact LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable
    fun _ a => χ.LSeriesSummable_zetaMul a

中文:
定理 LFunction_apply_one_ne_zero_of_quadratic
  结论: {χ : DirichletCharacter 复形 N}
  证明: by
  intro hL
  -- construct a "bad character" and put together a contradiction.
  let B : BadChar N := { χ := χ, χ_sq := hχ, hχ := hL, χ_ne := χ_ne }
  refine B.F_neg_two.not_gt ?_
  refine ArithmeticFunction.LSeries_positive_of_differentiable_of_eqOn (zetaMul_nonneg hχ)
    (χ.isMultiplicative_zetaMul.map_one ▸ zero_lt_one) B.F_differentiable ?_
    (fun _ => B.F_eq_LSeries) _
  exact LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable
    fun _ a => χ.LSeriesSummable_zetaMul a
-/
private theorem LFunction_apply_one_ne_zero_of_quadratic {χ : DirichletCharacter Complex N}
    (hχ : χ ^ 2 = 1) (χ_ne : χ != 1) :
    χ.LFunction 1 != 0 := by
  intro hL
  -- construct a "bad character" and put together a contradiction.
  let B : BadChar N := { χ := χ, χ_sq := hχ, hχ := hL, χ_ne := χ_ne }
  refine B.F_neg_two.not_gt ?_
  refine ArithmeticFunction.LSeries_positive_of_differentiable_of_eqOn (zetaMul_nonneg hχ)
    (χ.isMultiplicative_zetaMul.map_one ▸ zero_lt_one) B.F_differentiable ?_
    (fun _ => B.F_eq_LSeries) _
  exact LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable
    fun _ a => χ.LSeriesSummable_zetaMul a

end quadratic

section nonvanishing

variable (χ : DirichletCharacter Complex N)

-- This is the key positivity lemma that is used to show that the L-function
-- of a Dirichlet character `χ` does not vanish for `s.re ≥ 1` (unless `χ^2 = 1` and `s = 1`).
/--
lemma `re_log_comb_nonneg'` / 引理 `re_log_comb_nonneg'`

English:
lemma re_log_comb_nonneg'
  given: {a : Real} (ha₀ : 0 <= a) (ha₁ : a < 1) {z : Complex} (hz : ‖z‖ = 1)
  proof: by
  have hac₀ : ‖(a : Complex)‖ < 1 := by
    simp only [Complex.norm_of_nonneg ha₀, ha₁]
  have hac₁ : ‖a * z‖ < 1 := by rwa [norm_mul, hz, mul_one]
  have hac₂ : ‖a * z ^ 2‖ < 1 := by rwa [norm_mul, norm_pow, hz, one_pow, mul_one]
  rw [← ((hasSum_re <| hasSum_taylorSeries_neg_log hac₀).mul_left 3).add
.add ((hasSum_re <| hasSum_taylorSeries_neg_log hac₁).mul_left 4)
.tsum_eq] (hasSum_re <| hasSum_taylorSeries_neg_log hac₂)
  refine tsum_nonneg fun n => ?_
  simp only [← ofReal_pow, div_natCast_re, ofReal_re, mul_pow, mul_re, ofReal_im, zero_mul,
    sub_zero]
  rcases n.eq_zero_or_pos with rfl | hn
  · simp
  · simp only [← mul_div_assoc, ← add_div]
    refine div_nonneg ?_ n.cast_nonneg
    rw [← pow_mul]; rw [pow_mul']; rw [sq]; rw [mul_re]; rw [← sq]; rw [← sq]; rw [← sq_norm_sub_sq_re]; rw [norm_pow]; rw [hz]
    convert! (show 0 <= 2 * a ^ n * ((z ^ n).re + 1) ^ 2 by positivity) using 1
    ring

中文:
引理 re_log_comb_nonneg'
  条件: {a : 实数} (ha₀ : 0 <= a) (ha₁ : a < 1) {z : 复形} (hz : ‖z‖ = 1)
  证明: by
  have hac₀ : ‖(a : Complex)‖ < 1 := by
    simp only [Complex.norm_of_nonneg ha₀, ha₁]
  have hac₁ : ‖a * z‖ < 1 := by rwa [norm_mul, hz, mul_one]
  have hac₂ : ‖a * z ^ 2‖ < 1 := by rwa [norm_mul, norm_pow, hz, one_pow, mul_one]
  rw [← ((hasSum_re <| hasSum_taylorSeries_neg_log hac₀).mul_left 3).add
.add ((hasSum_re <| hasSum_taylorSeries_neg_log hac₁).mul_left 4)
.tsum_eq] (hasSum_re <| hasSum_taylorSeries_neg_log hac₂)
  refine tsum_nonneg fun n => ?_
  simp only [← ofReal_pow, div_natCast_re, ofReal_re, mul_pow, mul_re, ofReal_im, zero_mul,
    sub_zero]
  rcases n.eq_zero_or_pos with rfl | hn
  · simp
  · simp only [← mul_div_assoc, ← add_div]
    refine div_nonneg ?_ n.cast_nonneg
    rw [← pow_mul]; rw [pow_mul']; rw [sq]; rw [mul_re]; rw [← sq]; rw [← sq]; rw [← sq_norm_sub_sq_re]; rw [norm_pow]; rw [hz]
    convert! (show 0 <= 2 * a ^ n * ((z ^ n).re + 1) ^ 2 by positivity) using 1
    ring
-/
private lemma re_log_comb_nonneg' {a : Real} (ha₀ : 0 <= a) (ha₁ : a < 1) {z : Complex} (hz : ‖z‖ = 1) :
      0 <= 3 * (-log (1 - a)).re + 4 * (-log (1 - a * z)).re + (-log (1 - a * z ^ 2)).re := by
  have hac₀ : ‖(a : Complex)‖ < 1 := by
    simp only [Complex.norm_of_nonneg ha₀, ha₁]
  have hac₁ : ‖a * z‖ < 1 := by rwa [norm_mul, hz, mul_one]
  have hac₂ : ‖a * z ^ 2‖ < 1 := by rwa [norm_mul, norm_pow, hz, one_pow, mul_one]
  rw [← ((hasSum_re <| hasSum_taylorSeries_neg_log hac₀).mul_left 3).add
.add ((hasSum_re <| hasSum_taylorSeries_neg_log hac₁).mul_left 4)
.tsum_eq] (hasSum_re <| hasSum_taylorSeries_neg_log hac₂)
  refine tsum_nonneg fun n => ?_
  simp only [← ofReal_pow, div_natCast_re, ofReal_re, mul_pow, mul_re, ofReal_im, zero_mul,
    sub_zero]
  rcases n.eq_zero_or_pos with rfl | hn
  · simp
  · simp only [← mul_div_assoc, ← add_div]
    refine div_nonneg ?_ n.cast_nonneg
    rw [← pow_mul]; rw [pow_mul']; rw [sq]; rw [mul_re]; rw [← sq]; rw [← sq]; rw [← sq_norm_sub_sq_re]; rw [norm_pow]; rw [hz]
    convert! (show 0 <= 2 * a ^ n * ((z ^ n).re + 1) ^ 2 by positivity) using 1
    ring

-- This is the version of the technical positivity lemma for logarithms of Euler factors.
/--
lemma `re_log_comb_nonneg` / 引理 `re_log_comb_nonneg`

English:
lemma re_log_comb_nonneg
  given: {n : Nat} (hn : 2 <= n) {x : Real} (hx : 1 < x) (y : Real)
  proof: by
  by_cases hn' : IsUnit (n : ZMod N)
  · have hn : (n : Real) ^ (-x) < 1 := by
      rw [Real.rpow_neg (Nat.cast_nonneg n)]; rw [inv_lt_one_iff₀]
exact .inr Real.one_lt_rpow (mod_cast one_lt_two.trans_le hn) zero_lt_one.trans hx
    have hz : ‖χ n * (n : Complex) ^ (-(I * y))‖ = 1 := by
      rw [norm_mul]; rw [← hn'.unit_spec]; rw [DirichletCharacter.unit_norm_eq_one χ hn'.unit]; rw [← ofReal_natCast]; rw [norm_cpow_eq_rpow_re_of_pos (mod_cast by lia)]
      simp only [neg_re, mul_re, I_re, ofReal_re, zero_mul, I_im, ofReal_im, mul_zero, sub_self,
        neg_zero, Real.rpow_zero, one_mul]
    rw [MulChar.one_apply hn']; rw [one_mul]
    convert! re_log_comb_nonneg' (by positivity) hn hz using 6
    · simp only [ofReal_cpow n.cast_nonneg (-x), ofReal_natCast, ofReal_neg]
    · congr 2
      rw [neg_add]; rw [cpow_add _ _ <| mod_cast by lia]; rw [← ofReal_neg]; rw [ofReal_cpow n.cast_nonneg (-x)]; rw [ofReal_natCast]; rw [mul_left_comm]
    · rw [neg_add, cpow_add _ _ <| mod_cast by lia, ← ofReal_neg, ofReal_cpow n.cast_nonneg (-x),
        ofReal_natCast, show -(2 * I * y) = (2 : Nat) * -(I * y) by ring, cpow_nat_mul, mul_pow,
        mul_left_comm]
  · simp only [MulChar.map_nonunit _ hn', zero_mul, sub_zero, log_one, neg_zero, zero_re, mul_zero,
      neg_add_rev, add_zero, pow_two, le_refl]

中文:
引理 re_log_comb_nonneg
  条件: {n : 自然数} (hn : 2 <= n) {x : 实数} (hx : 1 < x) (y : 实数)
  证明: by
  by_cases hn' : IsUnit (n : ZMod N)
  · have hn : (n : Real) ^ (-x) < 1 := by
      rw [Real.rpow_neg (Nat.cast_nonneg n)]; rw [inv_lt_one_iff₀]
exact .inr Real.one_lt_rpow (mod_cast one_lt_two.trans_le hn) zero_lt_one.trans hx
    have hz : ‖χ n * (n : Complex) ^ (-(I * y))‖ = 1 := by
      rw [norm_mul]; rw [← hn'.unit_spec]; rw [DirichletCharacter.unit_norm_eq_one χ hn'.unit]; rw [← ofReal_natCast]; rw [norm_cpow_eq_rpow_re_of_pos (mod_cast by lia)]
      simp only [neg_re, mul_re, I_re, ofReal_re, zero_mul, I_im, ofReal_im, mul_zero, sub_self,
        neg_zero, Real.rpow_zero, one_mul]
    rw [MulChar.one_apply hn']; rw [one_mul]
    convert! re_log_comb_nonneg' (by positivity) hn hz using 6
    · simp only [ofReal_cpow n.cast_nonneg (-x), ofReal_natCast, ofReal_neg]
    · congr 2
      rw [neg_add]; rw [cpow_add _ _ <| mod_cast by lia]; rw [← ofReal_neg]; rw [ofReal_cpow n.cast_nonneg (-x)]; rw [ofReal_natCast]; rw [mul_left_comm]
    · rw [neg_add, cpow_add _ _ <| mod_cast by lia, ← ofReal_neg, ofReal_cpow n.cast_nonneg (-x),
        ofReal_natCast, show -(2 * I * y) = (2 : Nat) * -(I * y) by ring, cpow_nat_mul, mul_pow,
        mul_left_comm]
  · simp only [MulChar.map_nonunit _ hn', zero_mul, sub_zero, log_one, neg_zero, zero_re, mul_zero,
      neg_add_rev, add_zero, pow_two, le_refl]
-/
private lemma re_log_comb_nonneg {n : Nat} (hn : 2 <= n) {x : Real} (hx : 1 < x) (y : Real) :
    0 <= 3 * (-log (1 - (1 : DirichletCharacter Complex N) n * n ^ (-x : Complex))).re +
          4 * (-log (1 - χ n * n ^ (-(x + I * y)))).re +
          (-log (1 - (χ n ^ 2) * n ^ (-(x + 2 * I * y)))).re := by
  by_cases hn' : IsUnit (n : ZMod N)
  · have hn : (n : Real) ^ (-x) < 1 := by
      rw [Real.rpow_neg (Nat.cast_nonneg n)]; rw [inv_lt_one_iff₀]
exact .inr Real.one_lt_rpow (mod_cast one_lt_two.trans_le hn) zero_lt_one.trans hx
    have hz : ‖χ n * (n : Complex) ^ (-(I * y))‖ = 1 := by
      rw [norm_mul]; rw [← hn'.unit_spec]; rw [DirichletCharacter.unit_norm_eq_one χ hn'.unit]; rw [← ofReal_natCast]; rw [norm_cpow_eq_rpow_re_of_pos (mod_cast by lia)]
      simp only [neg_re, mul_re, I_re, ofReal_re, zero_mul, I_im, ofReal_im, mul_zero, sub_self,
        neg_zero, Real.rpow_zero, one_mul]
    rw [MulChar.one_apply hn']; rw [one_mul]
    convert! re_log_comb_nonneg' (by positivity) hn hz using 6
    · simp only [ofReal_cpow n.cast_nonneg (-x), ofReal_natCast, ofReal_neg]
    · congr 2
      rw [neg_add]; rw [cpow_add _ _ <| mod_cast by lia]; rw [← ofReal_neg]; rw [ofReal_cpow n.cast_nonneg (-x)]; rw [ofReal_natCast]; rw [mul_left_comm]
    · rw [neg_add, cpow_add _ _ <| mod_cast by lia, ← ofReal_neg, ofReal_cpow n.cast_nonneg (-x),
        ofReal_natCast, show -(2 * I * y) = (2 : Nat) * -(I * y) by ring, cpow_nat_mul, mul_pow,
        mul_left_comm]
  · simp only [MulChar.map_nonunit _ hn', zero_mul, sub_zero, log_one, neg_zero, zero_re, mul_zero,
      neg_add_rev, add_zero, pow_two, le_refl]

/--
lemma `summable_neg_log_one_sub_mul_prime_cpow` / 引理 `summable_neg_log_one_sub_mul_prime_cpow`

English:
lemma summable_neg_log_one_sub_mul_prime_cpow
  given: {s : Complex} (hs : 1 < s.re)
  proof: by
  have (p : Nat.Primes) : ‖χ p * (p : Complex) ^ (-s)‖ <= (p : Real) ^ (-s).re := by
    simpa only [norm_mul, norm_natCast_cpow_of_re_ne_zero _ <| re_neg_ne_zero_of_one_lt_re hs]
      using mul_le_of_le_one_left (by positivity) (χ.norm_le_one _)
  refine (Nat.Primes.summable_rpow.mpr ?_).of_nonneg_of_le (fun _ => norm_nonneg _) this
.of_norm.clog_one_sub.neg
  simp only [neg_re, neg_lt_neg_iff, hs]

中文:
引理 summable_neg_log_one_sub_mul_prime_cpow
  条件: {s : 复形} (hs : 1 < s.re)
  证明: by
  have (p : Nat.Primes) : ‖χ p * (p : Complex) ^ (-s)‖ <= (p : Real) ^ (-s).re := by
    simpa only [norm_mul, norm_natCast_cpow_of_re_ne_zero _ <| re_neg_ne_zero_of_one_lt_re hs]
      using mul_le_of_le_one_left (by positivity) (χ.norm_le_one _)
  refine (Nat.Primes.summable_rpow.mpr ?_).of_nonneg_of_le (fun _ => norm_nonneg _) this
.of_norm.clog_one_sub.neg
  simp only [neg_re, neg_lt_neg_iff, hs]

Depends on / 依赖: Nat.Primes, Nat.Primes.summable_rpow.mpr, Primes, clog_one_sub, mul_le_of_le_one_left, neg_lt_neg_iff, neg_re, norm_le_one, norm_mul, norm_natCast_cpow_of_re_ne_zero, norm_nonneg, of_nonneg_of_le, of_norm, of_norm.clog_one_sub.neg, re_neg_ne_zero_of_one_lt_re, summable_rpow
-/
lemma summable_neg_log_one_sub_mul_prime_cpow {s : Complex} (hs : 1 < s.re) :
    Summable fun p : Nat.Primes => -log (1 - χ p * (p : Complex) ^ (-s)) := by
  have (p : Nat.Primes) : ‖χ p * (p : Complex) ^ (-s)‖ <= (p : Real) ^ (-s).re := by
    simpa only [norm_mul, norm_natCast_cpow_of_re_ne_zero _ <| re_neg_ne_zero_of_one_lt_re hs]
      using mul_le_of_le_one_left (by positivity) (χ.norm_le_one _)
  refine (Nat.Primes.summable_rpow.mpr ?_).of_nonneg_of_le (fun _ => norm_nonneg _) this
.of_norm.clog_one_sub.neg
  simp only [neg_re, neg_lt_neg_iff, hs]

/--
lemma `one_lt_re_one_add` / 引理 `one_lt_re_one_add`

English:
lemma one_lt_re_one_add
  given: {x : Real} (hx : 0 < x) (y : Real)
  proof: by
  simp only [add_re, one_re, ofReal_re, lt_add_iff_pos_right, hx, mul_re, I_re, zero_mul, I_im,
    ofReal_im, mul_zero, sub_self, add_zero, re_ofNat, im_ofNat, mul_one, mul_im, and_self]

中文:
引理 one_lt_re_one_add
  条件: {x : 实数} (hx : 0 < x) (y : 实数)
  证明: by
  simp only [add_re, one_re, ofReal_re, lt_add_iff_pos_right, hx, mul_re, I_re, zero_mul, I_im,
    ofReal_im, mul_zero, sub_self, add_zero, re_ofNat, im_ofNat, mul_one, mul_im, and_self]
-/
private lemma one_lt_re_one_add {x : Real} (hx : 0 < x) (y : Real) :
    1 < (1 + x : Complex).re ∧ 1 < (1 + x + I * y).re ∧ 1 < (1 + x + 2 * I * y).re := by
  simp only [add_re, one_re, ofReal_re, lt_add_iff_pos_right, hx, mul_re, I_re, zero_mul, I_im,
    ofReal_im, mul_zero, sub_self, add_zero, re_ofNat, im_ofNat, mul_one, mul_im, and_self]

open scoped LSeries.notation in
/--
lemma `norm_LSeries_product_ge_one` / 引理 `norm_LSeries_product_ge_one`

English:
lemma norm_LSeries_product_ge_one
  given: {x : Real} (hx : 0 < x) (y : Real)
  proof: by
  have ⟨h₀, h₁, h₂⟩ := one_lt_re_one_add hx y
  have H₀ := summable_neg_log_one_sub_mul_prime_cpow (N := N) 1 h₀
  have H₁ := summable_neg_log_one_sub_mul_prime_cpow χ h₁
  have H₂ := summable_neg_log_one_sub_mul_prime_cpow (χ ^ 2) h₂
  have hsum₀ := (hasSum_re H₀.hasSum).summable.mul_left 3
  have hsum₁ := (hasSum_re H₁.hasSum).summable.mul_left 4
  have hsum₂ := (hasSum_re H₂.hasSum).summable
  rw [← LSeries_eulerProduct_exp_log _ h₀]; rw [← LSeries_eulerProduct_exp_log χ h₁]; rw [← LSeries_eulerProduct_exp_log _ h₂]
  simp only [← exp_nat_mul, Nat.cast_ofNat, ← exp_add, norm_exp, add_re, mul_re,
    re_ofNat, im_ofNat, zero_mul, sub_zero, Real.one_le_exp_iff]
  rw [re_tsum H₀]; rw [re_tsum H₁]; rw [re_tsum H₂]; rw [← tsum_mul_left]; rw [← tsum_mul_left]; rw [← hsum₀.tsum_add hsum₁]; rw [← (hsum₀.add hsum₁).tsum_add hsum₂]
  simpa only [neg_add_rev, neg_re, mul_neg, χ.pow_apply' two_ne_zero, ge_iff_le, add_re, one_re,
    ofReal_re, ofReal_add, ofReal_one] using
      tsum_nonneg fun (p : Nat.Primes) => χ.re_log_comb_nonneg p.prop.two_le h₀ y

中文:
引理 norm_LSeries_product_ge_one
  条件: {x : 实数} (hx : 0 < x) (y : 实数)
  证明: by
  have ⟨h₀, h₁, h₂⟩ := one_lt_re_one_add hx y
  have H₀ := summable_neg_log_one_sub_mul_prime_cpow (N := N) 1 h₀
  have H₁ := summable_neg_log_one_sub_mul_prime_cpow χ h₁
  have H₂ := summable_neg_log_one_sub_mul_prime_cpow (χ ^ 2) h₂
  have hsum₀ := (hasSum_re H₀.hasSum).summable.mul_left 3
  have hsum₁ := (hasSum_re H₁.hasSum).summable.mul_left 4
  have hsum₂ := (hasSum_re H₂.hasSum).summable
  rw [← LSeries_eulerProduct_exp_log _ h₀]; rw [← LSeries_eulerProduct_exp_log χ h₁]; rw [← LSeries_eulerProduct_exp_log _ h₂]
  simp only [← exp_nat_mul, Nat.cast_ofNat, ← exp_add, norm_exp, add_re, mul_re,
    re_ofNat, im_ofNat, zero_mul, sub_zero, Real.one_le_exp_iff]
  rw [re_tsum H₀]; rw [re_tsum H₁]; rw [re_tsum H₂]; rw [← tsum_mul_left]; rw [← tsum_mul_left]; rw [← hsum₀.tsum_add hsum₁]; rw [← (hsum₀.add hsum₁).tsum_add hsum₂]
  simpa only [neg_add_rev, neg_re, mul_neg, χ.pow_apply' two_ne_zero, ge_iff_le, add_re, one_re,
    ofReal_re, ofReal_add, ofReal_one] using
      tsum_nonneg fun (p : Nat.Primes) => χ.re_log_comb_nonneg p.prop.two_le h₀ y

Depends on / 依赖: LSeries_eulerProduct_ex, LSeries_eulerProduct_exp_log, hasSum, hasSum_re, mul_left, one_lt_re_one_add, summable, summable.mul_left, summable_neg_log_one_sub_mul_prime_cpow
-/
lemma norm_LSeries_product_ge_one {x : Real} (hx : 0 < x) (y : Real) :
    ‖L ↗(1 : DirichletCharacter Complex N) (1 + x) ^ 3 * L ↗χ (1 + x + I * y) ^ 4 *
      L ↗(χ ^ 2 :) (1 + x + 2 * I * y)‖ >= 1 := by
  have ⟨h₀, h₁, h₂⟩ := one_lt_re_one_add hx y
  have H₀ := summable_neg_log_one_sub_mul_prime_cpow (N := N) 1 h₀
  have H₁ := summable_neg_log_one_sub_mul_prime_cpow χ h₁
  have H₂ := summable_neg_log_one_sub_mul_prime_cpow (χ ^ 2) h₂
  have hsum₀ := (hasSum_re H₀.hasSum).summable.mul_left 3
  have hsum₁ := (hasSum_re H₁.hasSum).summable.mul_left 4
  have hsum₂ := (hasSum_re H₂.hasSum).summable
  rw [← LSeries_eulerProduct_exp_log _ h₀]; rw [← LSeries_eulerProduct_exp_log χ h₁]; rw [← LSeries_eulerProduct_exp_log _ h₂]
  simp only [← exp_nat_mul, Nat.cast_ofNat, ← exp_add, norm_exp, add_re, mul_re,
    re_ofNat, im_ofNat, zero_mul, sub_zero, Real.one_le_exp_iff]
  rw [re_tsum H₀]; rw [re_tsum H₁]; rw [re_tsum H₂]; rw [← tsum_mul_left]; rw [← tsum_mul_left]; rw [← hsum₀.tsum_add hsum₁]; rw [← (hsum₀.add hsum₁).tsum_add hsum₂]
  simpa only [neg_add_rev, neg_re, mul_neg, χ.pow_apply' two_ne_zero, ge_iff_le, add_re, one_re,
    ofReal_re, ofReal_add, ofReal_one] using
      tsum_nonneg fun (p : Nat.Primes) => χ.re_log_comb_nonneg p.prop.two_le h₀ y

variable [NeZero N]

/--
lemma `norm_LFunction_product_ge_one` / 引理 `norm_LFunction_product_ge_one`

English:
lemma norm_LFunction_product_ge_one
  given: {x : Real} (hx : 0 < x) (y : Real)
  proof: by
  have ⟨h₀, h₁, h₂⟩ := one_lt_re_one_add hx y
  rw [LFunctionTrivChar]; rw [DirichletCharacter.LFunction_eq_LSeries 1 h₀]; rw [χ.LFunction_eq_LSeries h₁]; rw [(χ ^ 2).LFunction_eq_LSeries h₂]
  exact norm_LSeries_product_ge_one χ hx y

中文:
引理 norm_LFunction_product_ge_one
  条件: {x : 实数} (hx : 0 < x) (y : 实数)
  证明: by
  have ⟨h₀, h₁, h₂⟩ := one_lt_re_one_add hx y
  rw [LFunctionTrivChar]; rw [DirichletCharacter.LFunction_eq_LSeries 1 h₀]; rw [χ.LFunction_eq_LSeries h₁]; rw [(χ ^ 2).LFunction_eq_LSeries h₂]
  exact norm_LSeries_product_ge_one χ hx y

Depends on / 依赖: DirichletCharacter, DirichletCharacter.LFunction_eq_LSeries, LFunctionTrivChar, LFunction_eq_LSeries, norm_LSeries_product_ge_one, one_lt_re_one_add
-/
lemma norm_LFunction_product_ge_one {x : Real} (hx : 0 < x) (y : Real) :
    ‖LFunctionTrivChar N (1 + x) ^ 3 * LFunction χ (1 + x + I * y) ^ 4 *
      LFunction (χ ^ 2) (1 + x + 2 * I * y)‖ >= 1 := by
  have ⟨h₀, h₁, h₂⟩ := one_lt_re_one_add hx y
  rw [LFunctionTrivChar]; rw [DirichletCharacter.LFunction_eq_LSeries 1 h₀]; rw [χ.LFunction_eq_LSeries h₁]; rw [(χ ^ 2).LFunction_eq_LSeries h₂]
  exact norm_LSeries_product_ge_one χ hx y

/--
lemma `LFunctionTrivChar_isBigO_near_one_horizontal` / 引理 `LFunctionTrivChar_isBigO_near_one_horizontal`

English:
lemma LFunctionTrivChar_isBigO_near_one_horizontal
  proof: by
  have : (fun w : Complex => LFunctionTrivChar N (1 + w)) =O[𝓝[!=] 0] (1 / ·) := by
    have H : Tendsto (fun w => w * LFunctionTrivChar N (1 + w)) (𝓝[!=] 0)
        (𝓝 <| ∏ p in N.primeFactors, (1 - (p : Complex)⁻¹)) := by
      convert! (LFunctionTrivChar_residue_one (N := N)).comp (f := fun w => 1 + w) ?_ using 1
      · simp only [Function.comp_def, add_sub_cancel_left]
      · simpa only [tendsto_iff_comap, Homeomorph.coe_addLeft, add_zero, map_le_iff_le_comap] using
          ((Homeomorph.addLeft (1 : Complex)).map_punctured_nhds_eq 0).le
exact (isBigO_mul_iff_isBigO_div eventually_mem_nhdsWithin).mp H.isBigO_one Complex
exact (isBigO_comp_ofReal_nhds_ne this).mono nhdsGT_le_nhdsNE 0

omit [NeZero N] in

中文:
引理 LFunctionTrivChar_isBigO_near_one_horizontal
  证明: by
  have : (fun w : Complex => LFunctionTrivChar N (1 + w)) =O[𝓝[!=] 0] (1 / ·) := by
    have H : Tendsto (fun w => w * LFunctionTrivChar N (1 + w)) (𝓝[!=] 0)
        (𝓝 <| ∏ p in N.primeFactors, (1 - (p : Complex)⁻¹)) := by
      convert! (LFunctionTrivChar_residue_one (N := N)).comp (f := fun w => 1 + w) ?_ using 1
      · simp only [Function.comp_def, add_sub_cancel_left]
      · simpa only [tendsto_iff_comap, Homeomorph.coe_addLeft, add_zero, map_le_iff_le_comap] using
          ((Homeomorph.addLeft (1 : Complex)).map_punctured_nhds_eq 0).le
exact (isBigO_mul_iff_isBigO_div eventually_mem_nhdsWithin).mp H.isBigO_one Complex
exact (isBigO_comp_ofReal_nhds_ne this).mono nhdsGT_le_nhdsNE 0

omit [NeZero N] in

Depends on / 依赖: Function, Function.comp_def, Homeomorph, Homeomorph.addLeft, Homeomorph.coe_addLeft, LFunctionTrivChar, LFunctionTrivChar_residue_one, N.primeFactors, Tendsto, addLeft, add_sub_cancel_left, add_zero, coe_addLeft, comp_def, convert, map_le_iff_le_comap, map_punctured_nh, primeFactors, tendsto_iff_comap
-/
lemma LFunctionTrivChar_isBigO_near_one_horizontal :
    (fun x : Real => LFunctionTrivChar N (1 + x)) =O[𝓝[>] 0] fun x => (1 : Complex) / x := by
  have : (fun w : Complex => LFunctionTrivChar N (1 + w)) =O[𝓝[!=] 0] (1 / ·) := by
    have H : Tendsto (fun w => w * LFunctionTrivChar N (1 + w)) (𝓝[!=] 0)
        (𝓝 <| ∏ p in N.primeFactors, (1 - (p : Complex)⁻¹)) := by
      convert! (LFunctionTrivChar_residue_one (N := N)).comp (f := fun w => 1 + w) ?_ using 1
      · simp only [Function.comp_def, add_sub_cancel_left]
      · simpa only [tendsto_iff_comap, Homeomorph.coe_addLeft, add_zero, map_le_iff_le_comap] using
          ((Homeomorph.addLeft (1 : Complex)).map_punctured_nhds_eq 0).le
exact (isBigO_mul_iff_isBigO_div eventually_mem_nhdsWithin).mp H.isBigO_one Complex
exact (isBigO_comp_ofReal_nhds_ne this).mono nhdsGT_le_nhdsNE 0

omit [NeZero N] in
/--
lemma `one_add_I_mul_ne_one_or` / 引理 `one_add_I_mul_ne_one_or`

English:
lemma one_add_I_mul_ne_one_or
  given: {y : Real} (hy : y != 0 ∨ χ != 1)
  proof: by
  simpa only [ne_eq, add_eq_left, _root_.mul_eq_zero, I_ne_zero, ofReal_eq_zero, false_or]
    using hy

中文:
引理 one_add_I_mul_ne_one_or
  条件: {y : 实数} (hy : y != 0 ∨ χ != 1)
  证明: by
  simpa only [ne_eq, add_eq_left, _root_.mul_eq_zero, I_ne_zero, ofReal_eq_zero, false_or]
    using hy
-/
private lemma one_add_I_mul_ne_one_or {y : Real} (hy : y != 0 ∨ χ != 1) :
    1 + I * y != 1 ∨ χ != 1 := by
  simpa only [ne_eq, add_eq_left, _root_.mul_eq_zero, I_ne_zero, ofReal_eq_zero, false_or]
    using hy

/--
lemma `LFunction_isBigO_horizontal` / 引理 `LFunction_isBigO_horizontal`

English:
lemma LFunction_isBigO_horizontal
  given: {y : Real} (hy : y != 0 ∨ χ != 1)
  proof: by
  refine IsBigO.mono ?_ nhdsWithin_le_nhds
  simp_rw [add_comm (1 : Complex), add_assoc]
  have := (χ.differentiableAt_LFunction _ <| one_add_I_mul_ne_one_or χ hy).continuousAt
  rw [← zero_add (1 + _)] at this
.tendsto.isBigO_one Complex exact this.comp (f := fun x : Real => x + (1 + I * y)) (x := 0) (by fun_prop)

中文:
引理 LFunction_isBigO_horizontal
  条件: {y : 实数} (hy : y != 0 ∨ χ != 1)
  证明: by
  refine IsBigO.mono ?_ nhdsWithin_le_nhds
  simp_rw [add_comm (1 : Complex), add_assoc]
  have := (χ.differentiableAt_LFunction _ <| one_add_I_mul_ne_one_or χ hy).continuousAt
  rw [← zero_add (1 + _)] at this
.tendsto.isBigO_one Complex exact this.comp (f := fun x : Real => x + (1 + I * y)) (x := 0) (by fun_prop)

Depends on / 依赖: IsBigO, IsBigO.mono, add_assoc, add_comm, continuousAt, differentiableAt_LFunction, fun_prop, isBigO_one, nhdsWithin_le_nhds, one_add_I_mul_ne_one_or, simp_rw, tendsto, tendsto.isBigO_one, this.comp, zero_add
-/
lemma LFunction_isBigO_horizontal {y : Real} (hy : y != 0 ∨ χ != 1) :
    (fun x : Real => LFunction χ (1 + x + I * y)) =O[𝓝[>] 0] fun _ => (1 : Complex) := by
  refine IsBigO.mono ?_ nhdsWithin_le_nhds
  simp_rw [add_comm (1 : Complex), add_assoc]
  have := (χ.differentiableAt_LFunction _ <| one_add_I_mul_ne_one_or χ hy).continuousAt
  rw [← zero_add (1 + _)] at this
.tendsto.isBigO_one Complex exact this.comp (f := fun x : Real => x + (1 + I * y)) (x := 0) (by fun_prop)

/--
lemma `LFunction_isBigO_horizontal_of_eq_zero` / 引理 `LFunction_isBigO_horizontal_of_eq_zero`

English:
lemma LFunction_isBigO_horizontal_of_eq_zero
  statement: {y : Real} (hy : y != 0 ∨ χ != 1)
  proof: by
  simp_rw [add_comm (1 : Complex), add_assoc]
  have := (χ.differentiableAt_LFunction _ <| one_add_I_mul_ne_one_or χ hy).hasDerivAt
  rw [← zero_add (1 + _)] at this
  simpa only [zero_add, h, sub_zero]
    using (Complex.isBigO_comp_ofReal_nhds
      (this.comp_add_const 0 _).differentiableAt.isBigO_sub) |>.mono nhdsWithin_le_nhds

中文:
引理 LFunction_isBigO_horizontal_of_eq_zero
  结论: {y : 实数} (hy : y != 0 ∨ χ != 1)
  证明: by
  simp_rw [add_comm (1 : Complex), add_assoc]
  have := (χ.differentiableAt_LFunction _ <| one_add_I_mul_ne_one_or χ hy).hasDerivAt
  rw [← zero_add (1 + _)] at this
  simpa only [zero_add, h, sub_zero]
    using (Complex.isBigO_comp_ofReal_nhds
      (this.comp_add_const 0 _).differentiableAt.isBigO_sub) |>.mono nhdsWithin_le_nhds
-/
private lemma LFunction_isBigO_horizontal_of_eq_zero {y : Real} (hy : y != 0 ∨ χ != 1)
    (h : LFunction χ (1 + I * y) = 0) :
    (fun x : Real => LFunction χ (1 + x + I * y)) =O[𝓝[>] 0] fun x : Real => (x : Complex) := by
  simp_rw [add_comm (1 : Complex), add_assoc]
  have := (χ.differentiableAt_LFunction _ <| one_add_I_mul_ne_one_or χ hy).hasDerivAt
  rw [← zero_add (1 + _)] at this
  simpa only [zero_add, h, sub_zero]
    using (Complex.isBigO_comp_ofReal_nhds
      (this.comp_add_const 0 _).differentiableAt.isBigO_sub) |>.mono nhdsWithin_le_nhds

-- intermediate statement, special case of the next theorem
/--
lemma `LFunction_ne_zero_of_not_quadratic_or_ne_one` / 引理 `LFunction_ne_zero_of_not_quadratic_or_ne_one`

English:
lemma LFunction_ne_zero_of_not_quadratic_or_ne_one
  given: {t : Real} (h : χ ^ 2 != 1 ∨ t != 0)
  proof: by
  intro Hz
  have hz₁ : t != 0 ∨ χ != 1 := by
    refine h.symm.imp_right (fun h H => ?_)
    simp only [H, one_pow, ne_eq, not_true_eq_false] at h
  have hz₂ : 2 * t != 0 ∨ χ ^ 2 != 1 :=
h.symm.imp_left mul_ne_zero two_ne_zero
  have help (x : Real) : ((1 / x) ^ 3 * x ^ 4 * 1 : Complex) = x := by
    rcases eq_or_ne x 0 with rfl | h
    · rw [ofReal_zero, zero_pow (by lia), mul_zero, mul_one]
    · rw [one_div, inv_pow, pow_succ _ 3, ← mul_assoc,
inv_mul_cancel₀ pow_ne_zero 3 (ofReal_ne_zero.mpr h), one_mul, mul_one]
  -- put together the various `IsBigO` statements and `norm_LFunction_product_ge_one`
  -- to derive a contradiction
  have H₀ : (fun _ : Real => (1 : Real)) =O[𝓝[>] 0]
      fun x => LFunctionTrivChar N (1 + x) ^ 3 * LFunction χ (1 + x + I * t) ^ 4 *
                   LFunction (χ ^ 2) (1 + x + 2 * I * t) :=
IsBigO.of_bound' eventually_nhdsWithin_of_forall
      fun _ hx => (norm_one (α := Real)).symm ▸ (χ.norm_LFunction_product_ge_one hx t).le
.mul have H := (LFunctionTrivChar_isBigO_near_one_horizontal (N := N)).pow 3
.mul (χ.LFunction_isBigO_horizontal_of_eq_zero hz₁ Hz).pow 4
    LFunction_isBigO_horizontal _ hz₂
  simp only [ofReal_mul, ofReal_ofNat, mul_left_comm I, ← mul_assoc, help] at H
  -- go via absolute value to translate into a statement over `ℝ`
  replace H := (H₀.trans H).norm_right
  simp only [norm_real] at H
exact isLittleO_irrefl (.of_forall (fun _ => one_ne_zero))
H.of_norm_right.trans_isLittleO isLittleO_id_one.mono nhdsWithin_le_nhds

中文:
引理 LFunction_ne_zero_of_not_quadratic_or_ne_one
  条件: {t : 实数} (h : χ ^ 2 != 1 ∨ t != 0)
  证明: by
  intro Hz
  have hz₁ : t != 0 ∨ χ != 1 := by
    refine h.symm.imp_right (fun h H => ?_)
    simp only [H, one_pow, ne_eq, not_true_eq_false] at h
  have hz₂ : 2 * t != 0 ∨ χ ^ 2 != 1 :=
h.symm.imp_left mul_ne_zero two_ne_zero
  have help (x : Real) : ((1 / x) ^ 3 * x ^ 4 * 1 : Complex) = x := by
    rcases eq_or_ne x 0 with rfl | h
    · rw [ofReal_zero, zero_pow (by lia), mul_zero, mul_one]
    · rw [one_div, inv_pow, pow_succ _ 3, ← mul_assoc,
inv_mul_cancel₀ pow_ne_zero 3 (ofReal_ne_zero.mpr h), one_mul, mul_one]
  -- put together the various `IsBigO` statements and `norm_LFunction_product_ge_one`
  -- to derive a contradiction
  have H₀ : (fun _ : Real => (1 : Real)) =O[𝓝[>] 0]
      fun x => LFunctionTrivChar N (1 + x) ^ 3 * LFunction χ (1 + x + I * t) ^ 4 *
                   LFunction (χ ^ 2) (1 + x + 2 * I * t) :=
IsBigO.of_bound' eventually_nhdsWithin_of_forall
      fun _ hx => (norm_one (α := Real)).symm ▸ (χ.norm_LFunction_product_ge_one hx t).le
.mul have H := (LFunctionTrivChar_isBigO_near_one_horizontal (N := N)).pow 3
.mul (χ.LFunction_isBigO_horizontal_of_eq_zero hz₁ Hz).pow 4
    LFunction_isBigO_horizontal _ hz₂
  simp only [ofReal_mul, ofReal_ofNat, mul_left_comm I, ← mul_assoc, help] at H
  -- go via absolute value to translate into a statement over `ℝ`
  replace H := (H₀.trans H).norm_right
  simp only [norm_real] at H
exact isLittleO_irrefl (.of_forall (fun _ => one_ne_zero))
H.of_norm_right.trans_isLittleO isLittleO_id_one.mono nhdsWithin_le_nhds
-/
private lemma LFunction_ne_zero_of_not_quadratic_or_ne_one {t : Real} (h : χ ^ 2 != 1 ∨ t != 0) :
    LFunction χ (1 + I * t) != 0 := by
  intro Hz
  have hz₁ : t != 0 ∨ χ != 1 := by
    refine h.symm.imp_right (fun h H => ?_)
    simp only [H, one_pow, ne_eq, not_true_eq_false] at h
  have hz₂ : 2 * t != 0 ∨ χ ^ 2 != 1 :=
h.symm.imp_left mul_ne_zero two_ne_zero
  have help (x : Real) : ((1 / x) ^ 3 * x ^ 4 * 1 : Complex) = x := by
    rcases eq_or_ne x 0 with rfl | h
    · rw [ofReal_zero, zero_pow (by lia), mul_zero, mul_one]
    · rw [one_div, inv_pow, pow_succ _ 3, ← mul_assoc,
inv_mul_cancel₀ pow_ne_zero 3 (ofReal_ne_zero.mpr h), one_mul, mul_one]
  -- put together the various `IsBigO` statements and `norm_LFunction_product_ge_one`
  -- to derive a contradiction
  have H₀ : (fun _ : Real => (1 : Real)) =O[𝓝[>] 0]
      fun x => LFunctionTrivChar N (1 + x) ^ 3 * LFunction χ (1 + x + I * t) ^ 4 *
                   LFunction (χ ^ 2) (1 + x + 2 * I * t) :=
IsBigO.of_bound' eventually_nhdsWithin_of_forall
      fun _ hx => (norm_one (α := Real)).symm ▸ (χ.norm_LFunction_product_ge_one hx t).le
.mul have H := (LFunctionTrivChar_isBigO_near_one_horizontal (N := N)).pow 3
.mul (χ.LFunction_isBigO_horizontal_of_eq_zero hz₁ Hz).pow 4
    LFunction_isBigO_horizontal _ hz₂
  simp only [ofReal_mul, ofReal_ofNat, mul_left_comm I, ← mul_assoc, help] at H
  -- go via absolute value to translate into a statement over `ℝ`
  replace H := (H₀.trans H).norm_right
  simp only [norm_real] at H
exact isLittleO_irrefl (.of_forall (fun _ => one_ne_zero))
H.of_norm_right.trans_isLittleO isLittleO_id_one.mono nhdsWithin_le_nhds

/--
theorem `LFunction_ne_zero_of_re_eq_one` / 定理 `LFunction_ne_zero_of_re_eq_one`

English:
theorem LFunction_ne_zero_of_re_eq_one
  given: {s : Complex} (hs : s.re = 1) (hχs : χ != 1 ∨ s != 1)
  proof: by
  by_cases h : χ ^ 2 = 1 ∧ s = 1
· exact h.2 ▸ LFunction_apply_one_ne_zero_of_quadratic h.1 hχs.neg_resolve_right h.2
  · have hs' : s = 1 + I * s.im := by
      conv_lhs => rw [← re_add_im s, hs, ofReal_one, mul_comm]
    rw [not_and_or]; rw [← ne_eq]; rw [← ne_eq]; rw [hs']; rw [add_ne_left] at h
    replace h : χ ^ 2 != 1 ∨ s.im != 0 :=
      h.imp_right (fun H => by exact_mod_cast right_ne_zero_of_mul H)
    exact hs'.symm ▸ χ.LFunction_ne_zero_of_not_quadratic_or_ne_one h

中文:
定理 LFunction_ne_zero_of_re_eq_one
  条件: {s : 复形} (hs : s.re = 1) (hχs : χ != 1 ∨ s != 1)
  证明: by
  by_cases h : χ ^ 2 = 1 ∧ s = 1
· exact h.2 ▸ LFunction_apply_one_ne_zero_of_quadratic h.1 hχs.neg_resolve_right h.2
  · have hs' : s = 1 + I * s.im := by
      conv_lhs => rw [← re_add_im s, hs, ofReal_one, mul_comm]
    rw [not_and_or]; rw [← ne_eq]; rw [← ne_eq]; rw [hs']; rw [add_ne_left] at h
    replace h : χ ^ 2 != 1 ∨ s.im != 0 :=
      h.imp_right (fun H => by exact_mod_cast right_ne_zero_of_mul H)
    exact hs'.symm ▸ χ.LFunction_ne_zero_of_not_quadratic_or_ne_one h

Depends on / 依赖: LFunction_apply_one_ne_zero_of_quadratic, LFunction_ne_zero_of_not_quadratic_or_ne_one, add_ne_left, conv_lhs, h.imp_right, imp_right, mul_comm, ne_eq, neg_resolve_right, not_and_or, ofReal_one, re_add_im, replace, right_ne_zero_of_mul, s.im, s.neg_resolve_right
-/
theorem LFunction_ne_zero_of_re_eq_one {s : Complex} (hs : s.re = 1) (hχs : χ != 1 ∨ s != 1) :
    LFunction χ s != 0 := by
  by_cases h : χ ^ 2 = 1 ∧ s = 1
· exact h.2 ▸ LFunction_apply_one_ne_zero_of_quadratic h.1 hχs.neg_resolve_right h.2
  · have hs' : s = 1 + I * s.im := by
      conv_lhs => rw [← re_add_im s, hs, ofReal_one, mul_comm]
    rw [not_and_or]; rw [← ne_eq]; rw [← ne_eq]; rw [hs']; rw [add_ne_left] at h
    replace h : χ ^ 2 != 1 ∨ s.im != 0 :=
      h.imp_right (fun H => by exact_mod_cast right_ne_zero_of_mul H)
    exact hs'.symm ▸ χ.LFunction_ne_zero_of_not_quadratic_or_ne_one h

/--
theorem `LFunction_ne_zero_of_one_le_re` / 定理 `LFunction_ne_zero_of_one_le_re`

English:
theorem LFunction_ne_zero_of_one_le_re
  given: ⦃s
  statement: Complex⦄ (hχs : χ != 1 ∨ s != 1) (hs : 1 <= s.re) :
  proof: hs.eq_or_lt.casesOn (fun hs => LFunction_ne_zero_of_re_eq_one χ hs.symm hχs)
    fun hs => LFunction_eq_LSeries χ hs ▸ LSeries_ne_zero_of_one_lt_re χ hs

中文:
定理 LFunction_ne_zero_of_one_le_re
  条件: ⦃s
  结论: 复形⦄ (hχs : χ != 1 ∨ s != 1) (hs : 1 <= s.re) :
  证明: hs.eq_or_lt.casesOn (fun hs => LFunction_ne_zero_of_re_eq_one χ hs.symm hχs)
    fun hs => LFunction_eq_LSeries χ hs ▸ LSeries_ne_zero_of_one_lt_re χ hs

Depends on / 依赖: LFunction_eq_LSeries, LFunction_ne_zero_of_re_eq_one, LSeries_ne_zero_of_one_lt_re, casesOn, eq_or_lt, hs.eq_or_lt.casesOn, hs.symm
-/
theorem LFunction_ne_zero_of_one_le_re ⦃s : Complex⦄ (hχs : χ != 1 ∨ s != 1) (hs : 1 <= s.re) :
    LFunction χ s != 0 :=
  hs.eq_or_lt.casesOn (fun hs => LFunction_ne_zero_of_re_eq_one χ hs.symm hχs)
    fun hs => LFunction_eq_LSeries χ hs ▸ LSeries_ne_zero_of_one_lt_re χ hs

-- Interesting special case:
variable {χ} in
/--
theorem `LFunction_apply_one_ne_zero` / 定理 `LFunction_apply_one_ne_zero`

English:
theorem LFunction_apply_one_ne_zero
  given: (hχ : χ != 1)
  statement: LFunction χ 1 != 0
  proof: LFunction_ne_zero_of_one_le_re χ (.inl hχ) one_re ▸ le_rfl

中文:
定理 LFunction_apply_one_ne_zero
  条件: (hχ : χ != 1)
  结论: L函数 χ 1 != 0
  证明: LFunction_ne_zero_of_one_le_re χ (.inl hχ) one_re ▸ le_rfl

Depends on / 依赖: LFunction_ne_zero_of_one_le_re, le_rfl, one_re
-/
theorem LFunction_apply_one_ne_zero (hχ : χ != 1) : LFunction χ 1 != 0 :=
LFunction_ne_zero_of_one_le_re χ (.inl hχ) one_re ▸ le_rfl

/--
lemma `_root_.riemannZeta_ne_zero_of_one_le_re` / 引理 `_root_.riemannZeta_ne_zero_of_one_le_re`

English:
lemma _root_.riemannZeta_ne_zero_of_one_le_re
  given: ⦃s
  statement: Complex⦄ (hs : 1 <= s.re) :
  proof: by
  rcases eq_or_ne s 1 with rfl | hs₀
  · exact riemannZeta_one_ne_zero
  · exact LFunction_modOne_eq (χ := 1) ▸ LFunction_ne_zero_of_one_le_re _ (.inr hs₀) hs

中文:
引理 _root_.riemannZeta_ne_zero_of_one_le_re
  条件: ⦃s
  结论: 复形⦄ (hs : 1 <= s.re) :
  证明: by
  rcases eq_or_ne s 1 with rfl | hs₀
  · exact riemannZeta_one_ne_zero
  · exact LFunction_modOne_eq (χ := 1) ▸ LFunction_ne_zero_of_one_le_re _ (.inr hs₀) hs

Depends on / 依赖: LFunction_modOne_eq, LFunction_ne_zero_of_one_le_re, eq_or_ne, riemannZeta_one_ne_zero
-/
lemma _root_.riemannZeta_ne_zero_of_one_le_re ⦃s : Complex⦄ (hs : 1 <= s.re) :
    riemannZeta s != 0 := by
  rcases eq_or_ne s 1 with rfl | hs₀
  · exact riemannZeta_one_ne_zero
  · exact LFunction_modOne_eq (χ := 1) ▸ LFunction_ne_zero_of_one_le_re _ (.inr hs₀) hs

end nonvanishing

end DirichletCharacter
