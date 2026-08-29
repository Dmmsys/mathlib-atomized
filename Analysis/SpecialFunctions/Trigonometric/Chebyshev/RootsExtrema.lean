/-
Copyright (c) 2025 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuval Filmus
-/
module

public import Mathlib.RingTheory.Polynomial.Chebyshev
public import Mathlib.Data.Real.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.NumberTheory.Niven

/-!
# Chebyshev polynomials over the reals: roots and extrema

## Main statements

* `T_n(x) ∈ [-1, 1]` iff `x ∈ [-1, 1]`: `abs_eval_T_real_le_one_iff`
* Zeroes of `T` and `U`: `roots_T_real`, `roots_U_real`
* Local extrema of `T`: `isLocalExtr_T_real_iff`, `isExtrOn_T_real_iff`
* Irrationality of zeroes of `T` other than zero: `irrational_of_isRoot_T_real`
* `|T_n^{(k)} (x)| ≤ T_n^{(k)} (1)` for `x ∈ [-1, 1]`: `abs_iterate_derivative_T_real_le`

## TODO

Show that the bound on `T_n^{(k)} (x)` is achieved only at `x = ±1`
-/

public section

namespace Polynomial.Chebyshev

open Real

/--
theorem `eval_T_real_mem_Icc` / 定理 `eval_T_real_mem_Icc`

English:
theorem eval_T_real_mem_Icc
  given: (n : Int) {x : Real} (hx : x in Set.Icc (-1) 1)
  proof: by
  rw [← cos_arccos (x := x) (by grind) (by grind)]
  grind [T_real_cos, cos_mem_Icc]

中文:
定理 eval_T_real_mem_Icc
  条件: (n : 整数) {x : 实数} (hx : x in Set.Icc (-1) 1)
  证明: by
  rw [← cos_arccos (x := x) (by grind) (by grind)]
  grind [T_real_cos, cos_mem_Icc]

Depends on / 依赖: T_real_cos, cos_arccos, cos_mem_Icc
-/
theorem eval_T_real_mem_Icc (n : Int) {x : Real} (hx : x in Set.Icc (-1) 1) :
    (T Real n).eval x in Set.Icc (-1) 1 := by
  rw [← cos_arccos (x := x) (by grind) (by grind)]
  grind [T_real_cos, cos_mem_Icc]

/--
theorem `abs_eval_T_real_le_one` / 定理 `abs_eval_T_real_le_one`

English:
theorem abs_eval_T_real_le_one
  given: (n : Int) {x : Real} (hx : |x| <= 1)
  proof: by
  #adaptation_note /-- Before nightly-2026-04-07, this was just
  `grind [eval_T_real_mem_Icc]`. `grind`'s e-matching now keeps the
  `Polynomial.eval` produced by the lemma (which uses `instCommSemiring.toSemiring`)
  and the `Polynomial.eval` propagated by abs unfolding (which uses `Real.semiri

中文:
定理 abs_eval_T_real_le_one
  条件: (n : 整数) {x : 实数} (hx : |x| <= 1)
  证明: by
  #adaptation_note /-- Before nightly-2026-04-07, this was just
  `grind [eval_T_real_mem_Icc]`. `grind`'s e-matching now keeps the
  `Polynomial.eval` produced by the lemma (which uses `instCommSemiring.toSemiring`)
  and the `Polynomial.eval` propagated by abs unfolding (which uses `Real.semiri

Depends on / 依赖: Before, Polynomial, Polynomial.eval, Real.semiring, Set.mem_Icc.mp, Set.mem_Icc.mpr, abs_le, abs_le.mp, abs_le.mpr, adaptation_note, distinct, eval_T_real_mem_Icc, instCommSemiring, instCommSemiring.toSemiring, matching, mem_Icc, nightly, produced, propagated, semiring
-/
theorem abs_eval_T_real_le_one (n : Int) {x : Real} (hx : |x| <= 1) :
    |(T Real n).eval x| <= 1 := by
  #adaptation_note /-- Before nightly-2026-04-07, this was just
  `grind [eval_T_real_mem_Icc]`. `grind`'s e-matching now keeps the
  `Polynomial.eval` produced by the lemma (which uses `instCommSemiring.toSemiring`)
  and the `Polynomial.eval` propagated by abs unfolding (which uses `Real.semiring`)
  as distinct atoms, even though they are `rfl`-equal, so the contradiction is
  never found. -/
  have h := eval_T_real_mem_Icc n (Set.mem_Icc.mpr (abs_le.mp hx))
  exact abs_le.mpr (Set.mem_Icc.mp h)

/--
theorem `one_le_eval_T_real` / 定理 `one_le_eval_T_real`

English:
theorem one_le_eval_T_real
  given: (n : Int) {x : Real} (hx : 1 <= x)
  statement: 1 <= (T Real n).eval x
  proof: by
  rw [← cosh_arcosh hx]
  grind [T_real_cosh, one_le_cosh]

中文:
定理 one_le_eval_T_real
  条件: (n : 整数) {x : 实数} (hx : 1 <= x)
  结论: 1 <= (T 实数 n).eval x
  证明: by
  rw [← cosh_arcosh hx]
  grind [T_real_cosh, one_le_cosh]

Depends on / 依赖: T_real_cosh, cosh_arcosh, one_le_cosh
-/
theorem one_le_eval_T_real (n : Int) {x : Real} (hx : 1 <= x) : 1 <= (T Real n).eval x := by
  rw [← cosh_arcosh hx]
  grind [T_real_cosh, one_le_cosh]

/--
theorem `one_lt_eval_T_real` / 定理 `one_lt_eval_T_real`

English:
theorem one_lt_eval_T_real
  given: {n : Int} (hn : n != 0) {x : Real} (hx : 1 < x)
  proof: by
  have : arcosh x != 0 := by grind [cosh_arcosh, cosh_zero]
  rw [← cosh_arcosh (le_of_lt hx)]; rw [T_real_cosh]; rw [one_lt_cosh]; rw [mul_ne_zero_iff]
  exact ⟨by norm_cast, by assumption⟩

中文:
定理 one_lt_eval_T_real
  条件: {n : 整数} (hn : n != 0) {x : 实数} (hx : 1 < x)
  证明: by
  have : arcosh x != 0 := by grind [cosh_arcosh, cosh_zero]
  rw [← cosh_arcosh (le_of_lt hx)]; rw [T_real_cosh]; rw [one_lt_cosh]; rw [mul_ne_zero_iff]
  exact ⟨by norm_cast, by assumption⟩

Depends on / 依赖: T_real_cosh, arcosh, cosh_arcosh, cosh_zero, le_of_lt, mul_ne_zero_iff, one_lt_cosh
-/
theorem one_lt_eval_T_real {n : Int} (hn : n != 0) {x : Real} (hx : 1 < x) :
    1 < (T Real n).eval x := by
  have : arcosh x != 0 := by grind [cosh_arcosh, cosh_zero]
  rw [← cosh_arcosh (le_of_lt hx)]; rw [T_real_cosh]; rw [one_lt_cosh]; rw [mul_ne_zero_iff]
  exact ⟨by norm_cast, by assumption⟩

/--
theorem `one_le_negOnePow_mul_eval_T_real` / 定理 `one_le_negOnePow_mul_eval_T_real`

English:
theorem one_le_negOnePow_mul_eval_T_real
  given: (n : Int) {x : Real} (hx : x <= -1)
  proof: by
  rw [← neg_neg x]; rw [T_eval_neg]
  convert! one_le_eval_T_real n (le_neg_of_le_neg hx)
  rw [Int.cast_negOnePow]; rw [← mul_assoc]; rw [← mul_zpow]
  simp

中文:
定理 one_le_negOnePow_mul_eval_T_real
  条件: (n : 整数) {x : 实数} (hx : x <= -1)
  证明: by
  rw [← neg_neg x]; rw [T_eval_neg]
  convert! one_le_eval_T_real n (le_neg_of_le_neg hx)
  rw [Int.cast_negOnePow]; rw [← mul_assoc]; rw [← mul_zpow]
  simp

Depends on / 依赖: Int.cast_negOnePow, T_eval_neg, cast_negOnePow, convert, le_neg_of_le_neg, mul_assoc, mul_zpow, neg_neg, one_le_eval_T_real
-/
theorem one_le_negOnePow_mul_eval_T_real (n : Int) {x : Real} (hx : x <= -1) :
    1 <= n.negOnePow * (T Real n).eval x := by
  rw [← neg_neg x]; rw [T_eval_neg]
  convert! one_le_eval_T_real n (le_neg_of_le_neg hx)
  rw [Int.cast_negOnePow]; rw [← mul_assoc]; rw [← mul_zpow]
  simp

/--
theorem `one_lt_negOnePow_mul_eval_T_real` / 定理 `one_lt_negOnePow_mul_eval_T_real`

English:
theorem one_lt_negOnePow_mul_eval_T_real
  given: {n : Int} (hn : n != 0) {x : Real} (hx : x < -1)
  proof: by
  rw [← neg_neg x]; rw [T_eval_neg]
  convert! one_lt_eval_T_real hn (lt_neg_of_lt_neg hx)
  rw [Int.cast_negOnePow]; rw [← mul_assoc]; rw [← mul_zpow]
  simp

中文:
定理 one_lt_negOnePow_mul_eval_T_real
  条件: {n : 整数} (hn : n != 0) {x : 实数} (hx : x < -1)
  证明: by
  rw [← neg_neg x]; rw [T_eval_neg]
  convert! one_lt_eval_T_real hn (lt_neg_of_lt_neg hx)
  rw [Int.cast_negOnePow]; rw [← mul_assoc]; rw [← mul_zpow]
  simp

Depends on / 依赖: Int.cast_negOnePow, T_eval_neg, cast_negOnePow, convert, lt_neg_of_lt_neg, mul_assoc, mul_zpow, neg_neg, one_lt_eval_T_real
-/
theorem one_lt_negOnePow_mul_eval_T_real {n : Int} (hn : n != 0) {x : Real} (hx : x < -1) :
    1 < n.negOnePow * (T Real n).eval x := by
  rw [← neg_neg x]; rw [T_eval_neg]
  convert! one_lt_eval_T_real hn (lt_neg_of_lt_neg hx)
  rw [Int.cast_negOnePow]; rw [← mul_assoc]; rw [← mul_zpow]
  simp

/--
theorem `one_le_abs_eval_T_real` / 定理 `one_le_abs_eval_T_real`

English:
theorem one_le_abs_eval_T_real
  given: (n : Int) {x : Real} (hx : 1 <= |x|)
  proof: by
  wlog! h : 0 <= x
  · simpa [T_eval_neg, abs_mul, abs_unit_intCast] using @this n (-x) (by grind) (by grind)
.trans le_abs_self _ · exact one_le_eval_T_real n (abs_of_nonneg h ▸ hx)

中文:
定理 one_le_abs_eval_T_real
  条件: (n : 整数) {x : 实数} (hx : 1 <= |x|)
  证明: by
  wlog! h : 0 <= x
  · simpa [T_eval_neg, abs_mul, abs_unit_intCast] using @this n (-x) (by grind) (by grind)
.trans le_abs_self _ · exact one_le_eval_T_real n (abs_of_nonneg h ▸ hx)

Depends on / 依赖: T_eval_neg, abs_mul, abs_of_nonneg, abs_unit_intCast, le_abs_self, one_le_eval_T_real
-/
theorem one_le_abs_eval_T_real (n : Int) {x : Real} (hx : 1 <= |x|) :
    1 <= |(T Real n).eval x| := by
  wlog! h : 0 <= x
  · simpa [T_eval_neg, abs_mul, abs_unit_intCast] using @this n (-x) (by grind) (by grind)
.trans le_abs_self _ · exact one_le_eval_T_real n (abs_of_nonneg h ▸ hx)

/--
theorem `one_lt_abs_eval_T_real` / 定理 `one_lt_abs_eval_T_real`

English:
theorem one_lt_abs_eval_T_real
  given: {n : Int} (hn : n != 0) {x : Real} (hx : 1 < |x|)
  proof: by
  wlog! h : 0 <= x
  · simpa [T_eval_neg, abs_mul, abs_unit_intCast] using @this n hn (-x) (by grind) (by grind)
.trans_le le_abs_self _ · exact one_lt_eval_T_real hn (abs_of_nonneg h ▸ hx)

中文:
定理 one_lt_abs_eval_T_real
  条件: {n : 整数} (hn : n != 0) {x : 实数} (hx : 1 < |x|)
  证明: by
  wlog! h : 0 <= x
  · simpa [T_eval_neg, abs_mul, abs_unit_intCast] using @this n hn (-x) (by grind) (by grind)
.trans_le le_abs_self _ · exact one_lt_eval_T_real hn (abs_of_nonneg h ▸ hx)

Depends on / 依赖: T_eval_neg, abs_mul, abs_of_nonneg, abs_unit_intCast, le_abs_self, one_lt_eval_T_real, trans_le
-/
theorem one_lt_abs_eval_T_real {n : Int} (hn : n != 0) {x : Real} (hx : 1 < |x|) :
    1 < |(T Real n).eval x| := by
  wlog! h : 0 <= x
  · simpa [T_eval_neg, abs_mul, abs_unit_intCast] using @this n hn (-x) (by grind) (by grind)
.trans_le le_abs_self _ · exact one_lt_eval_T_real hn (abs_of_nonneg h ▸ hx)

/--
theorem `abs_eval_T_real_le_one_iff` / 定理 `abs_eval_T_real_le_one_iff`

English:
theorem abs_eval_T_real_le_one_iff
  given: {n : Int} (hn : n != 0) (x : Real)
  proof: ⟨abs_eval_T_real_le_one n, by simpa using mt one_lt_abs_eval_T_real hn⟩

中文:
定理 abs_eval_T_real_le_one_iff
  条件: {n : 整数} (hn : n != 0) (x : 实数)
  证明: ⟨abs_eval_T_real_le_one n, by simpa using mt one_lt_abs_eval_T_real hn⟩

Depends on / 依赖: abs_eval_T_real_le_one, one_lt_abs_eval_T_real
-/
theorem abs_eval_T_real_le_one_iff {n : Int} (hn : n != 0) (x : Real) :
    |x| <= 1 ↔ |(T Real n).eval x| <= 1 :=
⟨abs_eval_T_real_le_one n, by simpa using mt one_lt_abs_eval_T_real hn⟩

/--
theorem `abs_eval_T_real_eq_one_iff` / 定理 `abs_eval_T_real_eq_one_iff`

English:
theorem abs_eval_T_real_eq_one_iff
  given: {n : Nat} (hn : n != 0) (x : Real)
  proof: by
  constructor
  · intro hTx
    have hx := (abs_eval_T_real_le_one_iff (Nat.cast_ne_zero.mpr hn) x).mpr (le_of_eq hTx)
    rw [← cos_arccos (neg_le_of_abs_le hx) (le_of_max_le_left hx)]; rw [T_real_cos]; rw [Int.cast_natCast]; rw [abs_cos_eq_one_iff] at hTx
    obtain ⟨k, hk⟩ := hTx
    have hk' 

中文:
定理 abs_eval_T_real_eq_one_iff
  条件: {n : 自然数} (hn : n != 0) (x : 实数)
  证明: by
  constructor
  · intro hTx
    have hx := (abs_eval_T_real_le_one_iff (Nat.cast_ne_zero.mpr hn) x).mpr (le_of_eq hTx)
    rw [← cos_arccos (neg_le_of_abs_le hx) (le_of_max_le_left hx)]; rw [T_real_cos]; rw [Int.cast_natCast]; rw [abs_cos_eq_one_iff] at hTx
    obtain ⟨k, hk⟩ := hTx
    have hk' 

Depends on / 依赖: Int.cast_natCast, Int.cast_nonneg_iff, Nat.cast_ne_zero.mpr, T_real_cos, abs_cos_eq_one_iff, abs_eval_T_real_le_one_iff, arccos, arccos_nonneg, cast_natCast, cast_ne_zero, cast_nonneg_iff, cos_arccos, le_of_eq, le_of_max_le_left, neg_le_of_abs_le
-/
theorem abs_eval_T_real_eq_one_iff {n : Nat} (hn : n != 0) (x : Real) :
    |(T Real n).eval x| = 1 ↔ exists k <= n, x = cos (k * π / n) := by
  constructor
  · intro hTx
    have hx := (abs_eval_T_real_le_one_iff (Nat.cast_ne_zero.mpr hn) x).mpr (le_of_eq hTx)
    rw [← cos_arccos (neg_le_of_abs_le hx) (le_of_max_le_left hx)]; rw [T_real_cos]; rw [Int.cast_natCast]; rw [abs_cos_eq_one_iff] at hTx
    obtain ⟨k, hk⟩ := hTx
    have hk' : k = n * (arccos x / π) := by simpa [field]
    lift k to Nat using (by rw [← Int.cast_nonneg_iff (R := Real), hk']; positivity [arccos_nonneg x])
    simp only [Int.cast_natCast] at hk hk'
    have hkn : (k : Real) <= n := by
      rw [← mul_one (n : Real)]; rw [hk']
      gcongr
      exact div_le_one_of_le₀ (arccos_le_pi x) (by positivity)
    refine ⟨k, by simpa using hkn, ?_⟩
    convert! congr(cos ($hk.symm / n))
    rw [mul_div_cancel_left₀ _ (by simpa)]; rw [cos_arccos (by grind) (by grind)]
  · rintro ⟨k, hk, rfl⟩
    rw [T_real_cos]; rw [abs_cos_eq_one_iff]
    exact ⟨k, by simp [field]⟩

/--
theorem `eval_T_real_cos_int_mul_pi_div` / 定理 `eval_T_real_cos_int_mul_pi_div`

English:
theorem eval_T_real_cos_int_mul_pi_div
  given: {k : Nat} {n : Nat} (hn : n != 0)
  proof: by
  rw [T_real_cos]; rw [Int.cast_negOnePow]
  convert! Real.cos_int_mul_pi k using 2
  simp [field]

中文:
定理 eval_T_real_cos_int_mul_pi_div
  条件: {k : 自然数} {n : 自然数} (hn : n != 0)
  证明: by
  rw [T_real_cos]; rw [Int.cast_negOnePow]
  convert! Real.cos_int_mul_pi k using 2
  simp [field]

Depends on / 依赖: Int.cast_negOnePow, Real.cos_int_mul_pi, T_real_cos, cast_negOnePow, convert, cos_int_mul_pi
-/
theorem eval_T_real_cos_int_mul_pi_div {k : Nat} {n : Nat} (hn : n != 0) :
    (T Real n).eval (cos (k * π / n)) = (k : Int).negOnePow := by
  rw [T_real_cos]; rw [Int.cast_negOnePow]
  convert! Real.cos_int_mul_pi k using 2
  simp [field]

/--
theorem `eval_T_real_eq_one_iff` / 定理 `eval_T_real_eq_one_iff`

English:
theorem eval_T_real_eq_one_iff
  given: {n : Nat} (hn : n != 0) (x : Real)
  proof: by
  constructor
  · intro hx
    obtain ⟨k, hk₁, hk₂⟩ := (abs_eval_T_real_eq_one_iff hn x).mp
      ((abs_eq_abs.mpr (.inl hx)).trans abs_one)
    use k
    refine ⟨hk₁, ?_, hk₂⟩
    rw [hk₂]; rw [eval_T_real_cos_int_mul_pi_div hn]; rw [Int.cast_negOnePow_natCast] at hx
    exact (neg_one_pow_eq_on

中文:
定理 eval_T_real_eq_one_iff
  条件: {n : 自然数} (hn : n != 0) (x : 实数)
  证明: by
  constructor
  · intro hx
    obtain ⟨k, hk₁, hk₂⟩ := (abs_eval_T_real_eq_one_iff hn x).mp
      ((abs_eq_abs.mpr (.inl hx)).trans abs_one)
    use k
    refine ⟨hk₁, ?_, hk₂⟩
    rw [hk₂]; rw [eval_T_real_cos_int_mul_pi_div hn]; rw [Int.cast_negOnePow_natCast] at hx
    exact (neg_one_pow_eq_on

Depends on / 依赖: Int.cast_negOnePow_natCast, Int.even_coe_nat, Int.negOnePow_even, abs_eq_abs, abs_eq_abs.mpr, abs_eval_T_real_eq_one_iff, abs_one, cast_negOnePow_natCast, eval_T_real_cos_int_mul_pi_div, even_coe_nat, negOnePow_even, neg_one_pow_eq_one_iff_even
-/
theorem eval_T_real_eq_one_iff {n : Nat} (hn : n != 0) (x : Real) :
    (T Real n).eval x = 1 ↔ exists k <= n, Even k ∧ x = cos (k * π / n) := by
  constructor
  · intro hx
    obtain ⟨k, hk₁, hk₂⟩ := (abs_eval_T_real_eq_one_iff hn x).mp
      ((abs_eq_abs.mpr (.inl hx)).trans abs_one)
    use k
    refine ⟨hk₁, ?_, hk₂⟩
    rw [hk₂]; rw [eval_T_real_cos_int_mul_pi_div hn]; rw [Int.cast_negOnePow_natCast] at hx
    exact (neg_one_pow_eq_one_iff_even (by grind)).mp hx
  · rintro ⟨k, hk₁, hk₂, hx⟩
    rw [hx]; rw [eval_T_real_cos_int_mul_pi_div hn]; rw [Int.negOnePow_even k ((Int.even_coe_nat k).mpr hk₂)]
    norm_cast

/--
theorem `eval_T_real_eq_neg_one_iff` / 定理 `eval_T_real_eq_neg_one_iff`

English:
theorem eval_T_real_eq_neg_one_iff
  given: {n : Nat} (hn : n != 0) (x : Real)
  proof: by
  constructor
  · intro hx
    obtain ⟨k, hk₁, hk₂⟩ := (abs_eval_T_real_eq_one_iff hn x).mp
      ((abs_eq_abs.mpr (.inl hx)).trans ((abs_neg 1).trans abs_one))
    use k
    refine ⟨hk₁, ?_, hk₂⟩
    rw [hk₂]; rw [eval_T_real_cos_int_mul_pi_div hn]; rw [Int.cast_negOnePow_natCast] at hx
    exac

中文:
定理 eval_T_real_eq_neg_one_iff
  条件: {n : 自然数} (hn : n != 0) (x : 实数)
  证明: by
  constructor
  · intro hx
    obtain ⟨k, hk₁, hk₂⟩ := (abs_eval_T_real_eq_one_iff hn x).mp
      ((abs_eq_abs.mpr (.inl hx)).trans ((abs_neg 1).trans abs_one))
    use k
    refine ⟨hk₁, ?_, hk₂⟩
    rw [hk₂]; rw [eval_T_real_cos_int_mul_pi_div hn]; rw [Int.cast_negOnePow_natCast] at hx
    exac

Depends on / 依赖: Int.cast_negOnePow_natCast, Int.negOnePow_odd, Int.odd_coe_nat, abs_eq_abs, abs_eq_abs.mpr, abs_eval_T_real_eq_one_iff, abs_neg, abs_one, cast_negOnePow_natCast, eval_T_real_cos_int_mul_pi_div, negOnePow_odd, neg_one_pow_eq_neg_one_iff_odd, odd_coe_nat
-/
theorem eval_T_real_eq_neg_one_iff {n : Nat} (hn : n != 0) (x : Real) :
    (T Real n).eval x = -1 ↔ exists k <= n, Odd k ∧ x = cos (k * π / n) := by
  constructor
  · intro hx
    obtain ⟨k, hk₁, hk₂⟩ := (abs_eval_T_real_eq_one_iff hn x).mp
      ((abs_eq_abs.mpr (.inl hx)).trans ((abs_neg 1).trans abs_one))
    use k
    refine ⟨hk₁, ?_, hk₂⟩
    rw [hk₂]; rw [eval_T_real_cos_int_mul_pi_div hn]; rw [Int.cast_negOnePow_natCast] at hx
    exact (neg_one_pow_eq_neg_one_iff_odd (by grind)).mp hx
  · rintro ⟨k, hk₁, hk₂, hx⟩
    rw [hx]; rw [eval_T_real_cos_int_mul_pi_div hn]; rw [Int.negOnePow_odd k ((Int.odd_coe_nat k).mpr hk₂)]
    norm_cast

/--
theorem `roots_T_real_nodup` / 定理 `roots_T_real_nodup`

English:
theorem roots_T_real_nodup
  given: (n : Nat)
  proof: by
  wlog! hn : n != 0
  · simp [hn]
  refine (Finset.range n).nodup_map_iff_injOn.mpr ?_
  refine injOn_cos.comp (by aesop) fun k hk => Set.mem_Icc.mpr ⟨by positivity, ?_⟩
  field_simp
  norm_cast
  grind

中文:
定理 roots_T_real_nodup
  条件: (n : 自然数)
  证明: by
  wlog! hn : n != 0
  · simp [hn]
  refine (Finset.range n).nodup_map_iff_injOn.mpr ?_
  refine injOn_cos.comp (by aesop) fun k hk => Set.mem_Icc.mpr ⟨by positivity, ?_⟩
  field_simp
  norm_cast
  grind

Depends on / 依赖: Finset, Finset.range, Set.mem_Icc.mpr, injOn_cos, injOn_cos.comp, mem_Icc, nodup_map_iff_injOn, nodup_map_iff_injOn.mpr
-/
theorem roots_T_real_nodup (n : Nat) :
    (Multiset.map (fun k : Nat => cos ((2 * k + 1) * π / (2 * n))) (.range n)).Nodup := by
  wlog! hn : n != 0
  · simp [hn]
  refine (Finset.range n).nodup_map_iff_injOn.mpr ?_
  refine injOn_cos.comp (by aesop) fun k hk => Set.mem_Icc.mpr ⟨by positivity, ?_⟩
  field_simp
  norm_cast
  grind

/--
theorem `roots_T_real` / 定理 `roots_T_real`

English:
theorem roots_T_real
  given: (n : Nat)
  proof: by
  wlog! hn : n != 0
  · simp [hn]
  refine roots_eq_of_degree_eq_card (fun x hx => ?_) ?_
  · obtain ⟨k, hk, hx⟩ := Finset.mem_image.mp hx
    rw [← hx]; rw [T_real_cos]; rw [cos_eq_zero_iff]
    use k
    field_simp
    norm_cast
  · rw [Finset.card_image_of_injOn, Finset.card_range, degree_T, I

中文:
定理 roots_T_real
  条件: (n : 自然数)
  证明: by
  wlog! hn : n != 0
  · simp [hn]
  refine roots_eq_of_degree_eq_card (fun x hx => ?_) ?_
  · obtain ⟨k, hk, hx⟩ := Finset.mem_image.mp hx
    rw [← hx]; rw [T_real_cos]; rw [cos_eq_zero_iff]
    use k
    field_simp
    norm_cast
  · rw [Finset.card_image_of_injOn, Finset.card_range, degree_T, I

Depends on / 依赖: Finset, Finset.card_image_of_injOn, Finset.card_range, Finset.mem_image.mp, Finset.range, Int.natAbs_natCast, T_real_cos, card_image_of_injOn, card_range, cos_eq_zero_iff, degree_T, mem_image, natAbs_natCast, nodup_map_iff_injOn, nodup_map_iff_injOn.mp, roots_T_real_nodup, roots_eq_of_degree_eq_card
-/
theorem roots_T_real (n : Nat) :
    (T Real n).roots =
    ((Finset.range n).image (fun (k : Nat) => cos ((2 * k + 1) * π / (2 * n)))).val := by
  wlog! hn : n != 0
  · simp [hn]
  refine roots_eq_of_degree_eq_card (fun x hx => ?_) ?_
  · obtain ⟨k, hk, hx⟩ := Finset.mem_image.mp hx
    rw [← hx]; rw [T_real_cos]; rw [cos_eq_zero_iff]
    use k
    field_simp
    norm_cast
  · rw [Finset.card_image_of_injOn, Finset.card_range, degree_T, Int.natAbs_natCast]
    exact (Finset.range n).nodup_map_iff_injOn.mp (roots_T_real_nodup n)

/--
theorem `rootMultiplicity_T_real` / 定理 `rootMultiplicity_T_real`

English:
theorem rootMultiplicity_T_real
  given: {n k : Nat} (hk : k < n)
  proof: by
  rw [← count_roots]; rw [roots_T_real]; rw [Multiset.count_eq_one_of_mem (by simp)]
  grind

中文:
定理 rootMultiplicity_T_real
  条件: {n k : 自然数} (hk : k < n)
  证明: by
  rw [← count_roots]; rw [roots_T_real]; rw [Multiset.count_eq_one_of_mem (by simp)]
  grind

Depends on / 依赖: Multiset, Multiset.count_eq_one_of_mem, count_eq_one_of_mem, count_roots, roots_T_real
-/
theorem rootMultiplicity_T_real {n k : Nat} (hk : k < n) :
    (T Real n).rootMultiplicity (cos ((2 * k + 1) * π / (2 * n))) = 1 := by
  rw [← count_roots]; rw [roots_T_real]; rw [Multiset.count_eq_one_of_mem (by simp)]
  grind

/--
theorem `roots_U_real_nodup` / 定理 `roots_U_real_nodup`

English:
theorem roots_U_real_nodup
  given: (n : Nat)
  proof: by
  refine (Finset.range n).nodup_map_iff_injOn.mpr ?_
  apply injOn_cos.comp
  · intro x hx y hy hxy
    field_simp at hxy
    aesop
  · refine fun k hk => Set.mem_Icc.mpr ⟨by positivity, ?_⟩
    field_simp
    norm_cast
    grind

中文:
定理 roots_U_real_nodup
  条件: (n : 自然数)
  证明: by
  refine (Finset.range n).nodup_map_iff_injOn.mpr ?_
  apply injOn_cos.comp
  · intro x hx y hy hxy
    field_simp at hxy
    aesop
  · refine fun k hk => Set.mem_Icc.mpr ⟨by positivity, ?_⟩
    field_simp
    norm_cast
    grind

Depends on / 依赖: Finset, Finset.range, Set.mem_Icc.mpr, injOn_cos, injOn_cos.comp, mem_Icc, nodup_map_iff_injOn, nodup_map_iff_injOn.mpr
-/
theorem roots_U_real_nodup (n : Nat) :
    (Multiset.map (fun k : Nat => cos ((k + 1) * π / (n + 1))) (.range n)).Nodup := by
  refine (Finset.range n).nodup_map_iff_injOn.mpr ?_
  apply injOn_cos.comp
  · intro x hx y hy hxy
    field_simp at hxy
    aesop
  · refine fun k hk => Set.mem_Icc.mpr ⟨by positivity, ?_⟩
    field_simp
    norm_cast
    grind

/--
theorem `roots_U_real` / 定理 `roots_U_real`

English:
theorem roots_U_real
  given: (n : Nat)
  proof: by
  wlog! hn : n != 0
  · simp [hn]
  refine roots_eq_of_degree_eq_card (fun x hx => ?_) ?_
  · obtain ⟨k, hk, hx⟩ := Finset.mem_image.mp hx
    suffices (U Real n).eval x * sin ((k + 1) * π / (n + 1)) = 0 by
      refine (mul_eq_zero_iff_right (ne_of_gt (sin_pos_of_pos_of_lt_pi (by positivity) ?_)

中文:
定理 roots_U_real
  条件: (n : 自然数)
  证明: by
  wlog! hn : n != 0
  · simp [hn]
  refine roots_eq_of_degree_eq_card (fun x hx => ?_) ?_
  · obtain ⟨k, hk, hx⟩ := Finset.mem_image.mp hx
    suffices (U Real n).eval x * sin ((k + 1) * π / (n + 1)) = 0 by
      refine (mul_eq_zero_iff_right (ne_of_gt (sin_pos_of_pos_of_lt_pi (by positivity) ?_)

Depends on / 依赖: Finset, Finset.card_image_of_injOn, Finset.card_range, Finset.mem_image.mp, Finset.range, U_real_cos, card_image_of_injOn, card_range, degree_U_natCast, mem_image, mul_eq_zero_iff_right, ne_of_gt, roots_eq_of_degree_eq_card, sin_eq_zero_iff, sin_pos_of_pos_of_lt_pi
-/
theorem roots_U_real (n : Nat) :
    (U Real n).roots =
    ((Finset.range n).image (fun (k : Nat) => cos ((k + 1) * π / (n + 1)))).val := by
  wlog! hn : n != 0
  · simp [hn]
  refine roots_eq_of_degree_eq_card (fun x hx => ?_) ?_
  · obtain ⟨k, hk, hx⟩ := Finset.mem_image.mp hx
    suffices (U Real n).eval x * sin ((k + 1) * π / (n + 1)) = 0 by
      refine (mul_eq_zero_iff_right (ne_of_gt (sin_pos_of_pos_of_lt_pi (by positivity) ?_))).mp this
      field_simp
      norm_cast
      grind
    rw [← hx]; rw [U_real_cos]; rw [sin_eq_zero_iff]
    use k + 1
    field_simp
    norm_cast
    ring
  · rw [Finset.card_image_of_injOn, Finset.card_range, degree_U_natCast]
    exact (Finset.range n).nodup_map_iff_injOn.mp (roots_U_real_nodup n)

/--
theorem `rootMultiplicity_U_real` / 定理 `rootMultiplicity_U_real`

English:
theorem rootMultiplicity_U_real
  given: {n k : Nat} (hk : k < n)
  proof: by
  rw [← count_roots]; rw [roots_U_real]; rw [Multiset.count_eq_one_of_mem (by simp)]
  grind

中文:
定理 rootMultiplicity_U_real
  条件: {n k : 自然数} (hk : k < n)
  证明: by
  rw [← count_roots]; rw [roots_U_real]; rw [Multiset.count_eq_one_of_mem (by simp)]
  grind

Depends on / 依赖: Multiset, Multiset.count_eq_one_of_mem, count_eq_one_of_mem, count_roots, roots_U_real
-/
theorem rootMultiplicity_U_real {n k : Nat} (hk : k < n) :
    (U Real n).rootMultiplicity (cos ((k + 1) * π / (n + 1))) = 1 := by
  rw [← count_roots]; rw [roots_U_real]; rw [Multiset.count_eq_one_of_mem (by simp)]
  grind

/--
theorem `isLocalMax_T_real` / 定理 `isLocalMax_T_real`

English:
theorem isLocalMax_T_real
  given: {n k : Nat} (hn : n != 0) (hk₀ : 0 < k) (hk₁ : k < n) (hk₂ : Even k)
  proof: by
  have zero_lt : 0 < k * π / n := by positivity
  have lt_pi : k * π / n < π := calc
    k * π / n < n * π / n := by gcongr
    _ = π := mul_div_cancel_left₀ _ (Nat.cast_ne_zero.mpr hn)
  refine eventually_nhds_iff.mpr ⟨Set.Ioo (-1) 1, ?_, isOpen_Ioo, ?_, ?_⟩
  · intro x hx
    dsimp
    rw [(eva

中文:
定理 isLocalMax_T_real
  条件: {n k : 自然数} (hn : n != 0) (hk₀ : 0 < k) (hk₁ : k < n) (hk₂ : Even k)
  证明: by
  have zero_lt : 0 < k * π / n := by positivity
  have lt_pi : k * π / n < π := calc
    k * π / n < n * π / n := by gcongr
    _ = π := mul_div_cancel_left₀ _ (Nat.cast_ne_zero.mpr hn)
  refine eventually_nhds_iff.mpr ⟨Set.Ioo (-1) 1, ?_, isOpen_Ioo, ?_, ?_⟩
  · intro x hx
    dsimp
    rw [(eva

Depends on / 依赖: Nat.cast_ne_zero.mpr, Set.Ioo, abs_eval_T_real_le_one, abs_le, abs_le.mp, cast_ne_zero, cos_lt_cos_of_nonneg_of_le_pi, cos_pi, eval_T_real_eq_one_iff, eventually_nhds_iff, eventually_nhds_iff.mpr, isOpen_Ioo, le_of_lt, le_refl, lt_pi, zero_lt
-/
theorem isLocalMax_T_real {n k : Nat} (hn : n != 0) (hk₀ : 0 < k) (hk₁ : k < n) (hk₂ : Even k) :
    IsLocalMax (T Real n).eval (cos (k * π / n)) := by
  have zero_lt : 0 < k * π / n := by positivity
  have lt_pi : k * π / n < π := calc
    k * π / n < n * π / n := by gcongr
    _ = π := mul_div_cancel_left₀ _ (Nat.cast_ne_zero.mpr hn)
  refine eventually_nhds_iff.mpr ⟨Set.Ioo (-1) 1, ?_, isOpen_Ioo, ?_, ?_⟩
  · intro x hx
    dsimp
    rw [(eval_T_real_eq_one_iff hn _).mpr ⟨k]; rw [le_of_lt hk₁]; rw [hk₂]; rw [rfl⟩]
    exact (abs_le.mp (abs_eval_T_real_le_one n (by grind))).2
  · rw [← cos_pi]
    exact cos_lt_cos_of_nonneg_of_le_pi (le_of_lt zero_lt) (le_refl π) lt_pi
  · rw [← cos_zero]
    exact cos_lt_cos_of_nonneg_of_le_pi (le_refl 0) (le_of_lt lt_pi) zero_lt

/--
theorem `isLocalMin_T_real` / 定理 `isLocalMin_T_real`

English:
theorem isLocalMin_T_real
  given: {n k : Nat} (hn : n != 0) (hk₁ : k < n) (hk₂ : Odd k)
  proof: by
  have k_pos : 0 < k := hk₂.pos
  have zero_lt : 0 < k * π / n := by positivity
  have lt_pi : k * π / n < π := calc
    k * π / n < n * π / n := by gcongr
    _ = π := mul_div_cancel_left₀ _ (Nat.cast_ne_zero.mpr hn)
  refine eventually_nhds_iff.mpr ⟨Set.Ioo (-1) 1, ?_, isOpen_Ioo, ?_, ?_⟩
  · i

中文:
定理 isLocalMin_T_real
  条件: {n k : 自然数} (hn : n != 0) (hk₁ : k < n) (hk₂ : Odd k)
  证明: by
  have k_pos : 0 < k := hk₂.pos
  have zero_lt : 0 < k * π / n := by positivity
  have lt_pi : k * π / n < π := calc
    k * π / n < n * π / n := by gcongr
    _ = π := mul_div_cancel_left₀ _ (Nat.cast_ne_zero.mpr hn)
  refine eventually_nhds_iff.mpr ⟨Set.Ioo (-1) 1, ?_, isOpen_Ioo, ?_, ?_⟩
  · i

Depends on / 依赖: Nat.cast_ne_zero.mpr, Set.Ioo, abs_eval_T_real_le_one, abs_le, abs_le.mp, cast_ne_zero, cos_lt_cos_of_nonneg_of_le_pi, cos_pi, eval_T_real_eq_neg_one_iff, eventually_nhds_iff, eventually_nhds_iff.mpr, isOpen_Ioo, k_pos, le_o, le_of_lt, lt_pi, zero_lt
-/
theorem isLocalMin_T_real {n k : Nat} (hn : n != 0) (hk₁ : k < n) (hk₂ : Odd k) :
    IsLocalMin (T Real n).eval (cos (k * π / n)) := by
  have k_pos : 0 < k := hk₂.pos
  have zero_lt : 0 < k * π / n := by positivity
  have lt_pi : k * π / n < π := calc
    k * π / n < n * π / n := by gcongr
    _ = π := mul_div_cancel_left₀ _ (Nat.cast_ne_zero.mpr hn)
  refine eventually_nhds_iff.mpr ⟨Set.Ioo (-1) 1, ?_, isOpen_Ioo, ?_, ?_⟩
  · intro x hx
    dsimp
    rw [(eval_T_real_eq_neg_one_iff hn _).mpr ⟨k]; rw [le_of_lt hk₁]; rw [hk₂]; rw [rfl⟩]
    refine (abs_le.mp (abs_eval_T_real_le_one n (by grind))).1
  · rw [← cos_pi]
    exact cos_lt_cos_of_nonneg_of_le_pi (le_of_lt zero_lt) (le_refl π) lt_pi
  · rw [← cos_zero]
    exact cos_lt_cos_of_nonneg_of_le_pi (le_refl 0) (le_of_lt lt_pi) zero_lt

/--
theorem `isLocalExtr_T_real` / 定理 `isLocalExtr_T_real`

English:
theorem isLocalExtr_T_real
  given: {n k : Nat} (hn : n != 0) (hk₀ : 0 < k) (hk₁ : k < n)
  proof: by
  cases k.even_or_odd
  case inl hk₂ => exact .inr (isLocalMax_T_real hn hk₀ hk₁ hk₂)
  case inr hk₂ => exact .inl (isLocalMin_T_real hn hk₁ hk₂)

中文:
定理 isLocalExtr_T_real
  条件: {n k : 自然数} (hn : n != 0) (hk₀ : 0 < k) (hk₁ : k < n)
  证明: by
  cases k.even_or_odd
  case inl hk₂ => exact .inr (isLocalMax_T_real hn hk₀ hk₁ hk₂)
  case inr hk₂ => exact .inl (isLocalMin_T_real hn hk₁ hk₂)

Depends on / 依赖: even_or_odd, isLocalMax_T_real, isLocalMin_T_real, k.even_or_odd
-/
theorem isLocalExtr_T_real {n k : Nat} (hn : n != 0) (hk₀ : 0 < k) (hk₁ : k < n) :
    IsLocalExtr (T Real n).eval (cos (k * π / n)) := by
  cases k.even_or_odd
  case inl hk₂ => exact .inr (isLocalMax_T_real hn hk₀ hk₁ hk₂)
  case inr hk₂ => exact .inl (isLocalMin_T_real hn hk₁ hk₂)

/--
theorem `isLocalExtr_T_real_iff` / 定理 `isLocalExtr_T_real_iff`

English:
theorem isLocalExtr_T_real_iff
  given: {n : Nat} (hn : 2 <= n) (x : Real)
  proof: by
  constructor
  · intro hx
    replace hx := hx.deriv_eq_zero
    rw [Polynomial.deriv]; rw [T_derivative_eq_U]; rw [eval_mul]; rw [Int.cast_natCast]; rw [eval_natCast]; rw [mul_eq_zero_iff_left (by aesop)] at hx
    replace hx : x in (U Real (n - 1)).roots :=
      (mem_roots (degree_ne_bot.mp (

中文:
定理 isLocalExtr_T_real_iff
  条件: {n : 自然数} (hn : 2 <= n) (x : 实数)
  证明: by
  constructor
  · intro hx
    replace hx := hx.deriv_eq_zero
    rw [Polynomial.deriv]; rw [T_derivative_eq_U]; rw [eval_mul]; rw [Int.cast_natCast]; rw [eval_natCast]; rw [mul_eq_zero_iff_left (by aesop)] at hx
    replace hx : x in (U Real (n - 1)).roots :=
      (mem_roots (degree_ne_bot.mp (

Depends on / 依赖: Finset, Finset.mem_image, Finset.mem_val, Int.cast_natCast, Polynomial, Polynomial.deriv, T_derivative_eq_U, WithBot, WithBot.natCast_ne_bot, cast_natCast, degree_U_natCast, degree_ne_bot, degree_ne_bot.mp, deriv_eq_zero, eval_mul, eval_natCast, hx.deriv_eq_zero, mem_image, mem_roots, mem_val
-/
theorem isLocalExtr_T_real_iff {n : Nat} (hn : 2 <= n) (x : Real) :
    IsLocalExtr (T Real n).eval x ↔ exists k in Finset.Ioo 0 n, x = cos (k * π / n) := by
  constructor
  · intro hx
    replace hx := hx.deriv_eq_zero
    rw [Polynomial.deriv]; rw [T_derivative_eq_U]; rw [eval_mul]; rw [Int.cast_natCast]; rw [eval_natCast]; rw [mul_eq_zero_iff_left (by aesop)] at hx
    replace hx : x in (U Real (n - 1)).roots :=
      (mem_roots (degree_ne_bot.mp (ne_of_eq_of_ne (by grind [degree_U_natCast])
        (WithBot.natCast_ne_bot (n - 1))))).mpr hx
    rw [show (n - 1 : Int) = (n - 1 : Nat) by grind]; rw [roots_U_real]; rw [Finset.mem_val] at hx
    obtain ⟨k, hk₁, hx⟩ := Finset.mem_image.mp hx
    refine ⟨k + 1, Finset.mem_Ioo.mpr ⟨k.zero_lt_succ, by grind⟩, ?_⟩
    rw [← hx]
    congr <;> norm_cast
    exact Nat.sub_add_cancel (Nat.one_le_of_lt hn)
  · rintro ⟨k, hk, hx⟩
    rw [hx]
    exact isLocalExtr_T_real (Nat.ne_zero_of_lt hn)
      (Finset.mem_Ioo.mp hk).1 (Finset.mem_Ioo.mp hk).2

/--
theorem `isMaxOn_T_real` / 定理 `isMaxOn_T_real`

English:
theorem isMaxOn_T_real
  given: {n k : Nat} (hn : n != 0) (hk₁ : k <= n) (hk₂ : Even k)
  proof: isMaxOn_iff.mpr (fun x hx => le_of_le_of_eq (abs_le.mp (abs_eval_T_real_le_one n (by grind))).2
    ((eval_T_real_eq_one_iff hn _).mpr ⟨k, hk₁, hk₂, rfl⟩).symm)

中文:
定理 isMaxOn_T_real
  条件: {n k : 自然数} (hn : n != 0) (hk₁ : k <= n) (hk₂ : Even k)
  证明: isMaxOn_iff.mpr (fun x hx => le_of_le_of_eq (abs_le.mp (abs_eval_T_real_le_one n (by grind))).2
    ((eval_T_real_eq_one_iff hn _).mpr ⟨k, hk₁, hk₂, rfl⟩).symm)

Depends on / 依赖: abs_eval_T_real_le_one, abs_le, abs_le.mp, eval_T_real_eq_one_iff, isMaxOn_iff, isMaxOn_iff.mpr, le_of_le_of_eq
-/
theorem isMaxOn_T_real {n k : Nat} (hn : n != 0) (hk₁ : k <= n) (hk₂ : Even k) :
    IsMaxOn (T Real n).eval (Set.Icc (-1) 1) (cos (k * π / n)) :=
  isMaxOn_iff.mpr (fun x hx => le_of_le_of_eq (abs_le.mp (abs_eval_T_real_le_one n (by grind))).2
    ((eval_T_real_eq_one_iff hn _).mpr ⟨k, hk₁, hk₂, rfl⟩).symm)

/--
theorem `isMinOn_T_real` / 定理 `isMinOn_T_real`

English:
theorem isMinOn_T_real
  given: {n k : Nat} (hn : n != 0) (hk₁ : k <= n) (hk₂ : Odd k)
  proof: isMinOn_iff.mpr (fun x hx => le_of_eq_of_le
    ((eval_T_real_eq_neg_one_iff hn _).mpr ⟨k, hk₁, hk₂, rfl⟩)
    (abs_le.mp (abs_eval_T_real_le_one n (by grind))).1)

中文:
定理 isMinOn_T_real
  条件: {n k : 自然数} (hn : n != 0) (hk₁ : k <= n) (hk₂ : Odd k)
  证明: isMinOn_iff.mpr (fun x hx => le_of_eq_of_le
    ((eval_T_real_eq_neg_one_iff hn _).mpr ⟨k, hk₁, hk₂, rfl⟩)
    (abs_le.mp (abs_eval_T_real_le_one n (by grind))).1)

Depends on / 依赖: abs_eval_T_real_le_one, abs_le, abs_le.mp, eval_T_real_eq_neg_one_iff, isMinOn_iff, isMinOn_iff.mpr, le_of_eq_of_le
-/
theorem isMinOn_T_real {n k : Nat} (hn : n != 0) (hk₁ : k <= n) (hk₂ : Odd k) :
    IsMinOn (T Real n).eval (Set.Icc (-1) 1) (cos (k * π / n)) :=
  isMinOn_iff.mpr (fun x hx => le_of_eq_of_le
    ((eval_T_real_eq_neg_one_iff hn _).mpr ⟨k, hk₁, hk₂, rfl⟩)
    (abs_le.mp (abs_eval_T_real_le_one n (by grind))).1)

/--
theorem `isExtrOn_T_real` / 定理 `isExtrOn_T_real`

English:
theorem isExtrOn_T_real
  given: {n k : Nat} (hn : n != 0) (hk : k <= n)
  proof: by
  cases k.even_or_odd
  case inl hk₂ => exact .inr (isMaxOn_T_real hn hk hk₂)
  case inr hk₂ => exact .inl (isMinOn_T_real hn hk hk₂)

中文:
定理 isExtrOn_T_real
  条件: {n k : 自然数} (hn : n != 0) (hk : k <= n)
  证明: by
  cases k.even_or_odd
  case inl hk₂ => exact .inr (isMaxOn_T_real hn hk hk₂)
  case inr hk₂ => exact .inl (isMinOn_T_real hn hk hk₂)

Depends on / 依赖: even_or_odd, isMaxOn_T_real, isMinOn_T_real, k.even_or_odd
-/
theorem isExtrOn_T_real {n k : Nat} (hn : n != 0) (hk : k <= n) :
    IsExtrOn (T Real n).eval (Set.Icc (-1) 1) (cos (k * π / n)) := by
  cases k.even_or_odd
  case inl hk₂ => exact .inr (isMaxOn_T_real hn hk hk₂)
  case inr hk₂ => exact .inl (isMinOn_T_real hn hk hk₂)

/--
theorem `isExtrOn_T_real_iff` / 定理 `isExtrOn_T_real_iff`

English:
theorem isExtrOn_T_real_iff
  given: {n : Nat} (hn : n != 0) {x : Real} (hx : x in Set.Icc (-1) 1)
  proof: by
  constructor
  · intro h
    apply (abs_eval_T_real_eq_one_iff hn x).mp
    apply eq_of_le_of_ge (abs_eval_T_real_le_one n (by grind))
    refine h.elim (fun h => ?_) (fun h => ?_)
    · refine le_abs.mpr (.inr (le_neg_of_le_neg ?_))
      have := isMinOn_iff.mp h (cos (1 * π / n)) (by grind [ab

中文:
定理 isExtrOn_T_real_iff
  条件: {n : 自然数} (hn : n != 0) {x : 实数} (hx : x in Set.Icc (-1) 1)
  证明: by
  constructor
  · intro h
    apply (abs_eval_T_real_eq_one_iff hn x).mp
    apply eq_of_le_of_ge (abs_eval_T_real_le_one n (by grind))
    refine h.elim (fun h => ?_) (fun h => ?_)
    · refine le_abs.mpr (.inr (le_neg_of_le_neg ?_))
      have := isMinOn_iff.mp h (cos (1 * π / n)) (by grind [ab

Depends on / 依赖: Nat.one_le_iff_ne_zero.mpr, abs_cos_le_one, abs_eval_T_real_eq_one_iff, abs_eval_T_real_le_one, eq_of_le_of_ge, eval_T_real_eq_neg_one_iff, h.elim, isMaxOn_iff, isMaxOn_iff.mp, isMinOn_iff, isMinOn_iff.mp, le_abs, le_abs.mpr, le_neg_of_le_neg, one_le_iff_ne_zero
-/
theorem isExtrOn_T_real_iff {n : Nat} (hn : n != 0) {x : Real} (hx : x in Set.Icc (-1) 1) :
    IsExtrOn (T Real n).eval (Set.Icc (-1) 1) x ↔
    exists k <= n, x = cos (k * π / n) := by
  constructor
  · intro h
    apply (abs_eval_T_real_eq_one_iff hn x).mp
    apply eq_of_le_of_ge (abs_eval_T_real_le_one n (by grind))
    refine h.elim (fun h => ?_) (fun h => ?_)
    · refine le_abs.mpr (.inr (le_neg_of_le_neg ?_))
      have := isMinOn_iff.mp h (cos (1 * π / n)) (by grind [abs_cos_le_one])
      rw [(eval_T_real_eq_neg_one_iff hn (cos (1 * π / n))).mpr ⟨1]; rw [Nat.one_le_iff_ne_zero.mpr hn]; rw [by simp⟩] at this
      assumption
    · refine le_abs.mpr (.inl ?_)
      have := isMaxOn_iff.mp h (cos (0 * π / n)) (by simp)
      rw [(eval_T_real_eq_one_iff hn _).mpr ⟨0]; rw [by simp]; rw [by simp⟩] at this
      assumption
  · rintro ⟨k, hk, hx⟩
    rw [hx]
    exact isExtrOn_T_real hn hk

/--
theorem `irrational_of_isRoot_T_real` / 定理 `irrational_of_isRoot_T_real`

English:
theorem irrational_of_isRoot_T_real
  given: {n : Nat} {x : Real} (hroot : (T Real n).IsRoot x) (hnz : x != 0)
  proof: by
  rw [← mem_roots (T_ne_zero Real n)]; rw [roots_T_real]; rw [Finset.mem_val] at hroot
  obtain ⟨k, hk₁, hk₂⟩ := Finset.mem_image.mp hroot
  have hn : n != 0 := by grind
  suffices Irrational (cos ((Rat.divInt (2 * k + 1) (2 * n)) * π)) by
    rw [← hk₂]; convert! this using 2; push_cast; field_s

中文:
定理 irrational_of_isRoot_T_real
  条件: {n : 自然数} {x : 实数} (hroot : (T 实数 n).IsRoot x) (hnz : x != 0)
  证明: by
  rw [← mem_roots (T_ne_zero Real n)]; rw [roots_T_real]; rw [Finset.mem_val] at hroot
  obtain ⟨k, hk₁, hk₂⟩ := Finset.mem_image.mp hroot
  have hn : n != 0 := by grind
  suffices Irrational (cos ((Rat.divInt (2 * k + 1) (2 * n)) * π)) by
    rw [← hk₂]; convert! this using 2; push_cast; field_s

Depends on / 依赖: Finset, Finset.mem_image.mp, Finset.mem_val, Irrational, Rat.den_divInt, Rat.divInt, T_ne_zero, contrapose, convert, den_divInt, divInt, irrational_cos_rat_mul_pi, mem_image, mem_roots, mem_val, n.gcd, roots_T_real
-/
theorem irrational_of_isRoot_T_real {n : Nat} {x : Real} (hroot : (T Real n).IsRoot x) (hnz : x != 0) :
    Irrational x := by
  rw [← mem_roots (T_ne_zero Real n)]; rw [roots_T_real]; rw [Finset.mem_val] at hroot
  obtain ⟨k, hk₁, hk₂⟩ := Finset.mem_image.mp hroot
  have hn : n != 0 := by grind
  suffices Irrational (cos ((Rat.divInt (2 * k + 1) (2 * n)) * π)) by
    rw [← hk₂]; convert! this using 2; push_cast; field_simp
  apply irrational_cos_rat_mul_pi
  contrapose! hnz
  have : (Rat.divInt (2 * k + 1) (2 * n)).den = 2 * (n / n.gcd (2 * k + 1)) := calc
    _ = 2 * n / (2 * n).gcd (2 * k + 1) := by rw [Rat.den_divInt]; norm_cast; simp [hn]
    _ = _ := by rw [Nat.Coprime.gcd_mul_left_cancel n (by simp),
      Nat.mul_div_assoc _ (Nat.gcd_dvd_left ..)]
  have hn : 2 * k + 1 = n := Nat.eq_of_dvd_of_lt_two_mul (by simp) (Nat.gcd_eq_left_iff_dvd.mp <|
    Nat.eq_of_dvd_of_div_eq_one (Nat.gcd_dvd_left ..) (by grind [Rat.den_pos])) (by grind)
  rw_mod_cast [← hk₂, hn]; convert! cos_pi_div_two using 2; push_cast; field_simp

/--
theorem `abs_iterate_derivative_T_real_le` / 定理 `abs_iterate_derivative_T_real_le`

English:
theorem abs_iterate_derivative_T_real_le
  given: (n : Int) (k : Nat) {x : Real} (hx : |x| <= 1)
  proof: by
  wlog hn : 0 <= n
  · convert! this (-n) k hx (by grind) using 1 <;> rw [T_neg]
  lift n to Nat using hn
  have := T_iterate_derivative_mem_span_T (R := Real) n k
  obtain ⟨f, hfsupp, hfderiv⟩ := Submodule.mem_span_set.mp this
  replace hfderiv : ∑ p in f.support, f p • p = derivative^[k] (T Rea

中文:
定理 abs_iterate_derivative_T_real_le
  条件: (n : 整数) (k : 自然数) {x : 实数} (hx : |x| <= 1)
  证明: by
  wlog hn : 0 <= n
  · convert! this (-n) k hx (by grind) using 1 <;> rw [T_neg]
  lift n to Nat using hn
  have := T_iterate_derivative_mem_span_T (R := Real) n k
  obtain ⟨f, hfsupp, hfderiv⟩ := Submodule.mem_span_set.mp this
  replace hfderiv : ∑ p in f.support, f p • p = derivative^[k] (T Rea

Depends on / 依赖: Polynomial, Polynomial.eval_finsetSum, Polynomial.eval_smul, Submodule, Submodule.mem_span_set.mp, T_iterate_derivative_mem_span_T, T_neg, convert, derivative, eval_finsetSum, eval_smul, f.support, hfderiv, hfsupp, mem_span_set, p.eval, replace, simp_rw, support
-/
theorem abs_iterate_derivative_T_real_le (n : Int) (k : Nat) {x : Real} (hx : |x| <= 1) :
    |(derivative^[k] (T Real n)).eval x| <= (derivative^[k] (T Real n)).eval 1 := by
  wlog hn : 0 <= n
  · convert! this (-n) k hx (by grind) using 1 <;> rw [T_neg]
  lift n to Nat using hn
  have := T_iterate_derivative_mem_span_T (R := Real) n k
  obtain ⟨f, hfsupp, hfderiv⟩ := Submodule.mem_span_set.mp this
  replace hfderiv : ∑ p in f.support, f p • p = derivative^[k] (T Real n) := by rw [← hfderiv]; rfl
  have hf (y : Real) :
      ∑ p in f.support, f p • p.eval y = (derivative^[k] (T Real n)).eval y := by
    rw [← hfderiv]; rw [Polynomial.eval_finsetSum]
    simp_rw [Polynomial.eval_smul]
  rw [← hf x]; rw [← hf 1]
  grw [Finset.abs_sum_le_sum_abs]
  refine Finset.sum_le_sum (fun i hi => ?_)
  obtain ⟨m, hm, hi⟩ := (Set.mem_image ..).mp (hfsupp hi)
  grw [abs_nsmul, ← hi, abs_eval_T_real_le_one m hx]
  simp

end Polynomial.Chebyshev
