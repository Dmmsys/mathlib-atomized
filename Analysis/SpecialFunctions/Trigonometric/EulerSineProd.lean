/-
Copyright (c) 2023 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Integral.PeakFunction

/-! # Euler's infinite product for the sine function

This file proves the infinite product formula

$$ \sin \pi z = \pi z \prod_{n = 1}^\infty \left(1 - \frac{z ^ 2}{n ^ 2}\right) $$

for any real or complex `z`. Our proof closely follows the article
[Salwinski, *Euler's Sine Product Formula: An Elementary Proof*][salwinski2018]: the basic strategy
is to prove a recurrence relation for the integrals `∫ x in 0..π/2, cos 2 z x * cos x ^ (2 * n)`,
generalising the arguments used to prove Wallis' limit formula for `π`.
-/

public section

open scoped Real Topology

open Real Set Filter intervalIntegral MeasureTheory.MeasureSpace

namespace EulerSine

section IntegralRecursion

/-! ## Recursion formula for the integral of `cos (2 * z * x) * cos x ^ n`

We evaluate the integral of `cos (2 * z * x) * cos x ^ n`, for any complex `z` and even integers
`n`, via repeated integration by parts. -/


variable {z : Complex} {n : Nat}

/--
theorem `antideriv_cos_comp_const_mul` / 定理 `antideriv_cos_comp_const_mul`

English:
theorem antideriv_cos_comp_const_mul
  given: (hz : z != 0) (x : Real)
  proof: by
  have a : HasDerivAt (fun y : Complex => y * (2 * z)) _ x := hasDerivAt_mul_const _
  have b : HasDerivAt (Complex.sin ∘ fun y : Complex => (y * (2 * z))) _ x :=
    HasDerivAt.comp (x : Complex) (Complex.hasDerivAt_sin (x * (2 * z))) a
  have c := b.comp_ofReal.div_const (2 * z)
  field_simp at

中文:
定理 antideriv_cos_comp_const_mul
  条件: (hz : z != 0) (x : 实数)
  证明: by
  have a : HasDerivAt (fun y : Complex => y * (2 * z)) _ x := hasDerivAt_mul_const _
  have b : HasDerivAt (Complex.sin ∘ fun y : Complex => (y * (2 * z))) _ x :=
    HasDerivAt.comp (x : Complex) (Complex.hasDerivAt_sin (x * (2 * z))) a
  have c := b.comp_ofReal.div_const (2 * z)
  field_simp at

Depends on / 依赖: Complex.hasDerivAt_sin, Complex.sin, HasDerivAt, HasDerivAt.comp, b.comp_ofReal.div_const, comp_ofReal, div_const, hasDerivAt_mul_const, hasDerivAt_sin, mul_rotate
-/
theorem antideriv_cos_comp_const_mul (hz : z != 0) (x : Real) :
    HasDerivAt (fun y : Real => Complex.sin (2 * z * y) / (2 * z)) (Complex.cos (2 * z * x)) x := by
  have a : HasDerivAt (fun y : Complex => y * (2 * z)) _ x := hasDerivAt_mul_const _
  have b : HasDerivAt (Complex.sin ∘ fun y : Complex => (y * (2 * z))) _ x :=
    HasDerivAt.comp (x : Complex) (Complex.hasDerivAt_sin (x * (2 * z))) a
  have c := b.comp_ofReal.div_const (2 * z)
  field_simp at c; simp only [mul_rotate _ 2 z] at c
  exact c

/--
theorem `antideriv_sin_comp_const_mul` / 定理 `antideriv_sin_comp_const_mul`

English:
theorem antideriv_sin_comp_const_mul
  given: (hz : z != 0) (x : Real)
  proof: by
  have a : HasDerivAt (fun y : Complex => y * (2 * z)) _ x := hasDerivAt_mul_const _
  have b : HasDerivAt (Complex.cos ∘ fun y : Complex => (y * (2 * z))) _ x :=
    HasDerivAt.comp (x : Complex) (Complex.hasDerivAt_cos (x * (2 * z))) a
  have c := (b.comp_ofReal.div_const (2 * z)).fun_neg
  sim

中文:
定理 antideriv_sin_comp_const_mul
  条件: (hz : z != 0) (x : 实数)
  证明: by
  have a : HasDerivAt (fun y : Complex => y * (2 * z)) _ x := hasDerivAt_mul_const _
  have b : HasDerivAt (Complex.cos ∘ fun y : Complex => (y * (2 * z))) _ x :=
    HasDerivAt.comp (x : Complex) (Complex.hasDerivAt_cos (x * (2 * z))) a
  have c := (b.comp_ofReal.div_const (2 * z)).fun_neg
  sim

Depends on / 依赖: Complex.cos, Complex.hasDerivAt_cos, HasDerivAt, HasDerivAt.comp, b.comp_ofReal.div_const, comp_ofReal, div_const, fun_neg, hasDerivAt_cos, hasDerivAt_mul_const, mul_rotate
-/
theorem antideriv_sin_comp_const_mul (hz : z != 0) (x : Real) :
    HasDerivAt (fun y : Real => -Complex.cos (2 * z * y) / (2 * z)) (Complex.sin (2 * z * x)) x := by
  have a : HasDerivAt (fun y : Complex => y * (2 * z)) _ x := hasDerivAt_mul_const _
  have b : HasDerivAt (Complex.cos ∘ fun y : Complex => (y * (2 * z))) _ x :=
    HasDerivAt.comp (x : Complex) (Complex.hasDerivAt_cos (x * (2 * z))) a
  have c := (b.comp_ofReal.div_const (2 * z)).fun_neg
  simp at c ⊢; field_simp at c ⊢; simp only [mul_rotate _ 2 z] at c
  exact c

/--
theorem `integral_cos_mul_cos_pow_aux` / 定理 `integral_cos_mul_cos_pow_aux`

English:
theorem integral_cos_mul_cos_pow_aux
  given: (hn : 2 <= n) (hz : z != 0)
  proof: by
  have der1 :
    forall x : Real,
      x in uIcc 0 (π / 2) ->
        HasDerivAt (fun y : Real => (cos y : Complex) ^ n) (-n * sin x * (cos x : Complex) ^ (n - 1)) x := by
    intro x _
    have b : HasDerivAt (fun y : Real => (cos y : Complex)) (-sin x) x := by
      simpa using (hasDerivAt_co

中文:
定理 integral_cos_mul_cos_pow_aux
  条件: (hn : 2 <= n) (hz : z != 0)
  证明: by
  have der1 :
    forall x : Real,
      x in uIcc 0 (π / 2) ->
        HasDerivAt (fun y : Real => (cos y : Complex) ^ n) (-n * sin x * (cos x : Complex) ^ (n - 1)) x := by
    intro x _
    have b : HasDerivAt (fun y : Real => (cos y : Complex)) (-sin x) x := by
      simpa using (hasDerivAt_co

Depends on / 依赖: HasDerivAt, HasDerivAt.comp, antideriv_cos_comp_const_mul, config, convert, hasDerivAt_cos, hasDerivAt_pow, integral_mul_deriv_eq_deriv_mul, ofReal_comp, sameFun
-/
theorem integral_cos_mul_cos_pow_aux (hn : 2 <= n) (hz : z != 0) :
    (∫ x in (0 : Real)..π / 2, Complex.cos (2 * z * x) * (cos x : Complex) ^ n) =
      n / (2 * z) *
        ∫ x in (0 : Real)..π / 2, Complex.sin (2 * z * x) * sin x * (cos x : Complex) ^ (n - 1) := by
  have der1 :
    forall x : Real,
      x in uIcc 0 (π / 2) ->
        HasDerivAt (fun y : Real => (cos y : Complex) ^ n) (-n * sin x * (cos x : Complex) ^ (n - 1)) x := by
    intro x _
    have b : HasDerivAt (fun y : Real => (cos y : Complex)) (-sin x) x := by
      simpa using (hasDerivAt_cos x).ofReal_comp
    convert! HasDerivAt.comp x (hasDerivAt_pow _ _) b using 1
    ring
  convert! (config := { sameFun := true })
    integral_mul_deriv_eq_deriv_mul der1 (fun x _ => antideriv_cos_comp_const_mul hz x) _ _ using 2
  · ext1 x; rw [mul_comm]
  · rw [Complex.ofReal_zero, mul_zero, Complex.sin_zero, zero_div, mul_zero, sub_zero,
      cos_pi_div_two, Complex.ofReal_zero, zero_pow (by positivity : n != 0), zero_mul, zero_sub,
      ← integral_neg, ← integral_const_mul]
    refine integral_congr fun x _ => ?_
    ring
  · apply Continuous.intervalIntegrable (by fun_prop)
· apply Continuous.intervalIntegrable by fun_prop

/--
theorem `integral_sin_mul_sin_mul_cos_pow_eq` / 定理 `integral_sin_mul_sin_mul_cos_pow_eq`

English:
theorem integral_sin_mul_sin_mul_cos_pow_eq
  given: (hn : 2 <= n) (hz : z != 0)
  proof: by
  have der1 :
    forall x : Real,
      x in uIcc 0 (π / 2) ->
        HasDerivAt (fun y : Real => sin y * (cos y : Complex) ^ (n - 1))
          ((cos x : Complex) ^ n - (n - 1) * (sin x : Complex) ^ 2 * (cos x : Complex) ^ (n - 2)) x := by
    intro x _
    have c := HasDerivAt.comp (x : Compl

中文:
定理 integral_sin_mul_sin_mul_cos_pow_eq
  条件: (hn : 2 <= n) (hz : z != 0)
  证明: by
  have der1 :
    forall x : Real,
      x in uIcc 0 (π / 2) ->
        HasDerivAt (fun y : Real => sin y * (cos y : Complex) ^ (n - 1))
          ((cos x : Complex) ^ n - (n - 1) * (sin x : Complex) ^ 2 * (cos x : Complex) ^ (n - 2)) x := by
    intro x _
    have c := HasDerivAt.comp (x : Compl

Depends on / 依赖: Complex.hasDerivAt_cos, Complex.hasDerivAt_sin, Complex.ofR, Complex.ofReal_cos, Complex.ofReal_sin, Function, Function.comp, HasDerivAt, HasDerivAt.comp, comp_ofReal, convert, fun_mul, hasDerivAt_cos, hasDerivAt_pow, hasDerivAt_sin, ofReal_cos, ofReal_sin
-/
theorem integral_sin_mul_sin_mul_cos_pow_eq (hn : 2 <= n) (hz : z != 0) :
    (∫ x in (0 : Real)..π / 2, Complex.sin (2 * z * x) * sin x * (cos x : Complex) ^ (n - 1)) =
      (n / (2 * z) * ∫ x in (0 : Real)..π / 2, Complex.cos (2 * z * x) * (cos x : Complex) ^ n) -
        (n - 1) / (2 * z) *
          ∫ x in (0 : Real)..π / 2, Complex.cos (2 * z * x) * (cos x : Complex) ^ (n - 2) := by
  have der1 :
    forall x : Real,
      x in uIcc 0 (π / 2) ->
        HasDerivAt (fun y : Real => sin y * (cos y : Complex) ^ (n - 1))
          ((cos x : Complex) ^ n - (n - 1) * (sin x : Complex) ^ 2 * (cos x : Complex) ^ (n - 2)) x := by
    intro x _
    have c := HasDerivAt.comp (x : Complex) (hasDerivAt_pow (n - 1) _) (Complex.hasDerivAt_cos x)
    convert! ((Complex.hasDerivAt_sin x).fun_mul c).comp_ofReal using 1
    · simp only [Complex.ofReal_sin, Complex.ofReal_cos, Function.comp]
    · simp only [Complex.ofReal_cos, Complex.ofReal_sin]
      rw [mul_neg]; rw [mul_neg]; rw [← sub_eq_add_neg]; rw [Function.comp_apply]
      congr 1
      · rw [← pow_succ', Nat.sub_add_cancel (by lia : 1 <= n)]
      · have : ((n - 1 : Nat) : Complex) = (n : Complex) - 1 := by
          rw [Nat.cast_sub (one_le_two.trans hn)]; rw [Nat.cast_one]
        rw [Nat.sub_sub]; rw [this]
        ring
  convert!
    integral_mul_deriv_eq_deriv_mul der1 (fun x _ => antideriv_sin_comp_const_mul hz x) _ _ using 1
  · refine integral_congr fun x _ => ?_
    ring_nf
  · -- now a tedious rearrangement of terms
    -- gather into a single integral, and deal with continuity subgoals:
    rw [sin_zero]; rw [cos_pi_div_two]; rw [Complex.ofReal_zero]; rw [zero_pow]; rw [zero_mul]; rw [mul_zero]; rw [zero_mul]; rw [zero_mul]; rw [sub_zero]; rw [zero_sub]; rw [←
      integral_neg]; rw [← integral_const_mul]; rw [← integral_const_mul]; rw [← integral_sub]
    rotate_left
· apply Continuous.intervalIntegrable by fun_prop
· apply Continuous.intervalIntegrable by fun_prop
    · exact Nat.sub_ne_zero_of_lt hn
    refine integral_congr fun x _ => ?_
    -- get rid of real trig functions and divisions by 2 * z:
    rw [Complex.ofReal_cos]; rw [Complex.ofReal_sin]; rw [Complex.sin_sq]; rw [← mul_div_right_comm]; rw [←
      mul_div_right_comm]; rw [← sub_div]; rw [mul_div]; rw [← neg_div]
    congr 1
    have : Complex.cos x ^ n = Complex.cos x ^ (n - 2) * Complex.cos x ^ 2 := by
      conv_lhs => rw [← Nat.sub_add_cancel hn, pow_add]
    rw [this]
    ring
· apply Continuous.intervalIntegrable by fun_prop
· apply Continuous.intervalIntegrable by fun_prop

/--
theorem `integral_cos_mul_cos_pow` / 定理 `integral_cos_mul_cos_pow`

English:
theorem integral_cos_mul_cos_pow
  given: (hn : 2 <= n) (hz : z != 0)
  proof: by
  have nne : (n : Complex) != 0 := by
    contrapose! hn; rw [Nat.cast_eq_zero] at hn; rw [hn]; exact zero_lt_two
  have := integral_cos_mul_cos_pow_aux hn hz
  rw [integral_sin_mul_sin_mul_cos_pow_eq hn hz]; rw [sub_eq_neg_add]; rw [mul_add]; rw [← sub_eq_iff_eq_add]
    at this
  convert! congr

中文:
定理 integral_cos_mul_cos_pow
  条件: (hn : 2 <= n) (hz : z != 0)
  证明: by
  have nne : (n : Complex) != 0 := by
    contrapose! hn; rw [Nat.cast_eq_zero] at hn; rw [hn]; exact zero_lt_two
  have := integral_cos_mul_cos_pow_aux hn hz
  rw [integral_sin_mul_sin_mul_cos_pow_eq hn hz]; rw [sub_eq_neg_add]; rw [mul_add]; rw [← sub_eq_iff_eq_add]
    at this
  convert! congr

Depends on / 依赖: Nat.cast_eq_zero, cast_eq_zero, congr_arg, contrapose, convert, integral_cos_mul_cos_pow_aux, integral_sin_mul_sin_mul_cos_pow_eq, mul_add, sub_eq_iff_eq_add, sub_eq_neg_add, zero_lt_two
-/
theorem integral_cos_mul_cos_pow (hn : 2 <= n) (hz : z != 0) :
    (((1 : Complex) - (4 : Complex) * z ^ 2 / (n : Complex) ^ 2) *
      ∫ x in (0 : Real)..π / 2, Complex.cos (2 * z * x) * (cos x : Complex) ^ n) =
      (n - 1 : Complex) / n *
        ∫ x in (0 : Real)..π / 2, Complex.cos (2 * z * x) * (cos x : Complex) ^ (n - 2) := by
  have nne : (n : Complex) != 0 := by
    contrapose! hn; rw [Nat.cast_eq_zero] at hn; rw [hn]; exact zero_lt_two
  have := integral_cos_mul_cos_pow_aux hn hz
  rw [integral_sin_mul_sin_mul_cos_pow_eq hn hz]; rw [sub_eq_neg_add]; rw [mul_add]; rw [← sub_eq_iff_eq_add]
    at this
  convert! congr_arg (fun u : Complex => -u * (2 * z) ^ 2 / n ^ 2) this using 1 <;> field

/--
theorem `integral_cos_mul_cos_pow_even` / 定理 `integral_cos_mul_cos_pow_even`

English:
theorem integral_cos_mul_cos_pow_even
  given: (n : Nat) (hz : z != 0)
  proof: by
  convert! integral_cos_mul_cos_pow (by lia : 2 <= 2 * n + 2) hz using 3
  · simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_two]
    nth_rw 2 [← mul_one (2 : Complex)]
    rw [← mul_add]; rw [mul_pow]; rw [← div_div]
    ring
  · push_cast; ring
  · push_cast; ring

中文:
定理 integral_cos_mul_cos_pow_even
  条件: (n : 自然数) (hz : z != 0)
  证明: by
  convert! integral_cos_mul_cos_pow (by lia : 2 <= 2 * n + 2) hz using 3
  · simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_two]
    nth_rw 2 [← mul_one (2 : Complex)]
    rw [← mul_add]; rw [mul_pow]; rw [← div_div]
    ring
  · push_cast; ring
  · push_cast; ring

Depends on / 依赖: Nat.cast_add, Nat.cast_mul, Nat.cast_two, cast_add, cast_mul, cast_two, convert, div_div, integral_cos_mul_cos_pow, mul_add, mul_one, mul_pow, nth_rw
-/
theorem integral_cos_mul_cos_pow_even (n : Nat) (hz : z != 0) :
    (((1 : Complex) - z ^ 2 / ((n : Complex) + 1) ^ 2) *
        ∫ x in (0 : Real)..π / 2, Complex.cos (2 * z * x) * (cos x : Complex) ^ (2 * n + 2)) =
      (2 * n + 1 : Complex) / (2 * n + 2) *
        ∫ x in (0 : Real)..π / 2, Complex.cos (2 * z * x) * (cos x : Complex) ^ (2 * n) := by
  convert! integral_cos_mul_cos_pow (by lia : 2 <= 2 * n + 2) hz using 3
  · simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_two]
    nth_rw 2 [← mul_one (2 : Complex)]
    rw [← mul_add]; rw [mul_pow]; rw [← div_div]
    ring
  · push_cast; ring
  · push_cast; ring

/--
theorem `integral_cos_pow_eq` / 定理 `integral_cos_pow_eq`

English:
theorem integral_cos_pow_eq
  given: (n : Nat)
  proof: by
  rw [mul_comm (1 / 2 : Real)]; rw [← div_eq_iff (one_div_ne_zero (two_ne_zero' Real))]; rw [← div_mul]; rw [div_one]; rw [mul_two]
  have L : IntervalIntegrable _ volume 0 (π / 2) :=
    (continuous_sin.fun_pow n).intervalIntegrable _ _
  have R : IntervalIntegrable _ volume (π / 2) π :=
    (co

中文:
定理 integral_cos_pow_eq
  条件: (n : 自然数)
  证明: by
  rw [mul_comm (1 / 2 : Real)]; rw [← div_eq_iff (one_div_ne_zero (two_ne_zero' Real))]; rw [← div_mul]; rw [div_one]; rw [mul_two]
  have L : IntervalIntegrable _ volume 0 (π / 2) :=
    (continuous_sin.fun_pow n).intervalIntegrable _ _
  have R : IntervalIntegrable _ volume (π / 2) π :=
    (co

Depends on / 依赖: IntervalIntegrable, continuous_sin, continuous_sin.fun_pow, div_eq_iff, div_mul, div_one, fun_pow, integral_add_adjacent_intervals, integral_comp_sub_left, intervalIntegrable, mul_comm, mul_two, nth_rw, one_div_ne_zero, two_ne_zero, volume
-/
theorem integral_cos_pow_eq (n : Nat) :
    (∫ x in (0 : Real)..π / 2, cos x ^ n) = 1 / 2 * ∫ x in (0 : Real)..π, sin x ^ n := by
  rw [mul_comm (1 / 2 : Real)]; rw [← div_eq_iff (one_div_ne_zero (two_ne_zero' Real))]; rw [← div_mul]; rw [div_one]; rw [mul_two]
  have L : IntervalIntegrable _ volume 0 (π / 2) :=
    (continuous_sin.fun_pow n).intervalIntegrable _ _
  have R : IntervalIntegrable _ volume (π / 2) π :=
    (continuous_sin.fun_pow n).intervalIntegrable _ _
  rw [← integral_add_adjacent_intervals L R]
  congr 1
  · nth_rw 1 [(by ring : 0 = π / 2 - π / 2)]
    nth_rw 3 [(by ring : π / 2 = π / 2 - 0)]
    rw [← integral_comp_sub_left]
    refine integral_congr fun x _ => ?_
    rw [cos_pi_div_two_sub]
  · nth_rw 3 [(by ring : π = π / 2 + π / 2)]
    nth_rw 2 [(by ring : π / 2 = 0 + π / 2)]
    rw [← integral_comp_add_right]
    refine integral_congr fun x _ => ?_
    rw [sin_add_pi_div_two]

/--
theorem `integral_cos_pow_pos` / 定理 `integral_cos_pow_pos`

English:
theorem integral_cos_pow_pos
  given: (n : Nat)
  statement: 0 < ∫ x in (0 : Real)..π / 2, cos x ^ n
  proof: (integral_cos_pow_eq n).symm ▸ mul_pos one_half_pos (integral_sin_pow_pos _)

中文:
定理 integral_cos_pow_pos
  条件: (n : 自然数)
  结论: 0 < ∫ x in (0 : 实数)..π / 2, cos x ^ n
  证明: (integral_cos_pow_eq n).symm ▸ mul_pos one_half_pos (integral_sin_pow_pos _)

Depends on / 依赖: integral_cos_pow_eq, integral_sin_pow_pos, mul_pos, one_half_pos
-/
theorem integral_cos_pow_pos (n : Nat) : 0 < ∫ x in (0 : Real)..π / 2, cos x ^ n :=
  (integral_cos_pow_eq n).symm ▸ mul_pos one_half_pos (integral_sin_pow_pos _)

/--
theorem `sin_pi_mul_eq` / 定理 `sin_pi_mul_eq`

English:
theorem sin_pi_mul_eq
  given: (z : Complex) (n : Nat)
  proof: by
  rcases eq_or_ne z 0 with (rfl | hz)
  · simp
  induction n with
  | zero =>
    simp_rw [mul_zero, pow_zero, mul_one, Finset.prod_range_zero, mul_one,
      integral_one, sub_zero]
    rw [integral_cos_mul_complex (mul_ne_zero two_ne_zero hz)]; rw [Complex.ofReal_zero]; rw [mul_zero]; rw [Compl

中文:
定理 sin_pi_mul_eq
  条件: (z : Complex) (n : 自然数)
  证明: by
  rcases eq_or_ne z 0 with (rfl | hz)
  · simp
  induction n with
  | zero =>
    simp_rw [mul_zero, pow_zero, mul_one, Finset.prod_range_zero, mul_one,
      integral_one, sub_zero]
    rw [integral_cos_mul_complex (mul_ne_zero two_ne_zero hz)]; rw [Complex.ofReal_zero]; rw [mul_zero]; rw [Compl

Depends on / 依赖: Complex.ofReal_zero, Complex.sin_zero, Finset, Finset.prod_range_succ, Finset.prod_range_zero, Finset.range, eq_or_ne, integral_cos_mul_complex, integral_one, mul_ne_zero, mul_one, mul_zero, ofReal_zero, pow_zero, prod_range_succ, prod_range_zero, simp_rw, sin_zero, sub_zero, two_ne_zero
-/
theorem sin_pi_mul_eq (z : Complex) (n : Nat) :
    Complex.sin (π * z) =
      ((π * z * ∏ j in Finset.range n, ((1 : Complex) - z ^ 2 / ((j : Complex) + 1) ^ 2)) *
          ∫ x in (0 : Real)..π / 2, Complex.cos (2 * z * x) * (cos x : Complex) ^ (2 * n)) /
        (∫ x in (0 : Real)..π / 2, cos x ^ (2 * n) : Real) := by
  rcases eq_or_ne z 0 with (rfl | hz)
  · simp
  induction n with
  | zero =>
    simp_rw [mul_zero, pow_zero, mul_one, Finset.prod_range_zero, mul_one,
      integral_one, sub_zero]
    rw [integral_cos_mul_complex (mul_ne_zero two_ne_zero hz)]; rw [Complex.ofReal_zero]; rw [mul_zero]; rw [Complex.sin_zero]; rw [zero_div]; rw [sub_zero]; rw [(by push_cast; ring : 2 * z * ↑(π / 2) = π * z)]
    simp [field]
  | succ n hn =>
    rw [hn]; rw [Finset.prod_range_succ]
    set A := ∏ j in Finset.range n, ((1 : Complex) - z ^ 2 / ((j : Complex) + 1) ^ 2)
    set B := ∫ x in (0 : Real)..π / 2, Complex.cos (2 * z * x) * (cos x : Complex) ^ (2 * n)
    set C := ∫ x in (0 : Real)..π / 2, cos x ^ (2 * n)
    have aux' : 2 * n.succ = 2 * n + 2 := by rw [Nat.succ_eq_add_one, mul_add, mul_one]
    have : (∫ x in (0 : Real)..π / 2, cos x ^ (2 * n.succ)) = (2 * (n : Real) + 1) / (2 * n + 2) * C := by
      rw [integral_cos_pow_eq]
      dsimp only [C]
      rw [integral_cos_pow_eq]; rw [aux']; rw [integral_sin_pow]; rw [sin_zero]; rw [sin_pi]; rw [pow_succ']; rw [zero_mul]; rw [zero_mul]; rw [zero_mul]; rw [sub_zero]; rw [zero_div]; rw [zero_add]; rw [← mul_assoc]; rw [← mul_assoc]; rw [mul_comm (1 / 2 : Real) _]; rw [Nat.cast_mul]; rw [Nat.cast_ofNat]
    rw [this]
    change
      π * z * A * B / C =
        (π * z * (A * ((1 : Complex) - z ^ 2 / ((n : Complex) + 1) ^ 2)) *
            ∫ x in (0 : Real)..π / 2, Complex.cos (2 * z * x) * (cos x : Complex) ^ (2 * n.succ)) /
          ((2 * n + 1) / (2 * n + 2) * C : Real)
    have :
      (π * z * (A * ((1 : Complex) - z ^ 2 / ((n : Complex) + 1) ^ 2)) *
          ∫ x in (0 : Real)..π / 2, Complex.cos (2 * z * x) * (cos x : Complex) ^ (2 * n.succ)) =
        π * z * A *
          (((1 : Complex) - z ^ 2 / (n.succ : Complex) ^ 2) *
            ∫ x in (0 : Real)..π / 2, Complex.cos (2 * z * x) * (cos x : Complex) ^ (2 * n.succ)) := by
      grind
    rw [this]
    suffices
      (((1 : Complex) - z ^ 2 / (n.succ : Complex) ^ 2) *
          ∫ x in (0 : Real)..π / 2, Complex.cos (2 * z * x) * (cos x : Complex) ^ (2 * n.succ)) =
        (2 * n + 1) / (2 * n + 2) * B by
      rw [this]; rw [Complex.ofReal_mul]; rw [Complex.ofReal_div]
      have : (C : Complex) != 0 := Complex.ofReal_ne_zero.mpr (integral_cos_pow_pos _).ne'
      have : 2 * (n : Complex) + 1 != 0 := by
        convert! (Nat.cast_add_one_ne_zero (2 * n) : (↑(2 * n) + 1 : Complex) != 0)
        simp
      have : (n : Complex) + 1 != 0 := Nat.cast_add_one_ne_zero n
      simp [field]
    convert! integral_cos_mul_cos_pow_even n hz
    rw [Nat.cast_succ]

end IntegralRecursion



/--
theorem `tendsto_integral_cos_pow_mul_div` / 定理 `tendsto_integral_cos_pow_mul_div`

English:
theorem tendsto_integral_cos_pow_mul_div
  given: {f : Real -> Complex} (hf : ContinuousOn f (Icc 0 (π / 2)))
  proof: by
  simp_rw [div_eq_inv_mul (α := Complex), ← Complex.ofReal_inv, integral_of_le pi_div_two_pos.le,
    ← MeasureTheory.integral_Icc_eq_integral_Ioc, ← Complex.ofReal_pow, ← Complex.real_smul]
  have c_lt : forall y : Real, y in Icc 0 (π / 2) -> y != 0 -> cos y < cos 0 := fun y hy hy' =>
    cos_lt

中文:
定理 tendsto_integral_cos_pow_mul_div
  条件: {f : 实数 -> Complex} (hf : ContinuousOn f (Icc 0 (π / 2)))
  证明: by
  simp_rw [div_eq_inv_mul (α := Complex), ← Complex.ofReal_inv, integral_of_le pi_div_two_pos.le,
    ← MeasureTheory.integral_Icc_eq_integral_Ioc, ← Complex.ofReal_pow, ← Complex.real_smul]
  have c_lt : forall y : Real, y in Icc 0 (π / 2) -> y != 0 -> cos y < cos 0 := fun y hy hy' =>
    cos_lt

Depends on / 依赖: Complex.ofReal_inv, Complex.ofReal_pow, Complex.real_smul, Icc_subset_Icc_left, MeasureTheory, MeasureTheory.integral_Icc_eq_integral_Ioc, c_lt, c_nonneg, cos_lt_cos_of_nonneg_of_le_pi_div_two, cos_nonneg_of_mem_Icc, div_eq_inv_mul, integral_Icc_eq_integral_Ioc, integral_of_le, le_refl, lt_of_le_of_ne, neg_no, ofReal_inv, ofReal_pow, pi_div_two_pos, pi_div_two_pos.le
-/
theorem tendsto_integral_cos_pow_mul_div {f : Real -> Complex} (hf : ContinuousOn f (Icc 0 (π / 2))) :
    Tendsto
      (fun n : Nat => (∫ x in (0 : Real)..π / 2, (cos x : Complex) ^ n * f x) /
        (∫ x in (0 : Real)..π / 2, cos x ^ n : Real))
      atTop (𝓝 <| f 0) := by
  simp_rw [div_eq_inv_mul (α := Complex), ← Complex.ofReal_inv, integral_of_le pi_div_two_pos.le,
    ← MeasureTheory.integral_Icc_eq_integral_Ioc, ← Complex.ofReal_pow, ← Complex.real_smul]
  have c_lt : forall y : Real, y in Icc 0 (π / 2) -> y != 0 -> cos y < cos 0 := fun y hy hy' =>
    cos_lt_cos_of_nonneg_of_le_pi_div_two (le_refl 0) hy.2 (lt_of_le_of_ne hy.1 hy'.symm)
  have c_nonneg : forall x : Real, x in Icc 0 (π / 2) -> 0 <= cos x := fun x hx =>
    cos_nonneg_of_mem_Icc ((Icc_subset_Icc_left (neg_nonpos_of_nonneg pi_div_two_pos.le)) hx)
  have c_zero_pos : 0 < cos 0 := by rw [cos_zero]; exact zero_lt_one
  have zero_mem : (0 : Real) in closure (interior (Icc 0 (π / 2))) := by
    rw [interior_Icc]; rw [closure_Ioo pi_div_two_pos.ne]; rw [left_mem_Icc]
    exact pi_div_two_pos.le
  exact
    tendsto_setIntegral_pow_smul_of_unique_maximum_of_isCompact_of_continuousOn isCompact_Icc
      continuousOn_cos c_lt c_nonneg c_zero_pos zero_mem hf

/--
theorem `_root_.Complex.tendsto_euler_sin_prod` / 定理 `_root_.Complex.tendsto_euler_sin_prod`

English:
theorem _root_.Complex.tendsto_euler_sin_prod
  given: (z : Complex)
  proof: by
  have A :
    Tendsto
      (fun n : Nat =>
        ((π * z * ∏ j in Finset.range n, ((1 : Complex) - z ^ 2 / ((j : Complex) + 1) ^ 2)) *
            ∫ x in (0 : Real)..π / 2, Complex.cos (2 * z * x) * (cos x : Complex) ^ (2 * n)) /
          (∫ x in (0 : Real)..π / 2, cos x ^ (2 * n) : Real))
 

中文:
定理 _root_.Complex.tendsto_euler_sin_prod
  条件: (z : Complex)
  证明: by
  have A :
    Tendsto
      (fun n : Nat =>
        ((π * z * ∏ j in Finset.range n, ((1 : Complex) - z ^ 2 / ((j : Complex) + 1) ^ 2)) *
            ∫ x in (0 : Real)..π / 2, Complex.cos (2 * z * x) * (cos x : Complex) ^ (2 * n)) /
          (∫ x in (0 : Real)..π / 2, cos x ^ (2 * n) : Real))
 

Depends on / 依赖: Complex.cos, Complex.sin, Finset, Finset.range, Tendsto, Tendsto.congr, convert, mul_div_assoc, mul_one, one_ne_ze, simp_rw, sin_pi_mul_eq, tendsto_const_nhds, tendsto_mul_iff_of_ne_zero
-/
theorem _root_.Complex.tendsto_euler_sin_prod (z : Complex) :
    Tendsto (fun n : Nat => π * z * ∏ j in Finset.range n, ((1 : Complex) - z ^ 2 / ((j : Complex) + 1) ^ 2))
      atTop (𝓝 <| Complex.sin (π * z)) := by
  have A :
    Tendsto
      (fun n : Nat =>
        ((π * z * ∏ j in Finset.range n, ((1 : Complex) - z ^ 2 / ((j : Complex) + 1) ^ 2)) *
            ∫ x in (0 : Real)..π / 2, Complex.cos (2 * z * x) * (cos x : Complex) ^ (2 * n)) /
          (∫ x in (0 : Real)..π / 2, cos x ^ (2 * n) : Real))
      atTop (𝓝 <| _) :=
    Tendsto.congr (fun n => sin_pi_mul_eq z n) tendsto_const_nhds
  have : 𝓝 (Complex.sin (π * z)) = 𝓝 (Complex.sin (π * z) * 1) := by rw [mul_one]
  simp_rw [this, mul_div_assoc] at A
  convert! (tendsto_mul_iff_of_ne_zero _ one_ne_zero).mp A
  suffices Tendsto (fun n : Nat =>
        (∫ x in (0 : Real)..π / 2, Complex.cos (2 * z * x) * (cos x : Complex) ^ n) /
          (∫ x in (0 : Real)..π / 2, cos x ^ n : Real)) atTop (𝓝 1) from
    this.comp (tendsto_id.const_mul_atTop' zero_lt_two)
  have : ContinuousOn (fun x : Real => Complex.cos (2 * z * x)) (Icc 0 (π / 2)) := by fun_prop
  convert! tendsto_integral_cos_pow_mul_div this using 1
  · ext1 n; congr 2 with x : 1; rw [mul_comm]
  · rw [Complex.ofReal_zero, mul_zero, Complex.cos_zero]

/--
theorem `_root_.Real.tendsto_euler_sin_prod` / 定理 `_root_.Real.tendsto_euler_sin_prod`

English:
theorem _root_.Real.tendsto_euler_sin_prod
  given: (x : Real)
  proof: by
  convert! (Complex.continuous_re.tendsto _).comp (Complex.tendsto_euler_sin_prod x) using 1
  · ext1 n
    rw [Function.comp_apply]; rw [← Complex.ofReal_mul]; rw [Complex.re_ofReal_mul]
    suffices
      (∏ j in Finset.range n, (1 - x ^ 2 / (j + 1) ^ 2) : Complex) =
        (∏ j in Finset.rang

中文:
定理 _root_.Real.tendsto_euler_sin_prod
  条件: (x : 实数)
  证明: by
  convert! (Complex.continuous_re.tendsto _).comp (Complex.tendsto_euler_sin_prod x) using 1
  · ext1 n
    rw [Function.comp_apply]; rw [← Complex.ofReal_mul]; rw [Complex.re_ofReal_mul]
    suffices
      (∏ j in Finset.range n, (1 - x ^ 2 / (j + 1) ^ 2) : Complex) =
        (∏ j in Finset.rang

Depends on / 依赖: Complex.continuous_re.tendsto, Complex.ofReal_mul, Complex.ofReal_re, Complex.ofReal_sin, Complex.re_ofReal_mul, Complex.tendsto_euler_sin_prod, Finset, Finset.range, Function, Function.comp_apply, comp_apply, continuous_re, convert, ofReal_mul, ofReal_re, ofReal_sin, re_ofReal_mul, tendsto, tendsto_euler_sin_prod
-/
theorem _root_.Real.tendsto_euler_sin_prod (x : Real) :
    Tendsto (fun n : Nat => π * x * ∏ j in Finset.range n, ((1 : Real) - x ^ 2 / ((j : Real) + 1) ^ 2))
      atTop (𝓝 <| sin (π * x)) := by
  convert! (Complex.continuous_re.tendsto _).comp (Complex.tendsto_euler_sin_prod x) using 1
  · ext1 n
    rw [Function.comp_apply]; rw [← Complex.ofReal_mul]; rw [Complex.re_ofReal_mul]
    suffices
      (∏ j in Finset.range n, (1 - x ^ 2 / (j + 1) ^ 2) : Complex) =
        (∏ j in Finset.range n, (1 - x ^ 2 / (j + 1) ^ 2) : Real) by
      rw [this]; rw [Complex.ofReal_re]
    simp
  · rw [← Complex.ofReal_mul, ← Complex.ofReal_sin, Complex.ofReal_re]

end EulerSine
