/-
Copyright (c) 2021 Hanting Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hanting Zhang
-/
module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! # The Wallis formula for Pi

This file establishes the Wallis product for `π` (`Real.tendsto_prod_pi_div_two`). Our proof is
largely about analyzing the behaviour of the sequence `∫ x in 0..π, sin x ^ n` as `n → ∞`.
See: https://en.wikipedia.org/wiki/Wallis_product

The proof can be broken down into two pieces. The first step (carried out in
`Mathlib/Analysis/SpecialFunctions/Integrals/Basic.lean`) is to use repeated integration by parts to
obtain an explicit formula for this integral, which is rational if `n` is odd and a rational
multiple of `π` if `n` is even.

The second step, carried out here, is to estimate the ratio
`∫ (x : ℝ) in 0..π, sin x ^ (2 * k + 1) / ∫ (x : ℝ) in 0..π, sin x ^ (2 * k)` and prove that
it converges to one using the squeeze theorem. The final product for `π` is obtained after some
algebraic manipulation.

## Main statements

* `Real.Wallis.W`: the product of the first `k` terms in Wallis' formula for `π`.
* `Real.Wallis.W_eq_integral_sin_pow_div_integral_sin_pow`: express `W n` as a ratio of integrals.
* `Real.Wallis.W_le` and `Real.Wallis.le_W`: upper and lower bounds for `W n`.
* `Real.tendsto_prod_pi_div_two`: the Wallis product formula.
-/

@[expose] public section


open scoped Real Topology Nat

open Filter Finset intervalIntegral

namespace Real

namespace Wallis


/--
Definition of `W` / `W` 的定义

English:
definition W
  signature: (k : Nat)
  body: ∏ i in range k, (2 * i + 2) / (2 * i + 1) * ((2 * i + 2) / (2 * i + 3))

中文:
定义 W
  签名: (k : 自然数)
  定义体: ∏ i in range k, (2 * i + 2) / (2 * i + 1) * ((2 * i + 2) / (2 * i + 3))
-/
noncomputable def W (k : Nat) : Real :=
  ∏ i in range k, (2 * i + 2) / (2 * i + 1) * ((2 * i + 2) / (2 * i + 3))

/--
theorem `W_succ` / 定理 `W_succ`

English:
theorem W_succ
  given: (k : Nat)
  proof: prod_range_succ _ _

中文:
定理 W_succ
  条件: (k : 自然数)
  证明: prod_range_succ _ _

Depends on / 依赖: prod_range_succ
-/
theorem W_succ (k : Nat) :
    W (k + 1) = W k * ((2 * k + 2) / (2 * k + 1) * ((2 * k + 2) / (2 * k + 3))) :=
  prod_range_succ _ _

/--
theorem `W_pos` / 定理 `W_pos`

English:
theorem W_pos
  given: (k : Nat)
  statement: 0 < W k
  proof: by
  induction k with
  | zero => unfold W; simp
  | succ k hk =>
    rw [W_succ]
    refine mul_pos hk (mul_pos (div_pos ?_ ?_) (div_pos ?_ ?_)) <;> positivity

中文:
定理 W_pos
  条件: (k : 自然数)
  结论: 0 < W k
  证明: by
  induction k with
  | zero => unfold W; simp
  | succ k hk =>
    rw [W_succ]
    refine mul_pos hk (mul_pos (div_pos ?_ ?_) (div_pos ?_ ?_)) <;> positivity

Depends on / 依赖: W_succ, div_pos, mul_pos
-/
theorem W_pos (k : Nat) : 0 < W k := by
  induction k with
  | zero => unfold W; simp
  | succ k hk =>
    rw [W_succ]
    refine mul_pos hk (mul_pos (div_pos ?_ ?_) (div_pos ?_ ?_)) <;> positivity

/--
theorem `W_eq_factorial_ratio` / 定理 `W_eq_factorial_ratio`

English:
theorem W_eq_factorial_ratio
  given: (n : Nat)
  proof: by
  induction n with
  | zero =>
    simp only [W, prod_range_zero, Nat.factorial_zero, mul_zero, pow_zero]
    norm_num
  | succ n IH =>
    unfold W at IH ⊢
    rw [prod_range_succ]; rw [IH]; rw [_root_.div_mul_div_comm]; rw [_root_.div_mul_div_comm]
    refine (div_eq_div_iff ?_ ?_).mpr ?_
    a

中文:
定理 W_eq_factorial_ratio
  条件: (n : 自然数)
  证明: by
  induction n with
  | zero =>
    simp only [W, prod_range_zero, Nat.factorial_zero, mul_zero, pow_zero]
    norm_num
  | succ n IH =>
    unfold W at IH ⊢
    rw [prod_range_succ]; rw [IH]; rw [_root_.div_mul_div_comm]; rw [_root_.div_mul_div_comm]
    refine (div_eq_div_iff ?_ ?_).mpr ?_
    a

Depends on / 依赖: Nat.factorial_succ, Nat.factorial_zero, Nat.mul_succ, _root_, _root_.div_mul_div_comm, any_goals, div_eq_div_iff, div_mul_div_comm, factorial_succ, factorial_zero, mul_succ, mul_zero, ne_of_gt, pow_succ, pow_zero, prod_range_succ, prod_range_zero, ring_nf, simp_rw
-/
theorem W_eq_factorial_ratio (n : Nat) :
    W n = 2 ^ (4 * n) * n ! ^ 4 / ((2 * n)! ^ 2 * (2 * n + 1)) := by
  induction n with
  | zero =>
    simp only [W, prod_range_zero, Nat.factorial_zero, mul_zero, pow_zero]
    norm_num
  | succ n IH =>
    unfold W at IH ⊢
    rw [prod_range_succ]; rw [IH]; rw [_root_.div_mul_div_comm]; rw [_root_.div_mul_div_comm]
    refine (div_eq_div_iff ?_ ?_).mpr ?_
    any_goals exact ne_of_gt (by positivity)
    simp_rw [Nat.mul_succ, Nat.factorial_succ, pow_succ]
    push_cast
    ring_nf

/--
theorem `W_eq_integral_sin_pow_div_integral_sin_pow` / 定理 `W_eq_integral_sin_pow_div_integral_sin_pow`

English:
theorem W_eq_integral_sin_pow_div_integral_sin_pow
  given: (k : Nat)
  statement: (π / 2)⁻¹ * W k =
  proof: by
  rw [integral_sin_pow_even]; rw [integral_sin_pow_odd]; rw [mul_div_mul_comm]; rw [← prod_div_distrib]; rw [inv_div]
  simp_rw [div_div_div_comm, div_div_eq_mul_div, mul_div_assoc]
  rfl

中文:
定理 W_eq_integral_sin_pow_div_integral_sin_pow
  条件: (k : 自然数)
  结论: (π / 2)⁻¹ * W k =
  证明: by
  rw [integral_sin_pow_even]; rw [integral_sin_pow_odd]; rw [mul_div_mul_comm]; rw [← prod_div_distrib]; rw [inv_div]
  simp_rw [div_div_div_comm, div_div_eq_mul_div, mul_div_assoc]
  rfl

Depends on / 依赖: div_div_div_comm, div_div_eq_mul_div, integral_sin_pow_even, integral_sin_pow_odd, inv_div, mul_div_assoc, mul_div_mul_comm, prod_div_distrib, simp_rw
-/
theorem W_eq_integral_sin_pow_div_integral_sin_pow (k : Nat) : (π / 2)⁻¹ * W k =
    (∫ x : Real in 0..π, sin x ^ (2 * k + 1)) / ∫ x : Real in 0..π, sin x ^ (2 * k) := by
  rw [integral_sin_pow_even]; rw [integral_sin_pow_odd]; rw [mul_div_mul_comm]; rw [← prod_div_distrib]; rw [inv_div]
  simp_rw [div_div_div_comm, div_div_eq_mul_div, mul_div_assoc]
  rfl

/--
theorem `W_le` / 定理 `W_le`

English:
theorem W_le
  given: (k : Nat)
  statement: W k <= π / 2
  proof: by
  rw [← div_le_one pi_div_two_pos]; rw [div_eq_inv_mul]
  rw [W_eq_integral_sin_pow_div_integral_sin_pow]; rw [div_le_one (integral_sin_pow_pos _)]
  apply integral_sin_pow_succ_le

中文:
定理 W_le
  条件: (k : 自然数)
  结论: W k <= π / 2
  证明: by
  rw [← div_le_one pi_div_two_pos]; rw [div_eq_inv_mul]
  rw [W_eq_integral_sin_pow_div_integral_sin_pow]; rw [div_le_one (integral_sin_pow_pos _)]
  apply integral_sin_pow_succ_le

Depends on / 依赖: W_eq_integral_sin_pow_div_integral_sin_pow, div_eq_inv_mul, div_le_one, integral_sin_pow_pos, integral_sin_pow_succ_le, pi_div_two_pos
-/
theorem W_le (k : Nat) : W k <= π / 2 := by
  rw [← div_le_one pi_div_two_pos]; rw [div_eq_inv_mul]
  rw [W_eq_integral_sin_pow_div_integral_sin_pow]; rw [div_le_one (integral_sin_pow_pos _)]
  apply integral_sin_pow_succ_le

/--
theorem `le_W` / 定理 `le_W`

English:
theorem le_W
  given: (k : Nat)
  statement: ((2 : Real) * k + 1) / (2 * k + 2) * (π / 2) <= W k
  proof: by
  rw [← le_div_iff₀ pi_div_two_pos]; rw [div_eq_inv_mul (W k) _]
  rw [W_eq_integral_sin_pow_div_integral_sin_pow]; rw [le_div_iff₀ (integral_sin_pow_pos _)]
  convert! integral_sin_pow_succ_le (2 * k + 1)
  rw [integral_sin_pow (2 * k)]
  simp

中文:
定理 le_W
  条件: (k : 自然数)
  结论: ((2 : 实数) * k + 1) / (2 * k + 2) * (π / 2) <= W k
  证明: by
  rw [← le_div_iff₀ pi_div_two_pos]; rw [div_eq_inv_mul (W k) _]
  rw [W_eq_integral_sin_pow_div_integral_sin_pow]; rw [le_div_iff₀ (integral_sin_pow_pos _)]
  convert! integral_sin_pow_succ_le (2 * k + 1)
  rw [integral_sin_pow (2 * k)]
  simp

Depends on / 依赖: W_eq_integral_sin_pow_div_integral_sin_pow, convert, div_eq_inv_mul, integral_sin_pow, integral_sin_pow_pos, integral_sin_pow_succ_le, pi_div_two_pos
-/
theorem le_W (k : Nat) : ((2 : Real) * k + 1) / (2 * k + 2) * (π / 2) <= W k := by
  rw [← le_div_iff₀ pi_div_two_pos]; rw [div_eq_inv_mul (W k) _]
  rw [W_eq_integral_sin_pow_div_integral_sin_pow]; rw [le_div_iff₀ (integral_sin_pow_pos _)]
  convert! integral_sin_pow_succ_le (2 * k + 1)
  rw [integral_sin_pow (2 * k)]
  simp

/--
theorem `tendsto_W_nhds_pi_div_two` / 定理 `tendsto_W_nhds_pi_div_two`

English:
theorem tendsto_W_nhds_pi_div_two
  statement: Tendsto W atTop (𝓝 <| π / 2)
  proof: by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le ?_ tendsto_const_nhds le_W W_le
  have : 𝓝 (π / 2) = 𝓝 ((1 - 0) * (π / 2)) := by rw [sub_zero, one_mul]
  rw [this]
  refine Tendsto.mul ?_ tendsto_const_nhds
  have h : forall n : Nat, ((2 : Real) * n + 1) / (2 * n + 2) = 1 - 1 / (2 * n + 2) := 

中文:
定理 tendsto_W_nhds_pi_div_two
  结论: Tendsto W atTop (𝓝 <| π / 2)
  证明: by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le ?_ tendsto_const_nhds le_W W_le
  have : 𝓝 (π / 2) = 𝓝 ((1 - 0) * (π / 2)) := by rw [sub_zero, one_mul]
  rw [this]
  refine Tendsto.mul ?_ tendsto_const_nhds
  have h : forall n : Nat, ((2 : Real) * n + 1) / (2 * n + 2) = 1 - 1 / (2 * n + 2) := 

Depends on / 依赖: Nat.cast_nonneg, Tendsto, Tendsto.mul, W_le, add_pos_of_nonneg_of_pos, cast_nonneg, div_atTop, le_W, mul_nonneg, ne_of_gt, one_mul, simp_rw, sub_div, sub_zero, tendsto_const_nhds, tendsto_const_nhds.div_atTop, tendsto_of_tendsto_of_tendsto_of_le_of_le, two_pos
-/
theorem tendsto_W_nhds_pi_div_two : Tendsto W atTop (𝓝 <| π / 2) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le ?_ tendsto_const_nhds le_W W_le
  have : 𝓝 (π / 2) = 𝓝 ((1 - 0) * (π / 2)) := by rw [sub_zero, one_mul]
  rw [this]
  refine Tendsto.mul ?_ tendsto_const_nhds
  have h : forall n : Nat, ((2 : Real) * n + 1) / (2 * n + 2) = 1 - 1 / (2 * n + 2) := by
    intro n
    rw [sub_div' (ne_of_gt (add_pos_of_nonneg_of_pos (mul_nonneg
      (two_pos : 0 < (2 : Real)).le (Nat.cast_nonneg _)) two_pos))]; rw [one_mul]
    congr 1; ring
  simp_rw [h]
  refine (tendsto_const_nhds.div_atTop ?_).const_sub _
  refine Tendsto.atTop_add ?_ tendsto_const_nhds
  exact tendsto_natCast_atTop_atTop.const_mul_atTop two_pos

end Wallis

end Real

/--
theorem `Real.tendsto_prod_pi_div_two` / 定理 `Real.tendsto_prod_pi_div_two`

English:
theorem Real.tendsto_prod_pi_div_two
  proof: Real.Wallis.tendsto_W_nhds_pi_div_two

中文:
定理 Real.tendsto_prod_pi_div_two
  证明: Real.Wallis.tendsto_W_nhds_pi_div_two

Depends on / 依赖: Real.Wallis.tendsto_W_nhds_pi_div_two, Wallis, tendsto_W_nhds_pi_div_two
-/
theorem Real.tendsto_prod_pi_div_two :
    Tendsto (fun k => ∏ i in range k, ((2 : Real) * i + 2) / (2 * i + 1) * ((2 * i + 2) / (2 * i + 3)))
      atTop (𝓝 (π / 2)) :=
  Real.Wallis.tendsto_W_nhds_pi_div_two
