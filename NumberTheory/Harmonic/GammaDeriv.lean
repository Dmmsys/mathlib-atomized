/-
Copyright (c) 2024 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
module

public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.NumberTheory.Harmonic.EulerMascheroni

/-!
# Derivative of Γ at positive integers

We prove the formula for the derivative of `Real.Gamma` at a positive integer:

`deriv Real.Gamma (n + 1) = Nat.factorial n * (-Real.eulerMascheroniConstant + harmonic n)`

-/

public section

open Nat Set Filter Topology

local notation "γ" => Real.eulerMascheroniConstant

namespace Real

/--
lemma `deriv_Gamma_nat` / 引理 `deriv_Gamma_nat`

English:
lemma deriv_Gamma_nat
  given: (n : Nat)
  proof: by
  /- This follows from two properties of the function `f n = log (Gamma n)`:
  firstly, the elementary computation that `deriv f (n + 1) = deriv f n + 1 / n`, so that
  `deriv f n = deriv f 1 + harmonic n`; secondly, the convexity of `f` (the Bohr-Mollerup theorem),
  which shows that `deriv f n` is `log n + o(1)` as `n → ∞`. -/
  let f := log ∘ Gamma
  -- First reduce to computing derivative of `log ∘ Gamma`.
  suffices deriv (log ∘ Gamma) (n + 1) = -γ + harmonic n by
    rwa [Function.comp_def, deriv.log (differentiableAt_Gamma (fun m => by linarith))
      (by positivity), Gamma_nat_eq_factorial, div_eq_iff_mul_eq (by positivity),
      mul_comm, Eq.comm] at this
  have hc : ConvexOn Real (Ioi 0) f := convexOn_log_Gamma
  have h_rec (x : Real) (hx : 0 < x) : f (x + 1) = f x + log x := by simp only [f, Function.comp_apply,
      Gamma_add_one hx.ne', log_mul hx.ne' (Gamma_pos_of_pos hx).ne', add_comm]
  have hder {x : Real} (hx : 0 < x) : DifferentiableAt Real f x := by
    refine ((differentiableAt_Gamma ?_).log (Gamma_ne_zero ?_)) <;>
    exact fun m => ne_of_gt (by linarith)
  -- Express derivative at general `n` in terms of value at `1` using recurrence relation
  have hder_rec (x : Real) (hx : 0 < x) : deriv f (x + 1) = deriv f x + 1 / x := by
    rw [← deriv_comp_add_const]; rw [one_div]; rw [← deriv_log]; rw [← deriv_add (hder <| by positivity) (differentiableAt_log hx.ne')]
    apply EventuallyEq.deriv_eq
    filter_upwards [eventually_gt_nhds hx] using h_rec
  have hder_nat (n : Nat) : deriv f (n + 1) = deriv f 1 + harmonic n := by
    induction n with
    | zero => simp
    | succ n hn =>
      rw [cast_succ]; rw [hder_rec (n + 1) (by positivity)]; rw [hn]; rw [harmonic_succ]
      push_cast
      ring
  suffices -deriv f 1 = γ by rw [hder_nat n, ← this, neg_neg]
  -- Use convexity to show derivative of `f` at `n + 1` is between `log n` and `log (n + 1)`
  have derivLB (n : Nat) (hn : 0 < n) : log n <= deriv f (n + 1) := by
refine (le_of_eq ?_).trans hc.slope_le_deriv (mem_Ioi.mpr <| Nat.cast_pos.mpr hn)
      (by positivity : _ < (_ : Real)) (by linarith) (hder <| by positivity)
    rw [slope_def_field]; rw [show n + 1 - n = (1 : Real) by ring]; rw [div_one]; rw [h_rec n (by positivity)]; rw [add_sub_cancel_left]
  have derivUB (n : Nat) : deriv f (n + 1) <= log (n + 1) := by
    refine (hc.deriv_le_slope (by positivity : (0 : Real) < n + 1) (by positivity : (0 : Real) < n + 2)
        (by linarith) (hder <| by positivity)).trans (le_of_eq ?_)
    rw [slope_def_field]; rw [show n + 2 - (n + 1) = (1 : Real) by ring]; rw [div_one]; rw [show n + 2 = (n + 1) + (1 : Real) by ring]; rw [h_rec (n + 1) (by positivity)]; rw [add_sub_cancel_left]
  -- deduce `-deriv f 1` is bounded above + below by sequences which both tend to `γ`
  apply le_antisymm
  · apply ge_of_tendsto tendsto_harmonic_sub_log
    filter_upwards [eventually_gt_atTop 0] with n hn
    rw [le_sub_iff_add_le']; rw [← sub_eq_add_neg]; rw [sub_le_iff_le_add']; rw [← hder_nat]
    exact derivLB n hn
  · apply le_of_tendsto tendsto_harmonic_sub_log_add_one
    filter_upwards with n
    rw [sub_le_iff_le_add']; rw [← sub_eq_add_neg]; rw [le_sub_iff_add_le']; rw [← hder_nat]
    exact derivUB n

中文:
引理 deriv_Gamma_nat
  条件: (n : 自然数)
  证明: by
  /- This follows from two properties of the function `f n = log (Gamma n)`:
  firstly, the elementary computation that `deriv f (n + 1) = deriv f n + 1 / n`, so that
  `deriv f n = deriv f 1 + harmonic n`; secondly, the convexity of `f` (the Bohr-Mollerup theorem),
  which shows that `deriv f n` is `log n + o(1)` as `n → ∞`. -/
  let f := log ∘ Gamma
  -- First reduce to computing derivative of `log ∘ Gamma`.
  suffices deriv (log ∘ Gamma) (n + 1) = -γ + harmonic n by
    rwa [Function.comp_def, deriv.log (differentiableAt_Gamma (fun m => by linarith))
      (by positivity), Gamma_nat_eq_factorial, div_eq_iff_mul_eq (by positivity),
      mul_comm, Eq.comm] at this
  have hc : ConvexOn Real (Ioi 0) f := convexOn_log_Gamma
  have h_rec (x : Real) (hx : 0 < x) : f (x + 1) = f x + log x := by simp only [f, Function.comp_apply,
      Gamma_add_one hx.ne', log_mul hx.ne' (Gamma_pos_of_pos hx).ne', add_comm]
  have hder {x : Real} (hx : 0 < x) : DifferentiableAt Real f x := by
    refine ((differentiableAt_Gamma ?_).log (Gamma_ne_zero ?_)) <;>
    exact fun m => ne_of_gt (by linarith)
  -- Express derivative at general `n` in terms of value at `1` using recurrence relation
  have hder_rec (x : Real) (hx : 0 < x) : deriv f (x + 1) = deriv f x + 1 / x := by
    rw [← deriv_comp_add_const]; rw [one_div]; rw [← deriv_log]; rw [← deriv_add (hder <| by positivity) (differentiableAt_log hx.ne')]
    apply EventuallyEq.deriv_eq
    filter_upwards [eventually_gt_nhds hx] using h_rec
  have hder_nat (n : Nat) : deriv f (n + 1) = deriv f 1 + harmonic n := by
    induction n with
    | zero => simp
    | succ n hn =>
      rw [cast_succ]; rw [hder_rec (n + 1) (by positivity)]; rw [hn]; rw [harmonic_succ]
      push_cast
      ring
  suffices -deriv f 1 = γ by rw [hder_nat n, ← this, neg_neg]
  -- Use convexity to show derivative of `f` at `n + 1` is between `log n` and `log (n + 1)`
  have derivLB (n : Nat) (hn : 0 < n) : log n <= deriv f (n + 1) := by
refine (le_of_eq ?_).trans hc.slope_le_deriv (mem_Ioi.mpr <| Nat.cast_pos.mpr hn)
      (by positivity : _ < (_ : Real)) (by linarith) (hder <| by positivity)
    rw [slope_def_field]; rw [show n + 1 - n = (1 : Real) by ring]; rw [div_one]; rw [h_rec n (by positivity)]; rw [add_sub_cancel_left]
  have derivUB (n : Nat) : deriv f (n + 1) <= log (n + 1) := by
    refine (hc.deriv_le_slope (by positivity : (0 : Real) < n + 1) (by positivity : (0 : Real) < n + 2)
        (by linarith) (hder <| by positivity)).trans (le_of_eq ?_)
    rw [slope_def_field]; rw [show n + 2 - (n + 1) = (1 : Real) by ring]; rw [div_one]; rw [show n + 2 = (n + 1) + (1 : Real) by ring]; rw [h_rec (n + 1) (by positivity)]; rw [add_sub_cancel_left]
  -- deduce `-deriv f 1` is bounded above + below by sequences which both tend to `γ`
  apply le_antisymm
  · apply ge_of_tendsto tendsto_harmonic_sub_log
    filter_upwards [eventually_gt_atTop 0] with n hn
    rw [le_sub_iff_add_le']; rw [← sub_eq_add_neg]; rw [sub_le_iff_le_add']; rw [← hder_nat]
    exact derivLB n hn
  · apply le_of_tendsto tendsto_harmonic_sub_log_add_one
    filter_upwards with n
    rw [sub_le_iff_le_add']; rw [← sub_eq_add_neg]; rw [le_sub_iff_add_le']; rw [← hder_nat]
    exact derivUB n
-/
lemma deriv_Gamma_nat (n : Nat) :
    deriv Gamma (n + 1) = n ! * (-γ + harmonic n) := by
  /- This follows from two properties of the function `f n = log (Gamma n)`:
  firstly, the elementary computation that `deriv f (n + 1) = deriv f n + 1 / n`, so that
  `deriv f n = deriv f 1 + harmonic n`; secondly, the convexity of `f` (the Bohr-Mollerup theorem),
  which shows that `deriv f n` is `log n + o(1)` as `n → ∞`. -/
  let f := log ∘ Gamma
  -- First reduce to computing derivative of `log ∘ Gamma`.
  suffices deriv (log ∘ Gamma) (n + 1) = -γ + harmonic n by
    rwa [Function.comp_def, deriv.log (differentiableAt_Gamma (fun m => by linarith))
      (by positivity), Gamma_nat_eq_factorial, div_eq_iff_mul_eq (by positivity),
      mul_comm, Eq.comm] at this
  have hc : ConvexOn Real (Ioi 0) f := convexOn_log_Gamma
  have h_rec (x : Real) (hx : 0 < x) : f (x + 1) = f x + log x := by simp only [f, Function.comp_apply,
      Gamma_add_one hx.ne', log_mul hx.ne' (Gamma_pos_of_pos hx).ne', add_comm]
  have hder {x : Real} (hx : 0 < x) : DifferentiableAt Real f x := by
    refine ((differentiableAt_Gamma ?_).log (Gamma_ne_zero ?_)) <;>
    exact fun m => ne_of_gt (by linarith)
  -- Express derivative at general `n` in terms of value at `1` using recurrence relation
  have hder_rec (x : Real) (hx : 0 < x) : deriv f (x + 1) = deriv f x + 1 / x := by
    rw [← deriv_comp_add_const]; rw [one_div]; rw [← deriv_log]; rw [← deriv_add (hder <| by positivity) (differentiableAt_log hx.ne')]
    apply EventuallyEq.deriv_eq
    filter_upwards [eventually_gt_nhds hx] using h_rec
  have hder_nat (n : Nat) : deriv f (n + 1) = deriv f 1 + harmonic n := by
    induction n with
    | zero => simp
    | succ n hn =>
      rw [cast_succ]; rw [hder_rec (n + 1) (by positivity)]; rw [hn]; rw [harmonic_succ]
      push_cast
      ring
  suffices -deriv f 1 = γ by rw [hder_nat n, ← this, neg_neg]
  -- Use convexity to show derivative of `f` at `n + 1` is between `log n` and `log (n + 1)`
  have derivLB (n : Nat) (hn : 0 < n) : log n <= deriv f (n + 1) := by
refine (le_of_eq ?_).trans hc.slope_le_deriv (mem_Ioi.mpr <| Nat.cast_pos.mpr hn)
      (by positivity : _ < (_ : Real)) (by linarith) (hder <| by positivity)
    rw [slope_def_field]; rw [show n + 1 - n = (1 : Real) by ring]; rw [div_one]; rw [h_rec n (by positivity)]; rw [add_sub_cancel_left]
  have derivUB (n : Nat) : deriv f (n + 1) <= log (n + 1) := by
    refine (hc.deriv_le_slope (by positivity : (0 : Real) < n + 1) (by positivity : (0 : Real) < n + 2)
        (by linarith) (hder <| by positivity)).trans (le_of_eq ?_)
    rw [slope_def_field]; rw [show n + 2 - (n + 1) = (1 : Real) by ring]; rw [div_one]; rw [show n + 2 = (n + 1) + (1 : Real) by ring]; rw [h_rec (n + 1) (by positivity)]; rw [add_sub_cancel_left]
  -- deduce `-deriv f 1` is bounded above + below by sequences which both tend to `γ`
  apply le_antisymm
  · apply ge_of_tendsto tendsto_harmonic_sub_log
    filter_upwards [eventually_gt_atTop 0] with n hn
    rw [le_sub_iff_add_le']; rw [← sub_eq_add_neg]; rw [sub_le_iff_le_add']; rw [← hder_nat]
    exact derivLB n hn
  · apply le_of_tendsto tendsto_harmonic_sub_log_add_one
    filter_upwards with n
    rw [sub_le_iff_le_add']; rw [← sub_eq_add_neg]; rw [le_sub_iff_add_le']; rw [← hder_nat]
    exact derivUB n


/--
lemma `hasDerivAt_Gamma_nat` / 引理 `hasDerivAt_Gamma_nat`

English:
lemma hasDerivAt_Gamma_nat
  given: (n : Nat)
  proof: (deriv_Gamma_nat n).symm ▸
    (differentiableAt_Gamma fun m => (by linarith : (n : Real) + 1 != -m)).hasDerivAt

中文:
引理 hasDerivAt_Gamma_nat
  条件: (n : 自然数)
  证明: (deriv_Gamma_nat n).symm ▸
    (differentiableAt_Gamma fun m => (by linarith : (n : Real) + 1 != -m)).hasDerivAt

Depends on / 依赖: deriv_Gamma_nat, differentiableAt_Gamma, hasDerivAt
-/
lemma hasDerivAt_Gamma_nat (n : Nat) :
    HasDerivAt Gamma (n ! * (-γ + harmonic n)) (n + 1) :=
  (deriv_Gamma_nat n).symm ▸
    (differentiableAt_Gamma fun m => (by linarith : (n : Real) + 1 != -m)).hasDerivAt

/--
lemma `eulerMascheroniConstant_eq_neg_deriv` / 引理 `eulerMascheroniConstant_eq_neg_deriv`

English:
lemma eulerMascheroniConstant_eq_neg_deriv
  statement: γ = -deriv Gamma 1
  proof: by
  rw [show (1 : Real) = ↑(0 : Nat) + 1 by simp]; rw [deriv_Gamma_nat 0]
  simp

中文:
引理 eulerMascheroniConstant_eq_neg_deriv
  结论: γ = -deriv Gamma 1
  证明: by
  rw [show (1 : Real) = ↑(0 : Nat) + 1 by simp]; rw [deriv_Gamma_nat 0]
  simp

Depends on / 依赖: deriv_Gamma_nat
-/
lemma eulerMascheroniConstant_eq_neg_deriv : γ = -deriv Gamma 1 := by
  rw [show (1 : Real) = ↑(0 : Nat) + 1 by simp]; rw [deriv_Gamma_nat 0]
  simp

/--
lemma `hasDerivAt_Gamma_one` / 引理 `hasDerivAt_Gamma_one`

English:
lemma hasDerivAt_Gamma_one
  statement: HasDerivAt Gamma (-γ) 1
  proof: by
  simpa only [factorial_zero, cast_one, harmonic_zero, Rat.cast_zero, add_zero, mul_neg, one_mul,
    cast_zero, zero_add] using hasDerivAt_Gamma_nat 0

中文:
引理 hasDerivAt_Gamma_one
  结论: 在点处可导 Gamma (-γ) 1
  证明: by
  simpa only [factorial_zero, cast_one, harmonic_zero, Rat.cast_zero, add_zero, mul_neg, one_mul,
    cast_zero, zero_add] using hasDerivAt_Gamma_nat 0

Depends on / 依赖: Rat.cast_zero, add_zero, cast_one, cast_zero, factorial_zero, harmonic_zero, hasDerivAt_Gamma_nat, mul_neg, one_mul, zero_add
-/
lemma hasDerivAt_Gamma_one : HasDerivAt Gamma (-γ) 1 := by
  simpa only [factorial_zero, cast_one, harmonic_zero, Rat.cast_zero, add_zero, mul_neg, one_mul,
    cast_zero, zero_add] using hasDerivAt_Gamma_nat 0

/--
lemma `hasDerivAt_Gamma_one_half` / 引理 `hasDerivAt_Gamma_one_half`

English:
lemma hasDerivAt_Gamma_one_half
  statement: HasDerivAt Gamma (-√π * (γ + 2 * log 2)) (1 / 2)
  proof: by
  have h_diff {s : Real} (hs : 0 < s) : DifferentiableAt Real Gamma s :=
    differentiableAt_Gamma fun m => ((neg_nonpos.mpr m.cast_nonneg).trans_lt hs).ne'
  have h_diff' {s : Real} (hs : 0 < s) : DifferentiableAt Real (fun s => Gamma (2 * s)) s :=
    .comp (g := Gamma) _ (h_diff <| mul_pos two_pos hs) (differentiableAt_id.const_mul _)
  refine (h_diff one_half_pos).hasDerivAt.congr_deriv ?_
  -- We calculate the deriv of Gamma at 1/2 using the doubling formula, since we already know
  -- the derivative of Gamma at 1.
  calc deriv Gamma (1 / 2)
  _ = (deriv (fun s => Gamma s * Gamma (s + 1 / 2)) (1 / 2)) + √π * γ := by
    rw [deriv_fun_mul]; rw [Gamma_one_half_eq]; rw [add_assoc]; rw [← mul_add]; rw [deriv_comp_add_const]; rw [(by norm_num : 1 / 2 + 1 / 2 = (1 : Real))]; rw [Gamma_one]; rw [mul_one]; rw [eulerMascheroniConstant_eq_neg_deriv]; rw [add_neg_cancel]; rw [mul_zero]; rw [add_zero]
    · apply h_diff; simp -- s = 1
    · exact ((h_diff (by simp)).hasDerivAt.comp_add_const).differentiableAt -- s = 1
  _ = (deriv (fun s => Gamma (2 * s) * 2 ^ (1 - 2 * s) * √π) (1 / 2)) + √π * γ := by
    rw [funext Gamma_mul_Gamma_add_half]
  _ = √π * (deriv (fun s => Gamma (2 * s) * 2 ^ (1 - 2 * s)) (1 / 2) + γ) := by
    rw [mul_comm √π]; rw [mul_comm √π]; rw [deriv_mul_const]; rw [add_mul]
    apply DifferentiableAt.mul
    · exact .comp (g := Gamma) _ (by apply h_diff; simp) -- s = 1
        (differentiableAt_id.const_mul _)
    · exact (differentiableAt_const _).rpow (by fun_prop) two_ne_zero
  _ = √π * (deriv (fun s => Gamma (2 * s)) (1 / 2) +
              deriv (fun s : Real => 2 ^ (1 - 2 * s)) (1 / 2) + γ) := by
    rw [deriv_fun_mul]
    · simp
    · exact h_diff' one_half_pos
    · exact DifferentiableAt.rpow (by fun_prop) (by fun_prop) two_ne_zero
  _ = √π * (-2 * γ + deriv (fun s : Real => 2 ^ (1 - 2 * s)) (1 / 2) + γ) := by
    congr 3
    change deriv (Gamma ∘ fun s => 2 * s) _ = _
    rw [deriv_comp]; rw [deriv_const_mul_id]; rw [mul_one_div]; rw [div_self two_ne_zero]
    · rw [mul_comm, hasDerivAt_Gamma_one.deriv, mul_neg, neg_mul]
    · apply h_diff; simp -- s = 1
    · fun_prop
  _ = √π * (-2 * γ + -(2 * log 2) + γ) := by
    congr 3
    apply HasDerivAt.deriv
    have := HasDerivAt.rpow (hasDerivAt_const (1 / 2 : Real) (2 : Real))
      (?_ : HasDerivAt (fun s : Real => 1 - 2 * s) (-2) (1 / 2)) two_pos
    · simpa
    simp_rw [mul_comm (2 : Real) _]
    apply HasDerivAt.const_sub
    exact hasDerivAt_mul_const (2 : Real)
  _ = -√π * (γ + 2 * log 2) := by ring

中文:
引理 hasDerivAt_Gamma_one_half
  结论: 在点处可导 Gamma (-√π * (γ + 2 * log 2)) (1 / 2)
  证明: by
  have h_diff {s : Real} (hs : 0 < s) : DifferentiableAt Real Gamma s :=
    differentiableAt_Gamma fun m => ((neg_nonpos.mpr m.cast_nonneg).trans_lt hs).ne'
  have h_diff' {s : Real} (hs : 0 < s) : DifferentiableAt Real (fun s => Gamma (2 * s)) s :=
    .comp (g := Gamma) _ (h_diff <| mul_pos two_pos hs) (differentiableAt_id.const_mul _)
  refine (h_diff one_half_pos).hasDerivAt.congr_deriv ?_
  -- We calculate the deriv of Gamma at 1/2 using the doubling formula, since we already know
  -- the derivative of Gamma at 1.
  calc deriv Gamma (1 / 2)
  _ = (deriv (fun s => Gamma s * Gamma (s + 1 / 2)) (1 / 2)) + √π * γ := by
    rw [deriv_fun_mul]; rw [Gamma_one_half_eq]; rw [add_assoc]; rw [← mul_add]; rw [deriv_comp_add_const]; rw [(by norm_num : 1 / 2 + 1 / 2 = (1 : Real))]; rw [Gamma_one]; rw [mul_one]; rw [eulerMascheroniConstant_eq_neg_deriv]; rw [add_neg_cancel]; rw [mul_zero]; rw [add_zero]
    · apply h_diff; simp -- s = 1
    · exact ((h_diff (by simp)).hasDerivAt.comp_add_const).differentiableAt -- s = 1
  _ = (deriv (fun s => Gamma (2 * s) * 2 ^ (1 - 2 * s) * √π) (1 / 2)) + √π * γ := by
    rw [funext Gamma_mul_Gamma_add_half]
  _ = √π * (deriv (fun s => Gamma (2 * s) * 2 ^ (1 - 2 * s)) (1 / 2) + γ) := by
    rw [mul_comm √π]; rw [mul_comm √π]; rw [deriv_mul_const]; rw [add_mul]
    apply DifferentiableAt.mul
    · exact .comp (g := Gamma) _ (by apply h_diff; simp) -- s = 1
        (differentiableAt_id.const_mul _)
    · exact (differentiableAt_const _).rpow (by fun_prop) two_ne_zero
  _ = √π * (deriv (fun s => Gamma (2 * s)) (1 / 2) +
              deriv (fun s : Real => 2 ^ (1 - 2 * s)) (1 / 2) + γ) := by
    rw [deriv_fun_mul]
    · simp
    · exact h_diff' one_half_pos
    · exact DifferentiableAt.rpow (by fun_prop) (by fun_prop) two_ne_zero
  _ = √π * (-2 * γ + deriv (fun s : Real => 2 ^ (1 - 2 * s)) (1 / 2) + γ) := by
    congr 3
    change deriv (Gamma ∘ fun s => 2 * s) _ = _
    rw [deriv_comp]; rw [deriv_const_mul_id]; rw [mul_one_div]; rw [div_self two_ne_zero]
    · rw [mul_comm, hasDerivAt_Gamma_one.deriv, mul_neg, neg_mul]
    · apply h_diff; simp -- s = 1
    · fun_prop
  _ = √π * (-2 * γ + -(2 * log 2) + γ) := by
    congr 3
    apply HasDerivAt.deriv
    have := HasDerivAt.rpow (hasDerivAt_const (1 / 2 : Real) (2 : Real))
      (?_ : HasDerivAt (fun s : Real => 1 - 2 * s) (-2) (1 / 2)) two_pos
    · simpa
    simp_rw [mul_comm (2 : Real) _]
    apply HasDerivAt.const_sub
    exact hasDerivAt_mul_const (2 : Real)
  _ = -√π * (γ + 2 * log 2) := by ring

Depends on / 依赖: DifferentiableAt, cast_nonneg, congr_deriv, const_mul, differentiableAt_Gamma, differentiableAt_id, differentiableAt_id.const_mul, h_diff, hasDerivAt, hasDerivAt.congr_deriv, m.cast_nonneg, mul_pos, neg_nonpos, neg_nonpos.mpr, one_half_pos, trans_lt, two_pos
-/
lemma hasDerivAt_Gamma_one_half : HasDerivAt Gamma (-√π * (γ + 2 * log 2)) (1 / 2) := by
  have h_diff {s : Real} (hs : 0 < s) : DifferentiableAt Real Gamma s :=
    differentiableAt_Gamma fun m => ((neg_nonpos.mpr m.cast_nonneg).trans_lt hs).ne'
  have h_diff' {s : Real} (hs : 0 < s) : DifferentiableAt Real (fun s => Gamma (2 * s)) s :=
    .comp (g := Gamma) _ (h_diff <| mul_pos two_pos hs) (differentiableAt_id.const_mul _)
  refine (h_diff one_half_pos).hasDerivAt.congr_deriv ?_
  -- We calculate the deriv of Gamma at 1/2 using the doubling formula, since we already know
  -- the derivative of Gamma at 1.
  calc deriv Gamma (1 / 2)
  _ = (deriv (fun s => Gamma s * Gamma (s + 1 / 2)) (1 / 2)) + √π * γ := by
    rw [deriv_fun_mul]; rw [Gamma_one_half_eq]; rw [add_assoc]; rw [← mul_add]; rw [deriv_comp_add_const]; rw [(by norm_num : 1 / 2 + 1 / 2 = (1 : Real))]; rw [Gamma_one]; rw [mul_one]; rw [eulerMascheroniConstant_eq_neg_deriv]; rw [add_neg_cancel]; rw [mul_zero]; rw [add_zero]
    · apply h_diff; simp -- s = 1
    · exact ((h_diff (by simp)).hasDerivAt.comp_add_const).differentiableAt -- s = 1
  _ = (deriv (fun s => Gamma (2 * s) * 2 ^ (1 - 2 * s) * √π) (1 / 2)) + √π * γ := by
    rw [funext Gamma_mul_Gamma_add_half]
  _ = √π * (deriv (fun s => Gamma (2 * s) * 2 ^ (1 - 2 * s)) (1 / 2) + γ) := by
    rw [mul_comm √π]; rw [mul_comm √π]; rw [deriv_mul_const]; rw [add_mul]
    apply DifferentiableAt.mul
    · exact .comp (g := Gamma) _ (by apply h_diff; simp) -- s = 1
        (differentiableAt_id.const_mul _)
    · exact (differentiableAt_const _).rpow (by fun_prop) two_ne_zero
  _ = √π * (deriv (fun s => Gamma (2 * s)) (1 / 2) +
              deriv (fun s : Real => 2 ^ (1 - 2 * s)) (1 / 2) + γ) := by
    rw [deriv_fun_mul]
    · simp
    · exact h_diff' one_half_pos
    · exact DifferentiableAt.rpow (by fun_prop) (by fun_prop) two_ne_zero
  _ = √π * (-2 * γ + deriv (fun s : Real => 2 ^ (1 - 2 * s)) (1 / 2) + γ) := by
    congr 3
    change deriv (Gamma ∘ fun s => 2 * s) _ = _
    rw [deriv_comp]; rw [deriv_const_mul_id]; rw [mul_one_div]; rw [div_self two_ne_zero]
    · rw [mul_comm, hasDerivAt_Gamma_one.deriv, mul_neg, neg_mul]
    · apply h_diff; simp -- s = 1
    · fun_prop
  _ = √π * (-2 * γ + -(2 * log 2) + γ) := by
    congr 3
    apply HasDerivAt.deriv
    have := HasDerivAt.rpow (hasDerivAt_const (1 / 2 : Real) (2 : Real))
      (?_ : HasDerivAt (fun s : Real => 1 - 2 * s) (-2) (1 / 2)) two_pos
    · simpa
    simp_rw [mul_comm (2 : Real) _]
    apply HasDerivAt.const_sub
    exact hasDerivAt_mul_const (2 : Real)
  _ = -√π * (γ + 2 * log 2) := by ring

end Real

namespace Complex

open scoped Real

/--
lemma `HasDerivAt.complex_of_real` / 引理 `HasDerivAt.complex_of_real`

English:
lemma HasDerivAt.complex_of_real
  statement: {f : Complex -> Complex} {g : Real -> Real} {g' s : Real}
  proof: by
  refine HasDerivAt.congr_deriv hf.hasDerivAt ?_
  rw [← (funext hfg ▸ hf.hasDerivAt.comp_ofReal.deriv :)]
  exact hg.ofReal_comp.deriv

中文:
引理 在点处可导.complex_of_real
  结论: {f : 复形 -> 复形} {g : 实数 -> 实数} {g' s : 实数}
  证明: by
  refine HasDerivAt.congr_deriv hf.hasDerivAt ?_
  rw [← (funext hfg ▸ hf.hasDerivAt.comp_ofReal.deriv :)]
  exact hg.ofReal_comp.deriv
-/
private lemma HasDerivAt.complex_of_real {f : Complex -> Complex} {g : Real -> Real} {g' s : Real}
    (hf : DifferentiableAt Complex f s) (hg : HasDerivAt g g' s) (hfg : forall s : Real, f ↑s = ↑(g s)) :
    HasDerivAt f ↑g' s := by
  refine HasDerivAt.congr_deriv hf.hasDerivAt ?_
  rw [← (funext hfg ▸ hf.hasDerivAt.comp_ofReal.deriv :)]
  exact hg.ofReal_comp.deriv

/--
lemma `differentiableAt_Gamma_nat_add_one` / 引理 `differentiableAt_Gamma_nat_add_one`

English:
lemma differentiableAt_Gamma_nat_add_one
  given: (n : Nat)
  proof: by
  refine differentiableAt_Gamma _ (fun m => ?_)
  simp only [Ne, ← ofReal_natCast, ← ofReal_one, ← ofReal_add, ← ofReal_neg, ofReal_inj,
    eq_neg_iff_add_eq_zero]
  positivity

中文:
引理 differentiableAt_Gamma_nat_add_one
  条件: (n : 自然数)
  证明: by
  refine differentiableAt_Gamma _ (fun m => ?_)
  simp only [Ne, ← ofReal_natCast, ← ofReal_one, ← ofReal_add, ← ofReal_neg, ofReal_inj,
    eq_neg_iff_add_eq_zero]
  positivity

Depends on / 依赖: differentiableAt_Gamma, eq_neg_iff_add_eq_zero, ofReal_add, ofReal_inj, ofReal_natCast, ofReal_neg, ofReal_one
-/
lemma differentiableAt_Gamma_nat_add_one (n : Nat) :
    DifferentiableAt Complex Gamma (n + 1) := by
  refine differentiableAt_Gamma _ (fun m => ?_)
  simp only [Ne, ← ofReal_natCast, ← ofReal_one, ← ofReal_add, ← ofReal_neg, ofReal_inj,
    eq_neg_iff_add_eq_zero]
  positivity

/--
lemma `hasDerivAt_Gamma_nat` / 引理 `hasDerivAt_Gamma_nat`

English:
lemma hasDerivAt_Gamma_nat
  given: (n : Nat)
  proof: by
  exact_mod_cast HasDerivAt.complex_of_real
    (by exact_mod_cast differentiableAt_Gamma_nat_add_one n)
    (Real.hasDerivAt_Gamma_nat n) Gamma_ofReal

中文:
引理 hasDerivAt_Gamma_nat
  条件: (n : 自然数)
  证明: by
  exact_mod_cast HasDerivAt.complex_of_real
    (by exact_mod_cast differentiableAt_Gamma_nat_add_one n)
    (Real.hasDerivAt_Gamma_nat n) Gamma_ofReal

Depends on / 依赖: Gamma_ofReal, HasDerivAt, HasDerivAt.complex_of_real, Real.hasDerivAt_Gamma_nat, complex_of_real, differentiableAt_Gamma_nat_add_one, hasDerivAt_Gamma_nat
-/
lemma hasDerivAt_Gamma_nat (n : Nat) :
    HasDerivAt Gamma (n ! * (-γ + harmonic n)) (n + 1) := by
  exact_mod_cast HasDerivAt.complex_of_real
    (by exact_mod_cast differentiableAt_Gamma_nat_add_one n)
    (Real.hasDerivAt_Gamma_nat n) Gamma_ofReal

/--
lemma `deriv_Gamma_nat` / 引理 `deriv_Gamma_nat`

English:
lemma deriv_Gamma_nat
  given: (n : Nat)
  proof: (hasDerivAt_Gamma_nat n).deriv

中文:
引理 deriv_Gamma_nat
  条件: (n : 自然数)
  证明: (hasDerivAt_Gamma_nat n).deriv

Depends on / 依赖: hasDerivAt_Gamma_nat
-/
lemma deriv_Gamma_nat (n : Nat) :
    deriv Gamma (n + 1) = n ! * (-γ + harmonic n) :=
  (hasDerivAt_Gamma_nat n).deriv

/--
lemma `hasDerivAt_Gamma_one` / 引理 `hasDerivAt_Gamma_one`

English:
lemma hasDerivAt_Gamma_one
  statement: HasDerivAt Gamma (-γ) 1
  proof: by
  simpa only [factorial_zero, cast_one, harmonic_zero, Rat.cast_zero, add_zero, mul_neg, one_mul,
    cast_zero, zero_add] using hasDerivAt_Gamma_nat 0

中文:
引理 hasDerivAt_Gamma_one
  结论: 在点处可导 Gamma (-γ) 1
  证明: by
  simpa only [factorial_zero, cast_one, harmonic_zero, Rat.cast_zero, add_zero, mul_neg, one_mul,
    cast_zero, zero_add] using hasDerivAt_Gamma_nat 0

Depends on / 依赖: Rat.cast_zero, add_zero, cast_one, cast_zero, factorial_zero, harmonic_zero, hasDerivAt_Gamma_nat, mul_neg, one_mul, zero_add
-/
lemma hasDerivAt_Gamma_one : HasDerivAt Gamma (-γ) 1 := by
  simpa only [factorial_zero, cast_one, harmonic_zero, Rat.cast_zero, add_zero, mul_neg, one_mul,
    cast_zero, zero_add] using hasDerivAt_Gamma_nat 0

/--
lemma `hasDerivAt_Gamma_one_half` / 引理 `hasDerivAt_Gamma_one_half`

English:
lemma hasDerivAt_Gamma_one_half
  statement: HasDerivAt Gamma (-√π * (γ + 2 * log 2)) (1 / 2)
  proof: by
  have := HasDerivAt.complex_of_real
    (differentiableAt_Gamma _ ?_) Real.hasDerivAt_Gamma_one_half Gamma_ofReal
  · simpa only [neg_mul, one_div, ofReal_neg, ofReal_mul, ofReal_add, ofReal_ofNat, ofNat_log,
      ofReal_inv] using this
  · intro m
    rw [← ofReal_natCast]; rw [← ofReal_neg]; rw [ne_eq]; rw [ofReal_inj]
    exact ((neg_nonpos.mpr m.cast_nonneg).trans_lt one_half_pos).ne'

中文:
引理 hasDerivAt_Gamma_one_half
  结论: 在点处可导 Gamma (-√π * (γ + 2 * log 2)) (1 / 2)
  证明: by
  have := HasDerivAt.complex_of_real
    (differentiableAt_Gamma _ ?_) Real.hasDerivAt_Gamma_one_half Gamma_ofReal
  · simpa only [neg_mul, one_div, ofReal_neg, ofReal_mul, ofReal_add, ofReal_ofNat, ofNat_log,
      ofReal_inv] using this
  · intro m
    rw [← ofReal_natCast]; rw [← ofReal_neg]; rw [ne_eq]; rw [ofReal_inj]
    exact ((neg_nonpos.mpr m.cast_nonneg).trans_lt one_half_pos).ne'

Depends on / 依赖: Gamma_ofReal, HasDerivAt, HasDerivAt.complex_of_real, Real.hasDerivAt_Gamma_one_half, cast_nonneg, complex_of_real, differentiableAt_Gamma, hasDerivAt_Gamma_one_half, m.cast_nonneg, ne_eq, neg_mul, neg_nonpos, neg_nonpos.mpr, ofNat_log, ofReal_add, ofReal_inj, ofReal_inv, ofReal_mul, ofReal_natCast, ofReal_neg
-/
lemma hasDerivAt_Gamma_one_half : HasDerivAt Gamma (-√π * (γ + 2 * log 2)) (1 / 2) := by
  have := HasDerivAt.complex_of_real
    (differentiableAt_Gamma _ ?_) Real.hasDerivAt_Gamma_one_half Gamma_ofReal
  · simpa only [neg_mul, one_div, ofReal_neg, ofReal_mul, ofReal_add, ofReal_ofNat, ofNat_log,
      ofReal_inv] using this
  · intro m
    rw [← ofReal_natCast]; rw [← ofReal_neg]; rw [ne_eq]; rw [ofReal_inj]
    exact ((neg_nonpos.mpr m.cast_nonneg).trans_lt one_half_pos).ne'

/--
lemma `hasDerivAt_GammaComplex_one` / 引理 `hasDerivAt_GammaComplex_one`

English:
lemma hasDerivAt_GammaComplex_one
  statement: HasDerivAt GammaComplex (-(γ + log (2 * π)) / π) 1
  proof: by
  let f (s : Complex) : Complex := 2 * (2 * π) ^ (-s)
  have : HasDerivAt (fun s : Complex => 2 * (2 * π : Complex) ^ (-s)) (-log (2 * π) / π) 1 := by
    have := (hasDerivAt_neg' (1 : Complex)).const_cpow (c := 2 * π)
      (Or.inl (by exact_mod_cast Real.two_pi_pos.ne'))
    refine (this.const_mul 2).congr_deriv ?_
    rw [mul_neg_one]; rw [mul_neg]; rw [cpow_neg_one]; rw [← div_eq_inv_mul]; rw [← mul_div_assoc]; rw [mul_div_mul_left _ _ two_ne_zero]; rw [neg_div]
  have := this.mul hasDerivAt_Gamma_one
  rwa [Gamma_one, mul_one, cpow_neg_one, ← div_eq_mul_inv, ← div_div, div_self two_ne_zero,
    mul_comm (1 / _), mul_one_div, ← _root_.add_div, ← neg_add, add_comm] at this

中文:
引理 hasDerivAt_GammaComplex_one
  结论: 在点处可导 GammaComplex (-(γ + log (2 * π)) / π) 1
  证明: by
  let f (s : Complex) : Complex := 2 * (2 * π) ^ (-s)
  have : HasDerivAt (fun s : Complex => 2 * (2 * π : Complex) ^ (-s)) (-log (2 * π) / π) 1 := by
    have := (hasDerivAt_neg' (1 : Complex)).const_cpow (c := 2 * π)
      (Or.inl (by exact_mod_cast Real.two_pi_pos.ne'))
    refine (this.const_mul 2).congr_deriv ?_
    rw [mul_neg_one]; rw [mul_neg]; rw [cpow_neg_one]; rw [← div_eq_inv_mul]; rw [← mul_div_assoc]; rw [mul_div_mul_left _ _ two_ne_zero]; rw [neg_div]
  have := this.mul hasDerivAt_Gamma_one
  rwa [Gamma_one, mul_one, cpow_neg_one, ← div_eq_mul_inv, ← div_div, div_self two_ne_zero,
    mul_comm (1 / _), mul_one_div, ← _root_.add_div, ← neg_add, add_comm] at this

Depends on / 依赖: HasDerivAt, Or.inl, Real.two_pi_pos.ne, congr_deriv, const_cpow, const_mul, cpow_neg_one, div_eq_inv_mul, hasDerivAt_Gamma_one, hasDerivAt_neg, mul_div_assoc, mul_div_mul_left, mul_neg, mul_neg_one, neg_div, this.const_mul, this.mul, two_ne_zero, two_pi_pos
-/
lemma hasDerivAt_GammaComplex_one : HasDerivAt GammaComplex (-(γ + log (2 * π)) / π) 1 := by
  let f (s : Complex) : Complex := 2 * (2 * π) ^ (-s)
  have : HasDerivAt (fun s : Complex => 2 * (2 * π : Complex) ^ (-s)) (-log (2 * π) / π) 1 := by
    have := (hasDerivAt_neg' (1 : Complex)).const_cpow (c := 2 * π)
      (Or.inl (by exact_mod_cast Real.two_pi_pos.ne'))
    refine (this.const_mul 2).congr_deriv ?_
    rw [mul_neg_one]; rw [mul_neg]; rw [cpow_neg_one]; rw [← div_eq_inv_mul]; rw [← mul_div_assoc]; rw [mul_div_mul_left _ _ two_ne_zero]; rw [neg_div]
  have := this.mul hasDerivAt_Gamma_one
  rwa [Gamma_one, mul_one, cpow_neg_one, ← div_eq_mul_inv, ← div_div, div_self two_ne_zero,
    mul_comm (1 / _), mul_one_div, ← _root_.add_div, ← neg_add, add_comm] at this

/--
lemma `hasDerivAt_GammaReal_one` / 引理 `hasDerivAt_GammaReal_one`

English:
lemma hasDerivAt_GammaReal_one
  statement: HasDerivAt GammaReal (-(γ + log (4 * π)) / 2) 1
  proof: by
  let f (s : Complex) : Complex := π ^ (-s / 2)
  let g (s : Complex) : Complex := Gamma (s / 2)
  have aux : (π : Complex) ^ (1 / 2 : Complex) = ↑√π := by
    rw [Real.sqrt_eq_rpow]; rw [ofReal_cpow Real.pi_pos.le]; rw [ofReal_div]; rw [ofReal_one]; rw [ofReal_ofNat]
  have aux2 : (√π : Complex) != 0 := by rw [ofReal_ne_zero]; positivity
  have hf : HasDerivAt f (-log π / 2 / √π) 1 := by
    have := ((hasDerivAt_neg (1 : Complex)).div_const 2).const_cpow (c := π) (Or.inr (by simp))
    refine this.congr_deriv ?_
    rw [mul_assoc]; rw [← mul_div_assoc]; rw [mul_neg_one]; rw [neg_div]; rw [cpow_neg]; rw [← div_eq_inv_mul]; rw [aux]
  have hg : HasDerivAt g (-√π * (γ + 2 * log 2) / 2) 1 := by
    have := hasDerivAt_Gamma_one_half.comp 1 (?_ : HasDerivAt (fun s : Complex => s / 2) (1 / 2) 1)
    · rwa [mul_one_div] at this
    · exact (hasDerivAt_id _).div_const _
  refine HasDerivAt.congr_deriv (hf.mul hg) ?_
  simp only [f]
  rw [Gamma_one_half_eq]; rw [aux]; rw [div_mul_cancel₀ _ aux2]; rw [neg_div _ (1 : Complex)]; rw [cpow_neg]; rw [aux]; rw [mul_div_assoc]; rw [← mul_assoc]; rw [mul_neg]; rw [inv_mul_cancel₀ aux2]; rw [neg_one_mul]; rw [← neg_div]; rw [← _root_.add_div]; rw [← neg_add]; rw [add_comm]; rw [add_assoc]; rw [← ofReal_log Real.pi_pos.le]; rw [← ofReal_ofNat]; rw [← ofReal_log zero_le_two]; rw [← ofReal_mul]; rw [← Nat.cast_ofNat (R := Real)]; rw [← Real.log_pow]; rw [← ofReal_add]; rw [← Real.log_mul (by positivity) (by positivity)]; rw [Nat.cast_ofNat]; rw [ofReal_ofNat]; rw [ofReal_log (by positivity)]
  norm_num

中文:
引理 hasDerivAt_Gamma实数_one
  结论: 在点处可导 Gamma实数 (-(γ + log (4 * π)) / 2) 1
  证明: by
  let f (s : Complex) : Complex := π ^ (-s / 2)
  let g (s : Complex) : Complex := Gamma (s / 2)
  have aux : (π : Complex) ^ (1 / 2 : Complex) = ↑√π := by
    rw [Real.sqrt_eq_rpow]; rw [ofReal_cpow Real.pi_pos.le]; rw [ofReal_div]; rw [ofReal_one]; rw [ofReal_ofNat]
  have aux2 : (√π : Complex) != 0 := by rw [ofReal_ne_zero]; positivity
  have hf : HasDerivAt f (-log π / 2 / √π) 1 := by
    have := ((hasDerivAt_neg (1 : Complex)).div_const 2).const_cpow (c := π) (Or.inr (by simp))
    refine this.congr_deriv ?_
    rw [mul_assoc]; rw [← mul_div_assoc]; rw [mul_neg_one]; rw [neg_div]; rw [cpow_neg]; rw [← div_eq_inv_mul]; rw [aux]
  have hg : HasDerivAt g (-√π * (γ + 2 * log 2) / 2) 1 := by
    have := hasDerivAt_Gamma_one_half.comp 1 (?_ : HasDerivAt (fun s : Complex => s / 2) (1 / 2) 1)
    · rwa [mul_one_div] at this
    · exact (hasDerivAt_id _).div_const _
  refine HasDerivAt.congr_deriv (hf.mul hg) ?_
  simp only [f]
  rw [Gamma_one_half_eq]; rw [aux]; rw [div_mul_cancel₀ _ aux2]; rw [neg_div _ (1 : Complex)]; rw [cpow_neg]; rw [aux]; rw [mul_div_assoc]; rw [← mul_assoc]; rw [mul_neg]; rw [inv_mul_cancel₀ aux2]; rw [neg_one_mul]; rw [← neg_div]; rw [← _root_.add_div]; rw [← neg_add]; rw [add_comm]; rw [add_assoc]; rw [← ofReal_log Real.pi_pos.le]; rw [← ofReal_ofNat]; rw [← ofReal_log zero_le_two]; rw [← ofReal_mul]; rw [← Nat.cast_ofNat (R := Real)]; rw [← Real.log_pow]; rw [← ofReal_add]; rw [← Real.log_mul (by positivity) (by positivity)]; rw [Nat.cast_ofNat]; rw [ofReal_ofNat]; rw [ofReal_log (by positivity)]
  norm_num

Depends on / 依赖: HasDerivAt, Or.inr, Real.pi_pos.le, Real.sqrt_eq_rpow, congr_deriv, const_cpow, div_const, hasDerivAt_neg, ofReal_cpow, ofReal_div, ofReal_ne_zero, ofReal_ofNat, ofReal_one, pi_pos, sqrt_eq_rpow, this.congr_deriv
-/
lemma hasDerivAt_GammaReal_one : HasDerivAt GammaReal (-(γ + log (4 * π)) / 2) 1 := by
  let f (s : Complex) : Complex := π ^ (-s / 2)
  let g (s : Complex) : Complex := Gamma (s / 2)
  have aux : (π : Complex) ^ (1 / 2 : Complex) = ↑√π := by
    rw [Real.sqrt_eq_rpow]; rw [ofReal_cpow Real.pi_pos.le]; rw [ofReal_div]; rw [ofReal_one]; rw [ofReal_ofNat]
  have aux2 : (√π : Complex) != 0 := by rw [ofReal_ne_zero]; positivity
  have hf : HasDerivAt f (-log π / 2 / √π) 1 := by
    have := ((hasDerivAt_neg (1 : Complex)).div_const 2).const_cpow (c := π) (Or.inr (by simp))
    refine this.congr_deriv ?_
    rw [mul_assoc]; rw [← mul_div_assoc]; rw [mul_neg_one]; rw [neg_div]; rw [cpow_neg]; rw [← div_eq_inv_mul]; rw [aux]
  have hg : HasDerivAt g (-√π * (γ + 2 * log 2) / 2) 1 := by
    have := hasDerivAt_Gamma_one_half.comp 1 (?_ : HasDerivAt (fun s : Complex => s / 2) (1 / 2) 1)
    · rwa [mul_one_div] at this
    · exact (hasDerivAt_id _).div_const _
  refine HasDerivAt.congr_deriv (hf.mul hg) ?_
  simp only [f]
  rw [Gamma_one_half_eq]; rw [aux]; rw [div_mul_cancel₀ _ aux2]; rw [neg_div _ (1 : Complex)]; rw [cpow_neg]; rw [aux]; rw [mul_div_assoc]; rw [← mul_assoc]; rw [mul_neg]; rw [inv_mul_cancel₀ aux2]; rw [neg_one_mul]; rw [← neg_div]; rw [← _root_.add_div]; rw [← neg_add]; rw [add_comm]; rw [add_assoc]; rw [← ofReal_log Real.pi_pos.le]; rw [← ofReal_ofNat]; rw [← ofReal_log zero_le_two]; rw [← ofReal_mul]; rw [← Nat.cast_ofNat (R := Real)]; rw [← Real.log_pow]; rw [← ofReal_add]; rw [← Real.log_mul (by positivity) (by positivity)]; rw [Nat.cast_ofNat]; rw [ofReal_ofNat]; rw [ofReal_log (by positivity)]
  norm_num

end Complex
