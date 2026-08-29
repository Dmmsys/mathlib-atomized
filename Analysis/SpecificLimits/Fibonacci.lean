/-
Copyright (c) 2025 Snir Broshi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Snir Broshi
-/
module

public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.NumberTheory.Real.GoldenRatio

/-!
# The ratio of consecutive Fibonacci numbers

We prove that the ratio of consecutive Fibonacci numbers tends to the golden ratio.
-/

public section

open Nat Real Filter Tendsto
open scoped Topology goldenRatio

/--
theorem `tendsto_fib_succ_div_fib_atTop` / 定理 `tendsto_fib_succ_div_fib_atTop`

English:
theorem tendsto_fib_succ_div_fib_atTop
  proof: by
  have h₁ n : (fib (n + 1) / fib n : Real) = (φ - ψ * (ψ / φ) ^ n) / (1 - (ψ / φ) ^ n) := by
    simp only [coe_fib_eq, pow_succ, div_pow]
    field
have h₂ := tendsto_pow_atTop_nhds_zero_of_abs_lt_one (r := ψ / φ) by
    rw [abs_div]; rw [div_lt_one <| by positivity]; rw [abs_of_pos goldenRatio_pos]; rw [abs_lt]
    ring_nf
    bound
  rw [show φ = (φ - ψ * 0) / (1 - 0) by ring]; rw [funext h₁]
.div (const_sub _ h₂) by simp exact const_sub _ (const_mul _ h₂)

中文:
定理 tendsto_fib_succ_div_fib_atTop
  证明: by
  have h₁ n : (fib (n + 1) / fib n : Real) = (φ - ψ * (ψ / φ) ^ n) / (1 - (ψ / φ) ^ n) := by
    simp only [coe_fib_eq, pow_succ, div_pow]
    field
have h₂ := tendsto_pow_atTop_nhds_zero_of_abs_lt_one (r := ψ / φ) by
    rw [abs_div]; rw [div_lt_one <| by positivity]; rw [abs_of_pos goldenRatio_pos]; rw [abs_lt]
    ring_nf
    bound
  rw [show φ = (φ - ψ * 0) / (1 - 0) by ring]; rw [funext h₁]
.div (const_sub _ h₂) by simp exact const_sub _ (const_mul _ h₂)

Depends on / 依赖: abs_div, abs_lt, abs_of_pos, coe_fib_eq, const_mul, const_sub, div_lt_one, div_pow, goldenRatio_pos, pow_succ, ring_nf, tendsto_pow_atTop_nhds_zero_of_abs_lt_one
-/
theorem tendsto_fib_succ_div_fib_atTop :
    Tendsto (fun n => (fib (n + 1) / fib n : Real)) atTop (𝓝 φ) := by
  have h₁ n : (fib (n + 1) / fib n : Real) = (φ - ψ * (ψ / φ) ^ n) / (1 - (ψ / φ) ^ n) := by
    simp only [coe_fib_eq, pow_succ, div_pow]
    field
have h₂ := tendsto_pow_atTop_nhds_zero_of_abs_lt_one (r := ψ / φ) by
    rw [abs_div]; rw [div_lt_one <| by positivity]; rw [abs_of_pos goldenRatio_pos]; rw [abs_lt]
    ring_nf
    bound
  rw [show φ = (φ - ψ * 0) / (1 - 0) by ring]; rw [funext h₁]
.div (const_sub _ h₂) by simp exact const_sub _ (const_mul _ h₂)

/--
theorem `tendsto_fib_div_fib_succ_atTop` / 定理 `tendsto_fib_div_fib_succ_atTop`

English:
theorem tendsto_fib_div_fib_succ_atTop
  proof: by
  convert! tendsto_fib_succ_div_fib_atTop.inv₀ (by positivity) using 2
  · rw [inv_div]
  · rw [inv_goldenRatio]

中文:
定理 tendsto_fib_div_fib_succ_atTop
  证明: by
  convert! tendsto_fib_succ_div_fib_atTop.inv₀ (by positivity) using 2
  · rw [inv_div]
  · rw [inv_goldenRatio]

Depends on / 依赖: convert, inv_div, inv_goldenRatio, tendsto_fib_succ_div_fib_atTop, tendsto_fib_succ_div_fib_atTop.inv
-/
theorem tendsto_fib_div_fib_succ_atTop :
    Tendsto (fun n => (fib n / fib (n + 1) : Real)) atTop (𝓝 (-ψ)) := by
  convert! tendsto_fib_succ_div_fib_atTop.inv₀ (by positivity) using 2
  · rw [inv_div]
  · rw [inv_goldenRatio]
