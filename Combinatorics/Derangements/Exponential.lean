/-
Copyright (c) 2021 Henry Swanson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henry Swanson, Patrick Massot
-/
module

public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Combinatorics.Derangements.Finite
public import Mathlib.Data.Nat.Cast.Field

/-!
# Derangement exponential series

This file proves that the probability of a permutation on n elements being a derangement is 1/e.
The specific lemma is `numDerangements_tendsto_inv_e`.
-/

public section


open Filter NormedSpace

open scoped Topology

/--
theorem `numDerangements_tendsto_inv_e` / 定理 `numDerangements_tendsto_inv_e`

English:
theorem numDerangements_tendsto_inv_e
  proof: by
  -- we show that d(n)/n! is the partial sum of exp(-1), but offset by 1.
  -- this isn't entirely obvious, since we have to ensure that asc_factorial and
  -- factorial interact in the right way, e.g., that k ≤ n always
  let s : Nat -> Real := fun n => ∑ k in Finset.range n, (-1 : Real) ^ k / k

中文:
定理 numDerangements_tendsto_inv_e
  证明: by
  -- we show that d(n)/n! is the partial sum of exp(-1), but offset by 1.
  -- this isn't entirely obvious, since we have to ensure that asc_factorial and
  -- factorial interact in the right way, e.g., that k ≤ n always
  let s : Nat -> Real := fun n => ∑ k in Finset.range n, (-1 : Real) ^ k / k
-/
theorem numDerangements_tendsto_inv_e :
    Tendsto (fun n => (numDerangements n : Real) / n.factorial) atTop (𝓝 (Real.exp (-1))) := by
  -- we show that d(n)/n! is the partial sum of exp(-1), but offset by 1.
  -- this isn't entirely obvious, since we have to ensure that asc_factorial and
  -- factorial interact in the right way, e.g., that k ≤ n always
  let s : Nat -> Real := fun n => ∑ k in Finset.range n, (-1 : Real) ^ k / k.factorial
  suffices forall n : Nat, (numDerangements n : Real) / n.factorial = s (n + 1) by
    simp_rw [this]
    -- shift the function by 1, and then use the fact that the partial sums
    -- converge to the infinite sum
    rw [tendsto_add_atTop_iff_nat
      (f := fun n => ∑ k in Finset.range n]; rw [(-1 : Real) ^ k / k.factorial) 1]
    apply HasSum.tendsto_sum_nat
    -- there's no specific lemma for ℝ that ∑ x^k/k! sums to exp(x), but it's
    -- true in more general fields, so use that lemma
    rw [Real.exp_eq_exp_Real]
    exact expSeries_div_hasSum_exp (-1 : Real)
  intro n
  rw [← Int.cast_natCast]; rw [numDerangements_sum]
  push_cast
  rw [Finset.sum_div]
  -- get down to individual terms
  refine Finset.sum_congr (refl _) ?_
  intro k hk
  have h_le : k <= n := Finset.mem_range_succ_iff.mp hk
  rw [Nat.ascFactorial_eq_div]; rw [add_tsub_cancel_of_le h_le]
  push_cast [Nat.factorial_dvd_factorial h_le]
  field
