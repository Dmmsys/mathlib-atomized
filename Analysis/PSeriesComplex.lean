/-
Copyright (c) 2024 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
module

public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.PSeries
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# Convergence of `p`-series (complex case)

Here we show convergence of `∑ n : ℕ, 1 / n ^ p` for complex `p`. This is done in a separate file
rather than in `Analysis.PSeries` in order to keep the prerequisites of the former relatively light.

## Tags

p-series, Cauchy condensation test
-/

public section

/--
lemma `Complex.summable_one_div_nat_cpow` / 引理 `Complex.summable_one_div_nat_cpow`

English:
lemma Complex.summable_one_div_nat_cpow
  given: {p : Complex}
  proof: by
  rw [← Real.summable_one_div_nat_rpow]; rw [← summable_nat_add_iff 1 (G := Real)]; rw [← summable_nat_add_iff 1 (G := Complex)]; rw [← summable_norm_iff]
  simp only [norm_div, norm_one, ← ofReal_natCast, norm_cpow_eq_rpow_re_of_pos
    (Nat.cast_pos.mpr <| Nat.succ_pos _)]

中文:
引理 复形.summable_one_div_nat_cpow
  条件: {p : 复形}
  证明: by
  rw [← Real.summable_one_div_nat_rpow]; rw [← summable_nat_add_iff 1 (G := Real)]; rw [← summable_nat_add_iff 1 (G := Complex)]; rw [← summable_norm_iff]
  simp only [norm_div, norm_one, ← ofReal_natCast, norm_cpow_eq_rpow_re_of_pos
    (Nat.cast_pos.mpr <| Nat.succ_pos _)]

Depends on / 依赖: Nat.cast_pos.mpr, Nat.succ_pos, Real.summable_one_div_nat_rpow, cast_pos, norm_cpow_eq_rpow_re_of_pos, norm_div, norm_one, ofReal_natCast, succ_pos, summable_nat_add_iff, summable_norm_iff, summable_one_div_nat_rpow
-/
lemma Complex.summable_one_div_nat_cpow {p : Complex} :
    Summable (fun n : Nat => 1 / (n : Complex) ^ p) ↔ 1 < re p := by
  rw [← Real.summable_one_div_nat_rpow]; rw [← summable_nat_add_iff 1 (G := Real)]; rw [← summable_nat_add_iff 1 (G := Complex)]; rw [← summable_norm_iff]
  simp only [norm_div, norm_one, ← ofReal_natCast, norm_cpow_eq_rpow_re_of_pos
    (Nat.cast_pos.mpr <| Nat.succ_pos _)]
