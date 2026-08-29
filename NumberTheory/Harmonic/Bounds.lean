/-
Copyright (c) 2024 Arend Mellendijk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arend Mellendijk
-/
module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SumIntegralComparisons
public import Mathlib.NumberTheory.Harmonic.Defs

/-!

This file proves $\log(n + 1) \le H_n \le 1 + \log(n)$ for all natural numbers $n$.

-/

public section

/--
lemma `harmonic_eq_sum_Icc` / 引理 `harmonic_eq_sum_Icc`

English:
lemma harmonic_eq_sum_Icc
  given: {n : Nat}
  statement: harmonic n = ∑ i in Finset.Icc 1 n, (↑i)⁻¹
  proof: by
  rw [harmonic]; rw [Finset.range_eq_Ico]; rw [Finset.sum_Ico_add' (fun (i : Nat) => (i : Rat)⁻¹) 0 n (c := 1)]
  simp only [Finset.Ico_add_one_right_eq_Icc]

中文:
引理 harmonic_eq_sum_Icc
  条件: {n : 自然数}
  结论: harmonic n = ∑ i in 有限集.闭区间 1 n, (↑i)⁻¹
  证明: by
  rw [harmonic]; rw [Finset.range_eq_Ico]; rw [Finset.sum_Ico_add' (fun (i : Nat) => (i : Rat)⁻¹) 0 n (c := 1)]
  simp only [Finset.Ico_add_one_right_eq_Icc]

Depends on / 依赖: Finset, Finset.Ico_add_one_right_eq_Icc, Finset.range_eq_Ico, Finset.sum_Ico_add, Ico_add_one_right_eq_Icc, harmonic, range_eq_Ico, sum_Ico_add
-/
lemma harmonic_eq_sum_Icc {n : Nat} : harmonic n = ∑ i in Finset.Icc 1 n, (↑i)⁻¹ := by
  rw [harmonic]; rw [Finset.range_eq_Ico]; rw [Finset.sum_Ico_add' (fun (i : Nat) => (i : Rat)⁻¹) 0 n (c := 1)]
  simp only [Finset.Ico_add_one_right_eq_Icc]

/--
theorem `log_add_one_le_harmonic` / 定理 `log_add_one_le_harmonic`

English:
theorem log_add_one_le_harmonic
  given: (n : Nat)
  proof: by
  calc _ = ∫ x in (1 : Nat)..↑(n + 1), x⁻¹ := ?_
       _ <= ∑ d in Finset.Icc 1 n, (d : Real)⁻¹ := ?_
       _ = harmonic n := ?_
  · rw [Nat.cast_one, integral_inv (by simp [(show ¬ (1 : Real) <= 0 by simp)]), div_one]
  · exact (inv_antitoneOn_Icc_right <| by simp).integral_le_sum_Ico (Nat.le_

中文:
定理 log_add_one_le_harmonic
  条件: (n : 自然数)
  证明: by
  calc _ = ∫ x in (1 : Nat)..↑(n + 1), x⁻¹ := ?_
       _ <= ∑ d in Finset.Icc 1 n, (d : Real)⁻¹ := ?_
       _ = harmonic n := ?_
  · rw [Nat.cast_one, integral_inv (by simp [(show ¬ (1 : Real) <= 0 by simp)]), div_one]
  · exact (inv_antitoneOn_Icc_right <| by simp).integral_le_sum_Ico (Nat.le_

Depends on / 依赖: Finset, Finset.Icc, Nat.cast_one, Nat.le_add_left, Rat.cast_inv, Rat.cast_natCast, Rat.cast_sum, cast_inv, cast_natCast, cast_one, cast_sum, div_one, harmonic, harmonic_eq_sum_Icc, integral_inv, integral_le_sum_Ico, inv_antitoneOn_Icc_right, le_add_left
-/
theorem log_add_one_le_harmonic (n : Nat) :
    Real.log ↑(n + 1) <= harmonic n := by
  calc _ = ∫ x in (1 : Nat)..↑(n + 1), x⁻¹ := ?_
       _ <= ∑ d in Finset.Icc 1 n, (d : Real)⁻¹ := ?_
       _ = harmonic n := ?_
  · rw [Nat.cast_one, integral_inv (by simp [(show ¬ (1 : Real) <= 0 by simp)]), div_one]
  · exact (inv_antitoneOn_Icc_right <| by simp).integral_le_sum_Ico (Nat.le_add_left 1 n)
  · simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]

/--
theorem `harmonic_le_one_add_log` / 定理 `harmonic_le_one_add_log`

English:
theorem harmonic_le_one_add_log
  given: (n : Nat)
  proof: by
  by_cases hn0 : n = 0
  · simp [hn0]
  have hn : 1 <= n := Nat.one_le_iff_ne_zero.mpr hn0
  simp_rw [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
  rw [← Finset.sum_erase_add (Finset.Icc 1 n) _ (Finset.left_mem_Icc.mpr hn)]; rw [add_comm]; rw [Nat.cast_one]; rw [inv_one]
  

中文:
定理 harmonic_le_one_add_log
  条件: (n : 自然数)
  证明: by
  by_cases hn0 : n = 0
  · simp [hn0]
  have hn : 1 <= n := Nat.one_le_iff_ne_zero.mpr hn0
  simp_rw [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
  rw [← Finset.sum_erase_add (Finset.Icc 1 n) _ (Finset.left_mem_Icc.mpr hn)]; rw [add_comm]; rw [Nat.cast_one]; rw [inv_one]
  

Depends on / 依赖: Finset, Finset.Icc, Finset.Icc_erase_left, Finset.left_mem_Icc.mpr, Finset.sum_erase_add, Icc_erase_left, Nat.cast_one, Nat.one_le_iff_ne_zero.mpr, Rat.cast_inv, Rat.cast_natCast, Rat.cast_sum, Real.log, add_comm, cast_inv, cast_natCast, cast_one, cast_sum, harmonic_eq_sum_Icc, inv_one, left_mem_Icc
-/
theorem harmonic_le_one_add_log (n : Nat) :
    harmonic n <= 1 + Real.log n := by
  by_cases hn0 : n = 0
  · simp [hn0]
  have hn : 1 <= n := Nat.one_le_iff_ne_zero.mpr hn0
  simp_rw [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
  rw [← Finset.sum_erase_add (Finset.Icc 1 n) _ (Finset.left_mem_Icc.mpr hn)]; rw [add_comm]; rw [Nat.cast_one]; rw [inv_one]
  gcongr
  simp only [Finset.Icc_erase_left]
  calc ∑ d in .Ico 2 (n + 1), (d : Real)⁻¹
    _ = ∑ d in .Ico 2 (n + 1), (↑(d + 1) - 1)⁻¹ := ?_
    _ <= ∫ x in 2..↑(n + 1), (x - 1)⁻¹ := ?_
    _ = ∫ x in 1..n, x⁻¹ := ?_
    _ = Real.log ↑n := ?_
  · simp_rw [Nat.cast_add, Nat.cast_one, add_sub_cancel_right]
· exact @AntitoneOn.sum_le_integral_Ico 2 (n + 1) (fun x : Real => (x - 1)⁻¹) (by linarith [hn])
      sub_inv_antitoneOn_Icc_right (by simp)
  · convert! intervalIntegral.integral_comp_sub_right _ 1
    · norm_num
    · simp only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right]
  · convert! integral_inv _
    · rw [div_one]
    · simp only [Nat.one_le_cast, hn, Set.uIcc_of_le, Set.mem_Icc, Nat.cast_nonneg,
        and_true, not_le, zero_lt_one]

/--
theorem `log_le_harmonic_floor` / 定理 `log_le_harmonic_floor`

English:
theorem log_le_harmonic_floor
  given: (y : Real) (hy : 0 <= y)
  proof: by
  by_cases h0 : y = 0
  · simp [h0]
  · calc
      _ <= Real.log ↑(Nat.floor y + 1) := ?_
      _ <= _ := log_add_one_le_harmonic _
    gcongr
    apply (Nat.le_ceil y).trans
    norm_cast
    exact Nat.ceil_le_floor_add_one y

中文:
定理 log_le_harmonic_floor
  条件: (y : 实数) (hy : 0 <= y)
  证明: by
  by_cases h0 : y = 0
  · simp [h0]
  · calc
      _ <= Real.log ↑(Nat.floor y + 1) := ?_
      _ <= _ := log_add_one_le_harmonic _
    gcongr
    apply (Nat.le_ceil y).trans
    norm_cast
    exact Nat.ceil_le_floor_add_one y

Depends on / 依赖: Nat.ceil_le_floor_add_one, Nat.floor, Nat.le_ceil, Real.log, ceil_le_floor_add_one, le_ceil, log_add_one_le_harmonic
-/
theorem log_le_harmonic_floor (y : Real) (hy : 0 <= y) :
    Real.log y <= harmonic ⌊y⌋₊ := by
  by_cases h0 : y = 0
  · simp [h0]
  · calc
      _ <= Real.log ↑(Nat.floor y + 1) := ?_
      _ <= _ := log_add_one_le_harmonic _
    gcongr
    apply (Nat.le_ceil y).trans
    norm_cast
    exact Nat.ceil_le_floor_add_one y

/--
theorem `harmonic_floor_le_one_add_log` / 定理 `harmonic_floor_le_one_add_log`

English:
theorem harmonic_floor_le_one_add_log
  given: (y : Real) (hy : 1 <= y)
  proof: by
  refine (harmonic_le_one_add_log _).trans ?_
  gcongr
  · exact_mod_cast Nat.floor_pos.mpr hy
· exact Nat.floor_le zero_le_one.trans hy

中文:
定理 harmonic_floor_le_one_add_log
  条件: (y : 实数) (hy : 1 <= y)
  证明: by
  refine (harmonic_le_one_add_log _).trans ?_
  gcongr
  · exact_mod_cast Nat.floor_pos.mpr hy
· exact Nat.floor_le zero_le_one.trans hy

Depends on / 依赖: Nat.floor_le, Nat.floor_pos.mpr, floor_le, floor_pos, harmonic_le_one_add_log, zero_le_one, zero_le_one.trans
-/
theorem harmonic_floor_le_one_add_log (y : Real) (hy : 1 <= y) :
    harmonic ⌊y⌋₊ <= 1 + Real.log y := by
  refine (harmonic_le_one_add_log _).trans ?_
  gcongr
  · exact_mod_cast Nat.floor_pos.mpr hy
· exact Nat.floor_le zero_le_one.trans hy
