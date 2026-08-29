/-
Copyright (c) 2020 Patrick Stevens. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Stevens, Bolton Bailey
-/
module

public import Mathlib.Data.Nat.Choose.Factorization
public import Mathlib.NumberTheory.Primorial
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Analysis.Convex.SpecificFunctions.Deriv
public import Mathlib.Tactic.NormNum.Prime

/-!
# Bertrand's Postulate

This file contains a proof of Bertrand's postulate: That between any positive number and its
double there is a prime.

The proof follows the outline of the Erdős proof presented in "Proofs from THE BOOK": One considers
the prime factorization of `(2 * n).choose n`, and splits the constituent primes up into various
groups, then upper bounds the contribution of each group. This upper bounds the central binomial
coefficient, and if the postulate does not hold, this upper bound conflicts with a simple lower
bound for large enough `n`. This proves the result holds for large enough `n`, and for smaller `n`
an explicit list of primes is provided which covers the remaining cases.

As in the [Metamath implementation](carneiro2015arithmetic), we rely on some optimizations from
[Shigenori Tochiori](tochiori_bertrand). In particular we use the cleaner bound on the central
binomial coefficient given in `Nat.four_pow_lt_mul_centralBinom`.

## References

* [M. Aigner and G. M. Ziegler _Proofs from THE BOOK_][aigner1999proofs]
* [S. Tochiori, _Considering the Proof of “There is a Prime between n and 2n”_][tochiori_bertrand]
* [M. Carneiro, _Arithmetic in Metamath, Case Study: Bertrand's Postulate_][carneiro2015arithmetic]

## Tags

Bertrand, prime, binomial coefficients
-/

public section


section Real

open Real

namespace Bertrand

/--
theorem `real_main_inequality` / 定理 `real_main_inequality`

English:
theorem real_main_inequality
  given: {x : Real} (x_large : (512 : Real) <= x)
  proof: by
  let f : Real -> Real := fun x => log x + √(2 * x) * log (2 * x) - log 4 / 3 * x
  have hf' : forall x, 0 < x -> 0 < x * (2 * x) ^ √(2 * x) / 4 ^ (x / 3) := fun x h =>
    div_pos (mul_pos h (rpow_pos_of_pos (mul_pos two_pos h) _)) (rpow_pos_of_pos four_pos _)
  have hf : forall x, 0 < x -> f x = log (x * (2 * x) ^ √(2 * x) / 4 ^ (x / 3)) := by
    intro x h5
    have h6 := mul_pos (zero_lt_two' Real) h5
    have h7 := rpow_pos_of_pos h6 (√(2 * x))
    rw [log_div (mul_pos h5 h7).ne' (rpow_pos_of_pos four_pos _).ne']; rw [log_mul h5.ne' h7.ne']; rw [log_rpow h6]; rw [log_rpow zero_lt_four]; rw [← mul_div_right_comm]; rw [← mul_div]; rw [mul_comm x]
  have h5 : 0 < x := lt_of_lt_of_le (by norm_num1) x_large
  rw [← div_le_one (rpow_pos_of_pos four_pos x)]; rw [← div_div_eq_mul_div]; rw [← rpow_sub four_pos]; rw [←
    mul_div 2 x]; rw [mul_div_left_comm]; rw [← mul_one_sub]; rw [(by norm_num1 : (1 : Real) - 2 / 3 = 1 / 3)]; rw [mul_one_div]; rw [← log_nonpos_iff (hf' x h5).le]; rw [← hf x h5]
  -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11083): the proof was rewritten, because it was too slow
  -- Original:
  /-
  have h : ConcaveOn ℝ (Set.Ioi 0.5) f := by
    refine ((strictConcaveOn_log_Ioi.concaveOn.subset (Set.Ioi_subset_Ioi _)
      (convex_Ioi 0.5)).add ((strictConcaveOn_sqrt_mul_log_Ioi.concaveOn.comp_linearMap
      ((2 : ℝ) • LinearMap.id)).subset
      (fun a ha => lt_of_eq_of_lt _ ((mul_lt_mul_iff_right₀ two_pos).mpr ha)) (convex_Ioi 0.5))).sub
      ((convex_on_id (convex_Ioi (0.5 : ℝ))).smul (div_nonneg (log_nonneg _) _))
    norm_num
  -/
  have h : ConcaveOn Real (Set.Ioi 0.5) f := by
    apply ConcaveOn.sub
    · apply ConcaveOn.add
      · exact strictConcaveOn_log_Ioi.concaveOn.subset
          (Set.Ioi_subset_Ioi (by norm_num)) (convex_Ioi 0.5)
      convert!
        ((strictConcaveOn_sqrt_mul_log_Ioi.concaveOn.comp_linearMap ((2 : Real) • LinearMap.id)))
        using 1
      ext x
      simp only [Set.mem_Ioi, Set.mem_preimage, LinearMap.smul_apply,
        LinearMap.id_coe, id_eq, smul_eq_mul]
      rw [← mul_lt_mul_iff_right₀ (two_pos)]
      norm_num1
      rfl
    apply ConvexOn.smul
    · refine div_nonneg (log_nonneg (by norm_num1)) (by norm_num1)
    · exact convexOn_id (convex_Ioi (0.5 : Real))
  suffices exists x1 x2, 0.5 < x1 ∧ x1 < x2 ∧ x2 <= x ∧ 0 <= f x1 ∧ f x2 <= 0 by
    obtain ⟨x1, x2, h1, h2, h0, h3, h4⟩ := this
    exact (h.right_le_of_le_left'' h1 ((h1.trans h2).trans_le h0) h2 h0 (h4.trans h3)).trans h4
  refine ⟨18, 512, by norm_num1, by norm_num1, x_large, ?_, ?_⟩
  · have : √(2 * 18 : Real) = 6 := (sqrt_eq_iff_mul_self_eq_of_pos (by norm_num1)).mpr (by norm_num1)
    rw [hf _ (by norm_num1)]; rw [log_nonneg_iff (by positivity)]; rw [this]; rw [one_le_div (by norm_num1)]
    norm_num1
  · have : √(2 * 512) = 32 :=
      (sqrt_eq_iff_mul_self_eq_of_pos (by norm_num1)).mpr (by norm_num1)
    rw [hf _ (by norm_num1)]; rw [log_nonpos_iff (hf' _ (by norm_num1)).le]; rw [this]; rw [div_le_one (by positivity)]
    conv in 512 => equals 2 ^ 9 => norm_num1
    conv in 2 * 512 => equals 2 ^ 10 => norm_num1
    conv in 32 => rw [← Nat.cast_ofNat]
    rw [rpow_natCast]; rw [← pow_mul]; rw [← pow_add]
    conv in 4 => equals 2 ^ (2 : Real) => rw [rpow_two]; norm_num1
    rw [← rpow_mul]; rw [← rpow_natCast]
    on_goal 1 => apply rpow_le_rpow_of_exponent_le
    all_goals norm_num1

中文:
定理 real_main_inequality
  条件: {x : 实数} (x_large : (512 : 实数) <= x)
  证明: by
  let f : Real -> Real := fun x => log x + √(2 * x) * log (2 * x) - log 4 / 3 * x
  have hf' : forall x, 0 < x -> 0 < x * (2 * x) ^ √(2 * x) / 4 ^ (x / 3) := fun x h =>
    div_pos (mul_pos h (rpow_pos_of_pos (mul_pos two_pos h) _)) (rpow_pos_of_pos four_pos _)
  have hf : forall x, 0 < x -> f x = log (x * (2 * x) ^ √(2 * x) / 4 ^ (x / 3)) := by
    intro x h5
    have h6 := mul_pos (zero_lt_two' Real) h5
    have h7 := rpow_pos_of_pos h6 (√(2 * x))
    rw [log_div (mul_pos h5 h7).ne' (rpow_pos_of_pos four_pos _).ne']; rw [log_mul h5.ne' h7.ne']; rw [log_rpow h6]; rw [log_rpow zero_lt_four]; rw [← mul_div_right_comm]; rw [← mul_div]; rw [mul_comm x]
  have h5 : 0 < x := lt_of_lt_of_le (by norm_num1) x_large
  rw [← div_le_one (rpow_pos_of_pos four_pos x)]; rw [← div_div_eq_mul_div]; rw [← rpow_sub four_pos]; rw [←
    mul_div 2 x]; rw [mul_div_left_comm]; rw [← mul_one_sub]; rw [(by norm_num1 : (1 : Real) - 2 / 3 = 1 / 3)]; rw [mul_one_div]; rw [← log_nonpos_iff (hf' x h5).le]; rw [← hf x h5]
  -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11083): the proof was rewritten, because it was too slow
  -- Original:
  /-
  have h : ConcaveOn ℝ (Set.Ioi 0.5) f := by
    refine ((strictConcaveOn_log_Ioi.concaveOn.subset (Set.Ioi_subset_Ioi _)
      (convex_Ioi 0.5)).add ((strictConcaveOn_sqrt_mul_log_Ioi.concaveOn.comp_linearMap
      ((2 : ℝ) • LinearMap.id)).subset
      (fun a ha => lt_of_eq_of_lt _ ((mul_lt_mul_iff_right₀ two_pos).mpr ha)) (convex_Ioi 0.5))).sub
      ((convex_on_id (convex_Ioi (0.5 : ℝ))).smul (div_nonneg (log_nonneg _) _))
    norm_num
  -/
  have h : ConcaveOn Real (Set.Ioi 0.5) f := by
    apply ConcaveOn.sub
    · apply ConcaveOn.add
      · exact strictConcaveOn_log_Ioi.concaveOn.subset
          (Set.Ioi_subset_Ioi (by norm_num)) (convex_Ioi 0.5)
      convert!
        ((strictConcaveOn_sqrt_mul_log_Ioi.concaveOn.comp_linearMap ((2 : Real) • LinearMap.id)))
        using 1
      ext x
      simp only [Set.mem_Ioi, Set.mem_preimage, LinearMap.smul_apply,
        LinearMap.id_coe, id_eq, smul_eq_mul]
      rw [← mul_lt_mul_iff_right₀ (two_pos)]
      norm_num1
      rfl
    apply ConvexOn.smul
    · refine div_nonneg (log_nonneg (by norm_num1)) (by norm_num1)
    · exact convexOn_id (convex_Ioi (0.5 : Real))
  suffices exists x1 x2, 0.5 < x1 ∧ x1 < x2 ∧ x2 <= x ∧ 0 <= f x1 ∧ f x2 <= 0 by
    obtain ⟨x1, x2, h1, h2, h0, h3, h4⟩ := this
    exact (h.right_le_of_le_left'' h1 ((h1.trans h2).trans_le h0) h2 h0 (h4.trans h3)).trans h4
  refine ⟨18, 512, by norm_num1, by norm_num1, x_large, ?_, ?_⟩
  · have : √(2 * 18 : Real) = 6 := (sqrt_eq_iff_mul_self_eq_of_pos (by norm_num1)).mpr (by norm_num1)
    rw [hf _ (by norm_num1)]; rw [log_nonneg_iff (by positivity)]; rw [this]; rw [one_le_div (by norm_num1)]
    norm_num1
  · have : √(2 * 512) = 32 :=
      (sqrt_eq_iff_mul_self_eq_of_pos (by norm_num1)).mpr (by norm_num1)
    rw [hf _ (by norm_num1)]; rw [log_nonpos_iff (hf' _ (by norm_num1)).le]; rw [this]; rw [div_le_one (by positivity)]
    conv in 512 => equals 2 ^ 9 => norm_num1
    conv in 2 * 512 => equals 2 ^ 10 => norm_num1
    conv in 32 => rw [← Nat.cast_ofNat]
    rw [rpow_natCast]; rw [← pow_mul]; rw [← pow_add]
    conv in 4 => equals 2 ^ (2 : Real) => rw [rpow_two]; norm_num1
    rw [← rpow_mul]; rw [← rpow_natCast]
    on_goal 1 => apply rpow_le_rpow_of_exponent_le
    all_goals norm_num1

Depends on / 依赖: div_pos, four_pos, log_div, mul_pos, rpow_pos_of_pos, two_pos, zero_lt_two
-/
theorem real_main_inequality {x : Real} (x_large : (512 : Real) <= x) :
    x * (2 * x) ^ √(2 * x) * 4 ^ (2 * x / 3) <= 4 ^ x := by
  let f : Real -> Real := fun x => log x + √(2 * x) * log (2 * x) - log 4 / 3 * x
  have hf' : forall x, 0 < x -> 0 < x * (2 * x) ^ √(2 * x) / 4 ^ (x / 3) := fun x h =>
    div_pos (mul_pos h (rpow_pos_of_pos (mul_pos two_pos h) _)) (rpow_pos_of_pos four_pos _)
  have hf : forall x, 0 < x -> f x = log (x * (2 * x) ^ √(2 * x) / 4 ^ (x / 3)) := by
    intro x h5
    have h6 := mul_pos (zero_lt_two' Real) h5
    have h7 := rpow_pos_of_pos h6 (√(2 * x))
    rw [log_div (mul_pos h5 h7).ne' (rpow_pos_of_pos four_pos _).ne']; rw [log_mul h5.ne' h7.ne']; rw [log_rpow h6]; rw [log_rpow zero_lt_four]; rw [← mul_div_right_comm]; rw [← mul_div]; rw [mul_comm x]
  have h5 : 0 < x := lt_of_lt_of_le (by norm_num1) x_large
  rw [← div_le_one (rpow_pos_of_pos four_pos x)]; rw [← div_div_eq_mul_div]; rw [← rpow_sub four_pos]; rw [←
    mul_div 2 x]; rw [mul_div_left_comm]; rw [← mul_one_sub]; rw [(by norm_num1 : (1 : Real) - 2 / 3 = 1 / 3)]; rw [mul_one_div]; rw [← log_nonpos_iff (hf' x h5).le]; rw [← hf x h5]
  -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11083): the proof was rewritten, because it was too slow
  -- Original:
  /-
  have h : ConcaveOn ℝ (Set.Ioi 0.5) f := by
    refine ((strictConcaveOn_log_Ioi.concaveOn.subset (Set.Ioi_subset_Ioi _)
      (convex_Ioi 0.5)).add ((strictConcaveOn_sqrt_mul_log_Ioi.concaveOn.comp_linearMap
      ((2 : ℝ) • LinearMap.id)).subset
      (fun a ha => lt_of_eq_of_lt _ ((mul_lt_mul_iff_right₀ two_pos).mpr ha)) (convex_Ioi 0.5))).sub
      ((convex_on_id (convex_Ioi (0.5 : ℝ))).smul (div_nonneg (log_nonneg _) _))
    norm_num
  -/
  have h : ConcaveOn Real (Set.Ioi 0.5) f := by
    apply ConcaveOn.sub
    · apply ConcaveOn.add
      · exact strictConcaveOn_log_Ioi.concaveOn.subset
          (Set.Ioi_subset_Ioi (by norm_num)) (convex_Ioi 0.5)
      convert!
        ((strictConcaveOn_sqrt_mul_log_Ioi.concaveOn.comp_linearMap ((2 : Real) • LinearMap.id)))
        using 1
      ext x
      simp only [Set.mem_Ioi, Set.mem_preimage, LinearMap.smul_apply,
        LinearMap.id_coe, id_eq, smul_eq_mul]
      rw [← mul_lt_mul_iff_right₀ (two_pos)]
      norm_num1
      rfl
    apply ConvexOn.smul
    · refine div_nonneg (log_nonneg (by norm_num1)) (by norm_num1)
    · exact convexOn_id (convex_Ioi (0.5 : Real))
  suffices exists x1 x2, 0.5 < x1 ∧ x1 < x2 ∧ x2 <= x ∧ 0 <= f x1 ∧ f x2 <= 0 by
    obtain ⟨x1, x2, h1, h2, h0, h3, h4⟩ := this
    exact (h.right_le_of_le_left'' h1 ((h1.trans h2).trans_le h0) h2 h0 (h4.trans h3)).trans h4
  refine ⟨18, 512, by norm_num1, by norm_num1, x_large, ?_, ?_⟩
  · have : √(2 * 18 : Real) = 6 := (sqrt_eq_iff_mul_self_eq_of_pos (by norm_num1)).mpr (by norm_num1)
    rw [hf _ (by norm_num1)]; rw [log_nonneg_iff (by positivity)]; rw [this]; rw [one_le_div (by norm_num1)]
    norm_num1
  · have : √(2 * 512) = 32 :=
      (sqrt_eq_iff_mul_self_eq_of_pos (by norm_num1)).mpr (by norm_num1)
    rw [hf _ (by norm_num1)]; rw [log_nonpos_iff (hf' _ (by norm_num1)).le]; rw [this]; rw [div_le_one (by positivity)]
    conv in 512 => equals 2 ^ 9 => norm_num1
    conv in 2 * 512 => equals 2 ^ 10 => norm_num1
    conv in 32 => rw [← Nat.cast_ofNat]
    rw [rpow_natCast]; rw [← pow_mul]; rw [← pow_add]
    conv in 4 => equals 2 ^ (2 : Real) => rw [rpow_two]; norm_num1
    rw [← rpow_mul]; rw [← rpow_natCast]
    on_goal 1 => apply rpow_le_rpow_of_exponent_le
    all_goals norm_num1

end Bertrand

end Real

section Nat

open Nat

/--
theorem `bertrand_main_inequality` / 定理 `bertrand_main_inequality`

English:
theorem bertrand_main_inequality
  given: {n : Nat} (n_large : 512 <= n)
  proof: by
  rw [← @cast_le Real]
  simp only [cast_mul, cast_pow, ← Real.rpow_natCast, cast_ofNat]
  refine _root_.trans ?_ (Bertrand.real_main_inequality (by exact_mod_cast n_large))
  gcongr
  · have n2_pos : 0 < 2 * n := by positivity
    exact mod_cast n2_pos
  · exact_mod_cast Real.nat_sqrt_le_real_sqrt
  · norm_num1
  · exact cast_div_le.trans (by norm_cast)

中文:
定理 bertrand_main_inequality
  条件: {n : 自然数} (n_large : 512 <= n)
  证明: by
  rw [← @cast_le Real]
  simp only [cast_mul, cast_pow, ← Real.rpow_natCast, cast_ofNat]
  refine _root_.trans ?_ (Bertrand.real_main_inequality (by exact_mod_cast n_large))
  gcongr
  · have n2_pos : 0 < 2 * n := by positivity
    exact mod_cast n2_pos
  · exact_mod_cast Real.nat_sqrt_le_real_sqrt
  · norm_num1
  · exact cast_div_le.trans (by norm_cast)

Depends on / 依赖: Bertrand, Bertrand.real_main_inequality, Real.nat_sqrt_le_real_sqrt, Real.rpow_natCast, _root_, _root_.trans, cast_div_le, cast_div_le.trans, cast_le, cast_mul, cast_ofNat, cast_pow, mod_cast, n2_pos, n_large, nat_sqrt_le_real_sqrt, norm_num1, real_main_inequality, rpow_natCast
-/
theorem bertrand_main_inequality {n : Nat} (n_large : 512 <= n) :
    n * (2 * n) ^ sqrt (2 * n) * 4 ^ (2 * n / 3) <= 4 ^ n := by
  rw [← @cast_le Real]
  simp only [cast_mul, cast_pow, ← Real.rpow_natCast, cast_ofNat]
  refine _root_.trans ?_ (Bertrand.real_main_inequality (by exact_mod_cast n_large))
  gcongr
  · have n2_pos : 0 < 2 * n := by positivity
    exact mod_cast n2_pos
  · exact_mod_cast Real.nat_sqrt_le_real_sqrt
  · norm_num1
  · exact cast_div_le.trans (by norm_cast)

/--
theorem `centralBinom_factorization_small` / 定理 `centralBinom_factorization_small`

English:
theorem centralBinom_factorization_small
  statement: (n : Nat) (n_large : 2 < n)
  proof: by
  refine (Eq.trans ?_ n.prod_pow_factorization_centralBinom).symm
  apply Finset.prod_subset
  · grw [Nat.div_le_self]
  intro x hx h2x
  rw [Finset.mem_range]; rw [Nat.lt_succ_iff] at hx h2x
  rw [not_le]; rw [div_lt_iff_lt_mul three_pos]; rw [mul_comm x] at h2x
  obtain h | h : ¬ x.Prime ∨ x <= n := by simpa [imp_iff_not_or, hx.not_gt] using no_prime x
  · rw [factorization_eq_zero_of_not_prime n.centralBinom h, Nat.pow_zero]
  · rw [factorization_centralBinom_of_two_mul_self_lt_three_mul n_large h h2x, Nat.pow_zero]

中文:
定理 centralBinom_factorization_small
  结论: (n : 自然数) (n_large : 2 < n)
  证明: by
  refine (Eq.trans ?_ n.prod_pow_factorization_centralBinom).symm
  apply Finset.prod_subset
  · grw [Nat.div_le_self]
  intro x hx h2x
  rw [Finset.mem_range]; rw [Nat.lt_succ_iff] at hx h2x
  rw [not_le]; rw [div_lt_iff_lt_mul three_pos]; rw [mul_comm x] at h2x
  obtain h | h : ¬ x.Prime ∨ x <= n := by simpa [imp_iff_not_or, hx.not_gt] using no_prime x
  · rw [factorization_eq_zero_of_not_prime n.centralBinom h, Nat.pow_zero]
  · rw [factorization_centralBinom_of_two_mul_self_lt_three_mul n_large h h2x, Nat.pow_zero]

Depends on / 依赖: Eq.trans, Finset, Finset.mem_range, Finset.prod_subset, Nat.div_le_self, Nat.lt_succ_iff, Nat.pow_zero, centralBinom, div_le_self, div_lt_iff_lt_mul, factorization_centralBinom_of_two_mul_self_lt_three_mul, factorization_eq_zero_of_not_prime, hx.not_gt, imp_iff_not_or, lt_succ_iff, mem_range, mul_comm, n.centralBinom, n.prod_pow_factorization_centralBinom, n_large
-/
theorem centralBinom_factorization_small (n : Nat) (n_large : 2 < n)
    (no_prime : forall p : Nat, p.Prime -> n < p -> 2 * n < p) :
    centralBinom n = ∏ p in Finset.range (2 * n / 3 + 1), p ^ (centralBinom n).factorization p := by
  refine (Eq.trans ?_ n.prod_pow_factorization_centralBinom).symm
  apply Finset.prod_subset
  · grw [Nat.div_le_self]
  intro x hx h2x
  rw [Finset.mem_range]; rw [Nat.lt_succ_iff] at hx h2x
  rw [not_le]; rw [div_lt_iff_lt_mul three_pos]; rw [mul_comm x] at h2x
  obtain h | h : ¬ x.Prime ∨ x <= n := by simpa [imp_iff_not_or, hx.not_gt] using no_prime x
  · rw [factorization_eq_zero_of_not_prime n.centralBinom h, Nat.pow_zero]
  · rw [factorization_centralBinom_of_two_mul_self_lt_three_mul n_large h h2x, Nat.pow_zero]

/--
theorem `centralBinom_le_of_no_bertrand_prime` / 定理 `centralBinom_le_of_no_bertrand_prime`

English:
theorem centralBinom_le_of_no_bertrand_prime
  statement: (n : Nat) (n_large : 2 < n)
  proof: by
  have n_pos : 0 < n := (Nat.zero_le _).trans_lt n_large
  have n2_pos : 1 <= 2 * n := mul_pos (zero_lt_two' Nat) n_pos
  let S := {p in Finset.range (2 * n / 3 + 1) | Nat.Prime p}
  let f x := x ^ n.centralBinom.factorization x
  have : ∏ x in S, f x = ∏ x in Finset.range (2 * n / 3 + 1), f x := by
    refine Finset.prod_filter_of_ne fun p _ h => ?_
    contrapose h; dsimp only [f]
    rw [factorization_eq_zero_of_not_prime n.centralBinom h]; rw [_root_.pow_zero]
  rw [centralBinom_factorization_small n n_large no_prime]; rw [← this]; rw [←
    Finset.prod_filter_mul_prod_filter_not S (· <= sqrt (2 * n))]
  apply mul_le_mul'
  · refine (Finset.prod_le_prod' fun p _ => (?_ : f p <= 2 * n)).trans ?_
    · exact pow_factorization_choose_le (mul_pos two_pos n_pos)
    have : (Finset.Icc 1 (sqrt (2 * n))).card = sqrt (2 * n) := by rw [card_Icc, Nat.add_sub_cancel]
    rw [Finset.prod_const]
    refine pow_right_mono₀ n2_pos ((Finset.card_le_card fun x hx => ?_).trans this.le)
    obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hx
    exact Finset.mem_Icc.mpr ⟨(Finset.mem_filter.1 h1).2.one_lt.le, h2⟩
  · refine le_trans ?_ (primorial_le_four_pow (2 * n / 3))
    refine (Finset.prod_le_prod' fun p hp => (?_ : f p <= p)).trans ?_
    · obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hp
      refine (pow_right_mono₀ (Finset.mem_filter.1 h1).2.one_lt.le ?_).trans (pow_one p).le
      exact Nat.factorization_choose_le_one (sqrt_lt'.mp <| not_le.1 h2)
    refine Finset.prod_le_prod_of_subset_of_one_le' (Finset.filter_subset _ _) ?_
    exact fun p hp _ => (Finset.mem_filter.1 hp).2.one_lt.le

中文:
定理 centralBinom_le_of_no_bertrand_prime
  结论: (n : 自然数) (n_large : 2 < n)
  证明: by
  have n_pos : 0 < n := (Nat.zero_le _).trans_lt n_large
  have n2_pos : 1 <= 2 * n := mul_pos (zero_lt_two' Nat) n_pos
  let S := {p in Finset.range (2 * n / 3 + 1) | Nat.Prime p}
  let f x := x ^ n.centralBinom.factorization x
  have : ∏ x in S, f x = ∏ x in Finset.range (2 * n / 3 + 1), f x := by
    refine Finset.prod_filter_of_ne fun p _ h => ?_
    contrapose h; dsimp only [f]
    rw [factorization_eq_zero_of_not_prime n.centralBinom h]; rw [_root_.pow_zero]
  rw [centralBinom_factorization_small n n_large no_prime]; rw [← this]; rw [←
    Finset.prod_filter_mul_prod_filter_not S (· <= sqrt (2 * n))]
  apply mul_le_mul'
  · refine (Finset.prod_le_prod' fun p _ => (?_ : f p <= 2 * n)).trans ?_
    · exact pow_factorization_choose_le (mul_pos two_pos n_pos)
    have : (Finset.Icc 1 (sqrt (2 * n))).card = sqrt (2 * n) := by rw [card_Icc, Nat.add_sub_cancel]
    rw [Finset.prod_const]
    refine pow_right_mono₀ n2_pos ((Finset.card_le_card fun x hx => ?_).trans this.le)
    obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hx
    exact Finset.mem_Icc.mpr ⟨(Finset.mem_filter.1 h1).2.one_lt.le, h2⟩
  · refine le_trans ?_ (primorial_le_four_pow (2 * n / 3))
    refine (Finset.prod_le_prod' fun p hp => (?_ : f p <= p)).trans ?_
    · obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hp
      refine (pow_right_mono₀ (Finset.mem_filter.1 h1).2.one_lt.le ?_).trans (pow_one p).le
      exact Nat.factorization_choose_le_one (sqrt_lt'.mp <| not_le.1 h2)
    refine Finset.prod_le_prod_of_subset_of_one_le' (Finset.filter_subset _ _) ?_
    exact fun p hp _ => (Finset.mem_filter.1 hp).2.one_lt.le

Depends on / 依赖: Finset, Finset.prod_filter_of_ne, Finset.range, Nat.Prime, Nat.zero_le, _root_, _root_.pow_zero, centralBinom, centralBinom_factorization_small, contrapose, factorization, factorization_eq_zero_of_not_prime, mul_pos, n.centralBinom, n.centralBinom.factorization, n2_pos, n_large, n_pos, pow_zero, prod_filter_of_ne
-/
theorem centralBinom_le_of_no_bertrand_prime (n : Nat) (n_large : 2 < n)
    (no_prime : forall p : Nat, p.Prime -> n < p -> 2 * n < p) :
    centralBinom n <= (2 * n) ^ sqrt (2 * n) * 4 ^ (2 * n / 3) := by
  have n_pos : 0 < n := (Nat.zero_le _).trans_lt n_large
  have n2_pos : 1 <= 2 * n := mul_pos (zero_lt_two' Nat) n_pos
  let S := {p in Finset.range (2 * n / 3 + 1) | Nat.Prime p}
  let f x := x ^ n.centralBinom.factorization x
  have : ∏ x in S, f x = ∏ x in Finset.range (2 * n / 3 + 1), f x := by
    refine Finset.prod_filter_of_ne fun p _ h => ?_
    contrapose h; dsimp only [f]
    rw [factorization_eq_zero_of_not_prime n.centralBinom h]; rw [_root_.pow_zero]
  rw [centralBinom_factorization_small n n_large no_prime]; rw [← this]; rw [←
    Finset.prod_filter_mul_prod_filter_not S (· <= sqrt (2 * n))]
  apply mul_le_mul'
  · refine (Finset.prod_le_prod' fun p _ => (?_ : f p <= 2 * n)).trans ?_
    · exact pow_factorization_choose_le (mul_pos two_pos n_pos)
    have : (Finset.Icc 1 (sqrt (2 * n))).card = sqrt (2 * n) := by rw [card_Icc, Nat.add_sub_cancel]
    rw [Finset.prod_const]
    refine pow_right_mono₀ n2_pos ((Finset.card_le_card fun x hx => ?_).trans this.le)
    obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hx
    exact Finset.mem_Icc.mpr ⟨(Finset.mem_filter.1 h1).2.one_lt.le, h2⟩
  · refine le_trans ?_ (primorial_le_four_pow (2 * n / 3))
    refine (Finset.prod_le_prod' fun p hp => (?_ : f p <= p)).trans ?_
    · obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hp
      refine (pow_right_mono₀ (Finset.mem_filter.1 h1).2.one_lt.le ?_).trans (pow_one p).le
      exact Nat.factorization_choose_le_one (sqrt_lt'.mp <| not_le.1 h2)
    refine Finset.prod_le_prod_of_subset_of_one_le' (Finset.filter_subset _ _) ?_
    exact fun p hp _ => (Finset.mem_filter.1 hp).2.one_lt.le

namespace Nat

/--
theorem `exists_prime_lt_and_le_two_mul_eventually` / 定理 `exists_prime_lt_and_le_two_mul_eventually`

English:
theorem exists_prime_lt_and_le_two_mul_eventually
  given: (n : Nat) (n_large : 512 <= n)
  proof: by
  have no_prime : 4 ^ n < n * n.centralBinom :=
    Nat.four_pow_lt_mul_centralBinom n (le_trans (by norm_num1) n_large)
  -- Assume there is no prime in the range.
  contrapose! no_prime
  -- Then we have the above sub-exponential bound on the size of this central binomial coefficient.
  -- We now couple this bound with an exponential lower bound on the central binomial coefficient,
  -- yielding an inequality which we have seen is false for large enough n.
  have : n.centralBinom <= (2 * n) ^ sqrt (2 * n) * 4 ^ (2 * n / 3) :=
    centralBinom_le_of_no_bertrand_prime n (lt_of_lt_of_le (by norm_num1) n_large) no_prime
  grw [this, ← mul_assoc, bertrand_main_inequality n_large]

中文:
定理 存在_prime_lt_and_le_two_mul_eventually
  条件: (n : 自然数) (n_large : 512 <= n)
  证明: by
  have no_prime : 4 ^ n < n * n.centralBinom :=
    Nat.four_pow_lt_mul_centralBinom n (le_trans (by norm_num1) n_large)
  -- Assume there is no prime in the range.
  contrapose! no_prime
  -- Then we have the above sub-exponential bound on the size of this central binomial coefficient.
  -- We now couple this bound with an exponential lower bound on the central binomial coefficient,
  -- yielding an inequality which we have seen is false for large enough n.
  have : n.centralBinom <= (2 * n) ^ sqrt (2 * n) * 4 ^ (2 * n / 3) :=
    centralBinom_le_of_no_bertrand_prime n (lt_of_lt_of_le (by norm_num1) n_large) no_prime
  grw [this, ← mul_assoc, bertrand_main_inequality n_large]

Depends on / 依赖: Nat.four_pow_lt_mul_centralBinom, centralBinom, four_pow_lt_mul_centralBinom, le_trans, n.centralBinom, n_large, no_prime, norm_num1
-/
theorem exists_prime_lt_and_le_two_mul_eventually (n : Nat) (n_large : 512 <= n) :
    exists p : Nat, p.Prime ∧ n < p ∧ p <= 2 * n := by
  have no_prime : 4 ^ n < n * n.centralBinom :=
    Nat.four_pow_lt_mul_centralBinom n (le_trans (by norm_num1) n_large)
  -- Assume there is no prime in the range.
  contrapose! no_prime
  -- Then we have the above sub-exponential bound on the size of this central binomial coefficient.
  -- We now couple this bound with an exponential lower bound on the central binomial coefficient,
  -- yielding an inequality which we have seen is false for large enough n.
  have : n.centralBinom <= (2 * n) ^ sqrt (2 * n) * 4 ^ (2 * n / 3) :=
    centralBinom_le_of_no_bertrand_prime n (lt_of_lt_of_le (by norm_num1) n_large) no_prime
  grw [this, ← mul_assoc, bertrand_main_inequality n_large]

/--
theorem `exists_prime_lt_and_le_two_mul_succ` / 定理 `exists_prime_lt_and_le_two_mul_succ`

English:
theorem exists_prime_lt_and_le_two_mul_succ
  statement: {n} (q) {p : Nat} (prime_p : Nat.Prime p)
  proof: by
  grind

中文:
定理 存在_prime_lt_and_le_two_mul_succ
  结论: {n} (q) {p : 自然数} (prime_p : 自然数.素 p)
  证明: by
  grind
-/
theorem exists_prime_lt_and_le_two_mul_succ {n} (q) {p : Nat} (prime_p : Nat.Prime p)
    (covering : p <= 2 * q) (H : n < q -> exists p : Nat, p.Prime ∧ n < p ∧ p <= 2 * n) (hn : n < p) :
    exists p : Nat, p.Prime ∧ n < p ∧ p <= 2 * n := by
  grind

/--
theorem `exists_prime_lt_and_le_two_mul` / 定理 `exists_prime_lt_and_le_two_mul`

English:
theorem exists_prime_lt_and_le_two_mul
  given: (n : Nat) (hn0 : n != 0)
  proof: by
  -- Split into cases whether `n` is large or small
  rcases lt_or_ge 511 n with h | h
  -- If `n` is large, apply the lemma derived from the inequalities on the central binomial
  -- coefficient.
  · exact exists_prime_lt_and_le_two_mul_eventually n h
  replace h : n < 521 := h.trans_lt (by norm_num1)
  revert h
  -- For small `n`, supply a list of primes to cover the initial cases.
  open Lean Elab Tactic in
  run_tac do
    for i in [317, 163, 83, 43, 23, 13, 7, 5, 3, 2] do
      let i : Term := quote i
evalTactic ←
        `(tactic| refine exists_prime_lt_and_le_two_mul_succ $i (by norm_num1) (by norm_num1) ?_)
  exact fun h2 => ⟨2, prime_two, h2, Nat.mul_le_mul_left 2 (Nat.pos_of_ne_zero hn0)⟩

alias bertrand := Nat.exists_prime_lt_and_le_two_mul

中文:
定理 存在_prime_lt_and_le_two_mul
  条件: (n : 自然数) (hn0 : n != 0)
  证明: by
  -- Split into cases whether `n` is large or small
  rcases lt_or_ge 511 n with h | h
  -- If `n` is large, apply the lemma derived from the inequalities on the central binomial
  -- coefficient.
  · exact exists_prime_lt_and_le_two_mul_eventually n h
  replace h : n < 521 := h.trans_lt (by norm_num1)
  revert h
  -- For small `n`, supply a list of primes to cover the initial cases.
  open Lean Elab Tactic in
  run_tac do
    for i in [317, 163, 83, 43, 23, 13, 7, 5, 3, 2] do
      let i : Term := quote i
evalTactic ←
        `(tactic| refine exists_prime_lt_and_le_two_mul_succ $i (by norm_num1) (by norm_num1) ?_)
  exact fun h2 => ⟨2, prime_two, h2, Nat.mul_le_mul_left 2 (Nat.pos_of_ne_zero hn0)⟩

alias bertrand := Nat.exists_prime_lt_and_le_two_mul
-/
theorem exists_prime_lt_and_le_two_mul (n : Nat) (hn0 : n != 0) :
    exists p, Nat.Prime p ∧ n < p ∧ p <= 2 * n := by
  -- Split into cases whether `n` is large or small
  rcases lt_or_ge 511 n with h | h
  -- If `n` is large, apply the lemma derived from the inequalities on the central binomial
  -- coefficient.
  · exact exists_prime_lt_and_le_two_mul_eventually n h
  replace h : n < 521 := h.trans_lt (by norm_num1)
  revert h
  -- For small `n`, supply a list of primes to cover the initial cases.
  open Lean Elab Tactic in
  run_tac do
    for i in [317, 163, 83, 43, 23, 13, 7, 5, 3, 2] do
      let i : Term := quote i
evalTactic ←
        `(tactic| refine exists_prime_lt_and_le_two_mul_succ $i (by norm_num1) (by norm_num1) ?_)
  exact fun h2 => ⟨2, prime_two, h2, Nat.mul_le_mul_left 2 (Nat.pos_of_ne_zero hn0)⟩

alias bertrand := Nat.exists_prime_lt_and_le_two_mul

end Nat

end Nat
