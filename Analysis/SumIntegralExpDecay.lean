/-
Copyright (c) 2025 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Pietro Monticone
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SumIntegralComparisons

/-!
# Bounds for sums and integrals of `x ^ k * exp (-c * x)`

We bound the integral and sums of `x ^ k * exp (-c * x)` by `k ! / c ^ (k + 1)`,
using the Gamma function.
-/

open scoped Nat
open Real MeasureTheory Set Filter

public section

/--
lemma `intervalIntegral_pow_mul_exp_neg_le` / 引理 `intervalIntegral_pow_mul_exp_neg_le`

English:
lemma intervalIntegral_pow_mul_exp_neg_le
  given: {k : Nat} {M c : Real} (hM : 0 <= M) (hc : 0 < c)
  proof: by
  have hk : (0 : Real) < ↑k + 1 := by positivity
  have key := integral_rpow_mul_exp_neg_mul_Ioi hk hc
  have hint : IntegrableOn (fun x => x ^ ((↑k + 1 : Real) - 1) * rexp (-(c * x))) (Ioi 0) :=
    .of_integral_ne_zero (by rw [key]; positivity)
  rw [intervalIntegral.integral_of_le hM]
  calc ∫

中文:
引理 interval整数egral_pow_mul_exp_neg_le
  条件: {k : 自然数} {M c : 实数} (hM : 0 <= M) (hc : 0 < c)
  证明: by
  have hk : (0 : Real) < ↑k + 1 := by positivity
  have key := integral_rpow_mul_exp_neg_mul_Ioi hk hc
  have hint : IntegrableOn (fun x => x ^ ((↑k + 1 : Real) - 1) * rexp (-(c * x))) (Ioi 0) :=
    .of_integral_ne_zero (by rw [key]; positivity)
  rw [intervalIntegral.integral_of_le hM]
  calc ∫

Depends on / 依赖: IntegrableOn, add_sub_cancel_right, integral_of_le, integral_rpow_mul_exp_neg_mul_Ioi, intervalIntegral, intervalIntegral.integral_of_le, of_integral_ne_zero, rpow_natCast
-/
lemma intervalIntegral_pow_mul_exp_neg_le {k : Nat} {M c : Real} (hM : 0 <= M) (hc : 0 < c) :
    ∫ x in (0 : Real)..M, x ^ k * rexp (- (c * x)) <= k ! / c ^ (k + 1) := by
  have hk : (0 : Real) < ↑k + 1 := by positivity
  have key := integral_rpow_mul_exp_neg_mul_Ioi hk hc
  have hint : IntegrableOn (fun x => x ^ ((↑k + 1 : Real) - 1) * rexp (-(c * x))) (Ioi 0) :=
    .of_integral_ne_zero (by rw [key]; positivity)
  rw [intervalIntegral.integral_of_le hM]
  calc ∫ x in Ioc (0 : Real) M, x ^ k * rexp (-(c * x))
    _ = ∫ x in Ioc (0 : Real) M, x ^ ((↑k + 1 : Real) - 1) * rexp (-(c * x)) := by
        simp [add_sub_cancel_right, rpow_natCast]
    _ <= ∫ x in Ioi (0 : Real), x ^ ((↑k + 1 : Real) - 1) * rexp (-(c * x)) := by
        apply setIntegral_mono_set hint _ Ioc_subset_Ioi_self.eventuallyLE
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
        exact mul_nonneg (rpow_nonneg hx.le _) (exp_nonneg _)
    _ = k ! / c ^ (k + 1) := by
        simp_rw [key, Gamma_nat_eq_factorial, div_eq_mul_inv,
          one_mul, mul_comm, inv_rpow hc.le, ← rpow_natCast]
        norm_cast

/--
lemma `sum_Ico_pow_mul_exp_neg_le` / 引理 `sum_Ico_pow_mul_exp_neg_le`

English:
lemma sum_Ico_pow_mul_exp_neg_le
  given: {k : Nat} {M : Nat} {c : Real} (hc : 0 < c)
  proof: calc
  ∑ i in Finset.Ico 0 M, i ^ k * rexp (- (c * i))
  _ <= ∫ x in (0 : Nat)..M, x ^ k * rexp (- (c * (x - 1))) := by
    apply sum_mul_Ico_le_integral_of_monotone_antitone
      (f := fun x => x ^ k) (g := fun x => rexp (- (c * x)))
    · exact Nat.zero_le M
    · intro x hx y hy hxy
      apply 

中文:
引理 sum_Ico_pow_mul_exp_neg_le
  条件: {k : 自然数} {M : 自然数} {c : 实数} (hc : 0 < c)
  证明: calc
  ∑ i in Finset.Ico 0 M, i ^ k * rexp (- (c * i))
  _ <= ∫ x in (0 : Nat)..M, x ^ k * rexp (- (c * (x - 1))) := by
    apply sum_mul_Ico_le_integral_of_monotone_antitone
      (f := fun x => x ^ k) (g := fun x => rexp (- (c * x)))
    · exact Nat.zero_le M
    · intro x hx y hy hxy
      apply 

Depends on / 依赖: SemilatticeInf, isCofilteredOrEmpty_of_semilatticeInf
-/
lemma sum_Ico_pow_mul_exp_neg_le {k : Nat} {M : Nat} {c : Real} (hc : 0 < c) :
    ∑ i in Finset.Ico 0 M, i ^ k * rexp (- (c * i)) <= rexp c * k ! / c ^ (k + 1) := calc
  ∑ i in Finset.Ico 0 M, i ^ k * rexp (- (c * i))
  _ <= ∫ x in (0 : Nat)..M, x ^ k * rexp (- (c * (x - 1))) := by
    apply sum_mul_Ico_le_integral_of_monotone_antitone
      (f := fun x => x ^ k) (g := fun x => rexp (- (c * x)))
    · exact Nat.zero_le M
    · intro x hx y hy hxy
      apply pow_le_pow_left₀ (by simpa using hx.1) hxy
    · intro x hx y hy hxy
      apply exp_monotone
      simp only [neg_le_neg_iff]
      gcongr
    · simp
    · apply exp_nonneg
  _ <= (k ! / c ^ (k + 1)) * rexp c := by
    simp only [mul_sub, mul_one, neg_sub, CharP.cast_eq_zero]
    simp only [sub_eq_add_neg, Real.exp_add, mul_comm (rexp c), ← mul_assoc]
    rw [intervalIntegral.integral_mul_const]
    gcongr
    exact intervalIntegral_pow_mul_exp_neg_le (by simp) hc
  _ = _ := by ring

/--
lemma `sum_Iic_pow_mul_exp_neg_le` / 引理 `sum_Iic_pow_mul_exp_neg_le`

English:
lemma sum_Iic_pow_mul_exp_neg_le
  given: {k : Nat} {M : Nat} {c : Real} (hc : 0 < c)
  proof: sum_Ico_pow_mul_exp_neg_le (M := M + 1) hc

中文:
引理 sum_Iic_pow_mul_exp_neg_le
  条件: {k : 自然数} {M : 自然数} {c : 实数} (hc : 0 < c)
  证明: sum_Ico_pow_mul_exp_neg_le (M := M + 1) hc

Depends on / 依赖: SemilatticeInf, isCofiltered_of_semilatticeInf_nonempty, sum_Ico_pow_mul_exp_neg_le
-/
lemma sum_Iic_pow_mul_exp_neg_le {k : Nat} {M : Nat} {c : Real} (hc : 0 < c) :
    ∑ i in Finset.Iic M, i ^ k * rexp (- (c * i)) <= rexp c * k ! / c ^ (k + 1) :=
  sum_Ico_pow_mul_exp_neg_le (M := M + 1) hc

/--
lemma `sum_Iic_pow_mul_two_pow_neg_le` / 引理 `sum_Iic_pow_mul_two_pow_neg_le`

English:
lemma sum_Iic_pow_mul_two_pow_neg_le
  given: {k : Nat} {M : Nat} {c : Real} (hc : 0 < c)
  proof: by
  have A (i : Nat) : (2 : Real) ^ (- (c * i)) = rexp (- (Real.log 2 * c) * i) := by
    conv_lhs => rw [← exp_log zero_lt_two, ← exp_mul]
    congr 1
    ring
  simp only [A, neg_mul]
  apply (sum_Iic_pow_mul_exp_neg_le (by positivity)).trans_eq
  rw [exp_mul]; rw [exp_log zero_lt_two]

中文:
引理 sum_Iic_pow_mul_two_pow_neg_le
  条件: {k : 自然数} {M : 自然数} {c : 实数} (hc : 0 < c)
  证明: by
  have A (i : Nat) : (2 : Real) ^ (- (c * i)) = rexp (- (Real.log 2 * c) * i) := by
    conv_lhs => rw [← exp_log zero_lt_two, ← exp_mul]
    congr 1
    ring
  simp only [A, neg_mul]
  apply (sum_Iic_pow_mul_exp_neg_le (by positivity)).trans_eq
  rw [exp_mul]; rw [exp_log zero_lt_two]

Depends on / 依赖: Preorder, Real.log, conv_lhs, exp_log, exp_mul, isCofilteredOrEmpty_of_directed_ge, neg_mul, sum_Iic_pow_mul_exp_neg_le, trans_eq, zero_lt_two
-/
lemma sum_Iic_pow_mul_two_pow_neg_le {k : Nat} {M : Nat} {c : Real} (hc : 0 < c) :
    ∑ i in Finset.Iic M, i ^ k * (2 : Real) ^ (- (c * i)) <=
      2 ^ c * k ! / (Real.log 2 * c) ^ (k + 1) := by
  have A (i : Nat) : (2 : Real) ^ (- (c * i)) = rexp (- (Real.log 2 * c) * i) := by
    conv_lhs => rw [← exp_log zero_lt_two, ← exp_mul]
    congr 1
    ring
  simp only [A, neg_mul]
  apply (sum_Iic_pow_mul_exp_neg_le (by positivity)).trans_eq
  rw [exp_mul]; rw [exp_log zero_lt_two]

end
