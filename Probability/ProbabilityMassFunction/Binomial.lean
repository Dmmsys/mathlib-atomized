/-
Copyright (c) 2023 Joachim Breitner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joachim Breitner
-/
module

public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Probability.Distributions.Binomial
public import Mathlib.Probability.ProbabilityMassFunction.Constructions
public import Mathlib.Tactic.FinCases

/-!
# The binomial distribution

This file defines the probability mass function of the binomial distribution.

## Main results

* `binomial_one_eq_bernoulli`: For `n = 1`, it is equal to `PMF.bernoulli`.
-/

@[expose] public section

namespace PMF

open ENNReal NNReal
/-- The binomial `PMF`: the probability of observing exactly `i` “heads” in a sequence of `n`
independent coin tosses, each having probability `p` of coming up “heads”. -/
@[deprecated ProbabilityTheory.binomial (since := "2026-04-07")]
/--
Definition of `binomial` / `binomial` 的定义

English:
definition binomial
  signature: (p : Real>=0) (h : p <= 1) (n : Nat)
  body: .ofFintype (fun i =>
      ↑(p ^ (i : Nat) * (1 - p) ^ ((Fin.last n - i) : Nat) * (n.choose i : Nat))) (by
    norm_cast
    convert! (add_pow p (1 - p) n).symm
    · rw [Finset.sum_fin_eq_sum_range]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mem_range] at hi
      rw [dif_po

中文:
定义 binomial
  签名: (p : 实数>=0) (h : p <= 1) (n : 自然数)
  定义体: .ofFintype (fun i =>
      ↑(p ^ (i : Nat) * (1 - p) ^ ((Fin.last n - i) : Nat) * (n.choose i : Nat))) (by
    norm_cast
    convert! (add_pow p (1 - p) n).symm
    · rw [Finset.sum_fin_eq_sum_range]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mem_range] at hi
      rw [dif_po

Depends on / 依赖: Fin.last, Finset, Finset.mem_range, Finset.sum_congr, Finset.sum_fin_eq_sum_range, add_pow, add_tsub_cancel_of_le, convert, dif_pos, mem_range, mod_cast, n.choose, ofFintype, one_pow, sum_congr, sum_fin_eq_sum_range
-/
def binomial (p : Real>=0) (h : p <= 1) (n : Nat) : PMF (Fin (n + 1)) :=
  .ofFintype (fun i =>
      ↑(p ^ (i : Nat) * (1 - p) ^ ((Fin.last n - i) : Nat) * (n.choose i : Nat))) (by
    norm_cast
    convert! (add_pow p (1 - p) n).symm
    · rw [Finset.sum_fin_eq_sum_range]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mem_range] at hi
      rw [dif_pos hi]
    · rw [add_tsub_cancel_of_le (mod_cast h), one_pow])

@[deprecated ProbabilityTheory.binomial_real_singleton (since := "2026-04-07")]
/--
theorem `binomial_apply` / 定理 `binomial_apply`

English:
theorem binomial_apply
  given: (p : Real>=0) (h : p <= 1) (n : Nat) (i : Fin (n + 1))
  proof: by
  simp [binomial]

@[deprecated ProbabilityTheory.binomial_real_zero (since := "2026-04-07")]

中文:
定理 binomial_apply
  条件: (p : 实数>=0) (h : p <= 1) (n : 自然数) (i : 有限集 (n + 1))
  证明: by
  simp [binomial]

@[deprecated ProbabilityTheory.binomial_real_zero (since := "2026-04-07")]

Depends on / 依赖: binomial
-/
theorem binomial_apply (p : Real>=0) (h : p <= 1) (n : Nat) (i : Fin (n + 1)) :
    binomial p h n i = p ^ (i : Nat) * (1 - p) ^ ((Fin.last n - i) : Nat) * (n.choose i : Nat) := by
  simp [binomial]

@[deprecated ProbabilityTheory.binomial_real_zero (since := "2026-04-07")]
/--
theorem `binomial_apply_zero` / 定理 `binomial_apply_zero`

English:
theorem binomial_apply_zero
  given: (p : Real>=0) (h : p <= 1) (n : Nat)
  proof: by
  simp [binomial_apply]

@[deprecated ProbabilityTheory.binomial_real_self (since := "2026-04-07")]

中文:
定理 binomial_apply_zero
  条件: (p : 实数>=0) (h : p <= 1) (n : 自然数)
  证明: by
  simp [binomial_apply]

@[deprecated ProbabilityTheory.binomial_real_self (since := "2026-04-07")]

Depends on / 依赖: binomial_apply
-/
theorem binomial_apply_zero (p : Real>=0) (h : p <= 1) (n : Nat) :
    binomial p h n 0 = (1 - p) ^ n := by
  simp [binomial_apply]

@[deprecated ProbabilityTheory.binomial_real_self (since := "2026-04-07")]
/--
theorem `binomial_apply_last` / 定理 `binomial_apply_last`

English:
theorem binomial_apply_last
  given: (p : Real>=0) (h : p <= 1) (n : Nat)
  proof: by
  simp [binomial_apply]

@[deprecated ProbabilityTheory.binomial_real_self (since := "2026-04-07")]

中文:
定理 binomial_apply_last
  条件: (p : 实数>=0) (h : p <= 1) (n : 自然数)
  证明: by
  simp [binomial_apply]

@[deprecated ProbabilityTheory.binomial_real_self (since := "2026-04-07")]

Depends on / 依赖: binomial_apply
-/
theorem binomial_apply_last (p : Real>=0) (h : p <= 1) (n : Nat) :
    binomial p h n (.last n) = p ^ n := by
  simp [binomial_apply]

@[deprecated ProbabilityTheory.binomial_real_self (since := "2026-04-07")]
/--
theorem `binomial_apply_self` / 定理 `binomial_apply_self`

English:
theorem binomial_apply_self
  given: (p : Real>=0) (h : p <= 1) (n : Nat)
  proof: by simp [binomial_apply_last]

中文:
定理 binomial_apply_self
  条件: (p : 实数>=0) (h : p <= 1) (n : 自然数)
  证明: by simp [binomial_apply_last]

Depends on / 依赖: binomial_apply_last
-/
theorem binomial_apply_self (p : Real>=0) (h : p <= 1) (n : Nat) :
    binomial p h n (.last n) = p ^ n := by simp [binomial_apply_last]

/-- The binomial distribution on one coin is the Bernoulli distribution. -/
@[deprecated ProbabilityTheory.binomial_one_eq_bernoulliMeasure (since := "2026-05-31")]
/--
theorem `binomial_one_eq_bernoulli` / 定理 `binomial_one_eq_bernoulli`

English:
theorem binomial_one_eq_bernoulli
  given: (p : Real>=0) (h : p <= 1)
  proof: by
  ext i; fin_cases i <;> simp [binomial_apply, bernoulli_apply]

@[deprecated ProbabilityTheory.binomial_singleton (since := "2026-04-07")]

中文:
定理 binomial_one_eq_bernoulli
  条件: (p : 实数>=0) (h : p <= 1)
  证明: by
  ext i; fin_cases i <;> simp [binomial_apply, bernoulli_apply]

@[deprecated ProbabilityTheory.binomial_singleton (since := "2026-04-07")]

Depends on / 依赖: bernoulli_apply, binomial_apply, fin_cases
-/
theorem binomial_one_eq_bernoulli (p : Real>=0) (h : p <= 1) :
    binomial p h 1 = (bernoulli p h).map (cond · 1 0) := by
  ext i; fin_cases i <;> simp [binomial_apply, bernoulli_apply]

@[deprecated ProbabilityTheory.binomial_singleton (since := "2026-04-07")]
/--
theorem `binomial_apply_of_le` / 定理 `binomial_apply_of_le`

English:
theorem binomial_apply_of_le
  given: {k b : Nat} (hb : k <= b) {x : Real>=0} (h : x <= 1)
  proof: by
  have eq0 : k % (b + 1) = k := by simpa using Order.lt_add_one_iff.mpr hb
  have eq1 : 1 - (x : Real>=0∞) = ENNReal.ofReal (1 - x : Real) := by norm_cast
  have : (1 - (x : Real)) >= 0 := by simpa
  rwa [Fin.ofNat_eq_cast, PMF.binomial_apply, Fin.val_natCast, Fin.val_last, eq0, eq1,
    coe_nnre

中文:
定理 binomial_apply_of_le
  条件: {k b : 自然数} (hb : k <= b) {x : 实数>=0} (h : x <= 1)
  证明: by
  have eq0 : k % (b + 1) = k := by simpa using Order.lt_add_one_iff.mpr hb
  have eq1 : 1 - (x : Real>=0∞) = ENNReal.ofReal (1 - x : Real) := by norm_cast
  have : (1 - (x : Real)) >= 0 := by simpa
  rwa [Fin.ofNat_eq_cast, PMF.binomial_apply, Fin.val_natCast, Fin.val_last, eq0, eq1,
    coe_nnre

Depends on / 依赖: ENNReal, ENNReal.ofReal, Fin.ofNat_eq_cast, Fin.val_last, Fin.val_natCast, Order.lt_add_one_iff.mpr, PMF.binomial_apply, all_goals, binomial_apply, coe_nnreal_eq, lt_add_one_iff, mul_rotate, ofNat_eq_cast, ofReal, ofReal_mul, ofReal_natCast, ofReal_pow, val_last, val_natCast
-/
theorem binomial_apply_of_le {k b : Nat} (hb : k <= b) {x : Real>=0} (h : x <= 1) :
    ENNReal.ofReal ((b.choose k) * x ^ k * (1 - x) ^ (b - k))
    = PMF.binomial x h b (Fin.ofNat (b + 1) k) := by
  have eq0 : k % (b + 1) = k := by simpa using Order.lt_add_one_iff.mpr hb
  have eq1 : 1 - (x : Real>=0∞) = ENNReal.ofReal (1 - x : Real) := by norm_cast
  have : (1 - (x : Real)) >= 0 := by simpa
  rwa [Fin.ofNat_eq_cast, PMF.binomial_apply, Fin.val_natCast, Fin.val_last, eq0, eq1,
    coe_nnreal_eq x, mul_rotate, ofReal_mul, ofReal_mul, ofReal_pow, ofReal_pow, ofReal_natCast]
  all_goals positivity

end PMF
