/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuval Filmus
-/

module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Orthogonality
public import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Algebra.Polynomial.Sequence

/-!
# Chebyshev polynomials over the reals: Chebyshev–Gauss

The Chebyshev–Gauss property calculates an integral of a polynomial of degree `< 2 * n`
with respect to the weight function `√(1 - x ^ 2)⁻¹` supported on `[-1, 1]` by a sum
over appropriate evaluations of the polynomial.

## Main statements

* integral_eq_sumZeroes: The integral of a polynomial of degree `< 2 * n` with respect to the weight
  function `√(1 - x ^ 2)⁻¹` supported on `[-1, 1]` is equal to `π` times the average of its values
  on the points `cos ((2 * i + 1) / (2 * n) * π)` for `0 ≤ i < n`.

## Implementation

The statement is proved for Chebyshev polynomials using the complex exponential representation
of `cos`, and then deduced for arbitrary polynomials.
-/
public section

namespace Polynomial.Chebyshev

open Real Polynomial Finset
open Complex (exp I)

/--
lemma `exp_sub_one_ne_zero` / 引理 `exp_sub_one_ne_zero`

English:
lemma exp_sub_one_ne_zero
  given: {n : Nat} {k : Int} (hn : n != 0) (hk : ¬ (2 * n : Int) ∣ k)
  proof: by
  contrapose hk
  obtain ⟨m, hx⟩ := Complex.exp_eq_one_iff.mp hk
  have h : k = 2 * n * m := by
    apply (@Int.cast_inj Complex _ _).mp
    linear_combination (norm := (push_cast; field [show (n : Complex) != 0 by aesop])) hx * (n / π / I)
  use m

中文:
引理 exp_sub_one_ne_zero
  条件: {n : 自然数} {k : 整数} (hn : n != 0) (hk : ¬ (2 * n : 整数) ∣ k)
  证明: by
  contrapose hk
  obtain ⟨m, hx⟩ := Complex.exp_eq_one_iff.mp hk
  have h : k = 2 * n * m := by
    apply (@Int.cast_inj Complex _ _).mp
    linear_combination (norm := (push_cast; field [show (n : Complex) != 0 by aesop])) hx * (n / π / I)
  use m
-/
private lemma exp_sub_one_ne_zero {n : Nat} {k : Int} (hn : n != 0) (hk : ¬ (2 * n : Int) ∣ k) :
    exp (k / n * π * I) != 1 := by
  contrapose hk
  obtain ⟨m, hx⟩ := Complex.exp_eq_one_iff.mp hk
  have h : k = 2 * n * m := by
    apply (@Int.cast_inj Complex _ _).mp
    linear_combination (norm := (push_cast; field [show (n : Complex) != 0 by aesop])) hx * (n / π / I)
  use m

/--
theorem `sum_exp` / 定理 `sum_exp`

English:
theorem sum_exp
  given: {n : Nat} {k : Int} (hn : n != 0) (hk : ¬ (2 * n : Int) ∣ k)
  proof: by
  suffices (∑ i in range n, exp ((k * ((2 * i + 1) / (2 * n) * π)) * I)) *
    exp (-(k / (2 * n) * π * I)) * (exp (k / n * π * I) - 1) = (-1) ^ k - 1 by
    rw [Complex.exp_neg] at this
    have hf {s a b t : Complex} (h : s * a⁻¹ * b = t) (ha : a != 0) (hb : b != 0) : s = a / b * t := by
      

中文:
定理 sum_exp
  条件: {n : 自然数} {k : 整数} (hn : n != 0) (hk : ¬ (2 * n : 整数) ∣ k)
  证明: by
  suffices (∑ i in range n, exp ((k * ((2 * i + 1) / (2 * n) * π)) * I)) *
    exp (-(k / (2 * n) * π * I)) * (exp (k / n * π * I) - 1) = (-1) ^ k - 1 by
    rw [Complex.exp_neg] at this
    have hf {s a b t : Complex} (h : s * a⁻¹ * b = t) (ha : a != 0) (hb : b != 0) : s = a / b * t := by
      
-/
private theorem sum_exp {n : Nat} {k : Int} (hn : n != 0) (hk : ¬ (2 * n : Int) ∣ k) :
    ∑ i in range n, exp ((k * ((2 * i + 1) / (2 * n) * π)) * I) =
      (exp (k / (2 * n) * π * I) / (exp (k / n * π * I) - 1)) * ((-1) ^ k - 1) := by
  suffices (∑ i in range n, exp ((k * ((2 * i + 1) / (2 * n) * π)) * I)) *
    exp (-(k / (2 * n) * π * I)) * (exp (k / n * π * I) - 1) = (-1) ^ k - 1 by
    rw [Complex.exp_neg] at this
    have hf {s a b t : Complex} (h : s * a⁻¹ * b = t) (ha : a != 0) (hb : b != 0) : s = a / b * t := by
      linear_combination (norm := field) h * a / b
    apply hf this (Complex.exp_ne_zero _) (by grind [exp_sub_one_ne_zero])
  convert! geom_sum_mul (exp (k / n * π * I)) n using 1
  · simp_rw [sum_mul]
    congr! 1 with i hi
    rw [← Complex.exp_nat_mul]; rw [← Complex.exp_add]
    grind
  · rw [← Complex.exp_nat_mul,
      show (n * (k / n * π * I)) = k * (π * I) by field [show (n : Complex) != 0 by aesop],
      Complex.exp_int_mul, Complex.exp_pi_mul_I]

/--
Definition of `sumZeroes` / `sumZeroes` 的定义

English:
definition sumZeroes
  signature: (n : Nat) (P : Real[X])
  body: (π / n) * ∑ i in range n, P.eval (cos ((2 * i + 1) / (2 * n) * π))

@[simp]

中文:
定义 sumZeroes
  签名: (n : 自然数) (P : 实数[X])
  定义体: (π / n) * ∑ i in range n, P.eval (cos ((2 * i + 1) / (2 * n) * π))

@[simp]

Depends on / 依赖: P.eval
-/
noncomputable def sumZeroes (n : Nat) (P : Real[X]) : Real :=
    (π / n) * ∑ i in range n, P.eval (cos ((2 * i + 1) / (2 * n) * π))

@[simp]
/--
theorem `sumZeroes_sum` / 定理 `sumZeroes_sum`

English:
theorem sumZeroes_sum
  given: (n : Nat) {ι : Type*} (s : Finset ι) (P : ι -> Real[X])
  proof: by
  simp_rw [sumZeroes, eval_finsetSum]
  rw [sum_comm]; rw [mul_sum]

@[simp]

中文:
定理 sumZeroes_sum
  条件: (n : 自然数) {ι : 类型} (s : Finset ι) (P : ι -> 实数[X])
  证明: by
  simp_rw [sumZeroes, eval_finsetSum]
  rw [sum_comm]; rw [mul_sum]

@[simp]

Depends on / 依赖: eval_finsetSum, mul_sum, simp_rw, sumZeroes, sum_comm
-/
theorem sumZeroes_sum (n : Nat) {ι : Type*} (s : Finset ι) (P : ι -> Real[X]) :
    sumZeroes n (∑ i in s, P i) = ∑ i in s, sumZeroes n (P i) := by
  simp_rw [sumZeroes, eval_finsetSum]
  rw [sum_comm]; rw [mul_sum]

@[simp]
/--
theorem `sumZeroes_smul` / 定理 `sumZeroes_smul`

English:
theorem sumZeroes_smul
  given: (n : Nat) (c : Real) (P : Real[X])
  proof: by
  simp_rw [sumZeroes, eval_smul, ← smul_sum, smul_eq_mul]; ring

中文:
定理 sumZeroes_smul
  条件: (n : 自然数) (c : 实数) (P : 实数[X])
  证明: by
  simp_rw [sumZeroes, eval_smul, ← smul_sum, smul_eq_mul]; ring

Depends on / 依赖: eval_smul, simp_rw, smul_eq_mul, smul_sum, sumZeroes
-/
theorem sumZeroes_smul (n : Nat) (c : Real) (P : Real[X]) :
    sumZeroes n (c • P) = c * sumZeroes n P := by
  simp_rw [sumZeroes, eval_smul, ← smul_sum, smul_eq_mul]; ring

/--
theorem `sumZeroes_T_zero` / 定理 `sumZeroes_T_zero`

English:
theorem sumZeroes_T_zero
  given: {n : Nat} (hn : n != 0)
  statement: sumZeroes n (T Real 0) = π
  proof: by
  simp [sumZeroes, show π / n * n = π by field]

中文:
定理 sumZeroes_T_zero
  条件: {n : 自然数} (hn : n != 0)
  结论: sumZeroes n (T 实数 0) = π
  证明: by
  simp [sumZeroes, show π / n * n = π by field]

Depends on / 依赖: sumZeroes
-/
theorem sumZeroes_T_zero {n : Nat} (hn : n != 0) : sumZeroes n (T Real 0) = π := by
  simp [sumZeroes, show π / n * n = π by field]

/--
theorem `sumZeroes_T_of_not_dvd` / 定理 `sumZeroes_T_of_not_dvd`

English:
theorem sumZeroes_T_of_not_dvd
  given: {n : Nat} {k : Int} (hk : ¬ (2 * n : Int) ∣ k)
  proof: by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [sumZeroes]
  suffices ∑ i in range n, 2 * cos (k * ((2 * i + 1) / (2 * n) * π)) = 0 by
    rw [sumZeroes]; rw [mul_eq_zero_iff_left (by aesop)]
    rw [← mul_sum]; rw [mul_eq_zero_iff_left (by norm_num)] at this
    simpa [T_real_cos]
  suffices (∑ i 

中文:
定理 sumZeroes_T_of_not_dvd
  条件: {n : 自然数} {k : 整数} (hk : ¬ (2 * n : 整数) ∣ k)
  证明: by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [sumZeroes]
  suffices ∑ i in range n, 2 * cos (k * ((2 * i + 1) / (2 * n) * π)) = 0 by
    rw [sumZeroes]; rw [mul_eq_zero_iff_left (by aesop)]
    rw [← mul_sum]; rw [mul_eq_zero_iff_left (by norm_num)] at this
    simpa [T_real_cos]
  suffices (∑ i 

Depends on / 依赖: Complex.cos, Complex.two_cos, T_real_cos, eq_or_ne, mul_eq_zero_iff_left, mul_sum, neg_mul, simp_rw, sumZeroes, two_cos
-/
theorem sumZeroes_T_of_not_dvd {n : Nat} {k : Int} (hk : ¬ (2 * n : Int) ∣ k) :
    sumZeroes n (T Real k) = 0 := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [sumZeroes]
  suffices ∑ i in range n, 2 * cos (k * ((2 * i + 1) / (2 * n) * π)) = 0 by
    rw [sumZeroes]; rw [mul_eq_zero_iff_left (by aesop)]
    rw [← mul_sum]; rw [mul_eq_zero_iff_left (by norm_num)] at this
    simpa [T_real_cos]
  suffices (∑ i in range n, 2 * cos (k * ((2 * i + 1) / (2 * n) * π)) : Complex) = 0 by norm_cast at this ⊢
  suffices ∑ i in range n, 2 * Complex.cos (k * ((2 * i + 1) / (2 * n) * π)) = 0 by aesop
  simp_rw [Complex.two_cos, ← neg_mul, ← Int.cast_neg]
  have : (-1 : Complex) ^ (-k) = (-1) ^ k := by rw [← Int.cast_negOnePow, ← Int.cast_negOnePow]; simp
  rw [sum_add_distrib]; rw [sum_exp hn hk]; rw [sum_exp hn (by aesop)]; rw [Int.cast_neg]; rw [neg_div]; rw [neg_mul]; rw [neg_mul]; rw [Complex.exp_neg]; rw [neg_div]; rw [neg_mul]; rw [neg_mul]; rw [Complex.exp_neg]; rw [this]; rw [← add_mul]; rw [mul_eq_zero_of_left]
  set z := exp (k / (2 * n) * π * I) with hz
  have hz₂ : exp (k / n * π * I) = z ^ 2 := by rw [hz, ← Complex.exp_nat_mul]; grind
  rw [hz₂]; rw [← inv_pow z 2]
  field [show z != 0 by grind [Complex.exp_ne_zero],
    show (z ^ 2 - 1 != 0) ∧ (1 - z ^ 2 != 0) by grind [exp_sub_one_ne_zero]]

/--
theorem `integral_eq_sumZeroes` / 定理 `integral_eq_sumZeroes`

English:
theorem integral_eq_sumZeroes
  given: {n : Nat} {P : Real[X]} (hn : n != 0) (hP : P.degree < 2 * n)
  proof: by
  have hmem : P in degreeLT Real (2 * n) := by rwa [mem_degreeLT]
  rw [← Sequence.span_degreeLT (chebyshevTsequence Real) (by simp)]; rw [show Set.Iio (2 * n) = Finset.range (2 * n) by simp]; rw [Submodule.mem_span_image_finset_iff_exists_fun'] at hmem
  obtain ⟨c, rfl⟩ := hmem
  simp_rw [eval_f

中文:
定理 integral_eq_sumZeroes
  条件: {n : 自然数} {P : 实数[X]} (hn : n != 0) (hP : P.degree < 2 * n)
  证明: by
  have hmem : P in degreeLT Real (2 * n) := by rwa [mem_degreeLT]
  rw [← Sequence.span_degreeLT (chebyshevTsequence Real) (by simp)]; rw [show Set.Iio (2 * n) = Finset.range (2 * n) by simp]; rw [Submodule.mem_span_image_finset_iff_exists_fun'] at hmem
  obtain ⟨c, rfl⟩ := hmem
  simp_rw [eval_f

Depends on / 依赖: Finset, Finset.range, MeasureTheory, MeasureTheory.integral_const_mul, MeasureTheory.integral_finsetSum, Sequence, Sequence.span_degreeLT, Set.Iio, Submodule, Submodule.mem_span_image_finset_iff_exists_fun, by_ca, chebyshevTsequence, degreeLT, eval_finsetSum, eval_smul, hrange, integral_const_mul, integral_finsetSum, mem_degreeLT, mem_span_image_finset_iff_exists_fun
-/
theorem integral_eq_sumZeroes {n : Nat} {P : Real[X]} (hn : n != 0) (hP : P.degree < 2 * n) :
    ∫ x, P.eval x ∂measureT = sumZeroes n P := by
  have hmem : P in degreeLT Real (2 * n) := by rwa [mem_degreeLT]
  rw [← Sequence.span_degreeLT (chebyshevTsequence Real) (by simp)]; rw [show Set.Iio (2 * n) = Finset.range (2 * n) by simp]; rw [Submodule.mem_span_image_finset_iff_exists_fun'] at hmem
  obtain ⟨c, rfl⟩ := hmem
  simp_rw [eval_finsetSum, eval_smul]
  rw [MeasureTheory.integral_finsetSum]; rw [sumZeroes_sum]
  · simp_rw [sumZeroes_smul, smul_eq_mul, MeasureTheory.integral_const_mul]
    congr! with i hrange
    simp_rw [chebyshevTsequence]
    by_cases i = 0
    case pos hi => rw [hi, Nat.cast_zero, integral_eval_T_real_measureT_zero, sumZeroes_T_zero hn]
    case neg hi =>
      have : ¬ (2 * n : Int) ∣ i := by
        refine (Int.not_dvd_iff_lt_mul_succ _ (by grind)).mpr ⟨0, ⟨by grind, ?_⟩⟩
        rw_mod_cast [zero_add, mul_one]
        exact mem_range.mp hrange
      rw [integral_eval_T_real_measureT_of_ne_zero (by grind)]; rw [sumZeroes_T_of_not_dvd this]
  · simp_rw [← eval_smul]
    exact fun i hi => integrable_measureT (by fun_prop)

end Polynomial.Chebyshev
