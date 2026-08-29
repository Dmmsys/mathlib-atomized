/-
Copyright (c) 2021 Ashvni Narayanan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvni Narayanan, David Loeffler
-/
module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Data.Nat.Choose.Cast
public import Mathlib.NumberTheory.Bernoulli

/-!
# Bernoulli polynomials

The [Bernoulli polynomials](https://en.wikipedia.org/wiki/Bernoulli_polynomials)
are an important tool obtained from Bernoulli numbers.

## Mathematical overview

The $n$-th Bernoulli polynomial is defined as
$$ B_n(X) = ∑_{k = 0}^n {n \choose k} (-1)^k B_k X^{n - k} $$
where $B_k$ is the $k$-th Bernoulli number. The Bernoulli polynomials are generating functions,
$$ \frac{t e^{tX} }{ e^t - 1} = ∑_{n = 0}^{\infty} B_n(X) \frac{t^n}{n!} $$

## Implementation detail

Bernoulli polynomials are defined using `bernoulli`, the Bernoulli numbers.

## Main theorems

- `Polynomial.sum_bernoulli`: The sum of the $k^\mathrm{th}$ Bernoulli polynomial with binomial
  coefficients up to `n` is `(n + 1) * X^n`.
- `Polynomial.bernoulli_generating_function`: The Bernoulli polynomials act as generating functions
  for the exponential.

-/

@[expose] public section


noncomputable section

open Nat Polynomial

open Nat Finset

namespace Polynomial

/--
Definition of `bernoulli` / `bernoulli` 的定义

English:
definition bernoulli
  signature: (n : Nat)
  body: ∑ i in range (n + 1), Polynomial.monomial (n - i) (_root_.bernoulli i * choose n i)

中文:
定义 bernoulli
  签名: (n : 自然数)
  定义体: ∑ i in range (n + 1), Polynomial.monomial (n - i) (_root_.bernoulli i * choose n i)

Depends on / 依赖: Polynomial, Polynomial.monomial, _root_, _root_.bernoulli, bernoulli, monomial
-/
def bernoulli (n : Nat) : Rat[X] :=
  ∑ i in range (n + 1), Polynomial.monomial (n - i) (_root_.bernoulli i * choose n i)

/--
theorem `bernoulli_def` / 定理 `bernoulli_def`

English:
theorem bernoulli_def
  given: (n : Nat)
  statement: bernoulli n =
  proof: by
  rw [← sum_range_reflect]; rw [add_succ_sub_one]; rw [add_zero]; rw [bernoulli]
  apply sum_congr rfl
  rintro x hx
  rw [mem_range_succ_iff] at hx
  rw [choose_symm hx]; rw [tsub_tsub_cancel_of_le hx]

中文:
定理 bernoulli_def
  条件: (n : 自然数)
  结论: bernoulli n =
  证明: by
  rw [← sum_range_reflect]; rw [add_succ_sub_one]; rw [add_zero]; rw [bernoulli]
  apply sum_congr rfl
  rintro x hx
  rw [mem_range_succ_iff] at hx
  rw [choose_symm hx]; rw [tsub_tsub_cancel_of_le hx]

Depends on / 依赖: add_succ_sub_one, add_zero, bernoulli, choose_symm, mem_range_succ_iff, sum_congr, sum_range_reflect, tsub_tsub_cancel_of_le
-/
theorem bernoulli_def (n : Nat) : bernoulli n =
    ∑ i in range (n + 1), Polynomial.monomial i (_root_.bernoulli (n - i) * choose n i) := by
  rw [← sum_range_reflect]; rw [add_succ_sub_one]; rw [add_zero]; rw [bernoulli]
  apply sum_congr rfl
  rintro x hx
  rw [mem_range_succ_iff] at hx
  rw [choose_symm hx]; rw [tsub_tsub_cancel_of_le hx]

/--
theorem `coeff_bernoulli` / 定理 `coeff_bernoulli`

English:
theorem coeff_bernoulli
  given: (n i : Nat)
  proof: by
  simp only [bernoulli, finsetSum_coeff, coeff_monomial]
  split_ifs with h
  · convert! sum_ite_eq_of_mem (range (n + 1)) (n - i) _ (by grind) using 3 <;> grind [choose_symm]
· exact Finset.sum_eq_zero by grind

中文:
定理 coeff_bernoulli
  条件: (n i : 自然数)
  证明: by
  simp only [bernoulli, finsetSum_coeff, coeff_monomial]
  split_ifs with h
  · convert! sum_ite_eq_of_mem (range (n + 1)) (n - i) _ (by grind) using 3 <;> grind [choose_symm]
· exact Finset.sum_eq_zero by grind

Depends on / 依赖: Finset, Finset.sum_eq_zero, bernoulli, choose_symm, coeff_monomial, convert, finsetSum_coeff, split_ifs, sum_eq_zero, sum_ite_eq_of_mem
-/
theorem coeff_bernoulli (n i : Nat) :
    (bernoulli n).coeff i = if i <= n then (_root_.bernoulli (n - i) * choose n i) else 0 := by
  simp only [bernoulli, finsetSum_coeff, coeff_monomial]
  split_ifs with h
  · convert! sum_ite_eq_of_mem (range (n + 1)) (n - i) _ (by grind) using 3 <;> grind [choose_symm]
· exact Finset.sum_eq_zero by grind

/-
### examples
-/
section Examples

@[simp]
/--
theorem `bernoulli_zero` / 定理 `bernoulli_zero`

English:
theorem bernoulli_zero
  statement: bernoulli 0 = 1
  proof: by simp [bernoulli]

@[simp]

中文:
定理 bernoulli_zero
  结论: bernoulli 0 = 1
  证明: by simp [bernoulli]

@[simp]

Depends on / 依赖: bernoulli
-/
theorem bernoulli_zero : bernoulli 0 = 1 := by simp [bernoulli]

@[simp]
/--
theorem `bernoulli_one` / 定理 `bernoulli_one`

English:
theorem bernoulli_one
  statement: bernoulli 1 = X - C 2⁻¹
  proof: by
  simp [bernoulli, ← smul_X_eq_monomial, sum_range_succ, ← C_1, -map_one, neg_div, sub_eq_add_neg]

@[simp]

中文:
定理 bernoulli_one
  结论: bernoulli 1 = X - C 2⁻¹
  证明: by
  simp [bernoulli, ← smul_X_eq_monomial, sum_range_succ, ← C_1, -map_one, neg_div, sub_eq_add_neg]

@[simp]

Depends on / 依赖: bernoulli, map_one, neg_div, smul_X_eq_monomial, sub_eq_add_neg, sum_range_succ
-/
theorem bernoulli_one : bernoulli 1 = X - C 2⁻¹ := by
  simp [bernoulli, ← smul_X_eq_monomial, sum_range_succ, ← C_1, -map_one, neg_div, sub_eq_add_neg]

@[simp]
/--
theorem `bernoulli_eval_zero` / 定理 `bernoulli_eval_zero`

English:
theorem bernoulli_eval_zero
  given: (n : Nat)
  statement: (bernoulli n).eval 0 = _root_.bernoulli n
  proof: by
  rw [← coeff_zero_eq_eval_zero]; rw [coeff_bernoulli]; rw [if_pos (Nat.zero_le n)]; rw [Nat.sub_zero]; rw [Nat.choose_zero_right]; rw [Nat.cast_one]; rw [mul_one]

@[simp]

中文:
定理 bernoulli_eval_zero
  条件: (n : 自然数)
  结论: (bernoulli n).eval 0 = _root_.bernoulli n
  证明: by
  rw [← coeff_zero_eq_eval_zero]; rw [coeff_bernoulli]; rw [if_pos (Nat.zero_le n)]; rw [Nat.sub_zero]; rw [Nat.choose_zero_right]; rw [Nat.cast_one]; rw [mul_one]

@[simp]

Depends on / 依赖: Nat.cast_one, Nat.choose_zero_right, Nat.sub_zero, Nat.zero_le, cast_one, choose_zero_right, coeff_bernoulli, coeff_zero_eq_eval_zero, if_pos, mul_one, sub_zero, zero_le
-/
theorem bernoulli_eval_zero (n : Nat) : (bernoulli n).eval 0 = _root_.bernoulli n := by
  rw [← coeff_zero_eq_eval_zero]; rw [coeff_bernoulli]; rw [if_pos (Nat.zero_le n)]; rw [Nat.sub_zero]; rw [Nat.choose_zero_right]; rw [Nat.cast_one]; rw [mul_one]

@[simp]
/--
theorem `bernoulli_eval_one` / 定理 `bernoulli_eval_one`

English:
theorem bernoulli_eval_one
  given: (n : Nat)
  statement: (bernoulli n).eval 1 = bernoulli' n
  proof: by
  simp only [bernoulli, eval_finsetSum]
  simp only [← succ_eq_add_one, sum_range_succ, mul_one, cast_one, choose_self,
    (_root_.bernoulli _).mul_comm, sum_bernoulli, one_pow, mul_one, eval_monomial, one_mul]
  by_cases h : n = 1
  · norm_num [h]
  · simp [h, bernoulli_eq_bernoulli'_of_ne_one 

中文:
定理 bernoulli_eval_one
  条件: (n : 自然数)
  结论: (bernoulli n).eval 1 = bernoulli' n
  证明: by
  simp only [bernoulli, eval_finsetSum]
  simp only [← succ_eq_add_one, sum_range_succ, mul_one, cast_one, choose_self,
    (_root_.bernoulli _).mul_comm, sum_bernoulli, one_pow, mul_one, eval_monomial, one_mul]
  by_cases h : n = 1
  · norm_num [h]
  · simp [h, bernoulli_eq_bernoulli'_of_ne_one 

Depends on / 依赖: _of_ne_one, _root_, _root_.bernoulli, bernoulli, bernoulli_eq_bernoulli, cast_one, choose_self, eval_finsetSum, eval_monomial, mul_comm, mul_one, one_mul, one_pow, succ_eq_add_one, sum_bernoulli, sum_range_succ
-/
theorem bernoulli_eval_one (n : Nat) : (bernoulli n).eval 1 = bernoulli' n := by
  simp only [bernoulli, eval_finsetSum]
  simp only [← succ_eq_add_one, sum_range_succ, mul_one, cast_one, choose_self,
    (_root_.bernoulli _).mul_comm, sum_bernoulli, one_pow, mul_one, eval_monomial, one_mul]
  by_cases h : n = 1
  · norm_num [h]
  · simp [h, bernoulli_eq_bernoulli'_of_ne_one h]

/--
theorem `bernoulli_three_eval_one_quarter` / 定理 `bernoulli_three_eval_one_quarter`

English:
theorem bernoulli_three_eval_one_quarter
  proof: by
  simp_rw [Polynomial.bernoulli, Finset.sum_range_succ, Polynomial.eval_add,
    Polynomial.eval_monomial]
  rw [Finset.sum_range_zero]; rw [Polynomial.eval_zero]; rw [zero_add]; rw [_root_.bernoulli_one]
  rw [bernoulli_eq_bernoulli'_of_ne_one zero_ne_one]; rw [bernoulli'_zero]; rw [bernoulli_eq

中文:
定理 bernoulli_three_eval_one_quarter
  证明: by
  simp_rw [Polynomial.bernoulli, Finset.sum_range_succ, Polynomial.eval_add,
    Polynomial.eval_monomial]
  rw [Finset.sum_range_zero]; rw [Polynomial.eval_zero]; rw [zero_add]; rw [_root_.bernoulli_one]
  rw [bernoulli_eq_bernoulli'_of_ne_one zero_ne_one]; rw [bernoulli'_zero]; rw [bernoulli_eq

Depends on / 依赖: Finset, Finset.sum_range_succ, Finset.sum_range_zero, Polynomial, Polynomial.bernoulli, Polynomial.eval_add, Polynomial.eval_monomial, Polynomial.eval_zero, _of_ne_one, _root_, _root_.bernoulli_one, _three, _two, _zero, bernoulli, bernoulli_eq_bernoulli, bernoulli_one, eval_add, eval_monomial, eval_zero
-/
theorem bernoulli_three_eval_one_quarter :
    (Polynomial.bernoulli 3).eval (1 / 4) = 3 / 64 := by
  simp_rw [Polynomial.bernoulli, Finset.sum_range_succ, Polynomial.eval_add,
    Polynomial.eval_monomial]
  rw [Finset.sum_range_zero]; rw [Polynomial.eval_zero]; rw [zero_add]; rw [_root_.bernoulli_one]
  rw [bernoulli_eq_bernoulli'_of_ne_one zero_ne_one]; rw [bernoulli'_zero]; rw [bernoulli_eq_bernoulli'_of_ne_one (by decide : 2 != 1)]; rw [bernoulli'_two]; rw [bernoulli_eq_bernoulli'_of_ne_one (by decide : 3 != 1)]; rw [bernoulli'_three]
  norm_num

end Examples

/--
theorem `derivative_bernoulli_add_one` / 定理 `derivative_bernoulli_add_one`

English:
theorem derivative_bernoulli_add_one
  given: (k : Nat)
  proof: by
  simp_rw [bernoulli, derivative_sum, derivative_monomial, Nat.sub_sub, Nat.add_sub_add_right]
  -- LHS sum has an extra term, but the coefficient is zero:
  rw [range_add_one]; rw [sum_insert notMem_range_self]; rw [tsub_self]; rw [cast_zero]; rw [mul_zero]; rw [map_zero]; rw [zero_add]; rw [mul

中文:
定理 derivative_bernoulli_add_one
  条件: (k : 自然数)
  证明: by
  simp_rw [bernoulli, derivative_sum, derivative_monomial, Nat.sub_sub, Nat.add_sub_add_right]
  -- LHS sum has an extra term, but the coefficient is zero:
  rw [range_add_one]; rw [sum_insert notMem_range_self]; rw [tsub_self]; rw [cast_zero]; rw [mul_zero]; rw [map_zero]; rw [zero_add]; rw [mul

Depends on / 依赖: Nat.add_sub_add_right, Nat.sub_sub, add_sub_add_right, bernoulli, derivative_monomial, derivative_sum, simp_rw, sub_sub
-/
theorem derivative_bernoulli_add_one (k : Nat) :
    Polynomial.derivative (bernoulli (k + 1)) = (k + 1) * bernoulli k := by
  simp_rw [bernoulli, derivative_sum, derivative_monomial, Nat.sub_sub, Nat.add_sub_add_right]
  -- LHS sum has an extra term, but the coefficient is zero:
  rw [range_add_one]; rw [sum_insert notMem_range_self]; rw [tsub_self]; rw [cast_zero]; rw [mul_zero]; rw [map_zero]; rw [zero_add]; rw [mul_sum]
  -- the rest of the sum is termwise equal:
  refine sum_congr rfl fun m _ => ?_
  conv_rhs => rw [← Nat.cast_one, ← Nat.cast_add, ← C_eq_natCast, C_mul_monomial, mul_comm]
  rw [mul_assoc]; rw [mul_assoc]; rw [← Nat.cast_mul]; rw [← Nat.cast_mul]
  congr 3
  rw [(choose_mul_succ_eq k m).symm]

/--
theorem `derivative_bernoulli` / 定理 `derivative_bernoulli`

English:
theorem derivative_bernoulli
  given: (k : Nat)
  proof: by
  cases k with
  | zero => rw [Nat.cast_zero, zero_mul, bernoulli_zero, derivative_one]
  | succ k => exact mod_cast derivative_bernoulli_add_one k

@[simp]
nonrec theorem sum_bernoulli (n : Nat) :
    (∑ k in range (n + 1), ((n + 1).choose k : Rat) • bernoulli k) = monomial n (n + 1 : Rat) := by

中文:
定理 derivative_bernoulli
  条件: (k : 自然数)
  证明: by
  cases k with
  | zero => rw [Nat.cast_zero, zero_mul, bernoulli_zero, derivative_one]
  | succ k => exact mod_cast derivative_bernoulli_add_one k

@[simp]
nonrec theorem sum_bernoulli (n : Nat) :
    (∑ k in range (n + 1), ((n + 1).choose k : Rat) • bernoulli k) = monomial n (n + 1 : Rat) := by

Depends on / 依赖: Nat.cast_zero, bernoulli_zero, cast_zero, derivative_bernoulli_add_one, derivative_one, mod_cast, zero_mul
-/
theorem derivative_bernoulli (k : Nat) :
    Polynomial.derivative (bernoulli k) = k * bernoulli (k - 1) := by
  cases k with
  | zero => rw [Nat.cast_zero, zero_mul, bernoulli_zero, derivative_one]
  | succ k => exact mod_cast derivative_bernoulli_add_one k

@[simp]
nonrec theorem sum_bernoulli (n : Nat) :
    (∑ k in range (n + 1), ((n + 1).choose k : Rat) • bernoulli k) = monomial n (n + 1 : Rat) := by
  simp_rw [bernoulli_def, Finset.smul_sum, Finset.range_eq_Ico, ← Finset.sum_Ico_Ico_comm,
    Finset.sum_Ico_eq_sum_range]
  simp only [add_tsub_cancel_left, zero_add, map_add]
  simp_rw [smul_monomial, mul_comm (_root_.bernoulli _) _, smul_eq_mul, ← mul_assoc]
  conv_lhs =>
    apply_congr
    · skip
    · conv =>
      apply_congr
      · skip
      · rw [← Nat.cast_mul, choose_mul (le_add_right _ _), Nat.cast_mul, add_tsub_cancel_left,
          mul_assoc, mul_comm, ← smul_eq_mul, ← smul_monomial]
  simp_rw [← sum_smul, Nat.sub_zero]
  rw [sum_range_succ_comm]
  simp only [add_eq_left, mul_one, cast_one, cast_add, add_tsub_cancel_left,
    choose_succ_self_right, one_smul, _root_.bernoulli_zero, sum_singleton, zero_add,
    map_add, range_one, mul_one]
  refine sum_eq_zero ?_
  intro x hx
  have hx1 : n + 1 - x != 1 := by grind
  simp [_root_.sum_bernoulli, hx1]

/--
theorem `bernoulli_eq_sub_sum` / 定理 `bernoulli_eq_sub_sum`

English:
theorem bernoulli_eq_sub_sum
  given: (n : Nat)
  proof: by
  simp_rw [← cast_smul_eq_nsmul (R := Rat), smul_X_eq_monomial,
    Nat.cast_succ, ← sum_bernoulli n, sum_range_succ_sub_sum, choose_succ_self_right,
    Nat.cast_succ]

中文:
定理 bernoulli_eq_sub_sum
  条件: (n : 自然数)
  证明: by
  simp_rw [← cast_smul_eq_nsmul (R := Rat), smul_X_eq_monomial,
    Nat.cast_succ, ← sum_bernoulli n, sum_range_succ_sub_sum, choose_succ_self_right,
    Nat.cast_succ]

Depends on / 依赖: Nat.cast_succ, cast_smul_eq_nsmul, cast_succ, choose_succ_self_right, simp_rw, smul_X_eq_monomial, sum_bernoulli, sum_range_succ_sub_sum
-/
theorem bernoulli_eq_sub_sum (n : Nat) :
    (n + 1) • bernoulli n =
      (n + 1) • X ^ n - ∑ k in Finset.range n, ((n + 1).choose k) • bernoulli k := by
  simp_rw [← cast_smul_eq_nsmul (R := Rat), smul_X_eq_monomial,
    Nat.cast_succ, ← sum_bernoulli n, sum_range_succ_sub_sum, choose_succ_self_right,
    Nat.cast_succ]

/--
theorem `sum_range_pow_eq_bernoulli_sub` / 定理 `sum_range_pow_eq_bernoulli_sub`

English:
theorem sum_range_pow_eq_bernoulli_sub
  given: (n p : Nat)
  proof: by
  rw [sum_range_pow]; rw [bernoulli_def]; rw [eval_finsetSum]; rw [← sum_div]; rw [mul_div_cancel₀ _ _]
  · simp_rw [eval_monomial]
    symm
    rw [← sum_flip _]; rw [sum_range_succ]
    simp only [tsub_self, tsub_zero, choose_zero_right, cast_one, mul_one, _root_.pow_zero,
      add_tsub_cancel

中文:
定理 sum_range_pow_eq_bernoulli_sub
  条件: (n p : 自然数)
  证明: by
  rw [sum_range_pow]; rw [bernoulli_def]; rw [eval_finsetSum]; rw [← sum_div]; rw [mul_div_cancel₀ _ _]
  · simp_rw [eval_monomial]
    symm
    rw [← sum_flip _]; rw [sum_range_succ]
    simp only [tsub_self, tsub_zero, choose_zero_right, cast_one, mul_one, _root_.pow_zero,
      add_tsub_cancel

Depends on / 依赖: Nat.sub_sub_self, _root_, _root_.pow_zero, add_tsub_cancel_right, bernoulli_def, cast_one, choose_symm, choose_zero_right, eval_finsetSum, eval_monomial, mem_range_le, mul_one, pow_zero, simp_rw, sub_sub_self, sum_congr, sum_div, sum_flip, sum_range_pow, sum_range_succ
-/
theorem sum_range_pow_eq_bernoulli_sub (n p : Nat) :
    ((p + 1 : Rat) * ∑ k in range n, (k : Rat) ^ p) = (bernoulli p.succ).eval (n : Rat) -
    _root_.bernoulli p.succ := by
  rw [sum_range_pow]; rw [bernoulli_def]; rw [eval_finsetSum]; rw [← sum_div]; rw [mul_div_cancel₀ _ _]
  · simp_rw [eval_monomial]
    symm
    rw [← sum_flip _]; rw [sum_range_succ]
    simp only [tsub_self, tsub_zero, choose_zero_right, cast_one, mul_one, _root_.pow_zero,
      add_tsub_cancel_right]
    apply sum_congr rfl fun x hx => _
    intro x hx
    apply congr_arg₂ _ (congr_arg₂ _ _ _) rfl
    · rw [Nat.sub_sub_self (mem_range_le hx)]
    · rw [← choose_symm (mem_range_le hx)]
  · norm_cast

/--
theorem `bernoulli_succ_eval` / 定理 `bernoulli_succ_eval`

English:
theorem bernoulli_succ_eval
  given: (n p : Nat)
  statement: (bernoulli p.succ).eval (n : Rat) =
  proof: by
  apply eq_add_of_sub_eq'
  rw [sum_range_pow_eq_bernoulli_sub]

中文:
定理 bernoulli_succ_eval
  条件: (n p : 自然数)
  结论: (bernoulli p.succ).eval (n : 有理数) =
  证明: by
  apply eq_add_of_sub_eq'
  rw [sum_range_pow_eq_bernoulli_sub]

Depends on / 依赖: eq_add_of_sub_eq, sum_range_pow_eq_bernoulli_sub
-/
theorem bernoulli_succ_eval (n p : Nat) : (bernoulli p.succ).eval (n : Rat) =
    _root_.bernoulli p.succ + (p + 1 : Rat) * ∑ k in range n, (k : Rat) ^ p := by
  apply eq_add_of_sub_eq'
  rw [sum_range_pow_eq_bernoulli_sub]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `bernoulli_comp_one_add_X` / 定理 `bernoulli_comp_one_add_X`

English:
theorem bernoulli_comp_one_add_X
  given: (n : Nat)
  proof: by
  refine Nat.strong_induction_on n fun d hd => ?_
  cases d with
  | zero => simp
  | succ d =>
  rw [← smul_right_inj (show d + 2 != 0 by positivity)]; rw [← smul_comp]; rw [smul_add]
  simp only [bernoulli_eq_sub_sum, sub_comp, sum_comp, add_assoc, one_add_one_eq_two, smul_smul]
  conv_lhs =>
 

中文:
定理 bernoulli_comp_one_add_X
  条件: (n : 自然数)
  证明: by
  refine Nat.strong_induction_on n fun d hd => ?_
  cases d with
  | zero => simp
  | succ d =>
  rw [← smul_right_inj (show d + 2 != 0 by positivity)]; rw [← smul_comp]; rw [smul_add]
  simp only [bernoulli_eq_sub_sum, sub_comp, sum_comp, add_assoc, one_add_one_eq_two, smul_smul]
  conv_lhs =>
 

Depends on / 依赖: Nat.strong_induction_on, add_assoc, apply_congr, bernoulli_eq_sub_sum, conv_lhs, mem_range, one_add_one_eq_two, simp_rw, smul_add, smul_comp, smul_right_inj, smul_smul, strong_induction_on, sub_add, sub_add_eq_sub_sub_swap, sub_comp, sub_sub_eq_add_sub, sum_add_distrib, sum_comp
-/
theorem bernoulli_comp_one_add_X (n : Nat) :
    (bernoulli n).comp (1 + X) = bernoulli n + n • X ^ (n - 1) := by
  refine Nat.strong_induction_on n fun d hd => ?_
  cases d with
  | zero => simp
  | succ d =>
  rw [← smul_right_inj (show d + 2 != 0 by positivity)]; rw [← smul_comp]; rw [smul_add]
  simp only [bernoulli_eq_sub_sum, sub_comp, sum_comp, add_assoc, one_add_one_eq_two, smul_smul]
  conv_lhs =>
    congr
    · skip
    · apply_congr
      · skip
      · rw [smul_comp, hd _ (mem_range.1 (by assumption))]
  simp_rw [smul_add, sum_add_distrib, sub_add, sub_add_eq_sub_sub_swap, sub_sub_eq_add_sub]
  congr 1
  rw [show forall a b c d : Rat[X], a - b = c + d ↔ a - c = b + d by grind]
  calc ((d + 2) • X ^ (d + 1)).comp (1 + X) - (d + 2) • X ^ (d + 1)
    _ = (d + 2) • ∑ i in range (d + 1), (d + 1).choose i • X ^ i := by
      rw [smul_comp]; rw [← smul_sub]; rw [X_pow_comp]; rw [one_add_X_pow_sub_X_pow]
    _ = ∑ i in range (d + 1), ((d + 2).choose (i + 1) * (i + 1)) • X ^ i := by
      simp_rw [smul_sum, smul_smul, ← add_one_mul_choose_eq (d + 1)]
    _ = ∑ i in range (d + 1), ((d + 2).choose i * i) • X ^ (i - 1) +
          (((d + 2).choose (d + 1)) * (d + 1)) • X ^ (d + 1 - 1) := by
      rw [← sum_range_succ _ (d + 1)]; simp [sum_range_succ']
    _ = ∑ i in range (d + 1), (d + 2).choose i • i • X ^ (i - 1) +
          ((d + 2) * (d + 1)) • X ^ (d + 1 - 1) := by
      simp [choose_succ_self_right, add_assoc, mul_assoc]

/--
theorem `bernoulli_eval_one_add` / 定理 `bernoulli_eval_one_add`

English:
theorem bernoulli_eval_one_add
  given: (n : Nat) (x : Rat)
  proof: by
  have := bernoulli_comp_one_add_X n
  simpa using congr(Polynomial.eval x $this)

中文:
定理 bernoulli_eval_one_add
  条件: (n : 自然数) (x : 有理数)
  证明: by
  have := bernoulli_comp_one_add_X n
  simpa using congr(Polynomial.eval x $this)

Depends on / 依赖: Polynomial, Polynomial.eval, bernoulli_comp_one_add_X
-/
theorem bernoulli_eval_one_add (n : Nat) (x : Rat) :
    (bernoulli n).eval (1 + x) = (bernoulli n).eval x + n * x ^ (n - 1) := by
  have := bernoulli_comp_one_add_X n
  simpa using congr(Polynomial.eval x $this)

set_option backward.isDefEq.respectTransparency false in
/--
theorem `bernoulli_comp_neg_X` / 定理 `bernoulli_comp_neg_X`

English:
theorem bernoulli_comp_neg_X
  given: (n : Nat)
  proof: by
  cases n with
  | zero => simp
  | succ n =>
  ext i
  rw [← neg_one_mul]; rw [← C_1]; rw [← C_neg]; rw [Polynomial.comp_C_mul_X_coeff]; rw [coeff_smul]; rw [coeff_add]; rw [coeff_smul]; rw [coeff_bernoulli]; rw [coeff_X_pow]
  split_ifs with h h'
  · subst h'
    simp
    grind
  · cases (n + 1

中文:
定理 bernoulli_comp_neg_X
  条件: (n : 自然数)
  证明: by
  cases n with
  | zero => simp
  | succ n =>
  ext i
  rw [← neg_one_mul]; rw [← C_1]; rw [← C_neg]; rw [Polynomial.comp_C_mul_X_coeff]; rw [coeff_smul]; rw [coeff_add]; rw [coeff_smul]; rw [coeff_bernoulli]; rw [coeff_X_pow]
  split_ifs with h h'
  · subst h'
    simp
    grind
  · cases (n + 1

Depends on / 依赖: C_neg, Polynomial, Polynomial.comp_C_mul_X_coeff, bernoulli_eq_zero_of_odd, coeff_X_pow, coeff_add, coeff_bernoulli, coeff_smul, comp_C_mul_X_coeff, even_or_odd, neg_one_mul, neg_one_pow_eq_ite, split_ifs
-/
theorem bernoulli_comp_neg_X (n : Nat) :
    (bernoulli n).comp (-X) = (-1) ^ n • (bernoulli n + n • X ^ (n - 1)) := by
  cases n with
  | zero => simp
  | succ n =>
  ext i
  rw [← neg_one_mul]; rw [← C_1]; rw [← C_neg]; rw [Polynomial.comp_C_mul_X_coeff]; rw [coeff_smul]; rw [coeff_add]; rw [coeff_smul]; rw [coeff_bernoulli]; rw [coeff_X_pow]
  split_ifs with h h'
  · subst h'
    simp
    grind
  · cases (n + 1 - i).even_or_odd with
    | inl h => grind [neg_one_pow_eq_ite]
    | inr h => rw [bernoulli_eq_zero_of_odd] <;> grind
  · grind
  · simp

/--
theorem `bernoulli_eval_neg` / 定理 `bernoulli_eval_neg`

English:
theorem bernoulli_eval_neg
  given: (n : Nat) (x : Rat)
  proof: by
  simpa [mul_add] using congr_arg (Polynomial.eval x) (bernoulli_comp_neg_X n)

中文:
定理 bernoulli_eval_neg
  条件: (n : 自然数) (x : 有理数)
  证明: by
  simpa [mul_add] using congr_arg (Polynomial.eval x) (bernoulli_comp_neg_X n)

Depends on / 依赖: Polynomial, Polynomial.eval, bernoulli_comp_neg_X, congr_arg, mul_add
-/
theorem bernoulli_eval_neg (n : Nat) (x : Rat) :
    (bernoulli n).eval (-x) = (-1) ^ n * ((bernoulli n).eval x + n * x ^ (n - 1)) := by
  simpa [mul_add] using congr_arg (Polynomial.eval x) (bernoulli_comp_neg_X n)

/--
theorem `bernoulli_comp_one_sub_X` / 定理 `bernoulli_comp_one_sub_X`

English:
theorem bernoulli_comp_one_sub_X
  given: (n : Nat)
  proof: by
  cases n with
  | zero => simp
  | succ n =>
    trans ((bernoulli (n + 1)).comp (1 + X)).comp (-X)
    · simp [comp_assoc, sub_eq_add_neg]
    simp [bernoulli_comp_one_add_X, bernoulli_comp_neg_X, neg_pow (X : Polynomial Rat)]
    ring

中文:
定理 bernoulli_comp_one_sub_X
  条件: (n : 自然数)
  证明: by
  cases n with
  | zero => simp
  | succ n =>
    trans ((bernoulli (n + 1)).comp (1 + X)).comp (-X)
    · simp [comp_assoc, sub_eq_add_neg]
    simp [bernoulli_comp_one_add_X, bernoulli_comp_neg_X, neg_pow (X : Polynomial Rat)]
    ring

Depends on / 依赖: Polynomial, bernoulli, bernoulli_comp_neg_X, bernoulli_comp_one_add_X, comp_assoc, neg_pow, sub_eq_add_neg
-/
theorem bernoulli_comp_one_sub_X (n : Nat) :
    (bernoulli n).comp (1 - X) = (-1) ^ n * bernoulli n := by
  cases n with
  | zero => simp
  | succ n =>
    trans ((bernoulli (n + 1)).comp (1 + X)).comp (-X)
    · simp [comp_assoc, sub_eq_add_neg]
    simp [bernoulli_comp_one_add_X, bernoulli_comp_neg_X, neg_pow (X : Polynomial Rat)]
    ring

/--
theorem `bernoulli_eval_one_sub` / 定理 `bernoulli_eval_one_sub`

English:
theorem bernoulli_eval_one_sub
  given: (n : Nat) (x : Rat)
  proof: by
  simpa using congr_arg (Polynomial.eval x) (bernoulli_comp_one_sub_X n)

中文:
定理 bernoulli_eval_one_sub
  条件: (n : 自然数) (x : 有理数)
  证明: by
  simpa using congr_arg (Polynomial.eval x) (bernoulli_comp_one_sub_X n)

Depends on / 依赖: Polynomial, Polynomial.eval, bernoulli_comp_one_sub_X, congr_arg
-/
theorem bernoulli_eval_one_sub (n : Nat) (x : Rat) :
    (bernoulli n).eval (1 - x) = (-1) ^ n * (bernoulli n).eval x := by
  simpa using congr_arg (Polynomial.eval x) (bernoulli_comp_one_sub_X n)

open PowerSeries

variable {A : Type*} [CommRing A] [Algebra Rat A]

-- TODO: define exponential generating functions, and use them here
-- This name should probably be updated afterwards
/--
theorem `bernoulli_generating_function` / 定理 `bernoulli_generating_function`

English:
theorem bernoulli_generating_function
  given: (t : A)
  proof: by
  -- check equality of power series by checking coefficients of X^n
  ext n
  -- n = 0 case solved by `simp`
  cases n with | zero => simp | succ n =>
  -- n ≥ 1, the coefficients is a sum to n+2, so use `sum_range_succ` to write as
  -- last term plus sum to n+1
  rw [coeff_succ_X_mul]; rw [coef

中文:
定理 bernoulli_generating_function
  条件: (t : A)
  证明: by
  -- check equality of power series by checking coefficients of X^n
  ext n
  -- n = 0 case solved by `simp`
  cases n with | zero => simp | succ n =>
  -- n ≥ 1, the coefficients is a sum to n+2, so use `sum_range_succ` to write as
  -- last term plus sum to n+1
  rw [coeff_succ_X_mul]; rw [coef
-/
theorem bernoulli_generating_function (t : A) :
    (mk fun n => aeval t ((1 / n ! : Rat) • bernoulli n)) * (exp A - 1) =
      PowerSeries.X * rescale t (exp A) := by
  -- check equality of power series by checking coefficients of X^n
  ext n
  -- n = 0 case solved by `simp`
  cases n with | zero => simp | succ n =>
  -- n ≥ 1, the coefficients is a sum to n+2, so use `sum_range_succ` to write as
  -- last term plus sum to n+1
  rw [coeff_succ_X_mul]; rw [coeff_rescale]; rw [coeff_exp]; rw [PowerSeries.coeff_mul]; rw [Nat.sum_antidiagonal_eq_sum_range_succ_mk]; rw [sum_range_succ]
  -- last term is zero so kill with `add_zero`
  simp only [map_sub, tsub_self, constantCoeff_one, constantCoeff_exp,
    coeff_zero_eq_constantCoeff, mul_zero, sub_self, add_zero]
  -- Let's multiply both sides by (n+1)! (OK because it's a unit)
  have hnp1 : IsUnit ((n + 1)! : Rat) := IsUnit.mk0 _ (mod_cast factorial_ne_zero (n + 1))
  rw [← (hnp1.map (algebraMap Rat A)).mul_right_inj]
  -- do trivial rearrangements to make RHS (n+1)*t^n
  rw [mul_left_comm]; rw [← map_mul]
  change _ = t ^ n * algebraMap Rat A (((n + 1) * n ! : Nat) * (1 / n !))
  rw [cast_mul]; rw [mul_assoc]; rw [mul_one_div_cancel (show (n ! : Rat) != 0 from cast_ne_zero.2 (factorial_ne_zero n))]; rw [mul_one]; rw [mul_comm (t ^ n)]; rw [← aeval_monomial]; rw [cast_add]; rw [cast_one]
  -- But this is the RHS of `Polynomial.sum_bernoulli`
  rw [← sum_bernoulli]; rw [Finset.mul_sum]; rw [map_sum]
  -- and now we have to prove a sum is a sum, but all the terms are equal.
  apply Finset.sum_congr rfl
  -- The rest is just trivialities, hampered by the fact that we're coercing
  -- factorials and binomial coefficients between ℕ and ℚ and A.
  intro i hi
  -- deal with coefficients of e^X-1
  simp only [Nat.cast_choose Rat (mem_range_le hi), coeff_mk, if_neg (mem_range_sub_ne_zero hi),
    PowerSeries.coeff_one, coeff_exp, sub_zero, Algebra.smul_def,
    mul_right_comm _ ((aeval t) _), ← mul_assoc, ← map_mul, ← Polynomial.C_eq_algebraMap,
    Polynomial.aeval_mul, Polynomial.aeval_C]
  -- finally cancel the Bernoulli polynomial and the algebra_map
  field_simp

end Polynomial
