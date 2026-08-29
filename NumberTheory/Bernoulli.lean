/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Kevin Buzzard, Seewoo Lee
-/
module

public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.GCDMonoid.FinsetLemmas
public import Mathlib.Algebra.Field.GeomSum
public import Mathlib.Data.Nat.Choose.Bounds
public import Mathlib.RingTheory.PowerSeries.Exp
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.RingTheory.ZMod.UnitsCyclic
public import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.Tactic.NormNum.GCD

/-!
# Bernoulli numbers

The Bernoulli numbers are a sequence of rational numbers that frequently show up in
number theory.

## Mathematical overview

The Bernoulli numbers $(B_0, B_1, B_2, \ldots)=(1, -1/2, 1/6, 0, -1/30, \ldots)$ are
a sequence of rational numbers. They show up in the formula for the sums of $k$th
powers. They are related to the Taylor series expansions of $x/\tan(x)$ and
of $\coth(x)$, and also show up in the values that the Riemann Zeta function
takes both at both negative and positive integers (and hence in the
theory of modular forms). For example, if $1 \leq n$ then

$$\zeta(2n)=\sum_{t\geq1}t^{-2n}=(-1)^{n+1}\frac{(2\pi)^{2n}B_{2n}}{2(2n)!}.$$

This result is formalised in Lean: `riemannZeta_two_mul_nat`.

The Bernoulli numbers can be formally defined using the power series

$$\sum B_n\frac{t^n}{n!}=\frac{t}{1-e^{-t}}$$

although that happens to not be the definition in mathlib (this is an *implementation
detail* and need not concern the mathematician).

Note that $B_1=-1/2$, meaning that we are using the $B_n^-$ of
[from Wikipedia](https://en.wikipedia.org/wiki/Bernoulli_number).

## Implementation detail

The Bernoulli numbers are defined using well-founded induction, by the formula
$$B_n=1-\sum_{k\lt n}\frac{\binom{n}{k}}{n-k+1}B_k.$$
This formula is true for all $n$ and in particular $B_0=1$. Note that this is the definition
for positive Bernoulli numbers, which we call `bernoulli'`. The negative Bernoulli numbers are
then defined as `bernoulli := (-1)^n * bernoulli'`.

The proof of von Staudt-Clausen's theorem follows Rado's JLMS 1934 paper
"A New Proof of a Theorem of v. Staudt".

## Main theorems

* `sum_bernoulli : ∑ k ∈ range n, (n.choose k : ℚ) * bernoulli k =
  if n = 1 then 1 else 0`
* `Bernoulli.vonStaudt_clausen : bernoulli (2 * k) + ∑ p ∈ range (2 * k + 2)
  with p.Prime ∧ (p - 1) ∣ 2 * k, (1 : ℚ) / p ∈ Set.range Int.cast`

## References

* https://en.wikipedia.org/wiki/Bernoulli_number
* [R. Rado, *A New Proof of a Theorem of v. Staudt*][Rado1934]
-/


@[expose] public section


open Nat Finset Finset.Nat PowerSeries

variable (A : Type*) [CommRing A] [Algebra Rat A]

/-! ### Definitions -/


/--
Definition of `bernoulli'` / `bernoulli'` 的定义

English:
definition bernoulli'
  signature: (n : Nat)
  body: 1 - ∑ k : Fin n, n.choose k / (n - k + 1) * bernoulli' k

中文:
定义 bernoulli'
  签名: (n : 自然数)
  定义体: 1 - ∑ k : Fin n, n.choose k / (n - k + 1) * bernoulli' k

Depends on / 依赖: bernoulli, n.choose
-/
def bernoulli' (n : Nat) : Rat :=
  1 - ∑ k : Fin n, n.choose k / (n - k + 1) * bernoulli' k

/--
theorem `bernoulli'_def'` / 定理 `bernoulli'_def'`

English:
theorem bernoulli'_def'
  given: (n : Nat)
  proof: by
  rw [bernoulli']

中文:
定理 bernoulli'_def'
  条件: (n : 自然数)
  证明: by
  rw [bernoulli']
-/
theorem bernoulli'_def' (n : Nat) :
    bernoulli' n = 1 - ∑ k : Fin n, n.choose k / (n - k + 1) * bernoulli' k := by
  rw [bernoulli']

/--
theorem `bernoulli'_def` / 定理 `bernoulli'_def`

English:
theorem bernoulli'_def
  given: (n : Nat)
  proof: by
  rw [bernoulli'_def']; rw [← Fin.sum_univ_eq_sum_range]

中文:
定理 bernoulli'_def
  条件: (n : 自然数)
  证明: by
  rw [bernoulli'_def']; rw [← Fin.sum_univ_eq_sum_range]
-/
theorem bernoulli'_def (n : Nat) :
    bernoulli' n = 1 - ∑ k in range n, n.choose k / (n - k + 1) * bernoulli' k := by
  rw [bernoulli'_def']; rw [← Fin.sum_univ_eq_sum_range]

/--
theorem `bernoulli'_spec` / 定理 `bernoulli'_spec`

English:
theorem bernoulli'_spec
  given: (n : Nat)
  proof: by
  rw [sum_range_succ_comm]; rw [bernoulli'_def n]; rw [tsub_self]; rw [choose_zero_right]; rw [sub_self]; rw [zero_add]; rw [div_one]; rw [cast_one]; rw [one_mul]; rw [sub_add]; rw [← sum_sub_distrib]; rw [← sub_eq_zero]; rw [sub_sub_cancel_left]; rw [neg_eq_zero]
  exact Finset.sum_eq_zero (fun 

中文:
定理 bernoulli'_spec
  条件: (n : 自然数)
  证明: by
  rw [sum_range_succ_comm]; rw [bernoulli'_def n]; rw [tsub_self]; rw [choose_zero_right]; rw [sub_self]; rw [zero_add]; rw [div_one]; rw [cast_one]; rw [one_mul]; rw [sub_add]; rw [← sum_sub_distrib]; rw [← sub_eq_zero]; rw [sub_sub_cancel_left]; rw [neg_eq_zero]
  exact Finset.sum_eq_zero (fun 
-/
theorem bernoulli'_spec (n : Nat) :
    (∑ k in range n.succ, (n.choose (n - k) : Rat) / (n - k + 1) * bernoulli' k) = 1 := by
  rw [sum_range_succ_comm]; rw [bernoulli'_def n]; rw [tsub_self]; rw [choose_zero_right]; rw [sub_self]; rw [zero_add]; rw [div_one]; rw [cast_one]; rw [one_mul]; rw [sub_add]; rw [← sum_sub_distrib]; rw [← sub_eq_zero]; rw [sub_sub_cancel_left]; rw [neg_eq_zero]
  exact Finset.sum_eq_zero (fun x hx => by rw [choose_symm (le_of_lt (mem_range.1 hx)), sub_self])

/--
theorem `bernoulli'_spec'` / 定理 `bernoulli'_spec'`

English:
theorem bernoulli'_spec'
  given: (n : Nat)
  proof: by
  refine ((sum_antidiagonal_eq_sum_range_succ_mk _ n).trans ?_).trans (bernoulli'_spec n)
  refine sum_congr rfl fun x hx => ?_
  simp only [add_tsub_cancel_of_le, mem_range_succ_iff.mp hx, cast_sub]

中文:
定理 bernoulli'_spec'
  条件: (n : 自然数)
  证明: by
  refine ((sum_antidiagonal_eq_sum_range_succ_mk _ n).trans ?_).trans (bernoulli'_spec n)
  refine sum_congr rfl fun x hx => ?_
  simp only [add_tsub_cancel_of_le, mem_range_succ_iff.mp hx, cast_sub]
-/
theorem bernoulli'_spec' (n : Nat) :
    (∑ k in antidiagonal n, ((k.1 + k.2).choose k.2 : Rat) / (k.2 + 1) * bernoulli' k.1) = 1 := by
  refine ((sum_antidiagonal_eq_sum_range_succ_mk _ n).trans ?_).trans (bernoulli'_spec n)
  refine sum_congr rfl fun x hx => ?_
  simp only [add_tsub_cancel_of_le, mem_range_succ_iff.mp hx, cast_sub]

/-! ### Examples -/


section Examples

@[simp]
/--
theorem `bernoulli'_zero` / 定理 `bernoulli'_zero`

English:
theorem bernoulli'_zero
  statement: bernoulli' 0 = 1
  proof: by
  rw [bernoulli'_def]
  simp

@[simp]

中文:
定理 bernoulli'_zero
  结论: bernoulli' 0 = 1
  证明: by
  rw [bernoulli'_def]
  simp

@[simp]
-/
theorem bernoulli'_zero : bernoulli' 0 = 1 := by
  rw [bernoulli'_def]
  simp

@[simp]
/--
theorem `bernoulli'_one` / 定理 `bernoulli'_one`

English:
theorem bernoulli'_one
  statement: bernoulli' 1 = 1 / 2
  proof: by
  rw [bernoulli'_def]
  norm_num

@[simp]

中文:
定理 bernoulli'_one
  结论: bernoulli' 1 = 1 / 2
  证明: by
  rw [bernoulli'_def]
  norm_num

@[simp]
-/
theorem bernoulli'_one : bernoulli' 1 = 1 / 2 := by
  rw [bernoulli'_def]
  norm_num

@[simp]
/--
theorem `bernoulli'_two` / 定理 `bernoulli'_two`

English:
theorem bernoulli'_two
  statement: bernoulli' 2 = 1 / 6
  proof: by
  rw [bernoulli'_def]
  norm_num [sum_range_succ, sum_range_succ, sum_range_zero]

@[simp]

中文:
定理 bernoulli'_two
  结论: bernoulli' 2 = 1 / 6
  证明: by
  rw [bernoulli'_def]
  norm_num [sum_range_succ, sum_range_succ, sum_range_zero]

@[simp]
-/
theorem bernoulli'_two : bernoulli' 2 = 1 / 6 := by
  rw [bernoulli'_def]
  norm_num [sum_range_succ, sum_range_succ, sum_range_zero]

@[simp]
/--
theorem `bernoulli'_three` / 定理 `bernoulli'_three`

English:
theorem bernoulli'_three
  statement: bernoulli' 3 = 0
  proof: by
  rw [bernoulli'_def]
  norm_num [sum_range_succ, sum_range_succ, sum_range_zero]

@[simp]

中文:
定理 bernoulli'_three
  结论: bernoulli' 3 = 0
  证明: by
  rw [bernoulli'_def]
  norm_num [sum_range_succ, sum_range_succ, sum_range_zero]

@[simp]
-/
theorem bernoulli'_three : bernoulli' 3 = 0 := by
  rw [bernoulli'_def]
  norm_num [sum_range_succ, sum_range_succ, sum_range_zero]

@[simp]
/--
theorem `bernoulli'_four` / 定理 `bernoulli'_four`

English:
theorem bernoulli'_four
  statement: bernoulli' 4 = -1 / 30
  proof: by
  have : Nat.choose 4 2 = 6 := by decide -- shrug
  rw [bernoulli'_def]
  norm_num [sum_range_succ, sum_range_succ, sum_range_zero, this]

中文:
定理 bernoulli'_four
  结论: bernoulli' 4 = -1 / 30
  证明: by
  have : Nat.choose 4 2 = 6 := by decide -- shrug
  rw [bernoulli'_def]
  norm_num [sum_range_succ, sum_range_succ, sum_range_zero, this]
-/
theorem bernoulli'_four : bernoulli' 4 = -1 / 30 := by
  have : Nat.choose 4 2 = 6 := by decide -- shrug
  rw [bernoulli'_def]
  norm_num [sum_range_succ, sum_range_succ, sum_range_zero, this]

end Examples

@[simp]
/--
theorem `sum_bernoulli'` / 定理 `sum_bernoulli'`

English:
theorem sum_bernoulli'
  given: (n : Nat)
  statement: (∑ k in range n, (n.choose k : Rat) * bernoulli' k) = n
  proof: by
  cases n with | zero => simp | succ n =>
  suffices
    ((n + 1 : Rat) * ∑ k in range n, ↑(n.choose k) / (n - k + 1) * bernoulli' k) =
      ∑ x in range n, ↑(n.succ.choose x) * bernoulli' x by
    rw_mod_cast [sum_range_succ, bernoulli'_def, ← this, choose_succ_self_right]
    ring
  simp_rw [m

中文:
定理 sum_bernoulli'
  条件: (n : 自然数)
  结论: (∑ k in range n, (n.choose k : 有理数) * bernoulli' k) = n
  证明: by
  cases n with | zero => simp | succ n =>
  suffices
    ((n + 1 : Rat) * ∑ k in range n, ↑(n.choose k) / (n - k + 1) * bernoulli' k) =
      ∑ x in range n, ↑(n.succ.choose x) * bernoulli' x by
    rw_mod_cast [sum_range_succ, bernoulli'_def, ← this, choose_succ_self_right]
    ring
  simp_rw [m

Depends on / 依赖: _def, bernoulli, cast_sub, choose_succ_self_right, mem_range, mul_assoc, mul_comm, mul_sum, n.choose, n.succ.choose, rw_mod_cast, simp_rw, succ_eq_add_one, sum_congr, sum_range_succ, tsub_add_eq_add_t
-/
theorem sum_bernoulli' (n : Nat) : (∑ k in range n, (n.choose k : Rat) * bernoulli' k) = n := by
  cases n with | zero => simp | succ n =>
  suffices
    ((n + 1 : Rat) * ∑ k in range n, ↑(n.choose k) / (n - k + 1) * bernoulli' k) =
      ∑ x in range n, ↑(n.succ.choose x) * bernoulli' x by
    rw_mod_cast [sum_range_succ, bernoulli'_def, ← this, choose_succ_self_right]
    ring
  simp_rw [mul_sum, ← mul_assoc]
  refine sum_congr rfl fun k hk => ?_
  congr
  have : ((n - k : Nat) : Rat) + 1 != 0 := by norm_cast
  simp only [← cast_sub (mem_range.1 hk).le, succ_eq_add_one, field, mul_comm]
  rw_mod_cast [tsub_add_eq_add_tsub (mem_range.1 hk).le, choose_mul_succ_eq]

/--
Definition of `bernoulli'PowerSeries` / `bernoulli'PowerSeries` 的定义

English:
definition bernoulli'PowerSeries
  body: mk fun n => algebraMap Rat A (bernoulli' n / n !)

中文:
定义 bernoulli'幂级数
  定义体: mk fun n => algebraMap Rat A (bernoulli' n / n !)
-/
def bernoulli'PowerSeries :=
  mk fun n => algebraMap Rat A (bernoulli' n / n !)

/--
theorem `bernoulli'PowerSeries_mul_exp_sub_one` / 定理 `bernoulli'PowerSeries_mul_exp_sub_one`

English:
theorem bernoulli'PowerSeries_mul_exp_sub_one
  proof: by
  ext n
  -- constant coefficient is a special case
  cases n with | zero => simp | succ n =>
  rw [bernoulli'PowerSeries]; rw [coeff_mul]; rw [mul_comm X]; rw [sum_antidiagonal_succ']
  suffices (∑ p in antidiagonal n,
      bernoulli' p.1 / p.1! * ((p.2 + 1) * p.2! : Rat)⁻¹) = (n ! : Rat)⁻¹ by


中文:
定理 bernoulli'PowerSeries_mul_exp_sub_one
  证明: by
  ext n
  -- constant coefficient is a special case
  cases n with | zero => simp | succ n =>
  rw [bernoulli'PowerSeries]; rw [coeff_mul]; rw [mul_comm X]; rw [sum_antidiagonal_succ']
  suffices (∑ p in antidiagonal n,
      bernoulli' p.1 / p.1! * ((p.2 + 1) * p.2! : Rat)⁻¹) = (n ! : Rat)⁻¹ by

-/
theorem bernoulli'PowerSeries_mul_exp_sub_one :
    bernoulli'PowerSeries A * (exp A - 1) = X * exp A := by
  ext n
  -- constant coefficient is a special case
  cases n with | zero => simp | succ n =>
  rw [bernoulli'PowerSeries]; rw [coeff_mul]; rw [mul_comm X]; rw [sum_antidiagonal_succ']
  suffices (∑ p in antidiagonal n,
      bernoulli' p.1 / p.1! * ((p.2 + 1) * p.2! : Rat)⁻¹) = (n ! : Rat)⁻¹ by
    simpa [map_sum, Nat.factorial] using congr_arg (algebraMap Rat A) this
  apply eq_inv_of_mul_eq_one_left
  rw [sum_mul]
  convert! bernoulli'_spec' n using 1
  apply sum_congr rfl
  simp_rw [mem_antidiagonal]
  rintro ⟨i, j⟩ rfl
  have := factorial_mul_factorial_dvd_factorial_add i j
  simp [field, add_choose, *]

/--
theorem `bernoulli'_eq_zero_of_odd` / 定理 `bernoulli'_eq_zero_of_odd`

English:
theorem bernoulli'_eq_zero_of_odd
  given: {n : Nat} (h_odd : Odd n) (hlt : 1 < n)
  statement: bernoulli' n = 0
  proof: by
  let B := mk fun n => bernoulli' n / (n ! : Rat)
  suffices (B - evalNegHom B) * (exp Rat - 1) = X * (exp Rat - 1) by
    rcases mul_eq_mul_right_iff.mp this with h | h <;>
      simp only [PowerSeries.ext_iff, evalNegHom, coeff_X] at h
    · apply eq_zero_of_neg_eq
      specialize h n
      sp

中文:
定理 bernoulli'_eq_zero_of_odd
  条件: {n : 自然数} (h_odd : Odd n) (hlt : 1 < n)
  结论: bernoulli' n = 0
  证明: by
  let B := mk fun n => bernoulli' n / (n ! : Rat)
  suffices (B - evalNegHom B) * (exp Rat - 1) = X * (exp Rat - 1) by
    rcases mul_eq_mul_right_iff.mp this with h | h <;>
      simp only [PowerSeries.ext_iff, evalNegHom, coeff_X] at h
    · apply eq_zero_of_neg_eq
      specialize h n
      sp
-/
theorem bernoulli'_eq_zero_of_odd {n : Nat} (h_odd : Odd n) (hlt : 1 < n) : bernoulli' n = 0 := by
  let B := mk fun n => bernoulli' n / (n ! : Rat)
  suffices (B - evalNegHom B) * (exp Rat - 1) = X * (exp Rat - 1) by
    rcases mul_eq_mul_right_iff.mp this with h | h <;>
      simp only [PowerSeries.ext_iff, evalNegHom, coeff_X] at h
    · apply eq_zero_of_neg_eq
      specialize h n
      split_ifs at h <;> simp_all [B, h_odd.neg_one_pow, factorial_ne_zero]
    · simpa +decide [Nat.factorial] using h 1
  have h : B * (exp Rat - 1) = X * exp Rat := by
    simpa [bernoulli'PowerSeries] using bernoulli'PowerSeries_mul_exp_sub_one Rat
  rw [sub_mul]; rw [h]; rw [mul_sub X]; rw [sub_right_inj]; rw [← neg_sub]; rw [mul_neg]; rw [neg_eq_iff_eq_neg]
  suffices evalNegHom (B * (exp Rat - 1)) * exp Rat = evalNegHom (X * exp Rat) * exp Rat by
    simpa [mul_assoc, sub_mul, mul_comm (evalNegHom (exp Rat)), exp_mul_exp_neg_eq_one]
  congr

/--
Definition of `bernoulli` / `bernoulli` 的定义

English:
definition bernoulli
  signature: (n : Nat)
  body: (-1) ^ n * bernoulli' n

中文:
定义 bernoulli
  签名: (n : 自然数)
  定义体: (-1) ^ n * bernoulli' n

Depends on / 依赖: bernoulli
-/
def bernoulli (n : Nat) : Rat :=
  (-1) ^ n * bernoulli' n

/--
theorem `bernoulli'_eq_bernoulli` / 定理 `bernoulli'_eq_bernoulli`

English:
theorem bernoulli'_eq_bernoulli
  given: (n : Nat)
  statement: bernoulli' n = (-1) ^ n * bernoulli n
  proof: by
  simp [bernoulli, ← mul_assoc, ← sq, ← pow_mul, mul_comm n 2]

@[simp]

中文:
定理 bernoulli'_eq_bernoulli
  条件: (n : 自然数)
  结论: bernoulli' n = (-1) ^ n * bernoulli n
  证明: by
  simp [bernoulli, ← mul_assoc, ← sq, ← pow_mul, mul_comm n 2]

@[simp]
-/
theorem bernoulli'_eq_bernoulli (n : Nat) : bernoulli' n = (-1) ^ n * bernoulli n := by
  simp [bernoulli, ← mul_assoc, ← sq, ← pow_mul, mul_comm n 2]

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
  statement: bernoulli 1 = -1 / 2
  proof: by norm_num [bernoulli]

@[simp]

中文:
定理 bernoulli_one
  结论: bernoulli 1 = -1 / 2
  证明: by norm_num [bernoulli]

@[simp]

Depends on / 依赖: bernoulli
-/
theorem bernoulli_one : bernoulli 1 = -1 / 2 := by norm_num [bernoulli]

@[simp]
/--
theorem `bernoulli_two` / 定理 `bernoulli_two`

English:
theorem bernoulli_two
  statement: bernoulli 2 = 6⁻¹
  proof: by
  simp [bernoulli]

@[simp]

中文:
定理 bernoulli_two
  结论: bernoulli 2 = 6⁻¹
  证明: by
  simp [bernoulli]

@[simp]

Depends on / 依赖: bernoulli
-/
theorem bernoulli_two : bernoulli 2 = 6⁻¹ := by
  simp [bernoulli]

@[simp]
/--
theorem `bernoulli_eq_zero_of_odd` / 定理 `bernoulli_eq_zero_of_odd`

English:
theorem bernoulli_eq_zero_of_odd
  given: {n : Nat} (h_odd : Odd n) (hlt : 1 < n)
  statement: bernoulli n = 0
  proof: by
  rw [bernoulli]; rw [bernoulli'_eq_zero_of_odd h_odd hlt]; rw [mul_zero]

中文:
定理 bernoulli_eq_zero_of_odd
  条件: {n : 自然数} (h_odd : Odd n) (hlt : 1 < n)
  结论: bernoulli n = 0
  证明: by
  rw [bernoulli]; rw [bernoulli'_eq_zero_of_odd h_odd hlt]; rw [mul_zero]

Depends on / 依赖: _eq_zero_of_odd, bernoulli, h_odd, mul_zero
-/
theorem bernoulli_eq_zero_of_odd {n : Nat} (h_odd : Odd n) (hlt : 1 < n) : bernoulli n = 0 := by
  rw [bernoulli]; rw [bernoulli'_eq_zero_of_odd h_odd hlt]; rw [mul_zero]

/--
theorem `bernoulli_eq_bernoulli'_of_ne_one` / 定理 `bernoulli_eq_bernoulli'_of_ne_one`

English:
theorem bernoulli_eq_bernoulli'_of_ne_one
  given: {n : Nat} (hn : n != 1)
  statement: bernoulli n = bernoulli' n
  proof: by
  cases hn.lt_or_gt with
  | inl hlt => simp [lt_one_iff.mp hlt]
  | inr hgt =>
    cases n.even_or_odd with
    | inl heven => rw [bernoulli, heven.neg_one_pow, one_mul]
    | inr hodd => rw [bernoulli'_eq_zero_of_odd hodd hgt, bernoulli_eq_zero_of_odd hodd hgt]

@[simp]

中文:
定理 bernoulli_eq_bernoulli'_of_ne_one
  条件: {n : 自然数} (hn : n != 1)
  结论: bernoulli n = bernoulli' n
  证明: by
  cases hn.lt_or_gt with
  | inl hlt => simp [lt_one_iff.mp hlt]
  | inr hgt =>
    cases n.even_or_odd with
    | inl heven => rw [bernoulli, heven.neg_one_pow, one_mul]
    | inr hodd => rw [bernoulli'_eq_zero_of_odd hodd hgt, bernoulli_eq_zero_of_odd hodd hgt]

@[simp]

Depends on / 依赖: _eq_zero_of_odd, bernoulli, bernoulli_eq_zero_of_odd, even_or_odd, heven.neg_one_pow, hn.lt_or_gt, lt_one_iff, lt_one_iff.mp, lt_or_gt, n.even_or_odd, neg_one_pow, one_mul
-/
theorem bernoulli_eq_bernoulli'_of_ne_one {n : Nat} (hn : n != 1) : bernoulli n = bernoulli' n := by
  cases hn.lt_or_gt with
  | inl hlt => simp [lt_one_iff.mp hlt]
  | inr hgt =>
    cases n.even_or_odd with
    | inl heven => rw [bernoulli, heven.neg_one_pow, one_mul]
    | inr hodd => rw [bernoulli'_eq_zero_of_odd hodd hgt, bernoulli_eq_zero_of_odd hodd hgt]

@[simp]
/--
theorem `sum_bernoulli` / 定理 `sum_bernoulli`

English:
theorem sum_bernoulli
  given: (n : Nat)
  proof: by
  cases n with | zero => simp | succ n =>
  cases n with
  | zero => simp
  | succ n =>
  suffices (∑ i in range n, ↑((n + 2).choose (i + 2)) * bernoulli (i + 2)) = n / 2 by
    simp only [this, sum_range_succ', cast_succ, bernoulli_one, bernoulli_zero, choose_one_right,
      mul_one, choose_zer

中文:
定理 sum_bernoulli
  条件: (n : 自然数)
  证明: by
  cases n with | zero => simp | succ n =>
  cases n with
  | zero => simp
  | succ n =>
  suffices (∑ i in range n, ↑((n + 2).choose (i + 2)) * bernoulli (i + 2)) = n / 2 by
    simp only [this, sum_range_succ', cast_succ, bernoulli_one, bernoulli_zero, choose_one_right,
      mul_one, choose_zer

Depends on / 依赖: Eq.trans, bernoulli, bernoulli_one, bernoulli_zero, cast_succ, cast_zero, choose_one_right, choose_zero_right, eq_sub_iff_add_eq, if_false, mul_one, n.succ.succ, simp_rw, succ_succ_ne_one, sum_bernoulli, sum_range_succ, zero_add
-/
theorem sum_bernoulli (n : Nat) :
    (∑ k in range n, (n.choose k : Rat) * bernoulli k) = if n = 1 then 1 else 0 := by
  cases n with | zero => simp | succ n =>
  cases n with
  | zero => simp
  | succ n =>
  suffices (∑ i in range n, ↑((n + 2).choose (i + 2)) * bernoulli (i + 2)) = n / 2 by
    simp only [this, sum_range_succ', cast_succ, bernoulli_one, bernoulli_zero, choose_one_right,
      mul_one, choose_zero_right, cast_zero, if_false, zero_add, succ_succ_ne_one]
    ring
  have f := sum_bernoulli' n.succ.succ
  simp_rw [sum_range_succ', cast_succ, ← eq_sub_iff_add_eq] at f
  refine Eq.trans ?_ (Eq.trans f ?_)
  · congr
    funext x
    rw [bernoulli_eq_bernoulli'_of_ne_one (succ_ne_zero x ∘ succ.inj)]
  · simp only [mul_one, bernoulli'_zero, choose_zero_right,
      zero_add, choose_one_right, cast_succ, bernoulli'_one]
    ring

/--
theorem `bernoulli_spec'` / 定理 `bernoulli_spec'`

English:
theorem bernoulli_spec'
  given: (n : Nat)
  proof: by
  cases n with | zero => simp | succ n =>
  rw [if_neg (succ_ne_zero _)]
  -- algebra facts
  have h₁ : (1, n) in antidiagonal n.succ := by simp [mem_antidiagonal, add_comm]
  have h₃ : (1 + n).choose n = n + 1 := by simp [add_comm]
  -- key equation: the corresponding fact for `bernoulli'`
  hav

中文:
定理 bernoulli_spec'
  条件: (n : 自然数)
  证明: by
  cases n with | zero => simp | succ n =>
  rw [if_neg (succ_ne_zero _)]
  -- algebra facts
  have h₁ : (1, n) in antidiagonal n.succ := by simp [mem_antidiagonal, add_comm]
  have h₃ : (1 + n).choose n = n + 1 := by simp [add_comm]
  -- key equation: the corresponding fact for `bernoulli'`
  hav

Depends on / 依赖: if_neg, succ_ne_zero
-/
theorem bernoulli_spec' (n : Nat) :
    (∑ k in antidiagonal n, ((k.1 + k.2).choose k.2 : Rat) / (k.2 + 1) * bernoulli k.1) =
      if n = 0 then 1 else 0 := by
  cases n with | zero => simp | succ n =>
  rw [if_neg (succ_ne_zero _)]
  -- algebra facts
  have h₁ : (1, n) in antidiagonal n.succ := by simp [mem_antidiagonal, add_comm]
  have h₃ : (1 + n).choose n = n + 1 := by simp [add_comm]
  -- key equation: the corresponding fact for `bernoulli'`
  have H := bernoulli'_spec' n.succ
  -- massage it to match the structure of the goal, then convert piece by piece
  rw [sum_eq_add_sum_sdiff_singleton_of_mem h₁] at H ⊢
  apply add_eq_of_eq_sub'
  convert! eq_sub_of_add_eq' H using 1
  · refine sum_congr rfl fun p h => ?_
    obtain ⟨h', h''⟩ : p in _ ∧ p != _ := by rwa [mem_sdiff, mem_singleton] at h
    simp [bernoulli_eq_bernoulli'_of_ne_one
      ((not_congr (HasAntidiagonal.antidiagonal_congr h' h₁)).mp h'')]
  · simp [field, h₃]
    norm_num

/--
Definition of `bernoulliPowerSeries` / `bernoulliPowerSeries` 的定义

English:
definition bernoulliPowerSeries
  body: mk fun n => algebraMap Rat A (bernoulli n / n !)

中文:
定义 bernoulliPowerSeries
  定义体: mk fun n => algebraMap Rat A (bernoulli n / n !)

Depends on / 依赖: algebraMap, bernoulli
-/
def bernoulliPowerSeries :=
  mk fun n => algebraMap Rat A (bernoulli n / n !)

/--
theorem `bernoulliPowerSeries_mul_exp_sub_one` / 定理 `bernoulliPowerSeries_mul_exp_sub_one`

English:
theorem bernoulliPowerSeries_mul_exp_sub_one
  statement: bernoulliPowerSeries A * (exp A - 1) = X
  proof: by
  ext n
  -- constant coefficient is a special case
  cases n with | zero => simp | succ n =>
  simp only [bernoulliPowerSeries, coeff_mul, coeff_X, sum_antidiagonal_succ', one_div, coeff_mk,
    coeff_one, coeff_exp, map_sub, factorial, if_pos, cast_succ, cast_mul,
    sub_zero, add_eq_zero, if_

中文:
定理 bernoulliPowerSeries_mul_exp_sub_one
  结论: bernoulliPowerSeries A * (exp A - 1) = X
  证明: by
  ext n
  -- constant coefficient is a special case
  cases n with | zero => simp | succ n =>
  simp only [bernoulliPowerSeries, coeff_mul, coeff_X, sum_antidiagonal_succ', one_div, coeff_mk,
    coeff_one, coeff_exp, map_sub, factorial, if_pos, cast_succ, cast_mul,
    sub_zero, add_eq_zero, if_
-/
theorem bernoulliPowerSeries_mul_exp_sub_one : bernoulliPowerSeries A * (exp A - 1) = X := by
  ext n
  -- constant coefficient is a special case
  cases n with | zero => simp | succ n =>
  simp only [bernoulliPowerSeries, coeff_mul, coeff_X, sum_antidiagonal_succ', one_div, coeff_mk,
    coeff_one, coeff_exp, map_sub, factorial, if_pos, cast_succ, cast_mul,
    sub_zero, add_eq_zero, if_false, one_ne_zero, and_false, ← map_mul, ← map_sum]
  cases n with | zero => simp | succ n =>
  rw [if_neg n.succ_succ_ne_one]
  have hfact : forall m, (m ! : Rat) != 0 := fun m => mod_cast factorial_ne_zero m
  have hite2 : ite (n.succ = 0) 1 0 = (0 : Rat) := if_neg n.succ_ne_zero
  simp only [CharP.cast_eq_zero, zero_add, inv_one, map_one, sub_self, mul_zero]
  rw [← map_zero (algebraMap Rat A)]; rw [← zero_div (n.succ ! : Rat)]; rw [← hite2]; rw [← bernoulli_spec']; rw [sum_div]
  refine congr_arg (algebraMap Rat A) (sum_congr rfl fun x h => eq_div_of_mul_eq (hfact n.succ) ?_)
  rw [mem_antidiagonal] at h
  rw [← h]; rw [add_choose]; rw [cast_div_charZero (factorial_mul_factorial_dvd_factorial_add _ _)]
  simp [field, mul_comm _ (bernoulli x.1), mul_assoc]

section Faulhaber

/--
theorem `sum_range_pow` / 定理 `sum_range_pow`

English:
theorem sum_range_pow
  given: (n p : Nat)
  proof: by
  have hne : forall m : Nat, (m ! : Rat) != 0 := fun m => mod_cast factorial_ne_zero m
  -- compute the Cauchy product of two power series
  have h_cauchy :
    ((mk fun p => bernoulli p / p !) * mk fun q => coeff (q + 1) (exp Rat ^ n)) =
      mk fun p => ∑ i in range (p + 1),
          bernoull

中文:
定理 sum_range_pow
  条件: (n p : 自然数)
  证明: by
  have hne : forall m : Nat, (m ! : Rat) != 0 := fun m => mod_cast factorial_ne_zero m
  -- compute the Cauchy product of two power series
  have h_cauchy :
    ((mk fun p => bernoulli p / p !) * mk fun q => coeff (q + 1) (exp Rat ^ n)) =
      mk fun p => ∑ i in range (p + 1),
          bernoull

Depends on / 依赖: factorial_ne_zero, mod_cast
-/
theorem sum_range_pow (n p : Nat) :
    (∑ k in range n, (k : Rat) ^ p) =
      ∑ i in range (p + 1), bernoulli i * ((p + 1).choose i) * (n : Rat) ^ (p + 1 - i) / (p + 1) := by
  have hne : forall m : Nat, (m ! : Rat) != 0 := fun m => mod_cast factorial_ne_zero m
  -- compute the Cauchy product of two power series
  have h_cauchy :
    ((mk fun p => bernoulli p / p !) * mk fun q => coeff (q + 1) (exp Rat ^ n)) =
      mk fun p => ∑ i in range (p + 1),
          bernoulli i * (p + 1).choose i * (n : Rat) ^ (p + 1 - i) / (p + 1)! := by
    ext q : 1
    let f a b := bernoulli a / a ! * coeff (b + 1) (exp Rat ^ n)
    -- key step: use `PowerSeries.coeff_mul` and then rewrite sums
    simp only [f, coeff_mul, coeff_mk, sum_antidiagonal_eq_sum_range_succ f]
    apply sum_congr rfl
    intro m h
    simp only [exp_pow_eq_rescale_exp, rescale, RingHom.coe_mk]
    -- manipulate factorials and binomial coefficients
    have h : m < q + 1 := by simpa using h
    rw [choose_eq_factorial_div_factorial h.le]; rw [eq_comm]; rw [div_eq_iff (hne q.succ)]; rw [succ_eq_add_one]; rw [mul_assoc _ _ (q.succ ! : Rat)]; rw [mul_comm _ (q.succ ! : Rat)]; rw [← mul_assoc]; rw [div_mul_eq_mul_div]
    simp only [MonoidHom.coe_mk, OneHom.coe_mk, coeff_exp, Algebra.algebraMap_self, one_div,
      map_inv₀, map_natCast, coeff_mk]
    rw [mul_comm ((n : Rat) ^ (q - m + 1))]; rw [← mul_assoc _ _ ((n : Rat) ^ (q - m + 1))]; rw [← one_div]; rw [mul_one_div]; rw [div_div]; rw [tsub_add_eq_add_tsub (le_of_lt_succ h)]; rw [cast_div]; rw [cast_mul]
    · ring
    · exact factorial_mul_factorial_dvd_factorial h.le
    · simp [factorial_ne_zero]
  -- same as our goal except we pull out `p!` for convenience
  have hps :
    (∑ k in range n, (k : Rat) ^ p) =
      (∑ i in range (p + 1),
          bernoulli i * (p + 1).choose i * (n : Rat) ^ (p + 1 - i) / (p + 1)!) * p ! := by
    suffices
      (mk fun p => ∑ k in range n, (k : Rat) ^ p * algebraMap Rat Rat p !⁻¹) =
        mk fun p =>
          ∑ i in range (p + 1), bernoulli i * (p + 1).choose i * (n : Rat) ^ (p + 1 - i) / (p + 1)! by
      rw [← div_eq_iff (hne p)]; rw [div_eq_mul_inv]; rw [sum_mul]
      rw [PowerSeries.ext_iff] at this
      simpa using this p
    -- the power series `exp ℚ - 1` is non-zero, a fact we need in order to use `mul_right_inj'`
    have hexp : exp Rat - 1 != 0 := by
      simp only [exp, PowerSeries.ext_iff, Ne, not_forall]
      use 1
      simp
    have h_r : exp Rat ^ n - 1 = X * mk fun p => coeff (p + 1) (exp Rat ^ n) := by
      have h_const : C (constantCoeff (exp Rat ^ n)) = 1 := by simp
      rw [← h_const]; rw [sub_const_eq_X_mul_shift]
    -- key step: a chain of equalities of power series
    rw [← mul_right_inj' hexp]; rw [mul_comm]
    rw [← exp_pow_sum]; rw [geom_sum_mul]; rw [h_r]; rw [← bernoulliPowerSeries_mul_exp_sub_one]; rw [bernoulliPowerSeries]; rw [mul_right_comm]
    simp only [mul_comm, mul_eq_mul_left_iff, hexp, or_false]
    refine Eq.trans (mul_eq_mul_right_iff.mpr ?_) (Eq.trans h_cauchy ?_)
    · left
      congr
    · simp only [mul_comm, factorial]
  -- massage `hps` into our goal
  rw [hps]; rw [sum_mul]
  refine sum_congr rfl fun x _ => ?_
  simp [field, factorial]

/--
theorem `sum_Ico_pow` / 定理 `sum_Ico_pow`

English:
theorem sum_Ico_pow
  given: (n p : Nat)
  proof: by
  rw [← Nat.cast_succ]
  -- dispose of the trivial case
  cases p with | zero => simp | succ p =>
  let f i := bernoulli i * p.succ.succ.choose i * (n : Rat) ^ (p.succ.succ - i) / p.succ.succ
  let f' i := bernoulli' i * p.succ.succ.choose i * (n : Rat) ^ (p.succ.succ - i) / p.succ.succ
  suffice

中文:
定理 sum_Ico_pow
  条件: (n p : 自然数)
  证明: by
  rw [← Nat.cast_succ]
  -- dispose of the trivial case
  cases p with | zero => simp | succ p =>
  let f i := bernoulli i * p.succ.succ.choose i * (n : Rat) ^ (p.succ.succ - i) / p.succ.succ
  let f' i := bernoulli' i * p.succ.succ.choose i * (n : Rat) ^ (p.succ.succ - i) / p.succ.succ
  suffice

Depends on / 依赖: Nat.cast_succ, cast_succ
-/
theorem sum_Ico_pow (n p : Nat) :
    (∑ k in Ico 1 (n + 1), (k : Rat) ^ p) =
      ∑ i in range (p + 1), bernoulli' i * (p + 1).choose i * (n : Rat) ^ (p + 1 - i) / (p + 1) := by
  rw [← Nat.cast_succ]
  -- dispose of the trivial case
  cases p with | zero => simp | succ p =>
  let f i := bernoulli i * p.succ.succ.choose i * (n : Rat) ^ (p.succ.succ - i) / p.succ.succ
  let f' i := bernoulli' i * p.succ.succ.choose i * (n : Rat) ^ (p.succ.succ - i) / p.succ.succ
  suffices (∑ k in Ico 1 n.succ, (k : Rat) ^ p.succ) = ∑ i in range p.succ.succ, f' i by convert!
    this
  -- prove some algebraic facts that will make things easier for us later on
  have hle := Nat.le_add_left 1 n
  have hne : (p + 1 + 1 : Rat) != 0 := by norm_cast
  have h1 : forall r : Rat, r * (p + 1 + 1) * (n : Rat) ^ p.succ / (p + 1 + 1 : Rat) = r * (n : Rat) ^ p.succ :=
      fun r => by rw [mul_div_right_comm, mul_div_cancel_right₀ _ hne]
  have h2 : f 1 + (n : Rat) ^ p.succ = 1 / 2 * (n : Rat) ^ p.succ := by
    simp_rw [f, bernoulli_one, choose_one_right, succ_sub_succ_eq_sub, cast_succ, tsub_zero, h1]
    ring
  have :
    (∑ i in range p, bernoulli (i + 2) * (p + 2).choose (i + 2) * (n : Rat) ^ (p - i) / ↑(p + 2)) =
      ∑ i in range p, bernoulli' (i + 2) * (p + 2).choose (i + 2) * (n : Rat) ^ (p - i) / ↑(p + 2) :=
    sum_congr rfl fun i _ => by rw [bernoulli_eq_bernoulli'_of_ne_one (succ_succ_ne_one i)]
  calc
    (-- replace sum over `Ico` with sum over `range` and simplify
        ∑ k in Ico 1 n.succ, (k : Rat) ^ p.succ)
    _ = ∑ k in range n.succ, (k : Rat) ^ p.succ := by simp [sum_Ico_eq_sub _ hle]
    -- extract the last term of the sum
    _ = (∑ k in range n, (k : Rat) ^ p.succ) + (n : Rat) ^ p.succ := by rw [sum_range_succ]
    -- apply the key lemma, `sum_range_pow`
    _ = (∑ i in range p.succ.succ, f i) + (n : Rat) ^ p.succ := by simp [f, sum_range_pow]
    -- extract the first two terms of the sum
    _ = (∑ i in range p, f i.succ.succ) + f 1 + f 0 + (n : Rat) ^ p.succ := by
      simp_rw [sum_range_succ']
    _ = (∑ i in range p, f i.succ.succ) + (f 1 + (n : Rat) ^ p.succ) + f 0 := by ring
    _ = (∑ i in range p, f i.succ.succ) + 1 / 2 * (n : Rat) ^ p.succ + f 0 := by rw [h2]
    -- convert from `bernoulli` to `bernoulli'`
    _ = (∑ i in range p, f' i.succ.succ) + f' 1 + f' 0 := by
      simpa [f, f', h1, fun i => show i + 2 = i + 1 + 1 from rfl]
    -- rejoin the first two terms of the sum
    _ = ∑ i in range p.succ.succ, f' i := by simp_rw [sum_range_succ']

end Faulhaber

section vonStaudtClausen

/-!
### The von Staudt-Clausen Theorem

Here we formalize Rado's proof of von Staudt-Clausen's theorem, which states that for any $k \ge 0$,
$$B_{2k} + \sum_{p \text{ prime}, (p - 1) \mid 2k} \frac{1}{p} \in \mathbb{Z}.$$
Rado's proof is based on Faulhaber's theorem and induction on $k$.
-/

namespace Bernoulli

/--
Definition of `noncomputable` / `noncomputable` 的定义

English:
definition noncomputable
  signature: def vonStaudtIndicator (k p : Nat)
  body: if (p - 1) ∣ k then 1 else 0

中文:
定义 noncomputable
  签名: def vonStaudtIndicator (k p : 自然数)
  定义体: if (p - 1) ∣ k then 1 else 0
-/
private noncomputable def vonStaudtIndicator (k p : Nat) : Rat :=
  if (p - 1) ∣ k then 1 else 0

/--
Definition of `vonStaudtPrimes` / `vonStaudtPrimes` 的定义

English:
abbreviation vonStaudtPrimes
  signature: (k : Nat)
  body: (range (2 * k + 2)).filter fun q => q.Prime ∧ (q - 1) ∣ 2 * k

中文:
缩写 vonStaudtPrimes
  签名: (k : 自然数)
  定义体: (range (2 * k + 2)).filter fun q => q.Prime ∧ (q - 1) ∣ 2 * k
-/
private abbrev vonStaudtPrimes (k : Nat) : Finset Nat :=
  (range (2 * k + 2)).filter fun q => q.Prime ∧ (q - 1) ∣ 2 * k

/--
lemma `sum_pow_add_indicator_eq_zero` / 引理 `sum_pow_add_indicator_eq_zero`

English:
lemma sum_pow_add_indicator_eq_zero
  given: {p : Nat} (l : Nat) [Fact p.Prime]
  proof: by
  have hbij : (∑ v in Ico 1 p, (v : ZMod p) ^ l) = ∑ u : (ZMod p)ˣ, (u : ZMod p) ^ l :=
    Finset.sum_bij'
      (fun v hv => Units.mk0 (v : ZMod p) (mt (ZMod.natCast_eq_zero_iff v p).mp (by
        grind [not_dvd_of_pos_of_lt])))
      (fun u _ => (u : ZMod p).val)
      (fun _ _ => Finset.mem_

中文:
引理 sum_pow_add_indicator_eq_zero
  条件: {p : 自然数} (l : 自然数) [Fact p.素]
  证明: by
  have hbij : (∑ v in Ico 1 p, (v : ZMod p) ^ l) = ∑ u : (ZMod p)ˣ, (u : ZMod p) ^ l :=
    Finset.sum_bij'
      (fun v hv => Units.mk0 (v : ZMod p) (mt (ZMod.natCast_eq_zero_iff v p).mp (by
        grind [not_dvd_of_pos_of_lt])))
      (fun u _ => (u : ZMod p).val)
      (fun _ _ => Finset.mem_
-/
private lemma sum_pow_add_indicator_eq_zero {p : Nat} (l : Nat) [Fact p.Prime] :
    (∑ v in Ico 1 p, (v : ZMod p) ^ l) + (if (p - 1) ∣ l then (1 : ZMod p) else 0) = 0 := by
  have hbij : (∑ v in Ico 1 p, (v : ZMod p) ^ l) = ∑ u : (ZMod p)ˣ, (u : ZMod p) ^ l :=
    Finset.sum_bij'
      (fun v hv => Units.mk0 (v : ZMod p) (mt (ZMod.natCast_eq_zero_iff v p).mp (by
        grind [not_dvd_of_pos_of_lt])))
      (fun u _ => (u : ZMod p).val)
      (fun _ _ => Finset.mem_univ _)
      (fun u _ => by grind [u.ne_zero, ZMod.val_ne_zero, ZMod.val_lt])
      (fun v hv => by simp [ZMod.val_cast_of_lt (Finset.mem_Ico.mp hv).2])
      (fun u _ => Units.ext (ZMod.natCast_zmod_val _))
      (fun _ _ => rfl)
  rw [hbij]; rw [FiniteField.sum_pow_units]; rw [ZMod.card]
  grind

/--
Definition of `pIntegral` / `pIntegral` 的定义

English:
abbreviation pIntegral
  signature: (p : Nat) (x : Rat) [Fact p.Prime]
  body: Rat.padicValuation p x <= 1

中文:
缩写 p整数egral
  签名: (p : 自然数) (x : 有理数) [Fact p.素]
  定义体: Rat.padicValuation p x <= 1
-/
private abbrev pIntegral (p : Nat) (x : Rat) [Fact p.Prime] : Prop := Rat.padicValuation p x <= 1

/--
lemma `pIntegral_mul` / 引理 `pIntegral_mul`

English:
lemma pIntegral_mul
  statement: {p : Nat} [Fact p.Prime] {x y : Rat}
  proof: ((Rat.padicValuation p).map_mul x y).trans_le (mul_le_one' hx hy)

中文:
引理 p整数egral_mul
  结论: {p : 自然数} [Fact p.素] {x y : 有理数}
  证明: ((Rat.padicValuation p).map_mul x y).trans_le (mul_le_one' hx hy)
-/
private lemma pIntegral_mul {p : Nat} [Fact p.Prime] {x y : Rat}
    (hx : pIntegral p x) (hy : pIntegral p y) : pIntegral p (x * y) :=
  ((Rat.padicValuation p).map_mul x y).trans_le (mul_le_one' hx hy)

/--
lemma `prod_one_div_prime_den_coprime` / 引理 `prod_one_div_prime_den_coprime`

English:
lemma prod_one_div_prime_den_coprime
  given: (k : Nat) {p : Nat} [Fact p.Prime]
  proof: by
  refine Nat.Coprime.prod_left fun q hq => ?_
  simp only [Finset.mem_filter, Finset.mem_range] at hq
  obtain ⟨⟨_, hq_prime, _⟩, hne⟩ := hq
  rw [show ((1 : Rat) / q).den = q by simp [hq_prime.ne_zero]]
  exact (Nat.coprime_primes hq_prime Fact.out).mpr hne

中文:
引理 prod_one_div_prime_den_coprime
  条件: (k : 自然数) {p : 自然数} [Fact p.素]
  证明: by
  refine Nat.Coprime.prod_left fun q hq => ?_
  simp only [Finset.mem_filter, Finset.mem_range] at hq
  obtain ⟨⟨_, hq_prime, _⟩, hne⟩ := hq
  rw [show ((1 : Rat) / q).den = q by simp [hq_prime.ne_zero]]
  exact (Nat.coprime_primes hq_prime Fact.out).mpr hne
-/
private lemma prod_one_div_prime_den_coprime (k : Nat) {p : Nat} [Fact p.Prime] :
    (∏ q in vonStaudtPrimes k with q != p, ((1 : Rat) / q).den).Coprime p := by
  refine Nat.Coprime.prod_left fun q hq => ?_
  simp only [Finset.mem_filter, Finset.mem_range] at hq
  obtain ⟨⟨_, hq_prime, _⟩, hne⟩ := hq
  rw [show ((1 : Rat) / q).den = q by simp [hq_prime.ne_zero]]
  exact (Nat.coprime_primes hq_prime Fact.out).mpr hne

/--
lemma `sum_one_div_prime_eq_indicator_div_add` / 引理 `sum_one_div_prime_eq_indicator_div_add`

English:
lemma sum_one_div_prime_eq_indicator_div_add
  given: {k p : Nat} (hk : k > 0) [Fact p.Prime]
  proof: by
  rw [Finset.sum_congr (Finset.filter_ne' (vonStaudtPrimes k) p) fun _ _ => rfl]
  by_cases hdvd : (p - 1) ∣ 2 * k
  · have hp_mem : p in vonStaudtPrimes k := Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (by have := Nat.le_of_dvd (by lia) hdvd; lia), Fact.out, hdvd⟩
    rw [← Finset.add_sum_

中文:
引理 sum_one_div_prime_eq_indicator_div_add
  条件: {k p : 自然数} (hk : k > 0) [Fact p.素]
  证明: by
  rw [Finset.sum_congr (Finset.filter_ne' (vonStaudtPrimes k) p) fun _ _ => rfl]
  by_cases hdvd : (p - 1) ∣ 2 * k
  · have hp_mem : p in vonStaudtPrimes k := Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (by have := Nat.le_of_dvd (by lia) hdvd; lia), Fact.out, hdvd⟩
    rw [← Finset.add_sum_
-/
private lemma sum_one_div_prime_eq_indicator_div_add {k p : Nat} (hk : k > 0) [Fact p.Prime] :
    (∑ q in vonStaudtPrimes k, (1 : Rat) / q) =
    vonStaudtIndicator (2 * k) p / p + ∑ q in vonStaudtPrimes k with q != p, (1 : Rat) / q := by
  rw [Finset.sum_congr (Finset.filter_ne' (vonStaudtPrimes k) p) fun _ _ => rfl]
  by_cases hdvd : (p - 1) ∣ 2 * k
  · have hp_mem : p in vonStaudtPrimes k := Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (by have := Nat.le_of_dvd (by lia) hdvd; lia), Fact.out, hdvd⟩
    rw [← Finset.add_sum_erase _ _ hp_mem]
    simp [vonStaudtIndicator, hdvd]
  · rw [Finset.erase_eq_of_notMem fun h => hdvd (Finset.mem_filter.mp h).2.2]
    simp [vonStaudtIndicator, hdvd]

/--
lemma `pIntegral_pow_div` / 引理 `pIntegral_pow_div`

English:
lemma pIntegral_pow_div
  statement: {p M N : Nat} [Fact p.Prime] (hM : M != 0)
  proof: by
  set e := M.factorization p
  set M' := M / p ^ e
  have hM'_cop : M'.Coprime p := (Nat.coprime_ordCompl Fact.out hM).symm
  have hp_ne : (p : Rat) != 0 := Nat.cast_ne_zero.mpr (Nat.Prime.ne_zero Fact.out)
  -- Rewrite p^N / M as p^(N-e) / M' where M' = M / p^e is coprime to p
  have hdecomp : p

中文:
引理 p整数egral_pow_div
  结论: {p M N : 自然数} [Fact p.素] (hM : M != 0)
  证明: by
  set e := M.factorization p
  set M' := M / p ^ e
  have hM'_cop : M'.Coprime p := (Nat.coprime_ordCompl Fact.out hM).symm
  have hp_ne : (p : Rat) != 0 := Nat.cast_ne_zero.mpr (Nat.Prime.ne_zero Fact.out)
  -- Rewrite p^N / M as p^(N-e) / M' where M' = M / p^e is coprime to p
  have hdecomp : p
-/
private lemma pIntegral_pow_div {p M N : Nat} [Fact p.Prime] (hM : M != 0)
    (hv : M.factorization p <= N) : pIntegral p ((p : Rat) ^ N / M) := by
  set e := M.factorization p
  set M' := M / p ^ e
  have hM'_cop : M'.Coprime p := (Nat.coprime_ordCompl Fact.out hM).symm
  have hp_ne : (p : Rat) != 0 := Nat.cast_ne_zero.mpr (Nat.Prime.ne_zero Fact.out)
  -- Rewrite p^N / M as p^(N-e) / M' where M' = M / p^e is coprime to p
  have hdecomp : p ^ e * M' = M := Nat.ordProj_mul_ordCompl_eq_self M p
  have hM_eq : (M : Rat) = ↑(p ^ e) * ↑M' := by rw [← hdecomp]; simp
  have hrw : (p : Rat) ^ N / M = (p : Rat) ^ (N - e) / M' := by
    rw [hM_eq]; rw [Nat.cast_pow]; rw [div_mul_eq_div_div]
    congr 1
    rw [div_eq_iff (pow_ne_zero e hp_ne)]; rw [← pow_add]; rw [Nat.sub_add_cancel hv]
  have hM'_eq : ((p : Rat) ^ (N - e) / (M' : Rat)) = Rat.divInt (p ^ (N - e) : Int) (M' : Int) := by
    norm_cast
    simp
  rw [hrw]
  exact Rat.padicValuation_le_one_iff.2 ((Nat.Prime.coprime_iff_not_dvd Fact.out).1
    (hM'_cop.coprime_dvd_left (by
      rw [hM'_eq]; exact Int.natCast_dvd_natCast.mp (Rat.den_dvd _ _))).symm)

/--
lemma `factorization_succ_le_sub_one` / 引理 `factorization_succ_le_sub_one`

English:
lemma factorization_succ_le_sub_one
  given: {p d : Nat} [Fact p.Prime] (hd : d >= 2)
  proof: by
  by_cases hcase : p = 2 ∧ d = 2
  · obtain ⟨rfl, rfl⟩ := hcase
    simp [Nat.factorization_eq_zero_of_not_dvd (by decide : ¬(2 ∣ 3))]
  · apply Nat.factorization_le_of_le_pow
    have hp2 := (Fact.out : p.Prime).two_le
    suffices forall n : Nat, n >= 2 -> ¬(p = 2 ∧ n = 2) -> n + 1 <= p ^ (n - 

中文:
引理 factorization_succ_le_sub_one
  条件: {p d : 自然数} [Fact p.素] (hd : d >= 2)
  证明: by
  by_cases hcase : p = 2 ∧ d = 2
  · obtain ⟨rfl, rfl⟩ := hcase
    simp [Nat.factorization_eq_zero_of_not_dvd (by decide : ¬(2 ∣ 3))]
  · apply Nat.factorization_le_of_le_pow
    have hp2 := (Fact.out : p.Prime).two_le
    suffices forall n : Nat, n >= 2 -> ¬(p = 2 ∧ n = 2) -> n + 1 <= p ^ (n - 
-/
private lemma factorization_succ_le_sub_one {p d : Nat} [Fact p.Prime] (hd : d >= 2) :
    (d + 1).factorization p <= d - 1 := by
  by_cases hcase : p = 2 ∧ d = 2
  · obtain ⟨rfl, rfl⟩ := hcase
    simp [Nat.factorization_eq_zero_of_not_dvd (by decide : ¬(2 ∣ 3))]
  · apply Nat.factorization_le_of_le_pow
    have hp2 := (Fact.out : p.Prime).two_le
    suffices forall n : Nat, n >= 2 -> ¬(p = 2 ∧ n = 2) -> n + 1 <= p ^ (n - 1) from this d hd hcase
    intro n hn hne'
    induction hn with
    | refl => norm_num at hne' ⊢; lia
    | @step m hm IH =>
      by_cases hm2 : p = 2 ∧ m = 2
      · obtain ⟨rfl, rfl⟩ := hm2; norm_num
      · calc m + 1 + 1 <= p ^ (m - 1) + 1 := by linarith [IH hm2]
          _ <= p ^ (m - 1) * p := by nlinarith [Nat.one_le_pow (m - 1) p (by lia)]
          _ = p ^ m := by rw [show m = m - 1 + 1 by lia]; exact pow_succ ..

/--
lemma `choose_two_mul_succ_mul_div_eq` / 引理 `choose_two_mul_succ_mul_div_eq`

English:
lemma choose_two_mul_succ_mul_div_eq
  given: {k m : Nat} (x : Rat) (hm_lt : m < k)
  proof: by
  rw [div_eq_div_iff (by norm_cast) (by norm_cast; lia)]; rw [mul_right_comm _ x]; rw [mul_right_comm _ x]
  refine congrArg (· * x) ?_
  rw [show (2 * (k : Rat) - 2 * (m : Rat) + 1) = (↑(2 * k + 1 - 2 * m) : Rat) by norm_cast; lia]
.symm exact_mod_cast Nat.choose_mul_succ_eq (2 * k) (2 * m)

中文:
引理 choose_two_mul_succ_mul_div_eq
  条件: {k m : 自然数} (x : 有理数) (hm_lt : m < k)
  证明: by
  rw [div_eq_div_iff (by norm_cast) (by norm_cast; lia)]; rw [mul_right_comm _ x]; rw [mul_right_comm _ x]
  refine congrArg (· * x) ?_
  rw [show (2 * (k : Rat) - 2 * (m : Rat) + 1) = (↑(2 * k + 1 - 2 * m) : Rat) by norm_cast; lia]
.symm exact_mod_cast Nat.choose_mul_succ_eq (2 * k) (2 * m)
-/
private lemma choose_two_mul_succ_mul_div_eq {k m : Nat} (x : Rat) (hm_lt : m < k) :
    ((2 * k + 1).choose (2 * m) : Rat) * x / (2 * k + 1) =
    ((2 * k).choose (2 * m) : Rat) * x / (2 * k - 2 * m + 1) := by
  rw [div_eq_div_iff (by norm_cast) (by norm_cast; lia)]; rw [mul_right_comm _ x]; rw [mul_right_comm _ x]
  refine congrArg (· * x) ?_
  rw [show (2 * (k : Rat) - 2 * (m : Rat) + 1) = (↑(2 * k + 1 - 2 * m) : Rat) by norm_cast; lia]
.symm exact_mod_cast Nat.choose_mul_succ_eq (2 * k) (2 * m)

/--
lemma `pIntegral_choose_mul_pow_div` / 引理 `pIntegral_choose_mul_pow_div`

English:
lemma pIntegral_choose_mul_pow_div
  statement: {k m p : Nat} (hm_lt : m < k) [Fact p.Prime]
  proof: by
  set d := 2 * k - 2 * m with hd_def
  have ⟨hd_plus_one_ne_zero, h_exp, hkm⟩ :
      d + 1 != 0 ∧ 2 * k - 2 * m - 1 = d - 1 ∧ 2 * m <= 2 * k := by lia
  have h_denom_rat : (2 * (k : Rat) - 2 * m + 1) = ((d + 1 : Nat) : Rat) := by
    simp only [hd_def]; push_cast [Nat.cast_sub hkm]; ring
  rw [h

中文:
引理 p整数egral_choose_mul_pow_div
  结论: {k m p : 自然数} (hm_lt : m < k) [Fact p.素]
  证明: by
  set d := 2 * k - 2 * m with hd_def
  have ⟨hd_plus_one_ne_zero, h_exp, hkm⟩ :
      d + 1 != 0 ∧ 2 * k - 2 * m - 1 = d - 1 ∧ 2 * m <= 2 * k := by lia
  have h_denom_rat : (2 * (k : Rat) - 2 * m + 1) = ((d + 1 : Nat) : Rat) := by
    simp only [hd_def]; push_cast [Nat.cast_sub hkm]; ring
  rw [h
-/
private lemma pIntegral_choose_mul_pow_div {k m p : Nat} (hm_lt : m < k) [Fact p.Prime]
    (hd : 2 * k - 2 * m >= 2) :
    pIntegral p (((2 * k).choose (2 * m) : Rat) * p ^ (2 * k - 2 * m - 1) / (2 * k - 2 * m + 1)) := by
  set d := 2 * k - 2 * m with hd_def
  have ⟨hd_plus_one_ne_zero, h_exp, hkm⟩ :
      d + 1 != 0 ∧ 2 * k - 2 * m - 1 = d - 1 ∧ 2 * m <= 2 * k := by lia
  have h_denom_rat : (2 * (k : Rat) - 2 * m + 1) = ((d + 1 : Nat) : Rat) := by
    simp only [hd_def]; push_cast [Nat.cast_sub hkm]; ring
  rw [h_exp]; rw [h_denom_rat]; rw [mul_div_assoc]
  exact pIntegral_mul (mod_cast Int.padicValuation_le_one p ((2 * k).choose (2 * m)))
    (pIntegral_pow_div hd_plus_one_ne_zero (factorization_succ_le_sub_one hd))

/--
lemma `pIntegral_bernoulli_even_term` / 引理 `pIntegral_bernoulli_even_term`

English:
lemma pIntegral_bernoulli_even_term
  statement: {k m p : Nat} (hm_lt : m < k) [Fact p.Prime]
  proof: by
  have hp_ne : (p : Rat) != 0 := mod_cast (Nat.Prime.ne_zero Fact.out)
  set P := (p : Rat) ^ (2 * k - 2 * m - 1)
  have hpow : (p : Rat) ^ (2 * k - 2 * m) = P * p := by
    rw [show 2 * k - 2 * m = (2 * k - 2 * m - 1) + 1 by lia]; rw [pow_succ]
  have hdecomp : bernoulli (2 * m) * ((2 * k + 1).c

中文:
引理 p整数egral_bernoulli_even_term
  结论: {k m p : 自然数} (hm_lt : m < k) [Fact p.素]
  证明: by
  have hp_ne : (p : Rat) != 0 := mod_cast (Nat.Prime.ne_zero Fact.out)
  set P := (p : Rat) ^ (2 * k - 2 * m - 1)
  have hpow : (p : Rat) ^ (2 * k - 2 * m) = P * p := by
    rw [show 2 * k - 2 * m = (2 * k - 2 * m - 1) + 1 by lia]; rw [pow_succ]
  have hdecomp : bernoulli (2 * m) * ((2 * k + 1).c
-/
private lemma pIntegral_bernoulli_even_term {k m p : Nat} (hm_lt : m < k) [Fact p.Prime]
    (ih : pIntegral p (bernoulli (2 * m) + vonStaudtIndicator (2 * m) p / p)) :
    pIntegral p (bernoulli (2 * m) * ((2 * k + 1).choose (2 * m)) *
      (p : Rat) ^ (2 * k - 2 * m) / (2 * k + 1)) := by
  have hp_ne : (p : Rat) != 0 := mod_cast (Nat.Prime.ne_zero Fact.out)
  set P := (p : Rat) ^ (2 * k - 2 * m - 1)
  have hpow : (p : Rat) ^ (2 * k - 2 * m) = P * p := by
    rw [show 2 * k - 2 * m = (2 * k - 2 * m - 1) + 1 by lia]; rw [pow_succ]
  have hdecomp : bernoulli (2 * m) * ((2 * k + 1).choose (2 * m)) *
      (p : Rat) ^ (2 * k - 2 * m) / (2 * k + 1) =
    (bernoulli (2 * m) + vonStaudtIndicator (2 * m) p / p) *
      ((2 * k + 1).choose (2 * m)) * (p : Rat) ^ (2 * k - 2 * m) / (2 * k + 1) -
    vonStaudtIndicator (2 * m) p * ((2 * k + 1).choose (2 * m)) *
      P / (2 * k + 1) := by rw [hpow]; field_simp [hp_ne]; ring
  rw [hdecomp]
  have hcmp := pIntegral_choose_mul_pow_div (p := p) hm_lt (by lia)
  have H x := choose_two_mul_succ_mul_div_eq x hm_lt
  apply (Rat.padicValuation p).map_sub_le
  · rw [mul_assoc, mul_div_assoc]
    apply pIntegral_mul ih
    have hpow_mul : ((2 * k).choose (2 * m) : Rat) * (p : Rat) ^ (2 * k - 2 * m) /
        (2 * k - 2 * m + 1) =
        (p : Rat) * (((2 * k).choose (2 * m) : Rat) * P / (2 * k - 2 * m + 1)) := by
      rw [hpow]; ring
    rw [H]; rw [hpow_mul]
    exact pIntegral_mul (Int.padicValuation_le_one p p) hcmp
  · unfold vonStaudtIndicator
    split_ifs
    · grind
    · simp

/--
lemma `pIntegral_faulhaber_sum` / 引理 `pIntegral_faulhaber_sum`

English:
lemma pIntegral_faulhaber_sum
  statement: {k p : Nat} (hk : k > 0) [Fact p.Prime]
  proof: by
  refine (Rat.padicValuation p).map_sum_le fun i hi => ?_
  rw [Finset.mem_range] at hi
  rcases i with _ | _ | i
  · simp only [bernoulli_zero, one_mul, Nat.choose_zero_right, Nat.cast_one, Nat.sub_zero]
    exact_mod_cast pIntegral_pow_div (by lia)
      (factorization_succ_le_sub_one (by lia) 

中文:
引理 p整数egral_faulhaber_sum
  结论: {k p : 自然数} (hk : k > 0) [Fact p.素]
  证明: by
  refine (Rat.padicValuation p).map_sum_le fun i hi => ?_
  rw [Finset.mem_range] at hi
  rcases i with _ | _ | i
  · simp only [bernoulli_zero, one_mul, Nat.choose_zero_right, Nat.cast_one, Nat.sub_zero]
    exact_mod_cast pIntegral_pow_div (by lia)
      (factorization_succ_le_sub_one (by lia) 
-/
private lemma pIntegral_faulhaber_sum {k p : Nat} (hk : k > 0) [Fact p.Prime]
    (ih : forall m, 0 < m -> m < k -> pIntegral p (bernoulli (2 * m) + vonStaudtIndicator (2 * m) p / p)) :
    pIntegral p (∑ i in range (2 * k),
      bernoulli i * ((2 * k + 1).choose i) * p ^ (2 * k - i) / (2 * k + 1)) := by
  refine (Rat.padicValuation p).map_sum_le fun i hi => ?_
  rw [Finset.mem_range] at hi
  rcases i with _ | _ | i
  · simp only [bernoulli_zero, one_mul, Nat.choose_zero_right, Nat.cast_one, Nat.sub_zero]
    exact_mod_cast pIntegral_pow_div (by lia)
      (factorization_succ_le_sub_one (by lia) |>.trans tsub_le_self)
  · rw [zero_add, Nat.choose_one_right, bernoulli_one]
    push_cast
    field_simp
    obtain rfl | hp2 := eq_or_ne p 2
    · push_cast
      rw [show 2 * k - 1 = (2 * k - 2) + 1 by lia]; rw [pow_succ]; rw [mul_div_cancel_right₀ _ two_ne_zero]
      exact_mod_cast Int.padicValuation_le_one ..
    · rw [Valuation.map_neg]
refine pIntegral_pow_div two_ne_zero
         (factorization_eq_zero_of_lt ?_).trans_le (by lia)
exact (Prime.odd_iff Fact.out).mp Prime.odd_of_ne_two Fact.out hp2
  · rcases Nat.even_or_odd (i + 2) with ⟨m, hm⟩ | hodd
    · have ⟨hm_pos, hm_lt, hi_eq⟩ : 0 < m ∧ m < k ∧ i + 2 = 2 * m := by lia
      simp only [hi_eq]
      exact pIntegral_bernoulli_even_term hm_lt (ih m hm_pos hm_lt)
    · simp [bernoulli_eq_zero_of_odd hodd (by lia)]

/--
lemma `sum_pow_filter_eq_faulhaber` / 引理 `sum_pow_filter_eq_faulhaber`

English:
lemma sum_pow_filter_eq_faulhaber
  given: {k : Nat} (p : Nat) (hk : 0 < k)
  proof: by
  have hfilter : (∑ v in Ico 1 p, (v : Rat) ^ (2 * k)) = ∑ v in range p, (v : Rat) ^ (2 * k) := by
    cases p <;> simp [Finset.sum_range_eq_add_Ico, show 2 * k != 0 by lia]
  rw [hfilter]; rw [sum_range_pow]; rw [Finset.sum_range_succ]; rw [Nat.choose_succ_self_right]; rw [show 2 * k + 1 - 2 * k

中文:
引理 sum_pow_filter_eq_faulhaber
  条件: {k : 自然数} (p : 自然数) (hk : 0 < k)
  证明: by
  have hfilter : (∑ v in Ico 1 p, (v : Rat) ^ (2 * k)) = ∑ v in range p, (v : Rat) ^ (2 * k) := by
    cases p <;> simp [Finset.sum_range_eq_add_Ico, show 2 * k != 0 by lia]
  rw [hfilter]; rw [sum_range_pow]; rw [Finset.sum_range_succ]; rw [Nat.choose_succ_self_right]; rw [show 2 * k + 1 - 2 * k
-/
private lemma sum_pow_filter_eq_faulhaber {k : Nat} (p : Nat) (hk : 0 < k) :
    (∑ v in Ico 1 p, (v : Rat) ^ (2 * k)) =
      (∑ i in range (2 * k), bernoulli i * ((2 * k + 1).choose i) *
        (p : Rat) ^ (2 * k + 1 - i) / (2 * k + 1)) + p * bernoulli (2 * k) := by
  have hfilter : (∑ v in Ico 1 p, (v : Rat) ^ (2 * k)) = ∑ v in range p, (v : Rat) ^ (2 * k) := by
    cases p <;> simp [Finset.sum_range_eq_add_Ico, show 2 * k != 0 by lia]
  rw [hfilter]; rw [sum_range_pow]; rw [Finset.sum_range_succ]; rw [Nat.choose_succ_self_right]; rw [show 2 * k + 1 - 2 * k = 1 by lia]
  push_cast
  field_simp

/--
lemma `faulhaber_sum_div_prime_eq` / 引理 `faulhaber_sum_div_prime_eq`

English:
lemma faulhaber_sum_div_prime_eq
  given: {k p : Nat} [Fact p.Prime]
  proof: by
  have hp_ne : (p : Rat) != 0 := mod_cast (Fact.out : p.Prime).ne_zero
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun i hi => ?_
  have := Finset.mem_range.mp hi
  rw [show 2 * k + 1 - i = (2 * k - i) + 1 by lia]; rw [pow_succ]
  field_simp [hp_ne]

中文:
引理 faulhaber_sum_div_prime_eq
  条件: {k p : 自然数} [Fact p.素]
  证明: by
  have hp_ne : (p : Rat) != 0 := mod_cast (Fact.out : p.Prime).ne_zero
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun i hi => ?_
  have := Finset.mem_range.mp hi
  rw [show 2 * k + 1 - i = (2 * k - i) + 1 by lia]; rw [pow_succ]
  field_simp [hp_ne]
-/
private lemma faulhaber_sum_div_prime_eq {k p : Nat} [Fact p.Prime] :
    (∑ i in range (2 * k), bernoulli i * ((2 * k + 1).choose i : Rat) *
      (p : Rat) ^ (2 * k + 1 - i) / (2 * k + 1 : Rat)) / (p : Rat) =
      ∑ i in range (2 * k), bernoulli i * ((2 * k + 1).choose i : Rat) *
        (p : Rat) ^ (2 * k - i) / (2 * k + 1 : Rat) := by
  have hp_ne : (p : Rat) != 0 := mod_cast (Fact.out : p.Prime).ne_zero
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun i hi => ?_
  have := Finset.mem_range.mp hi
  rw [show 2 * k + 1 - i = (2 * k - i) + 1 by lia]; rw [pow_succ]
  field_simp [hp_ne]

/--
lemma `bernoulli_add_indicator_eq_sub` / 引理 `bernoulli_add_indicator_eq_sub`

English:
lemma bernoulli_add_indicator_eq_sub
  given: {k p : Nat} (hk : k > 0) [Fact p.Prime]
  proof: by
  have hcast : (↑((∑ v in Ico 1 p, (v : Int) ^ (2 * k)) +
      (if (p - 1) ∣ 2 * k then 1 else 0)) : ZMod p) = 0 :=
    mod_cast sum_pow_add_indicator_eq_zero (p := p) _
  obtain ⟨T, hT_int⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hcast
  use T
  have hT : (∑ v in Ico 1 p, (v : Rat) ^ (2 *

中文:
引理 bernoulli_add_indicator_eq_sub
  条件: {k p : 自然数} (hk : k > 0) [Fact p.素]
  证明: by
  have hcast : (↑((∑ v in Ico 1 p, (v : Int) ^ (2 * k)) +
      (if (p - 1) ∣ 2 * k then 1 else 0)) : ZMod p) = 0 :=
    mod_cast sum_pow_add_indicator_eq_zero (p := p) _
  obtain ⟨T, hT_int⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hcast
  use T
  have hT : (∑ v in Ico 1 p, (v : Rat) ^ (2 *
-/
private lemma bernoulli_add_indicator_eq_sub {k p : Nat} (hk : k > 0) [Fact p.Prime] :
    exists T : Int, bernoulli (2 * k) + vonStaudtIndicator (2 * k) p / p =
      T - (∑ i in range (2 * k),
        bernoulli i * ((2 * k + 1).choose i) * (p : Rat) ^ (2 * k - i) / (2 * k + 1)) := by
  have hcast : (↑((∑ v in Ico 1 p, (v : Int) ^ (2 * k)) +
      (if (p - 1) ∣ 2 * k then 1 else 0)) : ZMod p) = 0 :=
    mod_cast sum_pow_add_indicator_eq_zero (p := p) _
  obtain ⟨T, hT_int⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hcast
  use T
  have hT : (∑ v in Ico 1 p, (v : Rat) ^ (2 * k)) + vonStaudtIndicator (2 * k) p =
      p * T := by unfold vonStaudtIndicator; exact_mod_cast hT_int
  have hp_ne : (p : Rat) != 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  have hAlg : bernoulli (2 * k) + vonStaudtIndicator (2 * k) p / p =
      T - (∑ i in range (2 * k), bernoulli i * ((2 * k + 1).choose i) *
        (p : Rat) ^ (2 * k + 1 - i) / (2 * k + 1)) / p := by
    field_simp [hp_ne]; linarith [hT, sum_pow_filter_eq_faulhaber p hk]
  rw [hAlg]; congr 1; simpa using faulhaber_sum_div_prime_eq

/--
lemma `not_dvd_den_bernoulli_add_indicator` / 引理 `not_dvd_den_bernoulli_add_indicator`

English:
lemma not_dvd_den_bernoulli_add_indicator
  given: {k p : Nat} (hk : k > 0) [Fact p.Prime]
  proof: by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    obtain ⟨T, hT⟩ := bernoulli_add_indicator_eq_sub (p := p) hk
    rw [hT]
    have hT_int : pIntegral p T := Int.padicValuation_le_one p T
    have hR := pIntegral_faulhaber_sum hk fun m hm_pos hm_lt =>
      Rat.padicValuation_le_

中文:
引理 not_dvd_den_bernoulli_add_indicator
  条件: {k p : 自然数} (hk : k > 0) [Fact p.素]
  证明: by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    obtain ⟨T, hT⟩ := bernoulli_add_indicator_eq_sub (p := p) hk
    rw [hT]
    have hT_int : pIntegral p T := Int.padicValuation_le_one p T
    have hR := pIntegral_faulhaber_sum hk fun m hm_pos hm_lt =>
      Rat.padicValuation_le_
-/
private lemma not_dvd_den_bernoulli_add_indicator {k p : Nat} (hk : k > 0) [Fact p.Prime] :
    ¬ p ∣ (bernoulli (2 * k) + vonStaudtIndicator (2 * k) p / p).den := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    obtain ⟨T, hT⟩ := bernoulli_add_indicator_eq_sub (p := p) hk
    rw [hT]
    have hT_int : pIntegral p T := Int.padicValuation_le_one p T
    have hR := pIntegral_faulhaber_sum hk fun m hm_pos hm_lt =>
      Rat.padicValuation_le_one_iff.mpr (ih m hm_lt hm_pos)
    exact Rat.padicValuation_le_one_iff.mp ((Rat.padicValuation p).map_sub_le hT_int hR)

/--
lemma `not_dvd_den_vonStaudt_sum` / 引理 `not_dvd_den_vonStaudt_sum`

English:
lemma not_dvd_den_vonStaudt_sum
  given: {k p : Nat} (hk : k > 0) [Fact p.Prime]
  proof: by
  rw [sum_one_div_prime_eq_indicator_div_add (p := p) hk]; rw [← add_assoc]
  have hcop_ind := ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr
    (not_dvd_den_bernoulli_add_indicator (p := p) hk)).symm
  have hcop_rest := Nat.Coprime.of_dvd_left (Rat.den_sum_dvd_prod_den _ _)
    (prod_one_div_pri

中文:
引理 not_dvd_den_vonStaudt_sum
  条件: {k p : 自然数} (hk : k > 0) [Fact p.素]
  证明: by
  rw [sum_one_div_prime_eq_indicator_div_add (p := p) hk]; rw [← add_assoc]
  have hcop_ind := ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr
    (not_dvd_den_bernoulli_add_indicator (p := p) hk)).symm
  have hcop_rest := Nat.Coprime.of_dvd_left (Rat.den_sum_dvd_prod_den _ _)
    (prod_one_div_pri
-/
private lemma not_dvd_den_vonStaudt_sum {k p : Nat} (hk : k > 0) [Fact p.Prime] :
    ¬ p ∣ (bernoulli (2 * k) + ∑ q in vonStaudtPrimes k, (1 : Rat) / q).den := by
  rw [sum_one_div_prime_eq_indicator_div_add (p := p) hk]; rw [← add_assoc]
  have hcop_ind := ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr
    (not_dvd_den_bernoulli_add_indicator (p := p) hk)).symm
  have hcop_rest := Nat.Coprime.of_dvd_left (Rat.den_sum_dvd_prod_den _ _)
    (prod_one_div_prime_den_coprime k (p := p))
  have hcop := (Nat.Coprime.of_dvd_left (Rat.add_den_dvd _ _) (hcop_ind.mul_left hcop_rest)).symm
  exact (Nat.Prime.coprime_iff_not_dvd Fact.out).1 hcop

/--
theorem `vonStaudt_clausen` / 定理 `vonStaudt_clausen`

English:
theorem vonStaudt_clausen
  given: (k : Nat)
  proof: by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exact ⟨1, by decide +kernel⟩
  · rw [Set.mem_range]
    refine ⟨_, Rat.coe_int_num_of_den_eq_one ?_⟩
    by_contra h
    obtain ⟨p, hp, hdvd⟩ := ne_one_iff_exists_prime_dvd.mp h
    exact (let : Fact p.Prime := ⟨hp⟩; not_dvd_den_vonStaudt_sum hk) hd

中文:
定理 vonStaudt_clausen
  条件: (k : 自然数)
  证明: by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exact ⟨1, by decide +kernel⟩
  · rw [Set.mem_range]
    refine ⟨_, Rat.coe_int_num_of_den_eq_one ?_⟩
    by_contra h
    obtain ⟨p, hp, hdvd⟩ := ne_one_iff_exists_prime_dvd.mp h
    exact (let : Fact p.Prime := ⟨hp⟩; not_dvd_den_vonStaudt_sum hk) hd

Depends on / 依赖: Nat.eq_zero_or_pos, Rat.coe_int_num_of_den_eq_one, Set.mem_range, coe_int_num_of_den_eq_one, eq_zero_or_pos, kernel, mem_range, ne_one_iff_exists_prime_dvd, ne_one_iff_exists_prime_dvd.mp, not_dvd_den_vonStaudt_sum, p.Prime
-/
theorem vonStaudt_clausen (k : Nat) :
    bernoulli (2 * k) + ∑ p in range (2 * k + 2) with p.Prime ∧ (p - 1) ∣ 2 * k,
      (1 : Rat) / p in Set.range Int.cast := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exact ⟨1, by decide +kernel⟩
  · rw [Set.mem_range]
    refine ⟨_, Rat.coe_int_num_of_den_eq_one ?_⟩
    by_contra h
    obtain ⟨p, hp, hdvd⟩ := ne_one_iff_exists_prime_dvd.mp h
    exact (let : Fact p.Prime := ⟨hp⟩; not_dvd_den_vonStaudt_sum hk) hdvd

end Bernoulli

end vonStaudtClausen
