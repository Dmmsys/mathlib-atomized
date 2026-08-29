/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Abhimanyu Pallavi Sudhir, Jean Lo, Calle Sönne
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Data.Nat.Factorization.Defs
public import Mathlib.Analysis.Normed.Module.RCLike.Real
public import Mathlib.Data.Rat.Cast.CharZero

/-!
# Real logarithm

In this file we define `Real.log` to be the logarithm of a real number. As usual, we extend it from
its domain `(0, +∞)` to a globally defined function. We choose to do it so that `log 0 = 0` and
`log (-x) = log x`.

We prove some basic properties of this function and show that it is continuous.

## Tags

logarithm, continuity
-/

@[expose] public section

open Set Filter Function

open Topology

noncomputable section

namespace Real

variable {x y : Real}

/-- The real logarithm function, equal to the inverse of the exponential for `x > 0`,
to `log |x|` for `x < 0`, and to `0` for `0`. We use this unconventional extension to
`(-∞, 0]` as it gives the formula `log (x * y) = log x + log y` for all nonzero `x` and `y`, and
the derivative of `log` is `1/x` away from `0`. -/
@[pp_nodot, wikidata Q11197]
/--
Definition of `log` / `log` 的定义

English:
definition log
  signature: (x : Real)
  body: if hx : x = 0 then 0 else expOrderIso.symm ⟨|x|, abs_pos.2 hx⟩

中文:
定义 log
  签名: (x : 实数)
  定义体: if hx : x = 0 then 0 else expOrderIso.symm ⟨|x|, abs_pos.2 hx⟩

Depends on / 依赖: abs_pos, expOrderIso, expOrderIso.symm
-/
noncomputable def log (x : Real) : Real :=
  if hx : x = 0 then 0 else expOrderIso.symm ⟨|x|, abs_pos.2 hx⟩

/--
theorem `log_of_ne_zero` / 定理 `log_of_ne_zero`

English:
theorem log_of_ne_zero
  given: (hx : x != 0)
  statement: log x = expOrderIso.symm ⟨|x|, abs_pos.2 hx⟩
  proof: dif_neg hx

中文:
定理 log_of_ne_zero
  条件: (hx : x != 0)
  结论: log x = expOrderIso.symm ⟨|x|, abs_pos.2 hx⟩
  证明: dif_neg hx

Depends on / 依赖: Category, dif_neg
-/
theorem log_of_ne_zero (hx : x != 0) : log x = expOrderIso.symm ⟨|x|, abs_pos.2 hx⟩ :=
  dif_neg hx

/--
theorem `log_of_pos` / 定理 `log_of_pos`

English:
theorem log_of_pos
  given: (hx : 0 < x)
  statement: log x = expOrderIso.symm ⟨x, hx⟩
  proof: by
  rw [log_of_ne_zero hx.ne']
  congr
  exact abs_of_pos hx

中文:
定理 log_of_pos
  条件: (hx : 0 < x)
  结论: log x = expOrderIso.symm ⟨x, hx⟩
  证明: by
  rw [log_of_ne_zero hx.ne']
  congr
  exact abs_of_pos hx

Depends on / 依赖: abs_of_pos, hx.ne, log_of_ne_zero
-/
theorem log_of_pos (hx : 0 < x) : log x = expOrderIso.symm ⟨x, hx⟩ := by
  rw [log_of_ne_zero hx.ne']
  congr
  exact abs_of_pos hx

set_option backward.isDefEq.respectTransparency false in
/--
theorem `exp_log_eq_abs` / 定理 `exp_log_eq_abs`

English:
theorem exp_log_eq_abs
  given: (hx : x != 0)
  statement: exp (log x) = |x|
  proof: by
  rw [log_of_ne_zero hx]; rw [← coe_expOrderIso_apply]; rw [OrderIso.apply_symm_apply]; rw [Subtype.coe_mk]

中文:
定理 exp_log_eq_abs
  条件: (hx : x != 0)
  结论: exp (log x) = |x|
  证明: by
  rw [log_of_ne_zero hx]; rw [← coe_expOrderIso_apply]; rw [OrderIso.apply_symm_apply]; rw [Subtype.coe_mk]

Depends on / 依赖: OrderIso, OrderIso.apply_symm_apply, Subtype, Subtype.coe_mk, apply_symm_apply, coe_expOrderIso_apply, coe_mk, log_of_ne_zero
-/
theorem exp_log_eq_abs (hx : x != 0) : exp (log x) = |x| := by
  rw [log_of_ne_zero hx]; rw [← coe_expOrderIso_apply]; rw [OrderIso.apply_symm_apply]; rw [Subtype.coe_mk]

/--
theorem `exp_log` / 定理 `exp_log`

English:
theorem exp_log
  given: (hx : 0 < x)
  statement: exp (log x) = x
  proof: by
  rw [exp_log_eq_abs hx.ne']
  exact abs_of_pos hx

中文:
定理 exp_log
  条件: (hx : 0 < x)
  结论: exp (log x) = x
  证明: by
  rw [exp_log_eq_abs hx.ne']
  exact abs_of_pos hx

Depends on / 依赖: abs_of_pos, exp_log_eq_abs, hx.ne
-/
theorem exp_log (hx : 0 < x) : exp (log x) = x := by
  rw [exp_log_eq_abs hx.ne']
  exact abs_of_pos hx

/--
theorem `exp_log_of_neg` / 定理 `exp_log_of_neg`

English:
theorem exp_log_of_neg
  given: (hx : x < 0)
  statement: exp (log x) = -x
  proof: by
  rw [exp_log_eq_abs (ne_of_lt hx)]
  exact abs_of_neg hx

中文:
定理 exp_log_of_neg
  条件: (hx : x < 0)
  结论: exp (log x) = -x
  证明: by
  rw [exp_log_eq_abs (ne_of_lt hx)]
  exact abs_of_neg hx

Depends on / 依赖: abs_of_neg, exp_log_eq_abs, ne_of_lt
-/
theorem exp_log_of_neg (hx : x < 0) : exp (log x) = -x := by
  rw [exp_log_eq_abs (ne_of_lt hx)]
  exact abs_of_neg hx

/--
theorem `le_exp_log` / 定理 `le_exp_log`

English:
theorem le_exp_log
  given: (x : Real)
  statement: x <= exp (log x)
  proof: by
  by_cases h_zero : x = 0
  · rw [h_zero, log, dif_pos rfl, exp_zero]
    exact zero_le_one
  · rw [exp_log_eq_abs h_zero]
    exact le_abs_self _

@[simp, push]

中文:
定理 le_exp_log
  条件: (x : 实数)
  结论: x <= exp (log x)
  证明: by
  by_cases h_zero : x = 0
  · rw [h_zero, log, dif_pos rfl, exp_zero]
    exact zero_le_one
  · rw [exp_log_eq_abs h_zero]
    exact le_abs_self _

@[simp, push]

Depends on / 依赖: dif_pos, exp_log_eq_abs, exp_zero, h_zero, le_abs_self, zero_le_one
-/
theorem le_exp_log (x : Real) : x <= exp (log x) := by
  by_cases h_zero : x = 0
  · rw [h_zero, log, dif_pos rfl, exp_zero]
    exact zero_le_one
  · rw [exp_log_eq_abs h_zero]
    exact le_abs_self _

@[simp, push]
/--
theorem `log_exp` / 定理 `log_exp`

English:
theorem log_exp
  given: (x : Real)
  statement: log (exp x) = x
  proof: exp_injective exp_log (exp_pos x)

中文:
定理 log_exp
  条件: (x : 实数)
  结论: log (exp x) = x
  证明: exp_injective exp_log (exp_pos x)

Depends on / 依赖: exp_injective, exp_log, exp_pos
-/
theorem log_exp (x : Real) : log (exp x) = x :=
exp_injective exp_log (exp_pos x)

/--
theorem `log_comp_exp` / 定理 `log_comp_exp`

English:
theorem log_comp_exp
  statement: log ∘ exp = id
  proof: funext log_exp

中文:
定理 log_comp_exp
  结论: log ∘ exp = id
  证明: funext log_exp
-/
@[simp] theorem log_comp_exp : log ∘ exp = id := funext log_exp

/--
theorem `exp_one_mul_le_exp` / 定理 `exp_one_mul_le_exp`

English:
theorem exp_one_mul_le_exp
  given: {x : Real}
  statement: exp 1 * x <= exp x
  proof: by
  by_cases hx0 : x <= 0
  · apply le_trans (mul_nonpos_of_nonneg_of_nonpos (exp_pos 1).le hx0) (exp_nonneg x)
  · have h := add_one_le_exp (log x)
    rwa [← exp_le_exp, exp_add, exp_log (lt_of_not_ge hx0), mul_comm] at h

中文:
定理 exp_one_mul_le_exp
  条件: {x : 实数}
  结论: exp 1 * x <= exp x
  证明: by
  by_cases hx0 : x <= 0
  · apply le_trans (mul_nonpos_of_nonneg_of_nonpos (exp_pos 1).le hx0) (exp_nonneg x)
  · have h := add_one_le_exp (log x)
    rwa [← exp_le_exp, exp_add, exp_log (lt_of_not_ge hx0), mul_comm] at h

Depends on / 依赖: add_one_le_exp, exp_add, exp_le_exp, exp_log, exp_nonneg, exp_pos, le_trans, lt_of_not_ge, mul_comm, mul_nonpos_of_nonneg_of_nonpos
-/
theorem exp_one_mul_le_exp {x : Real} : exp 1 * x <= exp x := by
  by_cases hx0 : x <= 0
  · apply le_trans (mul_nonpos_of_nonneg_of_nonpos (exp_pos 1).le hx0) (exp_nonneg x)
  · have h := add_one_le_exp (log x)
    rwa [← exp_le_exp, exp_add, exp_log (lt_of_not_ge hx0), mul_comm] at h

/--
theorem `two_mul_le_exp` / 定理 `two_mul_le_exp`

English:
theorem two_mul_le_exp
  given: {x : Real}
  statement: 2 * x <= exp x
  proof: by
  by_cases hx0 : x < 0
  · exact le_trans (mul_nonpos_of_nonneg_of_nonpos (by simp only [Nat.ofNat_nonneg]) hx0.le)
      (exp_nonneg x)
  · apply le_trans (mul_le_mul_of_nonneg_right _ (le_of_not_gt hx0)) exp_one_mul_le_exp
    have := Real.add_one_le_exp 1
    rwa [one_add_one_eq_two] at this

中文:
定理 two_mul_le_exp
  条件: {x : 实数}
  结论: 2 * x <= exp x
  证明: by
  by_cases hx0 : x < 0
  · exact le_trans (mul_nonpos_of_nonneg_of_nonpos (by simp only [Nat.ofNat_nonneg]) hx0.le)
      (exp_nonneg x)
  · apply le_trans (mul_le_mul_of_nonneg_right _ (le_of_not_gt hx0)) exp_one_mul_le_exp
    have := Real.add_one_le_exp 1
    rwa [one_add_one_eq_two] at this

Depends on / 依赖: Nat.ofNat_nonneg, Real.add_one_le_exp, add_one_le_exp, exp_nonneg, exp_one_mul_le_exp, hx0.le, le_of_not_gt, le_trans, mul_le_mul_of_nonneg_right, mul_nonpos_of_nonneg_of_nonpos, ofNat_nonneg, one_add_one_eq_two
-/
theorem two_mul_le_exp {x : Real} : 2 * x <= exp x := by
  by_cases hx0 : x < 0
  · exact le_trans (mul_nonpos_of_nonneg_of_nonpos (by simp only [Nat.ofNat_nonneg]) hx0.le)
      (exp_nonneg x)
  · apply le_trans (mul_le_mul_of_nonneg_right _ (le_of_not_gt hx0)) exp_one_mul_le_exp
    have := Real.add_one_le_exp 1
    rwa [one_add_one_eq_two] at this

/--
theorem `surjOn_log` / 定理 `surjOn_log`

English:
theorem surjOn_log
  statement: SurjOn log (Ioi 0) univ
  proof: fun x _ => ⟨exp x, exp_pos x, log_exp x⟩

中文:
定理 surjOn_log
  结论: 满射限制 log (左开右无界区间 0) univ
  证明: fun x _ => ⟨exp x, exp_pos x, log_exp x⟩

Depends on / 依赖: exp_pos, log_exp
-/
theorem surjOn_log : SurjOn log (Ioi 0) univ := fun x _ => ⟨exp x, exp_pos x, log_exp x⟩

/--
theorem `log_surjective` / 定理 `log_surjective`

English:
theorem log_surjective
  statement: Surjective log
  proof: fun x => ⟨exp x, log_exp x⟩

@[simp]

中文:
定理 log_surjective
  结论: 满射 log
  证明: fun x => ⟨exp x, log_exp x⟩

@[simp]

Depends on / 依赖: log_exp
-/
theorem log_surjective : Surjective log := fun x => ⟨exp x, log_exp x⟩

@[simp]
/--
theorem `range_log` / 定理 `range_log`

English:
theorem range_log
  statement: range log = univ
  proof: log_surjective.range_eq

@[simp, push]

中文:
定理 range_log
  结论: range log = univ
  证明: log_surjective.range_eq

@[simp, push]

Depends on / 依赖: log_surjective, log_surjective.range_eq, range_eq
-/
theorem range_log : range log = univ :=
  log_surjective.range_eq

@[simp, push]
/--
theorem `log_zero` / 定理 `log_zero`

English:
theorem log_zero
  statement: log 0 = 0
  proof: dif_pos rfl

@[simp, push]

中文:
定理 log_zero
  结论: log 0 = 0
  证明: dif_pos rfl

@[simp, push]

Depends on / 依赖: dif_pos
-/
theorem log_zero : log 0 = 0 :=
  dif_pos rfl

@[simp, push]
/--
theorem `log_one` / 定理 `log_one`

English:
theorem log_one
  statement: log 1 = 0
  proof: exp_injective by rw [exp_log zero_lt_one, exp_zero]

中文:
定理 log_one
  结论: log 1 = 0
  证明: exp_injective by rw [exp_log zero_lt_one, exp_zero]

Depends on / 依赖: exp_injective, exp_log, exp_zero, zero_lt_one
-/
theorem log_one : log 1 = 0 :=
exp_injective by rw [exp_log zero_lt_one, exp_zero]

/--
lemma `log_div_self` / 引理 `log_div_self`

English:
lemma log_div_self
  given: (x : Real)
  statement: log (x / x) = 0
  proof: by
  obtain rfl | hx := eq_or_ne x 0 <;> simp [*]

@[simp, push]

中文:
引理 log_div_self
  条件: (x : 实数)
  结论: log (x / x) = 0
  证明: by
  obtain rfl | hx := eq_or_ne x 0 <;> simp [*]

@[simp, push]
-/
@[simp] lemma log_div_self (x : Real) : log (x / x) = 0 := by
  obtain rfl | hx := eq_or_ne x 0 <;> simp [*]

@[simp, push]
/--
theorem `log_abs` / 定理 `log_abs`

English:
theorem log_abs
  given: (x : Real)
  statement: log |x| = log x
  proof: by
  by_cases h : x = 0
  · simp [h]
  · rw [← exp_eq_exp, exp_log_eq_abs h, exp_log_eq_abs (abs_pos.2 h).ne', abs_abs]

@[simp, push]

中文:
定理 log_abs
  条件: (x : 实数)
  结论: log |x| = log x
  证明: by
  by_cases h : x = 0
  · simp [h]
  · rw [← exp_eq_exp, exp_log_eq_abs h, exp_log_eq_abs (abs_pos.2 h).ne', abs_abs]

@[simp, push]

Depends on / 依赖: abs_abs, abs_pos, exp_eq_exp, exp_log_eq_abs
-/
theorem log_abs (x : Real) : log |x| = log x := by
  by_cases h : x = 0
  · simp [h]
  · rw [← exp_eq_exp, exp_log_eq_abs h, exp_log_eq_abs (abs_pos.2 h).ne', abs_abs]

@[simp, push]
/--
theorem `log_neg_eq_log` / 定理 `log_neg_eq_log`

English:
theorem log_neg_eq_log
  given: (x : Real)
  statement: log (-x) = log x
  proof: by rw [← log_abs x, ← log_abs (-x), abs_neg]

中文:
定理 log_neg_eq_log
  条件: (x : 实数)
  结论: log (-x) = log x
  证明: by rw [← log_abs x, ← log_abs (-x), abs_neg]

Depends on / 依赖: abs_neg, log_abs
-/
theorem log_neg_eq_log (x : Real) : log (-x) = log x := by rw [← log_abs x, ← log_abs (-x), abs_neg]

/--
theorem `sinh_log` / 定理 `sinh_log`

English:
theorem sinh_log
  given: {x : Real} (hx : 0 < x)
  statement: sinh (log x) = (x - x⁻¹) / 2
  proof: by
  rw [sinh_eq]; rw [exp_neg]; rw [exp_log hx]

中文:
定理 sinh_log
  条件: {x : 实数} (hx : 0 < x)
  结论: sinh (log x) = (x - x⁻¹) / 2
  证明: by
  rw [sinh_eq]; rw [exp_neg]; rw [exp_log hx]

Depends on / 依赖: exp_log, exp_neg, sinh_eq
-/
theorem sinh_log {x : Real} (hx : 0 < x) : sinh (log x) = (x - x⁻¹) / 2 := by
  rw [sinh_eq]; rw [exp_neg]; rw [exp_log hx]

/--
theorem `cosh_log` / 定理 `cosh_log`

English:
theorem cosh_log
  given: {x : Real} (hx : 0 < x)
  statement: cosh (log x) = (x + x⁻¹) / 2
  proof: by
  rw [cosh_eq]; rw [exp_neg]; rw [exp_log hx]

中文:
定理 cosh_log
  条件: {x : 实数} (hx : 0 < x)
  结论: cosh (log x) = (x + x⁻¹) / 2
  证明: by
  rw [cosh_eq]; rw [exp_neg]; rw [exp_log hx]

Depends on / 依赖: cosh_eq, exp_log, exp_neg
-/
theorem cosh_log {x : Real} (hx : 0 < x) : cosh (log x) = (x + x⁻¹) / 2 := by
  rw [cosh_eq]; rw [exp_neg]; rw [exp_log hx]

/--
theorem `surjOn_log'` / 定理 `surjOn_log'`

English:
theorem surjOn_log'
  statement: SurjOn log (Iio 0) univ
  proof: fun x _ =>
⟨-exp x, neg_lt_zero.2 exp_pos x, by rw [log_neg_eq_log, log_exp]⟩

@[push]

中文:
定理 surjOn_log'
  结论: 满射限制 log (左无界右开区间 0) univ
  证明: fun x _ =>
⟨-exp x, neg_lt_zero.2 exp_pos x, by rw [log_neg_eq_log, log_exp]⟩

@[push]
-/
theorem surjOn_log' : SurjOn log (Iio 0) univ := fun x _ =>
⟨-exp x, neg_lt_zero.2 exp_pos x, by rw [log_neg_eq_log, log_exp]⟩

@[push]
/--
theorem `log_mul` / 定理 `log_mul`

English:
theorem log_mul
  given: (hx : x != 0) (hy : y != 0)
  statement: log (x * y) = log x + log y
  proof: exp_injective by
    rw [exp_log_eq_abs (mul_ne_zero hx hy)]; rw [exp_add]; rw [exp_log_eq_abs hx]; rw [exp_log_eq_abs hy]; rw [abs_mul]

@[push]

中文:
定理 log_mul
  条件: (hx : x != 0) (hy : y != 0)
  结论: log (x * y) = log x + log y
  证明: exp_injective by
    rw [exp_log_eq_abs (mul_ne_zero hx hy)]; rw [exp_add]; rw [exp_log_eq_abs hx]; rw [exp_log_eq_abs hy]; rw [abs_mul]

@[push]

Depends on / 依赖: abs_mul, exp_add, exp_injective, exp_log_eq_abs, mul_ne_zero
-/
theorem log_mul (hx : x != 0) (hy : y != 0) : log (x * y) = log x + log y :=
exp_injective by
    rw [exp_log_eq_abs (mul_ne_zero hx hy)]; rw [exp_add]; rw [exp_log_eq_abs hx]; rw [exp_log_eq_abs hy]; rw [abs_mul]

@[push]
/--
theorem `log_div` / 定理 `log_div`

English:
theorem log_div
  given: (hx : x != 0) (hy : y != 0)
  statement: log (x / y) = log x - log y
  proof: exp_injective by
    rw [exp_log_eq_abs (div_ne_zero hx hy)]; rw [exp_sub]; rw [exp_log_eq_abs hx]; rw [exp_log_eq_abs hy]; rw [abs_div]

@[simp, push]

中文:
定理 log_div
  条件: (hx : x != 0) (hy : y != 0)
  结论: log (x / y) = log x - log y
  证明: exp_injective by
    rw [exp_log_eq_abs (div_ne_zero hx hy)]; rw [exp_sub]; rw [exp_log_eq_abs hx]; rw [exp_log_eq_abs hy]; rw [abs_div]

@[simp, push]

Depends on / 依赖: abs_div, div_ne_zero, exp_injective, exp_log_eq_abs, exp_sub
-/
theorem log_div (hx : x != 0) (hy : y != 0) : log (x / y) = log x - log y :=
exp_injective by
    rw [exp_log_eq_abs (div_ne_zero hx hy)]; rw [exp_sub]; rw [exp_log_eq_abs hx]; rw [exp_log_eq_abs hy]; rw [abs_div]

@[simp, push]
/--
theorem `log_inv` / 定理 `log_inv`

English:
theorem log_inv
  given: (x : Real)
  statement: log x⁻¹ = -log x
  proof: by
  by_cases hx : x = 0; · simp [hx]
  rw [← exp_eq_exp]; rw [exp_log_eq_abs (inv_ne_zero hx)]; rw [exp_neg]; rw [exp_log_eq_abs hx]; rw [abs_inv]

中文:
定理 log_inv
  条件: (x : 实数)
  结论: log x⁻¹ = -log x
  证明: by
  by_cases hx : x = 0; · simp [hx]
  rw [← exp_eq_exp]; rw [exp_log_eq_abs (inv_ne_zero hx)]; rw [exp_neg]; rw [exp_log_eq_abs hx]; rw [abs_inv]

Depends on / 依赖: abs_inv, exp_eq_exp, exp_log_eq_abs, exp_neg, inv_ne_zero
-/
theorem log_inv (x : Real) : log x⁻¹ = -log x := by
  by_cases hx : x = 0; · simp [hx]
  rw [← exp_eq_exp]; rw [exp_log_eq_abs (inv_ne_zero hx)]; rw [exp_neg]; rw [exp_log_eq_abs hx]; rw [abs_inv]

/--
theorem `log_le_log_iff` / 定理 `log_le_log_iff`

English:
theorem log_le_log_iff
  given: (h : 0 < x) (h₁ : 0 < y)
  statement: log x <= log y ↔ x <= y
  proof: by
  rw [← exp_le_exp]; rw [exp_log h]; rw [exp_log h₁]

@[gcongr, bound]

中文:
定理 log_le_log_iff
  条件: (h : 0 < x) (h₁ : 0 < y)
  结论: log x <= log y ↔ x <= y
  证明: by
  rw [← exp_le_exp]; rw [exp_log h]; rw [exp_log h₁]

@[gcongr, bound]

Depends on / 依赖: exp_le_exp, exp_log
-/
theorem log_le_log_iff (h : 0 < x) (h₁ : 0 < y) : log x <= log y ↔ x <= y := by
  rw [← exp_le_exp]; rw [exp_log h]; rw [exp_log h₁]

@[gcongr, bound]
/--
lemma `log_le_log` / 引理 `log_le_log`

English:
lemma log_le_log
  given: (hx : 0 < x) (hxy : x <= y)
  statement: log x <= log y
  proof: (log_le_log_iff hx (hx.trans_le hxy)).2 hxy

@[gcongr, bound]

中文:
引理 log_le_log
  条件: (hx : 0 < x) (hxy : x <= y)
  结论: log x <= log y
  证明: (log_le_log_iff hx (hx.trans_le hxy)).2 hxy

@[gcongr, bound]

Depends on / 依赖: Hom.mk, homEquiv, hx.trans_le, log_le_log_iff, trans_le
-/
lemma log_le_log (hx : 0 < x) (hxy : x <= y) : log x <= log y :=
  (log_le_log_iff hx (hx.trans_le hxy)).2 hxy

@[gcongr, bound]
/--
theorem `log_lt_log` / 定理 `log_lt_log`

English:
theorem log_lt_log
  given: (hx : 0 < x) (h : x < y)
  statement: log x < log y
  proof: by
  rwa [← exp_lt_exp, exp_log hx, exp_log (lt_trans hx h)]

中文:
定理 log_lt_log
  条件: (hx : 0 < x) (h : x < y)
  结论: log x < log y
  证明: by
  rwa [← exp_lt_exp, exp_log hx, exp_log (lt_trans hx h)]

Depends on / 依赖: exp_log, exp_lt_exp, lt_trans
-/
theorem log_lt_log (hx : 0 < x) (h : x < y) : log x < log y := by
  rwa [← exp_lt_exp, exp_log hx, exp_log (lt_trans hx h)]

/--
theorem `log_lt_log_iff` / 定理 `log_lt_log_iff`

English:
theorem log_lt_log_iff
  given: (hx : 0 < x) (hy : 0 < y)
  statement: log x < log y ↔ x < y
  proof: by
  rw [← exp_lt_exp]; rw [exp_log hx]; rw [exp_log hy]

中文:
定理 log_lt_log_iff
  条件: (hx : 0 < x) (hy : 0 < y)
  结论: log x < log y ↔ x < y
  证明: by
  rw [← exp_lt_exp]; rw [exp_log hx]; rw [exp_log hy]

Depends on / 依赖: exp_log, exp_lt_exp
-/
theorem log_lt_log_iff (hx : 0 < x) (hy : 0 < y) : log x < log y ↔ x < y := by
  rw [← exp_lt_exp]; rw [exp_log hx]; rw [exp_log hy]

/--
theorem `log_le_iff_le_exp` / 定理 `log_le_iff_le_exp`

English:
theorem log_le_iff_le_exp
  given: (hx : 0 < x)
  statement: log x <= y ↔ x <= exp y
  proof: by rw [← exp_le_exp, exp_log hx]

中文:
定理 log_le_iff_le_exp
  条件: (hx : 0 < x)
  结论: log x <= y ↔ x <= exp y
  证明: by rw [← exp_le_exp, exp_log hx]

Depends on / 依赖: exp_le_exp, exp_log
-/
theorem log_le_iff_le_exp (hx : 0 < x) : log x <= y ↔ x <= exp y := by rw [← exp_le_exp, exp_log hx]

/--
theorem `log_lt_iff_lt_exp` / 定理 `log_lt_iff_lt_exp`

English:
theorem log_lt_iff_lt_exp
  given: (hx : 0 < x)
  statement: log x < y ↔ x < exp y
  proof: by rw [← exp_lt_exp, exp_log hx]

中文:
定理 log_lt_iff_lt_exp
  条件: (hx : 0 < x)
  结论: log x < y ↔ x < exp y
  证明: by rw [← exp_lt_exp, exp_log hx]

Depends on / 依赖: exp_log, exp_lt_exp
-/
theorem log_lt_iff_lt_exp (hx : 0 < x) : log x < y ↔ x < exp y := by rw [← exp_lt_exp, exp_log hx]

/--
theorem `le_log_iff_exp_le` / 定理 `le_log_iff_exp_le`

English:
theorem le_log_iff_exp_le
  given: (hy : 0 < y)
  statement: x <= log y ↔ exp x <= y
  proof: by rw [← exp_le_exp, exp_log hy]

中文:
定理 le_log_iff_exp_le
  条件: (hy : 0 < y)
  结论: x <= log y ↔ exp x <= y
  证明: by rw [← exp_le_exp, exp_log hy]

Depends on / 依赖: exp_le_exp, exp_log
-/
theorem le_log_iff_exp_le (hy : 0 < y) : x <= log y ↔ exp x <= y := by rw [← exp_le_exp, exp_log hy]

/--
theorem `lt_log_iff_exp_lt` / 定理 `lt_log_iff_exp_lt`

English:
theorem lt_log_iff_exp_lt
  given: (hy : 0 < y)
  statement: x < log y ↔ exp x < y
  proof: by rw [← exp_lt_exp, exp_log hy]

中文:
定理 lt_log_iff_exp_lt
  条件: (hy : 0 < y)
  结论: x < log y ↔ exp x < y
  证明: by rw [← exp_lt_exp, exp_log hy]

Depends on / 依赖: exp_log, exp_lt_exp
-/
theorem lt_log_iff_exp_lt (hy : 0 < y) : x < log y ↔ exp x < y := by rw [← exp_lt_exp, exp_log hy]

/--
lemma `le_exp_of_log_le` / 引理 `le_exp_of_log_le`

English:
lemma le_exp_of_log_le
  given: (h : log x <= y)
  statement: x <= exp y
  proof: by
  rcases le_or_gt x 0 with hx | hx
· exact hx.trans exp_nonneg y
  · exact (log_le_iff_le_exp hx).mp h

中文:
引理 le_exp_of_log_le
  条件: (h : log x <= y)
  结论: x <= exp y
  证明: by
  rcases le_or_gt x 0 with hx | hx
· exact hx.trans exp_nonneg y
  · exact (log_le_iff_le_exp hx).mp h

Depends on / 依赖: exp_nonneg, hx.trans, le_or_gt, log_le_iff_le_exp
-/
lemma le_exp_of_log_le (h : log x <= y) : x <= exp y := by
  rcases le_or_gt x 0 with hx | hx
· exact hx.trans exp_nonneg y
  · exact (log_le_iff_le_exp hx).mp h

/--
lemma `lt_exp_of_log_lt` / 引理 `lt_exp_of_log_lt`

English:
lemma lt_exp_of_log_lt
  given: (h : log x < y)
  statement: x < exp y
  proof: by
  rcases le_or_gt x 0 with hx | hx
· exact hx.trans_lt exp_pos y
  · exact (log_lt_iff_lt_exp hx).mp h

中文:
引理 lt_exp_of_log_lt
  条件: (h : log x < y)
  结论: x < exp y
  证明: by
  rcases le_or_gt x 0 with hx | hx
· exact hx.trans_lt exp_pos y
  · exact (log_lt_iff_lt_exp hx).mp h

Depends on / 依赖: exp_pos, hx.trans_lt, le_or_gt, log_lt_iff_lt_exp, trans_lt
-/
lemma lt_exp_of_log_lt (h : log x < y) : x < exp y := by
  rcases le_or_gt x 0 with hx | hx
· exact hx.trans_lt exp_pos y
  · exact (log_lt_iff_lt_exp hx).mp h

/--
theorem `log_pos_iff` / 定理 `log_pos_iff`

English:
theorem log_pos_iff
  given: (hx : 0 <= x)
  statement: 0 < log x ↔ 1 < x
  proof: by
  rcases hx.eq_or_lt with (rfl | hx)
  · simp [zero_le_one]
  rw [← log_one]
  exact log_lt_log_iff zero_lt_one hx

@[bound]

中文:
定理 log_pos_iff
  条件: (hx : 0 <= x)
  结论: 0 < log x ↔ 1 < x
  证明: by
  rcases hx.eq_or_lt with (rfl | hx)
  · simp [zero_le_one]
  rw [← log_one]
  exact log_lt_log_iff zero_lt_one hx

@[bound]

Depends on / 依赖: eq_or_lt, hx.eq_or_lt, log_lt_log_iff, log_one, zero_le_one, zero_lt_one
-/
theorem log_pos_iff (hx : 0 <= x) : 0 < log x ↔ 1 < x := by
  rcases hx.eq_or_lt with (rfl | hx)
  · simp [zero_le_one]
  rw [← log_one]
  exact log_lt_log_iff zero_lt_one hx

@[bound]
/--
theorem `log_pos` / 定理 `log_pos`

English:
theorem log_pos
  given: (hx : 1 < x)
  statement: 0 < log x
  proof: (log_pos_iff (lt_trans zero_lt_one hx).le).2 hx

中文:
定理 log_pos
  条件: (hx : 1 < x)
  结论: 0 < log x
  证明: (log_pos_iff (lt_trans zero_lt_one hx).le).2 hx

Depends on / 依赖: log_pos_iff, lt_trans, zero_lt_one
-/
theorem log_pos (hx : 1 < x) : 0 < log x :=
  (log_pos_iff (lt_trans zero_lt_one hx).le).2 hx

/--
theorem `log_pos_of_lt_neg_one` / 定理 `log_pos_of_lt_neg_one`

English:
theorem log_pos_of_lt_neg_one
  given: (hx : x < -1)
  statement: 0 < log x
  proof: by
  rw [← neg_neg x]; rw [log_neg_eq_log]
  have : 1 < -x := by linarith
  exact log_pos this

中文:
定理 log_pos_of_lt_neg_one
  条件: (hx : x < -1)
  结论: 0 < log x
  证明: by
  rw [← neg_neg x]; rw [log_neg_eq_log]
  have : 1 < -x := by linarith
  exact log_pos this

Depends on / 依赖: log_neg_eq_log, log_pos, neg_neg
-/
theorem log_pos_of_lt_neg_one (hx : x < -1) : 0 < log x := by
  rw [← neg_neg x]; rw [log_neg_eq_log]
  have : 1 < -x := by linarith
  exact log_pos this

/--
theorem `log_neg_iff` / 定理 `log_neg_iff`

English:
theorem log_neg_iff
  given: (h : 0 < x)
  statement: log x < 0 ↔ x < 1
  proof: by
  rw [← log_one]
  exact log_lt_log_iff h zero_lt_one

@[bound]

中文:
定理 log_neg_iff
  条件: (h : 0 < x)
  结论: log x < 0 ↔ x < 1
  证明: by
  rw [← log_one]
  exact log_lt_log_iff h zero_lt_one

@[bound]

Depends on / 依赖: log_lt_log_iff, log_one, zero_lt_one
-/
theorem log_neg_iff (h : 0 < x) : log x < 0 ↔ x < 1 := by
  rw [← log_one]
  exact log_lt_log_iff h zero_lt_one

@[bound]
/--
theorem `log_neg` / 定理 `log_neg`

English:
theorem log_neg
  given: (h0 : 0 < x) (h1 : x < 1)
  statement: log x < 0
  proof: (log_neg_iff h0).2 h1

中文:
定理 log_neg
  条件: (h0 : 0 < x) (h1 : x < 1)
  结论: log x < 0
  证明: (log_neg_iff h0).2 h1

Depends on / 依赖: log_neg_iff
-/
theorem log_neg (h0 : 0 < x) (h1 : x < 1) : log x < 0 :=
  (log_neg_iff h0).2 h1

/--
theorem `log_neg_of_lt_zero` / 定理 `log_neg_of_lt_zero`

English:
theorem log_neg_of_lt_zero
  given: (h0 : x < 0) (h1 : -1 < x)
  statement: log x < 0
  proof: by
  rw [← neg_neg x]; rw [log_neg_eq_log]
  have h0' : 0 < -x := by linarith
  have h1' : -x < 1 := by linarith
  exact log_neg h0' h1'

中文:
定理 log_neg_of_lt_zero
  条件: (h0 : x < 0) (h1 : -1 < x)
  结论: log x < 0
  证明: by
  rw [← neg_neg x]; rw [log_neg_eq_log]
  have h0' : 0 < -x := by linarith
  have h1' : -x < 1 := by linarith
  exact log_neg h0' h1'

Depends on / 依赖: log_neg, log_neg_eq_log, neg_neg
-/
theorem log_neg_of_lt_zero (h0 : x < 0) (h1 : -1 < x) : log x < 0 := by
  rw [← neg_neg x]; rw [log_neg_eq_log]
  have h0' : 0 < -x := by linarith
  have h1' : -x < 1 := by linarith
  exact log_neg h0' h1'

/--
theorem `log_nonneg_iff` / 定理 `log_nonneg_iff`

English:
theorem log_nonneg_iff
  given: (hx : 0 < x)
  statement: 0 <= log x ↔ 1 <= x
  proof: by rw [← not_lt, log_neg_iff hx, not_lt]

@[bound]

中文:
定理 log_nonneg_iff
  条件: (hx : 0 < x)
  结论: 0 <= log x ↔ 1 <= x
  证明: by rw [← not_lt, log_neg_iff hx, not_lt]

@[bound]

Depends on / 依赖: log_neg_iff, not_lt
-/
theorem log_nonneg_iff (hx : 0 < x) : 0 <= log x ↔ 1 <= x := by rw [← not_lt, log_neg_iff hx, not_lt]

@[bound]
/--
theorem `log_nonneg` / 定理 `log_nonneg`

English:
theorem log_nonneg
  given: (hx : 1 <= x)
  statement: 0 <= log x
  proof: (log_nonneg_iff (zero_lt_one.trans_le hx)).2 hx

中文:
定理 log_nonneg
  条件: (hx : 1 <= x)
  结论: 0 <= log x
  证明: (log_nonneg_iff (zero_lt_one.trans_le hx)).2 hx

Depends on / 依赖: log_nonneg_iff, trans_le, zero_lt_one, zero_lt_one.trans_le
-/
theorem log_nonneg (hx : 1 <= x) : 0 <= log x :=
  (log_nonneg_iff (zero_lt_one.trans_le hx)).2 hx

/--
theorem `log_nonpos_iff` / 定理 `log_nonpos_iff`

English:
theorem log_nonpos_iff
  given: (hx : 0 <= x)
  statement: log x <= 0 ↔ x <= 1
  proof: by
  rcases hx.eq_or_lt with (rfl | hx)
  · simp [zero_le_one]
  rw [← not_lt]; rw [log_pos_iff hx.le]; rw [not_lt]

@[bound]

中文:
定理 log_nonpos_iff
  条件: (hx : 0 <= x)
  结论: log x <= 0 ↔ x <= 1
  证明: by
  rcases hx.eq_or_lt with (rfl | hx)
  · simp [zero_le_one]
  rw [← not_lt]; rw [log_pos_iff hx.le]; rw [not_lt]

@[bound]

Depends on / 依赖: eq_or_lt, hx.eq_or_lt, hx.le, log_pos_iff, not_lt, zero_le_one
-/
theorem log_nonpos_iff (hx : 0 <= x) : log x <= 0 ↔ x <= 1 := by
  rcases hx.eq_or_lt with (rfl | hx)
  · simp [zero_le_one]
  rw [← not_lt]; rw [log_pos_iff hx.le]; rw [not_lt]

@[bound]
/--
theorem `log_nonpos` / 定理 `log_nonpos`

English:
theorem log_nonpos
  given: (hx : 0 <= x) (h'x : x <= 1)
  statement: log x <= 0
  proof: (log_nonpos_iff hx).2 h'x

中文:
定理 log_nonpos
  条件: (hx : 0 <= x) (h'x : x <= 1)
  结论: log x <= 0
  证明: (log_nonpos_iff hx).2 h'x

Depends on / 依赖: log_nonpos_iff
-/
theorem log_nonpos (hx : 0 <= x) (h'x : x <= 1) : log x <= 0 :=
  (log_nonpos_iff hx).2 h'x

/--
theorem `log_natCast_nonneg` / 定理 `log_natCast_nonneg`

English:
theorem log_natCast_nonneg
  given: (n : Nat)
  statement: 0 <= log n
  proof: by
  if hn : n = 0 then
    simp [hn]
  else
have : (1 : Real) <= n := mod_cast Nat.one_le_of_lt Nat.pos_of_ne_zero hn
    exact log_nonneg this

中文:
定理 log_natCast_nonneg
  条件: (n : 自然数)
  结论: 0 <= log n
  证明: by
  if hn : n = 0 then
    simp [hn]
  else
have : (1 : Real) <= n := mod_cast Nat.one_le_of_lt Nat.pos_of_ne_zero hn
    exact log_nonneg this

Depends on / 依赖: Nat.one_le_of_lt, Nat.pos_of_ne_zero, log_nonneg, mod_cast, one_le_of_lt, pos_of_ne_zero
-/
theorem log_natCast_nonneg (n : Nat) : 0 <= log n := by
  if hn : n = 0 then
    simp [hn]
  else
have : (1 : Real) <= n := mod_cast Nat.one_le_of_lt Nat.pos_of_ne_zero hn
    exact log_nonneg this

/--
theorem `log_neg_natCast_nonneg` / 定理 `log_neg_natCast_nonneg`

English:
theorem log_neg_natCast_nonneg
  given: (n : Nat)
  statement: 0 <= log (-n)
  proof: by
  rw [← log_neg_eq_log]; rw [neg_neg]
  exact log_natCast_nonneg _

中文:
定理 log_neg_natCast_nonneg
  条件: (n : 自然数)
  结论: 0 <= log (-n)
  证明: by
  rw [← log_neg_eq_log]; rw [neg_neg]
  exact log_natCast_nonneg _

Depends on / 依赖: log_natCast_nonneg, log_neg_eq_log, neg_neg
-/
theorem log_neg_natCast_nonneg (n : Nat) : 0 <= log (-n) := by
  rw [← log_neg_eq_log]; rw [neg_neg]
  exact log_natCast_nonneg _

/--
theorem `log_intCast_nonneg` / 定理 `log_intCast_nonneg`

English:
theorem log_intCast_nonneg
  given: (n : Int)
  statement: 0 <= log n
  proof: by
  cases lt_trichotomy 0 n with
  | inl hn =>
      have : (1 : Real) <= n := mod_cast hn
      exact log_nonneg this
  | inr hn =>
      cases hn with
      | inl hn => simp [hn.symm]
      | inr hn =>
          have : (1 : Real) <= -n := by rw [← neg_zero, ← lt_neg] at hn; exact mod_cast hn
          rw [← log_neg_eq_log]
          exact log_nonneg this

中文:
定理 log_intCast_nonneg
  条件: (n : 整数)
  结论: 0 <= log n
  证明: by
  cases lt_trichotomy 0 n with
  | inl hn =>
      have : (1 : Real) <= n := mod_cast hn
      exact log_nonneg this
  | inr hn =>
      cases hn with
      | inl hn => simp [hn.symm]
      | inr hn =>
          have : (1 : Real) <= -n := by rw [← neg_zero, ← lt_neg] at hn; exact mod_cast hn
          rw [← log_neg_eq_log]
          exact log_nonneg this

Depends on / 依赖: backward, backward.isDefEq.respectTransparency.types, comp_assoc, hn.symm, isDefEq, log_neg_eq_log, log_nonneg, lt_neg, lt_trichotomy, mod_cast, neg_zero, normalizeAux, respectTransparency, set_option
-/
theorem log_intCast_nonneg (n : Int) : 0 <= log n := by
  cases lt_trichotomy 0 n with
  | inl hn =>
      have : (1 : Real) <= n := mod_cast hn
      exact log_nonneg this
  | inr hn =>
      cases hn with
      | inl hn => simp [hn.symm]
      | inr hn =>
          have : (1 : Real) <= -n := by rw [← neg_zero, ← lt_neg] at hn; exact mod_cast hn
          rw [← log_neg_eq_log]
          exact log_nonneg this

/--
theorem `strictMonoOn_log` / 定理 `strictMonoOn_log`

English:
theorem strictMonoOn_log
  statement: StrictMonoOn log (Set.Ioi 0)
  proof: fun _ hx _ _ hxy => log_lt_log hx hxy

中文:
定理 strictMonoOn_log
  结论: StrictMonoOn log (集合.左开右无界区间 0)
  证明: fun _ hx _ _ hxy => log_lt_log hx hxy

Depends on / 依赖: log_lt_log
-/
theorem strictMonoOn_log : StrictMonoOn log (Set.Ioi 0) := fun _ hx _ _ hxy => log_lt_log hx hxy

/--
theorem `strictAntiOn_log` / 定理 `strictAntiOn_log`

English:
theorem strictAntiOn_log
  statement: StrictAntiOn log (Set.Iio 0)
  proof: by
  rintro x (hx : x < 0) y (hy : y < 0) hxy
  rw [← log_abs y]; rw [← log_abs x]
  refine log_lt_log (abs_pos.2 hy.ne) ?_
  rwa [abs_of_neg hy, abs_of_neg hx, neg_lt_neg_iff]

中文:
定理 strictAntiOn_log
  结论: StrictAntiOn log (集合.左无界右开区间 0)
  证明: by
  rintro x (hx : x < 0) y (hy : y < 0) hxy
  rw [← log_abs y]; rw [← log_abs x]
  refine log_lt_log (abs_pos.2 hy.ne) ?_
  rwa [abs_of_neg hy, abs_of_neg hx, neg_lt_neg_iff]

Depends on / 依赖: abs_of_neg, abs_pos, hy.ne, log_abs, log_lt_log, neg_lt_neg_iff
-/
theorem strictAntiOn_log : StrictAntiOn log (Set.Iio 0) := by
  rintro x (hx : x < 0) y (hy : y < 0) hxy
  rw [← log_abs y]; rw [← log_abs x]
  refine log_lt_log (abs_pos.2 hy.ne) ?_
  rwa [abs_of_neg hy, abs_of_neg hx, neg_lt_neg_iff]

/--
theorem `log_injOn_pos` / 定理 `log_injOn_pos`

English:
theorem log_injOn_pos
  statement: Set.InjOn log (Set.Ioi 0)
  proof: strictMonoOn_log.injOn

中文:
定理 log_injOn_pos
  结论: 集合.单射限制 log (集合.左开右无界区间 0)
  证明: strictMonoOn_log.injOn

Depends on / 依赖: strictMonoOn_log, strictMonoOn_log.injOn
-/
theorem log_injOn_pos : Set.InjOn log (Set.Ioi 0) :=
  strictMonoOn_log.injOn

/--
theorem `log_lt_sub_one_of_pos` / 定理 `log_lt_sub_one_of_pos`

English:
theorem log_lt_sub_one_of_pos
  given: (hx1 : 0 < x) (hx2 : x != 1)
  statement: log x < x - 1
  proof: by
  have h : log x != 0 := by
    rwa [← log_one, log_injOn_pos.ne_iff hx1]
    exact mem_Ioi.mpr zero_lt_one
  linarith [add_one_lt_exp h, exp_log hx1]

中文:
定理 log_lt_sub_one_of_pos
  条件: (hx1 : 0 < x) (hx2 : x != 1)
  结论: log x < x - 1
  证明: by
  have h : log x != 0 := by
    rwa [← log_one, log_injOn_pos.ne_iff hx1]
    exact mem_Ioi.mpr zero_lt_one
  linarith [add_one_lt_exp h, exp_log hx1]

Depends on / 依赖: add_one_lt_exp, exp_log, log_injOn_pos, log_injOn_pos.ne_iff, log_one, mem_Ioi, mem_Ioi.mpr, ne_iff, zero_lt_one
-/
theorem log_lt_sub_one_of_pos (hx1 : 0 < x) (hx2 : x != 1) : log x < x - 1 := by
  have h : log x != 0 := by
    rwa [← log_one, log_injOn_pos.ne_iff hx1]
    exact mem_Ioi.mpr zero_lt_one
  linarith [add_one_lt_exp h, exp_log hx1]

/--
theorem `eq_one_of_pos_of_log_eq_zero` / 定理 `eq_one_of_pos_of_log_eq_zero`

English:
theorem eq_one_of_pos_of_log_eq_zero
  given: {x : Real} (h₁ : 0 < x) (h₂ : log x = 0)
  statement: x = 1
  proof: log_injOn_pos (Set.mem_Ioi.2 h₁) (Set.mem_Ioi.2 zero_lt_one) (h₂.trans Real.log_one.symm)

中文:
定理 eq_one_of_pos_of_log_eq_zero
  条件: {x : 实数} (h₁ : 0 < x) (h₂ : log x = 0)
  结论: x = 1
  证明: log_injOn_pos (Set.mem_Ioi.2 h₁) (Set.mem_Ioi.2 zero_lt_one) (h₂.trans Real.log_one.symm)

Depends on / 依赖: Real.log_one.symm, Set.mem_Ioi, log_injOn_pos, log_one, mem_Ioi, zero_lt_one
-/
theorem eq_one_of_pos_of_log_eq_zero {x : Real} (h₁ : 0 < x) (h₂ : log x = 0) : x = 1 :=
  log_injOn_pos (Set.mem_Ioi.2 h₁) (Set.mem_Ioi.2 zero_lt_one) (h₂.trans Real.log_one.symm)

/--
theorem `log_ne_zero_of_pos_of_ne_one` / 定理 `log_ne_zero_of_pos_of_ne_one`

English:
theorem log_ne_zero_of_pos_of_ne_one
  given: {x : Real} (hx_pos : 0 < x) (hx : x != 1)
  statement: log x != 0
  proof: mt (eq_one_of_pos_of_log_eq_zero hx_pos) hx

@[simp]

中文:
定理 log_ne_zero_of_pos_of_ne_one
  条件: {x : 实数} (hx_pos : 0 < x) (hx : x != 1)
  结论: log x != 0
  证明: mt (eq_one_of_pos_of_log_eq_zero hx_pos) hx

@[simp]

Depends on / 依赖: eq_one_of_pos_of_log_eq_zero, hx_pos
-/
theorem log_ne_zero_of_pos_of_ne_one {x : Real} (hx_pos : 0 < x) (hx : x != 1) : log x != 0 :=
  mt (eq_one_of_pos_of_log_eq_zero hx_pos) hx

@[simp]
/--
theorem `log_eq_zero` / 定理 `log_eq_zero`

English:
theorem log_eq_zero
  given: {x : Real}
  statement: log x = 0 ↔ x = 0 ∨ x = 1 ∨ x = -1
  proof: by
  constructor
  · intro h
    rcases lt_trichotomy x 0 with (x_lt_zero | rfl | x_gt_zero)
    · refine Or.inr (Or.inr (neg_eq_iff_eq_neg.mp ?_))
      rw [← log_neg_eq_log x] at h
      exact eq_one_of_pos_of_log_eq_zero (neg_pos.mpr x_lt_zero) h
    · exact Or.inl rfl
    · exact Or.inr (Or.inl (eq_one_of_pos_of_log_eq_zero x_gt_zero h))
  · rintro (rfl | rfl | rfl) <;> simp only [log_one, log_zero, log_neg_eq_log]

中文:
定理 log_eq_zero
  条件: {x : 实数}
  结论: log x = 0 ↔ x = 0 ∨ x = 1 ∨ x = -1
  证明: by
  constructor
  · intro h
    rcases lt_trichotomy x 0 with (x_lt_zero | rfl | x_gt_zero)
    · refine Or.inr (Or.inr (neg_eq_iff_eq_neg.mp ?_))
      rw [← log_neg_eq_log x] at h
      exact eq_one_of_pos_of_log_eq_zero (neg_pos.mpr x_lt_zero) h
    · exact Or.inl rfl
    · exact Or.inr (Or.inl (eq_one_of_pos_of_log_eq_zero x_gt_zero h))
  · rintro (rfl | rfl | rfl) <;> simp only [log_one, log_zero, log_neg_eq_log]

Depends on / 依赖: Or.inl, Or.inr, eq_one_of_pos_of_log_eq_zero, log_neg_eq_log, log_one, log_zero, lt_trichotomy, neg_eq_iff_eq_neg, neg_eq_iff_eq_neg.mp, neg_pos, neg_pos.mpr, x_gt_zero, x_lt_zero
-/
theorem log_eq_zero {x : Real} : log x = 0 ↔ x = 0 ∨ x = 1 ∨ x = -1 := by
  constructor
  · intro h
    rcases lt_trichotomy x 0 with (x_lt_zero | rfl | x_gt_zero)
    · refine Or.inr (Or.inr (neg_eq_iff_eq_neg.mp ?_))
      rw [← log_neg_eq_log x] at h
      exact eq_one_of_pos_of_log_eq_zero (neg_pos.mpr x_lt_zero) h
    · exact Or.inl rfl
    · exact Or.inr (Or.inl (eq_one_of_pos_of_log_eq_zero x_gt_zero h))
  · rintro (rfl | rfl | rfl) <;> simp only [log_one, log_zero, log_neg_eq_log]

/--
theorem `log_ne_zero` / 定理 `log_ne_zero`

English:
theorem log_ne_zero
  given: {x : Real}
  statement: log x != 0 ↔ x != 0 ∧ x != 1 ∧ x != -1
  proof: by
  simpa only [not_or] using log_eq_zero.not

@[simp, push]

中文:
定理 log_ne_zero
  条件: {x : 实数}
  结论: log x != 0 ↔ x != 0 ∧ x != 1 ∧ x != -1
  证明: by
  simpa only [not_or] using log_eq_zero.not

@[simp, push]

Depends on / 依赖: log_eq_zero, log_eq_zero.not, not_or
-/
theorem log_ne_zero {x : Real} : log x != 0 ↔ x != 0 ∧ x != 1 ∧ x != -1 := by
  simpa only [not_or] using log_eq_zero.not

@[simp, push]
/--
theorem `log_pow` / 定理 `log_pow`

English:
theorem log_pow
  given: (x : Real) (n : Nat)
  statement: log (x ^ n) = n * log x
  proof: by
  induction n with
  | zero => simp
  | succ n ih =>
    rcases eq_or_ne x 0 with (rfl | hx)
    · simp
    · rw [pow_succ, log_mul (pow_ne_zero _ hx) hx, ih, Nat.cast_succ, add_mul, one_mul]

@[simp, push]

中文:
定理 log_pow
  条件: (x : 实数) (n : 自然数)
  结论: log (x ^ n) = n * log x
  证明: by
  induction n with
  | zero => simp
  | succ n ih =>
    rcases eq_or_ne x 0 with (rfl | hx)
    · simp
    · rw [pow_succ, log_mul (pow_ne_zero _ hx) hx, ih, Nat.cast_succ, add_mul, one_mul]

@[simp, push]

Depends on / 依赖: Nat.cast_succ, add_mul, cast_succ, eq_or_ne, log_mul, one_mul, pow_ne_zero, pow_succ
-/
theorem log_pow (x : Real) (n : Nat) : log (x ^ n) = n * log x := by
  induction n with
  | zero => simp
  | succ n ih =>
    rcases eq_or_ne x 0 with (rfl | hx)
    · simp
    · rw [pow_succ, log_mul (pow_ne_zero _ hx) hx, ih, Nat.cast_succ, add_mul, one_mul]

@[simp, push]
/--
theorem `log_zpow` / 定理 `log_zpow`

English:
theorem log_zpow
  given: (x : Real) (n : Int)
  statement: log (x ^ n) = n * log x
  proof: by
  cases n
  · rw [Int.ofNat_eq_natCast, zpow_natCast, log_pow, Int.cast_natCast]
  · rw [zpow_negSucc, log_inv, log_pow, Int.cast_negSucc, Nat.cast_add_one, neg_mul_eq_neg_mul]

@[push]

中文:
定理 log_zpow
  条件: (x : 实数) (n : 整数)
  结论: log (x ^ n) = n * log x
  证明: by
  cases n
  · rw [Int.ofNat_eq_natCast, zpow_natCast, log_pow, Int.cast_natCast]
  · rw [zpow_negSucc, log_inv, log_pow, Int.cast_negSucc, Nat.cast_add_one, neg_mul_eq_neg_mul]

@[push]

Depends on / 依赖: Category, Int.cast_natCast, Int.cast_negSucc, Int.ofNat_eq_natCast, Nat.cast_add_one, cast_add_one, cast_natCast, cast_negSucc, log_inv, log_pow, neg_mul_eq_neg_mul, ofNat_eq_natCast, zpow_natCast, zpow_negSucc
-/
theorem log_zpow (x : Real) (n : Int) : log (x ^ n) = n * log x := by
  cases n
  · rw [Int.ofNat_eq_natCast, zpow_natCast, log_pow, Int.cast_natCast]
  · rw [zpow_negSucc, log_inv, log_pow, Int.cast_negSucc, Nat.cast_add_one, neg_mul_eq_neg_mul]

@[push]
/--
theorem `log_sqrt` / 定理 `log_sqrt`

English:
theorem log_sqrt
  given: {x : Real} (hx : 0 <= x)
  statement: log (√x) = log x / 2
  proof: by
  rw [eq_div_iff]; rw [mul_comm]; rw [← Nat.cast_two]; rw [← log_pow]; rw [sq_sqrt hx]
  exact two_ne_zero

中文:
定理 log_sqrt
  条件: {x : 实数} (hx : 0 <= x)
  结论: log (√x) = log x / 2
  证明: by
  rw [eq_div_iff]; rw [mul_comm]; rw [← Nat.cast_two]; rw [← log_pow]; rw [sq_sqrt hx]
  exact two_ne_zero

Depends on / 依赖: Nat.cast_two, cast_two, eq_div_iff, log_pow, mul_comm, sq_sqrt, two_ne_zero
-/
theorem log_sqrt {x : Real} (hx : 0 <= x) : log (√x) = log x / 2 := by
  rw [eq_div_iff]; rw [mul_comm]; rw [← Nat.cast_two]; rw [← log_pow]; rw [sq_sqrt hx]
  exact two_ne_zero

/--
theorem `log_le_sub_one_of_pos` / 定理 `log_le_sub_one_of_pos`

English:
theorem log_le_sub_one_of_pos
  given: {x : Real} (hx : 0 < x)
  statement: log x <= x - 1
  proof: by
  rw [le_sub_iff_add_le]
  convert! add_one_le_exp (log x)
  rw [exp_log hx]

中文:
定理 log_le_sub_one_of_pos
  条件: {x : 实数} (hx : 0 < x)
  结论: log x <= x - 1
  证明: by
  rw [le_sub_iff_add_le]
  convert! add_one_le_exp (log x)
  rw [exp_log hx]

Depends on / 依赖: add_one_le_exp, convert, exp_log, le_sub_iff_add_le
-/
theorem log_le_sub_one_of_pos {x : Real} (hx : 0 < x) : log x <= x - 1 := by
  rw [le_sub_iff_add_le]
  convert! add_one_le_exp (log x)
  rw [exp_log hx]

/--
lemma `one_sub_inv_le_log_of_pos` / 引理 `one_sub_inv_le_log_of_pos`

English:
lemma one_sub_inv_le_log_of_pos
  given: (hx : 0 < x)
  statement: 1 - x⁻¹ <= log x
  proof: by
  simpa [add_comm] using log_le_sub_one_of_pos (inv_pos.2 hx)

中文:
引理 one_sub_inv_le_log_of_pos
  条件: (hx : 0 < x)
  结论: 1 - x⁻¹ <= log x
  证明: by
  simpa [add_comm] using log_le_sub_one_of_pos (inv_pos.2 hx)

Depends on / 依赖: add_comm, inv_pos, log_le_sub_one_of_pos
-/
lemma one_sub_inv_le_log_of_pos (hx : 0 < x) : 1 - x⁻¹ <= log x := by
  simpa [add_comm] using log_le_sub_one_of_pos (inv_pos.2 hx)

/--
lemma `log_le_self` / 引理 `log_le_self`

English:
lemma log_le_self
  given: (hx : 0 <= x)
  statement: log x <= x
  proof: by
  obtain rfl | hx := hx.eq_or_lt
  · simp
  · exact (log_le_sub_one_of_pos hx).trans (by linarith)

中文:
引理 log_le_self
  条件: (hx : 0 <= x)
  结论: log x <= x
  证明: by
  obtain rfl | hx := hx.eq_or_lt
  · simp
  · exact (log_le_sub_one_of_pos hx).trans (by linarith)

Depends on / 依赖: eq_or_lt, hx.eq_or_lt, log_le_sub_one_of_pos
-/
lemma log_le_self (hx : 0 <= x) : log x <= x := by
  obtain rfl | hx := hx.eq_or_lt
  · simp
  · exact (log_le_sub_one_of_pos hx).trans (by linarith)

/--
lemma `neg_inv_le_log` / 引理 `neg_inv_le_log`

English:
lemma neg_inv_le_log
  given: (hx : 0 <= x)
  statement: -x⁻¹ <= log x
  proof: by
rw [neg_le]; rw [← log_inv]; exact log_le_self inv_nonneg.2 hx

中文:
引理 neg_inv_le_log
  条件: (hx : 0 <= x)
  结论: -x⁻¹ <= log x
  证明: by
rw [neg_le]; rw [← log_inv]; exact log_le_self inv_nonneg.2 hx

Depends on / 依赖: inv_nonneg, log_inv, log_le_self, neg_le
-/
lemma neg_inv_le_log (hx : 0 <= x) : -x⁻¹ <= log x := by
rw [neg_le]; rw [← log_inv]; exact log_le_self inv_nonneg.2 hx

/--
theorem `abs_log_mul_self_lt` / 定理 `abs_log_mul_self_lt`

English:
theorem abs_log_mul_self_lt
  given: (x : Real) (h1 : 0 < x) (h2 : x <= 1)
  statement: |log x * x| < 1
  proof: by
  have : 0 < 1 / x := by simpa only [one_div, inv_pos] using h1
  replace := log_le_sub_one_of_pos this
  replace : log (1 / x) < 1 / x := by linarith
  rw [log_div one_ne_zero h1.ne']; rw [log_one]; rw [zero_sub]; rw [lt_div_iff₀ h1] at this
  have aux : 0 <= -log x * x := by
    refine mul_nonneg ?_ h1.le
    rw [← log_inv]
    apply log_nonneg
    rw [← le_inv_comm₀ h1 zero_lt_one]; rw [inv_one]
    exact h2
  rw [← abs_of_nonneg aux]; rw [neg_mul]; rw [abs_neg] at this
  exact this

中文:
定理 abs_log_mul_self_lt
  条件: (x : 实数) (h1 : 0 < x) (h2 : x <= 1)
  结论: |log x * x| < 1
  证明: by
  have : 0 < 1 / x := by simpa only [one_div, inv_pos] using h1
  replace := log_le_sub_one_of_pos this
  replace : log (1 / x) < 1 / x := by linarith
  rw [log_div one_ne_zero h1.ne']; rw [log_one]; rw [zero_sub]; rw [lt_div_iff₀ h1] at this
  have aux : 0 <= -log x * x := by
    refine mul_nonneg ?_ h1.le
    rw [← log_inv]
    apply log_nonneg
    rw [← le_inv_comm₀ h1 zero_lt_one]; rw [inv_one]
    exact h2
  rw [← abs_of_nonneg aux]; rw [neg_mul]; rw [abs_neg] at this
  exact this

Depends on / 依赖: abs_neg, abs_of_nonneg, h1.le, h1.ne, inv_one, inv_pos, log_div, log_inv, log_le_sub_one_of_pos, log_nonneg, log_one, mul_nonneg, neg_mul, one_div, one_ne_zero, replace, zero_lt_one, zero_sub
-/
theorem abs_log_mul_self_lt (x : Real) (h1 : 0 < x) (h2 : x <= 1) : |log x * x| < 1 := by
  have : 0 < 1 / x := by simpa only [one_div, inv_pos] using h1
  replace := log_le_sub_one_of_pos this
  replace : log (1 / x) < 1 / x := by linarith
  rw [log_div one_ne_zero h1.ne']; rw [log_one]; rw [zero_sub]; rw [lt_div_iff₀ h1] at this
  have aux : 0 <= -log x * x := by
    refine mul_nonneg ?_ h1.le
    rw [← log_inv]
    apply log_nonneg
    rw [← le_inv_comm₀ h1 zero_lt_one]; rw [inv_one]
    exact h2
  rw [← abs_of_nonneg aux]; rw [neg_mul]; rw [abs_neg] at this
  exact this

/--
lemma `le_log_one_add_of_nonneg` / 引理 `le_log_one_add_of_nonneg`

English:
lemma le_log_one_add_of_nonneg
  given: {x : Real} (hx : 0 <= x)
  statement: 2 * x / (x + 2) <= log (1 + x)
  proof: by
  rw [le_log_iff_exp_le (by grind)]
  convert exp_le_two_add_div_two_sub (x := 2 * x / (x + 2)) (by positivity) _ using 1
  all_goals field_simp; grind

中文:
引理 le_log_one_add_of_nonneg
  条件: {x : 实数} (hx : 0 <= x)
  结论: 2 * x / (x + 2) <= log (1 + x)
  证明: by
  rw [le_log_iff_exp_le (by grind)]
  convert exp_le_two_add_div_two_sub (x := 2 * x / (x + 2)) (by positivity) _ using 1
  all_goals field_simp; grind

Depends on / 依赖: all_goals, convert, exp_le_two_add_div_two_sub, le_log_iff_exp_le
-/
lemma le_log_one_add_of_nonneg {x : Real} (hx : 0 <= x) : 2 * x / (x + 2) <= log (1 + x) := by
  rw [le_log_iff_exp_le (by grind)]
  convert exp_le_two_add_div_two_sub (x := 2 * x / (x + 2)) (by positivity) _ using 1
  all_goals field_simp; grind

/--
lemma `lt_log_one_add_of_pos` / 引理 `lt_log_one_add_of_pos`

English:
lemma lt_log_one_add_of_pos
  given: {x : Real} (hx : 0 < x)
  statement: 2 * x / (x + 2) < log (1 + x)
  proof: by
  rw [lt_log_iff_exp_lt (by grind)]
  convert exp_lt_two_add_div_two_sub (x := 2 * x / (x + 2)) (by positivity) _ using 1
  all_goals field_simp; grind

中文:
引理 lt_log_one_add_of_pos
  条件: {x : 实数} (hx : 0 < x)
  结论: 2 * x / (x + 2) < log (1 + x)
  证明: by
  rw [lt_log_iff_exp_lt (by grind)]
  convert exp_lt_two_add_div_two_sub (x := 2 * x / (x + 2)) (by positivity) _ using 1
  all_goals field_simp; grind

Depends on / 依赖: all_goals, convert, exp_lt_two_add_div_two_sub, lt_log_iff_exp_lt
-/
lemma lt_log_one_add_of_pos {x : Real} (hx : 0 < x) : 2 * x / (x + 2) < log (1 + x) := by
  rw [lt_log_iff_exp_lt (by grind)]
  convert exp_lt_two_add_div_two_sub (x := 2 * x / (x + 2)) (by positivity) _ using 1
  all_goals field_simp; grind

/--
theorem `tendsto_log_atTop` / 定理 `tendsto_log_atTop`

English:
theorem tendsto_log_atTop
  statement: Tendsto log atTop atTop
  proof: tendsto_comp_exp_atTop.1 by simpa only [log_exp] using! tendsto_id

中文:
定理 tendsto_log_atTop
  结论: 收敛 log atTop atTop
  证明: tendsto_comp_exp_atTop.1 by simpa only [log_exp] using! tendsto_id

Depends on / 依赖: log_exp, tendsto_comp_exp_atTop, tendsto_id
-/
theorem tendsto_log_atTop : Tendsto log atTop atTop :=
tendsto_comp_exp_atTop.1 by simpa only [log_exp] using! tendsto_id

/--
lemma `tendsto_log_nhdsGT_zero` / 引理 `tendsto_log_nhdsGT_zero`

English:
lemma tendsto_log_nhdsGT_zero
  statement: Tendsto log (𝓝[>] 0) atBot
  proof: by
  simpa [← tendsto_comp_exp_atBot] using! tendsto_id

中文:
引理 tendsto_log_nhdsGT_zero
  结论: 收敛 log (𝓝[>] 0) atBot
  证明: by
  simpa [← tendsto_comp_exp_atBot] using! tendsto_id

Depends on / 依赖: tendsto_comp_exp_atBot, tendsto_id
-/
lemma tendsto_log_nhdsGT_zero : Tendsto log (𝓝[>] 0) atBot := by
  simpa [← tendsto_comp_exp_atBot] using! tendsto_id

/--
theorem `tendsto_log_nhdsNE_zero` / 定理 `tendsto_log_nhdsNE_zero`

English:
theorem tendsto_log_nhdsNE_zero
  statement: Tendsto log (𝓝[!=] 0) atBot
  proof: by
  simpa [comp_def] using tendsto_log_nhdsGT_zero.comp tendsto_abs_nhdsNE_zero

中文:
定理 tendsto_log_nhdsNE_zero
  结论: 收敛 log (𝓝[!=] 0) atBot
  证明: by
  simpa [comp_def] using tendsto_log_nhdsGT_zero.comp tendsto_abs_nhdsNE_zero

Depends on / 依赖: comp_def, tendsto_abs_nhdsNE_zero, tendsto_log_nhdsGT_zero, tendsto_log_nhdsGT_zero.comp
-/
theorem tendsto_log_nhdsNE_zero : Tendsto log (𝓝[!=] 0) atBot := by
  simpa [comp_def] using tendsto_log_nhdsGT_zero.comp tendsto_abs_nhdsNE_zero

/--
lemma `tendsto_log_nhdsLT_zero` / 引理 `tendsto_log_nhdsLT_zero`

English:
lemma tendsto_log_nhdsLT_zero
  statement: Tendsto log (𝓝[<] 0) atBot
  proof: tendsto_log_nhdsNE_zero.mono_left nhdsWithin_mono _ fun _ h => ne_of_lt h

中文:
引理 tendsto_log_nhdsLT_zero
  结论: 收敛 log (𝓝[<] 0) atBot
  证明: tendsto_log_nhdsNE_zero.mono_left nhdsWithin_mono _ fun _ h => ne_of_lt h

Depends on / 依赖: mono_left, ne_of_lt, nhdsWithin_mono, tendsto_log_nhdsNE_zero, tendsto_log_nhdsNE_zero.mono_left
-/
lemma tendsto_log_nhdsLT_zero : Tendsto log (𝓝[<] 0) atBot :=
tendsto_log_nhdsNE_zero.mono_left nhdsWithin_mono _ fun _ h => ne_of_lt h

/--
theorem `continuousOn_log` / 定理 `continuousOn_log`

English:
theorem continuousOn_log
  statement: ContinuousOn log {0}ᶜ
  proof: by
  simp +unfoldPartialApp only [continuousOn_iff_continuous_domRestrict,
    domRestrict]
  conv in log _ => rw [log_of_ne_zero (show (x : Real) != 0 from x.2)]
  exact expOrderIso.symm.continuous.comp (continuous_subtype_val.norm.subtype_mk _)

中文:
定理 continuousOn_log
  结论: ContinuousOn log {0}ᶜ
  证明: by
  simp +unfoldPartialApp only [continuousOn_iff_continuous_domRestrict,
    domRestrict]
  conv in log _ => rw [log_of_ne_zero (show (x : Real) != 0 from x.2)]
  exact expOrderIso.symm.continuous.comp (continuous_subtype_val.norm.subtype_mk _)

Depends on / 依赖: continuous, continuousOn_iff_continuous_domRestrict, continuous_subtype_val, continuous_subtype_val.norm.subtype_mk, domRestrict, expOrderIso, expOrderIso.symm.continuous.comp, log_of_ne_zero, subtype_mk, unfoldPartialApp
-/
theorem continuousOn_log : ContinuousOn log {0}ᶜ := by
  simp +unfoldPartialApp only [continuousOn_iff_continuous_domRestrict,
    domRestrict]
  conv in log _ => rw [log_of_ne_zero (show (x : Real) != 0 from x.2)]
  exact expOrderIso.symm.continuous.comp (continuous_subtype_val.norm.subtype_mk _)

/-- The real logarithm is continuous as a function from nonzero reals. -/
@[fun_prop]
/--
theorem `continuous_log` / 定理 `continuous_log`

English:
theorem continuous_log
  statement: Continuous fun x : { x : Real // x != 0 } => log x
  proof: continuousOn_iff_continuous_domRestrict.1 continuousOn_log.mono fun _ => id

中文:
定理 continuous_log
  结论: 连续 fun x : { x : 实数 // x != 0 } => log x
  证明: continuousOn_iff_continuous_domRestrict.1 continuousOn_log.mono fun _ => id

Depends on / 依赖: continuousOn_iff_continuous_domRestrict, continuousOn_log, continuousOn_log.mono
-/
theorem continuous_log : Continuous fun x : { x : Real // x != 0 } => log x :=
continuousOn_iff_continuous_domRestrict.1 continuousOn_log.mono fun _ => id

/-- The real logarithm is continuous as a function from positive reals. -/
@[fun_prop]
/--
theorem `continuous_log'` / 定理 `continuous_log'`

English:
theorem continuous_log'
  statement: Continuous fun x : { x : Real // 0 < x } => log x
  proof: continuousOn_iff_continuous_domRestrict.1 continuousOn_log.mono fun _ hx => ne_of_gt hx

中文:
定理 continuous_log'
  结论: 连续 fun x : { x : 实数 // 0 < x } => log x
  证明: continuousOn_iff_continuous_domRestrict.1 continuousOn_log.mono fun _ hx => ne_of_gt hx

Depends on / 依赖: continuousOn_iff_continuous_domRestrict, continuousOn_log, continuousOn_log.mono, ne_of_gt
-/
theorem continuous_log' : Continuous fun x : { x : Real // 0 < x } => log x :=
continuousOn_iff_continuous_domRestrict.1 continuousOn_log.mono fun _ hx => ne_of_gt hx

/--
theorem `continuousAt_log` / 定理 `continuousAt_log`

English:
theorem continuousAt_log
  given: (hx : x != 0)
  statement: ContinuousAt log x
  proof: (continuousOn_log x hx).continuousAt isOpen_compl_singleton.mem_nhds hx

@[simp]

中文:
定理 continuousAt_log
  条件: (hx : x != 0)
  结论: ContinuousAt log x
  证明: (continuousOn_log x hx).continuousAt isOpen_compl_singleton.mem_nhds hx

@[simp]

Depends on / 依赖: continuousAt, continuousOn_log, isOpen_compl_singleton, isOpen_compl_singleton.mem_nhds, mem_nhds
-/
theorem continuousAt_log (hx : x != 0) : ContinuousAt log x :=
(continuousOn_log x hx).continuousAt isOpen_compl_singleton.mem_nhds hx

@[simp]
/--
theorem `continuousAt_log_iff` / 定理 `continuousAt_log_iff`

English:
theorem continuousAt_log_iff
  statement: ContinuousAt log x ↔ x != 0
  proof: by
  refine ⟨?_, continuousAt_log⟩
  rintro h rfl
exact not_tendsto_nhds_of_tendsto_atBot tendsto_log_nhdsNE_zero _
    h.tendsto.mono_left nhdsWithin_le_nhds

中文:
定理 continuousAt_log_iff
  结论: ContinuousAt log x ↔ x != 0
  证明: by
  refine ⟨?_, continuousAt_log⟩
  rintro h rfl
exact not_tendsto_nhds_of_tendsto_atBot tendsto_log_nhdsNE_zero _
    h.tendsto.mono_left nhdsWithin_le_nhds

Depends on / 依赖: continuousAt_log, h.tendsto.mono_left, mono_left, nhdsWithin_le_nhds, not_tendsto_nhds_of_tendsto_atBot, tendsto, tendsto_log_nhdsNE_zero
-/
theorem continuousAt_log_iff : ContinuousAt log x ↔ x != 0 := by
  refine ⟨?_, continuousAt_log⟩
  rintro h rfl
exact not_tendsto_nhds_of_tendsto_atBot tendsto_log_nhdsNE_zero _
    h.tendsto.mono_left nhdsWithin_le_nhds

open List in
/--
lemma `log_list_prod` / 引理 `log_list_prod`

English:
lemma log_list_prod
  given: {l : List Real} (h : forall x in l, x != 0)
  proof: by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp_all only [ne_eq, mem_cons, or_true, not_false_eq_true, forall_const, forall_eq_or_imp,
      prod_cons, map_cons, sum_cons]
    have : l.prod != 0 := by grind [prod_ne_zero]
    rw [log_mul h.1 this]; rw [add_right_inj]; rw [ih]

中文:
引理 log_list_prod
  条件: {l : 列表 实数} (h : 对任意 x in l, x != 0)
  证明: by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp_all only [ne_eq, mem_cons, or_true, not_false_eq_true, forall_const, forall_eq_or_imp,
      prod_cons, map_cons, sum_cons]
    have : l.prod != 0 := by grind [prod_ne_zero]
    rw [log_mul h.1 this]; rw [add_right_inj]; rw [ih]

Depends on / 依赖: add_right_inj, forall_const, forall_eq_or_imp, l.prod, log_mul, map_cons, mem_cons, ne_eq, not_false_eq_true, or_true, prod_cons, prod_ne_zero, sum_cons
-/
lemma log_list_prod {l : List Real} (h : forall x in l, x != 0) :
    log l.prod = (l.map (fun x => log x)).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp_all only [ne_eq, mem_cons, or_true, not_false_eq_true, forall_const, forall_eq_or_imp,
      prod_cons, map_cons, sum_cons]
    have : l.prod != 0 := by grind [prod_ne_zero]
    rw [log_mul h.1 this]; rw [add_right_inj]; rw [ih]

open Multiset in
/--
lemma `log_multiset_prod` / 引理 `log_multiset_prod`

English:
lemma log_multiset_prod
  given: {s : Multiset Real} (h : forall x in s, x != 0)
  proof: by
  rw [← prod_toList]; rw [log_list_prod (by simp_all)]; rw [sum_map_toList]

中文:
引理 log_multiset_prod
  条件: {s : Multiset 实数} (h : 对任意 x in s, x != 0)
  证明: by
  rw [← prod_toList]; rw [log_list_prod (by simp_all)]; rw [sum_map_toList]

Depends on / 依赖: log_list_prod, prod_toList, sum_map_toList
-/
lemma log_multiset_prod {s : Multiset Real} (h : forall x in s, x != 0) :
    log s.prod = (s.map (fun x => log x)).sum := by
  rw [← prod_toList]; rw [log_list_prod (by simp_all)]; rw [sum_map_toList]

open Finset in
@[push]
/--
theorem `log_prod` / 定理 `log_prod`

English:
theorem log_prod
  given: {α : Type*} {s : Finset α} {f : α -> Real} (hf : forall x in s, f x != 0)
  proof: by
  rw [← prod_map_toList]; rw [log_list_prod (by simp_all)]
  simp

@[push]

中文:
定理 log_prod
  条件: {α : 类型} {s : 有限集 α} {f : α -> 实数} (hf : 对任意 x in s, f x != 0)
  证明: by
  rw [← prod_map_toList]; rw [log_list_prod (by simp_all)]
  simp

@[push]

Depends on / 依赖: log_list_prod, prod_map_toList
-/
theorem log_prod {α : Type*} {s : Finset α} {f : α -> Real} (hf : forall x in s, f x != 0) :
    log (∏ i in s, f i) = ∑ i in s, log (f i) := by
  rw [← prod_map_toList]; rw [log_list_prod (by simp_all)]
  simp

@[push]
/--
theorem `_root_.Finsupp.log_prod` / 定理 `_root_.Finsupp.log_prod`

English:
theorem _root_.Finsupp.log_prod
  statement: {α β : Type*} [Zero β] (f : α ->₀ β) (g : α -> β -> Real)
  proof: log_prod fun _x hx h₀ => Finsupp.mem_support_iff.1 hx hg _ h₀

中文:
定理 _root_.有限支撑.log_prod
  结论: {α β : 类型} [零 β] (f : α ->₀ β) (g : α -> β -> 实数)
  证明: log_prod fun _x hx h₀ => Finsupp.mem_support_iff.1 hx hg _ h₀
-/
protected theorem _root_.Finsupp.log_prod {α β : Type*} [Zero β] (f : α ->₀ β) (g : α -> β -> Real)
    (hg : forall a, g a (f a) = 0 -> f a = 0) : log (f.prod g) = f.sum fun a b => log (g a b) :=
log_prod fun _x hx h₀ => Finsupp.mem_support_iff.1 hx hg _ h₀

-- Note: This is wrong assuming only `f a ≠ 0` (as in `Real.log_prod`).
-- E.g., `f = (2, -1, -1, ...)` (with infinitely many `-1`s).
/--
lemma `log_finprod` / 引理 `log_finprod`

English:
lemma log_finprod
  given: {α : Type*} {f : α -> Real} (h : forall a, 0 < f a)
  proof: by
  classical
  have H : (fun i => log (f i)).support = f.mulSupport := by
    grind [mem_mulSupport, mem_support, log_eq_zero]
  have H' : HasFiniteMulSupport f ↔ HasFiniteSupport fun a => log (f a) := by
    simp [HasFiniteMulSupport, HasFiniteSupport, H]
  simp only [finprod_def, finsum_def]
  by_cases h' : HasFiniteMulSupport f
  · simp [h', log_prod (fun a _ => (h a).ne'), H'.mp h', H]
  · simp [h', mt H'.mpr h']

中文:
引理 log_finprod
  条件: {α : 类型} {f : α -> 实数} (h : 对任意 a, 0 < f a)
  证明: by
  classical
  have H : (fun i => log (f i)).support = f.mulSupport := by
    grind [mem_mulSupport, mem_support, log_eq_zero]
  have H' : HasFiniteMulSupport f ↔ HasFiniteSupport fun a => log (f a) := by
    simp [HasFiniteMulSupport, HasFiniteSupport, H]
  simp only [finprod_def, finsum_def]
  by_cases h' : HasFiniteMulSupport f
  · simp [h', log_prod (fun a _ => (h a).ne'), H'.mp h', H]
  · simp [h', mt H'.mpr h']

Depends on / 依赖: HasFiniteMulSupport, HasFiniteSupport, classical, f.mulSupport, finprod_def, finsum_def, log_eq_zero, log_prod, mem_mulSupport, mem_support, mulSupport, support
-/
lemma log_finprod {α : Type*} {f : α -> Real} (h : forall a, 0 < f a) :
    log (∏ᶠ a, f a) = ∑ᶠ a, log (f a) := by
  classical
  have H : (fun i => log (f i)).support = f.mulSupport := by
    grind [mem_mulSupport, mem_support, log_eq_zero]
  have H' : HasFiniteMulSupport f ↔ HasFiniteSupport fun a => log (f a) := by
    simp [HasFiniteMulSupport, HasFiniteSupport, H]
  simp only [finprod_def, finsum_def]
  by_cases h' : HasFiniteMulSupport f
  · simp [h', log_prod (fun a _ => (h a).ne'), H'.mp h', H]
  · simp [h', mt H'.mpr h']

/--
theorem `log_nat_eq_sum_factorization` / 定理 `log_nat_eq_sum_factorization`

English:
theorem log_nat_eq_sum_factorization
  given: (n : Nat)
  proof: by
  rcases eq_or_ne n 0 with (rfl | hn)
  · simp -- relies on junk values of `log` and `Nat.factorization`
  · simp only [← log_pow, ← Nat.cast_pow]
    rw [← Finsupp.log_prod]; rw [← Nat.cast_finsuppProd]; rw [Nat.prod_factorization_pow_eq_self hn]
    intro p hp
    rw [eq_zero_of_pow_eq_zero (Nat.cast_eq_zero.1 hp)]; rw [Nat.factorization_zero_right]

中文:
定理 log_nat_eq_sum_factorization
  条件: (n : 自然数)
  证明: by
  rcases eq_or_ne n 0 with (rfl | hn)
  · simp -- relies on junk values of `log` and `Nat.factorization`
  · simp only [← log_pow, ← Nat.cast_pow]
    rw [← Finsupp.log_prod]; rw [← Nat.cast_finsuppProd]; rw [Nat.prod_factorization_pow_eq_self hn]
    intro p hp
    rw [eq_zero_of_pow_eq_zero (Nat.cast_eq_zero.1 hp)]; rw [Nat.factorization_zero_right]

Depends on / 依赖: Finsupp, Finsupp.log_prod, Nat.cast_eq_zero, Nat.cast_finsuppProd, Nat.cast_pow, Nat.factorization, Nat.factorization_zero_right, Nat.prod_factorization_pow_eq_self, cast_eq_zero, cast_finsuppProd, cast_pow, eq_or_ne, eq_zero_of_pow_eq_zero, factorization, factorization_zero_right, log_pow, log_prod, prod_factorization_pow_eq_self, relies, values
-/
theorem log_nat_eq_sum_factorization (n : Nat) :
    log n = n.factorization.sum fun p t => t * log p := by
  rcases eq_or_ne n 0 with (rfl | hn)
  · simp -- relies on junk values of `log` and `Nat.factorization`
  · simp only [← log_pow, ← Nat.cast_pow]
    rw [← Finsupp.log_prod]; rw [← Nat.cast_finsuppProd]; rw [Nat.prod_factorization_pow_eq_self hn]
    intro p hp
    rw [eq_zero_of_pow_eq_zero (Nat.cast_eq_zero.1 hp)]; rw [Nat.factorization_zero_right]

/--
theorem `tendsto_pow_log_div_mul_add_atTop` / 定理 `tendsto_pow_log_div_mul_add_atTop`

English:
theorem tendsto_pow_log_div_mul_add_atTop
  given: (a b : Real) (n : Nat) (ha : a != 0)
  proof: ((tendsto_div_pow_mul_exp_add_atTop a b n ha.symm).comp tendsto_log_atTop).congr' by
    filter_upwards [eventually_gt_atTop (0 : Real)] with x hx using by simp [exp_log hx]

中文:
定理 tendsto_pow_log_div_mul_add_atTop
  条件: (a b : 实数) (n : 自然数) (ha : a != 0)
  证明: ((tendsto_div_pow_mul_exp_add_atTop a b n ha.symm).comp tendsto_log_atTop).congr' by
    filter_upwards [eventually_gt_atTop (0 : Real)] with x hx using by simp [exp_log hx]

Depends on / 依赖: eventually_gt_atTop, exp_log, filter_upwards, ha.symm, tendsto_div_pow_mul_exp_add_atTop, tendsto_log_atTop
-/
theorem tendsto_pow_log_div_mul_add_atTop (a b : Real) (n : Nat) (ha : a != 0) :
    Tendsto (fun x => log x ^ n / (a * x + b)) atTop (𝓝 0) :=
((tendsto_div_pow_mul_exp_add_atTop a b n ha.symm).comp tendsto_log_atTop).congr' by
    filter_upwards [eventually_gt_atTop (0 : Real)] with x hx using by simp [exp_log hx]

/--
theorem `isLittleO_pow_log_id_atTop` / 定理 `isLittleO_pow_log_id_atTop`

English:
theorem isLittleO_pow_log_id_atTop
  given: {n : Nat}
  statement: (fun x => log x ^ n) =o[atTop] id
  proof: by
  rw [Asymptotics.isLittleO_iff_tendsto']
  · simpa using tendsto_pow_log_div_mul_add_atTop 1 0 n one_ne_zero
  filter_upwards [eventually_ne_atTop (0 : Real)] with x h₁ h₂ using (h₁ h₂).elim

中文:
定理 isLittleO_pow_log_id_atTop
  条件: {n : 自然数}
  结论: (fun x => log x ^ n) =o[atTop] id
  证明: by
  rw [Asymptotics.isLittleO_iff_tendsto']
  · simpa using tendsto_pow_log_div_mul_add_atTop 1 0 n one_ne_zero
  filter_upwards [eventually_ne_atTop (0 : Real)] with x h₁ h₂ using (h₁ h₂).elim

Depends on / 依赖: Asymptotics, Asymptotics.isLittleO_iff_tendsto, eventually_ne_atTop, filter_upwards, isLittleO_iff_tendsto, one_ne_zero, tendsto_pow_log_div_mul_add_atTop
-/
theorem isLittleO_pow_log_id_atTop {n : Nat} : (fun x => log x ^ n) =o[atTop] id := by
  rw [Asymptotics.isLittleO_iff_tendsto']
  · simpa using tendsto_pow_log_div_mul_add_atTop 1 0 n one_ne_zero
  filter_upwards [eventually_ne_atTop (0 : Real)] with x h₁ h₂ using (h₁ h₂).elim

/--
theorem `isLittleO_log_id_atTop` / 定理 `isLittleO_log_id_atTop`

English:
theorem isLittleO_log_id_atTop
  statement: log =o[atTop] id
  proof: isLittleO_pow_log_id_atTop.congr_left fun _ => pow_one _

中文:
定理 isLittleO_log_id_atTop
  结论: log =o[atTop] id
  证明: isLittleO_pow_log_id_atTop.congr_left fun _ => pow_one _

Depends on / 依赖: congr_left, isLittleO_pow_log_id_atTop, isLittleO_pow_log_id_atTop.congr_left, pow_one
-/
theorem isLittleO_log_id_atTop : log =o[atTop] id :=
  isLittleO_pow_log_id_atTop.congr_left fun _ => pow_one _

/--
theorem `isLittleO_const_log_atTop` / 定理 `isLittleO_const_log_atTop`

English:
theorem isLittleO_const_log_atTop
  given: {c : Real}
  statement: (fun _ => c) =o[atTop] log
  proof: by
  refine Asymptotics.isLittleO_of_tendsto' ?_
 Tendsto.div_atTop (a := c) (by simp) tendsto_log_atTop
  filter_upwards [eventually_gt_atTop 1] with x hx
  aesop (add safe forward log_pos)

中文:
定理 isLittleO_const_log_atTop
  条件: {c : 实数}
  结论: (fun _ => c) =o[atTop] log
  证明: by
  refine Asymptotics.isLittleO_of_tendsto' ?_
 Tendsto.div_atTop (a := c) (by simp) tendsto_log_atTop
  filter_upwards [eventually_gt_atTop 1] with x hx
  aesop (add safe forward log_pos)

Depends on / 依赖: Asymptotics, Asymptotics.isLittleO_of_tendsto, Tendsto, Tendsto.div_atTop, div_atTop, eventually_gt_atTop, filter_upwards, forward, isLittleO_of_tendsto, log_pos, tendsto_log_atTop
-/
theorem isLittleO_const_log_atTop {c : Real} : (fun _ => c) =o[atTop] log := by
  refine Asymptotics.isLittleO_of_tendsto' ?_
 Tendsto.div_atTop (a := c) (by simp) tendsto_log_atTop
  filter_upwards [eventually_gt_atTop 1] with x hx
  aesop (add safe forward log_pos)

/--
Definition of `expPartialHomeomorph` / `expPartialHomeomorph` 的定义

English:
definition expPartialHomeomorph
  signature: : OpenPartialHomeomorph Real Real where
  body: Real.exp
  invFun := Real.log
  source := univ
  target := Ioi (0 : Real)
  map_source' x _ := exp_pos x
  map_target' _ _ := mem_univ _
  left_inv' _ _ := by simp
  right_inv' _ hx := exp_log hx
  open_source := isOpen_univ
  open_target := isOpen_Ioi
  continuousOn_toFun := continuousOn_exp
  continuousOn_invFun x hx := (continuousAt_log (ne_of_gt hx)).continuousWithinAt

@[simp]

中文:
定义 expPartialHomeomorph
  签名: : OpenPartialHomeomorph 实数 实数 where
  定义体: Real.exp
  invFun := Real.log
  source := univ
  target := Ioi (0 : Real)
  map_source' x _ := exp_pos x
  map_target' _ _ := mem_univ _
  left_inv' _ _ := by simp
  right_inv' _ hx := exp_log hx
  open_source := isOpen_univ
  open_target := isOpen_Ioi
  continuousOn_toFun := continuousOn_exp
  continuousOn_invFun x hx := (continuousAt_log (ne_of_gt hx)).continuousWithinAt

@[simp]
-/
@[simps] noncomputable def expPartialHomeomorph : OpenPartialHomeomorph Real Real where
  toFun := Real.exp
  invFun := Real.log
  source := univ
  target := Ioi (0 : Real)
  map_source' x _ := exp_pos x
  map_target' _ _ := mem_univ _
  left_inv' _ _ := by simp
  right_inv' _ hx := exp_log hx
  open_source := isOpen_univ
  open_target := isOpen_Ioi
  continuousOn_toFun := continuousOn_exp
  continuousOn_invFun x hx := (continuousAt_log (ne_of_gt hx)).continuousWithinAt

@[simp]
/--
theorem `image_log_Ioi` / 定理 `image_log_Ioi`

English:
theorem image_log_Ioi
  given: {a : Real} (ha : 0 < a)
  statement: log '' Ioi a = Ioi (log a)
  proof: (continuousOn_log.mono fun _ hx => (ha.trans_le hx).ne').image_Ioi_of_strictMonoOn
    (strictMonoOn_log.mono fun _ hx => ha.trans_le hx) tendsto_log_atTop

@[simp]

中文:
定理 image_log_Ioi
  条件: {a : 实数} (ha : 0 < a)
  结论: log '' 左开右无界区间 a = 左开右无界区间 (log a)
  证明: (continuousOn_log.mono fun _ hx => (ha.trans_le hx).ne').image_Ioi_of_strictMonoOn
    (strictMonoOn_log.mono fun _ hx => ha.trans_le hx) tendsto_log_atTop

@[simp]

Depends on / 依赖: continuousOn_log, continuousOn_log.mono, ha.trans_le, image_Ioi_of_strictMonoOn, strictMonoOn_log, strictMonoOn_log.mono, tendsto_log_atTop, trans_le
-/
theorem image_log_Ioi {a : Real} (ha : 0 < a) : log '' Ioi a = Ioi (log a) :=
  (continuousOn_log.mono fun _ hx => (ha.trans_le hx).ne').image_Ioi_of_strictMonoOn
    (strictMonoOn_log.mono fun _ hx => ha.trans_le hx) tendsto_log_atTop

@[simp]
/--
theorem `image_log_Ici` / 定理 `image_log_Ici`

English:
theorem image_log_Ici
  given: {a : Real} (ha : 0 < a)
  statement: log '' Ici a = Ici (log a)
  proof: (continuousOn_log.mono fun _ hx => (ha.trans_le hx).ne').image_Ici_of_monotoneOn
    (strictMonoOn_log.monotoneOn.mono fun _ hx => ha.trans_le hx) tendsto_log_atTop

@[simp]

中文:
定理 image_log_Ici
  条件: {a : 实数} (ha : 0 < a)
  结论: log '' 左闭右无界区间 a = 左闭右无界区间 (log a)
  证明: (continuousOn_log.mono fun _ hx => (ha.trans_le hx).ne').image_Ici_of_monotoneOn
    (strictMonoOn_log.monotoneOn.mono fun _ hx => ha.trans_le hx) tendsto_log_atTop

@[simp]

Depends on / 依赖: continuousOn_log, continuousOn_log.mono, ha.trans_le, image_Ici_of_monotoneOn, monotoneOn, strictMonoOn_log, strictMonoOn_log.monotoneOn.mono, tendsto_log_atTop, trans_le
-/
theorem image_log_Ici {a : Real} (ha : 0 < a) : log '' Ici a = Ici (log a) :=
  (continuousOn_log.mono fun _ hx => (ha.trans_le hx).ne').image_Ici_of_monotoneOn
    (strictMonoOn_log.monotoneOn.mono fun _ hx => ha.trans_le hx) tendsto_log_atTop

@[simp]
/--
theorem `image_log_Icc` / 定理 `image_log_Icc`

English:
theorem image_log_Icc
  given: {a b : Real} (ha : 0 < a) (hab : a <= b)
  statement: log '' Icc a b = Icc (log a) (log b)
  proof: (continuousOn_log.mono fun _ hx => (ha.trans_le hx.1).ne').image_Icc_of_monotoneOn hab
    (strictMonoOn_log.monotoneOn.mono fun _ hx => ha.trans_le hx.1)

@[simp]

中文:
定理 image_log_Icc
  条件: {a b : 实数} (ha : 0 < a) (hab : a <= b)
  结论: log '' 闭区间 a b = 闭区间 (log a) (log b)
  证明: (continuousOn_log.mono fun _ hx => (ha.trans_le hx.1).ne').image_Icc_of_monotoneOn hab
    (strictMonoOn_log.monotoneOn.mono fun _ hx => ha.trans_le hx.1)

@[simp]

Depends on / 依赖: continuousOn_log, continuousOn_log.mono, ha.trans_le, image_Icc_of_monotoneOn, monotoneOn, strictMonoOn_log, strictMonoOn_log.monotoneOn.mono, trans_le
-/
theorem image_log_Icc {a b : Real} (ha : 0 < a) (hab : a <= b) : log '' Icc a b = Icc (log a) (log b) :=
  (continuousOn_log.mono fun _ hx => (ha.trans_le hx.1).ne').image_Icc_of_monotoneOn hab
    (strictMonoOn_log.monotoneOn.mono fun _ hx => ha.trans_le hx.1)

@[simp]
/--
theorem `image_log_Ico` / 定理 `image_log_Ico`

English:
theorem image_log_Ico
  given: {a b : Real} (ha : 0 < a) (hab : a <= b)
  statement: log '' Ico a b = Ico (log a) (log b)
  proof: (continuousOn_log.mono fun _ hx => (ha.trans_le hx.1).ne').image_Ico_of_strictMonoOn hab
    (strictMonoOn_log.mono fun _ hx => ha.trans_le hx.1)

@[simp]

中文:
定理 image_log_Ico
  条件: {a b : 实数} (ha : 0 < a) (hab : a <= b)
  结论: log '' 左闭右开区间 a b = 左闭右开区间 (log a) (log b)
  证明: (continuousOn_log.mono fun _ hx => (ha.trans_le hx.1).ne').image_Ico_of_strictMonoOn hab
    (strictMonoOn_log.mono fun _ hx => ha.trans_le hx.1)

@[simp]

Depends on / 依赖: continuousOn_log, continuousOn_log.mono, ha.trans_le, image_Ico_of_strictMonoOn, strictMonoOn_log, strictMonoOn_log.mono, trans_le
-/
theorem image_log_Ico {a b : Real} (ha : 0 < a) (hab : a <= b) : log '' Ico a b = Ico (log a) (log b) :=
  (continuousOn_log.mono fun _ hx => (ha.trans_le hx.1).ne').image_Ico_of_strictMonoOn hab
    (strictMonoOn_log.mono fun _ hx => ha.trans_le hx.1)

@[simp]
/--
theorem `image_log_Ioc` / 定理 `image_log_Ioc`

English:
theorem image_log_Ioc
  given: {a b : Real} (ha : 0 < a) (hab : a <= b)
  statement: log '' Ioc a b = Ioc (log a) (log b)
  proof: (continuousOn_log.mono fun _ hx => (ha.trans_le hx.1).ne').image_Ioc_of_strictMonoOn hab
    (strictMonoOn_log.mono fun _ hx => ha.trans_le hx.1)

@[simp]

中文:
定理 image_log_Ioc
  条件: {a b : 实数} (ha : 0 < a) (hab : a <= b)
  结论: log '' 左开右闭区间 a b = 左开右闭区间 (log a) (log b)
  证明: (continuousOn_log.mono fun _ hx => (ha.trans_le hx.1).ne').image_Ioc_of_strictMonoOn hab
    (strictMonoOn_log.mono fun _ hx => ha.trans_le hx.1)

@[simp]

Depends on / 依赖: continuousOn_log, continuousOn_log.mono, ha.trans_le, image_Ioc_of_strictMonoOn, strictMonoOn_log, strictMonoOn_log.mono, trans_le
-/
theorem image_log_Ioc {a b : Real} (ha : 0 < a) (hab : a <= b) : log '' Ioc a b = Ioc (log a) (log b) :=
  (continuousOn_log.mono fun _ hx => (ha.trans_le hx.1).ne').image_Ioc_of_strictMonoOn hab
    (strictMonoOn_log.mono fun _ hx => ha.trans_le hx.1)

@[simp]
/--
theorem `image_log_Ioo` / 定理 `image_log_Ioo`

English:
theorem image_log_Ioo
  given: {a b : Real} (ha : 0 < a) (hab : a <= b)
  statement: log '' Ioo a b = Ioo (log a) (log b)
  proof: (continuousOn_log.mono fun _ hx => (ha.trans_le hx.1).ne').image_Ioo_of_strictMonoOn hab
    (strictMonoOn_log.mono fun _ hx => ha.trans_le hx.1)

@[simp]

中文:
定理 image_log_Ioo
  条件: {a b : 实数} (ha : 0 < a) (hab : a <= b)
  结论: log '' 开区间 a b = 开区间 (log a) (log b)
  证明: (continuousOn_log.mono fun _ hx => (ha.trans_le hx.1).ne').image_Ioo_of_strictMonoOn hab
    (strictMonoOn_log.mono fun _ hx => ha.trans_le hx.1)

@[simp]

Depends on / 依赖: continuousOn_log, continuousOn_log.mono, ha.trans_le, image_Ioo_of_strictMonoOn, strictMonoOn_log, strictMonoOn_log.mono, trans_le
-/
theorem image_log_Ioo {a b : Real} (ha : 0 < a) (hab : a <= b) : log '' Ioo a b = Ioo (log a) (log b) :=
  (continuousOn_log.mono fun _ hx => (ha.trans_le hx.1).ne').image_Ioo_of_strictMonoOn hab
    (strictMonoOn_log.mono fun _ hx => ha.trans_le hx.1)

@[simp]
/--
theorem `image_log_uIcc` / 定理 `image_log_uIcc`

English:
theorem image_log_uIcc
  given: {a b : Real} (ha : 0 < a) (hb : 0 < b)
  proof: (continuousOn_log.mono fun _ hx => ((lt_min ha hb).trans_le hx.1).ne').image_uIcc_of_monotoneOn
    (strictMonoOn_log.monotoneOn.mono fun _ hx => (lt_min ha hb).trans_le hx.1)

@[simp]

中文:
定理 image_log_uIcc
  条件: {a b : 实数} (ha : 0 < a) (hb : 0 < b)
  证明: (continuousOn_log.mono fun _ hx => ((lt_min ha hb).trans_le hx.1).ne').image_uIcc_of_monotoneOn
    (strictMonoOn_log.monotoneOn.mono fun _ hx => (lt_min ha hb).trans_le hx.1)

@[simp]

Depends on / 依赖: continuousOn_log, continuousOn_log.mono, image_uIcc_of_monotoneOn, lt_min, monotoneOn, strictMonoOn_log, strictMonoOn_log.monotoneOn.mono, trans_le
-/
theorem image_log_uIcc {a b : Real} (ha : 0 < a) (hb : 0 < b) :
    log '' uIcc a b = uIcc (log a) (log b) :=
  (continuousOn_log.mono fun _ hx => ((lt_min ha hb).trans_le hx.1).ne').image_uIcc_of_monotoneOn
    (strictMonoOn_log.monotoneOn.mono fun _ hx => (lt_min ha hb).trans_le hx.1)

@[simp]
/--
theorem `image_log_Ioo_zero` / 定理 `image_log_Ioo_zero`

English:
theorem image_log_Ioo_zero
  given: {a : Real} (ha : 0 < a)
  statement: log '' Ioo 0 a = Iio (log a)
  proof: by
  nth_rw 1 [← exp_log ha, ← image_exp_Iio, ← image_comp, log_comp_exp, image_id]

@[simp]

中文:
定理 image_log_Ioo_zero
  条件: {a : 实数} (ha : 0 < a)
  结论: log '' 开区间 0 a = 左无界右开区间 (log a)
  证明: by
  nth_rw 1 [← exp_log ha, ← image_exp_Iio, ← image_comp, log_comp_exp, image_id]

@[simp]

Depends on / 依赖: exp_log, image_comp, image_exp_Iio, image_id, log_comp_exp, nth_rw
-/
theorem image_log_Ioo_zero {a : Real} (ha : 0 < a) : log '' Ioo 0 a = Iio (log a) := by
  nth_rw 1 [← exp_log ha, ← image_exp_Iio, ← image_comp, log_comp_exp, image_id]

@[simp]
/--
theorem `image_log_Ioc_zero` / 定理 `image_log_Ioc_zero`

English:
theorem image_log_Ioc_zero
  given: {a : Real} (ha : 0 < a)
  statement: log '' Ioc 0 a = Iic (log a)
  proof: by
  nth_rw 1 [← exp_log ha, ← image_exp_Iic, ← image_comp, log_comp_exp, image_id]

中文:
定理 image_log_Ioc_zero
  条件: {a : 实数} (ha : 0 < a)
  结论: log '' 左开右闭区间 0 a = 左无界右闭区间 (log a)
  证明: by
  nth_rw 1 [← exp_log ha, ← image_exp_Iic, ← image_comp, log_comp_exp, image_id]

Depends on / 依赖: exp_log, image_comp, image_exp_Iic, image_id, log_comp_exp, nth_rw
-/
theorem image_log_Ioc_zero {a : Real} (ha : 0 < a) : log '' Ioc 0 a = Iic (log a) := by
  nth_rw 1 [← exp_log ha, ← image_exp_Iic, ← image_comp, log_comp_exp, image_id]

end Real

namespace Nat.Prime

/--
theorem `log_pos` / 定理 `log_pos`

English:
theorem log_pos
  given: {p : Nat} (hp : p.Prime)
  statement: 0 < Real.log p
  proof: Real.log_pos mod_cast hp.one_lt

中文:
定理 log_pos
  条件: {p : 自然数} (hp : p.素)
  结论: 0 < 实数.log p
  证明: Real.log_pos mod_cast hp.one_lt

Depends on / 依赖: Real.log_pos, hp.one_lt, log_pos, mod_cast, one_lt
-/
theorem log_pos {p : Nat} (hp : p.Prime) : 0 < Real.log p :=
Real.log_pos mod_cast hp.one_lt

/--
theorem `log_ne_zero` / 定理 `log_ne_zero`

English:
theorem log_ne_zero
  given: {p : Nat} (hp : p.Prime)
  statement: Real.log p != 0
  proof: hp.log_pos.ne'

中文:
定理 log_ne_zero
  条件: {p : 自然数} (hp : p.素)
  结论: 实数.log p != 0
  证明: hp.log_pos.ne'

Depends on / 依赖: hp.log_pos.ne, log_pos
-/
theorem log_ne_zero {p : Nat} (hp : p.Prime) : Real.log p != 0 := hp.log_pos.ne'

end Nat.Prime

section Continuity

open Real

variable {α : Type*}

/--
theorem `Filter.Tendsto.log` / 定理 `Filter.Tendsto.log`

English:
theorem Filter.Tendsto.log
  given: {f : α -> Real} {l : Filter α} {x : Real} (h : Tendsto f l (𝓝 x)) (hx : x != 0)
  proof: (continuousAt_log hx).tendsto.comp h

中文:
定理 滤子.收敛.log
  条件: {f : α -> 实数} {l : 滤子 α} {x : 实数} (h : 收敛 f l (𝓝 x)) (hx : x != 0)
  证明: (continuousAt_log hx).tendsto.comp h

Depends on / 依赖: continuousAt_log, tendsto, tendsto.comp
-/
theorem Filter.Tendsto.log {f : α -> Real} {l : Filter α} {x : Real} (h : Tendsto f l (𝓝 x)) (hx : x != 0) :
    Tendsto (fun x => log (f x)) l (𝓝 (log x)) :=
  (continuousAt_log hx).tendsto.comp h

variable [TopologicalSpace α] {f : α -> Real} {s : Set α} {a : α}

@[fun_prop]
/--
theorem `Continuous.log` / 定理 `Continuous.log`

English:
theorem Continuous.log
  given: (hf : Continuous f) (h₀ : forall x, f x != 0)
  statement: Continuous fun x => log (f x)
  proof: continuousOn_log.comp_continuous hf h₀

@[fun_prop]
nonrec theorem ContinuousAt.log (hf : ContinuousAt f a) (h₀ : f a != 0) :
    ContinuousAt (fun x => log (f x)) a :=
  hf.log h₀

nonrec theorem ContinuousWithinAt.log (hf : ContinuousWithinAt f s a) (h₀ : f a != 0) :
    ContinuousWithinAt (fun x => log (f x)) s a :=
  hf.log h₀

@[fun_prop]

中文:
定理 连续.log
  条件: (hf : 连续 f) (h₀ : 对任意 x, f x != 0)
  结论: 连续 fun x => log (f x)
  证明: continuousOn_log.comp_continuous hf h₀

@[fun_prop]
nonrec theorem ContinuousAt.log (hf : ContinuousAt f a) (h₀ : f a != 0) :
    ContinuousAt (fun x => log (f x)) a :=
  hf.log h₀

nonrec theorem ContinuousWithinAt.log (hf : ContinuousWithinAt f s a) (h₀ : f a != 0) :
    ContinuousWithinAt (fun x => log (f x)) s a :=
  hf.log h₀

@[fun_prop]

Depends on / 依赖: comp_continuous, continuousOn_log, continuousOn_log.comp_continuous
-/
theorem Continuous.log (hf : Continuous f) (h₀ : forall x, f x != 0) : Continuous fun x => log (f x) :=
  continuousOn_log.comp_continuous hf h₀

@[fun_prop]
nonrec theorem ContinuousAt.log (hf : ContinuousAt f a) (h₀ : f a != 0) :
    ContinuousAt (fun x => log (f x)) a :=
  hf.log h₀

nonrec theorem ContinuousWithinAt.log (hf : ContinuousWithinAt f s a) (h₀ : f a != 0) :
    ContinuousWithinAt (fun x => log (f x)) s a :=
  hf.log h₀

@[fun_prop]
/--
theorem `ContinuousOn.log` / 定理 `ContinuousOn.log`

English:
theorem ContinuousOn.log
  given: (hf : ContinuousOn f s) (h₀ : forall x in s, f x != 0)
  proof: fun x hx => (hf x hx).log (h₀ x hx)

中文:
定理 ContinuousOn.log
  条件: (hf : ContinuousOn f s) (h₀ : 对任意 x in s, f x != 0)
  证明: fun x hx => (hf x hx).log (h₀ x hx)
-/
theorem ContinuousOn.log (hf : ContinuousOn f s) (h₀ : forall x in s, f x != 0) :
    ContinuousOn (fun x => log (f x)) s := fun x hx => (hf x hx).log (h₀ x hx)

end Continuity

section TendstoCompAddSub

open Filter

namespace Real

/--
theorem `tendsto_log_comp_add_sub_log` / 定理 `tendsto_log_comp_add_sub_log`

English:
theorem tendsto_log_comp_add_sub_log
  given: (y : Real)
  proof: by
  have : Tendsto (fun x => 1 + y / x) atTop (𝓝 (1 + 0)) :=
    tendsto_const_nhds.add (tendsto_const_nhds.div_atTop tendsto_id)
  rw [← comap_exp_nhds_exp]; rw [exp_zero]; rw [tendsto_comap_iff]; rw [← add_zero (1 : Real)]
  refine this.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : Real), eventually_gt_atTop (-y)] with x hx₀ hxy
  rw [comp_apply]; rw [exp_sub]; rw [exp_log]; rw [exp_log]; rw [one_add_div] <;> linarith

中文:
定理 tendsto_log_comp_add_sub_log
  条件: (y : 实数)
  证明: by
  have : Tendsto (fun x => 1 + y / x) atTop (𝓝 (1 + 0)) :=
    tendsto_const_nhds.add (tendsto_const_nhds.div_atTop tendsto_id)
  rw [← comap_exp_nhds_exp]; rw [exp_zero]; rw [tendsto_comap_iff]; rw [← add_zero (1 : Real)]
  refine this.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : Real), eventually_gt_atTop (-y)] with x hx₀ hxy
  rw [comp_apply]; rw [exp_sub]; rw [exp_log]; rw [exp_log]; rw [one_add_div] <;> linarith

Depends on / 依赖: Tendsto, add_zero, comap_exp_nhds_exp, comp_apply, div_atTop, eventually_gt_atTop, exp_log, exp_sub, exp_zero, filter_upwards, one_add_div, tendsto_comap_iff, tendsto_const_nhds, tendsto_const_nhds.add, tendsto_const_nhds.div_atTop, tendsto_id, this.congr
-/
theorem tendsto_log_comp_add_sub_log (y : Real) :
    Tendsto (fun x : Real => log (x + y) - log x) atTop (𝓝 0) := by
  have : Tendsto (fun x => 1 + y / x) atTop (𝓝 (1 + 0)) :=
    tendsto_const_nhds.add (tendsto_const_nhds.div_atTop tendsto_id)
  rw [← comap_exp_nhds_exp]; rw [exp_zero]; rw [tendsto_comap_iff]; rw [← add_zero (1 : Real)]
  refine this.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : Real), eventually_gt_atTop (-y)] with x hx₀ hxy
  rw [comp_apply]; rw [exp_sub]; rw [exp_log]; rw [exp_log]; rw [one_add_div] <;> linarith

/--
theorem `tendsto_log_nat_add_one_sub_log` / 定理 `tendsto_log_nat_add_one_sub_log`

English:
theorem tendsto_log_nat_add_one_sub_log
  statement: Tendsto (fun k : Nat => log (k + 1) - log k) atTop (𝓝 0)
  proof: (tendsto_log_comp_add_sub_log 1).comp tendsto_natCast_atTop_atTop

中文:
定理 tendsto_log_nat_add_one_sub_log
  结论: 收敛 (fun k : 自然数 => log (k + 1) - log k) atTop (𝓝 0)
  证明: (tendsto_log_comp_add_sub_log 1).comp tendsto_natCast_atTop_atTop

Depends on / 依赖: tendsto_log_comp_add_sub_log, tendsto_natCast_atTop_atTop
-/
theorem tendsto_log_nat_add_one_sub_log : Tendsto (fun k : Nat => log (k + 1) - log k) atTop (𝓝 0) :=
  (tendsto_log_comp_add_sub_log 1).comp tendsto_natCast_atTop_atTop

end Real

end TendstoCompAddSub

namespace Mathlib.Meta.Positivity
open Lean.Meta Qq

variable {e : Real} {d : Nat}

/--
lemma `log_nonneg_of_isNat` / 引理 `log_nonneg_of_isNat`

English:
lemma log_nonneg_of_isNat
  given: {n : Nat} (h : NormNum.IsNat e n)
  statement: 0 <= Real.log (e : Real)
  proof: by
  rw [NormNum.IsNat.to_eq h rfl]
  exact Real.log_natCast_nonneg _

中文:
引理 log_nonneg_of_is自然数
  条件: {n : 自然数} (h : NormNum.是自然数 e n)
  结论: 0 <= 实数.log (e : 实数)
  证明: by
  rw [NormNum.IsNat.to_eq h rfl]
  exact Real.log_natCast_nonneg _

Depends on / 依赖: NormNum, NormNum.IsNat.to_eq, Real.log_natCast_nonneg, log_natCast_nonneg, to_eq
-/
lemma log_nonneg_of_isNat {n : Nat} (h : NormNum.IsNat e n) : 0 <= Real.log (e : Real) := by
  rw [NormNum.IsNat.to_eq h rfl]
  exact Real.log_natCast_nonneg _

/--
lemma `log_pos_of_isNat` / 引理 `log_pos_of_isNat`

English:
lemma log_pos_of_isNat
  given: {n : Nat} (h : NormNum.IsNat e n) (w : Nat.blt 1 n = true)
  proof: by
  rw [NormNum.IsNat.to_eq h rfl]
  apply Real.log_pos
  simpa using w

中文:
引理 log_pos_of_is自然数
  条件: {n : 自然数} (h : NormNum.是自然数 e n) (w : 自然数.blt 1 n = true)
  证明: by
  rw [NormNum.IsNat.to_eq h rfl]
  apply Real.log_pos
  simpa using w

Depends on / 依赖: NormNum, NormNum.IsNat.to_eq, Real.log_pos, log_pos, to_eq
-/
lemma log_pos_of_isNat {n : Nat} (h : NormNum.IsNat e n) (w : Nat.blt 1 n = true) :
    0 < Real.log (e : Real) := by
  rw [NormNum.IsNat.to_eq h rfl]
  apply Real.log_pos
  simpa using w

/--
lemma `log_nonneg_of_isNegNat` / 引理 `log_nonneg_of_isNegNat`

English:
lemma log_nonneg_of_isNegNat
  given: {n : Nat} (h : NormNum.IsInt e (.negOfNat n))
  proof: by
  rw [NormNum.IsInt.neg_to_eq h rfl]
  exact Real.log_neg_natCast_nonneg _

中文:
引理 log_nonneg_of_isNeg自然数
  条件: {n : 自然数} (h : NormNum.是整数 e (.negOf自然数 n))
  证明: by
  rw [NormNum.IsInt.neg_to_eq h rfl]
  exact Real.log_neg_natCast_nonneg _

Depends on / 依赖: NormNum, NormNum.IsInt.neg_to_eq, Real.log_neg_natCast_nonneg, log_neg_natCast_nonneg, neg_to_eq
-/
lemma log_nonneg_of_isNegNat {n : Nat} (h : NormNum.IsInt e (.negOfNat n)) :
    0 <= Real.log (e : Real) := by
  rw [NormNum.IsInt.neg_to_eq h rfl]
  exact Real.log_neg_natCast_nonneg _

/--
lemma `log_pos_of_isNegNat` / 引理 `log_pos_of_isNegNat`

English:
lemma log_pos_of_isNegNat
  given: {n : Nat} (h : NormNum.IsInt e (.negOfNat n)) (w : Nat.blt 1 n = true)
  proof: by
  rw [NormNum.IsInt.neg_to_eq h rfl]
  rw [Real.log_neg_eq_log]
  apply Real.log_pos
  simpa using w

中文:
引理 log_pos_of_isNeg自然数
  条件: {n : 自然数} (h : NormNum.是整数 e (.negOf自然数 n)) (w : 自然数.blt 1 n = true)
  证明: by
  rw [NormNum.IsInt.neg_to_eq h rfl]
  rw [Real.log_neg_eq_log]
  apply Real.log_pos
  simpa using w

Depends on / 依赖: NormNum, NormNum.IsInt.neg_to_eq, Real.log_neg_eq_log, Real.log_pos, log_neg_eq_log, log_pos, neg_to_eq
-/
lemma log_pos_of_isNegNat {n : Nat} (h : NormNum.IsInt e (.negOfNat n)) (w : Nat.blt 1 n = true) :
    0 < Real.log (e : Real) := by
  rw [NormNum.IsInt.neg_to_eq h rfl]
  rw [Real.log_neg_eq_log]
  apply Real.log_pos
  simpa using w

/--
lemma `log_pos_of_isNNRat` / 引理 `log_pos_of_isNNRat`

English:
lemma log_pos_of_isNNRat
  given: {n : Nat}
  proof: by
      simpa using (Rat.cast_lt (K := Real)).2 (of_decide_eq_true h)
    exact Real.log_pos this

中文:
引理 log_pos_of_isNNRat
  条件: {n : 自然数}
  证明: by
      simpa using (Rat.cast_lt (K := Real)).2 (of_decide_eq_true h)
    exact Real.log_pos this

Depends on / 依赖: Rat.cast_lt, Real.log_pos, cast_lt, log_pos, of_decide_eq_true
-/
lemma log_pos_of_isNNRat {n : Nat} :
    (NormNum.IsNNRat e n d) -> (decide ((1 : Rat) < n / d)) -> (0 < Real.log (e : Real))
  | ⟨inv, eq⟩, h => by
    rw [eq]; rw [invOf_eq_inv]; rw [← div_eq_mul_inv]
    have : 1 < (n : Real) / d := by
      simpa using (Rat.cast_lt (K := Real)).2 (of_decide_eq_true h)
    exact Real.log_pos this

/--
lemma `log_pos_of_isRat_neg` / 引理 `log_pos_of_isRat_neg`

English:
lemma log_pos_of_isRat_neg
  given: {n : Int}
  proof: by exact_mod_cast of_decide_eq_true h
    exact Real.log_pos_of_lt_neg_one this

中文:
引理 log_pos_of_isRat_neg
  条件: {n : 整数}
  证明: by exact_mod_cast of_decide_eq_true h
    exact Real.log_pos_of_lt_neg_one this

Depends on / 依赖: Real.log_pos_of_lt_neg_one, log_pos_of_lt_neg_one, of_decide_eq_true
-/
lemma log_pos_of_isRat_neg {n : Int} :
    (NormNum.IsRat e n d) -> (decide (n / d < (-1 : Rat))) -> (0 < Real.log (e : Real))
  | ⟨inv, eq⟩, h => by
    rw [eq]; rw [invOf_eq_inv]; rw [← div_eq_mul_inv]
    have : (n : Real) / d < -1 := by exact_mod_cast of_decide_eq_true h
    exact Real.log_pos_of_lt_neg_one this

/--
lemma `log_nz_of_isNNRat` / 引理 `log_nz_of_isNNRat`

English:
lemma log_nz_of_isNNRat
  given: {n : Nat}
  statement: (NormNum.IsNNRat e n d) -> (decide ((0 : Rat) < n / d))
  proof: by
      simpa using (Rat.cast_pos (K := Real)).2 (of_decide_eq_true h₁)
    have h₂' : (n : Real) / d < 1 := by
      simpa using (Rat.cast_lt (K := Real)).2 (of_decide_eq_true h₂)
exact ne_of_lt Real.log_neg h₁' h₂'

中文:
引理 log_nz_of_isNNRat
  条件: {n : 自然数}
  结论: (NormNum.是NNRat e n d) -> (decide ((0 : 有理数) < n / d))
  证明: by
      simpa using (Rat.cast_pos (K := Real)).2 (of_decide_eq_true h₁)
    have h₂' : (n : Real) / d < 1 := by
      simpa using (Rat.cast_lt (K := Real)).2 (of_decide_eq_true h₂)
exact ne_of_lt Real.log_neg h₁' h₂'

Depends on / 依赖: Rat.cast_lt, Rat.cast_pos, Real.log_neg, cast_lt, cast_pos, log_neg, ne_of_lt, of_decide_eq_true
-/
lemma log_nz_of_isNNRat {n : Nat} : (NormNum.IsNNRat e n d) -> (decide ((0 : Rat) < n / d))
    -> (decide (n / d < (1 : Rat))) -> (Real.log (e : Real) != 0)
  | ⟨inv, eq⟩, h₁, h₂ => by
    rw [eq]; rw [invOf_eq_inv]; rw [← div_eq_mul_inv]
    have h₁' : 0 < (n : Real) / d := by
      simpa using (Rat.cast_pos (K := Real)).2 (of_decide_eq_true h₁)
    have h₂' : (n : Real) / d < 1 := by
      simpa using (Rat.cast_lt (K := Real)).2 (of_decide_eq_true h₂)
exact ne_of_lt Real.log_neg h₁' h₂'

/--
lemma `log_nz_of_isRat_neg` / 引理 `log_nz_of_isRat_neg`

English:
lemma log_nz_of_isRat_neg
  given: {n : Int}
  statement: (NormNum.IsRat e n d) -> (decide (n / d < (0 : Rat)))
  proof: by exact_mod_cast of_decide_eq_true h₁
    have h₂' : -1 < (n : Real) / d := by exact_mod_cast of_decide_eq_true h₂
exact ne_of_lt Real.log_neg_of_lt_zero h₁' h₂'

中文:
引理 log_nz_of_isRat_neg
  条件: {n : 整数}
  结论: (NormNum.是有理数 e n d) -> (decide (n / d < (0 : 有理数)))
  证明: by exact_mod_cast of_decide_eq_true h₁
    have h₂' : -1 < (n : Real) / d := by exact_mod_cast of_decide_eq_true h₂
exact ne_of_lt Real.log_neg_of_lt_zero h₁' h₂'

Depends on / 依赖: Real.log_neg_of_lt_zero, log_neg_of_lt_zero, ne_of_lt, of_decide_eq_true
-/
lemma log_nz_of_isRat_neg {n : Int} : (NormNum.IsRat e n d) -> (decide (n / d < (0 : Rat)))
    -> (decide ((-1 : Rat) < n / d)) -> (Real.log (e : Real) != 0)
  | ⟨inv, eq⟩, h₁, h₂ => by
    rw [eq]; rw [invOf_eq_inv]; rw [← div_eq_mul_inv]
    have h₁' : (n : Real) / d < 0 := by exact_mod_cast of_decide_eq_true h₁
    have h₂' : -1 < (n : Real) / d := by exact_mod_cast of_decide_eq_true h₂
exact ne_of_lt Real.log_neg_of_lt_zero h₁' h₂'

/-- Extension for the `positivity` tactic: `Real.log` of a natural number is always nonnegative. -/
@[positivity Real.log (Nat.cast _)]
meta def evalLogNatCast : PositivityExt where eval {u α} _zα pα? e :=
  match pα? with | none => pure .none | some _ => do
  match u, α, e with
  | 0, ~q(Real), ~q(Real.log (Nat.cast $a)) =>
    assertInstancesCommute
    pure (.nonnegative q(Real.log_natCast_nonneg $a))
  | _, _, _ => throwError "not Real.log"

/-- Extension for the `positivity` tactic: `Real.log` of an integer is always nonnegative. -/
@[positivity Real.log (Int.cast _)]
meta def evalLogIntCast : PositivityExt where eval {u α} _zα pα? e :=
  match pα? with | none => pure .none | some _ => do
  match u, α, e with
  | 0, ~q(Real), ~q(Real.log (Int.cast $a)) =>
    assertInstancesCommute
    pure (.nonnegative q(Real.log_intCast_nonneg $a))
  | _, _, _ => throwError "not Real.log"

/-- Extension for the `positivity` tactic: `Real.log` of a numeric literal. -/
@[positivity Real.log _]
meta def evalLogNatLit : PositivityExt where eval {u α} _ pα? e :=
  match pα? with | none => pure .none | some _ => do
  match u, α, e with
  | 0, ~q(Real), ~q(Real.log $a) =>
    match ← NormNum.derive a with
    | .isNat (_ : Q(AddMonoidWithOne Real)) lit p =>
      assumeInstancesCommute
      have p : Q(NormNum.IsNat $a $lit) := p
      if 1 < lit.natLit! then
        let p' : Q(Nat.blt 1 $lit = true) := (q(Eq.refl true) : Lean.Expr)
        pure (.positive q(log_pos_of_isNat $p $p'))
      else
        pure (.nonnegative q(log_nonneg_of_isNat $p))
    | .isNegNat _ lit p =>
      assumeInstancesCommute
      have p : Q(NormNum.IsInt $a (Int.negOfNat $lit)) := p
      if 1 < lit.natLit! then
        let p' : Q(Nat.blt 1 $lit = true) := (q(Eq.refl true) : Lean.Expr)
        pure (.positive q(log_pos_of_isNegNat $p $p'))
      else
        pure (.nonnegative q(log_nonneg_of_isNegNat $p))
    | .isNNRat _ q n d p =>
      assumeInstancesCommute
      if q < 1 then
        let w₁ : Q(decide ((0 : Rat) < $n / $d) = true) := (q(Eq.refl true) : Lean.Expr)
        let w₂ : Q(decide ($n / $d < (1 : Rat)) = true) := (q(Eq.refl true) : Lean.Expr)
        pure (.nonzero q(log_nz_of_isNNRat $p $w₁ $w₂))
      else if 1 < q then
        let w : Q(decide ((1 : Rat) < $n / $d) = true) := (q(Eq.refl true) : Lean.Expr)
        pure (.positive q(log_pos_of_isNNRat $p $w))
      else
        failure
    | .isNegNNRat _ q n d p =>
      assumeInstancesCommute
      if -1 < q then
        let w₁ : Q(decide ((Int.negOfNat $n) / $d < (0 : Rat)) = true) :=
          (q(Eq.refl true) : Lean.Expr)
        let w₂ : Q(decide ((-1 : Rat) < (Int.negOfNat $n) / $d) = true) :=
          (q(Eq.refl true) : Lean.Expr)
        pure (.nonzero q(log_nz_of_isRat_neg $p $w₁ $w₂))
      else if q < -1 then
        let w : Q(decide ((Int.negOfNat $n) / $d < (-1 : Rat)) = true) :=
          (q(Eq.refl true) : Lean.Expr)
        pure (.positive q(log_pos_of_isRat_neg $p $w))
      else
        failure
    | _ => failure
  | _, _, _ => throwError "not Real.log"

end Mathlib.Meta.Positivity
