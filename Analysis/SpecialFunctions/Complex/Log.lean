/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Abhimanyu Pallavi Sudhir, Jean Lo, Calle Sönne, Benjamin Davidson
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.Arg
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# The complex `log` function

Basic properties, relationship with `exp`.
-/

@[expose] public section

noncomputable section

namespace Complex

open Set Filter Bornology

open scoped Real Topology ComplexConjugate

/-- Inverse of the `exp` function. Returns values such that `(log x).im > - π` and `(log x).im ≤ π`.
  `log 0 = 0` -/
@[pp_nodot]
/--
Definition of `log` / `log` 的定义

English:
definition log
  signature: (x : Complex)
  body: Real.log ‖x‖ + arg x * I

中文:
定义 log
  签名: (x : 复形)
  定义体: Real.log ‖x‖ + arg x * I

Depends on / 依赖: Real.log
-/
noncomputable def log (x : Complex) : Complex :=
  Real.log ‖x‖ + arg x * I

/--
theorem `log_re` / 定理 `log_re`

English:
theorem log_re
  given: (x : Complex)
  statement: x.log.re = Real.log ‖x‖
  proof: by simp [log]

中文:
定理 log_re
  条件: (x : 复形)
  结论: x.log.re = 实数.log ‖x‖
  证明: by simp [log]
-/
theorem log_re (x : Complex) : x.log.re = Real.log ‖x‖ := by simp [log]

/--
theorem `log_im` / 定理 `log_im`

English:
theorem log_im
  given: (x : Complex)
  statement: x.log.im = x.arg
  proof: by simp [log]

中文:
定理 log_im
  条件: (x : 复形)
  结论: x.log.im = x.arg
  证明: by simp [log]
-/
theorem log_im (x : Complex) : x.log.im = x.arg := by simp [log]

/--
theorem `neg_pi_lt_log_im` / 定理 `neg_pi_lt_log_im`

English:
theorem neg_pi_lt_log_im
  given: (x : Complex)
  statement: -π < (log x).im
  proof: by simp only [log_im, neg_pi_lt_arg]

中文:
定理 neg_pi_lt_log_im
  条件: (x : 复形)
  结论: -π < (log x).im
  证明: by simp only [log_im, neg_pi_lt_arg]

Depends on / 依赖: log_im, neg_pi_lt_arg
-/
theorem neg_pi_lt_log_im (x : Complex) : -π < (log x).im := by simp only [log_im, neg_pi_lt_arg]

/--
theorem `log_im_le_pi` / 定理 `log_im_le_pi`

English:
theorem log_im_le_pi
  given: (x : Complex)
  statement: (log x).im <= π
  proof: by simp only [log_im, arg_le_pi]

中文:
定理 log_im_le_pi
  条件: (x : 复形)
  结论: (log x).im <= π
  证明: by simp only [log_im, arg_le_pi]

Depends on / 依赖: arg_le_pi, log_im
-/
theorem log_im_le_pi (x : Complex) : (log x).im <= π := by simp only [log_im, arg_le_pi]

/--
theorem `exp_log` / 定理 `exp_log`

English:
theorem exp_log
  given: {x : Complex} (hx : x != 0)
  statement: exp (log x) = x
  proof: by
  rw [log]; rw [exp_add_mul_I]; rw [← ofReal_sin]; rw [sin_arg]; rw [← ofReal_cos]; rw [cos_arg hx]; rw [← ofReal_exp]; rw [Real.exp_log (norm_pos_iff.mpr hx)]; rw [mul_add]; rw [ofReal_div]; rw [ofReal_div]; rw [mul_div_cancel₀ _ (ofReal_ne_zero.2 <| norm_ne_zero_iff.mpr hx)]; rw [← mul_assoc]; 

中文:
定理 exp_log
  条件: {x : 复形} (hx : x != 0)
  结论: exp (log x) = x
  证明: by
  rw [log]; rw [exp_add_mul_I]; rw [← ofReal_sin]; rw [sin_arg]; rw [← ofReal_cos]; rw [cos_arg hx]; rw [← ofReal_exp]; rw [Real.exp_log (norm_pos_iff.mpr hx)]; rw [mul_add]; rw [ofReal_div]; rw [ofReal_div]; rw [mul_div_cancel₀ _ (ofReal_ne_zero.2 <| norm_ne_zero_iff.mpr hx)]; rw [← mul_assoc]; 

Depends on / 依赖: Real.exp_log, cos_arg, exp_add_mul_I, exp_log, mul_add, mul_assoc, norm_ne_zero_iff, norm_ne_zero_iff.mpr, norm_pos_iff, norm_pos_iff.mpr, ofReal_cos, ofReal_div, ofReal_exp, ofReal_ne_zero, ofReal_sin, re_add_im, sin_arg
-/
theorem exp_log {x : Complex} (hx : x != 0) : exp (log x) = x := by
  rw [log]; rw [exp_add_mul_I]; rw [← ofReal_sin]; rw [sin_arg]; rw [← ofReal_cos]; rw [cos_arg hx]; rw [← ofReal_exp]; rw [Real.exp_log (norm_pos_iff.mpr hx)]; rw [mul_add]; rw [ofReal_div]; rw [ofReal_div]; rw [mul_div_cancel₀ _ (ofReal_ne_zero.2 <| norm_ne_zero_iff.mpr hx)]; rw [← mul_assoc]; rw [mul_div_cancel₀ _ (ofReal_ne_zero.2 <| norm_ne_zero_iff.mpr hx)]; rw [re_add_im]

@[simp]
/--
theorem `range_exp` / 定理 `range_exp`

English:
theorem range_exp
  statement: Set.range exp = {0}ᶜ
  proof: Set.ext fun x =>
    ⟨by
      rintro ⟨x, rfl⟩
      exact exp_ne_zero x, fun hx => ⟨log x, exp_log hx⟩⟩

中文:
定理 range_exp
  结论: 集合.range exp = {0}ᶜ
  证明: Set.ext fun x =>
    ⟨by
      rintro ⟨x, rfl⟩
      exact exp_ne_zero x, fun hx => ⟨log x, exp_log hx⟩⟩

Depends on / 依赖: Set.ext, exp_log, exp_ne_zero
-/
theorem range_exp : Set.range exp = {0}ᶜ :=
  Set.ext fun x =>
    ⟨by
      rintro ⟨x, rfl⟩
      exact exp_ne_zero x, fun hx => ⟨log x, exp_log hx⟩⟩

/--
theorem `log_exp` / 定理 `log_exp`

English:
theorem log_exp
  given: {x : Complex} (hx₁ : -π < x.im) (hx₂ : x.im <= π)
  statement: log (exp x) = x
  proof: by
  rw [log]; rw [norm_exp]; rw [Real.log_exp]; rw [exp_eq_exp_re_mul_sin_add_cos]; rw [← ofReal_exp]; rw [arg_mul_cos_add_sin_mul_I (Real.exp_pos _) ⟨hx₁]; rw [hx₂⟩]; rw [re_add_im]

中文:
定理 log_exp
  条件: {x : 复形} (hx₁ : -π < x.im) (hx₂ : x.im <= π)
  结论: log (exp x) = x
  证明: by
  rw [log]; rw [norm_exp]; rw [Real.log_exp]; rw [exp_eq_exp_re_mul_sin_add_cos]; rw [← ofReal_exp]; rw [arg_mul_cos_add_sin_mul_I (Real.exp_pos _) ⟨hx₁]; rw [hx₂⟩]; rw [re_add_im]

Depends on / 依赖: Real.exp_pos, Real.log_exp, arg_mul_cos_add_sin_mul_I, exp_eq_exp_re_mul_sin_add_cos, exp_pos, log_exp, norm_exp, ofReal_exp, re_add_im
-/
theorem log_exp {x : Complex} (hx₁ : -π < x.im) (hx₂ : x.im <= π) : log (exp x) = x := by
  rw [log]; rw [norm_exp]; rw [Real.log_exp]; rw [exp_eq_exp_re_mul_sin_add_cos]; rw [← ofReal_exp]; rw [arg_mul_cos_add_sin_mul_I (Real.exp_pos _) ⟨hx₁]; rw [hx₂⟩]; rw [re_add_im]

/--
theorem `log_exp_eq_re_add_toIocMod` / 定理 `log_exp_eq_re_add_toIocMod`

English:
theorem log_exp_eq_re_add_toIocMod
  given: (x : Complex)
  proof: by
  rw [log]; rw [norm_exp]; rw [Real.log_exp]; rw [arg_exp]

中文:
定理 log_exp_eq_re_add_toIocMod
  条件: (x : 复形)
  证明: by
  rw [log]; rw [norm_exp]; rw [Real.log_exp]; rw [arg_exp]

Depends on / 依赖: Real.log_exp, arg_exp, log_exp, norm_exp
-/
theorem log_exp_eq_re_add_toIocMod (x : Complex) :
    log (exp x) = x.re + (toIocMod Real.two_pi_pos (-π) x.im) * I := by
  rw [log]; rw [norm_exp]; rw [Real.log_exp]; rw [arg_exp]

/--
theorem `log_exp_eq_sub_toIocDiv` / 定理 `log_exp_eq_sub_toIocDiv`

English:
theorem log_exp_eq_sub_toIocDiv
  given: (x : Complex)
  proof: by
  rw [log_exp_eq_re_add_toIocMod]; rw [toIocMod]; rw [ofReal_sub]; rw [sub_mul]; rw [← add_sub_assoc]
  simp [mul_assoc]

中文:
定理 log_exp_eq_sub_toIocDiv
  条件: (x : 复形)
  证明: by
  rw [log_exp_eq_re_add_toIocMod]; rw [toIocMod]; rw [ofReal_sub]; rw [sub_mul]; rw [← add_sub_assoc]
  simp [mul_assoc]

Depends on / 依赖: add_sub_assoc, log_exp_eq_re_add_toIocMod, mul_assoc, ofReal_sub, sub_mul, toIocMod
-/
theorem log_exp_eq_sub_toIocDiv (x : Complex) :
    log (exp x) = x - (toIocDiv Real.two_pi_pos (-π) x.im) * (2 * π * I) := by
  rw [log_exp_eq_re_add_toIocMod]; rw [toIocMod]; rw [ofReal_sub]; rw [sub_mul]; rw [← add_sub_assoc]
  simp [mul_assoc]

/--
theorem `exp_inj_of_neg_pi_lt_of_le_pi` / 定理 `exp_inj_of_neg_pi_lt_of_le_pi`

English:
theorem exp_inj_of_neg_pi_lt_of_le_pi
  statement: {x y : Complex} (hx₁ : -π < x.im) (hx₂ : x.im <= π) (hy₁ : -π < y.im)
  proof: by
  rw [← log_exp hx₁ hx₂]; rw [← log_exp hy₁ hy₂]; rw [hxy]

中文:
定理 exp_inj_of_neg_pi_lt_of_le_pi
  结论: {x y : 复形} (hx₁ : -π < x.im) (hx₂ : x.im <= π) (hy₁ : -π < y.im)
  证明: by
  rw [← log_exp hx₁ hx₂]; rw [← log_exp hy₁ hy₂]; rw [hxy]

Depends on / 依赖: log_exp
-/
theorem exp_inj_of_neg_pi_lt_of_le_pi {x y : Complex} (hx₁ : -π < x.im) (hx₂ : x.im <= π) (hy₁ : -π < y.im)
    (hy₂ : y.im <= π) (hxy : exp x = exp y) : x = y := by
  rw [← log_exp hx₁ hx₂]; rw [← log_exp hy₁ hy₂]; rw [hxy]

/--
theorem `ofReal_log` / 定理 `ofReal_log`

English:
theorem ofReal_log
  given: {x : Real} (hx : 0 <= x)
  statement: (x.log : Complex) = log x
  proof: Complex.ext (by rw [log_re, ofReal_re, Complex.norm_of_nonneg hx])
    (by rw [ofReal_im, log_im, arg_ofReal_of_nonneg hx])

@[simp, norm_cast]

中文:
定理 of实数_log
  条件: {x : 实数} (hx : 0 <= x)
  结论: (x.log : 复形) = log x
  证明: Complex.ext (by rw [log_re, ofReal_re, Complex.norm_of_nonneg hx])
    (by rw [ofReal_im, log_im, arg_ofReal_of_nonneg hx])

@[simp, norm_cast]

Depends on / 依赖: Complex.ext, Complex.norm_of_nonneg, arg_ofReal_of_nonneg, log_im, log_re, norm_of_nonneg, ofReal_im, ofReal_re
-/
theorem ofReal_log {x : Real} (hx : 0 <= x) : (x.log : Complex) = log x :=
  Complex.ext (by rw [log_re, ofReal_re, Complex.norm_of_nonneg hx])
    (by rw [ofReal_im, log_im, arg_ofReal_of_nonneg hx])

@[simp, norm_cast]
/--
lemma `natCast_log` / 引理 `natCast_log`

English:
lemma natCast_log
  given: {n : Nat}
  statement: Real.log n = log n
  proof: ofReal_natCast n ▸ ofReal_log n.cast_nonneg

@[simp]

中文:
引理 natCast_log
  条件: {n : 自然数}
  结论: 实数.log n = log n
  证明: ofReal_natCast n ▸ ofReal_log n.cast_nonneg

@[simp]

Depends on / 依赖: cast_nonneg, n.cast_nonneg, ofReal_log, ofReal_natCast
-/
lemma natCast_log {n : Nat} : Real.log n = log n := ofReal_natCast n ▸ ofReal_log n.cast_nonneg

@[simp]
/--
lemma `ofNat_log` / 引理 `ofNat_log`

English:
lemma ofNat_log
  given: {n : Nat} [n.AtLeastTwo]
  proof: natCast_log

中文:
引理 of自然数_log
  条件: {n : 自然数} [n.AtLeastTwo]
  证明: natCast_log

Depends on / 依赖: natCast_log
-/
lemma ofNat_log {n : Nat} [n.AtLeastTwo] :
    Real.log ofNat(n) = log (OfNat.ofNat n) :=
  natCast_log

/--
theorem `log_ofReal_re` / 定理 `log_ofReal_re`

English:
theorem log_ofReal_re
  given: (x : Real)
  statement: (log (x : Complex)).re = Real.log x
  proof: by simp [log_re]

中文:
定理 log_of实数_re
  条件: (x : 实数)
  结论: (log (x : 复形)).re = 实数.log x
  证明: by simp [log_re]

Depends on / 依赖: log_re
-/
theorem log_ofReal_re (x : Real) : (log (x : Complex)).re = Real.log x := by simp [log_re]

/--
theorem `log_ofReal_mul` / 定理 `log_ofReal_mul`

English:
theorem log_ofReal_mul
  given: {r : Real} (hr : 0 < r) {x : Complex} (hx : x != 0)
  proof: by
  replace hx := norm_ne_zero_iff.mpr hx
  simp_rw [log, norm_mul, norm_real, arg_real_mul _ hr, Real.norm_of_nonneg hr.le,
    Real.log_mul hr.ne' hx, ofReal_add, add_assoc]

中文:
定理 log_of实数_mul
  条件: {r : 实数} (hr : 0 < r) {x : 复形} (hx : x != 0)
  证明: by
  replace hx := norm_ne_zero_iff.mpr hx
  simp_rw [log, norm_mul, norm_real, arg_real_mul _ hr, Real.norm_of_nonneg hr.le,
    Real.log_mul hr.ne' hx, ofReal_add, add_assoc]

Depends on / 依赖: Real.log_mul, Real.norm_of_nonneg, add_assoc, arg_real_mul, hr.le, hr.ne, log_mul, norm_mul, norm_ne_zero_iff, norm_ne_zero_iff.mpr, norm_of_nonneg, norm_real, ofReal_add, replace, simp_rw
-/
theorem log_ofReal_mul {r : Real} (hr : 0 < r) {x : Complex} (hx : x != 0) :
    log (r * x) = Real.log r + log x := by
  replace hx := norm_ne_zero_iff.mpr hx
  simp_rw [log, norm_mul, norm_real, arg_real_mul _ hr, Real.norm_of_nonneg hr.le,
    Real.log_mul hr.ne' hx, ofReal_add, add_assoc]

/--
theorem `log_mul_ofReal` / 定理 `log_mul_ofReal`

English:
theorem log_mul_ofReal
  given: (r : Real) (hr : 0 < r) (x : Complex) (hx : x != 0)
  proof: by rw [mul_comm, log_ofReal_mul hr hx]

中文:
定理 log_mul_of实数
  条件: (r : 实数) (hr : 0 < r) (x : 复形) (hx : x != 0)
  证明: by rw [mul_comm, log_ofReal_mul hr hx]

Depends on / 依赖: log_ofReal_mul, mul_comm
-/
theorem log_mul_ofReal (r : Real) (hr : 0 < r) (x : Complex) (hx : x != 0) :
    log (x * r) = Real.log r + log x := by rw [mul_comm, log_ofReal_mul hr hx]

/--
lemma `log_mul_eq_add_log_iff` / 引理 `log_mul_eq_add_log_iff`

English:
lemma log_mul_eq_add_log_iff
  given: {x y : Complex} (hx₀ : x != 0) (hy₀ : y != 0)
  proof: by
refine Complex.ext_iff.trans Iff.trans ?_ arg_mul_eq_add_arg_iff hx₀ hy₀
  simp_rw [add_re, add_im, log_re, log_im, norm_mul,
    Real.log_mul (norm_ne_zero_iff.mpr hx₀) (norm_ne_zero_iff.mpr hy₀), true_and]

alias ⟨_, log_mul⟩ := log_mul_eq_add_log_iff

@[simp]

中文:
引理 log_mul_eq_add_log_iff
  条件: {x y : 复形} (hx₀ : x != 0) (hy₀ : y != 0)
  证明: by
refine Complex.ext_iff.trans Iff.trans ?_ arg_mul_eq_add_arg_iff hx₀ hy₀
  simp_rw [add_re, add_im, log_re, log_im, norm_mul,
    Real.log_mul (norm_ne_zero_iff.mpr hx₀) (norm_ne_zero_iff.mpr hy₀), true_and]

alias ⟨_, log_mul⟩ := log_mul_eq_add_log_iff

@[simp]

Depends on / 依赖: Complex.ext_iff.trans, Iff.trans, Real.log_mul, add_im, add_re, arg_mul_eq_add_arg_iff, ext_iff, log_im, log_mul, log_re, norm_mul, norm_ne_zero_iff, norm_ne_zero_iff.mpr, simp_rw, true_and
-/
lemma log_mul_eq_add_log_iff {x y : Complex} (hx₀ : x != 0) (hy₀ : y != 0) :
    log (x * y) = log x + log y ↔ arg x + arg y in Set.Ioc (-π) π := by
refine Complex.ext_iff.trans Iff.trans ?_ arg_mul_eq_add_arg_iff hx₀ hy₀
  simp_rw [add_re, add_im, log_re, log_im, norm_mul,
    Real.log_mul (norm_ne_zero_iff.mpr hx₀) (norm_ne_zero_iff.mpr hy₀), true_and]

alias ⟨_, log_mul⟩ := log_mul_eq_add_log_iff

@[simp]
/--
theorem `log_zero` / 定理 `log_zero`

English:
theorem log_zero
  statement: log 0 = 0
  proof: by simp [log]

@[simp]

中文:
定理 log_zero
  结论: log 0 = 0
  证明: by simp [log]

@[simp]
-/
theorem log_zero : log 0 = 0 := by simp [log]

@[simp]
/--
theorem `log_one` / 定理 `log_one`

English:
theorem log_one
  statement: log 1 = 0
  proof: by simp [log]

中文:
定理 log_one
  结论: log 1 = 0
  证明: by simp [log]
-/
theorem log_one : log 1 = 0 := by simp [log]

/--
lemma `log_div_self` / 引理 `log_div_self`

English:
lemma log_div_self
  given: (x : Complex)
  statement: log (x / x) = 0
  proof: by simp [log]

中文:
引理 log_div_self
  条件: (x : 复形)
  结论: log (x / x) = 0
  证明: by simp [log]
-/
@[simp] lemma log_div_self (x : Complex) : log (x / x) = 0 := by simp [log]

/--
theorem `log_neg_one` / 定理 `log_neg_one`

English:
theorem log_neg_one
  statement: log (-1) = π * I
  proof: by simp [log]

中文:
定理 log_neg_one
  结论: log (-1) = π * I
  证明: by simp [log]
-/
theorem log_neg_one : log (-1) = π * I := by simp [log]

/--
theorem `log_I` / 定理 `log_I`

English:
theorem log_I
  statement: log I = π / 2 * I
  proof: by simp [log]

中文:
定理 log_I
  结论: log I = π / 2 * I
  证明: by simp [log]
-/
theorem log_I : log I = π / 2 * I := by simp [log]

/--
theorem `log_neg_I` / 定理 `log_neg_I`

English:
theorem log_neg_I
  statement: log (-I) = -(π / 2) * I
  proof: by simp [log]

中文:
定理 log_neg_I
  结论: log (-I) = -(π / 2) * I
  证明: by simp [log]
-/
theorem log_neg_I : log (-I) = -(π / 2) * I := by simp [log]

/--
theorem `log_conj_eq_ite` / 定理 `log_conj_eq_ite`

English:
theorem log_conj_eq_ite
  given: (x : Complex)
  statement: log (conj x) = if x.arg = π then log x else conj (log x)
  proof: by
  simp_rw [log, norm_conj, arg_conj, map_add, map_mul, conj_ofReal]
  split_ifs with hx
  · rw [hx]
  simp_rw [ofReal_neg, conj_I, mul_neg, neg_mul]

中文:
定理 log_conj_eq_ite
  条件: (x : 复形)
  结论: log (conj x) = if x.arg = π then log x else conj (log x)
  证明: by
  simp_rw [log, norm_conj, arg_conj, map_add, map_mul, conj_ofReal]
  split_ifs with hx
  · rw [hx]
  simp_rw [ofReal_neg, conj_I, mul_neg, neg_mul]

Depends on / 依赖: arg_conj, conj_I, conj_ofReal, map_add, map_mul, mul_neg, neg_mul, norm_conj, ofReal_neg, simp_rw, split_ifs
-/
theorem log_conj_eq_ite (x : Complex) : log (conj x) = if x.arg = π then log x else conj (log x) := by
  simp_rw [log, norm_conj, arg_conj, map_add, map_mul, conj_ofReal]
  split_ifs with hx
  · rw [hx]
  simp_rw [ofReal_neg, conj_I, mul_neg, neg_mul]

/--
theorem `log_conj` / 定理 `log_conj`

English:
theorem log_conj
  given: (x : Complex) (h : x.arg != π)
  statement: log (conj x) = conj (log x)
  proof: by
  rw [log_conj_eq_ite]; rw [if_neg h]

中文:
定理 log_conj
  条件: (x : 复形) (h : x.arg != π)
  结论: log (conj x) = conj (log x)
  证明: by
  rw [log_conj_eq_ite]; rw [if_neg h]

Depends on / 依赖: if_neg, log_conj_eq_ite
-/
theorem log_conj (x : Complex) (h : x.arg != π) : log (conj x) = conj (log x) := by
  rw [log_conj_eq_ite]; rw [if_neg h]

/--
theorem `log_inv_eq_ite` / 定理 `log_inv_eq_ite`

English:
theorem log_inv_eq_ite
  given: (x : Complex)
  statement: log x⁻¹ = if x.arg = π then -conj (log x) else -log x
  proof: by
  by_cases hx : x = 0
  · simp [hx]
  rw [inv_def]; rw [log_mul_ofReal]; rw [Real.log_inv]; rw [ofReal_neg]; rw [← sub_eq_neg_add]; rw [log_conj_eq_ite]
  · simp_rw [log, map_add, map_mul, conj_ofReal, conj_I, normSq_eq_norm_sq, Real.log_pow,
      Nat.cast_two, ofReal_mul, neg_add, mul_neg, neg_

中文:
定理 log_inv_eq_ite
  条件: (x : 复形)
  结论: log x⁻¹ = if x.arg = π then -conj (log x) else -log x
  证明: by
  by_cases hx : x = 0
  · simp [hx]
  rw [inv_def]; rw [log_mul_ofReal]; rw [Real.log_inv]; rw [ofReal_neg]; rw [← sub_eq_neg_add]; rw [log_conj_eq_ite]
  · simp_rw [log, map_add, map_mul, conj_ofReal, conj_I, normSq_eq_norm_sq, Real.log_pow,
      Nat.cast_two, ofReal_mul, neg_add, mul_neg, neg_

Depends on / 依赖: Complex.normSq_pos, Nat.cast_two, Real.log_inv, Real.log_pow, cast_two, conj_I, conj_ofReal, inv_def, inv_pos, log_conj_eq_ite, log_inv, log_mul_ofReal, log_pow, map_add, map_mul, map_ne_zero, mul_neg, neg_add, neg_neg, normSq_eq_norm_sq
-/
theorem log_inv_eq_ite (x : Complex) : log x⁻¹ = if x.arg = π then -conj (log x) else -log x := by
  by_cases hx : x = 0
  · simp [hx]
  rw [inv_def]; rw [log_mul_ofReal]; rw [Real.log_inv]; rw [ofReal_neg]; rw [← sub_eq_neg_add]; rw [log_conj_eq_ite]
  · simp_rw [log, map_add, map_mul, conj_ofReal, conj_I, normSq_eq_norm_sq, Real.log_pow,
      Nat.cast_two, ofReal_mul, neg_add, mul_neg, neg_neg]
    norm_num
    grind
  · rwa [inv_pos, Complex.normSq_pos]
  · rwa [map_ne_zero]

/--
theorem `log_inv` / 定理 `log_inv`

English:
theorem log_inv
  given: (x : Complex) (hx : x.arg != π)
  statement: log x⁻¹ = -log x
  proof: by rw [log_inv_eq_ite, if_neg hx]

中文:
定理 log_inv
  条件: (x : 复形) (hx : x.arg != π)
  结论: log x⁻¹ = -log x
  证明: by rw [log_inv_eq_ite, if_neg hx]

Depends on / 依赖: if_neg, log_inv_eq_ite
-/
theorem log_inv (x : Complex) (hx : x.arg != π) : log x⁻¹ = -log x := by rw [log_inv_eq_ite, if_neg hx]

/--
theorem `two_pi_I_ne_zero` / 定理 `two_pi_I_ne_zero`

English:
theorem two_pi_I_ne_zero
  statement: (2 * π * I : Complex) != 0
  proof: by simp [Real.pi_ne_zero, I_ne_zero]

中文:
定理 two_pi_I_ne_zero
  结论: (2 * π * I : 复形) != 0
  证明: by simp [Real.pi_ne_zero, I_ne_zero]

Depends on / 依赖: I_ne_zero, Real.pi_ne_zero, pi_ne_zero
-/
theorem two_pi_I_ne_zero : (2 * π * I : Complex) != 0 := by simp [Real.pi_ne_zero, I_ne_zero]

/--
theorem `exp_eq_one_iff` / 定理 `exp_eq_one_iff`

English:
theorem exp_eq_one_iff
  given: {x : Complex}
  statement: exp x = 1 ↔ exists n : Int, x = n * (2 * π * I)
  proof: by
  constructor
  · intro h
    rcases existsUnique_add_zsmul_mem_Ioc Real.two_pi_pos x.im (-π) with ⟨n, hn, -⟩
    use -n
    rw [Int.cast_neg]; rw [neg_mul]; rw [eq_neg_iff_add_eq_zero]
    have : (x + n * (2 * π * I)).im in Set.Ioc (-π) π := by simpa [two_mul, mul_add] using hn
    rw [← log_exp

中文:
定理 exp_eq_one_iff
  条件: {x : 复形}
  结论: exp x = 1 ↔ 存在 n : 整数, x = n * (2 * π * I)
  证明: by
  constructor
  · intro h
    rcases existsUnique_add_zsmul_mem_Ioc Real.two_pi_pos x.im (-π) with ⟨n, hn, -⟩
    use -n
    rw [Int.cast_neg]; rw [neg_mul]; rw [eq_neg_iff_add_eq_zero]
    have : (x + n * (2 * π * I)).im in Set.Ioc (-π) π := by simpa [two_mul, mul_add] using hn
    rw [← log_exp

Depends on / 依赖: Int.cast_neg, Real.two_pi_pos, Set.Ioc, cast_neg, eq.trans, eq_neg_iff_add_eq_zero, existsUnique_add_zsmul_mem_Ioc, exp_periodic, exp_periodic.int_mul, exp_zero, int_mul, log_exp, log_one, mul_add, neg_mul, two_mul, two_pi_pos, x.im
-/
theorem exp_eq_one_iff {x : Complex} : exp x = 1 ↔ exists n : Int, x = n * (2 * π * I) := by
  constructor
  · intro h
    rcases existsUnique_add_zsmul_mem_Ioc Real.two_pi_pos x.im (-π) with ⟨n, hn, -⟩
    use -n
    rw [Int.cast_neg]; rw [neg_mul]; rw [eq_neg_iff_add_eq_zero]
    have : (x + n * (2 * π * I)).im in Set.Ioc (-π) π := by simpa [two_mul, mul_add] using hn
    rw [← log_exp this.1 this.2]; rw [exp_periodic.int_mul n]; rw [h]; rw [log_one]
  · rintro ⟨n, rfl⟩
    exact (exp_periodic.int_mul n).eq.trans exp_zero

/--
theorem `exp_eq_one_iff_of_im_nonneg` / 定理 `exp_eq_one_iff_of_im_nonneg`

English:
theorem exp_eq_one_iff_of_im_nonneg
  given: {x : Complex} (hx : 0 <= x.im)
  proof: by
  rw [exp_eq_one_iff]
  refine ⟨fun ⟨n, hn⟩ => ?_, fun ⟨n, hn⟩ => ⟨n, by rw [hn]; norm_cast⟩⟩
  have : 0 <= n * (2 * π) := by simpa [hn] using hx
  lift n to Nat using by exact_mod_cast nonneg_of_mul_nonneg_left this (by positivity)
  exact ⟨n, hn⟩

中文:
定理 exp_eq_one_iff_of_im_nonneg
  条件: {x : 复形} (hx : 0 <= x.im)
  证明: by
  rw [exp_eq_one_iff]
  refine ⟨fun ⟨n, hn⟩ => ?_, fun ⟨n, hn⟩ => ⟨n, by rw [hn]; norm_cast⟩⟩
  have : 0 <= n * (2 * π) := by simpa [hn] using hx
  lift n to Nat using by exact_mod_cast nonneg_of_mul_nonneg_left this (by positivity)
  exact ⟨n, hn⟩

Depends on / 依赖: exp_eq_one_iff, nonneg_of_mul_nonneg_left
-/
theorem exp_eq_one_iff_of_im_nonneg {x : Complex} (hx : 0 <= x.im) :
    exp x = 1 ↔ exists n : Nat, x = n * (2 * π * I) := by
  rw [exp_eq_one_iff]
  refine ⟨fun ⟨n, hn⟩ => ?_, fun ⟨n, hn⟩ => ⟨n, by rw [hn]; norm_cast⟩⟩
  have : 0 <= n * (2 * π) := by simpa [hn] using hx
  lift n to Nat using by exact_mod_cast nonneg_of_mul_nonneg_left this (by positivity)
  exact ⟨n, hn⟩

/--
theorem `exp_two_pi_mul_I_mul_div_eq_one_iff` / 定理 `exp_two_pi_mul_I_mul_div_eq_one_iff`

English:
theorem exp_two_pi_mul_I_mul_div_eq_one_iff
  given: {k N : Nat} (hN : N != 0)
  proof: by
  rw [exp_eq_one_iff]
  conv in _ = _ => rw [← mul_comm (2 * π * I), mul_div_assoc, mul_right_inj' (by simp)]
  field_simp [Nat.cast_ne_zero.mpr hN]
  norm_cast
  simp [← dvd_def, Int.ofNat_dvd]

中文:
定理 exp_two_pi_mul_I_mul_div_eq_one_iff
  条件: {k N : 自然数} (hN : N != 0)
  证明: by
  rw [exp_eq_one_iff]
  conv in _ = _ => rw [← mul_comm (2 * π * I), mul_div_assoc, mul_right_inj' (by simp)]
  field_simp [Nat.cast_ne_zero.mpr hN]
  norm_cast
  simp [← dvd_def, Int.ofNat_dvd]

Depends on / 依赖: Int.ofNat_dvd, Nat.cast_ne_zero.mpr, cast_ne_zero, dvd_def, exp_eq_one_iff, mul_comm, mul_div_assoc, mul_right_inj, ofNat_dvd
-/
theorem exp_two_pi_mul_I_mul_div_eq_one_iff {k N : Nat} (hN : N != 0) :
    exp (2 * π * I * k / N) = 1 ↔ N ∣ k := by
  rw [exp_eq_one_iff]
  conv in _ = _ => rw [← mul_comm (2 * π * I), mul_div_assoc, mul_right_inj' (by simp)]
  field_simp [Nat.cast_ne_zero.mpr hN]
  norm_cast
  simp [← dvd_def, Int.ofNat_dvd]

/--
theorem `exp_eq_exp_iff_exp_sub_eq_one` / 定理 `exp_eq_exp_iff_exp_sub_eq_one`

English:
theorem exp_eq_exp_iff_exp_sub_eq_one
  given: {x y : Complex}
  statement: exp x = exp y ↔ exp (x - y) = 1
  proof: by
  rw [exp_sub]; rw [div_eq_one_iff_eq (exp_ne_zero _)]

中文:
定理 exp_eq_exp_iff_exp_sub_eq_one
  条件: {x y : 复形}
  结论: exp x = exp y ↔ exp (x - y) = 1
  证明: by
  rw [exp_sub]; rw [div_eq_one_iff_eq (exp_ne_zero _)]

Depends on / 依赖: div_eq_one_iff_eq, exp_ne_zero, exp_sub
-/
theorem exp_eq_exp_iff_exp_sub_eq_one {x y : Complex} : exp x = exp y ↔ exp (x - y) = 1 := by
  rw [exp_sub]; rw [div_eq_one_iff_eq (exp_ne_zero _)]

/--
theorem `exp_eq_exp_iff_exists_int` / 定理 `exp_eq_exp_iff_exists_int`

English:
theorem exp_eq_exp_iff_exists_int
  given: {x y : Complex}
  statement: exp x = exp y ↔ exists n : Int, x = y + n * (2 * π * I)
  proof: by
  simp only [exp_eq_exp_iff_exp_sub_eq_one, exp_eq_one_iff, sub_eq_iff_eq_add']

中文:
定理 exp_eq_exp_iff_存在_int
  条件: {x y : 复形}
  结论: exp x = exp y ↔ 存在 n : 整数, x = y + n * (2 * π * I)
  证明: by
  simp only [exp_eq_exp_iff_exp_sub_eq_one, exp_eq_one_iff, sub_eq_iff_eq_add']

Depends on / 依赖: exp_eq_exp_iff_exp_sub_eq_one, exp_eq_one_iff, sub_eq_iff_eq_add
-/
theorem exp_eq_exp_iff_exists_int {x y : Complex} : exp x = exp y ↔ exists n : Int, x = y + n * (2 * π * I) := by
  simp only [exp_eq_exp_iff_exp_sub_eq_one, exp_eq_one_iff, sub_eq_iff_eq_add']

/--
lemma `re_eq_re_of_cexp_eq_cexp` / 引理 `re_eq_re_of_cexp_eq_cexp`

English:
lemma re_eq_re_of_cexp_eq_cexp
  given: {x y : Complex} (h : cexp x = cexp y)
  proof: by
  obtain ⟨n, hn⟩ := exp_eq_exp_iff_exists_int.1 h
  simp [hn]

中文:
引理 re_eq_re_of_cexp_eq_cexp
  条件: {x y : 复形} (h : cexp x = cexp y)
  证明: by
  obtain ⟨n, hn⟩ := exp_eq_exp_iff_exists_int.1 h
  simp [hn]
-/
@[grind .] lemma re_eq_re_of_cexp_eq_cexp {x y : Complex} (h : cexp x = cexp y) :
    x.re = y.re := by
  obtain ⟨n, hn⟩ := exp_eq_exp_iff_exists_int.1 h
  simp [hn]

/--
theorem `log_exp_exists` / 定理 `log_exp_exists`

English:
theorem log_exp_exists
  given: (z : Complex)
  proof: by
  rw [← exp_eq_exp_iff_exists_int]; rw [exp_log]
  exact exp_ne_zero z

@[simp]

中文:
定理 log_exp_存在
  条件: (z : 复形)
  证明: by
  rw [← exp_eq_exp_iff_exists_int]; rw [exp_log]
  exact exp_ne_zero z

@[simp]

Depends on / 依赖: exp_eq_exp_iff_exists_int, exp_log, exp_ne_zero
-/
theorem log_exp_exists (z : Complex) :
    exists n : Int, log (exp z) = z + n * (2 * π * I) := by
  rw [← exp_eq_exp_iff_exists_int]; rw [exp_log]
  exact exp_ne_zero z

@[simp]
/--
theorem `countable_preimage_exp` / 定理 `countable_preimage_exp`

English:
theorem countable_preimage_exp
  given: {s : Set Complex}
  statement: (exp ⁻¹' s).Countable ↔ s.Countable
  proof: by
  refine ⟨fun hs => ?_, fun hs => ?_⟩
  · refine ((hs.image exp).insert 0).mono ?_
    rw [Set.image_preimage_eq_inter_range]; rw [range_exp]; rw [← Set.sdiff_eq]; rw [← Set.union_singleton]; rw [Set.sdiff_union_self]
    exact Set.subset_union_left
  · rw [← Set.biUnion_preimage_singleton]
    r

中文:
定理 countable_preimage_exp
  条件: {s : 集合 复形}
  结论: (exp ⁻¹' s).可数 ↔ s.可数
  证明: by
  refine ⟨fun hs => ?_, fun hs => ?_⟩
  · refine ((hs.image exp).insert 0).mono ?_
    rw [Set.image_preimage_eq_inter_range]; rw [range_exp]; rw [← Set.sdiff_eq]; rw [← Set.union_singleton]; rw [Set.sdiff_union_self]
    exact Set.subset_union_left
  · rw [← Set.biUnion_preimage_singleton]
    r

Depends on / 依赖: Set.biUnion_preimage_singleton, Set.countable_iUnion, Set.image_preimage_eq_inter_range, Set.mem_singleton_iff, Set.ofPred_exists, Set.preimage, Set.sdiff_eq, Set.sdiff_union_self, Set.subset_union_left, Set.union_singleton, biUnion, biUnion_preimage_singleton, countable_iUnion, exp_eq_exp_iff_exists_int, hs.biUnion, hs.image, image_preimage_eq_inter_range, insert, mem_singleton_iff, ofPred_exists
-/
theorem countable_preimage_exp {s : Set Complex} : (exp ⁻¹' s).Countable ↔ s.Countable := by
  refine ⟨fun hs => ?_, fun hs => ?_⟩
  · refine ((hs.image exp).insert 0).mono ?_
    rw [Set.image_preimage_eq_inter_range]; rw [range_exp]; rw [← Set.sdiff_eq]; rw [← Set.union_singleton]; rw [Set.sdiff_union_self]
    exact Set.subset_union_left
  · rw [← Set.biUnion_preimage_singleton]
    refine hs.biUnion fun z hz => ?_
    by_cases! h : exists w, exp w = z
    · rcases h with ⟨w, rfl⟩
      simp only [Set.preimage, Set.mem_singleton_iff, exp_eq_exp_iff_exists_int, Set.ofPred_exists]
      exact Set.countable_iUnion fun m => Set.countable_singleton _
    · simp [Set.preimage, h]

alias ⟨_, _root_.Set.Countable.preimage_cexp⟩ := countable_preimage_exp

/--
theorem `tendsto_log_nhdsWithin_im_neg_of_re_neg_of_im_zero` / 定理 `tendsto_log_nhdsWithin_im_neg_of_re_neg_of_im_zero`

English:
theorem tendsto_log_nhdsWithin_im_neg_of_re_neg_of_im_zero
  statement: {z : Complex} (hre : z.re < 0)
  proof: by
  convert!
    (continuous_ofReal.continuousAt.comp_continuousWithinAt
          (continuous_norm.continuousWithinAt.log _)).tendsto.add
      (((continuous_ofReal.tendsto _).comp <|
            tendsto_arg_nhdsWithin_im_neg_of_re_neg_of_im_zero hre him).mul
        tendsto_const_nhds) using 1
  

中文:
定理 tendsto_log_nhdsWithin_im_neg_of_re_neg_of_im_zero
  结论: {z : 复形} (hre : z.re < 0)
  证明: by
  convert!
    (continuous_ofReal.continuousAt.comp_continuousWithinAt
          (continuous_norm.continuousWithinAt.log _)).tendsto.add
      (((continuous_ofReal.tendsto _).comp <|
            tendsto_arg_nhdsWithin_im_neg_of_re_neg_of_im_zero hre him).mul
        tendsto_const_nhds) using 1
  

Depends on / 依赖: comp_continuousWithinAt, continuousAt, continuousWithinAt, continuous_norm, continuous_norm.continuousWithinAt.log, continuous_ofReal, continuous_ofReal.continuousAt.comp_continuousWithinAt, continuous_ofReal.tendsto, convert, hre.ne, sub_eq_add_neg, tendsto, tendsto.add, tendsto_arg_nhdsWithin_im_neg_of_re_neg_of_im_zero, tendsto_const_nhds
-/
theorem tendsto_log_nhdsWithin_im_neg_of_re_neg_of_im_zero {z : Complex} (hre : z.re < 0)
    (him : z.im = 0) : Tendsto log (𝓝[{ z : Complex | z.im < 0 }] z) (𝓝 <| Real.log ‖z‖ - π * I) := by
  convert!
    (continuous_ofReal.continuousAt.comp_continuousWithinAt
          (continuous_norm.continuousWithinAt.log _)).tendsto.add
      (((continuous_ofReal.tendsto _).comp <|
            tendsto_arg_nhdsWithin_im_neg_of_re_neg_of_im_zero hre him).mul
        tendsto_const_nhds) using 1
  · simp [sub_eq_add_neg]
  · lift z to Real using him
    simpa using hre.ne

/--
theorem `continuousWithinAt_log_of_re_neg_of_im_zero` / 定理 `continuousWithinAt_log_of_re_neg_of_im_zero`

English:
theorem continuousWithinAt_log_of_re_neg_of_im_zero
  given: {z : Complex} (hre : z.re < 0) (him : z.im = 0)
  proof: by
  convert!
    (continuous_ofReal.continuousAt.comp_continuousWithinAt
          (continuous_norm.continuousWithinAt.log _)).tendsto.add
      ((continuous_ofReal.continuousAt.comp_continuousWithinAt <|
            continuousWithinAt_arg_of_re_neg_of_im_zero hre him).mul
        tendsto_const_nhd

中文:
定理 continuousWithinAt_log_of_re_neg_of_im_zero
  条件: {z : 复形} (hre : z.re < 0) (him : z.im = 0)
  证明: by
  convert!
    (continuous_ofReal.continuousAt.comp_continuousWithinAt
          (continuous_norm.continuousWithinAt.log _)).tendsto.add
      ((continuous_ofReal.continuousAt.comp_continuousWithinAt <|
            continuousWithinAt_arg_of_re_neg_of_im_zero hre him).mul
        tendsto_const_nhd

Depends on / 依赖: comp_continuousWithinAt, continuousAt, continuousWithinAt, continuousWithinAt_arg_of_re_neg_of_im_zero, continuous_norm, continuous_norm.continuousWithinAt.log, continuous_ofReal, continuous_ofReal.continuousAt.comp_continuousWithinAt, convert, hre.ne, tendsto, tendsto.add, tendsto_const_nhds
-/
theorem continuousWithinAt_log_of_re_neg_of_im_zero {z : Complex} (hre : z.re < 0) (him : z.im = 0) :
    ContinuousWithinAt log { z : Complex | 0 <= z.im } z := by
  convert!
    (continuous_ofReal.continuousAt.comp_continuousWithinAt
          (continuous_norm.continuousWithinAt.log _)).tendsto.add
      ((continuous_ofReal.continuousAt.comp_continuousWithinAt <|
            continuousWithinAt_arg_of_re_neg_of_im_zero hre him).mul
        tendsto_const_nhds) using 1
  lift z to Real using him
  simpa using hre.ne

/--
theorem `tendsto_log_nhdsWithin_im_nonneg_of_re_neg_of_im_zero` / 定理 `tendsto_log_nhdsWithin_im_nonneg_of_re_neg_of_im_zero`

English:
theorem tendsto_log_nhdsWithin_im_nonneg_of_re_neg_of_im_zero
  statement: {z : Complex} (hre : z.re < 0)
  proof: by
  simpa only [log, arg_eq_pi_iff.2 ⟨hre, him⟩] using
    (continuousWithinAt_log_of_re_neg_of_im_zero hre him).tendsto

@[simp]

中文:
定理 tendsto_log_nhdsWithin_im_nonneg_of_re_neg_of_im_zero
  结论: {z : 复形} (hre : z.re < 0)
  证明: by
  simpa only [log, arg_eq_pi_iff.2 ⟨hre, him⟩] using
    (continuousWithinAt_log_of_re_neg_of_im_zero hre him).tendsto

@[simp]

Depends on / 依赖: arg_eq_pi_iff, continuousWithinAt_log_of_re_neg_of_im_zero, tendsto
-/
theorem tendsto_log_nhdsWithin_im_nonneg_of_re_neg_of_im_zero {z : Complex} (hre : z.re < 0)
    (him : z.im = 0) : Tendsto log (𝓝[{ z : Complex | 0 <= z.im }] z) (𝓝 <| Real.log ‖z‖ + π * I) := by
  simpa only [log, arg_eq_pi_iff.2 ⟨hre, him⟩] using
    (continuousWithinAt_log_of_re_neg_of_im_zero hre him).tendsto

@[simp]
/--
theorem `map_exp_comap_re_atBot` / 定理 `map_exp_comap_re_atBot`

English:
theorem map_exp_comap_re_atBot
  statement: map exp (comap re atBot) = 𝓝[!=] 0
  proof: by
  rw [← comap_exp_nhds_zero]; rw [map_comap]; rw [range_exp]; rw [nhdsWithin]

@[simp]

中文:
定理 map_exp_comap_re_atBot
  结论: map exp (comap re atBot) = 𝓝[!=] 0
  证明: by
  rw [← comap_exp_nhds_zero]; rw [map_comap]; rw [range_exp]; rw [nhdsWithin]

@[simp]

Depends on / 依赖: comap_exp_nhds_zero, map_comap, nhdsWithin, range_exp
-/
theorem map_exp_comap_re_atBot : map exp (comap re atBot) = 𝓝[!=] 0 := by
  rw [← comap_exp_nhds_zero]; rw [map_comap]; rw [range_exp]; rw [nhdsWithin]

@[simp]
/--
theorem `map_exp_comap_re_atTop` / 定理 `map_exp_comap_re_atTop`

English:
theorem map_exp_comap_re_atTop
  statement: map exp (comap re atTop) = cobounded Complex
  proof: by
  rw [← comap_exp_cobounded]; rw [map_comap]; rw [range_exp]; rw [inf_eq_left]; rw [le_principal_iff]
  exact eventually_ne_cobounded _

中文:
定理 map_exp_comap_re_atTop
  结论: map exp (comap re atTop) = cobounded 复形
  证明: by
  rw [← comap_exp_cobounded]; rw [map_comap]; rw [range_exp]; rw [inf_eq_left]; rw [le_principal_iff]
  exact eventually_ne_cobounded _

Depends on / 依赖: comap_exp_cobounded, eventually_ne_cobounded, inf_eq_left, le_principal_iff, map_comap, range_exp
-/
theorem map_exp_comap_re_atTop : map exp (comap re atTop) = cobounded Complex := by
  rw [← comap_exp_cobounded]; rw [map_comap]; rw [range_exp]; rw [inf_eq_left]; rw [le_principal_iff]
  exact eventually_ne_cobounded _

end Complex

section LogDeriv

open Complex Filter

open Topology

variable {α : Type*}

/--
theorem `continuousAt_clog` / 定理 `continuousAt_clog`

English:
theorem continuousAt_clog
  given: {x : Complex} (h : x in slitPlane)
  statement: ContinuousAt log x
  proof: by
  refine ContinuousAt.add ?_ ?_
  · refine continuous_ofReal.continuousAt.comp ?_
    refine (Real.continuousAt_log ?_).comp continuous_norm.continuousAt
exact norm_ne_zero_iff.mpr slitPlane_ne_zero h
  · have h_cont_mul : Continuous fun x : Complex => x * I := by fun_prop
    refine h_cont_mul.c

中文:
定理 continuousAt_clog
  条件: {x : 复形} (h : x in slitPlane)
  结论: ContinuousAt log x
  证明: by
  refine ContinuousAt.add ?_ ?_
  · refine continuous_ofReal.continuousAt.comp ?_
    refine (Real.continuousAt_log ?_).comp continuous_norm.continuousAt
exact norm_ne_zero_iff.mpr slitPlane_ne_zero h
  · have h_cont_mul : Continuous fun x : Complex => x * I := by fun_prop
    refine h_cont_mul.c

Depends on / 依赖: Continuous, ContinuousAt, ContinuousAt.add, Real.continuousAt_log, continuousAt, continuousAt_arg, continuousAt_log, continuous_norm, continuous_norm.continuousAt, continuous_ofReal, continuous_ofReal.continuousAt.comp, fun_prop, h_cont_mul, h_cont_mul.continuousAt.comp, norm_ne_zero_iff, norm_ne_zero_iff.mpr, slitPlane_ne_zero
-/
theorem continuousAt_clog {x : Complex} (h : x in slitPlane) : ContinuousAt log x := by
  refine ContinuousAt.add ?_ ?_
  · refine continuous_ofReal.continuousAt.comp ?_
    refine (Real.continuousAt_log ?_).comp continuous_norm.continuousAt
exact norm_ne_zero_iff.mpr slitPlane_ne_zero h
  · have h_cont_mul : Continuous fun x : Complex => x * I := by fun_prop
    refine h_cont_mul.continuousAt.comp (continuous_ofReal.continuousAt.comp ?_)
    exact continuousAt_arg h

/--
theorem `_root_.Filter.Tendsto.clog` / 定理 `_root_.Filter.Tendsto.clog`

English:
theorem _root_.Filter.Tendsto.clog
  statement: {l : Filter α} {f : α -> Complex} {x : Complex} (h : Tendsto f l (𝓝 x))
  proof: (continuousAt_clog hx).tendsto.comp h

中文:
定理 _root_.滤子.收敛.clog
  结论: {l : 滤子 α} {f : α -> 复形} {x : 复形} (h : 收敛 f l (𝓝 x))
  证明: (continuousAt_clog hx).tendsto.comp h

Depends on / 依赖: AB4OfSize, HasCoproducts, continuousAt_clog, tendsto, tendsto.comp
-/
theorem _root_.Filter.Tendsto.clog {l : Filter α} {f : α -> Complex} {x : Complex} (h : Tendsto f l (𝓝 x))
    (hx : x in slitPlane) : Tendsto (fun t => log (f t)) l (𝓝 <| log x) :=
  (continuousAt_clog hx).tendsto.comp h

variable [TopologicalSpace α]

nonrec
/--
theorem `_root_.ContinuousAt.clog` / 定理 `_root_.ContinuousAt.clog`

English:
theorem _root_.ContinuousAt.clog
  statement: {f : α -> Complex} {x : α} (h₁ : ContinuousAt f x)
  proof: h₁.clog h₂

nonrec

中文:
定理 _root_.ContinuousAt.clog
  结论: {f : α -> 复形} {x : α} (h₁ : ContinuousAt f x)
  证明: h₁.clog h₂

nonrec
-/
theorem _root_.ContinuousAt.clog {f : α -> Complex} {x : α} (h₁ : ContinuousAt f x)
    (h₂ : f x in slitPlane) : ContinuousAt (fun t => log (f t)) x :=
  h₁.clog h₂

nonrec
/--
theorem `_root_.ContinuousWithinAt.clog` / 定理 `_root_.ContinuousWithinAt.clog`

English:
theorem _root_.ContinuousWithinAt.clog
  statement: {f : α -> Complex} {s : Set α} {x : α}
  proof: h₁.clog h₂

nonrec

中文:
定理 _root_.ContinuousWithinAt.clog
  结论: {f : α -> 复形} {s : 集合 α} {x : α}
  证明: h₁.clog h₂

nonrec
-/
theorem _root_.ContinuousWithinAt.clog {f : α -> Complex} {s : Set α} {x : α}
    (h₁ : ContinuousWithinAt f s x) (h₂ : f x in slitPlane) :
    ContinuousWithinAt (fun t => log (f t)) s x :=
  h₁.clog h₂

nonrec
/--
theorem `_root_.ContinuousOn.clog` / 定理 `_root_.ContinuousOn.clog`

English:
theorem _root_.ContinuousOn.clog
  statement: {f : α -> Complex} {s : Set α} (h₁ : ContinuousOn f s)
  proof: fun x hx =>
  (h₁ x hx).clog (h₂ x hx)

nonrec

中文:
定理 _root_.ContinuousOn.clog
  结论: {f : α -> 复形} {s : 集合 α} (h₁ : ContinuousOn f s)
  证明: fun x hx =>
  (h₁ x hx).clog (h₂ x hx)

nonrec

Depends on / 依赖: AB4StarOfSize, HasProducts
-/
theorem _root_.ContinuousOn.clog {f : α -> Complex} {s : Set α} (h₁ : ContinuousOn f s)
    (h₂ : forall x in s, f x in slitPlane) : ContinuousOn (fun t => log (f t)) s := fun x hx =>
  (h₁ x hx).clog (h₂ x hx)

nonrec
/--
theorem `_root_.Continuous.clog` / 定理 `_root_.Continuous.clog`

English:
theorem _root_.Continuous.clog
  statement: {f : α -> Complex} (h₁ : Continuous f)
  proof: continuous_iff_continuousAt.2 fun x => h₁.continuousAt.clog (h₂ x)

中文:
定理 _root_.连续.clog
  结论: {f : α -> 复形} (h₁ : 连续 f)
  证明: continuous_iff_continuousAt.2 fun x => h₁.continuousAt.clog (h₂ x)

Depends on / 依赖: AB4OfSize, CountableAB4, HasCoproducts, continuousAt, continuousAt.clog, continuous_iff_continuousAt
-/
theorem _root_.Continuous.clog {f : α -> Complex} (h₁ : Continuous f)
    (h₂ : forall x, f x in slitPlane) : Continuous fun t => log (f t) :=
  continuous_iff_continuousAt.2 fun x => h₁.continuousAt.clog (h₂ x)

end LogDeriv

namespace Complex

open Set
open scoped Real

/--
Definition of `expOpenPartialHomeomorph` / `expOpenPartialHomeomorph` 的定义

English:
definition expOpenPartialHomeomorph
  signature: : OpenPartialHomeomorph Complex Complex where
  body: exp
  invFun := log
  source := {z : Complex | z.im in Ioo (-π) π}
  target := slitPlane
  map_source' := by
    rintro ⟨x, y⟩ ⟨h₁ : -π < y, h₂ : y < π⟩
    simp [exp_mem_slitPlane, h₂.ne,
      (toIocMod_eq_self Real.two_pi_pos).mpr ⟨h₁, by simpa [two_mul] using h₂.le⟩]
  map_target' z h := by
    

中文:
定义 expOpenPartialHomeomorph
  签名: : OpenPartialHomeomorph 复形 复形 where
  定义体: exp
  invFun := log
  source := {z : Complex | z.im in Ioo (-π) π}
  target := slitPlane
  map_source' := by
    rintro ⟨x, y⟩ ⟨h₁ : -π < y, h₂ : y < π⟩
    simp [exp_mem_slitPlane, h₂.ne,
      (toIocMod_eq_self Real.two_pi_pos).mpr ⟨h₁, by simpa [two_mul] using h₂.le⟩]
  map_target' z h := by
    

Depends on / 依赖: AB4StarOfSize, CountableAB4Star, HasProducts
-/
noncomputable def expOpenPartialHomeomorph : OpenPartialHomeomorph Complex Complex where
  toFun := exp
  invFun := log
  source := {z : Complex | z.im in Ioo (-π) π}
  target := slitPlane
  map_source' := by
    rintro ⟨x, y⟩ ⟨h₁ : -π < y, h₂ : y < π⟩
    simp [exp_mem_slitPlane, h₂.ne,
      (toIocMod_eq_self Real.two_pi_pos).mpr ⟨h₁, by simpa [two_mul] using h₂.le⟩]
  map_target' z h := by
    simp only [mem_ofPred, log_im, mem_Ioo, neg_pi_lt_arg, arg_lt_pi_iff, true_and]
    exact h.imp_left le_of_lt
  left_inv' _x hx := log_exp hx.1 (le_of_lt hx.2)
right_inv' _x hx := exp_log slitPlane_ne_zero hx
  open_source := isOpen_Ioo.preimage continuous_im
  open_target := isOpen_slitPlane
  continuousOn_toFun := by fun_prop
  continuousOn_invFun := continuousOn_id.clog fun _ => id

@[deprecated (since := "2026-01-13")]
alias expPartialHomeomorph := expOpenPartialHomeomorph

end Complex
