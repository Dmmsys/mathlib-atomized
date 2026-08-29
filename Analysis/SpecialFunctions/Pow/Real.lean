/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Abhimanyu Pallavi Sudhir, Jean Lo, Calle Sönne, Sébastien Gouëzel,
  Rémy Degenne, David Loeffler
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public meta import Mathlib.Data.Nat.NthRoot.Defs
public import Qq

/-! # Power function on `ℝ`

We construct the power functions `x ^ y`, where `x` and `y` are real numbers.
-/

@[expose] public section


noncomputable section

open Real ComplexConjugate Finset Set

/-
## Definitions
-/
namespace Real
variable {x y z : Real}

/--
Definition of `rpow` / `rpow` 的定义

English:
definition rpow
  signature: (x y : Real)
  body: ((x : Complex) ^ (y : Complex)).re

中文:
定义 rpow
  签名: (x y : 实数)
  定义体: ((x : Complex) ^ (y : Complex)).re
-/
noncomputable def rpow (x y : Real) :=
  ((x : Complex) ^ (y : Complex)).re

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Pow Real Real
  body: ⟨rpow⟩

@[simp]

中文:
实例 :
  签名: 幂 实数 实数
  定义体: ⟨rpow⟩

@[simp]
-/
noncomputable instance : Pow Real Real := ⟨rpow⟩

@[simp]
/--
theorem `rpow_eq_pow` / 定理 `rpow_eq_pow`

English:
theorem rpow_eq_pow
  given: (x y : Real)
  statement: rpow x y = x ^ y
  proof: rfl

中文:
定理 rpow_eq_pow
  条件: (x y : 实数)
  结论: rpow x y = x ^ y
  证明: rfl
-/
theorem rpow_eq_pow (x y : Real) : rpow x y = x ^ y := rfl

/--
theorem `rpow_def` / 定理 `rpow_def`

English:
theorem rpow_def
  given: (x y : Real)
  statement: x ^ y = ((x : Complex) ^ (y : Complex)).re
  proof: rfl

中文:
定理 rpow_def
  条件: (x y : 实数)
  结论: x ^ y = ((x : 复形) ^ (y : 复形)).re
  证明: rfl
-/
theorem rpow_def (x y : Real) : x ^ y = ((x : Complex) ^ (y : Complex)).re := rfl

/--
theorem `rpow_def_of_nonneg` / 定理 `rpow_def_of_nonneg`

English:
theorem rpow_def_of_nonneg
  given: {x : Real} (hx : 0 <= x) (y : Real)
  proof: by
  simp only [rpow_def, Complex.cpow_def]; split_ifs <;>
  simp_all [(Complex.ofReal_log hx).symm, -Complex.ofReal_mul,
      (Complex.ofReal_mul _ _).symm, Complex.exp_ofReal_re, Complex.ofReal_eq_zero]

中文:
定理 rpow_def_of_nonneg
  条件: {x : 实数} (hx : 0 <= x) (y : 实数)
  证明: by
  simp only [rpow_def, Complex.cpow_def]; split_ifs <;>
  simp_all [(Complex.ofReal_log hx).symm, -Complex.ofReal_mul,
      (Complex.ofReal_mul _ _).symm, Complex.exp_ofReal_re, Complex.ofReal_eq_zero]

Depends on / 依赖: Complex.cpow_def, Complex.exp_ofReal_re, Complex.ofReal_eq_zero, Complex.ofReal_log, Complex.ofReal_mul, cpow_def, exp_ofReal_re, ofReal_eq_zero, ofReal_log, ofReal_mul, rpow_def, split_ifs
-/
theorem rpow_def_of_nonneg {x : Real} (hx : 0 <= x) (y : Real) :
    x ^ y = if x = 0 then if y = 0 then 1 else 0 else exp (log x * y) := by
  simp only [rpow_def, Complex.cpow_def]; split_ifs <;>
  simp_all [(Complex.ofReal_log hx).symm, -Complex.ofReal_mul,
      (Complex.ofReal_mul _ _).symm, Complex.exp_ofReal_re, Complex.ofReal_eq_zero]

/--
theorem `rpow_def_of_pos` / 定理 `rpow_def_of_pos`

English:
theorem rpow_def_of_pos
  given: {x : Real} (hx : 0 < x) (y : Real)
  statement: x ^ y = exp (log x * y)
  proof: by
  rw [rpow_def_of_nonneg (le_of_lt hx)]; rw [if_neg (ne_of_gt hx)]

中文:
定理 rpow_def_of_pos
  条件: {x : 实数} (hx : 0 < x) (y : 实数)
  结论: x ^ y = exp (log x * y)
  证明: by
  rw [rpow_def_of_nonneg (le_of_lt hx)]; rw [if_neg (ne_of_gt hx)]

Depends on / 依赖: if_neg, le_of_lt, ne_of_gt, rpow_def_of_nonneg
-/
theorem rpow_def_of_pos {x : Real} (hx : 0 < x) (y : Real) : x ^ y = exp (log x * y) := by
  rw [rpow_def_of_nonneg (le_of_lt hx)]; rw [if_neg (ne_of_gt hx)]

/--
theorem `exp_mul` / 定理 `exp_mul`

English:
theorem exp_mul
  given: (x y : Real)
  statement: exp (x * y) = exp x ^ y
  proof: by rw [rpow_def_of_pos (exp_pos _), log_exp]

@[simp, norm_cast]

中文:
定理 exp_mul
  条件: (x y : 实数)
  结论: exp (x * y) = exp x ^ y
  证明: by rw [rpow_def_of_pos (exp_pos _), log_exp]

@[simp, norm_cast]

Depends on / 依赖: exp_pos, log_exp, rpow_def_of_pos
-/
theorem exp_mul (x y : Real) : exp (x * y) = exp x ^ y := by rw [rpow_def_of_pos (exp_pos _), log_exp]

@[simp, norm_cast]
/--
theorem `rpow_intCast` / 定理 `rpow_intCast`

English:
theorem rpow_intCast
  given: (x : Real) (n : Int)
  statement: x ^ (n : Real) = x ^ n
  proof: by
  simp only [rpow_def, ← Complex.ofReal_zpow, Complex.cpow_intCast, Complex.ofReal_intCast,
    Complex.ofReal_re]

@[simp, norm_cast]

中文:
定理 rpow_intCast
  条件: (x : 实数) (n : 整数)
  结论: x ^ (n : 实数) = x ^ n
  证明: by
  simp only [rpow_def, ← Complex.ofReal_zpow, Complex.cpow_intCast, Complex.ofReal_intCast,
    Complex.ofReal_re]

@[simp, norm_cast]

Depends on / 依赖: Complex.cpow_intCast, Complex.ofReal_intCast, Complex.ofReal_re, Complex.ofReal_zpow, cpow_intCast, ofReal_intCast, ofReal_re, ofReal_zpow, rpow_def
-/
theorem rpow_intCast (x : Real) (n : Int) : x ^ (n : Real) = x ^ n := by
  simp only [rpow_def, ← Complex.ofReal_zpow, Complex.cpow_intCast, Complex.ofReal_intCast,
    Complex.ofReal_re]

@[simp, norm_cast]
/--
theorem `rpow_natCast` / 定理 `rpow_natCast`

English:
theorem rpow_natCast
  given: (x : Real) (n : Nat)
  statement: x ^ (n : Real) = x ^ n
  proof: by simpa using rpow_intCast x n

@[simp, norm_cast]

中文:
定理 rpow_natCast
  条件: (x : 实数) (n : 自然数)
  结论: x ^ (n : 实数) = x ^ n
  证明: by simpa using rpow_intCast x n

@[simp, norm_cast]

Depends on / 依赖: rpow_intCast
-/
theorem rpow_natCast (x : Real) (n : Nat) : x ^ (n : Real) = x ^ n := by simpa using rpow_intCast x n

@[simp, norm_cast]
/--
theorem `rpow_neg_natCast` / 定理 `rpow_neg_natCast`

English:
theorem rpow_neg_natCast
  given: (x : Real) (n : Nat)
  statement: x ^ (-n : Real) = x ^ (-n : Int)
  proof: by
  rw [← rpow_intCast]; rw [Int.cast_neg]; rw [Int.cast_natCast]

@[simp]

中文:
定理 rpow_neg_natCast
  条件: (x : 实数) (n : 自然数)
  结论: x ^ (-n : 实数) = x ^ (-n : 整数)
  证明: by
  rw [← rpow_intCast]; rw [Int.cast_neg]; rw [Int.cast_natCast]

@[simp]

Depends on / 依赖: Int.cast_natCast, Int.cast_neg, cast_natCast, cast_neg, rpow_intCast
-/
theorem rpow_neg_natCast (x : Real) (n : Nat) : x ^ (-n : Real) = x ^ (-n : Int) := by
  rw [← rpow_intCast]; rw [Int.cast_neg]; rw [Int.cast_natCast]

@[simp]
/--
lemma `rpow_ofNat` / 引理 `rpow_ofNat`

English:
lemma rpow_ofNat
  given: (x : Real) (n : Nat) [n.AtLeastTwo]
  proof: rpow_natCast x n

@[simp]

中文:
引理 rpow_of自然数
  条件: (x : 实数) (n : 自然数) [n.AtLeastTwo]
  证明: rpow_natCast x n

@[simp]

Depends on / 依赖: rpow_natCast
-/
lemma rpow_ofNat (x : Real) (n : Nat) [n.AtLeastTwo] :
    x ^ (ofNat(n) : Real) = x ^ (ofNat(n) : Nat) :=
  rpow_natCast x n

@[simp]
/--
theorem `rpow_neg_ofNat` / 定理 `rpow_neg_ofNat`

English:
theorem rpow_neg_ofNat
  given: (x : Real) (n : Nat) [n.AtLeastTwo]
  statement: x ^ (-ofNat(n) : Real) = x ^ (-ofNat(n) : Int)
  proof: rpow_neg_natCast _ _

@[simp]

中文:
定理 rpow_neg_of自然数
  条件: (x : 实数) (n : 自然数) [n.AtLeastTwo]
  结论: x ^ (-of自然数(n) : 实数) = x ^ (-of自然数(n) : 整数)
  证明: rpow_neg_natCast _ _

@[simp]

Depends on / 依赖: rpow_neg_natCast
-/
theorem rpow_neg_ofNat (x : Real) (n : Nat) [n.AtLeastTwo] : x ^ (-ofNat(n) : Real) = x ^ (-ofNat(n) : Int) :=
  rpow_neg_natCast _ _

@[simp]
/--
theorem `exp_one_rpow` / 定理 `exp_one_rpow`

English:
theorem exp_one_rpow
  given: (x : Real)
  statement: exp 1 ^ x = exp x
  proof: by rw [← exp_mul, one_mul]

中文:
定理 exp_one_rpow
  条件: (x : 实数)
  结论: exp 1 ^ x = exp x
  证明: by rw [← exp_mul, one_mul]

Depends on / 依赖: exp_mul, one_mul
-/
theorem exp_one_rpow (x : Real) : exp 1 ^ x = exp x := by rw [← exp_mul, one_mul]

/--
lemma `exp_one_pow` / 引理 `exp_one_pow`

English:
lemma exp_one_pow
  given: (n : Nat)
  statement: exp 1 ^ n = exp n
  proof: by rw [← rpow_natCast, exp_one_rpow]

中文:
引理 exp_one_pow
  条件: (n : 自然数)
  结论: exp 1 ^ n = exp n
  证明: by rw [← rpow_natCast, exp_one_rpow]
-/
@[simp] lemma exp_one_pow (n : Nat) : exp 1 ^ n = exp n := by rw [← rpow_natCast, exp_one_rpow]

/--
theorem `rpow_eq_zero_iff_of_nonneg` / 定理 `rpow_eq_zero_iff_of_nonneg`

English:
theorem rpow_eq_zero_iff_of_nonneg
  given: (hx : 0 <= x)
  statement: x ^ y = 0 ↔ x = 0 ∧ y != 0
  proof: by
  simp only [rpow_def_of_nonneg hx]
  split_ifs <;> simp [*, exp_ne_zero]

@[simp]

中文:
定理 rpow_eq_zero_iff_of_nonneg
  条件: (hx : 0 <= x)
  结论: x ^ y = 0 ↔ x = 0 ∧ y != 0
  证明: by
  simp only [rpow_def_of_nonneg hx]
  split_ifs <;> simp [*, exp_ne_zero]

@[simp]

Depends on / 依赖: exp_ne_zero, rpow_def_of_nonneg, split_ifs
-/
theorem rpow_eq_zero_iff_of_nonneg (hx : 0 <= x) : x ^ y = 0 ↔ x = 0 ∧ y != 0 := by
  simp only [rpow_def_of_nonneg hx]
  split_ifs <;> simp [*, exp_ne_zero]

@[simp]
/--
lemma `rpow_eq_zero` / 引理 `rpow_eq_zero`

English:
lemma rpow_eq_zero
  given: (hx : 0 <= x) (hy : y != 0)
  statement: x ^ y = 0 ↔ x = 0
  proof: by
  simp [rpow_eq_zero_iff_of_nonneg, *]

中文:
引理 rpow_eq_zero
  条件: (hx : 0 <= x) (hy : y != 0)
  结论: x ^ y = 0 ↔ x = 0
  证明: by
  simp [rpow_eq_zero_iff_of_nonneg, *]

Depends on / 依赖: rpow_eq_zero_iff_of_nonneg
-/
lemma rpow_eq_zero (hx : 0 <= x) (hy : y != 0) : x ^ y = 0 ↔ x = 0 := by
  simp [rpow_eq_zero_iff_of_nonneg, *]

/--
lemma `rpow_ne_zero` / 引理 `rpow_ne_zero`

English:
lemma rpow_ne_zero
  given: (hx : 0 <= x) (hy : y != 0)
  statement: x ^ y != 0 ↔ x != 0
  proof: by
  simp [hx, hy]

中文:
引理 rpow_ne_zero
  条件: (hx : 0 <= x) (hy : y != 0)
  结论: x ^ y != 0 ↔ x != 0
  证明: by
  simp [hx, hy]
-/
lemma rpow_ne_zero (hx : 0 <= x) (hy : y != 0) : x ^ y != 0 ↔ x != 0 := by
  simp [hx, hy]

open Real

/--
theorem `rpow_def_of_neg` / 定理 `rpow_def_of_neg`

English:
theorem rpow_def_of_neg
  given: {x : Real} (hx : x < 0) (y : Real)
  statement: x ^ y = exp (log x * y) * cos (y * π)
  proof: by
  rw [rpow_def]; rw [Complex.cpow_def]; rw [if_neg]
  · have : Complex.log x * y = ↑(log (-x) * y) + ↑(y * π) * Complex.I := by
      simp only [Complex.log, Complex.norm_real, norm_eq_abs, abs_of_neg hx, log_neg_eq_log,
        Complex.arg_ofReal_of_neg hx, Complex.ofReal_mul]
      ring
    rw [this]; rw [Complex.exp_add_mul_I]; rw [← Complex.ofReal_exp]; rw [← Complex.ofReal_cos]; rw [←
      Complex.ofReal_sin]; rw [mul_add]; rw [← Complex.ofReal_mul]; rw [← mul_assoc]; rw [← Complex.ofReal_mul]; rw [Complex.add_re]; rw [Complex.ofReal_re]; rw [Complex.mul_re]; rw [Complex.I_re]; rw [Complex.ofReal_im]; rw [Real.log_neg_eq_log]
    ring
  · rw [Complex.ofReal_eq_zero]
    exact ne_of_lt hx

中文:
定理 rpow_def_of_neg
  条件: {x : 实数} (hx : x < 0) (y : 实数)
  结论: x ^ y = exp (log x * y) * cos (y * π)
  证明: by
  rw [rpow_def]; rw [Complex.cpow_def]; rw [if_neg]
  · have : Complex.log x * y = ↑(log (-x) * y) + ↑(y * π) * Complex.I := by
      simp only [Complex.log, Complex.norm_real, norm_eq_abs, abs_of_neg hx, log_neg_eq_log,
        Complex.arg_ofReal_of_neg hx, Complex.ofReal_mul]
      ring
    rw [this]; rw [Complex.exp_add_mul_I]; rw [← Complex.ofReal_exp]; rw [← Complex.ofReal_cos]; rw [←
      Complex.ofReal_sin]; rw [mul_add]; rw [← Complex.ofReal_mul]; rw [← mul_assoc]; rw [← Complex.ofReal_mul]; rw [Complex.add_re]; rw [Complex.ofReal_re]; rw [Complex.mul_re]; rw [Complex.I_re]; rw [Complex.ofReal_im]; rw [Real.log_neg_eq_log]
    ring
  · rw [Complex.ofReal_eq_zero]
    exact ne_of_lt hx

Depends on / 依赖: Complex.I, Complex.add_re, Complex.arg_ofReal_of_neg, Complex.cpow_def, Complex.exp_add_mul_I, Complex.log, Complex.norm_real, Complex.ofReal_cos, Complex.ofReal_exp, Complex.ofReal_mul, Complex.ofReal_sin, abs_of_neg, add_re, arg_ofReal_of_neg, cpow_def, exp_add_mul_I, if_neg, log_neg_eq_log, mul_add, mul_assoc
-/
theorem rpow_def_of_neg {x : Real} (hx : x < 0) (y : Real) : x ^ y = exp (log x * y) * cos (y * π) := by
  rw [rpow_def]; rw [Complex.cpow_def]; rw [if_neg]
  · have : Complex.log x * y = ↑(log (-x) * y) + ↑(y * π) * Complex.I := by
      simp only [Complex.log, Complex.norm_real, norm_eq_abs, abs_of_neg hx, log_neg_eq_log,
        Complex.arg_ofReal_of_neg hx, Complex.ofReal_mul]
      ring
    rw [this]; rw [Complex.exp_add_mul_I]; rw [← Complex.ofReal_exp]; rw [← Complex.ofReal_cos]; rw [←
      Complex.ofReal_sin]; rw [mul_add]; rw [← Complex.ofReal_mul]; rw [← mul_assoc]; rw [← Complex.ofReal_mul]; rw [Complex.add_re]; rw [Complex.ofReal_re]; rw [Complex.mul_re]; rw [Complex.I_re]; rw [Complex.ofReal_im]; rw [Real.log_neg_eq_log]
    ring
  · rw [Complex.ofReal_eq_zero]
    exact ne_of_lt hx

-- simp is called on three goals at once (leaving one), with different simp sets
set_option linter.flexible false in
/--
theorem `rpow_def_of_nonpos` / 定理 `rpow_def_of_nonpos`

English:
theorem rpow_def_of_nonpos
  given: {x : Real} (hx : x <= 0) (y : Real)
  proof: by
  split_ifs with h <;> simp [rpow_def, *]; exact rpow_def_of_neg (lt_of_le_of_ne hx h) _

@[bound]

中文:
定理 rpow_def_of_nonpos
  条件: {x : 实数} (hx : x <= 0) (y : 实数)
  证明: by
  split_ifs with h <;> simp [rpow_def, *]; exact rpow_def_of_neg (lt_of_le_of_ne hx h) _

@[bound]

Depends on / 依赖: lt_of_le_of_ne, rpow_def, rpow_def_of_neg, split_ifs
-/
theorem rpow_def_of_nonpos {x : Real} (hx : x <= 0) (y : Real) :
    x ^ y = if x = 0 then if y = 0 then 1 else 0 else exp (log x * y) * cos (y * π) := by
  split_ifs with h <;> simp [rpow_def, *]; exact rpow_def_of_neg (lt_of_le_of_ne hx h) _

@[bound]
/--
theorem `rpow_pos_of_pos` / 定理 `rpow_pos_of_pos`

English:
theorem rpow_pos_of_pos
  given: {x : Real} (hx : 0 < x) (y : Real)
  statement: 0 < x ^ y
  proof: by
  rw [rpow_def_of_pos hx]; apply exp_pos

@[simp]

中文:
定理 rpow_pos_of_pos
  条件: {x : 实数} (hx : 0 < x) (y : 实数)
  结论: 0 < x ^ y
  证明: by
  rw [rpow_def_of_pos hx]; apply exp_pos

@[simp]

Depends on / 依赖: exp_pos, rpow_def_of_pos
-/
theorem rpow_pos_of_pos {x : Real} (hx : 0 < x) (y : Real) : 0 < x ^ y := by
  rw [rpow_def_of_pos hx]; apply exp_pos

@[simp]
/--
theorem `rpow_zero` / 定理 `rpow_zero`

English:
theorem rpow_zero
  given: (x : Real)
  statement: x ^ (0 : Real) = 1
  proof: by simp [rpow_def]

中文:
定理 rpow_zero
  条件: (x : 实数)
  结论: x ^ (0 : 实数) = 1
  证明: by simp [rpow_def]

Depends on / 依赖: rpow_def
-/
theorem rpow_zero (x : Real) : x ^ (0 : Real) = 1 := by simp [rpow_def]

/--
theorem `rpow_zero_pos` / 定理 `rpow_zero_pos`

English:
theorem rpow_zero_pos
  given: (x : Real)
  statement: 0 < x ^ (0 : Real)
  proof: by simp

@[simp]

中文:
定理 rpow_zero_pos
  条件: (x : 实数)
  结论: 0 < x ^ (0 : 实数)
  证明: by simp

@[simp]
-/
theorem rpow_zero_pos (x : Real) : 0 < x ^ (0 : Real) := by simp

@[simp]
/--
theorem `pi_rpow_zero` / 定理 `pi_rpow_zero`

English:
theorem pi_rpow_zero
  given: {α : Type*} (f : α -> Real)
  statement: f ^ (0 : Real) = 1
  proof: by ext; simp

@[simp]

中文:
定理 pi_rpow_zero
  条件: {α : 类型} (f : α -> 实数)
  结论: f ^ (0 : 实数) = 1
  证明: by ext; simp

@[simp]
-/
theorem pi_rpow_zero {α : Type*} (f : α -> Real) : f ^ (0 : Real) = 1 := by ext; simp

@[simp]
/--
theorem `zero_rpow` / 定理 `zero_rpow`

English:
theorem zero_rpow
  given: {x : Real} (h : x != 0)
  statement: (0 : Real) ^ x = 0
  proof: by simp [rpow_def, *]

中文:
定理 zero_rpow
  条件: {x : 实数} (h : x != 0)
  结论: (0 : 实数) ^ x = 0
  证明: by simp [rpow_def, *]

Depends on / 依赖: rpow_def
-/
theorem zero_rpow {x : Real} (h : x != 0) : (0 : Real) ^ x = 0 := by simp [rpow_def, *]

/--
theorem `zero_rpow_eq_iff` / 定理 `zero_rpow_eq_iff`

English:
theorem zero_rpow_eq_iff
  given: {x : Real} {a : Real}
  statement: 0 ^ x = a ↔ x != 0 ∧ a = 0 ∨ x = 0 ∧ a = 1
  proof: by
  constructor
  · intro hyp
    simp only [rpow_def, Complex.ofReal_zero] at hyp
    by_cases h : x = 0
    · subst h
      simp only [Complex.one_re, Complex.ofReal_zero, Complex.cpow_zero] at hyp
      exact Or.inr ⟨rfl, hyp.symm⟩
    · rw [Complex.zero_cpow (Complex.ofReal_ne_zero.mpr h)] at hyp
      exact Or.inl ⟨h, hyp.symm⟩
  · rintro (⟨h, rfl⟩ | ⟨rfl, rfl⟩)
    · exact zero_rpow h
    · exact rpow_zero _

中文:
定理 zero_rpow_eq_iff
  条件: {x : 实数} {a : 实数}
  结论: 0 ^ x = a ↔ x != 0 ∧ a = 0 ∨ x = 0 ∧ a = 1
  证明: by
  constructor
  · intro hyp
    simp only [rpow_def, Complex.ofReal_zero] at hyp
    by_cases h : x = 0
    · subst h
      simp only [Complex.one_re, Complex.ofReal_zero, Complex.cpow_zero] at hyp
      exact Or.inr ⟨rfl, hyp.symm⟩
    · rw [Complex.zero_cpow (Complex.ofReal_ne_zero.mpr h)] at hyp
      exact Or.inl ⟨h, hyp.symm⟩
  · rintro (⟨h, rfl⟩ | ⟨rfl, rfl⟩)
    · exact zero_rpow h
    · exact rpow_zero _

Depends on / 依赖: Complex.cpow_zero, Complex.ofReal_ne_zero.mpr, Complex.ofReal_zero, Complex.one_re, Complex.zero_cpow, Or.inl, Or.inr, cpow_zero, hyp.symm, ofReal_ne_zero, ofReal_zero, one_re, rpow_def, rpow_zero, zero_cpow, zero_rpow
-/
theorem zero_rpow_eq_iff {x : Real} {a : Real} : 0 ^ x = a ↔ x != 0 ∧ a = 0 ∨ x = 0 ∧ a = 1 := by
  constructor
  · intro hyp
    simp only [rpow_def, Complex.ofReal_zero] at hyp
    by_cases h : x = 0
    · subst h
      simp only [Complex.one_re, Complex.ofReal_zero, Complex.cpow_zero] at hyp
      exact Or.inr ⟨rfl, hyp.symm⟩
    · rw [Complex.zero_cpow (Complex.ofReal_ne_zero.mpr h)] at hyp
      exact Or.inl ⟨h, hyp.symm⟩
  · rintro (⟨h, rfl⟩ | ⟨rfl, rfl⟩)
    · exact zero_rpow h
    · exact rpow_zero _

/--
theorem `eq_zero_rpow_iff` / 定理 `eq_zero_rpow_iff`

English:
theorem eq_zero_rpow_iff
  given: {x : Real} {a : Real}
  statement: a = 0 ^ x ↔ x != 0 ∧ a = 0 ∨ x = 0 ∧ a = 1
  proof: by
  rw [← zero_rpow_eq_iff]; rw [eq_comm]

@[simp]

中文:
定理 eq_zero_rpow_iff
  条件: {x : 实数} {a : 实数}
  结论: a = 0 ^ x ↔ x != 0 ∧ a = 0 ∨ x = 0 ∧ a = 1
  证明: by
  rw [← zero_rpow_eq_iff]; rw [eq_comm]

@[simp]

Depends on / 依赖: eq_comm, zero_rpow_eq_iff
-/
theorem eq_zero_rpow_iff {x : Real} {a : Real} : a = 0 ^ x ↔ x != 0 ∧ a = 0 ∨ x = 0 ∧ a = 1 := by
  rw [← zero_rpow_eq_iff]; rw [eq_comm]

@[simp]
/--
theorem `rpow_one` / 定理 `rpow_one`

English:
theorem rpow_one
  given: (x : Real)
  statement: x ^ (1 : Real) = x
  proof: by simp [rpow_def]

@[simp]

中文:
定理 rpow_one
  条件: (x : 实数)
  结论: x ^ (1 : 实数) = x
  证明: by simp [rpow_def]

@[simp]

Depends on / 依赖: rpow_def
-/
theorem rpow_one (x : Real) : x ^ (1 : Real) = x := by simp [rpow_def]

@[simp]
/--
theorem `pi_rpow_one` / 定理 `pi_rpow_one`

English:
theorem pi_rpow_one
  given: {α : Type*} (f : α -> Real)
  statement: f ^ (1 : Real) = f
  proof: by ext; simp

@[simp]

中文:
定理 pi_rpow_one
  条件: {α : 类型} (f : α -> 实数)
  结论: f ^ (1 : 实数) = f
  证明: by ext; simp

@[simp]

Depends on / 依赖: isIso_hom, toNatIso
-/
theorem pi_rpow_one {α : Type*} (f : α -> Real) : f ^ (1 : Real) = f := by ext; simp

@[simp]
/--
theorem `one_rpow` / 定理 `one_rpow`

English:
theorem one_rpow
  given: (x : Real)
  statement: (1 : Real) ^ x = 1
  proof: by simp [rpow_def]

中文:
定理 one_rpow
  条件: (x : 实数)
  结论: (1 : 实数) ^ x = 1
  证明: by simp [rpow_def]

Depends on / 依赖: isIso_inv, rpow_def, toNatIso
-/
theorem one_rpow (x : Real) : (1 : Real) ^ x = 1 := by simp [rpow_def]

/--
theorem `zero_rpow_le_one` / 定理 `zero_rpow_le_one`

English:
theorem zero_rpow_le_one
  given: (x : Real)
  statement: (0 : Real) ^ x <= 1
  proof: by
  by_cases h : x = 0 <;> simp [h, zero_le_one]

中文:
定理 zero_rpow_le_one
  条件: (x : 实数)
  结论: (0 : 实数) ^ x <= 1
  证明: by
  by_cases h : x = 0 <;> simp [h, zero_le_one]

Depends on / 依赖: zero_le_one
-/
theorem zero_rpow_le_one (x : Real) : (0 : Real) ^ x <= 1 := by
  by_cases h : x = 0 <;> simp [h, zero_le_one]

/--
theorem `zero_rpow_nonneg` / 定理 `zero_rpow_nonneg`

English:
theorem zero_rpow_nonneg
  given: (x : Real)
  statement: 0 <= (0 : Real) ^ x
  proof: by
  by_cases h : x = 0 <;> simp [h, zero_le_one]

@[bound]

中文:
定理 zero_rpow_nonneg
  条件: (x : 实数)
  结论: 0 <= (0 : 实数) ^ x
  证明: by
  by_cases h : x = 0 <;> simp [h, zero_le_one]

@[bound]

Depends on / 依赖: zero_le_one
-/
theorem zero_rpow_nonneg (x : Real) : 0 <= (0 : Real) ^ x := by
  by_cases h : x = 0 <;> simp [h, zero_le_one]

@[bound]
/--
theorem `rpow_nonneg` / 定理 `rpow_nonneg`

English:
theorem rpow_nonneg
  given: {x : Real} (hx : 0 <= x) (y : Real)
  statement: 0 <= x ^ y
  proof: by
  rw [rpow_def_of_nonneg hx]; split_ifs <;>
    simp only [zero_le_one, le_refl, le_of_lt (exp_pos _)]

中文:
定理 rpow_nonneg
  条件: {x : 实数} (hx : 0 <= x) (y : 实数)
  结论: 0 <= x ^ y
  证明: by
  rw [rpow_def_of_nonneg hx]; split_ifs <;>
    simp only [zero_le_one, le_refl, le_of_lt (exp_pos _)]

Depends on / 依赖: exp_pos, le_of_lt, le_refl, rpow_def_of_nonneg, split_ifs, zero_le_one
-/
theorem rpow_nonneg {x : Real} (hx : 0 <= x) (y : Real) : 0 <= x ^ y := by
  rw [rpow_def_of_nonneg hx]; split_ifs <;>
    simp only [zero_le_one, le_refl, le_of_lt (exp_pos _)]

/--
theorem `abs_rpow_of_nonneg` / 定理 `abs_rpow_of_nonneg`

English:
theorem abs_rpow_of_nonneg
  given: {x y : Real} (hx_nonneg : 0 <= x)
  statement: |x ^ y| = |x| ^ y
  proof: by
  have h_rpow_nonneg : 0 <= x ^ y := Real.rpow_nonneg hx_nonneg _
  rw [abs_eq_self.mpr hx_nonneg]; rw [abs_eq_self.mpr h_rpow_nonneg]

@[bound]

中文:
定理 abs_rpow_of_nonneg
  条件: {x y : 实数} (hx_nonneg : 0 <= x)
  结论: |x ^ y| = |x| ^ y
  证明: by
  have h_rpow_nonneg : 0 <= x ^ y := Real.rpow_nonneg hx_nonneg _
  rw [abs_eq_self.mpr hx_nonneg]; rw [abs_eq_self.mpr h_rpow_nonneg]

@[bound]

Depends on / 依赖: Real.rpow_nonneg, abs_eq_self, abs_eq_self.mpr, h_rpow_nonneg, hx_nonneg, rpow_nonneg
-/
theorem abs_rpow_of_nonneg {x y : Real} (hx_nonneg : 0 <= x) : |x ^ y| = |x| ^ y := by
  have h_rpow_nonneg : 0 <= x ^ y := Real.rpow_nonneg hx_nonneg _
  rw [abs_eq_self.mpr hx_nonneg]; rw [abs_eq_self.mpr h_rpow_nonneg]

@[bound]
/--
theorem `abs_rpow_le_abs_rpow` / 定理 `abs_rpow_le_abs_rpow`

English:
theorem abs_rpow_le_abs_rpow
  given: (x y : Real)
  statement: |x ^ y| <= |x| ^ y
  proof: by
  rcases le_or_gt 0 x with hx | hx
  · rw [abs_rpow_of_nonneg hx]
  · rw [abs_of_neg hx, rpow_def_of_neg hx, rpow_def_of_pos (neg_pos.2 hx), log_neg_eq_log, abs_mul,
      abs_of_pos (exp_pos _)]
    exact mul_le_of_le_one_right (exp_pos _).le (abs_cos_le_one _)

中文:
定理 abs_rpow_le_abs_rpow
  条件: (x y : 实数)
  结论: |x ^ y| <= |x| ^ y
  证明: by
  rcases le_or_gt 0 x with hx | hx
  · rw [abs_rpow_of_nonneg hx]
  · rw [abs_of_neg hx, rpow_def_of_neg hx, rpow_def_of_pos (neg_pos.2 hx), log_neg_eq_log, abs_mul,
      abs_of_pos (exp_pos _)]
    exact mul_le_of_le_one_right (exp_pos _).le (abs_cos_le_one _)

Depends on / 依赖: abs_cos_le_one, abs_mul, abs_of_neg, abs_of_pos, abs_rpow_of_nonneg, exp_pos, le_or_gt, log_neg_eq_log, mul_le_of_le_one_right, neg_pos, rpow_def_of_neg, rpow_def_of_pos
-/
theorem abs_rpow_le_abs_rpow (x y : Real) : |x ^ y| <= |x| ^ y := by
  rcases le_or_gt 0 x with hx | hx
  · rw [abs_rpow_of_nonneg hx]
  · rw [abs_of_neg hx, rpow_def_of_neg hx, rpow_def_of_pos (neg_pos.2 hx), log_neg_eq_log, abs_mul,
      abs_of_pos (exp_pos _)]
    exact mul_le_of_le_one_right (exp_pos _).le (abs_cos_le_one _)

/--
theorem `abs_rpow_le_exp_log_mul` / 定理 `abs_rpow_le_exp_log_mul`

English:
theorem abs_rpow_le_exp_log_mul
  given: (x y : Real)
  statement: |x ^ y| <= exp (log x * y)
  proof: by
  refine (abs_rpow_le_abs_rpow x y).trans ?_
  by_cases hx : x = 0
  · by_cases hy : y = 0 <;> simp [hx, hy, zero_le_one]
  · rw [rpow_def_of_pos (abs_pos.2 hx), log_abs]

中文:
定理 abs_rpow_le_exp_log_mul
  条件: (x y : 实数)
  结论: |x ^ y| <= exp (log x * y)
  证明: by
  refine (abs_rpow_le_abs_rpow x y).trans ?_
  by_cases hx : x = 0
  · by_cases hy : y = 0 <;> simp [hx, hy, zero_le_one]
  · rw [rpow_def_of_pos (abs_pos.2 hx), log_abs]

Depends on / 依赖: abs_pos, abs_rpow_le_abs_rpow, log_abs, rpow_def_of_pos, zero_le_one
-/
theorem abs_rpow_le_exp_log_mul (x y : Real) : |x ^ y| <= exp (log x * y) := by
  refine (abs_rpow_le_abs_rpow x y).trans ?_
  by_cases hx : x = 0
  · by_cases hy : y = 0 <;> simp [hx, hy, zero_le_one]
  · rw [rpow_def_of_pos (abs_pos.2 hx), log_abs]

/--
lemma `rpow_inv_log` / 引理 `rpow_inv_log`

English:
lemma rpow_inv_log
  given: (hx₀ : 0 < x) (hx₁ : x != 1)
  statement: x ^ (log x)⁻¹ = exp 1
  proof: by
  rw [rpow_def_of_pos hx₀]; rw [mul_inv_cancel₀]
  exact log_ne_zero.2 ⟨hx₀.ne', hx₁, by bound⟩

中文:
引理 rpow_inv_log
  条件: (hx₀ : 0 < x) (hx₁ : x != 1)
  结论: x ^ (log x)⁻¹ = exp 1
  证明: by
  rw [rpow_def_of_pos hx₀]; rw [mul_inv_cancel₀]
  exact log_ne_zero.2 ⟨hx₀.ne', hx₁, by bound⟩

Depends on / 依赖: log_ne_zero, rpow_def_of_pos
-/
lemma rpow_inv_log (hx₀ : 0 < x) (hx₁ : x != 1) : x ^ (log x)⁻¹ = exp 1 := by
  rw [rpow_def_of_pos hx₀]; rw [mul_inv_cancel₀]
  exact log_ne_zero.2 ⟨hx₀.ne', hx₁, by bound⟩

/--
lemma `rpow_inv_log_le_exp_one` / 引理 `rpow_inv_log_le_exp_one`

English:
lemma rpow_inv_log_le_exp_one
  statement: x ^ (log x)⁻¹ <= exp 1
  proof: by
  calc
    _ <= |x ^ (log x)⁻¹| := le_abs_self _
    _ <= |x| ^ (log x)⁻¹ := abs_rpow_le_abs_rpow ..
  rw [← log_abs]
  obtain hx | hx := (abs_nonneg x).eq_or_lt'
  · simp [hx]
  · rw [rpow_def_of_pos hx]
    gcongr
    exact mul_inv_le_one

中文:
引理 rpow_inv_log_le_exp_one
  结论: x ^ (log x)⁻¹ <= exp 1
  证明: by
  calc
    _ <= |x ^ (log x)⁻¹| := le_abs_self _
    _ <= |x| ^ (log x)⁻¹ := abs_rpow_le_abs_rpow ..
  rw [← log_abs]
  obtain hx | hx := (abs_nonneg x).eq_or_lt'
  · simp [hx]
  · rw [rpow_def_of_pos hx]
    gcongr
    exact mul_inv_le_one

Depends on / 依赖: abs_nonneg, abs_rpow_le_abs_rpow, eq_or_lt, le_abs_self, log_abs, mul_inv_le_one, rpow_def_of_pos
-/
lemma rpow_inv_log_le_exp_one : x ^ (log x)⁻¹ <= exp 1 := by
  calc
    _ <= |x ^ (log x)⁻¹| := le_abs_self _
    _ <= |x| ^ (log x)⁻¹ := abs_rpow_le_abs_rpow ..
  rw [← log_abs]
  obtain hx | hx := (abs_nonneg x).eq_or_lt'
  · simp [hx]
  · rw [rpow_def_of_pos hx]
    gcongr
    exact mul_inv_le_one

/--
theorem `norm_rpow_of_nonneg` / 定理 `norm_rpow_of_nonneg`

English:
theorem norm_rpow_of_nonneg
  given: {x y : Real} (hx_nonneg : 0 <= x)
  statement: ‖x ^ y‖ = ‖x‖ ^ y
  proof: by
  simp_rw [Real.norm_eq_abs]
  exact abs_rpow_of_nonneg hx_nonneg

中文:
定理 norm_rpow_of_nonneg
  条件: {x y : 实数} (hx_nonneg : 0 <= x)
  结论: ‖x ^ y‖ = ‖x‖ ^ y
  证明: by
  simp_rw [Real.norm_eq_abs]
  exact abs_rpow_of_nonneg hx_nonneg

Depends on / 依赖: Real.norm_eq_abs, abs_rpow_of_nonneg, hx_nonneg, norm_eq_abs, simp_rw
-/
theorem norm_rpow_of_nonneg {x y : Real} (hx_nonneg : 0 <= x) : ‖x ^ y‖ = ‖x‖ ^ y := by
  simp_rw [Real.norm_eq_abs]
  exact abs_rpow_of_nonneg hx_nonneg

variable {w x y z : Real}

/--
theorem `rpow_add` / 定理 `rpow_add`

English:
theorem rpow_add
  given: (hx : 0 < x) (y z : Real)
  statement: x ^ (y + z) = x ^ y * x ^ z
  proof: by
  simp only [rpow_def_of_pos hx, mul_add, exp_add]

中文:
定理 rpow_add
  条件: (hx : 0 < x) (y z : 实数)
  结论: x ^ (y + z) = x ^ y * x ^ z
  证明: by
  simp only [rpow_def_of_pos hx, mul_add, exp_add]

Depends on / 依赖: exp_add, mul_add, rpow_def_of_pos
-/
theorem rpow_add (hx : 0 < x) (y z : Real) : x ^ (y + z) = x ^ y * x ^ z := by
  simp only [rpow_def_of_pos hx, mul_add, exp_add]

/--
theorem `rpow_add'` / 定理 `rpow_add'`

English:
theorem rpow_add'
  given: (hx : 0 <= x) (h : y + z != 0)
  statement: x ^ (y + z) = x ^ y * x ^ z
  proof: by
  rcases hx.eq_or_lt with (rfl | pos)
  · rw [zero_rpow h, zero_eq_mul]
have : y != 0 ∨ z != 0 := not_and_or.1 fun ⟨hy, hz⟩ => h hy.symm ▸ hz.symm ▸ zero_add 0
    exact this.imp zero_rpow zero_rpow
  · exact rpow_add pos _ _

中文:
定理 rpow_add'
  条件: (hx : 0 <= x) (h : y + z != 0)
  结论: x ^ (y + z) = x ^ y * x ^ z
  证明: by
  rcases hx.eq_or_lt with (rfl | pos)
  · rw [zero_rpow h, zero_eq_mul]
have : y != 0 ∨ z != 0 := not_and_or.1 fun ⟨hy, hz⟩ => h hy.symm ▸ hz.symm ▸ zero_add 0
    exact this.imp zero_rpow zero_rpow
  · exact rpow_add pos _ _

Depends on / 依赖: eq_or_lt, hx.eq_or_lt, hy.symm, hz.symm, not_and_or, rpow_add, this.imp, zero_add, zero_eq_mul, zero_rpow
-/
theorem rpow_add' (hx : 0 <= x) (h : y + z != 0) : x ^ (y + z) = x ^ y * x ^ z := by
  rcases hx.eq_or_lt with (rfl | pos)
  · rw [zero_rpow h, zero_eq_mul]
have : y != 0 ∨ z != 0 := not_and_or.1 fun ⟨hy, hz⟩ => h hy.symm ▸ hz.symm ▸ zero_add 0
    exact this.imp zero_rpow zero_rpow
  · exact rpow_add pos _ _

/--
lemma `rpow_of_add_eq` / 引理 `rpow_of_add_eq`

English:
lemma rpow_of_add_eq
  given: (hx : 0 <= x) (hw : w != 0) (h : y + z = w)
  statement: x ^ w = x ^ y * x ^ z
  proof: by
  rw [← h]; rw [rpow_add' hx]; rwa [h]

中文:
引理 rpow_of_add_eq
  条件: (hx : 0 <= x) (hw : w != 0) (h : y + z = w)
  结论: x ^ w = x ^ y * x ^ z
  证明: by
  rw [← h]; rw [rpow_add' hx]; rwa [h]

Depends on / 依赖: rpow_add
-/
lemma rpow_of_add_eq (hx : 0 <= x) (hw : w != 0) (h : y + z = w) : x ^ w = x ^ y * x ^ z := by
  rw [← h]; rw [rpow_add' hx]; rwa [h]

/--
theorem `rpow_add_of_nonneg` / 定理 `rpow_add_of_nonneg`

English:
theorem rpow_add_of_nonneg
  given: (hx : 0 <= x) (hy : 0 <= y) (hz : 0 <= z)
  proof: by
  rcases hy.eq_or_lt with (rfl | hy)
  · rw [zero_add, rpow_zero, one_mul]
  exact rpow_add' hx (ne_of_gt <| add_pos_of_pos_of_nonneg hy hz)

中文:
定理 rpow_add_of_nonneg
  条件: (hx : 0 <= x) (hy : 0 <= y) (hz : 0 <= z)
  证明: by
  rcases hy.eq_or_lt with (rfl | hy)
  · rw [zero_add, rpow_zero, one_mul]
  exact rpow_add' hx (ne_of_gt <| add_pos_of_pos_of_nonneg hy hz)

Depends on / 依赖: add_pos_of_pos_of_nonneg, eq_or_lt, hy.eq_or_lt, ne_of_gt, one_mul, rpow_add, rpow_zero, zero_add
-/
theorem rpow_add_of_nonneg (hx : 0 <= x) (hy : 0 <= y) (hz : 0 <= z) :
    x ^ (y + z) = x ^ y * x ^ z := by
  rcases hy.eq_or_lt with (rfl | hy)
  · rw [zero_add, rpow_zero, one_mul]
  exact rpow_add' hx (ne_of_gt <| add_pos_of_pos_of_nonneg hy hz)

/--
theorem `le_rpow_add` / 定理 `le_rpow_add`

English:
theorem le_rpow_add
  given: {x : Real} (hx : 0 <= x) (y z : Real)
  statement: x ^ y * x ^ z <= x ^ (y + z)
  proof: by
  rcases le_iff_eq_or_lt.1 hx with (H | pos)
  · by_cases h : y + z = 0
    · simp only [H.symm, h, rpow_zero]
      calc
        (0 : Real) ^ y * 0 ^ z <= 1 * 1 := by
          gcongr
          exacts [zero_rpow_nonneg z, zero_rpow_le_one y, zero_rpow_le_one z]
        _ = 1 := by simp
    · simp [rpow_add', ← H, h]
  · simp [rpow_add pos]

中文:
定理 le_rpow_add
  条件: {x : 实数} (hx : 0 <= x) (y z : 实数)
  结论: x ^ y * x ^ z <= x ^ (y + z)
  证明: by
  rcases le_iff_eq_or_lt.1 hx with (H | pos)
  · by_cases h : y + z = 0
    · simp only [H.symm, h, rpow_zero]
      calc
        (0 : Real) ^ y * 0 ^ z <= 1 * 1 := by
          gcongr
          exacts [zero_rpow_nonneg z, zero_rpow_le_one y, zero_rpow_le_one z]
        _ = 1 := by simp
    · simp [rpow_add', ← H, h]
  · simp [rpow_add pos]

Depends on / 依赖: H.symm, exacts, le_iff_eq_or_lt, rpow_add, rpow_zero, zero_rpow_le_one, zero_rpow_nonneg
-/
theorem le_rpow_add {x : Real} (hx : 0 <= x) (y z : Real) : x ^ y * x ^ z <= x ^ (y + z) := by
  rcases le_iff_eq_or_lt.1 hx with (H | pos)
  · by_cases h : y + z = 0
    · simp only [H.symm, h, rpow_zero]
      calc
        (0 : Real) ^ y * 0 ^ z <= 1 * 1 := by
          gcongr
          exacts [zero_rpow_nonneg z, zero_rpow_le_one y, zero_rpow_le_one z]
        _ = 1 := by simp
    · simp [rpow_add', ← H, h]
  · simp [rpow_add pos]

/--
theorem `rpow_sum_of_pos` / 定理 `rpow_sum_of_pos`

English:
theorem rpow_sum_of_pos
  given: {ι : Type*} {a : Real} (ha : 0 < a) (f : ι -> Real) (s : Finset ι)
  proof: map_sum (⟨⟨fun (x : Real) => (a ^ x : Real), rpow_zero a⟩, rpow_add ha⟩ : Real ->+ (Additive Real)) f s

中文:
定理 rpow_sum_of_pos
  条件: {ι : 类型} {a : 实数} (ha : 0 < a) (f : ι -> 实数) (s : 有限集 ι)
  证明: map_sum (⟨⟨fun (x : Real) => (a ^ x : Real), rpow_zero a⟩, rpow_add ha⟩ : Real ->+ (Additive Real)) f s

Depends on / 依赖: Additive, map_sum, rpow_add, rpow_zero
-/
theorem rpow_sum_of_pos {ι : Type*} {a : Real} (ha : 0 < a) (f : ι -> Real) (s : Finset ι) :
    (a ^ ∑ x in s, f x) = ∏ x in s, a ^ f x :=
  map_sum (⟨⟨fun (x : Real) => (a ^ x : Real), rpow_zero a⟩, rpow_add ha⟩ : Real ->+ (Additive Real)) f s

/--
theorem `rpow_sum_of_nonneg` / 定理 `rpow_sum_of_nonneg`

English:
theorem rpow_sum_of_nonneg
  statement: {ι : Type*} {a : Real} (ha : 0 <= a) {s : Finset ι} {f : ι -> Real}
  proof: by
  induction s using Finset.cons_induction with
  | empty => rw [sum_empty, Finset.prod_empty, rpow_zero]
  | cons i s hi ihs =>
    rw [forall_mem_cons] at h
    rw [sum_cons]; rw [prod_cons]; rw [← ihs h.2]; rw [rpow_add_of_nonneg ha h.1 (sum_nonneg h.2)]

中文:
定理 rpow_sum_of_nonneg
  结论: {ι : 类型} {a : 实数} (ha : 0 <= a) {s : 有限集 ι} {f : ι -> 实数}
  证明: by
  induction s using Finset.cons_induction with
  | empty => rw [sum_empty, Finset.prod_empty, rpow_zero]
  | cons i s hi ihs =>
    rw [forall_mem_cons] at h
    rw [sum_cons]; rw [prod_cons]; rw [← ihs h.2]; rw [rpow_add_of_nonneg ha h.1 (sum_nonneg h.2)]

Depends on / 依赖: Finset, Finset.cons_induction, Finset.prod_empty, cons_induction, forall_mem_cons, prod_cons, prod_empty, rpow_add_of_nonneg, rpow_zero, sum_cons, sum_empty, sum_nonneg
-/
theorem rpow_sum_of_nonneg {ι : Type*} {a : Real} (ha : 0 <= a) {s : Finset ι} {f : ι -> Real}
    (h : forall x in s, 0 <= f x) : (a ^ ∑ x in s, f x) = ∏ x in s, a ^ f x := by
  induction s using Finset.cons_induction with
  | empty => rw [sum_empty, Finset.prod_empty, rpow_zero]
  | cons i s hi ihs =>
    rw [forall_mem_cons] at h
    rw [sum_cons]; rw [prod_cons]; rw [← ihs h.2]; rw [rpow_add_of_nonneg ha h.1 (sum_nonneg h.2)]

/--
theorem `rpow_neg_eq_inv_rpow` / 定理 `rpow_neg_eq_inv_rpow`

English:
theorem rpow_neg_eq_inv_rpow
  given: (x y : Real)
  statement: x ^ (-y) = x⁻¹ ^ y
  proof: by
  simp [rpow_def, Complex.cpow_neg, Complex.inv_cpow_eq_ite, apply_ite]

中文:
定理 rpow_neg_eq_inv_rpow
  条件: (x y : 实数)
  结论: x ^ (-y) = x⁻¹ ^ y
  证明: by
  simp [rpow_def, Complex.cpow_neg, Complex.inv_cpow_eq_ite, apply_ite]

Depends on / 依赖: Complex.cpow_neg, Complex.inv_cpow_eq_ite, apply_ite, cpow_neg, inv_cpow_eq_ite, rpow_def
-/
theorem rpow_neg_eq_inv_rpow (x y : Real) : x ^ (-y) = x⁻¹ ^ y := by
  simp [rpow_def, Complex.cpow_neg, Complex.inv_cpow_eq_ite, apply_ite]

/--
theorem `rpow_neg` / 定理 `rpow_neg`

English:
theorem rpow_neg
  given: {x : Real} (hx : 0 <= x) (y : Real)
  statement: x ^ (-y) = (x ^ y)⁻¹
  proof: by
  simp only [rpow_def_of_nonneg hx]; split_ifs <;> simp_all [exp_neg]

中文:
定理 rpow_neg
  条件: {x : 实数} (hx : 0 <= x) (y : 实数)
  结论: x ^ (-y) = (x ^ y)⁻¹
  证明: by
  simp only [rpow_def_of_nonneg hx]; split_ifs <;> simp_all [exp_neg]

Depends on / 依赖: exp_neg, rpow_def_of_nonneg, split_ifs
-/
theorem rpow_neg {x : Real} (hx : 0 <= x) (y : Real) : x ^ (-y) = (x ^ y)⁻¹ := by
  simp only [rpow_def_of_nonneg hx]; split_ifs <;> simp_all [exp_neg]

/--
theorem `rpow_sub` / 定理 `rpow_sub`

English:
theorem rpow_sub
  given: {x : Real} (hx : 0 < x) (y z : Real)
  statement: x ^ (y - z) = x ^ y / x ^ z
  proof: by
  simp only [sub_eq_add_neg, rpow_add hx, rpow_neg (le_of_lt hx), div_eq_mul_inv]

中文:
定理 rpow_sub
  条件: {x : 实数} (hx : 0 < x) (y z : 实数)
  结论: x ^ (y - z) = x ^ y / x ^ z
  证明: by
  simp only [sub_eq_add_neg, rpow_add hx, rpow_neg (le_of_lt hx), div_eq_mul_inv]

Depends on / 依赖: div_eq_mul_inv, le_of_lt, rpow_add, rpow_neg, sub_eq_add_neg
-/
theorem rpow_sub {x : Real} (hx : 0 < x) (y z : Real) : x ^ (y - z) = x ^ y / x ^ z := by
  simp only [sub_eq_add_neg, rpow_add hx, rpow_neg (le_of_lt hx), div_eq_mul_inv]

/--
theorem `rpow_sub'` / 定理 `rpow_sub'`

English:
theorem rpow_sub'
  given: {x : Real} (hx : 0 <= x) {y z : Real} (h : y - z != 0)
  statement: x ^ (y - z) = x ^ y / x ^ z
  proof: by
  simp only [sub_eq_add_neg] at h ⊢
  simp only [rpow_add' hx h, rpow_neg hx, div_eq_mul_inv]

中文:
定理 rpow_sub'
  条件: {x : 实数} (hx : 0 <= x) {y z : 实数} (h : y - z != 0)
  结论: x ^ (y - z) = x ^ y / x ^ z
  证明: by
  simp only [sub_eq_add_neg] at h ⊢
  simp only [rpow_add' hx h, rpow_neg hx, div_eq_mul_inv]

Depends on / 依赖: div_eq_mul_inv, rpow_add, rpow_neg, sub_eq_add_neg
-/
theorem rpow_sub' {x : Real} (hx : 0 <= x) {y z : Real} (h : y - z != 0) : x ^ (y - z) = x ^ y / x ^ z := by
  simp only [sub_eq_add_neg] at h ⊢
  simp only [rpow_add' hx h, rpow_neg hx, div_eq_mul_inv]

/--
theorem `_root_.HasCompactSupport.rpow_const` / 定理 `_root_.HasCompactSupport.rpow_const`

English:
theorem _root_.HasCompactSupport.rpow_const
  statement: {α : Type*} [TopologicalSpace α] {f : α -> Real}
  proof: hf.comp_left (g := (· ^ r)) (Real.zero_rpow hr)

中文:
定理 _root_.HasCompactSupport.rpow_const
  结论: {α : 类型} [拓扑空间 α] {f : α -> 实数}
  证明: hf.comp_left (g := (· ^ r)) (Real.zero_rpow hr)
-/
protected theorem _root_.HasCompactSupport.rpow_const {α : Type*} [TopologicalSpace α] {f : α -> Real}
    (hf : HasCompactSupport f) {r : Real} (hr : r != 0) : HasCompactSupport (fun x => f x ^ r) :=
  hf.comp_left (g := (· ^ r)) (Real.zero_rpow hr)

end Real

/-!
## Comparing real and complex powers
-/


namespace Complex

/--
theorem `ofReal_cpow` / 定理 `ofReal_cpow`

English:
theorem ofReal_cpow
  given: {x : Real} (hx : 0 <= x) (y : Real)
  statement: ((x ^ y : Real) : Complex) = (x : Complex) ^ (y : Complex)
  proof: by
  simp only [Real.rpow_def_of_nonneg hx, Complex.cpow_def, ofReal_eq_zero]; split_ifs <;>
    simp [Complex.ofReal_log hx]

中文:
定理 of实数_cpow
  条件: {x : 实数} (hx : 0 <= x) (y : 实数)
  结论: ((x ^ y : 实数) : 复形) = (x : 复形) ^ (y : 复形)
  证明: by
  simp only [Real.rpow_def_of_nonneg hx, Complex.cpow_def, ofReal_eq_zero]; split_ifs <;>
    simp [Complex.ofReal_log hx]

Depends on / 依赖: Complex.cpow_def, Complex.ofReal_log, Real.rpow_def_of_nonneg, cpow_def, ofReal_eq_zero, ofReal_log, rpow_def_of_nonneg, split_ifs
-/
theorem ofReal_cpow {x : Real} (hx : 0 <= x) (y : Real) : ((x ^ y : Real) : Complex) = (x : Complex) ^ (y : Complex) := by
  simp only [Real.rpow_def_of_nonneg hx, Complex.cpow_def, ofReal_eq_zero]; split_ifs <;>
    simp [Complex.ofReal_log hx]

/--
theorem `ofReal_cpow_of_nonpos` / 定理 `ofReal_cpow_of_nonpos`

English:
theorem ofReal_cpow_of_nonpos
  given: {x : Real} (hx : x <= 0) (y : Complex)
  proof: by
  rcases hx.eq_or_lt with (rfl | hlt)
  · rcases eq_or_ne y 0 with (rfl | hy) <;> simp [*]
  have hne : (x : Complex) != 0 := ofReal_ne_zero.mpr hlt.ne
  rw [cpow_def_of_ne_zero hne]; rw [cpow_def_of_ne_zero (neg_ne_zero.2 hne)]; rw [← exp_add]; rw [← add_mul]; rw [log]; rw [log]; rw [norm_neg]; rw [arg_ofReal_of_neg hlt]; rw [← ofReal_neg]; rw [arg_ofReal_of_nonneg (neg_nonneg.2 hx)]; rw [ofReal_zero]; rw [zero_mul]; rw [add_zero]

中文:
定理 of实数_cpow_of_nonpos
  条件: {x : 实数} (hx : x <= 0) (y : 复形)
  证明: by
  rcases hx.eq_or_lt with (rfl | hlt)
  · rcases eq_or_ne y 0 with (rfl | hy) <;> simp [*]
  have hne : (x : Complex) != 0 := ofReal_ne_zero.mpr hlt.ne
  rw [cpow_def_of_ne_zero hne]; rw [cpow_def_of_ne_zero (neg_ne_zero.2 hne)]; rw [← exp_add]; rw [← add_mul]; rw [log]; rw [log]; rw [norm_neg]; rw [arg_ofReal_of_neg hlt]; rw [← ofReal_neg]; rw [arg_ofReal_of_nonneg (neg_nonneg.2 hx)]; rw [ofReal_zero]; rw [zero_mul]; rw [add_zero]

Depends on / 依赖: add_mul, add_zero, arg_ofReal_of_neg, arg_ofReal_of_nonneg, cpow_def_of_ne_zero, eq_or_lt, eq_or_ne, exp_add, hlt.ne, hx.eq_or_lt, neg_ne_zero, neg_nonneg, norm_neg, ofReal_ne_zero, ofReal_ne_zero.mpr, ofReal_neg, ofReal_zero, zero_mul
-/
theorem ofReal_cpow_of_nonpos {x : Real} (hx : x <= 0) (y : Complex) :
    (x : Complex) ^ y = (-x : Complex) ^ y * exp (π * I * y) := by
  rcases hx.eq_or_lt with (rfl | hlt)
  · rcases eq_or_ne y 0 with (rfl | hy) <;> simp [*]
  have hne : (x : Complex) != 0 := ofReal_ne_zero.mpr hlt.ne
  rw [cpow_def_of_ne_zero hne]; rw [cpow_def_of_ne_zero (neg_ne_zero.2 hne)]; rw [← exp_add]; rw [← add_mul]; rw [log]; rw [log]; rw [norm_neg]; rw [arg_ofReal_of_neg hlt]; rw [← ofReal_neg]; rw [arg_ofReal_of_nonneg (neg_nonneg.2 hx)]; rw [ofReal_zero]; rw [zero_mul]; rw [add_zero]

/--
lemma `cpow_ofReal` / 引理 `cpow_ofReal`

English:
lemma cpow_ofReal
  given: (x : Complex) (y : Real)
  proof: by
  rcases eq_or_ne x 0 with rfl | hx
  · simp [ofReal_cpow le_rfl]
  · rw [cpow_def_of_ne_zero hx, exp_eq_exp_re_mul_sin_add_cos, mul_comm (log x)]
    norm_cast
    rw [re_ofReal_mul]; rw [im_ofReal_mul]; rw [log_re]; rw [log_im]; rw [mul_comm y]; rw [mul_comm y]; rw [Real.exp_mul]; rw [Real.exp_log]
    rwa [norm_pos_iff]

中文:
引理 cpow_of实数
  条件: (x : 复形) (y : 实数)
  证明: by
  rcases eq_or_ne x 0 with rfl | hx
  · simp [ofReal_cpow le_rfl]
  · rw [cpow_def_of_ne_zero hx, exp_eq_exp_re_mul_sin_add_cos, mul_comm (log x)]
    norm_cast
    rw [re_ofReal_mul]; rw [im_ofReal_mul]; rw [log_re]; rw [log_im]; rw [mul_comm y]; rw [mul_comm y]; rw [Real.exp_mul]; rw [Real.exp_log]
    rwa [norm_pos_iff]

Depends on / 依赖: Real.exp_log, Real.exp_mul, cpow_def_of_ne_zero, eq_or_ne, exp_eq_exp_re_mul_sin_add_cos, exp_log, exp_mul, im_ofReal_mul, le_rfl, log_im, log_re, mul_comm, norm_pos_iff, ofReal_cpow, re_ofReal_mul
-/
lemma cpow_ofReal (x : Complex) (y : Real) :
    x ^ (y : Complex) = ↑(‖x‖ ^ y) * (Real.cos (arg x * y) + Real.sin (arg x * y) * I) := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp [ofReal_cpow le_rfl]
  · rw [cpow_def_of_ne_zero hx, exp_eq_exp_re_mul_sin_add_cos, mul_comm (log x)]
    norm_cast
    rw [re_ofReal_mul]; rw [im_ofReal_mul]; rw [log_re]; rw [log_im]; rw [mul_comm y]; rw [mul_comm y]; rw [Real.exp_mul]; rw [Real.exp_log]
    rwa [norm_pos_iff]

/--
lemma `cpow_ofReal_re` / 引理 `cpow_ofReal_re`

English:
lemma cpow_ofReal_re
  given: (x : Complex) (y : Real)
  statement: (x ^ (y : Complex)).re = ‖x‖ ^ y * Real.cos (arg x * y)
  proof: by
  rw [cpow_ofReal]; generalize arg x * y = z; simp [Real.cos]

中文:
引理 cpow_of实数_re
  条件: (x : 复形) (y : 实数)
  结论: (x ^ (y : 复形)).re = ‖x‖ ^ y * 实数.cos (arg x * y)
  证明: by
  rw [cpow_ofReal]; generalize arg x * y = z; simp [Real.cos]

Depends on / 依赖: Real.cos, cpow_ofReal, generalize
-/
lemma cpow_ofReal_re (x : Complex) (y : Real) : (x ^ (y : Complex)).re = ‖x‖ ^ y * Real.cos (arg x * y) := by
  rw [cpow_ofReal]; generalize arg x * y = z; simp [Real.cos]

/--
lemma `cpow_ofReal_im` / 引理 `cpow_ofReal_im`

English:
lemma cpow_ofReal_im
  given: (x : Complex) (y : Real)
  statement: (x ^ (y : Complex)).im = ‖x‖ ^ y * Real.sin (arg x * y)
  proof: by
  rw [cpow_ofReal]; generalize arg x * y = z; simp [Real.sin]

中文:
引理 cpow_of实数_im
  条件: (x : 复形) (y : 实数)
  结论: (x ^ (y : 复形)).im = ‖x‖ ^ y * 实数.sin (arg x * y)
  证明: by
  rw [cpow_ofReal]; generalize arg x * y = z; simp [Real.sin]

Depends on / 依赖: Real.sin, cpow_ofReal, generalize
-/
lemma cpow_ofReal_im (x : Complex) (y : Real) : (x ^ (y : Complex)).im = ‖x‖ ^ y * Real.sin (arg x * y) := by
  rw [cpow_ofReal]; generalize arg x * y = z; simp [Real.sin]

/--
theorem `norm_cpow_of_ne_zero` / 定理 `norm_cpow_of_ne_zero`

English:
theorem norm_cpow_of_ne_zero
  given: {z : Complex} (hz : z != 0) (w : Complex)
  proof: by
  rw [cpow_def_of_ne_zero hz]; rw [norm_exp]; rw [mul_re]; rw [log_re]; rw [log_im]; rw [Real.exp_sub]; rw [Real.rpow_def_of_pos (norm_pos_iff.mpr hz)]

中文:
定理 norm_cpow_of_ne_zero
  条件: {z : 复形} (hz : z != 0) (w : 复形)
  证明: by
  rw [cpow_def_of_ne_zero hz]; rw [norm_exp]; rw [mul_re]; rw [log_re]; rw [log_im]; rw [Real.exp_sub]; rw [Real.rpow_def_of_pos (norm_pos_iff.mpr hz)]

Depends on / 依赖: Real.exp_sub, Real.rpow_def_of_pos, cpow_def_of_ne_zero, exp_sub, log_im, log_re, mul_re, norm_exp, norm_pos_iff, norm_pos_iff.mpr, rpow_def_of_pos
-/
theorem norm_cpow_of_ne_zero {z : Complex} (hz : z != 0) (w : Complex) :
    ‖z ^ w‖ = ‖z‖ ^ w.re / Real.exp (arg z * im w) := by
  rw [cpow_def_of_ne_zero hz]; rw [norm_exp]; rw [mul_re]; rw [log_re]; rw [log_im]; rw [Real.exp_sub]; rw [Real.rpow_def_of_pos (norm_pos_iff.mpr hz)]

/--
theorem `norm_cpow_of_imp` / 定理 `norm_cpow_of_imp`

English:
theorem norm_cpow_of_imp
  given: {z w : Complex} (h : z = 0 -> w.re = 0 -> w = 0)
  proof: by
  rcases ne_or_eq z 0 with (hz | rfl) <;> [exact norm_cpow_of_ne_zero hz w; rw [norm_zero]]
  rcases eq_or_ne w.re 0 with hw | hw
  · simp [h rfl hw]
  · rw [Real.zero_rpow hw, zero_div, zero_cpow, norm_zero]
    exact ne_of_apply_ne re hw

中文:
定理 norm_cpow_of_imp
  条件: {z w : 复形} (h : z = 0 -> w.re = 0 -> w = 0)
  证明: by
  rcases ne_or_eq z 0 with (hz | rfl) <;> [exact norm_cpow_of_ne_zero hz w; rw [norm_zero]]
  rcases eq_or_ne w.re 0 with hw | hw
  · simp [h rfl hw]
  · rw [Real.zero_rpow hw, zero_div, zero_cpow, norm_zero]
    exact ne_of_apply_ne re hw

Depends on / 依赖: Real.zero_rpow, eq_or_ne, ne_of_apply_ne, ne_or_eq, norm_cpow_of_ne_zero, norm_zero, w.re, zero_cpow, zero_div, zero_rpow
-/
theorem norm_cpow_of_imp {z w : Complex} (h : z = 0 -> w.re = 0 -> w = 0) :
    ‖z ^ w‖ = ‖z‖ ^ w.re / Real.exp (arg z * im w) := by
  rcases ne_or_eq z 0 with (hz | rfl) <;> [exact norm_cpow_of_ne_zero hz w; rw [norm_zero]]
  rcases eq_or_ne w.re 0 with hw | hw
  · simp [h rfl hw]
  · rw [Real.zero_rpow hw, zero_div, zero_cpow, norm_zero]
    exact ne_of_apply_ne re hw

/--
theorem `norm_cpow_le` / 定理 `norm_cpow_le`

English:
theorem norm_cpow_le
  given: (z w : Complex)
  statement: ‖z ^ w‖ <= ‖z‖ ^ w.re / Real.exp (arg z * im w)
  proof: by
  by_cases! h : z = 0 -> w.re = 0 -> w = 0
  · exact (norm_cpow_of_imp h).le
  · simp [h]

@[simp]

中文:
定理 norm_cpow_le
  条件: (z w : 复形)
  结论: ‖z ^ w‖ <= ‖z‖ ^ w.re / 实数.exp (arg z * im w)
  证明: by
  by_cases! h : z = 0 -> w.re = 0 -> w = 0
  · exact (norm_cpow_of_imp h).le
  · simp [h]

@[simp]

Depends on / 依赖: norm_cpow_of_imp, w.re
-/
theorem norm_cpow_le (z w : Complex) : ‖z ^ w‖ <= ‖z‖ ^ w.re / Real.exp (arg z * im w) := by
  by_cases! h : z = 0 -> w.re = 0 -> w = 0
  · exact (norm_cpow_of_imp h).le
  · simp [h]

@[simp]
/--
theorem `norm_cpow_real` / 定理 `norm_cpow_real`

English:
theorem norm_cpow_real
  given: (x : Complex) (y : Real)
  statement: ‖x ^ (y : Complex)‖ = ‖x‖ ^ y
  proof: by
  rw [norm_cpow_of_imp] <;> simp

@[simp]

中文:
定理 norm_cpow_real
  条件: (x : 复形) (y : 实数)
  结论: ‖x ^ (y : 复形)‖ = ‖x‖ ^ y
  证明: by
  rw [norm_cpow_of_imp] <;> simp

@[simp]

Depends on / 依赖: norm_cpow_of_imp
-/
theorem norm_cpow_real (x : Complex) (y : Real) : ‖x ^ (y : Complex)‖ = ‖x‖ ^ y := by
  rw [norm_cpow_of_imp] <;> simp

@[simp]
/--
theorem `norm_cpow_inv_nat` / 定理 `norm_cpow_inv_nat`

English:
theorem norm_cpow_inv_nat
  given: (x : Complex) (n : Nat)
  statement: ‖x ^ (n⁻¹ : Complex)‖ = ‖x‖ ^ (n⁻¹ : Real)
  proof: by
  rw [← norm_cpow_real]; simp

中文:
定理 norm_cpow_inv_nat
  条件: (x : 复形) (n : 自然数)
  结论: ‖x ^ (n⁻¹ : 复形)‖ = ‖x‖ ^ (n⁻¹ : 实数)
  证明: by
  rw [← norm_cpow_real]; simp

Depends on / 依赖: norm_cpow_real
-/
theorem norm_cpow_inv_nat (x : Complex) (n : Nat) : ‖x ^ (n⁻¹ : Complex)‖ = ‖x‖ ^ (n⁻¹ : Real) := by
  rw [← norm_cpow_real]; simp

/--
theorem `norm_cpow_eq_rpow_re_of_pos` / 定理 `norm_cpow_eq_rpow_re_of_pos`

English:
theorem norm_cpow_eq_rpow_re_of_pos
  given: {x : Real} (hx : 0 < x) (y : Complex)
  statement: ‖(x : Complex) ^ y‖ = x ^ y.re
  proof: by
  rw [norm_cpow_of_ne_zero (ofReal_ne_zero.mpr hx.ne')]; rw [arg_ofReal_of_nonneg hx.le]; rw [zero_mul]; rw [Real.exp_zero]; rw [div_one]; rw [Complex.norm_of_nonneg hx.le]

中文:
定理 norm_cpow_eq_rpow_re_of_pos
  条件: {x : 实数} (hx : 0 < x) (y : 复形)
  结论: ‖(x : 复形) ^ y‖ = x ^ y.re
  证明: by
  rw [norm_cpow_of_ne_zero (ofReal_ne_zero.mpr hx.ne')]; rw [arg_ofReal_of_nonneg hx.le]; rw [zero_mul]; rw [Real.exp_zero]; rw [div_one]; rw [Complex.norm_of_nonneg hx.le]

Depends on / 依赖: Complex.norm_of_nonneg, Real.exp_zero, arg_ofReal_of_nonneg, div_one, exp_zero, hx.le, hx.ne, norm_cpow_of_ne_zero, norm_of_nonneg, ofReal_ne_zero, ofReal_ne_zero.mpr, zero_mul
-/
theorem norm_cpow_eq_rpow_re_of_pos {x : Real} (hx : 0 < x) (y : Complex) : ‖(x : Complex) ^ y‖ = x ^ y.re := by
  rw [norm_cpow_of_ne_zero (ofReal_ne_zero.mpr hx.ne')]; rw [arg_ofReal_of_nonneg hx.le]; rw [zero_mul]; rw [Real.exp_zero]; rw [div_one]; rw [Complex.norm_of_nonneg hx.le]

/--
theorem `norm_cpow_eq_rpow_re_of_nonneg` / 定理 `norm_cpow_eq_rpow_re_of_nonneg`

English:
theorem norm_cpow_eq_rpow_re_of_nonneg
  given: {x : Real} (hx : 0 <= x) {y : Complex} (hy : re y != 0)
  proof: by
  rw [norm_cpow_of_imp] <;> simp [*, arg_ofReal_of_nonneg, abs_of_nonneg]

中文:
定理 norm_cpow_eq_rpow_re_of_nonneg
  条件: {x : 实数} (hx : 0 <= x) {y : 复形} (hy : re y != 0)
  证明: by
  rw [norm_cpow_of_imp] <;> simp [*, arg_ofReal_of_nonneg, abs_of_nonneg]

Depends on / 依赖: abs_of_nonneg, arg_ofReal_of_nonneg, norm_cpow_of_imp
-/
theorem norm_cpow_eq_rpow_re_of_nonneg {x : Real} (hx : 0 <= x) {y : Complex} (hy : re y != 0) :
    ‖(x : Complex) ^ y‖ = x ^ re y := by
  rw [norm_cpow_of_imp] <;> simp [*, arg_ofReal_of_nonneg, abs_of_nonneg]

open Filter in
/--
lemma `norm_ofReal_cpow_eventually_eq_atTop` / 引理 `norm_ofReal_cpow_eventually_eq_atTop`

English:
lemma norm_ofReal_cpow_eventually_eq_atTop
  given: (c : Complex)
  proof: by
  filter_upwards [eventually_gt_atTop 0] with t ht
  rw [norm_cpow_eq_rpow_re_of_pos ht]

中文:
引理 norm_of实数_cpow_eventually_eq_atTop
  条件: (c : 复形)
  证明: by
  filter_upwards [eventually_gt_atTop 0] with t ht
  rw [norm_cpow_eq_rpow_re_of_pos ht]

Depends on / 依赖: eventually_gt_atTop, filter_upwards, norm_cpow_eq_rpow_re_of_pos
-/
lemma norm_ofReal_cpow_eventually_eq_atTop (c : Complex) :
    (fun t : Real => ‖(t : Complex) ^ c‖) =ᶠ[atTop] fun t => t ^ c.re := by
  filter_upwards [eventually_gt_atTop 0] with t ht
  rw [norm_cpow_eq_rpow_re_of_pos ht]

/--
lemma `norm_natCast_cpow_of_re_ne_zero` / 引理 `norm_natCast_cpow_of_re_ne_zero`

English:
lemma norm_natCast_cpow_of_re_ne_zero
  given: (n : Nat) {s : Complex} (hs : s.re != 0)
  proof: by
  rw [← ofReal_natCast]; rw [norm_cpow_eq_rpow_re_of_nonneg n.cast_nonneg hs]

中文:
引理 norm_natCast_cpow_of_re_ne_zero
  条件: (n : 自然数) {s : 复形} (hs : s.re != 0)
  证明: by
  rw [← ofReal_natCast]; rw [norm_cpow_eq_rpow_re_of_nonneg n.cast_nonneg hs]

Depends on / 依赖: cast_nonneg, n.cast_nonneg, norm_cpow_eq_rpow_re_of_nonneg, ofReal_natCast
-/
lemma norm_natCast_cpow_of_re_ne_zero (n : Nat) {s : Complex} (hs : s.re != 0) :
    ‖(n : Complex) ^ s‖ = (n : Real) ^ (s.re) := by
  rw [← ofReal_natCast]; rw [norm_cpow_eq_rpow_re_of_nonneg n.cast_nonneg hs]

/--
lemma `norm_natCast_cpow_of_pos` / 引理 `norm_natCast_cpow_of_pos`

English:
lemma norm_natCast_cpow_of_pos
  given: {n : Nat} (hn : 0 < n) (s : Complex)
  proof: by
  rw [← ofReal_natCast]; rw [norm_cpow_eq_rpow_re_of_pos (Nat.cast_pos.mpr hn) _]

中文:
引理 norm_natCast_cpow_of_pos
  条件: {n : 自然数} (hn : 0 < n) (s : 复形)
  证明: by
  rw [← ofReal_natCast]; rw [norm_cpow_eq_rpow_re_of_pos (Nat.cast_pos.mpr hn) _]

Depends on / 依赖: Nat.cast_pos.mpr, cast_pos, norm_cpow_eq_rpow_re_of_pos, ofReal_natCast
-/
lemma norm_natCast_cpow_of_pos {n : Nat} (hn : 0 < n) (s : Complex) :
    ‖(n : Complex) ^ s‖ = (n : Real) ^ (s.re) := by
  rw [← ofReal_natCast]; rw [norm_cpow_eq_rpow_re_of_pos (Nat.cast_pos.mpr hn) _]

/--
lemma `norm_natCast_cpow_pos_of_pos` / 引理 `norm_natCast_cpow_pos_of_pos`

English:
lemma norm_natCast_cpow_pos_of_pos
  given: {n : Nat} (hn : 0 < n) (s : Complex)
  statement: 0 < ‖(n : Complex) ^ s‖
  proof: (norm_natCast_cpow_of_pos hn _).symm ▸ Real.rpow_pos_of_pos (Nat.cast_pos.mpr hn) _

中文:
引理 norm_natCast_cpow_pos_of_pos
  条件: {n : 自然数} (hn : 0 < n) (s : 复形)
  结论: 0 < ‖(n : 复形) ^ s‖
  证明: (norm_natCast_cpow_of_pos hn _).symm ▸ Real.rpow_pos_of_pos (Nat.cast_pos.mpr hn) _

Depends on / 依赖: Nat.cast_pos.mpr, Real.rpow_pos_of_pos, cast_pos, norm_natCast_cpow_of_pos, rpow_pos_of_pos
-/
lemma norm_natCast_cpow_pos_of_pos {n : Nat} (hn : 0 < n) (s : Complex) : 0 < ‖(n : Complex) ^ s‖ :=
  (norm_natCast_cpow_of_pos hn _).symm ▸ Real.rpow_pos_of_pos (Nat.cast_pos.mpr hn) _

/--
theorem `cpow_mul_ofReal_nonneg` / 定理 `cpow_mul_ofReal_nonneg`

English:
theorem cpow_mul_ofReal_nonneg
  given: {x : Real} (hx : 0 <= x) (y : Real) (z : Complex)
  proof: by
  rw [cpow_mul]; rw [ofReal_cpow hx]
  · rw [← ofReal_log hx, ← ofReal_mul, ofReal_im, neg_lt_zero]; exact Real.pi_pos
  · rw [← ofReal_log hx, ← ofReal_mul, ofReal_im]; exact Real.pi_pos.le

中文:
定理 cpow_mul_of实数_nonneg
  条件: {x : 实数} (hx : 0 <= x) (y : 实数) (z : 复形)
  证明: by
  rw [cpow_mul]; rw [ofReal_cpow hx]
  · rw [← ofReal_log hx, ← ofReal_mul, ofReal_im, neg_lt_zero]; exact Real.pi_pos
  · rw [← ofReal_log hx, ← ofReal_mul, ofReal_im]; exact Real.pi_pos.le

Depends on / 依赖: Real.pi_pos, Real.pi_pos.le, cpow_mul, neg_lt_zero, ofReal_cpow, ofReal_im, ofReal_log, ofReal_mul, pi_pos
-/
theorem cpow_mul_ofReal_nonneg {x : Real} (hx : 0 <= x) (y : Real) (z : Complex) :
    (x : Complex) ^ (↑y * z) = (↑(x ^ y) : Complex) ^ z := by
  rw [cpow_mul]; rw [ofReal_cpow hx]
  · rw [← ofReal_log hx, ← ofReal_mul, ofReal_im, neg_lt_zero]; exact Real.pi_pos
  · rw [← ofReal_log hx, ← ofReal_mul, ofReal_im]; exact Real.pi_pos.le

end Complex

/-! ### Positivity extension -/

namespace Mathlib.Meta.Positivity
open Lean Meta Qq

/-- Extension for the `positivity` tactic: exponentiation by a real number is positive (namely 1)
when the exponent is zero. The other cases are done in `evalRpow`. -/
@[positivity (_ : Real) ^ (0 : Real)]
meta def evalRpowZero : PositivityExt where eval {u α} _ pα? e :=
  match pα? with | none => pure .none | some _ => do
  match u, α, e with
  | 0, ~q(Real), ~q($a ^ (0 : Real)) =>
    assertInstancesCommute
    pure (.positive q(Real.rpow_zero_pos $a))
  | _, _, _ => throwError "not Real.rpow"

/-- Extension for the `positivity` tactic: exponentiation by a real number is nonnegative when
the base is nonnegative and positive when the base is positive. -/
@[positivity (_ : Real) ^ (_ : Real)]
meta def evalRpow : PositivityExt where eval {u α} _zα pα? e :=
  match pα? with | none => pure .none | some _ => do
  match u, α, e with
  | 0, ~q(Real), ~q($a ^ ($b : Real)) =>
    assertInstancesCommute
    let ra ← core q(inferInstance) (some q(inferInstance)) a
    match ra with
    | .positive pa =>
      pure (.positive q(Real.rpow_pos_of_pos $pa $b))
    | .nonnegative pa =>
      pure (.nonnegative q(Real.rpow_nonneg $pa $b))
    | _ => pure .none
  | _, _, _ => throwError "not Real.rpow"

end Mathlib.Meta.Positivity

/--
theorem `log_rpow` / 定理 `log_rpow`

English:
theorem log_rpow
  given: {x : Real} (hx : 0 < x) (y : Real)
  statement: log (x ^ y) = y * log x
  proof: by
  apply exp_injective
  rw [exp_log (rpow_pos_of_pos hx y)]; rw [← exp_log hx]; rw [mul_comm]; rw [rpow_def_of_pos (exp_pos (log x)) y]

中文:
定理 log_rpow
  条件: {x : 实数} (hx : 0 < x) (y : 实数)
  结论: log (x ^ y) = y * log x
  证明: by
  apply exp_injective
  rw [exp_log (rpow_pos_of_pos hx y)]; rw [← exp_log hx]; rw [mul_comm]; rw [rpow_def_of_pos (exp_pos (log x)) y]

Depends on / 依赖: exp_injective, exp_log, exp_pos, mul_comm, rpow_def_of_pos, rpow_pos_of_pos
-/
theorem log_rpow {x : Real} (hx : 0 < x) (y : Real) : log (x ^ y) = y * log x := by
  apply exp_injective
  rw [exp_log (rpow_pos_of_pos hx y)]; rw [← exp_log hx]; rw [mul_comm]; rw [rpow_def_of_pos (exp_pos (log x)) y]

/--
theorem `mul_log_eq_log_iff` / 定理 `mul_log_eq_log_iff`

English:
theorem mul_log_eq_log_iff
  given: {x y z : Real} (hx : 0 < x) (hz : 0 < z)
  proof: ⟨fun h => log_injOn_pos (rpow_pos_of_pos hx _) hz .trans h, log_rpow hx _
  by rintro rfl; rw [log_rpow hx]⟩

中文:
定理 mul_log_eq_log_iff
  条件: {x y z : 实数} (hx : 0 < x) (hz : 0 < z)
  证明: ⟨fun h => log_injOn_pos (rpow_pos_of_pos hx _) hz .trans h, log_rpow hx _
  by rintro rfl; rw [log_rpow hx]⟩

Depends on / 依赖: log_injOn_pos, log_rpow, rpow_pos_of_pos
-/
theorem mul_log_eq_log_iff {x y z : Real} (hx : 0 < x) (hz : 0 < z) :
    y * log x = log z ↔ x ^ y = z :=
⟨fun h => log_injOn_pos (rpow_pos_of_pos hx _) hz .trans h, log_rpow hx _
  by rintro rfl; rw [log_rpow hx]⟩

/--
lemma `rpow_rpow_inv` / 引理 `rpow_rpow_inv`

English:
lemma rpow_rpow_inv
  given: (hx : 0 <= x) (hy : y != 0)
  statement: (x ^ y) ^ y⁻¹ = x
  proof: by
  rw [← rpow_mul hx]; rw [mul_inv_cancel₀ hy]; rw [rpow_one]

中文:
引理 rpow_rpow_inv
  条件: (hx : 0 <= x) (hy : y != 0)
  结论: (x ^ y) ^ y⁻¹ = x
  证明: by
  rw [← rpow_mul hx]; rw [mul_inv_cancel₀ hy]; rw [rpow_one]
-/
@[simp] lemma rpow_rpow_inv (hx : 0 <= x) (hy : y != 0) : (x ^ y) ^ y⁻¹ = x := by
  rw [← rpow_mul hx]; rw [mul_inv_cancel₀ hy]; rw [rpow_one]

/--
lemma `rpow_inv_rpow` / 引理 `rpow_inv_rpow`

English:
lemma rpow_inv_rpow
  given: (hx : 0 <= x) (hy : y != 0)
  statement: (x ^ y⁻¹) ^ y = x
  proof: by
  rw [← rpow_mul hx]; rw [inv_mul_cancel₀ hy]; rw [rpow_one]

中文:
引理 rpow_inv_rpow
  条件: (hx : 0 <= x) (hy : y != 0)
  结论: (x ^ y⁻¹) ^ y = x
  证明: by
  rw [← rpow_mul hx]; rw [inv_mul_cancel₀ hy]; rw [rpow_one]
-/
@[simp] lemma rpow_inv_rpow (hx : 0 <= x) (hy : y != 0) : (x ^ y⁻¹) ^ y = x := by
  rw [← rpow_mul hx]; rw [inv_mul_cancel₀ hy]; rw [rpow_one]

/--
theorem `pow_rpow_inv_natCast` / 定理 `pow_rpow_inv_natCast`

English:
theorem pow_rpow_inv_natCast
  given: (hx : 0 <= x) (hn : n != 0)
  statement: (x ^ n) ^ (n⁻¹ : Real) = x
  proof: by
  have hn0 : (n : Real) != 0 := Nat.cast_ne_zero.2 hn
  rw [← rpow_natCast]; rw [← rpow_mul hx]; rw [mul_inv_cancel₀ hn0]; rw [rpow_one]

中文:
定理 pow_rpow_inv_natCast
  条件: (hx : 0 <= x) (hn : n != 0)
  结论: (x ^ n) ^ (n⁻¹ : 实数) = x
  证明: by
  have hn0 : (n : Real) != 0 := Nat.cast_ne_zero.2 hn
  rw [← rpow_natCast]; rw [← rpow_mul hx]; rw [mul_inv_cancel₀ hn0]; rw [rpow_one]

Depends on / 依赖: Nat.cast_ne_zero, cast_ne_zero, rpow_mul, rpow_natCast, rpow_one
-/
theorem pow_rpow_inv_natCast (hx : 0 <= x) (hn : n != 0) : (x ^ n) ^ (n⁻¹ : Real) = x := by
  have hn0 : (n : Real) != 0 := Nat.cast_ne_zero.2 hn
  rw [← rpow_natCast]; rw [← rpow_mul hx]; rw [mul_inv_cancel₀ hn0]; rw [rpow_one]

/--
theorem `rpow_inv_natCast_pow` / 定理 `rpow_inv_natCast_pow`

English:
theorem rpow_inv_natCast_pow
  given: (hx : 0 <= x) (hn : n != 0)
  statement: (x ^ (n⁻¹ : Real)) ^ n = x
  proof: by
  have hn0 : (n : Real) != 0 := Nat.cast_ne_zero.2 hn
  rw [← rpow_natCast]; rw [← rpow_mul hx]; rw [inv_mul_cancel₀ hn0]; rw [rpow_one]

中文:
定理 rpow_inv_natCast_pow
  条件: (hx : 0 <= x) (hn : n != 0)
  结论: (x ^ (n⁻¹ : 实数)) ^ n = x
  证明: by
  have hn0 : (n : Real) != 0 := Nat.cast_ne_zero.2 hn
  rw [← rpow_natCast]; rw [← rpow_mul hx]; rw [inv_mul_cancel₀ hn0]; rw [rpow_one]

Depends on / 依赖: Nat.cast_ne_zero, cast_ne_zero, rpow_mul, rpow_natCast, rpow_one
-/
theorem rpow_inv_natCast_pow (hx : 0 <= x) (hn : n != 0) : (x ^ (n⁻¹ : Real)) ^ n = x := by
  have hn0 : (n : Real) != 0 := Nat.cast_ne_zero.2 hn
  rw [← rpow_natCast]; rw [← rpow_mul hx]; rw [inv_mul_cancel₀ hn0]; rw [rpow_one]

/--
lemma `rpow_natCast_mul` / 引理 `rpow_natCast_mul`

English:
lemma rpow_natCast_mul
  given: (hx : 0 <= x) (n : Nat) (z : Real)
  statement: x ^ (n * z) = (x ^ n) ^ z
  proof: by
  rw [rpow_mul hx]; rw [rpow_natCast]

中文:
引理 rpow_natCast_mul
  条件: (hx : 0 <= x) (n : 自然数) (z : 实数)
  结论: x ^ (n * z) = (x ^ n) ^ z
  证明: by
  rw [rpow_mul hx]; rw [rpow_natCast]

Depends on / 依赖: rpow_mul, rpow_natCast
-/
lemma rpow_natCast_mul (hx : 0 <= x) (n : Nat) (z : Real) : x ^ (n * z) = (x ^ n) ^ z := by
  rw [rpow_mul hx]; rw [rpow_natCast]

/--
lemma `rpow_mul_natCast` / 引理 `rpow_mul_natCast`

English:
lemma rpow_mul_natCast
  given: (hx : 0 <= x) (y : Real) (n : Nat)
  statement: x ^ (y * n) = (x ^ y) ^ n
  proof: by
  rw [rpow_mul hx]; rw [rpow_natCast]

中文:
引理 rpow_mul_natCast
  条件: (hx : 0 <= x) (y : 实数) (n : 自然数)
  结论: x ^ (y * n) = (x ^ y) ^ n
  证明: by
  rw [rpow_mul hx]; rw [rpow_natCast]

Depends on / 依赖: rpow_mul, rpow_natCast
-/
lemma rpow_mul_natCast (hx : 0 <= x) (y : Real) (n : Nat) : x ^ (y * n) = (x ^ y) ^ n := by
  rw [rpow_mul hx]; rw [rpow_natCast]

/--
lemma `rpow_intCast_mul` / 引理 `rpow_intCast_mul`

English:
lemma rpow_intCast_mul
  given: (hx : 0 <= x) (n : Int) (z : Real)
  statement: x ^ (n * z) = (x ^ n) ^ z
  proof: by
  rw [rpow_mul hx]; rw [rpow_intCast]

中文:
引理 rpow_intCast_mul
  条件: (hx : 0 <= x) (n : 整数) (z : 实数)
  结论: x ^ (n * z) = (x ^ n) ^ z
  证明: by
  rw [rpow_mul hx]; rw [rpow_intCast]

Depends on / 依赖: rpow_intCast, rpow_mul
-/
lemma rpow_intCast_mul (hx : 0 <= x) (n : Int) (z : Real) : x ^ (n * z) = (x ^ n) ^ z := by
  rw [rpow_mul hx]; rw [rpow_intCast]

/--
lemma `rpow_mul_intCast` / 引理 `rpow_mul_intCast`

English:
lemma rpow_mul_intCast
  given: (hx : 0 <= x) (y : Real) (n : Int)
  statement: x ^ (y * n) = (x ^ y) ^ n
  proof: by
  rw [rpow_mul hx]; rw [rpow_intCast]

中文:
引理 rpow_mul_intCast
  条件: (hx : 0 <= x) (y : 实数) (n : 整数)
  结论: x ^ (y * n) = (x ^ y) ^ n
  证明: by
  rw [rpow_mul hx]; rw [rpow_intCast]

Depends on / 依赖: DecidableEq, Pairwise, Pairwise.Hom, rpow_intCast, rpow_mul
-/
lemma rpow_mul_intCast (hx : 0 <= x) (y : Real) (n : Int) : x ^ (y * n) = (x ^ y) ^ n := by
  rw [rpow_mul hx]; rw [rpow_intCast]

/-! Note: lemmas about `(∏ i ∈ s, f i ^ r)` such as `Real.finsetProd_rpow` are proved
in `Mathlib/Analysis/SpecialFunctions/Pow/NNReal.lean` instead. -/

/-!
## Order and monotonicity
-/


@[gcongr, bound]
/--
theorem `rpow_lt_rpow` / 定理 `rpow_lt_rpow`

English:
theorem rpow_lt_rpow
  given: (hx : 0 <= x) (hxy : x < y) (hz : 0 < z)
  statement: x ^ z < y ^ z
  proof: by
  rw [le_iff_eq_or_lt] at hx; rcases hx with hx | hx
  · rw [← hx, zero_rpow (ne_of_gt hz)]
    exact rpow_pos_of_pos (by rwa [← hx] at hxy) _
  · rw [rpow_def_of_pos hx, rpow_def_of_pos (lt_trans hx hxy), exp_lt_exp]
    exact mul_lt_mul_of_pos_right (log_lt_log hx hxy) hz

中文:
定理 rpow_lt_rpow
  条件: (hx : 0 <= x) (hxy : x < y) (hz : 0 < z)
  结论: x ^ z < y ^ z
  证明: by
  rw [le_iff_eq_or_lt] at hx; rcases hx with hx | hx
  · rw [← hx, zero_rpow (ne_of_gt hz)]
    exact rpow_pos_of_pos (by rwa [← hx] at hxy) _
  · rw [rpow_def_of_pos hx, rpow_def_of_pos (lt_trans hx hxy), exp_lt_exp]
    exact mul_lt_mul_of_pos_right (log_lt_log hx hxy) hz

Depends on / 依赖: exp_lt_exp, le_iff_eq_or_lt, log_lt_log, lt_trans, mul_lt_mul_of_pos_right, ne_of_gt, rpow_def_of_pos, rpow_pos_of_pos, zero_rpow
-/
theorem rpow_lt_rpow (hx : 0 <= x) (hxy : x < y) (hz : 0 < z) : x ^ z < y ^ z := by
  rw [le_iff_eq_or_lt] at hx; rcases hx with hx | hx
  · rw [← hx, zero_rpow (ne_of_gt hz)]
    exact rpow_pos_of_pos (by rwa [← hx] at hxy) _
  · rw [rpow_def_of_pos hx, rpow_def_of_pos (lt_trans hx hxy), exp_lt_exp]
    exact mul_lt_mul_of_pos_right (log_lt_log hx hxy) hz

/--
theorem `strictMonoOn_rpow_Ici_of_exponent_pos` / 定理 `strictMonoOn_rpow_Ici_of_exponent_pos`

English:
theorem strictMonoOn_rpow_Ici_of_exponent_pos
  given: {r : Real} (hr : 0 < r)
  proof: fun _ ha _ _ hab => rpow_lt_rpow ha hab hr

@[gcongr, bound]

中文:
定理 strictMonoOn_rpow_Ici_of_exponent_pos
  条件: {r : 实数} (hr : 0 < r)
  证明: fun _ ha _ _ hab => rpow_lt_rpow ha hab hr

@[gcongr, bound]

Depends on / 依赖: rpow_lt_rpow
-/
theorem strictMonoOn_rpow_Ici_of_exponent_pos {r : Real} (hr : 0 < r) :
    StrictMonoOn (fun (x : Real) => x ^ r) (Set.Ici 0) :=
  fun _ ha _ _ hab => rpow_lt_rpow ha hab hr

@[gcongr, bound]
/--
theorem `rpow_le_rpow` / 定理 `rpow_le_rpow`

English:
theorem rpow_le_rpow
  given: {x y z : Real} (h : 0 <= x) (h₁ : x <= y) (h₂ : 0 <= z)
  statement: x ^ z <= y ^ z
  proof: by
  rcases eq_or_lt_of_le h₁ with (rfl | h₁'); · rfl
  rcases eq_or_lt_of_le h₂ with (rfl | h₂'); · simp
  exact le_of_lt (rpow_lt_rpow h h₁' h₂')

中文:
定理 rpow_le_rpow
  条件: {x y z : 实数} (h : 0 <= x) (h₁ : x <= y) (h₂ : 0 <= z)
  结论: x ^ z <= y ^ z
  证明: by
  rcases eq_or_lt_of_le h₁ with (rfl | h₁'); · rfl
  rcases eq_or_lt_of_le h₂ with (rfl | h₂'); · simp
  exact le_of_lt (rpow_lt_rpow h h₁' h₂')

Depends on / 依赖: eq_or_lt_of_le, le_of_lt, rpow_lt_rpow
-/
theorem rpow_le_rpow {x y z : Real} (h : 0 <= x) (h₁ : x <= y) (h₂ : 0 <= z) : x ^ z <= y ^ z := by
  rcases eq_or_lt_of_le h₁ with (rfl | h₁'); · rfl
  rcases eq_or_lt_of_le h₂ with (rfl | h₂'); · simp
  exact le_of_lt (rpow_lt_rpow h h₁' h₂')

/--
theorem `monotoneOn_rpow_Ici_of_exponent_nonneg` / 定理 `monotoneOn_rpow_Ici_of_exponent_nonneg`

English:
theorem monotoneOn_rpow_Ici_of_exponent_nonneg
  given: {r : Real} (hr : 0 <= r)
  proof: fun _ ha _ _ hab => rpow_le_rpow ha hab hr

中文:
定理 monotoneOn_rpow_Ici_of_exponent_nonneg
  条件: {r : 实数} (hr : 0 <= r)
  证明: fun _ ha _ _ hab => rpow_le_rpow ha hab hr

Depends on / 依赖: rpow_le_rpow
-/
theorem monotoneOn_rpow_Ici_of_exponent_nonneg {r : Real} (hr : 0 <= r) :
    MonotoneOn (fun (x : Real) => x ^ r) (Set.Ici 0) :=
  fun _ ha _ _ hab => rpow_le_rpow ha hab hr

/--
lemma `rpow_lt_rpow_of_neg` / 引理 `rpow_lt_rpow_of_neg`

English:
lemma rpow_lt_rpow_of_neg
  given: (hx : 0 < x) (hxy : x < y) (hz : z < 0)
  statement: y ^ z < x ^ z
  proof: by
  have := hx.trans hxy
  rw [← inv_lt_inv₀]; rw [← rpow_neg]; rw [← rpow_neg]
  on_goal 1 => refine rpow_lt_rpow ?_ hxy (neg_pos.2 hz)
  all_goals positivity

中文:
引理 rpow_lt_rpow_of_neg
  条件: (hx : 0 < x) (hxy : x < y) (hz : z < 0)
  结论: y ^ z < x ^ z
  证明: by
  have := hx.trans hxy
  rw [← inv_lt_inv₀]; rw [← rpow_neg]; rw [← rpow_neg]
  on_goal 1 => refine rpow_lt_rpow ?_ hxy (neg_pos.2 hz)
  all_goals positivity

Depends on / 依赖: all_goals, hx.trans, neg_pos, on_goal, rpow_lt_rpow, rpow_neg
-/
lemma rpow_lt_rpow_of_neg (hx : 0 < x) (hxy : x < y) (hz : z < 0) : y ^ z < x ^ z := by
  have := hx.trans hxy
  rw [← inv_lt_inv₀]; rw [← rpow_neg]; rw [← rpow_neg]
  on_goal 1 => refine rpow_lt_rpow ?_ hxy (neg_pos.2 hz)
  all_goals positivity

/--
lemma `rpow_le_rpow_of_nonpos` / 引理 `rpow_le_rpow_of_nonpos`

English:
lemma rpow_le_rpow_of_nonpos
  given: (hx : 0 < x) (hxy : x <= y) (hz : z <= 0)
  statement: y ^ z <= x ^ z
  proof: by
  have := hx.trans_le hxy
  rw [← inv_le_inv₀]; rw [← rpow_neg]; rw [← rpow_neg]
  on_goal 1 => refine rpow_le_rpow ?_ hxy (neg_nonneg.2 hz)
  all_goals positivity

中文:
引理 rpow_le_rpow_of_nonpos
  条件: (hx : 0 < x) (hxy : x <= y) (hz : z <= 0)
  结论: y ^ z <= x ^ z
  证明: by
  have := hx.trans_le hxy
  rw [← inv_le_inv₀]; rw [← rpow_neg]; rw [← rpow_neg]
  on_goal 1 => refine rpow_le_rpow ?_ hxy (neg_nonneg.2 hz)
  all_goals positivity

Depends on / 依赖: all_goals, hx.trans_le, neg_nonneg, on_goal, rpow_le_rpow, rpow_neg, trans_le
-/
lemma rpow_le_rpow_of_nonpos (hx : 0 < x) (hxy : x <= y) (hz : z <= 0) : y ^ z <= x ^ z := by
  have := hx.trans_le hxy
  rw [← inv_le_inv₀]; rw [← rpow_neg]; rw [← rpow_neg]
  on_goal 1 => refine rpow_le_rpow ?_ hxy (neg_nonneg.2 hz)
  all_goals positivity

/--
theorem `rpow_lt_rpow_iff` / 定理 `rpow_lt_rpow_iff`

English:
theorem rpow_lt_rpow_iff
  given: (hx : 0 <= x) (hy : 0 <= y) (hz : 0 < z)
  statement: x ^ z < y ^ z ↔ x < y
  proof: ⟨lt_imp_lt_of_le_imp_le fun h => by gcongr, fun h => by gcongr⟩

中文:
定理 rpow_lt_rpow_iff
  条件: (hx : 0 <= x) (hy : 0 <= y) (hz : 0 < z)
  结论: x ^ z < y ^ z ↔ x < y
  证明: ⟨lt_imp_lt_of_le_imp_le fun h => by gcongr, fun h => by gcongr⟩

Depends on / 依赖: lt_imp_lt_of_le_imp_le
-/
theorem rpow_lt_rpow_iff (hx : 0 <= x) (hy : 0 <= y) (hz : 0 < z) : x ^ z < y ^ z ↔ x < y :=
  ⟨lt_imp_lt_of_le_imp_le fun h => by gcongr, fun h => by gcongr⟩

/--
theorem `rpow_le_rpow_iff` / 定理 `rpow_le_rpow_iff`

English:
theorem rpow_le_rpow_iff
  given: (hx : 0 <= x) (hy : 0 <= y) (hz : 0 < z)
  statement: x ^ z <= y ^ z ↔ x <= y
  proof: le_iff_le_iff_lt_iff_lt.2 rpow_lt_rpow_iff hy hx hz

中文:
定理 rpow_le_rpow_iff
  条件: (hx : 0 <= x) (hy : 0 <= y) (hz : 0 < z)
  结论: x ^ z <= y ^ z ↔ x <= y
  证明: le_iff_le_iff_lt_iff_lt.2 rpow_lt_rpow_iff hy hx hz

Depends on / 依赖: le_iff_le_iff_lt_iff_lt, rpow_lt_rpow_iff
-/
theorem rpow_le_rpow_iff (hx : 0 <= x) (hy : 0 <= y) (hz : 0 < z) : x ^ z <= y ^ z ↔ x <= y :=
le_iff_le_iff_lt_iff_lt.2 rpow_lt_rpow_iff hy hx hz

/--
lemma `rpow_lt_rpow_iff_of_neg` / 引理 `rpow_lt_rpow_iff_of_neg`

English:
lemma rpow_lt_rpow_iff_of_neg
  given: (hx : 0 < x) (hy : 0 < y) (hz : z < 0)
  statement: x ^ z < y ^ z ↔ y < x
  proof: ⟨lt_imp_lt_of_le_imp_le fun h => rpow_le_rpow_of_nonpos hx h hz.le,
    fun h => rpow_lt_rpow_of_neg hy h hz⟩

中文:
引理 rpow_lt_rpow_iff_of_neg
  条件: (hx : 0 < x) (hy : 0 < y) (hz : z < 0)
  结论: x ^ z < y ^ z ↔ y < x
  证明: ⟨lt_imp_lt_of_le_imp_le fun h => rpow_le_rpow_of_nonpos hx h hz.le,
    fun h => rpow_lt_rpow_of_neg hy h hz⟩

Depends on / 依赖: hz.le, lt_imp_lt_of_le_imp_le, rpow_le_rpow_of_nonpos, rpow_lt_rpow_of_neg
-/
lemma rpow_lt_rpow_iff_of_neg (hx : 0 < x) (hy : 0 < y) (hz : z < 0) : x ^ z < y ^ z ↔ y < x :=
  ⟨lt_imp_lt_of_le_imp_le fun h => rpow_le_rpow_of_nonpos hx h hz.le,
    fun h => rpow_lt_rpow_of_neg hy h hz⟩

/--
lemma `rpow_le_rpow_iff_of_neg` / 引理 `rpow_le_rpow_iff_of_neg`

English:
lemma rpow_le_rpow_iff_of_neg
  given: (hx : 0 < x) (hy : 0 < y) (hz : z < 0)
  statement: x ^ z <= y ^ z ↔ y <= x
  proof: le_iff_le_iff_lt_iff_lt.2 rpow_lt_rpow_iff_of_neg hy hx hz

中文:
引理 rpow_le_rpow_iff_of_neg
  条件: (hx : 0 < x) (hy : 0 < y) (hz : z < 0)
  结论: x ^ z <= y ^ z ↔ y <= x
  证明: le_iff_le_iff_lt_iff_lt.2 rpow_lt_rpow_iff_of_neg hy hx hz

Depends on / 依赖: le_iff_le_iff_lt_iff_lt, rpow_lt_rpow_iff_of_neg
-/
lemma rpow_le_rpow_iff_of_neg (hx : 0 < x) (hy : 0 < y) (hz : z < 0) : x ^ z <= y ^ z ↔ y <= x :=
le_iff_le_iff_lt_iff_lt.2 rpow_lt_rpow_iff_of_neg hy hx hz

/--
lemma `le_rpow_inv_iff_of_pos` / 引理 `le_rpow_inv_iff_of_pos`

English:
lemma le_rpow_inv_iff_of_pos
  given: (hx : 0 <= x) (hy : 0 <= y) (hz : 0 < z)
  statement: x <= y ^ z⁻¹ ↔ x ^ z <= y
  proof: by
  rw [← rpow_le_rpow_iff hx _ hz]; rw [rpow_inv_rpow] <;> positivity

中文:
引理 le_rpow_inv_iff_of_pos
  条件: (hx : 0 <= x) (hy : 0 <= y) (hz : 0 < z)
  结论: x <= y ^ z⁻¹ ↔ x ^ z <= y
  证明: by
  rw [← rpow_le_rpow_iff hx _ hz]; rw [rpow_inv_rpow] <;> positivity

Depends on / 依赖: rpow_inv_rpow, rpow_le_rpow_iff
-/
lemma le_rpow_inv_iff_of_pos (hx : 0 <= x) (hy : 0 <= y) (hz : 0 < z) : x <= y ^ z⁻¹ ↔ x ^ z <= y := by
  rw [← rpow_le_rpow_iff hx _ hz]; rw [rpow_inv_rpow] <;> positivity

/--
lemma `rpow_inv_le_iff_of_pos` / 引理 `rpow_inv_le_iff_of_pos`

English:
lemma rpow_inv_le_iff_of_pos
  given: (hx : 0 <= x) (hy : 0 <= y) (hz : 0 < z)
  statement: x ^ z⁻¹ <= y ↔ x <= y ^ z
  proof: by
  rw [← rpow_le_rpow_iff _ hy hz]; rw [rpow_inv_rpow] <;> positivity

中文:
引理 rpow_inv_le_iff_of_pos
  条件: (hx : 0 <= x) (hy : 0 <= y) (hz : 0 < z)
  结论: x ^ z⁻¹ <= y ↔ x <= y ^ z
  证明: by
  rw [← rpow_le_rpow_iff _ hy hz]; rw [rpow_inv_rpow] <;> positivity

Depends on / 依赖: rpow_inv_rpow, rpow_le_rpow_iff
-/
lemma rpow_inv_le_iff_of_pos (hx : 0 <= x) (hy : 0 <= y) (hz : 0 < z) : x ^ z⁻¹ <= y ↔ x <= y ^ z := by
  rw [← rpow_le_rpow_iff _ hy hz]; rw [rpow_inv_rpow] <;> positivity

/--
lemma `lt_rpow_inv_iff_of_pos` / 引理 `lt_rpow_inv_iff_of_pos`

English:
lemma lt_rpow_inv_iff_of_pos
  given: (hx : 0 <= x) (hy : 0 <= y) (hz : 0 < z)
  statement: x < y ^ z⁻¹ ↔ x ^ z < y
  proof: lt_iff_lt_of_le_iff_le rpow_inv_le_iff_of_pos hy hx hz

中文:
引理 lt_rpow_inv_iff_of_pos
  条件: (hx : 0 <= x) (hy : 0 <= y) (hz : 0 < z)
  结论: x < y ^ z⁻¹ ↔ x ^ z < y
  证明: lt_iff_lt_of_le_iff_le rpow_inv_le_iff_of_pos hy hx hz

Depends on / 依赖: lt_iff_lt_of_le_iff_le, rpow_inv_le_iff_of_pos
-/
lemma lt_rpow_inv_iff_of_pos (hx : 0 <= x) (hy : 0 <= y) (hz : 0 < z) : x < y ^ z⁻¹ ↔ x ^ z < y :=
lt_iff_lt_of_le_iff_le rpow_inv_le_iff_of_pos hy hx hz

/--
lemma `rpow_inv_lt_iff_of_pos` / 引理 `rpow_inv_lt_iff_of_pos`

English:
lemma rpow_inv_lt_iff_of_pos
  given: (hx : 0 <= x) (hy : 0 <= y) (hz : 0 < z)
  statement: x ^ z⁻¹ < y ↔ x < y ^ z
  proof: lt_iff_lt_of_le_iff_le le_rpow_inv_iff_of_pos hy hx hz

中文:
引理 rpow_inv_lt_iff_of_pos
  条件: (hx : 0 <= x) (hy : 0 <= y) (hz : 0 < z)
  结论: x ^ z⁻¹ < y ↔ x < y ^ z
  证明: lt_iff_lt_of_le_iff_le le_rpow_inv_iff_of_pos hy hx hz

Depends on / 依赖: le_rpow_inv_iff_of_pos, lt_iff_lt_of_le_iff_le
-/
lemma rpow_inv_lt_iff_of_pos (hx : 0 <= x) (hy : 0 <= y) (hz : 0 < z) : x ^ z⁻¹ < y ↔ x < y ^ z :=
lt_iff_lt_of_le_iff_le le_rpow_inv_iff_of_pos hy hx hz

/--
theorem `le_rpow_inv_iff_of_neg` / 定理 `le_rpow_inv_iff_of_neg`

English:
theorem le_rpow_inv_iff_of_neg
  given: (hx : 0 < x) (hy : 0 < y) (hz : z < 0)
  proof: by
  rw [← rpow_le_rpow_iff_of_neg _ hx hz]; rw [rpow_inv_rpow _ hz.ne] <;> positivity

中文:
定理 le_rpow_inv_iff_of_neg
  条件: (hx : 0 < x) (hy : 0 < y) (hz : z < 0)
  证明: by
  rw [← rpow_le_rpow_iff_of_neg _ hx hz]; rw [rpow_inv_rpow _ hz.ne] <;> positivity

Depends on / 依赖: hz.ne, rpow_inv_rpow, rpow_le_rpow_iff_of_neg
-/
theorem le_rpow_inv_iff_of_neg (hx : 0 < x) (hy : 0 < y) (hz : z < 0) :
    x <= y ^ z⁻¹ ↔ y <= x ^ z := by
  rw [← rpow_le_rpow_iff_of_neg _ hx hz]; rw [rpow_inv_rpow _ hz.ne] <;> positivity

/--
theorem `lt_rpow_inv_iff_of_neg` / 定理 `lt_rpow_inv_iff_of_neg`

English:
theorem lt_rpow_inv_iff_of_neg
  given: (hx : 0 < x) (hy : 0 < y) (hz : z < 0)
  proof: by
  rw [← rpow_lt_rpow_iff_of_neg _ hx hz]; rw [rpow_inv_rpow _ hz.ne] <;> positivity

中文:
定理 lt_rpow_inv_iff_of_neg
  条件: (hx : 0 < x) (hy : 0 < y) (hz : z < 0)
  证明: by
  rw [← rpow_lt_rpow_iff_of_neg _ hx hz]; rw [rpow_inv_rpow _ hz.ne] <;> positivity

Depends on / 依赖: hz.ne, rpow_inv_rpow, rpow_lt_rpow_iff_of_neg
-/
theorem lt_rpow_inv_iff_of_neg (hx : 0 < x) (hy : 0 < y) (hz : z < 0) :
    x < y ^ z⁻¹ ↔ y < x ^ z := by
  rw [← rpow_lt_rpow_iff_of_neg _ hx hz]; rw [rpow_inv_rpow _ hz.ne] <;> positivity

/--
theorem `rpow_inv_lt_iff_of_neg` / 定理 `rpow_inv_lt_iff_of_neg`

English:
theorem rpow_inv_lt_iff_of_neg
  given: (hx : 0 < x) (hy : 0 < y) (hz : z < 0)
  proof: by
  rw [← rpow_lt_rpow_iff_of_neg hy _ hz]; rw [rpow_inv_rpow _ hz.ne] <;> positivity

中文:
定理 rpow_inv_lt_iff_of_neg
  条件: (hx : 0 < x) (hy : 0 < y) (hz : z < 0)
  证明: by
  rw [← rpow_lt_rpow_iff_of_neg hy _ hz]; rw [rpow_inv_rpow _ hz.ne] <;> positivity

Depends on / 依赖: hz.ne, rpow_inv_rpow, rpow_lt_rpow_iff_of_neg
-/
theorem rpow_inv_lt_iff_of_neg (hx : 0 < x) (hy : 0 < y) (hz : z < 0) :
    x ^ z⁻¹ < y ↔ y ^ z < x := by
  rw [← rpow_lt_rpow_iff_of_neg hy _ hz]; rw [rpow_inv_rpow _ hz.ne] <;> positivity

/--
theorem `rpow_inv_le_iff_of_neg` / 定理 `rpow_inv_le_iff_of_neg`

English:
theorem rpow_inv_le_iff_of_neg
  given: (hx : 0 < x) (hy : 0 < y) (hz : z < 0)
  proof: by
  rw [← rpow_le_rpow_iff_of_neg hy _ hz]; rw [rpow_inv_rpow _ hz.ne] <;> positivity

中文:
定理 rpow_inv_le_iff_of_neg
  条件: (hx : 0 < x) (hy : 0 < y) (hz : z < 0)
  证明: by
  rw [← rpow_le_rpow_iff_of_neg hy _ hz]; rw [rpow_inv_rpow _ hz.ne] <;> positivity

Depends on / 依赖: hz.ne, rpow_inv_rpow, rpow_le_rpow_iff_of_neg
-/
theorem rpow_inv_le_iff_of_neg (hx : 0 < x) (hy : 0 < y) (hz : z < 0) :
    x ^ z⁻¹ <= y ↔ y ^ z <= x := by
  rw [← rpow_le_rpow_iff_of_neg hy _ hz]; rw [rpow_inv_rpow _ hz.ne] <;> positivity

/--
theorem `rpow_lt_rpow_of_exponent_lt` / 定理 `rpow_lt_rpow_of_exponent_lt`

English:
theorem rpow_lt_rpow_of_exponent_lt
  given: (hx : 1 < x) (hyz : y < z)
  statement: x ^ y < x ^ z
  proof: by
  repeat' rw [rpow_def_of_pos (lt_trans zero_lt_one hx)]
  rw [exp_lt_exp]; exact mul_lt_mul_of_pos_left hyz (log_pos hx)

@[gcongr]

中文:
定理 rpow_lt_rpow_of_exponent_lt
  条件: (hx : 1 < x) (hyz : y < z)
  结论: x ^ y < x ^ z
  证明: by
  repeat' rw [rpow_def_of_pos (lt_trans zero_lt_one hx)]
  rw [exp_lt_exp]; exact mul_lt_mul_of_pos_left hyz (log_pos hx)

@[gcongr]

Depends on / 依赖: exp_lt_exp, log_pos, lt_trans, mul_lt_mul_of_pos_left, repeat, rpow_def_of_pos, zero_lt_one
-/
theorem rpow_lt_rpow_of_exponent_lt (hx : 1 < x) (hyz : y < z) : x ^ y < x ^ z := by
  repeat' rw [rpow_def_of_pos (lt_trans zero_lt_one hx)]
  rw [exp_lt_exp]; exact mul_lt_mul_of_pos_left hyz (log_pos hx)

@[gcongr]
/--
theorem `rpow_le_rpow_of_exponent_le` / 定理 `rpow_le_rpow_of_exponent_le`

English:
theorem rpow_le_rpow_of_exponent_le
  given: (hx : 1 <= x) (hyz : y <= z)
  statement: x ^ y <= x ^ z
  proof: by
  repeat' rw [rpow_def_of_pos (lt_of_lt_of_le zero_lt_one hx)]
  rw [exp_le_exp]; gcongr; exact log_nonneg hx

中文:
定理 rpow_le_rpow_of_exponent_le
  条件: (hx : 1 <= x) (hyz : y <= z)
  结论: x ^ y <= x ^ z
  证明: by
  repeat' rw [rpow_def_of_pos (lt_of_lt_of_le zero_lt_one hx)]
  rw [exp_le_exp]; gcongr; exact log_nonneg hx

Depends on / 依赖: exp_le_exp, log_nonneg, lt_of_lt_of_le, repeat, rpow_def_of_pos, zero_lt_one
-/
theorem rpow_le_rpow_of_exponent_le (hx : 1 <= x) (hyz : y <= z) : x ^ y <= x ^ z := by
  repeat' rw [rpow_def_of_pos (lt_of_lt_of_le zero_lt_one hx)]
  rw [exp_le_exp]; gcongr; exact log_nonneg hx

/--
theorem `strictAntiOn_rpow_Ioi_of_exponent_neg` / 定理 `strictAntiOn_rpow_Ioi_of_exponent_neg`

English:
theorem strictAntiOn_rpow_Ioi_of_exponent_neg
  given: {r : Real} (hr : r < 0)
  proof: fun _ ha _ _ hab => rpow_lt_rpow_of_neg ha hab hr

中文:
定理 strictAntiOn_rpow_Ioi_of_exponent_neg
  条件: {r : 实数} (hr : r < 0)
  证明: fun _ ha _ _ hab => rpow_lt_rpow_of_neg ha hab hr

Depends on / 依赖: rpow_lt_rpow_of_neg
-/
theorem strictAntiOn_rpow_Ioi_of_exponent_neg {r : Real} (hr : r < 0) :
    StrictAntiOn (fun (x : Real) => x ^ r) (Set.Ioi 0) :=
  fun _ ha _ _ hab => rpow_lt_rpow_of_neg ha hab hr

/--
theorem `antitoneOn_rpow_Ioi_of_exponent_nonpos` / 定理 `antitoneOn_rpow_Ioi_of_exponent_nonpos`

English:
theorem antitoneOn_rpow_Ioi_of_exponent_nonpos
  given: {r : Real} (hr : r <= 0)
  proof: fun _ ha _ _ hab => rpow_le_rpow_of_nonpos ha hab hr

@[simp]

中文:
定理 antitoneOn_rpow_Ioi_of_exponent_nonpos
  条件: {r : 实数} (hr : r <= 0)
  证明: fun _ ha _ _ hab => rpow_le_rpow_of_nonpos ha hab hr

@[simp]

Depends on / 依赖: rpow_le_rpow_of_nonpos
-/
theorem antitoneOn_rpow_Ioi_of_exponent_nonpos {r : Real} (hr : r <= 0) :
    AntitoneOn (fun (x : Real) => x ^ r) (Set.Ioi 0) :=
  fun _ ha _ _ hab => rpow_le_rpow_of_nonpos ha hab hr

@[simp]
/--
theorem `rpow_le_rpow_left_iff` / 定理 `rpow_le_rpow_left_iff`

English:
theorem rpow_le_rpow_left_iff
  given: (hx : 1 < x)
  statement: x ^ y <= x ^ z ↔ y <= z
  proof: by
  have x_pos : 0 < x := lt_trans zero_lt_one hx
  rw [← log_le_log_iff (rpow_pos_of_pos x_pos y) (rpow_pos_of_pos x_pos z)]; rw [log_rpow x_pos]; rw [log_rpow x_pos]; rw [mul_le_mul_iff_left₀ (log_pos hx)]

@[simp]

中文:
定理 rpow_le_rpow_left_iff
  条件: (hx : 1 < x)
  结论: x ^ y <= x ^ z ↔ y <= z
  证明: by
  have x_pos : 0 < x := lt_trans zero_lt_one hx
  rw [← log_le_log_iff (rpow_pos_of_pos x_pos y) (rpow_pos_of_pos x_pos z)]; rw [log_rpow x_pos]; rw [log_rpow x_pos]; rw [mul_le_mul_iff_left₀ (log_pos hx)]

@[simp]

Depends on / 依赖: log_le_log_iff, log_pos, log_rpow, lt_trans, rpow_pos_of_pos, x_pos, zero_lt_one
-/
theorem rpow_le_rpow_left_iff (hx : 1 < x) : x ^ y <= x ^ z ↔ y <= z := by
  have x_pos : 0 < x := lt_trans zero_lt_one hx
  rw [← log_le_log_iff (rpow_pos_of_pos x_pos y) (rpow_pos_of_pos x_pos z)]; rw [log_rpow x_pos]; rw [log_rpow x_pos]; rw [mul_le_mul_iff_left₀ (log_pos hx)]

@[simp]
/--
theorem `rpow_lt_rpow_left_iff` / 定理 `rpow_lt_rpow_left_iff`

English:
theorem rpow_lt_rpow_left_iff
  given: (hx : 1 < x)
  statement: x ^ y < x ^ z ↔ y < z
  proof: by
  rw [lt_iff_not_ge]; rw [rpow_le_rpow_left_iff hx]; rw [lt_iff_not_ge]

中文:
定理 rpow_lt_rpow_left_iff
  条件: (hx : 1 < x)
  结论: x ^ y < x ^ z ↔ y < z
  证明: by
  rw [lt_iff_not_ge]; rw [rpow_le_rpow_left_iff hx]; rw [lt_iff_not_ge]

Depends on / 依赖: lt_iff_not_ge, rpow_le_rpow_left_iff
-/
theorem rpow_lt_rpow_left_iff (hx : 1 < x) : x ^ y < x ^ z ↔ y < z := by
  rw [lt_iff_not_ge]; rw [rpow_le_rpow_left_iff hx]; rw [lt_iff_not_ge]

/--
theorem `rpow_lt_rpow_of_exponent_gt` / 定理 `rpow_lt_rpow_of_exponent_gt`

English:
theorem rpow_lt_rpow_of_exponent_gt
  given: (hx0 : 0 < x) (hx1 : x < 1) (hyz : z < y)
  statement: x ^ y < x ^ z
  proof: by
  repeat' rw [rpow_def_of_pos hx0]
  rw [exp_lt_exp]; exact mul_lt_mul_of_neg_left hyz (log_neg hx0 hx1)

中文:
定理 rpow_lt_rpow_of_exponent_gt
  条件: (hx0 : 0 < x) (hx1 : x < 1) (hyz : z < y)
  结论: x ^ y < x ^ z
  证明: by
  repeat' rw [rpow_def_of_pos hx0]
  rw [exp_lt_exp]; exact mul_lt_mul_of_neg_left hyz (log_neg hx0 hx1)

Depends on / 依赖: exp_lt_exp, log_neg, mul_lt_mul_of_neg_left, repeat, rpow_def_of_pos
-/
theorem rpow_lt_rpow_of_exponent_gt (hx0 : 0 < x) (hx1 : x < 1) (hyz : z < y) : x ^ y < x ^ z := by
  repeat' rw [rpow_def_of_pos hx0]
  rw [exp_lt_exp]; exact mul_lt_mul_of_neg_left hyz (log_neg hx0 hx1)

/--
theorem `rpow_le_rpow_of_exponent_ge` / 定理 `rpow_le_rpow_of_exponent_ge`

English:
theorem rpow_le_rpow_of_exponent_ge
  given: (hx0 : 0 < x) (hx1 : x <= 1) (hyz : z <= y)
  statement: x ^ y <= x ^ z
  proof: by
  repeat' rw [rpow_def_of_pos hx0]
  rw [exp_le_exp]; exact mul_le_mul_of_nonpos_left hyz (log_nonpos (le_of_lt hx0) hx1)

@[simp]

中文:
定理 rpow_le_rpow_of_exponent_ge
  条件: (hx0 : 0 < x) (hx1 : x <= 1) (hyz : z <= y)
  结论: x ^ y <= x ^ z
  证明: by
  repeat' rw [rpow_def_of_pos hx0]
  rw [exp_le_exp]; exact mul_le_mul_of_nonpos_left hyz (log_nonpos (le_of_lt hx0) hx1)

@[simp]

Depends on / 依赖: exp_le_exp, le_of_lt, log_nonpos, mul_le_mul_of_nonpos_left, repeat, rpow_def_of_pos
-/
theorem rpow_le_rpow_of_exponent_ge (hx0 : 0 < x) (hx1 : x <= 1) (hyz : z <= y) : x ^ y <= x ^ z := by
  repeat' rw [rpow_def_of_pos hx0]
  rw [exp_le_exp]; exact mul_le_mul_of_nonpos_left hyz (log_nonpos (le_of_lt hx0) hx1)

@[simp]
/--
theorem `rpow_le_rpow_left_iff_of_base_lt_one` / 定理 `rpow_le_rpow_left_iff_of_base_lt_one`

English:
theorem rpow_le_rpow_left_iff_of_base_lt_one
  given: (hx0 : 0 < x) (hx1 : x < 1)
  proof: by
  rw [← log_le_log_iff (rpow_pos_of_pos hx0 y) (rpow_pos_of_pos hx0 z)]; rw [log_rpow hx0]; rw [log_rpow hx0]; rw [mul_le_mul_right_of_neg (log_neg hx0 hx1)]

@[simp]

中文:
定理 rpow_le_rpow_left_iff_of_base_lt_one
  条件: (hx0 : 0 < x) (hx1 : x < 1)
  证明: by
  rw [← log_le_log_iff (rpow_pos_of_pos hx0 y) (rpow_pos_of_pos hx0 z)]; rw [log_rpow hx0]; rw [log_rpow hx0]; rw [mul_le_mul_right_of_neg (log_neg hx0 hx1)]

@[simp]

Depends on / 依赖: log_le_log_iff, log_neg, log_rpow, mul_le_mul_right_of_neg, rpow_pos_of_pos
-/
theorem rpow_le_rpow_left_iff_of_base_lt_one (hx0 : 0 < x) (hx1 : x < 1) :
    x ^ y <= x ^ z ↔ z <= y := by
  rw [← log_le_log_iff (rpow_pos_of_pos hx0 y) (rpow_pos_of_pos hx0 z)]; rw [log_rpow hx0]; rw [log_rpow hx0]; rw [mul_le_mul_right_of_neg (log_neg hx0 hx1)]

@[simp]
/--
theorem `rpow_lt_rpow_left_iff_of_base_lt_one` / 定理 `rpow_lt_rpow_left_iff_of_base_lt_one`

English:
theorem rpow_lt_rpow_left_iff_of_base_lt_one
  given: (hx0 : 0 < x) (hx1 : x < 1)
  proof: by
  rw [lt_iff_not_ge]; rw [rpow_le_rpow_left_iff_of_base_lt_one hx0 hx1]; rw [lt_iff_not_ge]

中文:
定理 rpow_lt_rpow_left_iff_of_base_lt_one
  条件: (hx0 : 0 < x) (hx1 : x < 1)
  证明: by
  rw [lt_iff_not_ge]; rw [rpow_le_rpow_left_iff_of_base_lt_one hx0 hx1]; rw [lt_iff_not_ge]

Depends on / 依赖: lt_iff_not_ge, rpow_le_rpow_left_iff_of_base_lt_one
-/
theorem rpow_lt_rpow_left_iff_of_base_lt_one (hx0 : 0 < x) (hx1 : x < 1) :
    x ^ y < x ^ z ↔ z < y := by
  rw [lt_iff_not_ge]; rw [rpow_le_rpow_left_iff_of_base_lt_one hx0 hx1]; rw [lt_iff_not_ge]

/--
theorem `rpow_lt_one` / 定理 `rpow_lt_one`

English:
theorem rpow_lt_one
  given: {x z : Real} (hx1 : 0 <= x) (hx2 : x < 1) (hz : 0 < z)
  statement: x ^ z < 1
  proof: by
  rw [← one_rpow z]
  exact rpow_lt_rpow hx1 hx2 hz

中文:
定理 rpow_lt_one
  条件: {x z : 实数} (hx1 : 0 <= x) (hx2 : x < 1) (hz : 0 < z)
  结论: x ^ z < 1
  证明: by
  rw [← one_rpow z]
  exact rpow_lt_rpow hx1 hx2 hz

Depends on / 依赖: Preorder, SmallCategory, one_rpow, rpow_lt_rpow, smallCategory
-/
theorem rpow_lt_one {x z : Real} (hx1 : 0 <= x) (hx2 : x < 1) (hz : 0 < z) : x ^ z < 1 := by
  rw [← one_rpow z]
  exact rpow_lt_rpow hx1 hx2 hz

/--
theorem `rpow_le_one` / 定理 `rpow_le_one`

English:
theorem rpow_le_one
  given: {x z : Real} (hx1 : 0 <= x) (hx2 : x <= 1) (hz : 0 <= z)
  statement: x ^ z <= 1
  proof: by
  rw [← one_rpow z]
  gcongr

中文:
定理 rpow_le_one
  条件: {x z : 实数} (hx1 : 0 <= x) (hx2 : x <= 1) (hz : 0 <= z)
  结论: x ^ z <= 1
  证明: by
  rw [← one_rpow z]
  gcongr

Depends on / 依赖: one_rpow
-/
theorem rpow_le_one {x z : Real} (hx1 : 0 <= x) (hx2 : x <= 1) (hz : 0 <= z) : x ^ z <= 1 := by
  rw [← one_rpow z]
  gcongr

/--
theorem `rpow_lt_one_of_one_lt_of_neg` / 定理 `rpow_lt_one_of_one_lt_of_neg`

English:
theorem rpow_lt_one_of_one_lt_of_neg
  given: {x z : Real} (hx : 1 < x) (hz : z < 0)
  statement: x ^ z < 1
  proof: by
  convert! rpow_lt_rpow_of_exponent_lt hx hz
  exact (rpow_zero x).symm

中文:
定理 rpow_lt_one_of_one_lt_of_neg
  条件: {x z : 实数} (hx : 1 < x) (hz : z < 0)
  结论: x ^ z < 1
  证明: by
  convert! rpow_lt_rpow_of_exponent_lt hx hz
  exact (rpow_zero x).symm

Depends on / 依赖: convert, rpow_lt_rpow_of_exponent_lt, rpow_zero
-/
theorem rpow_lt_one_of_one_lt_of_neg {x z : Real} (hx : 1 < x) (hz : z < 0) : x ^ z < 1 := by
  convert! rpow_lt_rpow_of_exponent_lt hx hz
  exact (rpow_zero x).symm

/--
theorem `rpow_le_one_of_one_le_of_nonpos` / 定理 `rpow_le_one_of_one_le_of_nonpos`

English:
theorem rpow_le_one_of_one_le_of_nonpos
  given: {x z : Real} (hx : 1 <= x) (hz : z <= 0)
  statement: x ^ z <= 1
  proof: by
  convert! rpow_le_rpow_of_exponent_le hx hz
  exact (rpow_zero x).symm

中文:
定理 rpow_le_one_of_one_le_of_nonpos
  条件: {x z : 实数} (hx : 1 <= x) (hz : z <= 0)
  结论: x ^ z <= 1
  证明: by
  convert! rpow_le_rpow_of_exponent_le hx hz
  exact (rpow_zero x).symm

Depends on / 依赖: convert, rpow_le_rpow_of_exponent_le, rpow_zero
-/
theorem rpow_le_one_of_one_le_of_nonpos {x z : Real} (hx : 1 <= x) (hz : z <= 0) : x ^ z <= 1 := by
  convert! rpow_le_rpow_of_exponent_le hx hz
  exact (rpow_zero x).symm

/--
theorem `one_lt_rpow` / 定理 `one_lt_rpow`

English:
theorem one_lt_rpow
  given: {x z : Real} (hx : 1 < x) (hz : 0 < z)
  statement: 1 < x ^ z
  proof: by
  rw [← one_rpow z]
  exact rpow_lt_rpow zero_le_one hx hz

中文:
定理 one_lt_rpow
  条件: {x z : 实数} (hx : 1 < x) (hz : 0 < z)
  结论: 1 < x ^ z
  证明: by
  rw [← one_rpow z]
  exact rpow_lt_rpow zero_le_one hx hz

Depends on / 依赖: one_rpow, rpow_lt_rpow, zero_le_one
-/
theorem one_lt_rpow {x z : Real} (hx : 1 < x) (hz : 0 < z) : 1 < x ^ z := by
  rw [← one_rpow z]
  exact rpow_lt_rpow zero_le_one hx hz

/--
theorem `one_le_rpow` / 定理 `one_le_rpow`

English:
theorem one_le_rpow
  given: {x z : Real} (hx : 1 <= x) (hz : 0 <= z)
  statement: 1 <= x ^ z
  proof: by
  rw [← one_rpow z]
  gcongr

中文:
定理 one_le_rpow
  条件: {x z : 实数} (hx : 1 <= x) (hz : 0 <= z)
  结论: 1 <= x ^ z
  证明: by
  rw [← one_rpow z]
  gcongr

Depends on / 依赖: one_rpow
-/
theorem one_le_rpow {x z : Real} (hx : 1 <= x) (hz : 0 <= z) : 1 <= x ^ z := by
  rw [← one_rpow z]
  gcongr

/--
theorem `one_lt_rpow_of_pos_of_lt_one_of_neg` / 定理 `one_lt_rpow_of_pos_of_lt_one_of_neg`

English:
theorem one_lt_rpow_of_pos_of_lt_one_of_neg
  given: (hx1 : 0 < x) (hx2 : x < 1) (hz : z < 0)
  proof: by
  convert! rpow_lt_rpow_of_exponent_gt hx1 hx2 hz
  exact (rpow_zero x).symm

中文:
定理 one_lt_rpow_of_pos_of_lt_one_of_neg
  条件: (hx1 : 0 < x) (hx2 : x < 1) (hz : z < 0)
  证明: by
  convert! rpow_lt_rpow_of_exponent_gt hx1 hx2 hz
  exact (rpow_zero x).symm

Depends on / 依赖: convert, rpow_lt_rpow_of_exponent_gt, rpow_zero
-/
theorem one_lt_rpow_of_pos_of_lt_one_of_neg (hx1 : 0 < x) (hx2 : x < 1) (hz : z < 0) :
    1 < x ^ z := by
  convert! rpow_lt_rpow_of_exponent_gt hx1 hx2 hz
  exact (rpow_zero x).symm

/--
theorem `one_le_rpow_of_pos_of_le_one_of_nonpos` / 定理 `one_le_rpow_of_pos_of_le_one_of_nonpos`

English:
theorem one_le_rpow_of_pos_of_le_one_of_nonpos
  given: (hx1 : 0 < x) (hx2 : x <= 1) (hz : z <= 0)
  proof: by
  convert! rpow_le_rpow_of_exponent_ge hx1 hx2 hz
  exact (rpow_zero x).symm

中文:
定理 one_le_rpow_of_pos_of_le_one_of_nonpos
  条件: (hx1 : 0 < x) (hx2 : x <= 1) (hz : z <= 0)
  证明: by
  convert! rpow_le_rpow_of_exponent_ge hx1 hx2 hz
  exact (rpow_zero x).symm

Depends on / 依赖: convert, rpow_le_rpow_of_exponent_ge, rpow_zero
-/
theorem one_le_rpow_of_pos_of_le_one_of_nonpos (hx1 : 0 < x) (hx2 : x <= 1) (hz : z <= 0) :
    1 <= x ^ z := by
  convert! rpow_le_rpow_of_exponent_ge hx1 hx2 hz
  exact (rpow_zero x).symm

/--
theorem `rpow_lt_one_iff_of_pos` / 定理 `rpow_lt_one_iff_of_pos`

English:
theorem rpow_lt_one_iff_of_pos
  given: (hx : 0 < x)
  statement: x ^ y < 1 ↔ 1 < x ∧ y < 0 ∨ x < 1 ∧ 0 < y
  proof: by
  rw [rpow_def_of_pos hx]; rw [exp_lt_one_iff]; rw [mul_neg_iff]; rw [log_pos_iff hx.le]; rw [log_neg_iff hx]

中文:
定理 rpow_lt_one_iff_of_pos
  条件: (hx : 0 < x)
  结论: x ^ y < 1 ↔ 1 < x ∧ y < 0 ∨ x < 1 ∧ 0 < y
  证明: by
  rw [rpow_def_of_pos hx]; rw [exp_lt_one_iff]; rw [mul_neg_iff]; rw [log_pos_iff hx.le]; rw [log_neg_iff hx]

Depends on / 依赖: exp_lt_one_iff, hx.le, log_neg_iff, log_pos_iff, mul_neg_iff, rpow_def_of_pos
-/
theorem rpow_lt_one_iff_of_pos (hx : 0 < x) : x ^ y < 1 ↔ 1 < x ∧ y < 0 ∨ x < 1 ∧ 0 < y := by
  rw [rpow_def_of_pos hx]; rw [exp_lt_one_iff]; rw [mul_neg_iff]; rw [log_pos_iff hx.le]; rw [log_neg_iff hx]

/--
theorem `rpow_lt_one_iff` / 定理 `rpow_lt_one_iff`

English:
theorem rpow_lt_one_iff
  given: (hx : 0 <= x)
  proof: by
  rcases hx.eq_or_lt with (rfl | hx)
  · rcases _root_.em (y = 0) with (rfl | hy) <;> simp [*, zero_lt_one]
  · simp [rpow_lt_one_iff_of_pos hx, hx.ne.symm]

中文:
定理 rpow_lt_one_iff
  条件: (hx : 0 <= x)
  证明: by
  rcases hx.eq_or_lt with (rfl | hx)
  · rcases _root_.em (y = 0) with (rfl | hy) <;> simp [*, zero_lt_one]
  · simp [rpow_lt_one_iff_of_pos hx, hx.ne.symm]

Depends on / 依赖: _root_, _root_.em, eq_or_lt, hx.eq_or_lt, hx.ne.symm, rpow_lt_one_iff_of_pos, zero_lt_one
-/
theorem rpow_lt_one_iff (hx : 0 <= x) :
    x ^ y < 1 ↔ x = 0 ∧ y != 0 ∨ 1 < x ∧ y < 0 ∨ x < 1 ∧ 0 < y := by
  rcases hx.eq_or_lt with (rfl | hx)
  · rcases _root_.em (y = 0) with (rfl | hy) <;> simp [*, zero_lt_one]
  · simp [rpow_lt_one_iff_of_pos hx, hx.ne.symm]

/--
theorem `rpow_lt_one_iff'` / 定理 `rpow_lt_one_iff'`

English:
theorem rpow_lt_one_iff'
  given: {x y : Real} (hx : 0 <= x) (hy : 0 < y)
  proof: by
  rw [← Real.rpow_lt_rpow_iff hx zero_le_one hy]; rw [Real.one_rpow]

中文:
定理 rpow_lt_one_iff'
  条件: {x y : 实数} (hx : 0 <= x) (hy : 0 < y)
  证明: by
  rw [← Real.rpow_lt_rpow_iff hx zero_le_one hy]; rw [Real.one_rpow]

Depends on / 依赖: Real.one_rpow, Real.rpow_lt_rpow_iff, one_rpow, rpow_lt_rpow_iff, zero_le_one
-/
theorem rpow_lt_one_iff' {x y : Real} (hx : 0 <= x) (hy : 0 < y) :
    x ^ y < 1 ↔ x < 1 := by
  rw [← Real.rpow_lt_rpow_iff hx zero_le_one hy]; rw [Real.one_rpow]

/--
theorem `one_lt_rpow_iff_of_pos` / 定理 `one_lt_rpow_iff_of_pos`

English:
theorem one_lt_rpow_iff_of_pos
  given: (hx : 0 < x)
  statement: 1 < x ^ y ↔ 1 < x ∧ 0 < y ∨ x < 1 ∧ y < 0
  proof: by
  rw [rpow_def_of_pos hx]; rw [one_lt_exp_iff]; rw [mul_pos_iff]; rw [log_pos_iff hx.le]; rw [log_neg_iff hx]

中文:
定理 one_lt_rpow_iff_of_pos
  条件: (hx : 0 < x)
  结论: 1 < x ^ y ↔ 1 < x ∧ 0 < y ∨ x < 1 ∧ y < 0
  证明: by
  rw [rpow_def_of_pos hx]; rw [one_lt_exp_iff]; rw [mul_pos_iff]; rw [log_pos_iff hx.le]; rw [log_neg_iff hx]

Depends on / 依赖: hx.le, log_neg_iff, log_pos_iff, mul_pos_iff, one_lt_exp_iff, rpow_def_of_pos
-/
theorem one_lt_rpow_iff_of_pos (hx : 0 < x) : 1 < x ^ y ↔ 1 < x ∧ 0 < y ∨ x < 1 ∧ y < 0 := by
  rw [rpow_def_of_pos hx]; rw [one_lt_exp_iff]; rw [mul_pos_iff]; rw [log_pos_iff hx.le]; rw [log_neg_iff hx]

/--
theorem `one_lt_rpow_iff` / 定理 `one_lt_rpow_iff`

English:
theorem one_lt_rpow_iff
  given: (hx : 0 <= x)
  statement: 1 < x ^ y ↔ 1 < x ∧ 0 < y ∨ 0 < x ∧ x < 1 ∧ y < 0
  proof: by
  rcases hx.eq_or_lt with (rfl | hx)
  · rcases _root_.em (y = 0) with (rfl | hy) <;> simp [*, (zero_lt_one' Real).not_gt]
  · simp [one_lt_rpow_iff_of_pos hx, hx]

中文:
定理 one_lt_rpow_iff
  条件: (hx : 0 <= x)
  结论: 1 < x ^ y ↔ 1 < x ∧ 0 < y ∨ 0 < x ∧ x < 1 ∧ y < 0
  证明: by
  rcases hx.eq_or_lt with (rfl | hx)
  · rcases _root_.em (y = 0) with (rfl | hy) <;> simp [*, (zero_lt_one' Real).not_gt]
  · simp [one_lt_rpow_iff_of_pos hx, hx]

Depends on / 依赖: _root_, _root_.em, eq_or_lt, hx.eq_or_lt, not_gt, one_lt_rpow_iff_of_pos, zero_lt_one
-/
theorem one_lt_rpow_iff (hx : 0 <= x) : 1 < x ^ y ↔ 1 < x ∧ 0 < y ∨ 0 < x ∧ x < 1 ∧ y < 0 := by
  rcases hx.eq_or_lt with (rfl | hx)
  · rcases _root_.em (y = 0) with (rfl | hy) <;> simp [*, (zero_lt_one' Real).not_gt]
  · simp [one_lt_rpow_iff_of_pos hx, hx]

/--
theorem `rpow_le_rpow_of_exponent_ge_of_imp` / 定理 `rpow_le_rpow_of_exponent_ge_of_imp`

English:
theorem rpow_le_rpow_of_exponent_ge_of_imp
  statement: (hx0 : 0 <= x) (hx1 : x <= 1) (hyz : z <= y)
  proof: by
  rcases eq_or_lt_of_le hx0 with (rfl | hx0')
  · rcases eq_or_ne y 0 with rfl | hy0
    · rw [h rfl rfl]
    · rw [zero_rpow hy0]
      apply zero_rpow_nonneg
  · exact rpow_le_rpow_of_exponent_ge hx0' hx1 hyz

中文:
定理 rpow_le_rpow_of_exponent_ge_of_imp
  结论: (hx0 : 0 <= x) (hx1 : x <= 1) (hyz : z <= y)
  证明: by
  rcases eq_or_lt_of_le hx0 with (rfl | hx0')
  · rcases eq_or_ne y 0 with rfl | hy0
    · rw [h rfl rfl]
    · rw [zero_rpow hy0]
      apply zero_rpow_nonneg
  · exact rpow_le_rpow_of_exponent_ge hx0' hx1 hyz

Depends on / 依赖: eq_or_lt_of_le, eq_or_ne, rpow_le_rpow_of_exponent_ge, zero_rpow, zero_rpow_nonneg
-/
theorem rpow_le_rpow_of_exponent_ge_of_imp (hx0 : 0 <= x) (hx1 : x <= 1) (hyz : z <= y)
    (h : x = 0 -> y = 0 -> z = 0) :
    x ^ y <= x ^ z := by
  rcases eq_or_lt_of_le hx0 with (rfl | hx0')
  · rcases eq_or_ne y 0 with rfl | hy0
    · rw [h rfl rfl]
    · rw [zero_rpow hy0]
      apply zero_rpow_nonneg
  · exact rpow_le_rpow_of_exponent_ge hx0' hx1 hyz

/--
theorem `rpow_le_rpow_of_exponent_ge'` / 定理 `rpow_le_rpow_of_exponent_ge'`

English:
theorem rpow_le_rpow_of_exponent_ge'
  given: (hx0 : 0 <= x) (hx1 : x <= 1) (hz : 0 <= z) (hyz : z <= y)
  proof: rpow_le_rpow_of_exponent_ge_of_imp hx0 hx1 hyz fun _ hy => le_antisymm (hyz.trans_eq hy) hz

中文:
定理 rpow_le_rpow_of_exponent_ge'
  条件: (hx0 : 0 <= x) (hx1 : x <= 1) (hz : 0 <= z) (hyz : z <= y)
  证明: rpow_le_rpow_of_exponent_ge_of_imp hx0 hx1 hyz fun _ hy => le_antisymm (hyz.trans_eq hy) hz

Depends on / 依赖: hyz.trans_eq, le_antisymm, rpow_le_rpow_of_exponent_ge_of_imp, trans_eq
-/
theorem rpow_le_rpow_of_exponent_ge' (hx0 : 0 <= x) (hx1 : x <= 1) (hz : 0 <= z) (hyz : z <= y) :
    x ^ y <= x ^ z :=
  rpow_le_rpow_of_exponent_ge_of_imp hx0 hx1 hyz fun _ hy => le_antisymm (hyz.trans_eq hy) hz

/--
lemma `rpow_max` / 引理 `rpow_max`

English:
lemma rpow_max
  given: {x y p : Real} (hx : 0 <= x) (hy : 0 <= y) (hp : 0 <= p)
  proof: by
  rcases le_total x y with hxy | hxy
  · rw [max_eq_right hxy, max_eq_right (by gcongr)]
  · rw [max_eq_left hxy, max_eq_left (by gcongr)]

中文:
引理 rpow_max
  条件: {x y p : 实数} (hx : 0 <= x) (hy : 0 <= y) (hp : 0 <= p)
  证明: by
  rcases le_total x y with hxy | hxy
  · rw [max_eq_right hxy, max_eq_right (by gcongr)]
  · rw [max_eq_left hxy, max_eq_left (by gcongr)]

Depends on / 依赖: le_total, max_eq_left, max_eq_right
-/
lemma rpow_max {x y p : Real} (hx : 0 <= x) (hy : 0 <= y) (hp : 0 <= p) :
    (max x y) ^ p = max (x ^ p) (y ^ p) := by
  rcases le_total x y with hxy | hxy
  · rw [max_eq_right hxy, max_eq_right (by gcongr)]
  · rw [max_eq_left hxy, max_eq_left (by gcongr)]

/--
theorem `self_le_rpow_of_le_one` / 定理 `self_le_rpow_of_le_one`

English:
theorem self_le_rpow_of_le_one
  given: (h₁ : 0 <= x) (h₂ : x <= 1) (h₃ : y <= 1)
  statement: x <= x ^ y
  proof: by
  simpa only [rpow_one]
    using rpow_le_rpow_of_exponent_ge_of_imp h₁ h₂ h₃ fun _ => (absurd · one_ne_zero)

中文:
定理 self_le_rpow_of_le_one
  条件: (h₁ : 0 <= x) (h₂ : x <= 1) (h₃ : y <= 1)
  结论: x <= x ^ y
  证明: by
  simpa only [rpow_one]
    using rpow_le_rpow_of_exponent_ge_of_imp h₁ h₂ h₃ fun _ => (absurd · one_ne_zero)

Depends on / 依赖: absurd, one_ne_zero, rpow_le_rpow_of_exponent_ge_of_imp, rpow_one
-/
theorem self_le_rpow_of_le_one (h₁ : 0 <= x) (h₂ : x <= 1) (h₃ : y <= 1) : x <= x ^ y := by
  simpa only [rpow_one]
    using rpow_le_rpow_of_exponent_ge_of_imp h₁ h₂ h₃ fun _ => (absurd · one_ne_zero)

/--
theorem `self_le_rpow_of_one_le` / 定理 `self_le_rpow_of_one_le`

English:
theorem self_le_rpow_of_one_le
  given: (h₁ : 1 <= x) (h₂ : 1 <= y)
  statement: x <= x ^ y
  proof: by
  simpa only [rpow_one] using rpow_le_rpow_of_exponent_le h₁ h₂

中文:
定理 self_le_rpow_of_one_le
  条件: (h₁ : 1 <= x) (h₂ : 1 <= y)
  结论: x <= x ^ y
  证明: by
  simpa only [rpow_one] using rpow_le_rpow_of_exponent_le h₁ h₂

Depends on / 依赖: rpow_le_rpow_of_exponent_le, rpow_one
-/
theorem self_le_rpow_of_one_le (h₁ : 1 <= x) (h₂ : 1 <= y) : x <= x ^ y := by
  simpa only [rpow_one] using rpow_le_rpow_of_exponent_le h₁ h₂

/--
theorem `rpow_le_self_of_le_one` / 定理 `rpow_le_self_of_le_one`

English:
theorem rpow_le_self_of_le_one
  given: (h₁ : 0 <= x) (h₂ : x <= 1) (h₃ : 1 <= y)
  statement: x ^ y <= x
  proof: by
  simpa only [rpow_one]
    using rpow_le_rpow_of_exponent_ge_of_imp h₁ h₂ h₃ fun _ => (absurd · (one_pos.trans_le h₃).ne')

中文:
定理 rpow_le_self_of_le_one
  条件: (h₁ : 0 <= x) (h₂ : x <= 1) (h₃ : 1 <= y)
  结论: x ^ y <= x
  证明: by
  simpa only [rpow_one]
    using rpow_le_rpow_of_exponent_ge_of_imp h₁ h₂ h₃ fun _ => (absurd · (one_pos.trans_le h₃).ne')

Depends on / 依赖: absurd, one_pos, one_pos.trans_le, rpow_le_rpow_of_exponent_ge_of_imp, rpow_one, trans_le
-/
theorem rpow_le_self_of_le_one (h₁ : 0 <= x) (h₂ : x <= 1) (h₃ : 1 <= y) : x ^ y <= x := by
  simpa only [rpow_one]
    using rpow_le_rpow_of_exponent_ge_of_imp h₁ h₂ h₃ fun _ => (absurd · (one_pos.trans_le h₃).ne')

/--
theorem `rpow_le_self_of_one_le` / 定理 `rpow_le_self_of_one_le`

English:
theorem rpow_le_self_of_one_le
  given: (h₁ : 1 <= x) (h₂ : y <= 1)
  statement: x ^ y <= x
  proof: by
  simpa only [rpow_one] using rpow_le_rpow_of_exponent_le h₁ h₂

中文:
定理 rpow_le_self_of_one_le
  条件: (h₁ : 1 <= x) (h₂ : y <= 1)
  结论: x ^ y <= x
  证明: by
  simpa only [rpow_one] using rpow_le_rpow_of_exponent_le h₁ h₂

Depends on / 依赖: rpow_le_rpow_of_exponent_le, rpow_one
-/
theorem rpow_le_self_of_one_le (h₁ : 1 <= x) (h₂ : y <= 1) : x ^ y <= x := by
  simpa only [rpow_one] using rpow_le_rpow_of_exponent_le h₁ h₂

/--
theorem `self_lt_rpow_of_lt_one` / 定理 `self_lt_rpow_of_lt_one`

English:
theorem self_lt_rpow_of_lt_one
  given: (h₁ : 0 < x) (h₂ : x < 1) (h₃ : y < 1)
  statement: x < x ^ y
  proof: by
  simpa only [rpow_one] using rpow_lt_rpow_of_exponent_gt h₁ h₂ h₃

中文:
定理 self_lt_rpow_of_lt_one
  条件: (h₁ : 0 < x) (h₂ : x < 1) (h₃ : y < 1)
  结论: x < x ^ y
  证明: by
  simpa only [rpow_one] using rpow_lt_rpow_of_exponent_gt h₁ h₂ h₃

Depends on / 依赖: rpow_lt_rpow_of_exponent_gt, rpow_one
-/
theorem self_lt_rpow_of_lt_one (h₁ : 0 < x) (h₂ : x < 1) (h₃ : y < 1) : x < x ^ y := by
  simpa only [rpow_one] using rpow_lt_rpow_of_exponent_gt h₁ h₂ h₃

/--
theorem `self_lt_rpow_of_one_lt` / 定理 `self_lt_rpow_of_one_lt`

English:
theorem self_lt_rpow_of_one_lt
  given: (h₁ : 1 < x) (h₂ : 1 < y)
  statement: x < x ^ y
  proof: by
  simpa only [rpow_one] using rpow_lt_rpow_of_exponent_lt h₁ h₂

中文:
定理 self_lt_rpow_of_one_lt
  条件: (h₁ : 1 < x) (h₂ : 1 < y)
  结论: x < x ^ y
  证明: by
  simpa only [rpow_one] using rpow_lt_rpow_of_exponent_lt h₁ h₂

Depends on / 依赖: rpow_lt_rpow_of_exponent_lt, rpow_one
-/
theorem self_lt_rpow_of_one_lt (h₁ : 1 < x) (h₂ : 1 < y) : x < x ^ y := by
  simpa only [rpow_one] using rpow_lt_rpow_of_exponent_lt h₁ h₂

/--
theorem `rpow_lt_self_of_lt_one` / 定理 `rpow_lt_self_of_lt_one`

English:
theorem rpow_lt_self_of_lt_one
  given: (h₁ : 0 < x) (h₂ : x < 1) (h₃ : 1 < y)
  statement: x ^ y < x
  proof: by
  simpa only [rpow_one] using rpow_lt_rpow_of_exponent_gt h₁ h₂ h₃

中文:
定理 rpow_lt_self_of_lt_one
  条件: (h₁ : 0 < x) (h₂ : x < 1) (h₃ : 1 < y)
  结论: x ^ y < x
  证明: by
  simpa only [rpow_one] using rpow_lt_rpow_of_exponent_gt h₁ h₂ h₃

Depends on / 依赖: f.map_rel_iff, h.le, homOfLE, map_rel_iff, rpow_lt_rpow_of_exponent_gt, rpow_one
-/
theorem rpow_lt_self_of_lt_one (h₁ : 0 < x) (h₂ : x < 1) (h₃ : 1 < y) : x ^ y < x := by
  simpa only [rpow_one] using rpow_lt_rpow_of_exponent_gt h₁ h₂ h₃

/--
theorem `rpow_lt_self_of_one_lt` / 定理 `rpow_lt_self_of_one_lt`

English:
theorem rpow_lt_self_of_one_lt
  given: (h₁ : 1 < x) (h₂ : y < 1)
  statement: x ^ y < x
  proof: by
  simpa only [rpow_one] using rpow_lt_rpow_of_exponent_lt h₁ h₂

中文:
定理 rpow_lt_self_of_one_lt
  条件: (h₁ : 1 < x) (h₂ : y < 1)
  结论: x ^ y < x
  证明: by
  simpa only [rpow_one] using rpow_lt_rpow_of_exponent_lt h₁ h₂

Depends on / 依赖: rpow_lt_rpow_of_exponent_lt, rpow_one
-/
theorem rpow_lt_self_of_one_lt (h₁ : 1 < x) (h₂ : y < 1) : x ^ y < x := by
  simpa only [rpow_one] using rpow_lt_rpow_of_exponent_lt h₁ h₂

/--
theorem `rpow_left_injOn` / 定理 `rpow_left_injOn`

English:
theorem rpow_left_injOn
  given: {x : Real} (hx : x != 0)
  statement: InjOn (fun y : Real => y ^ x) { y : Real | 0 <= y }
  proof: by
  rintro y hy z hz (hyz : y ^ x = z ^ x)
  rw [← rpow_one y]; rw [← rpow_one z]; rw [← mul_inv_cancel₀ hx]; rw [rpow_mul hy]; rw [rpow_mul hz]; rw [hyz]

中文:
定理 rpow_left_injOn
  条件: {x : 实数} (hx : x != 0)
  结论: 单射限制 (fun y : 实数 => y ^ x) { y : 实数 | 0 <= y }
  证明: by
  rintro y hy z hz (hyz : y ^ x = z ^ x)
  rw [← rpow_one y]; rw [← rpow_one z]; rw [← mul_inv_cancel₀ hx]; rw [rpow_mul hy]; rw [rpow_mul hz]; rw [hyz]

Depends on / 依赖: rpow_mul, rpow_one
-/
theorem rpow_left_injOn {x : Real} (hx : x != 0) : InjOn (fun y : Real => y ^ x) { y : Real | 0 <= y } := by
  rintro y hy z hz (hyz : y ^ x = z ^ x)
  rw [← rpow_one y]; rw [← rpow_one z]; rw [← mul_inv_cancel₀ hx]; rw [rpow_mul hy]; rw [rpow_mul hz]; rw [hyz]

/--
lemma `rpow_left_inj` / 引理 `rpow_left_inj`

English:
lemma rpow_left_inj
  given: (hx : 0 <= x) (hy : 0 <= y) (hz : z != 0)
  statement: x ^ z = y ^ z ↔ x = y
  proof: (rpow_left_injOn hz).eq_iff hx hy

中文:
引理 rpow_left_inj
  条件: (hx : 0 <= x) (hy : 0 <= y) (hz : z != 0)
  结论: x ^ z = y ^ z ↔ x = y
  证明: (rpow_left_injOn hz).eq_iff hx hy

Depends on / 依赖: eq_iff, rpow_left_injOn
-/
lemma rpow_left_inj (hx : 0 <= x) (hy : 0 <= y) (hz : z != 0) : x ^ z = y ^ z ↔ x = y :=
  (rpow_left_injOn hz).eq_iff hx hy

/--
lemma `rpow_inv_eq` / 引理 `rpow_inv_eq`

English:
lemma rpow_inv_eq
  given: (hx : 0 <= x) (hy : 0 <= y) (hz : z != 0)
  statement: x ^ z⁻¹ = y ↔ x = y ^ z
  proof: by
  rw [← rpow_left_inj _ hy hz]; rw [rpow_inv_rpow hx hz]; positivity

中文:
引理 rpow_inv_eq
  条件: (hx : 0 <= x) (hy : 0 <= y) (hz : z != 0)
  结论: x ^ z⁻¹ = y ↔ x = y ^ z
  证明: by
  rw [← rpow_left_inj _ hy hz]; rw [rpow_inv_rpow hx hz]; positivity

Depends on / 依赖: rpow_inv_rpow, rpow_left_inj
-/
lemma rpow_inv_eq (hx : 0 <= x) (hy : 0 <= y) (hz : z != 0) : x ^ z⁻¹ = y ↔ x = y ^ z := by
  rw [← rpow_left_inj _ hy hz]; rw [rpow_inv_rpow hx hz]; positivity

/--
lemma `eq_rpow_inv` / 引理 `eq_rpow_inv`

English:
lemma eq_rpow_inv
  given: (hx : 0 <= x) (hy : 0 <= y) (hz : z != 0)
  statement: x = y ^ z⁻¹ ↔ x ^ z = y
  proof: by
  rw [← rpow_left_inj hx _ hz]; rw [rpow_inv_rpow hy hz]; positivity

中文:
引理 eq_rpow_inv
  条件: (hx : 0 <= x) (hy : 0 <= y) (hz : z != 0)
  结论: x = y ^ z⁻¹ ↔ x ^ z = y
  证明: by
  rw [← rpow_left_inj hx _ hz]; rw [rpow_inv_rpow hy hz]; positivity

Depends on / 依赖: rpow_inv_rpow, rpow_left_inj
-/
lemma eq_rpow_inv (hx : 0 <= x) (hy : 0 <= y) (hz : z != 0) : x = y ^ z⁻¹ ↔ x ^ z = y := by
  rw [← rpow_left_inj hx _ hz]; rw [rpow_inv_rpow hy hz]; positivity

/--
theorem `le_rpow_iff_log_le` / 定理 `le_rpow_iff_log_le`

English:
theorem le_rpow_iff_log_le
  given: (hx : 0 < x) (hy : 0 < y)
  statement: x <= y ^ z ↔ log x <= z * log y
  proof: by
  rw [← log_le_log_iff hx (rpow_pos_of_pos hy z)]; rw [log_rpow hy]

中文:
定理 le_rpow_iff_log_le
  条件: (hx : 0 < x) (hy : 0 < y)
  结论: x <= y ^ z ↔ log x <= z * log y
  证明: by
  rw [← log_le_log_iff hx (rpow_pos_of_pos hy z)]; rw [log_rpow hy]

Depends on / 依赖: log_le_log_iff, log_rpow, rpow_pos_of_pos
-/
theorem le_rpow_iff_log_le (hx : 0 < x) (hy : 0 < y) : x <= y ^ z ↔ log x <= z * log y := by
  rw [← log_le_log_iff hx (rpow_pos_of_pos hy z)]; rw [log_rpow hy]

/--
lemma `le_pow_iff_log_le` / 引理 `le_pow_iff_log_le`

English:
lemma le_pow_iff_log_le
  given: (hx : 0 < x) (hy : 0 < y)
  statement: x <= y ^ n ↔ log x <= n * log y
  proof: rpow_natCast _ _ ▸ le_rpow_iff_log_le hx hy

中文:
引理 le_pow_iff_log_le
  条件: (hx : 0 < x) (hy : 0 < y)
  结论: x <= y ^ n ↔ log x <= n * log y
  证明: rpow_natCast _ _ ▸ le_rpow_iff_log_le hx hy

Depends on / 依赖: le_rpow_iff_log_le, rpow_natCast
-/
lemma le_pow_iff_log_le (hx : 0 < x) (hy : 0 < y) : x <= y ^ n ↔ log x <= n * log y :=
  rpow_natCast _ _ ▸ le_rpow_iff_log_le hx hy

/--
lemma `le_zpow_iff_log_le` / 引理 `le_zpow_iff_log_le`

English:
lemma le_zpow_iff_log_le
  given: {n : Int} (hx : 0 < x) (hy : 0 < y)
  statement: x <= y ^ n ↔ log x <= n * log y
  proof: rpow_intCast _ _ ▸ le_rpow_iff_log_le hx hy

中文:
引理 le_zpow_iff_log_le
  条件: {n : 整数} (hx : 0 < x) (hy : 0 < y)
  结论: x <= y ^ n ↔ log x <= n * log y
  证明: rpow_intCast _ _ ▸ le_rpow_iff_log_le hx hy

Depends on / 依赖: le_rpow_iff_log_le, rpow_intCast
-/
lemma le_zpow_iff_log_le {n : Int} (hx : 0 < x) (hy : 0 < y) : x <= y ^ n ↔ log x <= n * log y :=
  rpow_intCast _ _ ▸ le_rpow_iff_log_le hx hy

/--
lemma `le_rpow_of_log_le` / 引理 `le_rpow_of_log_le`

English:
lemma le_rpow_of_log_le
  given: (hy : 0 < y) (h : log x <= z * log y)
  statement: x <= y ^ z
  proof: by
  obtain hx | hx := le_or_gt x 0
  · exact hx.trans (rpow_pos_of_pos hy _).le
  · exact (le_rpow_iff_log_le hx hy).2 h

中文:
引理 le_rpow_of_log_le
  条件: (hy : 0 < y) (h : log x <= z * log y)
  结论: x <= y ^ z
  证明: by
  obtain hx | hx := le_or_gt x 0
  · exact hx.trans (rpow_pos_of_pos hy _).le
  · exact (le_rpow_iff_log_le hx hy).2 h

Depends on / 依赖: hx.trans, le_or_gt, le_rpow_iff_log_le, rpow_pos_of_pos
-/
lemma le_rpow_of_log_le (hy : 0 < y) (h : log x <= z * log y) : x <= y ^ z := by
  obtain hx | hx := le_or_gt x 0
  · exact hx.trans (rpow_pos_of_pos hy _).le
  · exact (le_rpow_iff_log_le hx hy).2 h

/--
lemma `le_pow_of_log_le` / 引理 `le_pow_of_log_le`

English:
lemma le_pow_of_log_le
  given: (hy : 0 < y) (h : log x <= n * log y)
  statement: x <= y ^ n
  proof: rpow_natCast _ _ ▸ le_rpow_of_log_le hy h

中文:
引理 le_pow_of_log_le
  条件: (hy : 0 < y) (h : log x <= n * log y)
  结论: x <= y ^ n
  证明: rpow_natCast _ _ ▸ le_rpow_of_log_le hy h

Depends on / 依赖: le_rpow_of_log_le, rpow_natCast
-/
lemma le_pow_of_log_le (hy : 0 < y) (h : log x <= n * log y) : x <= y ^ n :=
  rpow_natCast _ _ ▸ le_rpow_of_log_le hy h

/--
lemma `le_zpow_of_log_le` / 引理 `le_zpow_of_log_le`

English:
lemma le_zpow_of_log_le
  given: {n : Int} (hy : 0 < y) (h : log x <= n * log y)
  statement: x <= y ^ n
  proof: rpow_intCast _ _ ▸ le_rpow_of_log_le hy h

中文:
引理 le_zpow_of_log_le
  条件: {n : 整数} (hy : 0 < y) (h : log x <= n * log y)
  结论: x <= y ^ n
  证明: rpow_intCast _ _ ▸ le_rpow_of_log_le hy h

Depends on / 依赖: le_rpow_of_log_le, rpow_intCast
-/
lemma le_zpow_of_log_le {n : Int} (hy : 0 < y) (h : log x <= n * log y) : x <= y ^ n :=
  rpow_intCast _ _ ▸ le_rpow_of_log_le hy h

/--
theorem `lt_rpow_iff_log_lt` / 定理 `lt_rpow_iff_log_lt`

English:
theorem lt_rpow_iff_log_lt
  given: (hx : 0 < x) (hy : 0 < y)
  statement: x < y ^ z ↔ log x < z * log y
  proof: by
  rw [← log_lt_log_iff hx (rpow_pos_of_pos hy z)]; rw [log_rpow hy]

中文:
定理 lt_rpow_iff_log_lt
  条件: (hx : 0 < x) (hy : 0 < y)
  结论: x < y ^ z ↔ log x < z * log y
  证明: by
  rw [← log_lt_log_iff hx (rpow_pos_of_pos hy z)]; rw [log_rpow hy]

Depends on / 依赖: log_lt_log_iff, log_rpow, rpow_pos_of_pos
-/
theorem lt_rpow_iff_log_lt (hx : 0 < x) (hy : 0 < y) : x < y ^ z ↔ log x < z * log y := by
  rw [← log_lt_log_iff hx (rpow_pos_of_pos hy z)]; rw [log_rpow hy]

/--
lemma `lt_pow_iff_log_lt` / 引理 `lt_pow_iff_log_lt`

English:
lemma lt_pow_iff_log_lt
  given: (hx : 0 < x) (hy : 0 < y)
  statement: x < y ^ n ↔ log x < n * log y
  proof: rpow_natCast _ _ ▸ lt_rpow_iff_log_lt hx hy

中文:
引理 lt_pow_iff_log_lt
  条件: (hx : 0 < x) (hy : 0 < y)
  结论: x < y ^ n ↔ log x < n * log y
  证明: rpow_natCast _ _ ▸ lt_rpow_iff_log_lt hx hy

Depends on / 依赖: lt_rpow_iff_log_lt, rpow_natCast
-/
lemma lt_pow_iff_log_lt (hx : 0 < x) (hy : 0 < y) : x < y ^ n ↔ log x < n * log y :=
  rpow_natCast _ _ ▸ lt_rpow_iff_log_lt hx hy

/--
lemma `lt_zpow_iff_log_lt` / 引理 `lt_zpow_iff_log_lt`

English:
lemma lt_zpow_iff_log_lt
  given: {n : Int} (hx : 0 < x) (hy : 0 < y)
  statement: x < y ^ n ↔ log x < n * log y
  proof: rpow_intCast _ _ ▸ lt_rpow_iff_log_lt hx hy

中文:
引理 lt_zpow_iff_log_lt
  条件: {n : 整数} (hx : 0 < x) (hy : 0 < y)
  结论: x < y ^ n ↔ log x < n * log y
  证明: rpow_intCast _ _ ▸ lt_rpow_iff_log_lt hx hy

Depends on / 依赖: lt_rpow_iff_log_lt, rpow_intCast
-/
lemma lt_zpow_iff_log_lt {n : Int} (hx : 0 < x) (hy : 0 < y) : x < y ^ n ↔ log x < n * log y :=
  rpow_intCast _ _ ▸ lt_rpow_iff_log_lt hx hy

/--
lemma `lt_rpow_of_log_lt` / 引理 `lt_rpow_of_log_lt`

English:
lemma lt_rpow_of_log_lt
  given: (hy : 0 < y) (h : log x < z * log y)
  statement: x < y ^ z
  proof: by
  obtain hx | hx := le_or_gt x 0
  · exact hx.trans_lt (rpow_pos_of_pos hy _)
  · exact (lt_rpow_iff_log_lt hx hy).2 h

中文:
引理 lt_rpow_of_log_lt
  条件: (hy : 0 < y) (h : log x < z * log y)
  结论: x < y ^ z
  证明: by
  obtain hx | hx := le_or_gt x 0
  · exact hx.trans_lt (rpow_pos_of_pos hy _)
  · exact (lt_rpow_iff_log_lt hx hy).2 h

Depends on / 依赖: hx.trans_lt, le_or_gt, lt_rpow_iff_log_lt, rpow_pos_of_pos, trans_lt
-/
lemma lt_rpow_of_log_lt (hy : 0 < y) (h : log x < z * log y) : x < y ^ z := by
  obtain hx | hx := le_or_gt x 0
  · exact hx.trans_lt (rpow_pos_of_pos hy _)
  · exact (lt_rpow_iff_log_lt hx hy).2 h

/--
lemma `lt_pow_of_log_lt` / 引理 `lt_pow_of_log_lt`

English:
lemma lt_pow_of_log_lt
  given: (hy : 0 < y) (h : log x < n * log y)
  statement: x < y ^ n
  proof: rpow_natCast _ _ ▸ lt_rpow_of_log_lt hy h

中文:
引理 lt_pow_of_log_lt
  条件: (hy : 0 < y) (h : log x < n * log y)
  结论: x < y ^ n
  证明: rpow_natCast _ _ ▸ lt_rpow_of_log_lt hy h

Depends on / 依赖: lt_rpow_of_log_lt, rpow_natCast
-/
lemma lt_pow_of_log_lt (hy : 0 < y) (h : log x < n * log y) : x < y ^ n :=
  rpow_natCast _ _ ▸ lt_rpow_of_log_lt hy h

/--
lemma `lt_zpow_of_log_lt` / 引理 `lt_zpow_of_log_lt`

English:
lemma lt_zpow_of_log_lt
  given: {n : Int} (hy : 0 < y) (h : log x < n * log y)
  statement: x < y ^ n
  proof: rpow_intCast _ _ ▸ lt_rpow_of_log_lt hy h

中文:
引理 lt_zpow_of_log_lt
  条件: {n : 整数} (hy : 0 < y) (h : log x < n * log y)
  结论: x < y ^ n
  证明: rpow_intCast _ _ ▸ lt_rpow_of_log_lt hy h

Depends on / 依赖: lt_rpow_of_log_lt, rpow_intCast
-/
lemma lt_zpow_of_log_lt {n : Int} (hy : 0 < y) (h : log x < n * log y) : x < y ^ n :=
  rpow_intCast _ _ ▸ lt_rpow_of_log_lt hy h

/--
lemma `rpow_le_iff_le_log` / 引理 `rpow_le_iff_le_log`

English:
lemma rpow_le_iff_le_log
  given: (hx : 0 < x) (hy : 0 < y)
  statement: x ^ z <= y ↔ z * log x <= log y
  proof: by
  rw [← log_le_log_iff (rpow_pos_of_pos hx _) hy]; rw [log_rpow hx]

中文:
引理 rpow_le_iff_le_log
  条件: (hx : 0 < x) (hy : 0 < y)
  结论: x ^ z <= y ↔ z * log x <= log y
  证明: by
  rw [← log_le_log_iff (rpow_pos_of_pos hx _) hy]; rw [log_rpow hx]

Depends on / 依赖: log_le_log_iff, log_rpow, rpow_pos_of_pos
-/
lemma rpow_le_iff_le_log (hx : 0 < x) (hy : 0 < y) : x ^ z <= y ↔ z * log x <= log y := by
  rw [← log_le_log_iff (rpow_pos_of_pos hx _) hy]; rw [log_rpow hx]

/--
lemma `pow_le_iff_le_log` / 引理 `pow_le_iff_le_log`

English:
lemma pow_le_iff_le_log
  given: (hx : 0 < x) (hy : 0 < y)
  statement: x ^ n <= y ↔ n * log x <= log y
  proof: by
  rw [← rpow_le_iff_le_log hx hy]; rw [rpow_natCast]

中文:
引理 pow_le_iff_le_log
  条件: (hx : 0 < x) (hy : 0 < y)
  结论: x ^ n <= y ↔ n * log x <= log y
  证明: by
  rw [← rpow_le_iff_le_log hx hy]; rw [rpow_natCast]

Depends on / 依赖: rpow_le_iff_le_log, rpow_natCast
-/
lemma pow_le_iff_le_log (hx : 0 < x) (hy : 0 < y) : x ^ n <= y ↔ n * log x <= log y := by
  rw [← rpow_le_iff_le_log hx hy]; rw [rpow_natCast]

/--
lemma `zpow_le_iff_le_log` / 引理 `zpow_le_iff_le_log`

English:
lemma zpow_le_iff_le_log
  given: {n : Int} (hx : 0 < x) (hy : 0 < y)
  statement: x ^ n <= y ↔ n * log x <= log y
  proof: by
  rw [← rpow_le_iff_le_log hx hy]; rw [rpow_intCast]

中文:
引理 zpow_le_iff_le_log
  条件: {n : 整数} (hx : 0 < x) (hy : 0 < y)
  结论: x ^ n <= y ↔ n * log x <= log y
  证明: by
  rw [← rpow_le_iff_le_log hx hy]; rw [rpow_intCast]

Depends on / 依赖: rpow_intCast, rpow_le_iff_le_log
-/
lemma zpow_le_iff_le_log {n : Int} (hx : 0 < x) (hy : 0 < y) : x ^ n <= y ↔ n * log x <= log y := by
  rw [← rpow_le_iff_le_log hx hy]; rw [rpow_intCast]

/--
lemma `le_log_of_rpow_le` / 引理 `le_log_of_rpow_le`

English:
lemma le_log_of_rpow_le
  given: (hx : 0 < x) (h : x ^ z <= y)
  statement: z * log x <= log y
  proof: log_rpow hx _ ▸ log_le_log (by positivity) h

中文:
引理 le_log_of_rpow_le
  条件: (hx : 0 < x) (h : x ^ z <= y)
  结论: z * log x <= log y
  证明: log_rpow hx _ ▸ log_le_log (by positivity) h

Depends on / 依赖: log_le_log, log_rpow
-/
lemma le_log_of_rpow_le (hx : 0 < x) (h : x ^ z <= y) : z * log x <= log y :=
  log_rpow hx _ ▸ log_le_log (by positivity) h

/--
lemma `le_log_of_pow_le` / 引理 `le_log_of_pow_le`

English:
lemma le_log_of_pow_le
  given: (hx : 0 < x) (h : x ^ n <= y)
  statement: n * log x <= log y
  proof: le_log_of_rpow_le hx (rpow_natCast _ _ ▸ h)

中文:
引理 le_log_of_pow_le
  条件: (hx : 0 < x) (h : x ^ n <= y)
  结论: n * log x <= log y
  证明: le_log_of_rpow_le hx (rpow_natCast _ _ ▸ h)

Depends on / 依赖: le_log_of_rpow_le, rpow_natCast
-/
lemma le_log_of_pow_le (hx : 0 < x) (h : x ^ n <= y) : n * log x <= log y :=
  le_log_of_rpow_le hx (rpow_natCast _ _ ▸ h)

/--
lemma `le_log_of_zpow_le` / 引理 `le_log_of_zpow_le`

English:
lemma le_log_of_zpow_le
  given: {n : Int} (hx : 0 < x) (h : x ^ n <= y)
  statement: n * log x <= log y
  proof: le_log_of_rpow_le hx (rpow_intCast _ _ ▸ h)

中文:
引理 le_log_of_zpow_le
  条件: {n : 整数} (hx : 0 < x) (h : x ^ n <= y)
  结论: n * log x <= log y
  证明: le_log_of_rpow_le hx (rpow_intCast _ _ ▸ h)

Depends on / 依赖: le_log_of_rpow_le, rpow_intCast
-/
lemma le_log_of_zpow_le {n : Int} (hx : 0 < x) (h : x ^ n <= y) : n * log x <= log y :=
  le_log_of_rpow_le hx (rpow_intCast _ _ ▸ h)

/--
lemma `rpow_le_of_le_log` / 引理 `rpow_le_of_le_log`

English:
lemma rpow_le_of_le_log
  given: (hy : 0 < y) (h : log x <= z * log y)
  statement: x <= y ^ z
  proof: by
  obtain hx | hx := le_or_gt x 0
  · exact hx.trans (rpow_pos_of_pos hy _).le
  · exact (le_rpow_iff_log_le hx hy).2 h

中文:
引理 rpow_le_of_le_log
  条件: (hy : 0 < y) (h : log x <= z * log y)
  结论: x <= y ^ z
  证明: by
  obtain hx | hx := le_or_gt x 0
  · exact hx.trans (rpow_pos_of_pos hy _).le
  · exact (le_rpow_iff_log_le hx hy).2 h

Depends on / 依赖: hx.trans, le_or_gt, le_rpow_iff_log_le, rpow_pos_of_pos
-/
lemma rpow_le_of_le_log (hy : 0 < y) (h : log x <= z * log y) : x <= y ^ z := by
  obtain hx | hx := le_or_gt x 0
  · exact hx.trans (rpow_pos_of_pos hy _).le
  · exact (le_rpow_iff_log_le hx hy).2 h

/--
lemma `pow_le_of_le_log` / 引理 `pow_le_of_le_log`

English:
lemma pow_le_of_le_log
  given: (hy : 0 < y) (h : log x <= n * log y)
  statement: x <= y ^ n
  proof: rpow_natCast _ _ ▸ rpow_le_of_le_log hy h

中文:
引理 pow_le_of_le_log
  条件: (hy : 0 < y) (h : log x <= n * log y)
  结论: x <= y ^ n
  证明: rpow_natCast _ _ ▸ rpow_le_of_le_log hy h

Depends on / 依赖: rpow_le_of_le_log, rpow_natCast
-/
lemma pow_le_of_le_log (hy : 0 < y) (h : log x <= n * log y) : x <= y ^ n :=
  rpow_natCast _ _ ▸ rpow_le_of_le_log hy h

/--
lemma `zpow_le_of_le_log` / 引理 `zpow_le_of_le_log`

English:
lemma zpow_le_of_le_log
  given: {n : Int} (hy : 0 < y) (h : log x <= n * log y)
  statement: x <= y ^ n
  proof: rpow_intCast _ _ ▸ rpow_le_of_le_log hy h

中文:
引理 zpow_le_of_le_log
  条件: {n : 整数} (hy : 0 < y) (h : log x <= n * log y)
  结论: x <= y ^ n
  证明: rpow_intCast _ _ ▸ rpow_le_of_le_log hy h

Depends on / 依赖: rpow_intCast, rpow_le_of_le_log
-/
lemma zpow_le_of_le_log {n : Int} (hy : 0 < y) (h : log x <= n * log y) : x <= y ^ n :=
  rpow_intCast _ _ ▸ rpow_le_of_le_log hy h

/--
lemma `rpow_lt_iff_lt_log` / 引理 `rpow_lt_iff_lt_log`

English:
lemma rpow_lt_iff_lt_log
  given: (hx : 0 < x) (hy : 0 < y)
  statement: x ^ z < y ↔ z * log x < log y
  proof: by
  rw [← log_lt_log_iff (rpow_pos_of_pos hx _) hy]; rw [log_rpow hx]

中文:
引理 rpow_lt_iff_lt_log
  条件: (hx : 0 < x) (hy : 0 < y)
  结论: x ^ z < y ↔ z * log x < log y
  证明: by
  rw [← log_lt_log_iff (rpow_pos_of_pos hx _) hy]; rw [log_rpow hx]

Depends on / 依赖: log_lt_log_iff, log_rpow, rpow_pos_of_pos
-/
lemma rpow_lt_iff_lt_log (hx : 0 < x) (hy : 0 < y) : x ^ z < y ↔ z * log x < log y := by
  rw [← log_lt_log_iff (rpow_pos_of_pos hx _) hy]; rw [log_rpow hx]

/--
lemma `pow_lt_iff_lt_log` / 引理 `pow_lt_iff_lt_log`

English:
lemma pow_lt_iff_lt_log
  given: (hx : 0 < x) (hy : 0 < y)
  statement: x ^ n < y ↔ n * log x < log y
  proof: by
  rw [← rpow_lt_iff_lt_log hx hy]; rw [rpow_natCast]

中文:
引理 pow_lt_iff_lt_log
  条件: (hx : 0 < x) (hy : 0 < y)
  结论: x ^ n < y ↔ n * log x < log y
  证明: by
  rw [← rpow_lt_iff_lt_log hx hy]; rw [rpow_natCast]

Depends on / 依赖: rpow_lt_iff_lt_log, rpow_natCast
-/
lemma pow_lt_iff_lt_log (hx : 0 < x) (hy : 0 < y) : x ^ n < y ↔ n * log x < log y := by
  rw [← rpow_lt_iff_lt_log hx hy]; rw [rpow_natCast]

/--
lemma `zpow_lt_iff_lt_log` / 引理 `zpow_lt_iff_lt_log`

English:
lemma zpow_lt_iff_lt_log
  given: {n : Int} (hx : 0 < x) (hy : 0 < y)
  statement: x ^ n < y ↔ n * log x < log y
  proof: by
  rw [← rpow_lt_iff_lt_log hx hy]; rw [rpow_intCast]

中文:
引理 zpow_lt_iff_lt_log
  条件: {n : 整数} (hx : 0 < x) (hy : 0 < y)
  结论: x ^ n < y ↔ n * log x < log y
  证明: by
  rw [← rpow_lt_iff_lt_log hx hy]; rw [rpow_intCast]

Depends on / 依赖: rpow_intCast, rpow_lt_iff_lt_log
-/
lemma zpow_lt_iff_lt_log {n : Int} (hx : 0 < x) (hy : 0 < y) : x ^ n < y ↔ n * log x < log y := by
  rw [← rpow_lt_iff_lt_log hx hy]; rw [rpow_intCast]

/--
lemma `lt_log_of_rpow_lt` / 引理 `lt_log_of_rpow_lt`

English:
lemma lt_log_of_rpow_lt
  given: (hx : 0 < x) (h : x ^ z < y)
  statement: z * log x < log y
  proof: log_rpow hx _ ▸ log_lt_log (by positivity) h

中文:
引理 lt_log_of_rpow_lt
  条件: (hx : 0 < x) (h : x ^ z < y)
  结论: z * log x < log y
  证明: log_rpow hx _ ▸ log_lt_log (by positivity) h

Depends on / 依赖: log_lt_log, log_rpow
-/
lemma lt_log_of_rpow_lt (hx : 0 < x) (h : x ^ z < y) : z * log x < log y :=
  log_rpow hx _ ▸ log_lt_log (by positivity) h

/--
lemma `lt_log_of_pow_lt` / 引理 `lt_log_of_pow_lt`

English:
lemma lt_log_of_pow_lt
  given: (hx : 0 < x) (h : x ^ n < y)
  statement: n * log x < log y
  proof: lt_log_of_rpow_lt hx (rpow_natCast _ _ ▸ h)

中文:
引理 lt_log_of_pow_lt
  条件: (hx : 0 < x) (h : x ^ n < y)
  结论: n * log x < log y
  证明: lt_log_of_rpow_lt hx (rpow_natCast _ _ ▸ h)

Depends on / 依赖: lt_log_of_rpow_lt, rpow_natCast
-/
lemma lt_log_of_pow_lt (hx : 0 < x) (h : x ^ n < y) : n * log x < log y :=
  lt_log_of_rpow_lt hx (rpow_natCast _ _ ▸ h)

/--
lemma `lt_log_of_zpow_lt` / 引理 `lt_log_of_zpow_lt`

English:
lemma lt_log_of_zpow_lt
  given: {n : Int} (hx : 0 < x) (h : x ^ n < y)
  statement: n * log x < log y
  proof: lt_log_of_rpow_lt hx (rpow_intCast _ _ ▸ h)

中文:
引理 lt_log_of_zpow_lt
  条件: {n : 整数} (hx : 0 < x) (h : x ^ n < y)
  结论: n * log x < log y
  证明: lt_log_of_rpow_lt hx (rpow_intCast _ _ ▸ h)

Depends on / 依赖: lt_log_of_rpow_lt, rpow_intCast
-/
lemma lt_log_of_zpow_lt {n : Int} (hx : 0 < x) (h : x ^ n < y) : n * log x < log y :=
  lt_log_of_rpow_lt hx (rpow_intCast _ _ ▸ h)

/--
lemma `rpow_lt_of_lt_log` / 引理 `rpow_lt_of_lt_log`

English:
lemma rpow_lt_of_lt_log
  given: (hy : 0 < y) (h : log x < z * log y)
  statement: x < y ^ z
  proof: by
  obtain hx | hx := le_or_gt x 0
  · exact hx.trans_lt (rpow_pos_of_pos hy _)
  · exact (lt_rpow_iff_log_lt hx hy).2 h

中文:
引理 rpow_lt_of_lt_log
  条件: (hy : 0 < y) (h : log x < z * log y)
  结论: x < y ^ z
  证明: by
  obtain hx | hx := le_or_gt x 0
  · exact hx.trans_lt (rpow_pos_of_pos hy _)
  · exact (lt_rpow_iff_log_lt hx hy).2 h

Depends on / 依赖: hx.trans_lt, le_or_gt, lt_rpow_iff_log_lt, rpow_pos_of_pos, trans_lt
-/
lemma rpow_lt_of_lt_log (hy : 0 < y) (h : log x < z * log y) : x < y ^ z := by
  obtain hx | hx := le_or_gt x 0
  · exact hx.trans_lt (rpow_pos_of_pos hy _)
  · exact (lt_rpow_iff_log_lt hx hy).2 h

/--
lemma `pow_lt_of_lt_log` / 引理 `pow_lt_of_lt_log`

English:
lemma pow_lt_of_lt_log
  given: (hy : 0 < y) (h : log x < n * log y)
  statement: x < y ^ n
  proof: rpow_natCast _ _ ▸ rpow_lt_of_lt_log hy h

中文:
引理 pow_lt_of_lt_log
  条件: (hy : 0 < y) (h : log x < n * log y)
  结论: x < y ^ n
  证明: rpow_natCast _ _ ▸ rpow_lt_of_lt_log hy h

Depends on / 依赖: rpow_lt_of_lt_log, rpow_natCast
-/
lemma pow_lt_of_lt_log (hy : 0 < y) (h : log x < n * log y) : x < y ^ n :=
  rpow_natCast _ _ ▸ rpow_lt_of_lt_log hy h

/--
lemma `zpow_lt_of_lt_log` / 引理 `zpow_lt_of_lt_log`

English:
lemma zpow_lt_of_lt_log
  given: {n : Int} (hy : 0 < y) (h : log x < n * log y)
  statement: x < y ^ n
  proof: rpow_intCast _ _ ▸ rpow_lt_of_lt_log hy h

中文:
引理 zpow_lt_of_lt_log
  条件: {n : 整数} (hy : 0 < y) (h : log x < n * log y)
  结论: x < y ^ n
  证明: rpow_intCast _ _ ▸ rpow_lt_of_lt_log hy h

Depends on / 依赖: rpow_intCast, rpow_lt_of_lt_log
-/
lemma zpow_lt_of_lt_log {n : Int} (hy : 0 < y) (h : log x < n * log y) : x < y ^ n :=
  rpow_intCast _ _ ▸ rpow_lt_of_lt_log hy h

/--
theorem `rpow_le_one_iff_of_pos` / 定理 `rpow_le_one_iff_of_pos`

English:
theorem rpow_le_one_iff_of_pos
  given: (hx : 0 < x)
  statement: x ^ y <= 1 ↔ 1 <= x ∧ y <= 0 ∨ x <= 1 ∧ 0 <= y
  proof: by
  rw [rpow_def_of_pos hx]; rw [exp_le_one_iff]; rw [mul_nonpos_iff]; rw [log_nonneg_iff hx]; rw [log_nonpos_iff hx.le]

中文:
定理 rpow_le_one_iff_of_pos
  条件: (hx : 0 < x)
  结论: x ^ y <= 1 ↔ 1 <= x ∧ y <= 0 ∨ x <= 1 ∧ 0 <= y
  证明: by
  rw [rpow_def_of_pos hx]; rw [exp_le_one_iff]; rw [mul_nonpos_iff]; rw [log_nonneg_iff hx]; rw [log_nonpos_iff hx.le]

Depends on / 依赖: exp_le_one_iff, hx.le, log_nonneg_iff, log_nonpos_iff, mul_nonpos_iff, rpow_def_of_pos
-/
theorem rpow_le_one_iff_of_pos (hx : 0 < x) : x ^ y <= 1 ↔ 1 <= x ∧ y <= 0 ∨ x <= 1 ∧ 0 <= y := by
  rw [rpow_def_of_pos hx]; rw [exp_le_one_iff]; rw [mul_nonpos_iff]; rw [log_nonneg_iff hx]; rw [log_nonpos_iff hx.le]

/--
theorem `abs_log_mul_self_rpow_lt` / 定理 `abs_log_mul_self_rpow_lt`

English:
theorem abs_log_mul_self_rpow_lt
  given: (x t : Real) (h1 : 0 < x) (h2 : x <= 1) (ht : 0 < t)
  proof: by
  rw [lt_div_iff₀ ht]
  have := abs_log_mul_self_lt (x ^ t) (rpow_pos_of_pos h1 t) (rpow_le_one h1.le h2 ht.le)
  rwa [log_rpow h1, mul_assoc, abs_mul, abs_of_pos ht, mul_comm] at this

中文:
定理 abs_log_mul_self_rpow_lt
  条件: (x t : 实数) (h1 : 0 < x) (h2 : x <= 1) (ht : 0 < t)
  证明: by
  rw [lt_div_iff₀ ht]
  have := abs_log_mul_self_lt (x ^ t) (rpow_pos_of_pos h1 t) (rpow_le_one h1.le h2 ht.le)
  rwa [log_rpow h1, mul_assoc, abs_mul, abs_of_pos ht, mul_comm] at this

Depends on / 依赖: abs_log_mul_self_lt, abs_mul, abs_of_pos, h1.le, ht.le, log_rpow, mul_assoc, mul_comm, rpow_le_one, rpow_pos_of_pos
-/
theorem abs_log_mul_self_rpow_lt (x t : Real) (h1 : 0 < x) (h2 : x <= 1) (ht : 0 < t) :
    |log x * x ^ t| < 1 / t := by
  rw [lt_div_iff₀ ht]
  have := abs_log_mul_self_lt (x ^ t) (rpow_pos_of_pos h1 t) (rpow_le_one h1.le h2 ht.le)
  rwa [log_rpow h1, mul_assoc, abs_mul, abs_of_pos ht, mul_comm] at this

/--
lemma `log_le_rpow_div` / 引理 `log_le_rpow_div`

English:
lemma log_le_rpow_div
  given: {x ε : Real} (hx : 0 <= x) (hε : 0 < ε)
  statement: log x <= x ^ ε / ε
  proof: by
  rcases hx.eq_or_lt with rfl | h
  · rw [log_zero, zero_rpow hε.ne', zero_div]
  rw [le_div_iff₀' hε]
exact (log_rpow h ε).symm.trans_le (log_le_sub_one_of_pos <| rpow_pos_of_pos h ε).trans
    (sub_one_lt _).le

中文:
引理 log_le_rpow_div
  条件: {x ε : 实数} (hx : 0 <= x) (hε : 0 < ε)
  结论: log x <= x ^ ε / ε
  证明: by
  rcases hx.eq_or_lt with rfl | h
  · rw [log_zero, zero_rpow hε.ne', zero_div]
  rw [le_div_iff₀' hε]
exact (log_rpow h ε).symm.trans_le (log_le_sub_one_of_pos <| rpow_pos_of_pos h ε).trans
    (sub_one_lt _).le

Depends on / 依赖: eq_or_lt, hx.eq_or_lt, log_le_sub_one_of_pos, log_rpow, log_zero, rpow_pos_of_pos, sub_one_lt, symm.trans_le, trans_le, zero_div, zero_rpow
-/
lemma log_le_rpow_div {x ε : Real} (hx : 0 <= x) (hε : 0 < ε) : log x <= x ^ ε / ε := by
  rcases hx.eq_or_lt with rfl | h
  · rw [log_zero, zero_rpow hε.ne', zero_div]
  rw [le_div_iff₀' hε]
exact (log_rpow h ε).symm.trans_le (log_le_sub_one_of_pos <| rpow_pos_of_pos h ε).trans
    (sub_one_lt _).le

/--
lemma `log_natCast_le_rpow_div` / 引理 `log_natCast_le_rpow_div`

English:
lemma log_natCast_le_rpow_div
  given: (n : Nat) {ε : Real} (hε : 0 < ε)
  statement: log n <= n ^ ε / ε
  proof: log_le_rpow_div n.cast_nonneg hε

中文:
引理 log_natCast_le_rpow_div
  条件: (n : 自然数) {ε : 实数} (hε : 0 < ε)
  结论: log n <= n ^ ε / ε
  证明: log_le_rpow_div n.cast_nonneg hε

Depends on / 依赖: cast_nonneg, log_le_rpow_div, n.cast_nonneg
-/
lemma log_natCast_le_rpow_div (n : Nat) {ε : Real} (hε : 0 < ε) : log n <= n ^ ε / ε :=
  log_le_rpow_div n.cast_nonneg hε

/--
lemma `strictMono_rpow_of_base_gt_one` / 引理 `strictMono_rpow_of_base_gt_one`

English:
lemma strictMono_rpow_of_base_gt_one
  given: {b : Real} (hb : 1 < b)
  proof: by
  simp_rw [Real.rpow_def_of_pos (zero_lt_one.trans hb)]
exact exp_strictMono.comp StrictMono.const_mul strictMono_id Real.log_pos hb

中文:
引理 strictMono_rpow_of_base_gt_one
  条件: {b : 实数} (hb : 1 < b)
  证明: by
  simp_rw [Real.rpow_def_of_pos (zero_lt_one.trans hb)]
exact exp_strictMono.comp StrictMono.const_mul strictMono_id Real.log_pos hb

Depends on / 依赖: Real.log_pos, Real.rpow_def_of_pos, StrictMono, StrictMono.const_mul, const_mul, exp_strictMono, exp_strictMono.comp, log_pos, rpow_def_of_pos, simp_rw, strictMono_id, zero_lt_one, zero_lt_one.trans
-/
lemma strictMono_rpow_of_base_gt_one {b : Real} (hb : 1 < b) :
    StrictMono (b ^ · : Real -> Real) := by
  simp_rw [Real.rpow_def_of_pos (zero_lt_one.trans hb)]
exact exp_strictMono.comp StrictMono.const_mul strictMono_id Real.log_pos hb

/--
lemma `monotone_rpow_of_base_ge_one` / 引理 `monotone_rpow_of_base_ge_one`

English:
lemma monotone_rpow_of_base_ge_one
  given: {b : Real} (hb : 1 <= b)
  proof: by
  rcases lt_or_eq_of_le hb with hb | rfl
  case inl => exact (strictMono_rpow_of_base_gt_one hb).monotone
  case inr => intro _ _ _; simp

中文:
引理 monotone_rpow_of_base_ge_one
  条件: {b : 实数} (hb : 1 <= b)
  证明: by
  rcases lt_or_eq_of_le hb with hb | rfl
  case inl => exact (strictMono_rpow_of_base_gt_one hb).monotone
  case inr => intro _ _ _; simp

Depends on / 依赖: lt_or_eq_of_le, monotone, strictMono_rpow_of_base_gt_one
-/
lemma monotone_rpow_of_base_ge_one {b : Real} (hb : 1 <= b) :
    Monotone (b ^ · : Real -> Real) := by
  rcases lt_or_eq_of_le hb with hb | rfl
  case inl => exact (strictMono_rpow_of_base_gt_one hb).monotone
  case inr => intro _ _ _; simp

/--
lemma `strictAnti_rpow_of_base_lt_one` / 引理 `strictAnti_rpow_of_base_lt_one`

English:
lemma strictAnti_rpow_of_base_lt_one
  given: {b : Real} (hb₀ : 0 < b) (hb₁ : b < 1)
  proof: by
  simp_rw [Real.rpow_def_of_pos hb₀]
exact exp_strictMono.comp_strictAnti StrictMono.const_mul_of_neg strictMono_id
 Real.log_neg hb₀ hb₁

中文:
引理 strictAnti_rpow_of_base_lt_one
  条件: {b : 实数} (hb₀ : 0 < b) (hb₁ : b < 1)
  证明: by
  simp_rw [Real.rpow_def_of_pos hb₀]
exact exp_strictMono.comp_strictAnti StrictMono.const_mul_of_neg strictMono_id
 Real.log_neg hb₀ hb₁

Depends on / 依赖: Real.log_neg, Real.rpow_def_of_pos, StrictMono, StrictMono.const_mul_of_neg, comp_strictAnti, const_mul_of_neg, exp_strictMono, exp_strictMono.comp_strictAnti, log_neg, rpow_def_of_pos, simp_rw, strictMono_id
-/
lemma strictAnti_rpow_of_base_lt_one {b : Real} (hb₀ : 0 < b) (hb₁ : b < 1) :
    StrictAnti (b ^ · : Real -> Real) := by
  simp_rw [Real.rpow_def_of_pos hb₀]
exact exp_strictMono.comp_strictAnti StrictMono.const_mul_of_neg strictMono_id
 Real.log_neg hb₀ hb₁

/--
lemma `antitone_rpow_of_base_le_one` / 引理 `antitone_rpow_of_base_le_one`

English:
lemma antitone_rpow_of_base_le_one
  given: {b : Real} (hb₀ : 0 < b) (hb₁ : b <= 1)
  proof: by
  rcases lt_or_eq_of_le hb₁ with hb₁ | rfl
  case inl => exact (strictAnti_rpow_of_base_lt_one hb₀ hb₁).antitone
  case inr => intro _ _ _; simp

中文:
引理 antitone_rpow_of_base_le_one
  条件: {b : 实数} (hb₀ : 0 < b) (hb₁ : b <= 1)
  证明: by
  rcases lt_or_eq_of_le hb₁ with hb₁ | rfl
  case inl => exact (strictAnti_rpow_of_base_lt_one hb₀ hb₁).antitone
  case inr => intro _ _ _; simp

Depends on / 依赖: antitone, lt_or_eq_of_le, strictAnti_rpow_of_base_lt_one
-/
lemma antitone_rpow_of_base_le_one {b : Real} (hb₀ : 0 < b) (hb₁ : b <= 1) :
    Antitone (b ^ · : Real -> Real) := by
  rcases lt_or_eq_of_le hb₁ with hb₁ | rfl
  case inl => exact (strictAnti_rpow_of_base_lt_one hb₀ hb₁).antitone
  case inr => intro _ _ _; simp

/--
lemma `rpow_right_inj` / 引理 `rpow_right_inj`

English:
lemma rpow_right_inj
  given: (hx₀ : 0 < x) (hx₁ : x != 1)
  statement: x ^ y = x ^ z ↔ y = z
  proof: by
  refine ⟨fun H => ?_, fun H => by rw [H]⟩
  rcases hx₁.lt_or_gt with h | h
  · exact (strictAnti_rpow_of_base_lt_one hx₀ h).injective H
  · exact (strictMono_rpow_of_base_gt_one h).injective H

中文:
引理 rpow_right_inj
  条件: (hx₀ : 0 < x) (hx₁ : x != 1)
  结论: x ^ y = x ^ z ↔ y = z
  证明: by
  refine ⟨fun H => ?_, fun H => by rw [H]⟩
  rcases hx₁.lt_or_gt with h | h
  · exact (strictAnti_rpow_of_base_lt_one hx₀ h).injective H
  · exact (strictMono_rpow_of_base_gt_one h).injective H

Depends on / 依赖: injective, lt_or_gt, strictAnti_rpow_of_base_lt_one, strictMono_rpow_of_base_gt_one
-/
lemma rpow_right_inj (hx₀ : 0 < x) (hx₁ : x != 1) : x ^ y = x ^ z ↔ y = z := by
  refine ⟨fun H => ?_, fun H => by rw [H]⟩
  rcases hx₁.lt_or_gt with h | h
  · exact (strictAnti_rpow_of_base_lt_one hx₀ h).injective H
  · exact (strictMono_rpow_of_base_gt_one h).injective H

/--
lemma `rpow_le_rpow_of_exponent_le_or_ge` / 引理 `rpow_le_rpow_of_exponent_le_or_ge`

English:
lemma rpow_le_rpow_of_exponent_le_or_ge
  statement: {x y z : Real}
  proof: by
  rcases h with ⟨x1, yz⟩ | ⟨x0, x1, zy⟩
  · exact Real.rpow_le_rpow_of_exponent_le x1 yz
  · exact Real.rpow_le_rpow_of_exponent_ge x0 x1 zy

中文:
引理 rpow_le_rpow_of_exponent_le_or_ge
  结论: {x y z : 实数}
  证明: by
  rcases h with ⟨x1, yz⟩ | ⟨x0, x1, zy⟩
  · exact Real.rpow_le_rpow_of_exponent_le x1 yz
  · exact Real.rpow_le_rpow_of_exponent_ge x0 x1 zy
-/
@[bound] lemma rpow_le_rpow_of_exponent_le_or_ge {x y z : Real}
    (h : 1 <= x ∧ y <= z ∨ 0 < x ∧ x <= 1 ∧ z <= y) : x ^ y <= x ^ z := by
  rcases h with ⟨x1, yz⟩ | ⟨x0, x1, zy⟩
  · exact Real.rpow_le_rpow_of_exponent_le x1 yz
  · exact Real.rpow_le_rpow_of_exponent_ge x0 x1 zy

end Real

namespace Complex

/--
lemma `norm_prime_cpow_le_one_half` / 引理 `norm_prime_cpow_le_one_half`

English:
lemma norm_prime_cpow_le_one_half
  given: (p : Nat.Primes) {s : Complex} (hs : 1 < s.re)
  proof: by
  rw [norm_natCast_cpow_of_re_ne_zero p <| by rw [neg_re]; linarith only [hs]]
  refine (Real.rpow_le_rpow_of_nonpos zero_lt_two (Nat.cast_le.mpr p.prop.two_le) <|
    by rw [neg_re]; linarith only [hs]).trans ?_
  rw [one_div]; rw [← Real.rpow_neg_one]
exact Real.rpow_le_rpow_of_exponent_le one_le_two (neg_lt_neg hs).le

中文:
引理 norm_prime_cpow_le_one_half
  条件: (p : 自然数.Primes) {s : 复形} (hs : 1 < s.re)
  证明: by
  rw [norm_natCast_cpow_of_re_ne_zero p <| by rw [neg_re]; linarith only [hs]]
  refine (Real.rpow_le_rpow_of_nonpos zero_lt_two (Nat.cast_le.mpr p.prop.two_le) <|
    by rw [neg_re]; linarith only [hs]).trans ?_
  rw [one_div]; rw [← Real.rpow_neg_one]
exact Real.rpow_le_rpow_of_exponent_le one_le_two (neg_lt_neg hs).le

Depends on / 依赖: Nat.cast_le.mpr, Real.rpow_le_rpow_of_exponent_le, Real.rpow_le_rpow_of_nonpos, Real.rpow_neg_one, cast_le, neg_lt_neg, neg_re, norm_natCast_cpow_of_re_ne_zero, one_div, one_le_two, p.prop.two_le, rpow_le_rpow_of_exponent_le, rpow_le_rpow_of_nonpos, rpow_neg_one, two_le, zero_lt_two
-/
lemma norm_prime_cpow_le_one_half (p : Nat.Primes) {s : Complex} (hs : 1 < s.re) :
    ‖(p : Complex) ^ (-s)‖ <= 1 / 2 := by
  rw [norm_natCast_cpow_of_re_ne_zero p <| by rw [neg_re]; linarith only [hs]]
  refine (Real.rpow_le_rpow_of_nonpos zero_lt_two (Nat.cast_le.mpr p.prop.two_le) <|
    by rw [neg_re]; linarith only [hs]).trans ?_
  rw [one_div]; rw [← Real.rpow_neg_one]
exact Real.rpow_le_rpow_of_exponent_le one_le_two (neg_lt_neg hs).le

/--
lemma `one_sub_prime_cpow_ne_zero` / 引理 `one_sub_prime_cpow_ne_zero`

English:
lemma one_sub_prime_cpow_ne_zero
  given: {p : Nat} (hp : p.Prime) {s : Complex} (hs : 1 < s.re)
  proof: by
  refine sub_ne_zero_of_ne fun H => ?_
  have := norm_prime_cpow_le_one_half ⟨p, hp⟩ hs
  simp only at this
  rw [← H]; rw [norm_one] at this
  norm_num at this

中文:
引理 one_sub_prime_cpow_ne_zero
  条件: {p : 自然数} (hp : p.素) {s : 复形} (hs : 1 < s.re)
  证明: by
  refine sub_ne_zero_of_ne fun H => ?_
  have := norm_prime_cpow_le_one_half ⟨p, hp⟩ hs
  simp only at this
  rw [← H]; rw [norm_one] at this
  norm_num at this

Depends on / 依赖: norm_one, norm_prime_cpow_le_one_half, sub_ne_zero_of_ne
-/
lemma one_sub_prime_cpow_ne_zero {p : Nat} (hp : p.Prime) {s : Complex} (hs : 1 < s.re) :
    1 - (p : Complex) ^ (-s) != 0 := by
  refine sub_ne_zero_of_ne fun H => ?_
  have := norm_prime_cpow_le_one_half ⟨p, hp⟩ hs
  simp only at this
  rw [← H]; rw [norm_one] at this
  norm_num at this

/--
lemma `norm_natCast_cpow_le_norm_natCast_cpow_of_pos` / 引理 `norm_natCast_cpow_le_norm_natCast_cpow_of_pos`

English:
lemma norm_natCast_cpow_le_norm_natCast_cpow_of_pos
  statement: {n : Nat} (hn : 0 < n) {w z : Complex}
  proof: by
  simp_rw [norm_natCast_cpow_of_pos hn]
  exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) h

中文:
引理 norm_natCast_cpow_le_norm_natCast_cpow_of_pos
  结论: {n : 自然数} (hn : 0 < n) {w z : 复形}
  证明: by
  simp_rw [norm_natCast_cpow_of_pos hn]
  exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) h

Depends on / 依赖: Real.rpow_le_rpow_of_exponent_le, norm_natCast_cpow_of_pos, rpow_le_rpow_of_exponent_le, simp_rw
-/
lemma norm_natCast_cpow_le_norm_natCast_cpow_of_pos {n : Nat} (hn : 0 < n) {w z : Complex}
    (h : w.re <= z.re) :
    ‖(n : Complex) ^ w‖ <= ‖(n : Complex) ^ z‖ := by
  simp_rw [norm_natCast_cpow_of_pos hn]
  exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) h

/--
lemma `norm_natCast_cpow_le_norm_natCast_cpow_iff` / 引理 `norm_natCast_cpow_le_norm_natCast_cpow_iff`

English:
lemma norm_natCast_cpow_le_norm_natCast_cpow_iff
  given: {n : Nat} (hn : 1 < n) {w z : Complex}
  proof: by
  simp_rw [norm_natCast_cpow_of_pos (Nat.zero_lt_of_lt hn),
    Real.rpow_le_rpow_left_iff (Nat.one_lt_cast.mpr hn)]

中文:
引理 norm_natCast_cpow_le_norm_natCast_cpow_iff
  条件: {n : 自然数} (hn : 1 < n) {w z : 复形}
  证明: by
  simp_rw [norm_natCast_cpow_of_pos (Nat.zero_lt_of_lt hn),
    Real.rpow_le_rpow_left_iff (Nat.one_lt_cast.mpr hn)]

Depends on / 依赖: C.str, Nat.one_lt_cast.mpr, Nat.zero_lt_of_lt, Real.rpow_le_rpow_left_iff, norm_natCast_cpow_of_pos, one_lt_cast, rpow_le_rpow_left_iff, simp_rw, zero_lt_of_lt
-/
lemma norm_natCast_cpow_le_norm_natCast_cpow_iff {n : Nat} (hn : 1 < n) {w z : Complex} :
    ‖(n : Complex) ^ w‖ <= ‖(n : Complex) ^ z‖ ↔ w.re <= z.re := by
  simp_rw [norm_natCast_cpow_of_pos (Nat.zero_lt_of_lt hn),
    Real.rpow_le_rpow_left_iff (Nat.one_lt_cast.mpr hn)]

/--
lemma `norm_log_natCast_le_rpow_div` / 引理 `norm_log_natCast_le_rpow_div`

English:
lemma norm_log_natCast_le_rpow_div
  given: (n : Nat) {ε : Real} (hε : 0 < ε)
  statement: ‖log n‖ <= n ^ ε / ε
  proof: by
  rcases n.eq_zero_or_pos with rfl | h
  · rw [Nat.cast_zero, Nat.cast_zero, log_zero, norm_zero, Real.zero_rpow hε.ne', zero_div]
  rw [← natCast_log]; rw [norm_real]; rw [norm_of_nonneg <| Real.log_nonneg <| by
    exact_mod_cast Nat.one_le_of_lt h.lt]
  exact Real.log_natCast_le_rpow_div n hε

中文:
引理 norm_log_natCast_le_rpow_div
  条件: (n : 自然数) {ε : 实数} (hε : 0 < ε)
  结论: ‖log n‖ <= n ^ ε / ε
  证明: by
  rcases n.eq_zero_or_pos with rfl | h
  · rw [Nat.cast_zero, Nat.cast_zero, log_zero, norm_zero, Real.zero_rpow hε.ne', zero_div]
  rw [← natCast_log]; rw [norm_real]; rw [norm_of_nonneg <| Real.log_nonneg <| by
    exact_mod_cast Nat.one_le_of_lt h.lt]
  exact Real.log_natCast_le_rpow_div n hε

Depends on / 依赖: Nat.cast_zero, Nat.one_le_of_lt, Real.log_natCast_le_rpow_div, Real.log_nonneg, Real.zero_rpow, cast_zero, eq_zero_or_pos, h.lt, log_natCast_le_rpow_div, log_nonneg, log_zero, n.eq_zero_or_pos, natCast_log, norm_of_nonneg, norm_real, norm_zero, one_le_of_lt, zero_div, zero_rpow
-/
lemma norm_log_natCast_le_rpow_div (n : Nat) {ε : Real} (hε : 0 < ε) : ‖log n‖ <= n ^ ε / ε := by
  rcases n.eq_zero_or_pos with rfl | h
  · rw [Nat.cast_zero, Nat.cast_zero, log_zero, norm_zero, Real.zero_rpow hε.ne', zero_div]
  rw [← natCast_log]; rw [norm_real]; rw [norm_of_nonneg <| Real.log_nonneg <| by
    exact_mod_cast Nat.one_le_of_lt h.lt]
  exact Real.log_natCast_le_rpow_div n hε

end Complex


/-!
## Square roots of reals
-/


namespace Real

variable {z x y : Real}

section Sqrt

/--
theorem `sqrt_eq_rpow` / 定理 `sqrt_eq_rpow`

English:
theorem sqrt_eq_rpow
  given: (x : Real)
  statement: √x = x ^ (1 / (2 : Real))
  proof: by
  obtain h | h := le_or_gt 0 x
  · rw [← mul_self_inj_of_nonneg (sqrt_nonneg _) (rpow_nonneg h _), mul_self_sqrt h, ← sq,
      ← rpow_natCast, ← rpow_mul h]
    simp
  · have : 1 / (2 : Real) * π = π / (2 : Real) := by ring
    rw [sqrt_eq_zero_of_nonpos h.le]; rw [rpow_def_of_neg h]; rw [this]; rw [cos_pi_div_two]; rw [mul_zero]

中文:
定理 sqrt_eq_rpow
  条件: (x : 实数)
  结论: √x = x ^ (1 / (2 : 实数))
  证明: by
  obtain h | h := le_or_gt 0 x
  · rw [← mul_self_inj_of_nonneg (sqrt_nonneg _) (rpow_nonneg h _), mul_self_sqrt h, ← sq,
      ← rpow_natCast, ← rpow_mul h]
    simp
  · have : 1 / (2 : Real) * π = π / (2 : Real) := by ring
    rw [sqrt_eq_zero_of_nonpos h.le]; rw [rpow_def_of_neg h]; rw [this]; rw [cos_pi_div_two]; rw [mul_zero]

Depends on / 依赖: cos_pi_div_two, h.le, le_or_gt, mul_self_inj_of_nonneg, mul_self_sqrt, mul_zero, rpow_def_of_neg, rpow_mul, rpow_natCast, rpow_nonneg, sqrt_eq_zero_of_nonpos, sqrt_nonneg
-/
theorem sqrt_eq_rpow (x : Real) : √x = x ^ (1 / (2 : Real)) := by
  obtain h | h := le_or_gt 0 x
  · rw [← mul_self_inj_of_nonneg (sqrt_nonneg _) (rpow_nonneg h _), mul_self_sqrt h, ← sq,
      ← rpow_natCast, ← rpow_mul h]
    simp
  · have : 1 / (2 : Real) * π = π / (2 : Real) := by ring
    rw [sqrt_eq_zero_of_nonpos h.le]; rw [rpow_def_of_neg h]; rw [this]; rw [cos_pi_div_two]; rw [mul_zero]

/--
theorem `rpow_div_two_eq_sqrt` / 定理 `rpow_div_two_eq_sqrt`

English:
theorem rpow_div_two_eq_sqrt
  given: {x : Real} (r : Real) (hx : 0 <= x)
  statement: x ^ (r / 2) = √x ^ r
  proof: by
  rw [sqrt_eq_rpow]; rw [← rpow_mul hx]
  congr
  ring

中文:
定理 rpow_div_two_eq_sqrt
  条件: {x : 实数} (r : 实数) (hx : 0 <= x)
  结论: x ^ (r / 2) = √x ^ r
  证明: by
  rw [sqrt_eq_rpow]; rw [← rpow_mul hx]
  congr
  ring

Depends on / 依赖: rpow_mul, sqrt_eq_rpow
-/
theorem rpow_div_two_eq_sqrt {x : Real} (r : Real) (hx : 0 <= x) : x ^ (r / 2) = √x ^ r := by
  rw [sqrt_eq_rpow]; rw [← rpow_mul hx]
  congr
  ring

end Sqrt

end Real

namespace Complex

/--
lemma `cpow_inv_two_re` / 引理 `cpow_inv_two_re`

English:
lemma cpow_inv_two_re
  given: (x : Complex)
  statement: (x ^ (2⁻¹ : Complex)).re = √((‖x‖ + x.re) / 2)
  proof: by
  rw [← ofReal_ofNat]; rw [← ofReal_inv]; rw [cpow_ofReal_re]; rw [← div_eq_mul_inv]; rw [← one_div]; rw [← Real.sqrt_eq_rpow]; rw [cos_half]; rw [← sqrt_mul]; rw [← mul_div_assoc]; rw [mul_add]; rw [mul_one]; rw [norm_mul_cos_arg]
  exacts [norm_nonneg _, (neg_pi_lt_arg _).le, arg_le_pi _]

中文:
引理 cpow_inv_two_re
  条件: (x : 复形)
  结论: (x ^ (2⁻¹ : 复形)).re = √((‖x‖ + x.re) / 2)
  证明: by
  rw [← ofReal_ofNat]; rw [← ofReal_inv]; rw [cpow_ofReal_re]; rw [← div_eq_mul_inv]; rw [← one_div]; rw [← Real.sqrt_eq_rpow]; rw [cos_half]; rw [← sqrt_mul]; rw [← mul_div_assoc]; rw [mul_add]; rw [mul_one]; rw [norm_mul_cos_arg]
  exacts [norm_nonneg _, (neg_pi_lt_arg _).le, arg_le_pi _]

Depends on / 依赖: Real.sqrt_eq_rpow, arg_le_pi, cos_half, cpow_ofReal_re, div_eq_mul_inv, exacts, mul_add, mul_div_assoc, mul_one, neg_pi_lt_arg, norm_mul_cos_arg, norm_nonneg, ofReal_inv, ofReal_ofNat, one_div, sqrt_eq_rpow, sqrt_mul
-/
lemma cpow_inv_two_re (x : Complex) : (x ^ (2⁻¹ : Complex)).re = √((‖x‖ + x.re) / 2) := by
  rw [← ofReal_ofNat]; rw [← ofReal_inv]; rw [cpow_ofReal_re]; rw [← div_eq_mul_inv]; rw [← one_div]; rw [← Real.sqrt_eq_rpow]; rw [cos_half]; rw [← sqrt_mul]; rw [← mul_div_assoc]; rw [mul_add]; rw [mul_one]; rw [norm_mul_cos_arg]
  exacts [norm_nonneg _, (neg_pi_lt_arg _).le, arg_le_pi _]

/--
lemma `cpow_inv_two_im_eq_sqrt` / 引理 `cpow_inv_two_im_eq_sqrt`

English:
lemma cpow_inv_two_im_eq_sqrt
  given: {x : Complex} (hx : 0 <= x.im)
  proof: by
  rw [← ofReal_ofNat]; rw [← ofReal_inv]; rw [cpow_ofReal_im]; rw [← div_eq_mul_inv]; rw [← one_div]; rw [← Real.sqrt_eq_rpow]; rw [sin_half_eq_sqrt]; rw [← sqrt_mul (norm_nonneg _)]; rw [← mul_div_assoc]; rw [mul_sub]; rw [mul_one]; rw [norm_mul_cos_arg]
  · rwa [arg_nonneg_iff]
  · linarith [pi_pos, arg_le_pi x]

中文:
引理 cpow_inv_two_im_eq_sqrt
  条件: {x : 复形} (hx : 0 <= x.im)
  证明: by
  rw [← ofReal_ofNat]; rw [← ofReal_inv]; rw [cpow_ofReal_im]; rw [← div_eq_mul_inv]; rw [← one_div]; rw [← Real.sqrt_eq_rpow]; rw [sin_half_eq_sqrt]; rw [← sqrt_mul (norm_nonneg _)]; rw [← mul_div_assoc]; rw [mul_sub]; rw [mul_one]; rw [norm_mul_cos_arg]
  · rwa [arg_nonneg_iff]
  · linarith [pi_pos, arg_le_pi x]

Depends on / 依赖: Real.sqrt_eq_rpow, arg_le_pi, arg_nonneg_iff, cpow_ofReal_im, div_eq_mul_inv, mul_div_assoc, mul_one, mul_sub, norm_mul_cos_arg, norm_nonneg, ofReal_inv, ofReal_ofNat, one_div, pi_pos, sin_half_eq_sqrt, sqrt_eq_rpow, sqrt_mul
-/
lemma cpow_inv_two_im_eq_sqrt {x : Complex} (hx : 0 <= x.im) :
    (x ^ (2⁻¹ : Complex)).im = √((‖x‖ - x.re) / 2) := by
  rw [← ofReal_ofNat]; rw [← ofReal_inv]; rw [cpow_ofReal_im]; rw [← div_eq_mul_inv]; rw [← one_div]; rw [← Real.sqrt_eq_rpow]; rw [sin_half_eq_sqrt]; rw [← sqrt_mul (norm_nonneg _)]; rw [← mul_div_assoc]; rw [mul_sub]; rw [mul_one]; rw [norm_mul_cos_arg]
  · rwa [arg_nonneg_iff]
  · linarith [pi_pos, arg_le_pi x]

/--
lemma `cpow_inv_two_im_eq_neg_sqrt` / 引理 `cpow_inv_two_im_eq_neg_sqrt`

English:
lemma cpow_inv_two_im_eq_neg_sqrt
  given: {x : Complex} (hx : x.im < 0)
  proof: by
  rw [← ofReal_ofNat]; rw [← ofReal_inv]; rw [cpow_ofReal_im]; rw [← div_eq_mul_inv]; rw [← one_div]; rw [← Real.sqrt_eq_rpow]; rw [sin_half_eq_neg_sqrt]; rw [mul_neg]; rw [← sqrt_mul (norm_nonneg _)]; rw [← mul_div_assoc]; rw [mul_sub]; rw [mul_one]; rw [norm_mul_cos_arg]
  · linarith [pi_pos, neg_pi_lt_arg x]
  · exact (arg_neg_iff.2 hx).le

中文:
引理 cpow_inv_two_im_eq_neg_sqrt
  条件: {x : 复形} (hx : x.im < 0)
  证明: by
  rw [← ofReal_ofNat]; rw [← ofReal_inv]; rw [cpow_ofReal_im]; rw [← div_eq_mul_inv]; rw [← one_div]; rw [← Real.sqrt_eq_rpow]; rw [sin_half_eq_neg_sqrt]; rw [mul_neg]; rw [← sqrt_mul (norm_nonneg _)]; rw [← mul_div_assoc]; rw [mul_sub]; rw [mul_one]; rw [norm_mul_cos_arg]
  · linarith [pi_pos, neg_pi_lt_arg x]
  · exact (arg_neg_iff.2 hx).le

Depends on / 依赖: Real.sqrt_eq_rpow, arg_neg_iff, cpow_ofReal_im, div_eq_mul_inv, mul_div_assoc, mul_neg, mul_one, mul_sub, neg_pi_lt_arg, norm_mul_cos_arg, norm_nonneg, ofReal_inv, ofReal_ofNat, one_div, pi_pos, sin_half_eq_neg_sqrt, sqrt_eq_rpow, sqrt_mul
-/
lemma cpow_inv_two_im_eq_neg_sqrt {x : Complex} (hx : x.im < 0) :
    (x ^ (2⁻¹ : Complex)).im = -√((‖x‖ - x.re) / 2) := by
  rw [← ofReal_ofNat]; rw [← ofReal_inv]; rw [cpow_ofReal_im]; rw [← div_eq_mul_inv]; rw [← one_div]; rw [← Real.sqrt_eq_rpow]; rw [sin_half_eq_neg_sqrt]; rw [mul_neg]; rw [← sqrt_mul (norm_nonneg _)]; rw [← mul_div_assoc]; rw [mul_sub]; rw [mul_one]; rw [norm_mul_cos_arg]
  · linarith [pi_pos, neg_pi_lt_arg x]
  · exact (arg_neg_iff.2 hx).le

/--
lemma `abs_cpow_inv_two_im` / 引理 `abs_cpow_inv_two_im`

English:
lemma abs_cpow_inv_two_im
  given: (x : Complex)
  statement: |(x ^ (2⁻¹ : Complex)).im| = √((‖x‖ - x.re) / 2)
  proof: by
  rw [← ofReal_ofNat]; rw [← ofReal_inv]; rw [cpow_ofReal_im]; rw [← div_eq_mul_inv]; rw [← one_div]; rw [← Real.sqrt_eq_rpow]; rw [abs_mul]; rw [abs_of_nonneg (sqrt_nonneg _)]; rw [abs_sin_half]; rw [← sqrt_mul (norm_nonneg _)]; rw [← mul_div_assoc]; rw [mul_sub]; rw [mul_one]; rw [norm_mul_cos_arg]

中文:
引理 abs_cpow_inv_two_im
  条件: (x : 复形)
  结论: |(x ^ (2⁻¹ : 复形)).im| = √((‖x‖ - x.re) / 2)
  证明: by
  rw [← ofReal_ofNat]; rw [← ofReal_inv]; rw [cpow_ofReal_im]; rw [← div_eq_mul_inv]; rw [← one_div]; rw [← Real.sqrt_eq_rpow]; rw [abs_mul]; rw [abs_of_nonneg (sqrt_nonneg _)]; rw [abs_sin_half]; rw [← sqrt_mul (norm_nonneg _)]; rw [← mul_div_assoc]; rw [mul_sub]; rw [mul_one]; rw [norm_mul_cos_arg]

Depends on / 依赖: Real.sqrt_eq_rpow, abs_mul, abs_of_nonneg, abs_sin_half, cpow_ofReal_im, div_eq_mul_inv, mul_div_assoc, mul_one, mul_sub, norm_mul_cos_arg, norm_nonneg, ofReal_inv, ofReal_ofNat, one_div, sqrt_eq_rpow, sqrt_mul, sqrt_nonneg
-/
lemma abs_cpow_inv_two_im (x : Complex) : |(x ^ (2⁻¹ : Complex)).im| = √((‖x‖ - x.re) / 2) := by
  rw [← ofReal_ofNat]; rw [← ofReal_inv]; rw [cpow_ofReal_im]; rw [← div_eq_mul_inv]; rw [← one_div]; rw [← Real.sqrt_eq_rpow]; rw [abs_mul]; rw [abs_of_nonneg (sqrt_nonneg _)]; rw [abs_sin_half]; rw [← sqrt_mul (norm_nonneg _)]; rw [← mul_div_assoc]; rw [mul_sub]; rw [mul_one]; rw [norm_mul_cos_arg]

open scoped ComplexOrder in
/--
lemma `inv_natCast_cpow_ofReal_pos` / 引理 `inv_natCast_cpow_ofReal_pos`

English:
lemma inv_natCast_cpow_ofReal_pos
  given: {n : Nat} (hn : n != 0) (x : Real)
  proof: by
  refine RCLike.inv_pos_of_pos ?_
  rw [show (n : Complex) ^ (x : Complex) = (n : Real) ^ (x : Complex) from rfl]; rw [← ofReal_cpow n.cast_nonneg']
  positivity

中文:
引理 inv_natCast_cpow_of实数_pos
  条件: {n : 自然数} (hn : n != 0) (x : 实数)
  证明: by
  refine RCLike.inv_pos_of_pos ?_
  rw [show (n : Complex) ^ (x : Complex) = (n : Real) ^ (x : Complex) from rfl]; rw [← ofReal_cpow n.cast_nonneg']
  positivity

Depends on / 依赖: RCLike, RCLike.inv_pos_of_pos, cast_nonneg, inv_pos_of_pos, n.cast_nonneg, ofReal_cpow
-/
lemma inv_natCast_cpow_ofReal_pos {n : Nat} (hn : n != 0) (x : Real) :
    0 < ((n : Complex) ^ (x : Complex))⁻¹ := by
  refine RCLike.inv_pos_of_pos ?_
  rw [show (n : Complex) ^ (x : Complex) = (n : Real) ^ (x : Complex) from rfl]; rw [← ofReal_cpow n.cast_nonneg']
  positivity

end Complex

section Tactics

/-!
## Tactic extensions for real powers
-/
namespace Mathlib.Meta.NormNum

open Lean.Meta Qq

/--
theorem `IsNat.rpow_eq_pow` / 定理 `IsNat.rpow_eq_pow`

English:
theorem IsNat.rpow_eq_pow
  given: {b : Real} {n : Nat} (h : IsNat b n) (a : Real)
  statement: a ^ b = a ^ n
  proof: by
  rw [h.1]; rw [Real.rpow_natCast]

中文:
定理 是自然数.rpow_eq_pow
  条件: {b : 实数} {n : 自然数} (h : 是自然数 b n) (a : 实数)
  结论: a ^ b = a ^ n
  证明: by
  rw [h.1]; rw [Real.rpow_natCast]

Depends on / 依赖: Real.rpow_natCast, rpow_natCast
-/
theorem IsNat.rpow_eq_pow {b : Real} {n : Nat} (h : IsNat b n) (a : Real) : a ^ b = a ^ n := by
  rw [h.1]; rw [Real.rpow_natCast]

/--
theorem `IsInt.rpow_eq_inv_pow` / 定理 `IsInt.rpow_eq_inv_pow`

English:
theorem IsInt.rpow_eq_inv_pow
  given: {b : Real} {n : Nat} (h : IsInt b (.negOfNat n)) (a : Real)
  proof: by
  rw [h.1]; rw [Real.rpow_intCast]; rw [Int.negOfNat_eq]; rw [zpow_neg]; rw [Int.ofNat_eq_natCast]; rw [zpow_natCast]

中文:
定理 是整数.rpow_eq_inv_pow
  条件: {b : 实数} {n : 自然数} (h : 是整数 b (.negOf自然数 n)) (a : 实数)
  证明: by
  rw [h.1]; rw [Real.rpow_intCast]; rw [Int.negOfNat_eq]; rw [zpow_neg]; rw [Int.ofNat_eq_natCast]; rw [zpow_natCast]

Depends on / 依赖: Int.negOfNat_eq, Int.ofNat_eq_natCast, Real.rpow_intCast, negOfNat_eq, ofNat_eq_natCast, rpow_intCast, zpow_natCast, zpow_neg
-/
theorem IsInt.rpow_eq_inv_pow {b : Real} {n : Nat} (h : IsInt b (.negOfNat n)) (a : Real) :
    a ^ b = (a ^ n)⁻¹ := by
  rw [h.1]; rw [Real.rpow_intCast]; rw [Int.negOfNat_eq]; rw [zpow_neg]; rw [Int.ofNat_eq_natCast]; rw [zpow_natCast]

/--
theorem `IsNat.rpow_isNNRat` / 定理 `IsNat.rpow_isNNRat`

English:
theorem IsNat.rpow_isNNRat
  statement: {a b : Real} {m n d r : Nat} (ha : IsNat a m) (hb : IsNNRat b n d)
  proof: by
  rcases ha with ⟨rfl⟩
  constructor
  have : d != 0 := mod_cast hb.den_nz
  rw [hb.to_eq rfl rfl]; rw [div_eq_mul_inv]; rw [Real.rpow_natCast_mul]; rw [← Nat.cast_pow]; rw [hm]; rw [← hkl]; rw [← hr]; rw [Nat.cast_pow]; rw [Real.pow_rpow_inv_natCast] <;> positivity

中文:
定理 是自然数.rpow_isNNRat
  结论: {a b : 实数} {m n d r : 自然数} (ha : 是自然数 a m) (hb : 是NNRat b n d)
  证明: by
  rcases ha with ⟨rfl⟩
  constructor
  have : d != 0 := mod_cast hb.den_nz
  rw [hb.to_eq rfl rfl]; rw [div_eq_mul_inv]; rw [Real.rpow_natCast_mul]; rw [← Nat.cast_pow]; rw [hm]; rw [← hkl]; rw [← hr]; rw [Nat.cast_pow]; rw [Real.pow_rpow_inv_natCast] <;> positivity

Depends on / 依赖: Nat.cast_pow, Real.pow_rpow_inv_natCast, Real.rpow_natCast_mul, cast_pow, den_nz, div_eq_mul_inv, hb.den_nz, hb.to_eq, mod_cast, pow_rpow_inv_natCast, rpow_natCast_mul, to_eq
-/
theorem IsNat.rpow_isNNRat {a b : Real} {m n d r : Nat} (ha : IsNat a m) (hb : IsNNRat b n d)
    (k : Nat) (hr : r ^ d = k) (l : Nat) (hm : m ^ n = l) (hkl : k = l) : IsNat (a ^ b) r := by
  rcases ha with ⟨rfl⟩
  constructor
  have : d != 0 := mod_cast hb.den_nz
  rw [hb.to_eq rfl rfl]; rw [div_eq_mul_inv]; rw [Real.rpow_natCast_mul]; rw [← Nat.cast_pow]; rw [hm]; rw [← hkl]; rw [← hr]; rw [Nat.cast_pow]; rw [Real.pow_rpow_inv_natCast] <;> positivity

/--
theorem `IsNNRat.rpow_isNNRat` / 定理 `IsNNRat.rpow_isNNRat`

English:
theorem IsNNRat.rpow_isNNRat
  statement: (a b : Real) (na da : Nat) (ha : IsNNRat a na da)
  proof: by
  suffices IsNNRat (nr / dr : Real) nr dr by
    simpa [ha.to_eq, Real.div_rpow, hnum.1, hden.1]
  apply IsNNRat.of_raw
  rw [← hden.1]
  apply (Real.rpow_pos_of_pos _ _).ne'
  exact lt_of_le_of_ne' da.cast_nonneg ha.den_nz

中文:
定理 是NNRat.rpow_isNNRat
  结论: (a b : 实数) (na da : 自然数) (ha : 是NNRat a na da)
  证明: by
  suffices IsNNRat (nr / dr : Real) nr dr by
    simpa [ha.to_eq, Real.div_rpow, hnum.1, hden.1]
  apply IsNNRat.of_raw
  rw [← hden.1]
  apply (Real.rpow_pos_of_pos _ _).ne'
  exact lt_of_le_of_ne' da.cast_nonneg ha.den_nz

Depends on / 依赖: IsNNRat, IsNNRat.of_raw, Real.div_rpow, Real.rpow_pos_of_pos, cast_nonneg, da.cast_nonneg, den_nz, div_rpow, ha.den_nz, ha.to_eq, lt_of_le_of_ne, of_raw, rpow_pos_of_pos, to_eq
-/
theorem IsNNRat.rpow_isNNRat (a b : Real) (na da : Nat) (ha : IsNNRat a na da)
    (nr dr : Nat) (hnum : IsNat ((na : Real) ^ b) nr) (hden : IsNat ((da : Real) ^ b) dr) :
    IsNNRat (a ^ b) nr dr := by
  suffices IsNNRat (nr / dr : Real) nr dr by
    simpa [ha.to_eq, Real.div_rpow, hnum.1, hden.1]
  apply IsNNRat.of_raw
  rw [← hden.1]
  apply (Real.rpow_pos_of_pos _ _).ne'
  exact lt_of_le_of_ne' da.cast_nonneg ha.den_nz

/--
theorem `rpow_isRat_eq_inv_rpow` / 定理 `rpow_isRat_eq_inv_rpow`

English:
theorem rpow_isRat_eq_inv_rpow
  given: (a b : Real) (n d : Nat) (hb : IsRat b (Int.negOfNat n) d)
  proof: by
  rw [← Real.rpow_neg_eq_inv_rpow]; rw [hb.neg_to_eq rfl rfl]

中文:
定理 rpow_isRat_eq_inv_rpow
  条件: (a b : 实数) (n d : 自然数) (hb : 是有理数 b (整数.negOf自然数 n) d)
  证明: by
  rw [← Real.rpow_neg_eq_inv_rpow]; rw [hb.neg_to_eq rfl rfl]

Depends on / 依赖: Real.rpow_neg_eq_inv_rpow, hb.neg_to_eq, neg_to_eq, rpow_neg_eq_inv_rpow
-/
theorem rpow_isRat_eq_inv_rpow (a b : Real) (n d : Nat) (hb : IsRat b (Int.negOfNat n) d) :
    a ^ b = (a⁻¹) ^ (n / d : Real) := by
  rw [← Real.rpow_neg_eq_inv_rpow]; rw [hb.neg_to_eq rfl rfl]

open Lean in
/-- Given proofs
- that `a` is a natural number `na`;
- that `b` is a nonnegative rational number `nb / db`;

returns a tuple of
- a natural number `r` (result);
- the same number, as an expression;
- a proof that `a ^ b = r`.

Fails if `na` is not a `db`th power of a natural number.
-/
meta def proveIsNatRPowIsNNRat
    (a : Q(Real)) (na : Q(Nat)) (pa : Q(IsNat $a $na))
    (b : Q(Real)) (nb db : Q(Nat)) (pb : Q(IsNNRat $b $nb $db)) :
    MetaM (Nat × Σ r : Q(Nat), Q(IsNat ($a ^ $b) $r)) := do
  let r := (Nat.nthRoot db.natLit! na.natLit!) ^ nb.natLit!
  have er : Q(Nat) := mkRawNatLit r
  -- avoid evaluating powers in kernel
let .some ⟨c, pc⟩ ← liftM OptionT.run evalNatPow er db | failure
let .some ⟨d, pd⟩ ← liftM OptionT.run evalNatPow na nb | failure
  guard (c.natLit! = d.natLit!)
  have hcd : Q($c = $d) := (q(Eq.refl $c) : Expr)
  return (r, ⟨er, q(IsNat.rpow_isNNRat $pa $pb $c $pc $d $pd $hcd)⟩)

/-- Evaluates expressions of the form `a ^ b` when `a` and `b` are both reals.
Works if `a`, `b`, and `a ^ b` are in fact rational numbers,
except for the case `a < 0`, `b` isn't integer.

TODO: simplify terms like `(-a : ℝ) ^ (b / 3 : ℝ)` and `(-a : ℝ) ^ (b / 2 : ℝ)` too,
possibly after first considering changing the junk value. -/
@[norm_num (_ : Real) ^ (_ : Real)]
meta def evalRPow : NormNumExt where eval {u αR} e := do
  match u, αR, e with
  | 0, ~q(Real), ~q(($a : Real)^($b : Real)) =>
    match ← derive b with
    | .isNat sβ nb pb =>
      assumeInstancesCommute
      return .eqTrans q(IsNat.rpow_eq_pow $pb _) (← derive q($a ^ $nb))
    | .isNegNat sβ nb pb =>
      assumeInstancesCommute
      return .eqTrans q(IsInt.rpow_eq_inv_pow $pb _) (← derive q(($a ^ $nb)⁻¹))
    | .isNNRat _ qb nb db pb => do
      assumeInstancesCommute
      match ← derive a with
      | .isNat sa na pa => do
        let ⟨_, r, pr⟩ ← proveIsNatRPowIsNNRat a na pa b nb db pb
        return .isNat sa r pr
      | .isNNRat _ qα na da pa => do
        assumeInstancesCommute
        let ⟨rnum, ernum, pnum⟩ ←
          proveIsNatRPowIsNNRat q(Nat.rawCast $na) na q(IsNat.of_raw _ _) b nb db pb
        let ⟨rden, erden, pden⟩ ←
          proveIsNatRPowIsNNRat q(Nat.rawCast $da) da q(IsNat.of_raw _ _) b nb db pb
        return .isNNRat q(inferInstance) (rnum / rden) ernum erden
          q(IsNNRat.rpow_isNNRat $a $b $na $da $pa $ernum $erden $pnum $pden)
      | _ => failure
    | .isNegNNRat _ qb nb db pb => do
      let r ← derive q(($a⁻¹) ^ ($nb / $db : Real))
      assumeInstancesCommute
      return .eqTrans q(rpow_isRat_eq_inv_rpow $a $b $nb $db $pb) r
    | _ => failure
  | _ => failure

end Mathlib.Meta.NormNum

end Tactics
