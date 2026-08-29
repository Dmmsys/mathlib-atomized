/-
Copyright (c) 2022 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey, Chris Hughes, Abhimanyu Pallavi Sudhir, Jean Lo, Calle Sönne
-/
module

public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Int.Log

/-!
# Real logarithm base `b`

In this file we define `Real.logb` to be the logarithm of a real number in a given base `b`. We
define this as the division of the natural logarithms of the argument and the base, so that we have
a globally defined function with `logb b 0 = 0`, `logb b (-x) = logb b x`, `logb 0 x = 0`, and
`logb (-b) x = logb b x`.

We prove some basic properties of this function and its relation to `rpow`.

## Tags

logarithm, continuity
-/

@[expose] public section


open Set Filter Function

open Topology

noncomputable section

namespace Real

variable {b x y : Real}

/-- The real logarithm in a given base. As with the natural logarithm, we define `logb b x` to
be `logb b |x|` for `x < 0`, and `0` for `x = 0`. -/
@[pp_nodot]
/--
Definition of `logb` / `logb` 的定义

English:
definition logb
  signature: (b x : Real)
  body: log x / log b

中文:
定义 logb
  签名: (b x : 实数)
  定义体: log x / log b
-/
noncomputable def logb (b x : Real) : Real :=
  log x / log b

/--
theorem `log_div_log` / 定理 `log_div_log`

English:
theorem log_div_log
  statement: log x / log b = logb b x
  proof: rfl

@[simp]

中文:
定理 log_div_log
  结论: log x / log b = logb b x
  证明: rfl

@[simp]
-/
theorem log_div_log : log x / log b = logb b x :=
  rfl

@[simp]
/--
theorem `logb_zero` / 定理 `logb_zero`

English:
theorem logb_zero
  statement: logb b 0 = 0
  proof: by simp [logb]

@[simp]

中文:
定理 logb_zero
  结论: logb b 0 = 0
  证明: by simp [logb]

@[simp]
-/
theorem logb_zero : logb b 0 = 0 := by simp [logb]

@[simp]
/--
theorem `logb_one` / 定理 `logb_one`

English:
theorem logb_one
  statement: logb b 1 = 0
  proof: by simp [logb]

中文:
定理 logb_one
  结论: logb b 1 = 0
  证明: by simp [logb]
-/
theorem logb_one : logb b 1 = 0 := by simp [logb]

/--
theorem `logb_zero_left` / 定理 `logb_zero_left`

English:
theorem logb_zero_left
  statement: logb 0 x = 0
  proof: by simp only [← log_div_log, log_zero, div_zero]

中文:
定理 logb_zero_left
  结论: logb 0 x = 0
  证明: by simp only [← log_div_log, log_zero, div_zero]

Depends on / 依赖: div_zero, log_div_log, log_zero
-/
theorem logb_zero_left : logb 0 x = 0 := by simp only [← log_div_log, log_zero, div_zero]

/--
theorem `logb_zero_left_eq_zero` / 定理 `logb_zero_left_eq_zero`

English:
theorem logb_zero_left_eq_zero
  statement: logb 0 = 0
  proof: by ext; rw [logb_zero_left, Pi.zero_apply]

中文:
定理 logb_zero_left_eq_zero
  结论: logb 0 = 0
  证明: by ext; rw [logb_zero_left, Pi.zero_apply]
-/
@[simp] theorem logb_zero_left_eq_zero : logb 0 = 0 := by ext; rw [logb_zero_left, Pi.zero_apply]

/--
theorem `logb_one_left` / 定理 `logb_one_left`

English:
theorem logb_one_left
  statement: logb 1 x = 0
  proof: by simp only [← log_div_log, log_one, div_zero]

中文:
定理 logb_one_left
  结论: logb 1 x = 0
  证明: by simp only [← log_div_log, log_one, div_zero]

Depends on / 依赖: div_zero, log_div_log, log_one
-/
theorem logb_one_left : logb 1 x = 0 := by simp only [← log_div_log, log_one, div_zero]

/--
theorem `logb_one_left_eq_zero` / 定理 `logb_one_left_eq_zero`

English:
theorem logb_one_left_eq_zero
  statement: logb 1 = 0
  proof: by ext; rw [logb_one_left, Pi.zero_apply]

@[simp]

中文:
定理 logb_one_left_eq_zero
  结论: logb 1 = 0
  证明: by ext; rw [logb_one_left, Pi.zero_apply]

@[simp]
-/
@[simp] theorem logb_one_left_eq_zero : logb 1 = 0 := by ext; rw [logb_one_left, Pi.zero_apply]

@[simp]
/--
lemma `logb_self_eq_one` / 引理 `logb_self_eq_one`

English:
lemma logb_self_eq_one
  given: (hb : 1 < b)
  statement: logb b b = 1
  proof: div_self (log_pos hb).ne'

中文:
引理 logb_self_eq_one
  条件: (hb : 1 < b)
  结论: logb b b = 1
  证明: div_self (log_pos hb).ne'

Depends on / 依赖: div_self, log_pos
-/
lemma logb_self_eq_one (hb : 1 < b) : logb b b = 1 :=
  div_self (log_pos hb).ne'

/--
lemma `logb_self_eq_one_iff` / 引理 `logb_self_eq_one_iff`

English:
lemma logb_self_eq_one_iff
  statement: logb b b = 1 ↔ b != 0 ∧ b != 1 ∧ b != -1
  proof: Iff.trans ⟨fun h h' => by simp [logb, h'] at h, div_self⟩ log_ne_zero

@[simp]

中文:
引理 logb_self_eq_one_iff
  结论: logb b b = 1 ↔ b != 0 ∧ b != 1 ∧ b != -1
  证明: Iff.trans ⟨fun h h' => by simp [logb, h'] at h, div_self⟩ log_ne_zero

@[simp]

Depends on / 依赖: Iff.trans, div_self, log_ne_zero
-/
lemma logb_self_eq_one_iff : logb b b = 1 ↔ b != 0 ∧ b != 1 ∧ b != -1 :=
  Iff.trans ⟨fun h h' => by simp [logb, h'] at h, div_self⟩ log_ne_zero

@[simp]
/--
theorem `logb_abs_base` / 定理 `logb_abs_base`

English:
theorem logb_abs_base
  given: (b x : Real)
  statement: logb |b| x = logb b x
  proof: by rw [logb, logb, log_abs]

@[simp]

中文:
定理 logb_abs_base
  条件: (b x : 实数)
  结论: logb |b| x = logb b x
  证明: by rw [logb, logb, log_abs]

@[simp]

Depends on / 依赖: log_abs
-/
theorem logb_abs_base (b x : Real) : logb |b| x = logb b x := by rw [logb, logb, log_abs]

@[simp]
/--
theorem `logb_abs` / 定理 `logb_abs`

English:
theorem logb_abs
  given: (b x : Real)
  statement: logb b |x| = logb b x
  proof: by rw [logb, logb, log_abs]

@[simp]

中文:
定理 logb_abs
  条件: (b x : 实数)
  结论: logb b |x| = logb b x
  证明: by rw [logb, logb, log_abs]

@[simp]

Depends on / 依赖: log_abs
-/
theorem logb_abs (b x : Real) : logb b |x| = logb b x := by rw [logb, logb, log_abs]

@[simp]
/--
theorem `logb_neg_base_eq_logb` / 定理 `logb_neg_base_eq_logb`

English:
theorem logb_neg_base_eq_logb
  given: (b : Real)
  statement: logb (-b) = logb b
  proof: by
  ext x; rw [← logb_abs_base b x, ← logb_abs_base (-b) x, abs_neg]

@[simp]

中文:
定理 logb_neg_base_eq_logb
  条件: (b : 实数)
  结论: logb (-b) = logb b
  证明: by
  ext x; rw [← logb_abs_base b x, ← logb_abs_base (-b) x, abs_neg]

@[simp]

Depends on / 依赖: abs_neg, logb_abs_base
-/
theorem logb_neg_base_eq_logb (b : Real) : logb (-b) = logb b := by
  ext x; rw [← logb_abs_base b x, ← logb_abs_base (-b) x, abs_neg]

@[simp]
/--
theorem `logb_neg_eq_logb` / 定理 `logb_neg_eq_logb`

English:
theorem logb_neg_eq_logb
  given: (b x : Real)
  statement: logb b (-x) = logb b x
  proof: by
  rw [← logb_abs b x]; rw [← logb_abs b (-x)]; rw [abs_neg]

中文:
定理 logb_neg_eq_logb
  条件: (b x : 实数)
  结论: logb b (-x) = logb b x
  证明: by
  rw [← logb_abs b x]; rw [← logb_abs b (-x)]; rw [abs_neg]

Depends on / 依赖: abs_neg, logb_abs
-/
theorem logb_neg_eq_logb (b x : Real) : logb b (-x) = logb b x := by
  rw [← logb_abs b x]; rw [← logb_abs b (-x)]; rw [abs_neg]

/--
theorem `logb_mul` / 定理 `logb_mul`

English:
theorem logb_mul
  given: (hx : x != 0) (hy : y != 0)
  statement: logb b (x * y) = logb b x + logb b y
  proof: by
  simp_rw [logb, log_mul hx hy, add_div]

中文:
定理 logb_mul
  条件: (hx : x != 0) (hy : y != 0)
  结论: logb b (x * y) = logb b x + logb b y
  证明: by
  simp_rw [logb, log_mul hx hy, add_div]

Depends on / 依赖: add_div, log_mul, simp_rw
-/
theorem logb_mul (hx : x != 0) (hy : y != 0) : logb b (x * y) = logb b x + logb b y := by
  simp_rw [logb, log_mul hx hy, add_div]

/--
theorem `logb_div` / 定理 `logb_div`

English:
theorem logb_div
  given: (hx : x != 0) (hy : y != 0)
  statement: logb b (x / y) = logb b x - logb b y
  proof: by
  simp_rw [logb, log_div hx hy, sub_div]

@[simp]

中文:
定理 logb_div
  条件: (hx : x != 0) (hy : y != 0)
  结论: logb b (x / y) = logb b x - logb b y
  证明: by
  simp_rw [logb, log_div hx hy, sub_div]

@[simp]

Depends on / 依赖: log_div, simp_rw, sub_div
-/
theorem logb_div (hx : x != 0) (hy : y != 0) : logb b (x / y) = logb b x - logb b y := by
  simp_rw [logb, log_div hx hy, sub_div]

@[simp]
/--
theorem `logb_inv` / 定理 `logb_inv`

English:
theorem logb_inv
  given: (b x : Real)
  statement: logb b x⁻¹ = -logb b x
  proof: by simp [logb, neg_div]

@[simp]

中文:
定理 logb_inv
  条件: (b x : 实数)
  结论: logb b x⁻¹ = -logb b x
  证明: by simp [logb, neg_div]

@[simp]

Depends on / 依赖: neg_div
-/
theorem logb_inv (b x : Real) : logb b x⁻¹ = -logb b x := by simp [logb, neg_div]

@[simp]
/--
theorem `logb_inv_base` / 定理 `logb_inv_base`

English:
theorem logb_inv_base
  given: (b x : Real)
  statement: logb b⁻¹ x = -logb b x
  proof: by simp [logb, div_neg]

中文:
定理 logb_inv_base
  条件: (b x : 实数)
  结论: logb b⁻¹ x = -logb b x
  证明: by simp [logb, div_neg]

Depends on / 依赖: div_neg
-/
theorem logb_inv_base (b x : Real) : logb b⁻¹ x = -logb b x := by simp [logb, div_neg]

/--
theorem `inv_logb` / 定理 `inv_logb`

English:
theorem inv_logb
  given: (a b : Real)
  statement: (logb a b)⁻¹ = logb b a
  proof: by simp_rw [logb, inv_div]

中文:
定理 inv_logb
  条件: (a b : 实数)
  结论: (logb a b)⁻¹ = logb b a
  证明: by simp_rw [logb, inv_div]

Depends on / 依赖: inv_div, simp_rw
-/
theorem inv_logb (a b : Real) : (logb a b)⁻¹ = logb b a := by simp_rw [logb, inv_div]

/--
theorem `inv_logb_mul_base` / 定理 `inv_logb_mul_base`

English:
theorem inv_logb_mul_base
  given: {a b : Real} (h₁ : a != 0) (h₂ : b != 0) (c : Real)
  proof: by
  simp_rw [inv_logb]; exact logb_mul h₁ h₂

中文:
定理 inv_logb_mul_base
  条件: {a b : 实数} (h₁ : a != 0) (h₂ : b != 0) (c : 实数)
  证明: by
  simp_rw [inv_logb]; exact logb_mul h₁ h₂

Depends on / 依赖: inv_logb, logb_mul, simp_rw
-/
theorem inv_logb_mul_base {a b : Real} (h₁ : a != 0) (h₂ : b != 0) (c : Real) :
    (logb (a * b) c)⁻¹ = (logb a c)⁻¹ + (logb b c)⁻¹ := by
  simp_rw [inv_logb]; exact logb_mul h₁ h₂

/--
theorem `inv_logb_div_base` / 定理 `inv_logb_div_base`

English:
theorem inv_logb_div_base
  given: {a b : Real} (h₁ : a != 0) (h₂ : b != 0) (c : Real)
  proof: by
  simp_rw [inv_logb]; exact logb_div h₁ h₂

中文:
定理 inv_logb_div_base
  条件: {a b : 实数} (h₁ : a != 0) (h₂ : b != 0) (c : 实数)
  证明: by
  simp_rw [inv_logb]; exact logb_div h₁ h₂

Depends on / 依赖: inv_logb, logb_div, simp_rw
-/
theorem inv_logb_div_base {a b : Real} (h₁ : a != 0) (h₂ : b != 0) (c : Real) :
    (logb (a / b) c)⁻¹ = (logb a c)⁻¹ - (logb b c)⁻¹ := by
  simp_rw [inv_logb]; exact logb_div h₁ h₂

/--
theorem `logb_mul_base` / 定理 `logb_mul_base`

English:
theorem logb_mul_base
  given: {a b : Real} (h₁ : a != 0) (h₂ : b != 0) (c : Real)
  proof: by rw [← inv_logb_mul_base h₁ h₂ c, inv_inv]

中文:
定理 logb_mul_base
  条件: {a b : 实数} (h₁ : a != 0) (h₂ : b != 0) (c : 实数)
  证明: by rw [← inv_logb_mul_base h₁ h₂ c, inv_inv]

Depends on / 依赖: inv_inv, inv_logb_mul_base
-/
theorem logb_mul_base {a b : Real} (h₁ : a != 0) (h₂ : b != 0) (c : Real) :
    logb (a * b) c = ((logb a c)⁻¹ + (logb b c)⁻¹)⁻¹ := by rw [← inv_logb_mul_base h₁ h₂ c, inv_inv]

/--
theorem `logb_div_base` / 定理 `logb_div_base`

English:
theorem logb_div_base
  given: {a b : Real} (h₁ : a != 0) (h₂ : b != 0) (c : Real)
  proof: by rw [← inv_logb_div_base h₁ h₂ c, inv_inv]

中文:
定理 logb_div_base
  条件: {a b : 实数} (h₁ : a != 0) (h₂ : b != 0) (c : 实数)
  证明: by rw [← inv_logb_div_base h₁ h₂ c, inv_inv]

Depends on / 依赖: inv_inv, inv_logb_div_base
-/
theorem logb_div_base {a b : Real} (h₁ : a != 0) (h₂ : b != 0) (c : Real) :
    logb (a / b) c = ((logb a c)⁻¹ - (logb b c)⁻¹)⁻¹ := by rw [← inv_logb_div_base h₁ h₂ c, inv_inv]

/--
theorem `mul_logb` / 定理 `mul_logb`

English:
theorem mul_logb
  given: {a b c : Real} (h₁ : b != 0) (h₂ : b != 1) (h₃ : b != -1)
  proof: by
  unfold logb
  rw [mul_comm]; rw [div_mul_div_cancel₀ (log_ne_zero.mpr ⟨h₁]; rw [h₂]; rw [h₃⟩)]

中文:
定理 mul_logb
  条件: {a b c : 实数} (h₁ : b != 0) (h₂ : b != 1) (h₃ : b != -1)
  证明: by
  unfold logb
  rw [mul_comm]; rw [div_mul_div_cancel₀ (log_ne_zero.mpr ⟨h₁]; rw [h₂]; rw [h₃⟩)]

Depends on / 依赖: log_ne_zero, log_ne_zero.mpr, mul_comm
-/
theorem mul_logb {a b c : Real} (h₁ : b != 0) (h₂ : b != 1) (h₃ : b != -1) :
    logb a b * logb b c = logb a c := by
  unfold logb
  rw [mul_comm]; rw [div_mul_div_cancel₀ (log_ne_zero.mpr ⟨h₁]; rw [h₂]; rw [h₃⟩)]

/--
theorem `div_logb` / 定理 `div_logb`

English:
theorem div_logb
  given: {a b c : Real} (h₁ : c != 0) (h₂ : c != 1) (h₃ : c != -1)
  proof: div_div_div_cancel_left' _ _ log_ne_zero.mpr ⟨h₁, h₂, h₃⟩

中文:
定理 div_logb
  条件: {a b c : 实数} (h₁ : c != 0) (h₂ : c != 1) (h₃ : c != -1)
  证明: div_div_div_cancel_left' _ _ log_ne_zero.mpr ⟨h₁, h₂, h₃⟩

Depends on / 依赖: div_div_div_cancel_left, log_ne_zero, log_ne_zero.mpr
-/
theorem div_logb {a b c : Real} (h₁ : c != 0) (h₂ : c != 1) (h₃ : c != -1) :
    logb a c / logb b c = logb a b :=
div_div_div_cancel_left' _ _ log_ne_zero.mpr ⟨h₁, h₂, h₃⟩

/--
theorem `logb_rpow_eq_mul_logb_of_pos` / 定理 `logb_rpow_eq_mul_logb_of_pos`

English:
theorem logb_rpow_eq_mul_logb_of_pos
  given: (hx : 0 < x)
  statement: logb b (x ^ y) = y * logb b x
  proof: by
  rw [logb]; rw [log_rpow hx]; rw [logb]; rw [mul_div_assoc]

中文:
定理 logb_rpow_eq_mul_logb_of_pos
  条件: (hx : 0 < x)
  结论: logb b (x ^ y) = y * logb b x
  证明: by
  rw [logb]; rw [log_rpow hx]; rw [logb]; rw [mul_div_assoc]

Depends on / 依赖: log_rpow, mul_div_assoc
-/
theorem logb_rpow_eq_mul_logb_of_pos (hx : 0 < x) : logb b (x ^ y) = y * logb b x := by
  rw [logb]; rw [log_rpow hx]; rw [logb]; rw [mul_div_assoc]

/--
theorem `logb_pow` / 定理 `logb_pow`

English:
theorem logb_pow
  given: (b x : Real) (k : Nat)
  statement: logb b (x ^ k) = k * logb b x
  proof: by
  rw [logb]; rw [logb]; rw [log_pow]; rw [mul_div_assoc]

中文:
定理 logb_pow
  条件: (b x : 实数) (k : 自然数)
  结论: logb b (x ^ k) = k * logb b x
  证明: by
  rw [logb]; rw [logb]; rw [log_pow]; rw [mul_div_assoc]

Depends on / 依赖: log_pow, mul_div_assoc
-/
theorem logb_pow (b x : Real) (k : Nat) : logb b (x ^ k) = k * logb b x := by
  rw [logb]; rw [logb]; rw [log_pow]; rw [mul_div_assoc]

section BPosAndNeOne

variable (b_pos : 0 < b) (b_ne_one : b != 1)
include b_pos b_ne_one

@[simp]
/--
theorem `logb_rpow` / 定理 `logb_rpow`

English:
theorem logb_rpow
  statement: logb b (b ^ x) = x
  proof: by
  rw [logb]; rw [div_eq_iff]; rw [log_rpow b_pos]
  exact log_ne_zero_of_pos_of_ne_one b_pos b_ne_one

中文:
定理 logb_rpow
  结论: logb b (b ^ x) = x
  证明: by
  rw [logb]; rw [div_eq_iff]; rw [log_rpow b_pos]
  exact log_ne_zero_of_pos_of_ne_one b_pos b_ne_one

Depends on / 依赖: b_ne_one, b_pos, div_eq_iff, log_ne_zero_of_pos_of_ne_one, log_rpow
-/
theorem logb_rpow : logb b (b ^ x) = x := by
  rw [logb]; rw [div_eq_iff]; rw [log_rpow b_pos]
  exact log_ne_zero_of_pos_of_ne_one b_pos b_ne_one

/--
theorem `rpow_logb_eq_abs` / 定理 `rpow_logb_eq_abs`

English:
theorem rpow_logb_eq_abs
  given: (hx : x != 0)
  statement: b ^ logb b x = |x|
  proof: by
  apply log_injOn_pos
  · simp only [Set.mem_Ioi]
    apply rpow_pos_of_pos b_pos
  · simp only [abs_pos, mem_Ioi, Ne, hx, not_false_iff]
  rw [log_rpow b_pos]; rw [logb]; rw [log_abs]
  field [log_ne_zero_of_pos_of_ne_one b_pos b_ne_one]

@[simp]

中文:
定理 rpow_logb_eq_abs
  条件: (hx : x != 0)
  结论: b ^ logb b x = |x|
  证明: by
  apply log_injOn_pos
  · simp only [Set.mem_Ioi]
    apply rpow_pos_of_pos b_pos
  · simp only [abs_pos, mem_Ioi, Ne, hx, not_false_iff]
  rw [log_rpow b_pos]; rw [logb]; rw [log_abs]
  field [log_ne_zero_of_pos_of_ne_one b_pos b_ne_one]

@[simp]

Depends on / 依赖: Set.mem_Ioi, abs_pos, b_ne_one, b_pos, log_abs, log_injOn_pos, log_ne_zero_of_pos_of_ne_one, log_rpow, mem_Ioi, not_false_iff, rpow_pos_of_pos
-/
theorem rpow_logb_eq_abs (hx : x != 0) : b ^ logb b x = |x| := by
  apply log_injOn_pos
  · simp only [Set.mem_Ioi]
    apply rpow_pos_of_pos b_pos
  · simp only [abs_pos, mem_Ioi, Ne, hx, not_false_iff]
  rw [log_rpow b_pos]; rw [logb]; rw [log_abs]
  field [log_ne_zero_of_pos_of_ne_one b_pos b_ne_one]

@[simp]
/--
theorem `rpow_logb` / 定理 `rpow_logb`

English:
theorem rpow_logb
  given: (hx : 0 < x)
  statement: b ^ logb b x = x
  proof: by
  rw [rpow_logb_eq_abs b_pos b_ne_one hx.ne']
  exact abs_of_pos hx

中文:
定理 rpow_logb
  条件: (hx : 0 < x)
  结论: b ^ logb b x = x
  证明: by
  rw [rpow_logb_eq_abs b_pos b_ne_one hx.ne']
  exact abs_of_pos hx

Depends on / 依赖: IsReflexivePair, IsReflexivePair.mk, U.map_comp, U.obj, abs_of_pos, b_ne_one, b_pos, comp_id, hx.ne, left_triangle_components, map_comp, map_comp_assoc, map_id, otherMap, right_triangle_components, rpow_logb_eq_abs, unit.app, unit_naturality_assoc
-/
theorem rpow_logb (hx : 0 < x) : b ^ logb b x = x := by
  rw [rpow_logb_eq_abs b_pos b_ne_one hx.ne']
  exact abs_of_pos hx

/--
theorem `rpow_logb_of_neg` / 定理 `rpow_logb_of_neg`

English:
theorem rpow_logb_of_neg
  given: (hx : x < 0)
  statement: b ^ logb b x = -x
  proof: by
  rw [rpow_logb_eq_abs b_pos b_ne_one (ne_of_lt hx)]
  exact abs_of_neg hx

中文:
定理 rpow_logb_of_neg
  条件: (hx : x < 0)
  结论: b ^ logb b x = -x
  证明: by
  rw [rpow_logb_eq_abs b_pos b_ne_one (ne_of_lt hx)]
  exact abs_of_neg hx

Depends on / 依赖: abs_of_neg, b_ne_one, b_pos, ne_of_lt, rpow_logb_eq_abs
-/
theorem rpow_logb_of_neg (hx : x < 0) : b ^ logb b x = -x := by
  rw [rpow_logb_eq_abs b_pos b_ne_one (ne_of_lt hx)]
  exact abs_of_neg hx

/--
theorem `logb_eq_iff_rpow_eq` / 定理 `logb_eq_iff_rpow_eq`

English:
theorem logb_eq_iff_rpow_eq
  given: (hy : 0 < y)
  statement: logb b y = x ↔ b ^ x = y
  proof: by
  constructor <;> rintro rfl
  · exact rpow_logb b_pos b_ne_one hy
  · exact logb_rpow b_pos b_ne_one

中文:
定理 logb_eq_iff_rpow_eq
  条件: (hy : 0 < y)
  结论: logb b y = x ↔ b ^ x = y
  证明: by
  constructor <;> rintro rfl
  · exact rpow_logb b_pos b_ne_one hy
  · exact logb_rpow b_pos b_ne_one

Depends on / 依赖: b_ne_one, b_pos, logb_rpow, rpow_logb
-/
theorem logb_eq_iff_rpow_eq (hy : 0 < y) : logb b y = x ↔ b ^ x = y := by
  constructor <;> rintro rfl
  · exact rpow_logb b_pos b_ne_one hy
  · exact logb_rpow b_pos b_ne_one

/--
theorem `surjOn_logb` / 定理 `surjOn_logb`

English:
theorem surjOn_logb
  statement: SurjOn (logb b) (Ioi 0) univ
  proof: fun x _ =>
  ⟨b ^ x, rpow_pos_of_pos b_pos x, logb_rpow b_pos b_ne_one⟩

中文:
定理 surjOn_logb
  结论: 满射限制 (logb b) (左开右无界区间 0) univ
  证明: fun x _ =>
  ⟨b ^ x, rpow_pos_of_pos b_pos x, logb_rpow b_pos b_ne_one⟩
-/
theorem surjOn_logb : SurjOn (logb b) (Ioi 0) univ := fun x _ =>
  ⟨b ^ x, rpow_pos_of_pos b_pos x, logb_rpow b_pos b_ne_one⟩

/--
theorem `logb_surjective` / 定理 `logb_surjective`

English:
theorem logb_surjective
  statement: Surjective (logb b)
  proof: fun x => ⟨b ^ x, logb_rpow b_pos b_ne_one⟩

@[simp]

中文:
定理 logb_surjective
  结论: 满射 (logb b)
  证明: fun x => ⟨b ^ x, logb_rpow b_pos b_ne_one⟩

@[simp]

Depends on / 依赖: b_ne_one, b_pos, logb_rpow
-/
theorem logb_surjective : Surjective (logb b) := fun x => ⟨b ^ x, logb_rpow b_pos b_ne_one⟩

@[simp]
/--
theorem `range_logb` / 定理 `range_logb`

English:
theorem range_logb
  statement: range (logb b) = univ
  proof: (logb_surjective b_pos b_ne_one).range_eq

中文:
定理 range_logb
  结论: range (logb b) = univ
  证明: (logb_surjective b_pos b_ne_one).range_eq

Depends on / 依赖: b_ne_one, b_pos, logb_surjective, range_eq
-/
theorem range_logb : range (logb b) = univ :=
  (logb_surjective b_pos b_ne_one).range_eq

/--
theorem `surjOn_logb'` / 定理 `surjOn_logb'`

English:
theorem surjOn_logb'
  statement: SurjOn (logb b) (Iio 0) univ
  proof: by
  intro x _
  use -b ^ x
  constructor
  · simp only [Right.neg_neg_iff, Set.mem_Iio]
    apply rpow_pos_of_pos b_pos
  · rw [logb_neg_eq_logb, logb_rpow b_pos b_ne_one]

中文:
定理 surjOn_logb'
  结论: 满射限制 (logb b) (左无界右开区间 0) univ
  证明: by
  intro x _
  use -b ^ x
  constructor
  · simp only [Right.neg_neg_iff, Set.mem_Iio]
    apply rpow_pos_of_pos b_pos
  · rw [logb_neg_eq_logb, logb_rpow b_pos b_ne_one]

Depends on / 依赖: Right.neg_neg_iff, Set.mem_Iio, b_ne_one, b_pos, logb_neg_eq_logb, logb_rpow, mem_Iio, neg_neg_iff, rpow_pos_of_pos
-/
theorem surjOn_logb' : SurjOn (logb b) (Iio 0) univ := by
  intro x _
  use -b ^ x
  constructor
  · simp only [Right.neg_neg_iff, Set.mem_Iio]
    apply rpow_pos_of_pos b_pos
  · rw [logb_neg_eq_logb, logb_rpow b_pos b_ne_one]

end BPosAndNeOne

section OneLtB

variable (hb : 1 < b)
include hb

/--
theorem `b_pos` / 定理 `b_pos`

English:
theorem b_pos
  statement: 0 < b
  proof: by linarith

中文:
定理 b_pos
  结论: 0 < b
  证明: by linarith
-/
private theorem b_pos : 0 < b := by linarith

-- Name has a prime added to avoid clashing with `b_ne_one` further down the file
/--
theorem `b_ne_one'` / 定理 `b_ne_one'`

English:
theorem b_ne_one'
  statement: b != 1
  proof: by linarith

@[simp]

中文:
定理 b_ne_one'
  结论: b != 1
  证明: by linarith

@[simp]
-/
private theorem b_ne_one' : b != 1 := by linarith

@[simp]
/--
theorem `logb_le_logb` / 定理 `logb_le_logb`

English:
theorem logb_le_logb
  given: (h : 0 < x) (h₁ : 0 < y)
  statement: logb b x <= logb b y ↔ x <= y
  proof: by
  rw [logb]; rw [logb]; rw [div_le_div_iff_of_pos_right (log_pos hb)]; rw [log_le_log_iff h h₁]

@[gcongr]

中文:
定理 logb_le_logb
  条件: (h : 0 < x) (h₁ : 0 < y)
  结论: logb b x <= logb b y ↔ x <= y
  证明: by
  rw [logb]; rw [logb]; rw [div_le_div_iff_of_pos_right (log_pos hb)]; rw [log_le_log_iff h h₁]

@[gcongr]

Depends on / 依赖: div_le_div_iff_of_pos_right, log_le_log_iff, log_pos
-/
theorem logb_le_logb (h : 0 < x) (h₁ : 0 < y) : logb b x <= logb b y ↔ x <= y := by
  rw [logb]; rw [logb]; rw [div_le_div_iff_of_pos_right (log_pos hb)]; rw [log_le_log_iff h h₁]

@[gcongr]
/--
theorem `logb_le_logb_of_le` / 定理 `logb_le_logb_of_le`

English:
theorem logb_le_logb_of_le
  given: (h : 0 < x) (hxy : x <= y)
  statement: logb b x <= logb b y
  proof: (logb_le_logb hb h (by linarith)).mpr hxy

@[gcongr]

中文:
定理 logb_le_logb_of_le
  条件: (h : 0 < x) (hxy : x <= y)
  结论: logb b x <= logb b y
  证明: (logb_le_logb hb h (by linarith)).mpr hxy

@[gcongr]

Depends on / 依赖: F.obj, Functor, Functor.map_comp, IsCoreflexivePair, IsCoreflexivePair.mk, counit, counit.app, logb_le_logb, map_comp, otherMap
-/
theorem logb_le_logb_of_le (h : 0 < x) (hxy : x <= y) : logb b x <= logb b y :=
  (logb_le_logb hb h (by linarith)).mpr hxy

@[gcongr]
/--
theorem `logb_lt_logb` / 定理 `logb_lt_logb`

English:
theorem logb_lt_logb
  given: (hx : 0 < x) (hxy : x < y)
  statement: logb b x < logb b y
  proof: by
  rw [logb]; rw [logb]; rw [div_lt_div_iff_of_pos_right (log_pos hb)]
  exact log_lt_log hx hxy

@[simp]

中文:
定理 logb_lt_logb
  条件: (hx : 0 < x) (hxy : x < y)
  结论: logb b x < logb b y
  证明: by
  rw [logb]; rw [logb]; rw [div_lt_div_iff_of_pos_right (log_pos hb)]
  exact log_lt_log hx hxy

@[simp]

Depends on / 依赖: div_lt_div_iff_of_pos_right, log_lt_log, log_pos
-/
theorem logb_lt_logb (hx : 0 < x) (hxy : x < y) : logb b x < logb b y := by
  rw [logb]; rw [logb]; rw [div_lt_div_iff_of_pos_right (log_pos hb)]
  exact log_lt_log hx hxy

@[simp]
/--
theorem `logb_lt_logb_iff` / 定理 `logb_lt_logb_iff`

English:
theorem logb_lt_logb_iff
  given: (hx : 0 < x) (hy : 0 < y)
  statement: logb b x < logb b y ↔ x < y
  proof: by
  rw [logb]; rw [logb]; rw [div_lt_div_iff_of_pos_right (log_pos hb)]
  exact log_lt_log_iff hx hy

中文:
定理 logb_lt_logb_iff
  条件: (hx : 0 < x) (hy : 0 < y)
  结论: logb b x < logb b y ↔ x < y
  证明: by
  rw [logb]; rw [logb]; rw [div_lt_div_iff_of_pos_right (log_pos hb)]
  exact log_lt_log_iff hx hy

Depends on / 依赖: div_lt_div_iff_of_pos_right, log_lt_log_iff, log_pos
-/
theorem logb_lt_logb_iff (hx : 0 < x) (hy : 0 < y) : logb b x < logb b y ↔ x < y := by
  rw [logb]; rw [logb]; rw [div_lt_div_iff_of_pos_right (log_pos hb)]
  exact log_lt_log_iff hx hy

/--
theorem `logb_le_iff_le_rpow` / 定理 `logb_le_iff_le_rpow`

English:
theorem logb_le_iff_le_rpow
  given: (hx : 0 < x)
  statement: logb b x <= y ↔ x <= b ^ y
  proof: by
  rw [← rpow_le_rpow_left_iff hb]; rw [rpow_logb (b_pos hb) (b_ne_one' hb) hx]

中文:
定理 logb_le_iff_le_rpow
  条件: (hx : 0 < x)
  结论: logb b x <= y ↔ x <= b ^ y
  证明: by
  rw [← rpow_le_rpow_left_iff hb]; rw [rpow_logb (b_pos hb) (b_ne_one' hb) hx]

Depends on / 依赖: b_ne_one, b_pos, rpow_le_rpow_left_iff, rpow_logb
-/
theorem logb_le_iff_le_rpow (hx : 0 < x) : logb b x <= y ↔ x <= b ^ y := by
  rw [← rpow_le_rpow_left_iff hb]; rw [rpow_logb (b_pos hb) (b_ne_one' hb) hx]

/--
theorem `logb_lt_iff_lt_rpow` / 定理 `logb_lt_iff_lt_rpow`

English:
theorem logb_lt_iff_lt_rpow
  given: (hx : 0 < x)
  statement: logb b x < y ↔ x < b ^ y
  proof: by
  rw [← rpow_lt_rpow_left_iff hb]; rw [rpow_logb (b_pos hb) (b_ne_one' hb) hx]

中文:
定理 logb_lt_iff_lt_rpow
  条件: (hx : 0 < x)
  结论: logb b x < y ↔ x < b ^ y
  证明: by
  rw [← rpow_lt_rpow_left_iff hb]; rw [rpow_logb (b_pos hb) (b_ne_one' hb) hx]

Depends on / 依赖: b_ne_one, b_pos, rpow_logb, rpow_lt_rpow_left_iff
-/
theorem logb_lt_iff_lt_rpow (hx : 0 < x) : logb b x < y ↔ x < b ^ y := by
  rw [← rpow_lt_rpow_left_iff hb]; rw [rpow_logb (b_pos hb) (b_ne_one' hb) hx]

/--
theorem `le_logb_iff_rpow_le` / 定理 `le_logb_iff_rpow_le`

English:
theorem le_logb_iff_rpow_le
  given: (hy : 0 < y)
  statement: x <= logb b y ↔ b ^ x <= y
  proof: by
  rw [← rpow_le_rpow_left_iff hb]; rw [rpow_logb (b_pos hb) (b_ne_one' hb) hy]

中文:
定理 le_logb_iff_rpow_le
  条件: (hy : 0 < y)
  结论: x <= logb b y ↔ b ^ x <= y
  证明: by
  rw [← rpow_le_rpow_left_iff hb]; rw [rpow_logb (b_pos hb) (b_ne_one' hb) hy]

Depends on / 依赖: b_ne_one, b_pos, rpow_le_rpow_left_iff, rpow_logb
-/
theorem le_logb_iff_rpow_le (hy : 0 < y) : x <= logb b y ↔ b ^ x <= y := by
  rw [← rpow_le_rpow_left_iff hb]; rw [rpow_logb (b_pos hb) (b_ne_one' hb) hy]

/--
theorem `lt_logb_iff_rpow_lt` / 定理 `lt_logb_iff_rpow_lt`

English:
theorem lt_logb_iff_rpow_lt
  given: (hy : 0 < y)
  statement: x < logb b y ↔ b ^ x < y
  proof: by
  rw [← rpow_lt_rpow_left_iff hb]; rw [rpow_logb (b_pos hb) (b_ne_one' hb) hy]

中文:
定理 lt_logb_iff_rpow_lt
  条件: (hy : 0 < y)
  结论: x < logb b y ↔ b ^ x < y
  证明: by
  rw [← rpow_lt_rpow_left_iff hb]; rw [rpow_logb (b_pos hb) (b_ne_one' hb) hy]

Depends on / 依赖: b_ne_one, b_pos, rpow_logb, rpow_lt_rpow_left_iff
-/
theorem lt_logb_iff_rpow_lt (hy : 0 < y) : x < logb b y ↔ b ^ x < y := by
  rw [← rpow_lt_rpow_left_iff hb]; rw [rpow_logb (b_pos hb) (b_ne_one' hb) hy]

/--
theorem `logb_pos_iff` / 定理 `logb_pos_iff`

English:
theorem logb_pos_iff
  given: (hx : 0 < x)
  statement: 0 < logb b x ↔ 1 < x
  proof: by
  rw [← @logb_one b]
  rw [logb_lt_logb_iff hb zero_lt_one hx]

中文:
定理 logb_pos_iff
  条件: (hx : 0 < x)
  结论: 0 < logb b x ↔ 1 < x
  证明: by
  rw [← @logb_one b]
  rw [logb_lt_logb_iff hb zero_lt_one hx]

Depends on / 依赖: logb_lt_logb_iff, logb_one, zero_lt_one
-/
theorem logb_pos_iff (hx : 0 < x) : 0 < logb b x ↔ 1 < x := by
  rw [← @logb_one b]
  rw [logb_lt_logb_iff hb zero_lt_one hx]

/--
theorem `logb_pos` / 定理 `logb_pos`

English:
theorem logb_pos
  given: (hx : 1 < x)
  statement: 0 < logb b x
  proof: by
  rw [logb_pos_iff hb (lt_trans zero_lt_one hx)]
  exact hx

中文:
定理 logb_pos
  条件: (hx : 1 < x)
  结论: 0 < logb b x
  证明: by
  rw [logb_pos_iff hb (lt_trans zero_lt_one hx)]
  exact hx

Depends on / 依赖: logb_pos_iff, lt_trans, zero_lt_one
-/
theorem logb_pos (hx : 1 < x) : 0 < logb b x := by
  rw [logb_pos_iff hb (lt_trans zero_lt_one hx)]
  exact hx

/--
theorem `logb_neg_iff` / 定理 `logb_neg_iff`

English:
theorem logb_neg_iff
  given: (h : 0 < x)
  statement: logb b x < 0 ↔ x < 1
  proof: by
  rw [← logb_one]
  exact logb_lt_logb_iff hb h zero_lt_one

中文:
定理 logb_neg_iff
  条件: (h : 0 < x)
  结论: logb b x < 0 ↔ x < 1
  证明: by
  rw [← logb_one]
  exact logb_lt_logb_iff hb h zero_lt_one

Depends on / 依赖: logb_lt_logb_iff, logb_one, zero_lt_one
-/
theorem logb_neg_iff (h : 0 < x) : logb b x < 0 ↔ x < 1 := by
  rw [← logb_one]
  exact logb_lt_logb_iff hb h zero_lt_one

/--
theorem `logb_neg` / 定理 `logb_neg`

English:
theorem logb_neg
  given: (h0 : 0 < x) (h1 : x < 1)
  statement: logb b x < 0
  proof: (logb_neg_iff hb h0).2 h1

中文:
定理 logb_neg
  条件: (h0 : 0 < x) (h1 : x < 1)
  结论: logb b x < 0
  证明: (logb_neg_iff hb h0).2 h1

Depends on / 依赖: logb_neg_iff
-/
theorem logb_neg (h0 : 0 < x) (h1 : x < 1) : logb b x < 0 :=
  (logb_neg_iff hb h0).2 h1

/--
theorem `logb_nonneg_iff` / 定理 `logb_nonneg_iff`

English:
theorem logb_nonneg_iff
  given: (hx : 0 < x)
  statement: 0 <= logb b x ↔ 1 <= x
  proof: by
  rw [← not_lt]; rw [logb_neg_iff hb hx]; rw [not_lt]

中文:
定理 logb_nonneg_iff
  条件: (hx : 0 < x)
  结论: 0 <= logb b x ↔ 1 <= x
  证明: by
  rw [← not_lt]; rw [logb_neg_iff hb hx]; rw [not_lt]

Depends on / 依赖: logb_neg_iff, not_lt
-/
theorem logb_nonneg_iff (hx : 0 < x) : 0 <= logb b x ↔ 1 <= x := by
  rw [← not_lt]; rw [logb_neg_iff hb hx]; rw [not_lt]

/--
theorem `logb_nonneg` / 定理 `logb_nonneg`

English:
theorem logb_nonneg
  given: (hx : 1 <= x)
  statement: 0 <= logb b x
  proof: (logb_nonneg_iff hb (zero_lt_one.trans_le hx)).2 hx

中文:
定理 logb_nonneg
  条件: (hx : 1 <= x)
  结论: 0 <= logb b x
  证明: (logb_nonneg_iff hb (zero_lt_one.trans_le hx)).2 hx

Depends on / 依赖: logb_nonneg_iff, trans_le, zero_lt_one, zero_lt_one.trans_le
-/
theorem logb_nonneg (hx : 1 <= x) : 0 <= logb b x :=
  (logb_nonneg_iff hb (zero_lt_one.trans_le hx)).2 hx

/--
theorem `logb_nonpos_iff` / 定理 `logb_nonpos_iff`

English:
theorem logb_nonpos_iff
  given: (hx : 0 < x)
  statement: logb b x <= 0 ↔ x <= 1
  proof: by
  rw [← not_lt]; rw [logb_pos_iff hb hx]; rw [not_lt]

中文:
定理 logb_nonpos_iff
  条件: (hx : 0 < x)
  结论: logb b x <= 0 ↔ x <= 1
  证明: by
  rw [← not_lt]; rw [logb_pos_iff hb hx]; rw [not_lt]

Depends on / 依赖: logb_pos_iff, not_lt
-/
theorem logb_nonpos_iff (hx : 0 < x) : logb b x <= 0 ↔ x <= 1 := by
  rw [← not_lt]; rw [logb_pos_iff hb hx]; rw [not_lt]

/--
theorem `logb_nonpos_iff'` / 定理 `logb_nonpos_iff'`

English:
theorem logb_nonpos_iff'
  given: (hx : 0 <= x)
  statement: logb b x <= 0 ↔ x <= 1
  proof: by
  rcases hx.eq_or_lt with (rfl | hx)
  · simp [zero_le_one]
  exact logb_nonpos_iff hb hx

中文:
定理 logb_nonpos_iff'
  条件: (hx : 0 <= x)
  结论: logb b x <= 0 ↔ x <= 1
  证明: by
  rcases hx.eq_or_lt with (rfl | hx)
  · simp [zero_le_one]
  exact logb_nonpos_iff hb hx

Depends on / 依赖: eq_or_lt, hx.eq_or_lt, logb_nonpos_iff, zero_le_one
-/
theorem logb_nonpos_iff' (hx : 0 <= x) : logb b x <= 0 ↔ x <= 1 := by
  rcases hx.eq_or_lt with (rfl | hx)
  · simp [zero_le_one]
  exact logb_nonpos_iff hb hx

/--
theorem `logb_nonpos` / 定理 `logb_nonpos`

English:
theorem logb_nonpos
  given: (hx : 0 <= x) (h'x : x <= 1)
  statement: logb b x <= 0
  proof: (logb_nonpos_iff' hb hx).2 h'x

中文:
定理 logb_nonpos
  条件: (hx : 0 <= x) (h'x : x <= 1)
  结论: logb b x <= 0
  证明: (logb_nonpos_iff' hb hx).2 h'x

Depends on / 依赖: logb_nonpos_iff
-/
theorem logb_nonpos (hx : 0 <= x) (h'x : x <= 1) : logb b x <= 0 :=
  (logb_nonpos_iff' hb hx).2 h'x

/--
theorem `strictMonoOn_logb` / 定理 `strictMonoOn_logb`

English:
theorem strictMonoOn_logb
  statement: StrictMonoOn (logb b) (Set.Ioi 0)
  proof: fun _ hx _ _ hxy =>
  logb_lt_logb hb hx hxy

中文:
定理 strictMonoOn_logb
  结论: StrictMonoOn (logb b) (集合.左开右无界区间 0)
  证明: fun _ hx _ _ hxy =>
  logb_lt_logb hb hx hxy
-/
theorem strictMonoOn_logb : StrictMonoOn (logb b) (Set.Ioi 0) := fun _ hx _ _ hxy =>
  logb_lt_logb hb hx hxy

/--
theorem `strictAntiOn_logb` / 定理 `strictAntiOn_logb`

English:
theorem strictAntiOn_logb
  statement: StrictAntiOn (logb b) (Set.Iio 0)
  proof: by
  rintro x (hx : x < 0) y (hy : y < 0) hxy
  rw [← logb_abs b y]; rw [← logb_abs b x]
  refine logb_lt_logb hb (abs_pos.2 hy.ne) ?_
  rwa [abs_of_neg hy, abs_of_neg hx, neg_lt_neg_iff]

中文:
定理 strictAntiOn_logb
  结论: StrictAntiOn (logb b) (集合.左无界右开区间 0)
  证明: by
  rintro x (hx : x < 0) y (hy : y < 0) hxy
  rw [← logb_abs b y]; rw [← logb_abs b x]
  refine logb_lt_logb hb (abs_pos.2 hy.ne) ?_
  rwa [abs_of_neg hy, abs_of_neg hx, neg_lt_neg_iff]

Depends on / 依赖: abs_of_neg, abs_pos, hy.ne, logb_abs, logb_lt_logb, neg_lt_neg_iff
-/
theorem strictAntiOn_logb : StrictAntiOn (logb b) (Set.Iio 0) := by
  rintro x (hx : x < 0) y (hy : y < 0) hxy
  rw [← logb_abs b y]; rw [← logb_abs b x]
  refine logb_lt_logb hb (abs_pos.2 hy.ne) ?_
  rwa [abs_of_neg hy, abs_of_neg hx, neg_lt_neg_iff]

/--
theorem `logb_injOn_pos` / 定理 `logb_injOn_pos`

English:
theorem logb_injOn_pos
  statement: Set.InjOn (logb b) (Set.Ioi 0)
  proof: (strictMonoOn_logb hb).injOn

中文:
定理 logb_injOn_pos
  结论: 集合.单射限制 (logb b) (集合.左开右无界区间 0)
  证明: (strictMonoOn_logb hb).injOn

Depends on / 依赖: strictMonoOn_logb
-/
theorem logb_injOn_pos : Set.InjOn (logb b) (Set.Ioi 0) :=
  (strictMonoOn_logb hb).injOn

/--
theorem `eq_one_of_pos_of_logb_eq_zero` / 定理 `eq_one_of_pos_of_logb_eq_zero`

English:
theorem eq_one_of_pos_of_logb_eq_zero
  given: (h₁ : 0 < x) (h₂ : logb b x = 0)
  statement: x = 1
  proof: logb_injOn_pos hb (Set.mem_Ioi.2 h₁) (Set.mem_Ioi.2 zero_lt_one) (h₂.trans Real.logb_one.symm)

中文:
定理 eq_one_of_pos_of_logb_eq_zero
  条件: (h₁ : 0 < x) (h₂ : logb b x = 0)
  结论: x = 1
  证明: logb_injOn_pos hb (Set.mem_Ioi.2 h₁) (Set.mem_Ioi.2 zero_lt_one) (h₂.trans Real.logb_one.symm)

Depends on / 依赖: Real.logb_one.symm, Set.mem_Ioi, logb_injOn_pos, logb_one, mem_Ioi, zero_lt_one
-/
theorem eq_one_of_pos_of_logb_eq_zero (h₁ : 0 < x) (h₂ : logb b x = 0) : x = 1 :=
  logb_injOn_pos hb (Set.mem_Ioi.2 h₁) (Set.mem_Ioi.2 zero_lt_one) (h₂.trans Real.logb_one.symm)

/--
theorem `logb_ne_zero_of_pos_of_ne_one` / 定理 `logb_ne_zero_of_pos_of_ne_one`

English:
theorem logb_ne_zero_of_pos_of_ne_one
  given: (hx_pos : 0 < x) (hx : x != 1)
  statement: logb b x != 0
  proof: mt (eq_one_of_pos_of_logb_eq_zero hb hx_pos) hx

中文:
定理 logb_ne_zero_of_pos_of_ne_one
  条件: (hx_pos : 0 < x) (hx : x != 1)
  结论: logb b x != 0
  证明: mt (eq_one_of_pos_of_logb_eq_zero hb hx_pos) hx

Depends on / 依赖: eq_one_of_pos_of_logb_eq_zero, hx_pos
-/
theorem logb_ne_zero_of_pos_of_ne_one (hx_pos : 0 < x) (hx : x != 1) : logb b x != 0 :=
  mt (eq_one_of_pos_of_logb_eq_zero hb hx_pos) hx

/--
theorem `tendsto_logb_atTop` / 定理 `tendsto_logb_atTop`

English:
theorem tendsto_logb_atTop
  statement: Tendsto (logb b) atTop atTop
  proof: Tendsto.atTop_div_const (log_pos hb) tendsto_log_atTop

中文:
定理 tendsto_logb_atTop
  结论: 收敛 (logb b) atTop atTop
  证明: Tendsto.atTop_div_const (log_pos hb) tendsto_log_atTop

Depends on / 依赖: Tendsto, Tendsto.atTop_div_const, atTop_div_const, log_pos, tendsto_log_atTop
-/
theorem tendsto_logb_atTop : Tendsto (logb b) atTop atTop :=
  Tendsto.atTop_div_const (log_pos hb) tendsto_log_atTop

end OneLtB

section BPosAndBLtOne

variable (b_pos : 0 < b) (b_lt_one : b < 1)
include b_lt_one

/--
theorem `b_ne_one` / 定理 `b_ne_one`

English:
theorem b_ne_one
  statement: b != 1
  proof: by linarith

include b_pos

@[simp]

中文:
定理 b_ne_one
  结论: b != 1
  证明: by linarith

include b_pos

@[simp]
-/
private theorem b_ne_one : b != 1 := by linarith

include b_pos

@[simp]
/--
theorem `logb_le_logb_of_base_lt_one` / 定理 `logb_le_logb_of_base_lt_one`

English:
theorem logb_le_logb_of_base_lt_one
  given: (h : 0 < x) (h₁ : 0 < y)
  statement: logb b x <= logb b y ↔ y <= x
  proof: by
  rw [logb]; rw [logb]; rw [div_le_div_right_of_neg (log_neg b_pos b_lt_one)]; rw [log_le_log_iff h₁ h]

中文:
定理 logb_le_logb_of_base_lt_one
  条件: (h : 0 < x) (h₁ : 0 < y)
  结论: logb b x <= logb b y ↔ y <= x
  证明: by
  rw [logb]; rw [logb]; rw [div_le_div_right_of_neg (log_neg b_pos b_lt_one)]; rw [log_le_log_iff h₁ h]

Depends on / 依赖: b_lt_one, b_pos, div_le_div_right_of_neg, log_le_log_iff, log_neg
-/
theorem logb_le_logb_of_base_lt_one (h : 0 < x) (h₁ : 0 < y) : logb b x <= logb b y ↔ y <= x := by
  rw [logb]; rw [logb]; rw [div_le_div_right_of_neg (log_neg b_pos b_lt_one)]; rw [log_le_log_iff h₁ h]

/--
theorem `logb_lt_logb_of_base_lt_one` / 定理 `logb_lt_logb_of_base_lt_one`

English:
theorem logb_lt_logb_of_base_lt_one
  given: (hx : 0 < x) (hxy : x < y)
  statement: logb b y < logb b x
  proof: by
  rw [logb]; rw [logb]; rw [div_lt_div_right_of_neg (log_neg b_pos b_lt_one)]
  exact log_lt_log hx hxy

@[simp]

中文:
定理 logb_lt_logb_of_base_lt_one
  条件: (hx : 0 < x) (hxy : x < y)
  结论: logb b y < logb b x
  证明: by
  rw [logb]; rw [logb]; rw [div_lt_div_right_of_neg (log_neg b_pos b_lt_one)]
  exact log_lt_log hx hxy

@[simp]

Depends on / 依赖: b_lt_one, b_pos, div_lt_div_right_of_neg, log_lt_log, log_neg
-/
theorem logb_lt_logb_of_base_lt_one (hx : 0 < x) (hxy : x < y) : logb b y < logb b x := by
  rw [logb]; rw [logb]; rw [div_lt_div_right_of_neg (log_neg b_pos b_lt_one)]
  exact log_lt_log hx hxy

@[simp]
/--
theorem `logb_lt_logb_iff_of_base_lt_one` / 定理 `logb_lt_logb_iff_of_base_lt_one`

English:
theorem logb_lt_logb_iff_of_base_lt_one
  given: (hx : 0 < x) (hy : 0 < y)
  proof: by
  rw [logb]; rw [logb]; rw [div_lt_div_right_of_neg (log_neg b_pos b_lt_one)]
  exact log_lt_log_iff hy hx

中文:
定理 logb_lt_logb_iff_of_base_lt_one
  条件: (hx : 0 < x) (hy : 0 < y)
  证明: by
  rw [logb]; rw [logb]; rw [div_lt_div_right_of_neg (log_neg b_pos b_lt_one)]
  exact log_lt_log_iff hy hx

Depends on / 依赖: b_lt_one, b_pos, div_lt_div_right_of_neg, log_lt_log_iff, log_neg
-/
theorem logb_lt_logb_iff_of_base_lt_one (hx : 0 < x) (hy : 0 < y) :
    logb b x < logb b y ↔ y < x := by
  rw [logb]; rw [logb]; rw [div_lt_div_right_of_neg (log_neg b_pos b_lt_one)]
  exact log_lt_log_iff hy hx

/--
theorem `logb_le_iff_le_rpow_of_base_lt_one` / 定理 `logb_le_iff_le_rpow_of_base_lt_one`

English:
theorem logb_le_iff_le_rpow_of_base_lt_one
  given: (hx : 0 < x)
  statement: logb b x <= y ↔ b ^ y <= x
  proof: by
  rw [← rpow_le_rpow_left_iff_of_base_lt_one b_pos b_lt_one]; rw [rpow_logb b_pos (b_ne_one b_lt_one) hx]

中文:
定理 logb_le_iff_le_rpow_of_base_lt_one
  条件: (hx : 0 < x)
  结论: logb b x <= y ↔ b ^ y <= x
  证明: by
  rw [← rpow_le_rpow_left_iff_of_base_lt_one b_pos b_lt_one]; rw [rpow_logb b_pos (b_ne_one b_lt_one) hx]

Depends on / 依赖: b_lt_one, b_ne_one, b_pos, rpow_le_rpow_left_iff_of_base_lt_one, rpow_logb
-/
theorem logb_le_iff_le_rpow_of_base_lt_one (hx : 0 < x) : logb b x <= y ↔ b ^ y <= x := by
  rw [← rpow_le_rpow_left_iff_of_base_lt_one b_pos b_lt_one]; rw [rpow_logb b_pos (b_ne_one b_lt_one) hx]

/--
theorem `logb_lt_iff_lt_rpow_of_base_lt_one` / 定理 `logb_lt_iff_lt_rpow_of_base_lt_one`

English:
theorem logb_lt_iff_lt_rpow_of_base_lt_one
  given: (hx : 0 < x)
  statement: logb b x < y ↔ b ^ y < x
  proof: by
  rw [← rpow_lt_rpow_left_iff_of_base_lt_one b_pos b_lt_one]; rw [rpow_logb b_pos (b_ne_one b_lt_one) hx]

中文:
定理 logb_lt_iff_lt_rpow_of_base_lt_one
  条件: (hx : 0 < x)
  结论: logb b x < y ↔ b ^ y < x
  证明: by
  rw [← rpow_lt_rpow_left_iff_of_base_lt_one b_pos b_lt_one]; rw [rpow_logb b_pos (b_ne_one b_lt_one) hx]

Depends on / 依赖: b_lt_one, b_ne_one, b_pos, rpow_logb, rpow_lt_rpow_left_iff_of_base_lt_one
-/
theorem logb_lt_iff_lt_rpow_of_base_lt_one (hx : 0 < x) : logb b x < y ↔ b ^ y < x := by
  rw [← rpow_lt_rpow_left_iff_of_base_lt_one b_pos b_lt_one]; rw [rpow_logb b_pos (b_ne_one b_lt_one) hx]

/--
theorem `le_logb_iff_rpow_le_of_base_lt_one` / 定理 `le_logb_iff_rpow_le_of_base_lt_one`

English:
theorem le_logb_iff_rpow_le_of_base_lt_one
  given: (hy : 0 < y)
  statement: x <= logb b y ↔ y <= b ^ x
  proof: by
  rw [← rpow_le_rpow_left_iff_of_base_lt_one b_pos b_lt_one]; rw [rpow_logb b_pos (b_ne_one b_lt_one) hy]

中文:
定理 le_logb_iff_rpow_le_of_base_lt_one
  条件: (hy : 0 < y)
  结论: x <= logb b y ↔ y <= b ^ x
  证明: by
  rw [← rpow_le_rpow_left_iff_of_base_lt_one b_pos b_lt_one]; rw [rpow_logb b_pos (b_ne_one b_lt_one) hy]

Depends on / 依赖: b_lt_one, b_ne_one, b_pos, rpow_le_rpow_left_iff_of_base_lt_one, rpow_logb
-/
theorem le_logb_iff_rpow_le_of_base_lt_one (hy : 0 < y) : x <= logb b y ↔ y <= b ^ x := by
  rw [← rpow_le_rpow_left_iff_of_base_lt_one b_pos b_lt_one]; rw [rpow_logb b_pos (b_ne_one b_lt_one) hy]

/--
theorem `lt_logb_iff_rpow_lt_of_base_lt_one` / 定理 `lt_logb_iff_rpow_lt_of_base_lt_one`

English:
theorem lt_logb_iff_rpow_lt_of_base_lt_one
  given: (hy : 0 < y)
  statement: x < logb b y ↔ y < b ^ x
  proof: by
  rw [← rpow_lt_rpow_left_iff_of_base_lt_one b_pos b_lt_one]; rw [rpow_logb b_pos (b_ne_one b_lt_one) hy]

中文:
定理 lt_logb_iff_rpow_lt_of_base_lt_one
  条件: (hy : 0 < y)
  结论: x < logb b y ↔ y < b ^ x
  证明: by
  rw [← rpow_lt_rpow_left_iff_of_base_lt_one b_pos b_lt_one]; rw [rpow_logb b_pos (b_ne_one b_lt_one) hy]

Depends on / 依赖: b_lt_one, b_ne_one, b_pos, rpow_logb, rpow_lt_rpow_left_iff_of_base_lt_one
-/
theorem lt_logb_iff_rpow_lt_of_base_lt_one (hy : 0 < y) : x < logb b y ↔ y < b ^ x := by
  rw [← rpow_lt_rpow_left_iff_of_base_lt_one b_pos b_lt_one]; rw [rpow_logb b_pos (b_ne_one b_lt_one) hy]

/--
theorem `logb_pos_iff_of_base_lt_one` / 定理 `logb_pos_iff_of_base_lt_one`

English:
theorem logb_pos_iff_of_base_lt_one
  given: (hx : 0 < x)
  statement: 0 < logb b x ↔ x < 1
  proof: by
  rw [← @logb_one b]; rw [logb_lt_logb_iff_of_base_lt_one b_pos b_lt_one zero_lt_one hx]

中文:
定理 logb_pos_iff_of_base_lt_one
  条件: (hx : 0 < x)
  结论: 0 < logb b x ↔ x < 1
  证明: by
  rw [← @logb_one b]; rw [logb_lt_logb_iff_of_base_lt_one b_pos b_lt_one zero_lt_one hx]

Depends on / 依赖: b_lt_one, b_pos, logb_lt_logb_iff_of_base_lt_one, logb_one, zero_lt_one
-/
theorem logb_pos_iff_of_base_lt_one (hx : 0 < x) : 0 < logb b x ↔ x < 1 := by
  rw [← @logb_one b]; rw [logb_lt_logb_iff_of_base_lt_one b_pos b_lt_one zero_lt_one hx]

/--
theorem `logb_pos_of_base_lt_one` / 定理 `logb_pos_of_base_lt_one`

English:
theorem logb_pos_of_base_lt_one
  given: (hx : 0 < x) (hx' : x < 1)
  statement: 0 < logb b x
  proof: by
  rw [logb_pos_iff_of_base_lt_one b_pos b_lt_one hx]
  exact hx'

中文:
定理 logb_pos_of_base_lt_one
  条件: (hx : 0 < x) (hx' : x < 1)
  结论: 0 < logb b x
  证明: by
  rw [logb_pos_iff_of_base_lt_one b_pos b_lt_one hx]
  exact hx'

Depends on / 依赖: b_lt_one, b_pos, logb_pos_iff_of_base_lt_one
-/
theorem logb_pos_of_base_lt_one (hx : 0 < x) (hx' : x < 1) : 0 < logb b x := by
  rw [logb_pos_iff_of_base_lt_one b_pos b_lt_one hx]
  exact hx'

/--
theorem `logb_neg_iff_of_base_lt_one` / 定理 `logb_neg_iff_of_base_lt_one`

English:
theorem logb_neg_iff_of_base_lt_one
  given: (h : 0 < x)
  statement: logb b x < 0 ↔ 1 < x
  proof: by
  rw [← @logb_one b]; rw [logb_lt_logb_iff_of_base_lt_one b_pos b_lt_one h zero_lt_one]

中文:
定理 logb_neg_iff_of_base_lt_one
  条件: (h : 0 < x)
  结论: logb b x < 0 ↔ 1 < x
  证明: by
  rw [← @logb_one b]; rw [logb_lt_logb_iff_of_base_lt_one b_pos b_lt_one h zero_lt_one]

Depends on / 依赖: b_lt_one, b_pos, logb_lt_logb_iff_of_base_lt_one, logb_one, zero_lt_one
-/
theorem logb_neg_iff_of_base_lt_one (h : 0 < x) : logb b x < 0 ↔ 1 < x := by
  rw [← @logb_one b]; rw [logb_lt_logb_iff_of_base_lt_one b_pos b_lt_one h zero_lt_one]

/--
theorem `logb_neg_of_base_lt_one` / 定理 `logb_neg_of_base_lt_one`

English:
theorem logb_neg_of_base_lt_one
  given: (h1 : 1 < x)
  statement: logb b x < 0
  proof: (logb_neg_iff_of_base_lt_one b_pos b_lt_one (lt_trans zero_lt_one h1)).2 h1

中文:
定理 logb_neg_of_base_lt_one
  条件: (h1 : 1 < x)
  结论: logb b x < 0
  证明: (logb_neg_iff_of_base_lt_one b_pos b_lt_one (lt_trans zero_lt_one h1)).2 h1

Depends on / 依赖: b_lt_one, b_pos, logb_neg_iff_of_base_lt_one, lt_trans, zero_lt_one
-/
theorem logb_neg_of_base_lt_one (h1 : 1 < x) : logb b x < 0 :=
  (logb_neg_iff_of_base_lt_one b_pos b_lt_one (lt_trans zero_lt_one h1)).2 h1

/--
theorem `logb_nonneg_iff_of_base_lt_one` / 定理 `logb_nonneg_iff_of_base_lt_one`

English:
theorem logb_nonneg_iff_of_base_lt_one
  given: (hx : 0 < x)
  statement: 0 <= logb b x ↔ x <= 1
  proof: by
  rw [← not_lt]; rw [logb_neg_iff_of_base_lt_one b_pos b_lt_one hx]; rw [not_lt]

中文:
定理 logb_nonneg_iff_of_base_lt_one
  条件: (hx : 0 < x)
  结论: 0 <= logb b x ↔ x <= 1
  证明: by
  rw [← not_lt]; rw [logb_neg_iff_of_base_lt_one b_pos b_lt_one hx]; rw [not_lt]

Depends on / 依赖: b_lt_one, b_pos, logb_neg_iff_of_base_lt_one, not_lt
-/
theorem logb_nonneg_iff_of_base_lt_one (hx : 0 < x) : 0 <= logb b x ↔ x <= 1 := by
  rw [← not_lt]; rw [logb_neg_iff_of_base_lt_one b_pos b_lt_one hx]; rw [not_lt]

/--
theorem `logb_nonneg_of_base_lt_one` / 定理 `logb_nonneg_of_base_lt_one`

English:
theorem logb_nonneg_of_base_lt_one
  given: (hx : 0 < x) (hx' : x <= 1)
  statement: 0 <= logb b x
  proof: by
  rw [logb_nonneg_iff_of_base_lt_one b_pos b_lt_one hx]
  exact hx'

中文:
定理 logb_nonneg_of_base_lt_one
  条件: (hx : 0 < x) (hx' : x <= 1)
  结论: 0 <= logb b x
  证明: by
  rw [logb_nonneg_iff_of_base_lt_one b_pos b_lt_one hx]
  exact hx'

Depends on / 依赖: b_lt_one, b_pos, logb_nonneg_iff_of_base_lt_one
-/
theorem logb_nonneg_of_base_lt_one (hx : 0 < x) (hx' : x <= 1) : 0 <= logb b x := by
  rw [logb_nonneg_iff_of_base_lt_one b_pos b_lt_one hx]
  exact hx'

/--
theorem `logb_nonpos_iff_of_base_lt_one` / 定理 `logb_nonpos_iff_of_base_lt_one`

English:
theorem logb_nonpos_iff_of_base_lt_one
  given: (hx : 0 < x)
  statement: logb b x <= 0 ↔ 1 <= x
  proof: by
  rw [← not_lt]; rw [logb_pos_iff_of_base_lt_one b_pos b_lt_one hx]; rw [not_lt]

中文:
定理 logb_nonpos_iff_of_base_lt_one
  条件: (hx : 0 < x)
  结论: logb b x <= 0 ↔ 1 <= x
  证明: by
  rw [← not_lt]; rw [logb_pos_iff_of_base_lt_one b_pos b_lt_one hx]; rw [not_lt]

Depends on / 依赖: b_lt_one, b_pos, logb_pos_iff_of_base_lt_one, not_lt
-/
theorem logb_nonpos_iff_of_base_lt_one (hx : 0 < x) : logb b x <= 0 ↔ 1 <= x := by
  rw [← not_lt]; rw [logb_pos_iff_of_base_lt_one b_pos b_lt_one hx]; rw [not_lt]

/--
theorem `strictAntiOn_logb_of_base_lt_one` / 定理 `strictAntiOn_logb_of_base_lt_one`

English:
theorem strictAntiOn_logb_of_base_lt_one
  statement: StrictAntiOn (logb b) (Set.Ioi 0)
  proof: fun _ hx _ _ hxy =>
  logb_lt_logb_of_base_lt_one b_pos b_lt_one hx hxy

中文:
定理 strictAntiOn_logb_of_base_lt_one
  结论: StrictAntiOn (logb b) (集合.左开右无界区间 0)
  证明: fun _ hx _ _ hxy =>
  logb_lt_logb_of_base_lt_one b_pos b_lt_one hx hxy
-/
theorem strictAntiOn_logb_of_base_lt_one : StrictAntiOn (logb b) (Set.Ioi 0) := fun _ hx _ _ hxy =>
  logb_lt_logb_of_base_lt_one b_pos b_lt_one hx hxy

/--
theorem `strictMonoOn_logb_of_base_lt_one` / 定理 `strictMonoOn_logb_of_base_lt_one`

English:
theorem strictMonoOn_logb_of_base_lt_one
  statement: StrictMonoOn (logb b) (Set.Iio 0)
  proof: by
  rintro x (hx : x < 0) y (hy : y < 0) hxy
  rw [← logb_abs b y]; rw [← logb_abs b x]
  refine logb_lt_logb_of_base_lt_one b_pos b_lt_one (abs_pos.2 hy.ne) ?_
  rwa [abs_of_neg hy, abs_of_neg hx, neg_lt_neg_iff]

中文:
定理 strictMonoOn_logb_of_base_lt_one
  结论: StrictMonoOn (logb b) (集合.左无界右开区间 0)
  证明: by
  rintro x (hx : x < 0) y (hy : y < 0) hxy
  rw [← logb_abs b y]; rw [← logb_abs b x]
  refine logb_lt_logb_of_base_lt_one b_pos b_lt_one (abs_pos.2 hy.ne) ?_
  rwa [abs_of_neg hy, abs_of_neg hx, neg_lt_neg_iff]

Depends on / 依赖: abs_of_neg, abs_pos, b_lt_one, b_pos, hy.ne, logb_abs, logb_lt_logb_of_base_lt_one, neg_lt_neg_iff
-/
theorem strictMonoOn_logb_of_base_lt_one : StrictMonoOn (logb b) (Set.Iio 0) := by
  rintro x (hx : x < 0) y (hy : y < 0) hxy
  rw [← logb_abs b y]; rw [← logb_abs b x]
  refine logb_lt_logb_of_base_lt_one b_pos b_lt_one (abs_pos.2 hy.ne) ?_
  rwa [abs_of_neg hy, abs_of_neg hx, neg_lt_neg_iff]

/--
theorem `logb_injOn_pos_of_base_lt_one` / 定理 `logb_injOn_pos_of_base_lt_one`

English:
theorem logb_injOn_pos_of_base_lt_one
  statement: Set.InjOn (logb b) (Set.Ioi 0)
  proof: (strictAntiOn_logb_of_base_lt_one b_pos b_lt_one).injOn

中文:
定理 logb_injOn_pos_of_base_lt_one
  结论: 集合.单射限制 (logb b) (集合.左开右无界区间 0)
  证明: (strictAntiOn_logb_of_base_lt_one b_pos b_lt_one).injOn

Depends on / 依赖: b_lt_one, b_pos, strictAntiOn_logb_of_base_lt_one
-/
theorem logb_injOn_pos_of_base_lt_one : Set.InjOn (logb b) (Set.Ioi 0) :=
  (strictAntiOn_logb_of_base_lt_one b_pos b_lt_one).injOn

/--
theorem `eq_one_of_pos_of_logb_eq_zero_of_base_lt_one` / 定理 `eq_one_of_pos_of_logb_eq_zero_of_base_lt_one`

English:
theorem eq_one_of_pos_of_logb_eq_zero_of_base_lt_one
  given: (h₁ : 0 < x) (h₂ : logb b x = 0)
  statement: x = 1
  proof: logb_injOn_pos_of_base_lt_one b_pos b_lt_one (Set.mem_Ioi.2 h₁) (Set.mem_Ioi.2 zero_lt_one)
    (h₂.trans Real.logb_one.symm)

中文:
定理 eq_one_of_pos_of_logb_eq_zero_of_base_lt_one
  条件: (h₁ : 0 < x) (h₂ : logb b x = 0)
  结论: x = 1
  证明: logb_injOn_pos_of_base_lt_one b_pos b_lt_one (Set.mem_Ioi.2 h₁) (Set.mem_Ioi.2 zero_lt_one)
    (h₂.trans Real.logb_one.symm)

Depends on / 依赖: Real.logb_one.symm, Set.mem_Ioi, b_lt_one, b_pos, logb_injOn_pos_of_base_lt_one, logb_one, mem_Ioi, zero_lt_one
-/
theorem eq_one_of_pos_of_logb_eq_zero_of_base_lt_one (h₁ : 0 < x) (h₂ : logb b x = 0) : x = 1 :=
  logb_injOn_pos_of_base_lt_one b_pos b_lt_one (Set.mem_Ioi.2 h₁) (Set.mem_Ioi.2 zero_lt_one)
    (h₂.trans Real.logb_one.symm)

/--
theorem `logb_ne_zero_of_pos_of_ne_one_of_base_lt_one` / 定理 `logb_ne_zero_of_pos_of_ne_one_of_base_lt_one`

English:
theorem logb_ne_zero_of_pos_of_ne_one_of_base_lt_one
  given: (hx_pos : 0 < x) (hx : x != 1)
  statement: logb b x != 0
  proof: mt (eq_one_of_pos_of_logb_eq_zero_of_base_lt_one b_pos b_lt_one hx_pos) hx

中文:
定理 logb_ne_zero_of_pos_of_ne_one_of_base_lt_one
  条件: (hx_pos : 0 < x) (hx : x != 1)
  结论: logb b x != 0
  证明: mt (eq_one_of_pos_of_logb_eq_zero_of_base_lt_one b_pos b_lt_one hx_pos) hx

Depends on / 依赖: b_lt_one, b_pos, eq_one_of_pos_of_logb_eq_zero_of_base_lt_one, hx_pos
-/
theorem logb_ne_zero_of_pos_of_ne_one_of_base_lt_one (hx_pos : 0 < x) (hx : x != 1) : logb b x != 0 :=
  mt (eq_one_of_pos_of_logb_eq_zero_of_base_lt_one b_pos b_lt_one hx_pos) hx

/--
theorem `tendsto_logb_atTop_of_base_lt_one` / 定理 `tendsto_logb_atTop_of_base_lt_one`

English:
theorem tendsto_logb_atTop_of_base_lt_one
  statement: Tendsto (logb b) atTop atBot
  proof: by
  rw [tendsto_atTop_atBot]
  intro e
  use 1 ⊔ b ^ e
  intro a
  simp only [and_imp, sup_le_iff]
  intro ha
  rw [logb_le_iff_le_rpow_of_base_lt_one b_pos b_lt_one]
  · tauto
  · exact lt_of_lt_of_le zero_lt_one ha

中文:
定理 tendsto_logb_atTop_of_base_lt_one
  结论: 收敛 (logb b) atTop atBot
  证明: by
  rw [tendsto_atTop_atBot]
  intro e
  use 1 ⊔ b ^ e
  intro a
  simp only [and_imp, sup_le_iff]
  intro ha
  rw [logb_le_iff_le_rpow_of_base_lt_one b_pos b_lt_one]
  · tauto
  · exact lt_of_lt_of_le zero_lt_one ha

Depends on / 依赖: and_imp, b_lt_one, b_pos, logb_le_iff_le_rpow_of_base_lt_one, lt_of_lt_of_le, sup_le_iff, tendsto_atTop_atBot, zero_lt_one
-/
theorem tendsto_logb_atTop_of_base_lt_one : Tendsto (logb b) atTop atBot := by
  rw [tendsto_atTop_atBot]
  intro e
  use 1 ⊔ b ^ e
  intro a
  simp only [and_imp, sup_le_iff]
  intro ha
  rw [logb_le_iff_le_rpow_of_base_lt_one b_pos b_lt_one]
  · tauto
  · exact lt_of_lt_of_le zero_lt_one ha

end BPosAndBLtOne

@[norm_cast]
/--
theorem `floor_logb_natCast` / 定理 `floor_logb_natCast`

English:
theorem floor_logb_natCast
  given: {b : Nat} {r : Real} (hr : 0 <= r)
  proof: by
  obtain rfl | hr := hr.eq_or_lt
  · rw [logb_zero, Int.log_zero_right, Int.floor_zero]
  by_cases hb : 1 < b
  · have hb1' : 1 < (b : Real) := Nat.one_lt_cast.mpr hb
    apply le_antisymm
    · rw [← Int.zpow_le_iff_le_log hb hr, ← rpow_intCast b]
      refine le_of_le_of_eq ?_ (rpow_logb (zero_

中文:
定理 floor_logb_natCast
  条件: {b : 自然数} {r : 实数} (hr : 0 <= r)
  证明: by
  obtain rfl | hr := hr.eq_or_lt
  · rw [logb_zero, Int.log_zero_right, Int.floor_zero]
  by_cases hb : 1 < b
  · have hb1' : 1 < (b : Real) := Nat.one_lt_cast.mpr hb
    apply le_antisymm
    · rw [← Int.zpow_le_iff_le_log hb hr, ← rpow_intCast b]
      refine le_of_le_of_eq ?_ (rpow_logb (zero_

Depends on / 依赖: Int.floor_le, Int.floor_zero, Int.le_floor, Int.log_zero_right, Int.zpow_le_iff_le_log, Int.zpow_log_le_self, Nat.one_lt_cast.mpr, Nat.one_lt_iff_ne_zero_and_ne, eq_or_lt, floor_le, floor_zero, hr.eq_or_lt, le_antisymm, le_floor, le_logb_iff_rpow_le, le_of_le_of_eq, log_zero_right, logb_zero, one_lt_cast, one_lt_iff_ne_zero_and_ne
-/
theorem floor_logb_natCast {b : Nat} {r : Real} (hr : 0 <= r) :
    ⌊logb b r⌋ = Int.log b r := by
  obtain rfl | hr := hr.eq_or_lt
  · rw [logb_zero, Int.log_zero_right, Int.floor_zero]
  by_cases hb : 1 < b
  · have hb1' : 1 < (b : Real) := Nat.one_lt_cast.mpr hb
    apply le_antisymm
    · rw [← Int.zpow_le_iff_le_log hb hr, ← rpow_intCast b]
      refine le_of_le_of_eq ?_ (rpow_logb (zero_lt_one.trans hb1') hb1'.ne' hr)
      exact rpow_le_rpow_of_exponent_le hb1'.le (Int.floor_le _)
    · rw [Int.le_floor, le_logb_iff_rpow_le hb1' hr, rpow_intCast]
      exact Int.zpow_log_le_self hb hr
  · rw [Nat.one_lt_iff_ne_zero_and_ne_one, ← or_iff_not_and_not] at hb
    cases hb
    · simp_all only [CharP.cast_eq_zero, logb_zero_left, Int.floor_zero, Int.log_zero_left]
    · simp_all only [Nat.cast_one, logb_one_left, Int.floor_zero, Int.log_one_left]

@[norm_cast]
/--
theorem `ceil_logb_natCast` / 定理 `ceil_logb_natCast`

English:
theorem ceil_logb_natCast
  given: {b : Nat} {r : Real} (hr : 0 <= r)
  proof: by
  obtain rfl | hr := hr.eq_or_lt
  · rw [logb_zero, Int.clog_zero_right, Int.ceil_zero]
  by_cases hb : 1 < b
  · have hb1' : 1 < (b : Real) := Nat.one_lt_cast.mpr hb
    apply le_antisymm
    · rw [Int.ceil_le, logb_le_iff_le_rpow hb1' hr, rpow_intCast]
      exact Int.self_le_zpow_clog hb r
   

中文:
定理 ceil_logb_natCast
  条件: {b : 自然数} {r : 实数} (hr : 0 <= r)
  证明: by
  obtain rfl | hr := hr.eq_or_lt
  · rw [logb_zero, Int.clog_zero_right, Int.ceil_zero]
  by_cases hb : 1 < b
  · have hb1' : 1 < (b : Real) := Nat.one_lt_cast.mpr hb
    apply le_antisymm
    · rw [Int.ceil_le, logb_le_iff_le_rpow hb1' hr, rpow_intCast]
      exact Int.self_le_zpow_clog hb r
   

Depends on / 依赖: Int.ceil_le, Int.ceil_zero, Int.clog_zero_right, Int.le_ceil, Int.le_zpow_iff_clog_le, Int.self_le_zpow_clog, Nat.one_lt_cast.mpr, Nat.one_lt_iff_ne_zero_and_ne_o, ceil_le, ceil_zero, clog_zero_right, eq_or_lt, hr.eq_or_lt, le_antisymm, le_ceil, le_zpow_iff_clog_le, logb_le_iff_le_rpow, logb_zero, one_lt_cast, one_lt_iff_ne_zero_and_ne_o
-/
theorem ceil_logb_natCast {b : Nat} {r : Real} (hr : 0 <= r) :
    ⌈logb b r⌉ = Int.clog b r := by
  obtain rfl | hr := hr.eq_or_lt
  · rw [logb_zero, Int.clog_zero_right, Int.ceil_zero]
  by_cases hb : 1 < b
  · have hb1' : 1 < (b : Real) := Nat.one_lt_cast.mpr hb
    apply le_antisymm
    · rw [Int.ceil_le, logb_le_iff_le_rpow hb1' hr, rpow_intCast]
      exact Int.self_le_zpow_clog hb r
    · rw [← Int.le_zpow_iff_clog_le hb hr, ← rpow_intCast b]
      refine (rpow_logb (zero_lt_one.trans hb1') hb1'.ne' hr).symm.trans_le ?_
      exact rpow_le_rpow_of_exponent_le hb1'.le (Int.le_ceil _)
  · rw [Nat.one_lt_iff_ne_zero_and_ne_one, ← or_iff_not_and_not] at hb
    cases hb
    · simp_all only [CharP.cast_eq_zero, logb_zero_left, Int.ceil_zero, Int.clog_zero_left]
    · simp_all only [Nat.cast_one, logb_one_left, Int.ceil_zero, Int.clog_one_left]

@[norm_cast]
/--
theorem `natFloor_logb_natCast` / 定理 `natFloor_logb_natCast`

English:
theorem natFloor_logb_natCast
  given: (b : Nat) (n : Nat)
  statement: ⌊logb b n⌋₊ = Nat.log b n
  proof: by
  obtain _ | _ | b := b
  · simp [Real.logb]
  · simp [Real.logb]
  obtain rfl | hn := eq_or_ne n 0
  · simp
  rw [← Nat.cast_inj (R := Int)]; rw [Int.natCast_floor_eq_floor]; rw [floor_logb_natCast (by simp)]; rw [Int.log_natCast]
  exact logb_nonneg (by simp [Nat.cast_add_one_pos]) (Nat.one_le_

中文:
定理 natFloor_logb_natCast
  条件: (b : 自然数) (n : 自然数)
  结论: ⌊logb b n⌋₊ = 自然数.log b n
  证明: by
  obtain _ | _ | b := b
  · simp [Real.logb]
  · simp [Real.logb]
  obtain rfl | hn := eq_or_ne n 0
  · simp
  rw [← Nat.cast_inj (R := Int)]; rw [Int.natCast_floor_eq_floor]; rw [floor_logb_natCast (by simp)]; rw [Int.log_natCast]
  exact logb_nonneg (by simp [Nat.cast_add_one_pos]) (Nat.one_le_

Depends on / 依赖: Int.log_natCast, Int.natCast_floor_eq_floor, Nat.cast_add_one_pos, Nat.cast_inj, Nat.one_le_cast, Real.logb, cast_add_one_pos, cast_inj, eq_or_ne, floor_logb_natCast, log_natCast, logb_nonneg, natCast_floor_eq_floor, one_le_cast
-/
theorem natFloor_logb_natCast (b : Nat) (n : Nat) : ⌊logb b n⌋₊ = Nat.log b n := by
  obtain _ | _ | b := b
  · simp [Real.logb]
  · simp [Real.logb]
  obtain rfl | hn := eq_or_ne n 0
  · simp
  rw [← Nat.cast_inj (R := Int)]; rw [Int.natCast_floor_eq_floor]; rw [floor_logb_natCast (by simp)]; rw [Int.log_natCast]
  exact logb_nonneg (by simp [Nat.cast_add_one_pos]) (Nat.one_le_cast.2 (by lia))

@[norm_cast]
/--
theorem `natCeil_logb_natCast` / 定理 `natCeil_logb_natCast`

English:
theorem natCeil_logb_natCast
  given: (b : Nat) (n : Nat)
  statement: ⌈logb b n⌉₊ = Nat.clog b n
  proof: by
  obtain _ | _ | b := b
  · simp [Real.logb]
  · simp [Real.logb]
  obtain rfl | hn := eq_or_ne n 0
  · simp
  rw [← Nat.cast_inj (R := Int)]; rw [Int.natCast_ceil_eq_ceil]; rw [ceil_logb_natCast (by simp)]; rw [Int.clog_natCast]
  exact logb_nonneg (by simp [Nat.cast_add_one_pos]) (Nat.one_le_ca

中文:
定理 natCeil_logb_natCast
  条件: (b : 自然数) (n : 自然数)
  结论: ⌈logb b n⌉₊ = 自然数.clog b n
  证明: by
  obtain _ | _ | b := b
  · simp [Real.logb]
  · simp [Real.logb]
  obtain rfl | hn := eq_or_ne n 0
  · simp
  rw [← Nat.cast_inj (R := Int)]; rw [Int.natCast_ceil_eq_ceil]; rw [ceil_logb_natCast (by simp)]; rw [Int.clog_natCast]
  exact logb_nonneg (by simp [Nat.cast_add_one_pos]) (Nat.one_le_ca

Depends on / 依赖: Int.clog_natCast, Int.natCast_ceil_eq_ceil, Nat.cast_add_one_pos, Nat.cast_inj, Nat.one_le_cast, Real.logb, cast_add_one_pos, cast_inj, ceil_logb_natCast, clog_natCast, eq_or_ne, logb_nonneg, natCast_ceil_eq_ceil, one_le_cast
-/
theorem natCeil_logb_natCast (b : Nat) (n : Nat) : ⌈logb b n⌉₊ = Nat.clog b n := by
  obtain _ | _ | b := b
  · simp [Real.logb]
  · simp [Real.logb]
  obtain rfl | hn := eq_or_ne n 0
  · simp
  rw [← Nat.cast_inj (R := Int)]; rw [Int.natCast_ceil_eq_ceil]; rw [ceil_logb_natCast (by simp)]; rw [Int.clog_natCast]
  exact logb_nonneg (by simp [Nat.cast_add_one_pos]) (Nat.one_le_cast.2 (by lia))

/--
lemma `natLog_le_logb` / 引理 `natLog_le_logb`

English:
lemma natLog_le_logb
  given: (a b : Nat)
  statement: Nat.log b a <= Real.logb b a
  proof: by
  apply le_trans _ (Int.floor_le ((b : Real).logb a))
  rw [Real.floor_logb_natCast (Nat.cast_nonneg a)]; rw [Int.log_natCast]; rw [Int.cast_natCast]

中文:
引理 natLog_le_logb
  条件: (a b : 自然数)
  结论: 自然数.log b a <= 实数.logb b a
  证明: by
  apply le_trans _ (Int.floor_le ((b : Real).logb a))
  rw [Real.floor_logb_natCast (Nat.cast_nonneg a)]; rw [Int.log_natCast]; rw [Int.cast_natCast]

Depends on / 依赖: Int.cast_natCast, Int.floor_le, Int.log_natCast, Nat.cast_nonneg, Real.floor_logb_natCast, cast_natCast, cast_nonneg, floor_le, floor_logb_natCast, le_trans, log_natCast
-/
lemma natLog_le_logb (a b : Nat) : Nat.log b a <= Real.logb b a := by
  apply le_trans _ (Int.floor_le ((b : Real).logb a))
  rw [Real.floor_logb_natCast (Nat.cast_nonneg a)]; rw [Int.log_natCast]; rw [Int.cast_natCast]

/--
lemma `log2_le_logb` / 引理 `log2_le_logb`

English:
lemma log2_le_logb
  given: (n : Nat)
  statement: Nat.log2 n <= Real.logb 2 n
  proof: by
  calc (Nat.log2 n : Real) = Nat.log 2 n := mod_cast Nat.log2_eq_log_two
  _ <= Real.logb 2 n := natLog_le_logb _ _

@[simp]

中文:
引理 log2_le_logb
  条件: (n : 自然数)
  结论: 自然数.log2 n <= 实数.logb 2 n
  证明: by
  calc (Nat.log2 n : Real) = Nat.log 2 n := mod_cast Nat.log2_eq_log_two
  _ <= Real.logb 2 n := natLog_le_logb _ _

@[simp]

Depends on / 依赖: Nat.log, Nat.log2, Nat.log2_eq_log_two, Real.logb, log2_eq_log_two, mod_cast, natLog_le_logb
-/
lemma log2_le_logb (n : Nat) : Nat.log2 n <= Real.logb 2 n := by
  calc (Nat.log2 n : Real) = Nat.log 2 n := mod_cast Nat.log2_eq_log_two
  _ <= Real.logb 2 n := natLog_le_logb _ _

@[simp]
/--
theorem `logb_eq_zero` / 定理 `logb_eq_zero`

English:
theorem logb_eq_zero
  statement: logb b x = 0 ↔ b = 0 ∨ b = 1 ∨ b = -1 ∨ x = 0 ∨ x = 1 ∨ x = -1
  proof: by
  simp_rw [logb, div_eq_zero_iff, log_eq_zero]
  tauto

中文:
定理 logb_eq_zero
  结论: logb b x = 0 ↔ b = 0 ∨ b = 1 ∨ b = -1 ∨ x = 0 ∨ x = 1 ∨ x = -1
  证明: by
  simp_rw [logb, div_eq_zero_iff, log_eq_zero]
  tauto

Depends on / 依赖: div_eq_zero_iff, log_eq_zero, simp_rw
-/
theorem logb_eq_zero : logb b x = 0 ↔ b = 0 ∨ b = 1 ∨ b = -1 ∨ x = 0 ∨ x = 1 ∨ x = -1 := by
  simp_rw [logb, div_eq_zero_iff, log_eq_zero]
  tauto

/--
theorem `tendsto_logb_nhdsNE_zero` / 定理 `tendsto_logb_nhdsNE_zero`

English:
theorem tendsto_logb_nhdsNE_zero
  given: (hb : 1 < b)
  statement: Tendsto (logb b) (𝓝[!=] 0) atBot
  proof: tendsto_log_nhdsNE_zero.atBot_div_const (log_pos hb)

中文:
定理 tendsto_logb_nhdsNE_zero
  条件: (hb : 1 < b)
  结论: 收敛 (logb b) (𝓝[!=] 0) atBot
  证明: tendsto_log_nhdsNE_zero.atBot_div_const (log_pos hb)

Depends on / 依赖: atBot_div_const, log_pos, tendsto_log_nhdsNE_zero, tendsto_log_nhdsNE_zero.atBot_div_const
-/
theorem tendsto_logb_nhdsNE_zero (hb : 1 < b) : Tendsto (logb b) (𝓝[!=] 0) atBot :=
  tendsto_log_nhdsNE_zero.atBot_div_const (log_pos hb)

/--
theorem `tendsto_logb_nhdsNE_zero_of_base_lt_one` / 定理 `tendsto_logb_nhdsNE_zero_of_base_lt_one`

English:
theorem tendsto_logb_nhdsNE_zero_of_base_lt_one
  given: (hb₀ : 0 < b) (hb : b < 1)
  proof: tendsto_log_nhdsNE_zero.atBot_mul_const_of_neg (inv_lt_zero.2 (log_neg hb₀ hb))

中文:
定理 tendsto_logb_nhdsNE_zero_of_base_lt_one
  条件: (hb₀ : 0 < b) (hb : b < 1)
  证明: tendsto_log_nhdsNE_zero.atBot_mul_const_of_neg (inv_lt_zero.2 (log_neg hb₀ hb))

Depends on / 依赖: atBot_mul_const_of_neg, inv_lt_zero, log_neg, tendsto_log_nhdsNE_zero, tendsto_log_nhdsNE_zero.atBot_mul_const_of_neg
-/
theorem tendsto_logb_nhdsNE_zero_of_base_lt_one (hb₀ : 0 < b) (hb : b < 1) :
    Tendsto (logb b) (𝓝[!=] 0) atTop :=
  tendsto_log_nhdsNE_zero.atBot_mul_const_of_neg (inv_lt_zero.2 (log_neg hb₀ hb))

/--
lemma `tendsto_logb_nhdsGT_zero` / 引理 `tendsto_logb_nhdsGT_zero`

English:
lemma tendsto_logb_nhdsGT_zero
  given: (hb : 1 < b)
  statement: Tendsto (logb b) (𝓝[>] 0) atBot
  proof: tendsto_log_nhdsGT_zero.atBot_div_const (log_pos hb)

中文:
引理 tendsto_logb_nhdsGT_zero
  条件: (hb : 1 < b)
  结论: 收敛 (logb b) (𝓝[>] 0) atBot
  证明: tendsto_log_nhdsGT_zero.atBot_div_const (log_pos hb)

Depends on / 依赖: atBot_div_const, log_pos, tendsto_log_nhdsGT_zero, tendsto_log_nhdsGT_zero.atBot_div_const
-/
lemma tendsto_logb_nhdsGT_zero (hb : 1 < b) : Tendsto (logb b) (𝓝[>] 0) atBot :=
  tendsto_log_nhdsGT_zero.atBot_div_const (log_pos hb)

/--
lemma `tendsto_logb_nhdsGT_zero_of_base_lt_one` / 引理 `tendsto_logb_nhdsGT_zero_of_base_lt_one`

English:
lemma tendsto_logb_nhdsGT_zero_of_base_lt_one
  given: (hb₀ : 0 < b) (hb : b < 1)
  proof: tendsto_log_nhdsGT_zero.atBot_mul_const_of_neg (inv_lt_zero.2 (log_neg hb₀ hb))

中文:
引理 tendsto_logb_nhdsGT_zero_of_base_lt_one
  条件: (hb₀ : 0 < b) (hb : b < 1)
  证明: tendsto_log_nhdsGT_zero.atBot_mul_const_of_neg (inv_lt_zero.2 (log_neg hb₀ hb))

Depends on / 依赖: atBot_mul_const_of_neg, inv_lt_zero, log_neg, tendsto_log_nhdsGT_zero, tendsto_log_nhdsGT_zero.atBot_mul_const_of_neg
-/
lemma tendsto_logb_nhdsGT_zero_of_base_lt_one (hb₀ : 0 < b) (hb : b < 1) :
    Tendsto (logb b) (𝓝[>] 0) atTop :=
  tendsto_log_nhdsGT_zero.atBot_mul_const_of_neg (inv_lt_zero.2 (log_neg hb₀ hb))

/--
lemma `tendsto_abs_logb_atTop` / 引理 `tendsto_abs_logb_atTop`

English:
lemma tendsto_abs_logb_atTop
  given: (hb : b != -1 ∧ b != 0 ∧ b != 1)
  proof: by
  wlog hb₀ : 0 < b generalizing b
  · exact (this (b := -b) (by simp [hb, neg_eq_iff_eq_neg]) (by linarith +splitNe)).congr (by simp)
  wlog hb₁ : 1 < b generalizing b
  · exact (this (b := b⁻¹) (by simp [hb, inv_eq_iff_eq_inv, inv_neg]) (by simpa)
      ((one_lt_inv₀ hb₀).2 (by linarith +splitNe

中文:
引理 tendsto_abs_logb_atTop
  条件: (hb : b != -1 ∧ b != 0 ∧ b != 1)
  证明: by
  wlog hb₀ : 0 < b generalizing b
  · exact (this (b := -b) (by simp [hb, neg_eq_iff_eq_neg]) (by linarith +splitNe)).congr (by simp)
  wlog hb₁ : 1 < b generalizing b
  · exact (this (b := b⁻¹) (by simp [hb, inv_eq_iff_eq_inv, inv_neg]) (by simpa)
      ((one_lt_inv₀ hb₀).2 (by linarith +splitNe

Depends on / 依赖: abs_of_nonneg, eventually_ge_atTop, filter_upwards, generalizing, inv_eq_iff_eq_inv, inv_neg, logb_nonneg, neg_eq_iff_eq_neg, splitNe, tendsto_logb_atTop
-/
lemma tendsto_abs_logb_atTop (hb : b != -1 ∧ b != 0 ∧ b != 1) :
    Tendsto (|logb b ·|) atTop atTop := by
  wlog hb₀ : 0 < b generalizing b
  · exact (this (b := -b) (by simp [hb, neg_eq_iff_eq_neg]) (by linarith +splitNe)).congr (by simp)
  wlog hb₁ : 1 < b generalizing b
  · exact (this (b := b⁻¹) (by simp [hb, inv_eq_iff_eq_inv, inv_neg]) (by simpa)
      ((one_lt_inv₀ hb₀).2 (by linarith +splitNe))).congr (by simp)
  refine (tendsto_logb_atTop hb₁).congr' ?_
  filter_upwards [eventually_ge_atTop 1] with x hx₁
  rw [abs_of_nonneg]
  exact logb_nonneg hb₁ hx₁

/--
theorem `continuousOn_logb` / 定理 `continuousOn_logb`

English:
theorem continuousOn_logb
  statement: ContinuousOn (logb b) {0}ᶜ
  proof: continuousOn_log.div_const _

中文:
定理 continuousOn_logb
  结论: ContinuousOn (logb b) {0}ᶜ
  证明: continuousOn_log.div_const _

Depends on / 依赖: continuousOn_log, continuousOn_log.div_const, div_const
-/
theorem continuousOn_logb : ContinuousOn (logb b) {0}ᶜ := continuousOn_log.div_const _

/-- The real logarithm base b is continuous as a function from nonzero reals. -/
@[fun_prop]
/--
theorem `continuous_logb` / 定理 `continuous_logb`

English:
theorem continuous_logb
  statement: Continuous fun x : { x : Real // x != 0 } => logb b x
  proof: continuous_log.div_const _

中文:
定理 continuous_logb
  结论: 连续 fun x : { x : 实数 // x != 0 } => logb b x
  证明: continuous_log.div_const _

Depends on / 依赖: continuous_log, continuous_log.div_const, div_const
-/
theorem continuous_logb : Continuous fun x : { x : Real // x != 0 } => logb b x :=
  continuous_log.div_const _

/-- The real logarithm base b is continuous as a function from positive reals. -/
@[fun_prop]
/--
theorem `continuous_logb'` / 定理 `continuous_logb'`

English:
theorem continuous_logb'
  statement: Continuous fun x : { x : Real // 0 < x } => logb b x
  proof: continuous_log'.div_const _

中文:
定理 continuous_logb'
  结论: 连续 fun x : { x : 实数 // 0 < x } => logb b x
  证明: continuous_log'.div_const _

Depends on / 依赖: continuous_log, div_const
-/
theorem continuous_logb' : Continuous fun x : { x : Real // 0 < x } => logb b x :=
  continuous_log'.div_const _

/--
theorem `continuousAt_logb` / 定理 `continuousAt_logb`

English:
theorem continuousAt_logb
  given: (hx : x != 0)
  statement: ContinuousAt (logb b) x
  proof: (continuousAt_log hx).div_const _

@[simp]

中文:
定理 continuousAt_logb
  条件: (hx : x != 0)
  结论: ContinuousAt (logb b) x
  证明: (continuousAt_log hx).div_const _

@[simp]

Depends on / 依赖: continuousAt_log, div_const
-/
theorem continuousAt_logb (hx : x != 0) : ContinuousAt (logb b) x :=
  (continuousAt_log hx).div_const _

@[simp]
/--
theorem `continuousAt_logb_iff` / 定理 `continuousAt_logb_iff`

English:
theorem continuousAt_logb_iff
  given: (hb₀ : 0 < b) (hb : b != 1)
  statement: ContinuousAt (logb b) x ↔ x != 0
  proof: by
  refine ⟨?_, continuousAt_logb⟩
  rintro h rfl
  cases lt_or_gt_of_ne hb with
  | inl hb₁ =>
      exact not_tendsto_nhds_of_tendsto_atTop (tendsto_logb_nhdsNE_zero_of_base_lt_one hb₀ hb₁)
        _ (h.tendsto.mono_left inf_le_left)
  | inr hb₁ =>
      exact not_tendsto_nhds_of_tendsto_atBot (t

中文:
定理 continuousAt_logb_iff
  条件: (hb₀ : 0 < b) (hb : b != 1)
  结论: ContinuousAt (logb b) x ↔ x != 0
  证明: by
  refine ⟨?_, continuousAt_logb⟩
  rintro h rfl
  cases lt_or_gt_of_ne hb with
  | inl hb₁ =>
      exact not_tendsto_nhds_of_tendsto_atTop (tendsto_logb_nhdsNE_zero_of_base_lt_one hb₀ hb₁)
        _ (h.tendsto.mono_left inf_le_left)
  | inr hb₁ =>
      exact not_tendsto_nhds_of_tendsto_atBot (t

Depends on / 依赖: continuousAt_logb, h.tendsto.mono_left, inf_le_left, lt_or_gt_of_ne, mono_left, not_tendsto_nhds_of_tendsto_atBot, not_tendsto_nhds_of_tendsto_atTop, tendsto, tendsto_logb_nhdsNE_zero, tendsto_logb_nhdsNE_zero_of_base_lt_one
-/
theorem continuousAt_logb_iff (hb₀ : 0 < b) (hb : b != 1) : ContinuousAt (logb b) x ↔ x != 0 := by
  refine ⟨?_, continuousAt_logb⟩
  rintro h rfl
  cases lt_or_gt_of_ne hb with
  | inl hb₁ =>
      exact not_tendsto_nhds_of_tendsto_atTop (tendsto_logb_nhdsNE_zero_of_base_lt_one hb₀ hb₁)
        _ (h.tendsto.mono_left inf_le_left)
  | inr hb₁ =>
      exact not_tendsto_nhds_of_tendsto_atBot (tendsto_logb_nhdsNE_zero hb₁)
        _ (h.tendsto.mono_left inf_le_left)

/--
theorem `logb_prod` / 定理 `logb_prod`

English:
theorem logb_prod
  given: {α : Type*} (s : Finset α) (f : α -> Real) (hf : forall x in s, f x != 0)
  proof: by
  induction s using Finset.cons_induction_on with
  | empty => simp
  | cons => simp_all [logb_mul, Finset.prod_ne_zero_iff]

中文:
定理 logb_prod
  条件: {α : 类型} (s : 有限集 α) (f : α -> 实数) (hf : 对任意 x in s, f x != 0)
  证明: by
  induction s using Finset.cons_induction_on with
  | empty => simp
  | cons => simp_all [logb_mul, Finset.prod_ne_zero_iff]

Depends on / 依赖: Finset, Finset.cons_induction_on, Finset.prod_ne_zero_iff, cons_induction_on, logb_mul, prod_ne_zero_iff
-/
theorem logb_prod {α : Type*} (s : Finset α) (f : α -> Real) (hf : forall x in s, f x != 0) :
    logb b (∏ i in s, f i) = ∑ i in s, logb b (f i) := by
  induction s using Finset.cons_induction_on with
  | empty => simp
  | cons => simp_all [logb_mul, Finset.prod_ne_zero_iff]

/--
theorem `_root_.Finsupp.logb_prod` / 定理 `_root_.Finsupp.logb_prod`

English:
theorem _root_.Finsupp.logb_prod
  statement: {α β : Type*} [Zero β] (f : α ->₀ β) (g : α -> β -> Real)
  proof: logb_prod _ _ fun _x hx h₀ => Finsupp.mem_support_iff.1 hx hg _ h₀

中文:
定理 _root_.有限支撑.logb_prod
  结论: {α β : 类型} [零 β] (f : α ->₀ β) (g : α -> β -> 实数)
  证明: logb_prod _ _ fun _x hx h₀ => Finsupp.mem_support_iff.1 hx hg _ h₀
-/
protected theorem _root_.Finsupp.logb_prod {α β : Type*} [Zero β] (f : α ->₀ β) (g : α -> β -> Real)
    (hg : forall a, g a (f a) = 0 -> f a = 0) : logb b (f.prod g) = f.sum fun a c => logb b (g a c) :=
logb_prod _ _ fun _x hx h₀ => Finsupp.mem_support_iff.1 hx hg _ h₀

/--
theorem `logb_nat_eq_sum_factorization` / 定理 `logb_nat_eq_sum_factorization`

English:
theorem logb_nat_eq_sum_factorization
  given: (n : Nat)
  proof: by
  simp only [logb, mul_div_assoc', log_nat_eq_sum_factorization n, Finsupp.sum, Finset.sum_div]

中文:
定理 logb_nat_eq_sum_factorization
  条件: (n : 自然数)
  证明: by
  simp only [logb, mul_div_assoc', log_nat_eq_sum_factorization n, Finsupp.sum, Finset.sum_div]

Depends on / 依赖: Finset, Finset.sum_div, Finsupp, Finsupp.sum, log_nat_eq_sum_factorization, mul_div_assoc, sum_div
-/
theorem logb_nat_eq_sum_factorization (n : Nat) :
    logb b n = n.factorization.sum fun p t => t * logb b p := by
  simp only [logb, mul_div_assoc', log_nat_eq_sum_factorization n, Finsupp.sum, Finset.sum_div]

/--
theorem `tendsto_pow_logb_div_mul_add_atTop` / 定理 `tendsto_pow_logb_div_mul_add_atTop`

English:
theorem tendsto_pow_logb_div_mul_add_atTop
  given: (a c : Real) (n : Nat) (ha : a != 0)
  proof: by
  cases eq_or_ne (log b) 0 with
  | inl h => simpa [logb, h] using! ((tendsto_mul_add_inv_atTop_nhds_zero _ _ ha).const_mul _)
  | inr h => apply (tendsto_pow_log_div_mul_add_atTop (a * (log b) ^ n) (c * (log b) ^ n) n
                (by positivity)).congr fun x => by simp [field, div_pow, logb]

中文:
定理 tendsto_pow_logb_div_mul_add_atTop
  条件: (a c : 实数) (n : 自然数) (ha : a != 0)
  证明: by
  cases eq_or_ne (log b) 0 with
  | inl h => simpa [logb, h] using! ((tendsto_mul_add_inv_atTop_nhds_zero _ _ ha).const_mul _)
  | inr h => apply (tendsto_pow_log_div_mul_add_atTop (a * (log b) ^ n) (c * (log b) ^ n) n
                (by positivity)).congr fun x => by simp [field, div_pow, logb]

Depends on / 依赖: const_mul, div_pow, eq_or_ne, tendsto_mul_add_inv_atTop_nhds_zero, tendsto_pow_log_div_mul_add_atTop
-/
theorem tendsto_pow_logb_div_mul_add_atTop (a c : Real) (n : Nat) (ha : a != 0) :
    Tendsto (fun x => logb b x ^ n / (a * x + c)) atTop (𝓝 0) := by
  cases eq_or_ne (log b) 0 with
  | inl h => simpa [logb, h] using! ((tendsto_mul_add_inv_atTop_nhds_zero _ _ ha).const_mul _)
  | inr h => apply (tendsto_pow_log_div_mul_add_atTop (a * (log b) ^ n) (c * (log b) ^ n) n
                (by positivity)).congr fun x => by simp [field, div_pow, logb]

/--
theorem `isLittleO_pow_logb_id_atTop` / 定理 `isLittleO_pow_logb_id_atTop`

English:
theorem isLittleO_pow_logb_id_atTop
  given: {n : Nat}
  statement: (fun x => logb b x ^ n) =o[atTop] id
  proof: by
  rw [Asymptotics.isLittleO_iff_tendsto']
  · simpa using tendsto_pow_logb_div_mul_add_atTop 1 0 n one_ne_zero
  · filter_upwards [eventually_ne_atTop (0 : Real)] with x h₁ h₂ using (h₁ h₂).elim

中文:
定理 isLittleO_pow_logb_id_atTop
  条件: {n : 自然数}
  结论: (fun x => logb b x ^ n) =o[atTop] id
  证明: by
  rw [Asymptotics.isLittleO_iff_tendsto']
  · simpa using tendsto_pow_logb_div_mul_add_atTop 1 0 n one_ne_zero
  · filter_upwards [eventually_ne_atTop (0 : Real)] with x h₁ h₂ using (h₁ h₂).elim

Depends on / 依赖: Asymptotics, Asymptotics.isLittleO_iff_tendsto, eventually_ne_atTop, filter_upwards, isLittleO_iff_tendsto, one_ne_zero, tendsto_pow_logb_div_mul_add_atTop
-/
theorem isLittleO_pow_logb_id_atTop {n : Nat} : (fun x => logb b x ^ n) =o[atTop] id := by
  rw [Asymptotics.isLittleO_iff_tendsto']
  · simpa using tendsto_pow_logb_div_mul_add_atTop 1 0 n one_ne_zero
  · filter_upwards [eventually_ne_atTop (0 : Real)] with x h₁ h₂ using (h₁ h₂).elim

/--
theorem `isLittleO_logb_id_atTop` / 定理 `isLittleO_logb_id_atTop`

English:
theorem isLittleO_logb_id_atTop
  statement: logb b =o[atTop] id
  proof: isLittleO_pow_logb_id_atTop.congr_left fun _ => pow_one _

中文:
定理 isLittleO_logb_id_atTop
  结论: logb b =o[atTop] id
  证明: isLittleO_pow_logb_id_atTop.congr_left fun _ => pow_one _

Depends on / 依赖: congr_left, isLittleO_pow_logb_id_atTop, isLittleO_pow_logb_id_atTop.congr_left, pow_one
-/
theorem isLittleO_logb_id_atTop : logb b =o[atTop] id :=
  isLittleO_pow_logb_id_atTop.congr_left fun _ => pow_one _

/--
theorem `isLittleO_const_logb_atTop` / 定理 `isLittleO_const_logb_atTop`

English:
theorem isLittleO_const_logb_atTop
  given: {c : Real} (hb : b != -1 ∧ b != 0 ∧ b != 1)
  proof: by
  rw [Asymptotics.isLittleO_const_left]; rw [or_iff_not_imp_left]
  intro hc
  exact tendsto_abs_logb_atTop hb

中文:
定理 isLittleO_const_logb_atTop
  条件: {c : 实数} (hb : b != -1 ∧ b != 0 ∧ b != 1)
  证明: by
  rw [Asymptotics.isLittleO_const_left]; rw [or_iff_not_imp_left]
  intro hc
  exact tendsto_abs_logb_atTop hb

Depends on / 依赖: Asymptotics, Asymptotics.isLittleO_const_left, isLittleO_const_left, or_iff_not_imp_left, tendsto_abs_logb_atTop
-/
theorem isLittleO_const_logb_atTop {c : Real} (hb : b != -1 ∧ b != 0 ∧ b != 1) :
    (fun _ => c) =o[atTop] logb b := by
  rw [Asymptotics.isLittleO_const_left]; rw [or_iff_not_imp_left]
  intro hc
  exact tendsto_abs_logb_atTop hb

/--
theorem `isBigO_logb_log` / 定理 `isBigO_logb_log`

English:
theorem isBigO_logb_log
  statement: logb b =O[⊤] log
  proof: by
  by_cases! h : b = -1 ∨ b = 0 ∨ b = 1
  · obtain rfl | rfl | rfl := h
    all_goals simpa [-Asymptotics.isBigO_top] using! Asymptotics.isBigO_zero log ⊤
  · simpa [logb, div_eq_mul_inv, mul_comm]
      using! (Asymptotics.isBigO_refl log ⊤).const_mul_left (log b)⁻¹

中文:
定理 isBigO_logb_log
  结论: logb b =O[⊤] log
  证明: by
  by_cases! h : b = -1 ∨ b = 0 ∨ b = 1
  · obtain rfl | rfl | rfl := h
    all_goals simpa [-Asymptotics.isBigO_top] using! Asymptotics.isBigO_zero log ⊤
  · simpa [logb, div_eq_mul_inv, mul_comm]
      using! (Asymptotics.isBigO_refl log ⊤).const_mul_left (log b)⁻¹

Depends on / 依赖: Asymptotics, Asymptotics.isBigO_refl, Asymptotics.isBigO_top, Asymptotics.isBigO_zero, all_goals, const_mul_left, div_eq_mul_inv, isBigO_refl, isBigO_top, isBigO_zero, mul_comm
-/
theorem isBigO_logb_log : logb b =O[⊤] log := by
  by_cases! h : b = -1 ∨ b = 0 ∨ b = 1
  · obtain rfl | rfl | rfl := h
    all_goals simpa [-Asymptotics.isBigO_top] using! Asymptotics.isBigO_zero log ⊤
  · simpa [logb, div_eq_mul_inv, mul_comm]
      using! (Asymptotics.isBigO_refl log ⊤).const_mul_left (log b)⁻¹

/--
theorem `isBigO_log_const_mul_log_atTop` / 定理 `isBigO_log_const_mul_log_atTop`

English:
theorem isBigO_log_const_mul_log_atTop
  given: (c : Real)
  statement: (fun x => log (c * x)) =O[atTop] log
  proof: by
  obtain rfl | hc := eq_or_ne c 0
  · simpa using isLittleO_const_log_atTop.isBigO
  · calc (fun x => log (c * x))
      =ᶠ[atTop] (fun x => log c + log x) := by
          filter_upwards [eventually_gt_atTop 0] with a ha using log_mul hc ha.ne'
      _ =O[atTop] log :=
          isLittleO_const_l

中文:
定理 isBigO_log_const_mul_log_atTop
  条件: (c : 实数)
  结论: (fun x => log (c * x)) =O[atTop] log
  证明: by
  obtain rfl | hc := eq_or_ne c 0
  · simpa using isLittleO_const_log_atTop.isBigO
  · calc (fun x => log (c * x))
      =ᶠ[atTop] (fun x => log c + log x) := by
          filter_upwards [eventually_gt_atTop 0] with a ha using log_mul hc ha.ne'
      _ =O[atTop] log :=
          isLittleO_const_l

Depends on / 依赖: Asymptotics, Asymptotics.isBigO_refl, eq_or_ne, eventually_gt_atTop, filter_upwards, ha.ne, isBigO, isBigO_refl, isLittleO_const_log_atTop, isLittleO_const_log_atTop.isBigO, isLittleO_const_log_atTop.isBigO.add, log_mul
-/
theorem isBigO_log_const_mul_log_atTop (c : Real) : (fun x => log (c * x)) =O[atTop] log := by
  obtain rfl | hc := eq_or_ne c 0
  · simpa using isLittleO_const_log_atTop.isBigO
  · calc (fun x => log (c * x))
      =ᶠ[atTop] (fun x => log c + log x) := by
          filter_upwards [eventually_gt_atTop 0] with a ha using log_mul hc ha.ne'
      _ =O[atTop] log :=
          isLittleO_const_log_atTop.isBigO.add (Asymptotics.isBigO_refl ..)

/--
theorem `isBigO_log_mul_const_log_atTop` / 定理 `isBigO_log_mul_const_log_atTop`

English:
theorem isBigO_log_mul_const_log_atTop
  given: (c : Real)
  statement: (fun x => log (x * c)) =O[atTop] log
  proof: by
  simpa [mul_comm] using isBigO_log_const_mul_log_atTop c

中文:
定理 isBigO_log_mul_const_log_atTop
  条件: (c : 实数)
  结论: (fun x => log (x * c)) =O[atTop] log
  证明: by
  simpa [mul_comm] using isBigO_log_const_mul_log_atTop c

Depends on / 依赖: isBigO_log_const_mul_log_atTop, mul_comm
-/
theorem isBigO_log_mul_const_log_atTop (c : Real) : (fun x => log (x * c)) =O[atTop] log := by
  simpa [mul_comm] using isBigO_log_const_mul_log_atTop c

/--
theorem `isBigO_logb_const_mul_log_atTop` / 定理 `isBigO_logb_const_mul_log_atTop`

English:
theorem isBigO_logb_const_mul_log_atTop
  given: (c : Real)
  statement: (fun x => logb b (c * x)) =O[atTop] log
  proof: by
  simpa [logb, div_eq_mul_inv, mul_comm]
    using (isBigO_log_const_mul_log_atTop c).const_mul_left (log b)⁻¹

中文:
定理 isBigO_logb_const_mul_log_atTop
  条件: (c : 实数)
  结论: (fun x => logb b (c * x)) =O[atTop] log
  证明: by
  simpa [logb, div_eq_mul_inv, mul_comm]
    using (isBigO_log_const_mul_log_atTop c).const_mul_left (log b)⁻¹

Depends on / 依赖: const_mul_left, div_eq_mul_inv, isBigO_log_const_mul_log_atTop, mul_comm
-/
theorem isBigO_logb_const_mul_log_atTop (c : Real) : (fun x => logb b (c * x)) =O[atTop] log := by
  simpa [logb, div_eq_mul_inv, mul_comm]
    using (isBigO_log_const_mul_log_atTop c).const_mul_left (log b)⁻¹

/--
theorem `isBigO_logb_mul_const_log_atTop` / 定理 `isBigO_logb_mul_const_log_atTop`

English:
theorem isBigO_logb_mul_const_log_atTop
  given: (c : Real)
  statement: (fun x => logb b (x * c)) =O[atTop] log
  proof: by
  simpa [mul_comm] using isBigO_logb_const_mul_log_atTop c

中文:
定理 isBigO_logb_mul_const_log_atTop
  条件: (c : 实数)
  结论: (fun x => logb b (x * c)) =O[atTop] log
  证明: by
  simpa [mul_comm] using isBigO_logb_const_mul_log_atTop c

Depends on / 依赖: isBigO_logb_const_mul_log_atTop, mul_comm
-/
theorem isBigO_logb_mul_const_log_atTop (c : Real) : (fun x => logb b (x * c)) =O[atTop] log := by
  simpa [mul_comm] using isBigO_logb_const_mul_log_atTop c

end Real

section Continuity

open Real

variable {α : Type*}
variable {b : Real}

/--
theorem `Filter.Tendsto.logb` / 定理 `Filter.Tendsto.logb`

English:
theorem Filter.Tendsto.logb
  statement: {f : α -> Real} {l : Filter α} {x : Real}
  proof: (continuousAt_logb hx).tendsto.comp h

中文:
定理 滤子.收敛.logb
  结论: {f : α -> 实数} {l : 滤子 α} {x : 实数}
  证明: (continuousAt_logb hx).tendsto.comp h

Depends on / 依赖: continuousAt_logb, tendsto, tendsto.comp
-/
theorem Filter.Tendsto.logb {f : α -> Real} {l : Filter α} {x : Real}
    (h : Tendsto f l (𝓝 x)) (hx : x != 0) :
    Tendsto (fun y => logb b (f y)) l (𝓝 (logb b x)) :=
  (continuousAt_logb hx).tendsto.comp h

variable [TopologicalSpace α] {f : α -> Real} {s : Set α} {a : α}

@[fun_prop]
/--
theorem `Continuous.logb` / 定理 `Continuous.logb`

English:
theorem Continuous.logb
  given: (hf : Continuous f) (h₀ : forall x, f x != 0)
  proof: continuousOn_logb.comp_continuous hf h₀

@[fun_prop]
nonrec theorem ContinuousAt.logb (hf : ContinuousAt f a) (h₀ : f a != 0) :
    ContinuousAt (fun x => logb b (f x)) a :=
  hf.logb h₀

nonrec theorem ContinuousWithinAt.logb (hf : ContinuousWithinAt f s a) (h₀ : f a != 0) :
    ContinuousWithinAt 

中文:
定理 连续.logb
  条件: (hf : 连续 f) (h₀ : 对任意 x, f x != 0)
  证明: continuousOn_logb.comp_continuous hf h₀

@[fun_prop]
nonrec theorem ContinuousAt.logb (hf : ContinuousAt f a) (h₀ : f a != 0) :
    ContinuousAt (fun x => logb b (f x)) a :=
  hf.logb h₀

nonrec theorem ContinuousWithinAt.logb (hf : ContinuousWithinAt f s a) (h₀ : f a != 0) :
    ContinuousWithinAt 

Depends on / 依赖: comp_continuous, continuousOn_logb, continuousOn_logb.comp_continuous
-/
theorem Continuous.logb (hf : Continuous f) (h₀ : forall x, f x != 0) :
    Continuous fun x => logb b (f x) :=
  continuousOn_logb.comp_continuous hf h₀

@[fun_prop]
nonrec theorem ContinuousAt.logb (hf : ContinuousAt f a) (h₀ : f a != 0) :
    ContinuousAt (fun x => logb b (f x)) a :=
  hf.logb h₀

nonrec theorem ContinuousWithinAt.logb (hf : ContinuousWithinAt f s a) (h₀ : f a != 0) :
    ContinuousWithinAt (fun x => logb b (f x)) s a :=
  hf.logb h₀

@[fun_prop]
/--
theorem `ContinuousOn.logb` / 定理 `ContinuousOn.logb`

English:
theorem ContinuousOn.logb
  given: (hf : ContinuousOn f s) (h₀ : forall x in s, f x != 0)
  proof: fun x hx => (hf x hx).logb (h₀ x hx)

中文:
定理 ContinuousOn.logb
  条件: (hf : ContinuousOn f s) (h₀ : 对任意 x in s, f x != 0)
  证明: fun x hx => (hf x hx).logb (h₀ x hx)
-/
theorem ContinuousOn.logb (hf : ContinuousOn f s) (h₀ : forall x in s, f x != 0) :
    ContinuousOn (fun x => logb b (f x)) s := fun x hx => (hf x hx).logb (h₀ x hx)

end Continuity

section TendstoCompAddSub

open Filter

namespace Real

variable {b : Real}

/--
theorem `tendsto_logb_comp_add_sub_logb` / 定理 `tendsto_logb_comp_add_sub_logb`

English:
theorem tendsto_logb_comp_add_sub_logb
  given: (y : Real)
  proof: by
  simpa [sub_div] using! (tendsto_log_comp_add_sub_log y).div_const (log b)

中文:
定理 tendsto_logb_comp_add_sub_logb
  条件: (y : 实数)
  证明: by
  simpa [sub_div] using! (tendsto_log_comp_add_sub_log y).div_const (log b)

Depends on / 依赖: div_const, sub_div, tendsto_log_comp_add_sub_log
-/
theorem tendsto_logb_comp_add_sub_logb (y : Real) :
    Tendsto (fun x : Real => logb b (x + y) - logb b x) atTop (𝓝 0) := by
  simpa [sub_div] using! (tendsto_log_comp_add_sub_log y).div_const (log b)

/--
theorem `tendsto_logb_nat_add_one_sub_logb` / 定理 `tendsto_logb_nat_add_one_sub_logb`

English:
theorem tendsto_logb_nat_add_one_sub_logb
  proof: (tendsto_logb_comp_add_sub_logb 1).comp tendsto_natCast_atTop_atTop

中文:
定理 tendsto_logb_nat_add_one_sub_logb
  证明: (tendsto_logb_comp_add_sub_logb 1).comp tendsto_natCast_atTop_atTop

Depends on / 依赖: tendsto_logb_comp_add_sub_logb, tendsto_natCast_atTop_atTop
-/
theorem tendsto_logb_nat_add_one_sub_logb :
    Tendsto (fun k : Nat => logb b (k + 1) - logb b k) atTop (𝓝 0) :=
  (tendsto_logb_comp_add_sub_logb 1).comp tendsto_natCast_atTop_atTop

end Real

end TendstoCompAddSub

section Induction

/--
lemma `Real.induction_Ico_mul` / 引理 `Real.induction_Ico_mul`

English:
lemma Real.induction_Ico_mul
  statement: {P : Real -> Prop} (x₀ r : Real) (hr : 1 < r) (hx₀ : 0 < x₀)
  proof: by
  suffices forall n : Nat, forall x in Set.Ico x₀ (r ^ (n + 1) * x₀), P x by
    intro x hx
    have hx' : 0 < x / x₀ := div_pos (hx₀.trans_le hx) hx₀
    refine this ⌊logb r (x / x₀)⌋₊ x ?_
    rw [mem_Ico]; rw [← div_lt_iff₀ hx₀]; rw [← rpow_natCast]; rw [← logb_lt_iff_lt_rpow hr hx']; rw [Nat.

中文:
引理 实数.induction_Ico_mul
  结论: {P : 实数 -> 命题} (x₀ r : 实数) (hr : 1 < r) (hx₀ : 0 < x₀)
  证明: by
  suffices forall n : Nat, forall x in Set.Ico x₀ (r ^ (n + 1) * x₀), P x by
    intro x hx
    have hx' : 0 < x / x₀ := div_pos (hx₀.trans_le hx) hx₀
    refine this ⌊logb r (x / x₀)⌋₊ x ?_
    rw [mem_Ico]; rw [← div_lt_iff₀ hx₀]; rw [← rpow_natCast]; rw [← logb_lt_iff_lt_rpow hr hx']; rw [Nat.

Depends on / 依赖: Ico_subset_Ico_union_Ico, Nat.cast_add, Nat.cast_one, Nat.lt_floor_add_one, Set.Ico, cast_add, cast_one, div_pos, logb_lt_iff_lt_rpow, lt_floor_add_one, mem_Ico, rpow_natCast, trans_le
-/
lemma Real.induction_Ico_mul {P : Real -> Prop} (x₀ r : Real) (hr : 1 < r) (hx₀ : 0 < x₀)
    (base : forall x in Set.Ico x₀ (r * x₀), P x)
    (step : forall n : Nat, n >= 1 -> (forall z in Set.Ico x₀ (r ^ n * x₀), P z) ->
      (forall z in Set.Ico (r ^ n * x₀) (r ^ (n + 1) * x₀), P z)) :
    forall x >= x₀, P x := by
  suffices forall n : Nat, forall x in Set.Ico x₀ (r ^ (n + 1) * x₀), P x by
    intro x hx
    have hx' : 0 < x / x₀ := div_pos (hx₀.trans_le hx) hx₀
    refine this ⌊logb r (x / x₀)⌋₊ x ?_
    rw [mem_Ico]; rw [← div_lt_iff₀ hx₀]; rw [← rpow_natCast]; rw [← logb_lt_iff_lt_rpow hr hx']; rw [Nat.cast_add]; rw [Nat.cast_one]
    exact ⟨hx, Nat.lt_floor_add_one _⟩
  intro n
  induction n with
  | zero => simpa using base
  | succ n ih =>
    exact fun x hx => (Ico_subset_Ico_union_Ico hx).elim (ih x) (step (n + 1) (by simp) ih _)

end Induction
