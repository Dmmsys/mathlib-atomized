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

variable {b x y : ℝ}

/-- The real logarithm in a given base. As with the natural logarithm, we define `logb b x` to
be `logb b |x|` for `x < 0`, and `0` for `x = 0`. -/
@[pp_nodot]
/-
**Real.logb** 是 Mathlib 中的一个定义，位于命名空间 `Real`。
形式化陈述：logb (b x : Real) : Real
参数：b x : Real。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The real logarithm in a given base. As with the natural logarithm, we define `lo
gb b x` to
be `logb b |x|` for `x < 0`, and `0` for `x = 0`.
-/
noncomputable def logb (b x : ℝ) : ℝ :=
  log x / log b
/-
**Real.log_div_log** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：log_div_log : log x / log b = logb b x
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem log_div_log : log x / log b = logb b x :=
  rfl

@[simp]
/-
**Real.logb_zero** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：logb_zero : logb b 0 = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.log_zero`：log_zero : log 0 = 0
· 使用定理 `zero_div`：zero_div (a : G₀) : 0 / a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem logb_zero : logb b 0 = 0 := by simp [logb]

@[simp]
/-
**Real.logb_one** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：logb_one : logb b 1 = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.log_one`：log_one : log 1 = 0
· 使用定理 `zero_div`：zero_div (a : G₀) : 0 / a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem logb_one : logb b 1 = 0 := by simp [logb]
/-
**Real.logb_zero_left** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：logb_zero_left : logb 0 x = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.log_zero`：log_zero : log 0 = 0
· 使用定理 `div_zero`：div_zero (a : G₀) : a / 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem logb_zero_left : logb 0 x = 0 := by simp only [← log_div_log, log_zero, div_zero]
/-
**Real.logb_zero_left_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：Real.logb 0 = 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.logb_zero_left`：logb_zero_left : logb 0 x = 0
· 使用定理 `Pi.zero_apply`：∀ {ι : Type u_1} {M : ι → Type u_5} [inst : (i : ι) → Zer
o (M i)] (i : ι), 0 i = 0
-/
@[simp] theorem logb_zero_left_eq_zero : logb 0 = 0 := by ext; rw [logb_zero_left, Pi.zero_apply]
/-
**Real.logb_one_left** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：logb_one_left : logb 1 x = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.log_one`：log_one : log 1 = 0
· 使用定理 `div_zero`：div_zero (a : G₀) : a / 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem logb_one_left : logb 1 x = 0 := by simp only [← log_div_log, log_one, div_zero]
/-
**Real.logb_one_left_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：Real.logb 1 = 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.logb_one_left`：logb_one_left : logb 1 x = 0
· 使用定理 `Pi.zero_apply`：∀ {ι : Type u_1} {M : ι → Type u_5} [inst : (i : ι) → Zer
o (M i)] (i : ι), 0 i = 0
-/
@[simp] theorem logb_one_left_eq_zero : logb 1 = 0 := by ext; rw [logb_one_left, Pi.zero_apply]

@[simp]
/-
**Real.logb_self_eq_one** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：logb_self_eq_one (hb : 1 < b) : logb b b = 1
参数：hb : 1 < b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `div_self`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a : G₀}, a ≠ 0 → 
a / a = 1
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Real.log_pos`：log_pos (hx : 1 < x) : 0 < log x
-/
lemma logb_self_eq_one (hb : 1 < b) : logb b b = 1 :=
  div_self (log_pos hb).ne'
/-
**Real.logb_self_eq_one_iff** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：logb_self_eq_one_iff : logb b b = 1 ↔ b != 0 ∧ b != 1 ∧ b != -1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `div_zero`：div_zero (a : G₀) : a / 0 = 0
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `div_self`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a : G₀}, a ≠ 0 → 
a / a = 1
· 使用定理 `Real.log_ne_zero`：log_ne_zero {x : Real} : log x != 0 ↔ x != 0 ∧ x != 1 
∧ x != -1
-/
lemma logb_self_eq_one_iff : logb b b = 1 ↔ b ≠ 0 ∧ b ≠ 1 ∧ b ≠ -1 :=
  Iff.trans ⟨fun h h' => by simp [logb, h'] at h, div_self⟩ log_ne_zero

@[simp]
/-
**Real.logb_abs_base** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：logb_abs_base (b x : Real) : logb |b| x = logb b x
参数：b x : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.logb.eq_1`：∀ (b x : ℝ), Real.logb b x = Real.log x / Real.log b
· 使用定理 `Real.log_abs`：log_abs (x : Real) : log |x| = log x
-/
theorem logb_abs_base (b x : ℝ) : logb |b| x = logb b x := by rw [logb, logb, log_abs]

@[simp]
/-
**Real.logb_abs** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：logb_abs (b x : Real) : logb b |x| = logb b x
参数：b x : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.logb.eq_1`：∀ (b x : ℝ), Real.logb b x = Real.log x / Real.log b
· 使用定理 `Real.log_abs`：log_abs (x : Real) : log |x| = log x
-/
theorem logb_abs (b x : ℝ) : logb b |x| = logb b x := by rw [logb, logb, log_abs]

@[simp]
/-
**Real.logb_neg_base_eq_logb** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：logb_neg_base_eq_logb (b : Real) : logb (-b) = logb b
参数：b : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.logb_abs_base`：logb_abs_base (b x : Real) : logb |b| x = logb b x
· 使用定理 `abs_neg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] (a : 
α), |(-a)| = |a|
-/
theorem logb_neg_base_eq_logb (b : ℝ) : logb (-b) = logb b := by
  ext x; rw [← logb_abs_base b x, ← logb_abs_base (-b) x, abs_neg]

@[simp]
/-
**Real.logb_neg_eq_logb** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：logb_neg_eq_logb (b x : Real) : logb b (-x) = logb b x
参数：b x : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.logb_abs`：logb_abs (b x : Real) : logb b |x| = logb b x
· 使用定理 `abs_neg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] (a : 
α), |(-a)| = |a|
-/
theorem logb_neg_eq_logb (b x : ℝ) : logb b (-x) = logb b x := by
  rw [← logb_abs b x, ← logb_abs b (-x), abs_neg]
/-
**Real.logb_mul** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：logb_mul (hx : x != 0) (hy : y != 0) : logb b (x * y) = logb b x + logb b 
y
参数：hx : x != 0；hy : y != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.log_mul`：log_mul (hx : x != 0) (hy : y != 0) : log (x * y) = log x 
+ log y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `add_div`：add_div (a b c : K) : (a + b) / c = a / c + b / c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem logb_mul (hx : x ≠ 0) (hy : y ≠ 0) : logb b (x * y) = logb b x + logb b y := by
  simp_rw [logb, log_mul hx hy, add_div]
/-
**Real.logb_div** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：logb_div (hx : x != 0) (hy : y != 0) : logb b (x / y) = logb b x - logb b 
y
参数：hx : x != 0；hy : y != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.log_div`：log_div (hx : x != 0) (hy : y != 0) : log (x / y) = log x 
- log y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `sub_div`：sub_div (a b c : K) : (a - b) / c = a / c - b / c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem logb_div (hx : x ≠ 0) (hy : y ≠ 0) : logb b (x / y) = logb b x - logb b y := by
  simp_rw [logb, log_div hx hy, sub_div]

@[simp]
/-
**Real.logb_inv** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：logb_inv (b x : Real) : logb b x⁻¹ = -logb b x
参数：b x : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.log_inv`：log_inv (x : Real) : log x⁻¹ = -log x
· 使用引理 `neg_div`：neg_div (a b : R) : -b / a = -(b / a)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem logb_inv (b x : ℝ) : logb b x⁻¹ = -logb b x := by simp [logb, neg_div]

@[simp]
/-
**Real.logb_inv_base** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：logb_inv_base (b x : Real) : logb b⁻¹ x = -logb b x
参数：b x : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.log_inv`：log_inv (x : Real) : log x⁻¹ = -log x
· 使用引理 `div_neg`：div_neg (a : R) : a / -b = -(a / b)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem logb_inv_base (b x : ℝ) : logb b⁻¹ x = -logb b x := by simp [logb, div_neg]
/-
**Real.inv_logb** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：inv_logb (a b : Real) : (logb a b)⁻¹ = logb b a
参数：a b : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inv_div`：inv_div : (a / b)⁻¹ = b / a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem inv_logb (a b : ℝ) : (logb a b)⁻¹ = logb b a := by simp_rw [logb, inv_div]
/-
**Real.inv_logb_mul_base** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：inv_logb_mul_base {a b : Real} (h₁ : a != 0) (h₂ : b != 0) (c : Real) : (l
ogb (a * b) c)⁻¹ = (logb a c)⁻¹ + (logb b c)⁻¹
参数：h₁ : a != 0；h₂ : b != 0；c : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.inv_logb`：inv_logb (a b : Real) : (logb a b)⁻¹ = logb b a
· 使用定理 `Real.logb_mul`：logb_mul (hx : x != 0) (hy : y != 0) : logb b (x * y) = l
ogb b x + logb b y
-/
theorem inv_logb_mul_base {a b : ℝ} (h₁ : a ≠ 0) (h₂ : b ≠ 0) (c : ℝ) :
    (logb (a * b) c)⁻¹ = (logb a c)⁻¹ + (logb b c)⁻¹ := by
  simp_rw [inv_logb]; exact logb_mul h₁ h₂
/-
**Real.inv_logb_div_base** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：inv_logb_div_base {a b : Real} (h₁ : a != 0) (h₂ : b != 0) (c : Real) : (l
ogb (a / b) c)⁻¹ = (logb a c)⁻¹ - (logb b c)⁻¹
参数：h₁ : a != 0；h₂ : b != 0；c : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.inv_logb`：inv_logb (a b : Real) : (logb a b)⁻¹ = logb b a
· 使用定理 `Real.logb_div`：logb_div (hx : x != 0) (hy : y != 0) : logb b (x / y) = l
ogb b x - logb b y
-/
theorem inv_logb_div_base {a b : ℝ} (h₁ : a ≠ 0) (h₂ : b ≠ 0) (c : ℝ) :
    (logb (a / b) c)⁻¹ = (logb a c)⁻¹ - (logb b c)⁻¹ := by
  simp_rw [inv_logb]; exact logb_div h₁ h₂
/-
**Real.logb_mul_base** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：logb_mul_base {a b : Real} (h₁ : a != 0) (h₂ : b != 0) (c : Real) : logb (
a * b) c = ((logb a c)⁻¹ + (logb b c)⁻¹)⁻¹
参数：h₁ : a != 0；h₂ : b != 0；c : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.inv_logb_mul_base`：inv_logb_mul_base {a b : Real} (h₁ : a != 0) (h₂
 : b != 0) (c : Real) : (logb (a * b) c)⁻¹ = (logb a c)⁻¹ + (logb b c)⁻¹
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
-/
theorem logb_mul_base {a b : ℝ} (h₁ : a ≠ 0) (h₂ : b ≠ 0) (c : ℝ) :
    logb (a * b) c = ((logb a c)⁻¹ + (logb b c)⁻¹)⁻¹ := by rw [← inv_logb_mul_base h₁ h₂ c, inv_inv]
/-
**Real.logb_div_base** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：logb_div_base {a b : Real} (h₁ : a != 0) (h₂ : b != 0) (c : Real) : logb (
a / b) c = ((logb a c)⁻¹ - (logb b c)⁻¹)⁻¹
参数：h₁ : a != 0；h₂ : b != 0；c : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.inv_logb_div_base`：inv_logb_div_base {a b : Real} (h₁ : a != 0) (h₂
 : b != 0) (c : Real) : (logb (a / b) c)⁻¹ = (logb a c)⁻¹ - (logb b c)⁻¹
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
-/
theorem logb_div_base {a b : ℝ} (h₁ : a ≠ 0) (h₂ : b ≠ 0) (c : ℝ) :
    logb (a / b) c = ((logb a c)⁻¹ - (logb b c)⁻¹)⁻¹ := by rw [← inv_logb_div_base h₁ h₂ c, inv_inv]
/-
**Real.mul_logb** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：mul_logb {a b c : Real} (h₁ : b != 0) (h₂ : b != 1) (h₃ : b != -1) : logb 
a b * logb b c = logb a c
参数：h₁ : b != 0；h₂ : b != 1；h₃ : b != -1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用引理 `div_mul_div_cancel₀`：div_mul_div_cancel₀ (hb : b != 0) : a / b * (b / c)
 = a / c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Real.log_ne_zero`：log_ne_zero {x : Real} : log x != 0 ↔ x != 0 ∧ x != 1 
∧ x != -1
-/
theorem mul_logb {a b c : ℝ} (h₁ : b ≠ 0) (h₂ : b ≠ 1) (h₃ : b ≠ -1) :
    logb a b * logb b c = logb a c := by
  unfold logb
  rw [mul_comm, div_mul_div_cancel₀ (log_ne_zero.mpr ⟨h₁, h₂, h₃⟩)]
/-
**Real.div_logb** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：div_logb {a b c : Real} (h₁ : c != 0) (h₂ : c != 1) (h₃ : c != -1) : logb 
a c / logb b c = logb a b
参数：h₁ : c != 0；h₂ : c != 1；h₃ : c != -1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `div_div_div_cancel_left'`：div_div_div_cancel_left' (a b : G₀) (hc : c !=
 0) : c / a / (c / b) = b / a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Real.log_ne_zero`：log_ne_zero {x : Real} : log x != 0 ↔ x != 0 ∧ x != 1 
∧ x != -1
-/
theorem div_logb {a b c : ℝ} (h₁ : c ≠ 0) (h₂ : c ≠ 1) (h₃ : c ≠ -1) :
    logb a c / logb b c = logb a b :=
  div_div_div_cancel_left' _ _ <| log_ne_zero.mpr ⟨h₁, h₂, h₃⟩
/-
**Real.logb_rpow_eq_mul_logb_of_pos** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：logb_rpow_eq_mul_logb_of_pos (hx : 0 < x) : logb b (x ^ y) = y * logb b x
参数：hx : 0 < x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.logb.eq_1`：∀ (b x : ℝ), Real.logb b x = Real.log x / Real.log b
· 使用定理 `Real.log_rpow`：log_rpow {x : Real} (hx : 0 < x) (y : Real) : log (x ^ y)
 = y * log x
· 使用定理 `mul_div_assoc`：mul_div_assoc (a b c : G) : a * b / c = a * (b / c)
-/
theorem logb_rpow_eq_mul_logb_of_pos (hx : 0 < x) : logb b (x ^ y) = y * logb b x := by
  rw [logb, log_rpow hx, logb, mul_div_assoc]
/-
**Real.logb_pow** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：logb_pow (b x : Real) (k : Nat) : logb b (x ^ k) = k * logb b x
参数：b x : Real；k : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.logb.eq_1`：∀ (b x : ℝ), Real.logb b x = Real.log x / Real.log b
· 使用定理 `Real.log_pow`：log_pow (x : Real) (n : Nat) : log (x ^ n) = n * log x
· 使用定理 `mul_div_assoc`：mul_div_assoc (a b c : G) : a * b / c = a * (b / c)
-/
theorem logb_pow (b x : ℝ) (k : ℕ) : logb b (x ^ k) = k * logb b x := by
  rw [logb, logb, log_pow, mul_div_assoc]

section BPosAndNeOne

variable (b_pos : 0 < b) (b_ne_one : b ≠ 1)
include b_pos b_ne_one

@[simp]
/-
**Real.logb_rpow** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：logb_rpow : logb b (b ^ x) = x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.logb.eq_1`：∀ (b x : ℝ), Real.logb b x = Real.log x / Real.log b
· 使用引理 `div_eq_iff`：div_eq_iff (hb : b != 0) : a / b = c ↔ a = c * b
· 使用定理 `Real.log_ne_zero_of_pos_of_ne_one`：log_ne_zero_of_pos_of_ne_one {x : Rea
l} (hx_pos : 0 < x) (hx : x != 1) : log x != 0
· 使用定理 `Real.log_rpow`：log_rpow {x : Real} (hx : 0 < x) (y : Real) : log (x ^ y)
 = y * log x
-/
theorem logb_rpow : logb b (b ^ x) = x := by
  rw [logb, div_eq_iff, log_rpow b_pos]
  exact log_ne_zero_of_pos_of_ne_one b_pos b_ne_one
/-
**Real.rpow_logb_eq_abs** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：rpow_logb_eq_abs (hx : x != 0) : b ^ logb b x = |x|
参数：hx : x != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.log_injOn_pos`：log_injOn_pos : Set.InjOn log (Set.Ioi 0)
· 使用定理 `Real.rpow_pos_of_pos`：rpow_pos_of_pos {x : Real} (hx : 0 < x) (y : Real)
 : 0 < x ^ y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Real.log_rpow`：log_rpow {x : Real} (hx : 0 < x) (y : Real) : log (x ^ y)
 = y * log x
· 使用定理 `Real.logb.eq_1`：∀ (b x : ℝ), Real.logb b x = Real.log x / Real.log b
· 使用定理 `Real.log_abs`：log_abs (x : Real) : log |x| = log x
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_eq_cancel_eq`：eq_eq_cancel_eq {M : Type*} [M
onoidWithZero M] [IsLeftCancelMulZero M] {e₁ e₂ f₁ f₂ L : M} (H₁ : e₁ = L * f₁) 
(H₂ : e₂ = L * f₂) (HL : L != …
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
· 使用定理 `instIsCancelMulZero`：∀ {G₀ : Type u_2} [inst : GroupWithZero G₀], IsCanc
elMulZero G₀
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_mul_of_eq_eq_eq_mul`：eq_mul_of_eq_eq_eq_mul 
{M : Type*} [Mul M] {a b c D e f : M} (h₁ : a = b) (h₂ : b = c) (h₃ : c = D * e)
 (h₄ : e = f) : a = D * f
· 使用定理 `congr_arg₂`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} (f : α → β → 
γ) {x x' : α} {y y' : β}, x = x' → y = y' → f x y = f x' y'
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.mul_eq_eval`：mul_eq_eval [GroupWithZero M] {
l₁ l₂ l : NF M} {x₁ x₂ : M} (hx₁ : x₁ = l₁.eval) (hx₂ : x₂ = l₂.eval) (h : l₁.ev
al * l₂.eval = l.eval) : x₁ *…
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.div_eq_eval`：div_eq_eval [GroupWithZero M] {
l₁ l₂ l : NF M} {x₁ x₂ : M} (hx₁ : x₁ = l₁.eval) (hx₂ : x₂ = l₂.eval) (h : l₁.ev
al / l₂.eval = l.eval) : x₁ /…
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.atom_eq_eval`：atom_eq_eval [GroupWithZero M]
 (x : M) : x = NF.eval [(1, x)]
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.div_eq_eval₃`：div_eq_eval₃ [CommGroupWithZer
o M] {a₁ : Int × M} (a₂ : Int × M) {l₁ l₂ l : NF M} (h : (a₁ ::ᵣ l₁).eval / l₂.e
val = l.eval) : (a₁ ::ᵣ l₁).ev…
· 使用定理 `div_one`：div_one (a : G) : a / 1 = a
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.mul_eq_eval₂`：mul_eq_eval₂ [CommGroupWithZer
o M] (r₁ r₂ : Int) (x : M) {l₁ l₂ l : NF M} (h : l₁.eval * l₂.eval = l.eval) : (
(r₁, x) ::ᵣ l₁).eval * ((r₂, x…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_mul_eval_cons_zero`：eval_mul_eval_cons_
zero [CommGroupWithZero M] {e : M} {L l l' l₀ : NF M} (h : L.eval * l.eval = l'.
eval) (h' : ((0, e) ::ᵣ l).eval = l₀.eval…
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_mul_eval_cons`：eval_mul_eval_cons [Comm
GroupWithZero M] (n : Int) (e : M) {L l l' : NF M} (h : L.eval * l.eval = l'.eva
l) : L.eval * ((n, e) ::ᵣ l).eval = …
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_cons_of_pow_eq_zero`：eval_cons_of_pow_e
q_zero [CommGroupWithZero M] {r : Int} (hr : r = 0) {x : M} (hx : x != 0) (l : N
F M) : ((r, x) ::ᵣ l).eval = NF.eval l
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用定理 `Real.log_ne_zero_of_pos_of_ne_one`：log_ne_zero_of_pos_of_ne_one {x : Rea
l} (hx_pos : 0 < x) (hx : x != 1) : log x != 0
· 使用定理 `not_false_eq_true`：(¬False) = True
（共 38 条，此处仅展示前 30 条）
-/
theorem rpow_logb_eq_abs (hx : x ≠ 0) : b ^ logb b x = |x| := by
  apply log_injOn_pos
  · simp only [Set.mem_Ioi]
    apply rpow_pos_of_pos b_pos
  · simp only [abs_pos, mem_Ioi, Ne, hx, not_false_iff]
  rw [log_rpow b_pos, logb, log_abs]
  field [log_ne_zero_of_pos_of_ne_one b_pos b_ne_one]

@[simp]
/-
**Real.rpow_logb** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：rpow_logb (hx : 0 < x) : b ^ logb b x = x
参数：hx : 0 < x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.rpow_logb_eq_abs`：rpow_logb_eq_abs (hx : x != 0) : b ^ logb b x = |
x|
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `abs_of_pos`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] {a
 : α} [AddLeftMono α], 0 < a → |a| = a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
-/
theorem rpow_logb (hx : 0 < x) : b ^ logb b x = x := by
  rw [rpow_logb_eq_abs b_pos b_ne_one hx.ne']
  exact abs_of_pos hx
/-
**Real.rpow_logb_of_neg** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：rpow_logb_of_neg (hx : x < 0) : b ^ logb b x = -x
参数：hx : x < 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.rpow_logb_eq_abs`：rpow_logb_eq_abs (hx : x != 0) : b ^ logb b x = |
x|
· 使用引理 `ne_of_lt`：ne_of_lt (h : a < b) : a != b
· 使用定理 `abs_of_neg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] {a
 : α} [AddLeftMono α], a < 0 → |a| = -a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
-/
theorem rpow_logb_of_neg (hx : x < 0) : b ^ logb b x = -x := by
  rw [rpow_logb_eq_abs b_pos b_ne_one (ne_of_lt hx)]
  exact abs_of_neg hx
/-
**Real.logb_eq_iff_rpow_eq** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：logb_eq_iff_rpow_eq (hy : 0 < y) : logb b y = x ↔ b ^ x = y
参数：hy : 0 < y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.rpow_logb`：rpow_logb (hx : 0 < x) : b ^ logb b x = x
· 使用定理 `Real.logb_rpow`：logb_rpow : logb b (b ^ x) = x
-/
theorem logb_eq_iff_rpow_eq (hy : 0 < y) : logb b y = x ↔ b ^ x = y := by
  constructor <;> rintro rfl
  · exact rpow_logb b_pos b_ne_one hy
  · exact logb_rpow b_pos b_ne_one
/-
**Real.surjOn_logb** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：surjOn_logb : SurjOn (logb b) (Ioi 0) univ
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.rpow_pos_of_pos`：rpow_pos_of_pos {x : Real} (hx : 0 < x) (y : Real)
 : 0 < x ^ y
· 使用定理 `Real.logb_rpow`：logb_rpow : logb b (b ^ x) = x
-/
theorem surjOn_logb : SurjOn (logb b) (Ioi 0) univ := fun x _ =>
  ⟨b ^ x, rpow_pos_of_pos b_pos x, logb_rpow b_pos b_ne_one⟩
/-
**Real.logb_surjective** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：logb_surjective : Surjective (logb b)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.logb_rpow`：logb_rpow : logb b (b ^ x) = x
-/
theorem logb_surjective : Surjective (logb b) := fun x => ⟨b ^ x, logb_rpow b_pos b_ne_one⟩

@[simp]
/-
**Real.range_logb** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：range_logb : range (logb b) = univ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Surjective.range_eq`：∀ {α : Type u_1} {ι : Sort u_4} {f : ι → α
}, Function.Surjective f → Set.range f = Set.univ
· 使用定理 `Real.logb_surjective`：logb_surjective : Surjective (logb b)
-/
theorem range_logb : range (logb b) = univ :=
  (logb_surjective b_pos b_ne_one).range_eq
/-
**Real.surjOn_logb'** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：surjOn_logb' : SurjOn (logb b) (Iio 0) univ
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `Real.rpow_pos_of_pos`：rpow_pos_of_pos {x : Real} (hx : 0 < x) (y : Real)
 : 0 < x ^ y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.logb_neg_eq_logb`：logb_neg_eq_logb (b x : Real) : logb b (-x) = log
b b x
· 使用定理 `Real.logb_rpow`：logb_rpow : logb b (b ^ x) = x
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

/-
**Real.b_pos** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem b_pos : 0 < b := by linarith

-- Name has a prime added to avoid clashing with `b_ne_one` further down the file
/-
**Real.b_ne_one'** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem b_ne_one' : b ≠ 1 := by linarith

@[simp]
/-
**Real.logb_le_logb** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：logb_le_logb (h : 0 < x) (h₁ : 0 < y) : logb b x <= logb b y ↔ x <= y
参数：h : 0 < x；h₁ : 0 < y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.logb.eq_1`：∀ (b x : ℝ), Real.logb b x = Real.log x / Real.log b
· 使用引理 `div_le_div_iff_of_pos_right`：div_le_div_iff_of_pos_right (hc : 0 < c) : 
a / c <= b / c ↔ a <= b
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `Real.log_pos`：log_pos (hx : 1 < x) : 0 < log x
· 使用定理 `Real.log_le_log_iff`：log_le_log_iff (h : 0 < x) (h₁ : 0 < y) : log x <= 
log y ↔ x <= y
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem logb_le_logb (h : 0 < x) (h₁ : 0 < y) : logb b x ≤ logb b y ↔ x ≤ y := by
  rw [logb, logb, div_le_div_iff_of_pos_right (log_pos hb), log_le_log_iff h h₁]

@[gcongr]
/-
**Real.logb_le_logb_of_le** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：logb_le_logb_of_le (h : 0 < x) (hxy : x <= y) : logb b x <= logb b y
参数：h : 0 < x；hxy : x <= y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Real.logb_le_logb`：logb_le_logb (h : 0 < x) (h₁ : 0 < y) : logb b x <= l
ogb b y ↔ x <= y
· 使用定理 `lt_of_not_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬b ≤ a 
→ a < b
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_zero`：∀ {R : Type u_1} [inst : CommSemiring R] 
{a : R}, Mathlib.Meta.NormNum.IsNat a 0 → a = 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_mul`：∀ {R : Type u_2} [inst : CommRing R]
 (a₁ : R) (a₂ : ℕ) {a₃ b : R}, -a₃ = b → -(a₁ ^ a₂ * a₃) = a₁ ^ a₂ * b
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℤ} [in
st : Ring α], Mathlib.Meta.NormNum.IsInt a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isInt_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {a' b : ℤ},   f = Neg.neg → Mathlib.Meta.NormNum.IsInt a a' → a'.ne
g = b → Mathlib.Meta…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isInt`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsInt a (
Int.ofNat n)
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_zero`：∀ {R : Type u_2} [inst : CommRing R
], -0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_overlap_zero`：∀ {R : Type u_1} [in
st : CommSemiring R] {a₁ a₂ b₁ b₂ c : R},   Mathlib.Meta.NormNum.IsNat (a₁ + b₁)
 0 → a₂ + b₂ = c → a₁ + a₂ + (b₁ + b₂) =…
· 使用定理 `Mathlib.Tactic.Ring.Common.add_overlap_pf_zero`：∀ {R : Type u_1} [inst :
 CommSemiring R] {a b : R} (x : R) (e : ℕ),   Mathlib.Meta.NormNum.IsNat (a + b)
 0 → Mathlib.Meta.NormNum.IsNat (x ^…
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_isNat`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsInt a (Int.ofNat n) → Mathlib.Meta.NormN
um.IsNat a n
· 使用定理 `Mathlib.Meta.NormNum.isInt_add`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α → α} {a b : α} {a' b' c : ℤ},   f = HAdd.hAdd →     Mathlib.Meta.NormNum.IsI
nt a a' →       Math…
· 使用定理 `Mathlib.Meta.NormNum.IsInt.of_raw`：∀ (α : Type u_1) [inst : Ring α] (n :
 ℤ), Mathlib.Meta.NormNum.IsInt n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Linarith.add_lt_of_neg_of_le`：add_lt_of_neg_of_le [IsStri
ctOrderedRing α] {a b c : α} (ha : a < 0) (hbc : b <= c) : a + b < c
（共 32 条，此处仅展示前 30 条）
-/
theorem logb_le_logb_of_le (h : 0 < x) (hxy : x ≤ y) : logb b x ≤ logb b y :=
  (logb_le_logb hb h (by linarith)).mpr hxy

@[gcongr]
/-
**Real.logb_lt_logb** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：logb_lt_logb (hx : 0 < x) (hxy : x < y) : logb b x < logb b y
参数：hx : 0 < x；hxy : x < y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.logb.eq_1`：∀ (b x : ℝ), Real.logb b x = Real.log x / Real.log b
· 使用引理 `div_lt_div_iff_of_pos_right`：div_lt_div_iff_of_pos_right (hc : 0 < c) : 
a / c < b / c ↔ a < b
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `Real.log_pos`：log_pos (hx : 1 < x) : 0 < log x
· 使用定理 `Real.log_lt_log`：log_lt_log (hx : 0 < x) (h : x < y) : log x < log y
-/
theorem logb_lt_logb (hx : 0 < x) (hxy : x < y) : logb b x < logb b y := by
  rw [logb, logb, div_lt_div_iff_of_pos_right (log_pos hb)]
  exact log_lt_log hx hxy

@[simp]
/-
**Real.logb_lt_logb_iff** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：logb_lt_logb_iff (hx : 0 < x) (hy : 0 < y) : logb b x < logb b y ↔ x < y
参数：hx : 0 < x；hy : 0 < y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.logb.eq_1`：∀ (b x : ℝ), Real.logb b x = Real.log x / Real.log b
· 使用引理 `div_lt_div_iff_of_pos_right`：div_lt_div_iff_of_pos_right (hc : 0 < c) : 
a / c < b / c ↔ a < b
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `Real.log_pos`：log_pos (hx : 1 < x) : 0 < log x
· 使用定理 `Real.log_lt_log_iff`：log_lt_log_iff (hx : 0 < x) (hy : 0 < y) : log x < 
log y ↔ x < y
-/
theorem logb_lt_logb_iff (hx : 0 < x) (hy : 0 < y) : logb b x < logb b y ↔ x < y := by
  rw [logb, logb, div_lt_div_iff_of_pos_right (log_pos hb)]
  exact log_lt_log_iff hx hy
/-
**Real.logb_le_iff_le_rpow** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：logb_le_iff_le_rpow (hx : 0 < x) : logb b x <= y ↔ x <= b ^ y
参数：hx : 0 < x。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.rpow_le_rpow_left_iff`：rpow_le_rpow_left_iff (hx : 1 < x) : x ^ y <
= x ^ z ↔ y <= z
· 使用定理 `Real.rpow_logb`：rpow_logb (hx : 0 < x) : b ^ logb b x = x
· 使用定理 `_private.Mathlib.Analysis.SpecialFunctions.Log.Base.0.Real.b_pos`：∀ {b :
 ℝ}, 1 < b → 0 < b
· 使用定理 `_private.Mathlib.Analysis.SpecialFunctions.Log.Base.0.Real.b_ne_one'`：∀ 
{b : ℝ}, 1 < b → b ≠ 1
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem logb_le_iff_le_rpow (hx : 0 < x) : logb b x ≤ y ↔ x ≤ b ^ y := by
  rw [← rpow_le_rpow_left_iff hb, rpow_logb (b_pos hb) (b_ne_one' hb) hx]
/-
**Real.logb_lt_iff_lt_rpow** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：logb_lt_iff_lt_rpow (hx : 0 < x) : logb b x < y ↔ x < b ^ y
参数：hx : 0 < x。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.rpow_lt_rpow_left_iff`：rpow_lt_rpow_left_iff (hx : 1 < x) : x ^ y <
 x ^ z ↔ y < z
· 使用定理 `Real.rpow_logb`：rpow_logb (hx : 0 < x) : b ^ logb b x = x
· 使用定理 `_private.Mathlib.Analysis.SpecialFunctions.Log.Base.0.Real.b_pos`：∀ {b :
 ℝ}, 1 < b → 0 < b
· 使用定理 `_private.Mathlib.Analysis.SpecialFunctions.Log.Base.0.Real.b_ne_one'`：∀ 
{b : ℝ}, 1 < b → b ≠ 1
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem logb_lt_iff_lt_rpow (hx : 0 < x) : logb b x < y ↔ x < b ^ y := by
  rw [← rpow_lt_rpow_left_iff hb, rpow_logb (b_pos hb) (b_ne_one' hb) hx]
/-
**Real.le_logb_iff_rpow_le** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：le_logb_iff_rpow_le (hy : 0 < y) : x <= logb b y ↔ b ^ x <= y
参数：hy : 0 < y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.rpow_le_rpow_left_iff`：rpow_le_rpow_left_iff (hx : 1 < x) : x ^ y <
= x ^ z ↔ y <= z
· 使用定理 `Real.rpow_logb`：rpow_logb (hx : 0 < x) : b ^ logb b x = x
· 使用定理 `_private.Mathlib.Analysis.SpecialFunctions.Log.Base.0.Real.b_pos`：∀ {b :
 ℝ}, 1 < b → 0 < b
· 使用定理 `_private.Mathlib.Analysis.SpecialFunctions.Log.Base.0.Real.b_ne_one'`：∀ 
{b : ℝ}, 1 < b → b ≠ 1
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem le_logb_iff_rpow_le (hy : 0 < y) : x ≤ logb b y ↔ b ^ x ≤ y := by
  rw [← rpow_le_rpow_left_iff hb, rpow_logb (b_pos hb) (b_ne_one' hb) hy]
/-
**Real.lt_logb_iff_rpow_lt** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：lt_logb_iff_rpow_lt (hy : 0 < y) : x < logb b y ↔ b ^ x < y
参数：hy : 0 < y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.rpow_lt_rpow_left_iff`：rpow_lt_rpow_left_iff (hx : 1 < x) : x ^ y <
 x ^ z ↔ y < z
· 使用定理 `Real.rpow_logb`：rpow_logb (hx : 0 < x) : b ^ logb b x = x
· 使用定理 `_private.Mathlib.Analysis.SpecialFunctions.Log.Base.0.Real.b_pos`：∀ {b :
 ℝ}, 1 < b → 0 < b
· 使用定理 `_private.Mathlib.Analysis.SpecialFunctions.Log.Base.0.Real.b_ne_one'`：∀ 
{b : ℝ}, 1 < b → b ≠ 1
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem lt_logb_iff_rpow_lt (hy : 0 < y) : x < logb b y ↔ b ^ x < y := by
  rw [← rpow_lt_rpow_left_iff hb, rpow_logb (b_pos hb) (b_ne_one' hb) hy]
/-
**Real.logb_pos_iff** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：logb_pos_iff (hx : 0 < x) : 0 < logb b x ↔ 1 < x
参数：hx : 0 < x。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.logb_one`：logb_one : logb b 1 = 0
· 使用定理 `Real.logb_lt_logb_iff`：logb_lt_logb_iff (hx : 0 < x) (hy : 0 < y) : logb
 b x < logb b y ↔ x < y
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem logb_pos_iff (hx : 0 < x) : 0 < logb b x ↔ 1 < x := by
  rw [← @logb_one b]
  rw [logb_lt_logb_iff hb zero_lt_one hx]
/-
**Real.logb_pos** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：logb_pos (hx : 1 < x) : 0 < logb b x
参数：hx : 1 < x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.logb_pos_iff`：logb_pos_iff (hx : 0 < x) : 0 < logb b x ↔ 1 < x
· 使用引理 `lt_trans`：lt_trans : a < b -> b < c -> a < c
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
-/
theorem logb_pos (hx : 1 < x) : 0 < logb b x := by
  rw [logb_pos_iff hb (lt_trans zero_lt_one hx)]
  exact hx
/-
**Real.logb_neg_iff** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：logb_neg_iff (h : 0 < x) : logb b x < 0 ↔ x < 1
参数：h : 0 < x。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.logb_one`：logb_one : logb b 1 = 0
· 使用定理 `Real.logb_lt_logb_iff`：logb_lt_logb_iff (hx : 0 < x) (hy : 0 < y) : logb
 b x < logb b y ↔ x < y
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
-/
theorem logb_neg_iff (h : 0 < x) : logb b x < 0 ↔ x < 1 := by
  rw [← logb_one]
  exact logb_lt_logb_iff hb h zero_lt_one
/-
**Real.logb_neg** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：logb_neg (h0 : 0 < x) (h1 : x < 1) : logb b x < 0
参数：h0 : 0 < x；h1 : x < 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Real.logb_neg_iff`：logb_neg_iff (h : 0 < x) : logb b x < 0 ↔ x < 1
-/
theorem logb_neg (h0 : 0 < x) (h1 : x < 1) : logb b x < 0 :=
  (logb_neg_iff hb h0).2 h1
/-
**Real.logb_nonneg_iff** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：logb_nonneg_iff (hx : 0 < x) : 0 <= logb b x ↔ 1 <= x
参数：hx : 0 < x。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `not_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a < b ↔ b ≤ 
a
· 使用定理 `Real.logb_neg_iff`：logb_neg_iff (h : 0 < x) : logb b x < 0 ↔ x < 1
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem logb_nonneg_iff (hx : 0 < x) : 0 ≤ logb b x ↔ 1 ≤ x := by
  rw [← not_lt, logb_neg_iff hb hx, not_lt]
/-
**Real.logb_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：logb_nonneg (hx : 1 <= x) : 0 <= logb b x
参数：hx : 1 <= x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Real.logb_nonneg_iff`：logb_nonneg_iff (hx : 0 < x) : 0 <= logb b x ↔ 1 <
= x
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
-/
theorem logb_nonneg (hx : 1 ≤ x) : 0 ≤ logb b x :=
  (logb_nonneg_iff hb (zero_lt_one.trans_le hx)).2 hx
/-
**Real.logb_nonpos_iff** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：logb_nonpos_iff (hx : 0 < x) : logb b x <= 0 ↔ x <= 1
参数：hx : 0 < x。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `not_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a < b ↔ b ≤ 
a
· 使用定理 `Real.logb_pos_iff`：logb_pos_iff (hx : 0 < x) : 0 < logb b x ↔ 1 < x
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem logb_nonpos_iff (hx : 0 < x) : logb b x ≤ 0 ↔ x ≤ 1 := by
  rw [← not_lt, logb_pos_iff hb hx, not_lt]
/-
**Real.logb_nonpos_iff'** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：logb_nonpos_iff' (hx : 0 <= x) : logb b x <= 0 ↔ x <= 1
参数：hx : 0 <= x。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.eq_or_lt`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a = b ∨ a < b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Real.logb_zero`：logb_zero : logb b 0 = 0
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Real.logb_nonpos_iff`：logb_nonpos_iff (hx : 0 < x) : logb b x <= 0 ↔ x <
= 1
-/
theorem logb_nonpos_iff' (hx : 0 ≤ x) : logb b x ≤ 0 ↔ x ≤ 1 := by
  rcases hx.eq_or_lt with (rfl | hx)
  · simp [zero_le_one]
  exact logb_nonpos_iff hb hx
/-
**Real.logb_nonpos** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：logb_nonpos (hx : 0 <= x) (h'x : x <= 1) : logb b x <= 0
参数：hx : 0 <= x；h'x : x <= 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Real.logb_nonpos_iff'`：logb_nonpos_iff' (hx : 0 <= x) : logb b x <= 0 ↔ 
x <= 1
-/
theorem logb_nonpos (hx : 0 ≤ x) (h'x : x ≤ 1) : logb b x ≤ 0 :=
  (logb_nonpos_iff' hb hx).2 h'x
/-
**Real.strictMonoOn_logb** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：strictMonoOn_logb : StrictMonoOn (logb b) (Set.Ioi 0)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.logb_lt_logb`：logb_lt_logb (hx : 0 < x) (hxy : x < y) : logb b x < 
logb b y
-/
theorem strictMonoOn_logb : StrictMonoOn (logb b) (Set.Ioi 0) := fun _ hx _ _ hxy =>
  logb_lt_logb hb hx hxy
/-
**Real.strictAntiOn_logb** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：strictAntiOn_logb : StrictAntiOn (logb b) (Set.Iio 0)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.logb_abs`：logb_abs (b x : Real) : logb b |x| = logb b x
· 使用定理 `Real.logb_lt_logb`：logb_lt_logb (hx : 0 < x) (hxy : x < y) : logb b x < 
logb b y
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `abs_pos`：∀ {α : Type u_1} [inst : AddGroup α] [inst_1 : LinearOrder α] [
AddLeftMono α] {a : α}, 0 < |a| ↔ a ≠ 0
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `abs_of_neg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] {a
 : α} [AddLeftMono α], a < 0 → |a| = -a
· 使用定理 `neg_lt_neg_iff`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [AddL
eftStrictMono α] {a b : α} [AddRightStrictMono α],   -a < -b ↔ b < a
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
-/
theorem strictAntiOn_logb : StrictAntiOn (logb b) (Set.Iio 0) := by
  rintro x (hx : x < 0) y (hy : y < 0) hxy
  rw [← logb_abs b y, ← logb_abs b x]
  refine logb_lt_logb hb (abs_pos.2 hy.ne) ?_
  rwa [abs_of_neg hy, abs_of_neg hx, neg_lt_neg_iff]
/-
**Real.logb_injOn_pos** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：logb_injOn_pos : Set.InjOn (logb b) (Set.Ioi 0)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `StrictMonoOn.injOn`：StrictMonoOn.injOn (hf : StrictMonoOn f s) : s.InjOn
 f
· 使用定理 `Real.strictMonoOn_logb`：strictMonoOn_logb : StrictMonoOn (logb b) (Set.I
oi 0)
-/
theorem logb_injOn_pos : Set.InjOn (logb b) (Set.Ioi 0) :=
  (strictMonoOn_logb hb).injOn
/-
**Real.eq_one_of_pos_of_logb_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：eq_one_of_pos_of_logb_eq_zero (h₁ : 0 < x) (h₂ : logb b x = 0) : x = 1
参数：h₁ : 0 < x；h₂ : logb b x = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.logb_injOn_pos`：logb_injOn_pos : Set.InjOn (logb b) (Set.Ioi 0)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.mem_Ioi`：∀ {α : Type u_1} [inst : Preorder α] {b x : α}, x ∈ Set.Ioi
 b ↔ b < x
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.logb_one`：logb_one : logb b 1 = 0
-/
theorem eq_one_of_pos_of_logb_eq_zero (h₁ : 0 < x) (h₂ : logb b x = 0) : x = 1 :=
  logb_injOn_pos hb (Set.mem_Ioi.2 h₁) (Set.mem_Ioi.2 zero_lt_one) (h₂.trans Real.logb_one.symm)
/-
**Real.logb_ne_zero_of_pos_of_ne_one** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：logb_ne_zero_of_pos_of_ne_one (hx_pos : 0 < x) (hx : x != 1) : logb b x !=
 0
参数：hx_pos : 0 < x；hx : x != 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Real.eq_one_of_pos_of_logb_eq_zero`：eq_one_of_pos_of_logb_eq_zero (h₁ : 
0 < x) (h₂ : logb b x = 0) : x = 1
-/
theorem logb_ne_zero_of_pos_of_ne_one (hx_pos : 0 < x) (hx : x ≠ 1) : logb b x ≠ 0 :=
  mt (eq_one_of_pos_of_logb_eq_zero hb hx_pos) hx
/-
**Real.tendsto_logb_atTop** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：tendsto_logb_atTop : Tendsto (logb b) atTop atTop
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.atTop_div_const`：∀ {α : Type u_1} {β : Type u_2} [inst : 
Semifield α] [inst_1 : LinearOrder α] [IsStrictOrderedRing α] {l : Filter β}   {
f : β → α} {r : α}, …
· 使用定理 `Real.log_pos`：log_pos (hx : 1 < x) : 0 < log x
· 使用定理 `Real.tendsto_log_atTop`：tendsto_log_atTop : Tendsto log atTop atTop
-/
theorem tendsto_logb_atTop : Tendsto (logb b) atTop atTop :=
  Tendsto.atTop_div_const (log_pos hb) tendsto_log_atTop

end OneLtB

section BPosAndBLtOne

variable (b_pos : 0 < b) (b_lt_one : b < 1)
include b_lt_one

/-
**Real.b_ne_one** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem b_ne_one : b ≠ 1 := by linarith

include b_pos

@[simp]
/-
**Real.logb_le_logb_of_base_lt_one** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：logb_le_logb_of_base_lt_one (h : 0 < x) (h₁ : 0 < y) : logb b x <= logb b 
y ↔ y <= x
参数：h : 0 < x；h₁ : 0 < y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.logb.eq_1`：∀ (b x : ℝ), Real.logb b x = Real.log x / Real.log b
· 使用定理 `div_le_div_right_of_neg`：div_le_div_right_of_neg (hc : c < 0) : a / c <=
 b / c ↔ b <= a
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Real.log_neg`：log_neg (h0 : 0 < x) (h1 : x < 1) : log x < 0
· 使用定理 `Real.log_le_log_iff`：log_le_log_iff (h : 0 < x) (h₁ : 0 < y) : log x <= 
log y ↔ x <= y
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem logb_le_logb_of_base_lt_one (h : 0 < x) (h₁ : 0 < y) : logb b x ≤ logb b y ↔ y ≤ x := by
  rw [logb, logb, div_le_div_right_of_neg (log_neg b_pos b_lt_one), log_le_log_iff h₁ h]
/-
**Real.logb_lt_logb_of_base_lt_one** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：logb_lt_logb_of_base_lt_one (hx : 0 < x) (hxy : x < y) : logb b y < logb b
 x
参数：hx : 0 < x；hxy : x < y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.logb.eq_1`：∀ (b x : ℝ), Real.logb b x = Real.log x / Real.log b
· 使用定理 `div_lt_div_right_of_neg`：div_lt_div_right_of_neg (hc : c < 0) : a / c < 
b / c ↔ b < a
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Real.log_neg`：log_neg (h0 : 0 < x) (h1 : x < 1) : log x < 0
· 使用定理 `Real.log_lt_log`：log_lt_log (hx : 0 < x) (h : x < y) : log x < log y
-/
theorem logb_lt_logb_of_base_lt_one (hx : 0 < x) (hxy : x < y) : logb b y < logb b x := by
  rw [logb, logb, div_lt_div_right_of_neg (log_neg b_pos b_lt_one)]
  exact log_lt_log hx hxy

@[simp]
/-
**Real.logb_lt_logb_iff_of_base_lt_one** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：logb_lt_logb_iff_of_base_lt_one (hx : 0 < x) (hy : 0 < y) : logb b x < log
b b y ↔ y < x
参数：hx : 0 < x；hy : 0 < y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.logb.eq_1`：∀ (b x : ℝ), Real.logb b x = Real.log x / Real.log b
· 使用定理 `div_lt_div_right_of_neg`：div_lt_div_right_of_neg (hc : c < 0) : a / c < 
b / c ↔ b < a
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Real.log_neg`：log_neg (h0 : 0 < x) (h1 : x < 1) : log x < 0
· 使用定理 `Real.log_lt_log_iff`：log_lt_log_iff (hx : 0 < x) (hy : 0 < y) : log x < 
log y ↔ x < y
-/
theorem logb_lt_logb_iff_of_base_lt_one (hx : 0 < x) (hy : 0 < y) :
    logb b x < logb b y ↔ y < x := by
  rw [logb, logb, div_lt_div_right_of_neg (log_neg b_pos b_lt_one)]
  exact log_lt_log_iff hy hx
/-
**Real.logb_le_iff_le_rpow_of_base_lt_one** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：logb_le_iff_le_rpow_of_base_lt_one (hx : 0 < x) : logb b x <= y ↔ b ^ y <=
 x
参数：hx : 0 < x。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.rpow_le_rpow_left_iff_of_base_lt_one`：rpow_le_rpow_left_iff_of_base
_lt_one (hx0 : 0 < x) (hx1 : x < 1) : x ^ y <= x ^ z ↔ z <= y
· 使用定理 `Real.rpow_logb`：rpow_logb (hx : 0 < x) : b ^ logb b x = x
· 使用定理 `_private.Mathlib.Analysis.SpecialFunctions.Log.Base.0.Real.b_ne_one`：∀ {
b : ℝ}, b < 1 → b ≠ 1
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem logb_le_iff_le_rpow_of_base_lt_one (hx : 0 < x) : logb b x ≤ y ↔ b ^ y ≤ x := by
  rw [← rpow_le_rpow_left_iff_of_base_lt_one b_pos b_lt_one, rpow_logb b_pos (b_ne_one b_lt_one) hx]
/-
**Real.logb_lt_iff_lt_rpow_of_base_lt_one** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：logb_lt_iff_lt_rpow_of_base_lt_one (hx : 0 < x) : logb b x < y ↔ b ^ y < x
参数：hx : 0 < x。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.rpow_lt_rpow_left_iff_of_base_lt_one`：rpow_lt_rpow_left_iff_of_base
_lt_one (hx0 : 0 < x) (hx1 : x < 1) : x ^ y < x ^ z ↔ z < y
· 使用定理 `Real.rpow_logb`：rpow_logb (hx : 0 < x) : b ^ logb b x = x
· 使用定理 `_private.Mathlib.Analysis.SpecialFunctions.Log.Base.0.Real.b_ne_one`：∀ {
b : ℝ}, b < 1 → b ≠ 1
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem logb_lt_iff_lt_rpow_of_base_lt_one (hx : 0 < x) : logb b x < y ↔ b ^ y < x := by
  rw [← rpow_lt_rpow_left_iff_of_base_lt_one b_pos b_lt_one, rpow_logb b_pos (b_ne_one b_lt_one) hx]
/-
**Real.le_logb_iff_rpow_le_of_base_lt_one** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：le_logb_iff_rpow_le_of_base_lt_one (hy : 0 < y) : x <= logb b y ↔ y <= b ^
 x
参数：hy : 0 < y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.rpow_le_rpow_left_iff_of_base_lt_one`：rpow_le_rpow_left_iff_of_base
_lt_one (hx0 : 0 < x) (hx1 : x < 1) : x ^ y <= x ^ z ↔ z <= y
· 使用定理 `Real.rpow_logb`：rpow_logb (hx : 0 < x) : b ^ logb b x = x
· 使用定理 `_private.Mathlib.Analysis.SpecialFunctions.Log.Base.0.Real.b_ne_one`：∀ {
b : ℝ}, b < 1 → b ≠ 1
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem le_logb_iff_rpow_le_of_base_lt_one (hy : 0 < y) : x ≤ logb b y ↔ y ≤ b ^ x := by
  rw [← rpow_le_rpow_left_iff_of_base_lt_one b_pos b_lt_one, rpow_logb b_pos (b_ne_one b_lt_one) hy]
/-
**Real.lt_logb_iff_rpow_lt_of_base_lt_one** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：lt_logb_iff_rpow_lt_of_base_lt_one (hy : 0 < y) : x < logb b y ↔ y < b ^ x
参数：hy : 0 < y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.rpow_lt_rpow_left_iff_of_base_lt_one`：rpow_lt_rpow_left_iff_of_base
_lt_one (hx0 : 0 < x) (hx1 : x < 1) : x ^ y < x ^ z ↔ z < y
· 使用定理 `Real.rpow_logb`：rpow_logb (hx : 0 < x) : b ^ logb b x = x
· 使用定理 `_private.Mathlib.Analysis.SpecialFunctions.Log.Base.0.Real.b_ne_one`：∀ {
b : ℝ}, b < 1 → b ≠ 1
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem lt_logb_iff_rpow_lt_of_base_lt_one (hy : 0 < y) : x < logb b y ↔ y < b ^ x := by
  rw [← rpow_lt_rpow_left_iff_of_base_lt_one b_pos b_lt_one, rpow_logb b_pos (b_ne_one b_lt_one) hy]
/-
**Real.logb_pos_iff_of_base_lt_one** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：logb_pos_iff_of_base_lt_one (hx : 0 < x) : 0 < logb b x ↔ x < 1
参数：hx : 0 < x。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.logb_one`：logb_one : logb b 1 = 0
· 使用定理 `Real.logb_lt_logb_iff_of_base_lt_one`：logb_lt_logb_iff_of_base_lt_one (h
x : 0 < x) (hy : 0 < y) : logb b x < logb b y ↔ y < x
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem logb_pos_iff_of_base_lt_one (hx : 0 < x) : 0 < logb b x ↔ x < 1 := by
  rw [← @logb_one b, logb_lt_logb_iff_of_base_lt_one b_pos b_lt_one zero_lt_one hx]
/-
**Real.logb_pos_of_base_lt_one** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：logb_pos_of_base_lt_one (hx : 0 < x) (hx' : x < 1) : 0 < logb b x
参数：hx : 0 < x；hx' : x < 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.logb_pos_iff_of_base_lt_one`：logb_pos_iff_of_base_lt_one (hx : 0 < 
x) : 0 < logb b x ↔ x < 1
-/
theorem logb_pos_of_base_lt_one (hx : 0 < x) (hx' : x < 1) : 0 < logb b x := by
  rw [logb_pos_iff_of_base_lt_one b_pos b_lt_one hx]
  exact hx'
/-
**Real.logb_neg_iff_of_base_lt_one** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：logb_neg_iff_of_base_lt_one (h : 0 < x) : logb b x < 0 ↔ 1 < x
参数：h : 0 < x。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.logb_one`：logb_one : logb b 1 = 0
· 使用定理 `Real.logb_lt_logb_iff_of_base_lt_one`：logb_lt_logb_iff_of_base_lt_one (h
x : 0 < x) (hy : 0 < y) : logb b x < logb b y ↔ y < x
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem logb_neg_iff_of_base_lt_one (h : 0 < x) : logb b x < 0 ↔ 1 < x := by
  rw [← @logb_one b, logb_lt_logb_iff_of_base_lt_one b_pos b_lt_one h zero_lt_one]
/-
**Real.logb_neg_of_base_lt_one** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：logb_neg_of_base_lt_one (h1 : 1 < x) : logb b x < 0
参数：h1 : 1 < x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Real.logb_neg_iff_of_base_lt_one`：logb_neg_iff_of_base_lt_one (h : 0 < x
) : logb b x < 0 ↔ 1 < x
· 使用引理 `lt_trans`：lt_trans : a < b -> b < c -> a < c
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
-/
theorem logb_neg_of_base_lt_one (h1 : 1 < x) : logb b x < 0 :=
  (logb_neg_iff_of_base_lt_one b_pos b_lt_one (lt_trans zero_lt_one h1)).2 h1
/-
**Real.logb_nonneg_iff_of_base_lt_one** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：logb_nonneg_iff_of_base_lt_one (hx : 0 < x) : 0 <= logb b x ↔ x <= 1
参数：hx : 0 < x。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `not_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a < b ↔ b ≤ 
a
· 使用定理 `Real.logb_neg_iff_of_base_lt_one`：logb_neg_iff_of_base_lt_one (h : 0 < x
) : logb b x < 0 ↔ 1 < x
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem logb_nonneg_iff_of_base_lt_one (hx : 0 < x) : 0 ≤ logb b x ↔ x ≤ 1 := by
  rw [← not_lt, logb_neg_iff_of_base_lt_one b_pos b_lt_one hx, not_lt]
/-
**Real.logb_nonneg_of_base_lt_one** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：logb_nonneg_of_base_lt_one (hx : 0 < x) (hx' : x <= 1) : 0 <= logb b x
参数：hx : 0 < x；hx' : x <= 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.logb_nonneg_iff_of_base_lt_one`：logb_nonneg_iff_of_base_lt_one (hx 
: 0 < x) : 0 <= logb b x ↔ x <= 1
-/
theorem logb_nonneg_of_base_lt_one (hx : 0 < x) (hx' : x ≤ 1) : 0 ≤ logb b x := by
  rw [logb_nonneg_iff_of_base_lt_one b_pos b_lt_one hx]
  exact hx'
/-
**Real.logb_nonpos_iff_of_base_lt_one** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：logb_nonpos_iff_of_base_lt_one (hx : 0 < x) : logb b x <= 0 ↔ 1 <= x
参数：hx : 0 < x。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `not_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a < b ↔ b ≤ 
a
· 使用定理 `Real.logb_pos_iff_of_base_lt_one`：logb_pos_iff_of_base_lt_one (hx : 0 < 
x) : 0 < logb b x ↔ x < 1
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem logb_nonpos_iff_of_base_lt_one (hx : 0 < x) : logb b x ≤ 0 ↔ 1 ≤ x := by
  rw [← not_lt, logb_pos_iff_of_base_lt_one b_pos b_lt_one hx, not_lt]
/-
**Real.strictAntiOn_logb_of_base_lt_one** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：strictAntiOn_logb_of_base_lt_one : StrictAntiOn (logb b) (Set.Ioi 0)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.logb_lt_logb_of_base_lt_one`：logb_lt_logb_of_base_lt_one (hx : 0 < 
x) (hxy : x < y) : logb b y < logb b x
-/
theorem strictAntiOn_logb_of_base_lt_one : StrictAntiOn (logb b) (Set.Ioi 0) := fun _ hx _ _ hxy =>
  logb_lt_logb_of_base_lt_one b_pos b_lt_one hx hxy
/-
**Real.strictMonoOn_logb_of_base_lt_one** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：strictMonoOn_logb_of_base_lt_one : StrictMonoOn (logb b) (Set.Iio 0)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.logb_abs`：logb_abs (b x : Real) : logb b |x| = logb b x
· 使用定理 `Real.logb_lt_logb_of_base_lt_one`：logb_lt_logb_of_base_lt_one (hx : 0 < 
x) (hxy : x < y) : logb b y < logb b x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `abs_pos`：∀ {α : Type u_1} [inst : AddGroup α] [inst_1 : LinearOrder α] [
AddLeftMono α] {a : α}, 0 < |a| ↔ a ≠ 0
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `abs_of_neg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] {a
 : α} [AddLeftMono α], a < 0 → |a| = -a
· 使用定理 `neg_lt_neg_iff`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [AddL
eftStrictMono α] {a b : α} [AddRightStrictMono α],   -a < -b ↔ b < a
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
-/
theorem strictMonoOn_logb_of_base_lt_one : StrictMonoOn (logb b) (Set.Iio 0) := by
  rintro x (hx : x < 0) y (hy : y < 0) hxy
  rw [← logb_abs b y, ← logb_abs b x]
  refine logb_lt_logb_of_base_lt_one b_pos b_lt_one (abs_pos.2 hy.ne) ?_
  rwa [abs_of_neg hy, abs_of_neg hx, neg_lt_neg_iff]
/-
**Real.logb_injOn_pos_of_base_lt_one** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：logb_injOn_pos_of_base_lt_one : Set.InjOn (logb b) (Set.Ioi 0)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `StrictAntiOn.injOn`：StrictAntiOn.injOn (hf : StrictAntiOn f s) : s.InjOn
 f
· 使用定理 `Real.strictAntiOn_logb_of_base_lt_one`：strictAntiOn_logb_of_base_lt_one 
: StrictAntiOn (logb b) (Set.Ioi 0)
-/
theorem logb_injOn_pos_of_base_lt_one : Set.InjOn (logb b) (Set.Ioi 0) :=
  (strictAntiOn_logb_of_base_lt_one b_pos b_lt_one).injOn
/-
**Real.eq_one_of_pos_of_logb_eq_zero_of_base_lt_one** 是 Mathlib 中的一个定理，位于命名空间 `R
eal`。
形式化陈述：eq_one_of_pos_of_logb_eq_zero_of_base_lt_one (h₁ : 0 < x) (h₂ : logb b x =
 0) : x = 1
参数：h₁ : 0 < x；h₂ : logb b x = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.logb_injOn_pos_of_base_lt_one`：logb_injOn_pos_of_base_lt_one : Set.
InjOn (logb b) (Set.Ioi 0)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.mem_Ioi`：∀ {α : Type u_1} [inst : Preorder α] {b x : α}, x ∈ Set.Ioi
 b ↔ b < x
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.logb_one`：logb_one : logb b 1 = 0
-/
theorem eq_one_of_pos_of_logb_eq_zero_of_base_lt_one (h₁ : 0 < x) (h₂ : logb b x = 0) : x = 1 :=
  logb_injOn_pos_of_base_lt_one b_pos b_lt_one (Set.mem_Ioi.2 h₁) (Set.mem_Ioi.2 zero_lt_one)
    (h₂.trans Real.logb_one.symm)
/-
**Real.logb_ne_zero_of_pos_of_ne_one_of_base_lt_one** 是 Mathlib 中的一个定理，位于命名空间 `R
eal`。
形式化陈述：logb_ne_zero_of_pos_of_ne_one_of_base_lt_one (hx_pos : 0 < x) (hx : x != 1
) : logb b x != 0
参数：hx_pos : 0 < x；hx : x != 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Real.eq_one_of_pos_of_logb_eq_zero_of_base_lt_one`：eq_one_of_pos_of_logb
_eq_zero_of_base_lt_one (h₁ : 0 < x) (h₂ : logb b x = 0) : x = 1
-/
theorem logb_ne_zero_of_pos_of_ne_one_of_base_lt_one (hx_pos : 0 < x) (hx : x ≠ 1) : logb b x ≠ 0 :=
  mt (eq_one_of_pos_of_logb_eq_zero_of_base_lt_one b_pos b_lt_one hx_pos) hx
/-
**Real.tendsto_logb_atTop_of_base_lt_one** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：tendsto_logb_atTop_of_base_lt_one : Tendsto (logb b) atTop atBot
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.tendsto_atTop_atBot`：tendsto_atTop_atBot : Tendsto f atTop atBot 
↔ forall b : β, exists i : α, forall a : α, i <= a -> f a <= b
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Real.logb_le_iff_le_rpow_of_base_lt_one`：logb_le_iff_le_rpow_of_base_lt_
one (hx : 0 < x) : logb b x <= y ↔ b ^ y <= x
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
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
/-
**Real.floor_logb_natCast** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：floor_logb_natCast {b : Nat} {r : Real} (hr : 0 <= r) : ⌊logb b r⌋ = Int.l
og b r
参数：hr : 0 <= r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.eq_or_lt`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a = b ∨ a < b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.logb_zero`：logb_zero : logb b 0 = 0
· 使用定理 `Int.log_zero_right`：log_zero_right (b : Nat) : log b (0 : R) = 0
· 使用定理 `Int.floor_zero`：floor_zero : ⌊(0 : R)⌋ = 0
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.one_lt_cast`：one_lt_cast : 1 < (n : α) ↔ 1 < n
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Int.zpow_le_iff_le_log`：zpow_le_iff_le_log {b : Nat} (hb : 1 < b) {x : I
nt} {r : R} (hr : 0 < r) : (b : R) ^ x <= r ↔ x <= log b r
· 使用定理 `Real.rpow_intCast`：rpow_intCast (x : Real) (n : Int) : x ^ (n : Real) = 
x ^ n
· 使用定理 `le_of_le_of_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `Real.rpow_le_rpow_of_exponent_le`：rpow_le_rpow_of_exponent_le (hx : 1 <=
 x) (hyz : y <= z) : x ^ y <= x ^ z
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Int.floor_le`：floor_le (a : α) : (⌊a⌋ : α) <= a
· 使用定理 `Real.rpow_logb`：rpow_logb (hx : 0 < x) : b ^ logb b x = x
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Int.le_floor`：le_floor : z <= ⌊a⌋ ↔ (z : α) <= a
· 使用定理 `Real.le_logb_iff_rpow_le`：le_logb_iff_rpow_le (hy : 0 < y) : x <= logb b
 y ↔ b ^ x <= y
· 使用定理 `Int.zpow_log_le_self`：zpow_log_le_self {b : Nat} {r : R} (hb : 1 < b) (h
r : 0 < r) : (b : R) ^ log b r <= r
· 使用定理 `or_iff_not_and_not`：or_iff_not_and_not : a ∨ b ↔ ¬(¬a ∧ ¬b)
· 使用定理 `Nat.one_lt_iff_ne_zero_and_ne_one`：∀ {n : ℕ}, 1 < n ↔ n ≠ 0 ∧ n ≠ 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
（共 37 条，此处仅展示前 30 条）
-/
theorem floor_logb_natCast {b : ℕ} {r : ℝ} (hr : 0 ≤ r) :
    ⌊logb b r⌋ = Int.log b r := by
  obtain rfl | hr := hr.eq_or_lt
  · rw [logb_zero, Int.log_zero_right, Int.floor_zero]
  by_cases hb : 1 < b
  · have hb1' : 1 < (b : ℝ) := Nat.one_lt_cast.mpr hb
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
/-
**Real.ceil_logb_natCast** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：ceil_logb_natCast {b : Nat} {r : Real} (hr : 0 <= r) : ⌈logb b r⌉ = Int.cl
og b r
参数：hr : 0 <= r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.eq_or_lt`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a = b ∨ a < b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.logb_zero`：logb_zero : logb b 0 = 0
· 使用定理 `Int.clog_zero_right`：clog_zero_right (b : Nat) : clog b (0 : R) = 0
· 使用定理 `Int.ceil_zero`：ceil_zero : ⌈(0 : R)⌉ = 0
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.one_lt_cast`：one_lt_cast : 1 < (n : α) ↔ 1 < n
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Int.ceil_le`：ceil_le : ⌈a⌉ <= z ↔ a <= z
· 使用定理 `Real.logb_le_iff_le_rpow`：logb_le_iff_le_rpow (hx : 0 < x) : logb b x <=
 y ↔ x <= b ^ y
· 使用定理 `Real.rpow_intCast`：rpow_intCast (x : Real) (n : Int) : x ^ (n : Real) = 
x ^ n
· 使用定理 `Int.self_le_zpow_clog`：self_le_zpow_clog {b : Nat} (hb : 1 < b) (r : R) 
: r <= (b : R) ^ clog b r
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Int.le_zpow_iff_clog_le`：le_zpow_iff_clog_le {b : Nat} (hb : 1 < b) {x :
 Int} {r : R} (hr : 0 < r) : r <= (b : R) ^ x ↔ clog b r <= x
· 使用定理 `Eq.trans_le`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a = b → b ≤ c →
 a ≤ c
· 使用定理 `Real.rpow_logb`：rpow_logb (hx : 0 < x) : b ^ logb b x = x
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Real.rpow_le_rpow_of_exponent_le`：rpow_le_rpow_of_exponent_le (hx : 1 <=
 x) (hyz : y <= z) : x ^ y <= x ^ z
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Int.le_ceil`：le_ceil (a : α) : a <= ⌈a⌉
· 使用定理 `or_iff_not_and_not`：or_iff_not_and_not : a ∨ b ↔ ¬(¬a ∧ ¬b)
· 使用定理 `Nat.one_lt_iff_ne_zero_and_ne_one`：∀ {n : ℕ}, 1 < n ↔ n ≠ 0 ∧ n ≠ 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
（共 37 条，此处仅展示前 30 条）
-/
theorem ceil_logb_natCast {b : ℕ} {r : ℝ} (hr : 0 ≤ r) :
    ⌈logb b r⌉ = Int.clog b r := by
  obtain rfl | hr := hr.eq_or_lt
  · rw [logb_zero, Int.clog_zero_right, Int.ceil_zero]
  by_cases hb : 1 < b
  · have hb1' : 1 < (b : ℝ) := Nat.one_lt_cast.mpr hb
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
/-
**Real.natFloor_logb_natCast** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：natFloor_logb_natCast (b : Nat) (n : Nat) : ⌊logb b n⌋₊ = Nat.log b n
参数：b : Nat；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CharP.cast_eq_zero`：∀ (R : Type u_1) [inst : AddMonoidWithOne R] (p : ℕ)
 [CharP R p], ↑p = 0
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Real.log_zero`：log_zero : log 0 = 0
· 使用定理 `div_zero`：div_zero (a : G₀) : a / 0 = 0
· 使用定理 `Nat.floor_zero`：floor_zero : ⌊(0 : R)⌋₊ = 0
· 使用定理 `Nat.log_zero_left`：∀ (n : ℕ), Nat.log 0 n = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Real.log_one`：log_one : log 1 = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.log_one_left`：log_one_left : forall n, log 1 n = 0
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Real.logb_zero`：logb_zero : logb b 0 = 0
· 使用定理 `Nat.log_zero_right`：log_zero_right (b : Nat) : log b 0 = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_inj`：cast_inj {m n : Nat} : (m : R) = n ↔ m = n
· 使用定理 `Int.natCast_floor_eq_floor`：Int.natCast_floor_eq_floor (ha : 0 <= a) : (
⌊a⌋₊ : Int) = ⌊a⌋
· 使用定理 `Real.logb_nonneg`：logb_nonneg (hx : 1 <= x) : 0 <= logb b x
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
（共 36 条，此处仅展示前 30 条）
-/
theorem natFloor_logb_natCast (b : ℕ) (n : ℕ) : ⌊logb b n⌋₊ = Nat.log b n := by
  obtain _ | _ | b := b
  · simp [Real.logb]
  · simp [Real.logb]
  obtain rfl | hn := eq_or_ne n 0
  · simp
  rw [← Nat.cast_inj (R := ℤ), Int.natCast_floor_eq_floor, floor_logb_natCast (by simp),
    Int.log_natCast]
  exact logb_nonneg (by simp [Nat.cast_add_one_pos]) (Nat.one_le_cast.2 (by lia))

@[norm_cast]
/-
**Real.natCeil_logb_natCast** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：natCeil_logb_natCast (b : Nat) (n : Nat) : ⌈logb b n⌉₊ = Nat.clog b n
参数：b : Nat；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CharP.cast_eq_zero`：∀ (R : Type u_1) [inst : AddMonoidWithOne R] (p : ℕ)
 [CharP R p], ↑p = 0
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Real.log_zero`：log_zero : log 0 = 0
· 使用定理 `div_zero`：div_zero (a : G₀) : a / 0 = 0
· 使用定理 `Nat.ceil_zero`：ceil_zero : ⌈(0 : R)⌉₊ = 0
· 使用定理 `Nat.clog_zero_left`：∀ (n : ℕ), Nat.clog 0 n = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Real.log_one`：log_one : log 1 = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.clog_one_left`：clog_one_left (n : Nat) : clog 1 n = 0
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Real.logb_zero`：logb_zero : logb b 0 = 0
· 使用定理 `Nat.clog_zero_right`：∀ (b : ℕ), Nat.clog b 0 = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_inj`：cast_inj {m n : Nat} : (m : R) = n ↔ m = n
· 使用定理 `Int.natCast_ceil_eq_ceil`：Int.natCast_ceil_eq_ceil (ha : 0 <= a) : (⌈a⌉₊
 : Int) = ⌈a⌉
· 使用定理 `Real.logb_nonneg`：logb_nonneg (hx : 1 <= x) : 0 <= logb b x
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
（共 36 条，此处仅展示前 30 条）
-/
theorem natCeil_logb_natCast (b : ℕ) (n : ℕ) : ⌈logb b n⌉₊ = Nat.clog b n := by
  obtain _ | _ | b := b
  · simp [Real.logb]
  · simp [Real.logb]
  obtain rfl | hn := eq_or_ne n 0
  · simp
  rw [← Nat.cast_inj (R := ℤ), Int.natCast_ceil_eq_ceil, ceil_logb_natCast (by simp),
    Int.clog_natCast]
  exact logb_nonneg (by simp [Nat.cast_add_one_pos]) (Nat.one_le_cast.2 (by lia))
/-
**Real.natLog_le_logb** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：natLog_le_logb (a b : Nat) : Nat.log b a <= Real.logb b a
参数：a b : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.floor_logb_natCast`：floor_logb_natCast {b : Nat} {r : Real} (hr : 0
 <= r) : ⌊logb b r⌋ = Int.log b r
· 使用定理 `Nat.cast_nonneg`：cast_nonneg {α} [Semiring α] [PartialOrder α] [IsOrdere
dRing α] (n : Nat) : 0 <= (n : α)
· 使用定理 `Int.log_natCast`：log_natCast (b : Nat) (n : Nat) : log b (n : R) = Nat.l
og b n
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Int.floor_le`：floor_le (a : α) : (⌊a⌋ : α) <= a
-/
lemma natLog_le_logb (a b : ℕ) : Nat.log b a ≤ Real.logb b a := by
  apply le_trans _ (Int.floor_le ((b : ℝ).logb a))
  rw [Real.floor_logb_natCast (Nat.cast_nonneg a), Int.log_natCast, Int.cast_natCast]
/-
**Real.log2_le_logb** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：log2_le_logb (n : Nat) : Nat.log2 n <= Real.logb 2 n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用引理 `Nat.log2_eq_log_two`：log2_eq_log_two {n : Nat} : Nat.log2 n = Nat.log 2 
n
· 使用引理 `Real.natLog_le_logb`：natLog_le_logb (a b : Nat) : Nat.log b a <= Real.lo
gb b a
-/
lemma log2_le_logb (n : ℕ) : Nat.log2 n ≤ Real.logb 2 n := by
  calc (Nat.log2 n : ℝ) = Nat.log 2 n := mod_cast Nat.log2_eq_log_two
  _ ≤ Real.logb 2 n := natLog_le_logb _ _

@[simp]
/-
**Real.logb_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：logb_eq_zero : logb b x = 0 ↔ b = 0 ∨ b = 1 ∨ b = -1 ∨ x = 0 ∨ x = 1 ∨ x =
 -1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Classical.or_iff_not_imp_left`：∀ {a b : Prop}, a ∨ b ↔ ¬a → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_or`：∀ {p q : Prop}, ¬(p ∨ q) ↔ ¬p ∧ ¬q
-/
theorem logb_eq_zero : logb b x = 0 ↔ b = 0 ∨ b = 1 ∨ b = -1 ∨ x = 0 ∨ x = 1 ∨ x = -1 := by
  simp_rw [logb, div_eq_zero_iff, log_eq_zero]
  tauto
/-
**Real.tendsto_logb_nhdsNE_zero** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：tendsto_logb_nhdsNE_zero (hb : 1 < b) : Tendsto (logb b) (𝓝[!=] 0) atBot
参数：hb : 1 < b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.atBot_div_const`：∀ {α : Type u_1} {β : Type u_2} [inst : 
Field α] [inst_1 : LinearOrder α] [IsStrictOrderedRing α] {l : Filter β}   {f : 
β → α} {r : α}, 0 < …
· 使用定理 `Real.log_pos`：log_pos (hx : 1 < x) : 0 < log x
· 使用定理 `Real.tendsto_log_nhdsNE_zero`：tendsto_log_nhdsNE_zero : Tendsto log (𝓝[!
=] 0) atBot
-/
theorem tendsto_logb_nhdsNE_zero (hb : 1 < b) : Tendsto (logb b) (𝓝[≠] 0) atBot :=
  tendsto_log_nhdsNE_zero.atBot_div_const (log_pos hb)
/-
**Real.tendsto_logb_nhdsNE_zero_of_base_lt_one** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：tendsto_logb_nhdsNE_zero_of_base_lt_one (hb₀ : 0 < b) (hb : b < 1) : Tends
to (logb b) (𝓝[!=] 0) atTop
参数：hb₀ : 0 < b；hb : b < 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.atBot_mul_const_of_neg`：∀ {α : Type u_1} {β : Type u_2} [
inst : Field α] [inst_1 : LinearOrder α] [IsStrictOrderedRing α] {l : Filter β} 
  {f : β → α} {r : α}, r < …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `inv_lt_zero`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] [inst_1 : Linea
rOrder G₀] {a : G₀} [PosMulMono G₀], a⁻¹ < 0 ↔ a < 0
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `Real.log_neg`：log_neg (h0 : 0 < x) (h1 : x < 1) : log x < 0
· 使用定理 `Real.tendsto_log_nhdsNE_zero`：tendsto_log_nhdsNE_zero : Tendsto log (𝓝[!
=] 0) atBot
-/
theorem tendsto_logb_nhdsNE_zero_of_base_lt_one (hb₀ : 0 < b) (hb : b < 1) :
    Tendsto (logb b) (𝓝[≠] 0) atTop :=
  tendsto_log_nhdsNE_zero.atBot_mul_const_of_neg (inv_lt_zero.2 (log_neg hb₀ hb))
/-
**Real.tendsto_logb_nhdsGT_zero** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：tendsto_logb_nhdsGT_zero (hb : 1 < b) : Tendsto (logb b) (𝓝[>] 0) atBot
参数：hb : 1 < b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.atBot_div_const`：∀ {α : Type u_1} {β : Type u_2} [inst : 
Field α] [inst_1 : LinearOrder α] [IsStrictOrderedRing α] {l : Filter β}   {f : 
β → α} {r : α}, 0 < …
· 使用定理 `Real.log_pos`：log_pos (hx : 1 < x) : 0 < log x
· 使用引理 `Real.tendsto_log_nhdsGT_zero`：tendsto_log_nhdsGT_zero : Tendsto log (𝓝[>
] 0) atBot
-/
lemma tendsto_logb_nhdsGT_zero (hb : 1 < b) : Tendsto (logb b) (𝓝[>] 0) atBot :=
  tendsto_log_nhdsGT_zero.atBot_div_const (log_pos hb)
/-
**Real.tendsto_logb_nhdsGT_zero_of_base_lt_one** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：tendsto_logb_nhdsGT_zero_of_base_lt_one (hb₀ : 0 < b) (hb : b < 1) : Tends
to (logb b) (𝓝[>] 0) atTop
参数：hb₀ : 0 < b；hb : b < 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.atBot_mul_const_of_neg`：∀ {α : Type u_1} {β : Type u_2} [
inst : Field α] [inst_1 : LinearOrder α] [IsStrictOrderedRing α] {l : Filter β} 
  {f : β → α} {r : α}, r < …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `inv_lt_zero`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] [inst_1 : Linea
rOrder G₀] {a : G₀} [PosMulMono G₀], a⁻¹ < 0 ↔ a < 0
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `Real.log_neg`：log_neg (h0 : 0 < x) (h1 : x < 1) : log x < 0
· 使用引理 `Real.tendsto_log_nhdsGT_zero`：tendsto_log_nhdsGT_zero : Tendsto log (𝓝[>
] 0) atBot
-/
lemma tendsto_logb_nhdsGT_zero_of_base_lt_one (hb₀ : 0 < b) (hb : b < 1) :
    Tendsto (logb b) (𝓝[>] 0) atTop :=
  tendsto_log_nhdsGT_zero.atBot_mul_const_of_neg (inv_lt_zero.2 (log_neg hb₀ hb))

/--
The function `|logb b x|` tends to `+∞` as `x` tendsto `+∞`.
See also `tendsto_logb_atTop` and `tendsto_logb_atTop_of_base_lt_one`.
-/
/-
**Real.tendsto_abs_logb_atTop** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：tendsto_abs_logb_atTop (hb : b != -1 ∧ b != 0 ∧ b != 1) : Tendsto (|logb b
 ·|) atTop atTop
参数：hb : b != -1 ∧ b != 0 ∧ b != 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `Filter.Tendsto.congr'`：∀ {α : Type u_1} {β : Type u_2} {f₁ f₂ : α → β} {
l₁ : Filter α} {l₂ : Filter β},   f₁ =ᶠ[l₁] f₂ → Filter.Tendsto f₁ l₁ l₂ → Filte
r.Tendsto f…
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.eventually_ge_atTop`：eventually_ge_atTop [Preorder α] (a : α) : f
orallᶠ x in atTop, a <= x
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `abs_of_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α]
 {a : α} [AddLeftMono α], 0 ≤ a → |a| = a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Real.logb_nonneg`：logb_nonneg (hx : 1 <= x) : 0 <= logb b x
· 使用定理 `Real.tendsto_logb_atTop`：tendsto_logb_atTop : Tendsto (logb b) atTop atT
op
· 使用定理 `Filter.Tendsto.congr`：∀ {α : Type u_1} {β : Type u_2} {f₁ f₂ : α → β} {l
₁ : Filter α} {l₂ : Filter β},   (∀ (x : α), f₁ x = f₂ x) → Filter.Tendsto f₁ l₁
 l₂ → Filt…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Real.logb_inv_base`：logb_inv_base (b x : Real) : logb b⁻¹ x = -logb b x
· 使用定理 `abs_neg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] (a : 
α), |(-a)| = |a|
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `inv_neg`：inv_neg : (-a)⁻¹ = -a⁻¹
· 使用定理 `inv_one`：inv_one : (1 : G)⁻¹ = 1
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `inv_zero`：∀ {G₀ : Type u} [inst : GroupWithZero G₀], 0⁻¹ = 0
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
（共 94 条，此处仅展示前 30 条）

--- 原说明 ---
The function `|logb b x|` tends to `+∞` as `x` tendsto `+∞`.
See also `tendsto_logb_atTop` and `tendsto_logb_atTop_of_base_lt_one`.
-/
lemma tendsto_abs_logb_atTop (hb : b ≠ -1 ∧ b ≠ 0 ∧ b ≠ 1) :
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
/-
**Real.continuousOn_logb** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：continuousOn_logb : ContinuousOn (logb b) {0}ᶜ
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousOn.div_const`：ContinuousOn.div_const (hf : ContinuousOn f s) (
y : G₀) : ContinuousOn (fun x => f x / y) s
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `Real.continuousOn_log`：continuousOn_log : ContinuousOn log {0}ᶜ
-/
theorem continuousOn_logb : ContinuousOn (logb b) {0}ᶜ := continuousOn_log.div_const _

/-- The real logarithm base b is continuous as a function from nonzero reals. -/
@[fun_prop]
/-
**Real.continuous_logb** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：continuous_logb : Continuous fun x : { x : Real // x != 0 } => logb b x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.div_const`：Continuous.div_const (hf : Continuous f) (y : G₀) 
: Continuous fun x => f x / y
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `Real.continuous_log`：continuous_log : Continuous fun x : { x : Real // x
 != 0 } => log x

--- 原说明 ---
The real logarithm base b is continuous as a function from nonzero reals.
-/
theorem continuous_logb : Continuous fun x : { x : ℝ // x ≠ 0 } => logb b x :=
  continuous_log.div_const _

/-- The real logarithm base b is continuous as a function from positive reals. -/
@[fun_prop]
/-
**Real.continuous_logb'** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：continuous_logb' : Continuous fun x : { x : Real // 0 < x } => logb b x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.div_const`：Continuous.div_const (hf : Continuous f) (y : G₀) 
: Continuous fun x => f x / y
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `Real.continuous_log'`：continuous_log' : Continuous fun x : { x : Real //
 0 < x } => log x

--- 原说明 ---
The real logarithm base b is continuous as a function from positive reals.
-/
theorem continuous_logb' : Continuous fun x : { x : ℝ // 0 < x } => logb b x :=
  continuous_log'.div_const _
/-
**Real.continuousAt_logb** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：continuousAt_logb (hx : x != 0) : ContinuousAt (logb b) x
参数：hx : x != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousAt.div_const`：∀ {α : Type u_1} {G₀ : Type u_3} [inst : DivInvM
onoid G₀] [inst_1 : TopologicalSpace G₀] [SeparatelyContinuousMul G₀]   {f : α →
 G₀} [inst_3…
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `Real.continuousAt_log`：continuousAt_log (hx : x != 0) : ContinuousAt log
 x
-/
theorem continuousAt_logb (hx : x ≠ 0) : ContinuousAt (logb b) x :=
  (continuousAt_log hx).div_const _

@[simp]
/-
**Real.continuousAt_logb_iff** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：continuousAt_logb_iff (hb₀ : 0 < b) (hb : b != 1) : ContinuousAt (logb b) 
x ↔ x != 0
参数：hb₀ : 0 < b；hb : b != 1。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_or_gt_of_ne`：lt_or_gt_of_ne (h : a != b) : a < b ∨ b < a
· 使用定理 `not_tendsto_nhds_of_tendsto_atTop`：∀ {α : Type u} {β : Type v} [inst : P
reorder α] [NoTopOrder α] [inst_2 : TopologicalSpace α] [ClosedIciTopology α]   
{l : Filter β} [l.NeBot…
· 使用定理 `instNoTopOrderOfNoMaxOrder`：∀ {α : Type u_1} [inst : Preorder α] [NoMaxO
rder α], NoTopOrder α
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `Real.tendsto_logb_nhdsNE_zero_of_base_lt_one`：tendsto_logb_nhdsNE_zero_o
f_base_lt_one (hb₀ : 0 < b) (hb : b < 1) : Tendsto (logb b) (𝓝[!=] 0) atTop
· 使用定理 `Filter.Tendsto.mono_left`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {x
 y : Filter α} {z : Filter β},   Filter.Tendsto f x z → y ≤ x → Filter.Tendsto f
 y z
· 使用定理 `ContinuousAt.tendsto`：ContinuousAt.tendsto (h : ContinuousAt f x) : Tend
sto f (𝓝 x) (𝓝 (f x))
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a
· 使用定理 `not_tendsto_nhds_of_tendsto_atBot`：not_tendsto_nhds_of_tendsto_atBot (hf
 : Tendsto f l atBot) (a : α) : ¬Tendsto f l (𝓝 a)
· 使用定理 `instNoBotOrderOfNoMinOrder`：∀ {α : Type u_1} [inst : Preorder α] [NoMinO
rder α], NoBotOrder α
· 使用定理 `instNoMinOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMinOrder R
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `Real.tendsto_logb_nhdsNE_zero`：tendsto_logb_nhdsNE_zero (hb : 1 < b) : T
endsto (logb b) (𝓝[!=] 0) atBot
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.continuousAt_logb`：continuousAt_logb (hx : x != 0) : ContinuousAt (
logb b) x
-/
theorem continuousAt_logb_iff (hb₀ : 0 < b) (hb : b ≠ 1) : ContinuousAt (logb b) x ↔ x ≠ 0 := by
  refine ⟨?_, continuousAt_logb⟩
  rintro h rfl
  cases lt_or_gt_of_ne hb with
  | inl hb₁ =>
      exact not_tendsto_nhds_of_tendsto_atTop (tendsto_logb_nhdsNE_zero_of_base_lt_one hb₀ hb₁)
        _ (h.tendsto.mono_left inf_le_left)
  | inr hb₁ =>
      exact not_tendsto_nhds_of_tendsto_atBot (tendsto_logb_nhdsNE_zero hb₁)
        _ (h.tendsto.mono_left inf_le_left)
/-
**Real.logb_prod** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：logb_prod {α : Type*} (s : Finset α) (f : α -> Real) (hf : forall x in s, 
f x != 0) : logb b (∏ i in s, f i) = ∑ i in s, logb b (f i)
参数：s : Finset α；f : α -> Real；hf : forall x in s, f x != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.cons_induction_on`：cons_induction_on {α : Type*} {motive : Finset
 α -> Prop} (s : Finset α) (empty : motive ∅) (cons : forall (a : α) (s : Finset
 α) (h : a ∉ s…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.logb_one`：logb_one : logb b 1 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.prod_cons`：prod_cons (h : a ∉ s) : ∏ x in cons a s h, f x = f a *
 ∏ x in s, f x
· 使用定理 `Real.logb_mul`：logb_mul (hx : x != 0) (hy : y != 0) : logb b (x * y) = l
ogb b x + logb b y
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Finset.sum_cons`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} {a : ι} 
[inst : AddCommMonoid M] {f : ι → M} (h : a ∉ s),   ∑ x ∈ Finset.cons a s h, f x
 = f …
-/
theorem logb_prod {α : Type*} (s : Finset α) (f : α → ℝ) (hf : ∀ x ∈ s, f x ≠ 0) :
    logb b (∏ i ∈ s, f i) = ∑ i ∈ s, logb b (f i) := by
  induction s using Finset.cons_induction_on with
  | empty => simp
  | cons => simp_all [logb_mul, Finset.prod_ne_zero_iff]
/-
**Real._root_.Finsupp.logb_prod** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem _root_.Finsupp.logb_prod {α β : Type*} [Zero β] (f : α →₀ β) (g : α → β → ℝ)
    (hg : ∀ a, g a (f a) = 0 → f a = 0) : logb b (f.prod g) = f.sum fun a c ↦ logb b (g a c) :=
  logb_prod _ _ fun _x hx h₀ ↦ Finsupp.mem_support_iff.1 hx <| hg _ h₀
/-
**Real.logb_nat_eq_sum_factorization** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：logb_nat_eq_sum_factorization (n : Nat) : logb b n = n.factorization.sum f
un p t => t * logb b p
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Real.log_nat_eq_sum_factorization`：log_nat_eq_sum_factorization (n : Nat
) : log n = n.factorization.sum fun p t => t * log p
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用引理 `Finset.sum_div`：Finset.sum_div (s : Finset ι) (f : ι -> K) (a : K) : (∑ 
i in s, f i) / a = ∑ i in s, f i / a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mul_div_assoc'`：mul_div_assoc' (a b c : G) : a * (b / c) = a * b / c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem logb_nat_eq_sum_factorization (n : ℕ) :
    logb b n = n.factorization.sum fun p t => t * logb b p := by
  simp only [logb, mul_div_assoc', log_nat_eq_sum_factorization n, Finsupp.sum, Finset.sum_div]
/-
**Real.tendsto_pow_logb_div_mul_add_atTop** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：tendsto_pow_logb_div_mul_add_atTop (a c : Real) (n : Nat) (ha : a != 0) : 
Tendsto (fun x => logb b x ^ n / (a * x + c)) atTop (𝓝 0)
参数：a c : Real；n : Nat；ha : a != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `div_zero`：div_zero (a : G₀) : a / 0 = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Filter.Tendsto.const_mul`：Filter.Tendsto.const_mul {α : Type*} {f : α ->
 M} {x : Filter α} {a : M} (b : M) (hf : Tendsto f x (𝓝 a)) : Tendsto (b * f ·) 
x (𝓝 (b * a))
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `tendsto_mul_add_inv_atTop_nhds_zero`：tendsto_mul_add_inv_atTop_nhds_zero
 (a c : Real) (ha : a != 0) : Tendsto (fun x => (a * x + c)⁻¹) atTop (𝓝 0)
· 使用定理 `Filter.Tendsto.congr`：∀ {α : Type u_1} {β : Type u_2} {f₁ f₂ : α → β} {l
₁ : Filter α} {l₂ : Filter β},   (∀ (x : α), f₁ x = f₂ x) → Filter.Tendsto f₁ l₁
 l₂ → Filt…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用引理 `div_pow`：div_pow (a b : α) (n : Nat) : (a / b) ^ n = a ^ n / b ^ n
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_eq_cancel_eq`：eq_eq_cancel_eq {M : Type*} [M
onoidWithZero M] [IsLeftCancelMulZero M] {e₁ e₂ f₁ f₂ L : M} (H₁ : e₁ = L * f₁) 
(H₂ : e₂ = L * f₂) (HL : L != …
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
· 使用定理 `instIsCancelMulZero`：∀ {G₀ : Type u_2} [inst : GroupWithZero G₀], IsCanc
elMulZero G₀
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_mul_of_eq_eq_eq_mul`：eq_mul_of_eq_eq_eq_mul 
{M : Type*} [Mul M] {a b c D e f : M} (h₁ : a = b) (h₂ : b = c) (h₃ : c = D * e)
 (h₄ : e = f) : a = D * f
· 使用定理 `congr_arg₂`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} (f : α → β → 
γ) {x x' : α} {y y' : β}, x = x' → y = y' → f x y = f x' y'
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.div_eq_eval`：div_eq_eval [GroupWithZero M] {
l₁ l₂ l : NF M} {x₁ x₂ : M} (hx₁ : x₁ = l₁.eval) (hx₂ : x₂ = l₂.eval) (h : l₁.ev
al / l₂.eval = l.eval) : x₁ /…
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.atom_eq_eval`：atom_eq_eval [GroupWithZero M]
 (x : M) : x = NF.eval [(1, x)]
· 使用定理 `Mathlib.Tactic.FieldSimp.subst_add`：subst_add {M : Type*} [Semiring M] {
x₁ x₂ X₁ X₂ Y y a : M} (h₁ : x₁ = a * X₁) (h₂ : x₂ = a * X₂) (H_atom : X₁ + X₂ =
 Y) (hy : a * Y = y) : x…
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.mul_eq_eval`：mul_eq_eval [GroupWithZero M] {
l₁ l₂ l : NF M} {x₁ x₂ : M} (hx₁ : x₁ = l₁.eval) (hx₂ : x₂ = l₂.eval) (h : l₁.ev
al * l₂.eval = l.eval) : x₁ *…
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.mul_eq_eval₃`：mul_eq_eval₃ [CommGroupWithZer
o M] {a₁ : Int × M} (a₂ : Int × M) {l₁ l₂ l : NF M} (h : (a₁ ::ᵣ l₁).eval * l₂.e
val = l.eval) : (a₁ ::ᵣ l₁).ev…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_mul_eval_cons`：eval_mul_eval_cons [Comm
GroupWithZero M] (n : Int) (e : M) {L l l' : NF M} (h : L.eval * l.eval = l'.eva
l) : L.eval * ((n, e) ::ᵣ l).eval = …
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_cons_mul_eval`：eval_cons_mul_eval [Comm
GroupWithZero M] (n : Int) (e : M) {L l l' : NF M} (h : L.eval * l.eval = l'.eva
l) : ((n, e) ::ᵣ L).eval * l.eval = …
（共 49 条，此处仅展示前 30 条）
-/
theorem tendsto_pow_logb_div_mul_add_atTop (a c : ℝ) (n : ℕ) (ha : a ≠ 0) :
    Tendsto (fun x => logb b x ^ n / (a * x + c)) atTop (𝓝 0) := by
  cases eq_or_ne (log b) 0 with
  | inl h => simpa [logb, h] using! ((tendsto_mul_add_inv_atTop_nhds_zero _ _ ha).const_mul _)
  | inr h => apply (tendsto_pow_log_div_mul_add_atTop (a * (log b) ^ n) (c * (log b) ^ n) n
                (by positivity)).congr fun x ↦ by simp [field, div_pow, logb]
/-
**Real.isLittleO_pow_logb_id_atTop** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：isLittleO_pow_logb_id_atTop {n : Nat} : (fun x => logb b x ^ n) =o[atTop] 
id
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Asymptotics.isLittleO_iff_tendsto'`：isLittleO_iff_tendsto' {f g : α -> 𝕜
} (hgf : forallᶠ x in l, g x = 0 -> f x = 0) : f =o[l] g ↔ Tendsto (fun x => f x
 / g x) l (𝓝 0)
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.eventually_ne_atTop`：eventually_ne_atTop [Preorder α] [NoTopOrder
 α] (a : α) : forallᶠ x in atTop, x != a
· 使用定理 `instNoTopOrderOfNoMaxOrder`：∀ {α : Type u_1} [inst : Preorder α] [NoMaxO
rder α], NoTopOrder α
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Real.tendsto_pow_logb_div_mul_add_atTop`：tendsto_pow_logb_div_mul_add_at
Top (a c : Real) (n : Nat) (ha : a != 0) : Tendsto (fun x => logb b x ^ n / (a *
 x + c)) atTop (𝓝 0)
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
-/
theorem isLittleO_pow_logb_id_atTop {n : ℕ} : (fun x => logb b x ^ n) =o[atTop] id := by
  rw [Asymptotics.isLittleO_iff_tendsto']
  · simpa using tendsto_pow_logb_div_mul_add_atTop 1 0 n one_ne_zero
  · filter_upwards [eventually_ne_atTop (0 : ℝ)] with x h₁ h₂ using (h₁ h₂).elim
/-
**Real.isLittleO_logb_id_atTop** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：isLittleO_logb_id_atTop : logb b =o[atTop] id
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsLittleO.congr_left`：∀ {α : Type u_1} {E : Type u_3} {F : T
ype u_4} [inst : Norm E] [inst_1 : Norm F] {g : α → F} {l : Filter α}   {f₁ f₂ :
 α → E}, f₁ =o[l] g → …
· 使用定理 `Real.isLittleO_pow_logb_id_atTop`：isLittleO_pow_logb_id_atTop {n : Nat} 
: (fun x => logb b x ^ n) =o[atTop] id
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
-/
theorem isLittleO_logb_id_atTop : logb b =o[atTop] id :=
  isLittleO_pow_logb_id_atTop.congr_left fun _ => pow_one _
/-
**Real.isLittleO_const_logb_atTop** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：isLittleO_const_logb_atTop {c : Real} (hb : b != -1 ∧ b != 0 ∧ b != 1) : (
fun _ => c) =o[atTop] logb b
参数：hb : b != -1 ∧ b != 0 ∧ b != 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Asymptotics.isLittleO_const_left`：isLittleO_const_left {c : E''} : (fun 
_x => c) =o[l] g'' ↔ c = 0 ∨ Tendsto (norm ∘ g'') l atTop
· 使用定理 `Classical.or_iff_not_imp_left`：∀ {a b : Prop}, a ∨ b ↔ ¬a → b
· 使用引理 `Real.tendsto_abs_logb_atTop`：tendsto_abs_logb_atTop (hb : b != -1 ∧ b !=
 0 ∧ b != 1) : Tendsto (|logb b ·|) atTop atTop
-/
theorem isLittleO_const_logb_atTop {c : ℝ} (hb : b ≠ -1 ∧ b ≠ 0 ∧ b ≠ 1) :
    (fun _ => c) =o[atTop] logb b := by
  rw [Asymptotics.isLittleO_const_left, or_iff_not_imp_left]
  intro hc
  exact tendsto_abs_logb_atTop hb
/-
**Real.isBigO_logb_log** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：isBigO_logb_log : logb b =O[⊤] log
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Real.logb_neg_base_eq_logb`：logb_neg_base_eq_logb (b : Real) : logb (-b)
 = logb b
· 使用定理 `Real.logb_one_left_eq_zero`：Real.logb 1 = 0
· 使用定理 `Asymptotics.isBigO_zero`：isBigO_zero : (fun _x => (0 : E')) =O[l] g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.logb_zero_left_eq_zero`：Real.logb 0 = 0
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `norm_mul`：∀ {α : Type u_2} [inst : Norm α] [inst_1 : Mul α] [NormMulClas
s α] (a b : α), ‖a * b‖ = ‖a‖ * ‖b‖
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `norm_inv`：norm_inv (a : α) : ‖a⁻¹‖ = ‖a‖⁻¹
· 使用定理 `Asymptotics.IsBigO.const_mul_left`：∀ {α : Type u_1} {F : Type u_4} {R : 
Type u_13} [inst : Norm F] [inst_1 : SeminormedRing R] {g : α → F} {l : Filter α
}   {f : α → R}, f =O[l…
· 使用定理 `Asymptotics.isBigO_refl`：isBigO_refl (f : α -> E) (l : Filter α) : f =O[
l] f
-/
theorem isBigO_logb_log : logb b =O[⊤] log := by
  by_cases! h : b = -1 ∨ b = 0 ∨ b = 1
  · obtain rfl | rfl | rfl := h
    all_goals simpa [-Asymptotics.isBigO_top] using! Asymptotics.isBigO_zero log ⊤
  · simpa [logb, div_eq_mul_inv, mul_comm]
      using! (Asymptotics.isBigO_refl log ⊤).const_mul_left (log b)⁻¹
/-
**Real.isBigO_log_const_mul_log_atTop** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：isBigO_log_const_mul_log_atTop (c : Real) : (fun x => log (c * x)) =O[atTo
p] log
参数：c : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Real.log_zero`：log_zero : log 0 = 0
· 使用定理 `Asymptotics.IsLittleO.isBigO`：∀ {α : Type u_1} {E : Type u_3} {F : Type 
u_4} [inst : Norm E] [inst_1 : Norm F] {f : α → E} {g : α → F} {l : Filter α},  
 f =o[l] g → f =O[…
· 使用定理 `Real.isLittleO_const_log_atTop`：isLittleO_const_log_atTop {c : Real} : (
fun _ => c) =o[atTop] log
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.eventually_gt_atTop`：eventually_gt_atTop [Preorder α] [NoTopOrder
 α] (a : α) : forallᶠ x in atTop, a < x
· 使用定理 `instNoTopOrderOfNoMaxOrder`：∀ {α : Type u_1} [inst : Preorder α] [NoMaxO
rder α], NoTopOrder α
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Real.log_mul`：log_mul (hx : x != 0) (hy : y != 0) : log (x * y) = log x 
+ log y
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Asymptotics.IsBigO.add`：∀ {α : Type u_1} {F : Type u_4} {E' : Type u_6} 
[inst : Norm F] [inst_1 : SeminormedAddCommGroup E'] {g : α → F}   {l : Filter α
} {f₁ f₂ : α…
· 使用定理 `Asymptotics.isBigO_refl`：isBigO_refl (f : α -> E) (l : Filter α) : f =O[
l] f
-/
theorem isBigO_log_const_mul_log_atTop (c : ℝ) : (fun x ↦ log (c * x)) =O[atTop] log := by
  obtain rfl | hc := eq_or_ne c 0
  · simpa using isLittleO_const_log_atTop.isBigO
  · calc (fun x ↦ log (c * x))
      =ᶠ[atTop] (fun x => log c + log x) := by
          filter_upwards [eventually_gt_atTop 0] with a ha using log_mul hc ha.ne'
      _ =O[atTop] log :=
          isLittleO_const_log_atTop.isBigO.add (Asymptotics.isBigO_refl ..)
/-
**Real.isBigO_log_mul_const_log_atTop** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：isBigO_log_mul_const_log_atTop (c : Real) : (fun x => log (x * c)) =O[atTo
p] log
参数：c : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Real.isBigO_log_const_mul_log_atTop`：isBigO_log_const_mul_log_atTop (c :
 Real) : (fun x => log (c * x)) =O[atTop] log
-/
theorem isBigO_log_mul_const_log_atTop (c : ℝ) : (fun x ↦ log (x * c)) =O[atTop] log := by
  simpa [mul_comm] using isBigO_log_const_mul_log_atTop c
/-
**Real.isBigO_logb_const_mul_log_atTop** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：isBigO_logb_const_mul_log_atTop (c : Real) : (fun x => logb b (c * x)) =O[
atTop] log
参数：c : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Asymptotics.IsBigO.const_mul_left`：∀ {α : Type u_1} {F : Type u_4} {R : 
Type u_13} [inst : Norm F] [inst_1 : SeminormedRing R] {g : α → F} {l : Filter α
}   {f : α → R}, f =O[l…
· 使用定理 `Real.isBigO_log_const_mul_log_atTop`：isBigO_log_const_mul_log_atTop (c :
 Real) : (fun x => log (c * x)) =O[atTop] log
-/
theorem isBigO_logb_const_mul_log_atTop (c : ℝ) : (fun x ↦ logb b (c * x)) =O[atTop] log := by
  simpa [logb, div_eq_mul_inv, mul_comm]
    using (isBigO_log_const_mul_log_atTop c).const_mul_left (log b)⁻¹
/-
**Real.isBigO_logb_mul_const_log_atTop** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：isBigO_logb_mul_const_log_atTop (c : Real) : (fun x => logb b (x * c)) =O[
atTop] log
参数：c : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Real.isBigO_logb_const_mul_log_atTop`：isBigO_logb_const_mul_log_atTop (c
 : Real) : (fun x => logb b (c * x)) =O[atTop] log
-/
theorem isBigO_logb_mul_const_log_atTop (c : ℝ) : (fun x ↦ logb b (x * c)) =O[atTop] log := by
  simpa [mul_comm] using isBigO_logb_const_mul_log_atTop c

end Real

section Continuity

open Real

variable {α : Type*}
variable {b : ℝ}

/-
**Filter.Tendsto.logb** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.Tendsto.logb {f : α -> Real} {l : Filter α} {x : Real} (h : Tendsto
 f l (𝓝 x)) (hx : x != 0) : Tendsto (fun y => logb b (f y)) l (𝓝 (logb b x))
参数：h : Tendsto f l (𝓝 x)；hx : x != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `ContinuousAt.tendsto`：ContinuousAt.tendsto (h : ContinuousAt f x) : Tend
sto f (𝓝 x) (𝓝 (f x))
· 使用定理 `Real.continuousAt_logb`：continuousAt_logb (hx : x != 0) : ContinuousAt (
logb b) x
-/
theorem Filter.Tendsto.logb {f : α → ℝ} {l : Filter α} {x : ℝ}
    (h : Tendsto f l (𝓝 x)) (hx : x ≠ 0) :
    Tendsto (fun y => logb b (f y)) l (𝓝 (logb b x)) :=
  (continuousAt_logb hx).tendsto.comp h

variable [TopologicalSpace α] {f : α → ℝ} {s : Set α} {a : α}

@[fun_prop]
/-
**Continuous.logb** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Continuous.logb (hf : Continuous f) (h₀ : forall x, f x != 0) : Continuous
 fun x => logb b (f x)
参数：hf : Continuous f；h₀ : forall x, f x != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousOn.comp_continuous`：ContinuousOn.comp_continuous {g : β -> γ} 
{f : α -> β} {s : Set β} (hg : ContinuousOn g s) (hf : Continuous f) (hs : foral
l x, f x in s) : C…
· 使用定理 `Real.continuousOn_logb`：continuousOn_logb : ContinuousOn (logb b) {0}ᶜ
-/
theorem Continuous.logb (hf : Continuous f) (h₀ : ∀ x, f x ≠ 0) :
    Continuous fun x => logb b (f x) :=
  continuousOn_logb.comp_continuous hf h₀

@[fun_prop]
nonrec theorem ContinuousAt.logb (hf : ContinuousAt f a) (h₀ : f a ≠ 0) :
    ContinuousAt (fun x => logb b (f x)) a :=
  hf.logb h₀

nonrec theorem ContinuousWithinAt.logb (hf : ContinuousWithinAt f s a) (h₀ : f a ≠ 0) :
    ContinuousWithinAt (fun x => logb b (f x)) s a :=
  hf.logb h₀

@[fun_prop]
/-
**ContinuousOn.logb** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousOn.logb (hf : ContinuousOn f s) (h₀ : forall x in s, f x != 0) :
 ContinuousOn (fun x => logb b (f x)) s
参数：hf : ContinuousOn f s；h₀ : forall x in s, f x != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousWithinAt.logb`：∀ {α : Type u_1} {b : ℝ} [inst : TopologicalSpa
ce α] {f : α → ℝ} {s : Set α} {a : α},   ContinuousWithinAt f s a → f a ≠ 0 → Co
ntinuousWithi…
-/
theorem ContinuousOn.logb (hf : ContinuousOn f s) (h₀ : ∀ x ∈ s, f x ≠ 0) :
    ContinuousOn (fun x => logb b (f x)) s := fun x hx => (hf x hx).logb (h₀ x hx)

end Continuity

section TendstoCompAddSub

open Filter

namespace Real

variable {b : ℝ}

/-
**Real.tendsto_logb_comp_add_sub_logb** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：tendsto_logb_comp_add_sub_logb (y : Real) : Tendsto (fun x : Real => logb 
b (x + y) - logb b x) atTop (𝓝 0)
参数：y : Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `sub_div`：sub_div (a b c : K) : (a - b) / c = a / c - b / c
· 使用定理 `zero_div`：zero_div (a : G₀) : 0 / a = 0
· 使用定理 `Filter.Tendsto.div_const`：Filter.Tendsto.div_const {x : G₀} (hf : Tendst
o f l (𝓝 x)) (y : G₀) : Tendsto (fun a => f a / y) l (𝓝 (x / y))
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `Real.tendsto_log_comp_add_sub_log`：tendsto_log_comp_add_sub_log (y : Rea
l) : Tendsto (fun x : Real => log (x + y) - log x) atTop (𝓝 0)
-/
theorem tendsto_logb_comp_add_sub_logb (y : ℝ) :
    Tendsto (fun x : ℝ => logb b (x + y) - logb b x) atTop (𝓝 0) := by
  simpa [sub_div] using! (tendsto_log_comp_add_sub_log y).div_const (log b)
/-
**Real.tendsto_logb_nat_add_one_sub_logb** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：tendsto_logb_nat_add_one_sub_logb : Tendsto (fun k : Nat => logb b (k + 1)
 - logb b k) atTop (𝓝 0)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `Real.tendsto_logb_comp_add_sub_logb`：tendsto_logb_comp_add_sub_logb (y :
 Real) : Tendsto (fun x : Real => logb b (x + y) - logb b x) atTop (𝓝 0)
· 使用定理 `tendsto_natCast_atTop_atTop`：tendsto_natCast_atTop_atTop [Semiring R] [P
artialOrder R] [IsOrderedRing R] [Archimedean R] : Tendsto ((↑) : Nat -> R) atTo
p atTop
-/
theorem tendsto_logb_nat_add_one_sub_logb :
    Tendsto (fun k : ℕ => logb b (k + 1) - logb b k) atTop (𝓝 0) :=
  (tendsto_logb_comp_add_sub_logb 1).comp tendsto_natCast_atTop_atTop

end Real

end TendstoCompAddSub

section Induction

/-- Induction principle for intervals of real numbers: if a proposition `P` is true
on `[x₀, r * x₀)` and if `P` for `[x₀, r^n * x₀)` implies `P` for `[r^n * x₀, r^(n+1) * x₀)`,
then `P` is true for all `x ≥ x₀`. -/
/-
**Real.induction_Ico_mul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Real.induction_Ico_mul {P : Real -> Prop} (x₀ r : Real) (hr : 1 < r) (hx₀ 
: 0 < x₀) (base : forall x in Set.Ico x₀ (r * x₀), P x) (step : forall n : Nat, 
n >= 1 -> (forall z in Set.Ico x₀ (r ^ n * x₀), P z) -> (forall z in Set.Ico (r 
^ n * x₀) (r ^ (n + 1) * x₀), P z)) : forall x >= x₀, P x
参数：x₀ r : Real；hr : 1 < r；hx₀ : 0 < x₀；base : forall x in Set.Ico x₀ (r * x₀), P
 x；step : forall n : Nat, n >= 1 -> (forall z in Set.Ico x₀ (r ^ n * x₀), P z) -
> (forall z in Set.Ico (r ^ n * x₀) (r ^ (n + 1) * x₀), P z)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `Set.Ico_subset_Ico_union_Ico`：Ico_subset_Ico_union_Ico : Ico a c subsete
q Ico a b union Ico b c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsRightCancelAdd.addRightReflectLE_of_addRightReflectLT`：∀ (N : Type u_2
) [inst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightReflect
LT N],   AddRightReflectLE N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `contravariant_swap_add_of_contravariant_add`：∀ (N : Type u_2) (r : N → N
 → Prop) [inst : AddCommSemigroup N] [ContravariantClass N N (fun x1 x2 => x1 + 
x2) r],   ContravariantClass N N …
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用引理 `div_pos`：div_pos (ha : 0 < a) (hb : 0 < b) : 0 < a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `Set.mem_Ico`：∀ {α : Type u_1} [inst : Preorder α] {a b x : α}, x ∈ Set.I
co a b ↔ a ≤ x ∧ x < b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `div_lt_iff₀`：div_lt_iff₀ (hc : 0 < c) : b / c < a ↔ b < a * c
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
（共 35 条，此处仅展示前 30 条）

--- 原说明 ---
Induction principle for intervals of real numbers: if a proposition `P` is true
on `[x₀, r * x₀)` and if `P` for `[x₀, r^n * x₀)` implies `P` for `[r^n * x₀, r^
(n+1) * x₀)`,
then `P` is true for all `x ≥ x₀`.
-/
lemma Real.induction_Ico_mul {P : ℝ → Prop} (x₀ r : ℝ) (hr : 1 < r) (hx₀ : 0 < x₀)
    (base : ∀ x ∈ Set.Ico x₀ (r * x₀), P x)
    (step : ∀ n : ℕ, n ≥ 1 → (∀ z ∈ Set.Ico x₀ (r ^ n * x₀), P z) →
      (∀ z ∈ Set.Ico (r ^ n * x₀) (r ^ (n + 1) * x₀), P z)) :
    ∀ x ≥ x₀, P x := by
  suffices ∀ n : ℕ, ∀ x ∈ Set.Ico x₀ (r ^ (n + 1) * x₀), P x by
    intro x hx
    have hx' : 0 < x / x₀ := div_pos (hx₀.trans_le hx) hx₀
    refine this ⌊logb r (x / x₀)⌋₊ x ?_
    rw [mem_Ico, ← div_lt_iff₀ hx₀, ← rpow_natCast, ← logb_lt_iff_lt_rpow hr hx', Nat.cast_add,
      Nat.cast_one]
    exact ⟨hx, Nat.lt_floor_add_one _⟩
  intro n
  induction n with
  | zero => simpa using base
  | succ n ih =>
    exact fun x hx => (Ico_subset_Ico_union_Ico hx).elim (ih x) (step (n + 1) (by simp) ih _)

end Induction

