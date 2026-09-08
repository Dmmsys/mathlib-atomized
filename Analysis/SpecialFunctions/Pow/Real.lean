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
variable {x y z : ℝ}

/-- The real power function `x ^ y`, defined as the real part of the complex power function.
For `x > 0`, it is equal to `exp (y log x)`. For `x = 0`, one sets `0 ^ 0=1` and `0 ^ y=0` for
`y ≠ 0`. For `x < 0`, the definition is somewhat arbitrary as it depends on the choice of a complex
determination of the logarithm. With our conventions, it is equal to `exp (y log x) cos (π y)`. -/
/-
**Real.rpow** 是 Mathlib 中的一个定义，位于命名空间 `Real`。
形式化陈述：rpow (x y : Real)
参数：x y : Real。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The real power function `x ^ y`, defined as the real part of the complex power f
unction.
For `x > 0`, it is equal to `exp (y log x)`. For `x = 0`, one sets `0 ^ 0=1` and
 `0 ^ y=0` for
`y ≠ 0`. For `x < 0`, the definition is somewhat arbitrary as it depends on the 
choice of a complex
determination of the logarithm. With our conventions, it is equal to `exp (y log
 x) cos (π y)`.
-/
noncomputable def rpow (x y : ℝ) :=
  ((x : ℂ) ^ (y : ℂ)).re
/-
**Real.** 是 Mathlib 中的一个实例，位于命名空间 `Real`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : Pow ℝ ℝ := ⟨rpow⟩

@[simp]
/-
**Real.rpow_eq_pow** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：rpow_eq_pow (x y : Real) : rpow x y = x ^ y
参数：x y : Real。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem rpow_eq_pow (x y : ℝ) : rpow x y = x ^ y := rfl
/-
**Real.rpow_def** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：rpow_def (x y : Real) : x ^ y = ((x : Complex) ^ (y : Complex)).re
参数：x y : Real。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem rpow_def (x y : ℝ) : x ^ y = ((x : ℂ) ^ (y : ℂ)).re := rfl
/-
**Real.rpow_def_of_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：rpow_def_of_nonneg {x : Real} (hx : 0 <= x) (y : Real) : x ^ y = if x = 0 
then if y = 0 then 1 else 0 else exp (log x * y)
参数：hx : 0 <= x；y : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Complex.ofReal_log`：ofReal_log {x : Real} (hx : 0 <= x) : (x.log : Compl
ex) = log x
· 使用定理 `Complex.ofReal_mul`：ofReal_mul (r s : Real) : ((r * s : Real) : Complex)
 = r * s
-/
theorem rpow_def_of_nonneg {x : ℝ} (hx : 0 ≤ x) (y : ℝ) :
    x ^ y = if x = 0 then if y = 0 then 1 else 0 else exp (log x * y) := by
  simp only [rpow_def, Complex.cpow_def]; split_ifs <;>
  simp_all [(Complex.ofReal_log hx).symm, -Complex.ofReal_mul,
      (Complex.ofReal_mul _ _).symm, Complex.exp_ofReal_re, Complex.ofReal_eq_zero]
/-
**Real.rpow_def_of_pos** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：rpow_def_of_pos {x : Real} (hx : 0 < x) (y : Real) : x ^ y = exp (log x * 
y)
参数：hx : 0 < x；y : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.rpow_def_of_nonneg`：rpow_def_of_nonneg {x : Real} (hx : 0 <= x) (y 
: Real) : x ^ y = if x = 0 then if y = 0 then 1 else 0 else exp (log x * y)
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
-/
theorem rpow_def_of_pos {x : ℝ} (hx : 0 < x) (y : ℝ) : x ^ y = exp (log x * y) := by
  rw [rpow_def_of_nonneg (le_of_lt hx), if_neg (ne_of_gt hx)]
/-
**Real.exp_mul** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：exp_mul (x y : Real) : exp (x * y) = exp x ^ y
参数：x y : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.rpow_def_of_pos`：rpow_def_of_pos {x : Real} (hx : 0 < x) (y : Real)
 : x ^ y = exp (log x * y)
· 使用定理 `Real.exp_pos`：exp_pos (x : Real) : 0 < exp x
· 使用定理 `Real.log_exp`：log_exp (x : Real) : log (exp x) = x
-/
theorem exp_mul (x y : ℝ) : exp (x * y) = exp x ^ y := by rw [rpow_def_of_pos (exp_pos _), log_exp]

@[simp, norm_cast]
/-
**Real.rpow_intCast** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：rpow_intCast (x : Real) (n : Int) : x ^ (n : Real) = x ^ n
参数：x : Real；n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Complex.cpow_intCast`：cpow_intCast (x : Complex) (n : Int) : x ^ (n : Co
mplex) = x ^ n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem rpow_intCast (x : ℝ) (n : ℤ) : x ^ (n : ℝ) = x ^ n := by
  simp only [rpow_def, ← Complex.ofReal_zpow, Complex.cpow_intCast, Complex.ofReal_intCast,
    Complex.ofReal_re]

@[simp, norm_cast]
/-
**Real.rpow_natCast** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：rpow_natCast (x : Real) (n : Nat) : x ^ (n : Real) = x ^ n
参数：x : Real；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用定理 `zpow_natCast`：zpow_natCast (a : G) : forall n : Nat, a ^ (n : Int) = a ^
 n | 0 => (zpow_zero _).trans (pow_zero _).symm | n + 1 => calc a ^ (↑(n + 1) : 
In…
· 使用定理 `Real.rpow_intCast`：rpow_intCast (x : Real) (n : Int) : x ^ (n : Real) = 
x ^ n
-/
theorem rpow_natCast (x : ℝ) (n : ℕ) : x ^ (n : ℝ) = x ^ n := by simpa using rpow_intCast x n

@[simp, norm_cast]
/-
**Real.rpow_neg_natCast** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：rpow_neg_natCast (x : Real) (n : Nat) : x ^ (-n : Real) = x ^ (-n : Int)
参数：x : Real；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.rpow_intCast`：rpow_intCast (x : Real) (n : Int) : x ^ (n : Real) = 
x ^ n
· 使用定理 `Int.cast_neg`：∀ {R : Type u} [inst : AddGroupWithOne R] (n : ℤ), ↑(-n) =
 -↑n
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
-/
theorem rpow_neg_natCast (x : ℝ) (n : ℕ) : x ^ (-n : ℝ) = x ^ (-n : ℤ) := by
  rw [← rpow_intCast, Int.cast_neg, Int.cast_natCast]

@[simp]
/-
**Real.rpow_ofNat** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：rpow_ofNat (x : Real) (n : Nat) [n.AtLeastTwo] : x ^ (ofNat(n) : Real) = x
 ^ (ofNat(n) : Nat)
参数：x : Real；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.rpow_natCast`：rpow_natCast (x : Real) (n : Nat) : x ^ (n : Real) = 
x ^ n
-/
lemma rpow_ofNat (x : ℝ) (n : ℕ) [n.AtLeastTwo] :
    x ^ (ofNat(n) : ℝ) = x ^ (ofNat(n) : ℕ) :=
  rpow_natCast x n

@[simp]
/-
**Real.rpow_neg_ofNat** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：rpow_neg_ofNat (x : Real) (n : Nat) [n.AtLeastTwo] : x ^ (-ofNat(n) : Real
) = x ^ (-ofNat(n) : Int)
参数：x : Real；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.rpow_neg_natCast`：rpow_neg_natCast (x : Real) (n : Nat) : x ^ (-n :
 Real) = x ^ (-n : Int)
-/
theorem rpow_neg_ofNat (x : ℝ) (n : ℕ) [n.AtLeastTwo] : x ^ (-ofNat(n) : ℝ) = x ^ (-ofNat(n) : ℤ) :=
  rpow_neg_natCast _ _

@[simp]
/-
**Real.exp_one_rpow** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：exp_one_rpow (x : Real) : exp 1 ^ x = exp x
参数：x : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.exp_mul`：exp_mul (x y : Real) : exp (x * y) = exp x ^ y
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
theorem exp_one_rpow (x : ℝ) : exp 1 ^ x = exp x := by rw [← exp_mul, one_mul]
/-
**Real.exp_one_pow** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：∀ (n : ℕ), Real.exp 1 ^ n = Real.exp ↑n
参数：n : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.rpow_natCast`：rpow_natCast (x : Real) (n : Nat) : x ^ (n : Real) = 
x ^ n
· 使用定理 `Real.exp_one_rpow`：exp_one_rpow (x : Real) : exp 1 ^ x = exp x
-/
@[simp] lemma exp_one_pow (n : ℕ) : exp 1 ^ n = exp n := by rw [← rpow_natCast, exp_one_rpow]
/-
**Real.rpow_eq_zero_iff_of_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：rpow_eq_zero_iff_of_nonneg (hx : 0 <= x) : x ^ y = 0 ↔ x = 0 ∧ y != 0
参数：hx : 0 <= x。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.rpow_def_of_nonneg`：rpow_def_of_nonneg {x : Real} (hx : 0 <= x) (y 
: Real) : x ^ y = if x = 0 then if y = 0 then 1 else 0 else exp (log x * y)
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
-/
theorem rpow_eq_zero_iff_of_nonneg (hx : 0 ≤ x) : x ^ y = 0 ↔ x = 0 ∧ y ≠ 0 := by
  simp only [rpow_def_of_nonneg hx]
  split_ifs <;> simp [*, exp_ne_zero]

@[simp]
/-
**Real.rpow_eq_zero** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：rpow_eq_zero (hx : 0 <= x) (hy : y != 0) : x ^ y = 0 ↔ x = 0
参数：hx : 0 <= x；hy : y != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma rpow_eq_zero (hx : 0 ≤ x) (hy : y ≠ 0) : x ^ y = 0 ↔ x = 0 := by
  simp [rpow_eq_zero_iff_of_nonneg, *]
/-
**Real.rpow_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：rpow_ne_zero (hx : 0 <= x) (hy : y != 0) : x ^ y != 0 ↔ x != 0
参数：hx : 0 <= x；hy : y != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma rpow_ne_zero (hx : 0 ≤ x) (hy : y ≠ 0) : x ^ y ≠ 0 ↔ x ≠ 0 := by
  simp [hx, hy]

open Real
/-
**Real.rpow_def_of_neg** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：rpow_def_of_neg {x : Real} (hx : x < 0) (y : Real) : x ^ y = exp (log x * 
y) * cos (y * π)
参数：hx : x < 0；y : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.rpow_def`：rpow_def (x y : Real) : x ^ y = ((x : Complex) ^ (y : Com
plex)).re
· 使用定理 `Complex.cpow_def`：cpow_def (x y : Complex) : x ^ y = if x = 0 then if y 
= 0 then 1 else 0 else exp (log x * y)
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Complex.ofReal_eq_zero`：ofReal_eq_zero {z : Real} : (z : Complex) = 0 ↔ 
z = 0
· 使用引理 `ne_of_lt`：ne_of_lt (h : a < b) : a != b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `Complex.norm_real`：norm_real (r : Real) : ‖(r : Complex)‖ = ‖r‖
· 使用定理 `abs_of_neg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] {a
 : α} [AddLeftMono α], a < 0 → |a| = -a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Real.log_neg_eq_log`：log_neg_eq_log (x : Real) : log (-x) = log x
· 使用定理 `Complex.arg_ofReal_of_neg`：arg_ofReal_of_neg {x : Real} (hx : x < 0) : a
rg x = π
· 使用定理 `Complex.ofReal_mul`：ofReal_mul (r s : Real) : ((r * s : Real) : Complex)
 = r * s
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_left`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₃ b c : R} (a₁ : R) (a₂ : ℕ), a₃ * b = c → a₁ ^ a₂ * a₃ * b = a₁ ^ a₂
 * c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_right`：∀ {R : Type u_1} [inst : CommSe
miring R] {a b₃ c : R} (b₁ : R) (b₂ : ℕ), a * b₃ = c → a * (b₁ ^ b₂ * b₃) = b₁ ^
 b₂ * c
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.zero_mul`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (b : R), 0 * b = 0
（共 50 条，此处仅展示前 30 条）
-/
theorem rpow_def_of_neg {x : ℝ} (hx : x < 0) (y : ℝ) : x ^ y = exp (log x * y) * cos (y * π) := by
  rw [rpow_def, Complex.cpow_def, if_neg]
  · have : Complex.log x * y = ↑(log (-x) * y) + ↑(y * π) * Complex.I := by
      simp only [Complex.log, Complex.norm_real, norm_eq_abs, abs_of_neg hx, log_neg_eq_log,
        Complex.arg_ofReal_of_neg hx, Complex.ofReal_mul]
      ring
    rw [this, Complex.exp_add_mul_I, ← Complex.ofReal_exp, ← Complex.ofReal_cos, ←
      Complex.ofReal_sin, mul_add, ← Complex.ofReal_mul, ← mul_assoc, ← Complex.ofReal_mul,
      Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.ofReal_im,
      Real.log_neg_eq_log]
    ring
  · rw [Complex.ofReal_eq_zero]
    exact ne_of_lt hx

-- simp is called on three goals at once (leaving one), with different simp sets
set_option linter.flexible false in
/-
**Real.rpow_def_of_nonpos** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：rpow_def_of_nonpos {x : Real} (hx : x <= 0) (y : Real) : x ^ y = if x = 0 
then if y = 0 then 1 else 0 else exp (log x * y) * cos (y * π)
参数：hx : x <= 0；y : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Complex.cpow_zero`：cpow_zero (x : Complex) : x ^ (0 : Complex) = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Complex.zero_cpow`：zero_cpow {x : Complex} (h : x != 0) : (0 : Complex) 
^ x = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Real.rpow_def_of_neg`：rpow_def_of_neg {x : Real} (hx : x < 0) (y : Real)
 : x ^ y = exp (log x * y) * cos (y * π)
· 使用引理 `lt_of_le_of_ne`：lt_of_le_of_ne : a <= b -> a != b -> a < b
-/
theorem rpow_def_of_nonpos {x : ℝ} (hx : x ≤ 0) (y : ℝ) :
    x ^ y = if x = 0 then if y = 0 then 1 else 0 else exp (log x * y) * cos (y * π) := by
  split_ifs with h <;> simp [rpow_def, *]; exact rpow_def_of_neg (lt_of_le_of_ne hx h) _

@[bound]
/-
**Real.rpow_pos_of_pos** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：rpow_pos_of_pos {x : Real} (hx : 0 < x) (y : Real) : 0 < x ^ y
参数：hx : 0 < x；y : Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.rpow_def_of_pos`：rpow_def_of_pos {x : Real} (hx : 0 < x) (y : Real)
 : x ^ y = exp (log x * y)
· 使用定理 `Real.exp_pos`：exp_pos (x : Real) : 0 < exp x
-/
theorem rpow_pos_of_pos {x : ℝ} (hx : 0 < x) (y : ℝ) : 0 < x ^ y := by
  rw [rpow_def_of_pos hx]; apply exp_pos

@[simp]
/-
**Real.rpow_zero** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：rpow_zero (x : Real) : x ^ (0 : Real) = 1
参数：x : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Complex.cpow_zero`：cpow_zero (x : Complex) : x ^ (0 : Complex) = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem rpow_zero (x : ℝ) : x ^ (0 : ℝ) = 1 := by simp [rpow_def]
/-
**Real.rpow_zero_pos** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：rpow_zero_pos (x : Real) : 0 < x ^ (0 : Real)
参数：x : Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.rpow_zero`：rpow_zero (x : Real) : x ^ (0 : Real) = 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
-/
theorem rpow_zero_pos (x : ℝ) : 0 < x ^ (0 : ℝ) := by simp

@[simp]
/-
**Real.pi_rpow_zero** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：pi_rpow_zero {α : Type*} (f : α -> Real) : f ^ (0 : Real) = 1
参数：f : α -> Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.rpow_zero`：rpow_zero (x : Real) : x ^ (0 : Real) = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem pi_rpow_zero {α : Type*} (f : α → ℝ) : f ^ (0 : ℝ) = 1 := by ext; simp

@[simp]
/-
**Real.zero_rpow** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：zero_rpow {x : Real} (h : x != 0) : (0 : Real) ^ x = 0
参数：h : x != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Complex.zero_cpow`：zero_cpow {x : Complex} (h : x != 0) : (0 : Complex) 
^ x = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem zero_rpow {x : ℝ} (h : x ≠ 0) : (0 : ℝ) ^ x = 0 := by simp [rpow_def, *]
/-
**Real.zero_rpow_eq_iff** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：zero_rpow_eq_iff {x : Real} {a : Real} : 0 ^ x = a ↔ x != 0 ∧ a = 0 ∨ x = 
0 ∧ a = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Complex.cpow_zero`：cpow_zero (x : Complex) : x ^ (0 : Complex) = 1
· 使用定理 `Complex.zero_cpow`：zero_cpow {x : Complex} (h : x != 0) : (0 : Complex) 
^ x = 0
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Complex.ofReal_ne_zero`：ofReal_ne_zero {z : Real} : (z : Complex) != 0 ↔
 z != 0
· 使用定理 `Real.zero_rpow`：zero_rpow {x : Real} (h : x != 0) : (0 : Real) ^ x = 0
· 使用定理 `Real.rpow_zero`：rpow_zero (x : Real) : x ^ (0 : Real) = 1
-/
theorem zero_rpow_eq_iff {x : ℝ} {a : ℝ} : 0 ^ x = a ↔ x ≠ 0 ∧ a = 0 ∨ x = 0 ∧ a = 1 := by
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
/-
**Real.eq_zero_rpow_iff** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：eq_zero_rpow_iff {x : Real} {a : Real} : a = 0 ^ x ↔ x != 0 ∧ a = 0 ∨ x = 
0 ∧ a = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.zero_rpow_eq_iff`：zero_rpow_eq_iff {x : Real} {a : Real} : 0 ^ x = 
a ↔ x != 0 ∧ a = 0 ∨ x = 0 ∧ a = 1
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem eq_zero_rpow_iff {x : ℝ} {a : ℝ} : a = 0 ^ x ↔ x ≠ 0 ∧ a = 0 ∨ x = 0 ∧ a = 1 := by
  rw [← zero_rpow_eq_iff, eq_comm]

@[simp]
/-
**Real.rpow_one** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：rpow_one (x : Real) : x ^ (1 : Real) = x
参数：x : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Complex.cpow_one`：cpow_one (x : Complex) : x ^ (1 : Complex) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem rpow_one (x : ℝ) : x ^ (1 : ℝ) = x := by simp [rpow_def]

@[simp]
/-
**Real.pi_rpow_one** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：pi_rpow_one {α : Type*} (f : α -> Real) : f ^ (1 : Real) = f
参数：f : α -> Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.rpow_one`：rpow_one (x : Real) : x ^ (1 : Real) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem pi_rpow_one {α : Type*} (f : α → ℝ) : f ^ (1 : ℝ) = f := by ext; simp

@[simp]
/-
**Real.one_rpow** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：one_rpow (x : Real) : (1 : Real) ^ x = 1
参数：x : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Complex.one_cpow`：one_cpow (x : Complex) : (1 : Complex) ^ x = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem one_rpow (x : ℝ) : (1 : ℝ) ^ x = 1 := by simp [rpow_def]
/-
**Real.zero_rpow_le_one** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：zero_rpow_le_one (x : Real) : (0 : Real) ^ x <= 1
参数：x : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.rpow_zero`：rpow_zero (x : Real) : x ^ (0 : Real) = 1
· 使用定理 `Real.zero_rpow`：zero_rpow {x : Real} (h : x != 0) : (0 : Real) ^ x = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem zero_rpow_le_one (x : ℝ) : (0 : ℝ) ^ x ≤ 1 := by
  by_cases h : x = 0 <;> simp [h, zero_le_one]
/-
**Real.zero_rpow_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：zero_rpow_nonneg (x : Real) : 0 <= (0 : Real) ^ x
参数：x : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.rpow_zero`：rpow_zero (x : Real) : x ^ (0 : Real) = 1
· 使用定理 `Real.zero_rpow`：zero_rpow {x : Real} (h : x != 0) : (0 : Real) ^ x = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem zero_rpow_nonneg (x : ℝ) : 0 ≤ (0 : ℝ) ^ x := by
  by_cases h : x = 0 <;> simp [h, zero_le_one]

@[bound]
/-
**Real.rpow_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：rpow_nonneg {x : Real} (hx : 0 <= x) (y : Real) : 0 <= x ^ y
参数：hx : 0 <= x；y : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.rpow_def_of_nonneg`：rpow_def_of_nonneg {x : Real} (hx : 0 <= x) (y 
: Real) : x ^ y = if x = 0 then if y = 0 then 1 else 0 else exp (log x * y)
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Real.exp_pos`：exp_pos (x : Real) : 0 < exp x
-/
theorem rpow_nonneg {x : ℝ} (hx : 0 ≤ x) (y : ℝ) : 0 ≤ x ^ y := by
  rw [rpow_def_of_nonneg hx]; split_ifs <;>
    simp only [zero_le_one, le_refl, le_of_lt (exp_pos _)]
/-
**Real.abs_rpow_of_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：abs_rpow_of_nonneg {x y : Real} (hx_nonneg : 0 <= x) : |x ^ y| = |x| ^ y
参数：hx_nonneg : 0 <= x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.rpow_nonneg`：rpow_nonneg {x : Real} (hx : 0 <= x) (y : Real) : 0 <=
 x ^ y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `abs_eq_self`：∀ {G : Type u_1} [inst : AddCommGroup G] [inst_1 : LinearOr
der G] [IsOrderedAddMonoid G] {a : G}, |a| = a ↔ 0 ≤ a
-/
theorem abs_rpow_of_nonneg {x y : ℝ} (hx_nonneg : 0 ≤ x) : |x ^ y| = |x| ^ y := by
  have h_rpow_nonneg : 0 ≤ x ^ y := Real.rpow_nonneg hx_nonneg _
  rw [abs_eq_self.mpr hx_nonneg, abs_eq_self.mpr h_rpow_nonneg]

@[bound]
/-
**Real.abs_rpow_le_abs_rpow** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：abs_rpow_le_abs_rpow (x y : Real) : |x ^ y| <= |x| ^ y
参数：x y : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_or_gt`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b <
 a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.abs_rpow_of_nonneg`：abs_rpow_of_nonneg {x y : Real} (hx_nonneg : 0 
<= x) : |x ^ y| = |x| ^ y
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `abs_of_neg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] {a
 : α} [AddLeftMono α], a < 0 → |a| = -a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Real.rpow_def_of_neg`：rpow_def_of_neg {x : Real} (hx : x < 0) (y : Real)
 : x ^ y = exp (log x * y) * cos (y * π)
· 使用定理 `Real.rpow_def_of_pos`：rpow_def_of_pos {x : Real} (hx : 0 < x) (y : Real)
 : x ^ y = exp (log x * y)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `neg_pos`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [AddLeftStri
ctMono α] {a : α}, 0 < -a ↔ a < 0
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `Real.log_neg_eq_log`：log_neg_eq_log (x : Real) : log (-x) = log x
· 使用引理 `abs_mul`：abs_mul (a b : α) : |a * b| = |a| * |b|
· 使用定理 `abs_of_pos`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] {a
 : α} [AddLeftMono α], 0 < a → |a| = a
· 使用定理 `Real.exp_pos`：exp_pos (x : Real) : 0 < exp x
· 使用定理 `mul_le_of_le_one_right`：mul_le_of_le_one_right [PosMulMono α] (ha : 0 <=
 a) (h : b <= 1) : a * b <= a
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Real.abs_cos_le_one`：abs_cos_le_one : |cos x| <= 1
-/
theorem abs_rpow_le_abs_rpow (x y : ℝ) : |x ^ y| ≤ |x| ^ y := by
  rcases le_or_gt 0 x with hx | hx
  · rw [abs_rpow_of_nonneg hx]
  · rw [abs_of_neg hx, rpow_def_of_neg hx, rpow_def_of_pos (neg_pos.2 hx), log_neg_eq_log, abs_mul,
      abs_of_pos (exp_pos _)]
    exact mul_le_of_le_one_right (exp_pos _).le (abs_cos_le_one _)
/-
**Real.abs_rpow_le_exp_log_mul** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：abs_rpow_le_exp_log_mul (x y : Real) : |x ^ y| <= exp (log x * y)
参数：x y : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Real.abs_rpow_le_abs_rpow`：abs_rpow_le_abs_rpow (x y : Real) : |x ^ y| <
= |x| ^ y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `abs_zero`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] [Add
LeftMono α], |0| = 0
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Real.rpow_zero`：rpow_zero (x : Real) : x ^ (0 : Real) = 1
· 使用定理 `Real.log_zero`：log_zero : log 0 = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Real.exp_zero`：exp_zero : exp 0 = 1
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Real.zero_rpow`：zero_rpow {x : Real} (h : x != 0) : (0 : Real) ^ x = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Real.rpow_def_of_pos`：rpow_def_of_pos {x : Real} (hx : 0 < x) (y : Real)
 : x ^ y = exp (log x * y)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `abs_pos`：∀ {α : Type u_1} [inst : AddGroup α] [inst_1 : LinearOrder α] [
AddLeftMono α] {a : α}, 0 < |a| ↔ a ≠ 0
· 使用定理 `Real.log_abs`：log_abs (x : Real) : log |x| = log x
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem abs_rpow_le_exp_log_mul (x y : ℝ) : |x ^ y| ≤ exp (log x * y) := by
  refine (abs_rpow_le_abs_rpow x y).trans ?_
  by_cases hx : x = 0
  · by_cases hy : y = 0 <;> simp [hx, hy, zero_le_one]
  · rw [rpow_def_of_pos (abs_pos.2 hx), log_abs]
/-
**Real.rpow_inv_log** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：rpow_inv_log (hx₀ : 0 < x) (hx₁ : x != 1) : x ^ (log x)⁻¹ = exp 1
参数：hx₀ : 0 < x；hx₁ : x != 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.rpow_def_of_pos`：rpow_def_of_pos {x : Real} (hx : 0 < x) (y : Real)
 : x ^ y = exp (log x * y)
· 使用引理 `mul_inv_cancel₀`：mul_inv_cancel₀ (h : a != 0) : a * a⁻¹ = 1
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Real.log_ne_zero`：log_ne_zero {x : Real} : log x != 0 ↔ x != 0 ∧ x != 1 
∧ x != -1
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Aesop.BuiltinRules.not_intro`：∀ {P : Prop}, (P → False) → ¬P
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b : R}, a = a' → -a' = b → -a = b
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
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
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_zero`：∀ {R : Type u_1} [inst : CommSemiring R] 
{a : R}, Mathlib.Meta.NormNum.IsNat a 0 → a = 0
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_isNat`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsInt a (Int.ofNat n) → Mathlib.Meta.NormN
um.IsNat a n
· 使用定理 `Mathlib.Meta.NormNum.IsInt.of_raw`：∀ (α : Type u_1) [inst : Ring α] (n :
 ℤ), Mathlib.Meta.NormNum.IsInt n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_overlap_zero`：∀ {R : Type u_1} [in
st : CommSemiring R] {a₁ a₂ b₁ b₂ c : R},   Mathlib.Meta.NormNum.IsNat (a₁ + b₁)
 0 → a₂ + b₂ = c → a₁ + a₂ + (b₁ + b₂) =…
· 使用定理 `Mathlib.Meta.NormNum.isInt_add`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α → α} {a b : α} {a' b' c : ℤ},   f = HAdd.hAdd →     Mathlib.Meta.NormNum.IsI
nt a a' →       Math…
（共 35 条，此处仅展示前 30 条）
-/
lemma rpow_inv_log (hx₀ : 0 < x) (hx₁ : x ≠ 1) : x ^ (log x)⁻¹ = exp 1 := by
  rw [rpow_def_of_pos hx₀, mul_inv_cancel₀]
  exact log_ne_zero.2 ⟨hx₀.ne', hx₁, by bound⟩

/-- See `Real.rpow_inv_log` for the equality when `x ≠ 1` is strictly positive. -/
/-
**Real.rpow_inv_log_le_exp_one** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：rpow_inv_log_le_exp_one : x ^ (log x)⁻¹ <= exp 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_abs_self`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] (
a : α), a ≤ |a|
· 使用定理 `Real.abs_rpow_le_abs_rpow`：abs_rpow_le_abs_rpow (x y : Real) : |x ^ y| <
= |x| ^ y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.log_abs`：log_abs (x : Real) : log |x| = log x
· 使用定理 `LE.le.eq_or_lt'`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, b ≤
 a → a = b ∨ b < a
· 使用定理 `abs_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] [A
ddLeftMono α] [AddRightMono α] (a : α), 0 ≤ |a|
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Real.log_zero`：log_zero : log 0 = 0
· 使用定理 `inv_zero`：∀ {G₀ : Type u} [inst : GroupWithZero G₀], 0⁻¹ = 0
· 使用定理 `Real.rpow_zero`：rpow_zero (x : Real) : x ^ (0 : Real) = 1
· 使用定理 `Real.rpow_def_of_pos`：rpow_def_of_pos {x : Real} (hx : 0 < x) (y : Real)
 : x ^ y = exp (log x * y)
· 使用定理 `Real.exp_monotone`：exp_monotone : Monotone exp
· 使用引理 `mul_inv_le_one`：mul_inv_le_one : a * a⁻¹ <= 1

--- 原说明 ---
See `Real.rpow_inv_log` for the equality when `x ≠ 1` is strictly positive.
-/
lemma rpow_inv_log_le_exp_one : x ^ (log x)⁻¹ ≤ exp 1 := by
  calc
    _ ≤ |x ^ (log x)⁻¹| := le_abs_self _
    _ ≤ |x| ^ (log x)⁻¹ := abs_rpow_le_abs_rpow ..
  rw [← log_abs]
  obtain hx | hx := (abs_nonneg x).eq_or_lt'
  · simp [hx]
  · rw [rpow_def_of_pos hx]
    gcongr
    exact mul_inv_le_one
/-
**Real.norm_rpow_of_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：norm_rpow_of_nonneg {x y : Real} (hx_nonneg : 0 <= x) : ‖x ^ y‖ = ‖x‖ ^ y
参数：hx_nonneg : 0 <= x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.abs_rpow_of_nonneg`：abs_rpow_of_nonneg {x y : Real} (hx_nonneg : 0 
<= x) : |x ^ y| = |x| ^ y
-/
theorem norm_rpow_of_nonneg {x y : ℝ} (hx_nonneg : 0 ≤ x) : ‖x ^ y‖ = ‖x‖ ^ y := by
  simp_rw [Real.norm_eq_abs]
  exact abs_rpow_of_nonneg hx_nonneg

variable {w x y z : ℝ}
/-
**Real.rpow_add** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：rpow_add (hx : 0 < x) (y z : Real) : x ^ (y + z) = x ^ y * x ^ z
参数：hx : 0 < x；y z : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.rpow_def_of_pos`：rpow_def_of_pos {x : Real} (hx : 0 < x) (y : Real)
 : x ^ y = exp (log x * y)
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `Real.exp_add`：∀ (x y : ℝ), Real.exp (x + y) = Real.exp x * Real.exp y
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem rpow_add (hx : 0 < x) (y z : ℝ) : x ^ (y + z) = x ^ y * x ^ z := by
  simp only [rpow_def_of_pos hx, mul_add, exp_add]
/-
**Real.rpow_add'** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：rpow_add' (hx : 0 <= x) (h : y + z != 0) : x ^ (y + z) = x ^ y * x ^ z
参数：hx : 0 <= x；h : y + z != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.eq_or_lt`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a = b ∨ a < b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.zero_rpow`：zero_rpow {x : Real} (h : x != 0) : (0 : Real) ^ x = 0
· 使用定理 `zero_eq_mul`：zero_eq_mul : 0 = a * b ↔ a = 0 ∨ b = 0
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_and_or`：not_and_or : ¬(a ∧ b) ↔ ¬a ∨ ¬b
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Or.imp`：∀ {a c b d : Prop}, (a → c) → (b → d) → a ∨ b → c ∨ d
· 使用定理 `Real.rpow_add`：rpow_add (hx : 0 < x) (y z : Real) : x ^ (y + z) = x ^ y 
* x ^ z
-/
theorem rpow_add' (hx : 0 ≤ x) (h : y + z ≠ 0) : x ^ (y + z) = x ^ y * x ^ z := by
  rcases hx.eq_or_lt with (rfl | pos)
  · rw [zero_rpow h, zero_eq_mul]
    have : y ≠ 0 ∨ z ≠ 0 := not_and_or.1 fun ⟨hy, hz⟩ => h <| hy.symm ▸ hz.symm ▸ zero_add 0
    exact this.imp zero_rpow zero_rpow
  · exact rpow_add pos _ _

/-- Variant of `Real.rpow_add'` that avoids having to prove `y + z = w` twice. -/
/-
**Real.rpow_of_add_eq** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：rpow_of_add_eq (hx : 0 <= x) (hw : w != 0) (h : y + z = w) : x ^ w = x ^ y
 * x ^ z
参数：hx : 0 <= x；hw : w != 0；h : y + z = w。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.rpow_add'`：rpow_add' (hx : 0 <= x) (h : y + z != 0) : x ^ (y + z) =
 x ^ y * x ^ z

--- 原说明 ---
Variant of `Real.rpow_add'` that avoids having to prove `y + z = w` twice.
-/
lemma rpow_of_add_eq (hx : 0 ≤ x) (hw : w ≠ 0) (h : y + z = w) : x ^ w = x ^ y * x ^ z := by
  rw [← h, rpow_add' hx]; rwa [h]
/-
**Real.rpow_add_of_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：rpow_add_of_nonneg (hx : 0 <= x) (hy : 0 <= y) (hz : 0 <= z) : x ^ (y + z)
 = x ^ y * x ^ z
参数：hx : 0 <= x；hy : 0 <= y；hz : 0 <= z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.eq_or_lt`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a = b ∨ a < b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Real.rpow_zero`：rpow_zero (x : Real) : x ^ (0 : Real) = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Real.rpow_add'`：rpow_add' (hx : 0 <= x) (h : y + z != 0) : x ^ (y + z) =
 x ^ y * x ^ z
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `add_pos_of_pos_of_nonneg`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst
_1 : Preorder α] [AddLeftMono α] {a b : α}, 0 < a → 0 ≤ b → 0 < a + b
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
-/
theorem rpow_add_of_nonneg (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    x ^ (y + z) = x ^ y * x ^ z := by
  rcases hy.eq_or_lt with (rfl | hy)
  · rw [zero_add, rpow_zero, one_mul]
  exact rpow_add' hx (ne_of_gt <| add_pos_of_pos_of_nonneg hy hz)

/-- For `0 ≤ x`, the only problematic case in the equality `x ^ y * x ^ z = x ^ (y + z)` is for
`x = 0` and `y + z = 0`, where the right-hand side is `1` while the left-hand side can vanish.
The inequality is always true, though, and given in this lemma. -/
/-
**Real.le_rpow_add** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：le_rpow_add {x : Real} (hx : 0 <= x) (y z : Real) : x ^ y * x ^ z <= x ^ (
y + z)
参数：hx : 0 <= x；y z : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `le_iff_eq_or_lt`：le_iff_eq_or_lt : a <= b ↔ a = b ∨ a < b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Real.rpow_zero`：rpow_zero (x : Real) : x ^ (0 : Real) = 1
· 使用定理 `mul_le_mul`：∀ {α : Type u_1} [inst : Mul α] [inst_1 : Zero α] [inst_2 : 
Preorder α] {a b c d : α} [PosMulMono α] [MulPosMono α],   a ≤ b → c ≤ d → 0 ≤ c
…
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `Real.zero_rpow_le_one`：zero_rpow_le_one (x : Real) : (0 : Real) ^ x <= 1
· 使用定理 `Real.zero_rpow_nonneg`：zero_rpow_nonneg (x : Real) : 0 <= (0 : Real) ^ x
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Real.rpow_add'`：rpow_add' (hx : 0 <= x) (h : y + z != 0) : x ^ (y + z) =
 x ^ y * x ^ z
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Real.rpow_add`：rpow_add (hx : 0 < x) (y z : Real) : x ^ (y + z) = x ^ y 
* x ^ z

--- 原说明 ---
For `0 ≤ x`, the only problematic case in the equality `x ^ y * x ^ z = x ^ (y +
 z)` is for
`x = 0` and `y + z = 0`, where the right-hand side is `1` while the left-hand si
de can vanish.
The inequality is always true, though, and given in this lemma.
-/
theorem le_rpow_add {x : ℝ} (hx : 0 ≤ x) (y z : ℝ) : x ^ y * x ^ z ≤ x ^ (y + z) := by
  rcases le_iff_eq_or_lt.1 hx with (H | pos)
  · by_cases h : y + z = 0
    · simp only [H.symm, h, rpow_zero]
      calc
        (0 : ℝ) ^ y * 0 ^ z ≤ 1 * 1 := by
          gcongr
          exacts [zero_rpow_nonneg z, zero_rpow_le_one y, zero_rpow_le_one z]
        _ = 1 := by simp
    · simp [rpow_add', ← H, h]
  · simp [rpow_add pos]
/-
**Real.rpow_sum_of_pos** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：rpow_sum_of_pos {ι : Type*} {a : Real} (ha : 0 < a) (f : ι -> Real) (s : F
inset ι) : (a ^ ∑ x in s, f x) = ∏ x in s, a ^ f x
参数：ha : 0 < a；f : ι -> Real；s : Finset ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `Real.rpow_zero`：rpow_zero (x : Real) : x ^ (0 : Real) = 1
· 使用定理 `Real.rpow_add`：rpow_add (hx : 0 < x) (y z : Real) : x ^ (y + z) = x ^ y 
* x ^ z
-/
theorem rpow_sum_of_pos {ι : Type*} {a : ℝ} (ha : 0 < a) (f : ι → ℝ) (s : Finset ι) :
    (a ^ ∑ x ∈ s, f x) = ∏ x ∈ s, a ^ f x :=
  map_sum (⟨⟨fun (x : ℝ) => (a ^ x : ℝ), rpow_zero a⟩, rpow_add ha⟩ : ℝ →+ (Additive ℝ)) f s
/-
**Real.rpow_sum_of_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：rpow_sum_of_nonneg {ι : Type*} {a : Real} (ha : 0 <= a) {s : Finset ι} {f 
: ι -> Real} (h : forall x in s, 0 <= f x) : (a ^ ∑ x in s, f x) = ∏ x in s, a ^
 f x
参数：ha : 0 <= a；h : forall x in s, 0 <= f x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.cons_induction`：∀ {α : Type u_3} {motive : Finset α → Prop},   mo
tive ∅ → (∀ (a : α) (s : Finset α) (h : a ∉ s), motive s → motive (Finset.cons a
 s h)) → ∀ …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_empty`：∀ {ι : Type u_1} {M : Type u_3} {f : ι → M} [inst : Ad
dCommMonoid M], ∑ x ∈ ∅, f x = 0
· 使用定理 `Finset.prod_empty`：prod_empty : ∏ x in ∅, f x = 1
· 使用定理 `Real.rpow_zero`：rpow_zero (x : Real) : x ^ (0 : Real) = 1
· 使用定理 `Finset.sum_cons`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} {a : ι} 
[inst : AddCommMonoid M] {f : ι → M} (h : a ∉ s),   ∑ x ∈ Finset.cons a s h, f x
 = f …
· 使用定理 `Finset.prod_cons`：prod_cons (h : a ∉ s) : ∏ x in cons a s h, f x = f a *
 ∏ x in s, f x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Finset.forall_mem_cons`：forall_mem_cons (h : a ∉ s) (p : α -> Prop) : (f
orall x, x in cons a s h -> p x) ↔ p a ∧ forall x, x in s -> p x
· 使用定理 `Real.rpow_add_of_nonneg`：rpow_add_of_nonneg (hx : 0 <= x) (hy : 0 <= y) 
(hz : 0 <= z) : x ^ (y + z) = x ^ y * x ^ z
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Finset.sum_nonneg`：∀ {ι : Type u_1} {N : Type u_5} [inst : AddCommMonoid
 N] [inst_1 : Preorder N] {f : ι → N} {s : Finset ι}   [AddLeftMono N], (∀ i ∈ s
, 0 ≤ f…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
-/
theorem rpow_sum_of_nonneg {ι : Type*} {a : ℝ} (ha : 0 ≤ a) {s : Finset ι} {f : ι → ℝ}
    (h : ∀ x ∈ s, 0 ≤ f x) : (a ^ ∑ x ∈ s, f x) = ∏ x ∈ s, a ^ f x := by
  induction s using Finset.cons_induction with
  | empty => rw [sum_empty, Finset.prod_empty, rpow_zero]
  | cons i s hi ihs =>
    rw [forall_mem_cons] at h
    rw [sum_cons, prod_cons, ← ihs h.2, rpow_add_of_nonneg ha h.1 (sum_nonneg h.2)]

/-- See also `rpow_neg` for a version with `(x ^ y)⁻¹` in the RHS. -/
/-
**Real.rpow_neg_eq_inv_rpow** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：rpow_neg_eq_inv_rpow (x y : Real) : x ^ (-y) = x⁻¹ ^ y
参数：x y : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Complex.ofReal_neg`：ofReal_neg (r : Real) : ((-r : Real) : Complex) = -r
· 使用定理 `Complex.cpow_neg`：cpow_neg (x y : Complex) : x ^ (-y) = (x ^ y)⁻¹
· 使用定理 `Complex.inv_re`：inv_re (z : Complex) : z⁻¹.re = z.re / normSq z
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Complex.ofReal_inv`：ofReal_inv (r : Real) : ((r⁻¹ : Real) : Complex) = (
r : Complex)⁻¹
· 使用定理 `Complex.inv_cpow_eq_ite`：inv_cpow_eq_ite (x : Complex) (n : Complex) : x
⁻¹ ^ n = if x.arg = π then conj (x ^ conj n)⁻¹ else (x ^ n)⁻¹
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `Complex.conj_ofReal`：conj_ofReal (r : Real) : conj (r : Complex) = r
· 使用定理 `map_inv₀`：map_inv₀ : f a⁻¹ = (f a)⁻¹
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `apply_ite`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β) (P : Prop) [inst 
: Decidable P] (x y : α),   f (if P then x else y) = if P then f x else f y
· 使用定理 `Complex.normSq_conj`：normSq_conj (z : Complex) : normSq (conj z) = normS
q z
· 使用定理 `ite_self`：∀ {α : Sort u} {c : Prop} {d : Decidable c} (a : α), (if c the
n a else a) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
See also `rpow_neg` for a version with `(x ^ y)⁻¹` in the RHS.
-/
theorem rpow_neg_eq_inv_rpow (x y : ℝ) : x ^ (-y) = x⁻¹ ^ y := by
  simp [rpow_def, Complex.cpow_neg, Complex.inv_cpow_eq_ite, apply_ite]

/-- See also `rpow_neg_eq_inv_rpow` for a version with `x⁻¹ ^ y` in the RHS. -/
/-
**Real.rpow_neg** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：rpow_neg {x : Real} (hx : 0 <= x) (y : Real) : x ^ (-y) = (x ^ y)⁻¹
参数：hx : 0 <= x；y : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.rpow_def_of_nonneg`：rpow_def_of_nonneg {x : Real} (hx : 0 <= x) (y 
: Real) : x ^ y = if x = 0 then if y = 0 then 1 else 0 else exp (log x * y)
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `inv_one`：inv_one : (1 : G)⁻¹ = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `inv_zero`：∀ {G₀ : Type u} [inst : GroupWithZero G₀], 0⁻¹ = 0
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `Real.exp_neg`：∀ (x : ℝ), Real.exp (-x) = (Real.exp x)⁻¹

--- 原说明 ---
See also `rpow_neg_eq_inv_rpow` for a version with `x⁻¹ ^ y` in the RHS.
-/
theorem rpow_neg {x : ℝ} (hx : 0 ≤ x) (y : ℝ) : x ^ (-y) = (x ^ y)⁻¹ := by
  simp only [rpow_def_of_nonneg hx]; split_ifs <;> simp_all [exp_neg]
/-
**Real.rpow_sub** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：rpow_sub {x : Real} (hx : 0 < x) (y z : Real) : x ^ (y - z) = x ^ y / x ^ 
z
参数：hx : 0 < x；y z : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `Real.rpow_add`：rpow_add (hx : 0 < x) (y z : Real) : x ^ (y + z) = x ^ y 
* x ^ z
· 使用定理 `Real.rpow_neg`：rpow_neg {x : Real} (hx : 0 <= x) (y : Real) : x ^ (-y) =
 (x ^ y)⁻¹
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem rpow_sub {x : ℝ} (hx : 0 < x) (y z : ℝ) : x ^ (y - z) = x ^ y / x ^ z := by
  simp only [sub_eq_add_neg, rpow_add hx, rpow_neg (le_of_lt hx), div_eq_mul_inv]
/-
**Real.rpow_sub'** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：rpow_sub' {x : Real} (hx : 0 <= x) {y z : Real} (h : y - z != 0) : x ^ (y 
- z) = x ^ y / x ^ z
参数：hx : 0 <= x；h : y - z != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Real.rpow_add'`：rpow_add' (hx : 0 <= x) (h : y + z != 0) : x ^ (y + z) =
 x ^ y * x ^ z
· 使用定理 `Real.rpow_neg`：rpow_neg {x : Real} (hx : 0 <= x) (y : Real) : x ^ (-y) =
 (x ^ y)⁻¹
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem rpow_sub' {x : ℝ} (hx : 0 ≤ x) {y z : ℝ} (h : y - z ≠ 0) : x ^ (y - z) = x ^ y / x ^ z := by
  simp only [sub_eq_add_neg] at h ⊢
  simp only [rpow_add' hx h, rpow_neg hx, div_eq_mul_inv]
/-
**Real._root_.HasCompactSupport.rpow_const** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem _root_.HasCompactSupport.rpow_const {α : Type*} [TopologicalSpace α] {f : α → ℝ}
    (hf : HasCompactSupport f) {r : ℝ} (hr : r ≠ 0) : HasCompactSupport (fun x ↦ f x ^ r) :=
  hf.comp_left (g := (· ^ r)) (Real.zero_rpow hr)

end Real

/-!
## Comparing real and complex powers
-/


namespace Complex

/-
**Complex.ofReal_cpow** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：ofReal_cpow {x : Real} (hx : 0 <= x) (y : Real) : ((x ^ y : Real) : Comple
x) = (x : Complex) ^ (y : Complex)
参数：hx : 0 <= x；y : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.rpow_def_of_nonneg`：rpow_def_of_nonneg {x : Real} (hx : 0 <= x) (y 
: Real) : x ^ y = if x = 0 then if y = 0 then 1 else 0 else exp (log x * y)
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Complex.ofReal_exp`：ofReal_exp (x : Real) : (Real.exp x : Complex) = exp
 x
· 使用定理 `Complex.ofReal_mul`：ofReal_mul (r s : Real) : ((r * s : Real) : Complex)
 = r * s
· 使用定理 `Complex.ofReal_log`：ofReal_log {x : Real} (hx : 0 <= x) : (x.log : Compl
ex) = log x
-/
theorem ofReal_cpow {x : ℝ} (hx : 0 ≤ x) (y : ℝ) : ((x ^ y : ℝ) : ℂ) = (x : ℂ) ^ (y : ℂ) := by
  simp only [Real.rpow_def_of_nonneg hx, Complex.cpow_def, ofReal_eq_zero]; split_ifs <;>
    simp [Complex.ofReal_log hx]
/-
**Complex.ofReal_cpow_of_nonpos** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：ofReal_cpow_of_nonpos {x : Real} (hx : x <= 0) (y : Complex) : (x : Comple
x) ^ y = (-x : Complex) ^ y * exp (π * I * y)
参数：hx : x <= 0；y : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.eq_or_lt`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a = b ∨ a < b
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Complex.cpow_zero`：cpow_zero (x : Complex) : x ^ (0 : Complex) = 1
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Complex.exp_zero`：exp_zero : exp 0 = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Complex.zero_cpow`：zero_cpow {x : Complex} (h : x != 0) : (0 : Complex) 
^ x = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Complex.ofReal_ne_zero`：ofReal_ne_zero {z : Real} : (z : Complex) != 0 ↔
 z != 0
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `Complex.cpow_def_of_ne_zero`：cpow_def_of_ne_zero {x : Complex} (hx : x !
= 0) (y : Complex) : x ^ y = exp (log x * y)
· 使用定理 `neg_ne_zero`：∀ {α : Type u_1} [inst : SubtractionMonoid α] {a : α}, -a ≠
 0 ↔ a ≠ 0
· 使用定理 `Complex.exp_add`：exp_add : exp (x + y) = exp x * exp y
· 使用定理 `add_mul`：add_mul {d : R} (_ : (a₁ : R) * b = c₁) (_ : a₂ * b = c₂) (_ : 
c₁ + c₂ = d) : (a₁ + a₂) * b = d
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
· 使用定理 `Complex.log.eq_1`：∀ (x : ℂ), Complex.log x = ↑(Real.log ‖x‖) + ↑x.arg * 
Complex.I
· 使用定理 `norm_neg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), ‖-a‖ =
 ‖a‖
· 使用定理 `Complex.arg_ofReal_of_neg`：arg_ofReal_of_neg {x : Real} (hx : x < 0) : a
rg x = π
· 使用定理 `Complex.ofReal_neg`：ofReal_neg (r : Real) : ((-r : Real) : Complex) = -r
（共 35 条，此处仅展示前 30 条）
-/
theorem ofReal_cpow_of_nonpos {x : ℝ} (hx : x ≤ 0) (y : ℂ) :
    (x : ℂ) ^ y = (-x : ℂ) ^ y * exp (π * I * y) := by
  rcases hx.eq_or_lt with (rfl | hlt)
  · rcases eq_or_ne y 0 with (rfl | hy) <;> simp [*]
  have hne : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hlt.ne
  rw [cpow_def_of_ne_zero hne, cpow_def_of_ne_zero (neg_ne_zero.2 hne), ← exp_add, ← add_mul, log,
    log, norm_neg, arg_ofReal_of_neg hlt, ← ofReal_neg, arg_ofReal_of_nonneg (neg_nonneg.2 hx),
    ofReal_zero, zero_mul, add_zero]
/-
**Complex.cpow_ofReal** 是 Mathlib 中的一个引理，位于命名空间 `Complex`。
形式化陈述：cpow_ofReal (x : Complex) (y : Real) : x ^ (y : Complex) = ↑(‖x‖ ^ y) * (R
eal.cos (arg x * y) + Real.sin (arg x * y) * I)
参数：x : Complex；y : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `Complex.ofReal_cpow`：ofReal_cpow {x : Real} (hx : 0 <= x) (y : Real) : (
(x ^ y : Real) : Complex) = (x : Complex) ^ (y : Complex)
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `Complex.arg_zero`：arg_zero : arg 0 = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Real.cos_zero`：cos_zero : cos 0 = 1
· 使用定理 `Real.sin_zero`：sin_zero : sin 0 = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Complex.cpow_def_of_ne_zero`：cpow_def_of_ne_zero {x : Complex} (hx : x !
= 0) (y : Complex) : x ^ y = exp (log x * y)
· 使用定理 `Complex.exp_eq_exp_re_mul_sin_add_cos`：exp_eq_exp_re_mul_sin_add_cos : e
xp x = exp x.re * (cos x.im + sin x.im * I)
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Complex.re_ofReal_mul`：re_ofReal_mul (r : Real) (z : Complex) : (r * z).
re = r * z.re
· 使用定理 `Complex.im_ofReal_mul`：im_ofReal_mul (r : Real) (z : Complex) : (r * z).
im = r * z.im
· 使用定理 `Complex.log_re`：log_re (x : Complex) : x.log.re = Real.log ‖x‖
· 使用定理 `Complex.log_im`：log_im (x : Complex) : x.log.im = x.arg
· 使用定理 `Real.exp_mul`：exp_mul (x y : Real) : exp (x * y) = exp x ^ y
· 使用定理 `Real.exp_log`：exp_log (hx : 0 < x) : exp (log x) = x
· 使用定理 `norm_pos_iff`：∀ {E : Type u_5} [inst : NormedAddGroup E] {a : E}, 0 < ‖a
‖ ↔ a ≠ 0
-/
lemma cpow_ofReal (x : ℂ) (y : ℝ) :
    x ^ (y : ℂ) = ↑(‖x‖ ^ y) * (Real.cos (arg x * y) + Real.sin (arg x * y) * I) := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp [ofReal_cpow le_rfl]
  · rw [cpow_def_of_ne_zero hx, exp_eq_exp_re_mul_sin_add_cos, mul_comm (log x)]
    norm_cast
    rw [re_ofReal_mul, im_ofReal_mul, log_re, log_im, mul_comm y, mul_comm y, Real.exp_mul,
      Real.exp_log]
    rwa [norm_pos_iff]
/-
**Complex.cpow_ofReal_re** 是 Mathlib 中的一个引理，位于命名空间 `Complex`。
形式化陈述：cpow_ofReal_re (x : Complex) (y : Real) : (x ^ (y : Complex)).re = ‖x‖ ^ y
 * Real.cos (arg x * y)
参数：x : Complex；y : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Complex.cpow_ofReal`：cpow_ofReal (x : Complex) (y : Real) : x ^ (y : Com
plex) = ↑(‖x‖ ^ y) * (Real.cos (arg x * y) + Real.sin (arg x * y) * I)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Complex.ofReal_cos_ofReal_re`：ofReal_cos_ofReal_re (x : Real) : ((cos x)
.re : Complex) = cos x
· 使用定理 `Complex.ofReal_sin`：ofReal_sin (x : Real) : (Real.sin x : Complex) = sin
 x
· 使用定理 `Complex.mul_re`：mul_re (z w : Complex) : (z * w).re = z.re * w.re - z.im
 * w.im
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Complex.sin_ofReal_im`：sin_ofReal_im (x : Real) : (sin x).im = 0
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Complex.cos_ofReal_im`：cos_ofReal_im (x : Real) : (cos x).im = 0
· 使用定理 `Complex.mul_im`：mul_im (z w : Complex) : (z * w).im = z.re * w.im + z.im
 * w.re
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma cpow_ofReal_re (x : ℂ) (y : ℝ) : (x ^ (y : ℂ)).re = ‖x‖ ^ y * Real.cos (arg x * y) := by
  rw [cpow_ofReal]; generalize arg x * y = z; simp [Real.cos]
/-
**Complex.cpow_ofReal_im** 是 Mathlib 中的一个引理，位于命名空间 `Complex`。
形式化陈述：cpow_ofReal_im (x : Complex) (y : Real) : (x ^ (y : Complex)).im = ‖x‖ ^ y
 * Real.sin (arg x * y)
参数：x : Complex；y : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Complex.cpow_ofReal`：cpow_ofReal (x : Complex) (y : Real) : x ^ (y : Com
plex) = ↑(‖x‖ ^ y) * (Real.cos (arg x * y) + Real.sin (arg x * y) * I)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Complex.ofReal_cos`：ofReal_cos (x : Real) : (Real.cos x : Complex) = cos
 x
· 使用定理 `Complex.ofReal_sin_ofReal_re`：ofReal_sin_ofReal_re (x : Real) : ((sin x)
.re : Complex) = sin x
· 使用定理 `Complex.mul_im`：mul_im (z w : Complex) : (z * w).im = z.re * w.im + z.im
 * w.re
· 使用定理 `Complex.cos_ofReal_im`：cos_ofReal_im (x : Real) : (cos x).im = 0
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Complex.sin_ofReal_im`：sin_ofReal_im (x : Real) : (sin x).im = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Complex.mul_re`：mul_re (z w : Complex) : (z * w).re = z.re * w.re - z.im
 * w.im
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma cpow_ofReal_im (x : ℂ) (y : ℝ) : (x ^ (y : ℂ)).im = ‖x‖ ^ y * Real.sin (arg x * y) := by
  rw [cpow_ofReal]; generalize arg x * y = z; simp [Real.sin]
/-
**Complex.norm_cpow_of_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：norm_cpow_of_ne_zero {z : Complex} (hz : z != 0) (w : Complex) : ‖z ^ w‖ =
 ‖z‖ ^ w.re / Real.exp (arg z * im w)
参数：hz : z != 0；w : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Complex.cpow_def_of_ne_zero`：cpow_def_of_ne_zero {x : Complex} (hx : x !
= 0) (y : Complex) : x ^ y = exp (log x * y)
· 使用定理 `Complex.norm_exp`：norm_exp (z : Complex) : ‖exp z‖ = Real.exp z.re
· 使用定理 `Complex.mul_re`：mul_re (z w : Complex) : (z * w).re = z.re * w.re - z.im
 * w.im
· 使用定理 `Complex.log_re`：log_re (x : Complex) : x.log.re = Real.log ‖x‖
· 使用定理 `Complex.log_im`：log_im (x : Complex) : x.log.im = x.arg
· 使用定理 `Real.exp_sub`：exp_sub : exp (x - y) = exp x / exp y
· 使用定理 `Real.rpow_def_of_pos`：rpow_def_of_pos {x : Real} (hx : 0 < x) (y : Real)
 : x ^ y = exp (log x * y)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `norm_pos_iff`：∀ {E : Type u_5} [inst : NormedAddGroup E] {a : E}, 0 < ‖a
‖ ↔ a ≠ 0
-/
theorem norm_cpow_of_ne_zero {z : ℂ} (hz : z ≠ 0) (w : ℂ) :
    ‖z ^ w‖ = ‖z‖ ^ w.re / Real.exp (arg z * im w) := by
  rw [cpow_def_of_ne_zero hz, norm_exp, mul_re, log_re, log_im, Real.exp_sub,
    Real.rpow_def_of_pos (norm_pos_iff.mpr hz)]
/-
**Complex.norm_cpow_of_imp** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：norm_cpow_of_imp {z w : Complex} (h : z = 0 -> w.re = 0 -> w = 0) : ‖z ^ w
‖ = ‖z‖ ^ w.re / Real.exp (arg z * im w)
参数：h : z = 0 -> w.re = 0 -> w = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ne_or_eq`：ne_or_eq {α : Sort*} (x y : α) : x != y ∨ x = y
· 使用定理 `Complex.norm_cpow_of_ne_zero`：norm_cpow_of_ne_zero {z : Complex} (hz : z
 != 0) (w : Complex) : ‖z ^ w‖ = ‖z‖ ^ w.re / Real.exp (arg z * im w)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Complex.cpow_zero`：cpow_zero (x : Complex) : x ^ (0 : Complex) = 1
· 使用定理 `NormOneClass.norm_one`：∀ {α : Type u_5} {inst : Norm α} {inst_1 : One α}
 [self : NormOneClass α], ‖1‖ = 1
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `Real.rpow_zero`：rpow_zero (x : Real) : x ^ (0 : Real) = 1
· 使用定理 `Complex.arg_zero`：arg_zero : arg 0 = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Real.exp_zero`：exp_zero : exp 0 = 1
· 使用定理 `div_self`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a : G₀}, a ≠ 0 → 
a / a = 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Real.zero_rpow`：zero_rpow {x : Real} (h : x != 0) : (0 : Real) ^ x = 0
· 使用定理 `zero_div`：zero_div (a : G₀) : 0 / a = 0
· 使用定理 `Complex.zero_cpow`：zero_cpow {x : Complex} (h : x != 0) : (0 : Complex) 
^ x = 0
· 使用定理 `ne_of_apply_ne`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β) {x y : α}, f
 x ≠ f y → x ≠ y
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem norm_cpow_of_imp {z w : ℂ} (h : z = 0 → w.re = 0 → w = 0) :
    ‖z ^ w‖ = ‖z‖ ^ w.re / Real.exp (arg z * im w) := by
  rcases ne_or_eq z 0 with (hz | rfl) <;> [exact norm_cpow_of_ne_zero hz w; rw [norm_zero]]
  rcases eq_or_ne w.re 0 with hw | hw
  · simp [h rfl hw]
  · rw [Real.zero_rpow hw, zero_div, zero_cpow, norm_zero]
    exact ne_of_apply_ne re hw
/-
**Complex.norm_cpow_le** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：norm_cpow_le (z w : Complex) : ‖z ^ w‖ <= ‖z‖ ^ w.re / Real.exp (arg z * i
m w)
参数：z w : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Complex.norm_cpow_of_imp`：norm_cpow_of_imp {z w : Complex} (h : z = 0 ->
 w.re = 0 -> w = 0) : ‖z ^ w‖ = ‖z‖ ^ w.re / Real.exp (arg z * im w)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Complex.zero_cpow`：zero_cpow {x : Complex} (h : x != 0) : (0 : Complex) 
^ x = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `Real.rpow_zero`：rpow_zero (x : Real) : x ^ (0 : Real) = 1
· 使用定理 `Complex.arg_zero`：arg_zero : arg 0 = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Real.exp_zero`：exp_zero : exp 0 = 1
· 使用定理 `div_self`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a : G₀}, a ≠ 0 → 
a / a = 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
-/
theorem norm_cpow_le (z w : ℂ) : ‖z ^ w‖ ≤ ‖z‖ ^ w.re / Real.exp (arg z * im w) := by
  by_cases! h : z = 0 → w.re = 0 → w = 0
  · exact (norm_cpow_of_imp h).le
  · simp [h]

@[simp]
/-
**Complex.norm_cpow_real** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：norm_cpow_real (x : Complex) (y : Real) : ‖x ^ (y : Complex)‖ = ‖x‖ ^ y
参数：x : Complex；y : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Complex.norm_cpow_of_imp`：norm_cpow_of_imp {z w : Complex} (h : z = 0 ->
 w.re = 0 -> w = 0) : ‖z ^ w‖ = ‖z‖ ^ w.re / Real.exp (arg z * im w)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Real.exp_zero`：exp_zero : exp 0 = 1
· 使用定理 `div_one`：div_one (a : G) : a / 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem norm_cpow_real (x : ℂ) (y : ℝ) : ‖x ^ (y : ℂ)‖ = ‖x‖ ^ y := by
  rw [norm_cpow_of_imp] <;> simp

@[simp]
/-
**Complex.norm_cpow_inv_nat** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：norm_cpow_inv_nat (x : Complex) (n : Nat) : ‖x ^ (n⁻¹ : Complex)‖ = ‖x‖ ^ 
(n⁻¹ : Real)
参数：x : Complex；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Complex.norm_cpow_real`：norm_cpow_real (x : Complex) (y : Real) : ‖x ^ (
y : Complex)‖ = ‖x‖ ^ y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Complex.ofReal_inv`：ofReal_inv (r : Real) : ((r⁻¹ : Real) : Complex) = (
r : Complex)⁻¹
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem norm_cpow_inv_nat (x : ℂ) (n : ℕ) : ‖x ^ (n⁻¹ : ℂ)‖ = ‖x‖ ^ (n⁻¹ : ℝ) := by
  rw [← norm_cpow_real]; simp
/-
**Complex.norm_cpow_eq_rpow_re_of_pos** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：norm_cpow_eq_rpow_re_of_pos {x : Real} (hx : 0 < x) (y : Complex) : ‖(x : 
Complex) ^ y‖ = x ^ y.re
参数：hx : 0 < x；y : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Complex.norm_cpow_of_ne_zero`：norm_cpow_of_ne_zero {z : Complex} (hz : z
 != 0) (w : Complex) : ‖z ^ w‖ = ‖z‖ ^ w.re / Real.exp (arg z * im w)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Complex.ofReal_ne_zero`：ofReal_ne_zero {z : Real} : (z : Complex) != 0 ↔
 z != 0
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Complex.arg_ofReal_of_nonneg`：arg_ofReal_of_nonneg {x : Real} (hx : 0 <=
 x) : arg x = 0
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Real.exp_zero`：exp_zero : exp 0 = 1
· 使用定理 `div_one`：div_one (a : G) : a / 1 = a
· 使用定理 `Complex.norm_of_nonneg`：∀ {r : ℝ}, 0 ≤ r → ‖↑r‖ = r
-/
theorem norm_cpow_eq_rpow_re_of_pos {x : ℝ} (hx : 0 < x) (y : ℂ) : ‖(x : ℂ) ^ y‖ = x ^ y.re := by
  rw [norm_cpow_of_ne_zero (ofReal_ne_zero.mpr hx.ne'), arg_ofReal_of_nonneg hx.le,
    zero_mul, Real.exp_zero, div_one, Complex.norm_of_nonneg hx.le]
/-
**Complex.norm_cpow_eq_rpow_re_of_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：norm_cpow_eq_rpow_re_of_nonneg {x : Real} (hx : 0 <= x) {y : Complex} (hy 
: re y != 0) : ‖(x : Complex) ^ y‖ = x ^ re y
参数：hx : 0 <= x；hy : re y != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Complex.norm_cpow_of_imp`：norm_cpow_of_imp {z w : Complex} (h : z = 0 ->
 w.re = 0 -> w = 0) : ‖z ^ w‖ = ‖z‖ ^ w.re / Real.exp (arg z * im w)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `Complex.norm_real`：norm_real (r : Real) : ‖(r : Complex)‖ = ‖r‖
· 使用定理 `abs_of_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α]
 {a : α} [AddLeftMono α], 0 ≤ a → |a| = a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Complex.arg_ofReal_of_nonneg`：arg_ofReal_of_nonneg {x : Real} (hx : 0 <=
 x) : arg x = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Real.exp_zero`：exp_zero : exp 0 = 1
· 使用定理 `div_one`：div_one (a : G) : a / 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem norm_cpow_eq_rpow_re_of_nonneg {x : ℝ} (hx : 0 ≤ x) {y : ℂ} (hy : re y ≠ 0) :
    ‖(x : ℂ) ^ y‖ = x ^ re y := by
  rw [norm_cpow_of_imp] <;> simp [*, arg_ofReal_of_nonneg, abs_of_nonneg]

open Filter in
/-
**Complex.norm_ofReal_cpow_eventually_eq_atTop** 是 Mathlib 中的一个引理，位于命名空间 `Comple
x`。
形式化陈述：norm_ofReal_cpow_eventually_eq_atTop (c : Complex) : (fun t : Real => ‖(t 
: Complex) ^ c‖) =ᶠ[atTop] fun t => t ^ c.re
参数：c : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.eventually_gt_atTop`：eventually_gt_atTop [Preorder α] [NoTopOrder
 α] (a : α) : forallᶠ x in atTop, a < x
· 使用定理 `instNoTopOrderOfNoMaxOrder`：∀ {α : Type u_1} [inst : Preorder α] [NoMaxO
rder α], NoTopOrder α
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Complex.norm_cpow_eq_rpow_re_of_pos`：norm_cpow_eq_rpow_re_of_pos {x : Re
al} (hx : 0 < x) (y : Complex) : ‖(x : Complex) ^ y‖ = x ^ y.re
-/
lemma norm_ofReal_cpow_eventually_eq_atTop (c : ℂ) :
    (fun t : ℝ ↦ ‖(t : ℂ) ^ c‖) =ᶠ[atTop] fun t ↦ t ^ c.re := by
  filter_upwards [eventually_gt_atTop 0] with t ht
  rw [norm_cpow_eq_rpow_re_of_pos ht]
/-
**Complex.norm_natCast_cpow_of_re_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 `Complex`。
形式化陈述：norm_natCast_cpow_of_re_ne_zero (n : Nat) {s : Complex} (hs : s.re != 0) :
 ‖(n : Complex) ^ s‖ = (n : Real) ^ (s.re)
参数：n : Nat；hs : s.re != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Complex.ofReal_natCast`：∀ (n : ℕ), ↑↑n = ↑n
· 使用定理 `Complex.norm_cpow_eq_rpow_re_of_nonneg`：norm_cpow_eq_rpow_re_of_nonneg {
x : Real} (hx : 0 <= x) {y : Complex} (hy : re y != 0) : ‖(x : Complex) ^ y‖ = x
 ^ re y
· 使用定理 `Nat.cast_nonneg`：cast_nonneg {α} [Semiring α] [PartialOrder α] [IsOrdere
dRing α] (n : Nat) : 0 <= (n : α)
-/
lemma norm_natCast_cpow_of_re_ne_zero (n : ℕ) {s : ℂ} (hs : s.re ≠ 0) :
    ‖(n : ℂ) ^ s‖ = (n : ℝ) ^ (s.re) := by
  rw [← ofReal_natCast, norm_cpow_eq_rpow_re_of_nonneg n.cast_nonneg hs]
/-
**Complex.norm_natCast_cpow_of_pos** 是 Mathlib 中的一个引理，位于命名空间 `Complex`。
形式化陈述：norm_natCast_cpow_of_pos {n : Nat} (hn : 0 < n) (s : Complex) : ‖(n : Comp
lex) ^ s‖ = (n : Real) ^ (s.re)
参数：hn : 0 < n；s : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Complex.ofReal_natCast`：∀ (n : ℕ), ↑↑n = ↑n
· 使用定理 `Complex.norm_cpow_eq_rpow_re_of_pos`：norm_cpow_eq_rpow_re_of_pos {x : Re
al} (hx : 0 < x) (y : Complex) : ‖(x : Complex) ^ y‖ = x ^ y.re
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.cast_pos`：cast_pos {α} [Semiring α] [PartialOrder α] [IsOrderedRing 
α] [Nontrivial α] {n : Nat} : (0 : α) < n ↔ 0 < n
-/
lemma norm_natCast_cpow_of_pos {n : ℕ} (hn : 0 < n) (s : ℂ) :
    ‖(n : ℂ) ^ s‖ = (n : ℝ) ^ (s.re) := by
  rw [← ofReal_natCast, norm_cpow_eq_rpow_re_of_pos (Nat.cast_pos.mpr hn) _]
/-
**Complex.norm_natCast_cpow_pos_of_pos** 是 Mathlib 中的一个引理，位于命名空间 `Complex`。
形式化陈述：norm_natCast_cpow_pos_of_pos {n : Nat} (hn : 0 < n) (s : Complex) : 0 < ‖(
n : Complex) ^ s‖
参数：hn : 0 < n；s : Complex。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.rpow_pos_of_pos`：rpow_pos_of_pos {x : Real} (hx : 0 < x) (y : Real)
 : 0 < x ^ y
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.cast_pos`：cast_pos {α} [Semiring α] [PartialOrder α] [IsOrderedRing 
α] [Nontrivial α] {n : Nat} : (0 : α) < n ↔ 0 < n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Complex.norm_natCast_cpow_of_pos`：norm_natCast_cpow_of_pos {n : Nat} (hn
 : 0 < n) (s : Complex) : ‖(n : Complex) ^ s‖ = (n : Real) ^ (s.re)
-/
lemma norm_natCast_cpow_pos_of_pos {n : ℕ} (hn : 0 < n) (s : ℂ) : 0 < ‖(n : ℂ) ^ s‖ :=
  (norm_natCast_cpow_of_pos hn _).symm ▸ Real.rpow_pos_of_pos (Nat.cast_pos.mpr hn) _
/-
**Complex.cpow_mul_ofReal_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：cpow_mul_ofReal_nonneg {x : Real} (hx : 0 <= x) (y : Real) (z : Complex) :
 (x : Complex) ^ (↑y * z) = (↑(x ^ y) : Complex) ^ z
参数：hx : 0 <= x；y : Real；z : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Complex.cpow_mul`：cpow_mul {x y : Complex} (z : Complex) (h₁ : -π < (log
 x * y).im) (h₂ : (log x * y).im <= π) : x ^ (y * z) = (x ^ y) ^ z
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Complex.ofReal_log`：ofReal_log {x : Real} (hx : 0 <= x) : (x.log : Compl
ex) = log x
· 使用定理 `Complex.ofReal_mul`：ofReal_mul (r s : Real) : ((r * s : Real) : Complex)
 = r * s
· 使用定理 `Complex.ofReal_im`：ofReal_im (r : Real) : (r : Complex).im = 0
· 使用定理 `neg_lt_zero`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [AddLeft
StrictMono α] {a : α}, -a < 0 ↔ 0 < a
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Real.pi_pos`：pi_pos : 0 < π
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Complex.ofReal_cpow`：ofReal_cpow {x : Real} (hx : 0 <= x) (y : Real) : (
(x ^ y : Real) : Complex) = (x : Complex) ^ (y : Complex)
-/
theorem cpow_mul_ofReal_nonneg {x : ℝ} (hx : 0 ≤ x) (y : ℝ) (z : ℂ) :
    (x : ℂ) ^ (↑y * z) = (↑(x ^ y) : ℂ) ^ z := by
  rw [cpow_mul, ofReal_cpow hx]
  · rw [← ofReal_log hx, ← ofReal_mul, ofReal_im, neg_lt_zero]; exact Real.pi_pos
  · rw [← ofReal_log hx, ← ofReal_mul, ofReal_im]; exact Real.pi_pos.le

end Complex

/-! ### Positivity extension -/

namespace Mathlib.Meta.Positivity
open Lean Meta Qq

/-- Extension for the `positivity` tactic: exponentiation by a real number is positive (namely 1)
when the exponent is zero. The other cases are done in `evalRpow`. -/
@[positivity (_ : ℝ) ^ (0 : ℝ)]
meta def evalRpowZero : PositivityExt where eval {u α} _ pα? e :=
  match pα? with | none => pure .none | some _ => do
  match u, α, e with
  | 0, ~q(ℝ), ~q($a ^ (0 : ℝ)) =>
    assertInstancesCommute
    pure (.positive q(Real.rpow_zero_pos $a))
  | _, _, _ => throwError "not Real.rpow"

/-- Extension for the `positivity` tactic: exponentiation by a real number is nonnegative when
the base is nonnegative and positive when the base is positive. -/
@[positivity (_ : ℝ) ^ (_ : ℝ)]
meta def evalRpow : PositivityExt where eval {u α} _zα pα? e :=
  match pα? with | none => pure .none | some _ => do
  match u, α, e with
  | 0, ~q(ℝ), ~q($a ^ ($b : ℝ)) =>
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

/-!
## Further algebraic properties of `rpow`
-/


namespace Real

variable {x y z : ℝ} {n : ℕ}

/-
**Real.rpow_mul** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：rpow_mul {x : Real} (hx : 0 <= x) (y z : Real) : x ^ (y * z) = (x ^ y) ^ z
参数：hx : 0 <= x；y z : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Complex.ofReal_inj`：ofReal_inj {z w : Real} : (z : Complex) = w ↔ z = w
· 使用定理 `Complex.ofReal_cpow`：ofReal_cpow {x : Real} (hx : 0 <= x) (y : Real) : (
(x ^ y : Real) : Complex) = (x : Complex) ^ (y : Complex)
· 使用定理 `Real.rpow_nonneg`：rpow_nonneg {x : Real} (hx : 0 <= x) (y : Real) : 0 <=
 x ^ y
· 使用定理 `Complex.ofReal_mul`：ofReal_mul (r s : Real) : ((r * s : Real) : Complex)
 = r * s
· 使用定理 `Complex.cpow_mul`：cpow_mul {x y : Complex} (z : Complex) (h₁ : -π < (log
 x * y).im) (h₂ : (log x * y).im <= π) : x ^ (y * z) = (x ^ y) ^ z
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Complex.ofReal_log`：ofReal_log {x : Real} (hx : 0 <= x) : (x.log : Compl
ex) = log x
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Real.pi_pos`：pi_pos : 0 < π
-/
theorem rpow_mul {x : ℝ} (hx : 0 ≤ x) (y z : ℝ) : x ^ (y * z) = (x ^ y) ^ z := by
  rw [← Complex.ofReal_inj, Complex.ofReal_cpow (rpow_nonneg hx _),
      Complex.ofReal_cpow hx, Complex.ofReal_mul, Complex.cpow_mul, Complex.ofReal_cpow hx] <;>
    simp only [(Complex.ofReal_mul _ _).symm, (Complex.ofReal_log hx).symm, Complex.ofReal_im,
      neg_lt_zero, pi_pos, le_of_lt pi_pos]
/-
**Real.rpow_pow_comm** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：rpow_pow_comm {x : Real} (hx : 0 <= x) (y : Real) (n : Nat) : (x ^ y) ^ n 
= (x ^ n) ^ y
参数：hx : 0 <= x；y : Real；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.rpow_mul`：rpow_mul {x : Real} (hx : 0 <= x) (y z : Real) : x ^ (y *
 z) = (x ^ y) ^ z
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma rpow_pow_comm {x : ℝ} (hx : 0 ≤ x) (y : ℝ) (n : ℕ) : (x ^ y) ^ n = (x ^ n) ^ y := by
  simp_rw [← rpow_natCast, ← rpow_mul hx, mul_comm y]
/-
**Real.rpow_zpow_comm** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：rpow_zpow_comm {x : Real} (hx : 0 <= x) (y : Real) (n : Int) : (x ^ y) ^ n
 = (x ^ n) ^ y
参数：hx : 0 <= x；y : Real；n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.rpow_mul`：rpow_mul {x : Real} (hx : 0 <= x) (y z : Real) : x ^ (y *
 z) = (x ^ y) ^ z
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma rpow_zpow_comm {x : ℝ} (hx : 0 ≤ x) (y : ℝ) (n : ℤ) : (x ^ y) ^ n = (x ^ n) ^ y := by
  simp_rw [← rpow_intCast, ← rpow_mul hx, mul_comm y]
/-
**Real.rpow_add_intCast** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：rpow_add_intCast {x : Real} (hx : x != 0) (y : Real) (n : Int) : x ^ (y + 
n) = x ^ y * x ^ n
参数：hx : x != 0；y : Real；n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.rpow_def`：rpow_def (x y : Real) : x ^ y = ((x : Complex) ^ (y : Com
plex)).re
· 使用定理 `Complex.ofReal_add`：ofReal_add (r s : Real) : ((r + s : Real) : Complex)
 = r + s
· 使用定理 `Complex.cpow_add`：cpow_add {x : Complex} (y z : Complex) (hx : x != 0) :
 x ^ (y + z) = x ^ y * x ^ z
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Complex.ofReal_ne_zero`：ofReal_ne_zero {z : Real} : (z : Complex) != 0 ↔
 z != 0
· 使用定理 `Complex.ofReal_intCast`：∀ (n : ℤ), ↑↑n = ↑n
· 使用定理 `Complex.cpow_intCast`：cpow_intCast (x : Complex) (n : Int) : x ^ (n : Co
mplex) = x ^ n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Complex.ofReal_zpow`：ofReal_zpow (r : Real) (n : Int) : ((r ^ n : Real) 
: Complex) = (r : Complex) ^ n
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Complex.re_ofReal_mul`：re_ofReal_mul (r : Real) (z : Complex) : (r * z).
re = r * z.re
-/
lemma rpow_add_intCast {x : ℝ} (hx : x ≠ 0) (y : ℝ) (n : ℤ) : x ^ (y + n) = x ^ y * x ^ n := by
  rw [rpow_def, rpow_def, Complex.ofReal_add,
    Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hx), Complex.ofReal_intCast,
    Complex.cpow_intCast, ← Complex.ofReal_zpow, mul_comm, Complex.re_ofReal_mul, mul_comm]
/-
**Real.rpow_add_natCast** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：rpow_add_natCast {x : Real} (hx : x != 0) (y : Real) (n : Nat) : x ^ (y + 
n) = x ^ y * x ^ n
参数：hx : x != 0；y : Real；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用定理 `zpow_natCast`：zpow_natCast (a : G) : forall n : Nat, a ^ (n : Int) = a ^
 n | 0 => (zpow_zero _).trans (pow_zero _).symm | n + 1 => calc a ^ (↑(n + 1) : 
In…
· 使用引理 `Real.rpow_add_intCast`：rpow_add_intCast {x : Real} (hx : x != 0) (y : Re
al) (n : Int) : x ^ (y + n) = x ^ y * x ^ n
-/
lemma rpow_add_natCast {x : ℝ} (hx : x ≠ 0) (y : ℝ) (n : ℕ) : x ^ (y + n) = x ^ y * x ^ n := by
  simpa using rpow_add_intCast hx y n
/-
**Real.rpow_sub_intCast** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：rpow_sub_intCast {x : Real} (hx : x != 0) (y : Real) (n : Int) : x ^ (y - 
n) = x ^ y / x ^ n
参数：hx : x != 0；y : Real；n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.cast_neg`：∀ {R : Type u} [inst : AddGroupWithOne R] (n : ℤ), ↑(-n) =
 -↑n
· 使用定理 `zpow_neg`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℤ), a 
^ (-n) = (a ^ n)⁻¹
· 使用引理 `Real.rpow_add_intCast`：rpow_add_intCast {x : Real} (hx : x != 0) (y : Re
al) (n : Int) : x ^ (y + n) = x ^ y * x ^ n
-/
lemma rpow_sub_intCast {x : ℝ} (hx : x ≠ 0) (y : ℝ) (n : ℤ) : x ^ (y - n) = x ^ y / x ^ n := by
  simpa using! rpow_add_intCast hx y (-n)
/-
**Real.rpow_sub_natCast** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：rpow_sub_natCast {x : Real} (hx : x != 0) (y : Real) (n : Nat) : x ^ (y - 
n) = x ^ y / x ^ n
参数：hx : x != 0；y : Real；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用定理 `zpow_natCast`：zpow_natCast (a : G) : forall n : Nat, a ^ (n : Int) = a ^
 n | 0 => (zpow_zero _).trans (pow_zero _).symm | n + 1 => calc a ^ (↑(n + 1) : 
In…
· 使用引理 `Real.rpow_sub_intCast`：rpow_sub_intCast {x : Real} (hx : x != 0) (y : Re
al) (n : Int) : x ^ (y - n) = x ^ y / x ^ n
-/
lemma rpow_sub_natCast {x : ℝ} (hx : x ≠ 0) (y : ℝ) (n : ℕ) : x ^ (y - n) = x ^ y / x ^ n := by
  simpa using rpow_sub_intCast hx y n
/-
**Real.rpow_add_intCast'** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：rpow_add_intCast' (hx : 0 <= x) {n : Int} (h : y + n != 0) : x ^ (y + n) =
 x ^ y * x ^ n
参数：hx : 0 <= x；h : y + n != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.rpow_add'`：rpow_add' (hx : 0 <= x) (h : y + z != 0) : x ^ (y + z) =
 x ^ y * x ^ z
· 使用定理 `Real.rpow_intCast`：rpow_intCast (x : Real) (n : Int) : x ^ (n : Real) = 
x ^ n
-/
lemma rpow_add_intCast' (hx : 0 ≤ x) {n : ℤ} (h : y + n ≠ 0) : x ^ (y + n) = x ^ y * x ^ n := by
  rw [rpow_add' hx h, rpow_intCast]
/-
**Real.rpow_add_natCast'** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：rpow_add_natCast' (hx : 0 <= x) (h : y + n != 0) : x ^ (y + n) = x ^ y * x
 ^ n
参数：hx : 0 <= x；h : y + n != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.rpow_add'`：rpow_add' (hx : 0 <= x) (h : y + z != 0) : x ^ (y + z) =
 x ^ y * x ^ z
· 使用定理 `Real.rpow_natCast`：rpow_natCast (x : Real) (n : Nat) : x ^ (n : Real) = 
x ^ n
-/
lemma rpow_add_natCast' (hx : 0 ≤ x) (h : y + n ≠ 0) : x ^ (y + n) = x ^ y * x ^ n := by
  rw [rpow_add' hx h, rpow_natCast]
/-
**Real.rpow_sub_intCast'** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：rpow_sub_intCast' (hx : 0 <= x) {n : Int} (h : y - n != 0) : x ^ (y - n) =
 x ^ y / x ^ n
参数：hx : 0 <= x；h : y - n != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.rpow_sub'`：rpow_sub' {x : Real} (hx : 0 <= x) {y z : Real} (h : y -
 z != 0) : x ^ (y - z) = x ^ y / x ^ z
· 使用定理 `Real.rpow_intCast`：rpow_intCast (x : Real) (n : Int) : x ^ (n : Real) = 
x ^ n
-/
lemma rpow_sub_intCast' (hx : 0 ≤ x) {n : ℤ} (h : y - n ≠ 0) : x ^ (y - n) = x ^ y / x ^ n := by
  rw [rpow_sub' hx h, rpow_intCast]
/-
**Real.rpow_sub_natCast'** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：rpow_sub_natCast' (hx : 0 <= x) (h : y - n != 0) : x ^ (y - n) = x ^ y / x
 ^ n
参数：hx : 0 <= x；h : y - n != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.rpow_sub'`：rpow_sub' {x : Real} (hx : 0 <= x) {y z : Real} (h : y -
 z != 0) : x ^ (y - z) = x ^ y / x ^ z
· 使用定理 `Real.rpow_natCast`：rpow_natCast (x : Real) (n : Nat) : x ^ (n : Real) = 
x ^ n
-/
lemma rpow_sub_natCast' (hx : 0 ≤ x) (h : y - n ≠ 0) : x ^ (y - n) = x ^ y / x ^ n := by
  rw [rpow_sub' hx h, rpow_natCast]
/-
**Real.rpow_add_one** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：rpow_add_one {x : Real} (hx : x != 0) (y : Real) : x ^ (y + 1) = x ^ y * x
参数：hx : x != 0；y : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用引理 `Real.rpow_add_natCast`：rpow_add_natCast {x : Real} (hx : x != 0) (y : Re
al) (n : Nat) : x ^ (y + n) = x ^ y * x ^ n
-/
theorem rpow_add_one {x : ℝ} (hx : x ≠ 0) (y : ℝ) : x ^ (y + 1) = x ^ y * x := by
  simpa using rpow_add_natCast hx y 1
/-
**Real.rpow_sub_one** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：rpow_sub_one {x : Real} (hx : x != 0) (y : Real) : x ^ (y - 1) = x ^ y / x
参数：hx : x != 0；y : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用引理 `Real.rpow_sub_natCast`：rpow_sub_natCast {x : Real} (hx : x != 0) (y : Re
al) (n : Nat) : x ^ (y - n) = x ^ y / x ^ n
-/
theorem rpow_sub_one {x : ℝ} (hx : x ≠ 0) (y : ℝ) : x ^ (y - 1) = x ^ y / x := by
  simpa using rpow_sub_natCast hx y 1
/-
**Real.rpow_add_one'** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：rpow_add_one' (hx : 0 <= x) (h : y + 1 != 0) : x ^ (y + 1) = x ^ y * x
参数：hx : 0 <= x；h : y + 1 != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.rpow_add'`：rpow_add' (hx : 0 <= x) (h : y + z != 0) : x ^ (y + z) =
 x ^ y * x ^ z
· 使用定理 `Real.rpow_one`：rpow_one (x : Real) : x ^ (1 : Real) = x
-/
lemma rpow_add_one' (hx : 0 ≤ x) (h : y + 1 ≠ 0) : x ^ (y + 1) = x ^ y * x := by
  rw [rpow_add' hx h, rpow_one]
/-
**Real.rpow_one_add'** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：rpow_one_add' (hx : 0 <= x) (h : 1 + y != 0) : x ^ (1 + y) = x * x ^ y
参数：hx : 0 <= x；h : 1 + y != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.rpow_add'`：rpow_add' (hx : 0 <= x) (h : y + z != 0) : x ^ (y + z) =
 x ^ y * x ^ z
· 使用定理 `Real.rpow_one`：rpow_one (x : Real) : x ^ (1 : Real) = x
-/
lemma rpow_one_add' (hx : 0 ≤ x) (h : 1 + y ≠ 0) : x ^ (1 + y) = x * x ^ y := by
  rw [rpow_add' hx h, rpow_one]
/-
**Real.rpow_sub_one'** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：rpow_sub_one' (hx : 0 <= x) (h : y - 1 != 0) : x ^ (y - 1) = x ^ y / x
参数：hx : 0 <= x；h : y - 1 != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.rpow_sub'`：rpow_sub' {x : Real} (hx : 0 <= x) {y z : Real} (h : y -
 z != 0) : x ^ (y - z) = x ^ y / x ^ z
· 使用定理 `Real.rpow_one`：rpow_one (x : Real) : x ^ (1 : Real) = x
-/
lemma rpow_sub_one' (hx : 0 ≤ x) (h : y - 1 ≠ 0) : x ^ (y - 1) = x ^ y / x := by
  rw [rpow_sub' hx h, rpow_one]
/-
**Real.rpow_one_sub'** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：rpow_one_sub' (hx : 0 <= x) (h : 1 - y != 0) : x ^ (1 - y) = x / x ^ y
参数：hx : 0 <= x；h : 1 - y != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.rpow_sub'`：rpow_sub' {x : Real} (hx : 0 <= x) {y z : Real} (h : y -
 z != 0) : x ^ (y - z) = x ^ y / x ^ z
· 使用定理 `Real.rpow_one`：rpow_one (x : Real) : x ^ (1 : Real) = x
-/
lemma rpow_one_sub' (hx : 0 ≤ x) (h : 1 - y ≠ 0) : x ^ (1 - y) = x / x ^ y := by
  rw [rpow_sub' hx h, rpow_one]
/-
**Real.rpow_two** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：rpow_two (x : Real) : x ^ (2 : Real) = x ^ 2
参数：x : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Real.rpow_ofNat`：rpow_ofNat (x : Real) (n : Nat) [n.AtLeastTwo] : x ^ (o
fNat(n) : Real) = x ^ (ofNat(n) : Nat)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem rpow_two (x : ℝ) : x ^ (2 : ℝ) = x ^ 2 := by
  simp
/-
**Real.rpow_neg_one** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：rpow_neg_one (x : Real) : x ^ (-1 : Real) = x⁻¹
参数：x : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.rpow_neg_eq_inv_rpow`：rpow_neg_eq_inv_rpow (x y : Real) : x ^ (-y) 
= x⁻¹ ^ y
· 使用定理 `Real.rpow_one`：rpow_one (x : Real) : x ^ (1 : Real) = x
-/
theorem rpow_neg_one (x : ℝ) : x ^ (-1 : ℝ) = x⁻¹ := by
  rw [rpow_neg_eq_inv_rpow, rpow_one]

-- TODO: fix non-terminal simp (acting on three goals, with different simp sets, leaving two)
set_option linter.flexible false in
/-
**Real.mul_rpow** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：mul_rpow (hx : 0 <= x) (hy : 0 <= y) : (x * y) ^ z = x ^ z * y ^ z
参数：hx : 0 <= x；hy : 0 <= y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.rpow_def_of_nonneg`：rpow_def_of_nonneg {x : Real} (hx : 0 <= x) (y 
: Real) : x ^ y = if x = 0 then if y = 0 then 1 else 0 else exp (log x * y)
· 使用定理 `mul_nonneg`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 :
 Preorder α] [PosMulMono α], 0 ≤ a → 0 ≤ b → 0 ≤ a * b
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Real.rpow_zero`：rpow_zero (x : Real) : x ^ (0 : Real) = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `Real.log_mul`：log_mul (hx : x != 0) (hy : y != 0) : log (x * y) = log x 
+ log y
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `add_mul`：add_mul {d : R} (_ : (a₁ : R) * b = c₁) (_ : a₂ * b = c₂) (_ : 
c₁ + c₂ = d) : (a₁ + a₂) * b = d
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
· 使用定理 `Real.exp_add`：∀ (x y : ℝ), Real.exp (x + y) = Real.exp x * Real.exp y
· 使用定理 `Real.rpow_def_of_pos`：rpow_def_of_pos {x : Real} (hx : 0 < x) (y : Real)
 : x ^ y = exp (log x * y)
· 使用定理 `LE.le.lt_of_ne'`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, b ≤
 a → a ≠ b → b < a
-/
theorem mul_rpow (hx : 0 ≤ x) (hy : 0 ≤ y) : (x * y) ^ z = x ^ z * y ^ z := by
  iterate 2 rw [Real.rpow_def_of_nonneg]; split_ifs with h_ifs <;> simp_all
  · rw [log_mul ‹_› ‹_›, add_mul, exp_add, rpow_def_of_pos (hy.lt_of_ne' ‹_›)]
  all_goals positivity
/-
**Real.inv_rpow** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：inv_rpow (hx : 0 <= x) (y : Real) : x⁻¹ ^ y = (x ^ y)⁻¹
参数：hx : 0 <= x；y : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.rpow_neg_eq_inv_rpow`：rpow_neg_eq_inv_rpow (x y : Real) : x ^ (-y) 
= x⁻¹ ^ y
· 使用定理 `Real.rpow_neg`：rpow_neg {x : Real} (hx : 0 <= x) (y : Real) : x ^ (-y) =
 (x ^ y)⁻¹
-/
theorem inv_rpow (hx : 0 ≤ x) (y : ℝ) : x⁻¹ ^ y = (x ^ y)⁻¹ := by
  rw [← rpow_neg_eq_inv_rpow, rpow_neg hx]
/-
**Real.div_rpow** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：div_rpow (hx : 0 <= x) (hy : 0 <= y) (z : Real) : (x / y) ^ z = x ^ z / y 
^ z
参数：hx : 0 <= x；hy : 0 <= y；z : Real。
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
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `Real.mul_rpow`：mul_rpow (hx : 0 <= x) (hy : 0 <= y) : (x * y) ^ z = x ^ 
z * y ^ z
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `inv_nonneg`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] [inst_1 : Partia
lOrder G₀] [PosMulReflectLT G₀] {a : G₀}, 0 ≤ a⁻¹ ↔ 0 ≤ a
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Real.inv_rpow`：inv_rpow (hx : 0 <= x) (y : Real) : x⁻¹ ^ y = (x ^ y)⁻¹
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem div_rpow (hx : 0 ≤ x) (hy : 0 ≤ y) (z : ℝ) : (x / y) ^ z = x ^ z / y ^ z := by
  simp only [div_eq_mul_inv, mul_rpow hx (inv_nonneg.2 hy), inv_rpow hy]

@[push low] /- Lower priority than `log_pow` and `log_zpow`.
This is because otherwise the `pull` tactic will use `log_rpow` in places where it should
use `log_pow` or `log_zpow`. -/
/-
**Real.log_rpow** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：log_rpow {x : Real} (hx : 0 < x) (y : Real) : log (x ^ y) = y * log x
参数：hx : 0 < x；y : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.exp_injective`：exp_injective : Function.Injective exp
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.exp_log`：exp_log (hx : 0 < x) : exp (log x) = x
· 使用定理 `Real.rpow_pos_of_pos`：rpow_pos_of_pos {x : Real} (hx : 0 < x) (y : Real)
 : 0 < x ^ y
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Real.rpow_def_of_pos`：rpow_def_of_pos {x : Real} (hx : 0 < x) (y : Real)
 : x ^ y = exp (log x * y)
· 使用定理 `Real.exp_pos`：exp_pos (x : Real) : 0 < exp x

--- 原说明 ---
Lower priority than `log_pow` and `log_zpow`.
This is because otherwise the `pull` tactic will use `log_rpow` in places where 
it should
use `log_pow` or `log_zpow`.
-/
theorem log_rpow {x : ℝ} (hx : 0 < x) (y : ℝ) : log (x ^ y) = y * log x := by
  apply exp_injective
  rw [exp_log (rpow_pos_of_pos hx y), ← exp_log hx, mul_comm, rpow_def_of_pos (exp_pos (log x)) y]
/-
**Real.mul_log_eq_log_iff** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：mul_log_eq_log_iff {x y z : Real} (hx : 0 < x) (hz : 0 < z) : y * log x = 
log z ↔ x ^ y = z
参数：hx : 0 < x；hz : 0 < z。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.log_injOn_pos`：log_injOn_pos : Set.InjOn log (Set.Ioi 0)
· 使用定理 `Real.rpow_pos_of_pos`：rpow_pos_of_pos {x : Real} (hx : 0 < x) (y : Real)
 : 0 < x ^ y
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Real.log_rpow`：log_rpow {x : Real} (hx : 0 < x) (y : Real) : log (x ^ y)
 = y * log x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem mul_log_eq_log_iff {x y z : ℝ} (hx : 0 < x) (hz : 0 < z) :
    y * log x = log z ↔ x ^ y = z :=
  ⟨fun h ↦ log_injOn_pos (rpow_pos_of_pos hx _) hz <| log_rpow hx _ |>.trans h,
  by rintro rfl; rw [log_rpow hx]⟩
/-
**Real.rpow_rpow_inv** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：∀ {x y : ℝ}, 0 ≤ x → y ≠ 0 → (x ^ y) ^ y⁻¹ = x
参数：x ^ y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.rpow_mul`：rpow_mul {x : Real} (hx : 0 <= x) (y z : Real) : x ^ (y *
 z) = (x ^ y) ^ z
· 使用引理 `mul_inv_cancel₀`：mul_inv_cancel₀ (h : a != 0) : a * a⁻¹ = 1
· 使用定理 `Real.rpow_one`：rpow_one (x : Real) : x ^ (1 : Real) = x
-/
@[simp] lemma rpow_rpow_inv (hx : 0 ≤ x) (hy : y ≠ 0) : (x ^ y) ^ y⁻¹ = x := by
  rw [← rpow_mul hx, mul_inv_cancel₀ hy, rpow_one]
/-
**Real.rpow_inv_rpow** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：∀ {x y : ℝ}, 0 ≤ x → y ≠ 0 → (x ^ y⁻¹) ^ y = x
参数：x ^ y⁻¹。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.rpow_mul`：rpow_mul {x : Real} (hx : 0 <= x) (y z : Real) : x ^ (y *
 z) = (x ^ y) ^ z
· 使用定理 `inv_mul_cancel₀`：inv_mul_cancel₀ (h : a != 0) : a⁻¹ * a = 1
· 使用定理 `Real.rpow_one`：rpow_one (x : Real) : x ^ (1 : Real) = x
-/
@[simp] lemma rpow_inv_rpow (hx : 0 ≤ x) (hy : y ≠ 0) : (x ^ y⁻¹) ^ y = x := by
  rw [← rpow_mul hx, inv_mul_cancel₀ hy, rpow_one]
/-
**Real.pow_rpow_inv_natCast** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：pow_rpow_inv_natCast (hx : 0 <= x) (hn : n != 0) : (x ^ n) ^ (n⁻¹ : Real) 
= x
参数：hx : 0 <= x；hn : n != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.cast_ne_zero`：cast_ne_zero {n : Nat} : (n : R) != 0 ↔ n != 0
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.rpow_natCast`：rpow_natCast (x : Real) (n : Nat) : x ^ (n : Real) = 
x ^ n
· 使用定理 `Real.rpow_mul`：rpow_mul {x : Real} (hx : 0 <= x) (y z : Real) : x ^ (y *
 z) = (x ^ y) ^ z
· 使用引理 `mul_inv_cancel₀`：mul_inv_cancel₀ (h : a != 0) : a * a⁻¹ = 1
· 使用定理 `Real.rpow_one`：rpow_one (x : Real) : x ^ (1 : Real) = x
-/
theorem pow_rpow_inv_natCast (hx : 0 ≤ x) (hn : n ≠ 0) : (x ^ n) ^ (n⁻¹ : ℝ) = x := by
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn
  rw [← rpow_natCast, ← rpow_mul hx, mul_inv_cancel₀ hn0, rpow_one]
/-
**Real.rpow_inv_natCast_pow** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：rpow_inv_natCast_pow (hx : 0 <= x) (hn : n != 0) : (x ^ (n⁻¹ : Real)) ^ n 
= x
参数：hx : 0 <= x；hn : n != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.cast_ne_zero`：cast_ne_zero {n : Nat} : (n : R) != 0 ↔ n != 0
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.rpow_natCast`：rpow_natCast (x : Real) (n : Nat) : x ^ (n : Real) = 
x ^ n
· 使用定理 `Real.rpow_mul`：rpow_mul {x : Real} (hx : 0 <= x) (y z : Real) : x ^ (y *
 z) = (x ^ y) ^ z
· 使用定理 `inv_mul_cancel₀`：inv_mul_cancel₀ (h : a != 0) : a⁻¹ * a = 1
· 使用定理 `Real.rpow_one`：rpow_one (x : Real) : x ^ (1 : Real) = x
-/
theorem rpow_inv_natCast_pow (hx : 0 ≤ x) (hn : n ≠ 0) : (x ^ (n⁻¹ : ℝ)) ^ n = x := by
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn
  rw [← rpow_natCast, ← rpow_mul hx, inv_mul_cancel₀ hn0, rpow_one]
/-
**Real.rpow_natCast_mul** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：rpow_natCast_mul (hx : 0 <= x) (n : Nat) (z : Real) : x ^ (n * z) = (x ^ n
) ^ z
参数：hx : 0 <= x；n : Nat；z : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.rpow_mul`：rpow_mul {x : Real} (hx : 0 <= x) (y z : Real) : x ^ (y *
 z) = (x ^ y) ^ z
· 使用定理 `Real.rpow_natCast`：rpow_natCast (x : Real) (n : Nat) : x ^ (n : Real) = 
x ^ n
-/
lemma rpow_natCast_mul (hx : 0 ≤ x) (n : ℕ) (z : ℝ) : x ^ (n * z) = (x ^ n) ^ z := by
  rw [rpow_mul hx, rpow_natCast]
/-
**Real.rpow_mul_natCast** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：rpow_mul_natCast (hx : 0 <= x) (y : Real) (n : Nat) : x ^ (y * n) = (x ^ y
) ^ n
参数：hx : 0 <= x；y : Real；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.rpow_mul`：rpow_mul {x : Real} (hx : 0 <= x) (y z : Real) : x ^ (y *
 z) = (x ^ y) ^ z
· 使用定理 `Real.rpow_natCast`：rpow_natCast (x : Real) (n : Nat) : x ^ (n : Real) = 
x ^ n
-/
lemma rpow_mul_natCast (hx : 0 ≤ x) (y : ℝ) (n : ℕ) : x ^ (y * n) = (x ^ y) ^ n := by
  rw [rpow_mul hx, rpow_natCast]
/-
**Real.rpow_intCast_mul** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：rpow_intCast_mul (hx : 0 <= x) (n : Int) (z : Real) : x ^ (n * z) = (x ^ n
) ^ z
参数：hx : 0 <= x；n : Int；z : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.rpow_mul`：rpow_mul {x : Real} (hx : 0 <= x) (y z : Real) : x ^ (y *
 z) = (x ^ y) ^ z
· 使用定理 `Real.rpow_intCast`：rpow_intCast (x : Real) (n : Int) : x ^ (n : Real) = 
x ^ n
-/
lemma rpow_intCast_mul (hx : 0 ≤ x) (n : ℤ) (z : ℝ) : x ^ (n * z) = (x ^ n) ^ z := by
  rw [rpow_mul hx, rpow_intCast]
/-
**Real.rpow_mul_intCast** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：rpow_mul_intCast (hx : 0 <= x) (y : Real) (n : Int) : x ^ (y * n) = (x ^ y
) ^ n
参数：hx : 0 <= x；y : Real；n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.rpow_mul`：rpow_mul {x : Real} (hx : 0 <= x) (y z : Real) : x ^ (y *
 z) = (x ^ y) ^ z
· 使用定理 `Real.rpow_intCast`：rpow_intCast (x : Real) (n : Int) : x ^ (n : Real) = 
x ^ n
-/
lemma rpow_mul_intCast (hx : 0 ≤ x) (y : ℝ) (n : ℤ) : x ^ (y * n) = (x ^ y) ^ n := by
  rw [rpow_mul hx, rpow_intCast]

/-! Note: lemmas about `(∏ i ∈ s, f i ^ r)` such as `Real.finsetProd_rpow` are proved
in `Mathlib/Analysis/SpecialFunctions/Pow/NNReal.lean` instead. -/

/-!
## Order and monotonicity
-/


@[gcongr, bound]
/-
**Real.rpow_lt_rpow** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：rpow_lt_rpow (hx : 0 <= x) (hxy : x < y) (hz : 0 < z) : x ^ z < y ^ z
参数：hx : 0 <= x；hxy : x < y；hz : 0 < z。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `le_iff_eq_or_lt`：le_iff_eq_or_lt : a <= b ↔ a = b ∨ a < b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.zero_rpow`：zero_rpow {x : Real} (h : x != 0) : (0 : Real) ^ x = 0
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Real.rpow_pos_of_pos`：rpow_pos_of_pos {x : Real} (hx : 0 < x) (y : Real)
 : 0 < x ^ y
· 使用定理 `Real.rpow_def_of_pos`：rpow_def_of_pos {x : Real} (hx : 0 < x) (y : Real)
 : x ^ y = exp (log x * y)
· 使用引理 `lt_trans`：lt_trans : a < b -> b < c -> a < c
· 使用定理 `Real.exp_lt_exp`：exp_lt_exp {x y : Real} : exp x < exp y ↔ x < y
· 使用定理 `mul_lt_mul_of_pos_right`：mul_lt_mul_of_pos_right [MulPosStrictMono α] (h
bc : b < c) (ha : 0 < a) : b * a < c * a
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `Real.log_lt_log`：log_lt_log (hx : 0 < x) (h : x < y) : log x < log y

--- 原说明 ---
## Order and monotonicity
-/
theorem rpow_lt_rpow (hx : 0 ≤ x) (hxy : x < y) (hz : 0 < z) : x ^ z < y ^ z := by
  rw [le_iff_eq_or_lt] at hx; rcases hx with hx | hx
  · rw [← hx, zero_rpow (ne_of_gt hz)]
    exact rpow_pos_of_pos (by rwa [← hx] at hxy) _
  · rw [rpow_def_of_pos hx, rpow_def_of_pos (lt_trans hx hxy), exp_lt_exp]
    exact mul_lt_mul_of_pos_right (log_lt_log hx hxy) hz
/-
**Real.strictMonoOn_rpow_Ici_of_exponent_pos** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：strictMonoOn_rpow_Ici_of_exponent_pos {r : Real} (hr : 0 < r) : StrictMono
On (fun (x : Real) => x ^ r) (Set.Ici 0)
参数：hr : 0 < r。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.rpow_lt_rpow`：rpow_lt_rpow (hx : 0 <= x) (hxy : x < y) (hz : 0 < z)
 : x ^ z < y ^ z
-/
theorem strictMonoOn_rpow_Ici_of_exponent_pos {r : ℝ} (hr : 0 < r) :
    StrictMonoOn (fun (x : ℝ) => x ^ r) (Set.Ici 0) :=
  fun _ ha _ _ hab => rpow_lt_rpow ha hab hr

@[gcongr, bound]
/-
**Real.rpow_le_rpow** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：rpow_le_rpow {x y z : Real} (h : 0 <= x) (h₁ : x <= y) (h₂ : 0 <= z) : x ^
 z <= y ^ z
参数：h : 0 <= x；h₁ : x <= y；h₂ : 0 <= z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_lt_of_le`：eq_or_lt_of_le (h : a <= b) : a = b ∨ a < b
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.rpow_zero`：rpow_zero (x : Real) : x ^ (0 : Real) = 1
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Real.rpow_lt_rpow`：rpow_lt_rpow (hx : 0 <= x) (hxy : x < y) (hz : 0 < z)
 : x ^ z < y ^ z
-/
theorem rpow_le_rpow {x y z : ℝ} (h : 0 ≤ x) (h₁ : x ≤ y) (h₂ : 0 ≤ z) : x ^ z ≤ y ^ z := by
  rcases eq_or_lt_of_le h₁ with (rfl | h₁'); · rfl
  rcases eq_or_lt_of_le h₂ with (rfl | h₂'); · simp
  exact le_of_lt (rpow_lt_rpow h h₁' h₂')
/-
**Real.monotoneOn_rpow_Ici_of_exponent_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：monotoneOn_rpow_Ici_of_exponent_nonneg {r : Real} (hr : 0 <= r) : Monotone
On (fun (x : Real) => x ^ r) (Set.Ici 0)
参数：hr : 0 <= r。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.rpow_le_rpow`：rpow_le_rpow {x y z : Real} (h : 0 <= x) (h₁ : x <= y
) (h₂ : 0 <= z) : x ^ z <= y ^ z
-/
theorem monotoneOn_rpow_Ici_of_exponent_nonneg {r : ℝ} (hr : 0 ≤ r) :
    MonotoneOn (fun (x : ℝ) => x ^ r) (Set.Ici 0) :=
  fun _ ha _ _ hab => rpow_le_rpow ha hab hr
/-
**Real.rpow_lt_rpow_of_neg** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：rpow_lt_rpow_of_neg (hx : 0 < x) (hxy : x < y) (hz : z < 0) : y ^ z < x ^ 
z
参数：hx : 0 < x；hxy : x < y；hz : z < 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `inv_lt_inv₀`：inv_lt_inv₀ (ha : 0 < a) (hb : 0 < b) : a⁻¹ < b⁻¹ ↔ b < a
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `Real.rpow_pos_of_pos`：rpow_pos_of_pos {x : Real} (hx : 0 < x) (y : Real)
 : 0 < x ^ y
· 使用定理 `Real.rpow_neg`：rpow_neg {x : Real} (hx : 0 <= x) (y : Real) : x ^ (-y) =
 (x ^ y)⁻¹
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Real.rpow_lt_rpow`：rpow_lt_rpow (hx : 0 <= x) (hxy : x < y) (hz : 0 < z)
 : x ^ z < y ^ z
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `neg_pos`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [AddLeftStri
ctMono α] {a : α}, 0 < -a ↔ a < 0
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
-/
lemma rpow_lt_rpow_of_neg (hx : 0 < x) (hxy : x < y) (hz : z < 0) : y ^ z < x ^ z := by
  have := hx.trans hxy
  rw [← inv_lt_inv₀, ← rpow_neg, ← rpow_neg]
  on_goal 1 => refine rpow_lt_rpow ?_ hxy (neg_pos.2 hz)
  all_goals positivity
/-
**Real.rpow_le_rpow_of_nonpos** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：rpow_le_rpow_of_nonpos (hx : 0 < x) (hxy : x <= y) (hz : z <= 0) : y ^ z <
= x ^ z
参数：hx : 0 < x；hxy : x <= y；hz : z <= 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `inv_le_inv₀`：inv_le_inv₀ (ha : 0 < a) (hb : 0 < b) : a⁻¹ <= b⁻¹ ↔ b <= a
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `Real.rpow_pos_of_pos`：rpow_pos_of_pos {x : Real} (hx : 0 < x) (y : Real)
 : 0 < x ^ y
· 使用定理 `Real.rpow_neg`：rpow_neg {x : Real} (hx : 0 <= x) (y : Real) : x ^ (-y) =
 (x ^ y)⁻¹
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Real.rpow_le_rpow`：rpow_le_rpow {x y z : Real} (h : 0 <= x) (h₁ : x <= y
) (h₂ : 0 <= z) : x ^ z <= y ^ z
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `neg_nonneg`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [AddLeftM
ono α] {a : α}, 0 ≤ -a ↔ a ≤ 0
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
-/
lemma rpow_le_rpow_of_nonpos (hx : 0 < x) (hxy : x ≤ y) (hz : z ≤ 0) : y ^ z ≤ x ^ z := by
  have := hx.trans_le hxy
  rw [← inv_le_inv₀, ← rpow_neg, ← rpow_neg]
  on_goal 1 => refine rpow_le_rpow ?_ hxy (neg_nonneg.2 hz)
  all_goals positivity
/-
**Real.rpow_lt_rpow_iff** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：rpow_lt_rpow_iff (hx : 0 <= x) (hy : 0 <= y) (hz : 0 < z) : x ^ z < y ^ z 
↔ x < y
参数：hx : 0 <= x；hy : 0 <= y；hz : 0 < z。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_imp_lt_of_le_imp_le`：lt_imp_lt_of_le_imp_le {β} [LinearOrder α] [Preo
rder β] {a b : α} {c d : β} (H : a <= b -> c <= d) (h : d < c) : b < a
· 使用定理 `Real.rpow_le_rpow`：rpow_le_rpow {x y z : Real} (h : 0 <= x) (h₁ : x <= y
) (h₂ : 0 <= z) : x ^ z <= y ^ z
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Real.rpow_lt_rpow`：rpow_lt_rpow (hx : 0 <= x) (hxy : x < y) (hz : 0 < z)
 : x ^ z < y ^ z
-/
theorem rpow_lt_rpow_iff (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 < z) : x ^ z < y ^ z ↔ x < y :=
  ⟨lt_imp_lt_of_le_imp_le fun h ↦ by gcongr, fun h ↦ by gcongr⟩
/-
**Real.rpow_le_rpow_iff** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：rpow_le_rpow_iff (hx : 0 <= x) (hy : 0 <= y) (hz : 0 < z) : x ^ z <= y ^ z
 ↔ x <= y
参数：hx : 0 <= x；hy : 0 <= y；hz : 0 < z。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `le_iff_le_iff_lt_iff_lt`：le_iff_le_iff_lt_iff_lt {β} [LinearOrder α] [Li
nearOrder β] {a b : α} {c d : β} : (a <= b ↔ c <= d) ↔ (b < a ↔ d < c)
· 使用定理 `Real.rpow_lt_rpow_iff`：rpow_lt_rpow_iff (hx : 0 <= x) (hy : 0 <= y) (hz 
: 0 < z) : x ^ z < y ^ z ↔ x < y
-/
theorem rpow_le_rpow_iff (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 < z) : x ^ z ≤ y ^ z ↔ x ≤ y :=
  le_iff_le_iff_lt_iff_lt.2 <| rpow_lt_rpow_iff hy hx hz
/-
**Real.rpow_lt_rpow_iff_of_neg** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：rpow_lt_rpow_iff_of_neg (hx : 0 < x) (hy : 0 < y) (hz : z < 0) : x ^ z < y
 ^ z ↔ y < x
参数：hx : 0 < x；hy : 0 < y；hz : z < 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_imp_lt_of_le_imp_le`：lt_imp_lt_of_le_imp_le {β} [LinearOrder α] [Preo
rder β] {a b : α} {c d : β} (H : a <= b -> c <= d) (h : d < c) : b < a
· 使用引理 `Real.rpow_le_rpow_of_nonpos`：rpow_le_rpow_of_nonpos (hx : 0 < x) (hxy : 
x <= y) (hz : z <= 0) : y ^ z <= x ^ z
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用引理 `Real.rpow_lt_rpow_of_neg`：rpow_lt_rpow_of_neg (hx : 0 < x) (hxy : x < y)
 (hz : z < 0) : y ^ z < x ^ z
-/
lemma rpow_lt_rpow_iff_of_neg (hx : 0 < x) (hy : 0 < y) (hz : z < 0) : x ^ z < y ^ z ↔ y < x :=
  ⟨lt_imp_lt_of_le_imp_le fun h ↦ rpow_le_rpow_of_nonpos hx h hz.le,
    fun h ↦ rpow_lt_rpow_of_neg hy h hz⟩
/-
**Real.rpow_le_rpow_iff_of_neg** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：rpow_le_rpow_iff_of_neg (hx : 0 < x) (hy : 0 < y) (hz : z < 0) : x ^ z <= 
y ^ z ↔ y <= x
参数：hx : 0 < x；hy : 0 < y；hz : z < 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `le_iff_le_iff_lt_iff_lt`：le_iff_le_iff_lt_iff_lt {β} [LinearOrder α] [Li
nearOrder β] {a b : α} {c d : β} : (a <= b ↔ c <= d) ↔ (b < a ↔ d < c)
· 使用引理 `Real.rpow_lt_rpow_iff_of_neg`：rpow_lt_rpow_iff_of_neg (hx : 0 < x) (hy :
 0 < y) (hz : z < 0) : x ^ z < y ^ z ↔ y < x
-/
lemma rpow_le_rpow_iff_of_neg (hx : 0 < x) (hy : 0 < y) (hz : z < 0) : x ^ z ≤ y ^ z ↔ y ≤ x :=
  le_iff_le_iff_lt_iff_lt.2 <| rpow_lt_rpow_iff_of_neg hy hx hz
/-
**Real.le_rpow_inv_iff_of_pos** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：le_rpow_inv_iff_of_pos (hx : 0 <= x) (hy : 0 <= y) (hz : 0 < z) : x <= y ^
 z⁻¹ ↔ x ^ z <= y
参数：hx : 0 <= x；hy : 0 <= y；hz : 0 < z。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.rpow_le_rpow_iff`：rpow_le_rpow_iff (hx : 0 <= x) (hy : 0 <= y) (hz 
: 0 < z) : x ^ z <= y ^ z ↔ x <= y
· 使用定理 `Real.rpow_nonneg`：rpow_nonneg {x : Real} (hx : 0 <= x) (y : Real) : 0 <=
 x ^ y
· 使用定理 `Real.rpow_inv_rpow`：∀ {x y : ℝ}, 0 ≤ x → y ≠ 0 → (x ^ y⁻¹) ^ y = x
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma le_rpow_inv_iff_of_pos (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 < z) : x ≤ y ^ z⁻¹ ↔ x ^ z ≤ y := by
  rw [← rpow_le_rpow_iff hx _ hz, rpow_inv_rpow] <;> positivity
/-
**Real.rpow_inv_le_iff_of_pos** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：rpow_inv_le_iff_of_pos (hx : 0 <= x) (hy : 0 <= y) (hz : 0 < z) : x ^ z⁻¹ 
<= y ↔ x <= y ^ z
参数：hx : 0 <= x；hy : 0 <= y；hz : 0 < z。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.rpow_le_rpow_iff`：rpow_le_rpow_iff (hx : 0 <= x) (hy : 0 <= y) (hz 
: 0 < z) : x ^ z <= y ^ z ↔ x <= y
· 使用定理 `Real.rpow_nonneg`：rpow_nonneg {x : Real} (hx : 0 <= x) (y : Real) : 0 <=
 x ^ y
· 使用定理 `Real.rpow_inv_rpow`：∀ {x y : ℝ}, 0 ≤ x → y ≠ 0 → (x ^ y⁻¹) ^ y = x
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma rpow_inv_le_iff_of_pos (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 < z) : x ^ z⁻¹ ≤ y ↔ x ≤ y ^ z := by
  rw [← rpow_le_rpow_iff _ hy hz, rpow_inv_rpow] <;> positivity
/-
**Real.lt_rpow_inv_iff_of_pos** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：lt_rpow_inv_iff_of_pos (hx : 0 <= x) (hy : 0 <= y) (hz : 0 < z) : x < y ^ 
z⁻¹ ↔ x ^ z < y
参数：hx : 0 <= x；hy : 0 <= y；hz : 0 < z。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_iff_lt_of_le_iff_le`：lt_iff_lt_of_le_iff_le {β} [LinearOrder α] [Line
arOrder β] {a b : α} {c d : β} (H : a <= b ↔ c <= d) : b < a ↔ d < c
· 使用引理 `Real.rpow_inv_le_iff_of_pos`：rpow_inv_le_iff_of_pos (hx : 0 <= x) (hy : 
0 <= y) (hz : 0 < z) : x ^ z⁻¹ <= y ↔ x <= y ^ z
-/
lemma lt_rpow_inv_iff_of_pos (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 < z) : x < y ^ z⁻¹ ↔ x ^ z < y :=
  lt_iff_lt_of_le_iff_le <| rpow_inv_le_iff_of_pos hy hx hz
/-
**Real.rpow_inv_lt_iff_of_pos** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：rpow_inv_lt_iff_of_pos (hx : 0 <= x) (hy : 0 <= y) (hz : 0 < z) : x ^ z⁻¹ 
< y ↔ x < y ^ z
参数：hx : 0 <= x；hy : 0 <= y；hz : 0 < z。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_iff_lt_of_le_iff_le`：lt_iff_lt_of_le_iff_le {β} [LinearOrder α] [Line
arOrder β] {a b : α} {c d : β} (H : a <= b ↔ c <= d) : b < a ↔ d < c
· 使用引理 `Real.le_rpow_inv_iff_of_pos`：le_rpow_inv_iff_of_pos (hx : 0 <= x) (hy : 
0 <= y) (hz : 0 < z) : x <= y ^ z⁻¹ ↔ x ^ z <= y
-/
lemma rpow_inv_lt_iff_of_pos (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 < z) : x ^ z⁻¹ < y ↔ x < y ^ z :=
  lt_iff_lt_of_le_iff_le <| le_rpow_inv_iff_of_pos hy hx hz
/-
**Real.le_rpow_inv_iff_of_neg** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：le_rpow_inv_iff_of_neg (hx : 0 < x) (hy : 0 < y) (hz : z < 0) : x <= y ^ z
⁻¹ ↔ y <= x ^ z
参数：hx : 0 < x；hy : 0 < y；hz : z < 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Real.rpow_le_rpow_iff_of_neg`：rpow_le_rpow_iff_of_neg (hx : 0 < x) (hy :
 0 < y) (hz : z < 0) : x ^ z <= y ^ z ↔ y <= x
· 使用定理 `Real.rpow_pos_of_pos`：rpow_pos_of_pos {x : Real} (hx : 0 < x) (y : Real)
 : 0 < x ^ y
· 使用定理 `Real.rpow_inv_rpow`：∀ {x y : ℝ}, 0 ≤ x → y ≠ 0 → (x ^ y⁻¹) ^ y = x
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem le_rpow_inv_iff_of_neg (hx : 0 < x) (hy : 0 < y) (hz : z < 0) :
    x ≤ y ^ z⁻¹ ↔ y ≤ x ^ z := by
  rw [← rpow_le_rpow_iff_of_neg _ hx hz, rpow_inv_rpow _ hz.ne] <;> positivity
/-
**Real.lt_rpow_inv_iff_of_neg** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：lt_rpow_inv_iff_of_neg (hx : 0 < x) (hy : 0 < y) (hz : z < 0) : x < y ^ z⁻
¹ ↔ y < x ^ z
参数：hx : 0 < x；hy : 0 < y；hz : z < 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Real.rpow_lt_rpow_iff_of_neg`：rpow_lt_rpow_iff_of_neg (hx : 0 < x) (hy :
 0 < y) (hz : z < 0) : x ^ z < y ^ z ↔ y < x
· 使用定理 `Real.rpow_pos_of_pos`：rpow_pos_of_pos {x : Real} (hx : 0 < x) (y : Real)
 : 0 < x ^ y
· 使用定理 `Real.rpow_inv_rpow`：∀ {x y : ℝ}, 0 ≤ x → y ≠ 0 → (x ^ y⁻¹) ^ y = x
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem lt_rpow_inv_iff_of_neg (hx : 0 < x) (hy : 0 < y) (hz : z < 0) :
    x < y ^ z⁻¹ ↔ y < x ^ z := by
  rw [← rpow_lt_rpow_iff_of_neg _ hx hz, rpow_inv_rpow _ hz.ne] <;> positivity
/-
**Real.rpow_inv_lt_iff_of_neg** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：rpow_inv_lt_iff_of_neg (hx : 0 < x) (hy : 0 < y) (hz : z < 0) : x ^ z⁻¹ < 
y ↔ y ^ z < x
参数：hx : 0 < x；hy : 0 < y；hz : z < 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Real.rpow_lt_rpow_iff_of_neg`：rpow_lt_rpow_iff_of_neg (hx : 0 < x) (hy :
 0 < y) (hz : z < 0) : x ^ z < y ^ z ↔ y < x
· 使用定理 `Real.rpow_pos_of_pos`：rpow_pos_of_pos {x : Real} (hx : 0 < x) (y : Real)
 : 0 < x ^ y
· 使用定理 `Real.rpow_inv_rpow`：∀ {x y : ℝ}, 0 ≤ x → y ≠ 0 → (x ^ y⁻¹) ^ y = x
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem rpow_inv_lt_iff_of_neg (hx : 0 < x) (hy : 0 < y) (hz : z < 0) :
    x ^ z⁻¹ < y ↔ y ^ z < x := by
  rw [← rpow_lt_rpow_iff_of_neg hy _ hz, rpow_inv_rpow _ hz.ne] <;> positivity
/-
**Real.rpow_inv_le_iff_of_neg** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：rpow_inv_le_iff_of_neg (hx : 0 < x) (hy : 0 < y) (hz : z < 0) : x ^ z⁻¹ <=
 y ↔ y ^ z <= x
参数：hx : 0 < x；hy : 0 < y；hz : z < 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Real.rpow_le_rpow_iff_of_neg`：rpow_le_rpow_iff_of_neg (hx : 0 < x) (hy :
 0 < y) (hz : z < 0) : x ^ z <= y ^ z ↔ y <= x
· 使用定理 `Real.rpow_pos_of_pos`：rpow_pos_of_pos {x : Real} (hx : 0 < x) (y : Real)
 : 0 < x ^ y
· 使用定理 `Real.rpow_inv_rpow`：∀ {x y : ℝ}, 0 ≤ x → y ≠ 0 → (x ^ y⁻¹) ^ y = x
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem rpow_inv_le_iff_of_neg (hx : 0 < x) (hy : 0 < y) (hz : z < 0) :
    x ^ z⁻¹ ≤ y ↔ y ^ z ≤ x := by
  rw [← rpow_le_rpow_iff_of_neg hy _ hz, rpow_inv_rpow _ hz.ne] <;> positivity
/-
**Real.rpow_lt_rpow_of_exponent_lt** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：rpow_lt_rpow_of_exponent_lt (hx : 1 < x) (hyz : y < z) : x ^ y < x ^ z
参数：hx : 1 < x；hyz : y < z。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.rpow_def_of_pos`：rpow_def_of_pos {x : Real} (hx : 0 < x) (y : Real)
 : x ^ y = exp (log x * y)
· 使用引理 `lt_trans`：lt_trans : a < b -> b < c -> a < c
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Real.exp_lt_exp`：exp_lt_exp {x y : Real} : exp x < exp y ↔ x < y
· 使用定理 `mul_lt_mul_of_pos_left`：mul_lt_mul_of_pos_left [PosMulStrictMono α] (hbc
 : b < c) (ha : 0 < a) : a * b < a * c
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Real.log_pos`：log_pos (hx : 1 < x) : 0 < log x
-/
theorem rpow_lt_rpow_of_exponent_lt (hx : 1 < x) (hyz : y < z) : x ^ y < x ^ z := by
  repeat' rw [rpow_def_of_pos (lt_trans zero_lt_one hx)]
  rw [exp_lt_exp]; exact mul_lt_mul_of_pos_left hyz (log_pos hx)

@[gcongr]
/-
**Real.rpow_le_rpow_of_exponent_le** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：rpow_le_rpow_of_exponent_le (hx : 1 <= x) (hyz : y <= z) : x ^ y <= x ^ z
参数：hx : 1 <= x；hyz : y <= z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.rpow_def_of_pos`：rpow_def_of_pos {x : Real} (hx : 0 < x) (y : Real)
 : x ^ y = exp (log x * y)
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Real.exp_le_exp`：exp_le_exp {x y : Real} : exp x <= exp y ↔ x <= y
· 使用定理 `mul_le_mul_of_nonneg_left`：mul_le_mul_of_nonneg_left [PosMulMono α] (hbc
 : b <= c) (ha : 0 <= a) : a * b <= a * c
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `Real.log_nonneg`：log_nonneg (hx : 1 <= x) : 0 <= log x
-/
theorem rpow_le_rpow_of_exponent_le (hx : 1 ≤ x) (hyz : y ≤ z) : x ^ y ≤ x ^ z := by
  repeat' rw [rpow_def_of_pos (lt_of_lt_of_le zero_lt_one hx)]
  rw [exp_le_exp]; gcongr; exact log_nonneg hx
/-
**Real.strictAntiOn_rpow_Ioi_of_exponent_neg** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：strictAntiOn_rpow_Ioi_of_exponent_neg {r : Real} (hr : r < 0) : StrictAnti
On (fun (x : Real) => x ^ r) (Set.Ioi 0)
参数：hr : r < 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Real.rpow_lt_rpow_of_neg`：rpow_lt_rpow_of_neg (hx : 0 < x) (hxy : x < y)
 (hz : z < 0) : y ^ z < x ^ z
-/
theorem strictAntiOn_rpow_Ioi_of_exponent_neg {r : ℝ} (hr : r < 0) :
    StrictAntiOn (fun (x : ℝ) => x ^ r) (Set.Ioi 0) :=
  fun _ ha _ _ hab => rpow_lt_rpow_of_neg ha hab hr
/-
**Real.antitoneOn_rpow_Ioi_of_exponent_nonpos** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：antitoneOn_rpow_Ioi_of_exponent_nonpos {r : Real} (hr : r <= 0) : Antitone
On (fun (x : Real) => x ^ r) (Set.Ioi 0)
参数：hr : r <= 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Real.rpow_le_rpow_of_nonpos`：rpow_le_rpow_of_nonpos (hx : 0 < x) (hxy : 
x <= y) (hz : z <= 0) : y ^ z <= x ^ z
-/
theorem antitoneOn_rpow_Ioi_of_exponent_nonpos {r : ℝ} (hr : r ≤ 0) :
    AntitoneOn (fun (x : ℝ) => x ^ r) (Set.Ioi 0) :=
  fun _ ha _ _ hab => rpow_le_rpow_of_nonpos ha hab hr

@[simp]
/-
**Real.rpow_le_rpow_left_iff** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：rpow_le_rpow_left_iff (hx : 1 < x) : x ^ y <= x ^ z ↔ y <= z
参数：hx : 1 < x。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_trans`：lt_trans : a < b -> b < c -> a < c
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.log_le_log_iff`：log_le_log_iff (h : 0 < x) (h₁ : 0 < y) : log x <= 
log y ↔ x <= y
· 使用定理 `Real.rpow_pos_of_pos`：rpow_pos_of_pos {x : Real} (hx : 0 < x) (y : Real)
 : 0 < x ^ y
· 使用定理 `Real.log_rpow`：log_rpow {x : Real} (hx : 0 < x) (y : Real) : log (x ^ y)
 = y * log x
· 使用定理 `mul_le_mul_iff_left₀`：mul_le_mul_iff_left₀ [MulPosMono α] [MulPosReflect
LE α] (a0 : 0 < a) : b * a <= c * a ↔ b <= c
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `Real.log_pos`：log_pos (hx : 1 < x) : 0 < log x
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem rpow_le_rpow_left_iff (hx : 1 < x) : x ^ y ≤ x ^ z ↔ y ≤ z := by
  have x_pos : 0 < x := lt_trans zero_lt_one hx
  rw [← log_le_log_iff (rpow_pos_of_pos x_pos y) (rpow_pos_of_pos x_pos z), log_rpow x_pos,
    log_rpow x_pos, mul_le_mul_iff_left₀ (log_pos hx)]

@[simp]
/-
**Real.rpow_lt_rpow_left_iff** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：rpow_lt_rpow_left_iff (hx : 1 < x) : x ^ y < x ^ z ↔ y < z
参数：hx : 1 < x。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `lt_iff_not_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, a < b 
↔ ¬b ≤ a
· 使用定理 `Real.rpow_le_rpow_left_iff`：rpow_le_rpow_left_iff (hx : 1 < x) : x ^ y <
= x ^ z ↔ y <= z
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem rpow_lt_rpow_left_iff (hx : 1 < x) : x ^ y < x ^ z ↔ y < z := by
  rw [lt_iff_not_ge, rpow_le_rpow_left_iff hx, lt_iff_not_ge]
/-
**Real.rpow_lt_rpow_of_exponent_gt** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：rpow_lt_rpow_of_exponent_gt (hx0 : 0 < x) (hx1 : x < 1) (hyz : z < y) : x 
^ y < x ^ z
参数：hx0 : 0 < x；hx1 : x < 1；hyz : z < y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.rpow_def_of_pos`：rpow_def_of_pos {x : Real} (hx : 0 < x) (y : Real)
 : x ^ y = exp (log x * y)
· 使用定理 `Real.exp_lt_exp`：exp_lt_exp {x y : Real} : exp x < exp y ↔ x < y
· 使用定理 `mul_lt_mul_of_neg_left`：mul_lt_mul_of_neg_left [ExistsAddOfLE R] [PosMul
StrictMono R] [AddRightStrictMono R] [AddRightReflectLT R] (h : b < a) (hc : c <
 0) : c * a …
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
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
· 使用定理 `contravariant_swap_add_of_contravariant_add`：∀ (N : Type u_2) (r : N → N
 → Prop) [inst : AddCommSemigroup N] [ContravariantClass N N (fun x1 x2 => x1 + 
x2) r],   ContravariantClass N N …
· 使用定理 `Real.log_neg`：log_neg (h0 : 0 < x) (h1 : x < 1) : log x < 0
-/
theorem rpow_lt_rpow_of_exponent_gt (hx0 : 0 < x) (hx1 : x < 1) (hyz : z < y) : x ^ y < x ^ z := by
  repeat' rw [rpow_def_of_pos hx0]
  rw [exp_lt_exp]; exact mul_lt_mul_of_neg_left hyz (log_neg hx0 hx1)
/-
**Real.rpow_le_rpow_of_exponent_ge** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：rpow_le_rpow_of_exponent_ge (hx0 : 0 < x) (hx1 : x <= 1) (hyz : z <= y) : 
x ^ y <= x ^ z
参数：hx0 : 0 < x；hx1 : x <= 1；hyz : z <= y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.rpow_def_of_pos`：rpow_def_of_pos {x : Real} (hx : 0 < x) (y : Real)
 : x ^ y = exp (log x * y)
· 使用定理 `Real.exp_le_exp`：exp_le_exp {x y : Real} : exp x <= exp y ↔ x <= y
· 使用定理 `mul_le_mul_of_nonpos_left`：mul_le_mul_of_nonpos_left [ExistsAddOfLE R] [
PosMulMono R] [AddRightMono R] [AddRightReflectLE R] (h : b <= a) (hc : c <= 0) 
: c * a <= c * …
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
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
· 使用定理 `Real.log_nonpos`：log_nonpos (hx : 0 <= x) (h'x : x <= 1) : log x <= 0
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
theorem rpow_le_rpow_of_exponent_ge (hx0 : 0 < x) (hx1 : x ≤ 1) (hyz : z ≤ y) : x ^ y ≤ x ^ z := by
  repeat' rw [rpow_def_of_pos hx0]
  rw [exp_le_exp]; exact mul_le_mul_of_nonpos_left hyz (log_nonpos (le_of_lt hx0) hx1)

@[simp]
/-
**Real.rpow_le_rpow_left_iff_of_base_lt_one** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：rpow_le_rpow_left_iff_of_base_lt_one (hx0 : 0 < x) (hx1 : x < 1) : x ^ y <
= x ^ z ↔ z <= y
参数：hx0 : 0 < x；hx1 : x < 1。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.log_le_log_iff`：log_le_log_iff (h : 0 < x) (h₁ : 0 < y) : log x <= 
log y ↔ x <= y
· 使用定理 `Real.rpow_pos_of_pos`：rpow_pos_of_pos {x : Real} (hx : 0 < x) (y : Real)
 : 0 < x ^ y
· 使用定理 `Real.log_rpow`：log_rpow {x : Real} (hx : 0 < x) (y : Real) : log (x ^ y)
 = y * log x
· 使用定理 `mul_le_mul_right_of_neg`：mul_le_mul_right_of_neg [ExistsAddOfLE R] [MulP
osStrictMono R] [AddRightMono R] [AddRightReflectLE R] {a b c : R} (h : c < 0) :
 a * c <= b *…
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
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
· 使用定理 `Real.log_neg`：log_neg (h0 : 0 < x) (h1 : x < 1) : log x < 0
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem rpow_le_rpow_left_iff_of_base_lt_one (hx0 : 0 < x) (hx1 : x < 1) :
    x ^ y ≤ x ^ z ↔ z ≤ y := by
  rw [← log_le_log_iff (rpow_pos_of_pos hx0 y) (rpow_pos_of_pos hx0 z), log_rpow hx0, log_rpow hx0,
    mul_le_mul_right_of_neg (log_neg hx0 hx1)]

@[simp]
/-
**Real.rpow_lt_rpow_left_iff_of_base_lt_one** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：rpow_lt_rpow_left_iff_of_base_lt_one (hx0 : 0 < x) (hx1 : x < 1) : x ^ y <
 x ^ z ↔ z < y
参数：hx0 : 0 < x；hx1 : x < 1。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `lt_iff_not_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, a < b 
↔ ¬b ≤ a
· 使用定理 `Real.rpow_le_rpow_left_iff_of_base_lt_one`：rpow_le_rpow_left_iff_of_base
_lt_one (hx0 : 0 < x) (hx1 : x < 1) : x ^ y <= x ^ z ↔ z <= y
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem rpow_lt_rpow_left_iff_of_base_lt_one (hx0 : 0 < x) (hx1 : x < 1) :
    x ^ y < x ^ z ↔ z < y := by
  rw [lt_iff_not_ge, rpow_le_rpow_left_iff_of_base_lt_one hx0 hx1, lt_iff_not_ge]
/-
**Real.rpow_lt_one** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：rpow_lt_one {x z : Real} (hx1 : 0 <= x) (hx2 : x < 1) (hz : 0 < z) : x ^ z
 < 1
参数：hx1 : 0 <= x；hx2 : x < 1；hz : 0 < z。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.one_rpow`：one_rpow (x : Real) : (1 : Real) ^ x = 1
· 使用定理 `Real.rpow_lt_rpow`：rpow_lt_rpow (hx : 0 <= x) (hxy : x < y) (hz : 0 < z)
 : x ^ z < y ^ z
-/
theorem rpow_lt_one {x z : ℝ} (hx1 : 0 ≤ x) (hx2 : x < 1) (hz : 0 < z) : x ^ z < 1 := by
  rw [← one_rpow z]
  exact rpow_lt_rpow hx1 hx2 hz
/-
**Real.rpow_le_one** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：rpow_le_one {x z : Real} (hx1 : 0 <= x) (hx2 : x <= 1) (hz : 0 <= z) : x ^
 z <= 1
参数：hx1 : 0 <= x；hx2 : x <= 1；hz : 0 <= z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.one_rpow`：one_rpow (x : Real) : (1 : Real) ^ x = 1
· 使用定理 `Real.rpow_le_rpow`：rpow_le_rpow {x y z : Real} (h : 0 <= x) (h₁ : x <= y
) (h₂ : 0 <= z) : x ^ z <= y ^ z
-/
theorem rpow_le_one {x z : ℝ} (hx1 : 0 ≤ x) (hx2 : x ≤ 1) (hz : 0 ≤ z) : x ^ z ≤ 1 := by
  rw [← one_rpow z]
  gcongr
/-
**Real.rpow_lt_one_of_one_lt_of_neg** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：rpow_lt_one_of_one_lt_of_neg {x z : Real} (hx : 1 < x) (hz : z < 0) : x ^ 
z < 1
参数：hx : 1 < x；hz : z < 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.rpow_zero`：rpow_zero (x : Real) : x ^ (0 : Real) = 1
· 使用定理 `Real.rpow_lt_rpow_of_exponent_lt`：rpow_lt_rpow_of_exponent_lt (hx : 1 < 
x) (hyz : y < z) : x ^ y < x ^ z
-/
theorem rpow_lt_one_of_one_lt_of_neg {x z : ℝ} (hx : 1 < x) (hz : z < 0) : x ^ z < 1 := by
  convert! rpow_lt_rpow_of_exponent_lt hx hz
  exact (rpow_zero x).symm
/-
**Real.rpow_le_one_of_one_le_of_nonpos** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：rpow_le_one_of_one_le_of_nonpos {x z : Real} (hx : 1 <= x) (hz : z <= 0) :
 x ^ z <= 1
参数：hx : 1 <= x；hz : z <= 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.rpow_zero`：rpow_zero (x : Real) : x ^ (0 : Real) = 1
· 使用定理 `Real.rpow_le_rpow_of_exponent_le`：rpow_le_rpow_of_exponent_le (hx : 1 <=
 x) (hyz : y <= z) : x ^ y <= x ^ z
-/
theorem rpow_le_one_of_one_le_of_nonpos {x z : ℝ} (hx : 1 ≤ x) (hz : z ≤ 0) : x ^ z ≤ 1 := by
  convert! rpow_le_rpow_of_exponent_le hx hz
  exact (rpow_zero x).symm
/-
**Real.one_lt_rpow** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：one_lt_rpow {x z : Real} (hx : 1 < x) (hz : 0 < z) : 1 < x ^ z
参数：hx : 1 < x；hz : 0 < z。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.one_rpow`：one_rpow (x : Real) : (1 : Real) ^ x = 1
· 使用定理 `Real.rpow_lt_rpow`：rpow_lt_rpow (hx : 0 <= x) (hxy : x < y) (hz : 0 < z)
 : x ^ z < y ^ z
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1
-/
theorem one_lt_rpow {x z : ℝ} (hx : 1 < x) (hz : 0 < z) : 1 < x ^ z := by
  rw [← one_rpow z]
  exact rpow_lt_rpow zero_le_one hx hz
/-
**Real.one_le_rpow** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：one_le_rpow {x z : Real} (hx : 1 <= x) (hz : 0 <= z) : 1 <= x ^ z
参数：hx : 1 <= x；hz : 0 <= z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.one_rpow`：one_rpow (x : Real) : (1 : Real) ^ x = 1
· 使用定理 `Real.rpow_le_rpow`：rpow_le_rpow {x y z : Real} (h : 0 <= x) (h₁ : x <= y
) (h₂ : 0 <= z) : x ^ z <= y ^ z
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
-/
theorem one_le_rpow {x z : ℝ} (hx : 1 ≤ x) (hz : 0 ≤ z) : 1 ≤ x ^ z := by
  rw [← one_rpow z]
  gcongr
/-
**Real.one_lt_rpow_of_pos_of_lt_one_of_neg** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：one_lt_rpow_of_pos_of_lt_one_of_neg (hx1 : 0 < x) (hx2 : x < 1) (hz : z < 
0) : 1 < x ^ z
参数：hx1 : 0 < x；hx2 : x < 1；hz : z < 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.rpow_zero`：rpow_zero (x : Real) : x ^ (0 : Real) = 1
· 使用定理 `Real.rpow_lt_rpow_of_exponent_gt`：rpow_lt_rpow_of_exponent_gt (hx0 : 0 <
 x) (hx1 : x < 1) (hyz : z < y) : x ^ y < x ^ z
-/
theorem one_lt_rpow_of_pos_of_lt_one_of_neg (hx1 : 0 < x) (hx2 : x < 1) (hz : z < 0) :
    1 < x ^ z := by
  convert! rpow_lt_rpow_of_exponent_gt hx1 hx2 hz
  exact (rpow_zero x).symm
/-
**Real.one_le_rpow_of_pos_of_le_one_of_nonpos** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：one_le_rpow_of_pos_of_le_one_of_nonpos (hx1 : 0 < x) (hx2 : x <= 1) (hz : 
z <= 0) : 1 <= x ^ z
参数：hx1 : 0 < x；hx2 : x <= 1；hz : z <= 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.rpow_zero`：rpow_zero (x : Real) : x ^ (0 : Real) = 1
· 使用定理 `Real.rpow_le_rpow_of_exponent_ge`：rpow_le_rpow_of_exponent_ge (hx0 : 0 <
 x) (hx1 : x <= 1) (hyz : z <= y) : x ^ y <= x ^ z
-/
theorem one_le_rpow_of_pos_of_le_one_of_nonpos (hx1 : 0 < x) (hx2 : x ≤ 1) (hz : z ≤ 0) :
    1 ≤ x ^ z := by
  convert! rpow_le_rpow_of_exponent_ge hx1 hx2 hz
  exact (rpow_zero x).symm
/-
**Real.rpow_lt_one_iff_of_pos** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：rpow_lt_one_iff_of_pos (hx : 0 < x) : x ^ y < 1 ↔ 1 < x ∧ y < 0 ∨ x < 1 ∧ 
0 < y
参数：hx : 0 < x。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.rpow_def_of_pos`：rpow_def_of_pos {x : Real} (hx : 0 < x) (y : Real)
 : x ^ y = exp (log x * y)
· 使用定理 `Real.exp_lt_one_iff`：exp_lt_one_iff {x : Real} : exp x < 1 ↔ x < 0
· 使用引理 `mul_neg_iff`：mul_neg_iff [PosMulStrictMono R] [MulPosStrictMono R] [AddL
eftReflectLT R] [AddLeftStrictMono R] : a * b < 0 ↔ 0 < a ∧ b < 0 ∨ a < 0 ∧ 0 < 
b
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `Real.log_pos_iff`：log_pos_iff (hx : 0 <= x) : 0 < log x ↔ 1 < x
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Real.log_neg_iff`：log_neg_iff (h : 0 < x) : log x < 0 ↔ x < 1
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem rpow_lt_one_iff_of_pos (hx : 0 < x) : x ^ y < 1 ↔ 1 < x ∧ y < 0 ∨ x < 1 ∧ 0 < y := by
  rw [rpow_def_of_pos hx, exp_lt_one_iff, mul_neg_iff, log_pos_iff hx.le, log_neg_iff hx]
/-
**Real.rpow_lt_one_iff** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：rpow_lt_one_iff (hx : 0 <= x) : x ^ y < 1 ↔ x = 0 ∧ y != 0 ∨ 1 < x ∧ y < 0
 ∨ x < 1 ∧ 0 < y
参数：hx : 0 <= x。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.eq_or_lt`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a = b ∨ a < b
· 使用定理 `em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Real.rpow_zero`：rpow_zero (x : Real) : x ^ (0 : Real) = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.zero_rpow`：zero_rpow {x : Real} (h : x != 0) : (0 : Real) ^ x = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `Real.rpow_lt_one_iff_of_pos`：rpow_lt_one_iff_of_pos (hx : 0 < x) : x ^ y
 < 1 ↔ 1 < x ∧ y < 0 ∨ x < 1 ∧ 0 < y
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
-/
theorem rpow_lt_one_iff (hx : 0 ≤ x) :
    x ^ y < 1 ↔ x = 0 ∧ y ≠ 0 ∨ 1 < x ∧ y < 0 ∨ x < 1 ∧ 0 < y := by
  rcases hx.eq_or_lt with (rfl | hx)
  · rcases _root_.em (y = 0) with (rfl | hy) <;> simp [*, zero_lt_one]
  · simp [rpow_lt_one_iff_of_pos hx, hx.ne.symm]
/-
**Real.rpow_lt_one_iff'** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：rpow_lt_one_iff' {x y : Real} (hx : 0 <= x) (hy : 0 < y) : x ^ y < 1 ↔ x <
 1
参数：hx : 0 <= x；hy : 0 < y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.rpow_lt_rpow_iff`：rpow_lt_rpow_iff (hx : 0 <= x) (hy : 0 <= y) (hz 
: 0 < z) : x ^ z < y ^ z ↔ x < y
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1
· 使用定理 `Real.one_rpow`：one_rpow (x : Real) : (1 : Real) ^ x = 1
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem rpow_lt_one_iff' {x y : ℝ} (hx : 0 ≤ x) (hy : 0 < y) :
    x ^ y < 1 ↔ x < 1 := by
  rw [← Real.rpow_lt_rpow_iff hx zero_le_one hy, Real.one_rpow]
/-
**Real.one_lt_rpow_iff_of_pos** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：one_lt_rpow_iff_of_pos (hx : 0 < x) : 1 < x ^ y ↔ 1 < x ∧ 0 < y ∨ x < 1 ∧ 
y < 0
参数：hx : 0 < x。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.rpow_def_of_pos`：rpow_def_of_pos {x : Real} (hx : 0 < x) (y : Real)
 : x ^ y = exp (log x * y)
· 使用定理 `Real.one_lt_exp_iff`：one_lt_exp_iff {x : Real} : 1 < exp x ↔ 0 < x
· 使用定理 `mul_pos_iff`：mul_pos_iff [ExistsAddOfLE R] [PosMulStrictMono R] [MulPosS
trictMono R] [AddLeftStrictMono R] [AddLeftReflectLT R] : 0 < a * b ↔ 0 < a ∧ 0 
<…
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Real.log_pos_iff`：log_pos_iff (hx : 0 <= x) : 0 < log x ↔ 1 < x
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Real.log_neg_iff`：log_neg_iff (h : 0 < x) : log x < 0 ↔ x < 1
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem one_lt_rpow_iff_of_pos (hx : 0 < x) : 1 < x ^ y ↔ 1 < x ∧ 0 < y ∨ x < 1 ∧ y < 0 := by
  rw [rpow_def_of_pos hx, one_lt_exp_iff, mul_pos_iff, log_pos_iff hx.le, log_neg_iff hx]
/-
**Real.one_lt_rpow_iff** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：one_lt_rpow_iff (hx : 0 <= x) : 1 < x ^ y ↔ 1 < x ∧ 0 < y ∨ 0 < x ∧ x < 1 
∧ y < 0
参数：hx : 0 <= x。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.eq_or_lt`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a = b ∨ a < b
· 使用定理 `em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.rpow_zero`：rpow_zero (x : Real) : x ^ (0 : Real) = 1
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `LT.lt.not_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 < a
· 使用引理 `zero_lt_one'`：zero_lt_one' : (0 : α) < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.zero_rpow`：zero_rpow {x : Real} (h : x != 0) : (0 : Real) ^ x = 0
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `Real.one_lt_rpow_iff_of_pos`：one_lt_rpow_iff_of_pos (hx : 0 < x) : 1 < x
 ^ y ↔ 1 < x ∧ 0 < y ∨ x < 1 ∧ y < 0
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
-/
theorem one_lt_rpow_iff (hx : 0 ≤ x) : 1 < x ^ y ↔ 1 < x ∧ 0 < y ∨ 0 < x ∧ x < 1 ∧ y < 0 := by
  rcases hx.eq_or_lt with (rfl | hx)
  · rcases _root_.em (y = 0) with (rfl | hy) <;> simp [*, (zero_lt_one' ℝ).not_gt]
  · simp [one_lt_rpow_iff_of_pos hx, hx]

/-- This is a more general but less convenient version of `rpow_le_rpow_of_exponent_ge`.
This version allows `x = 0`, so it explicitly forbids `x = y = 0`, `z ≠ 0`. -/
/-
**Real.rpow_le_rpow_of_exponent_ge_of_imp** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：rpow_le_rpow_of_exponent_ge_of_imp (hx0 : 0 <= x) (hx1 : x <= 1) (hyz : z 
<= y) (h : x = 0 -> y = 0 -> z = 0) : x ^ y <= x ^ z
参数：hx0 : 0 <= x；hx1 : x <= 1；hyz : z <= y；h : x = 0 -> y = 0 -> z = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_lt_of_le`：eq_or_lt_of_le (h : a <= b) : a = b ∨ a < b
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.zero_rpow`：zero_rpow {x : Real} (h : x != 0) : (0 : Real) ^ x = 0
· 使用定理 `Real.zero_rpow_nonneg`：zero_rpow_nonneg (x : Real) : 0 <= (0 : Real) ^ x
· 使用定理 `Real.rpow_le_rpow_of_exponent_ge`：rpow_le_rpow_of_exponent_ge (hx0 : 0 <
 x) (hx1 : x <= 1) (hyz : z <= y) : x ^ y <= x ^ z

--- 原说明 ---
This is a more general but less convenient version of `rpow_le_rpow_of_exponent_
ge`.
This version allows `x = 0`, so it explicitly forbids `x = y = 0`, `z ≠ 0`.
-/
theorem rpow_le_rpow_of_exponent_ge_of_imp (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hyz : z ≤ y)
    (h : x = 0 → y = 0 → z = 0) :
    x ^ y ≤ x ^ z := by
  rcases eq_or_lt_of_le hx0 with (rfl | hx0')
  · rcases eq_or_ne y 0 with rfl | hy0
    · rw [h rfl rfl]
    · rw [zero_rpow hy0]
      apply zero_rpow_nonneg
  · exact rpow_le_rpow_of_exponent_ge hx0' hx1 hyz

/-- This version of `rpow_le_rpow_of_exponent_ge` allows `x = 0` but requires `0 ≤ z`.
See also `rpow_le_rpow_of_exponent_ge_of_imp` for the most general version. -/
/-
**Real.rpow_le_rpow_of_exponent_ge'** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：rpow_le_rpow_of_exponent_ge' (hx0 : 0 <= x) (hx1 : x <= 1) (hz : 0 <= z) (
hyz : z <= y) : x ^ y <= x ^ z
参数：hx0 : 0 <= x；hx1 : x <= 1；hz : 0 <= z；hyz : z <= y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.rpow_le_rpow_of_exponent_ge_of_imp`：rpow_le_rpow_of_exponent_ge_of_
imp (hx0 : 0 <= x) (hx1 : x <= 1) (hyz : z <= y) (h : x = 0 -> y = 0 -> z = 0) :
 x ^ y <= x ^ z
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c

--- 原说明 ---
This version of `rpow_le_rpow_of_exponent_ge` allows `x = 0` but requires `0 ≤ z
`.
See also `rpow_le_rpow_of_exponent_ge_of_imp` for the most general version.
-/
theorem rpow_le_rpow_of_exponent_ge' (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hz : 0 ≤ z) (hyz : z ≤ y) :
    x ^ y ≤ x ^ z :=
  rpow_le_rpow_of_exponent_ge_of_imp hx0 hx1 hyz fun _ hy ↦ le_antisymm (hyz.trans_eq hy) hz
/-
**Real.rpow_max** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：rpow_max {x y p : Real} (hx : 0 <= x) (hy : 0 <= y) (hp : 0 <= p) : (max x
 y) ^ p = max (x ^ p) (y ^ p)
参数：hx : 0 <= x；hy : 0 <= y；hp : 0 <= p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_total`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b ≤
 a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `max_eq_right`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, a ≤ b →
 max a b = b
· 使用定理 `Real.rpow_le_rpow`：rpow_le_rpow {x y z : Real} (h : 0 <= x) (h₁ : x <= y
) (h₂ : 0 <= z) : x ^ z <= y ^ z
· 使用定理 `max_eq_left`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, b ≤ a → 
max a b = a
-/
lemma rpow_max {x y p : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hp : 0 ≤ p) :
    (max x y) ^ p = max (x ^ p) (y ^ p) := by
  rcases le_total x y with hxy | hxy
  · rw [max_eq_right hxy, max_eq_right (by gcongr)]
  · rw [max_eq_left hxy, max_eq_left (by gcongr)]
/-
**Real.self_le_rpow_of_le_one** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：self_le_rpow_of_le_one (h₁ : 0 <= x) (h₂ : x <= 1) (h₃ : y <= 1) : x <= x 
^ y
参数：h₁ : 0 <= x；h₂ : x <= 1；h₃ : y <= 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.rpow_one`：rpow_one (x : Real) : x ^ (1 : Real) = x
· 使用定理 `Real.rpow_le_rpow_of_exponent_ge_of_imp`：rpow_le_rpow_of_exponent_ge_of_
imp (hx0 : 0 <= x) (hx1 : x <= 1) (hyz : z <= y) (h : x = 0 -> y = 0 -> z = 0) :
 x ^ y <= x ^ z
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
-/
theorem self_le_rpow_of_le_one (h₁ : 0 ≤ x) (h₂ : x ≤ 1) (h₃ : y ≤ 1) : x ≤ x ^ y := by
  simpa only [rpow_one]
    using rpow_le_rpow_of_exponent_ge_of_imp h₁ h₂ h₃ fun _ ↦ (absurd · one_ne_zero)
/-
**Real.self_le_rpow_of_one_le** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：self_le_rpow_of_one_le (h₁ : 1 <= x) (h₂ : 1 <= y) : x <= x ^ y
参数：h₁ : 1 <= x；h₂ : 1 <= y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.rpow_one`：rpow_one (x : Real) : x ^ (1 : Real) = x
· 使用定理 `Real.rpow_le_rpow_of_exponent_le`：rpow_le_rpow_of_exponent_le (hx : 1 <=
 x) (hyz : y <= z) : x ^ y <= x ^ z
-/
theorem self_le_rpow_of_one_le (h₁ : 1 ≤ x) (h₂ : 1 ≤ y) : x ≤ x ^ y := by
  simpa only [rpow_one] using rpow_le_rpow_of_exponent_le h₁ h₂
/-
**Real.rpow_le_self_of_le_one** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：rpow_le_self_of_le_one (h₁ : 0 <= x) (h₂ : x <= 1) (h₃ : 1 <= y) : x ^ y <
= x
参数：h₁ : 0 <= x；h₂ : x <= 1；h₃ : 1 <= y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.rpow_one`：rpow_one (x : Real) : x ^ (1 : Real) = x
· 使用定理 `Real.rpow_le_rpow_of_exponent_ge_of_imp`：rpow_le_rpow_of_exponent_ge_of_
imp (hx0 : 0 <= x) (hx1 : x <= 1) (hyz : z <= y) (h : x = 0 -> y = 0 -> z = 0) :
 x ^ y <= x ^ z
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `one_pos`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 : Par
tialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
-/
theorem rpow_le_self_of_le_one (h₁ : 0 ≤ x) (h₂ : x ≤ 1) (h₃ : 1 ≤ y) : x ^ y ≤ x := by
  simpa only [rpow_one]
    using rpow_le_rpow_of_exponent_ge_of_imp h₁ h₂ h₃ fun _ ↦ (absurd · (one_pos.trans_le h₃).ne')
/-
**Real.rpow_le_self_of_one_le** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：rpow_le_self_of_one_le (h₁ : 1 <= x) (h₂ : y <= 1) : x ^ y <= x
参数：h₁ : 1 <= x；h₂ : y <= 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.rpow_one`：rpow_one (x : Real) : x ^ (1 : Real) = x
· 使用定理 `Real.rpow_le_rpow_of_exponent_le`：rpow_le_rpow_of_exponent_le (hx : 1 <=
 x) (hyz : y <= z) : x ^ y <= x ^ z
-/
theorem rpow_le_self_of_one_le (h₁ : 1 ≤ x) (h₂ : y ≤ 1) : x ^ y ≤ x := by
  simpa only [rpow_one] using rpow_le_rpow_of_exponent_le h₁ h₂
/-
**Real.self_lt_rpow_of_lt_one** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：self_lt_rpow_of_lt_one (h₁ : 0 < x) (h₂ : x < 1) (h₃ : y < 1) : x < x ^ y
参数：h₁ : 0 < x；h₂ : x < 1；h₃ : y < 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.rpow_one`：rpow_one (x : Real) : x ^ (1 : Real) = x
· 使用定理 `Real.rpow_lt_rpow_of_exponent_gt`：rpow_lt_rpow_of_exponent_gt (hx0 : 0 <
 x) (hx1 : x < 1) (hyz : z < y) : x ^ y < x ^ z
-/
theorem self_lt_rpow_of_lt_one (h₁ : 0 < x) (h₂ : x < 1) (h₃ : y < 1) : x < x ^ y := by
  simpa only [rpow_one] using rpow_lt_rpow_of_exponent_gt h₁ h₂ h₃
/-
**Real.self_lt_rpow_of_one_lt** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：self_lt_rpow_of_one_lt (h₁ : 1 < x) (h₂ : 1 < y) : x < x ^ y
参数：h₁ : 1 < x；h₂ : 1 < y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.rpow_one`：rpow_one (x : Real) : x ^ (1 : Real) = x
· 使用定理 `Real.rpow_lt_rpow_of_exponent_lt`：rpow_lt_rpow_of_exponent_lt (hx : 1 < 
x) (hyz : y < z) : x ^ y < x ^ z
-/
theorem self_lt_rpow_of_one_lt (h₁ : 1 < x) (h₂ : 1 < y) : x < x ^ y := by
  simpa only [rpow_one] using rpow_lt_rpow_of_exponent_lt h₁ h₂
/-
**Real.rpow_lt_self_of_lt_one** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：rpow_lt_self_of_lt_one (h₁ : 0 < x) (h₂ : x < 1) (h₃ : 1 < y) : x ^ y < x
参数：h₁ : 0 < x；h₂ : x < 1；h₃ : 1 < y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.rpow_one`：rpow_one (x : Real) : x ^ (1 : Real) = x
· 使用定理 `Real.rpow_lt_rpow_of_exponent_gt`：rpow_lt_rpow_of_exponent_gt (hx0 : 0 <
 x) (hx1 : x < 1) (hyz : z < y) : x ^ y < x ^ z
-/
theorem rpow_lt_self_of_lt_one (h₁ : 0 < x) (h₂ : x < 1) (h₃ : 1 < y) : x ^ y < x := by
  simpa only [rpow_one] using rpow_lt_rpow_of_exponent_gt h₁ h₂ h₃
/-
**Real.rpow_lt_self_of_one_lt** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：rpow_lt_self_of_one_lt (h₁ : 1 < x) (h₂ : y < 1) : x ^ y < x
参数：h₁ : 1 < x；h₂ : y < 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.rpow_one`：rpow_one (x : Real) : x ^ (1 : Real) = x
· 使用定理 `Real.rpow_lt_rpow_of_exponent_lt`：rpow_lt_rpow_of_exponent_lt (hx : 1 < 
x) (hyz : y < z) : x ^ y < x ^ z
-/
theorem rpow_lt_self_of_one_lt (h₁ : 1 < x) (h₂ : y < 1) : x ^ y < x := by
  simpa only [rpow_one] using rpow_lt_rpow_of_exponent_lt h₁ h₂
/-
**Real.rpow_left_injOn** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：rpow_left_injOn {x : Real} (hx : x != 0) : InjOn (fun y : Real => y ^ x) {
 y : Real | 0 <= y }
参数：hx : x != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.rpow_one`：rpow_one (x : Real) : x ^ (1 : Real) = x
· 使用引理 `mul_inv_cancel₀`：mul_inv_cancel₀ (h : a != 0) : a * a⁻¹ = 1
· 使用定理 `Real.rpow_mul`：rpow_mul {x : Real} (hx : 0 <= x) (y z : Real) : x ^ (y *
 z) = (x ^ y) ^ z
-/
theorem rpow_left_injOn {x : ℝ} (hx : x ≠ 0) : InjOn (fun y : ℝ => y ^ x) { y : ℝ | 0 ≤ y } := by
  rintro y hy z hz (hyz : y ^ x = z ^ x)
  rw [← rpow_one y, ← rpow_one z, ← mul_inv_cancel₀ hx, rpow_mul hy, rpow_mul hz, hyz]
/-
**Real.rpow_left_inj** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：rpow_left_inj (hx : 0 <= x) (hy : 0 <= y) (hz : z != 0) : x ^ z = y ^ z ↔ 
x = y
参数：hx : 0 <= x；hy : 0 <= y；hz : z != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.InjOn.eq_iff`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {f : α → β
} {x y : α}, Set.InjOn f s → x ∈ s → y ∈ s → (f x = f y ↔ x = y)
· 使用定理 `Real.rpow_left_injOn`：rpow_left_injOn {x : Real} (hx : x != 0) : InjOn (
fun y : Real => y ^ x) { y : Real | 0 <= y }
-/
lemma rpow_left_inj (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : z ≠ 0) : x ^ z = y ^ z ↔ x = y :=
  (rpow_left_injOn hz).eq_iff hx hy
/-
**Real.rpow_inv_eq** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：rpow_inv_eq (hx : 0 <= x) (hy : 0 <= y) (hz : z != 0) : x ^ z⁻¹ = y ↔ x = 
y ^ z
参数：hx : 0 <= x；hy : 0 <= y；hz : z != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Real.rpow_left_inj`：rpow_left_inj (hx : 0 <= x) (hy : 0 <= y) (hz : z !=
 0) : x ^ z = y ^ z ↔ x = y
· 使用定理 `Real.rpow_nonneg`：rpow_nonneg {x : Real} (hx : 0 <= x) (y : Real) : 0 <=
 x ^ y
· 使用定理 `Real.rpow_inv_rpow`：∀ {x y : ℝ}, 0 ≤ x → y ≠ 0 → (x ^ y⁻¹) ^ y = x
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma rpow_inv_eq (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : z ≠ 0) : x ^ z⁻¹ = y ↔ x = y ^ z := by
  rw [← rpow_left_inj _ hy hz, rpow_inv_rpow hx hz]; positivity
/-
**Real.eq_rpow_inv** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：eq_rpow_inv (hx : 0 <= x) (hy : 0 <= y) (hz : z != 0) : x = y ^ z⁻¹ ↔ x ^ 
z = y
参数：hx : 0 <= x；hy : 0 <= y；hz : z != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Real.rpow_left_inj`：rpow_left_inj (hx : 0 <= x) (hy : 0 <= y) (hz : z !=
 0) : x ^ z = y ^ z ↔ x = y
· 使用定理 `Real.rpow_nonneg`：rpow_nonneg {x : Real} (hx : 0 <= x) (y : Real) : 0 <=
 x ^ y
· 使用定理 `Real.rpow_inv_rpow`：∀ {x y : ℝ}, 0 ≤ x → y ≠ 0 → (x ^ y⁻¹) ^ y = x
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma eq_rpow_inv (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : z ≠ 0) : x = y ^ z⁻¹ ↔ x ^ z = y := by
  rw [← rpow_left_inj hx _ hz, rpow_inv_rpow hy hz]; positivity
/-
**Real.le_rpow_iff_log_le** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：le_rpow_iff_log_le (hx : 0 < x) (hy : 0 < y) : x <= y ^ z ↔ log x <= z * l
og y
参数：hx : 0 < x；hy : 0 < y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.log_le_log_iff`：log_le_log_iff (h : 0 < x) (h₁ : 0 < y) : log x <= 
log y ↔ x <= y
· 使用定理 `Real.rpow_pos_of_pos`：rpow_pos_of_pos {x : Real} (hx : 0 < x) (y : Real)
 : 0 < x ^ y
· 使用定理 `Real.log_rpow`：log_rpow {x : Real} (hx : 0 < x) (y : Real) : log (x ^ y)
 = y * log x
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem le_rpow_iff_log_le (hx : 0 < x) (hy : 0 < y) : x ≤ y ^ z ↔ log x ≤ z * log y := by
  rw [← log_le_log_iff hx (rpow_pos_of_pos hy z), log_rpow hy]
/-
**Real.le_pow_iff_log_le** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：le_pow_iff_log_le (hx : 0 < x) (hy : 0 < y) : x <= y ^ n ↔ log x <= n * lo
g y
参数：hx : 0 < x；hy : 0 < y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.le_rpow_iff_log_le`：le_rpow_iff_log_le (hx : 0 < x) (hy : 0 < y) : 
x <= y ^ z ↔ log x <= z * log y
· 使用定理 `Real.rpow_natCast`：rpow_natCast (x : Real) (n : Nat) : x ^ (n : Real) = 
x ^ n
-/
lemma le_pow_iff_log_le (hx : 0 < x) (hy : 0 < y) : x ≤ y ^ n ↔ log x ≤ n * log y :=
  rpow_natCast _ _ ▸ le_rpow_iff_log_le hx hy
/-
**Real.le_zpow_iff_log_le** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：le_zpow_iff_log_le {n : Int} (hx : 0 < x) (hy : 0 < y) : x <= y ^ n ↔ log 
x <= n * log y
参数：hx : 0 < x；hy : 0 < y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.le_rpow_iff_log_le`：le_rpow_iff_log_le (hx : 0 < x) (hy : 0 < y) : 
x <= y ^ z ↔ log x <= z * log y
· 使用定理 `Real.rpow_intCast`：rpow_intCast (x : Real) (n : Int) : x ^ (n : Real) = 
x ^ n
-/
lemma le_zpow_iff_log_le {n : ℤ} (hx : 0 < x) (hy : 0 < y) : x ≤ y ^ n ↔ log x ≤ n * log y :=
  rpow_intCast _ _ ▸ le_rpow_iff_log_le hx hy
/-
**Real.le_rpow_of_log_le** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：le_rpow_of_log_le (hy : 0 < y) (h : log x <= z * log y) : x <= y ^ z
参数：hy : 0 < y；h : log x <= z * log y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_or_gt`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b <
 a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Real.rpow_pos_of_pos`：rpow_pos_of_pos {x : Real} (hx : 0 < x) (y : Real)
 : 0 < x ^ y
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Real.le_rpow_iff_log_le`：le_rpow_iff_log_le (hx : 0 < x) (hy : 0 < y) : 
x <= y ^ z ↔ log x <= z * log y
-/
lemma le_rpow_of_log_le (hy : 0 < y) (h : log x ≤ z * log y) : x ≤ y ^ z := by
  obtain hx | hx := le_or_gt x 0
  · exact hx.trans (rpow_pos_of_pos hy _).le
  · exact (le_rpow_iff_log_le hx hy).2 h
/-
**Real.le_pow_of_log_le** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：le_pow_of_log_le (hy : 0 < y) (h : log x <= n * log y) : x <= y ^ n
参数：hy : 0 < y；h : log x <= n * log y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Real.le_rpow_of_log_le`：le_rpow_of_log_le (hy : 0 < y) (h : log x <= z *
 log y) : x <= y ^ z
· 使用定理 `Real.rpow_natCast`：rpow_natCast (x : Real) (n : Nat) : x ^ (n : Real) = 
x ^ n
-/
lemma le_pow_of_log_le (hy : 0 < y) (h : log x ≤ n * log y) : x ≤ y ^ n :=
  rpow_natCast _ _ ▸ le_rpow_of_log_le hy h
/-
**Real.le_zpow_of_log_le** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：le_zpow_of_log_le {n : Int} (hy : 0 < y) (h : log x <= n * log y) : x <= y
 ^ n
参数：hy : 0 < y；h : log x <= n * log y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Real.le_rpow_of_log_le`：le_rpow_of_log_le (hy : 0 < y) (h : log x <= z *
 log y) : x <= y ^ z
· 使用定理 `Real.rpow_intCast`：rpow_intCast (x : Real) (n : Int) : x ^ (n : Real) = 
x ^ n
-/
lemma le_zpow_of_log_le {n : ℤ} (hy : 0 < y) (h : log x ≤ n * log y) : x ≤ y ^ n :=
  rpow_intCast _ _ ▸ le_rpow_of_log_le hy h
/-
**Real.lt_rpow_iff_log_lt** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：lt_rpow_iff_log_lt (hx : 0 < x) (hy : 0 < y) : x < y ^ z ↔ log x < z * log
 y
参数：hx : 0 < x；hy : 0 < y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.log_lt_log_iff`：log_lt_log_iff (hx : 0 < x) (hy : 0 < y) : log x < 
log y ↔ x < y
· 使用定理 `Real.rpow_pos_of_pos`：rpow_pos_of_pos {x : Real} (hx : 0 < x) (y : Real)
 : 0 < x ^ y
· 使用定理 `Real.log_rpow`：log_rpow {x : Real} (hx : 0 < x) (y : Real) : log (x ^ y)
 = y * log x
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem lt_rpow_iff_log_lt (hx : 0 < x) (hy : 0 < y) : x < y ^ z ↔ log x < z * log y := by
  rw [← log_lt_log_iff hx (rpow_pos_of_pos hy z), log_rpow hy]
/-
**Real.lt_pow_iff_log_lt** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：lt_pow_iff_log_lt (hx : 0 < x) (hy : 0 < y) : x < y ^ n ↔ log x < n * log 
y
参数：hx : 0 < x；hy : 0 < y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.lt_rpow_iff_log_lt`：lt_rpow_iff_log_lt (hx : 0 < x) (hy : 0 < y) : 
x < y ^ z ↔ log x < z * log y
· 使用定理 `Real.rpow_natCast`：rpow_natCast (x : Real) (n : Nat) : x ^ (n : Real) = 
x ^ n
-/
lemma lt_pow_iff_log_lt (hx : 0 < x) (hy : 0 < y) : x < y ^ n ↔ log x < n * log y :=
  rpow_natCast _ _ ▸ lt_rpow_iff_log_lt hx hy
/-
**Real.lt_zpow_iff_log_lt** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：lt_zpow_iff_log_lt {n : Int} (hx : 0 < x) (hy : 0 < y) : x < y ^ n ↔ log x
 < n * log y
参数：hx : 0 < x；hy : 0 < y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.lt_rpow_iff_log_lt`：lt_rpow_iff_log_lt (hx : 0 < x) (hy : 0 < y) : 
x < y ^ z ↔ log x < z * log y
· 使用定理 `Real.rpow_intCast`：rpow_intCast (x : Real) (n : Int) : x ^ (n : Real) = 
x ^ n
-/
lemma lt_zpow_iff_log_lt {n : ℤ} (hx : 0 < x) (hy : 0 < y) : x < y ^ n ↔ log x < n * log y :=
  rpow_intCast _ _ ▸ lt_rpow_iff_log_lt hx hy
/-
**Real.lt_rpow_of_log_lt** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：lt_rpow_of_log_lt (hy : 0 < y) (h : log x < z * log y) : x < y ^ z
参数：hy : 0 < y；h : log x < z * log y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_or_gt`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b <
 a
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `Real.rpow_pos_of_pos`：rpow_pos_of_pos {x : Real} (hx : 0 < x) (y : Real)
 : 0 < x ^ y
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Real.lt_rpow_iff_log_lt`：lt_rpow_iff_log_lt (hx : 0 < x) (hy : 0 < y) : 
x < y ^ z ↔ log x < z * log y
-/
lemma lt_rpow_of_log_lt (hy : 0 < y) (h : log x < z * log y) : x < y ^ z := by
  obtain hx | hx := le_or_gt x 0
  · exact hx.trans_lt (rpow_pos_of_pos hy _)
  · exact (lt_rpow_iff_log_lt hx hy).2 h
/-
**Real.lt_pow_of_log_lt** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：lt_pow_of_log_lt (hy : 0 < y) (h : log x < n * log y) : x < y ^ n
参数：hy : 0 < y；h : log x < n * log y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Real.lt_rpow_of_log_lt`：lt_rpow_of_log_lt (hy : 0 < y) (h : log x < z * 
log y) : x < y ^ z
· 使用定理 `Real.rpow_natCast`：rpow_natCast (x : Real) (n : Nat) : x ^ (n : Real) = 
x ^ n
-/
lemma lt_pow_of_log_lt (hy : 0 < y) (h : log x < n * log y) : x < y ^ n :=
  rpow_natCast _ _ ▸ lt_rpow_of_log_lt hy h
/-
**Real.lt_zpow_of_log_lt** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：lt_zpow_of_log_lt {n : Int} (hy : 0 < y) (h : log x < n * log y) : x < y ^
 n
参数：hy : 0 < y；h : log x < n * log y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Real.lt_rpow_of_log_lt`：lt_rpow_of_log_lt (hy : 0 < y) (h : log x < z * 
log y) : x < y ^ z
· 使用定理 `Real.rpow_intCast`：rpow_intCast (x : Real) (n : Int) : x ^ (n : Real) = 
x ^ n
-/
lemma lt_zpow_of_log_lt {n : ℤ} (hy : 0 < y) (h : log x < n * log y) : x < y ^ n :=
  rpow_intCast _ _ ▸ lt_rpow_of_log_lt hy h
/-
**Real.rpow_le_iff_le_log** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：rpow_le_iff_le_log (hx : 0 < x) (hy : 0 < y) : x ^ z <= y ↔ z * log x <= l
og y
参数：hx : 0 < x；hy : 0 < y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.log_le_log_iff`：log_le_log_iff (h : 0 < x) (h₁ : 0 < y) : log x <= 
log y ↔ x <= y
· 使用定理 `Real.rpow_pos_of_pos`：rpow_pos_of_pos {x : Real} (hx : 0 < x) (y : Real)
 : 0 < x ^ y
· 使用定理 `Real.log_rpow`：log_rpow {x : Real} (hx : 0 < x) (y : Real) : log (x ^ y)
 = y * log x
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma rpow_le_iff_le_log (hx : 0 < x) (hy : 0 < y) : x ^ z ≤ y ↔ z * log x ≤ log y := by
  rw [← log_le_log_iff (rpow_pos_of_pos hx _) hy, log_rpow hx]
/-
**Real.pow_le_iff_le_log** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：pow_le_iff_le_log (hx : 0 < x) (hy : 0 < y) : x ^ n <= y ↔ n * log x <= lo
g y
参数：hx : 0 < x；hy : 0 < y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Real.rpow_le_iff_le_log`：rpow_le_iff_le_log (hx : 0 < x) (hy : 0 < y) : 
x ^ z <= y ↔ z * log x <= log y
· 使用定理 `Real.rpow_natCast`：rpow_natCast (x : Real) (n : Nat) : x ^ (n : Real) = 
x ^ n
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma pow_le_iff_le_log (hx : 0 < x) (hy : 0 < y) : x ^ n ≤ y ↔ n * log x ≤ log y := by
  rw [← rpow_le_iff_le_log hx hy, rpow_natCast]
/-
**Real.zpow_le_iff_le_log** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：zpow_le_iff_le_log {n : Int} (hx : 0 < x) (hy : 0 < y) : x ^ n <= y ↔ n * 
log x <= log y
参数：hx : 0 < x；hy : 0 < y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Real.rpow_le_iff_le_log`：rpow_le_iff_le_log (hx : 0 < x) (hy : 0 < y) : 
x ^ z <= y ↔ z * log x <= log y
· 使用定理 `Real.rpow_intCast`：rpow_intCast (x : Real) (n : Int) : x ^ (n : Real) = 
x ^ n
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma zpow_le_iff_le_log {n : ℤ} (hx : 0 < x) (hy : 0 < y) : x ^ n ≤ y ↔ n * log x ≤ log y := by
  rw [← rpow_le_iff_le_log hx hy, rpow_intCast]
/-
**Real.le_log_of_rpow_le** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：le_log_of_rpow_le (hx : 0 < x) (h : x ^ z <= y) : z * log x <= log y
参数：hx : 0 < x；h : x ^ z <= y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Real.log_le_log`：log_le_log (hx : 0 < x) (hxy : x <= y) : log x <= log y
· 使用定理 `Real.rpow_pos_of_pos`：rpow_pos_of_pos {x : Real} (hx : 0 < x) (y : Real)
 : 0 < x ^ y
· 使用定理 `Real.log_rpow`：log_rpow {x : Real} (hx : 0 < x) (y : Real) : log (x ^ y)
 = y * log x
-/
lemma le_log_of_rpow_le (hx : 0 < x) (h : x ^ z ≤ y) : z * log x ≤ log y :=
  log_rpow hx _ ▸ log_le_log (by positivity) h
/-
**Real.le_log_of_pow_le** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：le_log_of_pow_le (hx : 0 < x) (h : x ^ n <= y) : n * log x <= log y
参数：hx : 0 < x；h : x ^ n <= y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Real.le_log_of_rpow_le`：le_log_of_rpow_le (hx : 0 < x) (h : x ^ z <= y) 
: z * log x <= log y
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.rpow_natCast`：rpow_natCast (x : Real) (n : Nat) : x ^ (n : Real) = 
x ^ n
-/
lemma le_log_of_pow_le (hx : 0 < x) (h : x ^ n ≤ y) : n * log x ≤ log y :=
  le_log_of_rpow_le hx (rpow_natCast _ _ ▸ h)
/-
**Real.le_log_of_zpow_le** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：le_log_of_zpow_le {n : Int} (hx : 0 < x) (h : x ^ n <= y) : n * log x <= l
og y
参数：hx : 0 < x；h : x ^ n <= y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Real.le_log_of_rpow_le`：le_log_of_rpow_le (hx : 0 < x) (h : x ^ z <= y) 
: z * log x <= log y
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.rpow_intCast`：rpow_intCast (x : Real) (n : Int) : x ^ (n : Real) = 
x ^ n
-/
lemma le_log_of_zpow_le {n : ℤ} (hx : 0 < x) (h : x ^ n ≤ y) : n * log x ≤ log y :=
  le_log_of_rpow_le hx (rpow_intCast _ _ ▸ h)
/-
**Real.rpow_le_of_le_log** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：rpow_le_of_le_log (hy : 0 < y) (h : log x <= z * log y) : x <= y ^ z
参数：hy : 0 < y；h : log x <= z * log y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_or_gt`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b <
 a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Real.rpow_pos_of_pos`：rpow_pos_of_pos {x : Real} (hx : 0 < x) (y : Real)
 : 0 < x ^ y
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Real.le_rpow_iff_log_le`：le_rpow_iff_log_le (hx : 0 < x) (hy : 0 < y) : 
x <= y ^ z ↔ log x <= z * log y
-/
lemma rpow_le_of_le_log (hy : 0 < y) (h : log x ≤ z * log y) : x ≤ y ^ z := by
  obtain hx | hx := le_or_gt x 0
  · exact hx.trans (rpow_pos_of_pos hy _).le
  · exact (le_rpow_iff_log_le hx hy).2 h
/-
**Real.pow_le_of_le_log** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：pow_le_of_le_log (hy : 0 < y) (h : log x <= n * log y) : x <= y ^ n
参数：hy : 0 < y；h : log x <= n * log y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Real.rpow_le_of_le_log`：rpow_le_of_le_log (hy : 0 < y) (h : log x <= z *
 log y) : x <= y ^ z
· 使用定理 `Real.rpow_natCast`：rpow_natCast (x : Real) (n : Nat) : x ^ (n : Real) = 
x ^ n
-/
lemma pow_le_of_le_log (hy : 0 < y) (h : log x ≤ n * log y) : x ≤ y ^ n :=
  rpow_natCast _ _ ▸ rpow_le_of_le_log hy h
/-
**Real.zpow_le_of_le_log** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：zpow_le_of_le_log {n : Int} (hy : 0 < y) (h : log x <= n * log y) : x <= y
 ^ n
参数：hy : 0 < y；h : log x <= n * log y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Real.rpow_le_of_le_log`：rpow_le_of_le_log (hy : 0 < y) (h : log x <= z *
 log y) : x <= y ^ z
· 使用定理 `Real.rpow_intCast`：rpow_intCast (x : Real) (n : Int) : x ^ (n : Real) = 
x ^ n
-/
lemma zpow_le_of_le_log {n : ℤ} (hy : 0 < y) (h : log x ≤ n * log y) : x ≤ y ^ n :=
  rpow_intCast _ _ ▸ rpow_le_of_le_log hy h
/-
**Real.rpow_lt_iff_lt_log** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：rpow_lt_iff_lt_log (hx : 0 < x) (hy : 0 < y) : x ^ z < y ↔ z * log x < log
 y
参数：hx : 0 < x；hy : 0 < y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.log_lt_log_iff`：log_lt_log_iff (hx : 0 < x) (hy : 0 < y) : log x < 
log y ↔ x < y
· 使用定理 `Real.rpow_pos_of_pos`：rpow_pos_of_pos {x : Real} (hx : 0 < x) (y : Real)
 : 0 < x ^ y
· 使用定理 `Real.log_rpow`：log_rpow {x : Real} (hx : 0 < x) (y : Real) : log (x ^ y)
 = y * log x
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma rpow_lt_iff_lt_log (hx : 0 < x) (hy : 0 < y) : x ^ z < y ↔ z * log x < log y := by
  rw [← log_lt_log_iff (rpow_pos_of_pos hx _) hy, log_rpow hx]
/-
**Real.pow_lt_iff_lt_log** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：pow_lt_iff_lt_log (hx : 0 < x) (hy : 0 < y) : x ^ n < y ↔ n * log x < log 
y
参数：hx : 0 < x；hy : 0 < y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Real.rpow_lt_iff_lt_log`：rpow_lt_iff_lt_log (hx : 0 < x) (hy : 0 < y) : 
x ^ z < y ↔ z * log x < log y
· 使用定理 `Real.rpow_natCast`：rpow_natCast (x : Real) (n : Nat) : x ^ (n : Real) = 
x ^ n
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma pow_lt_iff_lt_log (hx : 0 < x) (hy : 0 < y) : x ^ n < y ↔ n * log x < log y := by
  rw [← rpow_lt_iff_lt_log hx hy, rpow_natCast]
/-
**Real.zpow_lt_iff_lt_log** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：zpow_lt_iff_lt_log {n : Int} (hx : 0 < x) (hy : 0 < y) : x ^ n < y ↔ n * l
og x < log y
参数：hx : 0 < x；hy : 0 < y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Real.rpow_lt_iff_lt_log`：rpow_lt_iff_lt_log (hx : 0 < x) (hy : 0 < y) : 
x ^ z < y ↔ z * log x < log y
· 使用定理 `Real.rpow_intCast`：rpow_intCast (x : Real) (n : Int) : x ^ (n : Real) = 
x ^ n
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma zpow_lt_iff_lt_log {n : ℤ} (hx : 0 < x) (hy : 0 < y) : x ^ n < y ↔ n * log x < log y := by
  rw [← rpow_lt_iff_lt_log hx hy, rpow_intCast]
/-
**Real.lt_log_of_rpow_lt** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：lt_log_of_rpow_lt (hx : 0 < x) (h : x ^ z < y) : z * log x < log y
参数：hx : 0 < x；h : x ^ z < y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.log_lt_log`：log_lt_log (hx : 0 < x) (h : x < y) : log x < log y
· 使用定理 `Real.rpow_pos_of_pos`：rpow_pos_of_pos {x : Real} (hx : 0 < x) (y : Real)
 : 0 < x ^ y
· 使用定理 `Real.log_rpow`：log_rpow {x : Real} (hx : 0 < x) (y : Real) : log (x ^ y)
 = y * log x
-/
lemma lt_log_of_rpow_lt (hx : 0 < x) (h : x ^ z < y) : z * log x < log y :=
  log_rpow hx _ ▸ log_lt_log (by positivity) h
/-
**Real.lt_log_of_pow_lt** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：lt_log_of_pow_lt (hx : 0 < x) (h : x ^ n < y) : n * log x < log y
参数：hx : 0 < x；h : x ^ n < y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Real.lt_log_of_rpow_lt`：lt_log_of_rpow_lt (hx : 0 < x) (h : x ^ z < y) :
 z * log x < log y
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.rpow_natCast`：rpow_natCast (x : Real) (n : Nat) : x ^ (n : Real) = 
x ^ n
-/
lemma lt_log_of_pow_lt (hx : 0 < x) (h : x ^ n < y) : n * log x < log y :=
  lt_log_of_rpow_lt hx (rpow_natCast _ _ ▸ h)
/-
**Real.lt_log_of_zpow_lt** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：lt_log_of_zpow_lt {n : Int} (hx : 0 < x) (h : x ^ n < y) : n * log x < log
 y
参数：hx : 0 < x；h : x ^ n < y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Real.lt_log_of_rpow_lt`：lt_log_of_rpow_lt (hx : 0 < x) (h : x ^ z < y) :
 z * log x < log y
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.rpow_intCast`：rpow_intCast (x : Real) (n : Int) : x ^ (n : Real) = 
x ^ n
-/
lemma lt_log_of_zpow_lt {n : ℤ} (hx : 0 < x) (h : x ^ n < y) : n * log x < log y :=
  lt_log_of_rpow_lt hx (rpow_intCast _ _ ▸ h)
/-
**Real.rpow_lt_of_lt_log** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：rpow_lt_of_lt_log (hy : 0 < y) (h : log x < z * log y) : x < y ^ z
参数：hy : 0 < y；h : log x < z * log y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_or_gt`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b <
 a
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `Real.rpow_pos_of_pos`：rpow_pos_of_pos {x : Real} (hx : 0 < x) (y : Real)
 : 0 < x ^ y
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Real.lt_rpow_iff_log_lt`：lt_rpow_iff_log_lt (hx : 0 < x) (hy : 0 < y) : 
x < y ^ z ↔ log x < z * log y
-/
lemma rpow_lt_of_lt_log (hy : 0 < y) (h : log x < z * log y) : x < y ^ z := by
  obtain hx | hx := le_or_gt x 0
  · exact hx.trans_lt (rpow_pos_of_pos hy _)
  · exact (lt_rpow_iff_log_lt hx hy).2 h
/-
**Real.pow_lt_of_lt_log** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：pow_lt_of_lt_log (hy : 0 < y) (h : log x < n * log y) : x < y ^ n
参数：hy : 0 < y；h : log x < n * log y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Real.rpow_lt_of_lt_log`：rpow_lt_of_lt_log (hy : 0 < y) (h : log x < z * 
log y) : x < y ^ z
· 使用定理 `Real.rpow_natCast`：rpow_natCast (x : Real) (n : Nat) : x ^ (n : Real) = 
x ^ n
-/
lemma pow_lt_of_lt_log (hy : 0 < y) (h : log x < n * log y) : x < y ^ n :=
  rpow_natCast _ _ ▸ rpow_lt_of_lt_log hy h
/-
**Real.zpow_lt_of_lt_log** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：zpow_lt_of_lt_log {n : Int} (hy : 0 < y) (h : log x < n * log y) : x < y ^
 n
参数：hy : 0 < y；h : log x < n * log y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Real.rpow_lt_of_lt_log`：rpow_lt_of_lt_log (hy : 0 < y) (h : log x < z * 
log y) : x < y ^ z
· 使用定理 `Real.rpow_intCast`：rpow_intCast (x : Real) (n : Int) : x ^ (n : Real) = 
x ^ n
-/
lemma zpow_lt_of_lt_log {n : ℤ} (hy : 0 < y) (h : log x < n * log y) : x < y ^ n :=
  rpow_intCast _ _ ▸ rpow_lt_of_lt_log hy h
/-
**Real.rpow_le_one_iff_of_pos** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：rpow_le_one_iff_of_pos (hx : 0 < x) : x ^ y <= 1 ↔ 1 <= x ∧ y <= 0 ∨ x <= 
1 ∧ 0 <= y
参数：hx : 0 < x。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.rpow_def_of_pos`：rpow_def_of_pos {x : Real} (hx : 0 < x) (y : Real)
 : x ^ y = exp (log x * y)
· 使用定理 `Real.exp_le_one_iff`：exp_le_one_iff {x : Real} : exp x <= 1 ↔ x <= 0
· 使用引理 `mul_nonpos_iff`：mul_nonpos_iff [MulPosStrictMono R] [PosMulStrictMono R]
 [AddLeftReflectLE R] [AddLeftMono R] : a * b <= 0 ↔ 0 <= a ∧ b <= 0 ∨ a <= 0 ∧ 
0 <=…
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Real.log_nonneg_iff`：log_nonneg_iff (hx : 0 < x) : 0 <= log x ↔ 1 <= x
· 使用定理 `Real.log_nonpos_iff`：log_nonpos_iff (hx : 0 <= x) : log x <= 0 ↔ x <= 1
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem rpow_le_one_iff_of_pos (hx : 0 < x) : x ^ y ≤ 1 ↔ 1 ≤ x ∧ y ≤ 0 ∨ x ≤ 1 ∧ 0 ≤ y := by
  rw [rpow_def_of_pos hx, exp_le_one_iff, mul_nonpos_iff, log_nonneg_iff hx, log_nonpos_iff hx.le]

/-- Bound for `|log x * x ^ t|` in the interval `(0, 1]`, for positive real `t`. -/
/-
**Real.abs_log_mul_self_rpow_lt** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：abs_log_mul_self_rpow_lt (x t : Real) (h1 : 0 < x) (h2 : x <= 1) (ht : 0 <
 t) : |log x * x ^ t| < 1 / t
参数：x t : Real；h1 : 0 < x；h2 : x <= 1；ht : 0 < t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `lt_div_iff₀`：lt_div_iff₀ (hc : 0 < c) : a < b / c ↔ a * c < b
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `Real.abs_log_mul_self_lt`：abs_log_mul_self_lt (x : Real) (h1 : 0 < x) (h
2 : x <= 1) : |log x * x| < 1
· 使用定理 `Real.rpow_pos_of_pos`：rpow_pos_of_pos {x : Real} (hx : 0 < x) (y : Real)
 : 0 < x ^ y
· 使用定理 `Real.rpow_le_one`：rpow_le_one {x z : Real} (hx1 : 0 <= x) (hx2 : x <= 1)
 (hz : 0 <= z) : x ^ z <= 1
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `abs_of_pos`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] {a
 : α} [AddLeftMono α], 0 < a → |a| = a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用引理 `abs_mul`：abs_mul (a b : α) : |a * b| = |a| * |b|
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Real.log_rpow`：log_rpow {x : Real} (hx : 0 < x) (y : Real) : log (x ^ y)
 = y * log x

--- 原说明 ---
Bound for `|log x * x ^ t|` in the interval `(0, 1]`, for positive real `t`.
-/
theorem abs_log_mul_self_rpow_lt (x t : ℝ) (h1 : 0 < x) (h2 : x ≤ 1) (ht : 0 < t) :
    |log x * x ^ t| < 1 / t := by
  rw [lt_div_iff₀ ht]
  have := abs_log_mul_self_lt (x ^ t) (rpow_pos_of_pos h1 t) (rpow_le_one h1.le h2 ht.le)
  rwa [log_rpow h1, mul_assoc, abs_mul, abs_of_pos ht, mul_comm] at this

/-- `log x` is bounded above by a multiple of every power of `x` with positive exponent. -/
/-
**Real.log_le_rpow_div** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：log_le_rpow_div {x ε : Real} (hx : 0 <= x) (hε : 0 < ε) : log x <= x ^ ε /
 ε
参数：hx : 0 <= x；hε : 0 < ε。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.eq_or_lt`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a = b ∨ a < b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.log_zero`：log_zero : log 0 = 0
· 使用定理 `Real.zero_rpow`：zero_rpow {x : Real} (h : x != 0) : (0 : Real) ^ x = 0
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `zero_div`：zero_div (a : G₀) : 0 / a = 0
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用引理 `le_div_iff₀'`：le_div_iff₀' (hc : 0 < c) : a <= b / c ↔ c * a <= b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Eq.trans_le`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a = b → b ≤ c →
 a ≤ c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.log_rpow`：log_rpow {x : Real} (hx : 0 < x) (y : Real) : log (x ^ y)
 = y * log x
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Real.log_le_sub_one_of_pos`：log_le_sub_one_of_pos {x : Real} (hx : 0 < x
) : log x <= x - 1
· 使用定理 `Real.rpow_pos_of_pos`：rpow_pos_of_pos {x : Real} (hx : 0 < x) (y : Real)
 : 0 < x ^ y
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用引理 `sub_one_lt`：sub_one_lt [ZeroLEOneClass R] [NeZero (1 : R)] [AddLeftStric
tMono R] (a : R) : a - 1 < a
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α

--- 原说明 ---
`log x` is bounded above by a multiple of every power of `x` with positive expon
ent.
-/
lemma log_le_rpow_div {x ε : ℝ} (hx : 0 ≤ x) (hε : 0 < ε) : log x ≤ x ^ ε / ε := by
  rcases hx.eq_or_lt with rfl | h
  · rw [log_zero, zero_rpow hε.ne', zero_div]
  rw [le_div_iff₀' hε]
  exact (log_rpow h ε).symm.trans_le <| (log_le_sub_one_of_pos <| rpow_pos_of_pos h ε).trans
    (sub_one_lt _).le

/-- The (real) logarithm of a natural number `n` is bounded by a multiple of every power of `n`
with positive exponent. -/
/-
**Real.log_natCast_le_rpow_div** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：log_natCast_le_rpow_div (n : Nat) {ε : Real} (hε : 0 < ε) : log n <= n ^ ε
 / ε
参数：n : Nat；hε : 0 < ε。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Real.log_le_rpow_div`：log_le_rpow_div {x ε : Real} (hx : 0 <= x) (hε : 0
 < ε) : log x <= x ^ ε / ε
· 使用定理 `Nat.cast_nonneg`：cast_nonneg {α} [Semiring α] [PartialOrder α] [IsOrdere
dRing α] (n : Nat) : 0 <= (n : α)

--- 原说明 ---
The (real) logarithm of a natural number `n` is bounded by a multiple of every p
ower of `n`
with positive exponent.
-/
lemma log_natCast_le_rpow_div (n : ℕ) {ε : ℝ} (hε : 0 < ε) : log n ≤ n ^ ε / ε :=
  log_le_rpow_div n.cast_nonneg hε
/-
**Real.strictMono_rpow_of_base_gt_one** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：strictMono_rpow_of_base_gt_one {b : Real} (hb : 1 < b) : StrictMono (b ^ ·
 : Real -> Real)
参数：hb : 1 < b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Real.rpow_def_of_pos`：rpow_def_of_pos {x : Real} (hx : 0 < x) (y : Real)
 : x ^ y = exp (log x * y)
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `StrictMono.comp`：∀ {α : Type u} {β : Type v} {γ : Type w} [inst : Preord
er α] [inst_1 : Preorder β] [inst_2 : Preorder γ] {g : β → γ}   {f : α → β}, Str
ictMo…
· 使用定理 `Real.exp_strictMono`：exp_strictMono : StrictMono exp
· 使用引理 `StrictMono.const_mul`：StrictMono.const_mul [PosMulStrictMono M₀] (hf : S
trictMono f) (ha : 0 < a) : StrictMono fun x => a * f x
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `strictMono_id`：strictMono_id [Preorder α] : StrictMono (id : α -> α)
· 使用定理 `Real.log_pos`：log_pos (hx : 1 < x) : 0 < log x
-/
lemma strictMono_rpow_of_base_gt_one {b : ℝ} (hb : 1 < b) :
    StrictMono (b ^ · : ℝ → ℝ) := by
  simp_rw [Real.rpow_def_of_pos (zero_lt_one.trans hb)]
  exact exp_strictMono.comp <| StrictMono.const_mul strictMono_id <| Real.log_pos hb
/-
**Real.monotone_rpow_of_base_ge_one** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：monotone_rpow_of_base_ge_one {b : Real} (hb : 1 <= b) : Monotone (b ^ · : 
Real -> Real)
参数：hb : 1 <= b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_or_eq_of_le`：lt_or_eq_of_le : a <= b -> a < b ∨ a = b
· 使用定理 `StrictMono.monotone`：∀ {α : Type u} {β : Type v} [inst : PartialOrder α]
 [inst_1 : Preorder β] {f : α → β}, StrictMono f → Monotone f
· 使用引理 `Real.strictMono_rpow_of_base_gt_one`：strictMono_rpow_of_base_gt_one {b :
 Real} (hb : 1 < b) : StrictMono (b ^ · : Real -> Real)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.one_rpow`：one_rpow (x : Real) : (1 : Real) ^ x = 1
-/
lemma monotone_rpow_of_base_ge_one {b : ℝ} (hb : 1 ≤ b) :
    Monotone (b ^ · : ℝ → ℝ) := by
  rcases lt_or_eq_of_le hb with hb | rfl
  case inl => exact (strictMono_rpow_of_base_gt_one hb).monotone
  case inr => intro _ _ _; simp
/-
**Real.strictAnti_rpow_of_base_lt_one** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：strictAnti_rpow_of_base_lt_one {b : Real} (hb₀ : 0 < b) (hb₁ : b < 1) : St
rictAnti (b ^ · : Real -> Real)
参数：hb₀ : 0 < b；hb₁ : b < 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Real.rpow_def_of_pos`：rpow_def_of_pos {x : Real} (hx : 0 < x) (y : Real)
 : x ^ y = exp (log x * y)
· 使用定理 `StrictMono.comp_strictAnti`：StrictMono.comp_strictAnti (hg : StrictMono 
g) (hf : StrictAnti f) : StrictAnti (g ∘ f)
· 使用定理 `Real.exp_strictMono`：exp_strictMono : StrictMono exp
· 使用定理 `StrictMono.const_mul_of_neg`：StrictMono.const_mul_of_neg [ExistsAddOfLE 
R] [PosMulStrictMono R] [AddRightStrictMono R] [AddRightReflectLT R] (hf : Stric
tMono f) (ha : a …
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
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
· 使用定理 `contravariant_swap_add_of_contravariant_add`：∀ (N : Type u_2) (r : N → N
 → Prop) [inst : AddCommSemigroup N] [ContravariantClass N N (fun x1 x2 => x1 + 
x2) r],   ContravariantClass N N …
· 使用定理 `strictMono_id`：strictMono_id [Preorder α] : StrictMono (id : α -> α)
· 使用定理 `Real.log_neg`：log_neg (h0 : 0 < x) (h1 : x < 1) : log x < 0
-/
lemma strictAnti_rpow_of_base_lt_one {b : ℝ} (hb₀ : 0 < b) (hb₁ : b < 1) :
    StrictAnti (b ^ · : ℝ → ℝ) := by
  simp_rw [Real.rpow_def_of_pos hb₀]
  exact exp_strictMono.comp_strictAnti <| StrictMono.const_mul_of_neg strictMono_id
      <| Real.log_neg hb₀ hb₁
/-
**Real.antitone_rpow_of_base_le_one** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：antitone_rpow_of_base_le_one {b : Real} (hb₀ : 0 < b) (hb₁ : b <= 1) : Ant
itone (b ^ · : Real -> Real)
参数：hb₀ : 0 < b；hb₁ : b <= 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_or_eq_of_le`：lt_or_eq_of_le : a <= b -> a < b ∨ a = b
· 使用定理 `StrictAnti.antitone`：∀ {α : Type u} {β : Type v} [inst : PartialOrder α]
 [inst_1 : Preorder β] {f : α → β}, StrictAnti f → Antitone f
· 使用引理 `Real.strictAnti_rpow_of_base_lt_one`：strictAnti_rpow_of_base_lt_one {b :
 Real} (hb₀ : 0 < b) (hb₁ : b < 1) : StrictAnti (b ^ · : Real -> Real)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.one_rpow`：one_rpow (x : Real) : (1 : Real) ^ x = 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma antitone_rpow_of_base_le_one {b : ℝ} (hb₀ : 0 < b) (hb₁ : b ≤ 1) :
    Antitone (b ^ · : ℝ → ℝ) := by
  rcases lt_or_eq_of_le hb₁ with hb₁ | rfl
  case inl => exact (strictAnti_rpow_of_base_lt_one hb₀ hb₁).antitone
  case inr => intro _ _ _; simp
/-
**Real.rpow_right_inj** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：rpow_right_inj (hx₀ : 0 < x) (hx₁ : x != 1) : x ^ y = x ^ z ↔ y = z
参数：hx₀ : 0 < x；hx₁ : x != 1。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ne.lt_or_gt`：Ne.lt_or_gt (h : a != b) : a < b ∨ b < a
· 使用定理 `StrictAnti.injective`：StrictAnti.injective (hf : StrictAnti f) : Injecti
ve f
· 使用引理 `Real.strictAnti_rpow_of_base_lt_one`：strictAnti_rpow_of_base_lt_one {b :
 Real} (hb₀ : 0 < b) (hb₁ : b < 1) : StrictAnti (b ^ · : Real -> Real)
· 使用定理 `StrictMono.injective`：StrictMono.injective (hf : StrictMono f) : Injecti
ve f
· 使用引理 `Real.strictMono_rpow_of_base_gt_one`：strictMono_rpow_of_base_gt_one {b :
 Real} (hb : 1 < b) : StrictMono (b ^ · : Real -> Real)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
lemma rpow_right_inj (hx₀ : 0 < x) (hx₁ : x ≠ 1) : x ^ y = x ^ z ↔ y = z := by
  refine ⟨fun H ↦ ?_, fun H ↦ by rw [H]⟩
  rcases hx₁.lt_or_gt with h | h
  · exact (strictAnti_rpow_of_base_lt_one hx₀ h).injective H
  · exact (strictMono_rpow_of_base_gt_one h).injective H

/-- Guessing rule for the `bound` tactic: when trying to prove `x ^ y ≤ x ^ z`, we can either assume
`1 ≤ x` or `0 < x ≤ 1`. -/
/-
**Real.rpow_le_rpow_of_exponent_le_or_ge** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：∀ {x y z : ℝ}, 1 ≤ x ∧ y ≤ z ∨ 0 < x ∧ x ≤ 1 ∧ z ≤ y → x ^ y ≤ x ^ z
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.rpow_le_rpow_of_exponent_le`：rpow_le_rpow_of_exponent_le (hx : 1 <=
 x) (hyz : y <= z) : x ^ y <= x ^ z
· 使用定理 `Real.rpow_le_rpow_of_exponent_ge`：rpow_le_rpow_of_exponent_ge (hx0 : 0 <
 x) (hx1 : x <= 1) (hyz : z <= y) : x ^ y <= x ^ z

--- 原说明 ---
Guessing rule for the `bound` tactic: when trying to prove `x ^ y ≤ x ^ z`, we c
an either assume
`1 ≤ x` or `0 < x ≤ 1`.
-/
@[bound] lemma rpow_le_rpow_of_exponent_le_or_ge {x y z : ℝ}
    (h : 1 ≤ x ∧ y ≤ z ∨ 0 < x ∧ x ≤ 1 ∧ z ≤ y) : x ^ y ≤ x ^ z := by
  rcases h with ⟨x1, yz⟩ | ⟨x0, x1, zy⟩
  · exact Real.rpow_le_rpow_of_exponent_le x1 yz
  · exact Real.rpow_le_rpow_of_exponent_ge x0 x1 zy

end Real

namespace Complex

/-
**Complex.norm_prime_cpow_le_one_half** 是 Mathlib 中的一个引理，位于命名空间 `Complex`。
形式化陈述：norm_prime_cpow_le_one_half (p : Nat.Primes) {s : Complex} (hs : 1 < s.re)
 : ‖(p : Complex) ^ (-s)‖ <= 1 / 2
参数：p : Nat.Primes；hs : 1 < s.re。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Complex.norm_natCast_cpow_of_re_ne_zero`：norm_natCast_cpow_of_re_ne_zero
 (n : Nat) {s : Complex} (hs : s.re != 0) : ‖(n : Complex) ^ s‖ = (n : Real) ^ (
s.re)
· 使用定理 `Complex.neg_re`：neg_re (z : Complex) : (-z).re = -z.re
· 使用定理 `Not.intro`：∀ {a : Prop}, (a → False) → ¬a
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b : R}, a = a' → -a' = b → -a = b
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
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
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_mul`：∀ {R : Type u_2} [inst : CommRing R]
 (a₁ : R) (a₂ : ℕ) {a₃ b : R}, -a₃ = b → -(a₁ ^ a₂ * a₃) = a₁ ^ a₂ * b
· 使用定理 `Mathlib.Tactic.Ring.cast_zero`：∀ {R : Type u_1} [inst : CommSemiring R] 
{a : R}, Mathlib.Meta.NormNum.IsNat a 0 → a = 0
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_isNat`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsInt a (Int.ofNat n) → Mathlib.Meta.NormN
um.IsNat a n
· 使用定理 `Mathlib.Meta.NormNum.IsInt.of_raw`：∀ (α : Type u_1) [inst : Ring α] (n :
 ℤ), Mathlib.Meta.NormNum.IsInt n.rawCast n
（共 58 条，此处仅展示前 30 条）
-/
lemma norm_prime_cpow_le_one_half (p : Nat.Primes) {s : ℂ} (hs : 1 < s.re) :
    ‖(p : ℂ) ^ (-s)‖ ≤ 1 / 2 := by
  rw [norm_natCast_cpow_of_re_ne_zero p <| by rw [neg_re]; linarith only [hs]]
  refine (Real.rpow_le_rpow_of_nonpos zero_lt_two (Nat.cast_le.mpr p.prop.two_le) <|
    by rw [neg_re]; linarith only [hs]).trans ?_
  rw [one_div, ← Real.rpow_neg_one]
  exact Real.rpow_le_rpow_of_exponent_le one_le_two <| (neg_lt_neg hs).le
/-
**Complex.one_sub_prime_cpow_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 `Complex`。
形式化陈述：one_sub_prime_cpow_ne_zero {p : Nat} (hp : p.Prime) {s : Complex} (hs : 1 
< s.re) : 1 - (p : Complex) ^ (-s) != 0
参数：hp : p.Prime；hs : 1 < s.re。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sub_ne_zero_of_ne`：∀ {α : Type u_1} [inst : SubtractionMonoid α] {a b : 
α}, a ≠ b → a - b ≠ 0
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `Complex.norm_prime_cpow_le_one_half`：norm_prime_cpow_le_one_half (p : Na
t.Primes) {s : Complex} (hs : 1 < s.re) : ‖(p : Complex) ^ (-s)‖ <= 1 / 2
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Mathlib.Meta.NormNum.isRat_le_false`：isRat_le_false [Ring α] [LinearOrde
r α] [IsStrictOrderedRing α] {a b : α} {na nb : Int} {da db : Nat} (ha : IsRat a
 na da) (hb : IsRat b nb …
· 使用定理 `Mathlib.Meta.NormNum.IsNNRat.to_isRat`：∀ {α : Type u_1} [inst : Ring α] 
{a : α} {n d : ℕ},   Mathlib.Meta.NormNum.IsNNRat a n d → Mathlib.Meta.NormNum.I
sRat a (Int.ofNat n) d
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isNNRat`：∀ {α : Type u_1} [inst : Semiring
 α] {a : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsN
NRat a n 1
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_div`：∀ {α : Type u} [inst : DivisionSemirin
g α] {a b : α} {cn cd : ℕ},   Mathlib.Meta.NormNum.IsNNRat (a * b⁻¹) cn cd → Mat
hlib.Meta.NormNum.IsNN…
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_mul`：isNNRat_mul {α} [Semiring α] {f : α ->
 α -> α} {a b : α} {na nb nc : Nat} {da db dc k : Nat} : f = HMul.hMul -> IsNNRa
t a na da -> IsNNRat b…
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_inv_pos`：isNNRat_inv_pos {α} [DivisionSemir
ing α] [CharZero α] {a : α} {n d : Nat} : IsNNRat a (Nat.succ n) d -> IsNNRat a⁻
¹ d (Nat.succ n)
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NormOneClass.norm_one`：∀ {α : Type u_5} {inst : Norm α} {inst_1 : One α}
 [self : NormOneClass α], ‖1‖ = 1
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma one_sub_prime_cpow_ne_zero {p : ℕ} (hp : p.Prime) {s : ℂ} (hs : 1 < s.re) :
    1 - (p : ℂ) ^ (-s) ≠ 0 := by
  refine sub_ne_zero_of_ne fun H ↦ ?_
  have := norm_prime_cpow_le_one_half ⟨p, hp⟩ hs
  simp only at this
  rw [← H, norm_one] at this
  norm_num at this
/-
**Complex.norm_natCast_cpow_le_norm_natCast_cpow_of_pos** 是 Mathlib 中的一个引理，位于命名空
间 `Complex`。
形式化陈述：norm_natCast_cpow_le_norm_natCast_cpow_of_pos {n : Nat} (hn : 0 < n) {w z 
: Complex} (h : w.re <= z.re) : ‖(n : Complex) ^ w‖ <= ‖(n : Complex) ^ z‖
参数：hn : 0 < n；h : w.re <= z.re。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Complex.norm_natCast_cpow_of_pos`：norm_natCast_cpow_of_pos {n : Nat} (hn
 : 0 < n) (s : Complex) : ‖(n : Complex) ^ s‖ = (n : Real) ^ (s.re)
· 使用定理 `Real.rpow_le_rpow_of_exponent_le`：rpow_le_rpow_of_exponent_le (hx : 1 <=
 x) (hyz : y <= z) : x ^ y <= x ^ z
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
-/
lemma norm_natCast_cpow_le_norm_natCast_cpow_of_pos {n : ℕ} (hn : 0 < n) {w z : ℂ}
    (h : w.re ≤ z.re) :
    ‖(n : ℂ) ^ w‖ ≤ ‖(n : ℂ) ^ z‖ := by
  simp_rw [norm_natCast_cpow_of_pos hn]
  exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) h
/-
**Complex.norm_natCast_cpow_le_norm_natCast_cpow_iff** 是 Mathlib 中的一个引理，位于命名空间 `
Complex`。
形式化陈述：norm_natCast_cpow_le_norm_natCast_cpow_iff {n : Nat} (hn : 1 < n) {w z : C
omplex} : ‖(n : Complex) ^ w‖ <= ‖(n : Complex) ^ z‖ ↔ w.re <= z.re
参数：hn : 1 < n。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `Complex.norm_natCast_cpow_of_pos`：norm_natCast_cpow_of_pos {n : Nat} (hn
 : 0 < n) (s : Complex) : ‖(n : Complex) ^ s‖ = (n : Real) ^ (s.re)
· 使用定理 `Nat.zero_lt_of_lt`：∀ {a b : ℕ}, a < b → 0 < b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Real.rpow_le_rpow_left_iff`：rpow_le_rpow_left_iff (hx : 1 < x) : x ^ y <
= x ^ z ↔ y <= z
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.one_lt_cast`：one_lt_cast : 1 < (n : α) ↔ 1 < n
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma norm_natCast_cpow_le_norm_natCast_cpow_iff {n : ℕ} (hn : 1 < n) {w z : ℂ} :
    ‖(n : ℂ) ^ w‖ ≤ ‖(n : ℂ) ^ z‖ ↔ w.re ≤ z.re := by
  simp_rw [norm_natCast_cpow_of_pos (Nat.zero_lt_of_lt hn),
    Real.rpow_le_rpow_left_iff (Nat.one_lt_cast.mpr hn)]
/-
**Complex.norm_log_natCast_le_rpow_div** 是 Mathlib 中的一个引理，位于命名空间 `Complex`。
形式化陈述：norm_log_natCast_le_rpow_div (n : Nat) {ε : Real} (hε : 0 < ε) : ‖log n‖ <
= n ^ ε / ε
参数：n : Nat；hε : 0 < ε。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.eq_zero_or_pos`：∀ (n : ℕ), n = 0 ∨ n > 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Complex.log_zero`：log_zero : log 0 = 0
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `Real.zero_rpow`：zero_rpow {x : Real} (h : x != 0) : (0 : Real) ^ x = 0
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `zero_div`：zero_div (a : G₀) : 0 / a = 0
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Complex.natCast_log`：natCast_log {n : Nat} : Real.log n = log n
· 使用引理 `Complex.norm_real`：norm_real (r : Real) : ‖(r : Complex)‖ = ‖r‖
· 使用定理 `Real.norm_of_nonneg`：norm_of_nonneg (hr : 0 <= r) : ‖r‖ = r
· 使用定理 `Real.log_nonneg`：log_nonneg (hx : 1 <= x) : 0 <= log x
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Nat.one_le_of_lt`：∀ {a b : ℕ}, a < b → 1 ≤ b
· 使用定理 `GT.gt.lt`：∀ {α : Type u_2} [inst : LT α] {a b : α}, a > b → b < a
· 使用引理 `Real.log_natCast_le_rpow_div`：log_natCast_le_rpow_div (n : Nat) {ε : Rea
l} (hε : 0 < ε) : log n <= n ^ ε / ε
-/
lemma norm_log_natCast_le_rpow_div (n : ℕ) {ε : ℝ} (hε : 0 < ε) : ‖log n‖ ≤ n ^ ε / ε := by
  rcases n.eq_zero_or_pos with rfl | h
  · rw [Nat.cast_zero, Nat.cast_zero, log_zero, norm_zero, Real.zero_rpow hε.ne', zero_div]
  rw [← natCast_log, norm_real, norm_of_nonneg <| Real.log_nonneg <| by
    exact_mod_cast Nat.one_le_of_lt h.lt]
  exact Real.log_natCast_le_rpow_div n hε

end Complex


/-!
## Square roots of reals
-/


namespace Real

variable {z x y : ℝ}

section Sqrt

/-
**Real.sqrt_eq_rpow** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：sqrt_eq_rpow (x : Real) : √x = x ^ (1 / (2 : Real))
参数：x : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `le_or_gt`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b <
 a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_self_inj_of_nonneg`：mul_self_inj_of_nonneg {α : Type*} [CommRing α] 
[NoZeroDivisors α] [PartialOrder α] [IsStrictOrderedRing α] {a b : α} (a0 : 0 <=
 a) (b0 : 0 …
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `Real.sqrt_nonneg`：∀ (x : ℝ), 0 ≤ √x
· 使用定理 `Real.rpow_nonneg`：rpow_nonneg {x : Real} (hx : 0 <= x) (y : Real) : 0 <=
 x ^ y
· 使用定理 `Real.mul_self_sqrt`：mul_self_sqrt (h : 0 <= x) : √x * √x = x
· 使用定理 `sq`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `Real.rpow_natCast`：rpow_natCast (x : Real) (n : Nat) : x ^ (n : Real) = 
x ^ n
· 使用定理 `Real.rpow_mul`：rpow_mul {x : Real} (hx : 0 <= x) (y z : Real) : x ^ (y *
 z) = (x ^ y) ^ z
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `inv_mul_cancel₀`：inv_mul_cancel₀ (h : a != 0) : a⁻¹ * a = 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Real.rpow_one`：rpow_one (x : Real) : x ^ (1 : Real) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.div_congr`：∀ {R : Type u_2} [inst : Semifield
 R] {a a' b b' c : R}, a = a' → b = b' → a' / b' = c → a / b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `Mathlib.Tactic.Ring.Common.div_pf`：∀ {R : Type u_2} [inst : Semifield R]
 {a b c d : R}, b⁻¹ = c → a * c = d → a / b = d
（共 51 条，此处仅展示前 30 条）
-/
theorem sqrt_eq_rpow (x : ℝ) : √x = x ^ (1 / (2 : ℝ)) := by
  obtain h | h := le_or_gt 0 x
  · rw [← mul_self_inj_of_nonneg (sqrt_nonneg _) (rpow_nonneg h _), mul_self_sqrt h, ← sq,
      ← rpow_natCast, ← rpow_mul h]
    simp
  · have : 1 / (2 : ℝ) * π = π / (2 : ℝ) := by ring
    rw [sqrt_eq_zero_of_nonpos h.le, rpow_def_of_neg h, this, cos_pi_div_two, mul_zero]
/-
**Real.rpow_div_two_eq_sqrt** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：rpow_div_two_eq_sqrt {x : Real} (r : Real) (hx : 0 <= x) : x ^ (r / 2) = √
x ^ r
参数：r : Real；hx : 0 <= x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.sqrt_eq_rpow`：sqrt_eq_rpow (x : Real) : √x = x ^ (1 / (2 : Real))
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.rpow_mul`：rpow_mul {x : Real} (hx : 0 <= x) (y z : Real) : x ^ (y *
 z) = (x ^ y) ^ z
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.div_congr`：∀ {R : Type u_2} [inst : Semifield
 R] {a a' b b' c : R}, a = a' → b = b' → a' / b' = c → a / b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `Mathlib.Tactic.Ring.Common.div_pf`：∀ {R : Type u_2} [inst : Semifield R]
 {a b c d : R}, b⁻¹ = c → a * c = d → a / b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.inv_single`：∀ {R : Type u_2} [inst : Semifiel
d R] {a b : R}, a⁻¹ = b → (a + 0)⁻¹ = b + 0
· 使用定理 `Mathlib.Meta.NormNum.IsNNRat.to_raw_eq`：∀ {α : Type u} {n d : ℕ} [inst :
 DivisionSemiring α] {a : α}, Mathlib.Meta.NormNum.IsNNRat a n d → a = NNRat.raw
Cast n d
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_inv_pos`：isNNRat_inv_pos {α} [DivisionSemir
ing α] [CharZero α] {a : α} {n d : Nat} : IsNNRat a (Nat.succ n) d -> IsNNRat a⁻
¹ d (Nat.succ n)
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isNNRat`：∀ {α : Type u_1} [inst : Semiring
 α] {a : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsN
NRat a n 1
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_left`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₃ b c : R} (a₁ : R) (a₂ : ℕ), a₃ * b = c → a₁ ^ a₂ * a₃ * b = a₁ ^ a₂
 * c
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_mul`：isNNRat_mul {α} [Semiring α] {f : α ->
 α -> α} {a b : α} {na nb nc : Nat} {da db dc k : Nat} : f = HMul.hMul -> IsNNRa
t a na da -> IsNNRat b…
· 使用定理 `Mathlib.Meta.NormNum.IsNNRat.of_raw`：∀ (α : Type u_1) [inst : DivisionSe
miring α] (n d : ℕ), ↑d ≠ 0 → Mathlib.Meta.NormNum.IsNNRat (NNRat.rawCast n d) n
 d
· 使用定理 `Mathlib.Meta.NormNum.IsNNRat.den_nz`：∀ {α : Type u_1} [inst : DivisionSe
miring α] {a : α} {n d : ℕ}, Mathlib.Meta.NormNum.IsNNRat a n d → ↑d ≠ 0
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.zero_mul`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (b : R), 0 * b = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
（共 31 条，此处仅展示前 30 条）
-/
theorem rpow_div_two_eq_sqrt {x : ℝ} (r : ℝ) (hx : 0 ≤ x) : x ^ (r / 2) = √x ^ r := by
  rw [sqrt_eq_rpow, ← rpow_mul hx]
  congr
  ring

end Sqrt

end Real

namespace Complex

/-
**Complex.cpow_inv_two_re** 是 Mathlib 中的一个引理，位于命名空间 `Complex`。
形式化陈述：cpow_inv_two_re (x : Complex) : (x ^ (2⁻¹ : Complex)).re = √((‖x‖ + x.re) 
/ 2)
参数：x : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Complex.ofReal_ofNat`：∀ (n : ℕ) [inst : n.AtLeastTwo], ↑(OfNat.ofNat n) 
= OfNat.ofNat n
· 使用定理 `Complex.ofReal_inv`：ofReal_inv (r : Real) : ((r⁻¹ : Real) : Complex) = (
r : Complex)⁻¹
· 使用引理 `Complex.cpow_ofReal_re`：cpow_ofReal_re (x : Complex) (y : Real) : (x ^ (
y : Complex)).re = ‖x‖ ^ y * Real.cos (arg x * y)
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `Real.sqrt_eq_rpow`：sqrt_eq_rpow (x : Real) : √x = x ^ (1 / (2 : Real))
· 使用引理 `Real.cos_half`：cos_half {x : Real} (hl : -π <= x) (hr : x <= π) : cos (x
 / 2) = √((1 + cos x) / 2)
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Complex.neg_pi_lt_arg`：neg_pi_lt_arg (x : Complex) : -π < arg x
· 使用定理 `Complex.arg_le_pi`：arg_le_pi (x : Complex) : arg x <= π
· 使用定理 `Real.sqrt_mul`：sqrt_mul {x : Real} (hx : 0 <= x) (y : Real) : √(x * y) =
 √x * √y
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `mul_div_assoc`：mul_div_assoc (a b c : G) : a * b / c = a * (b / c)
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用引理 `Complex.norm_mul_cos_arg`：norm_mul_cos_arg (x : Complex) : ‖x‖ * Real.co
s (arg x) = x.re
-/
lemma cpow_inv_two_re (x : ℂ) : (x ^ (2⁻¹ : ℂ)).re = √((‖x‖ + x.re) / 2) := by
  rw [← ofReal_ofNat, ← ofReal_inv, cpow_ofReal_re, ← div_eq_mul_inv, ← one_div,
    ← Real.sqrt_eq_rpow, cos_half, ← sqrt_mul, ← mul_div_assoc, mul_add, mul_one, norm_mul_cos_arg]
  exacts [norm_nonneg _, (neg_pi_lt_arg _).le, arg_le_pi _]
/-
**Complex.cpow_inv_two_im_eq_sqrt** 是 Mathlib 中的一个引理，位于命名空间 `Complex`。
形式化陈述：cpow_inv_two_im_eq_sqrt {x : Complex} (hx : 0 <= x.im) : (x ^ (2⁻¹ : Compl
ex)).im = √((‖x‖ - x.re) / 2)
参数：hx : 0 <= x.im。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Complex.ofReal_ofNat`：∀ (n : ℕ) [inst : n.AtLeastTwo], ↑(OfNat.ofNat n) 
= OfNat.ofNat n
· 使用定理 `Complex.ofReal_inv`：ofReal_inv (r : Real) : ((r⁻¹ : Real) : Complex) = (
r : Complex)⁻¹
· 使用引理 `Complex.cpow_ofReal_im`：cpow_ofReal_im (x : Complex) (y : Real) : (x ^ (
y : Complex)).im = ‖x‖ ^ y * Real.sin (arg x * y)
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `Real.sqrt_eq_rpow`：sqrt_eq_rpow (x : Real) : √x = x ^ (1 / (2 : Real))
· 使用引理 `Real.sin_half_eq_sqrt`：sin_half_eq_sqrt {x : Real} (hl : 0 <= x) (hr : x
 <= 2 * π) : sin (x / 2) = √((1 - cos x) / 2)
· 使用定理 `Complex.arg_nonneg_iff`：arg_nonneg_iff {z : Complex} : 0 <= arg z ↔ 0 <=
 z.im
· 使用引理 `le_of_not_gt`：le_of_not_gt (h : ¬b < a) : a <= b
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_right`：∀ {R : Type u_1} [inst : CommSe
miring R] {a b₃ c : R} (b₁ : R) (b₂ : ℕ), a * b₃ = c → a * (b₁ ^ b₂ * b₃) = b₁ ^
 b₂ * c
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
（共 62 条，此处仅展示前 30 条）
-/
lemma cpow_inv_two_im_eq_sqrt {x : ℂ} (hx : 0 ≤ x.im) :
    (x ^ (2⁻¹ : ℂ)).im = √((‖x‖ - x.re) / 2) := by
  rw [← ofReal_ofNat, ← ofReal_inv, cpow_ofReal_im, ← div_eq_mul_inv, ← one_div,
    ← Real.sqrt_eq_rpow, sin_half_eq_sqrt, ← sqrt_mul (norm_nonneg _), ← mul_div_assoc, mul_sub,
    mul_one, norm_mul_cos_arg]
  · rwa [arg_nonneg_iff]
  · linarith [pi_pos, arg_le_pi x]
/-
**Complex.cpow_inv_two_im_eq_neg_sqrt** 是 Mathlib 中的一个引理，位于命名空间 `Complex`。
形式化陈述：cpow_inv_two_im_eq_neg_sqrt {x : Complex} (hx : x.im < 0) : (x ^ (2⁻¹ : Co
mplex)).im = -√((‖x‖ - x.re) / 2)
参数：hx : x.im < 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Complex.ofReal_ofNat`：∀ (n : ℕ) [inst : n.AtLeastTwo], ↑(OfNat.ofNat n) 
= OfNat.ofNat n
· 使用定理 `Complex.ofReal_inv`：ofReal_inv (r : Real) : ((r⁻¹ : Real) : Complex) = (
r : Complex)⁻¹
· 使用引理 `Complex.cpow_ofReal_im`：cpow_ofReal_im (x : Complex) (y : Real) : (x ^ (
y : Complex)).im = ‖x‖ ^ y * Real.sin (arg x * y)
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `Real.sqrt_eq_rpow`：sqrt_eq_rpow (x : Real) : √x = x ^ (1 / (2 : Real))
· 使用引理 `Real.sin_half_eq_neg_sqrt`：sin_half_eq_neg_sqrt {x : Real} (hl : -(2 * π
) <= x) (hr : x <= 0) : sin (x / 2) = -√((1 - cos x) / 2)
· 使用引理 `le_of_not_gt`：le_of_not_gt (h : ¬b < a) : a <= b
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b : R}, a = a' → -a' = b → -a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_right`：∀ {R : Type u_1} [inst : CommSe
miring R] {a b₃ c : R} (b₁ : R) (b₂ : ℕ), a * b₃ = c → a * (b₁ ^ b₂ * b₃) = b₁ ^
 b₂ * c
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
（共 64 条，此处仅展示前 30 条）
-/
lemma cpow_inv_two_im_eq_neg_sqrt {x : ℂ} (hx : x.im < 0) :
    (x ^ (2⁻¹ : ℂ)).im = -√((‖x‖ - x.re) / 2) := by
  rw [← ofReal_ofNat, ← ofReal_inv, cpow_ofReal_im, ← div_eq_mul_inv, ← one_div,
    ← Real.sqrt_eq_rpow, sin_half_eq_neg_sqrt, mul_neg, ← sqrt_mul (norm_nonneg _),
    ← mul_div_assoc, mul_sub, mul_one, norm_mul_cos_arg]
  · linarith [pi_pos, neg_pi_lt_arg x]
  · exact (arg_neg_iff.2 hx).le
/-
**Complex.abs_cpow_inv_two_im** 是 Mathlib 中的一个引理，位于命名空间 `Complex`。
形式化陈述：abs_cpow_inv_two_im (x : Complex) : |(x ^ (2⁻¹ : Complex)).im| = √((‖x‖ - 
x.re) / 2)
参数：x : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Complex.ofReal_ofNat`：∀ (n : ℕ) [inst : n.AtLeastTwo], ↑(OfNat.ofNat n) 
= OfNat.ofNat n
· 使用定理 `Complex.ofReal_inv`：ofReal_inv (r : Real) : ((r⁻¹ : Real) : Complex) = (
r : Complex)⁻¹
· 使用引理 `Complex.cpow_ofReal_im`：cpow_ofReal_im (x : Complex) (y : Real) : (x ^ (
y : Complex)).im = ‖x‖ ^ y * Real.sin (arg x * y)
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `Real.sqrt_eq_rpow`：sqrt_eq_rpow (x : Real) : √x = x ^ (1 / (2 : Real))
· 使用引理 `abs_mul`：abs_mul (a b : α) : |a * b| = |a| * |b|
· 使用定理 `abs_of_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α]
 {a : α} [AddLeftMono α], 0 ≤ a → |a| = a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Real.sqrt_nonneg`：∀ (x : ℝ), 0 ≤ √x
· 使用引理 `Real.abs_sin_half`：abs_sin_half (x : Real) : |sin (x / 2)| = √((1 - cos 
x) / 2)
· 使用定理 `Real.sqrt_mul`：sqrt_mul {x : Real} (hx : 0 <= x) (y : Real) : √(x * y) =
 √x * √y
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `mul_div_assoc`：mul_div_assoc (a b c : G) : a * b / c = a * (b / c)
· 使用定理 `mul_sub`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), a 
* (b - c) = a * b - a * c
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用引理 `Complex.norm_mul_cos_arg`：norm_mul_cos_arg (x : Complex) : ‖x‖ * Real.co
s (arg x) = x.re
-/
lemma abs_cpow_inv_two_im (x : ℂ) : |(x ^ (2⁻¹ : ℂ)).im| = √((‖x‖ - x.re) / 2) := by
  rw [← ofReal_ofNat, ← ofReal_inv, cpow_ofReal_im, ← div_eq_mul_inv, ← one_div,
    ← Real.sqrt_eq_rpow, abs_mul, abs_of_nonneg (sqrt_nonneg _), abs_sin_half,
    ← sqrt_mul (norm_nonneg _), ← mul_div_assoc, mul_sub, mul_one, norm_mul_cos_arg]

open scoped ComplexOrder in
/-
**Complex.inv_natCast_cpow_ofReal_pos** 是 Mathlib 中的一个引理，位于命名空间 `Complex`。
形式化陈述：inv_natCast_cpow_ofReal_pos {n : Nat} (hn : n != 0) (x : Real) : 0 < ((n :
 Complex) ^ (x : Complex))⁻¹
参数：hn : n != 0；x : Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RCLike.inv_pos_of_pos`：∀ {K : Type u_1} [inst : RCLike K] {z : K}, 0 < z
 → 0 < z⁻¹
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Complex.ofReal_cpow`：ofReal_cpow {x : Real} (hx : 0 <= x) (y : Real) : (
(x ^ y : Real) : Complex) = (x : Complex) ^ (y : Complex)
· 使用定理 `Nat.cast_nonneg'`：cast_nonneg' (n : Nat) : 0 <= (n : α)
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Mathlib.Meta.Positivity.ofReal_pos`：∀ {x : ℝ}, 0 < x → 0 < ↑x
· 使用定理 `Real.rpow_pos_of_pos`：rpow_pos_of_pos {x : Real} (hx : 0 < x) (y : Real)
 : 0 < x ^ y
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.cast_pos'`：cast_pos' {n : Nat} : (0 : α) < n ↔ 0 < n
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `lt_of_le_of_ne'`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, b ≤
 a → a ≠ b → b < a
· 使用定理 `zero_le`：∀ {α : Type u_1} [inst : LE α] [inst_1 : Zero α] [IsBotZeroClas
s α] {a : α}, 0 ≤ a
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
-/
lemma inv_natCast_cpow_ofReal_pos {n : ℕ} (hn : n ≠ 0) (x : ℝ) :
    0 < ((n : ℂ) ^ (x : ℂ))⁻¹ := by
  refine RCLike.inv_pos_of_pos ?_
  rw [show (n : ℂ) ^ (x : ℂ) = (n : ℝ) ^ (x : ℂ) from rfl, ← ofReal_cpow n.cast_nonneg']
  positivity

end Complex

section Tactics

/-!
## Tactic extensions for real powers
-/
namespace Mathlib.Meta.NormNum

open Lean.Meta Qq

/-
**Mathlib.Meta.NormNum.IsNat.rpow_eq_pow** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Meta
.NormNum.IsNat`。
形式化陈述：∀ {b : ℝ} {n : ℕ}, Mathlib.Meta.NormNum.IsNat b n → ∀ (a : ℝ), a ^ b = a ^
 n
参数：a : ℝ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Mathlib.Meta.NormNum.IsNat.out`：∀ {α : Type u} [inst : AddMonoidWithOne 
α] {a : α} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = ↑n
· 使用定理 `Real.rpow_natCast`：rpow_natCast (x : Real) (n : Nat) : x ^ (n : Real) = 
x ^ n
-/
theorem IsNat.rpow_eq_pow {b : ℝ} {n : ℕ} (h : IsNat b n) (a : ℝ) : a ^ b = a ^ n := by
  rw [h.1, Real.rpow_natCast]
/-
**Mathlib.Meta.NormNum.IsInt.rpow_eq_inv_pow** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.
Meta.NormNum.IsInt`。
形式化陈述：∀ {b : ℝ} {n : ℕ}, Mathlib.Meta.NormNum.IsInt b (Int.negOfNat n) → ∀ (a : 
ℝ), a ^ b = (a ^ n)⁻¹
参数：Int.negOfNat n；a : ℝ；a ^ n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Mathlib.Meta.NormNum.IsInt.out`：∀ {α : Type u} [inst : Ring α] {a : α} {
n : ℤ}, Mathlib.Meta.NormNum.IsInt a n → a = ↑n
· 使用定理 `Real.rpow_intCast`：rpow_intCast (x : Real) (n : Int) : x ^ (n : Real) = 
x ^ n
· 使用定理 `Int.negOfNat_eq`：∀ {n : ℕ}, Int.negOfNat n = -Int.ofNat n
· 使用定理 `zpow_neg`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℤ), a 
^ (-n) = (a ^ n)⁻¹
· 使用定理 `Int.ofNat_eq_natCast`：∀ (n : ℕ), Int.ofNat n = ↑n
· 使用定理 `zpow_natCast`：zpow_natCast (a : G) : forall n : Nat, a ^ (n : Int) = a ^
 n | 0 => (zpow_zero _).trans (pow_zero _).symm | n + 1 => calc a ^ (↑(n + 1) : 
In…
-/
theorem IsInt.rpow_eq_inv_pow {b : ℝ} {n : ℕ} (h : IsInt b (.negOfNat n)) (a : ℝ) :
    a ^ b = (a ^ n)⁻¹ := by
  rw [h.1, Real.rpow_intCast, Int.negOfNat_eq, zpow_neg, Int.ofNat_eq_natCast, zpow_natCast]

/-- Given proofs
- that `a` is a natural number `m`
- that `b` is a nonnegative rational number `n / d`
- that `r ^ d = m ^ n` (written as `r ^ d = k`, `m ^ n = l`, `k = l`)

prove that `a ^ b = r`.
-/
/-
**Mathlib.Meta.NormNum.IsNat.rpow_isNNRat** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Met
a.NormNum.IsNat`。
形式化陈述：∀ {a b : ℝ} {m n d r : ℕ},   Mathlib.Meta.NormNum.IsNat a m →     Mathlib.
Meta.NormNum.IsNNRat b n d →       ∀ (k : ℕ), r ^ d = k → ∀ (l : ℕ), m ^ n = l →
 k = l → Mathlib.Meta.NormNum.IsNat (a ^ b) r
参数：k : ℕ；l : ℕ；a ^ b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Mathlib.Meta.NormNum.IsNNRat.den_nz`：∀ {α : Type u_1} [inst : DivisionSe
miring α] {a : α} {n d : ℕ}, Mathlib.Meta.NormNum.IsNNRat a n d → ↑d ≠ 0
· 使用定理 `Mathlib.Meta.NormNum.IsNNRat.to_eq`：∀ {α : Type u_1} [inst : DivisionSem
iring α] {n d : ℕ} {a n' d' : α},   Mathlib.Meta.NormNum.IsNNRat a n d → ↑n = n'
 → ↑d = d' → a = n' / d'
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用引理 `Real.rpow_natCast_mul`：rpow_natCast_mul (hx : 0 <= x) (n : Nat) (z : Rea
l) : x ^ (n * z) = (x ^ n) ^ z
· 使用定理 `Nat.cast_nonneg'`：cast_nonneg' (n : Nat) : 0 <= (n : α)
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Nat.cast_pow`：∀ {α : Type u_1} [inst : Semiring α] (m n : ℕ), ↑(m ^ n) =
 ↑m ^ n
· 使用定理 `Real.pow_rpow_inv_natCast`：pow_rpow_inv_natCast (hx : 0 <= x) (hn : n !=
 0) : (x ^ n) ^ (n⁻¹ : Real) = x
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `lt_of_le_of_ne'`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, b ≤
 a → a ≠ b → b < a
· 使用定理 `zero_le`：∀ {α : Type u_1} [inst : LE α] [inst_1 : Zero α] [IsBotZeroClas
s α] {a : α}, 0 ≤ a
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α

--- 原说明 ---
Given proofs
- that `a` is a natural number `m`
- that `b` is a nonnegative rational number `n / d`
- that `r ^ d = m ^ n` (written as `r ^ d = k`, `m ^ n = l`, `k = l`)

prove that `a ^ b = r`.
-/
theorem IsNat.rpow_isNNRat {a b : ℝ} {m n d r : ℕ} (ha : IsNat a m) (hb : IsNNRat b n d)
    (k : ℕ) (hr : r ^ d = k) (l : ℕ) (hm : m ^ n = l) (hkl : k = l) : IsNat (a ^ b) r := by
  rcases ha with ⟨rfl⟩
  constructor
  have : d ≠ 0 := mod_cast hb.den_nz
  rw [hb.to_eq rfl rfl, div_eq_mul_inv, Real.rpow_natCast_mul, ← Nat.cast_pow, hm, ← hkl, ← hr,
    Nat.cast_pow, Real.pow_rpow_inv_natCast] <;> positivity
/-
**Mathlib.Meta.NormNum.IsNNRat.rpow_isNNRat** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.M
eta.NormNum.IsNNRat`。
形式化陈述：∀ (a b : ℝ) (na da : ℕ),   Mathlib.Meta.NormNum.IsNNRat a na da →     ∀ (n
r dr : ℕ),       Mathlib.Meta.NormNum.IsNat (↑na ^ b) nr →         Mathlib.Meta.
NormNum.IsNat (↑da ^ b) dr → Mathlib.Meta.NormNum.IsNNRat (a ^ b) nr dr
参数：a b : ℝ；na da : ℕ；nr dr : ℕ；↑na ^ b；↑da ^ b；a ^ b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Meta.NormNum.IsNNRat.of_raw`：∀ (α : Type u_1) [inst : DivisionSe
miring α] (n d : ℕ), ↑d ≠ 0 → Mathlib.Meta.NormNum.IsNNRat (NNRat.rawCast n d) n
 d
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Meta.NormNum.IsNat.out`：∀ {α : Type u} [inst : AddMonoidWithOne 
α] {a : α} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = ↑n
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Real.rpow_pos_of_pos`：rpow_pos_of_pos {x : Real} (hx : 0 < x) (y : Real)
 : 0 < x ^ y
· 使用定理 `lt_of_le_of_ne'`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, b ≤
 a → a ≠ b → b < a
· 使用定理 `Nat.cast_nonneg`：cast_nonneg {α} [Semiring α] [PartialOrder α] [IsOrdere
dRing α] (n : Nat) : 0 <= (n : α)
· 使用定理 `Mathlib.Meta.NormNum.IsNNRat.den_nz`：∀ {α : Type u_1} [inst : DivisionSe
miring α] {a : α} {n d : ℕ}, Mathlib.Meta.NormNum.IsNNRat a n d → ↑d ≠ 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Mathlib.Meta.NormNum.IsNNRat.to_eq`：∀ {α : Type u_1} [inst : DivisionSem
iring α] {n d : ℕ} {a n' d' : α},   Mathlib.Meta.NormNum.IsNNRat a n d → ↑n = n'
 → ↑d = d' → a = n' / d'
· 使用定理 `Real.div_rpow`：div_rpow (hx : 0 <= x) (hy : 0 <= y) (z : Real) : (x / y)
 ^ z = x ^ z / y ^ z
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
-/
theorem IsNNRat.rpow_isNNRat (a b : ℝ) (na da : ℕ) (ha : IsNNRat a na da)
    (nr dr : ℕ) (hnum : IsNat ((na : ℝ) ^ b) nr) (hden : IsNat ((da : ℝ) ^ b) dr) :
    IsNNRat (a ^ b) nr dr := by
  suffices IsNNRat (nr / dr : ℝ) nr dr by
    simpa [ha.to_eq, Real.div_rpow, hnum.1, hden.1]
  apply IsNNRat.of_raw
  rw [← hden.1]
  apply (Real.rpow_pos_of_pos _ _).ne'
  exact lt_of_le_of_ne' da.cast_nonneg ha.den_nz
/-
**Mathlib.Meta.NormNum.rpow_isRat_eq_inv_rpow** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib
.Meta.NormNum`。
形式化陈述：rpow_isRat_eq_inv_rpow (a b : Real) (n d : Nat) (hb : IsRat b (Int.negOfNa
t n) d) : a ^ b = (a⁻¹) ^ (n / d : Real)
参数：a b : Real；n d : Nat；hb : IsRat b (Int.negOfNat n) d。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.rpow_neg_eq_inv_rpow`：rpow_neg_eq_inv_rpow (x y : Real) : x ^ (-y) 
= x⁻¹ ^ y
· 使用定理 `Mathlib.Meta.NormNum.IsRat.neg_to_eq`：∀ {α : Type u_1} [inst : DivisionR
ing α] {n d : ℕ} {a n' d' : α},   Mathlib.Meta.NormNum.IsRat a (Int.negOfNat n) 
d → ↑n = n' → ↑d = d' → a …
-/
theorem rpow_isRat_eq_inv_rpow (a b : ℝ) (n d : ℕ) (hb : IsRat b (Int.negOfNat n) d) :
    a ^ b = (a⁻¹) ^ (n / d : ℝ) := by
  rw [← Real.rpow_neg_eq_inv_rpow, hb.neg_to_eq rfl rfl]

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
    (a : Q(ℝ)) (na : Q(ℕ)) (pa : Q(IsNat $a $na))
    (b : Q(ℝ)) (nb db : Q(ℕ)) (pb : Q(IsNNRat $b $nb $db)) :
    MetaM (ℕ × Σ r : Q(ℕ), Q(IsNat ($a ^ $b) $r)) := do
  let r := (Nat.nthRoot db.natLit! na.natLit!) ^ nb.natLit!
  have er : Q(ℕ) := mkRawNatLit r
  -- avoid evaluating powers in kernel
  let .some ⟨c, pc⟩ ← liftM <| OptionT.run <| evalNatPow er db | failure
  let .some ⟨d, pd⟩ ← liftM <| OptionT.run <| evalNatPow na nb | failure
  guard (c.natLit! = d.natLit!)
  have hcd : Q($c = $d) := (q(Eq.refl $c) : Expr)
  return (r, ⟨er, q(IsNat.rpow_isNNRat $pa $pb $c $pc $d $pd $hcd)⟩)

/-- Evaluates expressions of the form `a ^ b` when `a` and `b` are both reals.
Works if `a`, `b`, and `a ^ b` are in fact rational numbers,
except for the case `a < 0`, `b` isn't integer.

TODO: simplify terms like  `(-a : ℝ) ^ (b / 3 : ℝ)` and `(-a : ℝ) ^ (b / 2 : ℝ)` too,
possibly after first considering changing the junk value. -/
@[norm_num (_ : ℝ) ^ (_ : ℝ)]
meta def evalRPow : NormNumExt where eval {u αR} e := do
  match u, αR, e with
  | 0, ~q(ℝ), ~q(($a : ℝ)^($b : ℝ)) =>
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
      let r ← derive q(($a⁻¹) ^ ($nb / $db : ℝ))
      assumeInstancesCommute
      return .eqTrans q(rpow_isRat_eq_inv_rpow $a $b $nb $db $pb) r
    | _ => failure
  | _ => failure

end Mathlib.Meta.NormNum

end Tactics

