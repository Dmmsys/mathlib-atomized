/-
Copyright (c) 2025 Fabrizio Barroero. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Barroero, Kevin H. Wilson
-/
module

public import Mathlib.Analysis.Analytic.Polynomial
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Multiset
public import Mathlib.Analysis.Polynomial.Norm
public import Mathlib.Analysis.SpecialFunctions.Integrals.PosLogEqCircleAverage
public import Mathlib.Analysis.Convex.Integral
public import Mathlib.Analysis.Polynomial.Fourier

/-!
# Mahler measure of complex polynomials

In this file we define the Mahler measure of a polynomial over `ℂ[X]` and prove some basic
properties.

## Main definitions

- `Polynomial.logMahlerMeasure p`: the logarithmic Mahler measure of a polynomial `p` defined as
  `(2 * π)⁻¹ * ∫ x ∈ (0, 2 * π), log ‖p (e ^ (i * x))‖`.
- `Polynomial.mahlerMeasure p`: the (exponential) Mahler measure of a polynomial `p`, which is equal
  to `e ^ p.logMahlerMeasure` if `p` is nonzero, and `0` otherwise.
- `Polynomial.mapMahlerMeasure p v`: the (exponential) Mahler measure of a polynomial `p` over a
  ring `A` whose coefficients are mapped to `ℂ` via `v : A →+* ℂ`

## Main results

- `Polynomial.mahlerMeasure_mul`: the Mahler measure of the product of two polynomials is the
  product of their Mahler measures.
- `mahlerMeasure_eq_leadingCoeff_mul_prod_roots`: the Mahler measure of a polynomial is the absolute
  value of its leading coefficient times the product of the absolute values of its roots lying
  outside the unit disk.
- `mahlerMeasure_le_sqrt_sum_sq_norm_coeff`: **Landau's inequality** — the Mahler measure is
  at most the ℓ² norm of the coefficient vector.
- `norm_coeff_le_choose_mul_mahlerMeasure_of_one_le_mahlerMeasure`: **Mignotte's coefficient
  bound** — if `f = g * h` with `M(h) ≥ 1`, then `‖g.coeff n‖ ≤ C(deg g, n) · M(f)`.
-/

@[expose] public section

namespace Polynomial

open Real

variable (p : ℂ[X])

/-- The logarithmic Mahler measure of a polynomial `p` defined as
`(2 * π)⁻¹ * ∫ x ∈ (0, 2 * π), log ‖p (e ^ (i * x))‖` -/
/-
**Polynomial.logMahlerMeasure** 是 Mathlib 中的一个定义，位于命名空间 `Polynomial`。
形式化陈述：logMahlerMeasure : Real
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The logarithmic Mahler measure of a polynomial `p` defined as
`(2 * π)⁻¹ * ∫ x ∈ (0, 2 * π), log ‖p (e ^ (i * x))‖`
-/
noncomputable def logMahlerMeasure : ℝ := circleAverage (fun x ↦ log ‖eval x p‖) 0 1
/-
**Polynomial.logMahlerMeasure_def** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：logMahlerMeasure_def : p.logMahlerMeasure = circleAverage (fun x => log ‖e
val x p‖) 0 1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem logMahlerMeasure_def : p.logMahlerMeasure = circleAverage (fun x ↦ log ‖eval x p‖) 0 1 :=
  rfl

@[simp]
/-
**Polynomial.logMahlerMeasure_zero** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：logMahlerMeasure_zero : (0 : Complex[X]).logMahlerMeasure = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Polynomial.eval_zero`：eval_zero : (0 : R[X]).eval x = 0
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `Real.log_zero`：log_zero : log 0 = 0
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `mul_inv_rev`：mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹
· 使用定理 `intervalIntegral.integral_zero`：integral_zero : (∫ _ in a..b, (0 : E) ∂μ
) = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem logMahlerMeasure_zero : (0 : ℂ[X]).logMahlerMeasure = 0 := by
  simp [logMahlerMeasure_def, circleAverage_def]

@[simp]
/-
**Polynomial.logMahlerMeasure_one** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：logMahlerMeasure_one : (1 : Complex[X]).logMahlerMeasure = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Polynomial.eval_one`：eval_one : (1 : R[X]).eval x = 1
· 使用定理 `NormOneClass.norm_one`：∀ {α : Type u_5} {inst : Norm α} {inst_1 : One α}
 [self : NormOneClass α], ‖1‖ = 1
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `Real.log_one`：log_one : log 1 = 0
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `mul_inv_rev`：mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹
· 使用定理 `intervalIntegral.integral_zero`：integral_zero : (∫ _ in a..b, (0 : E) ∂μ
) = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem logMahlerMeasure_one : (1 : ℂ[X]).logMahlerMeasure = 0 := by
  simp [logMahlerMeasure_def, circleAverage_def]

@[simp]
/-
**Polynomial.logMahlerMeasure_const** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：logMahlerMeasure_const (z : Complex) : (C z).logMahlerMeasure = log ‖z‖
参数：z : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Polynomial.eval_C`：eval_C : (C a).eval x = a
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `mul_inv_rev`：mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹
· 使用定理 `intervalIntegral.integral_const`：integral_const [CompleteSpace E] (c : E
) : ∫ _ in a..b, c = (b - a) • c
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `inv_mul_cancel_left₀`：inv_mul_cancel_left₀ (h : a != 0) (b : G₀) : a⁻¹ *
 (a * b) = b
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem logMahlerMeasure_const (z : ℂ) : (C z).logMahlerMeasure = log ‖z‖ := by
  simp [logMahlerMeasure_def, circleAverage_def, mul_assoc]

@[simp]
/-
**Polynomial.logMahlerMeasure_X** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：logMahlerMeasure_X : (X : Complex[X]).logMahlerMeasure = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Polynomial.eval_X`：eval_X : X.eval x = x
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `mul_inv_rev`：mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹
· 使用定理 `norm_circleMap_zero`：norm_circleMap_zero (R : Real) (θ : Real) : ‖circle
Map 0 R θ‖ = |R|
· 使用定理 `abs_one`：∀ {α : Type u_1} [inst : Ring α] [inst_1 : LinearOrder α] [IsOr
deredRing α], |1| = 1
· 使用定理 `Real.log_one`：log_one : log 1 = 0
· 使用定理 `intervalIntegral.integral_zero`：integral_zero : (∫ _ in a..b, (0 : E) ∂μ
) = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem logMahlerMeasure_X : (X : ℂ[X]).logMahlerMeasure = 0 := by
  simp [logMahlerMeasure_def, circleAverage_def]

@[simp]
/-
**Polynomial.logMahlerMeasure_monomial** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：logMahlerMeasure_monomial (n : Nat) (z : Complex) : (monomial n z).logMahl
erMeasure = log ‖z‖
参数：n : Nat；z : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Polynomial.eval_monomial`：eval_monomial {n a} : (monomial n a).eval x = 
a * x ^ n
· 使用定理 `Complex.norm_mul`：∀ (z w : ℂ), ‖z * w‖ = ‖z‖ * ‖w‖
· 使用定理 `norm_pow`：norm_pow (a : α) : forall n : Nat, ‖a ^ n‖ = ‖a‖ ^ n
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `mul_inv_rev`：mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹
· 使用定理 `norm_circleMap_zero`：norm_circleMap_zero (R : Real) (θ : Real) : ‖circle
Map 0 R θ‖ = |R|
· 使用定理 `abs_one`：∀ {α : Type u_1} [inst : Ring α] [inst_1 : LinearOrder α] [IsOr
deredRing α], |1| = 1
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `intervalIntegral.integral_const`：integral_const [CompleteSpace E] (c : E
) : ∫ _ in a..b, c = (b - a) • c
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `inv_mul_cancel_left₀`：inv_mul_cancel_left₀ (h : a != 0) (b : G₀) : a⁻¹ *
 (a * b) = b
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem logMahlerMeasure_monomial (n : ℕ) (z : ℂ) : (monomial n z).logMahlerMeasure = log ‖z‖ := by
  simp [logMahlerMeasure_def, circleAverage_def, mul_assoc]

/-- The Mahler measure of a polynomial `p` defined as `e ^ (logMahlerMeasure p)` if `p` is nonzero
and `0` otherwise -/
/-
**Polynomial.mahlerMeasure** 是 Mathlib 中的一个定义，位于命名空间 `Polynomial`。
形式化陈述：mahlerMeasure : Real
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Mahler measure of a polynomial `p` defined as `e ^ (logMahlerMeasure p)` if 
`p` is nonzero
and `0` otherwise
-/
noncomputable def mahlerMeasure : ℝ := if p ≠ 0 then exp (p.logMahlerMeasure) else 0

variable {p} in
/-
**Polynomial.mahlerMeasure_def_of_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`
。
形式化陈述：mahlerMeasure_def_of_ne_zero (hp : p != 0) : p.mahlerMeasure = exp ((2 * π
)⁻¹ * ∫ (x : Real) in (0)..(2 * π), log ‖eval (circleMap 0 1 x) p‖)
参数：hp : p != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mul_inv_rev`：mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mahlerMeasure_def_of_ne_zero (hp : p ≠ 0) : p.mahlerMeasure =
    exp ((2 * π)⁻¹ * ∫ (x : ℝ) in (0)..(2 * π), log ‖eval (circleMap 0 1 x) p‖) := by
  simp [mahlerMeasure, hp, logMahlerMeasure_def, circleAverage_def]

variable {p} in
/-
**Polynomial.logMahlerMeasure_eq_log_MahlerMeasure** 是 Mathlib 中的一个定理，位于命名空间 `Po
lynomial`。
形式化陈述：logMahlerMeasure_eq_log_MahlerMeasure : p.logMahlerMeasure = log p.mahlerM
easure
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.mahlerMeasure.eq_1`：∀ (p : Polynomial ℂ), p.mahlerMeasure = i
f p ≠ 0 then Real.exp p.logMahlerMeasure else 0
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mul_inv_rev`：mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹
· 使用定理 `Real.log_exp`：log_exp (x : Real) : log (exp x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Polynomial.eval_zero`：eval_zero : (0 : R[X]).eval x = 0
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `Real.log_zero`：log_zero : log 0 = 0
· 使用定理 `intervalIntegral.integral_zero`：integral_zero : (∫ _ in a..b, (0 : E) ∂μ
) = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
-/
theorem logMahlerMeasure_eq_log_MahlerMeasure : p.logMahlerMeasure = log p.mahlerMeasure := by
  rw [mahlerMeasure]
  split_ifs <;> simp_all [logMahlerMeasure_def, circleAverage_def]

@[simp]
/-
**Polynomial.mahlerMeasure_zero** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：mahlerMeasure_zero : (0 : Complex[X]).mahlerMeasure = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
-/
theorem mahlerMeasure_zero : (0 : ℂ[X]).mahlerMeasure = 0 := by simp [mahlerMeasure]

@[simp]
/-
**Polynomial.mahlerMeasure_one** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：mahlerMeasure_one : (1 : Complex[X]).mahlerMeasure = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Polynomial.logMahlerMeasure_one`：logMahlerMeasure_one : (1 : Complex[X])
.logMahlerMeasure = 0
· 使用定理 `Real.exp_zero`：exp_zero : exp 0 = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mahlerMeasure_one : (1 : ℂ[X]).mahlerMeasure = 1 := by simp [mahlerMeasure]

@[simp]
/-
**Polynomial.mahlerMeasure_const** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：mahlerMeasure_const (z : Complex) : (C z).mahlerMeasure = ‖z‖
参数：z : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `Complex.instNontrivial`：Nontrivial ℂ
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `Polynomial.logMahlerMeasure_const`：logMahlerMeasure_const (z : Complex) 
: (C z).logMahlerMeasure = log ‖z‖
· 使用定理 `ite_not`：∀ {α : Sort u_1} (p : Prop) [inst : Decidable p] (x y : α), (if
 ¬p then x else y) = if p then y else x
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Real.exp_log`：exp_log (hx : 0 < x) : exp (log x) = x
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem mahlerMeasure_const (z : ℂ) : (C z).mahlerMeasure = ‖z‖ := by
  simp only [mahlerMeasure, ne_eq, map_eq_zero, logMahlerMeasure_const, ite_not]
  split_ifs with h
  · simp [h]
  · simp [h, exp_log]
/-
**Polynomial.mahlerMeasure_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：mahlerMeasure_nonneg : 0 <= p.mahlerMeasure
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.mahlerMeasure_zero`：mahlerMeasure_zero : (0 : Complex[X]).mah
lerMeasure = 0
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Polynomial.mahlerMeasure_def_of_ne_zero`：mahlerMeasure_def_of_ne_zero (h
p : p != 0) : p.mahlerMeasure = exp ((2 * π)⁻¹ * ∫ (x : Real) in (0)..(2 * π), l
og ‖eval (circleMap 0 1 x) p‖…
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mul_inv_rev`：mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹
-/
theorem mahlerMeasure_nonneg : 0 ≤ p.mahlerMeasure := by
  by_cases hp : p = 0 <;> simp [hp, mahlerMeasure_def_of_ne_zero, exp_nonneg]

variable {p} in
/-
**Polynomial.mahlerMeasure_pos_of_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`
。
形式化陈述：mahlerMeasure_pos_of_ne_zero (hp : p != 0) : 0 < p.mahlerMeasure
参数：hp : p != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mahlerMeasure_pos_of_ne_zero (hp : p ≠ 0) : 0 < p.mahlerMeasure := by
  grind [exp_pos, mahlerMeasure_def_of_ne_zero]

@[simp]
/-
**Polynomial.mahlerMeasure_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：mahlerMeasure_eq_zero_iff : p.mahlerMeasure = 0 ↔ p = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.mahlerMeasure_def_of_ne_zero`：mahlerMeasure_def_of_ne_zero (h
p : p != 0) : p.mahlerMeasure = exp ((2 * π)⁻¹ * ∫ (x : Real) in (0)..(2 * π), l
og ‖eval (circleMap 0 1 x) p‖…
· 使用定理 `mul_inv_rev`：mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `Polynomial.mahlerMeasure_zero`：mahlerMeasure_zero : (0 : Complex[X]).mah
lerMeasure = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem mahlerMeasure_eq_zero_iff : p.mahlerMeasure = 0 ↔ p = 0 := by
  refine ⟨?_, by simp_all [mahlerMeasure_zero]⟩
  contrapose
  exact fun h ↦ by simp [mahlerMeasure_def_of_ne_zero h]
/-
**Polynomial.intervalIntegrable_mahlerMeasure** 是 Mathlib 中的一个引理，位于命名空间 `Polynom
ial`。
形式化陈述：intervalIntegrable_mahlerMeasure : IntervalIntegrable (fun x => log ‖p.eva
l (circleMap 0 1 x)‖) MeasureTheory.volume 0 (2 * π)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `circleIntegrable_def`：circleIntegrable_def (f : Complex -> E) (c : Compl
ex) (R : Real) : CircleIntegrable f c R ↔ IntervalIntegrable (fun θ : Real => f 
(circleMap…
· 使用定理 `MeromorphicOn.circleIntegrable_log_norm`：MeromorphicOn.circleIntegrable_
log_norm (hf : MeromorphicOn f (sphere c |R|)) : CircleIntegrable (log ‖f ·‖) c 
R
· 使用引理 `AnalyticOnNhd.meromorphicOn`：AnalyticOnNhd.meromorphicOn {f : 𝕜 -> E} {U
 : Set 𝕜} (hf : AnalyticOnNhd 𝕜 f U) : MeromorphicOn f U
· 使用定理 `AnalyticOnNhd.aeval_polynomial`：AnalyticOnNhd.aeval_polynomial (hf : Ana
lyticOnNhd 𝕜 f s) (p : A[X]) : AnalyticOnNhd 𝕜 (fun x => aeval (f x) p) s
· 使用定理 `analyticOnNhd_id`：analyticOnNhd_id : AnalyticOnNhd 𝕜 (fun x : E => x) s
-/
lemma intervalIntegrable_mahlerMeasure :
    IntervalIntegrable (fun x ↦ log ‖p.eval (circleMap 0 1 x)‖) MeasureTheory.volume 0 (2 * π) := by
  rw [← circleIntegrable_def fun z ↦ log ‖p.eval z‖]
  exact (analyticOnNhd_id.aeval_polynomial p).meromorphicOn.circleIntegrable_log_norm

/-! The Mahler measure of the product of two polynomials is the product of their Mahler measures -/
open intervalIntegral in
/-
**Polynomial.mahlerMeasure_mul** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：mahlerMeasure_mul (p q : Complex[X]) : (p * q).mahlerMeasure = p.mahlerMea
sure * q.mahlerMeasure
参数：p q : Complex[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.mahlerMeasure_zero`：mahlerMeasure_zero : (0 : Complex[X]).mah
lerMeasure = 0
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mul_eq_zero`：mul_eq_zero : a * b = 0 ↔ a = 0 ∨ b = 0
· 使用定理 `Polynomial.instNoZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [NoZer
oDivisors R], NoZeroDivisors (Polynomial R)
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_or`：∀ {p q : Prop}, ¬(p ∨ q) ↔ ¬p ∧ ¬q
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Polynomial.eval_mul`：eval_mul : (p * q).eval x = p.eval x * q.eval x
· 使用定理 `Complex.norm_mul`：∀ (z w : ℂ), ‖z * w‖ = ‖z‖ * ‖w‖
· 使用定理 `mul_inv_rev`：mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.exp_add`：∀ (x y : ℝ), Real.exp (x + y) = Real.exp x * Real.exp y
· 使用定理 `left_distrib`：left_distrib [Mul R] [Add R] [LeftDistribClass R] (a b c :
 R) : a * (b + c) = a * b + a * c
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `intervalIntegral.integral_add`：∀ {E : Type u_5} [inst : NormedAddCommGro
up E] [inst_1 : NormedSpace ℝ E] {a b : ℝ} {f g : ℝ → E}   {μ : MeasureTheory.Me
asure ℝ},   Interva…
· 使用引理 `Polynomial.intervalIntegrable_mahlerMeasure`：intervalIntegrable_mahlerMe
asure : IntervalIntegrable (fun x => log ‖p.eval (circleMap 0 1 x)‖) MeasureTheo
ry.volume 0 (2 * π)
· 使用定理 `intervalIntegral.integral_congr_ae`：integral_congr_ae (h : forallᵐ x ∂μ,
 x in Ι a b -> f x = g x) : ∫ x in a..b, f x ∂μ = ∫ x in a..b, g x ∂μ
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.ae_iff`：ae_iff {p : α -> Prop} : (forallᵐ a ∂μ, p a) ↔ μ {
 a | ¬p a } = 0
· 使用定理 `Set.Finite.measure_zero`：∀ {α : Type u_1} {m0 : MeasurableSpace α} {s : 
Set α},   s.Finite → ∀ (μ : MeasureTheory.Measure α) [MeasureTheory.NullSingleto
nClass μ], μ …
（共 52 条，此处仅展示前 30 条）
-/
theorem mahlerMeasure_mul (p q : ℂ[X]) :
    (p * q).mahlerMeasure = p.mahlerMeasure * q.mahlerMeasure := by
  by_cases hpq : p * q = 0
  · simpa [hpq, mahlerMeasure_zero] using mul_eq_zero.mp hpq
  rw [mul_eq_zero, not_or] at hpq
  simp only [mahlerMeasure, ne_eq, mul_eq_zero, hpq, or_self, not_false_eq_true, ↓reduceIte,
    logMahlerMeasure, eval_mul, Complex.norm_mul, circleAverage_def, mul_inv_rev, smul_eq_mul]
  rw [← exp_add, ← left_distrib]
  congr
  rw [← integral_add p.intervalIntegrable_mahlerMeasure q.intervalIntegrable_mahlerMeasure]
  apply integral_congr_ae
  rw [MeasureTheory.ae_iff]
  apply Set.Finite.measure_zero _ MeasureTheory.volume
  simp only [Classical.not_imp]
  apply Set.Finite.of_finite_image (f := circleMap 0 1) _ <|
    (injOn_circleMap_of_abs_sub_le one_ne_zero (by simp [le_of_eq, pi_nonneg])).mono (fun _ h ↦ h.1)
  apply (p * q).roots.finite_toSet.subset
  rintro _ ⟨_, ⟨_, h⟩, _⟩
  contrapose h
  simp_all [log_mul]

@[simp]
/-
**Polynomial.prod_mahlerMeasure_eq_mahlerMeasure_prod** 是 Mathlib 中的一个定理，位于命名空间 
`Polynomial`。
形式化陈述：prod_mahlerMeasure_eq_mahlerMeasure_prod (s : Multiset Complex[X]) : (s.pr
od).mahlerMeasure = (s.map (fun p => p.mahlerMeasure)).prod
参数：s : Multiset Complex[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.induction_on`：∀ {α : Type u_1} {p : Multiset α → Prop} (s : Mul
tiset α), p 0 → (∀ (a : α) (s : Multiset α), p s → p (a ::ₘ s)) → p s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.mahlerMeasure_one`：mahlerMeasure_one : (1 : Complex[X]).mahle
rMeasure = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Multiset.prod_cons`：prod_cons (a : M) (s) : prod (a ::ₘ s) = a * prod s
· 使用定理 `Polynomial.mahlerMeasure_mul`：mahlerMeasure_mul (p q : Complex[X]) : (p 
* q).mahlerMeasure = p.mahlerMeasure * q.mahlerMeasure
· 使用定理 `Multiset.map_cons`：map_cons (f : α -> β) (a s) : map f (a ::ₘ s) = f a :
:ₘ map f s
-/
theorem prod_mahlerMeasure_eq_mahlerMeasure_prod (s : Multiset ℂ[X]) :
    (s.prod).mahlerMeasure = (s.map (fun p ↦ p.mahlerMeasure)).prod := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons _ _ ih => simp [mahlerMeasure_mul, ih]
/-
**Polynomial.logMahlerMeasure_mul_eq_add_logMahlerMeasure** 是 Mathlib 中的一个定理，位于命
名空间 `Polynomial`。
形式化陈述：logMahlerMeasure_mul_eq_add_logMahlerMeasure {p q : Complex[X]} (hpq : p *
 q != 0) : (p * q).logMahlerMeasure = p.logMahlerMeasure + q.logMahlerMeasure
参数：hpq : p * q != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.logMahlerMeasure_eq_log_MahlerMeasure`：logMahlerMeasure_eq_lo
g_MahlerMeasure : p.logMahlerMeasure = log p.mahlerMeasure
· 使用定理 `Polynomial.mahlerMeasure_mul`：mahlerMeasure_mul (p q : Complex[X]) : (p 
* q).mahlerMeasure = p.mahlerMeasure * q.mahlerMeasure
· 使用定理 `Real.log_mul`：log_mul (hx : x != 0) (hy : y != 0) : log (x * y) = log x 
+ log y
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Polynomial.instNoZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [NoZer
oDivisors R], NoZeroDivisors (Polynomial R)
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem logMahlerMeasure_mul_eq_add_logMahlerMeasure {p q : ℂ[X]} (hpq : p * q ≠ 0) :
    (p * q).logMahlerMeasure = p.logMahlerMeasure + q.logMahlerMeasure := by
  simp_all [logMahlerMeasure_eq_log_MahlerMeasure, mahlerMeasure_mul, log_mul]
/-
**Polynomial.logMahlerMeasure_C_mul** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：logMahlerMeasure_C_mul {a : Complex} (ha : a != 0) {p : Complex[X]} (hp : 
p != 0) : (C a * p).logMahlerMeasure = log ‖a‖ + p.logMahlerMeasure
参数：ha : a != 0；hp : p != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.logMahlerMeasure_mul_eq_add_logMahlerMeasure`：logMahlerMeasur
e_mul_eq_add_logMahlerMeasure {p q : Complex[X]} (hpq : p * q != 0) : (p * q).lo
gMahlerMeasure = p.logMahlerMeasure + q.logMa…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Polynomial.instNoZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [NoZer
oDivisors R], NoZeroDivisors (Polynomial R)
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Complex.instNontrivial`：Nontrivial ℂ
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Polynomial.logMahlerMeasure_const`：logMahlerMeasure_const (z : Complex) 
: (C z).logMahlerMeasure = log ‖z‖
-/
theorem logMahlerMeasure_C_mul {a : ℂ} (ha : a ≠ 0) {p : ℂ[X]} (hp : p ≠ 0) :
    (C a * p).logMahlerMeasure = log ‖a‖ + p.logMahlerMeasure := by
  rw [logMahlerMeasure_mul_eq_add_logMahlerMeasure (by simp [ha, hp]), logMahlerMeasure_const]

open MeromorphicOn Metric in
/-- The logarithmic Mahler measure of `X - C z` is the `log⁺` of the absolute value of `z`. -/
@[simp]
/-
**Polynomial.logMahlerMeasure_X_sub_C** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：logMahlerMeasure_X_sub_C (z : Complex) : (X - C z).logMahlerMeasure = log⁺
 ‖z‖
参数：z : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Polynomial.eval_sub`：eval_sub (p q : R[X]) (x : R) : (p - q).eval x = p.
eval x - q.eval x
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Polynomial.eval_X`：eval_X : X.eval x = x
· 使用定理 `Polynomial.eval_C`：eval_C : (C a).eval x = a
· 使用定理 `circleAverage_log_norm_sub_const_eq_posLog`：circleAverage_log_norm_sub_c
onst_eq_posLog : circleAverage (log ‖· - a‖) 0 1 = log⁺ ‖a‖
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The logarithmic Mahler measure of `X - C z` is the `log⁺` of the absolute value 
of `z`.
-/
theorem logMahlerMeasure_X_sub_C (z : ℂ) : (X - C z).logMahlerMeasure = log⁺ ‖z‖ := by
  simp [logMahlerMeasure_def]

@[simp]
/-
**Polynomial.logMahlerMeasure_X_add_C** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：logMahlerMeasure_X_add_C (z : Complex) : (X + C z).logMahlerMeasure = log⁺
 ‖z‖
参数：z : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `Polynomial.logMahlerMeasure_X_sub_C`：logMahlerMeasure_X_sub_C (z : Compl
ex) : (X - C z).logMahlerMeasure = log⁺ ‖z‖
· 使用定理 `norm_neg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), ‖-a‖ =
 ‖a‖
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem logMahlerMeasure_X_add_C (z : ℂ) : (X + C z).logMahlerMeasure = log⁺ ‖z‖ := by
  simp [← sub_neg_eq_add, ← map_neg]
/-
**Polynomial.logMahlerMeasure_C_mul_X_add_C** 是 Mathlib 中的一个定理，位于命名空间 `Polynomia
l`。
形式化陈述：logMahlerMeasure_C_mul_X_add_C {a : Complex} (ha : a != 0) (b : Complex) :
 (C a * X + C b).logMahlerMeasure = log ‖a‖ + log⁺ ‖a⁻¹ * b‖
参数：ha : a != 0；b : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `mul_inv_cancel_left₀`：mul_inv_cancel_left₀ (h : a != 0) (b : G₀) : a * (
a⁻¹ * b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Polynomial.logMahlerMeasure_C_mul`：logMahlerMeasure_C_mul {a : Complex} 
(ha : a != 0) {p : Complex[X]} (hp : p != 0) : (C a * p).logMahlerMeasure = log 
‖a‖ + p.logMahlerMeasur…
· 使用定理 `Polynomial.X_add_C_ne_zero`：X_add_C_ne_zero (r : R) : X + C r != 0
· 使用定理 `Complex.instNontrivial`：Nontrivial ℂ
· 使用定理 `Polynomial.logMahlerMeasure_X_add_C`：logMahlerMeasure_X_add_C (z : Compl
ex) : (X + C z).logMahlerMeasure = log⁺ ‖z‖
-/
theorem logMahlerMeasure_C_mul_X_add_C {a : ℂ} (ha : a ≠ 0) (b : ℂ) :
    (C a * X + C b).logMahlerMeasure = log ‖a‖ + log⁺ ‖a⁻¹ * b‖ := by
  rw [show C a * X + C b = C a * (X + C (a⁻¹ * b)) by simp [mul_add, ← map_mul, ha],
    logMahlerMeasure_C_mul ha (X_add_C_ne_zero (a⁻¹ * b)), logMahlerMeasure_X_add_C]
/-
**Polynomial.logMahlerMeasure_of_degree_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `Polyno
mial`。
形式化陈述：logMahlerMeasure_of_degree_eq_one {p : Complex[X]} (h : p.degree = 1) : p.
logMahlerMeasure = log ‖p.coeff 1‖ + log⁺ ‖(p.coeff 1)⁻¹ * p.coeff 0‖
参数：h : p.degree = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.eq_X_add_C_of_degree_le_one`：eq_X_add_C_of_degree_le_one (h :
 degree p <= 1) : p = C (p.coeff 1) * X + C (p.coeff 0)
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Polynomial.logMahlerMeasure_C_mul_X_add_C`：logMahlerMeasure_C_mul_X_add_
C {a : Complex} (ha : a != 0) (b : Complex) : (C a * X + C b).logMahlerMeasure =
 log ‖a‖ + log⁺ ‖a⁻¹ * b‖
· 使用定理 `Polynomial.coeff_ne_zero_of_eq_degree`：coeff_ne_zero_of_eq_degree (hn : 
degree p = n) : coeff p n != 0
· 使用定理 `Complex.norm_mul`：∀ (z w : ℂ), ‖z * w‖ = ‖z‖ * ‖w‖
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `norm_inv`：norm_inv (a : α) : ‖a⁻¹‖ = ‖a‖⁻¹
· 使用定理 `Polynomial.coeff_add`：coeff_add (p q : R[X]) (n : Nat) : coeff (p + q) n
 = coeff p n + coeff q n
· 使用定理 `Polynomial.coeff_mul_X`：coeff_mul_X (p : R[X]) (n : Nat) : coeff (p * X)
 (n + 1) = coeff p n
· 使用定理 `Polynomial.coeff_C_zero`：coeff_C_zero : coeff (C a) 0 = a
· 使用引理 `Polynomial.coeff_C_succ`：coeff_C_succ {r : R} {n : Nat} : coeff (C r) (n
 + 1) = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Polynomial.mul_coeff_zero`：mul_coeff_zero (p q : R[X]) : coeff (p * q) 0
 = coeff p 0 * coeff q 0
· 使用定理 `Polynomial.coeff_X_zero`：coeff_X_zero : coeff (X : R[X]) 0 = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem logMahlerMeasure_of_degree_eq_one {p : ℂ[X]} (h : p.degree = 1) : p.logMahlerMeasure =
    log ‖p.coeff 1‖ + log⁺ ‖(p.coeff 1)⁻¹ * p.coeff 0‖ := by
  rw [eq_X_add_C_of_degree_le_one (le_of_eq h)]
  simp [logMahlerMeasure_C_mul_X_add_C (show p.coeff 1 ≠ 0 by exact coeff_ne_zero_of_eq_degree h)]

/-- The Mahler measure of `X - C z` equals `max 1 ‖z‖`. -/
@[simp]
/-
**Polynomial.mahlerMeasure_X_sub_C** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：mahlerMeasure_X_sub_C (z : Complex) : (X - C z).mahlerMeasure = max 1 ‖z‖
参数：z : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.logMahlerMeasure_X_sub_C`：logMahlerMeasure_X_sub_C (z : Compl
ex) : (X - C z).logMahlerMeasure = log⁺ ‖z‖
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.exp_log`：exp_log (hx : 0 < x) : exp (log x) = x
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `le_max_left`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ max 
a b
· 使用定理 `Polynomial.mahlerMeasure_pos_of_ne_zero`：mahlerMeasure_pos_of_ne_zero (h
p : p != 0) : 0 < p.mahlerMeasure
· 使用定理 `Polynomial.X_sub_C_ne_zero`：X_sub_C_ne_zero (r : R) : X - C r != 0
· 使用定理 `Complex.instNontrivial`：Nontrivial ℂ
· 使用定理 `Real.posLog_eq_log_max_one`：posLog_eq_log_max_one (hx : 0 <= x) : log⁺ x
 = log (max 1 x)
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.logMahlerMeasure_eq_log_MahlerMeasure`：logMahlerMeasure_eq_lo
g_MahlerMeasure : p.logMahlerMeasure = log p.mahlerMeasure

--- 原说明 ---
The Mahler measure of `X - C z` equals `max 1 ‖z‖`.
-/
theorem mahlerMeasure_X_sub_C (z : ℂ) : (X - C z).mahlerMeasure = max 1 ‖z‖ := by
  have := logMahlerMeasure_X_sub_C z
  rw [logMahlerMeasure_eq_log_MahlerMeasure] at this
  apply_fun exp at this
  rwa [posLog_eq_log_max_one (norm_nonneg z),
    exp_log (mahlerMeasure_pos_of_ne_zero <| X_sub_C_ne_zero z),
    exp_log (lt_of_lt_of_le zero_lt_one <| le_max_left 1 ‖z‖)] at this

@[simp]
/-
**Polynomial.mahlerMeasure_X_add_C** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：mahlerMeasure_X_add_C (z : Complex) : (X + C z).mahlerMeasure = max 1 ‖z‖
参数：z : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `Polynomial.mahlerMeasure_X_sub_C`：mahlerMeasure_X_sub_C (z : Complex) : 
(X - C z).mahlerMeasure = max 1 ‖z‖
· 使用定理 `norm_neg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), ‖-a‖ =
 ‖a‖
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mahlerMeasure_X_add_C (z : ℂ) : (X + C z).mahlerMeasure = max 1 ‖z‖ := by
  simp [← sub_neg_eq_add, ← map_neg]

@[simp]
/-
**Polynomial.mahlerMeasure_C_mul_X_add_C** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：mahlerMeasure_C_mul_X_add_C {a : Complex} (ha : a != 0) (b : Complex) : (C
 a * X + C b).mahlerMeasure = max ‖a‖ ‖b‖
参数：ha : a != 0；b : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `mul_inv_cancel_left₀`：mul_inv_cancel_left₀ (h : a != 0) (b : G₀) : a * (
a⁻¹ * b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Polynomial.mahlerMeasure_mul`：mahlerMeasure_mul (p q : Complex[X]) : (p 
* q).mahlerMeasure = p.mahlerMeasure * q.mahlerMeasure
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Polynomial.mahlerMeasure_const`：mahlerMeasure_const (z : Complex) : (C z
).mahlerMeasure = ‖z‖
· 使用定理 `Polynomial.mahlerMeasure_X_add_C`：mahlerMeasure_X_add_C (z : Complex) : 
(X + C z).mahlerMeasure = max 1 ‖z‖
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `nnnorm_mul`：∀ {α : Type u_2} [inst : SeminormedAddCommGroup α] [inst_1 :
 Mul α] [NormMulClass α] (a b : α), ‖a * b‖₊ = ‖a‖₊ * ‖b‖₊
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `nnnorm_inv`：nnnorm_inv (a : α) : ‖a⁻¹‖₊ = ‖a‖₊⁻¹
· 使用引理 `mul_max`：mul_max [MulLeftMono α] (a b c : α) : a * max b c = max (a * b)
 (a * c)
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
theorem mahlerMeasure_C_mul_X_add_C {a : ℂ} (ha : a ≠ 0) (b : ℂ) :
    (C a * X + C b).mahlerMeasure = max ‖a‖ ‖b‖ := by
  simp only [show C a * X + C b = C a * (X + C (a⁻¹ * b)) by simp [mul_add, ← map_mul, ha],
    mahlerMeasure_mul, mahlerMeasure_const, ← coe_nnnorm, mahlerMeasure_X_add_C]
  norm_cast
  simp [mul_max, ha]
/-
**Polynomial.mahlerMeasure_of_degree_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `Polynomia
l`。
形式化陈述：mahlerMeasure_of_degree_eq_one {p : Complex[X]} (h : p.degree = 1) : p.mah
lerMeasure = max ‖p.coeff 1‖ ‖p.coeff 0‖
参数：h : p.degree = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.eq_X_add_C_of_degree_le_one`：eq_X_add_C_of_degree_le_one (h :
 degree p <= 1) : p = C (p.coeff 1) * X + C (p.coeff 0)
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Polynomial.mahlerMeasure_C_mul_X_add_C`：mahlerMeasure_C_mul_X_add_C {a :
 Complex} (ha : a != 0) (b : Complex) : (C a * X + C b).mahlerMeasure = max ‖a‖ 
‖b‖
· 使用定理 `Polynomial.coeff_ne_zero_of_eq_degree`：coeff_ne_zero_of_eq_degree (hn : 
degree p = n) : coeff p n != 0
· 使用定理 `Polynomial.coeff_add`：coeff_add (p q : R[X]) (n : Nat) : coeff (p + q) n
 = coeff p n + coeff q n
· 使用定理 `Polynomial.coeff_mul_X`：coeff_mul_X (p : R[X]) (n : Nat) : coeff (p * X)
 (n + 1) = coeff p n
· 使用定理 `Polynomial.coeff_C_zero`：coeff_C_zero : coeff (C a) 0 = a
· 使用引理 `Polynomial.coeff_C_succ`：coeff_C_succ {r : R} {n : Nat} : coeff (C r) (n
 + 1) = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Polynomial.mul_coeff_zero`：mul_coeff_zero (p q : R[X]) : coeff (p * q) 0
 = coeff p 0 * coeff q 0
· 使用定理 `Polynomial.coeff_X_zero`：coeff_X_zero : coeff (X : R[X]) 0 = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mahlerMeasure_of_degree_eq_one {p : ℂ[X]} (h : p.degree = 1) :
    p.mahlerMeasure = max ‖p.coeff 1‖ ‖p.coeff 0‖ := by
  rw [eq_X_add_C_of_degree_le_one (le_of_eq h)]
  simp [mahlerMeasure_C_mul_X_add_C (show p.coeff 1 ≠ 0 by exact coeff_ne_zero_of_eq_degree h)]

/-- The logarithmic Mahler measure of a polynomial is the `log` of the absolute value of its leading
  coefficient plus the sum of the `log`s of the absolute values of its roots lying outside the unit
  disk. -/
/-
**Polynomial.logMahlerMeasure_eq_log_leadingCoeff_add_sum_log_roots** 是 Mathlib 
中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：logMahlerMeasure_eq_log_leadingCoeff_add_sum_log_roots (p : Complex[X]) : 
p.logMahlerMeasure = log ‖p.leadingCoeff‖ + (p.roots.map (fun a => log⁺ ‖a‖)).su
m
参数：p : Complex[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.logMahlerMeasure_zero`：logMahlerMeasure_zero : (0 : Complex[X
]).logMahlerMeasure = 0
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `Real.log_zero`：log_zero : log 0 = 0
· 使用定理 `Multiset.map_congr`：map_congr {f g : α -> β} {s t : Multiset α} : s = t 
-> (forall x in t, f x = g x) -> map f s = map g t
· 使用定理 `Polynomial.roots.congr_simp`：∀ {R : Type u} [inst : CommRing R] [inst_1 
: IsDomain R] (p p_1 : Polynomial R), p = p_1 → p.roots = p_1.roots
· 使用定理 `Polynomial.roots_zero`：roots_zero : (0 : R[X]).roots = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Polynomial.Splits.eq_prod_roots`：∀ {R : Type u_1} [inst : CommRing R] {f
 : Polynomial R} [inst_1 : IsDomain R],   f.Splits → f = Polynomial.C f.leadingC
oeff * (Multiset.map …
· 使用定理 `IsAlgClosed.splits`：∀ {k : Type u} {inst : Field k} [self : IsAlgClosed 
k] (p : Polynomial k), p.Splits
· 使用定理 `Polynomial.logMahlerMeasure_mul_eq_add_logMahlerMeasure`：logMahlerMeasur
e_mul_eq_add_logMahlerMeasure {p q : Complex[X]} (hpq : p * q != 0) : (p * q).lo
gMahlerMeasure = p.logMahlerMeasure + q.logMa…
· 使用定理 `Polynomial.instNoZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [NoZer
oDivisors R], NoZeroDivisors (Polynomial R)
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `Complex.instNontrivial`：Nontrivial ℂ
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `Polynomial.logMahlerMeasure_eq_log_MahlerMeasure`：logMahlerMeasure_eq_lo
g_MahlerMeasure : p.logMahlerMeasure = log p.mahlerMeasure
· 使用定理 `Polynomial.mahlerMeasure_const`：mahlerMeasure_const (z : Complex) : (C z
).mahlerMeasure = ‖z‖
· 使用定理 `Polynomial.prod_mahlerMeasure_eq_mahlerMeasure_prod`：prod_mahlerMeasure_
eq_mahlerMeasure_prod (s : Multiset Complex[X]) : (s.prod).mahlerMeasure = (s.ma
p (fun p => p.mahlerMeasure)).prod
（共 34 条，此处仅展示前 30 条）

--- 原说明 ---
The logarithmic Mahler measure of a polynomial is the `log` of the absolute valu
e of its leading
  coefficient plus the sum of the `log`s of the absolute values of its roots lyi
ng outside the unit
  disk.
-/
theorem logMahlerMeasure_eq_log_leadingCoeff_add_sum_log_roots (p : ℂ[X]) : p.logMahlerMeasure =
    log ‖p.leadingCoeff‖ + (p.roots.map (fun a ↦ log⁺ ‖a‖)).sum := by
  by_cases hp : p = 0
  · simp [hp]
  have : ∀ x ∈ Multiset.map (fun x ↦ max 1 ‖x‖) p.roots, x ≠ 0 := by grind [Multiset.mem_map]
  nth_rw 1 [(IsAlgClosed.splits p).eq_prod_roots]
  rw [logMahlerMeasure_mul_eq_add_logMahlerMeasure (by simp [hp, X_sub_C_ne_zero])]
  simp [posLog_eq_log_max_one, logMahlerMeasure_eq_log_MahlerMeasure,
    prod_mahlerMeasure_eq_mahlerMeasure_prod, log_multiset_prod this]

/-- The Mahler measure of a polynomial is the absolute value of its leading coefficient times
  the product of the absolute values of its roots lying outside the unit disk. -/
/-
**Polynomial.mahlerMeasure_eq_leadingCoeff_mul_prod_roots** 是 Mathlib 中的一个定理，位于命
名空间 `Polynomial`。
形式化陈述：mahlerMeasure_eq_leadingCoeff_mul_prod_roots (p : Complex[X]) : p.mahlerMe
asure = ‖p.leadingCoeff‖ * (p.roots.map (fun a => max 1 ‖a‖)).prod
参数：p : Complex[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.mahlerMeasure_zero`：mahlerMeasure_zero : (0 : Complex[X]).mah
lerMeasure = 0
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `Multiset.map_congr`：map_congr {f g : α -> β} {s t : Multiset α} : s = t 
-> (forall x in t, f x = g x) -> map f s = map g t
· 使用定理 `Polynomial.roots.congr_simp`：∀ {R : Type u} [inst : CommRing R] [inst_1 
: IsDomain R] (p p_1 : Polynomial R), p = p_1 → p.roots = p_1.roots
· 使用定理 `Polynomial.roots_zero`：roots_zero : (0 : R[X]).roots = 0
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Polynomial.logMahlerMeasure_eq_log_leadingCoeff_add_sum_log_roots`：logMa
hlerMeasure_eq_log_leadingCoeff_add_sum_log_roots (p : Complex[X]) : p.logMahler
Measure = log ‖p.leadingCoeff‖ + (p.roots.map (fun a =>…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Real.exp_log`：exp_log (hx : 0 < x) : exp (log x) = x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `norm_pos_iff`：∀ {E : Type u_5} [inst : NormedAddGroup E] {a : E}, 0 < ‖a
‖ ↔ a ≠ 0
· 使用定理 `Polynomial.leadingCoeff_ne_zero`：leadingCoeff_ne_zero : leadingCoeff p !
= 0 ↔ p != 0
· 使用定理 `Polynomial.mahlerMeasure_pos_of_ne_zero`：mahlerMeasure_pos_of_ne_zero (h
p : p != 0) : 0 < p.mahlerMeasure
· 使用定理 `Real.exp_add`：∀ (x y : ℝ), Real.exp (x + y) = Real.exp x * Real.exp y
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.logMahlerMeasure_eq_log_MahlerMeasure`：logMahlerMeasure_eq_lo
g_MahlerMeasure : p.logMahlerMeasure = log p.mahlerMeasure
· 使用定理 `Real.posLog_eq_log_max_one`：posLog_eq_log_max_one (hx : 0 <= x) : log⁺ x
 = log (max 1 x)
· 使用定理 `Real.exp_multiset_sum`：exp_multiset_sum (s : Multiset Real) : exp s.sum 
= (s.map exp).prod
· 使用定理 `Multiset.map_map`：map_map (g : β -> γ) (f : α -> β) (s : Multiset α) : m
ap g (map f s) = map (g ∘ f) s
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True

--- 原说明 ---
The Mahler measure of a polynomial is the absolute value of its leading coeffici
ent times
  the product of the absolute values of its roots lying outside the unit disk.
-/
theorem mahlerMeasure_eq_leadingCoeff_mul_prod_roots (p : ℂ[X]) : p.mahlerMeasure =
    ‖p.leadingCoeff‖ * (p.roots.map (fun a ↦ max 1 ‖a‖)).prod := by
  by_cases hp : p = 0
  · simp [hp]
  have := logMahlerMeasure_eq_log_leadingCoeff_add_sum_log_roots p
  rw [logMahlerMeasure_eq_log_MahlerMeasure] at this
  apply_fun exp at this
  rw [exp_add, exp_log <| mahlerMeasure_pos_of_ne_zero hp,
    exp_log <| norm_pos_iff.mpr <| leadingCoeff_ne_zero.mpr hp] at this
  simp [this, exp_multiset_sum, posLog_eq_log_max_one, exp_log]

/-!
### Estimates for the Mahler measure
-/

/-
**Polynomial.one_le_prod_max_one_norm_roots** 是 Mathlib 中的一个引理，位于命名空间 `Polynomia
l`。
形式化陈述：one_le_prod_max_one_norm_roots (p : Complex[X]) : 1 <= (p.roots.map (fun a
 => max 1 ‖a‖)).prod
参数：p : Complex[X]。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
### Estimates for the Mahler measure
-/
lemma one_le_prod_max_one_norm_roots (p : ℂ[X]) : 1 ≤ (p.roots.map (fun a ↦ max 1 ‖a‖)).prod := by
  grind [Multiset.one_le_prod, Multiset.mem_map]
/-
**Polynomial.leadingCoeff_le_mahlerMeasure** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial
`。
形式化陈述：leadingCoeff_le_mahlerMeasure (p : Complex[X]) : ‖p.leadingCoeff‖ <= p.mah
lerMeasure
参数：p : Complex[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Polynomial.mahlerMeasure_eq_leadingCoeff_mul_prod_roots`：mahlerMeasure_e
q_leadingCoeff_mul_prod_roots (p : Complex[X]) : p.mahlerMeasure = ‖p.leadingCoe
ff‖ * (p.roots.map (fun a => max 1 ‖a‖)).prod
· 使用定理 `mul_le_mul_of_nonneg_left`：mul_le_mul_of_nonneg_left [PosMulMono α] (hbc
 : b <= c) (ha : 0 <= a) : a * b <= a * c
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用引理 `Polynomial.one_le_prod_max_one_norm_roots`：one_le_prod_max_one_norm_root
s (p : Complex[X]) : 1 <= (p.roots.map (fun a => max 1 ‖a‖)).prod
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
-/
lemma leadingCoeff_le_mahlerMeasure (p : ℂ[X]) : ‖p.leadingCoeff‖ ≤ p.mahlerMeasure := by
  rw [← mul_one ‖_‖, mahlerMeasure_eq_leadingCoeff_mul_prod_roots]
  gcongr
  exact one_le_prod_max_one_norm_roots p

@[deprecated (since := "2026-01-02")] alias leading_coeff_le_mahlerMeasure :=
  leadingCoeff_le_mahlerMeasure
/-
**Polynomial.prod_max_one_norm_roots_le_mahlerMeasure_of_one_le_leadingCoeff** 是
 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：prod_max_one_norm_roots_le_mahlerMeasure_of_one_le_leadingCoeff {p : Compl
ex[X]} (hlc : 1 <= ‖p.leadingCoeff‖) : (p.roots.map (fun a => max 1 ‖a‖)).prod <
= p.mahlerMeasure
参数：hlc : 1 <= ‖p.leadingCoeff‖。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Polynomial.mahlerMeasure_eq_leadingCoeff_mul_prod_roots`：mahlerMeasure_e
q_leadingCoeff_mul_prod_roots (p : Complex[X]) : p.mahlerMeasure = ‖p.leadingCoe
ff‖ * (p.roots.map (fun a => max 1 ‖a‖)).prod
· 使用定理 `mul_le_mul_of_nonneg_right`：mul_le_mul_of_nonneg_right [MulPosMono α] (h
bc : b <= c) (ha : 0 <= a) : b * a <= c * a
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1
· 使用引理 `Polynomial.one_le_prod_max_one_norm_roots`：one_le_prod_max_one_norm_root
s (p : Complex[X]) : 1 <= (p.roots.map (fun a => max 1 ‖a‖)).prod
-/
lemma prod_max_one_norm_roots_le_mahlerMeasure_of_one_le_leadingCoeff {p : ℂ[X]}
    (hlc : 1 ≤ ‖p.leadingCoeff‖) : (p.roots.map (fun a ↦ max 1 ‖a‖)).prod ≤ p.mahlerMeasure := by
  rw [← one_mul (Multiset.prod _), mahlerMeasure_eq_leadingCoeff_mul_prod_roots]
  gcongr
  exact zero_le_one.trans <| one_le_prod_max_one_norm_roots p

/-- If the leading coefficient of a polynomial has norm at least 1, then its Mahler measure
is at least 1. This holds in particular for nonzero polynomials with integer coefficients,
since their leading coefficient is a nonzero integer. -/
/-
**Polynomial.one_le_mahlerMeasure_of_one_le_norm_leadingCoeff** 是 Mathlib 中的一个引理
，位于命名空间 `Polynomial`。
形式化陈述：one_le_mahlerMeasure_of_one_le_norm_leadingCoeff {p : Complex[X]} (hlc : 1
 <= ‖p.leadingCoeff‖) : 1 <= p.mahlerMeasure
参数：hlc : 1 <= ‖p.leadingCoeff‖。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `Polynomial.leadingCoeff_le_mahlerMeasure`：leadingCoeff_le_mahlerMeasure 
(p : Complex[X]) : ‖p.leadingCoeff‖ <= p.mahlerMeasure

--- 原说明 ---
If the leading coefficient of a polynomial has norm at least 1, then its Mahler 
measure
is at least 1. This holds in particular for nonzero polynomials with integer coe
fficients,
since their leading coefficient is a nonzero integer.
-/
lemma one_le_mahlerMeasure_of_one_le_norm_leadingCoeff {p : ℂ[X]}
    (hlc : 1 ≤ ‖p.leadingCoeff‖) : 1 ≤ p.mahlerMeasure :=
  hlc.trans (leadingCoeff_le_mahlerMeasure p)

open Filter MeasureTheory Set in
/-- The Mahler measure of a polynomial is bounded above by the sum of the norms of its coefficients.
-/
/-
**Polynomial.mahlerMeasure_le_sum_norm_coeff** 是 Mathlib 中的一个定理，位于命名空间 `Polynomi
al`。
形式化陈述：mahlerMeasure_le_sum_norm_coeff (p : Complex[X]) : p.mahlerMeasure <= p.su
m fun _ a => ‖a‖
参数：p : Complex[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.mahlerMeasure_zero`：mahlerMeasure_zero : (0 : Complex[X]).mah
lerMeasure = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.sum_zero_index`：sum_zero_index {S : Type*} [AddCommMonoid S] 
(f : Nat -> R -> S) : (0 : R[X]).sum f = 0
· 使用定理 `Finset.sum_pos'`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMonoid M
] [inst_1 : Preorder M] [IsOrderedCancelAddMonoid M] {f : ι → M}   {s : Finset ι
} [Ad…
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `mul_inv_rev`：mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹
· 使用定理 `intervalIntegral.integral_const`：integral_const [CompleteSpace E] (c : E
) : ∫ _ in a..b, c = (b - a) • c
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `inv_mul_cancel_left₀`：inv_mul_cancel_left₀ (h : a != 0) (b : G₀) : a⁻¹ *
 (a * b) = b
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Real.exp_log`：exp_log (hx : 0 < x) : exp (log x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Polynomial.mahlerMeasure_def_of_ne_zero`：mahlerMeasure_def_of_ne_zero (h
p : p != 0) : p.mahlerMeasure = exp ((2 * π)⁻¹ * ∫ (x : Real) in (0)..(2 * π), l
og ‖eval (circleMap 0 1 x) p‖…
· 使用引理 `Real.circleAverage_def`：circleAverage_def : circleAverage f c R = (2 * π
)⁻¹ • ∫ θ in 0..2 * π, f (circleMap c R θ)
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用定理 `Real.exp_monotone`：exp_monotone : Monotone exp
（共 117 条，此处仅展示前 30 条）

--- 原说明 ---
The Mahler measure of a polynomial is bounded above by the sum of the norms of i
ts coefficients.
-/
theorem mahlerMeasure_le_sum_norm_coeff (p : ℂ[X]) : p.mahlerMeasure ≤ p.sum fun _ a ↦ ‖a‖ := by
  by_cases hp : p = 0
  · simp [hp]
  have : 0 < p.sum fun _ a ↦ ‖a‖ :=
    Finset.sum_pos' (fun i _ ↦ norm_nonneg (p.coeff i)) ⟨p.natDegree, by simp [hp]⟩
  rw [show (p.sum fun _ a ↦ ‖a‖) = rexp (circleAverage (fun _ ↦ log (p.sum fun _ a ↦ ‖a‖)) 0 1)
    by simp [circleAverage_def, mul_assoc, exp_log this], mahlerMeasure_def_of_ne_zero hp,
    circleAverage_def, smul_eq_mul]
  gcongr
  apply intervalIntegral.integral_mono_ae_restrict (by positivity)
    p.intervalIntegrable_mahlerMeasure (by simp)
  rw [EventuallyLE, eventually_iff_exists_mem]
  use {x : ℝ | eval (circleMap 0 1 x) p ≠ 0}
  constructor
  · rw [mem_ae_iff, compl_def, Measure.restrict_apply' (by simp)]
    apply (Finite.of_sdiff _ <| finite_singleton (2 * π)).measure_zero
    simp only [ne_eq, mem_ofPred_eq, Decidable.not_not, inter_sdiff_assoc, Icc_sdiff_right]
    rw [ofPred_inter_eq_sep]
    apply Finite.of_finite_image (f := circleMap 0 1) ((Multiset.finite_toSet p.roots).subset _)
      <| fun _ h _ k l ↦ injOn_circleMap_of_abs_sub_le' one_ne_zero (by linarith) h.1 k.1 l
    simp [hp]
  · intro _ _
    gcongr
    rw [eval_eq_sum]
    apply norm_sum_le_of_le p.support
    simp

open MeasureTheory Set in
/-- **Landau's inequality**: the Mahler measure of a polynomial is at most the ℓ² norm
of its coefficient vector, `√(∑ ‖coeff i‖²)`.

This is the classical inequality due to Landau (1905). Combined with the multiplicativity of the
Mahler measure (`mahlerMeasure_mul`), it gives the Mignotte bound on coefficients of polynomial
factors.

TODO: restate using a dedicated polynomial ℓ² norm once one is defined (see the TODO in
`Mathlib.Analysis.Polynomial.Norm`). -/
/-
**Polynomial.mahlerMeasure_le_sqrt_sum_sq_norm_coeff** 是 Mathlib 中的一个定理，位于命名空间 `
Polynomial`。
形式化陈述：mahlerMeasure_le_sqrt_sum_sq_norm_coeff (p : Polynomial Complex) : p.mahle
rMeasure <= √(∑ i in p.support, ‖p.coeff i‖ ^ 2)
参数：p : Polynomial Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.uIoc_of_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, a ≤ b
 → Set.uIoc a b = Set.Ioc a b
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `mul_pos`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 : Pr
eorder α] [PosMulStrictMono α], 0 < a → 0 < b → 0 < a * b
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `Real.pi_pos`：pi_pos : 0 < π
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Real.volume_uIoc`：volume_uIoc {a b : Real} : volume (uIoc a b) = ofReal 
|b - a|
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用引理 `abs_mul`：abs_mul (a b : α) : |a * b| = |a| * |b|
· 使用定理 `Nat.abs_ofNat`：abs_ofNat (n : Nat) [n.AtLeastTwo] : |(ofNat(n) : R)| = o
fNat(n)
· 使用定理 `ENNReal.ofReal_mul`：ofReal_mul {p q : Real} (hp : 0 <= p) : ENNReal.ofRe
al (p * q) = ENNReal.ofReal p * ENNReal.ofReal q
· 使用定理 `ENNReal.ofReal_ofNat`：∀ (n : ℕ) [inst : n.AtLeastTwo], ENNReal.ofReal (O
fNat.ofNat n) = OfNat.ofNat n
· 使用定理 `ENNReal.instNoZeroDivisors`：NoZeroDivisors ENNReal
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `ENNReal.instCharZero`：CharZero ENNReal
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Polynomial.mahlerMeasure_zero`：mahlerMeasure_zero : (0 : Complex[X]).mah
lerMeasure = 0
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
（共 110 条，此处仅展示前 30 条）

--- 原说明 ---
**Landau's inequality**: the Mahler measure of a polynomial is at most the ℓ² no
rm
of its coefficient vector, `√(∑ ‖coeff i‖²)`.

This is the classical inequality due to Landau (1905). Combined with the multipl
icativity of the
Mahler measure (`mahlerMeasure_mul`), it gives the Mignotte bound on coefficient
s of polynomial
factors.

TODO: restate using a dedicated polynomial ℓ² norm once one is defined (see the 
TODO in
`Mathlib.Analysis.Polynomial.Norm`).
-/
theorem mahlerMeasure_le_sqrt_sum_sq_norm_coeff (p : Polynomial ℂ) :
    p.mahlerMeasure ≤ √(∑ i ∈ p.support, ‖p.coeff i‖ ^ 2) := by
  -- Proof: Jensen's inequality (twice) + Parseval's identity
  have : IsFiniteMeasure (volume.restrict (uIoc 0 (2 * π))) := by
    rw [uIoc_of_le (by positivity)]; infer_instance
  have : NeZero (volume (uIoc 0 (2 * π))) := ⟨by simp⟩
  by_cases! hp : p = 0
  · simp [hp]
  have : ∀ᵐ (θ : ℝ) ∂volume.restrict (uIoc 0 (2 * π)), 0 < ‖p.eval (circleMap 0 1 θ)‖ := by
    rw [ae_restrict_iff' measurableSet_uIoc]
    refine Set.Finite.measure_zero ?_ _
    simp only [norm_pos_iff, ne_eq, compl_ofPred, Classical.not_imp, Decidable.not_not]
    refine Finite.of_finite_image (f := circleMap 0 1) (p.roots.finite_toSet.subset ?_) ?_
    · rintro z ⟨θ, ⟨_, heval⟩, rfl⟩
      exact (mem_roots hp).mpr heval
    · grw [ofPred_and, inter_subset_left]
      exact injOn_circleMap_of_abs_sub_le one_ne_zero (by simp [abs_of_pos pi_pos])
  have hlogAe : ∀ᵐ (θ : ℝ) ∂volume.restrict (uIoc 0 (2 * π)),
      exp (log ‖p.eval (circleMap 0 1 θ)‖) = ‖p.eval (circleMap 0 1 θ)‖ := by
    filter_upwards [this] with θ hθ
    exact exp_log hθ
  have hcont : Continuous (fun x : ℝ ↦ ‖eval (circleMap 0 1 x) p‖) := by fun_prop
  simp only [mahlerMeasure, logMahlerMeasure, ne_eq, hp, not_false_eq_true, ↓reduceIte]
  rw [circleAverage_eq_intervalAverage]
  calc exp (⨍ (θ : ℝ) in 0..(2 * π), log ‖p.eval (circleMap 0 1 θ)‖)
    ≤ ⨍ (θ : ℝ) in 0..(2 * π), exp (log ‖p.eval (circleMap 0 1 θ)‖) := by
        -- First Jensen's inequality invocation
        refine convexOn_exp.map_average_le continuousOn_exp isClosed_univ (by simp) ?_ ?_
        · rw [Set.uIoc_of_le (by positivity : 0 ≤ 2 * Real.pi)]
          exact ((analyticOnNhd_id.aeval_polynomial p).meromorphicOn.circleIntegrable_log_norm).1
        · exact (integrable_congr hlogAe).mpr hcont.integrableOn_uIoc
    _ = ⨍ (θ : ℝ) in 0..(2 * π), ‖p.eval (circleMap 0 1 θ)‖ := average_congr hlogAe
    _ = √((⨍ (θ : ℝ) in 0..(2 * π), ‖p.eval (circleMap 0 1 θ)‖) ^ 2) := by
        rw [sqrt_sq]; exact integral_nonneg (fun _ ↦ norm_nonneg _)
    _ ≤ √(⨍ (θ : ℝ) in 0..(2 * π), ‖p.eval (circleMap 0 1 θ)‖ ^ 2) := by
        -- Second Jensen's inequality invocation
        gcongr
        refine (convexOn_pow 2).map_average_le (continuousOn_pow 2)
            isClosed_Ici (by filter_upwards; simp) ?_ ?_
        · exact hcont.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
        · exact ((continuous_pow 2).comp hcont).integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
    _ = √(circleAverage (fun θ ↦ ‖p.eval θ‖ ^ 2) 0 1) := by simp [circleAverage_eq_intervalAverage]
    _ = √(∑ i ∈ p.support, ‖p.coeff i‖ ^ 2) := by simp [p.sum_sq_norm_coeff_eq_circleAverage]

/-- The Mahler measure of a polynomial is at most the sup norm of the polynomial times the square
root of its degree plus one. -/
/-
**Polynomial.mahlerMeasure_le_sqrt_natDegree_add_one_mul_supNorm** 是 Mathlib 中的一
个定理，位于命名空间 `Polynomial`。
形式化陈述：mahlerMeasure_le_sqrt_natDegree_add_one_mul_supNorm (p : Polynomial Comple
x) : p.mahlerMeasure <= √(p.natDegree + 1) * p.supNorm
参数：p : Polynomial Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Polynomial.mahlerMeasure_le_sqrt_sum_sq_norm_coeff`：mahlerMeasure_le_sqr
t_sum_sq_norm_coeff (p : Polynomial Complex) : p.mahlerMeasure <= √(∑ i in p.sup
port, ‖p.coeff i‖ ^ 2)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.sqrt_mul`：sqrt_mul {x : Real} (hx : 0 <= x) (y : Real) : √(x * y) =
 √x * √y
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Right.add_pos_of_nonneg_of_pos`：∀ {α : Type u_1} [inst : AddZeroClass α]
 [inst_1 : Preorder α] [AddRightMono α] {a b : α}, 0 ≤ a → 0 < b → 0 < a + b
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Nat.cast_nonneg'`：cast_nonneg' (n : Nat) : 0 <= (n : α)
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Real.sqrt_sq`：sqrt_sq (h : 0 <= x) : √(x ^ 2) = x
· 使用引理 `Polynomial.supNorm_nonneg`：supNorm_nonneg : 0 <= p.supNorm
· 使用定理 `Real.sqrt_monotone`：sqrt_monotone : Monotone Real.sqrt
· 使用定理 `Finset.sum_le_card_nsmul`：∀ {ι : Type u_1} {N : Type u_5} [inst : AddCom
mMonoid N] [inst_1 : Preorder N] [AddLeftMono N] (s : Finset ι)   (f : ι → N) (n
 : N), (∀ x ∈ …
· 使用定理 `pow_le_pow_left₀`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 :
 Preorder M₀] {a b : M₀} [PosMulMono M₀] [MulPosMono M₀],   0 ≤ a → a ≤ b → ∀ (n
 : ℕ),…
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用引理 `Polynomial.le_supNorm`：le_supNorm (i : Nat) : ‖p.coeff i‖ <= p.supNorm
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
· 使用定理 `mul_le_mul_of_nonneg_right`：mul_le_mul_of_nonneg_right [MulPosMono α] (h
bc : b <= c) (ha : 0 <= a) : b * a <= c * a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Polynomial.card_supp_le_succ_natDegree`：card_supp_le_succ_natDegree (p :
 R[X]) : #p.support <= p.natDegree + 1
· 使用定理 `Even.pow_nonneg`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : LinearOr
der R] [IsOrderedRing R] [ExistsAddOfLE R] {n : ℕ},   Even n → ∀ (a : R), 0 ≤ a 
^ n
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
（共 34 条，此处仅展示前 30 条）

--- 原说明 ---
The Mahler measure of a polynomial is at most the sup norm of the polynomial tim
es the square
root of its degree plus one.
-/
theorem mahlerMeasure_le_sqrt_natDegree_add_one_mul_supNorm (p : Polynomial ℂ) :
    p.mahlerMeasure ≤ √(p.natDegree + 1) * p.supNorm :=
  (p.mahlerMeasure_le_sqrt_sum_sq_norm_coeff).trans <| by
    rw [show √(↑(p.natDegree) + 1) * p.supNorm = √((p.natDegree + 1) * p.supNorm ^ 2) by
      rw [Real.sqrt_mul (by positivity), Real.sqrt_sq p.supNorm_nonneg]]
    gcongr
    refine (p.support.sum_le_card_nsmul _ (p.supNorm ^ 2) fun i _ ↦ ?_).trans ?_
    · gcongr; exact p.le_supNorm _
    · simp only [nsmul_eq_mul]
      gcongr
      exact mod_cast p.card_supp_le_succ_natDegree

open Multiset in
/-
**Polynomial.norm_coeff_le_choose_mul_mahlerMeasure** 是 Mathlib 中的一个定理，位于命名空间 `P
olynomial`。
形式化陈述：norm_coeff_le_choose_mul_mahlerMeasure (n : Nat) (p : Complex[X]) : ‖p.coe
ff n‖ <= (p.natDegree).choose n * p.mahlerMeasure
参数：n : Nat；p : Complex[X]。
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
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `Polynomial.mahlerMeasure_zero`：mahlerMeasure_zero : (0 : Complex[X]).mah
lerMeasure = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `lt_or_ge`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a < b ∨ b ≤
 a
· 使用定理 `Polynomial.coeff_eq_zero_of_natDegree_lt`：coeff_eq_zero_of_natDegree_lt 
{p : R[X]} {n : Nat} (h : p.natDegree < n) : p.coeff n = 0
· 使用定理 `Nat.choose_eq_zero_of_lt`：choose_eq_zero_of_lt : forall {n k}, n < k -> 
choose n k = 0 | _, 0, hk => absurd hk (Nat.not_lt_zero _) | 0, _ + 1, _ => choo
se_zero_succ _…
· 使用定理 `CharP.cast_eq_zero`：∀ (R : Type u_1) [inst : AddMonoidWithOne R] (p : ℕ)
 [CharP R p], ↑p = 0
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Polynomial.mahlerMeasure_eq_leadingCoeff_mul_prod_roots`：mahlerMeasure_e
q_leadingCoeff_mul_prod_roots (p : Complex[X]) : p.mahlerMeasure = ‖p.leadingCoe
ff‖ * (p.roots.map (fun a => max 1 ‖a‖)).prod
· 使用定理 `mul_left_comm`：mul_left_comm (a b c : G) : a * (b * c) = b * (a * c)
· 使用定理 `Polynomial.coeff_eq_esymm_roots_of_card`：∀ {R : Type u_1} [inst : CommRi
ng R] [inst_1 : IsDomain R] {p : Polynomial R},   p.roots.card = p.natDegree →  
   ∀ {k : ℕ}, k ≤ p.natDegree…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Polynomial.splits_iff_card_roots`：splits_iff_card_roots : Splits f ↔ f.r
oots.card = f.natDegree
· 使用定理 `IsAlgClosed.splits`：∀ {k : Type u} {inst : Field k} [self : IsAlgClosed 
k] (p : Polynomial k), p.Splits
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `norm_mul`：∀ {α : Type u_2} [inst : Norm α] [inst_1 : Mul α] [NormMulClas
s α] (a b : α), ‖a * b‖ = ‖a‖ * ‖b‖
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `norm_pow`：norm_pow (a : α) : forall n : Nat, ‖a ^ n‖ = ‖a‖ ^ n
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `norm_neg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), ‖-a‖ =
 ‖a‖
· 使用定理 `NormOneClass.norm_one`：∀ {α : Type u_5} {inst : Norm α} {inst_1 : One α}
 [self : NormOneClass α], ‖1‖ = 1
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
（共 87 条，此处仅展示前 30 条）
-/
theorem norm_coeff_le_choose_mul_mahlerMeasure (n : ℕ) (p : ℂ[X]) :
    ‖p.coeff n‖ ≤ (p.natDegree).choose n * p.mahlerMeasure := by
  by_cases hp : p = 0
  · simp [hp]
  rcases lt_or_ge p.natDegree n with hlt | hn
  · simp [coeff_eq_zero_of_natDegree_lt hlt, Nat.choose_eq_zero_of_lt hlt]
  rw [mahlerMeasure_eq_leadingCoeff_mul_prod_roots, mul_left_comm,
    coeff_eq_esymm_roots_of_card (splits_iff_card_roots.mp (IsAlgClosed.splits p)) hn, mul_assoc,
    norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul,
    mul_le_mul_iff_right₀ (by simp [leadingCoeff_ne_zero.mpr hp]), esymm,
    Finset.sum_multiset_map_count]
  apply le_trans <| norm_sum_le _ _
  simp_rw [nsmul_eq_mul, norm_mul, _root_.norm_natCast]
  let S := powersetCard (p.natDegree - n) p.roots
  --to be used later in the calc block:
  have (x : Multiset ℂ) (hx : x ∈ S.toFinset) : ∏ x_1 ∈ x.toFinset, ‖x_1‖ ^ count x_1 x
      ≤ ∏ m ∈ p.roots.toFinset, max 1 ‖m‖ ^ count m p.roots := by
    rw [mem_toFinset, mem_powersetCard] at hx
    calc
    ∏ z ∈ x.toFinset, ‖z‖ ^ count z x
      ≤ ∏ z ∈ x.toFinset, (1 ⊔ ‖z‖) ^ count z x := by
      gcongr with a
      exact le_max_right 1 ‖a‖
    _ ≤ ∏ z ∈ p.roots.toFinset, (1 ⊔ ‖z‖) ^ count z x := by
      simp_rw [← coe_nnnorm]
      norm_cast
      exact Finset.prod_le_prod_of_subset_of_one_le' (toFinset_subset.mpr (subset_of_le hx.1))
        (fun a _ _ ↦ one_le_pow₀ (le_max_left 1 ‖a‖))
    _ ≤ ∏ z ∈ p.roots.toFinset, (1 ⊔ ‖z‖) ^ count z p.roots := by
      gcongr with a
      · exact le_max_left 1 ‖a‖
      · exact hx.1
  --final calc block:
  calc ∑ x ∈ S.toFinset, count x S * ‖x.prod‖
    _ ≤ ∑ x ∈ S.toFinset, count x S * ((p.roots).map (fun a ↦ max 1 ‖a‖)).prod := by
      gcongr with x hx
      rw [Finset.prod_multiset_map_count, Finset.prod_multiset_count, norm_prod]
      simp_rw [norm_pow]
      exact this x hx
    _ = p.natDegree.choose n * (p.roots.map (fun a ↦ 1 ⊔ ‖a‖)).prod := by
      rw [← Finset.sum_mul]
      congr
      norm_cast
      simp only [mem_powersetCard, mem_toFinset, imp_self, implies_true, sum_count_eq_card,
        card_powersetCard, S, ← Nat.choose_symm hn]
      congr
      exact splits_iff_card_roots.mp <| IsAlgClosed.splits p
/-
**Polynomial.supNorm_le_choose_natDegree_div_two_mul_mahlerMeasure** 是 Mathlib 中
的一个定理，位于命名空间 `Polynomial`。
形式化陈述：supNorm_le_choose_natDegree_div_two_mul_mahlerMeasure (p : Polynomial Comp
lex) : p.supNorm <= p.natDegree.choose (p.natDegree / 2) * p.mahlerMeasure
参数：p : Polynomial Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Polynomial.exists_eq_supNorm`：exists_eq_supNorm : exists i : Nat, p.supN
orm = ‖p.coeff i‖
· 使用定理 `Polynomial.norm_coeff_le_choose_mul_mahlerMeasure`：norm_coeff_le_choose_
mul_mahlerMeasure (n : Nat) (p : Complex[X]) : ‖p.coeff n‖ <= (p.natDegree).choo
se n * p.mahlerMeasure
· 使用定理 `mul_le_mul_of_nonneg_right`：mul_le_mul_of_nonneg_right [MulPosMono α] (h
bc : b <= c) (ha : 0 <= a) : b * a <= c * a
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Nat.choose_le_middle`：choose_le_middle (r n : Nat) : choose n r <= choos
e n (n / 2)
· 使用定理 `Polynomial.mahlerMeasure_nonneg`：mahlerMeasure_nonneg : 0 <= p.mahlerMea
sure
-/
theorem supNorm_le_choose_natDegree_div_two_mul_mahlerMeasure (p : Polynomial ℂ) :
    p.supNorm ≤ p.natDegree.choose (p.natDegree / 2) * p.mahlerMeasure := by
  obtain ⟨i, hi⟩ := p.exists_eq_supNorm
  calc p.supNorm = ‖p.coeff i‖ := hi
    _ ≤ (p.natDegree.choose i) * p.mahlerMeasure := p.norm_coeff_le_choose_mul_mahlerMeasure i
    _ ≤ (p.natDegree.choose (p.natDegree / 2)) * p.mahlerMeasure :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.choose_le_middle i p.natDegree)
        p.mahlerMeasure_nonneg

/-!
### The Mignotte bound
-/

/-- **Mignotte's coefficient bound**: if `f = g * h` and `h` has Mahler measure at least 1
(which holds in particular when `h` has integer coefficients with nonzero leading coefficient),
then the coefficients of `g` are bounded by a binomial coefficient times the Mahler measure
of `g * h`.

Combined with `mahlerMeasure_le_sqrt_sum_sq_norm_coeff` (Landau's inequality), this gives
the classical Mignotte bound
`‖g.coeff n‖ ≤ C(deg g, n) · √(∑ i ∈ f.support, ‖f.coeff i‖ ^ 2)`
used in polynomial factorization algorithms (Berlekamp–Zassenhaus). -/
/-
**Polynomial.norm_coeff_le_choose_mul_mahlerMeasure_of_one_le_mahlerMeasure** 是 
Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：norm_coeff_le_choose_mul_mahlerMeasure_of_one_le_mahlerMeasure (n : Nat) (
g h : Complex[X]) (hh : 1 <= h.mahlerMeasure) : ‖g.coeff n‖ <= g.natDegree.choos
e n * (g * h).mahlerMeasure
参数：n : Nat；g h : Complex[X]；hh : 1 <= h.mahlerMeasure。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Polynomial.norm_coeff_le_choose_mul_mahlerMeasure`：norm_coeff_le_choose_
mul_mahlerMeasure (n : Nat) (p : Complex[X]) : ‖p.coeff n‖ <= (p.natDegree).choo
se n * p.mahlerMeasure
· 使用定理 `mul_le_mul_of_nonneg_left`：mul_le_mul_of_nonneg_left [PosMulMono α] (hbc
 : b <= c) (ha : 0 <= a) : a * b <= a * c
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.mahlerMeasure_mul`：mahlerMeasure_mul (p q : Complex[X]) : (p 
* q).mahlerMeasure = p.mahlerMeasure * q.mahlerMeasure
· 使用定理 `le_mul_of_one_le_right`：le_mul_of_one_le_right [PosMulMono α] (ha : 0 <=
 a) (h : 1 <= b) : a <= a * b
· 使用定理 `Polynomial.mahlerMeasure_nonneg`：mahlerMeasure_nonneg : 0 <= p.mahlerMea
sure
· 使用定理 `Nat.cast_nonneg'`：cast_nonneg' (n : Nat) : 0 <= (n : α)
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α

--- 原说明 ---
**Mignotte's coefficient bound**: if `f = g * h` and `h` has Mahler measure at l
east 1
(which holds in particular when `h` has integer coefficients with nonzero leadin
g coefficient),
then the coefficients of `g` are bounded by a binomial coefficient times the Mah
ler measure
of `g * h`.

Combined with `mahlerMeasure_le_sqrt_sum_sq_norm_coeff` (Landau's inequality), t
his gives
the classical Mignotte bound
`‖g.coeff n‖ ≤ C(deg g, n) · √(∑ i ∈ f.support, ‖f.coeff i‖ ^ 2)`
used in polynomial factorization algorithms (Berlekamp–Zassenhaus).
-/
theorem norm_coeff_le_choose_mul_mahlerMeasure_of_one_le_mahlerMeasure (n : ℕ) (g h : ℂ[X])
    (hh : 1 ≤ h.mahlerMeasure) :
    ‖g.coeff n‖ ≤ g.natDegree.choose n * (g * h).mahlerMeasure :=
  (g.norm_coeff_le_choose_mul_mahlerMeasure n).trans <| by
    gcongr
    rw [mahlerMeasure_mul]
    exact le_mul_of_one_le_right g.mahlerMeasure_nonneg hh

end Polynomial

section generic

/-!
### Mahler Measure on Other Rings

While the Mahler measure is an inherently Complex concept, we often want to work with it for
polynomials with coefficients in subrings of `ℂ`. To do so, we introduce `mapMahlerMeasure`. This
takes a `RingHom A ℂ` which takes the polynomial from `A[X]` to `ℂ[X]`.

Some lemmas require the `RingHom` to also preserve the norm on the base ring, e.g.,
`leadingCoeff_le_mapMahlerMeasure`. Those will come below.
-/

namespace Polynomial

variable {A : Type*} [Semiring A] (p : A[X]) (v : A →+* ℂ)

/-- The Mahler measure for polynomials on rings other than `ℂ`. Most theorems
will require `A` to be a `NormedRing` and `v` to be an isometry. See, e.g.,
`mapMahlerMeasure_const` -/
/-
**Polynomial.mapMahlerMeasure** 是 Mathlib 中的一个定义，位于命名空间 `Polynomial`。
形式化陈述：mapMahlerMeasure
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Mahler measure for polynomials on rings other than `ℂ`. Most theorems
will require `A` to be a `NormedRing` and `v` to be an isometry. See, e.g.,
`mapMahlerMeasure_const`
-/
noncomputable def mapMahlerMeasure := (p.map v).mahlerMeasure
/-
**Polynomial.mapMahlerMeasure_eq** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：mapMahlerMeasure_eq : p.mapMahlerMeasure v = (p.map v).mahlerMeasure
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mapMahlerMeasure_eq : p.mapMahlerMeasure v = (p.map v).mahlerMeasure := rfl
/-
**Polynomial.mapMahlerMeasure_mul** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：mapMahlerMeasure_mul (f g : A[X]) : (f * g).mapMahlerMeasure v = (f.mapMah
lerMeasure v) * (g.mapMahlerMeasure v)
参数：f g : A[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.map_mul`：∀ {R : Type u} {S : Type v} [inst : Semiring R] {p q
 : Polynomial R} [inst_1 : Semiring S] (f : R →+* S),   Polynomial.map f (p * q)
 = Polyn…
· 使用定理 `Polynomial.mahlerMeasure_mul`：mahlerMeasure_mul (p q : Complex[X]) : (p 
* q).mahlerMeasure = p.mahlerMeasure * q.mahlerMeasure
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mapMahlerMeasure_mul (f g : A[X]) :
    (f * g).mapMahlerMeasure v = (f.mapMahlerMeasure v) * (g.mapMahlerMeasure v) := by
  simp [mapMahlerMeasure, mahlerMeasure_mul]
/-
**Polynomial.mapMahlerMeasure_nonneg** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：mapMahlerMeasure_nonneg : 0 <= p.mapMahlerMeasure v
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.mahlerMeasure_nonneg`：mahlerMeasure_nonneg : 0 <= p.mahlerMea
sure
-/
lemma mapMahlerMeasure_nonneg : 0 ≤ p.mapMahlerMeasure v :=
  Polynomial.mahlerMeasure_nonneg _

@[simp]
/-
**Polynomial.mapMahlerMeasure_zero** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：mapMahlerMeasure_zero : (0 : A[X]).mapMahlerMeasure v = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.map_zero`：∀ {R : Type u} {S : Type v} [inst : Semiring R] [in
st_1 : Semiring S] (f : R →+* S), Polynomial.map f 0 = 0
· 使用定理 `Polynomial.mahlerMeasure_zero`：mahlerMeasure_zero : (0 : Complex[X]).mah
lerMeasure = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mapMahlerMeasure_zero : (0 : A[X]).mapMahlerMeasure v = 0 := by
  simp [mapMahlerMeasure]

@[simp]
/-
**Polynomial.mapMahlerMeasure_one** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：mapMahlerMeasure_one : (1 : A[X]).mapMahlerMeasure v = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.map_one`：∀ {R : Type u} {S : Type v} [inst : Semiring R] [ins
t_1 : Semiring S] (f : R →+* S), Polynomial.map f 1 = 1
· 使用定理 `Polynomial.mahlerMeasure_one`：mahlerMeasure_one : (1 : Complex[X]).mahle
rMeasure = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mapMahlerMeasure_one : (1 : A[X]).mapMahlerMeasure v = 1 := by
  simp [mapMahlerMeasure]

variable {A : Type*} [NormedRing A] (p : A[X]) (v : A →+* ℂ)
/-
**Polynomial.mapMahlerMeasure_const** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：mapMahlerMeasure_const (hv : Isometry v) (z : A) : (C z).mapMahlerMeasure 
v = ‖z‖
参数：hv : Isometry v；z : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.map_C`：map_C : (C a).map f = C (f a)
· 使用定理 `Polynomial.mahlerMeasure_const`：mahlerMeasure_const (z : Complex) : (C z
).mahlerMeasure = ‖z‖
· 使用定理 `Isometry.norm_map_of_map_zero`：∀ {E : Type u_2} {F : Type u_3} [inst : S
eminormedAddGroup E] [inst_1 : SeminormedAddGroup F] {f : E → F},   Isometry f →
 f 0 = 0 → ∀ (x : E…
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mapMahlerMeasure_const (hv : Isometry v) (z : A) : (C z).mapMahlerMeasure v = ‖z‖ := by
  simp [mapMahlerMeasure, hv.norm_map_of_map_zero (map_zero _)]
/-
**Polynomial.leadingCoeff_le_mapMahlerMeasure** 是 Mathlib 中的一个引理，位于命名空间 `Polynom
ial`。
形式化陈述：leadingCoeff_le_mapMahlerMeasure (hv : Isometry v) : ‖p.leadingCoeff‖ <= p
.mapMahlerMeasure v
参数：hv : Isometry v。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `Isometry.injective`：∀ {α : Type u} {β : Type v} [inst : EMetricSpace α] 
[inst_1 : PseudoEMetricSpace β] {f : α → β},   Isometry f → Function.Injective f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `Isometry.norm_map_of_map_zero`：∀ {E : Type u_2} {F : Type u_3} [inst : S
eminormedAddGroup E] [inst_1 : SeminormedAddGroup F] {f : E → F},   Isometry f →
 f 0 = 0 → ∀ (x : E…
· 使用定理 `Polynomial.leadingCoeff_map_of_leadingCoeff_ne_zero`：leadingCoeff_map_of
_leadingCoeff_ne_zero (f : R ->+* S) (hf : f (leadingCoeff p) != 0) : leadingCoe
ff (p.map f) = f (leadingCoeff p)
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用引理 `Polynomial.leadingCoeff_le_mahlerMeasure`：leadingCoeff_le_mahlerMeasure 
(p : Complex[X]) : ‖p.leadingCoeff‖ <= p.mahlerMeasure
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Polynomial.mapMahlerMeasure.eq_1`：∀ {A : Type u_1} [inst : Semiring A] (
p : Polynomial A) (v : A →+* ℂ),   p.mapMahlerMeasure v = (Polynomial.map v p).m
ahlerMeasure
-/
lemma leadingCoeff_le_mapMahlerMeasure (hv : Isometry v) :
    ‖p.leadingCoeff‖ ≤ p.mapMahlerMeasure v := by
  by_cases hp : p.leadingCoeff = 0
  · simp [hp, mapMahlerMeasure_nonneg]
  · have hv_ne : v p.leadingCoeff ≠ 0 :=
      fun h ↦ hp <| hv.injective <| h.trans (map_zero _).symm
    have hv_norm : ‖v p.leadingCoeff‖ = ‖p.leadingCoeff‖ := hv.norm_map_of_map_zero (map_zero _) _
    grw [← hv_norm, ← leadingCoeff_map_of_leadingCoeff_ne_zero v hv_ne,
      leadingCoeff_le_mahlerMeasure, mapMahlerMeasure]

variable {p} in
/-
**Polynomial.Monic.one_le_mapMahlerMeasure** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial
.Monic`。
形式化陈述：∀ {A : Type u_2} [inst : NormedRing A] {p : Polynomial A} (v : A →+* ℂ) [N
ormOneClass A],   Isometry ⇑v → p.Monic → 1 ≤ p.mapMahlerMeasure v
参数：v : A →+* ℂ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用引理 `Polynomial.leadingCoeff_le_mapMahlerMeasure`：leadingCoeff_le_mapMahlerMe
asure (hv : Isometry v) : ‖p.leadingCoeff‖ <= p.mapMahlerMeasure v
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.Monic.leadingCoeff`：∀ {R : Type u} [inst : Semiring R] {p : P
olynomial R}, p.Monic → p.leadingCoeff = 1
· 使用定理 `NormOneClass.norm_one`：∀ {α : Type u_5} {inst : Norm α} {inst_1 : One α}
 [self : NormOneClass α], ‖1‖ = 1
-/
lemma Monic.one_le_mapMahlerMeasure [NormOneClass A] (hv : Isometry v) (hp : p.Monic) :
    1 ≤ p.mapMahlerMeasure v := by
  grw [← p.leadingCoeff_le_mapMahlerMeasure v hv, hp.leadingCoeff, norm_one]

variable {p} in
/-
**Polynomial.mapMahlerMeasure_pos_of_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Polynomi
al`。
形式化陈述：mapMahlerMeasure_pos_of_ne_zero (hv : Isometry v) (hp : p != 0) : 0 < p.ma
pMahlerMeasure v
参数：hv : Isometry v；hp : p != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.mahlerMeasure_pos_of_ne_zero`：mahlerMeasure_pos_of_ne_zero (h
p : p != 0) : 0 < p.mahlerMeasure
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `Polynomial.map_eq_zero_iff`：∀ {R : Type u} {S : Type v} [inst : Semiring
 R] {p : Polynomial R} [inst_1 : Semiring S] {f : R →+* S},   Function.Injective
 ⇑f → (Polynomia…
· 使用定理 `Isometry.injective`：∀ {α : Type u} {β : Type v} [inst : EMetricSpace α] 
[inst_1 : PseudoEMetricSpace β] {f : α → β},   Isometry f → Function.Injective f
-/
theorem mapMahlerMeasure_pos_of_ne_zero (hv : Isometry v) (hp : p ≠ 0) :
    0 < p.mapMahlerMeasure v :=
  mahlerMeasure_pos_of_ne_zero <| (Polynomial.map_eq_zero_iff hv.injective).not.mpr hp
/-
**Polynomial.mapMahlerMeasure_le_sum_norm_coeff** 是 Mathlib 中的一个定理，位于命名空间 `Polyn
omial`。
形式化陈述：mapMahlerMeasure_le_sum_norm_coeff (hv : Isometry v) : p.mapMahlerMeasure 
v <= p.sum fun _ a => ‖a‖
参数：hv : Isometry v。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `Polynomial.mahlerMeasure_le_sum_norm_coeff`：mahlerMeasure_le_sum_norm_co
eff (p : Complex[X]) : p.mahlerMeasure <= p.sum fun _ a => ‖a‖
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.sum_def`：sum_def {S : Type*} [AddCommMonoid S] (p : R[X]) (f 
: Nat -> R -> S) : p.sum f = ∑ n in p.support, f n (p.coeff n)
· 使用定理 `Polynomial.support_map_of_injective`：support_map_of_injective [Semiring 
R] [Semiring S] (p : R[X]) {f : R ->+* S} (hf : Function.Injective f) : (map f p
).support = p.support
· 使用定理 `Isometry.injective`：∀ {α : Type u} {β : Type v} [inst : EMetricSpace α] 
[inst_1 : PseudoEMetricSpace β] {f : α → β},   Isometry f → Function.Injective f
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.coeff_map`：coeff_map (n : Nat) : coeff (p.map f) n = f (coeff
 p n)
· 使用定理 `Isometry.norm_map_of_map_zero`：∀ {E : Type u_2} {F : Type u_3} [inst : S
eminormedAddGroup E] [inst_1 : SeminormedAddGroup F] {f : E → F},   Isometry f →
 f 0 = 0 → ∀ (x : E…
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mapMahlerMeasure_le_sum_norm_coeff (hv : Isometry v) :
    p.mapMahlerMeasure v ≤ p.sum fun _ a ↦ ‖a‖ := by
  apply mahlerMeasure_le_sum_norm_coeff _ |>.trans_eq
  rw [sum_def, sum_def, support_map_of_injective _ hv.injective]
  exact Finset.sum_congr rfl fun x _ ↦ by
    simp [hv.norm_map_of_map_zero (map_zero _)]
/-
**Polynomial.norm_coeff_le_choose_mul_mapMahlerMeasure** 是 Mathlib 中的一个定理，位于命名空间
 `Polynomial`。
形式化陈述：norm_coeff_le_choose_mul_mapMahlerMeasure (hv : Isometry v) (n : Nat) (p :
 A[X]) : ‖p.coeff n‖ <= (p.natDegree).choose n * p.mapMahlerMeasure v
参数：hv : Isometry v；n : Nat；p : A[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Isometry.norm_map_of_map_zero`：∀ {E : Type u_2} {F : Type u_3} [inst : S
eminormedAddGroup E] [inst_1 : SeminormedAddGroup F] {f : E → F},   Isometry f →
 f 0 = 0 → ∀ (x : E…
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.coeff_map`：coeff_map (n : Nat) : coeff (p.map f) n = f (coeff
 p n)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `Polynomial.norm_coeff_le_choose_mul_mahlerMeasure`：norm_coeff_le_choose_
mul_mahlerMeasure (n : Nat) (p : Complex[X]) : ‖p.coeff n‖ <= (p.natDegree).choo
se n * p.mahlerMeasure
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Polynomial.natDegree_map_eq_of_injective`：natDegree_map_eq_of_injective 
{f : R ->+* S} (hf : Function.Injective f) (p : Polynomial R) : (p.map f).natDeg
ree = p.natDegree
· 使用定理 `Isometry.injective`：∀ {α : Type u} {β : Type v} [inst : EMetricSpace α] 
[inst_1 : PseudoEMetricSpace β] {f : α → β},   Isometry f → Function.Injective f
· 使用定理 `Polynomial.mapMahlerMeasure.eq_1`：∀ {A : Type u_1} [inst : Semiring A] (
p : Polynomial A) (v : A →+* ℂ),   p.mapMahlerMeasure v = (Polynomial.map v p).m
ahlerMeasure
-/
theorem norm_coeff_le_choose_mul_mapMahlerMeasure (hv : Isometry v) (n : ℕ) (p : A[X]) :
    ‖p.coeff n‖ ≤ (p.natDegree).choose n * p.mapMahlerMeasure v := by
  have hv_norm : ‖p.coeff n‖ = ‖v (p.coeff n)‖ :=
    (hv.norm_map_of_map_zero (map_zero _) _).symm
  have hcoeff : ‖v (p.coeff n)‖ = ‖(p.map v).coeff n‖ := by simp
  grw [hv_norm, hcoeff, norm_coeff_le_choose_mul_mahlerMeasure,
    natDegree_map_eq_of_injective hv.injective, mapMahlerMeasure]

end Polynomial

end generic

