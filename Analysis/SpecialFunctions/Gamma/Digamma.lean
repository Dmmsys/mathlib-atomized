/-
Copyright (c) 2026 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
module

public import Mathlib.Analysis.Meromorphic.Complex
public import Mathlib.NumberTheory.Harmonic.GammaDeriv

import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

/-!
# The digamma function

This file defines the digamma function as the logarithmic derivative of the Gamma function and
proves some basic properties.

## Main definitions

* `Complex.digamma`: The digamma function of a complex variable.

## Main statements

* `Complex.digamma_apply_add_one`: The digamma function satisfies the functional equation
  `digamma (s + 1) = digamma s + s⁻¹`.
* `Complex.meromorphic_digamma`: The digamma function is meromorphic.

## TODO

* Prove Gauss' integral representation of the digamma function.
-/

@[expose] public section

namespace Complex

/-- The digamma function, defined as the logarithmic derivative of the Gamma function. -/
/-
**Complex.digamma** 是 Mathlib 中的一个定义，位于命名空间 `Complex`。
形式化陈述：digamma : Complex -> Complex
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The digamma function, defined as the logarithmic derivative of the Gamma functio
n.
-/
noncomputable def digamma : ℂ → ℂ := logDeriv Gamma
/-
**Complex.digamma_def** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：digamma_def : digamma = logDeriv Gamma
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem digamma_def : digamma = logDeriv Gamma := rfl

@[simp]
/-
**Complex.digamma_zero** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：digamma_zero : digamma 0 = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `logDeriv_eq_zero_of_not_differentiableAt`：logDeriv_eq_zero_of_not_differ
entiableAt (f : 𝕜 -> 𝕜') (x : 𝕜) (h : ¬DifferentiableAt 𝕜 f x) : logDeriv f x = 
0
· 使用定理 `Complex.not_differentiableAt_Gamma_zero`：not_differentiableAt_Gamma_zero
 : ¬ DifferentiableAt Complex Gamma 0
-/
theorem digamma_zero : digamma 0 = 0 :=
  logDeriv_eq_zero_of_not_differentiableAt Gamma 0 not_differentiableAt_Gamma_zero
/-
**Complex.digamma_one** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：digamma_one : digamma 1 = - Real.eulerMascheroniConstant
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Complex.digamma_def`：digamma_def : digamma = logDeriv Gamma
· 使用定理 `logDeriv_apply`：logDeriv_apply (f : 𝕜 -> 𝕜') (x : 𝕜) : logDeriv f x = de
riv f x / f x
· 使用定理 `HasDerivAt.deriv`：HasDerivAt.deriv (h : HasDerivAt f f' x) : deriv f x =
 f'
· 使用引理 `Complex.hasDerivAt_Gamma_one`：hasDerivAt_Gamma_one : HasDerivAt Gamma (-
γ) 1
· 使用定理 `Complex.Gamma_one`：Gamma_one : Gamma 1 = 1
· 使用定理 `div_one`：div_one (a : G) : a / 1 = a
-/
theorem digamma_one : digamma 1 = - Real.eulerMascheroniConstant := by
  rw [digamma_def, logDeriv_apply, hasDerivAt_Gamma_one.deriv, Gamma_one, div_one]
/-
**Complex.digamma_one_half** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：digamma_one_half : digamma (1 / 2) = - 2 * log 2 - Real.eulerMascheroniCon
stant
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Complex.digamma_def`：digamma_def : digamma = logDeriv Gamma
· 使用定理 `logDeriv_apply`：logDeriv_apply (f : 𝕜 -> 𝕜') (x : 𝕜) : logDeriv f x = de
riv f x / f x
· 使用定理 `HasDerivAt.deriv`：HasDerivAt.deriv (h : HasDerivAt f f' x) : deriv f x =
 f'
· 使用引理 `Complex.hasDerivAt_Gamma_one_half`：hasDerivAt_Gamma_one_half : HasDerivA
t Gamma (-√π * (γ + 2 * log 2)) (1 / 2)
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Complex.Gamma_one_half_eq`：Complex.Gamma_one_half_eq : Complex.Gamma (1 
/ 2) = (π : Complex) ^ (1 / 2 : Complex)
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `neg_add'`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a b : α), -
(a + b) = -a - b
· 使用定理 `Real.sqrt_eq_rpow`：sqrt_eq_rpow (x : Real) : √x = x ^ (1 / (2 : Real))
· 使用定理 `Complex.ofReal_cpow`：ofReal_cpow {x : Real} (hx : 0 <= x) (y : Real) : (
(x ^ y : Real) : Complex) = (x : Complex) ^ (y : Complex)
· 使用定理 `Real.pi_nonneg`：pi_nonneg : 0 <= π
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `Complex.ofReal_inv`：ofReal_inv (r : Real) : ((r⁻¹ : Real) : Complex) = (
r : Complex)⁻¹
· 使用定理 `mul_div_cancel_left₀`：∀ {M₀ : Type u_1} [inst : CommMonoidWithZero M₀] [
inst_1 : Div M₀] [MulDivCancelClass M₀] (b : M₀) {a : M₀},   a ≠ 0 → a * b / a =
 b
· 使用定理 `EuclideanDomain.toMulDivCancelClass`：∀ {R : Type u} [inst : EuclideanDom
ain R], MulDivCancelClass R
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem digamma_one_half : digamma (1 / 2) = - 2 * log 2 - Real.eulerMascheroniConstant := by
  rw [digamma_def, logDeriv_apply, hasDerivAt_Gamma_one_half.deriv, add_comm, Gamma_one_half_eq,
    neg_mul, ← mul_neg, neg_add', Real.sqrt_eq_rpow, ofReal_cpow Real.pi_nonneg]
  simp
/-
**Complex.digamma_apply_add_one** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：digamma_apply_add_one (s : Complex) (hs : forall m : Nat, s != - m) : diga
mma (s + 1) = digamma s + s⁻¹
参数：s : Complex；hs : forall m : Nat, s != - m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CharP.cast_eq_zero`：∀ (R : Type u_1) [inst : AddMonoidWithOne R] (p : ℕ)
 [CharP R p], ↑p = 0
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `Complex.digamma_def`：digamma_def : digamma = logDeriv Gamma
· 使用定理 `logDeriv_apply`：logDeriv_apply (f : 𝕜 -> 𝕜') (x : 𝕜) : logDeriv f x = de
riv f x / f x
· 使用定理 `Complex.deriv_Gamma_add_one`：deriv_Gamma_add_one (s : Complex) (hs : s !
= 0) : deriv Gamma (s + 1) = Gamma s + s * deriv Gamma s
· 使用定理 `Complex.Gamma_add_one`：Gamma_add_one (s : Complex) (h2 : s != 0) : Gamma
 (s + 1) = s * Gamma s
· 使用定理 `add_div`：add_div (a b c : K) : (a + b) / c = a / c + b / c
· 使用引理 `div_mul_cancel_right₀`：div_mul_cancel_right₀ (hb : b != 0) (a : G₀) : b 
/ (a * b) = a⁻¹
· 使用定理 `Complex.Gamma_ne_zero`：Gamma_ne_zero {s : Complex} (hs : forall m : Nat,
 s != -m) : Gamma s != 0
· 使用引理 `mul_div_mul_left`：mul_div_mul_left (a b : G₀) (hc : c != 0) : c * a / (c
 * b) = a / b
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
-/
theorem digamma_apply_add_one (s : ℂ) (hs : ∀ m : ℕ, s ≠ - m) :
    digamma (s + 1) = digamma s + s⁻¹ := by
  have hs0 : s ≠ 0 := by simpa using hs 0
  rw [digamma_def, logDeriv_apply, logDeriv_apply, deriv_Gamma_add_one s hs0, Gamma_add_one s hs0,
    add_div, div_mul_cancel_right₀ (Gamma_ne_zero hs), mul_div_mul_left _ _ hs0, add_comm]
/-
**Complex.meromorphic_digamma** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：meromorphic_digamma : Meromorphic digamma
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Meromorphic.logDeriv`：∀ {𝕜 : Type u_1} {𝕜' : Type u_2} [inst : Nontrivia
llyNormedField 𝕜] [inst_1 : NontriviallyNormedField 𝕜']   [inst_2 : NormedAlgebr
a 𝕜 𝕜'] [C…
· 使用定理 `Complex.instCompleteSpace`：CompleteSpace ℂ
· 使用引理 `Meromorphic.Gamma`：Meromorphic.Gamma : Meromorphic Gamma
-/
theorem meromorphic_digamma : Meromorphic digamma :=
  Meromorphic.Gamma.logDeriv

end Complex

