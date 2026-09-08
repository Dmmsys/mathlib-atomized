/-
Copyright (c) 2022 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Geißer, Michael Stoll
-/
module

public import Mathlib.Algebra.ContinuedFractions.Computation.ApproximationCorollaries
public import Mathlib.Algebra.ContinuedFractions.Computation.Translations
public import Mathlib.NumberTheory.DiophantineApproximation.Basic

/-!
# Diophantine Approximation using continued fractions

## Main statements

There are two versions of Legendre's Theorem.`Real.exists_rat_eq_convergent`,
defined in `Mathlib/NumberTheory/DiophantineApproximation/Basic.lean`, uses `Real.convergent`,
a simple recursive definition of the convergents that is also defined in that file.
This file provides `Real.exists_convs_eq_rat`, using `GenContFract.convs` of `GenContFract.of ξ`.
-/

public section

section Convergent

namespace Real

open Int

/-!
Our `convergent`s agree with `GenContFract.convs`.
-/

open GenContFract

/-- The `n`th convergent of the `GenContFract.of ξ` agrees with `ξ.convergent n`. -/
/-
**Real.convs_eq_convergent** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：convs_eq_convergent (ξ : Real) (n : Nat) : (GenContFract.of ξ).convs n = ξ
.convergent n
参数：ξ : Real；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `GenContFract.zeroth_conv_eq_h`：zeroth_conv_eq_h : g.convs 0 = g.h
· 使用定理 `Rat.cast_intCast`：cast_intCast (n : Int) : ((n : Rat) : α) = n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `GenContFract.convs_succ`：convs_succ (n : Nat) : (of v).convs (n + 1) = ⌊
v⌋ + 1 / (of (Int.fract v)⁻¹).convs n
· 使用定理 `Real.convergent_succ`：convergent_succ (ξ : Real) (n : Nat) : ξ.convergen
t (n + 1) = ⌊ξ⌋ + ((fract ξ)⁻¹.convergent n)⁻¹
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
The `n`th convergent of the `GenContFract.of ξ` agrees with `ξ.convergent n`.
-/
theorem convs_eq_convergent (ξ : ℝ) (n : ℕ) :
    (GenContFract.of ξ).convs n = ξ.convergent n := by
  induction n generalizing ξ with
  | zero => simp only [zeroth_conv_eq_h, of_h_eq_floor, convergent_zero, Rat.cast_intCast]
  | succ n ih => rw [convs_succ, ih (fract ξ)⁻¹, convergent_succ, one_div]; norm_cast

end Real

end Convergent

namespace Real

variable {ξ : ℝ} {u v : ℤ}

/-- The main result, *Legendre's Theorem* on rational approximation:
if `ξ` is a real number and `q` is a rational number such that `|ξ - q| < 1/(2*q.den^2)`,
then `q` is a convergent of the continued fraction expansion of `ξ`.
This is the version using `GenContFract.convs`. -/
/-
**Real.exists_convs_eq_rat** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：exists_convs_eq_rat {q : Rat} (h : |ξ - q| < 1 / (2 * (q.den : Real) ^ 2))
 : exists n, (GenContFract.of ξ).convs n = q
参数：h : |ξ - q| < 1 / (2 * (q.den : Real) ^ 2)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Real.exists_rat_eq_convergent`：exists_rat_eq_convergent {q : Rat} (h : |
ξ - q| < 1 / (2 * (q.den : Real) ^ 2)) : exists n, q = ξ.convergent n
· 使用定理 `Real.convs_eq_convergent`：convs_eq_convergent (ξ : Real) (n : Nat) : (Ge
nContFract.of ξ).convs n = ξ.convergent n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
The main result, *Legendre's Theorem* on rational approximation:
if `ξ` is a real number and `q` is a rational number such that `|ξ - q| < 1/(2*q
.den^2)`,
then `q` is a convergent of the continued fraction expansion of `ξ`.
This is the version using `GenContFract.convs`.
-/
theorem exists_convs_eq_rat {q : ℚ}
    (h : |ξ - q| < 1 / (2 * (q.den : ℝ) ^ 2)) : ∃ n, (GenContFract.of ξ).convs n = q := by
  obtain ⟨n, hn⟩ := exists_rat_eq_convergent h
  exact ⟨n, hn.symm ▸ convs_eq_convergent ξ n⟩

end Real

