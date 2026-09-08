/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Johannes Hölzl, Kim Morrison, Jens Wagemaker
-/
module

public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Algebra.Polynomial.Monomial
public import Mathlib.Data.Nat.SuccPred

/-!
# Degree of univariate monomials
-/

public section

noncomputable section

open Finsupp Finset Polynomial

namespace Polynomial

universe u v

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

section Semiring

variable [Semiring R] {p q : R[X]} {ι : Type*}

/-
**Polynomial.natDegree_le_pred** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：natDegree_le_pred (hf : p.natDegree <= n) (hn : p.coeff n = 0) : p.natDegr
ee <= n - 1
参数：hf : p.natDegree <= n；hn : p.coeff n = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Nat.le_succ_iff_eq_or_le`：le_succ_iff_eq_or_le : m <= n.succ ↔ m = n.suc
c ∨ m <= n
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.leadingCoeff_eq_zero`：leadingCoeff_eq_zero : leadingCoeff p =
 0 ↔ p = 0
· 使用定理 `Polynomial.coeff_natDegree`：coeff_natDegree : coeff p (natDegree p) = le
adingCoeff p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.succ_eq_add_one`：∀ (n : ℕ), n.succ = n + 1
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
-/
lemma natDegree_le_pred (hf : p.natDegree ≤ n) (hn : p.coeff n = 0) : p.natDegree ≤ n - 1 := by
  obtain _ | n := n
  · exact hf
  · refine (Nat.le_succ_iff_eq_or_le.1 hf).resolve_left fun h ↦ ?_
    rw [← Nat.succ_eq_add_one, ← h, coeff_natDegree, leadingCoeff_eq_zero] at hn
    simp_all
/-
**Polynomial.monomial_natDegree_leadingCoeff_eq_self** 是 Mathlib 中的一个定理，位于命名空间 `
Polynomial`。
形式化陈述：monomial_natDegree_leadingCoeff_eq_self (h : #p.support <= 1) : monomial p
.natDegree p.leadingCoeff = p
参数：h : #p.support <= 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Polynomial.card_support_le_one_iff_monomial`：card_support_le_one_iff_mon
omial {f : R[X]} : Finset.card f.support <= 1 ↔ exists n a, f = monomial n a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.monomial_zero_right`：monomial_zero_right (n : Nat) : monomial
 n (0 : R) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.natDegree_monomial`：natDegree_monomial [DecidableEq R] (i : N
at) (r : R) : natDegree (monomial i r) = if r = 0 then 0 else i
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Polynomial.leadingCoeff_monomial`：leadingCoeff_monomial (a : R) (n : Nat
) : leadingCoeff (monomial n a) = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem monomial_natDegree_leadingCoeff_eq_self (h : #p.support ≤ 1) :
    monomial p.natDegree p.leadingCoeff = p := by
  classical
  rcases card_support_le_one_iff_monomial.1 h with ⟨n, a, rfl⟩
  by_cases ha : a = 0 <;> simp [ha]
/-
**Polynomial.C_mul_X_pow_eq_self** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：C_mul_X_pow_eq_self (h : #p.support <= 1) : C p.leadingCoeff * X ^ p.natDe
gree = p
参数：h : #p.support <= 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.C_mul_X_pow_eq_monomial`：∀ {R : Type u} {a : R} [inst : Semir
ing R] {n : ℕ}, Polynomial.C a * Polynomial.X ^ n = (Polynomial.monomial n) a
· 使用定理 `Polynomial.monomial_natDegree_leadingCoeff_eq_self`：monomial_natDegree_l
eadingCoeff_eq_self (h : #p.support <= 1) : monomial p.natDegree p.leadingCoeff 
= p
-/
theorem C_mul_X_pow_eq_self (h : #p.support ≤ 1) : C p.leadingCoeff * X ^ p.natDegree = p := by
  rw [C_mul_X_pow_eq_monomial, monomial_natDegree_leadingCoeff_eq_self h]

end Semiring

end Polynomial

