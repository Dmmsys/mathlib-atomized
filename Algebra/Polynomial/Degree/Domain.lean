/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Johannes Hölzl, Kim Morrison, Jens Wagemaker
-/
module

public import Mathlib.Algebra.Polynomial.Degree.Operations

/-!
# Univariate polynomials form a domain

## Main results

* `Polynomial.instNoZeroDivisors`: `R[X]` has no zero divisors if `R` does not
* `Polynomial.instDomain`: `R[X]` is a domain if `R` is
-/

public section

noncomputable section

open Finsupp Finset

open Polynomial

namespace Polynomial

universe u v

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

section Semiring

variable [Semiring R] [NoZeroDivisors R] {p q : R[X]}

/-
**Polynomial.natDegree_mul** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：natDegree_mul (hp : p != 0) (hq : q != 0) : (p * q).natDegree = p.natDegre
e + q.natDegree
参数：hp : p != 0；hq : q != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_inj`：cast_inj {m n : Nat} : (m : R) = n ↔ m = n
· 使用定理 `Polynomial.degree_eq_natDegree`：degree_eq_natDegree (hp : p != 0) : degr
ee p = (natDegree p : WithBot Nat)
· 使用定理 `mul_ne_zero`：mul_ne_zero (ha : a != 0) (hb : b != 0) : a * b != 0
· 使用定理 `Polynomial.instNoZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [NoZer
oDivisors R], NoZeroDivisors (Polynomial R)
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用引理 `Polynomial.degree_mul`：degree_mul : degree (p * q) = degree p + degree q
-/
lemma natDegree_mul (hp : p ≠ 0) (hq : q ≠ 0) : (p * q).natDegree = p.natDegree + q.natDegree := by
  rw [← Nat.cast_inj (R := WithBot ℕ), ← degree_eq_natDegree (mul_ne_zero hp hq),
    Nat.cast_add, ← degree_eq_natDegree hp, ← degree_eq_natDegree hq, degree_mul]

omit [NoZeroDivisors R] in
variable (p) in
/-
**Polynomial.natDegree_smul** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：natDegree_smul {S : Type*} [Semiring S] [IsDomain S] [Module S R] [Module.
IsTorsionFree S R] {a : S} (ha : a != 0) : (a • p).natDegree = p.natDegree
参数：ha : a != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Polynomial.natDegree_eq_of_le_of_coeff_ne_zero`：natDegree_eq_of_le_of_co
eff_ne_zero (pn : p.natDegree <= n) (p1 : p.coeff n != 0) : p.natDegree = n
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Polynomial.natDegree_smul_le`：natDegree_smul_le {S : Type*} [SMulZeroCla
ss S R] (a : S) (p : R[X]) : natDegree (a • p) <= natDegree p
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.coeff_smul`：coeff_smul [SMulZeroClass S R] (r : S) (p : R[X])
 (n : Nat) : coeff (r • p) n = r • coeff p n
· 使用引理 `smul_ne_zero`：smul_ne_zero (hr : r != 0) (hm : m != 0) : r • m != 0
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
lemma natDegree_smul {S : Type*} [Semiring S] [IsDomain S] [Module S R] [Module.IsTorsionFree S R]
    {a : S} (ha : a ≠ 0) : (a • p).natDegree = p.natDegree := by
  by_cases hp : p = 0
  · simp only [hp, smul_zero]
  · apply natDegree_eq_of_le_of_coeff_ne_zero
    · exact (natDegree_smul_le _ _).trans (le_refl _)
    · simp only [coeff_smul]
      apply smul_ne_zero ha
      simp [hp]

@[simp]
/-
**Polynomial.natDegree_pow** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：natDegree_pow (p : R[X]) (n : Nat) : natDegree (p ^ n) = n * natDegree p
参数：p : R[X]；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `Polynomial.natDegree_one`：natDegree_one : natDegree (1 : R[X]) = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Polynomial.natDegree_pow'`：natDegree_pow' {n : Nat} (h : leadingCoeff p 
^ n != 0) : natDegree (p ^ n) = n * natDegree p
· 使用引理 `Polynomial.leadingCoeff_pow`：leadingCoeff_pow (p : R[X]) (n : Nat) : lea
dingCoeff (p ^ n) = leadingCoeff p ^ n
· 使用定理 `Ne.eq_1`：∀ {α : Sort u} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `Polynomial.leadingCoeff_eq_zero`：leadingCoeff_eq_zero : leadingCoeff p =
 0 ↔ p = 0
· 使用引理 `pow_ne_zero`：pow_ne_zero (n : Nat) (h : a != 0) : a ^ n != 0
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `Polynomial.instNoZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [NoZer
oDivisors R], NoZeroDivisors (Polynomial R)
-/
lemma natDegree_pow (p : R[X]) (n : ℕ) : natDegree (p ^ n) = n * natDegree p := by
  obtain rfl | hp := eq_or_ne p 0
  · obtain rfl | hn := eq_or_ne n 0 <;> simp [*]
  exact natDegree_pow' <| by
    rw [← leadingCoeff_pow, Ne, leadingCoeff_eq_zero]; exact pow_ne_zero _ hp
/-
**Polynomial.natDegree_le_of_dvd** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：natDegree_le_of_dvd (h1 : p ∣ q) (h2 : q != 0) : p.natDegree <= q.natDegre
e
参数：h1 : p ∣ q；h2 : q != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Polynomial.natDegree_mul`：natDegree_mul (hp : p != 0) (hq : q != 0) : (p
 * q).natDegree = p.natDegree + q.natDegree
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `mul_ne_zero_iff`：mul_ne_zero_iff : a * b != 0 ↔ a != 0 ∧ b != 0
· 使用定理 `Polynomial.instNoZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [NoZer
oDivisors R], NoZeroDivisors (Polynomial R)
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Nat.le_add_right`：∀ (n k : ℕ), n ≤ n + k
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma natDegree_le_of_dvd (h1 : p ∣ q) (h2 : q ≠ 0) : p.natDegree ≤ q.natDegree := by
  obtain ⟨q, rfl⟩ := h1
  rw [mul_ne_zero_iff] at h2
  rw [natDegree_mul h2.1 h2.2]; exact Nat.le_add_right _ _
/-
**Polynomial.degree_le_of_dvd** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：degree_le_of_dvd (h1 : p ∣ q) (h2 : q != 0) : degree p <= degree q
参数：h1 : p ∣ q；h2 : q != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Polynomial.degree_le_mul_left`：degree_le_mul_left (p : R[X]) (hq : q != 
0) : degree p <= degree (p * q)
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_ne_zero_iff`：mul_ne_zero_iff : a * b != 0 ↔ a != 0 ∧ b != 0
· 使用定理 `Polynomial.instNoZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [NoZer
oDivisors R], NoZeroDivisors (Polynomial R)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma degree_le_of_dvd (h1 : p ∣ q) (h2 : q ≠ 0) : degree p ≤ degree q := by
  rcases h1 with ⟨q, rfl⟩; rw [mul_ne_zero_iff] at h2
  exact degree_le_mul_left p h2.2
/-
**Polynomial.eq_zero_of_dvd_of_degree_lt** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：eq_zero_of_dvd_of_degree_lt (h₁ : p ∣ q) (h₂ : degree q < degree p) : q = 
0
参数：h₁ : p ∣ q；h₂ : degree q < degree p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `lt_iff_not_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, a < b 
↔ ¬b ≤ a
· 使用引理 `Polynomial.degree_le_of_dvd`：degree_le_of_dvd (h1 : p ∣ q) (h2 : q != 0)
 : degree p <= degree q
-/
lemma eq_zero_of_dvd_of_degree_lt (h₁ : p ∣ q) (h₂ : degree q < degree p) : q = 0 := by
  by_contra hc
  exact lt_iff_not_ge.mp h₂ (degree_le_of_dvd h₁ hc)
/-
**Polynomial.eq_zero_of_dvd_of_natDegree_lt** 是 Mathlib 中的一个引理，位于命名空间 `Polynomia
l`。
形式化陈述：eq_zero_of_dvd_of_natDegree_lt (h₁ : p ∣ q) (h₂ : natDegree q < natDegree 
p) : q = 0
参数：h₁ : p ∣ q；h₂ : natDegree q < natDegree p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `lt_iff_not_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, a < b 
↔ ¬b ≤ a
· 使用引理 `Polynomial.natDegree_le_of_dvd`：natDegree_le_of_dvd (h1 : p ∣ q) (h2 : q
 != 0) : p.natDegree <= q.natDegree
-/
lemma eq_zero_of_dvd_of_natDegree_lt (h₁ : p ∣ q) (h₂ : natDegree q < natDegree p) :
    q = 0 := by
  by_contra hc
  exact lt_iff_not_ge.mp h₂ (natDegree_le_of_dvd h₁ hc)
/-
**Polynomial.not_dvd_of_degree_lt** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：not_dvd_of_degree_lt (h0 : q != 0) (hl : q.degree < p.degree) : ¬p ∣ q
参数：h0 : q != 0；hl : q.degree < p.degree。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Polynomial.eq_zero_of_dvd_of_degree_lt`：eq_zero_of_dvd_of_degree_lt (h₁ 
: p ∣ q) (h₂ : degree q < degree p) : q = 0
-/
lemma not_dvd_of_degree_lt (h0 : q ≠ 0) (hl : q.degree < p.degree) : ¬p ∣ q := by
  by_contra hcontra
  exact h0 (eq_zero_of_dvd_of_degree_lt hcontra hl)
/-
**Polynomial.not_dvd_of_natDegree_lt** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：not_dvd_of_natDegree_lt (h0 : q != 0) (hl : q.natDegree < p.natDegree) : ¬
p ∣ q
参数：h0 : q != 0；hl : q.natDegree < p.natDegree。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Polynomial.eq_zero_of_dvd_of_natDegree_lt`：eq_zero_of_dvd_of_natDegree_l
t (h₁ : p ∣ q) (h₂ : natDegree q < natDegree p) : q = 0
-/
lemma not_dvd_of_natDegree_lt (h0 : q ≠ 0) (hl : q.natDegree < p.natDegree) :
    ¬p ∣ q := by
  by_contra hcontra
  exact h0 (eq_zero_of_dvd_of_natDegree_lt hcontra hl)

/-- This lemma is useful for working with the `intDegree` of a rational function. -/
/-
**Polynomial.natDegree_sub_eq_of_prod_eq** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：natDegree_sub_eq_of_prod_eq {p₁ p₂ q₁ q₂ : R[X]} (hp₁ : p₁ != 0) (hq₁ : q₁
 != 0) (hp₂ : p₂ != 0) (hq₂ : q₂ != 0) (h_eq : p₁ * q₂ = p₂ * q₁) : (p₁.natDegre
e : Int) - q₁.natDegree = (p₂.natDegree : Int) - q₂.natDegree
参数：hp₁ : p₁ != 0；hq₁ : q₁ != 0；hp₂ : p₂ != 0；hq₂ : q₂ != 0；h_eq : p₁ * q₂ = p₂ *
 q₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_sub_iff_add_eq_add`：∀ {G : Type u_3} [inst : AddCommGroup G] {a b
 c d : G}, a - b = c - d ↔ a + d = c + b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Polynomial.natDegree_mul`：natDegree_mul (hp : p != 0) (hq : q != 0) : (p
 * q).natDegree = p.natDegree + q.natDegree

--- 原说明 ---
This lemma is useful for working with the `intDegree` of a rational function.
-/
lemma natDegree_sub_eq_of_prod_eq {p₁ p₂ q₁ q₂ : R[X]} (hp₁ : p₁ ≠ 0) (hq₁ : q₁ ≠ 0)
    (hp₂ : p₂ ≠ 0) (hq₂ : q₂ ≠ 0) (h_eq : p₁ * q₂ = p₂ * q₁) :
    (p₁.natDegree : ℤ) - q₁.natDegree = (p₂.natDegree : ℤ) - q₂.natDegree := by
  rw [sub_eq_sub_iff_add_eq_add]
  norm_cast
  rw [← natDegree_mul hp₁ hq₂, ← natDegree_mul hp₂ hq₁, h_eq]

end Semiring

end Polynomial

